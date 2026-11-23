import SelfTest
import Winnow.Crypto.Sha2
import Kernel.Hw
import Kernel.Fdt
import Kernel.Rng
import Kernel.VaultStore
import Kernel.Wire
import Kernel.Fb
import Kernel.GpioKeys
import Kernel.Qemu.Pl011
import Kernel.Qemu.Ramfb
import Kernel.Qemu.VirtioMmio
import Kernel.Komodo
import Kernel.Dwc3
import Kernel.KomodoTouch
import Kernel.Idle
import Kernel.Panel
import Tricorder.BuildConfig
import Tricorder.Network
import Tricorder.Crypto.Bip39Ascii
import Tricorder.Crypto.Vault
import Tricorder.Crypto.Key
import Tricorder.Signer.Descriptor
import Tricorder.Signer.Review
import Tricorder.Signer.Sign
import Tricorder.Signer.Protocol
import Tricorder.Ui.Layout
import Tricorder.Ui.State
import Tricorder.Ui.View

/-! # Tricorder Bare-Metal AArch64 OS Main Loop (`Tricorder.OsMain`)

Zero Linux, zero Android, zero filesystems:
- Verifies FDT (`Kernel.Fdt.parse`) & hardware RNG (`Kernel.Rng`, fail-closed)
- Keeps the vault in two raw 4 KiB slots (`Kernel.VaultStore`): on a `VirtioBlk` disk under QEMU, and in
  memory only on the Pixel 9 Pro XL, where nothing is written to storage and power-off forgets the key
- Renders the screens and the focus ring (`Ui.Layout.withFocusRing`) onto hardware framebuffer
  (`Ramfb` in QEMU / ABL `cont_splash` + DECON on Pixel 9 Pro XL)
- Driven by physical buttons (Volume Up / Volume Down / Power via verified `Kernel.GpioKeys`) and
  zero-filesystem `Kernel.Wire` frames over PL011 UART (QEMU) or USB-C DWC3 bulk (Pixel). -/

namespace Tricorder.OsMain

open Kernel Kernel.Qemu Tricorder.Ui Tricorder.Signer

private def log (s : String) : BaseIO Unit :=
  Hw.consoleWrite (s ++ "\n").toUTF8

structure BareState where
  model : Model
  focusIdx : Nat := 0
  cmds : List DrawCmd := []
  disk : VaultStore.DualDisk := { slot0 := VaultStore.zeroSlot, slot1 := VaultStore.zeroSlot }
  blk? : Option VirtioMmio.VirtioBlk := none
  vrng? : Option VirtioMmio.VirtioRng := none
  uart : Pl011.Uart := {}
  hasPl011 : Bool := false
  dwc3? : Option Dwc3.Device := none
  touch? : Option KomodoTouch.Device := none
  deconFlushBase? : Option UInt64 := none
  gpioKeysBase? : Option UInt64 := none
  komodo : Komodo.KomodoHw := {}
  keys : GpioKeys.KeysState := {}
  lastSigned? : Option SignedResult := none
  dirty : Bool := true
  idle : Idle.State := {}
  /-- How many presses, taps and other stirrings `Kernel.Idle` has been told of, for the bench. -/
  idleSeen : Nat × Nat × Nat := (0, 0, 0)

private def hasWindow (wins : Array Hw.Window) (addr len : UInt64) : Bool :=
  wins.any fun w => addr ≥ w.base && w.size ≥ len && addr - w.base ≤ w.size - len

/-- Whether the host may press the buttons: only in an image built for regtest, which the tests under
emulation drive. On signet and mainnet a person presses them (`Kernel.WireProofs.only_test_builds_inject_keys`). -/
private def isTestBuild (m : Model) : Bool :=
  m.network == .regtest

/-- Whether a wallet or a payment is on the screen, waiting for its holder's answer. -/
private def isReviewing (m : Model) : Bool :=
  match m.screen with
  | .reviewTx .. | .reviewDescriptor .. => true
  | _ => false

/-- An unlocked signer left alone locks itself after about five minutes, and the panel of one left alone,
locked or not, goes dark after one. Both are counted on the Pixel's 24.576 MHz counter. -/
private def idleConfig : Idle.Config := { screenOffTicks := 1474560000, lockTicks := 7500000000 }

/-- Whether the panel is dark (`Kernel.Idle`). -/
private def BareState.dark (st : BareState) : Bool :=
  st.idle.phase == .off

/-- Health-checked hardware entropy: prefers AArch64 `RNDRRS`/`RNDR`, mixes/falls back to `virtio-rng`. -/
private def hardwareRandom (st : BareState) (count : Nat) : BaseIO (Except String (BareState × ByteArray)) := do
  let cpu ← Hw.cpuInfo
  if cpu.hasRndr then
    match ← Rng.collectRndr count with
    | .ok b => return .ok (st, b)
    | .error e => return .error e
  else if let some vr := st.vrng? then
    let mut cur := vr
    let mut out := ByteArray.empty
    let mut ctr : UInt64 := 0
    while out.size < count do
      let some (cur', raw) ← cur.readBytes 32 | return .error "virtio-rng timeout"
      cur := cur'
      let w0 := Rng.readLe64 raw 0
      let w1 := Rng.readLe64 raw 8
      let w2 := Rng.readLe64 raw 16
      let w3 := Rng.readLe64 raw 24
      match Rng.conditionBlock w0 w1 w2 w3 ctr with
      | .error e => return .error e
      | .ok blk =>
        let need := count - out.size
        out := out ++ (if blk.size ≤ need then blk else blk.extract 0 need)
        ctr := ctr + 1
    return .ok ({ st with vrng? := some cur }, out)
  else
    return .error "NO HARDWARE RNG AVAILABLE"

/-- Atomically commits updated `(failedAttempts, vault?, desc?)` to the inactive raw 4 KiB flash slot. -/
private def persistSlotChecked (st : BareState) (attempts : Nat) (vault? desc? : Option ByteArray) :
    BaseIO (BareState × Bool) := do
  let (targetIdx, nextSeq) := VaultStore.planWrite st.disk
  let blkBytes := VaultStore.encodeSlot { seq := nextSeq, failedAttempts := attempts, vault?, descriptor? := desc? }
  let disk' := st.disk.set targetIdx blkBytes
  let slotNum := if targetIdx then 1 else 0
  match st.blk? with
  | some blk =>
    match ← blk.writeBlock4K slotNum blkBytes with
    | some blk' => return ({ st with disk := disk', blk? := some blk' }, true)
    | none =>
      log "os: WARN virtio-blk write failed"
      return ({ st with disk := disk' }, false)
  -- With no disk the slots are in memory only, and the write is the assignment.
  | none => return ({ st with disk := disk' }, true)

private def persistSlot (st : BareState) (attempts : Nat) (vault? desc? : Option ByteArray) : BaseIO BareState :=
  return (← persistSlotChecked st attempts vault? desc?).1

/-- Zeroes BOTH raw 4 KiB slots on disk and in memory. -/
private def wipeStorage (st : BareState) : BaseIO BareState := do
  let disk' := VaultStore.wipeBoth st.disk
  match st.blk? with
  | some blk =>
    let blk1 := (← blk.writeBlock4K 0 VaultStore.zeroSlot).getD blk
    let blk2 := (← blk1.writeBlock4K 1 VaultStore.zeroSlot).getD blk1
    return { st with disk := disk', blk? := some blk2 }
  | none => return { st with disk := disk' }

private def currentVault? (st : BareState) : Option ByteArray :=
  (VaultStore.recover st.disk).bind (·.2.vault?)

private def currentDesc? (st : BareState) : Option ByteArray :=
  (VaultStore.recover st.disk).bind (·.2.descriptor?)

private def currentAttempts (st : BareState) : Nat :=
  match VaultStore.recover st.disk with
  | some (_, r) => r.failedAttempts
  | none => 0

private def selfTestDigestHex : String :=
  let h := Winnow.sha256 SelfTest.transcript
  hexBytes (h.extract 0 12)

/-- Executes one `Ui.Effect` directly against bare-metal RNG and 2-slot raw `VaultStore`. -/
private def performEffect (st : BareState) (eff : Effect) : BaseIO (BareState × Event) := do
  match eff with
  | .generateSeed =>
    match ← hardwareRandom st 32 with
    | .error e => return (st, .hostStatus e true)
    | .ok (st', ent) =>
      match Bip39Ascii.fromEntropy ent with
      | .ok words => return (st', .hostSeedGenerated words)
      | .error err => return (st', .hostStatus err true)
  | .sealVault pin words =>
    match ← hardwareRandom st 28 with
    | .error e => return (st, .hostStatus e true)
    | .ok (st', rnd) =>
      let salt := rnd.extract 0 16
      let nonce := rnd.extract 16 28
      match Vault.sealVault st'.model.network pin words salt nonce with
      | .error err => return (st', .hostStatus err true)
      | .ok blob =>
        match Identity.ofWords words st'.model.network.toBitcoin with
        | .error err => return (st', .hostStatus err true)
        | .ok id =>
          let st'' ← persistSlot st' 0 (some blob) none
          return (st'', .hostVaultSealed words id)
  | .unlockVault pin =>
    let some blob := currentVault? st
      | return (st, .hostStatus "VAULT SLOT EMPTY" true)
    -- The attempt is counted where it will survive a power cut before the PIN is tried, and if it cannot
    -- be counted the PIN is not tried: pulling the power must not buy a free guess.
    let nextAttempts := currentAttempts st + 1
    let (st, counted) ← persistSlotChecked st nextAttempts (some blob) (currentDesc? st)
    unless counted do
      return (st, .hostStatus "STORAGE FAILED - PIN NOT TRIED" true)
    match Vault.openVault st.model.network pin blob with
    | .ok words =>
      match Identity.ofWords words st.model.network.toBitcoin with
      | .error err => return (st, .hostStatus err true)
      | .ok id =>
        let desc? := currentDesc? st
        let st' ← persistSlot st 0 (some blob) desc?
        let wallet? : Option RegisteredWallet :=
          match desc? with
          | none => none
          | some db => (String.fromUTF8? db).bind fun txt => (registerDescriptor id txt).toOption
        return (st', .hostUnlockOk words id wallet?)
    | .error _ =>
      if nextAttempts ≥ Vault.maxFailedAttempts then
        let st' ← wipeStorage st
        return (st', .hostUnlockFailed nextAttempts true)
      else
        return (st, .hostUnlockFailed nextAttempts false)
  | .wipeVault =>
    let st' ← wipeStorage st
    return ({ st' with lastSigned? := none }, .hostStatus "VAULT WIPED" true)
  | .scanInbox =>
    return (st, .hostInboxLoaded #[])
  | .loadInboxItem _ =>
    return (st, .hostStatus "PUSH PSBT OVER WIRE" false)
  | .saveDescriptor desc =>
    let st' ← persistSlot st (currentAttempts st) (currentVault? st) (some desc.toUTF8)
    -- With no disk (the phone) the wallet is held in memory, and is gone at power-off: say so.
    return (st', .hostStatus (if st.blk?.isSome then "WALLET SAVED TO DISK" else "WALLET KEPT UNTIL POWER-OFF") false)
  | .exportKeys _ =>
    return (st, .hostStatus "KEYS READY ON QR / WIRE" false)
  | .executeSign tx =>
    match st.model.secrets with
    | none => return (st, .hostStatus "REFUSED: LOCKED" true)
    | some (id, _) =>
      match ← hardwareRandom st 32 with
      | .error e => return (st, .hostStatus e true)
      | .ok (st', fresh) =>
        match signReviewed id tx fresh with
        | .error err => return (st', .hostStatus err true)
        | .ok res =>
          return ({ st' with lastSigned? := some res }, .hostSigned res)
  | .runDiagnostics runBig =>
    let dig := selfTestDigestHex
    let bigOk : Option Bool :=
      if runBig then
        let a : Nat := (1 <<< 256) + 0x170147
        let b : Nat := (1 <<< 129) + 1701
        some (((a * b + 47) / b == a) && ((a * b + 47) % b == 47))
      else none
    match ← hardwareRandom st 12 with
    | .error e => return (st, .hostStatus e true)
    | .ok (st', ent) =>
      return (st', .hostDiagnostics dig bigOk (hexBytes ent).toUpper)

private def rebuildView (st : BareState) (resetFocus : Bool) : BareState :=
  let rawCmds := View.view st.model 540 1200 28 24
  let nBtns := (buttonsOf rawCmds).length
  let idx := if resetFocus || nBtns == 0 then 0 else st.focusIdx % nBtns
  let cmds := withFocusRing rawCmds idx st.model.network.palette.highlight
  { st with focusIdx := idx, cmds, dirty := true }

private def screenTag (s : Screen) : String :=
  match s with
  | .locked => "locked"
  | .setupChoice => "setupChoice"
  | .setupWords .. => "setupWords"
  | .setupRestore .. => "setupRestore"
  | .setupPin .. => "setupPin"
  | .home => "home"
  | .keys .. => "keys"
  | .inbox .. => "inbox"
  | .reviewDescriptor .. => "reviewDescriptor"
  | .reviewTx _ false => "reviewTx"
  | .reviewTx _ true => "reviewTxArmed"
  | .signed .. => "signed"
  | .diagnostics .. => "diagnostics"

/-- Dispatches one `Event` to quiescence (bounded to 4 steps). -/
private def dispatch (st : BareState) (ev : Event) : BaseIO BareState := do
  let prevTag := screenTag st.model.screen
  let mut cur := st
  let mut queue : List Event := [ev]
  let mut fuel := 4
  while fuel > 0 do
    match queue with
    | [] => break
    | e :: rest =>
      queue := rest
      let (nextModel, effs) := update cur.model e
      cur := { cur with model := nextModel }
      for eff in effs do
        let (cur', reply) ← performEffect cur eff
        cur := cur'
        queue := queue ++ [reply]
      fuel := fuel - 1
  let changedScreen := screenTag cur.model.screen != prevTag
  let cur' := if cur.model.secrets.isNone then { cur with lastSigned? := none } else cur
  return rebuildView cur' changedScreen

/-- Handles a semantic physical-button `KeyEvent` (`prev`, `next`, `select`, `back`). -/
private def handleKey (st : BareState) (k : GpioKeys.KeyEvent) : BaseIO BareState := do
  let nBtns := (buttonsOf st.cmds).length
  match k with
  | .prev =>
    if nBtns == 0 then return st
    let idx := if st.focusIdx == 0 then nBtns - 1 else st.focusIdx - 1
    return rebuildView { st with focusIdx := idx } false
  | .next =>
    if nBtns == 0 then return st
    let idx := (st.focusIdx + 1) % nBtns
    return rebuildView { st with focusIdx := idx } false
  | .select =>
    match focusedButton? st.cmds st.focusIdx with
    | none => return st
    | some btn => dispatch st (.tapButton btn)
  | .back =>
    dispatch st .appPaused

/-- Whether a control takes the physical buttons, so that a tap on the glass cannot press it. -/
private def needsButtons : ButtonId → Bool
  -- Arming and signing, and nothing else. They are the two presses that spend. Every other control either
  -- shows something or can be undone on the device: a wallet accepted by a tap still signs nothing by itself.
  | .armSign | .confirmSign => true
  | _ => false

/-- A tap on the glass, as a place on the 540 by 1200 picture. It does what pressing the control under it
would do, with one exception: arming a payment and signing it take the buttons. A stray touch on the glass
must not be able to sign, and the buttons are debounced and latched for exactly that
(`Kernel.GpioKeysProofs`). -/
private def handleTap (st : BareState) (x y : Nat) : BaseIO BareState := do
  match hitTest st.cmds x y with
  | none => return st
  | some btn =>
    if needsButtons btn then
      return rebuildView { st with model := { st.model with statusMsg := "USE THE BUTTONS FOR THIS", isError := false } } false
    else dispatch st (.tapButton btn)

/-- Handles one CRC-32-verified `Kernel.Wire.Frame`, enforcing proved `Op.allowed` security gating. -/
private def handleWireFrame (st : BareState) (f : Wire.Frame) : BaseIO (BareState × Wire.Frame) := do
  let unlocked := st.model.secrets.isSome
  let reviewing := isReviewing st.model
  if !f.op.allowed unlocked reviewing (isTestBuild st.model) then
    let why := if unlocked && reviewing && f.op.isPush then "BUSY_REVIEWING" else "DENIED_BY_SECURITY_POLICY"
    return (st, { op := .respErr, payload := why.toUTF8 })
  match f.op with
  | .ping =>
    return (st, { op := .respOk, payload := s!"TRICORDER-BARE-V1:{st.model.network.name}".toUTF8 })
  | .getStatus =>
    let tag := screenTag st.model.screen
    let u := if unlocked then "1" else "0"
    let w := if st.model.wallet.isSome then "1" else "0"
    let armed := match st.model.screen with | .reviewTx _ true => "1" | _ => "0"
    let s := s!"{tag}|{u}|{w}|{armed}|{st.focusIdx}|{st.model.statusMsg}"
    return (st, { op := .respOk, payload := s.toUTF8 })
  | .getKeys =>
    match st.model.secrets with
    | none => return (st, { op := .respErr, payload := "LOCKED".toUTF8 })
    | some (id, _) =>
      let txt := Protocol.formatKeysExport id st.model.wallet
      return (st, { op := .respOk, payload := txt.toUTF8 })
  | .pushDescriptor =>
    match st.model.secrets with
    | none => return (st, { op := .respErr, payload := "LOCKED".toUTF8 })
    | some (id, _) =>
      match String.fromUTF8? f.payload with
      | none => return (st, { op := .respErr, payload := "DESCRIPTOR_NOT_UTF8".toUTF8 })
      | some txt =>
        match registerDescriptor id txt with
        | .error err => return (st, { op := .respErr, payload := err.toUTF8 })
        | .ok w =>
          let st' ← dispatch st (.hostDescriptorReviewed "wire/descriptor.txt" w)
          return (st', { op := .respOk, payload := w.firstAddress.toUTF8 })
  | .pushOverride =>
    match st.model.secrets, st.model.wallet with
    | none, _ => return (st, { op := .respErr, payload := "LOCKED".toUTF8 })
    | _, none => return (st, { op := .respErr, payload := "NO_WALLET_REGISTERED".toUTF8 })
    | some (id, _), some w =>
      match parsePsbtBytes f.payload with
      | .error err => return (st, { op := .respErr, payload := err.toUTF8 })
      | .ok psbt =>
        match reviewOverride id w psbt "wire/override.psbt" with
        | .error err => return (st, { op := .respErr, payload := err.toUTF8 })
        | .ok rev =>
          -- What was signed before is not this payment: `pollResult` answers nothing until this one is signed.
          let st' ← dispatch { st with lastSigned? := none } (.hostTxReviewed rev)
          return (st', { op := .respOk, payload := rev.txidDisplay.toUTF8 })
  | .pollResult =>
    match st.lastSigned? with
    | none => return (st, { op := .respErr, payload := "NO_SIGNATURE_READY".toUTF8 })
    | some res => return (st, { op := .respOk, payload := res.payloadText.toUTF8 })
  | .injectKey =>
    let code := if f.payload.size > 0 then f.payload.get! 0 else 255
    let key? : Option GpioKeys.KeyEvent := match code with
      | 0 => some .prev
      | 1 => some .next
      | 2 => some .select
      | 3 => some .back
      | _ => none
    match key? with
    | none => return (st, { op := .respErr, payload := "BAD_KEY_CODE".toUTF8 })
    | some k =>
      let st' ← handleKey st k
      let tag := screenTag st'.model.screen
      return (st', { op := .respOk, payload := s!"{tag}|{st'.focusIdx}|{st'.model.statusMsg}".toUTF8 })
  | .lab => do
    -- Hardware bring-up, regtest builds only (`Kernel.WireProofs.only_test_builds_touch_registers`).
    -- The payload is a run of steps, done in order:
    --   'r' addr:u64        read a 32-bit register; its value is appended to the reply
    --   'w' addr:u64 v:u32  write one
    --   'd' micros:u32      wait
    --   'f' off:u32 n:u16   n bytes of the device tree the bootloader handed over (its size, if n = 0)
    --   'W'                 the register windows this image may touch: base:u64 size:u64 each
    --   'i'                 going dark, without disturbing it: whether the panel is dark (u32), ticks since a
    --                       person's last press or tap and since the panel last had a reason to be lit
    --                       (u64 each), and how many presses, taps and other stirrings there have been (u32 each)
    -- A register outside every window ends the run: the reply is what was read so far, as an error.
    let wins ← Hw.windows
    let p := f.payload
    let u64At (o : Nat) : UInt64 := (List.range 8).foldl (fun acc k => acc ||| ((p.get! (o + k)).toUInt64 <<< (8 * k).toUInt64)) 0
    let u32At (o : Nat) : UInt32 := (List.range 4).foldl (fun acc k => acc ||| ((p.get! (o + k)).toUInt32 <<< (8 * k).toUInt32)) 0
    let push32 (b : ByteArray) (v : UInt32) : ByteArray := (List.range 4).foldl (fun acc k => acc.push (v >>> (8 * k).toUInt32).toUInt8) b
    let push64 (b : ByteArray) (v : UInt64) : ByteArray := (List.range 8).foldl (fun acc k => acc.push (v >>> (8 * k).toUInt64).toUInt8) b
    let mut out := ByteArray.empty
    let mut i := 0
    let mut bad : Option String := none
    while i < p.size && bad.isNone do
      let tag := p.get! i
      if tag == 0x72 && i + 9 ≤ p.size then           -- 'r'
        let a := u64At (i + 1)
        if hasWindow wins a 4 && a % 4 == 0 then out := push32 out (← Hw.read32 a) else bad := some s!"NO_WINDOW {a}"
        i := i + 9
      else if tag == 0x77 && i + 13 ≤ p.size then     -- 'w'
        let a := u64At (i + 1)
        if hasWindow wins a 4 && a % 4 == 0 then Hw.write32 a (u32At (i + 9)) else bad := some s!"NO_WINDOW {a}"
        i := i + 13
      else if tag == 0x64 && i + 5 ≤ p.size then      -- 'd'
        let ticksToWait := (u32At (i + 1)).toUInt64 * 25
        let t0 ← Hw.ticks
        let mut now ← Hw.ticks
        while now - t0 < ticksToWait do
          Hw.pause
          now ← Hw.ticks
        i := i + 5
      else if tag == 0x66 && i + 7 ≤ p.size then      -- 'f'
        let fdt ← Hw.fdtBytes
        let off := (u32At (i + 1)).toNat
        let n := (p.get! (i + 5)).toNat ||| ((p.get! (i + 6)).toNat <<< 8)
        if n == 0 then out := push32 out fdt.size.toUInt32
        else out := out ++ fdt.extract off (min fdt.size (off + min n 3900))
        i := i + 7
      else if tag == 0x57 then                        -- 'W'
        for w in wins do
          out := push64 (push64 out w.base) w.size
        i := i + 1
      else if tag == 0x69 then                        -- 'i'
        let now := (← Hw.ticks).toNat
        let (keys, taps, stirs) := st.idleSeen
        out := push32 out (if st.idle.phase == .off then 1 else 0)
        out := push64 (push64 out (now - st.idle.lastPerson).toUInt64) (now - st.idle.lastScreen).toUInt64
        out := push32 (push32 (push32 out keys.toUInt32) taps.toUInt32) stirs.toUInt32
        i := i + 1
      else
        bad := some "BAD_LAB_STEP"
    match bad with
    | some why => return (st, { op := .respErr, payload := why.toUTF8 ++ out })
    | none => return (st, { op := .respOk, payload := out })
  | _ =>
    return (st, { op := .respErr, payload := "UNSUPPORTED_OP".toUTF8 })

/-- Draws the screen if it has changed. A dark panel is left dark: what changed is drawn when it is lit. -/
private def renderIfDirty (st : BareState) : BaseIO BareState := do
  if !st.dirty || st.dark then return st
  let pal := st.model.network.palette
  let frame := renderCmds 540 1200 pal.bg st.cmds
  Fb.blitToHardware frame.pixels 540 1200 .bgra8888
  if let some decon := st.deconFlushBase? then
    Komodo.deconFlushFrame decon
  return { st with dirty := false }

/-- Tells `Kernel.Idle` what just happened and does what it decides: locks, makes the panel dark, or lights
it. Returns whether a press or tap is to be passed on to the screens; one that lit a dark panel is not. -/
private def noteInput (st : BareState) (i : Idle.Input) : BaseIO (BareState × Bool) := do
  let now ← Hw.ticks
  let d := Idle.step idleConfig st.idle st.model.secrets.isSome now.toNat i
  let (keys, taps, stirs) := st.idleSeen
  let seen := match i with
    | .key => (keys + 1, taps, stirs)
    | .tap => (keys, taps + 1, stirs)
    | .stir => (keys, taps, stirs + 1)
    | .none => (keys, taps, stirs)
  let mut st := { st with idle := d.state, idleSeen := seen }
  if d.lock then
    -- Left alone while unlocked, the signer locks: its secrets are wiped as `appPaused` wipes them.
    st ← dispatch st .appPaused
    -- Locking in the dark does not light the panel; the lock screen is drawn when something does.
    if st.dark then st := { st with dirty := false }
  if d.blank then
    Panel.dark st.deconFlushBase?
  if d.wake then
    st := { st with dirty := true }
  st ← renderIfDirty st
  return (st, d.deliver)

/-- A change to the picture that came from the cable lights a dark panel, so that nothing new is shown where
it cannot be seen. A frame that changed nothing does not. -/
private def showIfChanged (st : BareState) : BaseIO BareState := do
  if st.dirty then return (← noteInput st .stir).1 else return st

/-- Handles a frame from the cable. A button press from the host (regtest builds only) is a press like any
other: on a dark panel it lights the panel and presses nothing, and the reply says so. -/
private def handleFrame (st : BareState) (frame : Wire.Frame) : BaseIO (BareState × Wire.Frame) := do
  if frame.op == .injectKey && frame.op.allowed st.model.secrets.isSome (isReviewing st.model) (isTestBuild st.model) then
    let (st, deliver) ← noteInput st .key
    if !deliver then
      return (st, { op := .respOk, payload := s!"woke|{st.focusIdx}|{st.model.statusMsg}".toUTF8 })
    let (st, reply) ← handleWireFrame st frame
    return (← renderIfDirty st, reply)
  let (st, reply) ← handleWireFrame st frame
  return (← showIfChanged st, reply)

@[export tricorder_bare_main]
def bareMain : IO UInt32 := do
  let net := BuildConfig.activeNetwork
  log s!"tricorder-os: bare-metal AArch64 starting ({net.name})"

  -- 1. Parse live FDT via verified pure-Lean parser & inspect announced capability windows
  let wins ← Hw.windows
  let hasPl011 := hasWindow wins Pl011.defaultBase 0x20
  let fdtRaw ← Hw.fdtBytes
  let komodo := match Fdt.parse fdtRaw with
    | .ok fdt => Komodo.discoverFromFdt fdt
    | .error _ => {}

  -- Disarm BOTH Tensor G4 hardware watchdogs (`watchdog_cl0` & `watchdog_cl1`, ~87s ABL timeout!)
  if hasWindow wins Komodo.wdtCl0DefaultBase 0x10 then
    Komodo.disarmWatchdog Komodo.wdtCl0DefaultBase
  if hasWindow wins Komodo.wdtCl1DefaultBase 0x10 then
    Komodo.disarmWatchdog Komodo.wdtCl1DefaultBase

  let deconFlushBase? : Option UInt64 :=
    if hasWindow wins Komodo.deconDefaultBase 0x60 then some Komodo.deconDefaultBase
    else match komodo.deconBase? with
      | some b => if hasWindow wins b 0x60 then some b else none
      | none => none

  let gpioKeysBase? : Option UInt64 :=
    if hasWindow wins Komodo.gpioAliveDefaultBase 0xB0 then some Komodo.gpioAliveDefaultBase
    else match komodo.gpioAliveBase? with
      | some b => if hasWindow wins b 0xB0 then some b else none
      | none => none

  -- 2. Bring up display (`ramfb` on QEMU; `cont_splash` on Pixel `komodo`)
  match ← Ramfb.init Ramfb.fwCfgDefaultBase 540 1200 with
  | some fbAddr => log s!"tricorder-os: QEMU ramfb 540x1200 active at {fbAddr}"
  | none =>
    let fi ← Hw.fbInfo
    log s!"tricorder-os: pre-initialized fb base={fi.base} {fi.width}x{fi.height} stride={fi.stride}"

  -- 3. Discover VirtIO-MMIO devices (`virtio-blk` for 2-slot vault, `virtio-rng` for entropy)
  let vdevs ← VirtioMmio.discover
  let vrng? ← VirtioMmio.VirtioRng.init vdevs
  let mut blk? ← VirtioMmio.VirtioBlk.init vdevs

  -- 4. Load raw 2-slot `VaultStore` (Slot 0 & Slot 1) with zero filesystem!
  let mut disk : VaultStore.DualDisk := { slot0 := VaultStore.zeroSlot, slot1 := VaultStore.zeroSlot }
  if let some b := blk? then
    let mut bCur := b
    if let some (b1, s0) ← bCur.readBlock4K 0 then
      disk := { disk with slot0 := s0 }
      bCur := b1
    if let some (b2, s1) ← bCur.readBlock4K 1 then
      disk := { disk with slot1 := s1 }
      bCur := b2
    blk? := some bCur

  let (hasVault, attempts) := match VaultStore.recover disk with
    | none => (false, 0)
    | some (_, rec) => (rec.vault?.isSome, rec.failedAttempts)
  log s!"tricorder-os: 2-slot raw vault mounted (hasVault={hasVault}, attempts={attempts})"

  -- 4b. Bring up polled USB-C DWC3 Device controller (`0x11210000`) on Pixel `komodo`
  let (dwc3?, usbStatus?) ←
    if !hasPl011 && hasWindow wins Dwc3.dwc3DefaultBase 0xD000 then
      match ← Dwc3.init Dwc3.dwc3DefaultBase with
      | .ok dev =>
        let dsts ← Hw.read32 (dev.base + Dwc3.regDsts)
        log s!"tricorder-os: USB-C DWC3 online (SNPSID={dev.snpsId} DSTS={dsts})"
        pure (some dev, some s!"USB ONLINE DSTS={dsts}")
      | .error err =>
        log s!"tricorder-os: USB-C DWC3 unavailable: {err}"
        pure (none, some err)
    else
      pure (none, none)

  -- 4c. The touchscreen, on the Pixel. Without it the buttons work as before, and the screen says why.
  let (touch?, touchStatus?) ←
    if !hasPl011 && KomodoTouch.windows.all (fun (base, size) => hasWindow wins base size) then
      match ← KomodoTouch.init with
      | .ok dev =>
        log s!"tricorder-os: touchscreen online ({dev.maxX + 1} x {dev.maxY + 1} units)"
        pure (some dev, none)
      | .error err =>
        log s!"tricorder-os: no touchscreen: {err}"
        pure (none, some err)
    else
      pure (none, none)

  let initModel0 := Model.initial net hasVault attempts
  let initModel := match touchStatus?, usbStatus? with
    | some msg, _ => { initModel0 with statusMsg := msg }
    | none, some msg => { initModel0 with statusMsg := msg }
    | none, none => initModel0
  let mut st : BareState := rebuildView {
    model := initModel, disk, blk?, vrng?, hasPl011, dwc3?, touch?, deconFlushBase?, gpioKeysBase?, komodo
  } true
  st ← renderIfDirty st
  log "TRICORDER_READY"

  -- 5. Main bare-metal single-threaded polling loop (zero interrupts, zero threads!)
  let fiLive ← Hw.fbInfo
  let hbActive := !hasPl011 && fiLive.base != 0 && fiLive.width == 1344 && fiLive.height ≥ 300 && fiLive.stride ≥ 1344
  let mkHbRow (b g r : UInt8) : ByteArray := Id.run do
    let mut arr := ByteArray.empty
    for _ in [0:16] do
      arr := arr.push b |>.push g |>.push r |>.push 0xFF
    return arr
  let hbRowGreen   := mkHbRow 0x66 0xFF 0x00
  let hbRowCyan    := mkHbRow 0xFF 0xCC 0x66
  let hbRowAmber   := mkHbRow 0x00 0xAA 0xFF
  let hbRowMagenta := mkHbRow 0xFF 0x00 0xFF
  let hbRowYellow  := mkHbRow 0x00 0xFF 0xFF
  let paintDot (lit : Bool) (row : ByteArray) : BaseIO Unit := do
    if hbActive && lit then
      let stride := fiLive.stride.toUInt64
      for dy in [0:16] do
        let off := ((260 + dy).toUInt64 * stride + 1260) * 4
        Hw.fbStore off row
      if let some decon := deconFlushBase? then
        Komodo.deconFlushFrame decon
  let mut running := true
  let mut lastGpioTick : UInt64 := 0
  let mut lastUsbUiTick : UInt64 := 0
  let mut lastHbTick : UInt64 := 0
  let mut hbPhase : Bool := false
  let mut lastShownEv : Nat := 0
  let mut shownClkGated : Bool := false
  let mut powerHoldTicks : Nat := 0
  let mut swallowTap : Bool := false
  let bootTicks := (← Hw.ticks).toNat
  st := { st with idle := { phase := .on, lastPerson := bootTicks, lastScreen := bootTicks } }
  while running do
    -- Poll serial / Wire transport on PL011 (QEMU) when announced
    let uartRes ← if st.hasPl011 then st.uart.pollInputOrWire else pure none
    match uartRes with
    | some (.inl byte) =>
      -- Interactive keyboard keys in QEMU console: w/k=prev, s/j=next, enter/space=select, q/esc=back/lock
      let key? : Option GpioKeys.KeyEvent := match byte with
        | 0x77 | 0x6b => some .prev   -- 'w' / 'k'
        | 0x73 | 0x6a => some .next   -- 's' / 'j'
        | 0x0d | 0x0a | 0x20 => some .select -- Enter / Space
        | 0x1b | 0x71 => some .back   -- Esc / 'q'
        | _ => none
      if let some k := key? then
        let (st', deliver) ← noteInput st .key
        st := st'
        if deliver then
          st ← handleKey st k
          st ← renderIfDirty st
    | some (.inr (.error err)) =>
      st.uart.sendFrame { op := .respErr, payload := err.toUTF8 }
    | some (.inr (.ok frame)) =>
      let (st', reply) ← handleFrame st frame
      st := st'
      st.uart.sendFrame reply
    | none =>
      -- Poll USB-C DWC3 Bulk-OUT `Kernel.Wire` transport on Pixel `komodo`
      -- Never block EP0 enumeration with full-screen redraws; only update UI once configured or after 1.5s idle!
      if let some usb := st.dwc3? then
        let wasCfg := usb.configured
        let (usb', frame?) ← usb.pollFrame
        st := { st with dwc3? := some usb' }
        if usb'.clkGated && !shownClkGated then
          shownClkGated := true
          st := rebuildView { st with model := { st.model with statusMsg := "USB CLK GATED (BUTTONS OK)" } } false
          st ← showIfChanged st
        else if !wasCfg && usb'.configured then
          lastShownEv := usb'.evSeen
          st := rebuildView { st with model := { st.model with statusMsg := s!"USB-C READY (1209:4701) EV={usb'.evSeen}" } } false
          st ← showIfChanged st
        else if !usb'.configured && usb'.evSeen != lastShownEv then
          let now ← Hw.ticks
          if lastUsbUiTick == 0 then
            lastUsbUiTick := now
          else if now - lastUsbUiTick ≥ 37000000 then -- ~1.5s after events settle
            lastShownEv := usb'.evSeen
            lastUsbUiTick := 0
            st := rebuildView { st with model := { st.model with statusMsg := s!"USB EV={usb'.evSeen} R={usb'.lastSetupReq} V={usb'.lastSetupVal}" } } false
            st ← showIfChanged st
        match frame? with
        | some (.error err) =>
          let usb'' ← usb'.sendFrame { op := .respErr, payload := err.toUTF8 }
          st := { st with dwc3? := some usb'' }
        | some (.ok frame) =>
          let (st', reply) ← handleFrame st frame
          st := st'
          if let some u := st.dwc3? then
            let u' ← u.sendFrame reply
            st := { st with dwc3? := some u' }
        | none => pure ()
      -- Poll physical Exynos GPIO_ALIVE keys (`gpa6-2` Vol+, `gpa4-1` Vol-, `gpa4-0` Power) at ~5ms intervals
      if let some gpio := st.gpioKeysBase? then
        let now ← Hw.ticks
        if now - lastGpioTick ≥ 125000 then
          lastGpioTick := now
          let (u, d, p) ← Komodo.sampleGpioKeys gpio
          if d && p then
            Hw.halt 99 -- Instant reboot to Fastboot when Power + VolDown held together!
          if u && p then
            let _ ← dispatch st .appPaused -- Wipe secrets from RAM before powering off!
            Hw.halt 98 -- Instant PSCI SYSTEM_OFF when Power + VolUp pressed together!
          if p then
            powerHoldTicks := powerHoldTicks + 1
            if powerHoldTicks ≥ 600 then -- ~3 seconds continuous Power hold -> clean Power Off!
              let _ ← dispatch st .appPaused
              Hw.halt 98
          else
            powerHoldTicks := 0
          let (keys', ev?) := st.keys.poll { volUp := u, volDown := d, power := p }
          st := { st with keys := keys' }
          if let some k := ev? then
            -- A press on a dark panel lights it and goes no further.
            let (st', deliver) ← noteInput st .key
            st := st'
            if deliver then
              paintDot true hbRowMagenta
              st ← handleKey st k
              paintDot true hbRowYellow
              st ← renderIfDirty st
              paintDot true hbRowGreen
        -- Live 2 Hz proof-of-life heartbeat LED in top-right OLED margin (`x=1260, y=260`)
        if hbActive && now - lastHbTick ≥ 12500000 then
          lastHbTick := now
          hbPhase := !hbPhase
          let row := if shownClkGated then hbRowAmber else if hbPhase then hbRowGreen else hbRowCyan
          paintDot (!st.dark) row
      -- The touchscreen: at most one message a turn of the loop, and at most one tap from it.
      if let some t := st.touch? then
        if st.dark then
          -- Dark, the controller is not read: only its interrupt line is looked at. When it has something
          -- to say the panel is lit, and the touch that lit it taps nothing.
          if ← KomodoTouch.waiting then
            st := (← noteInput st .stir).1
            swallowTap := true
        else
          let (t', tap?) ← t.poll 540 1200
          st := { st with touch? := some t' }
          if let some (x, y) := tap? then
            let (st', deliver) ← noteInput st .tap
            st := st'
            if swallowTap then
              swallowTap := false
            else if deliver then
              st ← handleTap st x y
              st ← renderIfDirty st
          else if swallowTap && t'.tap.start?.isNone && !(← KomodoTouch.waiting) then
            swallowTap := false
      -- The clocks: the lock, and the panel going dark.
      st := (← noteInput st .none).1
      -- Dark, every image sleeps between looks at the buttons, the glass and the cable. The sleep was
      -- seen to end on the phone in a regtest image before signet and mainnet images were given it.
      if st.dark then Hw.idleWait else Hw.pause
  return 0

def main : IO UInt32 := bareMain

end Tricorder.OsMain
