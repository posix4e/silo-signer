import MkBoot.ElfToImage
import MkBoot.BootImg
import MkBoot.Avb2
import Kernel.VaultStore
import Kernel.Wire
import Kernel.Fdt
import Kernel.GpioKeys

/-! # Pure-Lean Boot Image v4, AVB2 & Bare-Metal Kernel Subsystems Test Suite (`boot-img-test`)

Tests:
1. AOSP `boot_img_hdr_v4` pack/parse round-trip (zero ramdisk, cmdline preservation).
2. RSA-4096 AVB2 `vbmeta.img` + `avb_pkmd.bin` generation, cryptographic verification, AND
   1-byte tamper rejection on BOTH `boot.img` AND `vbmeta.img`!
3. End-to-end executable verification of `Kernel.VaultStore` (2-slot torn write & wipe),
   `Kernel.Wire` (CRC-32 round-trip & tamper rejection), and `Kernel.GpioKeys` debounce! -/

open MkBoot Kernel

private def expect (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then IO.println s!"ok    {name}"
  else throw <| IO.userError s!"FAIL  {name}: {detail}"

private def flipByte (b : ByteArray) (idx : Nat) : ByteArray :=
  if h : idx < b.size then b.set idx (b[idx] ^^^ 0x01) h else b

def main : IO Unit := do
  -- 1. BootImg v4 round-trip
  let fakeKernel := ByteArray.mk (Array.replicate 12345 0x42)
  let bootImg := BootImg.packV4 { kernel := fakeKernel, cmdline := "tricorder.net=regtest" }
  match BootImg.parseV4 bootImg with
  | .error e => throw <| IO.userError s!"BootImg.parseV4 failed: {e}"
  | .ok parsed =>
    expect "boot_img_hdr_v4 round-trip (kernel, 0 ramdisk, cmdline)"
      (parsed.kernel == fakeKernel && parsed.ramdisk.size == 0 && parsed.cmdline == "tricorder.net=regtest")

  -- 2. AVB2 RSA-4096 signing, avb_pkmd.bin, verification & 1-byte tamper rejection
  let tmpDir := "/tmp/tricorder-avb2-test"
  IO.FS.createDirAll tmpDir
  let keyPem := s!"{tmpDir}/avb.pem"
  let pubPem := s!"{tmpDir}/avb_pub.pem"
  let gen ← IO.Process.output { cmd := "openssl", args := #["genrsa", "-out", keyPem, "4096"] }
  if gen.exitCode != 0 then throw <| IO.userError s!"openssl genrsa failed: {gen.stderr}"
  let pub ← IO.Process.output { cmd := "openssl", args := #["rsa", "-in", keyPem, "-pubout", "-out", pubPem] }
  if pub.exitCode != 0 then throw <| IO.userError s!"openssl pubout failed: {pub.stderr}"

  let (vbmeta, pkmd) ← Avb2.signVbmeta "boot" bootImg keyPem
  expect s!"avb_pkmd.bin exact RSA-4096 size ({pkmd.size} == 1032B)" (pkmd.size == 8 + 512 + 512)
  let vOk ← Avb2.verifyVbmeta vbmeta bootImg pubPem
  expect "AVB2 RSA-4096 verifyVbmeta passes on clean boot.img + vbmeta.img" vOk.isOk

  let badBoot := flipByte bootImg 5000
  let vBadBoot ← Avb2.verifyVbmeta vbmeta badBoot pubPem
  expect "AVB2 rejects 1-byte tamper in boot.img" (!vBadBoot.isOk)

  let badVb := flipByte vbmeta 300
  let vBadVb ← Avb2.verifyVbmeta badVb bootImg pubPem
  expect "AVB2 rejects 1-byte tamper in vbmeta.img signature" (!vBadVb.isOk)

  -- 3. Zero-FS 2-slot VaultStore crash-consistency runtime test
  let d0 : VaultStore.DualDisk := { slot0 := VaultStore.zeroSlot, slot1 := VaultStore.zeroSlot }
  expect "VaultStore empty disk recovers none" (VaultStore.recover d0 == none)
  let d1 := VaultStore.commit d0 0 (some "VAULT_V1".toUTF8) none
  let d2 := VaultStore.commit d1 1 (some "VAULT_V1".toUTF8) (some "DESC_V2".toUTF8)
  -- Simulate torn write to the inactive slot (slot0, since d2 committed to slot1 with seq=2!)
  let (nextSlot, _) := VaultStore.planWrite d2
  let dTorn := d2.set nextSlot (flipByte (d2.get nextSlot) 100)
  match VaultStore.recover dTorn with
  | some (idx, rec) =>
    expect "VaultStore survives torn write to inactive slot"
      (idx == true && rec.seq == 2 && rec.failedAttempts == 1 && rec.descriptor? == some "DESC_V2".toUTF8)
  | none => throw <| IO.userError "VaultStore lost valid slot after torn write!"
  expect "VaultStore wipeBoth erases both slots" (VaultStore.recover (VaultStore.wipeBoth d2) == none)

  -- 4. Wire frame CRC-32 round-trip & 1-byte tamper rejection
  let frame : Wire.Frame := { op := .pushDescriptor, flags := 0, payload := "tr(NUMS,sortedmulti_a(2,...))".toUTF8 }
  let raw := Wire.encode frame
  let wireOk := match Wire.decode raw with | .ok f => f == frame | .error _ => false
  expect "Wire encode/decode round-trip" wireOk
  expect "Wire rejects 1-byte CRC tamper" (!(Wire.decode (flipByte raw 10)).isOk)

  -- 5. GpioKeys debounce & no-auto-repeat
  let (k1, e1) := ({} : GpioKeys.KeysState).poll { power := true }
  let (k2, e2) := k1.poll { power := true }
  let (k3, e3) := k2.poll { power := true }
  let (_,  e4) := k3.poll { power := true }
  expect "GpioKeys debounces 2 ticks, fires on tick 3, never auto-repeats on tick 4"
    (e1 == none && e2 == none && e3 == some .select && e4 == none)

  IO.println "boot-img-test: ALL BARE-METAL BOOTIMG, AVB2 & KERNEL TESTS PASSED!"
