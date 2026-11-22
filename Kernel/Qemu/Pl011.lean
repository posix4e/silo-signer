import Kernel.Hw
import Kernel.Wire

/-! # ARM PL011 UART Polled Driver (`Kernel.Qemu.Pl011`)

Drives QEMU `-M virt`'s PL011 UART (`0x09000000`) through the capability-checked `Kernel.Hw`
window interface (zero raw pointers). Supports:
- Console log output
- Non-blocking byte reception
- Complete length-prefixed `Kernel.Wire` frame TX/RX over a QEMU serial Unix socket! -/

namespace Kernel.Qemu.Pl011

def defaultBase : UInt64 := 0x09000000
def regDR : UInt64 := 0x000
def regFR : UInt64 := 0x018
def flagRXFE : UInt32 := (1 : UInt32) <<< 4 -- Receive FIFO empty
def flagTXFF : UInt32 := (1 : UInt32) <<< 5 -- Transmit FIFO full

structure Uart where
  base : UInt64 := defaultBase
  deriving Repr, Inhabited

/-- Writes one byte, spinning with `Hw.pause` only while the TX FIFO is full. -/
def Uart.writeByte (u : Uart) (b : UInt8) : BaseIO Unit := do
  let mut guard := 0
  while guard < 1000000 do
    let fr ← Hw.read32 (u.base + regFR)
    if (fr &&& flagTXFF) == 0 then break
    Hw.pause
    guard := guard + 1
  Hw.write32 (u.base + regDR) b.toUInt32

def Uart.writeBytes (u : Uart) (bs : ByteArray) : BaseIO Unit := do
  for i in [0:bs.size] do
    u.writeByte (bs.get! i)

/-- Non-blocking single-byte read (`none` if RX FIFO is empty). -/
def Uart.tryReadByte (u : Uart) : BaseIO (Option UInt8) := do
  let fr ← Hw.read32 (u.base + regFR)
  if (fr &&& flagRXFE) != 0 then return none
  let dr ← Hw.read32 (u.base + regDR)
  return some (dr &&& 0xff).toUInt8

/-- Blocking single-byte read up to `maxPolls` polls (returns `none` on timeout). -/
def Uart.readByteTimeout (u : Uart) (maxPolls : Nat := 2000000) : BaseIO (Option UInt8) := do
  for _ in [0:maxPolls] do
    match ← u.tryReadByte with
    | some b => return some b
    | none => Hw.pause
  return none

/-- Non-blocking check for a `Kernel.Wire` frame starting with `"TRIW"`.
If a non-`'T'` byte arrives when idle, returns it as a raw console key byte (`Sum.inl b`);
if `"TRIW"` arrives, reads the complete length-prefixed frame and verifies its CRC-32 (`Sum.inr f`). -/
def Uart.pollInputOrWire (u : Uart) : BaseIO (Option (Sum UInt8 (Except String Wire.Frame))) := do
  let some b0 ← u.tryReadByte | return none
  if b0 != 0x54 then -- not 'T' -> direct single-key control byte
    return some (.inl b0)
  -- Check for "RIW" following 'T'
  let some b1 ← u.readByteTimeout 500000 | return some (.inl b0)
  if b1 != 0x52 then return some (.inl b0)
  let some b2 ← u.readByteTimeout 500000 | return some (.inr (.error "truncated magic b2"))
  let some b3 ← u.readByteTimeout 500000 | return some (.inr (.error "truncated magic b3"))
  if b2 != 0x49 || b3 != 0x57 then return some (.inr (.error "bad wire magic"))
  -- Read remaining 4 header bytes: op, flags, lenLo, lenHi
  let mut buf := ByteArray.mk #[b0, b1, b2, b3]
  for _ in [0:4] do
    let some b ← u.readByteTimeout 1000000 | return some (.inr (.error "truncated wire header"))
    buf := buf.push b
  let len := Wire.readU16Le buf 6
  if len > Wire.maxPayload then
    return some (.inr (.error "wire payload exceeds maxPayload"))
  -- Read payload + 4-byte CRC-32
  for _ in [0:(len + Wire.trailerSize)] do
    let some b ← u.readByteTimeout 2000000 | return some (.inr (.error "truncated wire body"))
    buf := buf.push b
  return some (.inr (Wire.decode buf))

/-- Transmits a complete CRC-32-protected `Kernel.Wire.Frame`. -/
def Uart.sendFrame (u : Uart) (f : Wire.Frame) : BaseIO Unit :=
  u.writeBytes (Wire.encode f)

end Kernel.Qemu.Pl011
