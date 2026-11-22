/-! # The rules of UTF-8

What makes bytes a character and a character bytes. `Mini/String.lean` knows where a string's bytes are and how
many there are; it hands the bytes in question here, as numbers, and is told what they mean.

Like the rest of `Runtime`, this is called before any module has been initialised, so it has no constant that
is built at start-up; it works on machine words alone and allocates nothing. -/

set_option compiler.extract_closed false

namespace Runtime.Utf8

/-- The six bits a continuation byte carries. -/
@[inline] def six (b : UInt8) : UInt32 := b.toUInt32 &&& 0x3F

@[inline] def continues (b : UInt8) : Bool := b &&& 0xC0 == 0x80

/-- How many bytes a well-formed character takes whose first four bytes are these, `available` of them
really there: one to four, or zero if what is there is not a well-formed character. No overlong forms, no
surrogates, nothing above U+10FFFF, nothing cut short. -/
@[export rt_utf8_strict]
def strict (b0 b1 b2 b3 : UInt8) (available : USize) : UInt8 :=
  if b0 < 0x80 then 1
  else if b0 &&& 0xE0 == 0xC0 then
    let value := ((b0.toUInt32 &&& 0x1F) <<< 6) ||| six b1
    if available > 1 && continues b1 && value ≥ 0x80 then 2 else 0
  else if b0 &&& 0xF0 == 0xE0 then
    let value := ((b0.toUInt32 &&& 0x0F) <<< 12) ||| (six b1 <<< 6) ||| six b2
    if available > 2 && continues b1 && continues b2 && value ≥ 0x800 && !(value ≥ 0xD800 && value ≤ 0xDFFF)
    then 3 else 0
  else if b0 &&& 0xF8 == 0xF0 then
    let value := ((b0.toUInt32 &&& 0x07) <<< 18) ||| (six b1 <<< 12) ||| (six b2 <<< 6) ||| six b3
    if available > 3 && continues b1 && continues b2 && continues b3 && value ≥ 0x10000 && value ≤ 0x10FFFF
    then 4 else 0
  else 0

/-- `String.get`'s reading of the bytes at a position, `available` of them really there: the character with
bit 32 set, or zero if Lean says no character starts there. The rules are Lean's, case for case: it does not
look at whether the later bytes are continuation bytes. -/
@[export rt_utf8_read]
def read (b0 b1 b2 b3 : UInt8) (available : USize) : UInt64 :=
  let found (c : UInt32) : UInt64 := c.toUInt64 ||| 0x100000000
  let two := ((b0.toUInt32 &&& 0x1F) <<< 6) ||| six b1
  let three := ((b0.toUInt32 &&& 0x0F) <<< 12) ||| (six b1 <<< 6) ||| six b2
  let four := ((b0.toUInt32 &&& 0x07) <<< 18) ||| (six b1 <<< 12) ||| (six b2 <<< 6) ||| six b3
  if b0 &&& 0x80 == 0 then found b0.toUInt32
  else if b0 &&& 0xE0 == 0xC0 && available > 1 && two ≥ 0x80 then found two
  else if b0 &&& 0xF0 == 0xE0 && available > 2 && three ≥ 0x800 && (three < 0xD800 || three > 0xDFFF) then found three
  else if b0 &&& 0xF8 == 0xF0 && available > 3 && four ≥ 0x10000 && four ≤ 0x10FFFF then found four
  else 0

/-- The UTF-8 encoding of a character: its bytes in the low 32 bits, first byte lowest, and how many there
are (one to four) above them. -/
@[export rt_utf8_write]
def write (c : UInt32) : UInt64 :=
  let lead (mark : UInt32) (shift : UInt32) : UInt64 := ((mark ||| (c >>> shift)) &&& 0xFF).toUInt64
  let tail (shift : UInt32) : UInt64 := ((0x80 : UInt32) ||| ((c >>> shift) &&& 0x3F)).toUInt64
  if c < 0x80 then c.toUInt64 ||| 0x100000000
  else if c < 0x800 then lead 0xC0 6 ||| (tail 0 <<< 8) ||| 0x200000000
  else if c < 0x10000 then lead 0xE0 12 ||| (tail 6 <<< 8) ||| (tail 0 <<< 16) ||| 0x300000000
  else lead 0xF0 18 ||| (tail 12 <<< 8) ||| (tail 6 <<< 16) ||| (tail 0 <<< 24) ||| 0x400000000

/-- How many bytes the character led by this byte claims. `String.next` steps by this, counting up to four
(`most` is 4); counting characters in bytes Lean already trusts goes up to six, as Lean's runtime does. A
byte that leads nothing claims one. -/
@[export rt_utf8_claims]
def claims (c : UInt8) (most : UInt8) : UInt8 :=
  if c &&& 0x80 == 0 then 1
  else if c &&& 0xE0 == 0xC0 then 2
  else if c &&& 0xF0 == 0xE0 then 3
  else if c &&& 0xF8 == 0xF0 then 4
  else if most > 4 && c &&& 0xFC == 0xF8 then 5
  else if most > 4 && c &&& 0xFE == 0xFC then 6
  else 1

end Runtime.Utf8
