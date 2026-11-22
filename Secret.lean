/-! # Comparing and choosing in time that does not depend on secrets

For code that holds a secret: `Secret.equal` compares byte arrays without stopping at the first difference,
and `Secret.select` chooses between two words without a branch. Both are programs in the small language
(`Mini/Secret.lean`), checked to let no secret decide a branch, an address or a division
(`Mini/Constant.lean`), and printed as C. -/

namespace Secret

@[extern "silo_secret_equal"]
private opaque equalBytes (a b : @& ByteArray) (size : USize) : Bool

/-- Whether `a` and `b` are equal, in time that depends only on their lengths. -/
def equal (a b : ByteArray) : Bool :=
  a.size == b.size && equalBytes a b a.size.toUSize

/-- `x` if `c`, otherwise `y`, without a branch on `c`. -/
@[extern "silo_secret_select"]
opaque select (c : Bool) (x y : UInt64) : UInt64

end Secret
