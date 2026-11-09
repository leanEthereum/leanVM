import LeanVM.Guest.Fast.DiscreteLog

/-!
# Tests: the decoder's discrete logarithm, run

`discreteLog` (Pohlig–Hellman over the factors of `2^64 - 1`,
`Protocol/Extraction/Fast/DiscreteLog.lean`; proved: `discreteLog_eq_some_iff`) and the
decoder's readers over it (`Guest/Fast/DiscreteLog.lean`), evaluated:

* the logarithm of `g^n` is `n mod (2^64 - 1)`, at exponents across the range (small, at the
  baby-step strides, near the order), every nonzero word has one, and `0` has none;
* `cursorLenWith discreteLog p (p · gen^n)` is `n` for `n ≤ 2^32` and `0` past it, as
  `VerifySub.cursorLen`'s scan gives (`cursorLenWith_eq`);
* `gLogWith discreteLog`, B1's exponent of a power of `g` below `2^34` (`gLogWith_eq`).
-/

namespace LeanVMTests.Guest.DiscreteLog

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Extraction.Fast LeanVM.Guest.Fast
open LeanVM.Guest.Located

/-- A pseudo-random 64-bit word. -/
def lcg (s : ℕ) : ℕ := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Exponents across the range: small ones, the baby-step strides `2^12` and `2^16` and their
neighbours, the giant steps' ends, pseudo-random ones and the order's edge. -/
def exponents : List ℕ :=
  [0, 1, 2, 3, 640, 4095, 4096, 4097, 65535, 65536, 65537, 6700416, 6700417, 2 ^ 32, 2 ^ 34,
    2 ^ 63, 2 ^ 64 - 3, 2 ^ 64 - 2] ++ (List.range 16).map fun i ↦ lcg (i + 1) % (2 ^ 64 - 1)

/-- A pseudo-random word of `E`, its limbs nonzero or not as `s` falls. -/
def word (s : ℕ) : E :=
  E.ofLimbs (K.ofBits (if s % 3 = 0 then 0 else lcg s)) (K.ofBits (lcg (s + 1)))
    (K.ofBits (if s % 5 = 0 then 0 else lcg (s + 2)))

/-- The checks, the baby-step tables built once (`discreteLog` is `discreteLogWith` in
`discreteLogTables`), each named. -/
def checks : List (String × Bool) :=
  let T := discreteLogTables
  let dl := discreteLogWith T
  [("g^n", exponents.all fun n ↦ dl (addressOfIndex n) == some n),
    -- past the order, the exponent modulo it
    ("order", dl (addressOfIndex (2 ^ 64 - 1)) == some 0 && dl (addressOfIndex (2 ^ 64 + 5)) ==
        some 6),
    -- every nonzero word is a power of `g`, and its logarithm an exponent of it
    ("words", (List.range 32).all fun i ↦
      let x := K.ofBits (lcg (i + 100))
      x == 0 || (dl x).any fun n ↦ LeanVM.Parameters.addressOfIndex n == x && decide (n < 2 ^ 64 - 1)),
    ("zero", dl 0 == none),
    ("cursor", (List.range 8).all fun s ↦
      [0, 1, 7, 1000, 2 ^ 20, 2 ^ 32].all fun n ↦
        cursorLenWith dl (word s) (word s * gen ^ n) == n),
    ("cursor off", (List.range 4).all fun s ↦
      cursorLenWith dl (word s) (word s * gen ^ (2 ^ 32 + 1)) == 0 &&
        cursorLenWith dl (word s) (word (s + 1)) == 0 && cursorLenWith dl 0 (word s) == 0),
    ("gLog", ([0, 1, 5, 2 ^ 33, 2 ^ 34 - 1].all fun n ↦ gLogWith dl (ofK (addressOfIndex n))
        == n) &&
      gLogWith dl (ofK (addressOfIndex (2 ^ 34))) == 0 && gLogWith dl 0 == 0)]

/-- info: [] -/
#guard_msgs in
#eval (checks.filter fun c ↦ !c.2).map (·.1)

end LeanVMTests.Guest.DiscreteLog
