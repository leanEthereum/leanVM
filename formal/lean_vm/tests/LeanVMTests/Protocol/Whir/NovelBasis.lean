module

public import LeanVM.Protocol.Whir.ColumnWeight
meta import LeanVM.Protocol.Whir.ColumnWeight
meta import LeanVM.Parameters.Field
meta import CompPoly.Multilinear.Basic

/-!
# Binary Reed-Solomon code tests: subspace polynomials, encoder, column weights

Compiled checks (`#guard`) at `κ = 3`, `R = 1` (a 16-point domain):

* the encoder `enc` against an independent evaluation of `Σ_j g_j·X_j` built by coefficient-list
  arithmetic in this file (the `W_i` multiplied out of their linear factors, normalized, the
  `X_j` multiplied out, the sum evaluated by Horner), and `deg X_j = j` on those lists;
* negative tests: reading `⟨u⟩` high bit first, or reading the message as monomial
  coefficients, gives a different word; mutating the factor `1 + p(1 + Ŵ)` changes the induced
  weight;
* `K`-valued messages give `K`-valued words;
* `inducedWeight` against the naive `Σ_q w_q Σ_u W_{x_q}(u)·eq(p, u)`, its `none` branch, and the
  column weight's evaluator against CompPoly's `evalMle` and `Weight.pair`;
* constants from the pinned Python verifier (`python-verifier/verifier.py` at leanVM
  `a386121f84292f6fa663aaa3e570c15bc0240ea2`, run with CPython; both functions are unchanged at
  `127510d14c98ade4e8a97646c44fa7f1ff5e752d`, lines 964-992): `_subspace_roots(3)` and
  `_subspace_roots(4)`, and `_induced_weight(3, [0, 1, 5, 13], powers(E(2, 3, 4), 4), p)` at
  `p = [E(5, 7, 1), E(0x1234, 0, 9), E(3, 1, 0)]`.
-/

namespace LeanVMTests.Protocol.Whir

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Whir CompPoly CMlPolynomialEval

@[expose] public section

/-! ## Coefficient-list polynomials over `E` (low degree first) -/

/-- Sum of coefficient lists. -/
def pAdd : List E → List E → List E
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: pAdd p q

/-- Scalar multiple. -/
def pScale (c : E) (p : List E) : List E := p.map (c * ·)

/-- Product of coefficient lists. -/
def pMul : List E → List E → List E
  | [], _ => []
  | a :: p, q => pAdd (pScale a q) (0 :: pMul p q)

/-- Horner evaluation. -/
def pEval (p : List E) (a : E) : E := p.foldr (fun c acc ↦ c + a * acc) 0

/-- The degree of a coefficient list whose top coefficient is nonzero. -/
def pDeg (p : List E) : ℕ := p.length - 1

/-- `W_i = ∏_{v < 2^i} (X + x_v)`, multiplied out. -/
def wList (i : ℕ) : List E :=
  (List.range (2 ^ i)).foldl (fun acc v ↦ pMul acc [ofK (K.ofBits v), 1]) [1]

/-- `Ŵ_i = W_i / W_i(e_i)`. -/
def wHatList (i : ℕ) : List E := pScale (pEval (wList i) (ofK (K.ofBits (2 ^ i))))⁻¹ (wList i)

/-- `Ŵ_0, Ŵ_1, Ŵ_2`, each computed once where it is bound (an inverse in `E` is the costly
step of these checks). -/
def wHats : List (List E) := (List.range 3).map wHatList

/-- `X_j = ∏_{i < 3} Ŵ_i^{j_i}`, multiplied out from the given `Ŵ_i`. -/
def xList (hats : List (List E)) (j : ℕ) : List E :=
  (List.range 3).foldl (fun acc i ↦ if j.testBit i then pMul acc (hats.getD i []) else acc) [1]

/-- The polynomial with novel-basis coefficients `c_j` (index `j` = coefficient of `X_j`). -/
def novelSum (hats : List (List E)) (c : List E) : List E :=
  (List.range 8).foldl (fun acc j ↦ pAdd acc (pScale (c.getD j 0) (xList hats j))) []

/-- The polynomial with monomial coefficients `c_j`. -/
def monoSum (c : List E) : List E := c

/-- A word: the polynomial evaluated at `x_0, …, x_15`. -/
def word (p : List E) : List E := (List.range 16).map fun v ↦ pEval p (ofK (K.ofBits v))

/-! ## Messages -/

/-- The index `u_0 + 2u_1 + 4u_2`, written out independently of `bitsToNat`. -/
def idx (u : Fin 3 → Bool) : ℕ := (u 0).toNat + 2 * (u 1).toNat + 4 * (u 2).toNat

/-- The same bits read high bit first: `4u_0 + 2u_1 + u_2`. -/
def idxRev (j : ℕ) : ℕ := 4 * (j % 2) + 2 * (j / 2 % 2) + j / 4

/-- Novel-basis coefficients, `c_j` for `j < 8`. -/
def coeffsA : List E :=
  [E.ofLimbs (K.ofBits 1) 0 0, E.ofLimbs (K.ofBits 2) (K.ofBits 3) 0,
    E.ofLimbs (K.ofBits 5) 0 (K.ofBits 7), E.ofLimbs 0 (K.ofBits 11) 0,
    E.ofLimbs (K.ofBits 13) (K.ofBits 17) (K.ofBits 19), E.ofLimbs (K.ofBits 23) 0 0,
    E.ofLimbs 0 0 (K.ofBits 29), E.ofLimbs (K.ofBits 31) (K.ofBits 37) (K.ofBits 41)]

/-- A second message: one nonzero coefficient, on `X_6`. -/
def coeffsB : List E := [0, 0, 0, 0, 0, 0, E.ofLimbs (K.ofBits 9) (K.ofBits 4) 0, 0]

/-- A `K`-valued message. -/
def coeffsK : List K := [K.ofBits 3, 0, K.ofBits 8, K.ofBits 1, 0, K.ofBits 77, 0, K.ofBits 6]

/-- The message `u ↦ c_⟨u⟩`. -/
def msg (c : List E) (u : Fin 3 → Bool) : E := c.getD (idx u) 0

/-- The word of a message, as a list. -/
def encWord (c : List E) : List E := List.ofFn (enc 3 1 (msg c))

/-! ## The encoder against direct polynomial evaluation -/

-- `deg X_j = j` on the multiplied-out lists, with nonzero top coefficient.
#guard
  let hats := wHats
  (List.range 8).all fun j ↦ pDeg (xList hats j) == j && (xList hats j).getLast? != some 0
-- `Ŵ_i(e_i) = 1` and `deg W_i = 2^i`.
#guard
  let hats := wHats
  (List.range 3).all fun i ↦ pEval (hats.getD i []) (ofK (K.ofBits (2 ^ i))) == 1
#guard (List.range 4).all fun i ↦ pDeg (wList i) == 2 ^ i
-- `W_i` vanishes exactly on `U_i` inside the domain.
#guard (List.range 4).all fun i ↦ (List.range 16).all fun v ↦
  (pEval (wList i) (ofK (K.ofBits v)) == 0) == decide (v < 2 ^ i)
-- The computable evaluators agree with the lists.
#guard
  let hats := wHats
  (List.range 3).all fun i ↦ (List.range 16).all fun v ↦
    ofK (normVanishingAt i (K.ofBits v)) == pEval (hats.getD i []) (ofK (K.ofBits v))
/-- The coefficients permuted as if `⟨u⟩` were read high bit first. -/
def revCoeffs (c : List E) : List E := (List.range 8).map fun j ↦ c.getD (idxRev j) 0

-- The encoder is the evaluation of `Σ_j c_j X_j` on the domain. Negative tests: the bit order
-- is load-bearing (reading `⟨u⟩` high bit first is a different encoder), and the message is
-- not read as monomial coefficients. Each word is computed once per check.
#guard
  let hats := wHats
  let w := encWord coeffsA
  w = word (novelSum hats coeffsA) && w ≠ word (novelSum hats (revCoeffs coeffsA)) &&
    w ≠ word (monoSum coeffsA)
#guard
  let hats := wHats
  let w := encWord coeffsB
  w = word (novelSum hats coeffsB) && w ≠ word (novelSum hats (revCoeffs coeffsB))

/-! ## `K`-valued messages -/

/-- A `K`-valued message. -/
def msgK (u : Fin 3 → Bool) : K := coeffsK.getD (idx u) 0

-- Every entry of the word of a `K`-valued message lies in `K`, and is the `K`-encoder's.
#guard
  let w := List.ofFn (enc 3 1 fun u ↦ ofK (msgK u))
  w.all (fun z ↦ decide (IsInK z)) && w = List.ofFn fun v ↦ ofK (encK 3 1 msgK v)

/-! ## Column weights and the induced weight -/

/-- The point `p = [E(5, 7, 1), E(0x1234, 0, 9), E(3, 1, 0)]`. -/
def point : Vector E 3 :=
  #v[E.ofLimbs (K.ofBits 5) (K.ofBits 7) (K.ofBits 1),
    E.ofLimbs (K.ofBits 0x1234) 0 (K.ofBits 9), E.ofLimbs (K.ofBits 3) (K.ofBits 1) 0]

/-- The batching challenge `λ = E(2, 3, 4)`. -/
def lam : E := E.ofLimbs (K.ofBits 2) (K.ofBits 3) (K.ofBits 4)

/-- The queries. -/
def queries : List ℕ := [0, 1, 5, 13]

/-- Their weights `λ^0, …, λ^3`, the Python's `powers(lam, 4)`. -/
def weights : List E := (List.range 4).map (lam ^ ·)

/-- `eq(p, u) = ∏_i (u_i ? p_i : 1 + p_i)`. -/
def eqAt (p : Vector E 3) (u : Fin 3 → Bool) : E := ∏ i : Fin 3, if u i then p[i] else 1 + p[i]

/-- The naive batched weight `Σ_q w_q Σ_u W_{x_q}(u)·eq(p, u)`. -/
def naive (p : Vector E 3) : E :=
  ((weights.zip queries).map fun wq ↦
    wq.1 * ∑ u : Fin 3 → Bool, ofK (colWeight (K.ofBits wq.2) u) * eqAt p u).sum

-- The transcription agrees with the naive sum.
#guard inducedWeight 3 queries weights point.toList = some (naive point)
-- With the factor `1 + p(1 + Ŵ)` read as `1 + p·Ŵ` the sum would differ.
#guard (naive point) ≠ ((weights.zip queries).map fun wq ↦ wq.1 * ∏ i : Fin 3,
  (1 + point[i] * ofK (normVanishingAt i (K.ofBits wq.2)))).sum
-- The Python `require` and the strict `zip`.
#guard inducedWeight 2 queries weights point.toList = none
#guard inducedWeight 3 queries weights.tail point.toList = none
-- The evaluator of `colWeightE` is CompPoly's extension of its cube values.
#guard (List.range 16).all fun v ↦
  (colWeightE 3 (K.ofBits v)).mle point == evalMle (colWeightE 3 (K.ofBits v)).onCube point
-- A codeword entry is the pairing of the column weight with the message table.
#guard List.ofFn (enc 3 1 (msg coeffsA)) =
  List.ofFn fun v : Fin (2 ^ (3 + 1)) ↦
    (colWeightE 3 (K.ofBits v)).pair (RingHom.id E) (msgTable (msg coeffsA))

/-! ## Constants from the pinned Python verifier -/

/-- `_subspace_roots(4)` as printed by CPython: `W_i(e_i)` for `i ≤ 4`, all in `K`. -/
def pythonRoots4 : List E :=
  [ofK (K.ofBits 0x1), ofK (K.ofBits 0x6), ofK (K.ofBits 0x168), ofK (K.ofBits 0x1166880),
    ofK (K.ofBits 0x11616686880801b)]

#guard subspaceRoots 3 = pythonRoots4.take 4
#guard subspaceRoots 4 = pythonRoots4
-- The product definition of `W_i(e_i)` gives the same roots.
#guard (List.range 5).map (fun i ↦ ofK (vanishingAt i (basisVec i))) = pythonRoots4
-- `W_1(e_1) = x(x + 1) = x² + x`, the word `6`.
#guard vanishingAt 1 (basisVec 1) = K.ofBits 6

/-- `powers(E(2, 3, 4), 4)` as printed by CPython. -/
def pythonWeights : List E :=
  [E.ofLimbs (K.ofBits 0x1) 0 0, E.ofLimbs (K.ofBits 0x2) (K.ofBits 0x3) (K.ofBits 0x4),
    E.ofLimbs (K.ofBits 0x4) (K.ofBits 0x10) (K.ofBits 0x15),
    E.ofLimbs (K.ofBits 0x77) (K.ofBits 0x7) (K.ofBits 0x5e)]

/-- `_induced_weight(3, [0, 1, 5, 13], powers(E(2, 3, 4), 4), p)` as printed by CPython. -/
def pythonInduced : E :=
  E.ofLimbs (K.ofBits 0xb06534ea) (K.ofBits 0x4c3c056b) (K.ofBits 0x1f404c5bc)

#guard weights = pythonWeights
#guard inducedWeight 3 queries weights point.toList = some pythonInduced

end
end LeanVMTests.Protocol.Whir
