import LeanVM.Protocol.Extraction.Fast.FFT.Additive
import LeanVM.Protocol.Extraction.Fast.FFT.PlannedEval
import LeanVMTests.Extraction.Toy

/-!
# Tests: the additive-FFT product over `K`

* the monomial ↔ novel conversions (`toNovel`, `fromNovel`) are inverse to each other on
  pseudo-random arrays of `2^J` entries, `J ≤ 7`;
* the transform's entries are the polynomial's values at `x_v` (`novelFwdPoly`);
* `novelInvPoly` inverts `novelFwdPoly`;
* `mulFFT` (proved equal to `p * q`) agrees with CompPoly's schoolbook product on pseudo-random
  polynomials of various sizes, above and below the cutoff, and the low-product contexts with the
  truncated products;
* the plan (`mkPlan j`): its twiddles by additivity are `novelTwiddles`, its batched inverses
  give `tableInvUpTo`, `planFwd`/`planInv` (one product per butterfly) are
  `novelFwd j 0`/`novelInv j`, and the conversions with the plan's powers and in place
  (`toNovelInPlace`, `fromNovelInPlace`) are `toNovel`, `fromNovel`, `j ≤ 9`;
* the evaluation-domain matrix products (`mulEvalP`, `mulTruncEvalP`) on the additive FFT agree
  with the naive ones;
* the axiom footprints of the end theorems.
-/

namespace LeanVMTests.Extraction.FFT

open CompPoly LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Extraction.Fast.FFT

/-- `n` pseudo-random elements of `K`. -/
def randomArray (seed n : ℕ) : Array K := (randoms seed n).map K.ofBits

/-- A pseudo-random polynomial of `n` coefficients. -/
def randomPoly (seed n : ℕ) : CPolynomial K := CPolynomial.ofArray (randomArray seed n)

-- The conversions are inverse to each other.
#guard (List.range 8).all fun J ↦
  let a := randomArray (J + 3) (2 ^ J)
  fromNovel J (toNovel J a) == a && toNovel J (fromNovel J a) == a

-- The plan.
#guard (List.range 10).all fun j ↦
  let P := mkPlan j
  let c := randomArray (j + 60) (2 ^ j)
  (List.range j).all (fun i ↦ P.twiddles.getD i #[] == novelTwiddles j i) &&
    P.tableInv == tableInvUpTo j && planFwd P c == novelFwd j 0 c && planInv P c == novelInv j c &&
    toNovelInPlace P c == toNovel j c && fromNovelInPlace P c == fromNovel j c

-- The forward transform evaluates.
#guard (List.range 7).all fun j ↦
  let p := randomPoly (j + 20) (2 ^ j)
  let y := novelFwdPoly j p
  (List.range (2 ^ j)).all fun v ↦ y.getD v 0 == p.eval (K.ofBits v)

-- A polynomial of fewer coefficients than points.
#guard
  let p := randomPoly 7 37
  let y := novelFwdPoly 7 p
  y.size == 128 && (List.range 128).all fun v ↦ y.getD v 0 == p.eval (K.ofBits v)

-- Interpolation inverts evaluation.
#guard (List.range 8).all fun j ↦
  let p := randomPoly (j + 40) (2 ^ j - j / 2)
  novelInvPoly j (novelFwdPoly j p) == p

/-- The transform from three coefficients on (schoolbook below). -/
def testSchedule : MulSchedule K := ⟨2, 2, CPolynomial.MulContext.naive⟩

-- The transform's product, against the schoolbook one.
#guard [(40, 50), (33, 33), (100, 37), (64, 65), (3, 300), (129, 128), (250, 7), (3, 3)].all
  fun (m, n) ↦
  let p := randomPoly (m + 1) m
  let q := randomPoly (n + 1000) n
  mulVia novelTransform testSchedule p q == p * q

-- `mulFFT`'s schedule: schoolbook, Karatsuba, then the transform (`2^13` points).
#guard [(1, 300), (40, 50), (1100, 1030), (4200, 40)].all fun (m, n) ↦
  let p := randomPoly (m + 1) m
  let q := randomPoly (n + 1000) n
  mulFFT p q == karatsubaMulContext.mul p q

-- Zero factors and constants.
#guard mulFFT 0 (randomPoly 5 100) == 0
#guard mulFFT (randomPoly 6 100) (CPolynomial.C (K.ofBits 3)) == randomPoly 6 100 * CPolynomial.C (K.ofBits 3)

-- A larger product, `2^10` points.
#guard
  let p := randomPoly 77 500
  let q := randomPoly 78 400
  mulVia novelTransform testSchedule p q == p * q

-- The truncated products.
#guard [(10, 50, 60), (70, 50, 60), (200, 50, 60), (45, 45, 45)].all fun (o, m, n) ↦
  let p := randomPoly (m + 7) m
  let q := randomPoly (n + 9) n
  mulLowVia novelTransform testSchedule o p q == PolynomialMatrix.truncateX o (p * q) &&
    CPolynomial.ofArray (rawMulLowVia novelTransform testSchedule o p.val q.val) ==
      PolynomialMatrix.truncateX o (p * q) &&
    fftMulLowContext.mulLow o p q == PolynomialMatrix.truncateX o (p * q)

/-- A pseudo-random `r × c` polynomial matrix, entries of `n` coefficients. -/
def randomMatrix (seed r c n : ℕ) : PolynomialMatrix K :=
  Array.ofFn fun i : Fin r ↦ Array.ofFn fun k : Fin c ↦ randomPoly (seed + 100 * i.val + k.val) n

-- The evaluation-domain matrix product on the additive FFT.
#guard
  let A := randomMatrix 1 3 4 20
  let B := randomMatrix 2 4 2 13
  mulEvalP novelTransform fftMulContext A B ==
    PolynomialMatrix.mulWith CPolynomial.MulContext.naive A B &&
  mulTruncEvalP novelTransform fftMulContext #[5, 30] A B ==
    PolynomialMatrix.truncateColumns #[5, 30] (PolynomialMatrix.mulWith CPolynomial.MulContext.naive A B)

/-- info: 'LeanVM.Extraction.Fast.FFT.mulFFT_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mulFFT_eq

end LeanVMTests.Extraction.FFT
