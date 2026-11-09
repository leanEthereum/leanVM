/-
  LeanVMTests.Prover.Whir

  The executable code and opening (`Statement/Prover/Ntt.lean`, `Statement/Prover/Whir.lean`) on
  tiny inputs: the additive NTT against the encoder's formula, the level word against the
  specification's, the table of `Ŵ_c(e_m)` against the products, the query table against its
  defining sum.
-/

import Statement.Prover.Whir
import LeanVM.Protocol.Whir.Complete.Encoding

namespace LeanVMTests.Prover.Whir

open LeanVM.Parameters LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Complete LeanVM.Prover
open LeanVM.Protocol.Verifier

/-- A message of eight words. -/
def msg8 : Array K := ((List.range 8).map fun i ↦ K.ofBits (3 * i + 5)).toArray

/- The additive NTT at `κ = 3`, `R = 1` is the encoder's formula at every one of the 16
positions. -/
#guard (List.range 16).all fun p ↦
  (ntt (nttTwiddles 4 3) 3 1 msg8).getD p 0 == encKAt 3 (fun u ↦ msg8.getD (bitsToNat u) 0) p

/- And at `κ = 2`, `R = 2`. -/
#guard (List.range 16).all fun p ↦
  (ntt (nttTwiddles 4 2) 2 2 (msg8.extract 0 4)).getD p 0 ==
    encKAt 2 (fun u ↦ msg8.getD (bitsToNat u) 0) p

/- `Ŵ_c(x_n)` from the table is the product formula. -/
#guard (List.range 4).all fun c ↦ (List.range 20).all fun n ↦
  hatAt c n == normVanishingAt c (K.ofBits n)

/-- A table of `E` entries. -/
def tab8 : Array E :=
  ((List.range 8).map fun i ↦ E.ofLimbs (K.ofBits (i + 1)) (K.ofBits (7 * i)) (K.ofBits (i * i))).toArray

/- The level word at `κ = 2`, `k = 1`, `R = 1` is the specification's at every position, and
above the computed range too. -/
#guard (List.range 10).all fun p ↦ levelWordFast 2 1 1 tab8 p == levelWord 2 1 1 tab8.toList p

/- The query table: entry `i` is `Σ_q w_q·X_i(x_q)`. -/
#guard
  let qs := [3, 9, 14]
  let ws := [E.ofLimbs (K.ofBits 2) 0 1, E.ofLimbs (K.ofBits 5) (K.ofBits 1) 0, ofK (K.ofBits 9)]
  (List.range 8).all fun i ↦ (queryTableA 3 qs ws).getD i 0 ==
    ((List.zip ws qs).map fun wq ↦ wq.1 * ofK (novelAt i (K.ofBits wq.2))).sum

/- The equality kernel and the folds against the verifier's lists. -/
#guard
  let z := [E.ofLimbs (K.ofBits 2) 0 1, E.ofLimbs (K.ofBits 5) (K.ofBits 1) 0, ofK (K.ofBits 9)]
  (eqTable z).toList == eqKernel z && mleA tab8 z == multilinearEval tab8.toList z &&
    (foldPairsA (z.headD 0) tab8).toList == foldPairs (z.headD 0) tab8.toList

end LeanVMTests.Prover.Whir
