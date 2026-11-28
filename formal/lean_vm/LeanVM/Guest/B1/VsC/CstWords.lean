/-
  LeanVM.Guest.B1.VsC.CstWords

  `check_stack_terminal`'s own words: its ten buffers' honest contents.
-/

module

public import LeanVM.Guest.B1.VsC.CstVal
public import LeanVM.Guest.B1.VsC.RingRowsA

/-!
# `check_stack_terminal`'s own words

Its buffers, in allocation order from its cursor `c` (`cstBase`): `rchi` (`allocDyn`, `64 (|chi| + 1)`
words, the ring rows `rgRows`, which `ring_rows` checks), `pmask` (`33`, each pointer's mask
`maskW`), `rq` (`33`, the pointers' scales `rho · eq(qPoint, q)`), the four prefix chains (`42`
each: the row point `chi`, the Keccak output point `kOut`, the memory point `r`, the public input
point `rm, 0, …`; `chainW`), `pi_pt` (`31`, `rm` then zeros), `tq` (`126`, the slots' `eqtree`
levels, `tqW`), `ood_chain` (`31`, the chain of the out-of-domain point `z`). `cstWords` places them.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Stack LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The buffers' sizes, in allocation order. -/
def cstSizes (nchi : ℕ) : List ℕ := [64 * (nchi + 1), 33, 33, 42, 42, 42, 42, 31, 126, 31]

/-- Buffer `i`'s base from the cursor `c`. -/
def cstBase (nchi c i : ℕ) : ℕ := c + ((cstSizes nchi).take i).sum

/-- `pmask`: each pointer's mask. -/
def cstMaskW (layout : Layout) (x : List E) : List E := (List.range 33).map fun q => maskW layout x (ptrKinds.getD q 0)

/-- `rq`: the pointers' scales. -/
def cstRqW (rho : E) (qPoint : List E) : List E := (List.range 33).map fun q => rho * (eqKernel qPoint).getD q 0

/-- A prefix chain of the read words `as` against the opening point `x`, entries `0 ..= n`. -/
def chainW (as x : List E) (n : ℕ) : List E := (List.range (n + 1)).map (prefixProd 1 as (padX1 x))

/-- `pi_pt`: the public input point. -/
def piW (rm : E) : List E := rm :: List.replicate 30 0

/-- `tq`'s word at `o`: level `t = log₂(o + 2)` of the slots' `eqtree`, entry `o + 2 - 2^t`. -/
def tqEntry (layout : Layout) (x : List E) (o : ℕ) : E :=
  (eqKernel (((x.drop (hgt layout 5)).take 6).take (Nat.log 2 (o + 2)))).getD (o + 2 - 2 ^ Nat.log 2 (o + 2)) 0

/-- `tq`: the slots' `eqtree` levels `1 ..= 6`. -/
def tqW (layout : Layout) (x : List E) : List E := (List.range 126).map (tqEntry layout x)

/-- **`check_stack_terminal`'s own words** from its cursor `c`. -/
def cstWords (c : ℕ) (layout : Layout) (chi r qPoint kOut x z f g : List E) (rho rm : E) : Words :=
  let n := chi.length
  [(cstBase n c 0, rgRows (ringCoefficients f g) chi ((padX1 x).take n) n),
    (cstBase n c 1, cstMaskW layout x), (cstBase n c 2, cstRqW rho qPoint),
    (cstBase n c 3, chainW chi x n), (cstBase n c 4, chainW kOut x kOut.length),
    (cstBase n c 5, chainW r x layout.logMemory), (cstBase n c 6, chainW (piW rm) x layout.logMemory),
    (cstBase n c 7, piW rm), (cstBase n c 8, tqW layout x), (cstBase n c 9, chainW z x z.length)]

theorem cstSizes_sum (n : ℕ) : (cstSizes n).sum = 64 * (n + 1) + 422 := by
  simp [cstSizes]

end
end LeanVM.Guest.B1.VsC
