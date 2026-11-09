/-
  LeanVM.Guest.B1.VerifySub.H.Own

  `verify_sub`'s own buffers on an honest child, at the bump allocator's positions, and the oracle
  of its honest valuation: the allocations' pointers and the callees' returns.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Keccak
public import LeanVM.Guest.B1.VerifySub.C.Own
public import LeanVM.Guest.B1.Terminal.Interface

/-!
# The own buffers and the oracle

`ChildSegs.ownW`: the thirteen own buffers' honest words, in allocation order (`vs_allocs`):
`claim_pool` (`verify_tables`' pool words), the stream padded, `table_rows`, `dims_g`,
`kappa_base`, `zeta` (the bus point), `bus_alpha`, `fp_w`, `chi`, `z_vals` (the committed outputs'
point at `0`, the ring switch's at `39`), `slices`, the ring map's challenges, `c_table`.

`vsW bs outs`: the oracle: an allocation's value is the pointer to its buffer (`bs`, the buffers'
first words), a call's return is its callee's result in `outs` (`vsRetVars`, by callee).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

/-- `z_vals`' words: the committed outputs' point, the ring switch's at `39`. -/
def zvW (op kpt : List E) : List E := op ++ List.replicate (39 - op.length) 0 ++ kpt

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- The batching challenge. -/
def lam : E := S.s8.squeeze.1

/-- The ring map's six challenges. -/
def rchs : List E := S.m0 :: S.chs

/-- **The own buffers' honest words**, in allocation order. -/
noncomputable def ownW : List (List E) :=
  [S.H.poolW, vsStreamW c.proof.stream, S.rowsN.map eOfNat, vsDimsW S.logMem S.hs,
    vsKbW S.logMem S.hs, S.point, S.alphas, eqKernel S.alphas, S.chis, zvW S.op S.kpt, S.slices,
    S.rchs, ringCoefficients S.rchs]

end ChildSegs

/-! ## The oracle -/

/-- The callees' return values, callee by callee in call order. -/
def vsRetVars : List (List ℕ) :=
  [[120], [128], [309], [344], [345], (List.range 9).map (626 + ·), (List.range 10).map (636 + ·),
    (List.range 8).map (651 + ·), [1091], [1682, 1683], [1684], (List.range 5).map (1700 + ·), []]

/-- **The oracle**: an allocation's pointer, a callee's return. -/
noncomputable def vsW (bs : List ℕ) (outs : List (List E × Main.Layout)) (n : ℕ) : E :=
  if n ∈ vsAllocVars then ofK (addressOfIndex (bs.getD (vsAllocVars.idxOf n) 0))
  else (outs.getD (vsRetVars.findIdx (n ∈ ·)) ([], [])).1.getD
    ((vsRetVars.getD (vsRetVars.findIdx (n ∈ ·)) []).idxOf n) 0

theorem vsAllocVars_idx : ∀ i < 13, vsAllocVars.getD i 0 ∈ vsAllocVars ∧
    vsAllocVars.idxOf (vsAllocVars.getD i 0) = i := by decide

theorem vsW_alloc (bs : List ℕ) (outs : List (List E × Main.Layout)) {i : ℕ} (hi : i < 13) :
    vsW bs outs (vsAllocVars.getD i 0) = ofK (addressOfIndex (bs.getD i 0)) := by
  obtain ⟨h1, h2⟩ := vsAllocVars_idx i hi
  simp only [vsW, h1, ↓reduceIte, h2]

theorem vsRetVars_idx : ∀ j < 13, ∀ k < (vsRetVars.getD j []).length,
    (vsRetVars.getD j []).getD k 0 ∉ vsAllocVars ∧
      vsRetVars.findIdx (((vsRetVars.getD j []).getD k 0) ∈ ·) = j ∧
      (vsRetVars.getD j []).idxOf ((vsRetVars.getD j []).getD k 0) = k := by decide

theorem vsW_ret (bs : List ℕ) (outs : List (List E × Main.Layout)) {j k : ℕ} (hj : j < 13)
    (hk : k < (vsRetVars.getD j []).length) :
    vsW bs outs ((vsRetVars.getD j []).getD k 0) = (outs.getD j ([], [])).1.getD k 0 := by
  obtain ⟨h1, h2, h3⟩ := vsRetVars_idx j hj k hk
  simp only [vsW, h1, ↓reduceIte, h2, h3]

end
end LeanVM.Guest.B1.VerifySub
