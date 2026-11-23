/-
  LeanVM.Guest.B1.VerifySub.H.Own

  `verify_sub`'s own buffers on an honest child and the oracle of its honest valuation: the
  allocations' pointers and the callees' returns.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Runs
public import LeanVM.Guest.B1.VerifySub.C.Own
public import LeanVM.Guest.B1.VerifySub.C.Hon
public import LeanVM.Guest.Hints
public import LeanVM.Guest.B1.Bits.GrindFwd

/-!
# The own buffers and the oracle

`ChildSegs.ownW`: the fifteen own buffers' honest words, in allocation order (`vs_allocs`, the
first words `vb bs i` of `H/Kids`): `claim_pool` (`verify_tables`' pool words), the stream
padded, `table_rows`, `dims_g`, `kappa_base`, `zeta` (the bus point), `ood_z` (the out-of-domain
point), `ood_value`, `fp_w` (the slot weights), `chi`, `bc_point` (the slot point), `z_vals` (the
committed outputs' point at `0`, the ring switch's at `qkeccakVarsCap`), `slices`, the ring map's
challenges, `c_table`. `vs_own_mem`: buffer `i` at its base.

`vsW gw bs outs`: the oracle (`C/Hon`'s `w`): an allocation's value is the pointer to its buffer, a
call's return its callee's result in `outs` (`vsRetVars`, callee by callee in call order), an
inlined grind's window the honest one of its word (`gw`: the out-of-domain grind's, the ring
map's).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- `z_vals`' words: the committed outputs' point, the ring switch's at `qkeccakVarsCap`. -/
def zvW (op kpt : List E) : List E := op ++ List.replicate (qkeccakVarsCap - op.length) 0 ++ kpt

theorem vs_count_eq_gen {n : ℕ} (_h : n < 2 ^ 64) : Hints.count n = gen ^ n := by
  rw [Hints.count, LeanVM.Protocol.Verifier.gpow]

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- The ring map's coefficients. -/
noncomputable def ctab : List E :=
  ringCoefficients (S.rchs.take ringMapWidth) (S.rchs.drop ringMapWidth)

/-- **The own buffers' honest words**, in allocation order. -/
noncomputable def ownW : List (List E) :=
  [S.H.poolW, vsStreamW c.proof.stream, S.rowsN.map eOfNat, vsDimsW S.logMem S.hs,
    vsKbW S.logMem S.hs, S.rG.2.1, S.oodZ, [S.oodV], S.wb.1, S.H.chiW, S.H.slots,
    zvW S.kOut.point S.kc.2.1, S.kc.2.2, S.rchs, S.ctab]

theorem ownW_length : S.ownW.length = 15 := rfl

/-- The heights as `count` are their powers. -/
theorem hs_count (hbl : bytecode.length = 2 ^ 23) : S.hs.map Hints.count = S.hs.map (gen ^ ·) :=
  List.map_congr_left fun x hx ↦ vs_count_eq_gen (by have := (S.hs_bounds hbl).1 x hx; omega)

theorem kbW_eq (hbl : bytecode.length = 2 ^ 23) :
    vsKbW S.logMem S.hs = 1 :: gen ^ S.logMem :: S.hs.map (gen ^ ·) := by
  rw [vsKbW, S.hs_count hbl]

end ChildSegs

theorem bases_length : ∀ (b : ℕ) (sizes : List ℕ), (bases b sizes).length = sizes.length
  | _, [] => rfl
  | b, s :: sizes => by simp [bases, bases_length (b + s) sizes]

/-- **The own buffers at the bump allocator's positions.** -/
theorem vs_own_mem {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    (b : ℕ) {i : ℕ} (hi : i < 15) :
    ((bases b (vsSizes)).getD i 0, S.ownW.getD i []) ∈ bufL b (vsSizes) S.ownW := by
  have hl : (bases b (vsSizes)).length = 15 := by rw [bases_length]; rfl
  rw [bufL, List.mem_iff_getElem]
  refine ⟨i, by simp [hl, S.ownW_length, hi], ?_⟩
  rw [List.getElem_zip, List.getD_eq_getElem _ _ (by omega),
    List.getD_eq_getElem _ _ (by rw [S.ownW_length]; omega)]

/-! ## The oracle -/

/-- The callees' return values, callee by callee in call order. -/
def vsRetVars : List (List ℕ) :=
  [[64], [72], [253], [274, 275], [276], [356, 357, 358, 359, 360],
    [364, 365, 366, 367, 368, 369, 370, 371], [380], [597, 598, 599, 600, 601, 602, 603],
    [608, 609, 610, 611, 612, 613, 614, 615, 616, 617], [625, 626, 627, 628, 629, 630, 631],
    [1432], [1992, 1993, 1994, 1995, 1996], []]

/-- The oracle's values are the allocations' and the returns'. -/
theorem vsWVars_eq : vsWVars.Perm (vsAllocVars ++ vsRetVars.flatten) := by decide

/-- **The oracle**: an allocation's pointer, a callee's return, a grind's window. -/
noncomputable def vsW (gw : E × E) (bs : List ℕ) (outs : List (List E × Main.Layout)) (n : ℕ) : E :=
  if n ∈ vsAllocVars then ofK (addressOfIndex (bs.getD (vsAllocVars.idxOf n) 0))
  else if 301 ≤ n ∧ n ≤ 301 + gcW 15 then gcWin 15 gw.1 (n - 301)
  else if 653 ≤ n ∧ n ≤ 653 + gcW 13 then gcWin 13 gw.2 (n - 653)
  else (outs.getD (vsRetVars.findIdx (n ∈ ·)) ([], [])).1.getD
    ((vsRetVars.getD (vsRetVars.findIdx (n ∈ ·)) []).idxOf n) 0

theorem vsAllocVars_idx : ∀ i < 15, vsAllocVars.getD i 0 ∈ vsAllocVars ∧
    vsAllocVars.idxOf (vsAllocVars.getD i 0) = i := by decide

theorem vsW_alloc (gw : E × E) (bs : List ℕ) (outs : List (List E × Main.Layout)) {i : ℕ} (hi : i < 15) :
    vsW gw bs outs (vsAllocVars.getD i 0) = ofK (addressOfIndex (bs.getD i 0)) := by
  obtain ⟨h1, h2⟩ := vsAllocVars_idx i hi
  simp only [vsW, h1, ↓reduceIte, h2]

theorem vsRetVars_idx : ∀ j < 14, ∀ k < (vsRetVars.getD j []).length,
    (vsRetVars.getD j []).getD k 0 ∉ vsAllocVars ∧
      ¬ (301 ≤ (vsRetVars.getD j []).getD k 0 ∧ (vsRetVars.getD j []).getD k 0 ≤ 301 + gcW 15) ∧
      ¬ (653 ≤ (vsRetVars.getD j []).getD k 0 ∧ (vsRetVars.getD j []).getD k 0 ≤ 653 + gcW 13) ∧
      vsRetVars.findIdx (((vsRetVars.getD j []).getD k 0) ∈ ·) = j ∧
      (vsRetVars.getD j []).idxOf ((vsRetVars.getD j []).getD k 0) = k := by decide

theorem vsW_ret (gw : E × E) (bs : List ℕ) (outs : List (List E × Main.Layout)) {j k : ℕ} (hj : j < 14)
    (hk : k < (vsRetVars.getD j []).length) :
    vsW gw bs outs ((vsRetVars.getD j []).getD k 0) = (outs.getD j ([], [])).1.getD k 0 := by
  obtain ⟨h1, g1, g2, h2, h3⟩ := vsRetVars_idx j hj k hk
  simp only [vsW, h1, g1, g2, ↓reduceIte, h2, h3]

theorem vsW_win1 (gw : E × E) (bs : List ℕ) (outs : List (List E × Main.Layout)) :
    ∀ j ≤ gcW 15, vsW gw bs outs (301 + j) = gcWin 15 gw.1 j := by
  intro j hj
  have hW : gcW 15 = 4 := by decide
  have hn : 301 + j ∉ vsAllocVars := by rw [hW] at hj; interval_cases j <;> decide
  simp only [vsW, hn, ↓reduceIte, show 301 ≤ 301 + j ∧ 301 + j ≤ 301 + gcW 15 by omega, and_self,
    Nat.add_sub_cancel_left]

theorem vsW_win2 (gw : E × E) (bs : List ℕ) (outs : List (List E × Main.Layout)) :
    ∀ j ≤ gcW 13, vsW gw bs outs (653 + j) = gcWin 13 gw.2 j := by
  intro j hj
  have hW : gcW 13 = 4 := by decide
  have hn : 653 + j ∉ vsAllocVars := by rw [hW] at hj; interval_cases j <;> decide
  simp only [vsW, hn, ↓reduceIte, show ¬ (301 ≤ 653 + j ∧ 653 + j ≤ 301 + gcW 15) by
    rw [show gcW 15 = 4 by decide]; omega,
    show 653 ≤ 653 + j ∧ 653 + j ≤ 653 + gcW 13 by omega, and_self, Nat.add_sub_cancel_left]

end
end LeanVM.Guest.B1.VerifySub
