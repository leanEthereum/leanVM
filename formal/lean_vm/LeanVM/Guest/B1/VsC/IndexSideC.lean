/-
  LeanVM.Guest.B1.VsC.IndexSideC

  `index_side__L{w}` completes, layout-free.
-/

module

public import LeanVM.Guest.B1.VsC.FwdCalls
public import LeanVM.Guest.B1.VsC.IndexMleC
public import LeanVM.Guest.B1.Link.IndexSide
import LeanVM.Guest.CoreRef

/-!
# `index_side`, complete

`index_side(r, zeta, below, w)` calls `index_mle(r, w)`, folds `eq(ζ, r)` and its shift over the
`w` words at `zeta` and `r`, and stores `below[k] = Π_{k ≤ i < w} (1 + r_i)`, `k ≤ w`. By
`callCompletes_storesCalls`, the call's return the oracle's `indexMle rs`, on `index_mle`'s
completeness (`IndexMleComplete`): on every memory holding `rs` at `r`, `zs` at `zeta` and the
suffix products at `below`, on arrays apart, the call returns
`[indexMle rs, (sideFold zs rs).1, (sideFold zs rs).2.1]`, popping nothing, exact.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.KeccakGkr

@[expose] public section

/-- The input arrays of `index_side`: `rs` at `r`, `zs` at `zeta`. -/
def isIns (rs zs : List E) : List (ℕ × List E) := [(0, rs), (1, zs)]

/-- Its output array: the suffix products at `below`. -/
def isOuts (rs : List E) (w : ℕ) : List (ℕ × List E) := [(2, (List.range (w + 1)).map (belowE rs))]

/-- What `index_side__L{w}`'s completeness gives. -/
def IndexSideComplete (kd w : ℕ) (name : String) : Prop :=
  ∀ (r zeta below : E) (rs zs : List E), rs.length = w → zs.length = w →
    ArraysApart [r, zeta, below] [(0, w), (1, w), (2, w + 1)] →
    CallCompletes0 kd name [r, zeta, below] [indexMle rs, (sideFold zs rs).1, (sideFold zs rs).2.1]
      (fun rd ↦ HoldsArrays rd [r, zeta, below] (isIns rs zs) ∧
        HoldsArrays rd [r, zeta, below] (isOuts rs w))
      PostQuiet

theorem callsOfB_isBody (w : ℕ) :
    callsOfB (isBody w) = [⟨imNames.getD (w - 19) "", [.n 0], [.n 3], true⟩] := by
  have hb : ∀ k, (isBlk k).filterMap callOf? = [] := fun k => by unfold isBlk; split <;> rfl
  have ho : ∀ kk, (opsBlk (16 * w) 2 0 w kk).filterMap callOf? = [] := fun kk => by
    unfold opsBlk; split <;> rfl
  have hf : ∀ (f : ℕ → List Stmt), (∀ k, (f k).filterMap callOf? = []) → ∀ n,
      (((List.range n).map f).flatten).filterMap callOf? = [] := by
    intro f hf n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.flatten_append, List.filterMap_append, ih]
      simp [hf]
  unfold callsOfB isBody opsLoop
  simp only [List.filterMap_append, hf _ hb, hf _ ho]
  rfl

/-- **`index_side`'s template completes**, given `index_mle`'s completeness. -/
theorem is_complete {kd w : ℕ} {f : Fn} (h19 : 19 ≤ w) (h24 : w ≤ 24)
    (him : IndexMleComplete kd w (imNames.getD (w - 19) ""))
    (hfind : coreProgram.find? (isNames.getD (w - 19) "") = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2]) (hbody : f.body = isBody w)
    (hck : storeCallChecks 3 [(0, w), (1, w)] [(2, w + 1)] f.body = true) :
    IndexSideComplete kd w (isNames.getD (w - 19) "") := by
  intro r zeta below rs zs hrs hzs hap
  have hsh : shapeOf (isIns rs zs) = [(0, w), (1, w)] ∧ shapeOf (isOuts rs w) = [(2, w + 1)] := by
    simp [shapeOf, isIns, isOuts, hrs, hzs]
  have hsh' : shapeOf (isIns rs zs ++ isOuts rs w) = [(0, w), (1, w), (2, w + 1)] := by
    simp [shapeOf, isIns, isOuts, hrs, hzs]
  have hcall : Stmt.call (imNames.getD (w - 19) "") [.n 0] [.n 3] ∈ f.body := by
    rw [hbody, isBody]; simp
  refine callCompletes0_storesCalls (isIns rs zs) (isOuts rs w) (fun i ↦ if i = 3 then indexMle rs else 0)
    hfind (by rw [hparams]; rfl) (by rw [hsh.1, hsh.2]; exact hck) (by simp [isIns, isOuts])
    (by simp [isIns, isOuts]) (by rw [hsh']; exact hap) ?_ ?_
  · intro rd hl ⟨hin, _⟩
    rw [hbody, callsOfB_isBody]
    obtain ⟨t, hn, hv, hb, hq⟩ := him r rs hrs rd hl (hin (0, rs) (by simp [isIns]))
    refine ⟨[t], kidsValid_cons_taken rfl hn hv kidsValid_nil, ?_, ?_⟩
    · rw [Tree.BufsOkKids, Tree.BufsOkKids]; exact ⟨hb, trivial⟩
    · rw [List.map_cons, List.map_nil, kidsPost_cons]; exact ⟨fun _ ↦ hq, by simp [KidsPost]⟩
  · intro rd' σ vs hr hp hin hW hA
    have hH := holdsList_trivC hr hA
    rw [hparams] at hp
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
    obtain ⟨p0, p1, p2⟩ := hp
    have hidx : σ (.n 3) = indexMle rs := hW _ _ _ hcall (.n 3) (by simp)
    rw [hbody, isBody] at hH
    simp only [holdsList_append] at hH
    simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hH
    obtain ⟨-, h⟩ := hH
    rw [holdsList_range_flatten w isBlk isBlk_noRet] at h
    obtain ⟨hblk, h⟩ := h
    obtain ⟨⟨as, has, ras, hbel⟩, h⟩ := ops_run (16 * w) 2 0 w h
    obtain ⟨c0, c1, c2, hret⟩ := h
    have hb := fun k (hk : k < w) ↦ holds_isBlk (C := fun _ _ _ ↦ True) (rd := rd') k _ (hblk k hk)
    let x : ℕ → E := fun k ↦ σ (.n (isX k))
    let z : ℕ → E := fun k ↦ σ (.n (isZ k))
    have hS : ∀ k < w, (σ (.n (isEq k)), σ (.n (isSh k)), σ (.n (isCa k))) =
        ((List.range (k + 1)).map fun i ↦ (z i, x i)).foldl sideStep (1, 0, 1) := by
      intro k hk
      induction k with
      | zero => simpa using (hb 0 hk).2.2
      | succ k ih =>
        have e := (hb (k + 1) hk).2.2
        simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at e
        rw [e, ih (by omega), List.range_succ (n := k + 1), List.map_append, List.foldl_append]
        rfl
    have rx : ReadsAt rd' (σ (.n 0)) ((List.range w).map x) := readsAt_range_map fun k hk ↦ (hb k hk).1
    have rz : ReadsAt rd' (σ (.n 1)) ((List.range w).map z) := readsAt_range_map fun k hk ↦ (hb k hk).2.1
    have hr0 : ReadsAt rd' r rs := hin (0, rs) (by simp [isIns])
    have hz0 : ReadsAt rd' zeta zs := hin (1, zs) (by simp [isIns])
    rw [p0] at rx ras
    rw [p1] at rz
    have e1 : rs = (List.range w).map x := readsAt_unique hr0 rx (by simp [hrs])
    have e2 : as = (List.range w).map x := readsAt_unique ras rx (by simp [has])
    have e3 : zs = (List.range w).map z := readsAt_unique hz0 rz (by simp [hzs])
    have hf := hS (w - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at hf
    have hfold : sideFold zs rs =
        (σ (.n (isEq (w - 1))), σ (.n (isSh (w - 1))), σ (.n (isCa (w - 1)))) := by
      rw [hf, e1, e3, sideFold, zip_range_map]
    refine ⟨fun q hq ↦ ?_, ?_⟩
    · simp only [isOuts, List.mem_singleton] at hq
      subst hq
      show ReadsAt rd' below _
      rw [← p2]
      refine readsAt_range_map fun k hk ↦ ?_
      rw [e1, ← e2]
      exact hbel k (by omega)
    · rw [← hret, c0, c1, c2, hidx, hfold]

/-! ## The specializations -/

theorem imSpecNames_eq : imSpecNames = imNames := rfl

set_option maxRecDepth 100000 in
theorem index_side_L19_complete (kd : ℕ) : IndexSideComplete kd 19 (isNames.getD 0 "") :=
  is_complete (f := fn% «index_side__L19») (by omega) (by omega)
    (by have := index_mle_complete kd 19 (by omega) (by omega); rwa [imSpecNames_eq] at this)
    (coreProgram_find?_at (j := idx% «index_side__L19») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem index_side_L20_complete (kd : ℕ) : IndexSideComplete kd 20 (isNames.getD 1 "") :=
  is_complete (f := fn% «index_side__L20») (by omega) (by omega)
    (by have := index_mle_complete kd 20 (by omega) (by omega); rwa [imSpecNames_eq] at this)
    (coreProgram_find?_at (j := idx% «index_side__L20») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem index_side_L21_complete (kd : ℕ) : IndexSideComplete kd 21 (isNames.getD 2 "") :=
  is_complete (f := fn% «index_side__L21») (by omega) (by omega)
    (by have := index_mle_complete kd 21 (by omega) (by omega); rwa [imSpecNames_eq] at this)
    (coreProgram_find?_at (j := idx% «index_side__L21») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem index_side_L22_complete (kd : ℕ) : IndexSideComplete kd 22 (isNames.getD 3 "") :=
  is_complete (f := fn% «index_side__L22») (by omega) (by omega)
    (by have := index_mle_complete kd 22 (by omega) (by omega); rwa [imSpecNames_eq] at this)
    (coreProgram_find?_at (j := idx% «index_side__L22») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem index_side_L23_complete (kd : ℕ) : IndexSideComplete kd 23 (isNames.getD 4 "") :=
  is_complete (f := fn% «index_side__L23») (by omega) (by omega)
    (by have := index_mle_complete kd 23 (by omega) (by omega); rwa [imSpecNames_eq] at this)
    (coreProgram_find?_at (j := idx% «index_side__L23») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem index_side_L24_complete (kd : ℕ) : IndexSideComplete kd 24 (isNames.getD 5 "") :=
  is_complete (f := fn% «index_side__L24») (by omega) (by omega)
    (by have := index_mle_complete kd 24 (by omega) (by omega); rwa [imSpecNames_eq] at this)
    (coreProgram_find?_at (j := idx% «index_side__L24») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel)

/-- **Every `index_side__L{w}` completes**, `19 ≤ w ≤ 24`. -/
theorem index_side_complete (kd : ℕ) : ∀ w, 19 ≤ w → w ≤ 24 → IndexSideComplete kd w (isNames.getD (w - 19) "") := by
  intro w h1 h2
  interval_cases w
  exacts [index_side_L19_complete kd, index_side_L20_complete kd, index_side_L21_complete kd,
    index_side_L22_complete kd, index_side_L23_complete kd, index_side_L24_complete kd]

end
end LeanVM.Guest.B1.VsC
