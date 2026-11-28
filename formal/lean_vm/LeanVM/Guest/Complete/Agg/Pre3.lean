module

public import LeanVM.Guest.Complete.Agg.Pre0

/-!
# `aggregate_claims_loop3`'s precondition at the honest data

`eq_cols` is the column factor at the sumcheck's point (`aEqc565`, by `eqcChain_sound` on the
window's atoms, which hold on every memory with `main`'s and the own words); `bc_wsum`'s words are
`aWsum`'s, so each child's step is `weight_rows`' (`agg_pre3`).
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC
open LeanVM.Guest.Complete LeanVM.Guest.B1.Digest
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

@[expose] public section

section
variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {cover : List E} {c : ℕ}

/-- `eq_cols`' atoms: sums, products of earlier values, loads. -/
def eKind : Atom → Bool
  | .add .. => true
  | .mul d a b => decide (a.idx < d.idx ∧ b.idx < d.idx)
  | .load .. => true
  | _ => false

theorem w8E_kind : ∀ x ∈ w8E, eKind x = true := by decide +kernel

theorem eqc_chain : eqcChainOk w8E (.n 156) (.n 467) 19 6 (.n 565) = true := by decide +kernel

/-- `bc_point1`'s words, back by `1 + ·`: the sumcheck's point, its first `n ≤ 25` coordinates. -/
theorem aPt1 (hl : (aLists s w).map List.length = aBufs w.children.length) (hp25 : (aPt w).length = 25)
    {rd : Reader} (hO : HoldsWords rd (aWo s w c)) {n : ℕ} (hn : n ≤ 25) :
    (memRun rd (ptrAt (aB c w.children.length 9)) n).map (1 + ·) = (aPt w).take n := by
  obtain ⟨hq9, hlen9⟩ := aWo_get (c := c) hl (j := 9) (by norm_num)
  refine List.ext_getElem (by simp [memRun, hp25]; omega) fun k h1 h2 => ?_
  simp only [memRun, List.getElem_map, List.getElem_range, List.getElem_take]
  simp only [memRun, List.length_map, List.length_range] at h1
  rw [memAt_of_load (load_at hO hq9 (i := 0) (by rw [Nat.add_zero]) (by rw [hlen9]; simp [aBufs]; omega) rfl),
    Nat.zero_add, show (aLists s w).getD 9 [] = (aPt w).map (1 + ·) from rfl, getD_map_lt (by omega),
    ← add_assoc, e_add_self, zero_add]
  exact List.getD_eq_getElem _ _ _

set_option maxRecDepth 20000 in
/-- **`eq_cols` is the column factor** at the sumcheck's point. -/
theorem aEqc565 (hr : NodeRelation guestBytecode guestSeed s w) (hne : w.children ≠ []) (hd : DeployedLimits s w)
    (hc : c < 2 ^ 62) {rd : Reader} (hA : APre al s w cover c rd) :
    aV al s w cover c (.n 565) = aEqc (aCols w) (aPt w) := by
  obtain ⟨h25, hp25, -, -⟩ := aBatched_facts hr hne
  have hl := aLists_length (s := s) h25 hp25
  have hn : w.children.length ≤ 16 := hd.atMostSixteenChildren
  obtain ⟨-, -, -, -, p156, -, -, -, -, p467, -⟩ := aV_ptrs (al := al) (s := s) (w := w) (cover := cover) (c := c)
  obtain ⟨-, fE⟩ := w8_fresh
  have hmemE : ∀ x ∈ w8E, x ∈ atomsOf aggP := fun x hx => w8_mem x (by
    simp only [w8A, List.mem_append]; exact Or.inl (Or.inr hx))
  have hAll := holds_aAll hA.2 hA.1
  have hat : ∀ x ∈ w8E, x.Holds rd (aV al s w cover c) := by
    intro x hx
    have g := aV_good (al := al) (s := s) (w := w) (cover := cover) (c := c) (hmemE x hx)
    have hk := w8E_kind x hx
    rcases w8E_split x hx with hN | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · cases x with
      | add d a b => exact g
      | mul d a b =>
        have h2 : a.idx < d.idx ∧ b.idx < d.idx := by simpa [eKind] using hk
        simp only [Good, h2, and_self, ↓reduceIte] at g
        exact g
      | _ => simp [eKind, isNL] at hk hN
    · exact (own_fresh hl hc hn (hmemE _ hx) (fE _ hx) p156 (by norm_num) (by simp [aBufs]; omega)).2 rd hAll
    · exact (own_fresh hl hc hn (hmemE _ hx) (fE _ hx) p467 (by norm_num) (by simp [aBufs]; omega)).2 rd hAll
  have h := eqcChain_sound (atoms := w8E) (rd := rd) (σ := aV al s w cover c) eqc_chain hat
  obtain ⟨hq4, hlen4⟩ := aWo_get (c := c) hl (j := 4) (by norm_num)
  have hcols : (aCols w).length = 6 := Whir.squeezeN_length splitLog _
  have e1 : memRun rd (ptrAt (aB c w.children.length 4)) 6 = aCols w := by
    refine List.ext_getElem (by simp [memRun, hcols]) fun k h1 h2 => ?_
    simp only [memRun, List.getElem_map, List.getElem_range]
    simp only [memRun, List.length_map, List.length_range] at h1
    rw [memAt_of_load (load_at hA.2 hq4 (i := 0) (by rw [Nat.add_zero]) (by rw [hlen4]; simp [aBufs]; omega) rfl),
      Nat.zero_add, show (aLists s w).getD 4 [] = aCols w from rfl]
    exact List.getD_eq_getElem _ _ _
  obtain ⟨hq9, hlen9⟩ := aWo_get (c := c) hl (j := 9) (by norm_num)
  have e2 : ((List.range 6).map fun j => 1 + memAt rd (ptrAt (aB c w.children.length 9)) (19 + j)) =
      (aPt w).drop 19 := by
    refine List.ext_getElem (by simp [hp25]) fun k h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range, List.getElem_drop]
    simp only [List.length_map, List.length_range] at h1
    rw [memAt_of_load (load_at hA.2 hq9 (i := 0) (by rw [Nat.add_zero]) (by rw [hlen9]; simp [aBufs]; omega) rfl),
      Nat.zero_add, show (aLists s w).getD 9 [] = (aPt w).map (1 + ·) from rfl, getD_map_lt (by omega),
      ← add_assoc, e_add_self, zero_add]
    exact List.getD_eq_getElem _ _ _
  rw [h, p156, p467, e1, e2]
  rfl

/-- **`aggregate_claims_loop3`'s precondition** at the honest data: `bc_wsum`'s records. -/
theorem agg_pre3 (hr : NodeRelation guestBytecode guestSeed s w) (hok : ChildrenOk guestBytecode guestSeed w)
    (hne : w.children ≠ []) (hd : DeployedLimits s w) (hc : c < 2 ^ 62) :
    ∀ rd, APre al s w cover c rd → ∀ j < w.children.length, ∃ pw w0 : E,
      LoadHolds rd (ptrAt (aB c w.children.length 1) * gen ^ j) 0 (ptrAt (mBase (mainCounts s w) 6 + 55 * j)) ∧
      LoadHolds rd (ptrAt (aB c w.children.length 2) * gen ^ j) 0 (ptrAt (mBase (mainCounts s w) 7 + 26 * j)) ∧
      (∀ i < 19, ∃ v, LoadHolds rd (ptrAt (mBase (mainCounts s w) 6 + 55 * j)) i v) ∧
      (∀ i < 25, ∃ v, LoadHolds rd (ptrAt (mBase (mainCounts s w) 7 + 26 * j)) i v) ∧
      (∀ i < 25, ∃ v, LoadHolds rd (ptrAt (aB c w.children.length 9)) i v) ∧
      LoadHolds rd (ptrAt (aB c w.children.length 7) * (gen ^ j) ^ 2) 0 pw ∧
      LoadHolds rd (ptrAt (aB c w.children.length 10) * gen ^ j) 0 w0 ∧
      LoadHolds rd (ptrAt (aB c w.children.length 10) * gen ^ j) 1 (w0 + pw *
        (eqEval (memRun rd (ptrAt (mBase (mainCounts s w) 6 + 55 * j)) 19)
          ((memRun rd (ptrAt (aB c w.children.length 9)) 19).map (1 + ·)) * aV al s w cover c (.n 565) +
          aV al s w cover c (.n 78) * eqEval (memRun rd (ptrAt (mBase (mainCounts s w) 7 + 26 * j)) 25)
            ((memRun rd (ptrAt (aB c w.children.length 9)) 25).map (1 + ·)))) := by
  intro rd hA j hj
  obtain ⟨h25, hp25, -, -⟩ := aBatched_facts hr hne
  have hl := aLists_length (s := s) h25 hp25
  have cc := claimCells_of hr hok
  have hM := hA.1.1
  have hO := hA.2
  have hmem : w.children[j] ∈ w.children := List.getElem_mem _
  have hpl := fresh_len hok _ hmem
  have hfc := cc.fresh _ hmem
  simp only [FreshClaim.cells, List.length_append] at hfc
  have hcc := cc.carried _ hmem
  simp only [DeferredBytecodeClaim.cells, List.length_append, List.length_singleton] at hcc
  have hfl : (w.children.flatMap (·.freshClaim.cells)).length = 55 * w.children.length :=
    flatMap_length_const cc.fresh
  have hcl : (w.children.flatMap (·.statement.deferredClaim.cells)).length = 26 * w.children.length :=
    flatMap_length_const cc.carried
  have hj' : j < (aCs w).length := by rw [aCs_length]; exact hj
  obtain ⟨hq9, hlen9⟩ := aWo_get (c := c) hl (j := 9) (by norm_num)
  obtain ⟨hq10, hlen10⟩ := aWo_get (c := c) hl (j := 10) (by norm_num)
  -- the claims' points
  have hfp : memRun rd (ptrAt (mBase (mainCounts s w) 6 + 55 * j)) 19 = (w.children[j]).freshClaim.point := by
    refine List.ext_getElem (by simp [memRun, hpl]) fun k h1 h2 => ?_
    simp only [memRun, List.getElem_map, List.getElem_range]
    simp only [memRun, List.length_map, List.length_range] at h1
    rw [memAt_of_load (load_at hM mem_main6 rfl (by omega) rfl), show 55 * j + k = j * 55 + k by omega,
      LeanVM.Protocol.Relation.getD_flatMap_uniform _ 55 0 w.children cc.fresh j k hj (by omega), FreshClaim.cells,
      List.getD_append _ _ _ _ (by omega)]
    exact List.getD_eq_getElem _ _ _
  have hcp : memRun rd (ptrAt (mBase (mainCounts s w) 7 + 26 * j)) 25 =
      (w.children[j]).statement.deferredClaim.bytecodePoint := by
    refine List.ext_getElem (by simp [memRun]; omega) fun k h1 h2 => ?_
    simp only [memRun, List.getElem_map, List.getElem_range]
    simp only [memRun, List.length_map, List.length_range] at h1
    rw [memAt_of_load (load_at hM mem_main7 rfl (by omega) rfl), show 26 * j + k = j * 26 + k by omega,
      LeanVM.Protocol.Relation.getD_flatMap_uniform _ 26 0 w.children cc.carried j k hj (by omega),
      DeferredBytecodeClaim.cells, List.getD_append _ _ _ _ (by omega)]
    exact List.getD_eq_getElem _ _ _
  have hp19 := aPt1 (c := c) hl hp25 hO (n := 19) (by norm_num)
  have hp25' := aPt1 (c := c) hl hp25 hO (n := 25) le_rfl
  rw [List.take_of_length_le (by omega)] at hp25'
  -- `bc_wsum`'s words
  have hw : ∀ i ≤ w.children.length, LoadHolds rd (ptrAt (aB c w.children.length 10) * gen ^ j) (i - j)
      (aWsum (aCs w) (aCols w) (aLam w) (aPt w) i) ∨ i < j := by
    intro i hi
    by_cases hij : i < j
    · exact Or.inr hij
    · refine Or.inl (load_at hO hq10 (i := j) (by rw [ptrAt_mul_gen_pow]) (by rw [hlen10]; simp [aBufs]; omega) ?_)
      rw [show j + (i - j) = i by omega, show (aLists s w).getD 10 [] = (List.range (w.children.length + 1)).map
        (aWsum (aCs w) (aCols w) (aLam w) (aPt w)) from rfl,
        List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
  have w0 := (hw j hj.le).resolve_right (by omega)
  have w1 := (hw (j + 1) (by omega)).resolve_right (by omega)
  rw [Nat.sub_self] at w0
  rw [show j + 1 - j = 1 by omega] at w1
  refine ⟨aLam w ^ (2 * j), _, aTab1 hl hO hj, aTab2 hl hO hj,
    fun i hi => ⟨_, load_at hM mem_main6 rfl (by omega) rfl⟩,
    fun i hi => ⟨_, load_at hM mem_main7 rfl (by omega) rfl⟩,
    fun i hi => ⟨_, load_at hO hq9 (i := 0) (by rw [Nat.add_zero]) (by rw [hlen9]; simp [aBufs]; omega) rfl⟩,
    by rw [ptr_pow]; exact aChainAt hl hO hj.le 0 (by simp [aChain]), w0, ?_⟩
  rw [hfp, hcp, hp19, hp25', aEqc565 hr hne hd hc hA, aLam78 hr hne hd hc]
  have e : aWsum (aCs w) (aCols w) (aLam w) (aPt w) (j + 1) = aWsum (aCs w) (aCols w) (aLam w) (aPt w) j +
      aLam w ^ (2 * j) * (eqEval (w.children[j]).freshClaim.point ((aPt w).take 19) * aEqc (aCols w) (aPt w) +
        aLam w * eqEval (w.children[j]).statement.deferredClaim.bytecodePoint (aPt w)) := by
    rw [aWsum, aWsum, lambdaPowers_eq, zip_prefix _ _ _ hj', ← lambdaPowers_eq, aCs_getElem hj']
    dsimp only
    ring
  rw [← e]
  exact w1

end

end
end LeanVM.Guest.Complete.Agg
