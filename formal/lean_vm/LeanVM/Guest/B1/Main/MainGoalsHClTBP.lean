/-
  LeanVM.Guest.B1.Main.MainGoalsHClTBP

  Each child's claim lists' digests on `main`'s honest run by trees of honest shape popping the child's slots'
  pushes (`Hints.childSlotPushes`), on either walk.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHClTB
public import LeanVM.Guest.B1.Main.L5R
public import LeanVM.Guest.B1.Digest.ClaimListsAtMP
public import LeanVM.Guest.B1.Main.MainPushes

/-!
# The children's claim lists, with their pops

* `slotGaps_eq`: the gaps between slots, by index; `ccPops_mono_eq`, `ccPops_any_eq`: a list's entries on either walk
  are its slots' pushes;
* `kidTB_hXP`, `kidTB_hSP`, `childListGoalsTBR_honest`: `kidTB_hX`, `kidTB_hS`, `childListGoalsTB_honest` by trees
  popping the slots' pushes.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (GuestLimits)
open LeanVM.Guest.Coverage (planSlots)
open LeanVM.Guest.Hints (claimCells)
open LeanVM.Guest.Coverage (coveragePlan CoverageRegion)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT CompleteAtDTB CompleteAtDTBR Returns bufL)
open LeanVM.Guest.B1.Digest (ccBM mStart mStart_succ MRec mGap gapPops idxPops ccPopsW)

@[expose] public section

variable {fs : String → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness}

theorem slotGaps_eq : ∀ (l : List ℕ) (nx : ℕ), Hints.slotGaps nx l =
    (List.range l.length).map fun j => l.getD j 0 - (if j = 0 then nx else l.getD (j - 1) 0 + 1)
  | [], _ => rfl
  | x :: l, nx => by
    rw [Hints.slotGaps, slotGaps_eq l (x + 1), List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    simp only [List.getD_cons_zero, ↓reduceIte, List.cons.injEq, true_and]
    refine List.map_congr_left fun j _ => ?_
    rcases j with _ | j <;> simp

theorem listSplit_eq {n : ℕ} (hn : n < 2 ^ 63) :
    Hints.listSplit n = [gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)] := by
  rw [Hints.listSplit, show Hints.claimBig = 136 from rfl, show Hints.claimGroup = 17 from rfl,
    Nat.mod_mod_of_dvd _ (by norm_num : 17 ∣ 136), gen_pow_count (by omega), gen_pow_count (by omega),
    gen_pow_count (by omega)]

/-- **A list on the gap walk pops its slots' pushes.** -/
theorem ccPops_mono_eq {os : List ℕ} (hinc : Hints.increasing os = true) (hn : os.length < 2 ^ 63)
    (hb : ∀ j < os.length, os.getD j 0 < 2 ^ 63) :
    ccPopsW os.length gen (gapPops (fun j => os.getD j 0) 0 os.length) = Hints.childSlotPushes os := by
  unfold ccPopsW Hints.childSlotPushes
  by_cases h0 : os = []
  · subst h0; rfl
  have hl : os.length ≠ 0 := fun h => h0 (List.eq_nil_of_length_eq_zero h)
  have h1 : (gen : E) = Hints.count 1 := by rw [← gen_pow_count (by norm_num), pow_one]
  simp only [hl, h0, hinc, ↓reduceIte]
  rw [listSplit_eq hn, slotGaps_eq, gapPops, List.map_map,
    show (("child_mono", [gen]) : String × List E) = ("child_mono", [Hints.count 1]) by rw [h1]]
  refine congrArg (List.cons _) (congrArg (List.cons _) (List.map_congr_left fun j hj => ?_))
  have hj' := List.mem_range.mp hj
  simp only [Function.comp_apply, Nat.zero_add, mGap, mStart]
  rw [gen_pow_count (lt_of_le_of_lt (Nat.sub_le _ _) (by have := hb j hj'; omega))]

/-- **A list on the walk by hinted indices pops its slots' pushes.** -/
theorem ccPops_any_eq {os : List ℕ} (hinc : Hints.increasing os = false) (hn : os.length < 2 ^ 63)
    (hb : ∀ j < os.length, os.getD j 0 < 2 ^ 63) :
    ccPopsW os.length (ccHint false) (idxPops (fun j => os.getD j 0) 0 os.length) =
      Hints.childSlotPushes os := by
  unfold ccPopsW Hints.childSlotPushes
  by_cases h0 : os = []
  · subst h0; rfl
  have hl : os.length ≠ 0 := fun h => h0 (List.eq_nil_of_length_eq_zero h)
  have h1 : ccHint false = Hints.count 0 := by rw [← gen_pow_count (by norm_num), pow_zero]; rfl
  simp only [hl, h0, hinc, ↓reduceIte, Bool.false_eq_true]
  rw [listSplit_eq hn, h1]
  refine congrArg (List.cons _) (congrArg (List.cons _) (List.ext_getElem (by simp [idxPops]) fun j h1 h2 => ?_))
  have hj : j < os.length := by simpa [idxPops] using h1
  simp only [idxPops, List.getElem_map, List.getElem_range, Nat.zero_add]
  rw [List.getD_eq_getElem _ _ hj, gen_pow_count (by have := hb j hj; rw [List.getD_eq_getElem _ _ hj] at this; omega)]

/-- **Child `c`'s leanXMSS list is complete**, on the walk the honest prover takes, by a tree popping its slots' pushes. -/
theorem kidTB_hXP (cert : String → V → ℕ) (hl : GuestLimits s w) {c : ℕ}
    (hc : c < w.children.length) {SB : String → ℕ}
    (hLS : TotalLe coreProgram fs "list_split" (fun _ => SB "list_split")) :
    CompleteAtDTBR fs cert 23 "child_claim_list_digest" (hLmain fs fp seed s w)
      [(hm fs fp seed s w).a77, (hm fs fp seed s w).a117, (hKid s w c).base,
        gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd), gen ^ (hKid s w c).ex]
      (Returns [(hKid s w c).cx.1, (hKid s w c).cx.2])
      (fun rd t => ccHonest (hKid s w c).ex (hMonoX s w c) t ∧
        t.pops coreProgram rd = Hints.childSlotPushes ((xPlan s w).childSlots.getD c []))
      (ccBM fs SB (hMonoX s w c) (hKid s w c).ex) := by
  have hcov := cover_bound hl
  have hlen := (hl.childClaimListsBelow2Pow23 _ (List.getElem_mem hc)).1
  have hT := kid_length_flatMap_const (f := fun c : LeanXmssClaim => claimCells c.1.root c.1.parameter c.2)
    (s.claims.xmss ++ (xPlan s w).duplicates) fun a _ => kid_length_claimCells _ _ _
  rw [List.length_append] at hT
  have slot := fun j (hj : j < w.children[c].statement.claims.xmss.length) =>
    plan_slot s.claims.xmss (w.xmssSignatures.map (·.1))
      (w.children.map (·.statement.claims.xmss)) (c := c) (j := j) (by simpa using hc)
      (by simpa using hj)
  set o : ℕ → ℕ := fun j => ((xPlan s w).childSlots.getD c []).getD j 0 with ho
  set L := s.claims.xmss.length + (xPlan s w).duplicates.length with hL
  have hlt : ∀ j < (hKid s w c).ex, o j < L := fun j hj => by
    rw [hKid_ex hc] at hj
    have := (slot j hj).1; rw [List.length_append] at this; exact this
  have hlenO : ((xPlan s w).childSlots.getD c []).length = (hKid s w c).ex := by
    rw [hKid_ex hc]
    unfold xPlan
    have hcl := congrArg List.length (plan_children_lengths s.claims.xmss (w.xmssSignatures.map (·.1))
      (w.children.map (·.statement.claims.xmss)))
    simp only [List.length_map] at hcl
    have e := congrArg (fun l => l.getD c 0) (plan_children_lengths s.claims.xmss (w.xmssSignatures.map (·.1))
      (w.children.map (·.statement.claims.xmss)))
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at e
    rw [List.getElem?_eq_getElem hc, List.getElem?_eq_getElem (by rw [hcl]; exact hc)] at e
    rw [List.getD_eq_getElem _ _ (by rw [hcl]; exact hc)]
    simpa using e
  have hbnd : ∀ j < ((xPlan s w).childSlots.getD c []).length,
      ((xPlan s w).childSlots.getD c []).getD j 0 < 2 ^ 63 :=
    fun j hj => lt_of_lt_of_le (hlt j (by omega)) (by omega)
  have hmk : ∀ rd, MemL rd (hLmain fs fp seed s w) → ∀ j < (hKid s w c).ex,
      LoadHolds rd (gen ^ hP fs fp seed s w 2 * gen ^ o j) 0
        ((hKid s w c).base * gen ^ (if hMonoX s w c then 0 else j)) := by
    intro rd hM j hj
    have hlt' := hlt j hj
    rw [hKid_ex hc] at hj
    obtain ⟨-, hidx, -⟩ := slot j hj
    obtain ⟨-, -, r4, -⟩ := reads_buf fs fp seed s w hM
    rw [loadHolds_mul_gen_pow, Nat.add_zero, show (hKid s w c).base *
      gen ^ (if hMonoX s w c then 0 else j) = gen ^ (hW s w c + if hMonoX s w c then 0 else j) from
        (pow_add _ _ _).symm]
    have := loadHolds_getD r4 (k := o j) (by rw [kid_length_hCover]; omega)
    rw [kid_hCover_x hlt', show (slotsOf (xPlan s w)).idxOf (o j) = _ from hidx,
      kid_hMarkX_child hc hj] at this
    exact this
  have hcl : ∀ rd, MemL rd (hLmain fs fp seed s w) → ∀ j < (hKid s w c).ex, ∀ i < 4,
      LoadHolds rd (gen ^ hP fs fp seed s w 0) (4 * o j + i)
        ((w.children[c].statement.claims.xmss.flatMap
          fun c => claimCells c.1.root c.1.parameter c.2).getD (4 * j + i) 0) := by
    intro rd hM j hj i hi
    rw [hKid_ex hc] at hj
    obtain ⟨hlt2, -, hget⟩ := slot j hj
    have h2 : o j < (s.claims.xmss ++ (xPlan s w).duplicates).length := hlt2
    obtain ⟨r1, -⟩ := reads_buf fs fp seed s w hM
    have := loadHolds_getD r1 (k := 4 * o j + i) (by rw [hT]; rw [List.length_append] at h2; omega)
    rw [getD_flatMap_uniform (f := fun c => claimCells c.1.root c.1.parameter c.2) _
      (fun a _ => kid_length_claimCells _ _ _) (o j) h2 i hi] at this
    have eT : (s.claims.xmss ++ (xPlan s w).duplicates)[o j]'h2 =
        w.children[c].statement.claims.xmss[j] := by
      have h := hget
      change (s.claims.xmss ++ (xPlan s w).duplicates)[o j]? = _ at h
      rw [List.getElem?_eq_getElem h2] at h
      simpa using h
    rw [eT] at this
    rw [getD_flatMap_uniform (f := fun c => claimCells c.1.root c.1.parameter c.2) _
      (fun a _ => kid_length_claimCells _ _ _) j hj i hi]
    exact this
  have hR2 : ∀ j < (hKid s w c).ex, RegionL (hLmain fs fp seed s w) (hP fs fp seed s w 2 + o j) :=
    fun j hj => region_buf fs fp seed s w (i := 2) (by omega)
      (show _ < (hCover s w).length by have := hlt j hj; rw [kid_length_hCover]; omega)
  have hR3 : ∀ j < (hKid s w c).ex, ∀ i < 4,
      RegionL (hLmain fs fp seed s w) (hP fs fp seed s w 0 + 4 * o j + i) := fun j hj i hi => by
    have := hlt j hj
    rw [Nat.add_assoc]
    exact region_buf fs fp seed s w (i := 0) (by omega)
      (show _ < ((s.claims.xmss ++ (xPlan s w).duplicates).flatMap
        fun c => claimCells c.1.root c.1.parameter c.2).length by rw [hT]; omega)
  have hcells : (w.children[c].statement.claims.xmss.flatMap
      fun c => claimCells c.1.root c.1.parameter c.2).length = 4 * (hKid s w c).ex := by
    rw [hKid_ex hc]; exact kid_length_flatMap_const _ fun a _ => kid_length_claimCells _ _ _
  have hn : (hKid s w c).ex < B1.Digest.claimBig * B1.Digest.bigFramesCap := by
    rw [hKid_ex hc]; simp only [B1.Digest.claimBig, B1.Digest.bigFramesCap]; omega
  rw [hKid_cx hc, xmssList_cells]
  have hn63 : ((xPlan s w).childSlots.getD c []).length < 2 ^ 63 := by
    rw [hlenO]; simp only [B1.Digest.claimBig, B1.Digest.bigFramesCap] at hn; omega
  cases hmono : hMonoX s w c
  · have := B1.Digest.child_claim_list_digest_completeAtTBP_any fs cert (κ := 23) (by norm_num)
      (Lin := hLmain fs fp seed s w) (eP := hP fs fp seed s w 0) (rg := hP fs fp seed s w 2)
      (L := L) (n := (hKid s w c).ex) (base := (hKid s w c).base) (o := o) ccHint_any hn hcells
      (by omega) (by omega)
      (fun rd hM j hj => ⟨belowLog_of (hlt j hj) (by omega), by
        have := hmk rd hM j hj
        simp only [hmono, Bool.false_eq_true, ↓reduceIte] at this
        rw [loadHolds_mul_gen_pow, Nat.add_zero] at this
        rw [loadHolds_mul_gen_pow, Nat.add_zero]
        exact this, hcl rd hM j hj⟩) hR2 hR3 hLS
    refine this.mono le_rfl fun _ _ h => ⟨h.1, h.2.trans ?_⟩
    rw [← hlenO]
    exact ccPops_any_eq (by rw [← hmono]; rfl) hn63 hbnd
  · have hinc : ∀ j < (hKid s w c).ex, mStart o j ≤ o j := by
      have hm' : Hints.increasing ((coveragePlan s.claims.xmss (w.xmssSignatures.map (·.1))
          (w.children.map (·.statement.claims.xmss))).childSlots.getD c []) = true := hmono
      have := plan_mono _ _ _ (c := c) (by simpa using hc) hm'
      intro j hj
      rw [hKid_ex hc] at hj
      exact this j (by simpa using hj)
    have := B1.Digest.child_claim_list_digest_completeAtTBP_mono fs cert (κ := 23) (by norm_num)
      (Lin := hLmain fs fp seed s w) (eP := hP fs fp seed s w 0) (rg := hP fs fp seed s w 2)
      (L := L) (n := (hKid s w c).ex) (base := (hKid s w c).base) (o := o) hn hcells
      (by omega) hinc (mStart_le_of hlt)
      (fun rd hM j hj => ⟨hlt j hj, by
        have := hmk rd hM j hj
        simp only [hmono, ↓reduceIte, pow_zero, mul_one] at this
        exact this, hcl rd hM j hj⟩) hR2 hR3 hLS
    refine this.mono le_rfl fun _ _ h => ⟨h.1, h.2.trans ?_⟩
    rw [← hlenO]
    exact ccPops_mono_eq (by rw [← hmono]; rfl) hn63 hbnd

/-- **Child `c`'s leanSPHINCS list is complete**, on the walk the honest prover takes, by a tree popping its slots' pushes. -/
theorem kidTB_hSP (cert : String → V → ℕ) (hl : GuestLimits s w) {c : ℕ}
    (hc : c < w.children.length) {SB : String → ℕ}
    (hLS : TotalLe coreProgram fs "list_split" (fun _ => SB "list_split")) :
    CompleteAtDTBR fs cert 23 "child_claim_list_digest" (hLmain fs fp seed s w)
      [(hm fs fp seed s w).a80,
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hKid s w c).base * gen ^ (hKid s w c).ex,
        gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd), gen ^ (hKid s w c).es]
      (Returns [(hKid s w c).cs.1, (hKid s w c).cs.2])
      (fun rd t => ccHonest (hKid s w c).es (hMonoS s w c) t ∧
        t.pops coreProgram rd = Hints.childSlotPushes ((sPlan s w).childSlots.getD c []))
      (ccBM fs SB (hMonoS s w c) (hKid s w c).es) := by
  have hcov := cover_bound hl
  have hlen := (hl.childClaimListsBelow2Pow23 _ (List.getElem_mem hc)).2
  have hT := kid_length_flatMap_const (f := fun c : LeanSphincsClaim => claimCells c.1.publicSeed c.1.root c.2)
    (s.claims.sphincs ++ (sPlan s w).duplicates) fun a _ => kid_length_claimCells _ _ _
  rw [List.length_append] at hT
  have slot := fun j (hj : j < w.children[c].statement.claims.sphincs.length) =>
    plan_slot s.claims.sphincs (w.sphincsSignatures.map (·.1))
      (w.children.map (·.statement.claims.sphincs)) (c := c) (j := j) (by simpa using hc)
      (by simpa using hj)
  set o : ℕ → ℕ := fun j => ((sPlan s w).childSlots.getD c []).getD j 0 with ho
  set L := s.claims.sphincs.length + (sPlan s w).duplicates.length with hL
  set rg := hP fs fp seed s w 2 + (s.claims.xmss.length + (xPlan s w).duplicates.length) with hrg
  have hlt : ∀ j < (hKid s w c).es, o j < L := fun j hj => by
    rw [hKid_es hc] at hj
    have := (slot j hj).1; rw [List.length_append] at this; exact this
  have hlenO : ((sPlan s w).childSlots.getD c []).length = (hKid s w c).es := by
    rw [hKid_es hc]
    unfold sPlan
    have hcl := congrArg List.length (plan_children_lengths s.claims.sphincs (w.sphincsSignatures.map (·.1))
      (w.children.map (·.statement.claims.sphincs)))
    simp only [List.length_map] at hcl
    have e := congrArg (fun l => l.getD c 0) (plan_children_lengths s.claims.sphincs (w.sphincsSignatures.map (·.1))
      (w.children.map (·.statement.claims.sphincs)))
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at e
    rw [List.getElem?_eq_getElem hc, List.getElem?_eq_getElem (by rw [hcl]; exact hc)] at e
    rw [List.getD_eq_getElem _ _ (by rw [hcl]; exact hc)]
    simpa using e
  have hbnd : ∀ j < ((sPlan s w).childSlots.getD c []).length,
      ((sPlan s w).childSlots.getD c []).getD j 0 < 2 ^ 63 :=
    fun j hj => lt_of_lt_of_le (hlt j (by omega)) (by omega)
  have hmk : ∀ rd, MemL rd (hLmain fs fp seed s w) → ∀ j < (hKid s w c).es,
      LoadHolds rd (gen ^ rg * gen ^ o j) 0
        ((hKid s w c).base * gen ^ (hKid s w c).ex * gen ^ (if hMonoS s w c then 0 else j)) := by
    intro rd hM j hj
    have hlt' := hlt j hj
    rw [hKid_es hc] at hj
    obtain ⟨-, hidx, -⟩ := slot j hj
    obtain ⟨-, -, r4, -⟩ := reads_buf fs fp seed s w hM
    rw [loadHolds_mul_gen_pow, Nat.add_zero, hrg, pow_add, loadHolds_mul_gen_pow, show (hKid s w c).base * gen ^ (hKid s w c).ex *
      gen ^ (if hMonoS s w c then 0 else j) =
        gen ^ (hW s w c + hEx w c + if hMonoS s w c then 0 else j) by rw [pow_add, pow_add]; rfl]
    have := loadHolds_getD r4 (k := s.claims.xmss.length + (xPlan s w).duplicates.length + o j)
      (by rw [kid_length_hCover]; omega)
    rw [kid_hCover_s hlt', show (slotsOf (sPlan s w)).idxOf (o j) = _ from hidx,
      kid_hMarkS_child hc hj] at this
    exact this
  have hcl : ∀ rd, MemL rd (hLmain fs fp seed s w) → ∀ j < (hKid s w c).es, ∀ i < 4,
      LoadHolds rd (gen ^ hP fs fp seed s w 1) (4 * o j + i)
        ((w.children[c].statement.claims.sphincs.flatMap
          fun c => claimCells c.1.publicSeed c.1.root c.2).getD (4 * j + i) 0) := by
    intro rd hM j hj i hi
    rw [hKid_es hc] at hj
    obtain ⟨hlt2, -, hget⟩ := slot j hj
    have h2 : o j < (s.claims.sphincs ++ (sPlan s w).duplicates).length := hlt2
    obtain ⟨-, r2, -⟩ := reads_buf fs fp seed s w hM
    have := loadHolds_getD r2 (k := 4 * o j + i) (by rw [hT]; rw [List.length_append] at h2; omega)
    rw [getD_flatMap_uniform (f := fun c => claimCells c.1.publicSeed c.1.root c.2) _
      (fun a _ => kid_length_claimCells _ _ _) (o j) h2 i hi] at this
    have eT : (s.claims.sphincs ++ (sPlan s w).duplicates)[o j]'h2 =
        w.children[c].statement.claims.sphincs[j] := by
      have h := hget
      change (s.claims.sphincs ++ (sPlan s w).duplicates)[o j]? = _ at h
      rw [List.getElem?_eq_getElem h2] at h
      simpa using h
    rw [eT] at this
    rw [getD_flatMap_uniform (f := fun c => claimCells c.1.publicSeed c.1.root c.2) _
      (fun a _ => kid_length_claimCells _ _ _) j hj i hi]
    exact this
  have hR2 : ∀ j < (hKid s w c).es, RegionL (hLmain fs fp seed s w) (rg + o j) := fun j hj => by
    have := hlt j hj
    rw [hrg, Nat.add_assoc]
    exact region_buf fs fp seed s w (i := 2) (by omega)
      (show _ < (hCover s w).length by rw [kid_length_hCover]; omega)
  have hR3 : ∀ j < (hKid s w c).es, ∀ i < 4,
      RegionL (hLmain fs fp seed s w) (hP fs fp seed s w 1 + 4 * o j + i) := fun j hj i hi => by
    have := hlt j hj
    rw [Nat.add_assoc]
    exact region_buf fs fp seed s w (i := 1) (by omega)
      (show _ < ((s.claims.sphincs ++ (sPlan s w).duplicates).flatMap
        fun c => claimCells c.1.publicSeed c.1.root c.2).length by rw [hT]; omega)
  have hcells : (w.children[c].statement.claims.sphincs.flatMap
      fun c => claimCells c.1.publicSeed c.1.root c.2).length = 4 * (hKid s w c).es := by
    rw [hKid_es hc]; exact kid_length_flatMap_const _ fun a _ => kid_length_claimCells _ _ _
  have hn : (hKid s w c).es < B1.Digest.claimBig * B1.Digest.bigFramesCap := by
    rw [hKid_es hc]; simp only [B1.Digest.claimBig, B1.Digest.bigFramesCap]; omega
  have ea : (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd) =
      gen ^ rg := by rw [hrg, pow_add (a := gen) (hP fs fp seed s w 2)]; rfl
  rw [hKid_cs hc, sphincsList_cells, ea]
  have hn63 : ((sPlan s w).childSlots.getD c []).length < 2 ^ 63 := by
    rw [hlenO]; simp only [B1.Digest.claimBig, B1.Digest.bigFramesCap] at hn; omega
  cases hmono : hMonoS s w c
  · have := B1.Digest.child_claim_list_digest_completeAtTBP_any fs cert (κ := 23) (by norm_num)
      (Lin := hLmain fs fp seed s w) (eP := hP fs fp seed s w 1) (rg := rg)
      (L := L) (n := (hKid s w c).es) (base := (hKid s w c).base * gen ^ (hKid s w c).ex) (o := o)
      ccHint_any hn hcells (by omega) (by omega)
      (fun rd hM j hj => ⟨belowLog_of (hlt j hj) (by omega), by
        have := hmk rd hM j hj
        simp only [hmono, Bool.false_eq_true, ↓reduceIte] at this
        rw [loadHolds_mul_gen_pow, Nat.add_zero] at this
        rw [loadHolds_mul_gen_pow, Nat.add_zero]
        exact this, hcl rd hM j hj⟩) hR2 hR3 hLS
    refine this.mono le_rfl fun _ _ h => ⟨h.1, h.2.trans ?_⟩
    rw [← hlenO]
    exact ccPops_any_eq (by rw [← hmono]; rfl) hn63 hbnd
  · have hinc : ∀ j < (hKid s w c).es, mStart o j ≤ o j := by
      have hm' : Hints.increasing ((coveragePlan s.claims.sphincs (w.sphincsSignatures.map (·.1))
          (w.children.map (·.statement.claims.sphincs))).childSlots.getD c []) = true := hmono
      have := plan_mono _ _ _ (c := c) (by simpa using hc) hm'
      intro j hj
      rw [hKid_es hc] at hj
      exact this j (by simpa using hj)
    have := B1.Digest.child_claim_list_digest_completeAtTBP_mono fs cert (κ := 23) (by norm_num)
      (Lin := hLmain fs fp seed s w) (eP := hP fs fp seed s w 1) (rg := rg)
      (L := L) (n := (hKid s w c).es) (base := (hKid s w c).base * gen ^ (hKid s w c).ex) (o := o)
      hn hcells (by omega) hinc (mStart_le_of hlt)
      (fun rd hM j hj => ⟨hlt j hj, by
        have := hmk rd hM j hj
        simp only [hmono, ↓reduceIte, pow_zero, mul_one] at this
        exact this, hcl rd hM j hj⟩) hR2 hR3 hLS
    refine this.mono le_rfl fun _ _ h => ⟨h.1, h.2.trans ?_⟩
    rw [← hlenO]
    exact ccPops_mono_eq (by rw [← hmono]; rfl) hn63 hbnd

/-- **The children's claim lists' digests on the honest run, by trees of honest shape popping their slots' pushes,
within `ccBM`.** -/
theorem childListGoalsTBR_honest (cert : String → V → ℕ)
    (hl : GuestLimits s w) {SB : String → ℕ}
    (hLS : TotalLe coreProgram fs "list_split" (fun _ => SB "list_split")) :
    ChildListGoalsTBR fs cert fp seed s w
      (fun rd c t => ccHonest (hKid s w c).ex (hMonoX s w c) t ∧
        t.pops coreProgram rd = Hints.childSlotPushes ((xPlan s w).childSlots.getD c []))
      (fun rd c t => ccHonest (hKid s w c).es (hMonoS s w c) t ∧
        t.pops coreProgram rd = Hints.childSlotPushes ((sPlan s w).childSlots.getD c []))
      (fun c => ccBM fs SB (hMonoX s w c) (hKid s w c).ex)
      (fun c => ccBM fs SB (hMonoS s w c) (hKid s w c).es) := fun _ hc =>
  ⟨kidTB_hXP cert hl hc hLS, kidTB_hSP cert hl hc hLS⟩

end
end LeanVM.Guest.B1.Main
