module

public import LeanVM.Guest.Complete.Claims.KidList
public import LeanVM.Guest.Complete.RawFields
public import LeanVM.Guest.Complete.MainBytes
public import LeanVM.Guest.Memory.GuestWordsA

/-!
# The children's claim lists, at `main`

`kidsListsOpenE`: `MainCalleesOpenAt`'s fields `kidx`, `kids` on every node, for every coverage
table carrying the children's marks (`KidCover`), their ends within `2^40` of a cursor below `2^60`
(`KidsListsOpenE`, iface's `AtEveryB … (2^60) (2^40)` unfolded); `kidsListsOpen` the same at the
deployed choices, in `KidsListsOpen`'s `AtEveryB` form. Child `c`'s slots are the plan's (`xPlan s w`, `sPlan s w`), its claims the
table's there (`B1.Main.plan_child`), its marks the cover's (`KidCover`), so `kidList_atEvery`
applies with `L = sx` (resp. `ss`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak LeanVM.Guest.B1.Digest LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- **The children's claim lists, their ends bounded**: `KidsListsOpen` with `AtEveryE`. -/
def KidsListsOpenE (al : String → Bool) (k : ℕ) : Prop :=
  ∀ (s : NodeStatement) (w : NodeWitness) (cover : List E), NodeRelation guestBytecode guestSeed s w →
    DeployedLimits s w → ChildrenOk guestBytecode guestSeed w →
    cover.length = (mainCounts s w).sx + (mainCounts s w).ss → KidCover s w cover →
    (∀ c (hc : c < w.children.length), AtEveryE al k "child_claim_list_digest"
      [mPtr (mainCounts s w) 0 0, mPtr (mainCounts s w) 2 0, gen ^ kidBase w c, gen ^ (mainCounts s w).sx,
        gen ^ w.children[c].statement.claims.xmss.length]
      (Prover.digestCells (claimListDigest xmssPublicKeyBytes w.children[c].statement.claims.xmss))
      (mainR al (mainCounts s w)) (MainPreA al s w cover)
      (PopsPost (Prover.childSlotPushes ((xPlan s w).childSlots.getD c [])))
      (B2C.fs "child_claim_list_digest") (mLo al (mainCounts s w))) ∧
    (∀ c (hc : c < w.children.length), AtEveryE al k "child_claim_list_digest"
      [mPtr (mainCounts s w) 1 0, mPtr (mainCounts s w) 2 (mainCounts s w).sx,
        gen ^ kidBase w c * gen ^ w.children[c].statement.claims.xmss.length, gen ^ (mainCounts s w).ss,
        gen ^ w.children[c].statement.claims.sphincs.length]
      (Prover.digestCells (claimListDigest Sphincs.PublicKey.toBytes w.children[c].statement.claims.sphincs))
      (mainR al (mainCounts s w)) (MainPreA al s w cover)
      (PopsPost (Prover.childSlotPushes ((sPlan s w).childSlots.getD c [])))
      (B2C.fs "child_claim_list_digest") (mLo al (mainCounts s w)))

/-- `KidsListsOpen` is `KidsListsOpenE` (`AtEveryB … (2^60) (2^40)` is `AtEveryE` unfolded). -/
theorem KidsListsOpenE.toOpen {al : String → Bool} {k : ℕ} (h : KidsListsOpenE al k) : KidsListsOpen al k := h

/-! ## The plan -/

theorem getD_length_of_map {α : Type} {L1 : List (List ℕ)} {L2 : List (List α)}
    (h : L1.map List.length = L2.map List.length) {c : ℕ} (hc : c < L2.length) :
    (L1.getD c []).length = (L2[c]).length := by
  have hl : L1.length = L2.length := by simpa using congrArg List.length h
  rw [List.getD_eq_getElem _ _ (by omega)]
  have e := List.getElem_of_eq h (i := c) (by simp; omega)
  simpa using e

theorem slots_of_child {L : List (List ℕ)} {D : List ℕ} {c : ℕ} (hc : c < L.length) (hn : (D ++ L.flatten).Nodup)
    {S : ℕ} (hlt : ∀ t ∈ D ++ L.flatten, t < S) :
    (L.getD c []).Nodup ∧ ∀ t ∈ L.getD c [], t < S := by
  have hmem : L.getD c [] ∈ L := by rw [List.getD_eq_getElem _ _ hc]; exact List.getElem_mem _
  refine ⟨(List.nodup_flatten.mp (List.nodup_append.mp hn).2.1).1 _ hmem, fun t ht => hlt t ?_⟩
  exact List.mem_append_right _ (List.mem_flatten.mpr ⟨_, hmem, ht⟩)

theorem length_le_of_lt {l : List ℕ} (hn : l.Nodup) {S : ℕ} (hlt : ∀ t ∈ l, t < S) : l.length ≤ S := by
  have := (hn.subperm fun t ht => List.mem_range.mpr (hlt t ht) : l.Subperm (List.range S)).length_le
  simpa using this

/-! ## `main`'s words -/

theorem loadHolds_gpow_of_reads {rd : Reader} {X : ℕ} {xs : List E} (h : ReadsAt rd (ptrAt X) xs) {t : ℕ}
    (ht : t < xs.length) : LoadHolds rd (gen ^ (X + t)) 0 (xs.getD t 0) := by
  rw [pow_add, loadHolds_mul_gen_pow, Nat.add_zero, ← ptrAt_eq_gpow, List.getD_eq_getElem _ _ ht]
  exact h t ht

theorem mTop_ge2 (m : MainCounts) : mBase m 2 + m.sx + m.ss ≤ mTop m := by
  simp only [mTop, mBase_two, MainCounts.bufs, List.sum_cons, List.sum_nil]; omega

/-- A word below `main`'s tables' end is defined, by `LowDef 17` below `2^17` and the tables above. -/
theorem main_def {al : String → Bool} {k : ℕ} (hk : 17 ≤ k) {s : NodeStatement} {w : NodeWitness}
    {cover : List E} {rd : Reader} (hl : LowDef k rd) (hp : MainPreA al s w cover rd) {i : ℕ}
    (hi : i < 2 ^ 17 ∨ i < B2C.fs "main" + 4 * (mainCounts s w).sx + 4 * (mainCounts s w).ss) :
    ∃ t, LoadHolds rd (gen ^ i) 0 t := by
  by_cases hs : i < 2 ^ 17
  · exact loadHolds_of_isSome (hl i (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by norm_num) hk)))
  · replace hi := hi.resolve_left hs
    have hf := fs_main_lt
    have hx := xFlat_length (s.claims.xmss ++ (xPlan s w).duplicates)
    have hy := sFlat_length (s.claims.sphincs ++ (sPlan s w).duplicates)
    rw [List.length_append] at hx hy
    by_cases h0 : i < mBase (mainCounts s w) 1
    · refine loadHolds_of_isSome (isSome_of_inW hp.1 ⟨_, List.mem_cons_self, ?_, ?_⟩)
      · rw [mBase_zero]; omega
      · have e : (mainCounts s w).sx = s.claims.xmss.length + (xPlan s w).duplicates.length := rfl
        rw [mBase_zero, hx]
        rw [mBase_one] at h0
        omega
    · refine loadHolds_of_isSome (isSome_of_inW hp.1 ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_, ?_⟩)
      · omega
      · have e : (mainCounts s w).ss = s.claims.sphincs.length + (sPlan s w).duplicates.length := rfl
        rw [mBase_one, hy]
        omega

/-! ## The fields -/

set_option maxHeartbeats 1000000 in
/-- **`kidx`**: child `c`'s leanXMSS claim list at `main`. -/
theorem mainKidx {al : String → Bool} {k : ℕ} (hk : 17 ≤ k) {s : NodeStatement} {w : NodeWitness}
    (hr : NodeRelation guestBytecode guestSeed s w) (hl : DeployedLimits s w) {cover : List E}
    (hlen : cover.length = (mainCounts s w).sx + (mainCounts s w).ss) (hkc : KidCover s w cover)
    {c : ℕ} (hc : c < w.children.length) :
    AtEveryE al k "child_claim_list_digest"
      [mPtr (mainCounts s w) 0 0, mPtr (mainCounts s w) 2 0, gen ^ kidBase w c, gen ^ (mainCounts s w).sx,
        gen ^ w.children[c].statement.claims.xmss.length]
      (Prover.digestCells (claimListDigest xmssPublicKeyBytes w.children[c].statement.claims.xmss))
      (mainR al (mainCounts s w)) (MainPreA al s w cover)
      (PopsPost (Prover.childSlotPushes ((xPlan s w).childSlots.getD c [])))
      (B2C.fs "child_claim_list_digest") (mLo al (mainCounts s w)) := by
  set os := (xPlan s w).childSlots.getD c [] with hos
  set cx := w.children[c].statement.claims.xmss with hcx
  have hsl := slots_lt hr hl
  have hcs : c < (w.children.map (·.statement.claims.xmss)).length := by simpa using hc
  have hosl : os.length = cx.length := by
    have h := B1.Main.plan_children_lengths s.claims.xmss (w.xmssSignatures.map (·.1))
      (w.children.map (·.statement.claims.xmss))
    rw [← (coveragePlan_eq _ _ _).2.2] at h
    exact (getD_length_of_map h hcs).trans (by rw [List.getElem_map])
  obtain ⟨hnd, hlt⟩ : os.Nodup ∧ ∀ t ∈ os, t < (mainCounts s w).sx := slots_of_child (L := (xPlan s w).childSlots) (by rw [xPlan_childSlots_length]; exact hc)
    (xSlots_nodup s w) (xSlot_lt s w)
  have hle := length_le_of_lt hnd hlt
  have hT : (s.claims.xmss ++ (xPlan s w).duplicates).length = (mainCounts s w).sx := by simp [mainCounts]
  have hget : ∀ j (hj : j < os.length), (s.claims.xmss ++ (xPlan s w).duplicates)[os[j]]? = some (cx[j]'(by omega)) := by
    intro j hj
    obtain ⟨hc', hk', -, -, h⟩ := B1.Main.plan_child s.claims.xmss (w.xmssSignatures.map (·.1))
      (w.children.map (·.statement.claims.xmss)) hcs (k := j) (by rw [List.getElem_map]; exact hosl ▸ hj)
    have e1 : (Coverage.coveragePlan s.claims.xmss (w.xmssSignatures.map (·.1))
        (w.children.map (·.statement.claims.xmss))).duplicates = (xPlan s w).duplicates := (coveragePlan_eq _ _ _).1.symm
    have e2 : ((Coverage.coveragePlan s.claims.xmss (w.xmssSignatures.map (·.1))
        (w.children.map (·.statement.claims.xmss))).childSlots[c])[j] = os[j] := by
      simp only [hos, xPlan, (coveragePlan_eq _ _ _).2.2, List.getD_eq_getElem _ _ hc']
    rw [e1, e2] at h
    simpa [hcx] using h
  have hdig := xDigest cx
  rw [show mPtr (mainCounts s w) 0 0 = gen ^ mBase (mainCounts s w) 0 by rw [mPtr, Nat.add_zero, ptrAt_eq_gpow],
    show mPtr (mainCounts s w) 2 0 = gen ^ mBase (mainCounts s w) 2 by rw [mPtr, Nat.add_zero, ptrAt_eq_gpow]]
  refine kidList_atEvery hk xCells_length hosl (by omega) (by omega) (fun j hj => hlt _ (List.getElem_mem _))
    (fun j hj => Or.inl ⟨by rw [mBase_two]; omega, by have := mTop_ge2 (mainCounts s w); have := hlt _ (List.getElem_mem hj); omega⟩)
    (fun j hj c' hc' => Or.inl ⟨by rw [mBase_zero]; omega, by
      have := mTop_ge (mainCounts s w); have := hlt _ (List.getElem_mem hj); rw [mBase_zero]; omega⟩)
    (fun rd _ hp j hj => ?_) (fun rd _ hp j hj c' hc' => ?_) (fun rd hl' hp i hi => main_def hk hl' hp (by
      have := fs_main_lt; omega)) hdig _
  · have h := loadHolds_gpow_of_reads (mainWords_coverRun hp) (t := os[j]) (by
      rw [hlen]; have := hlt _ (List.getElem_mem hj); omega)
    rwa [(hkc c hc).1 j hj] at h
  · have hx := mainWords_x hp
    have hi : 4 * os[j] + c' < ((s.claims.xmss ++ (xPlan s w).duplicates).flatMap xCells).length := by
      rw [xFlat_length, hT]; have := hlt _ (List.getElem_mem hj); omega
    have h := hx _ hi
    rw [← ptrAt_eq_gpow]
    have hj' : os[j] < (s.claims.xmss ++ (xPlan s w).duplicates).length := by
      rw [hT]; exact hlt _ (List.getElem_mem hj)
    have e := getD_flatMap_four xCells_length (s.claims.xmss ++ (xPlan s w).duplicates) os[j] hj' c' hc'
    rw [List.getD_eq_getElem _ _ hi] at e
    rw [e] at h
    have hg := hget j hj
    rw [List.getElem?_eq_getElem hj'] at hg
    rw [Option.some.inj hg] at h
    exact h

set_option maxHeartbeats 1000000 in
/-- **`kids`**: child `c`'s leanSPHINCS claim list at `main`. -/
theorem mainKids {al : String → Bool} {k : ℕ} (hk : 17 ≤ k) {s : NodeStatement} {w : NodeWitness}
    (hr : NodeRelation guestBytecode guestSeed s w) (hl : DeployedLimits s w) {cover : List E}
    (hlen : cover.length = (mainCounts s w).sx + (mainCounts s w).ss) (hkc : KidCover s w cover)
    {c : ℕ} (hc : c < w.children.length) :
    AtEveryE al k "child_claim_list_digest"
      [mPtr (mainCounts s w) 1 0, mPtr (mainCounts s w) 2 (mainCounts s w).sx,
        gen ^ kidBase w c * gen ^ w.children[c].statement.claims.xmss.length, gen ^ (mainCounts s w).ss,
        gen ^ w.children[c].statement.claims.sphincs.length]
      (Prover.digestCells (claimListDigest Sphincs.PublicKey.toBytes w.children[c].statement.claims.sphincs))
      (mainR al (mainCounts s w)) (MainPreA al s w cover)
      (PopsPost (Prover.childSlotPushes ((sPlan s w).childSlots.getD c [])))
      (B2C.fs "child_claim_list_digest") (mLo al (mainCounts s w)) := by
  set os := (sPlan s w).childSlots.getD c [] with hos
  set cx := w.children[c].statement.claims.sphincs with hcx
  have hsl := slots_lt hr hl
  have hcs : c < (w.children.map (·.statement.claims.sphincs)).length := by simpa using hc
  have hosl : os.length = cx.length := by
    have h := B1.Main.plan_children_lengths s.claims.sphincs (w.sphincsSignatures.map (·.1))
      (w.children.map (·.statement.claims.sphincs))
    rw [← (coveragePlan_eq _ _ _).2.2] at h
    exact (getD_length_of_map h hcs).trans (by rw [List.getElem_map])
  obtain ⟨hnd, hlt⟩ : os.Nodup ∧ ∀ t ∈ os, t < (mainCounts s w).ss := slots_of_child (L := (sPlan s w).childSlots) (by rw [sPlan_childSlots_length]; exact hc)
    (sSlots_nodup s w) (sSlot_lt s w)
  have hle := length_le_of_lt hnd hlt
  have hT : (s.claims.sphincs ++ (sPlan s w).duplicates).length = (mainCounts s w).ss := by simp [mainCounts]
  have hget : ∀ j (hj : j < os.length), (s.claims.sphincs ++ (sPlan s w).duplicates)[os[j]]? = some (cx[j]'(by omega)) := by
    intro j hj
    obtain ⟨hc', hk', -, -, h⟩ := B1.Main.plan_child s.claims.sphincs (w.sphincsSignatures.map (·.1))
      (w.children.map (·.statement.claims.sphincs)) hcs (k := j) (by rw [List.getElem_map]; exact hosl ▸ hj)
    have e1 : (Coverage.coveragePlan s.claims.sphincs (w.sphincsSignatures.map (·.1))
        (w.children.map (·.statement.claims.sphincs))).duplicates = (sPlan s w).duplicates := (coveragePlan_eq _ _ _).1.symm
    have e2 : ((Coverage.coveragePlan s.claims.sphincs (w.sphincsSignatures.map (·.1))
        (w.children.map (·.statement.claims.sphincs))).childSlots[c])[j] = os[j] := by
      simp only [hos, sPlan, (coveragePlan_eq _ _ _).2.2, List.getD_eq_getElem _ _ hc']
    rw [e1, e2] at h
    simpa [hcx] using h
  have hdig := sDigest cx
  have hnx : (w.children.map (·.statement.claims.xmss.length)).getD c 0 = w.children[c].statement.claims.xmss.length := by
    rw [List.getD_eq_getElem _ _ (by simpa using hc)]; simp
  rw [show mPtr (mainCounts s w) 1 0 = gen ^ mBase (mainCounts s w) 1 by rw [mPtr, Nat.add_zero, ptrAt_eq_gpow],
    show mPtr (mainCounts s w) 2 (mainCounts s w).sx = gen ^ (mBase (mainCounts s w) 2 + (mainCounts s w).sx) by rw [mPtr, ptrAt_eq_gpow], ← pow_add]
  refine kidList_atEvery hk sCells_length hosl (by omega) (by omega) (fun j hj => hlt _ (List.getElem_mem _))
    (fun j hj => Or.inl ⟨by rw [mBase_two]; omega, by have := mTop_ge2 (mainCounts s w); have := hlt _ (List.getElem_mem hj); omega⟩)
    (fun j hj c' hc' => Or.inl ⟨by rw [mBase_one]; omega, by
      have := mTop_ge (mainCounts s w); have := hlt _ (List.getElem_mem hj); rw [mBase_one]; omega⟩)
    (fun rd _ hp j hj => ?_) (fun rd _ hp j hj c' hc' => ?_) (fun rd hl' hp i hi => main_def hk hl' hp (by
      have := fs_main_lt; omega)) hdig _
  · have h := loadHolds_gpow_of_reads (mainWords_coverRun hp) (t := (mainCounts s w).sx + os[j]) (by
      rw [hlen]; have := hlt _ (List.getElem_mem hj); omega)
    rw [(hkc c hc).2 j hj, hnx, ← Nat.add_assoc] at h
    exact h
  · have hx := mainWords_s hp
    have hi : 4 * os[j] + c' < ((s.claims.sphincs ++ (sPlan s w).duplicates).flatMap sCells).length := by
      rw [sFlat_length, hT]; have := hlt _ (List.getElem_mem hj); omega
    have h := hx _ hi
    rw [← ptrAt_eq_gpow]
    have hj' : os[j] < (s.claims.sphincs ++ (sPlan s w).duplicates).length := by
      rw [hT]; exact hlt _ (List.getElem_mem hj)
    have e := getD_flatMap_four sCells_length (s.claims.sphincs ++ (sPlan s w).duplicates) os[j] hj' c' hc'
    rw [List.getD_eq_getElem _ _ hi] at e
    rw [e] at h
    have hg := hget j hj
    rw [List.getElem?_eq_getElem hj'] at hg
    rw [Option.some.inj hg] at h
    exact h

/-- **The children's claim lists on every node, their ends bounded.** -/
theorem kidsListsOpenE {al : String → Bool} {k : ℕ} (hk : 17 ≤ k) : KidsListsOpenE al k :=
  fun _ _ _ hr hl _ hlen hkc => ⟨fun _ hc => mainKidx hk hr hl hlen hkc hc, fun _ hc => mainKids hk hr hl hlen hkc hc⟩

/-- **The children's claim lists on every node**, at the deployed choices (`mainCalleesOpenA_of_kids`). -/
theorem kidsListsOpen : KidsListsOpen Memory.alW 17 := (kidsListsOpenE le_rfl).toOpen

end
end LeanVM.Guest.Complete
