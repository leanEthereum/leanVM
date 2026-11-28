module

public import LeanVM.Guest.Complete.MainOrc
public import LeanVM.Guest.Complete.CoverageEq
public import LeanVM.Guest.B1.Main.Plan

/-!
# The honest coverage table

`honestCover s w`: the coverage table's `sx + ss` marks as the honest run writes them, from the plan
(`xPlan`, `sPlan`): raw leanXMSS signature `i`'s slot `g^i`, raw leanSPHINCS signature `i`'s slot
(at `sx` on) `g^(nrx + i)`, child `c`'s slots its first count `g^(kidBase w c)` (plus its leanXMSS
count in the leanSPHINCS region) when its slots increase (the gap walk), else that count times
`g^j` at its `j`-th slot (the walk by indices). The plan's slots are distinct (`B1.Main.plan_nodup`),
so the table is well defined; a slot no claim takes holds `0`.

`honestCover_length`, `kidCover_honest` (`KidCover`, the children's marks), `honestCover_rawx`,
`honestCover_raws` (the raw slots' marks, in `RawXPre`'s and `RawSPre`'s form), and the slots' bounds
(`xSlot_lt`, `sSlot_lt`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Guest.B1
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

noncomputable section

/-! ## The children's marks -/

/-- **The coverage marks the children's claim lists write**: at child `c`'s `j`-th leanXMSS slot its
first count `g^(kidBase w c)` on the gap walk (its slots increasing), `g^(kidBase w c + j)` on the walk
by indices; its leanSPHINCS slots, at `sx` on, the same from `kidBase w c` plus its leanXMSS count. -/
def KidCover (s : NodeStatement) (w : NodeWitness) (cover : List E) : Prop :=
  ∀ c < w.children.length,
    (∀ j (hj : j < ((xPlan s w).childSlots.getD c []).length),
      cover.getD (((xPlan s w).childSlots.getD c [])[j]) 0 =
        if Prover.increasing ((xPlan s w).childSlots.getD c []) then gen ^ kidBase w c
        else gen ^ (kidBase w c + j)) ∧
    (∀ j (hj : j < ((sPlan s w).childSlots.getD c []).length),
      cover.getD ((mainCounts s w).sx + ((sPlan s w).childSlots.getD c [])[j]) 0 =
        if Prover.increasing ((sPlan s w).childSlots.getD c [])
        then gen ^ (kidBase w c + (w.children.map (·.statement.claims.xmss.length)).getD c 0)
        else gen ^ (kidBase w c + (w.children.map (·.statement.claims.xmss.length)).getD c 0 + j))

/-! ## Marks and lookups -/

/-- A region's marks at the offset `off`: raw claim `i`'s slot `g^(r0 + i)`, child `c`'s `j`-th slot
`g^(kb c)` when its slots increase, else `g^(kb c + j)`. -/
def regionMarks {α : Type} (p : Prover.CoverageRegion α) (off r0 nc : ℕ) (kb : ℕ → ℕ) : List (ℕ × E) :=
  p.directSlots.mapIdx (fun i t => (off + t, gen ^ (r0 + i))) ++
    (List.range nc).flatMap fun c =>
      (p.childSlots.getD c []).mapIdx fun j t =>
        (off + t, if Prover.increasing (p.childSlots.getD c []) then gen ^ kb c else gen ^ (kb c + j))

/-- Child `c`'s leanXMSS claims' count. -/
def kidNx (w : NodeWitness) (c : ℕ) : ℕ := (w.children.map (·.statement.claims.xmss.length)).getD c 0

/-- Every slot's mark, the leanXMSS region's then the leanSPHINCS region's (at `sx` on). -/
def coverMarks (s : NodeStatement) (w : NodeWitness) : List (ℕ × E) :=
  regionMarks (xPlan s w) 0 0 w.children.length (kidBase w) ++
    regionMarks (sPlan s w) (mainCounts s w).sx w.xmssSignatures.length w.children.length
      fun c => kidBase w c + kidNx w c

/-- **The honest coverage table.** -/
def honestCover (s : NodeStatement) (w : NodeWitness) : List E :=
  (List.range ((mainCounts s w).sx + (mainCounts s w).ss)).map fun t => ((coverMarks s w).lookup t).getD 0

theorem honestCover_length (s : NodeStatement) (w : NodeWitness) :
    (honestCover s w).length = (mainCounts s w).sx + (mainCounts s w).ss := by
  simp [honestCover]

theorem lookup_of_mem {β : Type} : ∀ {L : List (ℕ × β)} {a : ℕ} {b : β}, (L.map Prod.fst).Nodup →
    (a, b) ∈ L → L.lookup a = some b
  | [], _, _, _, h => absurd h List.not_mem_nil
  | (a', b') :: L, a, b, hn, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h with h1 | h2
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      simp [List.lookup]
    · have hne : a ≠ a' := fun e => hn.1 (List.mem_map.mpr ⟨(a, b), h2, e⟩)
      have hb : (a == a') = false := by simpa using hne
      simp only [List.lookup, hb]
      exact lookup_of_mem hn.2 h2

theorem mapIdx_keys {β : Type} (l : List ℕ) (off : ℕ) (m : ℕ → β) :
    (l.mapIdx fun i t => (off + t, m i)).map Prod.fst = l.map (off + ·) :=
  List.ext_getElem (by simp) fun i h1 h2 => by simp

theorem mapIdx_mem {β : Type} (l : List ℕ) (off : ℕ) (m : ℕ → β) {i : ℕ} (hi : i < l.length) :
    (off + l[i], m i) ∈ l.mapIdx fun i t => (off + t, m i) :=
  List.mem_iff_getElem.mpr ⟨i, by simpa using hi, by simp⟩

theorem flatMap_range_getD_cover {β : Type} (f : List ℕ → List β) :
    ∀ L : List (List ℕ), (List.range L.length).flatMap (fun c => f (L.getD c [])) = L.flatMap f
  | [] => rfl
  | l :: L => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.flatMap_cons]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [flatMap_range_getD_cover f L]

theorem regionMarks_keys {α : Type} (p : Prover.CoverageRegion α) (off r0 : ℕ) (kb : ℕ → ℕ) :
    (regionMarks p off r0 p.childSlots.length kb).map Prod.fst =
      (p.directSlots ++ p.childSlots.flatten).map (off + ·) := by
  rw [regionMarks, List.map_append, mapIdx_keys, List.map_flatMap, List.map_append]
  congr 1
  simp only [mapIdx_keys]
  rw [flatMap_range_getD_cover (fun l => l.map (off + ·)), List.map_flatten, List.flatten_eq_flatMap,
    List.flatMap_map]
  rfl

/-! ## The plan's slots -/

theorem xPlan_childSlots_length (s : NodeStatement) (w : NodeWitness) :
    (xPlan s w).childSlots.length = w.children.length := by
  have := congrArg List.length (B1.Main.plan_children_lengths s.claims.xmss (w.xmssSignatures.map (·.1))
    (w.children.map (·.statement.claims.xmss)))
  simp only [List.length_map] at this
  rw [xPlan, (coveragePlan_eq _ _ _).2.2]; exact this

theorem sPlan_childSlots_length (s : NodeStatement) (w : NodeWitness) :
    (sPlan s w).childSlots.length = w.children.length := by
  have := congrArg List.length (B1.Main.plan_children_lengths s.claims.sphincs (w.sphincsSignatures.map (·.1))
    (w.children.map (·.statement.claims.sphincs)))
  simp only [List.length_map] at this
  rw [sPlan, (coveragePlan_eq _ _ _).2.2]; exact this

theorem xPlan_directSlots_length (s : NodeStatement) (w : NodeWitness) :
    (xPlan s w).directSlots.length = w.xmssSignatures.length := by
  have := B1.Main.plan_raw_length s.claims.xmss (w.xmssSignatures.map (·.1)) (w.children.map (·.statement.claims.xmss))
  rw [xPlan, (coveragePlan_eq _ _ _).2.1, this, List.length_map]

theorem sPlan_directSlots_length (s : NodeStatement) (w : NodeWitness) :
    (sPlan s w).directSlots.length = w.sphincsSignatures.length := by
  have := B1.Main.plan_raw_length s.claims.sphincs (w.sphincsSignatures.map (·.1))
    (w.children.map (·.statement.claims.sphincs))
  rw [sPlan, (coveragePlan_eq _ _ _).2.1, this, List.length_map]

theorem xSlots_nodup (s : NodeStatement) (w : NodeWitness) :
    ((xPlan s w).directSlots ++ (xPlan s w).childSlots.flatten).Nodup := by
  rw [xPlan, (coveragePlan_eq _ _ _).2.1, (coveragePlan_eq _ _ _).2.2]
  exact B1.Main.plan_nodup _ _ _

theorem sSlots_nodup (s : NodeStatement) (w : NodeWitness) :
    ((sPlan s w).directSlots ++ (sPlan s w).childSlots.flatten).Nodup := by
  rw [sPlan, (coveragePlan_eq _ _ _).2.1, (coveragePlan_eq _ _ _).2.2]
  exact B1.Main.plan_nodup _ _ _

/-- **The leanXMSS slots are below `sx`.** -/
theorem xSlot_lt (s : NodeStatement) (w : NodeWitness) :
    ∀ t ∈ (xPlan s w).directSlots ++ (xPlan s w).childSlots.flatten, t < (mainCounts s w).sx := by
  intro t ht
  have ex : (mainCounts s w).nxd = (B1.Main.xPlan s w).duplicates.length :=
    congrArg List.length (coveragePlan_eq _ _ _).1
  rw [xPlan, (coveragePlan_eq _ _ _).2.1, (coveragePlan_eq _ _ _).2.2] at ht
  have := B1.Main.plan_lt _ _ _ t ht
  rw [List.length_append] at this
  simp only [MainCounts.sx, ex]
  exact this

/-- **The leanSPHINCS slots are below `ss`.** -/
theorem sSlot_lt (s : NodeStatement) (w : NodeWitness) :
    ∀ t ∈ (sPlan s w).directSlots ++ (sPlan s w).childSlots.flatten, t < (mainCounts s w).ss := by
  intro t ht
  have es : (mainCounts s w).nsd = (B1.Main.sPlan s w).duplicates.length :=
    congrArg List.length (coveragePlan_eq _ _ _).1
  rw [sPlan, (coveragePlan_eq _ _ _).2.1, (coveragePlan_eq _ _ _).2.2] at ht
  have := B1.Main.plan_lt _ _ _ t ht
  rw [List.length_append] at this
  simp only [MainCounts.ss, es]
  exact this

theorem coverMarks_keys_nodup (s : NodeStatement) (w : NodeWitness) :
    ((coverMarks s w).map Prod.fst).Nodup := by
  have hx := regionMarks_keys (xPlan s w) 0 0 (kidBase w)
  have hs := regionMarks_keys (sPlan s w) (mainCounts s w).sx w.xmssSignatures.length
    fun c => kidBase w c + kidNx w c
  rw [xPlan_childSlots_length] at hx
  rw [sPlan_childSlots_length] at hs
  rw [coverMarks, List.map_append, hx, hs, List.nodup_append]
  refine ⟨(xSlots_nodup s w).map fun a b h => by omega, (sSlots_nodup s w).map fun a b h => by omega,
    fun a ha b hb => ?_⟩
  obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
  obtain ⟨b', -, rfl⟩ := List.mem_map.mp hb
  have := xSlot_lt s w a' ha'
  omega

/-- **A mark is the table's entry at its slot.** -/
theorem honestCover_getD {s : NodeStatement} {w : NodeWitness} {t : ℕ} {v : E} (h : (t, v) ∈ coverMarks s w)
    (ht : t < (mainCounts s w).sx + (mainCounts s w).ss) : (honestCover s w).getD t 0 = v := by
  rw [List.getD_eq_getElem _ _ (by rw [honestCover_length]; exact ht)]
  simp [honestCover, lookup_of_mem (coverMarks_keys_nodup s w) h]

theorem mem_flatten_of {L : List (List ℕ)} {c j : ℕ} (hc : c < L.length) (hj : j < (L.getD c []).length) :
    (L.getD c [])[j] ∈ L.flatten :=
  List.mem_flatten.mpr ⟨L.getD c [], by rw [List.getD_eq_getElem _ _ hc]; exact List.getElem_mem hc,
    List.getElem_mem hj⟩

/-! ## The marks -/

/-- **The children's marks** are the honest table's. -/
theorem kidCover_honest (s : NodeStatement) (w : NodeWitness) : KidCover s w (honestCover s w) := by
  intro c hc
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have hm := mapIdx_mem ((xPlan s w).childSlots.getD c []) 0
      (fun j => if Prover.increasing ((xPlan s w).childSlots.getD c []) then gen ^ kidBase w c
        else gen ^ (kidBase w c + j)) hj
    rw [Nat.zero_add] at hm
    refine honestCover_getD (List.mem_append_left _ (List.mem_append_right _ ?_)) ?_
    · exact List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, hm⟩
    · have := xSlot_lt s w _ (List.mem_append_right _
        (mem_flatten_of (by rw [xPlan_childSlots_length]; exact hc) hj))
      omega
  · have hm := mapIdx_mem ((sPlan s w).childSlots.getD c []) (mainCounts s w).sx
      (fun j => if Prover.increasing ((sPlan s w).childSlots.getD c []) then gen ^ (kidBase w c + kidNx w c)
        else gen ^ (kidBase w c + kidNx w c + j)) hj
    refine honestCover_getD (List.mem_append_right _ (List.mem_append_right _ ?_)) ?_
    · exact List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, hm⟩
    · have := sSlot_lt s w _ (List.mem_append_right _
        (mem_flatten_of (by rw [sPlan_childSlots_length]; exact hc) hj))
      omega

/-- **The raw leanXMSS slots' marks**: signature `i`'s slot, below `sx`, holds `g^i`. -/
theorem honestCover_rawx (s : NodeStatement) (w : NodeWitness) {i : ℕ}
    (hi : i < (xPlan s w).directSlots.length) :
    (xPlan s w).directSlots[i] < (mainCounts s w).sx ∧
      (honestCover s w).getD ((xPlan s w).directSlots[i]) 0 = gen ^ i := by
  have hlt := xSlot_lt s w _ (List.mem_append_left _ (List.getElem_mem hi))
  refine ⟨hlt, honestCover_getD (s := s) (w := w) (List.mem_append_left _ (List.mem_append_left _ ?_)) (by omega)⟩
  have := mapIdx_mem (xPlan s w).directSlots 0 (fun i => gen ^ (0 + i)) hi
  simpa using this

/-- **The raw leanSPHINCS slots' marks**: signature `i`'s slot, below `ss`, holds `g^nrx · g^i` at
`sx` past it. -/
theorem honestCover_raws (s : NodeStatement) (w : NodeWitness) {i : ℕ}
    (hi : i < (sPlan s w).directSlots.length) :
    (sPlan s w).directSlots[i] < (mainCounts s w).ss ∧
      (honestCover s w).getD ((mainCounts s w).sx + (sPlan s w).directSlots[i]) 0 =
        gen ^ (mainCounts s w).nrx * gen ^ i := by
  have hlt := sSlot_lt s w _ (List.mem_append_left _ (List.getElem_mem hi))
  refine ⟨hlt, honestCover_getD (s := s) (w := w) (List.mem_append_right _ (List.mem_append_left _ ?_)) (by omega)⟩
  have := mapIdx_mem (sPlan s w).directSlots (mainCounts s w).sx
    (fun i => gen ^ (w.xmssSignatures.length + i)) hi
  rw [← pow_add]
  exact this

end
end
end LeanVM.Guest.Complete
