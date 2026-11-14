/-
  LeanVM.Guest.B1.Main.MainGoalsHL5

  `main`'s honest children loop `main_loop4`: complete at `main`'s words (`MainGoalL5`).
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHKid
public import LeanVM.Guest.AcceptableChild

/-!
# The children loop on an honest run

`plan_slot`: child `c`'s claim `j` takes a slot of its region's table, the table holds the claim
there, and the coverage word there marks the claim's global index (`kid_hCover_x`,
`kid_hCover_s`: `g^(hW c + j)`, after the child's leanXMSS claims for leanSPHINCS). The children's
DA digests lie in `da_digests` before the own one (`reads_buf`).
`kidOk`: child `c` is `KidOkC` at `main`'s words, its two `child_claim_list_digest` calls and its
`verify_sub` call complete by hypothesis (the lists: `MainGoalsHClT`).
`mainGoalL5`: `l5_completeAt` from the counter `0`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (GuestLimits)
open LeanVM.Guest.Coverage (planSlots)
open LeanVM.Guest.Hints (claimCells)
open LeanVM.Guest.Coverage (coveragePlan CoverageRegion)
open LeanVM.Guest.B1 (CompleteAtD Returns bufL)

@[expose] public section

/-! ## A child's slots -/

/-- **Child `c`'s claim `j`'s slot**: in the table, its index among the slots, the table's claim
there. -/
theorem plan_slot {α : Type} [BEq α] [LawfulBEq α] (D R : List α) (Cs : List (List α)) {c j : ℕ}
    (hc : c < Cs.length) (hj : j < (Cs[c]).length) :
    ((coveragePlan D R Cs).childSlots.getD c []).getD j 0 < (D ++ (coveragePlan D R Cs).duplicates).length ∧
      (slotsOf (coveragePlan D R Cs)).idxOf (((coveragePlan D R Cs).childSlots.getD c []).getD j 0) = base R Cs c + j ∧
      (D ++ (coveragePlan D R Cs).duplicates)[((coveragePlan D R Cs).childSlots.getD c []).getD j 0]? = some (Cs[c])[j] := by
  obtain ⟨hc', hk', hs, e1, e2⟩ := plan_child D R Cs hc hj
  have eo : ((coveragePlan D R Cs).childSlots.getD c []).getD j 0 = ((coveragePlan D R Cs).childSlots[c])[j] := by
    rw [List.getD_eq_getElem _ _ hc', List.getD_eq_getElem _ _ hk']
  rw [eo]
  refine ⟨plan_lt D R Cs _ (e1 ▸ List.getElem_mem hs), ?_, e2⟩
  rw [← e1]
  exact (plan_nodup D R Cs).idxOf_getElem _ hs

theorem take_map_lengths {β : Type} (L : List Child) (f : Child → List β) (c : ℕ) :
    ((L.map f).take c).map List.length = (L.map fun ch => (f ch).length).take c := by
  rw [List.map_take, List.map_map]
  rfl

variable {s : NodeStatement} {w : NodeWitness}

theorem kid_hMarkX_child {c j : ℕ} (hc : c < w.children.length)
    (hj : j < w.children[c].statement.claims.xmss.length) :
    hMarkX s w (base (w.xmssSignatures.map (·.1))
      (w.children.map (·.statement.claims.xmss)) c + j) = hW s w c + j := by
  have e := kid_segOf_sum (w.children.map (·.statement.claims.xmss.length)) c j (by simpa using hc)
    (by simpa using hj)
  unfold hMarkX base
  rw [List.length_map, take_map_lengths]
  rw [ite_neg' (by unfold hRawX; omega)]
  simp only [hRawX, Nat.add_assoc, Nat.add_sub_cancel_left, e]

theorem kid_hMarkS_child {c j : ℕ} (hc : c < w.children.length)
    (hj : j < w.children[c].statement.claims.sphincs.length) :
    hMarkS s w (base (w.sphincsSignatures.map (·.1))
      (w.children.map (·.statement.claims.sphincs)) c + j) = hW s w c + hEx w c + j := by
  have e := kid_segOf_sum (w.children.map (·.statement.claims.sphincs.length)) c j (by simpa using hc)
    (by simpa using hj)
  unfold hMarkS base
  rw [List.length_map, take_map_lengths]
  rw [ite_neg' (by unfold hRawS; omega)]
  simp only [hRawS, Nat.add_assoc, Nat.add_sub_cancel_left, e]

/-! ## The coverage table -/

theorem kid_length_hCover : (hCover s w).length = s.claims.xmss.length + (xPlan s w).duplicates.length +
    (s.claims.sphincs.length + (sPlan s w).duplicates.length) := by
  simp only [hCover, List.length_append, List.length_map, List.length_range]

theorem kid_hCover_x {t : ℕ} (ht : t < s.claims.xmss.length + (xPlan s w).duplicates.length) :
    (hCover s w).getD t 0 = gen ^ hMarkX s w ((slotsOf (xPlan s w)).idxOf t) := by
  unfold hCover
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using ht),
    List.getElem?_map, List.getElem?_range (by simpa using ht)]
  rfl

theorem kid_hCover_s {t : ℕ} (ht : t < s.claims.sphincs.length + (sPlan s w).duplicates.length) :
    (hCover s w).getD (s.claims.xmss.length + (xPlan s w).duplicates.length + t) 0 =
      gen ^ hMarkS s w ((slotsOf (sPlan s w)).idxOf t) := by
  unfold hCover
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp only [List.length_map, List.length_range, List.length_append]; omega),
    List.getElem?_map]
  simp only [List.length_map, List.length_range, List.length_append, Nat.add_sub_cancel_left]
  rw [List.getElem?_range (by simpa using ht)]
  rfl

theorem loadHolds_getD {rd : Reader} {p : E} {xs : List E} (h : ReadsAt rd p xs) {k : ℕ}
    (hk : k < xs.length) : LoadHolds rd p k (xs.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

theorem kid_length_flatMap_const {α : Type} {f : α → List E} {k : ℕ} :
    ∀ (l : List α), (∀ a ∈ l, (f a).length = k) → (l.flatMap f).length = k * l.length
  | [], _ => by simp
  | a :: l, h => by
    rw [List.flatMap_cons, List.length_append, h a List.mem_cons_self,
      kid_length_flatMap_const l fun b hb => h b (List.mem_cons_of_mem _ hb), List.length_cons]
    ring

theorem getD_range_map (f : ℕ → E) {n c : ℕ} (hc : c < n) : ((List.range n).map f).getD c 0 = f c := by
  rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]

/-! ## `main`'s words -/

/-- Buffer `i`'s first word. -/
abbrev hP (fs : String → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement) (w : NodeWitness) (i : ℕ) :
    ℕ :=
  (mPos (hData seed s w) (fp + fs "main")).getD i 0

/-- **`main`'s honest buffers**, as the children loop reads them. -/
theorem reads_buf (fs : String → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement) (w : NodeWitness)
    {rd : Reader} (hM : B1.Main.MemL rd (hLmain fs fp seed s w)) :
    ReadsAt rd (gen ^ hP fs fp seed s w 0)
      ((s.claims.xmss ++ (xPlan s w).duplicates).flatMap fun c => claimCells c.1.root c.1.parameter c.2) ∧
    ReadsAt rd (gen ^ hP fs fp seed s w 1)
      ((s.claims.sphincs ++ (sPlan s w).duplicates).flatMap fun c => claimCells c.1.publicSeed c.1.root c.2) ∧
    ReadsAt rd (gen ^ hP fs fp seed s w 2) (hCover s w) ∧
    ReadsAt rd (gen ^ hP fs fp seed s w 4)
      ((w.children.map (·.statement.claims.daDigest) ++ [hOwnDa w]).flatMap B1.Digest.digestCells) ∧
    ReadsAt rd (gen ^ hP fs fp seed s w 5)
      (w.children.flatMap fun c => B1.Digest.digestCells (statementDigest seed c.statement)) ∧
    ReadsAt rd (gen ^ hP fs fp seed s w 7) (w.children.flatMap fun c => c.statement.deferredClaim.cells) ∧
    ReadsAt rd (gen ^ hP fs fp seed s w 8)
      ((List.range (w.children.length + 1)).map fun c => gen ^ hW s w c) := by
  have r0 := reads_hLmain fs fp seed s w hM (i := 0) (by omega)
  have r1 := reads_hLmain fs fp seed s w hM (i := 1) (by omega)
  have r2 := reads_hLmain fs fp seed s w hM (i := 2) (by omega)
  have r4 := reads_hLmain fs fp seed s w hM (i := 4) (by omega)
  have r5 := reads_hLmain fs fp seed s w hM (i := 5) (by omega)
  have r7 := reads_hLmain fs fp seed s w hM (i := 7) (by omega)
  have r8 := reads_hLmain fs fp seed s w hM (i := 8) (by omega)
  simp only [hOwn, List.getD_cons_succ, List.getD_cons_zero] at r0 r1 r2 r4 r5 r7 r8
  exact ⟨r0, r1, r2, r4, r5, r7, r8⟩

theorem region_buf (fs : String → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement) (w : NodeWitness)
    {i k : ℕ} (hi : i < 10) (hk : k < ((hOwn seed s w).getD i []).length) :
    B1.Main.RegionL (hLmain fs fp seed s w) (hP fs fp seed s w i + k) :=
  B1.Da.regionL_of_mem (mem_hLmain fs fp seed s w hi) hk

variable {fs : String → ℕ} {fp : ℕ} {seed : Digest}

/-! ## Child `c` -/

theorem belowLog_of {o L : ℕ} (h : o < L) (hL : L < 2 ^ 32) : B1.Digest.BelowLog (gen ^ L) o :=
  ⟨by omega, L - o - 1, by omega, by congr 1; omega⟩

theorem cover_bound (hl : GuestLimits s w) :
    s.claims.xmss.length + (xPlan s w).duplicates.length +
      (s.claims.sphincs.length + (sPlan s w).duplicates.length) < 2 ^ 23 := by
  have hcov := hl.planSlotsBelow2Pow23
  rw [coverage_eq] at hcov
  simp only [List.length_append] at hcov
  omega

/-- The children's statement digests' cells, two a child. -/
theorem length_piCells : (w.children.flatMap fun c =>
    B1.Digest.digestCells (statementDigest seed c.statement)).length = 2 * w.children.length :=
  kid_length_flatMap_const _ fun _ _ => rfl

/-- The DA digests' cells, two a slot. -/
theorem length_daDigests : ((w.children.map (·.statement.claims.daDigest) ++ [hOwnDa w]).flatMap
    B1.Digest.digestCells).length = 2 * (w.children.length + 1) := by
  rw [kid_length_flatMap_const (f := B1.Digest.digestCells) (k := 2) _ fun _ _ => rfl]
  simp

/-- **Child `c` is as `main_loop4` needs it**, at `main`'s honest words. -/
theorem kidOk (cert : String → V → ℕ) {bytecode : List K}
    (hbl : bytecode.length = 2 ^ bytecodeVars) (hrel : NodeRelation bytecode seed s w)
    (hl : GuestLimits s w)
    (hV : ∀ c (hc : c < w.children.length), CompleteAtD fs cert 20 "verify_sub" (hLmain fs fp seed s w)
      [(digestHalves (statementDigest seed w.children[c].statement)).1,
        (digestHalves (statementDigest seed w.children[c].statement)).2,
        (digestHalves seed).1, (digestHalves seed).2, (hm fs fp seed s w).et,
        (hm fs fp seed s w).a400 * gen ^ (24 * c)] (Returns []))
    {c : ℕ}
    (hX : CompleteAtD fs cert 23 "child_claim_list_digest" (hLmain fs fp seed s w)
      [(hm fs fp seed s w).a77, (hm fs fp seed s w).a117, (hKid s w c).base,
        gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd), gen ^ (hKid s w c).ex]
      (Returns [(hKid s w c).cx.1, (hKid s w c).cx.2]))
    (hS : CompleteAtD fs cert 23 "child_claim_list_digest" (hLmain fs fp seed s w)
      [(hm fs fp seed s w).a80,
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hKid s w c).base * gen ^ (hKid s w c).ex,
        gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd), gen ^ (hKid s w c).es]
      (Returns [(hKid s w c).cs.1, (hKid s w c).cs.2]))
    (hc : c < w.children.length) :
    KidOkC fs cert (hLmain fs fp seed s w) (hP fs fp seed s w 8) (hP fs fp seed s w 4)
      (hP fs fp seed s w 5) (hP fs fp seed s w 7)
      (hm fs fp seed s w).a77 (hm fs fp seed s w).a117
      (gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd)) (hm fs fp seed s w).a80
      ((hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd))
      (gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd))
      (digestHalves seed).1 (digestHalves seed).2 (hm fs fp seed s w).et
      (hm fs fp seed s w).a400 c (hKid s w c) := by
  have hsh := kid_shapes hbl hrel
  have hb : bytecodeVars = 23 := rfl
  have hmem := List.getElem_mem hc
  have hdl : w.children[c].statement.deferredClaim.cells.length = 24 := by
    simp [DeferredBytecodeClaim.cells, (hsh _ hmem).2, hb]
  have hpi := hKid_pi seed (s := s) hc
  have hW1 : hW s w (c + 1) = hW s w c + (hEx w c + hEs w c) := by
    simp only [hW]
  refine ⟨?_, ?_, by rw [hKid_defer hc]; exact hdl, fun rd hM => ?_, ?_, hX, hS,
    by rw [hpi]; exact hV c hc⟩
  · rw [hKid_ex hc]; have := (hl.childClaimListsBelow2Pow23 _ hmem).1; omega
  · rw [hKid_es hc]; have := (hl.childClaimListsBelow2Pow23 _ hmem).2; omega
  · -- the memory
    obtain ⟨-, -, -, r4, r5, r7, r8⟩ := reads_buf fs fp seed s w hM
    have p4 := readsAt_flatMap_of (w := 2) _ (fun _ _ => rfl) r4 c (by simp; omega)
    have p5 := readsAt_flatMap_of (w := 2) w.children (fun _ _ => rfl) r5 c hc
    have p7 := readsAt_flatMap_of (w := 24) w.children
      (fun a ha => by simp [DeferredBytecodeClaim.cells, (hsh a ha).2, hb]) r7 c hc
    have e4 : (w.children.map (·.statement.claims.daDigest) ++ [hOwnDa w])[c]'(by simp; omega) =
        w.children[c].statement.claims.daDigest := by
      rw [List.getElem_append_left (by simpa using hc), List.getElem_map]
    rw [e4] at p4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := loadHolds_getD r8 (k := c) (by simp; omega)
      rwa [getD_range_map _ (by omega)] at this
    · have := loadHolds_getD r8 (k := c + 1) (by simp; omega)
      rw [getD_range_map _ (by omega), hW1, pow_add, pow_add] at this
      exact this
    · have := p4 0 (by simp [B1.Digest.digestCells])
      rw [loadHolds_mul_gen_pow, Nat.add_zero] at this
      rw [hKid_da hc]; exact this
    · have := p4 1 (by simp [B1.Digest.digestCells])
      rw [loadHolds_mul_gen_pow] at this
      rw [hKid_da hc]; exact this
    · have := p5 0 (by simp [B1.Digest.digestCells])
      rw [loadHolds_mul_gen_pow, Nat.add_zero] at this
      rw [hpi]; exact this
    · have := p5 1 (by simp [B1.Digest.digestCells])
      rw [loadHolds_mul_gen_pow] at this
      rw [hpi]; exact this
    · rw [pow_add, hKid_defer hc]; exact p7
  · -- the regions
    have hlenW : ((hOwn seed s w).getD 8 []).length = w.children.length + 1 := by
      simp [hOwn]
    have hlenD : ((hOwn seed s w).getD 4 []).length = 2 * (w.children.length + 1) :=
      length_daDigests
    have hlenPi : ((hOwn seed s w).getD 5 []).length = 2 * w.children.length := length_piCells
    refine ⟨region_buf fs fp seed s w (by omega) (by rw [hlenW]; omega), ?_,
      region_buf fs fp seed s w (by omega) (by rw [hlenD]; omega), ?_,
      region_buf fs fp seed s w (by omega) (by rw [hlenPi]; omega), ?_⟩
    · rw [Nat.add_assoc]; exact region_buf fs fp seed s w (by omega) (by rw [hlenW]; omega)
    · rw [Nat.add_assoc]; exact region_buf fs fp seed s w (by omega) (by rw [hlenD]; omega)
    · rw [Nat.add_assoc]; exact region_buf fs fp seed s w (by omega) (by rw [hlenPi]; omega)

end
end LeanVM.Guest.B1.Main
