/-
  LeanVM.Guest.B1.Main.MainGoalsHClT

  Each child's claim lists' digests on `main`'s honest run, by trees of honest shape
  (`ccHonest`): `kid_hX`, `kid_hS` (same proofs) with `child_claim_list_digest_completeAtT`.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHL5T
public import LeanVM.Guest.B1.Main.MainGoalsClT
public import LeanVM.Guest.B1.Digest.ClaimListsAtT
public import LeanVM.Guest.AcceptableChild

/-!
# The children's claim lists, their trees exposed

`kidT_hX`, `kidT_hS`: child `c`'s claim lists' digests complete by trees `ccHonest` of its lists'
lengths. `childListGoalsT_honest`: `ChildListGoalsT` with those predicates.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (DeployedLimits)
open LeanVM.Guest.Coverage (planSlots)
open LeanVM.Guest.Hints (claimCells)
open LeanVM.Guest.Coverage (coveragePlan CoverageRegion)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT Returns bufL)
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1.Digest (ccQ ccCalls ccBufs ccTs)

@[expose] public section

/-- **`child_claim_list_digest`'s honest shape** on `n` claims. -/
def ccHonest (n : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "child_claim_list_digest" (ccQ n) (ccCalls n) (ccBufs n) (ccTs n)

variable {fs : String → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness}

/-- **Child `c`'s leanXMSS list is complete.** -/
theorem kidT_hX (cert : String → V → ℕ) (hl : DeployedLimits s w) {c : ℕ}
    (hc : c < w.children.length) :
    CompleteAtDT fs cert 20 "child_claim_list_digest" (hLmain fs fp seed s w)
      [(hm fs fp seed s w).a77, (hm fs fp seed s w).a117, (hKid s w c).base,
        gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd), gen ^ (hKid s w c).ex]
      (Returns [(hKid s w c).cx.1, (hKid s w c).cx.2]) (ccHonest (hKid s w c).ex) := by
  have hcov := cover_bound hl
  have hlen := (hl.childClaimListsBelow2Pow20 _ (List.getElem_mem hc)).1
  have hT := kid_length_flatMap_const (f := fun c : LeanXmssClaim => claimCells c.1.root c.1.parameter c.2)
    (s.claims.xmss ++ (xPlan s w).duplicates) fun a _ => kid_length_claimCells _ _ _
  rw [List.length_append] at hT
  have slot := fun j (hj : j < w.children[c].statement.claims.xmss.length) =>
    plan_slot s.claims.xmss (w.xmssSignatures.map (·.1))
      (w.children.map (·.statement.claims.xmss)) (c := c) (j := j) (by simpa using hc)
      (by simpa using hj)
  have := B1.Digest.child_claim_list_digest_completeAtT fs cert (κ := 20) (by norm_num)
    (Lin := hLmain fs fp seed s w) (eP := hP fs fp seed s w 0) (rg := hP fs fp seed s w 2)
    (L := s.claims.xmss.length + (xPlan s w).duplicates.length) (n := (hKid s w c).ex)
    (base := (hKid s w c).base) (o := fun j => ((xPlan s w).childSlots.getD c []).getD j 0)
    (cells := w.children[c].statement.claims.xmss.flatMap fun c => claimCells c.1.root c.1.parameter c.2)
    (by rw [hKid_ex hc]; simp only [B1.Digest.claimBig, B1.Digest.maxKeys]; omega)
    (by rw [hKid_ex hc]; exact kid_length_flatMap_const _ fun a _ => kid_length_claimCells _ _ _)
    (fun x hx => by
      obtain ⟨a, -, hx⟩ := List.mem_flatMap.mp hx
      exact claimCells_canonical _ _ _ x hx)
    (by omega) (by omega)
    (fun rd hM j hj => by
      rw [hKid_ex hc] at hj
      obtain ⟨hlt, hidx, hget⟩ := slot j hj
      have hlt' : ((xPlan s w).childSlots.getD c []).getD j 0 <
          s.claims.xmss.length + (xPlan s w).duplicates.length := by
        have := hlt; rw [List.length_append] at this; exact this
      obtain ⟨r1, r2, r4, -⟩ := reads_buf fs fp seed s w hM
      refine ⟨belowLog_of hlt' (by omega), ?_, fun i hi => ?_⟩
      · rw [loadHolds_mul_gen_pow, Nat.add_zero,
          show (hKid s w c).base * gen ^ j = gen ^ (hW s w c + j) from (pow_add _ _ _).symm]
        have := loadHolds_getD r4 (k := ((xPlan s w).childSlots.getD c []).getD j 0)
          (by rw [kid_length_hCover]; omega)
        rw [kid_hCover_x hlt', show (slotsOf (xPlan s w)).idxOf (((xPlan s w).childSlots.getD c []).getD j 0) =
          _ from hidx, kid_hMarkX_child hc hj] at this
        exact this
      · have hlt2 : ((xPlan s w).childSlots.getD c []).getD j 0 <
            (s.claims.xmss ++ (xPlan s w).duplicates).length := hlt
        have := loadHolds_getD r1 (k := 4 * ((xPlan s w).childSlots.getD c []).getD j 0 + i)
          (by rw [hT]; omega)
        rw [getD_flatMap_uniform (f := fun c => claimCells c.1.root c.1.parameter c.2) _
          (fun a _ => kid_length_claimCells _ _ _) _ hlt2 i hi] at this
        have eT : (s.claims.xmss ++ (xPlan s w).duplicates)[((xPlan s w).childSlots.getD c []).getD j 0]'hlt2 =
            w.children[c].statement.claims.xmss[j] := by
          have h := hget
          change (s.claims.xmss ++ (xPlan s w).duplicates)[((xPlan s w).childSlots.getD c []).getD j 0]? = _ at h
          rw [List.getElem?_eq_getElem hlt2] at h
          simpa using h
        rw [eT] at this
        rw [getD_flatMap_uniform (f := fun c => claimCells c.1.root c.1.parameter c.2) _
          (fun a _ => kid_length_claimCells _ _ _) j hj i hi]
        exact this)
    (fun j hj => by
      rw [hKid_ex hc] at hj
      have hlt' : ((xPlan s w).childSlots.getD c []).getD j 0 <
          s.claims.xmss.length + (xPlan s w).duplicates.length := by
        have := (slot j hj).1; rw [List.length_append] at this; exact this
      exact region_buf fs fp seed s w (i := 2) (by omega)
        (show _ < (hCover s w).length by rw [kid_length_hCover]; omega))
    (fun j hj i hi => by
      rw [hKid_ex hc] at hj
      have hlt' : ((xPlan s w).childSlots.getD c []).getD j 0 <
          s.claims.xmss.length + (xPlan s w).duplicates.length := by
        have := (slot j hj).1; rw [List.length_append] at this; exact this
      rw [Nat.add_assoc]
      exact region_buf fs fp seed s w (i := 0) (by omega)
        (show _ < ((s.claims.xmss ++ (xPlan s w).duplicates).flatMap
          fun c => claimCells c.1.root c.1.parameter c.2).length by rw [hT]; omega))
  rw [hKid_cx hc, xmssList_cells]
  exact this

/-- **Child `c`'s leanSPHINCS list is complete.** -/
theorem kidT_hS (cert : String → V → ℕ) (hl : DeployedLimits s w) {c : ℕ}
    (hc : c < w.children.length) :
    CompleteAtDT fs cert 20 "child_claim_list_digest" (hLmain fs fp seed s w)
      [(hm fs fp seed s w).a80,
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hKid s w c).base * gen ^ (hKid s w c).ex,
        gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd), gen ^ (hKid s w c).es]
      (Returns [(hKid s w c).cs.1, (hKid s w c).cs.2]) (ccHonest (hKid s w c).es) := by
  have hcov := cover_bound hl
  have hlen := (hl.childClaimListsBelow2Pow20 _ (List.getElem_mem hc)).2
  have hT := kid_length_flatMap_const (f := fun c : LeanSphincsClaim => claimCells c.1.publicSeed c.1.root c.2)
    (s.claims.sphincs ++ (sPlan s w).duplicates) fun a _ => kid_length_claimCells _ _ _
  rw [List.length_append] at hT
  have slot := fun j (hj : j < w.children[c].statement.claims.sphincs.length) =>
    plan_slot s.claims.sphincs (w.sphincsSignatures.map (·.1))
      (w.children.map (·.statement.claims.sphincs)) (c := c) (j := j) (by simpa using hc)
      (by simpa using hj)
  have := B1.Digest.child_claim_list_digest_completeAtT fs cert (κ := 20) (by norm_num)
    (Lin := hLmain fs fp seed s w) (eP := hP fs fp seed s w 1)
    (rg := hP fs fp seed s w 2 + (s.claims.xmss.length + (xPlan s w).duplicates.length))
    (L := s.claims.sphincs.length + (sPlan s w).duplicates.length) (n := (hKid s w c).es)
    (base := (hKid s w c).base * gen ^ (hKid s w c).ex)
    (o := fun j => ((sPlan s w).childSlots.getD c []).getD j 0)
    (cells := w.children[c].statement.claims.sphincs.flatMap
      fun c => claimCells c.1.publicSeed c.1.root c.2)
    (by rw [hKid_es hc]; simp only [B1.Digest.claimBig, B1.Digest.maxKeys]; omega)
    (by rw [hKid_es hc]; exact kid_length_flatMap_const _ fun a _ => kid_length_claimCells _ _ _)
    (fun x hx => by
      obtain ⟨a, -, hx⟩ := List.mem_flatMap.mp hx
      exact claimCells_canonical _ _ _ x hx)
    (by omega) (by omega)
    (fun rd hM j hj => by
      rw [hKid_es hc] at hj
      obtain ⟨hlt, hidx, hget⟩ := slot j hj
      have hlt' : ((sPlan s w).childSlots.getD c []).getD j 0 <
          s.claims.sphincs.length + (sPlan s w).duplicates.length := by
        have := hlt; rw [List.length_append] at this; exact this
      obtain ⟨r1, r2, r4, -⟩ := reads_buf fs fp seed s w hM
      refine ⟨belowLog_of hlt' (by omega), ?_, fun i hi => ?_⟩
      · rw [← pow_add, Nat.add_assoc, pow_add, loadHolds_mul_gen_pow, Nat.add_zero,
          show (hKid s w c).base * gen ^ (hKid s w c).ex * gen ^ j = gen ^ (hW s w c + hEx w c + j) by
            rw [pow_add, pow_add]; rfl]
        have := loadHolds_getD r4 (k := s.claims.xmss.length + (xPlan s w).duplicates.length +
          ((sPlan s w).childSlots.getD c []).getD j 0) (by rw [kid_length_hCover]; omega)
        rw [kid_hCover_s hlt', show (slotsOf (sPlan s w)).idxOf (((sPlan s w).childSlots.getD c []).getD j 0) =
          _ from hidx, kid_hMarkS_child hc hj] at this
        exact this
      · have hlt2 : ((sPlan s w).childSlots.getD c []).getD j 0 <
            (s.claims.sphincs ++ (sPlan s w).duplicates).length := hlt
        have := loadHolds_getD r2 (k := 4 * ((sPlan s w).childSlots.getD c []).getD j 0 + i)
          (by rw [hT]; omega)
        rw [getD_flatMap_uniform (f := fun c => claimCells c.1.publicSeed c.1.root c.2) _
          (fun a _ => kid_length_claimCells _ _ _) _ hlt2 i hi] at this
        have eT : (s.claims.sphincs ++ (sPlan s w).duplicates)[((sPlan s w).childSlots.getD c []).getD j 0]'hlt2 =
            w.children[c].statement.claims.sphincs[j] := by
          have h := hget
          change (s.claims.sphincs ++ (sPlan s w).duplicates)[((sPlan s w).childSlots.getD c []).getD j 0]? = _ at h
          rw [List.getElem?_eq_getElem hlt2] at h
          simpa using h
        rw [eT] at this
        rw [getD_flatMap_uniform (f := fun c => claimCells c.1.publicSeed c.1.root c.2) _
          (fun a _ => kid_length_claimCells _ _ _) j hj i hi]
        exact this)
    (fun j hj => by
      rw [hKid_es hc] at hj
      have hlt' : ((sPlan s w).childSlots.getD c []).getD j 0 <
          s.claims.sphincs.length + (sPlan s w).duplicates.length := by
        have := (slot j hj).1; rw [List.length_append] at this; exact this
      rw [Nat.add_assoc]
      exact region_buf fs fp seed s w (i := 2) (by omega)
        (show _ < (hCover s w).length by rw [kid_length_hCover]; omega))
    (fun j hj i hi => by
      rw [hKid_es hc] at hj
      have hlt' : ((sPlan s w).childSlots.getD c []).getD j 0 <
          s.claims.sphincs.length + (sPlan s w).duplicates.length := by
        have := (slot j hj).1; rw [List.length_append] at this; exact this
      rw [Nat.add_assoc]
      exact region_buf fs fp seed s w (i := 1) (by omega)
        (show _ < ((s.claims.sphincs ++ (sPlan s w).duplicates).flatMap
          fun c => claimCells c.1.publicSeed c.1.root c.2).length by rw [hT]; omega))
  rw [hKid_cs hc, sphincsList_cells]
  rw [pow_add (a := gen) (hP fs fp seed s w 2)] at this
  exact this

/-- **The children's claim lists' digests on the honest run, by trees of honest shape.** -/
theorem childListGoalsT_honest (cert : String → V → ℕ)
    (hl : DeployedLimits s w) :
    ChildListGoalsT fs cert fp seed s w (fun c => ccHonest (hKid s w c).ex)
      (fun c => ccHonest (hKid s w c).es) := fun _ hc =>
  ⟨kidT_hX cert hl hc, kidT_hS cert hl hc⟩

end
end LeanVM.Guest.B1.Main
