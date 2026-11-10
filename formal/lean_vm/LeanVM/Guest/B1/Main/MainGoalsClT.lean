/-
  LeanVM.Guest.B1.Main.MainGoalsClT

  `main`'s claim lists' digests on an honest run, by trees of honest shape (`Budget.NodeHonest`).
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsFCl
public import LeanVM.Guest.B1.Digest.ClaimListAt
public import LeanVM.Guest.AcceptableChild

/-!
# `main`'s claim lists' digests, by trees of honest shape

`clHonest n`: the honest shape of `claim_list_digest` on a list of `n` claims
(`Digest/ClaimListAt.lean`). `MainGoalClXT`, `MainGoalClST`: `MainGoalClX`,
`MainGoalClS` by trees of shape `clHonest` at the declared lists' lengths (`nlx`, `nls`);
`mainGoalClXT`, `mainGoalClST` prove them (same proofs as `mainGoalClX`, `mainGoalClS`), and
`MainGoalClXT.goal`, `MainGoalClST.goal` give back the plain goals.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (CompleteAtDT Returns)
open LeanVM.Guest.Hints (claimCells)
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

/-- **`claim_list_digest`'s honest shape** on `n` claims. -/
def clHonest (n : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "claim_list_digest" (clQ n) (clCalls n) (clBufs n) clTs

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement)
  (w : NodeWitness)

/-- `MainGoalClX` by a tree of honest shape. -/
def MainGoalClXT : Prop :=
  CompleteAtDT fs cert 16 "claim_list_digest" (hLmain fs fp seed s w)
    [(hm fs fp seed s w).a77, gen ^ (hm fs fp seed s w).nlx]
    (Returns (B1.Digest.digestCells (hm fs fp seed s w).xd)) (clHonest (hm fs fp seed s w).nlx)

/-- `MainGoalClS` by a tree of honest shape. -/
def MainGoalClST : Prop :=
  CompleteAtDT fs cert 16 "claim_list_digest" (hLmain fs fp seed s w)
    [(hm fs fp seed s w).a80, gen ^ (hm fs fp seed s w).nls]
    (Returns (B1.Digest.digestCells (hm fs fp seed s w).sd)) (clHonest (hm fs fp seed s w).nls)

variable {fs cert fp seed s w} in
theorem MainGoalClXT.goal (h : MainGoalClXT fs cert fp seed s w) : MainGoalClX fs cert fp seed s w :=
  CompleteAtDT.toD h

variable {fs cert fp seed s w} in
theorem MainGoalClST.goal (h : MainGoalClST fs cert fp seed s w) : MainGoalClS fs cert fp seed s w :=
  CompleteAtDT.toD h

/-- **`claim_list_digest` on the leanXMSS table's declared claims, by a tree of honest shape.** -/
theorem mainGoalClXT (hL : DeployedLimits s w) : MainGoalClXT fs cert fp seed s w := by
  have hn : s.claims.xmss.length < claimBig * maxKeys := by
    have := hL.planSlotsBelow2Pow16
    simp only [Coverage.planSlots] at this
    simp only [claimBig, maxKeys]
    omega
  have e : (hOwn seed s w).getD 0 [] =
      s.claims.xmss.flatMap (fun c => claimCells c.1.root c.1.parameter c.2) ++
        (xPlan s w).duplicates.flatMap (fun c => claimCells c.1.root c.1.parameter c.2) := by
    rw [← List.flatMap_append]; rfl
  have hl := mf_length_flatMap (fun c : LeanXmssClaim => claimCells c.1.root c.1.parameter c.2)
    (fun c => mf_claimCells_length c.1.root c.1.parameter c.2) s.claims.xmss
  have key := claim_list_digest_completeAtT fs cert (Lin := hLmain fs fp seed s w)
    (eP := mfB fs fp seed s w 0) hn hl
    (fun rd h => by
      have h1 := mf_reads fs fp seed s w h (i := 0) (by omega)
      rw [e] at h1
      exact (readsAt_append'.mp h1).1)
    (fun k hk => mf_region fs fp seed s w (i := 0) (by omega) (by rw [e, List.length_append]; omega))
  have ha : (hm fs fp seed s w).a77 = gen ^ mfB fs fp seed s w 0 := rfl
  have hn' : (hm fs fp seed s w).nlx = s.claims.xmss.length := rfl
  have hd : (hm fs fp seed s w).xd = claimListDigest xmssPublicKeyBytes s.claims.xmss := rfl
  unfold MainGoalClXT clHonest
  rw [ha, hn', hd, mf_xmss_digest]
  exact key

/-- **`claim_list_digest` on the leanSPHINCS table's declared claims, by a tree of honest shape.** -/
theorem mainGoalClST (hL : DeployedLimits s w) : MainGoalClST fs cert fp seed s w := by
  have hn : s.claims.sphincs.length < claimBig * maxKeys := by
    have := hL.planSlotsBelow2Pow16
    simp only [Coverage.planSlots] at this
    simp only [claimBig, maxKeys]
    omega
  have e : (hOwn seed s w).getD 1 [] =
      s.claims.sphincs.flatMap (fun c => claimCells c.1.publicSeed c.1.root c.2) ++
        (sPlan s w).duplicates.flatMap (fun c => claimCells c.1.publicSeed c.1.root c.2) := by
    rw [← List.flatMap_append]; rfl
  have hl := mf_length_flatMap (fun c : LeanSphincsClaim => claimCells c.1.publicSeed c.1.root c.2)
    (fun c => mf_claimCells_length c.1.publicSeed c.1.root c.2) s.claims.sphincs
  have key := claim_list_digest_completeAtT fs cert (Lin := hLmain fs fp seed s w)
    (eP := mfB fs fp seed s w 1) hn hl
    (fun rd h => by
      have h1 := mf_reads fs fp seed s w h (i := 1) (by omega)
      rw [e] at h1
      exact (readsAt_append'.mp h1).1)
    (fun k hk => mf_region fs fp seed s w (i := 1) (by omega) (by rw [e, List.length_append]; omega))
  have ha : (hm fs fp seed s w).a80 = gen ^ mfB fs fp seed s w 1 := rfl
  have hn' : (hm fs fp seed s w).nls = s.claims.sphincs.length := rfl
  have hd : (hm fs fp seed s w).sd = claimListDigest Sphincs.PublicKey.toBytes s.claims.sphincs := rfl
  unfold MainGoalClST clHonest
  rw [ha, hn', hd, mf_sphincs_digest]
  exact key


end
end LeanVM.Guest.B1.Main
