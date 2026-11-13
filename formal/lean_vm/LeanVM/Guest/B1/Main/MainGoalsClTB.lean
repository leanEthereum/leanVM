/-
  LeanVM.Guest.B1.Main.MainGoalsClTB

  `main`'s two claim lists' digests on its honest run, by trees of honest shape, within bounds
  before the memory (`clB` of the lists' lengths): `mainGoalClXT`, `mainGoalClST` (same proofs)
  with `claim_list_digest_completeAtTB`.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsClT
public import LeanVM.Guest.B1.Digest.ClaimListAtTB
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.Data.NameStrings

/-!
# `main`'s claim lists, within bounds

`MainGoalClXTB … SB SK`, `MainGoalClSTB`: `MainGoalClXT`, `MainGoalClST` with `CompleteAtDTB`
within `clB fs SB SK` of the declared lists' lengths. `mainGoalClXTB`, `mainGoalClSTB`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (CompleteAtDT CompleteAtDTB Returns)
open LeanVM.Guest.Hints (claimCells)
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement)
  (w : NodeWitness)

/-- `MainGoalClXT` within `clB` of the declared leanXMSS list's length. -/
def MainGoalClXTB (SB SK : String → ℕ) : Prop :=
  CompleteAtDTB fs cert 20 "claim_list_digest" (hLmain fs fp seed s w)
    [(hm fs fp seed s w).a77, gen ^ (hm fs fp seed s w).nlx]
    (Returns (B1.Digest.digestCells (hm fs fp seed s w).xd)) (clHonest (hm fs fp seed s w).nlx)
    (clB fs SB SK (hm fs fp seed s w).nlx)

/-- `MainGoalClST` within `clB` of the declared leanSPHINCS list's length. -/
def MainGoalClSTB (SB SK : String → ℕ) : Prop :=
  CompleteAtDTB fs cert 20 "claim_list_digest" (hLmain fs fp seed s w)
    [(hm fs fp seed s w).a80, gen ^ (hm fs fp seed s w).nls]
    (Returns (B1.Digest.digestCells (hm fs fp seed s w).sd)) (clHonest (hm fs fp seed s w).nls)
    (clB fs SB SK (hm fs fp seed s w).nls)

variable {fs cert fp seed s w} in
theorem MainGoalClXTB.toT {SB SK : String → ℕ} (h : MainGoalClXTB fs cert fp seed s w SB SK) :
    MainGoalClXT fs cert fp seed s w :=
  CompleteAtDTB.toDT h

variable {fs cert fp seed s w} in
theorem MainGoalClSTB.toT {SB SK : String → ℕ} (h : MainGoalClSTB fs cert fp seed s w SB SK) :
    MainGoalClST fs cert fp seed s w :=
  CompleteAtDTB.toDT h

/-- **`claim_list_digest` on the leanXMSS table's declared claims, by a tree of honest shape, within
`clB`.** -/
theorem mainGoalClXTB (hL : GuestLimits s w) {SB SK : String → ℕ}
    (hLS : TotalLe coreProgram fs "list_split" (fun _ => SB "list_split"))
    (hL15 : TotalLeOn coreProgram fs name% «claim_list_digest_loop0» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «claim_list_digest_loop0» + fs name% «claim_list_digest_loop0»))
    (hL16 : TotalLeOn coreProgram fs name% «claim_list_digest_loop1» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «claim_list_digest_loop1» + fs name% «claim_list_digest_loop1»))
    (hCL : ∀ j < 17, TotalLe coreProgram fs clNames[j]! (fun _ => SB clNames[j]!)) :
    MainGoalClXTB fs cert fp seed s w SB SK := by
  have hn : s.claims.xmss.length < claimBig * bigFramesCap := by
    have := hL.planSlotsBelow2Pow23
    simp only [Coverage.planSlots] at this
    simp only [claimBig, bigFramesCap]
    omega
  have e : (hOwn seed s w).getD 0 [] =
      s.claims.xmss.flatMap (fun c => claimCells c.1.root c.1.parameter c.2) ++
        (xPlan s w).duplicates.flatMap (fun c => claimCells c.1.root c.1.parameter c.2) := by
    rw [← List.flatMap_append]; rfl
  have hl := mf_length_flatMap (fun c : LeanXmssClaim => claimCells c.1.root c.1.parameter c.2)
    (fun c => mf_claimCells_length c.1.root c.1.parameter c.2) s.claims.xmss
  have key := claim_list_digest_completeAtTB fs cert (Lin := hLmain fs fp seed s w)
    (eP := mfB fs fp seed s w 0) hn hl
    (fun rd h => by
      have h1 := mf_reads fs fp seed s w h (i := 0) (by omega)
      rw [e] at h1
      exact (readsAt_append'.mp h1).1)
    (fun k hk => mf_region fs fp seed s w (i := 0) (by omega) (by rw [e, List.length_append]; omega))
    hLS hL15 hL16 hCL
  have ha : (hm fs fp seed s w).a77 = gen ^ mfB fs fp seed s w 0 := rfl
  have hn' : (hm fs fp seed s w).nlx = s.claims.xmss.length := rfl
  have hd : (hm fs fp seed s w).xd = claimListDigest xmssPublicKeyBytes s.claims.xmss := rfl
  unfold MainGoalClXTB clHonest
  rw [ha, hn', hd, mf_xmss_digest]
  exact key.lowMono (by norm_num)

/-- **`claim_list_digest` on the leanSPHINCS table's declared claims, by a tree of honest shape,
within `clB`.** -/
theorem mainGoalClSTB (hL : GuestLimits s w) {SB SK : String → ℕ}
    (hLS : TotalLe coreProgram fs "list_split" (fun _ => SB "list_split"))
    (hL15 : TotalLeOn coreProgram fs name% «claim_list_digest_loop0» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «claim_list_digest_loop0» + fs name% «claim_list_digest_loop0»))
    (hL16 : TotalLeOn coreProgram fs name% «claim_list_digest_loop1» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «claim_list_digest_loop1» + fs name% «claim_list_digest_loop1»))
    (hCL : ∀ j < 17, TotalLe coreProgram fs clNames[j]! (fun _ => SB clNames[j]!)) :
    MainGoalClSTB fs cert fp seed s w SB SK := by
  have hn : s.claims.sphincs.length < claimBig * bigFramesCap := by
    have := hL.planSlotsBelow2Pow23
    simp only [Coverage.planSlots] at this
    simp only [claimBig, bigFramesCap]
    omega
  have e : (hOwn seed s w).getD 1 [] =
      s.claims.sphincs.flatMap (fun c => claimCells c.1.publicSeed c.1.root c.2) ++
        (sPlan s w).duplicates.flatMap (fun c => claimCells c.1.publicSeed c.1.root c.2) := by
    rw [← List.flatMap_append]; rfl
  have hl := mf_length_flatMap (fun c : LeanSphincsClaim => claimCells c.1.publicSeed c.1.root c.2)
    (fun c => mf_claimCells_length c.1.publicSeed c.1.root c.2) s.claims.sphincs
  have key := claim_list_digest_completeAtTB fs cert (Lin := hLmain fs fp seed s w)
    (eP := mfB fs fp seed s w 1) hn hl
    (fun rd h => by
      have h1 := mf_reads fs fp seed s w h (i := 1) (by omega)
      rw [e] at h1
      exact (readsAt_append'.mp h1).1)
    (fun k hk => mf_region fs fp seed s w (i := 1) (by omega) (by rw [e, List.length_append]; omega))
    hLS hL15 hL16 hCL
  have ha : (hm fs fp seed s w).a80 = gen ^ mfB fs fp seed s w 1 := rfl
  have hn' : (hm fs fp seed s w).nls = s.claims.sphincs.length := rfl
  have hd : (hm fs fp seed s w).sd = claimListDigest Sphincs.PublicKey.toBytes s.claims.sphincs := rfl
  unfold MainGoalClSTB clHonest
  rw [ha, hn', hd, mf_sphincs_digest]
  exact key.lowMono (by norm_num)


end
end LeanVM.Guest.B1.Main
