/-
  LeanVM.Guest.B1.Main.MainGoalsClR

  `main`'s two claim lists' digests on its honest run (route R): within their bounds by trees of honest shape popping the claim list's honest pushes (`MainGoalsRR.clx`, `.cls`), and their `MainSegs` facts.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListPops
public import LeanVM.Guest.B1.Main.MainGoalsHKid
public import LeanVM.Guest.Budget.FinalP

/-!
# `main`'s claim lists, with their pops

* `claimPops_of_reads`: claims read off a table holding `L`'s cells, four a claim, are `L`'s entries;
* `cl_pops_honest`: a valid tree of `claim_list_digest` of honest shape on a table holding a list's cells pops `Hints.listPushes "claims"` of it;
* `mainGoalClXR`, `mainGoalClSR`: `MainGoalsRR`'s `clx`, `cls`, given `q.px`, `q.ps` are the lists' pushes; `mainSegs_cx`, `mainSegs_cs`: `MainSegs`' `cx`, `cs`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (CompleteAtDTBR CompleteAtDTB Returns)
open LeanVM.Guest.B1.Digest (claimPop cl_valid_pops claimBig bigFramesCap)
open LeanVM.Guest.Hints (claimCells)

@[expose] public section

variable {rd : Reader}

/-- **Claims read off a table holding `L`'s cells**, four a claim, are `L`'s entries. -/
theorem claimPops_of_reads {α : Type} {f : α → List E} {L : List α} (hf : ∀ a ∈ L, (f a).length = 4) {e : ℕ}
    (hr : ReadsAt rd (gen ^ e) (L.flatMap f)) :
    (List.range L.length).map (claimPop rd e) = L.map fun a => ("claims", f a) := by
  refine List.ext_getElem (by simp) fun k h1 h2 => ?_
  rw [List.getElem_map, List.getElem_map, List.getElem_range, claimPop]
  have hk : k < L.length := by simpa using h1
  refine congrArg (Prod.mk "claims") (List.ext_getElem (by rw [hf _ (List.getElem_mem hk)]; simp) fun c hc _ => ?_)
  have hc4 : c < 4 := by simpa using hc
  have hlen : (L.flatMap f).length = 4 * L.length := kid_length_flatMap_const L hf
  have hl := loadHolds_getD hr (k := 4 * k + c) (by omega)
  rw [getD_flatMap_uniform L hf k hk c hc4, List.getD_eq_getElem _ _ (by rw [hf _ (List.getElem_mem hk)]; exact hc4)]
    at hl
  obtain ⟨-, hl⟩ := hl
  rw [gen_pow_eq_ofK, addr_ofK, ← Nat.add_assoc] at hl
  simp only [List.getElem_map, List.getElem_range, hl, Option.getD_some]

/-- **A valid tree of `claim_list_digest` of honest shape on a table holding a list's cells** pops the list's
honest pushes. -/
theorem cl_pops_honest {α : Type} {f : α → List E} {L : List α} (hf : ∀ a ∈ L, (f a).length = 4)
    (hn : L.length < 2 ^ 23) {e : ℕ} (hr : ReadsAt rd (gen ^ e) (L.flatMap f)) {t : Tree} {rets : List E}
    (hv : t.Valid coreProgram rd [gen ^ e, gen ^ L.length] rets) (hH : clHonest L.length t) :
    t.pops coreProgram rd = Hints.listPushes "claims" (L.map f) := by
  rw [cl_valid_pops (by simp only [claimBig, bigFramesCap]; omega) hv hH, claimPops_of_reads hf hr,
    Hints.listPushes, List.map_map]
  congr 1
  by_cases h0 : L = []
  · subst h0; rfl
  · rw [ite_eq_right (fun h => h0 (List.eq_nil_of_length_eq_zero h)),
      ite_eq_right (fun h => h0 (List.map_eq_nil_iff.mp h)), List.length_map, Hints.listSplit,
      show Hints.claimBig = 136 from rfl, show Hints.claimGroup = 17 from rfl, Nat.mod_mod_of_dvd _ (by norm_num : 17 ∣ 136), gen_pow_count (by omega), gen_pow_count (by omega),
      gen_pow_count (by omega)]

variable {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement}
  {w : NodeWitness}

/-- **`MainGoalsRR.clx`**: `claim_list_digest` on the leanXMSS list within its bound, by a tree of honest shape popping
`q.px`, the list's honest pushes. -/
theorem mainGoalClXR (hL : GuestLimits s w) {SB SK : String → ℕ} {Bv : ℕ → ℕ} {Pvs : ℕ → Tree → Prop}
    {q : MainPops} (hS : MainStatics fs SB SK)
    (hq : ∀ rd, q.px rd = Hints.listPushes "claims" (s.claims.xmss.map fun c ↦ claimCells c.1.root c.1.parameter c.2)) :
    CompleteAtDTBR fs cert 20 "claim_list_digest" (hLmain fs fp seed s w)
      [(hm fs fp seed s w).a77, gen ^ (hm fs fp seed s w).nlx]
      (Returns (B1.Digest.digestCells (hm fs fp seed s w).xd)) (mainPredsHP fs SB SK Bv Pvs s w q).Px
      (mainBsH fs SB SK Bv s w).Bx := by
  have hn := (Budget.claims_lt hL).1
  refine CompleteAtDTB.withPops (mainGoalClXTB fs cert fp seed s w hL hS.ls hS.l15 hS.l16 hS.cl).with_total
    fun rd _ hM t rets hv hT => ?_
  have e : (hOwn seed s w).getD 0 [] =
      s.claims.xmss.flatMap (fun c => claimCells c.1.root c.1.parameter c.2) ++
        (xPlan s w).duplicates.flatMap (fun c => claimCells c.1.root c.1.parameter c.2) := by
    rw [← List.flatMap_append]; rfl
  have hr := mf_reads fs fp seed s w hM (i := 0) (by omega)
  rw [e] at hr
  rw [hq]
  exact cl_pops_honest (fun c _ => mf_claimCells_length _ _ _) hn (readsAt_append'.mp hr).1 hv hT.1

/-- **`MainGoalsRR.cls`**: `claim_list_digest` on the leanSPHINCS list within its bound, by a tree of honest shape
popping `q.ps`, the list's honest pushes. -/
theorem mainGoalClSR (hL : GuestLimits s w) {SB SK : String → ℕ} {Bv : ℕ → ℕ} {Pvs : ℕ → Tree → Prop}
    {q : MainPops} (hS : MainStatics fs SB SK)
    (hq : ∀ rd, q.ps rd = Hints.listPushes "claims"
      (s.claims.sphincs.map fun c ↦ claimCells c.1.publicSeed c.1.root c.2)) :
    CompleteAtDTBR fs cert 20 "claim_list_digest" (hLmain fs fp seed s w)
      [(hm fs fp seed s w).a80, gen ^ (hm fs fp seed s w).nls]
      (Returns (B1.Digest.digestCells (hm fs fp seed s w).sd)) (mainPredsHP fs SB SK Bv Pvs s w q).Ps
      (mainBsH fs SB SK Bv s w).Bs := by
  have hn := (Budget.claims_lt hL).2
  refine CompleteAtDTB.withPops (mainGoalClSTB fs cert fp seed s w hL hS.ls hS.l15 hS.l16 hS.cl).with_total
    fun rd _ hM t rets hv hT => ?_
  have e : (hOwn seed s w).getD 1 [] =
      s.claims.sphincs.flatMap (fun c => claimCells c.1.publicSeed c.1.root c.2) ++
        (sPlan s w).duplicates.flatMap (fun c => claimCells c.1.publicSeed c.1.root c.2) := by
    rw [← List.flatMap_append]; rfl
  have hr := mf_reads fs fp seed s w hM (i := 1) (by omega)
  rw [e] at hr
  rw [hq]
  exact cl_pops_honest (fun c _ => mf_claimCells_length _ _ _) hn (readsAt_append'.mp hr).1 hv hT.1

/-- `MainSegs.cx` for `q.px` the leanXMSS list's pushes. -/
theorem mainSegs_cx {q : MainPops}
    (hq : ∀ rd, q.px rd = Hints.listPushes "claims" (s.claims.xmss.map fun c ↦ claimCells c.1.root c.1.parameter c.2))
    (rd : Reader) :
    SameStreams (q.px rd) (Hints.listPushes "claims" (s.claims.xmss.map fun c ↦ claimCells c.1.root c.1.parameter c.2)) :=
  SameStreams.of_eq (hq rd)

/-- `MainSegs.cs` for `q.ps` the leanSPHINCS list's pushes. -/
theorem mainSegs_cs {q : MainPops}
    (hq : ∀ rd, q.ps rd = Hints.listPushes "claims"
      (s.claims.sphincs.map fun c ↦ claimCells c.1.publicSeed c.1.root c.2)) (rd : Reader) :
    SameStreams (q.ps rd) (Hints.listPushes "claims"
      (s.claims.sphincs.map fun c ↦ claimCells c.1.publicSeed c.1.root c.2)) :=
  SameStreams.of_eq (hq rd)

end
end LeanVM.Guest.B1.Main
