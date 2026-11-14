/-
  LeanVM.Guest.B1.Main.MainGoalsDaAgR

  `main`'s `da_verify` and `aggregate_claims` calls on an honest run, within their bounds, by trees popping their honest
  entries (route R): the DA check's (`daPopsH`) and the batching's hints (`Hints.batchPushes`).

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Main.MainPopsSR
public import LeanVM.Guest.B1.Main.MainGoalsDvTB
public import LeanVM.Guest.B1.Main.MainGoalsHAgTB
public import LeanVM.Guest.B1.Da.DvAtP

/-!
# `da_verify` and `aggregate_claims`, route R

* `CompleteAtDTBR.with_total`: the tree's words within the bound, in the predicate;
* `mainGoalDvTBP`: `mainGoalDvTB` by trees whose valid instances pop `daPopsH w` (`Da.da_verify_completeAtTBP`);
* `mainGoalAgTBR`: `mainGoalAgTB` by trees popping the batching's hints (`aggregate_claims_completeAtTBR`);
* `mainGoalsRR_dv`, `mainGoalsRR_ag`: `MainGoalsRR`'s fields for them, `q` popping those entries;
* `mainGoalAgTBRE`, `mainGoalsRR_agE`: the same with every node exact (`aggregate_claims_completeAtTBRE`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (GuestLimits)
open LeanVM.Guest.B1 (LowDef CompleteAtDTB CompleteAtDTBR Returns)
open LeanVM.Guest.B1.Da (reads_of_memL wLog)

@[expose] public section

/-- **The tree within the bound**: a `CompleteAtDTBR` tree's words are its size, at most `B`. -/
theorem _root_.LeanVM.Guest.B1.CompleteAtDTBR.with_total {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ}
    {f : String} {Lin : Layout} {args : List E} {Out : List E → Layout → Prop} {T : Reader → Tree → Prop} {B : ℕ}
    (h : CompleteAtDTBR fs cert k f Lin args Out T B) :
    CompleteAtDTBR fs cert k f Lin args Out (fun rd t => T rd t ∧ t.total fs ≤ B) B := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ⟨hn', hv, hb, hp, ht, hrest⟩, hT⟩ := hr rd hl hm
    ⟨t, ⟨hn', hv, hb, hp, ht, hrest⟩, hT, ht ▸ hn⟩⟩

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) {seed : Digest} {s : NodeStatement}
  {w : NodeWitness} {bytecode : List K}

/-- **`da_verify` on an honest run, by a tree of its honest shape whose valid instances pop `daPopsH w`, within
`hDvB`.** -/
theorem mainGoalDvTBP (hn : NodeRelation bytecode seed s w) (hrf : Lift.RunsFit fs cert)
    {SB SK : String → ℕ} (hS : Da.DvStaticB fs SB SK) : (hm fs fp seed s w).nd = 1 →
    CompleteAtDTB fs cert 20 "da_verify" (hLmain fs fp seed s w) [(hm fs fp seed s w).et]
      (Returns (hm fs fp seed s w).daR)
      (fun t => hDvNH w t ∧ ∀ (rd : Reader) (args rets : List E), t.Valid coreProgram rd args rets →
        t.pops coreProgram rd = daPopsH w) (hDvB fs SB SK w) := by
  intro h1
  obtain ⟨p, hp, hR, hw⟩ := checked_da fs fp hn h1
  rw [hR, hDvNH, hDvB, daPopsH, hp]
  simp only [Option.map_some, Option.getD_some]
  have hL := wLog_lt hw
  have h := Da.da_verify_completeAtTBP cert hrf hw (etB fs (mK0 (hData seed s w) fs fp)) hS
  have hq : (etB fs (mK0 (hData seed s w) fs fp), expTabAllWords) ∈ hLmain fs fp seed s w :=
    List.mem_append_right _ (by simp [etL])
  have hlen : expTabAllWords.length = 2284 := length_expTabAllWords
  refine completeAtDTB_lin_mono (fun rd hM => ?_) (fun i hi => ?_) (h.lowMono (by norm_num))
  · have hr := reads_of_memL hM hq (wLog p.2) (by omega)
    rw [expTabAllWords_sq (by omega)] at hr
    intro q hq'
    rw [List.mem_singleton] at hq'
    subst hq'
    intro k hk
    simp only [List.length_singleton, Nat.lt_one_iff] at hk
    subst hk
    rw [← gen_pow_eq_ofK, pow_add, loadHolds_mul_gen_pow, Nat.add_zero]
    exact hr
  · obtain ⟨q, hq', h1, h2⟩ := hi
    rw [List.mem_singleton] at hq'
    subst hq'
    simp only [List.length_singleton] at h1 h2
    refine ⟨_, hq, by dsimp only; omega, ?_⟩
    dsimp only
    rw [hlen]
    omega

/-- **`MainGoalsRR.dv`**, `q` popping `da_verify`'s honest entries. -/
theorem mainGoalsRR_dv (hn : NodeRelation bytecode seed s w) (hrf : Lift.RunsFit fs cert) {SB SK : String → ℕ}
    {Bv : ℕ → ℕ} {Pvs : ℕ → Tree → Prop} {q : MainPops} (hS : MainStatics fs SB SK)
    (hq : ∀ rd, q.pd rd = daPopsH w) : (hm fs fp seed s w).nd = 1 →
    CompleteAtDTBR fs cert 20 "da_verify" (hLmain fs fp seed s w) [(hm fs fp seed s w).et]
      (Returns (hm fs fp seed s w).daR) (mainPredsHP fs SB SK Bv Pvs s w q).Pd (mainBsH fs SB SK Bv s w).Bd :=
  fun h1 => ((mainGoalDvTBP fs cert fp hn hrf hS.dv h1).with_total.withPops (ps := fun _ => daPopsH w)
    fun rd _ _ _ _ hv hT => hT.1.2 rd _ _ hv).mono le_rfl fun rd _ h => ⟨⟨h.1.1.1, h.1.2⟩, h.2.trans (hq rd).symm⟩

/-- **`main`'s honest `aggregate_claims` call within `aggB`, by a tree of honest shape popping the batching's
hints, every node exact.** -/
theorem mainGoalAgTBRE (SB SK : String → ℕ)
    (hGr : TotalLe coreProgram fs "grind_check__L2" (fun _ => SB "grind_check__L2"))
    (h25 : TotalLeOn coreProgram fs name% «aggregate_claims_loop0» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «aggregate_claims_loop0» + fs
          name% «aggregate_claims_loop0»))
    (h26 : TotalLeOn coreProgram fs name% «aggregate_claims_loop1» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «aggregate_claims_loop1» + fs
          name% «aggregate_claims_loop1»))
    (h27 : TotalLeOn coreProgram fs name% «aggregate_claims_loop2» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «aggregate_claims_loop2» + fs
          name% «aggregate_claims_loop2»))
    (hbs : TotalLe coreProgram fs "batch_sumcheck__L23" (fun _ => SB "batch_sumcheck__L23"))
    (hbl : bytecode.length = 2 ^ bytecodeVars) (hrel : NodeRelation bytecode seed s w)
    (hl : GuestLimits s w) : (hm fs fp seed s w).nc ≠ 0 →
      CompleteAtDTBR fs cert 20 "aggregate_claims" (hLmain fs fp seed s w)
        [gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a394, (hm fs fp seed s w).a400,
          (hm fs fp seed s w).a406, (hm fs fp seed s w).a417,
          (hm fs fp seed s w).et * word 133823759239872512 0] (Returns [])
        (fun rd t => (aggHonest (hm fs fp seed s w).nc t ∧
          t.pops coreProgram rd = Hints.batchPushes w.batchingHints) ∧ t.Every (ExactAt coreProgram rd))
        (aggB fs SB SK (hm fs fp seed s w).nc) := by
  intro hnc
  have hnc' : w.children.length ≠ 0 := hnc
  have hne : w.children ≠ [] := fun h => hnc' (by rw [h, List.length_nil])
  have hb := (nodeRel_iff.mp hrel).2.2.2.2
  simp only [hne, ↓reduceIte] at hb
  have hlog : Nat.log2 bytecode.length = bytecodeVars := by rw [hbl, Nat.log2_two_pow]
  have hrl : w.batchingHints.sumcheckMessages.length = 23 := by
    have hpt : s.deferredClaim.bytecodePoint.length = 23 := by rw [hrel.hasBytecodeShape, hlog]
    rw [(batch_out hb).1, aggOut, aggRun, bsRun_len] at hpt
    exact hpt
  have hdst := mem_hLmain fs fp seed s w (i := 9) (by omega)
  simp only [hOwn, List.getD_cons_succ, List.getD_cons_zero] at hdst
  have := aggregate_claims_completeAtTBRE fs cert SB SK hGr h25 h26 h27 hbs
    (m := w.children.length) (by omega) hl.atMostSixteenChildren (cs := hKids seed w)
    (by rw [List.length_map]) hrl hb (fun rd hM => hkids_words fs fp hbl hrel hM)
    (fun rd _ hM => hLmain_winTabs fs fp hM) hdst
  exact this.lowMono (by norm_num)

/-- **`main`'s honest `aggregate_claims` call within `aggB`, by a tree of honest shape popping the batching's
hints.** -/
theorem mainGoalAgTBR (SB SK : String → ℕ)
    (hGr : TotalLe coreProgram fs "grind_check__L2" (fun _ => SB "grind_check__L2"))
    (h25 : TotalLeOn coreProgram fs name% «aggregate_claims_loop0» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «aggregate_claims_loop0» + fs
          name% «aggregate_claims_loop0»))
    (h26 : TotalLeOn coreProgram fs name% «aggregate_claims_loop1» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «aggregate_claims_loop1» + fs
          name% «aggregate_claims_loop1»))
    (h27 : TotalLeOn coreProgram fs name% «aggregate_claims_loop2» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «aggregate_claims_loop2» + fs
          name% «aggregate_claims_loop2»))
    (hbs : TotalLe coreProgram fs "batch_sumcheck__L23" (fun _ => SB "batch_sumcheck__L23"))
    (hbl : bytecode.length = 2 ^ bytecodeVars) (hrel : NodeRelation bytecode seed s w)
    (hl : GuestLimits s w) : (hm fs fp seed s w).nc ≠ 0 →
      CompleteAtDTBR fs cert 20 "aggregate_claims" (hLmain fs fp seed s w)
        [gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a394, (hm fs fp seed s w).a400,
          (hm fs fp seed s w).a406, (hm fs fp seed s w).a417,
          (hm fs fp seed s w).et * word 133823759239872512 0] (Returns [])
        (fun rd t => aggHonest (hm fs fp seed s w).nc t ∧ t.pops coreProgram rd = Hints.batchPushes w.batchingHints)
        (aggB fs SB SK (hm fs fp seed s w).nc) := fun h0 =>
  (mainGoalAgTBRE fs cert fp SB SK hGr h25 h26 h27 hbs hbl hrel hl h0).mono le_rfl fun _ _ h => h.1

/-- **`MainGoalsRR.ag`**, `q` popping the batching's hints. -/
theorem mainGoalsRR_ag (hbl : bytecode.length = 2 ^ 23) (hn : NodeRelation bytecode seed s w) (hl : GuestLimits s w)
    {SB SK : String → ℕ} {Bv : ℕ → ℕ} {Pvs : ℕ → Tree → Prop} {q : MainPops} (hS : MainStatics fs SB SK)
    (hq : ∀ rd, q.pa rd = Hints.batchPushes w.batchingHints) : (hm fs fp seed s w).nc ≠ 0 →
    CompleteAtDTBR fs cert 20 "aggregate_claims" (hLmain fs fp seed s w)
      [gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a394, (hm fs fp seed s w).a400,
        (hm fs fp seed s w).a406, (hm fs fp seed s w).a417,
          (hm fs fp seed s w).et * word 133823759239872512 0] (Returns [])
      (mainPredsHP fs SB SK Bv Pvs s w q).Pa (mainBsH fs SB SK Bv s w).Ba := fun h0 =>
  (mainGoalAgTBR fs cert fp SB SK hS.gr hS.l25 hS.l26 hS.l27 hS.bs hbl hn hl h0).with_total.mono le_rfl
    fun rd _ h => ⟨⟨h.1.1, h.2⟩, h.1.2.trans (hq rd).symm⟩

/-- **`MainGoalsRR.ag`, every node exact**, `q` popping the batching's hints. -/
theorem mainGoalsRR_agE (hbl : bytecode.length = 2 ^ 23) (hn : NodeRelation bytecode seed s w) (hl : GuestLimits s w)
    {SB SK : String → ℕ} {Bv : ℕ → ℕ} {Pvs : ℕ → Tree → Prop} {q : MainPops} (hS : MainStatics fs SB SK)
    (hq : ∀ rd, q.pa rd = Hints.batchPushes w.batchingHints) : (hm fs fp seed s w).nc ≠ 0 →
    CompleteAtDTBR fs cert 20 "aggregate_claims" (hLmain fs fp seed s w)
      [gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a394, (hm fs fp seed s w).a400,
        (hm fs fp seed s w).a406, (hm fs fp seed s w).a417,
          (hm fs fp seed s w).et * word 133823759239872512 0] (Returns [])
      (fun rd t => (mainPredsHP fs SB SK Bv Pvs s w q).Pa rd t ∧ t.Every (ExactAt coreProgram rd))
      (mainBsH fs SB SK Bv s w).Ba := fun h0 =>
  (mainGoalAgTBRE fs cert fp SB SK hS.gr hS.l25 hS.l26 hS.l27 hS.bs hbl hn hl h0).with_total.mono le_rfl
    fun rd _ h => ⟨⟨⟨h.1.1.1, h.2⟩, h.1.1.2.trans (hq rd).symm⟩, h.1.2⟩

end
end LeanVM.Guest.B1.Main
