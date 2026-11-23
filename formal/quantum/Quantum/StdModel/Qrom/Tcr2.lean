module

public import Quantum.StdModel.Qrom.Tcr

@[expose] public section

/-!
# SM-TCR-C in the QROM: free answers and free re-reads of the records

`Quantum.StdModel.Qrom.Tcr` charges every classical read of a `G`-cell, the challenger's answers
to the reduction's targets included. This file charges only the reads that can enter the event.

* **Poison answers** (`uAnsP`): every answer read of a `G`-cell without a record records it. A
  class with two records has no target, so before the reduction's first own read and the
  adversary's first call (phase `some false`) no `G`-cell outside the records is in the database
  or hardwired (`PhA`): the register is outside the event and the answers are free.
* **Charged reads** (`Chg`): a read of the setup, the reduction or the decision at a `G`-cell that
  is no record. A read of a record or off the classes has an empty target and is invisible
  (`badR_iff_of_read`): the reduction's re-reads of its targets are free.
* **The count** (`MemK`, `updK`): the mixed game tracks the memory with the number of charged
  reads; the read program's modes (`RMode`) add the phase. The graded bound along modes
  (`rpow_inv_two_tsum_potential_runtime2_moded`) pays `√(gradeEta F)` per adversary call and per
  charged read.

`probAvg_smTcrIn_slRed_le_count`: with `q` adversary calls and at most `n` charged reads on every
live run, the average winning probability is at most `(q + n)² · gradeEta F`.
`probAvg_smTcrIn_slRed_le_free`: if the reduction's own reads of `G`-cells are at most `c₀` in its
setup, none in its handler and at most `c₁` in its output, `n = c₀ + c₁ + 1`.

**Live runs at a table** (for handlers that only re-read the targets): a live run is a run at
every table consistent with its final log (`mem_support_logImpl_of_liveRedRun`), and an algorithm
that never fails at those tables under the failing semantics (`failImpl`, failing at the charged
cells) makes no charged read on its live runs (`liveRedRun_of_fail`).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.StdModel.Qrom.Tcr2

open Quantum Quantum.Qrom Quantum.Sponge Props HashSig
open Quantum.StdModel.Qrom.Tcr
open Quantum.Xmss.Assembly (ModedP modedP_bind modedP₂_bind modedP_map modeCmdOk modeCmdNx)
open Quantum.Xmss.Hybrid (runtime2 runtime2_branch kraus2)

/-! ## The policies and the charged reads -/

section policy

variable {Par Tw Fn Out : Type} {Msg : Fn → Type} (C : TwColl Par Tw Fn Msg Out)
  (G : Fn → Tw → Prop)

open scoped Classical in
/-- **The challenger's answers**: log the outcome; a `G`-cell that is no record becomes one, with
the outcome (`0` if none). -/
noncomputable def uAnsP (z : HashDomain) (m : Mem) (o : Option HashOutput) : Mem :=
  (m.1, Function.update m.log z o, m.seen,
    if IsG C G z ∧ m.recs z = none then Function.update m.recs z (some (o.getD 0)) else m.recs,
    m.slot)

/-- **The policy of each caller**: the poison answers, the reads of `Tcr` otherwise. -/
noncomputable def updP : Caller → HashDomain → Mem → Option HashOutput → Mem
  | .setup => uRed
  | .answer => uAnsP C G
  | .judge => uJudge
  | .red => uRed

/-- **A charged cell**: a `G`-cell that is no record. -/
def Chg (m : Mem) (z : HashDomain) : Prop :=
  IsG C G z ∧ m.recs z = none

open scoped Classical in
/-- **The charge of a read** of `z` with the policy `u`: one at a charged cell by another policy
than the answers'. -/
noncomputable def chgR (m : Mem) (z : HashDomain) (u : Mem → Option HashOutput → Mem) : ℕ :=
  if Chg C G m z ∧ u ≠ uAnsP C G z then 1 else 0

/-- The memory with the number of charged reads. -/
abbrev MemK :=
  Mem × ℕ

/-- **The policies with the count**: each read adds its charge. -/
noncomputable def updK (c : Caller) (z : HashDomain) (mk : MemK) (o : Option HashOutput) : MemK :=
  (updP C G c z mk.1 o, mk.2 + chgR C G mk.1 z (updP C G c z))

/-- The log of a memory with its count. -/
def rlK (mk : MemK) : HashDomain → Option HashOutput :=
  rl mk.1

/-- The count of a mode (`0` when dead). -/
def cnt (μ : Option MemK) : ℕ :=
  μ.elim 0 Prod.snd

/-- **The registers before the reduction's own reads and the adversary**: the memory `m`, no
hardwired cell, an empty slot, and no `G`-cell outside the records in the database. -/
def PhA (m : Mem) (s : RomReg HashDomain HashOutput Mem) : Prop :=
  s.2.2 = m ∧ s.2.1 = hwEmpty HashOutput HashDomain ∧ m.slot = none ∧
    ∀ x, IsG C G x → m.recs x = none → s.1.1 x = none

open scoped Classical in
/-- **The weight of a reduction's own reads of `G`-cells**: one each; coins and challenger
queries nothing. -/
noncomputable def gWR {Q' : Type} {R' : OracleSpec.{0, 0} Q'} :
    (romWorld.Oracles + R').Domain → ℕ
  | .inl (.inl _) => 0
  | .inl (.inr z) => if IsG C G z then 1 else 0
  | .inr _ => 0

variable {C G}

open scoped Classical in
theorem uAnsP_recs (z : HashDomain) (m : Mem) (o : Option HashOutput) :
    (uAnsP C G z m o).recs = if IsG C G z ∧ m.recs z = none then
      Function.update m.recs z (some (o.getD 0)) else m.recs :=
  rfl

theorem recordsAt_updP (c : Caller) (z : HashDomain) : RecordsAt rl z (updP C G c z) := by
  intro m o
  cases c <;> rfl

/-- **The answers' policy is the answers' only**: the other policies mark the cell read. -/
theorem updP_eq_uAnsP_iff (c : Caller) (z : HashDomain) :
    updP C G c z = uAnsP C G z ↔ c = .answer := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  let m₀ : Mem := (∅, fun _ ↦ none, fun _ ↦ false, fun _ ↦ none, none)
  have h' := congrArg (fun m : Mem ↦ m.seen z) (congrFun (congrFun h m₀) none)
  cases c
  · change Function.update (fun _ ↦ false) z true z = false at h'
    simp at h'
  · rfl
  · change Function.update (fun _ ↦ false) z true z = false at h'
    simp at h'
  · change Function.update (fun _ ↦ false) z true z = false at h'
    simp at h'

theorem updP_ne_uAnsP {c : Caller} (hc : c ≠ .answer) (z : HashDomain) :
    updP C G c z ≠ uAnsP C G z :=
  fun h ↦ hc ((updP_eq_uAnsP_iff c z).1 h)

/-- The policies other than the answers' keep the records. -/
theorem keepsRecs_updP {c : Caller} (hc : c ≠ .answer) (z : HashDomain) :
    KeepsRecs z (updP C G c z) := by
  cases c
  · exact keepsRecs_uRed z
  · exact absurd rfl hc
  · exact keepsRecs_uJudge z
  · exact keepsRecs_uRed z

theorem chgR_uAnsP (m : Mem) (z : HashDomain) : chgR C G m z (uAnsP C G z) = 0 := by
  unfold chgR
  rw [ite_eq_right fun h ↦ h.2 rfl]

open scoped Classical in
theorem chgR_le (m : Mem) (z : HashDomain) (u : Mem → Option HashOutput → Mem) :
    chgR C G m z u ≤ if IsG C G z then 1 else 0 := by
  unfold chgR
  by_cases h : Chg C G m z ∧ u ≠ uAnsP C G z
  · rw [ite_eq_left h, ite_eq_left h.1.1]
  · rw [ite_eq_right h]
    exact Nat.zero_le _

theorem chgR_le_one (m : Mem) (z : HashDomain) (u : Mem → Option HashOutput → Mem) :
    chgR C G m z u ≤ 1 := by
  unfold chgR
  split_ifs <;> omega

/-- A cell that is no charged cell has an empty target. -/
theorem tgt_eq_empty_of_not_chg {m : Mem} {z : HashDomain} (h : ¬ Chg C G m z)
    (W : Hw HashOutput HashDomain) : tgt C G W m z = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun y hy ↦ h ?_
  obtain ⟨x, v, -, hne, hxz, hu, -⟩ := hy
  refine ⟨hxz.isG_right, ?_⟩
  by_contra hz
  exact hne (hu z (Option.isSome_iff_ne_none.2 hz) hxz.isG_right.sameCls_self).symm

/-- **A read keeping the records at a cell that is not charged is invisible** to the event. -/
theorem badR_iff_of_read {z : HashDomain} {u : Mem → Option HashOutput → Mem}
    {s s' : RomReg HashDomain HashOutput Mem} {o : Option HashOutput}
    (hk : KeepsRecsAt z u s.2.2) (hz : ¬ Chg C G s.2.2 z)
    (hc : ∀ b, b ≠ z → s'.1.1 b = s.1.1 b) (hW : s'.2.1 = s.2.1) (hm : s'.2.2 = u s.2.2 o) :
    s' ∈ BadR C G ↔ s ∈ BadR C G := by
  have ht : tgt C G s'.2.1 s'.2.2 = tgt C G s.2.1 s.2.2 := by
    rw [hm]
    exact tgt_congr (hk o).1 _ _
  have hz' : ∀ W y, y ∉ tgt C G W s.2.2 z := fun W y hy ↦ by
    rw [tgt_eq_empty_of_not_chg hz] at hy
    exact hy
  have hx : ∀ x, x ≠ z → unionH s' x = unionH s x := fun x hx ↦ by
    simp only [unionH_apply, hW, hc x hx]
  constructor
  · rintro (⟨x, y, hxy, hy⟩ | ⟨z', y, hs, hy⟩)
    · rw [ht] at hy
      have hxz : x ≠ z := by
        rintro rfl
        exact hz' _ y hy
      exact Or.inl ⟨x, y, by rw [← hx x hxz]; exact hxy, hy⟩
    · rw [ht] at hy
      rw [hm] at hs
      rcases (hk o).2 with h | ⟨-, h⟩
      · exact Or.inr ⟨z', y, h.symm.trans hs, hy⟩
      · rw [h] at hs
        rcases o with _ | y'
        · cases hs
        · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          exact absurd hy (hz' _ _)
  · rintro (⟨x, y, hxy, hy⟩ | ⟨z', y, hs, hy⟩)
    · have hxz : x ≠ z := by
        rintro rfl
        exact hz' _ y hy
      exact Or.inl ⟨x, y, by rw [hx x hxz]; exact hxy, by rw [ht]; exact hy⟩
    · refine Or.inr ⟨z', y, ?_, by rw [ht]; exact hy⟩
      rw [hm]
      rcases (hk o).2 with h | ⟨h, -⟩
      · exact h.trans hs
      · rw [h] at hs
        cases hs

/-- **The registers before the reduction's own reads are outside the event.** -/
theorem not_mem_badR_of_phA {m : Mem} {s : RomReg HashDomain HashOutput Mem} (h : PhA C G m s) :
    s ∉ BadR C G := by
  obtain ⟨rfl, hW, hsl, hD⟩ := h
  rintro (⟨x, y, hxy, hy⟩ | ⟨z, y, hs, -⟩)
  · obtain ⟨x₀, v, -, hne, hc, hu, -⟩ := hy
    have hx : s.2.2.recs x = none := by
      by_contra hx
      exact hne (hu x (Option.isSome_iff_ne_none.2 hx) hc.isG_right.sameCls_self).symm
    have h1 : s.1.1 x = some y := by
      simpa [hW, hwEmpty_fst_apply] using hxy
    rw [hD x hc.isG_right hx] at h1
    cases h1
  · change s.2.2.slot = some (z, y) at hs
    rw [hsl] at hs
    cases hs

/-- **An answer read keeps the registers before the reduction's own reads.** -/
theorem phA_uAnsP {m : Mem} {s s' : RomReg HashDomain HashOutput Mem} {z : HashDomain}
    {o : Option HashOutput} (h : PhA C G m s) (hc : ∀ b, b ≠ z → s'.1.1 b = s.1.1 b)
    (hW : s'.2.1 = s.2.1) (hm : s'.2.2 = uAnsP C G z m o) : PhA C G (uAnsP C G z m o) s' := by
  obtain ⟨-, hW', hsl, hD⟩ := h
  refine ⟨hm, hW.trans hW', hsl, fun x hx hr ↦ ?_⟩
  rw [uAnsP_recs] at hr
  by_cases hxz : x = z
  · subst hxz
    split_ifs at hr with hcnd
    · rw [Function.update_self] at hr
      cases hr
    · exact absurd ⟨hx, hr⟩ hcnd
  · rw [hc x hxz]
    refine hD x hx ?_
    split_ifs at hr
    · rwa [Function.update_of_ne hxz] at hr
    · exact hr

end policy

/-! ## Live runs with the count -/

section live

open OracleComp OracleSpec

variable {Par Tw Fn Out : Type} {Msg : Fn → Type} {C : TwColl Par Tw Fn Msg Out}
  {G : Fn → Tw → Prop}

/-- A step with the count moves the memory as the step without. -/
theorem stepRd_updK (c : Caller) (z : HashDomain) (μ : Option MemK) (v : HashOutput) :
    (stepRd rlK (updK C G c z) z μ v).map Prod.fst =
      stepRd rl (updP C G c z) z (μ.map Prod.fst) v := by
  rcases μ with _ | ⟨m, k⟩
  · rfl
  · simp only [stepRd, Option.map_some]
    split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1 h2 | exact absurd h2 h1

/-- **A live run with the count is a live run of the memory.** -/
theorem liveRun_mapK (c : Caller) {α : Type} (oa : OracleComp romWorld.Oracles α)
    {μ : Option MemK} {a : α} {μ' : Option MemK} (h : LiveRun rlK (updK C G c) oa μ a μ') :
    LiveRun rl (updP C G c) oa (μ.map Prod.fst) a (μ'.map Prod.fst) := by
  induction oa using OracleComp.inductionOn generalizing μ with
  | pure x =>
    obtain ⟨rfl, rfl⟩ := liveRun_pure_inv h
    unfold LiveRun
    simp
  | query_bind t k ih =>
    obtain ⟨y, μ₁, h₁, h₂⟩ := liveRun_query_bind h
    unfold LiveRun
    rw [run_simulateQ_query_bind, mem_support_bind_iff]
    refine ⟨(y, μ₁.map Prod.fst), ?_, ih y h₂⟩
    rcases t with n | x
    · change (y, μ₁) ∈ support ((fun b ↦ (b, μ)) <$>
        liftM (romWorld.Oracles.query (.inl n))) at h₁
      rw [support_map] at h₁
      obtain ⟨_, _, he⟩ := h₁
      rw [← (Prod.mk.inj he).2]
      exact mem_support_liveImpl (updP C G) rl c (.inl n) _ y
    · rw [eq_stepRd_of_mem_support h₁]
      exact (congrArg (fun ν ↦ (y, ν) ∈ support ((liveImpl rl (updP C G c) (.inr x)).run
        (μ.map Prod.fst))) (stepRd_updK c x μ y)).mpr
        (mem_support_liveImpl (updP C G) rl c (.inr x) _ y)

/-- A live run's value through a bind. -/
theorem liveRun_bindK {u : HashDomain → MemK → Option HashOutput → MemK} {α β : Type}
    {oa : OracleComp romWorld.Oracles α} {ob : α → OracleComp romWorld.Oracles β} {b : β}
    {μ μ'' : Option MemK} (h : LiveRun rlK u (oa >>= ob) μ b μ'') :
    ∃ a μ', LiveRun rlK u oa μ a μ' ∧ LiveRun rlK u (ob a) μ' b μ'' := by
  unfold LiveRun at h
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at h
  obtain ⟨⟨a, μ'⟩, h1, h2⟩ := h
  exact ⟨a, μ', h1, h2⟩

/-- A live run of a read of `x` with the count: the mode moves by `stepRd`. -/
theorem liveRun_queryK {u : HashDomain → MemK → Option HashOutput → MemK} {x : romWorld.Prim}
    {w : romWorld.Oracles.Range (.inr x)} {μ μ' : Option MemK}
    (h : LiveRun rlK u (liftM (romWorld.Oracles.query (.inr x)) :
      OracleComp romWorld.Oracles (romWorld.Oracles.Range (.inr x))) μ w μ') :
    μ' = stepRd rlK (u x) x μ w := by
  unfold LiveRun at h
  rw [← bind_pure (liftM (romWorld.Oracles.query (.inr x)) :
    OracleComp romWorld.Oracles (romWorld.Oracles.Range (.inr x))), run_simulateQ_query_bind,
    mem_support_bind_iff] at h
  obtain ⟨⟨w', μ₂⟩, h3, h4⟩ := h
  have h5 : (w, μ') = (w', μ₂) := by simpa using h4
  simp only [Prod.mk.injEq] at h5
  obtain ⟨rfl, rfl⟩ := h5
  simp only [liveImpl, StateT.run, support_map, Set.mem_image, Prod.mk.injEq] at h3
  obtain ⟨v, -, rfl, rfl⟩ := h3
  rfl

/-- A live run of a hash of an encoded input with the count: one read of its cell. -/
theorem liveRun_hashQK {u : HashDomain → MemK → Option HashOutput → MemK} {β : Type}
    (f : HashOutput → β) {l : HashInput} {x : HashDomain} (hx : encodeInput l = some x) {b : β}
    {μ μ' : Option MemK} (h : LiveRun rlK u (f <$> hashQ l) μ b μ') :
    ∃ v, b = f v ∧ μ' = stepRd rlK (u x) x μ v := by
  rw [hashQ_of_encodeInput_eq_some hx] at h
  change LiveRun rlK u (f <$> (liftM (romWorld.Oracles.query (.inr x)) :
    OracleComp romWorld.Oracles HashOutput)) μ b μ' at h
  rw [map_eq_bind_pure_comp] at h
  obtain ⟨w, μ1, h1, h2⟩ := liveRun_bindK h
  obtain ⟨hb, hμ⟩ := liveRun_pure_inv h2
  rw [hμ]
  exact ⟨w, hb, liveRun_queryK h1⟩

/-- The count after a step is the count before plus the read's charge. -/
theorem cnt_stepRd_le (c : Caller) (z : HashDomain) (μ : Option MemK) (v : HashOutput) :
    cnt (stepRd rlK (updK C G c z) z μ v) ≤
      cnt μ + μ.elim 0 fun mk ↦ chgR C G mk.1 z (updP C G c z) := by
  rcases μ with _ | ⟨m, k⟩
  · exact Nat.zero_le _
  rcases h : stepRd rlK (updK C G c z) z (some (m, k)) v with _ | mk'
  · exact Nat.zero_le _
  obtain ⟨rfl, -⟩ := stepRd_some h
  exact le_rfl

/-- **The answers keep the count** along their live runs. -/
theorem cnt_liveRun_answer {α : Type} (oa : OracleComp romWorld.Oracles α) {μ : Option MemK}
    {a : α} {μ' : Option MemK} (h : LiveRun rlK (updK C G .answer) oa μ a μ') :
    cnt μ' ≤ cnt μ :=
  liveRun_inv_all (fun ν ↦ cnt ν ≤ cnt μ) (fun z ν v hν ↦ by
    refine (cnt_stepRd_le .answer z ν v).trans ?_
    rcases ν with _ | ⟨m, k⟩
    · exact hν
    · change k + chgR C G m z (uAnsP C G z) ≤ cnt μ
      rw [chgR_uAnsP, Nat.add_zero]
      exact hν) oa h le_rfl

/-- **The judge's live run adds at most one charged read.** -/
theorem cnt_liveRun_judge {EFn EOut : Type} {EMsg : EFn → Type} [SampleableType Par]
    {D : TwColl Par Tw EFn EMsg EOut} (hlen : C.LengthLe maxLen) {P : Par}
    {log : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)} (out : Σ l, Tw × Msg l)
    {μ μ' : Option MemK} {b : Bool}
    (h : LiveRun rlK (updK C G .judge) ((smTcrIn romWorld C D G).judge P log out) μ b μ') :
    cnt μ' ≤ cnt μ + 1 := by
  obtain ⟨b₁, μ₁, h1, h2⟩ := liveRun_bindK h
  obtain ⟨-, hμ₁⟩ := liveRun_pure_inv h2
  obtain ⟨y, μ₂, h3, h4⟩ := liveRun_bindK h1
  obtain ⟨-, hμ₂⟩ := liveRun_pure_inv h4
  have hz := encodeInput_tcell hlen P out
  change LiveRun rlK (updK C G .judge) (C.trunc <$> hashQ (C.layout out.1 P out.2.1 out.2.2)) μ y
    μ₂ at h3
  obtain ⟨v, -, hμv⟩ := liveRun_hashQK C.trunc hz h3
  rw [hμ₁, hμ₂, hμv]
  refine (cnt_stepRd_le .judge _ μ v).trans (Nat.add_le_add_left ?_ _)
  rcases μ with _ | ⟨m, k⟩
  · exact Nat.zero_le _
  · exact chgR_le_one _ _ _

open Common in
/-- **The count along a reduction's live run** grows by at most its own reads of `G`-cells: the
answers keep it. -/
theorem cnt_liveRedRun {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q')) {α : Type}
    (oa : OracleComp (romWorld.Oracles + R') α) {c : ℕ}
    (h : QueryCostAtMost oa (gWR C G (R' := R')) c) {log : QueryLog R'} {μ : Option MemK}
    {a : α × QueryLog R'} {μ' : Option MemK} (hrun : LiveRedRun rlK (updK C G) ans oa log μ a μ') :
    cnt μ' ≤ cnt μ + c := by
  induction oa using OracleComp.inductionOn generalizing log μ c with
  | pure x =>
    unfold LiveRedRun at hrun
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hrun
    rw [hrun.2.2]
    exact Nat.le_add_right _ _
  | query_bind t k ih =>
    rw [QueryCostAtMost, isQueryBound_query_bind_iff] at h
    unfold LiveRedRun at hrun
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hrun
    obtain ⟨⟨y, log₁, μ₁⟩, h₁, h₂⟩ := hrun
    have hk := ih y (h.2 y) h₂
    have hw : gWR C G (R' := R') t ≤ c := h.1
    have hstep : cnt μ₁ ≤ cnt μ + gWR C G (R' := R') t := by
      rcases t with (n | z) | q'
      · change (y, log₁, μ₁) ∈ support ((fun p ↦ (p.1, (log, p.2))) <$>
          (liveImpl rlK (updK C G .red) (.inl n)).run μ) at h₁
        rw [support_map] at h₁
        obtain ⟨⟨y', μ₂⟩, h₃, he⟩ := h₁
        change (y', μ₂) ∈ support ((fun b ↦ (b, μ)) <$>
          liftM (romWorld.Oracles.query (.inl n))) at h₃
        rw [support_map] at h₃
        obtain ⟨_, _, he'⟩ := h₃
        simp only [Prod.mk.injEq] at he
        obtain ⟨-, rfl, rfl⟩ := he
        rw [← (Prod.mk.inj he').2]
        exact Nat.le_add_right _ _
      · change (y, log₁, μ₁) ∈ support ((fun p ↦ (p.1, (log, p.2))) <$>
          (liveImpl rlK (updK C G .red) (.inr z)).run μ) at h₁
        rw [support_map] at h₁
        obtain ⟨⟨y', μ₂⟩, h₃, he⟩ := h₁
        simp only [Prod.mk.injEq] at he
        obtain ⟨-, rfl, rfl⟩ := he
        rw [eq_stepRd_of_mem_support h₃]
        refine (cnt_stepRd_le .red z μ y').trans (Nat.add_le_add_left ?_ _)
        rcases μ with _ | ⟨m, k⟩
        · exact Nat.zero_le _
        · exact chgR_le m z _
      · change (y, log₁, μ₁) ∈ support ((fun p ↦ (p.1, (log ++ [⟨q', p.1⟩], p.2))) <$>
          (simulateQ (liveImpl rlK (updK C G .answer)) (ans q')).run μ) at h₁
        rw [support_map] at h₁
        obtain ⟨⟨y', μ₂⟩, h₃, he⟩ := h₁
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        exact (cnt_liveRun_answer (ans q') h₃).trans (Nat.le_add_right _ _)
    omega

end live

/-! ## The invariant of the records under the poison answers -/

section win

open OracleComp OracleSpec TcrQuery

variable {Par Tw Fn Out EFn EOut : Type} {Msg : Fn → Type} {EMsg : EFn → Type}
  {C : TwColl Par Tw Fn Msg Out} {D : TwColl Par Tw EFn EMsg EOut} {G : Fn → Tw → Prop}

theorem uAnsP_recs_of_some {x y : HashDomain} {m : Mem} {o : Option HashOutput} {w : HashOutput}
    (h : m.recs y = some w) : (uAnsP C G x m o).recs y = some w := by
  rw [uAnsP_recs]
  split_ifs with hc
  · rw [Function.update_of_ne]
    · exact h
    · rintro rfl
      rw [hc.2] at h
      cases h
  · exact h

/-- A new record of an answer read is at its cell. -/
theorem uAnsP_recs_new {x y : HashDomain} {m : Mem} {o : Option HashOutput} {w : HashOutput}
    (h : (uAnsP C G x m o).recs y = some w) : m.recs y = some w ∨ y = x := by
  rw [uAnsP_recs] at h
  split_ifs at h with hc
  · by_cases hy : y = x
    · exact Or.inr hy
    · rw [Function.update_of_ne hy] at h
      exact Or.inl h
  · exact Or.inl h

/-- **An answer read keeps the invariant** for an entry reading its cell `x` whose class is
recorded, or a non-target entry. -/
theorem recInv_uAnsP {P : Par} {log : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)}
    {m : Mem} {x : HashDomain} {o : Option HashOutput}
    {e : (q : TcrQuery Tw Fn Msg EFn EMsg) × Resp Par Out EOut q}
    (hI : RecInv C D G P log m) (he : entCell C D P e = some x)
    (h3 : TVal (log ++ [e]) → ∀ e' ∈ (asTarget e).toList, G e'.1.1 e'.1.2.1 →
      ∃ v, (uAnsP C G x m o).recs (tcell C P e'.1) = some v ∧ e'.2 = C.trunc v) :
    RecInv C D G P (log ++ [e]) (uAnsP C G x m o) := by
  obtain ⟨h0, h2, h4⟩ := hI
  refine ⟨h0, fun y v hv ↦ ?_, fun hv e' he' hG ↦ ?_⟩
  · rcases uAnsP_recs_new hv with h | rfl
    · obtain ⟨e'', he'', hc⟩ := h2 y _ h
      exact ⟨e'', List.mem_append_left _ he'', hc⟩
    · exact ⟨e, List.mem_append_right _ (List.mem_singleton_self _), he⟩
  · rw [tcrTargets_append] at he'
    rcases List.mem_append.1 he' with he' | he'
    · obtain ⟨v, hv', hd⟩ := h4 (tVal_of_append hv) e' he' hG
      exact ⟨v, uAnsP_recs_of_some hv', hd⟩
    · exact h3 hv e' he' hG

/-- **The challenger's poison answers keep the invariant.** -/
theorem liveInv_answerP [SampleableType Par] (hs : GSep C G) (htw : D.TweakSeparated C)
    (hlen : C.LengthLe maxLen) {P : Par}
    {log : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)} {μ μ' : Option Mem}
    (q' : TcrQuery Tw Fn Msg EFn EMsg) {a : Resp Par Out EOut q'}
    (hI : LiveInv C D G P log μ)
    (h : LiveRun rl (updP C G .answer) ((smTcrIn romWorld C D G).answer P q') μ a μ') :
    LiveInv C D G P (log ++ [⟨q', a⟩]) μ' := by
  rcases q' with ⟨l, t, mm⟩ | ⟨l, t, mm⟩ | _
  · have hx := encodeInput_tcell hlen P ⟨l, t, mm⟩
    change LiveRun rl (updP C G .answer) (C.trunc <$> hashQ (C.layout l P t mm)) μ a μ' at h
    obtain ⟨v, rfl, rfl⟩ := liveRun_hashQ C.trunc hx h
    refine liveInv_stepRd hI fun m hm ↦ recInv_uAnsP hm hx fun hv e' he' hG ↦ ?_
    simp only [asTarget, Option.toList_some, List.mem_singleton] at he'
    subst he'
    have hrl := recordless_target hs htw hm hx hG hv
    have hxG : IsG C G (tcell C P ⟨l, t, mm⟩) := ⟨P, t, l, mm, hG, hx⟩
    refine ⟨v, ?_, rfl⟩
    change (uAnsP C G (tcell C P ⟨l, t, mm⟩) m (some v)).recs (tcell C P ⟨l, t, mm⟩) = some v
    rw [uAnsP_recs, ite_eq_left ⟨hxG, hrl _ hxG.sameCls_self⟩, Function.update_self]
    rfl
  · change LiveRun rl (updP C G .answer) (D.trunc <$> hashQ (D.layout l P t mm)) μ a μ' at h
    rcases hx : encodeInput (D.layout l P t mm) with _ | x
    · have h0 : hashQ (D.layout l P t mm) = pure 0 := by simp [hashQ, hx]
      rw [h0] at h
      change LiveRun rl (updP C G .answer) (pure (D.trunc 0)) μ a μ' at h
      obtain ⟨-, rfl⟩ := liveRun_pure h
      exact fun m hm ↦ recInv_append_nonTarget (hI m hm) rfl
    · obtain ⟨v, rfl, rfl⟩ := liveRun_hashQ D.trunc hx h
      refine liveInv_stepRd hI fun m hm ↦ recInv_uAnsP hm hx fun _ e' he' ↦ ?_
      simp [asTarget] at he'
  · change LiveRun rl (updP C G .answer) (pure P) μ a μ' at h
    obtain ⟨-, rfl⟩ := liveRun_pure h
    exact fun m hm ↦ recInv_append_nonTarget (hI m hm) rfl

/-- The zero weight bounds every computation by `0`. -/
theorem queryCostAtMost_zero {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (oa : OracleComp spec α) : Common.QueryCostAtMost oa (fun _ ↦ 0) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact Common.isWeightBound_pure _ _ _
  | query_bind t k ih => exact (Common.isWeightBound_query_bind_iff _ _ _ _).mpr ⟨le_rfl, ih⟩

/-- **The reduction's live runs with the count keep the invariant of the records.** -/
theorem liveInv_liveRedRunK [SampleableType Par] (hs : GSep C G) (htw : D.TweakSeparated C)
    (hlen : C.LengthLe maxLen) {P : Par} {α : Type}
    (oa : OracleComp (romWorld.Oracles + TcrSpec Par Tw Fn Msg Out EFn EMsg EOut) α)
    {log : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)} {μ : Option MemK}
    {a : α × QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)} {μ' : Option MemK}
    (hrun : LiveRedRun rlK (updK C G) ((smTcrIn romWorld C D G).answer P) oa log μ a μ')
    (hI : LiveInv C D G P log (μ.map Prod.fst)) : LiveInv C D G P a.2 (μ'.map Prod.fst) :=
  liveRedRun_inv_cost (updK C G) rlK _ (fun _ ↦ 0)
    (fun log μ ↦ LiveInv C D G P log (μ.map Prod.fst))
    (fun z _ μ v _ hΦ ↦ (congrArg (LiveInv C D G P _) (stepRd_updK .red z μ v)).mpr
      (liveInv_stepRd hΦ fun _ hm ↦ hm))
    (fun q' _ _ _ _ _ hΦ h ↦ liveInv_answerP hs htw hlen q' hΦ (liveRun_mapK .answer _ h))
    oa (queryCostAtMost_zero oa) hrun hI

end win

/-! ## The modes of the read program -/

section modes

variable {Par Tw Fn Out : Type} {Msg : Fn → Type} (C : TwColl Par Tw Fn Msg Out)
  (G : Fn → Tw → Prop)

/-- **The modes of the read program**: the memory with the count of charged reads, and the
phase (`some false` before the reduction's own reads and the adversary). -/
abbrev RMode :=
  Option MemK × Option Bool

/-- The memory of a mode. -/
def projR (μ : RMode) : Option Mem :=
  μ.1.map Prod.fst

/-- **The memory and the count after a call**: a sponge call keeps them, a read moves the memory
by `stepRd` and adds its charge. -/
noncomputable def nxK : Option MemK → (i : (hwSpec HashOutput HashDomain Mem).Port) →
    (hwSpec HashOutput HashDomain Mem).Result i → Option MemK
  | none, _, _ => none
  | some ν, .inl (.inl _), _ => some ν
  | some ν, .inl (.inr (.readH z u)), r =>
    (r.1.elim none (stepRd rl u z (some ν.1))).map fun m' ↦ (m', ν.2 + chgR C G ν.1 z u)
  | some _, _, _ => none

open scoped Classical in
/-- **The phase after a call**: a sponge call, or a read by another policy than the answers',
ends the first phase. -/
noncomputable def nxC2 : Option Bool → (i : (hwSpec HashOutput HashDomain Mem).Port) →
    (hwSpec HashOutput HashDomain Mem).Result i → Option Bool
  | none, _, _ => none
  | some _, .inl (.inl _), _ => some true
  | some b, .inl (.inr (.readH z u)), _ =>
    some (@ite _ (u = uAnsP C G z) (Classical.propDecidable _) b true)
  | some b, _, _ => some b

/-- **The calls a phase allows**: sponge calls, and reads of the policies, the answers' in the
first phase only. -/
def okC2 : Option Bool → (hwSpec HashOutput HashDomain Mem).Port → Prop
  | none, _ => True
  | some _, .inl (.inl _) => True
  | some b, .inl (.inr (.readH z u)) => ∃ c, u = updP C G c z ∧ (c = .answer → b = false)
  | some _, _ => False

/-- The calls a mode allows. -/
def okR (μ : RMode) (i : (hwSpec HashOutput HashDomain Mem).Port) : Prop :=
  OkD rl (projR μ) i ∧ (μ.1 = none ∨ okC2 C G μ.2 i)

/-- The mode after a call. -/
noncomputable def nxR (μ : RMode) (i : (hwSpec HashOutput HashDomain Mem).Port)
    (r : (hwSpec HashOutput HashDomain Mem).Result i) : RMode :=
  (nxK C G μ.1 i r, nxC2 C G μ.2 i r)

variable (n : ℕ)

/-- **Doomed modes**: a dead memory, no phase, or more than `n` charged reads. -/
def DoomR (μ : RMode) : Prop :=
  μ.1.elim True fun mk ↦ μ.2 = none ∨ n < mk.2

/-- **The budget of a mode**: the charged reads left. -/
def budR (μ : RMode) : ℕ :=
  μ.1.elim 0 fun mk ↦ n - mk.2

/-- The adversary's calls. -/
def κA (i : (hwSpec HashOutput HashDomain Mem).Port) : ℕ :=
  if hwCls i then 0 else 1

/-- **The charged reads.** -/
noncomputable def κB : RMode → (hwSpec HashOutput HashDomain Mem).Port → ℕ
  | (some ν, _), .inl (.inr (.readH z u)) => chgR C G ν.1 z u
  | _, _ => 0

/-- **The invariant of the first phase.** -/
def CInvR (μ : RMode) : Set (RomReg HashDomain HashOutput Mem) :=
  {s | ∀ mk, μ.1 = some mk → μ.2 = some false → PhA C G mk.1 s}

/-- **The leaves**: a live memory has a phase, at most `n` charged reads and, on `true`, the
judge's read in its target. -/
def FinR (p : Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) (μ : RMode) : Prop :=
  ∀ mk, μ.1 = some mk → μ.2 ≠ none ∧ mk.2 ≤ n ∧ (p.2.2 = true → mk.1 ∈ Won C G)

variable {C G n}

theorem nxK_readH (m : Mem) (k : ℕ) (z : HashDomain) (u : Mem → Option HashOutput → Mem)
    (r : (hwSpec HashOutput HashDomain Mem).Result (.inl (.inr (.readH z u)))) :
    nxK C G (some (m, k)) (.inl (.inr (.readH z u))) r =
      (r.1.elim none (stepRd rl u z (some m))).map fun m' ↦ (m', k + chgR C G m z u) :=
  rfl

theorem projR_nxR {μ : RMode} {i : (hwSpec HashOutput HashDomain Mem).Port}
    (r : (hwSpec HashOutput HashDomain Mem).Result i) (hi : okR C G μ i) :
    projR (nxR C G μ i r) = nxD rl (projR μ) i r := by
  rcases μ with ⟨_ | ⟨m, k⟩, β⟩
  · rfl
  rcases i with (p | c) | c
  · rfl
  · cases c with
    | readH z u =>
      change (nxK C G (some (m, k)) (.inl (.inr (.readH z u))) r).map Prod.fst =
        r.1.elim none (stepRd rl u z (some m))
      rw [nxK_readH]
      generalize r.1.elim none (stepRd rl u z (some m)) = o
      cases o <;> rfl
    | readK _ _ => exact hi.1.elim
    | readK' _ _ => exact hi.1.elim
  · exact hi.1.elim

theorem doom_nxR {μ : RMode} {i : (hwSpec HashOutput HashDomain Mem).Port}
    (r : (hwSpec HashOutput HashDomain Mem).Result i) (hd : DoomR n μ) :
    DoomR n (nxR C G μ i r) := by
  rcases μ with ⟨_ | ⟨m, k⟩, β⟩
  · trivial
  change β = none ∨ n < k at hd
  have hβ : β = none → nxC2 C G β i r = none := by
    rintro rfl
    rfl
  rcases i with (p | c) | c
  · show nxC2 C G β _ r = none ∨ n < k
    rcases hd with h | h
    · exact Or.inl (hβ h)
    · exact Or.inr h
  · cases c with
    | readH z u =>
      show (nxK C G (some (m, k)) (.inl (.inr (.readH z u))) r).elim True
        (fun mk ↦ nxC2 C G β _ r = none ∨ n < mk.2)
      rw [nxK_readH]
      generalize r.1.elim none (stepRd rl u z (some m)) = o
      rcases o with _ | m'
      · trivial
      · show nxC2 C G β _ r = none ∨ n < k + chgR C G m z u
        rcases hd with h | h
        · exact Or.inl (hβ h)
        · exact Or.inr (by omega)
    | readK _ _ => trivial
    | readK' _ _ => trivial
  · trivial

theorem bud_nxR {μ : RMode} {i : (hwSpec HashOutput HashDomain Mem).Port}
    (r : (hwSpec HashOutput HashDomain Mem).Result i) (hi : okR C G μ i)
    (hd : ¬ DoomR n (nxR C G μ i r)) : κB C G μ i + budR n (nxR C G μ i r) ≤ budR n μ := by
  rcases μ with ⟨_ | ⟨m, k⟩, β⟩
  · exact absurd trivial hd
  rcases i with (p | c) | c
  · show 0 + (n - k) ≤ n - k
    omega
  · cases c with
    | readH z u =>
      have hd' : ¬ (nxK C G (some (m, k)) (.inl (.inr (.readH z u))) r).elim True
          (fun mk ↦ nxC2 C G β _ r = none ∨ n < mk.2) := hd
      show chgR C G m z u + (nxK C G (some (m, k)) (.inl (.inr (.readH z u))) r).elim 0
        (fun mk ↦ n - mk.2) ≤ n - k
      rw [nxK_readH] at hd' ⊢
      generalize r.1.elim none (stepRd rl u z (some m)) = o at hd' ⊢
      rcases o with _ | m'
      · exact absurd trivial hd'
      · have h : ¬ n < k + chgR C G m z u := fun h ↦ hd' (Or.inr h)
        show chgR C G m z u + (n - (k + chgR C G m z u)) ≤ n - k
        omega
    | readK _ _ => exact hi.1.elim
    | readK' _ _ => exact hi.1.elim
  · exact hi.1.elim

open scoped Classical in
/-- **The first phase's invariant is kept** by every allowed call. -/
theorem cInvR_step (m₀ : Mem) {μ : RMode} {i : (hwSpec HashOutput HashDomain Mem).Port}
    (r : (hwSpec HashOutput HashDomain Mem).Result i) (hi : okR C G μ i)
    {σ : Matrix ((hwSpec HashOutput HashDomain Mem).In i × HwReg HashOutput HashDomain Mem)
      ((hwSpec HashOutput HashDomain Mem).In i × HwReg HashOutput HashDomain Mem) ℂ}
    (hσ : QuerySupportedOn (fun m : (hwSpec HashOutput HashDomain Mem).In i ×
      HwReg HashOutput HashDomain Mem ↦ m.2) (CInvR C G μ) σ) :
    QuerySupportedOn (fun m : (hwSpec HashOutput HashDomain Mem).Out i ×
      HwReg HashOutput HashDomain Mem ↦ m.2) (CInvR C G (nxR C G μ i r))
      (((runtime2 HashOutput HashDomain m₀).step i).branch r σ) := by
  have hall : (∀ s, s ∈ CInvR C G (nxR C G μ i r)) →
      QuerySupportedOn (fun m : (hwSpec HashOutput HashDomain Mem).Out i ×
        HwReg HashOutput HashDomain Mem ↦ m.2) (CInvR C G (nxR C G μ i r))
        (((runtime2 HashOutput HashDomain m₀).step i).branch r σ) :=
    fun h a b _ ↦ ⟨h _, h _⟩
  rcases μ with ⟨_ | ⟨m, k⟩, β⟩
  · exact hall fun s mk hmk _ ↦ by cases hmk
  rcases i with (p | c) | c
  · refine hall fun s mk _ hph ↦ ?_
    change nxC2 C G β _ r = some false at hph
    rcases β with _ | b <;> cases hph
  · cases c with
    | readH z u =>
      rw [runtime2_branch]
      refine QuerySupportedOn.conj hσ fun q' q hK hq mk' hmk' hph ↦ ?_
      obtain ⟨hcz, -, hW, hmem⟩ := hwReadKraus_readH_ne_zero z _ r hK
      change nxC2 C G β _ r = some false at hph
      obtain ⟨rfl, hu⟩ : β = some false ∧ u = uAnsP C G z := by
        rcases β with _ | b
        · cases hph
        · change some (@ite _ (u = uAnsP C G z) (Classical.propDecidable _) b true) =
            some false at hph
          by_cases hu : u = uAnsP C G z
          · rw [ite_eq_left hu] at hph
            cases hph
            exact ⟨rfl, hu⟩
          · rw [ite_eq_right hu] at hph
            cases hph
      subst hu
      change nxK C G (some (m, k)) (.inl (.inr (.readH z (uAnsP C G z)))) r = some mk' at hmk'
      rw [nxK_readH] at hmk'
      rcases hr : r.1 with _ | v
      · rw [hr] at hmk'
        cases hmk'
      rw [hr] at hmk' hmem
      change (stepRd rl (uAnsP C G z) z (some m) v).map _ = some mk' at hmk'
      rcases hst : stepRd rl (uAnsP C G z) z (some m) v with _ | m'
      · rw [hst] at hmk'
        cases hmk'
      rw [hst] at hmk'
      cases hmk'
      obtain ⟨rfl, -⟩ := stepRd_some hst
      have hq1 : PhA C G m q.2 := hq (m, k) rfl rfl
      rw [hq1.1] at hmem
      exact phA_uAnsP hq1 hcz hW hmem
    | readK _ _ => exact hi.1.elim
    | readK' _ _ => exact hi.1.elim
  · exact hi.1.elim

/-- `x ≤ (√x + a)²`. -/
theorem le_sq_rpow_add (x a : ℝ≥0∞) : x ≤ (x ^ (2⁻¹ : ℝ) + a) ^ 2 := by
  calc x = (x ^ (2⁻¹ : ℝ)) ^ 2 := (rpow_inv_two_sq x).symm
    _ ≤ (x ^ (2⁻¹ : ℝ) + a) ^ 2 := by gcongr; exact le_self_add

/-- `√x ≤ b` gives `x ≤ b²`. -/
theorem le_sq_of_rpow_le {x b : ℝ≥0∞} (h : x ^ (2⁻¹ : ℝ) ≤ b) : x ≤ b ^ 2 := by
  calc x = (x ^ (2⁻¹ : ℝ)) ^ 2 := (rpow_inv_two_sq x).symm
    _ ≤ b ^ 2 := by gcongr

open scoped Classical in
/-- **The price of every allowed call** from a live mode: `√(gradeEta F)` for the adversary's
calls and the charged reads, nothing for the others. -/
theorem tsum_potential_stepR {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ C.trunc y = o).card ≤ F) (m₀ : Mem) (μ : RMode)
    (i : (hwSpec HashOutput HashDomain Mem).Port)
    (σ : Matrix ((hwSpec HashOutput HashDomain Mem).In i × HwReg HashOutput HashDomain Mem)
      ((hwSpec HashOutput HashDomain Mem).In i × HwReg HashOutput HashDomain Mem) ℂ)
    (hi : okR C G μ i) (hd : ¬ DoomR n μ) (hσ : σ.PosSemidef) (hs : DSupp rl projR μ σ)
    (hc : QuerySupportedOn (fun m : (hwSpec HashOutput HashDomain Mem).In i ×
      HwReg HashOutput HashDomain Mem ↦ m.2) (CInvR C G μ) σ) :
    ∑' r, (if DoomR n (nxR C G μ i r) then 0 else
        QuantumRuntime.potential (hwProjector (BadR C G))
          (((runtime2 HashOutput HashDomain m₀).step i).branch r σ)) ≤
      (QuantumRuntime.potential (hwProjector (BadR C G)) σ ^ (2⁻¹ : ℝ) +
        κA i * (ENNReal.ofReal (gradeEta HashOutput F) *
          ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ) +
        κB C G μ i * (ENNReal.ofReal (gradeEta HashOutput F) *
          ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ)) ^ 2 := by
  refine (ENNReal.tsum_le_tsum fun r ↦ (show (if DoomR n (nxR C G μ i r) then 0 else
      QuantumRuntime.potential (hwProjector (BadR C G))
        (((runtime2 HashOutput HashDomain m₀).step i).branch r σ)) ≤
      QuantumRuntime.potential (hwProjector (BadR C G))
        (((runtime2 HashOutput HashDomain m₀).step i).branch r σ) by
    split_ifs
    · exact zero_le
    · exact le_rfl)).trans ?_
  have hbr : ∀ r, ((runtime2 HashOutput HashDomain m₀).step i).branch r σ =
      MatrixMap.conj (kraus2 HashOutput HashDomain m₀ i r) σ := fun r ↦ by
    rw [runtime2_branch]
  refine (le_of_eq (tsum_congr fun r ↦ congrArg _ (hbr r))).trans ?_
  rcases μ with ⟨_ | ⟨m, k⟩, β⟩
  · exact absurd trivial hd
  have hβ : β ≠ none := fun h ↦ hd (Or.inl h)
  have hsupp := querySupportedOn_of_dSupp (proj := projR) (μ := (some (m, k), β)) rfl hs
  rcases i with (p | c) | c
  · change (∑' r : Unit, QuantumRuntime.potential (hwProjector (BadR C G))
      (MatrixMap.conj ((spongeHardwired HashOutput HashDomain (hwEmpty HashOutput HashDomain)
        m₀).U p) σ)) ≤ _
    rw [tsum_eq_single () fun r hr ↦ absurd rfl hr]
    have h := potential_sponge_badR_le (G := G) hF m₀ p hσ
    refine le_sq_of_rpow_le (h.trans ?_)
    have hA : κA (.inl (.inl p) : (hwSpec HashOutput HashDomain Mem).Port) = 1 := rfl
    have hB : κB C G (some (m, k), β) (.inl (.inl p)) = 0 := rfl
    rw [hA, hB, Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, add_zero]
    exact le_rfl
  · cases c with
    | readH z u =>
      obtain ⟨b, rfl⟩ := Option.ne_none_iff_exists'.1 hβ
      obtain ⟨c, rfl, hca⟩ := hi.2.resolve_left (Option.some_ne_none _)
      change (∑' r, QuantumRuntime.potential (hwProjector (BadR C G))
        (MatrixMap.conj (hwReadKraus (HwRead.readH z (updP C G c z)) r) σ)) ≤ _
      by_cases hans : c = .answer
      · subst hans
        have hP : QuerySupportedOn (fun q : Unit × HwReg HashOutput HashDomain Mem ↦ q.2)
            {s | PhA C G m s} σ := hc.imp fun s hs ↦ hs (m, k) rfl (by rw [hca rfl])
        refine (tsum_potential_hwReadKraus_le_of_supp (BadR C G) _ {s | PhA C G m s}
          (fun r q' q hK hq ↦ ?_) hσ hP).trans ?_
        · obtain ⟨hcz, -, hW, hmem⟩ := hwReadKraus_readH_ne_zero z _ r hK
          have hq' : PhA C G m q.2 := hq
          rw [hq'.1] at hmem
          exact iff_of_false (not_mem_badR_of_phA (phA_uAnsP hq' hcz hW hmem))
            (not_mem_badR_of_phA hq')
        · rw [add_assoc]
          exact le_sq_rpow_add _ _
      have hk : ∀ q : Unit × HwReg HashOutput HashDomain Mem, σ q q ≠ 0 →
          KeepsRecsAt z (updP C G c z) q.2.2.2 := fun q hq ↦ by
        rw [(hsupp q q hq).1.1]
        exact keepsRecs_updP hans z m
      have hA : κA (.inl (.inr (.readH z (updP C G c z))) :
          (hwSpec HashOutput HashDomain Mem).Port) = 0 := rfl
      by_cases hch : Chg C G m z
      · have h := tsum_potential_read_badR (G := G) hF hσ
          (readNoBot_of_dSupp (proj := projR) (μ := (some (m, k), some b)) rfl hs _)
          fun q hq ↦ Or.inl (hk q hq)
        refine h.trans (le_of_eq ?_)
        have hκ : κB C G (some (m, k), some b) (.inl (.inr (.readH z (updP C G c z)))) = 1 := by
          change chgR C G m z (updP C G c z) = 1
          unfold chgR
          rw [ite_eq_left ⟨hch, updP_ne_uAnsP hans z⟩]
        rw [hκ, ENNReal.ofReal_mul (gradeEta_nonneg _ _), hA, Nat.cast_zero, zero_mul, add_zero,
          Nat.cast_one, one_mul]
        exact rfl
      · refine (tsum_potential_hwReadKraus_le_of_supp (BadR C G) _ {s | s.2.2 = m}
          (fun r q' q hK hq ↦ ?_) hσ (hsupp.imp fun s hs ↦ hs.1)).trans ?_
        · obtain ⟨hcz, -, hW, hmem⟩ := hwReadKraus_readH_ne_zero z _ r hK
          have hq' : q.2.2.2 = m := hq
          exact badR_iff_of_read (hq' ▸ keepsRecs_updP hans z m) (hq' ▸ hch) hcz hW hmem
        · rw [add_assoc]
          exact le_sq_rpow_add _ _
    | readK _ _ => exact hi.1.elim
    | readK' _ _ => exact hi.1.elim
  · exact hi.1.elim

end modes

/-! ## The bound of the read program -/

section bound

variable {Par Tw Fn Out : Type} {Msg : Fn → Type} {C : TwColl Par Tw Fn Msg Out}
  {G : Fn → Tw → Prop} {n : ℕ}

open scoped Classical in
/-- **The bound of a moded read program**: if every leaf is reached in a mode whose live memory
has at most `n` charged reads and, on `true`, the judge's read in its target, the probability of
`true` is at most `(q + n)² · gradeEta F`, with `q` the adversary's calls. -/
theorem evalDistMap_le_of_modedR {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ C.trunc y = o).card ≤ F)
    (x : QuantumComp LocalSig.instruments.{0} (hwSpec HashOutput HashDomain Mem)
      (QuantumComp₂.Leaf (QReg.of Unit) Bool) (QReg.of Unit)) {q : ℕ}
    (hq : IFreeM.IsChargeBound x (portCharge κA) q)
    (hx : ModedP (okR C G) (nxR C G) (FinR C G n) (some (mem₀, 0), some false) x) :
    (runtime2 HashOutput HashDomain mem₀).evalDistMap .instruments x (SubState.basis ())
        (fun p ↦ p.2.2) {true} ≤
      ((q + n : ℕ) : ℝ≥0∞) ^ 2 * ENNReal.ofReal (gradeEta HashOutput F) := by
  have hok : ∀ μ i, okR C G μ i → OkD rl (projR μ) i := fun _ _ h ↦ h.1
  have hnx : ∀ μ i r, okR C G μ i → projR (nxR C G μ i r) = nxD rl (projR μ) i r :=
    fun _ _ r h ↦ projR_nxR r h
  refine (evalDistMap_le_eventWeight_moded rl projR mem₀ (fun _ ↦ rfl) hok hnx (BadR C G)
    (Won C G) (fun s hs' ↦ by
      obtain ⟨z, y, h1, h2⟩ := hs'
      exact Or.inr ⟨z, y, h1, h2⟩) x _ rfl hx (fun p μ hf hp m hm ↦ ?_)).trans ?_
  · rcases hμ : μ.1 with _ | ⟨m', k⟩
    · rw [projR, hμ] at hm
      cases hm
    · rw [projR, hμ] at hm
      cases hm
      exact (hf _ hμ).2.2 hp
  rw [Quantum.Sponge.eventWeight_eq_tsum_potential]
  set ρ := (SubState.basis ()).matrix ⊗ₖ
    (runtime2 HashOutput HashDomain mem₀).init.matrix with hρdef
  have hρ : ρ.PosSemidef :=
    ((SubState.basis ()).prod (runtime2 HashOutput HashDomain mem₀).init).posSemidef
  have htr : ENNReal.ofReal ρ.trace.re ≤ 1 := ENNReal.ofReal_le_one.mpr ((SubState.basis ()).prod
    (runtime2 HashOutput HashDomain mem₀).init).trace_re_le_one
  have hds : DSupp rl projR ((some (mem₀, 0), some false) : RMode) ρ :=
    dInv_init rl mem₀ (fun _ ↦ rfl) _
  have hci : QuerySupportedOn (fun m : QReg.of Unit × HwReg HashOutput HashDomain Mem ↦ m.2)
      (CInvR C G (some (mem₀, 0), some false)) ρ :=
    (querySupportedOn_init (X := HashOutput) (Z := HashDomain) mem₀
      (SubState.basis ()).matrix).imp fun s hs mk hmk _ ↦ by
      rw [Set.mem_singleton_iff] at hs
      cases hmk
      rw [hs]
      exact ⟨rfl, rfl, rfl, fun _ _ _ ↦ rfl⟩
  have hp0 : QuantumRuntime.potential (hwProjector (BadR C G)) ρ = 0 :=
    potential_init_badR mem₀ (fun _ ↦ rfl)
  have h := rpow_inv_two_tsum_potential_runtime2_moded (rl := rl) (proj := projR) mem₀ hok hnx
    (BadR C G) (DoomR n) (fun μ i r _ hd ↦ doom_nxR r hd) κA (κB C G) (budR n)
    (fun μ i r hi hd ↦ bud_nxR r hi hd) (ENNReal.ofReal (gradeEta HashOutput F))
    (ENNReal.ofReal (gradeEta HashOutput F)) (CInvR C G)
    (fun μ i r σ hi hσ ↦ cInvR_step mem₀ r hi hσ)
    (fun μ i σ hi hd hσ hs hc ↦ tsum_potential_stepR hF mem₀ μ i σ hi hd hσ hs hc)
    (fun p μ hf hd ↦ by
      rcases μ with ⟨_ | mk, β⟩
      · rfl
      · exfalso
        obtain ⟨hβ, hk, -⟩ := hf mk rfl
        change β = none ∨ n < mk.2 at hd
        rcases hd with hd | hd
        · exact hβ hd
        · omega)
    .instruments x q hq (some (mem₀, 0), some false) hx hρ hds hci
  rw [hp0, ENNReal.zero_rpow_of_pos (by norm_num), add_zero] at h
  have hb : budR n ((some (mem₀, 0), some false) : RMode) = n := Nat.sub_zero n
  rw [hb] at h
  have h1 : (ENNReal.ofReal (gradeEta HashOutput F) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (gradeEta HashOutput F) ^ (2⁻¹ : ℝ) :=
    ENNReal.rpow_le_rpow (mul_le_of_le_one_right' htr) (by norm_num)
  refine (le_sq_of_rpow_le (b := ((q + n : ℕ) : ℝ≥0∞) *
    ENNReal.ofReal (gradeEta HashOutput F) ^ (2⁻¹ : ℝ)) (h.trans ?_)).trans_eq ?_
  · rw [Nat.cast_add, add_mul]
    exact add_le_add (by gcongr) (by gcongr)
  · rw [mul_pow, rpow_inv_two_sq]

end bound

/-! ## The mixed game as a moded program -/

section transfer

open OracleComp OracleSpec

/-- **From a dead mode every program is moded**, when the dead modes allow every call and stay
dead. -/
theorem modedP_of_deadP {spec : QuantumOracleSpec.{0, 0}} {Ω : QReg → Type} {Mode : Type}
    {ok : Mode → spec.Port → Prop} {nx : Mode → (i : spec.Port) → spec.Result i → Mode}
    {fin : (Σ u, Ω u) → Mode → Prop} (Dd : Mode → Prop) (hok : ∀ μ i, Dd μ → ok μ i)
    (hnx : ∀ μ i r, Dd μ → Dd (nx μ i r)) (hfin : ∀ p μ, Dd μ → fin p μ) {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} spec Ω A) : ∀ μ, Dd μ → ModedP ok nx fin μ x := by
  induction x using IFreeM.inductionOn with
  | pure _ a => exact fun μ h ↦ hfin _ μ h
  | liftBind _ c next ih =>
    intro μ h
    rcases c with o | ⟨i, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih b μ h⟩
    · exact ⟨hok μ i h, fun b ↦ ih b _ (hnx μ i b.down h)⟩

/-- **Moded substitution with dead modes**: if every allowed command's tree is moded, ending in
the mode the command moves to or in a dead mode, the substituted program is moded. -/
theorem modedP_substitute_dead {spec spec' : QuantumOracleSpec.{0, 0}} {Ω : QReg → Type}
    {Mode : Type} {ok : Mode → spec.Port → Prop}
    {nx : Mode → (i : spec.Port) → spec.Result i → Mode} {ok' : Mode → spec'.Port → Prop}
    {nx' : Mode → (i : spec'.Port) → spec'.Result i → Mode}
    (h : CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec'))
    (Dd : Mode → Prop) (hok : ∀ μ i, Dd μ → ok' μ i) (hnx : ∀ μ i r, Dd μ → Dd (nx' μ i r))
    (hh : ∀ (A : QReg) (c : QuantumComp.Cmd LocalSig.instruments.{0} spec A) μ,
      modeCmdOk ok c μ →
        ModedP ok' nx' (fun p μ' ↦ μ' = modeCmdNx nx c μ p.2.1 ∨ Dd μ') μ (h A c))
    {fin : (Σ u, Ω u) → Mode → Prop} (hfin : ∀ p μ, Dd μ → fin p μ) {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} spec Ω A) :
    ∀ μ, ModedP ok nx fin μ x → ModedP ok' nx' fin μ (x.substitute h) := by
  induction x using IFreeM.inductionOn with
  | pure _ a => exact fun μ hx ↦ hx
  | liftBind A c next ih =>
    intro μ hx
    rw [IFreeM.substitute_liftBind]
    refine modedP_bind _ _ (hh A c μ hx.1) fun u p μ' hμ' ↦ ?_
    obtain ⟨b, e⟩ := p
    subst e
    rcases hμ' with h' | h'
    · rw [h']
      exact ih b _ (hx.2 b)
    · exact modedP_of_deadP Dd hok hnx hfin _ μ' h'

variable {Par Tw Fn Out : Type} {Msg : Fn → Type} {C : TwColl Par Tw Fn Msg Out}
  {G : Fn → Tw → Prop}

theorem nxT_ne_none {β : Option Bool} (hβ : β ≠ none) (i : (MixSpec Caller).Port)
    (r : (MixSpec Caller).Result i) : nxT β i r ≠ none := by
  obtain ⟨b, rfl⟩ := Option.ne_none_iff_exists'.1 hβ
  rcases i with p | ⟨c, t⟩
  · exact Option.some_ne_none _
  · rcases t with n | z <;> cases c <;> exact Option.some_ne_none _

theorem stepRd_updK_some (c : Caller) (z : HashDomain) (m : Mem) (k : ℕ) (v : HashOutput) :
    stepRd rlK (updK C G c z) z (some (m, k)) v =
      (stepRd rl (updP C G c z) z (some m) v).map
        fun m' ↦ (m', k + chgR C G m z (updP C G c z)) := by
  simp only [stepRd]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1 h2 | exact absurd h2 h1

open scoped Classical in
theorem nxC2_readH (β : Option Bool) (c : Caller) (z : HashDomain) (r : Option HashOutput × Mem)
    (v : HashOutput) :
    nxC2 C G β (.inl (.inr (.readH z (updP C G c z)))) r = nxT β (.call (c, .inr z)) v := by
  rcases β with _ | b
  · rfl
  · show some (@ite _ (updP C G c z = uAnsP C G z) (Classical.propDecidable _) b true) =
      nxT (some b) (.call (c, .inr z)) v
    rw [nxT_call_inr]
    rcases Classical.em (c = .answer) with hc | hc
    · rw [ite_eq_left ((updP_eq_uAnsP_iff c z).2 hc), ite_eq_left hc]
    · rw [ite_eq_right (updP_ne_uAnsP hc z), ite_eq_right hc]

/-- The read modes after a read of a caller's policy follow the mixed modes, or die. -/
theorem nxR_readH_eq (μ : RMode) (tag : Caller) (z : HashDomain) (r : Option HashOutput × Mem) :
    nxR C G μ (.inl (.inr (.readH z (updP C G tag z)))) r =
        (nxM (updK C G) rlK μ.1 (.call (tag, .inr z)) (r.1.getD 0),
          nxT μ.2 (.call (tag, .inr z)) (r.1.getD 0)) ∨
      (nxR C G μ (.inl (.inr (.readH z (updP C G tag z)))) r).1 = none := by
  rcases μ with ⟨_ | ⟨m, k⟩, β⟩
  · exact Or.inr rfl
  rcases r with ⟨_ | v, m'⟩
  · exact Or.inr rfl
  · refine Or.inl (Prod.ext ?_ (nxC2_readH β tag z _ _))
    change (stepRd rl (updP C G tag z) z (some m) v).map _ =
      stepRd rlK (updK C G tag z) z (some (m, k)) v
    rw [stepRd_updK_some]

/-- One step of a moded command tree: normalize the head, then split the command. -/
local macro "moded_step" : tactic => `(tactic| (
  (conv => arg 5; whnf);
  refine ⟨?_, fun _ ↦ ?_⟩))

/-- **The read program of a mixed program moded in the memory with the count and the phase is
moded in the read modes.** -/
theorem modedP_toReadsR {Ω : QReg → Type} {fin : (Σ u, Ω u) → RMode → Prop}
    (hfin : ∀ p μ, μ.1 = none → fin p μ) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) Ω A)
    (μ : RMode)
    (hx : ModedP (fun μ i ↦ okM μ.1 i ∧ okT μ.2 i)
      (fun μ i r ↦ (nxM (updK C G) rlK μ.1 i r, nxT μ.2 i r)) fin μ x) :
    ModedP (okR C G) (nxR C G) fin μ
      (IFreeM.mapLens Quantum.Xmss.Assembly.liftReadLens
        (IFreeM.substitute (readSub (updP C G)) x)) := by
  rw [← IFreeM.substitute_toSubstitution, Quantum.Xmss.Assembly.substitute_substitute]
  refine modedP_substitute_dead _ (fun μ : RMode ↦ μ.1 = none)
    (fun μ i h ↦ ⟨by rw [projR, h]; trivial, Or.inl h⟩)
    (fun μ i r h ↦ by
      change nxK C G μ.1 i r = none
      rw [h]
      rfl) (fun A c μ hc ↦ ?_) hfin x μ hx
  rcases c with o | ⟨p | ⟨tag, n | z⟩, E, ℓ⟩
  · moded_step
    · trivial
    · exact Or.inl rfl
  · moded_step
    · refine ⟨okD_sponge rl _ _, ?_⟩
      rcases μ with ⟨_ | mk, β⟩
      · exact Or.inl rfl
      · exact Or.inr (by rcases β with _ | _ <;> trivial)
    · refine Or.inl (Prod.ext ?_ ?_)
      · rcases μ with ⟨_ | mk, β⟩ <;> rfl
      · rcases μ with ⟨μ₁, _ | b⟩ <;> rfl
  · moded_step
    · trivial
    moded_step
    · trivial
    refine Or.inl (Prod.ext rfl ?_)
    rcases μ with ⟨μ₁, _ | b⟩
    · rfl
    · cases tag <;> rfl
  · moded_step
    · trivial
    moded_step
    · refine ⟨okD_readH rl _ z _ (recordsAt_updP tag z), ?_⟩
      rcases μ with ⟨_ | mk, β⟩
      · exact Or.inl rfl
      · refine Or.inr ?_
        rcases β with _ | b
        · trivial
        · refine ⟨tag, rfl, fun ht ↦ ?_⟩
          subst ht
          have h2 : okT (some b) (.call (.answer, .inr z)) := hc.2
          cases b
          · rfl
          · exact h2.elim
    moded_step
    · trivial
    exact nxR_readH_eq _ tag z _

end transfer

/-! ## The QROM bound of SM-TCR-C with free answers and re-reads -/

section main

open OracleComp OracleSpec TcrQuery

variable {Par Tw Fn Out EFn EOut : Type} {Msg : Fn → Type} {EMsg : EFn → Type}
  {C : TwColl Par Tw Fn Msg Out} {D : TwColl Par Tw EFn EMsg EOut} {G : Fn → Tw → Prop}

/-- **The read program of the game is moded**: every leaf in a mode with a phase, at most `n`
charged reads and, on `true`, the judge's read in its target. -/
theorem modedP_tcrReads [SampleableType Par] (hs : GSep C G)
    (hinj : ∀ l P t, (C.layout l P t).Injective) (htw : D.TweakSeparated C)
    (hlen : C.LengthLe maxLen) (n : ℕ) {Q : Type} {R : OracleSpec.{0, 0} Q} {St S0 F' : Type}
    (pre : Unit → OracleComp (romWorld.Oracles + TcrSpec Par Tw Fn Msg Out EFn EMsg EOut) S0)
    (adv : Unit → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F')
    (st0 : Unit → S0 → St)
    (σ : Unit → HHandler romWorld R (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut) St)
    (post : Unit → S0 → F' → St →
      OracleComp (romWorld.Oracles + TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)
        (Σ l, Tw × Msg l))
    (hpre : ∀ p, ChalFirst (pre p)) (hσ : ∀ p st q, Common.QueryCostAtMost (σ p st q) chalW 0)
    (hpost : ∀ p a f st, Common.QueryCostAtMost (post p a f st) chalW 0)
    (Ju : Par → S0 → St × QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut) → Option MemK →
      Prop)
    (hpreU : ∀ P a μ, LiveRedRun rlK (updK C G) ((smTcrIn romWorld C D G).answer P) (pre ()) []
      (some (mem₀, 0)) a μ → Ju P a.1 (st0 () a.1, a.2) μ)
    (hσU : ∀ P a st log μ qq, Ju P a (st, log) μ → ∀ r μ',
      LiveRedRun rlK (updK C G) ((smTcrIn romWorld C D G).answer P) (σ () st qq) log μ r μ' →
        Ju P a (r.1.2, r.2) μ')
    (hpostU : ∀ P a f st log μ, Ju P a (st, log) μ → ∀ r μ',
      LiveRedRun rlK (updK C G) ((smTcrIn romWorld C D G).answer P) (post () a f st) log μ r μ' →
        cnt μ' + 1 ≤ n) :
    ModedP (okR C G) (nxR C G) (FinR C G n) (some (mem₀, 0), some false)
      (Quantum.Xmss.Assembly.liftReadProg
        (toReads (updP C G) (mixGame (smTcrIn romWorld C D G) pre adv st0 σ post))) := by
  have hmix := modedP_mixGame (updK C G) rlK (smTcrIn romWorld C D G) pre adv st0 σ post
    (mem₀, 0) (fun _ μ ↦ μ = some (mem₀, 0))
    (fun _ μ h ↦ liveRun_inv (fun _ ↦ True) rlK (updK C G .setup) (· = some (mem₀, 0))
      (fun _ _ _ hz _ ↦ absurd trivial hz) _
      (Common.isWeightBound_liftM_probComp (gCost fun _ ↦ True) (fun _ ↦ rfl) ($ᵗ Par)) h rfl)
    (fun P a s μ ↦ LiveInv C D G P s.2 (μ.map Prod.fst) ∧ Ju P a s μ)
    (fun P μ h0 a μ' hrun ↦ by
      subst h0
      have hI0 : LiveInv C D G P [] ((some ((mem₀, 0) : MemK)).map Prod.fst) := by
        intro m hm
        cases hm
        refine ⟨rfl, fun _ _ hv ↦ absurd hv (by simp [mem₀, Mem.recs]), fun _ e he ↦ ?_⟩
        simp [tcrTargets] at he
      have h1 := liveInv_liveRedRunK hs htw hlen _ hrun hI0
      exact ⟨h1, hpreU P a μ' hrun⟩)
    (fun P a st log μ qq hJ r μ' hrun ↦
      ⟨(liveInv_liveRedRunK hs htw hlen _ hrun hJ.1 :), hσU P a st log μ qq hJ.2 r μ' hrun⟩)
    (fun P r μ ↦ LiveInv C D G P r.2 (μ.map Prod.fst) ∧ cnt μ + 1 ≤ n)
    (fun P a f st log μ hJ r μ' hrun ↦
      ⟨liveInv_liveRedRunK hs htw hlen _ hrun hJ.1, hpostU P a f st log μ hJ.2 r μ' hrun⟩)
    (fun b μ ↦ ∀ mk, μ = some mk → mk.2 ≤ n ∧ (b = true → mk.1 ∈ Won C G))
    (fun P r μ hpo b μ' hrun mk' hmk' ↦ by
      obtain ⟨hI, hcnt⟩ := hpo
      have hc := cnt_liveRun_judge hlen r.1 hrun
      rw [hmk'] at hc
      refine ⟨by change mk'.2 ≤ cnt μ + 1 at hc; omega, fun hb ↦ ?_⟩
      subst hb
      exact won_of_judge hs hinj htw hlen r.1 hI (liveRun_mapK .judge _ hrun) mk'.1
        (by rw [hmk']; rfl))
  have hph := modedP_mixGame_phase (smTcrIn romWorld C D G) pre adv st0 σ post setup_noHash hpre
    hσ hpost
  have hph' := modedP_doom (fun β : Option Bool ↦ β ≠ none)
    (fun _ i r _ hβ ↦ nxT_ne_none hβ i r) _ (some false) (Option.some_ne_none _) hph
  have hprod := Quantum.Xmss.Assembly.modedP_prod _ _ _ hmix hph'
  refine modedP_toReadsR (fun p μ h mk hmk ↦ by rw [h] at hmk; cases hmk) _ _
    (modedP_mono (fun p μ h mk hmk ↦ ?_) _ _ hprod)
  obtain ⟨h1, -, h2⟩ := h
  exact ⟨h2, h1 mk hmk⟩

open scoped Classical in
/-- **The QROM bound of the restricted SM-TCR-C game, with free answers and re-reads.** Let the
target collection `C` be `G`-separated, injective in the message, every input at most `maxLen`
bytes, the evaluation collection `D` tweak-separated from `C`, and every fiber of `C.trunc` of
at most `F` values. Let the reduction ask the challenger only before its own hashes (`ChalFirst`),
and its handler and output never. Let `Ju` be an invariant of the reduction's live runs (every
read answered by any value consistent with the log, the memory moved by the policies `updK`)
under which the output leaves at most `n - 1` charged reads (`cnt`: reads of the setup, the
reduction or the decision at `G`-cells that are no record; the challenger's answers and re-reads
of the records are free). With `q` adversary calls the average winning probability over the
tables is at most `(q + n)² (2 √(F/N) + √((F + 2)/N))²`, `N = 2^256`. -/
theorem probAvg_smTcrIn_slRed_le_count [SampleableType Par] (hs : GSep C G)
    (hinj : ∀ l P t, (C.layout l P t).Injective) (htw : D.TweakSeparated C)
    (hlen : C.LengthLe maxLen) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ C.trunc y = o).card ≤ F)
    {Q : Type} {R : OracleSpec.{0, 0} Q} {St S0 F' : Type}
    (pre : Unit → OracleComp (romWorld.Oracles + TcrSpec Par Tw Fn Msg Out EFn EMsg EOut) S0)
    (adv : Unit → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F')
    (st0 : Unit → S0 → St)
    (σ : Unit → HHandler romWorld R (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut) St)
    (post : Unit → S0 → F' → St →
      OracleComp (romWorld.Oracles + TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)
        (Σ l, Tw × Msg l))
    (hpre : ∀ p, ChalFirst (pre p)) (hσ : ∀ p st q, Common.QueryCostAtMost (σ p st q) chalW 0)
    (hpost : ∀ p a f st, Common.QueryCostAtMost (post p a f st) chalW 0) {q : ℕ}
    (hq : ∀ a, IFreeM.IsChargeBound (adv () a) (cmdCharge hashCharge) q) (n : ℕ)
    (Ju : Par → S0 → St × QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut) → Option MemK →
      Prop)
    (hpreU : ∀ P a μ, LiveRedRun rlK (updK C G) ((smTcrIn romWorld C D G).answer P) (pre ()) []
      (some (mem₀, 0)) a μ → Ju P a.1 (st0 () a.1, a.2) μ)
    (hσU : ∀ P a st log μ qq, Ju P a (st, log) μ → ∀ r μ',
      LiveRedRun rlK (updK C G) ((smTcrIn romWorld C D G).answer P) (σ () st qq) log μ r μ' →
        Ju P a (r.1.2, r.2) μ')
    (hpostU : ∀ P a f st log μ, Ju P a (st, log) μ → ∀ r μ',
      LiveRedRun rlK (updK C G) ((smTcrIn romWorld C D G).answer P) (post () a f st) log μ r μ' →
        cnt μ' + 1 ≤ n) :
    romWorld.probAvg ((smTcrIn romWorld C D G).game fun p ↦
        slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) ≤
      ((q + n : ℕ) : ℝ≥0∞) ^ 2 * ENNReal.ofReal (gradeEta HashOutput F) :=
  (probAvg_game_slRed_le_hw (smTcrIn romWorld C D G) pre adv st0 σ post (updP C G) mem₀).trans
    (evalDistMap_le_of_modedR hF _ (isChargeBound_toReads (updP C G)
      (isChargeBound_mixGame (smTcrIn romWorld C D G) pre adv st0 σ post fun _ a ↦ hq a))
      (modedP_tcrReads hs hinj htw hlen n pre adv st0 σ post hpre hσ hpost Ju hpreU hσU hpostU))

open scoped Classical in
/-- **The QROM bound of the restricted SM-TCR-C game, by the reduction's own reads.** As
`probAvg_smTcrIn_slRed_le_count`, the reduction reading at most `c₀` `G`-cells itself in its setup
(the challenger's answers are free), none in its handler and at most `c₁` in its output:
`probAvg ≤ (q + c₀ + c₁ + 1)² · gradeEta F` (the judge's read is the last charged read). -/
theorem probAvg_smTcrIn_slRed_le_free [SampleableType Par] (hs : GSep C G)
    (hinj : ∀ l P t, (C.layout l P t).Injective) (htw : D.TweakSeparated C)
    (hlen : C.LengthLe maxLen) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ C.trunc y = o).card ≤ F)
    {Q : Type} {R : OracleSpec.{0, 0} Q} {St S0 F' : Type}
    (pre : Unit → OracleComp (romWorld.Oracles + TcrSpec Par Tw Fn Msg Out EFn EMsg EOut) S0)
    (adv : Unit → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F')
    (st0 : Unit → S0 → St)
    (σ : Unit → HHandler romWorld R (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut) St)
    (post : Unit → S0 → F' → St →
      OracleComp (romWorld.Oracles + TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)
        (Σ l, Tw × Msg l))
    (hpre : ∀ p, ChalFirst (pre p)) (hσ : ∀ p st q, Common.QueryCostAtMost (σ p st q) chalW 0)
    (hpost : ∀ p a f st, Common.QueryCostAtMost (post p a f st) chalW 0) {q : ℕ}
    (hq : ∀ a, IFreeM.IsChargeBound (adv () a) (cmdCharge hashCharge) q) (c₀ c₁ : ℕ)
    (hpreW : Common.QueryCostAtMost (pre ())
      (gWR C G (R' := TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)) c₀)
    (hσW : ∀ st qq, Common.QueryCostAtMost (σ () st qq)
      (gWR C G (R' := TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)) 0)
    (hpostW : ∀ a f st, Common.QueryCostAtMost (post () a f st)
      (gWR C G (R' := TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)) c₁) :
    romWorld.probAvg ((smTcrIn romWorld C D G).game fun p ↦
        slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) ≤
      ((q + (c₀ + c₁ + 1) : ℕ) : ℝ≥0∞) ^ 2 * ENNReal.ofReal (gradeEta HashOutput F) :=
  probAvg_smTcrIn_slRed_le_count hs hinj htw hlen hF pre adv st0 σ post hpre hσ hpost hq
    (c₀ + c₁ + 1) (fun _ _ _ μ ↦ cnt μ ≤ c₀)
    (fun _ _ _ hrun ↦ (cnt_liveRedRun _ _ hpreW hrun).trans (by simp [cnt]))
    (fun _ _ st _ _ qq hJ _ _ hrun ↦ (cnt_liveRedRun _ _ (hσW st qq) hrun).trans
      (by rw [Nat.add_zero]; exact hJ))
    (fun _ a f st _ _ hJ _ _ hrun ↦ by
      have h := cnt_liveRedRun _ _ (hpostW a f st) hrun
      omega)

end main

/-! ## Live runs at a table -/

section tables

open OracleComp OracleSpec

variable {Par Tw Fn Out : Type} {Msg : Fn → Type} {C : TwColl Par Tw Fn Msg Out}
  {G : Fn → Tw → Prop}

/-- **A table consistent with the log** of a memory. -/
def Consistent (H : HashDomain → HashOutput) (m : Mem) : Prop :=
  ∀ z w, m.log z = some w → H z = w

/-- A table consistent after a live read was consistent before, and answered the read. -/
theorem consistent_of_stepRd {c : Caller} {z : HashDomain} {mk mk' : MemK} {v : HashOutput}
    (h : stepRd rlK (updK C G c z) z (some mk) v = some mk') {H : HashDomain → HashOutput}
    (hH : Consistent H mk'.1) : Consistent H mk.1 ∧ H z = v := by
  obtain ⟨rfl, h2⟩ := stepRd_some h
  have hlog : (updK C G c z mk (some v)).1.log = Function.update mk.1.log z (some v) :=
    recordsAt_updP c z mk.1 (some v)
  have hz : H z = v := hH z v (by rw [hlog, Function.update_self])
  refine ⟨fun x w hx ↦ ?_, hz⟩
  by_cases hxz : x = z
  · subst hxz
    rcases h2 with h2 | h2
    · change mk.1.log x = none at h2
      rw [h2] at hx
      cases hx
    · change mk.1.log x = some v at h2
      rw [h2] at hx
      cases hx
      exact hz
  · exact hH x w (by rw [hlog, Function.update_of_ne hxz]; exact hx)

/-- The coins of a live run keep the mode. -/
theorem mode_of_liveImpl_coin {u : HashDomain → MemK → Option HashOutput → MemK} {n : ℕ}
    {y : romWorld.Oracles.Range (.inl n)} {μ μ₁ : Option MemK}
    (h : (y, μ₁) ∈ support ((liveImpl rlK u (.inl n)).run μ)) : μ₁ = μ := by
  change (y, μ₁) ∈ support ((fun b ↦ (b, μ)) <$> liftM (romWorld.Oracles.query (.inl n))) at h
  rw [support_map] at h
  obtain ⟨_, _, he⟩ := h
  exact (Prod.mk.inj he).2.symm

/-- **A table consistent at the end of a live run was consistent along it.** -/
theorem consistent_of_liveRun {c : Caller} {α : Type} (oa : OracleComp romWorld.Oracles α)
    {μ : Option MemK} {a : α} {mk' : MemK} (h : LiveRun rlK (updK C G c) oa μ a (some mk'))
    {H : HashDomain → HashOutput} (hH : Consistent H mk'.1) :
    ∀ mk, μ = some mk → Consistent H mk.1 := by
  induction oa using OracleComp.inductionOn generalizing μ with
  | pure x =>
    obtain ⟨-, rfl⟩ := liveRun_pure_inv h
    rintro mk ⟨⟩
    exact hH
  | query_bind t k ih =>
    obtain ⟨y, μ₁, h₁, h₂⟩ := liveRun_query_bind h
    intro mk hmk
    subst hmk
    rcases t with n | z
    · rw [mode_of_liveImpl_coin h₁] at h₂
      exact ih y h₂ mk rfl
    · rw [eq_stepRd_of_mem_support h₁] at h₂
      rcases hst : stepRd rlK (updK C G c z) z (some mk) y with _ | mk₁
      · rw [hst] at h₂
        exact absurd (liveRun_none_mode _ h₂) (Option.some_ne_none _)
      · rw [hst] at h₂
        exact (consistent_of_stepRd hst (ih y h₂ mk₁ rfl)).1

/-- **A live run is a run at every table consistent with its end.** -/
theorem mem_support_eager_of_liveRun {c : Caller} {α : Type} (oa : OracleComp romWorld.Oracles α)
    {mk mk' : MemK} {a : α} (h : LiveRun rlK (updK C G c) oa (some mk) a (some mk'))
    {H : HashDomain → HashOutput} (hH : Consistent H mk'.1) :
    a ∈ support (simulateQ (romWorld.eager H) oa) := by
  induction oa using OracleComp.inductionOn generalizing mk with
  | pure x =>
    obtain ⟨rfl, -⟩ := liveRun_pure_inv h
    simp
  | query_bind t k ih =>
    obtain ⟨y, μ₁, h₁, h₂⟩ := liveRun_query_bind h
    rw [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff]
    rcases t with n | z
    · rw [mode_of_liveImpl_coin h₁] at h₂
      refine ⟨y, ?_, ih y h₂⟩
      change y ∈ support (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
      simp
    · rw [eq_stepRd_of_mem_support h₁] at h₂
      rcases hst : stepRd rlK (updK C G c z) z (some mk) y with _ | mk₁
      · rw [hst] at h₂
        exact absurd (liveRun_none_mode _ h₂) (Option.some_ne_none _)
      · rw [hst] at h₂
        have hz := (consistent_of_stepRd hst (consistent_of_liveRun _ h₂ hH mk₁ rfl)).2
        refine ⟨y, ?_, ih y h₂⟩
        exact (show (y : HashOutput) ∈ support (pure (H z) : ProbComp HashOutput) by
          rw [support_pure, hz]
          exact Set.mem_singleton _)

/-- A reduction's live run from the dead mode stays dead. -/
theorem liveRedRun_none {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q')) {α : Type}
    (oa : OracleComp (romWorld.Oracles + R') α) {log : QueryLog R'} {a : α × QueryLog R'}
    {μ' : Option MemK} (h : LiveRedRun rlK (updK C G) ans oa log none a μ') : μ' = none :=
  liveRedRun_inv_cost (updK C G) rlK ans (fun _ ↦ 0) (fun _ μ ↦ μ = none)
    (fun _ _ _ _ _ hμ ↦ by rw [hμ]; rfl) (fun _ _ _ _ _ _ hμ h' ↦ by
      rw [hμ] at h'
      exact liveRun_none_mode _ h') oa (queryCostAtMost_zero oa) h rfl

/-- **A table consistent at the end of a reduction's live run was consistent along it.** -/
theorem consistent_of_liveRedRun {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q')) {α : Type}
    (oa : OracleComp (romWorld.Oracles + R') α) {log : QueryLog R'} {μ : Option MemK}
    {a : α × QueryLog R'} {mk' : MemK} (h : LiveRedRun rlK (updK C G) ans oa log μ a (some mk'))
    {H : HashDomain → HashOutput} (hH : Consistent H mk'.1) :
    ∀ mk, μ = some mk → Consistent H mk.1 := by
  induction oa using OracleComp.inductionOn generalizing log μ with
  | pure x =>
    unfold LiveRedRun at h
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at h
    rintro mk rfl
    obtain ⟨-, -, h3⟩ := h
    cases h3
    exact hH
  | query_bind t k ih =>
    unfold LiveRedRun at h
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at h
    obtain ⟨⟨y, log₁, μ₁⟩, h₁, h₂⟩ := h
    have hrest : ∀ mk₁, μ₁ = some mk₁ → Consistent H mk₁.1 := ih y h₂
    intro mk hmk
    subst hmk
    rcases t with (n | z) | q'
    · change (y, log₁, μ₁) ∈ support ((fun p ↦ (p.1, (log, p.2))) <$>
        (liveImpl rlK (updK C G .red) (.inl n)).run (some mk)) at h₁
      rw [support_map] at h₁
      obtain ⟨⟨y', μ₂⟩, h₃, he⟩ := h₁
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, -, rfl⟩ := he
      exact hrest mk (mode_of_liveImpl_coin h₃)
    · change (y, log₁, μ₁) ∈ support ((fun p ↦ (p.1, (log, p.2))) <$>
        (liveImpl rlK (updK C G .red) (.inr z)).run (some mk)) at h₁
      rw [support_map] at h₁
      obtain ⟨⟨y', μ₂⟩, h₃, he⟩ := h₁
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, -, rfl⟩ := he
      rw [eq_stepRd_of_mem_support h₃] at hrest h₂
      rcases hst : stepRd rlK (updK C G .red z) z (some mk) y' with _ | mk₁
      · rw [hst] at h₂
        exact absurd (liveRedRun_none ans _ h₂) (Option.some_ne_none _)
      · exact (consistent_of_stepRd hst (hrest mk₁ hst)).1
    · change (y, log₁, μ₁) ∈ support ((fun p ↦ (p.1, (log ++ [⟨q', p.1⟩], p.2))) <$>
        (simulateQ (liveImpl rlK (updK C G .answer)) (ans q')).run (some mk)) at h₁
      rw [support_map] at h₁
      obtain ⟨⟨y', μ₂⟩, h₃, he⟩ := h₁
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, -, rfl⟩ := he
      rcases μ₂ with _ | mk₂
      · exact absurd (liveRedRun_none ans _ h₂) (Option.some_ne_none _)
      · exact consistent_of_liveRun (ans q') (c := .answer) h₃ (hrest mk₂ rfl) mk rfl

/-- **A reduction's live run is a run at every table consistent with its end**, its transcript
and value included. -/
theorem mem_support_logImpl_of_liveRedRun {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q')) {α : Type}
    (oa : OracleComp (romWorld.Oracles + R') α) {log : QueryLog R'} {mk mk' : MemK}
    {a : α × QueryLog R'} (h : LiveRedRun rlK (updK C G) ans oa log (some mk) a (some mk'))
    {H : HashDomain → HashOutput} (hH : Consistent H mk'.1) :
    a ∈ support ((simulateQ (logImpl (W := romWorld) H ans) oa).run log) := by
  induction oa using OracleComp.inductionOn generalizing log mk with
  | pure x =>
    unfold LiveRedRun at h
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at h
    obtain ⟨h1, h2, -⟩ := h
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff]
    exact Prod.ext h1 h2
  | query_bind t k ih =>
    unfold LiveRedRun at h
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at h
    obtain ⟨⟨y, log₁, μ₁⟩, h₁, h₂⟩ := h
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
    rcases μ₁ with _ | mk₁
    · exact absurd (liveRedRun_none ans _ h₂) (Option.some_ne_none _)
    refine ⟨(y, log₁), ?_, ih y h₂⟩
    rcases t with (n | z) | q'
    · change (y, log₁, some mk₁) ∈ support ((fun p ↦ (p.1, (log, p.2))) <$>
        (liveImpl rlK (updK C G .red) (.inl n)).run (some mk)) at h₁
      rw [support_map] at h₁
      obtain ⟨⟨y', μ₂⟩, -, he⟩ := h₁
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, hl, -⟩ := he
      subst hl
      simp [logImpl, romWorld, eagerFunOracles]
    · change (y, log₁, some mk₁) ∈ support ((fun p ↦ (p.1, (log, p.2))) <$>
        (liveImpl rlK (updK C G .red) (.inr z)).run (some mk)) at h₁
      rw [support_map] at h₁
      obtain ⟨⟨y', μ₂⟩, h₃, he⟩ := h₁
      simp only [Prod.mk.injEq] at he
      obtain ⟨hy, hl, hμ⟩ := he
      subst hy hl hμ
      have hst := (eq_stepRd_of_mem_support h₃).symm
      have hz := (consistent_of_stepRd hst (consistent_of_liveRedRun ans _ h₂ hH mk₁ rfl)).2
      rw [← hz]
      simp [logImpl, romWorld, eagerFunOracles]
      exact Set.mem_singleton _
    · change (y, log₁, some mk₁) ∈ support ((fun p ↦ (p.1, (log ++ [⟨q', p.1⟩], p.2))) <$>
        (simulateQ (liveImpl rlK (updK C G .answer)) (ans q')).run (some mk)) at h₁
      rw [support_map] at h₁
      obtain ⟨⟨y', μ₂⟩, h₃, he⟩ := h₁
      simp only [Prod.mk.injEq] at he
      obtain ⟨hy, hl, hμ⟩ := he
      subst hy hl hμ
      show _ ∈ support ((fun a ↦ (a, log ++ [⟨q', a⟩])) <$> simulateQ (romWorld.eager H) (ans q'))
      rw [support_map]
      exact ⟨_, mem_support_eager_of_liveRun (ans q') (c := .answer) h₃
        (consistent_of_liveRedRun ans _ h₂ hH mk₁ rfl), rfl⟩

open scoped Classical in
/-- **The failing semantics** at the table `H`: coins and challenger queries fail, a read of a
cell of `B` fails, every other read answers `H`. -/
noncomputable def failImpl {Q' : Type} {R' : OracleSpec.{0, 0} Q'} (H : HashDomain → HashOutput)
    (B : HashDomain → Prop) : QueryImpl (romWorld.Oracles + R') Option
  | .inl (.inl _) => none
  | .inl (.inr z) => if B z then none else some (H z)
  | .inr _ => none

/-- A table consistent with a memory's log. -/
theorem consistent_logD (m : Mem) : Consistent (fun z ↦ (m.log z).getD 0) m :=
  fun z w hz ↦ by simp [hz]

open scoped Classical in
/-- **A reduction's algorithm never failing at the tables consistent with the log** makes no
charged read on its live runs, keeps the records, and returns its value at every table
consistent with its end. -/
theorem liveRedRun_of_fail {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q')) {α : Type}
    (oa : OracleComp (romWorld.Oracles + R') α) {log : QueryLog R'} {m : Mem} {k : ℕ}
    {a : α × QueryLog R'} {mk' : MemK}
    (hrun : LiveRedRun rlK (updK C G) ans oa log (some (m, k)) a (some mk'))
    (hf : ∀ H, Consistent H m → simulateQ (failImpl H (Chg C G m)) oa ≠ none) :
    mk'.2 = k ∧ mk'.1.recs = m.recs ∧ a.2 = log ∧
      ∀ H, Consistent H mk'.1 → simulateQ (failImpl H (Chg C G m)) oa = some a.1 := by
  induction oa using OracleComp.inductionOn generalizing log m k with
  | pure x =>
    unfold LiveRedRun at hrun
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hrun
    obtain ⟨h1, h2, h3⟩ := hrun
    cases h3
    exact ⟨rfl, rfl, h2, fun _ _ ↦ by rw [simulateQ_pure, h1]; rfl⟩
  | query_bind t k' ih =>
    unfold LiveRedRun at hrun
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hrun
    obtain ⟨⟨y, log₁, μ₁⟩, h₁, h₂⟩ := hrun
    have hf0 := hf _ (consistent_logD m)
    rw [simulateQ_bind, simulateQ_spec_query] at hf0
    rcases t with (n | z) | q'
    · exact absurd rfl hf0
    · change (y, log₁, μ₁) ∈ support ((fun p ↦ (p.1, (log, p.2))) <$>
        (liveImpl rlK (updK C G .red) (.inr z)).run (some (m, k))) at h₁
      rw [support_map] at h₁
      obtain ⟨⟨y', μ₂⟩, h₃, he⟩ := h₁
      simp only [Prod.mk.injEq] at he
      obtain ⟨hy, hl, hμ⟩ := he
      subst hl hμ
      rw [hy] at h₃
      rw [eq_stepRd_of_mem_support h₃] at h₂
      rcases hst : stepRd rlK (updK C G .red z) z (some (m, k)) y with _ | mk₁
      · rw [hst] at h₂
        exact absurd (liveRedRun_none ans _ h₂) (Option.some_ne_none _)
      rw [hst] at h₂
      obtain ⟨rfl, -⟩ := stepRd_some hst
      have hch : ¬ Chg C G m z := by
        intro hb
        refine hf _ (consistent_of_stepRd hst (consistent_logD _)).1 ?_
        rw [simulateQ_bind, simulateQ_spec_query]
        change (if Chg C G m z then none else some _) >>= _ = none
        rw [ite_eq_left hb]
        rfl
      have hrecs : (updK C G .red z (m, k) (some y)).1.recs = m.recs := rfl
      have hk : (updK C G .red z (m, k) (some y)).2 = k := by
        change k + chgR C G m z (uRed z) = k
        unfold chgR
        rw [ite_eq_right fun h ↦ hch h.1, Nat.add_zero]
      have key : ∀ H, Consistent H (updK C G .red z (m, k) (some y)).1 →
          simulateQ (failImpl H (Chg C G m)) (k' y) =
            simulateQ (failImpl H (Chg C G m)) (liftM ((romWorld.Oracles + R').query
              (.inl (.inr z))) >>= k') := by
        intro H hH
        rw [simulateQ_bind, simulateQ_spec_query]
        change _ = (if Chg C G m z then none else some (H z)) >>= _
        rw [ite_eq_right hch]
        exact congrArg (fun u ↦ simulateQ (failImpl H (Chg C G m)) (k' u))
          (consistent_of_stepRd hst hH).2.symm
      obtain ⟨h1, h2, h3, h4⟩ := ih y h₂ fun H hH h0 ↦
        hf H (consistent_of_stepRd hst hH).1 ((key H hH).symm.trans h0)
      refine ⟨h1.trans hk, h2.trans hrecs, h3, fun H hH ↦ ?_⟩
      exact (key H (consistent_of_liveRedRun ans _ h₂ hH _ rfl)).symm.trans (h4 H hH)
    · exact absurd rfl hf0

end tables

end Quantum.StdModel.Qrom.Tcr2

end
