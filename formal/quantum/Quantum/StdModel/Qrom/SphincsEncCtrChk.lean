module

public import Quantum.StdModel.Qrom.LiveDet
public import Quantum.StdModel.Sphincs.ItsrHop

@[expose] public section

/-!
# Live runs of a reduction's algorithm read off a table

* `liveRedRun_logLe_sph`: the log only grows along a live run of a reduction's algorithm.
* **The checking semantics** (`chkImpl T bad`): hash reads answered by the table `T` off the
  cells of `bad`; coins, challenger calls and reads of `bad` fail.
* `liveRedRun_of_chk`: a live run of an algorithm whose checking run succeeds, ending in a log
  that `T` extends, returns the checking run's value with the transcript kept, and keeps every
  invariant `Φ` kept by the reduction's reads off `bad`.
* `simulateQ_chkImpl_liftW`, `simulateQ_chkImplW_hashQ`, `simulateQ_chkImplW_hash`: the checking
  semantics of world programs and of the hash.
-/

open OracleComp OracleSpec

namespace Quantum.StdModel.Qrom.SphEnc

open Quantum.Qrom HashSig Common

variable {M : Type} {Q' : Type} {R' : OracleSpec.{0, 0} Q'}

/-- Every algorithm costs nothing under the zero cost. -/
theorem queryCostAtMost_zero_sphChk {ι : Type} {O : OracleSpec.{0, 0} ι} {α : Type}
    (oa : OracleComp O α) : QueryCostAtMost oa (fun _ ↦ 0) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih => exact (isWeightBound_query_bind_iff _ _ _ _).mpr ⟨le_rfl, ih⟩

/-- A reduction's live run from the dead mode stays dead. -/
theorem liveRedRun_none_sph (rl : M → HashDomain → Option HashOutput)
    (upd : Caller → HashDomain → M → Option HashOutput → M)
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q')) {α : Type}
    (oa : OracleComp (romWorld.Oracles + R') α) {log : QueryLog R'} {r : α × QueryLog R'}
    {μ' : Option M} (h : LiveRedRun rl upd ans oa log none r μ') : μ' = none :=
  liveRedRun_inv_cost upd rl ans (fun _ ↦ 0) (fun _ μ ↦ μ = none)
    (fun _ _ _ _ _ hμ ↦ by rw [hμ]; rfl) (fun _ _ _ _ _ _ hμ h' ↦ by
      rw [hμ] at h'
      exact liveRun_none_mode _ h') oa (queryCostAtMost_zero_sphChk oa) h rfl

/-- **The log only grows along a live run of a reduction's algorithm.** -/
theorem liveRedRun_logLe_sph (rl : M → HashDomain → Option HashOutput)
    (upd : Caller → HashDomain → M → Option HashOutput → M)
    (hupd : ∀ c z, RecordsAt rl z (upd c z))
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q')) {α : Type}
    (oa : OracleComp (romWorld.Oracles + R') α) {log : QueryLog R'} {m m' : M}
    {r : α × QueryLog R'} (h : LiveRedRun rl upd ans oa log (some m) r (some m')) :
    LiveDet.LogLe rl m m' := by
  refine liveRedRun_inv_cost upd rl ans (fun _ ↦ 0)
    (fun _ μ ↦ ∀ m₁, μ = some m₁ → LiveDet.LogLe rl m m₁) ?_ ?_ oa
    (queryCostAtMost_zero_sphChk oa) h ?_ m' rfl
  · intro z _ μ v _ hμ m₁ h₁
    rcases μ with _ | m₀
    · cases h₁
    · exact (hμ m₀ rfl).trans (LiveDet.logLe_stepRd (hupd .red z) h₁)
  · intro q' _ μ a μ' _ hμ hrun m₁ h₁
    subst h₁
    rcases μ with _ | m₀
    · exact absurd (liveRun_none_mode _ hrun) (Option.some_ne_none _)
    · exact (hμ m₀ rfl).trans (LiveDet.liveRun_logLe (fun z ↦ hupd .answer z) _ hrun)
  · intro m₁ h₁
    cases h₁
    exact LiveDet.LogLe.refl m

open scoped Classical in
/-- **The checking semantics**: hash reads answered by `T` off `bad`; coins, challenger calls and
reads of `bad` fail. -/
noncomputable def chkImpl (T : HashDomain → HashOutput) (bad : HashDomain → Prop) :
    QueryImpl (romWorld.Oracles + R') Option
  | .inl (.inl _) => none
  | .inl (.inr z) => if bad z then none else some (T z)
  | .inr _ => none

open scoped Classical in
/-- **The checking semantics of a world program**: hash reads answered by `T` off `bad`; coins
and reads of `bad` fail. -/
noncomputable def chkImplW (T : HashDomain → HashOutput) (bad : HashDomain → Prop) :
    QueryImpl romWorld.Oracles Option
  | .inl _ => none
  | .inr z => if bad z then none else some (T z)

open scoped Classical in
/-- The induction behind `liveRedRun_of_chk`, over the start of the run. -/
theorem liveRedRun_of_chk_aux (rl : M → HashDomain → Option HashOutput)
    (upd : Caller → HashDomain → M → Option HashOutput → M)
    (hupd : ∀ c z, RecordsAt rl z (upd c z))
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
    (T : HashDomain → HashOutput) (bad : HashDomain → Prop) (Φ : M → Prop)
    (hΦ : ∀ z m v, ¬ bad z → Φ m → Φ (upd .red z m (some v))) {α : Type}
    (oa : OracleComp (romWorld.Oracles + R') α) {m' : M} {r : α × QueryLog R'}
    (hT : ∀ z v, rl m' z = some v → T z = v) :
    ∀ {b : α} {log : QueryLog R'} {m : M}, simulateQ (chkImpl T bad) oa = some b →
      LiveRedRun rl upd ans oa log (some m) r (some m') → Φ m → r = (b, log) ∧ Φ m' := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro b log m hchk hrun hm
    unfold LiveRedRun at hrun
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hrun
    obtain ⟨h1, h2, h3⟩ := hrun
    cases h3
    have hx : x = b := Option.some.inj hchk
    exact ⟨Prod.ext (h1.trans hx) h2, hm⟩
  | query_bind t k ih =>
    intro b log m hchk hrun hm
    unfold LiveRedRun at hrun
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hrun
    obtain ⟨⟨y, log₁, μ₁⟩, h₁, h₂⟩ := hrun
    rw [simulateQ_bind, simulateQ_spec_query] at hchk
    rcases t with (n | z) | q'
    · exact absurd hchk (Option.some_ne_none b).symm
    · change (y, log₁, μ₁) ∈ support ((fun p ↦ (p.1, (log, p.2))) <$>
        (liveImpl rl (upd .red) (.inr z)).run (some m)) at h₁
      rw [support_map] at h₁
      obtain ⟨⟨y', μ₂⟩, h₃, he⟩ := h₁
      simp only [Prod.mk.injEq] at he
      obtain ⟨hy, rfl, rfl⟩ := he
      subst y'
      rw [eq_stepRd_of_mem_support h₃] at h₂
      rcases hst : stepRd rl (upd .red z) z (some m) y with _ | m₁
      · rw [hst] at h₂
        exact absurd (liveRedRun_none_sph rl upd ans _ h₂) (Option.some_ne_none _)
      rw [hst] at h₂
      have hy : rl m₁ z = some y := LiveDet.rl_stepRd_self (hupd .red z) hst
      have hTz : T z = y := hT z y (liveRedRun_logLe_sph rl upd hupd ans _ h₂ z y hy)
      have hb : ¬ bad z := by
        intro hb
        refine absurd hchk ?_
        change ¬ (if bad z then none else some (T z)) >>= _ = some b
        rw [ite_eq_left hb]
        exact (Option.some_ne_none b).symm
      change (if bad z then none else some (T z)) >>= _ = some b at hchk
      rw [ite_eq_right hb, hTz] at hchk
      obtain ⟨rfl, -⟩ := stepRd_some hst
      exact ih y hchk h₂ (hΦ z m y hb hm)
    · exact absurd hchk (Option.some_ne_none b).symm

/-- **A live run read off a table**: a live run of an algorithm whose checking run returns `b`,
ending in a log that `T` extends, returns `b` with the transcript kept, and keeps every invariant
`Φ` kept by the reduction's reads off `bad`. -/
theorem liveRedRun_of_chk (rl : M → HashDomain → Option HashOutput)
    (upd : Caller → HashDomain → M → Option HashOutput → M)
    (hupd : ∀ c z, RecordsAt rl z (upd c z))
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
    (T : HashDomain → HashOutput) (bad : HashDomain → Prop) (Φ : M → Prop)
    (hΦ : ∀ z m v, ¬ bad z → Φ m → Φ (upd .red z m (some v))) {α : Type}
    (oa : OracleComp (romWorld.Oracles + R') α) {b : α}
    (hchk : simulateQ (chkImpl T bad) oa = some b) {log : QueryLog R'} {m m' : M}
    {r : α × QueryLog R'} (hrun : LiveRedRun rl upd ans oa log (some m) r (some m'))
    (hT : ∀ z v, rl m' z = some v → T z = v) (hm : Φ m) : r = (b, log) ∧ Φ m' :=
  liveRedRun_of_chk_aux rl upd hupd ans T bad Φ hΦ oa hT hchk hrun hm

/-- **The checking semantics of a world program** in a reduction is its own. -/
theorem simulateQ_chkImpl_liftW (T : HashDomain → HashOutput) (bad : HashDomain → Prop)
    {α : Type} (oa : OracleComp romWorld.Oracles α) :
    simulateQ (chkImpl (R' := R') T bad) (Quantum.StdModel.Sphincs.liftW R' oa) =
      simulateQ (chkImplW T bad) oa := by
  unfold Quantum.StdModel.Sphincs.liftW
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, ih]
    rcases t with n | z <;> rfl

open scoped Classical in
/-- **The checking semantics of the hash**: the table off `bad` at the code of the input. -/
theorem simulateQ_chkImplW_hashQ (T : HashDomain → HashOutput) (bad : HashDomain → Prop)
    (l : HashInput) :
    simulateQ (chkImplW T bad) (Quantum.Qrom.hashQ l) =
      (encodeInput l).elim (some 0) (fun x ↦ if bad x then none else some (T x)) := by
  unfold Quantum.Qrom.hashQ
  rcases encodeInput l with _ | x
  · rfl
  · exact simulateQ_spec_query (chkImplW T bad) (.inr x : romWorld.Oracles.Domain)

open scoped Classical in
/-- **The checking semantics of the world's hash.** -/
theorem simulateQ_chkImplW_hash (T : HashDomain → HashOutput) (bad : HashDomain → Prop)
    (l : HashInput) :
    simulateQ (chkImplW T bad) (romWorld.hash l) =
      (encodeInput l).elim (some 0) (fun x ↦ if bad x then none else some (T x)) :=
  simulateQ_chkImplW_hashQ T bad l

end Quantum.StdModel.Qrom.SphEnc

end
