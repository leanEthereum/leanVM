module

public import Quantum.StdModel.Qrom.EncSaltAmort

@[expose] public section

/-!
# EncTCR$: the challenger's trial reads with a log-aware read count

`EncSaltAmort.totalWeight_saltProg_le` counts the reduction's reads of encoding cells statically
(`costR`). A read of a cell in the class of a tweak already in the transcript does not raise the
potential `potK (Yset e P (twOf log))` (that class has left `Yset`), so it need not be counted.

* `FreshRdWP e P oa log n Post`: along every path of `oa` from the transcript `log`, every
  challenger's query is at a tweak not in the transcript, the reads of encoding cells in no class
  (at `P`) of a tweak of the current transcript number at most `n`, and `Post` holds at the end
  (of the result, the transcript and the remaining budget).
* `potB_redImpl_rd`, `potB_mixRun_rd`, `totalWeight_saltProg_rd_le`: the bounds of
  `EncSaltAmort` with these budgets.
-/

open IPFunctor Matrix
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.StdModel.Qrom.EncSalt.LogCost

open Quantum QuantumRuntime Quantum.Sponge Quantum.Qrom HashSig Props OracleComp OracleSpec Common
open Quantum.Xmss.Hybrid (runtime2 runtime2_branch)
open Tcr (Mem IsG GCell GSep uRed uJudge BadR)

/-! ### The log-aware read budget -/

section wp

variable {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig) (P : Par)

/-- One step of the log-aware read budget: a query of the model costs its hit of the encoding
cells in no class of a tweak of the transcript, a challenger's query is at a fresh tweak and
extends the transcript. -/
noncomputable def freshRdStep :
    (t : (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))).Domain) →
    ((romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))).Range t →
      SLog Tw Msg Salt Dig → ℕ → Prop) → SLog Tw Msg Salt Dig → ℕ → Prop
  | .inl i, k, log, n => hitY (Yset e P (twOf log)) i ≤ n ∧
      ∀ y, k y log (n - hitY (Yset e P (twOf log)) i)
  | .inr q, k, log, n => q.1 ∉ twOf log ∧ ∀ y, k y (log ++ [⟨q, y⟩]) n

/-- **Fresh tweaks and a log-aware read budget**: along every path of `oa` from the transcript
`log` with budget `n`, every challenger's query is at a tweak not in the transcript, every read of
an encoding cell in no class (at `P`) of a tweak of the current transcript spends one unit of the
budget, which never runs out, and `Post` holds at the end of the result, the transcript and the
remaining budget. -/
noncomputable def FreshRdWP {α : Type}
    (oa : OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) α)
    (log : SLog Tw Msg Salt Dig) (n : ℕ) (Post : α → SLog Tw Msg Salt Dig → ℕ → Prop) : Prop :=
  PFunctor.FreeM.rec (P := (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))).toPFunctor)
    (motive := fun _ ↦ SLog Tw Msg Salt Dig → ℕ → Prop) (fun a log n ↦ Post a log n)
    (fun t _ ih log n ↦ freshRdStep e P t ih log n) oa log n

theorem freshRdWP_pure {α : Type} (a : α) (log : SLog Tw Msg Salt Dig) (n : ℕ)
    (Post : α → SLog Tw Msg Salt Dig → ℕ → Prop) :
    FreshRdWP e P (pure a : OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) α)
      log n Post ↔ Post a log n :=
  Iff.rfl

theorem freshRdWP_query_bind {α : Type}
    (t : (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))).Domain)
    (k : (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))).Range t →
      OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) α)
    (log : SLog Tw Msg Salt Dig) (n : ℕ) (Post : α → SLog Tw Msg Salt Dig → ℕ → Prop) :
    FreshRdWP e P (liftM ((romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))).query t) >>= k)
      log n Post ↔ freshRdStep e P t (fun y log' n' ↦ FreshRdWP e P (k y) log' n' Post) log n :=
  Iff.rfl

/-- **Sequencing**: the precondition of a bind is that of the first part with the precondition
of the continuation as its postcondition. -/
theorem freshRdWP_bind {α β : Type}
    (oa : OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) α)
    (f : α → OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) β)
    (Post : β → SLog Tw Msg Salt Dig → ℕ → Prop) :
    ∀ (log : SLog Tw Msg Salt Dig) (n : ℕ), FreshRdWP e P (oa >>= f) log n Post ↔
      FreshRdWP e P oa log n fun a log' n' ↦ FreshRdWP e P (f a) log' n' Post := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro log n
    rw [pure_bind]
    exact Iff.rfl
  | query_bind t k ih =>
    intro log n
    rw [bind_assoc, freshRdWP_query_bind, freshRdWP_query_bind]
    rcases t with i | q
    · exact and_congr Iff.rfl (forall_congr' fun y ↦ ih y _ _)
    · exact and_congr Iff.rfl (forall_congr' fun y ↦ ih y _ _)

/-- **Monotonicity**: a larger budget and a weaker postcondition (shifted by the extra budget). -/
theorem freshRdWP_mono {α : Type}
    (oa : OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) α) (d : ℕ)
    {Post Post' : α → SLog Tw Msg Salt Dig → ℕ → Prop}
    (h : ∀ a log k, Post a log k → Post' a log (k + d)) :
    ∀ (log : SLog Tw Msg Salt Dig) (n : ℕ), FreshRdWP e P oa log n Post →
      FreshRdWP e P oa log (n + d) Post' := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun log n hp ↦ h a log n hp
  | query_bind t k ih =>
    intro log n hf
    rw [freshRdWP_query_bind] at hf ⊢
    rcases t with i | q
    · obtain ⟨h1, h2⟩ := (hf : hitY (Yset e P (twOf log)) i ≤ n ∧
        ∀ y, FreshRdWP e P (k y) log (n - hitY (Yset e P (twOf log)) i) Post)
      refine ⟨h1.trans (Nat.le_add_right _ _), fun y ↦ ?_⟩
      have h3 := ih y log _ (h2 y)
      rw [Nat.sub_add_comm h1]
      exact h3
    · obtain ⟨h1, h2⟩ := (hf : q.1 ∉ twOf log ∧
        ∀ y, FreshRdWP e P (k y) (log ++ [⟨q, y⟩]) n Post)
      exact ⟨h1, fun y ↦ ih y _ _ (h2 y)⟩

/-- A query of the model hits the encoding cells of `Yset` at most as it reads encoding cells. -/
theorem hitY_Yset_le_costR (U : Set Tw) (i : romWorld.Oracles.Domain) :
    hitY (Yset e P U) i ≤ costR e (.inl i) := by
  rcases i with c | z
  · exact le_rfl
  · simp only [hitY, costR]
    split_ifs with h1 h2 <;> first | omega | exact absurd h1.1 h2

/-- A read of a cell of the class of a tweak of `U` does not hit `Yset`. -/
theorem hitY_Yset_of_gCell (U : Set Tw) (z : HashDomain) (t : Tw) (hz : GCell e.hash G z P t)
    (ht : t ∈ U) : hitY (Yset e P U) (.inr z) = 0 := by
  simp only [hitY]
  split_ifs with h
  · exact absurd hz (h.2 t ht)
  · rfl

/-- **The static count suffices**: fresh tweaks and at most `n` reads of encoding cells. -/
theorem freshRdWP_of_freshWP {α : Type}
    (oa : OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) α)
    (Post : α → SLog Tw Msg Salt Dig → Prop) :
    ∀ (log : SLog Tw Msg Salt Dig) (n : ℕ), QueryCostAtMost oa (costR e) n →
      FreshWP oa log Post → FreshRdWP e P oa log n fun a log' _ ↦ Post a log' := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun _ _ _ h ↦ h
  | query_bind t k ih =>
    intro log n hn hf
    rw [isWeightBound_query_bind_iff] at hn
    rw [freshWP_query_bind] at hf
    rw [freshRdWP_query_bind]
    rcases t with i | q
    · have hY := hitY_Yset_le_costR e P (twOf log) i
      have hf' : ∀ y, FreshWP (k y) log Post := hf
      refine ⟨hY.trans hn.1, fun y ↦ ?_⟩
      have h3 := freshRdWP_mono e P (k y) (costR e (.inl i) - hitY (Yset e P (twOf log)) i)
        (Post := fun a log' _ ↦ Post a log') (Post' := fun a log' _ ↦ Post a log')
        (fun _ _ _ h ↦ h) log _ (ih y log _ (hn.2 y) (hf' y))
      have he : n - costR e (.inl i) + (costR e (.inl i) - hitY (Yset e P (twOf log)) i) =
          n - hitY (Yset e P (twOf log)) i := by
        have := hn.1
        omega
      rw [he] at h3
      exact h3
    · obtain ⟨hq, hf'⟩ := (hf : q.1 ∉ twOf log ∧ ∀ y, FreshWP (k y) (log ++ [⟨q, y⟩]) Post)
      have hc : costR e (.inr q :
          (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))).Domain) = 0 := rfl
      refine ⟨hq, fun y ↦ ?_⟩
      have hn2 := hn.2 y
      rw [hc, Nat.sub_zero] at hn2
      exact ih y _ n hn2 (hf' y)

end wp

/-! ### The reduction's algorithms -/

section red

variable {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig)

/-- **The reduction's algorithm by log-aware reads**, the challenger answering fresh tweaks:
within the log-aware budget `n` and `m` answers, the weight is paid by the count of the encoding
cells of the unanswered classes, raised by `lam` per budgeted read, plus `c₀` per answer. -/
theorem potB_redImpl_rd [SampleableType Par] [SampleableType Salt] (P : Par) (lam c₀ : ℝ≥0∞)
    (B : QReg)
    (hblk : ∀ (q : Tw × Msg) (U : Set Tw), q.1 ∉ U →
      PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam
        (readProgOf (upd e) (((encTcrSalt romWorld e).answer P q).toQuantumAt
          (mixImpl .answer B)))
        (potK (Yset e P U)) (fun _ ↦ potK (Yset e P (insert q.1 U))) c₀ (fun _ ↦ True))
    {α : Type} (oa : OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) α) :
    ∀ (log : SLog Tw Msg Salt Dig) (n m : ℕ) (Post : α → SLog Tw Msg Salt Dig → Prop),
      QueryCostAtMost oa (costA Tw Msg Salt Dig) m →
      FreshRdWP e P oa log n (fun a log' _ ↦ Post a log') →
      PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam
        (readProgOf (upd e) ((simulateQ (redImpl ((encTcrSalt romWorld e).answer P) B) oa).run
          log))
        (potK (Yset e P (twOf log))) (fun p ↦ potK (Yset e P (twOf p.2.2.2)))
        (n * lam + m * c₀) (fun p ↦ Post p.2.2.1 p.2.2.2) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro log n m Post _ hf
    rw [simulateQ_pure, StateT.run_pure]
    have h := potB_pure₂ (R := runtime2 HashOutput HashDomain mem0)
      (I := LocalSig.Interp.instruments) (w := dS e) (P := Hw0) (lam := lam)
      (L := LocalSig.instruments.{0}) (spec := hwSpec HashOutput HashDomain Mem) (A := B)
      (a, log) (potK (Yset e P (twOf log))) (fun v ↦ potK (Yset e P (twOf v.2))) rfl
      (fun v ↦ Post v.1 v.2) hf
    have h' := h.mono (c' := n * lam + m * c₀) zero_le (fun _ _ _ ↦ le_rfl) fun _ h ↦ h
    exact h'
  | query_bind t k ih =>
    intro log n m Post hm hf
    rw [isWeightBound_query_bind_iff] at hm
    rw [freshRdWP_query_bind] at hf
    rcases t with i | q'
    · obtain ⟨hn1, hf'⟩ := (hf : hitY (Yset e P (twOf log)) i ≤ n ∧
        ∀ y, FreshRdWP e P (k y) log (n - hitY (Yset e P (twOf log)) i)
          fun a log' _ ↦ Post a log')
      rw [run_simulateQ_redImpl_inl, readProgOf_bind₂]
      have hx := potB_readProgOf (upd e) (dS e) badS (fun _ h ↦ badR_eq_zero_of_badS h)
        (fun _ σ h ↦ dS_eq_zero_of_badS e h σ) (fun _ ↦ rfl) lam (Yset e P (twOf log))
        (mixImpl .red B i) (hitY (Yset e P (twOf log)) i)
        (isChargeBound_kmB_mixImpl (upd e) badS .red (fun z ↦ by simp [badS, upd]) B i)
        ((isChargeBound_mixImpl_cost (kmY _) .red B i).mono (by
          rcases i with c | z
          · exact le_rfl
          · exact le_rfl))
      refine (potB_bind_dS e (Ψ := fun _ ↦ potK (Yset e P (twOf log)))
        (Lf := fun _ ↦ True) hx fun a _ ↦ ih a log _ _ Post (hm.2 a) (hf' a)).mono
        (le_of_eq ?_) (fun _ _ _ ↦ le_rfl) fun _ h ↦ h
      have hc : costA Tw Msg Salt Dig (.inl i) = 0 := rfl
      rw [hc, Nat.sub_zero, ← add_assoc, natCast_mul_add_le _ _ hn1]
    · obtain ⟨hq, hf'⟩ := (hf : q'.1 ∉ twOf log ∧
        ∀ y, FreshRdWP e P (k y) (log ++ [⟨q', y⟩]) n fun a log' _ ↦ Post a log')
      rw [run_simulateQ_redImpl_inr, readProgOf_bind₂]
      have hm1 : 1 ≤ m := hm.1
      refine (potB_bind_dS e
        (Ψ := fun _ ↦ potK (Yset e P (insert q'.1 (twOf log)))) (Lf := fun _ ↦ True)
        (c₂ := (n : ℝ≥0∞) * lam + (m - costA Tw Msg Salt Dig (.inr q') : ℕ) * c₀)
        (hblk q' (twOf log) hq) fun a _ ↦ ?_).mono ?_ (fun _ _ _ ↦ le_rfl) fun _ h ↦ h
      · have h := ih a (log ++ [⟨q', a⟩]) _ _ Post (hm.2 a) (hf' a)
        rwa [twOf_append] at h
      · have hc' : costA Tw Msg Salt Dig (.inr q') = 1 := rfl
        rw [hc']
        have h1 : (m : ℝ≥0∞) = ((m - 1 : ℕ) : ℝ≥0∞) + 1 := by
          exact_mod_cast (Nat.sub_add_cancel hm1).symm
        rw [h1]
        exact le_of_eq (by ring)

end red

/-! ### The adversary's run against the reduction's handler -/

section adv

variable {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig)

/-- **The adversary's run against the reduction's handler, by log-aware reads**: each hash call
of the adversary raises the count by `lam`, each of its classical calls runs the handler, within
the log-aware budget `nσ` and `mσ` fresh answers, under an invariant `J` of the handler's state
and the transcript. -/
theorem potB_mixRun_rd [SampleableType Par] [SampleableType Salt] {Q : Type}
    {R : OracleSpec.{0, 0} Q} {St : Type} (P : Par) (lam c₀ : ℝ≥0∞)
    (hblk : ∀ (B : QReg) (q : Tw × Msg) (U : Set Tw), q.1 ∉ U →
      PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam
        (readProgOf (upd e) (((encTcrSalt romWorld e).answer P q).toQuantumAt
          (mixImpl .answer B)))
        (potK (Yset e P U)) (fun _ ↦ potK (Yset e P (insert q.1 U))) c₀ (fun _ ↦ True))
    (σ : HHandler romWorld R (Tw × Msg →ₒ Option (Salt × Dig)) St)
    (J : St → SLog Tw Msg Salt Dig → Prop) (nσ mσ : ℕ)
    (hσm : ∀ st qq, QueryCostAtMost (σ st qq) (costA Tw Msg Salt Dig) mσ)
    (hσf : ∀ st qq log, J st log → FreshRdWP e P (σ st qq) log nσ fun r log' _ ↦ J r.2 log')
    {X Y : QReg → Type} (leaf : ∀ u, X u → St × SLog Tw Msg Salt Dig → Y u)
    (Ψ : (Σ u, Y u) →
      Matrix (HwReg HashOutput HashDomain Mem) (HwReg HashOutput HashDomain Mem) ℂ)
    (Lf : (Σ u, Y u) → Prop)
    (hleaf : ∀ u y st log, J st log →
      Ψ ⟨u, leaf u y (st, log)⟩ = potK (Yset e P (twOf log)) ∧ Lf ⟨u, leaf u y (st, log)⟩)
    {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X A) :
    ∀ (st : St) (log : SLog Tw Msg Salt Dig) (q k : ℕ), J st log →
      IFreeM.IsChargeBound x (cmdCharge hashCharge) q →
      IFreeM.IsChargeBound x (cmdCharge callCharge) k →
      PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam
        (readProgOf (upd e) (mixRun (mixTrees ((encTcrSalt romWorld e).answer P) σ) leaf x
          (st, log)))
        (potK (Yset e P (twOf log))) Ψ (q * lam + k * (nσ * lam + mσ * c₀)) Lf := by
  have hS : ∀ {Ω : QReg → Type} {B : QReg}
      (y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) Ω B)
      (n : ℕ) (U : Set HashDomain),
      IFreeM.IsChargeBound y (cmdCharge (kmB (upd e) badS)) 0 →
      IFreeM.IsChargeBound y (cmdCharge (kmY U)) n →
      PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam (readProgOf (upd e) y)
        (potK U) (fun _ ↦ potK U) (n * lam) (fun _ ↦ True) := fun y n U h1 h2 ↦
    potB_readProgOf (upd e) (dS e) badS (fun _ h ↦ badR_eq_zero_of_badS h)
      (fun _ σ h ↦ dS_eq_zero_of_badS e h σ) (fun _ ↦ rfl) lam U y n h1 h2
  induction x using IFreeM.inductionOn with
  | pure _ y =>
    intro st log q k hJ _ _
    obtain ⟨hΨ, hL⟩ := hleaf _ y st log hJ
    have h := potB_pure (R := runtime2 HashOutput HashDomain mem0)
      (I := LocalSig.Interp.instruments) (w := dS e) (P := Hw0) (lam := lam)
      (L := LocalSig.instruments.{0}) (spec := hwSpec HashOutput HashDomain Mem)
      (leaf _ y (st, log)) _ Ψ hΨ Lf hL
    have h' := h.mono (c' := q * lam + k * (nσ * lam + mσ * c₀)) zero_le
      (fun _ _ _ ↦ le_rfl) fun _ h ↦ h
    exact h'
  | liftBind A cmd next ih =>
    intro st log q k hJ hq hk
    replace hq := (IFreeM.isChargeBound_liftBind_iff _ _ _).mp hq
    replace hk := (IFreeM.isChargeBound_liftBind_iff _ _ _).mp hk
    rcases cmd with o | ⟨p | qq, E, ℓ⟩
    · refine PotB.of_eq ((congrArg (readProgOf (upd e))
        (mixRun_prim (mixTrees ((encTcrSalt romWorld e).answer P) σ) leaf o next
          (st, log))).trans (readProgOf_bind _ _ _)) ?_
      have h0 := potB_readProgOf (upd e) (dS e) badS (fun _ h ↦ badR_eq_zero_of_badS h)
        (fun _ σ h ↦ dS_eq_zero_of_badS e h σ) (fun _ ↦ rfl) lam (Yset e P (twOf log))
        (cmd1 (.prim o)) 0 (isChargeBound_cmd1 _ _ le_rfl) (isChargeBound_cmd1 _ _ le_rfl)
      refine (potB_bindG_dS e (c₂ := q * lam + k * (nσ * lam + mσ * c₀)) h0
        fun p _ ↦ ?_).mono (le_of_eq (by simp)) (fun _ _ _ ↦ le_rfl) fun _ h ↦ h
      obtain ⟨t, b, rfl⟩ := p
      exact ih b st log q k hJ (hq.2 b) (hk.2 b)
    · refine PotB.of_eq ((congrArg (readProgOf (upd e))
        (mixRun_hash (mixTrees ((encTcrSalt romWorld e).answer P) σ) leaf p E ℓ next
          (st, log))).trans (readProgOf_bind _ _ _)) ?_
      have hq1 : 1 ≤ q := hq.1
      have h0 := potB_readProgOf (upd e) (dS e) badS (fun _ h ↦ badR_eq_zero_of_badS h)
        (fun _ σ h ↦ dS_eq_zero_of_badS e h σ) (fun _ ↦ rfl) lam (Yset e P (twOf log))
        (cmd1 (.query (.hash p) E ℓ)) 1 (isChargeBound_cmd1 _ _ (Nat.zero_le _))
        (isChargeBound_cmd1 _ _ le_rfl)
      refine (potB_bindG_dS e (c₂ := (q - 1 : ℕ) * lam + k * (nσ * lam + mσ * c₀)) h0
        fun p _ ↦ ?_).mono (le_of_eq ?_) (fun _ _ _ ↦ le_rfl) fun _ h ↦ h
      · obtain ⟨t, b, rfl⟩ := p
        exact ih b st log (q - 1) k hJ (hq.2 b) (hk.2 b)
      · rw [natCast_eq_sub_one_add q hq1]
        ring
    · have hk1 : 1 ≤ k := hk.1
      have hT : PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam
          (readProgOf (upd e) (mixTrees ((encTcrSalt romWorld e).answer P) σ (st, log) qq E ℓ))
          (potK (Yset e P (twOf log))) (fun p ↦ potK (Yset e P (twOf p.2.2.2.2)))
          (((0 : ℕ) : ℝ≥0∞) * lam + ((nσ * lam + mσ * c₀) + 0))
          (fun p ↦ J p.2.2.2.1 p.2.2.2.2) := by
        rw [mixTrees_apply, readProgOf_bind₂]
        refine potB_bind_dS e (Ψ := fun _ ↦ potK (Yset e P (twOf log))) (Lf := fun _ ↦ True)
          (hS _ 0 _ (isChargeBound_act _ _ 0) (isChargeBound_act _ _ 0)) fun _ _ ↦ ?_
        rw [QuantumComp₂.map_eq_bind_pure, readProgOf_bind₂]
        have hr := potB_redImpl_rd e P lam c₀
          (QReg.of ((advSpec romWorld.spec R).Out (.call qq) × E)) (hblk _) (σ st qq) log nσ mσ
          (fun r log' ↦ J r.2 log') (hσm st qq) (hσf st qq log hJ)
        generalize hX : readProgOf (upd e) ((simulateQ (redImpl ((encTcrSalt romWorld e).answer P)
          (QReg.of ((advSpec romWorld.spec R).Out (.call qq) × E))) (σ st qq)).run log) = X at hr ⊢
        refine potB_bind_dS' e hr fun v hv ↦ ?_
        refine PotB.of_eq (readProgOf_pure (upd e) (Ω := QuantumComp₂.Leaf _ _)
          ⟨rfl, (v.1.1, (v.1.2, v.2))⟩) ?_
        exact potB_pure _ _ _ rfl _ hv
      refine PotB.of_eq ((congrArg (readProgOf (upd e))
        (mixRun_call (mixTrees ((encTcrSalt romWorld e).answer P) σ) leaf qq E ℓ next
          (st, log))).trans (readProgOf_bind _ _ _)) ?_
      refine (potB_bindG_dS e (c₂ := q * lam + (k - 1 : ℕ) * (nσ * lam + mσ * c₀)) hT
        fun p hp ↦ ?_).mono (le_of_eq ?_) (fun _ _ _ ↦ le_rfl) fun _ h ↦ h
      · obtain ⟨u, rfl, v⟩ := p
        exact ih ⟨v.1⟩ v.2.1 v.2.2 q (k - 1) hp (hq.2 _) (hk.2 _)
      · rw [natCast_eq_sub_one_add k hk1]
        ring

end adv

/-! ### The game -/

section game

variable {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig)

/-- **The total weight of the challenger's trial reads in the EncTCR$ game, by log-aware reads.**
Let the weight of each answer block be at most `ℓ` (`AnsBound`), with
`ℓ P q ≤ lam · (recorded cells of the class of q.1 at P) + c₀`. Let the adversary make at most
`q` hash calls and `kA` classical calls; let the reduction's setup, handler and output read at
most `n₁`, `nσ`, `n₂` encoding cells in no class of a tweak already in the transcript, and make
at most `m₁`, `mσ`, `m₂` challenger queries, each at a fresh tweak (`FreshRdWP`, with an
invariant `J` of the handler's state and the transcript). Then
`TW ≤ lam (n₁ + q + kA nσ + n₂) + c₀ (m₁ + kA mσ + m₂)`. -/
theorem totalWeight_saltProg_rd_le [SampleableType Par] [SampleableType Salt]
    (hs : GSep e.hash G) (ℓ : Par → Tw × Msg → HwReg HashOutput HashDomain Mem → ℝ)
    (hA : AnsBound e ℓ) (lamR c₀R : ℝ) (hlam : 0 ≤ lamR) (hc₀ : 0 ≤ c₀R)
    (hℓ : ∀ P q s, ℓ P q s ≤ lamR * cntY (Kset e P q.1) s + c₀R)
    {Q : Type} {R : OracleSpec.{0, 0} Q} {St S0 Fo : Type}
    (pre : Par → OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) S0)
    (adv : Par → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) Fo)
    (st0 : Par → S0 → St) (σ : Par → HHandler romWorld R (Tw × Msg →ₒ Option (Salt × Dig)) St)
    (post : Par → S0 → Fo → St →
      OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) (Tw × Msg × Salt))
    {q kA : ℕ} (hadv : ∀ p a, IFreeM.IsChargeBound (adv p a) (cmdCharge hashCharge) q)
    (hadvC : ∀ p a, IFreeM.IsChargeBound (adv p a) (cmdCharge callCharge) kA)
    {n₁ m₁ nσ mσ n₂ m₂ : ℕ}
    (hpreM : ∀ P, QueryCostAtMost (pre P) (costA Tw Msg Salt Dig) m₁)
    (hσM : ∀ P st qq, QueryCostAtMost (σ P st qq) (costA Tw Msg Salt Dig) mσ)
    (hpostM : ∀ P a f st, QueryCostAtMost (post P a f st) (costA Tw Msg Salt Dig) m₂)
    (J : Par → St → SLog Tw Msg Salt Dig → Prop)
    (hpreF : ∀ P, FreshRdWP e P (pre P) [] n₁ fun a log _ ↦ J P (st0 P a) log)
    (hσF : ∀ P st qq log, J P st log →
      FreshRdWP e P (σ P st qq) log nσ fun r log' _ ↦ J P r.2 log')
    (hpostF : ∀ P a f st log, J P st log →
      FreshRdWP e P (post P a f st) log n₂ fun _ _ _ ↦ True) :
    (runtime2 HashOutput HashDomain mem0).totalWeight .instruments (dS e)
        (saltProg e pre adv st0 σ post) (rhoMem0 mem0) ≤
      ENNReal.ofReal lamR * (n₁ + q + kA * nσ + n₂ : ℕ) +
        ENNReal.ofReal c₀R * (m₁ + kA * mσ + m₂ : ℕ) := by
  set lam := ENNReal.ofReal lamR
  set c₀ := ENNReal.ofReal c₀R
  have hblk : ∀ (P : Par) (B : QReg) (qq : Tw × Msg) (U : Set Tw), qq.1 ∉ U →
      PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam
        (readProgOf (upd e) (((encTcrSalt romWorld e).answer P qq).toQuantumAt
          (mixImpl .answer B)))
        (potK (Yset e P U)) (fun _ ↦ potK (Yset e P (insert qq.1 U))) c₀ (fun _ ↦ True) :=
    fun P B qq U hU ↦ potB_answer e hs ℓ hA lamR c₀R hlam hc₀ hℓ P qq B U hU
  have hle0 : ∀ (Y : Set HashDomain) {B : QReg}
      (τ : Matrix (B × HwReg HashOutput HashDomain Mem) (B × HwReg HashOutput HashDomain Mem) ℂ),
      τ.PosSemidef → potential (potK ∅) τ ≤ potential (potK Y) τ := fun Y _ τ hτ ↦
    potential_diagPot_mono (cntY_nonneg _) (fun s ↦ cntY_mono (Set.empty_subset Y) s) hτ
  have hgame : PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam
      (saltProg e pre adv st0 σ post) (potK (Gset e)) (fun _ ↦ potK ∅)
      (((0 : ℕ) : ℝ≥0∞) * lam + ((n₁ * lam + m₁ * c₀ + (q * lam + kA * (nσ * lam + mσ * c₀) +
        (n₂ * lam + m₂ * c₀))) + ((0 : ℕ) : ℝ≥0∞) * lam)) (fun _ ↦ True) := by
    show PotB _ _ _ _ _ (readProgOf (upd e) (mixGame (encTcrSalt romWorld e) pre adv st0 σ post))
      _ _ _ _
    unfold mixGame
    rw [readProgOf_bind₂]
    refine potB_bind_dS e (Ψ := fun _ ↦ potK (Gset e)) (Lf := fun _ ↦ True)
      (potB_toQuantumAt e .setup (dS e) badS (fun _ h ↦ badR_eq_zero_of_badS h)
        (fun _ σ h ↦ dS_eq_zero_of_badS e h σ) (fun _ ↦ rfl) (fun z ↦ by simp [badS, upd]) lam
        (Gset e) _ (encTcrSalt romWorld e).setup 0
        (by exact isWeightBound_liftM_probComp (hitY (Gset e)) (fun _ ↦ rfl) ($ᵗ Par)))
        fun P _ ↦ ?_
    rw [readProgOf_bind₂]
    refine potB_bind_dS e (Ψ := fun _ ↦ potK ∅) (Lf := fun _ ↦ True) ?_ fun r _ ↦ ?_
    · rw [← Yset_empty e P]
      unfold mixNormal
      rw [readProgOf_bind₂]
      have hpre := potB_redImpl_rd e P lam c₀ (QReg.of Unit) (hblk P _)
        (pre ((encTcrSalt romWorld e).pub P)) [] n₁ m₁
        (fun a log ↦ J P (st0 ((encTcrSalt romWorld e).pub P) a) log) (hpreM P) (hpreF P)
      rw [twOf_nil] at hpre
      generalize readProgOf (upd e) ((simulateQ (redImpl ((encTcrSalt romWorld e).answer P)
        (QReg.of Unit)) (pre ((encTcrSalt romWorld e).pub P))).run []) = X at hpre ⊢
      refine potB_bind_dS' e hpre fun p hp ↦ ?_
      rw [readProgOf_bind₂]
      unfold mixRunL
      refine potB_bind_dS' e (potB_mixRun_rd e P lam c₀ (hblk P)
        (σ ((encTcrSalt romWorld e).pub P)) (J P) nσ mσ (hσM P) (hσF P)
        (Y := QuantumComp₂.Leaf (QReg.of Unit)
          ((Fo × St) × QueryLog (Tw × Msg →ₒ Option (Salt × Dig))))
        (fun _ l q ↦ ⟨l.1, ((l.2, q.1), q.2)⟩)
        (fun p ↦ potK (Yset e P (twOf p.2.2.2))) (fun p ↦ J P p.2.2.1.2 p.2.2.2)
        (fun _ _ _ _ hJ ↦ ⟨rfl, hJ⟩) (adv ((encTcrSalt romWorld e).pub P) p.1)
        (st0 ((encTcrSalt romWorld e).pub P) p.1) p.2 q kA hp (hadv P p.1) (hadvC P p.1))
        fun r hr ↦ ?_
      have hpost := potB_redImpl_rd e P lam c₀ (QReg.of Unit) (hblk P _)
        (post ((encTcrSalt romWorld e).pub P) p.1 r.1.1 r.1.2) r.2 n₂ m₂
        (fun _ _ ↦ True) (hpostM P p.1 r.1.1 r.1.2) (hpostF P p.1 r.1.1 r.1.2 r.2 hr)
      generalize readProgOf (upd e) ((simulateQ (redImpl ((encTcrSalt romWorld e).answer P)
        (QReg.of Unit)) (post ((encTcrSalt romWorld e).pub P) p.1 r.1.1 r.1.2)).run r.2) = Z
        at hpost ⊢
      exact hpost.mono le_rfl (fun _ τ hτ ↦ hle0 _ τ hτ) fun _ _ ↦ trivial
    · refine potB_toQuantumAt e .judge (dS e) badS (fun _ h ↦ badR_eq_zero_of_badS h)
        (fun _ σ h ↦ dS_eq_zero_of_badS e h σ) (fun _ ↦ rfl) (fun z ↦ by simp [badS, upd]) lam
        ∅ _ ((encTcrSalt romWorld e).judge P r.2 r.1) 0
        ((queryCostAtMost_zero _).mono_weight fun t ↦ ?_)
      rcases t with k | z
      · exact le_rfl
      · simp only [hitY]
        split_ifs with h
        · exact h.elim
        · exact le_rfl
  have hρ : (rhoMem0 mem0 : Matrix (QReg.of Unit × RomReg HashDomain HashOutput Mem)
      (QReg.of Unit × RomReg HashDomain HashOutput Mem) ℂ).PosSemidef :=
    ((SubState.basis ()).prod (runtime2 HashOutput HashDomain mem0).init).posSemidef
  have htr : ENNReal.ofReal (rhoMem0 mem0 :
      Matrix (QReg.of Unit × RomReg HashDomain HashOutput Mem)
      (QReg.of Unit × RomReg HashDomain HashOutput Mem) ℂ).trace.re ≤ 1 := by
    change ENNReal.ofReal ((SubState.basis ()).matrix ⊗ₖ
      (runtime2 HashOutput HashDomain mem0).init.matrix).trace.re ≤ 1
    rw [← SubState.matrix_prod]
    exact ENNReal.ofReal_le_one.mpr
      ((SubState.basis ()).prod (runtime2 HashOutput HashDomain mem0).init).trace_re_le_one
  have h := (hgame _ hρ (querySupportedOn_init_hw mem0 ())).1
  rw [potential_cntY_init mem0 (Gset e) (), mul_zero, zero_add] at h
  refine le_self_add.trans (h.trans ((mul_le_mul_right htr _).trans (le_of_eq ?_)))
  rw [mul_one]
  push_cast
  ring

end game

end Quantum.StdModel.Qrom.EncSalt.LogCost

end
