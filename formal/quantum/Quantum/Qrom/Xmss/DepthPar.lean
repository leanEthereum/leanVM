module

public import Quantum.Qrom.SufCma.GamePar
public import Quantum.Par.Subst
public import VCVio.Quantum.Comp.TotalQueryBound
public import VCVio.Quantum.Comp.Potential
public import Quantum.Sponge.Oracle.Hardwired.EventPar
public import Quantum.Xmss.Hybrid.GradedPar
public import Quantum.Xmss.Hybrid.GradedMasked
public import Quantum.Xmss.Assembly.RecordPorts
public import Quantum.Qrom.CellEvent

@[expose] public section

/-!
# Serialized rounds: weights, charges and lifted programs

Facts about `Quantum.Par.parToSeq` used by the depth-aware QROM theorems, for any runtime and
any weights (not only traces of completely positive maps):

* `branch_run₂_seqCalls_cons`: the calls of a round at the results `Fin.cons r rs` are the
  first call at `r`, then the other calls at `rs`.
* `totalWeight_substitute_parToSeq_of_eq_zero`: a summed weight vanishing on the ports of rounds
  is the same for a parallel program against `R.par` and for its serialization against `R`.
* `eventWeight_substitute_parToSeq`: the event weight of the serialization is that of the
  parallel program.
* `isChargeBound_of_substitute_parToSeq`: a charge budget of the serialization is a width budget
  of the parallel program (the converse of `isChargeBound_substitute_parToSeq`).
* `substitute_parToSeq_liftOrdinary`: a program without rounds serializes to itself.
-/

open IPFunctor Quantum Quantum.SubInstrument
open scoped ENNReal

universe u v w w₁ w₂ u₁ v₁

namespace Quantum.QuantumRuntime

open Quantum.Par

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec)

/-- **The calls of a round at the results `Fin.cons r rs`**: the first call at `r`, then the other
calls at `rs`. -/
theorem branch_run₂_seqCalls_cons {w : ℕ} (f : Fin (w + 1) → spec.Port) (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn spec f × E) (post : roundOut spec f × E ≃ B) (r : spec.Result (f 0))
    (rs : RoundResult spec fun i ↦ f i.succ) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    (R.run₂ .instruments (seqCalls f E ℓ post)).branch (Fin.cons r rs) ρ =
      (R.run₂ .instruments (seqCalls (fun i ↦ f i.succ) (QReg.of (spec.Out (f 0) × E))
        (seqShift f E) (seqPost f E post))).branch rs
          ((R.queryStep (f 0) _ (seqSplitIn f E ℓ)).branch r ρ) := by
  rw [seqCalls_succ, run₂_queryBind, DSubInstrument.branch_bind_apply, tsum_eq_single r]
  · rw [run₂_map, SubInstrument.map_eq_bind_pure, DSubInstrument.branch_bind_apply,
      tsum_eq_single rs]
    · rw [SubInstrument.branch_pure_self, LinearMap.id_apply]
    · intro rs' h
      rw [SubInstrument.branch_pure_of_ne (fun h' ↦ h (Fin.cons_right_injective _ h').symm),
        LinearMap.zero_apply]
  · intro r' h
    rw [run₂_map, SubInstrument.map_eq_bind_pure, DSubInstrument.branch_bind_apply]
    refine (tsum_congr fun rs' ↦ ?_).trans tsum_zero
    have hne : Fin.cons (α := fun i ↦ spec.Result (f i)) r rs ≠ Fin.cons r' rs' := fun h' ↦
      h (by simpa using (congrFun h' 0).symm)
    rw [SubInstrument.branch_pure_of_ne hne, LinearMap.zero_apply]

variable {W : ∀ p, Matrix (spec.In p × R.D) (spec.In p × R.D) ℂ → ℝ≥0∞}

/-- **The weight of a round's calls, then a continuation**, for any weight vanishing on the ports
of the round: the weights of the continuations from the branches of the round. -/
theorem totalWeight_bind_seqCalls_of_eq_zero {w : ℕ} (f : Fin w → spec.Port)
    (hf : ∀ i σ, W (f i) σ = 0) (E : QReg) {A B : QReg} (ℓ : A ≃ roundIn spec f × E)
    (post : roundOut spec f × E ≃ B) {X : QReg → Type w₁}
    (g : ∀ u, QuantumComp₂.Leaf B (RoundResult spec f) u →
      QuantumComp LocalSig.instruments.{v₁} spec X u)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight .instruments W (IFreeM.bind (seqCalls f E ℓ post) g) ρ =
      ∑' rs, R.totalWeight .instruments W (g B ⟨rfl, rs⟩)
        ((R.run₂ .instruments (seqCalls f E ℓ post)).branch rs ρ) := by
  induction w generalizing E A B ρ with
  | zero =>
    have hL : IFreeM.bind (seqCalls f E ℓ post) g =
        QuantumComp.primBind (L := LocalSig.instruments.{v₁})
          ⟨RoundResult spec f, fun _ ↦ B, (relabel (ℓ.trans
            (((roundZeroEquiv f).prodCongr (Equiv.refl E)).trans post))).map
              fun _ ↦ (finZeroElim : RoundResult spec f)⟩ fun a ↦ g B ⟨rfl, a⟩ :=
      rfl
    rw [hL, R.totalWeight_primBind]
    refine tsum_congr fun rs ↦ congrArg _ ?_
    rw [seqCalls_zero, run₂_act, DSubInstrument.branch_bind_apply, tsum_eq_single rs]
    · rw [SubInstrument.branch_pure_self, LinearMap.id_apply]
      rfl
    · intro rs' h
      exact absurd (Subsingleton.elim rs' rs) h
  | succ w ih =>
    have hL : IFreeM.bind (seqCalls f E ℓ post) g =
        QuantumComp.queryBind (f 0) (QReg.of (roundIn spec (fun i ↦ f i.succ) × E))
          (seqSplitIn f E ℓ) fun r ↦ IFreeM.bind ((seqCalls (fun i ↦ f i.succ)
            (QReg.of (spec.Out (f 0) × E)) (seqShift f E) (seqPost f E post)).map
              (Fin.cons r)) g :=
      rfl
    refine (congrArg (fun y ↦ R.totalWeight .instruments W y ρ) hL).trans
      ((R.totalWeight_queryBind .instruments (f 0) _ (seqSplitIn f E ℓ) _ ρ).trans ?_)
    rw [hf 0, zero_add]
    have hk : ∀ r, IFreeM.bind ((seqCalls (fun i ↦ f i.succ) (QReg.of (spec.Out (f 0) × E))
        (seqShift f E) (seqPost f E post)).map (Fin.cons r)) g =
        IFreeM.bind (seqCalls (fun i ↦ f i.succ) (QReg.of (spec.Out (f 0) × E))
          (seqShift f E) (seqPost f E post)) fun u l ↦ g u ⟨l.1, Fin.cons r l.2⟩ :=
      fun r ↦ IFreeM.bind_imap _ _ _
    simp only [hk, ih (fun i ↦ f i.succ) (fun i ↦ hf i.succ)]
    refine Eq.trans ?_ ((Fin.consEquiv fun i ↦ spec.Result (f i)).tsum_eq _)
    refine Eq.trans ?_ ENNReal.tsum_prod'.symm
    refine tsum_congr fun r ↦ tsum_congr fun rs ↦ ?_
    exact (congrArg (R.totalWeight .instruments W (g B ⟨rfl, Fin.cons r rs⟩))
      (R.branch_run₂_seqCalls_cons f E ℓ post r rs ρ)).symm

/-- **Weights of the serialization, for any weight vanishing on the ports of rounds**: the summed
weight of the serialization against `R` is the summed weight of the parallel program against
`R.par` on its single calls. -/
theorem totalWeight_substitute_parToSeq_of_eq_zero {Q : Type u₁} (port : Q → spec.Port)
    (hvan : ∀ q σ, W (port q) σ = 0) {X : QReg → Type w} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v₁} (parSpec spec port) X A)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight .instruments W (IFreeM.substitute (parToSeq port) x) ρ =
      (R.par port).totalWeight .instruments (parWeight port W) x ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ y => exact (R.totalWeight_pure _ y ρ).trans ((R.par port).totalWeight_pure _ y ρ).symm
  | primBind _ o k ih =>
    exact (R.totalWeight_primBind _ o (fun b ↦ IFreeM.substitute (parToSeq port) (k b)) ρ).trans
      ((tsum_congr fun b ↦ ih b _).trans ((R.par port).totalWeight_primBind _ o k ρ).symm)
  | queryBind _ i E ℓ k ih =>
    rcases i with p | ⟨w, f⟩
    · exact (R.totalWeight_queryBind _ p E ℓ (fun r ↦ IFreeM.substitute (parToSeq port) (k r))
        ρ).trans ((congrArg (_ + ·) (tsum_congr fun r ↦ ih r _)).trans
          ((R.par port).totalWeight_queryBind _ (w := parWeight port W) (.inl p) E ℓ k ρ).symm)
    · have hq := R.queryStep_par_round port f E ℓ
      have hb : ∀ r, ((R.par port).queryStep (.inr (.round w f)) E ℓ).branch r ρ =
          (R.run₂ .instruments (seqCalls (fun i ↦ port (f i)) E
            (B := QReg.of (roundOut spec (fun i ↦ port (f i)) × E)) ℓ (Equiv.refl _))).branch
              r ρ := fun r ↦ congrArg (fun S ↦ DSubInstrument.branch S r ρ) hq
      exact (congrArg (fun y ↦ R.totalWeight .instruments W y ρ)
          (IFreeM.bind_assoc _ _ _)).trans
        ((R.totalWeight_bind_seqCalls_of_eq_zero _ (fun i ↦ hvan (f i)) E ℓ _ _ ρ).trans
          ((tsum_congr fun r ↦ (ih r _).trans
            (congrArg ((R.par port).totalWeight .instruments _ (k r)) (hb r).symm)).trans
            ((zero_add _).symm.trans
              ((R.par port).totalWeight_queryBind _ (w := parWeight port W)
                (.inr (.round w f)) E ℓ k ρ).symm)))

/-- **Event weights of the serialization**: the serialization against `R` has the event weight
of the parallel program against `R.par`. -/
theorem eventWeight_substitute_parToSeq {Q : Type u₁} (port : Q → spec.Port)
    (P : Matrix R.D R.D ℂ) {X : QReg → Type w} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v₁} (parSpec spec port) X A)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.eventWeight .instruments P (IFreeM.substitute (parToSeq port) x) ρ =
      (R.par port).eventWeight .instruments P x ρ := by
  unfold QuantumRuntime.eventWeight
  rw [R.run_substitute_parToSeq port x]
  rfl

end Quantum.QuantumRuntime

namespace Quantum.Par

variable {spec : QuantumOracleSpec.{u₁, v₁}}

/-- **The charges of a round's calls, then a continuation**: when every port of the round has a
result, a budget for the whole program covers the round's calls and leaves the rest for every
continuation. -/
theorem isChargeBound_of_bind_seqCalls (c : spec.Port → ℕ) {w : ℕ} (f : Fin w → spec.Port)
    (hne : ∀ i, Nonempty (spec.Result (f i))) (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn spec f × E) (post : roundOut spec f × E ≃ B) {X : QReg → Type w₁}
    {g : ∀ u, QuantumComp₂.Leaf B (RoundResult spec f) u →
      QuantumComp LocalSig.instruments.{v₁} spec X u} {n : ℕ}
    (h : IFreeM.IsChargeBound (IFreeM.bind (seqCalls f E ℓ post) g) (callCharge c) n) :
    ∑ i, c (f i) ≤ n ∧
      ∀ rs, IFreeM.IsChargeBound (g B ⟨rfl, rs⟩) (callCharge c) (n - ∑ i, c (f i)) := by
  induction w generalizing E A B n with
  | zero =>
    refine ⟨Nat.zero_le _, fun rs ↦ ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, Nat.sub_zero]
    exact h.2 (ULift.up rs)
  | succ w ih =>
    have h₀ := h.1
    have h₁ : ∀ r, ∑ i : Fin w, c (f i.succ) ≤ n - c (f 0) ∧ ∀ rs, IFreeM.IsChargeBound
        (g B ⟨rfl, Fin.cons r rs⟩) (callCharge c) (n - c (f 0) - ∑ i : Fin w, c (f i.succ)) :=
      fun r ↦ by
        have h2 : IFreeM.IsChargeBound (IFreeM.bind ((seqCalls (fun i ↦ f i.succ)
            (QReg.of (spec.Out (f 0) × E)) (seqShift f E) (seqPost f E post)).map (Fin.cons r))
              g) (callCharge c) (n - c (f 0)) := h.2 (ULift.up r)
        rw [show IFreeM.bind ((seqCalls (fun i ↦ f i.succ) (QReg.of (spec.Out (f 0) × E))
            (seqShift f E) (seqPost f E post)).map (Fin.cons r)) g =
            IFreeM.bind (seqCalls (fun i ↦ f i.succ) (QReg.of (spec.Out (f 0) × E))
              (seqShift f E) (seqPost f E post)) (fun u l ↦ g u ⟨l.1, Fin.cons r l.2⟩) from
            IFreeM.bind_imap _ _ _] at h2
        exact ih (fun i ↦ f i.succ) (fun i ↦ hne i.succ) _ _ _ h2
    obtain ⟨r⟩ := hne 0
    have hs : ∑ i, c (f i) = c (f 0) + ∑ i : Fin w, c (f i.succ) := Fin.sum_univ_succ _
    refine ⟨?_, fun rs ↦ ?_⟩
    · have := (h₁ r).1
      change c (f 0) ≤ n at h₀
      omega
    · have h₂ := (h₁ (rs 0)).2 (Fin.tail rs)
      rw [Fin.cons_self_tail] at h₂
      rwa [hs, ← Nat.sub_sub]

/-- `isChargeBound_of_bind_seqCalls` for a round's calls followed by two continuations. -/
theorem isChargeBound_of_bind_bind_seqCalls (c : spec.Port → ℕ) {w : ℕ}
    (f : Fin w → spec.Port) (hne : ∀ i, Nonempty (spec.Result (f i))) (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn spec f × E) (post : roundOut spec f × E ≃ B) {X : QReg → Type w₂}
    {Y : QReg → Type w₁}
    {g₁ : ∀ u, QuantumComp₂.Leaf B (RoundResult spec f) u →
      QuantumComp LocalSig.instruments.{v₁} spec X u}
    {y : QuantumComp LocalSig.instruments.{v₁} spec X A}
    (hy : y = IFreeM.bind (seqCalls f E ℓ post) g₁)
    {g₂ : ∀ u, X u → QuantumComp LocalSig.instruments.{v₁} spec Y u} {n : ℕ}
    (h : IFreeM.IsChargeBound (IFreeM.bind y g₂) (callCharge c) n) :
    ∑ i, c (f i) ≤ n ∧ ∀ rs, IFreeM.IsChargeBound (IFreeM.bind (g₁ B ⟨rfl, rs⟩) g₂)
      (callCharge c) (n - ∑ i, c (f i)) := by
  subst hy
  exact isChargeBound_of_bind_seqCalls c f hne E ℓ post
    ((congrArg (fun y ↦ IFreeM.IsChargeBound y (callCharge c) n)
      (IFreeM.bind_assoc (seqCalls f E ℓ post : IFreeM _ _ _) g₁ g₂)).mp h)

/-- **A charge budget of the serialization is a width budget of the parallel program** (when the
ports of rounds always have a result). -/
theorem isChargeBound_of_substitute_parToSeq {Q : Type u₁} (port : Q → spec.Port)
    (c : spec.Port → ℕ) (hne : ∀ q, Nonempty (spec.Result (port q))) {X : QReg → Type w}
    {A : QReg} (x : QuantumComp LocalSig.instruments.{v₁} (parSpec spec port) X A) {n : ℕ}
    (hx : IFreeM.IsChargeBound (IFreeM.substitute (parToSeq port) x) (callCharge c) n) :
    IFreeM.IsChargeBound x (callCharge (widthCharge port c)) n := by
  induction x using QuantumComp.inductionOn generalizing n with
  | pure _ _ => trivial
  | primBind _ o k ih => exact ⟨Nat.zero_le _, fun b ↦ ih b.down (hx.2 b)⟩
  | queryBind _ i E ℓ k ih =>
    rcases i with p | ⟨w, f⟩
    · exact ⟨hx.1, fun r ↦ ih r.down (hx.2 r)⟩
    · have h := isChargeBound_of_bind_bind_seqCalls c (fun i ↦ port (f i)) (fun i ↦ hne (f i)) E
        ℓ (B := QReg.of (roundOut spec (fun i ↦ port (f i)) × E)) (Equiv.refl _)
        (g₁ := fun _ l ↦ QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩)
        (y := parToSeq port _ (.query (.inr (.round w f)) E ℓ)) rfl hx
      exact ⟨h.1, fun r ↦ ih r.down (h.2 r.down)⟩

/-- **A program without rounds serializes to itself.** -/
theorem substitute_parToSeq_liftOrdinary {Q : Type u₁} (port : Q → spec.Port)
    {X : QReg → Type w} {A : QReg} (y : QuantumComp LocalSig.instruments.{v₁} spec X A) :
    IFreeM.substitute (parToSeq port)
      (QuantumComp.liftOrdinary (t := roundSpec spec port) y) = y := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => rfl
  | primBind _ o k ih => exact congrArg (QuantumComp.primBind o) (funext ih)
  | queryBind _ i E ℓ k ih => exact congrArg (QuantumComp.queryBind i E ℓ) (funext ih)

/-- A substitution distributes over sequencing of fixed-register programs. -/
theorem substitute_bind₂ {L : LocalSig.{u, v}} {spec spec' : QuantumOracleSpec.{u₁, v₁}}
    (σ : CommandSubstitution (QuantumComp.toIPFunctor L spec) (QuantumComp.toIPFunctor L spec'))
    {A B C : QReg} {α : Type w} {β : Type w₁} (x : QuantumComp₂ L spec A B α)
    (g : α → QuantumComp₂ L spec B C β) :
    IFreeM.substitute σ (x.bind g) =
      QuantumComp₂.bind (L := L) (spec := spec') (IFreeM.substitute σ x) fun a ↦
        IFreeM.substitute σ (g a) :=
  (IFreeM.substitute_bind σ x _).trans
    (congrArg _ (funext fun _ ↦ funext fun ⟨h, _⟩ ↦ by subst h; rfl))

end Quantum.Par

namespace Quantum.Qrom.SufCma

open Quantum.Par (roundIn roundOut seqCalls seqCalls_succ)

variable {Req Resp : Type}

/-! ## Signing transcripts of parallel adversaries -/

/-- The transcript after a command of a parallel adversary answered `b`: a signing request
appends itself and its answer. -/
def logAfterPar {L : LocalSig.{u, v}} {A : QReg} :
    (c : QuantumComp.Cmd L (advSpecPar Req Resp) A) → c.Resp → SignLog Req Resp →
      SignLog Req Resp
  | .query (.sign r) _ _, b, log => log ++ [⟨r, b.down⟩]
  | _, _, log => log

/-- `logSigns` for parallel adversaries: the same commands, the transcript threaded along each
path and handed to the leaf map `leaf` at the end. -/
def logSignsPar {L : LocalSig.{u, v}} {X : QReg → Type w} {Y : QReg → Type w₁}
    (leaf : ∀ u, X u → SignLog Req Resp → Y u) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor L (advSpecPar Req Resp)) X A →
      SignLog Req Resp → IFreeM (QuantumComp.toIPFunctor L (advSpecPar Req Resp)) Y A
  | _, .pure x, log => .pure (leaf _ x log)
  | _, .liftBind c next, log => .liftBind c fun b ↦ logSignsPar leaf (next b) (logAfterPar c b log)

/-- Keeping the transcript of a parallel adversary keeps every charge bound. -/
theorem isChargeBound_logSignsPar {L : LocalSig.{u, v}} {X : QReg → Type w}
    {Y : QReg → Type w₁} (leaf : ∀ u, X u → SignLog Req Resp → Y u)
    {c : (A : QReg) → QuantumComp.Cmd L (advSpecPar Req Resp) A → ℕ} {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor L (advSpecPar Req Resp)) X A) (log : SignLog Req Resp)
    {n : ℕ} (hx : IFreeM.IsChargeBound x c n) :
    IFreeM.IsChargeBound (logSignsPar leaf x log) c n := by
  induction x using IFreeM.inductionOn generalizing log n with
  | pure _ _ => trivial
  | liftBind _ c' next ih => exact ⟨hx.1, fun r ↦ ih r _ (hx.2 r)⟩

/-- The transcript passes through a round's calls of `H`. -/
theorem logSigns_bind_seqCalls {X : QReg → Type} {Y : QReg → Type}
    (leaf : ∀ u, X u → SignLog Req Resp → Y u) : ∀ {w : ℕ} (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn (advSpec Req Resp) (fun _ : Fin w ↦ .hash) × E)
    (post : roundOut (advSpec Req Resp) (fun _ : Fin w ↦ .hash) × E ≃ B)
    (g : ∀ u, QuantumComp₂.Leaf B (Fin w → Unit) u →
      QuantumComp LocalSig.instruments.{0} (advSpec Req Resp) X u) (log : SignLog Req Resp),
    logSigns leaf (IFreeM.bind (seqCalls (fun _ : Fin w ↦ AdvPort.hash) E ℓ post) g) log =
      IFreeM.bind (seqCalls (fun _ : Fin w ↦ AdvPort.hash) E ℓ post) fun u l ↦
        logSigns leaf (g u l) log
  | 0, _, _, _, _, _, _, _ => rfl
  | w + 1, E, _, B, ℓ, post, g, log =>
    congrArg (IFreeM.liftBind _) (funext fun b ↦ by
      dsimp only [QuantumComp.onDown]
      exact (congrArg (logSigns leaf · log) (IFreeM.bind_imap _ _ _)).trans
        ((logSigns_bind_seqCalls leaf (w := w) _ _ _ _ log).trans
          (IFreeM.bind_imap (fun s (p : QuantumComp₂.Leaf B (Fin w → Unit) s) ↦
            (⟨p.1, Fin.cons b.down p.2⟩ : QuantumComp₂.Leaf B (Fin (w + 1) → Unit) s))
            (fun u l ↦ logSigns leaf (g u l) log) _).symm))

/-- **Transcripts commute with serialization.** -/
theorem logSigns_substitute_toSeq {X : QReg → Type} {Y : QReg → Type}
    (leaf : ∀ u, X u → SignLog Req Resp → Y u) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpecPar Req Resp)) X A)
    (log : SignLog Req Resp) :
    logSigns leaf (IFreeM.substitute toSeq x) log =
      IFreeM.substitute toSeq (logSignsPar leaf x log) := by
  induction x using IFreeM.inductionOn generalizing log with
  | pure _ _ => rfl
  | liftBind _ c next ih =>
    rcases c with o | ⟨w | r, E, ℓ⟩
    · exact congrArg (IFreeM.liftBind _) (funext fun b ↦ ih b log)
    · refine (congrArg (logSigns leaf · log) (IFreeM.bind_assoc _ _ _)).trans
        ((logSigns_bind_seqCalls leaf E ℓ _ _ log).trans
          ((congrArg (IFreeM.bind _) (funext fun u ↦ funext fun l ↦ ?_)).trans
            (IFreeM.bind_assoc _ _ _).symm))
      obtain ⟨h, a⟩ := l
      subst h
      exact ih _ log
    · exact congrArg (IFreeM.liftBind _) (funext fun b ↦ ih b _)

end Quantum.Qrom.SufCma

namespace Quantum.Qrom

open Quantum.Sponge
open scoped Kronecker

variable {D Y M : Type} [Fintype D] [DecidableEq D] [Fintype Y] [DecidableEq Y]

/-! ## The cell events of a cell-target event -/

/-- **The cell-target event at the cell `c` alone.** -/
abbrev CellTargetBadAt (tgt : Hw Y D → M → D → Set Y) (c : D) : Set (RomReg D Y M) :=
  CellTargetBad fun W m x ↦ if x = c then tgt W m x else ∅

variable {tgt : Hw Y D → M → D → Set Y}

omit [Fintype D] [Fintype Y] [DecidableEq Y] in
theorem mem_cellTargetBadAt {c : D} {s : RomReg D Y M} :
    s ∈ CellTargetBadAt tgt c ↔ ∃ y, unionH s c = some y ∧ y ∈ tgt s.2.1 s.2.2 c := by
  constructor
  · rintro ⟨x, y, hxy, hy⟩
    by_cases hx : x = c
    · subst hx
      exact ⟨y, hxy, by simpa using hy⟩
    · simp [hx] at hy
  · rintro ⟨y, hy, hyt⟩
    exact ⟨c, y, hy, by simpa using hyt⟩

omit [Fintype D] [Fintype Y] [DecidableEq Y] in
theorem cellTargetBadAt_subset (c : D) : CellTargetBadAt (M := M) tgt c ⊆ CellTargetBad tgt :=
  fun _ hs ↦ by
    obtain ⟨y, hy, hyt⟩ := mem_cellTargetBadAt.1 hs
    exact ⟨c, y, hy, hyt⟩

omit [Fintype D] [Fintype Y] [DecidableEq Y] in
theorem exists_mem_cellTargetBadAt {s : RomReg D Y M} (hs : s ∈ CellTargetBad tgt) :
    ∃ c, s ∈ CellTargetBadAt tgt c := by
  obtain ⟨x, y, hy, hyt⟩ := hs
  exact ⟨x, mem_cellTargetBadAt.2 ⟨y, hy, hyt⟩⟩

omit [Fintype D] [Fintype Y] [DecidableEq Y] in
/-- The event at `c` reads the cell `c` of `h`, the other databases and the classical data. -/
theorem mem_cellTargetBadAt_congr (c : D) (s s' : RomReg D Y M) (h₁ : s'.1.1 c = s.1.1 c)
    (_h₂ : s'.1.2 = s.1.2) (h₃ : s'.2 = s.2) :
    s' ∈ CellTargetBadAt tgt c ↔ s ∈ CellTargetBadAt tgt c := by
  have hu : unionH s' c = unionH s c := by
    simp only [unionH, h₁, h₃]
  rw [mem_cellTargetBadAt, mem_cellTargetBadAt, hu, h₃]

open scoped Classical in
/-- **The fresh bound of the event at a cell**, from the target fractions of the cell-target
event. -/
theorem freshBound_slice_cellTargetBadAt (c : D) (W : Hw Y D) (m : M) {ε : ℝ≥0∞}
    (hε : ∀ x, W.1 x = none →
      ((Finset.univ.filter fun y ↦ y ∈ tgt W m x).card : ℝ≥0∞) / Fintype.card Y ≤ ε)
    (t : ℕ) : FreshBound (slice (CellTargetBadAt tgt c) W m) t ε := by
  refine freshBound_slice_cellTargetBad W m (fun x hx ↦ ?_) t
  by_cases h : x = c
  · subst h
    simpa using hε x hx
  · simp [h]

end Quantum.Qrom

/-! ## The event bound of runtime 2 with record ports, for serialized programs with rounds -/

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Par Quantum.Xmss.Hybrid
open scoped Kronecker ComplexOrder

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X]
  [AddCommGroup Z] [Nonempty X] [Nonempty Z] {S : Type} [Fintype S] [DecidableEq S] {M' : Type}
  [Fintype M'] [DecidableEq M']

/-- **The depth-graded event bound of `runtimeR` for a serialized program with rounds of `h`**:
the event of cell events with fresh bound `ε` has weight at most `(√(6 ε d q) + √classical)²`
after a program of total width `q` in `d` rounds and `K` classical calls; the classical costs
are those of the serialized program. -/
theorem eventWeight_runtimeR_serialize_le (B : Set (HwReg X Z (Finset S × M')))
    [DecidablePred (· ∈ B)] (hB : LabelFree X Z S M' B)
    (Sc : Z → Set (HwReg X Z (Finset S × M'))) [∀ c, DecidablePred (· ∈ Sc c)]
    (hsub : ∀ c, Sc c ⊆ B) (hunion : ∀ s ∈ B, ∃ c, s ∈ Sc c)
    (hloc : ∀ c (s s' : HwReg X Z (Finset S × M')), s'.1.1 c = s.1.1 c → s'.1.2 = s.1.2 →
      s'.2 = s.2 → (s' ∈ Sc c ↔ s ∈ Sc c))
    (hupc : ∀ c W m, UpClosed (slice (Sc c) W m)) (hup : ∀ W m, UpClosed (slice B W m))
    (m₀ : Finset S × M')
    (hempty : ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀) ∉ B)
    {q d K : ℕ} {ε : ℝ≥0∞} (hεtop : ε ≠ ⊤)
    (hεc : ∀ c W m, FreshBound (slice (Sc c) W m) (q + K + 1) ε)
    (hε : ∀ W m, FreshBound (slice B W m) (q + K + 1) ε)
    (dR : HwRead X Z (Finset S × M') → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (dP : HwProg X Z → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (hdR : ∀ c σ, σ.PosSemidef → ∑' r, potential (hwProjector B)
      (MatrixMap.conj (hwReadKraus c r) σ) ≤ potential (hwProjector B) σ + dR c σ)
    (hdP : ∀ c σ, σ.PosSemidef → ∑' r, potential (hwProjector B)
      (MatrixMap.conj (hwProgKraus c r) σ) ≤ potential (hwProjector B) σ + dP c σ)
    {Wf : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0}
      (parSpec (recHwSpec X Z S M') (ePort X Z (Finset S × M') (recSpec S M'))) Wf A)
    (hxq : IFreeM.IsChargeBound x (portCharge (spongeWidth (ePort X Z (Finset S × M')
      (recSpec S M')) (hwExtCls X Z (Finset S × M') (recSpec S M')))) q)
    (hxd : IFreeM.IsChargeBound x (portCharge (spongeRounds (ePort X Z (Finset S × M')
      (recSpec S M')) (hwExtCls X Z (Finset S × M') (recSpec S M')))) d)
    (hxK : IFreeM.IsChargeBound x (portCharge (clsCount (ePort X Z (Finset S × M')
      (recSpec S M')) (hwExtCls X Z (Finset S × M') (recSpec S M')))) K)
    (ρ : SubState A) :
    (runtimeR m₀).eventWeight .instruments (hwProjector B)
        (IFreeM.substitute (parToSeq (ePort X Z (Finset S × M') (recSpec S M'))) x)
        (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) ≤
      ((6 * ε * d * q) ^ (2⁻¹ : ℝ) +
        (runtimeR m₀).totalWeight .instruments (extWeight (hwCost dR dP))
          (IFreeM.substitute (parToSeq (ePort X Z (Finset S × M') (recSpec S M'))) x)
          (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := rpow_inv_two_eventWeight_extend_par_le B Sc hsub hunion hloc hupc hup (hwEmpty X Z)
    m₀ hempty hεtop hεc hε dR dP hdR hdP (initHw X Z m₀)
    (spongeHardwiredRuntime X Z (hwEmpty X Z) m₀).step rfl rfl (t := recSpec S M') recStep
    (fun _ _ ↦ 0) (fun T r n σ hσ ↦ querySupportedOn_recStep T r n σ hσ)
    (fun T σ hσ ↦ tsum_potential_recStep_le B hB T σ hσ) .instruments x hxq hxd hxK ρ
  have hw : hwExtCost (t := recSpec S M') dR dP (fun _ _ ↦ 0) =
      extWeight (D := QReg.of (HwReg X Z (Finset S × M'))) (hwCost dR dP) := by
    funext i σ
    rcases i with i | j <;> rfl
  have hpw : parWeight (ePort X Z (Finset S × M') (recSpec S M'))
      (hwExtCost (t := recSpec S M') dR dP (fun _ _ ↦ 0)) =
      parWeight (ePort X Z (Finset S × M') (recSpec S M'))
        (extWeight (D := QReg.of (HwReg X Z (Finset S × M'))) (hwCost dR dP)) := by
    rw [hw]
  have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
  rw [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h2
  exact ((runtimeR (X := X) (Z := Z) m₀).eventWeight_substitute_parToSeq _ _ x _).trans_le
    (h2.trans_eq (congrArg (fun t ↦ ((6 * ε * d * q) ^ (2⁻¹ : ℝ) + t ^ (2⁻¹ : ℝ)) ^ 2)
      ((congrArg (fun W ↦ ((runtimeR (X := X) (Z := Z) m₀).par
        (ePort X Z (Finset S × M') (recSpec S M'))).totalWeight .instruments W x
          (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)) hpw).trans
      ((runtimeR (X := X) (Z := Z) m₀).totalWeight_substitute_parToSeq_of_eq_zero
        (W := extWeight (hwCost dR dP)) _ (fun _ _ ↦ rfl) x _).symm)))

end Quantum.Xmss.Assembly

/-! ## Hidden masses of the rounds are the hidden masses of their calls -/

namespace Quantum.Xmss.Hybrid

open Quantum QuantumRuntime Quantum.Par Quantum.Sponge Quantum.Xmss.Assembly
open Matrix
open scoped Kronecker ComplexOrder

section diag

/-- The diagonal mass after a relabelling is the mass of the preimage. -/
theorem diagMass_relabel {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (C : Set β) (σ : Matrix α α ℂ) :
    diagMass C ((SubInstrument.relabel e).branch () σ) = diagMass {a | e a ∈ C} σ := by
  rw [SubInstrument.relabel_branch_apply, diagMass, diagMass]
  refine Fintype.sum_equiv e.symm _ _ fun b ↦ ?_
  obtain ⟨a, rfl⟩ := e.surjective b
  simp only [Equiv.symm_apply_apply, Matrix.submatrix_apply]
  by_cases h : e a ∈ C
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show a ∈ {a | e a ∈ C} from h),
      Equiv.symm_apply_apply]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show a ∉ {a | e a ∈ C} from h)]

/-- **An isometry moving basis states between `P'` and `P`** keeps the diagonal mass. -/
theorem diagMass_conj_of_keep {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (K : Matrix m n ℂ) (hK : Kᴴ * K = 1) (P : Set m) (P' : Set n)
    (hP : ∀ y x, K y x ≠ 0 → (y ∈ P ↔ x ∈ P')) {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    diagMass P (MatrixMap.conj K σ) = diagMass P' σ := by
  have hc : setProj P * K = K * setProj P' := by
    ext y x
    rw [setProj, setProj, diagonal_mul, mul_diagonal]
    by_cases h : K y x = 0
    · simp [h]
    · have hm := hP y x h
      by_cases hx : x ∈ P'
      · simp [Set.indicator_of_mem (hm.2 hx), Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem (fun hy ↦ hx (hm.1 hy)), Set.indicator_of_notMem hx]
  rw [diagMass_eq_ofReal_trace_conj P ((MatrixMap.isCP_conj K).posSemidef hσ),
    diagMass_eq_ofReal_trace_conj P' hσ, ← LinearMap.comp_apply, ← MatrixMap.conj_mul, hc,
    MatrixMap.conj_mul, LinearMap.comp_apply, MatrixMap.trace_conj_apply, hK, Matrix.one_mul]

/-- **The diagonal mass of a call's input** is the mass of the states whose exposed part and
runtime register lie in the set. -/
theorem diagMass_callInput {A J E D : Type} [Fintype A] [DecidableEq A] [Fintype J]
    [DecidableEq J] [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D] (ℓ : A ≃ J × E)
    (C : Set (J × D)) {ρ : Matrix (A × D) (A × D) ℂ} (hρ : ρ.PosSemidef) :
    diagMass C (callInput ℓ D ρ) = diagMass {p : A × D | ((ℓ p.1).1, p.2) ∈ C} ρ := by
  have hd : ∀ p, 0 ≤ (ρ p p).re := fun _ ↦ (Complex.nonneg_iff.1 hρ.diag_nonneg).1
  have hent : ∀ q, callInput ℓ D ρ q q =
      ∑ e, ρ ((queryEquivIn ℓ D).symm (q, e)) ((queryEquivIn ℓ D).symm (q, e)) := fun q ↦ by
    simp only [callInput, LinearMap.comp_apply, MatrixMap.traceRight_apply,
      SubInstrument.relabel_branch_apply, Matrix.submatrix_apply]
  have h1 : ∀ q, C.indicator (fun q ↦ ENNReal.ofReal (callInput ℓ D ρ q q).re) q =
      ∑ e, C.indicator (fun q' ↦ ENNReal.ofReal
        (ρ ((queryEquivIn ℓ D).symm (q', e)) ((queryEquivIn ℓ D).symm (q', e))).re) q := by
    intro q
    by_cases hq : q ∈ C
    · simp only [Set.indicator_of_mem hq]
      rw [hent, Complex.re_sum, ENNReal.ofReal_sum_of_nonneg fun e _ ↦ hd _]
    · simp only [Set.indicator_of_notMem hq, Finset.sum_const_zero]
  have h3 : ∀ x : (J × D) × E, C.indicator (fun q' ↦ ENNReal.ofReal
        (ρ ((queryEquivIn ℓ D).symm (q', x.2)) ((queryEquivIn ℓ D).symm (q', x.2))).re) x.1 =
      {p : A × D | ((ℓ p.1).1, p.2) ∈ C}.indicator (fun p ↦ ENNReal.ofReal (ρ p p).re)
        ((queryEquivIn ℓ D).symm x) := by
    intro x
    obtain ⟨p, rfl⟩ := (queryEquivIn ℓ D).surjective x
    rw [Equiv.symm_apply_apply]
    by_cases h : ((ℓ p.1).1, p.2) ∈ C
    · rw [Set.indicator_of_mem (show (queryEquivIn ℓ D p).1 ∈ C from h), Set.indicator_of_mem
        (show p ∈ {p : A × D | ((ℓ p.1).1, p.2) ∈ C} from h)]
      rw [show ((queryEquivIn ℓ D p).1, (queryEquivIn ℓ D p).2) = queryEquivIn ℓ D p from rfl,
        Equiv.symm_apply_apply]
    · rw [Set.indicator_of_notMem (show (queryEquivIn ℓ D p).1 ∉ C from h),
        Set.indicator_of_notMem (show p ∉ {p : A × D | ((ℓ p.1).1, p.2) ∈ C} from h)]
  rw [diagMass, diagMass, Finset.sum_congr rfl fun q _ ↦ h1 q]
  exact (Fintype.sum_prod_type (fun x : (J × D) × E ↦ C.indicator (fun q' ↦ ENNReal.ofReal
    (ρ ((queryEquivIn ℓ D).symm (q', x.2)) ((queryEquivIn ℓ D).symm (q', x.2))).re) x.1)).symm.trans
    (Fintype.sum_equiv (queryEquivIn ℓ D).symm _ _ h3)

/-- **A call keeping a coordinate `κ` of the runtime register keeps the diagonal masses** of the
sets reading only the program's remainder and `κ`. -/
theorem diagMass_queryStep_of_keep {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec)
    (i : spec.Port) (E : QReg) {A : QReg} (ℓ : A ≃ spec.In i × E) (r : spec.Result i)
    (U : Matrix (spec.Out i × R.D) (spec.In i × R.D) ℂ)
    (hU : (R.step i).branch r = MatrixMap.conj U) (hUu : Uᴴ * U = 1) {Λ : Type} (κ : R.D → Λ)
    (hkeep : ∀ o d' j d, U (o, d') (j, d) ≠ 0 → κ d' = κ d)
    (P : Set ((spec.Out i × E) × R.D)) (P' : Set (A × R.D))
    (hPP' : ∀ a d o d', κ d' = κ d → (((o, (ℓ a).2), d') ∈ P ↔ (a, d) ∈ P'))
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    diagMass P ((R.queryStep i E ℓ).branch r ρ) = diagMass P' ρ := by
  rw [queryStep_branch_apply, DSubInstrument.branch_frame_apply, hU, MatrixMap.amplify_conj,
    diagMass_relabel]
  have hK : (U ⊗ₖ (1 : Matrix E E ℂ))ᴴ * (U ⊗ₖ (1 : Matrix E E ℂ)) = 1 := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← Matrix.mul_kronecker_mul, hUu,
      Matrix.one_mul, Matrix.one_kronecker_one]
  rw [diagMass_conj_of_keep _ hK _ {y | (queryEquivIn ℓ R.D).symm y ∈ P'} ?_
    ((SubInstrument.relabel (queryEquivIn ℓ R.D)).posSemidef_branch_apply () hρ),
    diagMass_relabel]
  · show diagMass {a | (queryEquivIn ℓ R.D).symm (queryEquivIn ℓ R.D a) ∈ P'} ρ = _
    simp only [Equiv.symm_apply_apply]
    rfl
  · rintro ⟨⟨o, d'⟩, e'⟩ y h
    obtain ⟨⟨a, d⟩, rfl⟩ := (queryEquivIn ℓ R.D).surjective y
    rw [queryEquivIn_apply, kroneckerMap_apply, Matrix.one_apply] at h
    split_ifs at h with he
    · subst he
      show ((o, (ℓ a).2), d') ∈ P ↔ (queryEquivIn ℓ R.D).symm (queryEquivIn ℓ R.D (a, d)) ∈ P'
      rw [Equiv.symm_apply_apply]
      exact hPP' a d o d' (hkeep o d' _ _ (left_ne_zero_of_mul h))
    · exact absurd (mul_zero _) h

end diag

section transfer

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X]
  [AddCommGroup Z] [Nonempty X] [Nonempty Z] {S : Type} [Fintype S] [DecidableEq S] {M' : Type}
  [Fintype M'] [DecidableEq M'] (Hh : Set Z) (Hk Hk' : Set X) (m₀ : Finset S × M')

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
theorem spongeMass_h (σ : Matrix ((Z × X) × HwReg X Z (Finset S × M'))
    ((Z × X) × HwReg X Z (Finset S × M')) ℂ) :
    spongeMass Hh Hk Hk' (recHPort X Z S M' ()) σ = diagMass (hSlotSet M' Hh) σ := by
  rw [spongeMass_eq]
  rfl

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
theorem parSpongeMass_round_eq {w : ℕ} (f : Fin w → Unit) :
    parSpongeMass (S := S) (M' := M') Hh Hk Hk' (.inr (.round w f)) = roundHidMass S M' Hh w := by
  funext σ
  by_cases hw : w = 0
  · subst hw
    simp [parSpongeMass, hybCls, roundHidMass]
  · simp [parSpongeMass, hybCls, parHidMass, hw]

/-- **The hidden mass of a round, slot by slot**: its first slot's mass at the first call's
input, and the mass of the other slots after the first call. -/
theorem roundHidMass_succ_eq {w : ℕ} (E : QReg) {A : QReg}
    (ℓ : A ≃ roundIn (recHwSpec X Z S M') (fun _ : Fin (w + 1) ↦ recHPort X Z S M' ()) × E)
    {ρ : Matrix (A × HwReg X Z (Finset S × M')) (A × HwReg X Z (Finset S × M')) ℂ}
    (hρ : ρ.PosSemidef) :
    diagMass (hSlotSet M' Hh)
        (callInput (seqSplitIn (fun _ ↦ recHPort X Z S M' ()) E ℓ)
          (runtimeR (X := X) (Z := Z) m₀).D ρ) +
      roundHidMass S M' Hh w (callInput (seqShift (fun _ ↦ recHPort X Z S M' ()) E)
        (runtimeR (X := X) (Z := Z) m₀).D (((runtimeR m₀).queryStep (recHPort X Z S M' ()) _
          (seqSplitIn (fun _ ↦ recHPort X Z S M' ()) E ℓ)).branch () ρ)) =
      roundHidMass S M' Hh (w + 1) (callInput ℓ (runtimeR (X := X) (Z := Z) m₀).D ρ) := by
  have hb := ((runtimeR m₀).queryStep (recHPort X Z S M' ()) _
    (seqSplitIn (fun _ ↦ recHPort X Z S M' ()) E ℓ)).posSemidef_branch_apply () hρ
  simp only [roundHidMass]
  rw [Fin.sum_univ_succ]
  congr 1
  · exact (diagMass_callInput _ _ hρ).trans
      (diagMass_callInput ℓ {x | (x.1 0, x.2) ∈ hSlotSet M' Hh} hρ).symm
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    refine (diagMass_callInput _ _ hb).trans (Eq.trans ?_ (diagMass_callInput _ _ hρ).symm)
    refine diagMass_queryStep_of_keep (runtimeR m₀) (recHPort X Z S M' ()) _
      (seqSplitIn (fun _ ↦ recHPort X Z S M' ()) E ℓ) ()
      ((spongeHardwired X Z (hwEmpty X Z) m₀).U .h)
      (spongeHardwiredRuntime_step_branch (hwEmpty X Z) m₀ (.inl (.inl .h)) ())
      (mem_unitaryGroup_iff'.mp ((spongeHardwired X Z (hwEmpty X Z) m₀).unitary .h))
      (fun d ↦ d.2) (fun o d' j d h ↦ snd_eq_of_U_h_ne_zero (Or.inl rfl) (o, d') (j, d) h)
      _ _ (fun a d o d' h ↦ ?_) hρ
    show _ ∧ d'.2.1.1 _ = none ↔ _ ∧ d.2.1.1 _ = none
    rw [h]
    exact Iff.rfl

/-- **The calls of a round of `h`, then a continuation**: the sponge masses of the calls are the
round's hidden mass at the round's input. -/
theorem totalWeight_spongeMass_bind_seqCalls {Xf : QReg → Type} : ∀ {w : ℕ} (E : QReg)
    {A B : QReg} (ℓ : A ≃ roundIn (recHwSpec X Z S M') (fun _ : Fin w ↦ recHPort X Z S M' ()) × E)
    (post : roundOut (recHwSpec X Z S M') (fun _ : Fin w ↦ recHPort X Z S M' ()) × E ≃ B)
    (g : ∀ u, QuantumComp₂.Leaf B (RoundResult (recHwSpec X Z S M')
      (fun _ : Fin w ↦ recHPort X Z S M' ())) u →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M') Xf u)
    {ρ : Matrix (A × HwReg X Z (Finset S × M')) (A × HwReg X Z (Finset S × M')) ℂ},
    ρ.PosSemidef →
    (runtimeR m₀).totalWeight .instruments (spongeMass Hh Hk Hk')
        (IFreeM.bind (seqCalls (fun _ : Fin w ↦ recHPort X Z S M' ()) E ℓ post) g) ρ =
      roundHidMass S M' Hh w (callInput ℓ (runtimeR (X := X) (Z := Z) m₀).D ρ) +
        ∑' rs, (runtimeR m₀).totalWeight .instruments (spongeMass Hh Hk Hk') (g B ⟨rfl, rs⟩)
          (((runtimeR m₀).run₂ .instruments
            (seqCalls (fun _ : Fin w ↦ recHPort X Z S M' ()) E ℓ post)).branch rs ρ)
  | 0, E, A, B, ℓ, post, g, ρ, _ => by
    rw [show roundHidMass S M' Hh 0 (callInput ℓ (runtimeR (X := X) (Z := Z) m₀).D ρ) = 0 from
      Finset.sum_empty, zero_add]
    exact (runtimeR m₀).totalWeight_bind_seqCalls_of_eq_zero _ (fun i ↦ i.elim0) E ℓ post g ρ
  | w + 1, E, A, B, ℓ, post, g, ρ, hρ => by
    have hL : IFreeM.bind (seqCalls (fun _ : Fin (w + 1) ↦ recHPort X Z S M' ()) E ℓ post) g =
        QuantumComp.queryBind (recHPort X Z S M' ())
          (QReg.of (roundIn (recHwSpec X Z S M') (fun _ : Fin w ↦ recHPort X Z S M' ()) × E))
          (seqSplitIn (fun _ ↦ recHPort X Z S M' ()) E ℓ) fun r ↦ IFreeM.bind
            ((seqCalls (fun _ : Fin w ↦ recHPort X Z S M' ())
              (QReg.of ((recHwSpec X Z S M').Out (recHPort X Z S M' ()) × E))
              (seqShift (fun _ ↦ recHPort X Z S M' ()) E)
              (seqPost (fun _ ↦ recHPort X Z S M' ()) E post)).map (Fin.cons r)) g :=
      rfl
    have hk : ∀ r, IFreeM.bind ((seqCalls (fun _ : Fin w ↦ recHPort X Z S M' ())
        (QReg.of ((recHwSpec X Z S M').Out (recHPort X Z S M' ()) × E))
        (seqShift (fun _ ↦ recHPort X Z S M' ()) E)
        (seqPost (fun _ ↦ recHPort X Z S M' ()) E post)).map (Fin.cons r)) g =
        IFreeM.bind (seqCalls (fun _ : Fin w ↦ recHPort X Z S M' ())
          (QReg.of ((recHwSpec X Z S M').Out (recHPort X Z S M' ()) × E))
          (seqShift (fun _ ↦ recHPort X Z S M' ()) E)
          (seqPost (fun _ ↦ recHPort X Z S M' ()) E post)) fun u l ↦ g u ⟨l.1, Fin.cons r l.2⟩ :=
      fun _ ↦ IFreeM.bind_imap _ _ _
    have hb := fun r ↦ ((runtimeR m₀).queryStep (recHPort X Z S M' ()) _
      (seqSplitIn (fun _ ↦ recHPort X Z S M' ()) E ℓ)).posSemidef_branch_apply r hρ
    refine (congrArg (fun y ↦ (runtimeR m₀).totalWeight .instruments (spongeMass Hh Hk Hk') y ρ)
      hL).trans (((runtimeR m₀).totalWeight_queryBind .instruments _ _ _ _ ρ).trans ?_)
    refine (congrArg (_ + ·) (tsum_congr fun r ↦ (congrArg (fun y ↦
      (runtimeR m₀).totalWeight .instruments (spongeMass Hh Hk Hk') y _) (hk r)).trans
        (totalWeight_spongeMass_bind_seqCalls (w := w) _ _ _ _ (hb r)))).trans ?_
    rw [ENNReal.tsum_add, ← add_assoc]
    congr 1
    · refine Eq.trans ?_ (roundHidMass_succ_eq Hh m₀ E ℓ hρ)
      congr 1
      exact tsum_eq_single _ fun r h ↦ absurd rfl h
    · refine Eq.trans ?_ ((Fin.consEquiv fun _ ↦ Unit).tsum_eq _)
      refine Eq.trans ?_ ENNReal.tsum_prod'.symm
      refine tsum_congr fun r ↦ tsum_congr fun rs ↦ ?_
      exact (congrArg ((runtimeR m₀).totalWeight .instruments (spongeMass Hh Hk Hk')
        (g B ⟨rfl, Fin.cons r rs⟩)) ((runtimeR m₀).branch_run₂_seqCalls_cons _ E ℓ post r rs
          ρ)).symm

/-- **The hidden masses of a parallel program are those of its serialization**: a round's hidden
mass (the sum over its slots) is the summed hidden mass of its calls of `h`. -/
theorem totalWeight_parSpongeMass_eq {Xf : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} (parSpec (recHwSpec X Z S M') (recHPort X Z S M'))
      Xf A)
    {ρ : Matrix (A × HwReg X Z (Finset S × M')) (A × HwReg X Z (Finset S × M')) ℂ}
    (hρ : ρ.PosSemidef) :
    ((runtimeR m₀).par (recHPort X Z S M')).totalWeight .instruments
        (parSpongeMass Hh Hk Hk') x ρ =
      (runtimeR m₀).totalWeight .instruments (spongeMass Hh Hk Hk')
        (IFreeM.substitute (parToSeq (recHPort X Z S M')) x) ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ y =>
    exact ((runtimeR m₀).par (recHPort X Z S M')).totalWeight_pure _ y ρ |>.trans
      ((runtimeR m₀).totalWeight_pure _ y ρ).symm
  | primBind _ o k ih =>
    exact (((runtimeR m₀).par (recHPort X Z S M')).totalWeight_primBind _ o k ρ).trans
      ((tsum_congr fun b ↦ ih b (((LocalSig.Interp.instruments o).frame _).posSemidef_branch_apply
        b hρ)).trans ((runtimeR m₀).totalWeight_primBind _ o
          (fun b ↦ IFreeM.substitute (parToSeq (recHPort X Z S M')) (k b)) ρ).symm)
  | queryBind _ i E ℓ k ih =>
    rcases i with p | ⟨w, f⟩
    · exact (((runtimeR m₀).par (recHPort X Z S M')).totalWeight_queryBind _ (.inl p) E ℓ k
        ρ).trans ((congrArg₂ (· + ·) (congrFun (parSpongeMass_inl Hh Hk Hk' p) _)
          (tsum_congr fun r ↦ ih r (((runtimeR m₀).queryStep p E ℓ).posSemidef_branch_apply r
            hρ))).trans ((runtimeR m₀).totalWeight_queryBind _ p E ℓ
              (fun r ↦ IFreeM.substitute (parToSeq (recHPort X Z S M')) (k r)) ρ).symm)
    · obtain rfl : f = fun _ ↦ () := funext fun _ ↦ rfl
      have hq := (runtimeR m₀).queryStep_par_round (recHPort X Z S M') (fun _ ↦ ()) E ℓ
      have hb : ∀ r, (((runtimeR m₀).par (recHPort X Z S M')).queryStep
          (.inr (.round w fun _ ↦ ())) E ℓ).branch r ρ = ((runtimeR m₀).run₂ .instruments
            (seqCalls (fun _ : Fin w ↦ recHPort X Z S M' ()) E
              (B := QReg.of (roundOut (recHwSpec X Z S M')
                (fun _ : Fin w ↦ recHPort X Z S M' ()) × E)) ℓ (Equiv.refl _))).branch r ρ :=
        fun r ↦ congrArg (fun T ↦ DSubInstrument.branch T r ρ) hq
      have hR : (runtimeR m₀).totalWeight .instruments (spongeMass Hh Hk Hk')
          (IFreeM.substitute (parToSeq (recHPort X Z S M'))
            (QuantumComp.queryBind (.inr (.round w fun _ ↦ ())) E ℓ k)) ρ = _ :=
        (congrArg (fun y ↦ (runtimeR m₀).totalWeight .instruments (spongeMass Hh Hk Hk') y ρ)
          (IFreeM.bind_assoc _ _ _)).trans
          (totalWeight_spongeMass_bind_seqCalls Hh Hk Hk' m₀ E ℓ
            (B := QReg.of (roundOut (recHwSpec X Z S M') (fun _ : Fin w ↦ recHPort X Z S M' ()) ×
              E)) (Equiv.refl _) _ hρ)
      refine (((runtimeR m₀).par (recHPort X Z S M')).totalWeight_queryBind _
        (.inr (.round w fun _ ↦ ())) E ℓ k ρ).trans (Eq.trans ?_ hR.symm)
      refine congrArg₂ (· + ·) (congrFun (parSpongeMass_round_eq Hh Hk Hk' _) _)
        (tsum_congr fun r ↦ ?_)
      rw [hb r]
      exact ih r (((runtimeR m₀).run₂ .instruments _).posSemidef_branch_apply r hρ)

end transfer

end Quantum.Xmss.Hybrid

end
