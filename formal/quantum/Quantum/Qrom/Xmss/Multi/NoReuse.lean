module

public import Quantum.Qrom.SufCma.MultiOne
public import Quantum.Qrom.Xmss.NoReuse

@[expose] public section

/-!
# Multi-user adversaries that never reuse a leaf of a user, in the QROM

leanXMSS's multi-user game (`Quantum.Qrom.SufCma.Multi.muGame` with the validity `xmssValid`: no
leaf index requested twice) loses on a run that requests some leaf of some user twice. So an
adversary may as well never do it: `refuseMu A` answers a request of an already requested leaf of
the same user itself, with `none` and the register relabel of `signTree`, without asking the
signer, and wins at least as often as `A`. The single-user argument
(`Quantum.Qrom.Xmss.winProb_le_winProb_refuse`) with the requested pairs `(user, leaf)` in place of
the requested leaves.

* `MuAdversary n`, `xmssValid`: leanXMSS's multi-user adversaries and its transcript validity.
* `leafChargeAt i ℓ`: the requests of leaf `ℓ` to user `i` cost one, everything else nothing.
* `NoLeafReuseMu A`: on every path, each leaf of each user is requested at most once.
* `refuseMuFrom F x`, `refuseMu A`: answer the requests of already requested pairs (those in `F`,
  then those requested so far) locally with `none`.

## Main statements

* `noLeafReuseMu_refuseMu`: `refuseMu A` never reuses a leaf of a user.
* `isChargeBound_refuseMu`: `refuseMu A` keeps every charge bound of `A`.
* `muWinProb_le_refuseMu`: `muWinProb xmssRom xmssValid n A ≤ muWinProb xmssRom xmssValid n
  (refuseMu A)`.
* `xmss_muQuantumStronglyUnforgeable_one_iff`: with one user, leanXMSS's multi-user SUF-CMA is the
  single-user one.
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal

namespace Quantum.Qrom.Xmss.Multi

open LeanXmss HashSig
open Quantum.Xmss (obsWeight obsWeight_run_bind obsWeight_run_bind₂ obsWeight_run_pure₂
  not_noLeafIndexReused_append)
open Quantum.Qrom.SufCma.Multi (MuPort muAdvSpec cmdCharge MuSignLog muLogSigns muLogAfter
  muChallenged muChallenge muGame muWinProb)

/-- leanXMSS's multi-user quantum SUF-CMA adversary against `n` users in the QROM. -/
abbrev MuAdversary (n : ℕ) :=
  SufCma.Multi.MuAdversary n PublicKey SigningRequest (Option Signature) Forgery

/-- leanXMSS's transcript validity: no leaf index requested twice. -/
def xmssValid (log : SignLog) : Bool :=
  decide (SigningTranscript.NoLeafIndexReused log)

/-- The winning condition implies the validity. -/
theorem xmssValid_of_winningCondition (log : SignLog) (f : Forgery)
    (h : xmssRom.winningCondition log f = true) : xmssValid log = true :=
  decide_eq_true (of_decide_eq_true h).1

/-- **One user: leanXMSS's multi-user SUF-CMA is its single-user SUF-CMA.** -/
theorem xmss_muQuantumStronglyUnforgeable_one_iff {limit : ℕ} {bound : ℕ → ℝ≥0∞} :
    SufCma.Multi.MuQuantumStronglyUnforgeable xmssRom xmssValid 1 limit limit bound ↔
      SufCma.QuantumStronglyUnforgeable xmssRom limit bound :=
  SufCma.Multi.muQuantumStronglyUnforgeable_one_iff xmssRom xmssValid
    xmssValid_of_winningCondition

variable {n : ℕ}

-- The adversary's commands, as an indexed polynomial functor.
set_option quotPrecheck false in
local notation "MuP" n => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (muAdvSpec n SigningRequest (Option Signature))

/-! ## Leaf charges and refused requests -/

/-- The charge of the requests of leaf `ℓ` to user `i`: one per such request, nothing otherwise. -/
def leafChargeAt (i : Fin n) (ℓ : LeafIndex) : MuPort n SigningRequest → ℕ
  | .hash => 0
  | .sign j r => if j = i ∧ r.leafIndex = ℓ then 1 else 0

/-- **No leaf reuse**: on every path, no leaf index of a user is requested twice. -/
def NoLeafReuseMu (A : MuAdversary n) : Prop :=
  ∀ pks i ℓ, IFreeM.IsChargeBound (A pks) (cmdCharge (leafChargeAt i ℓ)) 1

/-- The local stand-in for the refused request `r` to user `i` on the register `A ≃ In × E`: the
register relabel of `signTree`, with one outcome and no call. -/
noncomputable def refuseOpMu (i : Fin n) (r : SigningRequest) (E : QReg) {A : QReg}
    (ℓ : A ≃ (muAdvSpec n SigningRequest (Option Signature)).In (.sign i r) × E) :
    LocalSig.instruments.{0}.Op A :=
  ⟨Unit, fun _ ↦ QReg.of ((muAdvSpec n SigningRequest (Option Signature)).Out (.sign i r) × E),
    SubInstrument.relabel ℓ⟩

/-- **Refuse reused pairs**: the same commands, except that a request to user `i` of a leaf `ℓ`
with `(i, ℓ)` in `F` or requested before on the path is answered `none` by `refuseOpMu`, without a
signer call. -/
noncomputable def refuseMuFrom {X : QReg → Type} :
    {A : QReg} → Finset (Fin n × LeafIndex) → IFreeM (MuP n) X A → IFreeM (MuP n) X A
  | _, _, .pure x => .pure x
  | _, F, .liftBind (.prim o) next => .liftBind (.prim o) fun b ↦ refuseMuFrom F (next b)
  | _, F, .liftBind (.query .hash E ℓ) next =>
      .liftBind (.query .hash E ℓ) fun b ↦ refuseMuFrom F (next b)
  | _, F, .liftBind (.query (.sign i r) E ℓ) next =>
      if (i, r.leafIndex) ∈ F then
        .liftBind (.prim (refuseOpMu i r E ℓ)) fun _ ↦ refuseMuFrom F (next (ULift.up none))
      else
        .liftBind (.query (.sign i r) E ℓ) fun b ↦ refuseMuFrom (insert (i, r.leafIndex) F) (next b)

/-- **The adversary that never reuses a leaf of a user**: `A` with the requests of already
requested pairs answered `none` locally. -/
noncomputable def refuseMu (A : MuAdversary n) : MuAdversary n :=
  fun pks ↦ refuseMuFrom ∅ (A pks)

section sign

variable {X : QReg → Type} {A : QReg} {F : Finset (Fin n × LeafIndex)} {i : Fin n}
  {r : SigningRequest} {E : QReg}
  {ℓ : A ≃ (muAdvSpec n SigningRequest (Option Signature)).In (.sign i r) × E}
  {next : (b : (MuP n).B A (QuantumComp.Cmd.query (MuPort.sign i r) E ℓ)) →
    IFreeM (MuP n) X ((MuP n).src A (QuantumComp.Cmd.query (MuPort.sign i r) E ℓ) b)}

/-- A request of a pair in `F` is refused. -/
theorem refuseMuFrom_sign_of_mem (h : (i, r.leafIndex) ∈ F) :
    refuseMuFrom F (IFreeM.liftBind (QuantumComp.Cmd.query (MuPort.sign i r) E ℓ) next) =
      .liftBind (.prim (refuseOpMu i r E ℓ)) fun _ ↦ refuseMuFrom F (next (ULift.up none)) := by
  rw [refuseMuFrom, ite_eq_left h]

/-- A request of a pair outside `F` is forwarded, and its pair joins `F`. -/
theorem refuseMuFrom_sign_of_notMem (h : (i, r.leafIndex) ∉ F) :
    refuseMuFrom F (IFreeM.liftBind (QuantumComp.Cmd.query (MuPort.sign i r) E ℓ) next) =
      .liftBind (.query (.sign i r) E ℓ) fun b ↦
        refuseMuFrom (insert (i, r.leafIndex) F) (next b) := by
  rw [refuseMuFrom, ite_eq_right h]

end sign

/-- Refusing keeps every charge bound: a refused request becomes a local operation, which costs
nothing. -/
theorem isChargeBound_refuseMuFrom {X : QReg → Type} {c : MuPort n SigningRequest → ℕ}
    {A : QReg} (x : IFreeM (MuP n) X A) (F : Finset (Fin n × LeafIndex)) {m : ℕ}
    (h : IFreeM.IsChargeBound x (cmdCharge c) m) :
    IFreeM.IsChargeBound (refuseMuFrom F x) (cmdCharge c) m := by
  induction x using IFreeM.inductionOn generalizing F m with
  | pure _ _ => trivial
  | liftBind A c' next ih =>
    rcases c' with o | ⟨_ | ⟨i, r⟩, E, ℓ⟩
    · exact ⟨h.1, fun b ↦ ih b F (h.2 b)⟩
    · exact ⟨h.1, fun b ↦ ih b F (h.2 b)⟩
    · by_cases hr : (i, r.leafIndex) ∈ F
      · rw [refuseMuFrom_sign_of_mem hr]
        exact ⟨Nat.zero_le _, fun _ ↦ (ih _ F (h.2 _)).mono (Nat.sub_le m _)⟩
      · rw [refuseMuFrom_sign_of_notMem hr]
        exact ⟨h.1, fun b ↦ ih b _ (h.2 b)⟩

/-- The requests of leaf `ℓ` to user `i` after refusing from `F`: none if `(i, ℓ) ∈ F`, else at
most one. -/
theorem isChargeBound_leafChargeAt_refuseMuFrom {X : QReg → Type} {A : QReg}
    (x : IFreeM (MuP n) X A) (F : Finset (Fin n × LeafIndex)) (i : Fin n) (ℓ : LeafIndex) :
    IFreeM.IsChargeBound (refuseMuFrom F x) (cmdCharge (leafChargeAt i ℓ))
      (if (i, ℓ) ∈ F then 0 else 1) := by
  induction x using IFreeM.inductionOn generalizing F with
  | pure _ _ => trivial
  | liftBind A c next ih =>
    rcases c with o | ⟨_ | ⟨j, r⟩, E, ℓ'⟩
    · exact ⟨Nat.zero_le _, fun b ↦ (ih b F).mono (Nat.le_of_eq (Nat.sub_zero _).symm)⟩
    · exact ⟨Nat.zero_le _, fun b ↦ (ih b F).mono (Nat.le_of_eq (Nat.sub_zero _).symm)⟩
    · by_cases hr : (j, r.leafIndex) ∈ F
      · rw [refuseMuFrom_sign_of_mem hr]
        exact ⟨Nat.zero_le _, fun _ ↦ (ih _ F).mono (Nat.le_of_eq (Nat.sub_zero _).symm)⟩
      · rw [refuseMuFrom_sign_of_notMem hr]
        refine ⟨?_, fun b ↦ (ih b _).mono ?_⟩
        · by_cases hℓ : j = i ∧ r.leafIndex = ℓ
          · obtain ⟨rfl, rfl⟩ := hℓ
            simp [cmdCharge, leafChargeAt, hr]
          · simp [cmdCharge, leafChargeAt, hℓ]
        · by_cases hℓ : j = i ∧ r.leafIndex = ℓ
          · obtain ⟨rfl, rfl⟩ := hℓ
            simp [cmdCharge, leafChargeAt, hr]
          · have hne : (i, ℓ) ≠ (j, r.leafIndex) := fun h ↦
              hℓ ⟨(Prod.ext_iff.mp h).1.symm, (Prod.ext_iff.mp h).2.symm⟩
            simp [cmdCharge, leafChargeAt, hℓ, hne]

/-- **`refuseMu A` never reuses a leaf of a user.** -/
theorem noLeafReuseMu_refuseMu (A : MuAdversary n) : NoLeafReuseMu (refuseMu A) :=
  fun pks i ℓ ↦ (isChargeBound_leafChargeAt_refuseMuFrom (A pks) ∅ i ℓ).mono (by simp)

/-- **`refuseMu A` keeps every charge bound of `A`**: its hash calls, its requests to each user
and its requests overall. -/
theorem isChargeBound_refuseMu {c : MuPort n SigningRequest → ℕ} {m : ℕ} {A : MuAdversary n}
    {pks : Fin n → PublicKey} (h : IFreeM.IsChargeBound (A pks) (cmdCharge c) m) :
    IFreeM.IsChargeBound (refuseMu A pks) (cmdCharge c) m :=
  isChargeBound_refuseMuFrom (A pks) ∅ h

/-! ## Transcripts -/

/-- A transcript in which some user's transcript repeats a leaf. -/
def Reused (log : MuSignLog n SigningRequest (Option Signature)) : Prop :=
  ∃ j, ¬SigningTranscript.NoLeafIndexReused (log.user j)

/-- The leaf map of `withMuSignLog`: the value with the transcript. -/
def muSignLeaf {B : QReg} {α : Type} (u : QReg) (l : QuantumComp₂.Leaf B α u)
    (log : MuSignLog n SigningRequest (Option Signature)) :
    QuantumComp₂.Leaf B (α × MuSignLog n SigningRequest (Option Signature)) u :=
  ⟨l.1, (l.2, log)⟩

/-- A transcript with a repeated leaf of a user keeps it after any command. -/
theorem reused_muLogAfter {A : QReg}
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (muAdvSpec n SigningRequest (Option Signature))
      A) (b : c.Resp) {log : MuSignLog n SigningRequest (Option Signature)} (h : Reused log) :
    Reused (muLogAfter c b log) := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, ?_⟩
  rcases c with o | ⟨_ | ⟨i, r⟩, E, ℓ⟩
  · exact hj
  · exact hj
  · change ¬SigningTranscript.NoLeafIndexReused (MuSignLog.user (log ++ [⟨(i, r), b.down⟩]) j)
    rw [MuSignLog.user_append_singleton]
    exact fun hn ↦ hj (List.Nodup.sublist ((List.sublist_append_left _ _).map _) hn)

/-- A reused transcript is not valid. -/
theorem allValid_eq_false_of_reused {log : MuSignLog n SigningRequest (Option Signature)}
    (h : Reused log) : log.allValid xmssValid = false := by
  obtain ⟨j, hj⟩ := h
  exact decide_eq_false fun hv ↦ hj (of_decide_eq_true (hv j))

/-- The requested pairs after a fresh request `r` to user `i`. -/
theorem mem_user_append_of_mem_insert {log : MuSignLog n SigningRequest (Option Signature)}
    {F : Finset (Fin n × LeafIndex)}
    (hF : ∀ p ∈ F, p.2 ∈ (log.user p.1).map fun q ↦ q.1.leafIndex) (i : Fin n)
    (r : SigningRequest) (s : Option Signature) :
    ∀ p ∈ insert (i, r.leafIndex) F,
      p.2 ∈ ((log ++ [⟨(i, r), s⟩] : MuSignLog n SigningRequest (Option Signature)).user
        p.1).map fun q ↦ q.1.leafIndex := by
  intro p h
  rw [MuSignLog.user_append_singleton, List.map_append, List.mem_append]
  rcases Finset.mem_insert.mp h with rfl | h
  · exact Or.inr (by simp)
  · exact Or.inl (hF p h)

/-! ## Reused leaves lose -/

section win

variable (R : QuantumRuntime romSpec) (sks : Fin n → SecretKey)

/-- The weights of the challenged commands below a common first command compare as the weights
below its answers. -/
theorem obsWeight_muChallenged_liftBind_le {A B C : QReg} {γ β : Type} (c : (MuP n).A A)
    {next next' : (b : (MuP n).B A c) →
      IFreeM (MuP n) (QuantumComp₂.Leaf B γ) ((MuP n).src A c b)}
    {k : γ → QComp romSpec B C β} {g : (Σ u, QuantumComp₂.Leaf C β u) → ℝ≥0∞}
    (h : ∀ b σ,
      obsWeight (R.run .instruments ((muChallenged xmssRom sks (next b)).bind k)) σ g ≤
        obsWeight (R.run .instruments ((muChallenged xmssRom sks (next' b)).bind k)) σ g)
    (ρ : SubState (A × R.D)) :
    obsWeight (R.run .instruments
        ((muChallenged xmssRom sks (IFreeM.liftBind c next)).bind k)) ρ g ≤
      obsWeight (R.run .instruments
        ((muChallenged xmssRom sks (IFreeM.liftBind c next')).bind k)) ρ g := by
  simp only [muChallenged, IFreeM.substitute_liftBind, QuantumComp₂.bind, FreeM₂.bind,
    IFreeM.bind_assoc]
  rw [obsWeight_run_bind, obsWeight_run_bind]
  refine ENNReal.tsum_le_tsum fun p ↦ ?_
  obtain ⟨t, b, rfl⟩ := p
  exact h b _

/-- The weight of the challenged commands below a first command vanishes when it vanishes below
each of its answers. -/
theorem obsWeight_muChallenged_liftBind_eq_zero {A B C : QReg} {γ β : Type} (c : (MuP n).A A)
    {next : (b : (MuP n).B A c) → IFreeM (MuP n) (QuantumComp₂.Leaf B γ) ((MuP n).src A c b)}
    {k : γ → QComp romSpec B C β} {g : (Σ u, QuantumComp₂.Leaf C β u) → ℝ≥0∞}
    (h : ∀ b σ,
      obsWeight (R.run .instruments ((muChallenged xmssRom sks (next b)).bind k)) σ g = 0)
    (ρ : SubState (A × R.D)) :
    obsWeight (R.run .instruments
        ((muChallenged xmssRom sks (IFreeM.liftBind c next)).bind k)) ρ g = 0 := by
  simp only [muChallenged, IFreeM.substitute_liftBind, QuantumComp₂.bind, FreeM₂.bind,
    IFreeM.bind_assoc]
  rw [obsWeight_run_bind]
  refine ENNReal.tsum_eq_zero.mpr fun p ↦ ?_
  obtain ⟨t, b, rfl⟩ := p
  exact h b _

variable {B C : QReg} {α β : Type}
  {k : α × MuSignLog n SigningRequest (Option Signature) → QComp romSpec B C β}
  {g : (Σ u, QuantumComp₂.Leaf C β u) → ℝ≥0∞}

/-- **Reused leaves lose**: when the continuation `k` has weight zero on reused transcripts, the
challenged program from such a transcript has weight zero. -/
theorem obsWeight_muReused (hk : ∀ a log, Reused log → ∀ σ,
      obsWeight (R.run .instruments (k (a, log))) σ g = 0)
    {A : QReg} (x : IFreeM (MuP n) (QuantumComp₂.Leaf B α) A)
    (log : MuSignLog n SigningRequest (Option Signature)) (hlog : Reused log)
    (ρ : SubState (A × R.D)) :
    obsWeight (R.run .instruments
      ((muChallenged xmssRom sks (muLogSigns muSignLeaf x log)).bind k)) ρ g = 0 := by
  induction x using IFreeM.inductionOn generalizing log with
  | pure A v =>
    obtain ⟨rfl, a⟩ := v
    exact hk a log hlog ρ
  | liftBind A c next ih =>
    exact obsWeight_muChallenged_liftBind_eq_zero R sks c
      (fun b σ ↦ ih b _ (reused_muLogAfter c b hlog) σ) ρ

/-- **Refusing does not lower the weight**, from a transcript `log` containing the pairs `F`: the
same commands, except at a refused request, below which the original program has weight zero
(`obsWeight_muReused`). -/
theorem obsWeight_le_refuseMuFrom (hk : ∀ a log, Reused log → ∀ σ,
      obsWeight (R.run .instruments (k (a, log))) σ g = 0)
    {A : QReg} (x : IFreeM (MuP n) (QuantumComp₂.Leaf B α) A)
    (log : MuSignLog n SigningRequest (Option Signature)) (F : Finset (Fin n × LeafIndex))
    (hF : ∀ p ∈ F, p.2 ∈ (log.user p.1).map fun q ↦ q.1.leafIndex) (ρ : SubState (A × R.D)) :
    obsWeight (R.run .instruments
        ((muChallenged xmssRom sks (muLogSigns muSignLeaf x log)).bind k)) ρ g ≤
      obsWeight (R.run .instruments
        ((muChallenged xmssRom sks (muLogSigns muSignLeaf (refuseMuFrom F x) log)).bind k))
        ρ g := by
  induction x using IFreeM.inductionOn generalizing log F with
  | pure _ _ => exact le_rfl
  | liftBind A c next ih =>
    rcases c with o | ⟨_ | ⟨i, r⟩, E, ℓ⟩
    · exact obsWeight_muChallenged_liftBind_le R sks _ (fun b σ ↦ ih b log F hF σ) ρ
    · exact obsWeight_muChallenged_liftBind_le R sks _ (fun b σ ↦ ih b log F hF σ) ρ
    · by_cases hr : (i, r.leafIndex) ∈ F
      · refine (obsWeight_muChallenged_liftBind_eq_zero R sks _ (fun b σ ↦ ?_) ρ).le.trans
          zero_le
        refine obsWeight_muReused R sks hk (next b) _ ⟨i, ?_⟩ σ
        change ¬SigningTranscript.NoLeafIndexReused
          (MuSignLog.user (log ++ [⟨(i, r), b.down⟩]) i)
        rw [MuSignLog.user_append_singleton, ite_eq_left rfl]
        exact not_noLeafIndexReused_append (hF _ hr) b.down
      · rw [refuseMuFrom_sign_of_notMem hr]
        exact obsWeight_muChallenged_liftBind_le R sks _
          (fun b σ ↦ ih b _ _ (mem_user_append_of_mem_insert hF i r b.down) σ) ρ

/-- The verification stage of `muGame` loses on a reused transcript. -/
theorem obsWeight_muVerify_reused (pk : PublicKey) (a : Fin n × Forgery)
    {log : MuSignLog n SigningRequest (Option Signature)} (h : Reused log)
    (σ : SubState (QReg.of Unit × R.D)) :
    obsWeight (R.run .instruments
      ((((xmssRom.verify pk a.2).toQuantumAt (SufCma.romImpl _)).bind fun verified ↦
        QuantumComp₂.pure (xmssRom.winningCondition (log.user a.1) a.2 &&
          log.allValid xmssValid && verified)) :
        QComp romSpec (QReg.of Unit) (QReg.of Unit) Bool))
      σ (fun p ↦ ({true} : Set Bool).indicator 1 p.2.2) = 0 := by
  rw [obsWeight_run_bind₂]
  refine ENNReal.tsum_eq_zero.mpr fun v ↦ ?_
  rw [obsWeight_run_pure₂, allValid_eq_false_of_reused h]
  simp

/-- **Per runtime, `refuseMu A` wins the game with at least the weight of `A`.** -/
theorem obsWeight_muGame_le (S0 : Fin n → MasterSeed) (A : MuAdversary n)
    (σ : SubState (QReg.of Unit × R.D)) :
    obsWeight (R.run .instruments (muGame xmssRom xmssValid S0 A)) σ
        (fun p ↦ ({true} : Set Bool).indicator 1 p.2.2) ≤
      obsWeight (R.run .instruments (muGame xmssRom xmssValid S0 (refuseMu A))) σ
        (fun p ↦ ({true} : Set Bool).indicator 1 p.2.2) := by
  unfold muGame
  rw [obsWeight_run_bind₂, obsWeight_run_bind₂]
  refine ENNReal.tsum_le_tsum fun keys ↦ ?_
  refine obsWeight_le_refuseMuFrom R (fun i ↦ (keys i).2) ?_ (A fun i ↦ (keys i).1) [] ∅
    (by simp) _
  intro a log h σ'
  exact obsWeight_muVerify_reused R (keys a.1).1 a h σ'

end win

/-- **Refusing reused leaves does not lower the multi-user winning probability.** -/
theorem muWinProb_le_refuseMu (A : MuAdversary n) :
    muWinProb xmssRom xmssValid n A ≤ muWinProb xmssRom xmssValid n (refuseMu A) := by
  unfold muWinProb
  exact Finset.sum_le_sum fun S0 _ ↦ mul_le_mul_right (qromEvalDistMap_true_le _ _ _ _
    fun H ↦ obsWeight_muGame_le (additiveOracleRuntime H) S0 A _) _

end Quantum.Qrom.Xmss.Multi

end
