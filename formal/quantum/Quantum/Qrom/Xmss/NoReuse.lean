module

public import Quantum.Qrom.SufCma.Game
public import Quantum.Qrom.Xmss.Scheme
public import Quantum.Xmss.NoReuse

@[expose] public section

/-!
# Adversaries that never reuse a leaf, in the QROM

A run that requests some leaf index twice loses the SUF-CMA game (`NoLeafIndexReused` in the
winning condition). So an adversary may as well never do it: `refuse A` answers a request of an
already requested leaf itself, with `none` and the register relabel of `signTree`, without asking
the signer, and wins at least as often as `A`. The QRPM argument (`Quantum.Xmss.NoReuse`) with
the hash port `.hash` in place of the permutation ports; the observed weights (`obsWeight`) and
the transcript facts are reused.

* `Adversary`, `SignLog`: leanXMSS's quantum adversaries and transcripts in the QROM.
* `leafCharge ℓ`: the requests of leaf `ℓ` cost one, everything else nothing.
* `NoLeafReuse A`: on every path, each leaf is requested at most once.
* `refuseFrom F x`, `refuse A`: answer the requests of already requested leaves (those in `F`,
  then those requested so far) locally with `none`.

## Main statements

* `noLeafReuse_refuse`: `refuse A` never reuses a leaf.
* `isChargeBound_refuse`: `refuse A` keeps every charge bound of `A` (a refused request becomes
  a local operation, which costs nothing).
* `winProb_le_winProb_refuse`: `winProb xmssRom A ≤ winProb xmssRom (refuse A)`. Per function
  `H`, by induction over the adversary's tree with its transcript: at a reused request every leaf
  of the game below has a transcript with a repeated leaf, so it returns `false`; elsewhere both
  games make the same command.
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal

namespace Quantum.Qrom.Xmss

open LeanXmss HashSig
open Quantum.Xmss (obsWeight obsWeight_run_bind obsWeight_run_bind₂ obsWeight_run_pure₂
  not_noLeafIndexReused_append mem_map_append_of_mem_insert)

/-- leanXMSS's quantum SUF-CMA adversary in the QROM. -/
abbrev Adversary := SufCma.Adversary PublicKey SigningRequest (Option Signature) Forgery

/-- leanXMSS's signing transcript. -/
abbrev SignLog := SufCma.SignLog SigningRequest (Option Signature)

-- The adversary's commands, as an indexed polynomial functor.
set_option quotPrecheck false in
local notation "AdvP" => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (SufCma.advSpec SigningRequest (Option Signature))

/-! ## Leaf charges and refused requests -/

/-- The charge of the requests of leaf `ℓ`: one per request of `ℓ`, nothing otherwise. -/
def leafCharge (ℓ : LeafIndex) : SufCma.AdvPort SigningRequest → ℕ
  | .hash => 0
  | .sign r => if r.leafIndex = ℓ then 1 else 0

/-- **No leaf reuse**: on every path, no leaf index is requested twice. -/
def NoLeafReuse (A : Adversary) : Prop :=
  ∀ pk ℓ, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge (leafCharge ℓ)) 1

/-- The local stand-in for the refused request `r` on the register `A ≃ In × E`: the register
relabel of `signTree`, with one outcome and no call. -/
noncomputable def refuseOp (r : SigningRequest) (E : QReg) {A : QReg}
    (ℓ : A ≃ (SufCma.advSpec SigningRequest (Option Signature)).In (.sign r) × E) :
    LocalSig.instruments.{0}.Op A :=
  ⟨Unit, fun _ ↦ QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E),
    SubInstrument.relabel ℓ⟩

/-- **Refuse reused leaves**: the same commands, except that a request of a leaf in `F` or
requested before on the path is answered `none` by `refuseOp`, without a signer call. -/
noncomputable def refuseFrom {X : QReg → Type} :
    {A : QReg} → Finset LeafIndex → IFreeM AdvP X A → IFreeM AdvP X A
  | _, _, .pure x => .pure x
  | _, F, .liftBind (.prim o) next => .liftBind (.prim o) fun b ↦ refuseFrom F (next b)
  | _, F, .liftBind (.query .hash E ℓ) next =>
      .liftBind (.query .hash E ℓ) fun b ↦ refuseFrom F (next b)
  | _, F, .liftBind (.query (.sign r) E ℓ) next =>
      if r.leafIndex ∈ F then
        .liftBind (.prim (refuseOp r E ℓ)) fun _ ↦ refuseFrom F (next (ULift.up none))
      else .liftBind (.query (.sign r) E ℓ) fun b ↦ refuseFrom (insert r.leafIndex F) (next b)

/-- **The adversary that never reuses a leaf**: `A` with the requests of already requested
leaves answered `none` locally. -/
noncomputable def refuse (A : Adversary) : Adversary :=
  fun pk ↦ refuseFrom ∅ (A pk)

section sign

variable {X : QReg → Type} {A : QReg} {F : Finset LeafIndex} {r : SigningRequest} {E : QReg}
  {ℓ : A ≃ (SufCma.advSpec SigningRequest (Option Signature)).In (.sign r) × E}
  {next : (b : (AdvP).B A (QuantumComp.Cmd.query (SufCma.AdvPort.sign r) E ℓ)) →
    IFreeM AdvP X ((AdvP).src A (QuantumComp.Cmd.query (SufCma.AdvPort.sign r) E ℓ) b)}

/-- A request of a leaf in `F` is refused. -/
theorem refuseFrom_sign_of_mem (h : r.leafIndex ∈ F) :
    refuseFrom F (IFreeM.liftBind (QuantumComp.Cmd.query (SufCma.AdvPort.sign r) E ℓ) next) =
      .liftBind (.prim (refuseOp r E ℓ)) fun _ ↦ refuseFrom F (next (ULift.up none)) := by
  rw [refuseFrom, ite_eq_left h]

/-- A request of a leaf outside `F` is forwarded, and its leaf joins `F`. -/
theorem refuseFrom_sign_of_notMem (h : r.leafIndex ∉ F) :
    refuseFrom F (IFreeM.liftBind (QuantumComp.Cmd.query (SufCma.AdvPort.sign r) E ℓ) next) =
      .liftBind (.query (.sign r) E ℓ) fun b ↦ refuseFrom (insert r.leafIndex F) (next b) := by
  rw [refuseFrom, ite_eq_right h]

end sign

/-- Refusing keeps every charge bound: a refused request becomes a local operation, which costs
nothing. -/
theorem isChargeBound_refuseFrom {X : QReg → Type} {c : SufCma.AdvPort SigningRequest → ℕ}
    {A : QReg} (x : IFreeM AdvP X A) (F : Finset LeafIndex) {n : ℕ}
    (h : IFreeM.IsChargeBound x (SufCma.cmdCharge c) n) :
    IFreeM.IsChargeBound (refuseFrom F x) (SufCma.cmdCharge c) n := by
  induction x using IFreeM.inductionOn generalizing F n with
  | pure _ _ => trivial
  | liftBind A c' next ih =>
    rcases c' with o | ⟨_ | r, E, ℓ⟩
    · exact ⟨h.1, fun b ↦ ih b F (h.2 b)⟩
    · exact ⟨h.1, fun b ↦ ih b F (h.2 b)⟩
    · by_cases hr : r.leafIndex ∈ F
      · rw [refuseFrom_sign_of_mem hr]
        exact ⟨Nat.zero_le _, fun _ ↦ (ih _ F (h.2 _)).mono (Nat.sub_le n _)⟩
      · rw [refuseFrom_sign_of_notMem hr]
        exact ⟨h.1, fun b ↦ ih b _ (h.2 b)⟩

/-- The requests of leaf `ℓ` after refusing from `F`: none if `ℓ ∈ F`, else at most one. -/
theorem isChargeBound_leafCharge_refuseFrom {X : QReg → Type} {A : QReg}
    (x : IFreeM AdvP X A) (F : Finset LeafIndex) (ℓ : LeafIndex) :
    IFreeM.IsChargeBound (refuseFrom F x) (SufCma.cmdCharge (leafCharge ℓ))
      (if ℓ ∈ F then 0 else 1) := by
  induction x using IFreeM.inductionOn generalizing F with
  | pure _ _ => trivial
  | liftBind A c next ih =>
    rcases c with o | ⟨_ | r, E, ℓ'⟩
    · exact ⟨Nat.zero_le _, fun b ↦ (ih b F).mono (Nat.le_of_eq (Nat.sub_zero _).symm)⟩
    · exact ⟨Nat.zero_le _, fun b ↦ (ih b F).mono (Nat.le_of_eq (Nat.sub_zero _).symm)⟩
    · by_cases hr : r.leafIndex ∈ F
      · rw [refuseFrom_sign_of_mem hr]
        exact ⟨Nat.zero_le _, fun _ ↦ (ih _ F).mono (Nat.le_of_eq (Nat.sub_zero _).symm)⟩
      · rw [refuseFrom_sign_of_notMem hr]
        refine ⟨?_, fun b ↦ (ih b _).mono ?_⟩
        · by_cases hℓ : r.leafIndex = ℓ
          · subst hℓ
            simp [SufCma.cmdCharge, leafCharge, hr]
          · simp [SufCma.cmdCharge, leafCharge, hℓ]
        · by_cases hℓ : r.leafIndex = ℓ
          · subst hℓ
            simp [SufCma.cmdCharge, leafCharge, hr]
          · simp [SufCma.cmdCharge, leafCharge, hℓ, Ne.symm hℓ]

/-- **`refuse A` never reuses a leaf.** -/
theorem noLeafReuse_refuse (A : Adversary) : NoLeafReuse (refuse A) := fun pk ℓ ↦
  (isChargeBound_leafCharge_refuseFrom (A pk) ∅ ℓ).mono (by simp)

/-- **`refuse A` keeps every charge bound of `A`**, in particular its hash calls (`hashCharge`)
and signing requests (`signCharge`). -/
theorem isChargeBound_refuse {c : SufCma.AdvPort SigningRequest → ℕ} {n : ℕ} {A : Adversary}
    {pk : PublicKey} (h : IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge c) n) :
    IFreeM.IsChargeBound (refuse A pk) (SufCma.cmdCharge c) n :=
  isChargeBound_refuseFrom (A pk) ∅ h

/-! ## Transcripts -/

/-- The leaf map of `withSignLog`: the value with the transcript. -/
def signLeaf {B : QReg} {α : Type} (u : QReg) (l : QuantumComp₂.Leaf B α u) (log : SignLog) :
    QuantumComp₂.Leaf B (α × SignLog) u :=
  ⟨l.1, (l.2, log)⟩

/-- A transcript with a repeated leaf keeps it after any command. -/
theorem not_noLeafIndexReused_logAfter {A : QReg}
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (SufCma.advSpec SigningRequest (Option Signature))
      A) (b : c.Resp) {log : SignLog}
    (h : ¬SigningTranscript.NoLeafIndexReused log) :
    ¬SigningTranscript.NoLeafIndexReused (SufCma.logAfter c b log) := by
  rcases c with o | ⟨_ | r, E, ℓ⟩
  · exact h
  · exact h
  · exact fun hn ↦ h (List.Nodup.sublist ((List.sublist_append_left _ _).map _) hn)

/-! ## Reused leaves lose -/

section win

variable (R : QuantumRuntime romSpec) (sk : SecretKey)

/-- The weights of the challenged commands below a common first command compare as the weights
below its answers. -/
theorem obsWeight_challenged_liftBind_le {A B C : QReg} {γ β : Type} (c : (AdvP).A A)
    {next next' : (b : (AdvP).B A c) → IFreeM AdvP (QuantumComp₂.Leaf B γ) ((AdvP).src A c b)}
    {k : γ → QComp romSpec B C β} {g : (Σ u, QuantumComp₂.Leaf C β u) → ℝ≥0∞}
    (h : ∀ b σ,
      obsWeight (R.run .instruments ((SufCma.challenged xmssRom sk (next b)).bind k)) σ g ≤
        obsWeight (R.run .instruments ((SufCma.challenged xmssRom sk (next' b)).bind k)) σ g)
    (ρ : SubState (A × R.D)) :
    obsWeight (R.run .instruments
        ((SufCma.challenged xmssRom sk (IFreeM.liftBind c next)).bind k)) ρ g ≤
      obsWeight (R.run .instruments
        ((SufCma.challenged xmssRom sk (IFreeM.liftBind c next')).bind k)) ρ g := by
  simp only [SufCma.challenged, IFreeM.substitute_liftBind, QuantumComp₂.bind, FreeM₂.bind,
    IFreeM.bind_assoc]
  rw [obsWeight_run_bind, obsWeight_run_bind]
  refine ENNReal.tsum_le_tsum fun p ↦ ?_
  obtain ⟨t, b, rfl⟩ := p
  exact h b _

/-- The weight of the challenged commands below a first command vanishes when it vanishes below
each of its answers. -/
theorem obsWeight_challenged_liftBind_eq_zero {A B C : QReg} {γ β : Type} (c : (AdvP).A A)
    {next : (b : (AdvP).B A c) → IFreeM AdvP (QuantumComp₂.Leaf B γ) ((AdvP).src A c b)}
    {k : γ → QComp romSpec B C β} {g : (Σ u, QuantumComp₂.Leaf C β u) → ℝ≥0∞}
    (h : ∀ b σ,
      obsWeight (R.run .instruments ((SufCma.challenged xmssRom sk (next b)).bind k)) σ g = 0)
    (ρ : SubState (A × R.D)) :
    obsWeight (R.run .instruments
        ((SufCma.challenged xmssRom sk (IFreeM.liftBind c next)).bind k)) ρ g = 0 := by
  simp only [SufCma.challenged, IFreeM.substitute_liftBind, QuantumComp₂.bind, FreeM₂.bind,
    IFreeM.bind_assoc]
  rw [obsWeight_run_bind]
  refine ENNReal.tsum_eq_zero.mpr fun p ↦ ?_
  obtain ⟨t, b, rfl⟩ := p
  exact h b _

variable {B C : QReg} {α β : Type} {k : α × SignLog → QComp romSpec B C β}
  {g : (Σ u, QuantumComp₂.Leaf C β u) → ℝ≥0∞}

/-- **Reused leaves lose**: when the continuation `k` has weight zero on transcripts with a
repeated leaf, the challenged program from such a transcript has weight zero. -/
theorem obsWeight_reused
    (hk : ∀ a log, ¬SigningTranscript.NoLeafIndexReused log → ∀ σ,
      obsWeight (R.run .instruments (k (a, log))) σ g = 0)
    {A : QReg} (x : IFreeM AdvP (QuantumComp₂.Leaf B α) A)
    (log : SignLog) (hlog : ¬SigningTranscript.NoLeafIndexReused log) (ρ : SubState (A × R.D)) :
    obsWeight (R.run .instruments
      ((SufCma.challenged xmssRom sk (SufCma.logSigns signLeaf x log)).bind k)) ρ g = 0 := by
  induction x using IFreeM.inductionOn generalizing log with
  | pure A v =>
    obtain ⟨rfl, a⟩ := v
    exact hk a log hlog ρ
  | liftBind A c next ih =>
    exact obsWeight_challenged_liftBind_eq_zero R sk c
      (fun b σ ↦ ih b _ (not_noLeafIndexReused_logAfter c b hlog) σ) ρ

/-- **Refusing does not lower the weight**, from a transcript `log` containing the leaves `F`:
the same commands, except at a refused request, below which the original program has weight
zero (`obsWeight_reused`). -/
theorem obsWeight_le_refuseFrom
    (hk : ∀ a log, ¬SigningTranscript.NoLeafIndexReused log → ∀ σ,
      obsWeight (R.run .instruments (k (a, log))) σ g = 0)
    {A : QReg} (x : IFreeM AdvP (QuantumComp₂.Leaf B α) A)
    (log : SignLog) (F : Finset LeafIndex) (hF : ∀ ℓ ∈ F, ℓ ∈ log.map fun q ↦ q.1.leafIndex)
    (ρ : SubState (A × R.D)) :
    obsWeight (R.run .instruments
        ((SufCma.challenged xmssRom sk (SufCma.logSigns signLeaf x log)).bind k)) ρ g ≤
      obsWeight (R.run .instruments
        ((SufCma.challenged xmssRom sk (SufCma.logSigns signLeaf (refuseFrom F x) log)).bind k))
        ρ g := by
  induction x using IFreeM.inductionOn generalizing log F with
  | pure _ _ => exact le_rfl
  | liftBind A c next ih =>
    rcases c with o | ⟨_ | r, E, ℓ⟩
    · exact obsWeight_challenged_liftBind_le R sk _ (fun b σ ↦ ih b log F hF σ) ρ
    · exact obsWeight_challenged_liftBind_le R sk _ (fun b σ ↦ ih b log F hF σ) ρ
    · by_cases hr : r.leafIndex ∈ F
      · refine (obsWeight_challenged_liftBind_eq_zero R sk _ (fun b σ ↦ ?_) ρ).le.trans
          zero_le
        exact obsWeight_reused R sk hk (next b) _
          (not_noLeafIndexReused_append (hF _ hr) b.down) σ
      · rw [refuseFrom_sign_of_notMem hr]
        exact obsWeight_challenged_liftBind_le R sk _
          (fun b σ ↦ ih b _ _ (mem_map_append_of_mem_insert hF r b.down) σ) ρ

/-- The verification stage of `game` loses on a transcript with a repeated leaf. -/
theorem obsWeight_verify_reused (pk : PublicKey) (a : Forgery) {log : SignLog}
    (h : ¬SigningTranscript.NoLeafIndexReused log) (σ : SubState (QReg.of Unit × R.D)) :
    obsWeight (R.run .instruments
      ((((xmssRom.verify pk a).toQuantumAt (SufCma.romImpl _)).bind fun verified ↦
        QuantumComp₂.pure (xmssRom.winningCondition log a && verified)) :
        QComp romSpec (QReg.of Unit) (QReg.of Unit) Bool))
      σ (fun p ↦ ({true} : Set Bool).indicator 1 p.2.2) = 0 := by
  have hw : xmssRom.winningCondition log a = false := decide_eq_false fun h' ↦ h h'.1
  rw [obsWeight_run_bind₂]
  refine ENNReal.tsum_eq_zero.mpr fun v ↦ ?_
  rw [obsWeight_run_pure₂, hw]
  simp

/-- **Per runtime, `refuse A` wins the game with at least the weight of `A`.** -/
theorem obsWeight_game_le (S0 : MasterSeed) (A : Adversary)
    (σ : SubState (QReg.of Unit × R.D)) :
    obsWeight (R.run .instruments (SufCma.game xmssRom S0 A)) σ
        (fun p ↦ ({true} : Set Bool).indicator 1 p.2.2) ≤
      obsWeight (R.run .instruments (SufCma.game xmssRom S0 (refuse A))) σ
        (fun p ↦ ({true} : Set Bool).indicator 1 p.2.2) := by
  unfold SufCma.game
  rw [obsWeight_run_bind₂, obsWeight_run_bind₂]
  refine ENNReal.tsum_le_tsum fun keys ↦ ?_
  refine obsWeight_le_refuseFrom R keys.2 ?_ (A keys.1) [] ∅ (by simp) _
  intro a log h σ'
  exact obsWeight_verify_reused R keys.1 a h σ'

end win

/-- **Weights compared per function compare in the QROM**: if against every function the run of
`x` puts at most the weight of the run of `y` on `true`, so does the QROM. Stated over abstract
`X`, `Y` (the kernel never sees a sum over the concrete functions). -/
theorem qromEvalDistMap_true_le {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [AddCommGroup Y] {W : QReg → Type} {A : QReg}
    (x y : QuantumComp LocalSig.instruments.{0} (qromSpec X Y) W A) (ρ : SubState A)
    (f : (Σ u, W u) → Bool)
    (h : ∀ H : X → Y,
      obsWeight ((additiveOracleRuntime H).run .instruments x)
          (ρ.prod (additiveOracleRuntime H).init) (fun p ↦ ({true} : Set Bool).indicator 1 (f p)) ≤
        obsWeight ((additiveOracleRuntime H).run .instruments y)
          (ρ.prod (additiveOracleRuntime H).init) (fun p ↦ ({true} : Set Bool).indicator 1 (f p))) :
    qromEvalDistMap .instruments x ρ (fun _ p ↦ f p) {true} ≤
      qromEvalDistMap .instruments y ρ (fun _ p ↦ f p) {true} := by
  have hs : MeasurableSet ({true} : Set Bool) := measurableSet_singleton true
  unfold qromEvalDistMap
  refine (sampledEvalDistMap_apply _ _ _ _ _ hs).trans_le
    ((Finset.sum_le_sum fun H _ ↦ mul_le_mul_right ?_ _).trans_eq
      (sampledEvalDistMap_apply _ _ _ _ _ hs).symm)
  exact (QuantumRuntime.evalDistMap_apply _ _ _ _ _ hs).trans_le
    ((h H).trans_eq (QuantumRuntime.evalDistMap_apply _ _ _ _ _ hs).symm)

/-- **Refusing reused leaves does not lower the winning probability.** -/
theorem winProb_le_winProb_refuse (A : Adversary) :
    SufCma.winProb xmssRom A ≤ SufCma.winProb xmssRom (refuse A) := by
  unfold SufCma.winProb
  exact Finset.sum_le_sum fun S0 _ ↦ mul_le_mul_right (qromEvalDistMap_true_le _ _ _ _
    fun H ↦ obsWeight_game_le (additiveOracleRuntime H) S0 A _) _

end Quantum.Qrom.Xmss

end
