module

public import Quantum.Xmss.Game

@[expose] public section

/-!
# Adversaries that never reuse a leaf

A run that requests some leaf index twice loses the SUF-CMA game (`NoLeafIndexReused` in the
winning condition). So an adversary may as well never do it: `refuse A` answers a request of an
already requested leaf itself, with `none` and the register relabel of `signTree`, without asking
the signer, and wins at least as often as `A`.

* `leafCharge ℓ`: the requests of leaf `ℓ` cost one, everything else nothing.
* `NoLeafReuse A`: on every path, each leaf is requested at most once.
* `refuseFrom F x`, `refuse A`: answer the requests of already requested leaves (those in `F`,
  then those requested so far) locally with `none`.

## Main statements

* `noLeafReuse_refuse`: `refuse A` never reuses a leaf.
* `isChargeBound_refuse`: `refuse A` keeps every charge bound of `A` (a refused request becomes
  a local operation, which costs nothing).
* `winProb_le_winProb_refuse`: `winProb e A ≤ winProb e (refuse A)`. Per permutation, by
  induction over the adversary's tree with its transcript: at a reused request every leaf of the
  game below has a transcript with a repeated leaf, so it returns `false`; elsewhere both games
  make the same command.
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal

universe u v u₁ v₁ w w₁

namespace Quantum.Xmss

open LeanXmss HashSig Common Common.SufCma LeanXmss.RandomPermutationModel
open LeanVM.Semantics (KeccakState)

/-! ## Leaf charges and refused requests -/

-- The adversary's commands, as an indexed polynomial functor.
set_option quotPrecheck false in
local notation "AdvP" S:max => QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec S)

section refuse

variable {S : Type} [Fintype S] [DecidableEq S]

/-- The charge of the requests of leaf `ℓ`: one per request of `ℓ`, nothing otherwise. -/
def leafCharge (ℓ : LeafIndex) : AdvPort → ℕ
  | .perm _ => 0
  | .sign r => if r.leafIndex = ℓ then 1 else 0

/-- **No leaf reuse**: on every path, no leaf index is requested twice. -/
def NoLeafReuse (A : Adversary S) : Prop :=
  ∀ pk ℓ, IFreeM.IsChargeBound (A pk) (cmdCharge (leafCharge ℓ)) 1

/-- The local stand-in for the refused request `r` on the register `A ≃ In × E`: the register
relabel of `signTree`, with one outcome and no call. -/
noncomputable def refuseOp (r : SigningRequest) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpec S).In (.sign r) × E) : LocalSig.instruments.{0}.Op A :=
  ⟨Unit, fun _ ↦ QReg.of ((advSpec S).Out (.sign r) × E), SubInstrument.relabel ℓ⟩

/-- **Refuse reused leaves**: the same commands, except that a request of a leaf in `F` or
requested before on the path is answered `none` by `refuseOp`, without a signer call. -/
noncomputable def refuseFrom {X : QReg → Type} :
    {A : QReg} → Finset LeafIndex → IFreeM (AdvP S) X A → IFreeM (AdvP S) X A
  | _, _, .pure x => .pure x
  | _, F, .liftBind (.prim o) next => .liftBind (.prim o) fun b ↦ refuseFrom F (next b)
  | _, F, .liftBind (.query (.perm p) E ℓ) next =>
      .liftBind (.query (.perm p) E ℓ) fun b ↦ refuseFrom F (next b)
  | _, F, .liftBind (.query (.sign r) E ℓ) next =>
      if r.leafIndex ∈ F then
        .liftBind (.prim (refuseOp r E ℓ)) fun _ ↦ refuseFrom F (next (ULift.up none))
      else .liftBind (.query (.sign r) E ℓ) fun b ↦ refuseFrom (insert r.leafIndex F) (next b)

/-- **The adversary that never reuses a leaf**: `A` with the requests of already requested
leaves answered `none` locally. -/
noncomputable def refuse (A : Adversary S) : Adversary S :=
  fun pk ↦ refuseFrom ∅ (A pk)

section sign

variable {X : QReg → Type} {A : QReg} {F : Finset LeafIndex} {r : SigningRequest} {E : QReg}
  {ℓ : A ≃ (advSpec S).In (.sign r) × E}
  {next : (b : (AdvP S).B A (QuantumComp.Cmd.query (AdvPort.sign r) E ℓ)) →
    IFreeM (AdvP S) X ((AdvP S).src A (QuantumComp.Cmd.query (AdvPort.sign r) E ℓ) b)}

/-- A request of a leaf in `F` is refused. -/
theorem refuseFrom_sign_of_mem (h : r.leafIndex ∈ F) :
    refuseFrom F (IFreeM.liftBind (QuantumComp.Cmd.query (AdvPort.sign r) E ℓ) next) =
      .liftBind (.prim (refuseOp r E ℓ)) fun _ ↦ refuseFrom F (next (ULift.up none)) := by
  rw [refuseFrom, ite_eq_left h]

/-- A request of a leaf outside `F` is forwarded, and its leaf joins `F`. -/
theorem refuseFrom_sign_of_notMem (h : r.leafIndex ∉ F) :
    refuseFrom F (IFreeM.liftBind (QuantumComp.Cmd.query (AdvPort.sign r) E ℓ) next) =
      .liftBind (.query (.sign r) E ℓ) fun b ↦ refuseFrom (insert r.leafIndex F) (next b) := by
  rw [refuseFrom, ite_eq_right h]

end sign

/-- Refusing keeps every charge bound: a refused request becomes a local operation, which costs
nothing. -/
theorem isChargeBound_refuseFrom {X : QReg → Type} {c : AdvPort → ℕ} {A : QReg}
    (x : IFreeM (AdvP S) X A) (F : Finset LeafIndex) {n : ℕ}
    (h : IFreeM.IsChargeBound x (cmdCharge c) n) :
    IFreeM.IsChargeBound (refuseFrom F x) (cmdCharge c) n := by
  induction x using IFreeM.inductionOn generalizing F n with
  | pure _ _ => trivial
  | liftBind A c' next ih =>
    rcases c' with o | ⟨p | r, E, ℓ⟩
    · exact ⟨h.1, fun b ↦ ih b F (h.2 b)⟩
    · exact ⟨h.1, fun b ↦ ih b F (h.2 b)⟩
    · by_cases hr : r.leafIndex ∈ F
      · rw [refuseFrom_sign_of_mem hr]
        exact ⟨Nat.zero_le _, fun _ ↦ (ih _ F (h.2 _)).mono (Nat.sub_le n _)⟩
      · rw [refuseFrom_sign_of_notMem hr]
        exact ⟨h.1, fun b ↦ ih b _ (h.2 b)⟩

/-- The requests of leaf `ℓ` after refusing from `F`: none if `ℓ ∈ F`, else at most one. -/
theorem isChargeBound_leafCharge_refuseFrom {X : QReg → Type} {A : QReg}
    (x : IFreeM (AdvP S) X A) (F : Finset LeafIndex) (ℓ : LeafIndex) :
    IFreeM.IsChargeBound (refuseFrom F x) (cmdCharge (leafCharge ℓ))
      (if ℓ ∈ F then 0 else 1) := by
  induction x using IFreeM.inductionOn generalizing F with
  | pure _ _ => trivial
  | liftBind A c next ih =>
    rcases c with o | ⟨p | r, E, ℓ'⟩
    · exact ⟨Nat.zero_le _, fun b ↦ (ih b F).mono (Nat.le_of_eq (Nat.sub_zero _).symm)⟩
    · exact ⟨Nat.zero_le _, fun b ↦ (ih b F).mono (Nat.le_of_eq (Nat.sub_zero _).symm)⟩
    · by_cases hr : r.leafIndex ∈ F
      · rw [refuseFrom_sign_of_mem hr]
        exact ⟨Nat.zero_le _, fun _ ↦ (ih _ F).mono (Nat.le_of_eq (Nat.sub_zero _).symm)⟩
      · rw [refuseFrom_sign_of_notMem hr]
        refine ⟨?_, fun b ↦ (ih b _).mono ?_⟩
        · by_cases hℓ : r.leafIndex = ℓ
          · subst hℓ
            simp [cmdCharge, leafCharge, hr]
          · simp [cmdCharge, leafCharge, hℓ]
        · by_cases hℓ : r.leafIndex = ℓ
          · subst hℓ
            simp [cmdCharge, leafCharge, hr]
          · simp [cmdCharge, leafCharge, hℓ, Ne.symm hℓ]

/-- **`refuse A` never reuses a leaf.** -/
theorem noLeafReuse_refuse (A : Adversary S) : NoLeafReuse (refuse A) := fun pk ℓ ↦
  (isChargeBound_leafCharge_refuseFrom (A pk) ∅ ℓ).mono (by simp)

/-- **`refuse A` keeps every charge bound of `A`**, in particular its permutation calls
(`permCharge`) and signing requests (`signCharge`). -/
theorem isChargeBound_refuse {c : AdvPort → ℕ} {n : ℕ} {A : Adversary S} {pk : PublicKey}
    (h : IFreeM.IsChargeBound (A pk) (cmdCharge c) n) :
    IFreeM.IsChargeBound (refuse A pk) (cmdCharge c) n :=
  isChargeBound_refuseFrom (A pk) ∅ h

/-! ### Transcripts -/

/-- The leaf map of `withSignLog`: the value with the transcript. -/
def signLeaf {B : QReg} {α : Type} (u : QReg) (l : QuantumComp₂.Leaf B α u) (log : SignLog) :
    QuantumComp₂.Leaf B (α × SignLog) u :=
  ⟨l.1, (l.2, log)⟩

/-- A transcript with a repeated leaf keeps it after any command. -/
theorem not_noLeafIndexReused_logAfter {A : QReg}
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec S) A) (b : c.Resp) {log : SignLog}
    (h : ¬SigningTranscript.NoLeafIndexReused log) :
    ¬SigningTranscript.NoLeafIndexReused (logAfter c b log) := by
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact h
  · exact h
  · exact fun hn ↦ h (List.Nodup.sublist ((List.sublist_append_left _ _).map _) hn)

end refuse

/-- A request of an already requested leaf repeats it. -/
theorem not_noLeafIndexReused_append {log : SignLog} {r : SigningRequest}
    (h : r.leafIndex ∈ log.map fun q ↦ q.1.leafIndex) (s : Option Signature) :
    ¬SigningTranscript.NoLeafIndexReused (log ++ [⟨r, s⟩]) := fun hn ↦ by
  rw [SigningTranscript.NoLeafIndexReused, List.map_append, List.nodup_append] at hn
  exact hn.2.2 _ h _ (List.mem_map_of_mem (List.mem_singleton_self _)) rfl

/-- The requested leaves after a fresh request `r`. -/
theorem mem_map_append_of_mem_insert {log : SignLog} {F : Finset LeafIndex}
    (hF : ∀ ℓ ∈ F, ℓ ∈ log.map fun q ↦ q.1.leafIndex) (r : SigningRequest)
    (s : Option Signature) :
    ∀ ℓ ∈ insert r.leafIndex F, ℓ ∈ (log ++ [⟨r, s⟩] : SignLog).map fun q ↦ q.1.leafIndex := by
  intro ℓ h
  rw [List.map_append, List.mem_append]
  rcases Finset.mem_insert.mp h with rfl | h
  · exact Or.inr (List.mem_map_of_mem (List.mem_singleton_self _))
  · exact Or.inl (hF ℓ h)

/-! ## Observed weights of runs -/

section weight

/-- The weight of an observation `g` of the outcomes of `p` from `ρ`: `∑ i, tr (p.branch i ρ) g i`.
-/
noncomputable def obsWeight {A : Type*} [Fintype A] {ι : Type*} {B : ι → Type*}
    [∀ i, Fintype (B i)] (p : DSubInstrument A ι B) (ρ : SubState A) (g : ι → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (p.branch i ρ.matrix).trace.re * g i

variable {A : Type*} [Fintype A] {ι κ : Type*} {B : ι → Type*} [∀ i, Fintype (B i)]
  {C : κ → Type*} [∀ c, Fintype (C c)]

/-- The weight of a composite sums the weights of the continuations on the post-branch
substates. -/
theorem obsWeight_bind (p : DSubInstrument A ι B) (k : (i : ι) → DSubInstrument (B i) κ C)
    (ρ : SubState A) (g : κ → ℝ≥0∞) :
    obsWeight (p.bind k) ρ g = ∑' i, obsWeight (k i) (p.post ρ i) g := by
  unfold obsWeight
  simp only [DSubInstrument.matrix_post]
  have h := p.isCPTNIFamily.comp_eval fun i ↦ (k i).isCPTNIFamily
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun c ↦ ?_
  rw [DSubInstrument.branch_bind, MatrixMap.trace_re_familyBind_apply p.isCPTNIFamily
      (fun i ↦ (k i).isCPTNIFamily),
    ENNReal.ofReal_tsum_of_nonneg (f := fun i ↦ ((k i).branch c (p.branch i ρ.matrix)).trace.re)
      (fun i ↦ (h c).trace_re_apply_nonneg i ρ.posSemidef)
      ((h c).summable_trace_re_apply ρ.posSemidef), ENNReal.tsum_mul_right]

/-- The weight of a return is the trace of the substate times the observation of its outcome. -/
theorem obsWeight_ret (i : ι) (ρ : SubState (B i)) (g : ι → ℝ≥0∞) :
    obsWeight (DSubInstrument.ret B i) ρ g = ENNReal.ofReal ρ.matrix.trace.re * g i := by
  unfold obsWeight
  rw [tsum_eq_single i fun j hj ↦ by simp [DSubInstrument.branch_ret_of_ne B hj]]
  simp only [DSubInstrument.branch_ret_self, LinearMap.id_apply]

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} (R : QuantumRuntime spec)
  (I : L.Interp)

/-- The weight of a run of `x.bind k`, over the leaves of `x`. -/
theorem obsWeight_run_bind {X : QReg → Type w} {Y : QReg → Type w₁} {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor L spec) X A)
    (k : ∀ u, X u → IFreeM (QuantumComp.toIPFunctor L spec) Y u)
    (ρ : SubState (A × R.D)) (g : (Σ u, Y u) → ℝ≥0∞) :
    obsWeight (R.run I (IFreeM.bind x k)) ρ g =
      ∑' p, obsWeight (R.run I (k p.1 p.2)) ((R.run I x).post ρ p) g :=
  (congrArg (obsWeight · ρ g) (R.run_bind I x k)).trans (obsWeight_bind _ _ _ _)

/-- The weight of a run of a fixed-register `x.bind k`, over the values of `x`. -/
theorem obsWeight_run_bind₂ {A B C : QReg} {α : Type w} {β : Type w₁}
    (x : QuantumComp₂ L spec A B α) (k : α → QuantumComp₂ L spec B C β)
    (ρ : SubState (A × R.D)) (g : (Σ u, QuantumComp₂.Leaf C β u) → ℝ≥0∞) :
    obsWeight (R.run I (x.bind k)) ρ g =
      ∑' a, obsWeight (R.run I (k a)) ((R.run₂ I x).post ρ a) g := by
  have h := R.run_bind I x fun u (p : QuantumComp₂.Leaf B α u) ↦ p.casesOn fun h a ↦ h ▸ k a
  change R.run I (x.bind k) = _ at h
  rw [h, obsWeight_bind, ← (QuantumComp₂.leafEquiv B α).tsum_eq]
  rfl

/-- The weight of a run of `pure b`. -/
theorem obsWeight_run_pure₂ {C : QReg} {β : Type w} (b : β) (σ : SubState (C × R.D))
    (g : (Σ u, QuantumComp₂.Leaf C β u) → ℝ≥0∞) :
    obsWeight (R.run I (QuantumComp₂.pure b : QuantumComp₂ L spec C C β)) σ g =
      ENNReal.ofReal σ.matrix.trace.re * g ⟨C, rfl, b⟩ :=
  obsWeight_ret (B := fun p : Σ u, QuantumComp₂.Leaf C β u ↦ p.1 × R.D) ⟨C, rfl, b⟩ σ g

end weight

/-! ## Reused leaves lose -/

section win

variable {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S] (e : KeccakState ≃ S)
  (R : QuantumRuntime (qrpmSpec S)) (sk : SecretKey)

/-- The weights of the challenged commands below a common first command compare as the weights
below its answers. -/
theorem obsWeight_challenged_liftBind_le {A B C : QReg} {γ β : Type} (c : (AdvP S).A A)
    {next next' : (b : (AdvP S).B A c) →
      IFreeM (AdvP S) (QuantumComp₂.Leaf B γ) ((AdvP S).src A c b)}
    {k : γ → QComp (qrpmSpec S) B C β} {g : (Σ u, QuantumComp₂.Leaf C β u) → ℝ≥0∞}
    (h : ∀ b σ, obsWeight (R.run .instruments ((challenged e sk (next b)).bind k)) σ g ≤
      obsWeight (R.run .instruments ((challenged e sk (next' b)).bind k)) σ g)
    (ρ : SubState (A × R.D)) :
    obsWeight (R.run .instruments ((challenged e sk (IFreeM.liftBind c next)).bind k)) ρ g ≤
      obsWeight (R.run .instruments ((challenged e sk (IFreeM.liftBind c next')).bind k)) ρ g := by
  simp only [challenged, IFreeM.substitute_liftBind, QuantumComp₂.bind, FreeM₂.bind,
    IFreeM.bind_assoc]
  rw [obsWeight_run_bind, obsWeight_run_bind]
  refine ENNReal.tsum_le_tsum fun p ↦ ?_
  obtain ⟨t, b, rfl⟩ := p
  exact h b _

/-- The weight of the challenged commands below a first command vanishes when it vanishes below
each of its answers. -/
theorem obsWeight_challenged_liftBind_eq_zero {A B C : QReg} {γ β : Type} (c : (AdvP S).A A)
    {next : (b : (AdvP S).B A c) → IFreeM (AdvP S) (QuantumComp₂.Leaf B γ) ((AdvP S).src A c b)}
    {k : γ → QComp (qrpmSpec S) B C β} {g : (Σ u, QuantumComp₂.Leaf C β u) → ℝ≥0∞}
    (h : ∀ b σ, obsWeight (R.run .instruments ((challenged e sk (next b)).bind k)) σ g = 0)
    (ρ : SubState (A × R.D)) :
    obsWeight (R.run .instruments ((challenged e sk (IFreeM.liftBind c next)).bind k)) ρ g =
      0 := by
  simp only [challenged, IFreeM.substitute_liftBind, QuantumComp₂.bind, FreeM₂.bind,
    IFreeM.bind_assoc]
  rw [obsWeight_run_bind]
  refine ENNReal.tsum_eq_zero.mpr fun p ↦ ?_
  obtain ⟨t, b, rfl⟩ := p
  exact h b _

variable {B C : QReg} {α β : Type} {k : α × SignLog → QComp (qrpmSpec S) B C β}
  {g : (Σ u, QuantumComp₂.Leaf C β u) → ℝ≥0∞}

/-- **Reused leaves lose**: when the continuation `k` has weight zero on transcripts with a
repeated leaf, the challenged program from such a transcript has weight zero. -/
theorem obsWeight_reused
    (hk : ∀ a log, ¬SigningTranscript.NoLeafIndexReused log → ∀ σ,
      obsWeight (R.run .instruments (k (a, log))) σ g = 0)
    {A : QReg} (x : IFreeM (AdvP S) (QuantumComp₂.Leaf B α) A)
    (log : SignLog) (hlog : ¬SigningTranscript.NoLeafIndexReused log) (ρ : SubState (A × R.D)) :
    obsWeight (R.run .instruments ((challenged e sk (logSigns signLeaf x log)).bind k)) ρ g = 0 := by
  induction x using IFreeM.inductionOn generalizing log with
  | pure A v =>
    obtain ⟨rfl, a⟩ := v
    exact hk a log hlog ρ
  | liftBind A c next ih =>
    exact obsWeight_challenged_liftBind_eq_zero e R sk c
      (fun b σ ↦ ih b _ (not_noLeafIndexReused_logAfter c b hlog) σ) ρ

/-- **Refusing does not lower the weight**, from a transcript `log` containing the leaves `F`:
the same commands, except at a refused request, below which the original program has weight
zero (`obsWeight_reused`). -/
theorem obsWeight_le_refuseFrom
    (hk : ∀ a log, ¬SigningTranscript.NoLeafIndexReused log → ∀ σ,
      obsWeight (R.run .instruments (k (a, log))) σ g = 0)
    {A : QReg} (x : IFreeM (AdvP S) (QuantumComp₂.Leaf B α) A)
    (log : SignLog) (F : Finset LeafIndex) (hF : ∀ ℓ ∈ F, ℓ ∈ log.map fun q ↦ q.1.leafIndex)
    (ρ : SubState (A × R.D)) :
    obsWeight (R.run .instruments ((challenged e sk (logSigns signLeaf x log)).bind k)) ρ g ≤
      obsWeight (R.run .instruments
        ((challenged e sk (logSigns signLeaf (refuseFrom F x) log)).bind k)) ρ g := by
  induction x using IFreeM.inductionOn generalizing log F with
  | pure _ _ => exact le_rfl
  | liftBind A c next ih =>
    rcases c with o | ⟨p | r, E, ℓ⟩
    · exact obsWeight_challenged_liftBind_le e R sk _ (fun b σ ↦ ih b log F hF σ) ρ
    · exact obsWeight_challenged_liftBind_le e R sk _ (fun b σ ↦ ih b log F hF σ) ρ
    · by_cases hr : r.leafIndex ∈ F
      · refine (obsWeight_challenged_liftBind_eq_zero e R sk _ (fun b σ ↦ ?_) ρ).le.trans
          zero_le
        exact obsWeight_reused e R sk hk (next b) _
          (not_noLeafIndexReused_append (hF _ hr) b.down) σ
      · rw [refuseFrom_sign_of_notMem hr]
        exact obsWeight_challenged_liftBind_le e R sk _
          (fun b σ ↦ ih b _ _ (mem_map_append_of_mem_insert hF r b.down) σ) ρ

/-- The verification stage of `game` loses on a transcript with a repeated leaf. -/
theorem obsWeight_verify_reused (pk : PublicKey) (a : Forgery) {log : SignLog}
    (h : ¬SigningTranscript.NoLeafIndexReused log) (σ : SubState (QReg.of Unit × R.D)) :
    obsWeight (R.run .instruments
      ((((sufCmaScheme.verify pk a).toQuantumAt (permImpl e _)).bind fun verified ↦
        QuantumComp₂.pure (sufCmaScheme.winningCondition log a && verified)) :
        QComp (qrpmSpec S) (QReg.of Unit) (QReg.of Unit) Bool))
      σ (fun p ↦ ({true} : Set Bool).indicator 1 p.2.2) = 0 := by
  have hw : sufCmaScheme.winningCondition log a = false := decide_eq_false fun h' ↦ h h'.1
  rw [obsWeight_run_bind₂]
  refine ENNReal.tsum_eq_zero.mpr fun v ↦ ?_
  rw [obsWeight_run_pure₂, hw]
  simp

/-- **Per runtime, `refuse A` wins the game with at least the weight of `A`.** -/
theorem obsWeight_game_le (S0 : MasterSeed) (A : Adversary S)
    (σ : SubState (QReg.of Unit × R.D)) :
    obsWeight (R.run .instruments (game e S0 A)) σ
        (fun p ↦ ({true} : Set Bool).indicator 1 p.2.2) ≤
      obsWeight (R.run .instruments (game e S0 (refuse A))) σ
        (fun p ↦ ({true} : Set Bool).indicator 1 p.2.2) := by
  unfold game
  rw [obsWeight_run_bind₂, obsWeight_run_bind₂]
  refine ENNReal.tsum_le_tsum fun keys ↦ ?_
  refine obsWeight_le_refuseFrom e R keys.2 ?_ (A keys.1) [] ∅ (by simp) _
  intro a log h σ'
  exact obsWeight_verify_reused e R keys.1 a h σ'

/-- **Refusing reused leaves does not lower the winning probability.** -/
theorem winProb_le_winProb_refuse (A : Adversary S) : winProb e A ≤ winProb e (refuse A) := by
  have hs : MeasurableSet ({true} : Set Bool) := measurableSet_singleton true
  unfold winProb qrpmEvalDistMap
  refine mul_le_mul_right (Finset.sum_le_sum fun S0 _ ↦ ?_) _
  refine (sampledEvalDistMap_apply _ _ _ _ _ hs).trans_le
    ((Finset.sum_le_sum fun φ _ ↦ mul_le_mul_right ?_ _).trans_eq
      (sampledEvalDistMap_apply _ _ _ _ _ hs).symm)
  exact (QuantumRuntime.evalDistMap_apply _ _ _ _ _ hs).trans_le
    ((obsWeight_game_le e (permutationRuntime φ) S0 A
      ((SubState.basis ()).prod (permutationRuntime φ).init)).trans_eq
      (QuantumRuntime.evalDistMap_apply _ _ _ _ _ hs).symm)

end win

end Quantum.Xmss

end
