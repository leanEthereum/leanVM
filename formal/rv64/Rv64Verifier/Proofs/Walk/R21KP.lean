import Rv64Verifier.Proofs.Walk.AtR21

/-!
# `verify_stacked_opening`'s mirror keeps the proof

`KP m`: `m` keeps the transcript's proof (its commitments add roots, its Merkle checks move the
opening offset). `kp_verifyStackedOpening`: so does `verifyStackedOpeningRust`.
-/

namespace Rv64Verifier.Proofs.Walk
open LeanVM.Parameters LeanVM.Protocol Rv64Verifier.Model Rv64Verifier.Model.Pcs

/-- `m` keeps the proof. -/
def KP {α : Type} (m : TM α) : Prop :=
  ∀ t a t', m.run t = some (a, t') → t'.proof = t.proof

theorem KP.of {α : Type} {m : TM α} (h : Keeps m) : KP m := fun t a t' e ↦ (h t a t' e).1

theorem KP.bind {α β : Type} {m : TM α} {k : α → TM β} (hm : KP m) (hk : ∀ a, KP (k a)) :
    KP (m >>= k) := by
  intro t b t' h
  rw [StateT.run_bind] at h
  cases hmt : m.run t with
  | none => rw [hmt] at h; cases h
  | some p =>
    obtain ⟨a, t₁⟩ := p
    rw [hmt] at h
    exact (hk a t₁ b t' h).trans (hm t a t₁ hmt)

theorem KP.pure {α : Type} (a : α) : KP (Pure.pure a : TM α) := KP.of (Keeps.pure a)

theorem KP.ite {α : Type} {c : Prop} {_ : Decidable c} {a b : TM α} (ha : KP a) (hb : KP b) :
    KP (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem KP.commit (h w : ℕ) : KP (TM.commit h w) := by
  intro t a t' e
  simp only [StateT.run, TM.commit] at e
  split at e
  · split at e
    · cases e; rfl
    · cases e
  · cases e

theorem KP.merkle (i : ℕ) (ps : List ℕ) : KP (TM.merkle i ps) := by
  intro t a t' e
  simp only [StateT.run, TM.merkle] at e
  split at e
  · split at e
    · cases e; rfl
    · cases e
  · cases e

theorem KP.merkleLeaves (i : ℕ) (q : List (BitVec 64)) (lw : ℕ) : KP (TM.merkleLeaves i q lw) :=
  KP.bind (KP.merkle _ _) fun _ ↦ KP.bind (KP.of (keeps_require _)) fun _ ↦ KP.pure _

theorem KP.forRange {σ : Type} {f : ℕ → σ → TM σ} (hf : ∀ i x, KP (f i x)) :
    ∀ start n x, KP (TM.forRange f start n x)
  | _, 0, _ => KP.pure _
  | start, n + 1, x => KP.bind (hf start x) fun y ↦ KP.forRange hf (start + 1) n y

theorem kp_sqLoop (b : BitVec 64) (d c : ℕ) :
    ∀ fuel r, KP (Pcs.sampleQueriesLoop b d c fuel r)
  | 0, _ => KP.pure _
  | fuel + 1, r => by
    unfold Pcs.sampleQueriesLoop
    exact KP.ite (KP.bind (KP.of Keeps.sample) fun _ ↦ kp_sqLoop b d c fuel _) (KP.pure _)

theorem kp_sampleQueries (b : BitVec 64) (c : ℕ) : KP (sampleQueriesRust b c) :=
  KP.bind (KP.of (keeps_ofOption _)) fun _ ↦ kp_sqLoop _ _ _ _ _

theorem KP.tailRound (m i : ℕ) (st : List E × List E × E) : KP (tailRoundRust m i st) :=
  KP.bind (KP.of Keeps.sample) fun _ ↦
    KP.ite (KP.bind (KP.of (Keeps.roundPoly _ _ _)) fun _ ↦ KP.pure _) (KP.pure _)

theorem KP.whirLevels (logN : ℕ) (config : WhirConfigRust) (basis : List E → Option E) :
    ∀ level ls s, KP (whirLevelsRust logN config basis level ls s)
  | _, [], _ => KP.of keeps_fail
  | level, (fc, lr) :: rest, s => by
    unfold whirLevelsRust
    refine KP.bind (KP.of (Keeps.loopN Keeps.foldRound _ _)) fun p ↦ ?_
    rcases p with ⟨s₁, lf⟩
    dsimp only
    repeat' (first
      | exact KP.of (Keeps.nextScalars _)
      | exact KP.of (Keeps.samples _)
      | exact KP.of Keeps.nextScalar
      | exact KP.of Keeps.sample
      | exact KP.of (Keeps.roundPoly _ _ _)
      | exact KP.of (Keeps.grind _)
      | exact KP.of (keeps_ofOption _)
      | exact KP.of (keeps_require _)
      | exact KP.commit _ _
      | exact kp_sampleQueries _ _
      | exact KP.merkleLeaves _ _ _
      | exact KP.forRange (fun i x ↦ KP.tailRound _ i x) _ _ _
      | exact KP.whirLevels logN config basis _ rest _
      | exact KP.pure _
      | refine KP.bind ?_ fun _ ↦ ?_
      | split)

theorem kp_verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaimRust) :
    KP (verifyStackedOpeningRust stackLog logInvRate claims) := by
  unfold verifyStackedOpeningRust verifyWhirRust
  exact KP.bind (KP.of Keeps.sample) fun _ ↦ KP.bind (KP.of (keeps_ofOption _)) fun _ ↦
    KP.bind (KP.of (Keeps.roundPoly _ _ _)) fun _ ↦ KP.whirLevels _ _ _ _ _ _

end Rv64Verifier.Proofs.Walk
