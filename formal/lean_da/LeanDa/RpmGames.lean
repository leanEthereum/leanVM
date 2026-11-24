module

public import LeanDa.RpmScheme
public import Common.Rerun
public import LeanDa.HashOracle
public import LeanDa.WithHash

@[expose] public section

/-!
# The verifier's oracle programs through simulations and relabelings

The verifier's oracle programs are written for any monad, so they commute with a monad morphism
such as a simulation (`grindM_map`, `membershipChallengeM_map`, `walkM_map`, `verifyCellM_map`,
`merkleRootM_map`, `commitCellsM_map`). Read on byte states (`Common.relabel`), they are the same
programs (`relabel_hK`, `relabel_pK`, `relabel_commitCellsM`, `relabel_verifyCellM`,
`relabel_membershipChallengeM`), and in the two-oracle form of `Common.rpmGame2` the verifier's
calls of the permutation are direct calls `F` (`toK`), which `Common.toOne` turns back into `π`
queries (`toOne_rpmGame2`, `isWeightBound_toOne_iff`): the form of the two-oracle transfer
(`Common.keccak256_transfer2`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common PqDas

namespace LeanDa

/-! ## Oracle programs through a monad morphism -/

section Map

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
  (φ : ∀ {α}, m α → n α) (hpure : ∀ {α} (a : α), φ (pure a) = pure a)
  (hbind : ∀ {α β} (x : m α) (f : α → m β), φ (x >>= f) = φ x >>= fun a ↦ φ (f a))
  (H : List UInt8 → m Common.DigestBytes) (P : Lanes → m Lanes)

include hpure hbind

/-- **The nonce search through a monad morphism.** -/
theorem grindM_map (y : Lanes) : ∀ (fuel nonce : ℕ),
    φ (grindMWithHash P y nonce fuel) = grindMWithHash (fun L ↦ φ (P L)) y nonce fuel
  | 0, _ => hpure _
  | fuel + 1, nonce => by
    simp only [grindMWithHash, hbind]
    refine bind_congr fun o ↦ ?_
    split
    · exact hpure _
    · exact grindM_map y fuel (nonce + 1)

/-- **The challenge's sponge through a monad morphism.** -/
theorem membershipChallengeM_map (root : Common.DigestBytes) :
    φ (membershipChallengeMWithHash H P root) =
      membershipChallengeMWithHash (fun a ↦ φ (H a)) (fun L ↦ φ (P L)) root := by
  simp only [membershipChallengeMWithHash, Sponge.newWith, hbind, hpure, grindM_map φ hpure hbind P]

theorem walkM_map (idx : ℕ) (node : Common.DigestBytes) (path : List Common.DigestBytes) :
    φ (walkMWithHash H idx node path) = walkMWithHash (fun a ↦ φ (H a)) idx node path := by
  induction path generalizing idx node with
  | nil => exact hpure _
  | cons s rest ih =>
    simp only [walkMWithHash, hbind, ih]

theorem verifyCellM_map (r : ℕ) (com : Common.DigestBytes) (p : Fin (r * 128)) (x : Cell) (τ : CellOpening) :
    φ (verifyCellMWithHash H r com p x τ) = verifyCellMWithHash (fun a ↦ φ (H a)) r com p x τ := by
  simp only [verifyCellMWithHash, hbind, hpure, walkM_map φ hpure hbind]

theorem merkleRootM_map (d : ℕ) : ∀ f : ℕ → m Common.DigestBytes,
    φ (merkleRootMWithHash H d f) = merkleRootMWithHash (fun a ↦ φ (H a)) d fun i ↦ φ (f i) := by
  induction d with
  | zero => intro f; rfl
  | succ d ih =>
    intro f
    simp only [merkleRootMWithHash, ih]
    congr 1
    funext i
    simp only [upMWithHash, hbind]

/-- **The commitment through a monad morphism.** -/
theorem commitCellsM_map {r : ℕ} (c : Fin (r * 128) → Cell) :
    φ (commitCellsMWithHash H c) = commitCellsMWithHash (fun a ↦ φ (H a)) c := by
  have hb : (fun i ↦ φ (blobRootMWithHash H c i)) = blobRootMWithHash (fun a ↦ φ (H a)) c := by
    funext i
    simp only [blobRootMWithHash, merkleRootM_map φ hpure hbind, cellLeavesMWithHash]
    rfl
  simp only [commitCellsMWithHash, hbind, merkleRootM_map φ hpure hbind, hb]

end Map

/-! ## Direct calls as `π` queries -/

/-- The verifier's oracles as those of the games on byte states: `F` a `π` query. -/
abbrev toK : QueryImpl Rom2 (OracleComp KSpecB) :=
  toOne (E := KRest) (C := KCap) ∘ₛ hfEmbed (Msg := List UInt8)

theorem toK_hR (a : List UInt8) : simulateQ toK (hR a) = hKB a := by
  simp [toK, hR, hQuery, hq]
  rfl

theorem toK_pR (L : Lanes) : simulateQ toK (pR L) = pKB L := by
  simp [toK, pR, pKB, lanePerm, fQuery, hq]
  rfl

theorem toK_membershipChallengeM (root : Common.DigestBytes) :
    simulateQ toK (membershipChallengeMWithHash hR pR root) =
      membershipChallengeMWithHash hKB pKB root := by
  rw [membershipChallengeM_map (fun x ↦ simulateQ toK x) (fun _ ↦ simulateQ_pure _ _)
    (fun _ _ ↦ simulateQ_bind _ _ _)]
  simp only [toK_hR, toK_pR]

theorem toK_commitCellsM {r : ℕ} (c : Fin (r * 128) → Cell) :
    simulateQ toK (commitCellsMWithHash hR c) = commitCellsMWithHash hKB c := by
  rw [commitCellsM_map (fun x ↦ simulateQ toK x) (fun _ ↦ simulateQ_pure _ _)
    (fun _ _ ↦ simulateQ_bind _ _ _)]
  simp only [toK_hR]

theorem toOne_advEmbed {α : Type} (X : OracleComp KSpecB α) :
    simulateQ (toOne (E := KRest) (C := KCap) ∘ₛ advEmbed (Msg := List UInt8)) X = X := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_query_bind]
    simp only [ih]
    rcases t with n | a | q <;> rfl

/-- **A two-oracle game through `toOne`**: the honest part, the adversary as it is, and the
verifier's part through `toK`. -/
theorem toOne_rpmGame2 {β γ δ : Type} (p : ProbComp β) (A : β → OracleComp KSpecB γ)
    (post : β → γ → OracleComp Rom2 δ) :
    simulateQ (toOne (E := KRest) (C := KCap)) (rpmGame2 (liftM p) A post) =
      (liftM p : OracleComp KSpecB β) >>= fun x ↦ A x >>= fun a ↦ simulateQ toK (post x a) := by
  simp only [rpmGame2, simulateQ_bind, ← QueryImpl.simulateQ_compose, toOne_advEmbed]
  rw [simulateQ_liftM_of_coins _ (fun n ↦ rfl)]

/-! ## The games -/

/-- **The cost of a game through `toOne`** is its cost in the two-oracle form: each query is
renamed to one of the same cost. -/
theorem isWeightBound_toOne_iff {α : Type} (D : OracleComp (dSpec2 (List UInt8) DigestBytes KState) α)
    (q : ℕ) :
    QueryCostAtMost (simulateQ (toOne (E := KRest) (C := KCap)) D) permCallsB q ↔
      QueryCostAtMost D permCalls2 q := by
  induction D using OracleComp.inductionOn generalizing q with
  | pure a => exact Iff.rfl
  | query_bind t k ih =>
    rw [simulateQ_query_bind, isWeightBound_query_bind_iff]
    rcases t with n | a | x | x
    · change QueryCostAtMost (liftM (KSpecB.query (.inl n)) >>= fun u ↦ simulateQ toOne (k u))
        permCallsB q ↔ _
      simp only [isWeightBound_query_bind_iff, permCallsB, permCalls2, ih]
      exact Iff.rfl
    · change QueryCostAtMost (liftM (KSpecB.query (.inr (.inl a))) >>= fun u ↦ simulateQ toOne (k u))
        permCallsB q ↔ _
      simp only [isWeightBound_query_bind_iff, permCallsB, permCalls2, ih]
      exact Iff.rfl
    · change QueryCostAtMost (liftM (KSpecB.query (.inr (.inr x))) >>= fun u ↦ simulateQ toOne (k u))
        permCallsB q ↔ _
      simp only [isWeightBound_query_bind_iff, permCallsB, permCalls2, ih]
      exact Iff.rfl
    · change QueryCostAtMost
        (liftM (KSpecB.query (.inr (.inr (.forward x)))) >>= fun u ↦ simulateQ toOne (k u))
          permCallsB q ↔ _
      simp only [isWeightBound_query_bind_iff, permCallsB, permCalls2, ih]
      exact Iff.rfl

section Games

variable (r : ℕ) {Crs Proof : Type}

/-! ### The statement's oracles, read on byte states -/

theorem relabel_hK (a : List UInt8) : simulateQ relabel (hK a) = hKB a := by
  simp [hK, hKB, relabel]

theorem relabel_pK (x : Lanes) : simulateQ relabel (pK x) = pKB x := by
  simp [pK, pKB, relabel, lanePerm, lanesToState, LeanVM.Rpm.mapQ]
  rfl

theorem relabel_commitCellsM (c : Fin (r * 128) → Cell) :
    simulateQ relabel (commitCellsMWithHash hK c) = commitCellsMWithHash hKB c := by
  rw [commitCellsM_map (fun x ↦ simulateQ relabel x) (fun _ ↦ simulateQ_pure _ _)
    (fun _ _ ↦ simulateQ_bind _ _ _)]
  simp only [relabel_hK]

theorem relabel_verifyCellM (com : Common.DigestBytes) (p : Fin (r * 128)) (x : Cell) (τ : CellOpening) :
    simulateQ relabel (verifyCellMWithHash hK r com p x τ) = verifyCellMWithHash hKB r com p x τ := by
  rw [verifyCellM_map (fun x ↦ simulateQ relabel x) (fun _ ↦ simulateQ_pure _ _)
    (fun _ _ ↦ simulateQ_bind _ _ _)]
  simp only [relabel_hK]

theorem relabel_membershipChallengeM (root : Common.DigestBytes) :
    simulateQ relabel (membershipChallengeMWithHash hK pK root) = membershipChallengeMWithHash hKB pKB root := by
  rw [membershipChallengeM_map (fun x ↦ simulateQ relabel x) (fun _ ↦ simulateQ_pure _ _)
    (fun _ _ ↦ simulateQ_bind _ _ _)]
  simp only [relabel_hK, relabel_pK]

end Games

end LeanDa
