module

public import Quantum.Xmss.NoReuse
public import Quantum.SufCma.GamePar

@[expose] public section

/-!
# Parallel adversaries that never reuse a leaf

`refusePar A` answers a parallel adversary's requests of already requested leaves itself, as
`Quantum.Xmss.refuse` does for sequential adversaries. Rounds pass through, so refusing commutes
with serialization (`serialize_refusePar`); it keeps the width, round and signing budgets
(`isChargeBound_refuseFromPar`), `winProbPar A ≤ winProbPar (refusePar A)`
(`winProbPar_le_refusePar`) and `NoLeafReuse (serialize (refusePar A))`
(`noLeafReuse_serialize_refusePar`).
-/

open IPFunctor
open scoped ENNReal

namespace Quantum.Xmss

open LeanXmss HashSig Common Common.SufCma
  LeanXmss.RandomPermutationModel Quantum.SufCma Quantum.Par
open LeanVM.Semantics (KeccakState)

set_option quotPrecheck false in
local notation "AdvP" S:max => QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec S)

set_option quotPrecheck false in
local notation "AdvPP" S:max => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (advSpecPar SigningRequest (Option Signature) S)

variable {S : Type} [Fintype S] [DecidableEq S]

/-- **Refuse reused leaves, in a parallel program**: rounds pass through, the requests of leaves in
`F` or requested before on the path are answered `none` locally. -/
noncomputable def refuseFromPar {X : QReg → Type} :
    {A : QReg} → Finset LeafIndex → IFreeM (AdvPP S) X A → IFreeM (AdvPP S) X A
  | _, _, .pure x => .pure x
  | _, F, .liftBind (.prim o) next => .liftBind (.prim o) fun b ↦ refuseFromPar F (next b)
  | _, F, .liftBind (.query (.permPar w dir) E ℓ) next =>
      .liftBind (.query (.permPar w dir) E ℓ) fun b ↦ refuseFromPar F (next b)
  | _, F, .liftBind (.query (.sign (r : SigningRequest)) E ℓ) next =>
      if r.leafIndex ∈ F then
        .liftBind (.prim (refuseOp (S := S) r E ℓ)) fun _ ↦
          refuseFromPar F (next (ULift.up none))
      else .liftBind (.query (.sign r) E ℓ) fun b ↦ refuseFromPar (insert r.leafIndex F) (next b)

/-- The parallel adversary that never reuses a leaf. -/
noncomputable def refusePar
    (A : AdversaryPar PublicKey SigningRequest (Option Signature) Forgery S) :
    AdversaryPar PublicKey SigningRequest (Option Signature) Forgery S :=
  fun pk ↦ refuseFromPar ∅ (A pk)

section sign

variable {X : QReg → Type} {A : QReg} {F : Finset LeafIndex} {r : SigningRequest} {E : QReg}
  {ℓ : A ≃ (advSpecPar SigningRequest (Option Signature) S).In (.sign r) × E}
  {next : (b : (AdvPP S).B A (QuantumComp.Cmd.query (AdvPortPar.sign r) E ℓ)) →
    IFreeM (AdvPP S) X ((AdvPP S).src A (QuantumComp.Cmd.query (AdvPortPar.sign r) E ℓ) b)}

/-- A request of a leaf in `F` is refused. -/
theorem refuseFromPar_sign_of_mem (h : r.leafIndex ∈ F) :
    refuseFromPar F (IFreeM.liftBind (QuantumComp.Cmd.query (AdvPortPar.sign r) E ℓ) next) =
      .liftBind (.prim (refuseOp (S := S) r E ℓ)) fun _ ↦
        refuseFromPar F (next (ULift.up none)) := by
  rw [refuseFromPar, ite_eq_left h]

/-- A request of a leaf outside `F` is forwarded, and its leaf joins `F`. -/
theorem refuseFromPar_sign_of_notMem (h : r.leafIndex ∉ F) :
    refuseFromPar F (IFreeM.liftBind (QuantumComp.Cmd.query (AdvPortPar.sign r) E ℓ) next) =
      .liftBind (.query (.sign r) E ℓ) fun b ↦
        refuseFromPar (insert r.leafIndex F) (next b) := by
  rw [refuseFromPar, ite_eq_right h]

end sign

/-- **Refusing passes through a program without signing requests**: refusing after it is refusing
its continuations. -/
theorem refuseFrom_bind_of_noSign {X Y : QReg → Type} (F : Finset LeafIndex) {A : QReg}
    (x : IFreeM (AdvP S) X A) (hx : IFreeM.IsChargeBound x (cmdCharge signCharge) 0)
    (g : ∀ u, X u → IFreeM (AdvP S) Y u) :
    refuseFrom F (IFreeM.bind x g) = IFreeM.bind x fun u l ↦ refuseFrom F (g u l) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind A c next ih =>
    rcases c with o | ⟨p | r, E, ℓ⟩
    · exact congrArg (IFreeM.liftBind (P := AdvP S) (QuantumComp.Cmd.prim o))
        (funext fun b ↦ ih b (hx.2 b))
    · exact congrArg (IFreeM.liftBind (P := AdvP S) (QuantumComp.Cmd.query (.perm p) E ℓ))
        (funext fun b ↦ ih b (hx.2 b))
    · exact absurd hx.1 (by simp [cmdCharge, signCharge])

/-- Refusing passes through the calls of a round. -/
theorem refuseFrom_bind_permRound {X : QReg → Type} (F : Finset LeafIndex) {w : ℕ}
    (dir : Fin w → PermutationPort) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpecPar SigningRequest (Option Signature) S).In (.permPar w dir) × E)
    (g : ∀ u, QuantumComp₂.Leaf
      (QReg.of ((advSpecPar SigningRequest (Option Signature) S).Out (.permPar w dir) × E))
      (Fin w → Unit) u → IFreeM (AdvP S) X u) :
    refuseFrom F (IFreeM.bind (permRound dir E ℓ) g) =
      IFreeM.bind (permRound dir E ℓ) fun u l ↦ refuseFrom F (g u l) :=
  refuseFrom_bind_of_noSign F (permRound dir E ℓ)
    ((isChargeBound_seqCalls (k := fun _ ↦ 0) (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ le_rfl) _ _ _).mono
      (by simp)) g

/-- **Refusing commutes with serialization.** -/
theorem refuseFrom_substitute_toSeq {X : QReg → Type} {A : QReg} (x : IFreeM (AdvPP S) X A)
    (F : Finset LeafIndex) :
    refuseFrom F (IFreeM.substitute toSeq x) = IFreeM.substitute toSeq (refuseFromPar F x) := by
  induction x using IFreeM.inductionOn generalizing F with
  | pure _ _ => rfl
  | liftBind A c next ih =>
    rcases c with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩
    · exact congrArg (IFreeM.liftBind (P := AdvP S) (QuantumComp.Cmd.prim o))
        (funext fun b ↦ ih b F)
    · change refuseFrom F (IFreeM.bind (IFreeM.bind (permRound dir E ℓ) _) _) =
        IFreeM.bind (IFreeM.bind (permRound dir E ℓ) _) _
      refine (congrArg (refuseFrom F) (IFreeM.bind_assoc _ _ _)).trans
        ((refuseFrom_bind_permRound F dir E ℓ _).trans
          ((congrArg (IFreeM.bind (permRound dir E ℓ)) (funext fun u ↦ funext fun l ↦ ?_)).trans
            (IFreeM.bind_assoc _ _ _).symm))
      obtain ⟨rfl, _⟩ := l
      exact ih _ F
    · by_cases hr : r.leafIndex ∈ F
      · rw [refuseFromPar_sign_of_mem hr]
        change refuseFrom F (IFreeM.liftBind (QuantumComp.Cmd.query (.sign r) E ℓ) fun b ↦ _) =
          IFreeM.liftBind (QuantumComp.Cmd.prim (refuseOp (S := S) r E ℓ)) fun b ↦ _
        exact (refuseFrom_sign_of_mem hr).trans
          (congrArg (IFreeM.liftBind (P := AdvP S) (QuantumComp.Cmd.prim (refuseOp r E ℓ)))
            (funext fun _ ↦ ih _ F))
      · rw [refuseFromPar_sign_of_notMem hr]
        change refuseFrom F (IFreeM.liftBind (QuantumComp.Cmd.query (.sign r) E ℓ) fun b ↦ _) =
          IFreeM.liftBind (QuantumComp.Cmd.query (AdvPort.sign r) E ℓ) fun b ↦ _
        exact (refuseFrom_sign_of_notMem hr).trans
          (congrArg (IFreeM.liftBind (P := AdvP S) (QuantumComp.Cmd.query (.sign r) E ℓ))
            (funext fun b ↦ ih b _))

/-- **Refusing commutes with serialization**, for adversaries. -/
theorem serialize_refusePar
    (A : AdversaryPar PublicKey SigningRequest (Option Signature) Forgery S) :
    serialize (refusePar A) = refuse (serialize A) :=
  funext fun pk ↦ (refuseFrom_substitute_toSeq (A pk) ∅).symm

/-- **The serialized refusing adversary never reuses a leaf.** -/
theorem noLeafReuse_serialize_refusePar
    (A : AdversaryPar PublicKey SigningRequest (Option Signature) Forgery S) :
    NoLeafReuse (serialize (refusePar A)) := by
  rw [serialize_refusePar]
  exact noLeafReuse_refuse _

/-- **Refusing keeps every charge bound** of a parallel program (width, rounds, signing
requests): a refused request becomes a local operation, which costs nothing. -/
theorem isChargeBound_refuseFromPar {X : QReg → Type} {c : AdvPortPar SigningRequest → ℕ}
    {A : QReg} (x : IFreeM (AdvPP S) X A) (F : Finset LeafIndex) {n : ℕ}
    (h : IFreeM.IsChargeBound x (cmdChargePar c) n) :
    IFreeM.IsChargeBound (refuseFromPar F x) (cmdChargePar c) n := by
  induction x using IFreeM.inductionOn generalizing F n with
  | pure _ _ => trivial
  | liftBind A c' next ih =>
    rcases c' with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩
    · rw [refuseFromPar]
      exact ⟨h.1, fun b ↦ ih b F (h.2 b)⟩
    · rw [refuseFromPar]
      exact ⟨h.1, fun b ↦ ih b F (h.2 b)⟩
    · by_cases hr : r.leafIndex ∈ F
      · rw [refuseFromPar_sign_of_mem hr]
        exact ⟨Nat.zero_le _, fun _ ↦ (ih _ F (h.2 _)).mono (Nat.sub_le n _)⟩
      · rw [refuseFromPar_sign_of_notMem hr]
        exact ⟨h.1, fun b ↦ ih b _ (h.2 b)⟩

/-- `refusePar A` keeps every charge bound of `A`. -/
theorem isChargeBound_refusePar {c : AdvPortPar SigningRequest → ℕ} {n : ℕ}
    {A : AdversaryPar PublicKey SigningRequest (Option Signature) Forgery S} {pk : PublicKey}
    (h : IFreeM.IsChargeBound (A pk) (cmdChargePar c) n) :
    IFreeM.IsChargeBound (refusePar A pk) (cmdChargePar c) n :=
  isChargeBound_refuseFromPar (A pk) ∅ h

/-- **A parallel adversary wins at most as often as its refusing version**, which never reuses a
leaf. -/
theorem winProbPar_le_refusePar [AddCommGroup S] (e : KeccakState ≃ S)
    (A : AdversaryPar PublicKey SigningRequest (Option Signature) Forgery S) :
    winProbPar sufCmaScheme e A ≤ winProbPar sufCmaScheme e (refusePar A) := by
  rw [winProbPar_eq, winProbPar_eq, serialize_refusePar]
  exact winProb_le_winProb_refuse e (serialize A)

end Quantum.Xmss

end
