module

public import Quantum.Sphincs.Assembly.GameTCalls.Charges
public import Quantum.Sphincs.Assembly.ReparamFull.Game

@[expose] public section

/-!
# The recorded candidate coordinates of leanSPHINCS's canonical game

Mismatch's averaging (`sum_revW_le`, KeyLazy's `uavg_kW_table_le`, MassSources' `chgRevAvg`) needs
`hR`: every path of the canonical game records at most `R` coordinates of a candidate set `J`
(`candCharge J`: a reveal of `T` costs `|T ∩ J|`). The charged coordinates of the composed
reparametrization (`chgB t`) are randomizers and `H_msg` outputs, so the candidates are a set `J`
without value coordinates.

* `candT J`: the template charge (a reveal of `T` costs `|T ∩ J|`); `isChargeBound_realizeT_candT`
  realizes it as `candCharge J`.
* A reveal of value positions costs nothing (`card_valSet_inter_eq_zero`), so the FORS opening and
  the layer signatures cost nothing; a signature costs `c₁ + c₂` (`chg_signT_candT`: the reveal of
  `{PK.root, R(M)}` and the policy's digest coordinates); the root's reveal and the verification's
  reads cost nothing (`chg_gameT_candT`).
* `isChargeBound_gameR_cand`: at `msgPol`, for `J` without value coordinates, every path records at
  most `3 · signatureLimit` candidates (one randomizer and two `H_msg` outputs per signing request);
  `isChargeBound_gameR_rndDig` at `J = rndDigJ` (all randomizers and `H_msg` outputs,
  `chgB t ⊆ rndDigJ`); `isChargeBound_gameR_cand_rnd`: `signatureLimit` for `J` of randomizers.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker

universe u v w

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs Common
open HashSig (Message)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (LazyProg candCharge)
open Quantum.Xmss.Assembly (recHwSpec readLift readLens tmplLens realizeT revealThen progThen
  rdCharge chg_act chg_map chg_readsProgram RevealVals isChargeBound_simulate)

namespace Quantum.Sphincs.Assembly

/-! ## The candidate sets -/

/-- A randomizer or an `H_msg` output coordinate. -/
def IsRndDig : HPos → Prop
  | .rnd _ => True
  | .dig _ _ => True
  | _ => False

open scoped Classical in
/-- **All randomizer and `H_msg` output coordinates.** Irreducible: membership does not unfold the
enumeration of the coordinates. -/
@[irreducible]
noncomputable def rndDigJ : Finset HPos :=
  Finset.univ.filter IsRndDig

theorem mem_rndDigJ {s : HPos} : s ∈ rndDigJ ↔ IsRndDig s := by
  unfold rndDigJ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem val_notMem_rndDigJ (p : ValPos) : HPos.val p ∉ rndDigJ :=
  fun h ↦ mem_rndDigJ.mp h

/-- **The charged coordinates are candidates.** -/
theorem chgB_subset_rndDigJ (t : FT) : chgB t ⊆ rndDigJ := by
  intro s hs
  refine mem_rndDigJ.mpr ?_
  have h := mem_chgB.mp hs
  cases s with
  | val q => exact h
  | rnd M => trivial
  | dig M i => trivial
  | str j i => exact h
  | asg M j => exact h

/-- A reveal of value positions records no candidate. -/
theorem card_valSet_inter_eq_zero {J : Finset HPos} (hJ : ∀ p, HPos.val p ∉ J)
    (T : Finset ValPos) : (valSet T ∩ J).card = 0 := by
  refine Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun s hs ↦ ?_)
  obtain ⟨hs₁, hs₂⟩ := Finset.mem_inter.mp hs
  unfold valSet at hs₁
  obtain ⟨p, -, rfl⟩ := Finset.mem_map.mp hs₁
  exact hJ p hs₂

/-- The signer's first reveal records at most the randomizer. -/
theorem card_root_rnd_inter_le {J : Finset HPos} (hJ : ∀ p, HPos.val p ∉ J) (p : ValPos)
    (msg : Message) :
    (({.val p, .rnd msg} : Finset HPos) ∩ J).card ≤ (({.rnd msg} : Finset HPos) ∩ J).card := by
  refine Finset.card_le_card fun s hs ↦ ?_
  obtain ⟨hs₁, hs₂⟩ := Finset.mem_inter.mp hs
  refine Finset.mem_inter.mpr ⟨?_, hs₂⟩
  rcases Finset.mem_insert.mp hs₁ with rfl | h
  · exact absurd hs₂ (hJ p)
  · exact h

theorem card_singleton_inter_le_one (s : HPos) (J : Finset HPos) :
    (({s} : Finset HPos) ∩ J).card ≤ 1 :=
  (Finset.card_le_card Finset.inter_subset_left).trans_eq (Finset.card_singleton s)

theorem card_singleton_inter_eq_zero {s : HPos} {J : Finset HPos} (h : s ∉ J) :
    (({s} : Finset HPos) ∩ J).card = 0 :=
  Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun t ht ↦ by
    obtain ⟨ht₁, ht₂⟩ := Finset.mem_inter.mp ht
    rw [Finset.mem_singleton.mp ht₁] at ht₂
    exact h ht₂)

/-- `msgPol`'s digest coordinates record at most two candidates. -/
theorem card_msgPol_need_inter_le (J : Finset HPos) (T : Finset HPos) (msg : Message) :
    (msgPol.need T msg ∩ J).card ≤ 2 := by
  refine (Finset.card_le_card Finset.inter_subset_left).trans ?_
  unfold DigestPolicy.need
  refine (Finset.card_insert_le _ _).trans ?_
  refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
  show (∅ : Finset HPos).card + 1 ≤ 1
  rw [Finset.card_empty]

/-- `msgPol`'s digest coordinates record no candidate outside the `H_msg` outputs. -/
theorem card_msgPol_need_inter_eq_zero {J : Finset HPos} (hJ : ∀ msg i, HPos.dig msg i ∉ J)
    (T : Finset HPos) (msg : Message) : (msgPol.need T msg ∩ J).card = 0 := by
  refine Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun s hs ↦ ?_)
  obtain ⟨hs₁, hs₂⟩ := Finset.mem_inter.mp hs
  unfold DigestPolicy.need at hs₁
  rcases Finset.mem_insert.mp hs₁ with rfl | hs₁
  · exact hJ msg 0 hs₂
  rcases Finset.mem_insert.mp hs₁ with rfl | hs₁
  · exact hJ msg 1 hs₂
  · exact Finset.notMem_empty s hs₁

/-! ## The template charge -/

section cand

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

variable (M) in
/-- The template charge counting the candidates `J` a reveal records. -/
def candT (J : Finset HPos) : (SSpec M).Port → ℕ
  | .inl _ => 0
  | .inr T => (T ∩ J).card

variable (J : Finset HPos)

omit [Fintype M] [DecidableEq M] in
/-- **Realizing keeps the candidate charge.** -/
theorem isChargeBound_realizeT_candT (v : (s : HPos) → XD s) {A : QReg}
    {y : QuantumComp L (SSpec M) Ω A} {n : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge (candT M J)) n) :
    IFreeM.IsChargeBound (realizeT v y) (portCharge (candCharge X Z M J)) n := by
  refine IFreeM.IsChargeBound.mapLens (tmplLens v) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (candCharge X Z M J) s
      ((tmplLens v).toFunA s cmd)) = portCharge (candT M J) := by
    funext s cmd
    rcases cmd with o | ⟨((i | c) | p) | T, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

omit [Fintype M] [DecidableEq M] in
theorem isChargeBound_readLift_candT {A : QReg} {y : QuantumComp L (hwReadSpec X Z M) Ω A}
    {n : ℕ} (h : IFreeM.IsChargeBound y (portCharge (rdCharge M 0 0)) n) :
    IFreeM.IsChargeBound (readLift goodAll y) (portCharge (candT M J)) n := by
  refine IFreeM.IsChargeBound.mapLens (readLens goodAll) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (candT M J) s
      ((readLens goodAll).toFunA s cmd)) = portCharge (rdCharge M 0 0) := by
    funext s cmd
    rcases cmd with o | ⟨i | c, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

omit [Fintype M] [DecidableEq M] in
theorem chg_revealThen_candT {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (SSpec M) B B' α) {n : ℕ}
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge (candT M J)) n) :
    IFreeM.IsChargeBound (revealThen goodAll T k) (portCharge (candT M J))
      ((T ∩ J).card + n) := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr
    ⟨Nat.le_add_right _ n, fun r ↦ ?_⟩
  simp only [candT, Nat.add_sub_cancel_left]
  exact IFreeM.IsChargeBound.mono
    (FreeM₂.isChargeBound_bind (n₁ := 0) (chg_act _ _ 0) fun _ ↦ hk r) (Nat.zero_add n).le

omit [Fintype M] [DecidableEq M] in
/-- A reveal of value positions costs nothing. -/
theorem chg_revealThen_valSet_candT (hJ : ∀ p, HPos.val p ∉ J) {B B' : QReg} {α : Type}
    (T : Finset ValPos) (k : RevealVals XD (valSet T) × (Finset HPos × M) → QComp (SSpec M) B B' α)
    {n : ℕ} (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge (candT M J)) n) :
    IFreeM.IsChargeBound (revealThen goodAll (valSet T) k) (portCharge (candT M J)) n := by
  have h := chg_revealThen_candT J (valSet T) k hk
  rwa [card_valSet_inter_eq_zero hJ, Nat.zero_add] at h

omit [Fintype M] [DecidableEq M] in
theorem chg_progThen_candT {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (SSpec M) B B' α) {n : ℕ}
    (hk : IFreeM.IsChargeBound k (portCharge (candT M J)) n) :
    IFreeM.IsChargeBound (progThen p hp k) (portCharge (candT M J)) n := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.zero_le n, fun r ↦ ?_⟩
  simp only [candT, Nat.sub_zero]
  exact IFreeM.IsChargeBound.mono
    (FreeM₂.isChargeBound_bind (n₁ := 0) (chg_act _ _ 0) fun _ ↦ hk) (Nat.zero_add n).le

omit [Fintype M] [DecidableEq M] in
theorem chg_progPorts_candT (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    IFreeM.IsChargeBound (progPorts M B ps) (portCharge (candT M J)) 0 := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact chg_progThen_candT J p trivial _ ih

omit [Fintype M] [DecidableEq M] in
theorem chg_progSlots_candT (pub : Pub) (B : QReg) (ss : List Slot) :
    IFreeM.IsChargeBound (progSlots M pub B ss) (portCharge (candT M J)) 0 := by
  induction ss with
  | nil => trivial
  | cons s ss ih =>
    exact FreeM₂.isChargeBound_bind (n₁ := 0) (chg_progPorts_candT J B _) fun _ ↦ ih

variable {J} (hJ : ∀ p, HPos.val p ∉ J)
include hJ

omit [Fintype M] [DecidableEq M] in
/-- **A FORS opening records no candidate.** -/
theorem chg_forsOpenT_candT (pub : Pub) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) :
    IFreeM.IsChargeBound (forsOpenT M pub B idx lv) (portCharge (candT M J)) 0 := by
  unfold forsOpenT
  exact chg_revealThen_valSet_candT J hJ _ _ fun _ ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_progSlots_candT J pub B _) fun _ ↦ trivial

variable (upd : TrialUpd M)

omit [Fintype M] [DecidableEq M] in
/-- **A layer signature records no candidate.** -/
theorem chg_signLayerT_candT (pub : Pub) (B : QReg) (K : Key) :
    IFreeM.IsChargeBound (signLayerT M upd pub B K) (portCharge (candT M J)) 0 := by
  unfold signLayerT
  refine IFreeM.IsChargeBound.mono (chg_revealThen_candT (n := 0) J _ _ fun _ ↦ ?_)
    (by rw [card_singleton_inter_eq_zero (hJ _)])
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (isChargeBound_readLift_candT J
    (IFreeM.IsChargeBound.mono (chg_grindK 0 0 upd pub B K _ _ _) (by simp))) fun g ↦ ?_
  rcases g with _ | ⟨c, x⟩
  · trivial
  · exact chg_revealThen_valSet_candT J hJ _ _ fun _ ↦
      FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_progSlots_candT J pub B _) fun _ ↦
        trivial

omit [Fintype M] [DecidableEq M] in
/-- **A signature records at most `c₁ + c₂` candidates**: its reveal of `{PK.root, R(M)}` (at most
`c₁` of `R(M)`) and of the policy's digest coordinates (at most `c₂`). -/
theorem chg_signT_candT (pol : DigestPolicy) (pub : Pub) {c₁ c₂ : ℕ}
    (h₁ : ∀ msg : Message, (({.rnd msg} : Finset HPos) ∩ J).card ≤ c₁)
    (h₂ : ∀ T msg, (pol.need T msg ∩ J).card ≤ c₂) (B : QReg) (msg : Message) :
    IFreeM.IsChargeBound (signT M upd pol pub B msg) (portCharge (candT M J)) (c₁ + c₂) := by
  unfold signT
  refine IFreeM.IsChargeBound.mono (chg_revealThen_candT (n := c₂) J _ _ fun r₁ ↦
    IFreeM.IsChargeBound.mono (chg_revealThen_candT (n := 0) J _ _ fun r₂ ↦ ?_)
      ((Nat.add_zero _).le.trans (h₂ _ msg)))
    (Nat.add_le_add_right ((card_root_rnd_inter_le hJ _ msg).trans (h₁ msg)) c₂)
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_progPorts_candT J B _) fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_forsOpenT_candT hJ pub B _ _)
    fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_signLayerT_candT hJ upd pub B _)
    fun s₀ ↦ ?_
  rcases s₀ with _ | bottom
  · trivial
  · refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_signLayerT_candT hJ upd pub B _)
      fun s₁ ↦ ?_
    rcases s₁ with _ | middle
    · trivial
    · refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
        (chg_signLayerT_candT hJ upd pub B _) fun s₂ ↦ ?_
      rcases s₂ with _ | top <;> trivial

omit hJ [Fintype M] [DecidableEq M] in
/-- **The challenger's candidates** per command: `S` per signing request, none otherwise. -/
theorem chg_challengeT_candT (pol : DigestPolicy) (pub : Pub) {S : ℕ}
    (hS : ∀ B msg, IFreeM.IsChargeBound (signT M upd pol pub B msg) (portCharge (candT M J)) S)
    (A : QReg) (cmd : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    IFreeM.IsChargeBound (challengeT M upd pol pub A cmd) (portCharge (candT M J))
      (S * cmdCharge signCharge A cmd) := by
  rcases cmd with o | ⟨p | msg, E, ℓ⟩
  · refine IFreeM.IsChargeBound.mono (isChargeBound_readLift_candT J (isChargeBound_simulate 0 0
      _ (q := 0) ((QuantumComp.isTotalQueryBound_primBind_iff _ _ _).mpr fun _ ↦ trivial))) ?_
    simp [cmdCharge]
  · refine IFreeM.IsChargeBound.mono (isChargeBound_readLift_candT J (isChargeBound_simulate 0 0
      _ (q := 1) ((QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
        ⟨Nat.one_pos, fun _ ↦ trivial⟩))) ?_
    simp [cmdCharge, signCharge]
  · refine IFreeM.IsChargeBound.mono (IFreeM.isChargeBound_bind (FreeM₂.isChargeBound_bind
      (n₁ := 0) (chg_act _ _ 0) fun _ ↦ hS _ msg) fun _ _ ↦ IFreeM.isChargeBound_pure _ 0) ?_
    simp only [cmdCharge, signCharge]
    omega

omit [Fintype M] [DecidableEq M] in
/-- **The template game records at most `(c₁ + c₂) · signatureLimit` candidates** for an
adversary making at most `signatureLimit` signing requests on every path: none at the root's
reveal and at the verification's reads, `c₁ + c₂` per signature. -/
theorem chg_gameT_candT (pol : DigestPolicy) (pub : Pub) {c₁ c₂ : ℕ}
    (h₁ : ∀ msg : Message, (({.rnd msg} : Finset HPos) ∩ J).card ≤ c₁)
    (h₂ : ∀ T msg, (pol.need T msg ∩ J).card ≤ c₂) (A : SAdversary)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit) :
    IFreeM.IsChargeBound (gameT M upd pol pub A) (portCharge (candT M J))
      ((c₁ + c₂) * signatureLimit) := by
  unfold gameT
  refine IFreeM.IsChargeBound.mono
    (chg_revealThen_candT (n := (c₁ + c₂) * signatureLimit) J _ _ fun r₀ ↦ ?_)
    (by rw [card_singleton_inter_eq_zero (hJ _), Nat.zero_add])
  have hc := IFreeM.IsChargeBound.substitute_mul (challengeT M upd pol pub) (c₁ + c₂)
    (chg_challengeT_candT upd pol pub (chg_signT_candT hJ upd pol pub h₁ h₂))
    (isChargeBound_withSignLog (hsign (pkOf pub r₀.1)))
  refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0) hc fun run ↦ ?_)
    (Nat.add_zero _).le
  have hv := chg_readsProgram (M := M) 0 0 pub.perm (QReg.of Unit)
    (verify_hashBlocks (pkOf pub r₀.1) run.1)
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    (isChargeBound_readLift_candT J (IFreeM.IsChargeBound.mono (chg_map _ Prod.fst hv)
      (by simp))) fun _ ↦ trivial

end cand

/-! ## The canonical game -/

section gameR

variable {J : Finset HPos} (hJ : ∀ p, HPos.val p ∉ J) (A : SAdversary)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hJ hsign

/-- **The canonical game's candidates**, for every digest policy: at most `(c₁ + c₂) ·
signatureLimit`, `c₁` bounding the randomizer's and `c₂` the policy's digest coordinates. -/
theorem isChargeBound_gameR_cand_of (pol : DigestPolicy) {c₁ c₂ : ℕ}
    (h₁ : ∀ msg : Message, (({.rnd msg} : Finset HPos) ∩ J).card ≤ c₁)
    (h₂ : ∀ T msg, (pol.need T msg ∩ J).card ≤ c₂) (pub : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (gameR pol A pub v) (portCharge (candCharge X Z Selections J))
      ((c₁ + c₂) * signatureLimit) :=
  isChargeBound_realizeT_candT J v (chg_gameT_candT hJ cwUpd pol pub h₁ h₂ A hsign)

/-- **`hR` at `msgPol`**: for candidates `J` without value coordinates, every path of the
canonical game records at most `3 · signatureLimit` of them (one randomizer and two `H_msg`
outputs per signing request). -/
theorem isChargeBound_gameR_cand (pub : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (gameR msgPol A pub v) (portCharge (candCharge X Z Selections J))
      (3 * signatureLimit) :=
  isChargeBound_gameR_cand_of hJ A hsign msgPol (c₁ := 1) (c₂ := 2)
    (fun _ ↦ card_singleton_inter_le_one _ J) (card_msgPol_need_inter_le J) pub v

/-- **`hR` at `msgPol` for candidates among the randomizers**: at most `signatureLimit`. -/
theorem isChargeBound_gameR_cand_rnd (hJd : ∀ msg i, HPos.dig msg i ∉ J) (pub : Pub)
    (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (gameR msgPol A pub v) (portCharge (candCharge X Z Selections J))
      signatureLimit := by
  have h := isChargeBound_gameR_cand_of hJ A hsign msgPol (c₁ := 1) (c₂ := 0)
    (fun _ ↦ card_singleton_inter_le_one _ J)
    (fun T msg ↦ (card_msgPol_need_inter_eq_zero hJd T msg).le) pub v
  rwa [Nat.add_zero, Nat.one_mul] at h

end gameR

/-- **`hR` for all randomizers and `H_msg` outputs** (`rndDigJ ⊇ chgB t`): at most
`3 · signatureLimit`. -/
theorem isChargeBound_gameR_rndDig (A : SAdversary)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
    (pub : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (gameR msgPol A pub v) (portCharge (candCharge X Z Selections rndDigJ))
      (3 * signatureLimit) :=
  isChargeBound_gameR_cand val_notMem_rndDigJ A hsign pub v

end Quantum.Sphincs.Assembly

end
