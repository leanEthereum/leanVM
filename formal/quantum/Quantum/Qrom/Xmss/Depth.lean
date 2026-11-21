module

public import Quantum.Qrom.Xmss.DepthBridge
public import Quantum.Qrom.Xmss.Security

@[expose] public section

/-!
# leanXMSS in the QROM against parallel adversaries: the budgets of the game with rounds

A parallel adversary (`Qrom.SufCma.AdversaryPar`) calls `H` in rounds; its game is the game of its
serialization (`Qrom.SufCma.winProbPar_eq`), the serialization of the game with rounds
`gameQPar A θ` (DepthBridge's `gameQ_serialize`). Every cost of the sequential chain is kept on the
serialized adversary; only the event bound and the hidden-value hybrid are redone on the round
runtime, where a round of width `w` costs `√(6 ε w)` (event, `eventWeight_runtimeR_serialize_le`)
and `4 · (its hidden mass)` (hybrid, `Hybrid.uavg_win_runtime1R_par_le_graded_total`). Summed
over the `d` rounds by Cauchy-Schwarz, `q√(6ε)` becomes `√(6 ε d q)` and `2q·2^-64` becomes
`2√(d q)·2^-64`, with `d` replaced by `min d q` (a round of positive width has a call).

This file gives the three budgets of the game with rounds that these bounds need:

* **Rounds** (`rounds_prefixQPar`, `rounds_gameQPar`): at most `d` rounds of `h`, since the
  challenger's commands and the reveals make no sponge call (`cmdQ_spongeFree`,
  `pkRevealQ_spongeFree`); at most `min d q` (`rounds_gameQPar_min`), since a round of positive
  width makes a call.
* **Width** (`width_prefixQPar`, `width_gameQPar`): at most `q` calls of `h`, and
  **classical calls** (`cls_prefixQPar`): at most `clsCapQ`, both from the budgets of the
  serialized game (`width_of_serialize`).

The hybrid is DepthHybrid, the event DepthEnd, the theorem DepthSecurity and the closed form
DepthBoundValue.
-/

open IPFunctor
open scoped ENNReal Kronecker

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Par Quantum.Sponge Quantum.Xmss.Hybrid
open LeanXmss HashSig
open Quantum.Xmss.Assembly (recHwSpec recSpec realizeT runtimeR runtime1R extCls extWeight
  isChargeBound_mono_charge eventWeight_runtimeR_serialize_le)

attribute [local irreducible] xmssRom

/-! ## Charges of the game with rounds -/

section charges

/-- The sponge calls of runtime 2's ports. -/
abbrev spongeQ : (RSpec SelMem).Port → ℕ :=
  fun i ↦ if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 0 else 1

/-- The classical calls of runtime 2's ports. -/
abbrev clsQ : (RSpec SelMem).Port → ℕ :=
  fun i ↦ if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 1 else 0

/-- The rounds of the game with rounds: single sponge calls and rounds of positive width. -/
abbrev roundsQ : ParRSpec.Port → ℕ :=
  spongeRounds portQ (extCls HashOutput HashDomain QMem (recSpec HPos SelMem))

theorem roundsQ_inl_le (i : (RSpec SelMem).Port) : roundsQ (.inl i) ≤ spongeQ i :=
  roundCharge_le_widthCharge portQ _ (.inl i)

theorem hwExtCls_eq :
    hwExtCls HashOutput HashDomain QMem (recSpec HPos SelMem) =
      extCls HashOutput HashDomain QMem (recSpec HPos SelMem) := by
  funext i
  rcases i with i | j <;> rfl

/-- A program without sponge calls, lifted, has no round. -/
theorem rounds_liftOrdinary {A : QReg} {Ω : QReg → Type}
    {y : QuantumComp LocalSig.instruments.{0} (RSpec SelMem) Ω A}
    (h : IFreeM.IsChargeBound y (portCharge spongeQ) 0) :
    IFreeM.IsChargeBound (QuantumComp.liftOrdinary (t := roundSpec (RSpec SelMem) portQ) y)
      (portCharge roundsQ) 0 :=
  Quantum.Qrom.isChargeBound_liftOrdinary _
    (isChargeBound_mono_charge (fun s a ↦ by
      rcases a with o | ⟨i, E, ℓ⟩
      · exact le_rfl
      · exact roundsQ_inl_le i) h)

/-- **The challenger's local operations and signing requests make no sponge call.** -/
theorem cmdQ_spongeFree (θ : HPos → Digest) (P : PublicParameter) {A : QReg}
    (c : QuantumComp.Cmd LocalSig.instruments.{0}
      (SufCma.advSpecPar SigningRequest (Option Signature)) A)
    (hc : IFreeM.IsChargeBound (SufCma.toSeq A c) (advChargeQ 1 0) 0) :
    IFreeM.IsChargeBound (cmdQ θ P A c) (portCharge spongeQ) 0 := by
  have hS : ∀ B r, IFreeM.IsChargeBound (signT SelMem cwUpd P B r)
      (portCharge (tChargeQ SelMem 1 0 0 0 0)) 0 := fun B r ↦
    (chg_signT 1 0 0 0 0 cwUpd P B r).mono (by simp [reqCallsQ])
  have h := isChargeBound_realizeT 1 0 0 0 0 θ (IFreeM.IsChargeBound.substitute
    (challengeT SelMem cwUpd P) (chg_challengeT 1 0 0 0 0 cwUpd P hS) hc)
  rw [← advCharge_eq] at h
  exact h

/-- **The rounds of the challenged parallel adversary**: at most its rounds of `H`. -/
theorem rounds_advParQ (θ : HPos → Digest) (P : PublicParameter) {A B : QReg} {α : Type}
    (x : QComp (SufCma.advSpecPar SigningRequest (Option Signature)) A B α) {d : ℕ}
    (hx : IFreeM.IsChargeBound x (SufCma.cmdChargePar SufCma.roundCharge) d) :
    IFreeM.IsChargeBound (advParQ θ P x) (portCharge roundsQ) d := by
  refine IFreeM.IsChargeBound.substitute (advSubstQ θ P) (fun s c ↦ ?_)
    (SufCma.isChargeBound_logSignsPar _ x [] hx)
  rcases c with o | ⟨w | r, E, ℓ⟩
  · exact rounds_liftOrdinary (cmdQ_spongeFree θ P _ ⟨by simp [advChargeQ, SufCma.cmdCharge],
      fun _ ↦ trivial⟩)
  · refine ⟨?_, fun _ ↦ trivial⟩
    change roundCharge portQ _ (.inr (.round w fun _ ↦ ())) ≤ 1
    unfold roundCharge
    split_ifs <;> omega
  · exact rounds_liftOrdinary (cmdQ_spongeFree θ P _ ⟨by
      simp [advChargeQ, SufCma.cmdCharge, SufCma.hashCharge, SufCma.signCharge],
      fun _ ↦ trivial⟩)

/-- The public key's reveal makes no sponge call. -/
theorem pkRevealQ_spongeFree (θ : HPos → Digest) :
    IFreeM.IsChargeBound (pkRevealQ θ) (portCharge spongeQ) 0 := by
  have h0 : IFreeM.IsChargeBound (Quantum.Xmss.Assembly.revealThen (M := SelMem)
      (B := QReg.of Unit) (C := QReg.of Unit) goodQ pkReveal QuantumComp₂.pure)
      (portCharge (tChargeQ SelMem 1 0 0 0 0)) (0 + 0) :=
    chg_revealThen 1 0 0 0 0 pkReveal QuantumComp₂.pure fun _ ↦ IFreeM.isChargeBound_pure _ 0
  have h := isChargeBound_realizeT 1 0 0 0 0 θ h0
  rw [← advCharge_eq] at h
  exact h

variable (A : AdversaryPar) {q d : ℕ}
  (hw : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.widthCharge) q)
  (hr : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.roundCharge) d)
  (hs : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.signChargePar) lifetime)

include hr in
/-- **The prefix's rounds**: at most `d`. -/
theorem rounds_prefixQPar (θ : HPos → Digest) :
    IFreeM.IsChargeBound (prefixQPar A θ) (portCharge roundsQ) d := by
  have h : IFreeM.IsChargeBound (prefixQPar A θ) (portCharge roundsQ) (0 + (d + 0)) := by
    unfold prefixQPar
    refine FreeM₂.isChargeBound_bind (rounds_liftOrdinary (pkRevealQ_spongeFree θ))
      fun r₀ ↦ ?_
    exact FreeM₂.isChargeBound_bind
      (rounds_advParQ θ (pkT r₀.1).parameter (A (pkT r₀.1)) (hr _)) fun _ ↦ trivial
  rwa [zero_add, add_zero] at h

include hr in
/-- **The game's rounds**: at most `d`. -/
theorem rounds_gameQPar (θ : HPos → Digest) :
    IFreeM.IsChargeBound (gameQPar A θ) (portCharge roundsQ) d := by
  have h := FreeM₂.isChargeBound_bind (n₂ := 0) (rounds_prefixQPar A hr θ) fun x ↦
    rounds_liftOrdinary (by
      have h := isChargeBound_realizeT 1 0 0 0 0 θ (chg_verifyT 1 0 0 0 0 (M := SelMem) x)
      rw [← advCharge_eq] at h
      exact h.mono (by simp))
  rw [add_zero] at h
  exact h

/-- A charge bound of the serialization is a width bound of the program with rounds. -/
theorem width_of_serialize {Ω : QReg → Type} {B : QReg}
    {x : QuantumComp LocalSig.instruments.{0} ParRSpec Ω B} (c : (RSpec SelMem).Port → ℕ) {n : ℕ}
    (h : IFreeM.IsChargeBound (IFreeM.substitute (parToSeq portQ) x) (portCharge c) n) :
    IFreeM.IsChargeBound x (portCharge (widthCharge portQ c)) n := by
  rw [portCharge_eq_callCharge] at h ⊢
  exact isChargeBound_of_substitute_parToSeq portQ c (fun _ ↦ ⟨()⟩) x h

include hw hs in
/-- **The game's width**: at most `q` calls of `h`. -/
theorem width_gameQPar (θ : HPos → Digest) :
    IFreeM.IsChargeBound (gameQPar A θ) (portCharge (spongeWidth portQ
      (extCls HashOutput HashDomain QMem (recSpec HPos SelMem)))) q := by
  have h := advCalls_gameQ cwUpd (SufCma.serialize A) (fun pk ↦ SufCma.isChargeBound_toSeq_hash
    (hw pk)) (fun pk ↦ SufCma.isChargeBound_toSeq_sign (hs pk)) θ
  change IFreeM.IsChargeBound (gameQ (SufCma.serialize A) θ) _ q at h
  rw [gameQ_serialize] at h
  exact width_of_serialize _ h

include hw hs in
theorem width_prefixQPar (θ : HPos → Digest) :
    IFreeM.IsChargeBound (prefixQPar A θ) (portCharge (spongeWidth portQ
      (extCls HashOutput HashDomain QMem (recSpec HPos SelMem)))) q := by
  have h := advCalls_prefixQ cwUpd (SufCma.serialize A) (fun pk ↦ SufCma.isChargeBound_toSeq_hash
    (hw pk)) (fun pk ↦ SufCma.isChargeBound_toSeq_sign (hs pk)) θ
  change IFreeM.IsChargeBound (prefixQ (SufCma.serialize A) θ) _ q at h
  rw [prefixQ_serialize] at h
  exact width_of_serialize _ h

include hw hs in
theorem cls_prefixQPar (θ : HPos → Digest) :
    IFreeM.IsChargeBound (prefixQPar A θ) (portCharge (clsCount portQ
      (extCls HashOutput HashDomain QMem (recSpec HPos SelMem)))) clsCapQ := by
  have h := clsCalls_prefixQ cwUpd (SufCma.serialize A) (fun pk ↦ SufCma.isChargeBound_toSeq_hash
    (hw pk)) (fun pk ↦ SufCma.isChargeBound_toSeq_sign (hs pk)) θ
  change IFreeM.IsChargeBound (prefixQ (SufCma.serialize A) θ) _ clsCapQ at h
  rw [prefixQ_serialize] at h
  exact width_of_serialize _ h

include hw hr hs in
/-- The rounds are at most `min d q`: a round of positive width makes a call. -/
theorem rounds_gameQPar_min (θ : HPos → Digest) :
    IFreeM.IsChargeBound (gameQPar A θ) (portCharge roundsQ) (min d q) := by
  rcases le_total d q with h | h
  · rw [min_eq_left h]
    exact rounds_gameQPar A hr θ
  · rw [min_eq_right h]
    exact isChargeBound_mono_charge (fun s a ↦ by
      rcases a with o | ⟨i, E, ℓ⟩
      · exact le_rfl
      · exact roundCharge_le_widthCharge portQ _ i) (width_gameQPar A hw hs θ)

include hw hr hs in
theorem rounds_prefixQPar_min (θ : HPos → Digest) :
    IFreeM.IsChargeBound (prefixQPar A θ) (portCharge roundsQ) (min d q) := by
  rcases le_total d q with h | h
  · rw [min_eq_left h]
    exact rounds_prefixQPar A hr θ
  · rw [min_eq_right h]
    exact isChargeBound_mono_charge (fun s a ↦ by
      rcases a with o | ⟨i, E, ℓ⟩
      · exact le_rfl
      · exact roundCharge_le_widthCharge portQ _ i) (width_prefixQPar A hw hs θ)

end charges

end Quantum.Qrom.Xmss

end
