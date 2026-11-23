module

public import Quantum.Qrom.Sphincs.DepthBridge

@[expose] public section

/-!
# Budgets and template facts of leanSPHINCS's game with batched rounds

* **Calls by kind** (`chg_gameTPar`, `chg_prefixTPar`): the template game of a parallel adversary
  of total width `q` and at most `signatureLimit` signing requests makes the calls of the
  sequential game (`gameCallsQ`, `prefixCallsQ`): a round of width `w` is `w` calls of `F`.
* **The game with rounds**: total width `q` (`width_gameQPar`), classical calls `clsCapQ`
  (`cls_prefixQPar`) and at most `min d q` rounds (`rounds_gameQPar_min`).
* **The template facts of the hidden masses** (`disc_gameTPar`, `hp_gameTPar`): the batched rounds
  are runtime 1's programs.
-/

open IPFunctor
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Par Quantum.Sponge
open Quantum.Xmss.Assembly (recHwSpec recSpec realizeT revealThen readLift extCls
  isChargeBound_mono_charge chg_act chg_map Disc disc_readLift disc_substitute disc_bind disc₂_bind
  disc_revealThen)

attribute [local irreducible] sphincsRom

set_option quotPrecheck false in
local notation "AdvPP" => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (SufCma.advSpecPar Message (Option Signature))

/-! ## Calls by kind -/

section charges

variable (a b c d : ℕ)

/-- The source charge of the parallel adversary's commands: `α` per call of `H` in a round, `β`
per signing request. -/
def advChargeQPar (α β : ℕ) (A : QReg) (cmd : (AdvPP).A A) : ℕ :=
  α * SufCma.cmdChargePar SufCma.widthCharge A cmd +
    β * SufCma.cmdChargePar SufCma.signChargePar A cmd

/-- The batched round of width `w`: `w` calls of `F`. -/
theorem chg_batRoundT (w : ℕ) (E : QReg) {A : QReg}
    (ℓ : A ≃ hRound Qrom.HashDomain HashOutput w × E) :
    IFreeM.IsChargeBound (batRoundT w E ℓ) (portCharge (tChargeQ SelMem a b c d)) (a * w) := by
  have h : IFreeM.IsChargeBound (batRoundSG TPos SelMem hmsgRoute w E ℓ)
      (portCharge fun i ↦ rdChargeQ SelMem a b (.inl i)) (0 + ((∑ _i : Fin w, a) + 0)) := by
    unfold batRoundSG
    exact FreeM₂.isChargeBound_bind (chg_act _ _ 0) fun _ ↦
      FreeM₂.isChargeBound_bind (isChargeBound_seqCalls
        (c := portCharge fun i ↦ rdChargeQ SelMem a b (.inl i)) (k := fun _ ↦ a)
        (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ le_rfl) _ _ _) fun _ ↦ chg_map _ _ (chg_act _ _ 0)
  refine isChargeBound_readLift a b c d (isChargeBound_liftOrdinary (rdChargeQ SelMem a b)
    (h.mono ?_))
  simp [mul_comm]

/-- **The challenger of a parallel adversary's calls** per command. -/
theorem chg_challengeTPar (pol : DigestPolicy) {S : ℕ}
    (hS : ∀ B msg, IFreeM.IsChargeBound (signT SelMem cwUpd pol B msg)
      (portCharge (tChargeQ SelMem a b c d)) S)
    (A : QReg) (cmd : (AdvPP).A A) :
    IFreeM.IsChargeBound (challengeTPar pol A cmd) (portCharge (tChargeQ SelMem a b c d))
      (advChargeQPar a S A cmd) := by
  rcases cmd with o | ⟨w | r, E, ℓ⟩
  · refine IFreeM.IsChargeBound.mono (IFreeM.IsChargeBound.substitute _
      (chg_challengeT a b c d cwUpd pol hS) (n := 0) ⟨by simp [advChargeQ, SufCma.cmdCharge],
        fun _ ↦ trivial⟩) ?_
    simp [advChargeQPar, SufCma.cmdChargePar]
  · refine IFreeM.IsChargeBound.mono (IFreeM.isChargeBound_bind (chg_batRoundT a b c d w E ℓ)
      fun _ _ ↦ IFreeM.isChargeBound_pure _ 0) ?_
    simp [advChargeQPar, SufCma.cmdChargePar, SufCma.widthCharge, SufCma.signChargePar]
  · refine IFreeM.IsChargeBound.mono (IFreeM.IsChargeBound.substitute _
      (chg_challengeT a b c d cwUpd pol hS) (n := S) ⟨by
        simp [advChargeQ, SufCma.cmdCharge, SufCma.hashCharge, SufCma.signCharge],
        fun _ ↦ trivial⟩) ?_
    simp [advChargeQPar, SufCma.cmdChargePar, SufCma.widthCharge, SufCma.signChargePar]

/-- The challenged parallel adversary's calls: `a` per call of `H`, `S` per signing request. -/
theorem chg_advTPar (pol : DigestPolicy) {S q n : ℕ}
    (hS : ∀ B msg, IFreeM.IsChargeBound (signT SelMem cwUpd pol B msg)
      (portCharge (tChargeQ SelMem a b c d)) S)
    {x : QComp (SufCma.advSpecPar Message (Option Signature)) (QReg.of Unit) (QReg.of Unit)
      Forgery}
    (hw : IFreeM.IsChargeBound x (SufCma.cmdChargePar SufCma.widthCharge) q)
    (hs : IFreeM.IsChargeBound x (SufCma.cmdChargePar SufCma.signChargePar) n) :
    IFreeM.IsChargeBound (advTPar pol x) (portCharge (tChargeQ SelMem a b c d))
      (a * q + S * n) :=
  IFreeM.IsChargeBound.substitute (challengeTPar pol) (chg_challengeTPar a b c d pol hS)
    (IFreeM.IsChargeBound.add ((SufCma.isChargeBound_logSignsPar _ x [] hw).mul a)
      ((SufCma.isChargeBound_logSignsPar _ x [] hs).mul S))

variable {q : ℕ} (pol : DigestPolicy) (A : SAdversaryPar)
  (hw : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.widthCharge) q)
  (hs : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.signChargePar)
    signatureLimit)
include hw hs

/-- **The game's calls by kind.** -/
theorem chg_gameTPar :
    IFreeM.IsChargeBound (gameTPar pol A) (portCharge (tChargeQ SelMem a b c d))
      (gameCallsQ a b c d q) :=
  chg_revealThen a b c d _ _ fun _ ↦ FreeM₂.isChargeBound_bind
    (chg_advTPar a b c d pol (chg_signT a b c d cwUpd pol) (hw _) (hs _)) fun _ ↦
      chg_verifyT a b c d _

/-- **The prefix's calls by kind.** -/
theorem chg_prefixTPar :
    IFreeM.IsChargeBound (prefixTPar pol A) (portCharge (tChargeQ SelMem a b c d))
      (prefixCallsQ a b c d q) :=
  chg_revealThen a b c d _ _ fun _ ↦ FreeM₂.isChargeBound_bind
    (chg_advTPar a b c d pol (chg_signT a b c d cwUpd pol) (hw _) (hs _)) fun _ ↦ trivial

omit hw hs in
/-- The calls of `F` of runtime 2's ports. -/
abbrev spongeQS : (RSpecS SelMem).Port → ℕ :=
  fun i ↦ if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 0 else 1

omit hw hs in
/-- The classical calls of runtime 2's ports. -/
abbrev clsQS : (RSpecS SelMem).Port → ℕ :=
  fun i ↦ if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1 else 0

/-- **At most `q` calls of `F`** in the batched game. -/
theorem advCalls_gameQB (θ : TVals) :
    IFreeM.IsChargeBound (gameQB pol A θ) (portCharge spongeQS) q := by
  have h := (isChargeBound_realizeT 1 0 0 0 θ (chg_gameTPar 1 0 0 0 pol A hw hs)).mono
    (le_of_eq (by simp [gameCallsQ, signCallsQ, selCallsQ, pubCallsQ] : gameCallsQ 1 0 0 0 q = q))
  rw [← advCharge_eq SelMem] at h
  exact h

/-- **At most `q` calls of `F`** in the batched prefix. -/
theorem advCalls_prefixQB (θ : TVals) :
    IFreeM.IsChargeBound (prefixQB pol A θ) (portCharge spongeQS) q := by
  have h := (isChargeBound_realizeT 1 0 0 0 θ (chg_prefixTPar 1 0 0 0 pol A hw hs)).mono
    (le_of_eq (by simp [prefixCallsQ, signCallsQ, selCallsQ, pubCallsQ] :
      prefixCallsQ 1 0 0 0 q = q))
  rw [← advCharge_eq SelMem] at h
  exact h

/-- **At most `clsCapQ` classical calls** in the batched prefix. -/
theorem clsCalls_prefixQB (θ : TVals) :
    IFreeM.IsChargeBound (prefixQB pol A θ) (portCharge clsQS) clsCapQ := by
  have he : clsQS = rChargeQ SelMem 0 1 1 1 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  have h := (isChargeBound_realizeT 0 1 1 1 θ (chg_prefixTPar 0 1 1 1 pol A hw hs)).mono
    (show prefixCallsQ 0 1 1 1 q ≤ clsCapQ by simp only [clsCapQ, gameCallsQ, prefixCallsQ]; omega)
  rw [← he] at h
  exact h

end charges

/-! ## Budgets of the game with rounds -/

section rounds

/-- The rounds of the game with rounds: single calls of `F` and rounds of positive width. -/
abbrev roundsQS : ParRSpecS.Port → ℕ :=
  spongeRounds portS (extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem))

theorem roundsQS_inl_le (i : (RSpecS SelMem).Port) : roundsQS (.inl i) ≤ spongeQS i :=
  roundCharge_le_widthCharge portS _ (.inl i)

/-- A program without calls of `F`, lifted, has no round. -/
theorem roundsQS_liftOrdinary {A : QReg} {Ω : QReg → Type}
    {y : QuantumComp LocalSig.instruments.{0} (RSpecS SelMem) Ω A}
    (h : IFreeM.IsChargeBound y (portCharge spongeQS) 0) :
    IFreeM.IsChargeBound (QuantumComp.liftOrdinary (t := roundSpec (RSpecS SelMem) portS) y)
      (portCharge roundsQS) 0 :=
  Quantum.Qrom.isChargeBound_liftOrdinary _
    (isChargeBound_mono_charge (fun s a ↦ by
      rcases a with o | ⟨i, E, ℓ⟩
      · exact le_rfl
      · exact roundsQS_inl_le i) h)

/-- **A local operation or a signing request of the challenger makes no call of `F`.** -/
theorem challengeTPar_spongeFree (θ : TVals) (pol : DigestPolicy) {A : QReg} (c : (AdvPP).A A)
    (hc : SufCma.cmdChargePar SufCma.widthCharge A c = 0) :
    IFreeM.IsChargeBound (realizeT θ (challengeTPar pol A c)) (portCharge spongeQS) 0 := by
  have h := isChargeBound_realizeT 1 0 0 0 θ (chg_challengeTPar 1 0 0 0 pol
    (fun B msg ↦ chg_signT 1 0 0 0 cwUpd pol B msg) A c)
  rw [← advCharge_eq] at h
  refine h.mono ?_
  simp [advChargeQPar, hc, signCallsQ, selCallsQ, pubCallsQ]

/-- **The rounds of the challenged parallel adversary**: at most its rounds of `H`. -/
theorem rounds_advParS (θ : TVals) (pol : DigestPolicy) {A B : QReg} {α : Type}
    (x : QComp (SufCma.advSpecPar Message (Option Signature)) A B α) {d : ℕ}
    (hx : IFreeM.IsChargeBound x (SufCma.cmdChargePar SufCma.roundCharge) d) :
    IFreeM.IsChargeBound (advParS θ pol x) (portCharge roundsQS) d := by
  refine IFreeM.IsChargeBound.substitute (advSubstS θ pol) (fun s c ↦ ?_)
    (SufCma.isChargeBound_logSignsPar _ x [] hx)
  rcases c with o | ⟨w | r, E, ℓ⟩
  · exact roundsQS_liftOrdinary (challengeTPar_spongeFree θ pol _ rfl)
  · refine IFreeM.isChargeBound_bind (n₂ := 0) ?_ fun _ _ ↦ IFreeM.isChargeBound_pure _ 0
    refine ⟨Nat.zero_le _, fun _ ↦ ⟨?_, fun _ ↦ ⟨Nat.zero_le _, fun _ ↦ trivial⟩⟩⟩
    change roundCharge portS _ (.inr (.round w fun _ ↦ ())) ≤ 1
    unfold roundCharge
    split_ifs <;> omega
  · exact roundsQS_liftOrdinary (challengeTPar_spongeFree θ pol _ rfl)

/-- The public key's reveal makes no call of `F`. -/
theorem pkRevealS_spongeFree (θ : TVals) :
    IFreeM.IsChargeBound (pkRevealS θ) (portCharge spongeQS) 0 := by
  have h0 : IFreeM.IsChargeBound (revealThen (M := SelMem) (B := QReg.of Unit)
      (C := QReg.of Unit) goodQ pkReveal QuantumComp₂.pure)
      (portCharge (tChargeQ SelMem 1 0 0 0)) (0 + 0) :=
    chg_revealThen 1 0 0 0 pkReveal QuantumComp₂.pure fun _ ↦ IFreeM.isChargeBound_pure _ 0
  have h := isChargeBound_realizeT 1 0 0 0 θ h0
  rw [← advCharge_eq] at h
  exact h

variable (pol : DigestPolicy) (A : SAdversaryPar) {q d : ℕ}
  (hw : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.widthCharge) q)
  (hr : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.roundCharge) d)
  (hs : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.signChargePar)
    signatureLimit)

include hr in
/-- **The prefix's rounds**: at most `d`. -/
theorem rounds_prefixQPar (θ : TVals) :
    IFreeM.IsChargeBound (prefixQPar pol A θ) (portCharge roundsQS) d := by
  have h : IFreeM.IsChargeBound (prefixQPar pol A θ) (portCharge roundsQS) (0 + (d + 0)) := by
    unfold prefixQPar
    refine FreeM₂.isChargeBound_bind (roundsQS_liftOrdinary (pkRevealS_spongeFree θ))
      fun r₀ ↦ ?_
    exact FreeM₂.isChargeBound_bind
      (rounds_advParS θ pol (A (tabR r₀.1).publicKey) (hr _)) fun _ ↦ trivial
  rwa [zero_add, add_zero] at h

include hr in
/-- **The game's rounds**: at most `d`. -/
theorem rounds_gameQPar (θ : TVals) :
    IFreeM.IsChargeBound (gameQPar pol A θ) (portCharge roundsQS) d := by
  have h := FreeM₂.isChargeBound_bind (n₂ := 0) (rounds_prefixQPar pol A hr θ) fun x ↦
    roundsQS_liftOrdinary (by
      have h := isChargeBound_realizeT 1 0 0 0 θ (chg_verifyT 1 0 0 0 (M := SelMem) x)
      rw [← advCharge_eq] at h
      exact h.mono (by simp))
  rw [add_zero] at h
  exact h

/-- A charge bound of the serialization is a width bound of the program with rounds. -/
theorem width_of_serializeS {Ω : QReg → Type} {B : QReg}
    {x : QuantumComp LocalSig.instruments.{0} ParRSpecS Ω B} (κ : (RSpecS SelMem).Port → ℕ)
    {n : ℕ} (h : IFreeM.IsChargeBound (IFreeM.substitute (parToSeq portS) x) (portCharge κ) n) :
    IFreeM.IsChargeBound x (portCharge (widthCharge portS κ)) n := by
  rw [portCharge_eq_callCharge] at h ⊢
  exact isChargeBound_of_substitute_parToSeq portS κ (fun _ ↦ ⟨()⟩) x h

include hw hs in
/-- **The game's width**: at most `q` calls of `h`. -/
theorem width_gameQPar (θ : TVals) :
    IFreeM.IsChargeBound (gameQPar pol A θ) (portCharge (spongeWidth portS
      (extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem)))) q := by
  have h := advCalls_gameQB pol A hw hs θ
  rw [gameQB_serialize] at h
  exact width_of_serializeS _ h

include hw hs in
theorem width_prefixQPar (θ : TVals) :
    IFreeM.IsChargeBound (prefixQPar pol A θ) (portCharge (spongeWidth portS
      (extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem)))) q := by
  have h := advCalls_prefixQB pol A hw hs θ
  rw [prefixQB_serialize] at h
  exact width_of_serializeS _ h

include hw hs in
theorem cls_prefixQPar (θ : TVals) :
    IFreeM.IsChargeBound (prefixQPar pol A θ) (portCharge (clsCount portS
      (extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem)))) clsCapQ := by
  have h := clsCalls_prefixQB pol A hw hs θ
  rw [prefixQB_serialize] at h
  exact width_of_serializeS _ h

include hw hr hs in
/-- The rounds are at most `min d q`: a round of positive width makes a call. -/
theorem rounds_gameQPar_min (θ : TVals) :
    IFreeM.IsChargeBound (gameQPar pol A θ) (portCharge roundsQS) (min d q) := by
  rcases le_total d q with h | h
  · rw [min_eq_left h]
    exact rounds_gameQPar pol A hr θ
  · rw [min_eq_right h]
    exact isChargeBound_mono_charge (fun s a ↦ by
      rcases a with o | ⟨i, E, ℓ⟩
      · exact le_rfl
      · exact roundCharge_le_widthCharge portS _ i) (width_gameQPar pol A hw hs θ)

include hw hr hs in
theorem rounds_prefixQPar_min (θ : TVals) :
    IFreeM.IsChargeBound (prefixQPar pol A θ) (portCharge roundsQS) (min d q) := by
  rcases le_total d q with h | h
  · rw [min_eq_left h]
    exact rounds_prefixQPar pol A hr θ
  · rw [min_eq_right h]
    exact isChargeBound_mono_charge (fun s a ↦ by
      rcases a with o | ⟨i, E, ℓ⟩
      · exact le_rfl
      · exact roundCharge_le_widthCharge portS _ i) (width_prefixQPar pol A hw hs θ)

end rounds

/-! ## Template facts of the hidden masses -/

section facts

theorem disc_challengeTPar (pol : DigestPolicy) (A : QReg) (c : (AdvPP).A A) (T : Finset TPos) :
    Disc (challengeTPar pol A c) T := by
  rcases c with o | ⟨w | r, E, ℓ⟩
  · exact disc_substitute _ (disc_challengeT SelMem cwUpd pol) _ T
  · exact disc_bind _ _ (disc_readLift _ T) fun _ _ _ _ ↦ trivial
  · exact disc_substitute _ (disc_challengeT SelMem cwUpd pol) _ T

/-- **The batched game reveals before it programs.** -/
theorem disc_gameTPar (pol : DigestPolicy) (A : SAdversaryPar) (T : Finset TPos) :
    Disc (gameTPar pol A) T :=
  disc_revealThen _ _ T fun _ ↦ disc₂_bind _ _
    (disc_substitute _ (disc_challengeTPar pol) _ _) fun _ T' _ ↦ disc_verifyT SelMem _ T'

theorem hp_challengeTPar (θ : TVals) {pol : DigestPolicy} (hpol : pol.NoVal) (A : QReg)
    (c : (AdvPP).A A) : HP θ (challengeTPar pol A c) ∅ ∅ := by
  rcases c with o | ⟨w | r, E, ℓ⟩
  · exact hp_substitute θ _ (hp_challengeT θ cwUpd hpol) _
  · exact hp_bind θ _ _ (hp_readLift θ _) fun _ _ ↦ subset_rfl
  · exact hp_substitute θ _ (hp_challengeT θ cwUpd hpol) _

/-- **The batched game keeps the invariant.** -/
theorem hp_gameTPar (θ : TVals) {pol : DigestPolicy} (hpol : pol.NoVal) (A : SAdversaryPar) :
    HP θ (gameTPar pol A) ∅ ∅ := by
  rw [gameTPar_eq_prefixTPar_bind]
  refine hp₂_bind θ _ _ (hp_revealThen θ _ _ fun _ ↦ hp_mono θ _
    (hp₂_bind θ _ _ (hp_substitute θ _ (hp_challengeTPar θ hpol) _) fun _ ↦ subset_rfl)
    (Set.union_subset (subset_refl _) (revealSet_pkReveal θ)) subset_rfl) fun x ↦ ?_
  rw [verifyT, readsThenT_eq]
  exact hp₂_bind θ _ _ (hp_readLift θ _) fun _ ↦ subset_rfl

end facts

end Quantum.Qrom.Sphincs

end
