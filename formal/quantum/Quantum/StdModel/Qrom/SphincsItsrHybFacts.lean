module

public import Quantum.StdModel.Qrom.SphincsItsrGame

@[expose] public section

/-!
# The ITSR template game of leanSPHINCS: lazy sampling, the source invariant, the stream

The facts of the runtime-2 template game (`Quantum.Qrom.Sphincs.Template`, `GameTFacts`,
`StreamGame`) for the ITSR template game `gameIT` (`Quantum.StdModel.Qrom.SphincsItsrGame`). The
data fold `foldT` runs, per signed message, the signer's first three steps (`signT`): reveal
`PK.seed`, `PK.root`, `R(M)`, reveal the digest policy's coordinates, hardwire the digest cell; so
each fact is the first part of the signer's.

* **Lazy sampling**: `disc_gameIT`, `keepsLab_gameIT` (the game reveals before it programs, its
  reads keep the label), hence `viewBy_gameIT`, `viewByOn_gameIT`.
* **The source invariant** (`HP`, GameTFacts): `hp_foldT` (the reveal of `R(M)` makes the digest
  cell pending, the digest port programs it), `hp_gameIT`, `forallQueries_gameIT`, `hinvI`.
* **The stream reindexing** (`RenSim`, StreamGame): `renSim_foldT` (the digest reveal of `strPol`
  is simulated by `msgPol`'s, the digest ports and the data agree), `renSim_prefixIT`,
  `renSim_gameIT`; **`uavg_gameIT_msgPol_eq_strPol`**.
-/

open Matrix
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.StdModel.Sphincs.SphItsr

open Quantum QuantumRuntime
open Quantum.Qrom.Sphincs
open Quantum.Sponge (HwReg)
open Quantum.Xmss.Hybrid (LazyProg ViewBy ViewByOn lazy_const suppAt_empty KeepsLab
  keepsLab₂_bind keepsLab_revealThen keepsLab_progThen uavg)
open Quantum.Xmss.Assembly (recHwSpec runtimeR realizeT revealThen progThen invSupp Disc
  disc_revealThen disc_progThen disc₂_bind viewBy_runtimeR_of_disc)
open Quantum.Sig (uavg_realizeT_outcome_eq_sampled)
open Quantum.Sphincs.Assembly (RenSim renSim_progThen renSim_substitute
  evalDistMap_sampled_eq_of_renSim)

attribute [local irreducible] Quantum.Qrom.hashQ LeanSphincsOver.messageDigest

/-! ## Lazy sampling -/

section lazy

variable (M : Type) [Fintype M] [DecidableEq M] (upd : TrialUpd M)

omit [Fintype M] [DecidableEq M] in
/-- The data fold reveals before it programs. -/
theorem disc_foldT (pol : DigestPolicy) (B : QReg) (msgs : List Message) (T : Finset TPos) :
    Disc (foldT M pol B msgs) T := by
  induction msgs generalizing T with
  | nil => trivial
  | cons msg ms ih =>
    rw [foldT]
    exact disc_revealThen _ _ T fun r₁ ↦ disc_revealThen _ _ _ fun _ ↦
      disc_progThen _ trivial _ _ (digNeed_subset pol T r₁.2.1 msg)
        (disc₂_bind _ _ (ih _) fun _ _ _ ↦ trivial)

omit [Fintype M] [DecidableEq M] in
/-- The challenge prefix with the data reveals before it programs. -/
theorem disc_prefixIT (pol : DigestPolicy) (A : SAdversary) (T : Finset TPos) :
    Disc (prefixIT M upd pol A) T := by
  unfold prefixIT
  exact disc₂_bind _ _ (disc_prefixT M upd pol A T) fun _ T' _ ↦
    disc₂_bind _ _ (disc_foldT M pol _ _ T') fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- **The ITSR game reveals before it programs.** -/
theorem disc_gameIT (pol : DigestPolicy) (A : SAdversary) (T : Finset TPos) :
    Disc (gameIT M upd pol A) T := by
  rw [gameIT_eq]
  exact disc₂_bind _ _ (disc_prefixIT M upd pol A T) fun _ T' _ ↦ disc_readsThenT M _ _ T'

omit [Fintype M] [DecidableEq M] in
/-- The data fold's reads keep the label. -/
theorem keepsLab_foldT (pol : DigestPolicy) (B : QReg) (msgs : List Message) :
    KeepsLab (foldT M pol B msgs) := by
  induction msgs with
  | nil => trivial
  | cons msg ms ih =>
    rw [foldT]
    exact keepsLab_revealThen _ _ fun _ ↦ keepsLab_revealThen _ _ fun _ ↦
      keepsLab_progThen _ trivial _ (keepsLab₂_bind _ _ ih fun _ ↦ trivial)

omit [Fintype M] [DecidableEq M] in
/-- The challenge prefix with the data keeps the label. -/
theorem keepsLab_prefixIT (pol : DigestPolicy) (A : SAdversary) :
    KeepsLab (prefixIT M upd pol A) := by
  unfold prefixIT
  exact keepsLab₂_bind _ _ (keepsLab_prefixT M upd pol A) fun _ ↦
    keepsLab₂_bind _ _ (keepsLab_foldT M pol _ _) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- **The ITSR game's reads keep the label.** -/
theorem keepsLab_gameIT (pol : DigestPolicy) (A : SAdversary) :
    KeepsLab (gameIT M upd pol A) := by
  rw [gameIT_eq]
  exact keepsLab₂_bind _ _ (keepsLab_prefixIT M upd pol A) fun _ ↦ keepsLab_readsThenT M _ _

/-- **The lazy-sampling property of the ITSR game.** For every initial state that does not depend
on the hidden values, the realized games satisfy `ViewBy` for runtime 2 with record ports and the
memory label, at every call. -/
theorem viewBy_gameIT (pol : DigestPolicy) (A : SAdversary) (m₀ : Finset TPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × M)))
      (QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × M))) ℂ) (j : ℕ) :
    ViewBy (runtimeR m₀) LocalSig.Interp.instruments (fun r ↦ r.2.2.1)
      (fun θ ↦ realizeT θ (gameIT M upd pol A)) (fun _ ↦ ρ) j :=
  viewBy_runtimeR_of_disc _ m₀ (gameIT M upd pol A) ∅ (disc_gameIT M upd pol A ∅) (fun _ ↦ ρ)
    (lazy_const _ ρ) (fun _ ↦ suppAt_empty _ ρ) j

/-- **`ViewByOn` for the ITSR game**: the `hview` hypothesis of the hidden-mass bounds, for
weights vanishing on the program ports. -/
theorem viewByOn_gameIT (pol : DigestPolicy) (A : SAdversary) (m₀ : Finset TPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × M)))
      (QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × M))) ℂ) (j : ℕ) :
    ViewByOn (runtimeR m₀) LocalSig.Interp.instruments (fun i ↦ i.isLeft = true)
      (fun r ↦ r.2.2.1) (fun θ ↦ realizeT θ (gameIT M upd pol A)) (fun _ ↦ ρ) j :=
  (viewBy_gameIT M upd pol A m₀ ρ j).viewByOn _

end lazy

/-! ## The source invariant -/

section hp

variable {M : Type} [Fintype M] [DecidableEq M] (θ : TVals)

omit [Fintype M] [DecidableEq M] in
/-- **The data fold keeps the invariant**, for a digest policy revealing no value coordinate: the
reveal of `R(M)` makes the digest cell pending, which the digest port then programs. -/
theorem hp_foldT {pol : DigestPolicy} (hpol : pol.NoVal) (B : QReg) (msgs : List Message) :
    HP θ (foldT M pol B msgs) ∅ ∅ := by
  induction msgs with
  | nil => exact subset_rfl
  | cons msg ms ih =>
    rw [foldT]
    refine hp_revealThen θ _ _ fun r₁ ↦ hp_revealThen θ _ _ fun r₂ ↦ ?_
    refine hp_progThen θ _ trivial _ (hp_mono θ _ (C := ∅) ?_ ?_ subset_rfl)
    · exact hp₂_bind θ _ _ ih fun _ ↦ subset_rfl
    · rw [realize_digPort, ← cellOf_digPos]
      rintro z ⟨(hz | hz) | hz, hn⟩
      · exact hz
      · exact hn (revealSet_sigReveal θ msg hz)
      · exact revealSet_noVal θ hpol _ msg hz

variable (upd : TrialUpd M)

omit [Fintype M] [DecidableEq M] in
/-- **The challenge prefix with the data keeps the invariant.** -/
theorem hp_prefixIT {pol : DigestPolicy} (hpol : pol.NoVal) (A : SAdversary) :
    HP θ (prefixIT M upd pol A) ∅ ∅ := by
  unfold prefixIT
  refine hp₂_bind θ _ _ (hp_revealThen θ _ _ fun _ ↦ hp_mono θ _
    (hp₂_bind θ _ _ (hp_substitute θ _ (hp_challengeT θ upd hpol) _) fun _ ↦ subset_rfl)
    (Set.union_subset (subset_refl _) (revealSet_pkReveal θ)) subset_rfl) fun _ ↦ ?_
  exact hp₂_bind θ _ _ (hp_foldT θ hpol _ _) fun _ ↦ subset_rfl

omit [Fintype M] [DecidableEq M] in
/-- **The ITSR game keeps the invariant**: the prefix with the data, then the reads. -/
theorem hp_gameIT {pol : DigestPolicy} (hpol : pol.NoVal) (A : SAdversary) :
    HP θ (gameIT M upd pol A) ∅ ∅ := by
  rw [gameIT_eq]
  refine hp₂_bind θ _ _ (hp_prefixIT θ upd hpol A) fun y ↦ ?_
  rw [tailIT, readsThenT_eq]
  exact hp₂_bind θ _ _ (hp_readLift θ _) fun _ ↦ subset_rfl

end hp

section hinv

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M)

/-- **`hinv` for the realized ITSR game**, for every digest policy revealing no value coordinate
(`msgPol`, `strPol`): from states with an empty memory label, every call of ports `Q` other than
the program and record ports sees the invariant `SrcInv`. -/
theorem forallQueries_gameIT {pol : DigestPolicy} (hpol : pol.NoVal)
    {Q : (recHwSpec PairOut Qrom.HashDomain TPos M).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (hQ' : ∀ T, ¬Q (.inr T)) (m₀ : Finset TPos × M)
    (A : SAdversary) (θ : TVals)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × M)))
      (QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × M))) ℂ)
    (hρ : QuerySupportedOn
      (fun a : QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × M)) ↦
        a.2.2.2.1) {∅} ρ) :
    (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m₀) Q (SrcInv M θ)) (realizeT θ (gameIT M upd pol A)) ρ :=
  forallQueries_of_hp hQ hQ' m₀ _ θ _ ∅ ∅ (hp_gameIT θ upd hpol A) ρ
    (hρ.imp fun _ ha ↦ invP_of_label_empty (Set.mem_singleton_iff.1 ha))

end hinv

/-- **Masses' `hinv` for the canonical realized ITSR game** with `Inv θ := SrcInv SelMem θ`. -/
theorem hinvI (pol : DigestPolicy) (hpol : pol.NoVal)
    (Q : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port → Prop)
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (hQ' : ∀ T, ¬Q (.inr T)) (A : SAdversary) (θ : TVals) :
    (runtimeR m0H).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m0H) Q (SrcInv SelMem θ)) (gameIQ pol A θ) initH :=
  forallQueries_gameIT cwUpd hpol hQ hQ' m0H A θ initH (querySupportedOn_init m0H rfl _)

/-! ## The stream reindexing -/

section sim

variable (M : Type) [Fintype M] [DecidableEq M] (upd : TrialUpd M)

/-- The renaming simulation of the stream, at `TPos`. -/
local notation "Sim" => RenSim msgLab (msgStore (Ω := PairOut)) StreamInv

omit [Fintype M] [DecidableEq M] in
/-- **After the digest port**, the rest of the fold and the datum are simulated by themselves, at
equal digests. -/
theorem renSim_foldT_tail {Q : Finset TPos → Prop} (B : QReg) (msg : Message) (R : Randomizer)
    {d d' : MessageDigest} (hd : d = d') {ms : List Message}
    (h : Sim (fun _ ↦ True) (foldT M strPol B ms) (foldT M msgPol B ms)) :
    Sim Q ((foldT M strPol B ms).bind fun ds ↦ QuantumComp₂.pure ((msg, R, d) :: ds))
      ((foldT M msgPol B ms).bind fun ds ↦ QuantumComp₂.pure ((msg, R, d') :: ds)) := by
  subst hd
  exact (h.mono fun _ _ ↦ trivial).bind₂ fun _ ↦ .pure _ _

omit [Fintype M] [DecidableEq M] in
/-- **The data fold at `strPol` is simulated by the data fold at `msgPol`**: per message, the
first part of the signer's simulation (`renSim_signT`). -/
theorem renSim_foldT (B : QReg) (msgs : List Message) :
    Sim (fun _ ↦ True) (foldT M strPol B msgs) (foldT M msgPol B msgs) := by
  induction msgs with
  | nil => exact .pure _ _
  | cons msg ms ih =>
    rw [foldT, foldT]
    have hU := (valOnly_sigReveal msg).asg
    refine renSim_revealThen_val (valOnly_sigReveal msg) ?_
    intro w₁ L m₁ _
    dsimp only
    rcases hs : streamIdx L msg with _ | j
    · refine renSim_revealFall hU hs ?_
      intro w₂ L₂ m₂ _
      dsimp only
      refine renSim_progThen (portSim_digPort_fall hs) trivial trivial ?_
      exact renSim_foldT_tail M B msg _ (digestT_fall hs w₂) ih
    · refine renSim_revealEntry hU hs ?_
      intro w₂ L₂ m₂ _
      dsimp only
      refine renSim_progThen (portSim_digPort_entry hs) trivial trivial ?_
      exact renSim_foldT_tail M B msg _ (digestT_entry hs w₂) ih

omit [Fintype M] [DecidableEq M] in
/-- **The challenge prefix with the data at `strPol` is simulated by that at `msgPol`.** -/
theorem renSim_prefixIT (A : SAdversary) :
    Sim (fun _ ↦ True) (prefixIT M upd strPol A) (prefixIT M upd msgPol A) := by
  unfold prefixIT
  refine RenSim.bind₂ ?_ fun x ↦ (renSim_foldT M _ _).bind₂ fun _ ↦ .pure _ _
  refine renSim_revealThen_val valOnly_pkReveal ?_
  intro _ _ _ _
  exact ((renSim_substitute _ _ _ (renSim_challengeT M upd) _).bind₂ fun _ ↦
    .pure _ _).mono fun _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- **The ITSR game at `strPol` is simulated by the ITSR game at `msgPol`.** -/
theorem renSim_gameIT (A : SAdversary) :
    Sim (fun _ ↦ True) (gameIT M upd strPol A) (gameIT M upd msgPol A) := by
  rw [gameIT_eq, gameIT_eq]
  exact (renSim_prefixIT M upd A).bind₂ fun _ ↦ renSim_readsThenT M _ _

end sim

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M)

/-- **The stream relabelling of the ITSR game**: averaged over uniform hidden values, the
runtime-2 ITSR game started with nothing revealed has the same law at the hybrid side's policy
`msgPol` and at the event side's `strPol`, for every inner memory and trial update. -/
theorem uavg_gameIT_msgPol_eq_strPol (A : SAdversary) (m₀ : M) (ρ : SubState (QReg.of Unit))
    {γ : Type*} [MeasurableSpace γ] (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ)
    {s : Set γ} (hs : MeasurableSet s) :
    uavg (fun θ : TVals ↦ (runtimeR ((∅ : Finset TPos), m₀)).evalDistMap .instruments
        (realizeT θ (gameIT M upd msgPol A)) ρ f s) =
      uavg (fun θ : TVals ↦ (runtimeR ((∅ : Finset TPos), m₀)).evalDistMap .instruments
        (realizeT θ (gameIT M upd strPol A)) ρ f s) := by
  have h := fun pol ↦ uavg_realizeT_outcome_eq_sampled (good := goodQ)
    LocalSig.Interp.instruments m₀ (gameIT M upd pol A) (disc_gameIT M upd pol A ∅)
    (keepsLab_gameIT M upd pol A) ρ f hs
  rw [h msgPol, h strPol]
  exact congrArg (· s) (evalDistMap_sampled_eq_of_renSim LocalSig.Interp.instruments m₀
    (renSim_gameIT M upd A) trivial (streamInv_empty (P := Option Pos) (J := Message)
      (N := signatureLimit) (Ω := PairOut)) msgLab_empty msgStore_empty ρ f).symm

end Quantum.StdModel.Sphincs.SphItsr

end
