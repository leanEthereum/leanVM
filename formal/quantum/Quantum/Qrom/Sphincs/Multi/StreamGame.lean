module

public import Quantum.Qrom.Sphincs.Multi.Template

@[expose] public section

/-!
# The stream relabelling of leanSPHINCS's multi-user runtime-2 game in the QROM

The `n`-user analog of `Quantum.Qrom.Sphincs.StreamGame`: averaged over uniform hidden values,
the multi-user template game (`Quantum.Qrom.Sphincs.Multi.Template`) has the same law at the
hybrid side's digest policies `msgPolN n` (every user's digest cell `(i, .dig M)`) and at the
event side's `strPolN n` (user `i`'s stream entry `(i, .str j)` of `M` in user `i`'s
first-request order, marked; `(i, .dig M)` past user `i`'s stream).

**Route.** By lazy sampling (`Quantum.Sig.uavg_realizeT_outcome_eq_sampled`, with
`disc_muGameT`, `keepsLab_muGameT`) each side is the run of the template game against the sampled
runtime. There `strPolN`'s game is simulated by `msgPolN`'s through the renaming of all users'
streams at once, `msgLabN`, `msgStoreN` (`Quantum.Qrom.Sphincs.Multi.StreamN`), with the
invariant `StreamInvN`.

* Every reveal and program port outside the digest policy is at user `i`'s base coordinates
  (`valOnlyN_atU`), so it is simulated by itself (`renSim_revealThen_valN`, `portSim_selfN`);
  the public keys of all users (`pkRevealN`, read by the `pdOK` mask) likewise.
* User `i`'s digest reveal at `strPol` is simulated by its reveal at `msgPol`
  (`renSim_revealEntryN`, `renSim_revealFallN`); the digest ports hardwire the same cell with the
  same pair (`portSim_digPortN_entry`, `portSim_digPortN_fall`) and the digests agree
  (`digestTN_entry`, `digestTN_fall`), so the memoized selections, the FORS opening and the
  layers are simulated by themselves.
* `renSim_signTN`, `renSim_challengeTN`, `renSim_muGameT`;
  **`uavg_muGameT_msgPolN_eq_strPolN`**.
-/

open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime
open Quantum.Sig (Store fill uavg_realizeT_outcome_eq_sampled)
open Quantum.Sphincs (Key keyOf msgPos)
open Quantum.Xmss.Hybrid (LazyProg restrictTo uavg)
open Quantum.Xmss.Assembly (runtimeR realizeT revealThen progThen readLift readLiftQ RevealVals)
open Quantum.Sphincs.Assembly (RenSim PortSim renSim_progThen renSim_readLift
  renSim_substitute renSim_act_bind evalDistMap_sampled_eq_of_renSim)

attribute [local irreducible] sphincsRom

variable {n : ℕ}

/-! ## Base coordinates of a user -/

/-- The renamed store holds the same pair at a user's base coordinate. -/
theorem pairAt_fill_msgStoreN (L : Finset (TPosN n)) (σ : Store (S := TPosN n) (TValN n))
    (i : Fin n) {s : TPos} (hs : s.IsVal) :
    pairAt (userOf (fill (msgStoreN L σ)) i) s = pairAt (userOf (fill σ) i) s := by
  cases s with
  | val p => exact fill_msgStoreN_of_isVal L σ (a := (i, .val p)) hs
  | _ => exact absurd hs id

/-! ## The renaming simulation of the game -/

section sim

variable (M : Type) [Fintype M] [DecidableEq M] (upd : Fin n → TrialUpd M)

/-- The renaming simulation of all users' streams, at `TPosN n`. -/
local notation "Sim" => RenSim msgLabN (msgStoreN (Ω := PairOut)) StreamInvN

/-- The simulated program ports of all users' streams, at `TPosN n`. -/
local notation "PSim" => PortSim (msgStoreN (Ω := PairOut)) StreamInvN

omit [Fintype M] [DecidableEq M] in
theorem progPosN_nil_bind (i : Fin n) (B : QReg) {C : QReg} {α : Type}
    (k : Unit → QComp (XSpecSN M n) B C α) : (progPosN M i B []).bind k = k () :=
  rfl

omit [Fintype M] [DecidableEq M] in
theorem progPosN_cons_bind (i : Fin n) (B : QReg) {C : QReg} {α : Type} (p : Pos) (ps : List Pos)
    (k : Unit → QComp (XSpecSN M n) B C α) :
    (progPosN M i B (p :: ps)).bind k =
      progThen (progTN i p) trivial ((progPosN M i B ps).bind k) :=
  rfl

omit [Fintype M] [DecidableEq M] in
/-- **User `i`'s program ports of structural positions are simulated by themselves.** -/
theorem renSim_progPosN_bind {Q : Finset (TPosN n) → Prop} (i : Fin n) {B C : QReg} {α : Type}
    (ps : List Pos) (hps : ∀ p ∈ ps, p.1.IsStruct) {k k' : Unit → QComp (XSpecSN M n) B C α}
    (hk : Sim Q (k ()) (k' ())) :
    Sim Q ((progPosN M i B ps).bind k) ((progPosN M i B ps).bind k') := by
  induction ps with
  | nil =>
    rw [progPosN_nil_bind, progPosN_nil_bind]
    exact hk
  | cons p ps ih =>
    rw [progPosN_cons_bind, progPosN_cons_bind]
    exact renSim_progThen
      (portSim_selfN (p := progTN i p)
        (valOnlyN_atU i (valOnly_progNeed (hps p List.mem_cons_self)))) trivial
      trivial (ih fun q hq ↦ hps q (List.mem_cons_of_mem _ hq))

omit [Fintype M] [DecidableEq M] in
/-- **User `i`'s FORS opening** is simulated by itself. -/
theorem renSim_forsOpenTN {Q : Finset (TPosN n) → Prop} (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) :
    Sim Q (forsOpenTN M i B idx lv) (forsOpenTN M i B idx lv) := by
  refine renSim_revealThen_valN (valOnlyN_atU i (valOnly_forsReveal idx lv)) ?_
  intro _ _ _ _
  exact renSim_progPosN_bind M i _ (fun _ hp ↦ isStruct_of_mem_forsPos hp) (.pure _ _)

omit [Fintype M] [DecidableEq M] in
/-- **User `i`'s counter search** is simulated by itself. -/
theorem renSim_selectTN {Q : Finset (TPosN n) → Prop} (i : Fin n) (seed : PublicParameter)
    (B : QReg) (K : Key) : Sim Q (selectTN M upd i seed B K) (selectTN M upd i seed B K) := by
  refine renSim_revealThen_valN (valOnlyN_atU i (valOnly_singleton (isVal_vcoord _))) ?_
  intro _ _ _ _
  exact renSim_readLift _ _ _ _ _

omit [Fintype M] [DecidableEq M] in
/-- **User `i`'s memoized selection or counter search** is simulated by itself. -/
theorem renSim_selOrMemoTN {Q : Finset (TPosN n) → Prop} (i : Fin n) (seed : PublicParameter)
    (B : QReg) (K : Key) (o : Option SelS) :
    Sim Q (selOrMemoTN M upd i seed B K o) (selOrMemoTN M upd i seed B K o) := by
  rcases o with _ | o
  · exact renSim_selectTN M upd i seed B K
  · exact .pure _ _

omit [Fintype M] [DecidableEq M] in
/-- **User `i`'s layer publication** is simulated by itself. -/
theorem renSim_publishTN {Q : Finset (TPosN n) → Prop} (i : Fin n) (B : QReg) (K : Key)
    (c : EncodingCounter) (x : Encoding) :
    Sim Q (publishTN M i B K c x) (publishTN M i B K c x) := by
  refine renSim_revealThen_valN (valOnlyN_atU i (valOnly_layerReveal K x)) ?_
  intro _ _ _ _
  exact renSim_progPosN_bind M i _ (fun _ hp ↦ isStruct_of_mem_layerPos hp) (.pure _ _)

omit [Fintype M] [DecidableEq M] in
/-- **The publication of user `i`'s signature** is simulated by itself. -/
theorem renSim_publishAllTN {Q : Finset (TPosN n) → Prop} (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (R : Randomizer) (g₀ g₁ g₂ : SelS) :
    Sim Q (publishAllTN M i B idx lv R g₀ g₁ g₂) (publishAllTN M i B idx lv R g₀ g₁ g₂) := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try exact .pure _ _
  exact (renSim_forsOpenTN M i B _ _).bind₂ fun _ ↦ (renSim_publishTN M i B _ _ _).bind₂ fun _ ↦
    (renSim_publishTN M i B _ _ _).bind₂ fun _ ↦ (renSim_publishTN M i B _ _ _).bind₂ fun _ ↦
      .pure _ _

/-- **User `i`'s digest ports are simulated** when the renamed store holds the event side's
digest pair at the hybrid side's coordinate (the cell's inputs are base coordinates). -/
theorem portSim_digPortN {Q : Finset (TPosN n) → Prop} {pol pol' : DigestPolicy} {i : Fin n}
    {L L' : Finset (TPosN n)} {msg : Message}
    (hout : ∀ (L₁ : Finset (TPosN n)) (σ : Store (S := TPosN n) (TValN n)), Q L₁ →
      StreamInvN L₁ σ →
      pairAt (userOf (fill (msgStoreN L₁ σ)) i) (pol'.out (labU L' i) msg) =
        pairAt (userOf (fill σ) i) (pol.out (labU L i) msg)) :
    PSim Q (digPortN pol i L msg) (digPortN pol' i L' msg) :=
  .progH _ _ _ _ fun L₁ σ hL hG ↦ by
    have hs : (tabOf (userOf (fill σ) i)).publicSeed =
        (tabOf (userOf (fill (msgStoreN L₁ σ)) i)).publicSeed :=
      publicSeed_tabOf_congr (pairAt_fill_msgStoreN L₁ σ i isVal_seedC).symm
    have hr : (tabOf (userOf (fill σ) i)).root =
        (tabOf (userOf (fill (msgStoreN L₁ σ)) i)).root :=
      root_tabOf_congr (pairAt_fill_msgStoreN L₁ σ i isVal_rootC).symm
    have hR : (tabOf (userOf (fill σ) i)).randomizer msg =
        (tabOf (userOf (fill (msgStoreN L₁ σ)) i)).randomizer msg :=
      randomizer_tabOf_congr (pairAt_fill_msgStoreN L₁ σ i (isVal_rndC msg)).symm
    have e := (realize_digPortN pol i L msg (fill σ)).trans
      ((congrArg₂ Quantum.Sponge.HwProg.programH (by rw [hs, hr, hR])
        (hout L₁ σ hL hG).symm).trans
        (realize_digPortN pol' i L' msg (fill (msgStoreN L₁ σ))).symm)
    obtain ⟨h₁, h₂⟩ := Quantum.Sponge.HwProg.programH.inj e
    exact Prod.ext h₁ h₂

/-- **User `i`'s digest port at a stream entry**: after the reveal of user `i`'s entry `j`
(marked for `M`), the event side's digest port is simulated by the hybrid side's. -/
theorem portSim_digPortN_entry {i : Fin n} {L L₂ : Finset (TPosN n)} {msg : Message}
    {j : Fin signatureLimit} (hs : streamIdx (labU L i) msg = some j) :
    PSim (fun L' ↦ L' = L₂ ∪ atU i (strNeed (labU L i) msg)) (digPortN strPol i L msg)
      (digPortN msgPol i (msgLabN L) msg) :=
  portSim_digPortN fun L₁ σ hL hG ↦ by
    subst hL
    show fill (msgStoreN (Ω := PairOut) _ σ) (i, .dig msg) =
      pairAt (userOf (fill σ) i) (strOut (labU L i) msg)
    rw [fill_msgStoreN_dig_entry hs Finset.subset_union_right hG, strOut_some hs]
    rfl

/-- **User `i`'s digest port past the stream**: both sides hardwire user `i`'s digest cell of
`M`. -/
theorem portSim_digPortN_fall {i : Fin n} {L L₂ : Finset (TPosN n)} {msg : Message}
    (hs : streamIdx (labU L i) msg = none) :
    PSim (fun L' ↦ L' = L₂ ∪ atU i (strNeed (labU L i) msg)) (digPortN strPol i L msg)
      (digPortN msgPol i (msgLabN L) msg) :=
  portSim_digPortN fun L₁ σ hL hG ↦ by
    subst hL
    show fill (msgStoreN (Ω := PairOut) _ σ) (i, .dig msg) =
      pairAt (userOf (fill σ) i) (strOut (labU L i) msg)
    rw [fill_msgStoreN_dig_fall hG
      (Finset.mem_union_right _ (mk_mem_atU i ((mem_strNeed_none hs _).2 rfl))), strOut_none hs]
    rfl

/-- **User `i`'s digest at a stream entry**: the event side's revealed entry is the hybrid
side's revealed digest. -/
theorem digestTN_entry {i : Fin n} {L : Finset (TPosN n)} {msg : Message}
    {j : Fin signatureLimit} (hs : streamIdx (labU L i) msg = some j)
    (w : RevealVals (TValN n) (atU i (strNeed (labU L i) msg))) :
    digestTN strPol i L msg w = digestTN msgPol i (msgLabN L) msg (entryEquivN i hs w) := by
  have hT : (i, SPos.str j) ∈ atU i (strNeed (labU L i) msg) :=
    mk_mem_atU i (str_mem_of_entry (mem_strNeed_some hs))
  have hT' : (i, SPos.dig msg) ∈ atU i (msgNeed (P := Option Pos) (N := signatureLimit) msg) :=
    mk_mem_atU i ((mem_msgNeed msg _).2 rfl)
  unfold digestTN pairRN
  show digestOfPair (pairAt (SValsN.user (extWN w) i) (strOut (labU L i) msg)) =
    digestOfPair (extWN (entryEquivN i hs w) (i, .dig msg))
  rw [strOut_some hs]
  show digestOfPair (extWN w (i, .str j)) = _
  rw [extWN_of_mem _ hT, extWN_of_mem _ hT', entryEquivN_dig]

/-- **User `i`'s digest past the stream**: both sides reveal the same digest. -/
theorem digestTN_fall {i : Fin n} {L : Finset (TPosN n)} {msg : Message}
    (hs : streamIdx (labU L i) msg = none)
    (w : RevealVals (TValN n) (atU i (strNeed (labU L i) msg))) :
    digestTN strPol i L msg w = digestTN msgPol i (msgLabN L) msg (fallEquivN i hs w) := by
  have hT : (i, SPos.dig msg) ∈ atU i (strNeed (labU L i) msg) :=
    mk_mem_atU i ((mem_strNeed_none hs _).2 rfl)
  have hT' : (i, SPos.dig msg) ∈ atU i (msgNeed (P := Option Pos) (N := signatureLimit) msg) :=
    mk_mem_atU i ((mem_msgNeed msg _).2 rfl)
  unfold digestTN pairRN
  show digestOfPair (pairAt (SValsN.user (extWN w) i) (strOut (labU L i) msg)) =
    digestOfPair (extWN (fallEquivN i hs w) (i, .dig msg))
  rw [strOut_none hs]
  show digestOfPair (extWN w (i, .dig msg)) = _
  rw [extWN_of_mem _ hT, extWN_of_mem _ hT', fallEquivN_dig]

omit [Fintype M] [DecidableEq M] in
/-- **After the digest port**, user `i`'s memoized selections or counter searches and the
publication are simulated by themselves, at equal digests. -/
theorem renSim_signTailN {Q : Finset (TPosN n) → Prop} (i : Fin n) (seed : PublicParameter)
    (B : QReg) (R : Randomizer) (h : KeyMemo) {d d' : MessageDigest} (hd : d = d') :
    Sim Q ((selOrMemoTN M upd i seed B (keyOf 0 (digestIndex d))
          (h (keyOf 0 (digestIndex d)))).bind fun g₀ ↦
        (selOrMemoTN M upd i seed B (keyOf 1 (digestIndex d))
          (h (keyOf 1 (digestIndex d)))).bind fun g₁ ↦
        (selOrMemoTN M upd i seed B (keyOf 2 (digestIndex d))
          (h (keyOf 2 (digestIndex d)))).bind fun g₂ ↦
        (publishAllTN M i B (digestIndex d) (digestForsLeaves d) R g₀ g₁ g₂).map fun s ↦
          (s, (digestIndex d, layerSels g₀ g₁ g₂)))
      ((selOrMemoTN M upd i seed B (keyOf 0 (digestIndex d'))
          (h (keyOf 0 (digestIndex d')))).bind fun g₀ ↦
        (selOrMemoTN M upd i seed B (keyOf 1 (digestIndex d'))
          (h (keyOf 1 (digestIndex d')))).bind fun g₁ ↦
        (selOrMemoTN M upd i seed B (keyOf 2 (digestIndex d'))
          (h (keyOf 2 (digestIndex d')))).bind fun g₂ ↦
        (publishAllTN M i B (digestIndex d') (digestForsLeaves d') R g₀ g₁ g₂).map fun s ↦
          (s, (digestIndex d', layerSels g₀ g₁ g₂))) := by
  subst hd
  refine (renSim_selOrMemoTN M upd i seed B _ _).bind₂ fun _ ↦
    (renSim_selOrMemoTN M upd i seed B _ _).bind₂ fun _ ↦
      (renSim_selOrMemoTN M upd i seed B _ _).bind₂ fun _ ↦ ?_
  rw [QuantumComp₂.map_eq_bind_pure]
  exact (renSim_publishAllTN M i B _ _ R _ _ _).bind₂ fun _ ↦ .pure _ _

omit [Fintype M] [DecidableEq M] in
/-- **User `i`'s signer at `strPol` is simulated by its signer at `msgPol`.** -/
theorem renSim_signTN (i : Fin n) (B : QReg) (msg : Message) (h : KeyMemo) :
    Sim (fun _ ↦ True) (signTN M upd (strPolN n) i B msg h)
      (signTN M upd (msgPolN n) i B msg h) := by
  have hU := (valOnlyN_atU i (valOnly_sigReveal msg)).asg i
  refine renSim_revealThen_valN (valOnlyN_atU i (valOnly_sigReveal msg)) ?_
  intro w₁ L m₁ _
  dsimp only
  rcases hs : streamIdx (labU L i) msg with _ | j
  · refine renSim_revealFallN i hU hs ?_
    intro w₂ L₂ m₂ _
    dsimp only
    refine renSim_progThen (portSim_digPortN_fall hs) trivial trivial ?_
    exact renSim_signTailN M upd i _ B _ h (digestTN_fall hs w₂)
  · refine renSim_revealEntryN i hU hs ?_
    intro w₂ L₂ m₂ _
    dsimp only
    refine renSim_progThen (portSim_digPortN_entry hs) trivial trivial ?_
    exact renSim_signTailN M upd i _ B _ h (digestTN_entry hs w₂)

omit [Fintype M] [DecidableEq M] in
/-- **The multi-user challenger at `strPolN` is simulated by the challenger at `msgPolN`.** -/
theorem renSim_challengeTN (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (memoSpecS n) A) :
    Sim (fun _ ↦ True) (challengeTN M upd (strPolN n) A c) (challengeTN M upd (msgPolN n) A c) := by
  rcases c with o | ⟨_ | ⟨i, q⟩, E, ℓ⟩
  · exact renSim_readLift _ _ _ _ _
  · exact renSim_readLift _ _ _ _ _
  · exact (renSim_act_bind _ fun _ ↦ renSim_signTN M upd i _ q.1 q.2).bind fun _ _ ↦ .pure _ _

omit [Fintype M] [DecidableEq M] in
/-- A read program followed by a pure step is simulated by itself. -/
theorem renSim_readsThenTN {Q : Finset (TPosN n) → Prop} {α β : Type}
    (oa : OracleComp RomOracles α) (f : α → β) :
    Sim Q (readsThenTN (n := n) M oa f) (readsThenTN M oa f) := by
  rw [readsThenTN_eq]
  exact (renSim_readLift _ _ _ _ _).bind₂ fun _ ↦ .pure _ _

omit [Fintype M] [DecidableEq M] in
/-- **The multi-user game at `strPolN` is simulated by the game at `msgPolN`**: the renaming of
every user's stream entries of its marked messages to its digest cells. -/
theorem renSim_muGameT (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (A : MuAdversaryS n) :
    Sim (fun _ ↦ True) (muGameT M upd (strPolN n) valid A) (muGameT M upd (msgPolN n) valid A) := by
  refine renSim_revealThen_valN (valOnlyN_prod Finset.univ valOnly_pkReveal) ?_
  intro _ _ _ _
  exact ((renSim_substitute _ _ _ (renSim_challengeTN M upd) _).bind₂ fun _ ↦
    renSim_readsThenTN M _ _).mono fun _ _ ↦ trivial

end sim

/-! ## The averaged laws of the two policies -/

variable {M : Type} [Fintype M] [DecidableEq M]

/-- **The multi-user stream relabelling**: averaged over uniform hidden values, the multi-user
runtime-2 game started with nothing revealed has the same law at the hybrid side's policies
`msgPolN n` and at the event side's `strPolN n`, for every inner memory and trial update. -/
theorem uavg_muGameT_msgPolN_eq_strPolN (upd : Fin n → TrialUpd M)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n) (m₀ : M)
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) {s : Set γ}
    (hs : MeasurableSet s) :
    uavg (fun θ : TValsN n ↦ (runtimeR ((∅ : Finset (TPosN n)), m₀)).evalDistMap .instruments
        (realizeT θ (muGameT M upd (msgPolN n) valid A)) ρ f s) =
      uavg (fun θ : TValsN n ↦ (runtimeR ((∅ : Finset (TPosN n)), m₀)).evalDistMap .instruments
        (realizeT θ (muGameT M upd (strPolN n) valid A)) ρ f s) := by
  have h := fun pol ↦ uavg_realizeT_outcome_eq_sampled (good := goodQN)
    LocalSig.Interp.instruments m₀ (muGameT M upd pol valid A) (disc_muGameT M upd pol valid A ∅)
    (keepsLab_muGameT M upd pol valid A) ρ f hs
  rw [h (msgPolN n), h (strPolN n)]
  exact congrArg (· s) (evalDistMap_sampled_eq_of_renSim LocalSig.Interp.instruments m₀
    (renSim_muGameT M upd valid A) trivial
    (streamInvN_empty (P := Option Pos) (J := Message) (N := signatureLimit) (Ω := PairOut))
    msgLabN_empty msgStoreN_empty ρ f).symm

end Quantum.Qrom.Sphincs.Multi

end
