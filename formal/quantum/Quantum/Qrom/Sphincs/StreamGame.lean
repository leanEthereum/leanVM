module

public import Quantum.Qrom.Sphincs.Template

@[expose] public section

/-!
# The stream relabelling of leanSPHINCS's runtime-2 game in the QROM

The game-level reindexing of `Quantum.Qrom.Sphincs.Stream` (the QROM counterpart of the QRPM's
`Quantum.Sphincs.Assembly.uavg_p2R_msgPol_eq_strPol`): averaged over uniform hidden values, the
runtime-2 template game (`Quantum.Qrom.Sphincs.Template`) has the same law at the hybrid side's
digest policy `msgPol` (the digest cell `.dig M` of each signed message) and at the event side's
`strPol` (the stream entry of `M` in first-request order, marked; `.dig M` past the stream).

**Route.** By lazy sampling (`Quantum.Sig.uavg_realizeT_outcome_eq_sampled`, with `disc_gameT`,
`keepsLab_gameT`) each side is the run of the template game against the sampled runtime. There
`strPol`'s game is simulated by `msgPol`'s through the renaming `msgLab`, `msgStore` of the
sampled register with the invariant `StreamInv` (`Quantum.Sphincs.Assembly.RenSim`; the generic
run theorem `evalDistMap_sampled_eq_of_renSim`).

* Every reveal and program port outside the digest policy is at base coordinates (`.val`,
  `ValOnly`: `valOnly_progNeed`, `valOnly_layerReveal`, `valOnly_forsReveal`, ...), so it is
  simulated by itself (`renSim_revealThen_val`, `portSim_self`).
* The digest reveal of `strPol` is simulated by `msgPol`'s (`renSim_revealEntry`,
  `renSim_revealFall`); the digest ports then hardwire the same cell with the same pair
  (`portSim_digPort_entry`, `portSim_digPort_fall`), and the digests agree
  (`digestT_entry`, `digestT_fall`), so the FORS opening and the layers are simulated by
  themselves.
* `renSim_signT`, `renSim_challengeT`, `renSim_gameT`; **`uavg_gameT_msgPol_eq_strPol`**.
-/

open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime
open Quantum.Sig (Store fill uavg_realizeT_outcome_eq_sampled)
open Quantum.Sphincs (Key keyOf)
open Quantum.Xmss.Hybrid (LazyProg restrictTo uavg)
open Quantum.Xmss.Assembly (runtimeR realizeT revealThen progThen readLift readLiftQ RevealVals)
open Quantum.Sphincs.Assembly (RenSim PortSim renSim_revealThen renSim_progThen renSim_readLift
  renSim_substitute renSim_act_bind evalDistMap_sampled_eq_of_renSim)

/-! ## Base coordinates -/

section base

theorem isVal_seedC : (seedC : TPos).IsVal :=
  trivial

/-- A hash call's coordinate is a base coordinate unless it is a digest cell's. -/
theorem isVal_rawC {q : RawPos} (hq : ∀ m, q ≠ .hmsg m) : (rawC q).IsVal := by
  unfold rawC
  split_ifs with h
  · cases q with
    | hmsg m => exact absurd rfl (hq m)
    | _ => trivial
  · trivial

theorem isVal_chainC (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) (j : ℕ) :
    (chainC l τ e i j).IsVal := by
  cases j with
  | zero => exact isVal_rawC fun _ h ↦ by cases h
  | succ j =>
    show (if h : j < chainLength - 1 then rawC (.chain l τ e i ⟨j, h⟩) else seedC).IsVal
    split_ifs
    · exact isVal_rawC fun _ h ↦ by cases h
    · trivial

theorem isVal_treeC (l : Layer) (τ : TreeIndex) (level index : ℕ) :
    (treeC l τ level index).IsVal := by
  cases level with
  | zero => exact isVal_rawC fun _ h ↦ by cases h
  | succ level =>
    show (if h : level < layerHeight topLayer ∧ index < 2 ^ layerHeight topLayer then
      rawC (.node l τ ⟨level, h.1⟩ ⟨index, h.2⟩) else seedC).IsVal
    split_ifs
    · exact isVal_rawC fun _ h ↦ by cases h
    · trivial

theorem isVal_forsC (idx : Index) (κ : ForsTreeIndex) (height j : ℕ) :
    (forsC idx κ height j).IsVal := by
  cases height with
  | zero => exact isVal_rawC fun _ h ↦ by cases h
  | succ height =>
    show (if hh : height < forsTreeHeight ∧ j < 2 ^ forsTreeHeight then
      rawC (.forsNode idx κ ⟨height, hh.1⟩ ⟨j, hh.2⟩) else seedC).IsVal
    split_ifs
    · exact isVal_rawC fun _ h ↦ by cases h
    · trivial

theorem isVal_vcoord (q : Quantum.Sphincs.ValPos) : (vcoord q).IsVal := by
  cases q with
  | chain l τ e i j => exact isVal_chainC l τ e i j.val
  | tree l τ level index => exact isVal_treeC l τ level.val index.val
  | forsSecret idx κ s => exact isVal_rawC fun _ h ↦ by cases h
  | forsTree idx κ height node => exact isVal_forsC idx κ height.val node.val
  | forsKey idx => exact isVal_rawC fun _ h ↦ by cases h

theorem isVal_rootC : (rootC : TPos).IsVal :=
  isVal_treeC _ _ _ _

theorem isVal_rndC (msg : Message) : (rndC msg).IsVal :=
  isVal_rawC fun _ h ↦ by cases h

theorem isVal_coordOf {p : Pos} (hp : p.1.IsStruct) : (coordOf p).IsVal := by
  obtain ⟨q, hq⟩ := p
  cases q with
  | hmsg m => exact absurd hp id
  | _ => trivial

theorem valOnly_insert {a : TPos} {T : Finset TPos} (ha : a.IsVal) (hT : ValOnly T) :
    ValOnly (insert a T) := fun s hs ↦
  (Finset.mem_insert.1 hs).elim (fun h ↦ h ▸ ha) (hT s)

theorem valOnly_singleton {a : TPos} (ha : a.IsVal) : ValOnly ({a} : Finset TPos) := fun _ hs ↦
  (Finset.mem_singleton.1 hs) ▸ ha

theorem valOnly_union {T T' : Finset TPos} (hT : ValOnly T) (hT' : ValOnly T') :
    ValOnly (T ∪ T') := fun s hs ↦ (Finset.mem_union.1 hs).elim (hT s) (hT' s)

theorem valOnly_image {ι : Type} [Fintype ι] {f : ι → TPos} (hf : ∀ i, (f i).IsVal) :
    ValOnly (Finset.univ.image f) := fun s hs ↦ by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
  exact hf i

theorem valOnly_cellNeed : ∀ q : RawPos, ValOnly (cellNeed q)
  | .chain l τ e i step =>
    valOnly_insert isVal_seedC (valOnly_singleton (isVal_chainC l τ e i step.val))
  | .leaf l τ e =>
    valOnly_insert isVal_seedC (valOnly_image fun i ↦ isVal_chainC l τ e i _)
  | .node l τ level index =>
    valOnly_insert isVal_seedC (valOnly_insert (isVal_treeC l τ _ _)
      (valOnly_singleton (isVal_treeC l τ _ _)))
  | .forsLeaf idx κ s =>
    valOnly_insert isVal_seedC (valOnly_singleton (isVal_rawC fun _ h ↦ by cases h))
  | .forsNode idx κ level node =>
    valOnly_insert isVal_seedC (valOnly_insert (isVal_forsC idx κ _ _)
      (valOnly_singleton (isVal_forsC idx κ _ _)))
  | .forsRoots idx =>
    valOnly_insert isVal_seedC (valOnly_image fun κ ↦ isVal_forsC idx κ _ _)
  | .prfKey => valOnly_singleton isVal_seedC
  | .publicSeed => valOnly_singleton isVal_seedC
  | .chainStart .. => valOnly_singleton isVal_seedC
  | .forsSecret .. => valOnly_singleton isVal_seedC
  | .prfMsg _ => valOnly_singleton isVal_seedC
  | .hmsg _ => valOnly_singleton isVal_seedC

theorem valOnly_progNeed {p : Pos} (hp : p.1.IsStruct) : ValOnly (progNeed p) :=
  valOnly_insert (isVal_coordOf hp) (valOnly_cellNeed p.1)

theorem valOnly_needUnion {ps : List Pos} (hps : ∀ p ∈ ps, p.1.IsStruct) :
    ValOnly (needUnion ps) := by
  induction ps with
  | nil => exact fun _ h ↦ absurd h (Finset.notMem_empty _)
  | cons p ps ih =>
    exact valOnly_union (valOnly_progNeed (hps p List.mem_cons_self))
      (ih fun q hq ↦ hps q (List.mem_cons_of_mem _ hq))

theorem valOnly_layerReveal (K : Key) (x : Encoding) : ValOnly (layerReveal K x) :=
  valOnly_union (valOnly_union (valOnly_needUnion fun _ hp ↦ isStruct_of_mem_layerPos hp)
    (valOnly_image fun _ ↦ isVal_chainC _ _ _ _ _)) (valOnly_image fun _ ↦ isVal_treeC _ _ _ _)

theorem valOnly_forsReveal (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    ValOnly (forsReveal idx lv) :=
  valOnly_union (valOnly_union (valOnly_needUnion fun _ hp ↦ isStruct_of_mem_forsPos hp)
    (valOnly_image fun _ ↦ isVal_rawC fun _ h ↦ by cases h))
    (valOnly_image fun _ ↦ isVal_forsC _ _ _ _)

theorem valOnly_pkReveal : ValOnly pkReveal :=
  valOnly_insert isVal_seedC (valOnly_singleton isVal_rootC)

theorem valOnly_sigReveal (msg : Message) : ValOnly ({seedC, rootC, rndC msg} : Finset TPos) :=
  valOnly_insert isVal_seedC (valOnly_insert isVal_rootC (valOnly_singleton (isVal_rndC msg)))

/-- The renamed store holds the same pair at a base coordinate. -/
theorem pairAt_fill_msgStore {L : Finset TPos} (σ : Store (S := TPos) TVal) {s : TPos}
    (hs : s.IsVal) : pairAt (fill (msgStore L σ)) s = pairAt (fill σ) s := by
  cases s with
  | val p =>
    show fill (msgStore L σ) (.val p) = fill σ (.val p)
    unfold fill
    rw [msgStore_of_isVal L σ hs]
  | _ => exact absurd hs id

end base

/-! ## The renaming simulation of the game -/

section sim

variable (M : Type) [Fintype M] [DecidableEq M] (upd : TrialUpd M)

/-- The renaming simulation of the stream, at `TPos`. -/
local notation "Sim" => RenSim msgLab (msgStore (Ω := PairOut)) StreamInv

/-- The simulated program ports of the stream, at `TPos`. -/
local notation "PSim" => PortSim (msgStore (Ω := PairOut)) StreamInv

omit [Fintype M] [DecidableEq M] in
theorem progPos_nil_bind (B : QReg) {C : QReg} {α : Type} (k : Unit → QComp (SSpecQ M) B C α) :
    (progPos M B []).bind k = k () :=
  rfl

omit [Fintype M] [DecidableEq M] in
theorem progPos_cons_bind (B : QReg) {C : QReg} {α : Type} (p : Pos) (ps : List Pos)
    (k : Unit → QComp (SSpecQ M) B C α) :
    (progPos M B (p :: ps)).bind k = progThen (progT p) trivial ((progPos M B ps).bind k) :=
  rfl

omit [Fintype M] [DecidableEq M] in
/-- **Program ports of structural positions are simulated by themselves.** -/
theorem renSim_progPos_bind {Q : Finset TPos → Prop} {B C : QReg} {α : Type} (ps : List Pos)
    (hps : ∀ p ∈ ps, p.1.IsStruct) {k k' : Unit → QComp (SSpecQ M) B C α}
    (hk : Sim Q (k ()) (k' ())) :
    Sim Q ((progPos M B ps).bind k) ((progPos M B ps).bind k') := by
  induction ps with
  | nil =>
    rw [progPos_nil_bind, progPos_nil_bind]
    exact hk
  | cons p ps ih =>
    rw [progPos_cons_bind, progPos_cons_bind]
    exact renSim_progThen
      (portSim_self (p := progT p) (valOnly_progNeed (hps p List.mem_cons_self))) trivial
      trivial (ih fun q hq ↦ hps q (List.mem_cons_of_mem _ hq))

omit [Fintype M] [DecidableEq M] in
/-- **The FORS opening** is simulated by itself. -/
theorem renSim_forsOpenT {Q : Finset TPos → Prop} (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) :
    Sim Q (forsOpenT M B idx lv) (forsOpenT M B idx lv) := by
  refine renSim_revealThen_val (valOnly_forsReveal idx lv) ?_
  intro _ _ _ _
  exact renSim_progPos_bind M _ (fun _ hp ↦ isStruct_of_mem_forsPos hp) (.pure _ _)

omit [Fintype M] [DecidableEq M] in
/-- **A counter search** is simulated by itself, at equal keys. -/
theorem renSim_selectT {Q : Finset TPos → Prop} (seed : PublicParameter) (B : QReg)
    {K K' : Key} (hK : K = K') : Sim Q (selectT M upd seed B K) (selectT M upd seed B K') := by
  subst hK
  refine renSim_revealThen_val (valOnly_singleton (isVal_vcoord _)) ?_
  intro _ _ _ _
  exact renSim_readLift _ _ _ _ _

omit [Fintype M] [DecidableEq M] in
/-- **A layer publication** is simulated by itself. -/
theorem renSim_publishT {Q : Finset TPos → Prop} (B : QReg) (K : Key) (c : EncodingCounter)
    (x : Encoding) : Sim Q (publishT M B K c x) (publishT M B K c x) := by
  refine renSim_revealThen_val (valOnly_layerReveal K x) ?_
  intro _ _ _ _
  exact renSim_progPos_bind M _ (fun _ hp ↦ isStruct_of_mem_layerPos hp) (.pure _ _)

omit [Fintype M] [DecidableEq M] in
/-- **The publication of a signature** is simulated by itself, at equal indices and leaves. -/
theorem renSim_publishAllT {Q : Finset TPos → Prop} (B : QReg) {idx idx' : Index}
    {lv lv' : ForsTreeIndex → ForsLeafIndex} (hidx : idx = idx') (hlv : lv = lv') (R : Randomizer)
    (g₀ g₁ g₂ : Option (EncodingCounter × Encoding)) :
    Sim Q (publishAllT M B idx lv R g₀ g₁ g₂) (publishAllT M B idx' lv' R g₀ g₁ g₂) := by
  subst hidx hlv
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try exact .pure _ _
  exact (renSim_forsOpenT M B _ _).bind₂ fun _ ↦ (renSim_publishT M B _ _ _).bind₂ fun _ ↦
    (renSim_publishT M B _ _ _).bind₂ fun _ ↦ (renSim_publishT M B _ _ _).bind₂ fun _ ↦
      .pure _ _

/-- **The digest ports agree at the store and the renamed store** when the renamed store holds
the event side's digest pair at `.dig M`. -/
theorem digFun_fill_msgStore {L L₁ : Finset TPos} {msg : Message} {σ : Store (S := TPos) TVal}
    (hout : pairAt (fill (msgStore L₁ σ)) (.dig msg) = pairAt (fill σ) (strOut L msg)) :
    digFun strPol L msg (restrictTo (digNeed strPol L msg) (fill σ)) =
      digFun msgPol (msgLab L) msg
        (restrictTo (digNeed msgPol (msgLab L) msg) (fill (msgStore L₁ σ))) := by
  rw [digFun_restrictTo _ _ _ subset_rfl, digFun_restrictTo _ _ _ subset_rfl]
  have hs : (tabOf (fill σ)).publicSeed = (tabOf (fill (msgStore L₁ σ))).publicSeed :=
    publicSeed_tabOf_congr (pairAt_fill_msgStore σ isVal_seedC).symm
  have hr : (tabOf (fill σ)).root = (tabOf (fill (msgStore L₁ σ))).root :=
    root_tabOf_congr (pairAt_fill_msgStore σ isVal_rootC).symm
  have hR : (tabOf (fill σ)).randomizer msg = (tabOf (fill (msgStore L₁ σ))).randomizer msg :=
    randomizer_tabOf_congr (pairAt_fill_msgStore σ (isVal_rndC msg)).symm
  rw [hs, hr, hR]
  exact congrArg (Prod.mk _) hout.symm

/-- **The digest port at a stream entry**: after the reveal of entry `j` (marked for `M`), the
event side's digest port is simulated by the hybrid side's. -/
theorem portSim_digPort_entry {L L₂ : Finset TPos} {msg : Message} {j : Fin signatureLimit}
    (hs : streamIdx L msg = some j) :
    PSim (fun L' ↦ L' = L₂ ∪ strNeed L msg) (digPort strPol L msg)
      (digPort msgPol (msgLab L) msg) :=
  .progH _ _ _ _ fun L₁ σ hL hG ↦ digFun_fill_msgStore (by
    subst hL
    show fill (msgStore _ σ) (.dig msg) = pairAt (fill σ) (strOut L msg)
    rw [fill_msgStore_dig_entry hs Finset.subset_union_right hG, strOut_some hs]
    rfl)

/-- **The digest port past the stream**: both sides hardwire the digest cell of `M`. -/
theorem portSim_digPort_fall {L L₂ : Finset TPos} {msg : Message}
    (hs : streamIdx L msg = none) :
    PSim (fun L' ↦ L' = L₂ ∪ strNeed L msg) (digPort strPol L msg)
      (digPort msgPol (msgLab L) msg) :=
  .progH _ _ _ _ fun L₁ σ hL hG ↦ digFun_fill_msgStore (by
    subst hL
    show fill (msgStore _ σ) (.dig msg) = pairAt (fill σ) (strOut L msg)
    rw [fill_msgStore_dig_fall hG (Finset.subset_union_right ((mem_strNeed_none hs _).2 rfl)),
      strOut_none hs]
    rfl)

/-- **The digest at a stream entry**: the event side's revealed entry is the hybrid side's
revealed digest. -/
theorem digestT_entry {L : Finset TPos} {msg : Message} {j : Fin signatureLimit}
    (hs : streamIdx L msg = some j) (w : RevealVals TVal (strNeed L msg)) :
    digestT strPol L msg w =
      digestT msgPol (msgLab L) msg
        (entryEquiv (mem_strNeed_some hs) (mem_msgNeed (P := Option Pos) (N := signatureLimit)
          msg) w) := by
  have hT := mem_strNeed_some hs
  have hT' := mem_msgNeed (P := Option Pos) (N := signatureLimit) msg
  unfold digestT pairR
  show digestOfPair (pairAt (extW w) (strOut L msg)) =
    digestOfPair (extW (entryEquiv hT hT' w) (.dig msg))
  rw [strOut_some hs]
  show digestOfPair (extW w (.str j)) = _
  rw [extW_of_mem _ (str_mem_of_entry hT), extW_of_mem _ (dig_mem_of_entry hT'),
    entryEquiv_dig]

/-- **The digest past the stream**: both sides reveal the same digest. -/
theorem digestT_fall {L : Finset TPos} {msg : Message} (hs : streamIdx L msg = none)
    (w : RevealVals TVal (strNeed L msg)) :
    digestT strPol L msg w =
      digestT msgPol (msgLab L) msg
        (fallEquiv (mem_strNeed_none hs) (mem_msgNeed (P := Option Pos) (N := signatureLimit)
          msg) w) := by
  have hT := mem_strNeed_none hs
  have hT' := mem_msgNeed (P := Option Pos) (N := signatureLimit) msg
  unfold digestT pairR
  show digestOfPair (pairAt (extW w) (strOut L msg)) =
    digestOfPair (extW (fallEquiv hT hT' w) (.dig msg))
  rw [strOut_none hs]
  show digestOfPair (extW w (.dig msg)) = _
  rw [extW_of_mem _ ((hT _).2 rfl), extW_of_mem _ ((hT' _).2 rfl), fallEquiv_apply]

omit [Fintype M] [DecidableEq M] in
/-- **After the digest port**, the counter searches and the publication are simulated by
themselves, at equal digests. -/
theorem renSim_signTail {Q : Finset TPos → Prop} (seed : PublicParameter) (B : QReg)
    (R : Randomizer) {d d' : MessageDigest} (hd : d = d') :
    Sim Q ((selectT M upd seed B (keyOf 0 (digestIndex d))).bind fun g₀ ↦
        (selectT M upd seed B (keyOf 1 (digestIndex d))).bind fun g₁ ↦
        (selectT M upd seed B (keyOf 2 (digestIndex d))).bind fun g₂ ↦
        publishAllT M B (digestIndex d) (digestForsLeaves d) R g₀ g₁ g₂)
      ((selectT M upd seed B (keyOf 0 (digestIndex d'))).bind fun g₀ ↦
        (selectT M upd seed B (keyOf 1 (digestIndex d'))).bind fun g₁ ↦
        (selectT M upd seed B (keyOf 2 (digestIndex d'))).bind fun g₂ ↦
        publishAllT M B (digestIndex d') (digestForsLeaves d') R g₀ g₁ g₂) := by
  subst hd
  exact (renSim_selectT M upd seed B rfl).bind₂ fun _ ↦
    (renSim_selectT M upd seed B rfl).bind₂ fun _ ↦
      (renSim_selectT M upd seed B rfl).bind₂ fun _ ↦ renSim_publishAllT M B rfl rfl R _ _ _

omit [Fintype M] [DecidableEq M] in
/-- **The signer at `strPol` is simulated by the signer at `msgPol`.** -/
theorem renSim_signT (B : QReg) (msg : Message) :
    Sim (fun _ ↦ True) (signT M upd strPol B msg) (signT M upd msgPol B msg) := by
  have hU := (valOnly_sigReveal msg).asg
  refine renSim_revealThen_val (valOnly_sigReveal msg) ?_
  intro w₁ L m₁ _
  dsimp only
  rcases hs : streamIdx L msg with _ | j
  · refine renSim_revealFall hU hs ?_
    intro w₂ L₂ m₂ _
    dsimp only
    refine renSim_progThen (portSim_digPort_fall hs) trivial trivial ?_
    exact renSim_signTail M upd _ B _ (digestT_fall hs w₂)
  · refine renSim_revealEntry hU hs ?_
    intro w₂ L₂ m₂ _
    dsimp only
    refine renSim_progThen (portSim_digPort_entry hs) trivial trivial ?_
    exact renSim_signTail M upd _ B _ (digestT_entry hs w₂)

omit [Fintype M] [DecidableEq M] in
/-- **The challenger at `strPol` is simulated by the challenger at `msgPol`.** -/
theorem renSim_challengeT (A : QReg) (c : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    Sim (fun _ ↦ True) (challengeT M upd strPol A c) (challengeT M upd msgPol A c) := by
  rcases c with o | ⟨_ | msg, E, ℓ⟩
  · exact renSim_readLift _ _ _ _ _
  · exact renSim_readLift _ _ _ _ _
  · exact (renSim_act_bind _ fun _ ↦ renSim_signT M upd _ msg).bind fun _ _ ↦ .pure _ _

omit [Fintype M] [DecidableEq M] in
/-- A read program followed by a pure step is simulated by itself. -/
theorem renSim_readsThenT {Q : Finset TPos → Prop} {α β : Type} (oa : OracleComp RomOracles α)
    (f : α → β) : Sim Q (readsThenT M oa f) (readsThenT M oa f) := by
  rw [readsThenT_eq]
  exact (renSim_readLift _ _ _ _ _).bind₂ fun _ ↦ .pure _ _

omit [Fintype M] [DecidableEq M] in
/-- **The game at `strPol` is simulated by the game at `msgPol`**: the renaming of the stream
entries of the marked messages to their digest cells. -/
theorem renSim_gameT (A : SAdversary) :
    Sim (fun _ ↦ True) (gameT M upd strPol A) (gameT M upd msgPol A) := by
  refine renSim_revealThen_val valOnly_pkReveal ?_
  intro _ _ _ _
  exact ((renSim_substitute _ _ _ (renSim_challengeT M upd) _).bind₂ fun _ ↦
    renSim_readsThenT M _ _).mono fun _ _ ↦ trivial

end sim

/-! ## The averaged laws of the two policies -/

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M)

/-- **The stream relabelling** (the game-level reindexing): averaged over uniform hidden values,
the runtime-2 game started with nothing revealed has the same law at the hybrid side's policy
`msgPol` and at the event side's `strPol`, for every inner memory and trial update. -/
theorem uavg_gameT_msgPol_eq_strPol (A : SAdversary) (m₀ : M) (ρ : SubState (QReg.of Unit))
    {γ : Type*} [MeasurableSpace γ] (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ)
    {s : Set γ} (hs : MeasurableSet s) :
    uavg (fun θ : TVals ↦ (runtimeR ((∅ : Finset TPos), m₀)).evalDistMap .instruments
        (realizeT θ (gameT M upd msgPol A)) ρ f s) =
      uavg (fun θ : TVals ↦ (runtimeR ((∅ : Finset TPos), m₀)).evalDistMap .instruments
        (realizeT θ (gameT M upd strPol A)) ρ f s) := by
  have h := fun pol ↦ uavg_realizeT_outcome_eq_sampled (good := goodQ)
    LocalSig.Interp.instruments m₀ (gameT M upd pol A) (disc_gameT M upd pol A ∅)
    (keepsLab_gameT M upd pol A) ρ f hs
  rw [h msgPol, h strPol]
  exact congrArg (· s) (evalDistMap_sampled_eq_of_renSim LocalSig.Interp.instruments m₀
    (renSim_gameT M upd A) trivial (streamInv_empty (P := Option Pos) (J := Message)
      (N := signatureLimit) (Ω := PairOut)) msgLab_empty msgStore_empty ρ f).symm

end Quantum.Qrom.Sphincs

end
