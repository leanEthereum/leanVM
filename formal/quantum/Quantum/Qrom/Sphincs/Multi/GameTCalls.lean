module

public import Quantum.Qrom.Sphincs.Multi.Template
public import Quantum.Qrom.Sphincs.Classify
public import Quantum.Cost.Charge

@[expose] public section

/-!
# The calls of leanSPHINCS's realized multi-user runtime-2 template game in the QROM

The `n`-user analog of `Quantum.Qrom.Sphincs.GameTCalls` and of the pending invariant of
`Quantum.Qrom.Sphincs.GameTFacts`, for `realizeT θ (muGameT M upd pols valid A)`, in the shape of
`Quantum.Qrom.Xmss.Multi.GameTCalls`. The sources of the cells (`srcOf`, `revealSet_*`,
`DigestPolicy.NoVal`), the verifier's calls (`verifyCalls`), the publications' program calls
(`pubCallsQ`) and runtime 1's read programs (`chg_readsProgram`) are the single-user ones.

* **The source invariant of `n` users** (`SrcInvN θ`): every position of user `i` whose source
  `(i, srcOf p)` is revealed has user `i`'s cell hardwired. `PendInvN θ C` with pending cells `C`,
  `HPendN` (templates keeping it), `hPend_muGameT` for digest policies revealing no value
  coordinate; `forallQueries_muGameQSN`, `forallQueries_prefixQSN`: Masses' `hinv` for any ports
  `Q` other than the program and record ports, from states with an empty memory label.
* **Encoding cells** (`isEncCell`: slot `.enc`): every trial cell is one (`isEncCell_trialCell`),
  no table cell is (`isEncCell_cellOf`).
* **Charges by kind** (`tChargeSN`, `rChargeSN`: `a` per sponge call, `b` per read at a cell other
  than an encoding cell, `b'` per read at an encoding cell, `c` per program call, `d` per reveal or
  record): `chg_selOrMemoTN` (no call on a memo hit), `chg_signTN` (`signCallsSN`: three full
  searches whatever the memo), `chg_challengeTN` (`memoChargeS`), `chg_realizeT_muGameT`,
  `chg_realizeT_prefixTN` (`gameCallsSN`).
* **Counts**: `advCalls_muGameQS` (`q` sponge calls), `clsCalls_muGameQS` (`clsCapSN total`,
  `clsCapSN_eq`, `clsCapSN_le`), `progCalls_muGameQS` (`progCapSN`), `readQCalls_muGameQS`
  (`verifyCalls` reads at cells other than encoding cells), and the same for the prefix.

The reads keep the label: Template's `keepsLab_muGameT`, `keepsLab_prefixTN`.
-/

open Matrix IPFunctor
open scoped Kronecker
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

universe u v w w₁

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key keyOf msgPos)
open Quantum.Xmss.Hybrid (LazyProg restrictTo ReadMono ReadKeeps readKeeps_liftRead
  querySupportedOn_queryStep progUpdate hwProgKraus_ne_zero_snd clsKraus_ne_zero_cls)
open Quantum.Xmss.Assembly (tmplSpec recHwSpec recSpec readLift readLiftQ readLens tmplLens
  realizeT revealThen progThen RevealVals memLab invSupp recKraus_ne_zero runtimeR extCls chg_act
  chg_map)
open Quantum.Xmss (extProgCharge)
open Quantum.Qrom.SufCma.Multi (MuPort muAdvSpec muChallenge withMuSignLog cmdCharge hashCharge
  signCharge isChargeBound_withMuSignLog)

/- Instance search for the registers over `Finset (TPosN n)` exceeds the default size. -/
set_option synthInstance.maxSize 2000

attribute [local irreducible] sphincsRom

variable {n : ℕ}

/-! ## The source invariant of `n` users -/

section pending

variable {M : Type}

/-- **The source invariant of `n` users** at the hidden values `θ`: every position of user `i`
whose source coordinate is revealed has user `i`'s cell hardwired. -/
def SrcInvN (θ : TValsN n) (r : HwReg PairOut HashDomain (Finset (TPosN n) × M)) : Prop :=
  ∀ i p, (i, srcOf p) ∈ r.2.2.1 → r.2.1.1 (cellOf (seedsOf θ i) p (tabOf (userOf θ i))) ≠ none

/-- **The source invariant of `n` users with pending cells `C`**: a position of user `i` whose
source is revealed has user `i`'s cell hardwired or pending. -/
def PendInvN (θ : TValsN n) (C : Set HashDomain)
    (r : HwReg PairOut HashDomain (Finset (TPosN n) × M)) : Prop :=
  ∀ i p, (i, srcOf p) ∈ r.2.2.1 →
    r.2.1.1 (cellOf (seedsOf θ i) p (tabOf (userOf θ i))) ≠ none ∨
      cellOf (seedsOf θ i) p (tabOf (userOf θ i)) ∈ C

/-- The cells whose source a reveal of `T` reveals. -/
def revealCellsN (θ : TValsN n) (T : Finset (TPosN n)) : Set HashDomain :=
  {z | ∃ i p, (i, srcOf p) ∈ T ∧ cellOf (seedsOf θ i) p (tabOf (userOf θ i)) = z}

variable {θ : TValsN n}

theorem pendInvN_mono {C C' : Set HashDomain} (h : C ⊆ C')
    {r : HwReg PairOut HashDomain (Finset (TPosN n) × M)} (hr : PendInvN θ C r) :
    PendInvN θ C' r :=
  fun i p hp ↦ (hr i p hp).imp_right fun hc ↦ h hc

theorem pendInvN_of_eq {C : Set HashDomain}
    {r r' : HwReg PairOut HashDomain (Finset (TPosN n) × M)}
    (h1 : r'.2.1 = r.2.1) (h2 : r'.2.2.1 = r.2.2.1) (hr : PendInvN θ C r) : PendInvN θ C r' := by
  intro i p hp
  rw [h1]
  exact hr i p (h2 ▸ hp)

theorem pendInvN_of_label_empty {C : Set HashDomain}
    {r : HwReg PairOut HashDomain (Finset (TPosN n) × M)} (h : r.2.2.1 = ∅) :
    PendInvN θ C r := by
  intro i p hp
  rw [h] at hp
  exact absurd hp (Finset.notMem_empty _)

/-- A program port hardwires its cell and keeps the others: it leaves the pending set. -/
theorem pendInvN_prog {C : Set HashDomain} (c : HwProg PairOut HashDomain)
    {r r' : HwReg PairOut HashDomain (Finset (TPosN n) × M)}
    (h : r'.2 = (progUpdate c r.2.1, r.2.2)) (hr : PendInvN θ C r) :
    PendInvN θ (C \ progCells c) r' := by
  intro i p hp
  rw [h] at hp ⊢
  rcases hr i p hp with hc | hc
  · exact .inl (progUpdate_ne_none hc)
  · by_cases hz : cellOf (seedsOf θ i) p (tabOf (userOf θ i)) ∈ progCells c
    · exact .inl (progUpdate_self_ne_none hz)
    · exact .inr ⟨hc, hz⟩

/-- A reveal of `T` adds the cells whose source it reveals to the pending set. -/
theorem pendInvN_reveal {C : Set HashDomain} (T : Finset (TPosN n))
    {r r' : HwReg PairOut HashDomain (Finset (TPosN n) × M)}
    (h : r'.2 = (r.2.1, (r.2.2.1 ∪ T, r.2.2.2))) (hr : PendInvN θ C r) :
    PendInvN θ (C ∪ revealCellsN θ T) r' := by
  intro i p hp
  rw [h] at hp ⊢
  rcases Finset.mem_union.1 hp with hp | hp
  · exact (hr i p hp).imp_right Or.inl
  · exact .inr (.inr ⟨i, p, hp, rfl⟩)

theorem srcInvN_of_pendInvN {r : HwReg PairOut HashDomain (Finset (TPosN n) × M)}
    (h : PendInvN θ ∅ r) : SrcInvN θ r :=
  fun i p hp ↦ (h i p hp).resolve_right (Set.notMem_empty _)

variable (θ)

/-- A reveal of user `i`'s coordinates makes pending at most user `i`'s cells whose source it
reveals. -/
theorem revealCellsN_atU (i : Fin n) (T : Finset TPos) :
    revealCellsN θ (atU i T) ⊆ revealSet (userOf θ i) T := by
  rintro z ⟨j, p, hp, rfl⟩
  obtain ⟨rfl, hs⟩ := mem_atU.1 hp
  exact ⟨p, hs, rfl⟩

theorem revealCellsN_pkRevealN : revealCellsN θ pkRevealN ⊆ ∅ := by
  rintro z ⟨i, p, hp, rfl⟩
  rw [pkRevealN, Finset.mem_product] at hp
  exact revealSet_pkReveal (userOf θ i) ⟨p, hp.2, rfl⟩

/-- **`R(M)` of user `i` is the source of user `i`'s digest cell of `M` only.** -/
theorem revealCellsN_sigReveal (i : Fin n) (msg : Message) :
    revealCellsN θ (atU i {seedC, rootC, rndC msg}) ⊆
      {cellOf (seedsOf θ i) (digPos msg) (tabOf (userOf θ i))} :=
  (revealCellsN_atU θ i _).trans (revealSet_sigReveal (userOf θ i) msg)

theorem revealCellsN_msgPos (i : Fin n) (K : Key) :
    revealCellsN θ (atU i {vcoord (msgPos K)}) ⊆ ∅ :=
  (revealCellsN_atU θ i _).trans (revealSet_msgPos (userOf θ i) K)

theorem revealCellsN_noVal {pol : DigestPolicy} (hpol : pol.NoVal) (i : Fin n)
    (L : Finset TPos) (msg : Message) : revealCellsN θ (atU i (pol.need L msg)) ⊆ ∅ :=
  (revealCellsN_atU θ i _).trans (revealSet_noVal (userOf θ i) hpol L msg)

/-- The cells a layer signature's reveal of user `i` makes pending are those it programs. -/
theorem revealCellsN_layerReveal (i : Fin n) (K : Key) (x : Encoding) :
    revealCellsN θ (atU i (layerReveal K x)) ⊆
      {z | ∃ p ∈ layerPos K x, cellOf (seedsOf θ i) p (tabOf (userOf θ i)) = z} :=
  (revealCellsN_atU θ i _).trans (revealSet_layerReveal (userOf θ i) K x)

/-- The cells a FORS opening's reveal of user `i` makes pending are those it programs. -/
theorem revealCellsN_forsReveal (i : Fin n) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    revealCellsN θ (atU i (forsReveal idx lv)) ⊆
      {z | ∃ p ∈ forsPos idx lv, cellOf (seedsOf θ i) p (tabOf (userOf θ i)) = z} :=
  (revealCellsN_atU θ i _).trans (revealSet_forsReveal (userOf θ i) idx lv)

end pending

/-! ## Templates that keep the source invariant of `n` users

`HPendN θ y C C'`: run from states on the pending invariant `C`, the template `y` calls the
sponge and read ports with nothing pending, its reads keep the label, a program port leaves the
pending set, a reveal of `T` adds the cells whose source it reveals; it ends on `C'`. -/

section hp

variable {M : Type} {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- The condition of `HPendN` on the pending set before a call. -/
def portPreQN : (XSpecSN M n).Port → Set HashDomain → Prop
  | .inl (.inl (.inl _)), C => C = ∅
  | .inl (.inl (.inr c)), C => C = ∅ ∧ ReadKeeps c.1
  | .inl (.inr _), _ => True
  | .inr _, _ => True

/-- The pending set after a call. -/
def portPostQN (θ : TValsN n) : (XSpecSN M n).Port → Set HashDomain → Set HashDomain
  | .inl (.inl (.inl _)), C => C
  | .inl (.inl (.inr _)), C => C
  | .inl (.inr p), C => C \ progCells (p.1.realize θ)
  | .inr T, C => C ∪ revealCellsN θ T

/-- The condition before a command. -/
def cmdPreQN {A : QReg} : QuantumComp.Cmd L (XSpecSN M n) A → Set HashDomain → Prop
  | .prim _, _ => True
  | .query i _ _, C => portPreQN i C

/-- The pending set after a command. -/
def cmdPostQN (θ : TValsN n) {A : QReg} :
    QuantumComp.Cmd L (XSpecSN M n) A → Set HashDomain → Set HashDomain
  | .prim _, C => C
  | .query i _ _, C => portPostQN θ i C

/-- **A template that keeps the source invariant of `n` users**, from the pending set `C` to
`C'`. -/
def HPendN (θ : TValsN n) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor L (XSpecSN M n)) Ω A → Set HashDomain →
      Set HashDomain → Prop
  | _, .pure _, C, C' => C ⊆ C'
  | _, .liftBind c next, C, C' => cmdPreQN c C ∧ ∀ b, HPendN θ (next b) (cmdPostQN θ c C) C'

theorem cmdPreQN_anti {A : QReg} (c : QuantumComp.Cmd L (XSpecSN M n) A) {C D : Set HashDomain}
    (hD : D ⊆ C) (h : cmdPreQN c C) : cmdPreQN c D := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · trivial
  · exact Set.subset_empty_iff.1 (h ▸ hD)
  · exact ⟨Set.subset_empty_iff.1 (h.1 ▸ hD), h.2⟩
  · trivial
  · trivial

theorem cmdPostQN_mono (θ : TValsN n) {A : QReg} (c : QuantumComp.Cmd L (XSpecSN M n) A)
    {C D : Set HashDomain} (hD : D ⊆ C) : cmdPostQN θ c D ⊆ cmdPostQN θ c C := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · exact hD
  · exact hD
  · exact hD
  · exact Set.sdiff_subset_sdiff_left hD
  · exact Set.union_subset_union_left _ hD

variable (θ : TValsN n)

theorem hPendN_mono {A : QReg} (y : IFreeM (QuantumComp.toIPFunctor L (XSpecSN M n)) Ω A)
    {C C' D D' : Set HashDomain} (hy : HPendN θ y C C') (hD : D ⊆ C) (hD' : C' ⊆ D') :
    HPendN θ y D D' := by
  induction y using IFreeM.inductionOn generalizing C D with
  | pure _ _ => exact hD.trans (hy.trans hD')
  | liftBind _ c next ih =>
    exact ⟨cmdPreQN_anti c hD hy.1, fun b ↦ ih b (hy.2 b) (cmdPostQN_mono θ c hD)⟩

theorem hPendN_cast {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor L (XSpecSN M n)) Ω A) (C C' : Set HashDomain) :
    HPendN θ (e ▸ y) C C' ↔ HPendN θ y C C' := by
  subst e
  rfl

theorem hPendN_bind {A : QReg} {Y : QReg → Type w₁}
    (x : IFreeM (QuantumComp.toIPFunctor L (XSpecSN M n)) Ω A)
    (g : ∀ u, Ω u → IFreeM (QuantumComp.toIPFunctor L (XSpecSN M n)) Y u)
    {C D C' : Set HashDomain} (hx : HPendN θ x C D) (hg : ∀ u a, HPendN θ (g u a) D C') :
    HPendN θ (x.bind g) C C' := by
  induction x using IFreeM.inductionOn generalizing C with
  | pure _ a => exact hPendN_mono θ _ (hg _ a) hx subset_rfl
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

theorem hPendN₂_bind {A B B' : QReg} {α : Type w} {β : Type w₁}
    (x : QuantumComp₂ L (XSpecSN M n) A B α) (g : α → QuantumComp₂ L (XSpecSN M n) B B' β)
    {C D C' : Set HashDomain} (hx : HPendN θ x C D) (hg : ∀ a, HPendN θ (g a) D C') :
    HPendN θ (x.bind g) C C' := by
  refine hPendN_bind θ x _ hx fun u p ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hg a

/-- Substituting trees that keep the invariant with nothing pending. -/
theorem hPendN_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor L spec)
      (QuantumComp.toIPFunctor L (XSpecSN M n)))
    (hσ : ∀ A c, HPendN θ (σ A c) ∅ ∅) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor L spec) Ω A) : HPendN θ (x.substitute σ) ∅ ∅ := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind s c next ih =>
    rw [IFreeM.substitute_liftBind]
    exact hPendN_bind θ _ _ (hσ s c) fun u ans ↦ (hPendN_cast θ ans.2 _ _ _).mpr (ih ans.1)

/-- **Runtime 1's programs keep the invariant**: their sponge and read ports (the reads lifted,
keeping the label) leave nothing pending. -/
theorem hPendN_readLift {A : QReg}
    (y : QuantumComp L (hwReadSpec PairOut HashDomain M) Ω A) :
    HPendN θ (readLift goodQN y) ∅ ∅ := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind _ c next ih =>
    show HPendN θ (IFreeM.mapLens (readLens (goodQN (n := n)))
      (IFreeM.liftBind c next)) ∅ ∅
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · refine ⟨trivial, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨rfl, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨⟨rfl, readKeeps_liftRead c⟩, fun b ↦ ?_⟩
      dsimp only
      exact ih _

theorem hPendN_act {A B : QReg} {α : Type} (p : SubInstrument A B α) (C : Set HashDomain) :
    HPendN θ (QComp.act (spec := XSpecSN M n) p) C C :=
  ⟨trivial, fun _ ↦ subset_rfl⟩

/-- A reveal makes the cells whose source it reveals pending. -/
theorem hPendN_revealThen {B B' : QReg} {α : Type} (T : Finset (TPosN n))
    (k : RevealVals (TValN n) T × (Finset (TPosN n) × M) → QComp (XSpecSN M n) B B' α)
    {C C' : Set HashDomain} (hk : ∀ r, HPendN θ (k r) (C ∪ revealCellsN θ T) C') :
    HPendN θ (revealThen goodQN T k) C C' :=
  ⟨trivial, fun r ↦ hPendN₂_bind θ _ _ (hPendN_act θ _ _) fun _ ↦ hk r.down⟩

theorem hPendN_progThen {B B' : QReg} {α : Type}
    (p : LazyProg PairOut HashDomain (TPosN n) (TValN n)) (hp : goodQN p)
    (k : QComp (XSpecSN M n) B B' α) {C C' : Set HashDomain}
    (hk : HPendN θ k (C \ progCells (p.realize θ)) C') : HPendN θ (progThen p hp k) C C' :=
  ⟨trivial, fun _ ↦ hPendN₂_bind θ _ _ (hPendN_act θ _ _) fun _ ↦ hk⟩

theorem hPend_progPosN (i : Fin n) (B : QReg) (ps : List Pos) (hps : ∀ p ∈ ps, p.1.IsStruct)
    (C : Set HashDomain) :
    HPendN θ (progPosN M i B ps) C
      (C \ {z | ∃ p ∈ ps, cellOf (seedsOf θ i) p (tabOf (userOf θ i)) = z}) := by
  induction ps generalizing C with
  | nil => exact fun z hz ↦ ⟨hz, fun ⟨_, hp, _⟩ ↦ absurd hp List.not_mem_nil⟩
  | cons p ps ih =>
    refine hPendN_progThen θ (progTN i p) trivial _ (hPendN_mono θ _ (ih (fun q hq ↦ hps q
      (List.mem_cons_of_mem _ hq)) _) subset_rfl ?_)
    rw [realize_progTN (hps p List.mem_cons_self) i θ]
    rintro z ⟨⟨hz, hne⟩, hn⟩
    refine ⟨hz, ?_⟩
    rintro ⟨q, hq, rfl⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hne rfl
    · exact hn ⟨q, hq, rfl⟩

/-- **User `i`'s FORS opening keeps the invariant**: the cells with a revealed source are the
opening's, which it then programs. -/
theorem hPend_forsOpenTN (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) : HPendN θ (forsOpenTN M i B idx lv) ∅ ∅ :=
  hPendN_revealThen θ _ _ fun _ ↦ hPendN₂_bind θ _ _ (hPend_progPosN θ i B _
    (fun _ hp ↦ isStruct_of_mem_forsPos hp) _) fun _ ↦ by
    rintro z ⟨hz | hz, hn⟩
    · exact hz
    · exact hn (revealCellsN_forsReveal θ i idx lv hz)

/-- **User `i`'s layer publication keeps the invariant.** -/
theorem hPend_publishTN (i : Fin n) (B : QReg) (K : Key) (c : EncodingCounter) (x : Encoding) :
    HPendN θ (publishTN M i B K c x) ∅ ∅ :=
  hPendN_revealThen θ _ _ fun _ ↦ hPendN₂_bind θ _ _ (hPend_progPosN θ i B _
    (fun _ hp ↦ isStruct_of_mem_layerPos hp) _) fun _ ↦ by
    rintro z ⟨hz | hz, hn⟩
    · exact hz
    · exact hn (revealCellsN_layerReveal θ i K x hz)

theorem hPend_publishAllTN (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (R : Randomizer) (g₀ g₁ g₂ : SelS) :
    HPendN θ (publishAllTN M i B idx lv R g₀ g₁ g₂) ∅ ∅ := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try exact subset_rfl
  simp only [publishAllTN]
  refine hPendN₂_bind θ _ _ (hPend_forsOpenTN θ i B _ _) fun _ ↦ ?_
  refine hPendN₂_bind θ _ _ (hPend_publishTN θ i B _ _ _) fun _ ↦ ?_
  refine hPendN₂_bind θ _ _ (hPend_publishTN θ i B _ _ _) fun _ ↦ ?_
  exact hPendN₂_bind θ _ _ (hPend_publishTN θ i B _ _ _) fun _ ↦ subset_rfl

variable (upd : Fin n → TrialUpd M)

/-- **User `i`'s counter search keeps the invariant**: the value the key signs is no source. -/
theorem hPend_selectTN (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key) :
    HPendN θ (selectTN M upd i seed B K) ∅ ∅ :=
  hPendN_revealThen θ _ _ fun _ ↦ hPendN_mono θ _ (hPendN_readLift θ _)
    (Set.union_subset (subset_refl _) (revealCellsN_msgPos θ i K)) subset_rfl

theorem hPend_selOrMemoTN (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key)
    (o : Option SelS) : HPendN θ (selOrMemoTN M upd i seed B K o) ∅ ∅ := by
  cases o with
  | none => exact hPend_selectTN θ upd i seed B K
  | some _ => exact subset_rfl

/-- **User `i`'s signature keeps the invariant**, for a digest policy revealing no value
coordinate: the reveal of `R(M)` makes user `i`'s digest cell pending, which the digest port then
programs. -/
theorem hPend_signTN {pols : Fin n → DigestPolicy} (hpols : ∀ i, (pols i).NoVal) (i : Fin n)
    (B : QReg) (msg : Message) (h : KeyMemo) : HPendN θ (signTN M upd pols i B msg h) ∅ ∅ := by
  unfold signTN
  refine hPendN_revealThen θ _ _ fun r₁ ↦ hPendN_revealThen θ _ _ fun r₂ ↦ ?_
  refine hPendN_progThen θ _ trivial _ (hPendN_mono θ _ (C := ∅) ?_ ?_ subset_rfl)
  · refine hPendN₂_bind θ _ _ (hPend_selOrMemoTN θ upd i _ B _ _) fun _ ↦ ?_
    refine hPendN₂_bind θ _ _ (hPend_selOrMemoTN θ upd i _ B _ _) fun _ ↦ ?_
    refine hPendN₂_bind θ _ _ (hPend_selOrMemoTN θ upd i _ B _ _) fun _ ↦ ?_
    rw [QuantumComp₂.map_eq_bind_pure]
    exact hPendN₂_bind θ _ _ (hPend_publishAllTN θ i B _ _ _ _ _ _) fun _ ↦ subset_rfl
  · rw [realize_digPortN, ← cellOf_digPos (seedsOf θ i)]
    rintro z ⟨(hz | hz) | hz, hn⟩
    · exact hz
    · exact hn (revealCellsN_sigReveal θ i msg hz)
    · exact revealCellsN_noVal θ (hpols i) i _ msg hz

/-- **The challenger keeps the invariant**, with nothing pending between commands. -/
theorem hPend_challengeTN {pols : Fin n → DigestPolicy} (hpols : ∀ i, (pols i).NoVal)
    (A : QReg) (c : QuantumComp.Cmd LocalSig.instruments.{0} (memoSpecS n) A) :
    HPendN θ (challengeTN M upd pols A c) ∅ ∅ := by
  rcases c with o | ⟨_ | ⟨i, q⟩, E, ℓ⟩
  · exact hPendN_readLift θ _
  · exact hPendN_readLift θ _
  · exact hPendN_bind θ _ _ (hPendN₂_bind θ _ _ (hPendN_act θ _ _) fun _ ↦
      hPend_signTN θ upd hpols i _ q.1 q.2) fun _ _ ↦ subset_rfl

theorem hPend_prefixTN {pols : Fin n → DigestPolicy} (hpols : ∀ i, (pols i).NoVal)
    (A : MuAdversaryS n) : HPendN θ (prefixTN M upd pols A) ∅ ∅ :=
  hPendN_revealThen θ _ _ fun _ ↦ hPendN_mono θ _
    (hPendN₂_bind θ _ _ (hPendN_substitute θ _ (hPend_challengeTN θ upd hpols) _) fun _ ↦
      subset_rfl)
    (Set.union_subset (subset_refl _) (revealCellsN_pkRevealN θ)) subset_rfl

theorem hPend_verifyTN (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (x : (Fin n → PublicKey) × MuRunS n) : HPendN θ (verifyTN M valid x) ∅ ∅ := by
  unfold verifyTN
  rw [readsThenTN_eq]
  exact hPendN₂_bind θ _ _ (hPendN_readLift θ _) fun _ ↦ subset_rfl

/-- **The game keeps the source invariant of `n` users**, for digest policies revealing no value
coordinate. -/
theorem hPend_muGameT {pols : Fin n → DigestPolicy} (hpols : ∀ i, (pols i).NoVal)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n) :
    HPendN θ (muGameT M upd pols valid A) ∅ ∅ := by
  rw [muGameT_eq_prefixTN_bind]
  exact hPendN₂_bind θ _ _ (hPend_prefixTN θ upd hpols A) fun x ↦ hPend_verifyTN θ valid x

end hp

/-! ## The steps of `runtimeR` on the pending invariant -/

section steps

variable {M : Type} [Fintype M] [DecidableEq M] {θ : TValsN n}

omit [Fintype M] in
/-- A read port keeping the label keeps the hardwired cells and the label. -/
theorem hwReadKraus_ne_zero_keepQN {c : HwRead PairOut HashDomain (Finset (TPosN n) × M)}
    (hc : ReadKeeps c) (r : c.Result) {u u' : Unit}
    {s s' : HwReg PairOut HashDomain (Finset (TPosN n) × M)}
    (h : hwReadKraus c r (u', s') (u, s) ≠ 0) : s'.2.1 = s.2.1 ∧ s'.2.2.1 = s.2.2.1 := by
  cases c with
  | readH z upd =>
    simp only [hwReadKraus, readKrausH] at h
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
    exact ⟨rfl, (hc _ _).trans (congrArg Prod.fst hp).symm⟩
  | readK x upd =>
    simp only [hwReadKraus, readKrausK] at h
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
    exact ⟨rfl, (hc _ _).trans (congrArg Prod.fst hp).symm⟩
  | readK' x upd =>
    simp only [hwReadKraus, readKrausK'] at h
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
    exact ⟨rfl, (hc _ _).trans (congrArg Prod.fst hp).symm⟩

variable (θ) in
/-- A step of `runtimeR` at port `i` carries support on the pending invariant `C` to support on
the pending invariant `C'`. -/
def StepPendN (m₀ : Finset (TPosN n) × M) (i : (recHwSpec PairOut HashDomain (TPosN n) M).Port)
    (C C' : Set HashDomain) : Prop :=
  ∀ r σ, QuerySupportedOn (fun m : (recHwSpec PairOut HashDomain (TPosN n) M).In i ×
      (runtimeR m₀).D ↦ m.2) {s | PendInvN θ C s} σ →
    QuerySupportedOn (fun m : (recHwSpec PairOut HashDomain (TPosN n) M).Out i ×
      (runtimeR m₀).D ↦ m.2) {s | PendInvN θ C' s} (((runtimeR m₀).step i).branch r σ)

theorem stepPendN_sponge (m₀ : Finset (TPosN n) × M) (i : SpongePort) (C : Set HashDomain) :
    StepPendN θ m₀ (.inl (.inl (.inl i))) C C := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inl i)))).branch r σ =
      MatrixMap.conj ((spongeHardwired PairOut HashDomain
        (hwEmpty PairOut HashDomain) m₀).U i) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty PairOut HashDomain) m₀ i
      r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    have he := snd_eq_of_spongeHardwired_U_ne_zero (hwEmpty PairOut HashDomain) m₀ i q.1 q'.1
      q.2 q'.2 hK
    exact pendInvN_of_eq (congrArg Prod.fst he) (congrArg (fun t ↦ t.2.1) he) hq

theorem stepPendN_read (m₀ : Finset (TPosN n) × M)
    (c : {c : HwRead PairOut HashDomain (Finset (TPosN n) × M) //
      ReadMono (memLab PairOut HashDomain (TPosN n) M) c})
    (hc : ReadKeeps c.1) (C : Set HashDomain) : StepPendN θ m₀ (.inl (.inl (.inr c.1))) C C := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inr c.1)))).branch r σ =
      MatrixMap.conj (hwReadKraus c.1 r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty PairOut HashDomain) m₀ c.1
      r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    obtain ⟨h1, h2⟩ := hwReadKraus_ne_zero_keepQN hc r (u := q.1) (s := q.2) (u' := q'.1)
      (s' := q'.2) hK
    exact pendInvN_of_eq h1 h2 hq

theorem stepPendN_prog (m₀ : Finset (TPosN n) × M) (c : HwProg PairOut HashDomain)
    (C : Set HashDomain) : StepPendN θ m₀ (.inl (.inr c)) C (C \ progCells c) := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inr c))).branch r σ =
      MatrixMap.conj (hwProgKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty PairOut HashDomain) m₀ c
      r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    pendInvN_prog c (hwProgKraus_ne_zero_snd c r (u := q.1) (s := q.2) (u' := q'.1)
      (s' := q'.2) hK) hq

theorem stepPendN_rec (m₀ : Finset (TPosN n) × M) (T : Finset (TPosN n)) (C : Set HashDomain) :
    StepPendN θ m₀ (.inr T) C (C ∪ revealCellsN θ T) := by
  intro r σ hσ
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    pendInvN_reveal T (recKraus_ne_zero (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK) hq

/-- An operator supported on the invariant presents, at a call, no diagonal mass outside it. -/
theorem relabel_diag_eq_zero_srcInvN (m₀ : Finset (TPosN n) × M) {A : QReg}
    {i : (recHwSpec PairOut HashDomain (TPosN n) M).Port} (E : QReg)
    (ℓ : A ≃ (recHwSpec PairOut HashDomain (TPosN n) M).In i × E)
    {ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | PendInvN θ ∅ s} ρ)
    (a : ((recHwSpec PairOut HashDomain (TPosN n) M).In i × (runtimeR m₀).D) × E)
    (ha : ¬SrcInvN θ a.1.2) :
    (SubInstrument.relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).branch () ρ a a =
      0 := by
  by_contra h
  have h₁ := (hρ.branch_relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).imp
    (q' := fun m : ((recHwSpec PairOut HashDomain (TPosN n) M).In i × (runtimeR m₀).D) × E ↦
      m.1.2)
    (S' := {s | PendInvN θ ∅ s}) fun m hm ↦ by
      obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D).surjective m
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
  exact ha (srcInvN_of_pendInvN (h₁ a a h).1)

end steps

/-! ## The invariant at the calls (`hinv`) -/

section hinv

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- One call of a realized program on the pending invariant. -/
theorem forallQueries_queryBind_of_stepPendN
    {Q : (recHwSpec PairOut HashDomain (TPosN n) M).Port → Prop}
    (m₀ : Finset (TPosN n) × M) (I : L.Interp) (θ : TValsN n) {A : QReg}
    (i : (recHwSpec PairOut HashDomain (TPosN n) M).Port) (E : QReg)
    (ℓ : A ≃ (recHwSpec PairOut HashDomain (TPosN n) M).In i × E)
    (k' : (recHwSpec PairOut HashDomain (TPosN n) M).Result i →
      QuantumComp L (recHwSpec PairOut HashDomain (TPosN n) M) Ω
        (QReg.of ((recHwSpec PairOut HashDomain (TPosN n) M).Out i × E)))
    {C C' : Set HashDomain} (hpre : Q i → C = ∅) (hstep : StepPendN θ m₀ i C C')
    (hk : ∀ r ρ', QuerySupportedOn (fun m : QReg.of
        ((recHwSpec PairOut HashDomain (TPosN n) M).Out i × E) × (runtimeR m₀).D ↦ m.2)
        {s | PendInvN θ C' s} ρ' →
      (runtimeR m₀).ForallQueries I (invSupp (runtimeR m₀) Q (SrcInvN θ)) (k' r) ρ')
    (ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ)
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | PendInvN θ C s} ρ) :
    (runtimeR m₀).ForallQueries I (invSupp (runtimeR m₀) Q (SrcInvN θ))
      (QuantumComp.queryBind i E ℓ k') ρ :=
  ⟨fun hq a ha ↦ relabel_diag_eq_zero_srcInvN (i := i) m₀ E ℓ (hpre hq ▸ hρ) a ha, fun r ↦
    hk r _ (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s) i r (hstep r) E ℓ hρ)⟩

/-- **The realized program of a template keeping the source invariant of `n` users presents, at
every call of the ports `Q` (no program or record port), only states of the invariant.** -/
theorem forallQueries_of_hPendN {Q : (recHwSpec PairOut HashDomain (TPosN n) M).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (hQ' : ∀ T, ¬Q (.inr T)) (m₀ : Finset (TPosN n) × M)
    (I : L.Interp) (θ : TValsN n) {A : QReg} (y : QuantumComp L (XSpecSN M n) Ω A) :
    ∀ C C', HPendN θ y C C' → ∀ ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | PendInvN θ C s} ρ →
      (runtimeR m₀).ForallQueries I (invSupp (runtimeR m₀) Q (SrcInvN θ))
        (realizeT θ y) ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _ _ _; trivial
  | primBind _ o k ih =>
    intro C C' hy ρ hρ b
    exact ih b C C' (hy.2 (ULift.up b)) _ (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _)
  | queryBind _ i E ℓ k ih =>
    intro C C' hy ρ hρ
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · exact forallQueries_queryBind_of_stepPendN m₀ I θ (.inl (.inl (.inl i))) E ℓ
        (fun r ↦ realizeT θ (k r)) (fun _ ↦ hy.1) (stepPendN_sponge m₀ i C)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepPendN m₀ I θ (.inl (.inl (.inr c.1))) E ℓ
        (fun r ↦ realizeT θ (k r)) (fun _ ↦ hy.1.1) (stepPendN_read m₀ c hy.1.2 C)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · cases p with
      | programH T₀ c =>
        exact forallQueries_queryBind_of_stepPendN m₀ I θ
          (.inl (.inr ((LazyProg.programH T₀ c).realize θ))) E ℓ (fun r ↦ realizeT θ (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepPendN_prog m₀ _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK T₀ c =>
        exact forallQueries_queryBind_of_stepPendN m₀ I θ
          (.inl (.inr ((LazyProg.programK T₀ c).realize θ))) E ℓ (fun r ↦ realizeT θ (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepPendN_prog m₀ _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK' T₀ c =>
        exact forallQueries_queryBind_of_stepPendN m₀ I θ
          (.inl (.inr ((LazyProg.programK' T₀ c).realize θ))) E ℓ (fun r ↦ realizeT θ (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepPendN_prog m₀ _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepPendN m₀ I θ (.inr T) E ℓ
        (fun m ↦ realizeT θ (k (restrictTo T θ, m))) (fun hq ↦ absurd hq (hQ' _))
        (stepPendN_rec m₀ T C)
        (fun m ↦ ih (restrictTo T θ, m) _ C' (hy.2 (ULift.up (restrictTo T θ, m)))) ρ hρ

/-- An initial state whose memory label is empty. -/
theorem querySupportedOn_initQSN (m₀ : Finset (TPosN n) × M) (hm₀ : m₀.1 = ∅) {A : QReg}
    (σ : Matrix A A ℂ) :
    QuerySupportedOn (fun a : A × QReg.of (HwReg PairOut HashDomain (Finset (TPosN n) × M)) ↦
      a.2.2.2.1) {∅} (σ ⊗ₖ (runtimeR (X := PairOut) (Z := HashDomain) m₀).init.matrix) := by
  intro a b h
  change (σ ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
    hwEmpty PairOut HashDomain, m₀) :
      HwReg PairOut HashDomain (Finset (TPosN n) × M))).matrix) a b ≠ 0 at h
  rw [SubState.matrix_basis, kroneckerMap_apply] at h
  have h' := right_ne_zero_of_mul h
  rw [Matrix.single_apply] at h'
  split_ifs at h' with he
  · show a.2.2.2.1 ∈ ({∅} : Set (Finset (TPosN n))) ∧ b.2.2.2.1 ∈ ({∅} : Set (Finset (TPosN n)))
    rw [← he.1, ← he.2]
    exact ⟨hm₀, hm₀⟩
  · exact absurd rfl h'

variable (upd : Fin n → TrialUpd M)

/-- **`hinv` for the realized multi-user template game**, for digest policies revealing no value
coordinate: from states with an empty memory label, every call of ports `Q` other than the program
and record ports sees the source invariant of `n` users. -/
theorem forallQueries_muGameQSN {Q : (recHwSpec PairOut HashDomain (TPosN n) M).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (hQ' : ∀ T, ¬Q (.inr T)) {pols : Fin n → DigestPolicy}
    (hpols : ∀ i, (pols i).NoVal) (m₀ : Finset (TPosN n) × M)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
    (θ : TValsN n)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg PairOut HashDomain (Finset (TPosN n) × M)))
      (QReg.of Unit × QReg.of (HwReg PairOut HashDomain (Finset (TPosN n) × M))) ℂ)
    (hρ : QuerySupportedOn (fun a : QReg.of Unit ×
      QReg.of (HwReg PairOut HashDomain (Finset (TPosN n) × M)) ↦ a.2.2.2.1) {∅} ρ) :
    (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m₀) Q (SrcInvN θ)) (realizeT θ (muGameT M upd pols valid A)) ρ :=
  forallQueries_of_hPendN hQ hQ' m₀ _ θ _ ∅ ∅ (hPend_muGameT θ upd hpols valid A) ρ
    (hρ.imp fun _ ha ↦ pendInvN_of_label_empty (Set.mem_singleton_iff.1 ha))

/-- The same for the challenge prefix. -/
theorem forallQueries_prefixQSN {Q : (recHwSpec PairOut HashDomain (TPosN n) M).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (hQ' : ∀ T, ¬Q (.inr T)) {pols : Fin n → DigestPolicy}
    (hpols : ∀ i, (pols i).NoVal) (m₀ : Finset (TPosN n) × M) (A : MuAdversaryS n)
    (θ : TValsN n)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg PairOut HashDomain (Finset (TPosN n) × M)))
      (QReg.of Unit × QReg.of (HwReg PairOut HashDomain (Finset (TPosN n) × M))) ℂ)
    (hρ : QuerySupportedOn (fun a : QReg.of Unit ×
      QReg.of (HwReg PairOut HashDomain (Finset (TPosN n) × M)) ↦ a.2.2.2.1) {∅} ρ) :
    (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m₀) Q (SrcInvN θ)) (realizeT θ (prefixTN M upd pols A)) ρ :=
  forallQueries_of_hPendN hQ hQ' m₀ _ θ _ ∅ ∅ (hPend_prefixTN θ upd hpols A) ρ
    (hρ.imp fun _ ha ↦ pendInvN_of_label_empty (Set.mem_singleton_iff.1 ha))

end hinv

/-! ## Encoding cells -/

section enc

/-- An encoding cell (slot `.enc`, read under the key its bytes name). -/
def isEncCell (z : HashDomain) : Bool :=
  match slotF z with
  | some (.enc ..) => true
  | _ => false

/-- **Every trial cell is an encoding cell.** -/
theorem isEncCell_trialCell (seed : PublicParameter) (K : Key) (m : Digest) (c : ℕ) :
    isEncCell (trialCell seed K m c) = true := by
  have h : slotF (trialCell seed K m c) = some (.enc K.1 K.2.1 K.2.2) :=
    slotOfInput_pkOfInput (slotOf_cell ⟨0, 0, seed⟩ 0 (s := .enc K.1 K.2.1 K.2.2) trivial
      (m, BitVec.ofNat counterBits c))
  rw [isEncCell, h]

/-- **No table cell is an encoding cell.** -/
theorem isEncCell_cellOf (S0 : MasterSeed) (v : QTable) (p : Pos) :
    isEncCell (cellOf S0 p v) = false := by
  rw [isEncCell, slotF_cellOf]
  have h := posSlot_ne_enc v p.1
  generalize posSlot v p.1 = s at h ⊢
  cases s <;> first | rfl | exact absurd rfl (h _ _ _)

/-- A read at an encoding cell. -/
def encRead {M' : Type} : HwRead PairOut HashDomain M' → Bool
  | .readH z _ => isEncCell z
  | _ => false

end enc

/-! ## Charges of the calls by kind -/

section charges

variable {M : Type} {L : LocalSig.{u, v}} {Ω : QReg → Type w}

variable (M) in
/-- A charge on the template ports of `n` users by kind: `a` per sponge call, `b` per read at a
cell other than an encoding cell, `b'` per read at an encoding cell, `c` per program call, `d`
per reveal. -/
def tChargeSN (a b b' c d : ℕ) : (XSpecSN M n).Port → ℕ
  | .inl (.inl (.inl _)) => a
  | .inl (.inl (.inr r)) => if encRead r.1 then b' else b
  | .inl (.inr _) => c
  | .inr _ => d

variable (M) in
/-- The same charge on runtime 2 with record ports (a reveal realizes as a record call). -/
def rChargeSN (a b b' c d : ℕ) : (recHwSpec PairOut HashDomain (TPosN n) M).Port → ℕ
  | .inl (.inl (.inl _)) => a
  | .inl (.inl (.inr r)) => if encRead r then b' else b
  | .inl (.inr _) => c
  | .inr _ => d

variable (M) in
/-- The charge on runtime 1's ports: `a` per sponge call, `b` per read at a cell other than an
encoding cell, `b'` per read at an encoding cell. -/
def rdChargeSN (a b b' : ℕ) : (hwReadSpec PairOut HashDomain M).Port → ℕ
  | .inl _ => a
  | .inr r => if encRead r then b' else b

variable (M) in
/-- The reads at cells other than encoding cells: the ports of the read mass. -/
def readQSN : (recHwSpec PairOut HashDomain (TPosN n) M).Port → Bool
  | .inl (.inl (.inr r)) => !encRead r
  | _ => false

variable (a b b' c d : ℕ)

/-- **Realizing keeps the charges by kind.** -/
theorem isChargeBound_realizeTSN (θ : TValsN n) {A : QReg}
    {y : QuantumComp L (XSpecSN M n) Ω A} {k : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge (tChargeSN M a b b' c d)) k) :
    IFreeM.IsChargeBound (realizeT θ y) (portCharge (rChargeSN M a b b' c d)) k := by
  refine IFreeM.IsChargeBound.mapLens (tmplLens (good := goodQN) (M := M) θ) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (rChargeSN M a b b' c d) s
      ((tmplLens (good := goodQN) (M := M) θ).toFunA s cmd)) =
      portCharge (tChargeSN M a b b' c d) := by
    funext s cmd
    rcases cmd with o | ⟨((i | r) | p) | T, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

theorem isChargeBound_readLiftSN {A : QReg}
    {y : QuantumComp L (hwReadSpec PairOut HashDomain M) Ω A} {k : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge (rdChargeSN M a b b')) k) :
    IFreeM.IsChargeBound (readLift (goodQN (n := n)) y) (portCharge (tChargeSN M a b b' c d))
      k := by
  refine IFreeM.IsChargeBound.mapLens (readLens (goodQN (n := n))) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (tChargeSN M a b b' c d) s
      ((readLens (goodQN (n := n))).toFunA s cmd)) = portCharge (rdChargeSN M a b b') := by
    funext s cmd
    rcases cmd with o | ⟨i | r, E, ℓ⟩
    · rfl
    · rfl
    · cases r <;> rfl
  rw [he]
  exact h

theorem chg_revealThenSN {B B' : QReg} {α : Type} (T : Finset (TPosN n))
    (k : RevealVals (TValN n) T × (Finset (TPosN n) × M) → QComp (XSpecSN M n) B B' α) {m : ℕ}
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge (tChargeSN M a b b' c d)) m) :
    IFreeM.IsChargeBound (revealThen goodQN T k) (portCharge (tChargeSN M a b b' c d))
      (d + m) := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.le_add_right d m, fun r ↦ ?_⟩
  simp only [tChargeSN, Nat.add_sub_cancel_left]
  exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₁ := 0)
    (chg_act _ _ 0) fun _ ↦ hk r) (Nat.zero_add m).le

theorem chg_progThenSN {B B' : QReg} {α : Type}
    (p : LazyProg PairOut HashDomain (TPosN n) (TValN n)) (hp : goodQN p)
    (k : QComp (XSpecSN M n) B B' α) {m : ℕ}
    (hk : IFreeM.IsChargeBound k (portCharge (tChargeSN M a b b' c d)) m) :
    IFreeM.IsChargeBound (progThen p hp k) (portCharge (tChargeSN M a b b' c d)) (c + m) := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.le_add_right c m, fun r ↦ ?_⟩
  simp only [tChargeSN, Nat.add_sub_cancel_left]
  exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₁ := 0)
    (chg_act _ _ 0) fun _ ↦ hk) (Nat.zero_add m).le

theorem chg_progPosN (i : Fin n) (B : QReg) (ps : List Pos) :
    IFreeM.IsChargeBound (progPosN M i B ps) (portCharge (tChargeSN M a b b' c d))
      (c * ps.length) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    refine IFreeM.IsChargeBound.mono (chg_progThenSN a b b' c d (progTN i p) trivial _ ih)
      (le_of_eq ?_)
    rw [List.length_cons, Nat.mul_succ, Nat.add_comm]

theorem chg_readCallSN (r : HwRead PairOut HashDomain M) (B : QReg) :
    IFreeM.IsChargeBound (readCall r B) (portCharge (rdChargeSN M a b b'))
      (if encRead r then b' else b) := by
  unfold readCall
  exact FreeM₂.isChargeBound_bind (n₂ := 0)
    ((IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨le_rfl, fun _ ↦ trivial⟩) fun _ ↦
      FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ trivial

/-- **A computation through read ports**: one read per call of `H` of a path bound, at most
`max b b'` each. -/
theorem chg_readsProgramSN (B : QReg) {α : Type} {x : OracleComp RomOracles α} {k : ℕ}
    (h : Common.QueryCostAtMost x hashCallCost k) :
    IFreeM.IsChargeBound (readsProgram M B x) (portCharge (rdChargeSN M a b b'))
      (max b b' * k) := by
  refine (chg_readsProgram (M := M) a (max b b') B h).mono_charge fun s cmd ↦ ?_
  rcases cmd with o | ⟨i | r, E, ℓ⟩
  · exact le_rfl
  · exact le_rfl
  · show (if encRead r then b' else b) ≤ max b b'
    split
    · exact le_max_right b b'
    · exact le_max_left b b'

/-- **The counter search**: one read of an encoding cell per trial. -/
theorem chg_grindTSN (u : TrialUpd M) (seed : PublicParameter) (B : QReg) (K : Key)
    (m : Digest) : ∀ k cnt, IFreeM.IsChargeBound (grindT M u seed B K m k cnt)
      (portCharge (rdChargeSN M a b b')) (k * b')
  | 0, _ => trivial
  | k + 1, cnt => by
    have hr := chg_readCallSN a b b' (.readH (trialCell seed K m cnt)
      (u K (trialCell seed K m cnt))) B
    rw [show encRead (HwRead.readH (trialCell seed K m cnt) (u K (trialCell seed K m cnt))) =
      true from isEncCell_trialCell seed K m cnt, ite_eq_left rfl] at hr
    rw [grindT]
    refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := k * b') hr fun r ↦ ?_)
      (le_of_eq (by ring))
    generalize TargetSum.decodeDigest (truncateHash (r.1.getD 0).1) = dd
    cases dd with
    | none => exact chg_grindTSN u seed B K m k (cnt + 1)
    | some x => trivial

theorem chg_forsOpenTN (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) :
    IFreeM.IsChargeBound (forsOpenTN M i B idx lv) (portCharge (tChargeSN M a b b' c d))
      (d + c * 265) := by
  refine chg_revealThenSN a b b' c d _ _ fun _ ↦ IFreeM.IsChargeBound.mono
    (FreeM₂.isChargeBound_bind (n₂ := 0) (chg_progPosN a b b' c d i B _) fun _ ↦ trivial) ?_
  rw [Nat.add_zero]
  exact Nat.mul_le_mul_left c (length_forsPos_le idx lv)

theorem chg_publishTN (i : Fin n) (B : QReg) (K : Key) (cnt : EncodingCounter) (x : Encoding) :
    IFreeM.IsChargeBound (publishTN M i B K cnt x) (portCharge (tChargeSN M a b b' c d))
      (d + c * 203) := by
  refine chg_revealThenSN a b b' c d _ _ fun _ ↦ IFreeM.IsChargeBound.mono
    (FreeM₂.isChargeBound_bind (n₂ := 0) (chg_progPosN a b b' c d i B _) fun _ ↦ trivial) ?_
  rw [Nat.add_zero]
  exact Nat.mul_le_mul_left c (length_layerPos_le K x)

theorem chg_publishAllTN (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (R : Randomizer) (g₀ g₁ g₂ : SelS) :
    IFreeM.IsChargeBound (publishAllTN M i B idx lv R g₀ g₁ g₂)
      (portCharge (tChargeSN M a b b' c d)) (pubCallsQ c d) := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try trivial
  simp only [publishAllTN]
  refine FreeM₂.isChargeBound_bind (chg_forsOpenTN a b b' c d i B _ _) fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (chg_publishTN a b b' c d i B _ _ _) fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (chg_publishTN a b b' c d i B _ _ _) fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (n₂ := 0) (chg_publishTN a b b' c d i B _ _ _) fun _ ↦ ?_
  trivial

variable (upd : Fin n → TrialUpd M)

theorem chg_selectTN (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key) :
    IFreeM.IsChargeBound (selectTN M upd i seed B K) (portCharge (tChargeSN M a b b' c d))
      (d + encodingAttemptLimit * b') :=
  chg_revealThenSN a b b' c d _ _ fun _ ↦
    isChargeBound_readLiftSN a b b' c d (chg_grindTSN a b b' (upd i) seed B K _ _ 0)

/-- **A key's selection or its memo**: no call on a memo hit. -/
theorem chg_selOrMemoTN (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key)
    (o : Option SelS) :
    IFreeM.IsChargeBound (selOrMemoTN M upd i seed B K o) (portCharge (tChargeSN M a b b' c d))
      (d + encodingAttemptLimit * b') := by
  cases o with
  | none => exact chg_selectTN a b b' c d upd i seed B K
  | some _ => trivial

/-- The calls of one signature by kind, whatever the memo: two reveals, the digest's program
call, three counter searches (a reveal and `encodingAttemptLimit` encoding reads each) and the
publication. -/
def signCallsSN (b' c d : ℕ) : ℕ :=
  2 * d + c + 3 * (d + encodingAttemptLimit * b') + pubCallsQ c d

/-- **A signature's calls**, for every digest policy and memo. -/
theorem chg_signTN (pols : Fin n → DigestPolicy) (i : Fin n) (B : QReg) (msg : Message)
    (h : KeyMemo) :
    IFreeM.IsChargeBound (signTN M upd pols i B msg h) (portCharge (tChargeSN M a b b' c d))
      (signCallsSN b' c d) := by
  unfold signTN
  refine IFreeM.IsChargeBound.mono (chg_revealThenSN a b b' c d _ _ fun r₁ ↦
    chg_revealThenSN a b b' c d _ _ fun r₂ ↦ chg_progThenSN a b b' c d _ trivial _ <|
      FreeM₂.isChargeBound_bind (chg_selOrMemoTN a b b' c d upd i _ B _ _) fun _ ↦
      FreeM₂.isChargeBound_bind (chg_selOrMemoTN a b b' c d upd i _ B _ _) fun _ ↦
      FreeM₂.isChargeBound_bind (chg_selOrMemoTN a b b' c d upd i _ B _ _) fun _ ↦
      chg_map _ _ (chg_publishAllTN a b b' c d i B _ _ _ _ _ _)) (le_of_eq ?_)
  unfold signCallsSN
  ring

/-- A hash call of the adversary, regrouped and lifted, is one call of `F`. -/
theorem chg_hashCmdSN (A : QReg)
    (cmd : QuantumComp.Cmd LocalSig.instruments.{0} (muAdvSpec n Message (Option Signature)) A)
    {k : ℕ} (hq : QuantumComp.IsQueryBound (muChallenge sphincsRom (noKeysS (n := n)) A cmd)
      fun _ ↦ k) :
    IFreeM.IsChargeBound (readLift (goodQN (n := n)) ((liftH (regroupCalls hmsgRoute
      (muChallenge sphincsRom (noKeysS (n := n)) A cmd))).liftOrdinary
        (t := hwReadCmdSpec PairOut HashDomain M))) (portCharge (tChargeSN M a b b' c d))
      (a * k) := by
  refine isChargeBound_readLiftSN a b b' c d (isChargeBound_liftOrdinary (rdChargeSN M a b b') ?_)
  refine (isChargeBound_liftH_iff _ _ _).mpr ?_
  have h := ((isQueryBound_regroupCalls hmsgRoute hq) ()).mul a
  have he : (portCharge fun _ ↦ (fun i ↦ rdChargeSN M a b b' (.inl i)) SpongePort.h) =
      fun s cmd ↦ a * QuantumComp.queryCharge (L := LocalSig.instruments.{0})
        (spec := qromSpec HashDomain PairOut) () s cmd := by
    funext s cmd
    rcases cmd with o | ⟨i, E, ℓ⟩
    · simp [QuantumComp.queryCharge, portCharge]
    · simp [QuantumComp.queryCharge, portCharge, rdChargeSN]
  rw [he]
  exact h

/-- **The challenger's calls** per command: a local operation none, a hash call one sponge call,
a signing request a signature's calls. -/
theorem chg_challengeTN (pols : Fin n → DigestPolicy) (A : QReg)
    (cmd : QuantumComp.Cmd LocalSig.instruments.{0} (memoSpecS n) A) :
    IFreeM.IsChargeBound (challengeTN M upd pols A cmd) (portCharge (tChargeSN M a b b' c d))
      (cmdCharge (memoChargeS a (signCallsSN b' c d)) A cmd) := by
  rcases cmd with o | ⟨_ | ⟨i, q⟩, E, ℓ⟩
  · refine IFreeM.IsChargeBound.mono (chg_hashCmdSN a b b' c d A (.prim o) (k := 0) fun _ ↦
      (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨by simp [QuantumComp.queryCharge],
        fun _ ↦ trivial⟩) ?_
    simp [cmdCharge]
  · refine IFreeM.IsChargeBound.mono (chg_hashCmdSN a b b' c d A (.query .hash E ℓ) (k := 1)
      fun _ ↦ (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨by simp [QuantumComp.queryCharge],
        fun _ ↦ trivial⟩) ?_
    simp [cmdCharge, memoChargeS]
  · refine IFreeM.IsChargeBound.mono (IFreeM.isChargeBound_bind (FreeM₂.isChargeBound_bind
      (n₁ := 0) (chg_act _ _ 0) fun _ ↦
        chg_signTN a b b' c d upd pols i _ q.1 q.2) fun _ _ ↦ IFreeM.isChargeBound_pure _ 0) ?_
    simp [cmdCharge, memoChargeS]

/-- **The challenge prefix's calls**: the public keys' reveal, the challenged memo transform. -/
theorem chg_prefixTN (pols : Fin n → DigestPolicy) (A : MuAdversaryS n) {q total : ℕ}
    (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
    (hsign : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total) :
    IFreeM.IsChargeBound (prefixTN M upd pols A) (portCharge (tChargeSN M a b b' c d))
      (d + ((a * q + signCallsSN b' c d * total) + 0)) := by
  refine chg_revealThenSN a b b' c d _ _ fun r₀ ↦ ?_
  have hx := isChargeBound_memoFromS_memoChargeS (withMuSignLog (A (pksT r₀.1)))
    (fun _ _ ↦ none) (isChargeBound_withMuSignLog (hhash _))
    (isChargeBound_withMuSignLog (hsign _)) a (signCallsSN b' c d)
  have hc := IFreeM.IsChargeBound.substitute (challengeTN M upd pols)
    (chg_challengeTN a b b' c d upd pols) hx
  exact FreeM₂.isChargeBound_bind hc fun _ ↦ trivial

/-- **The verification's calls**: one read per hash call of the verifier. -/
theorem chg_verifyTN (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (x : (Fin n → PublicKey) × MuRunS n) :
    IFreeM.IsChargeBound (verifyTN M valid x) (portCharge (tChargeSN M a b b' c d))
      (max b b' * verifyCalls + 0) := by
  unfold verifyTN
  rw [readsThenTN_eq]
  exact FreeM₂.isChargeBound_bind (isChargeBound_readLiftSN a b b' c d
    (chg_map _ Prod.fst (chg_readsProgramSN a b b' _ (verify_hashCalls _ _)))) fun _ ↦ trivial

/-- The calls of the multi-user game by kind: the public keys' reveal, `a` per hash call, a
signature's calls per request, the verification's reads. -/
def gameCallsSN (a b b' c d q total : ℕ) : ℕ :=
  d + (a * q + signCallsSN b' c d * total) + max b b' * verifyCalls

/-- **The realized game's calls by kind**, for an adversary making at most `q` hash calls and at
most `total` signing requests on every path, at all hidden values. -/
theorem chg_realizeT_muGameT (pols : Fin n → DigestPolicy)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
    {q total : ℕ} (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
    (hsign : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total)
    (θ : TValsN n) :
    IFreeM.IsChargeBound (realizeT θ (muGameT M upd pols valid A))
      (portCharge (rChargeSN M a b b' c d)) (gameCallsSN a b b' c d q total) := by
  refine isChargeBound_realizeTSN a b b' c d θ ?_
  rw [muGameT_eq_prefixTN_bind]
  exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind
    (chg_prefixTN a b b' c d upd pols A hhash hsign) fun x ↦ chg_verifyTN a b b' c d valid x)
      (le_of_eq (by unfold gameCallsSN; omega))

/-- **The realized prefix's calls by kind.** -/
theorem chg_realizeT_prefixTN (pols : Fin n → DigestPolicy) (A : MuAdversaryS n) {q total : ℕ}
    (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
    (hsign : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total)
    (θ : TValsN n) :
    IFreeM.IsChargeBound (realizeT θ (prefixTN M upd pols A))
      (portCharge (rChargeSN M a b b' c d)) (gameCallsSN a b b' c d q total) :=
  isChargeBound_realizeTSN a b b' c d θ (IFreeM.IsChargeBound.mono
    (chg_prefixTN a b b' c d upd pols A hhash hsign) (by unfold gameCallsSN; omega))

end charges

/-! ## The call counts -/

section counts

/-- **The classical calls of the game**: the public keys' reveal; per signing request two
reveals, the digest's program call, three full counter searches (a reveal and `2 ^ 32` reads
each) and the publication; the verification's reads. -/
def clsCapSN (total : ℕ) : ℕ :=
  gameCallsSN 0 1 1 1 1 0 total

theorem clsCapSN_eq (total : ℕ) : clsCapSN total = 1 + (3 * 2 ^ 32 + 884) * total + 879 := by
  simp only [clsCapSN, gameCallsSN, signCallsSN, pubCallsQ, verifyCalls_eq, encodingAttemptLimit,
    max_self]
  ring

theorem clsCapSN_le {total : ℕ} (ht : total ≤ 2 ^ 64) : clsCapSN total ≤ 2 ^ 98 := by
  rw [clsCapSN_eq]
  have h := Nat.mul_le_mul_left (3 * 2 ^ 32 + 884) ht
  norm_num at h ⊢
  omega

/-- **The program calls of the game**: the digest's and the publication's per request. -/
def progCapSN (total : ℕ) : ℕ :=
  signCallsSN 0 1 0 * total

theorem progCapSN_eq (total : ℕ) : progCapSN total = 875 * total := by
  simp [progCapSN, signCallsSN, pubCallsQ]

theorem gameCallsSN_adv (q total : ℕ) : gameCallsSN 1 0 0 0 0 q total = q := by
  simp [gameCallsSN, signCallsSN, pubCallsQ]

theorem gameCallsSN_cls (q total : ℕ) : gameCallsSN 0 1 1 1 1 q total = clsCapSN total := by
  simp [clsCapSN, gameCallsSN]

theorem gameCallsSN_prog (q total : ℕ) : gameCallsSN 0 0 0 1 0 q total = progCapSN total := by
  simp [gameCallsSN, progCapSN]

theorem gameCallsSN_readQ (q total : ℕ) : gameCallsSN 0 1 0 0 0 q total = verifyCalls := by
  simp [gameCallsSN, signCallsSN, pubCallsQ]

variable {M : Type}

theorem advCharge_eqSN :
    (fun i ↦ if extCls PairOut HashDomain (Finset (TPosN n) × M) (recSpec (TPosN n) M) i then 0
      else 1) = rChargeSN M 1 0 0 0 0 := by
  funext i
  rcases i with ((i | r) | p) | T
  · rfl
  · exact (ite_self 0).symm
  · rfl
  · rfl

theorem clsCharge_eqSN :
    (fun i ↦ if extCls PairOut HashDomain (Finset (TPosN n) × M) (recSpec (TPosN n) M) i then 1
      else 0) = rChargeSN M 0 1 1 1 1 := by
  funext i
  rcases i with ((i | r) | p) | T
  · rfl
  · exact (ite_self 1).symm
  · rfl
  · rfl

theorem progCharge_eqSN :
    extProgCharge PairOut HashDomain (Finset (TPosN n) × M) (recSpec (TPosN n) M) =
      rChargeSN M 0 0 0 1 0 := by
  funext i
  rcases i with ((i | r) | p) | T
  · rfl
  · exact (ite_self 0).symm
  · rfl
  · rfl

theorem readQCharge_eqSN :
    (fun i ↦ if readQSN M (n := n) i = true then 1 else 0) = rChargeSN M 0 1 0 0 0 := by
  funext i
  rcases i with ((i | r) | p) | T
  · rfl
  · simp only [readQSN, rChargeSN]
    rcases Bool.eq_false_or_eq_true (encRead r) with h | h <;> simp [h]
  · rfl
  · rfl

variable (upd : Fin n → TrialUpd M) (pols : Fin n → DigestPolicy)
  (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n) {q total : ℕ}
  (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
  (hsign : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total)
include hhash hsign

/-- **The game's sponge calls**: at most `q`. -/
theorem advCalls_muGameQS (θ : TValsN n) :
    IFreeM.IsChargeBound (realizeT θ (muGameT M upd pols valid A))
      (portCharge fun i ↦ if extCls PairOut HashDomain (Finset (TPosN n) × M)
        (recSpec (TPosN n) M) i then 0 else 1) q := by
  rw [advCharge_eqSN]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_muGameT 1 0 0 0 0 upd pols valid A hhash hsign θ)
    (le_of_eq (gameCallsSN_adv q total))

/-- **The game's classical calls** (reads, program and record calls): at most `clsCapSN`. -/
theorem clsCalls_muGameQS (θ : TValsN n) :
    IFreeM.IsChargeBound (realizeT θ (muGameT M upd pols valid A))
      (portCharge fun i ↦ if extCls PairOut HashDomain (Finset (TPosN n) × M)
        (recSpec (TPosN n) M) i then 1 else 0) (clsCapSN total) := by
  rw [clsCharge_eqSN]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_muGameT 0 1 1 1 1 upd pols valid A hhash hsign θ)
    (le_of_eq (gameCallsSN_cls q total))

/-- **The game's program calls**: at most `progCapSN`. -/
theorem progCalls_muGameQS (θ : TValsN n) :
    IFreeM.IsChargeBound (realizeT θ (muGameT M upd pols valid A))
      (portCharge (extProgCharge PairOut HashDomain (Finset (TPosN n) × M)
        (recSpec (TPosN n) M))) (progCapSN total) := by
  rw [progCharge_eqSN]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_muGameT 0 0 0 1 0 upd pols valid A hhash hsign θ)
    (le_of_eq (gameCallsSN_prog q total))

/-- **The game's reads at cells other than encoding cells**: the verification's, at most
`verifyCalls`. -/
theorem readQCalls_muGameQS (θ : TValsN n) :
    IFreeM.IsChargeBound (realizeT θ (muGameT M upd pols valid A))
      (portCharge fun i ↦ if readQSN M (n := n) i = true then 1 else 0) verifyCalls := by
  rw [readQCharge_eqSN]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_muGameT 0 1 0 0 0 upd pols valid A hhash hsign θ)
    (le_of_eq (gameCallsSN_readQ q total))

omit valid in
theorem advCalls_prefixQS (θ : TValsN n) :
    IFreeM.IsChargeBound (realizeT θ (prefixTN M upd pols A))
      (portCharge fun i ↦ if extCls PairOut HashDomain (Finset (TPosN n) × M)
        (recSpec (TPosN n) M) i then 0 else 1) q := by
  rw [advCharge_eqSN]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_prefixTN 1 0 0 0 0 upd pols A hhash hsign θ)
    (le_of_eq (gameCallsSN_adv q total))

omit valid in
theorem clsCalls_prefixQS (θ : TValsN n) :
    IFreeM.IsChargeBound (realizeT θ (prefixTN M upd pols A))
      (portCharge fun i ↦ if extCls PairOut HashDomain (Finset (TPosN n) × M)
        (recSpec (TPosN n) M) i then 1 else 0) (clsCapSN total) := by
  rw [clsCharge_eqSN]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_prefixTN 0 1 1 1 1 upd pols A hhash hsign θ)
    (le_of_eq (gameCallsSN_cls q total))

omit valid in
theorem progCalls_prefixQS (θ : TValsN n) :
    IFreeM.IsChargeBound (realizeT θ (prefixTN M upd pols A))
      (portCharge (extProgCharge PairOut HashDomain (Finset (TPosN n) × M)
        (recSpec (TPosN n) M))) (progCapSN total) := by
  rw [progCharge_eqSN]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_prefixTN 0 0 0 1 0 upd pols A hhash hsign θ)
    (le_of_eq (gameCallsSN_prog q total))

omit valid in
theorem readQCalls_prefixQS (θ : TValsN n) :
    IFreeM.IsChargeBound (realizeT θ (prefixTN M upd pols A))
      (portCharge fun i ↦ if readQSN M (n := n) i = true then 1 else 0) verifyCalls := by
  rw [readQCharge_eqSN]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_prefixTN 0 1 0 0 0 upd pols A hhash hsign θ)
    (le_of_eq (gameCallsSN_readQ q total))

end counts

end Quantum.Qrom.Sphincs.Multi

end
