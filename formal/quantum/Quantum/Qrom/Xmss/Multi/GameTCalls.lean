module

public import Quantum.Qrom.Xmss.Multi.Template
public import Quantum.Qrom.Xmss.GameTCalls
public import Quantum.Cost.Charge

@[expose] public section

/-!
# The calls of the realized multi-user runtime-2 template game in the QROM

The `n`-user analog of `Quantum.Qrom.Xmss.GameTCalls`, for `realizeT θ (muGameT M upd valid A)`.
The sources of the cells (`srcOf`, `mem_layerPos_of_srcOf_mem`), the verifier's calls
(`verifyCalls`) and the charges of runtime 1 (`rdChargeQ`, `chg_grindT`, `chg_readsProgram`) are
the single-user ones.

* **The source invariant of `n` users** (`SrcInvN θ`): every position of user `i` whose source
  `(i, srcOf p)` is revealed has user `i`'s cell hardwired. `PendInvN θ C` with pending cells `C`,
  `HPendN` (templates keeping it), `hPend_muGameT`; `forallQueries_muGameQN`,
  `forallQueries_prefixQN`: Masses' `hinv` for any ports `Q` other than the program ports, from
  states with an empty memory label.
* **Charges by kind** (`tChargeQN`, `rChargeQN`: `a` per sponge call, `b` per read at a cell other
  than a message digest, `b'` per read at a message digest, `c` per program call, `d` per reveal
  or record): `chg_selectTN`, `chg_publishTN`, `chg_topTN` (no call on a memo hit), `chg_signTN`
  (`hitCallsQ` per request, `missCallsQ` more without a memoized top selection).
* **The adversary's side**: `memoCharge α βh βm` on the memo ports, `chg_challengeTN` per command.
  `memoFrom` keeps the hash and signing charges (`isChargeBound_memoFrom_of_le`); from the empty
  memo it asks each user's top key without a memoized selection at most once, so at most
  `min total (n * 2 ^ 16)` times (`isChargeBound_missCharge_memoFrom_empty`).
* **Totals**: `chg_realizeT_muGameT`, `chg_realizeT_prefixTN` (`gameCallsQN`). The counts:
  `advCalls_muGameQ` (`q` sponge calls), `clsCalls_muGameQ` (`clsCapN`), `progCalls_muGameQ`
  (`progCapN`), `readQCalls_muGameQ` (`verifyCalls`), and the same for the prefix.
* `keepsLab_muGameQ`, `keepsLab_prefixQN`: the reads keep the memory label.
-/

open Matrix IPFunctor OracleComp OracleSpec
open scoped ENNReal Kronecker

universe u v w w₁

namespace Quantum.Qrom.Xmss.Multi

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open LeanXmss HashSig
open Quantum.Xmss.Assembly (tmplSpec recHwSpec recSpec runtimeR realizeT revealThen progThen
  readLift readLiftQ RevealVals)
open Quantum.Qrom.SufCma.Multi (MuPort muAdvSpec muChallenge withMuSignLog cmdCharge hashCharge
  signCharge isChargeBound_withMuSignLog)

variable {n : ℕ}

-- The adversary's commands without and with the memo, as indexed polynomial functors.
set_option quotPrecheck false in
local notation "MuP" n => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (muAdvSpec n SigningRequest (Option Signature))

set_option quotPrecheck false in
local notation "MemoP" n => QuantumComp.toIPFunctor LocalSig.instruments.{0} (memoSpec n)

/-! ## The source invariant of `n` users -/

section pending

variable {M : Type}

/-- **The source invariant of `n` users** at the hidden values `θ`: every position of user `i`
whose source coordinate is revealed has user `i`'s cell hardwired. -/
def SrcInvN (θ : HPosN n → Digest) (r : HwReg HashOutput HashDomain (Finset (HPosN n) × M)) :
    Prop :=
  ∀ i p, (i, srcOf p) ∈ r.2.2.1 → r.2.1.1 (cellOf (seedsOf θ i) p (tabOf (userOf θ i))) ≠ none

/-- **The source invariant of `n` users with pending cells `C`**: a position of user `i` whose
source is revealed has user `i`'s cell hardwired or pending. -/
def PendInvN (θ : HPosN n → Digest) (C : Set HashDomain)
    (r : HwReg HashOutput HashDomain (Finset (HPosN n) × M)) : Prop :=
  ∀ i p, (i, srcOf p) ∈ r.2.2.1 →
    r.2.1.1 (cellOf (seedsOf θ i) p (tabOf (userOf θ i))) ≠ none ∨
      cellOf (seedsOf θ i) p (tabOf (userOf θ i)) ∈ C

/-- The cells whose source a reveal of `T` reveals. -/
def revealCellsN (θ : HPosN n → Digest) (T : Finset (HPosN n)) : Set HashDomain :=
  {z | ∃ i p, (i, srcOf p) ∈ T ∧ cellOf (seedsOf θ i) p (tabOf (userOf θ i)) = z}

variable {θ : HPosN n → Digest}

theorem pendInvN_mono {C C' : Set HashDomain} (h : C ⊆ C')
    {r : HwReg HashOutput HashDomain (Finset (HPosN n) × M)} (hr : PendInvN θ C r) :
    PendInvN θ C' r :=
  fun i p hp ↦ (hr i p hp).imp_right fun hc ↦ h hc

theorem pendInvN_of_eq {C : Set HashDomain}
    {r r' : HwReg HashOutput HashDomain (Finset (HPosN n) × M)}
    (h1 : r'.2.1 = r.2.1) (h2 : r'.2.2.1 = r.2.2.1) (hr : PendInvN θ C r) : PendInvN θ C r' := by
  intro i p hp
  rw [h1]
  exact hr i p (h2 ▸ hp)

theorem pendInvN_of_label_empty {C : Set HashDomain}
    {r : HwReg HashOutput HashDomain (Finset (HPosN n) × M)} (h : r.2.2.1 = ∅) :
    PendInvN θ C r := by
  intro i p hp
  rw [h] at hp
  exact absurd hp (Finset.notMem_empty _)

/-- A program port hardwires its cell and keeps the others: it leaves the pending set. -/
theorem pendInvN_prog {C : Set HashDomain} (c : HwProg HashOutput HashDomain)
    {r r' : HwReg HashOutput HashDomain (Finset (HPosN n) × M)}
    (h : r'.2 = (progUpdate c r.2.1, r.2.2)) (hr : PendInvN θ C r) :
    PendInvN θ (C \ progCellH c) r' := by
  intro i p hp
  rw [h] at hp ⊢
  rcases hr i p hp with hc | hc
  · exact .inl (progUpdate_ne_none c _ (.inl hc))
  · by_cases hz : cellOf (seedsOf θ i) p (tabOf (userOf θ i)) ∈ progCellH c
    · exact .inl (progUpdate_ne_none c _ (.inr hz))
    · exact .inr ⟨hc, hz⟩

/-- A reveal of `T` adds the cells whose source it reveals to the pending set. -/
theorem pendInvN_reveal {C : Set HashDomain} (T : Finset (HPosN n))
    {r r' : HwReg HashOutput HashDomain (Finset (HPosN n) × M)}
    (h : r'.2 = (r.2.1, (r.2.2.1 ∪ T, r.2.2.2))) (hr : PendInvN θ C r) :
    PendInvN θ (C ∪ revealCellsN θ T) r' := by
  intro i p hp
  rw [h] at hp ⊢
  rcases Finset.mem_union.1 hp with hp | hp
  · exact (hr i p hp).imp_right Or.inl
  · exact .inr (.inr ⟨i, p, hp, rfl⟩)

theorem srcInvN_of_pendInvN {r : HwReg HashOutput HashDomain (Finset (HPosN n) × M)}
    (h : PendInvN θ ∅ r) : SrcInvN θ r :=
  fun i p hp ↦ (h i p hp).resolve_right (Set.notMem_empty _)

variable (θ)

/-- A reveal of user `i`'s coordinates makes pending at most user `i`'s cells whose source it
reveals. -/
theorem revealCellsN_atU (i : Fin n) (T : Finset HPos) :
    revealCellsN θ (atU i T) ⊆ revealCells (userOf θ i) T := by
  rintro z ⟨j, p, hp, rfl⟩
  obtain ⟨rfl, hs⟩ := mem_atU.1 hp
  exact ⟨p, hs, rfl⟩

theorem revealCellsN_pkRevealN : revealCellsN θ pkRevealN ⊆ ∅ := by
  rintro z ⟨i, p, hp, -⟩
  rw [pkRevealN, Finset.mem_product] at hp
  exact srcOf_not_mem_pkReveal p hp.2

theorem revealCellsN_rootReveal (i : Fin n) (r : SigningRequest) :
    revealCellsN θ (atU i (rootReveal r)) ⊆ ∅ :=
  (revealCellsN_atU θ i _).trans (revealCells_rootReveal (userOf θ i) r)

theorem revealCellsN_rndBottom (i : Fin n) (e : KeyIndex) (m : Message) :
    revealCellsN θ (atU i {loC (.rndBottom e m)}) ⊆ ∅ :=
  (revealCellsN_atU θ i _).trans (revealCells_rndBottom (userOf θ i) e m)

theorem revealCellsN_rndTop (i : Fin n) (e : KeyIndex) (d : Digest) :
    revealCellsN θ (atU i {loC (.rndTop e d)}) ⊆ ∅ :=
  (revealCellsN_atU θ i _).trans (revealCells_rndTop (userOf θ i) e d)

/-- The cells a layer signature's reveal of user `i` makes pending are those it programs. -/
theorem revealCellsN_layerReveal (i : Fin n) (l : Layer) (e : KeyIndex) (x : Encoding) :
    revealCellsN θ (atU i (layerReveal l e x)) ⊆
      {z | ∃ q ∈ layerPos l e x, z ∈ progCellH ((progTN i q).realize θ)} := by
  rintro z ⟨j, p, hp, rfl⟩
  obtain ⟨rfl, hs⟩ := mem_atU.1 hp
  have hq := mem_layerPos_of_srcOf_mem hs
  refine ⟨p, hq, ?_⟩
  rw [realize_progTN (isStruct_of_mem_layerPos hq) _ (seedsOf θ _) θ]
  exact Set.mem_singleton _

end pending

/-! ## Templates that keep the source invariant of `n` users

`HPendN θ y C C'`: run from states on the pending invariant `C`, the template `y` calls the
sponge, read and reveal ports with nothing pending, its reads keep the label, a program port
leaves the pending set, a reveal of `T` adds the cells whose source it reveals; it ends on `C'`. -/

section hp

variable {M : Type} {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- The condition of `HPendN` on the pending set before a call. -/
def portPreQN : (XSpecN M n).Port → Set HashDomain → Prop
  | .inl (.inl (.inl _)), C => C = ∅
  | .inl (.inl (.inr c)), C => C = ∅ ∧ ReadKeeps c.1
  | .inl (.inr _), _ => True
  | .inr _, C => C = ∅

/-- The pending set after a call. -/
def portPostQN (θ : HPosN n → Digest) : (XSpecN M n).Port → Set HashDomain → Set HashDomain
  | .inl (.inl (.inl _)), C => C
  | .inl (.inl (.inr _)), C => C
  | .inl (.inr p), C => C \ progCellH (p.1.realize θ)
  | .inr T, C => C ∪ revealCellsN θ T

/-- The condition before a command. -/
def cmdPreQN {A : QReg} : QuantumComp.Cmd L (XSpecN M n) A → Set HashDomain → Prop
  | .prim _, _ => True
  | .query i _ _, C => portPreQN i C

/-- The pending set after a command. -/
def cmdPostQN (θ : HPosN n → Digest) {A : QReg} :
    QuantumComp.Cmd L (XSpecN M n) A → Set HashDomain → Set HashDomain
  | .prim _, C => C
  | .query i _ _, C => portPostQN θ i C

/-- **A template that keeps the source invariant of `n` users**, from the pending set `C` to
`C'`. -/
def HPendN (θ : HPosN n → Digest) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor L (XSpecN M n)) Ω A → Set HashDomain →
      Set HashDomain → Prop
  | _, .pure _, C, C' => C ⊆ C'
  | _, .liftBind c next, C, C' => cmdPreQN c C ∧ ∀ b, HPendN θ (next b) (cmdPostQN θ c C) C'

theorem cmdPreQN_anti {A : QReg} (c : QuantumComp.Cmd L (XSpecN M n) A) {C D : Set HashDomain}
    (hD : D ⊆ C) (h : cmdPreQN c C) : cmdPreQN c D := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · trivial
  · exact Set.subset_empty_iff.1 (h ▸ hD)
  · exact ⟨Set.subset_empty_iff.1 (h.1 ▸ hD), h.2⟩
  · trivial
  · exact Set.subset_empty_iff.1 (h ▸ hD)

theorem cmdPostQN_mono (θ : HPosN n → Digest) {A : QReg} (c : QuantumComp.Cmd L (XSpecN M n) A)
    {C D : Set HashDomain} (hD : D ⊆ C) : cmdPostQN θ c D ⊆ cmdPostQN θ c C := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · exact hD
  · exact hD
  · exact hD
  · exact Set.sdiff_subset_sdiff_left hD
  · exact Set.union_subset_union_left _ hD

variable (θ : HPosN n → Digest)

theorem hPendN_mono {A : QReg} (y : IFreeM (QuantumComp.toIPFunctor L (XSpecN M n)) Ω A)
    {C C' D D' : Set HashDomain} (hy : HPendN θ y C C') (hD : D ⊆ C) (hD' : C' ⊆ D') :
    HPendN θ y D D' := by
  induction y using IFreeM.inductionOn generalizing C D with
  | pure _ _ => exact hD.trans (hy.trans hD')
  | liftBind _ c next ih =>
    exact ⟨cmdPreQN_anti c hD hy.1, fun b ↦ ih b (hy.2 b) (cmdPostQN_mono θ c hD)⟩

theorem hPendN_cast {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor L (XSpecN M n)) Ω A) (C C' : Set HashDomain) :
    HPendN θ (e ▸ y) C C' ↔ HPendN θ y C C' := by
  subst e
  rfl

theorem hPendN_bind {A : QReg} {Y : QReg → Type w₁}
    (x : IFreeM (QuantumComp.toIPFunctor L (XSpecN M n)) Ω A)
    (g : ∀ u, Ω u → IFreeM (QuantumComp.toIPFunctor L (XSpecN M n)) Y u)
    {C D C' : Set HashDomain} (hx : HPendN θ x C D) (hg : ∀ u a, HPendN θ (g u a) D C') :
    HPendN θ (x.bind g) C C' := by
  induction x using IFreeM.inductionOn generalizing C with
  | pure _ a => exact hPendN_mono θ _ (hg _ a) hx subset_rfl
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

theorem hPendN₂_bind {A B B' : QReg} {α : Type w} {β : Type w₁}
    (x : QuantumComp₂ L (XSpecN M n) A B α) (g : α → QuantumComp₂ L (XSpecN M n) B B' β)
    {C D C' : Set HashDomain} (hx : HPendN θ x C D) (hg : ∀ a, HPendN θ (g a) D C') :
    HPendN θ (x.bind g) C C' := by
  refine hPendN_bind θ x _ hx fun u p ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hg a

/-- Substituting trees that keep the invariant with nothing pending. -/
theorem hPendN_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor L spec)
      (QuantumComp.toIPFunctor L (XSpecN M n)))
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
    (y : QuantumComp L (hwReadSpec HashOutput HashDomain M) Ω A) :
    HPendN θ (readLift goodQN y) ∅ ∅ := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind _ c next ih =>
    show HPendN θ (IFreeM.mapLens (Quantum.Xmss.Assembly.readLens (goodQN (n := n)))
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
    HPendN θ (QComp.act (spec := XSpecN M n) p) C C :=
  ⟨trivial, fun _ ↦ subset_rfl⟩

/-- A reveal with nothing pending makes the cells whose source it reveals pending. -/
theorem hPendN_revealThen {B B' : QReg} {α : Type} (T : Finset (HPosN n))
    (k : RevealVals (HDN n) T × (Finset (HPosN n) × M) → QComp (XSpecN M n) B B' α)
    {C' : Set HashDomain} (hk : ∀ r, HPendN θ (k r) (revealCellsN θ T) C') :
    HPendN θ (revealThen goodQN T k) ∅ C' :=
  ⟨rfl, fun r ↦ hPendN₂_bind θ _ _ (hPendN_act θ _ _) fun _ ↦
    hPendN_mono θ _ (hk r.down) (Set.empty_union _).le subset_rfl⟩

theorem hPendN_progThen {B B' : QReg} {α : Type}
    (p : LazyProg HashOutput HashDomain (HPosN n) (HDN n)) (hp : goodQN p)
    (k : QComp (XSpecN M n) B B' α) {C C' : Set HashDomain}
    (hk : HPendN θ k (C \ progCellH (p.realize θ)) C') : HPendN θ (progThen p hp k) C C' :=
  ⟨trivial, fun _ ↦ hPendN₂_bind θ _ _ (hPendN_act θ _ _) fun _ ↦ hk⟩

theorem hPend_progPosN (i : Fin n) (B : QReg) (ps : List Pos) (C : Set HashDomain) :
    HPendN θ (progPosN M i B ps) C
      (C \ {z | ∃ q ∈ ps, z ∈ progCellH ((progTN i q).realize θ)}) := by
  induction ps generalizing C with
  | nil => exact fun z hz ↦ ⟨hz, fun ⟨_, hq, _⟩ ↦ absurd hq List.not_mem_nil⟩
  | cons q ps ih =>
    refine hPendN_progThen θ (progTN i q) trivial _ (hPendN_mono θ _ (ih _) subset_rfl ?_)
    rintro z ⟨⟨hz, hne⟩, hn⟩
    refine ⟨hz, ?_⟩
    rintro ⟨q', hq', hz'⟩
    rcases List.mem_cons.1 hq' with rfl | hq'
    · exact hne hz'
    · exact hn ⟨q', hq', hz'⟩

variable (upd : Fin n → TrialUpd M)

theorem hPend_selectTN (i : Fin n) (P : PublicParameter) (B : QReg) (l : Layer) (e : KeyIndex)
    (message : MsgBytes) (rnd : Pos) (hrnd : revealCellsN θ (atU i {loC rnd}) ⊆ ∅) :
    HPendN θ (selectTN M upd i P B l e message rnd) ∅ ∅ :=
  hPendN_revealThen θ _ _ fun _ ↦ hPendN_mono θ _ (hPendN_readLift θ _) hrnd subset_rfl

theorem hPend_publishTN (i : Fin n) (B : QReg) (l : Layer) (e : KeyIndex) (ρ : Randomizer)
    (x : Encoding) : HPendN θ (publishTN M i B l e ρ x) ∅ ∅ :=
  hPendN_revealThen θ _ _ fun _ ↦ hPendN₂_bind θ _ _ (hPend_progPosN θ i B _ _) fun _ ↦ by
    rintro z ⟨hz, hn⟩
    exact hn (revealCellsN_layerReveal θ i l e x hz)

theorem hPend_topTN (i : Fin n) (P : PublicParameter) (B : QReg) (r : SigningRequest)
    (h : Option TopSel) : HPendN θ (topTN M upd i P B r h) ∅ ∅ := by
  rcases h with _ | o
  · exact hPendN_revealThen θ _ _ fun _ ↦ hPendN_mono θ _
      (hPend_selectTN θ upd i P B _ _ _ _ (revealCellsN_rndTop θ i _ _))
      (revealCellsN_rootReveal θ i r) subset_rfl
  · exact subset_rfl

theorem hPend_pubBothN (i : Fin n) (B : QReg) (r : SigningRequest) (gb gt : TopSel) :
    HPendN θ (pubBothN (publishTN M i B) r gb gt) ∅ ∅ := by
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  · exact subset_rfl
  · exact subset_rfl
  · exact subset_rfl
  · exact hPendN₂_bind θ _ _ (hPend_publishTN θ i B _ _ _ _) fun _ ↦
      hPendN₂_bind θ _ _ (hPend_publishTN θ i B _ _ _ _) fun _ ↦ subset_rfl

theorem hPend_signTN (i : Fin n) (P : PublicParameter) (B : QReg) (r : SigningRequest)
    (h : Option TopSel) : HPendN θ (signTN M upd i P B r h) ∅ ∅ := by
  unfold signTN signWithN
  refine hPendN₂_bind θ _ _
    (hPend_selectTN θ upd i P B _ _ _ _ (revealCellsN_rndBottom θ i _ _)) fun gb ↦ ?_
  refine hPendN₂_bind θ _ _ (hPend_topTN θ upd i P B r h) fun gt ↦ ?_
  rw [QuantumComp₂.map_eq_bind_pure]
  exact hPendN₂_bind θ _ _ (hPend_pubBothN θ i B r gb gt) fun _ ↦ subset_rfl

theorem hPend_challengeTN (P : Fin n → PublicParameter) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (memoSpec n) A) :
    HPendN θ (challengeTN M upd P A c) ∅ ∅ := by
  rcases c with o | ⟨_ | ⟨i, q⟩, E, ℓ⟩
  · exact hPendN_readLift θ _
  · exact hPendN_readLift θ _
  · exact hPendN_bind θ _ _ (hPendN₂_bind θ _ _ (hPendN_act θ _ _) fun _ ↦
      hPend_signTN θ upd i (P i) _ q.1 q.2) fun _ _ ↦ subset_rfl

attribute [local irreducible] xmssRom

theorem hPend_prefixTN (A : MuAdversary n) : HPendN θ (prefixTN M upd A) ∅ ∅ :=
  hPendN_revealThen θ _ _ fun _ ↦ hPendN_mono θ _
    (hPendN₂_bind θ _ _ (hPendN_substitute θ _ (hPend_challengeTN θ upd _) _) fun _ ↦ subset_rfl)
    (revealCellsN_pkRevealN θ) subset_rfl

theorem hPend_verifyTN (valid : SignLog → Bool) (x : (Fin n → PublicKey) × MuRun n) :
    HPendN θ (verifyTN M valid x) ∅ ∅ := by
  unfold verifyTN
  generalize (readsProgram M _ (xmssRom.verify (x.1 x.2.1.1) x.2.1.2)).map Prod.fst = y
  exact hPendN₂_bind θ _ _ (hPendN_readLift θ _) fun _ ↦ subset_rfl

/-- **The game keeps the source invariant of `n` users.** -/
theorem hPend_muGameT (valid : SignLog → Bool) (A : MuAdversary n) :
    HPendN θ (muGameT M upd valid A) ∅ ∅ := by
  rw [muGameT_eq_prefixTN_bind]
  exact hPendN₂_bind θ _ _ (hPend_prefixTN θ upd A) fun x ↦ hPend_verifyTN θ valid x

end hp

/-! ## The steps of `runtimeR` on the pending invariant -/

section steps

variable {M : Type} [Fintype M] [DecidableEq M] {θ : HPosN n → Digest}

set_option synthInstance.maxSize 2000 in
omit [Fintype M] in
/-- A read port keeping the label keeps the hardwired cells and the label. -/
theorem hwReadKraus_ne_zero_keepQN {c : HwRead HashOutput HashDomain (Finset (HPosN n) × M)}
    (hc : ReadKeeps c) (r : c.Result) {u u' : Unit}
    {s s' : HwReg HashOutput HashDomain (Finset (HPosN n) × M)}
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
def StepPendN (m₀ : Finset (HPosN n) × M) (i : (recHwSpec HashOutput HashDomain (HPosN n) M).Port)
    (C C' : Set HashDomain) : Prop :=
  ∀ r σ, QuerySupportedOn (fun m : (recHwSpec HashOutput HashDomain (HPosN n) M).In i ×
      (runtimeR m₀).D ↦ m.2) {s | PendInvN θ C s} σ →
    QuerySupportedOn (fun m : (recHwSpec HashOutput HashDomain (HPosN n) M).Out i ×
      (runtimeR m₀).D ↦ m.2) {s | PendInvN θ C' s} (((runtimeR m₀).step i).branch r σ)

theorem stepPendN_sponge (m₀ : Finset (HPosN n) × M) (i : SpongePort) (C : Set HashDomain) :
    StepPendN θ m₀ (.inl (.inl (.inl i))) C C := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inl i)))).branch r σ =
      MatrixMap.conj ((spongeHardwired HashOutput HashDomain
        (hwEmpty HashOutput HashDomain) m₀).U i) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty HashOutput HashDomain) m₀ i
      r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    have he := snd_eq_of_spongeHardwired_U_ne_zero (hwEmpty HashOutput HashDomain) m₀ i q.1 q'.1
      q.2 q'.2 hK
    exact pendInvN_of_eq (congrArg Prod.fst he) (congrArg (fun t ↦ t.2.1) he) hq

theorem stepPendN_read (m₀ : Finset (HPosN n) × M)
    (c : {c : HwRead HashOutput HashDomain (Finset (HPosN n) × M) //
      ReadMono (Quantum.Xmss.Assembly.memLab HashOutput HashDomain (HPosN n) M) c})
    (hc : ReadKeeps c.1) (C : Set HashDomain) : StepPendN θ m₀ (.inl (.inl (.inr c.1))) C C := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inr c.1)))).branch r σ =
      MatrixMap.conj (hwReadKraus c.1 r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty HashOutput HashDomain) m₀ c.1
      r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    obtain ⟨h1, h2⟩ := hwReadKraus_ne_zero_keepQN hc r (u := q.1) (s := q.2) (u' := q'.1)
      (s' := q'.2) hK
    exact pendInvN_of_eq h1 h2 hq

theorem stepPendN_prog (m₀ : Finset (HPosN n) × M) (c : HwProg HashOutput HashDomain)
    (C : Set HashDomain) : StepPendN θ m₀ (.inl (.inr c)) C (C \ progCellH c) := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inr c))).branch r σ =
      MatrixMap.conj (hwProgKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty HashOutput HashDomain) m₀ c
      r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    pendInvN_prog c (hwProgKraus_ne_zero_snd c r (u := q.1) (s := q.2) (u' := q'.1)
      (s' := q'.2) hK) hq

theorem stepPendN_rec (m₀ : Finset (HPosN n) × M) (T : Finset (HPosN n)) (C : Set HashDomain) :
    StepPendN θ m₀ (.inr T) C (C ∪ revealCellsN θ T) := by
  intro r σ hσ
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    pendInvN_reveal T (Quantum.Xmss.Assembly.recKraus_ne_zero (u := q.1) (s := q.2) (u' := q'.1)
      (s' := q'.2) hK) hq

/-- An operator supported on the invariant presents, at a call, no diagonal mass outside it. -/
theorem relabel_diag_eq_zero_srcInvN (m₀ : Finset (HPosN n) × M) {A : QReg}
    {i : (recHwSpec HashOutput HashDomain (HPosN n) M).Port} (E : QReg)
    (ℓ : A ≃ (recHwSpec HashOutput HashDomain (HPosN n) M).In i × E)
    {ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | PendInvN θ ∅ s} ρ)
    (a : ((recHwSpec HashOutput HashDomain (HPosN n) M).In i × (runtimeR m₀).D) × E)
    (ha : ¬SrcInvN θ a.1.2) :
    (SubInstrument.relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).branch () ρ a a =
      0 := by
  by_contra h
  have h₁ := (hρ.branch_relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).imp
    (q' := fun m : ((recHwSpec HashOutput HashDomain (HPosN n) M).In i × (runtimeR m₀).D) × E ↦
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
    {Q : (recHwSpec HashOutput HashDomain (HPosN n) M).Port → Prop}
    (m₀ : Finset (HPosN n) × M) (I : L.Interp) (θ : HPosN n → Digest) {A : QReg}
    (i : (recHwSpec HashOutput HashDomain (HPosN n) M).Port) (E : QReg)
    (ℓ : A ≃ (recHwSpec HashOutput HashDomain (HPosN n) M).In i × E)
    (k' : (recHwSpec HashOutput HashDomain (HPosN n) M).Result i →
      QuantumComp L (recHwSpec HashOutput HashDomain (HPosN n) M) Ω
        (QReg.of ((recHwSpec HashOutput HashDomain (HPosN n) M).Out i × E)))
    {C C' : Set HashDomain} (hpre : Q i → C = ∅) (hstep : StepPendN θ m₀ i C C')
    (hk : ∀ r ρ', QuerySupportedOn (fun m : QReg.of
        ((recHwSpec HashOutput HashDomain (HPosN n) M).Out i × E) × (runtimeR m₀).D ↦ m.2)
        {s | PendInvN θ C' s} ρ' →
      (runtimeR m₀).ForallQueries I (Quantum.Xmss.Assembly.invSupp (runtimeR m₀) Q (SrcInvN θ))
        (k' r) ρ')
    (ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ)
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | PendInvN θ C s} ρ) :
    (runtimeR m₀).ForallQueries I (Quantum.Xmss.Assembly.invSupp (runtimeR m₀) Q (SrcInvN θ))
      (QuantumComp.queryBind i E ℓ k') ρ :=
  ⟨fun hq a ha ↦ relabel_diag_eq_zero_srcInvN (i := i) m₀ E ℓ (hpre hq ▸ hρ) a ha, fun r ↦
    hk r _ (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s) i r (hstep r) E ℓ hρ)⟩

/-- **The realized program of a template keeping the source invariant of `n` users presents, at
every call of the ports `Q` (no program port), only states of the invariant.** -/
theorem forallQueries_of_hPendN {Q : (recHwSpec HashOutput HashDomain (HPosN n) M).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (m₀ : Finset (HPosN n) × M) (I : L.Interp)
    (θ : HPosN n → Digest) {A : QReg} (y : QuantumComp L (XSpecN M n) Ω A) :
    ∀ C C', HPendN θ y C C' → ∀ ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | PendInvN θ C s} ρ →
      (runtimeR m₀).ForallQueries I (Quantum.Xmss.Assembly.invSupp (runtimeR m₀) Q (SrcInvN θ))
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
        (fun m ↦ realizeT θ (k (restrictTo T θ, m))) (fun _ ↦ hy.1) (stepPendN_rec m₀ T C)
        (fun m ↦ ih (restrictTo T θ, m) _ C' (hy.2 (ULift.up (restrictTo T θ, m)))) ρ hρ

/-- An initial state whose memory label is empty. -/
theorem querySupportedOn_initQN (m₀ : Finset (HPosN n) × M) (hm₀ : m₀.1 = ∅) {A : QReg}
    (σ : Matrix A A ℂ) :
    QuerySupportedOn (fun a : A × QReg.of (HwReg HashOutput HashDomain (Finset (HPosN n) × M)) ↦
      a.2.2.2.1) {∅} (σ ⊗ₖ (runtimeR (X := HashOutput) (Z := HashDomain) m₀).init.matrix) := by
  intro a b h
  change (σ ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
    hwEmpty HashOutput HashDomain, m₀) :
      HwReg HashOutput HashDomain (Finset (HPosN n) × M))).matrix) a b ≠ 0 at h
  rw [SubState.matrix_basis, kroneckerMap_apply] at h
  have h' := right_ne_zero_of_mul h
  rw [Matrix.single_apply] at h'
  split_ifs at h' with he
  · show a.2.2.2.1 ∈ ({∅} : Set (Finset (HPosN n))) ∧ b.2.2.2.1 ∈ ({∅} : Set (Finset (HPosN n)))
    rw [← he.1, ← he.2]
    exact ⟨hm₀, hm₀⟩
  · exact absurd rfl h'

variable (upd : Fin n → TrialUpd M)

/-- **`hinv` for the realized multi-user template game**: from states with an empty memory label,
every call of ports `Q` that are not program ports sees the source invariant of `n` users. -/
theorem forallQueries_muGameQN {Q : (recHwSpec HashOutput HashDomain (HPosN n) M).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (m₀ : Finset (HPosN n) × M) (valid : SignLog → Bool)
    (A : MuAdversary n) (θ : HPosN n → Digest)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset (HPosN n) × M)))
      (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset (HPosN n) × M))) ℂ)
    (hρ : QuerySupportedOn (fun a : QReg.of Unit ×
      QReg.of (HwReg HashOutput HashDomain (Finset (HPosN n) × M)) ↦ a.2.2.2.1) {∅} ρ) :
    (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (Quantum.Xmss.Assembly.invSupp (runtimeR m₀) Q (SrcInvN θ))
      (realizeT θ (muGameT M upd valid A)) ρ :=
  forallQueries_of_hPendN hQ m₀ _ θ _ ∅ ∅ (hPend_muGameT θ upd valid A) ρ
    (hρ.imp fun _ ha ↦ pendInvN_of_label_empty (Set.mem_singleton_iff.1 ha))

/-- The same for the challenge prefix. -/
theorem forallQueries_prefixQN {Q : (recHwSpec HashOutput HashDomain (HPosN n) M).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (m₀ : Finset (HPosN n) × M) (A : MuAdversary n)
    (θ : HPosN n → Digest)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset (HPosN n) × M)))
      (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset (HPosN n) × M))) ℂ)
    (hρ : QuerySupportedOn (fun a : QReg.of Unit ×
      QReg.of (HwReg HashOutput HashDomain (Finset (HPosN n) × M)) ↦ a.2.2.2.1) {∅} ρ) :
    (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (Quantum.Xmss.Assembly.invSupp (runtimeR m₀) Q (SrcInvN θ))
      (realizeT θ (prefixTN M upd A)) ρ :=
  forallQueries_of_hPendN hQ m₀ _ θ _ ∅ ∅ (hPend_prefixTN θ upd A) ρ
    (hρ.imp fun _ ha ↦ pendInvN_of_label_empty (Set.mem_singleton_iff.1 ha))

end hinv

/-! ## The memo transform's charges -/

section memo

/-- Two charge bounds give their minimum. -/
theorem isChargeBound_min {I : Type*} {P : IPFunctor.Endo I} {X : I → Type*}
    {c : (s : I) → P.A s → ℕ} {s : I} {x : IFreeM P X s} {m₁ m₂ : ℕ}
    (h₁ : x.IsChargeBound c m₁) (h₂ : x.IsChargeBound c m₂) :
    x.IsChargeBound c (min m₁ m₂) := by
  induction x using IFreeM.inductionOn generalizing m₁ m₂ with
  | pure _ _ => trivial
  | liftBind s a next ih =>
    rw [IFreeM.isChargeBound_liftBind_iff] at h₁ h₂ ⊢
    exact ⟨le_min h₁.1 h₂.1, fun b ↦ (ih b (h₁.2 b) (h₂.2 b)).mono (by omega)⟩

/-- The charge of the adversary's commands with the memo: `α` per hash call, `βh` per signing
request, and `βm` more per request without a memoized top selection. -/
def memoCharge (α βh βm : ℕ) : MuPort n (SigningRequest × Option TopSel) → ℕ
  | .hash => α
  | .sign _ (_, h) => βh + if h = none then βm else 0

/-- A signing request without a memoized top selection costs one, every other call nothing. -/
def missCharge : MuPort n (SigningRequest × Option TopSel) → ℕ
  | .hash => 0
  | .sign _ (_, none) => 1
  | .sign _ (_, some _) => 0

/-- **The memo transform keeps a charge bound** for a charge on the memo ports at most the
adversary's charge of the same call. -/
theorem isChargeBound_memoFrom_of_le {Y : QReg → Type} {c : MuPort n SigningRequest → ℕ}
    {c' : MuPort n (SigningRequest × Option TopSel) → ℕ} (hh : c' .hash ≤ c .hash)
    (hs : ∀ i r h, c' (.sign i (r, h)) ≤ c (.sign i r)) {A : QReg} (x : IFreeM (MuP n) Y A)
    (T : SelMemo n) {m : ℕ} (hx : IFreeM.IsChargeBound x (cmdCharge c) m) :
    IFreeM.IsChargeBound (memoFrom T x) (cmdCharge c') m := by
  induction x using IFreeM.inductionOn generalizing T m with
  | pure _ _ => trivial
  | liftBind _ cmd next ih =>
    rcases cmd with o | ⟨_ | ⟨i, r⟩, E, ℓ⟩
    · exact ⟨hx.1, fun b ↦ ih b T (hx.2 b)⟩
    · exact ⟨hh.trans hx.1, fun b ↦ (ih b T (hx.2 b)).mono (Nat.sub_le_sub_left hh m)⟩
    · exact ⟨(hs i r _).trans hx.1, fun b ↦ (ih _ _ (hx.2 _)).mono
        (Nat.sub_le_sub_left (hs i r _) m)⟩

theorem missCharge_sign_le (T : SelMemo n) (F : Finset (Fin n × KeyIndex))
    (hF : ∀ i r, T i (topKeyOf r) = none → (i, topKeyOf r) ∈ F) (i : Fin n)
    (r : SigningRequest) : missCharge (.sign i (r, T i (topKeyOf r))) ≤ F.card := by
  cases hT : T i (topKeyOf r) with
  | none => exact Finset.card_pos.2 ⟨_, hF i r hT⟩
  | some _ => exact Nat.zero_le _

theorem card_erase_le_sub_missCharge (T : SelMemo n) (F : Finset (Fin n × KeyIndex))
    (hF : ∀ i r, T i (topKeyOf r) = none → (i, topKeyOf r) ∈ F) (i : Fin n)
    (r : SigningRequest) :
    (F.erase (i, topKeyOf r)).card ≤ F.card - missCharge (.sign i (r, T i (topKeyOf r))) := by
  cases hT : T i (topKeyOf r) with
  | none =>
    rw [Finset.card_erase_of_mem (hF i r hT)]
    exact le_rfl
  | some _ => exact Finset.card_erase_le.trans (Nat.le_of_eq (Nat.sub_zero _).symm)

theorem mem_erase_of_put_eq_none (T : SelMemo n) (F : Finset (Fin n × KeyIndex))
    (hF : ∀ i r, T i (topKeyOf r) = none → (i, topKeyOf r) ∈ F) (i : Fin n)
    (r : SigningRequest) (s : TopSel) (j : Fin n) (r' : SigningRequest)
    (h : T.put i (topKeyOf r) s j (topKeyOf r') = none) :
    (j, topKeyOf r') ∈ F.erase (i, topKeyOf r) := by
  by_cases he : j = i ∧ topKeyOf r' = topKeyOf r
  · obtain ⟨rfl, he⟩ := he
    rw [he, SelMemo.put_self] at h
    exact absurd h (Option.some_ne_none _)
  · rw [SelMemo.put_of_ne T s he] at h
    exact Finset.mem_erase.2 ⟨fun h' ↦ he ⟨(Prod.ext_iff.1 h').1, (Prod.ext_iff.1 h').2⟩,
      hF j r' h⟩

/-- **The requests without a memoized top selection**: at most the number of pairs `F` of a user
and a top key holding every pair the memo `T` has not memoized. -/
theorem isChargeBound_missCharge_memoFrom {Y : QReg → Type} {A : QReg} (x : IFreeM (MuP n) Y A)
    (T : SelMemo n) (F : Finset (Fin n × KeyIndex))
    (hF : ∀ i r, T i (topKeyOf r) = none → (i, topKeyOf r) ∈ F) :
    IFreeM.IsChargeBound (memoFrom T x) (cmdCharge missCharge) F.card := by
  induction x using IFreeM.inductionOn generalizing T F with
  | pure _ _ => trivial
  | liftBind _ cmd next ih =>
    rcases cmd with o | ⟨_ | ⟨i, r⟩, E, ℓ⟩
    · exact ⟨Nat.zero_le _, fun b ↦ (ih b T F hF).mono (Nat.le_of_eq (Nat.sub_zero _).symm)⟩
    · exact ⟨Nat.zero_le _, fun b ↦ (ih b T F hF).mono (Nat.le_of_eq (Nat.sub_zero _).symm)⟩
    · exact ⟨missCharge_sign_le T F hF i r, fun b ↦ (ih _ _ (F.erase (i, topKeyOf r))
        (mem_erase_of_put_eq_none T F hF i r _)).mono
          (card_erase_le_sub_missCharge T F hF i r)⟩

theorem topKey_le_lifetime : 2 ^ (32 - layerHeight) ≤ lifetime := by
  rw [lifetime_eq]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)

/-- The pairs of a user and a top key: the keys below `2 ^ (32 - layerHeight)`. -/
def topPairs (n : ℕ) : Finset (Fin n × KeyIndex) :=
  Finset.univ ×ˢ (Finset.univ : Finset (Fin (2 ^ (32 - layerHeight)))).image
    (Fin.castLE topKey_le_lifetime)

theorem mem_topPairs (i : Fin n) (r : SigningRequest) : (i, topKeyOf r) ∈ topPairs n :=
  Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_image.2
    ⟨⟨(topKeyOf r).val, QTable.keyIndexOnLayer_top_lt r.leafIndex⟩, Finset.mem_univ _,
      Fin.ext rfl⟩⟩

theorem card_topPairs_le (n : ℕ) : (topPairs n).card ≤ n * 2 ^ 16 := by
  rw [topPairs, Finset.card_product, Finset.card_univ, Fintype.card_fin]
  refine Nat.mul_le_mul_left n (Finset.card_image_le.trans ?_)
  rw [Finset.card_univ, Fintype.card_fin, layerHeight_eq]

/-- **From the empty memo, the requests without a memoized top selection** are at most the
requests and at most one per user and top key. -/
theorem isChargeBound_missCharge_memoFrom_empty {Y : QReg → Type} {A : QReg}
    (x : IFreeM (MuP n) Y A) {total : ℕ}
    (hsign : IFreeM.IsChargeBound x (cmdCharge signCharge) total) :
    IFreeM.IsChargeBound (memoFrom (fun _ _ ↦ none) x) (cmdCharge missCharge)
      (min total (n * 2 ^ 16)) :=
  isChargeBound_min
    (isChargeBound_memoFrom_of_le (c := signCharge) le_rfl
      (fun _ _ h ↦ by cases h <;> simp [missCharge, signCharge]) x _
      hsign)
    ((isChargeBound_missCharge_memoFrom x _ (topPairs n) fun i r _ ↦ mem_topPairs i r).mono
      (card_topPairs_le n))

/-- **The adversary's charge with the memo**, from the empty memo: `α` per hash call, `βh` per
request, `βm` per request without a memoized top selection. -/
theorem isChargeBound_memoFrom_memoCharge {Y : QReg → Type} {A : QReg} (x : IFreeM (MuP n) Y A)
    {q total : ℕ} (hhash : IFreeM.IsChargeBound x (cmdCharge hashCharge) q)
    (hsign : IFreeM.IsChargeBound x (cmdCharge signCharge) total) (α βh βm : ℕ) :
    IFreeM.IsChargeBound (memoFrom (fun _ _ ↦ none) x) (cmdCharge (memoCharge α βh βm))
      (α * q + βh * total + βm * min total (n * 2 ^ 16)) := by
  have h1 := (isChargeBound_memoFrom_of_le (c := hashCharge) (c' := hashCharge) le_rfl
    (fun _ _ _ ↦ le_rfl) x (fun _ _ ↦ none) hhash).mul α
  have h2 := (isChargeBound_memoFrom_of_le (c := signCharge) (c' := signCharge) le_rfl
    (fun _ _ _ ↦ le_rfl) x (fun _ _ ↦ none) hsign).mul βh
  have h3 := (isChargeBound_missCharge_memoFrom_empty x hsign).mul βm
  refine ((h1.add h2).add h3).mono_charge fun s cmd ↦ ?_
  rcases cmd with o | ⟨_ | ⟨i, r, h⟩, E, ℓ⟩
  · exact Nat.zero_le _
  · simp [cmdCharge, memoCharge, hashCharge, signCharge, missCharge]
  · cases h <;> simp [cmdCharge, memoCharge, hashCharge, signCharge, missCharge]

end memo

/-! ## Charges of the calls by kind -/

section charges

variable {M : Type} {L : LocalSig.{u, v}} {Ω : QReg → Type w}

variable (M) in
/-- A charge on the template ports of `n` users by kind: `a` per sponge call, `b` per read at a
cell other than a message digest, `b'` per read at a message digest, `c` per program call, `d` per
reveal. -/
def tChargeQN (a b b' c d : ℕ) : (XSpecN M n).Port → ℕ
  | .inl (.inl (.inl _)) => a
  | .inl (.inl (.inr r)) => if readMsg r.1 then b' else b
  | .inl (.inr _) => c
  | .inr _ => d

variable (M) in
/-- The same charge on runtime 2 with record ports (a reveal realizes as a record call). -/
def rChargeQN (a b b' c d : ℕ) : (recHwSpec HashOutput HashDomain (HPosN n) M).Port → ℕ
  | .inl (.inl (.inl _)) => a
  | .inl (.inl (.inr r)) => if readMsg r then b' else b
  | .inl (.inr _) => c
  | .inr _ => d

variable (M) in
/-- The reads at cells other than message digests: the ports of the read mass. -/
def readQN : (recHwSpec HashOutput HashDomain (HPosN n) M).Port → Bool
  | .inl (.inl (.inr r)) => !readMsg r
  | _ => false

variable (a b b' c d : ℕ)

/-- **Realizing keeps the charges by kind.** -/
theorem isChargeBound_realizeTN (θ : HPosN n → Digest) {A : QReg}
    {y : QuantumComp L (XSpecN M n) Ω A} {k : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge (tChargeQN M a b b' c d)) k) :
    IFreeM.IsChargeBound (realizeT θ y) (portCharge (rChargeQN M a b b' c d)) k := by
  refine IFreeM.IsChargeBound.mapLens
    (Quantum.Xmss.Assembly.tmplLens (good := goodQN) (M := M) θ) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (rChargeQN M a b b' c d) s
      ((Quantum.Xmss.Assembly.tmplLens (good := goodQN) (M := M) θ).toFunA s cmd)) =
      portCharge (tChargeQN M a b b' c d) := by
    funext s cmd
    rcases cmd with o | ⟨((i | r) | p) | T, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

theorem isChargeBound_readLiftN {A : QReg}
    {y : QuantumComp L (hwReadSpec HashOutput HashDomain M) Ω A} {k : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge (rdChargeQ M a b b')) k) :
    IFreeM.IsChargeBound (readLift (goodQN (n := n)) y) (portCharge (tChargeQN M a b b' c d))
      k := by
  refine IFreeM.IsChargeBound.mapLens (Quantum.Xmss.Assembly.readLens (goodQN (n := n))) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (tChargeQN M a b b' c d) s
      ((Quantum.Xmss.Assembly.readLens (goodQN (n := n))).toFunA s cmd)) =
      portCharge (rdChargeQ M a b b') := by
    funext s cmd
    rcases cmd with o | ⟨i | r, E, ℓ⟩
    · rfl
    · rfl
    · cases r <;> rfl
  rw [he]
  exact h

theorem chg_revealThenN {B B' : QReg} {α : Type} (T : Finset (HPosN n))
    (k : RevealVals (HDN n) T × (Finset (HPosN n) × M) → QComp (XSpecN M n) B B' α) {m : ℕ}
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge (tChargeQN M a b b' c d)) m) :
    IFreeM.IsChargeBound (revealThen goodQN T k) (portCharge (tChargeQN M a b b' c d))
      (d + m) := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.le_add_right d m, fun r ↦ ?_⟩
  simp only [tChargeQN, Nat.add_sub_cancel_left]
  exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₁ := 0)
    (Quantum.Xmss.Assembly.chg_act _ _ 0) fun _ ↦ hk r) (Nat.zero_add m).le

theorem chg_progThenN {B B' : QReg} {α : Type}
    (p : LazyProg HashOutput HashDomain (HPosN n) (HDN n)) (hp : goodQN p)
    (k : QComp (XSpecN M n) B B' α) {m : ℕ}
    (hk : IFreeM.IsChargeBound k (portCharge (tChargeQN M a b b' c d)) m) :
    IFreeM.IsChargeBound (progThen p hp k) (portCharge (tChargeQN M a b b' c d)) (c + m) := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.le_add_right c m, fun r ↦ ?_⟩
  simp only [tChargeQN, Nat.add_sub_cancel_left]
  exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₁ := 0)
    (Quantum.Xmss.Assembly.chg_act _ _ 0) fun _ ↦ hk) (Nat.zero_add m).le

theorem chg_progPosN (i : Fin n) (B : QReg) (ps : List Pos) :
    IFreeM.IsChargeBound (progPosN M i B ps) (portCharge (tChargeQN M a b b' c d))
      (c * ps.length) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    refine IFreeM.IsChargeBound.mono (chg_progThenN a b b' c d (progTN i p) trivial _ ih)
      (le_of_eq ?_)
    rw [List.length_cons, Nat.mul_succ, Nat.add_comm]

variable (upd : Fin n → TrialUpd M)

theorem chg_selectTN (i : Fin n) (P : PublicParameter) (B : QReg) (l : Layer) (e : KeyIndex)
    (message : MsgBytes) (rnd : Pos) :
    IFreeM.IsChargeBound (selectTN M upd i P B l e message rnd)
      (portCharge (tChargeQN M a b b' c d)) (d + randomizerAttemptLimit * b') :=
  chg_revealThenN a b b' c d _ _ fun _ ↦
    isChargeBound_readLiftN a b b' c d (chg_grindT a b b' (upd i) P B l e message _ _ 0)

theorem chg_publishTN (i : Fin n) (B : QReg) (l : Layer) (e : KeyIndex) (ρ : Randomizer)
    (x : Encoding) :
    IFreeM.IsChargeBound (publishTN M i B l e ρ x) (portCharge (tChargeQN M a b b' c d))
      (d + c * layerProgCap) := by
  refine chg_revealThenN a b b' c d _ _ fun _ ↦ IFreeM.IsChargeBound.mono
    (FreeM₂.isChargeBound_bind (n₂ := 0) (chg_progPosN a b b' c d i B _) fun _ ↦ trivial) ?_
  rw [Nat.add_zero]
  exact Nat.mul_le_mul_left c (length_layerPos_le l e x)

/-- The calls of a signing request with a memoized top selection: the bottom search's, two layer
publications. -/
def hitCallsQ (b' c d : ℕ) : ℕ :=
  3 * d + randomizerAttemptLimit * b' + 2 * c * layerProgCap

/-- The further calls of a signing request without a memoized top selection: the bottom root's
reveal and the top search's. -/
def missCallsQ (b' d : ℕ) : ℕ :=
  2 * d + randomizerAttemptLimit * b'

/-- **The top layer's search or memo**: no call on a memo hit. -/
theorem chg_topTN (i : Fin n) (P : PublicParameter) (B : QReg) (r : SigningRequest)
    (h : Option TopSel) :
    IFreeM.IsChargeBound (topTN M upd i P B r h) (portCharge (tChargeQN M a b b' c d))
      (if h = none then missCallsQ b' d else 0) := by
  rcases h with _ | o
  · refine IFreeM.IsChargeBound.mono (chg_revealThenN a b b' c d _ _ fun _ ↦
      chg_selectTN a b b' c d upd i P B _ _ _ _) (le_of_eq ?_)
    rw [ite_eq_left rfl, missCallsQ]
    ring
  · trivial

theorem chg_pubBothN (i : Fin n) (B : QReg) (r : SigningRequest) (gb gt : TopSel) :
    IFreeM.IsChargeBound (pubBothN (publishTN M i B) r gb gt)
      (portCharge (tChargeQN M a b b' c d)) ((d + c * layerProgCap) + ((d + c * layerProgCap) + 0))
    := by
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  · trivial
  · trivial
  · trivial
  · simp only [pubBothN]
    refine FreeM₂.isChargeBound_bind (n₁ := d + c * layerProgCap)
      (n₂ := (d + c * layerProgCap) + 0) (chg_publishTN a b b' c d i B _ _ _ _) fun _ ↦ ?_
    exact FreeM₂.isChargeBound_bind (n₁ := d + c * layerProgCap) (n₂ := 0)
      (chg_publishTN a b b' c d i B _ _ _ _) fun _ ↦ trivial

/-- **A signature's calls**: `hitCallsQ`, and `missCallsQ` more without a memoized top
selection. -/
theorem chg_signTN (i : Fin n) (P : PublicParameter) (B : QReg) (r : SigningRequest)
    (h : Option TopSel) :
    IFreeM.IsChargeBound (signTN M upd i P B r h) (portCharge (tChargeQN M a b b' c d))
      (hitCallsQ b' c d + (if h = none then missCallsQ b' d else 0)) := by
  unfold signTN signWithN
  refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind
    (chg_selectTN a b b' c d upd i P B _ _ _ _) fun gb ↦ FreeM₂.isChargeBound_bind
      (chg_topTN a b b' c d upd i P B r h) fun gt ↦ Quantum.Xmss.Assembly.chg_map _ _
        (chg_pubBothN a b b' c d i B r gb gt)) (le_of_eq ?_)
  unfold hitCallsQ
  ring

/-- **The challenger's calls** per command: a local operation none, a hash call one sponge call,
a signing request `hitCallsQ`, and `missCallsQ` more without a memoized top selection. -/
theorem chg_challengeTN (P : Fin n → PublicParameter) (A : QReg)
    (cmd : QuantumComp.Cmd LocalSig.instruments.{0} (memoSpec n) A) :
    IFreeM.IsChargeBound (challengeTN M upd P A cmd) (portCharge (tChargeQN M a b b' c d))
      (cmdCharge (memoCharge a (hitCallsQ b' c d) (missCallsQ b' d)) A cmd) := by
  rcases cmd with o | ⟨_ | ⟨i, r, h⟩, E, ℓ⟩
  · refine isChargeBound_readLiftN a b b' c d (isChargeBound_liftOrdinary _
      ((isChargeBound_liftH_iff _ _ _).mpr ?_))
    exact (isChargeBound_portCharge_primBind_iff _ _ _ _).mpr fun _ ↦ trivial
  · refine isChargeBound_readLiftN a b b' c d (isChargeBound_liftOrdinary _
      ((isChargeBound_liftH_iff _ _ _).mpr ?_))
    exact (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨le_rfl, fun _ ↦ trivial⟩
  · refine IFreeM.IsChargeBound.mono (IFreeM.isChargeBound_bind (FreeM₂.isChargeBound_bind
      (n₁ := 0) (Quantum.Xmss.Assembly.chg_act _ _ 0) fun _ ↦
        chg_signTN a b b' c d upd i (P i) _ r h) fun _ _ ↦ IFreeM.isChargeBound_pure _ 0) ?_
    cases h <;> simp [cmdCharge, memoCharge]

attribute [local irreducible] xmssRom

/-- **The challenge prefix's calls**: the public keys' reveal, the challenged memo transform. -/
theorem chg_prefixTN (A : MuAdversary n) {q total : ℕ}
    (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
    (hsign : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total) :
    IFreeM.IsChargeBound (prefixTN M upd A) (portCharge (tChargeQN M a b b' c d))
      (d + ((a * q + hitCallsQ b' c d * total + missCallsQ b' d * min total (n * 2 ^ 16)) +
        0)) := by
  refine chg_revealThenN a b b' c d _ _ fun r₀ ↦ ?_
  have hx := isChargeBound_memoFrom_memoCharge (withMuSignLog (A (pksT r₀.1)))
    (isChargeBound_withMuSignLog (hhash _)) (isChargeBound_withMuSignLog (hsign _)) a
    (hitCallsQ b' c d) (missCallsQ b' d)
  have hc := IFreeM.IsChargeBound.substitute
    (challengeTN M upd fun i ↦ (pksT r₀.1 i).parameter)
    (chg_challengeTN a b b' c d upd fun i ↦ (pksT r₀.1 i).parameter) hx
  exact FreeM₂.isChargeBound_bind hc fun _ ↦ trivial

/-- **The verification's calls**: one read per hash call of the verifier. -/
theorem chg_verifyTN (valid : SignLog → Bool) (x : (Fin n → PublicKey) × MuRun n) :
    IFreeM.IsChargeBound (verifyTN M valid x) (portCharge (tChargeQN M a b b' c d))
      (max b b' * verifyCalls + 0) := by
  unfold verifyTN
  exact FreeM₂.isChargeBound_bind (isChargeBound_readLiftN a b b' c d
    (Quantum.Xmss.Assembly.chg_map _ Prod.fst (chg_readsProgram a b b' _ (verify_cost _ _))))
      fun _ ↦ trivial

/-- The calls of the multi-user game by kind: the public keys' reveal, `a` per hash call,
`hitCallsQ` per request, `missCallsQ` per request without a memoized top selection (at most one
per user and top key), the verification's reads. -/
def gameCallsQN (a b b' c d q n total : ℕ) : ℕ :=
  d + (a * q + hitCallsQ b' c d * total + missCallsQ b' d * min total (n * 2 ^ 16)) +
    max b b' * verifyCalls

/-- **The realized game's calls by kind**, for an adversary making at most `q` hash calls and at
most `total` signing requests on every path, at all hidden values. -/
theorem chg_realizeT_muGameT (valid : SignLog → Bool) (A : MuAdversary n) {q total : ℕ}
    (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
    (hsign : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total)
    (θ : HPosN n → Digest) :
    IFreeM.IsChargeBound (realizeT θ (muGameT M upd valid A))
      (portCharge (rChargeQN M a b b' c d)) (gameCallsQN a b b' c d q n total) := by
  refine isChargeBound_realizeTN a b b' c d θ ?_
  rw [muGameT_eq_prefixTN_bind]
  exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind
    (chg_prefixTN a b b' c d upd A hhash hsign) fun x ↦ chg_verifyTN a b b' c d valid x)
      (le_of_eq (by unfold gameCallsQN; omega))

/-- **The realized prefix's calls by kind.** -/
theorem chg_realizeT_prefixTN (A : MuAdversary n) {q total : ℕ}
    (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
    (hsign : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total)
    (θ : HPosN n → Digest) :
    IFreeM.IsChargeBound (realizeT θ (prefixTN M upd A)) (portCharge (rChargeQN M a b b' c d))
      (gameCallsQN a b b' c d q n total) :=
  isChargeBound_realizeTN a b b' c d θ (IFreeM.IsChargeBound.mono
    (chg_prefixTN a b b' c d upd A hhash hsign) (by unfold gameCallsQN; omega))

end charges

/-! ## The call counts -/

section counts

/-- The program calls of the game: two layer publications per request. -/
def progCapN (total : ℕ) : ℕ :=
  2 * layerProgCap * total

/-- The classical calls of the game: the public keys' reveal, per request the bottom search's
reads, three reveals, two publications' program calls and two more reveals, per request without a
memoized top selection the top search's reads, and the verification's reads. -/
def clsCapN (n total : ℕ) : ℕ :=
  1 + (randomizerAttemptLimit + 5 + 2 * layerProgCap) * total +
    randomizerAttemptLimit * min total (n * 2 ^ 16) + verifyCalls

theorem gameCallsQN_adv (q n total : ℕ) : gameCallsQN 1 0 0 0 0 q n total = q := by
  simp [gameCallsQN, hitCallsQ, missCallsQ]

theorem gameCallsQN_cls_le (q n total : ℕ) : gameCallsQN 0 1 1 1 1 q n total ≤ clsCapN n total := by
  have hm := min_le_left total (n * 2 ^ 16)
  simp only [gameCallsQN, hitCallsQ, missCallsQ, clsCapN, max_self]
  generalize min total (n * 2 ^ 16) = m at hm ⊢
  generalize randomizerAttemptLimit = R
  generalize layerProgCap = P
  generalize verifyCalls = V
  nlinarith

theorem gameCallsQN_prog (q n total : ℕ) : gameCallsQN 0 0 0 1 0 q n total = progCapN total := by
  simp only [gameCallsQN, hitCallsQ, missCallsQ, progCapN, max_self]
  generalize min total (n * 2 ^ 16) = m
  generalize randomizerAttemptLimit = R
  generalize layerProgCap = P
  generalize verifyCalls = V
  ring

theorem gameCallsQN_readQ (q n total : ℕ) : gameCallsQN 0 1 0 0 0 q n total = verifyCalls := by
  simp [gameCallsQN, hitCallsQ, missCallsQ]

variable {M : Type}

theorem advCharge_eqN :
    (fun i ↦ if Quantum.Xmss.Assembly.extCls HashOutput HashDomain (Finset (HPosN n) × M)
      (recSpec (HPosN n) M) i then 0 else 1) = rChargeQN M 1 0 0 0 0 := by
  funext i
  rcases i with ((i | r) | p) | T
  · rfl
  · exact (ite_self 0).symm
  · rfl
  · rfl

theorem clsCharge_eqN :
    (fun i ↦ if Quantum.Xmss.Assembly.extCls HashOutput HashDomain (Finset (HPosN n) × M)
      (recSpec (HPosN n) M) i then 1 else 0) = rChargeQN M 0 1 1 1 1 := by
  funext i
  rcases i with ((i | r) | p) | T
  · rfl
  · exact (ite_self 1).symm
  · rfl
  · rfl

theorem progCharge_eqN :
    Quantum.Xmss.extProgCharge HashOutput HashDomain (Finset (HPosN n) × M)
      (recSpec (HPosN n) M) = rChargeQN M 0 0 0 1 0 := by
  funext i
  rcases i with ((i | r) | p) | T
  · rfl
  · exact (ite_self 0).symm
  · rfl
  · rfl

theorem readQCharge_eqN :
    (fun i ↦ if readQN M (n := n) i = true then 1 else 0) = rChargeQN M 0 1 0 0 0 := by
  funext i
  rcases i with ((i | r) | p) | T
  · rfl
  · simp only [readQN, rChargeQN]
    rcases Bool.eq_false_or_eq_true (readMsg r) with h | h <;> simp [h]
  · rfl
  · rfl

variable (upd : Fin n → TrialUpd M) (valid : SignLog → Bool) (A : MuAdversary n) {q total : ℕ}
  (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
  (hsign : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total)
include hhash hsign

/-- **The game's sponge calls**: at most `q`. -/
theorem advCalls_muGameQ (θ : HPosN n → Digest) :
    IFreeM.IsChargeBound (realizeT θ (muGameT M upd valid A))
      (portCharge fun i ↦ if Quantum.Xmss.Assembly.extCls HashOutput HashDomain
        (Finset (HPosN n) × M) (recSpec (HPosN n) M) i then 0 else 1) q := by
  rw [advCharge_eqN]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_muGameT 1 0 0 0 0 upd valid A hhash hsign θ)
    (le_of_eq (gameCallsQN_adv q n total))

/-- **The game's classical calls** (reads, program and record calls): at most `clsCapN`. -/
theorem clsCalls_muGameQ (θ : HPosN n → Digest) :
    IFreeM.IsChargeBound (realizeT θ (muGameT M upd valid A))
      (portCharge fun i ↦ if Quantum.Xmss.Assembly.extCls HashOutput HashDomain
        (Finset (HPosN n) × M) (recSpec (HPosN n) M) i then 1 else 0) (clsCapN n total) := by
  rw [clsCharge_eqN]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_muGameT 0 1 1 1 1 upd valid A hhash hsign θ)
    (gameCallsQN_cls_le q n total)

/-- **The game's program calls**: at most `progCapN`. -/
theorem progCalls_muGameQ (θ : HPosN n → Digest) :
    IFreeM.IsChargeBound (realizeT θ (muGameT M upd valid A))
      (portCharge (Quantum.Xmss.extProgCharge HashOutput HashDomain (Finset (HPosN n) × M)
        (recSpec (HPosN n) M))) (progCapN total) := by
  rw [progCharge_eqN]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_muGameT 0 0 0 1 0 upd valid A hhash hsign θ)
    (le_of_eq (gameCallsQN_prog q n total))

/-- **The game's reads at cells other than message digests**: the verification's, at most
`verifyCalls`. -/
theorem readQCalls_muGameQ (θ : HPosN n → Digest) :
    IFreeM.IsChargeBound (realizeT θ (muGameT M upd valid A))
      (portCharge fun i ↦ if readQN M (n := n) i = true then 1 else 0) verifyCalls := by
  rw [readQCharge_eqN]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_muGameT 0 1 0 0 0 upd valid A hhash hsign θ)
    (le_of_eq (gameCallsQN_readQ q n total))

omit valid in
theorem advCalls_prefixQN (θ : HPosN n → Digest) :
    IFreeM.IsChargeBound (realizeT θ (prefixTN M upd A))
      (portCharge fun i ↦ if Quantum.Xmss.Assembly.extCls HashOutput HashDomain
        (Finset (HPosN n) × M) (recSpec (HPosN n) M) i then 0 else 1) q := by
  rw [advCharge_eqN]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_prefixTN 1 0 0 0 0 upd A hhash hsign θ)
    (le_of_eq (gameCallsQN_adv q n total))

omit valid in
theorem clsCalls_prefixQN (θ : HPosN n → Digest) :
    IFreeM.IsChargeBound (realizeT θ (prefixTN M upd A))
      (portCharge fun i ↦ if Quantum.Xmss.Assembly.extCls HashOutput HashDomain
        (Finset (HPosN n) × M) (recSpec (HPosN n) M) i then 1 else 0) (clsCapN n total) := by
  rw [clsCharge_eqN]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_prefixTN 0 1 1 1 1 upd A hhash hsign θ)
    (gameCallsQN_cls_le q n total)

omit valid in
theorem progCalls_prefixQN (θ : HPosN n → Digest) :
    IFreeM.IsChargeBound (realizeT θ (prefixTN M upd A))
      (portCharge (Quantum.Xmss.extProgCharge HashOutput HashDomain (Finset (HPosN n) × M)
        (recSpec (HPosN n) M))) (progCapN total) := by
  rw [progCharge_eqN]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_prefixTN 0 0 0 1 0 upd A hhash hsign θ)
    (le_of_eq (gameCallsQN_prog q n total))

omit valid in
theorem readQCalls_prefixQN (θ : HPosN n → Digest) :
    IFreeM.IsChargeBound (realizeT θ (prefixTN M upd A))
      (portCharge fun i ↦ if readQN M (n := n) i = true then 1 else 0) verifyCalls := by
  rw [readQCharge_eqN]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_prefixTN 0 1 0 0 0 upd A hhash hsign θ)
    (le_of_eq (gameCallsQN_readQ q n total))

end counts

/-! ## The game's reads keep the label

Mismatch's `KeepsLab` for the realized multi-user template game and its prefix. -/

section keepsLab

variable {M : Type} (upd : Fin n → TrialUpd M)

theorem keepsLab_progPosN (i : Fin n) (B : QReg) (ps : List Pos) :
    KeepsLab (progPosN M i B ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact keepsLab_progThen _ trivial _ ih

theorem keepsLab_selectTN (i : Fin n) (P : PublicParameter) (B : QReg) (l : Layer)
    (e : KeyIndex) (message : MsgBytes) (rnd : Pos) :
    KeepsLab (selectTN M upd i P B l e message rnd) :=
  keepsLab_revealThen _ _ fun _ ↦ keepsLab_readLift _

theorem keepsLab_publishTN (i : Fin n) (B : QReg) (l : Layer) (e : KeyIndex) (ρ : Randomizer)
    (x : Encoding) : KeepsLab (publishTN M i B l e ρ x) :=
  keepsLab_revealThen _ _ fun _ ↦ keepsLab₂_bind _ _ (keepsLab_progPosN i B _) fun _ ↦ trivial

theorem keepsLab_topTN (i : Fin n) (P : PublicParameter) (B : QReg) (r : SigningRequest)
    (h : Option TopSel) : KeepsLab (topTN M upd i P B r h) := by
  rcases h with _ | o
  · exact keepsLab_revealThen _ _ fun _ ↦ keepsLab_selectTN upd i P B _ _ _ _
  · trivial

theorem keepsLab_pubBothN (i : Fin n) (B : QReg) (r : SigningRequest) (gb gt : TopSel) :
    KeepsLab (pubBothN (publishTN M i B) r gb gt) := by
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  · trivial
  · trivial
  · trivial
  · exact keepsLab₂_bind _ _ (keepsLab_publishTN i B _ _ _ _) fun _ ↦
      keepsLab₂_bind _ _ (keepsLab_publishTN i B _ _ _ _) fun _ ↦ trivial

theorem keepsLab_signTN (i : Fin n) (P : PublicParameter) (B : QReg) (r : SigningRequest)
    (h : Option TopSel) : KeepsLab (signTN M upd i P B r h) := by
  unfold signTN signWithN
  refine keepsLab₂_bind _ _ (keepsLab_selectTN upd i P B _ _ _ _) fun gb ↦
    keepsLab₂_bind _ _ (keepsLab_topTN upd i P B r h) fun gt ↦ ?_
  rw [QuantumComp₂.map_eq_bind_pure]
  exact keepsLab₂_bind _ _ (keepsLab_pubBothN i B r gb gt) fun _ ↦ trivial

theorem keepsLab_challengeTN (P : Fin n → PublicParameter) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (memoSpec n) A) :
    KeepsLab (challengeTN M upd P A c) := by
  rcases c with o | ⟨_ | ⟨i, q⟩, E, ℓ⟩
  · exact keepsLab_readLift _
  · exact keepsLab_readLift _
  · exact keepsLab_bind _ _ (keepsLab₂_bind _ _ (keepsLab_act _) fun _ ↦
      keepsLab_signTN upd i (P i) _ q.1 q.2) fun _ _ ↦ trivial

attribute [local irreducible] xmssRom

/-- The challenge prefix's reads keep the label. -/
theorem keepsLab_prefixQN (A : MuAdversary n) : KeepsLab (prefixTN M upd A) :=
  keepsLab_revealThen _ _ fun _ ↦ keepsLab₂_bind _ _
    (keepsLab_substitute _ (keepsLab_challengeTN upd _) _) fun _ ↦ trivial

theorem keepsLab_verifyQN (valid : SignLog → Bool) (x : (Fin n → PublicKey) × MuRun n) :
    KeepsLab (verifyTN M valid x) := by
  unfold verifyTN
  generalize (readsProgram M _ (xmssRom.verify (x.1 x.2.1.1) x.2.1.2)).map Prod.fst = y
  exact keepsLab₂_bind _ _ (keepsLab_readLift _) fun _ ↦ trivial

/-- **The game's reads keep the label.** -/
theorem keepsLab_muGameQ (valid : SignLog → Bool) (A : MuAdversary n) :
    KeepsLab (muGameT M upd valid A) := by
  rw [muGameT_eq_prefixTN_bind]
  exact keepsLab₂_bind _ _ (keepsLab_prefixQN upd A) fun x ↦ keepsLab_verifyQN valid x

end keepsLab

end Quantum.Qrom.Xmss.Multi

end
