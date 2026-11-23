module

public import Quantum.Sphincs.Assembly.HmsgCovers
public import Quantum.Sphincs.Assembly.GameTCalls

@[expose] public section

/-!
# The revealed randomizers' `H_msg` cells are hardwired at every sponge and read call

The template game at `msgPol` reveals a message's randomizer `.rnd M` only inside a signature,
which then (before any sponge or read call) programs both `H_msg` calls of `M` (`digestPorts`).
So at every sponge and read call, every message whose randomizer is in the memory label has its
`H_msg` cells hardwired (`HmInv`, `forallQueries_hmInv_gameT`). This is the invariant on which
the template's `H_msg` cells have the randomizers as sources
(`Quantum.Sphincs.Assembly.HmsgCoversMass`).

* **Pending ports** (`InvM`, `HM`): as GameTCalls' `InvP`, `HP`, for the ports `hmPortSet` of the
  messages whose randomizer is revealed; reveals and programs may be called with ports pending,
  sponge and read calls may not.
* **Per component** (`hm_readLift`, `hm_forsOpenT`, `hm_signLayerT`, `hm_signT`, `hm_challengeT`,
  `hm_gameT`); `forallQueries_of_hm` gives `ForallQueries` of `invSupp` for ports `Q` other than the
  program and record ports.
* **The cells** (`hmCells_hardwired`): on `HmInv`, a revealed randomizer's `H_msg` cells
  (`hmCellK`, `hmCellR`, `hmCellZ` at the hidden root and randomizer) are hardwired.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker

universe u v w w₁

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message Randomizer)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (LazyProg restrictTo ReadMono querySupportedOn_queryStep progUpdate
  capOf rateOf)
open Quantum.Xmss.Assembly (tmplSpec recHwSpec recSpec readLift readLens realizeT revealThen
  progThen RevealVals memLab liftRead CellHardwired cellHardwired_progUpdate
  cellHardwired_progUpdate_self invSupp runtimeR rnK_zero rnZ)
open Quantum.Sphincs.Hybrid (DLab)

namespace Quantum.Sphincs.Assembly

/- Membership in the concrete FORS opening's sets is otherwise decided by evaluating them. -/
attribute [local irreducible] forsNeed forsSlots

/-! ## The pending invariant -/

section pending

variable {M : Type}

/-- **The realized program ports of both `H_msg` calls of `msg`** at `msgPol`. -/
def hmPortSet (pub : Pub) (v : (s : HPos) → XD s) (msg : Message) : Set (HwProg X Z) :=
  {c | ∃ p ∈ digestPorts pub msgPol ∅ msg, p.realize v = c}

/-- **The pending invariant**: a message whose randomizer is in the memory label has each of its
realized `H_msg` ports hardwired or pending. -/
def InvM (pub : Pub) (v : (s : HPos) → XD s) (C : Set (HwProg X Z))
    (r : HwReg X Z (Finset HPos × M)) : Prop :=
  ∀ msg, HPos.rnd msg ∈ r.2.2.1 → ∀ c ∈ hmPortSet pub v msg, CellHardwired c r.2.1 ∨ c ∈ C

/-- The realized `H_msg` ports of the messages whose randomizer is in `T`. -/
def revealSetM (pub : Pub) (v : (s : HPos) → XD s) (T : Finset HPos) : Set (HwProg X Z) :=
  {c | ∃ msg, HPos.rnd msg ∈ T ∧ c ∈ hmPortSet pub v msg}

/-- **The invariant**: every message whose randomizer is in the memory label has its realized
`H_msg` ports hardwired. -/
def HmInv (pub : Pub) (v : (s : HPos) → XD s) (r : HwReg X Z (Finset HPos × M)) : Prop :=
  InvM pub v ∅ r

variable {pub : Pub} {v : (s : HPos) → XD s}

theorem invM_of_label_empty {C : Set (HwProg X Z)} {r : HwReg X Z (Finset HPos × M)}
    (h : r.2.2.1 = ∅) : InvM pub v C r := by
  intro msg hl
  rw [h] at hl
  exact absurd hl (Finset.notMem_empty _)

theorem invM_of_eq {C : Set (HwProg X Z)} {r r' : HwReg X Z (Finset HPos × M)}
    (h1 : r'.2.1 = r.2.1) (h2 : r'.2.2.1 = r.2.2.1) (hr : InvM pub v C r) : InvM pub v C r' := by
  intro msg hl c hc
  rw [h1]
  exact hr msg (h2 ▸ hl) c hc

theorem invM_prog {C : Set (HwProg X Z)} (c : HwProg X Z) {r r' : HwReg X Z (Finset HPos × M)}
    (h : r'.2 = (progUpdate c r.2.1, r.2.2)) (hr : InvM pub v C r) : InvM pub v (C \ {c}) r' := by
  intro msg hl c' hc'
  rw [h] at hl ⊢
  rcases hr msg hl c' hc' with h' | h'
  · exact Or.inl (cellHardwired_progUpdate h')
  · by_cases he : c' = c
    · rw [he]
      exact Or.inl (cellHardwired_progUpdate_self c _)
    · exact Or.inr ⟨h', he⟩

theorem invM_reveal {C : Set (HwProg X Z)} (T : Finset HPos)
    {r r' : HwReg X Z (Finset HPos × M)} (h : r'.2 = (r.2.1, (r.2.2.1 ∪ T, r.2.2.2)))
    (hr : InvM pub v C r) : InvM pub v (C ∪ revealSetM pub v T) r' := by
  intro msg hl c hc
  rw [h] at hl ⊢
  rcases Finset.mem_union.1 hl with hl | hl
  · exact (hr msg hl c hc).imp_right Or.inl
  · exact Or.inr (Or.inr ⟨msg, hl, hc⟩)

theorem revealSetM_valSet (T : Finset ValPos) : revealSetM pub v (valSet T) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun c ⟨msg, hm, _⟩ ↦ ?_
  obtain ⟨q, -, hq⟩ := Finset.mem_map.1 hm
  cases hq

theorem revealSetM_val (q : ValPos) : revealSetM pub v {.val q} = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun c ⟨msg, hm, _⟩ ↦ ?_
  cases Finset.mem_singleton.1 hm

theorem revealSetM_root_rnd (msg : Message) :
    revealSetM pub v {.val rootPos, .rnd msg} ⊆ hmPortSet pub v msg := by
  rintro c ⟨m, hm, hc⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, false_or] at hm
  cases hm
  exact hc

theorem revealSetM_msgPol_need (T : Finset HPos) (msg : Message) :
    revealSetM pub v (msgPol.need T msg) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun c ⟨m, hm, _⟩ ↦ ?_
  simp [DigestPolicy.need, msgPol] at hm

end pending

/-! ## Templates that keep the invariant -/

section hm

variable {M : Type} {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- The condition of `HM` on the pending set before a call: no pending port at a sponge or read
call, and the read keeps the label. -/
def portPreM : (SSpec M).Port → Set (HwProg X Z) → Prop
  | .inl (.inl (.inl _)), C => C = ∅
  | .inl (.inl (.inr c)), C => C = ∅ ∧ LabKeep c.1
  | .inl (.inr _), _ => True
  | .inr _, _ => True

/-- The pending set after a call. -/
def portPostM (pub : Pub) (v : (s : HPos) → XD s) :
    (SSpec M).Port → Set (HwProg X Z) → Set (HwProg X Z)
  | .inl (.inl (.inl _)), C => C
  | .inl (.inl (.inr _)), C => C
  | .inl (.inr p), C => C \ {p.1.realize v}
  | .inr T, C => C ∪ revealSetM pub v T

/-- The condition before a command. -/
def cmdPreM {A : QReg} : QuantumComp.Cmd L (SSpec M) A → Set (HwProg X Z) → Prop
  | .prim _, _ => True
  | .query i _ _, C => portPreM i C

/-- The pending set after a command. -/
def cmdPostM (pub : Pub) (v : (s : HPos) → XD s) {A : QReg} :
    QuantumComp.Cmd L (SSpec M) A → Set (HwProg X Z) → Set (HwProg X Z)
  | .prim _, C => C
  | .query i _ _, C => portPostM pub v i C

/-- **A template that keeps the invariant**, from the pending set `C` to the pending set `C'`. -/
def HM (pub : Pub) (v : (s : HPos) → XD s) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor L (SSpec M)) Ω A → Set (HwProg X Z) →
      Set (HwProg X Z) → Prop
  | _, .pure _, C, C' => C ⊆ C'
  | _, .liftBind c next, C, C' => cmdPreM c C ∧ ∀ b, HM pub v (next b) (cmdPostM pub v c C) C'

theorem cmdPreM_anti {A : QReg} (c : QuantumComp.Cmd L (SSpec M) A) {C D : Set (HwProg X Z)}
    (hD : D ⊆ C) (h : cmdPreM c C) : cmdPreM c D := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · trivial
  · exact Set.subset_empty_iff.1 (h ▸ hD)
  · exact ⟨Set.subset_empty_iff.1 (h.1 ▸ hD), h.2⟩
  · trivial
  · trivial

theorem cmdPostM_mono (pub : Pub) (v : (s : HPos) → XD s) {A : QReg}
    (c : QuantumComp.Cmd L (SSpec M) A) {C D : Set (HwProg X Z)} (hD : D ⊆ C) :
    cmdPostM pub v c D ⊆ cmdPostM pub v c C := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · exact hD
  · exact hD
  · exact hD
  · exact Set.sdiff_subset_sdiff_left hD
  · exact Set.union_subset_union_left _ hD

variable (pub : Pub) (v : (s : HPos) → XD s)

theorem hm_mono {A : QReg} (y : IFreeM (QuantumComp.toIPFunctor L (SSpec M)) Ω A)
    {C C' D D' : Set (HwProg X Z)} (hy : HM pub v y C C') (hD : D ⊆ C) (hD' : C' ⊆ D') :
    HM pub v y D D' := by
  induction y using IFreeM.inductionOn generalizing C D with
  | pure _ _ => exact hD.trans (hy.trans hD')
  | liftBind _ c next ih =>
    exact ⟨cmdPreM_anti c hD hy.1, fun b ↦ ih b (hy.2 b) (cmdPostM_mono pub v c hD)⟩

theorem hm_cast {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor L (SSpec M)) Ω A) (C C' : Set (HwProg X Z)) :
    HM pub v (e ▸ y) C C' ↔ HM pub v y C C' := by
  subst e
  rfl

theorem hm_bind {A : QReg} {Y : QReg → Type w₁}
    (x : IFreeM (QuantumComp.toIPFunctor L (SSpec M)) Ω A)
    (g : ∀ u, Ω u → IFreeM (QuantumComp.toIPFunctor L (SSpec M)) Y u)
    {C D C' : Set (HwProg X Z)} (hx : HM pub v x C D) (hg : ∀ u a, HM pub v (g u a) D C') :
    HM pub v (x.bind g) C C' := by
  induction x using IFreeM.inductionOn generalizing C with
  | pure _ a => exact hm_mono pub v _ (hg _ a) hx subset_rfl
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

theorem hm₂_bind {A B B' : QReg} {α : Type w} {β : Type w₁}
    (x : QuantumComp₂ L (SSpec M) A B α) (g : α → QuantumComp₂ L (SSpec M) B B' β)
    {C D C' : Set (HwProg X Z)} (hx : HM pub v x C D) (hg : ∀ a, HM pub v (g a) D C') :
    HM pub v (x.bind g) C C' := by
  refine hm_bind pub v x _ hx fun u p ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hg a

theorem hm_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor L spec)
      (QuantumComp.toIPFunctor L (SSpec M)))
    (hσ : ∀ A c, HM pub v (σ A c) ∅ ∅) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor L spec) Ω A) : HM pub v (x.substitute σ) ∅ ∅ := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind s c next ih =>
    rw [IFreeM.substitute_liftBind]
    exact hm_bind pub v _ _ (hσ s c) fun u ans ↦ (hm_cast pub v ans.2 _ _ _).mpr (ih ans.1)

theorem hm_readLift {A : QReg} (y : QuantumComp L (hwReadSpec X Z M) Ω A) :
    HM pub v (readLift goodAll y) ∅ ∅ := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind _ c next ih =>
    show HM pub v (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next)) ∅ ∅
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · refine ⟨trivial, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨rfl, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨⟨rfl, labKeep_liftRead c⟩, fun b ↦ ?_⟩
      dsimp only
      exact ih _

theorem hm_act {A B : QReg} {α : Type} (p : SubInstrument A B α) (C : Set (HwProg X Z)) :
    HM pub v (QComp.act (spec := SSpec M) p) C C :=
  ⟨trivial, fun _ ↦ subset_rfl⟩

/-- A reveal adds the ports of the messages whose randomizer it reveals. -/
theorem hm_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (SSpec M) B B' α)
    {C C' : Set (HwProg X Z)} (hk : ∀ r, HM pub v (k r) (C ∪ revealSetM pub v T) C') :
    HM pub v (revealThen goodAll T k) C C' :=
  ⟨trivial, fun r ↦ hm₂_bind pub v _ _ (hm_act pub v _ _) fun _ ↦ hk r.down⟩

theorem hm_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (SSpec M) B B' α) {C C' : Set (HwProg X Z)}
    (hk : HM pub v k (C \ {p.realize v}) C') : HM pub v (progThen p hp k) C C' :=
  ⟨trivial, fun _ ↦ hm₂_bind pub v _ _ (hm_act pub v _ _) fun _ ↦ hk⟩

theorem hm_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) (C : Set (HwProg X Z)) :
    HM pub v (progPorts M B ps) C (C \ {c | ∃ p ∈ ps, p.realize v = c}) := by
  induction ps generalizing C with
  | nil => exact fun c hc ↦ ⟨hc, fun ⟨_, hp, _⟩ ↦ absurd hp List.not_mem_nil⟩
  | cons p ps ih =>
    refine hm_progThen pub v p trivial _ (hm_mono pub v _ (ih _) subset_rfl ?_)
    rintro c ⟨⟨hc, hne⟩, hn⟩
    refine ⟨hc, ?_⟩
    rintro ⟨p', hp', rfl⟩
    rcases List.mem_cons.1 hp' with rfl | hp'
    · exact hne (Set.mem_singleton _)
    · exact hn ⟨p', hp', rfl⟩

theorem hm_progSlots (B : QReg) (ss : List Slot) (C : Set (HwProg X Z)) :
    HM pub v (progSlots M pub B ss) C C := by
  induction ss generalizing C with
  | nil => exact subset_rfl
  | cons s ss ih =>
    exact hm₂_bind pub v _ _ (hm_mono pub v _ (hm_progPorts pub v B (slotPorts pub s) C)
      subset_rfl Set.sdiff_subset) fun _ ↦ ih C

theorem hm_forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    HM pub v (forsOpenT M pub B idx lv) ∅ ∅ :=
  hm_revealThen pub v _ _ fun _ ↦ hm₂_bind pub v _ _
    (hm_mono pub v _ (hm_progSlots pub v B _ ∅) (by rw [revealSetM_valSet, Set.union_empty])
      subset_rfl) fun _ ↦ subset_rfl

variable (upd : TrialUpd M)

theorem hm_signLayerT (B : QReg) (K : Key) : HM pub v (signLayerT M upd pub B K) ∅ ∅ := by
  refine hm_revealThen pub v _ _ fun _ ↦ hm_mono pub v _
    (hm₂_bind pub v _ _ (hm_readLift pub v _) fun g ↦ ?_)
    (by rw [revealSetM_val, Set.union_empty]) subset_rfl
  rcases g with _ | ⟨cnt, x⟩
  · exact subset_rfl
  · exact hm_revealThen pub v _ _ fun _ ↦ hm₂_bind pub v _ _
      (hm_mono pub v _ (hm_progSlots pub v B _ ∅) (by rw [revealSetM_valSet, Set.union_empty])
        subset_rfl) fun _ ↦ subset_rfl

/-- `msgPol`'s digest ports do not depend on the label. -/
theorem digestPorts_msgPol (T : Finset HPos) (msg : Message) :
    digestPorts pub msgPol T msg = digestPorts pub msgPol ∅ msg :=
  rfl

/-- **A signature keeps the invariant**: the reveal of the randomizer makes the message's `H_msg`
ports pending, the digest's reveal adds none, the `H_msg` programs remove them, then the FORS
opening and the three layer signatures. -/
theorem hm_signT (B : QReg) (msg : Message) : HM pub v (signT M upd msgPol pub B msg) ∅ ∅ := by
  refine hm_revealThen pub v _ _ fun r₁ ↦ hm_revealThen pub v _ _ fun r₂ ↦ ?_
  refine hm₂_bind pub v _ _ (D := ∅)
    (hm_mono pub v _ (hm_progPorts pub v B _ _) subset_rfl (D' := ∅) ?_) fun _ ↦ ?_
  · rintro c ⟨hc, hn⟩
    rw [revealSetM_msgPol_need, Set.union_empty, Set.empty_union] at hc
    obtain ⟨p, hp, rfl⟩ := revealSetM_root_rnd msg hc
    exact hn ⟨p, (digestPorts_msgPol pub _ msg).symm ▸ hp, rfl⟩
  refine hm₂_bind pub v _ _ (hm_forsOpenT pub v B _ _) fun _ ↦ ?_
  refine hm₂_bind pub v _ _ (hm_signLayerT pub v upd B _) fun s₀ ↦ ?_
  rcases s₀ with _ | bottom
  · exact subset_rfl
  · refine hm₂_bind pub v _ _ (hm_signLayerT pub v upd B _) fun s₁ ↦ ?_
    rcases s₁ with _ | middle
    · exact subset_rfl
    · refine hm₂_bind pub v _ _ (hm_signLayerT pub v upd B _) fun s₂ ↦ ?_
      rcases s₂ with _ | top <;> exact subset_rfl

theorem hm_challengeT (A : QReg) (c : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    HM pub v (challengeT M upd msgPol pub A c) ∅ ∅ := by
  rcases c with o | ⟨p | msg, E, ℓ⟩
  · exact hm_readLift pub v _
  · exact hm_readLift pub v _
  · exact hm_bind pub v _ _ (hm₂_bind pub v _ _ (hm_act pub v _ _) fun _ ↦
      hm_signT pub v upd _ msg) fun _ _ ↦ subset_rfl

theorem hm_gameT (A : SAdversary) : HM pub v (gameT M upd msgPol pub A) ∅ ∅ :=
  hm_revealThen pub v _ _ fun _ ↦ hm_mono pub v _
    (hm₂_bind pub v _ _ (hm_substitute pub v _ (hm_challengeT pub v upd) _) fun _ ↦
      hm₂_bind pub v _ _ (hm_readLift pub v _) fun _ ↦ subset_rfl)
    (by rw [revealSetM_val, Set.union_empty]) subset_rfl

end hm

/-! ## `ForallQueries` of the invariant -/

section fq

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- One call of a realized program on the pending invariant. -/
theorem forallQueries_queryBind_of_stepInvM {Q : (recHwSpec X Z HPos M).Port → Prop}
    (m₀ : Finset HPos × M) (I : L.Interp) (pub : Pub) (v : (s : HPos) → XD s) {A : QReg}
    (i : (recHwSpec X Z HPos M).Port) (E : QReg) (ℓ : A ≃ (recHwSpec X Z HPos M).In i × E)
    (k' : (recHwSpec X Z HPos M).Result i → QuantumComp L (recHwSpec X Z HPos M) Ω
      (QReg.of ((recHwSpec X Z HPos M).Out i × E)))
    {C C' : Set (HwProg X Z)} (hpre : Q i → C = ∅)
    (hstep : StepR m₀ i (fun s ↦ InvM pub v C s) (fun s ↦ InvM pub v C' s))
    (hk : ∀ r ρ', QuerySupportedOn (fun m : QReg.of ((recHwSpec X Z HPos M).Out i × E) ×
        (runtimeR m₀).D ↦ m.2) {s | InvM pub v C' s} ρ' →
      (runtimeR m₀).ForallQueries I (invSupp (runtimeR m₀) Q (HmInv pub v)) (k' r) ρ')
    (ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ)
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | InvM pub v C s} ρ) :
    (runtimeR m₀).ForallQueries I (invSupp (runtimeR m₀) Q (HmInv pub v))
      (QuantumComp.queryBind i E ℓ k') ρ :=
  forallQueries_queryBind_of_stepR (Sup := invSupp (runtimeR m₀) Q (HmInv pub v))
    (P := fun s ↦ InvM pub v C s) (P' := fun s ↦ InvM pub v C' s) m₀ I i E ℓ k'
    (fun _ hρ hq a ha ↦ relabel_diag_eq_zero_of_supp m₀ E ℓ (hpre hq ▸ hρ) a ha) hstep hk ρ hρ

/-- **The realized program of a template keeping the invariant presents, at every call of the
ports `Q` (no program or record port), only states of the invariant.** -/
theorem forallQueries_of_hm {Q : (recHwSpec X Z HPos M).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (hQr : ∀ T, ¬Q (.inr T)) (m₀ : Finset HPos × M)
    (I : L.Interp) (pub : Pub) (v : (s : HPos) → XD s) {A : QReg}
    (y : QuantumComp L (SSpec M) Ω A) :
    ∀ C C', HM pub v y C C' → ∀ ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | InvM pub v C s} ρ →
      (runtimeR m₀).ForallQueries I (invSupp (runtimeR m₀) Q (HmInv pub v))
        (realizeT v y) ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _ _ _; trivial
  | primBind _ o k ih =>
    intro C C' hy ρ hρ b
    exact ih b C C' (hy.2 (ULift.up b)) _ (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _)
  | queryBind _ i E ℓ k ih =>
    intro C C' hy ρ hρ
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · exact forallQueries_queryBind_of_stepInvM m₀ I pub v (.inl (.inl (.inl i))) E ℓ
        (fun r ↦ realizeT v (k r)) (fun _ ↦ hy.1)
        (stepR_sponge m₀ i fun _ _ he hr ↦ invM_of_eq (congrArg Prod.fst he)
          (congrArg (fun t ↦ t.2.1) he) hr)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepInvM m₀ I pub v (.inl (.inl (.inr c.1))) E ℓ
        (fun r ↦ realizeT v (k r)) (fun _ ↦ hy.1.1)
        (stepR_readKeep m₀ c hy.1.2 fun _ _ h1 h2 hr ↦ invM_of_eq h1 h2 hr)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · cases p with
      | programH T₀ c =>
        exact forallQueries_queryBind_of_stepInvM m₀ I pub v
          (.inl (.inr ((LazyProg.programH T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepR_prog m₀ _ fun _ _ h hr ↦ invM_prog _ h hr)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK T₀ c =>
        exact forallQueries_queryBind_of_stepInvM m₀ I pub v
          (.inl (.inr ((LazyProg.programK T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepR_prog m₀ _ fun _ _ h hr ↦ invM_prog _ h hr)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK' T₀ c =>
        exact forallQueries_queryBind_of_stepInvM m₀ I pub v
          (.inl (.inr ((LazyProg.programK' T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepR_prog m₀ _ fun _ _ h hr ↦ invM_prog _ h hr)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepInvM m₀ I pub v (.inr T) E ℓ
        (fun m ↦ realizeT v (k (restrictTo T v, m))) (fun hq ↦ absurd hq (hQr _))
        (stepR_rec m₀ T fun _ _ h hr ↦ invM_reveal T h hr)
        (fun m ↦ ih (restrictTo T v, m) _ C' (hy.2 (ULift.up (restrictTo T v, m)))) ρ hρ

variable (upd : TrialUpd M)

/-- **The invariant along the realized game at `msgPol`**, from states with an empty memory label,
at the calls of ports `Q` other than the program and record ports. -/
theorem forallQueries_hmInv_gameT {Q : (recHwSpec X Z HPos M).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (hQr : ∀ T, ¬Q (.inr T)) (m₀ : Finset HPos × M) (pub : Pub)
    (A : SAdversary) (v : (s : HPos) → XD s)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ)
    (hρ : QuerySupportedOn (fun a : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      a.2.2.2.1) {∅} ρ) :
    (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m₀) Q (HmInv pub v)) (realizeT v (gameT M upd msgPol pub A)) ρ :=
  forallQueries_of_hm hQ hQr m₀ _ pub v _ ∅ ∅ (hm_gameT pub v upd A) ρ
    (hρ.imp fun _ ha ↦ invM_of_label_empty (Set.mem_singleton_iff.1 ha))

end fq

/-! ## The hardwired cells -/

section cells

variable {M : Type} (pub : Pub) (v : (s : HPos) → XD s)

/-- **The realized `H_msg` ports program the `H_msg` cells** at the hidden root and randomizer. -/
theorem hmCells_mem_hmPortSet (msg : Message) (i : DigestCall) :
    (∃ a, HwProg.programK (hmCellK pub (rootV v) (v (.rnd msg)) (msg, i)) a ∈
        hmPortSet pub v msg) ∧
      (∃ a, HwProg.programK' (hmCellR pub (rootV v) (v (.rnd msg)) (msg, i)) a ∈
        hmPortSet pub v msg) ∧
      ∃ a, HwProg.programH (hmCellZ pub (rootV v) (v (.rnd msg)) (msg, i)) a ∈
        hmPortSet pub v msg := by
  set b := slotBlk pub.seed (.hmsg (v (.rnd msg)) msg i) (valsOf v) with hb
  have hmem : ∀ c ∈ pathCells pub b (cor256 (hashOut _ (v (msgPol.out ∅ msg i)))) 1,
      c ∈ hmPortSet pub v msg := fun c hc ↦ by
    rw [hb, ← realize_hmsgPorts pub msgPol ∅ msg i v] at hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    refine ⟨p, ?_, rfl⟩
    fin_cases i
    · exact List.mem_append_left _ hp
    · exact List.mem_append_right _ hp
  obtain ⟨m1, m2, m3⟩ := mem_pathCells_round pub b
    (cor256 (hashOut _ (v (msgPol.out ∅ msg i)))) (Nat.zero_lt_one)
  have hb0 : b 0 = hmCellK pub (rootV v) (v (.rnd msg)) (msg, i) :=
    slotBlk_hmsg_zero pub.seed _ msg i _
  refine ⟨?_, ?_, ?_⟩
  · have h := hmem _ m1
    rw [show (cellK pub b 0).1 = hmCellK pub (rootV v) (v (.rnd msg)) (msg, i) from
      (rnK_zero _ _ _ _ _).trans hb0] at h
    exact ⟨_, h⟩
  · have h := hmem _ m2
    rw [show (cellK' pub b 0).1 = hmCellR pub (rootV v) (v (.rnd msg)) (msg, i) from
      (rnR_zero pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 b).trans (by rw [hb0]; rfl)] at h
    exact ⟨_, h⟩
  · have h := hmem _ m3
    rw [cellH_fst, show rnZ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 b 0 =
      hmCellZ pub (rootV v) (v (.rnd msg)) (msg, i) from
      (rnZ_zero pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 b).trans
        (congrArg (capOf pub.keys.2.1 pub.keys.2.2 pub.perm) hb0)] at h
    exact ⟨_, h⟩

/-- **On the invariant, a revealed randomizer's `H_msg` cells are hardwired.** -/
theorem hmCells_hardwired {r : HwReg X Z (Finset HPos × M)} (hr : HmInv pub v r)
    {msg : Message} (hm : HPos.rnd msg ∈ r.2.2.1) (i : DigestCall) :
    r.2.1.2.1 (hmCellK pub (rootV v) (v (.rnd msg)) (msg, i)) ≠ none ∧
      r.2.1.2.2 (hmCellR pub (rootV v) (v (.rnd msg)) (msg, i)) ≠ none ∧
      r.2.1.1 (hmCellZ pub (rootV v) (v (.rnd msg)) (msg, i)) ≠ none := by
  obtain ⟨⟨a1, h1⟩, ⟨a2, h2⟩, ⟨a3, h3⟩⟩ := hmCells_mem_hmPortSet pub v msg i
  refine ⟨?_, ?_, ?_⟩
  · exact (hr msg hm _ h1).resolve_right (Set.notMem_empty _)
  · exact (hr msg hm _ h2).resolve_right (Set.notMem_empty _)
  · exact (hr msg hm _ h3).resolve_right (Set.notMem_empty _)

end cells

end Quantum.Sphincs.Assembly

end
