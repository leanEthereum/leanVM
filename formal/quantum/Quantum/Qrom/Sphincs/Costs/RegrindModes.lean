module

public import Quantum.Qrom.Sphincs.Costs.Ports
public import Quantum.Qrom.Sphincs.GameTFacts
public import Quantum.Xmss.Assembly.NoReuse

@[expose] public section

/-!
# Re-grinds: the search modes of leanSPHINCS's challenge prefix

The challenge prefix `prefixQ pol A θ` reads only the trials of its counter searches. Every key
`K` has one search at the hidden values `θ`: the seed `(tabOf θ).publicSeed`, the value the key
signs `(tabOf θ).valuePos (msgPos K)` and the trials `tcG θ K c`, from trial `0` until a
codeword. This file records that structure (the leanSPHINCS counterpart of leanXMSS's
`Quantum.Qrom.Xmss` `Costs/RegrindModes`, without randomizer bases).

* **The modes** (`SModeG`, `RgModeG`, `curG`, `rgOkZG`, `rgNxZG`): a mode is the current search
  (key and next trial, `SModeG.srch`, or none, `SModeG.free`) and the pairs the trial reads have
  returned so far. A read must be the next trial of the current search, or trial `0` of a key
  between searches (the key is read off the cell's encoding slot, `keyAtG`); after it the search
  stops at a codeword. A program hardwires a cell off the trial cells (`RgProgOkG`).
* **The prefix is moded** (`rgModed_prefixQG`), from every mode.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key keyOf msgPos)
open Quantum.Xmss.Hybrid (restrictTo LazyProg)
open Quantum.Xmss.Assembly (recHwSpec realizeT revealThen progThen readLift readLiftQ RevealVals
  liftRead tmplLens readLens ModedP modedP₂_bind modedP_bind modedP_cast_mode modeCmdOk
  modeCmdNx realizeT_bind realizeT_bind₂ realizeT_substitute)

attribute [local irreducible] sphincsRom

/-! ## The trials of a key -/

section trials

variable (θ : TVals)

/-- **Trial `c` of the search of `K`** at the hidden values `θ`: the encoding cell of `K` on the
value it signs. -/
def tcG (K : Key) (c : ℕ) : Qrom.HashDomain :=
  trialCell (tabOf θ).publicSeed K ((tabOf θ).valuePos (msgPos K)) c

theorem slotOf_tcG (K : Key) (c : ℕ) :
    slotOf (pkQ θ) (tcG θ K c) = some (.enc K.1 K.2.1 K.2.2) :=
  slotOf_trialCell (pkQ θ) K _ c

/-- The key of a cell at an encoding slot under `pkQ θ`. -/
def keyAtG (z : Qrom.HashDomain) : Option Key :=
  match slotOf (pkQ θ) z with
  | some (.enc l τ e) => some (l, τ, e)
  | _ => none

theorem keyAtG_tcG (K : Key) (c : ℕ) : keyAtG θ (tcG θ K c) = some K := by
  unfold keyAtG
  rw [slotOf_tcG]

end trials

/-! ## The modes -/

/-- The search part of a mode: between searches, or within the search of key `K` before trial
`j`. -/
inductive SModeG
  | free
  | srch (K : Key) (j : ℕ)

/-- **The modes of the challenge prefix**: the search, and the pairs the trial reads returned. -/
abbrev RgModeG : Type :=
  SModeG × (Qrom.HashDomain → Option PairOut)

/-- **The trial a read of the cell `z` makes**: within a search its next trial; between searches
trial `0` of the key of `z`'s encoding slot. -/
def curG (θ : TVals) : SModeG → Qrom.HashDomain → Option (Key × ℕ)
  | .srch K j, _ => some (K, j)
  | .free, z => (keyAtG θ z).map fun K ↦ (K, 0)

theorem curG_free_tcG (θ : TVals) (K : Key) : curG θ .free (tcG θ K 0) = some (K, 0) := by
  show (keyAtG θ (tcG θ K 0)).map _ = _
  rw [keyAtG_tcG]
  rfl

/-- **The mode after a read** of the cell `z` with outcome `o`: within the trial's search, the
search stops at a codeword and the next trial follows otherwise; the outcome is recorded. -/
noncomputable def rgStepG (θ : TVals) (μ : RgModeG) (z : Qrom.HashDomain) (o : Option PairOut) :
    RgModeG :=
  (curG θ μ.1 z).elim (.free, μ.2) fun p ↦
    (if Quantum.Sphincs.Codeword.Valid (pairDigest (o.getD 0)) then .free
      else .srch p.1 (p.2 + 1), Function.update μ.2 z o)

theorem rgStepG_of {θ : TVals} {μ : RgModeG} {z : Qrom.HashDomain} {K : Key} {j : ℕ}
    (h : curG θ μ.1 z = some (K, j)) (o : Option PairOut) :
    rgStepG θ μ z o =
      (if Quantum.Sphincs.Codeword.Valid (pairDigest (o.getD 0)) then .free
        else .srch K (j + 1), Function.update μ.2 z o) := by
  unfold rgStepG
  rw [h]
  try rfl

/-- **The mode after a read port** with result `r`. -/
noncomputable def rgRdNxG (θ : TVals) {M' : Type} (μ : RgModeG) :
    (c : HwRead PairOut Qrom.HashDomain M') → c.Result → RgModeG
  | .readH z _, r => rgStepG θ μ z r.1
  | _, _ => (.free, μ.2)

/-- A read of runtime 1 allowed by a search mode: the trial its cell makes, read with `cwUpd`. -/
def RdOk1G (θ : TVals) (σ : SModeG) (c : HwRead PairOut Qrom.HashDomain SelMem) : Prop :=
  ∃ K j, curG θ σ (tcG θ K j) = some (K, j) ∧ c = .readH (tcG θ K j) (cwUpd K (tcG θ K j))

/-- **A read of runtime 2 allowed by a search mode**: the trial read of the trial its cell
makes. -/
def RdOkG (θ : TVals) (σ : SModeG) (c : HwRead PairOut Qrom.HashDomain QMem) : Prop :=
  ∃ K j, curG θ σ (tcG θ K j) = some (K, j) ∧ c = trialRead (tcG θ K j) K

/-- **A program allowed by the modes**: of a cell off the trial cells. -/
def RgProgOkG (θ : TVals) (c : HwProg PairOut Qrom.HashDomain) : Prop :=
  ∃ z a, c = .programH z a ∧ ∀ K j, z ≠ tcG θ K j

/-- The calls of runtime 1 allowed by a mode. -/
def rgOk1G (θ : TVals) : RgModeG → (hwReadSpec PairOut Qrom.HashDomain SelMem).Port → Prop
  | _, .inl _ => True
  | μ, .inr c => RdOk1G θ μ.1 c

/-- The mode after a call of runtime 1. -/
noncomputable def rgNx1G (θ : TVals) : RgModeG →
    (i : (hwReadSpec PairOut Qrom.HashDomain SelMem).Port) →
    (hwReadSpec PairOut Qrom.HashDomain SelMem).Result i → RgModeG
  | μ, .inl _, _ => (.free, μ.2)
  | μ, .inr c, r => rgRdNxG θ μ c r

/-- The calls of the template allowed by a mode, at `θ`. -/
def rgOkTG (θ : TVals) : RgModeG → (SSpecQ SelMem).Port → Prop
  | _, .inl (.inl (.inl _)) => True
  | μ, .inl (.inl (.inr c)) => RdOkG θ μ.1 c.1
  | _, .inl (.inr p) => RgProgOkG θ (p.1.realize θ)
  | _, .inr _ => True

/-- The mode after a call of the template, at `θ`. -/
noncomputable def rgNxTG (θ : TVals) :
    RgModeG → (i : (SSpecQ SelMem).Port) → (SSpecQ SelMem).Result i → RgModeG
  | μ, .inl (.inl (.inr c)), r => rgRdNxG θ μ c.1 r
  | μ, _, _ => (.free, μ.2)

/-- **The calls of runtime 2 allowed by a mode**, at `θ`. -/
def rgOkZG (θ : TVals) : RgModeG → (RSpecS SelMem).Port → Prop
  | _, .inl (.inl (.inl _)) => True
  | μ, .inl (.inl (.inr c)) => RdOkG θ μ.1 c
  | _, .inl (.inr c) => RgProgOkG θ c
  | _, .inr _ => True

/-- **The mode after a call of runtime 2**, at `θ`: a read moves by its outcome, every other call
ends the search. -/
noncomputable def rgNxZG (θ : TVals) :
    RgModeG → (i : (RSpecS SelMem).Port) → (RSpecS SelMem).Result i → RgModeG
  | μ, .inl (.inl (.inr c)), r => rgRdNxG θ μ c r
  | μ, _, _ => (.free, μ.2)

/-! ## The programs of the prefix -/

section progs

variable (θ : TVals)

theorem rgProgOkG_progT {p : Pos} (hp : p.1.IsStruct) : RgProgOkG θ ((progT p).realize θ) := by
  rw [realize_progT hp (seedOf θ) θ]
  exact ⟨_, _, rfl, fun K j ↦ cellOf_ne_encCell (seedOf θ) (tabOf θ) p K.1 K.2.1 K.2.2 _ _⟩

theorem rgProgOkG_digPort (pol : DigestPolicy) (L : Finset TPos) (msg : Message) :
    RgProgOkG θ ((digPort pol L msg).realize θ) := by
  rw [realize_digPort, ← cellOf_digPos (seedOf θ)]
  exact ⟨_, _, rfl, fun K j ↦
    cellOf_ne_encCell (seedOf θ) (tabOf θ) (digPos msg) K.1 K.2.1 K.2.2 _ _⟩

end progs

/-! ## Runtime 1's searches, lifted -/

section lift

variable (θ : TVals)

/-- **The counter search is moded** from a mode in which its first read makes its trial. -/
theorem rgModed_grindTG (B : QReg) (K : Key) :
    ∀ n c (μ : RgModeG), curG θ μ.1 (tcG θ K c) = some (K, c) →
      ModedP (L := LocalSig.instruments) (rgOk1G θ) (rgNx1G θ) (fun _ _ ↦ True) μ
        (grindT SelMem cwUpd (tabOf θ).publicSeed B K ((tabOf θ).valuePos (msgPos K)) n c)
  | 0, _, _, _ => trivial
  | n + 1, c, μ, h => by
    rw [grindT]
    refine modedP₂_bind (F := fun r μ' ↦ μ' = rgRdNxG θ μ
        (.readH (tcG θ K c) (cwUpd K (tcG θ K c))) r)
      (F' := fun _ _ ↦ True) _ _ ⟨⟨K, c, h, rfl⟩, fun _ ↦ ⟨trivial, fun _ ↦ rfl⟩⟩
      fun r μ' hμ ↦ ?_
    subst hμ
    split
    · trivial
    · rename_i hd
      have hv : ¬Quantum.Sphincs.Codeword.Valid (pairDigest (r.1.getD 0)) :=
        Quantum.Sphincs.Codeword.decode_eq_none_iff.1 hd
      have e : rgRdNxG θ μ (.readH (tcG θ K c) (cwUpd K (tcG θ K c))) r =
          (.srch K (c + 1), Function.update μ.2 (tcG θ K c) r.1) := by
        show rgStepG θ μ (tcG θ K c) r.1 = _
        rw [rgStepG_of h, ite_eq_right hv]
      rw [e]
      exact rgModed_grindTG B K n (c + 1) _ rfl

/-- A sponge program of runtime 1 is moded from every mode. -/
theorem rgModed_liftOrdinaryG {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments (spongeSpec PairOut Qrom.HashDomain) Ω A) :
    ∀ μ : RgModeG, ModedP (rgOk1G θ) (rgNx1G θ) (fun _ _ ↦ True) μ
      (y.liftOrdinary (t := hwReadCmdSpec PairOut Qrom.HashDomain SelMem)) := by
  induction y using IFreeM.inductionOn with
  | pure _ a => exact fun _ ↦ trivial
  | liftBind _ c next ih =>
    intro μ
    show ModedP _ _ _ _ (IFreeM.mapLens QuantumComp.ordinaryLens (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ μ⟩
    · exact ⟨trivial, fun b ↦ ih _ _⟩

/-- **Lifting runtime 1's moded programs to templates.** -/
theorem rgModed_readLiftG {Ω : QReg → Type} {A : QReg} {fin : (Σ u, Ω u) → RgModeG → Prop}
    (y : QuantumComp LocalSig.instruments (hwReadSpec PairOut Qrom.HashDomain SelMem) Ω A)
    {μ : RgModeG} (hy : ModedP (rgOk1G θ) (rgNx1G θ) fin μ y) :
    ModedP (rgOkTG θ) (rgNxTG θ) fin μ (readLift goodQ y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ μ (IFreeM.mapLens (readLens goodQ) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨?_, fun b ↦ ?_⟩
      · obtain ⟨K, j, h, hc⟩ := hy.1
        subst hc
        exact ⟨K, j, h, rfl⟩
      · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;>
          exact ih _ (hy.2 (ULift.up (b.down.1, b.down.2.2)))

/-- **Realizing keeps the modes.** -/
theorem rgModed_realizeTG {Ω : QReg → Type} {A : QReg} {fin : (Σ u, Ω u) → RgModeG → Prop}
    (y : QuantumComp LocalSig.instruments (SSpecQ SelMem) Ω A) {μ : RgModeG}
    (hy : ModedP (rgOkTG θ) (rgNxTG θ) fin μ y) :
    ModedP (rgOkZG θ) (rgNxZG θ) fin μ (realizeT θ y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ μ (IFreeM.mapLens (tmplLens θ) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨((i | c) | ⟨p, hp⟩) | T, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · cases p <;> exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 (ULift.up (restrictTo T θ, b.down)))⟩

theorem rgModed_readLiftQG {B : QReg} {α : Type}
    (y : QComp (hwReadSpec PairOut Qrom.HashDomain SelMem) B B α) {μ : RgModeG}
    (hy : ModedP (rgOk1G θ) (rgNx1G θ) (fun _ _ ↦ True) μ y) :
    ModedP (rgOkZG θ) (rgNxZG θ) (fun _ _ ↦ True) μ (realizeT θ (readLiftQ goodQ y)) :=
  rgModed_realizeTG θ _ (rgModed_readLiftG θ y hy)

end lift

/-! ## The realized template pieces -/

section pieces

variable (θ : TVals)

/-- **A template whose realization is moded from every mode.** -/
def RgAnyG {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (SSpecQ SelMem) Ω A) : Prop :=
  ∀ μ : RgModeG, ModedP (rgOkZG θ) (rgNxZG θ) (fun _ _ ↦ True) μ (realizeT θ y)

variable {θ}

theorem rgAnyG_bind₂ {A B C : QReg} {α β : Type} {x : QComp (SSpecQ SelMem) A B α}
    {k : α → QComp (SSpecQ SelMem) B C β} (hx : RgAnyG θ x) (hk : ∀ a, RgAnyG θ (k a)) :
    RgAnyG θ (x.bind k) := by
  intro μ
  rw [realizeT_bind₂]
  exact modedP₂_bind (F := fun _ _ ↦ True) (F' := fun _ _ ↦ True) _ _ (hx μ) fun a μ' _ ↦ hk a μ'

variable (θ)

theorem rgAnyG_pure {A : QReg} {α : Type} (a : α) :
    RgAnyG θ (QuantumComp₂.pure (L := LocalSig.instruments) (spec := SSpecQ SelMem) (A := A) a) :=
  fun _ ↦ trivial

theorem rgAnyG_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    RgAnyG θ (QComp.act (spec := SSpecQ SelMem) p) :=
  fun _ ↦ ⟨trivial, fun _ ↦ trivial⟩

/-- **A realized reveal** ends the search. -/
theorem rgModed_revealThenG {B C : QReg} {α : Type} (T : Finset TPos)
    (k : RevealVals TVal T × QMem → QComp (SSpecQ SelMem) B C α) (μ : RgModeG)
    (hk : ∀ mem, ModedP (rgOkZG θ) (rgNxZG θ) (fun _ _ ↦ True) (.free, μ.2)
      (realizeT θ (k (restrictTo T θ, mem)))) :
    ModedP (rgOkZG θ) (rgNxZG θ) (fun _ _ ↦ True) μ (realizeT θ (revealThen goodQ T k)) := by
  have e : realizeT θ (revealThen goodQ T k) =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := RSpecS SelMem) (.inr T) B
        (Equiv.uniqueProd B Unit).symm fun mem ↦
          (QComp.act (A := QReg.of ((RSpecS SelMem).Out (.inr T) × B)) (B := B)
            (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
              realizeT θ (k (restrictTo T θ, mem)) :=
    rfl
  rw [e]
  exact ⟨trivial, fun b ↦ modedP₂_bind (F := fun _ μ' ↦ μ' = (SModeG.free, μ.2))
    (F' := fun _ _ ↦ True) _ _ ⟨trivial, fun _ ↦ rfl⟩ fun _ μ' h ↦ h ▸ hk b.down⟩

theorem rgAnyG_revealThen {B C : QReg} {α : Type} (T : Finset TPos)
    (k : RevealVals TVal T × QMem → QComp (SSpecQ SelMem) B C α)
    (hk : ∀ mem, RgAnyG θ (k (restrictTo T θ, mem))) : RgAnyG θ (revealThen goodQ T k) :=
  fun μ ↦ rgModed_revealThenG θ T k μ fun mem ↦ hk mem _

theorem rgAnyG_progThen {B C : QReg} {α : Type} (p : LazyProg PairOut Qrom.HashDomain TPos TVal)
    (hp : RgProgOkG θ (p.realize θ)) (k : QComp (SSpecQ SelMem) B C α) (hk : RgAnyG θ k) :
    RgAnyG θ (progThen p trivial k) := by
  intro μ
  have e : realizeT θ (progThen p trivial k) =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := RSpecS SelMem)
        (.inl (.inr (p.realize θ))) B (Equiv.uniqueProd B Unit).symm fun _ ↦
          (QComp.act (A := QReg.of ((RSpecS SelMem).Out (.inl (.inr (p.realize θ))) × B))
            (B := B) (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
              realizeT θ k :=
    rfl
  rw [e]
  exact ⟨hp, fun _ ↦ modedP₂_bind (F := fun _ _ ↦ True) (F' := fun _ _ ↦ True)
    _ _ ⟨trivial, fun _ ↦ trivial⟩ fun _ μ' _ ↦ hk μ'⟩

theorem rgAnyG_progPos (B : QReg) :
    ∀ ps : List Pos, (∀ p ∈ ps, p.1.IsStruct) → RgAnyG θ (progPos SelMem B ps)
  | [], _ => rgAnyG_pure θ ()
  | p :: ps, h => rgAnyG_progThen θ _ (rgProgOkG_progT θ (h p List.mem_cons_self)) _
      (rgAnyG_progPos B ps fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

/-- **A counter search** from its key's reveal. -/
theorem rgAnyG_selectT (B : QReg) (K : Key) :
    RgAnyG θ (selectT SelMem cwUpd (tabOf θ).publicSeed B K) := by
  intro μ
  rw [selectT]
  refine rgModed_revealThenG θ _ _ μ fun mem ↦ ?_
  have hb : (tabR (restrictTo {vcoord (msgPos K)} θ)).valuePos (msgPos K) =
      (tabOf θ).valuePos (msgPos K) :=
    valuePos_tabOf_congr _ (pairAt_extW_restrictTo (Finset.mem_singleton_self _) θ)
  dsimp only
  rw [hb]
  exact rgModed_readLiftQG θ _ (rgModed_grindTG θ B K _ 0 _ (curG_free_tcG θ K))

theorem rgAnyG_forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    RgAnyG θ (forsOpenT SelMem B idx lv) := by
  rw [forsOpenT]
  exact rgAnyG_revealThen θ _ _ fun _ ↦
    rgAnyG_bind₂ (rgAnyG_progPos θ B _ fun _ hp ↦ isStruct_of_mem_forsPos hp) fun _ ↦
      rgAnyG_pure θ _

theorem rgAnyG_publishT (B : QReg) (K : Key) (c : EncodingCounter) (x : Encoding) :
    RgAnyG θ (publishT SelMem B K c x) := by
  rw [publishT]
  exact rgAnyG_revealThen θ _ _ fun _ ↦
    rgAnyG_bind₂ (rgAnyG_progPos θ B _ fun _ hp ↦ isStruct_of_mem_layerPos hp) fun _ ↦
      rgAnyG_pure θ _

theorem rgAnyG_publishAllT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (R : Randomizer) (g₀ g₁ g₂ : Option (EncodingCounter × Encoding)) :
    RgAnyG θ (publishAllT SelMem B idx lv R g₀ g₁ g₂) := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try exact rgAnyG_pure θ _
  simp only [publishAllT]
  exact rgAnyG_bind₂ (rgAnyG_forsOpenT θ B idx lv) fun _ ↦
    rgAnyG_bind₂ (rgAnyG_publishT θ B _ _ _) fun _ ↦
      rgAnyG_bind₂ (rgAnyG_publishT θ B _ _ _) fun _ ↦
        rgAnyG_bind₂ (rgAnyG_publishT θ B _ _ _) fun _ ↦ rgAnyG_pure θ _

/-- **A signature is moded.** -/
theorem rgAnyG_signT (pol : DigestPolicy) (B : QReg) (msg : Message) :
    RgAnyG θ (signT SelMem cwUpd pol B msg) := by
  rw [signT]
  refine rgAnyG_revealThen θ _ _ fun mem₁ ↦ rgAnyG_revealThen θ _ _ fun mem₂ ↦ ?_
  have hs₀ : (tabR (restrictTo {seedC, rootC, rndC msg} θ)).publicSeed = (tabOf θ).publicSeed :=
    sigTabD_publicSeed msg
  dsimp only
  rw [hs₀]
  refine rgAnyG_progThen θ _ (rgProgOkG_digPort θ pol _ msg) _ ?_
  refine rgAnyG_bind₂ (rgAnyG_selectT θ B _) fun g₀ ↦ ?_
  refine rgAnyG_bind₂ (rgAnyG_selectT θ B _) fun g₁ ↦ ?_
  exact rgAnyG_bind₂ (rgAnyG_selectT θ B _) fun g₂ ↦ rgAnyG_publishAllT θ B _ _ _ g₀ g₁ g₂

/-- **The challenger is moded.** -/
theorem rgAnyG_challengeT (pol : DigestPolicy) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    RgAnyG θ (challengeT SelMem cwUpd pol A c) := by
  intro μ
  rcases c with o | ⟨_ | msg, E, ℓ⟩
  · exact rgModed_realizeTG θ _ (rgModed_readLiftG θ _ (rgModed_liftOrdinaryG θ _ μ))
  · exact rgModed_realizeTG θ _ (rgModed_readLiftG θ _ (rgModed_liftOrdinaryG θ _ μ))
  · change ModedP _ _ _ μ (realizeT θ (QuantumComp.bind
      (signAt SelMem cwUpd pol msg E ℓ) _))
    refine (congrArg (fun y ↦ ModedP (rgOkZG θ) (rgNxZG θ) (fun _ _ ↦ True) μ y)
      (realizeT_bind (good := goodQ) (M := SelMem) θ _ _)).mpr ?_
    exact modedP_bind _ _ (rgAnyG_bind₂ (rgAnyG_act θ _) (fun _ ↦ rgAnyG_signT θ pol _ msg) μ)
      fun _ _ _ _ ↦ trivial

/-- Substituting moded commands. -/
theorem rgModed_substituteG {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments spec)
      (QuantumComp.toIPFunctor LocalSig.instruments (RSpecS SelMem)))
    (hσ : ∀ A c μ, ModedP (rgOkZG θ) (rgNxZG θ) (fun _ _ ↦ True) μ (σ A c)) {Ω : QReg → Type}
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) :
    ∀ μ, ModedP (rgOkZG θ) (rgNxZG θ) (fun _ _ ↦ True) μ (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact fun _ ↦ trivial
  | liftBind s c next ih =>
    intro μ
    rw [IFreeM.substitute_liftBind]
    exact modedP_bind _ _ (hσ s c μ) fun u ans μ' _ ↦ (modedP_cast_mode ans.2 _ _).mpr
      (ih ans.1 μ')

/-- **The realized challenge prefix is moded**, from every mode. -/
theorem rgModed_prefixQG (pol : DigestPolicy) (A : SAdversary) (μ : RgModeG) :
    ModedP (rgOkZG θ) (rgNxZG θ) (fun _ _ ↦ True) μ (prefixQ pol A θ) := by
  unfold prefixQ prefixT
  refine rgModed_revealThenG θ _ _ μ fun mem ↦ ?_
  dsimp only
  rw [realizeT_bind₂]
  refine modedP₂_bind (F := fun _ _ ↦ True) (F' := fun _ _ ↦ True) _ _ ?_ fun _ _ _ ↦ trivial
  unfold challengedT
  have e := realizeT_substitute (good := goodQ) (M := SelMem) θ
    (challengeT SelMem cwUpd pol)
    (SufCma.withSignLog (A (tabR (restrictTo pkReveal θ)).publicKey))
  exact (congrArg (fun y ↦ ModedP (rgOkZG θ) (rgNxZG θ) (fun _ _ ↦ True) (.free, μ.2) y)
    e).mpr (rgModed_substituteG θ _ (fun A c ↦ rgAnyG_challengeT θ pol A c) _ _)

end pieces

end Quantum.Qrom.Sphincs

end
