module

public import Quantum.Qrom.Xmss.Costs.Ports
public import Quantum.Xmss.Assembly.NoReuse

@[expose] public section

/-!
# Re-grinds: the search modes and the bottom reveals of the challenge prefix

The challenge prefix `prefixQ A θ` reads only the trials of its randomizer searches, one search
after each reveal of a randomizer base. This file records that structure.

* **The modes** (`SMode`, `RgMode`, `rgOkZ`, `rgNxZ`): a mode is the current search (key, message,
  base and next trial, `SMode.srch`, or none, `SMode.free`) and the values the trial reads have
  returned so far. A read must be the next trial of the current search; after it the search
  stops at a codeword. A reveal of a single randomizer base starts the search of its key from
  that base (`rgRnd`, `rgRev`); a reveal of a top base carries the canonical bottom root
  (`RgRevOk`, `rgRoot`); a program hardwires a cell off the message slots (`RgProgOk`).
* **The prefix is moded** (`rgModed_prefixQ`), from every mode.
* **The bottom reveals** (`BotRev`, `botRevCharge`, `chgBot_prefixQ`): the record ports revealing
  a bottom base of key `e` cost one (reads and programs of other forms too); against an adversary
  that reuses no leaf (`NoLeafReuse`) the realized prefix costs at most one.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid HashSig LeanXmss
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT revealThen progThen readLift
  readLiftQ RevealVals liftRead tmplLens readLens ModedP modedP₂_bind modedP_bind
  modedP_cast_mode modeCmdOk modeCmdNx chg_act isChargeBound_zero isChargeBound_mono_charge
  realizeT_bind realizeT_bind₂ realizeT_substitute)

attribute [local irreducible] xmssRom

/-! ## The modes -/

/-- The search part of a mode: between searches, or within the search of key `e` of layer `l` on
`msg` from the base `base`, before trial `j`. -/
inductive SMode
  | free
  | srch (l : Layer) (e : KeyIndex) (msg : MsgBytes) (base : Randomizer) (j : ℕ)

/-- **The modes of the challenge prefix**: the search, and the values the trial reads returned. -/
abbrev RgMode : Type :=
  SMode × (HashDomain → Option HashOutput)

/-- The root of the bottom tree under the top key `b` (`QTable.bottomRoot` of its leaves). -/
def rgRoot (θ : HPos → Digest) (b : KeyIndex) : Digest :=
  (tabOf θ).treeValue bottomLayer layerHeight b.val

theorem bottomRoot_tabOf (θ : HPos → Digest) (i : LeafIndex) :
    (tabOf θ).bottomRoot i = rgRoot θ (keyIndexOnLayer i topLayer) :=
  rfl

/-- The search a reveal of the coordinate `loC p` starts: from a randomizer base, the search of
its key from the base's digest at trial `0`. -/
def rgRnd (θ : HPos → Digest) : Pos → SMode
  | .rndBottom e m =>
    .srch bottomLayer e (messageBytes m) (truncateHash (tabOf θ (.rndBottom e m))) 0
  | .rndTop b d => .srch topLayer b (rootBytes d) (truncateHash (tabOf θ (.rndTop b d))) 0
  | _ => .free

/-- The search a reveal of `T` starts: that of a single coordinate `loC p`, none otherwise. -/
noncomputable def rgRev (θ : HPos → Digest) (T : Finset HPos) : SMode :=
  @dite _ (∃ p, T = {loC p}) (Classical.propDecidable _) (fun h ↦ rgRnd θ h.choose)
    fun _ ↦ .free

theorem loC_injective : Function.Injective loC :=
  fun _ _ h ↦ Option.some.inj (congrArg Prod.fst h)

theorem rgRev_loC (θ : HPos → Digest) (p : Pos) : rgRev θ {loC p} = rgRnd θ p := by
  have h : ∃ q, ({loC p} : Finset HPos) = {loC q} := ⟨p, rfl⟩
  unfold rgRev
  rw [dite_eq_left h]
  exact congrArg (rgRnd θ) (loC_injective (Finset.singleton_injective h.choose_spec)).symm

theorem rgRev_cases (θ : HPos → Digest) (T : Finset HPos) :
    rgRev θ T = .free ∨ ∃ p, T = {loC p} ∧ rgRev θ T = rgRnd θ p := by
  by_cases h : ∃ p, T = {loC p}
  · obtain ⟨p, rfl⟩ := h
    exact .inr ⟨p, rfl, rgRev_loC θ p⟩
  · left
    unfold rgRev
    rw [dite_eq_right h]

/-- **The mode after a read** with outcome `r`: within a search, the search stops at a codeword
and the next trial follows otherwise; the read cell's outcome is recorded. -/
noncomputable def rgRdNx {M' : Type} (μ : RgMode) :
    (c : HwRead HashOutput HashDomain M') → c.Result → RgMode
  | .readH z _, r =>
    match μ.1 with
    | .srch l e msg base j =>
      (if Codeword.Valid (truncateHash (r.1.getD 0)) then .free else .srch l e msg base (j + 1),
        Function.update μ.2 z r.1)
    | .free => (.free, μ.2)
  | _, _ => (.free, μ.2)

theorem rgRdNx_srch {M' : Type} (l : Layer) (e : KeyIndex) (msg : MsgBytes) (base : Randomizer)
    (j : ℕ) (rd : HashDomain → Option HashOutput) (z : HashDomain)
    (u : M' → Option HashOutput → M')
    (r : (HwRead.readH z u : HwRead HashOutput HashDomain M').Result) :
    rgRdNx (.srch l e msg base j, rd) (.readH z u) r =
      (if Codeword.Valid (truncateHash (r.1.getD 0)) then .free else .srch l e msg base (j + 1),
        Function.update rd z r.1) :=
  rfl

theorem rgRdNx_trial (l : Layer) (e : KeyIndex) (msg : MsgBytes) (base : Randomizer) (j : ℕ)
    (rd : HashDomain → Option HashOutput) (z : HashDomain) (l' : Layer) (e' : KeyIndex)
    (r : (trialRead z l' e').Result) :
    rgRdNx (.srch l e msg base j, rd) (trialRead z l' e') r =
      (if Codeword.Valid (truncateHash (r.1.getD 0)) then .free else .srch l e msg base (j + 1),
        Function.update rd z r.1) :=
  rfl

/-- A read of runtime 1 allowed by a search: its next trial. -/
def rgRdOk1 (P : PublicParameter) : SMode → HwRead HashOutput HashDomain SelMem → Prop
  | .srch l e msg base j, c =>
    c = .readH (trialCell P l e msg base j) (cwUpd l e (trialCell P l e msg base j))
  | .free, _ => False

/-- A read of runtime 2 allowed by a search: the trial read of its next trial. -/
def rgRdOk (P : PublicParameter) : SMode → HwRead HashOutput HashDomain QMem → Prop
  | .srch l e msg base j, c => c = trialRead (trialCell P l e msg base j) l e
  | .free, _ => False

/-- A program allowed by the modes: of a cell off the message slots. -/
def RgProgOk (c : HwProg HashOutput HashDomain) : Prop :=
  ∃ z a, c = .programH z a ∧ ∀ l e, slotOf z ≠ some (.msg l e)

/-- A reveal allowed by the modes: a reveal of a top base carries the canonical bottom root. -/
def RgRevOk (θ : HPos → Digest) (T : Finset HPos) : Prop :=
  ∀ b d, T = {loC (.rndTop b d)} → d = rgRoot θ b

/-- The calls of runtime 1 allowed by a mode. -/
def rgOk1 (P : PublicParameter) : RgMode → (hwReadSpec HashOutput HashDomain SelMem).Port → Prop
  | _, .inl _ => True
  | μ, .inr c => rgRdOk1 P μ.1 c

/-- The mode after a call of runtime 1. -/
noncomputable def rgNx1 : RgMode → (i : (hwReadSpec HashOutput HashDomain SelMem).Port) →
    (hwReadSpec HashOutput HashDomain SelMem).Result i → RgMode
  | μ, .inl _, _ => (.free, μ.2)
  | μ, .inr c, r => rgRdNx μ c r

/-- The calls of the template allowed by a mode, at `θ`. -/
def rgOkT (θ : HPos → Digest) : RgMode → (XSpec SelMem).Port → Prop
  | _, .inl (.inl (.inl _)) => True
  | μ, .inl (.inl (.inr c)) => rgRdOk (tabOf θ).param μ.1 c.1
  | _, .inl (.inr p) => RgProgOk (p.1.realize θ)
  | _, .inr T => RgRevOk θ T

/-- The mode after a call of the template, at `θ`. -/
noncomputable def rgNxT (θ : HPos → Digest) :
    RgMode → (i : (XSpec SelMem).Port) → (XSpec SelMem).Result i → RgMode
  | μ, .inl (.inl (.inr c)), r => rgRdNx μ c.1 r
  | μ, .inr T, _ => (rgRev θ T, μ.2)
  | μ, _, _ => (.free, μ.2)

/-- **The calls of runtime 2 allowed by a mode**, at `θ`. -/
def rgOkZ (θ : HPos → Digest) : RgMode → (RSpec SelMem).Port → Prop
  | _, .inl (.inl (.inl _)) => True
  | μ, .inl (.inl (.inr c)) => rgRdOk (tabOf θ).param μ.1 c
  | _, .inl (.inr c) => RgProgOk c
  | _, .inr T => RgRevOk θ T

/-- **The mode after a call of runtime 2**, at `θ`. -/
noncomputable def rgNxZ (θ : HPos → Digest) :
    RgMode → (i : (RSpec SelMem).Port) → (RSpec SelMem).Result i → RgMode
  | μ, .inl (.inl (.inr c)), r => rgRdNx μ c r
  | μ, .inr T, _ => (rgRev θ T, μ.2)
  | μ, _, _ => (.free, μ.2)

/-! ## The coordinates the reveals carry -/

theorem vcoord_ne_rnd (q : Quantum.Xmss.Pos) :
    (∀ e m, vcoord q ≠ loC (.rndBottom e m)) ∧ ∀ b d, vcoord q ≠ loC (.rndTop b d) := by
  rcases q with ⟨l, e, i, _ | j⟩ | ⟨l, _ | level, idx⟩ <;>
    simp only [vcoord, loC, paramC] <;> (try split_ifs) <;> simp

theorem rgRevOk_of_paramC (θ : HPos → Digest) {T : Finset HPos} (h : paramC ∈ T) :
    RgRevOk θ T := by
  intro b d hT
  rw [hT, Finset.mem_singleton] at h
  exact absurd (loC_injective h) fun h' ↦ by cases h'

theorem paramC_mem_layerReveal (l : Layer) (e : KeyIndex) (x : Encoding) :
    paramC ∈ layerReveal l e x :=
  Finset.mem_union_left _ (Finset.mem_union_left _ (progNeed_subset_needUnion (p := .leaf l e)
    (List.mem_append_right _ List.mem_cons_self)
    (cellNeed_subset_progNeed _ (paramC_mem_cellNeed _))))

theorem rgRevOk_rndBottom (θ : HPos → Digest) (e : KeyIndex) (m : Message) :
    RgRevOk θ {loC (.rndBottom e m)} := by
  intro b d hT
  exact absurd (loC_injective (Finset.singleton_injective hT)) fun h' ↦ by cases h'

theorem rgRevOk_rndTop (θ : HPos → Digest) (r : SigningRequest) :
    RgRevOk θ {loC (.rndTop (keyIndexOnLayer r.leafIndex topLayer)
      ((tabOf θ).bottomRoot r.leafIndex))} := by
  intro b d hT
  have h := loC_injective (Finset.singleton_injective hT)
  injection h with hb hd
  rw [← hb, ← hd]
  rfl

theorem rgRevOk_rootReveal (θ : HPos → Digest) (r : SigningRequest) :
    RgRevOk θ (rootReveal r) := by
  intro b d hT
  exact absurd (Finset.singleton_injective hT) ((vcoord_ne_rnd _).2 b d)

theorem slotOf_cellOf_ne_msg' (S0 : MasterSeed) (v : QTable) {p : Pos} (hp : p.IsStruct)
    (l : Layer) (e : KeyIndex) : slotOf (cellOf S0 p v) ≠ some (.msg l e) := by
  rw [slotOf_cellOf S0 v p]
  intro h
  have h2 := Option.some.inj h
  cases p with
  | chain => cases h2
  | leaf => cases h2
  | node => cases h2
  | seed | param | prf | rndBottom | rndTop => exact absurd hp id

theorem rgProgOk_progT (θ : HPos → Digest) {p : Pos} (hp : p.IsStruct) :
    RgProgOk ((progT p).realize θ) := by
  rw [realize_progT hp (seedOf θ) θ]
  exact ⟨_, _, rfl, slotOf_cellOf_ne_msg' (seedOf θ) (tabOf θ) hp⟩

/-! ## Runtime 1's searches, lifted -/

section lift

variable (θ : HPos → Digest)

/-- **The randomizer search is moded** from its first trial. -/
theorem rgModed_grindT (P : PublicParameter) (B : QReg) (l : Layer) (e : KeyIndex)
    (msg : MsgBytes) (base : Randomizer) :
    ∀ n trial (rd : HashDomain → Option HashOutput),
      ModedP (L := LocalSig.instruments) (rgOk1 P) rgNx1 (fun _ _ ↦ True)
        (.srch l e msg base trial, rd) (grindT SelMem cwUpd P B l e msg base n trial)
  | 0, _, _ => trivial
  | n + 1, trial, rd => by
    rw [grindT]
    refine modedP₂_bind (F := fun r μ ↦ μ = rgRdNx (.srch l e msg base trial, rd)
      (.readH (trialCell P l e msg base trial) (cwUpd l e (trialCell P l e msg base trial))) r)
      (F' := fun _ _ ↦ True) _ _ ⟨rfl, fun _ ↦ ⟨trivial, fun _ ↦ rfl⟩⟩ fun r μ hμ ↦ ?_
    subst hμ
    split
    · trivial
    · rename_i hd
      rw [rgRdNx_srch, ite_eq_right (not_valid_of_decode hd)]
      exact rgModed_grindT P B l e msg base n (trial + 1) _

/-- A sponge program of runtime 1 is moded from every mode. -/
theorem rgModed_liftOrdinary (P : PublicParameter) {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments (spongeSpec HashOutput HashDomain) Ω A) :
    ∀ μ : RgMode, ModedP (rgOk1 P) rgNx1 (fun _ _ ↦ True) μ
      (y.liftOrdinary (t := hwReadCmdSpec HashOutput HashDomain SelMem)) := by
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
theorem rgModed_readLift {Ω : QReg → Type} {A : QReg} {fin : (Σ u, Ω u) → RgMode → Prop}
    (y : QuantumComp LocalSig.instruments (hwReadSpec HashOutput HashDomain SelMem) Ω A)
    {μ : RgMode} (hy : ModedP (rgOk1 (tabOf θ).param) rgNx1 fin μ y) :
    ModedP (rgOkT θ) (rgNxT θ) fin μ (readLift goodQ y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ μ (IFreeM.mapLens (readLens goodQ) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨?_, fun b ↦ ?_⟩
      · obtain ⟨σ, rd⟩ := μ
        cases σ with
        | free => exact hy.1.elim
        | srch l e msg base j =>
          have h : c = _ := hy.1
          subst h
          rfl
      · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;> obtain ⟨σ, rd⟩ := μ <;> cases σ <;>
          exact ih _ (hy.2 (ULift.up (b.down.1, b.down.2.2)))

/-- **Realizing keeps the modes.** -/
theorem rgModed_realizeT {Ω : QReg → Type} {A : QReg} {fin : (Σ u, Ω u) → RgMode → Prop}
    (y : QuantumComp LocalSig.instruments (XSpec SelMem) Ω A) {μ : RgMode}
    (hy : ModedP (rgOkT θ) (rgNxT θ) fin μ y) :
    ModedP (rgOkZ θ) (rgNxZ θ) fin μ (realizeT θ y) := by
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

theorem rgModed_readLiftQ {B : QReg} {α : Type}
    (y : QComp (hwReadSpec HashOutput HashDomain SelMem) B B α) {μ : RgMode}
    (hy : ModedP (rgOk1 (tabOf θ).param) rgNx1 (fun _ _ ↦ True) μ y) :
    ModedP (rgOkZ θ) (rgNxZ θ) (fun _ _ ↦ True) μ (realizeT θ (readLiftQ goodQ y)) :=
  rgModed_realizeT θ _ (rgModed_readLift θ y hy)

end lift

/-! ## The realized template pieces -/

section pieces

variable (θ : HPos → Digest)

/-- **A template whose realization is moded from every mode.** -/
def RgAny {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (XSpec SelMem) Ω A) : Prop :=
  ∀ μ : RgMode, ModedP (rgOkZ θ) (rgNxZ θ) (fun _ _ ↦ True) μ (realizeT θ y)

variable {θ}

theorem rgAny_bind₂ {A B C : QReg} {α β : Type} {x : QComp (XSpec SelMem) A B α}
    {k : α → QComp (XSpec SelMem) B C β} (hx : RgAny θ x) (hk : ∀ a, RgAny θ (k a)) :
    RgAny θ (x.bind k) := by
  intro μ
  rw [realizeT_bind₂]
  exact modedP₂_bind (F := fun _ _ ↦ True) (F' := fun _ _ ↦ True) _ _ (hx μ) fun a μ' _ ↦ hk a μ'

variable (θ)

theorem rgAny_pure {A : QReg} {α : Type} (a : α) :
    RgAny θ (QuantumComp₂.pure (L := LocalSig.instruments) (spec := XSpec SelMem) (A := A) a) :=
  fun _ ↦ trivial

theorem rgAny_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    RgAny θ (QComp.act (spec := XSpec SelMem) p) :=
  fun _ ↦ ⟨trivial, fun _ ↦ trivial⟩

/-- **A realized reveal** moves to the search it starts. -/
theorem rgModed_revealThen {B C : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals HD T × QMem → QComp (XSpec SelMem) B C α) (μ : RgMode)
    (hT : RgRevOk θ T)
    (hk : ∀ mem, ModedP (rgOkZ θ) (rgNxZ θ) (fun _ _ ↦ True) (rgRev θ T, μ.2)
      (realizeT θ (k (restrictTo T θ, mem)))) :
    ModedP (rgOkZ θ) (rgNxZ θ) (fun _ _ ↦ True) μ (realizeT θ (revealThen goodQ T k)) := by
  have e : realizeT θ (revealThen goodQ T k) =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := RSpec SelMem) (.inr T) B
        (Equiv.uniqueProd B Unit).symm fun mem ↦
          (QComp.act (A := QReg.of ((RSpec SelMem).Out (.inr T) × B)) (B := B)
            (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
              realizeT θ (k (restrictTo T θ, mem)) :=
    rfl
  rw [e]
  exact ⟨hT, fun b ↦ modedP₂_bind (F := fun _ μ' ↦ μ' = (rgRev θ T, μ.2))
    (F' := fun _ _ ↦ True) _ _ ⟨trivial, fun _ ↦ rfl⟩ fun _ μ' h ↦ h ▸ hk b.down⟩

theorem rgAny_revealThen {B C : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals HD T × QMem → QComp (XSpec SelMem) B C α) (hT : RgRevOk θ T)
    (hk : ∀ mem, RgAny θ (k (restrictTo T θ, mem))) : RgAny θ (revealThen goodQ T k) :=
  fun μ ↦ rgModed_revealThen θ T k μ hT fun mem ↦ hk mem _

theorem rgAny_progThen {B C : QReg} {α : Type} {p : Pos} (hp : p.IsStruct)
    (k : QComp (XSpec SelMem) B C α) (hk : RgAny θ k) :
    RgAny θ (progThen (progT p) trivial k) := by
  intro μ
  have e : realizeT θ (progThen (progT p) trivial k) =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := RSpec SelMem)
        (.inl (.inr ((progT p).realize θ))) B (Equiv.uniqueProd B Unit).symm fun _ ↦
          (QComp.act (A := QReg.of ((RSpec SelMem).Out (.inl (.inr ((progT p).realize θ))) × B))
            (B := B) (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
              realizeT θ k :=
    rfl
  rw [e]
  exact ⟨rgProgOk_progT θ hp, fun _ ↦ modedP₂_bind (F := fun _ _ ↦ True) (F' := fun _ _ ↦ True)
    _ _ ⟨trivial, fun _ ↦ trivial⟩ fun _ μ' _ ↦ hk μ'⟩

theorem rgAny_progPos (B : QReg) :
    ∀ ps : List Pos, (∀ p ∈ ps, p.IsStruct) → RgAny θ (progPos SelMem B ps)
  | [], _ => rgAny_pure θ ()
  | p :: ps, h => rgAny_progThen (θ := θ) (h p List.mem_cons_self) _
      (rgAny_progPos B ps fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

/-- **A layer's search** from its revealed base. -/
theorem rgAny_selectT (B : QReg) (l : Layer) (e : KeyIndex) (msg : MsgBytes) (rnd : Pos)
    (hr : rgRnd θ rnd = .srch l e msg (truncateHash (tabOf θ rnd)) 0)
    (hT : RgRevOk θ {loC rnd}) :
    RgAny θ (selectT SelMem cwUpd (tabOf θ).param B l e msg rnd) := by
  intro μ
  rw [selectT]
  refine rgModed_revealThen θ _ _ μ hT fun mem ↦ ?_
  have hb : truncateHash (tabR (restrictTo {loC rnd} θ) rnd) = truncateHash (tabOf θ rnd) :=
    baseOf_eq θ rnd
  dsimp only
  rw [hb, rgRev_loC, hr]
  exact rgModed_readLiftQ θ _ (rgModed_grindT _ B l e msg _ _ 0 μ.2)

theorem rgAny_publishT (B : QReg) (l : Layer) (e : KeyIndex) (ρ : Randomizer) (x : Encoding) :
    RgAny θ (publishT SelMem B l e ρ x) := by
  rw [publishT]
  exact rgAny_revealThen θ _ _ (rgRevOk_of_paramC θ (paramC_mem_layerReveal l e x)) fun _ ↦
    rgAny_bind₂ (rgAny_progPos θ B _ fun _ hp ↦ isStruct_of_mem_layerPos hp) fun _ ↦
      rgAny_pure θ _

/-- **A signature is moded.** -/
theorem rgAny_signT (B : QReg) (r : SigningRequest) :
    RgAny θ (signT SelMem cwUpd (tabOf θ).param B r) := by
  rw [signT]
  refine rgAny_bind₂ (rgAny_selectT θ B _ _ _ _ rfl (rgRevOk_rndBottom θ _ _)) fun gb ↦ ?_
  refine rgAny_revealThen θ _ _ (rgRevOk_rootReveal θ r) fun mem ↦ ?_
  dsimp only
  rw [show (tabR (restrictTo (rootReveal r) θ)).bottomRoot r.leafIndex =
    (tabOf θ).bottomRoot r.leafIndex from rootOf_eq θ r]
  refine rgAny_bind₂ (rgAny_selectT θ B _ _ _ _ rfl (rgRevOk_rndTop θ r)) fun gt ↦ ?_
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  · exact rgAny_pure θ _
  · exact rgAny_pure θ _
  · exact rgAny_pure θ _
  · exact rgAny_bind₂ (rgAny_publishT θ B _ _ _ _) fun _ ↦
      rgAny_bind₂ (rgAny_publishT θ B _ _ _ _) fun _ ↦ rgAny_pure θ _

/-- **The challenger is moded.** -/
theorem rgAny_challengeT (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0}
      (SufCma.advSpec SigningRequest (Option Signature)) A) :
    RgAny θ (challengeT SelMem cwUpd (tabOf θ).param A c) := by
  intro μ
  rcases c with o | ⟨_ | r, E, ℓ⟩
  · exact rgModed_realizeT θ _ (rgModed_readLift θ _ (rgModed_liftOrdinary _ _ μ))
  · exact rgModed_realizeT θ _ (rgModed_readLift θ _ (rgModed_liftOrdinary _ _ μ))
  · change ModedP _ _ _ μ (realizeT θ (QuantumComp.bind
      (signAt SelMem cwUpd (tabOf θ).param r E ℓ) _))
    refine (congrArg (fun y ↦ ModedP (rgOkZ θ) (rgNxZ θ) (fun _ _ ↦ True) μ y)
      (realizeT_bind (good := goodQ) (M := SelMem) θ _ _)).mpr ?_
    exact modedP_bind _ _ (rgAny_bind₂ (rgAny_act θ _) (fun _ ↦ rgAny_signT θ _ r) μ)
      fun _ _ _ _ ↦ trivial

/-- Substituting moded commands. -/
theorem rgModed_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments spec)
      (QuantumComp.toIPFunctor LocalSig.instruments (RSpec SelMem)))
    (hσ : ∀ A c μ, ModedP (rgOkZ θ) (rgNxZ θ) (fun _ _ ↦ True) μ (σ A c)) {Ω : QReg → Type}
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) :
    ∀ μ, ModedP (rgOkZ θ) (rgNxZ θ) (fun _ _ ↦ True) μ (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact fun _ ↦ trivial
  | liftBind s c next ih =>
    intro μ
    rw [IFreeM.substitute_liftBind]
    exact modedP_bind _ _ (hσ s c μ) fun u ans μ' _ ↦ (modedP_cast_mode ans.2 _ _).mpr
      (ih ans.1 μ')

/-- **The realized challenge prefix is moded**, from every mode. -/
theorem rgModed_prefixQ (A : Adversary) (μ : RgMode) :
    ModedP (rgOkZ θ) (rgNxZ θ) (fun _ _ ↦ True) μ (prefixQ A θ) := by
  unfold prefixQ prefixT
  refine rgModed_revealThen θ _ _ μ (rgRevOk_of_paramC θ (Finset.mem_insert_self _ _))
    fun mem ↦ ?_
  have hP : (pkT (restrictTo pkReveal θ)).parameter = (tabOf θ).param := by
    rw [show pkT (restrictTo pkReveal θ) = pkD θ from rfl, pkD_eq]
    rfl
  dsimp only
  rw [hP, realizeT_bind₂]
  refine modedP₂_bind (F := fun _ _ ↦ True) (F' := fun _ _ ↦ True) _ _ ?_ fun _ _ _ ↦ trivial
  unfold challengedT
  have e := realizeT_substitute (good := goodQ) (M := SelMem) θ
    (challengeT SelMem cwUpd (tabOf θ).param)
    (SufCma.withSignLog (A (pkT (restrictTo pkReveal θ))))
  exact (congrArg (fun y ↦ ModedP (rgOkZ θ) (rgNxZ θ) (fun _ _ ↦ True) (rgRev θ pkReveal, μ.2) y)
    e).mpr (rgModed_substitute θ _ (fun A c ↦ rgAny_challengeT θ A c) _ _)

end pieces

/-! ## The bottom reveals -/

section bottom

/-- A bottom base of key `e` is in `T`. -/
def BotRev (e : KeyIndex) (T : Finset HPos) : Prop :=
  ∃ m, loC (.rndBottom e m) ∈ T

/-- A lifted read of an `h`-cell. -/
def RdPort (c : HwRead HashOutput HashDomain QMem) : Prop :=
  ∃ z u, c = liftRead (.readH z u)

/-- A program of an `h`-cell. -/
def PgPort (c : HwProg HashOutput HashDomain) : Prop :=
  ∃ z a, c = .programH z a

/-- **The bottom-reveal charge of key `e`**: a record port revealing a bottom base of `e`, a read
other than a lifted `h`-read, and a program other than of an `h`-cell cost one. -/
noncomputable def botRevCharge (e : KeyIndex) : (RSpec SelMem).Port → ℕ
  | .inl (.inl (.inl _)) => 0
  | .inl (.inl (.inr c)) => @ite ℕ (RdPort c) (Classical.propDecidable _) 0 1
  | .inl (.inr c) => @ite ℕ (PgPort c) (Classical.propDecidable _) 0 1
  | .inr T => @ite ℕ (BotRev e T) (Classical.propDecidable _) 1 0

/-- The charge on runtime 1's ports, through `liftRead`. -/
noncomputable def botRevChargeR (e : KeyIndex) :
    (hwReadSpec HashOutput HashDomain SelMem).Port → ℕ
  | .inl i => botRevCharge e (.inl (.inl (.inl i)))
  | .inr c => botRevCharge e (.inl (.inl (.inr (liftRead (S := HPos) c))))

/-- The charge on the template ports at `θ`, through the realization. -/
noncomputable def botRevChargeT (θ : HPos → Digest) (e : KeyIndex) : (XSpec SelMem).Port → ℕ
  | .inl (.inl (.inl i)) => botRevCharge e (.inl (.inl (.inl i)))
  | .inl (.inl (.inr c)) => botRevCharge e (.inl (.inl (.inr c.1)))
  | .inl (.inr p) => botRevCharge e (.inl (.inr (p.1.realize θ)))
  | .inr T => botRevCharge e (.inr T)

theorem botRevCharge_rec_of_not {e : KeyIndex} {T : Finset HPos} (h : ¬BotRev e T) :
    botRevCharge e (.inr T) = 0 :=
  ite_eq_right h

theorem ne_rndBottom_of_mem_needUnion : ∀ {ps : List Pos}, (∀ p ∈ ps, p.IsStruct) →
    ∀ {c : HPos}, c ∈ needUnion ps → ∀ e m, c ≠ loC (.rndBottom e m)
  | [], _, _, hc => absurd hc (Finset.notMem_empty _)
  | p :: ps, hps, c, hc => by
    rcases Finset.mem_union.mp hc with hc | hc
    · intro e m hce
      subst hce
      rcases Finset.mem_union.mp hc with hc | hc
      · rcases Finset.mem_insert.mp hc with hc | hc
        · exact absurd (loC_injective hc) fun h' ↦ by cases h'
        · obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hc
          exact (vcoord_ne_rnd q).1 e m hq
      · rcases Finset.mem_insert.mp hc with hc | hc
        · have h := hps p List.mem_cons_self
          rw [← loC_injective hc] at h
          exact h
        · rw [Finset.mem_singleton] at hc
          exact absurd (congrArg Prod.snd hc) (by simp [loC, hiC])
    · exact ne_rndBottom_of_mem_needUnion (fun q hq ↦ hps q (List.mem_cons_of_mem _ hq)) hc

theorem not_botRev_layerReveal (e' : KeyIndex) (l : Layer) (e : KeyIndex) (x : Encoding) :
    ¬BotRev e' (layerReveal l e x) := by
  rintro ⟨m, hm⟩
  rcases Finset.mem_union.mp hm with hm | hm
  · rcases Finset.mem_union.mp hm with hm | hm
    · exact ne_rndBottom_of_mem_needUnion (fun _ hp ↦ isStruct_of_mem_layerPos hp) hm e' m rfl
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hm
      exact (vcoord_ne_rnd _).1 e' m hi
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hm
    exact (vcoord_ne_rnd _).1 e' m hi

theorem not_botRev_rootReveal (e : KeyIndex) (r : SigningRequest) : ¬BotRev e (rootReveal r) := by
  rintro ⟨m, hm⟩
  rw [rootReveal, Finset.mem_singleton] at hm
  exact (vcoord_ne_rnd _).1 e m hm.symm

theorem not_botRev_rndTop (e b : KeyIndex) (d : Digest) : ¬BotRev e {loC (.rndTop b d)} := by
  rintro ⟨m, hm⟩
  exact absurd (loC_injective (Finset.mem_singleton.mp hm)) fun h' ↦ by cases h'

theorem not_botRev_pkReveal (e : KeyIndex) : ¬BotRev e pkReveal := by
  rintro ⟨m, hm⟩
  rcases Finset.mem_insert.mp hm with hm | hm
  · exact absurd (loC_injective hm) fun h' ↦ by cases h'
  · exact absurd (loC_injective (Finset.mem_singleton.mp hm)) fun h' ↦ by cases h'

theorem botRevCharge_rndBottom_le (e : KeyIndex) (r : SigningRequest) :
    botRevCharge e (.inr {loC (.rndBottom (keyIndexOnLayer r.leafIndex bottomLayer) r.message)}) ≤
      leafCharge e (.sign r) := by
  show @ite ℕ (BotRev e _) (Classical.propDecidable _) 1 0 ≤ if r.leafIndex = e then 1 else 0
  by_cases h : r.leafIndex = e
  · rw [ite_eq_left h]
    split_ifs <;> omega
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨m, hm⟩
    have h1 := loC_injective (Finset.mem_singleton.mp hm)
    injection h1 with he
    exact h (Fin.ext (by rw [he]; simp [keyIndexOnLayer, bottomLayer]))

variable (θ : HPos → Digest) (e : KeyIndex) {Ω : QReg → Type}

theorem chgBot_realizeT {A : QReg}
    {y : QuantumComp LocalSig.instruments.{0} (XSpec SelMem) Ω A} {n : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge (botRevChargeT θ e)) n) :
    IFreeM.IsChargeBound (realizeT θ y) (portCharge (botRevCharge e)) n := by
  refine IFreeM.IsChargeBound.mapLens (tmplLens θ) ?_
  have he : (fun s cmd ↦ portCharge (L := LocalSig.instruments.{0}) (botRevCharge e) s
      ((tmplLens θ).toFunA s cmd)) = portCharge (botRevChargeT θ e) := by
    funext s cmd
    rcases cmd with o | ⟨((i | c) | p) | T, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

theorem chgBot_readLift {A : QReg}
    {y : QuantumComp LocalSig.instruments.{0} (hwReadSpec HashOutput HashDomain SelMem) Ω A}
    {n : ℕ} (h : IFreeM.IsChargeBound y (portCharge (botRevChargeR e)) n) :
    IFreeM.IsChargeBound (readLift goodQ y) (portCharge (botRevChargeT θ e)) n := by
  refine IFreeM.IsChargeBound.mapLens (readLens goodQ) ?_
  have he : (fun s cmd ↦ portCharge (L := LocalSig.instruments.{0}) (botRevChargeT θ e) s
      ((readLens goodQ).toFunA s cmd)) = portCharge (botRevChargeR e) := by
    funext s cmd
    rcases cmd with o | ⟨i | c, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

theorem chgBot_grindT (P : PublicParameter) (B : QReg) (l : Layer) (e' : KeyIndex)
    (message : MsgBytes) (base : Randomizer) :
    ∀ n trial, IFreeM.IsChargeBound (grindT SelMem cwUpd P B l e' message base n trial)
      (portCharge (botRevChargeR e)) 0
  | 0, _ => trivial
  | n + 1, trial => by
    have hc : RdPort (liftRead (S := HPos) (.readH (trialCell P l e' message base trial)
        (cwUpd l e' (trialCell P l e' message base trial)))) := ⟨_, _, rfl⟩
    rw [grindT]
    refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) ?_ fun r ↦ ?_
    · unfold readCall
      exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
        ((IFreeM.isChargeBound_liftBind_iff _ _ _).mpr
          ⟨Nat.le_of_eq (ite_eq_left hc), fun _ ↦ trivial⟩)
        fun _ ↦ FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ trivial
    · split
      · trivial
      · exact chgBot_grindT P B l e' message base n (trial + 1)

theorem chgBot_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals HD T × QMem → QComp (XSpec SelMem) B B' α) {n : ℕ}
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge (botRevChargeT θ e)) n) :
    IFreeM.IsChargeBound (revealThen goodQ T k) (portCharge (botRevChargeT θ e))
      (botRevCharge e (.inr T) + n) :=
  (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.le_add_right _ _, fun r ↦ by
    rw [show botRevChargeT θ e (.inr T) = botRevCharge e (.inr T) from rfl,
      Nat.add_sub_cancel_left]
    exact (FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := n) (chg_act _ _ 0) fun _ ↦ hk r).mono
      (Nat.zero_add n).le⟩

theorem chgBot_revealThen₀ {B B' : QReg} {α : Type} (T : Finset HPos) (hT : ¬BotRev e T)
    (k : RevealVals HD T × QMem → QComp (XSpec SelMem) B B' α) {n : ℕ}
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge (botRevChargeT θ e)) n) :
    IFreeM.IsChargeBound (revealThen goodQ T k) (portCharge (botRevChargeT θ e)) n :=
  (chgBot_revealThen θ e T k hk).mono (le_of_eq (by rw [botRevCharge_rec_of_not hT, zero_add]))

theorem chgBot_progPos (B : QReg) :
    ∀ ps : List Pos, (∀ p ∈ ps, p.IsStruct) →
      IFreeM.IsChargeBound (progPos SelMem B ps) (portCharge (botRevChargeT θ e)) 0
  | [], _ => trivial
  | p :: ps, h => by
    have h0 : botRevChargeT θ e (.inl (.inr ⟨progT p, trivial⟩)) = 0 := by
      show botRevCharge e (.inl (.inr ((progT p).realize θ))) = 0
      rw [realize_progT (h p List.mem_cons_self) (seedOf θ) θ]
      exact ite_eq_left ⟨_, _, rfl⟩
    exact (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨h0.le, fun _ ↦
      IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0)
        fun _ ↦ chgBot_progPos B ps fun q hq ↦ h q (List.mem_cons_of_mem _ hq))
        (Nat.zero_le _)⟩

theorem chgBot_selectT (P : PublicParameter) (B : QReg) (l : Layer) (e' : KeyIndex)
    (message : MsgBytes) (rnd : Pos) :
    IFreeM.IsChargeBound (selectT SelMem cwUpd P B l e' message rnd)
      (portCharge (botRevChargeT θ e)) (botRevCharge e (.inr {loC rnd})) :=
  chgBot_revealThen θ e _ _ (n := 0) fun _ ↦
    chgBot_readLift θ e (chgBot_grindT e P B l e' message _ _ 0)

theorem chgBot_publishT (B : QReg) (l : Layer) (e' : KeyIndex) (ρ : Randomizer) (x : Encoding) :
    IFreeM.IsChargeBound (publishT SelMem B l e' ρ x) (portCharge (botRevChargeT θ e)) 0 :=
  chgBot_revealThen₀ θ e _ (not_botRev_layerReveal e l e' x) _ fun _ ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
      (chgBot_progPos θ e B _ fun _ hp ↦ isStruct_of_mem_layerPos hp) fun _ ↦ trivial

/-- **A signature** reveals a bottom base of `e` only for the leaf `e`. -/
theorem chgBot_signT (P : PublicParameter) (B : QReg) (r : SigningRequest) :
    IFreeM.IsChargeBound (signT SelMem cwUpd P B r) (portCharge (botRevChargeT θ e))
      (leafCharge e (.sign r)) := by
  unfold signT
  refine (FreeM₂.isChargeBound_bind (n₂ := 0) (chgBot_selectT θ e P B _ _ _ _) fun gb ↦ ?_).mono
    (botRevCharge_rndBottom_le e r)
  refine chgBot_revealThen₀ θ e _ (not_botRev_rootReveal e r) _ fun rr ↦ ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    ((chgBot_selectT θ e P B _ _ _ _).mono (le_of_eq (botRevCharge_rec_of_not
      (not_botRev_rndTop e _ _)))) fun gt ↦ ?_
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  · trivial
  · trivial
  · trivial
  · exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgBot_publishT θ e B _ _ _ _) fun _ ↦
      FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgBot_publishT θ e B _ _ _ _) fun _ ↦
        trivial

/-- **The challenger** reveals a bottom base of `e` only at a request of the leaf `e`. -/
theorem chgBot_challengeT (P : PublicParameter) (A : QReg)
    (cmd : QuantumComp.Cmd LocalSig.instruments.{0}
      (SufCma.advSpec SigningRequest (Option Signature)) A) :
    IFreeM.IsChargeBound (challengeT SelMem cwUpd P A cmd) (portCharge (botRevChargeT θ e))
      (SufCma.cmdCharge (leafCharge e) A cmd) := by
  rcases cmd with o | ⟨_ | r, E, ℓ⟩
  · exact chgBot_readLift θ e (isChargeBound_liftOrdinary _ ((isChargeBound_liftH_iff _ _ _).mpr
      (isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl) (isChargeBound_zero _))))
  · exact chgBot_readLift θ e (isChargeBound_liftOrdinary _ ((isChargeBound_liftH_iff _ _ _).mpr
      (isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl) (isChargeBound_zero _))))
  · exact IFreeM.isChargeBound_bind (n₂ := 0) ((FreeM₂.isChargeBound_bind (n₁ := 0)
      (chg_act _ _ 0) fun _ ↦ chgBot_signT θ e P _ r).mono (Nat.zero_add _).le)
      fun _ _ ↦ IFreeM.isChargeBound_pure _ 0

/-- **The realized challenge prefix** of an adversary reusing no leaf reveals a bottom base of
`e` at most once. -/
theorem chgBot_prefixQ {A : Adversary} (hleaf : NoLeafReuse A) :
    IFreeM.IsChargeBound (prefixQ A θ) (portCharge (botRevCharge e)) 1 := by
  refine chgBot_realizeT θ e ?_
  unfold prefixT
  refine chgBot_revealThen₀ θ e _ (not_botRev_pkReveal e) _ fun _ ↦ ?_
  exact FreeM₂.isChargeBound_bind (n₁ := 1) (n₂ := 0)
    (IFreeM.IsChargeBound.substitute (challengeT SelMem cwUpd _)
      (c := SufCma.cmdCharge (leafCharge e)) (fun s cmd ↦ chgBot_challengeT θ e _ s cmd)
      (SufCma.isChargeBound_withSignLog (hleaf _ e))) fun _ ↦ trivial

end bottom

end Quantum.Qrom.Xmss

end
