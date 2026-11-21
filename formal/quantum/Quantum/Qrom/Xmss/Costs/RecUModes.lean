module

public import Quantum.Qrom.Xmss.Costs.Ports
public import Quantum.Xmss.Assembly.CwReFail

@[expose] public section

/-!
# The randomizer searches of the challenge prefix, as moded programs

The modes of the randomizer searches of runtime 2: free, or in the search of the randomizer
position `rnd` (`rndLab rnd`: its key and message) from the base `base`, before trial `j`. A
reveal of `{loC rnd}` starts the search from the revealed base; a trial read whose digest is a
codeword ends it (free mode), otherwise the next trial follows; the calls between searches
(sponge calls, programs of non-message cells, reveals of one base or none) happen only in a rest
mode (free, or after the last trial).

* `rndLab`, `RndC`, `rndOfT`, `RevOkQ`, `ProgOkQ`, `SrchMode`, `SrchMode.Rest`.
* The allowed calls and the mode after a call, on runtime 1's ports (`srchOkR`, `srchNxR`), the
  template's (`srchOkT`, `srchNxT`) and runtime 2's with record ports (`srchOkZ`, `srchNxZ`).
* **`modedP_prefixQ`**: the realized challenge prefix `prefixQ A θ` is moded from the free mode,
  its searches' trials at the parameter `θ paramC`, ending in a rest mode.
-/

open Matrix IPFunctor
open scoped ENNReal

universe u v w

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss.Hybrid (restrictTo)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT revealThen progThen readLift
  readLiftQ RevealVals liftRead tmplLens readLens readMono_liftRead ModedP modedP_bind
  modedP₂_bind modedP_map modeCmdOk modeCmdNx)

attribute [local irreducible] xmssRom

/-! ## Randomizer positions and reveals -/

/-- **The key and message of a randomizer position's search**; `none` off the randomizer
positions. -/
def rndLab : Pos → Option (Layer × KeyIndex × MsgBytes)
  | .rndBottom e m => some (bottomLayer, e, messageBytes m)
  | .rndTop e root => some (topLayer, e, rootBytes root)
  | _ => none

/-- The low half of a randomizer base. -/
def RndC : HPos → Prop
  | (some (.rndBottom ..), false) => True
  | (some (.rndTop ..), false) => True
  | _ => False

theorem rndC_loC {rnd : Pos} (h : (rndLab rnd).isSome) : RndC (loC rnd) := by
  cases rnd <;> trivial

theorem loC_injective : Function.Injective loC := fun _ _ h ↦
  Option.some.inj (congrArg Prod.fst h)

/-- **The randomizer position of a reveal** of a single randomizer base (decided classically:
the enumeration of the positions is not to be evaluated). -/
noncomputable def rndOfT (T : Finset HPos) : Option Pos :=
  @dite _ (∃ rnd : Pos, (rndLab rnd).isSome ∧ T = {loC rnd}) (Classical.propDecidable _)
    (fun h ↦ some h.choose) fun _ ↦ none

theorem rndOfT_spec {T : Finset HPos} {rnd : Pos} (h : rndOfT T = some rnd) :
    (rndLab rnd).isSome ∧ T = {loC rnd} := by
  unfold rndOfT at h
  split_ifs at h with h'
  obtain rfl := Option.some.inj h
  exact h'.choose_spec

theorem rndOfT_loC {rnd : Pos} (h : (rndLab rnd).isSome) : rndOfT {loC rnd} = some rnd := by
  unfold rndOfT
  split_ifs with h'
  · exact congrArg some (loC_injective (Finset.singleton_injective h'.choose_spec.2.symm))
  · exact absurd ⟨rnd, h, rfl⟩ h'

theorem rndOfT_eq_none {T : Finset HPos} (h : ∀ s ∈ T, ¬ RndC s) : rndOfT T = none := by
  rcases hT : rndOfT T with _ | rnd
  · rfl
  · obtain ⟨hr, rfl⟩ := rndOfT_spec hT
    exact absurd (rndC_loC hr) (h _ (Finset.mem_singleton_self _))

/-- **A reveal the searches allow**: one randomizer base, or no randomizer base. -/
def RevOkQ (T : Finset HPos) : Prop :=
  (∃ rnd, (rndLab rnd).isSome ∧ T = {loC rnd}) ∨ ∀ s ∈ T, ¬ RndC s

/-- **A program the searches allow**: an `h`-cell outside the message slots. -/
def ProgOkQ (c : HwProg HashOutput HashDomain) : Prop :=
  ∃ z a, c = .programH z a ∧ ∀ l e, slotOf z ≠ some (.msg l e)

/-! ## The modes -/

/-- **The modes of the randomizer searches**: free; in the search of the randomizer position
`rnd` from the base `base`, before trial `j`. -/
inductive SrchMode
  | free
  | grd (rnd : Pos) (base : Randomizer) (j : ℕ)

/-- A mode between searches: free, or after the last trial. -/
def SrchMode.Rest : SrchMode → Prop
  | .free => True
  | .grd _ _ j => j = randomizerAttemptLimit

/-- The mode after a reveal of `T`, the bases given by `bse`: the search of its randomizer
position from its base, free otherwise. -/
noncomputable def revNxQ (T : Finset HPos) (bse : Pos → Randomizer) : SrchMode :=
  match rndOfT T with
  | some rnd => .grd rnd (bse rnd) 0
  | none => .free

theorem revNxQ_congr {T : Finset HPos} {bse bse' : Pos → Randomizer}
    (h : ∀ rnd, rndOfT T = some rnd → bse rnd = bse' rnd) : revNxQ T bse = revNxQ T bse' := by
  unfold revNxQ
  rcases hT : rndOfT T with _ | rnd
  · rfl
  · exact congrArg (fun b ↦ SrchMode.grd rnd b 0) (h rnd hT)

theorem revNxQ_loC {rnd : Pos} (h : (rndLab rnd).isSome) (bse : Pos → Randomizer) :
    revNxQ {loC rnd} bse = .grd rnd (bse rnd) 0 := by
  unfold revNxQ
  rw [rndOfT_loC h]

theorem revNxQ_none {T : Finset HPos} (h : ∀ s ∈ T, ¬ RndC s) (bse : Pos → Randomizer) :
    revNxQ T bse = .free := by
  unfold revNxQ
  rw [rndOfT_eq_none h]

variable (P : PublicParameter)

/-- **The trial read a mode allows**: in the search of `rnd` from `base` before trial `j < 2^32`,
the read of trial `j`'s message-digest cell under the parameter `P`. -/
def srchRdOk : SrchMode → HwRead HashOutput HashDomain QMem → Prop
  | .grd rnd b j, c => j < randomizerAttemptLimit ∧ ∃ l e msg, rndLab rnd = some (l, e, msg) ∧
      c = trialRead (trialCell P l e msg b j) l e
  | .free, _ => False

/-- **The mode after a read**: free after a codeword digest, the next trial otherwise. -/
noncomputable def srchRdNx {M' : Type} :
    SrchMode → (c : HwRead HashOutput HashDomain M') → c.Result → SrchMode
  | .grd rnd b j, .readH _ _, r =>
      match Codeword.decode (truncateHash (r.1.getD 0)) with
      | some _ => .free
      | none => .grd rnd b (j + 1)
  | _, _, _ => .free

/-- The calls the modes allow, on runtime 1's ports. -/
def srchOkR : SrchMode → (hwReadSpec HashOutput HashDomain SelMem).Port → Prop
  | μ, .inl _ => μ.Rest
  | μ, .inr c => srchRdOk P μ (liftRead (S := HPos) c)

/-- The mode after a call of runtime 1. -/
noncomputable def srchNxR : SrchMode → (i : (hwReadSpec HashOutput HashDomain SelMem).Port) →
    (hwReadSpec HashOutput HashDomain SelMem).Result i → SrchMode
  | μ, .inr c, r => srchRdNx μ c r
  | _, .inl _, _ => .free

/-- The calls the modes allow, on the template's ports. -/
def srchOkT : SrchMode → (XSpec SelMem).Port → Prop
  | μ, .inl (.inl (.inl _)) => μ.Rest
  | μ, .inl (.inl (.inr c)) => srchRdOk P μ c.1
  | μ, .inl (.inr p) => μ.Rest ∧ ∀ θ : HPos → Digest, ProgOkQ (p.1.realize θ)
  | μ, .inr T => μ.Rest ∧ RevOkQ T

/-- The mode after a call of the template: a reveal of one randomizer base starts its search. -/
noncomputable def srchNxT :
    SrchMode → (i : (XSpec SelMem).Port) → (XSpec SelMem).Result i → SrchMode
  | μ, .inl (.inl (.inr c)), r => srchRdNx μ c.1 r
  | _, .inr T, r => revNxQ T fun rnd ↦ extendT r.1 (loC rnd)
  | _, _, _ => .free

/-- **The calls the modes allow**, on runtime 2's ports with record ports. -/
def srchOkZ : SrchMode → (RSpec SelMem).Port → Prop
  | μ, .inl (.inl (.inl _)) => μ.Rest
  | μ, .inl (.inl (.inr c)) => srchRdOk P μ c
  | μ, .inl (.inr c) => μ.Rest ∧ ProgOkQ c
  | μ, .inr T => μ.Rest ∧ RevOkQ T

/-- **The mode after a call** of runtime 2 with record ports, at the hidden values `θ`. -/
noncomputable def srchNxZ (θ : HPos → Digest) :
    SrchMode → (i : (RSpec SelMem).Port) → (RSpec SelMem).Result i → SrchMode
  | μ, .inl (.inl (.inr c)), r => srchRdNx μ c r
  | _, .inr T, _ => revNxQ T fun rnd ↦ θ (loC rnd)
  | _, _, _ => .free

/-! ## Runtime 1's searches -/

variable {P}

theorem modedP_readCall_srch {μ : SrchMode} {c : HwRead HashOutput HashDomain SelMem}
    (h : srchRdOk P μ (liftRead (S := HPos) c)) (B : QReg) :
    ModedP (L := LocalSig.instruments) (srchOkR P) srchNxR
      (fun p μ' ↦ μ' = srchRdNx μ c p.2.2) μ (readCall c B) :=
  ⟨h, fun _ ↦ ⟨trivial, fun _ ↦ rfl⟩⟩

/-- **The randomizer search** of `rnd` from its base, from trial `trial` to the last, ends in a
rest mode: free after a codeword, after the last trial otherwise. -/
theorem modedP_grindT {rnd : Pos} {l : Layer} {e : KeyIndex} {msg : MsgBytes}
    (hr : rndLab rnd = some (l, e, msg)) (B : QReg) (base : Randomizer) :
    ∀ n trial, trial + n = randomizerAttemptLimit →
      ModedP (L := LocalSig.instruments) (srchOkR P) srchNxR (fun _ (μ : SrchMode) ↦ μ.Rest)
        (.grd rnd base trial) (grindT SelMem cwUpd P B l e msg base n trial)
  | 0, trial, hn => by
    show SrchMode.Rest (.grd rnd base trial)
    exact (Nat.add_zero trial).symm.trans hn
  | n + 1, trial, hn => by
    rw [grindT]
    refine modedP₂_bind (F := fun r (μ : SrchMode) ↦ μ = srchRdNx (.grd rnd base trial)
        (.readH (trialCell P l e msg base trial) (cwUpd l e (trialCell P l e msg base trial))) r)
      (F' := fun _ (μ : SrchMode) ↦ μ.Rest) _ _
      (modedP_readCall_srch (μ := .grd rnd base trial) ⟨by omega, l, e, msg, hr, rfl⟩ B)
      fun r μ hμ ↦ ?_
    subst hμ
    show ModedP _ _ _ (match Codeword.decode (truncateHash (r.1.getD 0)) with
      | some _ => SrchMode.free
      | none => SrchMode.grd rnd base (trial + 1))
      (match Codeword.decode (truncateHash (r.1.getD 0)) with
      | some x => QuantumComp₂.pure (some (base + BitVec.ofNat digestBits trial, x))
      | none => grindT SelMem cwUpd P B l e msg base n (trial + 1))
    split
    · trivial
    · exact modedP_grindT hr B base n (trial + 1) (by omega)

/-- **Lifting runtime 1's moded programs to templates.** -/
theorem modedP_readLift_srch {Ω : QReg → Type} {A : QReg} {fin : (Σ u, Ω u) → SrchMode → Prop}
    (y : QuantumComp LocalSig.instruments (hwReadSpec HashOutput HashDomain SelMem) Ω A)
    {μ : SrchMode} (hy : ModedP (srchOkR P) srchNxR fin μ y) :
    ModedP (srchOkT P) srchNxT fin μ (readLift goodQ y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ μ (IFreeM.mapLens (readLens goodQ) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨hy.1, fun b ↦ ?_⟩
      rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;> rcases μ with _ | ⟨rnd, base, j⟩ <;>
        exact ih _ (hy.2 (ULift.up (b.down.1, b.down.2.2)))

/-- A sponge program of runtime 1 is moded between searches. -/
theorem modedP_liftOrdinary_srch {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments (spongeSpec HashOutput HashDomain) Ω A) :
    ∀ μ : SrchMode, μ.Rest → ModedP (srchOkR P) srchNxR (fun _ (μ : SrchMode) ↦ μ.Rest) μ
      (y.liftOrdinary (t := hwReadCmdSpec HashOutput HashDomain SelMem)) := by
  induction y using IFreeM.inductionOn with
  | pure _ a => exact fun _ h ↦ h
  | liftBind _ c next ih =>
    intro μ hμ
    show ModedP _ _ _ _ (IFreeM.mapLens QuantumComp.ordinaryLens (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ μ hμ⟩
    · exact ⟨hμ, fun b ↦ ih _ .free trivial⟩

/-! ## The template's searches -/

theorem srchNxZ_rec_eq (θ : HPos → Digest) (μ : SrchMode) (T : Finset HPos) (m : QMem) :
    srchNxZ θ μ (.inr T) m = srchNxT μ (.inr T) (restrictTo T θ, m) :=
  revNxQ_congr fun rnd hr ↦ (extendT_restrictTo
    (by rw [(rndOfT_spec hr).2]; exact Finset.mem_singleton_self _) θ).symm

/-- **Realizing keeps the modes.** -/
theorem modedP_realizeT_srch (θ : HPos → Digest) {L : LocalSig.{u, v}} {Ω : QReg → Type w}
    {A : QReg} {fin : (Σ u, Ω u) → SrchMode → Prop} (y : QuantumComp L (XSpec SelMem) Ω A)
    {μ : SrchMode} (hy : ModedP (srchOkT P) srchNxT fin μ y) :
    ModedP (srchOkZ P) (srchNxZ θ) fin μ (realizeT θ y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ μ (IFreeM.mapLens (tmplLens θ) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨((i | c) | ⟨p, hp⟩) | T, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · cases p <;> exact ⟨⟨hy.1.1, hy.1.2 θ⟩, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨hy.1, fun b ↦ ?_⟩
      have h := ih _ (hy.2 (ULift.up (restrictTo T θ, b.down)))
      exact (congrArg (fun μ' ↦ ModedP (srchOkZ P) (srchNxZ θ) fin μ' _)
        (srchNxZ_rec_eq θ μ T b.down)).mpr h

variable (P) in
/-- A template moded between searches: from every rest mode, it ends in a rest mode. -/
def SRestQ {Ω : QReg → Type} {A : QReg} (y : QuantumComp LocalSig.instruments (XSpec SelMem) Ω A) :
    Prop :=
  ∀ μ : SrchMode, μ.Rest → ModedP (srchOkT P) srchNxT (fun _ (μ : SrchMode) ↦ μ.Rest) μ y

theorem sRestQ_bind {A B B' : QReg} {α β : Type} (x : QComp (XSpec SelMem) A B α)
    (g : α → QComp (XSpec SelMem) B B' β) (hx : SRestQ P x) (hg : ∀ a, SRestQ P (g a)) :
    SRestQ P (x.bind g) :=
  fun μ hμ ↦ modedP₂_bind (F := fun _ (μ : SrchMode) ↦ μ.Rest)
    (F' := fun _ (μ : SrchMode) ↦ μ.Rest) x g (hx μ hμ) fun a μ' h ↦ hg a μ' h

theorem sRestQ_pure {A : QReg} {α : Type} (a : α) :
    SRestQ P (QuantumComp₂.pure (L := LocalSig.instruments) (spec := XSpec SelMem) (A := A) a) :=
  fun _ h ↦ h

theorem sRestQ_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    SRestQ P (QComp.act (spec := XSpec SelMem) p) :=
  fun _ hμ ↦ ⟨trivial, fun _ ↦ hμ⟩

/-- A reveal of no randomizer base keeps the search modes free. -/
theorem sRestQ_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (hT : ∀ s ∈ T, ¬ RndC s)
    (k : RevealVals HD T × QMem → QComp (XSpec SelMem) B B' α)
    (hk : ∀ r, SRestQ P (k r)) : SRestQ P (revealThen goodQ T k) := by
  intro μ hμ
  refine ⟨⟨hμ, .inr hT⟩, fun b ↦ ?_⟩
  have he : srchNxT μ (.inr T) b.down = .free := revNxQ_none hT _
  rw [show modeCmdNx srchNxT (QuantumComp.Cmd.query (L := LocalSig.instruments)
    (.inr T) B _) μ b = srchNxT μ (.inr T) b.down from rfl, he]
  exact sRestQ_bind _ _ (sRestQ_act _) (fun _ ↦ hk b.down) _ trivial

theorem sRestQ_progThen {B B' : QReg} {α : Type} {p : Pos} (hp : p.IsStruct)
    (k : QComp (XSpec SelMem) B B' α) (hk : SRestQ P k) :
    SRestQ P (progThen (progT p) trivial k) := by
  intro μ hμ
  refine ⟨⟨hμ, fun θ ↦ ?_⟩, fun _ ↦ sRestQ_bind _ _ (sRestQ_act _) (fun _ ↦ hk) _ trivial⟩
  refine ⟨cellOf 0 p (tabOf θ), tabOf θ p, realize_progT hp 0 θ, fun l e h ↦ ?_⟩
  rw [slotOf_cellOf] at h
  cases p with
  | chain => cases h
  | leaf => cases h
  | node => cases h
  | seed | param | prf | rndBottom | rndTop => exact absurd hp id

theorem sRestQ_progPos (B : QReg) :
    ∀ ps : List Pos, (∀ p ∈ ps, p.IsStruct) → SRestQ P (progPos SelMem B ps)
  | [], _ => sRestQ_pure _
  | p :: ps, h => sRestQ_progThen (h p List.mem_cons_self) _
      (sRestQ_progPos B ps fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

/-! ## The coordinates the signatures reveal -/

theorem not_rndC_vcoord (q : Quantum.Xmss.Pos) : ¬ RndC (vcoord q) := by
  unfold vcoord
  split
  · exact id
  · split_ifs <;> exact id
  · exact id
  · split_ifs <;> exact id

theorem not_rndC_of_struct {p : Pos} (hp : p.IsStruct) (b : Bool) : ¬ RndC (some p, b) := by
  cases p with
  | chain => cases b <;> exact id
  | leaf => cases b <;> exact id
  | node => cases b <;> exact id
  | seed | param | prf | rndBottom | rndTop => exact absurd hp id

theorem not_rndC_of_mem_needUnion {ps : List Pos} (hps : ∀ p ∈ ps, p.IsStruct) :
    ∀ s ∈ needUnion ps, ¬ RndC s := by
  induction ps with
  | nil => exact fun _ h ↦ absurd h (Finset.notMem_empty _)
  | cons p ps ih =>
    intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · rcases Finset.mem_union.mp hs with hs | hs
      · rcases Finset.mem_insert.mp hs with rfl | hs
        · exact id
        · obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hs
          exact not_rndC_vcoord q
      · rcases Finset.mem_insert.mp hs with rfl | hs
        · exact not_rndC_of_struct (hps p List.mem_cons_self) false
        · rw [Finset.mem_singleton.mp hs]
          exact not_rndC_of_struct (hps p List.mem_cons_self) true
    · exact ih (fun q hq ↦ hps q (List.mem_cons_of_mem _ hq)) s hs

theorem not_rndC_of_mem_layerReveal {l : Layer} {e : KeyIndex} {x : Encoding} :
    ∀ s ∈ layerReveal l e x, ¬ RndC s := by
  intro s hs
  rcases Finset.mem_union.mp hs with hs | hs
  · rcases Finset.mem_union.mp hs with hs | hs
    · exact not_rndC_of_mem_needUnion (fun _ hp ↦ isStruct_of_mem_layerPos hp) s hs
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
      exact not_rndC_vcoord _
  · obtain ⟨lev, -, rfl⟩ := Finset.mem_image.mp hs
    exact not_rndC_vcoord _

theorem not_rndC_of_mem_rootReveal (r : SigningRequest) : ∀ s ∈ rootReveal r, ¬ RndC s := by
  intro s hs
  rw [Finset.mem_singleton.mp hs]
  exact not_rndC_vcoord _

theorem not_rndC_of_mem_pkReveal : ∀ s ∈ pkReveal, ¬ RndC s := by
  intro s hs
  rcases Finset.mem_insert.mp hs with rfl | hs
  · exact id
  · rw [Finset.mem_singleton.mp hs]
    exact id

/-! ## The searches of a signature -/

theorem truncateHash_tabR {T : Finset HPos} (w : RevealVals HD T) (p : Pos) :
    truncateHash (tabR w p) = extendT w (loC p) :=
  truncateHash_joinHalves _ _

/-- **A layer's randomizer search** reveals its base and searches from it. -/
theorem sRestQ_selectT (B : QReg) {rnd : Pos} {l : Layer} {e : KeyIndex} {msg : MsgBytes}
    (hr : rndLab rnd = some (l, e, msg)) :
    SRestQ P (selectT SelMem cwUpd P B l e msg rnd) := by
  have hs : (rndLab rnd).isSome := by rw [hr]; rfl
  intro μ hμ
  refine ⟨⟨hμ, .inl ⟨rnd, hs, rfl⟩⟩, fun b ↦ ?_⟩
  have he : srchNxT μ (.inr {loC rnd}) b.down = .grd rnd (extendT b.down.1 (loC rnd)) 0 :=
    revNxQ_loC hs _
  rw [show modeCmdNx srchNxT (QuantumComp.Cmd.query (L := LocalSig.instruments)
    (.inr {loC rnd}) B _) μ b = srchNxT μ (.inr {loC rnd}) b.down from rfl, he]
  refine modedP₂_bind (F := fun _ (μ : SrchMode) ↦ μ = .grd rnd (extendT b.down.1 (loC rnd)) 0)
    (F' := fun _ (μ : SrchMode) ↦ μ.Rest) _ _ ⟨trivial, fun _ ↦ rfl⟩ fun _ μ' h ↦ ?_
  subst h
  rw [← truncateHash_tabR]
  exact modedP_readLift_srch _ (modedP_grindT hr B _ _ 0 (Nat.zero_add _))

theorem sRestQ_publishT (B : QReg) (l : Layer) (e : KeyIndex) (ρ : Randomizer) (x : Encoding) :
    SRestQ P (publishT SelMem B l e ρ x) :=
  sRestQ_revealThen _ not_rndC_of_mem_layerReveal _ fun _ ↦ sRestQ_bind _ _
    (sRestQ_progPos B _ fun _ hp ↦ isStruct_of_mem_layerPos hp) fun _ ↦ sRestQ_pure _

theorem sRestQ_signT (B : QReg) (r : SigningRequest) :
    SRestQ P (signT SelMem cwUpd P B r) := by
  refine sRestQ_bind _ _ (sRestQ_selectT B rfl) fun gb ↦ ?_
  refine sRestQ_revealThen _ (not_rndC_of_mem_rootReveal r) _ fun rr ↦ ?_
  refine sRestQ_bind _ _ (sRestQ_selectT B rfl) fun gt ↦ ?_
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  · exact sRestQ_pure _
  · exact sRestQ_pure _
  · exact sRestQ_pure _
  · exact sRestQ_bind _ _ (sRestQ_publishT B _ _ _ _) fun _ ↦
      sRestQ_bind _ _ (sRestQ_publishT B _ _ _ _) fun _ ↦ sRestQ_pure _

theorem sRestQ_challengeT (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0}
      (SufCma.advSpec SigningRequest (Option Signature)) A) :
    ∀ μ : SrchMode, μ.Rest → ModedP (srchOkT P) srchNxT (fun _ (μ : SrchMode) ↦ μ.Rest) μ
      (challengeT SelMem cwUpd P A c) := by
  intro μ hμ
  rcases c with o | ⟨_ | r, E, ℓ⟩
  · exact modedP_readLift_srch _ (modedP_liftOrdinary_srch _ μ hμ)
  · exact modedP_readLift_srch _ (modedP_liftOrdinary_srch _ μ hμ)
  · exact modedP_bind _ _ (sRestQ_bind _ _ (sRestQ_act _) (fun _ ↦ sRestQ_signT _ r) μ hμ)
      fun _ _ μ' h ↦ h

theorem modedP_cast_srch {spec : QuantumOracleSpec.{0, 0}} {ok : SrchMode → spec.Port → Prop}
    {nx : SrchMode → (i : spec.Port) → spec.Result i → SrchMode} {Ω : QReg → Type w}
    {fin : (Σ u, Ω u) → SrchMode → Prop} {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) (μ : SrchMode) :
    ModedP ok nx fin μ (e ▸ y) ↔ ModedP ok nx fin μ y := by
  subst e
  rfl

/-- Substituting trees moded between searches. -/
theorem modedP_substitute_srch {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments spec)
      (QuantumComp.toIPFunctor LocalSig.instruments (XSpec SelMem)))
    (hσ : ∀ A c, ∀ μ : SrchMode, μ.Rest → ModedP (srchOkT P) srchNxT
      (fun _ (μ : SrchMode) ↦ μ.Rest) μ (σ A c)) {Ω : QReg → Type}
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) :
    ∀ μ : SrchMode, μ.Rest → ModedP (srchOkT P) srchNxT (fun _ (μ : SrchMode) ↦ μ.Rest) μ
      (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact fun _ h ↦ h
  | liftBind s c next ih =>
    intro μ hμ
    rw [IFreeM.substitute_liftBind]
    exact modedP_bind _ _ (hσ s c μ hμ) fun u ans μ' h ↦ (modedP_cast_srch ans.2 _ _).mpr
      (ih ans.1 μ' h)

/-! ## The realized challenge prefix -/

theorem parameter_pkT_restrictTo (θ : HPos → Digest) :
    (pkT (restrictTo pkReveal θ)).parameter = θ paramC :=
  (param_tabOf _).trans (extendT_restrictTo (Finset.mem_insert_self _ _) θ)

/-- **The realized challenge prefix is moded** from the free mode, its searches' trials at the
parameter `θ paramC`, ending in a rest mode. -/
theorem modedP_prefixQ (A : Adversary) (θ : HPos → Digest) :
    ModedP (srchOkZ (θ paramC)) (srchNxZ θ) (fun _ (μ : SrchMode) ↦ μ.Rest) .free
      (prefixQ A θ) := by
  have e : prefixQ A θ =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := RSpec SelMem) (.inr pkReveal)
        (QReg.of Unit) (Equiv.uniqueProd (QReg.of Unit) Unit).symm fun mem ↦
          (QComp.act (A := QReg.of ((RSpec SelMem).Out (.inr pkReveal) × QReg.of Unit))
            (B := QReg.of Unit) (SubInstrument.relabel (Equiv.uniqueProd (QReg.of Unit) Unit))).bind
            fun _ ↦ realizeT θ ((challengedT SelMem cwUpd
              (pkT (restrictTo pkReveal θ)).parameter
              (SufCma.withSignLog (A (pkT (restrictTo pkReveal θ))))).bind fun run ↦
                QuantumComp₂.pure (pkT (restrictTo pkReveal θ), run)) :=
    rfl
  rw [e]
  refine ⟨⟨trivial, .inr not_rndC_of_mem_pkReveal⟩, fun b ↦ ⟨trivial, fun _ ↦ ?_⟩⟩
  have he : srchNxZ θ .free (.inr pkReveal) b.down = .free := revNxQ_none not_rndC_of_mem_pkReveal _
  rw [show modeCmdNx (srchNxZ θ) (QuantumComp.Cmd.query (L := LocalSig.instruments)
    (.inr pkReveal) (QReg.of Unit) _) SrchMode.free b = srchNxZ θ .free (.inr pkReveal) b.down
      from rfl, he, ← parameter_pkT_restrictTo θ]
  refine modedP_realizeT_srch θ _ ?_
  exact sRestQ_bind _ _ (modedP_substitute_srch _ (sRestQ_challengeT) _) (fun _ ↦ sRestQ_pure _)
    .free trivial

/-! ## The reveal charges -/

/-- **A repeated reveal of `rnd` with its key unselected**: `loC rnd` already revealed, the key
of `rnd`'s search unselected. -/
def ReRevQ (rnd : Pos) (s : RReg SelMem) : Prop :=
  loC rnd ∈ s.2.2.1 ∧ ∃ l e msg, rndLab rnd = some (l, e, msg) ∧ s.2.2.2 l e = none

open scoped Classical in
/-- **The repeated-reveal charges**: at a reveal of one randomizer base `{loC rnd}`, `2^32` times
the mass of `ReRevQ rnd`; nothing elsewhere. -/
noncomputable def reRevQW : ∀ i : (RSpec SelMem).Port,
    Matrix ((RSpec SelMem).In i × RD) ((RSpec SelMem).In i × RD) ℂ → ℝ≥0∞
  | .inr T, σ =>
    match rndOfT T with
    | some rnd => (randomizerAttemptLimit : ℝ≥0∞) *
        Quantum.Xmss.Hybrid.diagMass {q : Unit × RReg SelMem | ReRevQ rnd q.2} σ
    | none => 0
  | _, _ => 0

end Quantum.Qrom.Xmss

end
