module

public import Quantum.Qrom.Xmss.Multi.Costs.Defs
public import Quantum.Qrom.Xmss.Costs.RecUMove

@[expose] public section

/-!
# The randomizer searches of the `n`-user challenge prefix, as moded programs

The `n`-user analog of `Quantum.Qrom.Xmss.Costs.RecUModes`. The modes: free, or in the search of
user `i`'s randomizer position `rnd` (`rndLab rnd`: its key and message) from the base `base`,
before trial `j`. A reveal of `atU i {loC rnd}` starts the search from the revealed base; a trial
read whose digest is a codeword ends it (free mode), otherwise the next trial follows; the calls
between searches (sponge calls, programs of non-message cells, reveals of one base or none) happen
only in a rest mode (free, or after the last trial).

* `rndOfTN`, `RevOkQN`, `SrchModeN`, `SrchModeN.Rest`, `revNxQN`.
* The allowed calls and the mode after a call, on runtime 1's ports (`srchOkRN`, `srchNxRN`), the
  template's (`srchOkTN`, `srchNxTN`) and runtime 2's with record ports (`srchOkZN`, `srchNxZN`).
* **`modedP_prefixQN`**: the realized challenge prefix `prefixQN A θ` is moded from the free mode,
  user `i`'s trials at the parameter `parQN θ i`, ending in a rest mode. The memo hits of the top
  layer make no call.
* `ReRevQN`, `reRevQWN`: the repeated reveals of a randomizer base with its key unselected.
-/

open Matrix IPFunctor
open scoped ENNReal

universe u v w

namespace Quantum.Qrom.Xmss.Multi

open Quantum QuantumRuntime Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss.Hybrid (restrictTo)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT revealThen progThen readLift
  readLiftQ RevealVals liftRead tmplLens readLens ModedP modedP_bind modedP₂_bind modedP_map
  modeCmdNx)
open Quantum.Qrom.SufCma.Multi (withMuSignLog)

attribute [local irreducible] xmssRom

/- Instance search for the register's memory exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ}

/-! ## Reveals of randomizer bases -/

theorem atU_singleton (i : Fin n) (a : HPos) : atU i {a} = {(i, a)} :=
  Finset.singleton_product_singleton

/-- **User `i`'s randomizer position of a reveal** of a single randomizer base (decided
classically). -/
noncomputable def rndOfTN (T : Finset (HPosN n)) : Option (Fin n × Pos) :=
  @dite _ (∃ k : Fin n × Pos, (rndLab k.2).isSome ∧ T = atU k.1 {loC k.2})
    (Classical.propDecidable _) (fun h ↦ some h.choose) fun _ ↦ none

theorem rndOfTN_spec {T : Finset (HPosN n)} {i : Fin n} {rnd : Pos}
    (h : rndOfTN T = some (i, rnd)) : (rndLab rnd).isSome ∧ T = atU i {loC rnd} := by
  unfold rndOfTN at h
  split_ifs at h with h'
  obtain ⟨h1, h2⟩ := h'.choose_spec
  have e := Option.some.inj h
  exact ⟨(congrArg (fun p ↦ (rndLab p).isSome = true) (congrArg Prod.snd e)).mp h1,
    h2.trans (congrArg₂ (fun a b ↦ atU a {loC b}) (congrArg Prod.fst e) (congrArg Prod.snd e))⟩

theorem rndOfTN_atU {rnd : Pos} (h : (rndLab rnd).isSome) (i : Fin n) :
    rndOfTN (atU i {loC rnd}) = some (i, rnd) := by
  unfold rndOfTN
  split_ifs with h'
  · have e' := Finset.singleton_injective
      ((atU_singleton _ _).symm.trans (h'.choose_spec.2.trans (atU_singleton _ _)))
    exact congrArg some (Prod.ext (congrArg Prod.fst e').symm
      (loC_injective (congrArg Prod.snd e').symm))
  · exact absurd ⟨(i, rnd), h, rfl⟩ h'

theorem rndOfTN_eq_none {T : Finset (HPosN n)} (h : ∀ s ∈ T, ¬ RndC s.2) :
    rndOfTN T = none := by
  rcases hT : rndOfTN T with _ | ⟨i, rnd⟩
  · rfl
  · obtain ⟨hr, rfl⟩ := rndOfTN_spec hT
    exact absurd (rndC_loC hr) (h _ (mk_mem_atU i (Finset.mem_singleton_self _)))

/-- **A reveal the searches allow**: one randomizer base of a user, or no randomizer base. -/
def RevOkQN (T : Finset (HPosN n)) : Prop :=
  (∃ i rnd, (rndLab rnd).isSome ∧ T = atU i {loC rnd}) ∨ ∀ s ∈ T, ¬ RndC s.2

/-! ## The modes -/

/-- **The modes of the randomizer searches**: free; in the search of user `i`'s randomizer
position `rnd` from the base `base`, before trial `j`. -/
inductive SrchModeN (n : ℕ)
  | free
  | grd (i : Fin n) (rnd : Pos) (base : Randomizer) (j : ℕ)

/-- A mode between searches: free, or after the last trial. -/
def SrchModeN.Rest : SrchModeN n → Prop
  | .free => True
  | .grd _ _ _ j => j = randomizerAttemptLimit

/-- The mode after a reveal of `T`, the bases given by `bse`: the search of its randomizer
position from its base, free otherwise. -/
noncomputable def revNxQN (T : Finset (HPosN n)) (bse : Fin n → Pos → Randomizer) :
    SrchModeN n :=
  match rndOfTN T with
  | some (i, rnd) => .grd i rnd (bse i rnd) 0
  | none => .free

theorem revNxQN_congr {T : Finset (HPosN n)} {bse bse' : Fin n → Pos → Randomizer}
    (h : ∀ i rnd, rndOfTN T = some (i, rnd) → bse i rnd = bse' i rnd) :
    revNxQN T bse = revNxQN T bse' := by
  unfold revNxQN
  rcases hT : rndOfTN T with _ | ⟨i, rnd⟩
  · rfl
  · exact congrArg (fun b ↦ SrchModeN.grd i rnd b 0) (h i rnd hT)

theorem revNxQN_atU {rnd : Pos} (h : (rndLab rnd).isSome) (i : Fin n)
    (bse : Fin n → Pos → Randomizer) :
    revNxQN (atU i {loC rnd}) bse = .grd i rnd (bse i rnd) 0 := by
  unfold revNxQN
  rw [rndOfTN_atU h i]

theorem revNxQN_none {T : Finset (HPosN n)} (h : ∀ s ∈ T, ¬ RndC s.2)
    (bse : Fin n → Pos → Randomizer) : revNxQN T bse = .free := by
  unfold revNxQN
  rw [rndOfTN_eq_none h]

variable (P : Fin n → PublicParameter)

/-- **The trial read a mode allows**: in the search of user `i`'s `rnd` from `base` before trial
`j < 2^32`, the trial read of trial `j`'s message-digest cell under user `i`'s parameter. -/
def srchRdOkN : SrchModeN n → HwRead HashOutput HashDomain (QMemN n) → Prop
  | .grd i rnd b j, c => j < randomizerAttemptLimit ∧ ∃ l e msg, rndLab rnd = some (l, e, msg) ∧
      c = trialReadN (trialCell (P i) l e msg b j) (i, l, e)
  | .free, _ => False

/-- **The mode after a read**: free after a codeword digest, the next trial otherwise. -/
noncomputable def srchRdNxN {M' : Type} :
    SrchModeN n → (c : HwRead HashOutput HashDomain M') → c.Result → SrchModeN n
  | .grd i rnd b j, .readH _ _, r =>
      match Codeword.decode (truncateHash (r.1.getD 0)) with
      | some _ => .free
      | none => .grd i rnd b (j + 1)
  | _, _, _ => .free

/-- The calls the modes allow, on runtime 1's ports. -/
def srchOkRN : SrchModeN n → (hwReadSpec HashOutput HashDomain (SelMemN n)).Port → Prop
  | μ, .inl _ => μ.Rest
  | μ, .inr c => srchRdOkN P μ (liftRead (S := HPosN n) c)

/-- The mode after a call of runtime 1. -/
noncomputable def srchNxRN : SrchModeN n →
    (i : (hwReadSpec HashOutput HashDomain (SelMemN n)).Port) →
    (hwReadSpec HashOutput HashDomain (SelMemN n)).Result i → SrchModeN n
  | μ, .inr c, r => srchRdNxN μ c r
  | _, .inl _, _ => .free

/-- The calls the modes allow, on the template's ports. -/
def srchOkTN : SrchModeN n → (XSpecN (SelMemN n) n).Port → Prop
  | μ, .inl (.inl (.inl _)) => μ.Rest
  | μ, .inl (.inl (.inr c)) => srchRdOkN P μ c.1
  | μ, .inl (.inr p) => μ.Rest ∧ ∀ θ : HPosN n → Digest, ProgOkQ (p.1.realize θ)
  | μ, .inr T => μ.Rest ∧ RevOkQN T

/-- The mode after a call of the template: a reveal of one randomizer base starts its search. -/
noncomputable def srchNxTN : SrchModeN n → (i : (XSpecN (SelMemN n) n).Port) →
    (XSpecN (SelMemN n) n).Result i → SrchModeN n
  | μ, .inl (.inl (.inr c)), r => srchRdNxN μ c.1 r
  | _, .inr T, r => revNxQN T fun i rnd ↦ extendTN r.1 (i, loC rnd)
  | _, _, _ => .free

/-- **The calls the modes allow**, on runtime 2's ports with record ports. -/
def srchOkZN : SrchModeN n → (RSpecN n (SelMemN n)).Port → Prop
  | μ, .inl (.inl (.inl _)) => μ.Rest
  | μ, .inl (.inl (.inr c)) => srchRdOkN P μ c
  | μ, .inl (.inr c) => μ.Rest ∧ ProgOkQ c
  | μ, .inr T => μ.Rest ∧ RevOkQN T

/-- **The mode after a call** of runtime 2 with record ports, at the hidden values `θ`. -/
noncomputable def srchNxZN (θ : HPosN n → Digest) : SrchModeN n →
    (i : (RSpecN n (SelMemN n)).Port) → (RSpecN n (SelMemN n)).Result i → SrchModeN n
  | μ, .inl (.inl (.inr c)), r => srchRdNxN μ c r
  | _, .inr T, _ => revNxQN T fun i rnd ↦ θ (i, loC rnd)
  | _, _, _ => .free

/-! ## Runtime 1's searches -/

variable {P}

theorem modedP_readCall_srchN {μ : SrchModeN n} {c : HwRead HashOutput HashDomain (SelMemN n)}
    (h : srchRdOkN P μ (liftRead (S := HPosN n) c)) (B : QReg) :
    ModedP (L := LocalSig.instruments) (srchOkRN P) srchNxRN
      (fun p μ' ↦ μ' = srchRdNxN μ c p.2.2) μ (readCall c B) :=
  ⟨h, fun _ ↦ ⟨trivial, fun _ ↦ rfl⟩⟩

/-- **User `i`'s randomizer search** of `rnd` from its base, from trial `trial` to the last, ends
in a rest mode. -/
theorem modedP_grindTN (i : Fin n) {rnd : Pos} {l : Layer} {e : KeyIndex} {msg : MsgBytes}
    (hr : rndLab rnd = some (l, e, msg)) (B : QReg) (base : Randomizer) :
    ∀ k trial, trial + k = randomizerAttemptLimit →
      ModedP (L := LocalSig.instruments) (srchOkRN P) srchNxRN
        (fun _ (μ : SrchModeN n) ↦ μ.Rest) (.grd i rnd base trial)
        (grindT (SelMemN n) (cwUpdN i) (P i) B l e msg base k trial)
  | 0, trial, hk => by
    show SrchModeN.Rest (.grd i rnd base trial)
    exact (Nat.add_zero trial).symm.trans hk
  | k + 1, trial, hk => by
    rw [grindT]
    refine modedP₂_bind (F := fun r (μ : SrchModeN n) ↦ μ = srchRdNxN (.grd i rnd base trial)
        (.readH (trialCell (P i) l e msg base trial)
          (cwUpdN i l e (trialCell (P i) l e msg base trial))) r)
      (F' := fun _ (μ : SrchModeN n) ↦ μ.Rest) _ _
      (modedP_readCall_srchN (μ := .grd i rnd base trial) ⟨by omega, l, e, msg, hr, rfl⟩ B)
      fun r μ hμ ↦ ?_
    subst hμ
    show ModedP _ _ _ (match Codeword.decode (truncateHash (r.1.getD 0)) with
      | some _ => SrchModeN.free
      | none => SrchModeN.grd i rnd base (trial + 1))
      (match Codeword.decode (truncateHash (r.1.getD 0)) with
      | some x => QuantumComp₂.pure (some (base + BitVec.ofNat digestBits trial, x))
      | none => grindT (SelMemN n) (cwUpdN i) (P i) B l e msg base k (trial + 1))
    split
    · trivial
    · exact modedP_grindTN i hr B base k (trial + 1) (by omega)

/-- **Lifting runtime 1's moded programs to templates.** -/
theorem modedP_readLift_srchN {Ω : QReg → Type} {A : QReg}
    {fin : (Σ u, Ω u) → SrchModeN n → Prop}
    (y : QuantumComp LocalSig.instruments (hwReadSpec HashOutput HashDomain (SelMemN n)) Ω A)
    {μ : SrchModeN n} (hy : ModedP (srchOkRN P) srchNxRN fin μ y) :
    ModedP (srchOkTN P) srchNxTN fin μ (readLift goodQN y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ μ (IFreeM.mapLens (readLens goodQN) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨hy.1, fun b ↦ ?_⟩
      rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;> rcases μ with _ | ⟨i, rnd, base, j⟩ <;>
        exact ih _ (hy.2 (ULift.up (b.down.1, b.down.2.2)))

/-- A sponge program of runtime 1 is moded between searches. -/
theorem modedP_liftOrdinary_srchN {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments (spongeSpec HashOutput HashDomain) Ω A) :
    ∀ μ : SrchModeN n, μ.Rest →
      ModedP (srchOkRN P) srchNxRN (fun _ (μ : SrchModeN n) ↦ μ.Rest) μ
        (y.liftOrdinary (t := hwReadCmdSpec HashOutput HashDomain (SelMemN n))) := by
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

theorem srchNxZN_rec_eq (θ : HPosN n → Digest) (μ : SrchModeN n) (T : Finset (HPosN n))
    (m : QMemN n) : srchNxZN θ μ (.inr T) m = srchNxTN μ (.inr T) (restrictTo T θ, m) :=
  revNxQN_congr fun i _ hr ↦ (extendTN_restrictTo
    (by rw [(rndOfTN_spec hr).2]; exact mk_mem_atU i (Finset.mem_singleton_self _)) θ).symm

/-- **Realizing keeps the modes.** -/
theorem modedP_realizeT_srchN (θ : HPosN n → Digest) {L : LocalSig.{u, v}} {Ω : QReg → Type w}
    {A : QReg} {fin : (Σ u, Ω u) → SrchModeN n → Prop}
    (y : QuantumComp L (XSpecN (SelMemN n) n) Ω A) {μ : SrchModeN n}
    (hy : ModedP (srchOkTN P) srchNxTN fin μ y) :
    ModedP (srchOkZN P) (srchNxZN θ) fin μ (realizeT θ y) := by
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
      exact (congrArg (fun μ' ↦ ModedP (srchOkZN P) (srchNxZN θ) fin μ' _)
        (srchNxZN_rec_eq θ μ T b.down)).mpr h

variable (P) in
/-- A template moded between searches: from every rest mode, it ends in a rest mode. -/
def SRestQN {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments (XSpecN (SelMemN n) n) Ω A) : Prop :=
  ∀ μ : SrchModeN n, μ.Rest →
    ModedP (srchOkTN P) srchNxTN (fun _ (μ : SrchModeN n) ↦ μ.Rest) μ y

theorem sRestQN_bind {A B B' : QReg} {α β : Type} (x : QComp (XSpecN (SelMemN n) n) A B α)
    (g : α → QComp (XSpecN (SelMemN n) n) B B' β) (hx : SRestQN P x)
    (hg : ∀ a, SRestQN P (g a)) : SRestQN P (x.bind g) :=
  fun μ hμ ↦ modedP₂_bind (F := fun _ (μ : SrchModeN n) ↦ μ.Rest)
    (F' := fun _ (μ : SrchModeN n) ↦ μ.Rest) x g (hx μ hμ) fun a μ' h ↦ hg a μ' h

theorem sRestQN_pure {A : QReg} {α : Type} (a : α) :
    SRestQN P (QuantumComp₂.pure (L := LocalSig.instruments) (spec := XSpecN (SelMemN n) n)
      (A := A) a) :=
  fun _ h ↦ h

theorem sRestQN_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    SRestQN P (QComp.act (spec := XSpecN (SelMemN n) n) p) :=
  fun _ hμ ↦ ⟨trivial, fun _ ↦ hμ⟩

theorem sRestQN_map {A B : QReg} {α β : Type} {x : QComp (XSpecN (SelMemN n) n) A B α}
    (g : α → β) (hx : SRestQN P x) : SRestQN P (x.map g) :=
  fun μ hμ ↦ modedP_map g (F := fun _ (μ : SrchModeN n) ↦ μ.Rest) (hx μ hμ)

/-- A reveal of no randomizer base keeps the search modes free. -/
theorem sRestQN_revealThen {B B' : QReg} {α : Type} (T : Finset (HPosN n))
    (hT : ∀ s ∈ T, ¬ RndC s.2)
    (k : RevealVals (HDN n) T × QMemN n → QComp (XSpecN (SelMemN n) n) B B' α)
    (hk : ∀ r, SRestQN P (k r)) : SRestQN P (revealThen goodQN T k) := by
  intro μ hμ
  refine ⟨⟨hμ, .inr hT⟩, fun b ↦ ?_⟩
  have he : srchNxTN μ (.inr T) b.down = .free := revNxQN_none hT _
  rw [show modeCmdNx srchNxTN (QuantumComp.Cmd.query (L := LocalSig.instruments)
    (.inr T) B _) μ b = srchNxTN μ (.inr T) b.down from rfl, he]
  exact sRestQN_bind _ _ (sRestQN_act _) (fun _ ↦ hk b.down) _ trivial

theorem sRestQN_progThen {B B' : QReg} {α : Type} {p : Pos} (hp : p.IsStruct) (i : Fin n)
    (k : QComp (XSpecN (SelMemN n) n) B B' α) (hk : SRestQN P k) :
    SRestQN P (progThen (progTN i p) trivial k) := by
  intro μ hμ
  refine ⟨⟨hμ, fun θ ↦ ?_⟩, fun _ ↦ sRestQN_bind _ _ (sRestQN_act _) (fun _ ↦ hk) _ trivial⟩
  refine ⟨cellOf 0 p (tabOf (userOf θ i)), tabOf (userOf θ i) p, realize_progTN hp i 0 θ,
    fun l e h ↦ ?_⟩
  rw [slotOf_cellOf] at h
  cases p with
  | chain => cases h
  | leaf => cases h
  | node => cases h
  | seed | param | prf | rndBottom | rndTop => exact absurd hp id

theorem sRestQN_progPosN (i : Fin n) (B : QReg) :
    ∀ ps : List Pos, (∀ p ∈ ps, p.IsStruct) → SRestQN P (progPosN (SelMemN n) i B ps)
  | [], _ => sRestQN_pure _
  | p :: ps, h => sRestQN_progThen (h p List.mem_cons_self) i _
      (sRestQN_progPosN i B ps fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

/-! ## The coordinates the signatures reveal -/

theorem not_rndC_atU {i : Fin n} {T : Finset HPos} (h : ∀ s ∈ T, ¬ RndC s) :
    ∀ s ∈ atU i T, ¬ RndC s.2 := by
  intro s hs
  unfold atU at hs
  exact h s.2 (Finset.mem_product.1 hs).2

theorem not_rndC_of_mem_pkRevealN : ∀ s ∈ pkRevealN (n := n), ¬ RndC s.2 := by
  intro s hs
  unfold pkRevealN at hs
  exact not_rndC_of_mem_pkReveal s.2 (Finset.mem_product.1 hs).2

/-! ## The searches of a signature -/

theorem truncateHash_tabRN {T : Finset (HPosN n)} (w : RevealVals (HDN n) T) (i : Fin n)
    (p : Pos) : truncateHash (tabRN w i p) = extendTN w (i, loC p) :=
  truncateHash_joinHalves _ _

/-- **User `i`'s randomizer search** reveals its base and searches from it. -/
theorem sRestQN_selectTN (i : Fin n) (B : QReg) {rnd : Pos} {l : Layer} {e : KeyIndex}
    {msg : MsgBytes} (hr : rndLab rnd = some (l, e, msg)) :
    SRestQN P (selectTN (SelMemN n) cwUpdN i (P i) B l e msg rnd) := by
  have hs : (rndLab rnd).isSome := by rw [hr]; rfl
  intro μ hμ
  refine ⟨⟨hμ, .inl ⟨i, rnd, hs, rfl⟩⟩, fun b ↦ ?_⟩
  have he : srchNxTN μ (.inr (atU i {loC rnd})) b.down =
      .grd i rnd (extendTN b.down.1 (i, loC rnd)) 0 :=
    revNxQN_atU hs i _
  rw [show modeCmdNx srchNxTN (QuantumComp.Cmd.query (L := LocalSig.instruments)
    (.inr (atU i {loC rnd})) B _) μ b = srchNxTN μ (.inr (atU i {loC rnd})) b.down from rfl, he]
  refine modedP₂_bind
    (F := fun _ (μ : SrchModeN n) ↦ μ = .grd i rnd (extendTN b.down.1 (i, loC rnd)) 0)
    (F' := fun _ (μ : SrchModeN n) ↦ μ.Rest) _ _ ⟨trivial, fun _ ↦ rfl⟩ fun _ μ' h ↦ ?_
  subst h
  rw [← truncateHash_tabRN]
  exact modedP_readLift_srchN _ (modedP_grindTN i hr B _ _ 0 (Nat.zero_add _))

theorem sRestQN_publishTN (i : Fin n) (B : QReg) (l : Layer) (e : KeyIndex) (ρ : Randomizer)
    (x : Encoding) : SRestQN P (publishTN (SelMemN n) i B l e ρ x) :=
  sRestQN_revealThen _ (not_rndC_atU not_rndC_of_mem_layerReveal) _ fun _ ↦ sRestQN_bind _ _
    (sRestQN_progPosN i B _ fun _ hp ↦ isStruct_of_mem_layerPos hp) fun _ ↦ sRestQN_pure _

/-- The top layer's search, or a memo hit without any call. -/
theorem sRestQN_topTN (i : Fin n) (B : QReg) (r : SigningRequest) (h : Option TopSel) :
    SRestQN P (topTN (SelMemN n) cwUpdN i (P i) B r h) := by
  rcases h with _ | o
  · exact sRestQN_revealThen _ (not_rndC_atU (not_rndC_of_mem_rootReveal r)) _ fun _ ↦
      sRestQN_selectTN i B rfl
  · exact sRestQN_pure _

theorem sRestQN_pubBothN (i : Fin n) (B : QReg) (r : SigningRequest) (gb gt : TopSel) :
    SRestQN P (pubBothN (publishTN (SelMemN n) i B) r gb gt) := by
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  · exact sRestQN_pure _
  · exact sRestQN_pure _
  · exact sRestQN_pure _
  · exact sRestQN_bind _ _ (sRestQN_publishTN i B _ _ _ _) fun _ ↦
      sRestQN_bind _ _ (sRestQN_publishTN i B _ _ _ _) fun _ ↦ sRestQN_pure _

theorem sRestQN_signTN (i : Fin n) (B : QReg) (r : SigningRequest) (h : Option TopSel) :
    SRestQN P (signTN (SelMemN n) cwUpdN i (P i) B r h) := by
  unfold signTN signWithN
  refine sRestQN_bind _ _ (sRestQN_selectTN i B rfl) fun gb ↦ ?_
  refine sRestQN_bind _ _ (sRestQN_topTN i B r h) fun gt ↦ ?_
  exact sRestQN_map _ (sRestQN_pubBothN i B r gb gt)

variable (P) in
theorem sRestQN_challengeTN (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (memoSpec n) A) :
    ∀ μ : SrchModeN n, μ.Rest → ModedP (srchOkTN P) srchNxTN
      (fun _ (μ : SrchModeN n) ↦ μ.Rest) μ (challengeTN (SelMemN n) cwUpdN P A c) := by
  intro μ hμ
  rcases c with o | ⟨_ | ⟨i, q⟩, E, ℓ⟩
  · exact modedP_readLift_srchN _ (modedP_liftOrdinary_srchN _ μ hμ)
  · exact modedP_readLift_srchN _ (modedP_liftOrdinary_srchN _ μ hμ)
  · exact modedP_bind _ _ (sRestQN_bind _ _ (sRestQN_act _)
      (fun _ ↦ sRestQN_signTN i _ q.1 q.2) μ hμ) fun _ _ μ' h ↦ h

theorem modedP_cast_srchN {spec : QuantumOracleSpec.{0, 0}}
    {ok : SrchModeN n → spec.Port → Prop}
    {nx : SrchModeN n → (i : spec.Port) → spec.Result i → SrchModeN n} {Ω : QReg → Type w}
    {fin : (Σ u, Ω u) → SrchModeN n → Prop} {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) (μ : SrchModeN n) :
    ModedP ok nx fin μ (e ▸ y) ↔ ModedP ok nx fin μ y := by
  subst e
  rfl

/-- Substituting trees moded between searches. -/
theorem modedP_substitute_srchN {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments spec)
      (QuantumComp.toIPFunctor LocalSig.instruments (XSpecN (SelMemN n) n)))
    (hσ : ∀ A c, ∀ μ : SrchModeN n, μ.Rest → ModedP (srchOkTN P) srchNxTN
      (fun _ (μ : SrchModeN n) ↦ μ.Rest) μ (σ A c)) {Ω : QReg → Type}
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) :
    ∀ μ : SrchModeN n, μ.Rest → ModedP (srchOkTN P) srchNxTN
      (fun _ (μ : SrchModeN n) ↦ μ.Rest) μ (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact fun _ h ↦ h
  | liftBind s c next ih =>
    intro μ hμ
    rw [IFreeM.substitute_liftBind]
    exact modedP_bind _ _ (hσ s c μ hμ) fun u ans μ' h ↦ (modedP_cast_srchN ans.2 _ _).mpr
      (ih ans.1 μ' h)

/-! ## The realized challenge prefix -/

theorem parameter_pkDN (θ : HPosN n → Digest) (i : Fin n) : (pkDN θ i).parameter = parQN θ i := by
  rw [pkDN_eq]
  rfl

/-- **The realized challenge prefix is moded** from the free mode, user `i`'s trials at the
parameter `parQN θ i`, ending in a rest mode. -/
theorem modedP_prefixQN (A : MuAdversary n) (θ : HPosN n → Digest) :
    ModedP (srchOkZN (parQN θ)) (srchNxZN θ) (fun _ (μ : SrchModeN n) ↦ μ.Rest) .free
      (prefixQN A θ) := by
  have e : prefixQN A θ =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := RSpecN n (SelMemN n))
        (.inr pkRevealN) (QReg.of Unit) (Equiv.uniqueProd (QReg.of Unit) Unit).symm fun mem ↦
          (QComp.act (A := QReg.of ((RSpecN n (SelMemN n)).Out (.inr pkRevealN) × QReg.of Unit))
            (B := QReg.of Unit)
            (SubInstrument.relabel (Equiv.uniqueProd (QReg.of Unit) Unit))).bind fun _ ↦
            realizeT θ ((challengedTN (SelMemN n) cwUpdN (fun i ↦ (pkDN θ i).parameter)
              (memoFrom (fun _ _ ↦ none) (withMuSignLog (A (pkDN θ))))).bind fun run ↦
                QuantumComp₂.pure (pkDN θ, run)) :=
    rfl
  rw [e]
  refine ⟨⟨trivial, .inr not_rndC_of_mem_pkRevealN⟩, fun b ↦ ⟨trivial, fun _ ↦ ?_⟩⟩
  have he : srchNxZN θ .free (.inr pkRevealN) b.down = .free :=
    revNxQN_none not_rndC_of_mem_pkRevealN _
  have hP : parQN θ = fun i ↦ (pkDN θ i).parameter := funext fun i ↦ (parameter_pkDN θ i).symm
  rw [show modeCmdNx (srchNxZN θ) (QuantumComp.Cmd.query (L := LocalSig.instruments)
    (.inr pkRevealN) (QReg.of Unit) _) SrchModeN.free b = srchNxZN θ .free (.inr pkRevealN) b.down
      from rfl, he, hP]
  refine modedP_realizeT_srchN θ _ ?_
  exact sRestQN_bind _ _ (modedP_substitute_srchN _ (sRestQN_challengeTN _) _)
    (fun _ ↦ sRestQN_pure _) .free trivial

/-! ## The repeated-reveal charges -/

/-- **A repeated reveal of user `i`'s `rnd` with its key unselected**: `(i, loC rnd)` already
revealed, user `i`'s key of `rnd`'s search unselected. -/
def ReRevQN (rnd : Pos) (i : Fin n) (s : RRegN n (SelMemN n)) : Prop :=
  (i, loC rnd) ∈ s.2.2.1 ∧ ∃ l e msg, rndLab rnd = some (l, e, msg) ∧ memAt s (i, l, e) = none

open scoped Classical in
/-- **The repeated-reveal charges**: at a reveal of one randomizer base `atU i {loC rnd}`, `2^32`
times the mass of `ReRevQN rnd i`; nothing elsewhere. -/
noncomputable def reRevQWN : ∀ i : (RSpecN n (SelMemN n)).Port,
    Matrix ((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n))
      ((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n)) ℂ → ℝ≥0∞
  | .inr T, σ =>
    match rndOfTN T with
    | some (i, rnd) => (randomizerAttemptLimit : ℝ≥0∞) *
        Quantum.Xmss.Hybrid.diagMass {q : Unit × RRegN n (SelMemN n) | ReRevQN rnd i q.2} σ
    | none => 0
  | _, _ => 0

end Quantum.Qrom.Xmss.Multi

end
