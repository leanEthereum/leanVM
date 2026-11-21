module

public import Quantum.Sphincs.Assembly.CostRun
public import Quantum.Sphincs.Assembly.PrefixRun
public import Quantum.Xmss.Assembly.CwRev

@[expose] public section

/-!
# Each WOTS key signs one fixed value

In leanSPHINCS the key `K = (l, τ, e)` signs the value at `msgPos K` in every signature (a FORS key
at the bottom, a tree root above), so every counter search of `K` runs on the same value
`valsOf v (msgPos K)`. This file proves the invariant that every stored selection of `K` is a trial
block of that search, along every call of the realized challenge prefix (the part of leanXMSS's
`Quantum.Xmss.Assembly.NoReuse` invariant `SelLab` that survives without leaf reuse; leanSPHINCS
has no randomizer labels).

* **Trial blocks** (`encBlk`, `SelKey`, `selKey_cwUpd`, `trialUpd_inj`): the block of `K`'s trial
  at counter `n` on the value `m`; the invariant on the selections; a trial read of `K` on its
  value keeps it; a trial's update determines its key and its block.
* **Modes** (`KMode`, `kOpt`, `KeyRd`, `kOkT`, `kNxT`, `kOkZ`, `kNxZ`): a mode is the values of the
  last reveal at the value positions; a read is allowed if it is a `k`, `k'` read keeping the
  memory or a trial read of a key `K` whose block is a trial block on the remembered value at
  `msgPos K`.
* **The challenge prefix is moded** (`chgK_grindK`, `kModed_readLift`, `kAll_signLayerT`,
  `kAll_signT`, `kAll_challengeT`, `kAll_prefixT`, `kModed_realizeT`): every counter search runs
  right after the reveal of `msgPos K`, so on the remembered value; realizing keeps the modes, the
  remembered values becoming those of `v`.
* **The invariant** (`KInv`, `kInv_step`, `forallQueries_selKey`): on every call of
  `prefixR pol A p v` the remembered values agree with `valsOf v` and the selections satisfy
  `SelKey`. At a trial read of key `K` this gives a re-grind (`sameGrind_of_kInv`): if `K` is
  selected, the selection and the trial are blocks of the same search.
-/

universe u v w

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest Message)
open Quantum.Xmss (X Z blocks trunc128)
open Quantum.Xmss.Hybrid (LazyProg restrictTo clsKraus_ne_zero_cls hwProgKraus_ne_zero_snd)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT tmplLens readLift readLens
  readLiftQ revealThen progThen RevealVals hashTrial rdRoundU rdHU liftRead recStep recStep_branch
  recKraus_ne_zero ModedP modedP_bind modedP₂_bind SChg sChg_bind sChg_pure sChg_map sChg_mono
  chg_act chg_map isChargeBound_simulate isChargeBound_mono_charge forallQueries_of_modedP)

namespace Quantum.Sphincs.Assembly

/- Instance search for `DecidableEq (Mem HPos)` (the read ports' memory) exceeds the default
size. -/
set_option synthInstance.maxSize 2000

/-! ## Trial blocks -/

section blocks

variable (pub : Pub)

/-- **The block of key `K`'s trial at counter `n` on the value `m`** (its input is one block,
`blocks_encIn`). -/
def encBlk (K : Key) (m : Digest) (n : EncodingCounter) : X :=
  (blocks (encIn pub K m n)).headD 0

/-- **Every stored selection of a key is a trial block of its search** on the value `f` gives at
its message position. -/
def SelKey (f : ValPos → Digest) (sel : Selections) : Prop :=
  ∀ K b, sel K = some b → ∃ n, b.1 = encBlk pub K (f (msgPos K)) n

/-- **A selection after a trial read** is an earlier one or the trial's block for its key. -/
theorem cwUpd_eq_some_cases {K : Key} {x xi : X} {sel : Selections} {o : Option X} {K' : Key}
    {b : X × Digest} (h : cwUpd K x xi sel o K' = some b) :
    sel K' = some b ∨ (K' = K ∧ b.1 = x) := by
  rcases o with _ | w
  · exact .inl h
  · rcases cwUpd_some K x xi sel w with h' | h'
    · rw [h'] at h
      exact .inl h
    · rw [h'] at h
      rcases cwSel_eq sel K x xi w with h'' | h''
      · rw [h''] at h
        exact .inl h
      · rw [h''] at h
        by_cases hK : K' = K
        · subst hK
          rw [Selections.select_self] at h
          exact .inr ⟨rfl, by rw [← Option.some.inj h]⟩
        · rw [Selections.select_of_ne _ _ _ hK] at h
          exact .inl h

/-- **A trial read of key `K` with a trial block of its search keeps `SelKey`.** -/
theorem selKey_cwUpd {f : ValPos → Digest} {sel : Selections} (h : SelKey pub f sel) {K : Key}
    {x : X} (hx : ∃ n, x = encBlk pub K (f (msgPos K)) n) (xi : X) (o : Option X) :
    SelKey pub f (cwUpd K x xi sel o) := by
  intro K' b hb
  rcases cwUpd_eq_some_cases hb with h' | ⟨rfl, hb'⟩
  · exact h K' b h'
  · obtain ⟨n, hn⟩ := hx
    exact ⟨n, hb'.trans hn⟩

/-- A filter whose count is a product of positive numbers has a member. -/
theorem exists_of_card_filter_eq_mul {α : Type} [Fintype α] {p : α → Prop} [DecidablePred p]
    {a b : ℕ} (h : (Finset.univ.filter p).card = a * b) (ha : 0 < a) (hb : 0 < b) : ∃ x, p x := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (h ▸ Nat.mul_pos ha hb)
  exact ⟨x, (Finset.mem_filter.mp hx).2⟩

set_option exponentiation.threshold 1024 in
/-- **A trial's update determines its key and its block** (a codeword value of the read cell
selects the trial's block for its key). -/
theorem trialUpd_inj {t t' : TrialPt} (h : trialUpd t' = trialUpd t) :
    t'.K = t.K ∧ t'.x = t.x := by
  have hc : 0 < cwCount := Nat.pos_of_ne_zero fun h0 ↦ by
    have := rhoCw_pos
    simp [rhoCw, h0] at this
  obtain ⟨w, hw⟩ := exists_of_card_filter_eq_mul (card_codeword_trunc128 t.xi) hc
    (Nat.two_pow_pos _)
  set m₀ : Mem HPos := (∅, fun _ ↦ none) with hm₀
  have h1 : (trialUpd t' m₀ (some w)).2 t.K = (trialUpd t m₀ (some w)).2 t.K :=
    congrArg (fun m' : Mem HPos ↦ m'.2 t.K) (congrFun (congrFun h m₀) (some w))
  have hR : (trialUpd t m₀ (some w)).2 t.K = some (t.x, trunc128 (t.xi + w)) := by
    rw [show trialUpd t m₀ (some w) = (m₀.1, cwUpd t.K t.x t.xi m₀.2 (some w)) from rfl,
      snd_pair, cwUpd_some_of_none t.K t.x t.xi (show m₀.2 t.K = none from rfl), cwSel,
      ite_eq_left hw, Selections.select_self]
  have hL : (trialUpd t' m₀ (some w)).2 t.K = cwSel m₀.2 t'.K t'.x t'.xi w t.K := by
    rw [show trialUpd t' m₀ (some w) = (m₀.1, cwUpd t'.K t'.x t'.xi m₀.2 (some w)) from rfl,
      snd_pair, cwUpd_some_of_none t'.K t'.x t'.xi (show m₀.2 t'.K = none from rfl)]
  rw [hR, hL] at h1
  rcases cwSel_eq m₀.2 t'.K t'.x t'.xi w with he | he
  · rw [he] at h1
    exact absurd h1 (by simp [hm₀])
  · rw [he] at h1
    by_cases hK : t.K = t'.K
    · rw [hK, Selections.select_self] at h1
      exact ⟨hK.symm, (Prod.mk.inj (Option.some.inj h1)).1⟩
    · rw [Selections.select_of_ne _ _ _ hK] at h1
      exact absurd h1 (by simp [hm₀])

/-- Two blocks of the same counter search: trials of key `K` on the same value. -/
def SameGrind (K : Key) (x x' : X) : Prop :=
  ∃ (m : Digest) (n n' : EncodingCounter), x = encBlk pub K m n ∧ x' = encBlk pub K m n'

end blocks

/-! ## Modes: the values of the last reveal -/

section modes

/-- The modes: the values of the last reveal at the value positions. -/
abbrev KMode : Type := ValPos → Option Digest

/-- The values a reveal returns at the value positions, `none` off them. -/
def kOpt {T : Finset HPos} (w : RevealVals XD T) (p : ValPos) : Option Digest :=
  if HPos.val p ∈ T then some (extendVals w p) else none

/-- The remembered values are those of `f`. -/
def KAgree (τ : KMode) (f : ValPos → Digest) : Prop :=
  ∀ p d, τ p = some d → f p = d

theorem kOpt_of_mem {T : Finset HPos} (w : RevealVals XD T) {q : ValPos} (h : HPos.val q ∈ T) :
    kOpt w q = some (extendVals w q) := by
  unfold kOpt
  exact ite_eq_left h

theorem kAgree_kOpt (v : (s : HPos) → XD s) (T : Finset HPos) :
    KAgree (kOpt (restrictTo T v)) (valsOf v) := by
  intro p d h
  unfold kOpt at h
  split_ifs at h with hp
  rw [← Option.some.inj h, extendVals_restrictTo hp v]
  rfl

variable (pub : Pub)

/-- **The reads a mode allows on runtime 1's ports**: a `k`, `k'` read keeping the memory, or a
trial read of key `K` whose block is a trial block on the remembered value at `msgPos K`. -/
def KeyRd1 (τ : KMode) (c : HwRead X Z Selections) : Prop :=
  (∃ x, c = .readK x keepMem) ∨ (∃ x, c = .readK' x keepMem) ∨
    ∃ (z : Z) (K : Key) (b xi : X) (m : Digest) (n : EncodingCounter),
      c = .readH z (cwUpd K b xi) ∧ τ (msgPos K) = some m ∧ b = encBlk pub K m n

/-- **The reads a mode allows on the labelled memory.** -/
def KeyRd (τ : KMode) (c : HwRead X Z (Mem HPos)) : Prop :=
  (∃ x, c = readKPort x) ∨ (∃ x, c = readK'Port x) ∨
    ∃ (z : Z) (t : TrialPt) (m : Digest) (n : EncodingCounter),
      c = .readH z (trialUpd t) ∧ τ (msgPos t.K) = some m ∧ t.x = encBlk pub t.K m n

theorem keyRd_liftRead {τ : KMode} {c : HwRead X Z Selections} (h : KeyRd1 pub τ c) :
    KeyRd pub τ (liftRead (S := HPos) c) := by
  rcases h with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ⟨z, K, b, xi, m, n, rfl, hτ, hb⟩
  · exact .inl ⟨x, rfl⟩
  · exact .inr (.inl ⟨x, rfl⟩)
  · exact .inr (.inr ⟨z, ⟨K, b, xi⟩, m, n, rfl, hτ, hb⟩)

open scoped Classical in
/-- The charge of runtime 1's ports: `1` on the reads the mode does not allow. -/
noncomputable def kBad (τ : KMode) : (hwReadSpec X Z Selections).Port → ℕ
  | .inl _ => 0
  | .inr c => if KeyRd1 pub τ c then 0 else 1

theorem kBad_le_one (τ : KMode) (i : (hwReadSpec X Z Selections).Port) : kBad pub τ i ≤ 1 := by
  rcases i with _ | c
  · exact Nat.zero_le _
  · by_cases h : KeyRd1 pub τ c <;> simp [kBad, h]

theorem keyRd1_of_kBad {τ : KMode} {c : HwRead X Z Selections} (h : kBad pub τ (.inr c) ≤ 0) :
    KeyRd1 pub τ c := by
  by_contra hc
  simp only [kBad, hc, ↓reduceIte] at h
  omega

/-- The calls the modes allow, on the template's ports. -/
def kOkT (τ : KMode) : (SSpec Selections).Port → Prop
  | .inl (.inl (.inr c)) => KeyRd pub τ c.1
  | _ => True

/-- The mode after a call of the template: a reveal remembers its values. -/
def kNxT (τ : KMode) : (i : (SSpec Selections).Port) → (SSpec Selections).Result i → KMode
  | .inr _, r => kOpt r.1
  | _, _ => τ

/-- The calls the modes allow, on runtime 2's ports with record ports. -/
def kOkZ (τ : KMode) : (recHwSpec X Z HPos Selections).Port → Prop
  | .inl (.inl (.inr c)) => KeyRd pub τ c
  | _ => True

/-- The mode after a call of runtime 2 with record ports, at the hidden values `v`. -/
def kNxZ (v : (s : HPos) → XD s) (τ : KMode) :
    (i : (recHwSpec X Z HPos Selections).Port) → (recHwSpec X Z HPos Selections).Result i →
      KMode
  | .inr T, _ => kOpt (restrictTo T v)
  | _, _ => τ

end modes

/-! ## Runtime 1's counter searches -/

section grind

variable (pub : Pub) {τ : KMode}

theorem chgK_readCall {c : HwRead X Z Selections} (hc : KeyRd1 pub τ c) (B : QReg) :
    IFreeM.IsChargeBound (readCall c B) (portCharge (kBad pub τ)) 0 := by
  unfold readCall
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    ((IFreeM.isChargeBound_liftBind_iff _ _ _).mpr
      ⟨Nat.le_of_eq (show kBad pub τ (.inr c) = 0 from ite_eq_left hc), fun _ ↦ trivial⟩)
    fun _ ↦ FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ trivial

theorem sChgK_readCall {c : HwRead X Z Selections} (hc : KeyRd1 pub τ c) (B : QReg) {β : Type}
    (g : c.Result → List (SpongeRead X Z) → β × List (SpongeRead X Z)) :
    SChg (kBad pub τ) (fun log ↦ (readCall c B).bind fun r ↦ QuantumComp₂.pure (g r log) :
      StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z Selections) B B) β) 0 := by
  intro log
  show IFreeM.IsChargeBound ((readCall c B).bind fun r ↦ QuantumComp₂.pure (g r log)) _ _
  exact FreeM₂.isChargeBound_bind (n₂ := 0) (chgK_readCall pub hc B) fun _ ↦ trivial

/-- **A trial's round of reads** of key `K` with a trial block on the remembered value. -/
theorem sChgK_rdRoundU {K : Key} {m : Digest} (hτ : τ (msgPos K) = some m)
    (π : Equiv.Perm (X × Z)) (B : QReg) (s : X × Z) (n : EncodingCounter) :
    SChg (kBad pub τ) (rdRoundU Selections (cwUpd K) π B s (encBlk pub K m n)) 0 :=
  sChg_mono _ (sChg_bind _ (sChgK_readCall pub (c := .readK _ keepMem) (.inl ⟨_, rfl⟩) B _)
    fun _ ↦ sChg_bind _ (sChgK_readCall pub (c := .readK' _ keepMem) (.inr (.inl ⟨_, rfl⟩)) B _)
      fun _ ↦ sChg_bind _ (sChgK_readCall pub (c := .readH _ (cwUpd K _ _))
        (.inr (.inr ⟨_, K, _, _, m, n, rfl, hτ, rfl⟩)) B _) fun _ ↦ sChg_pure _ _ 0) (by omega)

/-- **A counter trial's hash** on the remembered value. -/
theorem chgK_hashTrial {K : Key} {m : Digest} (hτ : τ (msgPos K) = some m)
    (π : Equiv.Perm (X × Z)) (B : QReg) (c : ℕ) :
    IFreeM.IsChargeBound (hashTrial Selections (cwUpd K) π B (trialInput pub K m c))
      (portCharge (kBad pub τ)) 0 := by
  have hb : blocks (trialInput pub K m c) =
      [encBlk pub K m (BitVec.ofNat counterBits c)] :=
    blocks_encIn pub K m _
  unfold hashTrial
  rw [StateT.run'_eq, hb, List.foldlM_cons]
  exact chg_map _ _ (sChg_map _ _ (sChg_map _ _ (sChg_mono _ (sChg_bind _
    (sChgK_rdRoundU pub hτ π B (0, 0) _) fun _ ↦ sChg_pure _ _ 0) le_rfl)) [])

/-- **The counter search** on the remembered value calls only allowed reads. -/
theorem chgK_grindK {K : Key} {m : Digest} (hτ : τ (msgPos K) = some m) (B : QReg) :
    ∀ n c, IFreeM.IsChargeBound (grindK Selections cwUpd pub B K m n c)
      (portCharge (kBad pub τ)) 0
  | 0, _ => trivial
  | n + 1, c => by
    rw [grindK]
    refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgK_hashTrial pub hτ pub.perm B c)
      fun out ↦ ?_
    split
    · trivial
    · exact chgK_grindK hτ B n (c + 1)

/-- A simulated permutation program makes no read calls. -/
theorem chgK_simulate (π : Equiv.Perm (X × Z)) {Ω : QReg → Type} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (qrpmSpec (X × Z)) Ω A} {q : ℕ}
    (hx : x.IsTotalQueryBound q) :
    IFreeM.IsChargeBound ((simulate LocalSig.Interp.instruments π x).liftOrdinary
      (t := hwReadCmdSpec X Z Selections)) (portCharge (kBad pub τ)) 0 := by
  refine (isChargeBound_mono_charge (fun s a ↦ ?_)
    (isChargeBound_simulate (M := Selections) 0 1 π hx)).mono (le_of_eq (zero_mul _))
  rcases a with o | ⟨i | c, E, ℓ⟩
  · exact le_rfl
  · exact le_rfl
  · exact kBad_le_one pub τ (.inr c)

end grind

/-! ## The challenge prefix is moded -/

section moded

variable (pub : Pub)

/-- **Runtime 1's programs with only allowed reads** are moded on the template, in their mode. -/
theorem kModed_readLift {Ω : QReg → Type} {A : QReg} {fin : (Σ u, Ω u) → KMode → Prop}
    (y : QuantumComp LocalSig.instruments (hwReadSpec X Z Selections) Ω A) (τ : KMode)
    (hy : IFreeM.IsChargeBound y (portCharge (kBad pub τ)) 0) (hfin : ∀ p, fin p τ) :
    ModedP (kOkT pub) kNxT fin τ (readLift goodAll y) := by
  induction y using IFreeM.inductionOn with
  | pure _ a => exact hfin _
  | liftBind _ c next ih =>
    show ModedP _ _ _ τ (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    obtain ⟨hy1, hy2⟩ := (IFreeM.isChargeBound_liftBind_iff _ _ _).1 hy
    rcases c with o | ⟨i | c, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ ((hy2 _).mono (Nat.sub_le _ _))⟩
    · exact ⟨trivial, fun b ↦ ih _ ((hy2 _).mono (Nat.sub_le _ _))⟩
    · exact ⟨keyRd_liftRead pub (keyRd1_of_kBad pub hy1), fun b ↦
        ih _ ((hy2 _).mono (Nat.sub_le _ _))⟩

theorem kModed_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × Selections) → QComp (SSpec Selections) B B' α)
    {F : α → KMode → Prop} {τ : KMode}
    (hk : ∀ r, ModedP (kOkT pub) kNxT (fun p τ' ↦ F p.2.2 τ') (kOpt r.1) (k r)) :
    ModedP (kOkT pub) kNxT (fun p τ' ↦ F p.2.2 τ') τ (revealThen goodAll T k) :=
  ⟨trivial, fun b ↦ modedP₂_bind (F := fun _ τ' ↦ τ' = kOpt b.down.1) _ _ ⟨trivial, fun _ ↦ rfl⟩
    fun _ τ' h ↦ by subst h; exact hk b.down⟩

/-- A template moded from every mode. -/
def KAll {B B' : QReg} {α : Type} (y : QComp (SSpec Selections) B B' α) : Prop :=
  ∀ τ, ModedP (kOkT pub) kNxT (fun _ _ ↦ True) τ y

theorem kAll_bind {A B B' : QReg} {α β : Type} (x : QComp (SSpec Selections) A B α)
    (g : α → QComp (SSpec Selections) B B' β) (hx : KAll pub x) (hg : ∀ a, KAll pub (g a)) :
    KAll pub (x.bind g) :=
  fun τ ↦ modedP₂_bind (F := fun _ _ ↦ True) (F' := fun _ _ ↦ True) x g (hx τ)
    fun a τ' _ ↦ hg a τ'

theorem kAll_pure {A : QReg} {α : Type} (a : α) :
    KAll pub
      (QuantumComp₂.pure (L := LocalSig.instruments) (spec := SSpec Selections) (A := A) a) :=
  fun _ ↦ trivial

theorem kAll_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    KAll pub (QComp.act (spec := SSpec Selections) p) :=
  fun _ ↦ ⟨trivial, fun _ ↦ trivial⟩

theorem kAll_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × Selections) → QComp (SSpec Selections) B B' α)
    (hk : ∀ r, KAll pub (k r)) : KAll pub (revealThen goodAll T k) :=
  fun _ ↦ kModed_revealThen pub T k (F := fun _ _ ↦ True) fun r ↦ hk r _

theorem kAll_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (SSpec Selections) B B' α) (hk : KAll pub k) : KAll pub (progThen p hp k) :=
  fun τ ↦ ⟨trivial, fun _ ↦ kAll_bind pub _ _ (kAll_act pub _) (fun _ ↦ hk) τ⟩

theorem kAll_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    KAll pub (progPorts Selections B ps) := by
  induction ps with
  | nil => exact kAll_pure pub _
  | cons p ps ih => exact kAll_progThen pub p trivial _ ih

theorem kAll_progSlots (B : QReg) (ss : List Slot) :
    KAll pub (progSlots Selections pub B ss) := by
  induction ss with
  | nil => exact kAll_pure pub _
  | cons s ss ih => exact kAll_bind pub _ _ (kAll_progPorts pub B _) fun _ ↦ ih

theorem kAll_forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    KAll pub (forsOpenT Selections pub B idx lv) := by
  unfold forsOpenT
  exact kAll_revealThen pub _ _ fun _ ↦
    kAll_bind pub _ _ (kAll_progSlots pub B _) fun _ ↦ kAll_pure pub _

/-- **A layer signature**: its counter search runs right after the reveal of `msgPos K`, on the
revealed value. -/
theorem kAll_signLayerT (B : QReg) (K : Key) :
    KAll pub (signLayerT Selections cwUpd pub B K) := by
  intro τ
  unfold signLayerT
  refine kModed_revealThen pub _ _ (F := fun _ _ ↦ True) fun r₀ ↦ ?_
  refine modedP₂_bind (F := fun _ τ' ↦ τ' = kOpt r₀.1) (F' := fun _ _ ↦ True) _ _
    (kModed_readLift pub _ _ (chgK_grindK pub (kOpt_of_mem r₀.1 (Finset.mem_singleton_self _))
      B _ _) fun _ ↦ rfl) fun g τ' h ↦ ?_
  subst h
  rcases g with _ | ⟨c, x⟩
  · trivial
  · exact kAll_revealThen pub _ _ (fun r ↦ kAll_bind pub _ _ (kAll_progSlots pub B _)
      fun _ ↦ kAll_pure pub _) _

/-- **A signature** is moded, for every digest policy. -/
theorem kAll_signT (pol : DigestPolicy) (B : QReg) (msg : Message) :
    KAll pub (signT Selections cwUpd pol pub B msg) := by
  unfold signT
  refine kAll_revealThen pub _ _ fun _ ↦ kAll_revealThen pub _ _ fun _ ↦ ?_
  refine kAll_bind pub _ _ (kAll_progPorts pub B _) fun _ ↦ ?_
  refine kAll_bind pub _ _ (kAll_forsOpenT pub B _ _) fun _ ↦ ?_
  refine kAll_bind pub _ _ (kAll_signLayerT pub B _) fun s₀ ↦ ?_
  rcases s₀ with _ | bottom
  · exact kAll_pure pub _
  · refine kAll_bind pub _ _ (kAll_signLayerT pub B _) fun s₁ ↦ ?_
    rcases s₁ with _ | middle
    · exact kAll_pure pub _
    · refine kAll_bind pub _ _ (kAll_signLayerT pub B _) fun s₂ ↦ ?_
      rcases s₂ with _ | top <;> exact kAll_pure pub _

/-- **The challenger** is moded, for every digest policy. -/
theorem kAll_challengeT (pol : DigestPolicy) (A : QReg)
    (cmd : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) (τ : KMode) :
    ModedP (kOkT pub) kNxT (fun _ _ ↦ True) τ (challengeT Selections cwUpd pol pub A cmd) := by
  rcases cmd with o | ⟨q | msg, E, ℓ⟩
  · exact kModed_readLift pub _ τ (chgK_simulate pub _ (q := 0)
      ((QuantumComp.isTotalQueryBound_primBind_iff _ _ _).mpr fun _ ↦ trivial)) fun _ ↦ trivial
  · exact kModed_readLift pub _ τ (chgK_simulate pub _ (q := 1)
      ((QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
        ⟨Nat.one_pos, fun _ ↦ trivial⟩)) fun _ ↦ trivial
  · exact modedP_bind _ _ (kAll_bind pub _ _ (kAll_act pub _)
      (fun _ ↦ kAll_signT pub pol _ msg) τ) fun _ _ _ _ ↦ trivial

theorem kModed_cast {spec : QuantumOracleSpec.{0, 0}} {ok : KMode → spec.Port → Prop}
    {nx : KMode → (i : spec.Port) → spec.Result i → KMode} {Ω : QReg → Type w}
    {fin : (Σ u, Ω u) → KMode → Prop} {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) (τ : KMode) :
    ModedP ok nx fin τ (e ▸ y) ↔ ModedP ok nx fin τ y := by
  subst e
  rfl

/-- Substituting trees moded from every mode. -/
theorem kAll_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments spec)
      (QuantumComp.toIPFunctor LocalSig.instruments (SSpec Selections)))
    (hσ : ∀ A c τ, ModedP (kOkT pub) kNxT (fun _ _ ↦ True) τ (σ A c)) {Ω : QReg → Type}
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) :
    ∀ τ, ModedP (kOkT pub) kNxT (fun _ _ ↦ True) τ (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact fun _ ↦ trivial
  | liftBind s c next ih =>
    intro τ
    rw [IFreeM.substitute_liftBind]
    exact modedP_bind _ _ (hσ s c τ) fun u ans τ' _ ↦ (kModed_cast ans.2 _ _).mpr (ih ans.1 τ')

/-- **The challenge prefix is moded**, for every digest policy. -/
theorem kAll_prefixT (pol : DigestPolicy) (A : SAdversary) :
    KAll pub (prefixT Selections cwUpd pol pub A) := by
  unfold prefixT challengedT
  exact kAll_revealThen pub _ _ fun _ ↦
    kAll_bind pub _ _ (kAll_substitute pub _ (kAll_challengeT pub pol) _) fun _ ↦ kAll_pure pub _

/-- **Realizing keeps the modes**, the remembered values becoming those of `v`. -/
theorem kModed_realizeT (v : (s : HPos) → XD s) {L : LocalSig.{u, v}} {Ω : QReg → Type w}
    {A : QReg} {fin : (Σ u, Ω u) → KMode → Prop} (y : QuantumComp L (SSpec Selections) Ω A)
    {τ : KMode} (hy : ModedP (kOkT pub) kNxT fin τ y) :
    ModedP (kOkZ pub) (kNxZ v) fin τ (realizeT v y) := by
  induction y using IFreeM.inductionOn generalizing τ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ τ (IFreeM.mapLens (tmplLens v) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨((i | c) | ⟨p, hp⟩) | T, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · cases p <;> exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 (ULift.up (restrictTo T v, b.down)))⟩

/-- **The realized challenge prefix is moded**, from every mode. -/
theorem kModed_prefixR (pol : DigestPolicy) (A : SAdversary) (v : (s : HPos) → XD s)
    (τ : KMode) :
    ModedP (kOkZ pub) (kNxZ v) (fun _ _ ↦ True) τ (prefixR pol A pub v) :=
  kModed_realizeT pub v _ (kAll_prefixT pub pol A τ)

end moded

/-! ## The memory along the ports of `runtimeR` -/

section memStep

variable {S M' : Type} [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M']

/-- The memory a read port's outcome reports (the memory before the read). -/
def kReadPre : (c : HwRead X Z (Finset S × M')) → c.Result → Finset S × M'
  | .readH _ _, r => r.2
  | .readK _ _, r => r.2
  | .readK' _ _, r => r.2

/-- The memory after a read port with outcome `r`. -/
def kReadMem : (c : HwRead X Z (Finset S × M')) → c.Result → Finset S × M'
  | .readH _ u, r => u r.2 r.1
  | .readK _ u, r => u r.2 r.1
  | .readK' _ u, r => u r.2 r.1

theorem kmStep_sponge (m₀ : Finset S × M') (p : SpongePort)
    (r : (recHwSpec X Z S M').Result (.inl (.inl (.inl p))))
    {U U' : Set (HwReg X Z (Finset S × M'))}
    (hU : ∀ s s' : HwReg X Z (Finset S × M'), s'.2 = s.2 → s ∈ U → s' ∈ U')
    (σ : Matrix ((recHwSpec X Z S M').In (.inl (.inl (.inl p))) × HwReg X Z (Finset S × M'))
      ((recHwSpec X Z S M').In (.inl (.inl (.inl p))) × HwReg X Z (Finset S × M')) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z S M').In (.inl (.inl (.inl p))) ×
      HwReg X Z (Finset S × M') ↦ m.2) U σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z S M').Out (.inl (.inl (.inl p))) ×
      HwReg X Z (Finset S × M') ↦ m.2) U'
      (((runtimeR (X := X) (Z := Z) m₀).step (.inl (.inl (.inl p)))).branch r σ) := by
  have hb : ((runtimeR (X := X) (Z := Z) m₀).step (.inl (.inl (.inl p)))).branch r σ =
      MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U p) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m₀ p r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    hU q.2 q'.2 (snd_eq_of_spongeHardwired_U_ne_zero (hwEmpty X Z) m₀ p q.1 q'.1 q.2 q'.2 hK) hq

theorem kmStep_read (m₀ : Finset S × M') (c : HwRead X Z (Finset S × M')) (r : c.Result)
    {U U' : Set (HwReg X Z (Finset S × M'))}
    (hU : ∀ s s' : HwReg X Z (Finset S × M'), s.2.2 = kReadPre c r →
      s'.2 = (s.2.1, kReadMem c r) → s ∈ U → s' ∈ U')
    (σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ)
    (hσ : QuerySupportedOn (fun m : Unit × HwReg X Z (Finset S × M') ↦ m.2) U σ) :
    QuerySupportedOn (fun m : Unit × HwReg X Z (Finset S × M') ↦ m.2) U'
      (((runtimeR (X := X) (Z := Z) m₀).step (.inl (.inl (.inr c)))).branch r σ) := by
  have hb : ((runtimeR (X := X) (Z := Z) m₀).step (.inl (.inl (.inr c)))).branch r σ =
      MatrixMap.conj (hwReadKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m₀ c r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  refine QuerySupportedOn.conj hσ fun q' q hK hq ↦ ?_
  cases c with
  | readH z upd =>
    simp only [hwReadKraus, readKrausH] at hK
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero hK).2
    exact hU q.2 q'.2 hp hφ hq
  | readK x upd =>
    simp only [hwReadKraus, readKrausK] at hK
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero hK).2
    exact hU q.2 q'.2 hp hφ hq
  | readK' x upd =>
    simp only [hwReadKraus, readKrausK'] at hK
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero hK).2
    exact hU q.2 q'.2 hp hφ hq

theorem kmStep_prog (m₀ : Finset S × M') (c : HwProg X Z) (r : c.Result)
    {U U' : Set (HwReg X Z (Finset S × M'))}
    (hU : ∀ s s' : HwReg X Z (Finset S × M'), s'.2.2 = s.2.2 → s ∈ U → s' ∈ U')
    (σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ)
    (hσ : QuerySupportedOn (fun m : Unit × HwReg X Z (Finset S × M') ↦ m.2) U σ) :
    QuerySupportedOn (fun m : Unit × HwReg X Z (Finset S × M') ↦ m.2) U'
      (((runtimeR (X := X) (Z := Z) m₀).step (.inl (.inr c))).branch r σ) := by
  have hb : ((runtimeR (X := X) (Z := Z) m₀).step (.inl (.inr c))).branch r σ =
      MatrixMap.conj (hwProgKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m₀ c r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    hU q.2 q'.2 (by rw [hwProgKraus_ne_zero_snd c r hK]) hq

theorem kmStep_rec (m₀ : Finset S × M') (T : Finset S) (r : Finset S × M')
    {U U' : Set (HwReg X Z (Finset S × M'))}
    (hU : ∀ s s' : HwReg X Z (Finset S × M'), s'.2.2 = (s.2.2.1 ∪ T, s.2.2.2) → s ∈ U → s' ∈ U')
    (σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ)
    (hσ : QuerySupportedOn (fun m : Unit × HwReg X Z (Finset S × M') ↦ m.2) U σ) :
    QuerySupportedOn (fun m : Unit × HwReg X Z (Finset S × M') ↦ m.2) U'
      (((runtimeR (X := X) (Z := Z) m₀).step (.inr T)).branch r σ) := by
  show QuerySupportedOn _ _ ((recStep (X := X) (Z := Z) T).branch r σ)
  rw [recStep_branch]
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    hU q.2 q'.2 (congrArg Prod.snd (recKraus_ne_zero hK)) hq

end memStep

/-! ## The invariant -/

section inv

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- **The invariant of a mode**: the remembered values are those of `v`, and every stored selection
of a key is a trial block of its search on its value. -/
def KInv (τ : KMode) : Set (HwReg X Z (Mem HPos)) :=
  {s | KAgree τ (valsOf v) ∧ SelKey pub (valsOf v) s.2.2.2}

/-- **An allowed read keeps `SelKey`** when the remembered values are those of `v`. -/
theorem selKey_kReadMem {τ : KMode} {c : HwRead X Z (Mem HPos)} (hc : KeyRd pub τ c)
    (hτ : KAgree τ (valsOf v)) (r : c.Result) (h : SelKey pub (valsOf v) (kReadPre c r).2) :
    SelKey pub (valsOf v) (kReadMem c r).2 := by
  rcases hc with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ⟨z, t, m, n, rfl, hm, hx⟩
  · exact h
  · exact h
  · show SelKey pub (valsOf v) (trialUpd t r.2 r.1).2
    rw [show trialUpd t r.2 r.1 = (r.2.1, cwUpd t.K t.x t.xi r.2.2 r.1) from rfl, snd_pair]
    exact selKey_cwUpd pub h ⟨n, by rw [hτ _ _ hm]; exact hx⟩ t.xi r.1

/- Instance search for the run families over the register exceeds the default size (as in
PrefixRun). -/
set_option synthInstance.maxSize 2000 in
/-- **Every allowed call keeps the invariant of its mode.** -/
theorem kInv_step (τ : KMode) (i : (recHwSpec X Z HPos Selections).Port)
    (r : (recHwSpec X Z HPos Selections).Result i)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × HwReg X Z (Mem HPos))
      ((recHwSpec X Z HPos Selections).In i × HwReg X Z (Mem HPos)) ℂ)
    (hok : kOkZ pub τ i)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × HwReg X Z (Mem HPos) ↦
      m.2) (KInv pub v τ) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out i × HwReg X Z (Mem HPos) ↦ m.2)
      (KInv pub v (kNxZ v τ i r)) (((runtimeR (X := X) (Z := Z) m0R).step i).branch r σ) := by
  rcases i with ((p | c) | c) | T
  · refine kmStep_sponge (U := KInv pub v τ) (U' := KInv pub v τ) m0R p r ?_ σ hσ
    intro s s' h hs
    refine ⟨hs.1, ?_⟩
    rw [show s'.2.2.2 = s.2.2.2 from congrArg (fun w ↦ w.2.2) h]
    exact hs.2
  · refine kmStep_read (U := KInv pub v τ) (U' := KInv pub v τ) m0R c r ?_ σ hσ
    intro s s' hpre hpost hs
    refine ⟨hs.1, ?_⟩
    rw [show s'.2.2.2 = (kReadMem c r).2 from congrArg (fun w ↦ w.2.2) hpost]
    exact selKey_kReadMem pub v hok hs.1 r (by rw [← hpre]; exact hs.2)
  · refine kmStep_prog (U := KInv pub v τ) (U' := KInv pub v τ) m0R c r ?_ σ hσ
    intro s s' h hs
    refine ⟨hs.1, ?_⟩
    rw [show s'.2.2.2 = s.2.2.2 from congrArg Prod.snd h]
    exact hs.2
  · refine kmStep_rec (U := KInv pub v τ) (U' := KInv pub v (kOpt (restrictTo T v))) m0R T r ?_
      σ hσ
    intro s s' h hs
    refine ⟨kAgree_kOpt v T, ?_⟩
    rw [h]
    exact hs.2

/-- The initial operator is on the invariant of the empty mode. -/
theorem kInv_initR :
    QuerySupportedOn (fun m : QReg.of Unit × HwReg X Z (Mem HPos) ↦ m.2)
      (KInv pub v fun _ ↦ none) initR := by
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty X Z, m0R) : HwReg X Z (Mem HPos))).matrix) m m' ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · have hI : (((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m0R) :
        HwReg X Z (Mem HPos)) ∈ KInv pub v fun _ ↦ none := by
      refine ⟨fun _ _ h ↦ by simp at h, fun _ _ h ↦ ?_⟩
      exact absurd h (by simp [m0R, m0])
    refine ⟨?_, ?_⟩
    · show m.2 ∈ KInv pub v fun _ ↦ none
      rw [← he.1]
      exact hI
    · show m'.2 ∈ KInv pub v fun _ ↦ none
      rw [← he.2]
      exact hI
  · exact False.elim (h rfl)

/-- **The invariant at the calls of the realized challenge prefix**: for every digest policy,
adversary and template data, every call is presented an operator supported on the invariant of a
mode allowing it. -/
theorem forallQueries_selKey (pol : DigestPolicy) (A : SAdversary) :
    (runtimeR m0R).ForallQueries .instruments (fun i E σ ↦ ∃ τ : KMode, kOkZ pub τ i ∧
      QuerySupportedOn (fun m : ((recHwSpec X Z HPos Selections).In i × HwReg X Z (Mem HPos)) × E ↦
        m.1.2) (KInv pub v τ) σ)
      (prefixR pol A pub v) initR :=
  forallQueries_of_modedP (runtimeR m0R) .instruments (KInv pub v)
    (fun τ i r σ hok hσ ↦ kInv_step pub v τ i r σ hok hσ) (prefixR pol A pub v) (fun _ ↦ none)
    (kModed_prefixR pub pol A v _) (kInv_initR pub v)

/-- **At an allowed trial read on the invariant the trial's block is a trial block of its key's
search on its value**, and every selection is one. -/
theorem trial_of_kInv {τ : KMode} {c : HwRead X Z (Mem HPos)} (hc : KeyRd pub τ c)
    (ht : IsTrial trialUpd c) {s : HwReg X Z (Mem HPos)} (hs : s ∈ KInv pub v τ) :
    ∃ n, (trialOf trialUpd c).2.x =
      encBlk pub (trialOf trialUpd c).2.K (valsOf v (msgPos (trialOf trialUpd c).2.K)) n := by
  have hc' := eq_readH_trialOf trialUpd ht
  rcases hc with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ⟨z, t, m, n, rfl, hm, hx⟩
  · cases hc'
  · cases hc'
  · obtain ⟨-, hu⟩ := HwRead.readH.inj hc'
    obtain ⟨hK, hX⟩ := trialUpd_inj hu.symm
    exact ⟨n, by rw [hK, hX, hs.1 _ _ hm]; exact hx⟩

/-- **A trial read of a selected key on the invariant is a re-grind**: the selection and the trial
are blocks of the same search. -/
theorem sameGrind_of_kInv {τ : KMode} {c : HwRead X Z (Mem HPos)} (hc : KeyRd pub τ c)
    (ht : IsTrial trialUpd c) {s : HwReg X Z (Mem HPos)} (hs : s ∈ KInv pub v τ)
    {sel : X × Digest} (hsel : s.2.2.2 (trialOf trialUpd c).2.K = some sel) :
    SameGrind pub (trialOf trialUpd c).2.K (trialOf trialUpd c).2.x sel.1 := by
  obtain ⟨n, hn⟩ := trial_of_kInv pub v hc ht hs
  obtain ⟨n', hn'⟩ := hs.2 _ sel hsel
  exact ⟨_, n, n', hn, hn'⟩

end inv

end Quantum.Sphincs.Assembly

end
