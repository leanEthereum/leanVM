module

public import Quantum.StdModel.Qrom.ReadGrade
public import Quantum.StdModel.Qrom.Moded
public import Quantum.StdModel.Sphincs.PropsIn

@[expose] public section

/-!
# SM-TCR-C in the QROM

The QROM bound of the restricted SM-TCR-C game `Props.smTcrIn W C D G` for a straight-line
reduction whose challenger calls are all in its setup.

* **Classes** (`GCell`, `SameCls`): a `G`-cell is the input of a target function at a tweak of
  `G`; under `G`-separation (`GSep`) it fixes the parameter and the tweak, and two `G`-cells are in
  the same class when they share them.
* **The memory** (`TMem`): the log of every read's outcome, the cells read, the records (the first
  answer read of a `G`-cell of each class, with its value) and the judge's read.
* **The events**: a recorded cell of a class whose unique record is another cell, with the
  record's truncation (`tgt`, `CellTargetBad`), or a judge's read in the target (`JBad`):
  `BadR = CellTargetBad tgt ∪ JBad`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.StdModel.Qrom.Tcr

open Quantum Quantum.Qrom Quantum.Sponge Props HashSig

/-! ## Classes of target inputs -/

section cells

variable {Par Tw Fn Out : Type} {Msg : Fn → Type} (C : TwColl Par Tw Fn Msg Out)
  (G : Fn → Tw → Prop)

/-- `x` is the cell of an input of a function of `C` at the parameter `P` and a tweak `t` of
`G`. -/
def GCell (x : HashDomain) (P : Par) (t : Tw) : Prop :=
  ∃ l m, G l t ∧ encodeInput (C.layout l P t m) = some x

/-- Two cells are `G`-cells at the same parameter and tweak. -/
def SameCls (x z : HashDomain) : Prop :=
  ∃ P t, GCell C G x P t ∧ GCell C G z P t

/-- `z` is a `G`-cell. -/
def IsG (z : HashDomain) : Prop :=
  ∃ P t, GCell C G z P t

/-- **`G`-separation**: an input of `C` with the bytes of an input at a tweak of `G` has its
parameter and tweak. -/
def GSep : Prop :=
  ∀ l P t m l' P' t' m', G l t → C.layout l' P' t' m' = C.layout l P t m → P' = P ∧ t' = t

variable {C G}

theorem gCell_unique (h : GSep C G) {x : HashDomain} {P P' : Par} {t t' : Tw}
    (h₁ : GCell C G x P t) (h₂ : GCell C G x P' t') : P' = P ∧ t' = t := by
  obtain ⟨l, m, hG, he⟩ := h₁
  obtain ⟨l', m', -, he'⟩ := h₂
  exact h l P t m l' P' t' m' hG (encodeInput_injective he' he)

theorem SameCls.symm {x z : HashDomain} (h : SameCls C G x z) : SameCls C G z x := by
  obtain ⟨P, t, h₁, h₂⟩ := h
  exact ⟨P, t, h₂, h₁⟩

theorem SameCls.trans (hs : GSep C G) {x z w : HashDomain} (h : SameCls C G x z)
    (h' : SameCls C G z w) : SameCls C G x w := by
  obtain ⟨P, t, h₁, h₂⟩ := h
  obtain ⟨P', t', h₃, h₄⟩ := h'
  obtain ⟨rfl, rfl⟩ := gCell_unique hs h₂ h₃
  exact ⟨_, _, h₁, h₄⟩

theorem SameCls.isG_left {x z : HashDomain} (h : SameCls C G x z) : IsG C G x := by
  obtain ⟨P, t, h₁, -⟩ := h
  exact ⟨P, t, h₁⟩

theorem SameCls.isG_right {x z : HashDomain} (h : SameCls C G x z) : IsG C G z := by
  obtain ⟨P, t, -, h₂⟩ := h
  exact ⟨P, t, h₂⟩

end cells

/-! ## The memory and the events -/

/-- **The memory of the read program**: the log of every read's outcome, the cells read, the
records and the judge's read. -/
abbrev TMem :=
  (HashDomain → Option HashOutput) × (HashDomain → Bool) × (HashDomain → Option HashOutput) ×
    Option (HashDomain × HashOutput)

/-- The memory with the (unused) label of the record ports. -/
abbrev Mem :=
  Finset Empty × TMem

/-- Decidable equality of the logs. -/
instance (priority := high) instDecidableEqLog : DecidableEq (HashDomain → Option HashOutput) :=
  Fintype.decidablePiFintype

/-- Decidable equality of the cells read. -/
instance (priority := high) instDecidableEqSeen : DecidableEq (HashDomain → Bool) :=
  Fintype.decidablePiFintype

/-- Decidable equality of the memory without the label. -/
instance (priority := high) instDecidableEqTMem : DecidableEq TMem :=
  @instDecidableEqProd _ _ instDecidableEqLog <| @instDecidableEqProd _ _ instDecidableEqSeen <|
    @instDecidableEqProd _ _ instDecidableEqLog inferInstance

/-- The memory without the label is finite. -/
instance (priority := high) instFintypeTMem : Fintype TMem := by
  unfold TMem
  infer_instance

/-- Decidable equality of the memory, as that of the product. -/
instance (priority := high) instDecidableEqMem : DecidableEq Mem :=
  @instDecidableEqProd _ _ inferInstance instDecidableEqTMem

/-- The memory is finite, as the product. -/
instance (priority := high) instFintypeMem : Fintype Mem :=
  @instFintypeProd _ _ inferInstance instFintypeTMem

/-- The log of a memory. -/
def Mem.log (m : Mem) : HashDomain → Option HashOutput :=
  m.2.1

/-- The cells read. -/
def Mem.seen (m : Mem) : HashDomain → Bool :=
  m.2.2.1

/-- The records of a memory. -/
def Mem.recs (m : Mem) : HashDomain → Option HashOutput :=
  m.2.2.2.1

/-- The judge's read of a memory. -/
def Mem.slot (m : Mem) : Option (HashDomain × HashOutput) :=
  m.2.2.2.2

section events

variable {Par Tw Fn Out : Type} {Msg : Fn → Type} (C : TwColl Par Tw Fn Msg Out)
  (G : Fn → Tw → Prop)

/-- **The target of cell `z`**: the values with the truncation of the unique record of its class,
when that record is at another cell. -/
def tgt (_W : Hw HashOutput HashDomain) (m : Mem) (z : HashDomain) : Set HashOutput :=
  {y | ∃ x v, m.recs x = some v ∧ x ≠ z ∧ SameCls C G x z ∧
    (∀ x', (m.recs x').isSome → SameCls C G x' z → x' = x) ∧ C.trunc y = C.trunc v}

/-- **The judge's read is in its target.** -/
def JBad : Set (RomReg HashDomain HashOutput Mem) :=
  {s | ∃ z y, s.2.2.slot = some (z, y) ∧ y ∈ tgt C G s.2.1 s.2.2 z}

/-- **The event while the adversary runs.** -/
def BadR : Set (RomReg HashDomain HashOutput Mem) :=
  CellTargetBad (tgt C G) ∪ JBad C G

/-- Membership in `BadR`, decided classically. -/
noncomputable instance instDecidablePredBadR : DecidablePred (· ∈ BadR C G) :=
  fun _ ↦ Classical.propDecidable _

variable {C G}

open scoped Classical in
/-- **A target has at most `F` values**, `F` a bound on the fibers of the truncation. -/
theorem card_tgt_le {F : ℕ} (hF : ∀ o, (Finset.univ.filter fun y ↦ C.trunc y = o).card ≤ F)
    (W : Hw HashOutput HashDomain) (m : Mem) (z : HashDomain) :
    (Finset.univ.filter fun y ↦ y ∈ tgt C G W m z).card ≤ F := by
  by_cases h : ∃ x v, m.recs x = some v ∧ x ≠ z ∧ SameCls C G x z ∧
      (∀ x', (m.recs x').isSome → SameCls C G x' z → x' = x)
  · obtain ⟨x₀, v₀, hv₀, -, -, hu₀⟩ := h
    refine (Finset.card_le_card fun y hy ↦ ?_).trans (hF (C.trunc v₀))
    obtain ⟨x, v, hv, -, hxz, -, hy⟩ := (Finset.mem_filter.1 hy).2
    have hx : x = x₀ := hu₀ x (by rw [hv]; rfl) hxz
    subst hx
    rw [hv₀] at hv
    cases hv
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩
  · rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun y _ hy ↦ ?_)]
    · exact Nat.zero_le F
    obtain ⟨x, v, hv, hne, hxz, hu, -⟩ := hy
    exact h ⟨x, v, hv, hne, hxz, hu⟩


/-- `JBad` reads only the memory. -/
theorem mem_jBad_iff {s : RomReg HashDomain HashOutput Mem} :
    s ∈ JBad C G ↔ ∃ z y, s.2.2.slot = some (z, y) ∧ y ∈ tgt C G s.2.1 s.2.2 z :=
  Iff.rfl

/-- **Every slice of the event is upward closed.** -/
theorem upClosed_slice_badR (W : Hw HashOutput HashDomain) (m : Mem) :
    UpClosed (slice (BadR C G) W m) where
  h Db hDb z u hz := by
    rcases hDb with h | h
    · exact Or.inl ((upClosed_slice_cellTargetBad (tgt := tgt C G) W m).h Db h z u hz)
    · exact Or.inr h
  k Db hDb _ _ _ := hDb
  k' Db hDb _ _ _ := hDb

/-- **The start is outside the event** when the memory has no record and no judge's read. -/
theorem start_not_mem_badR (m₀ : Mem) (hr : ∀ x, m₀.recs x = none) :
    (((Database.empty, Database.empty, Database.empty), hwEmpty HashOutput HashDomain, m₀) :
      RomReg HashDomain HashOutput Mem) ∉ BadR C G := by
  rintro (⟨x, y, -, hy⟩ | ⟨z, y, -, hy⟩) <;>
  · obtain ⟨x', v, hv, -⟩ := hy
    rw [hr x'] at hv
    cases hv

open scoped Classical in
/-- **The fresh bound of every slice**: `F / |Y|`, `F` a bound on the fibers of the truncation. -/
theorem freshBound_slice_badR {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ C.trunc y = o).card ≤ F)
    (W : Hw HashOutput HashDomain) (m : Mem) (t : ℕ) :
    FreshBound (slice (BadR C G) W m) t ((F : ℝ≥0∞) / Fintype.card HashOutput) where
  h Db hDb h₁ h₂ h₃ z hz := by
    have hc := (freshBound_slice_cellTargetBad (tgt := tgt C G) W m (ε := (F : ℝ≥0∞) /
      Fintype.card HashOutput) (fun x _ ↦ ENNReal.div_le_div_right (Nat.cast_le.2
        (card_tgt_le hF W m x)) _) t).h Db (fun h ↦ hDb (Or.inl h)) h₁ h₂ h₃ z hz
    refine le_trans (ENNReal.div_le_div_right (Nat.cast_le.2 (Finset.card_le_card
      fun u hu ↦ ?_)) _) hc
    rcases (Finset.mem_filter.1 hu).2 with h | h
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
    · exact absurd (Or.inr h) hDb
  k Db hDb _ _ _ x _ := by
    rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun _ _ hu ↦ ?_)]
    · rw [Nat.cast_zero, ENNReal.zero_div]
      exact zero_le
    rcases hu with h | h
    · exact hDb (Or.inl h)
    · exact hDb (Or.inr h)
  k' Db hDb _ _ _ x _ := by
    rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun _ _ hu ↦ ?_)]
    · rw [Nat.cast_zero, ENNReal.zero_div]
      exact zero_le
    rcases hu with h | h
    · exact hDb (Or.inl h)
    · exact hDb (Or.inr h)

end events

/-! ## Classes without a record -/

section recordless

variable {Par Tw Fn Out : Type} {Msg : Fn → Type} (C : TwColl Par Tw Fn Msg Out)
  (G : Fn → Tw → Prop)

/-- **No cell of the class of `z` is recorded** in the memory `m`. -/
def Recordless (m : Mem) (z : HashDomain) : Prop :=
  ∀ x, SameCls C G x z → m.recs x = none

/-- **A read creating the record of its class**, at the state `s`: `z` is a `G`-cell of a class
without a record, the read records `z` with its outcome (`0` if none) and keeps the empty slot,
and no cell of the class is in the database or hardwired. -/
def RecCase (z : HashDomain) (u : Mem → Option HashOutput → Mem)
    (s : RomReg HashDomain HashOutput Mem) : Prop :=
  IsG C G z ∧ Recordless C G s.2.2 z ∧ s.2.2.slot = none ∧
    (∀ o, (u s.2.2 o).recs = Function.update s.2.2.recs z (some (o.getD 0)) ∧
      (u s.2.2 o).slot = s.2.2.slot) ∧
    ∀ x, SameCls C G x z → unionH s x = none

variable {C G}

theorem IsG.sameCls_self {z : HashDomain} (h : IsG C G z) : SameCls C G z z := by
  obtain ⟨P, t, h⟩ := h
  exact ⟨P, t, h, h⟩

theorem recordless_of_sameCls (hs : GSep C G) {m : Mem} {x z : HashDomain}
    (h : Recordless C G m z) (hxz : SameCls C G x z) : Recordless C G m x :=
  fun x' hx' ↦ h x' (hx'.trans hs hxz)

/-- The target of `x` reads only the records of its class. -/
theorem tgt_congr_cls {m m' : Mem} {x : HashDomain}
    (h : ∀ x₀, SameCls C G x₀ x → m'.recs x₀ = m.recs x₀) (W W' : Hw HashOutput HashDomain) :
    tgt C G W' m' x = tgt C G W m x := by
  ext y
  constructor
  · rintro ⟨x₀, v, hv, hne, hc, hu, ht⟩
    refine ⟨x₀, v, by rw [← h x₀ hc]; exact hv, hne, hc, fun x' hx' hc' ↦ hu x' ?_ hc', ht⟩
    rw [h x' hc']
    exact hx'
  · rintro ⟨x₀, v, hv, hne, hc, hu, ht⟩
    refine ⟨x₀, v, by rw [h x₀ hc]; exact hv, hne, hc, fun x' hx' hc' ↦ hu x' ?_ hc', ht⟩
    rw [← h x' hc']
    exact hx'

/-- A class without a record gives no target. -/
theorem tgt_eq_empty_of_recordless {m : Mem} {z : HashDomain} (h : Recordless C G m z)
    (W : Hw HashOutput HashDomain) : tgt C G W m z = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ ⟨x₀, _, hv, _, hc, _⟩ ↦ by
    rw [h x₀ hc] at hv
    cases hv

/-- **Recording a class without a record keeps the event** when no other cell of the class is
in the database or hardwired and the slot stays empty. -/
theorem badR_record_move {s : RomReg HashDomain HashOutput Mem} {z : HashDomain} {w : HashOutput}
    {m' : Mem} (hrl : Recordless C G s.2.2 z)
    (hrec : m'.recs = Function.update s.2.2.recs z (some w)) (hslot : m'.slot = none)
    (hsl : s.2.2.slot = none) (hcls : ∀ x, x ≠ z → SameCls C G x z → unionH s x = none) :
    ((s.1, s.2.1, m') : RomReg HashDomain HashOutput Mem) ∈ BadR C G ↔ s ∈ BadR C G := by
  have key : ∀ (m : Mem) x y, (m = m' ∨ m = s.2.2) → unionH s x = some y →
      y ∈ tgt C G s.2.1 m x → ¬ SameCls C G x z := by
    intro m x y hm hxy hy hxz
    by_cases hx : x = z
    · subst hx
      rcases hm with rfl | rfl
      · obtain ⟨x₀, v, hv, hne, hc, -⟩ := hy
        rw [hrec, Function.update_of_ne hne, hrl x₀ hc] at hv
        cases hv
      · rw [tgt_eq_empty_of_recordless hrl] at hy
        exact hy
    · rw [hcls x hx hxz] at hxy
      cases hxy
  have ht : ∀ x, ¬ SameCls C G x z → tgt C G s.2.1 m' x = tgt C G s.2.1 s.2.2 x :=
    fun x hx ↦ tgt_congr_cls (fun x₀ hx₀ ↦ by
      rw [hrec, Function.update_of_ne]
      rintro rfl
      exact hx hx₀.symm) _ _
  constructor
  · rintro (⟨x, y, hxy, hy⟩ | ⟨z', y, hs', -⟩)
    · exact Or.inl ⟨x, y, hxy, by rw [← ht x (key m' x y (Or.inl rfl) hxy hy)]; exact hy⟩
    · change m'.slot = some (z', y) at hs'
      rw [hslot] at hs'
      cases hs'
  · rintro (⟨x, y, hxy, hy⟩ | ⟨z', y, hs', -⟩)
    · exact Or.inl ⟨x, y, hxy, by rw [ht x (key s.2.2 x y (Or.inr rfl) hxy hy)]; exact hy⟩
    · rw [hsl] at hs'
      cases hs'

end recordless

/-! ## Reads that keep the records -/

section reads

variable {Par Tw Fn Out : Type} {Msg : Fn → Type} {C : TwColl Par Tw Fn Msg Out}
  {G : Fn → Tw → Prop}

/-- **A read policy at cell `z` that keeps the records of the memory `m`** and writes the
judge's read at most once: the slot is kept, or written from empty with the outcome at `z`. -/
def KeepsRecsAt (z : HashDomain) (u : Mem → Option HashOutput → Mem) (m : Mem) : Prop :=
  ∀ o, (u m o).recs = m.recs ∧
    ((u m o).slot = m.slot ∨ (m.slot = none ∧ (u m o).slot = o.map fun y ↦ (z, y)))

/-- **A read policy at cell `z` that keeps the records** of every memory. -/
def KeepsRecs (z : HashDomain) (u : Mem → Option HashOutput → Mem) : Prop :=
  ∀ m, KeepsRecsAt z u m

theorem tgt_congr {m m' : Mem} (h : m'.recs = m.recs) (W W' : Hw HashOutput HashDomain) :
    tgt C G W' m' = tgt C G W m := by
  funext z
  simp only [tgt, h]

/-- The membership in `JBad` after a read keeping the records, from outside, needs the outcome in
the target of the read cell. -/
theorem jBad_of_keepsRecs {z : HashDomain} {u : Mem → Option HashOutput → Mem}
    {s : RomReg HashDomain HashOutput Mem} (hu : KeepsRecsAt z u s.2.2) {o : Option HashOutput}
    (s' : RomReg HashDomain HashOutput Mem) (hm : s'.2.2 = u s.2.2 o)
    (h : s' ∈ JBad C G) : s ∈ JBad C G ∨ ∃ y, o = some y ∧ y ∈ tgt C G s.2.1 s.2.2 z := by
  obtain ⟨z', y, hs, hy⟩ := h
  rw [hm, tgt_congr (hu o).1 s.2.1 s'.2.1] at hy
  rw [hm] at hs
  rcases (hu o).2 with h | ⟨-, h⟩
  · exact Or.inl ⟨z', y, h ▸ hs, hy⟩
  · rw [h] at hs
    rcases o with _ | y'
    · cases hs
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact Or.inr ⟨_, rfl, hy⟩

/-- **A read of a cell outside every class is invisible** to the event, if it keeps the records. -/
theorem readInvisible_badR {z : HashDomain} (hz : ¬ IsG C G z) {u : Mem → Option HashOutput → Mem}
    (hu : KeepsRecs z u) : ReadInvisible (BadR C G) z u := by
  have hz' : ∀ W m, tgt C G W m z = ∅ := fun W m ↦ Set.eq_empty_iff_forall_notMem.2
    fun y ⟨x, v, _, _, hxz, _, _⟩ ↦ hz hxz.isG_right
  have hc := readInvisible_cellTargetBad (tgt := tgt C G) (z := z) (u := u) hz'
    fun W m o ↦ tgt_congr (hu m o).1 W W
  intro s s' o h₁ h₂ h₃ h₄
  have hJ : s' ∈ JBad C G ↔ s ∈ JBad C G := by
    constructor
    · intro h
      rcases jBad_of_keepsRecs (hu s.2.2) s' h₄ h with h | ⟨y, -, hy⟩
      · exact h
      · rw [hz'] at hy
        exact absurd hy (Set.notMem_empty y)
    · rintro ⟨z', y, hs, hy⟩
      refine ⟨z', y, ?_, ?_⟩
      · rw [h₄]
        rcases (hu s.2.2 o).2 with h | ⟨h, -⟩
        · exact h.trans hs
        · rw [h] at hs
          cases hs
      · rw [h₄, h₃, tgt_congr (hu s.2.2 o).1 s.2.1 s.2.1]
        exact hy
  exact or_congr (hc s s' o h₁ h₂ h₃ h₄) hJ

/-- **The memory move of a read keeping the records**: it keeps the event, and enters it only with
an outcome in the target of the read cell. -/
theorem badR_memMove {z : HashDomain} {u : Mem → Option HashOutput → Mem}
    (s : RomReg HashDomain HashOutput Mem) (hu : KeepsRecsAt z u s.2.2) (o : Option HashOutput) :
    ((s.1, s.2.1, u s.2.2 o) ∈ BadR C G → s ∈ BadR C G ∨
      ∃ y, o = some y ∧ y ∈ tgt C G s.2.1 s.2.2 z) ∧
    (s ∈ BadR C G → (s.1, s.2.1, u s.2.2 o) ∈ BadR C G) := by
  have ht : tgt C G s.2.1 (u s.2.2 o) = tgt C G s.2.1 s.2.2 :=
    tgt_congr (hu o).1 s.2.1 s.2.1
  constructor
  · rintro (⟨x, y, hxy, hy⟩ | h)
    · exact Or.inl (Or.inl ⟨x, y, hxy, by rw [← ht]; exact hy⟩)
    · rcases jBad_of_keepsRecs hu (s.1, s.2.1, u s.2.2 o) rfl h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  · rintro (⟨x, y, hxy, hy⟩ | ⟨z', y, hs, hy⟩)
    · exact Or.inl ⟨x, y, hxy, by change y ∈ tgt C G s.2.1 (u s.2.2 o) x; rw [ht]; exact hy⟩
    · refine Or.inr ⟨z', y, ?_, ?_⟩
      · rcases (hu o).2 with h | ⟨h, -⟩
        · exact h.trans hs
        · rw [h] at hs
          cases hs
      · change y ∈ tgt C G s.2.1 (u s.2.2 o) z'
        rw [ht]
        exact hy

/-- Recording a value outside the target of an empty, unhardwired cell keeps the event. -/
theorem badR_record_iff {s : RomReg HashDomain HashOutput Mem} {z : HashDomain} {v : HashOutput}
    (hw : s.2.1.1 z = none) (hv : v ∉ tgt C G s.2.1 s.2.2 z) (a : Option HashOutput)
    (ha : s.1.1 z = a) (hav : a = none ∨ a = some v) :
    (((Function.update s.1.1 z (some v), s.1.2), s.2) : RomReg HashDomain HashOutput Mem) ∈
      BadR C G ↔ s ∈ BadR C G := by
  have hJ : ((((Function.update s.1.1 z (some v), s.1.2), s.2) :
      RomReg HashDomain HashOutput Mem) ∈ JBad C G ↔ s ∈ JBad C G) := Iff.rfl
  refine or_congr ?_ hJ
  constructor
  · rintro ⟨x, y, hxy, hy⟩
    by_cases hx : x = z
    · subst hx
      change (s.2.1.1 x).or (Function.update s.1.1 x (some v) x) = some y at hxy
      rw [hw, Function.update_self] at hxy
      cases hxy
      exact absurd hy hv
    · refine ⟨x, y, ?_, hy⟩
      change (s.2.1.1 x).or (Function.update s.1.1 z (some v) x) = some y at hxy
      rwa [Function.update_of_ne hx] at hxy
  · rintro ⟨x, y, hxy, hy⟩
    refine ⟨x, y, ?_, hy⟩
    change (s.2.1.1 x).or (Function.update s.1.1 z (some v) x) = some y
    by_cases hx : x = z
    · subst hx
      change (s.2.1.1 x).or (s.1.1 x) = some y at hxy
      rw [hw, ha] at hxy
      rcases hav with rfl | rfl
      · cases hxy
      · rw [hw, Function.update_self]
        exact hxy
    · rwa [Function.update_of_ne hx]

/-- A state whose read cell holds a value in its target is in the event. -/
theorem mem_badR_of_cell {s : RomReg HashDomain HashOutput Mem} {z : HashDomain} {y : HashOutput}
    (hz : unionH s z = some y) (hy : y ∈ tgt C G s.2.1 s.2.2 z) : s ∈ BadR C G :=
  Or.inl ⟨z, y, hz, hy⟩

open scoped Classical in
/-- **A read of a cell costs like a sponge call** (`gradeEta`, `F` a bound on the fibers of the
truncation), on a state with no decompressed `⊥` at the cell, if at every state of its support it
keeps the records or creates the record of a class with no cell in the database. -/
theorem tsum_potential_read_badR {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ C.trunc y = o).card ≤ F) {z : HashDomain}
    {u : Mem → Option HashOutput → Mem}
    {σ : Matrix (Unit × RomReg HashDomain HashOutput Mem) (Unit × RomReg HashDomain HashOutput Mem)
      ℂ} (hσ : σ.PosSemidef) (hnb : ReadNoBot (.readH z u) σ)
    (hu : ∀ q, σ q q ≠ 0 → KeepsRecsAt z u q.2.2.2 ∨ RecCase C G z u q.2) :
    ∑' r, QuantumRuntime.potential (hwProjector (BadR C G))
        (MatrixMap.conj (hwReadKraus (.readH z u) r) σ) ≤
      (QuantumRuntime.potential (hwProjector (BadR C G)) σ ^ (2⁻¹ : ℝ) +
        ENNReal.ofReal (gradeEta HashOutput F * σ.trace.re) ^ (2⁻¹ : ℝ)) ^ 2 := by
  refine tsum_potential_readH_le_sqrt (BadR C G) z u F
    (Quantum.Xmss.Assembly.upCell_of_upClosed _ (fun W m ↦ upClosed_slice_badR W m) _) hσ hnb
    (fun q hq hw hd ↦ ?_) (fun q hq hw ↦ ?_) (fun q hq hw ↦ ?_) (fun q hq hw hd hm ↦ ?_) <;>
    rcases hu q hq with hk | ⟨hzG, hrl, hsl, hu', hcls⟩
  · have hmv := fun (s : RomReg HashDomain HashOutput Mem) (hs : s.2.2 = q.2.2.2) o ↦
      badR_memMove (C := C) (G := G) s (hs ▸ hk) o
    refine ⟨?_, ?_⟩
    · refine (Finset.card_le_card fun v hv ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩).trans
        (card_tgt_le (G := G) hF q.2.2.1 q.2.2.2 z)
      by_contra hvt
      rcases (Finset.mem_filter.1 hv).2 with h | ⟨a, h⟩
      · exact h (badR_record_iff hw hvt none hd (Or.inl rfl))
      · refine h ⟨fun h2 ↦ ?_,
          (hmv ((Function.update q.2.1.1 z a, q.2.1.2), q.2.2) rfl (some v)).2⟩
        rcases (hmv ((Function.update q.2.1.1 z a, q.2.1.2), q.2.2.1, q.2.2.2) rfl
          (some v)).1 h2 with h3 | ⟨y, hy, hyt⟩
        · exact h3
        · cases hy
          exact absurd hyt hvt
    · refine (Finset.card_le_card fun v hv ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩).trans
        (card_tgt_le (G := G) hF q.2.2.1 q.2.2.2 z)
      by_contra hvt
      have h1 := badR_record_iff (C := C) (G := G) hw hvt none hd (Or.inl rfl)
      have h2 : ((((Function.update q.2.1.1 z (some v), q.2.1.2), q.2.2.1, u q.2.2.2 (some v))) :
          RomReg HashDomain HashOutput Mem) ∈ BadR C G ↔
          (((Function.update q.2.1.1 z (some v), q.2.1.2), q.2.2) :
            RomReg HashDomain HashOutput Mem) ∈ BadR C G := by
        refine ⟨fun h ↦ ?_,
          (hmv ((Function.update q.2.1.1 z (some v), q.2.1.2), q.2.2) rfl (some v)).2⟩
        rcases (hmv ((Function.update q.2.1.1 z (some v), q.2.1.2), q.2.2) rfl (some v)).1 h with
          h3 | ⟨y, hy, hyt⟩
        · exact h3
        · cases hy
          exact absurd hyt hvt
      exact (Finset.mem_filter.1 hv).2 (h2.trans h1)
  · have hrm : ∀ (a : Option HashOutput) (v : HashOutput),
        (((Function.update q.2.1.1 z a, q.2.1.2), q.2.2.1, u q.2.2.2 (some v)) :
          RomReg HashDomain HashOutput Mem) ∈ BadR C G ↔
        (((Function.update q.2.1.1 z a, q.2.1.2), q.2.2) :
          RomReg HashDomain HashOutput Mem) ∈ BadR C G := fun a v ↦
      badR_record_move (s := ((Function.update q.2.1.1 z a, q.2.1.2), q.2.2)) hrl
        (hu' (some v)).1 ((hu' (some v)).2.trans hsl) hsl fun x hx hxz ↦ by
          change (q.2.2.1.1 x).or (Function.update q.2.1.1 z a x) = none
          rw [Function.update_of_ne hx]
          exact hcls x hxz
    have hrec : ∀ v, (((Function.update q.2.1.1 z (some v), q.2.1.2), q.2.2) :
        RomReg HashDomain HashOutput Mem) ∈ BadR C G ↔ q.2 ∈ BadR C G := fun v ↦
      badR_record_iff hw (by rw [tgt_eq_empty_of_recordless hrl]; exact fun h ↦ h) none hd
        (Or.inl rfl)
    refine ⟨?_, ?_⟩
    · rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun v _ hv ↦ ?_)]
      · exact Nat.zero_le F
      rcases hv with h | ⟨a, h⟩
      · exact h (hrec v)
      · exact h (hrm a v)
    · unfold rdCnt
      rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun v _ hv ↦
        hv ((hrm (some v) v).trans (hrec v)))]
      exact Nat.zero_le F
  · have hmv := fun (s : RomReg HashDomain HashOutput Mem) (hs : s.2.2 = q.2.2.2) o ↦
      badR_memMove (C := C) (G := G) s (hs ▸ hk) o
    rintro ⟨hq, h⟩
    rcases (hmv q.2 rfl (q.2.1.1 z)).1 h with h' | ⟨y, hy, hyt⟩
    · exact hq h'
    · refine hq (mem_badR_of_cell (z := z) ?_ hyt)
      change (q.2.2.1.1 z).or (q.2.1.1 z) = some y
      rw [hw, hy]
      rfl
  · rintro ⟨hq, h⟩
    exact hq ((badR_record_move (s := q.2) hrl (hu' _).1 ((hu' _).2.trans hsl) hsl
      fun x _ hxz ↦ hcls x hxz).1 h)
  · have hmv := fun (s : RomReg HashDomain HashOutput Mem) (hs : s.2.2 = q.2.2.2) o ↦
      badR_memMove (C := C) (G := G) s (hs ▸ hk) o
    rintro ⟨hq, h⟩
    rcases (hmv q.2 rfl (q.2.2.1.1 z)).1 h with h' | ⟨y, hy, hyt⟩
    · exact hq h'
    · refine hq (mem_badR_of_cell (z := z) ?_ hyt)
      change (q.2.2.1.1 z).or (q.2.1.1 z) = some y
      rw [hy]
      rfl
  · have h0 := hcls z hzG.sameCls_self
    rcases h1 : q.2.2.1.1 z with _ | y
    · exact absurd h1 hw
    · change (q.2.2.1.1 z).or (q.2.1.1 z) = none at h0
      rw [h1] at h0
      cases h0
  · have hmv := fun (s : RomReg HashDomain HashOutput Mem) (hs : s.2.2 = q.2.2.2) o ↦
      badR_memMove (C := C) (G := G) s (hs ▸ hk) o
    by_contra hq
    obtain ⟨a, h⟩ := hm
    refine h ⟨fun h2 ↦ ?_,
      (hmv ((Function.update q.2.1.1 z a, q.2.1.2), q.2.2) rfl (q.2.1.1 z)).2⟩
    rcases (hmv ((Function.update q.2.1.1 z a, q.2.1.2), q.2.2.1, q.2.2.2) rfl
      (q.2.1.1 z)).1 h2 with h3 | ⟨y, hy, hyt⟩
    · exact h3
    · refine absurd (mem_badR_of_cell (s := q.2) (z := z) ?_ hyt) hq
      change (q.2.2.1.1 z).or (q.2.1.1 z) = some y
      rw [hw, hy]
      rfl
  · have h0 := hcls z hzG.sameCls_self
    change (q.2.2.1.1 z).or (q.2.1.1 z) = none at h0
    rw [hw] at h0
    exact absurd h0 hd

end reads

/-! ## Sponge calls -/

section sponge

variable {Par Tw Fn Out : Type} {Msg : Fn → Type} {C : TwColl Par Tw Fn Msg Out}
  {G : Fn → Tw → Prop}

/-- Every database triple has grade at most the sum of the domain sizes. -/
theorem dbGrade_le_card (D : DbReg HashOutput HashDomain) :
    dbGrade D ≤ Fintype.card HashDomain + Fintype.card HashOutput := by
  have h₁ : D.1.size ≤ Fintype.card HashDomain := Finset.card_le_univ _
  have h₂ : D.2.1.size ≤ Fintype.card HashOutput := Finset.card_le_univ _
  have h₃ : D.2.2.size ≤ Fintype.card HashOutput := Finset.card_le_univ _
  unfold dbGrade
  omega

/-- `6 F / N ≤ gradeEta F`. -/
theorem six_mul_le_gradeEta (F : ℕ) :
    6 * ((F : ℝ≥0∞) / Fintype.card HashOutput) ≤ ENNReal.ofReal (gradeEta HashOutput F) := by
  have hN : (0 : ℝ) < Fintype.card HashOutput := Nat.cast_pos.mpr Fintype.card_pos
  have ha : 0 ≤ (F : ℝ) / Fintype.card HashOutput := div_nonneg (Nat.cast_nonneg _) hN.le
  have hab : √((F : ℝ) / Fintype.card HashOutput) ≤
      √(((F : ℝ) + 2) / Fintype.card HashOutput) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hN.le)
  have hreal : 6 * ((F : ℝ) / Fintype.card HashOutput) ≤ gradeEta HashOutput F := by
    unfold gradeEta
    have h0 := Real.sq_sqrt ha
    nlinarith [Real.sqrt_nonneg ((F : ℝ) / Fintype.card HashOutput)]
  rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_natCast F, ← ENNReal.ofReal_natCast
    (Fintype.card HashOutput), ← ENNReal.ofReal_inv_of_pos hN, ← ENNReal.ofReal_mul
    (inv_nonneg.mpr hN.le), ← ENNReal.ofReal_ofNat 6, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [inv_mul_eq_div]
  exact hreal

open scoped Classical in
/-- **A sponge call costs `√(gradeEta F)`** for the event `BadR` (fresh bound `F / N`). -/
theorem potential_sponge_badR_le {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ C.trunc y = o).card ≤ F) (m₀ : Mem) (i : SpongePort)
    {σ : Matrix (spongeIn HashOutput HashDomain i × RomReg HashDomain HashOutput Mem)
      (spongeIn HashOutput HashDomain i × RomReg HashDomain HashOutput Mem) ℂ}
    (hσ : σ.PosSemidef) :
    QuantumRuntime.potential (hwProjector (BadR C G))
        (MatrixMap.conj ((spongeHardwired HashOutput HashDomain (hwEmpty HashOutput HashDomain)
          m₀).U i) σ) ^ (2⁻¹ : ℝ) ≤
      QuantumRuntime.potential (hwProjector (BadR C G)) σ ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal (gradeEta HashOutput F) * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ) := by
  have hεtop : (F : ℝ≥0∞) / Fintype.card HashOutput ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top F)
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  refine (rpow_inv_two_potential_spongeHardwired_le (BadR C G)
    (fun W m ↦ upClosed_slice_badR W m) hεtop (fun W m ↦ freshBound_slice_badR hF W m _)
    (hwEmpty HashOutput HashDomain) m₀ i hσ
    (N := Fintype.card HashDomain + Fintype.card HashOutput)
    (fun _ _ _ ↦ ⟨dbGrade_le_card _, dbGrade_le_card _⟩)).trans
    (add_le_add le_rfl (ENNReal.rpow_le_rpow ?_ (by norm_num)))
  exact mul_le_mul_of_nonneg_right (six_mul_le_gradeEta F) zero_le

end sponge

/-! ## The read policies -/

section policy

variable {Par Tw Fn Out : Type} {Msg : Fn → Type} (C : TwColl Par Tw Fn Msg Out)
  (G : Fn → Tw → Prop)

open scoped Classical in
/-- **The challenger's answers**: log the outcome; a `G`-cell of a class without a record
becomes its record, with the outcome (`0` if none). -/
noncomputable def uAns (z : HashDomain) (m : Mem) (o : Option HashOutput) : Mem :=
  (m.1, Function.update m.log z o, m.seen,
    if IsG C G z ∧ Recordless C G m z then Function.update m.recs z (some (o.getD 0))
    else m.recs, m.slot)

/-- **The reduction's and the setup's reads**: log the outcome and mark the cell read. -/
def uRed (z : HashDomain) (m : Mem) (o : Option HashOutput) : Mem :=
  (m.1, Function.update m.log z o, Function.update m.seen z true, m.recs, m.slot)

/-- **The decision's reads**: log the outcome, mark the cell read, and fill an empty slot with
the cell and the outcome. -/
def uJudge (z : HashDomain) (m : Mem) (o : Option HashOutput) : Mem :=
  (m.1, Function.update m.log z o, Function.update m.seen z true, m.recs,
    m.slot.or (o.map fun y ↦ (z, y)))

/-- **The policy of each caller.** -/
noncomputable def upd : Caller → HashDomain → Mem → Option HashOutput → Mem
  | .setup => uRed
  | .answer => uAns C G
  | .judge => uJudge
  | .red => uRed

/-- The log of a memory, read by the moded runs. -/
def rl : Mem → HashDomain → Option HashOutput :=
  Mem.log

/-- **A read policy of the phase before the adversary**: the answers', or one keeping the
records. -/
def PolicyOK (z : HashDomain) (u : Mem → Option HashOutput → Mem) : Prop :=
  u = uAns C G z ∨ KeepsRecs z u

/-- **The register before the adversary**: no hardwired cell, an empty slot, and no cell of a
class without a record in the database. -/
def PhaseA (s : RomReg HashDomain HashOutput Mem) : Prop :=
  s.2.1 = hwEmpty HashOutput HashDomain ∧ s.2.2.slot = none ∧
    ∀ x, IsG C G x → Recordless C G s.2.2 x → s.1.1 x = none

variable {C G}

open scoped Classical in
theorem uAns_recs (z : HashDomain) (m : Mem) (o : Option HashOutput) :
    (uAns C G z m o).recs = if IsG C G z ∧ Recordless C G m z then
      Function.update m.recs z (some (o.getD 0)) else m.recs :=
  rfl

theorem recordsAt_upd (c : Caller) (z : HashDomain) : RecordsAt rl z (upd C G c z) := by
  intro m o
  cases c <;> rfl

theorem keepsRecs_uRed (z : HashDomain) : KeepsRecs z (uRed z) :=
  fun _ _ ↦ ⟨rfl, Or.inl rfl⟩

theorem keepsRecs_uJudge (z : HashDomain) : KeepsRecs z (uJudge z) := by
  intro m o
  refine ⟨rfl, ?_⟩
  rcases h : m.slot with _ | p
  · refine Or.inr ⟨rfl, ?_⟩
    change m.slot.or _ = _
    rw [h]
    rfl
  · refine Or.inl ?_
    change m.slot.or _ = _
    rw [h]
    rfl

/-- The policies other than the challenger's answers keep the records. -/
theorem keepsRecs_upd {c : Caller} (hc : c ≠ .answer) (z : HashDomain) :
    KeepsRecs z (upd C G c z) := by
  cases c
  · exact keepsRecs_uRed z
  · exact absurd rfl hc
  · exact keepsRecs_uJudge z
  · exact keepsRecs_uRed z

theorem policyOK_upd (c : Caller) (z : HashDomain) : PolicyOK C G z (upd C G c z) := by
  by_cases hc : c = .answer
  · subst hc
    exact Or.inl rfl
  · exact Or.inr (keepsRecs_upd hc z)

/-- **The answers' policy is the answers' only**: the other policies mark the cell read. -/
theorem upd_eq_uAns_iff (c : Caller) (z : HashDomain) :
    upd C G c z = uAns C G z ↔ c = .answer := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  let m₀ : Mem := (∅, fun _ ↦ none, fun _ ↦ false, fun _ ↦ none, none)
  have h' := congrArg (fun m : Mem ↦ m.seen z) (congrFun (congrFun h m₀) none)
  cases c
  · change Function.update (fun _ ↦ false) z true z = false at h'
    simp at h'
  · rfl
  · change Function.update (fun _ ↦ false) z true z = false at h'
    simp at h'
  · change Function.update (fun _ ↦ false) z true z = false at h'
    simp at h'

/-- The answers only add records. -/
theorem recordless_of_uAns {z x : HashDomain} {m : Mem} {o : Option HashOutput}
    (h : Recordless C G (uAns C G z m o) x) : Recordless C G m x := by
  intro x' hx'
  have h' := h x' hx'
  rw [uAns_recs] at h'
  split_ifs at h' with hc
  · by_cases hxz : x' = z
    · subst hxz
      exact hc.2 x' hc.1.sameCls_self
    · rwa [Function.update_of_ne hxz] at h'
  · exact h'

/-- After an answer read of a `G`-cell its class has a record. -/
theorem not_recordless_uAns {z : HashDomain} (hz : IsG C G z) (m : Mem) (o : Option HashOutput) :
    ¬ Recordless C G (uAns C G z m o) z := by
  intro h
  by_cases hc : Recordless C G m z
  · have h' := h z hz.sameCls_self
    rw [uAns_recs, ite_eq_left ⟨hz, hc⟩, Function.update_self] at h'
    cases h'
  · exact hc (recordless_of_uAns h)

/-- **A read of the phase before the adversary keeps the records or creates one.** -/
theorem keepsRecsAt_or_recCase (hs : GSep C G) {z : HashDomain}
    {u : Mem → Option HashOutput → Mem} (hu : PolicyOK C G z u)
    {s : RomReg HashDomain HashOutput Mem} (hA : PhaseA C G s) :
    KeepsRecsAt z u s.2.2 ∨ RecCase C G z u s := by
  rcases hu with rfl | hu
  · by_cases h : IsG C G z ∧ Recordless C G s.2.2 z
    · refine Or.inr ⟨h.1, h.2, hA.2.1, fun o ↦ ⟨by rw [uAns_recs, ite_eq_left h], rfl⟩,
        fun x hxz ↦ ?_⟩
      change (s.2.1.1 x).or (s.1.1 x) = none
      rw [hA.1, hA.2.2 x hxz.isG_left (recordless_of_sameCls hs h.2 hxz)]
      rfl
    · exact Or.inl fun o ↦ ⟨by rw [uAns_recs, ite_eq_right h], Or.inl rfl⟩
  · exact Or.inl (hu s.2.2)

/-- **An answer read keeps the register before the adversary.** -/
theorem phaseA_of_readKrausH {z : HashDomain} (r : Option HashOutput × Mem)
    {s' s : RomReg HashDomain HashOutput Mem} (h : readKrausH z (uAns C G z) r s' s ≠ 0)
    (hA : PhaseA C G s) : PhaseA C G s' := by
  obtain ⟨hc, -, hW⟩ := Quantum.Xmss.Assembly.readKrausH_ne_zero_rest z (uAns C G z) r h
  have hm : s'.2.2 = uAns C G z s.2.2 r.1 := by
    rw [readKrausH, clsKraus_apply] at h
    split_ifs at h with hcond
    · rw [hcond.2, hcond.1]
    · exact absurd rfl h
  refine ⟨hW.trans hA.1, ?_, fun x hx hrl ↦ ?_⟩
  · rw [hm]
    exact hA.2.1
  · rw [hm] at hrl
    by_cases hxz : x = z
    · subst hxz
      exact absurd hrl (not_recordless_uAns hx _ _)
    · rw [hc x hxz]
      exact hA.2.2 x hx (recordless_of_uAns hrl)

end policy

/-! ## The phases of the mixed game -/

section phase

open OracleComp OracleSpec
open Quantum.Xmss.Assembly (ModedP modedP_bind modedP₂_bind modedP_map modedP_act)

/-- One step of a moded command tree: normalize the head, then split the command. -/
local macro "moded_step" : tactic => `(tactic| (
  (conv => arg 5; whnf);
  refine ⟨?_, fun _ ↦ ?_⟩))

/-- **The calls a phase of the mixed game allows** (`some false`: before any hash call of the
adversary and of the reduction; `some true`: after; `none`: dead): the challenger's answers come
before only. -/
def okT : Option Bool → (MixSpec Caller).Port → Prop
  | some true, .call (.answer, _) => False
  | _, _ => True

/-- **The phase after a mixed call**: a hash call, or a hash by a caller other than the
challenger's answers, ends the phase before. -/
def nxT : Option Bool → (p : (MixSpec Caller).Port) → (MixSpec Caller).Result p → Option Bool
  | none, _, _ => none
  | some _, .hash _, _ => some true
  | some b, .call (.answer, _), _ => some b
  | some b, .call (_, .inl _), _ => some b
  | some _, .call (_, .inr _), _ => some true

/-- The world's hash as a cost: a hash one, a coin nothing. -/
def hashW : romWorld.Oracles.Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

variable {Q' : Type} {R' : OracleSpec.{0, 0} Q'}

/-- The challenger's queries as a cost: one each. -/
def chalW {Q' : Type} : romWorld.Oracles.Domain ⊕ Q' → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- A reduction's query at a phase: the challenger's only before. -/
def chalCan {Q' : Type} : romWorld.Oracles.Domain ⊕ Q' → Bool → Prop
  | .inr _, b => b = false
  | .inl _, _ => True

/-- The phase after a reduction's query: its own hash ends the phase before. -/
def chalCost {Q' : Type} : romWorld.Oracles.Domain ⊕ Q' → Bool → Bool
  | .inl (.inr _), _ => true
  | _, b => b

/-- **The challenger's queries come first**: on every path, no challenger query after a hash of
the reduction's own. -/
def ChalFirst {α : Type} (oa : OracleComp (romWorld.Oracles + R') α) : Prop :=
  IsQueryBound oa false chalCan chalCost

theorem modedP_mixImpl_phase (c : Caller) (B : QReg) (t : romWorld.Oracles.Domain)
    (μ : Option Bool) (h : okT μ (.call (c, t))) :
    ModedP okT nxT (fun p μ' ↦ μ' = nxT μ (.call (c, t)) p.2.2) μ (mixImpl c B t) := by
  moded_step
  · exact h
  moded_step
  · trivial
  rfl

/-- The challenger's answers keep the phase before. -/
theorem modedP_toQuantumAt_answer (B : QReg) {α : Type} (oa : OracleComp romWorld.Oracles α) :
    ModedP okT nxT (fun _ μ' ↦ μ' = some false) (some false)
      (oa.toQuantumAt (mixImpl .answer B)) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact (rfl : some false = some false)
  | query_bind t k ih =>
    rw [toQuantumAt_query_bind]
    refine modedP₂_bind (F := fun _ μ' ↦ μ' = some false) (F' := fun _ μ' ↦ μ' = some false) _ _
      (modedP_mono (fun p μ' h ↦ by rw [h]; rfl) _ _
        (modedP_mixImpl_phase .answer B t (some false) trivial)) fun y μ' hμ' ↦ ?_
    subst hμ'
    exact ih y

/-- A setup making no hash keeps the phase before. -/
theorem modedP_toQuantumAt_setup (B : QReg) {α : Type} (oa : OracleComp romWorld.Oracles α)
    (h : Common.QueryCostAtMost oa hashW 0) :
    ModedP okT nxT (fun _ μ' ↦ μ' = some false) (some false)
      (oa.toQuantumAt (mixImpl .setup B)) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact (rfl : some false = some false)
  | query_bind t k ih =>
    rw [Common.isWeightBound_query_bind_iff] at h
    rw [toQuantumAt_query_bind]
    rcases t with n | z
    · refine modedP₂_bind (F := fun _ μ' ↦ μ' = some false) (F' := fun _ μ' ↦ μ' = some false)
        _ _
        (modedP_mono (fun p μ' h ↦ by rw [h]; rfl) _ _
          (modedP_mixImpl_phase .setup B (.inl n) (some false) trivial)) fun y μ' hμ' ↦ ?_
      subst hμ'
      exact ih y (h.2 y)
    · exact absurd h.1 (by simp [hashW])

/-- The decision runs at any phase. -/
theorem modedP_toQuantumAt_other {c : Caller} (hc : c ≠ .answer) (B : QReg) {α : Type}
    (oa : OracleComp romWorld.Oracles α) (μ : Option Bool) :
    ModedP okT nxT (fun _ _ ↦ True) μ (oa.toQuantumAt (mixImpl c B)) := by
  induction oa using OracleComp.inductionOn generalizing μ with
  | pure a => trivial
  | query_bind t k ih =>
    rw [toQuantumAt_query_bind]
    refine modedP₂_bind (F := fun _ _ ↦ True) (F' := fun _ _ ↦ True) _ _
      (modedP_mono (fun _ _ _ ↦ trivial) _ _ (modedP_mixImpl_phase c B t μ ?_))
      fun y μ' _ ↦ ih y μ'
    rcases μ with _ | _ | _ <;> cases c <;> trivial

/-- **The reduction's algorithm against the challenger, by phases**: from a phase allowing its
queries on every path, its tagged program is moded. -/
theorem modedP_redImpl_phase (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
    (B : QReg) {α : Type} (oa : OracleComp (romWorld.Oracles + R') α) (log : QueryLog R')
    (b : Bool) (h : IsQueryBound oa b chalCan chalCost) :
    ModedP okT nxT (fun _ _ ↦ True) (some b) ((simulateQ (redImpl ans B) oa).run log) := by
  induction oa using OracleComp.inductionOn generalizing log b with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBound_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with i | q'
    · change ModedP okT nxT _ (some b) (QuantumComp₂.bind ((mixImpl .red B i).map
          fun a ↦ (a, log)) fun p ↦ (simulateQ (redImpl ans B) (k p.1)).run p.2)
      have hnx : ∀ v, nxT (some b) (.call (.red, i)) v = some (chalCost (Q' := Q') (.inl i) b) := by
        intro v
        rcases i with n | z <;> rfl
      have hok : okT (some b) (.call (.red, i)) := by
        cases b <;> trivial
      refine modedP₂_bind (F := fun (p : romWorld.Oracles.Range i × QueryLog R') μ' ↦
          p.2 = log ∧ μ' = some (chalCost (Q' := Q') (.inl i) b)) (F' := fun _ _ ↦ True) _ _
        (modedP_map (F := fun (p : romWorld.Oracles.Range i × QueryLog R') μ' ↦
          p.2 = log ∧ μ' = some (chalCost (Q' := Q') (.inl i) b)) _
          (modedP_mono (fun p μ' hμ' ↦ ⟨rfl, hμ'.trans (hnx _)⟩) _ _
            (modedP_mixImpl_phase .red B i (some b) hok)))
        fun p μ' hp ↦ ?_
      obtain ⟨y, l⟩ := p
      obtain ⟨hl, rfl⟩ := hp
      change l = log at hl
      subst hl
      exact ih y l _ (h.2 y)
    · have hb : b = false := h.1
      subst hb
      change ModedP okT nxT _ (some false) (QuantumComp₂.bind (((ans q').toQuantumAt
          (mixImpl .answer B)).map fun a ↦ (a, log ++ [⟨q', a⟩])) fun p ↦
            (simulateQ (redImpl ans B) (k p.1)).run p.2)
      refine modedP₂_bind (F := fun _ μ' ↦ μ' = some false) (F' := fun _ _ ↦ True) _ _
        (modedP_map (F := fun _ μ' ↦ μ' = some false) _ (modedP_toQuantumAt_answer B (ans q')))
        fun p μ' hp ↦ ?_
      subst hp
      exact ih p.1 p.2 false (h.2 p.1)

/-- An algorithm with no challenger query allows its queries at every phase. -/
theorem isQueryBound_of_noChal {α : Type} (oa : OracleComp (romWorld.Oracles + R') α)
    (h : Common.QueryCostAtMost oa chalW 0) (b : Bool) : IsQueryBound oa b chalCan chalCost := by
  induction oa using OracleComp.inductionOn generalizing b with
  | pure a => trivial
  | query_bind t k ih =>
    rw [Common.isWeightBound_query_bind_iff] at h
    rw [isQueryBound_query_bind_iff]
    rcases t with i | q'
    · exact ⟨trivial, fun u ↦ ih u (h.2 u) _⟩
    · exact absurd h.1 (by simp [chalW])

/-- **An algorithm with no challenger query is moded from every phase.** -/
theorem modedP_redImpl_noChal (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
    (B : QReg) {α : Type} (oa : OracleComp (romWorld.Oracles + R') α)
    (h : Common.QueryCostAtMost oa chalW 0) (log : QueryLog R') (μ : Option Bool) :
    ModedP okT nxT (fun _ _ ↦ True) μ ((simulateQ (redImpl ans B) oa).run log) := by
  rcases μ with _ | b
  · exact modedP_of_dead none (fun _ ↦ trivial) (fun _ _ ↦ rfl) (fun _ ↦ trivial) _
  · exact modedP_redImpl_phase ans B oa log b (isQueryBound_of_noChal oa h b)

theorem modedP_mixRun_phase {Q : Type} {R : OracleSpec.{0, 0} Q} {St : Type}
    {X Y : QReg → Type} (Tr : MixTrees R St) (leaf : ∀ u, X u → St → Y u)
    (hTr : ∀ s q (E A : QReg) (ℓ : A ≃ (advSpec romWorld.spec R).In (.call q) × E) μ,
      ModedP okT nxT (fun _ _ ↦ True) μ (Tr s q E ℓ))
    {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X A)
    (s : St) (μ : Option Bool) :
    ModedP okT nxT (fun _ _ ↦ True) μ (mixRun Tr leaf x s) := by
  induction x using IFreeM.inductionOn generalizing s μ with
  | pure u y => trivial
  | liftBind A cmd next ih =>
    rcases cmd with o | ⟨p | q, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih b s _⟩
    · exact ⟨by rcases μ with _ | _ | _ <;> trivial, fun b ↦ ih b s _⟩
    · refine modedP_bind (Tr s q E ℓ) _ (hTr s q E A ℓ μ) fun u l μ' _ ↦ ?_
      obtain ⟨rfl, v⟩ := l
      exact ih ⟨v.1⟩ v.2 μ'

theorem modedP_mixTrees_phase {Q : Type} {R : OracleSpec.{0, 0} Q} {St : Type}
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q')) (σ : HHandler romWorld R R' St)
    (hσ : ∀ st q, Common.QueryCostAtMost (σ st q) chalW 0) (s : St × QueryLog R') (q : Q)
    (E A : QReg) (ℓ : A ≃ (advSpec romWorld.spec R).In (.call q) × E) (μ : Option Bool) :
    ModedP okT nxT (fun _ _ ↦ True) μ (mixTrees ans σ s q E ℓ) := by
  refine modedP₂_bind (F := fun _ μ' ↦ μ' = μ) (F' := fun _ _ ↦ True) _ _
    (modedP_act (F := fun _ μ' ↦ μ' = μ) _ μ fun _ ↦ rfl) fun _ μ' hμ' ↦ ?_
  subst hμ'
  exact modedP_map (F := fun _ _ ↦ True) _
    (modedP_redImpl_noChal ans _ (σ s.1 q) (hσ s.1 q) s.2 _)

/-- **The game of a straight-line reduction by phases**: a setup with no hash, a reduction's
setup whose challenger queries come first (`ChalFirst`), and handler and output with no
challenger query make a moded mixed game: no challenger's answer after a hash call. -/
theorem modedP_mixGame_phase {Q : Type} {R : OracleSpec.{0, 0} Q} {St Pub Out : Type}
    (E : Props.Experiment romWorld R' Pub Out) {S0 F : Type}
    (pre : Pub → OracleComp (romWorld.Oracles + R') S0)
    (adv : Pub → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : Pub → S0 → St) (σ : Pub → HHandler romWorld R R' St)
    (post : Pub → S0 → F → St → OracleComp (romWorld.Oracles + R') Out)
    (hsetup : Common.QueryCostAtMost E.setup hashW 0) (hpre : ∀ p, ChalFirst (pre p))
    (hσ : ∀ p st q, Common.QueryCostAtMost (σ p st q) chalW 0)
    (hpost : ∀ p a f st, Common.QueryCostAtMost (post p a f st) chalW 0) :
    ModedP okT nxT (fun _ _ ↦ True) (some false) (mixGame E pre adv st0 σ post) := by
  refine modedP₂_bind (F := fun _ μ ↦ μ = some false) (F' := fun _ _ ↦ True) _ _
    (modedP_toQuantumAt_setup _ E.setup hsetup) fun s μ hμ ↦ ?_
  subst hμ
  refine modedP₂_bind (F := fun _ _ ↦ True) (F' := fun _ _ ↦ True) _ _ ?_ fun r μ _ ↦
    modedP_toQuantumAt_other (by decide) _ _ μ
  unfold mixNormal mixRunL
  refine modedP₂_bind (F := fun _ _ ↦ True) (F' := fun _ _ ↦ True) _ _
    (modedP_redImpl_phase _ _ (pre (E.pub s)) [] false (hpre _)) fun a μ1 _ ↦ ?_
  refine modedP₂_bind (F := fun _ _ ↦ True) (F' := fun _ _ ↦ True) _ _ ?_ fun r μ2 _ ↦
    modedP_redImpl_noChal _ _ _ (hpost _ _ _ _) _ μ2
  exact modedP_mixRun_phase _ _
    (fun st q E' A ℓ μ ↦ modedP_mixTrees_phase _ _ (hσ _) st q E' A ℓ μ) _ _ μ1

end phase

/-! ## The phases of the read program -/

section readPhase

open Quantum.Xmss.Assembly (ModedP forallQueries_of_modedP_sguard)

/-- One step of a moded command tree: normalize the head, then split the command. -/
local macro "moded_step" : tactic => `(tactic| (
  (conv => arg 5; whnf);
  refine ⟨?_, fun _ ↦ ?_⟩))

variable {Par Tw Fn Out : Type} {Msg : Fn → Type} (C : TwColl Par Tw Fn Msg Out)
  (G : Fn → Tw → Prop)

/-- **The calls a phase of the read program allows**: sponge calls; reads of `PolicyOK` before
the adversary, reads keeping the records after. -/
def okC : Option Bool → (hwSpec HashOutput HashDomain Mem).Port → Prop
  | none, _ => True
  | some _, .inl (.inl _) => True
  | some true, .inl (.inr (.readH z u)) => KeepsRecs z u
  | some false, .inl (.inr (.readH z u)) => PolicyOK C G z u
  | some _, _ => False

open scoped Classical in
/-- **The phase after a call of the read program**: a sponge call, or a read by a policy other
than the answers', ends the phase before. -/
noncomputable def nxC : Option Bool → (i : (hwSpec HashOutput HashDomain Mem).Port) →
    (hwSpec HashOutput HashDomain Mem).Result i → Option Bool
  | none, _, _ => none
  | some _, .inl (.inl _), _ => some true
  | some b, .inl (.inr (.readH z u)), _ =>
    some (@ite _ (u = uAns C G z) (Classical.propDecidable _) b true)
  | some b, _, _ => some b

/-- **The support of a phase**: none when dead, `PhaseA` before the adversary, any after. -/
def InvC : Option Bool → Set (RomReg HashDomain HashOutput Mem)
  | none => ∅
  | some false => {s | PhaseA C G s}
  | some true => Set.univ

variable {C G}

theorem upd_answer : upd C G .answer = uAns C G :=
  rfl

theorem nxC_readH (b : Bool) (z : HashDomain) (u : Mem → Option HashOutput → Mem)
    (r : Option HashOutput × Mem) :
    nxC C G (some b) (.inl (.inr (.readH z u))) r =
      some (@ite _ (u = uAns C G z) (Classical.propDecidable _) b true) :=
  rfl

theorem nxT_call_inr (b : Bool) (c : Caller) (z : HashDomain) (v : HashOutput) :
    nxT (some b) (.call (c, .inr z)) v = some (if c = .answer then b else true) := by
  cases c <;> rfl

/-- **The read program of a mixed game by phases is moded by phases.** -/
theorem modedP_toReads_phase {Ω : QReg → Type} {fin : (Σ u, Ω u) → Option Bool → Prop}
    (hfin : ∀ p, fin p none) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) Ω A)
    (μ : Option Bool) (hx : ModedP okT nxT fin μ x) :
    ModedP (okC C G) (nxC C G) fin μ (IFreeM.mapLens Quantum.Xmss.Assembly.liftReadLens
      (IFreeM.substitute (readSub (upd C G)) x)) := by
  rw [← IFreeM.substitute_toSubstitution, Quantum.Xmss.Assembly.substitute_substitute]
  refine modedP_substitute _ none (fun _ ↦ trivial) (fun _ _ ↦ rfl) (fun A c μ hc ↦ ?_) hfin x μ
    hx
  rcases c with o | ⟨p | ⟨tag, n | z⟩, E, ℓ⟩
  · moded_step
    · trivial
    · exact Or.inl rfl
  · moded_step
    · rcases μ with _ | _ | _ <;> trivial
    · rcases μ with _ | _ | _ <;> exact Or.inl rfl
  · moded_step
    · trivial
    moded_step
    · trivial
    rcases μ with _ | _ | _ <;> cases tag <;> exact Or.inl rfl
  · moded_step
    · trivial
    moded_step
    · rcases μ with _ | _ | _
      · trivial
      · exact policyOK_upd tag z
      · exact keepsRecs_upd (fun h ↦ by subst h; exact hc) z
    moded_step
    · trivial
    refine Or.inl ?_
    rcases μ with _ | b
    · rfl
    · show some (@ite _ (upd C G tag z = uAns C G z) (Classical.propDecidable _) b true) =
        nxT (some b) (.call (tag, .inr z)) _
      rw [nxT_call_inr]
      rcases Classical.em (tag = .answer) with ht | ht
      · rw [ite_eq_left ht, ite_eq_left ((upd_eq_uAns_iff tag z).2 ht)]
      · rw [ite_eq_right ht, ite_eq_right fun h ↦ ht ((upd_eq_uAns_iff tag z).1 h)]

/-- A read port's entry in the register. -/
theorem readKrausH_of_hwReadKraus {z : HashDomain} {u : Mem → Option HashOutput → Mem}
    (r : Option HashOutput × Mem) {q' q : Unit × RomReg HashDomain HashOutput Mem}
    (h : hwReadKraus (.readH z u) r q' q ≠ 0) : readKrausH z u r q'.2 q.2 ≠ 0 := by
  change ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausH z u r) q' q ≠ 0 at h
  rw [kroneckerMap_apply] at h
  exact right_ne_zero_of_mul h

/-- A read from the register before the adversary lands in the support of the next phase. -/
theorem invC_readH {z : HashDomain} {u : Mem → Option HashOutput → Mem}
    (r : Option HashOutput × Mem) {s' s : RomReg HashDomain HashOutput Mem}
    (h : readKrausH z u r s' s ≠ 0) (hs : PhaseA C G s) :
    s' ∈ InvC C G (some (@ite _ (u = uAns C G z) (Classical.propDecidable _) false true)) := by
  rcases Classical.em (u = uAns C G z) with hu | hu
  · rw [ite_eq_left hu]
    rw [hu] at h
    exact phaseA_of_readKrausH r h hs
  · rw [ite_eq_right hu]
    trivial

/-- **The support of the phases at every call** of a read program moded by phases, from the
start with an empty slot. -/
theorem forallQueries_phase (m₀ : Mem) (hm₀ : m₀.slot = none) {Ω : QReg → Type}
    {fin : (Σ u, Ω u) → Option Bool → Prop} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} (hwSpec HashOutput HashDomain Mem) Ω A)
    (hx : ModedP (okC C G) (nxC C G) fin (some false) x) (ρ : Matrix A A ℂ) :
    (Quantum.Xmss.Hybrid.runtime2 HashOutput HashDomain m₀).ForallQueries .instruments
      (fun i E σ ↦ ∃ μ, okC C G μ i ∧
        QuerySupportedOn (fun m : ((hwSpec HashOutput HashDomain Mem).In i ×
          RomReg HashDomain HashOutput Mem) × E ↦ m.1.2) (InvC C G μ) σ) x
      (ρ ⊗ₖ (Quantum.Xmss.Hybrid.runtime2 HashOutput HashDomain m₀).init.matrix) := by
  refine forallQueries_of_modedP_sguard (Quantum.Xmss.Hybrid.runtime2 HashOutput HashDomain m₀)
    .instruments (InvC C G) (fun _ ↦ Set.univ) (fun μ i r σ hi hσ ↦ ?_) x (some false) hx
    (Quantum.Xmss.Hybrid.forallQueries_of_forall _ _ (fun _ _ _ ↦ querySupportedOn_univ _ _) _ _)
    ?_
  · rw [Quantum.Xmss.Hybrid.runtime2_branch]
    refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
    rcases μ with _ | _ | _
    · exact hm.1.elim
    · rcases i with (p | c) | c
      · trivial
      · cases c with
        | readH z u =>
          exact invC_readH r (readKrausH_of_hwReadKraus r hK) hm.1
        | readK _ _ => exact hi.elim
        | readK' _ _ => exact hi.elim
      · exact hi.elim
    · rcases i with (p | c) | c
      · trivial
      · cases c with
        | readH z u =>
          have he : nxC C G (some true) (.inl (.inr (.readH z u))) r = some true :=
            (nxC_readH true z u r).trans (congrArg some (ite_self _))
          rw [he]
          trivial
        | readK _ _ => exact hi.elim
        | readK' _ _ => exact hi.elim
      · exact hi.elim
  · have hS : PhaseA C G (((Database.empty, Database.empty, Database.empty),
        hwEmpty HashOutput HashDomain, m₀) : RomReg HashDomain HashOutput Mem) :=
      ⟨rfl, hm₀, fun _ _ _ ↦ rfl⟩
    intro m m' hm
    change (ρ ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
      hwEmpty HashOutput HashDomain, m₀) : RomReg HashDomain HashOutput Mem)).matrix) m m' ≠ 0
      at hm
    rw [SubState.matrix_basis, kroneckerMap_apply] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · show m.2 ∈ InvC C G (some false) ∧ m'.2 ∈ InvC C G (some false)
      rw [← he.1, ← he.2]
      exact ⟨hS, hS⟩
    · exact absurd rfl h

/-- Every program is moded when every call is allowed and every leaf accepted. -/
theorem modedP_true {spec : QuantumOracleSpec.{0, 0}} {L : LocalSig} {Ω : QReg → Type}
    {Mode : Type} (nx : Mode → (i : spec.Port) → spec.Result i → Mode) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor L spec) Ω A) (μ : Mode) :
    ModedP (fun _ _ ↦ True) nx (fun _ _ ↦ True) μ x := by
  induction x using IFreeM.inductionOn generalizing μ with
  | pure _ _ => trivial
  | liftBind _ c next ih => exact ⟨by rcases c with _ | _ <;> trivial, fun b ↦ ih b _⟩

variable (C G) in
/-- **No decompressed `⊥` at the calls** of the read program of a mixed game (Moded's
decompressed invariant, every policy logging its outcome). -/
theorem forallQueries_noBot_reads (m₀ : Mem) (hlog : ∀ z, m₀.log z = none) {Ω : QReg → Type}
    {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) Ω A)
    (ρ : Matrix A A ℂ) :
    (Quantum.Xmss.Hybrid.runtime2 HashOutput HashDomain m₀).ForallQueries .instruments
      (fun i E τ ↦ QuerySupportedOn (fun m : (hwSpec HashOutput HashDomain Mem).In i ×
        RomReg HashDomain HashOutput Mem ↦ m.2) {s | Quantum.Xmss.Assembly.NoBot s}
        (MatrixMap.conj ((1 : Matrix ((hwSpec HashOutput HashDomain Mem).In i)
          ((hwSpec HashOutput HashDomain Mem).In i) ℂ) ⊗ₖ compressReg HashOutput HashDomain Mem)
          (MatrixMap.traceRight _ E τ)))
      (IFreeM.mapLens Quantum.Xmss.Assembly.liftReadLens
        (IFreeM.substitute (readSub (upd C G)) x))
      (ρ ⊗ₖ (Quantum.Xmss.Hybrid.runtime2 HashOutput HashDomain m₀).init.matrix) := by
  have hx := modedP_toReads (upd C G) rl (fun c z ↦ recordsAt_upd c z)
    (fin := fun _ _ ↦ True) (fun _ ↦ trivial) x (some m₀) (modedP_true _ x _)
  refine QuantumRuntime.ForallQueries.mono .instruments (fun i E τ h ↦ ?_)
    (forallQueries_runtime2_dInv rl id m₀ hlog (fun _ _ h ↦ h) (fun _ _ _ _ ↦ rfl) _ (some m₀)
      rfl hx ρ)
  obtain ⟨μ, -, hμ⟩ := h
  refine hμ.mono fun s hs ↦ ?_
  rcases μ with _ | m
  · exact hs.elim
  · exact hs.2.2.1

end readPhase

/-! ## The graded bound of the read program -/

section bound

open QuantumRuntime
open Quantum.Xmss.Hybrid (runtime2 runtime2_branch kraus2)

variable {Par Tw Fn Out : Type} {Msg : Fn → Type} (C : TwColl Par Tw Fn Msg Out)
  (G : Fn → Tw → Prop)

open scoped Classical in
/-- **The weight of a call**: a sponge call and a read of a `G`-cell one, every other call
none. -/
noncomputable def κG : (hwSpec HashOutput HashDomain Mem).Port → ℕ
  | .inl (.inl _) => 1
  | .inl (.inr (.readH z _)) => if IsG C G z then 1 else 0
  | _ => 0

variable {C G}

/-- An operator supported on no register is zero. -/
theorem eq_zero_of_querySupportedOn_empty {α Y : Type*} {q : α → Y} {σ : Matrix α α ℂ}
    (h : QuerySupportedOn q ∅ σ) : σ = 0 := by
  ext a b
  by_contra hab
  exact (h a b hab).1

/-- `(√a)² = a`. -/
theorem rpow_inv_two_sq (a : ℝ≥0∞) : (a ^ (2⁻¹ : ℝ)) ^ 2 = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

open scoped Classical in
/-- **The graded step of every allowed call** of the read program in runtime 2, for the event
`BadR` (`F` a bound on the fibers of the truncation): a sponge call and a read of a `G`-cell cost
`√(gradeEta F · tr)`, every other read nothing. -/
theorem tsum_potential_step_le (hs : GSep C G) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ C.trunc y = o).card ≤ F) (m₀ : Mem)
    (i : (hwSpec HashOutput HashDomain Mem).Port)
    {σ : Matrix ((hwSpec HashOutput HashDomain Mem).In i × RomReg HashDomain HashOutput Mem)
      ((hwSpec HashOutput HashDomain Mem).In i × RomReg HashDomain HashOutput Mem) ℂ}
    (hσ : σ.PosSemidef)
    (hC : ∃ μ, okC C G μ i ∧ QuerySupportedOn (fun m : (hwSpec HashOutput HashDomain Mem).In i ×
      RomReg HashDomain HashOutput Mem ↦ m.2) (InvC C G μ) σ)
    (hnb : QuerySupportedOn (fun m : (hwSpec HashOutput HashDomain Mem).In i ×
        RomReg HashDomain HashOutput Mem ↦ m.2) {s | Quantum.Xmss.Assembly.NoBot s}
      (MatrixMap.conj ((1 : Matrix ((hwSpec HashOutput HashDomain Mem).In i)
        ((hwSpec HashOutput HashDomain Mem).In i) ℂ) ⊗ₖ compressReg HashOutput HashDomain Mem) σ)) :
    ∑' r, potential (hwProjector (BadR C G)) (((runtime2 HashOutput HashDomain m₀).step i).branch
        r σ) ≤
      (potential (hwProjector (BadR C G)) σ ^ (2⁻¹ : ℝ) + κG C G i *
        (ENNReal.ofReal (gradeEta HashOutput F) * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ)) ^ 2 := by
  obtain ⟨μ, hok, hsupp⟩ := hC
  have hbr : ∀ r, ((runtime2 HashOutput HashDomain m₀).step i).branch r σ =
      MatrixMap.conj (kraus2 HashOutput HashDomain m₀ i r) σ := fun r ↦
    LinearMap.congr_fun (runtime2_branch m₀ i r) σ
  simp only [hbr]
  rcases μ with _ | b
  · have h0 := eq_zero_of_querySupportedOn_empty hsupp
    subst h0
    have hz : ∀ r, potential (hwProjector (BadR C G))
        (MatrixMap.conj (kraus2 HashOutput HashDomain m₀ i r) 0) = 0 := fun r ↦ by
      rw [map_zero, potential, map_zero, Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero]
    simp only [hz, tsum_zero]
    exact zero_le
  rcases i with (p | c) | c
  · change ∑' r : Unit, _ ≤ _
    rw [tsum_eq_single () fun r hr ↦ absurd (Subsingleton.elim r ()) hr]
    have h := potential_sponge_badR_le (G := G) hF m₀ p hσ
    have h2 := pow_le_pow_left₀ (by positivity) h 2
    rw [rpow_inv_two_sq] at h2
    refine h2.trans_eq ?_
    change _ = (_ + ((1 : ℕ) : ℝ≥0∞) * _) ^ 2
    rw [Nat.cast_one, one_mul]
    rfl
  · cases c with
    | readH z u =>
      have hbr' : ∀ r, MatrixMap.conj (kraus2 HashOutput HashDomain m₀ (.inl (.inr (.readH z u))) r)
          σ = MatrixMap.conj (hwReadKraus (.readH z u) r) σ := fun _ ↦ rfl
      simp only [hbr']
      by_cases hz : IsG C G z
      · have hκ : κG C G (.inl (.inr (.readH z u))) = 1 := by simp [κG, hz]
        rw [hκ, Nat.cast_one, one_mul, ← ENNReal.ofReal_mul (gradeEta_nonneg _ _)]
        refine tsum_potential_read_badR hF hσ (readNoBot_of_noBot _ hnb) fun q hq ↦ ?_
        have hm := (hsupp q q hq).1
        rcases b with _ | _
        · exact keepsRecsAt_or_recCase hs hok hm
        · exact Or.inl (hok q.2.2.2)
      · have hκ : κG C G (.inl (.inr (.readH z u))) = 0 := by simp [κG, hz]
        have hk : KeepsRecs z u := by
          rcases b with _ | _
          · rcases hok with rfl | h
            · exact fun m o ↦ ⟨by rw [uAns_recs, ite_eq_right fun h ↦ hz h.1], Or.inl rfl⟩
            · exact h
          · exact hok
        have h0 := readFlip_eq_zero (BadR C G) (readInvisible_badR hz hk) σ hσ
        unfold readFlip at h0
        rw [tsub_eq_zero_iff_le] at h0
        rw [hκ, Nat.cast_zero, zero_mul, add_zero, rpow_inv_two_sq]
        exact h0
    | readK _ _ => rcases b with _ | _ <;> exact hok.elim
    | readK' _ _ => rcases b with _ | _ <;> exact hok.elim
  · rcases b with _ | _ <;> exact hok.elim

/-- The event starts empty. -/
theorem potential_init_badR (m₀ : Mem) (hm₀ : ∀ x, m₀.recs x = none) :
    potential (hwProjector (BadR C G)) ((SubState.basis ()).matrix ⊗ₖ
      (runtime2 HashOutput HashDomain m₀).init.matrix) = 0 := by
  have hz : hwProjector (BadR C G) * (SubState.basis (((Database.empty, Database.empty,
      Database.empty), hwEmpty HashOutput HashDomain, m₀) : RomReg HashDomain HashOutput Mem)).matrix
      = 0 := by
    rw [hwProjector, labelProjector, SubState.matrix_basis]
    ext a b
    rw [diagonal_mul, Matrix.single_apply, Matrix.zero_apply]
    by_cases h : ((Database.empty, Database.empty, Database.empty), hwEmpty HashOutput HashDomain,
        m₀) = a ∧ ((Database.empty, Database.empty, Database.empty),
          hwEmpty HashOutput HashDomain, m₀) = b
    · rcases h with ⟨rfl, rfl⟩
      simp [start_not_mem_badR (C := C) (G := G) m₀ hm₀]
    · simp [h]
  change potential (hwProjector (BadR C G)) ((SubState.basis ()).matrix ⊗ₖ
    (SubState.basis (((Database.empty, Database.empty, Database.empty),
      hwEmpty HashOutput HashDomain, m₀) : RomReg HashDomain HashOutput Mem)).matrix) = 0
  rw [potential, MatrixMap.amplifyLeft_conj, MatrixMap.conj_apply, ← mul_kronecker_mul, hz,
    kronecker_zero, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero]

variable (C G) in
/-- The read program of a mixed program with the policies `upd`. -/
noncomputable abbrev readProg {Ω : QReg → Type} {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) Ω A) :
    QuantumComp LocalSig.instruments.{0} (hwSpec HashOutput HashDomain Mem) Ω A :=
  IFreeM.mapLens Quantum.Xmss.Assembly.liftReadLens (IFreeM.substitute (readSub (upd C G)) x)

open scoped Classical in
/-- **The event weight of the read program of a mixed program by phases**: with at most `n` sponge
calls and reads of `G`-cells (charge `κG`), the event `BadR` ends with weight at most
`n² · gradeEta F`. -/
theorem eventWeight_badR_le (hs : GSep C G) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ C.trunc y = o).card ≤ F) (m₀ : Mem)
    (hm₀ : m₀.slot = none) (hrec : ∀ x, m₀.recs x = none) (hlog : ∀ z, m₀.log z = none)
    {Ω : QReg → Type}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) Ω
      (QReg.of Unit))
    (hx : Quantum.Xmss.Assembly.ModedP okT nxT (fun _ _ ↦ True) (some false) x) {n : ℕ}
    (hn : IFreeM.IsChargeBound (readProg C G x) (portCharge (κG C G)) n) :
    (runtime2 HashOutput HashDomain m₀).eventWeight .instruments (hwProjector (BadR C G))
        (readProg C G x) ((SubState.basis ()).matrix ⊗ₖ
          (runtime2 HashOutput HashDomain m₀).init.matrix) ≤
      (n : ℝ≥0∞) ^ 2 * ENNReal.ofReal (gradeEta HashOutput F) := by
  have hρ : ((SubState.basis ()).matrix ⊗ₖ
      (runtime2 HashOutput HashDomain m₀).init.matrix).PosSemidef :=
    ((SubState.basis ()).prod (runtime2 HashOutput HashDomain m₀).init).posSemidef
  have htr : ENNReal.ofReal ((SubState.basis ()).matrix ⊗ₖ
      (runtime2 HashOutput HashDomain m₀).init.matrix).trace.re ≤ 1 := by
    rw [← SubState.matrix_prod]
    exact ENNReal.ofReal_le_one.mpr
      ((SubState.basis ()).prod (runtime2 HashOutput HashDomain m₀).init).trace_re_le_one
  set ρ := (SubState.basis ()).matrix ⊗ₖ (runtime2 HashOutput HashDomain m₀).init.matrix
  have hP := Quantum.Xmss.Assembly.forallQueries_and
    (forallQueries_phase m₀ hm₀ _ (modedP_toReads_phase (C := C) (G := G) (fun _ ↦ trivial) x _ hx)
      (SubState.basis ()).matrix)
    (forallQueries_noBot_reads C G m₀ hlog x (SubState.basis ()).matrix)
  have h := rpow_inv_two_eventWeight_le_weighted (runtime2 HashOutput HashDomain m₀) .instruments
    (hwProjector (BadR C G)) (κG C G)
    (fun i E τ ↦ (∃ μ, okC C G μ i ∧ QuerySupportedOn (fun m : ((hwSpec HashOutput HashDomain
      Mem).In i × RomReg HashDomain HashOutput Mem) × E ↦ m.1.2) (InvC C G μ) τ) ∧
      QuerySupportedOn (fun m : (hwSpec HashOutput HashDomain Mem).In i ×
        RomReg HashDomain HashOutput Mem ↦ m.2) {s | Quantum.Xmss.Assembly.NoBot s}
        (MatrixMap.conj ((1 : Matrix ((hwSpec HashOutput HashDomain Mem).In i)
          ((hwSpec HashOutput HashDomain Mem).In i) ℂ) ⊗ₖ compressReg HashOutput HashDomain Mem)
          (MatrixMap.traceRight _ E τ)))
    (ENNReal.ofReal (gradeEta HashOutput F)) (fun _ _ ↦ 0)
    (fun i E τ hτ hτp ↦ by
      obtain ⟨⟨μ, hok, hsup⟩, hN⟩ := hτ
      rw [add_zero]
      exact tsum_potential_step_le hs hF m₀ i hτp.traceRight
        ⟨μ, hok, Quantum.Xmss.Assembly.querySupportedOn_traceRight
          (q := fun m : (hwSpec HashOutput HashDomain Mem).In i ×
            RomReg HashDomain HashOutput Mem ↦ m.2) hsup⟩ hN)
    (readProg C G x) n hn hρ hP
  have hw0 : (runtime2 HashOutput HashDomain m₀).totalWeight .instruments (fun _ _ ↦ 0)
      (readProg C G x) ρ = 0 := by
    simpa using Quantum.Xmss.Hybrid.totalWeight_const_mul_weight
      (runtime2 HashOutput HashDomain m₀) .instruments 0 (fun _ _ ↦ 0) (readProg C G x) ρ
  rw [potential_init_badR m₀ hrec, hw0, add_zero, ENNReal.zero_rpow_of_pos (by norm_num),
    add_zero] at h
  have h2 := pow_le_pow_left₀ (by positivity) h 2
  rw [rpow_inv_two_sq] at h2
  refine h2.trans ?_
  rw [mul_pow, rpow_inv_two_sq]
  gcongr
  exact mul_le_of_le_one_right zero_le htr

end bound

/-! ## A win is in the event -/

section win

open OracleComp OracleSpec TcrQuery

variable {Par Tw Fn Out EFn EOut : Type} {Msg : Fn → Type} {EMsg : EFn → Type}
  (C : TwColl Par Tw Fn Msg Out) (D : TwColl Par Tw EFn EMsg EOut) (G : Fn → Tw → Prop)

/-- The cell of a target input at the parameter `P` (`0` if too long). -/
def tcell (P : Par) (e : Σ l, Tw × Msg l) : HashDomain :=
  (encodeInput (C.layout e.1 P e.2.1 e.2.2)).getD 0

/-- The cell a transcript entry's answer reads. -/
def entCell (P : Par) :
    ((q : TcrQuery Tw Fn Msg EFn EMsg) × Resp Par Out EOut q) → Option HashDomain
  | ⟨.target l t m, _⟩ => encodeInput (C.layout l P t m)
  | ⟨.eval l t m, _⟩ => encodeInput (D.layout l P t m)
  | ⟨.reveal, _⟩ => none

/-- The rules of the transcript the records need: distinct target tweaks, no evaluation at a
target tweak. -/
def TVal (log : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)) : Prop :=
  ((tcrTargets log).map fun e ↦ e.1.2.1).Nodup ∧
    ∀ t ∈ log.filterMap evalTweak, t ∉ (tcrTargets log).map fun e ↦ e.1.2.1

/-- **The invariant of the records**: an empty slot, every record read by a logged answer, and
on a transcript following the rules, every target at a tweak of `G` recorded at its cell with its
digest. -/
def RecInv (P : Par) (log : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)) (m : Mem) :
    Prop :=
  m.slot = none ∧
  (∀ x v, m.recs x = some v → ∃ e ∈ log, entCell C D P e = some x) ∧
  (TVal log → ∀ e ∈ tcrTargets log, G e.1.1 e.1.2.1 →
    ∃ v, m.recs (tcell C P e.1) = some v ∧ e.2 = C.trunc v)

/-- The invariant at a live mode. -/
def LiveInv (P : Par) (log : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut))
    (μ : Option Mem) : Prop :=
  ∀ m, μ = some m → RecInv C D G P log m

variable {C D G}

theorem tcrTargets_append (log : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut))
    (e : (q : TcrQuery Tw Fn Msg EFn EMsg) × Resp Par Out EOut q) :
    tcrTargets (log ++ [e]) = tcrTargets log ++ (asTarget e).toList := by
  unfold tcrTargets
  rw [List.filterMap_append]
  rcases h : asTarget e with _ | a <;> simp [h]

theorem tVal_of_append {log : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)}
    {e : (q : TcrQuery Tw Fn Msg EFn EMsg) × Resp Par Out EOut q} (h : TVal (log ++ [e])) :
    TVal log := by
  obtain ⟨h1, h2⟩ := h
  rw [tcrTargets_append, List.map_append] at h1 h2
  refine ⟨h1.of_append_left, fun t ht htt ↦ h2 t ?_ (List.mem_append_left _ htt)⟩
  rw [List.filterMap_append]
  exact List.mem_append_left _ ht

theorem uAns_recs_of_some {x y : HashDomain} {m : Mem} {o : Option HashOutput} {w : HashOutput}
    (h : m.recs y = some w) : (uAns C G x m o).recs y = some w := by
  rw [uAns_recs]
  split_ifs with hc
  · rw [Function.update_of_ne]
    · exact h
    · rintro rfl
      rw [hc.2 y hc.1.sameCls_self] at h
      cases h
  · exact h

/-- A new record of an answer read is at its cell. -/
theorem uAns_recs_new {x y : HashDomain} {m : Mem} {o : Option HashOutput} {w : HashOutput}
    (h : (uAns C G x m o).recs y = some w) : m.recs y = some w ∨ y = x := by
  rw [uAns_recs] at h
  split_ifs at h with hc
  · by_cases hy : y = x
    · exact Or.inr hy
    · rw [Function.update_of_ne hy] at h
      exact Or.inl h
  · exact Or.inl h

/-- **An answer read keeps the invariant** for an entry reading its cell `x` whose class is
recorded, or a non-target entry. -/
theorem recInv_uAns {P : Par} {log : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)}
    {m : Mem} {x : HashDomain} {o : Option HashOutput}
    {e : (q : TcrQuery Tw Fn Msg EFn EMsg) × Resp Par Out EOut q}
    (hI : RecInv C D G P log m) (he : entCell C D P e = some x)
    (h3 : TVal (log ++ [e]) → ∀ e' ∈ (asTarget e).toList, G e'.1.1 e'.1.2.1 →
      ∃ v, (uAns C G x m o).recs (tcell C P e'.1) = some v ∧ e'.2 = C.trunc v) :
    RecInv C D G P (log ++ [e]) (uAns C G x m o) := by
  obtain ⟨h0, h2, h4⟩ := hI
  refine ⟨h0, fun y v hv ↦ ?_, fun hv e' he' hG ↦ ?_⟩
  · rcases uAns_recs_new hv with h | rfl
    · obtain ⟨e'', he'', hc⟩ := h2 y _ h
      exact ⟨e'', List.mem_append_left _ he'', hc⟩
    · exact ⟨e, List.mem_append_right _ (List.mem_singleton_self _), he⟩
  · rw [tcrTargets_append] at he'
    rcases List.mem_append.1 he' with he' | he'
    · obtain ⟨v, hv', hd⟩ := h4 (tVal_of_append hv) e' he' hG
      exact ⟨v, uAns_recs_of_some hv', hd⟩
    · exact h3 hv e' he' hG

/-- **A read of a `G`-cell by a target's answer creates the record** on a transcript following
the rules. -/
theorem recordless_target (hs : GSep C G) (htw : D.TweakSeparated C) {P : Par}
    {log : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)} {m : Mem} {l : Fn} {t : Tw}
    {mm : Msg l} {y : Out} {x : HashDomain} (hI : RecInv C D G P log m)
    (hx : encodeInput (C.layout l P t mm) = some x) (hG : G l t)
    (hv : TVal (log ++ [⟨.target l t mm, y⟩])) : Recordless C G m x := by
  intro x₀ hx₀
  by_contra hne
  obtain ⟨v₀, hv₀⟩ := Option.ne_none_iff_exists'.1 hne
  obtain ⟨e', he', hc⟩ := hI.2.1 x₀ v₀ hv₀
  have hxG : GCell C G x P t := ⟨l, mm, hG, hx⟩
  obtain ⟨P', t', h₀, h₁⟩ := hx₀
  obtain ⟨hP, ht⟩ := gCell_unique hs hxG h₁
  rw [hP, ht] at h₀
  obtain ⟨l₀, m₀', hG₀, he₀⟩ := h₀
  have htgt : t ∉ (tcrTargets log).map (fun e ↦ e.1.2.1) := fun ht ↦ by
    have hnd := hv.1
    rw [tcrTargets_append, List.map_append] at hnd
    exact List.disjoint_of_nodup_append hnd ht (by simp [asTarget])
  rcases e' with ⟨q, a⟩
  rcases q with ⟨l', t', mm'⟩ | ⟨l', t', mm'⟩ | _
  · simp only [entCell] at hc
    have hb := encodeInput_injective hc he₀
    obtain ⟨-, rfl⟩ := hs l₀ P t m₀' l' P t' mm' hG₀ hb
    exact htgt (List.mem_map.2 ⟨(⟨l', t', mm'⟩, a), List.mem_filterMap.2
      ⟨⟨.target l' t' mm', a⟩, he', rfl⟩, rfl⟩)
  · simp only [entCell] at hc
    have hb := encodeInput_injective hc he₀
    obtain rfl := htw l₀ P t m₀' l' t' mm' hb
    refine hv.2 t' ?_ ?_
    · rw [List.filterMap_append]
      exact List.mem_append_left _ (List.mem_filterMap.2 ⟨⟨.eval l' t' mm', a⟩, he', rfl⟩)
    · rw [tcrTargets_append, List.map_append]
      exact List.mem_append_right _ (by simp [asTarget])
  · cases hc


theorem recInv_append_nonTarget {P : Par}
    {log : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)} {m : Mem}
    {e : (q : TcrQuery Tw Fn Msg EFn EMsg) × Resp Par Out EOut q} (hI : RecInv C D G P log m)
    (he : asTarget e = none) : RecInv C D G P (log ++ [e]) m := by
  obtain ⟨h0, h2, h4⟩ := hI
  refine ⟨h0, fun y v hv ↦ ?_, fun hv e' he' hG ↦ ?_⟩
  · obtain ⟨e'', he'', hc⟩ := h2 y v hv
    exact ⟨e'', List.mem_append_left _ he'', hc⟩
  · rw [tcrTargets_append, he, Option.toList_none, List.append_nil] at he'
    exact h4 (tVal_of_append hv) e' he' hG

/-- A live mode keeps the invariant through a read whose policy keeps it. -/
theorem liveInv_stepRd {P : Par} {log log' : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)}
    {μ : Option Mem} {u : Mem → Option HashOutput → Mem} {z : HashDomain} {v : HashOutput}
    (hI : LiveInv C D G P log μ)
    (hu : ∀ m, RecInv C D G P log m → RecInv C D G P log' (u m (some v))) :
    LiveInv C D G P log' (stepRd rl u z μ v) := by
  intro m' hm'
  rcases μ with _ | m
  · cases hm'
  · simp only [stepRd] at hm'
    split_ifs at hm'
    injection hm' with hm'
    subst hm'
    exact hu m (hI m rfl)

theorem liveRun_pure {u : HashDomain → Mem → Option HashOutput → Mem} {α : Type} {a a' : α}
    {μ μ' : Option Mem} (h : LiveRun rl u (pure a') μ a μ') : a = a' ∧ μ' = μ := by
  unfold LiveRun at h
  simpa using h

theorem liveRun_bind {u : HashDomain → Mem → Option HashOutput → Mem} {α β : Type}
    {oa : OracleComp romWorld.Oracles α} {ob : α → OracleComp romWorld.Oracles β} {b : β}
    {μ μ'' : Option Mem} (h : LiveRun rl u (oa >>= ob) μ b μ'') :
    ∃ a μ', LiveRun rl u oa μ a μ' ∧ LiveRun rl u (ob a) μ' b μ'' := by
  unfold LiveRun at h
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at h
  obtain ⟨⟨a, μ'⟩, h1, h2⟩ := h
  exact ⟨a, μ', h1, h2⟩

/-- A live run of a read of `x`: the mode moves by `stepRd`. -/
theorem liveRun_query {u : HashDomain → Mem → Option HashOutput → Mem} {x : romWorld.Prim}
    {w : romWorld.Oracles.Range (.inr x)} {μ μ' : Option Mem}
    (h : LiveRun rl u (liftM (romWorld.Oracles.query (.inr x)) :
      OracleComp romWorld.Oracles (romWorld.Oracles.Range (.inr x))) μ w μ') :
    μ' = stepRd rl (u x) x μ w := by
  unfold LiveRun at h
  rw [← bind_pure (liftM (romWorld.Oracles.query (.inr x)) :
    OracleComp romWorld.Oracles (romWorld.Oracles.Range (.inr x))), run_simulateQ_query_bind,
    mem_support_bind_iff] at h
  obtain ⟨⟨w', μ₂⟩, h3, h4⟩ := h
  have h5 : (w, μ') = (w', μ₂) := by simpa using h4
  simp only [Prod.mk.injEq] at h5
  obtain ⟨rfl, rfl⟩ := h5
  simp only [liveImpl, StateT.run, support_map, Set.mem_image, Prod.mk.injEq] at h3
  obtain ⟨v, -, rfl, rfl⟩ := h3
  rfl

/-- A live run of a hash of an encoded input: one read of its cell. -/
theorem liveRun_hashQ {u : HashDomain → Mem → Option HashOutput → Mem} {β : Type}
    (f : HashOutput → β) {l : HashInput} {x : HashDomain} (hx : encodeInput l = some x) {b : β}
    {μ μ' : Option Mem} (h : LiveRun rl u (f <$> hashQ l) μ b μ') :
    ∃ v, b = f v ∧ μ' = stepRd rl (u x) x μ v := by
  rw [hashQ_of_encodeInput_eq_some hx] at h
  change LiveRun rl u (f <$> (liftM (romWorld.Oracles.query (.inr x)) :
    OracleComp romWorld.Oracles HashOutput)) μ b μ' at h
  rw [map_eq_bind_pure_comp] at h
  obtain ⟨w, μ1, h1, h2⟩ := liveRun_bind h
  obtain ⟨hb, hμ⟩ := liveRun_pure h2
  rw [hμ]
  exact ⟨w, hb, liveRun_query h1⟩

/-- A live run with no hash keeps the mode. -/
theorem liveRun_noHash {u : HashDomain → Mem → Option HashOutput → Mem} {α : Type}
    (oa : OracleComp romWorld.Oracles α) (h : Common.QueryCostAtMost oa hashW 0) {a : α}
    {μ μ' : Option Mem} (hl : LiveRun rl u oa μ a μ') : μ' = μ := by
  induction oa using OracleComp.inductionOn generalizing μ with
  | pure a' => exact (liveRun_pure hl).2
  | query_bind t k ih =>
    rw [Common.isWeightBound_query_bind_iff] at h
    unfold LiveRun at hl
    rw [run_simulateQ_query_bind, mem_support_bind_iff] at hl
    obtain ⟨⟨w, μ1⟩, h1, h2⟩ := hl
    rcases t with n | z
    · change (w, μ1) ∈ support ((fun b ↦ (b, μ)) <$>
        (liftM (romWorld.Oracles.query (.inl n)) : OracleComp romWorld.Oracles _)) at h1
      simp only [support_map, Set.mem_image, Prod.mk.injEq] at h1
      obtain ⟨w', -, -, hμ⟩ := h1
      rw [← hμ] at h2
      exact ih w (h.2 w) h2
    · exact absurd h.1 (by simp [hashW])

/-- **The reduction's live runs keep an invariant** kept by its own reads and by the challenger's
answers. -/
theorem liveRedRun_inv {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
    (Inv : QueryLog R' → Option Mem → Prop)
    (hred : ∀ log μ i y μ', Inv log μ →
      (y, μ') ∈ support ((liveImpl rl (upd C G .red) i).run μ) → Inv log μ')
    (hans : ∀ log μ q' a μ', Inv log μ → LiveRun rl (upd C G .answer) (ans q') μ a μ' →
      Inv (log ++ [⟨q', a⟩]) μ') {α : Type} (oa : OracleComp (romWorld.Oracles + R') α) :
    ∀ log μ r μ', Inv log μ → LiveRedRun rl (upd C G) ans oa log μ r μ' → Inv r.2 μ' := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro log μ r μ' hI h
    unfold LiveRedRun at h
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at h
    obtain ⟨-, h1, h2⟩ := h
    rw [h1, h2]
    exact hI
  | query_bind t k ih =>
    intro log μ r μ' hI h
    unfold LiveRedRun at h
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at h
    obtain ⟨⟨a, log₁, μ₁⟩, h1, h2⟩ := h
    refine ih a log₁ μ₁ r μ' ?_ h2
    rcases t with i | q'
    · change (a, (log₁, μ₁)) ∈ support ((fun p ↦ (p.1, (log, p.2))) <$>
        (liveImpl rl (upd C G .red) i).run μ) at h1
      rw [support_map] at h1
      obtain ⟨⟨y, μ₂⟩, h3, h4⟩ := h1
      simp only [Prod.mk.injEq] at h4
      obtain ⟨rfl, rfl, rfl⟩ := h4
      exact hred log μ i y μ₂ hI h3
    · change (a, (log₁, μ₁)) ∈ support ((fun p ↦ (p.1, (log ++ [⟨q', p.1⟩], p.2))) <$>
        (simulateQ (liveImpl rl (upd C G .answer)) (ans q')).run μ) at h1
      rw [support_map] at h1
      obtain ⟨⟨y, μ₂⟩, h3, h4⟩ := h1
      simp only [Prod.mk.injEq] at h4
      obtain ⟨rfl, rfl, rfl⟩ := h4
      exact hans log μ q' y μ₂ hI h3

/-- The reduction's own reads keep the invariant. -/
theorem liveInv_red {P : Par} {log : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)}
    {μ μ' : Option Mem} {i : romWorld.Oracles.Domain} {y : romWorld.Oracles.Range i}
    (hI : LiveInv C D G P log μ) (h : (y, μ') ∈ support ((liveImpl rl (upd C G .red) i).run μ)) :
    LiveInv C D G P log μ' := by
  rcases i with n | z
  · change (y, μ') ∈ support ((fun b ↦ (b, μ)) <$>
      (liftM (romWorld.Oracles.query (.inl n)) : OracleComp romWorld.Oracles _)) at h
    rw [support_map] at h
    obtain ⟨w, -, hw⟩ := h
    simp only [Prod.mk.injEq] at hw
    rw [← hw.2]
    exact hI
  · have hμ := liveRun_query (u := upd C G .red) (x := z) (w := y) (μ := μ) (μ' := μ') h
    rw [hμ]
    exact liveInv_stepRd hI fun m hm ↦ hm

theorem encodeInput_tcell (hlen : C.LengthLe maxLen) (P : Par) (e : Σ l, Tw × Msg l) :
    encodeInput (C.layout e.1 P e.2.1 e.2.2) = some (tcell C P e) := by
  rw [tcell, encodeInput_of_length_le (hlen _ _ _ _)]
  rfl

/-- **The challenger's answers keep the invariant.** -/
theorem liveInv_answer [SampleableType Par] (hs : GSep C G) (htw : D.TweakSeparated C)
    (hlen : C.LengthLe maxLen) {P : Par}
    {log : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)} {μ μ' : Option Mem}
    (q' : TcrQuery Tw Fn Msg EFn EMsg) {a : Resp Par Out EOut q'}
    (hI : LiveInv C D G P log μ)
    (h : LiveRun rl (upd C G .answer) ((smTcrIn romWorld C D G).answer P q') μ a μ') :
    LiveInv C D G P (log ++ [⟨q', a⟩]) μ' := by
  rcases q' with ⟨l, t, mm⟩ | ⟨l, t, mm⟩ | _
  · have hx := encodeInput_tcell hlen P ⟨l, t, mm⟩
    change LiveRun rl (upd C G .answer) (C.trunc <$> hashQ (C.layout l P t mm)) μ a μ' at h
    obtain ⟨v, rfl, rfl⟩ := liveRun_hashQ C.trunc hx h
    refine liveInv_stepRd hI fun m hm ↦ recInv_uAns hm hx fun hv e' he' hG ↦ ?_
    simp only [asTarget, Option.toList_some, List.mem_singleton] at he'
    subst he'
    have hrl := recordless_target hs htw hm hx hG hv
    refine ⟨v, ?_, rfl⟩
    change (uAns C G (tcell C P ⟨l, t, mm⟩) m (some v)).recs (tcell C P ⟨l, t, mm⟩) = some v
    rw [uAns_recs, ite_eq_left ⟨⟨P, t, l, mm, hG, hx⟩, hrl⟩, Function.update_self]
    rfl
  · change LiveRun rl (upd C G .answer) (D.trunc <$> hashQ (D.layout l P t mm)) μ a μ' at h
    rcases hx : encodeInput (D.layout l P t mm) with _ | x
    · have h0 : hashQ (D.layout l P t mm) = pure 0 := by simp [hashQ, hx]
      rw [h0] at h
      change LiveRun rl (upd C G .answer) (pure (D.trunc 0)) μ a μ' at h
      obtain ⟨-, rfl⟩ := liveRun_pure h
      exact fun m hm ↦ recInv_append_nonTarget (hI m hm) rfl
    · obtain ⟨v, rfl, rfl⟩ := liveRun_hashQ D.trunc hx h
      refine liveInv_stepRd hI fun m hm ↦ recInv_uAns hm hx fun _ e' he' ↦ ?_
      simp [asTarget] at he'
  · change LiveRun rl (upd C G .answer) (pure P) μ a μ' at h
    obtain ⟨-, rfl⟩ := liveRun_pure h
    exact fun m hm ↦ recInv_append_nonTarget (hI m hm) rfl

variable (C G) in
/-- **The winning memories**: the judge's read is in its target. -/
def Won : Set Mem :=
  {m | ∃ z y, m.slot = some (z, y) ∧ y ∈ tgt C G (hwEmpty HashOutput HashDomain) m z}

/-- **On a transcript following the rules, the record of a target's class is its cell.** -/
theorem rec_eq_tcell (hs : GSep C G) (htw : D.TweakSeparated C) (hlen : C.LengthLe maxLen)
    {P : Par} {log : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)} {m : Mem}
    (hI : RecInv C D G P log m) (hv : TVal log) {e : (Σ l, Tw × Msg l) × Out}
    (he : e ∈ tcrTargets log) (hG : G e.1.1 e.1.2.1) {x' : HashDomain}
    (hx' : (m.recs x').isSome) (hc : SameCls C G x' (tcell C P e.1)) : x' = tcell C P e.1 := by
  obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.1 hx'
  obtain ⟨e'', he'', hsrc⟩ := hI.2.1 x' v' hv'
  have hxe : GCell C G (tcell C P e.1) P e.1.2.1 :=
    ⟨e.1.1, e.1.2.2, hG, encodeInput_tcell hlen P e.1⟩
  obtain ⟨P', t', h₀, h₁⟩ := hc
  obtain ⟨hP, ht⟩ := gCell_unique hs hxe h₁
  rw [hP, ht] at h₀
  obtain ⟨l₀, m₀', hG₀, he₀⟩ := h₀
  rcases e'' with ⟨q, a⟩
  rcases q with ⟨l', t'', mm'⟩ | ⟨l', t'', mm'⟩ | _
  · simp only [entCell] at hsrc
    have hb := encodeInput_injective hsrc he₀
    obtain ⟨-, ht''⟩ := hs l₀ P _ m₀' l' P t'' mm' hG₀ hb
    have hmem : ((⟨l', t'', mm'⟩ : Σ l, Tw × Msg l), a) ∈ tcrTargets log :=
      List.mem_filterMap.2 ⟨_, he'', rfl⟩
    have heq := List.inj_on_of_nodup_map hv.1 hmem he ht''
    subst heq
    exact Option.some.inj (hsrc.symm.trans (encodeInput_tcell hlen P ⟨l', t'', mm'⟩))
  · simp only [entCell] at hsrc
    have hb := encodeInput_injective hsrc he₀
    obtain rfl := htw l₀ P _ m₀' l' t'' mm' hb
    exact absurd (List.mem_map.2 ⟨e, he, rfl⟩) (hv.2 _ (List.mem_filterMap.2 ⟨_, he'', rfl⟩))
  · cases hsrc

/-- **The decision accepts only in a winning memory.** -/
theorem won_of_judge [SampleableType Par] (hs : GSep C G)
    (hinj : ∀ l P t, (C.layout l P t).Injective) (htw : D.TweakSeparated C)
    (hlen : C.LengthLe maxLen) {P : Par}
    {log : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)} (out : Σ l, Tw × Msg l)
    {μ μ' : Option Mem} (hI : LiveInv C D G P log μ)
    (h : LiveRun rl (upd C G .judge) ((smTcrIn romWorld C D G).judge P log out) μ true μ') :
    ∀ m, μ' = some m → m ∈ Won C G := by
  obtain ⟨b, μ₁, h1, h2⟩ := liveRun_bind h
  obtain ⟨hb, hμ₁⟩ := liveRun_pure h2
  obtain ⟨y, μ₂, h3, h4⟩ := liveRun_bind h1
  obtain ⟨hby, hμ₂⟩ := liveRun_pure h4
  have hz := encodeInput_tcell hlen P out
  change LiveRun rl (upd C G .judge) (C.trunc <$> hashQ (C.layout out.1 P out.2.1 out.2.2)) μ y
    μ₂ at h3
  obtain ⟨v, rfl, hμv⟩ := liveRun_hashQ C.trunc hz h3
  rw [hμ₁, hμ₂, hμv]
  subst hby
  have hb' := hb.symm
  rw [Bool.and_eq_true, holds_eq_true, holds_eq_true] at hb'
  obtain ⟨hIn, hval, e, he, h1e, h2e, hne, hde⟩ := hb'
  intro m' hm'
  rcases μ with _ | m
  · cases hm'
  simp only [stepRd] at hm'
  split_ifs at hm'
  injection hm' with hm'
  subst hm'
  obtain ⟨h0, -, h4⟩ := hI m rfl
  obtain ⟨w, hw, hdw⟩ := h4 ⟨hval.1, hval.2.2⟩ e he (hIn e he)
  have hcls : SameCls C G (tcell C P e.1) (tcell C P out) := by
    obtain ⟨⟨l, t, mm⟩, d⟩ := e
    obtain ⟨l', t', mm'⟩ := out
    simp only at h1e h2e
    subst h1e h2e
    exact ⟨P, t, ⟨l, mm, hIn _ he, encodeInput_tcell hlen P ⟨l, t, mm⟩⟩,
      ⟨l, mm', hIn _ he, encodeInput_tcell hlen P ⟨l, t, mm'⟩⟩⟩
  refine ⟨tcell C P out, v, ?_, tcell C P e.1, w, hw, ?_, hcls,
    fun x' hx' hc ↦ rec_eq_tcell hs htw hlen (hI m rfl) ⟨hval.1, hval.2.2⟩ he (hIn e he) hx'
      (hc.trans hs hcls.symm), hde.symm.trans hdw⟩
  · change m.slot.or _ = _
    rw [h0]
    rfl
  · intro heq
    obtain ⟨⟨l, t, mm⟩, d⟩ := e
    obtain ⟨l', t', mm'⟩ := out
    simp only at h1e h2e
    subst h1e h2e
    have hx := encodeInput_tcell hlen P ⟨l, t, mm⟩
    rw [heq] at hx
    have hmm := hinj l P t (encodeInput_injective hx hz)
    exact hne (by simp only at hmm; subst hmm; rfl)

end win

/-! ## The QROM bound of SM-TCR-C -/

section main

open OracleComp OracleSpec TcrQuery
open Quantum.Xmss.Hybrid (runtime2)

variable {Par Tw Fn Out EFn EOut : Type} {Msg : Fn → Type} {EMsg : EFn → Type}
  {C : TwColl Par Tw Fn Msg Out} {D : TwColl Par Tw EFn EMsg EOut} {G : Fn → Tw → Prop}

variable (C G) in
open scoped Classical in
/-- **The charge of a mixed call**: a hash call of the adversary one, a classical hash of a
`G`-cell one, every other call (coins, hashes of other cells) none. -/
noncomputable def gCharge : Port romWorld.spec.Port (Caller × RomOracles.Domain) → ℕ
  | .hash _ => 1
  | .call (_, .inl _) => 0
  | .call (_, .inr z) => if IsG C G z then 1 else 0

/-- One step of a charge bound on a command tree: normalize the head, then charge the command. -/
local macro "charge_step" : tactic => `(tactic| (
  (conv => arg 1; whnf);
  refine (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr
    ⟨by first | exact Nat.zero_le _ | exact le_rfl, fun _ ↦ ?_⟩))

/-- **The read program pays the mixed charge**: a mixed program within the charge `gCharge`
has a read program within the charge `κG`. -/
theorem isChargeBound_readProg {Ω : QReg → Type} {A : QReg}
    {x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) Ω A} {n : ℕ}
    (hx : IFreeM.IsChargeBound x (cmdCharge (gCharge C G)) n) :
    IFreeM.IsChargeBound (readProg C G x) (portCharge (κG C G)) n := by
  unfold readProg
  rw [← IFreeM.substitute_toSubstitution, Quantum.Xmss.Assembly.substitute_substitute]
  refine IFreeM.IsChargeBound.substitute _ (fun A c ↦ ?_) hx
  rcases c with o | ⟨p | ⟨tag, n | z⟩, E, ℓ⟩
  · charge_step
    exact IFreeM.isChargeBound_pure _ _
  · charge_step
    exact IFreeM.isChargeBound_pure _ _
  · charge_step
    charge_step
    exact IFreeM.isChargeBound_pure _ _
  · charge_step
    charge_step
    charge_step
    exact IFreeM.isChargeBound_pure _ _

/-- The start memory: no label, an empty log, nothing read, no record, an empty slot. -/
def mem₀ : Mem :=
  (∅, fun _ ↦ none, fun _ ↦ false, fun _ ↦ none, none)

theorem setup_noHash [SampleableType Par] :
    Common.QueryCostAtMost (smTcrIn romWorld C D G).setup hashW 0 :=
  Common.isWeightBound_liftM_probComp hashW (fun _ ↦ rfl) ($ᵗ Par)

/-- **A win of the read program of the SM-TCR-C game is in the event `BadR`.** -/
theorem evalDistMap_le_eventWeight_smTcrIn [SampleableType Par] (hs : GSep C G)
    (hinj : ∀ l P t, (C.layout l P t).Injective) (htw : D.TweakSeparated C)
    (hlen : C.LengthLe maxLen) {Q : Type} {R : OracleSpec.{0, 0} Q} {St S0 F : Type}
    (pre : Unit → OracleComp (romWorld.Oracles + TcrSpec Par Tw Fn Msg Out EFn EMsg EOut) S0)
    (adv : Unit → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : Unit → S0 → St)
    (σ : Unit → HHandler romWorld R (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut) St)
    (post : Unit → S0 → F → St →
      OracleComp (romWorld.Oracles + TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)
        (Σ l, Tw × Msg l)) :
    (runtime2 HashOutput HashDomain mem₀).evalDistMap .instruments
        (readProg C G (mixGame (smTcrIn romWorld C D G) pre adv st0 σ post)) (SubState.basis ())
        (fun p ↦ p.2.2) {true} ≤
      (runtime2 HashOutput HashDomain mem₀).eventWeight .instruments (hwProjector (BadR C G))
        (readProg C G (mixGame (smTcrIn romWorld C D G) pre adv st0 σ post))
        ((SubState.basis ()).matrix ⊗ₖ (runtime2 HashOutput HashDomain mem₀).init.matrix) := by
  have hred : ∀ (P : Par) log μ i y μ', LiveInv C D G P log μ →
      (y, μ') ∈ support ((liveImpl rl (upd C G .red) i).run μ) → LiveInv C D G P log μ' :=
    fun _ _ _ _ _ _ hI h ↦ liveInv_red hI h
  have hans : ∀ (P : Par) log μ q' a μ', LiveInv C D G P log μ →
      LiveRun rl (upd C G .answer) ((smTcrIn romWorld C D G).answer P q') μ a μ' →
      LiveInv C D G P (log ++ [⟨q', a⟩]) μ' :=
    fun _ _ _ q' _ _ hI h ↦ liveInv_answer hs htw hlen q' hI h
  have hx := modedP_mixGame (upd C G) rl (smTcrIn romWorld C D G) pre adv st0 σ post mem₀
    (fun P μ ↦ LiveInv C D G P [] μ)
    (fun s μ h ↦ by
      rw [liveRun_noHash _ setup_noHash h]
      rintro m hm
      cases hm
      refine ⟨rfl, fun _ _ hv ↦ absurd hv (by simp [mem₀, Mem.recs]), fun _ e he ↦ ?_⟩
      simp [tcrTargets] at he)
    (fun P _ s μ ↦ LiveInv C D G P s.2 μ)
    (fun s μ hμ a μ' h ↦
      liveRedRun_inv _ (LiveInv C D G s) (hred s) (hans s) _ _ _ a μ' hμ h)
    (fun s _ _ _ _ _ hμ r μ' h ↦
      liveRedRun_inv _ (LiveInv C D G s) (hred s) (hans s) _ _ _ r μ' hμ h)
    (fun P r μ ↦ LiveInv C D G P r.2 μ)
    (fun s _ _ _ _ _ hμ r μ' h ↦
      liveRedRun_inv _ (LiveInv C D G s) (hred s) (hans s) _ _ _ r μ' hμ h)
    (fun b μ ↦ b = true → ∀ m, μ = some m → m ∈ Won C G)
    (fun s r μ hμ b μ' h hb ↦ by
      subst hb
      exact won_of_judge hs hinj htw hlen r.1 hμ h)
  exact evalDistMap_le_eventWeight_moded rl id mem₀ (fun _ ↦ rfl) (fun _ _ h ↦ h)
    (fun _ _ _ _ ↦ rfl) (BadR C G) (Won C G)
    (fun s hs' ↦ by
      obtain ⟨z, y, h1, h2⟩ := hs'
      exact Or.inr ⟨z, y, h1, h2⟩) _ (some mem₀) rfl
    (modedP_toReads (upd C G) rl (fun c z ↦ recordsAt_upd c z)
      (fin := fun p μ ↦ p.2.2 = true → ∀ m, μ = some m → m ∈ Won C G)
      (fun _ _ m hm ↦ by cases hm) _ (some mem₀) hx)
    (fun _ _ hf hp m hm ↦ hf hp m hm)

open scoped Classical in
/-- **The QROM bound of the restricted SM-TCR-C game for a straight-line reduction.** Let the
target collection `C` be `G`-separated (an input with the bytes of an input at a tweak of `G` has
its parameter and tweak), injective in the message at every function, parameter and tweak, every
input at most `maxLen` bytes, the evaluation collection `D` tweak-separated from `C`, and every
fiber of `C.trunc` of at most `F` values. Let the reduction ask the challenger only before its
own hashes (`ChalFirst`), and its handler and output never. If the mixed game is within `n`
calls of the charge `gCharge` (the adversary's hash calls and the classical hashes of `G`-cells;
coins and hashes of other cells are free), the average winning probability over the tables is
at most `n² (2 √(F/N) + √((F + 2)/N))²`, `N = 2^256`. -/
theorem probAvg_smTcrIn_slRed_le [SampleableType Par] (hs : GSep C G)
    (hinj : ∀ l P t, (C.layout l P t).Injective) (htw : D.TweakSeparated C)
    (hlen : C.LengthLe maxLen) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ C.trunc y = o).card ≤ F)
    {Q : Type} {R : OracleSpec.{0, 0} Q} {St S0 F' : Type}
    (pre : Unit → OracleComp (romWorld.Oracles + TcrSpec Par Tw Fn Msg Out EFn EMsg EOut) S0)
    (adv : Unit → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F')
    (st0 : Unit → S0 → St)
    (σ : Unit → HHandler romWorld R (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut) St)
    (post : Unit → S0 → F' → St →
      OracleComp (romWorld.Oracles + TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)
        (Σ l, Tw × Msg l))
    (hpre : ∀ p, ChalFirst (pre p)) (hσ : ∀ p st q, Common.QueryCostAtMost (σ p st q) chalW 0)
    (hpost : ∀ p a f st, Common.QueryCostAtMost (post p a f st) chalW 0) {n : ℕ}
    (hn : IFreeM.IsChargeBound (mixGame (smTcrIn romWorld C D G) pre adv st0 σ post)
      (cmdCharge (gCharge C G)) n) :
    romWorld.probAvg ((smTcrIn romWorld C D G).game fun p ↦
        slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) ≤
      (n : ℝ≥0∞) ^ 2 * ENNReal.ofReal (gradeEta HashOutput F) :=
  (probAvg_game_slRed_le_hw (smTcrIn romWorld C D G) pre adv st0 σ post (upd C G) mem₀).trans
    ((evalDistMap_le_eventWeight_smTcrIn hs hinj htw hlen pre adv st0 σ post).trans
      (eventWeight_badR_le hs hF mem₀ rfl (fun _ ↦ rfl) (fun _ ↦ rfl) _
        (modedP_mixGame_phase _ pre adv st0 σ post setup_noHash hpre hσ hpost)
        (isChargeBound_readProg hn)))

end main

end Quantum.StdModel.Qrom.Tcr

end
