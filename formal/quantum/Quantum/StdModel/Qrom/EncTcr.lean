module

public import Quantum.StdModel.Qrom.Moded
public import Quantum.StdModel.Sphincs.PropsIn

@[expose] public section

/-!
# EncTCR+C in the QROM

The QROM bound of the restricted EncTCR+C game `Props.encTcrCtrIn W e C G` for a straight-line
reduction whose challenger calls are all in its setup.

* **Cells** (`cellOf`, `IsGTw`, `encTw`): the encoding input of trial `c` of `(P, T, M)`; an input
  at a tweak of `G` with a counter below the limit has a unique tweak under the separation
  `EncSep`, its class.
* **The memory** (`TMem`): the log of every read's outcome, the cells the challenger read, the
  selected digests (the codeword reads of the challenger at the cells of `G`), the judge's hit and
  the number of charged reads (reads of the other callers at encoding cells of `G` the challenger
  did not read).
* **The event**: a cell of a class, not read by the challenger, whose value has the truncation of
  the unique selected cell of its class (`tgt`, `CellTargetBad`), or the judge's hit (`FlagBad`):
  `Bad = CellTargetBad tgt ∪ FlagBad`.
* **The calls**: the adversary's calls cost `√(6 F/N)` each, the charged reads
  `√(gradeEta F)` each; the challenger's answers (all before the adversary's first call and before
  any other read of an encoding cell of `G`), the reads off the classes and the re-reads of cells
  the challenger read cost nothing.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.StdModel.Qrom.EncTcr

open Quantum Quantum.Qrom Quantum.Sponge Props HashSig

/-! ## Encoding cells at the tweaks of `G` -/

section cells

variable {Par Tw Msg Dig : Type} (e : CtrEnc Par Tw Msg Dig) (G : Tw → Prop)

/-- The cell of the trial `c` of the message `m` at `(P, t)`. -/
def cellOf (P : Par) (t : Tw) (m : Msg) (c : ℕ) : Option HashDomain :=
  encodeInput (e.hash.layout () P t (m, c))

/-- `x` is the cell of a trial below the limit at the tweak `t` of `G`. -/
def IsGTw (x : HashDomain) (t : Tw) : Prop :=
  G t ∧ ∃ P m c, c < e.limit ∧ cellOf e P t m c = some x

open scoped Classical in
/-- **The class of a cell**: its tweak of `G`, if it is the cell of a trial below the limit at
a tweak of `G`. -/
noncomputable def encTw (x : HashDomain) : Option Tw :=
  if h : ∃ t, IsGTw e G x t then some h.choose else none

/-- **Separation at the tweaks of `G`**: an encoding input with the bytes of an input at a tweak of
`G` has its tweak, under any parameter. -/
def EncSep : Prop :=
  ∀ P t mc P' t' mc', G t → e.hash.layout () P' t' mc' = e.hash.layout () P t mc → t' = t

variable {e G}

theorem isGTw_of_encTw {x : HashDomain} {t : Tw} (h : encTw e G x = some t) :
    IsGTw e G x t := by
  unfold encTw at h
  split_ifs at h with hx
  cases h
  exact hx.choose_spec

theorem isGTw_unique (hs : EncSep e G) {x : HashDomain} {t t' : Tw} (h : IsGTw e G x t)
    (h' : IsGTw e G x t') : t' = t := by
  obtain ⟨hG, P, m, c, -, hx⟩ := h
  obtain ⟨-, P', m', c', -, hx'⟩ := h'
  exact hs P t (m, c) P' t' (m', c') hG (encodeInput_injective hx' hx)

theorem encTw_eq_some (hs : EncSep e G) {x : HashDomain} {t : Tw} (h : IsGTw e G x t) :
    encTw e G x = some t := by
  unfold encTw
  split_ifs with hx
  · exact congrArg some (isGTw_unique hs h hx.choose_spec)
  · exact absurd ⟨t, h⟩ hx

end cells

/-! ## The memory and the event -/

section memory

variable (n : ℕ)

/-- **The memory of the read program**: the log of every read's outcome, the cells the
challenger read, the selected digests, the judge's hit and the number of charged reads (up to
`n + 1`). -/
abbrev TMem :=
  (HashDomain → Option HashOutput) × (HashDomain → Bool) × (HashDomain → Option HashOutput) ×
    Bool × Fin (n + 2)

/-- The memory with the (unused) label of the record ports. -/
abbrev Mem :=
  Finset Empty × TMem n

/-- Decidable equality of the logs. -/
instance (priority := high) instDecidableEqLog : DecidableEq (HashDomain → Option HashOutput) :=
  Fintype.decidablePiFintype

/-- Decidable equality of the cells read. -/
instance (priority := high) instDecidableEqAx : DecidableEq (HashDomain → Bool) :=
  Fintype.decidablePiFintype

variable {n}

/-- The log of a memory. -/
def Mem.log (m : Mem n) : HashDomain → Option HashOutput :=
  m.2.1

/-- The cells the challenger read. -/
def Mem.ax (m : Mem n) : HashDomain → Bool :=
  m.2.2.1

/-- The selected digests. -/
def Mem.sel (m : Mem n) : HashDomain → Option HashOutput :=
  m.2.2.2.1

/-- The judge's hit. -/
def Mem.flag (m : Mem n) : Bool :=
  m.2.2.2.2.1

/-- The number of charged reads. -/
def Mem.cnt (m : Mem n) : Fin (n + 2) :=
  m.2.2.2.2.2

/-- **The start memory**: nothing logged, read or selected. -/
def mem₀ : Mem n :=
  (∅, fun _ ↦ none, fun _ ↦ false, fun _ ↦ none, false, 0)

end memory

section events

variable {Par Tw Msg Dig : Type} (e : CtrEnc Par Tw Msg Dig) (G : Tw → Prop) (n : ℕ)

/-- **The target of cell `x`**: for a cell of a class not read by the challenger, the values with
the truncation of the unique selected cell of its class, when that cell is another one. -/
def tgt (_W : Hw HashOutput HashDomain) (m : Mem n) (x : HashDomain) : Set HashOutput :=
  {y | m.ax x = false ∧ encTw e G x ≠ none ∧ ∃ z w, m.sel z = some w ∧ z ≠ x ∧
    encTw e G z = encTw e G x ∧
    (∀ z', (m.sel z').isSome → encTw e G z' = encTw e G x → z' = z) ∧
    e.hash.trunc y = e.hash.trunc w}

/-- **The judge's hit.** -/
def FlagBad : Set (RomReg HashDomain HashOutput (Mem n)) :=
  {s | s.2.2.flag = true}

/-- **The event.** -/
def Bad : Set (RomReg HashDomain HashOutput (Mem n)) :=
  CellTargetBad (tgt e G n) ∪ FlagBad n

/-- Membership in `Bad`, decided classically. -/
noncomputable instance instDecidablePredBad : DecidablePred (· ∈ Bad e G n) :=
  fun _ ↦ Classical.propDecidable _

variable {e G n}

open scoped Classical in
/-- **A target has at most `F` values**, `F` a bound on the fibers of the truncation. -/
theorem card_tgt_le {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F)
    (W : Hw HashOutput HashDomain) (m : Mem n) (x : HashDomain) :
    (Finset.univ.filter fun y ↦ y ∈ tgt e G n W m x).card ≤ F := by
  by_cases h : ∃ z w, m.sel z = some w ∧
      (∀ z', (m.sel z').isSome → encTw e G z' = encTw e G x → z' = z) ∧
      encTw e G z = encTw e G x
  · obtain ⟨z₀, w₀, hw₀, hu₀, -⟩ := h
    refine (Finset.card_le_card fun y hy ↦ ?_).trans (hF (e.hash.trunc w₀))
    obtain ⟨-, -, z, w, hw, -, hc, -, hy⟩ := (Finset.mem_filter.1 hy).2
    have hz : z = z₀ := hu₀ z (by rw [hw]; rfl) hc
    subst hz
    rw [hw₀] at hw
    cases hw
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩
  · rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun y _ hy ↦ ?_)]
    · exact Nat.zero_le F
    obtain ⟨-, -, z, w, hw, -, hc, hu, -⟩ := hy
    exact h ⟨z, w, hw, hu, hc⟩

/-- **Every slice of the event is upward closed.** -/
theorem upClosed_slice_bad (W : Hw HashOutput HashDomain) (m : Mem n) :
    UpClosed (slice (Bad e G n) W m) where
  h Db hDb z u hz := by
    rcases hDb with h | h
    · exact Or.inl ((upClosed_slice_cellTargetBad (tgt := tgt e G n) W m).h Db h z u hz)
    · exact Or.inr h
  k Db hDb _ _ _ := hDb
  k' Db hDb _ _ _ := hDb

/-- **The start is outside the event** when nothing is selected and no hit. -/
theorem start_not_mem_bad (m₀ : Mem n) (hs : ∀ x, m₀.sel x = none) (hf : m₀.flag = false) :
    (((Database.empty, Database.empty, Database.empty), hwEmpty HashOutput HashDomain, m₀) :
      RomReg HashDomain HashOutput (Mem n)) ∉ Bad e G n := by
  rintro (⟨x, y, -, hy⟩ | h)
  · obtain ⟨-, -, z, w, hw, -⟩ := hy
    rw [hs z] at hw
    cases hw
  · change m₀.flag = true at h
    rw [hf] at h
    cases h

open scoped Classical in
/-- **The fresh bound of every slice**: `F / |Y|`, `F` a bound on the fibers of the truncation. -/
theorem freshBound_slice_bad {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F)
    (W : Hw HashOutput HashDomain) (m : Mem n) (t : ℕ) :
    FreshBound (slice (Bad e G n) W m) t ((F : ℝ≥0∞) / Fintype.card HashOutput) where
  h Db hDb h₁ h₂ h₃ z hz := by
    have hc := (freshBound_slice_cellTargetBad (tgt := tgt e G n) W m (ε := (F : ℝ≥0∞) /
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

/-- The target reads only the cells read by the challenger and the selections. -/
theorem tgt_congr {m m' : Mem n} (hax : m'.ax = m.ax) (hsel : m'.sel = m.sel)
    (W W' : Hw HashOutput HashDomain) : tgt e G n W' m' = tgt e G n W m := by
  funext x
  simp only [tgt, hax, hsel]

/-- Recording a value outside the target of an empty, unhardwired cell keeps the event. -/
theorem bad_record_iff {s : RomReg HashDomain HashOutput (Mem n)} {z : HashDomain}
    {v : HashOutput} (hw : s.2.1.1 z = none) (hv : v ∉ tgt e G n s.2.1 s.2.2 z)
    (a : Option HashOutput) (ha : s.1.1 z = a) (hav : a = none ∨ a = some v) :
    (((Function.update s.1.1 z (some v), s.1.2), s.2) : RomReg HashDomain HashOutput (Mem n)) ∈
      Bad e G n ↔ s ∈ Bad e G n := by
  have hJ : ((((Function.update s.1.1 z (some v), s.1.2), s.2) :
      RomReg HashDomain HashOutput (Mem n)) ∈ FlagBad n ↔ s ∈ FlagBad n) := Iff.rfl
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
theorem mem_bad_of_cell {s : RomReg HashDomain HashOutput (Mem n)} {z : HashDomain}
    {y : HashOutput} (hz : unionH s z = some y) (hy : y ∈ tgt e G n s.2.1 s.2.2 z) :
    s ∈ Bad e G n :=
  Or.inl ⟨z, y, hz, hy⟩

end events

/-! ## The read policies -/

section policy

variable {Par Tw Msg Dig : Type} (e : CtrEnc Par Tw Msg Dig) (G : Tw → Prop) (n : ℕ)

/-- **A charged read**: at a cell of a class the challenger did not read. -/
def Charged (m : Mem n) (z : HashDomain) : Prop :=
  encTw e G z ≠ none ∧ m.ax z = false

/-- The count after one more charged read, saturating at `n + 1`. -/
def bumpCnt (k : Fin (n + 2)) : Fin (n + 2) :=
  ⟨min (k.val + 1) (n + 1), by omega⟩

open scoped Classical in
/-- The count after a read of `z` by another caller than the challenger's answers. -/
noncomputable def cntAfter (m : Mem n) (z : HashDomain) : Fin (n + 2) :=
  if Charged e G n m z then bumpCnt n m.cnt else m.cnt

open scoped Classical in
/-- **The challenger's answers**: log the outcome, mark the cell read, and select a codeword
outcome at a cell of a class. -/
noncomputable def uAns (z : HashDomain) (m : Mem n) (o : Option HashOutput) : Mem n :=
  (m.1, Function.update m.log z o, Function.update m.ax z true,
    if encTw e G z ≠ none ∧ ∃ v, o = some v ∧ e.isCode (e.hash.trunc v) = true then
      Function.update m.sel z o else m.sel, m.flag, m.cnt)

/-- **The reduction's (and the setup's) reads**: log the outcome and count a charged read. -/
noncomputable def uRed (z : HashDomain) (m : Mem n) (o : Option HashOutput) : Mem n :=
  (m.1, Function.update m.log z o, m.ax, m.sel, m.flag, cntAfter e G n m z)

open scoped Classical in
/-- **The judge's read**: log the outcome, count a charged read, and record a hit when the
outcome is in the target of the cell. -/
noncomputable def uJudge (z : HashDomain) (m : Mem n) (o : Option HashOutput) : Mem n :=
  (m.1, Function.update m.log z o, m.ax, m.sel,
    m.flag || decide (∃ y, o = some y ∧ y ∈ tgt e G n (hwEmpty HashOutput HashDomain) m z),
    cntAfter e G n m z)

/-- **The read policies.** -/
noncomputable def upd : Caller → HashDomain → Mem n → Option HashOutput → Mem n
  | .answer => uAns e G n
  | .judge => uJudge e G n
  | .setup => uRed e G n
  | .red => uRed e G n

/-- The log of the memory. -/
def rl (m : Mem n) : HashDomain → Option HashOutput :=
  m.log

/-- **A policy at `z` keeping the targets** of the memory `m`, and raising the hit only with an
outcome in the target of `z`. -/
def KeepsAt (z : HashDomain) (u : Mem n → Option HashOutput → Mem n) (m : Mem n) : Prop :=
  ∀ o, (u m o).ax = m.ax ∧ (u m o).sel = m.sel ∧ (m.flag = true → (u m o).flag = true) ∧
    ((u m o).flag = true → m.flag = true ∨
      ∃ y, o = some y ∧ y ∈ tgt e G n (hwEmpty HashOutput HashDomain) m z)

/-- **The states of the first phase**: no hit, no hardwired cell, and every cell of a class in
the database read by the challenger. -/
def P1 (m : Mem n) (s : RomReg HashDomain HashOutput (Mem n)) : Prop :=
  s.2.2 = m ∧ s.2.1 = hwEmpty HashOutput HashDomain ∧ m.flag = false ∧
    ∀ x, encTw e G x ≠ none → s.1.1 x ≠ none → m.ax x = true

variable {e G n}

theorem recordsAt_upd (c : Caller) (z : HashDomain) :
    RecordsAt (rl (n := n)) z (upd e G n c z) := by
  intro m o
  cases c <;> rfl

theorem upd_ne_answer {c : Caller} (hc : c ≠ .answer) (z : HashDomain) :
    upd e G n c z ≠ upd e G n .answer z := by
  intro h
  have h1 := congrArg (fun m : Mem n ↦ m.ax z) (congrFun (congrFun h mem₀) none)
  cases c <;> simp_all [upd, uRed, uJudge, uAns, Mem.ax, mem₀]

theorem tgt_eq_empty_of_not_charged {m : Mem n} {z : HashDomain} (h : ¬ Charged e G n m z)
    (W : Hw HashOutput HashDomain) : tgt e G n W m z = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ hy ↦ h ⟨hy.2.1, hy.1⟩

open scoped Classical in
theorem keepsAt_upd {c : Caller} (hc : c ≠ .answer) (z : HashDomain) (m : Mem n) :
    KeepsAt e G n z (upd e G n c z) m := by
  intro o
  cases c
  · exact ⟨rfl, rfl, id, Or.inl⟩
  · exact absurd rfl hc
  · refine ⟨rfl, rfl, fun h ↦ ?_, fun h ↦ ?_⟩
    · change (m.flag || _) = true
      rw [h, Bool.true_or]
    · change (m.flag || _) = true at h
      rw [Bool.or_eq_true, decide_eq_true_iff] at h
      exact h
  · exact ⟨rfl, rfl, id, Or.inl⟩

open scoped Classical in
/-- The judge's hit after a read of `z` with value `y`. -/
theorem uJudge_flag (z : HashDomain) (m : Mem n) (y : HashOutput) :
    (uJudge e G n z m (some y)).flag = true ↔
      m.flag = true ∨ y ∈ tgt e G n (hwEmpty HashOutput HashDomain) m z := by
  change (m.flag || _) = true ↔ _
  rw [Bool.or_eq_true, decide_eq_true_iff]
  constructor
  · rintro (h | ⟨y', hy', h⟩)
    · exact Or.inl h
    · obtain rfl := Option.some.inj hy'
      exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨y, rfl, h⟩

/-- **The memory move of a read keeping the targets**: it keeps the event, and enters it only
with an outcome in the target of the read cell. -/
theorem bad_memMove {z : HashDomain} {u : Mem n → Option HashOutput → Mem n}
    (s : RomReg HashDomain HashOutput (Mem n)) (hu : KeepsAt e G n z u s.2.2)
    (o : Option HashOutput) :
    ((s.1, s.2.1, u s.2.2 o) ∈ Bad e G n → s ∈ Bad e G n ∨
      ∃ y, o = some y ∧ y ∈ tgt e G n s.2.1 s.2.2 z) ∧
    (s ∈ Bad e G n → (s.1, s.2.1, u s.2.2 o) ∈ Bad e G n) := by
  obtain ⟨hax, hsel, hf1, hf2⟩ := hu o
  have ht : tgt e G n s.2.1 (u s.2.2 o) = tgt e G n s.2.1 s.2.2 := tgt_congr hax hsel _ _
  constructor
  · rintro (⟨x, y, hxy, hy⟩ | h)
    · exact Or.inl (Or.inl ⟨x, y, hxy, by rw [← ht]; exact hy⟩)
    · rcases hf2 h with h' | ⟨y, hy, hyt⟩
      · exact Or.inl (Or.inr h')
      · exact Or.inr ⟨y, hy, hyt⟩
  · rintro (⟨x, y, hxy, hy⟩ | h)
    · exact Or.inl ⟨x, y, hxy, by change y ∈ tgt e G n s.2.1 (u s.2.2 o) x; rw [ht]; exact hy⟩
    · exact Or.inr (hf1 h)

/-- **A read without target keeping the targets is invisible** to the event. -/
theorem bad_iff_of_read {z : HashDomain} {u : Mem n → Option HashOutput → Mem n}
    {s s' : RomReg HashDomain HashOutput (Mem n)} {o : Option HashOutput}
    (hk : KeepsAt e G n z u s.2.2) (hz : ¬ Charged e G n s.2.2 z)
    (hc : ∀ b, b ≠ z → s'.1.1 b = s.1.1 b) (hW : s'.2.1 = s.2.1) (hm : s'.2.2 = u s.2.2 o) :
    s' ∈ Bad e G n ↔ s ∈ Bad e G n := by
  obtain ⟨hax, hsel, hf1, hf2⟩ := hk o
  have ht : tgt e G n s'.2.1 s'.2.2 = tgt e G n s.2.1 s.2.2 := by
    rw [hm]
    exact tgt_congr hax hsel _ _
  have hz' : ∀ W y, y ∉ tgt e G n W s.2.2 z := fun W y hy ↦ by
    rw [tgt_eq_empty_of_not_charged hz] at hy
    exact hy
  have hx : ∀ x, x ≠ z → unionH s' x = unionH s x := fun x hx ↦ by
    simp only [unionH_apply, hW, hc x hx]
  constructor
  · rintro (⟨x, y, hxy, hy⟩ | h)
    · rw [ht] at hy
      have hxz : x ≠ z := by
        rintro rfl
        exact hz' _ y hy
      exact Or.inl ⟨x, y, by rw [← hx x hxz]; exact hxy, hy⟩
    · change s'.2.2.flag = true at h
      rw [hm] at h
      rcases hf2 h with h' | ⟨y, -, hy⟩
      · exact Or.inr h'
      · exact absurd hy (hz' _ y)
  · rintro (⟨x, y, hxy, hy⟩ | h)
    · have hxz : x ≠ z := by
        rintro rfl
        exact hz' _ y hy
      exact Or.inl ⟨x, y, by rw [hx x hxz]; exact hxy, by rw [ht]; exact hy⟩
    · refine Or.inr ?_
      change s'.2.2.flag = true
      rw [hm]
      exact hf1 h

/-- The states of the first phase are outside the event. -/
theorem not_mem_bad_of_p1 {m : Mem n} {s : RomReg HashDomain HashOutput (Mem n)}
    (h : P1 e G n m s) : s ∉ Bad e G n := by
  obtain ⟨rfl, hW, hf, hax⟩ := h
  rintro (⟨x, y, hxy, hy⟩ | h)
  · obtain ⟨hx, hG, -⟩ := hy
    have h1 : s.1.1 x = some y := by
      simpa [hW, hwEmpty_fst_apply] using hxy
    rw [hax x hG (by rw [h1]; exact Option.some_ne_none y)] at hx
    cases hx
  · change s.2.2.flag = true at h
    rw [hf] at h
    cases h

/-- **An answer keeps the first phase.** -/
theorem p1_uAns {m : Mem n} {s s' : RomReg HashDomain HashOutput (Mem n)} {z : HashDomain}
    {o : Option HashOutput} (h : P1 e G n m s) (hc : ∀ b, b ≠ z → s'.1.1 b = s.1.1 b)
    (hW : s'.2.1 = s.2.1) (hm : s'.2.2 = uAns e G n z m o) : P1 e G n (uAns e G n z m o) s' := by
  obtain ⟨-, hW', hf, hax⟩ := h
  refine ⟨hm, hW.trans hW', hf, fun x hx hd ↦ ?_⟩
  change Function.update m.ax z true x = true
  by_cases hxz : x = z
  · subst hxz
    exact Function.update_self ..
  · rw [Function.update_of_ne hxz]
    exact hax x hx (by rwa [← hc x hxz])

/-- **A read of another caller off the classes keeps the first phase.** -/
theorem p1_read {c : Caller} (hc : c ≠ .answer) {m : Mem n}
    {s s' : RomReg HashDomain HashOutput (Mem n)} {z : HashDomain} (hz : encTw e G z = none)
    {o : Option HashOutput} (h : P1 e G n m s) (hc' : ∀ b, b ≠ z → s'.1.1 b = s.1.1 b)
    (hW : s'.2.1 = s.2.1) (hm : s'.2.2 = upd e G n c z m o) :
    P1 e G n (upd e G n c z m o) s' := by
  obtain ⟨-, hW', hf, hax⟩ := h
  obtain ⟨hax', -, -, hf2⟩ := keepsAt_upd (e := e) (G := G) hc z m o
  have hnc : ¬ Charged e G n m z := fun h ↦ h.1 hz
  refine ⟨hm, hW.trans hW', ?_, fun x hx hd ↦ ?_⟩
  · rcases hb : (upd e G n c z m o).flag with _ | _
    · rfl
    · rcases hf2 hb with h' | ⟨y, -, hy⟩
      · rw [hf] at h'
        cases h'
      · rw [tgt_eq_empty_of_not_charged hnc] at hy
        exact absurd hy (Set.notMem_empty y)
  · rw [hax']
    have hxz : x ≠ z := by
      rintro rfl
      exact hx hz
    exact hax x hx (by rwa [← hc' x hxz])

end policy

/-! ## The price of a call -/

section price

variable {Par Tw Msg Dig : Type} {e : CtrEnc Par Tw Msg Dig} {G : Tw → Prop} {n : ℕ}

open scoped Classical in
/-- **A charged read costs like a sponge call** (`gradeEta`, `F` a bound on the fibers of the
truncation), on a state with no decompressed `⊥` at the cell, if the policy keeps the targets on
its support. -/
theorem tsum_potential_read_bad {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F) {z : HashDomain}
    {u : Mem n → Option HashOutput → Mem n}
    {σ : Matrix (Unit × RomReg HashDomain HashOutput (Mem n))
      (Unit × RomReg HashDomain HashOutput (Mem n)) ℂ}
    (hσ : σ.PosSemidef) (hnb : ReadNoBot (.readH z u) σ)
    (hu : ∀ q, σ q q ≠ 0 → KeepsAt e G n z u q.2.2.2) :
    ∑' r, QuantumRuntime.potential (hwProjector (Bad e G n))
        (MatrixMap.conj (hwReadKraus (.readH z u) r) σ) ≤
      (QuantumRuntime.potential (hwProjector (Bad e G n)) σ ^ (2⁻¹ : ℝ) +
        ENNReal.ofReal (gradeEta HashOutput F * σ.trace.re) ^ (2⁻¹ : ℝ)) ^ 2 := by
  refine tsum_potential_readH_le_sqrt (Bad e G n) z u F
    (Quantum.Xmss.Assembly.upCell_of_upClosed _ (fun W m ↦ upClosed_slice_bad W m) _) hσ hnb
    (fun q hq hw hd ↦ ?_) (fun q hq hw ↦ ?_) (fun q hq hw ↦ ?_) (fun q hq hw hd hm ↦ ?_) <;>
    have hmv := fun (s : RomReg HashDomain HashOutput (Mem n)) (hs : s.2.2 = q.2.2.2) o ↦
      bad_memMove (e := e) (G := G) s (hs ▸ hu q hq) o
  · refine ⟨?_, ?_⟩
    · refine (Finset.card_le_card fun v hv ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩).trans
        (card_tgt_le (G := G) hF q.2.2.1 q.2.2.2 z)
      by_contra hvt
      rcases (Finset.mem_filter.1 hv).2 with h | ⟨a, h⟩
      · exact h (bad_record_iff hw hvt none hd (Or.inl rfl))
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
      have h1 := bad_record_iff (e := e) (G := G) hw hvt none hd (Or.inl rfl)
      have h2 : ((((Function.update q.2.1.1 z (some v), q.2.1.2), q.2.2.1,
          u q.2.2.2 (some v))) : RomReg HashDomain HashOutput (Mem n)) ∈ Bad e G n ↔
          (((Function.update q.2.1.1 z (some v), q.2.1.2), q.2.2) :
            RomReg HashDomain HashOutput (Mem n)) ∈ Bad e G n := by
        refine ⟨fun h ↦ ?_,
          (hmv ((Function.update q.2.1.1 z (some v), q.2.1.2), q.2.2) rfl (some v)).2⟩
        rcases (hmv ((Function.update q.2.1.1 z (some v), q.2.1.2), q.2.2) rfl (some v)).1 h
          with h3 | ⟨y, hy, hyt⟩
        · exact h3
        · cases hy
          exact absurd hyt hvt
      exact (Finset.mem_filter.1 hv).2 (h2.trans h1)
  · rintro ⟨hq, h⟩
    rcases (hmv q.2 rfl (q.2.1.1 z)).1 h with h' | ⟨y, hy, hyt⟩
    · exact hq h'
    · refine hq (mem_bad_of_cell (z := z) ?_ hyt)
      change (q.2.2.1.1 z).or (q.2.1.1 z) = some y
      rw [hw, hy]
      rfl
  · rintro ⟨hq, h⟩
    rcases (hmv q.2 rfl (q.2.2.1.1 z)).1 h with h' | ⟨y, hy, hyt⟩
    · exact hq h'
    · refine hq (mem_bad_of_cell (z := z) ?_ hyt)
      change (q.2.2.1.1 z).or (q.2.1.1 z) = some y
      rw [hy]
      rfl
  · by_contra hq
    obtain ⟨a, h⟩ := hm
    refine h ⟨fun h2 ↦ ?_,
      (hmv ((Function.update q.2.1.1 z a, q.2.1.2), q.2.2) rfl (q.2.1.1 z)).2⟩
    rcases (hmv ((Function.update q.2.1.1 z a, q.2.1.2), q.2.2.1, q.2.2.2) rfl
      (q.2.1.1 z)).1 h2 with h3 | ⟨y, hy, hyt⟩
    · exact h3
    · refine absurd (mem_bad_of_cell (s := q.2) (z := z) ?_ hyt) hq
      change (q.2.2.1.1 z).or (q.2.1.1 z) = some y
      rw [hw, hy]
      rfl

open scoped Classical in
/-- **A sponge call costs `√(6 F / N)`** for the event `Bad`. -/
theorem potential_sponge_bad_le {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F) (m₀ : Mem n)
    (i : SpongePort)
    {σ : Matrix (spongeIn HashOutput HashDomain i × RomReg HashDomain HashOutput (Mem n))
      (spongeIn HashOutput HashDomain i × RomReg HashDomain HashOutput (Mem n)) ℂ}
    (hσ : σ.PosSemidef) :
    QuantumRuntime.potential (hwProjector (Bad e G n))
        (MatrixMap.conj ((spongeHardwired HashOutput HashDomain (hwEmpty HashOutput HashDomain)
          m₀).U i) σ) ^ (2⁻¹ : ℝ) ≤
      QuantumRuntime.potential (hwProjector (Bad e G n)) σ ^ (2⁻¹ : ℝ) +
        (6 * ((F : ℝ≥0∞) / Fintype.card HashOutput) * ENNReal.ofReal σ.trace.re) ^
          (2⁻¹ : ℝ) := by
  have hεtop : (F : ℝ≥0∞) / Fintype.card HashOutput ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top F)
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hg : ∀ D : DbReg HashOutput HashDomain,
      dbGrade D ≤ Fintype.card HashDomain + Fintype.card HashOutput := fun D ↦ by
    have h₁ : D.1.size ≤ Fintype.card HashDomain := Finset.card_le_univ _
    have h₂ : D.2.1.size ≤ Fintype.card HashOutput := Finset.card_le_univ _
    have h₃ : D.2.2.size ≤ Fintype.card HashOutput := Finset.card_le_univ _
    unfold dbGrade
    omega
  exact rpow_inv_two_potential_spongeHardwired_le (Bad e G n)
    (fun W m ↦ upClosed_slice_bad W m) hεtop (fun W m ↦ freshBound_slice_bad hF W m _)
    (hwEmpty HashOutput HashDomain) m₀ i hσ
    (N := Fintype.card HashDomain + Fintype.card HashOutput) (fun _ _ _ ↦ ⟨hg _, hg _⟩)

end price


/-! ## The modes of the read program -/

section modes

variable {Par Tw Msg Dig : Type} (e : CtrEnc Par Tw Msg Dig) (G : Tw → Prop) (n : ℕ)

/-- The cells of the classes: the first phase ends at another caller's read of one. -/
def Gc (z : HashDomain) : Prop :=
  encTw e G z ≠ none

/-- **Doomed modes**: a dead memory or `n + 1` charged reads. -/
def Doom (μ : Option (Mem n) × Bool) : Prop :=
  μ.1.elim True fun m ↦ m.cnt.val = n + 1

/-- **The budget of a mode**: the charged reads left. -/
def bud (μ : Option (Mem n) × Bool) : ℕ :=
  μ.1.elim 0 fun m ↦ n - m.cnt.val

/-- The adversary's calls. -/
def κA (i : (hwSpec HashOutput HashDomain (Mem n)).Port) : ℕ :=
  if hwCls i then 0 else 1

open scoped Classical in
/-- **The charged reads.** -/
noncomputable def κB : Option (Mem n) × Bool → (hwSpec HashOutput HashDomain (Mem n)).Port → ℕ
  | (some m, _), .inl (.inr (.readH z u)) =>
      if Charged e G n m z ∧ u ≠ upd e G n .answer z then 1 else 0
  | _, _ => 0

/-- **The invariant of the first phase.** -/
def CInv (μ : Option (Mem n) × Bool) : Set (RomReg HashDomain HashOutput (Mem n)) :=
  {s | ∀ m, μ.1 = some m → μ.2 = true → P1 e G n m s}

/-- The calls the modes allow. -/
abbrev okR : Option (Mem n) × Bool → (hwSpec HashOutput HashDomain (Mem n)).Port → Prop :=
  okD2 (upd e G n) (rl (n := n))

/-- The modes after a call. -/
noncomputable abbrev nxR : (μ : Option (Mem n) × Bool) →
    (i : (hwSpec HashOutput HashDomain (Mem n)).Port) →
      (hwSpec HashOutput HashDomain (Mem n)).Result i → Option (Mem n) × Bool :=
  nxD2 (Gc e G) (upd e G n) (rl (n := n))

variable {e G n}

theorem cnt_upd (c : Caller) (z : HashDomain) (m : Mem n) (o : Option HashOutput) :
    (upd e G n c z m o).cnt = if c = .answer then m.cnt else cntAfter e G n m z := by
  cases c <;> rfl

/-- A live read moves the memory by its policy with the outcome. -/
theorem nxD_live {m m' : Mem n} {z : HashDomain} {u : Mem n → Option HashOutput → Mem n}
    {r : Option HashOutput × Mem n}
    (h : nxD (rl (n := n)) (some m) (.inl (.inr (.readH z u))) r = some m') :
    ∃ v, r.1 = some v ∧ m' = u m (some v) := by
  rcases r with ⟨_ | v, mm⟩
  · cases h
  · refine ⟨v, rfl, ?_⟩
    change stepRd (rl (n := n)) u z (some m) v = some m' at h
    unfold stepRd at h
    dsimp only at h
    split_ifs at h
    exact (Option.some.inj h).symm

/-- The calls of a live mode: sponge calls and reads of the policies. -/
theorem okR_live {m : Mem n} {ph : Bool} {i : (hwSpec HashOutput HashDomain (Mem n)).Port}
    (hi : okR e G n (some m, ph) i) :
    (∃ p, i = .inl (.inl p)) ∨
      ∃ z c, i = .inl (.inr (.readH z (upd e G n c z))) ∧ (c = .answer → ph = true) := by
  rcases hi.2 with h | ⟨hph, hp⟩
  · cases h
  rcases i with (p | c) | c
  · exact Or.inl ⟨p, rfl⟩
  · cases c with
    | readH z u =>
      obtain ⟨c, rfl⟩ := hp
      exact Or.inr ⟨z, c, rfl, fun hc ↦ hph (by rw [hc])⟩
    | readK _ _ => exact absurd hp id
    | readK' _ _ => exact absurd hp id
  · exact absurd hp id

theorem doom_nx {μ : Option (Mem n) × Bool} {i : (hwSpec HashOutput HashDomain (Mem n)).Port}
    (r : (hwSpec HashOutput HashDomain (Mem n)).Result i) (hi : okR e G n μ i)
    (hd : Doom n μ) : Doom n (nxR e G n μ i r) := by
  rcases μ with ⟨_ | m, ph⟩
  · change (nxD (rl (n := n)) none i r).elim True _
    rw [nxD_none]
    trivial
  change m.cnt.val = n + 1 at hd
  rcases okR_live hi with ⟨p, rfl⟩ | ⟨z, c, rfl, -⟩
  · change (nxD (rl (n := n)) (some m) _ r).elim True _
    rw [nxD_sponge]
    exact hd
  · change (nxD (rl (n := n)) (some m) _ r).elim True _
    rcases hx : nxD (rl (n := n)) (some m) (.inl (.inr (.readH z (upd e G n c z)))) r with
      _ | m'
    · trivial
    obtain ⟨v, -, rfl⟩ := nxD_live hx
    change (upd e G n c z m (some v)).cnt.val = n + 1
    rw [cnt_upd]
    split_ifs
    · exact hd
    · unfold cntAfter
      split_ifs
      · change min (m.cnt.val + 1) (n + 1) = n + 1
        omega
      · exact hd

theorem bud_nx {μ : Option (Mem n) × Bool} {i : (hwSpec HashOutput HashDomain (Mem n)).Port}
    (r : (hwSpec HashOutput HashDomain (Mem n)).Result i) (hi : okR e G n μ i)
    (hd : ¬ Doom n (nxR e G n μ i r)) :
    κB e G n μ i + bud n (nxR e G n μ i r) ≤ bud n μ := by
  rcases μ with ⟨_ | m, ph⟩
  · exact absurd (by
      change (nxD (rl (n := n)) none i r).elim True _
      rw [nxD_none]
      trivial) hd
  rcases okR_live hi with ⟨p, rfl⟩ | ⟨z, c, rfl, -⟩
  · change 0 + (nxD (rl (n := n)) (some m) _ r).elim 0 _ ≤ n - m.cnt.val
    rw [nxD_sponge]
    simp
  · change ¬ (nxD (rl (n := n)) (some m) _ r).elim True _ at hd
    change _ + (nxD (rl (n := n)) (some m) _ r).elim 0 _ ≤ n - m.cnt.val
    rcases hx : nxD (rl (n := n)) (some m) (.inl (.inr (.readH z (upd e G n c z)))) r with
      _ | m'
    · rw [hx] at hd
      exact absurd trivial hd
    rw [hx] at hd
    obtain ⟨v, -, rfl⟩ := nxD_live hx
    change ¬ (upd e G n c z m (some v)).cnt.val = n + 1 at hd
    change κB e G n (some m, ph) _ + (n - (upd e G n c z m (some v)).cnt.val) ≤ n - m.cnt.val
    rw [cnt_upd] at hd ⊢
    have hm := m.cnt.isLt
    by_cases hca : c = .answer
    · subst hca
      simp only [κB, ne_eq, not_true_eq_false, and_false, ↓reduceIte, zero_add, le_refl]
    · have hu : upd e G n c z ≠ upd e G n .answer z := upd_ne_answer hca z
      simp only [hca, ↓reduceIte, cntAfter] at hd ⊢
      by_cases hch : Charged e G n m z
      · simp only [κB, hch, hu, ne_eq, not_false_eq_true, and_self, ↓reduceIte] at hd ⊢
        change ¬ min (m.cnt.val + 1) (n + 1) = n + 1 at hd
        change 1 + (n - min (m.cnt.val + 1) (n + 1)) ≤ n - m.cnt.val
        omega
      · simp only [κB, hch, false_and, ↓reduceIte, zero_add, le_refl]

open scoped Classical in
/-- **The first phase's invariant is kept** by every allowed call. -/
theorem cInv_step (m₀ : Mem n) {μ : Option (Mem n) × Bool}
    {i : (hwSpec HashOutput HashDomain (Mem n)).Port}
    (r : (hwSpec HashOutput HashDomain (Mem n)).Result i) (hi : okR e G n μ i)
    {σ : Matrix ((hwSpec HashOutput HashDomain (Mem n)).In i × HwReg HashOutput HashDomain (Mem n))
      ((hwSpec HashOutput HashDomain (Mem n)).In i × HwReg HashOutput HashDomain (Mem n)) ℂ}
    (hσ : QuerySupportedOn (fun m : (hwSpec HashOutput HashDomain (Mem n)).In i ×
      HwReg HashOutput HashDomain (Mem n) ↦ m.2) (CInv e G n μ) σ) :
    QuerySupportedOn (fun m : (hwSpec HashOutput HashDomain (Mem n)).Out i ×
      HwReg HashOutput HashDomain (Mem n) ↦ m.2) (CInv e G n (nxR e G n μ i r))
      (((Quantum.Xmss.Hybrid.runtime2 HashOutput HashDomain m₀).step i).branch r σ) := by
  have hall : (∀ s, s ∈ CInv e G n (nxR e G n μ i r)) →
      QuerySupportedOn (fun m : (hwSpec HashOutput HashDomain (Mem n)).Out i ×
        HwReg HashOutput HashDomain (Mem n) ↦ m.2) (CInv e G n (nxR e G n μ i r))
        (((Quantum.Xmss.Hybrid.runtime2 HashOutput HashDomain m₀).step i).branch r σ) :=
    fun h a b _ ↦ ⟨h _, h _⟩
  rcases μ with ⟨_ | m, ph⟩
  · refine hall fun s m' hm' _ ↦ ?_
    change nxD (rl (n := n)) none i r = some m' at hm'
    rw [nxD_none] at hm'
    cases hm'
  rcases okR_live hi with ⟨p, rfl⟩ | ⟨z, c, rfl, hc⟩
  · refine hall fun s m' _ hph ↦ ?_
    change phStep (some m) (nxD (rl (n := n)) (some m) _ r) ph false = true at hph
    rw [nxD_sponge] at hph
    cases hph
  rw [Quantum.Xmss.Hybrid.runtime2_branch]
  refine QuerySupportedOn.conj hσ fun q' q hK hq m' hm' hph ↦ ?_
  obtain ⟨hcz, -, hW, hmem⟩ := hwReadKraus_readH_ne_zero z _ r hK
  change nxD (rl (n := n)) (some m) _ r = some m' at hm'
  change phStep (some m) (nxD (rl (n := n)) (some m) _ r) ph
    (nxPhH (Gc e G) (upd e G n) ph _ r) = true at hph
  rw [hm'] at hph
  change nxPhH (Gc e G) (upd e G n) ph (.inl (.inr (.readH z (upd e G n c z)))) r = true at hph
  obtain ⟨v, hv, rfl⟩ := nxD_live hm'
  simp only [nxPhH] at hph
  split_ifs at hph with hg
  have hq1 := hq m rfl hph
  rw [hv] at hmem
  rw [hq1.1] at hmem
  by_cases hca : c = .answer
  · subst hca
    exact p1_uAns hq1 hcz hW hmem
  · have hz : encTw e G z = none := by
      by_contra hz
      exact hg ⟨hz, upd_ne_answer hca z⟩
    exact p1_read hca hz hq1 hcz hW hmem

/-- `x ≤ (√x + a)²`. -/
theorem le_sq_rpow_add (x a : ℝ≥0∞) : x ≤ (x ^ (2⁻¹ : ℝ) + a) ^ 2 := by
  calc x = (x ^ (2⁻¹ : ℝ)) ^ 2 := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ (x ^ (2⁻¹ : ℝ) + a) ^ 2 := by gcongr; exact le_self_add

/-- `√x ≤ b` gives `x ≤ b²`. -/
theorem le_sq_of_rpow_le {x b : ℝ≥0∞} (h : x ^ (2⁻¹ : ℝ) ≤ b) : x ≤ b ^ 2 := by
  calc x = (x ^ (2⁻¹ : ℝ)) ^ 2 := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ b ^ 2 := by gcongr

open scoped Classical in
/-- **The price of every allowed call** from a live mode: `√(6 F/N)` for the adversary's calls,
`√(gradeEta F)` for the charged reads, nothing for the others. -/
theorem tsum_potential_step_le {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F) (m₀ : Mem n)
    (μ : Option (Mem n) × Bool) (i : (hwSpec HashOutput HashDomain (Mem n)).Port)
    (σ : Matrix ((hwSpec HashOutput HashDomain (Mem n)).In i × HwReg HashOutput HashDomain (Mem n))
      ((hwSpec HashOutput HashDomain (Mem n)).In i × HwReg HashOutput HashDomain (Mem n)) ℂ)
    (hi : okR e G n μ i) (hd : ¬ Doom n μ) (hσ : σ.PosSemidef)
    (hs : DSupp (rl (n := n)) Prod.fst μ σ)
    (hc : QuerySupportedOn (fun m : (hwSpec HashOutput HashDomain (Mem n)).In i ×
      HwReg HashOutput HashDomain (Mem n) ↦ m.2) (CInv e G n μ) σ) :
    ∑' r, (if Doom n (nxR e G n μ i r) then 0 else
        QuantumRuntime.potential (hwProjector (Bad e G n))
          (((Quantum.Xmss.Hybrid.runtime2 HashOutput HashDomain m₀).step i).branch r σ)) ≤
      (QuantumRuntime.potential (hwProjector (Bad e G n)) σ ^ (2⁻¹ : ℝ) +
        κA n i * (6 * ((F : ℝ≥0∞) / Fintype.card HashOutput) *
          ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ) +
        κB e G n μ i * (ENNReal.ofReal (gradeEta HashOutput F) *
          ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ)) ^ 2 := by
  refine (ENNReal.tsum_le_tsum fun r ↦ (show (if Doom n (nxR e G n μ i r) then 0 else
      QuantumRuntime.potential (hwProjector (Bad e G n))
        (((Quantum.Xmss.Hybrid.runtime2 HashOutput HashDomain m₀).step i).branch r σ)) ≤
      QuantumRuntime.potential (hwProjector (Bad e G n))
        (((Quantum.Xmss.Hybrid.runtime2 HashOutput HashDomain m₀).step i).branch r σ) by
    split_ifs
    · exact zero_le
    · exact le_rfl)).trans ?_
  have hbr : ∀ r, ((Quantum.Xmss.Hybrid.runtime2 HashOutput HashDomain m₀).step i).branch r σ =
      MatrixMap.conj (Quantum.Xmss.Hybrid.kraus2 HashOutput HashDomain m₀ i r) σ := fun r ↦ by
    rw [Quantum.Xmss.Hybrid.runtime2_branch]
  refine (le_of_eq (tsum_congr fun r ↦ congrArg _ (hbr r))).trans ?_
  rcases μ with ⟨_ | m, ph⟩
  · exact absurd trivial hd
  have hsupp := querySupportedOn_of_dSupp (proj := Prod.fst) (μ := (some m, ph)) rfl hs
  rcases okR_live hi with ⟨p, rfl⟩ | ⟨z, c, rfl, hca⟩
  · change (∑' r : Unit, QuantumRuntime.potential (hwProjector (Bad e G n))
      (MatrixMap.conj ((spongeHardwired HashOutput HashDomain (hwEmpty HashOutput HashDomain)
        m₀).U p) σ)) ≤ _
    rw [tsum_eq_single () fun r hr ↦ absurd rfl hr]
    have h := potential_sponge_bad_le (G := G) hF m₀ p hσ
    refine le_sq_of_rpow_le (h.trans ?_)
    have hA : κA n (.inl (.inl p) : (hwSpec HashOutput HashDomain (Mem n)).Port) = 1 := rfl
    have hB : κB e G n (some m, ph) (.inl (.inl p)) = 0 := rfl
    rw [hA, hB, Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, add_zero]
    exact le_rfl
  change (∑' r, QuantumRuntime.potential (hwProjector (Bad e G n))
    (MatrixMap.conj (hwReadKraus (HwRead.readH z (upd e G n c z)) r) σ)) ≤ _
  by_cases hans : c = .answer
  · subst hans
    have hP : QuerySupportedOn (fun q : Unit × HwReg HashOutput HashDomain (Mem n) ↦ q.2)
        {s | P1 e G n m s} σ := hc.imp fun s hs ↦ hs m rfl (hca rfl)
    refine (tsum_potential_hwReadKraus_le_of_supp (Bad e G n) _ {s | P1 e G n m s}
      (fun r q' q hK hq ↦ ?_) hσ hP).trans ?_
    · obtain ⟨hcz, -, hW, hmem⟩ := hwReadKraus_readH_ne_zero z _ r hK
      have hq' : P1 e G n m q.2 := hq
      rw [hq'.1] at hmem
      exact iff_of_false (not_mem_bad_of_p1 (p1_uAns hq' hcz hW hmem)) (not_mem_bad_of_p1 hq')
    · rw [add_assoc]
      exact le_sq_rpow_add _ _
  have hk : ∀ q : Unit × HwReg HashOutput HashDomain (Mem n), σ q q ≠ 0 →
      KeepsAt e G n z (upd e G n c z) q.2.2.2 := fun q hq ↦ by
    rw [(hsupp q q hq).1.1]
    exact keepsAt_upd hans z m
  by_cases hch : Charged e G n m z
  · have h := tsum_potential_read_bad hF hσ
      (readNoBot_of_dSupp (proj := Prod.fst) (μ := (some m, ph)) rfl hs _) hk
    refine h.trans (le_of_eq ?_)
    have hκ : κB e G n (some m, ph) (.inl (.inr (.readH z (upd e G n c z)))) = 1 := by
      simp [κB, hch, upd_ne_answer hans z]
    rw [hκ, ENNReal.ofReal_mul (gradeEta_nonneg _ _)]
    have hA : κA n (.inl (.inr (.readH z (upd e G n c z))) :
      (hwSpec HashOutput HashDomain (Mem n)).Port) = 0 := rfl
    rw [hA, Nat.cast_zero, zero_mul, add_zero, Nat.cast_one, one_mul]
    exact rfl
  · refine (tsum_potential_hwReadKraus_le_of_supp (Bad e G n) _ {s | s.2.2 = m}
      (fun r q' q hK hq ↦ ?_) hσ (hsupp.imp fun s hs ↦ hs.1)).trans ?_
    · obtain ⟨hcz, -, hW, hmem⟩ := hwReadKraus_readH_ne_zero z _ r hK
      have hq' : q.2.2.2 = m := hq
      exact bad_iff_of_read (hq' ▸ keepsAt_upd hans z m) (hq' ▸ hch) hcz hW hmem
    · rw [add_assoc]
      exact le_sq_rpow_add _ _

end modes

/-! ## The bound of the read program -/

section bound

variable {Par Tw Msg Dig : Type} {e : CtrEnc Par Tw Msg Dig} {G : Tw → Prop} {n : ℕ}

open scoped Classical in
/-- **The bound of a moded read program**: if every leaf is reached in a mode whose live memory
has at most `n` charged reads and, on `true`, the judge's hit, the probability of `true` is at
most `(q √(6 F/N) + n √(gradeEta F))²`, with `q` the adversary's calls. -/
theorem evalDistMap_le_of_moded {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F)
    (x : QuantumComp LocalSig.instruments.{0} (hwSpec HashOutput HashDomain (Mem n))
      (QuantumComp₂.Leaf (QReg.of Unit) Bool) (QReg.of Unit)) {q : ℕ}
    (hq : IFreeM.IsChargeBound x (portCharge (κA n)) q)
    (Win : Bool → Option (Mem n) → Prop)
    (hWin : ∀ b m, Win b (some m) → m.cnt.val ≤ n ∧ (b = true → m.flag = true))
    (hx : Quantum.Xmss.Assembly.ModedP (okR e G n) (nxR e G n) (fun p μ ↦ Win p.2.2 μ.1)
      (some mem₀, true) x) :
    (Quantum.Xmss.Hybrid.runtime2 HashOutput HashDomain (mem₀ (n := n))).evalDistMap
        .instruments x (SubState.basis ()) (fun p ↦ p.2.2) {true} ≤
      (q * (6 * ((F : ℝ≥0∞) / Fintype.card HashOutput)) ^ (2⁻¹ : ℝ) +
        n * ENNReal.ofReal (gradeEta HashOutput F) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hok : ∀ μ i, okR e G n μ i → OkD (rl (n := n)) (Prod.fst μ) i := fun _ _ h ↦ h.1
  have hnx : ∀ μ i r, okR e G n μ i →
      Prod.fst (nxR e G n μ i r) = nxD (rl (n := n)) (Prod.fst μ) i r := fun _ _ _ _ ↦ rfl
  refine (evalDistMap_le_eventWeight_moded (rl (n := n)) Prod.fst mem₀ (fun _ ↦ rfl) hok hnx
    (Bad e G n) {m | m.flag = true} (fun s hs ↦ Or.inr hs) x (some mem₀, true) rfl hx
    (fun p μ hf hp m hm ↦ ?_)).trans ?_
  · rw [hm] at hf
    exact (hWin _ m hf).2 hp
  rw [Quantum.Sponge.eventWeight_eq_tsum_potential]
  set ρ := (SubState.basis ()).matrix ⊗ₖ
    (Quantum.Xmss.Hybrid.runtime2 HashOutput HashDomain (mem₀ (n := n))).init.matrix with hρdef
  have hρ : ρ.PosSemidef := ((SubState.basis ()).prod
    (Quantum.Xmss.Hybrid.runtime2 HashOutput HashDomain (mem₀ (n := n))).init).posSemidef
  have htr : ENNReal.ofReal ρ.trace.re ≤ 1 := ENNReal.ofReal_le_one.mpr ((SubState.basis ()).prod
    (Quantum.Xmss.Hybrid.runtime2 HashOutput HashDomain (mem₀ (n := n))).init).trace_re_le_one
  have hds : DSupp (rl (n := n)) Prod.fst ((some mem₀, true) : Option (Mem n) × Bool) ρ :=
    dInv_init (rl (n := n)) mem₀ (fun _ ↦ rfl) _
  have hci : QuerySupportedOn (fun m : QReg.of Unit × HwReg HashOutput HashDomain (Mem n) ↦ m.2)
      (CInv e G n (some mem₀, true)) ρ :=
    (querySupportedOn_init (X := HashOutput) (Z := HashDomain) mem₀
      (SubState.basis ()).matrix).imp fun s hs m hm _ ↦ by
      rw [Set.mem_singleton_iff] at hs
      cases hm
      rw [hs]
      exact ⟨rfl, rfl, rfl, fun x _ hx ↦ absurd rfl hx⟩
  have hp0 : QuantumRuntime.potential (hwProjector (Bad e G n)) ρ = 0 :=
    potential_eq_zero_of_supp _ (hci.imp fun s hs ↦ not_mem_bad_of_p1 (hs mem₀ rfl rfl))
  have h := rpow_inv_two_tsum_potential_runtime2_moded (rl := rl (n := n)) (proj := Prod.fst)
    mem₀ hok hnx
    (Bad e G n) (Doom n) (fun μ i r hi hd ↦ doom_nx r hi hd) (κA n) (κB e G n) (bud n)
    (fun μ i r hi hd ↦ bud_nx r hi hd) (6 * ((F : ℝ≥0∞) / Fintype.card HashOutput))
    (ENNReal.ofReal (gradeEta HashOutput F)) (CInv e G n)
    (fun μ i r σ hi hσ ↦ cInv_step mem₀ r hi hσ)
    (fun μ i σ hi hd hσ hs hc ↦ tsum_potential_step_le hF mem₀ μ i σ hi hd hσ hs hc)
    (fun p μ hf hd ↦ by
      rcases μ with ⟨_ | m, ph⟩
      · rfl
      · exact absurd hd (by
          have := (hWin _ m hf).1
          change ¬ m.cnt.val = n + 1
          omega))
    .instruments x q hq (some mem₀, true) hx hρ hds hci
  rw [hp0, ENNReal.zero_rpow_of_pos (by norm_num), add_zero] at h
  refine le_sq_of_rpow_le (h.trans ?_)
  have hb : bud n ((some mem₀, true) : Option (Mem n) × Bool) = n := by
    change n - (0 : Fin (n + 2)).val = n
    simp
  rw [hb]
  have h1 : (6 * ((F : ℝ≥0∞) / Fintype.card HashOutput) * ENNReal.ofReal ρ.trace.re) ^
      (2⁻¹ : ℝ) ≤ (6 * ((F : ℝ≥0∞) / Fintype.card HashOutput)) ^ (2⁻¹ : ℝ) :=
    ENNReal.rpow_le_rpow (mul_le_of_le_one_right' htr) (by norm_num)
  have h2 : (ENNReal.ofReal (gradeEta HashOutput F) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (gradeEta HashOutput F) ^ (2⁻¹ : ℝ) :=
    ENNReal.rpow_le_rpow (mul_le_of_le_one_right' htr) (by norm_num)
  exact add_le_add (by gcongr) (by gcongr)

end bound

/-! ## The transcript and the memory of the challenger's reads -/

section inv

open OracleComp OracleSpec

variable {Par Tw Msg Dig Fn Out : Type} {CMsg : Fn → Type}

open scoped Classical in
/-- The targets of a transcript at the tweak `t`: their messages and answers. -/
noncomputable def tgtAt (log : QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out)) (t : Tw) :
    List (Msg × Option (ℕ × Dig)) :=
  (ctrTargets log).filterMap fun x ↦ if x.1.1 = t then some (x.1.2, x.2) else none

/-- An evaluation of the transcript is at the tweak `t`. -/
def EvAt (log : QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out)) (t : Tw) : Prop :=
  t ∈ log.filterMap CtrQuery.evalTweak

variable (e : CtrEnc Par Tw Msg Dig) (G : Tw → Prop) (n : ℕ)

/-- The number of non-codeword trials of an answer. -/
def bnd : Option (ℕ × Dig) → ℕ
  | some (c, _) => c
  | none => e.limit

/-- **The memory after the grinding of the target `(t, mm)` answered `a`**: its trials are read
and logged, the non-codeword ones before the answer, the answer's cell selected with its digest,
and no other cell of the class read or selected. -/
def GrindFacts (P : Par) (t : Tw) (mm : Msg) (a : Option (ℕ × Dig)) (m : Mem n) : Prop :=
  (∀ c x, c < bnd e a → cellOf e P t mm c = some x →
    m.ax x = true ∧ ∃ v, m.log x = some v ∧ e.isCode (e.hash.trunc v) = false) ∧
  (∀ c d, a = some (c, d) → c < e.limit ∧ e.isCode d = true ∧ ∀ x, cellOf e P t mm c = some x →
    m.ax x = true ∧ ∃ w, m.log x = some w ∧ m.sel x = some w ∧ e.hash.trunc w = d) ∧
  (∀ x, encTw e G x = some t → m.ax x = true →
    ∃ c, cellOf e P t mm c = some x ∧ (c < bnd e a ∨ ∃ d, a = some (c, d))) ∧
  (∀ z, encTw e G z = some t → (m.sel z).isSome →
    ∃ c d, a = some (c, d) ∧ cellOf e P t mm c = some z)

/-- **The invariant of the challenger's reads**: a selected cell was read by the challenger; at a
tweak of `G` without evaluation, no target means no cell of the class read, and a unique target
means its grinding's memory. -/
def Inv (P : Par) (log : QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out)) (m : Mem n) : Prop :=
  (∀ z, (m.sel z).isSome → m.ax z = true) ∧
  ∀ t, G t → ¬ EvAt log t →
    (tgtAt log t = [] → ∀ x, encTw e G x = some t → m.ax x = false) ∧
    ∀ mm a, tgtAt log t = [(mm, a)] → GrindFacts e G n P t mm a m

/-- **The first phase**: every logged cell of a class was read by the challenger. -/
def PhA (m : Mem n) : Prop :=
  ∀ x, encTw e G x ≠ none → (m.log x).isSome → m.ax x = true

/-- **A move keeping the class of `t`**: its reads and selections, and every logged value. -/
def Frame (t : Tw) (m m' : Mem n) : Prop :=
  (∀ x, encTw e G x = some t → m'.ax x = m.ax x ∧ m'.sel x = m.sel x) ∧
    ∀ x v, m.log x = some v → m'.log x = some v

variable {e G n}

theorem frame_refl (t : Tw) (m : Mem n) : Frame e G n t m m :=
  ⟨fun _ _ ↦ ⟨rfl, rfl⟩, fun _ _ h ↦ h⟩

theorem Frame.trans {t : Tw} {m m' m'' : Mem n} (h : Frame e G n t m m')
    (h' : Frame e G n t m' m'') : Frame e G n t m m'' :=
  ⟨fun x hx ↦ ⟨(h'.1 x hx).1.trans (h.1 x hx).1, (h'.1 x hx).2.trans (h.1 x hx).2⟩,
    fun x v hv ↦ h'.2 x v (h.2 x v hv)⟩

theorem encTw_cellOf (hs : EncSep e G) {P : Par} {t : Tw} {mm : Msg} {c : ℕ} {x : HashDomain}
    (hG : G t) (hc : c < e.limit) (hx : cellOf e P t mm c = some x) : encTw e G x = some t :=
  encTw_eq_some hs ⟨hG, P, mm, c, hc, hx⟩

/-- A cell of a trial at the tweak `t` is in no other class. -/
theorem encTw_ne_of_cellOf (hs : EncSep e G) {P : Par} {t t' : Tw} {mm : Msg} {c : ℕ}
    {x : HashDomain} (hx : cellOf e P t mm c = some x) (ht : t' ≠ t) : encTw e G x ≠ some t' :=
  fun h ↦ by
    obtain ⟨hG, P', mm', c', -, hx'⟩ := isGTw_of_encTw h
    exact ht (hs P' t' (mm', c') P t (mm, c) hG (encodeInput_injective hx hx')).symm

theorem lt_limit_of_grindFacts {P : Par} {t : Tw} {mm : Msg} {a : Option (ℕ × Dig)}
    {m : Mem n} (h : GrindFacts e G n P t mm a m) {c : ℕ} (hc : c < bnd e a) : c < e.limit := by
  rcases a with _ | ⟨c₀, d⟩
  · exact hc
  · exact hc.trans (h.2.1 c₀ d rfl).1

theorem grindFacts_frame (hs : EncSep e G) {P : Par} {t : Tw} {mm : Msg}
    {a : Option (ℕ × Dig)} {m m' : Mem n} (hG : G t) (hf : Frame e G n t m m')
    (h : GrindFacts e G n P t mm a m) : GrindFacts e G n P t mm a m' := by
  obtain ⟨g1, g2, g3, g4⟩ := h
  refine ⟨fun c x hc hx ↦ ?_, fun c d ha ↦ ?_, fun x hx hax ↦ ?_, fun z hz hsel ↦ ?_⟩
  · have hcl := lt_limit_of_grindFacts ⟨g1, g2, g3, g4⟩ hc
    obtain ⟨h1, v, h2, h3⟩ := g1 c x hc hx
    refine ⟨?_, v, hf.2 x v h2, h3⟩
    rw [(hf.1 x (encTw_cellOf hs hG hcl hx)).1]
    exact h1
  · obtain ⟨hc, hcode, hx⟩ := g2 c d ha
    refine ⟨hc, hcode, fun x hxc ↦ ?_⟩
    obtain ⟨h1, w, h2, h3, h4⟩ := hx x hxc
    have hfx := hf.1 x (encTw_cellOf hs hG hc hxc)
    exact ⟨by rw [hfx.1]; exact h1, w, hf.2 x w h2, by rw [hfx.2]; exact h3, h4⟩
  · exact g3 x hx (by rw [← (hf.1 x hx).1]; exact hax)
  · exact g4 z hz (by rw [← (hf.1 z hz).2]; exact hsel)

theorem uAns_ax (z : HashDomain) (m : Mem n) (o : Option HashOutput) :
    (uAns e G n z m o).ax = Function.update m.ax z true :=
  rfl

theorem uAns_log (z : HashDomain) (m : Mem n) (o : Option HashOutput) :
    (uAns e G n z m o).log = Function.update m.log z o :=
  rfl

theorem uAns_sel_of_code {z : HashDomain} (hz : encTw e G z ≠ none) (m : Mem n) {v : HashOutput}
    (hv : e.isCode (e.hash.trunc v) = true) :
    (uAns e G n z m (some v)).sel = Function.update m.sel z (some v) := by
  simp only [uAns, Mem.sel]
  split_ifs with h
  · rfl
  · exact absurd ⟨hz, v, rfl, hv⟩ h

theorem uAns_sel_of_not_code (z : HashDomain) (m : Mem n) {v : HashOutput}
    (hv : e.isCode (e.hash.trunc v) = false) : (uAns e G n z m (some v)).sel = m.sel := by
  simp only [uAns, Mem.sel]
  split_ifs with h
  · obtain ⟨-, v', hv', hc⟩ := h
    cases hv'
    rw [hv] at hc
    cases hc
  · rfl

/-- The logged values persist along a live step. -/
theorem log_persist {u : Mem n → Option HashOutput → Mem n} {z : HashDomain}
    (hu : ∀ m o, (u m o).log = Function.update m.log z o) {m m' : Mem n} {y : HashOutput}
    (h : stepRd (rl n) u z (some m) y = some m') : ∀ x v, m.log x = some v → m'.log x = some v := by
  obtain ⟨rfl, hc⟩ := stepRd_some h
  intro x v hv
  rw [hu]
  by_cases hx : x = z
  · subst hx
    rw [Function.update_self]
    rcases hc with hc | hc
    · change m.log x = none at hc
      rw [hc] at hv
      cases hv
    · change m.log x = some y at hc
      rw [hv] at hc
      exact hc.symm
  · rw [Function.update_of_ne hx]
    exact hv

/-- **A live answer read** keeps the first phase's logs read, the selections read, and every other
class. -/
theorem uAns_step {x : HashDomain} {m m' : Mem n} {y : HashOutput}
    (h : stepRd (rl n) (uAns e G n x) x (some m) y = some m') (hph : PhA e G n m)
    (hI : ∀ z, (m.sel z).isSome → m.ax z = true) :
    PhA e G n m' ∧ (∀ z, (m'.sel z).isSome → m'.ax z = true) ∧
      ∀ t, encTw e G x ≠ some t → Frame e G n t m m' := by
  have hp := log_persist (fun m o ↦ uAns_log x m o) h
  obtain ⟨rfl, -⟩ := stepRd_some h
  refine ⟨fun z hz hl ↦ ?_, fun z hz ↦ ?_, fun t ht ↦ ⟨fun z hz ↦ ?_, hp⟩⟩
  · rw [uAns_ax]
    by_cases hzx : z = x
    · subst hzx
      exact Function.update_self ..
    · rw [Function.update_of_ne hzx]
      rw [uAns_log, Function.update_of_ne hzx] at hl
      exact hph z hz hl
  · rw [uAns_ax]
    by_cases hzx : z = x
    · subst hzx
      exact Function.update_self ..
    · rw [Function.update_of_ne hzx]
      refine hI z ?_
      by_cases hc : e.isCode (e.hash.trunc y) = true ∧ encTw e G x ≠ none
      · rwa [uAns_sel_of_code hc.2 m hc.1, Function.update_of_ne hzx] at hz
      · have : (uAns e G n x m (some y)).sel = m.sel := by
          simp only [uAns, Mem.sel]
          split_ifs with h'
          · obtain ⟨hx, v', hv', hc'⟩ := h'
            cases hv'
            exact absurd ⟨hc', hx⟩ hc
          · rfl
        rwa [this] at hz
  · have hzx : z ≠ x := by
      rintro rfl
      exact ht hz
    refine ⟨by rw [uAns_ax, Function.update_of_ne hzx], ?_⟩
    by_cases hc : e.isCode (e.hash.trunc y) = true ∧ encTw e G x ≠ none
    · rw [uAns_sel_of_code hc.2 m hc.1, Function.update_of_ne hzx]
    · simp only [uAns, Mem.sel]
      split_ifs with h'
      · obtain ⟨hx, v', hv', hc'⟩ := h'
        cases hv'
        exact absurd ⟨hc', hx⟩ hc
      · rfl

/-- **A live read of another caller** keeps every class. -/
theorem upd_step {c : Caller} (hc : c ≠ .answer) {x : HashDomain} {m m' : Mem n}
    {y : HashOutput} (h : stepRd (rl n) (upd e G n c x) x (some m) y = some m') (t : Tw) :
    Frame e G n t m m' ∧ m'.ax = m.ax ∧ m'.sel = m.sel := by
  have hp := log_persist (fun m o ↦ recordsAt_upd (e := e) (G := G) c x m o) h
  obtain ⟨rfl, -⟩ := stepRd_some h
  obtain ⟨hax, hsel, -⟩ := keepsAt_upd (e := e) (G := G) hc x m (some y)
  exact ⟨⟨fun z _ ↦ ⟨by rw [hax], by rw [hsel]⟩, hp⟩, hax, hsel⟩

end inv

/-! ## The live runs of the challenger -/

section live

open OracleComp OracleSpec

variable {Par Tw Msg Dig Fn Out : Type} {CMsg : Fn → Type} {e : CtrEnc Par Tw Msg Dig}
  {G : Tw → Prop} {n : ℕ}

/-- **Lengths of the encoding inputs**: every one is a cell. -/
def LenOk (e : CtrEnc Par Tw Msg Dig) : Prop :=
  ∀ P t mc, (e.hash.layout () P t mc).length ≤ maxLen

theorem cellOf_isSome (hlen : LenOk e) (P : Par) (t : Tw) (mm : Msg) (c : ℕ) :
    ∃ x, cellOf e P t mm c = some x :=
  ⟨_, encodeInput_of_length_le (hlen P t (mm, c))⟩

/-- One trial of the grinding. -/
theorem grind_succ (P : Par) (t : Tw) (mm : Msg) (c k : ℕ) :
    e.grind romWorld P t mm c (k + 1) = hashQ (e.hash.layout () P t (mm, c)) >>= fun y ↦
      if e.isCode (e.hash.trunc y) then pure (some (c, e.hash.trunc y))
      else e.grind romWorld P t mm (c + 1) k := by
  simp only [CtrEnc.grind, TwColl.eval]
  change (e.hash.trunc <$> hashQ (e.hash.layout () P t (mm, c))) >>= _ = _
  exact bind_map_left _ _ _

/-- **The grinding at the tweak `t` keeps the first phase and every other class.** -/
theorem grind_frame (hs : EncSep e G) (hlen : LenOk e) (P : Par) (t : Tw) (mm : Msg) :
    ∀ (k c : ℕ) (m : Mem n) (a : Option (ℕ × Dig)) (μ' : Option (Mem n)), PhA e G n m →
      (∀ z, (m.sel z).isSome → m.ax z = true) →
      LiveRun (rl n) (upd e G n .answer) (e.grind romWorld P t mm c k) (some m) a μ' →
      ∀ m', μ' = some m' → PhA e G n m' ∧ (∀ z, (m'.sel z).isSome → m'.ax z = true) ∧
        ∀ t', t' ≠ t → Frame e G n t' m m' := by
  intro k
  induction k with
  | zero =>
    intro c m a μ' hph hI hrun m' hm'
    change LiveRun _ _ (pure none) _ _ _ at hrun
    obtain ⟨-, rfl⟩ := liveRun_pure_inv hrun
    cases hm'
    exact ⟨hph, hI, fun t' _ ↦ frame_refl t' m⟩
  | succ k ih =>
    intro c m a μ' hph hI hrun m' hm'
    obtain ⟨x, hx⟩ := cellOf_isSome hlen P t mm c
    rw [grind_succ P t mm c k] at hrun
    change LiveRun _ _ (hashQ (e.hash.layout () P t (mm, c)) >>= _) _ _ _ at hrun
    rw [hashQ_of_encodeInput_eq_some hx] at hrun
    obtain ⟨y, μ₁, hy, hrun'⟩ := liveRun_query_bind hrun
    have hμ₁ := eq_stepRd_of_mem_support hy
    rcases h₁ : μ₁ with _ | m₁
    · rw [h₁] at hrun'
      split_ifs at hrun' <;> rw [liveRun_none_mode _ hrun'] at hm' <;> cases hm'
    rw [h₁] at hμ₁ hrun'
    obtain ⟨hph₁, hI₁, hf₁⟩ := uAns_step hμ₁.symm hph hI
    have hft : ∀ t', t' ≠ t → Frame e G n t' m m₁ := fun t' ht' ↦
      hf₁ t' (encTw_ne_of_cellOf hs hx ht')
    by_cases hcode : e.isCode (e.hash.trunc y) = true <;>
      simp only [hcode, ↓reduceIte] at hrun'
    · obtain ⟨-, rfl⟩ := liveRun_pure_inv hrun'
      cases hm'
      exact ⟨hph₁, hI₁, hft⟩
    · obtain ⟨h1, h2, h3⟩ := ih (c + 1) m₁ a μ' hph₁ hI₁ hrun' m' hm'
      exact ⟨h1, h2, fun t' ht' ↦ (hft t' ht').trans (h3 t' ht')⟩

variable (e G n) in
/-- **The memory before the trial `c` of a target's grinding**: the earlier trials read, logged
and not codewords, no other cell of the class read, nothing of the class selected. -/
def PreG (P : Par) (t : Tw) (mm : Msg) (c : ℕ) (m : Mem n) : Prop :=
  (∀ c' x, c' < c → cellOf e P t mm c' = some x →
    m.ax x = true ∧ ∃ v, m.log x = some v ∧ e.isCode (e.hash.trunc v) = false) ∧
  (∀ x, encTw e G x = some t → m.ax x = true → ∃ c', c' < c ∧ cellOf e P t mm c' = some x) ∧
  (∀ z, encTw e G z = some t → m.sel z = none) ∧ PhA e G n m ∧
  ∀ z, (m.sel z).isSome → m.ax z = true

/-- **The grinding of a fresh target** leaves its memory. -/
theorem grind_live (hs : EncSep e G) (hlen : LenOk e)
    (hinj : ∀ P t, G t → Set.InjOn (e.hash.layout () P t) {x | x.2 < e.limit}) (P : Par)
    {t : Tw} (hG : G t) (mm : Msg) :
    ∀ (k c : ℕ) (m : Mem n) (a : Option (ℕ × Dig)) (μ' : Option (Mem n)), c + k = e.limit →
      PreG e G n P t mm c m →
      LiveRun (rl n) (upd e G n .answer) (e.grind romWorld P t mm c k) (some m) a μ' →
      ∀ m', μ' = some m' → GrindFacts e G n P t mm a m' := by
  have hcell : ∀ {c c' : ℕ} {x : HashDomain}, c < e.limit → c' < e.limit →
      cellOf e P t mm c = some x → cellOf e P t mm c' = some x → c = c' := fun hc hc' hx hx' ↦
    (Prod.mk.inj (hinj P t hG hc hc' (encodeInput_injective hx hx'))).2
  intro k
  induction k with
  | zero =>
    intro c m a μ' hck hpre hrun m' hm'
    change LiveRun _ _ (pure none) _ _ _ at hrun
    obtain ⟨rfl, rfl⟩ := liveRun_pure_inv hrun
    cases hm'
    have hc : c = e.limit := by omega
    subst hc
    obtain ⟨p1, p2, p3, -, -⟩ := hpre
    refine ⟨fun c' x hc' hx ↦ p1 c' x hc' hx, ?_, fun x hx hax ↦ ?_, fun z hz hsel ↦ ?_⟩
    · intro c d h
      cases h
    · obtain ⟨c', hc', hx'⟩ := p2 x hx hax
      exact ⟨c', hx', Or.inl hc'⟩
    · rw [p3 z hz] at hsel
      cases hsel
  | succ k ih =>
    intro c m a μ' hck hpre hrun m' hm'
    have hcl : c < e.limit := by omega
    obtain ⟨x, hx⟩ := cellOf_isSome hlen P t mm c
    have hxt := encTw_cellOf hs hG hcl hx
    obtain ⟨p1, p2, p3, p4, p5⟩ := hpre
    have hax : m.ax x = false := by
      by_contra h
      obtain ⟨c', hc', hx'⟩ := p2 x hxt (by simpa using h)
      exact absurd (hcell (hc'.trans hcl) hcl hx' hx) (Nat.ne_of_lt hc')
    have hlog : m.log x = none := by
      by_contra h
      rw [p4 x (by rw [hxt]; exact Option.some_ne_none t)
        (Option.ne_none_iff_isSome.mp h)] at hax
      cases hax
    rw [grind_succ P t mm c k] at hrun
    change LiveRun _ _ (hashQ (e.hash.layout () P t (mm, c)) >>= _) _ _ _ at hrun
    rw [hashQ_of_encodeInput_eq_some hx] at hrun
    obtain ⟨y, μ₁, hy, hrun'⟩ := liveRun_query_bind hrun
    have hμ₁ : μ₁ = stepRd (rl n) (uAns e G n x) x (some m) y := eq_stepRd_of_mem_support hy
    have hstep : stepRd (rl n) (uAns e G n x) x (some m) y = some (uAns e G n x m (some y)) :=
      stepRd_of_none hlog y
    rw [hstep] at hμ₁
    subst hμ₁
    obtain ⟨hph₁, hI₁, -⟩ := uAns_step hstep p4 p5
    have hpers := log_persist (fun m o ↦ uAns_log x m o) hstep
    have hax' : ∀ x', m.ax x' = true → (uAns e G n x m (some y)).ax x' = true := fun x' h ↦ by
      rw [uAns_ax]
      by_cases hxx : x' = x
      · subst hxx
        exact Function.update_self ..
      · rw [Function.update_of_ne hxx]
        exact h
    have haxx : (uAns e G n x m (some y)).ax x = true := by
      rw [uAns_ax]
      exact Function.update_self ..
    have hlogx : (uAns e G n x m (some y)).log x = some y := by
      rw [uAns_log]
      exact Function.update_self ..
    by_cases hcode : e.isCode (e.hash.trunc y) = true <;>
      simp only [hcode, ↓reduceIte] at hrun'
    · obtain ⟨rfl, rfl⟩ := liveRun_pure_inv hrun'
      cases hm'
      have hsel := uAns_sel_of_code (n := n) (by rw [hxt]; exact Option.some_ne_none t) m hcode
      refine ⟨fun c' x' hc' hx' ↦ ?_, fun c' d h ↦ ?_, fun x' hx' hax'' ↦ ?_, fun z hz hs' ↦ ?_⟩
      · obtain ⟨h1, v, h2, h3⟩ := p1 c' x' hc' hx'
        exact ⟨hax' x' h1, v, hpers x' v h2, h3⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        refine ⟨hcl, hcode, fun x' hx' ↦ ?_⟩
        rw [hx] at hx'
        cases hx'
        exact ⟨haxx, y, hlogx, by rw [hsel]; exact Function.update_self .., rfl⟩
      · by_cases hxx : x' = x
        · subst hxx
          exact ⟨c, hx, Or.inr ⟨_, rfl⟩⟩
        · rw [uAns_ax, Function.update_of_ne hxx] at hax''
          obtain ⟨c', hc', h'⟩ := p2 x' hx' hax''
          exact ⟨c', h', Or.inl hc'⟩
      · by_cases hzx : z = x
        · subst hzx
          exact ⟨c, _, rfl, hx⟩
        · rw [hsel, Function.update_of_ne hzx, p3 z hz] at hs'
          cases hs'
    · have hcode' : e.isCode (e.hash.trunc y) = false := by simpa using hcode
      have hsel := uAns_sel_of_not_code (G := G) (n := n) x m hcode'
      refine ih (c + 1) _ a μ' (by omega) ⟨fun c' x' hc' hx' ↦ ?_, fun x' hx' hax'' ↦ ?_,
        fun z hz ↦ by rw [hsel]; exact p3 z hz, hph₁, hI₁⟩ hrun' m' hm'
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hc' with hc' | rfl
        · obtain ⟨h1, v, h2, h3⟩ := p1 c' x' hc' hx'
          exact ⟨hax' x' h1, v, hpers x' v h2, h3⟩
        · rw [hx] at hx'
          cases hx'
          exact ⟨haxx, y, hlogx, hcode'⟩
      · by_cases hxx : x' = x
        · subst hxx
          exact ⟨c, Nat.lt_succ_self c, hx⟩
        · rw [uAns_ax, Function.update_of_ne hxx] at hax''
          obtain ⟨c', hc', h'⟩ := p2 x' hx' hax''
          exact ⟨c', hc'.trans (Nat.lt_succ_self c), h'⟩

open scoped Classical in
theorem tgtAt_append_target (log : QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out)) (t' : Tw)
    (mm : Msg) (a : Option (ℕ × Dig)) (t : Tw) :
    tgtAt (log ++ [⟨.target t' mm, a⟩]) t = tgtAt log t ++ if t' = t then [(mm, a)] else [] := by
  unfold tgtAt ctrTargets
  rw [List.filterMap_append, List.filterMap_append]
  congr 1
  simp only [List.filterMap_cons, List.filterMap_nil, CtrQuery.asTarget]
  split_ifs <;> rfl

theorem tgtAt_append_of_asTarget (log : QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out))
    (x : (q : CtrQuery Tw Msg Fn CMsg) × (CtrSpec Par Tw Msg Dig Fn CMsg Out).Range q)
    (hx : CtrQuery.asTarget x = none) (t : Tw) : tgtAt (log ++ [x]) t = tgtAt log t := by
  unfold tgtAt ctrTargets
  rw [List.filterMap_append, List.filterMap_append]
  simp [hx]

theorem evAt_append (log : QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out))
    (x : (q : CtrQuery Tw Msg Fn CMsg) × (CtrSpec Par Tw Msg Dig Fn CMsg Out).Range q)
    (t : Tw) : EvAt (log ++ [x]) t ↔ EvAt log t ∨ CtrQuery.evalTweak x = some t := by
  unfold EvAt
  rw [List.filterMap_append, List.mem_append]
  rcases h : CtrQuery.evalTweak x with _ | t'
  · simp [h]
  · simp [h, eq_comm]

open scoped Classical in
/-- **A unique target at its tweak**, on a transcript with distinct target tweaks. -/
theorem tgtAt_eq_singleton (log : QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out))
    (hnd : ((ctrTargets log).map fun x ↦ x.1.1).Nodup) {x : (Tw × Msg) × Option (ℕ × Dig)}
    (hx : x ∈ ctrTargets log) : tgtAt log x.1.1 = [(x.1.2, x.2)] := by
  unfold tgtAt
  generalize ctrTargets log = L at hnd hx
  induction L with
  | nil => cases hx
  | cons y L ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hx with rfl | hx
    · have h0 : L.filterMap (fun z ↦ if z.1.1 = x.1.1 then some (z.1.2, z.2) else none) = [] :=
        List.filterMap_eq_nil_iff.mpr fun z hz ↦ by
          split_ifs with h
          · exact absurd (by rw [← h]; exact List.mem_map_of_mem hz) hnd.1
          · rfl
      simp [h0]
    · have hne : ¬ y.1.1 = x.1.1 := fun h ↦ hnd.1 (h ▸ List.mem_map_of_mem hx)
      simp only [List.filterMap_cons, hne, ↓reduceIte]
      exact ih hnd.2 hx

end live

/-! ## The challenger's answers and decision -/

section game

open OracleComp OracleSpec Common

variable {Par Tw Msg Dig Fn Out : Type} {CMsg : Fn → Type} [SampleableType Par]
  {e : CtrEnc Par Tw Msg Dig} {G : Tw → Prop} {n : ℕ}

omit [SampleableType Par] in
/-- **An evaluation of the collection**: one read of its cell. -/
theorem eval_eq (C : TwColl Par Tw Fn CMsg Out) (l : Fn) (P : Par) (t : Tw) (mm : CMsg l) :
    C.eval romWorld l P t mm = hashQ (C.layout l P t mm) >>= fun y ↦ pure (C.trunc y) := by
  change C.trunc <$> hashQ (C.layout l P t mm) = _
  exact map_eq_bind_pure_comp (m := OracleComp romWorld.Oracles) C.trunc _

open scoped Classical in
/-- **An answer of the challenger keeps the invariant and the first phase.** -/
theorem inv_answer (C : TwColl Par Tw Fn CMsg Out) (hs : EncSep e G) (hlen : LenOk e)
    (hinj : ∀ P t, G t → Set.InjOn (e.hash.layout () P t) {x | x.2 < e.limit})
    (hCsep : ∀ l P t' mm P' t mc, G t → C.layout l P t' mm = e.hash.layout () P' t mc → t' = t)
    (P : Par) (q' : CtrQuery Tw Msg Fn CMsg) {log : QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out)}
    {m : Mem n} (hI : Inv e G n P log m) (hph : PhA e G n m)
    {a : (CtrSpec Par Tw Msg Dig Fn CMsg Out).Range q'} {μ' : Option (Mem n)}
    (hrun : LiveRun (rl n) (upd e G n .answer) ((encTcrCtrIn romWorld e C G).answer P q')
      (some m) a μ') :
    ∀ m', μ' = some m' → Inv e G n P (log ++ [⟨q', a⟩]) m' ∧ PhA e G n m' := by
  intro m' hm'
  rcases q' with ⟨t', mm⟩ | ⟨l, t', mm⟩ | _
  · change LiveRun _ _ (e.grind romWorld P t' mm 0 e.limit) _ _ _ at hrun
    obtain ⟨hph', hI', hfr⟩ := grind_frame hs hlen P t' mm e.limit 0 m a μ' hph hI.1 hrun m' hm'
    refine ⟨⟨hI', fun t hG hev ↦ ?_⟩, hph'⟩
    have hev' : ¬ EvAt log t := fun h ↦ hev ((evAt_append _ _ t).2 (Or.inl h))
    have htg : tgtAt (log ++ [⟨.target t' mm, a⟩]) t =
        tgtAt log t ++ if t' = t then [(mm, show Option (ℕ × Dig) from a)] else [] :=
          tgtAt_append_target log t' mm a t
    rw [htg]
    have hrest := hI.2 t hG hev'
    by_cases htt : t' = t
    · subst htt
      simp only [↓reduceIte]
      rcases hT : tgtAt log t' with _ | ⟨p, ps⟩
      · refine ⟨fun h ↦ by simp at h, fun mm' a' h ↦ ?_⟩
        simp only [List.nil_append, List.cons.injEq, and_true] at h
        obtain ⟨rfl, rfl⟩ := h
        refine grind_live hs hlen hinj P hG mm e.limit 0 m a μ' (by omega)
          ⟨fun _ _ h ↦ absurd h (Nat.not_lt_zero _), fun x hx hax ↦ ?_, fun z hz ↦ ?_, hph, hI.1⟩
          hrun m' hm'
        · rw [hrest.1 hT x hx] at hax
          cases hax
        · by_contra h
          have h' := hI.1 z (Option.ne_none_iff_isSome.mp h)
          rw [hrest.1 hT z hz] at h'
          cases h'
      · exact ⟨fun h ↦ by simp at h, fun mm' a' h ↦ by simp at h⟩
    · simp only [htt, ↓reduceIte, List.append_nil]
      have hf := hfr t (Ne.symm htt)
      exact ⟨fun h x hx ↦ by rw [(hf.1 x hx).1]; exact hrest.1 h x hx,
        fun mm' a' h ↦ grindFacts_frame hs hG hf (hrest.2 mm' a' h)⟩
  · change LiveRun _ _ (C.eval romWorld l P t' mm) _ _ _ at hrun
    rw [eval_eq] at hrun
    have htg : ∀ t, tgtAt (log ++ [⟨.eval l t' mm, a⟩]) t = tgtAt log t :=
      tgtAt_append_of_asTarget log _ rfl
    rcases hx0 : encodeInput (C.layout l P t' mm) with _ | x0
    · have h0 : hashQ (C.layout l P t' mm) = pure 0 := by simp [hashQ, hx0]
      rw [h0] at hrun
      replace hrun := liveRun_pure_bind hrun
      obtain ⟨-, rfl⟩ := liveRun_pure_inv hrun
      cases hm'
      refine ⟨⟨hI.1, fun t hG hev' ↦ ?_⟩, hph⟩
      rw [htg]
      exact hI.2 t hG fun h ↦ hev' ((evAt_append _ _ t).2 (Or.inl h))
    · rw [hashQ_of_encodeInput_eq_some hx0] at hrun
      obtain ⟨y, μ₁, hy, hrun'⟩ := liveRun_query_bind hrun
      have hμ₁ : μ₁ = stepRd (rl n) (uAns e G n x0) x0 (some m) y := eq_stepRd_of_mem_support hy
      obtain ⟨-, rfl⟩ := liveRun_pure_inv hrun'
      rw [hμ₁] at hm'
      obtain ⟨hph', hI', hfr⟩ := uAns_step hm' hph hI.1
      refine ⟨⟨hI', fun t hG hev' ↦ ?_⟩, hph'⟩
      have hne : t' ≠ t := fun h ↦ hev' ((evAt_append _ _ t).2 (Or.inr (by rw [h]; rfl)))
      have hev'' : ¬ EvAt log t := fun h ↦ hev' ((evAt_append _ _ t).2 (Or.inl h))
      have hx0t : encTw e G x0 ≠ some t := fun h ↦ by
        obtain ⟨hG', P', mm', c, -, hc⟩ := isGTw_of_encTw h
        exact hne (hCsep l P t' mm P' t (mm', c) hG' (encodeInput_injective hx0 hc))
      have hf := hfr t hx0t
      have hrest := hI.2 t hG hev''
      rw [htg]
      exact ⟨fun h x hx ↦ by rw [(hf.1 x hx).1]; exact hrest.1 h x hx,
        fun mm' a' h ↦ grindFacts_frame hs hG hf (hrest.2 mm' a' h)⟩
  · change LiveRun _ _ (pure P) _ _ _ at hrun
    obtain ⟨-, rfl⟩ := liveRun_pure_inv hrun
    cases hm'
    refine ⟨⟨hI.1, fun t hG hev ↦ ?_⟩, hph⟩
    rw [tgtAt_append_of_asTarget log _ rfl]
    exact hI.2 t hG fun h ↦ hev ((evAt_append _ _ t).2 (Or.inl h))

omit [SampleableType Par] in
/-- **A read of another caller keeps the invariant**, and the first phase off the classes. -/
theorem inv_read {c : Caller} (hc : c ≠ .answer) (hs : EncSep e G) {P : Par}
    {log : QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out)} {x : HashDomain} {m m' : Mem n}
    {y : HashOutput} (h : stepRd (rl n) (upd e G n c x) x (some m) y = some m')
    (hI : Inv e G n P log m) :
    Inv e G n P log m' ∧ (encTw e G x = none → PhA e G n m → PhA e G n m') := by
  have hm' := (stepRd_some h).1
  obtain ⟨hax, hsel, -⟩ := keepsAt_upd (e := e) (G := G) hc x m (some y)
  have hlog := recordsAt_upd (e := e) (G := G) c x m (some y)
  rw [← hm'] at hax hsel hlog
  refine ⟨⟨fun z hz ↦ ?_, fun t hG hev ↦ ?_⟩, fun hx hph x' hx' hl ↦ ?_⟩
  · rw [hsel] at hz
    rw [hax]
    exact hI.1 z hz
  · have hf := (upd_step hc h t).1
    obtain ⟨h1, h2⟩ := hI.2 t hG hev
    exact ⟨fun h0 x' hx' ↦ by rw [(hf.1 x' hx').1]; exact h1 h0 x' hx',
      fun mm a h0 ↦ grindFacts_frame hs hG hf (h2 mm a h0)⟩
  · have hxx : x' ≠ x := by
      rintro rfl
      exact hx' hx
    change (m'.log x').isSome = true at hl
    rw [hax]
    change (rl n m' x').isSome = true at hl
    rw [hlog, Function.update_of_ne hxx] at hl
    exact hph x' hx' hl

/-- **The decision of the challenger**: one read of the forgery's cell. -/
theorem judge_eq (C : TwColl Par Tw Fn CMsg Out) (P : Par)
    (log : QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out)) (out : Tw × Msg × ℕ) :
    (encTcrCtrIn romWorld e C G).judge P log out =
      hashQ (e.hash.layout () P out.1 (out.2.1, out.2.2)) >>= fun y ↦
        pure (holds (EncIn G log) && holds (EncCtrValid log ∧ out.2.2 < e.limit ∧
          ∃ x ∈ ctrTargets log, ∃ c, x.2 = some (c, e.hash.trunc y) ∧ x.1.1 = out.1 ∧
            (x.1.2, c) ≠ out.2)) := by
  change ((e.hash.trunc <$> hashQ (e.hash.layout () P out.1 (out.2.1, out.2.2))) >>= fun d ↦
    pure (holds (EncCtrValid log ∧ out.2.2 < e.limit ∧ ∃ x ∈ ctrTargets log, ∃ c,
      x.2 = some (c, d) ∧ x.1.1 = out.1 ∧ (x.1.2, c) ≠ out.2))) >>= (fun b ↦
        pure (holds (EncIn G log) && b)) = _
  simp only [bind_map_left, bind_assoc, pure_bind]

open scoped Classical in
/-- **The judge's hit**: a winning decision from the invariant raises the hit, and the judge's
read leaves at most `n` charged reads. -/
theorem win_judge (C : TwColl Par Tw Fn CMsg Out) (hs : EncSep e G) (hlen : LenOk e)
    (hinj : ∀ P t, G t → Set.InjOn (e.hash.layout () P t) {x | x.2 < e.limit}) {P : Par}
    {log : QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out)} {out : Tw × Msg × ℕ} {m : Mem n}
    (hI : Inv e G n P log m) (hcnt : m.cnt.val + 1 ≤ n) {b : Bool} {μ' : Option (Mem n)}
    (hrun : LiveRun (rl n) (upd e G n .judge) ((encTcrCtrIn romWorld e C G).judge P log out)
      (some m) b μ') :
    ∀ m', μ' = some m' → m'.cnt.val ≤ n ∧ (b = true → m'.flag = true) := by
  intro m' hm'
  obtain ⟨xs, hxs⟩ := cellOf_isSome hlen P out.1 out.2.1 out.2.2
  rw [judge_eq] at hrun
  change LiveRun _ _ (hashQ (e.hash.layout () P out.1 (out.2.1, out.2.2)) >>= _) _ _ _ at hrun
  rw [hashQ_of_encodeInput_eq_some hxs] at hrun
  obtain ⟨y, μ₁, hy, hrun'⟩ := liveRun_query_bind hrun
  have hμ₁ : μ₁ = stepRd (rl n) (uJudge e G n xs) xs (some m) y := eq_stepRd_of_mem_support hy
  obtain ⟨rfl, rfl⟩ := liveRun_pure_inv hrun'
  rw [hμ₁] at hm'
  have hcons := (stepRd_some hm').2
  obtain ⟨rfl, -⟩ := stepRd_some hm'
  refine ⟨?_, fun hb ↦ ?_⟩
  · change (cntAfter e G n m xs).val ≤ n
    unfold cntAfter
    split_ifs
    · change min (m.cnt.val + 1) (n + 1) ≤ n
      omega
    · omega
  rw [Bool.and_eq_true, holds_eq_true, holds_eq_true] at hb
  obtain ⟨hEIn, ⟨hnd, -, hev⟩, hlt, x, hxm, c, hxa, hxt, hne⟩ := hb
  have hG : G out.1 := hxt ▸ hEIn x hxm
  have hev' : ¬ EvAt log out.1 := fun h ↦
    hev out.1 h (hxt ▸ List.mem_map_of_mem (f := fun e ↦ e.1.1) hxm)
  have htg : tgtAt log out.1 = [(x.1.2, x.2)] := hxt ▸ tgtAt_eq_singleton log hnd hxm
  have hgf := (hI.2 out.1 hG hev').2 x.1.2 x.2 htg
  rw [hxa] at hgf
  obtain ⟨g1, g2, g3, g4⟩ := hgf
  obtain ⟨hcl, hcode, hz⟩ := g2 c (e.hash.trunc y) rfl
  obtain ⟨z, hzc⟩ := cellOf_isSome hlen P out.1 x.1.2 c
  obtain ⟨-, w, -, hselz, htw⟩ := hz z hzc
  have hxsT : encTw e G xs = some out.1 := encTw_cellOf hs hG hlt hxs
  have hzT : encTw e G z = some out.1 := encTw_cellOf hs hG hcl hzc
  have hinj' : ∀ {c₁ c₂ : ℕ} {m₁ m₂ : Msg} {x' : HashDomain}, c₁ < e.limit → c₂ < e.limit →
      cellOf e P out.1 m₁ c₁ = some x' → cellOf e P out.1 m₂ c₂ = some x' →
      (m₁, c₁) = (m₂, c₂) := fun h₁ h₂ hx₁ hx₂ ↦
    hinj P out.1 hG h₁ h₂ (encodeInput_injective hx₁ hx₂)
  have hzx : z ≠ xs := fun h ↦ hne (hinj' hcl hlt hzc (by rw [h]; exact hxs))
  have hax : m.ax xs = false := by
    by_contra hax'
    obtain ⟨c', hc'x, hc'⟩ := g3 xs hxsT (by simpa using hax')
    rcases hc' with hc' | ⟨d, hd⟩
    · have hc'' : c' < c := hc'
      obtain ⟨-, v, hv, hvc⟩ := g1 c' xs hc'' hc'x
      have hvy : v = y := by
        rcases hcons with h | h
        · change m.log xs = none at h
          rw [hv] at h
          cases h
        · change m.log xs = some y at h
          rw [hv] at h
          exact Option.some.inj h
      subst hvy
      rw [hcode] at hvc
      cases hvc
    · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hd)
      exact hne (hinj' hcl hlt hc'x hxs)
  refine (uJudge_flag xs m y).2 (Or.inr ⟨hax, by rw [hxsT]; exact Option.some_ne_none _, z, w,
    hselz, hzx, by rw [hzT, hxsT], fun z' hz' hz'T ↦ ?_, htw.symm⟩)
  obtain ⟨c'', d, hd, hc''⟩ := g4 z' (hz'T.trans hxsT) hz'
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hd)
  rw [hzc] at hc''
  exact (Option.some.inj hc'').symm

end game

/-! ## The bound of the game -/

section main

open OracleComp OracleSpec Common

variable {Par Tw Msg Dig Fn Out : Type} {CMsg : Fn → Type} [SampleableType Par]

/-- **The setup of the challenger makes no read.** -/
theorem setup_cost (e : CtrEnc Par Tw Msg Dig) (C : TwColl Par Tw Fn CMsg Out) (G : Tw → Prop)
    (Gc' : HashDomain → Prop) :
    QueryCostAtMost (encTcrCtrIn romWorld e C G).setup (gCost Gc') 0 :=
  Common.isWeightBound_liftM_probComp (gCost Gc') (fun _ ↦ rfl) ($ᵗ Par)

/-- **The reduction's setup keeps the invariant and the first phase.** -/
theorem pre_inv (e : CtrEnc Par Tw Msg Dig) (C : TwColl Par Tw Fn CMsg Out) (G : Tw → Prop)
    (n : ℕ) (hlen : LenOk e) (hs : EncSep e G)
    (hinj : ∀ P t, G t → Set.InjOn (e.hash.layout () P t) {x | x.2 < e.limit})
    (hCsep : ∀ l P t' mm P' t mc, G t → C.layout l P t' mm = e.hash.layout () P' t mc → t' = t)
    {S0 : Type} (oa : OracleComp (romWorld.Oracles + CtrSpec Par Tw Msg Dig Fn CMsg Out) S0)
    (hoa : QueryCostAtMost oa (gCostR (Gc e G) (R' := CtrSpec Par Tw Msg Dig Fn CMsg Out)) 0)
    (P : Par) {a : S0 × QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out)} {μ' : Option (Mem n)}
    (hrun : LiveRedRun (rl n) (upd e G n) ((encTcrCtrIn romWorld e C G).answer P) oa []
      (some mem₀) a μ') :
    ∀ m, μ' = some m → Inv e G n P a.2 m ∧ PhA e G n m := by
  have hred0 : (Caller.red : Caller) ≠ .answer := by intro h; cases h
  refine liveRedRun_inv_cost (upd e G n) (rl n) _ (gCostR (Gc e G))
    (fun log μ ↦ ∀ m, μ = some m → Inv e G n P log m ∧ PhA e G n m)
    (fun z log μ v hz hΦ m' hm' ↦ ?_) (fun q' log μ a μ' _ hΦ hrun m' hm' ↦ ?_) oa hoa hrun ?_
  · rcases μ with _ | m
    · cases hm'
    have hz' : encTw e G z = none := by
      by_contra h
      simp [gCostR, gCost, Gc, h] at hz
    obtain ⟨hI, hph⟩ := hΦ m rfl
    have h := inv_read hred0 hs hm' hI
    exact ⟨h.1, h.2 hz' hph⟩
  · rcases μ with _ | m
    · rw [liveRun_none_mode _ hrun] at hm'
      cases hm'
    obtain ⟨hI, hph⟩ := hΦ m rfl
    exact inv_answer C hs hlen hinj hCsep P q' hI hph hrun m' hm'
  · rintro m ⟨⟩
    refine ⟨⟨fun z hz ↦ by simp [mem₀, Mem.sel] at hz, fun t _ _ ↦
      ⟨fun _ x _ ↦ rfl, fun mm a h ↦ by simp [tgtAt, ctrTargets] at h⟩⟩, fun x _ hl ↦ ?_⟩
    simp [mem₀, Mem.log] at hl

omit [SampleableType Par] in
/-- **A reduction's algorithm without challenger calls keeps the invariant.** -/
theorem keep_inv (e : CtrEnc Par Tw Msg Dig) (G : Tw → Prop) (n : ℕ) (hs : EncSep e G) (P : Par)
    {ans : (q' : CtrQuery Tw Msg Fn CMsg) →
      OracleComp romWorld.Oracles ((CtrSpec Par Tw Msg Dig Fn CMsg Out).Range q')} {α : Type}
    (oa : OracleComp (romWorld.Oracles + CtrSpec Par Tw Msg Dig Fn CMsg Out) α)
    (hoa : QueryCostAtMost oa (ansCost (R' := CtrSpec Par Tw Msg Dig Fn CMsg Out)) 0)
    {log : QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out)} {μ : Option (Mem n)}
    {r : α × QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out)} {μ' : Option (Mem n)}
    (hrun : LiveRedRun (rl n) (upd e G n) ans oa log μ r μ')
    (hΦ : ∀ m, μ = some m → Inv e G n P log m) : ∀ m, μ' = some m → Inv e G n P r.2 m := by
  have hred0 : (Caller.red : Caller) ≠ .answer := by intro h; cases h
  refine liveRedRun_inv_cost (upd e G n) (rl n) ans ansCost
    (fun log μ ↦ ∀ m, μ = some m → Inv e G n P log m) (fun z log μ v _ hΦ m' hm' ↦ ?_)
    (fun q' log μ a μ' hc _ _ ↦ absurd hc (by simp [ansCost])) oa hoa hrun hΦ
  rcases μ with _ | m
  · cases hm'
  exact (inv_read hred0 hs hm' (hΦ m rfl)).1

/-- **The read program of the game is moded**: every leaf in a mode with at most `n` charged
reads and, on `true`, the judge's hit. -/
theorem modedP_encReads (e : CtrEnc Par Tw Msg Dig) (C : TwColl Par Tw Fn CMsg Out)
    (G : Tw → Prop) (n : ℕ) (hlen : LenOk e) (hs : EncSep e G)
    (hinj : ∀ P t, G t → Set.InjOn (e.hash.layout () P t) {x | x.2 < e.limit})
    (hCsep : ∀ l P t' mm P' t mc, G t → C.layout l P t' mm = e.hash.layout () P' t mc → t' = t)
    {Q : Type} {R : OracleSpec.{0, 0} Q} {St S0 A : Type}
    (pre : Unit → OracleComp (romWorld.Oracles + CtrSpec Par Tw Msg Dig Fn CMsg Out) S0)
    (adv : Unit → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) A)
    (st0 : Unit → S0 → St)
    (σ : Unit → HHandler romWorld R (CtrSpec Par Tw Msg Dig Fn CMsg Out) St)
    (post : Unit → S0 → A → St →
      OracleComp (romWorld.Oracles + CtrSpec Par Tw Msg Dig Fn CMsg Out) (Tw × Msg × ℕ))
    (hpre : QueryCostAtMost (pre ()) (gCostR (Gc e G) (R' := CtrSpec Par Tw Msg Dig Fn CMsg Out))
      0)
    (hσ : ∀ s qq, QueryCostAtMost (σ () s qq)
      (ansCost (R' := CtrSpec Par Tw Msg Dig Fn CMsg Out)) 0)
    (hpost : ∀ a f s, QueryCostAtMost (post () a f s)
      (ansCost (R' := CtrSpec Par Tw Msg Dig Fn CMsg Out)) 0)
    (Ju : Par → S0 → St × QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out) → Option (Mem n) → Prop)
    (hpreU : ∀ P a μ, LiveRedRun (rl n) (upd e G n) ((encTcrCtrIn romWorld e C G).answer P)
      (pre ()) [] (some mem₀) a μ → Ju P a.1 (st0 () a.1, a.2) μ)
    (hσU : ∀ P a st log μ qq, (∀ m, μ = some m → Inv e G n P log m) → Ju P a (st, log) μ →
      ∀ r μ', LiveRedRun (rl n) (upd e G n) ((encTcrCtrIn romWorld e C G).answer P)
        (σ () st qq) log μ r μ' → Ju P a (r.1.2, r.2) μ')
    (hpostU : ∀ P a f st log μ, (∀ m, μ = some m → Inv e G n P log m) → Ju P a (st, log) μ →
      ∀ r μ', LiveRedRun (rl n) (upd e G n) ((encTcrCtrIn romWorld e C G).answer P)
        (post () a f st) log μ r μ' → ∀ m, μ' = some m → m.cnt.val + 1 ≤ n) :
    Quantum.Xmss.Assembly.ModedP (okR e G n) (nxR e G n)
      (fun (p : Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) μ ↦ ∀ m, μ.1 = some m →
        m.cnt.val ≤ n ∧ (p.2.2 = true → m.flag = true)) (some mem₀, true)
      (Quantum.Xmss.Assembly.liftReadProg
        (toReads (upd e G n) (mixGame (encTcrCtrIn romWorld e C G) pre adv st0 σ post))) := by
  have hmix := modedP_mixGame (upd e G n) (rl n) (encTcrCtrIn romWorld e C G) pre adv st0 σ post
    mem₀ (fun _ μ ↦ μ = some mem₀)
    (fun P μ h ↦ liveRun_inv (fun _ ↦ True) (rl n) (upd e G n .setup) (· = some mem₀)
      (fun z μ v hz _ ↦ absurd trivial hz) _ (setup_cost e C G _) h rfl)
    (fun P a s μ ↦ (∀ m, μ = some m → Inv e G n P s.2 m) ∧ Ju P a s μ)
    (fun P μ h0 a μ' hrun ↦ by
      subst h0
      exact ⟨fun m hm ↦ (pre_inv e C G n hlen hs hinj hCsep _ hpre P hrun m hm).1,
        hpreU P a μ' hrun⟩)
    (fun P a st log μ qq hJ r μ' hrun ↦
      ⟨keep_inv e G n hs P _ (hσ st qq) hrun hJ.1, hσU P a st log μ qq hJ.1 hJ.2 r μ' hrun⟩)
    (fun P r μ ↦ ∀ m, μ = some m → Inv e G n P r.2 m ∧ m.cnt.val + 1 ≤ n)
    (fun P a f st log μ hJ r μ' hrun m hm ↦
      ⟨keep_inv e G n hs P _ (hpost a f st) hrun hJ.1 m hm,
        hpostU P a f st log μ hJ.1 hJ.2 r μ' hrun m hm⟩)
    (fun b μ ↦ ∀ m, μ = some m → m.cnt.val ≤ n ∧ (b = true → m.flag = true))
    (fun P r μ hpo b μ' hrun m' hm' ↦ by
      rcases μ with _ | m
      · rw [liveRun_none_mode _ hrun] at hm'
        cases hm'
      obtain ⟨hI, hc⟩ := hpo m rfl
      exact win_judge C hs hlen hinj hI hc hrun m' hm')
  have hphase := modedP_phase_mixGame (Gc e G) (encTcrCtrIn romWorld e C G) pre adv st0 σ post
    (setup_cost e C G _) (fun _ ↦ hpre) (fun _ s qq ↦ hσ s qq) (fun _ a f s ↦ hpost a f s)
  have hprod := modedP_prod (Gc e G) (upd e G n) (rl n) _ (some mem₀) true true (Or.inr rfl) hmix
    hphase
  exact modedP_toReads_prod (Gc e G) (upd e G n) (rl n) (fun c z ↦ recordsAt_upd c z)
    (fun c z hc ↦ upd_ne_answer hc z) (fun p m hm ↦ by cases hm) _ _ hprod

open scoped Classical in
/-- **EncTCR+C at the tweaks of `G` in the QROM, against a straight-line reduction.** Let the
encoding inputs be cells (`LenOk`), determine their tweak of `G` (`EncSep`) and, at a tweak of
`G`, their message and counter below the limit (`hinj`); let no input of the evaluation collection
be an encoding input at a tweak of `G` under another tweak (`hCsep`); let the truncation's fibers
have at most `F` values. Let the reduction make all its challenger calls in its setup `pre`, which
reads no encoding cell of a tweak of `G` (`Gc`), and let its handler and output make none. Let
`Ju` be an invariant of the reduction's live runs (every read answered by any value consistent
with the log `rl`, the memory moved by the policies `upd`) under which the output leaves at most
`n - 1` charged reads (reads of encoding cells of tweaks of `G` the challenger did not read,
`Mem.cnt`). Then, with `q` the adversary's calls of the oracle,
`probAvg ≤ (q √(6 F/N) + n √(gradeEta F))²`, `N = |HashOutput|`. -/
theorem encTcrCtrIn_probAvg_le (e : CtrEnc Par Tw Msg Dig) (C : TwColl Par Tw Fn CMsg Out)
    (G : Tw → Prop) (n : ℕ) {F : ℕ} (hlen : LenOk e) (hs : EncSep e G)
    (hinj : ∀ P t, G t → Set.InjOn (e.hash.layout () P t) {x | x.2 < e.limit})
    (hCsep : ∀ l P t' mm P' t mc, G t → C.layout l P t' mm = e.hash.layout () P' t mc → t' = t)
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F)
    {Q : Type} {R : OracleSpec.{0, 0} Q} {St S0 A : Type}
    (pre : Unit → OracleComp (romWorld.Oracles + CtrSpec Par Tw Msg Dig Fn CMsg Out) S0)
    (adv : Unit → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) A)
    (st0 : Unit → S0 → St)
    (σ : Unit → HHandler romWorld R (CtrSpec Par Tw Msg Dig Fn CMsg Out) St)
    (post : Unit → S0 → A → St →
      OracleComp (romWorld.Oracles + CtrSpec Par Tw Msg Dig Fn CMsg Out) (Tw × Msg × ℕ))
    {q : ℕ} (hq : ∀ a, IFreeM.IsChargeBound (adv () a) (cmdCharge hashCharge) q)
    (hpre : QueryCostAtMost (pre ()) (gCostR (Gc e G) (R' := CtrSpec Par Tw Msg Dig Fn CMsg Out))
      0)
    (hσ : ∀ s qq, QueryCostAtMost (σ () s qq)
      (ansCost (R' := CtrSpec Par Tw Msg Dig Fn CMsg Out)) 0)
    (hpost : ∀ a f s, QueryCostAtMost (post () a f s)
      (ansCost (R' := CtrSpec Par Tw Msg Dig Fn CMsg Out)) 0)
    (Ju : Par → S0 → St × QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out) → Option (Mem n) → Prop)
    (hpreU : ∀ P a μ, LiveRedRun (rl n) (upd e G n) ((encTcrCtrIn romWorld e C G).answer P)
      (pre ()) [] (some mem₀) a μ → Ju P a.1 (st0 () a.1, a.2) μ)
    (hσU : ∀ P a st log μ qq, (∀ m, μ = some m → Inv e G n P log m) → Ju P a (st, log) μ →
      ∀ r μ', LiveRedRun (rl n) (upd e G n) ((encTcrCtrIn romWorld e C G).answer P)
        (σ () st qq) log μ r μ' → Ju P a (r.1.2, r.2) μ')
    (hpostU : ∀ P a f st log μ, (∀ m, μ = some m → Inv e G n P log m) → Ju P a (st, log) μ →
      ∀ r μ', LiveRedRun (rl n) (upd e G n) ((encTcrCtrIn romWorld e C G).answer P)
        (post () a f st) log μ r μ' → ∀ m, μ' = some m → m.cnt.val + 1 ≤ n) :
    romWorld.probAvg ((encTcrCtrIn romWorld e C G).game fun p ↦
        slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) ≤
      (q * (6 * ((F : ℝ≥0∞) / Fintype.card HashOutput)) ^ (2⁻¹ : ℝ) +
        n * ENNReal.ofReal (gradeEta HashOutput F) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hreads := modedP_encReads e C G n hlen hs hinj hCsep pre adv st0 σ post hpre hσ hpost Ju
    hpreU hσU hpostU
  refine (probAvg_game_slRed_le_hw (encTcrCtrIn romWorld e C G) pre adv st0 σ post (upd e G n)
    mem₀).trans ?_
  exact evalDistMap_le_of_moded hF _ (isChargeBound_toReads (upd e G n)
    (isChargeBound_mixGame (encTcrCtrIn romWorld e C G) pre adv st0 σ post fun _ a ↦ hq a))
    (fun b μ ↦ ∀ m, μ = some m → m.cnt.val ≤ n ∧ (b = true → m.flag = true))
    (fun b m h ↦ h m rfl) hreads

open scoped Classical in
/-- **EncTCR+C at the tweaks of `G`, with an output of `k` charged reads at most**: as
`encTcrCtrIn_probAvg_le`, the handler's live runs keeping no charged read (re-reads of cells the
challenger read, or reads off the classes) and the output reading at most `k` encoding cells of
tweaks of `G` on every path: `probAvg ≤ (q √(6 F/N) + (k + 1) √(gradeEta F))²` (the judge's read
is the last charged read). -/
theorem encTcrCtrIn_probAvg_le_of_post (e : CtrEnc Par Tw Msg Dig)
    (C : TwColl Par Tw Fn CMsg Out) (G : Tw → Prop) (k : ℕ) {F : ℕ} (hlen : LenOk e)
    (hs : EncSep e G)
    (hinj : ∀ P t, G t → Set.InjOn (e.hash.layout () P t) {x | x.2 < e.limit})
    (hCsep : ∀ l P t' mm P' t mc, G t → C.layout l P t' mm = e.hash.layout () P' t mc → t' = t)
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F)
    {Q : Type} {R : OracleSpec.{0, 0} Q} {St S0 A : Type}
    (pre : Unit → OracleComp (romWorld.Oracles + CtrSpec Par Tw Msg Dig Fn CMsg Out) S0)
    (adv : Unit → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) A)
    (st0 : Unit → S0 → St)
    (σ : Unit → HHandler romWorld R (CtrSpec Par Tw Msg Dig Fn CMsg Out) St)
    (post : Unit → S0 → A → St →
      OracleComp (romWorld.Oracles + CtrSpec Par Tw Msg Dig Fn CMsg Out) (Tw × Msg × ℕ))
    {q : ℕ} (hq : ∀ a, IFreeM.IsChargeBound (adv () a) (cmdCharge hashCharge) q)
    (hpre : QueryCostAtMost (pre ()) (gCostR (Gc e G) (R' := CtrSpec Par Tw Msg Dig Fn CMsg Out))
      0)
    (hσ : ∀ s qq, QueryCostAtMost (σ () s qq)
      (ansCost (R' := CtrSpec Par Tw Msg Dig Fn CMsg Out)) 0)
    (hpost : ∀ a f s, QueryCostAtMost (post () a f s)
      (ansCost (R' := CtrSpec Par Tw Msg Dig Fn CMsg Out)) 0)
    (hpostk : ∀ a f s, QueryCostAtMost (post () a f s)
      (gCostR (Gc e G) (R' := CtrSpec Par Tw Msg Dig Fn CMsg Out)) k)
    (hσfree : ∀ P st log μ qq, (∀ m, μ = some m → Inv e G (k + 1) P log m) →
      (∀ m, μ = some m → m.cnt.val = 0) →
      ∀ r μ', LiveRedRun (rl (k + 1)) (upd e G (k + 1)) ((encTcrCtrIn romWorld e C G).answer P)
        (σ () st qq) log μ r μ' → ∀ m, μ' = some m → m.cnt.val = 0) :
    romWorld.probAvg ((encTcrCtrIn romWorld e C G).game fun p ↦
        slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) ≤
      (q * (6 * ((F : ℝ≥0∞) / Fintype.card HashOutput)) ^ (2⁻¹ : ℝ) +
        (k + 1 : ℕ) * ENNReal.ofReal (gradeEta HashOutput F) ^ (2⁻¹ : ℝ)) ^ 2 := by
  refine encTcrCtrIn_probAvg_le e C G (k + 1) hlen hs hinj hCsep hF pre adv st0 σ post hq hpre
    hσ hpost (fun _ _ _ μ ↦ ∀ m, μ = some m → m.cnt.val = 0) (fun P a μ hrun ↦ ?_)
    (fun P a st log μ qq hI hJ r μ' hrun ↦ hσfree P st log μ qq hI hJ r μ' hrun)
    (fun P a f st log μ _ hJ r μ' hrun m hm ↦ ?_)
  · refine liveRedRun_inv_cost (upd e G (k + 1)) (rl (k + 1)) _ (gCostR (Gc e G))
      (fun _ μ ↦ ∀ m, μ = some m → m.cnt.val = 0) (fun z log μ v hz hΦ m' hm' ↦ ?_)
      (fun q' log μ a μ' _ hΦ hrun' ↦ ?_) (pre ()) hpre hrun (by rintro m ⟨⟩; rfl)
    · rcases μ with _ | m
      · cases hm'
      have hz' : encTw e G z = none := by
        by_contra h
        simp [gCostR, gCost, Gc, h] at hz
      obtain ⟨rfl, -⟩ := stepRd_some hm'
      have hch : ¬ Charged e G (k + 1) m z := fun h ↦ h.1 hz'
      change (cntAfter e G (k + 1) m z).val = 0
      simp only [cntAfter, hch, ↓reduceIte]
      exact hΦ m rfl
    · exact liveRun_inv_all (fun μ ↦ ∀ m, μ = some m → m.cnt.val = 0) (fun z μ v hΦ' m' hm' ↦ by
        rcases μ with _ | m
        · cases hm'
        obtain ⟨rfl, -⟩ := stepRd_some hm'
        exact hΦ' m rfl) _ hrun' hΦ
  · have h := liveRedRun_count (upd e G (k + 1)) (rl (k + 1)) _ (gCostR (Gc e G))
      (fun μ ↦ μ.elim 0 fun m ↦ m.cnt.val) (fun z μ v ↦ ?_) (post () a f st) (hpostk a f st)
      (hpost a f st) hrun
    · rw [hm] at h
      have h0 : (μ.elim 0 fun m ↦ m.cnt.val) = 0 := by
        rcases μ with _ | m₀
        · rfl
        · exact hJ m₀ rfl
      have h1 := h.1
      change m.cnt.val ≤ (μ.elim 0 fun m ↦ m.cnt.val) + k at h1
      rw [h0] at h1
      omega
    · rcases μ with _ | m
      · exact Nat.zero_le _
      rcases hst : stepRd (rl (k + 1)) (upd e G (k + 1) .red z) z (some m) v with _ | m'
      · exact Nat.zero_le _
      obtain ⟨rfl, -⟩ := stepRd_some hst
      change (cntAfter e G (k + 1) m z).val ≤ m.cnt.val + gCostR (Gc e G) (.inl (.inr z))
      unfold cntAfter
      split_ifs with hch
      · have hg : gCostR (Gc e G) (R' := CtrSpec Par Tw Msg Dig Fn CMsg Out) (.inl (.inr z)) =
            1 := by simp [gCostR, gCost, Gc, hch.1]
        rw [hg]
        change min (m.cnt.val + 1) (k + 1 + 1) ≤ _
        omega
      · omega

end main

end Quantum.StdModel.Qrom.EncTcr

end
