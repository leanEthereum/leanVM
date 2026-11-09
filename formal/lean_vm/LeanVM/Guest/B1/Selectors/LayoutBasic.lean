/-
  LeanVM.Guest.B1.Selectors.LayoutBasic

  Layouts of words for B1-c's completeness: runs `(e, ws)` (word `j` at `g^(e + j)`), the memory
  holding them, and a reader that holds them, to evaluate a body on before the memory is known.
-/

module

public import LeanVM.Guest.B1.Fwd.Canon
public import LeanVM.Guest.B1.Tables.Basic

/-!
# Layouts

A layout is a list of runs `(e, ws)`: word `j` of `ws` at the address `g^(e + j)`. `MemLay rd L`:
the memory holds every run (`TbReadsAt` at `ofK (g^e)`). `layRd L`: a reader answering every
address of a run with one of its words (by choice); on a memory holding `L` it answers as the
memory does (`layRd_agree`). An honest body is evaluated on `layRd` of its inputs (`Fwd.ev`), and
its loads of them hold on every memory holding them (`load_of_layRd`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- Runs of words: word `j` of `(e, ws)` at `g^(e + j)`. -/
abbrev TLay : Type := List (ℕ × List E)

/-- The memory holds the layout. -/
def MemLay (rd : Reader) (L : TLay) : Prop := ∀ q ∈ L, TbReadsAt rd (ofK (addressOfIndex q.1)) q.2

theorem memLay_append {rd : Reader} {L L' : TLay} :
    MemLay rd (L ++ L') ↔ MemLay rd L ∧ MemLay rd L' := by
  simp only [MemLay, List.mem_append]
  exact ⟨fun h => ⟨fun q hq => h q (Or.inl hq), fun q hq => h q (Or.inr hq)⟩,
    fun h q hq => hq.elim (h.1 q) (h.2 q)⟩

theorem tb_addr_ofK (e j : ℕ) : (ofK (addressOfIndex e)).limb 0 * addressOfIndex j = addressOfIndex
    (e + j) := by
  rw [limb_ofK]; exact (pow_add _ _ _).symm

theorem tb_isInK_ofK (a : K) : IsInK (ofK a) := by
  simp [IsInK]

/-- An address of the layout. -/
def InLay (L : TLay) (a : K) : Prop := ∃ q ∈ L, ∃ j < q.2.length, a = addressOfIndex (q.1 + j)

open Classical in
/-- A reader holding the layout: an address of a run, one of its words there; else nothing. -/
noncomputable def layRd (L : TLay) : Reader := fun a =>
  if h : InLay L a then
    some ((Classical.choose h).2.getD (Classical.choose (Classical.choose_spec h).2) 0)
  else none

theorem memLay_read {rd : Reader} {L : TLay} (hm : MemLay rd L) {q : ℕ × List E} (hq : q ∈ L)
    {j : ℕ} (hj : j < q.2.length) : rd (addressOfIndex (q.1 + j)) = some (q.2.getD j 0) := by
  have := (hm q hq j hj).2
  rw [tb_addr_ofK] at this
  rw [this, List.getD_eq_getElem _ _ hj]

/-- **On a memory holding the layout, `layRd` answers its addresses as the memory does.** -/
theorem layRd_agree {rd : Reader} {L : TLay} (hm : MemLay rd L) {a : K} (ha : InLay L a) :
    layRd L a = rd a := by
  unfold layRd
  simp only [ha, ↓reduceDIte]
  obtain ⟨hqL, hex⟩ := Classical.choose_spec ha
  obtain ⟨hj, he⟩ := Classical.choose_spec hex
  conv_rhs => rw [he]
  exact (memLay_read hm hqL hj).symm

/-- Runs pairwise apart. -/
def DisjLay (L : TLay) : Prop :=
  L.Pairwise fun q q' => q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1

/-- Runs below the order of `g`. -/
def LowLay (L : TLay) : Prop := ∀ q ∈ L, q.1 + q.2.length < 2 ^ 64 - 1

theorem tb_pairwise_mem {α : Type} {R : α → α → Prop} :
    ∀ {L : List α}, L.Pairwise R → ∀ {a b : α}, a ∈ L → b ∈ L → a ≠ b → R a b ∨ R b a
  | [], _, _, _, ha, _, _ => absurd ha (by simp)
  | x :: L, h, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with hax | ha' <;> rcases List.mem_cons.mp hb with hbx | hb'
    · exact absurd (hax.trans hbx.symm) hne
    · subst hax; exact Or.inl (h.1 b hb')
    · subst hbx; exact Or.inr (h.1 a ha')
    · exact tb_pairwise_mem h.2 ha' hb' hne

theorem lay_same {L : TLay} (hd : DisjLay L) (hl : LowLay L) {q q' : ℕ × List E} (hq : q ∈ L)
    (hq' : q' ∈ L) {j j' : ℕ} (hj : j < q.2.length) (hj' : j' < q'.2.length)
    (he : addressOfIndex (q.1 + j) = addressOfIndex (q'.1 + j')) : q'.2.getD j' 0 = q.2.getD j
        0 := by
  have hq1 := hl q hq
  have hq1' := hl q' hq'
  have hij : q.1 + j = q'.1 + j' := gpow_injOn (by simp only [Set.mem_Iio]; omega)
    (by simp only [Set.mem_Iio]; omega) he
  have hqq : q' = q := by
    by_contra hne
    rcases tb_pairwise_mem hd hq' hq hne with h | h <;> omega
  subst hqq
  have hjj : j' = j := by omega
  rw [hjj]

/-- **`layRd` holds a layout of runs apart, below the order of `g`.** -/
theorem memLay_layRd {L : TLay} (hd : DisjLay L) (hl : LowLay L) : MemLay (layRd L) L := by
  intro q hq j hj
  refine ⟨tb_isInK_ofK _, ?_⟩
  rw [tb_addr_ofK]
  have ha : InLay L (addressOfIndex (q.1 + j)) := ⟨q, hq, j, hj, rfl⟩
  unfold layRd
  simp only [ha, ↓reduceDIte]
  obtain ⟨hqL, hex⟩ := Classical.choose_spec ha
  obtain ⟨hj', he⟩ := Classical.choose_spec hex
  rw [lay_same hd hl hq hqL hj hj' he, List.getD_eq_getElem _ _ hj]

/-- **A word of a run read on one memory holding it is the word on any other.** -/
theorem lay_transfer {rd rd' : Reader} {L : TLay} (hm : MemLay rd L) (hm' : MemLay rd' L)
    {q : ℕ × List E} (hq : q ∈ L) {i : ℕ} (hi : i < q.2.length) {v : E}
    (h : LoadHolds rd (ofK (addressOfIndex q.1)) i v) : LoadHolds rd' (ofK (addressOfIndex q.1)) i
        v := by
  have e1 := tb_loadHolds_unique h (hm q hq i hi)
  rw [e1]; exact hm' q hq i hi

end
end LeanVM.Guest.B1.Tables
