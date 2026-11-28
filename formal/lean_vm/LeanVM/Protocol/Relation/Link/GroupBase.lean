/-
  LeanVM.Protocol.Relation.Link.GroupBase

  The link's drawn group: its doom, counted through a polynomial that is nonzero only where doom
  holds, and the Keccak defect, which dooms every draw.
-/

module

public import LeanVM.Protocol.Relation.Link.Summand
public import LeanVM.Protocol.Relation.Link.GroupPoly

/-!
# The drawn group's doom

`GroupDoomAt v`: the doom `LinkSummandFacts.group` counts the failures of, at `v = (θ_0, drawn)`.
It holds when the index claim is not the index side's sum (`groupDoom_of_claim`), when a weight
`linkB … r i` is nonzero at some index point `r` (`groupDoom_of_B`), or when the Keccak defect is
nonzero (`groupDoom_of_keccak`), which `¬ KeccakRel` gives (`keccakCarry_of_not_rel`).
`card_not_doom_le`: a polynomial of degree at most `D`, nonzero somewhere and nonzero only where
doom holds, leaves at most `D·|E|^N` draws undoomed.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Link
open LeanVM.Protocol.Hotwire Finset

@[expose] public section

open Classical

/-- **The drawn group's doom** at `v = (θ_0, drawn)`, as `LinkSummandFacts.group` reads it. -/
def GroupDoomAt (layout : Layout) {μ : ℕ} (q : Column μ) (chunks : Chunks)
    (v : Fin (linkDrawn layout chunks + 1) → E) : Prop :=
  RoundDoom True (linkIdx layout chunks q ((List.ofFn v).headD 0) (List.ofFn v).tail)
    (IndexCarry layout q chunks (linkB layout chunks q) ((List.ofFn v).headD 0) (List.ofFn v).tail)
    (indexClaim layout chunks (List.ofFn v).tail) []

/-- **The count from a polynomial witness.** -/
theorem card_not_doom_le {N : ℕ} {Doom : (Fin (N + 1) → E) → Prop} {f : (Fin (N + 1) → E) → E}
    {D B : ℕ} (hf : PolyFn (N + 1) D f) {x0 : Fin (N + 1) → E} (hx0 : f x0 ≠ 0)
    (hdoom : ∀ v, f v ≠ 0 → Doom v) (hB : D ≤ B) :
    (univ.filter fun v ↦ ¬ Doom v).card ≤ B * Fintype.card E ^ N := by
  refine (card_le_card fun v hv ↦ ?_).trans ((hf.card_zero_le hx0).trans ?_)
  · simp only [mem_filter, mem_univ, true_and] at hv ⊢
    by_contra h
    exact hv (hdoom v h)
  · rw [Nat.add_sub_cancel]
    exact Nat.mul_le_mul_right _ hB

/-- A false index claim dooms the draw. -/
theorem groupDoom_of_claim {layout : Layout} {μ : ℕ} {q : Column μ} {chunks : Chunks}
    {v : Fin (linkDrawn layout chunks + 1) → E}
    (h : indexClaim layout chunks (List.ofFn v).tail ≠
      linkIdx layout chunks q ((List.ofFn v).headD 0) (List.ofFn v).tail []) :
    GroupDoomAt layout q chunks v :=
  .inl ⟨trivial, h⟩

/-- A weight nonzero at some index point dooms the draw. -/
theorem groupDoom_of_B {layout : Layout} {μ : ℕ} {q : Column μ} {chunks : Chunks}
    {v : Fin (linkDrawn layout chunks + 1) → E} (i : Fin 5) (r : List E) (hr : r.length = chunks.width)
    (h : linkB layout chunks q ((List.ofFn v).headD 0) (List.ofFn v).tail r i ≠ 0) :
    GroupDoomAt layout q chunks v :=
  .inr (.inl ⟨i, r, by simpa using hr, by simpa using h⟩)

/-- The Keccak defect dooms every draw. -/
theorem groupDoom_of_keccak {layout : Layout} {μ : ℕ} {q : Column μ} {chunks : Chunks}
    (h : KeccakCarry layout q []) (v : Fin (linkDrawn layout chunks + 1) → E) :
    GroupDoomAt layout q chunks v :=
  .inr (.inr h)

theorem lane_ofLane (w : UInt64) : K.lane (K.ofLane w) = w := rfl

/-- **`¬ KeccakRel` leaves the defect nonzero**: some lane's defect is nonzero on some row, so its
extension is nonzero at that row's Boolean point. -/
theorem keccakCarry_of_not_rel {layout : Layout} {μ : ℕ} {q : Column μ}
    (hK : ¬ KeccakRel layout q) : KeccakCarry layout q [] := by
  unfold KeccakRel at hK
  push Not at hK
  obtain ⟨row, hrow, hne⟩ := hK
  have hl : ∃ l < keccakStateLanes, Keccak.lane (keccakMid layout q row) l ≠
      Keccak.lane (keccakRounds (keccakInput layout q row) 0 keccakDepth) l := by
    by_contra hc
    push Not at hc
    refine hne (Vector.ext fun i hi ↦ ?_)
    have := hc i hi
    simpa [Keccak.lane, hi] using this
  obtain ⟨l, hl, hlne⟩ := hl
  have hd : keccakDefect layout q l row ≠ 0 := by
    unfold keccakDefect
    rw [sub_ne_zero]
    intro h
    exact hlne (by simpa [lane_ofLane] using congrArg K.lane (ofK_injective h))
  have hkh := keccakHeight_le_linkRows layout
  refine .inl ⟨⟨l, hl⟩, boolL (keccakHeight layout) row ++
    List.replicate (linkRowVars layout - keccakHeight layout) 0, ?_, ?_⟩
  · simp [length_boolL, linkRowVars]
    omega
  · simp only [List.nil_append, keccakDefectRow]
    rw [List.take_append_of_le_length (by rw [length_boolL]), List.take_of_length_le
      (by rw [length_boolL]), rowMle_boolL hrow]
    exact hd

end

end LeanVM.Protocol.Relation
