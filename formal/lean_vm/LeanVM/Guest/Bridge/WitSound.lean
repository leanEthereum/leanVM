/-
  LeanVM.Guest.Bridge.WitSound

  What the witness hints' data check gives on a path: each witness hint's destination at its
  certificate cells, and a pinned heap pointer's atoms on the path.
-/

module

public import LeanVM.Guest.Bridge.WitDefs
public import LeanVM.Guest.Bridge.Pair

/-!
# The witness check on a path

`witChk_sound`: on a path of a checked body, a witness hint's stack values, and its heap pointer
unless at a hint-only cell, are at their cells of the context's map in the frame. `ptrOk_sound`: a heap
pointer the spine pins is allocated on the path or loaded through by it, and loaded through at
offset `0` or written through from offset `0` by a heap hint on it.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B2C

public section

variable {σ : Val}

/-- **What the witness check gives of a witness hint on a path**: a stack destination's values,
and a heap destination's pointer unless at a hint-only cell, at their cells in the frame. -/
theorem witChk_sound {X : AlignCtx} {n : ℕ} {body : List Stmt}
    (hc : witChk X n body = true) {es : List Ev} {vs : List V} (hw : walk σ body = .ret es vs)
    {S : String} {d : Dest} (hh : Ev.atom (.hint (.witness S d)) ∈ es) :
    ∀ v ∈ destUses d, (X.extra.lookup v.idx = none ∧ v.idx < 2 ^ 30 ∧ 2 ≤ X.locAt v.idx ∧
      X.locAt v.idx < n) ∨ (∃ p off len, d = .heap p off len ∧ v = p ∧ (X.extra.lookup p.idx).isSome) := by
  have hcell : ∀ v, cellOkX X n v = true →
      X.extra.lookup v.idx = none ∧ v.idx < 2 ^ 30 ∧ 2 ≤ X.locAt v.idx ∧ X.locAt v.idx < n := fun v hv ↦ by
    simp only [cellOkX, Bool.and_eq_true, Option.isNone_iff_eq_none, Nat.ble_eq, Nat.blt_eq] at hv
    exact ⟨hv.1.1.1, hv.1.1.2, hv.1.2, hv.2⟩
  unfold witChk at hc
  rw [AlignCtx.seq_eq] at hc
  have hok := blockAll_sound _ body hc _ (walk_atoms body (by rw [hw]; exact hh))
  intro v hv
  cases d with
  | stack ws =>
    simp only [witAtomOk, List.all_eq_true] at hok
    exact Or.inl (hcell v (hok v hv))
  | heap p off len =>
    simp only [destUses, List.mem_singleton] at hv
    subst hv
    simp only [witAtomOk, Bool.or_eq_true] at hok
    rcases hok with h | h
    · exact Or.inl (hcell v h)
    · exact Or.inr ⟨v, off, len, rfl, rfl, h⟩

/-- **A pinned heap pointer on a path**: allocated on it or loaded through by it, and loaded
through at offset `0` or written through from offset `0` by a heap hint on it. -/
theorem ptrOk_sound {body : List Stmt} {p : V} (hp : ptrOk (spine body) p = true) {es : List Ev} {vs : List V}
    (hw : walk σ body = .ret es vs) :
    (p ∈ allocDsts es ∨ ∃ d off, Ev.atom (.load d p off) ∈ es) ∧
      ((∃ d, Ev.atom (.load d p 0) ∈ es) ∨ ∃ a len, Ev.atom a ∈ es ∧ atomHeapDest? a = some (p, 0, len + 1)) := by
  simp only [ptrOk, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at hp
  obtain ⟨h1, h2⟩ := hp
  refine ⟨?_, ?_⟩
  · rcases h1 with ⟨a, ha, hal⟩ | ⟨a, ha, hl⟩
    · exact Or.inl (allocDsts_of_mem (spine_on_path body hw a ha) hal)
    · cases a with
      | load d q off =>
        simp only [loadPtr, Option.some.injEq] at hl
        subst hl
        exact Or.inr ⟨d, off, spine_on_path body hw _ ha⟩
      | _ => simp [loadPtr] at hl
  · rcases h2 with ⟨a, ha, hl⟩ | ⟨a, ha, hh⟩
    · cases a with
      | load d q off =>
        cases off with
        | zero =>
          simp only [loadPtr0, Option.some.injEq] at hl
          subst hl
          exact Or.inl ⟨d, spine_on_path body hw _ ha⟩
        | succ _ => simp [loadPtr0] at hl
      | _ => simp [loadPtr0] at hl
    · unfold heapPtr0 at hh
      split at hh
      · rename_i q len hq
        cases hh
        exact Or.inr ⟨a, len, spine_on_path body hw a ha, hq⟩
      · cases hh

end

end LeanVM.Guest.Bridge
