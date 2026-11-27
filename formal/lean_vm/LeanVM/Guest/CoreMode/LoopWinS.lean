/-
  LeanVM.Guest.CoreMode.LoopWinS

  A long loop helper's code windows (`CWins`) over slices of its code chunks: no window walks the
  code before it.
-/

module

public import LeanVM.Guest.CoreMode.LoopWin
public import LeanVM.Guest.Bridge.ProgAlSlice

/-!
# The code windows over slices

`CWins` hands each window `slice code a b` of the flattened chunks, which the kernel flattens and
walks up to offset `a` every time. `cwOkS` hands it the slice of the chunks between two cuts
(`Bridge.slice`, built from the chunks it touches) and checks that it is `b - a` long; at the cut of
offset `a` (read off the chunks' lengths, stated once per function) it is the window over the
flattened chunks (`cw_of_slice`), so a window's statement, and the chain of them, stay as they are.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest.Bridge (PCut restL sliceOk lenTR)

@[expose] public section

/-- **A code window over a slice**: the chunks `C` from cut `ca`, at offset `a`, to cut `cb`, at
offset `b`, pass the frame walk's tables' check and the jump table's reads' check. -/
noncomputable def cwOkS (Cf : CFun) (E : Mode.Env) (ml : List (ℕ × ℕ)) (C : List (List OffsetInstruction))
    (a b : ℕ) (ca cb : PCut) : Bool :=
  sliceOk C ca cb && Nat.beq (lenTR (Bridge.slice C ca cb) a) b && tgtGo Cf ml a (Bridge.slice C ca cb) &&
    jtdGo Cf E ml [] (Bridge.slice C ca cb)

end

public section

/-- **A code window from a slice of the chunks**: at the offset of cut `ca` (from the chunks'
lengths), the window over the flattened chunks is the slice's. -/
theorem cw_of_slice {Cf : CFun} {E : Mode.Env} {ml : List (ℕ × ℕ)} {C : List (List OffsetInstruction)}
    {a b : ℕ} {ca cb : PCut} (ha : ((C.map List.length).take ca.1).sum + ca.2 = a)
    (h : cwOkS Cf E ml C a b ca cb = true) :
    (tgtGo Cf ml a (slice C.flatten a b) && jtdGo Cf E ml [] (slice C.flatten a b)) = true := by
  simp only [cwOkS, Bool.and_eq_true, Nat.beq_eq, Bridge.lenTR_eq] at h
  obtain ⟨⟨⟨hs, hb⟩, ht⟩, hj⟩ := h
  have hd : C.flatten.drop a = restL C ca := by
    have hC : C.flatten = (C.take ca.1).flatten ++ (C.drop ca.1).flatten := by
      rw [← List.flatten_append, List.take_append_drop]
    rw [← ha, restL, ← List.map_take, ← List.length_flatten, hC, ← List.drop_drop, List.drop_left]
  have hsl : slice C.flatten a b = Bridge.slice C ca cb := by
    rw [slice, hd, ← Bridge.slice_rest hs, show b - a = (Bridge.slice C ca cb).length by omega, List.take_left]
  rw [hsl, ht, hj]; rfl

end

end LeanVM.Guest.CoreMode
