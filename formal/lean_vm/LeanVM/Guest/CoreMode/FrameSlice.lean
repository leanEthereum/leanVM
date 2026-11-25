/-
  LeanVM.Guest.CoreMode.FrameSlice

  A long function's frame walk checked in windows over slices of its code chunks: no window walks
  the code before it.
-/

module

public import LeanVM.Guest.CoreMode.FrameWin
public import LeanVM.Guest.Bridge.ProgAlSlice

/-!
# The frame walk's windows over slices

`frameWin` (`Frame.lean`) hands each window the whole code and drops the offsets before it, which the
kernel walks every time. `frameWinS` hands it the slice of the code's chunks between two cuts
(`Bridge.slice`) and checks its length; a chain of such windows from the chunks' start (`ChainFS`)
gives each window's `frameWin` (`chainFS_wins`), what `frameAcc_of_wins` takes.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Exec
open LeanVM.Guest.Bridge (PCut slice sliceOk restL slice_rest lenTR lenTR_eq)

@[expose] public section

/-- `frameWin`'s check of a window, over the window's instructions `piece`. -/
noncomputable def frameWinOn (Fn : FFun) (piece : List OffsetInstruction) (a b : ℕ) : Bool :=
  (match Fn.cutAt a with
    | some c => some (cutSt c)
    | none => if a = 0 then some (some (entryF Fn), []) else none).elim false fun S ↦
  match frameRun Fn piece a Fn.hints S.1 S.2 with
  | some (cur, pend) =>
    if b < Fn.len then (cutF Fn b cur pend).isSome
    else match cur, pend with
      | none, [] => true
      | _, _ => false
  | none => false

/-- **A window of the frame walk over a slice**: offsets `a` to `b`, the slice of the code's chunks
`C` between the cuts `ca` and `cb`, of length `b - a`. -/
noncomputable def frameWinS (Fn : FFun) (C : List (List OffsetInstruction)) (ca cb : PCut) (a b : ℕ) : Bool :=
  sliceOk C ca cb && Nat.ble a b && Nat.beq (lenTR (slice C ca cb) 0) (b - a) && frameWinOn Fn (slice C ca cb) a b

/-- **A chain of windows over slices**, from a cut at an offset. -/
def ChainFS (Fn : FFun) (C : List (List OffsetInstruction)) : PCut × ℕ → List (PCut × ℕ) → Prop
  | _, [] => True
  | (c, a), (c', b) :: ks => frameWinS Fn C c c' a b = true ∧ ChainFS Fn C (c', b) ks

/-- The windows' offsets, from `a`. -/
def winPairs : ℕ → List (PCut × ℕ) → List (ℕ × ℕ)
  | _, [] => []
  | a, (_, b) :: ks => (a, b) :: winPairs b ks

end

public section

theorem frameWin_eq (Fn : FFun) (code : List OffsetInstruction) (a b : ℕ) :
    frameWin Fn code a b = frameWinOn Fn ((code.drop a).take (b - a)) a b := rfl

/-- A window over a slice is the window over the code, from a cut at its first offset. -/
theorem frameWin_of_S {Fn : FFun} {C : List (List OffsetInstruction)} {ca cb : PCut} {a b : ℕ}
    (h : frameWinS Fn C ca cb a b = true) (hr : restL C ca = C.flatten.drop a) :
    frameWin Fn C.flatten a b = true ∧ restL C cb = C.flatten.drop b := by
  simp only [frameWinS, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, lenTR_eq, Nat.add_zero] at h
  obtain ⟨⟨⟨hs, hab⟩, hl⟩, hw⟩ := h
  have he := slice_rest hs
  rw [hr] at he
  refine ⟨?_, ?_⟩
  · rw [frameWin_eq, ← he, List.take_left' hl]
    exact hw
  · have := congrArg (List.drop (b - a)) he
    rw [List.drop_left' hl, List.drop_drop, show a + (b - a) = b by omega] at this
    exact this

/-- **A chain of windows over slices gives each window's `frameWin`.** -/
theorem chainFS_wins {Fn : FFun} {C : List (List OffsetInstruction)} :
    ∀ (ks : List (PCut × ℕ)) (c : PCut) (a : ℕ), ChainFS Fn C (c, a) ks → restL C c = C.flatten.drop a →
      ∀ p ∈ winPairs a ks, frameWin Fn C.flatten p.1 p.2 = true
  | [], _, _, _, _ => by simp [winPairs]
  | (c', b) :: ks, c, a, ⟨hw, hc⟩, hr => by
    obtain ⟨h1, h2⟩ := frameWin_of_S hw hr
    intro p hp
    simp only [winPairs, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h1
    · exact chainFS_wins ks c' b hc h2 p hp

theorem restL_zero {α : Type} (C : List (List α)) : restL C (0, 0) = C.flatten.drop 0 := by
  simp [restL]

end

end LeanVM.Guest.CoreMode
