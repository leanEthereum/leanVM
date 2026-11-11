/-
  LeanVM.Guest.B1.Place.Lp

  `level_positions` complete placed, at every specialization of `lpTable`: the statement.
-/

module

public import LeanVM.Guest.B1.Place.HelperAt
public import LeanVM.Guest.B1.Bits.QueryWindowsAt
public import LeanVM.Guest.B1.Whir.CLp
public import LeanVM.Guest.B1.Whir.HelperAll
public import LeanVM.Guest.Lift.OsCallees

/-!
# `level_positions`, placed

`level_positions__L{sq}_L{d}_L{cd}(cap0 .. cap4, positions, win_ptrs, tabs)` (`lpBody sq loop`,
its loop `lpLoopBody d cd loop`) squeezes `sq` challenges from the capacity `cap` (the chain
`sqCaps cap`, challenge `j` is `sqChal cap j`), decodes challenge `j`'s `192 / d` positions and
windows by `decode_query_windows__L{d}_L{cd}` (`qwDecName d cd`) into `positions·g^(j·(192/d))`
and `win_ptrs·g^(j·(192/d))`, and returns the last capacity `sqCaps cap sq`. Its squeeze run
`sqz` is its own `HeapBuf`; decoder `j`'s windows are a frame run of the decoder's frame
(`qwRunL`), which the caller's window pointers name (`qwPtrAt`). So where the decoders' frames lie
is part of the statement: `dfp fp j`, decoder `j`'s frame pointer when the helper is entered at
`fp`, a function of the frame sizes and certificates alone.

**The statement** (`LpAtO`): with the helper at `fp`, on every memory holding the caller's words
`Lin fp` (the window table at `tabs`, challenge `j`'s positions `qwPosOf d (sqChal cap j) i` at
`positions` and the pointers `qwPtrAt … (dfp fp j) … i` at `win_ptrs`, offset `j·(192/d) + i`),
the helper relates `cap ++ [positions, win_ptrs, tabs]` to `sqCaps cap sq`, handing back the
decoders' runs (`lpRuns`: run `j` the windows `qwRunList d cd (sqChal cap j)`), by a tree within
`Bd` when given. `level_positions_completeAt_Spec`: every entry of `lpTable`, for frame runs that
fit their frames with consecutive cells, on memories defined below `2^κ`, `7 ≤ κ`.

**Design note for the proof.** Build on:
* `lp_complete` (`Whir/CLp.lean`): the unplaced relation, from the squeeze run holding `sqCaps`
  and each decoder's relation; `lpTable_ok` (`Whir/HelperAll.lean`) for the bodies.
* `qwDecodeAtD_holds` (`Bits/QueryWindowsAtAll.lean`): each decoder `QwDecodeAtD` at its frame
  pointer, its run `qwRunL`; the entry's `(qwDecName d cd, d, cd) ∈ queryWindowsShapes` by
  `decide`.
* the placement of a straight-line body with one `HeapBuf` (`sqz`, `(sq + 1)·5` words) and a
  loop call, the loop's iterations placing their tail at `fp + fs loop` then the decoder (mumbai's
  `Place/SqAt.lean`, `sqLoop_relAtIn`, `sqDecAt`, `sqTot`, before this design: the old squeeze
  loop was `open_stacked`'s own callee; `dfp` is `sqDecAt` shifted past `level_positions`' frame
  and `sqz`), `relAtIn_of_walk`, `RunsConsec` for the decoders' runs.
* the bound: `TotalLe` at `Bd = some B` gives `n ≤ B` (`completeAtDTB_of_relIn`'s pattern,
  `Budget/LiftB.lean`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir (qwDecName sqCaps sqChal lpTable)
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- The decoders' runs of `level_positions` at `sq` squeezes from `cap`, decoder `j` at the frame
pointer `dfp j`: its windows of the challenge `sqChal cap j`. -/
def lpRuns (cert : String → V → ℕ) (d cd sq : ℕ) (dfp : ℕ → ℕ) (cap : List E) : Layout :=
  (List.range sq).flatMap fun j ↦ qwRunL cert (qwDecName d cd) (dfp j) d cd (sqChal cap j)

/-- The caller's words `level_positions` reads, on a memory: the window table at `tabs`, and at
offset `j·(192/d) + i` of `positions` and `win_ptrs`, challenge `j`'s position `i` and the
pointer to its windows in decoder `j`'s run (frame pointer `dfp j`). -/
def LpMem (cert : String → V → ℕ) (d cd sq : ℕ) (dfp : ℕ → ℕ) (cap : List E) (pos wp tabs : E)
    (rd : Reader) : Prop :=
  WinTabs rd tabs ∧ ∀ j < sq, ∀ i < 192 / d,
    LoadHolds rd pos (j * (192 / d) + i) (eOfNat (qwPosOf d (sqChal cap j) i)) ∧
    LoadHolds rd wp (j * (192 / d) + i) (qwPtrAt cert (qwDecName d cd) (dfp j) d cd i)

/-- **`level_positions` at `(name, sq, d, cd)`, placed**, its decoders at `dfp fp j` when entered
at `fp`: on canonical capacity cells, its loads among the caller's words, on every memory holding
them (`LpMem`), complete by a tree within `Bd` when given, handing back the decoders' runs. -/
def LpAtO (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (name : String) (sq d cd : ℕ)
    (dfp : ℕ → ℕ → ℕ) (Bd : Option ℕ) : Prop :=
  ∀ (cap : List E) (pos wp tabs : E) (Lin : ℕ → Layout), cap.length = 5 → AllCanonical cap →
    (∀ fp, RegPtrs [(5, sq * (192 / d)), (6, sq * (192 / d)), (7, 128)] (cap ++ [pos, wp, tabs])
      (RegionL (Lin fp))) →
    (∀ fp rd, LowDef κ rd → MemL rd (Lin fp) → LpMem cert d cd sq (dfp fp) cap pos wp tabs rd) →
    BoundsAt fs name Bd →
    CompleteAtPO fs cert κ name Lin (cap ++ [pos, wp, tabs]) (sqCaps cap sq)
      (fun fp ↦ lpRuns cert d cd sq (dfp fp) cap) Bd

/-- **`level_positions` is complete placed at every specialization**: for frame runs fitting their
frames, their cells consecutive, on memories defined below `2^κ`, `7 ≤ κ` (the decoders' range
checks), each entry `(name, sq, loop, d, cd)` of `lpTable` has its decoders' frame pointers `dfp`
and is `LpAtO` at every bound. -/
def level_positions_completeAt_Spec : Prop :=
  ∀ (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ), Lift.RunsFit fs cert → RunsConsec cert →
    7 ≤ κ → ∀ e ∈ lpTable, ∃ dfp : ℕ → ℕ → ℕ, ∀ Bd : Option ℕ,
      LpAtO fs cert κ e.1 e.2.1 e.2.2.2.1 e.2.2.2.2 dfp Bd

end
end LeanVM.Guest.B1
