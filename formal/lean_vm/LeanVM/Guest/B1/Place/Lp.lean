/-
  LeanVM.Guest.B1.Place.Lp

  `level_positions` complete placed, at every specialization of `lpTable`.
-/

module

public import LeanVM.Guest.B1.Place.HelperAt
public import LeanVM.Guest.B1.Place.OsSqGroup
public import LeanVM.Guest.B1.Whir.CSqLoop
public import LeanVM.Guest.B1.Whir.HelperAll
public import LeanVM.Guest.B1.Whir.Squeezes

/-!
# `level_positions`, placed

`level_positions__L{S}_L{d}_L{cd}(w0, fs0 .. fs4, positions, win_ptrs, tabs)`
(`lpBody S d cd loop`) allocates its squeeze run `sqz` (`(S + 1)·5` words), stores the capacity
`cap` in its row `1`, decodes the first word `w0` (`decode_query_windows__L{d}_L{cd}`), runs its
loop (`lpLoopBody d cd loop`, the squeeze loop's template at offset `0`) over the squeezes
`1 .. S - 1`, each decoding the next squeeze's word and storing the next capacity, and returns
the last row's capacity, the capacity after `S - 1` squeezes. The decoders are a group of callees
placed after its frame and its run (`os_sq_group`): decoder `j`'s frame at `lpDecPos … fp j`,
its windows a run of that frame, which the caller's window pointers name.

**The statement** (`LpAtD`): with the helper at `fp`, on every memory holding the caller's words
`Lin fp` (the window table at `tabs`, squeeze `j`'s positions `qwPosOf d (sqSample w0 cap j) i`
at `positions` and the pointers into decoder `j`'s run at `win_ptrs`, offset `j·(128/d) + i`),
the helper relates `w0 :: cap ++ [positions, win_ptrs, tabs]` to the last capacity, handing back
the decoders' runs. `level_positions_completeAt`: every entry of `lpTable`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-! ## The statement -/

/-- The squeeze loop's row of a level of depth `d` and cap depth `cd` (`lpLoopBody`). -/
abbrev lpLvP (d cd : ℕ) : OsLv := lpLv d cd

/-- The decoders' group's base, `level_positions` entered at `fp`: past its frame and its squeeze
run. -/
def lpKidsAt (fs : String → ℕ) (name : String) (S fp : ℕ) : ℕ := fp + fs name + (S + 1) * 5

/-- Decoder `j`'s frame, `level_positions` entered at `fp`. -/
def lpDecPos (fs : String → ℕ) (name loop : String) (S d cd fp j : ℕ) : ℕ :=
  sqDecPos fs (lpLvP d cd) loop S (lpKidsAt fs name S fp) j

/-- The decoders' runs: decoder `j`'s windows of squeeze `j`'s word. -/
def lpRuns (fs : String → ℕ) (cert : String → V → ℕ) (name loop : String) (S d cd : ℕ) (w0 : E)
    (cap : List E) (fp : ℕ) : Layout :=
  sqGroupRuns fs cert (lpLvP d cd) loop S (lpKidsAt fs name S fp) (sqSample w0 cap)

/-- The words of `level_positions`: its frame, its squeeze run and its decoders' group. -/
def lpN (fs : String → ℕ) (name loop : String) (S d cd : ℕ) : ℕ :=
  fs name + (S + 1) * 5 + (fs (dqwName d cd) + sqTot fs (lpLvP d cd) loop (S - 1) 0)

/-- The caller's words `level_positions` reads, on a memory: the window table at `tabs`, and at
offset `j·(128/d) + i` of `positions` and `win_ptrs`, squeeze `j`'s position `i` and the
pointer into decoder `j`'s run (its frame at `dfp j`). -/
def LpMem (cert : String → V → ℕ) (S d cd : ℕ) (dfp : ℕ → ℕ) (w0 : E) (cap : List E)
    (pos wp tabs : E) (rd : Reader) : Prop :=
  WinTabs rd tabs ∧ ∀ j < S, ∀ i < 128 / d,
    LoadHolds rd pos (j * (128 / d) + i) (eOfNat (qwPosOf d (sqSample w0 cap j) i)) ∧
    LoadHolds rd wp (j * (128 / d) + i) (qwPtrAt cert (dqwName d cd) (dfp j) d cd i)

/-- **`level_positions` at `(name, S, loop, d, cd)`, placed**: its loads among the caller's
words (`positions` and `win_ptrs` from `g^ep` and `g^ew`, `S·128/d` each, and the window table),
on every memory holding them (`LpMem`), complete, handing back the decoders' runs. -/
def LpAtD (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (name loop : String) (S d cd : ℕ) :
    Prop :=
  ∀ (w0 : E) (cap : List E) (ep ew : ℕ) (tabs : E) (Lin : ℕ → Layout), cap.length = 5 →
    (∀ fp, ∀ k < S * (128 / d), RegionL (Lin fp) (ep + k) ∧ RegionL (Lin fp) (ew + k)) →
    (∀ fp, ∀ t < 128, ∃ i, tabs.limb 0 * addressOfIndex t = addressOfIndex i ∧
      RegionL (Lin fp) i) →
    (∀ fp rd, LowDef κ rd → MemL rd (Lin fp) →
      LpMem cert S d cd (lpDecPos fs name loop S d cd fp) w0 cap (ofK (addressOfIndex ep))
        (ofK (addressOfIndex ew)) tabs rd) →
    CompleteAtPO fs cert κ name Lin
      (w0 :: cap ++ [ofK (addressOfIndex ep), ofK (addressOfIndex ew), tabs])
      ((⟨cap, []⟩ : Fs).squeezeN (S - 1)).2.cap (lpRuns fs cert name loop S d cd w0 cap) none

/-- **`level_positions` is complete placed at every specialization**: for frame runs fitting their
frames, their cells consecutive, on memories defined below `2^κ`, `7 ≤ κ` (the decoders' range
checks), each entry `(name, S, loop, d, cd)` of `lpTable` is `LpAtD`. -/
def level_positions_completeAt_Spec : Prop :=
  ∀ (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ), Lift.RunsFit fs cert → RunsConsec cert →
    7 ≤ κ → ∀ e ∈ lpTable, LpAtD fs cert κ e.1 e.2.2.1 e.2.1 e.2.2.2.1 e.2.2.2.2

end
end LeanVM.Guest.B1
