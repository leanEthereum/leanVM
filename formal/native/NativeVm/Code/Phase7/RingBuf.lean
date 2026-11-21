module

public import NativeVm.Code.Phase7.RingWeqE
public import NativeVm.Transcript.Mem

/-!
# A small buffer of words

`weightRing` keeps its state in a buffer of `bufWords` words at a base `b`, word `j` at `ew b j`:
`setMem_ew` reads a word after a store to another (`simp (disch := omega) only [setMem_ew]`),
`eval_w` and `eval_idx` give the addresses `at_ r (wdisp k)` and `r + i·8 + wdisp k`, and
`EArr_congr`/`EW_congr` move a list's facts to a memory agreeing on its words.
-/

@[expose] public section

namespace NativeVm.Code.Ring

open Native NativeVm.Field LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeVm.Transcript (wdisp wdisp_toUInt64)

/-- `weightRing`'s buffer: eight words of state, then up to `36` elements. -/
def bufWords : Nat := 80

theorem setMem_ew (t : QState) (b : UInt64) (j k : Nat) (v : UInt64) (hj : j < 2 ^ 61)
    (hk : k < 2 ^ 61) :
    (t.setMem (ew b j) v).mem (ew b k) = if k = j then some v else t.mem (ew b k) := by
  rw [QState.setMem_mem]
  by_cases h : k = j
  · subst h; simp
  · simp [h, ew_ne b hk hj h]

theorem at_wdisp (s : QState) (r : Reg64) (k : Nat) : (at_ r (wdisp k)).eval s = ew (s.reg r) k := by
  rw [eval_at, wdisp_toUInt64]
  rfl

theorem eval_w {s : QState} {r : Reg64} {b : UInt64} (h : s.reg r = b) (k : Nat) :
    (at_ r (wdisp k)).eval s = ew b k := by
  rw [eval_at, h, wdisp_toUInt64]
  rfl

theorem eval_idx {s : QState} {base ix : Reg64} {b : UInt64} {i k : Nat} (hb : s.reg base = b)
    (hi : s.reg ix = i.toUInt64) :
    ({ base := base, idx := some (ix, .W64), disp := wdisp k } : Addr).eval s = ew b (i + k) := by
  have := NativeVm.Transcript.eval_idx64 (s := s) (b := b) (j := 0) (i := i)
    (by rw [hb, NativeVm.Transcript.wd_zero]) hi k
  rw [this, Nat.zero_add]
  rfl

theorem EArr_congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {L : List E}
    (h : ∀ j < 2 * L.length, mem' (ew p j) = mem (ew p j)) (hL : EArr mem p L) : EArr mem' p L := by
  rw [EArr_iff_EW] at hL ⊢
  intro k hk
  obtain ⟨h0, h1⟩ := hL k hk
  exact ⟨by rw [h _ (by omega)]; exact h0, by rw [h _ (by omega)]; exact h1⟩

theorem EW_congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {k : Nat} {x : E}
    (h0 : mem' (ew p (2 * k)) = mem (ew p (2 * k)))
    (h1 : mem' (ew p (2 * k + 1)) = mem (ew p (2 * k + 1))) (hx : EW mem p k x) : EW mem' p k x :=
  ⟨by rw [h0]; exact hx.1, by rw [h1]; exact hx.2⟩

/-- A list apart from a buffer survives a run that writes only the buffer. -/
theorem EArr_apart {mem mem' : UInt64 → Option UInt64} {b p : UInt64} {n : Nat} {L : List E}
    (hF : ∀ a, (∀ k < n, a ≠ ew b k) → mem' a = mem a)
    (hs : ∀ k < n, ∀ j < 2 * L.length, ew b k ≠ ew p j) (hL : EArr mem p L) : EArr mem' p L :=
  EArr_congr (fun j hj ↦ hF _ fun k hk e ↦ hs k hk j hj e.symm) hL

theorem shl4 (w : Nat) : w.toUInt64 <<< (4 : UInt64) = (16 * w).toUInt64 := by
  have := NativeVm.Transcript.toUInt64_shl w 4 (by omega)
  rw [show (4 : Nat).toUInt64 = 4 from rfl] at this
  rw [this]
  rfl

theorem shl1 (w : Nat) : w.toUInt64 <<< (1 : UInt64) = (2 * w).toUInt64 := by
  have := NativeVm.Transcript.toUInt64_shl w 1 (by omega)
  rw [show (1 : Nat).toUInt64 = 1 from rfl] at this
  rw [this]
  rfl

end NativeVm.Code.Ring
