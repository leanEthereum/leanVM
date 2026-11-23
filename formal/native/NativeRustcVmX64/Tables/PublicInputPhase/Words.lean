module

public import NativeRustcVmX64.Tables.PublicInputPhase.Steps

/-!
# `public_input_phase`: the frame's words (x86-64)

The claims' point at the frame's offset `64` (`PtW`: the challenge, then zeros; `slice_pt`), the
two values at `32` and the challenge at `16` the `multilinear_eval_by` calls read
(`ewsAt_two`, `ewsAt_one`); bytes of the frame a block or a call does not write (`keepHi`,
`PtW.keep`).
-/

namespace NativeRustcVmX64.Tables.PublicInputPhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Tables
open NativeRustcVm (wordOf ewsOf)

@[expose] public section

/-- Word `i` of the point. -/
def ptw (ch : EW) : Nat → UInt64
  | 0 => ch.c0
  | 1 => ch.c1
  | _ => 0

/-- The point's `62` words at the frame's offset `64`, from word `lo` on. -/
def PtW (m0 : MachineData) (d : DataMem) (ch : EW) (lo : Nat) : Prop :=
  ∀ i, lo ≤ i → i < 62 → NativeRustcVm.WordAt d (off (fb m0) (64 + 8 * i)) (ptw ch i)

end

public section

variable {m0 : MachineData}

theorem size_pt (ch : EW) (n : Nat) : (pt ch n).size = 1 + (n - 1) := by simp [pt]

/-- **The point's words** are its elements. -/
theorem ewsAt_pt {d : DataMem} {ch : EW} (h : PtW m0 d ch 0) {n : Nat} (hn : n ≤ 31) :
    NativeRustcVm.EWsAt d (off (fb m0) 64) (pt ch n).toList := by
  rw [NativeRustcVm.Transcript.ewsAt_iff]
  intro i hi
  have hl : (pt ch n).toList.length = 1 + (n - 1) := by simp [pt]; omega
  rw [hl] at hi
  rw [NativeRustcVm.Transcript.ewAt_iff, off_off, off_off]
  rcases i with _ | i
  · have hx : (pt ch n).toList[0] = ch := by simp [pt]
    rw [hx]
    exact ⟨h 0 (by omega) (by omega), h 1 (by omega) (by omega)⟩
  · have hx : (pt ch n).toList[i + 1] = 0 := by simp [pt]
    rw [hx]
    refine ⟨?_, ?_⟩
    · have := h (2 * i + 2) (by omega) (by omega)
      rwa [show 64 + 8 * (2 * i + 2) = 64 + 16 * (i + 1) by omega] at this
    · have := h (2 * i + 3) (by omega) (by omega)
      rwa [show 64 + 8 * (2 * i + 3) = 64 + 16 * (i + 1) + 8 by omega] at this

/-- **The point** `push_claim` reads. -/
theorem slice_pt {m : MachineData} {ch : EW} (h : PtW m0 m.dmem ch 0) {n : Nat} (h1 : 1 ≤ n)
    (hn : n ≤ 31) : slice m (off (fb m0) 64) (BitVec.ofNat 64 n) = pt ch n := by
  unfold slice
  have e := NativeRustcVm.ewsOf_of_ewsAt (ewsAt_pt h hn)
  have hl : (pt ch n).toList.length = n := by simp [pt]; omega
  rw [hl] at e
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), e]

/-- Two elements from their four words. -/
theorem ewsAt_two {d : DataMem} {b : BitVec 64} {x0 x1 y0 y1 : UInt64}
    (h0 : NativeRustcVm.WordAt d b x0) (h1 : NativeRustcVm.WordAt d (off b 8) x1)
    (h2 : NativeRustcVm.WordAt d (off b 16) y0) (h3 : NativeRustcVm.WordAt d (off b 24) y1) :
    NativeRustcVm.EWsAt d b [⟨x0, x1⟩, ⟨y0, y1⟩] := by
  rw [NativeRustcVm.Transcript.ewsAt_iff]
  intro i hi
  rw [NativeRustcVm.Transcript.ewAt_iff, off_off]
  match i, hi with
  | 0, _ => exact ⟨by rwa [off_zero], h1⟩
  | 1, _ => exact ⟨h2, h3⟩

/-- One element from its two words. -/
theorem ewsAt_one {d : DataMem} {b : BitVec 64} {x0 x1 : UInt64}
    (h0 : NativeRustcVm.WordAt d b x0) (h1 : NativeRustcVm.WordAt d (off b 8) x1) :
    NativeRustcVm.EWsAt d b [⟨x0, x1⟩] := by
  rw [NativeRustcVm.Transcript.ewsAt_iff]
  intro i hi
  rw [NativeRustcVm.Transcript.ewAt_iff, off_off]
  match i, hi with
  | 0, _ => exact ⟨by rwa [off_zero], h1⟩

section
variable [Labels]

/-- A frame byte at offset `j ≥ L` a block writing below `L` did not write. -/
theorem keepHi {rest : List (BitVec 64 × Nat)} {d d' : MachineData} {S : SState} {ret : BitVec 64}
    (hwf : (frameEnv m0 d 608 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 608 rest (fun _ ↦ 0) ret) S d') (hin : writesIn S = true) {L : Nat}
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ L) {j : Nat} (hLj : L ≤ j) (hj : j < 616) :
    d'.dmem.get? (off (fb m0) j) = d.dmem.get? (off (fb m0) j) :=
  hm.get?_mem0 hwf (not_written0 hwf hm hin hj fun w hw' _ ↦ .inl (by have := (hw w hw').2; omega))

/-- A word of the frame at offset `o ≥ L` a block writing below `L` did not write. -/
theorem wordHi {rest : List (BitVec 64 × Nat)} {d d' : MachineData} {S : SState} {ret : BitVec 64}
    (hwf : (frameEnv m0 d 608 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 608 rest (fun _ ↦ 0) ret) S d') (hin : writesIn S = true) {L : Nat}
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ L) {o : Nat} (hLo : L ≤ o) (ho : o + 8 ≤ 616)
    {v : UInt64} (h : NativeRustcVm.WordAt d.dmem (off (fb m0) o) v) :
    NativeRustcVm.WordAt d'.dmem (off (fb m0) o) v := fun i hi ↦ by
  have hi' : i < 8 := by simpa [NativeRustcVm.length_wordBytes] using hi
  rw [off_add, keepHi hwf hm hin hw (by omega) (by omega), ← off_add]
  exact h i hi

/-- The point's words kept by a block writing below offset `64`. -/
theorem PtW.block {rest : List (BitVec 64 × Nat)} {d d' : MachineData} {S : SState}
    {ret : BitVec 64} {ch : EW} {lo : Nat} (h : PtW m0 d.dmem ch lo)
    (hwf : (frameEnv m0 d 608 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 608 rest (fun _ ↦ 0) ret) S d') (hin : writesIn S = true)
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 64 + 8 * lo) : PtW m0 d'.dmem ch lo :=
  fun i h1 h2 ↦ wordHi hwf hm hin hw (by omega) (by omega) (h i h1 h2)

/-- A word written by a block. -/
theorem wordW {rest : List (BitVec 64 × Nat)} {d d' : MachineData} {S : SState} {ret : BitVec 64}
    (hm : Match (frameEnv m0 d 608 rest (fun _ ↦ 0) ret) S d') {o : Nat} (ho : o + 8 ≤ 616)
    {v : Sym} (hw : ∀ t < 8, findWrite 0 (o + t) S.mem = some (v, t)) :
    NativeRustcVm.WordAt d'.dmem (off (fb m0) o)
      (UInt64.ofBitVec (v.eval (frameEnv m0 d 608 rest (fun _ ↦ 0) ret))) :=
  wordAt_write hm (r := 0) rfl ho hw

end

end

end NativeRustcVmX64.Tables.PublicInputPhase
