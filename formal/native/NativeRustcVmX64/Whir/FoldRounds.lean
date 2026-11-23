module

public import NativeRustcVmX64.Whir.FoldRounds.Round
public import NativeRustcVmX64.Code.Vm.FoldRound.Names
public import NativeRustcVmX64.Code.Vm.FoldRounds.Names

/-!
# `fold_rounds` on x86-64

**`foldRounds_spec`**: rustc's `fold_rounds`, placed anywhere in the program, meets
`FoldRoundsPre`/`FoldRoundsPost` given `fold_round`'s contract. `b0` pushes the registers, clears
the buffer's count and sets BL to `1`; `n = 0` returns at once (`ret0`). Otherwise `b1` calls
`fold_round`; rustc unrolled the (at most `6`) rounds, each a call, its tag tested (a rejection
returns `0`, `fail20`), its `α`, `β` pushed on the buffer, then compared with `n` (equal: the
return with `1`, `done`): `round`, `step`. The state, the rounds and the transcript's state are
`foldRounds`' (`Inv`).
-/

namespace NativeRustcVmX64.Whir.FoldRounds

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.FoldRounds
open NativeRustcVmX64.Transcript (Frame frameEnv)
open NativeRustcVmX64.Whir.SampleQueries (al_one)
open NativeRustcVmX64.Arrays (pc_cond)

public section

variable [Host] {k : Nat}

/-- **`fold_rounds` meets its contract.** -/
theorem foldRounds_spec (hp : Placed code k)
    (hfr : ∀ a s w, Spec (Labels.label NativeRustcVmX64.Vm.FoldRound.entryLabel) (FoldRoundPre a s w) (FoldRoundPost a s w))
    (a : DecArea) (s : TState) (w : WhirStateW) :
    Spec (Labels.label NativeRustcVmX64.Vm.FoldRounds.entryLabel) (FoldRoundsPre a s w) (FoldRoundsPost a s w) := by
  intro m0 h
  rw [show Labels.label NativeRustcVmX64.Vm.FoldRounds.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRounds.b0Offset) from hp.label NativeRustcVmX64.Vm.FoldRounds.entry_at]
  have hn6 := pre_n6 h
  have hwf := entry_wf h (r := (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRounds.b1Offset + b1.length)).toBitVec)
  refine exec_then (inf hp b0_in_code (by simp [b0])) run_b0 hwf (by intro l h; cases h)
    entry_match fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  rw [test0] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases h0 : (reg m0 .rsi).toNat = 0
  · -- `n = 0`: `b21`.
    have hpc := (hT (decide_eq_true h0)).trans (hp.label NativeRustcVmX64.Vm.FoldRounds.label_3_at)
    refine exec_at (inf hp b21_in_code (by simp [b21])) (exec_after run_b0 run_b21z) hwf
      (by intro l h; cases h) hpc hm1 fun st2 hm2 hpc2 ↦ .done _ ?_
    rw [← after_eq run_b21z] at hm2
    exact ret0 h h0 hm2 hpc2
  -- `b1`: the first call.
  have hpc := hF fun h' ↦ h0 (of_decide_eq_true h')
  refine exec_at (inf hp b1_in_code (by simp [b1])) (exec_after run_b0 run_b1) hwf
    (fun _ _ ↦ rfl) (hpc.trans rfl) hm1 fun st2 hm2 hpc2 ↦ ?_
  rw [← after_eq run_b1] at hm2
  obtain ⟨hpro, hw, hw0, hdi, hsi, hdx, h12, h13, h14, h15, hbx⟩ := ok_b1
  have hfr2 := Frame.of_prologue Frame.entry hwf hm2 hpro slots_le slots_cs
  have hs2 := entry_same h hm2 hw
  have hI : Inv a s w m0 0 0 st2.data :=
    ⟨hfr2, entry_sm h hs2, (hm2.regs .r12 _ h12).trans (Transcript.eval_ptr rfl),
      hm2.regs .r13 _ h13, hm2.regs .r14 _ h14, hm2.regs .r15 _ h15,
      by rw [show reg st2.data .rbx = _ from hm2.regs .rbx _ hbx]; exact al_one _,
      fun h' ↦ absurd h' (by omega),
      ⟨w, #[], s, rfl, rfl, rfl, entry_ws h hs2,
        ⟨by simp [roundCap], count0 hm2 hw0, ewsAt_nil _ _⟩, entry_ts h (hm2.kept hwf) hs2⟩⟩
  simp only [PcOk] at hpc2
  -- Round 1.
  refine round hp hfr h 0 b2_in_code (by simp [b2]) run_b2 ok_b2 (fun _ hd ↦ tag8_0 hd)
    (fun _ hd ↦ tag8_1 hd) (by rw [NativeRustcVmX64.Vm.FoldRounds.b2_length]; exact b3_in_code) (by simp [b3])
    (.inl rfl) run_b3 ok_b3 (by omega)
    ⟨hpc2.1, hpc2.2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.FoldRounds.b1_next)⟩ hI
    ((hm2.regs .rdi _ hdi).trans (Transcript.eval_ptr0 40)) (hm2.regs .rsi _ hsi)
    (hm2.regs .rdx _ hdx) fun st3 hpc3 hne1 hI1 ↦ ?_
  -- Round 2.
  refine step hp hfr h 1 b4_in_code (by simp [b4]) run_b4 ok_b4
    (by rw [NativeRustcVmX64.Vm.FoldRounds.b4_length]; exact b5_in_code) (by simp [b5]) run_b5 ok_b5
    (fun _ hd ↦ tag32_0 hd) (fun _ hd ↦ tag32_1 hd)
    (by rw [NativeRustcVmX64.Vm.FoldRounds.b4_length, NativeRustcVmX64.Vm.FoldRounds.b5_length]; exact b6_in_code)
    (by simp [b6]) (.inr ⟨rfl, by omega⟩) run_b6 ok_b6 (by omega)
    (hpc3.trans (by rw [NativeRustcVmX64.Vm.FoldRounds.b2_next, Nat.add_assoc, NativeRustcVmX64.Vm.FoldRounds.b3_next])) hI1
    fun st4 hpc4 hne2 hI2 ↦ ?_
  -- Round 3.
  refine step hp hfr h 2 b7_in_code (by simp [b7]) run_b7 ok_b7
    (by rw [NativeRustcVmX64.Vm.FoldRounds.b7_length]; exact b8_in_code) (by simp [b8]) run_b8 ok_b8
    (fun _ hd ↦ tag32_0 hd) (fun _ hd ↦ tag32_1 hd)
    (by rw [NativeRustcVmX64.Vm.FoldRounds.b7_length, NativeRustcVmX64.Vm.FoldRounds.b8_length]; exact b9_in_code)
    (by simp [b9]) (.inr ⟨rfl, by omega⟩) run_b9 ok_b9 (by omega)
    (hpc4.trans (by rw [NativeRustcVmX64.Vm.FoldRounds.b4_next, NativeRustcVmX64.Vm.FoldRounds.b5_next, Nat.add_assoc, NativeRustcVmX64.Vm.FoldRounds.b6_next])) hI2
    fun st5 hpc5 hne3 hI3 ↦ ?_
  -- Round 4.
  refine step hp hfr h 3 b10_in_code (by simp [b10]) run_b10 ok_b10
    (by rw [NativeRustcVmX64.Vm.FoldRounds.b10_length]; exact b11_in_code) (by simp [b11]) run_b11 ok_b11
    (fun _ hd ↦ tag32_0 hd) (fun _ hd ↦ tag32_1 hd)
    (by rw [NativeRustcVmX64.Vm.FoldRounds.b10_length, NativeRustcVmX64.Vm.FoldRounds.b11_length]; exact b12_in_code)
    (by simp [b12]) (.inr ⟨rfl, by omega⟩) run_b12 ok_b12 (by omega)
    (hpc5.trans (by rw [NativeRustcVmX64.Vm.FoldRounds.b7_next, NativeRustcVmX64.Vm.FoldRounds.b8_next, Nat.add_assoc, NativeRustcVmX64.Vm.FoldRounds.b9_next])) hI3
    fun st6 hpc6 hne4 hI4 ↦ ?_
  -- Round 5.
  refine step hp hfr h 4 b13_in_code (by simp [b13]) run_b13 ok_b13
    (by rw [NativeRustcVmX64.Vm.FoldRounds.b13_length]; exact b14_in_code) (by simp [b14]) run_b14 ok_b14
    (fun _ hd ↦ tag32_0 hd) (fun _ hd ↦ tag32_1 hd)
    (by rw [NativeRustcVmX64.Vm.FoldRounds.b13_length, NativeRustcVmX64.Vm.FoldRounds.b14_length]; exact b15_in_code)
    (by simp [b15]) (.inr ⟨rfl, by omega⟩) run_b15 ok_b15 (by omega)
    (hpc6.trans (by rw [NativeRustcVmX64.Vm.FoldRounds.b10_next, NativeRustcVmX64.Vm.FoldRounds.b11_next, Nat.add_assoc, NativeRustcVmX64.Vm.FoldRounds.b12_next])) hI4
    fun st7 hpc7 hne5 hI5 ↦ ?_
  -- Round 6: `n = 6`, the seventh call (`b19`) unreached.
  exact step hp hfr h 5 b16_in_code (by simp [b16]) run_b16 ok_b16
    (by rw [NativeRustcVmX64.Vm.FoldRounds.b16_length]; exact b17_in_code) (by simp [b17]) run_b17 ok_b17
    (fun _ hd ↦ tag32_0 hd) (fun _ hd ↦ tag32_1 hd)
    (by rw [NativeRustcVmX64.Vm.FoldRounds.b16_length, NativeRustcVmX64.Vm.FoldRounds.b17_length]; exact b18_in_code)
    (by simp [b18]) (.inr ⟨rfl, by omega⟩) run_b18 ok_b18 (by omega)
    (hpc7.trans (by rw [NativeRustcVmX64.Vm.FoldRounds.b13_next, NativeRustcVmX64.Vm.FoldRounds.b14_next, Nat.add_assoc, NativeRustcVmX64.Vm.FoldRounds.b15_next])) hI5
    fun _ _ hne6 _ ↦ absurd hn6 (by omega)

end

end NativeRustcVmX64.Whir.FoldRounds
