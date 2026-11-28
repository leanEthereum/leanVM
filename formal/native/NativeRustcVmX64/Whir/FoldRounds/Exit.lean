module

public import NativeRustcVmX64.Whir.FoldRounds.Parts

/-!
# `fold_rounds` on x86-64: the exits

`exit21`: from the frame with RSP at its offset `8`, BL the verdict, `b21` returns it in AL;
`fail20`: a rejected round (`b20` clears EBX, `b21`); `done`: all `n` rounds done (BL `1`);
`ret0`: `n = 0`, `b21` right after the prologue.
-/

namespace NativeRustcVmX64.Whir.FoldRounds

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.FoldRounds
open NativeRustcVmX64.Transcript (Frame frameEnv MidOk)
open NativeRustcVmX64.Whir.SampleQueries (al_one)
open NativeRustcVm (WordAt EWAt EWsAt)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {w : WhirStateW} {m0 : MachineData}

/-- **`b21`**: BL the verdict, returned in AL; the outputs as `foldRounds` leaves them. -/
theorem exit21 (hp : Placed code k) (h : FoldRoundsPre a s w m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRounds.b21Offset)) (hf : Frame m0 160 slots 8 st.data) (hs : Sm m0 st.data)
    (hbx : (reg st.data .rbx).toNat % 256 =
      (okWord ((foldRounds (reg m0 .rsi).toNat w).run s).isSome).toNat)
    (hout : ∀ w' rs s', (foldRounds (reg m0 .rsi).toNat w).run s = some ((w', rs), s') →
      WhirStateAt st.data.dmem (pA m0) w' ∧ BufRoundsAt st.data.dmem (rA m0) rs.toList ∧
        TStateAt st.data.dmem (tA m0) a s') :
    Eventually (step1 Host.exe) (Goal a s w m0) st := by
  have c := ctx h
  have hwf := c.wf0 (d := st.data) (vars := fun _ ↦ 0) (ret := 0) hf.kept
  refine exec_at (inf hp b21_in_code (by simp [b21])) run_b21 hwf (by intro l h; cases h) hpc
    (mid hf) fun st1 hm1 hpc1 ↦ .done _ ?_
  obtain ⟨he, hmem, hax⟩ := after_eq run_b21 ▸ ok_b21
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf hwf hm1 he
  have hd : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf hmem
  refine ⟨?_, hrsp, ?_, fun w' rs s' hr ↦ by rw [hd]; exact hout w' rs s' hr,
    fun q hq ↦ by rw [hd]; exact changes hs q hq, hsv⟩
  · simp only [PcOk] at hpc1
    rw [hpc1]
    exact hf.load_ret c.stack F_le
  · show (reg st1.data .rax).toNat % 256 = _
    rw [show reg st1.data .rax = _ from hm1.regs .rax _ hax]
    exact (trunc32_low8 _).trans hbx

/-- **A rejected round**: `b20` clears EBX, `b21` returns `0`. -/
theorem fail20 (hp : Placed code k) (h : FoldRoundsPre a s w m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRounds.b20Offset)) (hf : Frame m0 160 slots 8 st.data) (hs : Sm m0 st.data)
    (hnone : (foldRounds (reg m0 .rsi).toNat w).run s = none) :
    Eventually (step1 Host.exe) (Goal a s w m0) st := by
  have c := ctx h
  have hwf := c.wf0 (d := st.data) (vars := fun _ ↦ 0) (ret := 0) hf.kept
  refine exec_at (inf hp b20_in_code (by simp [b20])) run_b20 hwf (by intro l h; cases h) hpc
    (mid hf) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hmem, hbx⟩ := after_eq run_b20 ▸ ok_b20
  have hd : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf hmem
  simp only [PcOk] at hpc1
  refine exit21 hp h (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.FoldRounds.b20_next))
    (Frame.of_block hf hwf hm1 hmid slots_le) (fun q hq ↦ by rw [hd]; exact hs q hq) ?_ ?_
  · rw [show reg st1.data .rbx = _ from hm1.regs .rbx _ hbx, hnone]
    rfl
  · intro _ _ _ hr
    rw [hnone] at hr
    cases hr

/-- **All rounds done**: `b21` returns `1`. -/
theorem done (hp : Placed code k) (h : FoldRoundsPre a s w m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRounds.b21Offset))
    (hI : Inv a s w m0 (reg m0 .rsi).toNat 8 st.data) :
    Eventually (step1 Host.exe) (Goal a s w m0) st := by
  obtain ⟨w', rs, s', hrun, -, -, hws, hbr, hts⟩ := hI.run
  refine exit21 hp h hpc hI.fr hI.same (by rw [hI.rbx, hrun]; rfl) fun w'' rs' s'' hr ↦ ?_
  rw [hrun] at hr
  cases hr
  exact ⟨hws, hbr, hts⟩

/-- **`n = 0`**: `b21` right after the prologue returns `1`, the buffer empty. -/
theorem ret0 (h : FoldRoundsPre a s w m0) (h0 : (reg m0 .rsi).toNat = 0) {st : MachineState}
    {r : BitVec 64} {nx : Int64} (hm : Match (entryEnv m0 r) (after b21 S0) st.data)
    (hpc : PcOk (entryEnv m0 r) (.ret (.load 0 160 8)) nx st) : Goal a s w m0 st := by
  obtain ⟨he, hw, hw0, hax⟩ := ok_b21z
  have hwf := entry_wf h (r := r)
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue Frame.entry hwf hm he
  have hs := entry_same h hm hw
  have hrun : (foldRounds (reg m0 .rsi).toNat w).run s = some ((w, #[]), s) := by rw [h0]; rfl
  refine ⟨?_, hrsp, ?_, fun w' rs s' hr ↦ ?_, changes (entry_sm h hs), hsv⟩
  · simp only [PcOk] at hpc
    rw [hpc]
    exact Frame.entry.load_ret (pre_S h) F_le
  · show (reg st.data .rax).toNat % 256 = _
    rw [show reg st.data .rax = _ from hm.regs .rax _ hax, hrun]
    exact (trunc32_low8 _).trans (al_one _)
  · rw [hrun] at hr
    cases hr
    exact ⟨entry_ws h hs, ⟨by simp [roundCap], count0 hm hw0, ewsAt_nil _ _⟩,
      entry_ts h hsv.2 hs⟩

end

end NativeRustcVmX64.Whir.FoldRounds
