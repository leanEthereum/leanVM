module

public import NativeRustcVmX64.Tables.ColumnClaims.Defs
public import NativeRustcVmX64.Transcript.Arith
public import NativeRustcVmX64.Code.Vm.TableColumnClaims.Names

/-!
# `table_column_claims`: the exits (x86-64)

The epilogue `b25` (`NativeRustcVmX64.Vm.TableColumnClaims.label_20`) returns AL (`exit_step`); before it, the failure
`b24` (`NativeRustcVmX64.Vm.TableColumnClaims.label_19`: AL zero, `fail_step`), reached from the tables' failure jumps
(`jump19`), or `b30` (table `5`'s failure, AL already zero, `fail30`), and the success `b31`
(`NativeRustcVmX64.Vm.TableColumnClaims.label_16`: AL one, `done_step`).
-/

namespace NativeRustcVmX64.Tables.ColumnClaims

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Tables NativeRustcVmX64.Arrays
open NativeRustcVmX64.Vm.TableColumnClaims NativeRustcVmX64.Field
open NativeRustcVm.Layout (claimsBytes ClaimsWAt claimCap pointCap Same)

public section

variable [Host] {k : Nat} {ev : Array (Array EW × Array EW)} {cs : Array ColumnClaimW}
  {m0 : MachineData}

theorem hb24 (hp : Placed code k) : b24.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableColumnClaims.b24Offset) :=
  b24_in_code.trans hp.1 (by simp [b24])
theorem hb25 (hp : Placed code k) : b25.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableColumnClaims.b25Offset) :=
  b25_in_code.trans hp.1 (by simp [b25])
theorem hb30 (hp : Placed code k) : b30.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableColumnClaims.b30Offset) :=
  b30_in_code.trans hp.1 (by simp [b30])
theorem hb31 (hp : Placed code k) : b31.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableColumnClaims.b31Offset) :=
  b31_in_code.trans hp.1 (by simp [b31])

theorem lbl_19 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.TableColumnClaims.label_19 = Host.addrOf (k + NativeRustcVmX64.Vm.TableColumnClaims.b24Offset) :=
  hp.label NativeRustcVmX64.Vm.TableColumnClaims.label_19_at
theorem lbl_20 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.TableColumnClaims.label_20 = Host.addrOf (k + NativeRustcVmX64.Vm.TableColumnClaims.b25Offset) :=
  hp.label NativeRustcVmX64.Vm.TableColumnClaims.label_20_at

omit [Host] in
theorem h64 : 64 ≤ N := by decide

/-- **The epilogue**: AL returned. -/
theorem exit_step (hp : Placed code k) (hpre : TableColumnClaimsPre ev cs m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableColumnClaims.b25Offset)) (hb : Bd m0 st.data)
    (hal : (reg st.data .rax).toNat % 256 = (okWord (decide (Fits ev cs))).toNat)
    (hc : Fits ev cs → ClaimsWAt st.data.dmem (reg m0 .rsi) (cs ++ tableColumnClaims ev)) :
    Eventually (step1 Host.exe) (Goal ev cs m0) st := by
  obtain ⟨hS, -, -, hCR, hCO, -⟩ := pre_parts hpre
  have hwf := hb.wf (vars := fun _ ↦ 0) (ret := 0) hS h64
  refine exec_at (hb25 hp) run_b25 hwf (fun _ h ↦ by cases h) hpc hb.mid_match
    fun st' hm hpc' ↦ .done _ ?_
  obtain ⟨hr, hmem, hax⟩ := after_eq run_b25 ▸ ok_b25
  obtain ⟨hpc'', hrsp, hdm, hsaved⟩ := hb.done hS h64 hm hpc' hr hmem (ret_not_in hS hCR.2 hCO)
  refine ⟨hpc'', hrsp, ?_, fun h ↦ by rw [hdm]; exact hc h, fun p hp' ↦ by
    rw [hdm]; exact hb.same p hp', hsaved⟩
  show (st'.data.regs.get64 .rax).toNat % 256 = _
  rw [hm.regs _ _ (hax (.rax, .reg .rax) (by simp))]
  exact hal

/-- **The failure** `b24`: AL zero. -/
theorem fail_step (hp : Placed code k) (hpre : TableColumnClaimsPre ev cs m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableColumnClaims.b24Offset)) (hb : Bd m0 st.data) (hn : ¬Fits ev cs) :
    Eventually (step1 Host.exe) (Goal ev cs m0) st := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hk24, -, h24, -⟩ := after_eq run_b24 ▸ ok_exit
  refine exec_at (hb24 hp) run_b24 (Env.wf_nil _) (fun _ h ↦ by cases h) hpc (match_nil _)
    fun st' hm hpc' ↦ ?_
  have hd : st'.data.dmem = st.data.dmem := hm.dmem_eq (Env.wf_nil _)
    (after_eq run_b24 ▸ ok_exit).2.2.2.2.2.1
  refine exit_step hp hpre hpc' (Body.congr hb (fun r hc ↦ keptBut_reg hm hk24 (by
      intro h; simp at h; subst h; simp [calleeSaved] at hc)) (keptBut_reg hm hk24 (by simp)) hd)
    ?_ fun h ↦ absurd h hn
  show (st'.data.regs.get64 .rax).toNat % 256 = _
  rw [hm.regs _ _ (h24 (.rax, .lit 0) (by simp)), decide_eq_false hn]
  rfl

/-- **A failure jump** to `b24`. -/
theorem jump19 (hp : Placed code k) (hpre : TableColumnClaimsPre ev cs m0) {D : List Directive}
    {kk : Nat} (hD : D.IsInfixAt Host.prog kk)
    (hx : exec D regsS = some (after D regsS, .jump NativeRustcVmX64.Vm.TableColumnClaims.label_19))
    (hmem : (after D regsS).mem = []) (hk : KeptBut (after D regsS) [])
    {st : MachineState} (hpc : st.pc = Host.addrOf kk) (hb : Bd m0 st.data) (hn : ¬Fits ev cs) :
    Eventually (step1 Host.exe) (Goal ev cs m0) st := by
  refine exec_at hD hx (Env.wf_nil _) (fun _ h ↦ by cases h) hpc (match_nil _) fun st' hm hpc' ↦ ?_
  simp only [PcOk] at hpc'
  have hd : st'.data.dmem = st.data.dmem := hm.dmem_eq (Env.wf_nil _) hmem
  exact fail_step hp hpre (hpc'.trans (lbl_19 hp))
    (Body.congr hb (fun r _ ↦ keptBut_reg hm hk (by simp)) (keptBut_reg hm hk (by simp)) hd) hn

/-- **Table `5`'s failure** `b30`: AL already zero. -/
theorem fail30 (hp : Placed code k) (hpre : TableColumnClaimsPre ev cs m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableColumnClaims.b30Offset)) (hb : Bd m0 st.data)
    (hal : (reg st.data .rax).toNat % 256 = 0) (hn : ¬Fits ev cs) :
    Eventually (step1 Host.exe) (Goal ev cs m0) st := by
  obtain ⟨-, -, -, -, h30, -, -, -, -, -, -, hk30, -⟩ := after_eq run_b30 ▸ ok_exit
  refine exec_at (hb30 hp) run_b30 (Env.wf_nil _) (fun _ h ↦ by cases h) hpc (match_nil _)
    fun st' hm hpc' ↦ ?_
  simp only [PcOk] at hpc'
  have hd : st'.data.dmem = st.data.dmem := hm.dmem_eq (Env.wf_nil _) h30
  refine exit_step hp hpre (hpc'.trans (lbl_20 hp))
    (Body.congr hb (fun r _ ↦ keptBut_reg hm hk30 (by simp)) (keptBut_reg hm hk30 (by simp)) hd) ?_
    fun h ↦ absurd h hn
  rw [keptBut_reg hm hk30 (by simp), hal, decide_eq_false hn]
  rfl

/-- **The success** `b31`: AL one. -/
theorem done_step (hp : Placed code k) (hpre : TableColumnClaimsPre ev cs m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableColumnClaims.b31Offset)) (hb : Bd m0 st.data)
    (hc : ClaimsWAt st.data.dmem (reg m0 .rsi) (cs ++ tableColumnClaims ev)) :
    Eventually (step1 Host.exe) (Goal ev cs m0) st := by
  obtain ⟨-, -, -, -, -, -, h31, -, -, -, -, -, -, hk31, -, hr31⟩ := after_eq run_b31 ▸ ok_exit
  refine exec_at (hb31 hp) run_b31 (Env.wf_nil _) (fun _ h ↦ by cases h) hpc (match_nil _)
    fun st' hm hpc' ↦ ?_
  simp only [PcOk] at hpc'
  have hd : st'.data.dmem = st.data.dmem := hm.dmem_eq (Env.wf_nil _) h31
  have hfit : Fits ev cs := by
    have := hc.len_le
    rw [Array.size_append] at this
    exact this
  refine exit_step hp hpre (hpc'.trans (lbl_20 hp))
    (Body.congr hb (fun r hcs ↦ keptBut_reg hm hk31 (by
      intro h; simp at h; subst h; simp [calleeSaved] at hcs)) (keptBut_reg hm hk31 (by simp)) hd)
    ?_ fun _ ↦ by rw [hd]; exact hc
  show (st'.data.regs.get64 .rax).toNat % 256 = _
  rw [hm.regs _ _ (hr31 (.rax, .bin .merge .W8 (.reg .rax) (.lit 1)) (by simp)),
    decide_eq_true hfit]
  exact NativeRustcVmX64.Transcript.merge_one_mod _

end

end NativeRustcVmX64.Tables.ColumnClaims
