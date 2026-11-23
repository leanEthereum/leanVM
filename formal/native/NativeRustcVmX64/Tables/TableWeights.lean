module

public import NativeRustcVmX64.Tables.TableWeights.Ends
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.TableWeights.Names

/-!
# `table_weights` on x86-64

**`table_weights_spec`**: rustc's `table_weights`, placed anywhere in the program, meets
`TableWeightsPre`/`TableWeightsPost` given `EW::mul`'s contract. The entry (`entry_step`) into the
loop (`turn`, one coordinate a turn) or, for an empty point, straight to the exit; the exit
(`exit_step`) stores the six weights at `out` and returns.
-/

namespace NativeRustcVmX64.Tables.TableWeights

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Tables NativeRustcVmX64.Arrays
open NativeRustcVmX64.Vm.TableWeights NativeRustcVmX64.Field
open NativeRustcVm (wordOf wordsOf ewsOf)

public section

variable [Host] {k : Nat}

/-- `table_weights`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ TableWeightsPost m0 st.data

/-- **The exit**: the weights stored at `out`, the epilogue. -/
theorem exit_step (hp : Placed code k) {m0 : MachineData} (hpre : TableWeightsPre m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b13Offset)) (hI : Fin m0 st.data) :
    Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hS, hOr, hOo, -, -, -⟩ := hpre
  have hb : Body m0 256 tableWeightsStack slots (reg m0 .rdi) 96 st.data := Body.widen hI.body
  have hOo' : Apart (stackBelow m0 256) (256 + 8) (reg m0 .rdi) 96 := by
    have h1 := h256
    have hS1 := hS.1
    have hr := (rspOf m0).isLt
    have hh := hOo
    unfold OffStack Apart at hh
    unfold Apart
    rw [stackBelow_toNat (by omega)]
    rw [stackBelow_toNat hS1] at hh
    omega
  have hwf := wf_two (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS h256) hb.kept
    (show Readable st.data (reg m0 .rdi) 96 from ⟨fun i hi ↦ hb.kept _ (hOr.1 i hi), hOr.2⟩) hOo'
  have hm : Match (Env.ofMachine st.data [(stackBelow m0 256, 256 + 8), (reg m0 .rdi, 96)])
      outS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb.rsp, trivial⟩ trivial trivial
      ⟨by beta_reduce; rw [eval_load, load_fw rfl rfl, hI.out]; simp, trivial⟩
  obtain ⟨hregs, hw, hwr, hkr⟩ := after_eq run_b13a ▸ b13a_ok
  refine exec_at (hb13 hp).1 run_b13a hwf (fun _ h ↦ by cases h) hpc hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, show b13a.length = 24 from rfl] at hpc1
  have hb1 := Body.of_store hb hwf hm hm1 hkr hw (fun _ h ↦ h) fun p hp' ↦ (slots_ok p hp').2
  -- the weights at `out`
  have hout : NativeRustcVm.EWsAt st1.data.dmem (reg m0 .rdi)
      (tableWeights (heightsOf m0.dmem (reg m0 .rsi)) (slice m0 (reg m0 .rdx) (reg m0 .rcx))
        (slice m0 (reg m0 .r8) (reg m0 .r9))).toList := by
    show NativeRustcVm.EWsAt _ _ (tableWeights (H m0) (E m0) (P m0)).toList
    rw [tableWeights_W, NativeRustcVm.ewsAt_iff]
    intro i hi
    have hi6 : i < 6 := by simpa [W_size] using hi
    have he : ∀ (o : Nat) (u v : Sym), (o, u) ∈ [(0, Sym.load 0 16 8), (8, .load 0 24 8),
        (16, .load 0 32 8), (24, .load 0 40 8), (32, .load 0 48 8), (40, .load 0 56 8),
        (48, .load 0 64 8), (56, .load 0 72 8), (64, .load 0 88 8), (72, .load 0 80 8),
        (80, .reg .rax), (88, .reg .rdx)] → (o + 8, v) ∈ [(0, Sym.load 0 16 8), (8, .load 0 24 8),
        (16, .load 0 32 8), (24, .load 0 40 8), (32, .load 0 48 8), (40, .load 0 56 8),
        (48, .load 0 64 8), (56, .load 0 72 8), (64, .load 0 88 8), (72, .load 0 80 8),
        (80, .reg .rax), (88, .reg .rdx)] → o + 16 ≤ 96 →
        NativeRustcVm.EWAt st1.data.dmem (reg m0 .rdi + BitVec.ofNat 64 o)
          (ewArg (u.eval (Env.ofMachine st.data [(stackBelow m0 256, 256 + 8), (reg m0 .rdi, 96)]))
            (v.eval (Env.ofMachine st.data [(stackBelow m0 256, 256 + 8), (reg m0 .rdi, 96)]))) :=
      fun o u v hu hv hle ↦ ewAt_of_writes hm1 (r := 1) rfl hle (hwr _ hu) (hwr _ hv)
    rw [Array.getElem_toList, ← getD_of_lt (d := (0 : EW)) (by rw [W_size]; exact hi6)]
    match i, hi6 with
    | 0, _ => have := he 0 (.load 0 16 8) (.load 0 24 8) (by simp) (by simp) (by omega)
              rw [eval_load, eval_load, load_fw rfl rfl, load_fw rfl rfl] at this
              rw [← hI.w 0 (by omega)]; exact this
    | 1, _ => have := he 16 (.load 0 32 8) (.load 0 40 8) (by simp) (by simp) (by omega)
              rw [eval_load, eval_load, load_fw rfl rfl, load_fw rfl rfl] at this
              rw [← hI.w 1 (by omega)]; exact this
    | 2, _ => have := he 32 (.load 0 48 8) (.load 0 56 8) (by simp) (by simp) (by omega)
              rw [eval_load, eval_load, load_fw rfl rfl, load_fw rfl rfl] at this
              rw [← hI.w 2 (by omega)]; exact this
    | 3, _ => have := he 48 (.load 0 64 8) (.load 0 72 8) (by simp) (by simp) (by omega)
              rw [eval_load, eval_load, load_fw rfl rfl, load_fw rfl rfl] at this
              rw [← hI.w 3 (by omega)]; exact this
    | 4, _ => have := he 64 (.load 0 88 8) (.load 0 80 8) (by simp) (by simp) (by omega)
              rw [eval_load, eval_load, load_fw rfl rfl, load_fw rfl rfl] at this
              rw [← hI.w 4 (by omega)]; exact this
    | 5, _ => have := he 80 (.reg .rax) (.reg .rdx) (by simp) (by simp) (by omega)
              rw [eval_reg, eval_reg] at this
              rw [← hI.w5]; exact this
  -- the epilogue
  have hwf2 := hb1.wf (vars := fun _ ↦ 0) (ret := 0) hS h256
  refine exec_at (hb13 hp).2 run_b13b hwf2 (fun _ h ↦ by cases h) hpc1 hb1.mid_match
    fun st2 hm2 hpc2 ↦ .done _ ?_
  obtain ⟨hr, hmem⟩ := after_eq run_b13b ▸ b13b_ok
  obtain ⟨hpc', hrsp, hdm, hsaved⟩ := hb1.done hS h256 hm2 hpc2 hr hmem
    (ret_not_in hS hOr.2 hOo)
  exact ⟨hpc', hrsp, by rw [hdm]; exact hout, fun p hp' ↦ by rw [hdm]; exact hb1.same p hp',
    hsaved⟩

/-- **`table_weights` meets its contract.** -/
theorem table_weights_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.TableWeights.entryLabel) TableWeightsPre TableWeightsPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  refine Eventually.bind (entry_step hp hpre) fun st h ↦ ?_
  rcases h with ⟨hpc, hI⟩ | ⟨hpc, hF⟩
  · refine Sym.loop (fun c st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b10Offset) ∧ ∃ i, n m0 - i = c ∧
      It m0 i st.data) (fun c st ⟨hpc, i, hc, hI⟩ ↦ ?_) ⟨hpc, 0, rfl, hI⟩
    refine Eventually.bind (turn hp hmul hpre hpc hI) fun st' h ↦ ?_
    rcases h with ⟨hpc', hI'⟩ | ⟨hpc', hF⟩
    · exact .done _ (Or.inr ⟨n m0 - (i + 1), by have := hI'.lt; omega, hpc', i + 1, rfl, hI'⟩)
    · exact Eventually.mono (exit_step hp hpre hpc' hF) fun _ h ↦ Or.inl h
  · exact exit_step hp hpre hpc hF

end

end NativeRustcVmX64.Tables.TableWeights
