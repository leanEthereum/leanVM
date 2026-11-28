module

public import NativeRustcVmX64.Tables.ColumnClaims.Setup

/-!
# `table_column_claims`: the entry and the passage between tables (x86-64)

`entry`: the prologue (`b0a`) and table `0`'s setup (`b0b`, the evaluations at RDI) reach table
`0`'s loop head. `next`: after table `t`'s last value, table `t + 1`'s setup reaches its loop head.
-/

namespace NativeRustcVmX64.Tables.ColumnClaims

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Tables NativeRustcVmX64.Arrays
open NativeRustcVmX64.Vm.TableColumnClaims NativeRustcVmX64.Field NativeRustcVmX64.Tables
open NativeRustcVm.Layout (claimsBytes ClaimsWAt claimCap pointCap Same)
open NativeRustcVm (wordOf ewOf ewsOf)

public section

variable {ev : Array (Array EW × Array EW)} {cs : Array ColumnClaimW} {m0 : MachineData}

theorem pre_zero : pre ev 0 0 = [] := by simp [pre]

theorem claims_next {t : Nat} {d : DataMem} {a : BitVec 64}
    (h : ClaimsWAt d a (cs ++ (pre ev t (cnt ev t)).toArray)) :
    ClaimsWAt d a (cs ++ (pre ev (t + 1) 0).toArray) := by
  rwa [show cnt ev t = (claimsOf ev t).length from (length_claimsOf t).symm, pre_next] at h

theorem claims_end (h6 : ev.size = 6) {d : DataMem} {a : BitVec 64}
    (h : ClaimsWAt d a (cs ++ (pre ev 5 (cnt ev 5)).toArray)) :
    ClaimsWAt d a (cs ++ tableColumnClaims ev) := by
  have := claims_next h
  rwa [pre_six h6, Array.toArray_toList] at this

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableColumnClaims.b0Offset) ∧
    b0b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableColumnClaims.b0Offset + b0a.length) := by
  have h := b0_in_code.trans hp.1 (by simp [b0])
  rw [← List.take_append_drop 9 b0] at h
  exact h.append

/-- **The entry**: table `0`'s loop head, no value pushed. -/
theorem entry (hp : Placed code k) (hpre : TableColumnClaimsPre ev cs m0) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableColumnClaims.b1Offset) ∧
      LoopAt ev cs m0 R04 0 0 st'.data) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.TableColumnClaims.b0Offset)⟩ := by
  obtain ⟨hS, -, -, hCR, hCO, hcl⟩ := pre_parts hpre
  have hwf := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS h64) fun _ h ↦ h
  have hm : Match (frameEnv m0 m0 64) entryS m0 := match_frame
  obtain ⟨hsl, hw0, hsp0, hr0⟩ := after_eq run_b0a ▸ ok_b0a
  refine exec_then (hb0 hp).1 run_b0a hwf (fun _ h ↦ by cases h) hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, show b0a.length = 9 from rfl] at hpc1
  have hb1 : Bd m0 st1.data := Body.of_entry hS h64 hm1 hsp0 hsl
    (by rw [freeRegs_slots]; intro r h; cases h) hw0
  have hrdi : reg st1.data .rdi = reg m0 .rdi := hm1.regs _ _ (hr0 (.rdi, .reg .rdi) (by simp))
  have hrbx : reg st1.data .rbx = reg m0 .rsi := hm1.regs _ _ (hr0 (.rbx, .reg .rsi) (by simp))
  have hc1 : ClaimsWAt st1.data.dmem (reg m0 .rsi) cs :=
    NativeRustcVm.Tables.ClaimsWAt.of_same hcl fun i hi ↦ frame_keep hwf hm1 (by omega) hw0
      (not_inRange_le (by omega) (not_frame hS h64 hCR.2 hCO
        (NativeRustcVm.inRange_add hi (by have := hCR.2; unfold NoWrap at this; omega))))
  -- table `0`'s setup
  have hev := ev_part hpre (o := 0) (k := tableEvalsBytes) (by decide) (by omega)
  rw [add_ofNat_zero] at hev
  have hap : Apart (stackBelow m0 64) (64 + 8) (reg m0 .rdi) tableEvalsBytes := by
    have h1 := hS.1
    have h2 := h64
    have hr := (rspOf m0).isLt
    have hh := hev.2.1
    unfold OffStack Apart at hh
    unfold Apart
    rw [stackBelow_toNat (by omega)]
    rw [stackBelow_toNat h1] at hh
    omega
  have hwf2 := wf_two (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS h64) hb1.kept
    (show Readable st1.data (reg m0 .rdi) tableEvalsBytes from
      ⟨fun i hi ↦ hb1.kept _ (hev.1.1 i hi), hev.1.2⟩) hap
  have hm2 : Match (Env.ofMachine st1.data [(stackBelow m0 64, 64 + 8),
      (reg m0 .rdi, tableEvalsBytes)]) evS st1.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb1.rsp, trivial⟩ trivial trivial
      ⟨by show reg st1.data .rdi = _; rw [hrdi]; simp, trivial⟩
  obtain ⟨hsh, hw1, hw8, hrb⟩ := after_eq run_b0b ▸ ok_b0b
  have hka := (after_eq run_b0b ▸ keeps_set).1
  refine exec_at (hb0 hp).2 run_b0b hwf2 (fun _ h ↦ by cases h) hpc1 hm2
    fun st2 hm3 hpc2 ↦ .done _ ⟨by simp only [PcOk, show b0b.length = 16 from rfl] at hpc2; exact hpc2, ?_⟩
  have hsm := same_ev hpre hb1
  have hld : ∀ o, (Env.ofMachine st1.data [(stackBelow m0 64, 64 + 8),
      (reg m0 .rdi, tableEvalsBytes)]).load 1 o 8 = (wordOf st1.data.dmem (reg m0 .rdi +
        BitVec.ofNat 64 o)).toBitVec := fun o ↦ by
    rw [load8_eq, Env.base_eq (b := reg m0 .rdi) (n := tableEvalsBytes) rfl, Env.ofMachine_mem0]
  obtain ⟨ha, hn, hpp, hl, hcc, -⟩ := shapes_regs (t := 0) hpre (by decide) hsh hm3
    (by rw [eval_reg, Env.ofMachine_regs]; exact hrdi)
    (by rw [hld]; exact cnt_word hpre hsm (by decide))
    (by rw [hld]; exact plen_word hpre hsm (by decide))
  have hwr : ∀ p, ¬InRange (stackBelow m0 64) 16 p → st2.data.dmem.get? p = st1.data.dmem.get? p :=
    fun p hp' ↦ frame_keep hwf2 hm3 (by omega) hw1 hp'
  refine ⟨Body.of_frame hb1 hS h64 hwf2 hm2 hm3 hka hw1 (by omega) slots_ok, ?_, ?_, Nat.zero_le _,
    ha, hn, hpp, hl, ?_, ?_⟩
  · have := wordAt_of_write hm3 (r := 0) (b := stackBelow m0 64) (sz := 64 + 8) rfl (o := 8)
      (by omega) hw8
    unfold fw
    rw [NativeRustcVm.wordOf_of_wordAt this, eval_reg, Env.ofMachine_regs]
    exact hrdi
  · rw [show reg st2.data .rbx = _ from hm3.regs _ _ (hrb (.rbx, .reg .rbx) (by simp)), eval_reg,
      Env.ofMachine_regs]
    exact hrbx
  · rw [hcc]; unfold base; rw [bases_eq]; rfl
  · rw [pre_zero]
    rw [show cs ++ ([] : List ColumnClaimW).toArray = cs from by simp]
    exact NativeRustcVm.Tables.ClaimsWAt.of_same hc1 fun i hi ↦ hwr _
      (not_inRange_le (by omega) (not_frame hS h64 hCR.2 hCO
        (NativeRustcVm.inRange_add hi (by have := hCR.2; unfold NoWrap at this; omega))))

/-- **The next table**: after table `t`'s last value, table `t + 1`'s setup. -/
theorem next (hpre : TableColumnClaimsPre ev cs m0) {R R' : Regs} {t c : Nat} (ht : t + 1 < 6)
    (hc : c + 1 = base (t + 1)) {D : List Directive} {kk : Nat} (hD : D.IsInfixAt Host.prog kk)
    (hx : exec D setS = some (after D setS, .fall))
    (hs : Shapes R' (t + 1) c (.load 0 8 8) false (after D setS) ∨
      Shapes R' (t + 1) c (.load 0 8 8) true (after D setS))
    (hmem : (after D setS).mem = []) (hka : keepsAll setS (after D setS) (freeRegs slots) = true)
    (hrbx : RegsAre (after D setS) [(.rbx, .reg .rbx)])
    {Q : MachineState → Prop}
    (cont : ∀ st, st.pc = Host.addrOf (kk + D.length) → LoopAt ev cs m0 R' (t + 1) 0 st.data →
      Eventually (step1 Host.exe) Q st)
    {st : MachineState} (hpc : st.pc = Host.addrOf kk) (hL : LoopAt ev cs m0 R t (cnt ev t) st.data) :
    Eventually (step1 Host.exe) Q st :=
  Eventually.bind (setup hpre ht hc hD hx hs hmem hka hrbx hpc hL.body hL.ev8 hL.rbx
    (claims_next hL.claims)) fun st' h ↦ cont st' h.1 h.2

end

end NativeRustcVmX64.Tables.ColumnClaims
