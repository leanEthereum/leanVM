module

public import NativeRustcVmX64.Tables.ColumnClaims.Entry
public import NativeRustcVmX64.Code.Vm.PushClaim.Names
public import NativeRustcVmX64.Code.Vm.TableColumnClaims.Names

/-!
# `table_column_claims` on x86-64

**`tableColumnClaims_spec`**: rustc's `table_column_claims`, placed anywhere in the program, meets
`TableColumnClaimsPre`/`TableColumnClaimsPost` given `push_claim`'s contract. rustc unrolled the
loop over the six tables: the entry (`entry`) sets table `0`'s loop registers; each table's loop
(`loop`) pushes its values' claims, then the next table's setup (`next`); a failed push (the claims
do not fit) goes to the failure (AL zero), after the last table to the success (AL one, the claims
`cs ++ tableColumnClaims evals`).
-/

namespace NativeRustcVmX64.Tables.ColumnClaims

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Tables NativeRustcVmX64.Arrays
open NativeRustcVmX64.Vm.TableColumnClaims NativeRustcVmX64.Field NativeRustcVmX64.Tables
open NativeRustcVm.Layout (claimsBytes ClaimsWAt claimCap pointCap Same)

public section

variable [Host] {k : Nat}

omit [Host] in
theorem base_lit (t : Nat) (ht : t < 6) : base t = #[5, 18, 31, 38, 52, 66][t]! := by
  unfold base; rw [bases_eq]
  match t, ht with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => rfl

/-- **`table_column_claims` meets its contract.** -/
theorem tableColumnClaims_spec (hp : Placed code k)
    (hpush : ∀ cs, Spec (Labels.label NativeRustcVmX64.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    {ev : Array (Array EW × Array EW)} {cs : Array ColumnClaimW} :
    Spec (Labels.label NativeRustcVmX64.Vm.TableColumnClaims.entryLabel) (TableColumnClaimsPre ev cs)
      (TableColumnClaimsPost ev cs) := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmX64.Vm.TableColumnClaims.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.TableColumnClaims.b0Offset) from hp.label NativeRustcVmX64.Vm.TableColumnClaims.entry_at]
  show Eventually _ (Goal ev cs m0) _
  have h6 := size_ev hpre
  obtain ⟨s1, s2, s3, s4, s5, m5, m10, m15, m20, m26, r5, r10, r15, r20, r26⟩ := ok_set
  obtain ⟨-, k5, k10, k15, k20, k26⟩ := keeps_set
  obtain ⟨tm1, tm6, tm11, tm16, tm21, tm27, tk1, tk6, tk11, tk16, tk21, tk27⟩ := ok_test
  obtain ⟨p2, p7, p12, p17, p22, p28⟩ := ok_push
  obtain ⟨ar3, ar8, ar13, ar18, ar23, ar29, am3, am8, am13, am18, am23, am29,
    ak3, ak8, ak13, ak18, ak23, ak29⟩ := ok_after
  obtain ⟨em4, em9, em14, em19, -, -, -, ek4, ek9, ek14, ek19, -⟩ := ok_exit
  have hR04 : ([R04.n, R04.p, R04.l, R04.c, .rbx, .r14].all fun r ↦
      calleeSaved r && !([R04.a, .rax, .rcx].contains r)) = true := by decide
  have hR5 : ([R5.n, R5.p, R5.l, R5.c, .rbx, .r14].all fun r ↦
      calleeSaved r && !([R5.a, .rax, .rcx].contains r)) = true := by decide
  have hRa04 : calleeSaved R04.a = false ∧ R04.a ≠ .rsp := by decide
  have hRa5 : calleeSaved R5.a = false ∧ R5.a ≠ .rsp := by decide
  have hx04 : ∀ env : Env, ((Sym.reg .rax).eval env).toNat % 256 = (env.regs .rax).toNat % 256 :=
    fun _ ↦ rfl
  have hx5 : ∀ env : Env, ((Sym.un .trunc .W32 (.reg .rax)).eval env).toNat % 256 =
      (env.regs .rax).toNat % 256 := fun _ ↦ NativeRustcVmX64.Transcript.trunc32_mod _
  -- the success, after table `5`
  have d5 : ∀ st : MachineState, st.pc = Labels.label NativeRustcVmX64.Vm.TableColumnClaims.label_16 →
      LoopAt ev cs m0 R5 5 (cnt ev 5) st.data → Eventually (step1 Host.exe) (Goal ev cs m0) st :=
    fun st hpc hL ↦ done_step hp hpre (hpc.trans (hp.label NativeRustcVmX64.Vm.TableColumnClaims.label_16_at)) hL.body
      (claims_end h6 hL.claims)
  -- table `5`
  have t5 : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableColumnClaims.b27Offset) →
      LoopAt ev cs m0 R5 5 0 st.data → Eventually (step1 Host.exe) (Goal ev cs m0) st :=
    fun st hpc hL ↦ loop hpush hpre (by decide) hR5 hRa5 (b27_in_code.trans hp.1 (by simp [b27]))
      rfl (by rw [after_eq run_b27]; exact run_b27) tm27 tk27
      (b28_in_code.trans hp.1 (by simp [b28])) rfl (by rw [after_eq run_b28]; exact run_b28) p28
      (b29_in_code.trans hp.1 (by simp [b29])) rfl (by rw [after_eq run_b29]; exact run_b29)
      (ar29 (R5.a, .reg .r14) (by simp)) am29 ak29 hx5
      (fun st st' hm _ ↦ by
        rw [show reg st' .rax = _ from hm.regs _ _ (ar29 (.rax, .lit 0) (by simp))]; rfl)
      (hp.label NativeRustcVmX64.Vm.TableColumnClaims.label_15_at) (fun st hpc hb hal hn ↦ fail30 hp hpre hpc hb hal hn) d5 0 st hpc hL
  -- table `4`
  have t4 : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableColumnClaims.b21Offset) →
      LoopAt ev cs m0 R04 4 0 st.data → Eventually (step1 Host.exe) (Goal ev cs m0) st :=
    fun st hpc hL ↦ loop hpush hpre (by decide) hR04 hRa04 (b21_in_code.trans hp.1 (by simp [b21]))
      rfl (by rw [after_eq run_b21]; exact run_b21) tm21 tk21
      (b22_in_code.trans hp.1 (by simp [b22])) rfl (by rw [after_eq run_b22]; exact run_b22) p22
      (b23_in_code.trans hp.1 (by simp [b23])) rfl (by rw [after_eq run_b23]; exact run_b23)
      (ar23 (R04.a, .reg .r14) (by simp)) am23 ak23 hx04
      (fun st st' hm h ↦ by
        rw [show reg st' .rax = _ from hm.regs _ _ (ar23 (.rax, .reg .rax) (by simp))]; exact h)
      (hp.label NativeRustcVmX64.Vm.TableColumnClaims.label_12_at) (fun st hpc hb _ hn ↦ fail_step hp hpre hpc hb hn)
      (fun st hpc hL ↦ next (t := 4) hpre (by decide) (by rw [base_lit 5 (by decide)]; rfl)
        (b26_in_code.trans hp.1 (by simp [b26])) (by rw [after_eq run_b26]; exact run_b26)
        (Or.inr s5) m26 k26 r26 t5 (hpc.trans (hp.label NativeRustcVmX64.Vm.TableColumnClaims.label_14_at)) hL) 0 st hpc hL
  -- table `3`
  have t3 : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableColumnClaims.b16Offset) →
      LoopAt ev cs m0 R04 3 0 st.data → Eventually (step1 Host.exe) (Goal ev cs m0) st :=
    fun st hpc hL ↦ loop hpush hpre (by decide) hR04 hRa04 (b16_in_code.trans hp.1 (by simp [b16]))
      rfl (by rw [after_eq run_b16]; exact run_b16) tm16 tk16
      (b17_in_code.trans hp.1 (by simp [b17])) rfl (by rw [after_eq run_b17]; exact run_b17) p17
      (b18_in_code.trans hp.1 (by simp [b18])) rfl (by rw [after_eq run_b18]; exact run_b18)
      (ar18 (R04.a, .reg .r14) (by simp)) am18 ak18 hx04
      (fun st st' hm h ↦ by
        rw [show reg st' .rax = _ from hm.regs _ _ (ar18 (.rax, .reg .rax) (by simp))]; exact h)
      (hp.label NativeRustcVmX64.Vm.TableColumnClaims.label_9_at)
      (fun st hpc hb _ hn ↦ jump19 hp hpre (b19_in_code.trans hp.1 (by simp [b19]))
        (by rw [after_eq run_b19]; exact run_b19) em19 ek19 hpc hb hn)
      (fun st hpc hL ↦ next (t := 3) hpre (by decide) (by rw [base_lit 4 (by decide)]; rfl)
        (b20_in_code.trans hp.1 (by simp [b20])) (by rw [after_eq run_b20]; exact run_b20)
        (Or.inl s4) m20 k20 r20 t4 (hpc.trans (hp.label NativeRustcVmX64.Vm.TableColumnClaims.label_11_at)) hL) 0 st hpc hL
  -- table `2`
  have t2 : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableColumnClaims.b11Offset) →
      LoopAt ev cs m0 R04 2 0 st.data → Eventually (step1 Host.exe) (Goal ev cs m0) st :=
    fun st hpc hL ↦ loop hpush hpre (by decide) hR04 hRa04 (b11_in_code.trans hp.1 (by simp [b11]))
      rfl (by rw [after_eq run_b11]; exact run_b11) tm11 tk11
      (b12_in_code.trans hp.1 (by simp [b12])) rfl (by rw [after_eq run_b12]; exact run_b12) p12
      (b13_in_code.trans hp.1 (by simp [b13])) rfl (by rw [after_eq run_b13]; exact run_b13)
      (ar13 (R04.a, .reg .r14) (by simp)) am13 ak13 hx04
      (fun st st' hm h ↦ by
        rw [show reg st' .rax = _ from hm.regs _ _ (ar13 (.rax, .reg .rax) (by simp))]; exact h)
      (hp.label NativeRustcVmX64.Vm.TableColumnClaims.label_6_at)
      (fun st hpc hb _ hn ↦ jump19 hp hpre (b14_in_code.trans hp.1 (by simp [b14]))
        (by rw [after_eq run_b14]; exact run_b14) em14 ek14 hpc hb hn)
      (fun st hpc hL ↦ next (t := 2) hpre (by decide) (by rw [base_lit 3 (by decide)]; rfl)
        (b15_in_code.trans hp.1 (by simp [b15])) (by rw [after_eq run_b15]; exact run_b15)
        (Or.inl s3) m15 k15 r15 t3 (hpc.trans (hp.label NativeRustcVmX64.Vm.TableColumnClaims.label_8_at)) hL) 0 st hpc hL
  -- table `1`
  have t1 : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableColumnClaims.b6Offset) →
      LoopAt ev cs m0 R04 1 0 st.data → Eventually (step1 Host.exe) (Goal ev cs m0) st :=
    fun st hpc hL ↦ loop hpush hpre (by decide) hR04 hRa04 (b6_in_code.trans hp.1 (by simp [b6]))
      rfl (by rw [after_eq run_b6]; exact run_b6) tm6 tk6
      (b7_in_code.trans hp.1 (by simp [b7])) rfl (by rw [after_eq run_b7]; exact run_b7) p7
      (b8_in_code.trans hp.1 (by simp [b8])) rfl (by rw [after_eq run_b8]; exact run_b8)
      (ar8 (R04.a, .reg .r14) (by simp)) am8 ak8 hx04
      (fun st st' hm h ↦ by
        rw [show reg st' .rax = _ from hm.regs _ _ (ar8 (.rax, .reg .rax) (by simp))]; exact h)
      (hp.label NativeRustcVmX64.Vm.TableColumnClaims.label_3_at)
      (fun st hpc hb _ hn ↦ jump19 hp hpre (b9_in_code.trans hp.1 (by simp [b9]))
        (by rw [after_eq run_b9]; exact run_b9) em9 ek9 hpc hb hn)
      (fun st hpc hL ↦ next (t := 1) hpre (by decide) (by rw [base_lit 2 (by decide)]; rfl)
        (b10_in_code.trans hp.1 (by simp [b10])) (by rw [after_eq run_b10]; exact run_b10)
        (Or.inl s2) m10 k10 r10 t2 (hpc.trans (hp.label NativeRustcVmX64.Vm.TableColumnClaims.label_5_at)) hL) 0 st hpc hL
  -- table `0`
  have t0 : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableColumnClaims.b1Offset) →
      LoopAt ev cs m0 R04 0 0 st.data → Eventually (step1 Host.exe) (Goal ev cs m0) st :=
    fun st hpc hL ↦ loop hpush hpre (by decide) hR04 hRa04 (b1_in_code.trans hp.1 (by simp [b1]))
      rfl (by rw [after_eq run_b1]; exact run_b1) tm1 tk1
      (b2_in_code.trans hp.1 (by simp [b2])) rfl (by rw [after_eq run_b2]; exact run_b2) p2
      (b3_in_code.trans hp.1 (by simp [b3])) rfl (by rw [after_eq run_b3]; exact run_b3)
      (ar3 (R04.a, .reg .r14) (by simp)) am3 ak3 hx04
      (fun st st' hm h ↦ by
        rw [show reg st' .rax = _ from hm.regs _ _ (ar3 (.rax, .reg .rax) (by simp))]; exact h)
      (hp.label NativeRustcVmX64.Vm.TableColumnClaims.label_1_at)
      (fun st hpc hb _ hn ↦ jump19 hp hpre (b4_in_code.trans hp.1 (by simp [b4]))
        (by rw [after_eq run_b4]; exact run_b4) em4 ek4 hpc hb hn)
      (fun st hpc hL ↦ next (t := 0) hpre (by decide) (by rw [base_lit 1 (by decide)]; rfl)
        (b5_in_code.trans hp.1 (by simp [b5])) (by rw [after_eq run_b5]; exact run_b5)
        (Or.inl s1) m5 k5 r5 t1 (hpc.trans (hp.label NativeRustcVmX64.Vm.TableColumnClaims.label_2_at)) hL) 0 st hpc hL
  exact Eventually.bind (entry hp hpre) fun st h ↦ t0 st h.1 h.2

end

end NativeRustcVmX64.Tables.ColumnClaims
