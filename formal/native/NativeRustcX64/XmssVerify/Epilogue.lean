module

public import NativeRustcX64.Code.Xmss.XmssVerify.Names

public import NativeRustcX64.XmssVerify.Top

/-!
# `xmss_verify`: the comparison with the key's root and the return (x86-64)

Block 26: the top root in RCX and RDX compared with the key's root at `40`, RAX `1` if equal else
`0`, to block 28 (`final`); block 27 (`.LXmssVerify_10`, the failure): RAX `0` (`fail`);
block 28 (`.LXmssVerify_9`): RSP back to the pushed registers, RBX, R12 to R15, RBP popped,
`retq` (`epilogue`).
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash NativeRustc NativeRustc.Xmss

set_option Elab.async false

@[expose] public section

/-- Block 26's test: RCX and RDX are the 16 bytes at `40`. -/
def eqRoot : SBool :=
  .cmp .eq .W64 (.bin .or .W64 (.bin .xor .W64 (.reg .rdx) (.load 0 48 8))
    (.bin .xor .W64 (.reg .rcx) (.load 0 40 8))) (.lit 0)

end

public section

theorem run_b26' : exec b26 (stF []) = some (after b26 (stF []), .jump NativeRustcX64.Xmss.XmssVerify.label_9) := by
  rw [after_eq run_b26]; exact run_b26

theorem st26_facts : (after b26 (stF [])).reg .rsp = some (.ptr 0 24) ∧
    (after b26 (stF [])).reg .rax = some (.bin .merge .W8 (.lit 0) (.ite eqRoot (.lit 1) (.lit 0))) ∧
    (after b26 (stF [])).mem = [] := by
  decide +kernel

theorem st27_facts : (after b27 (stF [])).reg .rsp = some (.ptr 0 24) ∧
    (after b27 (stF [])).reg .rax = some (.lit 0) ∧ (after b27 (stF [])).mem = [] := by
  decide +kernel

theorem run_b28' : exec b28 (stF []) = some (after b28 (stF []), .ret (.load 0 5808 8)) := by
  rw [after_eq run_b28]; exact run_b28

theorem st28_facts : (after b28 (stF [])).reg .rsp = some (.ptr 0 5816) ∧
    (after b28 (stF [])).reg .rax = some (.reg .rax) ∧
    (∀ j < 6, (after b28 (stF [])).reg (saveRegs.getD j .rax) = some (.load 0 (5760 + 8 * j) 8)) ∧
    (after b28 (stF [])).mem = [] := by
  decide +kernel

theorem eqRoot_eval [Labels] (env : Env) :
    eqRoot.eval env = decide (env.regs .rcx = env.load 0 40 8 ∧ env.regs .rdx = env.load 0 48 8) := by
  simp only [eqRoot, SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64]
  by_cases h1 : env.regs .rcx = env.load 0 40 8 <;> by_cases h2 : env.regs .rdx = env.load 0 48 8 <;>
    simp [h1, h2, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]

theorem merge_eval [Labels] (env : Env) (c : SBool) :
    (Sym.bin .merge .W8 (.lit 0) (.ite c (.lit 1) (.lit 0))).eval env =
      if c.eval env then 1 else 0 := by
  simp only [Sym.eval, BinOp.apply]
  cases c.eval env <;> rfl

theorem regBytes_inj {x y : BitVec 64} (h : regBytes x = regBytes y) : x = y := by
  rw [← ofBytes_regBytes x, ← ofBytes_regBytes y, h]

end

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

/-- **The epilogue**: from block 28 with `Common`, the return to the caller, RSP 8 above the
entry's, RAX kept, memory as at entry outside the stack, the entry's callee-saved registers. -/
public theorem epilogue {k : Nat} (hp : Placed code k) (P : Pre w m₀) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b28Offset)) (C : Common m₀ st.data)
    (hrsp : rspOf st.data = ad m₀ (fr + 24)) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m₀ ∧
      rspOf st'.data = rspOf m₀ + 8#64 ∧ reg st'.data .rax = reg st.data .rax ∧
      SameOutside m₀.dmem st'.data.dmem
        (InRange (stackBelow m₀ xmssVerifyStack) xmssVerifyStack) ∧
      Saved m₀ st'.data) st := by
  let env := Env.ofMachine st.data (frameRs m₀) (fun _ => 0) 0
  have hwf : env.WF := frameG_wf P C.kept
  have hm : Match env (stF []) st.data := match_stG P C.same hrsp trivial
  have hread := hm.read hwf (r := 0) (o := 5808) (n := 8) rfl (by decide) (by decide)
  obtain ⟨esp, eax, esave, emem⟩ := st28_facts
  refine exec_at (b28_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b28' hwf
    (fun _ h => nomatch h) hpc hm fun st' hm' hpc' => .done _ ?_
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf emem
  have hsave : ∀ j < 6, reg st'.data (saveRegs.getD j .rax) = reg m₀ (saveRegs.getD j .rax) :=
    fun j hj => by
      rw [show reg st'.data _ = _ from hm'.regs _ _ (esave j hj)]
      show env.load 0 (5760 + 8 * j) 8 = _
      rw [Env.load_of_bytesAt (length_regBytes _) (by
        rw [show env.base 0 + BitVec.ofNat 64 (5760 + 8 * j) = ad m₀ (fr + 5760 + 8 * j) by
          rw [show env.base 0 = ad m₀ fr from rfl, ad_add, Nat.add_assoc]]
        exact C.save j hj), ofBytes_regBytes]
  have hslot : ∀ i < 8, st.data.dmem.get? (rspOf m₀ + BitVec.ofNat 64 i) =
      m₀.dmem.get? (rspOf m₀ + BitVec.ofNat 64 i) := fun i hi => by
    apply C.same
    rw [← sp_eq m₀, ad_add]
    have h := P.not_inRange_ad (o := 0) (s := 9248) (x := fr + 5808 + i) (by omega) (by fro)
      (Or.inr (by fro))
    rwa [show ad m₀ 0 = lo m₀ from BitVec.add_zero _] at h
  rw [show env.base 0 + BitVec.ofNat 64 5808 = rspOf m₀ from (ad_add _ _ _).trans (sp_eq m₀),
    loadInt_congr hslot] at hread
  refine ⟨?_, ?_, hm'.regs _ _ eax, by rw [hd]; exact C.same, fun r hr => ?_, by
    rw [hd]; exact C.kept⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    exact (retOf_of_loadInt hread).symm
  · refine (hm'.regs _ _ esp).trans ((eval_ptr0 5816).trans ?_)
    rw [← sp_eq m₀, ad_add]
  · cases r <;> simp only [calleeSaved, Bool.false_eq_true] at hr
    · exact hsave 0 (by decide)
    · exact hsave 5 (by decide)
    · exact hsave 1 (by decide)
    · exact hsave 2 (by decide)
    · exact hsave 3 (by decide)
    · exact hsave 4 (by decide)

/-- **The failure** (block 27): RAX `0`, then the epilogue. -/
public theorem fail {k : Nat} (hp : Placed code k) (P : Pre w m₀) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b27Offset)) (h : FailAt w m₀ st.data) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m₀ ∧
      rspOf st'.data = rspOf m₀ + 8#64 ∧ reg st'.data .rax = (if xmssVerify w then 1 else 0) ∧
      SameOutside m₀.dmem st'.data.dmem
        (InRange (stackBelow m₀ xmssVerifyStack) xmssVerifyStack) ∧
      Saved m₀ st'.data) st := by
  let env := Env.ofMachine st.data (frameRs m₀) (fun _ => 0) 0
  have hwf : env.WF := frameG_wf P h.common.kept
  have hm : Match env (stF []) st.data := match_stG P h.common.same h.rsp trivial
  obtain ⟨esp, eax, emem⟩ := st27_facts
  refine fall_step (b27_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b27 hwf hpc hm
    fun st' hpc' hm' => ?_
  change Match _ (after b27 (stF [])) st'.data at hm'
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf emem
  refine NativeRustcX64.Eventually.mono (epilogue hp P (hpc'.trans rfl) (h.common.congr hd)
    ((hm'.regs _ _ esp).trans (eval_ptr0 _))) fun s ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, ?_, h4, h5⟩
  rw [h3, show reg st'.data .rax = _ from hm'.regs _ _ eax, h.bad]
  rfl

/-- **The comparison** of the top root with the key's root (block 26), then the epilogue. -/
public theorem final {k : Nat} (hp : Placed code k) (P : Pre w m₀) {leaf : List UInt8}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b26Offset)) (h : TreeAt1 w m₀ leaf st.data 16) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m₀ ∧
      rspOf st'.data = rspOf m₀ + 8#64 ∧
      reg st'.data .rax = (if pf (pp w) 1 (li1 w).toNat (topL w).path leaf 16 == root w then 1
        else 0) ∧
      SameOutside m₀.dmem st'.data.dmem
        (InRange (stackBelow m₀ xmssVerifyStack) xmssVerifyStack) ∧
      Saved m₀ st'.data) st := by
  let env := Env.ofMachine st.data (frameRs m₀) (fun _ => 0) 0
  have hwf : env.WF := frameG_wf P h.common.kept
  have hm : Match env (stF []) st.data := match_stG P h.common.same h.rsp trivial
  obtain ⟨esp, eax, emem⟩ := st26_facts
  refine exec_at (b26_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b26' hwf
    (fun _ h => nomatch h) hpc hm fun st' hm' hpc' => ?_
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf emem
  have hpc'' : st'.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b28Offset) :=
    hpc'.trans (hp.label NativeRustcX64.Xmss.XmssVerify.label_9_at)
  refine NativeRustcX64.Eventually.mono (epilogue hp P hpc'' (h.common.congr hd)
    ((hm'.regs _ _ esp).trans (eval_ptr0 _))) fun s ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, ?_, h4, h5⟩
  rw [h3, show reg st'.data .rax = _ from hm'.regs _ _ eax, merge_eval, eqRoot_eval]
  -- The key's root and the top root.
  have hpk := halves (bytes_take h.pk 16)
  have hr0 : regBytes (env.load 0 40 8) = (pkB w).take 8 := by
    refine regBytes_frame (by simp [length_pkB]) ?_
    have := hpk.1
    rwa [List.take_take, show min 8 16 = 8 from rfl] at this
  have hr1 : regBytes (env.load 0 48 8) = ((pkB w).drop 8).take 8 := by
    refine regBytes_frame (by simp [length_pkB]) ?_
    have := hpk.2
    rw [List.drop_take, List.take_take, show min 8 (16 - 8) = 8 from rfl] at this
    exact this
  have hroot : root w = regBytes (env.load 0 40 8) ++ regBytes (env.load 0 48 8) := by
    rw [hr0, hr1, root, ← List.take_add]
  rw [← h.cur, hroot]
  generalize env.load 0 40 8 = L0
  generalize env.load 0 48 8 = L1
  show (if decide (reg st.data .rcx = L0 ∧ reg st.data .rdx = L1) = true then (1 : BitVec 64)
    else 0) = _
  by_cases hA : reg st.data .rcx = L0 ∧ reg st.data .rdx = L1
  · rw [hA.1, hA.2]
    simp
  · have hne : (regBytes (reg st.data .rcx) ++ regBytes (reg st.data .rdx) ==
        regBytes L0 ++ regBytes L1) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro he
      obtain ⟨e1, e2⟩ := List.append_inj he (by rw [length_regBytes, length_regBytes])
      exact hA ⟨regBytes_inj e1, regBytes_inj e2⟩
    rw [decide_eq_false hA, hne]

end NativeRustcX64.Xmss.XmssVerify
