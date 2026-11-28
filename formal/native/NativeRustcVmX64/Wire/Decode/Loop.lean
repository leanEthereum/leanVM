module

public import NativeRustcVmX64.Wire.Decode.Stream
public import NativeRustcVmX64.Code.Vm.Decode.Names
public import NativeRustcVmX64.Code.Vm.PhaseM.Names

/-!
# `decode`: the phases (x86-64)

From the loop's head (`Head`, `b9`): with every phase read, the cursor against the wire's length
(`b16`, `done_run`); else the count (`b10`, never past the room `b8` computed), `phase_m` into
phase `i`'s words (`b11`), its result (`b12`): to the head with one more phase (`step_run`), or
out with `None` (`b13`).
-/

namespace NativeRustcVmX64.Wire.Decode

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Vm.Decode
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap Frame.of_block
  after after_eq eval_ptr0 wordAt_write mapped_off stackOk_callee load_ofMachine RcAt.callee
  stackBelow_callee
  trunc32_mod)
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off Mapped.keeps PhaseAt
  phaseAt_agree)
open NativeRustcVmX64.Wire.PhaseM (bytesAt_keep wordAt_keep wordsAt_keep reader_keep iv_of_inRange
  callee_toNat toNat_toUInt64 agree_keep)
open NativeRustcVmX64.Sumcheck (testAl_eq)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- **At `phase_m`'s call** (`b11`), phase `i` of `p`. -/
structure At11 [Labels] [Host] (m0 : MachineData) (k n : Nat) (ws : List K) (p i : Nat)
    (done : List PhaseOut) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Labels.label NativeRustcVmX64.Vm.PhaseM.entryLabel
  ret : retOf st.data = Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b12Offset)
  bod : Bod m0 0 st.data
  pos : 4 ≤ LN m0
  model : decodeM (Bs m0) = tailPh (Bs m0) (streamOf n ws) done (p - i) ci
  ple : p ≤ 8
  ilt : i < p
  dlen : done.length = i
  dec : Dec m0 st.data.dmem n ws p done
  rd : ReaderAt st.data.dmem (rdA m0) (BP m0) (Bs m0) ci
  rsi : reg st.data .rsi = wd m0 (phaseBase (LN m0) i)
  rdi : reg st.data .rdi = rdA m0
  rdx : reg st.data .rdx = WK m0
  r12 : (reg st.data .r12).toNat = p
  rbp : (reg st.data .rbp).toNat = i + 1
  r13 : reg st.data .r13 = wd m0 (phaseBase (LN m0) i)
  r14 : 9 ≤ (reg st.data .r14).toNat

/-- **After `phase_m`** (`b12`), phase `i` of `p`: the phases before it kept, `phase_m`'s result. -/
structure AtR [Labels] [Host] (m0 : MachineData) (k n : Nat) (ws : List K) (p i : Nat)
    (done : List PhaseOut) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b12Offset)
  bod : Bod m0 8 st.data
  pos : 4 ≤ LN m0
  model : decodeM (Bs m0) = tailPh (Bs m0) (streamOf n ws) done (p - i) ci
  ple : p ≤ 8
  ilt : i < p
  dlen : done.length = i
  dec : Dec m0 st.data.dmem n ws p done
  res : match phaseM (Bs m0) ci with
    | some (po, c') => boolRet st.data = 1 ∧
        PhaseAt st.data.dmem (wd m0 (phaseBase (LN m0) i)) (phaseW po) ∧
        ReaderAt st.data.dmem (rdA m0) (BP m0) (Bs m0) c'
    | none => boolRet st.data = 0
  r12 : (reg st.data .r12).toNat = p
  rbp : (reg st.data .rbp).toNat = i + 1
  r13 : reg st.data .r13 = wd m0 (phaseBase (LN m0) i)
  r14 : 9 ≤ (reg st.data .r14).toNat

end

public section

/-- Six regions pairwise apart, by numbers. -/
theorem disjoint6 {a1 a2 a3 a4 a5 a6 : BitVec 64} {n1 n2 n3 n4 n5 n6 : Nat}
    (h12 : a1.toNat + n1 ≤ a2.toNat ∨ a2.toNat + n2 ≤ a1.toNat)
    (h13 : a1.toNat + n1 ≤ a3.toNat ∨ a3.toNat + n3 ≤ a1.toNat)
    (h14 : a1.toNat + n1 ≤ a4.toNat ∨ a4.toNat + n4 ≤ a1.toNat)
    (h15 : a1.toNat + n1 ≤ a5.toNat ∨ a5.toNat + n5 ≤ a1.toNat)
    (h16 : a1.toNat + n1 ≤ a6.toNat ∨ a6.toNat + n6 ≤ a1.toNat)
    (h23 : a2.toNat + n2 ≤ a3.toNat ∨ a3.toNat + n3 ≤ a2.toNat)
    (h24 : a2.toNat + n2 ≤ a4.toNat ∨ a4.toNat + n4 ≤ a2.toNat)
    (h25 : a2.toNat + n2 ≤ a5.toNat ∨ a5.toNat + n5 ≤ a2.toNat)
    (h26 : a2.toNat + n2 ≤ a6.toNat ∨ a6.toNat + n6 ≤ a2.toNat)
    (h34 : a3.toNat + n3 ≤ a4.toNat ∨ a4.toNat + n4 ≤ a3.toNat)
    (h35 : a3.toNat + n3 ≤ a5.toNat ∨ a5.toNat + n5 ≤ a3.toNat)
    (h36 : a3.toNat + n3 ≤ a6.toNat ∨ a6.toNat + n6 ≤ a3.toNat)
    (h45 : a4.toNat + n4 ≤ a5.toNat ∨ a5.toNat + n5 ≤ a4.toNat)
    (h46 : a4.toNat + n4 ≤ a6.toNat ∨ a6.toNat + n6 ≤ a4.toNat)
    (h56 : a5.toNat + n5 ≤ a6.toNat ∨ a6.toNat + n6 ≤ a5.toNat) :
    NativeRustcVm.Disjoint [⟨a1, n1⟩, ⟨a2, n2⟩, ⟨a3, n3⟩, ⟨a4, n4⟩, ⟨a5, n5⟩, ⟨a6, n6⟩] := by
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_
    (.cons (fun _ h ↦ absurd h List.not_mem_nil) .nil)))))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; assumption

/-- `phase_m`'s six places apart, from the numbers. -/
theorem pm_disjoint {Sb rc R bp O W : BitVec 64} {sp D N L : Nat} (hsp : 1296 ≤ sp)
    (hSb : Sb.toNat = sp - 1296) (hRv : R.toNat = sp - 72) (hO1 : D ≤ O.toNat)
    (hO2 : O.toNat + 395288 ≤ D + 8 * N)
    (hcS : rc.toNat + 192 ≤ sp - 1296 ∨ sp + 8 ≤ rc.toNat)
    (hcB : rc.toNat + 192 ≤ bp.toNat ∨ bp.toNat + L ≤ rc.toNat)
    (hcD : rc.toNat + 192 ≤ D ∨ D + 8 * N ≤ rc.toNat)
    (hcW : rc.toNat + 192 ≤ W.toNat ∨ W.toNat + 483584 ≤ rc.toNat)
    (hsD : D + 8 * N ≤ sp - 1296 ∨ sp + 8 ≤ D)
    (hsW : W.toNat + 483584 ≤ sp - 1296 ∨ sp + 8 ≤ W.toNat)
    (hsB : bp.toNat + L ≤ sp - 1296 ∨ sp + 8 ≤ bp.toNat)
    (hbD : bp.toNat + L ≤ D ∨ D + 8 * N ≤ bp.toNat)
    (hbW : bp.toNat + L ≤ W.toNat ∨ W.toNat + 483584 ≤ bp.toNat)
    (hdW : D + 8 * N ≤ W.toNat ∨ W.toNat + 483584 ≤ D) :
    NativeRustcVm.Disjoint [⟨Sb, 1216 + 8⟩, ⟨rc, 192⟩, ⟨R, 24⟩, ⟨bp, L⟩, ⟨O, 395288⟩,
      ⟨W, 483584⟩] :=
  disjoint6
    (by clear hcB hcD hcW hsD hsW hsB hbD hbW hdW; omega)
    (by clear hcS hcB hcD hcW hsD hsW hsB hbD hbW hdW; omega)
    (by clear hcS hcB hcD hcW hsD hsW hbD hbW hdW; omega)
    (by clear hcS hcB hcD hcW hsW hsB hbD hbW hdW; omega)
    (by clear hcS hcB hcD hcW hsD hsB hbD hbW hdW; omega)
    (by clear hcB hcD hcW hsD hsW hsB hbD hbW hdW; omega)
    hcB
    (by clear hcS hcB hcW hsD hsW hsB hbD hbW hdW; omega)
    hcW
    (by clear hcS hcB hcD hcW hsD hsW hbD hbW hdW; omega)
    (by clear hcS hcB hcD hcW hsW hsB hbD hbW hdW; omega)
    (by clear hcS hcB hcD hcW hsD hsB hbD hbW hdW; omega)
    (by clear hcS hcB hcD hcW hsD hsW hsB hbW hdW; omega)
    hbW
    (by clear hcS hcB hcD hcW hsD hsW hsB hbD hbW; omega)

theorem phaseBase_lt {L i : Nat} (hi : i < 8) : phaseBase L i + 49411 ≤ decodedWords L := by
  rw [phaseBase_eq, decodedWords_eq]; omega

variable {m0 : MachineData} [Host] {k : Nat}

/-- **Every phase read**: the cursor against the wire's length (`b16`), then the epilogue. -/
theorem done_run (hp : Placed code k) (G : Geo m0) {n : Nat} {ws : List K} {p : Nat}
    {done : List PhaseOut} {ci : Nat} {st0 : MachineState}
    (hh : Head m0 k n ws p p done ci st0) :
    Eventually (step1 Host.exe) (Post m0) st0 := by
  -- `b9`: the last phase read, to `b16`.
  refine fblk hp G b9_in_code (by simp [b9]) exit_b9 nofun ok_b9.1 (ok_b9.2 .rbx (by simp))
    (ok_b9.2 .r15 (by simp)) hh.pc hh.bod fun st hbod hd0 hm0 hpc0 ↦ ?_
  have hpc : st.pc = if (SBool.cmp .eq .W64 (.reg .r12) (.reg .rbp)).eval
      (frameEnv m0 st0.data 80 []) = true then Labels.label NativeRustcVmX64.Vm.Decode.label_7
      else Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b9Offset + b9.length) := hpc0
  have he : (SBool.cmp .eq .W64 (.reg .r12) (.reg .rbp)).eval (frameEnv m0 st0.data 80 []) =
      true := by
    show CmpOp.apply .eq .W64 (reg st0.data .r12) (reg st0.data .rbp) = true
    rw [eqv_eval, hh.r12, hh.rbp]; simp
  simp only [he, ↓reduceIte] at hpc
  rw [hp.label NativeRustcVmX64.Vm.Decode.label_7_at] at hpc
  have hpos := hh.pos
  have hmod := hh.model
  have hple := hh.ple
  have hdl := hh.dlen
  have hdec : Dec m0 st.data.dmem n ws p done := by rw [hd0]; exact hh.dec
  have hrd : ReaderAt st.data.dmem (rdA m0) (BP m0) (Bs m0) ci := by rw [hd0]; exact hh.rd
  refine fblk hp G b16_in_code (by simp [b16]) exit_b16 nofun ok_b16.1 (ok_b16.2.2 .rbx (by simp))
    (ok_b16.2.2 .r15 (by simp)) hpc hbod fun s1 hb1 hd1 hm1 hpc1 ↦ ?_
  have hL := hrd.len_lt
  have hcl := hrd.c_le
  rw [length_Bs] at hcl hL
  have hcur : (frameEnv m0 st.data 80 []).load 0 24 8 = ci.toUInt64.toBitVec :=
    load_ofMachine (o := 24) rfl (by
      have := hrd.cur
      rw [off_off] at this
      exact this)
  have hal : boolRet s1.data = if ci = LN m0 then 1 else 0 := by
    unfold boolRet
    rw [show reg s1.data .rax = _ from hm1.regs .rax _ ok_b16.2.1]
    rw [merge_eq_al]
    have e1 : ((Sym.load 0 24 8).eval (frameEnv m0 st.data 80 [])).toNat = ci := by
      show ((frameEnv m0 st.data 80 []).load 0 24 8).toNat = ci
      rw [hcur, UInt64.toNat_toBitVec, toNat_toUInt64 (by omega)]
    have e2 : ((Sym.reg .r15).eval (frameEnv m0 st.data 80 [])).toNat = LN m0 := by
      show (reg st.data .r15).toNat = _
      rw [hbod.r15]
    simp only [e1, e2]
  refine fin hp G (hpc1.trans (hp.label NativeRustcVmX64.Vm.Decode.label_10_at)) hb1 ?_
  unfold Res
  rw [hmod, Nat.sub_self, tailPh_zero, length_Bs]
  by_cases hc : ci = LN m0
  · simp only [hc, ↓reduceIte]
    refine ⟨by simp [hal, hc], ?_⟩
    rw [hd1]
    have hlen := G.len
    exact decodedAt_of (a := ⟨DEC m0, LEN m0, LN m0⟩) (by have := G.Llt; omega) hlen hdec.nle
      hdec.wsl hdec.count hdec.words (by rw [hdl]; unfold wireMaxPhases; omega)
      (by rw [hdl]; exact hdec.pcnt) hdec.phases
  · simp only [hc, ↓reduceIte]
    simp [hal, hc]

omit [Host] in
theorem trunc_cond (x : BitVec 64) :
    (!CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (UnOp.apply .trunc .W32 x)
      (UnOp.apply .trunc .W32 x)) (BitVec.ofNat 64 0)) = !decide (x.toNat % 256 = 0) := by
  rw [testAl_eq, trunc32_mod]

/-- **A phase, up to `phase_m`'s call**: from the loop's head with `i < p`. -/
theorem pre_run (hp : Placed code k) (G : Geo m0) {n : Nat} {ws : List K}
    {p i : Nat} {done : List PhaseOut} {ci : Nat} {st : MachineState}
    (h : Head m0 k n ws p i done ci st) (hi : i < p) :
    Eventually (step1 Host.exe) (fun st' ↦ At11 m0 k n ws p i done ci st') st := by
  obtain ⟨hpc, hbod, hpos, hmod, hple, hile, hdl, hdec, hrd, h12, hbp, h13, h14⟩ := h
  have hst := G.st
  have hsp := G.sp
  have htop := G.top
  have hlen := G.len
  have hdn := G.dNw
  have hwn := G.wNw
  have hbn := G.bNw
  have hsD := G.sD
  have hsW := G.sW
  have hdW := G.dW
  have hsB := G.sB (by omega)
  have hbD := G.bD (by omega)
  have hbW := G.bW (by omega)
  have hS := stackBelow_toNat (m := m0) (n := 80) (by omega)
  have hr' : (rdA m0).toNat = SP0 m0 - 72 := by rw [G.fr (j := 8) (by omega)]; omega
  have hL := hrd.len_lt
  rw [length_Bs] at hL
  have hpb := phaseBase_lt (L := LN m0) (i := i) (by omega)
  have hpbi := phaseBase_eq (LN m0) i
  have hout : (wd m0 (phaseBase (LN m0) i)).toNat = (DEC m0).toNat + 8 * phaseBase (LN m0) i :=
    G.wd (by omega)
  -- `b9`: not the last phase.
  refine fblk hp G b9_in_code (by simp [b9]) exit_b9 nofun ok_b9.1 (ok_b9.2 .rbx (by simp))
    (ok_b9.2 .r15 (by simp)) hpc hbod fun s1 hb1 hd1 hm1 hpc1 ↦ ?_
  have rk1 : ∀ x ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg s1.data x = reg st.data x :=
    fun x hx ↦ hm1.regs x _ (ok_b9.2 x hx)
  have hpc1' : s1.pc = if (SBool.cmp .eq .W64 (.reg .r12) (.reg .rbp)).eval
      (frameEnv m0 st.data 80 []) = true then Labels.label NativeRustcVmX64.Vm.Decode.label_7
      else Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b9Offset + b9.length) := hpc1
  simp only [SBool.eval, Sym.eval, Env.ofMachine_regs, eqv_eval] at hpc1'
  rw [show st.data.regs.get64 .r12 = reg st.data .r12 from rfl,
    show st.data.regs.get64 .rbp = reg st.data .rbp from rfl, h12, hbp,
    decide_eq_false (by omega)] at hpc1'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1'
  -- `b10`: the count, within the room.
  refine fblk hp G b10_in_code (by simp [b10]) exit_b10 nofun ok_b10.1
    (ok_b10.2.2 .rbx (by simp)) (ok_b10.2.2 .r15 (by simp))
    (hpc1'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Decode.b9_next)) hb1 fun s2 hb2 hd2 hm2 hpc2 ↦ ?_
  have rk2 : ∀ x ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], reg s2.data x = reg s1.data x :=
    fun x hx ↦ hm2.regs x _ (ok_b10.2.2 x hx)
  have hbp2 : (reg s2.data .rbp).toNat = i + 1 := by
    rw [show reg s2.data .rbp = _ from hm2.regs .rbp _ ok_b10.2.1]
    simp only [Sym.eval, Env.ofMachine_regs, BinOp.apply, low_W64, ext_W64, BitVec.toNat_add,
      BitVec.toNat_ofNat]
    rw [show s1.data.regs.get64 .rbp = reg s1.data .rbp from rfl, rk1 .rbp (by simp), hbp]
    omega
  have hpc2' : s2.pc = if (SBool.cmp .eq .W64 (.reg .r14) (.bin .add .W64 (.reg .rbp) (.lit 1))).eval
      (frameEnv m0 s1.data 80 []) = true then Labels.label NativeRustcVmX64.Vm.Decode.label_9
      else Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b10Offset + b10.length) := hpc2
  have hne : (SBool.cmp .eq .W64 (.reg .r14) (.bin .add .W64 (.reg .rbp) (.lit 1))).eval
      (frameEnv m0 s1.data 80 []) = false := by
    show CmpOp.apply .eq .W64 (reg s1.data .r14)
      (BinOp.apply .add .W64 (reg s1.data .rbp) (BitVec.ofNat 64 1)) = false
    rw [eqv_eval, add1_toNat _ (by rw [rk1 .rbp (by simp), hbp]; omega), rk1 .r14 (by simp),
      rk1 .rbp (by simp), hbp]
    exact decide_eq_false (by omega)
  rw [hne] at hpc2'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc2'
  -- `b11`: `phase_m` into phase `i`'s words.
  obtain ⟨hmid11, hw11, hr13_11, hrsi11, hrdi11, hrdx11, hk11⟩ := ok_b11
  refine cblk hp G b11_in_code (by simp [b11]) exit_b11 hmid11 hw11 (hk11 .rbx (by simp))
    (hk11 .r15 (by simp)) (hpc2'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Decode.b10_next)) hb2
    fun s3 hb3 hs3 hm3 hpc3 ↦ ?_
  have hsp3 : rspOf s3.data = stackBelow m0 80 := by rw [hb3.fr.sp, off_zero]
  have hPS : phaseMStack = 1216 := rfl
  have hsb3 : stackBelow s3.data 1216 = stackBelow m0 1296 := by
    rw [stackBelow_callee hsp3 (by omega)]
  have hS96 : (stackBelow m0 1296).toNat = SP0 m0 - 1296 := stackBelow_toNat G.sp
  have hrsi3 : reg s3.data .rsi = wd m0 (phaseBase (LN m0) i) := by
    rw [show reg s3.data .rsi = _ from hm3.regs .rsi _ hrsi11]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [add_lit_eq', show s2.data.regs.get64 .r13 = reg s2.data .r13 from rfl, rk2 .r13 (by simp),
      rk1 .r13 (by simp), h13]
  have hrdi3 : reg s3.data .rdi = rdA m0 := (hm3.regs .rdi _ hrdi11).trans (eval_ptr0 8)
  have hrdx3 : reg s3.data .rdx = WK m0 := by
    rw [show reg s3.data .rdx = _ from hm3.regs .rdx _ hrdx11]; exact hb2.rbx
  have hR3 : ReaderAt s3.data.dmem (rdA m0) (BP m0) (Bs m0) ci := by
    refine reader_keep (by rw [hd2, hd1]; exact hrd) hs3 (fun q hq ↦ by rw [hr']; omega)
      (fun q hq ↦ by rw [length_Bs]; omega)
  have hd3 : NativeRustcVm.SameOutside st.data.dmem s3.data.dmem
      (fun q ↦ SP0 m0 - 80 ≤ q.toNat ∧ q.toNat < SP0 m0 - 72) := by
    have h3 := hs3
    rw [hd2, hd1] at h3
    exact h3
  have hse := streamEnd_eq (LN m0)
  have hw0 : (wd m0 0).toNat = (DEC m0).toNat := by rw [G.wd (by omega)]; rfl
  have hw1 : (wd m0 1).toNat = (DEC m0).toNat + 8 := G.wd (by omega)
  have hseL0 : streamEnd (LN m0) < LEN m0 := by rw [decodedWords_eq] at hlen; omega
  have hwS : (wd m0 (streamEnd (LN m0))).toNat = (DEC m0).toNat + 8 * streamEnd (LN m0) :=
    G.wd hseL0
  have hl1 : (ws.map K.lane).length = 2 * n := by rw [List.length_map, hdec.wsl]
  have hnle := hdec.nle
  unfold maxStream at hnle
  refine .done _ ⟨hpc3.1, by rw [hpc3.2, Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Decode.b11_next, hb3, hpos, hmod, hple, hi,
    hdl, ⟨hdec.nle, hdec.wsl, ?_, ?_, ?_, fun j hj ↦ ?_⟩, hR3, hrsi3, hrdi3, hrdx3, ?_, ?_, ?_, ?_⟩
  · exact wordAt_keep hdec.count hd3 (by rw [hw0]; omega) fun q hq ↦ by
      rw [hw0]; clear * - hq hsD hsp; omega
  · have h2n : 8 + 8 * (2 * n) ≤ 8 * LEN m0 := by rw [decodedWords_eq] at hlen; omega
    exact wordsAt_keep hdec.words hd3 (by rw [hl1, hw1]; omega) fun q hq ↦ by
      rw [hl1, hw1]; clear * - hq hsD hsp h2n; omega
  · exact wordAt_keep hdec.pcnt hd3 (by rw [hwS]; omega) fun q hq ↦ by
      rw [hwS]; clear * - hq hsD hsp hseL0; omega
  · have hA := agree_keep (a := DEC m0) (n := 8 * LEN m0) hd3 (by omega) fun q hq ↦ by
      clear * - hq hsD hsp; omega
    refine phaseAt_agree hA ?_ (hdec.phases j hj)
    have := phaseBase_lt (L := LN m0) (i := j) (by omega)
    rw [show phaseWords = 49411 from rfl]
    omega
  · rw [show reg s3.data .r12 = reg s2.data .r12 from hm3.regs .r12 _ (hk11 .r12 (by simp)),
      rk2 .r12 (by simp), rk1 .r12 (by simp)]; exact h12
  · rw [show reg s3.data .rbp = reg s2.data .rbp from hm3.regs .rbp _ (hk11 .rbp (by simp))]
    exact hbp2
  · rw [show reg s3.data .r13 = _ from hm3.regs .r13 _ hr13_11]
    exact (hm3.regs .rsi _ hrsi11).symm.trans hrsi3
  · rw [show reg s3.data .r14 = reg s2.data .r14 from hm3.regs .r14 _ (hk11 .r14 (by simp)),
      rk2 .r14 (by simp), rk1 .r14 (by simp)]; exact h14

/-- **`phase_m`**, from its call to its return. -/
theorem call_run (G : Geo m0)
    (hpm : Spec (Labels.label NativeRustcVmX64.Vm.PhaseM.entryLabel) PhaseMPre PhaseMPost) {n : Nat} {ws : List K}
    {p i : Nat} {done : List PhaseOut} {ci : Nat} {s3 : MachineState}
    (h : At11 m0 k n ws p i done ci s3) :
    Eventually (step1 Host.exe) (fun st' ↦ AtR m0 k n ws p i done ci st') s3 := by
  obtain ⟨hpc3a, hret3, hb3, hpos, hmod, hple, hi, hdl, hdec, hR3, hrsi3, hrdi3, hrdx3, h12, hbp2,
    h13, h14⟩ := h
  have hst := G.st
  have hsp := G.sp
  have htop := G.top
  have hlen := G.len
  have hdn := G.dNw
  have hwn := G.wNw
  have hbn := G.bNw
  have hsD := G.sD
  have hsW := G.sW
  have hdW := G.dW
  have hsB := G.sB (by omega)
  have hbD := G.bD (by omega)
  have hbW := G.bW (by omega)
  have hr' : (rdA m0).toNat = SP0 m0 - 72 := by rw [G.fr (j := 8) (by omega)]; omega
  have hL := hR3.len_lt
  rw [length_Bs] at hL
  have hpb := phaseBase_lt (L := LN m0) (i := i) (by omega)
  have hpbi := phaseBase_eq (LN m0) i
  have hout : (wd m0 (phaseBase (LN m0) i)).toNat = (DEC m0).toNat + 8 * phaseBase (LN m0) i :=
    G.wd (by omega)
  have hsp3 : rspOf s3.data = stackBelow m0 80 := by rw [hb3.fr.sp, off_zero]
  have hPS : phaseMStack = 1216 := rfl
  have hsb3 : stackBelow s3.data 1216 = stackBelow m0 1296 := by
    rw [stackBelow_callee hsp3 (by omega)]
  have hS96 : (stackBelow m0 1296).toNat = SP0 m0 - 1296 := stackBelow_toNat G.sp
  have hchg3 := hb3.chg
  have hrc := G.rc_keep hb3.chg
  have hpre : PhaseMPre s3.data := by
    refine ⟨stackOk_callee hst hb3.fr.kept hsp3 (by rw [hPS]),
      RcAt.callee G.rc hrc hsp3 (by omega) (by rw [hPS]), ?_, ?_, BP m0, Bs m0, ci,
      by rw [hrdi3]; exact hR3, ?_, ?_⟩
    · rw [hrsi3]
      have hdm : NativeRustcVm.Mapped m0.dmem (DEC m0) (8 * LEN m0) := G.dOk.1
      show NativeRustcVm.Mapped s3.data.dmem (wd m0 (phaseBase (LN m0) i)) phaseBytes ∧
        (wd m0 (phaseBase (LN m0) i)).toNat + phaseBytes ≤ 2 ^ 64
      rw [phaseBytes_eq]
      exact ⟨mapped_off (Mapped.keeps hdm hb3.fr.kept) (by omega), by omega⟩
    · rw [hrdx3]
      have hwm : NativeRustcVm.Mapped m0.dmem (WK m0) 483584 := G.wOk.1
      show NativeRustcVm.Mapped s3.data.dmem (WK m0) workBytes ∧ (WK m0).toNat + workBytes ≤ 2 ^ 64
      rw [workBytes_eq]
      exact ⟨Mapped.keeps hwm hb3.fr.kept, hwn⟩
    · rw [hrdi3, hrsi3, hrdx3]
      simp only [stackR, rcR, phaseBytes_eq, workBytes_eq, length_Bs, hsb3, hPS]
      exact pm_disjoint G.sp hS96 hr' (by rw [hout]; omega) (by rw [hout]; omega) G.cS
        (G.cB (by omega)) G.cD G.cW hsD hsW hsB hbD hbW hdW
    · refine G.got.transport (G.got_keep hb3.chg) ?_ ?_
      · intro l hl
        have hs := (G.got.1 l hl).2.2.1
        change Apart (gotAddr l) 8 (stackBelow m0 1296) 1304 at hs
        change Apart (gotAddr l) 8 (stackBelow s3.data phaseMStack) (phaseMStack + 8)
        rw [hPS, hsb3]
        unfold NativeRustcX64.Apart at hs ⊢
        omega
      · intro l hl a ha
        simp only [hrdi3, hrsi3, hrdx3, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl
        · exact (G.got.1 l hl).2.2.2 (rcAddr, 192) (by simp)
        · have hs := (G.got.1 l hl).2.2.1
          change Apart (gotAddr l) 8 (stackBelow m0 1296) 1304 at hs
          change Apart (gotAddr l) 8 (rdA m0) 24
          unfold NativeRustcX64.Apart at hs ⊢
          rw [hS96] at hs
          rw [hr']
          omega
        · have hd := (G.got.1 l hl).2.2.2 (DEC m0, 8 * LEN m0) (by simp)
          change Apart (gotAddr l) 8 (wd m0 (phaseBase (LN m0) i)) phaseBytes
          unfold NativeRustcX64.Apart at hd ⊢
          dsimp only at hd
          rw [hout, phaseBytes_eq]
          omega
        · exact (G.got.1 l hl).2.2.2 (WK m0, 483584) (by simp)
  refine call_then (env := frameEnv m0 s3.data 80 []) (l := NativeRustcVmX64.Vm.PhaseM.entryLabel) ⟨hpc3a, hret3⟩ hpm
    hpre fun s4 hpc4 hrsp4 ⟨hres4, hso4, hsv4⟩ ↦ ?_
  rw [hrdi3, hrsi3, hrdx3] at hso4
  simp only [frameR, hsb3, hPS] at hso4
  have hc16 : (off (rdA m0) 16).toNat = SP0 m0 - 80 + 24 := by rw [off_off]; exact G.fr (by omega)
  have hso4' : NativeRustcVm.SameOutside s3.data.dmem s4.data.dmem (fun q ↦
      ((DEC m0).toNat + 8 * phaseBase (LN m0) i ≤ q.toNat ∧
        q.toNat < (DEC m0).toNat + 8 * phaseBase (LN m0) i + 395288) ∨
      ((WK m0).toNat ≤ q.toNat ∧ q.toNat < (WK m0).toNat + 483584) ∨
      (SP0 m0 - 1296 ≤ q.toNat ∧ q.toNat < SP0 m0 - 48)) := hso4.mono fun q ⟨Rg, hRg, hq⟩ ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRg
    rcases hRg with rfl | rfl | rfl | rfl <;>
      simp only [NativeRustcVm.Region.Holds, curRegion, phaseBytes_eq, workBytes_eq] at hq
    · have := iv_of_inRange (a := wd m0 (phaseBase (LN m0) i)) (n := 395288)
        (by rw [hout]; omega) hq
      rw [hout] at this; exact .inl this
    · exact .inr (.inl (iv_of_inRange (by omega) hq))
    · have := iv_of_inRange (a := off (rdA m0) 16) (n := 8) (by rw [hc16]; omega) hq
      rw [hc16] at this; exact .inr (.inr (by omega))
    · have := iv_of_inRange (a := stackBelow m0 1296) (n := 1216) (by rw [hS96]; omega) hq
      rw [hS96] at this; exact .inr (.inr (by omega))
  have hb4 : Bod m0 8 s4.data := Bod.call G hb3 hsv4 hrsp4 hso4' fun q hq ↦ by
    unfold Chg
    rcases hq with hq | hq | hq <;> refine ⟨?_, ?_⟩ <;> omega
  have rk4 : ∀ x ∈ [Reg64.rbp, .r12, .r14], reg s4.data x = reg s3.data x := fun x hx ↦ by
    have hc : calleeSaved x = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> rfl
    exact hsv4.1 x hc
  have h13_4 : reg s4.data .r13 = wd m0 (phaseBase (LN m0) i) :=
    (hsv4.1 .r13 rfl).trans h13
  have hres := hres4 (BP m0) (Bs m0) ci (by rw [hrdi3]; exact hR3)
  rw [hrsi3, hrdi3] at hres
  -- What the phase changed, from the head.
  have hall : NativeRustcVm.SameOutside s3.data.dmem s4.data.dmem (fun q ↦
      ((DEC m0).toNat + 8 * phaseBase (LN m0) i ≤ q.toNat ∧
        q.toNat < (DEC m0).toNat + 8 * phaseBase (LN m0) i + 395288) ∨
      ((WK m0).toNat ≤ q.toNat ∧ q.toNat < (WK m0).toNat + 483584) ∨
      (SP0 m0 - 1296 ≤ q.toNat ∧ q.toNat < SP0 m0 - 48)) := by
    exact hso4'
  have hse := streamEnd_eq (LN m0)
  have hw0 : (wd m0 0).toNat = (DEC m0).toNat := by rw [G.wd (by omega)]; rfl
  have hw1 : (wd m0 1).toNat = (DEC m0).toNat + 8 := G.wd (by omega)
  have hseL0 : streamEnd (LN m0) < LEN m0 := by rw [decodedWords_eq] at hlen; omega
  have hwS : (wd m0 (streamEnd (LN m0))).toNat = (DEC m0).toNat + 8 * streamEnd (LN m0) :=
    G.wd hseL0
  have hnle := hdec.nle
  unfold maxStream at hnle
  have hseL : streamEnd (LN m0) < LEN m0 := by rw [decodedWords_eq] at hlen; omega
  have hR : ∀ (a : BitVec 64) (l : Nat), a.toNat + l ≤ (DEC m0).toNat + 8 * phaseBase (LN m0) i →
      (DEC m0).toNat ≤ a.toNat → ∀ q : BitVec 64, ((DEC m0).toNat + 8 * phaseBase (LN m0) i ≤ q.toNat ∧
        q.toNat < (DEC m0).toNat + 8 * phaseBase (LN m0) i + 395288) ∨
      ((WK m0).toNat ≤ q.toNat ∧ q.toNat < (WK m0).toNat + 483584) ∨
      (SP0 m0 - 1296 ≤ q.toNat ∧ q.toNat < SP0 m0 - 48) → q.toNat < a.toNat ∨ a.toNat + l ≤ q.toNat :=
    fun a l h1 h2 q hq ↦ by clear * - h1 h2 hq hdW hsD hpb hlen; omega
  have hl1 : (ws.map K.lane).length = 2 * n := by rw [List.length_map, hdec.wsl]
  have k0 : NativeRustcVm.WordAt s4.data.dmem (wd m0 0) n.toUInt64 :=
    wordAt_keep hdec.count hall (by rw [hw0]; rw [decodedWords_eq] at hlen; clear * - hdn hlen; omega)
      (hR _ 8 (by rw [hw0]; clear * - hpbi; omega) (by rw [hw0]))
  have k1 : NativeRustcVm.WordsAt s4.data.dmem (wd m0 1) (ws.map K.lane) :=
    wordsAt_keep hdec.words hall (by
      rw [hl1, hw1]; rw [decodedWords_eq] at hlen; clear * - hdn hlen hnle; omega)
      (hR _ _ (by rw [hl1, hw1]; clear * - hpbi hnle; omega) (by rw [hw1]; omega))
  have k2 : NativeRustcVm.WordAt s4.data.dmem (wd m0 (streamEnd (LN m0))) p.toUInt64 :=
    wordAt_keep hdec.pcnt hall (by rw [hwS]; clear * - hdn hseL0; omega)
      (hR _ 8 (by rw [hwS, streamEnd_eq]; clear * - hpbi; omega) (by rw [hwS]; omega))
  refine .done _ ⟨hpc4, hb4, hpos, hmod, hple, hi,
    hdl, ⟨hdec.nle, hdec.wsl, k0, k1, k2, fun j hj ↦ ?_⟩, hres, ?_, ?_, h13_4, ?_⟩
  · have hA := agree_keep (a := DEC m0) (n := 8 * phaseBase (LN m0) i) hall
      (by clear * - hdn hpb hlen; omega) (hR _ _ (by omega) (by omega))
    refine phaseAt_agree hA ?_ (hdec.phases j hj)
    rw [phaseBase_eq, phaseBase_eq, show phaseWords = 49411 from rfl]
    have : j * 49411 + 49411 ≤ i * 49411 := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    clear * - this
    omega
  · rw [rk4 .r12 (by simp)]; exact h12
  · rw [rk4 .rbp (by simp)]; exact hbp2
  · rw [rk4 .r14 (by simp)]; exact h14

/-- **A phase**: from the loop's head with `i < p`, `phase_m` into phase `i`'s words; back at the
head with one more phase, or out with `None`. -/
theorem step_run (hp : Placed code k) (G : Geo m0)
    (hpm : Spec (Labels.label NativeRustcVmX64.Vm.PhaseM.entryLabel) PhaseMPre PhaseMPost) {n : Nat} {ws : List K}
    {p i : Nat} {done : List PhaseOut} {ci : Nat} {st : MachineState}
    (h : Head m0 k n ws p i done ci st) (hi : i < p) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      ∃ po c', Head m0 k n ws p (i + 1) (done ++ [po]) c' st') st := by
  refine Eventually.bind (pre_run hp G h hi) fun s3 h3 ↦ ?_
  refine Eventually.bind (call_run G hpm h3) fun s4 h4 ↦ ?_
  obtain ⟨hpc4, hb4, hpos, hmod, hple, -, hdl, hdec, hres, h12, hbp2, h13_4, h14⟩ := h4
  -- `b12`: `phase_m`'s result.
  refine fblk hp G b12_in_code (by simp [b12]) exit_b12 nofun ok_b12.1
    (ok_b12.2.2 .rbx (by simp)) (ok_b12.2.2 .r15 (by simp)) hpc4 hb4 fun s5 hb5 hd5 hm5 hpc5 ↦ ?_
  have rk5 : ∀ x ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg s5.data x = reg s4.data x :=
    fun x hx ↦ hm5.regs x _ (ok_b12.2.2 x hx)
  have hpc5' : s5.pc = if (!CmpOp.apply .eq .W8 (BinOp.apply .and .W8
      (UnOp.apply .trunc .W32 (reg s4.data .rax)) (UnOp.apply .trunc .W32 (reg s4.data .rax)))
      (BitVec.ofNat 64 0)) = true then Labels.label NativeRustcVmX64.Vm.Decode.label_6
      else Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b12Offset + b12.length) := hpc5
  rw [trunc_cond] at hpc5'
  rcases hph : phaseM (Bs m0) ci with _ | ⟨po, c'⟩
  · -- `None`: `b13`, out.
    rw [hph] at hres
    have hb0 : (reg s4.data .rax).toNat % 256 = 0 := hres
    simp only [hb0, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc5'
    refine fblk hp G b13_in_code (by simp [b13]) exit_b13 nofun ok_b13.1
      (ok_b13.2.2 .rbx (by simp)) (ok_b13.2.2 .r15 (by simp))
      (hpc5'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Decode.b12_next)) hb5 fun s6 hb6 _ hm6 hpc6 ↦ ?_
    refine Eventually.mono (fin hp G (hpc6.trans (hp.label NativeRustcVmX64.Vm.Decode.label_10_at)) hb6 (res_none ?_ ?_))
      fun _ h ↦ .inl h
    · rw [hmod, show p - i = (p - i - 1) + 1 by omega, tailPh_none hph]
    · unfold boolRet
      rw [show reg s6.data .rax = _ from hm6.regs .rax _ ok_b13.2.1]
      show (reg s5.data .rax).toNat % 256 = 0
      rw [show reg s5.data .rax = _ from hm5.regs .rax _ ok_b12.2.1]
      rfl
  -- `Some`: back at the head.
  rw [hph] at hres
  obtain ⟨hb1', hPh, hR4⟩ := hres
  have hb1'' : (reg s4.data .rax).toNat % 256 = 1 := hb1'
  simp only [hb1'', Nat.one_ne_zero, decide_false, Bool.not_false, ↓reduceIte] at hpc5'
  rw [hp.label NativeRustcVmX64.Vm.Decode.label_6_at] at hpc5'
  refine .done _ (.inr ⟨po, c', ⟨hpc5', hb5, hpos, ?_, hple, by omega, by simp [hdl], ⟨hdec.nle,
    hdec.wsl, by rw [hd5]; exact hdec.count, by rw [hd5]; exact hdec.words,
    by rw [hd5]; exact hdec.pcnt, fun j hj ↦ ?_⟩, by rw [hd5]; exact hR4, ?_, ?_, ?_, ?_⟩⟩)
  · rw [hmod, show p - i = (p - (i + 1)) + 1 by omega, tailPh_succ hph]
  · simp only [List.length_append, List.length_singleton] at hj
    rw [hd5]
    by_cases hji : j < i
    · rw [List.getElem_append_left (by omega)]
      exact hdec.phases j (by omega)
    · have hj' : j = i := by omega
      subst hj'
      rw [List.getElem_append_right (by omega)]
      simp only [hdl, Nat.sub_self, List.getElem_cons_zero]
      exact hPh
  · rw [rk5 .r12 (by simp)]; exact h12
  · rw [rk5 .rbp (by simp)]; exact hbp2
  · rw [rk5 .r13 (by simp), h13_4, off_add]
    rw [show 8 * phaseBase (LN m0) i + 395288 = 8 * phaseBase (LN m0) (i + 1) by
      simp only [phaseBase_eq]; omega]
  · rw [rk5 .r14 (by simp)]; exact h14

/-- **The loop**: from the head with no phase read, every phase, then the cursor. -/
theorem loop_run (hp : Placed code k) (G : Geo m0)
    (hpm : Spec (Labels.label NativeRustcVmX64.Vm.PhaseM.entryLabel) PhaseMPre PhaseMPost) {n : Nat} {ws : List K}
    {p : Nat} {ci : Nat} {st : MachineState} (h : Head m0 k n ws p 0 [] ci st) :
    Eventually (step1 Host.exe) (Post m0) st := by
  refine Sym.loop (tr := step1 Host.exe)
    (fun r st ↦ ∃ i done ci, r = p - i ∧ Head m0 k n ws p i done ci st)
    (fun _ st ⟨i, done, ci, hr, hh⟩ ↦ ?_) ⟨0, [], ci, rfl, h⟩
  by_cases hi : i < p
  · refine Eventually.mono (step_run hp G hpm hh hi) fun s h' ↦ ?_
    rcases h' with h' | ⟨po, c', h'⟩
    · exact .inl h'
    · exact .inr ⟨p - (i + 1), by omega, i + 1, done ++ [po], c', rfl, h'⟩
  · have hip : i = p := by have := hh.ile; omega
    subst hip
    exact Eventually.mono (done_run hp G hh) fun _ h ↦ .inl h

end

end NativeRustcVmX64.Wire.Decode
