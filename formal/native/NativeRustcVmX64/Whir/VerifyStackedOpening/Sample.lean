module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.Entry
public import NativeRustcVmX64.Whir.VerifyStackedOpening.Squeeze

/-!
# `verify_stacked_opening`: the count, the batching challenge (x86-64)

`tail_b15`: after the pairs, an even count goes to `NativeRustcVmX64.Vm.VerifyStackedOpening.label_16` (`b20`); an odd one
counts its last claim (`tail_b16`: `b16` reads its column, `b17` its `present` bit or `b18` none,
`b19` adds it): `AtB20`, every placed claim counted. `sample_b20`: `b20`, `b22` check the count
(`placed + 2`, at most `162`: never too many), `b21` saves the `TState` and the Keccak output and
squeezes the challenge, `b23` saves the claims and the rate: `NativeRustcVmX64.Vm.VerifyStackedOpening.label_19` (`b24`,
`AtB24`). With no claim, `b3` does the same, `b4` sets the count `2` (`sample_b3`). `to_b24`:
from the entry.
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVmX64.Vm.VerifyStackedOpening

@[expose] public section

/-- The count of the stack claims. -/
abbrev cntOf (layout : LayoutW) (cs : Array ColumnClaimW) : Nat := placedOf layout cs cs.size + 2

/-- The frame's words from the squeeze to the ladder: the `TState`, the claims, the rate, the
Keccak output, the ring switch's output. -/
def fwL (m0 : MachineData) : List (Nat × UInt64) :=
  [(24, UInt64.ofBitVec (tA m0)), (40, UInt64.ofBitVec (clA m0)),
    (48, UInt64.ofBitVec (reg m0 .rdx)), (56, UInt64.ofBitVec (reg m0 .r8)),
    (64, UInt64.ofBitVec (reg m0 .rcx))]

/-- **Every placed claim counted**, at `NativeRustcVmX64.Vm.VerifyStackedOpening.label_16`. -/
structure AtB20 [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (cs : Array ColumnClaimW)
    (m0 st : MachineData) : Prop where
  cb : CB a s cs m0 st
  rbx : (reg st .rbx).toNat = placedOf layout cs cs.size

/-- **After the squeeze**, at `NativeRustcVmX64.Vm.VerifyStackedOpening.label_19`: the `TState` after it, the challenge
in RAX, RDX, the count in RBX. -/
structure AtB24 [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (cs : Array ColumnClaimW)
    (m0 st : MachineData) : Prop where
  ok : Ok m0 st 8
  ts : TStateAt st.dmem (tA m0) a (sq s).2
  fw : FW st.dmem m0 (fwL m0)
  rax : reg st .rax = (sq s).1.c0.toBitVec
  rdx : reg st .rdx = (sq s).1.c1.toBitVec
  rbx : (reg st .rbx).toNat = cntOf layout cs
  rbp : reg st .rbp = layA m0
  r13 : reg st .r13 = off (clA m0) 8
  r15 : (reg st .r15).toNat = cs.size

/-- The last claim's environment: the claims from `R13`. -/
abbrev tailEnv (m0 st : MachineData) (ret : BitVec 64) : Env :=
  frameEnv m0 st 512 [(off (clA m0) 8, 97280)] (fun _ ↦ 0) ret

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

omit [Host] in
/-- Part of an area not wrapping does not wrap (stated over variables: no literal unfolding). -/
theorem noWrap_off' {b : BitVec 64} {N o k : Nat} (h : NativeRustcVm.NoWrap b N) (hk : 0 < k)
    (hle : o + k ≤ N) : NativeRustcVm.NoWrap (off b o) k := by
  unfold NativeRustcVm.NoWrap at h ⊢
  rw [toNat_off (by omega)]
  omega

/-- The last claim's environment is well formed (the claims from their first). -/
theorem Ok.tail_wf (h : Parts a s layout target coefficients point slices cs z value m0)
    {st : MachineData} {o : Nat} (hok : Ok m0 st o) {ret : BitVec 64} :
    (tailEnv m0 st ret).WF := by
  have hc := (h.ins _ mem_cl).1
  have hcb : NativeRustcVm.Layout.claimsBytes = 97288 := rfl
  simp only [hcb] at hc
  have hcn : (clA m0).toNat + 97288 ≤ 2 ^ 64 := hc.1.2
  have ho : (off (clA m0) 8).toNat = (clA m0).toNat + 8 := toNat_off (by omega)
  refine hok.wf1 h (mapped_off hc.1.1 (by omega)) (noWrap_off' hc.1.2 (by omega) (by omega)) ?_
  have : NativeRustcVm.Apart (clA m0) 97288 (stackBelow m0 verifyStackedOpeningStack)
      (verifyStackedOpeningStack + 8) := hc.2
  unfold NativeRustcVm.Apart at this ⊢
  rw [ho]
  omega

section
variable (h : Parts a s layout target coefficients point slices cs z value m0)
  (hp : Placed code k)
include h hp

/-- **The last claim** of an odd count: `b16`, then `b17` or `b18`, then `b19`. -/
theorem tail_b16 {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b16Offset))
    (hA : AtB15 a s layout cs m0 st.data) (hodd : cs.size % 2 = 1) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b20Offset) → AtB20 a s layout cs m0 st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hn := h.n_le
  have hc := hA.cb
  have hok := hc.ok
  have hi : cs.size - 1 < cs.size := by omega
  have hie : cs.size - 1 = 2 * (cs.size / 2) := by omega
  have hwf : ∀ ret, (tailEnv m0 st.data ret).WF := fun _ ↦ hok.tail_wf h
  have hm : ∀ ret, Match (tailEnv m0 st.data ret) tailS st.data := fun _ ↦
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hok.fr.rsp_eval, trivial⟩ trivial
      ⟨by show (reg st.data .rcx).toNat < 160; rw [hA.rcx]; omega, trivial⟩
      ⟨by show reg st.data .r13 = _
          rw [hc.r13, Env.base_ofMachine _ _ _ _ (r := 1) rfl,
            show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
  refine h.run hp b16_in_code (List.cons_ne_nil _ _) hpc hok (hwf _) (hm _) run_b16 (o := 8)
    (by decide +kernel) (by decide) fun st1 hok1 _ hm1 hpc1 ↦ ?_
  have hd1 := hm1.dmem_eq (hwf _) rfl
  have hk1 : ∀ r ∈ cbRegs ++ [.rax, .rbx], reg st1.data r = reg st.data r :=
    fun r hr ↦ kept_reg hm1 (show keeps (cbRegs ++ [.rax, .rbx]) (after b16 tailS) = true by
      rw [after_eq run_b16]; decide) hr
  have hc1 := hc.keep hok1 hd1 fun r hr ↦ hk1 r (List.mem_append_left _ hr)
  -- The last claim's column.
  have hcol : ((Sym.loadx 1 0 (.bin .mul .W64 (.reg .rcx) (.lit 608)) 8).eval
      (tailEnv m0 st.data (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b16Offset + b16.length)).toBitVec)).toNat =
        cs[cs.size - 1].column := by
    have hrc : (reg st.data .rcx).toNat = cs.size - 1 := by rw [hA.rcx]; omega
    have hmul : ((Sym.bin .mul .W64 (.reg .rcx) (.lit 608)).eval
        (tailEnv m0 st.data (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b16Offset + b16.length)).toBitVec)).toNat =
          608 * (cs.size - 1) := by
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_mul, BitVec.toNat_ofNat]
      show (reg st.data .rcx).toNat * (608 % 2 ^ 64) % 2 ^ 64 = _
      rw [hrc]
      omega
    show ((tailEnv m0 st.data _).load 1 (0 + _) 8).toNat = _
    rw [hmul, Nat.zero_add, load_ofMachine (r := 1) (w := cs[cs.size - 1].column.toUInt64) rfl (by
      rw [off_off]; exact hok.col h hi)]
    exact u64n ((hok.cl h).claims _ hi).column_lt
  have hlast : (cs.size - 1) + 1 = cs.size := by omega
  have hb19 : ∀ (st2 : MachineState), st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b19Offset) → CB a s cs m0 st2.data →
      (reg st2.data .rbx).toNat = placedOf layout cs (cs.size - 1) →
      (reg st2.data .rcx).toNat = bitAt layout cs (cs.size - 1) →
      Eventually (step1 Host.exe) R st2 := by
    intro st2 hpc2 hc2 hbx hcx
    refine h.cbRun hp b19_in_code (List.cons_ne_nil _ _) hpc2 hc2 run_b19 (by decide +kernel) rfl
      (by decide +kernel) fun st3 hc3 _ hm3 hpc3 ↦ ?_
    simp only [PcOk] at hpc3
    refine cont st3 (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b19_next)) ⟨hc3, ?_⟩
    rw [show reg st3.data .rbx = _ from hm3.regs .rbx _ rfl, eval_add64]
    show (reg st2.data .rcx + reg st2.data .rbx).toNat = _
    have hb := placedOf_le_self (layout := layout) (cs := cs) (cs.size - 1)
    have hbit : bitAt layout cs (cs.size - 1) ≤ 1 := by rw [bitAt_eq hi]; split <;> omega
    rw [toNat_add_small (by omega), hcx, hbx, ← hlast, placedOf_succ', hlast]
    omega
  simp only [PcOk] at hpc1
  rw [eval_gt157, hcol] at hpc1
  have hbx1 : (reg st1.data .rbx).toNat = placedOf layout cs (cs.size - 1) := by
    rw [hk1 .rbx (by simp), hA.rbx, ← hie]
  by_cases hgt : 157 < cs[cs.size - 1].column
  · simp only [hgt, decide_true, ↓reduceIte] at hpc1
    rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_14_at] at hpc1
    refine h.cbRun hp b18_in_code (List.cons_ne_nil _ _) hpc1 hc1 run_b18 (by decide +kernel) rfl
      (by decide +kernel) fun st2 hc2 _ hm2 hpc2 ↦ ?_
    simp only [PcOk] at hpc2
    refine hb19 st2 (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b18_next)) hc2 ?_ ?_
    · rw [show reg st2.data .rbx = _ from hm2.regs .rbx _ rfl]; exact hbx1
    · rw [show reg st2.data .rcx = 0#64 from hm2.regs .rcx _ rfl, hok.bit_eq h hi]
      split
      · omega
      · rfl
  · simp only [hgt, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    have hj2 : 2 * (cs.size / 2) + 2 ≤ 160 := by omega
    have hrcx1 : (reg st1.data .rcx).toNat = cs[cs.size - 1].column := by
      rw [show reg st1.data .rcx = _ from hm1.regs .rcx _ rfl]; exact hcol
    have hm' : Match (cntEnv m0 st1.data (cs.size / 2)
        (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b17Offset + b17.length)).toBitVec) tail2S st1.data :=
      match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hok1.fr.rsp_eval, trivial⟩ trivial
        ⟨by show ((t3 (.reg .rcx)).eval _).toNat < 472
            rw [toNat_t3 _ (by show (reg st1.data .rcx).toNat < _; omega)]
            show 3 * (reg st1.data .rcx).toNat < 472
            omega, trivial⟩
        ⟨by show reg st1.data .rax = _; rw [hk1 .rax (by simp), hA.rax]; rfl, trivial⟩
    refine h.run hp b17_in_code (List.cons_ne_nil _ _)
      (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b16_next)) hok1 (hok1.cnt_wf' h hj2) hm' run_b17
      (o := 8) (by decide +kernel) (by decide) fun st2 hok2 _ hm2 hpc2 ↦ ?_
    have hd2 := hm2.dmem_eq (hok1.cnt_wf' h hj2) rfl
    have hk2 : ∀ r ∈ cbRegs ++ [.rbx], reg st2.data r = reg st1.data r :=
      fun r hr ↦ kept_reg hm2 (show keeps (cbRegs ++ [.rbx]) (after b17 tail2S) = true by
        rw [after_eq run_b17]; decide) hr
    simp only [PcOk] at hpc2
    rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_15_at] at hpc2
    refine hb19 st2 hpc2 (hc1.keep hok2 hd2 fun r hr ↦ hk2 r (List.mem_append_left _ hr)) ?_ ?_
    · rw [hk2 .rbx (by simp)]; exact hbx1
    · rw [show reg st2.data .rcx = _ from hm2.regs .rcx _ rfl]
      exact hok1.bit_val h hi (by omega) (.reg .rcx) hrcx1

/-- **After the pairs**: an even count to `b20`, an odd one through its last claim. -/
theorem tail_b15 {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b15Offset))
    (hA : AtB15 a s layout cs m0 st.data) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b20Offset) → AtB20 a s layout cs m0 st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  refine h.cbRun hp b15_in_code (List.cons_ne_nil _ _) hpc hA.cb run_b15 (by decide +kernel) rfl
    (by decide +kernel) fun st1 hc1 _ hm1 hpc1 ↦ ?_
  have hk1 : ∀ r ∈ [Reg64.rax, .rcx, .rbx], reg st1.data r = reg st.data r :=
    fun r hr ↦ kept_reg hm1 (show keeps [.rax, .rcx, .rbx] (after b15 regS) = true by
      rw [after_eq run_b15]; decide) hr
  have hA1 : AtB15 a s layout cs m0 st1.data :=
    ⟨hc1, (hk1 .rax (by simp)).trans hA.rax, (hk1 .rcx (by simp)) ▸ hA.rcx,
      (hk1 .rbx (by simp)) ▸ hA.rbx⟩
  simp only [PcOk] at hpc1
  rw [eval_even] at hpc1
  have h15 : ((Sym.reg .r15).eval (frameEnv m0 st.data 512 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b15Offset + b15.length)).toBitVec)).toNat = cs.size := hA.cb.r15
  rw [h15] at hpc1
  by_cases he : cs.size % 2 = 0
  · simp only [he, decide_true, ↓reduceIte] at hpc1
    rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_16_at] at hpc1
    refine cont st1 hpc1 ⟨hc1, ?_⟩
    rw [hA1.rbx]; congr 1; omega
  · simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    exact tail_b16 h hp (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b15_next)) hA1 (by omega) cont

end

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
