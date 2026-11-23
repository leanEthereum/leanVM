module

public import NativeRustcVmX64.KeccakGkr.FirstClaim.Pro
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `first_claim`: the bit weights' loop (x86-64)

A turn (`w_step`): `b3` loads lane `j / 64` of the lanes' kernel (`lane_eval`), computes
`1 << (j % 64)` (`shl_eval`) and calls `EW::mul`; `b4` stores the product as bit weight `j` and
loops while `j + 1 < 1600`. `w_loop`: all 1600 (`WDone`).
-/

namespace NativeRustcVmX64.KeccakGkr.FirstClaim

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.FirstClaim
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' Mapped.keeps
  bytesAt_congr inRange_off_self Touch)
open NativeVm.Math.Keccak (bitW)

@[expose] public section

/-- **The bit weights written**. -/
structure WDone (m0 : MachineData) (lanePoint : Array EW) (st : MachineData) : Prop where
  body : Body m0 st
  il : IL m0 st.dmem
  lanes : NativeRustcVm.EWsAt st.dmem (off (fbA m0) 328) (eqKernel lanePoint).toList
  w : ElemsAt st.dmem (wA m0) (bitW (eqKernel lanePoint)) 1600
  r15 : reg st .r15 = outA m0
  rbx : reg st .rbx = reg m0 .rcx
  r13 : reg st .r13 = reg m0 .r9

end

public section

theorem lane_nat : ∀ j, j < 1600 → (BinOp.apply .and .W32 (BinOp.apply .shr .W32
    (UnOp.apply .trunc .W32 (BitVec.ofNat 64 j)) (BitVec.ofNat 64 2)) (BitVec.ofNat 64 496)).toNat =
      16 * (j / 64) := by
  decide +kernel

theorem shl_nat : ∀ j, j < 1600 →
    UInt64.ofBitVec (BinOp.apply .shl .W64 (BitVec.ofNat 64 1) (BitVec.ofNat 64 j)) =
      (1 : UInt64) <<< (j % 64).toUInt64 := by
  decide +kernel

/-- **A lane's offset** in the lanes' kernel. -/
theorem lane_eval [Labels] (env : Env) {j : Nat} (hj : j < 1600)
    (h : env.regs .rcx = BitVec.ofNat 64 j) : (laneS.eval env).toNat = 16 * (j / 64) := by
  show (BinOp.apply .and .W32 (BinOp.apply .shr .W32 (UnOp.apply .trunc .W32 (env.regs .rcx))
    (BitVec.ofNat 64 2)) (BitVec.ofNat 64 496)).toNat = _
  rw [h]
  exact lane_nat j hj

variable {inst segment lanePoint output : Array EW} {m0 : MachineData}

/-- The frame's bytes from offset `o`, as numbers. -/
theorem fb_range (h : PreOk inst segment lanePoint output m0) {o n : Nat} (hon : o + n ≤ 1384) :
    (rspOf m0).toNat - 1632 ≤ (off (fbA m0) o).toNat ∧
      (off (fbA m0) o).toNat + n ≤ (rspOf m0).toNat + 8 := by
  have := (nums h).r1
  rw [fb_off h (by omega)]
  omega

/-- Frame bytes from offset `o ≥ 8` kept by a call (only `Low` and nothing else changed). -/
theorem keep_call (h : PreOk inst segment lanePoint output m0) {d₁ d₂ : DataMem} {o : Nat}
    {bs : List UInt8} (hs : NativeRustcVm.SameOutside d₁ d₂ (fun q ↦ False ∨ Low m0 q))
    (hle : o + bs.length ≤ 1384) (hb : NativeRustcVm.BytesAt d₁ (off (fbA m0) o) bs) :
    NativeRustcVm.BytesAt d₂ (off (fbA m0) o) bs :=
  keep_loc hs (fun i hi hq ↦ by
    rcases hq with hq | hq
    · exact hq
    · rw [low_iff h, fb_off h (by omega)] at hq
      omega) hb

variable [Host] {k : Nat}

/-- **A turn of the bit weights' loop.** -/
theorem w_step (hp : Placed code k) (hpre : FirstClaimPre inst segment lanePoint output m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {j : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b3Offset)) (hI : WInv m0 lanePoint j st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (j + 1 < 1600 ∧ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b3Offset) ∧
      WInv m0 lanePoint (j + 1) s'.data) ∨ (j + 1 = 1600 ∧ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b5Offset) ∧
      WDone m0 lanePoint s'.data)) st := by
  have h := preOk hpre
  have hn := nums h
  have hr1 := hn.r1
  have hr2 := hn.r2
  have hw := hn.w
  have hj := hI.j_lt
  have hlsz : (eqKernel lanePoint).size = 32 := by
    rw [NativeVm.Math.Keccak.eqKernel_size, h.lpSz]; rfl
  -- `b3`: the lane, `1 << (j % 64)`, `call EW::mul`.
  have hwf := wf_body h hI.body.frame.kept (d := st.data) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b3Offset + b3.length)).toBitVec)
  have hlane := lane_eval (frameEnv m0 st.data 1376 [(argA m0, 24)] (fun _ ↦ 0)
    (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b3Offset + b3.length)).toBitVec) hj hI.rcx
  have hm : Match (frameEnv m0 st.data 1376 [(argA m0, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b3Offset + b3.length)).toBitVec) lanesS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hI.body.frame.rsp_eval, trivial⟩ trivial
      ⟨by show (Sym.eval _ laneS).toNat < 497; rw [hlane]; omega, trivial⟩ ⟨arg_alias 0, arg_alias 1, arg_alias 2, trivial⟩
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf (fun _ _ ↦ rfl) hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hwi1, hrdi, hrsi, hrdx, hrcx, hr12, hat1⟩ := ok_b3
  have hf1 : Frame m0 1376 slots 0 st1.data := Frame.of_block hI.body.frame hwf hm1 hmid1 slots_le'
  have hs1 := sameOutside_touch hwf hm1 (r := 0) rfl (by decide) (within_spec hwi1)
  have hsp1 : rspOf st1.data = fbA m0 := by rw [hf1.sp, off_zero]
  have hso1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (Out m0) := fun q hq ↦
    (hs1 q fun ht ↦ hq (touch_out h (fun _ hj ↦ by omega) ht)).trans (hI.body.same q hq)
  -- the lane
  have ea := NativeRustcVm.ewAt_iff.mp (ewsAt_getD hI.lanes (i := j / 64) (by rw [hlsz]; omega))
  have e0 : NativeRustcVm.WordAt st.data.dmem (off (fbA m0) (328 + 16 * (j / 64)))
      ((eqKernel lanePoint).getD (j / 64) 0).c0 := by
    rw [← off_off]; exact ea.1
  have e1 : NativeRustcVm.WordAt st.data.dmem (off (fbA m0) (336 + 16 * (j / 64)))
      ((eqKernel lanePoint).getD (j / 64) 0).c1 := by
    rw [show 336 + 16 * (j / 64) = 328 + 16 * (j / 64) + 8 by omega,
      ← NativeRustcVm.Transcript.off_add, ← off_off]
    exact ea.2
  have v7 : reg st1.data .rdi = ((eqKernel lanePoint).getD (j / 64) 0).c0.toBitVec := by
    rw [show reg st1.data .rdi = _ from hm1.regs .rdi _ hrdi]
    show Env.load _ 0 (328 + (laneS.eval _).toNat) 8 = _
    rw [hlane]
    exact load_of_wordAt e0
  have v6 : reg st1.data .rsi = ((eqKernel lanePoint).getD (j / 64) 0).c1.toBitVec := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hrsi]
    show Env.load _ 0 (336 + (laneS.eval _).toNat) 8 = _
    rw [hlane]
    exact load_of_wordAt e1
  have v2 : UInt64.ofBitVec (reg st1.data .rdx) = (1 : UInt64) <<< (j % 64).toUInt64 := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hrdx]
    show UInt64.ofBitVec (BinOp.apply .shl .W64 (BitVec.ofNat 64 1) (st.data.regs.get64 .rcx)) = _
    rw [show st.data.regs.get64 .rcx = _ from hI.rcx]
    exact shl_nat j hj
  have v1 : reg st1.data .rcx = 0#64 := hm1.regs .rcx _ hrcx
  have hprod : EW.mul ⟨.ofBitVec (reg st1.data .rdi), .ofBitVec (reg st1.data .rsi)⟩
      ⟨.ofBitVec (reg st1.data .rdx), .ofBitVec (reg st1.data .rcx)⟩ =
      bitW (eqKernel lanePoint) j := by
    rw [v7, v6, v2, v1, UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec]
    rfl
  -- `EW::mul`
  have hpre1 : EWMulPre st1.data :=
    stackOk_callee h.st hf1.kept hsp1 (by rw [stack_eq]; decide)
  refine call_then hpc1 hmul hpre1 fun st2 hpc2 hrsp2 ⟨hrax, hrdx2, hch, hsv2⟩ ↦ ?_
  rw [hprod] at hrax hrdx2
  obtain ⟨hb2, hch2⟩ := call_body h hf1 hso1 hsv2 hrsp2 (s := ewMulStack) (by decide)
    (D := fun _ ↦ False) (NativeRustcVm.Transcript.SameOutside.mono hch fun _ hq ↦ Or.inr hq)
    (fun _ hq ↦ hq.elim)
  -- the registers kept
  have k1 : ∀ r, r ∈ [Reg64.rbx, .rbp, .r13, .r14, .r15] → reg st2.data r = reg st.data r :=
    fun r hr ↦ (hsv2.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl)).trans (atoms_eq hm1 hat1 hr)
  have k12 : reg st2.data .r12 = BitVec.ofNat 64 (j + 1) := by
    rw [show reg st2.data .r12 = reg st1.data .r12 from hsv2.1 .r12 rfl,
      show reg st1.data .r12 = _ from hm1.regs .r12 _ hr12]
    show st.data.regs.get64 .rcx + BitVec.ofNat 64 1 = _
    rw [show st.data.regs.get64 .rcx = _ from hI.rcx, add_ofNat']
  -- `b4`: the weight stored.
  have hwm : NativeRustcVm.Mapped m0.dmem (wA m0) 25600 :=
    (Areas.ok h.areas (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))).1
  have hwj : (off (wA m0) (16 * j)).toNat = (wA m0).toNat + 16 * j := toNat_off (by omega)
  have hfb := fbA_toNat h
  have hws := hn.ws
  have hwf4 : (frameEnv m0 st2.data 1376 [(off (wA m0) (16 * j), 16)] (fun _ ↦ 0) 0).WF := by
    refine frame_wf ⟨Mapped.keeps (frame_mapped h.st (by rw [stack_eq]; decide)) hb2.frame.kept,
      frame_noWrap h.st (by rw [stack_eq]; decide)⟩ (fun x hx ↦ ?_) (List.pairwise_pair.mpr ?_)
    · rw [List.mem_singleton] at hx
      subst hx
      exact ⟨Mapped.keeps (mapped_off hwm (by omega)) hb2.frame.kept,
        by show (off (wA m0) (16 * j)).toNat + 16 ≤ 2 ^ 64; omega⟩
    · show (fbA m0).toNat + (1376 + 8) ≤ (off (wA m0) (16 * j)).toNat ∨ _
      rw [hwj, hfb]
      omega
  have hm4 : Match (frameEnv m0 st2.data 1376 [(off (wA m0) (16 * j), 16)] (fun _ ↦ 0) 0)
      storeS st2.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb2.frame.rsp_eval, trivial⟩ trivial trivial
      ⟨by
        show reg st2.data .r14 + reg st2.data .rbp =
          wA m0 + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 8
        rw [k1 .r14 (by simp), k1 .rbp (by simp), hI.r14, hI.rbp, BitVec.add_assoc, add_ofNat',
          show 16 * j + 8 = 8 + 16 * j by omega], trivial⟩
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf4 nofun
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.FirstClaim.b3_next)) hm4 fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hws3, hw0, hw1, hrbp3, hrcx3, hat3⟩ := ok_b4
  have hf3 : Frame m0 1376 slots 8 st3.data := Frame.of_block hb2.frame hwf4 hm3 hmid3 slots_le'
  have hs3 : NativeRustcVm.SameOutside st2.data.dmem st3.data.dmem
      (NativeRustcVm.InRange (off (wA m0) (16 * j)) 16) :=
    sameOutside_region hwf4 hm3 (r := 1) rfl hws3
  have hin : ∀ q, NativeRustcVm.InRange (off (wA m0) (16 * j)) 16 q →
      NativeRustcVm.InRange (wA m0) 25600 q :=
    fun q hq ↦ off_in (by unfold NativeRustcVm.NoWrap; omega) (by omega) hq
  have hb3 : Body m0 st3.data :=
    ⟨hf3, fun q hq ↦ (hs3 q fun hr ↦ hq (Or.inr (Or.inl (hin q hr)))).trans (hb2.same q hq)⟩
  have hel := Match.ewAt_write hm3 (r := 1) (o := 0) (v0 := .reg .rax) (v1 := .reg .rdx) rfl
    (by decide) hw0 hw1
  rw [off_zero] at hel
  change NativeRustcVm.EWAt _ _ ⟨UInt64.ofBitVec (reg st2.data .rax),
    UInt64.ofBitVec (reg st2.data .rdx)⟩ at hel
  rw [hrax, hrdx2, UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec] at hel
  -- the frame's bytes kept
  have kf : ∀ {o : Nat} {bs : List UInt8}, 8 ≤ o → o + bs.length ≤ 1376 →
      NativeRustcVm.BytesAt st.data.dmem (off (fbA m0) o) bs →
      NativeRustcVm.BytesAt st3.data.dmem (off (fbA m0) o) bs := fun h8 hle hb ↦
    keep_off_w h (o := 16 * j) (n := 16) (by omega) hs3 (fb_range h (by omega))
      (keep_call h hch2 (by omega) (keep_touch h hs1 (by omega) (by omega) hb))
  have hil : IL m0 st3.data.dmem :=
    ⟨kf (by decide) (by rw [NativeRustcVm.length_wordBytes]; decide) hI.il.ip,
      kf (by decide) (by rw [NativeRustcVm.length_wordBytes]; decide) hI.il.il⟩
  have hlanes := kf (by decide) (by rw [lanes_len h]; decide) hI.lanes
  -- the weights before `j` kept, `j` written
  have hwk : ElemsAt st2.data.dmem (wA m0) (bitW (eqKernel lanePoint)) j := by
    have hR : ∀ {R : BitVec 64 → Prop}, (∀ q, R q → Stk m0 q) →
        ∀ q, NativeRustcVm.InRange (wA m0) (16 * j) q → ¬ R q := fun hR q hq hr ↦
      w_not_stk h (inRange_mono hq (by omega)) (hR q hr)
    exact (hI.w.keep hs1 (hR fun q hq ↦ touch_stk h (fun _ hj ↦ by omega) hq)
      (by unfold NativeRustcVm.NoWrap; omega)).keep hch2
      (hR fun q hq ↦ hq.elim (fun hf ↦ hf.elim) (low_stk h)) (by unfold NativeRustcVm.NoWrap; omega)
  have hw3 : ElemsAt st3.data.dmem (wA m0) (bitW (eqKernel lanePoint)) (j + 1) :=
    ElemsAt.grow hwk (by omega) (by rw [Nat.mul_one]; exact hs3) fun i hi ↦ by
      rw [show i = 0 by omega, Nat.add_zero]; exact hel
  -- the registers
  have e15 : reg st3.data .r15 = outA m0 :=
    (atoms_eq hm3 hat3 (by simp)).trans ((k1 .r15 (by simp)).trans hI.r15)
  have e13 : reg st3.data .r13 = reg m0 .r9 :=
    (atoms_eq hm3 hat3 (by simp)).trans ((k1 .r13 (by simp)).trans hI.r13)
  have ebx : reg st3.data .rbx = reg m0 .rcx :=
    (atoms_eq hm3 hat3 (by simp)).trans ((k1 .rbx (by simp)).trans hI.rbx)
  have hbp : (frameEnv m0 st2.data 1376 [(off (wA m0) (16 * j), 16)] (fun _ ↦ 0) 0).regs .rbp =
      BitVec.ofNat 64 (8 + 16 * j) := (k1 .rbp (by simp)).trans hI.rbp
  simp only [PcOk, SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64] at hpc3
  rw [hbp, add_ofNat', beq_ofNat (by omega) (by omega)] at hpc3
  by_cases hlast : j + 1 = 1600
  · rw [decide_eq_true (show 16 + (8 + 16 * j) = 25608 by omega)] at hpc3
    simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hpc3
    refine .done _ (Or.inr ⟨hlast, hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.FirstClaim.b4_next), hb3, hil, hlanes,
      by rw [← hlast]; exact hw3, e15, ebx, e13⟩)
  · rw [decide_eq_false (show ¬16 + (8 + 16 * j) = 25608 by omega)] at hpc3
    simp only [Bool.not_false, ite_true] at hpc3
    refine .done _ (Or.inl ⟨by omega, hpc3.trans (label_of_infix hp b3_in_code rfl), hb3, hil,
      hlanes, hw3, by omega, ?_, ?_, (atoms_eq hm3 hat3 (by simp)).trans
        ((k1 .r14 (by simp)).trans hI.r14), e15, ebx, e13⟩)
    · exact (hm3.regs .rcx _ hrcx3).trans k12
    · rw [show reg st3.data .rbp = _ from hm3.regs .rbp _ hrbp3]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
      rw [hbp, add_ofNat', show 16 + (8 + 16 * j) = 8 + 16 * (j + 1) by omega]

/-- **The bit weights' loop**: all 1600 written. -/
theorem w_loop (hp : Placed code k) (hpre : FirstClaimPre inst segment lanePoint output m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b3Offset)) (hI : WInv m0 lanePoint 0 st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b5Offset) ∧
      WDone m0 lanePoint s'.data) st :=
  loop (fun n st ↦ ∃ j, n = 1600 - j ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b3Offset) ∧
      WInv m0 lanePoint j st.data)
    (fun _ st ⟨j, hn, hpc, hI⟩ ↦ (w_step hp hpre hmul hpc hI).mono fun s' h' ↦ by
      have := hI.j_lt
      rcases h' with ⟨hlt, hpc', hI'⟩ | ⟨-, hpc', hD⟩
      · exact Or.inr ⟨1600 - (j + 1), by omega, j + 1, rfl, hpc', hI'⟩
      · exact Or.inl ⟨hpc', hD⟩)
    ⟨0, rfl, hpc, hI⟩

end

end NativeRustcVmX64.KeccakGkr.FirstClaim
