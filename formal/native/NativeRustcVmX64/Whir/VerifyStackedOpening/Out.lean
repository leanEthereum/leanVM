module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.Challenge

/-!
# `verify_stacked_opening`: outputs, steps, the return (x86-64)

`Outs`: the `TState` after the squeeze, the scales' count word and the scales; kept by a step
changing only the stack (`Outs.keep`; blocks `Parts.blk_stack`, calls `Parts.call_stack`). A block
writing the frame and one output area (`Ok.blockOut`, its writes checked by `outW`); a call writing
a window of the frame below the slots (`Ok.callWin`). The function's goal (`Goal`); the epilogue
(`exit_b51`) and the failure path (`fail_b50`, AL `0`).
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVmX64.Vm.VerifyStackedOpening

@[expose] public section

/-- The scales. -/
abbrev scalesOf (s : TState) (layout : LayoutW) (cs : Array ColumnClaimW) : Array EW :=
  powers (sq s).1 (cntOf layout cs)

/-- **The outputs** from the scales on: the `TState` after the squeeze, the scales' count and the
scales. -/
structure Outs [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (cs : Array ColumnClaimW)
    (m0 : MachineData) (d : Mem 64) : Prop where
  ts : TStateAt d (tA m0) a (sq s).2
  scw : NativeRustcVm.WordAt d (scA m0) (cntOf layout cs).toUInt64
  scs : NativeRustcVm.EWsAt d (off (scA m0) 8) (scalesOf s layout cs).toList

/-- Every write of `S` is into the frame below its offset `512` or into region `i` (`n` bytes). -/
def outW (i n : Nat) (S : SState) : Bool :=
  S.mem.all fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 512)) || (w.r == i && decide (w.off + w.n ≤ n))

/-- **The function's goal**: back at the return address, RSP above it, the postcondition. -/
def Goal [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (coefficients point : Array EW) (cs : Array ColumnClaimW) (z : Array EW) (value : EW)
    (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
    VerifyStackedOpeningPost a s layout target coefficients point cs z value m0 st.data

/-- The model's run. -/
abbrev runOf (s : TState) (layout : LayoutW) (target : EW) (coefficients point : Array EW)
    (cs : Array ColumnClaimW) (z : Array EW) (value : EW) (m0 : MachineData) :=
  (verifyStackedOpening layout.stackLog (reg m0 .rdx).toNat
    (stackClaims layout target point coefficients cs z value)).run s

end

public section

theorem size_scalesOf (s : TState) (layout : LayoutW) (cs : Array ColumnClaimW) :
    (scalesOf s layout cs).size = cntOf layout cs := by
  unfold scalesOf powers
  generalize (sq s).1 = b
  suffices ∀ n (acc : Array EW × EW), ((List.range n).foldl (fun (acc : Array EW × EW) _ ↦
      (acc.1.push acc.2, acc.2 * b)) acc).1.size = acc.1.size + n from by
    simpa using this _ (#[], 1)
  intro n
  induction n with
  | zero => intro acc; simp
  | succ n ih =>
    intro acc
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp [ih]
    omega

theorem ofBitVec_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) :
    UInt64.ofBitVec x = n.toUInt64 :=
  UInt64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (by
    show x.toNat = _
    rw [h, u64n (h ▸ x.isLt)]))

theorem outW_spec {i n : Nat} {S : SState} (h : outW i n S = true) :
    ∀ w ∈ S.mem, (w.r = 0 ∧ w.off + w.n ≤ 512) ∨ (w.r = i ∧ w.off + w.n ≤ n) := by
  intro w hw
  unfold outW at h
  rw [List.all_eq_true] at h
  have := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact this

section
variable [Labels] {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

variable (h : Parts a s layout target coefficients point slices cs z value m0)
include h

/-- A block's change of the frame, as one of the stack. -/
theorem Parts.blk_stack {d d' : Mem 64}
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (stackBelow m0 512) 512)) :
    NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (stackBelow m0 verifyStackedOpeningStack)
      verifyStackedOpeningStack) :=
  NativeRustcVm.SameOutside.mono hs fun _ hq ↦ h.frame_stack hq

/-- A callee's change of its stack, as one of the stack. -/
theorem Parts.call_stack {st : MachineData} (hok : Ok m0 st 0) {N' : Nat}
    (hN' : 512 + N' ≤ verifyStackedOpeningStack) {d d' : Mem 64}
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (stackBelow st N') N')) :
    NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (stackBelow m0 verifyStackedOpeningStack)
      verifyStackedOpeningStack) :=
  NativeRustcVm.SameOutside.mono hs fun _ hq ↦ (h.callee_stack (Ok.sp hok) hN' hq).1

theorem Parts.sc_nw : NativeRustcVm.NoWrap (scA m0) scalesBytes := h.so.1.2.1

theorem Parts.sc8_le : 8 + 16 * cntOf layout cs ≤ scalesBytes := by
  have hP := (placedOf_le_self (layout := layout) (cs := cs) cs.size).trans h.n_le
  unfold cntOf; show _ ≤ 2600; omega

/-- **The outputs** across a step changing only the stack. -/
theorem Outs.keep {d d' : Mem 64} (ho : Outs a s layout cs m0 d) (hk : Keeps d d')
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange
      (stackBelow m0 verifyStackedOpeningStack) verifyStackedOpeningStack)) :
    Outs a s layout cs m0 d' := by
  have hsnw := noWrap_stackBelow h.wt.1
  have hscn := h.sc_nw
  have hsc8 := h.sc8_le (layout := layout)
  refine ⟨ho.ts.frame hk (fun q hq ↦ ⟨fun ht ↦ h.outs_not_stack (.inr (.inr ht)) hq,
      fun hd ↦ not_inRange_of_apart h.wt.2.2.2.1.2.1 ho.ts.footprint.2.1.2 hsnw hd
        (inRange_mono hq (by omega))⟩) hs, ?_, ?_⟩
  · refine NativeRustcVm.BytesAt.of_sameOutside ho.scw hs fun i hi hq ↦
      h.outs_not_stack (.inr (.inl ?_)) hq
    rw [NativeRustcVm.length_wordBytes] at hi
    exact NativeRustcVm.inRange_add (by show i < 2600; omega) (by unfold NativeRustcVm.NoWrap at hscn; omega)
  · refine NativeRustcVm.BytesAt.of_sameOutside ho.scs hs fun i hi hq ↦
      h.outs_not_stack (.inr (.inl ?_)) hq
    rw [NativeRustcVm.length_flatMap_const NativeRustcVm.length_ewBytes, Array.length_toList,
      size_scalesOf] at hi
    rw [off_add]
    exact inRange_off_self (by omega) (by unfold NativeRustcVm.NoWrap at hscn; omega)

/-- **A block** writing the frame below its return address and an output area (region `i`): `Ok`
after it, the bytes changed among the frame's and the area's. -/
theorem Ok.blockOut {st st' : MachineData} {o o' : Nat} (hok : Ok m0 st o)
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (frameEnv m0 st 512 rest vars ret).WF)
    (hm : Match (frameEnv m0 st 512 rest vars ret) S st') (hS : MidOk 512 o' slots S = true)
    {i n : Nat} {x : BitVec 64} (hi : (frameEnv m0 st 512 rest vars ret).regions[i]? = some (x, n))
    (hx : ∀ q, NativeRustcVm.InRange x n q → outs m0 q) (hW : outW i n S = true) :
    Ok m0 st' o' ∧ NativeRustcVm.SameOutside st.dmem st'.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow m0 512) 512 q ∨ NativeRustcVm.InRange x n q) := by
  have hfr := Frame.of_block hok.fr hwf hm hS slots_le
  have hnw0 := hwf.noWrap 0 (stackBelow m0 512) 520 rfl
  have hnwx := hwf.noWrap i x n hi
  have hsame : NativeRustcVm.SameOutside st.dmem st'.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow m0 512) 512 q ∨ NativeRustcVm.InRange x n q) := by
    intro q hq
    refine hm.get?_mem0 hwf fun hW' ↦ hq ?_
    obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hW'
    rcases outW_spec hW w hw with ⟨hr, hle⟩ | ⟨hr, hle⟩
    · rw [hr] at hb
      cases hb
      exact .inl ((inR (by unfold NativeRustcVm.NoWrap; omega)).mpr ⟨by omega, by omega⟩)
    · rw [hr, hi] at hb
      cases hb
      exact .inr ((inR hnwx).mpr ⟨by omega, by omega⟩)
  refine ⟨⟨hfr, fun q hq ↦ ?_⟩, hsame⟩
  rw [hsame q ?_]
  · exact hok.so q hq
  · rintro (h1 | h1)
    · exact hq (.inr (h.frame_stack h1))
    · exact hq (.inl (hx q h1))

/-- **A call** writing a window of the frame below its slots and its stack: `Ok` after it, the
bytes changed among the stack's. -/
theorem Ok.callWin {st st' : MachineData} (hok : Ok m0 st 0) (hs : Saved st st')
    (hrsp : rspOf st' = rspOf st + 8#64) {N' : Nat} (hN' : 512 + N' ≤ verifyStackedOpeningStack)
    {lo n : Nat} (hlo : lo + n ≤ 464)
    (hso : NativeRustcVm.SameOutside st.dmem st'.dmem
      (fun q ↦ NativeRustcVm.InRange (off (stackBelow m0 512) lo) n q ∨
        NativeRustcVm.InRange (stackBelow st N') N' q)) :
    Ok m0 st' 8 ∧ NativeRustcVm.SameOutside st.dmem st'.dmem
      (NativeRustcVm.InRange (stackBelow m0 verifyStackedOpeningStack)
        verifyStackedOpeningStack) := by
  have hsp := Ok.sp hok
  have hfn : (stackBelow m0 512).toNat = (rspOf m0).toNat - 512 := h.fbn
  have hR := h.rsp
  have hwin : ∀ q, NativeRustcVm.InRange (off (stackBelow m0 512) lo) n q →
      NativeRustcVm.InRange (stackBelow m0 512) 512 q := fun q hq ↦
    inRange_of_off (by unfold NativeRustcVm.NoWrap; omega) (by omega) hq
  have hR' : ∀ q, (NativeRustcVm.InRange (off (stackBelow m0 512) lo) n q ∨
      NativeRustcVm.InRange (stackBelow st N') N' q) →
      NativeRustcVm.InRange (stackBelow m0 verifyStackedOpeningStack) verifyStackedOpeningStack q
    := by
    rintro q (hq | hq)
    · exact h.frame_stack (hwin q hq)
    · exact (h.callee_stack hsp hN' hq).1
  have hnot : ∀ j, 464 ≤ j → j < 520 → ¬ (NativeRustcVm.InRange (off (stackBelow m0 512) lo) n
      (off (stackBelow m0 512) j) ∨ NativeRustcVm.InRange (stackBelow st N') N'
        (off (stackBelow m0 512) j)) := by
    rintro j hj1 hj2 (hq | hq)
    · have ho : (off (stackBelow m0 512) lo).toNat = (stackBelow m0 512).toNat + lo :=
        toNat_off (by omega)
      rw [inR (by unfold NativeRustcVm.NoWrap; rw [ho]; omega), ho,
        toNat_off (by omega)] at hq
      omega
    · exact (h.callee_stack hsp hN' hq).2 (inRange_off_self (by omega) (by omega))
  refine ⟨⟨Frame.call_slots hok.fr hs hrsp hso (fun p hp i hi ↦ hnot _
      (by have := slots_ge p hp; omega) (by have := slots_le p hp; omega))
      (fun j hj ↦ hnot _ (by omega) (by omega)), fun q hq ↦ ?_⟩,
    NativeRustcVm.SameOutside.mono hso hR'⟩
  rw [hso q fun h' ↦ hq (.inr (hR' q h'))]
  exact hok.so q hq

end

/-! ## The return -/

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

section
variable (h : Parts a s layout target coefficients point slices cs z value m0)
  (hp : Placed code k)
include h hp

/-- **The epilogue** `b51`: the postcondition, given AL and the `TState`. -/
theorem exit_b51 {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b51Offset))
    (hok : Ok m0 st.data 8)
    (hal : OkAl st.data (runOf s layout target coefficients point cs z value m0).isSome)
    (hnext : NextAt st.data.dmem (tA m0) a (runOf s layout target coefficients point cs z value m0)) :
    Eventually (step1 Host.exe) (Goal a s layout target coefficients point cs z value m0) st := by
  have hwf : (frameEnv m0 st.data 512 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b51Offset + b51.length)).toBitVec).WF := hok.wf0 h
  refine exec_at (infix_of b51_in_code (List.cons_ne_nil _ _) hp) run_b51 hwf nofun hpc hok.m_reg
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hok.fr hwf hm' (by decide +kernel)
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf rfl
  have hax : reg st'.data .rax = reg st.data .rax := regKeep hm' .rax rfl
  simp only [PcOk] at hpc'
  refine .done _ ⟨hpc'.trans (Frame.load_ret hok.fr h.wt.1 (by rw [stack_eq]; omega)), hrsp, ?_,
    by rw [hd]; exact hnext, ?_, hsv⟩
  · unfold OkAl boolRet at hal ⊢
    rw [hax]
    exact hal
  · intro q hq
    rw [hd]
    refine hok.so q fun hw ↦ hq ?_
    rcases hw with (h1 | h1 | h1) | h1
    · exact .inl ⟨_, List.mem_cons_self, h1⟩
    · exact .inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h1⟩
    · exact .inl ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), h1⟩
    · exact .inr h1

/-- **The failure path** `b50`: AL `0`, the model's `none`. -/
theorem fail_b50 {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b50Offset))
    (hok : Ok m0 st.data 8) (hr : runOf s layout target coefficients point cs z value m0 = none) :
    Eventually (step1 Host.exe) (Goal a s layout target coefficients point cs z value m0) st := by
  refine h.run hp b50_in_code (List.cons_ne_nil _ _) hpc hok (vars := fun _ ↦ 0) (hok.wf0 h)
    hok.m_reg run_b50 (o := 8) (by decide +kernel) (by decide) fun st1 hok1 _ hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  refine exit_b51 h hp (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b50_next)) hok1 ?_ ?_
  · rw [hr]
    unfold OkAl boolRet
    rw [show reg st1.data .rax = _ from hm1.regs .rax _ rfl]
    rfl
  · rw [hr]
    intro _ _ h'
    cases h'

end

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
