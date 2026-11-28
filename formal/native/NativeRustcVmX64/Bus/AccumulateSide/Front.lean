module

public import NativeRustcVmX64.Bus.AccumulateSide.Ones
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqEvalFnOfEqAbove.Names

/-!
# `accumulate_side`: the known part and the framework ones (x86-64)

`knownLoop`: the known part's loop (`b2` to `b4`) to its end; `b5` adds the known part to the
tree's value in the frame. `front`: from the entry to `b12`, the frame holding the tree's value
plus the known part (offsets `64`, `72`), R14, R15 the ones over the framework.
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

public section

variable [Host] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData} {k : Nat}

/-- **The known part's loop** from turn `i`. -/
theorem knownLoop (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {i : Nat} (hi : i < cA SL m0) {st : MachineData}
    (hst : St m0 Z (Vt SL m0 (lpK SL m0 i)) DK 8 st) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b5Offset) ∧
      St m0 Z (Vt SL m0 (lpK SL m0 (cA SL m0))) DK 8 st'.data)
      ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b2Offset)⟩ := by
  refine Sym.loop (fun n (s : MachineState) ↦ ∃ i, n = cA SL m0 - i ∧ i < cA SL m0 ∧
      s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b2Offset) ∧ St m0 Z (Vt SL m0 (lpK SL m0 i)) DK 8 s.data)
    (fun n s ⟨i, hn, hi, hpc, hst⟩ ↦ ?_) ⟨i, rfl, hi, rfl, hst⟩
  obtain ⟨d, pc⟩ := s
  simp only at hpc hst
  subst hpc
  refine Eventually.bind (turnKA hp h hee hi hst) fun s ⟨hpc, hst', hret⟩ ↦ ?_
  obtain ⟨d', pc'⟩ := s
  simp only at hpc hst' hret
  subst hpc
  refine (turnKB hp h hmul hi hst' hret).mono fun s' ⟨hst'', hx⟩ ↦ ?_
  rcases hx with ⟨hpc'', hlt⟩ | ⟨hpc'', heq⟩
  · exact .inr ⟨cA SL m0 - (i + 1), by omega, i + 1, rfl, hlt, hpc'', hst''⟩
  · exact .inl ⟨hpc'', heq ▸ hst''⟩

/-- `b5`: the known part added to the tree's value. -/
theorem addKnown (hp : Placed code k) (h : Pre L rows bl Fm SL m0) {st : MachineData}
    (hst : St m0 Z (Vt SL m0 (lpK SL m0 (cA SL m0))) DK 8 st) (lp : Nat → UInt64) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b6Offset) ∧
      St m0 Z (Vt SL m0 lp) D6 8 st'.data)
      ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b5Offset)⟩ := by
  obtain ⟨hmid, hw, htr, h64, h72⟩ := ok_b5
  refine St.run h (rest := [(rspOf m0 + 8#64, 88)]) (vs := fun _ ↦ 0) (ret := 0) rfl
    (infix_of b5_in_code (by simp [b5]) hp) exit_b5 nofun hst.fr hst.same
    (((hst.hd.reg0 (rs' := (fb m0, F + 8) :: [(rspOf m0 + 8#64, 88)]) (by decide) rfl)).append
      (St.holdsDA h hst Z_outs)) (by decide)
    (wf1 h hst.fr.kept h.argsIn)
    (St.mt hst ⟨rfl, rfl, trivial⟩ trivial trivial argAliases_ok) hmid hw (by decide) htr
    fun st1 _ hpc1 hst1 hc ↦ .done _ ⟨hpc1, ?_⟩
  have g15 := hst.hd.reg (r := .r15) (i := 33) (by decide)
  have g13 := hst.hd.reg (r := .r13) (i := 34) (by decide)
  have l64 := hst.hd.load (r := 0) (o := 64) (i := 15) (by decide)
  have l72 := hst.hd.load (r := 0) (o := 72) (i := 16) (by decide)
  refine St.sub (St.add (V' := Vt SL m0 lp) hst1 (fun p hp ↦ Vt_lt (by revert p hp; decide))
    (holds_content (s := Lw 64) (i := 20) (hc _ _ rfl h64) ?_
      (holds_content (s := Lw 72) (i := 21) (hc _ _ rfl h72) ?_ (holds_nil _ _ _)))) (by decide)
  · show BinOp.apply .xor .W64 ((Env.ofMachine st [(fb m0, F + 8), (rspOf m0 + 8#64, 88)]).load 0 64 8)
      (st.regs.get64 .r15) = _
    rw [xor64, show (Env.ofMachine st [(fb m0, F + 8), (rspOf m0 + 8#64, 88)]).load 0 64 8 =
      (Env.ofMachine st [(fb m0, F + 8)]).load 0 64 8 from rfl, l64, g15]
    rw [Vt15, Vt33, lpK1, Vt20, add_c0, UInt64.toBitVec_xor]
  · show BinOp.apply .xor .W64 ((Env.ofMachine st [(fb m0, F + 8), (rspOf m0 + 8#64, 88)]).load 0 72 8)
      (st.regs.get64 .r13) = _
    rw [xor64, show (Env.ofMachine st [(fb m0, F + 8), (rspOf m0 + 8#64, 88)]).load 0 72 8 =
      (Env.ofMachine st [(fb m0, F + 8)]).load 0 72 8 from rfl, l72, g13]
    rw [Vt16, Vt34, lpK2, Vt21, add_c1, UInt64.toBitVec_xor]

/-- **From the entry to `b12`.** -/
theorem front (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (lp : Nat → UInt64) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b12Offset) ∧
      St m0 Z (Vt SL m0 lp) D12 8 st'.data)
      ⟨m0, Labels.label NativeRustcVmX64.Vm.AccumulateSide.entryLabel⟩ := by
  refine Eventually.bind (entry hp h lp) fun s hs ↦ ?_
  obtain ⟨d, pc⟩ := s
  rcases hs with ⟨hpc, hpos, hst⟩ | ⟨hpc, hz, hst⟩
  · simp only at hpc hst
    subst hpc
    refine Eventually.bind (knownLoop hp h hee hmul hpos hst) fun s ⟨hpc1, hst1⟩ ↦ ?_
    obtain ⟨d1, pc1⟩ := s
    simp only at hpc1 hst1
    subst hpc1
    refine Eventually.bind (addKnown hp h hst1 lp) fun s ⟨hpc2, hst2⟩ ↦ ?_
    obtain ⟨d2, pc2⟩ := s
    simp only at hpc2 hst2
    subst hpc2
    exact ones hp h hee hst2 lp
  · simp only at hpc hst
    subst hpc
    have l64 := hst.hd (Lw 64, 15) (by decide)
    have l72 := hst.hd (Lw 72, 16) (by decide)
    have hkn : knA SL m0 (cA SL m0) = 0 := by rw [hz]; rfl
    have hD6 : St m0 Z (Vt SL m0 lp) D6 8 d :=
      St.sub (St.add (V' := Vt SL m0 lp) hst (fun _ _ ↦ rfl)
        (holds_cons (s := Lw 64) (i := 20) (by
          rw [l64]; show Vt SL m0 lp 15 = _; rw [Vt15, Vt20, hkn, ew_add_zero])
        (holds_cons (s := Lw 72) (i := 21) (by
          rw [l72]; show Vt SL m0 lp 16 = _; rw [Vt16, Vt21, hkn, ew_add_zero]) (holds_nil _ _ _)))) (by decide)
    exact ones hp h hee hD6 lp

end

end NativeRustcVmX64.Bus.AccumulateSide
