module

public import NativeRustcVmX64.Bus.AccumulateSide.Arith
public import NativeRustcVmX64.Bus.AccumulateSide.FactsK
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names

/-!
# `accumulate_side`: the prologue (x86-64)

`b0` pushes the callee-saved registers, keeps the arguments in the frame and computes the
framework's address (R12), count (R13) and the known part's count (`min` of it and the
fingerprints', RDX and the frame word at `24`); with no known part it jumps to the ones (`b6`),
else `b1` clears the known part's sums and falls into its loop (`b2`). `entry`: the body's state
at either.
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

@[expose] public section

/-- No output written. -/
def Z (_ : BitVec 64) : Prop := False

end

public section

theorem Z_outs {m0 : MachineData} : ∀ q, Z q → outs m0 q := fun _ h ↦ h.elim

section
variable [Labels] (env : Env)

theorem ev_r13S {s : Nat} (hs : s ≤ 3) (h2 : env.load 2 8 8 = BitVec.ofNat 64 s) :
    r13S.eval env = BitVec.ofNat 64 s := by
  simp only [r13S, Sym.eval, SBool.eval, CmpOp.apply, low_W64, h2, ult_ofNat (by omega : s < 2 ^ 64)
    (by decide : 4 < 2 ^ 64), show s < 4 from by omega, decide_true, ↓reduceIte]

theorem ev_r12S {s : Nat} (hs : s ≤ 3) (h2 : env.load 2 8 8 = BitVec.ofNat 64 s) :
    r12S.eval env = env.load 1 0 8 + 16#64 := by
  simp only [r12S, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, h2,
    ult_ofNat (by omega : s < 2 ^ 64) (by decide : 4 < 2 ^ 64), show s < 4 from by omega,
    decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem ev_minS {s : Nat} (hs : s ≤ 3) (h2 : env.load 2 8 8 = BitVec.ofNat 64 s) :
    (minS.eval env).toNat = min (env.load 1 16 8).toNat s := by
  have e : r13S.eval env = BitVec.ofNat 64 s := ev_r13S env hs h2
  simp only [minS, Sym.eval, SBool.eval, CmpOp.apply, low_W64] at e ⊢
  rw [e]
  have h' : (BitVec.ofNat 64 s).toNat = s := toNat_ofNat_lt (by omega)
  split <;> rename_i hc <;> simp only [Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not,
    h'] at hc <;> (try simp only [h']) <;> omega

theorem ev_c0 {s : Nat} (hs : s ≤ 3) (h2 : env.load 2 8 8 = BitVec.ofNat 64 s) :
    c0.eval env = decide (min (env.load 1 16 8).toNat s = 0) := by
  have e := ev_minS env hs h2
  simp only [c0, SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64,
    BitVec.and_self]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    rw [← e, h]
    rfl
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [e, h]
    rfl

end

variable [Host] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData} {k : Nat}

/-- The side layout's address as an input. -/
theorem Pre.slIn (h : Pre L rows bl Fm SL m0) : In m0 (stackArg m0 0) 888 :=
  In.of_inOk h.slOk (Apart.symm' h.fSL)

/-- The framework's count. -/
theorem Pre.fw (h : Pre L rows bl Fm SL m0) : SL.framework.size ≤ 3 ∧
    NativeRustcVm.WordAt m0.dmem (off (stackArg m0 0) 8) SL.framework.size.toUInt64 :=
  ⟨h.sl.framework.1, h.sl.framework.2.1⟩

/-- The table blocks' count. -/
theorem Pre.tb (h : Pre L rows bl Fm SL m0) : SL.tables.size ≤ 51 ∧
    NativeRustcVm.WordAt m0.dmem (off (stackArg m0 0) 64) SL.tables.size.toUInt64 :=
  ⟨h.sl.tables.1, h.sl.tables.2.1⟩

/-- The registers' and stack arguments' description at the entry. -/
theorem holdsDE (h : Pre L rows bl Fm SL m0) {lp : Nat → UInt64} {rest : List (BitVec 64 × Nat)} :
    Holds ((fb m0, F + 8) :: (rspOf m0 + 8#64, 88) :: rest) (Vt SL m0 lp) DE m0 := by
  refine Holds.append (Holds.append ?_ (holdsArgs fun i hi ↦ argWord0 h hi)) holdsDl
  refine holds_reg rfl (holds_reg rfl (holds_reg rfl (holds_reg rfl (holds_reg rfl
    (holds_reg rfl (holds_nil _ _ _))))))

/-- **The prologue** (`b0`, `b1`): the known part's loop's head (`b2`, turn `0`) or, with no
known part, the ones' (`b6`). -/
theorem entry (hp : Placed code k) (h : Pre L rows bl Fm SL m0) (lp : Nat → UInt64) :
    Eventually (step1 Host.exe) (fun st ↦
      (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b2Offset) ∧ 0 < cA SL m0 ∧
        St m0 Z (Vt SL m0 (lpK SL m0 0)) DK 8 st.data) ∨
      (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b6Offset) ∧ cA SL m0 = 0 ∧
        St m0 Z (Vt SL m0 lp) (D0 ++ E0) 8 st.data))
      ⟨m0, Labels.label NativeRustcVmX64.Vm.AccumulateSide.entryLabel⟩ := by
  have hfw := h.fw
  have hsl := h.slIn
  have hA := h.argsIn
  have hAS : Apart (rspOf m0 + 8#64) 88 (stackArg m0 0) 888 := Apart.symm' h.slArgs
  let rs : List (BitVec 64 × Nat) := [(rspOf m0 + 8#64, 88), (stackArg m0 0, 888)]
  let env := frameEnv m0 m0 F rs (fun _ ↦ 0) 0
  have hwf : env.WF := wf2 h (fun _ h ↦ h) hA hsl hAS
  have hl0 : env.load 1 0 8 = stackArg m0 0 := by
    rw [load_ofMachine (r := 1) (n := 88) (o := 0) rfl (argWord0 h (i := 0) (by decide))]
  have hl16 : env.load 1 16 8 = stackArg m0 2 := by
    rw [load_ofMachine (r := 1) (n := 88) (o := 16) rfl (argWord0 h (i := 2) (by decide))]
  have hl28 : env.load 2 8 8 = BitVec.ofNat 64 SL.framework.size :=
    load_ofMachine (r := 2) (n := 888) (o := 8) rfl hfw.2
  have hm : Match env entryS m0 :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial
      (allOf_append argAliases_ok ⟨by
        show env.load 1 0 8 = stackArg m0 0 + BitVec.ofInt 64 0
        rw [hl0]; simp, trivial⟩)
  unfold NativeRustcVmX64.Vm.AccumulateSide.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.AccumulateSide.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf nofun hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hw1, htr1, h12, h13, hdx, hc24⟩ := ok_b0
  have hw1' : ∀ w ∈ (after b0 entryS).mem, w.r = 0 := fun w hw ↦ by
    simpa using List.all_eq_true.mp hw1 w hw
  have hfr1 : Frame m0 F slots 8 st1.data :=
    Frame.of_prologue Frame.entry hwf hm1 hpro slots_le slots_cs
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (fun q ↦ Z q ∨ NativeRustcVm.InRange (stackBelow m0 N) N q) := fun q hq ↦
    hm1.get?_mem0 hwf fun hW ↦ hq (.inr (inRange_frame_stack h.sp8 h.spN le_F
      (written_low hwf hw1' (belowRet_of_pro hpro) hW)))
  have e12 : st1.data.regs.get64 .r12 = stackArg m0 0 + 16#64 := by
    rw [hm1.regs .r12 _ h12, ev_r12S env hfw.1 hl28, hl0]
  have e13 : st1.data.regs.get64 .r13 = BitVec.ofNat 64 SL.framework.size := by
    rw [hm1.regs .r13 _ h13, ev_r13S env hfw.1 hl28]
  have emin : (minS.eval env).toNat = cA SL m0 := by
    rw [ev_minS env hfw.1 hl28, hl16]
  have hH : Holds [(fb m0, F + 8)] (Vt SL m0 lp) (D0 ++ E0) st1.data := by
    refine Holds.append (Holds.reg0 (Holds.after rfl (holdsDE h) (by decide) hm1 htr1) (by decide)
      rfl) ?_
    refine holds_reg (by rw [e12]; rfl) (holds_reg (by rw [e13]; rfl)
      (holds_reg ?_ (holds_content (s := Lw 24) (e := env) (c := minS) ?_ ?_ (holds_nil _ _ _))))
    · rw [hm1.regs .rdx _ hdx, bv_eq emin]; rfl
    · have := content_eval (rs := (fb m0, F + 8) :: rs) rfl hm1 hc24
      rw [← this]
      unfold tval
      rfl
    · rw [bv_eq emin]; rfl
  have hst1 : St m0 Z (Vt SL m0 lp) (D0 ++ E0) 8 st1.data := ⟨hfr1, hs1, hH⟩
  simp only [PcOk] at hpc1
  rw [ev_c0 env hfw.1 hl28, hl16] at hpc1
  by_cases hc : cA SL m0 = 0
  · refine .done _ (.inr ⟨?_, hc, hst1⟩)
    rw [hpc1, decide_eq_true hc]
    exact hp.label NativeRustcVmX64.Vm.AccumulateSide.label_4_at
  · rw [decide_eq_false hc] at hpc1
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
    have hpos : 0 < cA SL m0 := Nat.pos_of_ne_zero hc
    obtain ⟨d1, pc1⟩ := st1
    simp only at hpc1 hst1
    subst hpc1
    -- `b1`: the known part's sums cleared.
    obtain ⟨hmid, hw, htr, hc24', hbp, h15, h13'⟩ := ok_b1
    refine St.run h (rest := []) (vs := fun _ ↦ 0) (ret := 0) rfl (infix_of b1_in_code (by simp [b1]) hp) exit_b1 nofun
      hst1.fr hst1.same hst1.hd (by decide) (wf0 h hst1.fr.kept)
      (St.mt hst1 ⟨rfl, trivial⟩ trivial trivial trivial) hmid hw (by decide) htr
      fun st hm' hpc hst hcont ↦ ?_
    have h24 := hcont (Lw 24) _ rfl hc24'
    have e24 : (Sym.load 0 24 8).eval (frameEnv m0 d1 F [] (fun _ ↦ 0) 0) =
        BitVec.ofNat 64 (cA SL m0) := by
      rw [show (Sym.load 0 24 8).eval (frameEnv m0 d1 F [] (fun _ ↦ 0) 0) =
        (Env.ofMachine d1 [(fb m0, F + 8)]).load 0 24 8 from rfl,
        hst1.hd.load (by decide : (Sym.load 0 24 8, 28) ∈ D0 ++ E0)]
      rfl
    have hcA : cA SL m0 ≤ 3 := Nat.le_trans (Nat.min_le_right _ _) hfw.1
    refine .done _ (.inl ⟨by rw [hpc]; change Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b0Offset + b0.length + b1.length) = _; rw [Nat.add_assoc k NativeRustcVmX64.Vm.AccumulateSide.b0Offset b0.length, NativeRustcVmX64.Vm.AccumulateSide.b0_next, Nat.add_assoc, NativeRustcVmX64.Vm.AccumulateSide.b1_next], hpos, St.sub (St.add (V' := Vt SL m0 (lpK SL m0 0))
      (E := [(Lw 24, 19), (Rg .rbp, 32), (Rg .r15, 33), (Rg .r13, 34)]) hst
      (fun p hp ↦ Vt_lt (by revert p hp; decide)) ?_) (by decide)⟩)
    refine holds_content (e := frameEnv m0 d1 F [] (fun _ ↦ 0) 0) h24 ?_
      (holds_reg ?_ (holds_reg ?_ (holds_reg ?_ (holds_nil _ _ _))))
    · rw [Sym.eval, e24, Sym.eval, shl4, toNat_ofNat_lt (by omega)]; rfl
    · rw [hm'.regs .rbp _ hbp]; rfl
    · rw [hm'.regs .r15 _ h15]; rfl
    · rw [hm'.regs .r13 _ h13']; rfl

end

end NativeRustcVmX64.Bus.AccumulateSide
