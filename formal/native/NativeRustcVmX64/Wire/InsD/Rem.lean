module

public import NativeRustcVmX64.Wire.InsD.Shift

/-!
# `ins_d`'s shift from its set-up (x86-64)

The four-at-a-time loop (`unr_spec`), its test (`b11`, `f_spec`), the one-by-one moves (`b10`,
`rem_spec`), and the set-up (`b7`, `b8`, `b9`: `six_spec`).
-/

namespace NativeRustcVmX64.Wire.InsD

open NativeRustcX64 NativeRustcX64.Sym NativeRustcX64.Mem NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVm (WordAt WordsAt)
open NativeRustcVmX64.Vm.InsD

public section

variable [Host] {k : Nat} {m : MachineData} {L : List UInt64}

section
variable (hp : Placed code k) (g : G m L)
include hp g

/-- **The four-at-a-time loop**, then the store. -/
theorem unr_spec {i j : Nat} {gj : UInt64} {st : MachineState} (hI : UInv m L k i j gj st) :
    Eventually (step1 Host.exe) (Post m) st := by
  refine Sym.loop (fun n st ↦ ∃ g', UInv m L k i n g' st)
    (fun n st ⟨g', hI'⟩ ↦ ?_) ⟨gj, hI⟩
  refine Eventually.mono (unr_step hp g hI') fun st' h ↦ ?_
  rcases h with h | h
  · exact .inl h
  · exact .inr ⟨n - 4, by have := hI'.four; omega, _, h⟩

/-- **The test of four or more** (`b11`): the store, or the four-at-a-time loop. -/
theorem f_spec {i j : Nat} {gj : UInt64} {st : MachineState} (hI : FInv m L k i j gj st) :
    Eventually (step1 Host.exe) (Post m) st := by
  have hlt := g.lt
  refine run_reg hp b11_in_code (by simp [b11]) run_b11 rfl (by decide) (by decide) nofun hI.pc
    hI.kp fun st1 hk1 hd1 hr1 hpc1 ↦ ?_
  have hpc2 := pc_cond hpc1 (P := L.length - i < 4) (by
    refine (ge4 (n := reg st.data .r8) (i := reg st.data .rcx) (by rw [hI.r8]; omega)
      (by rw [hI.r8, hI.rcx]; exact hI.lt)).trans ?_
    rw [hI.r8, hI.rcx])
  have e : ∀ r ∈ [Reg64.rcx, .rax, .rsi], reg st1.data r = reg st.data r := fun r hr ↦
    hr1 r (.reg r) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> rfl)
  have hw1 : WordsAt st1.data.dmem (arr m) (hl L j gj) := by rw [hd1]; exact hI.w
  by_cases h4 : L.length - i < 4
  · rw [ite_t h4, hp.label NativeRustcVmX64.Vm.InsD.label_10_at] at hpc2
    have hji : j = i := by have := hI.rem; have := hI.jle; have := hI.lt; omega
    subst hji
    exact store_spec hp g hpc2 hk1 (by rw [e .rcx (by simp)]; exact hI.rcx)
      (by rw [e .rax (by simp)]; exact hI.rax) (le_of_lt hI.lt) hI.below hI.above hw1
  · rw [ite_f h4] at hpc2
    refine run_reg hp b12_in_code (by simp [b12]) run_b12 rfl (by decide) (by decide) nofun
      (hpc2.trans (congrArg Host.addrOf rfl)) hk1 fun st2 hk2 hd2 hr2 hpc3 ↦ ?_
    have e2 : ∀ r ∈ [Reg64.rcx, .rax, .rsi], reg st2.data r = reg st.data r := fun r hr ↦
      (hr2 r (.reg r) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> rfl)).trans (e r hr)
    simp only [PcOk] at hpc3
    have := hI.rem
    have := hI.jle
    exact unr_spec hp g (j := j) (gj := gj) ⟨hpc3.trans (congrArg Host.addrOf rfl), hk2,
      by rw [e2 .rcx (by simp)]; exact hI.rcx, by rw [e2 .rax (by simp)]; exact hI.rax,
      by rw [e2 .rsi (by simp)]; exact hI.rsi, by omega, by omega, hI.jle, hI.below, hI.above,
      by rw [hd2]; exact hw1⟩

/-- **A move** (`b10`): element `j - 1` to `j`; back at `NativeRustcVmX64.Vm.InsD.label_4` or at the test. -/
theorem rem_step {i j : Nat} {gj : UInt64} {st : MachineState} (hI : RInv m L k i j gj st) :
    Eventually (step1 Host.exe) (fun st' ↦ FInv m L k i (j - 1) (L.getD (j - 1) 0) st' ∨
      RInv m L k i (j - 1) (L.getD (j - 1) 0) st') st := by
  have hlt := g.lt
  have hjn := hI.jle
  have hc := hI.r9
  have hc0 := hI.pos
  have hj1 : 1 ≤ j := by omega
  have hij : i < j := by omega
  have hok := g.ok
  let rs : List (BitVec 64 × Nat) := [(pos m (j - 1), 8), (pos m j, 8)]
  let env := Env.ofMachine st.data rs
  have hwf : env.WF := Env.wf_of
    ⟨pos_ok hok hI.kp (by omega), pos_ok hok hI.kp (by omega), trivial⟩
    (List.pairwise_pair.mpr (pos_apart hok (by omega) (by omega) (by omega)))
  have hm : Match env remS st.data := by
    refine match_ofMachine ⟨rfl, rfl, trivial⟩ trivial trivial trivial
      ⟨elem_alias hI.kp (r := 0) rfl ?_, elem_alias hI.kp (r := 1) rfl ?_, trivial⟩
    · show (BinOp.apply .add .W64 (reg st.data .r10) (BitVec.ofNat 64 (2 ^ 64 - 1))).toNat % 256 =
        j - 1
      have := hI.r10
      rw [dec64 (by omega) (by omega), hI.r10]; omega
    · show (reg st.data .r10).toNat % 256 = j
      rw [hI.r10]; omega
  refine exec_at (Wire.infix_of b10_in_code (by simp [b10]) hp) run_b10 hwf nofun hI.pc hm
    fun st' hm' hpc' ↦ ?_
  have hs : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
      (NativeRustcVm.InRange (pos m j) 8) :=
    NativeRustcVmX64.Transcript.sameOutside_region hwf hm' (r := 1) rfl (by decide)
  have hkp : Kp m st'.data := hI.kp.block hm hm' hwf rfl (by decide) (by decide)
    (pos_sub1 hok (by omega) hs)
  have hws : WordsAt st'.data.dmem (arr m) (hl L (j - 1) (L.getD (j - 1) 0)) := by
    refine wordsAt_update (C := hl L j gj) (by rw [length_hl L hjn, length_hl L (by omega)]) hI.w
      (g.hl_noWrap hjn gj) (lo := j) (hi := j + 1) (by omega) (by rw [length_hl L hjn]; omega)
      (by rw [show 8 * (j + 1 - j) = 8 by omega]; exact hs) (fun t h1 h2 ↦ ?_)
      (fun t _ ht ↦ getD_hl_out (by omega) hjn gj (by omega))
    obtain rfl : t = j := by omega
    rw [getD_hl_in (by omega) (by omega)]
    exact moved hm' (r := 1) (r' := 0) rfl rfl (by decide) (hl_word hjn hI.w (by omega))
  have e : ∀ r ∈ [Reg64.rcx, .rax, .r8], reg st'.data r = reg st.data r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Match.reg_eq hm hm' rfl rfl
  have hr9 : (reg st'.data .r9).toNat = (reg st.data .r9).toNat - 1 := by
    rw [show reg st'.data .r9 = BinOp.apply .sub .W64 (reg st.data .r9) (BitVec.ofNat 64 1)
      from hm'.regs .r9 _ rfl, toNat_sub64 (by rw [BitVec.toNat_ofNat]; omega),
      BitVec.toNat_ofNat]
  have hdec : ∀ r ∈ [Reg64.rsi, .r10], (reg st'.data r).toNat = j - 1 := fun r hr ↦ by
    have hv : (BinOp.apply .add .W64 (reg st.data .r10)
        (BitVec.ofNat 64 18446744073709551615)).toNat = j - 1 := by
      rw [toNat_add64, hI.r10, BitVec.toNat_ofNat]
      omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (congrArg BitVec.toNat
        (hm'.regs .rsi (.bin .add .W64 (.reg .r10) (.lit 18446744073709551615)) rfl)).trans hv
    · exact (congrArg BitVec.toNat
        (hm'.regs .r10 (.bin .add .W64 (.reg .r10) (.lit 18446744073709551615)) rfl)).trans hv
  have hpc2 := pc_cond hpc' (P := (reg st.data .r9).toNat - 1 ≠ 0) (by
    show (!(CmpOp.apply .eq .W64 (BinOp.apply .sub .W64 (reg st.data .r9) (BitVec.ofNat 64 1))
      (BitVec.ofNat 64 0))) = _
    rw [eq64, toNat_sub64 (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq])
  by_cases hz : (reg st.data .r9).toNat - 1 ≠ 0
  · rw [ite_t hz, hp.label NativeRustcVmX64.Vm.InsD.label_4_at] at hpc2
    exact .done _ (.inr ⟨hpc2, hkp, by rw [e .rcx (by simp)]; exact hI.rcx,
      by rw [e .rax (by simp)]; exact hI.rax, by rw [e .r8 (by simp)]; exact hI.r8,
      hdec .r10 (by simp), by rw [hr9]; omega, by rw [hr9]; omega, hI.lt, by omega, hI.below,
      hI.above, hws⟩)
  · rw [ite_f hz] at hpc2
    exact .done _ (.inl ⟨hpc2.trans (congrArg Host.addrOf rfl), hkp,
      by rw [e .rcx (by simp)]; exact hI.rcx, by rw [e .rax (by simp)]; exact hI.rax,
      by rw [e .r8 (by simp)]; exact hI.r8, hdec .rsi (by simp), by omega, hI.lt, by omega,
      hI.below, hI.above, hws⟩)

/-- **The one-by-one moves**, then the rest. -/
theorem rem_spec {i j : Nat} {gj : UInt64} {st : MachineState} (hI : RInv m L k i j gj st) :
    Eventually (step1 Host.exe) (Post m) st := by
  refine Sym.loop (fun n st ↦ ∃ g', RInv m L k i n g' st)
    (fun n st ⟨g', hI'⟩ ↦ ?_) ⟨gj, hI⟩
  refine Eventually.bind (rem_step hp g hI') fun st' h ↦ ?_
  rcases h with h | h
  · exact Eventually.mono (f_spec hp g h) fun _ h ↦ .inl h
  · exact .done _ (.inr ⟨n - 1, by have := hI'.r9; have := hI'.pos; omega, _, h⟩)

/-- **From `NativeRustcVmX64.Vm.InsD.label_1`** (`b7`): `x` stored at once, or the shift. -/
theorem six_spec {i : Nat} {gn : UInt64} (hgn : WordsAt m.dmem (arr m) (L ++ [gn]))
    {st : MachineState} (hI : SixInv m L k i st) : Eventually (step1 Host.exe) (Post m) st := by
  have hlt := g.lt
  have hw0 : WordsAt st.data.dmem (arr m) (hl L L.length gn) := by
    rw [hl_length, hI.d]; exact hgn
  refine run_reg hp b7_in_code (by simp [b7]) run_b7 rfl (by decide) (by decide) nofun hI.pc
    hI.kp fun st1 hk1 hd1 hr1 hpc1 ↦ ?_
  have hR : (Sym.ite (SBool.cmp .ult .W64 (.reg .rax) (.lit 255)) (.reg .rax) (.lit 255)).eval
      (Env.ofMachine st.data []) = reg st.data .rax := by
    simp only [Sym.eval, SBool.eval, Env.ofMachine_regs]
    exact min255 (by rw [hI.rax]; omega)
  have h8 : (reg st1.data .r8).toNat = L.length := by
    rw [hr1 .r8 _ rfl, hR, hI.rax]
  have e : ∀ r ∈ [Reg64.rcx, .rax], reg st1.data r = reg st.data r := fun r hr ↦
    hr1 r (.reg r) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> rfl)
  have hpc2 := pc_cond hpc1 (P := i = L.length) (by
    show (CmpOp.apply .ult .W64 ((Sym.ite (SBool.cmp .ult .W64 (.reg .rax) (.lit 255)) (.reg .rax)
      (.lit 255)).eval (Env.ofMachine st.data [])) (reg st.data .rcx) ||
      CmpOp.apply .eq .W64 ((Sym.ite (SBool.cmp .ult .W64 (.reg .rax) (.lit 255)) (.reg .rax)
      (.lit 255)).eval (Env.ofMachine st.data [])) (reg st.data .rcx)) = _
    rw [hR, ult64, eq64]
    rw [hI.rax, hI.rcx, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    have := hI.le
    omega)
  have hrcx : (reg st1.data .rcx).toNat = i := by rw [e .rcx (by simp)]; exact hI.rcx
  have hrax : (reg st1.data .rax).toNat = L.length := by rw [e .rax (by simp)]; exact hI.rax
  have hw1 : WordsAt st1.data.dmem (arr m) (hl L L.length gn) := by rw [hd1]; exact hw0
  by_cases hin : i = L.length
  · rw [ite_t hin, hp.label NativeRustcVmX64.Vm.InsD.label_10_at] at hpc2
    subst hin
    exact store_spec hp g hpc2 hk1 hrcx hrax le_rfl hI.below hI.above hw1
  rw [ite_f hin] at hpc2
  have hil : i < L.length := by have := hI.le; omega
  -- `b8`: the remainder's count.
  refine run_reg hp b8_in_code (by simp [b8]) run_b8 rfl (by decide) (by decide) nofun
    (hpc2.trans (congrArg Host.addrOf rfl)) hk1 fun st2 hk2 hd2 hr2 hpc3 ↦ ?_
  have hq : (BinOp.apply .and .W32 (BinOp.apply .sub .W32 (UnOp.apply .trunc .W32
      (reg st1.data .r8)) (reg st1.data .rcx)) (BitVec.ofNat 64 3)).toNat =
      (L.length - i) % 4 := by
    rw [rem4 (by rw [h8]; omega) (by rw [h8, hrcx]; exact hil), h8, hrcx]
  have hpc4 := pc_cond hpc3 (P := (L.length - i) % 4 = 0) (by
    show CmpOp.apply .eq .W32 (BinOp.apply .and .W32 (BinOp.apply .sub .W32
      (UnOp.apply .trunc .W32 (reg st1.data .r8)) (reg st1.data .rcx)) (BitVec.ofNat 64 3))
      (BitVec.ofNat 64 0) = _
    rw [eq32_zero _ (by rw [hq]; omega), hq])
  have e2 : ∀ r ∈ [Reg64.rcx, .rax, .r8], reg st2.data r = reg st1.data r := fun r hr ↦
    hr2 r (.reg r) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> rfl)
  have hsi2 : (reg st2.data .rsi).toNat = L.length := by rw [hr2 .rsi _ rfl]; exact h8
  have hr92 : (reg st2.data .r9).toNat = (L.length - i) % 4 := by rw [hr2 .r9 _ rfl]; exact hq
  have hw2 : WordsAt st2.data.dmem (arr m) (hl L L.length gn) := by rw [hd2]; exact hw1
  by_cases h0 : (L.length - i) % 4 = 0
  · rw [ite_t h0, hp.label NativeRustcVmX64.Vm.InsD.label_5_at] at hpc4
    exact f_spec hp g ⟨hpc4, hk2, by rw [e2 .rcx (by simp)]; exact hrcx,
      by rw [e2 .rax (by simp)]; exact hrax, by rw [e2 .r8 (by simp)]; exact h8, hsi2,
      by omega, hil, le_rfl, hI.below, hI.above, hw2⟩
  rw [ite_f h0] at hpc4
  -- `b9`: the moves' start.
  refine run_reg hp b9_in_code (by simp [b9]) run_b9 rfl (by decide) (by decide) nofun
    (hpc4.trans (congrArg Host.addrOf rfl)) hk2 fun st3 hk3 hd3 hr3 hpc5 ↦ ?_
  simp only [PcOk] at hpc5
  have e3 : ∀ r ∈ [Reg64.rcx, .rax, .r8, .r9], reg st3.data r = reg st2.data r := fun r hr ↦
    hr3 r (.reg r) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> rfl)
  exact rem_spec hp g (j := L.length) (gj := gn) ⟨hpc5.trans (congrArg Host.addrOf rfl), hk3,
    by rw [e3 .rcx (by simp), e2 .rcx (by simp)]; exact hrcx,
    by rw [e3 .rax (by simp), e2 .rax (by simp)]; exact hrax,
    by rw [e3 .r8 (by simp), e2 .r8 (by simp)]; exact h8,
    by rw [hr3 .r10 _ rfl, show (Sym.reg .r8).eval (Env.ofMachine st2.data []) = reg st2.data .r8
      from rfl, e2 .r8 (by simp)]; exact h8,
    by rw [e3 .r9 (by simp), hr92]; omega, by rw [e3 .r9 (by simp), hr92]; omega, hil, le_rfl,
    hI.below, hI.above, by rw [hd3]; exact hw2⟩

end

end

end NativeRustcVmX64.Wire.InsD
