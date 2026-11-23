module

public import NativeRustcVmX64.Whir.NovelEval.Dbl
public import NativeRustcVmX64.Code.Vm.Kmul.Names

/-!
# `novel_eval`'s inner doubling loop (x86-64)

`inner`: a turn of the inner loop (`b6a`, `kmul`, `b7`) stores the product of basis word `t` and
value `j` after the basis (`IInv j (t + 1)`); after the last, `b8` doubles the size and goes back
to the doubling loop's head (`OInv (j + 1)`) or, the basis long enough, to `b9` (`Mid`).
-/

namespace NativeRustcVmX64.Whir.NovelEval

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.NovelEval NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region WordAt WordsAt wordOf)
open NativeRustcVmX64.Field (midS frameS frameEnv)
open NativeRustcVmX64.Arrays (load8_eq wordAt_of_write eval_reg eval_lit eval_load eval_add
  eval_cmp_eq eval_not)

public section

theorem dec_toNat {x : BitVec 64} {n : Nat} (h : x.toNat = n) (h1 : 1 ≤ n) :
    (x - BitVec.ofNat 64 1).toNat = n - 1 := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, h]
  have := x.isLt
  omega

theorem add8 (a : BitVec 64) (n : Nat) :
    BitVec.ofNat 64 8 + (a + BitVec.ofNat 64 n) = a + BitVec.ofNat 64 (n + 8) := by
  rw [BitVec.add_comm, addr_add]

variable [Host] {k : Nat}

/-- **A turn of the inner loop.** -/
theorem inner (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 : MachineData} (hpre : NovelEvalPre m0) (hc : cnt m0 ≤ 64) {j t : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b6Offset)) (hI : IInv m0 j t st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b6Offset) ∧ IInv m0 j (t + 1) s.data) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b4Offset) ∧ OInv m0 (j + 1) s.data) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b9Offset) ∧ Mid m0 s.data)) st := by
  obtain ⟨hS, hcs, hwh, hout, _⟩ := hpre
  have hF : 1104 ≤ novelEvalStack := by decide
  have hle : 1104 + kmulStack ≤ novelEvalStack := by decide
  have hS1 := hS.1
  have hS2 := hS.2.1
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hfr := hI.fr
  have hsz := basis_le_32 m0 j hc hI.lt
  have ht := hI.ht
  have hsl := slots_ok
  have hlw : ∀ w : UInt64, (NativeRustcVm.wordBytes w).length = 8 := NativeRustcVm.length_wordBytes
  have hlb : ((basisOf m0 j).toList.flatMap NativeRustcVm.wordBytes).length =
      8 * (basisOf m0 j).size := by
    rw [NativeRustcVm.length_wordsBytes, Array.length_toList]
  have hln : ∀ u, (List.flatMap NativeRustcVm.wordBytes
      (((basisOf m0 j).toList.take u).map (kmul · ((whatOf m0).getD j 0)))).length =
        8 * min u (basisOf m0 j).size := fun u ↦ by
    rw [NativeRustcVm.length_wordsBytes, List.length_map, List.length_take, Array.length_toList]
  -- `b6a`: basis word `t`
  have hrd : Readable st.data (fbOf m0 + BitVec.ofNat 64 (32 + 8 * t)) 8 :=
    Readable.keep (Readable.sub (m := m0) ⟨hfmap, hfnw⟩ (by omega)) hfr.kept
  have hwf : (Env.ofMachine st.data [(fbOf m0 + BitVec.ofNat 64 (32 + 8 * t), 8)]).WF :=
    Env.wf_of ⟨⟨hrd.1, hrd.2⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine st.data [(fbOf m0 + BitVec.ofNat 64 (32 + 8 * t), 8)]) ldS
      st.data :=
    match_ofMachine ⟨rfl, trivial⟩
      ⟨show reg st.data .r14 = fbOf m0 + BitVec.ofNat 64 (32 + 8 * t) + BitVec.ofInt 64 0 by
          rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; exact hI.r14, trivial⟩
      trivial trivial trivial
  refine exec_at (hb6 hp).1 run_b6a hwf (by intro l h; cases h) hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hfr1 := hfr.of_block hm hm1 hwf rfl (after_eq run_b6a ▸ b6a_keeps)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hrdi1 : reg st1.data .rdi = ((basisOf m0 j)[t]'(by omega)).toBitVec := by
    refine (hm1.regs .rdi _ rfl).trans ?_
    rw [eval_load, load8_eq]
    show (wordOf st.data.dmem (fbOf m0 + BitVec.ofNat 64 (32 + 8 * t) + BitVec.ofNat 64 0)).toBitVec = _
    have h := NativeRustcVm.WordsAt.getElem hI.basis (i := t) (by rw [Array.length_toList]; omega)
    rw [addr_add, Array.getElem_toList] at h
    rw [NativeRustcVm.addr_add_zero, NativeRustcVm.wordOf_of_wordAt h]
  have hrsi1 : reg st1.data .rsi = ((whatOf m0).getD j 0).toBitVec :=
    (hm1.regs .rsi _ rfl).trans hI.r13
  have e1 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg st1.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm hm1 rfl rfl
  -- `b6b`: `kmul`
  have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b6Offset + b6a.length) := hpc1
  have hwf2 := hfr1.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b7Offset)).toBitVec) hS hF
  refine exec_at (hb6 hp).2 run_b6b hwf2 (fun _ _ ↦ rfl) hpc1' hfr1.mid_match fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hk2, hsp2, hw2⟩ := after_eq run_b6b ▸ b6b_call
  have hrsp2 := rsp_call hm2 hsp2
  refine Frame.call hkmul hfr1 hS hle (L := 1056) (by decide) hsl out_nil hwf2 hfr1.mid_match hm2
    hpc2 hk2 hsp2 (fun w hw ↦ ⟨(hw2 w hw).1, by have := (hw2 w hw).2; omega⟩)
    (stackOk_callee hS (fun p h ↦ hm2.kept hwf2 p (hfr1.kept p h)) hrsp2 hle)
    (fun m' ⟨_, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inr (.inr h))⟩)
    fun st3 hpc3 hfr3 ⟨hax3, hso3, hsv3⟩ ↦ ?_
  have k3 : ∀ {o : Nat} {bs : List UInt8}, 8 ≤ o → o + bs.length ≤ 1112 →
      NativeRustcVm.BytesAt st.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st3.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs :=
    fun h8 hlen h ↦ keep_call hm2 hwf2 rfl rfl hw2 hS hrsp2 hle hso3 h8 hlen (hd1 ▸ h)
  have e3 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg st3.data r = reg st.data r := by
    intro r hr
    rw [← e1 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (hsv3.1 _ rfl).trans (Match.reg_eq hfr1.mid_match hm2 rfl rfl)
  have hprod : UInt64.ofBitVec (reg st3.data .rax) =
      kmul ((basisOf m0 j)[t]'(by omega)) ((whatOf m0).getD j 0) := by
    rw [hax3, show reg st2.data .rdi = reg st1.data .rdi from Match.reg_eq hfr1.mid_match hm2 rfl rfl,
      show reg st2.data .rsi = reg st1.data .rsi from Match.reg_eq hfr1.mid_match hm2 rfl rfl,
      hrdi1, hrsi1, UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec]
  -- `b7`: the product stored
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b7Offset) := hpc3
  have hc7 : 32 + 8 * ((basisOf m0 j).size + t) + 8 ≤ 1056 := by omega
  have hrd4 : Readable st3.data
      (fbOf m0 + BitVec.ofNat 64 (32 + 8 * ((basisOf m0 j).size + t))) 8 :=
    Readable.keep (Readable.sub (m := m0) ⟨hfmap, hfnw⟩ (by omega)) hfr3.kept
  have hwf4 : (Env.ofMachine st3.data
      [(fbOf m0 + BitVec.ofNat 64 (32 + 8 * ((basisOf m0 j).size + t)), 8)]).WF :=
    Env.wf_of ⟨⟨hrd4.1, hrd4.2⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hrbp3 : reg st3.data .rbp = BitVec.ofNat 64 (basisOf m0 j).size :=
    ofNat_toNat ((congrArg BitVec.toNat (e3 .rbp (by simp))).trans hI.rbp)
  have hm4 : Match (Env.ofMachine st3.data
      [(fbOf m0 + BitVec.ofNat 64 (32 + 8 * ((basisOf m0 j).size + t)), 8)]) hiS st3.data :=
    match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨by
      show BinOp.apply .add .W64 (reg st3.data .r14)
        (BinOp.apply .mul .W64 (reg st3.data .rbp) (BitVec.ofNat 64 8)) =
          fbOf m0 + BitVec.ofNat 64 (32 + 8 * ((basisOf m0 j).size + t)) + BitVec.ofInt 64 0
      rw [add64, mul64, e3 .r14 (by simp), hI.r14, hrbp3, mul8, addr_add,
        show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
      congr 2
      omega, trivial⟩
  refine exec_at (hb7 hp) run_b7 hwf4 (by intro l h; cases h) hpc3' hm4 fun st4 hm5 hpc4 ↦ ?_
  obtain ⟨hk5, hw5, hv5⟩ := after_eq run_b7 ▸ b7_write
  have hfr4 := hfr3.of_write hm4 hm5 hwf4 rfl hk5 (r := 0) rfl le_rfl hw5
    (fun p h ↦ .inr (inRange_stack_of hS hF (L := 1056) (by decide) hc7 h))
    (slot_not_in hS hF hc7 (by omega) hsl)
  have k4 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 1112 →
      (o + bs.length ≤ 32 + 8 * ((basisOf m0 j).size + t) ∨
        32 + 8 * ((basisOf m0 j).size + t) + 8 ≤ o) →
      NativeRustcVm.BytesAt st3.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st4.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs :=
    fun hlen hap h ↦ keep_write hm5 hwf4 rfl rfl hw5 hS hF (by omega) hlen hap h
  have hv : WordAt st4.data.dmem (fbOf m0 + BitVec.ofNat 64 (32 + 8 * ((basisOf m0 j).size + t)))
      (kmul ((basisOf m0 j)[t]'(by omega)) ((whatOf m0).getD j 0)) := by
    have := wordAt_of_write hm5 (r := 0) (o := 0) rfl (by decide) (v := .reg .rax) hv5
    rwa [NativeRustcVm.addr_add_zero, eval_reg, Env.ofMachine_regs,
      show UInt64.ofBitVec (st3.data.regs.get64 .rax) = _ from hprod] at this
  have e4 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13], reg st4.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact (Match.reg_eq hm4 hm5 rfl rfl).trans (e3 _ (by simp))
  have hsp4 : Spill m0 st4.data :=
    ⟨k4 (by rw [hlw]; omega) (.inl (by rw [hlw]; omega)) (k3 (by omega) (by rw [hlw]; omega)
        hI.sp.out),
      k4 (by rw [hlw]; omega) (.inl (by rw [hlw]; omega)) (k3 (by omega) (by rw [hlw]; omega)
        hI.sp.cs)⟩
  have hed4 : EndAt m0 st4.data :=
    k4 (by rw [hlw]; omega) (.inl (by rw [hlw]; omega)) (k3 (by omega) (by rw [hlw]; omega) hI.ed)
  have hbas4 : WordsAt st4.data.dmem (fbOf m0 + BitVec.ofNat 64 32) (basisOf m0 j).toList :=
    k4 (by rw [hlb]; omega) (.inl (by rw [hlb]; omega)) (k3 (by omega) (by rw [hlb]; omega)
      hI.basis)
  have hnew4 : WordsAt st4.data.dmem (fbOf m0 + BitVec.ofNat 64 (32 + 8 * (basisOf m0 j).size))
      (((basisOf m0 j).toList.take (t + 1)).map (kmul · ((whatOf m0).getD j 0))) := by
    have hl : ((basisOf m0 j).toList.take (t + 1)).map (kmul · ((whatOf m0).getD j 0)) =
        ((basisOf m0 j).toList.take t).map (kmul · ((whatOf m0).getD j 0)) ++
          [kmul ((basisOf m0 j)[t]'(by omega)) ((whatOf m0).getD j 0)] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by rw [Array.length_toList]; omega),
        Option.toList_some, List.map_append, List.map_singleton, Array.getElem_toList]
    rw [hl, NativeRustcVm.wordsAt_append, NativeRustcVm.wordsAt_singleton, List.length_map,
      List.length_take, Array.length_toList, addr_add]
    refine ⟨k4 (by rw [hln]; omega) (.inl (by rw [hln]; omega))
      (k3 (by omega) (by rw [hln]; omega) hI.new), ?_⟩
    rw [show 32 + 8 * (basisOf m0 j).size + 8 * min t (basisOf m0 j).size =
      32 + 8 * ((basisOf m0 j).size + t) by omega]
    exact hv
  -- the branch
  have hr15 : (reg st3.data .r15).toNat = (basisOf m0 j).size - t :=
    (congrArg BitVec.toNat (e3 .r15 (by simp))).trans hI.r15
  simp only [PcOk] at hpc4
  rw [eval_not, eval_cmp_eq] at hpc4
  rw [show (Sym.bin .sub .W64 (.reg .r15) (.lit 1)).eval (Env.ofMachine st3.data
      [(fbOf m0 + BitVec.ofNat 64 (32 + 8 * ((basisOf m0 j).size + t)), 8)]) =
      reg st3.data .r15 - BitVec.ofNat 64 1 from sub64 _ _, eval_lit, bv_beq_toNat,
    dec_toNat hr15 (by omega), BitVec.toNat_ofNat] at hpc4
  obtain ⟨hT, hF4⟩ := Arrays.pc_cond hpc4
  have hr14' : reg st4.data .r14 = fbOf m0 + BitVec.ofNat 64 (32 + 8 * (t + 1)) := by
    refine (hm5.regs .r14 _ rfl).trans ?_
    rw [eval_add, eval_lit, eval_reg, Env.ofMachine_regs,
      show st3.data.regs.get64 .r14 = _ from e3 .r14 (by simp), hI.r14, add8]
    congr 2
  have hr15' : (reg st4.data .r15).toNat = (basisOf m0 j).size - (t + 1) := by
    rw [show reg st4.data .r15 = reg st3.data .r15 - BitVec.ofNat 64 1 from
      (hm5.regs .r15 _ rfl).trans (sub64 _ _), dec_toNat hr15 (by omega)]
    omega
  by_cases hlast : t + 1 = (basisOf m0 j).size
  · -- `b8`: the basis doubled
    have hpc4' : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b8Offset) :=
      hF4 (by rw [Bool.not_eq_true, Bool.not_eq_false', decide_eq_true_eq]; omega)
    refine exec_at (hb8 hp) run_b8 (Env.wf_nil _) (by intro l h; cases h) hpc4' (match_nil _)
      fun st5 hm6 hpc5 ↦ ?_
    have hfr5 := hfr4.of_block (match_nil _) hm6 (Env.wf_nil _) rfl (after_eq run_b8 ▸ b8_keeps)
    have hd5 : st5.data.dmem = st4.data.dmem := hm6.dmem_eq (Env.wf_nil _) rfl
    have hsucc := basisOf_succ m0 hI.hj hI.lt
    have hsize : (basisOf m0 (j + 1)).size = 2 * (basisOf m0 j).size := by
      rw [hsucc, Array.size_append, Array.size_map]; omega
    have hbas5 : WordsAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 32) (basisOf m0 (j + 1)).toList := by
      rw [hd5, hsucc, Array.toList_append, NativeRustcVm.wordsAt_append, Array.length_toList,
        addr_add, Array.toList_map]
      refine ⟨hbas4, ?_⟩
      have := hnew4
      rwa [hlast, List.take_of_length_le (by rw [Array.length_toList])] at this
    have hrbp5 : reg st5.data .rbp = BitVec.ofNat 64 (2 * (basisOf m0 j).size) := by
      refine (hm6.regs .rbp _ rfl).trans ?_
      rw [eval_add, eval_reg, Env.ofMachine_regs, show st4.data.regs.get64 .rbp = _ from
        e4 .rbp (by simp), ofNat_toNat hI.rbp, ← BitVec.ofNat_add]
      congr 1
      omega
    have hrbx4 : reg st4.data .rbx = reg m0 .rdx := (e4 .rbx (by simp)).trans hI.rbx
    have hr145 : reg st5.data .r14 = reg m0 .rdx := (hm6.regs .r14 _ rfl).trans hrbx4
    have hspill5 : Spill m0 st5.data := ⟨hd5 ▸ hsp4.out, hd5 ▸ hsp4.cs⟩
    simp only [PcOk] at hpc5
    rw [gt_eval, eval_add, eval_reg, eval_reg, Env.ofMachine_regs, Env.ofMachine_regs,
      show st4.data.regs.get64 .rbx = _ from hrbx4, show st4.data.regs.get64 .rbp = _ from
        e4 .rbp (by simp), ofNat_toNat hI.rbp, ← BitVec.ofNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)] at hpc5
    obtain ⟨hT5, hF5⟩ := Arrays.pc_cond hpc5
    have hcnt : (reg m0 .rdx).toNat = cnt m0 := rfl
    by_cases hmore : 2 * (basisOf m0 j).size < cnt m0
    · refine .done _ (.inr (.inl ⟨(hT5 (by rw [decide_eq_true_eq]; omega)).trans
        (hp.label NativeRustcVmX64.Vm.NovelEval.label_3_at), hfr5, hspill5, by unfold EndAt; rw [hd5]; exact hed4, by have := hI.hj; omega,
        by omega, ?_, ?_, hr145, hbas5⟩))
      · refine (hm6.regs .r12 _ rfl).trans ?_
        rw [eval_add, eval_lit, eval_reg, Env.ofMachine_regs,
          show st4.data.regs.get64 .r12 = _ from e4 .r12 (by simp), hI.r12, add8]
        congr 2
      · rw [hrbp5, hsize, BitVec.toNat_ofNat]; omega
    · have hpc5' : st5.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b9Offset) := hF5 (by rw [decide_eq_true_eq]; omega)
      refine .done _ (.inr (.inr ⟨hpc5', hfr5, hspill5, ?_, hr145, ?_⟩))
      · rw [basisOf_final m0 (j := j + 1) (by have := hI.hj; omega) (by omega), hrbp5, hsize,
          BitVec.toNat_ofNat]; omega
      · rw [basisOf_final m0 (j := j + 1) (by have := hI.hj; omega) (by omega)]; exact hbas5
  · refine .done _ (.inl ⟨(hT (by rw [Bool.not_eq_true', decide_eq_false_iff_not]; omega)).trans (hp.label NativeRustcVmX64.Vm.NovelEval.label_5_at), hfr4, hsp4, hed4, hI.hj, hI.lt, by omega, ?_, ?_,
      ?_, ?_, hr14', hr15', hbas4, hnew4⟩)
    · exact (e4 .r12 (by simp)).trans hI.r12
    · rw [e4 .rbp (by simp)]; exact hI.rbp
    · exact (e4 .rbx (by simp)).trans hI.rbx
    · exact (e4 .r13 (by simp)).trans hI.r13

end

end NativeRustcVmX64.Whir.NovelEval
