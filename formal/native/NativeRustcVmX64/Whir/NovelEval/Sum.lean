module

public import NativeRustcVmX64.Whir.NovelEval.Inner
public import NativeRustcVmX64.Code.Vm.Kmul.Names

/-!
# `novel_eval`'s loops to the result (x86-64)

`doubling`: from the doubling loop's head after no value (`OInv 0`), the basis complete (`Mid`
at `b9`), by `Sym.loop` over both loops. `sumTurn`: a turn of the sum (`b11a` loads basis word
`t` and coefficient `t`, two `kmul`s, `b13` adds them). `sum`: from `Mid`, `b9` takes the
products' count; none (`b15`) or the sum's loop (`b10`, `sumTurn`), to `Done` at `b16`.
-/

namespace NativeRustcVmX64.Whir.NovelEval

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.NovelEval NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region WordAt WordsAt wordOf)
open NativeRustcVmX64.Field (midS frameS frameEnv)
open NativeRustcVmX64.Arrays (load8_eq wordAt_of_write eval_reg eval_lit eval_load eval_add
  eval_cmp_eq eval_not eval_test eval_min eval_shl_lit eval_xor apart_symm)

public section

theorem shl3 {L : Nat} (_h : L ≤ 64) : BitVec.ofNat 64 L <<< 3 = BitVec.ofNat 64 (8 * L) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem acc_zero (m0 : MachineData) : accOf m0 0 = 0 := novelAcc_zero _ _

variable [Host] {k : Nat}

/-- **The doubling loops**, from no value read to the complete basis. -/
theorem doubling (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 : MachineData} (hpre : NovelEvalPre m0) (hc : cnt m0 ≤ 64) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b4Offset)) (hI : OInv m0 0 st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b9Offset) ∧ Mid m0 s.data) st := by
  refine Sym.loop (fun n s ↦ (∃ j, n = (wn m0 - j) * 65 + 64 ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b4Offset) ∧
      OInv m0 j s.data) ∨ (∃ j t, n = (wn m0 - j) * 65 + (63 - t) ∧ t < 64 ∧
      s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b6Offset) ∧ IInv m0 j t s.data)) (fun n s h ↦ ?_) (.inl ⟨0, rfl, hpc, hI⟩)
  rcases h with ⟨j, rfl, hpc, hI⟩ | ⟨j, t, rfl, ht64, hpc, hI⟩
  · refine (outer hp hpre hpc hI).mono fun s' h ↦ ?_
    rcases h with h | ⟨hpc', hI'⟩
    · exact .inl h
    · exact .inr ⟨(wn m0 - j) * 65 + (63 - 0), by omega, .inr ⟨j, 0, rfl, by omega, hpc', hI'⟩⟩
  · have hsz := basis_le_32 m0 j hc hI.lt
    have hjw := hI.hj
    have hts := hI.ht
    refine (inner hp hkmul hpre hc hpc hI).mono fun s' h ↦ ?_
    rcases h with ⟨hpc', hI'⟩ | ⟨hpc', hI'⟩ | h
    · have := hI'.ht
      exact .inr ⟨(wn m0 - j) * 65 + (63 - (t + 1)), by omega,
        .inr ⟨j, t + 1, rfl, by omega, hpc', hI'⟩⟩
    · exact .inr ⟨(wn m0 - (j + 1)) * 65 + 64, by omega, .inl ⟨j + 1, rfl, hpc', hI'⟩⟩
    · exact .inl h

theorem hb11 (hp : Placed code k) : b11a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b11Offset) ∧
    b11b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b11Offset + b11a.length) := by
  have h := b11_in_code.trans hp.1 (by simp [b11])
  rw [← List.take_append_drop 6 b11] at h
  exact h.append
theorem hb12 (hp : Placed code k) : b12.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b12Offset) :=
  b12_in_code.trans hp.1 (by simp [b12])
theorem hb13 (hp : Placed code k) : b13.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b13Offset) :=
  b13_in_code.trans hp.1 (by simp [b13])
theorem hb14 (hp : Placed code k) : b14.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b14Offset) :=
  b14_in_code.trans hp.1 (by simp [b14])

/-- **A turn of the sum.** -/
theorem sumTurn (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 : MachineData} (hpre : NovelEvalPre m0) (hc : cnt m0 ≤ 64) {t : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b11Offset)) (hI : SInv m0 t st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b11Offset) ∧ SInv m0 (t + 1) s.data) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b16Offset) ∧ Done m0 s.data)) st := by
  obtain ⟨hS, hcs, hwh, hout, _⟩ := hpre
  have hF : 1104 ≤ novelEvalStack := by decide
  have hle : 1104 + kmulStack ≤ novelEvalStack := by decide
  have hS1 := hS.1
  have hS2 := hS.2.1
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hfr := hI.fr
  have hsl := slots_ok
  have ht := hI.ht
  have hL : lenOf m0 ≤ (basisOf m0 (wn m0)).size ∧ lenOf m0 ≤ cnt m0 :=
    ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩
  have hcnt : cnt m0 = (reg m0 .rdx).toNat := rfl
  have hc64 := Arrays.lt_of_offStack hcs.1.2 hcs.2
  have hblen : (basisOf m0 (wn m0)).size ≤ 64 := novelPre_size_le _ hc _
  have hlw : ∀ w : UInt64, (NativeRustcVm.wordBytes w).length = 8 := NativeRustcVm.length_wordBytes
  have hlb : ((basisOf m0 (wn m0)).toList.flatMap NativeRustcVm.wordBytes).length =
      8 * (basisOf m0 (wn m0)).size := by
    rw [NativeRustcVm.length_wordsBytes, Array.length_toList]
  have htb : t < (basisOf m0 (wn m0)).size := by omega
  have htc : t < (csOf m0).size := by rw [csOf_size]; omega
  have hcsw : WhirIn m0 (reg m0 .rsi) (16 * (reg m0 .rdx).toNat) novelEvalStack := hcs
  -- `b11a`: the loads
  have hrd0 : Readable st.data (fbOf m0) 32 :=
    Readable.keep (Readable.mono (m := m0) ⟨hfmap, hfnw⟩ (by omega)) hfr.kept
  have hrd1 : Readable st.data (fbOf m0 + BitVec.ofNat 64 (32 + 8 * t)) 8 :=
    Readable.keep (Readable.sub (m := m0) ⟨hfmap, hfnw⟩ (by omega)) hfr.kept
  have hrd2 : Readable st.data (reg m0 .rsi + BitVec.ofNat 64 (16 * t)) 16 :=
    Readable.keep (Readable.sub hcsw.1 (by omega)) hfr.kept
  have hfb : (fbOf m0).toNat = (rspOf m0).toNat - 1104 := hfe
  have hofs := hcsw.2
  have hnw2 := hcsw.1.2
  unfold OffStack Apart at hofs
  unfold NoWrap at hnw2
  rw [Arrays.stackBelow_toNat hS1] at hofs
  have h2t : (reg m0 .rsi + BitVec.ofNat 64 (16 * t)).toNat = (reg m0 .rsi).toNat + 16 * t :=
    toNat_add_ofNat _ _ (by omega)
  have h1t : (fbOf m0 + BitVec.ofNat 64 (32 + 8 * t)).toNat = (rspOf m0).toNat - 1104 + 32 + 8 * t :=
    by rw [toNat_add_ofNat _ _ (by omega), hfb]; omega
  have hwf : (Env.ofMachine st.data [(fbOf m0, 32), (fbOf m0 + BitVec.ofNat 64 (32 + 8 * t), 8),
      (reg m0 .rsi + BitVec.ofNat 64 (16 * t), 16)]).WF := by
    refine Env.wf_of ⟨⟨hrd0.1, hrd0.2⟩, ⟨hrd1.1, hrd1.2⟩, ⟨hrd2.1, hrd2.2⟩, trivial⟩ ?_
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons nofun .nil))
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> unfold Apart <;> simp only [h1t, h2t, hfb] <;> omega
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      subst he
      unfold Apart
      simp only [h1t, h2t]
      omega
  have hld24 : (Env.ofMachine st.data [(fbOf m0, 32), (fbOf m0 + BitVec.ofNat 64 (32 + 8 * t), 8),
      (reg m0 .rsi + BitVec.ofNat 64 (16 * t), 16)]).load 0 24 8 = reg m0 .rsi := by
    rw [load8_eq]
    exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt hI.sp.cs)
  have hm : Match (Env.ofMachine st.data [(fbOf m0, 32), (fbOf m0 + BitVec.ofNat 64 (32 + 8 * t), 8),
      (reg m0 .rsi + BitVec.ofNat 64 (16 * t), 16)]) sumS st.data :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hfr.rsp, trivial⟩ trivial trivial
      ⟨by
        show BinOp.apply .add .W64 (BinOp.apply .add .W64 (fbOf m0 + BitVec.ofInt 64 8)
          (reg st.data .r15)) (BitVec.ofNat 64 24) =
            fbOf m0 + BitVec.ofNat 64 (32 + 8 * t) + BitVec.ofInt 64 0
        rw [add64, add64, hI.r15, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add,
          addr_add, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
        congr 2
        omega,
       by
        show BinOp.apply .add .W64 (Env.load _ 0 24 8)
          (BinOp.apply .mul .W64 (reg st.data .r15) (BitVec.ofNat 64 2)) =
            reg m0 .rsi + BitVec.ofNat 64 (16 * t) + BitVec.ofInt 64 0
        rw [add64, mul64, hld24, hI.r15, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
          show BitVec.ofNat 64 (8 * t) * BitVec.ofNat 64 2 = BitVec.ofNat 64 (16 * t) by
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
            rw [Nat.mod_mul_mod]
            congr 1
            omega], trivial⟩
  have hk11 := (hb11 hp).1
  refine exec_at hk11 run_b11a hwf (by intro l h; cases h) hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hfr1 := hfr.of_block hm hm1 hwf rfl (after_eq run_b11a ▸ b11a_keeps)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have harg := hfr.get?_arg hS hcsw fun _ hr ↦ absurd hr List.not_mem_nil
  have h0 : UInt64.ofBitVec (reg st1.data .rsi) =
      wordOf m0.dmem (reg m0 .rsi + BitVec.ofNat 64 (16 * t)) := by
    show UInt64.ofBitVec (st1.data.regs.get64 .rsi) = _
    rw [hm1.regs .rsi _ rfl, eval_load, load8_eq, UInt64.ofBitVec_toBitVec]
    show wordOf st.data.dmem (reg m0 .rsi + BitVec.ofNat 64 (16 * t) + BitVec.ofNat 64 0) = _
    rw [NativeRustcVm.addr_add_zero]
    refine NativeRustcVm.wordOf_congr fun i hi ↦ ?_
    rw [addr_add]
    exact harg _ (by omega)
  have h1 : UInt64.ofBitVec (reg st1.data .r12) =
      wordOf m0.dmem (reg m0 .rsi + BitVec.ofNat 64 (16 * t) + 8#64) := by
    show UInt64.ofBitVec (st1.data.regs.get64 .r12) = _
    rw [hm1.regs .r12 _ rfl, eval_load, load8_eq, UInt64.ofBitVec_toBitVec]
    show wordOf st.data.dmem (reg m0 .rsi + BitVec.ofNat 64 (16 * t) + BitVec.ofNat 64 8) = _
    refine NativeRustcVm.wordOf_congr fun i hi ↦ ?_
    rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, addr_add, addr_add]
    exact harg _ (by omega)
  have hcoef : ((csOf m0)[t]'htc) = ⟨UInt64.ofBitVec (reg st1.data .rsi),
      UInt64.ofBitVec (reg st1.data .r12)⟩ := by
    rw [csOf_get, h0, h1]
    rfl
  have hbt : reg st1.data .r13 = ((basisOf m0 (wn m0))[t]'htb).toBitVec := by
    refine (hm1.regs .r13 _ rfl).trans ?_
    rw [eval_load, load8_eq]
    have h := NativeRustcVm.WordsAt.getElem hI.basis (i := t) (by rw [Array.length_toList]; omega)
    rw [addr_add, Array.getElem_toList] at h
    show (wordOf st.data.dmem (fbOf m0 + BitVec.ofNat 64 (32 + 8 * t) + BitVec.ofNat 64 0)).toBitVec = _
    rw [NativeRustcVm.addr_add_zero, NativeRustcVm.wordOf_of_wordAt h]
  have hrdi1 : reg st1.data .rdi = reg st1.data .r13 :=
    (hm1.regs .rdi _ rfl).trans (hm1.regs .r13 _ rfl).symm
  have e1 : ∀ r ∈ [Reg64.rbx, .r14, .r15], reg st1.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Match.reg_eq hm hm1 rfl rfl
  -- `b11b`: `kmul(b, c0)`
  have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b11Offset + b11a.length) := hpc1
  have hwf2 := hfr1.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b12Offset)).toBitVec) hS hF
  refine exec_at (hb11 hp).2 run_b11b hwf2 (fun _ _ ↦ rfl) hpc1' hfr1.mid_match
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hk2, hsp2, hw2⟩ := after_eq run_b11b ▸ b11b_call
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
  have e3 : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], reg st3.data r = reg st1.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact (hsv3.1 _ rfl).trans (Match.reg_eq hfr1.mid_match hm2 rfl rfl)
  have hp0 : reg st3.data .rax = (kmul ((basisOf m0 (wn m0))[t]'htb) ((csOf m0)[t]'htc).c0).toBitVec := by
    rw [hax3, show reg st2.data .rdi = reg st1.data .rdi from
        Match.reg_eq hfr1.mid_match hm2 rfl rfl,
      show reg st2.data .rsi = reg st1.data .rsi from Match.reg_eq hfr1.mid_match hm2 rfl rfl,
      hrdi1, hbt, hcoef, UInt64.ofBitVec_toBitVec]
  -- `b12`: `kmul(b, c1)`
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b12Offset) := hpc3
  have hwf4 := hfr3.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b13Offset)).toBitVec) hS hF
  refine exec_at (hb12 hp) run_b12 hwf4 (fun _ _ ↦ rfl) hpc3' hfr3.mid_match fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hk4, hsp4, hw4⟩ := after_eq run_b12 ▸ b12_call
  have hrsp4 := rsp_call hm4 hsp4
  refine Frame.call hkmul hfr3 hS hle (L := 1056) (by decide) hsl out_nil hwf4 hfr3.mid_match hm4
    hpc4 hk4 hsp4 (fun w hw ↦ ⟨(hw4 w hw).1, by have := (hw4 w hw).2; omega⟩)
    (stackOk_callee hS (fun p h ↦ hm4.kept hwf4 p (hfr3.kept p h)) hrsp4 hle)
    (fun m' ⟨_, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inr (.inr h))⟩)
    fun st5 hpc5 hfr5 ⟨hax5, hso5, hsv5⟩ ↦ ?_
  have k5 : ∀ {o : Nat} {bs : List UInt8}, 8 ≤ o → o + bs.length ≤ 1112 →
      NativeRustcVm.BytesAt st3.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs :=
    fun h8 hlen h ↦ keep_call hm4 hwf4 rfl rfl hw4 hS hrsp4 hle hso5 h8 hlen h
  have hp1 : reg st5.data .rax = (kmul ((basisOf m0 (wn m0))[t]'htb) ((csOf m0)[t]'htc).c1).toBitVec := by
    rw [hax5, show reg st4.data .rdi = reg st3.data .r13 from hm4.regs .rdi _ rfl,
      show reg st4.data .rsi = reg st3.data .r12 from hm4.regs .rsi _ rfl,
      e3 .r13 (by simp), e3 .r12 (by simp), hbt, hcoef, UInt64.ofBitVec_toBitVec]
  have hrbp5 : reg st5.data .rbp = (kmul ((basisOf m0 (wn m0))[t]'htb) ((csOf m0)[t]'htc).c0).toBitVec :=
    (hsv5.1 .rbp rfl).trans ((hm4.regs .rbp _ rfl).trans hp0)
  have e5 : ∀ r ∈ [Reg64.rbx, .r14, .r15], reg st5.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (hsv5.1 _ rfl).trans ((Match.reg_eq hfr3.mid_match hm4 rfl rfl).trans
        ((e3 _ (by simp)).trans (e1 _ (by simp))))
  -- `b13`: the sum, the count
  have hpc5' : st5.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b13Offset) := hpc5
  have hwf6 := hfr5.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb13 hp) run_b13 hwf6 (by intro l h; cases h) hpc5' hfr5.mid_match
    fun st6 hm6 hpc6 ↦ ?_
  have hfr6 := hfr5.of_block hfr5.mid_match hm6 hwf6 rfl (after_eq run_b13 ▸ b13_keeps)
  have hd6 : st6.data.dmem = st5.data.dmem := hm6.dmem_eq hwf6 rfl
  have kk : ∀ {o : Nat} {bs : List UInt8}, 8 ≤ o → o + bs.length ≤ 1112 →
      NativeRustcVm.BytesAt st.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st6.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs :=
    fun h8 hlen h ↦ hd6 ▸ k5 h8 hlen (k3 h8 hlen h)
  have hsp6 : Spill m0 st6.data :=
    ⟨kk (by omega) (by rw [hlw]; omega) hI.sp.out, kk (by omega) (by rw [hlw]; omega) hI.sp.cs⟩
  have hlen6 := kk (by omega) (by rw [hlw]; omega) hI.len
  have hbas6 := kk (by omega) (by rw [hlb]; omega) hI.basis
  have hacc : accOf m0 (t + 1) = ⟨(accOf m0 t).c0 ^^^ kmul ((basisOf m0 (wn m0))[t]'htb)
      ((csOf m0)[t]'htc).c0, (accOf m0 t).c1 ^^^ kmul ((basisOf m0 (wn m0))[t]'htb)
      ((csOf m0)[t]'htc).c1⟩ := accOf_succ m0 ht
  have hr14 : reg st6.data .r14 = (accOf m0 (t + 1)).c0.toBitVec := by
    refine (hm6.regs .r14 _ rfl).trans ?_
    rw [eval_xor, eval_reg, eval_reg, Env.ofMachine_regs, Env.ofMachine_regs,
      show st5.data.regs.get64 .r14 = _ from (e5 .r14 (by simp)).trans hI.r14,
      show st5.data.regs.get64 .rbp = _ from hrbp5, hacc, UInt64.toBitVec_xor]
  have hrbx : reg st6.data .rbx = (accOf m0 (t + 1)).c1.toBitVec := by
    refine (hm6.regs .rbx _ rfl).trans ?_
    rw [eval_xor, eval_reg, eval_reg, Env.ofMachine_regs, Env.ofMachine_regs,
      show st5.data.regs.get64 .rbx = _ from (e5 .rbx (by simp)).trans hI.rbx,
      show st5.data.regs.get64 .rax = _ from hp1, hacc, UInt64.toBitVec_xor]
  have hr15 : reg st6.data .r15 = BitVec.ofNat 64 (8 * (t + 1)) := by
    refine (hm6.regs .r15 _ rfl).trans ?_
    rw [eval_add, eval_lit, eval_reg, Env.ofMachine_regs,
      show st5.data.regs.get64 .r15 = _ from (e5 .r15 (by simp)).trans hI.r15, ← BitVec.ofNat_add]
    congr 1
    omega
  simp only [PcOk] at hpc6
  rw [eval_not, eval_cmp_eq, eval_load, eval_add, eval_lit, eval_reg, Env.ofMachine_regs,
    show st5.data.regs.get64 .r15 = _ from (e5 .r15 (by simp)).trans hI.r15, load8_eq,
    show (frameEnv m0 st5.data 1104 (fun _ ↦ 0) 0).base 0 = fbOf m0 from rfl, Env.ofMachine_mem0,
    NativeRustcVm.wordOf_of_wordAt (k5 (by omega) (by rw [hlw]; omega)
      (k3 (by omega) (by rw [hlw]; omega) hI.len)), ← BitVec.ofNat_add,
    show (UInt64.ofNat (8 * lenOf m0)).toBitVec = BitVec.ofNat 64 (8 * lenOf m0) from rfl,
    ofNat_beq (by omega) (by omega)] at hpc6
  obtain ⟨hT, hF6⟩ := Arrays.pc_cond hpc6
  by_cases hlast : t + 1 = lenOf m0
  · have hpc6' : st6.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b14Offset) :=
      hF6 (by rw [Bool.not_eq_true, Bool.not_eq_false', decide_eq_true_eq]; omega)
    refine exec_at (hb14 hp) run_b14 (Env.wf_nil _) (by intro l h; cases h) hpc6' (match_nil _)
      fun st7 hm7 hpc7 ↦ .done _ (.inr ⟨?_, ?_⟩)
    · simp only [PcOk] at hpc7
      exact hpc7.trans (hp.label NativeRustcVmX64.Vm.NovelEval.label_11_at)
    have hd7 : st7.data.dmem = st6.data.dmem := hm7.dmem_eq (Env.wf_nil _) rfl
    refine ⟨hfr6.of_block (match_nil _) hm7 (Env.wf_nil _) rfl (after_eq run_b14 ▸ b14_keeps),
      ⟨hd7 ▸ hsp6.out, hd7 ▸ hsp6.cs⟩, ?_, ?_⟩
    · rw [← hlast]; exact (Match.reg_eq (match_nil _) hm7 rfl rfl).trans hr14
    · rw [← hlast]; exact (Match.reg_eq (match_nil _) hm7 rfl rfl).trans hrbx
  · exact .done _ (.inl ⟨(hT (by rw [Bool.not_eq_true', decide_eq_false_iff_not]; omega)).trans
      (hp.label NativeRustcVmX64.Vm.NovelEval.label_10_at), hfr6, hsp6, hlen6, by omega, hr15, hr14, hrbx, hbas6⟩)

end

end NativeRustcVmX64.Whir.NovelEval
