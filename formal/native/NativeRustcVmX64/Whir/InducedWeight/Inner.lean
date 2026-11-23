module

public import NativeRustcVmX64.Whir.InducedWeight.Entry
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.Kmul.Names

/-!
# `induced_weight`'s product loop (x86-64)

A turn: `inner_a` from the head `b10` (`IInv j i`): `b10a` spills the product's high word, `b10b`
loads the point's element `i` and `What_i`, `b10c` calls `kmul((1 ⊕ What_i), r₀)`, `b11`
`kmul((1 ⊕ What_i), r₁)` (`AtB12`); `inner_b`: `b12` multiplies the product by the factor
(`EW::mul`), `b13` counts; after the last, `b14` goes to the sum (`Acc`).
-/

namespace NativeRustcVmX64.Whir.InducedWeight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.InducedWeight NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region InAny WordAt WordsAt wordOf ewOf BufWordsAt)
open NativeRustcVmX64.Field (midS frameS frameEnv)
open NativeRustcVmX64.Arrays (stackOk_mono load8_eq wordAt_of_write eval_reg eval_lit eval_load
  eval_add eval_xor eval_not eval_cmp_eq apart_symm keepsRegs freeRegs)

public section

/-- Element `i` of an argument slice, in a body. -/
theorem slice_get {m0 st : MachineData} (hfr : Fr m0 st) (hS : StackOk m0 inducedWeightStack)
    {a n : BitVec 64} (h : SliceOk m0 a n inducedWeightStack) {i : Nat} (hi : i < n.toNat) :
    ewOf st.dmem (a + BitVec.ofNat 64 (16 * i)) = (slice m0 a n)[i]'(by simpa [slice]) := by
  simp only [slice, List.getElem_toArray, NativeRustcVm.getElem_ewsOf]
  refine NativeRustcVm.ewOf_congr fun b hb ↦ ?_
  rw [addr_add]
  exact hfr.get?_arg hS h (fun r hr ↦ absurd hr List.not_mem_nil) _ (by omega)

/-- **Frame bytes from 8 kept by a block writing the calls' slot and its callee.** -/
theorem keep_call8 [Labels] {m0 : MachineData} {env : Env} {S : SState} {d1 d2 : MachineData}
    {N : Nat} (hS : StackOk m0 inducedWeightStack) (hm : Match env S d1) (hwf : env.WF)
    (hb : env.regions[0]? = some (fbOf m0, 1176))
    (hsig : S.mem.map wsig = [(0, 0, 8)]) (hsp : rspOf d1 = fbOf m0)
    (hle : 1168 + N ≤ inducedWeightStack)
    (hs : SameOutside d1.dmem d2.dmem (InRange (stackBelow d1 N) N)) :
    FKeep m0 env.mem0 d2.dmem 8 1176 :=
  (fkeep_block hm hwf hb le_rfl (hall_of hsig (by decide))).trans
    (fkeep_stack hS hsp hle hs le_rfl)

/-- **At `b12`**: query `j`'s product after `i` factors, its high word spilled at 96, the two
`kmul`s of factor `i` done. -/
structure AtB12 (m0 : MachineData) (j i : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  sp : Spills m0 st
  lp : Loop m0 j st
  hj : j < cntOf m0
  mu : muOf m0 ≤ stackCap
  what : BufWordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 104) rootCap (whatOf m0 j).toList
  len : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 16) (8 * lenOf m0 j).toUInt64
  hi : i < lenOf m0 j
  w96 : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 96) (prodOf m0 j i).c1
  r12 : reg st .r12 = (prodOf m0 j i).c0.toBitVec
  r14 : reg st .r14 = stackArg m0 0
  r15 : reg st .r15 = BitVec.ofNat 64 (8 * i)
  rbp : reg st .rbp =
    (kmul ((whatOf m0 j).getD i 0 ^^^ 1) ((ptOf m0).getD i 0).c0).toBitVec
  rax : reg st .rax =
    (kmul ((whatOf m0 j).getD i 0 ^^^ 1) ((ptOf m0).getD i 0).c1).toBitVec

variable [Host] {k : Nat}

theorem hb10 (hp : Placed code k) : b10a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b10Offset) ∧
    b10b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b10Offset + b10a.length) ∧ b10c.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b10Offset + b10a.length + b10b.length) := by
  have h := b10_in_code.trans hp.1 (by simp [b10])
  rw [← List.take_append_drop 2 b10, ← List.take_append_drop 6 (b10.drop 2)] at h
  exact ⟨h.append.1, h.append.2.append.1, h.append.2.append.2⟩
theorem hb11 (hp : Placed code k) : b11.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b11Offset) :=
  b11_in_code.trans hp.1 (by simp [b11])
theorem hb12 (hp : Placed code k) : b12.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b12Offset) :=
  b12_in_code.trans hp.1 (by simp [b12])
theorem hb13 (hp : Placed code k) : b13.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b13Offset) :=
  b13_in_code.trans hp.1 (by simp [b13])
theorem hb14 (hp : Placed code k) : b14.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b14Offset) :=
  b14_in_code.trans hp.1 (by simp [b14])

/-- **A turn of the product loop, to `b12`.** -/
theorem inner_a (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 : MachineData} (hpre : InducedWeightPre m0) {j i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b10Offset)) (hI : IInv m0 j i st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b12Offset) ∧ AtB12 m0 j i s.data) st := by
  obtain ⟨hS, -, -, -, hpin, -, -⟩ := hpre
  obtain ⟨hF, -, -, hle_k, -, -⟩ := stack_le
  have hsl := slots_ok
  have hS1 := hS.1
  have hS2 := hS.2.1
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hfr := hI.fr
  have hi := hI.hi
  have hip : i < (stackArg m0 1).toNat := by
    unfold lenOf at hi
    rw [ptOf_size] at hi
    omega
  have hiw : i < (whatOf m0 j).size := by
    have := Nat.min_le_right (ptOf m0).size (whatOf m0 j).size; unfold lenOf at hi; omega
  have hw31 : (whatOf m0 j).toList.length ≤ 31 := hI.what.1
  have hi31 : i < 31 := by simp at hw31; omega
  -- `b10a`: the product's high word
  have hwf1 := hfr.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb10 hp).1 run_b10a hwf1 (by intro l h; cases h) hpc hfr.mid_match
    fun s1 hm1 hpc1 ↦ ?_
  obtain ⟨hk1, hsig1, hv96⟩ := after_eq run_b10a ▸ b10a_write
  have hfr1 := fr_write hS hfr hfr.mid_match hm1 hwf1 rfl hk1 rfl (by omega)
    (hw_of hsig1 (by decide))
  have k1a := fkeep_block hm1 hwf1 (m0 := m0) rfl (lo := 8) (hi := 96) (by omega)
    (hall_of hsig1 (by decide))
  have k1b := fkeep_block hm1 hwf1 (m0 := m0) rfl (lo := 104) (hi := 1176) (by omega)
    (hall_of hsig1 (by decide))
  have w96 : WordAt s1.data.dmem (fbOf m0 + BitVec.ofNat 64 96) (prodOf m0 j i).c1 := by
    have := wordAt_of_write hm1 (r := 0) (o := 96) rfl (by decide) (v := .reg .r12) hv96
    rwa [eval_reg, Env.ofMachine_regs, show st.data.regs.get64 .r12 = _ from hI.r12] at this
  have e1 : ∀ r ∈ [Reg64.rbx, .r14, .r15], reg s1.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Match.reg_eq hfr.mid_match hm1 rfl rfl
  -- `b10b`: the point's element, `What_i`
  let pa := stackArg m0 0 + BitVec.ofNat 64 (16 * i)
  let wa := fbOf m0 + BitVec.ofNat 64 (112 + 8 * i)
  have hprd : Readable s1.data pa 16 := hfr1.readable (Readable.sub hpin.1 (by omega))
  have hwrd : Readable s1.data wa 8 :=
    hfr1.readable (Readable.sub (m := m0) ⟨hfmap, hfnw⟩ (by omega))
  have hap : Apart pa 16 wa 8 := by
    have h0 := apart_frame' hS hF hpin.2
    have hnw : (stackArg m0 0).toNat + 16 * (stackArg m0 1).toNat ≤ 2 ^ 64 := hpin.1.2
    have hwa : wa.toNat = (rspOf m0).toNat - 1168 + (112 + 8 * i) := fb_toNat hS hF (by omega)
    unfold Apart at h0 ⊢
    rw [hfe] at h0
    rw [toNat_add_ofNat _ _ (by omega), hwa]
    omega
  let env2 := Env.ofMachine s1.data [(pa, 16), (wa, 8)]
  have hwf2 : env2.WF :=
    Env.wf_of ⟨⟨hprd.1, hprd.2⟩, ⟨hwrd.1, hwrd.2⟩, trivial⟩ (List.pairwise_pair.mpr hap)
  have hm2 : Match env2 pS s1.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ trivial trivial trivial
      ⟨by
        show BinOp.apply .add .W64 (reg s1.data .r14)
          (BinOp.apply .mul .W64 (reg s1.data .r15) (BitVec.ofNat 64 2)) =
            stackArg m0 0 + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 0
        rw [add64, mul64, e1 .r14 (by simp), e1 .r15 (by simp), hI.r14, hI.r15, mul_lit,
          show 8 * i * 2 = 16 * i by omega, show BitVec.ofInt 64 0 = 0#64 from rfl,
          BitVec.add_zero],
       by
        show BinOp.apply .add .W64 (BinOp.apply .add .W64 (reg s1.data .rsp) (reg s1.data .r15))
          (BitVec.ofNat 64 104) = stackBelow m0 1168 + BitVec.ofNat 64 (112 + 8 * i) +
            BitVec.ofInt 64 0
        rw [add64, add64, e1 .r15 (by simp), hI.r15, show reg s1.data .rsp = _ from hfr1.rsp,
          show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add, addr_add,
          show 8 + (8 * i + 104) = 112 + 8 * i by omega, show BitVec.ofInt 64 0 = 0#64 from rfl,
          BitVec.add_zero], trivial⟩
  have hpc1' : s1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b10Offset + b10a.length) := hpc1
  refine exec_at (hb10 hp).2.1 run_b10b hwf2 (by intro l h; cases h) hpc1' hm2
    fun s2 hm2' hpc2 ↦ ?_
  have hfr2 := hfr1.of_block hm2 hm2' hwf2 rfl (after_eq run_b10b ▸ b10b_keeps)
  have hd2 : s2.data.dmem = s1.data.dmem := hm2'.dmem_eq hwf2 rfl
  let c := (ptOf m0)[i]'(by rw [ptOf_size]; exact hip)
  let v := (whatOf m0 j)[i]'hiw
  have hc : ewOf s1.data.dmem pa = c := slice_get hfr1 hS hpin hip
  have hwhat1 : BufWordsAt s1.data.dmem (fbOf m0 + BitVec.ofNat 64 104) 31 (whatOf m0 j).toList :=
    bufWords_keep hI.what k1b (by omega) (by omega)
  have hv : wordOf s1.data.dmem wa = v := by
    have := NativeRustcVm.wordsAt_getElem hwhat1.2.2 (i := i) (by simpa using hiw)
    rw [addr_add, addr_add, show 104 + (8 + 8 * i) = 112 + 8 * i by omega,
      Array.getElem_toList] at this
    exact NativeRustcVm.wordOf_of_wordAt this
  have lv : env2.load 1 0 8 = v.toBitVec := by
    rw [load8_eq, show env2.base 1 = wa from rfl, NativeRustcVm.addr_add_zero, ← hv]; rfl
  have lc0 : env2.load 0 0 8 = c.c0.toBitVec := by
    rw [load8_eq, show env2.base 0 = pa from rfl, NativeRustcVm.addr_add_zero, ← hc]; rfl
  have lc1 : env2.load 0 8 8 = c.c1.toBitVec := by
    rw [load8_eq, show env2.base 0 = pa from rfl, ← hc]; rfl
  have f2rdi : reg s2.data .rdi = (v ^^^ 1).toBitVec := by
    refine (hm2'.regs .rdi _ rfl).trans ?_
    rw [eval_xor, eval_load, lv]; rfl
  have f2r13 : reg s2.data .r13 = (v ^^^ 1).toBitVec := by
    refine (hm2'.regs .r13 _ rfl).trans ?_
    rw [eval_xor, eval_load, lv]; rfl
  have f2rsi : reg s2.data .rsi = c.c0.toBitVec := (hm2'.regs .rsi _ rfl).trans lc0
  have f2rbx : reg s2.data .rbx = c.c1.toBitVec := (hm2'.regs .rbx _ rfl).trans lc1
  have f2r12 : reg s2.data .r12 = (prodOf m0 j i).c0.toBitVec :=
    (hm2'.regs .r12 _ rfl).trans ((e1 .rbx (by simp)).trans hI.rbx)
  have f2r14 : reg s2.data .r14 = stackArg m0 0 :=
    (Match.reg_eq hm2 hm2' rfl rfl).trans ((e1 .r14 (by simp)).trans hI.r14)
  have f2r15 : reg s2.data .r15 = BitVec.ofNat 64 (8 * i) :=
    (Match.reg_eq hm2 hm2' rfl rfl).trans ((e1 .r15 (by simp)).trans hI.r15)
  -- `b10c`: `kmul((1 ⊕ v), r₀)`
  have hpc2' : s2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b10Offset + b10a.length + b10b.length) := hpc2
  have hwf3 := hfr2.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b11Offset)).toBitVec) hS hF
  refine exec_at (hb10 hp).2.2 run_b10c hwf3 (fun _ _ ↦ rfl) hpc2' hfr2.mid_match
    fun s3 hm3 hpc3 ↦ ?_
  obtain ⟨hk3, hsig3⟩ := after_eq run_b10c ▸ b10c_call
  have hrsp3 := rsp_call hm3 rfl
  refine Frame.call hkmul hfr2 hS hle_k (L := 1120) (by omega) hsl out_nil hwf3 hfr2.mid_match hm3
    hpc3 hk3 rfl (hw_of hsig3 (by decide))
    (stackOk_callee hS (fun p h ↦ hm3.kept hwf3 p (hfr2.kept p h)) hrsp3 hle_k)
    (fun m' ⟨_, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inr (.inr h))⟩)
    fun s4 hpc4 hfr4 ⟨hax4, hso4, hsv4⟩ ↦ ?_
  have k4 := keep_call8 hS hm3 hwf3 rfl hsig3 hrsp3 hle_k hso4
  have e4 : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], reg s4.data r = reg s2.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact (hsv4.1 _ rfl).trans (Match.reg_eq hfr2.mid_match hm3 rfl rfl)
  have hk0 : reg s4.data .rax = (kmul (v ^^^ 1) c.c0).toBitVec := by
    rw [hax4, show reg s3.data .rdi = reg s2.data .rdi from Match.reg_eq hfr2.mid_match hm3 rfl rfl,
      show reg s3.data .rsi = reg s2.data .rsi from Match.reg_eq hfr2.mid_match hm3 rfl rfl,
      f2rdi, f2rsi, UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec]
  -- `b11`: `kmul((1 ⊕ v), r₁)`
  have hpc4' : s4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b11Offset) := hpc4
  have hwf5 := hfr4.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b12Offset)).toBitVec) hS hF
  refine exec_at (hb11 hp) run_b11 hwf5 (fun _ _ ↦ rfl) hpc4' hfr4.mid_match fun s5 hm5 hpc5 ↦ ?_
  obtain ⟨hk5, hsig5⟩ := after_eq run_b11 ▸ b11_call
  have hrsp5 := rsp_call hm5 rfl
  refine Frame.call hkmul hfr4 hS hle_k (L := 1120) (by omega) hsl out_nil hwf5 hfr4.mid_match hm5
    hpc5 hk5 rfl (hw_of hsig5 (by decide))
    (stackOk_callee hS (fun p h ↦ hm5.kept hwf5 p (hfr4.kept p h)) hrsp5 hle_k)
    (fun m' ⟨_, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inr (.inr h))⟩)
    fun s6 hpc6 hfr6 ⟨hax6, hso6, hsv6⟩ ↦ ?_
  have k6 := keep_call8 hS hm5 hwf5 rfl hsig5 hrsp5 hle_k hso6
  have e6 : ∀ r ∈ [Reg64.r12, .r14, .r15], reg s6.data r = reg s2.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (hsv6.1 _ rfl).trans ((Match.reg_eq hfr4.mid_match hm5 rfl rfl).trans (e4 _ (by simp)))
  have hk1 : reg s6.data .rax = (kmul (v ^^^ 1) c.c1).toBitVec := by
    rw [hax6, show reg s5.data .rdi = reg s4.data .r13 from hm5.regs .rdi _ rfl,
      show reg s5.data .rsi = reg s4.data .rbx from hm5.regs .rsi _ rfl,
      e4 .r13 (by simp), e4 .rbx (by simp), f2r13, f2rbx, UInt64.ofBitVec_toBitVec,
      UInt64.ofBitVec_toBitVec]
  have hrbp6 : reg s6.data .rbp = (kmul (v ^^^ 1) c.c0).toBitVec :=
    (hsv6.1 .rbp rfl).trans ((hm5.regs .rbp _ rfl).trans hk0)
  have hkk : FKeep m0 s1.data.dmem s6.data.dmem 8 1176 :=
    ((FKeep.of_eq hd2).trans k4).trans k6
  have hk8 : FKeep m0 st.data.dmem s6.data.dmem 8 96 :=
    k1a.trans (hkk.mono le_rfl (by omega))
  have hk104 : FKeep m0 st.data.dmem s6.data.dmem 104 1176 :=
    k1b.trans (hkk.mono (by omega) le_rfl)
  have hgc : (ptOf m0).getD i 0 = c := getD_eq _ _ (by rw [ptOf_size]; exact hip)
  have hgv : (whatOf m0 j).getD i 0 = v := getD_eq _ _ hiw
  have hpc6' : s6.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b12Offset) := hpc6
  refine .done _ ⟨hpc6', hfr6, hI.sp.mono (hk8.mono (by omega) (by omega))
    (hk104.mono (by omega) (by omega)), hI.lp.mono (hk8.mono (by omega) le_rfl), hI.hj, hI.mu,
    bufWords_keep hI.what hk104 le_rfl (by omega), word_keep hI.len hk8 (by omega) (by omega),
    hi, word_keep w96 hkk (by omega) (by omega), (e6 .r12 (by simp)).trans f2r12,
    (e6 .r14 (by simp)).trans f2r14, (e6 .r15 (by simp)).trans f2r15, ?_, ?_⟩
  · rw [hgv, hgc]; exact hrbp6
  · rw [hgv, hgc]; exact hk1

/-- **A turn of the product loop, from `b12`**: the product times the factor; the next factor or
the sum. -/
theorem inner_b (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : InducedWeightPre m0) {j i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b12Offset)) (hA : AtB12 m0 j i st.data) :
    Eventually (step1 Host.exe)
      (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b10Offset) ∧ IInv m0 j (i + 1) s.data) ∨
        (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b6Offset) ∧ Acc m0 j s.data)) st := by
  obtain ⟨hS, -, -, -, -, -, -⟩ := hpre
  obtain ⟨hF, -, -, -, hle_m, -⟩ := stack_le
  have hsl := slots_ok
  have hfr := hA.fr
  have hi := hA.hi
  have hip : i < (ptOf m0).size := by unfold lenOf at hi; omega
  have hiw : i < (whatOf m0 j).size := by unfold lenOf at hi; omega
  have hw31 : (whatOf m0 j).toList.length ≤ 31 := hA.what.1
  have hi31 : i < 31 := by simp at hw31; omega
  have hlen31 : lenOf m0 j ≤ 31 := by
    have := Nat.min_le_right (ptOf m0).size (whatOf m0 j).size; simp at hw31; unfold lenOf; omega
  -- `b12`: `EW::mul`
  have hwf1 := hfr.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b13Offset)).toBitVec) hS hF
  refine exec_at (hb12 hp) run_b12 hwf1 (fun _ _ ↦ rfl) hpc hfr.mid_match fun s1 hm1 hpc1 ↦ ?_
  obtain ⟨hk1, hsig1⟩ := after_eq run_b12 ▸ b12_call
  have hrsp1 := rsp_call hm1 rfl
  refine Frame.call hmul hfr hS hle_m (L := 1120) (by omega) hsl out_nil hwf1 hfr.mid_match hm1
    hpc1 hk1 rfl (hw_of hsig1 (by decide))
    (stackOk_callee hS (fun p h ↦ hm1.kept hwf1 p (hfr.kept p h)) hrsp1 hle_m)
    (fun m' ⟨_, _, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inr (.inr h))⟩)
    fun s2 hpc2 hfr2 ⟨hp0, hp1, hso2, hsv2⟩ ↦ ?_
  have k2 := keep_call8 hS hm1 hwf1 rfl hsig1 hrsp1 hle_m hso2
  have hfac : (⟨UInt64.ofBitVec (reg s1.data .rdx), UInt64.ofBitVec (reg s1.data .rcx)⟩ : EW) =
      indFactor ((ptOf m0).getD i 0) ((whatOf m0 j).getD i 0) := by
    rw [indFactor_eq, UInt64.xor_comm 1]
    have h3 : reg s1.data .rcx = reg st.data .rax := hm1.regs .rcx _ rfl
    have h2 : reg s1.data .rdx = reg st.data .rbp ^^^ BitVec.ofNat 64 1 :=
      (hm1.regs .rdx _ rfl).trans (eval_xor _ _)
    rw [h2, h3, hA.rbp, hA.rax]
    rfl
  have hprod : (⟨UInt64.ofBitVec (reg s1.data .rdi), UInt64.ofBitVec (reg s1.data .rsi)⟩ : EW) =
      prodOf m0 j i := by
    have h0 : reg s1.data .rdi = (prodOf m0 j i).c0.toBitVec := (hm1.regs .rdi _ rfl).trans hA.r12
    have h1 : reg s1.data .rsi = (prodOf m0 j i).c1.toBitVec := by
      refine (hm1.regs .rsi _ rfl).trans ?_
      rw [eval_load, load8_eq]
      exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt hA.w96)
    rw [h0, h1]
  rw [hprod, hfac, getD_eq (ptOf m0) 0 hip, getD_eq (whatOf m0 j) 0 hiw,
    ← prodOf_succ m0 hi] at hp0 hp1
  -- `b13`: count
  have hpc2' : s2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b13Offset) := hpc2
  have hwf3 := hfr2.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb13 hp) run_b13 hwf3 (by intro l h; cases h) hpc2' hfr2.mid_match
    fun s3 hm3 hpc3 ↦ ?_
  have hfr3 := hfr2.of_block hfr2.mid_match hm3 hwf3 rfl (after_eq run_b13 ▸ b13_keeps)
  have hd3 : s3.data.dmem = s2.data.dmem := hm3.dmem_eq hwf3 rfl
  have hk : FKeep m0 st.data.dmem s3.data.dmem 8 1176 := k2.trans (FKeep.of_eq hd3)
  have e2 : ∀ r ∈ [Reg64.r14, .r15], reg s2.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      exact (hsv2.1 _ rfl).trans (Match.reg_eq hfr.mid_match hm1 rfl rfl)
  have hr15 : reg s3.data .r15 = BitVec.ofNat 64 (8 * (i + 1)) := by
    refine (hm3.regs .r15 _ rfl).trans ?_
    rw [eval_add, eval_lit, eval_reg, Env.ofMachine_regs,
      show s2.data.regs.get64 .r15 = _ from (e2 .r15 (by simp)).trans hA.r15, ← BitVec.ofNat_add]
    congr 1
    omega
  have hrbx : reg s3.data .rbx = (prodOf m0 j (i + 1)).c0.toBitVec := (hm3.regs .rbx _ rfl).trans hp0
  have hr12 : reg s3.data .r12 = (prodOf m0 j (i + 1)).c1.toBitVec := (hm3.regs .r12 _ rfl).trans hp1
  have hr14 : reg s3.data .r14 = stackArg m0 0 :=
    (Match.reg_eq hfr2.mid_match hm3 rfl rfl).trans ((e2 .r14 (by simp)).trans hA.r14)
  have hsp3 : Spills m0 s3.data := hA.sp.mono (hk.mono (by omega) (by omega))
    (hk.mono (by omega) (by omega))
  have hlp3 : Loop m0 j s3.data := hA.lp.mono (hk.mono (by omega) (by omega))
  have hlen2 : WordAt s2.data.dmem (fbOf m0 + BitVec.ofNat 64 16) (8 * lenOf m0 j).toUInt64 :=
    word_keep hA.len k2 (by omega) (by omega)
  simp only [PcOk] at hpc3
  rw [eval_not, eval_cmp_eq, eval_load, eval_add, eval_lit, eval_reg, Env.ofMachine_regs,
    show s2.data.regs.get64 .r15 = _ from (e2 .r15 (by simp)).trans hA.r15, load8_eq,
    show (frameEnv m0 s2.data 1168 (fun _ ↦ 0) 0).base 0 = fbOf m0 from rfl, Env.ofMachine_mem0,
    NativeRustcVm.wordOf_of_wordAt hlen2, ← BitVec.ofNat_add,
    show ((8 * lenOf m0 j).toUInt64).toBitVec = BitVec.ofNat 64 (8 * lenOf m0 j) from rfl,
    ofNat_beq (by omega) (by omega)] at hpc3
  obtain ⟨hT, hF3⟩ := Arrays.pc_cond hpc3
  by_cases hlast : i + 1 = lenOf m0 j
  · have hpc3' : s3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b14Offset) :=
      hF3 (by rw [Bool.not_eq_true, Bool.not_eq_false', decide_eq_true_eq]; omega)
    refine exec_at (hb14 hp) run_b14 (Env.wf_nil _) (by intro l h; cases h) hpc3' (match_nil _)
      fun s4 hm4 hpc4 ↦ .done _ (.inr ⟨?_, ?_⟩)
    · simp only [PcOk] at hpc4
      exact hpc4.trans (hp.label NativeRustcVmX64.Vm.InducedWeight.label_9_at)
    have hd4 : s4.data.dmem = s3.data.dmem := hm4.dmem_eq (Env.wf_nil _) rfl
    have r4 : ∀ r ∈ [Reg64.rbx, .r12, .r14], reg s4.data r = reg s3.data r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Match.reg_eq (match_nil _) hm4 rfl rfl
    refine ⟨hfr3.of_block (match_nil _) hm4 (Env.wf_nil _) rfl (after_eq run_b14 ▸ b14_keeps),
      hsp3.of_dmem hd4, hlp3.of_dmem hd4, hA.hj, hA.mu, ?_, ?_, (r4 .r14 (by simp)).trans hr14⟩
    · rw [← hlast]; exact (r4 .rbx (by simp)).trans hrbx
    · rw [← hlast]; exact (r4 .r12 (by simp)).trans hr12
  · refine .done _ (.inl ⟨(hT (by rw [Bool.not_eq_true', decide_eq_false_iff_not]; omega)).trans
      (hp.label NativeRustcVmX64.Vm.InducedWeight.label_8_at), hfr3, hsp3, hlp3, hA.hj, hA.mu,
      bufWords_keep hA.what hk (by omega) (by omega), word_keep hA.len hk (by omega) (by omega),
      by omega, hrbx, hr12, hr14, hr15⟩)

end

end NativeRustcVmX64.Whir.InducedWeight
