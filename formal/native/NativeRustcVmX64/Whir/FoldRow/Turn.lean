module

public import NativeRustcVmX64.Whir.FoldRow.Inv
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `fold_row`'s turns (x86-64)

`turn`: from the turn's head (`TInv r i`, `b10`): for `i > 31` straight to `b9`; else `b11` loads
lanes `2i`, `2i + 1` and the factor and calls `EW::mul`, `b12` stores `g + factor·f` in lane `i`.
`b9` (`count`) counts: back at the head (`TInv r (i + 1)`) or, the round done, at `b3`
(`EInv r`).
-/

namespace NativeRustcVmX64.Whir.FoldRow

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.FoldRow NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region WordAt WordsAt EWAt ewOf)
open NativeRustcVmX64.Field (midS frameS frameEnv)
open NativeRustcVmX64.Arrays (stackOk_mono load8_eq load_word wordAt_of_write ewAt_of_writes ew_of_loads
  eval_reg eval_lit eval_load eval_add eval_cmp_eq eval_not eval_xor wf_two apart_symm
  not_inRange_of_apart ew_add_comm written_region0)

@[expose] public section

/-- At `b9`: turn `i` done. -/
structure B9 (m0 : MachineData) (r i : Nat) (st : MachineData) : Prop where
  base : Base m0 st
  hr : r < rnOf m0
  rd : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 40) (.ofBitVec (rpOf m0 + BitVec.ofNat 64 (32 * r)))
  f0 : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 16) (facOf m0 r).c0
  f1 : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 8) (facOf m0 r).c1
  hi : i < nOf m0 >>> (r + 1)
  rbx : reg st .rbx = BitVec.ofNat 64 (nOf m0 >>> (r + 1))
  r12 : reg st .r12 = BitVec.ofNat 64 i
  r13 : reg st .r13 = BitVec.ofNat 64 (8 + 16 * i)
  lanes : LanesAt m0 st.dmem (foldPart (xOf m0) (rdOf m0 r) (i + 1) (lanesAt m0 r))

end

public section

/-- The frame's spilled words kept by a change in the lanes. -/
theorem frame_word_keep {m0 : MachineData} {d d' : DataMem} {o : Nat} {w : UInt64}
    (hS : StackOk m0 foldRowStack) (hlanes : WhirIn m0 (aOf m0) lanesBytes foldRowStack)
    {c n : Nat} (hcn : c + n ≤ lanesBytes)
    (hs : SameOutside d d' (InRange (aOf m0 + BitVec.ofNat 64 c) n)) (ho : o + 8 ≤ 104)
    (h : WordAt d (fbOf m0 + BitVec.ofNat 64 o) w) : WordAt d' (fbOf m0 + BitVec.ofNat 64 o) w :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun j hj ↦ by
    rw [NativeRustcVm.length_wordBytes] at hj
    rw [addr_add]
    intro hin
    exact not_inRange_frame hS (by decide) hlanes.2 hlanes.1.2 (j := o + j) (by omega)
      (Arrays.inRange_sub hlanes.1.2 hcn hin)


/-- Lanes kept by changes in the stack. -/
theorem lanes_stack {m0 : MachineData} {d d' : DataMem} {f : Nat → EW} {R : BitVec 64 → Prop}
    (hS : StackOk m0 foldRowStack) (hlanes : WhirIn m0 (aOf m0) lanesBytes foldRowStack)
    (hf : LanesAt m0 d f) (hs : SameOutside d d' R)
    (hR : ∀ p, R p → InRange (stackBelow m0 foldRowStack) foldRowStack p) : LanesAt m0 d' f :=
  lanesAt_keep hf hs fun j hj h ↦
    not_inRange_of_apart (Arrays.apart_mono hlanes.2 (n'' := foldRowStack) (by omega))
      hlanes.1.2 (NativeRustcVm.NoWrap.mono (stack_noWrap hS) (by omega)) (by
        show j < lanesBytes; exact hj) (hR _ h)

variable [Host] {k : Nat}

theorem hb9 (hp : Placed code k) : b9.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.FoldRow.b9Offset) :=
  b9_in_code.trans hp.1 (by simp [b9])
theorem hb10 (hp : Placed code k) : b10.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.FoldRow.b10Offset) :=
  b10_in_code.trans hp.1 (by simp [b10])
theorem hb11 (hp : Placed code k) : b11.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.FoldRow.b11Offset) :=
  b11_in_code.trans hp.1 (by simp [b11])
theorem hb12 (hp : Placed code k) : b12.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.FoldRow.b12Offset) :=
  b12_in_code.trans hp.1 (by simp [b12])

/-- **The count** (`b9`). -/
theorem count (hp : Placed code k) {m0 : MachineData} {r i : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b9Offset)) (hB : B9 m0 r i st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b10Offset) ∧ TInv m0 r (i + 1) s.data) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b3Offset) ∧ EInv m0 r s.data)) st := by
  have hn64 := (reg m0 .rsi).isLt
  have hnn : nOf m0 = (reg m0 .rsi).toNat := rfl
  have hsh : nOf m0 >>> (r + 1) ≤ nOf m0 := Nat.shiftRight_le _ _
  have hi := hB.hi
  refine exec_at (hb9 hp) run_b9 (Env.wf_nil _) (by intro l h; cases h) hpc (match_nil _)
    fun st1 hm1 hpc1 ↦ ?_
  have hfr1 := hB.base.fr.of_block (match_nil _) hm1 (Env.wf_nil _) rfl (after_eq run_b9 ▸ b9_keeps)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq (Env.wf_nil _) rfl
  have hbase : Base m0 st1.data := ⟨hfr1, hd1 ▸ hB.base.x, hd1 ▸ hB.base.ed,
    (Match.reg_eq (r := .r14) (match_nil _) hm1 rfl rfl).trans hB.base.r14⟩
  have hrbx : reg st1.data .rbx = BitVec.ofNat 64 (nOf m0 >>> (r + 1)) :=
    (Match.reg_eq (r := .rbx) (match_nil _) hm1 rfl rfl).trans hB.rbx
  simp only [PcOk] at hpc1
  rw [eval_cmp_eq, eval_reg, eval_add, eval_reg, eval_lit, Env.ofMachine_regs, Env.ofMachine_regs,
    show st.data.regs.get64 .rbx = _ from hB.rbx, show st.data.regs.get64 .r12 = _ from hB.r12,
    ← BitVec.ofNat_add, ofNat_beq (by omega) (by omega)] at hpc1
  obtain ⟨hT, hF⟩ := Arrays.pc_cond hpc1
  by_cases hlast : nOf m0 >>> (r + 1) = i + 1
  · refine .done _ (.inr ⟨(hT (by rw [decide_eq_true_eq]; exact hlast)).trans
      (hp.label NativeRustcVmX64.Vm.FoldRow.label_2_at), hbase, hB.hr, hd1 ▸ hB.rd, hrbx, ?_⟩)
    rw [hd1, lanesAt_succ, hlast]
    exact hB.lanes
  · refine .done _ (.inl ⟨hF (by rw [decide_eq_true_eq]; exact hlast), hbase, hB.hr,
      hd1 ▸ hB.rd, hd1 ▸ hB.f0, hd1 ▸ hB.f1, by omega, hrbx, ?_, ?_, hd1 ▸ hB.lanes⟩)
    · refine (hm1.regs .r12 _ rfl).trans ?_
      rw [eval_add, eval_reg, eval_lit, Env.ofMachine_regs, show st.data.regs.get64 .r12 = _ from
        hB.r12, ← BitVec.ofNat_add]
    · refine (hm1.regs .r13 _ rfl).trans ?_
      rw [eval_add, eval_reg, eval_lit, Env.ofMachine_regs, show st.data.regs.get64 .r13 = _ from
        hB.r13, ← BitVec.ofNat_add]
      congr 1
      omega

/-- **A turn** from its head. -/
theorem turn (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : FoldRowPre m0) {r i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b10Offset)) (hI : TInv m0 r i st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b10Offset) ∧ TInv m0 r (i + 1) s.data) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b3Offset) ∧ EInv m0 r s.data)) st := by
  obtain ⟨hS, hlanes, hrin, hap, hR6⟩ := hpre
  obtain ⟨hF, -, hle⟩ := stack_le
  have hS1 := hS.1
  have hS2 := hS.2.1
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hlb : lanesBytes = 1024 := rfl
  have hout := out_one hlanes
  have hsl := slots_ok
  have hfr := hI.base.fr
  have hlw : ∀ w : UInt64, (NativeRustcVm.wordBytes w).length = 8 := NativeRustcVm.length_wordBytes
  have hanw := hlanes.1.2
  unfold NoWrap at hanw
  rw [hlb] at hanw
  refine exec_at (hb10 hp) run_b10 (Env.wf_nil _) (by intro l h; cases h) hpc (match_nil _)
    fun st1 hm1 hpc1 ↦ ?_
  have hfr1 := hfr.of_block (match_nil _) hm1 (Env.wf_nil _) rfl (after_eq run_b10 ▸ b10_keeps)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq (Env.wf_nil _) rfl
  have e1 : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14], reg st1.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact Match.reg_eq (match_nil _) hm1 rfl rfl
  have hbase1 : Base m0 st1.data := ⟨hfr1, hd1 ▸ hI.base.x, hd1 ▸ hI.base.ed,
    (e1 .r14 (by simp)).trans hI.base.r14⟩
  have hi64 : i < 2 ^ 64 := by
    have := hI.hi
    have := Nat.shiftRight_le (nOf m0) (r + 1)
    have := (reg m0 .rsi).isLt
    unfold nOf at *
    omega
  simp only [PcOk] at hpc1
  rw [gt_eval, eval_reg, eval_lit, Env.ofMachine_regs,
    show st.data.regs.get64 .r12 = _ from hI.r12, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 31 < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt hi64] at hpc1
  obtain ⟨hT, hF1⟩ := Arrays.pc_cond hpc1
  have hi := hI.hi
  have hn64 := (reg m0 .rsi).isLt
  have hsh : nOf m0 >>> (r + 1) ≤ nOf m0 := Nat.shiftRight_le _ _
  have hnn : nOf m0 = (reg m0 .rsi).toNat := rfl
  by_cases hbig : 31 < i
  · have hc : decide (31 < i) = true := decide_eq_true hbig
    have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b9Offset) := (hT hc).trans (hp.label NativeRustcVmX64.Vm.FoldRow.label_7_at)
    refine count hp hpc1' ⟨hbase1, hI.hr, hd1 ▸ hI.rd, hd1 ▸ hI.f0, hd1 ▸ hI.f1, hi,
      (e1 .rbx (by simp)).trans hI.rbx, (e1 .r12 (by simp)).trans hI.r12,
      (e1 .r13 (by simp)).trans hI.r13, ?_⟩
    rw [hd1, foldPart_succ_of_le _ _ _ (by omega)]
    exact hI.lanes
  have hi32 : i < 32 := by omega
  have hc : ¬decide (31 < i) = true := by rw [decide_eq_true_eq]; exact hbig
  have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b11Offset) := hF1 hc
  -- `b11`: lanes `2i`, `2i + 1`, the factor; `EW::mul`
  have hrd : Readable st1.data (aOf m0 + BitVec.ofNat 64 (32 * i)) 32 :=
    Readable.keep (Readable.sub hlanes.1 (by rw [hlb]; omega)) hfr1.kept
  have hap1 : Apart (stackBelow m0 96) (96 + 8) (aOf m0 + BitVec.ofNat 64 (32 * i)) 32 :=
    apart_symm (apart_frame' hS hF (OffStack.sub hlanes.2 hlanes.1.2 (by rw [hlb]; omega)))
  have hwf2 : (Env.ofMachine st1.data [(stackBelow m0 96, 96 + 8),
      (aOf m0 + BitVec.ofNat 64 (32 * i), 32)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b12Offset)).toBitVec).WF :=
    wf_two (stackOk_mono hS hF) hfr1.kept hrd hap1
  have hm2 : Match (Env.ofMachine st1.data [(stackBelow m0 96, 96 + 8),
      (aOf m0 + BitVec.ofNat 64 (32 * i), 32)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b12Offset)).toBitVec) pairS st1.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hfr1.rsp, trivial⟩ trivial trivial
      ⟨by
        show BinOp.apply .add .W64 (reg st1.data .r14)
          (BinOp.apply .mul .W64 (reg st1.data .r13) (BitVec.ofNat 64 2)) =
            aOf m0 + BitVec.ofNat 64 (32 * i) + BitVec.ofInt 64 16
        rw [add64, mul64, hbase1.r14, e1 .r13 (by simp), hI.r13,
          show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, addr_add]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
        omega, trivial⟩
  refine exec_at (hb11 hp) run_b11 hwf2 (fun _ _ ↦ rfl) hpc1' hm2 fun st2 hm3 hpc2 ↦ ?_
  obtain ⟨hk3, hsp3, hw3⟩ := after_eq run_b11 ▸ b11_call
  have hrsp3 := rsp_call hm3 hsp3
  have hf : ewArg (reg st2.data .rdx) (reg st2.data .rcx) =
      foldPart (xOf m0) (rdOf m0 r) i (lanesAt m0 r) (2 * i) := by
    rw [ew_of_loads (r := 1) (off := 0) hm3 rfl rfl]
    show ewOf st1.data.dmem (aOf m0 + BitVec.ofNat 64 (32 * i) + BitVec.ofNat 64 0) = _
    rw [NativeRustcVm.addr_add_zero, show 32 * i = 16 * (2 * i) by omega]
    exact NativeRustcVm.ewOf_of_ewAt (hd1 ▸ hI.lanes (2 * i) (by omega))
  have hg : ewArg (reg st2.data .rbp) (reg st2.data .r15) = lanesAt m0 r (2 * i + 1) := by
    rw [ew_of_loads (r := 1) (off := 16) hm3 rfl rfl]
    show ewOf st1.data.dmem (aOf m0 + BitVec.ofNat 64 (32 * i) + BitVec.ofNat 64 16) = _
    rw [addr_add, show 32 * i + 16 = 16 * (2 * i + 1) by omega, ← foldPart_old (xOf m0) (rdOf m0 r) (lanesAt m0 r) (i := i) (j := 2 * i + 1) (by omega)]
    exact NativeRustcVm.ewOf_of_ewAt (hd1 ▸ hI.lanes (2 * i + 1) (by omega))
  have hfac : ewArg (reg st2.data .rdi) (reg st2.data .rsi) = facOf m0 r := by
    show (⟨UInt64.ofBitVec (st2.data.regs.get64 .rdi), UInt64.ofBitVec (st2.data.regs.get64 .rsi)⟩
      : EW) = _
    rw [hm3.regs .rdi _ rfl, hm3.regs .rsi _ rfl, eval_load, eval_load,
      load_word (show WordAt st1.data.dmem (stackBelow m0 96 + BitVec.ofNat 64 16) _ from
        hd1 ▸ hI.f0),
      load_word (show WordAt st1.data.dmem (stackBelow m0 96 + BitVec.ofNat 64 8) _ from
        hd1 ▸ hI.f1), UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec]
  have e3 : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14], reg st2.data r = reg st1.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm2 hm3 rfl rfl
  refine Frame.call hmul hfr1 hS hle (L := 48) (by decide) (fun q hq ↦ hsl q hq) hout hwf2 hm2 hm3
    hpc2 hk3 hsp3 (fun w hw ↦ ⟨(hw3 w hw).1, by have := (hw3 w hw).2; omega⟩)
    (stackOk_callee hS (fun p h ↦ hm3.kept hwf2 p (hfr1.kept p h)) hrsp3 hle)
    (fun m' ⟨_, _, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inr (.inr h))⟩)
    fun st3 hpc3 hfr3 ⟨hax3, hdx3, hso3, hsv3⟩ ↦ ?_
  have hkw : ∀ {o : Nat} {w : UInt64}, 8 ≤ o → o + 8 ≤ 104 →
      WordAt st.data.dmem (fbOf m0 + BitVec.ofNat 64 o) w →
      WordAt st3.data.dmem (fbOf m0 + BitVec.ofNat 64 o) w := fun h8 ho h ↦
    keep_call hm3 hwf2 rfl rfl hw3 hS hrsp3 hle hso3 h8 (by rw [hlw]; omega) (hd1 ▸ h)
  have hlanes3 : LanesAt m0 st3.data.dmem (foldPart (xOf m0) (rdOf m0 r) i (lanesAt m0 r)) := by
    have h0 : LanesAt m0 st1.data.dmem (foldPart (xOf m0) (rdOf m0 r) i (lanesAt m0 r)) := by
      unfold LanesAt; rw [hd1]; exact hI.lanes
    refine lanes_stack hS hlanes (lanes_stack hS hlanes h0
      (Match.sameOutside hm3 hwf2) fun p h ↦ ?_) hso3 fun p h ↦ inRange_callee hS hrsp3 hle h
    exact inRange_frame hS hF (L := 8) (by omega) (written_region0 rfl hwf2 (k := 8) (by omega)
      (fun w hw' ↦ ⟨(hw3 w hw').1, (hw3 w hw').2⟩) h)
  have e3 : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14], reg st3.data r = reg st.data r := by
    intro r hr
    have hc : calleeSaved r = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> rfl
    rw [← e1 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact (hsv3.1 _ rfl).trans (Match.reg_eq hm2 hm3 rfl rfl)
  have hgg : ewArg (reg st3.data .rbp) (reg st3.data .r15) = lanesAt m0 r (2 * i + 1) := by
    rw [show reg st3.data .rbp = reg st2.data .rbp from hsv3.1 .rbp rfl,
      show reg st3.data .r15 = reg st2.data .r15 from hsv3.1 .r15 rfl]
    exact hg
  have hprod : ewArg (reg st3.data .rax) (reg st3.data .rdx) =
      facOf m0 r * foldPart (xOf m0) (rdOf m0 r) i (lanesAt m0 r) (2 * i) := by
    rw [hax3, hdx3, ← hfac, ← hf]
    rfl
  -- `b12`: lane `i`
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b12Offset) := hpc3
  have hrd4 : Readable st3.data (aOf m0 + BitVec.ofNat 64 (16 * i)) 16 :=
    Readable.keep (Readable.sub hlanes.1 (by rw [hlb]; omega)) hfr3.kept
  have hwf4 : (Env.ofMachine st3.data [(aOf m0 + BitVec.ofNat 64 (16 * i), 16)]).WF :=
    Env.wf_of ⟨⟨hrd4.1, hrd4.2⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm4 : Match (Env.ofMachine st3.data [(aOf m0 + BitVec.ofNat 64 (16 * i), 16)]) laneS
      st3.data :=
    match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨by
      show BinOp.apply .add .W64 (reg st3.data .r14) (reg st3.data .r13) =
        aOf m0 + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 8
      rw [add64, e3 .r14 (by simp), e3 .r13 (by simp), hI.base.r14, hI.r13,
        show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add]
      congr 2
      omega, trivial⟩
  refine exec_at (hb12 hp) run_b12 hwf4 (by intro l h; cases h) hpc3' hm4 fun st4 hm5 hpc4 ↦ ?_
  obtain ⟨hk5, hw5, hv0, hv8⟩ := after_eq run_b12 ▸ b12_write
  have hfr4 := hfr3.of_write hm4 hm5 hwf4 rfl hk5 (r := 0) rfl le_rfl hw5
    (fun p h ↦ .inl (inAny_one (Arrays.inRange_sub hlanes.1.2 (by rw [hlb]; omega) h)))
    fun q hq j hj ↦ by
      rw [addr_add]
      intro hin
      exact not_inRange_frame hS hF hlanes.2 hlanes.1.2 (j := q.1 + j)
        (by have := hsl q hq; omega) (Arrays.inRange_sub hlanes.1.2 (by rw [hlb]; omega) hin)
  have hso4 := same_region_le hm5 hwf4 (r := 0) rfl le_rfl hw5
  have hnew : EWAt st4.data.dmem (aOf m0 + BitVec.ofNat 64 (16 * i))
      (lanesAt m0 r (2 * i + 1) + facOf m0 r *
        foldPart (xOf m0) (rdOf m0 r) i (lanesAt m0 r) (2 * i)) := by
    have := ewAt_of_writes hm5 (r := 0) (o := 0) rfl (by decide) hv0 hv8
    rw [NativeRustcVm.addr_add_zero, eval_xor, eval_xor, eval_reg, eval_reg, eval_reg, eval_reg,
      Env.ofMachine_regs, Env.ofMachine_regs, Env.ofMachine_regs, Env.ofMachine_regs,
      Arrays.ewArg_xor] at this
    rw [ew_add_comm, ← hgg, ← hprod]
    exact this
  have hlanes4 : LanesAt m0 st4.data.dmem
      (foldPart (xOf m0) (rdOf m0 r) (i + 1) (lanesAt m0 r)) := by
    rw [foldPart_succ _ _ _ hi32]
    rw [foldPart_old (xOf m0) (rdOf m0 r) (lanesAt m0 r) (i := i) (j := 2 * i) (by omega)] at hnew
    exact lanesAt_update hlanes3 (by omega) hlanes.1.2 hnew hso4
  have e4 : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14], reg st4.data r = reg st.data r := by
    intro r hr
    rw [← e3 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm4 hm5 rfl rfl
  have hkw4 : ∀ {o : Nat} {w : UInt64}, 8 ≤ o → o + 8 ≤ 104 →
      WordAt st.data.dmem (fbOf m0 + BitVec.ofNat 64 o) w →
      WordAt st4.data.dmem (fbOf m0 + BitVec.ofNat 64 o) w := fun h8 ho h ↦
    frame_word_keep hS hlanes (c := 16 * i) (n := 16) (by rw [hlb]; omega) hso4 ho (hkw h8 ho h)
  simp only [PcOk] at hpc4
  exact count hp (hpc4.trans (hp.label NativeRustcVmX64.Vm.FoldRow.label_7_at)) ⟨⟨hfr4, hkw4 (by omega) (by omega) hI.base.x,
    hkw4 (by omega) (by omega) hI.base.ed, (e4 .r14 (by simp)).trans hI.base.r14⟩, hI.hr,
    hkw4 (by omega) (by omega) hI.rd, hkw4 (by omega) (by omega) hI.f0,
    hkw4 (by omega) (by omega) hI.f1, hi, (e4 .rbx (by simp)).trans hI.rbx,
    (e4 .r12 (by simp)).trans hI.r12, (e4 .r13 (by simp)).trans hI.r13, hlanes4⟩

end

end NativeRustcVmX64.Whir.FoldRow
