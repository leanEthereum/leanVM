module

public import NativeRustcVmArm.Code.Vm.ReaderLe.Names
public import NativeRustcVmArm.Code.Vm.ReaderWords.Names
public import NativeRustcVmArm.Wire.Decode.Iter

/-!
# `decode`'s first reads

From the entry: the prologue and the reader at the frame's byte 8 (`b0`), the stream's count
(`Reader::le`, `b1`), its bound (`b2`), its words (`Reader::words`, `b3`, `b4`): `None`, or the
state before the count is stored (`Mid`, at `b5`).
-/

namespace NativeRustcVmArm.Wire.Decode

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeVm.Model
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.Decode
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- **After the stream's words** (`b5`): the count `n` and the words `ws` read, to the cursor
`c1`. -/
structure Mid [Host] (k0 : Nat) (m0 : MachineData) (B : List UInt8) (n : Nat) (ws : List K)
    (c1 : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k0 + NativeRustcVmArm.Vm.Decode.b5Offset)
  fr : Frm m0 st.data
  x19 : st.data.regs.getXReg .X19 = m0.regs.X4
  x20 : st.data.regs.getXReg .X20 = m0.regs.X1
  x21 : st.data.regs.getXReg .X21 = m0.regs.X2
  x22 : st.data.regs.getXReg .X22 = m0.regs.X3
  x23 : (st.data.regs.getXReg .X23).toNat = n
  r1 : rdU32 B 0 = some (n, 4)
  r2 : rdWords B (2 * n) 4 = some (ws, c1)
  rd : ReaderAt st.data.dmem (rdr m0) (bpA m0) B c1
  wsAt : WordsAt st.data.dmem (dw m0 1) (ws.map K.lane)

end

public section

variable {m0 : MachineData} {B : List UInt8}

theorem wordAt_reg {d : Mem 64} {a x : BitVec 64}
    (h : BytesAt d a ((List.range 8).map (byteOf x))) : WordAt d a (UInt64.ofBitVec x) := by
  rw [byteOf_range] at h; exact h

theorem ofInt8 : BitVec.ofInt 64 8 = BitVec.ofNat 64 8 := rfl

theorem add_lit (x : BitVec 64) (n : Nat) :
    BinOp.apply .add .W64 x (BitVec.ofNat 64 n) = x + BitVec.ofNat 64 n := by
  simp [BinOp.apply]

theorem decode_none_1 (h : rdU32 B 0 = none) : decodeM B = none := by
  rw [decodeM_eq', h]

theorem decode_none_2 {n c0 : Nat} (h1 : rdU32 B 0 = some (n, c0))
    (h2 : rdWords B (2 * n) c0 = none) : decodeM B = none := by
  rw [decodeM_eq', h1]
  dsimp only
  rw [h2]

/-- The words of a stream that fits: fewer than the decoded area's. -/
theorem words_lt {n : Nat} {ws : List K} {c1 : Nat}
    (h2 : rdWords B (2 * n) 4 = some (ws, c1)) {len : Nat} (hd : decodedWords B.length ≤ len) :
    2 * n < len ∧ n ≤ maxStream B.length := by
  obtain ⟨-, hc, -⟩ := rdWords_c h2
  unfold decodedWords phaseBase streamEnd maxStream wireMaxPhases at *
  omega

theorem decodedWords_ge (L : Nat) : streamEnd L + 1 + 8 * phaseWords ≤ decodedWords L := by
  unfold decodedWords phaseBase wireMaxPhases; omega

theorem disjoint4 {a b c d : Region}
    (hab : NativeRustcVm.Apart a.addr a.size b.addr b.size)
    (hac : NativeRustcVm.Apart a.addr a.size c.addr c.size)
    (had : NativeRustcVm.Apart a.addr a.size d.addr d.size)
    (hbc : NativeRustcVm.Apart b.addr b.size c.addr c.size)
    (hbd : NativeRustcVm.Apart b.addr b.size d.addr d.size)
    (hcd : NativeRustcVm.Apart c.addr c.size d.addr d.size) :
    NativeRustcVm.Disjoint [a, b, c, d] := by
  simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
    implies_true]
  exact ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩

theorem cond_eq1 (x : UInt64) (h : x = 0 ∨ x = 1) :
    CmpOp.apply .eq .W64 x.toBitVec (BitVec.ofNat 64 1) = decide (x = 1) := by
  rcases h with rfl | rfl <;> rfl

theorem cond_eq0_32 (x : UInt64) (h : x = 0 ∨ x = 1) :
    CmpOp.apply .eq .W32 x.toBitVec (BitVec.ofNat 64 0) = decide (x = 0) := by
  rcases h with rfl | rfl <;> rfl

variable [Host] {k0 : Nat}

/-- **The first reads.** -/
theorem head_spec (hp : Placed code k0) (G : Geo m0 B)
    (hle : Spec (Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    (hwd : Spec (Labels.label NativeRustcVmArm.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost) :
    Eventually (step1 Host.exe) (fun st ↦ Res m0 B st ∨ ∃ n ws c1, Mid k0 m0 B n ws c1 st)
      ⟨m0, Host.addrOf (k0 + NativeRustcVmArm.Vm.Decode.b0Offset)⟩ := by
  have hst := G.st
  have hN := hst.2.1
  have hSP := m0.regs.SP.toNat_lt
  let env0 := Env.ofMachine m0 [(base m0 96, 96)]
  have hb := Ring.base_noWrap (m0 := m0) (F := 96) (by omega)
  have hbt := G.base_toNat (F := 96) (by omega)
  have hwf0 : env0.WF :=
    Env.wf_of ⟨⟨Ring.frame_mapped hst (by omega), hb⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm0 : Match env0 entryS m0 := match_ofMachine ⟨rfl, fun _ ↦ base_aligned hst, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]
        rw [show BitVec.ofInt 64 96 = BitVec.ofNat 64 96 from rfl]
        exact Ring.base_add_eq.symm)
    trivial trivial trivial trivial
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun s1 hm1 hpc1 ↦ ?_
  have hfr1 : Frm m0 s1.data :=
    Fr.ofPrologue hN (by omega) hm1 hwf0 rfl (by decide +kernel) (by decide) (by decide)
      (by decide)
  have hs1 := Match.sameOutside_in hm1 hwf0 (r0 := 0) (o := 0) (n := 96) rfl (by omega)
    (by decide)
  rw [NativeRustcVm.addr_add_zero] at hs1
  -- the reader
  have w8 := wordAt_reg (hm1.bytesAt_write (r := 0) (o := 8) (n := 8) (b := base m0 96)
    (sz := 96) rfl (by omega) (v := .reg .X0) (by decide))
  have w16 := wordAt_reg (hm1.bytesAt_write (r := 0) (o := 16) (n := 8) (b := base m0 96)
    (sz := 96) rfl (by omega) (v := .reg .X1) (by decide))
  have w24 := wordAt_reg (hm1.bytesAt_write (r := 0) (o := 24) (n := 8) (b := base m0 96)
    (sz := 96) rfl (by omega) (v := .lit 0) (by decide))
  have hlen := G.len
  have hL := G.l32
  have hR1 : ReaderAt s1.data.dmem (rdr m0) (bpA m0) B 0 := by
    refine ⟨⟨fun i hi ↦ ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, Nat.zero_le _⟩
    · rw [NativeRustcVm.addr_add_add]
      exact hfr1.kept _ (Ring.frame_mapped hst (by omega) _ (by change i < 24 at hi; omega))
    · show (rdr m0).toNat + 24 ≤ 2 ^ 64
      rw [G.rdr_toNat]; omega
    · have : rdr m0 = base m0 96 + BitVec.ofNat 64 8 := rfl
      rw [this]
      exact w8
    · have : NativeRustcVm.Transcript.off (rdr m0) 8 = base m0 96 + BitVec.ofNat 64 16 :=
        NativeRustcVm.addr_add_add _ _ _
      rw [this]
      have e : (B.length).toUInt64 = UInt64.ofBitVec ((Sym.reg .X1).eval env0) := by
        apply UInt64.toNat_inj.mp
        rw [toNat_toUInt64_of_lt (by omega), hlen]
        rfl
      rw [e]
      exact w16
    · rw [cur_eq]
      exact w24
    · refine NativeRustcVm.BytesAt.of_sameOutside G.bytes hs1 fun i hi hq ↦ ?_
      have hsB := G.sB (by omega)
      have hbn := G.bNw
      unfold NativeRustcVm.Apart at hsB
      unfold NoWrap at hbn
      rw [Sym.inRange_iff hb, hbt] at hq
      have hb' := G.base_toNat (F := 1280) le_rfl
      rw [NativeRustcVm.toNat_add_ofNat (by omega)] at hq
      omega
    · rw [hlen]; exact G.bNw
    · intro hl
      have hsB := G.sB (by omega)
      have hb' := G.base_toNat (F := 1280) le_rfl
      unfold NativeRustcVm.Apart at hsB ⊢
      rw [G.rdr_toNat, hlen]
      omega
  have e19 : s1.data.regs.getXReg .X19 = m0.regs.X4 := UInt64.toBitVec_inj.mp (hm1.regs .X19 _ rfl)
  have e20 : s1.data.regs.getXReg .X20 = m0.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X20 _ rfl)
  have e21 : s1.data.regs.getXReg .X21 = m0.regs.X2 := UInt64.toBitVec_inj.mp (hm1.regs .X21 _ rfl)
  have e22 : s1.data.regs.getXReg .X22 = m0.regs.X3 := UInt64.toBitVec_inj.mp (hm1.regs .X22 _ rfl)
  have hx0 : s1.data.regs.X0.toBitVec = rdr m0 := by
    rw [show s1.data.regs.X0 = s1.data.regs.getXReg .X0 from rfl, hm1.regs .X0 _ rfl]
    rfl
  have hx1 : s1.data.regs.X1.toNat = 4 := by
    show (s1.data.regs.getXReg .X1).toBitVec.toNat = 4
    rw [hm1.regs .X1 _ rfl]
    rfl
  simp only [PcOk] at hpc1
  refine le4_call hle G hfr1 hR1 hx0 hx1 hpc1 fun m2 hfr2 hcs2 _ hr2 ↦ ?_
  -- `b1`
  have hwf2 := frEnv_wf hst hfr2
  have hm2 := frEnv_match hst hfr2
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf2 (congrArg Host.addrOf rfl)
    hm2 fun s3 hm3 hpc3 ↦ ?_
  have hfr3 : Frm m0 s3.data := Fr.ofBlock hfr2 hm2 hm3 hwf2 rfl rfl rfl (keepOk (by decide))
  simp only [PcOk] at hpc3
  have hd3 : s3.data.dmem = m2.dmem := hm3.dmem_eq hwf2 rfl
  unfold Read4 at hr2
  rcases h1 : rdU32 B 0 with _ | ⟨n, c0⟩
  · rw [h1] at hr2
    have hc : (SBool.cmp .eq .W64 (.reg .X0) (.lit 1)).not.eval (frEnv m0 m2) = true := by
      simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
      rw [show m2.regs.getXReg .X0 = 0 from hr2]
      rfl
    simp only [hc, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.Decode.b14Offset) NativeRustcVmArm.Vm.Decode.label_9_at] at hpc3
    exact Eventually.mono (exit14 hp G hpc3 hfr3 (decode_none_1 h1)) fun _ h ↦ .inl h
  rw [h1] at hr2
  obtain ⟨h0, hn, hR2⟩ := hr2
  obtain ⟨rfl, -⟩ := rdU32_c h1
  have hn32 : n < 2 ^ 32 := rdU32_lt h1
  have hc : (SBool.cmp .eq .W64 (.reg .X0) (.lit 1)).not.eval (frEnv m0 m2) = false := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [show m2.regs.getXReg .X0 = 1 from h0]
    rfl
  simp only [hc, Bool.false_eq_true, ↓reduceIte] at hpc3
  -- `b2`
  have hwf3 := frEnv_wf hst hfr3
  have hm3' := frEnv_match hst hfr3
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf3
    (hpc3.trans (congrArg Host.addrOf rfl)) hm3' fun s4 hm4 hpc4 ↦ ?_
  have hfr4 : Frm m0 s4.data := Fr.ofBlock hfr3 hm3' hm4 hwf3 rfl rfl rfl (keepOk (by decide))
  have hd4 : s4.data.dmem = s3.data.dmem := hm4.dmem_eq hwf3 rfl
  simp only [PcOk] at hpc4
  have r3 : ∀ x ∈ [XReg.X1, .X19, .X20, .X21, .X22], s3.data.regs.getXReg x = m2.regs.getXReg x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm2 hm3 rfl rfl
  have c22 : m2.regs.getXReg .X22 = m0.regs.X3 := by rw [hcs2 .X22 rfl, e22]
  have c21 : m2.regs.getXReg .X21 = m0.regs.X2 := by rw [hcs2 .X21 rfl, e21]
  have c20 : m2.regs.getXReg .X20 = m0.regs.X1 := by rw [hcs2 .X20 rfl, e20]
  have c19 : m2.regs.getXReg .X19 = m0.regs.X4 := by rw [hcs2 .X19 rfl, e19]
  have h2n : (UnOp.apply (.ubfm 63 62) .W64 (s3.data.regs.getXReg .X1).toBitVec).toNat = 2 * n := by
    rw [lsl1_toNat, r3 .X1 (by simp)]
    show 2 * m2.regs.X1.toNat % 2 ^ 64 = 2 * n
    rw [hn]; omega
  have hc4 : (SBool.cmp .ult .W64 (.un (.ubfm 63 62) .W64 (.reg .X1)) (.reg .X22)).not.eval
      (frEnv m0 s3.data) = decide ¬(2 * n < lenW m0) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs, ult_apply, h2n, r3 .X22 (by simp), c22]
    rfl
  rw [hc4] at hpc4
  have hdLe := G.dLe
  by_cases hlt : 2 * n < lenW m0
  swap
  · simp only [hlt, not_false_eq_true, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.Decode.b14Offset) NativeRustcVmArm.Vm.Decode.label_9_at] at hpc4
    refine Eventually.mono (exit14 hp G hpc4 hfr4 (decode_none_2 h1 ?_)) fun _ h ↦ .inl h
    rcases h2 : rdWords B (2 * n) 4 with _ | ⟨ws, c1⟩
    · rfl
    · exact absurd (words_lt h2 (by rw [hlen]; exact hdLe)).1 hlt
  simp only [hlt, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc4
  -- `b3`: `Reader::words`' call
  have hwf4 := frEnv_wf hst hfr4
  have hm4' := frEnv_match hst hfr4
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf4
    (hpc4.trans (congrArg Host.addrOf rfl)) hm4' fun s5 hm5 hpc5 ↦ ?_
  have hfr5 : Frm m0 s5.data := Fr.ofBlock hfr4 hm4' hm5 hwf4 rfl rfl rfl (keepOk (by decide))
  have hd5 : s5.data.dmem = s4.data.dmem := hm5.dmem_eq hwf4 rfl
  simp only [PcOk] at hpc5
  have r4 : ∀ x ∈ [XReg.X19, .X20, .X21, .X22], s4.data.regs.getXReg x = m2.regs.getXReg x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      rw [Match.reg_eq hm3' hm4 rfl rfl, r3 _ (by simp)]
  have y0 : s5.data.regs.X0.toBitVec = rdr m0 := by
    rw [show s5.data.regs.X0 = s5.data.regs.getXReg .X0 from rfl, hm5.regs .X0 _ rfl]
    simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some, ofInt8]
  have y1 : s5.data.regs.X1.toBitVec = dw m0 1 := by
    rw [show s5.data.regs.X1 = s5.data.regs.getXReg .X1 from rfl, hm5.regs .X1 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs, add_lit, r4 .X21 (by simp), c21]
  have y2 : s5.data.regs.X2.toNat = 2 * n := by
    show (s5.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [Match.reg_eq hm4' hm5 rfl rfl, hm4.regs .X2 _ rfl]
    exact h2n
  have y23 : (s5.data.regs.getXReg .X23).toNat = n := by
    show (s5.data.regs.getXReg .X23).toBitVec.toNat = n
    rw [hm5.regs .X23 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [Match.reg_eq hm3' hm4 rfl rfl, r3 .X1 (by simp)]
    exact hn
  have hR5 : ReaderAt s5.data.dmem (rdr m0) (bpA m0) B 4 := by
    rw [hd5, hd4, hd3]; exact hR2
  have hl : 0 < Ln m0 := by have := (rdU32_c h1).2; omega
  have hNs : 96 + readerWordsStack ≤ 1280 := by decide
  have hrw : readerWordsStack = 32 := rfl
  have hsb : stackBelow s5.data readerWordsStack = base m0 (96 + readerWordsStack) :=
    Ring.stackBelow_eq hfr5.sp (by rw [hrw]; omega)
  rw [hrw] at hsb
  have hb128 := G.base_toNat (F := 128) (by omega)
  have hdg := decodedWords_ge (Ln m0)
  rw [phaseWords_eq] at hdg
  have hd1 := G.dw_toNat (i := 1) (by omega)
  have hdN := G.dNw
  obtain ⟨hr, hbl⟩ := G.rdr_base
  have hb1280 := G.base_toNat (F := 1280) le_rfl
  have sD := G.sD
  have sB := G.sB hl
  have bD := G.bD hl
  have hbN := G.bNw
  unfold NativeRustcVm.Apart at sD sB bD
  unfold NoWrap at hbN
  have hpre : ReaderWordsPre s5.data := by
    refine ⟨hfr5.stackOk hst (by decide) hNs, ?_, bpA m0, B, 4, by rw [y0]; exact hR5, ?_⟩
    · rw [y1, y2]
      refine ⟨fun i hi ↦ ?_, by show (dw m0 1).toNat + 8 * (2 * n) ≤ 2 ^ 64; rw [hd1]; omega⟩
      rw [NativeRustcVm.addr_add_add]
      exact hfr5.kept _ (G.dOk.1 _ (by change i < 8 * (2 * n) at hi; show _ < 8 * lenW m0; omega))
    · rw [y0, y1, y2]
      refine disjoint4 ?_ ?_ ?_ ?_ ?_ ?_ <;>
        simp only [NativeRustcVm.Apart, stackR, hrw, hsb, hb128, hr, hd1, hlen] <;> omega
  have hQ : ∀ m', ReaderWordsPost s5.data m' → SameOutside s5.data.dmem m'.dmem (fun q ↦
      InRange (stackBelow s5.data readerWordsStack) readerWordsStack q ∨
      InRange (base m0 96 + BitVec.ofNat 64 24) 8 q ∨ W m0 q) ∧ Saved s5.data m' := by
    rintro m' ⟨-, hs, hsv⟩
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q ⟨Rg, hRg, hq⟩ ↦ ?_, hsv⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRg
    rcases hRg with rfl | rfl | rfl
    · have h : InRange s5.data.regs.X1.toBitVec (8 * s5.data.regs.X2.toNat) q := hq
      rw [y1, y2] at h
      exact .inr (.inr (.inl (NativeRustcVm.InRange.of_sub h hdN (by omega))))
    · have h : InRange (NativeRustcVm.Transcript.off s5.data.regs.X0.toBitVec 16) 8 q := hq
      rw [y0, cur_eq] at h
      exact .inr (.inl h)
    · exact .inl hq
  refine Fr.leafIn (N' := readerWordsStack) (lo := 24) (n := 8) hfr5 G.sp hNs (by omega)
    (by decide) (by decide) G.notFrame hwd hpc5 hpre hQ fun m6 hfr6 hq6 hcs6 ↦ ?_
  obtain ⟨hpost, hs6, -⟩ := hq6
  have hpost' := hpost (bpA m0) B 4 (by rw [y0]; exact hR5)
  rw [y0, y1, y2] at hpost'
  -- `b4`
  have hwf6 := frEnv_wf hst hfr6
  have hm6 := frEnv_match hst hfr6
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf6 (congrArg Host.addrOf rfl)
    hm6 fun s7 hm7 hpc7 ↦ ?_
  have hfr7 : Frm m0 s7.data := Fr.ofBlock hfr6 hm6 hm7 hwf6 rfl rfl rfl (keepOk (by decide))
  have hd7 : s7.data.dmem = m6.dmem := hm7.dmem_eq hwf6 rfl
  simp only [PcOk] at hpc7
  have e70 : s7.data.regs.X0 = m6.regs.X0 := Match.reg_eq hm6 hm7 (r := .X0) rfl rfl
  rcases h2 : rdWords B (2 * n) 4 with _ | ⟨ws, c1⟩
  · rw [h2] at hpost'
    have hc7 : (SBool.cmp .eq .W32 (.reg .X0) (.lit 0)).eval (frEnv m0 m6) = true := by
      simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
      rw [show m6.regs.getXReg .X0 = 0 from hpost']
      rfl
    simp only [hc7, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.Decode.b15Offset) NativeRustcVmArm.Vm.Decode.label_10_at] at hpc7
    refine Eventually.mono (exit15 hp G hpc7 hfr7 ?_) fun _ h ↦ .inl h
    rw [decode_none_2 h1 h2, e70]
    exact hpost'
  rw [h2] at hpost'
  obtain ⟨h60, hws, hR6⟩ := hpost'
  have hc7 : (SBool.cmp .eq .W32 (.reg .X0) (.lit 0)).eval (frEnv m0 m6) = false := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [show m6.regs.getXReg .X0 = 1 from h60]
    rfl
  simp only [hc7, Bool.false_eq_true, ↓reduceIte] at hpc7
  have r7 : ∀ x ∈ [XReg.X19, .X20, .X21, .X22, .X23], s7.data.regs.getXReg x =
      s5.data.regs.getXReg x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      rw [Match.reg_eq hm6 hm7 rfl rfl, hcs6 _ rfl]
  have r5 : ∀ x ∈ [XReg.X19, .X20, .X21, .X22], s5.data.regs.getXReg x =
      m2.regs.getXReg x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      rw [Match.reg_eq hm4' hm5 rfl rfl, r4 _ (by simp)]
  refine .done _ (.inr ⟨n, ws, c1, hpc7.trans (congrArg Host.addrOf rfl), hfr7, ?_, ?_, ?_, ?_,
    ?_, h1, h2, by rw [hd7]; exact hR6, by rw [hd7]; exact hws⟩)
  · rw [r7 .X19 (by simp), r5 .X19 (by simp), c19]
  · rw [r7 .X20 (by simp), r5 .X20 (by simp), c20]
  · rw [r7 .X21 (by simp), r5 .X21 (by simp), c21]
  · rw [r7 .X22 (by simp), r5 .X22 (by simp), c22]
  · rw [r7 .X23 (by simp)]; exact y23

end

end NativeRustcVmArm.Wire.Decode
