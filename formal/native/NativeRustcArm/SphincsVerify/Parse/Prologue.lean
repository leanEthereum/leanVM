module

public import NativeRustcArm.SphincsVerify.Parse.OpenBasic
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify

/-!
# The parse, part 1: the prologue and initial copies (`b0 .. b2`)

`b0` saves X29, X30, X28 ... X19 at `SP₀ - 96` and points X29 there; the probe loop `b1` lowers SP
a page at a time (5 turns, region 0 the 16 bytes at the new SP); `b2` allocates the last 1040
bytes, copies `pk` (32 bytes from X0) to `448` (`b2a`) and `R` (16 bytes from X2) to `20048`
(`b2b`), and initializes the openings' loop registers (`AtOpen 0` at `b3`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify
  LeanVM.Protocol.KeccakHash

@[expose] public section

/-- At the entry: region 0 the frame, SP its top. -/
def entryS : SState := init [(21616, true)] (.ptr 0 21616)

/-- In the probe loop: region 0 the 16 bytes at the next page, SP a page above them. -/
def probeS : SState := init [(16, true)] (.ptr 0 4096)

/-- First 17 directives of `b2`: allocates the last 1040 bytes, copies `pk` from `X0`, sets up
registers. -/
def b2a : List Directive := b2.take 17

/-- Last 3 directives of `b2`: copies the 16-byte randomizer from `X2` to `20048`. -/
def b2b : List Directive := b2.drop 17

/-- At `b2a`: region 0 the frame (SP at `1040`), region 1 `pk` (`X0 = .ptr 1 0`). -/
def b2aS : SState := init [(21616, true), (32, false)] (.ptr 0 1040) [(.X0, .ptr 1 0)]

/-- At `b2b`: region 0 the frame (SP at `0`), region 1 the randomizer (`X2 = .ptr 1 0`). -/
def b2bS : SState := init [(21616, true), (16, false)] (.ptr 0 0) [(.X2, .ptr 1 0)]

/-- In the probe loop after `t` turns. -/
def Probe (r : Run) (t : Nat) (m : MachineData) : Prop :=
  t ≤ 5 ∧ m.regs.SP.toBitVec = r.off (21520 - 4096 * t) ∧ Run.RegIs m .X9 (r.off 1040) ∧
    Run.RegIs m .X29 (r.off 21520) ∧ m.regs.getXReg .X0 = r.m0.regs.getXReg .X0 ∧
    m.regs.getXReg .X1 = r.m0.regs.getXReg .X1 ∧ m.regs.getXReg .X2 = r.m0.regs.getXReg .X2 ∧
    BytesAt m.dmem (r.off 21520) (savedBytes r.m0) ∧
    SameOutside r.m0.dmem m.dmem (InRange (r.off 21520) 96) ∧ Kept r.m0.dmem m.dmem

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 probeS
sym_block run_b2a := exec b2a b2aS
sym_block run_b2b := exec b2b b2bS

public section

theorem ofInt_ofNat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  simp

variable (r : Run)

theorem base_add (a : Nat) : r.base + BitVec.ofInt 64 (a : Int) = r.off a := by
  rw [ofInt_ofNat]; rfl

theorem off_add_int (a b : Nat) : r.off a + BitVec.ofInt 64 (b : Int) = r.off (a + b) := by
  rw [ofInt_ofNat, off_add]

theorem off_inj [Labels] (hpre : r.Pre) {a b : Nat} (ha : a ≤ 21616) (hb : b ≤ 21616) :
    r.off a = r.off b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [r.off_toNat hpre ha, r.off_toNat hpre hb, Nat.add_left_cancel_iff] at this
  · rintro rfl; rfl

theorem infix_take {α : Type} {l m : List α} {k n : Nat} (h : l.IsInfixAt m k) :
    (l.take n).IsInfixAt m k := by
  obtain ⟨t, ht⟩ := h
  refine ⟨l.drop n ++ t, ?_⟩
  rw [← List.append_assoc, List.take_append_drop, ht]

theorem infix_drop {α : Type} {l m : List α} {k n : Nat} (h : l.IsInfixAt m k) (hn : n ≤ l.length) :
    (l.drop n).IsInfixAt m (k + n) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ?_⟩
  rw [← List.drop_drop, ← ht, List.drop_append_of_le_length hn]

variable [ElfHost]

/-- **`b0`**: the saved registers, X29 and SP at `21520`, X9 `1040`. -/
theorem b0_spec (hp : PlacedIn code r.sec r.k) (hpre : r.Pre) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b1Offset ∧ Probe r 0 st.data)
      ⟨r.m0, r.pc NativeRustcArm.Sphincs.SphincsVerify.b0Offset⟩ := by
  have hk : b0.IsInfixAt (ElfHost.sectionProg r.sec) (r.k + NativeRustcArm.Sphincs.SphincsVerify.b0Offset) := b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hfm := frame_mapped0 r hpre (Kept.refl _) (a := 0) (n := 21616) (by decide)
  rw [Run.off_zero] at hfm
  have hwf : (Env.ofMachine r.m0 [(r.base, 21616)]).WF :=
    Env.wf_of ⟨hfm, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine r.m0 [(r.base, 21616)]) entryS r.m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ r.base_aligned hpre, trivial⟩
      (by
        show _ = r.base + BitVec.ofInt 64 (21616 : Nat)
        rw [ofInt_ofNat]
        simp [Run.base, frameSize])
      trivial trivial trivial trivial
  refine exec_then_elf hk run_b0 hwf hm fun st hm' hpc ↦ .done _ ⟨hpc, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hm'.sp.trans (base_add r 21520)
  · exact (hm'.regs .X9 _ rfl).trans (base_add r 1040)
  · exact (hm'.regs .X29 _ rfl).trans (base_add r 21520)
  · exact UInt64.toBitVec_inj.mp (hm'.regs .X0 _ rfl)
  · exact UInt64.toBitVec_inj.mp (hm'.regs .X1 _ rfl)
  · exact UInt64.toBitVec_inj.mp (hm'.regs .X2 _ rfl)
  · have hb : (Env.ofMachine r.m0 [(r.base, 21616)]).regions[0]? = some (r.base, 21616) := rfl
    refine bytesAt_words _ fun i hi ↦ ?_
    simp only [List.length_map, List.length_cons, List.length_nil] at hi
    rw [off_add]
    interval_cases i
    · exact bytesAt_reg (x := .X29) hm' hb (by decide) rfl
    · exact bytesAt_reg (x := .X30) hm' hb (by decide) rfl
    · exact bytesAt_reg (x := .X28) hm' hb (by decide) rfl
    · exact bytesAt_reg (x := .X27) hm' hb (by decide) rfl
    · exact bytesAt_reg (x := .X26) hm' hb (by decide) rfl
    · exact bytesAt_reg (x := .X25) hm' hb (by decide) rfl
    · exact bytesAt_reg (x := .X24) hm' hb (by decide) rfl
    · exact bytesAt_reg (x := .X23) hm' hb (by decide) rfl
    · exact bytesAt_reg (x := .X22) hm' hb (by decide) rfl
    · exact bytesAt_reg (x := .X21) hm' hb (by decide) rfl
    · exact bytesAt_reg (x := .X20) hm' hb (by decide) rfl
    · exact bytesAt_reg (x := .X19) hm' hb (by decide) rfl
  · exact sameOutside_hull hm' hwf (lo := 21520) (hi := 21616) rfl le_rfl rfl
  · exact hm'.kept hwf

/-- **The probe loop**: from `t ≤ 4` turns, the next turn; after the fifth, `b2`. -/
theorem b1_spec (hp : PlacedIn code r.sec r.k) (hpre : r.Pre) {t : Nat} (ht : t ≤ 4) {m : MachineData}
    (h : Probe r t m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ (st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b2Offset ∧ Probe r 5 st.data) ∨
      ∃ n' < 4 - t, ∃ t', t' ≤ 4 ∧ n' = 4 - t' ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b1Offset ∧ Probe r t' st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b1Offset⟩ := by
  obtain ⟨-, hsp, h9, h29, h0, h1, h2, hsv, hso, hkp⟩ := h
  obtain ⟨a, ha⟩ : ∃ a, 21520 - 4096 * (t + 1) = a := ⟨_, rfl⟩
  have ha' : a + 4096 = 21520 - 4096 * t := by omega
  have ha16 : a % 16 = 0 := by omega
  have hk : b1.IsInfixAt (ElfHost.sectionProg r.sec) (r.k + NativeRustcArm.Sphincs.SphincsVerify.b1Offset) := b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hfm := frame_mapped0 r hpre hkp (a := a) (n := 16) (by omega)
  have hwf : (Env.ofMachine m [(r.off a, 16)]).WF :=
    Env.wf_of ⟨hfm, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine m [(r.off a, 16)]) probeS m :=
    match_ofMachine ⟨rfl, fun _ ↦ off_aligned r hpre (by omega) (by omega), trivial⟩
      (by
        show _ = r.off a + BitVec.ofInt 64 (4096 : Nat)
        rw [off_add_int, hsp, ha'])
      trivial trivial trivial trivial
  refine exec_then_elf hk run_b1 hwf hm fun st hm' hpc ↦ ?_
  have hd : st.data.dmem = m.dmem := hm'.dmem_eq hwf rfl
  have hP : Probe r (t + 1) st.data := by
    rw [Probe, ha]
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, hd ▸ hsv, hd ▸ hso, hd ▸ hkp⟩
    · exact hm'.sp.trans (eval_ptr_off r (i := 0) rfl 0)
    · exact (hm'.regs .X9 _ rfl).trans h9
    · exact (hm'.regs .X29 _ rfl).trans h29
    · rw [← h0]; exact UInt64.toBitVec_inj.mp (hm'.regs .X0 _ rfl)
    · rw [← h1]; exact UInt64.toBitVec_inj.mp (hm'.regs .X1 _ rfl)
    · rw [← h2]; exact UInt64.toBitVec_inj.mp (hm'.regs .X2 _ rfl)
  have hc : ∀ env : Env, env = Env.ofMachine m [(r.off a, 16)] →
      (SBool.not (SBool.cmp CmpOp.eq RegWidth.W64 (ptr 0 0)
        (un (UnOp.extend { type := ExtendType.UXTX, amount := ExtendAmount.E0 }) RegWidth.W64
          (reg XReg.X9)))).eval env = !decide (t = 4) := by
    rintro env rfl
    have e1 : (ptr 0 0 : Sym).eval (Env.ofMachine m [(r.off a, 16)]) =
        r.off a := eval_ptr_off r (i := 0) rfl 0
    have e2 : (un (UnOp.extend { type := ExtendType.UXTX, amount := ExtendAmount.E0 }) RegWidth.W64
        (reg XReg.X9)).eval (Env.ofMachine m [(r.off a, 16)]) = r.off 1040 := by
      show BitVec.ofInt 64 (BitVec.apply_extend (m.regs.getXReg .X9).toBitVec
        { type := ExtendType.UXTX, amount := ExtendAmount.E0 }) = _
      simp only [BitVec.apply_extend, BitVec.unsigned, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
      exact h9
    have e3 : (r.off a == r.off 1040) = decide (t = 4) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, off_inj r hpre (by omega) (by decide)]
      omega
    simp only [SBool.eval, CmpOp.apply, Sym.low_W64, e1, e2, e3]
  simp only [PcOk] at hpc
  rw [hc _ rfl] at hpc
  by_cases h4 : t = 4
  · subst h4
    simp only [decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc
    exact .done _ (Or.inl ⟨hpc, hP⟩)
  · have h4' : (!decide (t = 4)) = true := by simpa using h4
    simp only [h4', ↓reduceIte] at hpc
    rw [hp.label NativeRustcArm.Sphincs.SphincsVerify.label_1_at] at hpc
    exact .done _ (Or.inr ⟨4 - (t + 1), by omega, t + 1, by omega, rfl, hpc, hP⟩)

/-- **`b2`**: allocates the last 1040 bytes, copies `pk` and `R`, sets up the openings' loop. -/
theorem b2_spec (hp : PlacedIn code r.sec r.k) (hpre : r.Pre) {m : MachineData} (h : Probe r 5 m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b3Offset ∧ AtOpen r 0 st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b2Offset⟩ := by
  obtain ⟨-, hsp, -, h29, h0, h1, h2, hsv, hso, hkp⟩ := h
  have hS : SameOutside r.m0.dmem m.dmem r.StackArea := hso.mono fun _ ↦ saved_area r hpre
  have hka : b2a.IsInfixAt (ElfHost.sectionProg r.sec) (r.k + b2Offset) :=
    (infix_take b2_in_code).trans hp.1 (by decide)
  have hwfa := wf_frame_pk r hpre hS hkp (a := 0) (n := 21616) (by decide) (fun _ ↦ 0)
  have hma : Match (Env.ofMachine m [(r.off 0, 21616), (r.pkPtr, 32)]) b2aS m :=
    match_ofMachine ⟨rfl, fun _ ↦ off_aligned r hpre (by decide) (by decide),
        ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩⟩
      (by show _ = r.off 0 + BitVec.ofInt 64 (1040 : Nat); rw [off_add_int, hsp])
      ⟨by show (m.regs.getXReg .X0).toBitVec = r.pkPtr + BitVec.ofInt 64 0; rw [h0]; simp [Run.pkPtr]; rfl,
        trivial⟩ trivial trivial trivial
  refine exec_then_elf hka run_b2a hwfa hma fun st1 hm1 hpc1 ↦ ?_
  have hb0a : (Env.ofMachine m [(r.off 0, 21616), (r.pkPtr, 32)]).regions[0]? = some (r.off 0, 21616) := rfl
  have hout1 := sameOutside_hull hm1 hwfa hb0a (lo := 448) (hi := 480) (by decide) (by decide)
  rw [off_add] at hout1
  have hF1 : r.Frame st1.data := by
    refine ⟨?_, ?_, keep r hpre hsv hout1 (Run.length_savedBytes _) (by right; decide) (by decide)
      (by decide), ?_, hkp.trans (hm1.kept hwfa)⟩
    · exact hm1.sp.trans ((eval_ptr_off r (i := 0) rfl 0).trans (Run.off_zero r))
    · exact (hm1.regs .X29 _ rfl).trans h29
    · exact (hS.trans hout1).mono fun p hp ↦ hp.elim id fun h ↦ (r.inRange_off hpre (by decide) h).1
  have hpk1 : BytesAt st1.data.dmem (r.off 448) r.pkBytes := by
    have := copy hm1 hb0a (o := 448) (r' := 1) (o' := 0) (n := 32) (by decide) (by decide) r.hpk
      (by show BytesAt m.dmem (r.pkPtr + BitVec.ofNat 64 0) r.pkBytes; rw [add_ofNat_zero]; exact bytesAt_pk r hpre hS)
    rwa [off_add] at this
  have h2_1 : (st1.data.regs.getXReg .X2).toBitVec = r.sigPtr := by
    rw [hm1.regs .X2 _ rfl]; show (m.regs.getXReg .X2).toBitVec = _; rw [h2]; rfl
  have h19_1 : (st1.data.regs.getXReg .X19).toBitVec = r.sigPtr := by
    rw [hm1.regs .X19 _ rfl]; show (m.regs.getXReg .X2).toBitVec = _; rw [h2]; rfl
  have h20_1 : (st1.data.regs.getXReg .X20).toBitVec = r.off 448 :=
    (hm1.regs .X20 _ rfl).trans (eval_ptr_off r (i := 0) rfl 448)
  have h21_1 : (st1.data.regs.getXReg .X21).toBitVec = r.msgPtr := by
    rw [hm1.regs .X21 _ rfl]; show (m.regs.getXReg .X1).toBitVec = _; rw [h1]; rfl
  have h22_1 : (st1.data.regs.getXReg .X22).toBitVec = r.off 484 :=
    (hm1.regs .X22 _ rfl).trans (eval_ptr_off r (i := 0) rfl 484)
  have h23_1 : (st1.data.regs.getXReg .X23).toBitVec = r.sigPtr + BitVec.ofNat 64 96 := by
    rw [hm1.regs .X23 _ rfl]; sym_simp; rw [Env.ofMachine_regs, h2]; rfl
  have h24_1 : (st1.data.regs.getXReg .X24).toBitVec = BitVec.ofNat 64 (2 ^ 64 - 4224 + 176 * 0) :=
    (hm1.regs .X24 _ rfl).trans rfl
  have h25_1 : (st1.data.regs.getXReg .X25).toBitVec = r.off 8640 :=
    (hm1.regs .X25 _ rfl).trans (eval_ptr_off r (i := 0) rfl 8640)
  have h26_1 : (st1.data.regs.getXReg .X26).toBitVec = BitVec.ofNat 64 4224 :=
    (hm1.regs .X26 _ rfl).trans rfl
  have h27_1 : (st1.data.regs.getXReg .X27).toBitVec = r.off 19008 :=
    (hm1.regs .X27 _ rfl).trans (eval_ptr_off r (i := 0) rfl 19008)
  -- Now b2b:
  have hkb : b2b.IsInfixAt (ElfHost.sectionProg r.sec) (r.k + (b2Offset + 17)) := by
    have := (infix_drop b2_in_code (n := 17) (by decide)).trans hp.1 (by decide)
    rwa [← Nat.add_assoc] at this
  have hwfb := wf_frame_sig r hpre hF1.2.2.2.1 hF1.2.2.2.2 (a := 0) (n := 21616) (s := 0) (k := 16)
    (by decide) (by decide) (by decide) (fun _ ↦ 0)
  have hmb : Match (Env.ofMachine st1.data [(r.off 0, 21616), (r.sigPtr + BitVec.ofNat 64 0, 16)]) b2bS st1.data :=
    match_ofMachine ⟨rfl, fun _ ↦ off_aligned r hpre (by decide) (by decide),
        ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩⟩
      (by show _ = r.off 0 + BitVec.ofInt 64 0; simp [Run.off_zero, hF1.1])
      ⟨by show _ = r.sigPtr + BitVec.ofNat 64 0 + BitVec.ofInt 64 0; simp [h2_1], trivial⟩
      trivial trivial trivial
  have hpc1' : st1.pc = ElfHost.addrOf r.sec (r.k + (b2Offset + 17)) := by
    rw [show st1.pc = _ from hpc1, Nat.add_assoc]; rfl
  refine exec_at_elf hkb run_b2b hwfb hpc1' hmb fun st2 hm2 hpc2 ↦ ?_
  have hb0b : (Env.ofMachine st1.data [(r.off 0, 21616), (r.sigPtr + BitVec.ofNat 64 0, 16)]).regions[0]? =
      some (r.off 0, 21616) := rfl
  have hout2 := sameOutside_hull hm2 hwfb hb0b (lo := 20048) (hi := 20064) (by decide) (by decide)
  rw [off_add] at hout2
  have hF2 : r.Frame st2.data :=
    hF1.of_block (hm2.sp.trans ((eval_ptr_off r (i := 0) rfl 0).trans (Run.off_zero r)))
      ((hm2.regs .X29 _ rfl).trans hF1.2.1) hout2 (fun _ hp ↦ r.inRange_off hpre (by decide) hp)
      (hm2.kept hwfb)
  have hpk2 : BytesAt st2.data.dmem (r.off 448) r.pkBytes :=
    keep r hpre hpk1 hout2 r.hpk (by left; decide) (by decide) (by decide)
  have hrand2 : BytesAt st2.data.dmem (r.off 20048) r.sig.randomizer := by
    rw [Run.sig, randomizer_fromBytes]
    have := copy hm2 hb0b (o := 20048) (r' := 1) (o' := 0) (n := 16) (by decide) (by decide)
      (length_slice_sigB r (a := 0) (n := 16) (by decide))
      (by
        show BytesAt st1.data.dmem (r.sigPtr + BitVec.ofNat 64 0 + BitVec.ofNat 64 0) _
        rw [add_ofNat_zero]
        exact bytesAt_sig_sub r hpre hF1.2.2.2.1 (s := 0) (k := 16) (by decide))
    rwa [off_add] at this
  have hpc2' : st2.pc = r.pc b3Offset := by
    rw [show st2.pc = _ from hpc2, Nat.add_assoc]; rfl
  refine .done _ ⟨hpc2', hF2, ⟨hpk2, hrand2, fun i hi ↦ by simp at hi⟩,
    (hm2.regs .X19 _ rfl).trans h19_1, (hm2.regs .X20 _ rfl).trans h20_1,
    (hm2.regs .X21 _ rfl).trans h21_1, (hm2.regs .X22 _ rfl).trans h22_1,
    (hm2.regs .X23 _ rfl).trans h23_1, (hm2.regs .X24 _ rfl).trans h24_1,
    (hm2.regs .X25 _ rfl).trans h25_1, (hm2.regs .X26 _ rfl).trans h26_1,
    (hm2.regs .X27 _ rfl).trans h27_1⟩

/-- **The parse's first part**: from the entry, `AtOpen 0` at `b3`. -/
theorem prologue_spec (hp : PlacedIn code r.sec r.k) (hpre : r.Pre) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b3Offset ∧ AtOpen r 0 st.data)
      ⟨r.m0, r.pc NativeRustcArm.Sphincs.SphincsVerify.b0Offset⟩ := by
  refine Eventually.bind_elf (b0_spec r hp hpre) fun st ⟨hpc, h0⟩ ↦ ?_
  have hloop := loop (tr := elfStep1 ElfHost.exe)
    (Q := fun st : MachineState ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b2Offset ∧ Probe r 5 st.data)
    (fun n st ↦ ∃ t, t ≤ 4 ∧ n = 4 - t ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b1Offset ∧ Probe r t st.data)
    (fun n st ⟨t, ht, hn, hpc, hP⟩ ↦ by
      obtain ⟨m, pc⟩ := st
      simp only at hpc
      subst hpc hn
      exact b1_spec r hp hpre ht hP)
    (n := 4) (s := st) ⟨0, by decide, rfl, hpc, h0⟩
  refine Eventually.bind_elf hloop fun st ⟨hpc, h5⟩ ↦ ?_
  obtain ⟨m, pc⟩ := st
  simp only at hpc
  subst hpc
  exact b2_spec r hp hpre h5

end

end NativeRustcArm.SphincsVerifyProof.Parse
