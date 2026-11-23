module

public import NativeRustcArm.SphincsVerify.Parse.Glue
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify

/-!
# The parse, part 1: the prologue and the signature's `memset` (`b0 .. b2`)

`b0` saves X29, X30, X28 ... X19 at `SP₀ - 96` and points X29 there; the probe loop `b1` lowers SP
a page at a time (7 turns, region 0 the 16 bytes at the new SP); `b2` allocates the last 608
bytes, stores the message's words 4 .. 7 at `432`, keeps the context in X19, words 0 .. 3 in
X21, X23, X24, X22, and calls `memset` on the signature's 7740 bytes at `468`. Result: `AtWords`
at `b3` (directive 32).
-/

namespace NativeRustcArm.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify
  LeanVM.Protocol.KeccakHash

@[expose] public section

/-- At the entry: region 0 the frame, SP its top. -/
def entryS : SState := init [(29376, true)] (.ptr 0 29376)

/-- In the probe loop: region 0 the 16 bytes at the next page, SP a page above them. -/
def probeS : SState := init [(16, true)] (.ptr 0 4096)

/-- At `b2`: region 0 the frame (SP at `608`), region 1 the input (X0 1024 below it). -/
def b2S : SState := init [(29376, true), (7816, false)] (.ptr 0 608) [(.X0, .ptr 1 (-1024))]

/-- **At `b3`**, after the signature's `memset`: the frame, the message at `432`; X19 the context,
X20 `468`, X21, X23, X24, X22 the words 0 .. 3, X25 `4564`. -/
def AtWords (r : Run) (m : MachineData) : Prop :=
  r.Frame m ∧ BytesAt m.dmem (r.off 432) r.msg ∧ Run.RegIs m .X19 r.m0.regs.X0.toBitVec ∧
    Run.RegIs m .X20 (r.off 468) ∧ Run.RegIs m .X21 (r.w 0).toBitVec ∧
    Run.RegIs m .X22 (r.w 3).toBitVec ∧ Run.RegIs m .X23 (r.w 1).toBitVec ∧
    Run.RegIs m .X24 (r.w 2).toBitVec ∧ Run.RegIs m .X25 (r.off 4564)

/-- In the probe loop after `t` turns. -/
def Probe (r : Run) (t : Nat) (m : MachineData) : Prop :=
  t ≤ 7 ∧ m.regs.SP.toBitVec = r.off (29280 - 4096 * t) ∧ Run.RegIs m .X9 (r.off 608) ∧
    Run.RegIs m .X29 (r.off 29280) ∧ m.regs.getXReg .X0 = r.m0.regs.getXReg .X0 ∧
    BytesAt m.dmem (r.off 29280) (savedBytes r.m0) ∧
    SameOutside r.m0.dmem m.dmem (InRange (r.off 29280) 96) ∧ Kept r.m0.dmem m.dmem

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 probeS
sym_block run_b2 := exec b2 b2S

public section

theorem ofInt_ofNat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  simp

variable (r : Run)

theorem base_add (a : Nat) : r.base + BitVec.ofInt 64 (a : Int) = r.off a := by
  rw [ofInt_ofNat]; rfl

theorem off_add_int (a b : Nat) : r.off a + BitVec.ofInt 64 (b : Int) = r.off (a + b) := by
  rw [ofInt_ofNat, off_add]

theorem off_inj [Labels] (hpre : r.Pre) {a b : Nat} (ha : a ≤ 29376) (hb : b ≤ 29376) :
    r.off a = r.off b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [r.off_toNat hpre ha, r.off_toNat hpre hb, Nat.add_left_cancel_iff] at this
  · rintro rfl; rfl

theorem input_sub : r.input + BitVec.ofNat 64 (8 * 0) + BitVec.ofInt 64 (-1024) =
    r.m0.regs.X0.toBitVec := by
  unfold Run.input
  rw [BitVec.add_assoc, BitVec.add_assoc, show BitVec.ofNat 64 1024 + (BitVec.ofNat 64 (8 * 0) +
    BitVec.ofInt 64 (-1024)) = 0 by decide]
  simp

theorem wb_one (w : Nat → UInt64) (s : Nat) : wb w s 1 = wordBytes (w s) := by
  simp [wb, Native.Keccak.wordsBytes]

theorem bytesAt_wb' [Labels] (hpre : r.Pre) {d : DataMem} (hS : SameOutside r.m0.dmem d r.StackArea)
    {s o k n : Nat} (ho : 8 * s + o = 8 * k) (h : k + n ≤ 977) :
    BytesAt d (r.input + BitVec.ofNat 64 (8 * s) + BitVec.ofNat 64 o) (wb r.w k n) := by
  rw [addr_add, ho]
  exact bytesAt_wb r hpre hS h

theorem word_at [Labels] (hpre : r.Pre) {d : DataMem} (hS : SameOutside r.m0.dmem d r.StackArea)
    {s o k : Nat} (ho : 8 * s + o = 8 * k) (h : k < 977) :
    BytesAt d (r.input + BitVec.ofNat 64 (8 * s) + BitVec.ofNat 64 o) (wordBytes (r.w k)) := by
  rw [← wb_one]
  exact bytesAt_wb' r hpre hS ho h

variable [NativeRustcArm.Host]

/-- **`b0`**: the saved registers, X29 and SP at `29280`, X9 `608`. -/
theorem b0_spec (hp : Placed code r.k) (hpre : r.Pre) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b1Offset ∧ Probe r 0 st.data)
      ⟨r.m0, r.pc NativeRustcArm.Sphincs.SphincsVerify.b0Offset⟩ := by
  have hk : b0.IsInfixAt NativeRustcArm.Host.prog (r.k + NativeRustcArm.Sphincs.SphincsVerify.b0Offset) := b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hfm := frame_mapped0 r hpre (Kept.refl _) (a := 0) (n := 29376) (by decide)
  rw [Run.off_zero] at hfm
  have hwf : (Env.ofMachine r.m0 [(r.base, 29376)]).WF :=
    Env.wf_of ⟨hfm, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine r.m0 [(r.base, 29376)]) entryS r.m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ r.base_aligned hpre, trivial⟩
      (by
        show _ = r.base + BitVec.ofInt 64 (29376 : Nat)
        rw [ofInt_ofNat]
        simp [Run.base, frameSize])
      trivial trivial trivial trivial
  refine exec_then hk run_b0 hwf hm fun st hm' hpc ↦ .done _ ⟨hpc, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hm'.sp.trans (base_add r 29280)
  · exact (hm'.regs .X9 _ rfl).trans (base_add r 608)
  · exact (hm'.regs .X29 _ rfl).trans (base_add r 29280)
  · exact UInt64.toBitVec_inj.mp (hm'.regs .X0 _ rfl)
  · have hb : (Env.ofMachine r.m0 [(r.base, 29376)]).regions[0]? = some (r.base, 29376) := rfl
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
  · exact sameOutside_hull hm' hwf (lo := 29280) (hi := 29376) rfl le_rfl rfl
  · exact hm'.kept hwf

/-- **The probe loop**: from `t ≤ 6` turns, the next turn; after the seventh, `b2`. -/
theorem b1_spec (hp : Placed code r.k) (hpre : r.Pre) {t : Nat} (ht : t ≤ 6) {m : MachineData}
    (h : Probe r t m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ (st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b2Offset ∧ Probe r 7 st.data) ∨
      ∃ n' < 6 - t, ∃ t', t' ≤ 6 ∧ n' = 6 - t' ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b1Offset ∧ Probe r t' st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b1Offset⟩ := by
  obtain ⟨-, hsp, h9, h29, h0, hsv, hso, hkp⟩ := h
  obtain ⟨a, ha⟩ : ∃ a, 29280 - 4096 * (t + 1) = a := ⟨_, rfl⟩
  have ha' : a + 4096 = 29280 - 4096 * t := by omega
  have ha16 : a % 16 = 0 := by omega
  have hk : b1.IsInfixAt NativeRustcArm.Host.prog (r.k + NativeRustcArm.Sphincs.SphincsVerify.b1Offset) := b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hfm := frame_mapped0 r hpre hkp (a := a) (n := 16) (by omega)
  have hwf : (Env.ofMachine m [(r.off a, 16)]).WF :=
    Env.wf_of ⟨hfm, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine m [(r.off a, 16)]) probeS m :=
    match_ofMachine ⟨rfl, fun _ ↦ off_aligned r hpre (by omega) (by omega), trivial⟩
      (by
        show _ = r.off a + BitVec.ofInt 64 (4096 : Nat)
        rw [off_add_int, hsp, ha'])
      trivial trivial trivial trivial
  refine exec_then hk run_b1 hwf hm fun st hm' hpc ↦ ?_
  have hd : st.data.dmem = m.dmem := hm'.dmem_eq hwf rfl
  have hP : Probe r (t + 1) st.data := by
    rw [Probe, ha]
    refine ⟨by omega, ?_, ?_, ?_, ?_, hd ▸ hsv, hd ▸ hso, hd ▸ hkp⟩
    · exact hm'.sp.trans (eval_ptr_off r (i := 0) rfl 0)
    · exact (hm'.regs .X9 _ rfl).trans h9
    · exact (hm'.regs .X29 _ rfl).trans h29
    · rw [← h0]; exact UInt64.toBitVec_inj.mp (hm'.regs .X0 _ rfl)
  have hc : ∀ env : Env, env = Env.ofMachine m [(r.off a, 16)] →
      (SBool.not (SBool.cmp CmpOp.eq RegWidth.W64 (ptr 0 0)
        (un (UnOp.extend { type := ExtendType.UXTX, amount := ExtendAmount.E0 }) RegWidth.W64
          (reg XReg.X9)))).eval env = !decide (t = 6) := by
    rintro env rfl
    have e1 : (ptr 0 0 : Sym).eval (Env.ofMachine m [(r.off a, 16)]) =
        r.off a := eval_ptr_off r (i := 0) rfl 0
    have e2 : (un (UnOp.extend { type := ExtendType.UXTX, amount := ExtendAmount.E0 }) RegWidth.W64
        (reg XReg.X9)).eval (Env.ofMachine m [(r.off a, 16)]) = r.off 608 := by
      show BitVec.ofInt 64 (BitVec.apply_extend (m.regs.getXReg .X9).toBitVec
        { type := ExtendType.UXTX, amount := ExtendAmount.E0 }) = _
      simp only [BitVec.apply_extend, BitVec.unsigned, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
      exact h9
    have e3 : (r.off a == r.off 608) = decide (t = 6) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, off_inj r hpre (by omega) (by decide)]
      omega
    simp only [SBool.eval, CmpOp.apply, Sym.low_W64, e1, e2, e3]
  simp only [PcOk] at hpc
  rw [hc _ rfl] at hpc
  by_cases h6 : t = 6
  · subst h6
    simp only [decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc
    exact .done _ (Or.inl ⟨hpc, hP⟩)
  · have h6' : (!decide (t = 6)) = true := by simpa using h6
    simp only [h6', ↓reduceIte] at hpc
    rw [hp.label NativeRustcArm.Sphincs.SphincsVerify.label_1_at] at hpc
    exact .done _ (Or.inr ⟨6 - (t + 1), by omega, t + 1, by omega, rfl, hpc, hP⟩)

/-- **`b2` and the signature's `memset`**. -/
theorem b2_spec (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {m : MachineData}
    (h : Probe r 7 m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b3Offset ∧ AtWords r st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b2Offset⟩ := by
  obtain ⟨-, hsp, -, h29, h0, hsv, hso, hkp⟩ := h
  have hS : SameOutside r.m0.dmem m.dmem r.StackArea := hso.mono fun _ ↦ saved_area r hpre
  have hk : b2.IsInfixAt NativeRustcArm.Host.prog (r.k + NativeRustcArm.Sphincs.SphincsVerify.b2Offset) := b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := wf_frame_input r hpre hS hkp (a := 0) (n := 29376) (s := 0) (k := 7816) (by decide)
    (by decide) (by decide) (fun _ ↦ 0)
  have hm : Match (Env.ofMachine m [(r.off 0, 29376), (r.input + BitVec.ofNat 64 (8 * 0), 7816)])
      b2S m :=
    match_ofMachine ⟨rfl, fun _ ↦ off_aligned r hpre (by decide) (by decide),
        ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩⟩
      (by
        show _ = r.off 0 + BitVec.ofInt 64 (608 : Nat)
        rw [off_add_int, hsp])
      ⟨by
        show _ = r.input + BitVec.ofNat 64 (8 * 0) + BitVec.ofInt 64 (-1024)
        rw [h0, input_sub r]; rfl, trivial⟩ trivial trivial trivial
  refine exec_then hk run_b2 hwf hm fun st hm' hpc ↦ ?_
  have hb0 : (Env.ofMachine m [(r.off 0, 29376), (r.input + BitVec.ofNat 64 (8 * 0), 7816)]).regions[0]? =
      some (r.off 0, 29376) := rfl
  have hout := sameOutside_hull hm' hwf hb0 (lo := 432) (hi := 464) (by decide) rfl
  rw [off_add] at hout
  have hF : r.Frame st.data := by
    refine ⟨?_, ?_, keep r hpre hsv hout (Run.length_savedBytes _) (by right; decide) (by decide)
      (by decide), ?_,
      hkp.trans (hm'.kept hwf)⟩
    · exact hm'.sp.trans ((eval_ptr_off r (i := 0) rfl 0).trans (Run.off_zero r))
    · exact (hm'.regs .X29 _ rfl).trans h29
    · exact (hS.trans hout).mono fun p hp ↦ hp.elim id fun h ↦ (r.inRange_off hpre (by decide) h).1
  have hx0 : (st.data.regs.getXReg .X0).toBitVec = r.off 468 := by
    exact (hm'.regs .X0 _ rfl).trans (eval_ptr_off r (i := 0) rfl 468)
  have hx2 : (st.data.regs.getXReg .X2).toNat = 7740 := by
    show (st.data.regs.getXReg .X2).toBitVec.toNat = 7740
    rw [hm'.regs .X2 _ rfl]
    rfl
  refine memset_frame r hpre hc hpc hF hx0 hx2 (by decide) fun st' hpc' hF' hS' hout' ↦ ?_
  have hmsg : BytesAt st.data.dmem (r.off 432) r.msg := by
    have := copy hm' hb0 (o := 432) (r' := 1) (o' := 32) (n := 32) (by decide) rfl rfl
      (bytesAt_wb' r hpre hS (s := 0) (o := 32) (k := 4) (n := 4) (by decide) (by decide))
    rwa [off_add] at this
  have hreg : ∀ x v, (st.data.regs.getXReg x).toBitVec = v → calleeSaved x = true →
      Run.RegIs st'.data x v := fun x v h hx ↦ by rw [Run.RegIs, hS'.1 x hx]; exact h
  have hE : ∀ o k, 8 * 0 + o = 8 * k → k < 977 →
      (Env.ofMachine m [(r.off 0, 29376), (r.input + BitVec.ofNat 64 (8 * 0), 7816)]).load 1 o 8 =
        (r.w k).toBitVec := fun o k ho hk ↦ load_word (word_at r hpre hS ho hk)
  refine .done _ ⟨hpc', hF', keep r hpre hmsg hout' (length_wb r.w 4 4) (by left; decide) (by decide)
    (by decide),
    hreg .X19 _ ?_ rfl, hreg .X20 _ ?_ rfl, hreg .X21 _ ?_ rfl, hreg .X22 _ ?_ rfl,
    hreg .X23 _ ?_ rfl, hreg .X24 _ ?_ rfl, hreg .X25 _ ?_ rfl⟩
  · exact (hm'.regs .X19 _ rfl).trans (input_sub r)
  · exact (hm'.regs .X20 _ rfl).trans (eval_ptr_off r (i := 0) rfl 468)
  · exact (hm'.regs .X21 _ rfl).trans (hE 0 0 rfl (by decide))
  · exact (hm'.regs .X22 _ rfl).trans (hE 24 3 rfl (by decide))
  · exact (hm'.regs .X23 _ rfl).trans (hE 8 1 rfl (by decide))
  · exact (hm'.regs .X24 _ rfl).trans (hE 16 2 rfl (by decide))
  · exact (hm'.regs .X25 _ rfl).trans (eval_ptr_off r (i := 0) rfl 4564)

/-- **The parse's first part**: from the entry, `AtWords` at `b3`. -/
theorem prologue_spec (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b3Offset ∧ AtWords r st.data)
      ⟨r.m0, r.pc NativeRustcArm.Sphincs.SphincsVerify.b0Offset⟩ := by
  refine Eventually.bind (b0_spec r hp hpre) fun st ⟨hpc, h0⟩ ↦ ?_
  have hloop := loop (tr := step1 NativeRustcArm.Host.exe)
    (Q := fun st : MachineState ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b2Offset ∧ Probe r 7 st.data)
    (fun n st ↦ ∃ t, t ≤ 6 ∧ n = 6 - t ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b1Offset ∧ Probe r t st.data)
    (fun n st ⟨t, ht, hn, hpc, hP⟩ ↦ by
      obtain ⟨m, pc⟩ := st
      simp only at hpc
      subst hpc hn
      exact b1_spec r hp hpre ht hP)
    (n := 6) (s := st) ⟨0, by decide, rfl, hpc, h0⟩
  refine Eventually.bind hloop fun st ⟨hpc, h7⟩ ↦ ?_
  obtain ⟨m, pc⟩ := st
  simp only at hpc
  subst hpc
  exact b2_spec r hp hc hpre h7

end

end NativeRustcArm.SphincsVerifyProof.Parse
