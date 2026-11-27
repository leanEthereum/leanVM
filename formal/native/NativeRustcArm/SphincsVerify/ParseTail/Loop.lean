module

public import NativeRustcArm.SphincsVerify.ParseTail.Facts

/-!
# The parse's copy loops

`b9`, `b17`, `b25` copy a layer's 1024 bytes of chain values from `r.sigPtr + src` to the frame's
`484`, 16 bytes a turn (`X8` the offset, `X9` the source, `D` the destination). A turn
(`copy_turn`) runs from the 16 destination bytes and the 16 source bytes as the regions; the loop
(`copy_loop`) takes `Facts` with none of the 1024 bytes to all of them, keeping the other facts.
-/

namespace NativeRustcArm.SphincsVerifyProof.ParseTail

open NativeRustc NativeRustcArm.Sym

@[expose] public section

/-- The loop's condition: another turn unless `X8 + 16` is `1024`. -/
def loopCond : SBool := .not (.cmp .eq .W64 (.bin .add .W64 (.reg .X8) (.lit 16)) (.lit 1024))

/-- What a turn's summary says: writes in the 16 destination bytes, each from a load of the source
byte, SP, X29, X9 and `D` kept, `X8` advanced by 16. -/
def turnOk (D : XReg) (S' : SState) : Bool :=
  S'.mem.all (fun w => w.r == 0 && decide (0 ≤ w.off) && decide (w.off + w.n ≤ 16)) &&
    Parse.copies S'.mem 0 0 1 0 16 && S'.sp == .sp &&
    S'.reg .X8 == some (.bin .add .W64 (.reg .X8) (.lit 16)) &&
    S'.reg .X29 == some (.reg .X29) && S'.reg .X9 == some (.reg .X9) && S'.reg D == some (.reg D)

end

public section

theorem cond_beq {t : Nat} (ht : t < 64) :
    (BitVec.ofNat 64 (16 * t) + BitVec.ofNat 64 16 == BitVec.ofNat 64 1024) = decide (t + 1 = 64) := by
  rw [← BitVec.ofNat_add, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
    omega
  · intro h
    congr 1
    omega

theorem take_snoc_16 (W : List UInt8) (t : Nat) :
    W.take (16 * t) ++ (W.drop (16 * t)).take 16 = W.take (16 * (t + 1)) := by
  rw [show 16 * (t + 1) = 16 * t + 16 by omega, List.take_add]

variable (r : Run) [ElfHost]

/-- **A turn of a copy loop** from `r.sigPtr + src` to `r.off 484`. -/
theorem copy_turn (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    {ds : List Directive} {j : Nat} (hk : ds.IsInfixAt Sphincs.SphincsVerify.code j) (hne : ds ≠ [])
    {lbl : Label} (hlbl : Sphincs.SphincsVerify.code[j]? = some (.label lbl))
    {D : XReg} {S' : SState} (hx : exec ds (loopS D) = some (S', .cond loopCond lbl))
    (hok : turnOk D S' = true)
    {src : Nat} (hsrc : src + 1024 ≤ 7740)
    {L : List (Nat × Nat × List UInt8)} (hL : disj L 484 1024 = true)
    {K : List (XReg × BitVec 64)} (hK : keptK (loopS D) S' K = true)
    {t : Nat} (ht : t < 64) {m : MachineData}
    (h : Facts r m ((484, 16 * t, (slice r.sigBytes src 1024).take (16 * t)) :: L)
      ((.X8, BitVec.ofNat 64 (16 * t)) :: (.X9, r.sigPtr + BitVec.ofNat 64 src) ::
        (D, r.off 484) :: K)) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦
      st.pc = (if t + 1 < 64 then r.pc j else r.pc (j + ds.length)) ∧
      Facts r st.data ((484, 16 * (t + 1), (slice r.sigBytes src 1024).take (16 * (t + 1))) :: L)
        ((.X8, BitVec.ofNat 64 (16 * (t + 1))) :: (.X9, r.sigPtr + BitVec.ofNat 64 src) ::
          (D, r.off 484) :: K))
      ⟨m, r.pc j⟩ := by
  obtain ⟨hF, ⟨⟨hTl, hTb⟩, hLL⟩, h8, h9, hD, hKK⟩ := h
  simp only at hTl hTb h8 h9 hD
  have hW : (slice r.sigBytes src 1024).length = 1024 := by simp [slice, r.hsig]; omega
  have hk' : ds.IsInfixAt (ElfHost.sectionProg r.sec) (r.k + j) := hk.trans hp.1 hne
  have hwf := Parse.wf_frame_sig r hpre hF.2.2.2.1 hF.2.2.2.2 (a := 484 + 16 * t) (n := 16)
    (s := src + 16 * t) (k := 16) (by omega) (by omega) (by decide) (fun _ ↦ 0)
  have hm : Match (Env.ofMachine m [(r.off (484 + 16 * t), 16),
      (r.sigPtr + BitVec.ofNat 64 (src + 16 * t), 16)]) (loopS D) m := by
    refine match_ofMachine ⟨rfl, fun h ↦ absurd h Bool.false_ne_true, rfl,
      fun h ↦ absurd h Bool.false_ne_true, trivial⟩ rfl trivial trivial trivial ⟨?_, ?_, trivial⟩
    · show (Sym.bin .add .W64 (.reg D) (.reg .X8)).eval _ = r.off (484 + 16 * t) + BitVec.ofInt 64 0
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, hD, h8,
        Parse.off_add, BitVec.ofInt_ofNat, BitVec.add_zero]
    · show (Sym.bin .add .W64 (.reg .X9) (.reg .X8)).eval _ =
        r.sigPtr + BitVec.ofNat 64 (src + 16 * t) + BitVec.ofInt 64 0
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, h9, h8,
        addr_add, BitVec.ofInt_ofNat, BitVec.add_zero]
  refine exec_then_elf hk' hx hwf hm fun st hm' hpc ↦ .done _ ?_
  simp only [turnOk, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨hw, hcp⟩, hsp'⟩, h8'⟩, h29'⟩, h9'⟩, hD'⟩ := hok
  have hout := Parse.sameOutside_hull hm' hwf (B := r.off (484 + 16 * t)) (sz := 16) (lo := 0)
    (hi := 16) rfl le_rfl hw
  rw [Parse.off_add, Nat.add_zero, Nat.sub_zero] at hout
  have hWb : BytesAt m.dmem (r.sigPtr + BitVec.ofNat 64 src) (slice r.sigBytes src 1024) :=
    Parse.bytesAt_sig_sub r hpre hF.2.2.2.1 hsrc
  have hnew := Parse.copy hm' (r := 0) (o := 0) (r' := 1) (o' := 0) (n := 16)
    (B := r.off (484 + 16 * t)) (sz := 16) rfl le_rfl hcp
    (bs := ((slice r.sigBytes src 1024).drop (16 * t)).take 16) (by simp [hW]; omega) (by
      have := Parse.bytesAt_sub hWb (k := 16 * t) (n := 16) (by omega)
      rw [addr_add] at this
      show BytesAt m.dmem (r.sigPtr + BitVec.ofNat 64 (src + 16 * t) + BitVec.ofNat 64 0) _
      rw [addr_add, Nat.add_zero]
      exact this)
  rw [Parse.off_add, Nat.add_zero] at hnew
  have hF' : r.Frame st.data :=
    hF.of_block (by rw [hm'.sp, hsp']; exact hF.1)
      (by rw [hm'.regs .X29 _ h29']; exact hF.2.1) hout
      (fun _ hp ↦ r.inRange_off hpre (by omega) hp) (hm'.kept hwf)
  have hTb' := Parse.keep r hpre hTb hout hTl (by omega) (by omega) (by omega)
  have hdst : BytesAt st.data.dmem (r.off 484) ((slice r.sigBytes src 1024).take (16 * (t + 1))) := by
    rw [← take_snoc_16]
    refine bytesAt_append hTb' ?_
    rw [hTl, Parse.off_add]
    exact hnew
  refine ⟨?_, hF', ⟨⟨by simp [hW]; omega, hdst⟩, BytesL.keep r hpre hout (by omega)
      (disj_mono hL (by omega) (by omega)) hLL⟩, ?_, ?_, ?_, RegsL.keep_block hm hm' hK hKK⟩
  · simp only [PcOk] at hpc
    rw [hpc]
    have hc : loopCond.eval (Env.ofMachine m [(r.off (484 + 16 * t), 16),
        (r.sigPtr + BitVec.ofNat 64 (src + 16 * t), 16)]) = decide (t + 1 < 64) := by
      simp only [loopCond, SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64,
        Env.ofMachine_regs, h8, cond_beq ht]
      by_cases h64 : t + 1 = 64
      · simp [h64]
      · simp [h64]; omega
    rw [hc, hp.label hlbl]
    by_cases h64 : t + 1 < 64
    · simp [h64, Run.pc]
    · simp [h64, Run.pc, Nat.add_assoc]
  · show (st.data.regs.getXReg .X8).toBitVec = _
    rw [hm'.regs .X8 _ h8']
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, h8, ← BitVec.ofNat_add]
    congr 1
  · show (st.data.regs.getXReg .X9).toBitVec = _
    rw [hm'.regs .X9 _ h9']
    exact h9
  · show (st.data.regs.getXReg D).toBitVec = _
    rw [hm'.regs D _ hD']
    exact hD

/-- **A copy loop**: from none of the 1024 bytes copied to all of them, at the loop's exit. -/
theorem copy_loop (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    {ds : List Directive} {j : Nat} (hk : ds.IsInfixAt Sphincs.SphincsVerify.code j) (hne : ds ≠ [])
    {lbl : Label} (hlbl : Sphincs.SphincsVerify.code[j]? = some (.label lbl))
    {D : XReg} {S' : SState} (hx : exec ds (loopS D) = some (S', .cond loopCond lbl))
    (hok : turnOk D S' = true)
    {src : Nat} (hsrc : src + 1024 ≤ 7740)
    {L : List (Nat × Nat × List UInt8)} (hL : disj L 484 1024 = true)
    {K : List (XReg × BitVec 64)} (hK : keptK (loopS D) S' K = true) {m : MachineData}
    (h : Facts r m ((484, 0, []) :: L)
      ((.X8, BitVec.ofNat 64 0) :: (.X9, r.sigPtr + BitVec.ofNat 64 src) :: (D, r.off 484) :: K)) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc (j + ds.length) ∧
      Facts r st.data ((484, 1024, slice r.sigBytes src 1024) :: L)
        ((.X9, r.sigPtr + BitVec.ofNat 64 src) :: (D, r.off 484) :: K)) ⟨m, r.pc j⟩ := by
  have hW : (slice r.sigBytes src 1024).length = 1024 := by simp [slice, r.hsig]; omega
  suffices key : ∀ n t, t + n = 63 → ∀ m, Facts r m ((484, 16 * t,
      (slice r.sigBytes src 1024).take (16 * t)) :: L)
      ((.X8, BitVec.ofNat 64 (16 * t)) :: (.X9, r.sigPtr + BitVec.ofNat 64 src) ::
        (D, r.off 484) :: K) →
      Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc (j + ds.length) ∧
        Facts r st.data ((484, 1024, slice r.sigBytes src 1024) :: L)
          ((.X9, r.sigPtr + BitVec.ofNat 64 src) :: (D, r.off 484) :: K)) ⟨m, r.pc j⟩ from
    key 63 0 rfl m h
  intro n
  induction n with
  | zero =>
    intro t ht m hm
    refine Eventually.mono_elf (copy_turn r hp hpre hk hne hlbl hx hok hsrc hL hK (t := t)
      (by omega) hm) fun st ⟨hpc, hF, hb, hr⟩ ↦ ⟨?_, hF, ?_, hr.2⟩
    · rw [hpc, ite_eq_right_iff.mpr (fun h ↦ absurd h (by omega))]
    · obtain ⟨⟨h2l, h2⟩, h3⟩ := hb
      refine ⟨⟨hW, ?_⟩, h3⟩
      rwa [show 16 * (t + 1) = 1024 by omega, List.take_of_length_le (by omega)] at h2
  | succ n ih =>
    intro t ht m hm
    refine Eventually.bind_elf (copy_turn r hp hpre hk hne hlbl hx hok hsrc hL hK (t := t)
      (by omega) hm) fun st ⟨hpc, hst⟩ ↦ ?_
    rw [ite_eq_left_iff.mpr (fun h ↦ absurd (by omega) h)] at hpc
    obtain ⟨m', pc⟩ := st
    simp only at hpc
    subst hpc
    exact ih (t + 1) (by omega) m' hst

end

end NativeRustcArm.SphincsVerifyProof.ParseTail
