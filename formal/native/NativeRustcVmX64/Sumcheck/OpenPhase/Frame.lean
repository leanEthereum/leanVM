module

public import NativeRustcVmX64.Sumcheck.OpenPhase.Exec
public import NativeRustcVmX64.Spec.Sumcheck
public import NativeRustcVm.Sumcheck.OpenPhase

/-!
# `open_phase`: the frame and the exits (x86-64)

The 176-byte frame below the entry's RSP (`fa`): `FrO m0 o m`, the frame with RSP at offset `o`
and memory changed only in `open_phase`'s stack. Inputs apart from the stack are kept
(`keepB`); a block of the frame keeps `FrO` (`FrO.block`, `frTest`); a call from the frame's
base writing 32 bytes of the frame keeps it (`FrO.call`). The exits: `exit_fail8` (`b8`, `b9`),
`exit_fail` (`b22`, `b9`): `None` at the output; `exit_rows` (`b21`, `b9`): the rows.
-/

namespace NativeRustcVmX64.Sumcheck.OpenPhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.OpenPhase NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck NativeVm NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVm.Sumcheck LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- The output, the root, the positions, the phase: RDI, RSI, R8, the stack argument. -/
abbrev outO (m0 : MachineData) : BitVec 64 := reg m0 .rdi
abbrev rootO (m0 : MachineData) : BitVec 64 := reg m0 .rsi
abbrev posO (m0 : MachineData) : BitVec 64 := reg m0 .r8
abbrev phO (m0 : MachineData) : BitVec 64 := stackArg m0 0

/-- The frame: 176 bytes below the entry's RSP. -/
abbrev fa (m0 : MachineData) : BitVec 64 := stackBelow m0 176

/-- `open_phase`'s stack. -/
abbrev Stk (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (stackBelow m0 openPhaseStack) openPhaseStack q

/-- **The frame**, RSP at offset `o`, memory changed only in the stack. -/
structure FrO (m0 : MachineData) (o : Nat) (m : MachineData) : Prop where
  frame : Frame m0 176 slots o m
  same : NativeRustcVm.SameOutside m0.dmem m.dmem (Stk m0)

/-- `PhaseAt` with its height `h` and width `w`. -/
def PhaseHW (d : Mem 64) (b : BitVec 64) (P : Array OpeningW) (h w : Nat) : Prop :=
  h ≤ wireMaxHeight ∧ w ≤ wireMaxLeafWords ∧ P.size ≤ wireMaxQueries ∧
    NativeRustcVm.WordAt d b P.size.toUInt64 ∧ NativeRustcVm.WordAt d (off b 8) h.toUInt64 ∧
    NativeRustcVm.WordAt d (off b 16) w.toUInt64 ∧
    ∀ j (hj : j < P.size), OpeningAt d (off b (8 * (3 + j * openingWords))) h w P[j]

/-- What the shape check asks and the count's. -/
def ShapeOk (P : Array OpeningW) (Q : Array UInt64) (h w height width : Nat) : Prop :=
  (P.size = 0 ∨ (w = width ∧ h = height)) ∧ P.size = Q.size

end

public section

theorem openPhaseStack_eq : openPhaseStack = 1184 := rfl
theorem keccak256WordsStack_eq : keccak256WordsStack = 768 := rfl
theorem climbStack_eq : climbStack = 1008 := rfl

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 176 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide
theorem slots_ge : ∀ p ∈ slots, 128 ≤ p.1 := by decide

/-! ## The model -/

/-- The openings' shape, from `PhaseHW`. -/
theorem PhaseHW.shape {d : Mem 64} {b : BitVec 64} {P : Array OpeningW} {h w : Nat}
    (hph : PhaseHW d b P h w) : ∀ j (hj : j < P.size), P[j].leaf.size = w ∧ P[j].path.size = h :=
  fun j hj ↦ ⟨(hph.2.2.2.2.2.2 j hj).1, (hph.2.2.2.2.2.2 j hj).2.1⟩

/-- **The model rejects** where the checks fail. -/
theorem openPhase_none {R : Digest} {height width : Nat} {Q : Array UInt64} {P : Array OpeningW}
    {d : Mem 64} {b : BitVec 64} {h w : Nat} (hph : PhaseHW d b P h w)
    (hn : ¬ ((P.size = 0 ∨ (w = width ∧ h = height)) ∧ P.size = Q.size ∧
      PositionsOk P Q P.size)) :
    openPhase R height width Q P = none := by
  rw [openPhase_eq hph.shape, ite_eq_right hn]

/-- The model, the checks passed: the climbs decide. -/
theorem openPhase_climbs {R : Digest} {height width : Nat} {Q : Array UInt64} {P : Array OpeningW}
    {d : Mem 64} {b : BitVec 64} {h w : Nat} (hph : PhaseHW d b P h w)
    (hsh : ShapeOk P Q h w height width) (hpos : PositionsOk P Q P.size) :
    openPhase R height width Q P =
      if ClimbsOk R P P.size then some (P.map (·.leaf)) else none := by
  rw [openPhase_eq hph.shape, ite_eq_left ⟨hsh.1, hsh.2, hpos⟩]

theorem toUInt64_toNat {x : Nat} (hx : x < 2 ^ 64) : x.toUInt64.toBitVec.toNat = x := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hx

theorem toUInt64_beq {x : Nat} (hx : x < 2 ^ 64) (y : BitVec 64) :
    (x.toUInt64.toBitVec == y) = decide (x = y.toNat) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · rintro rfl; exact (toUInt64_toNat hx).symm
  · intro h; apply BitVec.eq_of_toNat_eq; rw [toUInt64_toNat hx]; exact h

theorem beq_toUInt64 {x : Nat} (hx : x < 2 ^ 64) (y : BitVec 64) :
    (y == x.toUInt64.toBitVec) = decide (x = y.toNat) := by
  rw [← toUInt64_beq hx, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact eq_comm

theorem bv_beq_zero (y : BitVec 64) : (y == 0#64) = decide (y.toNat = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  exact ⟨fun h ↦ by rw [h]; rfl, fun h ↦ BitVec.eq_of_toNat_eq h⟩

/-- `(a ^ b) | (c ^ d)` is zero exactly when `a = b` and `c = d`. -/
theorem xor_or_beq (a b c d : BitVec 64) :
    ((a ^^^ b) ||| (c ^^^ d) == 0#64) = (a == b && c == d) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    refine ⟨BitVec.eq_of_getLsbD_eq fun i _ ↦ ?_, BitVec.eq_of_getLsbD_eq fun i _ ↦ ?_⟩ <;>
    · have := congrArg (fun x : BitVec 64 ↦ x.getLsbD i) h
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_zero] at this
      revert this
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> cases d.getLsbD i <;>
        decide
  · rintro ⟨rfl, rfl⟩
    simp

/-! ## The geometry -/

variable {m0 m d d' : MachineData}

theorem fa_toNat (hst : StackOk m0 openPhaseStack) : (fa m0).toNat = (rspOf m0).toNat - 176 :=
  stackBelow_toNat (by have := hst.1; rw [openPhaseStack_eq] at this; omega)

theorem stk_toNat (hst : StackOk m0 openPhaseStack) :
    (stackBelow m0 openPhaseStack).toNat = (rspOf m0).toNat - 1184 :=
  stackBelow_toNat hst.1

theorem off_fa_toNat (hst : StackOk m0 openPhaseStack) {o : Nat} (ho : o < 184) :
    (off (fa m0) o).toNat = (rspOf m0).toNat - 176 + o := by
  have := hst.1; have := hst.2.1
  rw [openPhaseStack_eq] at *
  rw [toNat_off (by rw [fa_toNat hst]; omega), fa_toNat hst]

theorem fa_noWrap (hst : StackOk m0 openPhaseStack) : NativeRustcVm.NoWrap (fa m0) (176 + 8) :=
  frame_noWrap hst (by decide)

/-- A callee's stack below the frame. -/
theorem callee_toNat (hst : StackOk m0 openPhaseStack) (hsp : rspOf d = fa m0) {N' : Nat}
    (hN' : 176 + N' ≤ openPhaseStack) :
    (stackBelow d N').toNat = (rspOf m0).toNat - 176 - N' := by
  have := hst.1
  rw [stackBelow_callee hsp (by omega), stackBelow_toNat (by omega)]
  omega

/-- What is apart from the stack is apart from a callee's. -/
theorem apart_callee' (hst : StackOk m0 openPhaseStack) (hsp : rspOf d = fa m0) {N' : Nat}
    (hN' : 176 + N' ≤ openPhaseStack) {x : BitVec 64} {n : Nat}
    (h : NativeRustcVm.Apart x n (stackBelow m0 openPhaseStack) (openPhaseStack + 8)) :
    NativeRustcVm.Apart x n (stackBelow d N') (N' + 8) :=
  apart_callee h hsp hst.1 hN'

/-- The frame's bytes from `o ≥ 8` are apart from a callee's stack. -/
theorem fa_apart_callee (hst : StackOk m0 openPhaseStack) (hsp : rspOf d = fa m0) {N' : Nat}
    (hN' : 176 + N' ≤ openPhaseStack) {o n : Nat} (ho : 8 ≤ o) (hon : o + n ≤ 176) :
    NativeRustcVm.Apart (off (fa m0) o) n (stackBelow d N') (N' + 8) := by
  have := hst.1; have := hst.2.1
  unfold NativeRustcVm.Apart
  rw [off_fa_toNat hst (by omega), callee_toNat hst hsp hN']
  rw [openPhaseStack_eq] at *
  omega

theorem fa_noWrap' (hst : StackOk m0 openPhaseStack) {o n : Nat} (hon : o + n ≤ 184)
    (ho : o < 184) :
    NativeRustcVm.NoWrap (off (fa m0) o) n := by
  have := hst.1; have := hst.2.1
  unfold NativeRustcVm.NoWrap
  rw [off_fa_toNat hst (by omega)]
  rw [openPhaseStack_eq] at *
  omega

/-- What is apart from the stack is apart from the frame's bytes `o` to `o + n`. -/
theorem apart_fa (hst : StackOk m0 openPhaseStack) {x : BitVec 64} {n o k : Nat}
    (h : NativeRustcVm.Apart x n (stackBelow m0 openPhaseStack) (openPhaseStack + 8))
    (hk : o + k ≤ 184) (ho : o < 184) : NativeRustcVm.Apart x n (off (fa m0) o) k := by
  have := hst.1; have := hst.2.1
  unfold NativeRustcVm.Apart at h ⊢
  rw [stk_toNat hst] at h
  rw [off_fa_toNat hst (by omega)]
  rw [openPhaseStack_eq] at *
  omega

/-- The frame's bytes below the return address are in the stack. -/
theorem fa_stk (hst : StackOk m0 openPhaseStack) {q : BitVec 64}
    (h : NativeRustcVm.InRange (fa m0) 176 q) : Stk m0 q :=
  inRange_frame_stack hst.2.1 hst.1 (by decide) h

theorem fa_off_stk (hst : StackOk m0 openPhaseStack) {o n : Nat} (hon : o + n ≤ 176)
    {q : BitVec 64} (h : NativeRustcVm.InRange (off (fa m0) o) n q) : Stk m0 q :=
  fa_stk hst (inRange_of_off ((fa_noWrap hst).mono (by omega)) hon h)

/-- A callee's stack is in `open_phase`'s. -/
theorem callee_stk (hst : StackOk m0 openPhaseStack) (hsp : rspOf d = fa m0) {N' : Nat}
    (hN' : 176 + N' ≤ openPhaseStack) {q : BitVec 64}
    (h : NativeRustcVm.InRange (stackBelow d N') N' q) : Stk m0 q :=
  (inRange_callee hsp hst.2.1 hst.1 hN' h).1

/-- A callee's output (`o` to `o + 32` of the frame) and stack miss the frame's other bytes. -/
theorem notR (hst : StackOk m0 openPhaseStack) (hsp : rspOf d = fa m0) {N' : Nat}
    (hN' : 176 + N' ≤ openPhaseStack) {o j : Nat} (ho : o + 32 ≤ 184) (hj : j < 184)
    (hjo : j < o ∨ o + 32 ≤ j) :
    ¬ (NativeRustcVm.InRange (off (fa m0) o) 32 (off (fa m0) j) ∨
      NativeRustcVm.InRange (stackBelow d N') N' (off (fa m0) j)) := by
  have := hst.1; have := hst.2.1
  have hc := callee_toNat hst hsp hN'
  rw [openPhaseStack_eq] at *
  rw [inRange_iff' (fa_noWrap' hst ho (by omega)), inRange_iff' (by
      unfold NativeRustcVm.NoWrap; rw [hc]; omega),
    off_fa_toNat hst (by omega), off_fa_toNat hst (by omega), hc]
  omega

/-! ## Inputs kept -/

/-- **Bytes apart from the stack kept**. -/
theorem keepB (hst : StackOk m0 openPhaseStack)
    (hs : NativeRustcVm.SameOutside m0.dmem d.dmem (Stk m0)) {x : BitVec 64} {n : Nat}
    (hnw : NativeRustcVm.NoWrap x n)
    (hap : NativeRustcVm.Apart x n (stackBelow m0 openPhaseStack) (openPhaseStack + 8))
    {bs : List UInt8} (hle : bs.length ≤ n) (h : NativeRustcVm.BytesAt m0.dmem x bs) :
    NativeRustcVm.BytesAt d.dmem x bs :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi hq ↦
    not_inRange_of_apart hap hnw (noWrap_stackBelow hst)
      (inRange_off_self (by omega) (by unfold NativeRustcVm.NoWrap at hnw; omega))
      (inRange_mono hq (by omega))

section
variable [Labels]

/-- **The phase's bytes kept** where only the stack changed. -/
theorem ph_keep {P : Array OpeningW} {R : Digest} {Q : Array UInt64}
    (hpre : OpenPhasePre P R Q m0) (hs : NativeRustcVm.SameOutside m0.dmem d.dmem (Stk m0))
    {o : Nat} {bs : List UInt8} (ho : o < 8 * phaseWords) (hle : o + bs.length ≤ 8 * phaseWords)
    (h : NativeRustcVm.BytesAt m0.dmem (off (phO m0) o) bs) :
    NativeRustcVm.BytesAt d.dmem (off (phO m0) o) bs := by
  have hnwp : (phO m0).toNat + 8 * phaseWords ≤ 2 ^ 64 := hpre.2.2.2.2.2.2.2.2.1
  have haps : (phO m0).toNat + 8 * phaseWords ≤ (stackBelow m0 openPhaseStack).toNat ∨
      (stackBelow m0 openPhaseStack).toNat + (openPhaseStack + 8) ≤ (phO m0).toNat :=
    hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hoff : (off (phO m0) o).toNat = (phO m0).toNat + o := toNat_off (by omega)
  exact keepB hpre.1 hs (n := bs.length) (by unfold NativeRustcVm.NoWrap; rw [hoff]; omega)
    (by unfold NativeRustcVm.Apart; rw [hoff]; omega) le_rfl h

theorem ph_word {P : Array OpeningW} {R : Digest} {Q : Array UInt64}
    (hpre : OpenPhasePre P R Q m0) (hs : NativeRustcVm.SameOutside m0.dmem d.dmem (Stk m0))
    {o : Nat} (ho : o + 8 ≤ 8 * phaseWords) {v : UInt64}
    (h : NativeRustcVm.WordAt m0.dmem (off (phO m0) o) v) :
    NativeRustcVm.WordAt d.dmem (off (phO m0) o) v :=
  ph_keep hpre hs (by omega) (by rw [NativeRustcVm.length_wordBytes]; exact ho) h

end

/-! ## Blocks and calls -/

theorem memNil {S : SState} (h : S.mem = []) {P : Write → Prop} : ∀ w ∈ S.mem, P w := by
  rw [h]; nofun

section
variable [Labels]

/-- **A block of the frame** writing only below its slots keeps `FrO`. -/
theorem FrO.block (hst : StackOk m0 openPhaseStack) {o o' : Nat} (hf : FrO m0 o m)
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (frameEnv m0 m 176 rest vars ret).WF)
    (hm : Match (frameEnv m0 m 176 rest vars ret) S d') (hmid : MidOk 176 o' slots S = true)
    (hW : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 176) : FrO m0 o' d' :=
  ⟨Frame.of_block hf.frame hwf hm hmid slots_le,
    NativeRustcVm.SameOutside.mono (hf.same.trans (sameOutside_low hwf hm (r := 0) rfl
      (hi := 176) (by omega) hW)) fun q hq ↦ hq.elim id (fa_stk hst)⟩

end

/-- The frame-only environment is well formed. -/
theorem wf0 (hst : StackOk m0 openPhaseStack) {o : Nat} (hf : FrO m0 o m) {ret : BitVec 64} :
    (frameEnv m0 m 176 [] (fun _ ↦ 0) ret).WF :=
  frame_wf ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.frame.kept, fa_noWrap hst⟩ (by simp)
    (List.pairwise_singleton _ _)

/-- The frame and one more region apart from the stack: well formed. -/
theorem wf1 (hst : StackOk m0 openPhaseStack) {o : Nat} (hf : FrO m0 o m) {ret : BitVec 64}
    {x : BitVec 64} {n : Nat} (hmx : NativeRustcVm.Mapped m.dmem x n)
    (hnw : NativeRustcVm.NoWrap x n)
    (hap : NativeRustcVm.Apart x n (stackBelow m0 openPhaseStack) (openPhaseStack + 8)) :
    (frameEnv m0 m 176 [(x, n)] (fun _ ↦ 0) ret).WF :=
  frame_wf ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.frame.kept, fa_noWrap hst⟩
    (fun z hz ↦ by rw [List.mem_singleton] at hz; subst hz; exact ⟨hmx, hnw⟩)
    (List.pairwise_pair.mpr (Apart.symm' (by
      have := apart_fa hst hap (o := 0) (k := 184) (by omega) (by omega)
      rwa [off_zero] at this)))

/-- **A call from the frame's base** writing the 32 bytes at `o` of the frame (below its slots)
and its stack: the frame, and the frame's other bytes kept. -/
theorem FrO.call (hst : StackOk m0 openPhaseStack) (hf : FrO m0 0 d) (hs : Saved d d')
    (hrsp : rspOf d' = rspOf d + 8#64) {N' o : Nat} (hN' : 176 + N' ≤ openPhaseStack)
    (ho : o + 32 ≤ 128)
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem (fun q ↦
      NativeRustcVm.InRange (off (fa m0) o) 32 q ∨ NativeRustcVm.InRange (stackBelow d N') N' q)) :
    FrO m0 8 d' ∧ ∀ j, j < 184 → (j < o ∨ o + 32 ≤ j) →
      d'.dmem.get? (off (fa m0) j) = d.dmem.get? (off (fa m0) j) := by
  have hsp : rspOf d = fa m0 := by rw [hf.frame.sp, off_zero]
  refine ⟨⟨Frame.call_slots hf.frame hs hrsp hso (fun p hp i hi ↦ notR hst hsp hN' (by omega)
      (by have := slots_le p hp; omega) (by have := slots_ge p hp; omega))
      (fun j hj ↦ notR hst hsp hN' (by omega) (by omega) (by omega)), ?_⟩, fun j hj hjo ↦
    hso _ (notR hst hsp hN' (by omega) hj hjo)⟩
  refine NativeRustcVm.SameOutside.mono (hf.same.trans hso) fun q hq ↦ ?_
  rcases hq with hq | hq | hq
  · exact hq
  · exact fa_off_stk hst (by omega) hq
  · exact callee_stk hst hsp hN' hq

/-- Bytes of the frame a call kept. -/
theorem keep_call {o : Nat} (hk : ∀ j, j < 184 → (j < o ∨ o + 32 ≤ j) →
      d'.dmem.get? (off (fa m0) j) = d.dmem.get? (off (fa m0) j)) {o' : Nat} {bs : List UInt8}
    (hle : o' + bs.length ≤ 184) (hd : o' + bs.length ≤ o ∨ o + 32 ≤ o')
    (h : NativeRustcVm.BytesAt d.dmem (off (fa m0) o') bs) :
    NativeRustcVm.BytesAt d'.dmem (off (fa m0) o') bs :=
  bytesAt_congr h fun i hi ↦ by rw [off_add]; exact hk _ (by omega) (by omega)

section
variable [Labels]

/-- The round constants for a callee from the frame's base. -/
theorem rcAt_callee (hst : StackOk m0 openPhaseStack) (hrc : RcAt m0 openPhaseStack)
    (hf : FrO m0 0 d) {N' : Nat} (hN' : 176 + N' ≤ openPhaseStack) : RcAt d N' :=
  RcAt.callee hrc (rc_keep hf.same fun q hq h ↦ not_inRange_of_apart hrc.2.2 hrc.2.1
      (noWrap_stackBelow hst) h (inRange_mono hq (by omega)))
    (by rw [hf.frame.sp, off_zero]) hst.1 hN'

/-- The frame's bytes are apart from the round constants. -/
theorem fa_rc (hrc : RcAt m0 openPhaseStack) (hst : StackOk m0 openPhaseStack) {o n : Nat}
    (hon : o + n ≤ 184) (ho : o < 184) : NativeRustcVm.Apart (off (fa m0) o) n rcAddr 192 :=
  Apart.symm' (apart_fa hst hrc.2.2 hon ho)

theorem got_of {P : Array OpeningW} {R : Digest} {Q : Array UInt64}
    (h : OpenPhasePre P R Q m0) :
    GotAt m0 openPhaseStack
      [(phO m0, 8 * phaseWords), (reg m0 .rsi, 32), (reg m0 .r8, 8 * (reg m0 .r9).toNat),
        (outO m0, 32), (rcAddr, 192)] ["memcpy", "memset"] := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hg⟩ := h
  exact hg

/-- The opening loop only writes its stack, so it preserves every loader slot. -/
theorem FrO.gotAt {P : Array OpeningW} {R : Digest} {Q : Array UInt64}
    (hf : FrO m0 0 d) (h : OpenPhasePre P R Q m0) {Nc : Nat}
    (hle : 176 + Nc ≤ openPhaseStack) {areas : List (BitVec 64 × Nat)}
    (ha : ∀ l ∈ (["memcpy", "memset"] : List Label), ∀ x ∈ areas,
      Apart (gotAddr l) 8 x.1 x.2) : GotAt d Nc areas ["memcpy", "memset"] := by
  have hg := got_of h
  refine hg.transport (fun l hl i hi ↦ hf.same _ ?_)
    (fun l hl ↦ apart_callee' h.1 (by rw [hf.frame.sp, off_zero]) hle
      (hg.1 l hl).2.2.1) ha
  intro hq
  exact not_inRange_of_apart (hg.1 l hl).2.2.1 (hg.1 l hl).2.1
    (noWrap_stackBelow h.1) (inRange_off_self hi (by decide))
    (inRange_mono hq (by omega))

theorem got_frame {P : Array OpeningW} {R : Digest} {Q : Array UInt64}
    (h : OpenPhasePre P R Q m0) {l : Label} (hl : l ∈ (["memcpy", "memset"] : List Label))
    {o n : Nat} (hon : o + n ≤ 176) : Apart (gotAddr l) 8 (off (fa m0) o) n :=
  apart_fa h.1 ((got_of h).1 l hl).2.2.1 (by omega) (by omega)

/-- The return, after `b9` from `S` with the output (region 1) written by `S`'s blocks. -/
theorem retPost {P : Array OpeningW} {R : Digest} {Q : Array UInt64}
    (hpre : OpenPhasePre P R Q m0) (hf : FrO m0 8 m) {S : SState}
    (hwf : (frameEnv m0 m 176 [(outO m0, 32)] (fun _ ↦ 0) 0).WF)
    {st : MachineState} (hm : Match (frameEnv m0 m 176 [(outO m0, 32)] (fun _ ↦ 0) 0) S st.data)
    (hpc : PcOk (frameEnv m0 m 176 [(outO m0, 32)] (fun _ ↦ 0) 0) (.ret (.load 0 176 8)) 0 st)
    (hepi : EpiOk 176 slots S = true)
    (hW : ∀ w ∈ S.mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 32)
    (hout : OptRowsAt st.data.dmem (outO m0) (off (phO m0) 24)
      (openPhase R (reg m0 .rdx).toNat (reg m0 .rcx).toNat Q P)) :
    st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ OpenPhasePost P R Q m0 st.data := by
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf.frame hwf hm hepi
  have hs := sameOutside_region hwf hm (r := 1) rfl hW
  simp only [PcOk] at hpc
  refine ⟨by rw [hpc]; exact hf.frame.load_ret hpre.1 (by decide), hrsp, hout, ?_, hsv⟩
  refine NativeRustcVm.SameOutside.mono (hf.same.trans hs) fun q hq ↦ ?_
  rcases hq with hq | hq
  · exact .inr hq
  · exact .inl hq

/-- The output's address at the frame's `16`, as `outS` reads it. -/
theorem match_outS (hf : FrO m0 8 m)
    (h16 : NativeRustcVm.WordAt m.dmem (off (fa m0) 16) (UInt64.ofBitVec (outO m0))) :
    Match (frameEnv m0 m 176 [(outO m0, 32)] (fun _ ↦ 0) 0) outS m := by
  have hal : (Sym.load 0 16 8).eval (frameEnv m0 m 176 [(outO m0, 32)] (fun _ ↦ 0) 0) =
      (frameEnv m0 m 176 [(outO m0, 32)] (fun _ ↦ 0) 0).base 1 + BitVec.ofInt 64 0 := by
    rw [ofInt_zero64, BitVec.add_zero]
    exact load_ofMachine (o := 16) rfl h16
  exact match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.frame.rsp_eval, trivial⟩ trivial trivial
    ⟨hal, trivial⟩

/-- The output's environment is well formed. -/
theorem wf_out {P : Array OpeningW} {R : Digest} {Q : Array UInt64}
    (hpre : OpenPhasePre P R Q m0) (hf : FrO m0 8 m) :
    (frameEnv m0 m 176 [(outO m0, 32)] (fun _ ↦ 0) 0).WF :=
  wf1 hpre.1 hf (Mapped.keeps hpre.2.2.2.2.2.2.2.2.2.2.2.1 hf.frame.kept)
    hpre.2.2.2.2.2.2.2.2.2.2.2.2.1 hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end

variable [Host] {k : Nat}

/-- **A test block of the frame** (`frS`): no write, the registers but `rs` kept. -/
theorem frTest (hst : StackOk m0 openPhaseStack) (hf : FrO m0 8 m) {ds : List Directive}
    {S' : SState} {x : Exit} {j : Nat} (hk : ds.IsInfixAt Host.prog j)
    (hx : exec ds frS = some (S', x)) (hret : ∀ l, x ≠ .call l)
    (hmid : MidOk 176 8 slots S' = true) (hmem : S'.mem = []) {rs : List Reg64}
    (hkeep : KeepBut rs S' = true) {Rs : MachineState → Prop}
    (cont : ∀ st : MachineState, FrO m0 8 st.data → st.data.dmem = m.dmem →
      (∀ r, r ≠ .rsp → rs.contains r = false → reg st.data r = reg m r) →
      Match (frameEnv m0 m 176 [] (fun _ ↦ 0) 0) S' st.data →
      PcOk (frameEnv m0 m 176 [] (fun _ ↦ 0) 0) x (Host.addrOf (j + ds.length)) st →
      Eventually (step1 Host.exe) Rs st) :
    Eventually (step1 Host.exe) Rs ⟨m, Host.addrOf j⟩ := by
  have hwf := wf0 hst hf (ret := 0)
  refine exec_then hk hx hwf (fun l h ↦ absurd h (hret l))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf.frame.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st hm hpc ↦ cont st (FrO.block hst hf hwf hm hmid (memNil hmem)) (hm.dmem_eq hwf hmem)
      (fun r h1 h2 ↦ KeepBut.regs hkeep hm h1 h2) hm hpc

/-- **`b22`, `b9`**: a rejection, `None` at the output. -/
theorem exit_fail (hp : Placed code k) {P : Array OpeningW} {R : Digest} {Q : Array UInt64}
    (hpre : OpenPhasePre P R Q m0) (hf : FrO m0 8 m)
    (h16 : NativeRustcVm.WordAt m.dmem (off (fa m0) 16) (UInt64.ofBitVec (outO m0)))
    (hr : openPhase R (reg m0 .rdx).toNat (reg m0 .rcx).toNat Q P = none) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧
      rspOf st.data = rspOf m0 + 8#64 ∧ OpenPhasePost P R Q m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b22Offset)⟩ := by
  have hwf := wf_out hpre hf
  refine exec_then (infix_of b22_in_code (by simp [b22]) hp) exit_b22 hwf nofun
    (match_outS hf h16) fun st1 hm1 hpc1 ↦ ?_
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) exit_b9n hwf nofun
    (hpc1.trans (hp.label NativeRustcVmX64.Vm.OpenPhase.label_17_at)) hm1 fun st hm hpc ↦ ?_
  obtain ⟨hepi, hw0, hW⟩ := ok_b9n
  refine .done _ (retPost hpre hf hwf hm hpc hepi hW ?_)
  rw [hr]
  have := wordAt_write hm (r := 1) (o := 0) (b := outO m0) (sz := 32) rfl (by decide) hw0
  rwa [off_zero] at this

/-- **`b8`, `b9`**: a rejection by the checks, `None` at the output through RDI. -/
theorem exit_fail8 (hp : Placed code k) {P : Array OpeningW} {R : Digest} {Q : Array UInt64}
    (hpre : OpenPhasePre P R Q m0) (hf : FrO m0 8 m) (hdi : reg m .rdi = outO m0)
    (hr : openPhase R (reg m0 .rdx).toNat (reg m0 .rcx).toNat Q P = none) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧
      rspOf st.data = rspOf m0 + 8#64 ∧ OpenPhasePost P R Q m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b8Offset)⟩ := by
  have hwf := wf_out hpre hf
  refine exec_then (infix_of b8_in_code (by simp [b8]) hp) exit_b8 hwf nofun
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.frame.rsp_eval, known_ptr rfl hdi, trivial⟩ trivial
      trivial trivial) fun st1 hm1 hpc1 ↦ ?_
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) exit_b9f hwf nofun
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.OpenPhase.b8_next)) hm1 fun st hm hpc ↦ ?_
  obtain ⟨hepi, hw0, hW⟩ := ok_b9f
  refine .done _ (retPost hpre hf hwf hm hpc hepi hW ?_)
  rw [hr]
  have := wordAt_write hm (r := 1) (o := 0) (b := outO m0) (sz := 32) rfl (by decide) hw0
  rwa [off_zero] at this

/-- **`b21`, `b9`**: the rows at the output, reading the openings at `phase + 24`. -/
theorem exit_rows (hp : Placed code k) {P : Array OpeningW} {R : Digest} {Q : Array UInt64}
    (hpre : OpenPhasePre P R Q m0) (hf : FrO m0 8 m)
    (h16 : NativeRustcVm.WordAt m.dmem (off (fa m0) 16) (UInt64.ofBitVec (outO m0))) {w : Nat}
    (hw : w ≤ wireMaxLeafWords) (hsz : P.size ≤ wireMaxQueries)
    (hbp : reg m .rbp = off (phO m0) 24) (h13 : reg m .r13 = P.size.toUInt64.toBitVec)
    (h14 : reg m .r14 = w.toUInt64.toBitVec)
    (hleaf : ∀ j (hj : j < P.size), P[j].leaf.size = w ∧
      NativeRustcVm.WordsAt m.dmem (off (off (phO m0) 24) (8 * (1 + j * openingWords)))
        P[j].leaf.toList)
    (hr : openPhase R (reg m0 .rdx).toNat (reg m0 .rcx).toNat Q P = some (P.map (·.leaf))) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧
      rspOf st.data = rspOf m0 + 8#64 ∧ OpenPhasePost P R Q m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b21Offset)⟩ := by
  obtain ⟨hst, -, -, -, -, -, -, -, hnwp, -, -, -, hnwo, -, -, -, -, hop, -⟩ := id hpre
  have hwf := wf_out hpre hf
  refine exec_then (infix_of b21_in_code (by simp [b21]) hp) exit_b21 hwf nofun
    (match_outS hf h16) fun st1 hm1 hpc1 ↦ ?_
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) exit_b9r hwf nofun
    (hpc1.trans (hp.label NativeRustcVmX64.Vm.OpenPhase.label_17_at)) hm1 fun st hm hpc ↦ ?_
  obtain ⟨hepi, hw0, hw8, hw16, hw24, hW⟩ := ok_b9r
  refine .done _ (retPost hpre hf hwf hm hpc hepi hW ?_)
  rw [hr]
  have hpw : phaseWords = 49411 := rfl
  have how : openingWords = 193 := rfl
  have hnwp' : (phO m0).toNat + 8 * 49411 ≤ 2 ^ 64 := by rw [← hpw]; exact hnwp
  have hnwo' : (reg m0 .rdi).toNat + 32 ≤ 2 ^ 64 := hnwo
  have hop' : (reg m0 .rdi).toNat + 32 ≤ (phO m0).toNat ∨
      (phO m0).toNat + 8 * 49411 ≤ (reg m0 .rdi).toNat := by rw [← hpw]; exact hop
  have hs : NativeRustcVm.SameOutside m.dmem st.data.dmem
      (NativeRustcVm.InRange (outO m0) 32) := sameOutside_region hwf hm (r := 1) rfl hW
  have v0 := wordAt_write hm (r := 1) (o := 0) (b := outO m0) (sz := 32) rfl (by decide) hw0
  have v8 := wordAt_write hm (r := 1) (o := 8) (b := outO m0) (sz := 32) rfl (by decide) hw8
  have v16 := wordAt_write hm (r := 1) (o := 16) (b := outO m0) (sz := 32) rfl (by decide) hw16
  have v24 := wordAt_write hm (r := 1) (o := 24) (b := outO m0) (sz := 32) rfl (by decide) hw24
  rw [off_zero, show (Sym.reg .rbp).eval (frameEnv m0 m 176 [(outO m0, 32)] (fun _ ↦ 0) 0) =
    off (phO m0) 24 from hbp] at v0
  rw [show (Sym.reg .r13).eval (frameEnv m0 m 176 [(outO m0, 32)] (fun _ ↦ 0) 0) =
    P.size.toUInt64.toBitVec from h13] at v16
  rw [show (Sym.reg .r14).eval (frameEnv m0 m 176 [(outO m0, 32)] (fun _ ↦ 0) 0) =
    w.toUInt64.toBitVec from h14] at v24
  have hpz : off (phO m0) 24 ≠ 0 := fun h ↦ by
    have := congrArg BitVec.toNat h
    rw [toNat_off (by omega)] at this
    simp at this
  refine ⟨hpz, by simpa using hsz, w, hw, ?_, fun j hj ↦ ?_⟩
  · have v16' : NativeRustcVm.WordAt st.data.dmem (off (outO m0) (8 + 8))
        (P.map (·.leaf)).size.toUInt64 := by rw [Array.size_map]; exact v16
    have v24' : NativeRustcVm.WordAt st.data.dmem (off (outO m0) (8 + 8 + 8)) w.toUInt64 := v24
    refine wordsAt_cons.mpr ⟨v0, wordsAt_cons.mpr ⟨v8, ?_⟩⟩
    rw [off_off]
    refine wordsAt_cons.mpr ⟨v16', wordsAt_cons.mpr ⟨?_, wordsAt_nil _ _⟩⟩
    rw [off_off]
    exact v24'
  · simp only [Array.size_map] at hj
    obtain ⟨hl, hws⟩ := hleaf j hj
    simp only [Array.getElem_map]
    refine ⟨hl, bytesAt_congr hws fun i hi ↦ hs _ fun hq ↦ ?_⟩
    rw [NativeRustcVm.length_wordsBytes, Array.length_toList, hl] at hi
    have hsz' : P.size ≤ 256 := hsz
    have hw' : w ≤ 64 := hw
    have e : (off (off (phO m0) 24) (8 * (1 + j * openingWords)) + BitVec.ofNat 64 i).toNat =
        (phO m0).toNat + (24 + (8 * (1 + j * openingWords) + i)) := by
      rw [off_add, off_off, toNat_off (by rw [how]; omega)]
    rw [inRange_iff' hnwo, e] at hq
    rw [how] at hq
    omega

end

end NativeRustcVmX64.Sumcheck.OpenPhase
