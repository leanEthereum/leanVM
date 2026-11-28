module

public import NativeRustcVmX64.Whir.FinalLevel.Basic
public import NativeRustcVm.Wire.WordsFacts
public import NativeRustcVmX64.Whir.WhirLevels.Steps

/-!
# `final_level`: the frame through blocks and calls (x86-64)

The frame's region (`fa`, 2688 bytes with the return address and the argument word) as numbers
(`Ctx.loc_toNat`, `Ctx.region_ok`); the inputs (the level, the state `w` with its rounds, the
basis) kept wherever memory changed only in the stack and the outputs (`Ctx.level_at`,
`Ctx.whir_at`, `Ctx.basis_at`); a body block writing the frame below its pushed registers keeps
`Fr` (`Ctx.blk`, `Ctx.bytes_blk`); a call from RSP offset `o` (the callee's entry RSP) gets the
transcript's context (`Ctx.at_call`, `Ctx.whirT`, `Ctx.outLoc`, …) and keeps `Fr`, the frame's
bytes above `o + 8` but its outputs (`Ctx.call`, `bytes_call`) and the bytes of any area apart from
its changes (`Ctx.same_call`). The `TState` across both (`Ctx.ts_frame`, `Ctx.ts_call`).
-/

namespace NativeRustcVmX64.Whir.Levels.FL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck

public section

theorem stackBelow_off {m : MachineData} {F o : Nat} (h : F ≤ (rspOf m).toNat) (ho : o ≤ F) :
    off (stackBelow m F) o = stackBelow m (F - o) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_off (by rw [stackBelow_toNat h]; have := (rspOf m).isLt; omega), stackBelow_toNat h,
    stackBelow_toNat (by omega)]
  omega

/-- A call keeps the frame where the callee changes none of its slots' or return address's
bytes, RSP at any offset `o`. -/
theorem Frame.callO {m0 d d' : MachineData} {F o : Nat} {slots : Slots}
    (hf : Frame m0 F slots o d) (hs : Saved d d') (hrsp : rspOf d' = rspOf d + 8#64)
    {R : BitVec 64 → Prop} (hso : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ p ∈ slots, ∀ i < 8, ¬ R (off (stackBelow m0 F) (p.1 + i)))
    (hRr : ∀ j < 8, ¬ R (off (stackBelow m0 F) (F + j))) : Frame m0 F slots (o + 8) d' := by
  refine ⟨?_, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans hf.kept hs.2, fun r hr hsl ↦ ?_⟩
  · rw [hrsp, hf.sp, off_add]
  · refine bytesAt_congr (hf.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    rw [off_add]
    exact hso _ (hR p hp i hi')
  · rw [hso _ (hRr j hj)]
    exact hf.ret j hj
  · exact (hs.1 r hr).trans (hf.regs r hr hsl)

/-- `Frame` in a state with the same registers and memory. -/
theorem Frame.congr' {m0 d d' : MachineData} {F o : Nat} {sl : Slots} (hf : Frame m0 F sl o d)
    (hr : ∀ r, reg d' r = reg d r) (hd : d'.dmem = d.dmem) : Frame m0 F sl o d' :=
  ⟨by show reg d' .rsp = _; rw [hr]; exact hf.sp, fun p hp ↦ by rw [hd]; exact hf.slot p hp,
    fun j hj ↦ by rw [hd]; exact hf.ret j hj, by rw [hd]; exact hf.kept,
    fun r hr' hs ↦ by rw [hr]; exact hf.regs r hr' hs⟩

theorem Fr.congr {m0 d d' : MachineData} {o : Nat} (hf : Fr m0 o d)
    (hr : ∀ r, reg d' r = reg d r) (hd : d'.dmem = d.dmem) : Fr m0 o d' :=
  ⟨Frame.congr' hf.frame hr hd, by rw [Sm, hd]; exact hf.same⟩

/-- **Bytes of the frame a call does not change.** -/
theorem bytes_call {m0 d d' : MachineData} {o lo n : Nat}
    (hk : ∀ j, o + 8 ≤ j → j < 2688 → (j < lo ∨ lo + n ≤ j) →
      d'.dmem.get? (loc m0 j) = d.dmem.get? (loc m0 j))
    {j : Nat} {bs : List UInt8} (hj : o + 8 ≤ j) (hjn : j + bs.length ≤ 2688)
    (hmiss : j + bs.length ≤ lo ∨ lo + n ≤ j) (h : NativeRustcVm.BytesAt d.dmem (loc m0 j) bs) :
    NativeRustcVm.BytesAt d'.dmem (loc m0 j) bs := by
  intro i hi
  have := h i hi
  rw [off_add] at this ⊢
  rw [hk (j + i) (by omega) (by omega) (by omega)]
  exact this

/-- **Bytes of the frame a block does not write.** -/
theorem bytes_blk [Labels] {m0 d d' : MachineData} {rest : List (BitVec 64 × Nat)} {S : SState}
    {ret : BitVec 64} (hwf : (argEnv m0 d 2672 8 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (argEnv m0 d 2672 8 rest (fun _ ↦ 0) ret) S d')
    (hin : writesIn S = true) {rs : List (Nat × Nat)} (hW : Wr rs S) {j : Nat} {bs : List UInt8}
    (hj : j + bs.length ≤ 2688) (hmiss : ∀ p ∈ rs, p.2 ≤ j ∨ j + bs.length ≤ p.1)
    (h : NativeRustcVm.BytesAt d.dmem (loc m0 j) bs) :
    NativeRustcVm.BytesAt d'.dmem (loc m0 j) bs := by
  intro i hi
  have := h i hi
  rw [off_add] at this ⊢
  rw [hm.get?_mem0 hwf (not_written0A hwf hm hin (by omega) fun w hw _ ↦ ?_)]
  · exact this
  · obtain ⟨-, p, hp, h1, h2⟩ := hW w hw
    rcases hmiss p hp with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData}

namespace Ctx

variable (c : Ctx a s level ba b w rounds m0)
include c

theorem fa_toNat : (fa m0).toNat = (rspOf m0).toNat - 2672 :=
  stackBelow_toNat (by have := c.geo.hN; omega)

theorem loc_toNat {j : Nat} (hj : j < 2688) : (loc m0 j).toNat = (rspOf m0).toNat - 2672 + j := by
  have := c.geo.hN; have := c.geo.hA
  rw [toNat_off (by rw [c.fa_toNat]; omega), c.fa_toNat]

theorem stk_toNat : (stackBelow m0 finalLevelStack).toNat = (rspOf m0).toNat - 5760 := by
  rw [stackBelow_toNat c.stack.1, stack_eq]

theorem arg_toNat : (rspOf m0 + 8#64).toNat = (rspOf m0).toNat + 8 := by
  have := c.geo.hA
  rw [BitVec.toNat_add, show (8#64 : BitVec 64).toNat = 8 from rfl]
  omega

theorem qA_toNat : (qA m0).toNat = (pA m0).toNat + 61352 :=
  NativeRustcVm.toNat_add_ofNat (by have := c.geo.pW; omega)

/-- The frame's region with the argument word: mapped, not wrapping. -/
theorem region_ok {d : MachineData} (hk : Kept m0.dmem d.dmem) :
    NativeRustcVm.Mapped d.dmem (fa m0) 2688 ∧ NativeRustcVm.NoWrap (fa m0) 2688 := by
  have hfm := frame_mapped (F := 2672) c.stack (by rw [stack_eq]; omega)
  have ham := c.args.1
  have hf := c.fa_toNat
  have ha := c.arg_toNat
  have := c.geo.hN; have := c.geo.hA
  refine ⟨fun i hi ↦ hk _ ?_, ?_⟩
  · by_cases h : i < 2680
    · exact hfm i h
    · have e : fa m0 + BitVec.ofNat 64 i = rspOf m0 + 8#64 + BitVec.ofNat 64 (i - 2680) := by
        apply BitVec.eq_of_toNat_eq
        rw [NativeRustcVm.toNat_add_ofNat (by omega), NativeRustcVm.toNat_add_ofNat (by omega), hf,
          ha]
        omega
      rw [e]
      exact ham _ (by omega)
  · unfold NativeRustcVm.NoWrap; rw [hf]; omega

theorem inP {q : BitVec 64} : NativeRustcVm.InRange (pA m0) whirBytes q ↔
    (pA m0).toNat ≤ q.toNat ∧ q.toNat < (pA m0).toNat + 63200 := inRange_iff' c.geo.pW

theorem inT {q : BitVec 64} : NativeRustcVm.InRange (tA m0) tstateBytes q ↔
    (tA m0).toNat ≤ q.toNat ∧ q.toNat < (tA m0).toNat + 760 := inRange_iff' c.geo.tW

theorem inA {q : BitVec 64} : NativeRustcVm.InRange a.words (8 * a.len) q ↔
    a.words.toNat ≤ q.toNat ∧ q.toNat < a.words.toNat + 8 * a.len := inRange_iff' c.geo.aW

theorem inQ {q : BitVec 64} : NativeRustcVm.InRange (qA m0) queryBufBytes q ↔
    (pA m0).toNat + 61352 ≤ q.toNat ∧ q.toNat < (pA m0).toNat + 63200 := by
  have := c.geo.pW
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap queryBufBytes queryCap; rw [c.qA_toNat]; omega),
    c.qA_toNat]
  unfold queryBufBytes queryCap
  omega

theorem inLc {j n : Nat} (hj : j < 2688) (hjn : j + n ≤ 2688) {q : BitVec 64} :
    NativeRustcVm.InRange (loc m0 j) n q ↔
      (rspOf m0).toNat - 2672 + j ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 2672 + j + n := by
  have := c.geo.hA; have := c.geo.hN
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [c.loc_toNat hj]; omega), c.loc_toNat hj]

/-- The outputs, as numbers: off the stack, the return address and the argument word. -/
theorem outs_nat {q : BitVec 64} (hq : outs m0 q) :
    q.toNat < (rspOf m0).toNat - 5760 ∨ (rspOf m0).toNat + 16 ≤ q.toNat := by
  have g := c.geo
  rcases hq with hq | hq
  · rw [c.inQ] at hq; have := g.pS; have := g.hN; omega
  · rw [c.inT] at hq; have := g.tS; have := g.hN; omega

/-- The stack below RSP, as numbers. -/
theorem stk_nat {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow m0 finalLevelStack) finalLevelStack q) :
    (rspOf m0).toNat - 5760 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat := by
  have g := c.geo
  have := g.hN
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [c.stk_toNat, stack_eq]; omega),
    c.stk_toNat, stack_eq] at hq
  omega

/-- The frame's byte `j` is not an output. -/
theorem loc_not_outs {j : Nat} (hj : j < 2688) : ¬outs m0 (loc m0 j) := fun h ↦ by
  have := c.outs_nat h
  rw [c.loc_toNat (by omega)] at this
  have := c.geo.hN
  omega

/-- The frame below its pushed registers is in the stack. -/
theorem loc_stk {j : Nat} (hj : j < 2672) :
    NativeRustcVm.InRange (stackBelow m0 finalLevelStack) finalLevelStack (loc m0 j) := by
  have := c.geo.hN; have := c.geo.hA
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [c.stk_toNat, stack_eq]; omega),
    c.stk_toNat, stack_eq, c.loc_toNat (by omega)]
  omega

/-- **An area apart from the stack and the outputs** is kept where memory changed only there. -/
theorem same_sm {d : MachineData} (hs : Sm m0 d) {x : BitVec 64} {n : Nat}
    (hnw : x.toNat + n ≤ 2 ^ 64) (hst : x.toNat + n ≤ (rspOf m0).toNat - 5760 ∨
      (rspOf m0).toNat ≤ x.toNat)
    (hq : x.toNat + n ≤ (pA m0).toNat + 61352 ∨ (pA m0).toNat + 63200 ≤ x.toNat)
    (ht : x.toNat + n ≤ (tA m0).toNat ∨ (tA m0).toNat + 760 ≤ x.toNat) :
    NativeRustcVm.Layout.Same m0.dmem d.dmem x n := by
  refine NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj hq' ↦ ?_
  have hx : (x + BitVec.ofNat 64 j).toNat = x.toNat + j := NativeRustcVm.toNat_add_ofNat (by omega)
  rcases hq' with hq' | hq' | hq'
  · have := c.stk_nat hq'; omega
  · rw [c.inQ, hx] at hq'; omega
  · rw [c.inT, hx] at hq'; omega

/-- An input (apart from the stack), apart from the `WhirW` and the `TState`, as numbers. -/
theorem same_in {d : MachineData} (hs : Sm m0 d) {x : BitVec 64} {n : Nat}
    (hx : WhirIn m0 x n finalLevelStack) (hp : NativeRustcVm.Apart x n (pA m0) whirBytes)
    (ht : NativeRustcVm.Apart x n (tA m0) tstateBytes) :
    NativeRustcVm.Layout.Same m0.dmem d.dmem x n := by
  have g := c.geo
  have h1 : NativeRustcVm.Apart x n (stackBelow m0 finalLevelStack) (finalLevelStack + 8) := hx.2
  have h2 := hx.1.2
  unfold NativeRustcVm.Apart at h1
  unfold NativeRustcVm.Apart at hp ht
  rw [c.stk_toNat, stack_eq] at h1
  unfold whirBytes at hp
  unfold tstateBytes at ht
  exact c.same_sm hs h2 (by omega) (by omega) (by omega)

/-- The level, where memory changed only in the stack and the outputs. -/
theorem level_at {d : MachineData} (hs : Sm m0 d) : LevelAt d.dmem (lA m0) level :=
  LevelAt.of_same c.lv (c.same_in hs c.lin c.lp c.lt)

/-- The state `w` and its rounds, where memory changed only in the stack and the outputs. -/
theorem whir_at {d : MachineData} (hs : Sm m0 d) : WhirAt d.dmem (pA m0) w rounds := by
  have g := c.geo
  have hsm := c.same_sm hs (x := pA m0) (n := 61352) (by have := g.pW; omega)
    (by have := g.pS; omega) (by omega) (by have := g.pT; omega)
  exact ⟨WhirStateAt.of_same c.wa.1 fun j hj ↦ hsm j (by unfold stateBytes at hj; omega),
    bufRoundsAt_of_same c.wa.2 (hsm.sub (o := roundsOff) (k := 8 + roundBytes * roundCap)
      (by decide))⟩

/-- The basis, where memory changed only in the stack and the outputs. -/
theorem basis_at {d : MachineData} (hs : Sm m0 d) : BasisWAt d.dmem (bA m0) ba b :=
  basisWAt_of_same c.bw (c.same_in hs c.bp.1 c.bp.2.1 c.bt.2.1) fun r hr ↦
    c.same_in hs (c.bp.2.2 r hr).1 (c.bp.2.2 r hr).2 (c.bt.2.2 r hr).2

/-- The argument word stays where memory changed only in the stack and the outputs. -/
theorem arg_keep {d : MachineData} (hsm : Sm m0 d) :
    NativeRustcVm.WordAt d.dmem (loc m0 2680) (UInt64.ofBitVec (pA m0)) := by
  have hl : loc m0 2680 = rspOf m0 + 8#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [c.loc_toNat (by omega), c.arg_toNat]
    have := c.geo.hN; omega
  rw [hl]
  obtain ⟨v, hv⟩ := NativeRustcVm.Wire.exists_wordAt (a := rspOf m0 + 8#64) (d := m0.dmem)
    fun i hi ↦ c.args.1 i (by omega)
  have hpa : UInt64.ofBitVec (pA m0) = v := by
    show UInt64.ofBitVec
      (NativeRustcVm.wordOf m0.dmem (rspOf m0 + BitVec.ofNat 64 (8 + 8 * 0))).toBitVec = v
    rw [show rspOf m0 + BitVec.ofNat 64 (8 + 8 * 0) = rspOf m0 + 8#64 from rfl,
      NativeRustcVm.wordOf_of_wordAt hv]
  rw [hpa]
  refine hv.of_sameOutside hsm fun i hi hq ↦ ?_
  have hi8 : i < 8 := by rw [NativeRustcVm.length_wordBytes] at hi; exact hi
  have ha := c.arg_toNat
  have hx : (rspOf m0 + 8#64 + BitVec.ofNat 64 i).toNat = (rspOf m0).toNat + 8 + i := by
    rw [NativeRustcVm.toNat_add_ofNat (by have := c.geo.hA; omega), ha]
  rcases hq with hq | hq
  · have := c.stk_nat hq; omega
  · have := c.outs_nat hq; omega

/-- The round constants' bytes kept where memory changed only in the stack and the outputs. -/
theorem rc_keep {d : MachineData} (hs : Sm m0 d) :
    ∀ i < 192, d.dmem.get? (rcAddr + BitVec.ofNat 64 i) =
      m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) := by
  have g := c.geo
  intro i hi
  refine hs _ fun hq ↦ ?_
  have hx : (rcAddr + BitVec.ofNat 64 i).toNat = rcAddr.toNat + i :=
    NativeRustcVm.toNat_add_ofNat (by have := g.rW; omega)
  rcases hq with hq | hq
  · have := c.stk_nat hq; have := g.rS; omega
  · rcases hq with hq | hq
    · rw [c.inQ] at hq; have := g.pR; omega
    · rw [c.inT] at hq; have := g.tR; omega

/-- The `Sumcheck` context with a frame of `F` bytes. -/
theorem sctx {F : Nat} (hF : F ≤ finalLevelStack) :
    Sumcheck.Ctx m0 (tA m0) a finalLevelStack F :=
  ⟨c.wt.1, c.wt.2.1, c.wt.2.2.2.1, c.ts.footprint, hF⟩

/-- **At a call** from RSP offset `o`. -/
theorem at_call {o : Nat} (ho : o ≤ 2672) {d : MachineData} (hf : Fr m0 o d) :
    At m0 (2672 - o) d :=
  ⟨by rw [hf.frame.sp, stackBelow_off (by have := c.geo.hN; omega) ho], hf.frame.kept,
    c.rc_keep hf.same⟩

/-- The read-only data for a callee. -/
theorem rodataAt {F : Nat} {d : MachineData} (hat : At m0 F d) (hs : Sm m0 d) {N' : Nat}
    (hle : F + N' ≤ finalLevelStack) : RodataAt d N' := by
  have hro := c.wt.2.2.1
  have hsb : stackBelow d N' = stackBelow m0 (F + N') :=
    stackBelow_callee hat.sp (by have := c.stack.1; omega)
  intro t
  refine ⟨(hro.bytesAt t).of_sameOutside hs fun i hi hq ↦ ?_, hro.noWrap t, ?_⟩
  · have hin : NativeRustcVm.InRange (rodataAddr t) t.bytes.length
        (rodataAddr t + BitVec.ofNat 64 i) :=
      NativeRustcVm.inRange_add hi (by
        have := hro.noWrap t; unfold NativeRustcVm.NoWrap at this; omega)
    rcases hq with hq | hq
    · exact NativeRustcVm.Apart.not_inRange (hro.apart t) (hro.noWrap t)
        (noWrap_stackBelow c.stack) hin (inRange_mono hq (by omega))
    · rcases hq with hq | hq
      · have hsub : NativeRustcVm.InRange (pA m0) whirBytes (rodataAddr t + BitVec.ofNat 64 i) :=
          NativeRustcVm.InRange.of_sub hq c.pout.1.2.1 (by decide)
        exact NativeRustcVm.Apart.not_inRange (c.pout.2 t) c.pout.1.2.1 (hro.noWrap t) hsub hin
      · exact NativeRustcVm.Apart.not_inRange (c.wt.2.2.2.2 t) c.ts.footprint.1.2
          (hro.noWrap t) hq hin
  · rw [hsb]
    have := hro.apart t
    have h1 := stackBelow_toNat (m := m0) (n := F + N') (by have := c.stack.1; omega)
    have h2 := stackBelow_toNat (m := m0) (n := finalLevelStack) c.stack.1
    refine NativeRustcVm.Apart.mono_right this ?_ ?_ <;> rw [h1, h2] <;> omega

/-- **The transcript's context** for a callee. -/
theorem whirT {F : Nat} {d : MachineData} (hat : At m0 F d) (hs : Sm m0 d) {N' : Nat}
    (hle : F + N' ≤ finalLevelStack) : WhirT d (tA m0) a N' :=
  ⟨(c.sctx (by omega)).stackOk hat hle, (c.sctx (by omega)).rcAt hat hle, c.rodataAt hat hs hle,
    (c.sctx (by omega)).tstateOk hat hle, c.wt.2.2.2.2⟩

/-- An output among the caller's for a callee. -/
theorem whirOut {F : Nat} {d : MachineData} (hat : At m0 F d) {N' : Nat}
    (hle : F + N' ≤ finalLevelStack) {o : BitVec 64} {n : Nat}
    (h : WhirOut m0 (tA m0) a o n finalLevelStack) : WhirOut d (tA m0) a o n N' :=
  ⟨(c.sctx (by omega)).outOk hat hle h.1, h.2⟩

/-- An input for a callee. -/
theorem whirIn {F : Nat} {d : MachineData} (hat : At m0 F d) {N' : Nat}
    (hle : F + N' ≤ finalLevelStack) {x : BitVec 64} {n : Nat}
    (h : WhirIn m0 x n finalLevelStack) : WhirIn d x n N' :=
  ⟨⟨Mapped.keeps h.1.1 hat.kept, h.1.2⟩, (c.sctx (by omega)).apart hat hle h.2⟩

/-- **The frame's bytes from `j ≥ o + 8` as a callee's output.** -/
theorem outLoc {o : Nat} (ho : o ≤ 2672) {d : MachineData} (hf : Fr m0 o d) {N' : Nat}
    (hle : 2672 - o + N' ≤ finalLevelStack) {j n : Nat} (hj : o + 8 ≤ j) (hjn : j + n ≤ 2672) :
    OutOk d (tA m0) a (loc m0 j) n N' := by
  have := (c.sctx (F := 2672 - o) (by omega)).outOk_frame (c.at_call ho hf) hle (o := j - o)
    (n := n) (by omega) (by omega)
  rwa [← stackBelow_off (by have := c.geo.hN; omega) ho, off_off,
    show o + (j - o) = j by omega] at this

/-- The frame's bytes as a callee's input. -/
theorem inLoc {o : Nat} (ho : o ≤ 2672) {d : MachineData} (hf : Fr m0 o d) {N' : Nat}
    (hle : 2672 - o + N' ≤ finalLevelStack) {j n : Nat} (hj : o + 8 ≤ j) (hjn : j + n ≤ 2672) :
    WhirIn d (loc m0 j) n N' := by
  have h := c.outLoc ho hf hle hj hjn
  exact ⟨⟨h.1, h.2.1⟩, h.2.2.2.2.1⟩

/-- A slice in the frame for a callee. -/
theorem sliceLoc {o : Nat} (ho : o ≤ 2672) {d : MachineData} (hf : Fr m0 o d) {N' : Nat}
    (hle : 2672 - o + N' ≤ finalLevelStack) {j : Nat} {n : BitVec 64} (hj : o + 8 ≤ j)
    (hjn : j + 16 * n.toNat ≤ 2672) : SliceOk d (loc m0 j) n N' :=
  c.inLoc ho hf hle hj hjn

/-- The environment of a body block: the frame's region, then `rest`. -/
theorem wf0 {d : MachineData} (hk : Kept m0.dmem d.dmem) {ret : BitVec 64} :
    (argEnv m0 d 2672 8 [] (fun _ ↦ 0) ret).WF :=
  argEnv_wf (c.region_ok hk) (by simp) (List.pairwise_singleton _ _)

/-- The environment of a body block with one more region `x` (`n` bytes), apart. -/
theorem wf1 {d : MachineData} (hk : Kept m0.dmem d.dmem) {x : BitVec 64} {n : Nat}
    (hx : NativeRustcVm.Mapped d.dmem x n) (hnw : x.toNat + n ≤ 2 ^ 64)
    (hap : x.toNat + n ≤ (rspOf m0).toNat - 2672 ∨ (rspOf m0).toNat + 16 ≤ x.toNat)
    {ret : BitVec 64} : (argEnv m0 d 2672 8 [(x, n)] (fun _ ↦ 0) ret).WF := by
  have hf := c.fa_toNat
  have := c.geo.hN
  refine argEnv_wf (c.region_ok hk) (fun y hy ↦ ?_) (List.pairwise_pair.mpr ?_)
  · rw [List.mem_singleton] at hy; subst hy; exact ⟨hx, hnw⟩
  · show (fa m0).toNat + (2672 + 8 + 8) ≤ x.toNat ∨ x.toNat + n ≤ (fa m0).toNat
    rw [hf]; omega

/-- **A body block** keeps the frame; it writes the frame below offset `hi ≤ 2624`. -/
theorem blk {o o' : Nat} {d d' : MachineData} {rest : List (BitVec 64 × Nat)} {S : SState}
    {ret : BitVec 64} (hf : Fr m0 o d) (hwf : (argEnv m0 d 2672 8 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (argEnv m0 d 2672 8 rest (fun _ ↦ 0) ret) S d')
    (hmid : MidOk 2672 o' slots S = true)
    {hi : Nat} (hhi : hi ≤ 2624) (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ hi) :
    Fr m0 o' d' ∧ NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fa m0) hi) := by
  have hs : NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fa m0) hi) :=
    sameOutside_low hwf hm (r := 0) rfl (by omega) hw
  refine ⟨⟨Frame.of_blockA hf.frame hwf hm hmid slots_le, NativeRustcVm.SameOutside.mono
    (hf.same.trans hs) fun q hq ↦ ?_⟩, hs⟩
  rcases hq with hq | hq
  · exact hq
  · left
    obtain ⟨j, hj, rfl⟩ := NativeRustcVm.InRange.exists hq
    exact c.loc_stk (j := j) (by omega)

/-- The `TState` across a change of the frame. -/
theorem ts_frame {d d' : Mem 64} {hi : Nat} (hhi : hi ≤ 2672) (hk : Keeps d d')
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (fa m0) hi)) {s' : TState}
    (ht : TStateAt d (tA m0) a s') : TStateAt d' (tA m0) a s' := by
  have g := c.geo
  refine ht.frame hk (fun q hq ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩) hs
  · obtain ⟨j, hj, rfl⟩ := NativeRustcVm.InRange.exists hq
    have hl : (fa m0 + BitVec.ofNat 64 j).toNat = _ := c.loc_toNat (j := j) (by omega)
    rw [c.inT, hl] at h
    have := g.tS; have := g.hN; omega
  · obtain ⟨j, hj, rfl⟩ := NativeRustcVm.InRange.exists hq
    have hl : (fa m0 + BitVec.ofNat 64 j).toNat = _ := c.loc_toNat (j := j) (by omega)
    rw [c.inA, hl] at h
    have := g.aS; have := g.hN; omega

/-- Bytes of an area apart from the frame below `hi` across a change of it. -/
theorem same_frame {d d' : Mem 64} {hi : Nat} (hhi : hi ≤ 2688)
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (fa m0) hi)) {x : BitVec 64}
    {n : Nat} (hnw : x.toNat + n ≤ 2 ^ 64)
    (hx : x.toNat + n ≤ (rspOf m0).toNat - 2672 ∨ (rspOf m0).toNat - 2672 + hi ≤ x.toNat) :
    NativeRustcVm.Layout.Same d d' x n := by
  refine NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj hq ↦ ?_
  obtain ⟨i, hi, he⟩ := NativeRustcVm.InRange.exists hq
  have h1 := congrArg BitVec.toNat he
  rw [NativeRustcVm.toNat_add_ofNat (by omega)] at h1
  have hl : (fa m0 + BitVec.ofNat 64 i).toNat = _ := c.loc_toNat (j := i) (by omega)
  rw [hl] at h1
  omega

/-- **A call** from RSP offset `o`, its changes its stack, the outputs and the frame's `n` bytes
from `lo ≥ o + 8`: the frame kept, the frame's other bytes from `o + 8` kept. -/
theorem call {o : Nat} (ho : o ≤ 2624) {d d' : MachineData} (hf : Fr m0 o d) {N' : Nat}
    (hle : 2672 - o + N' ≤ finalLevelStack) (hsv : Saved d d') (hrsp : rspOf d' = rspOf d + 8#64)
    {R : BitVec 64 → Prop} {lo n : Nat} (hlo : o + 8 ≤ lo) (hn : lo + n ≤ 2624)
    (hR : ∀ q, R q → outs m0 q ∨ NativeRustcVm.InRange (loc m0 lo) n q)
    (hch : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow d N') N' q)) :
    Fr m0 (o + 8) d' ∧ ∀ j, o + 8 ≤ j → j < 2688 → (j < lo ∨ lo + n ≤ j) →
      d'.dmem.get? (loc m0 j) = d.dmem.get? (loc m0 j) := by
  have g := c.geo
  have hle' : 2672 - o + N' ≤ 5760 := by rw [stack_eq] at hle; exact hle
  have := g.hN
  have hat := c.at_call (by omega) hf
  have hsb : (stackBelow d N').toNat = (rspOf m0).toNat - 2672 + o - N' := by
    rw [stackBelow_callee hat.sp (by have := g.hN; omega),
      stackBelow_toNat (by have := g.hN; omega)]
    omega
  have hkeep : ∀ j, o + 8 ≤ j → j < 2688 → (j < lo ∨ lo + n ≤ j) →
      ¬ (R (loc m0 j) ∨ NativeRustcVm.InRange (stackBelow d N') N' (loc m0 j)) := by
    intro j hj1 hj2 hj3 hq
    have hl := c.loc_toNat (j := j) (by omega)
    have := g.hN; have := g.hA
    rcases hq with hq | hq
    · rcases hR _ hq with hq | hq
      · exact c.loc_not_outs hj2 hq
      · rw [c.inLc (by omega) (by omega), hl] at hq
        omega
    · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hsb]; omega), hsb, hl] at hq
      omega
  refine ⟨⟨Frame.callO hf.frame hsv hrsp hch (fun p hp i hi h ↦ ?_) (fun j hj h ↦ ?_),
    NativeRustcVm.SameOutside.mono (hf.same.trans hch) fun q hq ↦ ?_⟩,
    fun j h1 h2 h3 ↦ hch _ (hkeep j h1 h2 h3)⟩
  · have := slots_ge p hp; have := slots_le p hp
    exact hkeep (p.1 + i) (by omega) (by omega) (Or.inr (by omega)) h
  · exact hkeep (2672 + j) (by omega) (by omega) (Or.inr (by omega)) h
  · rcases hq with hq | hq | hq
    · exact hq
    · rcases hR q hq with hq | hq
      · exact Or.inr hq
      · left
        obtain ⟨j, hj, rfl⟩ := NativeRustcVm.InRange.exists hq
        rw [off_add]
        exact c.loc_stk (by omega)
    · left
      have := (c.sctx (F := 2672 - o) (by rw [stack_eq] at hle ⊢; omega)).inRange_callee hat hle hq
      exact inRange_mono this.1 le_rfl

/-- **Bytes of an area kept by a call** from RSP offset `o` whose changes are its stack and `R`:
the area apart from `R`, below the stack or above the frame's byte `o`. -/
theorem same_call {o : Nat} (ho : o ≤ 2672) {d d' : MachineData} (hf : Fr m0 o d) {N' : Nat}
    (hle : 2672 - o + N' ≤ finalLevelStack) {R : BitVec 64 → Prop}
    (hch : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow d N') N' q))
    {x : BitVec 64} {n : Nat} (hnw : x.toNat + n ≤ 2 ^ 64)
    (hx : x.toNat + n ≤ (rspOf m0).toNat - 5760 ∨ (rspOf m0).toNat - 2672 + o ≤ x.toNat)
    (hxR : ∀ j < n, ¬ R (x + BitVec.ofNat 64 j)) :
    NativeRustcVm.Layout.Same d.dmem d'.dmem x n := by
  have g := c.geo
  have hle' : 2672 - o + N' ≤ 5760 := by rw [stack_eq] at hle; exact hle
  have := g.hN
  have hat := c.at_call ho hf
  have hsb : (stackBelow d N').toNat = (rspOf m0).toNat - 2672 + o - N' := by
    rw [stackBelow_callee hat.sp (by have := g.hN; omega),
      stackBelow_toNat (by have := g.hN; omega)]
    omega
  refine NativeRustcVm.Layout.Same.of_sameOutside hch fun j hj hq ↦ ?_
  rcases hq with hq | hq
  · exact hxR j hj hq
  · have hxj : (x + BitVec.ofNat 64 j).toNat = x.toNat + j :=
      NativeRustcVm.toNat_add_ofNat (by omega)
    rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hsb]; omega), hsb, hxj] at hq
    omega

/-- The `TState` across a call whose changes are its stack and `R`. -/
theorem ts_call {o : Nat} (ho : o ≤ 2672) {d d' : MachineData} (hf : Fr m0 o d) {N' : Nat}
    (hle : 2672 - o + N' ≤ finalLevelStack) (hsv : Saved d d') {R : BitVec 64 → Prop}
    (hR : ∀ q, R q → ¬NativeRustcVm.InRange (tA m0) tstateBytes q ∧
      ¬NativeRustcVm.InRange a.words (8 * a.len) q)
    (hch : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow d N') N' q)) {s' : TState}
    (ht : TStateAt d.dmem (tA m0) a s') : TStateAt d'.dmem (tA m0) a s' := by
  have hat := c.at_call ho hf
  refine ht.frame hsv.2 (fun q hq ↦ ?_) hch
  rcases hq with hq | hq
  · exact hR q hq
  · exact (c.sctx (F := 2672 - o) (by omega)).stack_not_t
      ((c.sctx (F := 2672 - o) (by omega)).inRange_callee hat hle hq).1

/-- A frame range is apart from the `TState`, its area. -/
theorem loc_not_t {j n : Nat} (hjn : j + n ≤ 2680) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (loc m0 j) n q) :
    ¬NativeRustcVm.InRange (tA m0) tstateBytes q ∧
      ¬NativeRustcVm.InRange a.words (8 * a.len) q := by
  have g := c.geo
  have := g.hN
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd hq (by unfold NativeRustcVm.InRange; omega)
  rw [c.inLc (by omega) (by omega)] at hq
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [c.inT] at h; have := g.tS; omega
  · rw [c.inA] at h; have := g.aS; omega

/-- The query buffer's range is apart from the `TState`, its area. -/
theorem q_not_t {q : BitVec 64} (hq : NativeRustcVm.InRange (qA m0) queryBufBytes q) :
    ¬NativeRustcVm.InRange (tA m0) tstateBytes q ∧
      ¬NativeRustcVm.InRange a.words (8 * a.len) q := by
  have g := c.geo
  rw [c.inQ] at hq
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [c.inT] at h; have := g.pT; omega
  · rw [c.inA] at h; have := g.pA; omega

end Ctx

end

end

end NativeRustcVmX64.Whir.Levels.FL
