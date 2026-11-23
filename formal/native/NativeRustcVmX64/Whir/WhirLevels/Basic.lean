module

public import NativeRustcVmX64.Whir.WhirLevels.Exec
public import NativeRustcVmX64.Whir.WhirLevels.ArgFrame
public import NativeRustcVmX64.Whir.WhirLevels.Model
public import NativeRustcVmX64.Whir.WhirLevels.Same
public import NativeRustcVmX64.Spec.Whir
public import NativeRustcVmX64.Sumcheck.Ctx
public import NativeRustcVm.Wire.WordsFacts
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# `whir_levels`: its frame, its context, its invariant (x86-64)

From the entry `m0` (the `TState` RDI, `logN` RSI, `laneFolds` RDX, the basis RCX, the levels R8,
their count R9, the state `w` the stack argument): the 112-byte frame (`Fr`: `Frame` and memory
changed only in the stack and the outputs `outs`), the entry's facts (`Ctx`, the levels the ladder
`ladderW logN rate`), the loop's invariant at its head `NativeRustcVmX64.Vm.WhirLevels.label_1` before level `k`'s fold
rounds (`Head`): RBX the level, R12 `24` times the levels left, R13 `k - 1`, R15 the `TState`, RBP
the state, the frame's words (`24` the last index, `32` `laneFolds`, `40` the basis, `48`
`1 - n`, `56` `logN`), the run so far the model's.
-/

namespace NativeRustcVmX64.Whir.Levels.WL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck

@[expose] public section

/-- The `TState`. -/
abbrev tA (m0 : MachineData) : BitVec 64 := reg m0 .rdi
/-- The state `w` (`WhirW`), the stack argument. -/
abbrev pA (m0 : MachineData) : BitVec 64 := stackArg m0 0
/-- The levels. -/
abbrev lvA (m0 : MachineData) : BitVec 64 := reg m0 .r8
/-- The basis. -/
abbrev bA (m0 : MachineData) : BitVec 64 := reg m0 .rcx
/-- `logN`. -/
abbrev logN (m0 : MachineData) : Nat := (reg m0 .rsi).toNat
/-- `laneFolds`. -/
abbrev lf (m0 : MachineData) : Nat := (reg m0 .rdx).toNat
/-- The frame's base. -/
abbrev fa (m0 : MachineData) : BitVec 64 := stackBelow m0 112

/-- The outputs: the state and the `TState`. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (pA m0) whirBytes q ∨ NativeRustcVm.InRange (tA m0) tstateBytes q

/-- Memory changed only in the stack and the outputs. -/
abbrev Sm (m0 d : MachineData) : Prop :=
  NativeRustcVm.SameOutside m0.dmem d.dmem (fun q ↦
    NativeRustcVm.InRange (stackBelow m0 whirLevelsStack) whirLevelsStack q ∨ outs m0 q)

/-- **The frame**, RSP at offset `o`: `Frame`, memory changed only in the stack and the outputs. -/
structure Fr (m0 : MachineData) (o : Nat) (d : MachineData) : Prop where
  frame : Frame m0 112 slots o d
  same : Sm m0 d

/-- The whole run. -/
abbrev runAll (s0 : TState) (levels : List Whir.Level) (b : BasisW) (claim : EW)
    (m0 : MachineData) : Option (Unit × TState) :=
  (whirLevels (logN m0) (lf m0) b 0 levels ⟨claim, #[], #[]⟩).run s0

/-- The frame's word `48`, `1 - n`. -/
abbrev w48 (m0 : MachineData) : UInt64 := .ofBitVec (1#64 - reg m0 .r9)

section
variable [Labels]

/-- **The entry's facts**, the levels the ladder of `logN` at the rate exponent `rate`. -/
structure Ctx (a : DecArea) (s0 : TState) (levels : List Whir.Level) (ba : BasisAddrs)
    (b : BasisW) (claim : EW) (m0 : MachineData) (rate : Nat) : Prop where
  wt : WhirT m0 (tA m0) a whirLevelsStack
  args : ArgsOk m0 1
  ts0 : TStateAt m0.dmem (tA m0) a s0
  roots0 : s0.roots.size + levels.length ≤ maxRoots
  adm : Whir.Admissible (logN m0) rate
  lad : levels = ladderW (logN m0) rate
  len : levels.length = (reg m0 .r9).toNat
  lvs : LevelsAt m0.dmem (lvA m0) levels
  bw : BasisWAt m0.dmem (bA m0) ba b
  ws0 : WhirStateAt m0.dmem (pA m0) ⟨claim, #[], #[]⟩
  pout : WhirOut m0 (tA m0) a (pA m0) whirBytes whirLevelsStack
  lin : WhirIn m0 (lvA m0) (levelBytes * levels.length) whirLevelsStack
  lp : NativeRustcVm.Apart (lvA m0) (levelBytes * levels.length) (pA m0) whirBytes
  lt : NativeRustcVm.Apart (lvA m0) (levelBytes * levels.length) (tA m0) tstateBytes
  bp : BasisIn m0 (bA m0) ba whirLevelsStack (pA m0) whirBytes
  bt : BasisIn m0 (bA m0) ba whirLevelsStack (tA m0) tstateBytes
  bap : BasisApart (bA m0) ba
  at' : NativeRustcVm.Apart (rspOf m0 + 8#64) 8 (tA m0) tstateBytes
  ap : NativeRustcVm.Apart (rspOf m0 + 8#64) 8 (pA m0) whirBytes
  got : GotAt m0 whirLevelsStack
    ([(tA m0, tstateBytes), (a.words, 8 * a.len), (pA m0, whirBytes),
      (lvA m0, levelBytes * levels.length), (rspOf m0 + 8#64, 8)] ++ rodataAreas)
    ["memcpy", "memset"]

/-- **The loop's registers and the frame's words** at level `k`, RSP at offset `o`: RBX the level,
R12 `24` times the levels left, R13 `k - 1`, R15 the `TState`, RBP the state; the words `24` (the
last index), `32` (`laneFolds`), `40` (the basis), `48` (`1 - n`), `56` (`logN`). -/
structure Loop (levels : List Whir.Level) (m0 : MachineData) (k o : Nat) (d : MachineData) :
    Prop where
  fr : Fr m0 o d
  rbx : reg d .rbx = lvA m0 + BitVec.ofNat 64 (levelBytes * k)
  r12 : reg d .r12 = BitVec.ofNat 64 (levelBytes * (levels.length - k))
  r13 : reg d .r13 = BitVec.ofNat 64 k - 1#64
  r15 : reg d .r15 = tA m0
  rbp : reg d .rbp = pA m0
  w24 : NativeRustcVm.WordAt d.dmem (off (fa m0) 24) (.ofNat (levels.length - 1))
  w32 : NativeRustcVm.WordAt d.dmem (off (fa m0) 32) (.ofBitVec (reg m0 .rdx))
  w40 : NativeRustcVm.WordAt d.dmem (off (fa m0) 40) (.ofBitVec (reg m0 .rcx))
  w48 : NativeRustcVm.WordAt d.dmem (off (fa m0) 48) (w48 m0)
  w56 : NativeRustcVm.WordAt d.dmem (off (fa m0) 56) (.ofBitVec (reg m0 .rsi))

/-- **Before level `k`'s fold rounds** (at `NativeRustcVmX64.Vm.WhirLevels.label_1`): `Loop`, the `TState` `s` and the
state `w` (`alphasAt k` `α`s, `2 k` glued claims), room for a root per level left, the run the
model's from level `k`. -/
structure Head (a : DecArea) (s0 : TState) (levels : List Whir.Level) (b : BasisW) (claim : EW)
    (m0 : MachineData) (k : Nat) (s : TState) (w : WhirStateW) (d : MachineData) : Prop where
  loop : Loop levels m0 k 8 d
  ts : TStateAt d.dmem (tA m0) a s
  ws : WhirStateAt d.dmem (pA m0) w
  lt : k < levels.length
  alphas : w.alphas.size = alphasAt k
  glued : w.glued.size = 2 * k
  roots : s.roots.size + (levels.length - k) ≤ maxRoots
  run : runAll s0 levels b claim m0 =
    (whirLevels (logN m0) (lf m0) b k (levels.drop k) w).run s

/-- **After level `k`'s fold rounds** (at `b4`): `Loop`, the `TState` `s`, the state `w` and the
rounds `rs`, the run the model's `final_level` (the last level) or `next_level` then the levels
after. -/
structure Mid (a : DecArea) (s0 : TState) (levels : List Whir.Level) (b : BasisW) (claim : EW)
    (m0 : MachineData) (rate k : Nat) (s : TState) (w : WhirStateW) (rs : Array FoldRoundW)
    (d : MachineData) : Prop where
  loop : Loop levels m0 k 8 d
  ts : TStateAt d.dmem (tA m0) a s
  wa : WhirAt d.dmem (pA m0) w rs
  lt : k < levels.length
  alphas : w.alphas.size = alphasAt (k + 1)
  glued : w.glued.size = 2 * k
  roots : s.roots.size + (levels.length - k) ≤ maxRoots
  fin : k + 1 = levels.length → runAll s0 levels b claim m0 =
    (finalLevelM k (lvl (logN m0) rate k) (logN m0 - w.alphas.size) (lf m0) b w rs).run s
  nxt : k + 1 < levels.length → runAll s0 levels b claim m0 =
    ((nextLevelM k (lvl (logN m0) rate k) (lvl (logN m0) rate (k + 1)) (logN m0 - w.alphas.size)
      w rs).run s).bind fun p ↦
        (whirLevels (logN m0) (lf m0) b (k + 1) (levels.drop (k + 1)) p.1).run p.2

/-- The function's goal. -/
abbrev Goal (a : DecArea) (s0 : TState) (levels : List Whir.Level) (b : BasisW) (claim : EW)
    (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
    WhirLevelsPost a s0 levels b claim m0 st.data

end

end

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 112 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide
theorem slots_ge : ∀ p ∈ slots, 64 ≤ p.1 := by decide

theorem fold_le : 112 + foldRoundsStack ≤ whirLevelsStack := by
  unfold whirLevelsStack; exact Nat.add_le_add_left (Nat.le_max_left _ _) _
theorem next_le : 112 + nextLevelStack ≤ whirLevelsStack := by
  unfold whirLevelsStack
  exact Nat.add_le_add_left ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)) _
theorem final_le : finalLevelStack ≤ whirLevelsStack := by
  unfold whirLevelsStack
  exact ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)).trans (Nat.le_add_left _ _)
theorem frame_le : 112 ≤ whirLevelsStack := by unfold whirLevelsStack; omega

section
variable [Labels] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat} {o : Nat}

theorem Ctx.of_pre (h : WhirLevelsPre a s0 levels ba b claim m0) :
    ∃ rate, Ctx a s0 levels ba b claim m0 rate := by
  obtain ⟨hwt, hargs, hts, hroots, ⟨rate, hlad⟩, hlen, hlvs, hbw, hws, hpo, hlin, hlp, hlt, hbp,
    hbt, hbap, hat, hap, hgot⟩ := h
  by_cases hadm : Whir.Admissible (reg m0 .rsi).toNat rate
  · rw [ladder_eq hadm, Option.some.injEq] at hlad
    exact ⟨rate, hwt, hargs, hts, hroots, hadm, hlad.symm, hlen, hlvs, hbw, hws, hpo, hlin, hlp,
      hlt, hbp, hbt, hbap, hat, hap, hgot⟩
  · rw [ladder_none hadm] at hlad
    cases hlad

namespace Ctx

variable (c : Ctx a s0 levels ba b claim m0 rate)
include c

theorem stack : StackOk m0 whirLevelsStack := c.wt.1
theorem hN : whirLevelsStack ≤ (rspOf m0).toNat := c.wt.1.1
theorem sp8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := c.wt.1.2.1
theorem sp16 : (rspOf m0).toNat + 16 ≤ 2 ^ 64 := by have := c.args.2; omega

theorem logN_le : 16 ≤ logN m0 ∧ logN m0 ≤ 30 := by
  have := admissible_iff.mp c.adm; omega

theorem len_eq : levels.length = nOf (logN m0) := by rw [c.lad, length_ladderW]

theorem len_le : 3 ≤ levels.length ∧ levels.length ≤ 6 := by
  rw [c.len_eq]; exact nOf_le _

theorem getElem {k : Nat} (h : k < levels.length) : levels[k] = lvl (logN m0) rate k := by
  have h' : k < (ladderW (logN m0) rate).length := by rw [← c.lad]; exact h
  simp only [c.lad]
  exact ladderW_getElem h'

theorem drop_eq {k : Nat} (h : k < levels.length) :
    levels.drop k = lvl (logN m0) rate k :: levels.drop (k + 1) := by
  rw [drop_cons h, c.getElem h]

/-- The `Sumcheck` context of the calls. -/
theorem sctx : Sumcheck.Ctx m0 (tA m0) a whirLevelsStack 112 :=
  ⟨c.wt.1, c.wt.2.1, c.wt.2.2.2.1, c.ts0.footprint, frame_le⟩

theorem fa_toNat : (fa m0).toNat = (rspOf m0).toNat - 112 :=
  stackBelow_toNat (by have := c.hN; have := frame_le; omega)

theorem stk_toNat : (stackBelow m0 whirLevelsStack).toNat = (rspOf m0).toNat - whirLevelsStack :=
  stackBelow_toNat c.hN

theorem arg_toNat : (rspOf m0 + 8#64).toNat = (rspOf m0).toNat + 8 := by
  have := c.sp16
  rw [BitVec.toNat_add, show (8#64 : BitVec 64).toNat = 8 from rfl]
  omega

theorem noWrap_arg : NativeRustcVm.NoWrap (rspOf m0 + 8#64) 8 := by
  unfold NativeRustcVm.NoWrap; rw [c.arg_toNat]; have := c.sp16; omega

/-- The frame's region with the argument word: mapped, not wrapping. -/
theorem region_ok {d : MachineData} (hk : Kept m0.dmem d.dmem) :
    NativeRustcVm.Mapped d.dmem (fa m0) 128 ∧ NativeRustcVm.NoWrap (fa m0) 128 := by
  have hfm := frame_mapped (F := 112) c.stack frame_le
  have ham := c.args.1
  have hf := c.fa_toNat
  have ha := c.arg_toNat
  have := c.hN; have := frame_le
  have := c.sp16
  refine ⟨fun i hi ↦ hk _ ?_, ?_⟩
  · by_cases h : i < 120
    · exact hfm i h
    · have e : fa m0 + BitVec.ofNat 64 i = rspOf m0 + 8#64 + BitVec.ofNat 64 (i - 120) := by
        apply BitVec.eq_of_toNat_eq
        rw [NativeRustcVm.toNat_add_ofNat (by omega), NativeRustcVm.toNat_add_ofNat (by omega), hf,
          ha]
        omega
      rw [e]
      exact ham _ (by omega)
  · unfold NativeRustcVm.NoWrap; rw [hf]; omega

/-- The frame's region, without the argument word. -/
theorem frame_ok {d : MachineData} (hk : Kept m0.dmem d.dmem) :
    NativeRustcVm.Mapped d.dmem (fa m0) 120 ∧ NativeRustcVm.NoWrap (fa m0) 120 :=
  ⟨(c.region_ok hk).1.mono (by omega), (c.region_ok hk).2.mono (by omega)⟩

/-- The outputs are apart from the stack, its return address and the argument word. -/
theorem outs_not_stack {q : BitVec 64} (hq : outs m0 q) :
    ¬NativeRustcVm.InRange (stackBelow m0 whirLevelsStack) (whirLevelsStack + 8) q ∧
      ¬NativeRustcVm.InRange (rspOf m0 + 8#64) 8 q := by
  have hnS := noWrap_stackBelow c.stack
  have hna := c.noWrap_arg
  rcases hq with hq | hq
  · exact ⟨NativeRustcVm.Apart.not_inRange c.pout.1.2.2.2.2.1 c.pout.1.2.1 hnS hq,
      NativeRustcVm.Apart.not_inRange (NativeRustcVm.Apart.symm c.ap) c.pout.1.2.1 hna hq⟩
  · exact ⟨NativeRustcVm.Apart.not_inRange c.wt.2.2.2.1.1 c.ts0.footprint.1.2 hnS hq,
      NativeRustcVm.Apart.not_inRange (NativeRustcVm.Apart.symm c.at') c.ts0.footprint.1.2 hna hq⟩

/-- A byte of the frame's region (with the argument word) is in the stack or the argument word. -/
theorem region_split {j : Nat} (hj : j < 128) :
    NativeRustcVm.InRange (stackBelow m0 whirLevelsStack) (whirLevelsStack + 8) (off (fa m0) j) ∨
      NativeRustcVm.InRange (rspOf m0 + 8#64) 8 (off (fa m0) j) := by
  have hf := c.fa_toNat
  have := c.hN; have := frame_le
  have := c.sp16
  have hs := c.stk_toNat
  have ha := c.arg_toNat
  have ho : (off (fa m0) j).toNat = (rspOf m0).toNat - 112 + j := by
    rw [toNat_off (by omega), hf]
  by_cases h : j < 120
  · left
    rw [inRange_iff' (noWrap_stackBelow c.stack), ho, hs]
    omega
  · right
    rw [inRange_iff' c.noWrap_arg, ho, ha]
    omega

/-- The outputs miss the frame's region. -/
theorem outs_not_frame {q : BitVec 64} (hq : outs m0 q) : ¬NativeRustcVm.InRange (fa m0) 128 q := by
  intro hin
  obtain ⟨j, hj, rfl⟩ := NativeRustcVm.InRange.exists hin
  have := c.outs_not_stack hq
  rcases c.region_split hj with h | h
  · exact this.1 h
  · exact this.2 h

/-- The stack below RSP is apart from the argument word. -/
theorem stack_not_arg {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow m0 whirLevelsStack) whirLevelsStack q) :
    ¬NativeRustcVm.InRange (rspOf m0 + 8#64) 8 q := by
  have := c.hN; have := c.sp16; have hs := c.stk_toNat; have ha := c.arg_toNat
  rw [inRange_iff' ((noWrap_stackBelow c.stack).mono (by omega)), hs] at hq
  rw [inRange_iff' c.noWrap_arg, ha]
  omega

/-- The argument word stays in the frame's states. -/
theorem arg_keep {d : MachineData} (hsm : Sm m0 d) :
    NativeRustcVm.WordAt d.dmem (rspOf m0 + 8#64) (UInt64.ofBitVec (pA m0)) := by
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
  have hin : NativeRustcVm.InRange (rspOf m0 + 8#64) 8 (rspOf m0 + 8#64 + BitVec.ofNat 64 i) :=
    NativeRustcVm.inRange_add hi8 (by omega)
  rcases hq with hq | hq
  · exact c.stack_not_arg hq hin
  · exact (c.outs_not_stack hq).2 hin

/-- The rodata items are apart from the outputs. -/
theorem ro_not_outs (t : NativeRustcVm.Data.Item) {q : BitVec 64} (hq : outs m0 q) :
    ¬NativeRustcVm.InRange (rodataAddr t) t.bytes.length q := by
  have hro := c.wt.2.2.1
  rcases hq with hq | hq
  · exact NativeRustcVm.Apart.not_inRange (c.pout.2 t) c.pout.1.2.1 (hro.noWrap t) hq
  · exact NativeRustcVm.Apart.not_inRange (c.wt.2.2.2.2 t) c.ts0.footprint.1.2 (hro.noWrap t) hq

/-- The round constants' bytes kept where memory changed only in the stack and the outputs. -/
theorem rc_keep {d : MachineData} (hs : Sm m0 d) :
    ∀ i < 192, d.dmem.get? (rcAddr + BitVec.ofNat 64 i) =
      m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) := by
  have hrc := c.wt.2.1
  have sc := c.sctx
  intro i hi
  refine hs _ fun hq ↦ ?_
  have hin : NativeRustcVm.InRange rcAddr 192 (rcAddr + BitVec.ofNat 64 i) :=
    NativeRustcVm.inRange_add hi (by have := hrc.2.1; unfold NativeRustcVm.NoWrap at this; omega)
  rcases hq with hq | hq | hq
  · exact sc.not_rc_stack hq hin
  · exact sc.out_not_rc c.pout.1 hq hin
  · exact sc.not_rc_tstate hq hin

/-- The `Sumcheck` context with a frame of `F` bytes. -/
theorem sctxF {F : Nat} (hF : F ≤ whirLevelsStack) :
    Sumcheck.Ctx m0 (tA m0) a whirLevelsStack F :=
  ⟨c.wt.1, c.wt.2.1, c.wt.2.2.2.1, c.ts0.footprint, hF⟩

/-- At a call (RSP at the frame's base). -/
theorem at_call {d : MachineData} (hf : Fr m0 0 d) : At m0 112 d :=
  At.of_frame hf.frame (c.rc_keep hf.same)

/-- The read-only data for a callee with `N'` bytes of stack below `F` bytes. -/
theorem rodataAt {F : Nat} {d : MachineData} (hat : At m0 F d) (hs : Sm m0 d) {N' : Nat}
    (hle : F + N' ≤ whirLevelsStack) : RodataAt d N' := by
  have hro := c.wt.2.2.1
  have hsb : stackBelow d N' = stackBelow m0 (F + N') :=
    stackBelow_callee hat.sp (by have := c.hN; omega)
  intro t
  refine ⟨(hro.bytesAt t).of_sameOutside hs fun i hi hq ↦ ?_, hro.noWrap t, ?_⟩
  · have hin : NativeRustcVm.InRange (rodataAddr t) t.bytes.length
        (rodataAddr t + BitVec.ofNat 64 i) :=
      NativeRustcVm.inRange_add hi (by have := hro.noWrap t; unfold NativeRustcVm.NoWrap at this; omega)
    rcases hq with hq | hq
    · exact NativeRustcVm.Apart.not_inRange (hro.apart t) (hro.noWrap t) (noWrap_stackBelow c.stack)
        hin (inRange_mono hq (by omega))
    · exact c.ro_not_outs t hq hin
  · rw [hsb]
    have := hro.apart t
    have h1 := stackBelow_toNat (m := m0) (n := F + N') (by have := c.hN; omega)
    have h2 := c.stk_toNat
    refine NativeRustcVm.Apart.mono_right this ?_ ?_ <;> rw [h1, h2] <;> omega

/-- **The transcript's context** for a callee with `N'` bytes of stack below `F` bytes. -/
theorem whirT {F : Nat} {d : MachineData} (hat : At m0 F d) (hs : Sm m0 d) {N' : Nat}
    (hle : F + N' ≤ whirLevelsStack) : WhirT d (tA m0) a N' :=
  ⟨(c.sctxF (by omega)).stackOk hat hle, (c.sctxF (by omega)).rcAt hat hle, c.rodataAt hat hs hle,
    (c.sctxF (by omega)).tstateOk hat hle, c.wt.2.2.2.2⟩

/-- An output for a callee. -/
theorem whirOut {F : Nat} {d : MachineData} (hat : At m0 F d) {N' : Nat}
    (hle : F + N' ≤ whirLevelsStack) {o : BitVec 64} {n : Nat}
    (h : WhirOut m0 (tA m0) a o n whirLevelsStack) : WhirOut d (tA m0) a o n N' :=
  ⟨(c.sctxF (by omega)).outOk hat hle h.1, h.2⟩

/-- An input for a callee. -/
theorem whirIn {F : Nat} {d : MachineData} (hat : At m0 F d) {N' : Nat}
    (hle : F + N' ≤ whirLevelsStack) {x : BitVec 64} {n : Nat}
    (h : WhirIn m0 x n whirLevelsStack) : WhirIn d x n N' :=
  ⟨⟨Mapped.keeps h.1.1 hat.kept, h.1.2⟩, (c.sctxF (by omega)).apart hat hle h.2⟩

/-- The basis's areas for a callee. -/
theorem basisIn {F : Nat} {d : MachineData} (hat : At m0 F d) {N' : Nat}
    (hle : F + N' ≤ whirLevelsStack) {x o : BitVec 64} {n : Nat}
    (h : BasisIn m0 x ba whirLevelsStack o n) : BasisIn d x ba N' o n :=
  ⟨c.whirIn hat hle h.1, h.2.1, fun r hr ↦ ⟨c.whirIn hat hle (h.2.2 r hr).1, (h.2.2 r hr).2⟩⟩

/-- Bytes apart from the stack and the outputs stay the same. -/
theorem same {d : MachineData} (hsm : Sm m0 d) {x : BitVec 64} {n : Nat}
    (hnw : NativeRustcVm.NoWrap x n)
    (hs : NativeRustcVm.Apart x n (stackBelow m0 whirLevelsStack) (whirLevelsStack + 8))
    (hp : NativeRustcVm.Apart x n (pA m0) whirBytes)
    (ht : NativeRustcVm.Apart x n (tA m0) tstateBytes) :
    NativeRustcVm.Layout.Same m0.dmem d.dmem x n := by
  refine NativeRustcVm.Layout.Same.of_sameOutside hsm fun j hj hq ↦ ?_
  rcases hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange_add hs hnw (noWrap_stackBelow c.stack) hj
      (inRange_mono hq (by omega))
  · exact NativeRustcVm.Apart.not_inRange_add hp hnw c.pout.1.2.1 hj hq
  · exact NativeRustcVm.Apart.not_inRange_add ht hnw c.ts0.footprint.1.2 hj hq

/-- Level `k` where memory changed only in the stack and the outputs. -/
theorem levelAt {d : MachineData} (hsm : Sm m0 d) {k : Nat} (hk : k < levels.length) :
    LevelAt d.dmem (lvA m0 + BitVec.ofNat 64 (levelBytes * k)) (lvl (logN m0) rate k) := by
  have hs := c.same hsm c.lin.1.2 c.lin.2 c.lp c.lt
  have := c.lvs k hk
  rw [c.getElem hk] at this
  refine LevelAt.of_same this (hs.sub (o := levelBytes * k) (k := levelBytes) ?_)
  have := Nat.mul_le_mul_left levelBytes (show k + 1 ≤ levels.length by omega)
  rw [Nat.mul_succ] at this
  exact this

/-- The basis where memory changed only in the stack and the outputs. -/
theorem basis_at {d : MachineData} (hsm : Sm m0 d) : BasisWAt d.dmem (bA m0) ba b :=
  basisWAt_of_same c.bw (c.same hsm c.bp.1.1.2 c.bp.1.2 c.bp.2.1 c.bt.2.1) fun r hr ↦
    c.same hsm (c.bp.2.2 r hr).1.1.2 (c.bp.2.2 r hr).1.2 (c.bp.2.2 r hr).2 (c.bt.2.2 r hr).2

end Ctx

end

end

end NativeRustcVmX64.Whir.Levels.WL
