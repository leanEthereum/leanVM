module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Spec.Sumcheck

/-!
# Calls from a frame on the transcript (x86-64)

A function entered in `m0` with `N` bytes of stack (its callees' included), holding the `TState`
at `t` with its decoded area `a`, its frame the `F` bytes below the entry's RSP (`Ctx`). In a
state `d` at a call (`At`: RSP at the frame's base, the entry's bytes kept, the round constants'
bytes the same), a callee with `Nc` bytes of stack, `F + Nc ≤ N`, gets its `StackOk`, `RcAt`,
`TStateOk`, an `OutOk` output (`Ctx.stackOk`, …); a range of the frame from offset `8` is an
output of it (`Ctx.outOk_frame`); its stack is in the function's, below the frame
(`Ctx.inRange_callee`).

`Written.inRegion`: a block's writes are in its environment's regions.
-/

namespace NativeRustcVmX64.Sumcheck

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVmX64.Transcript

@[expose] public section

/-- The function's context: its stack, the round constants, the `TState` and its area apart from
the stack and each other, a frame of `F ≤ N` bytes. -/
structure Ctx [Labels] (m0 : MachineData) (t : BitVec 64) (a : DecArea) (N F : Nat) : Prop where
  stack : StackOk m0 N
  rc : RcAt m0 N
  tok : TStateOk m0 t a N
  fp : Footprint m0.dmem t a
  le : F ≤ N

/-- The state `d` at a call from the frame: RSP at the frame's base, the entry's bytes kept, the
round constants' bytes the same. -/
structure At [Labels] (m0 : MachineData) (F : Nat) (d : MachineData) : Prop where
  sp : rspOf d = stackBelow m0 F
  kept : Kept m0.dmem d.dmem
  rc : ∀ i < 192, d.dmem.get? (rcAddr + BitVec.ofNat 64 i) =
    m0.dmem.get? (rcAddr + BitVec.ofNat 64 i)

end

public section

variable [Labels] {m0 d : MachineData} {t : BitVec 64} {a : DecArea} {N F Nc : Nat}

namespace Ctx

theorem spN (c : Ctx m0 t a N F) : N ≤ (rspOf m0).toNat := c.stack.1

theorem sp8 (c : Ctx m0 t a N F) : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := c.stack.2.1

theorem stk (c : Ctx m0 t a N F) : (stackBelow m0 N).toNat = (rspOf m0).toNat - N :=
  stackBelow_toNat c.spN

theorem fr (c : Ctx m0 t a N F) : (stackBelow m0 F).toNat = (rspOf m0).toNat - F :=
  stackBelow_toNat (by have := c.spN; have := c.le; omega)

theorem stackOk (c : Ctx m0 t a N F) (h : At m0 F d) (hle : F + Nc ≤ N) : StackOk d Nc :=
  stackOk_callee c.stack h.kept h.sp hle

theorem rcAt (c : Ctx m0 t a N F) (h : At m0 F d) (hle : F + Nc ≤ N) : RcAt d Nc :=
  RcAt.callee c.rc h.rc h.sp c.spN hle

theorem apart (c : Ctx m0 t a N F) (h : At m0 F d) (hle : F + Nc ≤ N) {x : BitVec 64} {n : Nat}
    (hx : NativeRustcVm.Apart x n (stackBelow m0 N) (N + 8)) :
    NativeRustcVm.Apart x n (stackBelow d Nc) (Nc + 8) :=
  apart_callee hx h.sp c.spN hle

theorem tstateOk (c : Ctx m0 t a N F) (h : At m0 F d) (hle : F + Nc ≤ N) : TStateOk d t a Nc :=
  ⟨c.apart h hle c.tok.1, c.apart h hle c.tok.2.1, c.tok.2.2⟩

theorem outOk (c : Ctx m0 t a N F) (h : At m0 F d) (hle : F + Nc ≤ N) {o : BitVec 64} {n : Nat}
    (ho : OutOk m0 t a o n N) : OutOk d t a o n Nc :=
  ⟨Mapped.keeps ho.1 h.kept, ho.2.1, ho.2.2.1, ho.2.2.2.1, c.apart h hle ho.2.2.2.2.1,
    ho.2.2.2.2.2⟩

theorem noWrap_stack (c : Ctx m0 t a N F) : NativeRustcVm.NoWrap (stackBelow m0 N) (N + 8) :=
  noWrap_stackBelow c.stack

theorem noWrap_frame (c : Ctx m0 t a N F) : NativeRustcVm.NoWrap (stackBelow m0 F) (F + 8) :=
  frame_noWrap c.stack c.le

theorem mapped_frame (c : Ctx m0 t a N F) (hk : Kept m0.dmem d.dmem) :
    NativeRustcVm.Mapped d.dmem (stackBelow m0 F) (F + 8) :=
  Mapped.keeps (frame_mapped c.stack c.le) hk

/-- What is apart from the stack is apart from the bytes `o` to `o + k` of the frame. -/
theorem apart_of_stack (c : Ctx m0 t a N F) {x : BitVec 64} {n o k : Nat}
    (hx : NativeRustcVm.Apart x n (stackBelow m0 N) (N + 8)) (hk : o + k ≤ F) :
    NativeRustcVm.Apart x n (off (stackBelow m0 F) o) k := by
  have := c.spN; have := c.sp8; have := c.le
  have hf := c.fr; have hs := c.stk
  unfold NativeRustcVm.Apart at hx ⊢
  rw [toNat_off (by omega), hf]
  rw [hs] at hx
  omega

/-- The frame's bytes from `o ≥ 8` are apart from a callee's stack. -/
theorem apart_frame_callee (c : Ctx m0 t a N F) (h : At m0 F d) (hle : F + Nc ≤ N) {o n : Nat}
    (ho : 8 ≤ o) (hon : o + n ≤ F) :
    NativeRustcVm.Apart (off (stackBelow m0 F) o) n (stackBelow d Nc) (Nc + 8) := by
  have := c.spN; have := c.sp8; have := c.le
  have hf := c.fr
  have hc : (stackBelow d Nc).toNat = (rspOf m0).toNat - (F + Nc) := by
    rw [stackBelow_callee h.sp (by omega), stackBelow_toNat (by omega)]
  unfold NativeRustcVm.Apart
  rw [toNat_off (by omega), hf, hc]
  omega

/-- **The frame's bytes from `o ≥ 8` as a callee's output.** -/
theorem outOk_frame (c : Ctx m0 t a N F) (h : At m0 F d) (hle : F + Nc ≤ N) {o n : Nat}
    (ho : 8 ≤ o) (hon : o + n ≤ F) : OutOk d t a (off (stackBelow m0 F) o) n Nc := by
  have hnw := c.noWrap_frame
  unfold NativeRustcVm.NoWrap at hnw
  refine ⟨mapped_off (c.mapped_frame h.kept) (by omega), ?_,
    Apart.symm' (c.apart_of_stack c.tok.1 hon), Apart.symm' (c.apart_of_stack c.tok.2.1 hon),
    c.apart_frame_callee h hle ho hon, Apart.symm' (c.apart_of_stack c.rc.2.2 hon)⟩
  unfold NativeRustcX64.NoWrap
  rw [toNat_off (by omega)]
  omega

/-- A callee's stack is in the function's, below the frame's base. -/
theorem inRange_callee (c : Ctx m0 t a N F) (h : At m0 F d) (hle : F + Nc ≤ N) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow d Nc) Nc q) :
    NativeRustcVm.InRange (stackBelow m0 N) N q ∧
      ¬ NativeRustcVm.InRange (stackBelow m0 F) (F + 8) q :=
  NativeRustcVmX64.Transcript.inRange_callee h.sp c.sp8 c.spN hle hq

/-- The frame below its return address is in the stack. -/
theorem inRange_frame (c : Ctx m0 t a N F) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow m0 F) F q) :
    NativeRustcVm.InRange (stackBelow m0 N) N q :=
  inRange_frame_stack c.sp8 c.spN c.le hq

/-- The round constants are apart from the stack. -/
theorem not_rc_stack (c : Ctx m0 t a N F) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow m0 N) N q) : ¬ NativeRustcVm.InRange rcAddr 192 q :=
  fun h ↦ not_inRange_of_apart c.rc.2.2 c.rc.2.1 c.noWrap_stack h (inRange_mono hq (by omega))

/-- The round constants are apart from the `TState`. -/
theorem not_rc_tstate (c : Ctx m0 t a N F) {q : BitVec 64}
    (hq : NativeRustcVm.InRange t tstateBytes q) : ¬ NativeRustcVm.InRange rcAddr 192 q :=
  fun h ↦ not_inRange_of_apart c.tok.2.2 c.fp.1.2 c.rc.2.1 hq h

/-- The `TState` and its area are apart from the stack. -/
theorem stack_not_t (c : Ctx m0 t a N F) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow m0 N) N q) :
    ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
  ⟨fun h ↦ not_inRange_of_apart c.tok.1 c.fp.1.2 c.noWrap_stack h (inRange_mono hq (by omega)),
    fun h ↦ not_inRange_of_apart c.tok.2.1 c.fp.2.1.2 c.noWrap_stack h
      (inRange_mono hq (by omega))⟩

/-- An output `o` is apart from the `TState`, its area. -/
theorem out_not_t (c : Ctx m0 t a N F) {o : BitVec 64} {n : Nat} (ho : OutOk m0 t a o n N)
    {q : BitVec 64} (hq : NativeRustcVm.InRange o n q) :
    ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
  ⟨not_inRange_of_apart ho.2.2.1 ho.2.1 c.fp.1.2 hq,
    not_inRange_of_apart ho.2.2.2.1 ho.2.1 c.fp.2.1.2 hq⟩

/-- An output `o` is apart from the stack. -/
theorem out_not_stack (c : Ctx m0 t a N F) {o : BitVec 64} {n : Nat} (ho : OutOk m0 t a o n N)
    {q : BitVec 64} (hq : NativeRustcVm.InRange o n q) :
    ¬ NativeRustcVm.InRange (stackBelow m0 N) N q :=
  fun h ↦ not_inRange_of_apart ho.2.2.2.2.1 ho.2.1 c.noWrap_stack hq (inRange_mono h (by omega))

/-- An output `o` is apart from the round constants. -/
theorem out_not_rc (c : Ctx m0 t a N F) {o : BitVec 64} {n : Nat} (ho : OutOk m0 t a o n N)
    {q : BitVec 64} (hq : NativeRustcVm.InRange o n q) : ¬ NativeRustcVm.InRange rcAddr 192 q :=
  not_inRange_of_apart ho.2.2.2.2.2 ho.2.1 c.rc.2.1 hq


/-- A callee inherits loader slots when its caller's writes stay in protected areas. -/
theorem gotAt (c : Ctx m0 t a N F) (h : At m0 F d) (hle : F + Nc ≤ N)
    {areas areas' : List (BitVec 64 × Nat)} {symbols : List Label}
    (hg : GotAt m0 N areas symbols) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside m0.dmem d.dmem R)
    (hR : ∀ q, R q → NativeRustcVm.InRange (stackBelow m0 N) N q ∨
      ∃ x ∈ areas, NativeRustcVm.NoWrap x.1 x.2 ∧ NativeRustcVm.InRange x.1 x.2 q)
    (ha : ∀ l ∈ symbols, ∀ x ∈ areas', Apart (gotAddr l) 8 x.1 x.2) :
    GotAt d Nc areas' symbols := by
  refine hg.transport (fun l hl i hi ↦ hs _ ?_)
    (fun l hl ↦ c.apart h hle (hg.1 l hl).2.2.1) ha
  intro hw
  have hin : NativeRustcVm.InRange (gotAddr l) 8 (gotAddr l + BitVec.ofNat 64 i) :=
    inRange_off_self hi (by decide)
  rcases hR _ hw with hw | ⟨x, hx, hn, hw⟩
  · exact not_inRange_of_apart (hg.1 l hl).2.2.1 (hg.1 l hl).2.1
      c.noWrap_stack hin (inRange_mono hw (by omega))
  · exact not_inRange_of_apart ((hg.1 l hl).2.2.2 x hx) (hg.1 l hl).2.1 hn hin hw
end Ctx

/-- A state at a call from a frame at offset `0`. -/
theorem At.of_frame {sl : Slots} (hf : Frame m0 F sl 0 d)
    (hrc : ∀ i < 192, d.dmem.get? (rcAddr + BitVec.ofNat 64 i) =
      m0.dmem.get? (rcAddr + BitVec.ofNat 64 i)) : At m0 F d :=
  ⟨by rw [hf.sp, off_zero], hf.kept, hrc⟩

omit [Labels] in
/-- **A block's writes are in its regions**, those of `writesIn`. -/
theorem Written.inRegion {env : Env} {S : SState} (hin : writesIn S = true) {q : BitVec 64}
    (h : Written env S q) (hreg : ∀ (r sz : Nat), S.regions[r]? = some sz →
      ∃ b, env.regions[r]? = some (b, sz)) :
    ∃ (r : Nat) (b : BitVec 64) (sz : Nat), env.regions[r]? = some (b, sz) ∧ b.toNat ≤ q.toNat ∧
      q.toNat < b.toNat + sz := by
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := h
  unfold writesIn at hin
  rw [List.all_eq_true] at hin
  have hw' := hin w hw
  obtain ⟨sz', hS'⟩ : ∃ sz', S.regions[w.r]? = some sz' := by
    revert hw'
    cases S.regions[w.r]? with
    | none => simp
    | some x => exact fun _ ↦ ⟨x, rfl⟩
  rw [hS'] at hw'
  simp only [decide_eq_true_eq] at hw'
  obtain ⟨b', hb'⟩ := hreg _ _ hS'
  rw [hb] at hb'
  cases hb'
  exact ⟨w.r, b, _, hb, by omega, by omega⟩

end

end NativeRustcVmX64.Sumcheck
