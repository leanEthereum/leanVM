module

public import NativeRustcVmX64.Sumcheck.Ctx
public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVm.Sumcheck.RoundPoly
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVm.Transcript.Update

/-!
# The sumcheck loop on x86-64: what its three instances share

`TState::sumcheck` (with `sumcheck_plain`'s, `gkr_step`'s or `verify_layer`'s closure) keeps a
frame of `F` bytes below the entry's RSP (`Frame`, the pushed registers' slots from offset `lo`)
and changes, until its exit, only the stack, the `TState` at `t` and the `n` slots at `sl`
(`SF`; `Geo`: the precondition's geometry). A block of the frame keeps it (`SF.block`), a call
too where its changes miss the pushed registers (`SF.call`). A round: `sumcheck_round_poly`
(`Geo.roundPolyPre`, `Geo.afterRoundPoly`), `squeeze` (`Geo.squeezePre`, `Geo.afterSqueeze`),
the challenge into its slot, `poly_eval` (`Geo.polyEvalPre`, `Geo.afterPolyEval`). After `i`
rounds the model's run (`Rounds`).
-/

namespace NativeRustcVmX64.Sumcheck

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Transcript NativeRustcVmX64.Transcript
open NativeVm.Model NativeRustcVm.Sumcheck

@[expose] public section

/-- After `i` rounds of `sumcheckFn claim count E` from `s`: the claim `c`, the challenges in the
first `i` slots at `sl`, the `TState` at `t` the state. -/
def Rounds (d : Mem 64) (t : BitVec 64) (a : DecArea) (sl : BitVec 64) (claim : EW) (count : Nat)
    (E : Nat → Option EW) (s : TState) (i : Nat) (c : EW) : Prop :=
  ∃ xs si, (sumcheckFn claim count E i).run s = some ((xs, c), si) ∧ xs.size = i ∧
    NativeRustcVm.EWsAt d sl xs.toList ∧ TStateAt d t a si

/-- What the loop changes: the stack, the `TState`, the slots. -/
def LChg (m0 : MachineData) (N : Nat) (t sl : BitVec 64) (n : Nat) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (stackBelow m0 N) N q ∨ NativeRustcVm.InRange t tstateBytes q ∨
    NativeRustcVm.InRange sl (16 * n) q

/-- A byte of the frame from offset `lo`: the pushed registers, the return address. -/
def High (m0 : MachineData) (F lo : Nat) (q : BitVec 64) : Prop :=
  ∃ j, lo ≤ j ∧ j < F + 8 ∧ q = off (stackBelow m0 F) j

/-- A sumcheck's geometry: its precondition (`SumcheckOk`, `N` bytes of stack), a frame of
`F` bytes above its callees' stacks, its slots between `lo` and `F`. -/
structure Geo [Labels] (a : DecArea) (s : TState) (m0 : MachineData) (t out sl : BitVec 64)
    (count n N F : Nat) (slots : Slots) (lo : Nat) : Prop where
  ok : SumcheckOk a s m0 t out sl count n N
  le : F + sumcheckCallStack ≤ N
  lo_le : lo ≤ F
  sl : ∀ p ∈ slots, lo ≤ p.1 ∧ p.1 + 8 ≤ F

/-- **The loop's frame**, RSP at offset `o`: the memory changed only in the stack, the `TState`
and the slots. -/
structure SF [Labels] (m0 : MachineData) (t sl : BitVec 64) (n N F : Nat) (slots : Slots) (o : Nat)
    (d : MachineData) : Prop where
  frame : Frame m0 F slots o d
  same : NativeRustcVm.SameOutside m0.dmem d.dmem (LChg m0 N t sl n)

end

public section

theorem rp_le : roundPolyStack ≤ sumcheckCallStack := Nat.le_max_left _ _

theorem sq_le : squeezeStack ≤ sumcheckCallStack :=
  (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

theorem pe_le : polyEvalStack ≤ sumcheckCallStack :=
  (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

/-! ## The stack arguments -/

section
variable {m0 : MachineData} {k : Nat}

/-- The argument words' address. -/
theorem args_toNat (h : ArgsOk m0 k) (hk : 0 < k) :
    (rspOf m0 + 8#64).toNat = (rspOf m0).toNat + 8 := by
  have := h.2
  rw [BitVec.toNat_add, show (8#64).toNat = 8 from rfl]
  omega

/-- The argument words: data memory, not wrapping. -/
theorem args_readable (h : ArgsOk m0 k) (hk : 0 < k) :
    NativeRustcVm.Mapped m0.dmem (rspOf m0 + 8#64) (8 * k) ∧
      NativeRustcVm.NoWrap (rspOf m0 + 8#64) (8 * k) := by
  refine ⟨h.1, ?_⟩
  unfold NativeRustcVm.NoWrap
  rw [args_toNat h hk]
  have := h.2
  omega

/-- The argument words are above the frame and the return address. -/
theorem args_apart {F S : Nat} (hst : StackOk m0 S) (h : ArgsOk m0 k) (hk : 0 < k) (hF : F ≤ S) :
    NativeRustcVm.Apart (stackBelow m0 F) (F + 8) (rspOf m0 + 8#64) (8 * k) := by
  have := hst.1
  unfold NativeRustcVm.Apart
  rw [args_toNat h hk, stackBelow_toNat (by omega)]
  omega

/-- Argument word `i` (`i < k`), at its address. -/
theorem stackArg_wordAt (h : ArgsOk m0 k) {i : Nat} (hi : i < k) :
    NativeRustcVm.WordAt m0.dmem (off (rspOf m0 + 8#64) (8 * i))
      (UInt64.ofBitVec (stackArg m0 i)) := by
  have e : off (rspOf m0 + 8#64) (8 * i) = rspOf m0 + BitVec.ofNat 64 (8 + 8 * i) := by
    rw [off, BitVec.add_assoc, show (8#64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
  have hw := NativeRustcVm.wordAt_of_mapped (d := m0.dmem) (a := off (rspOf m0 + 8#64) (8 * i))
    (fun j hj ↦ by rw [off_add]; exact h.1 _ (by omega))
  rw [e] at hw ⊢
  exact hw

end

/-! ## The model -/

theorem rounds_zero {d : Mem 64} {t : BitVec 64} {a : DecArea} {sl : BitVec 64} {claim : EW}
    {count : Nat} {E : Nat → Option EW} {s : TState} (h : TStateAt d t a s) :
    Rounds d t a sl claim count E s 0 claim :=
  ⟨#[], s, sumcheckFn_zero claim count E s, rfl, NativeRustcVm.ewsAt_nil d sl, h⟩

/-- The first `i` slots hold the challenges, and the challenge at slot `i`. -/
theorem ewsAt_push {d : Mem 64} {sl : BitVec 64} {xs : Array EW} {x : EW}
    (h : NativeRustcVm.EWsAt d sl xs.toList) (hx : NativeRustcVm.EWAt d (off sl (16 * xs.size)) x) :
    NativeRustcVm.EWsAt d sl (xs.push x).toList := by
  rw [Array.toList_push, NativeRustcVm.ewsAt_append_iff, NativeRustcVm.ewsAt_singleton_iff]
  exact ⟨h, by simpa using hx⟩

/-- What a sumcheck leaves on a rejection. -/
theorem sumcheckOut_none {d : Mem 64} {t : BitVec 64} {a : DecArea} {out sl : BitVec 64}
    (h : NativeRustcVm.WordAt d out 0) : SumcheckOut d t a out sl none :=
  ⟨h, fun _ _ _ h ↦ (nomatch h), fun _ _ h ↦ (nomatch h)⟩

/-- What a sumcheck leaves on a success. -/
theorem sumcheckOut_some {d : Mem 64} {t : BitVec 64} {a : DecArea} {out sl : BitVec 64}
    {xs : Array EW} {c : EW} {s' : TState} (ho : OptEWAt d out (some c))
    (hxs : NativeRustcVm.EWsAt d sl xs.toList) (hts : TStateAt d t a s') :
    SumcheckOut d t a out sl (some ((xs, c), s')) :=
  ⟨ho, fun xs' c' s'' h ↦ by cases h; exact hxs, fun x s'' h ↦ by cases h; exact hts⟩

section
variable [Labels] {a : DecArea} {s : TState} {m0 d d' : MachineData} {t out sl : BitVec 64}
  {count n N F : Nat} {slots : Slots} {lo o : Nat}

namespace Geo

variable (g : Geo a s m0 t out sl count n N F slots lo)
include g

theorem ctx : Ctx m0 t a N F :=
  ⟨g.ok.1, g.ok.2.1, g.ok.2.2.2.1, g.ok.2.2.1.footprint, by have := g.le; omega⟩

theorem outOk : OutOk m0 t a out 24 N := g.ok.2.2.2.2.2.2.1

theorem slOk : OutOk m0 t a sl (16 * n) N := g.ok.2.2.2.2.2.2.2.1

theorem cnt2 : 2 ≤ count := g.ok.2.2.2.2.1

theorem cnt5 : count ≤ 5 := g.ok.2.2.2.2.2.1

theorem sl_nw : sl.toNat + 16 * n ≤ 2 ^ 64 := g.slOk.2.1

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ F := fun p hp ↦ (g.sl p hp).2

theorem frame_nw : (stackBelow m0 F).toNat + (F + 8) ≤ 2 ^ 64 := g.ctx.noWrap_frame

/-- The bytes `o` to `o + w` of the frame do not wrap. -/
theorem noWrap_local {o w : Nat} (h : o + w ≤ F) : NativeRustcVm.NoWrap (off (stackBelow m0 F) o) w := by
  have := g.frame_nw
  unfold NativeRustcVm.NoWrap
  rw [toNat_off (by omega)]
  omega

theorem not_rc {q : BitVec 64} (hq : LChg m0 N t sl n q) : ¬ NativeRustcVm.InRange rcAddr 192 q := by
  rcases hq with hq | hq | hq
  · exact g.ctx.not_rc_stack hq
  · exact g.ctx.not_rc_tstate hq
  · exact g.ctx.out_not_rc g.slOk hq

theorem high_frame {q : BitVec 64} (hq : High m0 F lo q) :
    NativeRustcVm.InRange (stackBelow m0 F) (F + 8) q := by
  obtain ⟨j, -, hj, rfl⟩ := hq
  have := g.frame_nw
  exact inRange_off_self hj (by omega)

theorem not_high_of_apart {x : BitVec 64} {l : Nat}
    (hx : NativeRustcVm.Apart x l (stackBelow m0 N) (N + 8)) (hnw : NativeRustcVm.NoWrap x l)
    {q : BitVec 64} (hq : NativeRustcVm.InRange x l q) : ¬ High m0 F lo q := fun h ↦
  not_inRange_of_apart (apart_frame hx g.ctx.spN g.ctx.le) hnw g.ctx.noWrap_frame hq
    (g.high_frame h)

/-- Bytes of the frame below `lo` are not among the pushed registers. -/
theorem local_not_high {o w : Nat} (hw : o + w ≤ lo) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (off (stackBelow m0 F) o) w q) : ¬ High m0 F lo q := by
  rintro ⟨j, hj1, hj2, rfl⟩
  have := g.frame_nw
  have := g.lo_le
  rw [inRange_off_iff (by omega) (by omega)] at hq
  omega

/-- Bytes of the frame are in the stack. -/
theorem local_in {o w : Nat} (how : o + w ≤ F) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (off (stackBelow m0 F) o) w q) :
    NativeRustcVm.InRange (stackBelow m0 N) N q :=
  g.ctx.inRange_frame (inRange_of_off (g.ctx.noWrap_frame.mono (by omega)) how hq)

/-- Two parts of the frame, one before the other. -/
theorem local_disjoint {o1 w1 o2 w2 : Nat} (h : o1 + w1 ≤ o2 ∨ o2 + w2 ≤ o1) (h1 : o1 + w1 ≤ F)
    (h2 : o2 + w2 ≤ F) {q : BitVec 64}
    (hq1 : NativeRustcVm.InRange (off (stackBelow m0 F) o1) w1 q) :
    ¬ NativeRustcVm.InRange (off (stackBelow m0 F) o2) w2 q := fun hq2 ↦ by
  rw [inRange_iff' (g.noWrap_local h1), toNat_off (by have := g.frame_nw; omega)] at hq1
  rw [inRange_iff' (g.noWrap_local h2), toNat_off (by have := g.frame_nw; omega)] at hq2
  omega

theorem t_not_high {q : BitVec 64} (hq : NativeRustcVm.InRange t tstateBytes q) :
    ¬ High m0 F lo q :=
  g.not_high_of_apart g.ctx.tok.1 g.ctx.fp.1.2 hq

theorem sl_not_high {q : BitVec 64} (hq : NativeRustcVm.InRange sl (16 * n) q) :
    ¬ High m0 F lo q :=
  g.not_high_of_apart g.slOk.2.2.2.2.1 g.slOk.2.1 hq

theorem not_local_of_apart {x : BitVec 64} {l : Nat}
    (hx : NativeRustcVm.Apart x l (stackBelow m0 N) (N + 8)) (hnw : NativeRustcVm.NoWrap x l)
    {o w : Nat} (how : o + w ≤ F + 8) {q : BitVec 64} (hq : NativeRustcVm.InRange x l q) :
    ¬ NativeRustcVm.InRange (off (stackBelow m0 F) o) w q := fun h ↦
  not_inRange_of_apart (apart_frame hx g.ctx.spN g.ctx.le) hnw g.ctx.noWrap_frame hq
    (inRange_of_off g.ctx.noWrap_frame how h)

theorem t_not_local {o w : Nat} (how : o + w ≤ F + 8) {q : BitVec 64}
    (hq : NativeRustcVm.InRange t tstateBytes q) :
    ¬ NativeRustcVm.InRange (off (stackBelow m0 F) o) w q :=
  g.not_local_of_apart g.ctx.tok.1 g.ctx.fp.1.2 how hq

theorem sl_not_local {o w : Nat} (how : o + w ≤ F + 8) {q : BitVec 64}
    (hq : NativeRustcVm.InRange sl (16 * n) q) :
    ¬ NativeRustcVm.InRange (off (stackBelow m0 F) o) w q :=
  g.not_local_of_apart g.slOk.2.2.2.2.1 g.slOk.2.1 how hq

theorem not_sl_stack {q : BitVec 64} (hq : NativeRustcVm.InRange (stackBelow m0 N) N q) :
    ¬ NativeRustcVm.InRange sl (16 * n) q :=
  not_inRange_of_apart (Apart.symm' g.slOk.2.2.2.2.1) g.ctx.noWrap_stack g.slOk.2.1
    (inRange_mono hq (by omega))

theorem not_sl_t {q : BitVec 64} (hq : NativeRustcVm.InRange t tstateBytes q) :
    ¬ NativeRustcVm.InRange sl (16 * n) q :=
  not_inRange_of_apart (Apart.symm' g.slOk.2.2.1) g.ctx.fp.1.2 g.slOk.2.1 hq

/-- The round constants' bytes under the loop's frame. -/
theorem rc (hf : SF m0 t sl n N F slots o d) :
    ∀ i < 192, d.dmem.get? (rcAddr + BitVec.ofNat 64 i) = m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) :=
  rc_keep hf.same fun _ hq ↦ g.not_rc hq

theorem at_ (hf : SF m0 t sl n N F slots 0 d) : At m0 F d := At.of_frame hf.frame (g.rc hf)

/-- A callee's stack is in the stack, apart from the pushed registers. -/
theorem callee_in (hat : At m0 F d) {Nc : Nat} (hle : F + Nc ≤ N) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow d Nc) Nc q) :
    NativeRustcVm.InRange (stackBelow m0 N) N q ∧ ¬ High m0 F lo q := by
  obtain ⟨h1, h2⟩ := g.ctx.inRange_callee hat hle hq
  exact ⟨h1, fun h ↦ h2 (g.high_frame h)⟩

/-- A callee's stack misses the frame's bytes from `8`. -/
theorem callee_not_local (hat : At m0 F d) {Nc : Nat} (hle : F + Nc ≤ N) {o w : Nat} (ho : 8 ≤ o)
    (how : o + w ≤ F) {q : BitVec 64} (hq : NativeRustcVm.InRange (stackBelow d Nc) Nc q) :
    ¬ NativeRustcVm.InRange (off (stackBelow m0 F) o) w q := fun h ↦
  not_inRange_of_apart (g.ctx.apart_frame_callee hat hle ho how) (g.noWrap_local (by omega))
    (noWrap_stackBelow (g.ctx.stackOk hat hle)) h (inRange_mono hq (by omega))

/-- **A block** keeps the loop's frame. -/
theorem block {o o' : Nat} (hf : SF m0 t sl n N F slots o d) {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (frameEnv m0 d F rest vars ret).WF) (hm : Match (frameEnv m0 d F rest vars ret) S d')
    (hmid : MidOk F o' slots S = true) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem R) (hR : ∀ q, R q → LChg m0 N t sl n q) :
    SF m0 t sl n N F slots o' d' :=
  ⟨Frame.of_block hf.frame hwf hm hmid g.slots_le,
    NativeRustcVm.SameOutside.mono (hf.same.trans hs) fun q hq ↦ hq.elim id (hR q)⟩

/-- **A call** keeps the loop's frame where its changes miss the pushed registers. -/
theorem call (hf : SF m0 t sl n N F slots 0 d) {Nc : Nat} (hle : F + Nc ≤ N) (hsv : Saved d d')
    (hrsp : rspOf d' = rspOf d + 8#64) {R : BitVec 64 → Prop}
    (hR : ∀ q, R q → LChg m0 N t sl n q ∧ ¬ High m0 F lo q)
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow d Nc) Nc q)) :
    SF m0 t sl n N F slots 8 d' := by
  have hat := g.at_ hf
  have hall : ∀ q, (R q ∨ NativeRustcVm.InRange (stackBelow d Nc) Nc q) →
      LChg m0 N t sl n q ∧ ¬ High m0 F lo q := fun q hq ↦
    hq.elim (hR q) fun h ↦ ⟨Or.inl (g.callee_in hat hle h).1, (g.callee_in hat hle h).2⟩
  have := g.lo_le
  refine ⟨Frame.call_slots hf.frame hsv hrsp hso
      (fun p hp i hi hq ↦ (hall _ hq).2 ⟨p.1 + i, by have := g.sl p hp; omega,
        by have := g.sl p hp; omega, rfl⟩)
      (fun j hj hq ↦ (hall _ hq).2 ⟨F + j, by omega, by omega, rfl⟩),
    NativeRustcVm.SameOutside.mono (hf.same.trans hso) fun q hq ↦ hq.elim id fun h ↦ (hall q h).1⟩

/-- **Bytes of the frame from `8` kept by a call** whose own changes miss them. -/
theorem keep_call (hat : At m0 F d) {Nc : Nat} (hle : F + Nc ≤ N) {R : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow d Nc) Nc q))
    {o : Nat} {bs : List UInt8} (ho : 8 ≤ o) (hon : o + bs.length ≤ F)
    (hR : ∀ q, R q → ¬ NativeRustcVm.InRange (off (stackBelow m0 F) o) bs.length q)
    (hb : NativeRustcVm.BytesAt d.dmem (off (stackBelow m0 F) o) bs) :
    NativeRustcVm.BytesAt d'.dmem (off (stackBelow m0 F) o) bs := by
  have hnw := g.noWrap_local (o := o) (w := bs.length) (by omega)
  unfold NativeRustcVm.NoWrap at hnw
  refine NativeRustcVm.BytesAt.of_sameOutside hb hso fun i hi hq ↦ ?_
  have hin : NativeRustcVm.InRange (off (stackBelow m0 F) o) bs.length
      (off (off (stackBelow m0 F) o) i) := inRange_off_self hi (by omega)
  rcases hq with hq | hq
  · exact hR _ hq hin
  · exact g.callee_not_local hat hle ho hon hq hin

/-- **Slots kept** where the memory changed apart from them. -/
theorem sl_keep {d d' : Mem 64} {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → ¬ NativeRustcVm.InRange sl (16 * n) q) {xs : List EW} (hlen : xs.length ≤ n)
    (h : NativeRustcVm.EWsAt d sl xs) : NativeRustcVm.EWsAt d' sl xs := by
  have hnw := g.sl_nw
  refine NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi hRq ↦ hR _ hRq ?_
  rw [NativeRustcVm.length_ewsBytes] at hi
  exact inRange_off_self (b := sl) (by omega) (by omega)

/-- **The `TState` kept** where the memory changed in the stack and the slots only. -/
theorem t_keep {d d' : Mem 64} {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' R)
    (hk : Kept d d')
    (hR : ∀ q, R q → NativeRustcVm.InRange (stackBelow m0 N) N q ∨
      NativeRustcVm.InRange sl (16 * n) q)
    {s' : TState} (h : TStateAt d t a s') : TStateAt d' t a s' :=
  h.frame hk (fun q hq ↦ (hR q hq).elim g.ctx.stack_not_t (g.ctx.out_not_t g.slOk)) hs

/-- **The rounds kept** where the memory changed in the stack only. -/
theorem rounds_keep {d d' : Mem 64} {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' R)
    (hk : Kept d d') (hR : ∀ q, R q → NativeRustcVm.InRange (stackBelow m0 N) N q)
    {claim : EW} {E : Nat → Option EW} {s' : TState} {i : Nat} {c : EW} (hi : i ≤ n)
    (h : Rounds d t a sl claim count E s' i c) : Rounds d' t a sl claim count E s' i c := by
  obtain ⟨xs, si, hrun, hsz, hxs, hts⟩ := h
  exact ⟨xs, si, hrun, hsz, g.sl_keep hs (fun q hq ↦ g.not_sl_stack (hR q hq))
    (by simp [hsz]; omega) hxs, g.t_keep hs hk (fun q hq ↦ Or.inl (hR q hq)) hts⟩

/-! ## The calls of a round -/


/-- The loop's changes preserve the caller's loader slots. -/
theorem gotAt (hf : SF m0 t sl n N F slots 0 d) {Nc : Nat} (hle : F + Nc ≤ N)
    {areas : List (BitVec 64 × Nat)}
    (ha : ∀ l ∈ (["memcpy"] : List Label), ∀ x ∈ areas, Apart (gotAddr l) 8 x.1 x.2) :
    GotAt d Nc areas ["memcpy"] := by
  refine g.ctx.gotAt (g.at_ hf) hle g.ok.2.2.2.2.2.2.2.2.2 hf.same ?_ ha
  intro q hq
  rcases hq with hq | hq | hq
  · exact Or.inl hq
  · exact Or.inr ⟨(t, tstateBytes), by simp, g.ctx.fp.1.2, hq⟩
  · exact Or.inr ⟨(sl, 16 * n), by simp, g.slOk.2.1, hq⟩

theorem got_area {l : Label} (hl : l ∈ (["memcpy"] : List Label)) {x : BitVec 64 × Nat}
    (hx : x ∈ [(t, tstateBytes), (a.words, 8 * a.len), (out, 24), (sl, 16 * n),
      (rcAddr, 192)]) : Apart (gotAddr l) 8 x.1 x.2 :=
  (g.ok.2.2.2.2.2.2.2.2.2.1 l hl).2.2.2 x hx

theorem got_frame {l : Label} (hl : l ∈ (["memcpy"] : List Label))
    {o w : Nat} (how : o + w ≤ F) : Apart (gotAddr l) 8 (off (stackBelow m0 F) o) w :=
  g.ctx.apart_of_stack (g.ok.2.2.2.2.2.2.2.2.2.1 l hl).2.2.1 how

/-- `sumcheck_round_poly`'s precondition from the frame: `eq` at `Eo`, the message at `Mo`. -/
theorem roundPolyPre (hf : SF m0 t sl n N F slots 0 d) {si : TState} {e : Option EW}
    {Mo Eo : Nat} (hE : 8 ≤ Eo) (hE' : Eo + 24 ≤ F) (hM : 8 ≤ Mo) (hM' : Mo + 80 ≤ F)
    (hts : TStateAt d.dmem t a si) (he : OptEWAt d.dmem (off (stackBelow m0 F) Eo) e)
    (hrdi : reg d .rdi = t) (hrsi : (reg d .rsi).toNat = count)
    (hr8 : reg d .r8 = off (stackBelow m0 F) Eo) (hr9 : reg d .r9 = off (stackBelow m0 F) Mo) :
    RoundPolyPre a si e d := by
  have c := g.ctx
  have hat := g.at_ hf
  have hle : F + roundPolyStack ≤ N := by have := g.le; have := rp_le; omega
  unfold RoundPolyPre
  rw [hrdi, hrsi, hr8, hr9]
  refine ⟨c.stackOk hat hle, c.rcAt hat hle, hts, c.tstateOk hat hle, g.cnt2, g.cnt5, he,
    g.noWrap_local (by omega), c.apart_frame_callee hat hle hE hE',
    c.outOk_frame hat hle hM (by unfold maxCount; omega), ?_⟩
  apply g.gotAt hf hle
  intro l hl x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact g.got_area hl (by simp)
  · exact g.got_area hl (by simp)
  · exact g.got_frame hl hE'
  · exact g.got_frame hl hM'
  · exact g.got_area hl (by simp)

/-- **After `sumcheck_round_poly`**: the frame, the message and the next state on `some`, the
slots and the frame's bytes apart from the message kept. -/
theorem afterRoundPoly (hf : SF m0 t sl n N F slots 0 d) {si : TState} {e : Option EW}
    {Mo : Nat} (hlo : Mo + 80 ≤ lo) (hpost : RoundPolyPost a si e d d')
    (hrsp : rspOf d' = rspOf d + 8#64) (hrdi : reg d .rdi = t)
    (hr9 : reg d .r9 = off (stackBelow m0 F) Mo) :
    SF m0 t sl n N F slots 8 d' ∧
      (∀ msg s1, (sumcheckRoundPoly (reg d .rsi).toNat
          ⟨.ofBitVec (reg d .rdx), .ofBitVec (reg d .rcx)⟩ e).run si = some (msg, s1) →
        NativeRustcVm.EWsAt d'.dmem (off (stackBelow m0 F) Mo) msg.toList ∧
          TStateAt d'.dmem t a s1) ∧
      (∀ xs : List EW, xs.length ≤ n → NativeRustcVm.EWsAt d.dmem sl xs →
        NativeRustcVm.EWsAt d'.dmem sl xs) ∧
      (∀ (o : Nat) (bs : List UInt8), 8 ≤ o → o + bs.length ≤ F →
        (o + bs.length ≤ Mo ∨ Mo + 80 ≤ o) →
        NativeRustcVm.BytesAt d.dmem (off (stackBelow m0 F) o) bs →
        NativeRustcVm.BytesAt d'.dmem (off (stackBelow m0 F) o) bs) := by
  obtain ⟨-, hmsg, hnext, hs, hsv⟩ := hpost
  have c := g.ctx
  have hat := g.at_ hf
  have hle : F + roundPolyStack ≤ N := by have := g.le; have := rp_le; omega
  have := g.lo_le
  rw [hrdi, hr9] at hs
  rw [hr9] at hmsg
  rw [hrdi] at hnext
  have h80 : 16 * maxCount = 80 := rfl
  rw [h80] at hs
  have hs' : NativeRustcVm.SameOutside d.dmem d'.dmem (fun q ↦
      (NativeRustcVm.InRange (off (stackBelow m0 F) Mo) 80 q ∨
        NativeRustcVm.InRange t tstateBytes q) ∨
      NativeRustcVm.InRange (stackBelow d roundPolyStack) roundPolyStack q) :=
    fun q hq ↦ hs q fun h ↦ hq (or_assoc.mpr h)
  refine ⟨g.call hf hle hsv hrsp (fun q hq ↦ ?_) hs', fun msg s1 hr ↦ ⟨hmsg msg s1 hr,
    hnext msg s1 hr⟩, fun xs hlen hxs ↦ g.sl_keep hs' (fun q hq ↦ ?_) hlen hxs,
    fun o bs ho hon hdis hb ↦ g.keep_call hat hle hs' ho hon (fun q hq ↦ ?_) hb⟩
  · rcases hq with hq | hq
    · exact ⟨Or.inl (g.local_in (by omega) hq), g.local_not_high hlo hq⟩
    · exact ⟨Or.inr (Or.inl hq), g.t_not_high hq⟩
  · rcases hq with (hq | hq) | hq
    · exact g.not_sl_stack (g.local_in (by omega) hq)
    · exact g.not_sl_t hq
    · exact g.not_sl_stack (g.callee_in hat hle hq).1
  · rcases hq with hq | hq
    · exact g.local_disjoint (by omega) (by omega) (by omega) hq
    · exact g.t_not_local (by omega) hq

/-- `squeeze`'s precondition from the frame. -/
theorem squeezePre (hf : SF m0 t sl n N F slots 0 d) {si : TState}
    (hts : TStateAt d.dmem t a si) (hrdi : reg d .rdi = t) : SqueezePre si.sponge d := by
  have c := g.ctx
  have hat := g.at_ hf
  have hle : F + squeezeStack ≤ N := by have := g.le; have := sq_le; omega
  have htok := c.tstateOk hat hle
  have hfp := hts.footprint
  unfold SqueezePre
  rw [hrdi]
  have h1 : t.toNat + 760 ≤ (stackBelow d squeezeStack).toNat ∨
      (stackBelow d squeezeStack).toNat + (squeezeStack + 8) ≤ t.toNat := htok.1
  have h2 : t.toNat + 760 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ t.toNat := htok.2.2
  have hnw : t.toNat + 760 ≤ 2 ^ 64 := hfp.1.2
  refine ⟨c.stackOk hat hle, c.rcAt hat hle,
    ⟨fun j hj ↦ hfp.1.1 j (by simp only [spongeBytes] at hj; show j < 760; omega), ?_, ?_, ?_⟩,
    hts.sponge, ?_⟩
  · show t.toNat + 328 ≤ 2 ^ 64; omega
  · show t.toNat + 328 ≤ _ ∨ _ ≤ t.toNat; omega
  · show t.toNat + 328 ≤ _ ∨ _ ≤ t.toNat; omega
  · apply g.gotAt hf hle
    intro l hl x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · have ha := g.got_area hl (x := (t, tstateBytes)) (by simp)
      change (gotAddr l).toNat + 8 ≤ t.toNat ∨
        t.toNat + 328 ≤ (gotAddr l).toNat
      change (gotAddr l).toNat + 8 ≤ t.toNat ∨
        t.toNat + 760 ≤ (gotAddr l).toNat at ha
      omega
    · exact g.got_area hl (by simp)

/-- **After `squeeze`**: the frame and its bytes from `8`, the challenge in RAX, RDX, the
`TState` with the sponge squeezed, the slots kept. -/
theorem afterSqueeze (hf : SF m0 t sl n N F slots 0 d) {si : TState}
    (hts : TStateAt d.dmem t a si) (hpost : SqueezePost si.sponge d d')
    (hrsp : rspOf d' = rspOf d + 8#64) (hrdi : reg d .rdi = t) :
    SF m0 t sl n N F slots 8 d' ∧
      reg d' .rax = si.sponge.squeeze.1.c0.toBitVec ∧ reg d' .rdx = si.sponge.squeeze.1.c1.toBitVec ∧
      TStateAt d'.dmem t a { si with sponge := si.sponge.squeeze.2 } ∧
      (∀ xs : List EW, xs.length ≤ n → NativeRustcVm.EWsAt d.dmem sl xs →
        NativeRustcVm.EWsAt d'.dmem sl xs) ∧
      (∀ (o : Nat) (bs : List UInt8), 8 ≤ o → o + bs.length ≤ F →
        NativeRustcVm.BytesAt d.dmem (off (stackBelow m0 F) o) bs →
        NativeRustcVm.BytesAt d'.dmem (off (stackBelow m0 F) o) bs) := by
  obtain ⟨h0, h1, hsp, hs, hsv⟩ := hpost
  have c := g.ctx
  have hat := g.at_ hf
  have hle : F + squeezeStack ≤ N := by have := g.le; have := sq_le; omega
  have hnwt : NativeRustcVm.NoWrap t tstateBytes := hts.footprint.1.2
  rw [hrdi] at hsp hs
  have hR : ∀ q, NativeRustcVm.InRange t spongeBytes q → NativeRustcVm.InRange t tstateBytes q :=
    fun q hq ↦ inRange_mono hq (by decide)
  have hs' : NativeRustcVm.SameOutside d.dmem d'.dmem (fun q ↦
      NativeRustcVm.InRange t tstateBytes q ∨
        NativeRustcVm.InRange (stackBelow d squeezeStack) squeezeStack q) :=
    NativeRustcVm.SameOutside.mono hs fun q hq ↦ hq.elim (fun h ↦ Or.inl (hR q h)) Or.inr
  refine ⟨g.call hf hle hsv hrsp (fun q hq ↦ ⟨Or.inr (Or.inl hq), g.t_not_high hq⟩) hs', h0, h1,
    ?_, fun xs hlen hxs ↦ g.sl_keep hs' (fun q hq ↦ hq.elim g.not_sl_t
      fun h ↦ g.not_sl_stack (g.callee_in hat hle h).1) hlen hxs,
    fun o bs ho hon hb ↦ g.keep_call hat hle hs' ho hon (fun q hq ↦ g.t_not_local (by omega) hq) hb⟩
  refine hts.with_sponge hsv.2 (R := NativeRustcVm.InRange (stackBelow d squeezeStack) squeezeStack)
    (fun q hq ↦ c.stack_not_t (g.callee_in hat hle hq).1) (fun q hq ↦ hs q ?_) hsp
  rintro (h | h)
  · obtain ⟨j, hj, hw, hq'⟩ := touch_of_inRange (o := 0) (n := spongeBytes) hnwt (by decide)
      (by rwa [off_zero])
    exact hq (Or.inl ⟨j, hj, hw.2, hq'⟩)
  · exact hq (Or.inr h)

/-- `poly_eval`'s precondition from the frame: the message at `Mo`. -/
theorem polyEvalPre (hf : SF m0 t sl n N F slots 0 d) {Mo : Nat} (hM : 8 ≤ Mo) (hM' : Mo + 80 ≤ F)
    (hrdi : reg d .rdi = off (stackBelow m0 F) Mo) (hrsi : (reg d .rsi).toNat = count) :
    PolyEvalPre d := by
  have c := g.ctx
  have hat := g.at_ hf
  have hle : F + polyEvalStack ≤ N := by have := g.le; have := pe_le; omega
  have h5 := g.cnt5
  have ho := c.outOk_frame hat hle hM (n := 16 * count) (by omega)
  unfold PolyEvalPre SliceOk Readable OffStack
  rw [hrdi, hrsi]
  exact ⟨c.stackOk hat hle, by have := g.cnt2; omega, ⟨ho.1, ho.2.1⟩, ho.2.2.2.2.1⟩

/-- **After `poly_eval`**: the frame, its bytes from `8`, the slots and the `TState` kept. -/
theorem afterPolyEval (hf : SF m0 t sl n N F slots 0 d) (hpost : PolyEvalPost d d')
    (hrsp : rspOf d' = rspOf d + 8#64) :
    SF m0 t sl n N F slots 8 d' ∧
      (∀ xs : List EW, xs.length ≤ n → NativeRustcVm.EWsAt d.dmem sl xs →
        NativeRustcVm.EWsAt d'.dmem sl xs) ∧
      (∀ s' : TState, TStateAt d.dmem t a s' → TStateAt d'.dmem t a s') ∧
      (∀ (o : Nat) (bs : List UInt8), 8 ≤ o → o + bs.length ≤ F →
        NativeRustcVm.BytesAt d.dmem (off (stackBelow m0 F) o) bs →
        NativeRustcVm.BytesAt d'.dmem (off (stackBelow m0 F) o) bs) := by
  obtain ⟨-, hs, hsv⟩ := hpost
  have hat := g.at_ hf
  have hle : F + polyEvalStack ≤ N := by have := g.le; have := pe_le; omega
  have h00 : ∀ q, ¬ NativeRustcVm.InRange 0 0 q := fun q hq ↦ by
    unfold NativeRustcVm.InRange at hq; omega
  have hs' : NativeRustcVm.SameOutside d.dmem d'.dmem (fun q ↦ False ∨
      NativeRustcVm.InRange (stackBelow d polyEvalStack) polyEvalStack q) :=
    NativeRustcVm.SameOutside.mono hs fun q hq ↦ hq.elim (fun h ↦ (h00 q h).elim) Or.inr
  refine ⟨g.call hf hle hsv hrsp (fun _ h ↦ h.elim) hs',
    fun xs hlen hxs ↦ g.sl_keep hs' (fun q hq ↦ hq.elim False.elim
      fun h ↦ g.not_sl_stack (g.callee_in hat hle h).1) hlen hxs,
    fun s' hts ↦ g.t_keep hs' hsv.2 (fun q hq ↦ hq.elim False.elim
      fun h ↦ Or.inl (g.callee_in hat hle h).1) hts,
    fun o bs ho hon hb ↦ g.keep_call hat hle hs' ho hon (fun _ h ↦ h.elim) hb⟩

/-! ## The slots -/

/-- Slot `i`'s address as a number. -/
theorem slot_toNat {i : Nat} (hi : i < n) : (off sl (16 * i)).toNat = sl.toNat + 16 * i := by
  have hnw := g.sl_nw
  exact toNat_off (by omega)

/-- Slot `i`: mapped, not wrapping, apart from the frame. -/
theorem slot_ok {i : Nat} (hi : i < n) (hk : Kept m0.dmem d.dmem) :
    (NativeRustcVm.Mapped d.dmem (off sl (16 * i)) 16 ∧ NativeRustcVm.NoWrap (off sl (16 * i)) 16) ∧
      NativeRustcVm.Apart (stackBelow m0 F) (F + 8) (off sl (16 * i)) 16 := by
  have ho := g.slOk
  have hA := apart_frame ho.2.2.2.2.1 g.ctx.spN g.ctx.le
  have hnw := g.sl_nw
  unfold NativeRustcVm.Apart at hA
  refine ⟨⟨Mapped.keeps (mapped_off ho.1 (by omega)) hk, ?_⟩, ?_⟩
  · unfold NativeRustcVm.NoWrap; rw [g.slot_toNat hi]; omega
  · unfold NativeRustcVm.Apart; rw [g.slot_toNat hi]; omega

/-- A byte of slot `i` is one of the slots'. -/
theorem slot_in {i : Nat} (hi : i < n) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (off sl (16 * i)) 16 q) : NativeRustcVm.InRange sl (16 * n) q :=
  inRange_of_off g.slOk.2.1 (by omega) hq

/-- **The first `i` slots kept** where only slot `i` and bytes apart from the slots changed. -/
theorem prefix_keep {d d' : Mem 64} {i : Nat} (hi : i < n) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → NativeRustcVm.InRange (off sl (16 * i)) 16 q ∨
      ¬ NativeRustcVm.InRange sl (16 * n) q)
    {xs : List EW} (hlen : xs.length = i) (h : NativeRustcVm.EWsAt d sl xs) :
    NativeRustcVm.EWsAt d' sl xs := by
  have hnw := g.sl_nw
  refine NativeRustcVm.BytesAt.of_sameOutside h hs fun j hj hq ↦ ?_
  rw [NativeRustcVm.length_ewsBytes] at hj
  have hnw' : NativeRustcVm.NoWrap (off sl (16 * i)) 16 := by
    unfold NativeRustcVm.NoWrap; rw [g.slot_toNat hi]; omega
  rcases hR _ hq with hq | hq
  · rw [inRange_iff' hnw', g.slot_toNat hi, show sl + BitVec.ofNat 64 j = off sl j from rfl,
      toNat_off (by omega)] at hq
    omega
  · exact hq (inRange_off_self (b := sl) (by omega) (by omega))

/-- Slot `i + 1`'s address is the end's exactly at the last. -/
theorem slot_eq_end {i : Nat} (hi : i < n) :
    (off sl (16 * (i + 1)) == off sl (16 * n)) = (i + 1 == n) := by
  have hnw := g.sl_nw
  by_cases h : i + 1 = n
  · rw [h]; simp
  · have hne : off sl (16 * (i + 1)) ≠ off sl (16 * n) := fun he ↦ by
      have := congrArg BitVec.toNat he
      simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (a := 16 * (i + 1)) (by omega),
        Nat.mod_eq_of_lt (a := 16 * n) (by omega),
        Nat.mod_eq_of_lt (a := sl.toNat + 16 * (i + 1)) (by omega)] at this
      by_cases hlt : sl.toNat + 16 * n < 2 ^ 64
      · rw [Nat.mod_eq_of_lt hlt] at this; omega
      · rw [show sl.toNat + 16 * n = 2 ^ 64 by omega, Nat.mod_self] at this; omega
    simp [hne, h]

end Geo

end

end

end NativeRustcVmX64.Sumcheck
