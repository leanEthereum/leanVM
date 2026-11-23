module

public import NativeRustcVmX64.Sumcheck.RoundPoly.Exec
public import NativeRustcVmX64.Sumcheck.Ctx
public import NativeRustcVm.Sumcheck.RoundPoly
public import NativeRustcVm.Transcript.Update

/-!
# `sumcheck_round_poly`'s frame, its blocks and calls, its exit (x86-64)

`RF m0 o d`: the frame (`Frame`, RSP at offset `o`), memory changed only in the message, the
`TState` and the stack (`Chg`), RBX the message. A body block keeps it (`RF.block`), a call too
where the callee's changes miss the frame's pushed registers (`RF.call`). From it at `.L9`, `b19`
returns RBP's low byte in AL (`exit_spec`); at `.L8`, `b18` clears RBP first (`fail_spec`).
`post_none`, `post_some`: the postcondition from the exit.
-/

namespace NativeRustcVmX64.Sumcheck.RoundPoly

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateSumcheckRoundPoly
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Sumcheck

@[expose] public section

/-- The frame: 112 bytes below the entry's RSP. -/
abbrev fa (m0 : MachineData) : BitVec 64 := stackBelow m0 112

/-- The `TState` (RDI), the message (R9), the count (RSI), the claim (RDX, RCX) at the entry. -/
abbrev tAt (m0 : MachineData) : BitVec 64 := reg m0 .rdi
abbrev msgAt (m0 : MachineData) : BitVec 64 := reg m0 .r9
abbrev cnt (m0 : MachineData) : Nat := (reg m0 .rsi).toNat
abbrev claimOf (m0 : MachineData) : EW := ⟨.ofBitVec (reg m0 .rdx), .ofBitVec (reg m0 .rcx)⟩

/-- What `sumcheck_round_poly` may change: the message, the `TState`, its stack. -/
def Chg (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (msgAt m0) (16 * maxCount) q ∨ InRange (tAt m0) tstateBytes q ∨
    InRange (stackBelow m0 roundPolyStack) roundPolyStack q

/-- A byte not among the frame's pushed registers and return address (offsets `64` to `120`). -/
def NotHigh (m0 : MachineData) (q : BitVec 64) : Prop :=
  ∀ j, 64 ≤ j → j < 120 → q ≠ off (fa m0) j

/-- **The frame**, RSP at offset `o`. -/
structure RF [Labels] (m0 : MachineData) (o : Nat) (d : MachineData) : Prop where
  frame : Frame m0 112 slots o d
  same : NativeRustcVm.SameOutside m0.dmem d.dmem (Chg m0)
  rbx : reg d .rbx = msgAt m0

/-- A body block's environment: the frame, the message. -/
abbrev envB (m0 d : MachineData) (ret : BitVec 64) : Env :=
  frameEnv m0 d 112 [(msgAt m0, 80)] (fun _ ↦ 0) ret

/-- The model's run. -/
abbrev runR (m0 : MachineData) (s : TState) (e : Option EW) : Option (Array EW × TState) :=
  (sumcheckRoundPoly (cnt m0) (claimOf m0) e).run s

end

public section

theorem roundPolyStack_eq : roundPolyStack = 816 := by decide

theorem slots_range : ∀ p ∈ slots, 64 ≤ p.1 ∧ p.1 + 8 ≤ 112 := by decide

section

variable [Labels] {a : DecArea} {s : TState} {e : Option EW} {m0 : MachineData}

/-- The context of `sumcheck_round_poly`. -/
theorem ctx_of (h : RoundPolyPre a s e m0) : Ctx m0 (tAt m0) a roundPolyStack 112 :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.1.footprint, by rw [roundPolyStack_eq]; omega⟩

/-- The message as an output. -/
theorem msgOk (h : RoundPolyPre a s e m0) :
    OutOk m0 (tAt m0) a (msgAt m0) (16 * maxCount) roundPolyStack :=
  h.2.2.2.2.2.2.2.2.2.1

theorem msg_noWrap (h : RoundPolyPre a s e m0) : NativeRustcVm.NoWrap (msgAt m0) 80 :=
  (msgOk h).2.1

/-- The round constants are apart from the changes. -/
theorem not_rc (h : RoundPolyPre a s e m0) {q : BitVec 64} (hq : Chg m0 q) :
    ¬ NativeRustcVm.InRange rcAddr 192 q := by
  have c := ctx_of h
  rcases hq with hq | hq | hq
  · exact c.out_not_rc (msgOk h) hq
  · exact c.not_rc_tstate hq
  · exact c.not_rc_stack hq

/-- The message, the `TState` and its area are apart from the frame's region. -/
theorem not_frame_msg (h : RoundPolyPre a s e m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (msgAt m0) 80 q) :
    ¬ NativeRustcVm.InRange (fa m0) 120 q := by
  have c := ctx_of h
  exact not_inRange_of_apart (apart_frame (msgOk h).2.2.2.2.1 c.spN (by rw [roundPolyStack_eq]; omega))
    (msg_noWrap h) c.noWrap_frame hq

theorem not_frame_t (h : RoundPolyPre a s e m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (tAt m0) tstateBytes q) : ¬ NativeRustcVm.InRange (fa m0) 120 q := by
  have c := ctx_of h
  exact not_inRange_of_apart (apart_frame c.tok.1 c.spN (by rw [roundPolyStack_eq]; omega))
    c.fp.1.2 c.noWrap_frame hq

/-- Outside the frame's region: not its high bytes. -/
theorem notHigh_of_not_frame (h : RoundPolyPre a s e m0) {q : BitVec 64}
    (hq : ¬ NativeRustcVm.InRange (fa m0) 120 q) : NotHigh m0 q := by
  rintro j - hj rfl
  exact hq (inRange_off_self hj (by have := (ctx_of h).noWrap_frame; unfold NativeRustcVm.NoWrap at this; omega))

/-- `read_scalar`'s output in the frame (offsets `40` to `64`): not its high bytes. -/
theorem notHigh_out (h : RoundPolyPre a s e m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (off (fa m0) 40) 24 q) : NotHigh m0 q := by
  have c := ctx_of h
  have hnw := c.noWrap_frame
  unfold NativeRustcVm.NoWrap at hnw
  rintro j hj1 hj2 rfl
  rw [inRange_off_iff (by omega) (by omega)] at hq
  omega

/-- The callee's stack and the frame's high bytes. -/
theorem notHigh_callee (h : RoundPolyPre a s e m0) {d : MachineData} (hat : At m0 112 d) {Nc : Nat}
    (hle : 112 + Nc ≤ roundPolyStack) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow d Nc) Nc q) : Chg m0 q ∧ NotHigh m0 q := by
  have c := ctx_of h
  obtain ⟨h1, h2⟩ := c.inRange_callee hat hle hq
  exact ⟨Or.inr (Or.inr h1), notHigh_of_not_frame h h2⟩

/-- The frame below its return address is in the stack. -/
theorem chg_frame (h : RoundPolyPre a s e m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (fa m0) 112 q) : Chg m0 q :=
  Or.inr (Or.inr ((ctx_of h).inRange_frame hq))

/-- The round constants' bytes under `RF`. -/
theorem RF.rc (h : RoundPolyPre a s e m0) {o : Nat} {d : MachineData} (hf : RF m0 o d) :
    ∀ i < 192, d.dmem.get? (rcAddr + BitVec.ofNat 64 i) =
      m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) :=
  rc_keep hf.same fun _ hq ↦ not_rc h hq

/-- At a call. -/
theorem RF.at (h : RoundPolyPre a s e m0) {d : MachineData} (hf : RF m0 0 d) : At m0 112 d :=
  At.of_frame hf.frame (hf.rc h)

/-- Loader assumptions at any call, including outputs in the frame or message. -/
theorem RF.gotAt (h : RoundPolyPre a s e m0) {d : MachineData} (hf : RF m0 0 d)
    {Nc : Nat} (hle : 112 + Nc ≤ roundPolyStack) {areas : List (BitVec 64 × Nat)}
    (ha : ∀ l ∈ (["memcpy"] : List Label), ∀ x ∈ areas,
      Apart (gotAddr l) 8 x.1 x.2) : GotAt d Nc areas ["memcpy"] := by
  have c := ctx_of h
  have hg := h.2.2.2.2.2.2.2.2.2.2
  refine c.gotAt (hf.at h) hle hg hf.same ?_ ha
  intro q hq
  rcases hq with hq | hq | hq
  · exact Or.inr ⟨(msgAt m0, 80), by simp [maxCount], msg_noWrap h, hq⟩
  · exact Or.inr ⟨(tAt m0, tstateBytes), by simp, c.fp.1.2, hq⟩
  · exact Or.inl hq

/-- GOT slots are apart from each entry area. -/
theorem got_area (h : RoundPolyPre a s e m0) {l : Label} (hl : l ∈ (["memcpy"] : List Label))
    {x : BitVec 64 × Nat}
    (hx : x ∈ [(tAt m0, tstateBytes), (a.words, 8 * a.len), (reg m0 .r8, 24),
      (msgAt m0, 80), (rcAddr, 192)]) : Apart (gotAddr l) 8 x.1 x.2 :=
  (h.2.2.2.2.2.2.2.2.2.2.1 l hl).2.2.2 x hx

theorem got_frame (h : RoundPolyPre a s e m0) {l : Label}
    (hl : l ∈ (["memcpy"] : List Label)) {o n : Nat} (hon : o + n ≤ 112) :
    Apart (gotAddr l) 8 (off (fa m0) o) n :=
  (ctx_of h).apart_of_stack (h.2.2.2.2.2.2.2.2.2.2.1 l hl).2.2.1 hon

theorem got_msg (h : RoundPolyPre a s e m0) {l : Label}
    (hl : l ∈ (["memcpy"] : List Label)) {o n : Nat} (ho : o < 80) (hon : o + n ≤ 80) :
    Apart (gotAddr l) 8 (off (msgAt m0) o) n := by
  have ha := got_area h hl (x := (msgAt m0, 80)) (by simp)
  have hn := msg_noWrap h
  change (gotAddr l).toNat + 8 ≤ (msgAt m0).toNat ∨
    (msgAt m0).toNat + 80 ≤ (gotAddr l).toNat at ha
  unfold NativeRustcX64.Apart
  rw [toNat_off (by unfold NativeRustcVm.NoWrap at hn; omega)]
  omega

theorem wf_envB (h : RoundPolyPre a s e m0) {d : MachineData} (hk : Kept m0.dmem d.dmem)
    (ret : BitVec 64) : (envB m0 d ret).WF := by
  have c := ctx_of h
  refine frame_wf ⟨c.mapped_frame hk, c.noWrap_frame⟩ (fun x hx ↦ ?_)
    (List.pairwise_pair.mpr (Apart.symm' (apart_frame (msgOk h).2.2.2.2.1 c.spN
      (by rw [roundPolyStack_eq]; omega))))
  rw [List.mem_singleton] at hx
  subst hx
  exact ⟨Mapped.keeps (msgOk h).1 hk, msg_noWrap h⟩

omit [Labels] in
theorem eval_ptr1 [Labels] {d : MachineData} {ret : BitVec 64} (o : Nat) :
    (Sym.ptr 1 (o : Int)).eval (envB m0 d ret) = off (msgAt m0) o := by
  show (envB m0 d ret).base 1 + BitVec.ofInt 64 (o : Int) = _
  rw [BitVec.ofInt_natCast]
  rfl

theorem match_bodyS {d : MachineData} (hf : RF m0 8 d) (ret : BitVec 64) :
    Match (envB m0 d ret) bodyS d :=
  match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.frame.rsp_eval, known_ptr rfl hf.rbx, trivial⟩ trivial
    trivial trivial

/-- **A body block** keeps the frame; it writes only the frame below its pushed registers and the
message. -/
theorem RF.block (h : RoundPolyPre a s e m0) {d d' : MachineData} {ret : BitVec 64} {S : SState}
    (hf : RF m0 8 d) (hm : Match (envB m0 d ret) S d') {o : Nat}
    (hmid : MidOk 112 o slots S = true) (hrbx : S.reg .rbx = some (.ptr 1 0)) :
    RF m0 o d' ∧ NativeRustcVm.SameOutside d.dmem d'.dmem (fun q ↦
      NativeRustcVm.InRange (fa m0) 112 q ∨ NativeRustcVm.InRange (msgAt m0) 80 q) := by
  have c := ctx_of h
  have hwf := wf_envB h hf.frame.kept ret
  have hs : NativeRustcVm.SameOutside d.dmem d'.dmem (fun q ↦
      NativeRustcVm.InRange (fa m0) 112 q ∨ NativeRustcVm.InRange (msgAt m0) 80 q) :=
    fun q hq ↦ hm.get?_mem0 hwf fun hw ↦ hq (written_frame2 hm (writesIn_of_mid hmid)
      (belowRet_of_mid hmid) (msg_noWrap h) c.noWrap_frame hw)
  refine ⟨⟨Frame.of_block hf.frame hwf hm hmid (by decide), SameOutside.mono (hf.same.trans hs)
    fun q hq ↦ ?_, (hm.regs .rbx _ hrbx).trans (eval_ptr rfl)⟩, hs⟩
  rcases hq with hq | hq | hq
  · exact hq
  · exact chg_frame h hq
  · exact Or.inl hq

/-- **A call** keeps the frame where the callee's changes miss its high bytes. -/
theorem RF.call (h : RoundPolyPre a s e m0) {d d' : MachineData} (hf : RF m0 0 d) {Nc : Nat}
    (hle : 112 + Nc ≤ roundPolyStack) (hsv : Saved d d') (hrsp : rspOf d' = rspOf d + 8#64)
    {R : BitVec 64 → Prop} (hR : ∀ q, R q → Chg m0 q ∧ NotHigh m0 q)
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow d Nc) Nc q)) : RF m0 8 d' := by
  have hat := hf.at h
  have hall : ∀ q, (R q ∨ NativeRustcVm.InRange (stackBelow d Nc) Nc q) →
      Chg m0 q ∧ NotHigh m0 q :=
    fun q hq ↦ hq.elim (hR q) (notHigh_callee h hat hle)
  refine ⟨Frame.call_slots hf.frame hsv hrsp hso (fun p hp i hi hq ↦ ?_)
      (fun j hj hq ↦ (hall _ hq).2 (112 + j) (by omega) (by omega) rfl),
    SameOutside.mono (hf.same.trans hso) fun q hq ↦ hq.elim id fun hq ↦ (hall q hq).1,
    (hsv.1 .rbx rfl).trans hf.rbx⟩
  have hp' := slots_range p hp
  exact (hall _ hq).2 (p.1 + i) (by omega) (by omega) rfl

/-- **The `TState` kept** where the memory changed only in the message and the stack. -/
theorem tstate_keep (h : RoundPolyPre a s e m0) {d d' : Mem 64} {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R) (hk : Kept d d')
    (hR : ∀ q, R q → NativeRustcVm.InRange (msgAt m0) 80 q ∨
      NativeRustcVm.InRange (stackBelow m0 roundPolyStack) roundPolyStack q)
    {s' : TState} (ht : TStateAt d (tAt m0) a s') : TStateAt d' (tAt m0) a s' := by
  have c := ctx_of h
  refine ht.frame hk (fun q hq ↦ ?_) hs
  rcases hR q hq with hq | hq
  · exact c.out_not_t (msgOk h) hq
  · exact c.stack_not_t hq

/-- **Elements of the message kept** where the memory changed apart from them. -/
theorem msg_keep (h : RoundPolyPre a s e m0) {d d' : Mem 64} {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R) {o : Nat} {xs : List EW}
    (hle : o + 16 * xs.length ≤ 80)
    (hR : ∀ q, R q → ¬ NativeRustcVm.InRange (off (msgAt m0) o) (16 * xs.length) q)
    (hx : NativeRustcVm.EWsAt d (off (msgAt m0) o) xs) :
    NativeRustcVm.EWsAt d' (off (msgAt m0) o) xs := by
  have hnw := msg_noWrap h
  unfold NativeRustcVm.NoWrap at hnw
  refine NativeRustcVm.BytesAt.of_sameOutside hx hs fun i hi hR' ↦ hR _ hR' ?_
  rw [NativeRustcVm.length_ewsBytes] at hi
  exact inRange_off_self hi (by omega)

/-- A part of the message: its bytes in the message. -/
theorem msg_part (h : RoundPolyPre a s e m0) {o n : Nat} (ho : o < 80) (hon : o + n ≤ 80)
    {q : BitVec 64}
    (hq : NativeRustcVm.InRange (off (msgAt m0) o) n q) : NativeRustcVm.InRange (msgAt m0) 80 q := by
  have hnw := msg_noWrap h
  unfold NativeRustcVm.NoWrap at hnw
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega)]; omega),
    toNat_off (by omega)] at hq
  rw [inRange_iff' hnw]
  omega

/-- **A part of the message as a callee's output.** -/
theorem msgOut (h : RoundPolyPre a s e m0) {d : MachineData} (hat : At m0 112 d) {Nc : Nat}
    (hle : 112 + Nc ≤ roundPolyStack) {o n : Nat} (ho' : o < 80) (hon : o + n ≤ 80) :
    OutOk d (tAt m0) a (off (msgAt m0) o) n Nc := by
  have c := ctx_of h
  have ho := c.outOk hat hle (msgOk h)
  have hnw := msg_noWrap h
  unfold NativeRustcVm.NoWrap at hnw
  have ht : (off (msgAt m0) o).toNat = (msgAt m0).toNat + o := toNat_off (by omega)
  have m1 : ∀ {x : BitVec 64} {nx : Nat}, NativeRustcVm.Apart (msgAt m0) (16 * maxCount) x nx →
      NativeRustcVm.Apart (off (msgAt m0) o) n x nx := fun hx ↦ by
    unfold NativeRustcVm.Apart at hx ⊢
    rw [ht]
    have : maxCount = 5 := rfl
    omega
  refine ⟨mapped_off ho.1 (by have : maxCount = 5 := rfl; omega), ?_, m1 ho.2.2.1, m1 ho.2.2.2.1,
    m1 ho.2.2.2.2.1, m1 ho.2.2.2.2.2⟩
  unfold NativeRustcX64.NoWrap
  rw [ht]
  omega


/-- **Frame bytes from `o ≥ 8` kept by a call** whose changes miss the frame's region. -/
theorem keep_call (h : RoundPolyPre a s e m0) {d d' : MachineData} (hat : At m0 112 d) {Nc : Nat}
    (hle : 112 + Nc ≤ roundPolyStack) {R : BitVec 64 → Prop}
    (hR : ∀ q, R q → ¬ NativeRustcVm.InRange (fa m0) 120 q)
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow d Nc) Nc q))
    {o : Nat} {bs : List UInt8} (ho : 8 ≤ o) (hon : o + bs.length ≤ 112)
    (hb : NativeRustcVm.BytesAt d.dmem (off (fa m0) o) bs) :
    NativeRustcVm.BytesAt d'.dmem (off (fa m0) o) bs := by
  have c := ctx_of h
  have hfnw := c.noWrap_frame
  unfold NativeRustcVm.NoWrap at hfnw
  refine NativeRustcVm.BytesAt.of_sameOutside hb hso fun i hi hq ↦ ?_
  rw [off_add] at hq
  rcases hq with hq | hq
  · exact hR _ hq (inRange_off_self (by omega) (by omega))
  · have hA := c.apart_frame_callee hat hle (o := o) (n := bs.length) ho hon
    have hin : NativeRustcVm.InRange (off (fa m0) o) bs.length (off (fa m0) (o + i)) := by
      rw [← off_add]; exact inRange_off_self hi (by omega)
    exact not_inRange_of_apart hA (by unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega)]; omega)
      (noWrap_stackBelow (c.stackOk hat hle)) hin (inRange_mono hq (by omega))

/-- A word of the frame kept by a call. -/
theorem keepW_call (h : RoundPolyPre a s e m0) {d d' : MachineData} (hat : At m0 112 d) {Nc : Nat}
    (hle : 112 + Nc ≤ roundPolyStack) {R : BitVec 64 → Prop}
    (hR : ∀ q, R q → ¬ NativeRustcVm.InRange (fa m0) 120 q)
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow d Nc) Nc q))
    {o : Nat} {w : UInt64} (ho : 8 ≤ o) (hon : o + 8 ≤ 112)
    (hb : NativeRustcVm.WordAt d.dmem (off (fa m0) o) w) :
    NativeRustcVm.WordAt d'.dmem (off (fa m0) o) w :=
  keep_call h hat hle hR hso (bs := NativeRustcVm.wordBytes w) ho hon hb

/-- **The `TState` and a tail of the message from `o0` kept** where the memory changed only in
the message before `o0` and the stack. -/
theorem keep_ts_tail (h : RoundPolyPre a s e m0) {d d' : Mem 64} {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R) (hk : Kept d d') {o0 : Nat}
    (hR : ∀ q, R q → NativeRustcVm.InRange (msgAt m0) o0 q ∨
      NativeRustcVm.InRange (stackBelow m0 roundPolyStack) roundPolyStack q)
    {tail : List EW} (hsz : o0 + 16 * tail.length ≤ 80) (ho0 : o0 < 80) {s' : TState}
    (ht : TStateAt d (tAt m0) a s') (htl : NativeRustcVm.EWsAt d (off (msgAt m0) o0) tail) :
    TStateAt d' (tAt m0) a s' ∧ NativeRustcVm.EWsAt d' (off (msgAt m0) o0) tail := by
  have c := ctx_of h
  have hnw := msg_noWrap h
  unfold NativeRustcVm.NoWrap at hnw
  refine ⟨tstate_keep h hs hk (fun q hq ↦ (hR q hq).imp_left fun h' ↦ inRange_mono h' (by omega))
    ht, msg_keep h hs (by omega) (fun q hq hin ↦ ?_) htl⟩
  rcases hR q hq with h1 | h1
  · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)] at h1
    rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega)]; omega),
      toNat_off (by omega)] at hin
    omega
  · exact c.out_not_stack (msgOk h) (msg_part h ho0 (by omega) hin) h1

/-- A byte at an offset from `lo` to `hi` of the message: in its part from `lo`. -/
theorem touch_msg (h : RoundPolyPre a s e m0) {lo hi : Nat} (hhi : hi ≤ 80) {q : BitVec 64}
    (hq : Touch (msgAt m0) 80 (fun j ↦ lo ≤ j ∧ j < hi) q) :
    NativeRustcVm.InRange (off (msgAt m0) lo) (hi - lo) q := by
  have hnw := msg_noWrap h
  unfold NativeRustcVm.NoWrap at hnw
  obtain ⟨j, hj, ⟨h1, h2⟩, rfl⟩ := hq
  exact (inRange_off_iff (by omega) (by omega)).mpr ⟨h1, by omega⟩

/-- A part of the message within another. -/
theorem msg_sub (h : RoundPolyPre a s e m0) {o1 n1 o2 n2 : Nat} (h12 : o1 ≤ o2)
    (h2 : o2 + n2 ≤ o1 + n1) (h1 : o1 + n1 ≤ 80) (ho : o2 < 80) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (off (msgAt m0) o2) n2 q) :
    NativeRustcVm.InRange (off (msgAt m0) o1) n1 q := by
  have hnw := msg_noWrap h
  unfold NativeRustcVm.NoWrap at hnw
  rcases Nat.eq_zero_or_pos n2 with rfl | hn2
  · unfold NativeRustcVm.InRange at hq; omega
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega)]; omega),
    toNat_off (by omega)] at hq ⊢
  omega

/-- Two parts of the message, one before the other, are apart. -/
theorem msg_parts (h : RoundPolyPre a s e m0) {o1 n1 o2 n2 : Nat} (h12 : o1 + n1 ≤ o2)
    (h2 : o2 + n2 ≤ 80) {q : BitVec 64} (hq1 : NativeRustcVm.InRange (off (msgAt m0) o1) n1 q)
    (hq2 : NativeRustcVm.InRange (off (msgAt m0) o2) n2 q) : False := by
  have hnw := msg_noWrap h
  unfold NativeRustcVm.NoWrap at hnw
  rcases Nat.eq_zero_or_pos n2 with rfl | hn2
  · unfold NativeRustcVm.InRange at hq2; omega
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega)]; omega),
    toNat_off (by omega)] at hq1 hq2
  omega

/-- A callee's changes, its output `R` the `TState`: in the stack or the `TState`. -/
theorem callee_in (h : RoundPolyPre a s e m0) {d : MachineData} (hat : At m0 112 d) {Nc : Nat}
    (hle : 112 + Nc ≤ roundPolyStack) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow d Nc) Nc q) :
    NativeRustcVm.InRange (stackBelow m0 roundPolyStack) roundPolyStack q :=
  ((ctx_of h).inRange_callee hat hle hq).1

/-- The frame's region is in the stack, but its last 8 bytes (the return address). -/
theorem frame_in (h : RoundPolyPre a s e m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (fa m0) 112 q) :
    NativeRustcVm.InRange (stackBelow m0 roundPolyStack) roundPolyStack q :=
  (ctx_of h).inRange_frame hq

omit [Labels] in
/-- **A rejection.** -/
theorem post_none (hr : runR m0 s e = none) {m : MachineData} (hal : (reg m .rax).toNat % 256 = 0)
    (hs : NativeRustcVm.SameOutside m0.dmem m.dmem (Chg m0)) (hsv : Saved m0 m) :
    RoundPolyPost a s e m0 m := by
  refine ⟨?_, fun xs s' h ↦ ?_, fun xs s' h ↦ ?_, hs, hsv⟩
  · show boolRet m = _
    unfold boolRet
    rw [hal]; simp only [runR] at hr; simp [hr, okWord]
  · simp only [runR] at hr; simp [hr] at h
  · simp only [runR] at hr; simp [hr] at h

omit [Labels] in
/-- **A success.** -/
theorem post_some {msg : Array EW} {s' : TState} (hr : runR m0 s e = some (msg, s'))
    {m : MachineData} (hal : (reg m .rax).toNat % 256 = 1)
    (hm : NativeRustcVm.EWsAt m.dmem (msgAt m0) msg.toList) (ht : TStateAt m.dmem (tAt m0) a s')
    (hs : NativeRustcVm.SameOutside m0.dmem m.dmem (Chg m0)) (hsv : Saved m0 m) :
    RoundPolyPost a s e m0 m := by
  refine ⟨?_, fun xs s'' h ↦ ?_, fun xs s'' h ↦ ?_, hs, hsv⟩
  · show boolRet m = _
    unfold boolRet
    rw [hal]; simp only [runR] at hr; simp [hr, okWord]
  · simp only [runR] at hr
    rw [hr, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact hm
  · simp only [runR] at hr
    rw [hr, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact ht

end

theorem KeepsR.reg {S : SState} {rs : List Reg64} (h : KeepsR S rs = true) {r : Reg64}
    (hr : r ∈ rs) : S.reg r = some (.reg r) := by
  simp only [KeepsR, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact h.2 r hr

theorem KeepsR.rbx {S : SState} {rs : List Reg64} (h : KeepsR S rs = true) :
    S.reg .rbx = some (.ptr 1 0) := by
  simp only [KeepsR, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact h.1

/-- The grind's bits from `bit_length`'s result `n ≤ 64`, RBP zero: `n - 3`. -/
theorem eval_bitsS [Labels] (env : Env) {n : Nat} (hn : (env.regs .rax).toNat = n) (h64 : n ≤ 64)
    (hbp : env.regs .rbp = 0) : (bitsS.eval env).toNat % 2 ^ 32 = n - 3 := by
  simp only [bitsS, Sym.eval, SBool.eval, CmpOp.apply, UnOp.apply, BinOp.apply, hbp]
  have hlow : (low .W32 (env.regs .rax)).toNat = n := by
    simp only [low, BitVec.toNat_setWidth, show (2 : Nat) ^ Width.W32.bits = 2 ^ 32 from rfl]
    rw [hn]; omega
  by_cases h3 : n < 3
  · have : (low .W32 (env.regs .rax)).ult (low .W32 (BitVec.ofNat 64 3)) = true := by
      simp only [BitVec.ult, hlow, decide_eq_true_eq]; simp [low]; omega
    simp only [this, ite_true]
    simp [ext, low]
    omega
  · have : (low .W32 (env.regs .rax)).ult (low .W32 (BitVec.ofNat 64 3)) = false := by
      simp only [BitVec.ult, hlow, decide_eq_false_iff_not]; simp [low]; omega
    simp only [this, Bool.false_eq_true, ite_false]
    simp only [ext, low, BitVec.toNat_setWidth, BitVec.toNat_sub]
    simp [low] at hlow ⊢
    omega

/-- A value's low byte. -/
theorem toNat_mod256 (v : BitVec 64) : v.toNat % 256 = (low .W8 v).toNat := by
  simp [low, BitVec.toNat_setWidth]

/-- `RBP`'s low byte after `movb $1, %bpl`. -/
theorem merge_one (x : BitVec 64) :
    (BinOp.apply .merge .W8 x (BitVec.ofNat 64 1)).toNat % 256 = 1 := by
  rw [toNat_mod256, BinOp.apply, low8_merge]
  decide

variable [Host] {a : DecArea} {s : TState} {e : Option EW} {m0 : MachineData} {k : Nat}

/-- **The exit** at `.L9`: AL RBP's low byte, the registers restored, `ret`. -/
theorem exit_spec (hp : Placed code k) (h : RoundPolyPre a s e m0) {d : MachineData}
    (hf : RF m0 8 d) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
        (reg st.data .rax).toNat % 256 = (reg d .rbp).toNat % 256 ∧ st.data.dmem = d.dmem ∧
        Saved m0 st.data)
      ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b19Offset)⟩ := by
  have c := ctx_of h
  have hwf := frame_wf (m0 := m0) (d := d) (F := 112) (rest := []) (vars := fun _ ↦ 0) (ret := 0)
    ⟨c.mapped_frame hf.frame.kept, c.noWrap_frame⟩ (by simp) (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 d 112 [] (fun _ ↦ 0) 0) exitS d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hf.frame.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_then (infix_of b19_in_code (by simp [b19]) hp) exit_b19 hwf nofun hm
    fun st hm' hpc ↦ ?_
  obtain ⟨hepi, hmem, hrax⟩ := ok_b19
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf.frame hwf hm' hepi
  simp only [PcOk, Sym.eval] at hpc
  refine .done _ ⟨hpc.trans (hf.frame.load_ret c.stack (by rw [roundPolyStack_eq]; omega)), hrsp,
    ?_, hm'.dmem_eq hwf hmem, hsv⟩
  rw [show reg st.data .rax = _ from hm'.regs .rax _ hrax]
  simp only [Sym.eval, UnOp.apply, Env.ofMachine_regs]
  simp [ext, low, BitVec.toNat_setWidth]

/-- **A failure** at `.L8`: RBP cleared, then the exit; AL `0`. -/
theorem fail_spec (hp : Placed code k) (h : RoundPolyPre a s e m0) {d : MachineData}
    (hf : RF m0 8 d) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
        (reg st.data .rax).toNat % 256 = 0 ∧ st.data.dmem = d.dmem ∧ Saved m0 st.data)
      ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b18Offset)⟩ := by
  have c := ctx_of h
  have hwf := frame_wf (m0 := m0) (d := d) (F := 112) (rest := []) (vars := fun _ ↦ 0) (ret := 0)
    ⟨c.mapped_frame hf.frame.kept, c.noWrap_frame⟩ (by simp) (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 d 112 [] (fun _ ↦ 0) 0) exitS d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hf.frame.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_then (infix_of b18_in_code (by simp [b18]) hp) exit_b18 hwf nofun hm
    fun st hm' hpc ↦ ?_
  obtain ⟨hmid, hmem, hrbp, hrbx⟩ := ok_b18
  have hd : st.data.dmem = d.dmem := hm'.dmem_eq hwf hmem
  have hf' : RF m0 8 st.data :=
    ⟨Frame.of_block hf.frame hwf hm' hmid (by decide), by rw [hd]; exact hf.same,
      (hm'.regs .rbx _ hrbx).trans hf.rbx⟩
  have h0 : reg st.data .rbp = 0 := hm'.regs .rbp _ hrbp
  simp only [PcOk] at hpc
  obtain ⟨d', pc⟩ := st
  simp only at hpc
  subst hpc
  refine Eventually.mono (exit_spec hp h hf') fun st ⟨h1, h2, h3, h4, h5⟩ ↦
    ⟨h1, h2, ?_, h4.trans hd, h5⟩
  rw [h3, h0]
  rfl

end

end NativeRustcVmX64.Sumcheck.RoundPoly
