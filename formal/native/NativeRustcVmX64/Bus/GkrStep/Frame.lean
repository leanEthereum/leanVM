module

public import NativeRustcVmX64.Bus.GkrStep.Exec
public import NativeRustcVmX64.Bus.GkrCommon
public import NativeRustcVmX64.Bus.GkrModel
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcX64.Got

/-!
# `gkr_step`'s frame, its calls, its exits (x86-64)

The frame (`FR m0 o d`: `Fr` of `gkr_step`'s 1408-byte frame, RSP at offset `o`): `40` in the
body, `32` at an ordinary call, `0` at the sumcheck's (its three stack arguments above). The
outputs are the `TState` (RDI) and the `GkrStateW` (RCX).

- `ctxF`, `At`s at a call (`at32`, `at0`), the callee's `StackOk`, `RcAt`, `TStateOk`, outputs
  (`outFb`: frame bytes from offset `c + 8`).
- `keepCall`: frame bytes above a call kept by it; `tsKeep`, `gsKeep`: the outputs kept.
- `exit_spec`: the epilogue (`b35`), AL = RBP's low byte; `fail_spec`: `b34`, RBP = `0`.
-/

namespace NativeRustcVmX64.Bus.GkrStep

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.GkrStep
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus

@[expose] public section

/-- The outputs: the `TState` (RDI), the `GkrStateW` (RCX). -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨
    NativeRustcVm.InRange (reg m0 .rcx) gkrStateBytes q

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 1408

/-- **`gkr_step`'s frame**, RSP at offset `o`. -/
abbrev FR (m0 : MachineData) (o : Nat) (d : MachineData) : Prop :=
  Fr m0 1408 gkrStepStack slots (outs m0) o d

/-- `gkrStep`'s run from the entry's arguments. -/
abbrev run0 (s0 : TState) (g0 : GkrStateW) (m0 : MachineData) : Option (GkrStateW × TState) :=
  (gkrStep (reg m0 .rsi).toNat (decide ((reg m0 .rdx).toNat = 1)) g0).run s0

end

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 1408 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide
theorem slots_hi : ∀ p ∈ slots, 1360 ≤ p.1 ∧ p.1 + 8 ≤ 1408 := by decide
/-- The slots above every call and every frame output (`[lo, lo + len)` within `[0, 1360)`). -/
theorem slots_call {c lo len : Nat} (hc : c ≤ 1360) (hl : lo + len ≤ 1360) :
    ∀ p ∈ slots, c ≤ p.1 ∧ lo + len ≤ p.1 ∧ p.1 + 8 ≤ 1408 := by
  intro p hp
  have : 1360 ≤ p.1 ∧ p.1 + 8 ≤ 1408 := by revert p; decide
  omega

theorem N_ge : 1408 ≤ gkrStepStack := by
  unfold gkrStepStack; simp only [maxOf, List.foldr]; omega

/-- The stack an ordinary callee has. -/
theorem le32 {X : Nat}
    (hX : X ∈ [bitLengthStack, grindStack, squeezeStack, polyEvalStack, readScalarsStack,
      prodEStack, sampleChallengesStack, mleStack]) : 1408 - 32 + X ≤ gkrStepStack := by
  unfold gkrStepStack
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
  simp only [maxOf, List.foldr]
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem le0 : 1408 - 0 + sumcheckGkrStack ≤ gkrStepStack := by
  unfold gkrStepStack; simp only [maxOf, List.foldr]; omega

/-- `bitLength` of at most `3`: at most `2`. -/
theorem bitLength_small {n : Nat} (h : n ≤ 3) : LeanVM.Protocol.Verifier.bitLength n ≤ 2 := by
  unfold LeanVM.Protocol.Verifier.bitLength
  split
  · omega
  · have : Nat.log2 n < 2 := (Nat.log2_lt (by omega)).mpr (by omega)
    omega

section
variable [Labels] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData}

theorem pre_stack (h : GkrStepPre a s0 g0 m0) : StackOk m0 gkrStepStack := h.1
theorem pre_rc (h : GkrStepPre a s0 g0 m0) : RcAt m0 gkrStepStack := h.2.1
theorem pre_ts (h : GkrStepPre a s0 g0 m0) : TStateAt m0.dmem (reg m0 .rdi) a s0 := h.2.2.1
theorem pre_tok (h : GkrStepPre a s0 g0 m0) : TStateOk m0 (reg m0 .rdi) a gkrStepStack := h.2.2.2.1
theorem pre_step (h : GkrStepPre a s0 g0 m0) :
    (reg m0 .rsi).toNat = 1 ∨ (reg m0 .rsi).toNat = 2 := h.2.2.2.2.1
theorem pre_last (h : GkrStepPre a s0 g0 m0) : (reg m0 .rdx).toNat ≤ 1 := h.2.2.2.2.2.1
theorem pre_size (h : GkrStepPre a s0 g0 m0) :
    g0.point.size + (reg m0 .rsi).toNat ≤ busPointCap := h.2.2.2.2.2.2.1
theorem pre_gk (h : GkrStepPre a s0 g0 m0) :
    OutOk m0 (reg m0 .rdi) a (reg m0 .rcx) gkrStateBytes gkrStepStack := h.2.2.2.2.2.2.2.1
theorem pre_gs (h : GkrStepPre a s0 g0 m0) : GkrStateWAt m0.dmem (reg m0 .rcx) g0 :=
  h.2.2.2.2.2.2.2.2.1

theorem pre_got (h : GkrStepPre a s0 g0 m0) :
    GotAt m0 gkrStepStack [(reg m0 .rdi, tstateBytes), (a.words, 8 * a.len),
      (reg m0 .rcx, gkrStateBytes), (rcAddr, 192)] ["memcpy"] :=
  h.2.2.2.2.2.2.2.2.2

theorem FR.got_same (h : GkrStepPre a s0 g0 m0) {c : Nat} {d : MachineData}
    (fr : FR m0 c d) :
    ∀ l ∈ ["memcpy"], ∀ i < 8, d.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
      m0.dmem.get? (gotAddr l + BitVec.ofNat 64 i) := by
  refine got_keep (pre_got h) h.1
    (writes := [(reg m0 .rdi, tstateBytes), (reg m0 .rcx, gkrStateBytes)])
    (by intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> simp)
    (by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact (pre_ts h).footprint.1.2
      · exact (pre_gk h).2.1)
    (NativeRustcVm.SameOutside.mono fr.same ?_)
  intro q hq
  rcases hq with hq | hq | hq
  · exact .inr hq
  · exact .inl ⟨(reg m0 .rdi, tstateBytes), by simp, hq⟩
  · exact .inl ⟨(reg m0 .rcx, gkrStateBytes), by simp, hq⟩

/-- The entry's context, a frame of `F' ≤ N` bytes. -/
theorem ctxF (h : GkrStepPre a s0 g0 m0) (F' : Nat) (hF : F' ≤ gkrStepStack) :
    Ctx m0 (reg m0 .rdi) a gkrStepStack F' :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.1.footprint, hF⟩

theorem outs_not_rc (h : GkrStepPre a s0 g0 m0) :
    ∀ q, outs m0 q → ¬ NativeRustcVm.InRange rcAddr 192 q := by
  intro q hq
  have c := ctxF h 1408 N_ge
  rcases hq with hq | hq
  · exact c.not_rc_tstate hq
  · exact c.out_not_rc (pre_gk h) hq

theorem outs_not_frame (h : GkrStepPre a s0 g0 m0) :
    ∀ q, outs m0 q → ¬ NativeRustcVm.InRange (stackBelow m0 1408) (1408 + 8) q := by
  intro q hq
  have c := ctxF h 1408 N_ge
  rcases hq with hq | hq
  · exact not_inRange_of_apart (apart_frame c.tok.1 c.spN N_ge) c.fp.1.2 c.noWrap_frame hq
  · exact not_inRange_of_apart (apart_frame (pre_gk h).2.2.2.2.1 c.spN N_ge) (pre_gk h).2.1
      c.noWrap_frame hq

theorem wf0 (h : GkrStepPre a s0 g0 m0) {d : MachineData} (hk : Kept m0.dmem d.dmem)
    (ret : BitVec 64) : (frameEnv m0 d 1408 [] (fun _ ↦ 0) ret).WF := by
  have c := ctxF h 1408 N_ge
  exact frame_wf ⟨c.mapped_frame hk, c.noWrap_frame⟩ (by simp) (List.pairwise_singleton _ _)

theorem wfS (h : GkrStepPre a s0 g0 m0) {d : MachineData} (hk : Kept m0.dmem d.dmem)
    (ret : BitVec 64) : (frameEnv m0 d 1408 [(reg m0 .rcx, 1064)] (fun _ ↦ 0) ret).WF := by
  have c := ctxF h 1408 N_ge
  refine frame_wf ⟨c.mapped_frame hk, c.noWrap_frame⟩ (fun x hx ↦ ?_)
    (List.pairwise_pair.mpr (Apart.symm' (apart_frame (pre_gk h).2.2.2.2.1 c.spN N_ge)))
  rw [List.mem_singleton] at hx
  subst hx
  exact ⟨Mapped.keeps (pre_gk h).1 hk, (pre_gk h).2.1⟩

omit [Labels] in
theorem match_head [Labels] {d : MachineData} (fr : FR m0 40 d) (ret : BitVec 64) :
    Match (frameEnv m0 d 1408 [] (fun _ ↦ 0) ret) headS d :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨fr.frame.rsp_eval, trivial⟩ trivial trivial trivial

omit [Labels] in
theorem match_sS [Labels] {d : MachineData} (fr : FR m0 40 d) (h14 : reg d .r14 = reg m0 .rcx)
    (ret : BitVec 64) :
    Match (frameEnv m0 d 1408 [(reg m0 .rcx, 1064)] (fun _ ↦ 0) ret) sS d :=
  match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨fr.frame.rsp_eval, known_ptr rfl h14, trivial⟩
    trivial trivial trivial

/-! ## The outputs kept -/

/-- The `TState` kept where the memory changed in the stack or the `GkrStateW`. -/
theorem tsKeep (h : GkrStepPre a s0 g0 m0) {d d' : Mem 64} {R : BitVec 64 → Prop}
    (hk : Kept d d') (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → NativeRustcVm.InRange (stackBelow m0 gkrStepStack) gkrStepStack q ∨
      NativeRustcVm.InRange (reg m0 .rcx) gkrStateBytes q)
    {s : TState} (ht : TStateAt d (reg m0 .rdi) a s) : TStateAt d' (reg m0 .rdi) a s := by
  have c := ctxF h 1408 N_ge
  refine ht.frame hk (fun q hq ↦ ?_) hs
  rcases hR q hq with hq | hq
  · exact c.stack_not_t hq
  · exact c.out_not_t (pre_gk h) hq

/-- The `GkrStateW` kept where the memory changed in the stack or the `TState`. -/
theorem gsKeep (h : GkrStepPre a s0 g0 m0) {d d' : Mem 64} {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → NativeRustcVm.InRange (stackBelow m0 gkrStepStack) gkrStepStack q ∨
      NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q)
    {g : GkrStateW} (hg : GkrStateWAt d (reg m0 .rcx) g) : GkrStateWAt d' (reg m0 .rcx) g := by
  have c := ctxF h 1408 N_ge
  refine gkrStateWAt_keep hg hs fun q hq hp ↦ ?_
  rcases hR q hq with hq | hq
  · exact c.out_not_stack (pre_gk h) hp hq
  · exact (c.out_not_t (pre_gk h) hp).1 hq

/-- A byte of the frame is no output's. -/
theorem fb_not_outs (h : GkrStepPre a s0 g0 m0) {j : Nat} (hj : j < 1416) :
    ¬ outs m0 (off (fb m0) j) := fun hq ↦
  outs_not_frame h _ hq (inRange_off_self hj (by
    have := (ctxF h 1408 N_ge).noWrap_frame; unfold NativeRustcVm.NoWrap at this; omega))

/-- The frame's bytes below the slots are the stack's. -/
theorem fb_stack (h : GkrStepPre a s0 g0 m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (fb m0) 1408 q) :
    NativeRustcVm.InRange (stackBelow m0 gkrStepStack) gkrStepStack q :=
  (ctxF h 1408 N_ge).inRange_frame hq

/-! ## Calls -/

/-- The frame's base `c` bytes up, as the stack below the entry's RSP. -/
theorem fb_shift (h : GkrStepPre a s0 g0 m0) {c j : Nat} (hc : c + j ≤ 1408) :
    off (stackBelow m0 (1408 - c)) j = off (fb m0) (c + j) := by
  have := (pre_stack h).1
  have := N_ge
  rw [← off_fb (pre_stack h) N_ge (show c ≤ 1408 by omega), off_off]

/-- A state at a call from offset `c`. -/
theorem atC (h : GkrStepPre a s0 g0 m0) {c : Nat} (hc : c ≤ 1408) {d : MachineData}
    (fr : FR m0 c d) : At m0 (1408 - c) d :=
  fr.at_ (ctxF h 1408 N_ge) hc (outs_not_rc h)

theorem got_atC (h : GkrStepPre a s0 g0 m0) {c : Nat} (hc : c ≤ 1408)
    {d : MachineData} (fr : FR m0 c d) {n : Nat} (hn : 1408 - c + n ≤ gkrStepStack)
    {areas : List (BitVec 64 × Nat)}
    (ha : ∀ l ∈ ["memcpy"], ∀ b ∈ areas, Apart (gotAddr l) 8 b.1 b.2) :
    GotAt d n areas ["memcpy"] :=
  got_callee (pre_got h) (fr.got_same h) (atC h hc fr).sp h.1.1 hn ha

/-- **A frame output** for a callee at offset `c`: `n` bytes at offset `o ≥ c + 8`. -/
theorem outFb (h : GkrStepPre a s0 g0 m0) {c : Nat} {d : MachineData} (fr : FR m0 c d)
    {Nc : Nat} (hle : 1408 - c + Nc ≤ gkrStepStack) {o n : Nat} (ho : c + 8 ≤ o)
    (hon : o + n ≤ 1408) : OutOk d (reg m0 .rdi) a (off (fb m0) o) n Nc := by
  have cx := ctxF h (1408 - c) (by omega)
  have := cx.outOk_frame (atC h (by omega) fr) hle (o := o - c) (n := n) (by omega) (by omega)
  rwa [fb_shift h (by omega), show c + (o - c) = o by omega] at this

/-- **Frame bytes above a call** kept by it, where its changes `X` miss them. -/
theorem keepCall (h : GkrStepPre a s0 g0 m0) {c : Nat} {d d' : MachineData} (fr : FR m0 c d)
    {Nc : Nat} (hle : 1408 - c + Nc ≤ gkrStepStack) {X : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow d Nc) Nc q ∨ X q))
    {o : Nat} {bs : List UInt8} (ho : c ≤ o) (hob : o + bs.length ≤ 1408)
    (hX : ∀ i < bs.length, ¬ X (off (fb m0) (o + i)))
    (hb : NativeRustcVm.BytesAt d.dmem (off (fb m0) o) bs) :
    NativeRustcVm.BytesAt d'.dmem (off (fb m0) o) bs := by
  have hS := pre_stack h
  have e1 := hS.1
  have e2 := hS.2.1
  have hN := N_ge
  have hsp : (rspOf d).toNat = (rspOf m0).toNat - 1408 + c := by
    rw [fr.frame.sp, fb_off_toNat hS hN (by omega)]
  have hcb : (stackBelow d Nc).toNat = (rspOf m0).toNat - 1408 + c - Nc := by
    rw [stackBelow_toNat (by omega), hsp]
  refine NativeRustcVm.BytesAt.of_sameOutside hb hs fun i hi hq ↦ ?_
  rw [off_add] at hq
  rcases hq with hq | hq
  · rw [inRange_toNat (by rw [hcb]; omega), hcb, fb_off_toNat hS hN (by omega)] at hq
    omega
  · exact hX i hi hq

/-- A word of the frame above a call, kept. -/
theorem keepCallW (h : GkrStepPre a s0 g0 m0) {c : Nat} {d d' : MachineData} (fr : FR m0 c d)
    {Nc : Nat} (hle : 1408 - c + Nc ≤ gkrStepStack) {X : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow d Nc) Nc q ∨ X q))
    {o : Nat} {w : UInt64} (ho : c ≤ o) (hob : o + 8 ≤ 1408)
    (hX : ∀ i < 8, ¬ X (off (fb m0) (o + i)))
    (hb : NativeRustcVm.WordAt d.dmem (off (fb m0) o) w) :
    NativeRustcVm.WordAt d'.dmem (off (fb m0) o) w :=
  keepCall h fr hle hs (bs := NativeRustcVm.wordBytes w) ho
    (by rw [NativeRustcVm.length_wordBytes]; exact hob)
    (fun i hi ↦ hX i (by rwa [NativeRustcVm.length_wordBytes] at hi)) hb

/-- Elements of the frame above a call, kept. -/
theorem keepCallE (h : GkrStepPre a s0 g0 m0) {c : Nat} {d d' : MachineData} (fr : FR m0 c d)
    {Nc : Nat} (hle : 1408 - c + Nc ≤ gkrStepStack) {X : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow d Nc) Nc q ∨ X q))
    {o : Nat} {xs : List EW} (ho : c ≤ o) (hob : o + 16 * xs.length ≤ 1408)
    (hX : ∀ i < 16 * xs.length, ¬ X (off (fb m0) (o + i)))
    (hb : NativeRustcVm.EWsAt d.dmem (off (fb m0) o) xs) :
    NativeRustcVm.EWsAt d'.dmem (off (fb m0) o) xs :=
  keepCall h fr hle hs (bs := xs.flatMap NativeRustcVm.ewBytes) ho
    (by rw [NativeRustcVm.length_ewsBytes]; exact hob)
    (fun i hi ↦ hX i (by rwa [NativeRustcVm.length_ewsBytes] at hi)) hb

/-- A callee's stack is in the entry's. -/
theorem calleeStack (h : GkrStepPre a s0 g0 m0) {c : Nat} (hc : c ≤ 1408) {d : MachineData}
    (fr : FR m0 c d) {Nc : Nat} (hle : 1408 - c + Nc ≤ gkrStepStack) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow d Nc) Nc q) :
    NativeRustcVm.InRange (stackBelow m0 gkrStepStack) gkrStepStack q :=
  ((ctxF h (1408 - c) (by omega)).inRange_callee (atC h hc fr) hle hq).1

/-- Bytes of the frame at `o` within the frame's bytes. -/
theorem fbo_fb (h : GkrStepPre a s0 g0 m0) {o n : Nat} (hon : o + n ≤ 1408) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (off (fb m0) o) n q) : NativeRustcVm.InRange (fb m0) 1408 q := by
  have hnw := (ctxF h 1408 N_ge).noWrap_frame
  unfold NativeRustcVm.NoWrap at hnw
  exact inRange_of_off (by show (stackBelow m0 1408).toNat + 1408 ≤ 2 ^ 64; omega) hon hq

/-- A frame byte at offset `o` is in the stack. -/
theorem fbo_stack (h : GkrStepPre a s0 g0 m0) {o n : Nat} (hon : o + n ≤ 1408) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (off (fb m0) o) n q) :
    NativeRustcVm.InRange (stackBelow m0 gkrStepStack) gkrStepStack q :=
  fb_stack h (fbo_fb h hon hq)

/-- Two frame ranges apart. -/
theorem fbo_apart (h : GkrStepPre a s0 g0 m0) {o n o' n' : Nat} (hon : o + n ≤ 1408)
    (hon' : o' + n' ≤ 1408) (hd : o + n ≤ o' ∨ o' + n' ≤ o) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (off (fb m0) o) n q) :
    ¬ NativeRustcVm.InRange (off (fb m0) o') n' q := by
  have hS := pre_stack h
  have hN := N_ge
  have e1 := hS.1
  have e2 := hS.2.1
  have hb := stackBelow_toNat (m := m0) (n := 1408) (by omega)
  intro hq'
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; exact absurd hq (by unfold NativeRustcVm.InRange; omega)
  rcases Nat.eq_zero_or_pos n' with h0' | h0'
  · subst h0'; exact absurd hq' (by unfold NativeRustcVm.InRange; omega)
  rw [inRange_toNat (by rw [fb_off_toNat hS hN (by omega)]; omega),
    fb_off_toNat hS hN (by omega)] at hq hq'
  omega

end

/-! ## Blocks -/

section
variable [Labels] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData}

omit [Labels] in
theorem keeps_reg {S : SState} {rs : List Reg64} (h : Keeps S rs = true) {r : Reg64}
    (hr : r ∈ rs) : S.reg r = some (.reg r) := by
  unfold Keeps at h
  rw [List.all_eq_true] at h
  simpa using h r hr

/-- A register a block kept. -/
theorem kr {d d' : MachineData} {rs' : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hm : Match (Env.ofMachine d rs' vars ret) S d')
    {rs : List Reg64} (hk : Keeps S rs = true) {r : Reg64} (hr : r ∈ rs) : reg d' r = reg d r :=
  hm.regs _ _ (keeps_reg hk hr)

/-- A register a block set. -/
theorem rv {d d' : MachineData} {rs' : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hm : Match (Env.ofMachine d rs' vars ret) S d') {r : Reg64}
    {v : Sym} (h : S.reg r = some v) : reg d' r = v.eval (Env.ofMachine d rs' vars ret) :=
  hm.regs _ _ h

omit [Labels] in
theorem W0_spec {S : SState} {ivs : List (Nat × Nat)} (h : W0 S ivs = true) :
    ∀ w ∈ S.mem, w.r = 0 ∧ ∃ p ∈ ivs, p.1 ≤ w.off ∧ w.off + w.n ≤ p.2 := by
  intro w hw
  unfold W0 at h
  rw [List.all_eq_true] at h
  have := h w hw
  simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true, decide_eq_true_eq] at this
  exact this

omit [Labels] in
theorem W01_spec {S : SState} {ivs : List (Nat × Nat)} {lo hi : Nat} (h : W01 S ivs lo hi = true) :
    ∀ w ∈ S.mem, (w.r = 0 ∧ ∃ p ∈ ivs, p.1 ≤ w.off ∧ w.off + w.n ≤ p.2) ∨
      (w.r = 1 ∧ lo ≤ w.off ∧ w.off + w.n ≤ hi) := by
  intro w hw
  unfold W01 at h
  rw [List.all_eq_true] at h
  have := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true,
    decide_eq_true_eq] at this
  rcases this with h1 | h1
  · exact .inl h1
  · exact .inr ⟨h1.1.1, h1.1.2, h1.2⟩

/-- A block writing the frame below the slots (and region 1, the `GkrStateW`, within `[lo, hi)`):
the frame kept, the memory changed in the frame below `1360` and those bytes. -/
theorem FR.block (h : GkrStepPre a s0 g0 m0) {o o' : Nat} {d d' : MachineData}
    {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {S : SState} (fr : FR m0 o d)
    (hwf : (frameEnv m0 d 1408 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 1408 rest (fun _ ↦ 0) ret) S d') (hmid : MidOk 1408 o' slots S = true)
    (hrest : rest = [] ∨ rest = [(reg m0 .rcx, 1064)]) {ivs : List (Nat × Nat)} {lo hi : Nat}
    (hW : W01 S ivs lo hi = true) (hivs : ∀ p ∈ ivs, p.2 ≤ 1360) (hhi : hi ≤ 1064) :
    FR m0 o' d' ∧ NativeRustcVm.SameOutside d.dmem d'.dmem (fun q ↦
      NativeRustcVm.InRange (fb m0) 1360 q ∨ NativeRustcVm.InRange (off (reg m0 .rcx) lo) (hi - lo) q) := by
  have hS := pre_stack h
  have hN := N_ge
  have e1 := hS.1
  have e2 := hS.2.1
  have hfb := stackBelow_toNat (m := m0) (n := 1408) (by omega)
  have hfb' : (fb m0).toNat = (rspOf m0).toNat - 1408 := hfb
  have hsN := stackBelow_toNat (m := m0) (n := gkrStepStack) (by omega)
  have hgb : gkrStateBytes = 1064 := rfl
  have hgnw : (reg m0 .rcx).toNat + 1064 ≤ 2 ^ 64 := (pre_gk h).2.1
  have hWr : ∀ q, Written (frameEnv m0 d 1408 rest (fun _ ↦ 0) ret) S q →
      NativeRustcVm.InRange (fb m0) 1360 q ∨
        NativeRustcVm.InRange (off (reg m0 .rcx) lo) (hi - lo) q := by
    intro q hq
    obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hq
    rcases W01_spec hW w hw with ⟨hr, p, hp, hp1, hp2⟩ | ⟨hr, hl, hh⟩
    · rw [hr] at hb
      cases hb
      have := hivs p hp
      left
      rw [inRange_toNat (by omega)]
      omega
    · rw [hr] at hb
      rcases hrest with rfl | rfl
      · cases hb
      · cases hb
        have hwn : 0 < w.n := by omega
        right
        rw [inRange_toNat (by rw [toNat_off (by omega)]; omega), toNat_off (by omega)]
        omega
  have hs : NativeRustcVm.SameOutside d.dmem d'.dmem (fun q ↦
      NativeRustcVm.InRange (fb m0) 1360 q ∨ NativeRustcVm.InRange (off (reg m0 .rcx) lo) (hi - lo) q) :=
    fun q hq ↦ hm.get?_mem0 hwf fun hw ↦ hq (hWr q hw)
  refine ⟨(Fr.block fr hS hN hwf hm hmid slots_le fun q hw ↦ ?_).1, hs⟩
  rcases hWr q hw with hq | hq
  · left
    rw [inRange_toNat (by omega)] at hq ⊢
    omega
  · right; right
    rcases Nat.eq_zero_or_pos (hi - lo) with h0 | h0
    · rw [h0] at hq; exact absurd hq (by unfold NativeRustcVm.InRange; omega)
    rw [inRange_toNat (by rw [toNat_off (by omega)]; omega), toNat_off (by omega)] at hq
    rw [hgb, inRange_toNat (by omega)]
    omega

/-- A block without writes keeps the frame and the memory. -/
theorem FR.block_nil (h : GkrStepPre a s0 g0 m0) {o o' : Nat} {d d' : MachineData}
    {ret : BitVec 64} {S : SState} (fr : FR m0 o d)
    (hwf : (frameEnv m0 d 1408 [] (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 1408 [] (fun _ ↦ 0) ret) S d') (hmid : MidOk 1408 o' slots S = true)
    (hmem : S.mem = []) : FR m0 o' d' ∧ d'.dmem = d.dmem :=
  ⟨(Fr.block0 fr (pre_stack h) N_ge hwf hm hmid slots_le (by simp [hmem])).1, hm.dmem_eq hwf hmem⟩

/-- **Memory changed in the frame below the slots** (a loop's writes) keeps the frame. -/
theorem FR.local (h : GkrStepPre a s0 g0 m0) {o : Nat} {d d' : MachineData} (fr : FR m0 o d)
    (hrsp : rspOf d' = rspOf d) (hcs : ∀ r, calleeSaved r = true → reg d' r = reg d r)
    (hk : Kept d.dmem d'.dmem)
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fb m0) 1360)) :
    FR m0 o d' := by
  have hS := pre_stack h
  have hN := N_ge
  have e1 := hS.1
  have e2 := hS.2.1
  have hnot : ∀ j, 1360 ≤ j → j < 1416 → ¬ NativeRustcVm.InRange (fb m0) 1360 (off (fb m0) j) := by
    intro j hj1 hj2 hq
    rw [inRange_toNat (by rw [stackBelow_toNat (by omega)]; omega),
      fb_off_toNat hS hN (by omega), stackBelow_toNat (by omega)] at hq
    omega
  refine ⟨⟨hrsp.trans fr.frame.sp, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans fr.frame.kept hk,
    fun r hr hsl ↦ (hcs r hr).trans (fr.frame.regs r hr hsl)⟩,
    NativeRustcVm.SameOutside.mono (fr.same.trans hs) fun q hq ↦ hq.elim id
      fun hq ↦ .inl (fb_stack h (inRange_mono hq (by omega)))⟩
  · refine bytesAt_congr (fr.frame.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    have := slots_hi p hp
    rw [off_add]
    exact hs _ (hnot _ (by omega) (by omega))
  · rw [hs _ (hnot _ (by omega) (by omega))]
    exact fr.frame.ret j hj

omit [Labels] in
/-- A stack argument a block wrote in the frame, RSP at offset `c`. -/
theorem stackArg_of {d : MachineData} {c : Nat} (hrsp : rspOf d = off (fb m0) c) {i : Nat}
    {w : UInt64} (hw : NativeRustcVm.WordAt d.dmem (off (fb m0) (c + 8 + 8 * i)) w) :
    stackArg d i = w.toBitVec := by
  unfold stackArg
  rw [hrsp, off_add, show c + (8 + 8 * i) = c + 8 + 8 * i by omega,
    NativeRustcVm.wordOf_of_wordAt hw]

end

section
variable [Labels]

/-- **After `poly_eval`** (`b5`, `k + NativeRustcVmX64.Vm.GkrStep.b5Offset`): the combiner `c`, the claim it gives (RAX, RDX), the
`TState` after the challenge, `last` at `44`, `c₀` at `104`, `c₁` in RBP. -/
structure AtPE (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData) (d : MachineData) :
    Prop where
  fr : FR m0 40 d
  rbx : reg d .rbx = reg m0 .rsi
  r12 : reg d .r12 = reg m0 .rdx
  r14 : reg d .r14 = reg m0 .rcx
  r15 : reg d .r15 = reg m0 .rdi
  rbp : reg d .rbp = s0.sponge.squeeze.1.c1.toBitVec
  rax : reg d .rax = (polyEval g0.values s0.sponge.squeeze.1).c0.toBitVec
  rdx : reg d .rdx = (polyEval g0.values s0.sponge.squeeze.1).c1.toBitVec
  l44 : NativeRustcVm.BytesAt d.dmem (off (fb m0) 44) ((List.range 4).map (byteOf (reg m0 .rdx)))
  c104 : NativeRustcVm.WordAt d.dmem (off (fb m0) 104) s0.sponge.squeeze.1.c0
  ts : TStateAt d.dmem (reg m0 .rdi) a { s0 with sponge := s0.sponge.squeeze.2 }
  gs : GkrStateWAt d.dmem (reg m0 .rcx) g0

/-- **At the children** (`b9`, `k + NativeRustcVmX64.Vm.GkrStep.b9Offset`): the sumcheck's challenges `xs` at `352`, its claim `cl`
(the `Option<EW>` at `112`), `2^step` in R12, `|xs|` in R13. -/
structure AtCh (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData) (c cl : EW)
    (xs : Array EW) (s2 : TState) (d : MachineData) : Prop where
  fr : FR m0 40 d
  rbx : reg d .rbx = reg m0 .rsi
  r12 : (reg d .r12).toNat = 2 ^ (reg m0 .rsi).toNat
  r13 : (reg d .r13).toNat = xs.size
  r14 : reg d .r14 = reg m0 .rcx
  r15 : reg d .r15 = reg m0 .rdi
  rbp : reg d .rbp = c.c1.toBitVec
  l44 : NativeRustcVm.BytesAt d.dmem (off (fb m0) 44) ((List.range 4).map (byteOf (reg m0 .rdx)))
  c104 : NativeRustcVm.WordAt d.dmem (off (fb m0) 104) c.c0
  clw : NativeRustcVm.EWAt d.dmem (off (fb m0) 120) cl
  pa : NativeRustcVm.WordAt d.dmem (off (fb m0) 96) (UInt64.ofBitVec (off (reg m0 .rcx) 56))
  hxs : NativeRustcVm.EWsAt d.dmem (off (fb m0) 352) xs.toList
  size : xs.size + (reg m0 .rsi).toNat ≤ busPointCap
  ts : TStateAt d.dmem (reg m0 .rdi) a s2
  gs : GkrStateWAt d.dmem (reg m0 .rcx) g0
  run : run0 s0 g0 m0 = gkrChildren (reg m0 .rsi).toNat c cl xs s2

/-- **At the products** (`b15`, `k + NativeRustcVmX64.Vm.GkrStep.b15Offset`): the children `h0`, `h1`, `h2` at `112`, `176`, `240`,
the claim's limbs at `88`, `80`. -/
structure AtPr (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData) (c cl : EW)
    (xs h0 h1 h2 : Array EW) (s3 : TState) (d : MachineData) : Prop where
  fr : FR m0 40 d
  rbx : reg d .rbx = reg m0 .rsi
  r12 : (reg d .r12).toNat = 2 ^ (reg m0 .rsi).toNat
  r13 : (reg d .r13).toNat = xs.size
  r14 : reg d .r14 = reg m0 .rcx
  r15 : reg d .r15 = reg m0 .rdi
  rbp : reg d .rbp = c.c1.toBitVec
  l44 : NativeRustcVm.BytesAt d.dmem (off (fb m0) 44) ((List.range 4).map (byteOf (reg m0 .rdx)))
  c104 : NativeRustcVm.WordAt d.dmem (off (fb m0) 104) c.c0
  cl88 : NativeRustcVm.WordAt d.dmem (off (fb m0) 88) cl.c0
  cl80 : NativeRustcVm.WordAt d.dmem (off (fb m0) 80) cl.c1
  pa : NativeRustcVm.WordAt d.dmem (off (fb m0) 96) (UInt64.ofBitVec (off (reg m0 .rcx) 56))
  hxs : NativeRustcVm.EWsAt d.dmem (off (fb m0) 352) xs.toList
  size : xs.size + (reg m0 .rsi).toNat ≤ busPointCap
  k0 : NativeRustcVm.EWsAt d.dmem (off (fb m0) 112) h0.toList
  k1 : NativeRustcVm.EWsAt d.dmem (off (fb m0) 176) h1.toList
  k2 : NativeRustcVm.EWsAt d.dmem (off (fb m0) 240) h2.toList
  z0 : h0.size = 2 ^ (reg m0 .rsi).toNat
  z1 : h1.size = 2 ^ (reg m0 .rsi).toNat
  z2 : h2.size = 2 ^ (reg m0 .rsi).toNat
  ts : TStateAt d.dmem (reg m0 .rdi) a s3
  gs : GkrStateWAt d.dmem (reg m0 .rcx) g0
  run : run0 s0 g0 m0 = gkrFinish (reg m0 .rsi).toNat c cl xs h0 h1 h2 s3

/-- **After the check** (`b21`, `k + NativeRustcVmX64.Vm.GkrStep.b21Offset`): the coordinates to sample. -/
structure AtTl (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData)
    (xs h0 h1 h2 : Array EW) (s3 : TState) (d : MachineData) : Prop where
  fr : FR m0 40 d
  rbx : reg d .rbx = reg m0 .rsi
  r12 : (reg d .r12).toNat = 2 ^ (reg m0 .rsi).toNat
  r13 : (reg d .r13).toNat = xs.size
  r14 : reg d .r14 = reg m0 .rcx
  r15 : reg d .r15 = reg m0 .rdi
  l44 : NativeRustcVm.BytesAt d.dmem (off (fb m0) 44) ((List.range 4).map (byteOf (reg m0 .rdx)))
  pa : NativeRustcVm.WordAt d.dmem (off (fb m0) 96) (UInt64.ofBitVec (off (reg m0 .rcx) 56))
  hxs : NativeRustcVm.EWsAt d.dmem (off (fb m0) 352) xs.toList
  size : xs.size + (reg m0 .rsi).toNat ≤ busPointCap
  k0 : NativeRustcVm.EWsAt d.dmem (off (fb m0) 112) h0.toList
  k1 : NativeRustcVm.EWsAt d.dmem (off (fb m0) 176) h1.toList
  k2 : NativeRustcVm.EWsAt d.dmem (off (fb m0) 240) h2.toList
  z0 : h0.size = 2 ^ (reg m0 .rsi).toNat
  z1 : h1.size = 2 ^ (reg m0 .rsi).toNat
  z2 : h2.size = 2 ^ (reg m0 .rsi).toNat
  ts : TStateAt d.dmem (reg m0 .rdi) a s3
  gs : GkrStateWAt d.dmem (reg m0 .rcx) g0
  run : run0 s0 g0 m0 = ((sampleChallenges (reg m0 .rsi).toNat).run s3).bind fun y ↦
    some (⟨#[multilinearEval h0 y.1, multilinearEval h1 y.1, multilinearEval h2 y.1],
      y.1 ++ xs⟩, y.2)

end

/-! ## The exits -/

section
variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData} {k : Nat}

/-- What `gkr_step` reaches. -/
abbrev Goal (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData) (st : MachineState) :
    Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ GkrStepPost a s0 g0 m0 st.data

/-- **The epilogue** (`NativeRustcVmX64.Vm.GkrStep.label_18`, `b35`): AL = RBP's low byte. -/
theorem exit_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0) {d : MachineData}
    (fr : FR m0 40 d) (hbp : (reg d .rbp).toNat % 256 = (okWord (run0 s0 g0 m0).isSome).toNat)
    (hok : ∀ g' s', run0 s0 g0 m0 = some (g', s') →
      TStateAt d.dmem (reg m0 .rdi) a s' ∧ GkrStateWAt d.dmem (reg m0 .rcx) g') :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b35Offset)⟩ := by
  have hwf := wf0 h fr.frame.kept 0
  obtain ⟨hepi, hmem, hrax⟩ := ok_b35
  refine fr.exit (pre_stack h) N_ge (infix_of b35_in_code (by simp [b35]) hp) exit_b35 hwf rfl
    (match_head fr 0) hepi (fun q hw ↦ ?_)
    fun st hm hpc hrsp hsame _ hsv ↦ .done _ ⟨hpc, hrsp, ?_, ?_, ?_, hsv⟩
  · obtain ⟨w, hw, -⟩ := hw
    rw [hmem] at hw
    cases hw
  · show (reg st.data .rax).toNat % 256 = _
    rw [show reg st.data .rax = _ from hm.regs _ _ hrax]
    show (UnOp.apply .trunc .W32 (reg d .rbp)).toNat % 256 = _
    rw [trunc32_mod, hbp]
  · intro g' s' he
    rw [hm.dmem_eq hwf hmem]
    exact hok g' s' he
  · exact NativeRustcVm.SameOutside.mono hsame fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact .inr (.inr hq)
      · exact .inl hq
      · exact .inr (.inl hq)

/-- **A failure** (`NativeRustcVmX64.Vm.GkrStep.label_17`, `b34`): RBP = `0`, then the epilogue. -/
theorem fail_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0) {d : MachineData}
    (fr : FR m0 40 d) (hr : run0 s0 g0 m0 = none) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b34Offset)⟩ := by
  have hwf := wf0 h fr.frame.kept 0
  obtain ⟨hok, hmem, hbp⟩ := ok_b34
  refine exec_then (infix_of b34_in_code (by simp [b34]) hp) exit_b34 hwf nofun
    (match_head fr 0) fun st hm hpc ↦ ?_
  have fr' := (Fr.block0 fr (pre_stack h) N_ge hwf hm hok slots_le (by simp [hmem])).1
  simp only [PcOk] at hpc
  refine at_pc (hpc.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b34_next))
    (exit_spec hp h fr' ?_ fun g' s' he ↦ by rw [hr] at he; cases he)
  rw [hr, show reg st.data .rbp = BitVec.ofNat 64 0 from hm.regs _ _ hbp]
  rfl

end

end

end NativeRustcVmX64.Bus.GkrStep
