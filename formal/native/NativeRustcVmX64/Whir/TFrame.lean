module

public import NativeRustcVmX64.Whir.Common
public import NativeRustcVmX64.Transcript.Callee
public import NativeRustcVmX64.Spec.Whir
public import NativeRustcVm.Transcript.Update
public import NativeRustcVm.Whir.Sample
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Got
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names

/-!
# Calls from a frame holding a `TState` (x86-64)

`TCtx m0 F N t a outs`: the entry `m0` of a function keeping an `F`-byte frame (its pushes, its
locals and the 8-byte slot its calls push their return address in; region 0 of a block's
environment, `Transcript.frameEnv`) at the top of its `N` bytes of stack, with the `TState` at `t`
(reading the decoded area `a`) among its outputs `outs`, which are apart from the frame, the round
constants and the decoded area. `WFr`: a state of the body, RSP at the frame's offset `8`, memory
changed only in the outputs and the stack. A block keeps it (`WFr.block`), a block ending in a
call and the call keep it (`WFr.call`); the callee gets its stack (`TCtx.stackOk`), the round
constants (`TCtx.rcAt`), the `TState`'s footprint (`TCtx.tstateOk`), an output in the frame
(`TCtx.localOk`).
-/

namespace NativeRustcVmX64.Whir

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript (Frame frameEnv Slots MidOk)

@[expose] public section

/-- **The context**: the entry's stack, round constants, the `TState`'s footprint; the outputs
contain the `TState` and miss the round constants, the decoded area and the frame. -/
structure TCtx [Labels] (m0 : MachineData) (F N : Nat) (t : BitVec 64) (a : DecArea)
    (outs : BitVec 64 → Prop) : Prop where
  stack : StackOk m0 N
  rc : RcAt m0 N
  tok : TStateOk m0 t a N
  fp : Footprint m0.dmem t a
  hF : F ≤ N
  ot : ∀ q, InRange t tstateBytes q → outs q
  orc : ∀ q, outs q → ¬ InRange rcAddr 192 q
  oa : ∀ q, outs q → ¬ InRange a.words (8 * a.len) q
  ofr : ∀ q, outs q → ¬ InRange (stackBelow m0 F) (F + 8) q
  got : GotAt m0 N [(t, tstateBytes), (a.words, 8 * a.len), (rcAddr, 192)] ["memcpy"]
  got_keep : ∀ d : MachineData,
    SameOutside m0.dmem d.dmem (fun q => outs q ∨ InRange (stackBelow m0 N) N q) →
    ∀ i < 8, d.dmem.get? (gotAddr "memcpy" + BitVec.ofNat 64 i) =
      m0.dmem.get? (gotAddr "memcpy" + BitVec.ofNat 64 i)

/-- **A state of the body**: the frame, RSP at its offset `8`; memory changed only in the outputs
and the stack. -/
structure WFr (m0 : MachineData) (F N : Nat) (slots : Slots) (outs : BitVec 64 → Prop)
    (d : MachineData) : Prop where
  fr : Frame m0 F slots 8 d
  same : SameOutside m0.dmem d.dmem (fun q ↦ outs q ∨ InRange (stackBelow m0 N) N q)

/-- **Before a call**: the frame, RSP at its offset `0`; memory changed only in the outputs and
the stack; the `TState` `s` at `t`. -/
structure AtCall (m0 : MachineData) (F N : Nat) (slots : Slots) (outs : BitVec 64 → Prop)
    (t : BitVec 64) (a : DecArea) (s : TState) (d : MachineData) : Prop where
  fr : Frame m0 F slots 0 d
  same : SameOutside m0.dmem d.dmem (fun q ↦ outs q ∨ InRange (stackBelow m0 N) N q)
  ts : TStateAt d.dmem t a s

end

public section

section
variable [Labels] {m0 : MachineData} {F N : Nat} {t : BitVec 64} {a : DecArea}
  {outs : BitVec 64 → Prop} {slots : Slots}

theorem TCtx.hN (c : TCtx m0 F N t a outs) : N ≤ (rspOf m0).toNat := c.stack.1
theorem TCtx.h8 (c : TCtx m0 F N t a outs) : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := c.stack.2.1

/-- The Keccak constants are one of the verifier's already protected read-only items. -/
theorem rc_mem_rodata : (rcAddr, 192) ∈ rodataAreas := by
  change (rodataAddr .keccakRC, NativeRustcVm.Data.Item.bytes .keccakRC |>.length) ∈ rodataAreas
  exact List.mem_map.mpr ⟨.keccakRC, by decide, rfl⟩

/-- Calls preserve the loader bytes and protect only subranges of existing areas. -/
theorem TCtx.got_callee (c : TCtx m0 F N t a outs) {d : MachineData} {n : Nat}
    {areas : List (BitVec 64 × Nat)}
    (hs : SameOutside m0.dmem d.dmem (fun q => outs q ∨ InRange (stackBelow m0 N) N q))
    (hsp : rspOf d = stackBelow m0 F) (hle : F + n ≤ N)
    (hcover : ∀ ar ∈ areas, ∃ b ∈ (stackBelow m0 N, N + 8) ::
      [(t, tstateBytes), (a.words, 8 * a.len), (rcAddr, 192)],
      b.1.toNat ≤ ar.1.toNat ∧ ar.1.toNat + ar.2 ≤ b.1.toNat + b.2) :
    GotAt d n areas ["memcpy"] := by
  have hfb := stackBelow_toNat (m := m0) (n := F) (by have := c.hN; have := c.hF; omega)
  have hsb := stackBelow_toNat c.hN
  have hd : (stackBelow d n).toNat = (rspOf m0).toNat - F - n := by
    rw [stackBelow_toNat (by rw [hsp, hfb]; have := c.hN; omega), hsp, hfb]
  apply NativeRustcVmX64.GotAt.callee c.got _ _ _ hcover
  · intro l hl i hi
    simp only [List.mem_singleton] at hl
    subst l
    exact c.got_keep d hs i hi
  · rw [hsb, hd]; have := c.hN; omega
  · rw [hsb, hd]; have := c.hN; omega

/-- Local transcript buffers lie in the caller's existing stack area. -/
theorem TCtx.got_local (c : TCtx m0 F N t a outs) {ob n : Nat} (hob : ob + n ≤ F) :
    ∃ b ∈ (stackBelow m0 N, N + 8) ::
      [(t, tstateBytes), (a.words, 8 * a.len), (rcAddr, 192)],
      b.1.toNat ≤ (off (stackBelow m0 F) ob).toNat ∧
        (off (stackBelow m0 F) ob).toNat + n ≤ b.1.toNat + b.2 := by
  have hfb := stackBelow_toNat (m := m0) (n := F) (by have := c.hN; have := c.hF; omega)
  have hsb := stackBelow_toNat c.hN
  have hf := c.hF
  have hn := c.hN
  have ht := c.h8
  refine ⟨(stackBelow m0 N, N + 8), by simp, ?_, ?_⟩ <;>
    rw [hsb, NativeRustcVm.Transcript.toNat_off (by rw [hfb]; omega), hfb] <;> omega

theorem TCtx.fnw (c : TCtx m0 F N t a outs) : NativeRustcVm.NoWrap (stackBelow m0 F) (F + 8) :=
  Transcript.frame_noWrap c.stack c.hF

/-- The frame's bytes below `F` are the stack's. -/
theorem TCtx.frame_stack (c : TCtx m0 F N t a outs) {q : BitVec 64}
    (hq : InRange (stackBelow m0 F) F q) : InRange (stackBelow m0 N) N q :=
  Transcript.inRange_frame_stack c.h8 c.hN c.hF hq

/-- The frame's environment without other regions is well formed. -/
theorem TCtx.wf0 (c : TCtx m0 F N t a outs) {d : MachineData} (hk : Kept m0.dmem d.dmem)
    {vars : Nat → BitVec 64} {ret : BitVec 64} : (frameEnv m0 d F [] vars ret).WF :=
  Transcript.frame_wf ⟨Mapped.keeps (Transcript.frame_mapped c.stack c.hF) hk, c.fnw⟩ (by simp)
    (List.pairwise_singleton _ _)

/-- The middle state of a frame. -/
theorem WFr.mid {d : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hw : WFr m0 F N slots outs d) :
    Match (frameEnv m0 d F [] vars ret) (init [F + 8] [(.rsp, .ptr 0 ((8 : Nat) : Int))]) d :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨hw.fr.rsp_eval, trivial⟩ trivial trivial trivial

/-- The `TState` kept by memory changes in the frame. -/
theorem TCtx.ts_frame (c : TCtx m0 F N t a outs) {d d' : MachineData} {s : TState}
    (hk : Kept d.dmem d'.dmem) {L : Nat} (hL : L ≤ F + 8)
    (hs : SameOutside d.dmem d'.dmem (InRange (stackBelow m0 F) L))
    (ht : TStateAt d.dmem t a s) : TStateAt d'.dmem t a s := by
  have hTF := Transcript.apart_frame c.tok.1 c.hN c.hF
  have hAF := Transcript.apart_frame c.tok.2.1 c.hN c.hF
  refine ht.frame hk (fun q hq ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩) hs
  · exact not_inRange_of_apart hTF c.fp.1.2 c.fnw h (Transcript.inRange_mono hq hL)
  · exact not_inRange_of_apart hAF c.fp.2.1.2 c.fnw h (Transcript.inRange_mono hq hL)

/-- **A block** keeps a body state: RSP back at offset `8`, its writes in the frame below `F` or
in the outputs. -/
theorem WFr.block (c : TCtx m0 F N t a outs) {d d' : MachineData} (hw : WFr m0 F N slots outs d)
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (frameEnv m0 d F rest vars ret).WF) (hm : Match (frameEnv m0 d F rest vars ret) S d')
    (hmid : MidOk F 8 slots S = true) (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F)
    (hwr : ∀ q, Written (frameEnv m0 d F rest vars ret) S q →
      InRange (stackBelow m0 F) F q ∨ outs q) : WFr m0 F N slots outs d' :=
  ⟨Frame.of_block hw.fr hwf hm hmid hsl, fun q hq ↦ by
    rw [hm.get?_mem0 hwf fun hW ↦ hq ((hwr q hW).elim (fun h ↦ .inr (c.frame_stack h)) .inl)]
    exact hw.same q hq⟩

/-- Memory a block's writes miss. -/
theorem block_same {d d' : MachineData} {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hm : Match (frameEnv m0 d F rest vars ret) S d') :
    SameOutside d.dmem d'.dmem (fun q ↦ Written (frameEnv m0 d F rest vars ret) S q) :=
  fun _ hq ↦ hm.get?_mem0 hwf hq

omit [Labels] in
/-- Writes all in region `0` below `L`: in the frame's first `L` bytes. -/
theorem written0 {d : MachineData} {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hwf : (frameEnv m0 d F rest vars ret).WF) {L : Nat}
    (hL : L ≤ F + 8) (hS : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ L) {q : BitVec 64}
    (h : Written (frameEnv m0 d F rest vars ret) S q) : InRange (stackBelow m0 F) L q := by
  obtain ⟨w, hw, b, sz, hb, j, h1, h2, rfl⟩ := Transcript.written_off hwf h
  obtain ⟨hr, hle⟩ := hS w hw
  rw [hr] at hb
  cases hb
  have := hwf.noWrap 0 _ _ rfl
  exact inRange_off_self (by omega) (by omega)

/-- **A block ending in a call** from a body state, its writes in the frame below `F`; the
memory it leaves outside the frame the body state's. -/
theorem WFr.atCall (c : TCtx m0 F N t a outs) {d : MachineData} (hw : WFr m0 F N slots outs d)
    {s : TState} (hts : TStateAt d.dmem t a s) {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState} {d' : MachineData}
    (hwf : (frameEnv m0 d F rest vars ret).WF) (hm : Match (frameEnv m0 d F rest vars ret) S d')
    (hmid : MidOk F 0 slots S = true) (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F)
    (hS : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ F) :
    AtCall m0 F N slots outs t a s d' ∧ SameOutside d.dmem d'.dmem (InRange (stackBelow m0 F) F) := by
  have hs1 : SameOutside d.dmem d'.dmem (InRange (stackBelow m0 F) F) :=
    Transcript.sameOutside_low hwf hm (r := 0) rfl (by omega) hS
  refine ⟨⟨Frame.of_block hw.fr hwf hm hmid hsl, fun q hq ↦ ?_,
    c.ts_frame (hm.kept hwf) (by omega) hs1 hts⟩, hs1⟩
  rw [hs1 q fun h ↦ hq (.inr (c.frame_stack h))]
  exact hw.same q hq

end

section
variable [Host] {m0 : MachineData} {F N : Nat} {t : BitVec 64} {a : DecArea}
  {outs : BitVec 64 → Prop} {slots : Slots}

/-- **A call** from a state `st1` of the frame with RSP at its offset `0` (the return address
pushed there), memory changed only in the outputs and the stack: the callee, of `N'` bytes of stack
below the frame, changes its stack, frame bytes `Lf` (off the slots, below `F`) and the outputs. -/
theorem call0 (c : TCtx m0 F N t a outs) {st1 : MachineState} (hf1 : Frame m0 F slots 0 st1.data)
    (hso1 : SameOutside m0.dmem st1.data.dmem (fun q ↦ outs q ∨ InRange (stackBelow m0 N) N q))
    (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F)
    {l : Label} {P : MachineData → Prop} {Q : MachineData → MachineData → Prop} {N' : Nat}
    (hle : F + N' ≤ N) (hspec : Spec (Labels.label l) P Q) {Lf : BitVec 64 → Prop}
    (hQ : ∀ m', Q st1.data m' → Saved st1.data m' ∧ SameOutside st1.data.dmem m'.dmem (fun q ↦
      InRange (stackBelow st1.data N') N' q ∨ Lf q ∨ outs q))
    (hLf : ∀ q, Lf q → InRange (stackBelow m0 F) F q)
    (hLs : ∀ p ∈ slots, ∀ i < 8, ¬ Lf (off (stackBelow m0 F) (p.1 + i)))
    {next : Int64} {R : MachineState → Prop}
    (hpc : st1.pc = Labels.label l ∧ retOf st1.data = next) (hP : P st1.data)
    (cont : ∀ st2 : MachineState, st2.pc = next → WFr m0 F N slots outs st2.data →
      Q st1.data st2.data →
      SameOutside st1.data.dmem st2.data.dmem (fun q ↦
        InRange (stackBelow m0 N) N q ∧ ¬ InRange (stackBelow m0 F) (F + 8) q ∨ Lf q ∨ outs q) →
      Eventually (step1 Host.exe) R st2) :
    Eventually (step1 Host.exe) R st1 := by
  have hsp1 : rspOf st1.data = stackBelow m0 F := by rw [hf1.sp, off_zero]
  have hfnw := c.fnw
  refine call_then (env := frameEnv m0 st1.data F [] (fun _ ↦ 0) 0) (l := l) hpc hspec hP
    fun st2 hpc2 hrsp2 hq ↦ ?_
  obtain ⟨hsv, hso⟩ := hQ _ hq
  have hcal : ∀ q, InRange (stackBelow st1.data N') N' q →
      InRange (stackBelow m0 N) N q ∧ ¬ InRange (stackBelow m0 F) (F + 8) q :=
    fun q hq ↦ Transcript.inRange_callee hsp1 c.h8 c.hN hle hq
  have hLr : ∀ j < 8, ¬ Lf (off (stackBelow m0 F) (F + j)) := fun j hj hl ↦ by
    have := hLf _ hl
    unfold NativeRustcVm.NoWrap at hfnw
    rw [Sym.inRange_iff (by omega), toNat_off (by omega)] at this
    omega
  have hf2 : Frame m0 F slots 8 st2.data := by
    refine Frame.call_slots hf1 hsv hrsp2 hso (fun p hp i hi hr ↦ ?_) (fun j hj hr ↦ ?_)
    · have hpF := hsl p hp
      rcases hr with hr | hr | hr
      · exact (hcal _ hr).2 (inRange_off_self (by omega) (by unfold NativeRustcVm.NoWrap at hfnw; omega))
      · exact hLs p hp i hi hr
      · exact c.ofr _ hr (inRange_off_self (by omega) (by unfold NativeRustcVm.NoWrap at hfnw; omega))
    · rcases hr with hr | hr | hr
      · exact (hcal _ hr).2 (inRange_off_self (by omega) (by unfold NativeRustcVm.NoWrap at hfnw; omega))
      · exact hLr j hj hr
      · exact c.ofr _ hr (inRange_off_self (by omega) (by unfold NativeRustcVm.NoWrap at hfnw; omega))
  have hso' : SameOutside st1.data.dmem st2.data.dmem (fun q ↦
      InRange (stackBelow m0 N) N q ∧ ¬ InRange (stackBelow m0 F) (F + 8) q ∨ Lf q ∨ outs q) :=
    SameOutside.mono hso fun q hq ↦ hq.elim (fun h ↦ .inl (hcal q h)) .inr
  refine cont st2 hpc2 ⟨hf2, fun q hq ↦ ?_⟩ hq hso'
  rw [hso' q fun h ↦ hq (h.elim (fun h ↦ .inr h.1) fun h ↦ h.elim
      (fun h ↦ .inr (c.frame_stack (hLf q h))) .inl)]
  exact hso1 q hq

/-- **A block ending in a call, and the call**: from a body state `d`, the block leaves RSP at the
frame's offset `0` and writes the frame below `F` or the outputs; then `call0`. -/
theorem WFr.call (c : TCtx m0 F N t a outs) {d : MachineData} (hw : WFr m0 F N slots outs d)
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    {st1 : MachineState} (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hm : Match (frameEnv m0 d F rest vars ret) S st1.data) (hmid : MidOk F 0 slots S = true)
    (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F)
    (hwr : ∀ q, Written (frameEnv m0 d F rest vars ret) S q →
      InRange (stackBelow m0 F) F q ∨ outs q)
    {l : Label} {P : MachineData → Prop} {Q : MachineData → MachineData → Prop} {N' : Nat}
    (hle : F + N' ≤ N) (hspec : Spec (Labels.label l) P Q) {Lf : BitVec 64 → Prop}
    (hQ : ∀ m', Q st1.data m' → Saved st1.data m' ∧ SameOutside st1.data.dmem m'.dmem (fun q ↦
      InRange (stackBelow st1.data N') N' q ∨ Lf q ∨ outs q))
    (hLf : ∀ q, Lf q → InRange (stackBelow m0 F) F q)
    (hLs : ∀ p ∈ slots, ∀ i < 8, ¬ Lf (off (stackBelow m0 F) (p.1 + i)))
    {next : Int64} {R : MachineState → Prop}
    (hpc : PcOk (frameEnv m0 d F rest vars ret) (.call l) next st1) (hP : P st1.data)
    (cont : ∀ st2 : MachineState, st2.pc = next → WFr m0 F N slots outs st2.data →
      Q st1.data st2.data →
      SameOutside st1.data.dmem st2.data.dmem (fun q ↦
        InRange (stackBelow m0 N) N q ∧ ¬ InRange (stackBelow m0 F) (F + 8) q ∨ Lf q ∨ outs q) →
      Eventually (step1 Host.exe) R st2) :
    Eventually (step1 Host.exe) R st1 :=
  call0 c (Frame.of_block hw.fr hwf hm hmid hsl) (fun q hq ↦ by
    rw [hm.get?_mem0 hwf fun hW ↦ hq ((hwr q hW).elim (fun h ↦ .inr (c.frame_stack h)) .inl)]
    exact hw.same q hq) hsl hle hspec hQ hLf hLs hpc hP cont

/-! ## What a callee gets -/

/-- The callee's stack. -/
theorem TCtx.stackOk (c : TCtx m0 F N t a outs) {d : MachineData} (hk : Kept m0.dmem d.dmem)
    (hsp : rspOf d = stackBelow m0 F) {N' : Nat} (hle : F + N' ≤ N) : StackOk d N' :=
  Transcript.stackOk_callee c.stack hk hsp hle

/-- The round constants, memory changed only in the outputs and the stack. -/
theorem TCtx.rcAt (c : TCtx m0 F N t a outs) {d : MachineData}
    (hs : SameOutside m0.dmem d.dmem (fun q ↦ outs q ∨ InRange (stackBelow m0 N) N q))
    (hsp : rspOf d = stackBelow m0 F) {N' : Nat} (hle : F + N' ≤ N) : RcAt d N' := by
  refine Transcript.RcAt.callee c.rc (Transcript.rc_keep hs fun q hq hr ↦ ?_) hsp c.hN hle
  rcases hq with hq | hq
  · exact c.orc q hq hr
  · exact not_inRange_of_apart c.rc.2.2 c.rc.2.1 (noWrap_stackBelow c.stack) hr
      (Transcript.inRange_mono hq (by omega))

/-- The `TState`'s footprint for the callee. -/
theorem TCtx.tstateOk (c : TCtx m0 F N t a outs) {d : MachineData}
    (hsp : rspOf d = stackBelow m0 F) {N' : Nat} (hle : F + N' ≤ N) : TStateOk d t a N' :=
  Transcript.TStateOk.callee c.tok hsp c.hN hle

/-- An output of the callee in the frame at `ob ≥ 8`. -/
theorem TCtx.localOk (c : TCtx m0 F N t a outs) {d : MachineData} (hk : Kept m0.dmem d.dmem)
    (hsp : rspOf d = stackBelow m0 F) {N' : Nat} (hle : F + N' ≤ N) {ob l : Nat} (hob8 : 8 ≤ ob)
    (hob : ob + l ≤ F) : OutOk d t a (off (stackBelow m0 F) ob) l N' :=
  Transcript.OutOk.frame c.stack hle hsp hk hob8 hob c.tok c.rc

omit [Host] in
theorem AtCall.sp {s : TState} {d : MachineData} (h : AtCall m0 F N slots outs t a s d) :
    rspOf d = stackBelow m0 F := by
  rw [h.fr.sp, off_zero]

/-- The stack holds no byte of the `TState` and the decoded area. -/
theorem TCtx.stack_not_t (c : TCtx m0 F N t a outs) {q : BitVec 64}
    (hq : InRange (stackBelow m0 N) N q) :
    ¬ InRange t tstateBytes q ∧ ¬ InRange a.words (8 * a.len) q :=
  ⟨fun ht ↦ not_inRange_of_apart c.tok.1 c.fp.1.2 (noWrap_stackBelow c.stack) ht
      (Transcript.inRange_mono hq (by omega)),
    fun ha ↦ not_inRange_of_apart c.tok.2.1 c.fp.2.1.2 (noWrap_stackBelow c.stack) ha
      (Transcript.inRange_mono hq (by omega))⟩

omit [Host] in
/-- A frame byte at `x` off the frame's interval `[o, o + l)`. -/
theorem off_not_in {b : BitVec 64} {N x o l : Nat} (hN : b.toNat + N ≤ 2 ^ 64) (hx : x < N)
    (ho : o + l < N) (h : x < o ∨ o + l ≤ x) : ¬ InRange (off b o) l (off b x) := by
  intro hq
  rw [Sym.inRange_iff (by rw [toNat_off (by omega)]; omega), toNat_off (by omega),
    toNat_off (by omega)] at hq
  omega

/-- **`read_scalar`** into the frame at `ob`, from a state before the call: the scalar (or the
tag `0`) there, the next `TState` at `t`, the callee-saved registers kept, memory changed in the
stack below the frame, the output and the `TState`. -/
theorem AtCall.readScalar (c : TCtx m0 F N t a outs)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    {s : TState} {st1 : MachineState} (h1 : AtCall m0 F N slots outs t a s st1.data)
    (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F) (hle : F + readScalarStack ≤ N) {ob : Nat} (hob8 : 8 ≤ ob)
    (hob : ob + 24 ≤ F) (hobs : ∀ p ∈ slots, ob + 24 ≤ p.1)
    (hrdi : reg st1.data .rdi = off (stackBelow m0 F) ob) (hrsi : reg st1.data .rsi = t)
    {next : Int64} {R : MachineState → Prop}
    (hpc : st1.pc = Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel ∧ retOf st1.data = next)
    (cont : ∀ st2 : MachineState, st2.pc = next → WFr m0 F N slots outs st2.data →
      OptEWAt st2.data.dmem (off (stackBelow m0 F) ob) ((readScalar.run s).map (·.1)) →
      NextAt st2.data.dmem t a (readScalar.run s) →
      (∀ r, calleeSaved r = true → reg st2.data r = reg st1.data r) →
      SameOutside st1.data.dmem st2.data.dmem (fun q ↦ (InRange (stackBelow m0 N) N q ∧
        ¬ InRange (stackBelow m0 F) (F + 8) q) ∨ InRange (off (stackBelow m0 F) ob) 24 q ∨
        InRange t tstateBytes q) →
      Eventually (step1 Host.exe) R st2) :
    Eventually (step1 Host.exe) R st1 := by
  have hsp := h1.sp
  have hfnw' : (stackBelow m0 F).toNat + (F + 8) ≤ 2 ^ 64 := c.fnw
  have hcal := fun {q : BitVec 64} (hq : InRange (stackBelow st1.data readScalarStack)
    readScalarStack q) ↦ Transcript.inRange_callee hsp c.h8 c.hN hle hq
  refine call0 c h1.fr h1.same hsl hle (hrs s) (Lf := InRange (off (stackBelow m0 F) ob) 24)
    (fun m' hq ↦ ⟨hq.2.2.2, SameOutside.mono hq.2.2.1 fun q hq ↦ ?_⟩)
    (fun q hq ↦ Transcript.inRange_of_off (N := F) (by unfold NativeRustcVm.NoWrap; omega) hob hq)
    (fun p hp i hi ↦ off_not_in (N := F + 8) hfnw' (by have := hsl p hp; omega) (by omega)
      (by have := hobs p hp; omega)) hpc ?_ fun st2 hpc2 hw2 hq _ ↦ ?_
  · rcases hq with h | h | h
    · exact .inr (.inl (by rwa [hrdi] at h))
    · exact .inr (.inr (c.ot q (by rwa [hrsi] at h)))
    · exact .inl h
  · unfold ReadScalarPre
    rw [hrsi, hrdi]
    exact ⟨c.stackOk h1.fr.kept hsp hle, c.rcAt h1.same hsp hle, h1.ts, c.tstateOk hsp hle,
      c.localOk h1.fr.kept hsp hle hob8 hob, by
        apply c.got_callee h1.same hsp hle
        intro ar har
        simp only [List.mem_cons, List.not_mem_nil, or_false] at har
        rcases har with rfl | rfl | rfl | rfl
        · exact ⟨(t, tstateBytes), by simp, le_rfl, le_rfl⟩
        · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
        · exact c.got_local hob
        · exact ⟨(rcAddr, 192), by simp, le_rfl, le_rfl⟩⟩
  · obtain ⟨hopt, hnext, hso, hsv⟩ := hq
    rw [hrdi] at hopt
    rw [hrsi] at hnext
    refine cont st2 hpc2 hw2 hopt hnext hsv.1 (SameOutside.mono hso fun q hq ↦ ?_)
    rcases hq with h | h | h
    · exact .inr (.inl (by rwa [hrdi] at h))
    · exact .inr (.inr (by rwa [hrsi] at h))
    · exact .inl (hcal h)

/-- **`grind`** of `bits`, from a state before the call: AL its result, the next `TState` at
`t`, the callee-saved registers kept, memory changed in the stack below the frame and the
`TState`. -/
theorem AtCall.grind (c : TCtx m0 F N t a outs)
    (hgr : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    {s : TState} {st1 : MachineState} (h1 : AtCall m0 F N slots outs t a s st1.data)
    (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F) (hle : F + grindStack ≤ N) (hrdi : reg st1.data .rdi = t)
    {bits : Nat} (hbits : grindBits st1.data = bits) (hb : bits < 64)
    {next : Int64} {R : MachineState → Prop}
    (hpc : st1.pc = Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel ∧ retOf st1.data = next)
    (cont : ∀ st2 : MachineState, st2.pc = next → WFr m0 F N slots outs st2.data →
      OkAl st2.data ((NativeVm.Model.grind bits).run s).isSome →
      NextAt st2.data.dmem t a ((NativeVm.Model.grind bits).run s) →
      (∀ r, calleeSaved r = true → reg st2.data r = reg st1.data r) →
      SameOutside st1.data.dmem st2.data.dmem (fun q ↦ (InRange (stackBelow m0 N) N q ∧
        ¬ InRange (stackBelow m0 F) (F + 8) q) ∨ InRange t tstateBytes q) →
      Eventually (step1 Host.exe) R st2) :
    Eventually (step1 Host.exe) R st1 := by
  have hsp := h1.sp
  have hcal := fun {q : BitVec 64} (hq : InRange (stackBelow st1.data grindStack)
    grindStack q) ↦ Transcript.inRange_callee hsp c.h8 c.hN hle hq
  refine call0 c h1.fr h1.same hsl hle (hgr s) (Lf := fun _ ↦ False)
    (fun m' hq ↦ ⟨hq.2.2.2, SameOutside.mono hq.2.2.1 fun q hq ↦ ?_⟩)
    (fun _ h ↦ h.elim) (fun _ _ _ _ h ↦ h) hpc ?_ fun st2 hpc2 hw2 hq _ ↦ ?_
  · rcases hq with h | h
    · exact .inr (.inr (c.ot q (by rwa [hrdi] at h)))
    · exact .inl h
  · unfold GrindPre
    rw [hrdi, hbits]
    exact ⟨c.stackOk h1.fr.kept hsp hle, c.rcAt h1.same hsp hle, h1.ts, c.tstateOk hsp hle, hb,
      c.got_callee h1.same hsp hle (fun ar har => ⟨ar, by simp [har], le_rfl, le_rfl⟩)⟩
  · obtain ⟨hok, hnext, hso, hsv⟩ := hq
    rw [hbits] at hok hnext
    rw [hrdi] at hnext
    refine cont st2 hpc2 hw2 hok hnext hsv.1 (SameOutside.mono hso fun q hq ↦ ?_)
    rcases hq with h | h
    · exact .inr (by rwa [hrdi] at h)
    · exact .inl (hcal h)

/-- **`SpongeW::squeeze` on the `TState`'s sponge**, from a state before the call: the
challenge `(sq s).1` in RAX, RDX, the `TState` then `(sq s).2`, the callee-saved registers kept,
memory changed in the stack below the frame and the `TState`. -/
theorem AtCall.squeeze (c : TCtx m0 F N t a outs)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {s : TState} {st1 : MachineState} (h1 : AtCall m0 F N slots outs t a s st1.data)
    (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F) (hle : F + squeezeStack ≤ N) (hrdi : reg st1.data .rdi = t)
    {next : Int64} {R : MachineState → Prop}
    (hpc : st1.pc = Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel ∧ retOf st1.data = next)
    (cont : ∀ st2 : MachineState, st2.pc = next → WFr m0 F N slots outs st2.data →
      TStateAt st2.data.dmem t a (NativeRustcVm.Whir.sq s).2 →
      reg st2.data .rax = (NativeRustcVm.Whir.sq s).1.c0.toBitVec →
      reg st2.data .rdx = (NativeRustcVm.Whir.sq s).1.c1.toBitVec →
      (∀ r, calleeSaved r = true → reg st2.data r = reg st1.data r) →
      SameOutside st1.data.dmem st2.data.dmem (fun q ↦ (InRange (stackBelow m0 N) N q ∧
        ¬ InRange (stackBelow m0 F) (F + 8) q) ∨ InRange t tstateBytes q) →
      Eventually (step1 Host.exe) R st2) :
    Eventually (step1 Host.exe) R st1 := by
  have hsp := h1.sp
  have hcal := fun {q : BitVec 64} (hq : InRange (stackBelow st1.data squeezeStack)
    squeezeStack q) ↦ Transcript.inRange_callee hsp c.h8 c.hN hle hq
  have hTn : t.toNat + 760 ≤ 2 ^ 64 := c.fp.1.2
  have hT328 : ∀ q, InRange t spongeBytes q → InRange t tstateBytes q :=
    fun q hq ↦ Transcript.inRange_mono hq (by simp only [spongeBytes, tstateBytes]; omega)
  refine call0 c h1.fr h1.same hsl hle (hsq s.sponge) (Lf := fun _ ↦ False)
    (fun m' hq ↦ ⟨hq.2.2.2.2, SameOutside.mono hq.2.2.2.1 fun q hq ↦ ?_⟩)
    (fun _ h ↦ h.elim) (fun _ _ _ _ h ↦ h) hpc ?_ fun st2 hpc2 hw2 hq _ ↦ ?_
  · rcases hq with h | h
    · exact .inr (.inr (c.ot q (hT328 q (by rwa [hrdi] at h))))
    · exact .inl h
  · have htok := c.tstateOk hsp hle
    have h1' : t.toNat + 760 ≤ (stackBelow st1.data squeezeStack).toNat ∨
        (stackBelow st1.data squeezeStack).toNat + (squeezeStack + 8) ≤ t.toNat := htok.1
    have h2 : t.toNat + 760 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ t.toNat := htok.2.2
    unfold SqueezePre
    rw [hrdi]
    refine ⟨c.stackOk h1.fr.kept hsp hle, c.rcAt h1.same hsp hle,
      ⟨fun j hj ↦ h1.ts.footprint.1.1 j (by simp only [spongeBytes] at hj; show j < 760; omega),
        ?_, ?_, ?_⟩, h1.ts.sponge, ?_⟩
    · show t.toNat + 328 ≤ 2 ^ 64; omega
    · show t.toNat + 328 ≤ _ ∨ _ ≤ t.toNat; omega
    · show t.toNat + 328 ≤ _ ∨ _ ≤ t.toNat; omega
    · apply c.got_callee h1.same hsp hle
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl
      · exact ⟨(t, tstateBytes), by simp, le_rfl, by
          change t.toNat + 328 ≤ t.toNat + 760; omega⟩
      · exact ⟨(rcAddr, 192), by simp, le_rfl, le_rfl⟩
  · obtain ⟨hc0, hc1, hsp2, hs2, hsv2⟩ := hq
    rw [hrdi] at hsp2 hs2
    have hts2 : TStateAt st2.data.dmem t a (NativeRustcVm.Whir.sq s).2 := by
      refine h1.ts.with_sponge hsv2.2 (fun q hq ↦ c.stack_not_t (hcal hq).1)
        (fun q hq ↦ hs2 q ?_) hsp2
      rintro (hq' | hq')
      · obtain ⟨j, hj, hw', rfl⟩ := touch_of_inRange (o := 0) (n := 328)
          (hTn : NativeRustcVm.NoWrap t 760) (by decide) (by rwa [off_zero])
        exact hq (Or.inl ⟨j, hj, hw'.2, rfl⟩)
      · exact hq (Or.inr hq')
    refine cont st2 hpc2 hw2 hts2 hc0 hc1 hsv2.1 (SameOutside.mono hs2 fun q hq ↦ ?_)
    rcases hq with h | h
    · exact .inr (hT328 q h)
    · exact .inl (hcal h)

/-- **`EW::mul`**, from a state before the call: the product in RAX, RDX, the `TState` kept,
the callee-saved registers kept, memory changed in the stack below the frame. -/
theorem AtCall.ewMul (c : TCtx m0 F N t a outs)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {s : TState} {st1 : MachineState} (h1 : AtCall m0 F N slots outs t a s st1.data)
    (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F) (hle : F + ewMulStack ≤ N)
    {next : Int64} {R : MachineState → Prop}
    (hpc : st1.pc = Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel ∧ retOf st1.data = next)
    (cont : ∀ st2 : MachineState, st2.pc = next → WFr m0 F N slots outs st2.data →
      TStateAt st2.data.dmem t a s →
      reg st2.data .rax = (EW.mul ⟨.ofBitVec (reg st1.data .rdi), .ofBitVec (reg st1.data .rsi)⟩
        ⟨.ofBitVec (reg st1.data .rdx), .ofBitVec (reg st1.data .rcx)⟩).c0.toBitVec →
      reg st2.data .rdx = (EW.mul ⟨.ofBitVec (reg st1.data .rdi), .ofBitVec (reg st1.data .rsi)⟩
        ⟨.ofBitVec (reg st1.data .rdx), .ofBitVec (reg st1.data .rcx)⟩).c1.toBitVec →
      (∀ r, calleeSaved r = true → reg st2.data r = reg st1.data r) →
      SameOutside st1.data.dmem st2.data.dmem (fun q ↦ InRange (stackBelow m0 N) N q ∧
        ¬ InRange (stackBelow m0 F) (F + 8) q) →
      Eventually (step1 Host.exe) R st2) :
    Eventually (step1 Host.exe) R st1 := by
  have hsp := h1.sp
  have hcal := fun {q : BitVec 64} (hq : InRange (stackBelow st1.data ewMulStack)
    ewMulStack q) ↦ Transcript.inRange_callee hsp c.h8 c.hN hle hq
  refine call0 c h1.fr h1.same hsl hle hmul (Lf := fun _ ↦ False)
    (fun m' hq ↦ ⟨hq.2.2.2, SameOutside.mono hq.2.2.1 fun q hq ↦ .inl hq⟩)
    (fun _ h ↦ h.elim) (fun _ _ _ _ h ↦ h) hpc (c.stackOk h1.fr.kept hsp hle)
    fun st2 hpc2 hw2 hq _ ↦ ?_
  obtain ⟨hc0, hc1, hso, hsv⟩ := hq
  refine cont st2 hpc2 hw2 (h1.ts.frame hsv.2 (fun q hq ↦ c.stack_not_t (hcal hq).1) hso) hc0 hc1
    hsv.1 (SameOutside.mono hso fun q hq ↦ hcal hq)

end

end

end NativeRustcVmX64.Whir
