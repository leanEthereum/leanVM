module

public import NativeRustcVmX64.Whir.SampleQueries.Exec
public import NativeRustcVmX64.Transcript.Callee
public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Spec.Whir
public import NativeRustcVm.Whir.Sample
public import NativeRustcVm.Whir.Per
public import NativeRustcVm.Transcript.Update
public import NativeRustcVmX64.Code.Vm.QueryBits.Names
public import NativeRustcVmX64.Got
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names

/-!
# `sample_queries` on x86-64: its states and what every step shares

From the entry `m0` (the `TState` RDI, the depth RSI, the count RDX, the buffer RCX): the frame
`fb m0` (128 bytes below RSP), the bytes the function may change (`Outs`: the buffer, the
`TState`, its stack), what every state between blocks keeps (`Ctx`: the frame with RSP at its
offset `8`, the buffer's address in its word `72`, the depth in R13, memory changed only in
`Outs`), and the loop heads: the outer loop's `NativeRustcVmX64.Vm.SampleQueries.label_3` (`Outer`), `b9` (`AtB9`), the
inner loop's `NativeRustcVmX64.Vm.SampleQueries.label_6` (`Inner`), the squeezes' loop for a depth above `128` (`Big`).
Then the facts a block keeps (`Ctx.block`, `loc_keep`, `loc_write`) and the two calls
(`squeeze_call`, `qb_call`).
-/

namespace NativeRustcVmX64.Whir.SampleQueries

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.SampleQueries
open NativeRustcVmX64.Transcript (Frame frameEnv Slots ProOk MidOk EpiOk writesIn)
open NativeRustcVm (BufWordsAt WordsAt WordAt)

@[expose] public section

/-- The `TState`. -/
abbrev tA (m0 : MachineData) : BitVec 64 := reg m0 .rdi
/-- The buffer. -/
abbrev oA (m0 : MachineData) : BitVec 64 := reg m0 .rcx
/-- The depth. -/
abbrev dep (m0 : MachineData) : Nat := (reg m0 .rsi).toNat
/-- The count. -/
abbrev cnt (m0 : MachineData) : Nat := (reg m0 .rdx).toNat
/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 128
/-- A chunk's size. -/
abbrev nOf (m0 : MachineData) (r : Nat) : Nat := min (128 / dep m0) r

/-- What the function may change: the buffer, the `TState`, its stack. -/
def Outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (oA m0) queryBufBytes q ∨ InRange (tA m0) tstateBytes q ∨
    InRange (stackBelow m0 sampleQueriesStack) sampleQueriesStack q

/-- **Between blocks**: the frame, RSP at its offset `8`; the buffer's address in the frame's
word `72`; the depth in R13; memory changed only in `Outs`. -/
structure Ctx (m0 st : MachineData) : Prop where
  fr : Frame m0 128 slots 8 st
  out : WordAt st.dmem (off (fb m0) 72) (UInt64.ofBitVec (oA m0))
  same : SameOutside m0.dmem st.dmem (Outs m0)
  r13 : reg st .r13 = reg m0 .rsi

section
variable [Labels]

/-- **The outer loop's head** `NativeRustcVmX64.Vm.SampleQueries.label_3`, after `j` challenges, `r` positions left, the
`TState` `s`, the positions `qs`. -/
structure Outer (a : DecArea) (s0 : TState) (m0 : MachineData) (j r : Nat) (s : TState)
    (qs : List UInt64) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  tw : WordAt st.dmem (off (fb m0) 24) (UInt64.ofBitVec (tA m0))
  rax : (reg st .rax).toNat = r
  rbx : reg st .rbx = tA m0
  r15 : (reg st .r15).toNat = j
  r14 : (reg st .r14).toNat = cnt m0
  r12 : reg st .r12 = rodataAddr .perChallenge
  rbp : (reg st .rbp).toNat = qs.length
  jlt : j < cnt m0
  len : qs.length + r = cnt m0
  dlt : dep m0 < 129
  ts : TStateAt st.dmem (tA m0) a s
  buf : BufWordsAt st.dmem (oA m0) queryCap qs
  model : auxP (dep m0) (cnt m0) (cnt m0) s0 =
    (qs.toArray ++ (auxP (dep m0) (cnt m0 - j) r s).1, (auxP (dep m0) (cnt m0 - j) r s).2)

/-- **At `b9`**: the `j`th challenge's `n` positions pushed, `r` positions left before them, the
`TState` `s` after the challenge, the positions `qs` with them. -/
structure AtB9 (a : DecArea) (s0 : TState) (m0 : MachineData) (j r n : Nat) (s : TState)
    (qs : List UInt64) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  tw : WordAt st.dmem (off (fb m0) 24) (UInt64.ofBitVec (tA m0))
  rax : (reg st .rax).toNat = r
  rcx : (reg st .rcx).toNat = n
  rbx : reg st .rbx = tA m0
  r15 : (reg st .r15).toNat = j
  r14 : (reg st .r14).toNat = cnt m0
  r12 : reg st .r12 = rodataAddr .perChallenge
  rbp : (reg st .rbp).toNat = qs.length
  jlt : j < cnt m0
  nle : n ≤ r
  len : qs.length + (r - n) = cnt m0
  dlt : dep m0 < 129
  ts : TStateAt st.dmem (tA m0) a s
  buf : BufWordsAt st.dmem (oA m0) queryCap qs
  model : auxP (dep m0) (cnt m0) (cnt m0) s0 =
    (qs.toArray ++ (auxP (dep m0) (cnt m0 - (j + 1)) (r - n) s).1,
      (auxP (dep m0) (cnt m0 - (j + 1)) (r - n) s).2)

/-- **The inner loop's head** `NativeRustcVmX64.Vm.SampleQueries.label_6`: the `j`th challenge `(sq s).1`, `i` of its
`n` positions pushed after `qs`. -/
structure Inner (a : DecArea) (s0 : TState) (m0 : MachineData) (j r : Nat) (s : TState)
    (qs : List UInt64) (i : Nat) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  tw : WordAt st.dmem (off (fb m0) 24) (UInt64.ofBitVec (tA m0))
  l16 : WordAt st.dmem (off (fb m0) 16) r.toUInt64
  l32 : WordAt st.dmem (off (fb m0) 32) j.toUInt64
  l40 : WordAt st.dmem (off (fb m0) 40) (8 * nOf m0 r).toUInt64
  l48 : WordAt st.dmem (off (fb m0) 48)
    (UInt64.ofBitVec (BitVec.ofNat 64 (8 * qs.length) - BitVec.ofNat 64 1840))
  l56 : WordAt st.dmem (off (fb m0) 56) (sq s).1.c1
  l64 : WordAt st.dmem (off (fb m0) 64) (sq s).1.c0
  rcx : (reg st .rcx).toNat = nOf m0 r
  r12 : reg st .r12 = 0#64 - BitVec.ofNat 64 (8 * i)
  r14 : (reg st .r14).toNat = cnt m0
  r15 : reg st .r15 = BitVec.ofNat 64 (i * dep m0)
  rbp : (reg st .rbp).toNat = qs.length + i + 1
  jlt : j < cnt m0
  len : qs.length + r = cnt m0
  r0 : r ≠ 0
  dpos : 0 < dep m0
  dle : dep m0 ≤ 128
  ilt : i < nOf m0 r
  ts : TStateAt st.dmem (tA m0) a (sq s).2
  buf : BufWordsAt st.dmem (oA m0) queryCap (qs ++ (chunk (dep m0) (sq s).1 (nOf m0 r)).toList.take i)
  model : auxP (dep m0) (cnt m0) (cnt m0) s0 =
    (qs.toArray ++ (auxP (dep m0) (cnt m0 - j) r s).1, (auxP (dep m0) (cnt m0 - j) r s).2)

/-- **The squeezes' loop head** `NativeRustcVmX64.Vm.SampleQueries.label_11` (a depth above `128`), `j` squeezes done. -/
structure Big (a : DecArea) (s0 : TState) (m0 : MachineData) (j : Nat) (s : TState)
    (st : MachineData) : Prop where
  ctx : Ctx m0 st
  rbx : reg st .rbx = tA m0
  r14 : (reg st .r14).toNat = cnt m0 - j
  jlt : j < cnt m0
  dge : 129 ≤ dep m0
  ts : TStateAt st.dmem (tA m0) a s
  buf : WordAt st.dmem (oA m0) 0
  model : auxP (dep m0) (cnt m0) (cnt m0) s0 = auxP (dep m0) (cnt m0 - j) (cnt m0) s

/-- `sample_queries`' postcondition, reached. -/
abbrev Post (a : DecArea) (s0 : TState) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ SampleQueriesPost a s0 m0 st.data

end

end

public section

theorem N_eq : sampleQueriesStack = 128 + squeezeStack := rfl
theorem N_ge : 128 ≤ sampleQueriesStack := by rw [N_eq]; omega
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 128 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide
theorem qbb_eq : queryBufBytes = 1848 := rfl

/-! ## The literal facts -/

theorem wrote_spec {S : SState} {r o : Nat} {v : Sym} (h : wrote S r o v = true) :
    ∀ t < 8, findWrite r (o + t) S.mem = some (v, t) := by
  intro t ht
  unfold wrote at h
  rw [List.all_eq_true] at h
  simpa using h t (List.mem_range.mpr ht)

theorem kept_spec {S : SState} {rs : List Reg64} (h : kept S rs = true) {r : Reg64} (hr : r ∈ rs) :
    S.reg r = some (.reg r) := by
  unfold kept at h
  rw [List.all_eq_true] at h
  simpa using h r hr

theorem wr0_spec {S : SState} {L : Nat} (h : wr0 S L = true) : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ L := by
  intro w hw
  unfold wr0 at h
  rw [List.all_eq_true] at h
  simpa using h w hw

theorem miss_spec {S : SState} {o : Nat} (h : miss S o = true) :
    ∀ w ∈ S.mem, w.r = 0 → w.off + w.n ≤ o ∨ o + 8 ≤ w.off := by
  intro w hw hr
  unfold miss at h
  rw [List.all_eq_true] at h
  have := h w hw
  simp only [hr, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at this
  exact this

theorem midOk_writesIn {F o : Nat} {sl : Slots} {S : SState} (h : MidOk F o sl S = true) :
    writesIn S = true := by
  simp only [MidOk, Bool.and_eq_true] at h
  exact h.1.1.2

theorem miss_nil {S : SState} (h : S.mem = []) (o : Nat) : miss S o = true := by
  unfold miss; rw [h]; rfl

theorem wr0_nil {S : SState} (h : S.mem = []) (L : Nat) : wr0 S L = true := by
  unfold wr0; rw [h]; rfl

theorem miss_of_wr0 {S : SState} {L : Nat} (h : wr0 S L = true) {o : Nat} (ho : L ≤ o) :
    miss S o = true := by
  unfold miss
  rw [List.all_eq_true]
  intro w hwm
  have := wr0_spec h w hwm
  simp only [this.1, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq]
  omega

/-- `movb $1, %al`: AL is `1`. -/
theorem al_one (x : BitVec 64) : (BinOp.apply .merge .W8 x (BitVec.ofNat 64 1)).toNat % 256 = 1 := by
  have : low .W8 (x.replaceLow (low .W8 (BitVec.ofNat 64 1))) = low .W8 (BitVec.ofNat 64 1) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hi8 : i < 8 := hi
    simp only [low, BitVec.replaceLow, BitVec.getLsbD_setWidth]
    change (decide (i < 8) && (decide (i < 64) && ((x.drop 8) ++ low .W8 (BitVec.ofNat 64 1)).getLsbD i)) = _
    rw [BitVec.getLsbD_append]
    simp [hi8, show i < 64 by omega]
  have h2 := congrArg BitVec.toNat this
  rw [toNat_low] at h2
  exact h2.trans (by decide)

/-! ## The entry's ranges -/

section
variable [Labels] {a : DecArea} {s0 : TState} {m0 : MachineData}

theorem pre_S (h : SampleQueriesPre a s0 m0) : StackOk m0 sampleQueriesStack := h.1.1
theorem pre_rc (h : SampleQueriesPre a s0 m0) : RcAt m0 sampleQueriesStack := h.1.2.1
theorem pre_ro (h : SampleQueriesPre a s0 m0) : RodataAt m0 sampleQueriesStack := h.1.2.2.1
theorem pre_tok (h : SampleQueriesPre a s0 m0) : TStateOk m0 (tA m0) a sampleQueriesStack :=
  h.1.2.2.2.1
theorem pre_ts (h : SampleQueriesPre a s0 m0) : TStateAt m0.dmem (tA m0) a s0 := h.2.1
theorem pre_cnt (h : SampleQueriesPre a s0 m0) : cnt m0 ≤ 230 := h.2.2.1
theorem pre_out (h : SampleQueriesPre a s0 m0) :
    OutOk m0 (tA m0) a (oA m0) queryBufBytes sampleQueriesStack := h.2.2.2.1.1
theorem pre_oro (h : SampleQueriesPre a s0 m0) : RodataApart (oA m0) queryBufBytes := h.2.2.2.1.2

theorem pre_hn (h : SampleQueriesPre a s0 m0) : sampleQueriesStack ≤ (rspOf m0).toNat := (pre_S h).1
theorem pre_h8 (h : SampleQueriesPre a s0 m0) : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := (pre_S h).2.1

theorem fb_toNat (h : SampleQueriesPre a s0 m0) : (fb m0).toNat = (rspOf m0).toNat - 128 :=
  stackBelow_toNat (by have := pre_hn h; have := N_ge; omega)

theorem fb_noWrap (h : SampleQueriesPre a s0 m0) : NativeRustcVm.NoWrap (fb m0) (128 + 8) :=
  Transcript.frame_noWrap (pre_S h) (by decide)

/-- The frame's bytes below its return address are the stack's. -/
theorem frame_stack (h : SampleQueriesPre a s0 m0) {L : Nat} (hL : L ≤ 128) {q : BitVec 64}
    (hq : InRange (fb m0) L q) : InRange (stackBelow m0 sampleQueriesStack) sampleQueriesStack q :=
  Transcript.inRange_frame_stack (pre_h8 h) (pre_hn h) N_ge
    (Transcript.inRange_mono hq hL)

theorem frame_outs (h : SampleQueriesPre a s0 m0) {L : Nat} (hL : L ≤ 128) {q : BitVec 64}
    (hq : InRange (fb m0) L q) : Outs m0 q := .inr (.inr (frame_stack h hL hq))

/-- The `TState` and the decoded area hold no byte of the frame. -/
theorem frame_not_t (h : SampleQueriesPre a s0 m0) {q : BitVec 64} (hq : InRange (fb m0) (128 + 8) q) :
    ¬ InRange (tA m0) tstateBytes q ∧ ¬ InRange a.words (8 * a.len) q := by
  have hfp := (pre_ts h).footprint
  have h1 := Transcript.apart_frame (pre_tok h).1 (pre_hn h) N_ge
  have h2 := Transcript.apart_frame (pre_tok h).2.1 (pre_hn h) N_ge
  exact ⟨fun ht ↦ not_inRange_of_apart h1 hfp.1.2 (fb_noWrap h) ht hq,
    fun ha ↦ not_inRange_of_apart h2 hfp.2.1.2 (fb_noWrap h) ha hq⟩

theorem frame_not_o (h : SampleQueriesPre a s0 m0) {q : BitVec 64} (hq : InRange (fb m0) (128 + 8) q) :
    ¬ InRange (oA m0) queryBufBytes q := by
  have h1 := Transcript.apart_frame (pre_out h).2.2.2.2.1 (pre_hn h) N_ge
  exact fun ho ↦ not_inRange_of_apart h1 (pre_out h).2.1 (fb_noWrap h) ho hq

/-- The stack holds no byte of the `TState` and the decoded area. -/
theorem stack_not_t (h : SampleQueriesPre a s0 m0) {q : BitVec 64}
    (hq : InRange (stackBelow m0 sampleQueriesStack) sampleQueriesStack q) :
    ¬ InRange (tA m0) tstateBytes q ∧ ¬ InRange a.words (8 * a.len) q := by
  have hfp := (pre_ts h).footprint
  have hs := noWrap_stackBelow (pre_S h)
  exact ⟨fun ht ↦ not_inRange_of_apart (pre_tok h).1 hfp.1.2 hs ht (Transcript.inRange_mono hq (by omega)),
    fun ha ↦ not_inRange_of_apart (pre_tok h).2.1 hfp.2.1.2 hs ha (Transcript.inRange_mono hq (by omega))⟩

theorem stack_not_o (h : SampleQueriesPre a s0 m0) {q : BitVec 64}
    (hq : InRange (stackBelow m0 sampleQueriesStack) sampleQueriesStack q) :
    ¬ InRange (oA m0) queryBufBytes q := fun ho ↦
  not_inRange_of_apart (pre_out h).2.2.2.2.1 (pre_out h).2.1 (noWrap_stackBelow (pre_S h)) ho
    (Transcript.inRange_mono hq (by omega))

theorem o_not_t (h : SampleQueriesPre a s0 m0) {q : BitVec 64} (hq : InRange (oA m0) queryBufBytes q) :
    ¬ InRange (tA m0) tstateBytes q ∧ ¬ InRange a.words (8 * a.len) q :=
  ⟨not_inRange_of_apart (pre_out h).2.2.1 (pre_out h).2.1 (pre_ts h).footprint.1.2 hq,
    not_inRange_of_apart (pre_out h).2.2.2.1 (pre_out h).2.1 (pre_ts h).footprint.2.1.2 hq⟩

/-! ## Memory kept -/

/-- **The buffer kept** where memory changed apart from it. -/
theorem buf_keep (h : SampleQueriesPre a s0 m0) {d d' : DataMem} {R : BitVec 64 → Prop}
    {qs : List UInt64} (hb : BufWordsAt d (oA m0) queryCap qs) (hs : SameOutside d d' R)
    (hR : ∀ q, R q → ¬ InRange (oA m0) queryBufBytes q) : BufWordsAt d' (oA m0) queryCap qs := by
  have hnw : (oA m0).toNat + 1848 ≤ 2 ^ 64 := (pre_out h).2.1
  obtain ⟨hl, hw, hws⟩ := hb
  have hl' : qs.length ≤ 230 := hl
  refine ⟨hl, NativeRustcVm.BytesAt.of_sameOutside hw hs fun i hi hq ↦ hR _ hq ?_,
    NativeRustcVm.BytesAt.of_sameOutside hws hs fun i hi hq ↦ hR _ hq ?_⟩
  · have hi' : i < 8 := hi
    exact inRange_off_self (b := oA m0) (j := i) (N := 1848) (by omega) (by omega)
  · rw [length_flatMap_wordBytes] at hi
    have := inRange_off_self (b := oA m0) (j := 8 + i) (N := 1848) (by omega) (by omega)
    rwa [← off_add] at this

theorem wordAt0_keep (h : SampleQueriesPre a s0 m0) {d d' : DataMem} {R : BitVec 64 → Prop}
    (hb : WordAt d (oA m0) 0) (hs : SameOutside d d' R)
    (hR : ∀ q, R q → ¬ InRange (oA m0) queryBufBytes q) : WordAt d' (oA m0) 0 := by
  have hnw : (oA m0).toNat + 1848 ≤ 2 ^ 64 := (pre_out h).2.1
  exact NativeRustcVm.BytesAt.of_sameOutside hb hs fun i hi hq ↦ hR _ hq
    (inRange_off_self (b := oA m0) (j := i) (N := 1848) (by have : i < 8 := hi; omega) (by omega))

theorem same_trans (h : SampleQueriesPre a s0 m0) {d d' : MachineData} {R : BitVec 64 → Prop}
    (h1 : SameOutside m0.dmem d.dmem (Outs m0)) (h2 : SameOutside d.dmem d'.dmem R)
    (hR : ∀ q, R q → Outs m0 q) : SameOutside m0.dmem d'.dmem (Outs m0) := by
  have _ := h
  exact fun q hq ↦ (h2 q fun h ↦ hq (hR q h)).trans (h1 q hq)

end

/-! ## A block -/

section
variable [Labels] {m0 st st' : MachineData} {rest : List (BitVec 64 × Nat)}
  {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}

/-- **A frame word kept** by a block whose writes miss it. -/
theorem loc_keep (hwf : (frameEnv m0 st 128 rest vars ret).WF)
    (hm : Match (frameEnv m0 st 128 rest vars ret) S st') (hin : writesIn S = true) {o : Nat}
    (ho : o + 8 ≤ 136) (hmiss : miss S o = true) {w : UInt64}
    (h : WordAt st.dmem (off (fb m0) o) w) : WordAt st'.dmem (off (fb m0) o) w := by
  have hmi := miss_spec hmiss
  refine fun i hi ↦ ?_
  have hi' : i < 8 := hi
  rw [off_add, hm.get?_mem0 hwf (Transcript.not_written0 hwf hm hin (j := o + i) (by omega)
    fun w hw hr ↦ by have := hmi w hw hr; omega), ← off_add]
  exact h i hi

/-- **A frame word a block wrote.** -/
theorem loc_write (hm : Match (frameEnv m0 st 128 rest vars ret) S st') {o : Nat} (ho : o + 8 ≤ 136)
    {v : Sym} (hw : wrote S 0 o v = true) :
    WordAt st'.dmem (off (fb m0) o) (UInt64.ofBitVec (v.eval (frameEnv m0 st 128 rest vars ret))) :=
  Transcript.wordAt_write hm (r := 0) rfl ho (wrote_spec hw)

omit [Labels] in
/-- A frame word, loaded. -/
theorem loc_load {o : Nat} {w : UInt64} (h : WordAt st.dmem (off (fb m0) o) w) :
    (frameEnv m0 st 128 rest vars ret).load 0 o 8 = w.toBitVec :=
  Transcript.load_ofMachine rfl h

/-- A register a block kept. -/
theorem reg_kept (hm : Match (frameEnv m0 st 128 rest vars ret) S st') {r : Reg64}
    (h : S.reg r = some (.reg r)) : reg st' r = reg st r :=
  hm.regs r _ h

/-- The middle state of a frame. -/
theorem mid_match {o : Nat} (hf : Frame m0 128 slots o st) :
    Match (frameEnv m0 st 128 [] vars ret) (init [136] [(.rsp, .ptr 0 (o : Int))]) st :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial

theorem mid_wf {a : DecArea} {s0 : TState} (h : SampleQueriesPre a s0 m0) (hk : Kept m0.dmem st.dmem) :
    (frameEnv m0 st 128 [] vars ret).WF :=
  Transcript.frame_wf ⟨Mapped.keeps (Transcript.frame_mapped (pre_S h) (by decide)) hk, fb_noWrap h⟩
    (by simp) (List.pairwise_singleton _ _)

/-- **A block writing the frame below `L`** keeps the memory outside it. -/
theorem block_same (hwf : (frameEnv m0 st 128 [] vars ret).WF)
    (hm : Match (frameEnv m0 st 128 [] vars ret) S st') {L : Nat} (hL : L ≤ 136)
    (hw : wr0 S L = true) : SameOutside st.dmem st'.dmem (InRange (fb m0) L) :=
  Transcript.sameOutside_low hwf hm (r := 0) rfl hL (wr0_spec hw)

/-- **A block** keeps the context, its writes in the frame below `L ≤ 72`. -/
theorem Ctx.blockW {a : DecArea} {s0 : TState} (h : SampleQueriesPre a s0 m0) (hc : Ctx m0 st)
    (hwf : (frameEnv m0 st 128 rest vars ret).WF)
    (hm : Match (frameEnv m0 st 128 rest vars ret) S st') {L : Nat} (hL : L ≤ 72)
    (hmid : MidOk 128 8 slots S = true) (hw : wr0 S L = true) (h13 : S.reg .r13 = some (.reg .r13)) :
    Ctx m0 st' := by
  have hs : SameOutside st.dmem st'.dmem (InRange (fb m0) L) :=
    Transcript.sameOutside_low hwf hm (r := 0) rfl (by omega) (wr0_spec hw)
  refine ⟨Frame.of_block hc.fr hwf hm hmid slots_le, ?_, same_trans h hc.same hs
    fun q hq ↦ frame_outs h (by omega) hq, (reg_kept hm h13).trans hc.r13⟩
  refine loc_keep hwf hm (midOk_writesIn hmid) (by omega) ?_ hc.out
  unfold miss
  rw [List.all_eq_true]
  intro w hwm
  have := wr0_spec hw w hwm
  simp only [this.1, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq]
  omega

/-- **A block** keeps the context, its writes in the frame below `L ≤ 72`. -/
theorem Ctx.block {a : DecArea} {s0 : TState} (h : SampleQueriesPre a s0 m0) (hc : Ctx m0 st)
    (hm : Match (frameEnv m0 st 128 [] vars ret) S st') {L : Nat} (hL : L ≤ 72)
    (hmid : MidOk 128 8 slots S = true) (hw : wr0 S L = true) (h13 : S.reg .r13 = some (.reg .r13)) :
    Ctx m0 st' :=
  hc.blockW h (mid_wf h hc.fr.kept) hm hL hmid hw h13

theorem TStateAt.block {a : DecArea} {s0 s : TState} (h : SampleQueriesPre a s0 m0)
    (hk : Kept st.dmem st'.dmem) {L : Nat} (hL : L ≤ 136)
    (hs : SameOutside st.dmem st'.dmem (InRange (fb m0) L)) (ht : TStateAt st.dmem (tA m0) a s) :
    TStateAt st'.dmem (tA m0) a s :=
  ht.frame hk (fun _ hq ↦ frame_not_t h (Transcript.inRange_mono hq hL)) hs

end

/-! ## The calls -/

section
variable [Host] {a : DecArea} {s0 : TState} {m0 : MachineData}

/-- **`SpongeW::squeeze` on the `TState`'s sponge**, from a block of a context's state `st` ending
in the call with RSP at the frame's offset `0`, RDI the `TState`, writing the frame below `24`:
the challenge `(sq s).1` in RAX, RDX, the `TState` then `(sq s).2`, the context kept, the
callee-saved registers the block's, the frame's bytes from `8` on the block's. -/
theorem squeeze_call (h : SampleQueriesPre a s0 m0)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {st : MachineData} (hc : Ctx m0 st) {s : TState} (hts : TStateAt st.dmem (tA m0) a s)
    {ret : BitVec 64} {S : SState} {st1 : MachineState} {next : Int64} {R : MachineState → Prop}
    (hm : Match (frameEnv m0 st 128 [] (fun _ ↦ 0) ret) S st1.data)
    (hmid : MidOk 128 0 slots S = true) {L : Nat} (hL : L ≤ 24) (hw : wr0 S L = true)
    (h13 : S.reg .r13 = some (.reg .r13)) (hrdi : reg st1.data .rdi = tA m0)
    (hpc : PcOk (frameEnv m0 st 128 [] (fun _ ↦ 0) ret) (.call NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) next st1)
    (cont : ∀ st2 : MachineState, st2.pc = next → Ctx m0 st2.data →
      TStateAt st2.data.dmem (tA m0) a (sq s).2 →
      reg st2.data .rax = (sq s).1.c0.toBitVec → reg st2.data .rdx = (sq s).1.c1.toBitVec →
      (∀ r, calleeSaved r = true → reg st2.data r = reg st1.data r) →
      (∀ j, 8 ≤ j → j < 136 → st2.data.dmem.get? (off (fb m0) j) =
        st1.data.dmem.get? (off (fb m0) j)) →
      SameOutside st1.data.dmem st2.data.dmem (fun q ↦ InRange (tA m0) tstateBytes q ∨
        InRange (stackBelow m0 sampleQueriesStack) sampleQueriesStack q) →
      Eventually (step1 Host.exe) R st2) :
    Eventually (step1 Host.exe) R st1 := by
  have hS := pre_S h
  have hn := pre_hn h
  have h8 := pre_h8 h
  have hwf := mid_wf (vars := fun _ ↦ 0) (ret := ret) h hc.fr.kept
  have hfnw := fb_noWrap h
  have hf1 : Frame m0 128 slots 0 st1.data := Frame.of_block hc.fr hwf hm hmid slots_le
  have hs1 := block_same hwf hm (by omega) hw
  have hsp1 : rspOf st1.data = fb m0 := by rw [hf1.sp, off_zero]
  have hfp := hts.footprint
  have hTn : (tA m0).toNat + 760 ≤ 2 ^ 64 := hfp.1.2
  have htok := pre_tok h
  have hts1 : TStateAt st1.data.dmem (tA m0) a s :=
    TStateAt.block h (hm.kept hwf) (by omega) hs1 hts
  have hso1 : SameOutside m0.dmem st1.data.dmem (Outs m0) :=
    same_trans h hc.same hs1 fun q hq ↦ frame_outs h (by omega) hq
  have hrc := pre_rc h
  have hrcOut : ∀ q, Outs m0 q → ¬ InRange rcAddr 192 q := by
    rintro q (hq | hq | hq) hr
    · exact not_inRange_of_apart (Transcript.Apart.symm' (pre_out h).2.2.2.2.2) hrc.2.1
        (pre_out h).2.1 hr hq
    · exact not_inRange_of_apart (Transcript.Apart.symm' htok.2.2) hrc.2.1 hfp.1.2 hr hq
    · exact not_inRange_of_apart hrc.2.2 hrc.2.1 (noWrap_stackBelow hS) hr
        (Transcript.inRange_mono hq (by omega))
  have hpre : SqueezePre s.sponge st1.data := by
    unfold SqueezePre
    rw [hrdi]
    have h1 : (tA m0).toNat + 760 ≤ (stackBelow m0 sampleQueriesStack).toNat ∨
        (stackBelow m0 sampleQueriesStack).toNat + (sampleQueriesStack + 8) ≤ (tA m0).toNat :=
      htok.1
    have h2 : (tA m0).toNat + 760 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (tA m0).toNat := htok.2.2
    refine ⟨Transcript.stackOk_callee hS hf1.kept hsp1 (by rw [N_eq]),
      Transcript.RcAt.callee hrc (Transcript.rc_keep hso1 hrcOut) hsp1 hn (by rw [N_eq]),
      ⟨fun j hj ↦ hts1.footprint.1.1 j (by simp only [spongeBytes] at hj; show j < 760; omega), ?_,
        Transcript.apart_callee (n := sampleQueriesStack) (F := 128) ?_ hsp1 hn (by rw [N_eq]), ?_⟩,
      hts1.sponge, ?_⟩
    · show (tA m0).toNat + 328 ≤ 2 ^ 64; omega
    · show (tA m0).toNat + 328 ≤ _ ∨ _ ≤ (tA m0).toNat; omega
    · show (tA m0).toNat + 328 ≤ _ ∨ _ ≤ (tA m0).toNat; omega
    · have hg := h.2.2.2.2
      have hgout := hg.areas (areas' := [(oA m0, queryBufBytes), (tA m0, tstateBytes)])
        (by intro ar har; simp only [List.mem_cons, List.not_mem_nil, or_false] at har; rcases har with rfl | rfl <;> simp [oA, tA])
      have hbytes := hgout.unchanged hS
        (by
          intro ar har
          simp only [List.mem_cons, List.not_mem_nil, or_false] at har
          rcases har with rfl | rfl
          · exact noWrap_iff.mpr (pre_out h).2.1
          · exact noWrap_iff.mpr hfp.1.2)
        (fun q hq => hso1 q (fun hc => hq (by
          rcases hc with ho | ht | hs
          · exact .inr ⟨(oA m0, queryBufBytes), by simp, ho⟩
          · exact .inr ⟨(tA m0, tstateBytes), by simp, ht⟩
          · exact .inl hs)))
      have hbase : stackBelow st1.data squeezeStack = stackBelow m0 sampleQueriesStack := by
        unfold stackBelow
        rw [hsp1]
        unfold fb stackBelow
        rw [N_eq]
        bv_omega
      apply NativeRustcVmX64.GotAt.callee hg hbytes
      · rw [hbase]
      · rw [hbase, N_eq]
        omega
      · intro ar har
        simp only [List.mem_cons, List.not_mem_nil, or_false] at har
        rcases har with rfl | rfl
        · exact ⟨(tA m0, tstateBytes), by simp [tA], le_rfl, by
            change (tA m0).toNat + 328 ≤ (tA m0).toNat + 760; omega⟩
        · have hrcmem : (rcAddr, 192) ∈ rodataAreas := by
            change (rodataAddr .keccakRC, NativeRustcVm.Data.Item.bytes .keccakRC |>.length) ∈ rodataAreas
            exact List.mem_map.mpr ⟨.keccakRC, by decide, rfl⟩
          exact ⟨(rcAddr, 192), by simp [hrcmem], le_rfl, le_rfl⟩
  refine call_then hpc (hsq s.sponge) hpre fun st2 hpc2 hrsp2 ⟨hc0, hc1, hsp2, hs2, hsv2⟩ ↦ ?_
  rw [hrdi] at hsp2 hs2
  have hcal : ∀ q, InRange (stackBelow st1.data squeezeStack) squeezeStack q →
      InRange (stackBelow m0 sampleQueriesStack) sampleQueriesStack q ∧
        ¬ InRange (fb m0) (128 + 8) q :=
    fun q hq ↦ Transcript.inRange_callee hsp1 h8 hn (by rw [N_eq]) hq
  have hT328 : ∀ q, InRange (tA m0) spongeBytes q → InRange (tA m0) 760 q :=
    fun q hq ↦ Transcript.inRange_mono hq (by simp only [spongeBytes]; omega)
  have hRf : ∀ q, (InRange (tA m0) spongeBytes q ∨
      InRange (stackBelow st1.data squeezeStack) squeezeStack q) → ¬ InRange (fb m0) (128 + 8) q := by
    rintro q (hq | hq)
    · exact not_inRange_of_apart (Transcript.apart_frame htok.1 hn N_ge) hfp.1.2 hfnw
        (hT328 q hq)
    · exact (hcal q hq).2
  have hf2 : Frame m0 128 slots 8 st2.data :=
    Frame.call hf1 hsv2 hrsp2 hs2 hRf hfnw slots_le
  have hkeep : ∀ j, 8 ≤ j → j < 136 → st2.data.dmem.get? (off (fb m0) j) =
      st1.data.dmem.get? (off (fb m0) j) := fun j hj1 hj2 ↦
    hs2 _ fun hq ↦ hRf _ hq (inRange_off_self (by omega) (by omega))
  have hts2 : TStateAt st2.data.dmem (tA m0) a (sq s).2 := by
    refine hts1.with_sponge hsv2.2 (fun q hq ↦ ⟨fun ht ↦ not_inRange_of_apart htok.1 hfp.1.2
      (noWrap_stackBelow hS) ht (Transcript.inRange_mono (hcal q hq).1 (by omega)),
      fun ha ↦ not_inRange_of_apart htok.2.1 hfp.2.1.2 (noWrap_stackBelow hS) ha
        (Transcript.inRange_mono (hcal q hq).1 (by omega))⟩)
      (fun q hq ↦ hs2 q ?_) hsp2
    rintro (hq' | hq')
    · obtain ⟨j, hj, hw', rfl⟩ := touch_of_inRange (o := 0) (n := 328)
        (hTn : NativeRustcVm.NoWrap (tA m0) 760) (by decide) (by rwa [off_zero])
      exact hq (Or.inl ⟨j, hj, hw'.2, rfl⟩)
    · exact hq (Or.inr hq')
  refine cont st2 hpc2 ⟨hf2, ?_, ?_, ?_⟩ hts2 hc0 hc1 (fun r hr ↦ hsv2.1 r hr) hkeep
    (SameOutside.mono hs2 ?_)
  · have hout1 := loc_keep hwf hm (midOk_writesIn hmid) (o := 72) (by omega) ?_ hc.out
    · exact fun i hi ↦ by
        have hi' : i < 8 := hi
        rw [off_add, hkeep _ (by omega) (by omega), ← off_add]
        exact hout1 i hi
    · unfold miss
      rw [List.all_eq_true]
      intro w hwm
      have := wr0_spec hw w hwm
      simp only [this.1, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq]
      omega
  · refine same_trans h hso1 hs2 ?_
    rintro q (hq | hq)
    · exact .inr (.inl (hT328 q hq))
    · exact .inr (.inr (hcal q hq).1)
  · exact (hsv2.1 .r13 rfl).trans ((reg_kept hm h13).trans hc.r13)
  · rintro q (hq | hq)
    · exact .inl (hT328 q hq)
    · exact .inr (hcal q hq).1

/-- **`query_bits`**, from a block of a context's state `st` ending in the call with RSP at the
frame's offset `0`, writing the frame below `8`: RAX its value, the context kept, the
callee-saved registers and memory the block's. -/
theorem qb_call (h : SampleQueriesPre a s0 m0)
    (hqb : Spec (Labels.label NativeRustcVmX64.Vm.QueryBits.entryLabel) QueryBitsPre QueryBitsPost)
    {st : MachineData} (hc : Ctx m0 st)
    {ret : BitVec 64} {S : SState} {st1 : MachineState} {next : Int64} {R : MachineState → Prop}
    (hm : Match (frameEnv m0 st 128 [] (fun _ ↦ 0) ret) S st1.data)
    (hmid : MidOk 128 0 slots S = true) (hw : wr0 S 8 = true) (h13 : S.reg .r13 = some (.reg .r13))
    (hpc : PcOk (frameEnv m0 st 128 [] (fun _ ↦ 0) ret) (.call NativeRustcVmX64.Vm.QueryBits.entryLabel) next st1)
    (cont : ∀ st2 : MachineState, st2.pc = next → Ctx m0 st2.data →
      reg st2.data .rax = (queryBits (ewArg (reg st1.data .rdi) (reg st1.data .rsi))
        (reg st1.data .rdx).toNat (reg st1.data .rcx).toNat).toBitVec →
      (∀ r, calleeSaved r = true → reg st2.data r = reg st1.data r) →
      st2.data.dmem = st1.data.dmem →
      Eventually (step1 Host.exe) R st2) :
    Eventually (step1 Host.exe) R st1 := by
  have hS := pre_S h
  have hn := pre_hn h
  have hwf := mid_wf (vars := fun _ ↦ 0) (ret := ret) h hc.fr.kept
  have hf1 : Frame m0 128 slots 0 st1.data := Frame.of_block hc.fr hwf hm hmid slots_le
  have hs1 := block_same hwf hm (by omega) hw
  have hsp1 : rspOf st1.data = fb m0 := by rw [hf1.sp, off_zero]
  refine call_then hpc hqb (Transcript.stackOk_callee hS hf1.kept hsp1 (by rw [N_eq]; simp [queryBitsStack]))
    fun st2 hpc2 hrsp2 ⟨hax, hs2, hsv2⟩ ↦ ?_
  have hd2 : st2.data.dmem = st1.data.dmem := by
    apply Std.ExtHashMap.ext_getElem?
    intro q
    rw [← Std.ExtHashMap.get?_eq_getElem?, ← Std.ExtHashMap.get?_eq_getElem?]
    refine hs2 q fun hq ↦ ?_
    rcases hq with ⟨r, hr, -⟩ | hq
    · exact absurd hr List.not_mem_nil
    · unfold InRange queryBitsStack at hq; omega
  have hRf : ∀ q, False → ¬ InRange (fb m0) (128 + 8) q := fun _ hq ↦ hq.elim
  have hf2 : Frame m0 128 slots 8 st2.data :=
    Frame.call hf1 hsv2 hrsp2 (R := fun _ ↦ False) (fun q _ ↦ by rw [hd2]) hRf (fb_noWrap h)
      slots_le
  refine cont st2 hpc2 ⟨hf2, ?_, ?_, ?_⟩ hax (fun r hr ↦ hsv2.1 r hr) hd2
  · rw [hd2]
    refine loc_keep hwf hm (midOk_writesIn hmid) (o := 72) (by omega) ?_ hc.out
    unfold miss
    rw [List.all_eq_true]
    intro w hwm
    have := wr0_spec hw w hwm
    simp only [this.1, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq]
    omega
  · rw [hd2]
    exact same_trans h hc.same hs1 fun q hq ↦ frame_outs h (by omega) hq
  · exact (hsv2.1 .r13 rfl).trans ((reg_kept hm h13).trans hc.r13)

end

end

end NativeRustcVmX64.Whir.SampleQueries
