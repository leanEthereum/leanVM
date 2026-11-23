module

public import NativeRustcVmX64.Whir.BasisWEval.Defs

/-!
# `BasisW::eval`: the invariants and the steps they share (x86-64)

`Base m0 ba o d`: the frame (RSP at offset `o`) and the words every later block reads from it:
the output's address (`32`), the point (`40`, `48`), the layout's address (`72`). `Acc W`: the
running sum over the weights `W` at `24`, `64`, the next scale's address R13, the scales' end
RBP.

A block run from a state of the frame (`In.block`) keeps the frame and the words it misses
(`FW.block`); a call keeps the frame's words above its call slot and outside its output
(`FW.call`). The callees' arguments: inputs readable and apart from a callee's stack
(`In.argIn`, `In.argSlice`), the callee's stack (`In.stackOk_at`), the frame's `Option<EW>` at
`80` (`In.optOut`), the two argument words at `8`, `16` (`In.argsOk`, `stackArg_of`).
-/

namespace NativeRustcVmX64.Whir.BasisWEval

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model LeanVM.Parameters
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVm.KeccakGkr (KeccakOutAt outBytes)
open NativeRustcVm.Transcript (off off_add off_zero toNat_off bytesAt_congr OptEWAt)
open LeanVM.Protocol.Verifier (qkeccak Placement)

@[expose] public section

/-- **The frame and the words every later block reads.** -/
structure Base (m0 : MachineData) (ba : BasisAddrs) (o : Nat) (d : MachineData) : Prop where
  fr : Fb m0 o d
  w32 : FW m0 d 32 (reg m0 .rdi)
  w40 : FW m0 d 40 (reg m0 .rdx)
  w48 : FW m0 d 48 (reg m0 .rcx)
  w72 : FW m0 d 72 ba.layout

/-- **The running sum** over the weights `W` (`24`, `64`), the next scale's address (R13), the
scales' end (RBP). -/
structure Acc (m0 : MachineData) (ba : BasisAddrs) (b : BasisW) (W : Array EW) (d : MachineData) :
    Prop where
  w24 : FW m0 d 24 (dot b.scales W).c0.toBitVec
  w64 : FW m0 d 64 (dot b.scales W).c1.toBitVec
  r13 : reg d .r13 = sA ba (min W.size ba.count)
  rbp : reg d .rbp = sA ba ba.count

end

public section

variable {m0 : MachineData} {ba : BasisAddrs} {b : BasisW} {v : Vals}

theorem N_ge : 160 ≤ basisWEvalStack := stack_le.2.2.2.2.2

/-! ## Frame words -/

section
variable {d d' : MachineData} {o : Nat} {w : BitVec 64}

/-- A frame word kept where its bytes are. -/
theorem FW.keep (h : FW m0 d o w)
    (hk : ∀ i < 8, d'.dmem.get? (off (fb m0) (o + i)) = d.dmem.get? (off (fb m0) (o + i))) :
    FW m0 d' o w :=
  bytesAt_congr h fun i hi ↦ by
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    rw [off_add]
    exact hk i hi'

/-- A frame word kept by a block that misses it. -/
theorem FW.block [Labels] {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {S : SState}
    {o' : Nat} (h : FW m0 d o w) (hwf : (envB m0 d rest ret).WF)
    (hm : Match (envB m0 d rest ret) S d') (hmid : MidOk 160 o' slots S = true)
    (ho : o + 8 ≤ 168) (hmiss : missW o S = true) : FW m0 d' o w :=
  wordAt_block hwf hm (writesIn_of_mid hmid) ho hmiss h

/-- A frame word kept by a call at offset `c ≤ o`, its output at `lo` (`len` bytes) apart. -/
theorem FW.call {c lo len : Nat} (h : FW m0 d o w)
    (hk : ∀ j, c ≤ j → j < 160 + 8 → (j < lo ∨ lo + len ≤ j) →
      d'.dmem.get? (off (fb m0) j) = d.dmem.get? (off (fb m0) j))
    (hc : c ≤ o) (ho : o + 8 ≤ 168) (hl : o + 8 ≤ lo ∨ lo + len ≤ o) : FW m0 d' o w :=
  h.keep fun i hi ↦ hk _ (by omega) (by omega) (by omega)

/-- A frame word a block stored. -/
theorem FW.wrote [Labels] {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {S : SState}
    (hm : Match (envB m0 d rest ret) S d') (ho : o + 8 ≤ 168) {s : Sym}
    (hw : wrote S 0 o s = true) (hv : s.eval (envB m0 d rest ret) = w) : FW m0 d' o w := by
  have := wordAt_wrote hm ho hw
  rwa [hv] at this

/-- A frame word loaded. -/
theorem FW.load [Labels] {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} (h : FW m0 d o w) :
    (envB m0 d rest ret).load 0 o 8 = w :=
  load_fw h

/-- A frame word read. -/
theorem FW.wordOf (h : FW m0 d o w) : (NativeRustcVm.wordOf d.dmem (off (fb m0) o)).toBitVec = w := by
  rw [NativeRustcVm.wordOf_of_wordAt h]

end

/-! ## Blocks -/

/-- **A block** from a state of the frame: the frame at the block's end, RSP at `o'`. -/
theorem In.block [Host] (h : In m0 ba b v) {o o' : Nat} {d : MachineData} (hf : Fb m0 o d)
    {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} (hwf : (envB m0 d rest ret).WF)
    {ds : List Directive} {j : Nat} (hk : ds.IsInfixAt Host.prog j) {S S' : SState} {x : Exit}
    (hx : exec ds S = some (S', x))
    (hret : ∀ l, x = .call l → ret = (Host.addrOf (j + ds.length)).toBitVec)
    (hm : Match (envB m0 d rest ret) S d) (hmid : MidOk 160 o' slots S' = true)
    (h0 : ∀ w ∈ S'.mem, w.r = 0) {R : MachineState → Prop}
    (cont : ∀ st : MachineState, Match (envB m0 d rest ret) S' st.data →
      PcOk (envB m0 d rest ret) x (Host.addrOf (j + ds.length)) st → Fb m0 o' st.data →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf j⟩ :=
  exec_then hk hx hwf hret hm fun st hm' hpc ↦
    cont st hm' hpc (hf.block0 h.stackOk N_ge hwf hm' hmid slots_le h0)

/-- The block's `MidOk` gives its writes in region 0. -/
theorem h0_of_nil {S : SState} (h : S.mem = []) : ∀ w ∈ S.mem, w.r = 0 := by
  rw [h]; simp

/-- `Base` after a block that misses its words. -/
theorem Base.block [Labels] {o o' : Nat} {d d' : MachineData} {rest : List (BitVec 64 × Nat)}
    {ret : BitVec 64} {S : SState} (hb : Base m0 ba o d) (hf : Fb m0 o' d')
    (hwf : (envB m0 d rest ret).WF) (hm : Match (envB m0 d rest ret) S d')
    (hmid : MidOk 160 o' slots S = true) (hmiss : missWs [32, 40, 48, 72] S = true) :
    Base m0 ba o' d' := by
  have hw := missWs_spec hmiss
  exact ⟨hf, hb.w32.block hwf hm hmid (by omega) (hw 32 (by simp)),
    hb.w40.block hwf hm hmid (by omega) (hw 40 (by simp)),
    hb.w48.block hwf hm hmid (by omega) (hw 48 (by simp)),
    hb.w72.block hwf hm hmid (by omega) (hw 72 (by simp))⟩

/-- `Base` after a block without writes. -/
theorem Base.nil [Labels] {o o' : Nat} {d d' : MachineData} {rest : List (BitVec 64 × Nat)}
    {ret : BitVec 64} {S : SState} (hb : Base m0 ba o d) (hf : Fb m0 o' d')
    (hwf : (envB m0 d rest ret).WF) (hm : Match (envB m0 d rest ret) S d') (hmem : S.mem = []) :
    Base m0 ba o' d' := by
  have hd : d'.dmem = d.dmem := hm.dmem_eq hwf hmem
  exact ⟨hf, by unfold FW; rw [hd]; exact hb.w32, by unfold FW; rw [hd]; exact hb.w40,
    by unfold FW; rw [hd]; exact hb.w48, by unfold FW; rw [hd]; exact hb.w72⟩

/-- A frame word after a block without writes. -/
theorem FW.nil [Labels] {o : Nat} {d d' : MachineData} {rest : List (BitVec 64 × Nat)}
    {ret : BitVec 64} {S : SState} {w : BitVec 64} (h : FW m0 d o w)
    (hwf : (envB m0 d rest ret).WF) (hm : Match (envB m0 d rest ret) S d') (hmem : S.mem = []) :
    FW m0 d' o w := by
  unfold FW; rw [hm.dmem_eq hwf hmem]; exact h

/-- `Base` across a call at `c ≤ 32`, its output above `72`. -/
theorem Base.call {o o' c lo len : Nat} {d d' : MachineData} (hb : Base m0 ba o d)
    (hf : Fb m0 o' d')
    (hk : ∀ j, c ≤ j → j < 160 + 8 → (j < lo ∨ lo + len ≤ j) →
      d'.dmem.get? (off (fb m0) j) = d.dmem.get? (off (fb m0) j))
    (hc : c ≤ 32) (hl : 80 ≤ lo ∨ lo + len ≤ 32) : Base m0 ba o' d' :=
  ⟨hf, hb.w32.call hk (by omega) (by omega) (by omega),
    hb.w40.call hk (by omega) (by omega) (by omega),
    hb.w48.call hk (by omega) (by omega) (by omega),
    hb.w72.call hk (by omega) (by omega) (by omega)⟩

/-! ## Callees -/

section
variable {o : Nat} {d : MachineData}

theorem In.rsp_toNat (h : In m0 ba b v) (hf : Fb m0 o d) (ho : o < 168) :
    (rspOf d).toNat = (rspOf m0).toNat - 160 + o := by
  rw [hf.frame.sp]
  exact fb_off_toNat (j := o) h.stackOk N_ge ho

/-- RSP at offset `o` is `160 - o` below the entry's. -/
theorem In.rsp_eq (h : In m0 ba b v) (hf : Fb m0 o d) (ho : o ≤ 160) :
    rspOf d = stackBelow m0 (160 - o) := by
  apply BitVec.eq_of_toNat_eq
  have := h.hN
  have := N_ge
  rw [h.rsp_toNat hf (by omega), stackBelow_toNat (by omega)]
  omega

/-- A callee's stack, RSP at the frame's offset `o`. -/
theorem In.stackOk_at (h : In m0 ba b v) (hf : Fb m0 o d) (ho : o ≤ 160) {Nc : Nat}
    (hle : 160 - o + Nc ≤ basisWEvalStack) : StackOk d Nc :=
  NativeRustcVmX64.Transcript.stackOk_callee h.stackOk hf.frame.kept (h.rsp_eq hf ho) hle

/-- An input, for a callee called at the frame's offset `o`. -/
theorem In.argIn (h : In m0 ba b v) (hf : Fb m0 o d) (ho : o ≤ 160) {Nc : Nat}
    (hle : 160 - o + Nc ≤ basisWEvalStack) {a : BitVec 64} {n : Nat}
    (ha : WhirIn m0 a n basisWEvalStack) : WhirIn d a n Nc :=
  whirIn_callee ha h.stackOk hf.frame.kept (h.rsp_eq hf ho) hle

/-- The frame's `Option<EW>` at `80`, for a callee called at the frame's offset `0` with two
argument words. -/
theorem In.optOut (h : In m0 ba b v) (hf : Fb m0 0 d) {Nc : Nat}
    (hle : 160 + Nc ≤ basisWEvalStack) : OptOutOk d (off (fb m0) 80) Nc 2 := by
  have hS := h.stackOk
  have hN := h.hN
  have e2 := N_ge
  have hfb := stackBelow_toNat (m := m0) (n := 160) (by omega)
  have hsp := h.rsp_toNat hf (by omega)
  have h80 : (off (fb m0) 80).toNat = (rspOf m0).toNat - 160 + 80 :=
    fb_off_toNat hS N_ge (by omega)
  refine ⟨⟨fun i hi ↦ ?_, ?_⟩, ?_, ?_⟩
  · rw [off_add]
    exact h.frame_mapped hf.frame.kept _ (by omega)
  · show (off (fb m0) 80).toNat + 24 ≤ 2 ^ 64
    have := hS.2.1; omega
  · show NativeRustcVm.Apart _ _ _ _
    unfold NativeRustcVm.Apart
    rw [stackBelow_toNat (by omega), hsp, h80]
    omega
  · show NativeRustcVm.Apart _ _ _ _
    unfold NativeRustcVm.Apart
    have e8 : (rspOf d + 8#64).toNat = (rspOf d).toNat + 8 := by
      rw [BitVec.toNat_add, show (8#64 : BitVec 64).toNat = 8 from rfl]
      have := hS.2.1
      omega
    rw [e8, hsp, h80]
    omega

/-- The argument words, for a callee called at the frame's offset `0`. -/
theorem In.argsOk (h : In m0 ba b v) (hf : Fb m0 0 d) : ArgsOk d 2 := by
  have hS := h.stackOk
  have hN := h.hN
  have e2 := N_ge
  have hsp := h.rsp_toNat hf (by omega)
  have e : rspOf d + 8#64 = off (fb m0) 8 := by
    simp only [hf.frame.sp, off_add, Nat.zero_add]
  refine ⟨fun i hi ↦ ?_, by have := hS.2.1; omega⟩
  rw [e, off_add]
  exact h.frame_mapped hf.frame.kept _ (by omega)

/-- Argument word `i`, at the frame's `8 + 8 i`. -/
theorem stackArg_of (hf : Fb m0 0 d) {i : Nat} {w : BitVec 64} (hw : FW m0 d (8 + 8 * i) w) :
    stackArg d i = w := by
  unfold stackArg
  simp only [hf.frame.sp, off_add, Nat.zero_add]
  exact hw.wordOf

end

/-! ## Callee results -/

/-- An `Option<EW>`'s `Some` at the frame's `80`, as the blocks read it. -/
theorem optSome {d : MachineData} {x : EW}
    (h : OptEWAt d.dmem (off (fb m0) 80) (some x)) :
    FW m0 d 80 1#64 ∧ FW m0 d 88 x.c0.toBitVec ∧ FW m0 d 96 x.c1.toBitVec := by
  obtain ⟨h1, h2⟩ := h
  have he := NativeRustcVm.Transcript.ewAt_iff.mp h2
  refine ⟨h1, ?_, ?_⟩
  · show NativeRustcVm.WordAt _ (off (fb m0) 88) _
    rw [show off (fb m0) 88 = off (off (fb m0) 80) 8 by rw [NativeRustcVm.Transcript.off_off]]
    exact he.1
  · show NativeRustcVm.WordAt _ (off (fb m0) 96) _
    rw [show off (fb m0) 96 = off (off (off (fb m0) 80) 8) 8 by
      rw [NativeRustcVm.Transcript.off_off, NativeRustcVm.Transcript.off_off]]
    exact he.2

/-- The tag word's low half `1`: `cmpl $1; jne` not taken. -/
theorem tag_false [Labels] {d : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64}
    (h : FW m0 d 80 1#64) : cTag.eval (envB m0 d rest ret) = false := by
  have : (envB m0 d rest ret).load 0 80 4 = BitVec.ofNat 64 (1 : UInt64).toNat :=
    load4_of_tag (w := 1) (.inr rfl) (by
      show NativeRustcVm.WordAt d.dmem (off (fb m0) 80) 1
      exact h)
  simp only [cTag, SBool.eval, Sym.eval, this]
  decide

end

end NativeRustcVmX64.Whir.BasisWEval
