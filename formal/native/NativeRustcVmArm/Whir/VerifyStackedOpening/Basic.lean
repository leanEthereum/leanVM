module

public import NativeRustcVmArm.Whir.VerifyStackedOpening.Exec
public import NativeRustcVmArm.Whir.VerifyStackedOpening.Model
public import NativeRustcVmArm.Whir.TFrame
public import NativeRustcVm.Tables.Same
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVmArm.Whir.GlueLevel.Mem
public import NativeRustcVmArm.Whir.MathFrame

/-!
# `verify_stacked_opening`: its frame, its context

From the entry `m0` (the `TState` X0, the layout X1, the rate X2, the ring switch's output X3, the
Keccak output X4, the column claims X5, the out-of-domain claim X6, the scales X7, the `WhirW` at
the word at SP): the 512-byte frame (`VFr`, X19 to X30 saved at 416 to 511), the outputs (`outs`:
the `WhirW` but the stack argument's word, the scales, the `TState`; `outsF`: all three), the
context `ctx` for the calls (`ctxOf` for other outputs). An input is unchanged in a state of the
frame (`same_input`).
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir

@[expose] public section

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(416, .X29), (424, .X30), (432, .X28), (440, .X27), (448, .X26), (456, .X25), (464, .X24),
    (472, .X23), (480, .X22), (488, .X21), (496, .X20), (504, .X19)]

/-- The `TState`. -/
abbrev tA (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- The `WhirW`. -/
abbrev pA (m0 : MachineData) : BitVec 64 := (whirStackArg m0 0).toBitVec
/-- The scales. -/
abbrev scA (m0 : MachineData) : BitVec 64 := m0.regs.X7.toBitVec

/-- The outputs up to `b34`: the `WhirW` but the word at SP (the stack argument, which no step
before `b34` writes), the scales, the `TState`. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  (InRange (pA m0) whirBytes q ∧ ¬InRange m0.regs.SP.toBitVec 8 q) ∨
    InRange (scA m0) scalesBytes q ∨ InRange (tA m0) tstateBytes q

/-- All the outputs. -/
def outsF (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (pA m0) whirBytes q ∨ InRange (scA m0) scalesBytes q ∨ InRange (tA m0) tstateBytes q

/-- The frame. -/
abbrev VFr (m0 st : MachineData) : Prop :=
  Fr m0 512 verifyStackedOpeningStack slots [] (outs m0) st

/-- The frame's byte `o`. -/
abbrev loc (m0 : MachineData) (o : Nat) : BitVec 64 := base m0 512 + BitVec.ofNat 64 o

end

public section

theorem stack_eq : verifyStackedOpeningStack = 12032 := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 512 := by decide

section
variable [Labels] {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- The precondition's parts. -/
structure Parts (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (coefficients point slices : Array EW) (cs : Array ColumnClaimW) (z : Array EW) (value : EW)
    (m0 : MachineData) : Prop where
  wt : WhirT m0 (tA m0) a verifyStackedOpeningStack
  ts : TStateAt m0.dmem (tA m0) a s
  roots : s.roots.size ≤ 2
  lay : NativeRustcVm.Layout.LayoutWAt m0.dmem m0.regs.X1.toBitVec layout
  ring : NativeRustcVm.Ring.RingWAt m0.dmem m0.regs.X3.toBitVec target coefficients
  kec : NativeRustcVm.KeccakGkr.KeccakOutAt m0.dmem m0.regs.X4.toBitVec point slices
  cl : NativeRustcVm.Layout.ClaimsWAt m0.dmem m0.regs.X5.toBitVec cs
  ood : NativeRustcVm.Layout.EqClaimAt m0.dmem m0.regs.X6.toBitVec z value
  arg : Readable m0 m0.regs.SP.toBitVec 8
  argt : Apart m0.regs.SP.toBitVec 8 (tA m0) tstateBytes
  args : Apart m0.regs.SP.toBitVec 8 (scA m0) scalesBytes
  po : WhirOut m0 (tA m0) a (pA m0) whirBytes verifyStackedOpeningStack
  so : WhirOut m0 (tA m0) a (scA m0) scalesBytes verifyStackedOpeningStack
  psc : Apart (pA m0) whirBytes (scA m0) scalesBytes
  ins : ∀ r ∈ vsoInputs m0, WhirIn m0 r.addr r.size verifyStackedOpeningStack ∧
    Apart r.addr r.size (tA m0) tstateBytes ∧ Apart r.addr r.size (pA m0) whirBytes ∧
    Apart r.addr r.size (scA m0) scalesBytes
  pw : (vsoInputs m0).Pairwise fun r r' ↦ Apart r.addr r.size r'.addr r'.size

theorem parts (h : VerifyStackedOpeningPre a s layout target coefficients point slices cs z value
    m0) : Parts a s layout target coefficients point slices cs z value m0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h9a, h9b, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h9a, h9b, h10, h11, h12, h13, h14⟩

variable (h : Parts a s layout target coefficients point slices cs z value m0)
include h

theorem Parts.hN : verifyStackedOpeningStack ≤ m0.regs.SP.toNat := h.wt.1.2.1

theorem Parts.hS : 12032 ≤ m0.regs.SP.toNat := by have := h.hN; rw [stack_eq] at this; exact this

/-- The frame's bytes are in the entry's stack. -/
theorem Parts.frame_sub {q : BitVec 64} (hq : InRange (base m0 512) 512 q) :
    InRange (stackBelow m0 verifyStackedOpeningStack) verifyStackedOpeningStack q := by
  have hN := h.hN
  have e1 := base_toNat (m0 := m0) (F := 512) (by rw [stack_eq] at hN; omega)
  have e2 := base_toNat (m0 := m0) (F := verifyStackedOpeningStack) hN
  rw [stack_eq] at e2 hN ⊢
  exact NativeRustcVm.InRange.mono hq (base_noWrap (by omega)) (base_noWrap hN)
    (by show (base m0 12032).toNat ≤ _; omega) (by show _ ≤ (base m0 12032).toNat + _; omega)

/-- **The context of the calls**, for outputs `O` among `outsF` holding the `TState`. -/
theorem Parts.ctxOf {O : BitVec 64 → Prop} (hO : ∀ q, O q → outsF m0 q)
    (hOt : ∀ q, InRange (tA m0) tstateBytes q → O q) :
    TCtx m0 512 verifyStackedOpeningStack (tA m0) a O := by
  have hfs : ∀ q, InRange (base m0 512) 512 q →
      InRange (stackBelow m0 verifyStackedOpeningStack) verifyStackedOpeningStack q :=
    fun q hq ↦ h.frame_sub hq
  obtain ⟨⟨hS, hrc, -, htok, -⟩, hts, -, -, -, -, -, -, -, -, -, ⟨hpo, -⟩, ⟨hso, -⟩, -, -, -⟩ := h
  have hfp := hts.footprint
  have hnt : NoWrap (tA m0) tstateBytes := hfp.1.2
  have hnd : NoWrap a.words (8 * a.len) := hfp.2.1.2
  refine ⟨hS, hrc, htok, hfp, by rw [stack_eq]; decide, rfl, fun q hq hr ↦ ?_, fun q hq hd ↦ ?_,
    hOt, fun q hq hf ↦ ?_⟩
  · rcases hO q hq with hq | hq | hq
    · exact NativeRustcVm.Apart.not_inRange hpo.2.2.2.2.2 hpo.2.1 hrc.2.1 hq hr
    · exact NativeRustcVm.Apart.not_inRange hso.2.2.2.2.2 hso.2.1 hrc.2.1 hq hr
    · exact NativeRustcVm.Apart.not_inRange htok.2.2 hnt hrc.2.1 hq hr
  · rcases hO q hq with hq | hq | hq
    · exact NativeRustcVm.Apart.not_inRange hpo.2.2.2.1 hpo.2.1 hnd hq hd
    · exact NativeRustcVm.Apart.not_inRange hso.2.2.2.1 hso.2.1 hnd hq hd
    · exact NativeRustcVm.Apart.not_inRange hfp.2.2 hnt hnd hq hd
  · have hs := hfs q hf
    have hnN := base_noWrap (m0 := m0) (F := verifyStackedOpeningStack) hS.2.1
    rcases hO q hq with hq | hq | hq
    · exact NativeRustcVm.Apart.not_inRange hpo.2.2.2.2.1 hpo.2.1 hnN hq hs
    · exact NativeRustcVm.Apart.not_inRange hso.2.2.2.2.1 hso.2.1 hnN hq hs
    · exact NativeRustcVm.Apart.not_inRange htok.1 hnt hnN hq hs

/-- **The context of the calls.** -/
theorem Parts.ctx : TCtx m0 512 verifyStackedOpeningStack (tA m0) a (outs m0) :=
  h.ctxOf (fun _ hq ↦ hq.elim (fun hq ↦ .inl hq.1) .inr) fun _ hq ↦ .inr (.inr hq)

/-- The frame is apart from the `TState` and its decoded area. -/
theorem Parts.frame_not_t {q : BitVec 64} (hq : InRange (base m0 512) 512 q) :
    ¬InRange (tA m0) tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := by
  have hs := h.frame_sub hq
  have htok := h.wt.2.2.2.1
  have hfp := h.ts.footprint
  exact ⟨fun ht ↦ NativeRustcVm.Apart.not_inRange htok.1 hfp.1.2 (base_noWrap h.hN) ht hs,
    fun hd ↦ NativeRustcVm.Apart.not_inRange htok.2.1 hfp.2.1.2 (base_noWrap h.hN) hd hs⟩

/-- The `TState` across a step changing the frame only. -/
theorem Parts.ts_frame {d d' : Mem 64} {s' : TState} (hts : TStateAt d (tA m0) a s')
    (hk : NativeRustcVm.Transcript.Keeps d d') (hs : SameOutside d d' (InRange (base m0 512) 512)) :
    TStateAt d' (tA m0) a s' :=
  hts.frame hk (fun _ hq ↦ h.frame_not_t hq) hs

/-- The `TState` across a call writing its stack and the scales. -/
theorem Parts.ts_call {st : MachineData} (hf : VFr m0 st) {N' : Nat}
    (hle : 512 + N' ≤ verifyStackedOpeningStack) {d' : Mem 64} {s' : TState}
    (hts : TStateAt st.dmem (tA m0) a s') (hk : NativeRustcVm.Transcript.Keeps st.dmem d')
    (hs : SameOutside st.dmem d' fun q ↦
      InRange (stackBelow st N') N' q ∨ InRange (scA m0) scalesBytes q) :
    TStateAt d' (tA m0) a s' := by
  have htok := h.ctx.tstateOk hf hle
  have hfp := h.ts.footprint
  have hso := h.so.1
  have hnN : NoWrap (stackBelow st N') N' := by
    have hS := h.hS
    rw [stack_eq] at hle
    rw [stackBelow_eq hf.sp (by omega)]
    exact NativeRustcVm.NoWrap.mono (base_noWrap (m0 := m0) (F := 512 + N') (by omega))
      (by omega)
  refine hts.frame hk (fun q hq ↦ ?_) hs
  rcases hq with hq | hq
  · exact ⟨fun ht ↦ NativeRustcVm.Apart.not_inRange htok.1 hfp.1.2 hnN ht hq,
      fun hd ↦ NativeRustcVm.Apart.not_inRange htok.2.1 hfp.2.1.2 hnN hd hq⟩
  · exact ⟨fun ht ↦ NativeRustcVm.Apart.not_inRange hso.2.2.1 hso.2.1 hfp.1.2 hq ht,
      fun hd ↦ NativeRustcVm.Apart.not_inRange hso.2.2.2.1 hso.2.1 hfp.2.1.2 hq hd⟩

theorem Parts.sc_nw : NoWrap (scA m0) scalesBytes := h.so.1.2.1

/-- A part of the scales, apart from a callee's stack. -/
theorem Parts.sc_off {st : MachineData} (hf : VFr m0 st) {N' : Nat}
    (hle : 512 + N' ≤ verifyStackedOpeningStack) {o n : Nat} (hon : o + n ≤ scalesBytes)
    (hn : 0 < n) : Apart (scA m0 + BitVec.ofNat 64 o) n (stackBelow st N') N' := by
  have := (h.ctx.outOk hf hle h.so.1).2.2.2.2.1
  have hnw := h.sc_nw
  unfold NoWrap at hnw
  unfold Apart at this ⊢
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

/-- A part of the scales, apart from the frame. -/
theorem Parts.sc_frame {o n : Nat} (hon : o + n ≤ scalesBytes) (hn : 0 < n) :
    Apart (scA m0 + BitVec.ofNat 64 o) n (base m0 512) 512 := by
  have := Ring.apart_frame (F := 512) h.hN (by rw [stack_eq]; decide) h.so.1.2.2.2.2.1
  have hnw := h.sc_nw
  unfold NoWrap at hnw
  unfold Apart at this ⊢
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

/-- **Bytes of the scales** across a step writing a callee's stack and the frame. -/
theorem Parts.sc_keep {st : MachineData} (hf : VFr m0 st) {N' : Nat}
    (hle : 512 + N' ≤ verifyStackedOpeningStack) {d' : Mem 64}
    (hs : SameOutside st.dmem d' fun q ↦
      InRange (stackBelow st N') N' q ∨ InRange (base m0 512) 512 q)
    {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ scalesBytes) (hn : 0 < bs.length)
    (hb : NativeRustcVm.BytesAt st.dmem (scA m0 + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt d' (scA m0 + BitVec.ofNat 64 o) bs := by
  have hnw := h.sc_nw
  unfold NoWrap at hnw
  have hno : NoWrap (scA m0 + BitVec.ofNat 64 o) bs.length := by
    unfold NoWrap; rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega
  have hS := h.hS
  have hle' := hle
  rw [stack_eq] at hle'
  have hnN : NoWrap (stackBelow st N') N' := by
    rw [stackBelow_eq hf.sp (by omega)]
    exact NativeRustcVm.NoWrap.mono (base_noWrap (m0 := m0) (F := 512 + N') (by omega))
      (by omega)
  refine hb.of_sameOutside hs fun i hi hq ↦ ?_
  have hin := NativeRustcVm.inRange_add (a := scA m0 + BitVec.ofNat 64 o) hi
    (by unfold NoWrap at hno; omega)
  rcases hq with hq | hq
  · exact NativeRustcVm.Apart.not_inRange (h.sc_off hf hle ho hn) hno hnN hin hq
  · exact NativeRustcVm.Apart.not_inRange (h.sc_frame ho hn) hno (base_noWrap (by omega)) hin hq

/-- **An input** unchanged in a state of the frame. -/
theorem Parts.same_input {st : MachineData} (hf : VFr m0 st) {x : BitVec 64} {n : Nat}
    (hin : WhirIn m0 x n verifyStackedOpeningStack) (ht : Apart x n (tA m0) tstateBytes)
    (hp : Apart x n (pA m0) whirBytes) (hs : Apart x n (scA m0) scalesBytes) :
    NativeRustcVm.Layout.Same m0.dmem st.dmem x n := by
  have hnx : NoWrap x n := hin.1.2
  have hnN := base_noWrap (m0 := m0) (F := verifyStackedOpeningStack) h.hN
  refine fun j hj ↦ hf.same _ fun hq ↦ ?_
  have hxj := NativeRustcVm.inRange_add (a := x) hj (by unfold NoWrap at hnx; omega)
  rcases hq with hq | hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange hin.2 hnx hnN hxj hq
  · exact NativeRustcVm.Apart.not_inRange hp hnx h.po.1.2.1 hxj hq.1
  · exact NativeRustcVm.Apart.not_inRange hs hnx h.so.1.2.1 hxj hq
  · exact NativeRustcVm.Apart.not_inRange ht hnx h.ts.footprint.1.2 hxj hq

/-- **An input area** unchanged in a state of the frame. -/
theorem Parts.same_in {st : MachineData} (hf : VFr m0 st) {r : NativeRustcVm.Region}
    (hr : r ∈ vsoInputs m0) : NativeRustcVm.Layout.Same m0.dmem st.dmem r.addr r.size :=
  have hi := h.ins r hr
  h.same_input hf hi.1 hi.2.1 hi.2.2.1 hi.2.2.2

/-- **An input area**, readable in a state of the frame and apart from the frame. -/
theorem Parts.in_ok {st : MachineData} (hf : VFr m0 st) {r : NativeRustcVm.Region}
    (hr : r ∈ vsoInputs m0) :
    NativeRustcVm.Mapped st.dmem r.addr r.size ∧ NoWrap r.addr r.size ∧
      Apart (base m0 512) 512 r.addr r.size := by
  have hi := (h.ins r hr).1
  exact ⟨fun i hi' ↦ hf.kept _ (hi.1.1 i hi'), hi.1.2, NativeRustcVm.Apart.symm
    (Ring.apart_frame h.hN (by rw [stack_eq]; decide) hi.2)⟩

omit [Labels] h in
theorem mem_lay : (⟨m0.regs.X1.toBitVec, NativeRustcVm.Layout.layoutBytes⟩ : NativeRustcVm.Region) ∈
    vsoInputs m0 := by simp [vsoInputs, BasisAddrs.regions]
omit [Labels] h in
theorem mem_ring : (⟨m0.regs.X3.toBitVec, NativeRustcVm.Ring.ringWBytes⟩ : NativeRustcVm.Region) ∈
    vsoInputs m0 := by simp [vsoInputs, BasisAddrs.regions]
omit [Labels] h in
theorem mem_kec : (⟨m0.regs.X4.toBitVec, NativeRustcVm.KeccakGkr.outBytes⟩ : NativeRustcVm.Region) ∈
    vsoInputs m0 := by simp [vsoInputs, BasisAddrs.regions]
omit [Labels] h in
theorem mem_cl : (⟨m0.regs.X5.toBitVec, NativeRustcVm.Layout.claimsBytes⟩ : NativeRustcVm.Region) ∈
    vsoInputs m0 := by simp [vsoInputs, BasisAddrs.regions]
omit [Labels] h in
theorem mem_ood :
    (⟨m0.regs.X6.toBitVec, NativeRustcVm.Layout.eqClaimBytes⟩ : NativeRustcVm.Region) ∈
      vsoInputs m0 := by simp [vsoInputs, BasisAddrs.regions]

/-- The frame alone, as an environment. -/
theorem Parts.frame_env {st : MachineData} (hf : VFr m0 st) :
    (Env.ofMachine st [(base m0 512, 512)]).WF ∧
      Match (Env.ofMachine st [(base m0 512, 512)]) frameS st := by
  have hstk := h.wt.1
  have hS := h.hS
  exact ⟨Env.wf_of ⟨⟨fun i hi ↦ hf.kept _ (Ring.frame_mapped hstk (by rw [stack_eq]; decide) i hi),
      base_noWrap (by omega)⟩, trivial⟩ (List.pairwise_singleton _ _),
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by rw [stack_eq]; decide) rfl, trivial⟩
      (by rw [hf.sp]; simp [Sym.eval]) trivial trivial trivial trivial⟩

end

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
