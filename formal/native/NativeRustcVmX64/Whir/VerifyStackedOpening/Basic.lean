module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.Exec
public import NativeRustcVmX64.Whir.VerifyStackedOpening.Model
public import NativeRustcVmX64.Spec.Whir
public import NativeRustcVmX64.Spec.Layout
public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Transcript.Callee
public import NativeRustcVm.Tables.Same

/-!
# `verify_stacked_opening`: its frame, its context (x86-64)

From the entry `m0` (the `TState` RDI, the layout RSI, the rate RDX, the ring switch's output
RCX, the Keccak output R8, the column claims R9, the out-of-domain claim, the scales and the
`WhirW` the stack arguments `0` to `2`): the 512-byte frame (`Frame m0 512 slots`), the outputs
(`outs`: the `WhirW`, the scales, the `TState`), what may change (`Wr`: the outputs and the
stack). `Ok m0 st o`: a state of the frame (RSP at offset `o`) whose memory changed only there;
kept by a block writing the frame (`Ok.block`) and by a call writing its stack and outputs
(`Ok.call`, the frame's bytes then unchanged). Every address is a number (`toNat`): each area
apart from the stack is below the stack or above the stack arguments (`Parts.out_nat`, …).
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir

/-- The entry's RSP as a number. -/
local notation "R0 " m0:max => BitVec.toNat (rspOf m0)

@[expose] public section

/-- The `TState`. -/
abbrev tA (m0 : MachineData) : BitVec 64 := reg m0 .rdi
/-- The out-of-domain claim. -/
abbrev oA (m0 : MachineData) : BitVec 64 := stackArg m0 0
/-- The scales. -/
abbrev scA (m0 : MachineData) : BitVec 64 := stackArg m0 1
/-- The `WhirW`. -/
abbrev pA (m0 : MachineData) : BitVec 64 := stackArg m0 2
/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 512

/-- The outputs. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (pA m0) whirBytes q ∨ NativeRustcVm.InRange (scA m0) scalesBytes q ∨
    NativeRustcVm.InRange (tA m0) tstateBytes q

/-- What may change: the outputs and the stack. -/
def Wr (m0 : MachineData) (q : BitVec 64) : Prop :=
  outs m0 q ∨ NativeRustcVm.InRange (stackBelow m0 verifyStackedOpeningStack) verifyStackedOpeningStack q

/-- **A state of the frame**, RSP at offset `o`, memory changed only in the outputs and the
stack. -/
structure Ok (m0 st : MachineData) (o : Nat) : Prop where
  fr : Frame m0 512 slots o st
  so : NativeRustcVm.SameOutside m0.dmem st.dmem (Wr m0)

/-- The frame's bytes unchanged. -/
def FrameSame (m0 : MachineData) (d d' : Mem 64) : Prop :=
  ∀ q, NativeRustcVm.InRange (fb m0) 520 q → d'.get? q = d.get? q

/-- The frame's words: word `v` at offset `o` for each `(o, v)`. -/
def FW (d : Mem 64) (m0 : MachineData) (L : List (Nat × UInt64)) : Prop :=
  ∀ p ∈ L, NativeRustcVm.WordAt d (off (fb m0) p.1) p.2

end

public section

theorem stack_eq : verifyStackedOpeningStack = 11936 := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 512 := by decide

theorem slots_ge : ∀ p ∈ slots, 464 ≤ p.1 := by decide

theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

theorem inR {a q : BitVec 64} {n : Nat} (h : NativeRustcVm.NoWrap a n) :
    NativeRustcVm.InRange a n q ↔ a.toNat ≤ q.toNat ∧ q.toNat < a.toNat + n :=
  inRange_iff' h

section
variable [Labels] {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- The precondition's parts. -/
structure Parts (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (coefficients point slices : Array EW) (cs : Array ColumnClaimW) (z : Array EW) (value : EW)
    (m0 : MachineData) : Prop where
  wt : WhirT m0 (tA m0) a verifyStackedOpeningStack
  args : ArgsOk m0 3
  ts : TStateAt m0.dmem (tA m0) a s
  roots : s.roots.size ≤ 2
  lay : NativeRustcVm.Layout.LayoutWAt m0.dmem (reg m0 .rsi) layout
  ring : NativeRustcVm.Ring.RingWAt m0.dmem (reg m0 .rcx) target coefficients
  kec : NativeRustcVm.KeccakGkr.KeccakOutAt m0.dmem (reg m0 .r8) point slices
  cl : NativeRustcVm.Layout.ClaimsWAt m0.dmem (reg m0 .r9) cs
  ood : NativeRustcVm.Layout.EqClaimAt m0.dmem (oA m0) z value
  argt : NativeRustcVm.Apart (rspOf m0 + 8#64) 24 (tA m0) tstateBytes
  argsc : NativeRustcVm.Apart (rspOf m0 + 8#64) 24 (scA m0) scalesBytes
  argp : NativeRustcVm.Apart (rspOf m0 + 8#64) 24 (pA m0) whirBytes
  po : WhirOut m0 (tA m0) a (pA m0) whirBytes verifyStackedOpeningStack
  so : WhirOut m0 (tA m0) a (scA m0) scalesBytes verifyStackedOpeningStack
  psc : NativeRustcVm.Apart (pA m0) whirBytes (scA m0) scalesBytes
  ins : ∀ r ∈ vsoInputs m0, WhirIn m0 r.addr r.size verifyStackedOpeningStack ∧
    NativeRustcVm.Apart r.addr r.size (tA m0) tstateBytes ∧
    NativeRustcVm.Apart r.addr r.size (pA m0) whirBytes ∧
    NativeRustcVm.Apart r.addr r.size (scA m0) scalesBytes
  pw : (vsoInputs m0).Pairwise fun r r' ↦ NativeRustcVm.Apart r.addr r.size r'.addr r'.size
  got : GotAt m0 verifyStackedOpeningStack
    ([(tA m0, tstateBytes), (a.words, 8 * a.len), (scA m0, scalesBytes), (pA m0, whirBytes)] ++
      (vsoInputs m0).map (fun r => (r.addr, r.size)) ++ rodataAreas) ["memcpy", "memset"]

theorem parts (h : VerifyStackedOpeningPre a s layout target coefficients point slices cs z value
    m0) : Parts a s layout target coefficients point slices cs z value m0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, hg⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, hg⟩

omit [Labels] in
theorem mem_lay : (⟨reg m0 .rsi, NativeRustcVm.Layout.layoutBytes⟩ : NativeRustcVm.Region) ∈
    vsoInputs m0 := by simp [vsoInputs, BasisAddrs.regions]
omit [Labels] in
theorem mem_ring : (⟨reg m0 .rcx, NativeRustcVm.Ring.ringWBytes⟩ : NativeRustcVm.Region) ∈
    vsoInputs m0 := by simp [vsoInputs, BasisAddrs.regions]
omit [Labels] in
theorem mem_kec : (⟨reg m0 .r8, NativeRustcVm.KeccakGkr.outBytes⟩ : NativeRustcVm.Region) ∈
    vsoInputs m0 := by simp [vsoInputs, BasisAddrs.regions]
omit [Labels] in
theorem mem_cl : (⟨reg m0 .r9, NativeRustcVm.Layout.claimsBytes⟩ : NativeRustcVm.Region) ∈
    vsoInputs m0 := by simp [vsoInputs, BasisAddrs.regions]
omit [Labels] in
theorem mem_ood : (⟨oA m0, NativeRustcVm.Layout.eqClaimBytes⟩ : NativeRustcVm.Region) ∈
    vsoInputs m0 := by simp [vsoInputs, BasisAddrs.regions]

variable (h : Parts a s layout target coefficients point slices cs z value m0)
include h

/-- The stack, the stack arguments, as numbers. -/
theorem Parts.rsp : 11936 ≤ R0 m0 ∧ R0 m0 + 32 ≤ 2 ^ 64 := by
  have h1 := h.wt.1.1
  have h2 := h.args.2
  rw [stack_eq] at h1
  exact ⟨h1, by omega⟩

theorem Parts.sb : (stackBelow m0 verifyStackedOpeningStack).toNat = R0 m0 - 11936 := by
  rw [stackBelow_toNat (by rw [stack_eq]; exact h.rsp.1), stack_eq]

theorem Parts.fbn : (fb m0).toNat = R0 m0 - 512 :=
  stackBelow_toNat (by have := h.rsp.1; omega)

/-- A byte of the stack, as a number. -/
theorem Parts.inStack {q : BitVec 64} :
    NativeRustcVm.InRange (stackBelow m0 verifyStackedOpeningStack) verifyStackedOpeningStack q ↔
      R0 m0 - 11936 ≤ q.toNat ∧ q.toNat < R0 m0 := by
  have hs := h.sb
  have hr := h.rsp
  rw [inR (by unfold NativeRustcVm.NoWrap; rw [hs, stack_eq]; omega), hs, stack_eq]
  omega

/-- A byte of the frame (and its return address), as a number. -/
theorem Parts.inFrame {q : BitVec 64} {n : Nat} (hn : n ≤ 520) :
    NativeRustcVm.InRange (fb m0) n q ↔ R0 m0 - 512 ≤ q.toNat ∧ q.toNat < R0 m0 - 512 + n := by
  have hf := h.fbn
  have hr := h.rsp
  rw [inR (by unfold NativeRustcVm.NoWrap; omega), hf]

/-- **An area apart from the stack**, as numbers: below the stack, or above the return
address. -/
theorem Parts.off_nat {x : BitVec 64} {n : Nat}
    (hx : NativeRustcVm.Apart x n (stackBelow m0 verifyStackedOpeningStack) (verifyStackedOpeningStack + 8)) :
    x.toNat + n ≤ R0 m0 - 11936 ∨ R0 m0 + 8 ≤ x.toNat := by
  have := h.sb
  unfold NativeRustcVm.Apart at hx
  rw [this, stack_eq] at hx
  have := h.rsp.1
  omega

/-- The `TState` as numbers: below the stack or above the stack arguments. -/
theorem Parts.t_nat : (tA m0).toNat + tstateBytes ≤ 2 ^ 64 ∧
    ((tA m0).toNat + tstateBytes ≤ R0 m0 - 11936 ∨ R0 m0 + 32 ≤ (tA m0).toNat) := by
  have h1 := h.off_nat h.wt.2.2.2.1.1
  have h2 := h.argt
  have h3 := h.ts.footprint.1.2
  have ht : tstateBytes = 760 := rfl
  unfold NativeRustcVm.Apart at h2
  unfold NativeRustcVm.NoWrap at h3
  have : (rspOf m0 + 8#64).toNat = R0 m0 + 8 := by
    rw [BitVec.toNat_add]; have := h.rsp.2; simp; omega
  rw [this] at h2
  refine ⟨h3, by omega⟩

/-- The decoded area as numbers: below the stack or above the return address. -/
theorem Parts.a_nat : a.words.toNat + 8 * a.len ≤ 2 ^ 64 ∧
    (a.words.toNat + 8 * a.len ≤ R0 m0 - 11936 ∨ R0 m0 + 8 ≤ a.words.toNat) :=
  ⟨h.ts.footprint.2.1.2, h.off_nat h.wt.2.2.2.1.2.1⟩

/-- An output as numbers: below the stack or above the stack arguments. -/
theorem Parts.out_nat {x : BitVec 64} {n : Nat} (hn : 0 < n) (ho : WhirOut m0 (tA m0) a x n verifyStackedOpeningStack)
    (ha : NativeRustcVm.Apart (rspOf m0 + 8#64) 24 x n) :
    x.toNat + n ≤ 2 ^ 64 ∧ (x.toNat + n ≤ R0 m0 - 11936 ∨ R0 m0 + 32 ≤ x.toNat) := by
  have h1 := h.off_nat ho.1.2.2.2.2.1
  have h3 := ho.1.2.1
  unfold NativeRustcVm.Apart at ha
  have : (rspOf m0 + 8#64).toNat = R0 m0 + 8 := by
    rw [BitVec.toNat_add]; have := h.rsp.2; simp; omega
  rw [this] at ha
  exact ⟨h3, by omega⟩

theorem Parts.p_nat : (pA m0).toNat + whirBytes ≤ 2 ^ 64 ∧
    ((pA m0).toNat + whirBytes ≤ R0 m0 - 11936 ∨ R0 m0 + 32 ≤ (pA m0).toNat) :=
  h.out_nat (by decide) h.po h.argp

theorem Parts.sc_nat : (scA m0).toNat + scalesBytes ≤ 2 ^ 64 ∧
    ((scA m0).toNat + scalesBytes ≤ R0 m0 - 11936 ∨ R0 m0 + 32 ≤ (scA m0).toNat) :=
  h.out_nat (by decide) h.so h.argsc

/-- An input as numbers: below the stack or above the return address. -/
theorem Parts.in_nat {r : NativeRustcVm.Region} (hr : r ∈ vsoInputs m0) :
    r.addr.toNat + r.size ≤ 2 ^ 64 ∧
      (r.addr.toNat + r.size ≤ R0 m0 - 11936 ∨ R0 m0 + 8 ≤ r.addr.toNat) :=
  ⟨(h.ins r hr).1.1.2, h.off_nat (h.ins r hr).1.2⟩

/-- **The frame's bytes** are none of the outputs'. -/
theorem Parts.frame_not_outs {q : BitVec 64} (hq : NativeRustcVm.InRange (fb m0) 520 q) :
    ¬ outs m0 q := by
  have hf := h.fbn
  have hr := h.rsp
  rw [inR (by unfold NativeRustcVm.NoWrap; omega), hf] at hq
  have ht := h.t_nat
  have hp := h.p_nat
  have hs := h.sc_nat
  rintro (hq' | hq' | hq')
  · rw [inR (by unfold NativeRustcVm.NoWrap; omega)] at hq'; omega
  · rw [inR (by unfold NativeRustcVm.NoWrap; omega)] at hq'; omega
  · rw [inR (by unfold NativeRustcVm.NoWrap; omega)] at hq'; omega

/-- The frame's bytes are none of the `TState`'s or its decoded area's. -/
theorem Parts.frame_not_t {q : BitVec 64} (hq : NativeRustcVm.InRange (fb m0) 520 q) :
    ¬ NativeRustcVm.InRange (tA m0) tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q := by
  have hf := h.fbn
  have hr := h.rsp
  rw [inR (by unfold NativeRustcVm.NoWrap; omega), hf] at hq
  have ht := h.t_nat
  have ha := h.a_nat
  refine ⟨fun hq' ↦ ?_, fun hq' ↦ ?_⟩
  · rw [inR (by unfold NativeRustcVm.NoWrap; omega)] at hq'; omega
  · rw [inR (by unfold NativeRustcVm.NoWrap; omega)] at hq'; omega

/-- The frame's bytes below its return address are the stack's. -/
theorem Parts.frame_stack {q : BitVec 64} (hq : NativeRustcVm.InRange (fb m0) 512 q) :
    NativeRustcVm.InRange (stackBelow m0 verifyStackedOpeningStack) verifyStackedOpeningStack q := by
  have hr := h.rsp
  rw [h.inFrame (n := 512) (by omega)] at hq
  rw [h.inStack]
  obtain ⟨h1, h2⟩ := hq
  exact ⟨Nat.le_trans (Nat.sub_le_sub_left (by decide) _) h1,
    Nat.lt_of_lt_of_eq h2 (Nat.sub_add_cancel (Nat.le_trans (by decide) hr.1))⟩

/-- A callee's stack below the frame: the stack's, none of the frame's. -/
theorem Parts.callee_stack {st : MachineData} (hsp : rspOf st = fb m0) {N' : Nat}
    (hN' : 512 + N' ≤ verifyStackedOpeningStack) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow st N') N' q) :
    NativeRustcVm.InRange (stackBelow m0 verifyStackedOpeningStack) verifyStackedOpeningStack q ∧ ¬ NativeRustcVm.InRange (fb m0) 520 q := by
  have hr := h.rsp
  rw [stack_eq] at hN'
  have := inRange_callee (m0 := m0) (n := verifyStackedOpeningStack) (F := 512) hsp (by omega)
    (by rw [stack_eq]; omega) (by rw [stack_eq]; omega) hq
  exact this

/-- An output's bytes are none of a callee's stack's. -/
theorem Parts.outs_not_stack {q : BitVec 64} (hq : outs m0 q) :
    ¬ NativeRustcVm.InRange (stackBelow m0 verifyStackedOpeningStack) verifyStackedOpeningStack q := by
  have hr := h.rsp
  have ht := h.t_nat
  have hp := h.p_nat
  have hc := h.sc_nat
  rw [h.inStack]
  rcases hq with hq | hq | hq
  · rw [inR (by unfold NativeRustcVm.NoWrap; omega)] at hq; omega
  · rw [inR (by unfold NativeRustcVm.NoWrap; omega)] at hq; omega
  · rw [inR (by unfold NativeRustcVm.NoWrap; omega)] at hq; omega

/-- **An input's bytes** are none of what may change. -/
theorem Parts.in_not_wr {r : NativeRustcVm.Region} (hr : r ∈ vsoInputs m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange r.addr r.size q) : ¬ Wr m0 q := by
  have hi := h.ins r hr
  have hn := h.in_nat hr
  have hs := h.sb
  have hR := h.rsp
  rw [inR (by unfold NativeRustcVm.NoWrap; omega)] at hq
  rintro ((hq' | hq' | hq') | hq')
  · exact not_inRange_of_apart hi.2.2.1 hn.1 h.p_nat.1 ((inR hn.1).mpr hq) hq'
  · exact not_inRange_of_apart hi.2.2.2 hn.1 h.sc_nat.1 ((inR hn.1).mpr hq) hq'
  · exact not_inRange_of_apart hi.2.1 hn.1 h.t_nat.1 ((inR hn.1).mpr hq) hq'
  · rw [h.inStack] at hq'
    omega

/-- The stack arguments' bytes are none of what may change. -/
theorem Parts.arg_not_wr {q : BitVec 64}
    (hq : NativeRustcVm.InRange (rspOf m0 + 8#64) 24 q) : ¬ Wr m0 q := by
  have hs := h.sb
  have hR := h.rsp
  have e : (rspOf m0 + 8#64).toNat = R0 m0 + 8 := by
    rw [BitVec.toNat_add]; simp; omega
  have hnw : NativeRustcVm.NoWrap (rspOf m0 + 8#64) 24 := by
    unfold NativeRustcVm.NoWrap; omega
  rintro ((hq' | hq' | hq') | hq')
  · exact not_inRange_of_apart h.argp hnw h.p_nat.1 hq hq'
  · exact not_inRange_of_apart h.argsc hnw h.sc_nat.1 hq hq'
  · exact not_inRange_of_apart h.argt hnw h.t_nat.1 hq hq'
  · rw [inR hnw, e] at hq
    rw [h.inStack] at hq'
    omega

/-! ## Blocks and calls -/

/-- **A block** writing only the frame below its return address keeps `Ok`, the frame's other
bytes and every byte outside the frame. -/
theorem Ok.block {st st' : MachineData} {o o' : Nat} (hok : Ok m0 st o)
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (frameEnv m0 st 512 rest vars ret).WF)
    (hm : Match (frameEnv m0 st 512 rest vars ret) S st') (hS : MidOk 512 o' slots S = true)
    (hw : ∀ w ∈ S.mem, w.r = 0) :
    Ok m0 st' o' ∧ NativeRustcVm.SameOutside st.dmem st'.dmem (NativeRustcVm.InRange (fb m0) 512) := by
  have hlow := sameOutside_low hwf hm (r := 0) rfl (hi := 512) (by omega)
    fun w hw' ↦ ⟨hw w hw', by
      have := NativeRustcVmX64.Sumcheck.belowRet_of_mid hS
      exact belowRet_spec this w hw' (hw w hw')⟩
  refine ⟨⟨Frame.of_block hok.fr hwf hm hS slots_le, fun q hq ↦ ?_⟩, hlow⟩
  rw [hlow q fun h' ↦ hq (.inr (h.frame_stack h'))]
  exact hok.so q hq

/-- **A call** writing its stack and some of the outputs: `Ok` after it, the frame's bytes
unchanged. -/
theorem Ok.call {st st' : MachineData} (hok : Ok m0 st 0) (hs : Saved st st')
    (hrsp : rspOf st' = rspOf st + 8#64) {N' : Nat} (hN' : 512 + N' ≤ verifyStackedOpeningStack)
    {Rw : BitVec 64 → Prop} (hR : ∀ q, Rw q → outs m0 q)
    (hso : NativeRustcVm.SameOutside st.dmem st'.dmem
      (fun q ↦ Rw q ∨ NativeRustcVm.InRange (stackBelow st N') N' q)) :
    Ok m0 st' 8 ∧ FrameSame m0 st.dmem st'.dmem := by
  have hsp : rspOf st = fb m0 := by rw [hok.fr.sp, off_zero]
  have hnot : ∀ q, (Rw q ∨ NativeRustcVm.InRange (stackBelow st N') N' q) →
      ¬ NativeRustcVm.InRange (stackBelow m0 512) (512 + 8) q := by
    rintro q (hq | hq) hf
    · exact h.frame_not_outs hf (hR q hq)
    · exact (h.callee_stack hsp hN' hq).2 hf
  have hfnw : NativeRustcVm.NoWrap (stackBelow m0 512) (512 + 8) := by
    have : (stackBelow m0 512).toNat = R0 m0 - 512 := h.fbn
    have := h.rsp; unfold NativeRustcVm.NoWrap; omega
  refine ⟨⟨Frame.call hok.fr hs hrsp hso hnot hfnw slots_le, fun q hq ↦ ?_⟩,
    fun q hq ↦ hso q (hnot q · hq)⟩
  rw [hso q ?_]
  · exact hok.so q hq
  · rintro (hq' | hq')
    · exact hq (.inl (hR q hq'))
    · exact hq (.inr (h.callee_stack hsp hN' hq').1)

/-- An input's bytes in a state of the frame. -/
theorem Ok.same_in {st : MachineData} {o : Nat} (hok : Ok m0 st o) {r : NativeRustcVm.Region}
    (hr : r ∈ vsoInputs m0) : NativeRustcVm.Layout.Same m0.dmem st.dmem r.addr r.size := by
  have hn := h.in_nat hr
  refine fun j hj ↦ hok.so _ (h.in_not_wr hr ?_)
  exact (inR hn.1).mpr ⟨by rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega,
    by rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega⟩

omit [Labels] h in
theorem arg_addr (i : Nat) :
    rspOf m0 + 8#64 + BitVec.ofNat 64 (8 * i) = rspOf m0 + BitVec.ofNat 64 (8 + 8 * i) := by
  rw [BitVec.add_assoc, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]

/-- A stack argument in a state of the frame. -/
theorem Ok.arg {st : MachineData} {o : Nat} (hok : Ok m0 st o) {i : Nat} (hi : i < 3) :
    NativeRustcVm.WordAt st.dmem (rspOf m0 + 8#64 + BitVec.ofNat 64 (8 * i))
      (UInt64.ofBitVec (stackArg m0 i)) := by
  have hR := h.rsp
  have e : (rspOf m0 + 8#64).toNat = R0 m0 + 8 := by
    rw [BitVec.toNat_add]; simp; omega
  have hnw : NativeRustcVm.NoWrap (rspOf m0 + 8#64) 24 := by
    unfold NativeRustcVm.NoWrap; omega
  have hm : NativeRustcVm.Mapped m0.dmem (rspOf m0 + 8#64 + BitVec.ofNat 64 (8 * i)) 8 :=
    fun j hj ↦ by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact h.args.1 _ (by omega)
  have hw : NativeRustcVm.WordAt m0.dmem (rspOf m0 + 8#64 + BitVec.ofNat 64 (8 * i))
      (UInt64.ofBitVec (stackArg m0 i)) := by
    have := NativeRustcVm.wordAt_of_mapped hm
    rw [arg_addr] at this ⊢; exact this
  refine NativeRustcVm.BytesAt.of_sameOutside hw hok.so fun j hj hq ↦ h.arg_not_wr ?_ hq
  rw [NativeRustcVm.length_wordBytes] at hj
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact NativeRustcVm.inRange_add (by omega) (by omega)

end

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
