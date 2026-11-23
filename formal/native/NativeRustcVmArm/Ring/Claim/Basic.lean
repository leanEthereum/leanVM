module

public import NativeRustcVmArm.Code.Vm.EqEvalFnOfEqAbove.Names
public import NativeRustcVmArm.Ring.OptOut
public import NativeRustcVmArm.Ring.Claim.Exec
public import NativeRustcVmArm.Ring.Column.Basic
public import NativeRustcVmArm.Ring.Switch.Basic
public import NativeRustcVmArm.Whir.MathFrame

/-!
# `ring_claim_weight`: its frame, the prologue and `eq_eval_fn`

From the entry state `m0` (the `Option<EW>` at X0, the placement X1, X2, `r` X3, X4, the
coefficients X5, `x` X6, X7): the frame (`CFr`: 112 bytes, X19 to X26 and X30 saved from byte
`32`, `ring_weight`'s `Option<EW>` at byte `8`), the state after `eq_eval_fn` (`Mid1`).
`stepEntry` (`b0`): the arguments of `eq_above` (`eval_satSub`, `eval_shr`, `eval_above`,
`eval_min`: the values the executor computes), `eq_eval_fn`, `eqAbove`.
-/

namespace NativeRustcVmArm.Ring.Claim

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Vm.RingClaimWeight NativeRustcVmArm.Whir

@[expose] public section

/-- The saved registers' slots. -/
def slots : List (Nat × XReg) :=
  [(32, .X30), (48, .X26), (56, .X25), (64, .X24), (72, .X23), (80, .X22), (88, .X21),
    (96, .X20), (104, .X19)]

/-- The callee-saved registers the prologue does not save. -/
def keep : List XReg := [.X27, .X28, .X29]

/-- The output's address. -/
def oA (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec

/-- The frame (the output written by the last blocks only). -/
abbrev CFr (m0 m : MachineData) : Prop :=
  Fr m0 112 ringClaimWeightStack slots keep (fun _ ↦ False) m

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := base m0 112

/-- The environment between the calls: the frame. -/
abbrev envM (m0 m : MachineData) : Env := Env.ofMachine m [(fb m0, 112)]

/-- The environment after `ring_weight`: the frame, the output. -/
abbrev envR (m0 m : MachineData) : Env := Env.ofMachine m [(fb m0, 112), (oA m0, 24)]

/-- `x`. -/
def xOf (m0 : MachineData) : Array EW := slice m0 m0.regs.X6 m0.regs.X7

/-- `eq_above(p, x)`. -/
def eqOf (m0 : MachineData) : EW := eqAbove (placementArg m0) (xOf m0)

/-- **After `eq_eval_fn`**: the frame, `eq_above(p, x)` in X0, X1, the output in X19, `x` in
X22, the coefficients in X23, `r` in X25, X24, `min(vc, |x|)` in X26. -/
structure Mid1 (m0 m : MachineData) : Prop where
  fr : CFr m0 m
  ret : ewRet m = eqOf m0
  x19 : m.regs.getXReg .X19 = m0.regs.X0
  x22 : m.regs.getXReg .X22 = m0.regs.X6
  x23 : m.regs.getXReg .X23 = m0.regs.X5
  x24 : m.regs.getXReg .X24 = m0.regs.X4
  x25 : m.regs.getXReg .X25 = m0.regs.X3
  x26 : (m.regs.getXReg .X26).toNat = min m0.regs.X1.toNat m0.regs.X7.toNat

end

/-! ## The values `b0` computes -/

section
variable [Labels] (env : Env)

/-- `subs; csel lo`: the saturating difference. -/
theorem eval_satSub (r s : XReg) :
    ((Sym.ite (.cmp .ult .W64 (.reg r) (.reg s)) (.lit 0) (.bin .sub .W64 (.reg r) (.reg s))).eval
      env).toNat = (env.regs r).toNat - (env.regs s).toNat := by
  simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
  split <;> rename_i hc <;> simp only [BitVec.ult, decide_eq_true_eq] at hc
  · simp; omega
  · rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]

/-- `lsr; cmp #63; csel hi`: `shr`. -/
theorem eval_shr (r s : XReg) :
    ((Sym.ite (.and (.not (.cmp .ult .W64 (.reg s) (.lit 63)))
        (.not (.cmp .eq .W64 (.reg s) (.lit 63))))
      (.lit 0) (.bin .lsrv .W64 (.reg r) (.reg s))).eval env).toNat =
      (env.regs r).toNat >>> (env.regs s).toNat := by
  simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
  have hr := (env.regs r).isLt
  split <;> rename_i hc
  · simp only [Bool.and_eq_true, Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not,
      beq_eq_false_iff_ne, ne_eq] at hc
    have : 63 < (env.regs s).toNat := by
      obtain ⟨h1, h2⟩ := hc
      have h3 : (env.regs s).toNat ≠ 63 := fun h ↦ h2 (BitVec.eq_of_toNat_eq (by simpa using h))
      simp at h1; omega
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt
      (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) (by omega)))]
    rfl
  · simp only [Bool.and_eq_true, Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not,
      beq_eq_false_iff_ne, ne_eq, not_and, Decidable.not_not] at hc
    have : (env.regs s).toNat ≤ 63 := by
      by_cases h : (env.regs s).toNat < 63
      · omega
      · have := hc (by simpa using h); have := congrArg BitVec.toNat this; simp at this; omega
    simp [BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt (show (env.regs s).toNat < 64 by omega)]

/-- `add x8, x6, x1, lsl #4; cmp x1, x7; csel x8, x9, x8, hi`: the slice's rest, or `8`. -/
theorem eval_above (r s n : XReg) :
    (Sym.ite (.and (.not (.cmp .ult .W64 (.reg s) (.reg n))) (.not (.cmp .eq .W64 (.reg s) (.reg n))))
      (.lit 8) (.bin .add .W64 (.reg r) (.un (.shift .LSL 4) .W64 (.reg s)))).eval env =
      if (env.regs n).toNat < (env.regs s).toNat then 8#64
      else env.regs r + BitVec.ofNat 64 (16 * (env.regs s).toNat) := by
  simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, UnOp.apply, shiftW, low_W64, ext_W64]
  split <;> rename_i hc
  · simp only [Bool.and_eq_true, Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not,
      beq_eq_false_iff_ne, ne_eq] at hc
    obtain ⟨h1, h2⟩ := hc
    have h3 : (env.regs s).toNat ≠ (env.regs n).toNat := fun h ↦ h2 (BitVec.eq_of_toNat_eq h)
    simp at h1
    rw [ite_eq_left (show (env.regs n).toNat < (env.regs s).toNat by omega)]
  · simp only [Bool.and_eq_true, Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not,
      beq_eq_false_iff_ne, ne_eq, not_and, Decidable.not_not] at hc
    have : ¬ (env.regs n).toNat < (env.regs s).toNat := by
      intro h
      have := congrArg BitVec.toNat (hc (by simp; omega))
      omega
    rw [ite_eq_right this]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega

/-- `cmp; csel lo`: the minimum. -/
theorem eval_min (s n : XReg) :
    ((Sym.ite (.cmp .ult .W64 (.reg s) (.reg n)) (.reg s) (.reg n)).eval env).toNat =
      min (env.regs s).toNat (env.regs n).toNat := by
  simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64]
  split <;> rename_i hc <;> simp only [BitVec.ult, decide_eq_true_eq] at hc <;> omega

end

/-! ## The frame -/

public section

variable {m0 : MachineData}

theorem stack_eq : ringClaimWeightStack = 1392 := rfl

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 112 := by decide

theorem keep_cs : ∀ r ∈ keep, calleeSaved r = true := by decide

theorem xOf_size : (xOf m0).size = m0.regs.X7.toNat := by simp [xOf, slice]

section
variable (h : RingClaimWeightPre m0)
include h

theorem hN : ringClaimWeightStack ≤ m0.regs.SP.toNat := h.1.2.1

theorem fbN : (fb m0).toNat = m0.regs.SP.toNat - 112 :=
  base_toNat (by have := hN h; rw [stack_eq] at this; omega)

theorem fbw : NoWrap (fb m0) 112 := base_noWrap (by have := hN h; rw [stack_eq] at this; omega)

theorem out_frame : Apart (oA m0) 24 (fb m0) 112 :=
  apart_frame (hN h) (by decide) h.2.2.2.2.2.2.2

/-- A range in the frame is apart from a callee's stack. -/
theorem apart_callee {m : MachineData} (hfr : CFr m0 m) {o n N' : Nat} (hon : o + n ≤ 112)
    (hle : 112 + N' ≤ ringClaimWeightStack) :
    Apart (fb m0 + BitVec.ofNat 64 o) n (stackBelow m N') N' := by
  have h1 := fbN h
  have h2 := hN h
  have hSP := m0.regs.SP.toNat_lt
  rw [stackBelow_eq hfr.sp (by omega)]
  have h3 := base_toNat (m0 := m0) (F := 112 + N') (by omega)
  unfold Apart
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

/-- Bytes apart from the stack are the entry's in every state of the frame. -/
theorem same_of {m : MachineData} (hfr : CFr m0 m) {a : BitVec 64} {n : Nat}
    (ha : Apart a n (stackBelow m0 ringClaimWeightStack) ringClaimWeightStack) (hw : NoWrap a n)
    {j : Nat} (hj : j < n) :
    m.dmem.get? (a + BitVec.ofNat 64 j) = m0.dmem.get? (a + BitVec.ofNat 64 j) :=
  hfr.same _ fun hq ↦ hq.elim (fun hq ↦ NativeRustcVm.Apart.not_inRange_add ha hw
    (base_noWrap (hN h)) hj hq) id

/-- A slice apart from the stack reads as at the entry in every state of the frame. -/
theorem slice_same {m : MachineData} (hfr : CFr m0 m) {a n : UInt64}
    (ha : SliceOk m0 a n ringClaimWeightStack) : slice m a n = slice m0 a n := by
  unfold slice
  rw [NativeRustcVm.ewsOf_congr fun j hj ↦ same_of h hfr ha.2 ha.1.2 hj]

omit h in
/-- A slice of the entry's, readable in every state of the frame. -/
theorem readable_of {m : MachineData} (hfr : CFr m0 m) {a : BitVec 64} {n : Nat}
    (ha : Readable m0 a n) : Readable m a n :=
  ⟨fun j hj ↦ hfr.kept _ (ha.1 j hj), ha.2⟩

end

theorem envM_wf (h : RingClaimWeightPre m0) {m : MachineData} (hfr : CFr m0 m) :
    (envM m0 m).WF :=
  Env.wf_of ⟨⟨fun i hi ↦ hfr.kept _ (frame_mapped h.1 (by decide) i hi), fbw h⟩, trivial⟩
    (List.pairwise_singleton _ _)

theorem envR_wf (h : RingClaimWeightPre m0) {m : MachineData} (hfr : CFr m0 m) :
    (envR m0 m).WF :=
  Env.wf_of ⟨⟨fun i hi ↦ hfr.kept _ (frame_mapped h.1 (by decide) i hi), fbw h⟩,
    ⟨fun i hi ↦ hfr.kept _ (h.2.2.2.2.2.2.1.1 i hi), h.2.2.2.2.2.2.1.2⟩, trivial⟩
    (List.pairwise_pair.mpr (out_frame h).symm)

/-! ## `eq_above` -/

/-- The elements from `x + 16·vc`: `x`'s from `vc`. -/
theorem slice_above {m : MachineData} {a n : UInt64} {v : Nat} (hv : v ≤ n.toNat)
    {a' n' : UInt64} (ha' : a'.toBitVec = a.toBitVec + BitVec.ofNat 64 (16 * v))
    (hn' : n'.toNat = n.toNat - v) :
    slice m a' n' = (slice m a n).extract v (slice m a n).size := by
  unfold slice
  rw [ha', hn', ← Switch.ewsOf_drop m.dmem a.toBitVec (n.toNat - v) v,
    show v + (n.toNat - v) = n.toNat by omega]
  simp

/-- An empty rest when `vc > |x|`. -/
theorem slice_above_nil {m : MachineData} {a n : UInt64} {v : Nat} (hv : n.toNat < v)
    {a' n' : UInt64} (hn' : n'.toNat = 0) :
    slice m a' n' = (slice m a n).extract v (slice m a n).size := by
  unfold slice
  rw [hn']
  apply Array.ext (by simp; omega) fun i h1 h2 ↦ by simp at h1

/-- `x.get(..vc).unwrap_or(x)`: the first `min(vc, |x|)` elements. -/
theorem slice_low {m : MachineData} {a n : UInt64} {v : Nat} {n' : UInt64}
    (hn' : n'.toNat = min v n.toNat) : slice m a n' = (slice m a n).extract 0 v := by
  unfold slice
  rw [hn']
  apply Array.ext (by simp) fun i h1 h2 ↦ by simp

section
variable [Labels]

theorem matchM (h : RingClaimWeightPre m0) {m : MachineData} (hfr : CFr m0 m) :
    Match (envM m0 m) midS m :=
  match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.1 (by decide) (by decide), trivial⟩
    (by rw [hfr.sp]; simp [Sym.eval]) trivial trivial trivial trivial

end

variable [Host] {k : Nat}

theorem hb {ds : List Directive} {j : Nat} (h : ds.IsInfixAt code j) (hne : ds ≠ [])
    (hp : Placed code k) : ds.IsInfixAt Host.prog (k + j) :=
  h.trans hp.1 hne

/-- **The prologue and `eq_eval_fn`** (`b0`). -/
theorem stepEntry (hp : Placed code k) (h : RingClaimWeightPre m0)
    (hee : Spec (Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre
      EqEvalFnOfEqAbovePost)
    {R : MachineState → Prop}
    (cont : ∀ m1, Mid1 m0 m1 → Eventually (step1 Host.exe) R ⟨m1, Host.addrOf (k + NativeRustcVmArm.Vm.RingClaimWeight.b1Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.RingClaimWeight.b0Offset)⟩ := by
  have hfw := fbw h
  have hfN := fbN h
  have hN' := hN h
  rw [stack_eq] at hN'
  have hSP := m0.regs.SP.toNat_lt
  have hwf : (Env.ofMachine m0 [(fb m0, 112)]).WF :=
    Env.wf_of ⟨⟨frame_mapped h.1 (by decide), hfw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine m0 [(fb m0, 112)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.1 (by decide) (by decide), trivial⟩
      (by
        show m0.regs.SP.toBitVec = fb m0 + BitVec.ofInt 64 (112 : Nat)
        rw [BitVec.ofInt_natCast, base_add_eq])
      trivial trivial trivial trivial
  refine exec_then (hb b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun st hm1 hpc ↦ ?_
  have hfr1 : CFr m0 st.data :=
    Fr.ofPrologue (rs := []) (hN h) (by decide) hm1 hwf rfl (by decide +kernel) slots_le
      (Column.mem_low (by decide +kernel)) (fun r hr ↦ by
        simp only [keep, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> rfl)
  have e0 : st.data.regs.X0.toNat = m0.regs.X7.toNat - m0.regs.X1.toNat := by
    have := congrArg BitVec.toNat (hm1.regs .X0 _ rfl)
    rw [eval_satSub] at this
    exact this
  have e3 : st.data.regs.X3.toNat = m0.regs.X7.toNat - m0.regs.X1.toNat := by
    have := congrArg BitVec.toNat (hm1.regs .X3 _ rfl)
    rw [eval_satSub] at this
    exact this
  have e1 : st.data.regs.X1.toNat = m0.regs.X2.toNat >>> m0.regs.X1.toNat := by
    have := congrArg BitVec.toNat (hm1.regs .X1 _ rfl)
    rw [eval_shr] at this
    exact this
  have e2 : st.data.regs.X2.toBitVec = if m0.regs.X7.toNat < m0.regs.X1.toNat then 8#64
      else m0.regs.X6.toBitVec + BitVec.ofNat 64 (16 * m0.regs.X1.toNat) := by
    have := hm1.regs .X2 _ rfl
    rw [eval_above] at this
    exact this
  have e26 : (st.data.regs.getXReg .X26).toNat = min m0.regs.X1.toNat m0.regs.X7.toNat := by
    have := congrArg BitVec.toNat (hm1.regs .X26 _ rfl)
    rw [eval_min] at this
    exact this
  have hx := h.2.2.2.2.2.1
  have hx64 := h.2.2.1
  -- `eq_eval_fn`'s slice: `x`'s rest from `vc`
  have hsl : slice st.data st.data.regs.X2 st.data.regs.X3 =
      (xOf m0).extract m0.regs.X1.toNat (xOf m0).size := by
    unfold xOf
    rw [← slice_same h hfr1 hx]
    by_cases hlt : m0.regs.X7.toNat < m0.regs.X1.toNat
    · exact slice_above_nil hlt (by rw [e3]; omega)
    · rw [ite_eq_right hlt] at e2
      exact slice_above (by omega) e2 e3
  have hpre : EqEvalFnOfEqAbovePre st.data := by
    refine ⟨hfr1.stackOk h.1 (by decide) (by decide), by omega, ?_⟩
    have hxs : OffStack st.data m0.regs.X6.toBitVec (16 * m0.regs.X7.toNat) eqEvalFnStack :=
      hfr1.apart (hN h) hx.2 (by decide)
    unfold SliceOk
    by_cases hlt : m0.regs.X7.toNat < m0.regs.X1.toNat
    · rw [ite_eq_left hlt] at e2
      rw [show st.data.regs.X3.toNat = 0 by omega, Nat.mul_zero]
      refine ⟨⟨fun j hj ↦ absurd hj (by omega), by unfold NoWrap; omega⟩, ?_⟩
      unfold OffStack Apart
      rw [show eqEvalFnStack = 640 from rfl] at *
      rw [e2, stackBelow_eq hfr1.sp (by omega), base_toNat (by omega)]
      left
      simp
      omega
    · rw [ite_eq_right hlt] at e2
      rw [e2, e3, show 16 * (m0.regs.X7.toNat - m0.regs.X1.toNat) =
        16 * m0.regs.X7.toNat - 16 * m0.regs.X1.toNat by omega]
      exact ⟨Readable.sub (readable_of hfr1 hx.1) (by omega), OffStack.sub hxs hx.1.2 (by omega)⟩
  have hnil : ∀ q, ¬InRange (0 : BitVec 64) 0 q := fun q hq ↦ by unfold InRange at hq; omega
  refine Fr.leafAt hfr1 (hN h) (N' := eqEvalFnStack) (by decide) keep_cs slots_le
    (fun _ h ↦ h.elim) hee hpc hpre
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq ↦ hq.elim
      (fun hq ↦ absurd hq (hnil q)) .inl, hq.2.2⟩)
    fun m1 hfr2 hq hcs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingClaimWeight.b0Offset + b0.length = k + NativeRustcVmArm.Vm.RingClaimWeight.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingClaimWeight.b0_next]]
  refine cont m1 ⟨hfr2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hq.1, hsl, e1, show st.data.regs.X0.toNat = (xOf m0).size - m0.regs.X1.toNat by
      rw [xOf_size, e0]]
    rfl
  · rw [hcs .X19 rfl]; exact Column.reg_of hm1 (v := .reg .X0) rfl rfl
  · rw [hcs .X22 rfl]; exact Column.reg_of hm1 (v := .reg .X6) rfl rfl
  · rw [hcs .X23 rfl]; exact Column.reg_of hm1 (v := .reg .X5) rfl rfl
  · rw [hcs .X24 rfl]; exact Column.reg_of hm1 (v := .reg .X4) rfl rfl
  · rw [hcs .X25 rfl]; exact Column.reg_of hm1 (v := .reg .X3) rfl rfl
  · rw [hcs .X26 rfl]; exact e26

end

end NativeRustcVmArm.Ring.Claim
