module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EWSqIter.Names
public import NativeRustcVmArm.Code.Vm.PolyEval.Names
public import NativeRustcVmArm.Ring.Target.Env

/-!
# `ring_target`: the calls after the images loop

A block ending in a call to `EW::sq_iter` (`sqStep`: the count a literal, the element from the
table), `poly_eval` (`polyStep`: the images' copy at frame byte `208`, the point from the table)
or `EW::mul` (`mulStep`): the table's entries `r0`, `r1` its result, X0 and X1 added to the
description.
-/

namespace NativeRustcVmArm.Ring.Target

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring

public section

variable {m0 : MachineData}

theorem tval_reg [Labels] (rs : List (BitVec 64 × Nat)) (m : MachineData) (r : XReg) :
    tval rs m (.reg r) = m.regs.getXReg r := rfl

/-- An argument register from the table. -/
theorem arg_of [Labels] {D : List (Sym × Nat)} {S' : SState} {m st : MachineData}
    (hH : Holds (rsT m0) (tv m0) D m) (hm1 : Match (Env.ofMachine m (rsT m0)) S' st) {r : XReg}
    {a : Nat} (ht : trackOk szT S' D [(.reg r, a)] = true) : st.regs.getXReg r = tv m0 a := by
  have := hH.after szT_eq hm1 ht _ (List.mem_singleton_self _)
  rwa [tval_reg] at this

/-- The description with the call's result in X0, X1. -/
theorem holds_ret [Labels] {D : List (Sym × Nat)} {m : MachineData}
    (hH : Holds (rsT m0) (tv m0) D m) {r0 r1 : Nat} (h0 : m.regs.getXReg .X0 = tv m0 r0)
    (h1 : m.regs.getXReg .X1 = tv m0 r1) :
    Holds (rsT m0) (tv m0) ((.reg .X0, r0) :: (.reg .X1, r1) :: D) m := by
  intro p hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | rfl | hp
  · exact h0
  · exact h1
  · exact hH p hp

variable [Host]

/-- **A block calling `EW::sq_iter`**. -/
theorem sqStep (h : P m0) (hsq : Spec (Labels.label NativeRustcVmArm.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost)
    {D D' : List (Sym × Nat)} {S0 S' : SState} {ds : List Directive} {i c a b r0 r1 : Nat}
    {R : MachineState → Prop} {m : MachineData}
    (hk : ds.IsInfixAt Host.prog i) (hrun : exec ds S0 = some (S', .call NativeRustcVmArm.Vm.EWSqIter.entryLabel))
    (hst : St m0 D m) (hm : Match (Env.ofMachine m (rsT m0)) S0 m) (hsp : S'.sp = S0.sp)
    (hwr : wr208 S' = true) (htr : trackOk szT S' D D' = true)
    (hsafe : D'.all (fun p ↦ callSafe szT p.1) = true) (h0 : S'.reg .X0 = some (.lit c))
    (hc : c < 2 ^ 64) (ha : trackOk szT S' D [(.reg .X1, a)] = true)
    (hb : trackOk szT S' D [(.reg .X2, b)] = true)
    (hr : EW.sqIter c ⟨tv m0 a, tv m0 b⟩ = ⟨tv m0 r0, tv m0 r1⟩)
    (cont : ∀ m2, St m0 ((.reg .X0, r0) :: (.reg .X1, r1) :: D') m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ :=
  stepT h hk hrun hst hm hsp hwr htr hsafe (N' := ewSqIterStack) (by decide) hsq
    (fun _ _ hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun _ h ↦ .inl h, hq.2.2.2⟩)
    (fun st _ hfr ↦ hfr.stackOk h.st (by decide) (by decide))
    fun st m2 hm1 hq _ hst2 ↦ cont m2 ⟨hst2.fr, by
      obtain ⟨q0, q1, -⟩ := hq
      have e0 : st.regs.X0 = c.toUInt64 := by
        apply UInt64.toBitVec_inj.mp
        rw [show st.regs.X0 = st.regs.getXReg .X0 from rfl, hm1.regs .X0 _ h0]
        rfl
      have e1 : st.regs.X1 = tv m0 a := arg_of hst.hd hm1 ha
      have e2 : st.regs.X2 = tv m0 b := arg_of hst.hd hm1 hb
      rw [e0, e1, e2, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' hc, hr] at q0 q1
      exact holds_ret hst2.hd q0 q1, hst2.copy⟩

/-- **A block calling `EW::mul`**. -/
theorem mulStep (h : P m0) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {D D' : List (Sym × Nat)} {S0 S' : SState} {ds : List Directive} {i a0 a1 b0 b1 r0 r1 : Nat}
    {R : MachineState → Prop} {m : MachineData}
    (hk : ds.IsInfixAt Host.prog i) (hrun : exec ds S0 = some (S', .call NativeRustcVmArm.Vm.EWMul.entryLabel))
    (hst : St m0 D m) (hm : Match (Env.ofMachine m (rsT m0)) S0 m) (hsp : S'.sp = S0.sp)
    (hwr : wr208 S' = true) (htr : trackOk szT S' D D' = true)
    (hsafe : D'.all (fun p ↦ callSafe szT p.1) = true)
    (ha0 : trackOk szT S' D [(.reg .X0, a0)] = true)
    (ha1 : trackOk szT S' D [(.reg .X1, a1)] = true)
    (hb0 : trackOk szT S' D [(.reg .X2, b0)] = true)
    (hb1 : trackOk szT S' D [(.reg .X3, b1)] = true)
    (hr : EW.mul ⟨tv m0 a0, tv m0 a1⟩ ⟨tv m0 b0, tv m0 b1⟩ = ⟨tv m0 r0, tv m0 r1⟩)
    (cont : ∀ m2, St m0 ((.reg .X0, r0) :: (.reg .X1, r1) :: D') m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ :=
  stepT h hk hrun hst hm hsp hwr htr hsafe (N' := ewMulStack) (by decide) hmul
    (fun _ _ hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun _ h ↦ .inl h, hq.2.2.2⟩)
    (fun st _ hfr ↦ hfr.stackOk h.st (by decide) (by decide))
    fun st m2 hm1 hq _ hst2 ↦ cont m2 ⟨hst2.fr, by
      obtain ⟨q0, q1, -⟩ := hq
      have e0 : st.regs.X0 = tv m0 a0 := arg_of hst.hd hm1 ha0
      have e1 : st.regs.X1 = tv m0 a1 := arg_of hst.hd hm1 ha1
      have e2 : st.regs.X2 = tv m0 b0 := arg_of hst.hd hm1 hb0
      have e3 : st.regs.X3 = tv m0 b1 := arg_of hst.hd hm1 hb1
      rw [e0, e1, e2, e3, hr] at q0 q1
      exact holds_ret hst2.hd q0 q1, hst2.copy⟩

/-- **A block calling `poly_eval`** on the images' copy; the callee-saved registers `E` the block
computed (`hE`) kept across the call. -/
theorem polyStep (h : P m0) (hpoly : Spec (Labels.label NativeRustcVmArm.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    {D D' E : List (Sym × Nat)} {S0 S' : SState} {ds : List Directive} {i a b r0 r1 : Nat}
    {R : MachineState → Prop} {m : MachineData}
    (hk : ds.IsInfixAt Host.prog i) (hrun : exec ds S0 = some (S', .call NativeRustcVmArm.Vm.PolyEval.entryLabel))
    (hst : St m0 D m) (hm : Match (Env.ofMachine m (rsT m0)) S0 m) (hsp : S'.sp = S0.sp)
    (hwr : wr208 S' = true) (htr : trackOk szT S' D D' = true)
    (hsafe : D'.all (fun p ↦ callSafe szT p.1) = true)
    (h0 : S'.reg .X0 = some (.ptr 0 208)) (h1 : S'.reg .X1 = some (.lit 64))
    (ha : trackOk szT S' D [(.reg .X2, a)] = true)
    (hb : trackOk szT S' D [(.reg .X3, b)] = true)
    (hr : polyEval (imgs m0) ⟨tv m0 a, tv m0 b⟩ = ⟨tv m0 r0, tv m0 r1⟩)
    (hEr : ∀ p ∈ E, ∃ r, p.1 = .reg r ∧ calleeSaved r = true)
    (hE : ∀ st, Match (Env.ofMachine m (rsT m0)) S' st → Holds (rsT m0) (tv m0) E st)
    (cont : ∀ m2, St m0 ((.reg .X0, r0) :: (.reg .X1, r1) :: (E ++ D')) m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hfbN := h.fbN
  have hfbw := h.fbw
  have hN := h.hN
  have he := stack_eq
  have hSP := m0.regs.SP.toNat_lt
  unfold NoWrap at hfbw
  have ex0 : ∀ {st : MachineData}, Match (Env.ofMachine m (rsT m0)) S' st →
      st.regs.X0.toBitVec = fb m0 + BitVec.ofNat 64 208 := fun {st} hm1 ↦ by
    rw [show st.regs.X0 = st.regs.getXReg .X0 from rfl, hm1.regs .X0 _ h0]
    rfl
  have ex1 : ∀ {st : MachineData}, Match (Env.ofMachine m (rsT m0)) S' st →
      st.regs.X1 = 64 := fun {st} hm1 ↦ by
    apply UInt64.toBitVec_inj.mp
    rw [show st.regs.X1 = st.regs.getXReg .X1 from rfl, hm1.regs .X1 _ h1]
    rfl
  refine stepT h hk hrun hst hm hsp hwr htr hsafe (N' := polyEvalStack) (by decide) hpoly
    (fun _ _ hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun _ h ↦ Or.elim h (fun h ↦ ?_) .inl,
      hq.2.2⟩) (fun st hm1 hfr ↦ ⟨hfr.stackOk h.st (by decide) (by decide), by rw [ex1 hm1]; decide,
        ⟨⟨fun j hj ↦ ?_, ?_⟩, ?_⟩⟩)
    fun st m2 hm1 hq hcp hst2 ↦ cont m2 ⟨hst2.fr, by
      obtain ⟨q, -, hS⟩ := hq
      have e2 : st.regs.X2 = tv m0 a := arg_of hst.hd hm1 ha
      have e3 : st.regs.X3 = tv m0 b := arg_of hst.hd hm1 hb
      have hsl : slice st st.regs.X0 st.regs.X1 = imgs m0 := by
        rw [slice, ex1 hm1, ex0 hm1]
        have := NativeRustcVm.ewsOf_of_ewsAt hcp
        rw [show (imgs m0).toList.length = 64 by simp [imgs, sl, arr, coeffCount]] at this
        rw [show (64 : UInt64).toNat = 64 from rfl, this]
      rw [hsl, ewArg, e2, e3, hr] at q
      have hE2 : Holds (rsT m0) (tv m0) (E ++ D') m2 := fun p hp ↦ by
        rcases List.mem_append.mp hp with hp | hp
        · obtain ⟨r, hr1, hcs⟩ := hEr p hp
          rw [← hE st hm1 p hp, hr1, tval_reg, tval_reg, hS.1 r hcs]
        · exact hst2.hd p hp
      exact holds_ret hE2 (congrArg EW.c0 q) (congrArg EW.c1 q), hst2.copy⟩
  · exact absurd h (Nat.not_lt_zero _)
  · rw [ex1 hm1, show (64 : UInt64).toNat = 64 from rfl] at hj
    rw [ex0 hm1, NativeRustcVm.addr_add_add]
    exact hfr.kept _ (frame_mapped h.st (by decide) _ (by omega))
  · rw [ex0 hm1, ex1 hm1]
    show (fb m0 + BitVec.ofNat 64 208).toNat + 16 * 64 ≤ _
    rw [NativeRustcVm.toNat_add_ofNat (by omega)]
    omega
  · rw [ex0 hm1, ex1 hm1, show (64 : UInt64).toNat = 64 from rfl]
    have hsb := stackBelow_eq hfr.sp (N' := polyEvalStack)
      (show 2352 + polyEvalStack ≤ m0.regs.SP.toNat by rw [show polyEvalStack = 656 from rfl]; omega)
    show Apart _ _ (stackBelow st polyEvalStack) _
    rw [hsb, show polyEvalStack = 656 from rfl]
    unfold Apart
    rw [NativeRustcVm.toNat_add_ofNat (by omega), base_toNat (m0 := m0) (F := 2352 + 656) (by omega)]
    omega

end

end NativeRustcVmArm.Ring.Target
