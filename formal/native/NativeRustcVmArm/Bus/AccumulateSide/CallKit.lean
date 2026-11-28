module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EqEvalFnOfEqAbove.Names
public import NativeRustcVmArm.Bus.AccumulateSide.Kit

/-!
# `accumulate_side`: its calls of `eq_eval_fn` and `EW::mul`

A block of the body ending in a call (`St.runCall`): `eq_eval_fn` for `eq_above p point`
(`St.eqCall`, the registers `eq_above`'s inlined head computes), `EW::mul` (`St.mulCall`). Both
callees write only their stack: the forms stay (`KeepF`), and the frame's bytes the block does not
write (`KeepB`).
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout
open LeanVM.Protocol.Verifier (Placement)

public section

/-- The forms from `m` in `m2`. -/
@[expose] def KeepF (m0 m m2 : MachineData) : Prop :=
  ∀ G, FormsAt m.dmem m0.regs.X1.toBitVec G → FormsAt m2.dmem m0.regs.X1.toBitVec G

/-- The frame's bytes from `m` in `m2`, but the ones the writes `ws` cover. -/
@[expose] def KeepB (m0 m m2 : MachineData) (ws : List Write) : Prop :=
  ∀ o n, o + n ≤ F → (∀ w ∈ ws, w.r = 0 ∧ (w.off + w.n ≤ o ∨ o + n ≤ w.off)) →
    Same m.dmem m2.dmem (base m0 F + BitVec.ofNat 64 o) n

variable [Host] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW}

/-- **A block of the body ending in a call writing only its stack**: the forms and the frame's
bytes kept. -/
theorem St.runCallK (h : Pre L rows bl Fm SL m0) {A : Nat} (hA : A = 0 ∨ A = 72)
    {rs : List (BitVec 64 × Nat)} {sz : List Nat}
    (hsz : ((base m0 F, F + A) :: rs).map Prod.snd = sz) {S S' : SState} {ds : List Directive}
    {i : Nat} {l : Label} {R : MachineState → Prop} {m : MachineData} {V : Nat → UInt64}
    {D D' E : List (Sym × Nat)} {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    {N' : Nat} (hk : ds.IsInfixAt Host.prog i) (hrun : exec ds S = some (S', .call l))
    (hfr : Fr m0 F N slots keep (outs m0) m) (hH : Holds ((base m0 F, F + A) :: rs) V D m)
    (hwf : (Env.ofMachine m ((base m0 F, F + A) :: rs)).WF)
    (hm : Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S m)
    (hsp : S'.sp = .ptr 0 0) (hw : wrOk S' = true)
    (hD' : (D' ++ E).all (fun p ↦ loc0 p.1) = true) (htr : trackOk sz S' D D' = true)
    (hE : ∀ st : MachineData, Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S' st →
      Holds ((base m0 F, F + A) :: rs) V E st)
    (hle : F + N' ≤ N) (hok : (D' ++ E).all (fun p ↦ callOk 0 0 p.1) = true)
    (hspec : Spec (Labels.label l) P Q)
    (hP : ∀ st : MachineData, Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S' st →
      St m0 V (D' ++ E) st → P st)
    (hQ : ∀ st m' : MachineData, Q st m' →
      SameOutside st.dmem m'.dmem (InRange (stackBelow st N') N') ∧ Saved st m')
    (cont : ∀ st m2 : MachineData, Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S' st →
      St m0 V (D' ++ E) st → St m0 V (D' ++ E) m2 → Q st m2 → KeepF m0 m m2 →
      KeepB m0 m m2 S'.mem →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hN := h.stack.2.1
  refine St.runCall h hsz hk hrun hfr hH hwf hm hsp hw hD' htr hE hle (lo := 0) (n := 0)
    (by omega) hok hspec hP (fun st m' _ hq ↦ ⟨NativeRustcVm.SameOutside.mono (hQ st m' hq).1
      fun _ h ↦ .inl h, (hQ st m' hq).2⟩) fun st m2 hm' hst hst2 hq _ ↦ ?_
  have hs := (hQ st m2 hq).1
  refine cont st m2 hm' hst hst2 hq (fun G hG ↦ forms_call h hst.fr.sp hle hs
    (forms_wrOk h hA hm' hwf hw hG)) fun o n hon hw' ↦ ?_
  refine (same_block (by have := F_le h; omega) hm' hwf hon hw').trans ?_
  exact same_call (X := fun _ ↦ False) hst.fr.sp (by omega) (fun _ h ↦ h.elim) (lo := 0)
    (n' := 0) (NativeRustcVm.SameOutside.mono hs fun _ h ↦ .inl h) hon (by omega) (.inr (by omega))

/-- **A block calling `eq_eval_fn`** for `eq_above p point`: `n` the point's length, `pa` its
address, `vs`, `is` the placement's variable count and index. -/
theorem St.eqCall (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre
      EqEvalFnOfEqAbovePost)
    {A : Nat} (hA : A = 0 ∨ A = 72) {rs : List (BitVec 64 × Nat)} {sz : List Nat}
    (hsz : ((base m0 F, F + A) :: rs).map Prod.snd = sz) {S S' : SState} {ds : List Directive}
    {i : Nat} {R : MachineState → Prop} {m : MachineData} {V : Nat → UInt64}
    {D D' E : List (Sym × Nat)} (hk : ds.IsInfixAt Host.prog i)
    (hrun : exec ds S = some (S', .call NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel))
    (hfr : Fr m0 F N slots keep (outs m0) m) (hH : Holds ((base m0 F, F + A) :: rs) V D m)
    (hwf : (Env.ofMachine m ((base m0 F, F + A) :: rs)).WF)
    (hm : Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S m)
    (hsp : S'.sp = .ptr 0 0) (hw : wrOk S' = true)
    (hD' : (D' ++ E).all (fun p ↦ loc0 p.1) = true) (htr : trackOk sz S' D D' = true)
    (hE : ∀ st : MachineData, Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S' st →
      Holds ((base m0 F, F + A) :: rs) V E st)
    (hok : (D' ++ E).all (fun p ↦ callOk 0 0 p.1) = true)
    {n pa z vs is : Sym} {p : Placement}
    (h0 : S'.reg .X0 = some (.ite (.cmp .ult .W64 n vs) (.lit 0) (.bin .sub .W64 n vs)))
    (h1 : S'.reg .X1 = some (.ite (.and (.not (.cmp .ult .W64 vs (.lit 63)))
      (.not (.cmp .eq .W64 vs (.lit 63)))) (.lit 0) (.bin .lsrv .W64 is vs)))
    (h2 : S'.reg .X2 = some (.ite (.cmp .ult .W64 n vs) z
      (.bin .add .W64 pa (.un (.shift .LSL 4) .W64 vs))))
    (h3 : S'.reg .X3 = some (.ite (.cmp .ult .W64 n vs) (.lit 0) (.bin .sub .W64 n vs)))
    (hn : (n.eval (Env.ofMachine m ((base m0 F, F + A) :: rs))).toNat = (stackArg m0 48).toNat)
    (hpa : pa.eval (Env.ofMachine m ((base m0 F, F + A) :: rs)) = (stackArg m0 40).toBitVec)
    (hz : z.eval (Env.ofMachine m ((base m0 F, F + A) :: rs)) = 8#64)
    (hvc : (vs.eval (Env.ofMachine m ((base m0 F, F + A) :: rs))).toNat = p.variableCount)
    (hix : (is.eval (Env.ofMachine m ((base m0 F, F + A) :: rs))).toNat = p.index)
    (cont : ∀ m2, St m0 V (D' ++ E) m2 → ewRet m2 = eqAbove p (ptA m0) → KeepF m0 m m2 →
      KeepB m0 m m2 S'.mem → Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hsp0 := sp_ge h
  have r0 : ∀ st : MachineData,
      Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S' st →
      st.regs.X0.toNat = (stackArg m0 48).toNat - p.variableCount := fun st hm' ↦ by
    have := ev_satSub (Env.ofMachine m ((base m0 F, F + A) :: rs)) n vs
    rw [← hm'.regs .X0 _ h0, hn, hvc] at this
    exact this
  have r3 : ∀ st : MachineData,
      Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S' st →
      st.regs.X3.toNat = (stackArg m0 48).toNat - p.variableCount := fun st hm' ↦ by
    have := ev_satSub (Env.ofMachine m ((base m0 F, F + A) :: rs)) n vs
    rw [← hm'.regs .X3 _ h3, hn, hvc] at this
    exact this
  have r1 : ∀ st : MachineData,
      Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S' st →
      st.regs.X1.toNat = p.index >>> p.variableCount := fun st hm' ↦ by
    have := ev_shr (Env.ofMachine m ((base m0 F, F + A) :: rs)) is vs
    rw [← hm'.regs .X1 _ h1, hix, hvc] at this
    exact this
  have r2 : ∀ st : MachineData,
      Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S' st →
      st.regs.X2.toBitVec = if (stackArg m0 48).toNat < p.variableCount then 8#64
        else (stackArg m0 40).toBitVec + BitVec.ofNat 64 (16 * p.variableCount) := fun st hm' ↦ by
    have := ev_above (Env.ofMachine m ((base m0 F, F + A) :: rs)) n pa vs z hz
    rw [← hm'.regs .X2 _ h2, hn, hvc, hpa] at this
    exact this
  refine St.runCallK h hA hsz hk hrun hfr hH hwf hm hsp hw hD' htr hE (N' := eqEvalFnStack)
    le_ee hok hee (fun st hm' hst ↦ ?_) (fun _ _ hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1
      fun _ h ↦ h.elim (fun h ↦ by unfold InRange at h; omega) id, hq.2.2⟩)
    fun st m2 hm' hst hst2 hq hF hB ↦ cont m2 hst2 ?_ hF hB
  · have hS' := hst.fr.stackOk h.stack (by decide) le_ee
    refine eqAbove_pre hS' h.pn ⟨Bus.Fr.readable hst.fr h.pt.1,
      Bus.Fr.offStack hst.fr h.stack h.pt.2 le_ee⟩ ?_ (r0 st hm') (r2 st hm') (r3 st hm')
    rw [stackBelow_toNat h hst.fr le_ee, ee_eq, show F = 12096 from rfl]
    omega
  · rw [eqAbove_ret (r0 st hm') (r1 st hm') (r2 st hm') (r3 st hm') hq, pt_eq h hst.fr]

/-- **A block calling `EW::mul`**. -/
theorem St.mulCall (h : Pre L rows bl Fm SL m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {A : Nat} (hA : A = 0 ∨ A = 72) {rs : List (BitVec 64 × Nat)} {sz : List Nat}
    (hsz : ((base m0 F, F + A) :: rs).map Prod.snd = sz) {S S' : SState} {ds : List Directive}
    {i : Nat} {R : MachineState → Prop} {m : MachineData} {V : Nat → UInt64}
    {D D' E : List (Sym × Nat)} (hk : ds.IsInfixAt Host.prog i)
    (hrun : exec ds S = some (S', .call NativeRustcVmArm.Vm.EWMul.entryLabel))
    (hfr : Fr m0 F N slots keep (outs m0) m) (hH : Holds ((base m0 F, F + A) :: rs) V D m)
    (hwf : (Env.ofMachine m ((base m0 F, F + A) :: rs)).WF)
    (hm : Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S m)
    (hsp : S'.sp = .ptr 0 0) (hw : wrOk S' = true)
    (hD' : (D' ++ E).all (fun p ↦ loc0 p.1) = true) (htr : trackOk sz S' D D' = true)
    (hE : ∀ st : MachineData, Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S' st →
      Holds ((base m0 F, F + A) :: rs) V E st)
    (hok : (D' ++ E).all (fun p ↦ callOk 0 0 p.1) = true)
    (cont : ∀ st m2 : MachineData, Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S' st →
      St m0 V (D' ++ E) m2 →
      ewRet m2 = EW.mul ⟨st.regs.X0, st.regs.X1⟩ ⟨st.regs.X2, st.regs.X3⟩ →
      KeepF m0 m m2 → KeepB m0 m m2 S'.mem →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ :=
  St.runCallK h hA hsz hk hrun hfr hH hwf hm hsp hw hD' htr hE (N' := ewMulStack)
    le_mul hok hmul (fun _ _ hst ↦ hst.fr.stackOk h.stack (by decide) le_mul)
    (fun _ _ hq ↦ ⟨hq.2.2.1, hq.2.2.2⟩)
    fun st m2 hm' _ hst2 hq hF hB ↦ cont st m2 hm' hst2 (by
      obtain ⟨q0, q1, -⟩ := hq
      unfold ewRet
      rw [q0, q1]) hF hB

end

end NativeRustcVmArm.Bus.AccumulateSide
