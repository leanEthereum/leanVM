module

public import NativeRustcVmArm.Ring.Target.Basic

/-!
# `ring_target`: the code after the images loop

The state after the images loop (`St D`): the frame, the description `D` of the table `tv`
(locations in the regions `rsT`: the frame, `f`), the images copied at frame byte `208`. A block
ending in a call to `EW::sq_iter` (`sqStep`), `poly_eval` (`polyStep`) or `EW::mul` (`mulStep`):
its arguments from the table, its result the table's entries `r0`, `r1`, checked by `decide`.
-/

namespace NativeRustcVmArm.Ring.Target

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring

@[expose] public section

/-- The block writes only the frame's first 208 bytes. -/
def wr208 (S : SState) : Bool := S.mem.all fun w ↦ w.r == 0 && decide (w.off + w.n ≤ 208)

/-- **After the images loop**: the frame, the table's description `D`, the images' copy. -/
structure St [Labels] (m0 : MachineData) (D : List (Sym × Nat)) (m : MachineData) : Prop where
  fr : TFr m0 m
  hd : Holds (rsT m0) (tv m0) D m
  copy : NativeRustcVm.EWsAt m.dmem (fb m0 + BitVec.ofNat 64 208) (imgs m0).toList

end

public section

variable {m0 : MachineData}

theorem stack_eq : ringTargetStack = 3008 := rfl

/-- The entry's facts, unpacked. -/
structure P (m0 : MachineData) : Prop where
  st : StackOk m0 ringTargetStack
  sm : Mapped m0.dmem (sA m0) 1024
  sw : NoWrap (sA m0) 1024
  ss : Apart (sA m0) 1024 (stackBelow m0 ringTargetStack) ringTargetStack
  fm : Mapped m0.dmem (fA m0) 128
  fw : NoWrap (fA m0) 128
  fs : Apart (fA m0) 128 (stackBelow m0 ringTargetStack) ringTargetStack
  gm : Mapped m0.dmem (gA m0) 128
  gw : NoWrap (gA m0) 128
  gs : Apart (gA m0) 128 (stackBelow m0 ringTargetStack) ringTargetStack

theorem P.intro (h : RingTargetPre m0) : P m0 :=
  ⟨h.1, h.2.1.1.1, h.2.1.1.2, h.2.1.2, h.2.2.1.1.1, h.2.2.1.1.2, h.2.2.1.2, h.2.2.2.1.1,
    h.2.2.2.1.2, h.2.2.2.2⟩

theorem P.hN (h : P m0) : ringTargetStack ≤ m0.regs.SP.toNat := h.st.2.1

theorem P.fbN (h : P m0) : (fb m0).toNat = m0.regs.SP.toNat - 2352 :=
  base_toNat (by have := h.hN; rw [stack_eq] at this; omega)

theorem P.fbw (h : P m0) : NoWrap (fb m0) 2352 :=
  base_noWrap (by have := h.hN; rw [stack_eq] at this; omega)

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 2352 := by decide

theorem slots_ge : ∀ p ∈ slots, 2256 ≤ p.1 := by decide

theorem szT_eq : (rsT m0).map Prod.snd = szT := rfl

/-- A region apart from the stack is apart from the frame. -/
theorem P.frame_apart (h : P m0) {a : BitVec 64} {n : Nat}
    (ha : Apart a n (stackBelow m0 ringTargetStack) ringTargetStack) : Apart a n (fb m0) 2352 :=
  apart_frame h.hN (by decide) ha

section
variable [Labels] {m : MachineData}

omit [Labels] in
theorem envT_wf (h : P m0) (hfr : TFr m0 m) : (Env.ofMachine m (rsT m0)).WF := by
  have hfw := h.fbw
  have hfa := h.frame_apart h.fs
  have := h.fw
  refine Env.wf_of ⟨⟨fun i hi ↦ hfr.kept _ (frame_mapped h.st (by decide) i hi), hfw⟩,
    ⟨fun i hi ↦ hfr.kept _ (h.fm i hi), h.fw⟩, trivial⟩ (List.pairwise_pair.mpr hfa.symm)

/-- The environment after the loop matches `midT` where X21 is `f`. -/
theorem matchT (hfr : TFr m0 m) (h21 : (m.regs.getXReg .X21).toBitVec = fA m0) (h : P m0) :
    Match (Env.ofMachine m (rsT m0)) midT m :=
  match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.st (by decide) (by decide), rfl,
      fun h ↦ absurd h (by decide), trivial⟩
    (by rw [hfr.sp]; simp [Sym.eval])
    ⟨by show (m.regs.getXReg .X21).toBitVec = _; rw [h21]; simp [Sym.eval], trivial⟩
    trivial trivial trivial

/-- It matches `midT2`. -/
theorem matchT2 (hfr : TFr m0 m) (h : P m0) : Match (Env.ofMachine m (rsT m0)) midT2 m :=
  match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.st (by decide) (by decide), trivial⟩
    (by rw [hfr.sp]; simp [Sym.eval]) trivial trivial trivial trivial

/-- X21 from the table. -/
theorem x21_of (hH : Holds (rsT m0) (tv m0) [(.reg .X21, fPtr)] m) :
    (m.regs.getXReg .X21).toBitVec = fA m0 := by
  have := hH _ (List.mem_singleton_self _)
  simp only [tval, Sym.eval] at this
  rw [show tv m0 fPtr = UInt64.ofBitVec (fA m0) from rfl] at this
  exact congrArg UInt64.toBitVec this

end

variable [Host]

/-- **A block ending in a call** after the loop: the description `D'` and the copy after the
call. -/
theorem stepT (h : P m0) {D D' : List (Sym × Nat)} {S0 S' : SState} {ds : List Directive}
    {i : Nat} {l : Label} {Pc : MachineData → Prop} {Qc : MachineData → MachineData → Prop}
    {N' : Nat} {R : MachineState → Prop} {m : MachineData}
    (hk : ds.IsInfixAt Host.prog i) (hrun : exec ds S0 = some (S', .call l)) (hst : St m0 D m)
    (hm : Match (Env.ofMachine m (rsT m0)) S0 m) (hsp : S'.sp = S0.sp)
    (hwr : wr208 S' = true) (htr : trackOk szT S' D D' = true)
    (hsafe : D'.all (fun p ↦ callSafe szT p.1) = true) (hle : 2352 + N' ≤ ringTargetStack)
    (hspec : Spec (Labels.label l) Pc Qc)
    (hQ : ∀ a b, Qc a b → SameOutside a.dmem b.dmem
      (fun q ↦ InRange (stackBelow a N') N' q ∨ False) ∧ Saved a b)
    (hP : ∀ st : MachineData, Match (Env.ofMachine m (rsT m0)) S' st → TFr m0 st → Pc st)
    (cont : ∀ st m2 : MachineData, Match (Env.ofMachine m (rsT m0)) S' st → Qc st m2 →
      NativeRustcVm.EWsAt st.dmem (fb m0 + BitVec.ofNat 64 208) (imgs m0).toList →
      St m0 D' m2 → Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hwf := envT_wf h hst.fr
  have hN := h.hN
  simp only [wr208, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hwr
  refine trackStep szT_eq hk hrun hst.fr hm hwf rfl (by decide) hN slots_le hsp
    (fun _ h ↦ by cases h) (fun w hw ↦ .inl ⟨(hwr w hw).1, by have := (hwr w hw).2; omega,
      fun q hq ↦ .inl (by have := slots_ge q hq; have := (hwr w hw).2; omega)⟩)
    (fun _ h ↦ h.elim) (fun r b n hb hr ↦ ?_) hst.hd htr hsafe hle hspec hQ hP
    fun st m2 hm1 hq hfr2 hd2 ↦ ?_
  · match r, hr with
    | 1, _ =>
      cases hb
      exact h.fs
  · -- the copy: not written by the block, not in the callee's stack
    have hcp := hst.copy
    have hs := (hQ _ _ hq).1
    have hfr1 : TFr m0 st :=
      hst.fr.ofBlockW hm hm1 hwf rfl hsp (fun _ h ↦ by cases h) rfl (by decide) hN slots_le
        fun w hw ↦ .inl ⟨(hwr w hw).1, by have := (hwr w hw).2; omega,
          fun q hq ↦ .inl (by have := slots_ge q hq; have := (hwr w hw).2; omega)⟩
    have hfbN := h.fbN
    have hfbw := h.fbw
    unfold NoWrap at hfbw
    have hc0 : ∀ j < 1024, st.dmem.get? (fb m0 + BitVec.ofNat 64 208 + BitVec.ofNat 64 j) =
        m.dmem.get? (fb m0 + BitVec.ofNat 64 208 + BitVec.ofNat 64 j) := by
      intro j hj
      rw [NativeRustcVm.addr_add_add]
      refine hm1.get?_mem0 hwf (not_written fun w hw b sz hb ↦ ?_)
      rw [(hwr w hw).1] at hb
      obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj hb)
      subst e1 e2
      rw [NativeRustcVm.toNat_add_ofNat (by omega)]
      have := (hwr w hw).2
      omega
    have hc1 : ∀ j < 1024, m2.dmem.get? (fb m0 + BitVec.ofNat 64 208 + BitVec.ofNat 64 j) =
        st.dmem.get? (fb m0 + BitVec.ofNat 64 208 + BitVec.ofNat 64 j) := by
      intro j hj
      refine hs _ ?_
      have hSP := m0.regs.SP.toNat_lt
      have hnw : NoWrap (base m0 (2352 + N')) N' := by
        unfold NoWrap; rw [base_toNat (by omega)]; omega
      rintro (hq' | hq')
      · rw [stackBelow_eq hfr1.sp (N' := N') (by omega), NativeRustcVm.addr_add_add,
          Sym.inRange_iff hnw, base_toNat (by omega),
          NativeRustcVm.toNat_add_ofNat (by omega), hfbN] at hq'
        omega
      · exact hq'
    have hlen : 16 * (imgs m0).toList.length = 1024 := by simp [imgs, sl, arr, coeffCount]
    have hcst : NativeRustcVm.EWsAt st.dmem (fb m0 + BitVec.ofNat 64 208) (imgs m0).toList := by
      intro j hj
      rw [NativeRustcVm.length_ewsBytes, hlen] at hj
      rw [hc0 j hj]
      exact hcp j (by rw [NativeRustcVm.length_ewsBytes, hlen]; exact hj)
    refine cont st m2 hm1 hq hcst ⟨hfr2, hd2, ?_⟩
    intro j hj
    rw [NativeRustcVm.length_ewsBytes, hlen] at hj
    rw [hc1 j hj]
    exact hcst j (by rw [NativeRustcVm.length_ewsBytes, hlen]; exact hj)

end

end NativeRustcVmArm.Ring.Target
