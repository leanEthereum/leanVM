module

public import NativeRustcVmX64.Ring.Coeff.Entry
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EWSqIter.Names
public import NativeRustcVmX64.Code.Vm.RingCoefficients.Names

/-!
# `ring_coefficients` on x86-64

`ringCoefficients_spec`: rustc's `ring_coefficients(f, g, out)`, placed anywhere in the program,
given the contracts of `EW::mul` and `EW::sq_iter`, writes `ringCoefficients f g` at `out`. Its
entry block reads `G = g` into registers and spills (`enter`); each of the 8 turns (`turn_body`)
writes the row `f_p · G` and replaces `G` by its Frobenius images: at a turn's head (`Head`) the
rows so far are the model's `(rc p).1` and `G` the model's `(rc p).2`. The epilogue returns.
-/

namespace NativeRustcVmX64.Ring.Coeff

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingCoefficients

@[expose] public section

variable [Host]

/-- **Turn `p`'s head**: `G`'s elements `g`, the rows so far. -/
def Head (m0 : MachineData) (k p : Nat) (st : MachineState) : Prop :=
  ∃ g : Nat → EW, (∀ b < 8, g b = gG m0 p b) ∧ Mem m0 st.data ∧
    TAt m0 st.data p k 40 tH (hvG m0 p g) st ∧
    NativeRustcVm.EWsAt st.data.dmem (oA m0) (rc m0 p).1.toList

/-- After the last turn, before the epilogue: the coefficients written. -/
def Last (m0 : MachineData) (k : Nat) (st : MachineState) : Prop :=
  ∃ m F g G', Mem m0 m ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.RingCoefficients.b18Offset) ∧
    Bnd (own m0 m) 176 NC (rsP m0 7) wrRow tX (bvG m0 7 F g G' 17) st.data ∧
    NativeRustcVm.EWsAt st.data.dmem (oA m0) (rc m0 8).1.toList

end

public section

variable {m0 : MachineData}

/-- The rows so far are outside the stack and the row of turn `p`. -/
theorem rows_kept [Labels] (h : P m0) {p : Nat} (hpl : p < 8) {m d : MachineData} {T : SState}
    {vals : Nat → BitVec 64} (hB : Bnd (own m0 m) 176 NC (rsP m0 p) wrRow T vals d)
    (hE : NativeRustcVm.EWsAt m.dmem (oA m0) (rc m0 p).1.toList) :
    NativeRustcVm.EWsAt d.dmem (oA m0) (rc m0 p).1.toList := by
  refine NativeRustcVm.BytesAt.of_sameOutside hE hB.same fun i hi hin ↦ ?_
  rw [NativeRustcVm.length_ewsBytes, Array.length_toList, rc_size1 (by omega)] at hi
  have how := h.ow
  have hos := h.os
  have hb := h.below
  unfold NoWrap at how
  unfold Apart at hos
  have hq : (oA m0 + BitVec.ofNat 64 i).toNat = (oA m0).toNat + i :=
    toNat_add_ofNat _ _ (by omega)
  rcases hin with h1 | ⟨j, e, hwr, he, h2⟩
  · rw [show stackBelow (own m0 m) NC = stackBelow m0 NC from rfl,
      Sym.inRange_iff (by rw [hb]; have := h.st.2.1; omega), hq, hb] at h1
    rw [hb] at hos
    omega
  · cases j with
    | zero =>
      simp only [rsP, List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      have hr : (oA m0 + BitVec.ofNat 64 (128 * p)).toNat = (oA m0).toNat + 128 * p :=
        toNat_add_ofNat _ _ (by omega)
      simp only at h2
      rw [Sym.inRange_iff (by rw [hr]; omega), hr, hq] at h2
      omega
    | succ j => simp [wrRow] at hwr

/-- The row of turn `p` is in `out`. -/
theorem row_in_out (h : P m0) {p : Nat} (hpl : p < 8) {q : BitVec 64}
    (hq : outsOf (rsP m0 p) wrRow q) : InRange (oA m0) 1024 q := by
  obtain ⟨j, e, hwr, he, h2⟩ := hq
  cases j with
  | zero =>
    simp only [rsP, List.getElem?_cons_zero, Option.some.injEq] at he
    subst he
    have how := h.ow
    unfold NoWrap at how
    have hr : (oA m0 + BitVec.ofNat 64 (128 * p)).toNat = (oA m0).toNat + 128 * p :=
      toNat_add_ofNat _ _ (by omega)
    simp only at h2
    rw [Sym.inRange_iff (by rw [hr]; omega), hr] at h2
    rw [Sym.inRange_iff (by omega)]
    omega
  | succ j => simp [wrRow] at hwr

/-- `out`'s bytes are outside the stack. -/
theorem out_not_stack (h : P m0) {i : Nat} (hi : i < 1024) :
    ¬InRange (stackBelow m0 NC) NC (oA m0 + BitVec.ofNat 64 i) := by
  have how := h.ow
  have hos := h.os
  have hb := h.below
  have ht := h.st.2.1
  have hsN := h.sN
  unfold NoWrap at how
  unfold Apart at hos
  have hq : (oA m0 + BitVec.ofNat 64 i).toNat = (oA m0).toNat + i :=
    toNat_add_ofNat _ _ (by omega)
  intro h1
  rw [Sym.inRange_iff (by rw [hb]; omega), hq, hb] at h1
  rw [hb] at hos
  omega

theorem prods_eq {p : Nat} {g : Nat → EW} (hg : ∀ b < 8, g b = gG m0 p b) :
    (List.range 8).map (fun k ↦ fE m0 p * g k) = prods m0 p 8 := by
  unfold prods
  refine List.map_congr_left fun b hb ↦ ?_
  rw [hg b (List.mem_range.mp hb)]

variable [Host] {k : Nat}

/-- **A turn**: from turn `p`'s head to the next, or past the last. -/
theorem turn (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hsq : Spec (Labels.label NativeRustcVmX64.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost) (h : P m0) {p : Nat}
    (hpl : p < 8) {st : MachineState} (hH : Head m0 k p st) :
    Eventually (step1 Host.exe) (fun st' ↦ (p < 7 ∧ Head m0 k (p + 1) st') ∨
      (p = 7 ∧ Last m0 k st')) st := by
  obtain ⟨g, hg, hM, hA, hE⟩ := hH
  refine Eventually.mono (turn_body hp hmul hsq h hM hpl (F := fE m0 p) rfl
    (G' := fun b ↦ frobenius8 (g b) 1) (fun _ ↦ rfl) hA) fun st' ⟨hpc, hB⟩ ↦ ?_
  have hM' := Mem.of_bnd h hM hpl hB
  have hrows : NativeRustcVm.EWsAt st'.data.dmem (oA m0) (rc m0 (p + 1)).1.toList := by
    rw [rc_succ_fst hpl, NativeRustcVm.ewsAt_append_iff, Array.length_toList, rc_size1 (by omega)]
    refine ⟨rows_kept h hpl hB hE, ?_⟩
    rw [show 16 * (8 * p) = 128 * p by omega, ← prods_eq hg]
    exact row_at hB
  by_cases h7 : p = 7
  · subst h7
    exact .inr ⟨rfl, st.data, _, _, _, hM, by rw [hpc]; rfl, to_exit hB, hrows⟩
  · refine .inl ⟨by omega, fun b ↦ frobenius8 (g b) 1, fun b hb ↦ ?_, hM', ⟨?_, next_head hB⟩,
      hrows⟩
    · show frobenius8 (g b) 1 = _
      rw [hg b hb, gG_succ hpl hb]
    · rw [hpc, ite_eq_right h7]
      exact hp.label NativeRustcVmX64.Vm.RingCoefficients.label_1_at

/-- **The turns**, from turn `p`'s head. -/
theorem turns (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hsq : Spec (Labels.label NativeRustcVmX64.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost) (h : P m0) :
    ∀ n p, p + n = 7 → ∀ {st : MachineState}, Head m0 k p st →
      Eventually (step1 Host.exe) (Last m0 k) st := by
  intro n
  induction n with
  | zero =>
    intro p hp7 st hH
    refine Eventually.mono (turn hp hmul hsq h (by omega) hH) fun st' hst ↦ ?_
    rcases hst with ⟨hlt, -⟩ | ⟨-, hl⟩
    · omega
    · exact hl
  | succ n ih =>
    intro p hp7 st hH
    refine Eventually.bind (turn hp hmul hsq h (by omega) hH) fun st' hst ↦ ?_
    rcases hst with ⟨-, hH'⟩ | ⟨h7, -⟩
    · exact ih (p + 1) (by omega) hH'
    · omega

/-- **`ring_coefficients` writes the coefficients.** -/
theorem ringCoefficients_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hsq : Spec (Labels.label NativeRustcVmX64.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.RingCoefficients.entryLabel) RingCoefficientsPre RingCoefficientsPost := by
  intro m0 hpre
  have h := P.intro hpre
  rw [show Labels.label NativeRustcVmX64.Vm.RingCoefficients.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.RingCoefficients.b0Offset) from hp.label NativeRustcVmX64.Vm.RingCoefficients.entry_at]
  refine Eventually.bind (enter hp h) fun st ⟨hpc, hM, hB⟩ ↦ ?_
  have hH : Head m0 k 0 st :=
    ⟨g0 m0, fun _ hb ↦ g0_eq hb, hM, ⟨hpc, hB⟩, NativeRustcVm.ewsAt_nil _ _⟩
  refine Eventually.bind (turns hp hmul hsq h 7 0 rfl hH) fun st ⟨m, F, g, G', hM, hpc, hB, hE⟩ ↦ ?_
  obtain ⟨d, pc⟩ := st
  simp only at hpc hB hE
  subst hpc
  have hl := lay h hM (p := 7) (by decide)
  refine exitStep hl hB (b18_in_code.trans hp.1 (by simp [b18])) run_b18 rfl rfl
    (fun r hr ↦ by cases r <;> simp only [calleeSaved, Bool.false_eq_true] at hr <;>
      exact ⟨_, rfl, rfl⟩) fun st hm hret hrsp hso hsv ↦ .done _ ⟨?_, hrsp, ?_, ?_, ?_⟩
  · rw [hret]
    refine Field.retOf_eq rfl fun j hj ↦ hM.same _ fun hin ↦ ?_
    have ht := h.st.2.1
    have hb := h.below
    have hsN := h.sN
    have hq : (rspOf m0 + BitVec.ofNat 64 j).toNat = (rspOf m0).toNat + j :=
      toNat_add_ofNat _ _ (by omega)
    have how := h.ow
    have hos := h.os
    unfold NoWrap at how
    unfold Apart at hos
    rcases hin with h1 | h2
    · rw [Sym.inRange_iff (by rw [hb]; omega), hq, hb] at h1
      omega
    · rw [Sym.inRange_iff (by omega), hq] at h2
      rw [hb] at hos
      omega
  · -- The coefficients.
    have hwf := hl.wf hB.kept (vals := bvG m0 7 F g G' 17) (ret := 0)
    have hkeep : NativeRustcVm.EWsAt st.data.dmem (oA m0) (rc m0 8).1.toList := by
      refine NativeRustcVm.BytesAt.of_sameOutside hE
        (R := fun q ↦ InRange (stackBelow m0 NC) NC q) (fun q hq ↦ ?_) fun i hi ↦ ?_
      · rw [hm.get?_mem0 hwf fun hW ↦ hq ?_]
        · rfl
        · rcases hl.written (wr := fun _ ↦ false) rfl hW with h1 | ⟨_, _, h2, _⟩
          · exact h1
          · cases h2
      · rw [NativeRustcVm.length_ewsBytes, Array.length_toList, rc_size1 (by decide)] at hi
        exact out_not_stack h hi
    rw [rc_final] at hkeep
    exact hkeep
  · intro q hq
    refine (hso q fun hin ↦ hq ?_).trans (hM.same q fun hin ↦ hq ?_)
    · rcases hin with h1 | h2
      · exact .inr h1
      · exact .inl (row_in_out h (by decide) h2)
    · rcases hin with h1 | h2
      · exact .inr h1
      · exact .inl h2
  · exact ⟨fun r hr ↦ hsv.1 r hr, fun q hq ↦ hsv.2 q (hM.kept q hq)⟩

end

end NativeRustcVmX64.Ring.Coeff
