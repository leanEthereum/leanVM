module

public import NativeRustcX64.SphincsVerify.Frame

/-!
# The frame with a window (x86-64)

Where a block reads or writes 16 bytes of the frame at an offset the proof knows but the block
computes from a register (`b65`'s path node, `b96`'s root slot), the executor's regions are the
frame's first `n0` bytes (region 0, RSP its base), the 16 slots below it (region 1) and the
window's 16 bytes at `o2 ≥ n0` (region 2): `Run.winRegs`, `Run.envW`. The environment is well
formed (`Run.wfW`); a fresh symbolic state matches the machine (`Run.matchW`); after a block whose
writes stay in the regions (`winWrites`) the frame's invariant holds (`Run.Frame.of_matchW`), or
it is at a call (`Run.AtCall.of_matchW`); the frame's bytes no write of region 0 or 1 reaches,
apart from the window, are kept (`Run.bytesAt_keptW`, `noWriteW`).
-/

namespace NativeRustcX64.SphincsVerifyProof

open NativeRustc

@[expose] public section

namespace Run

variable (r : Run)

/-- The regions: the frame's first `n0` bytes, the slots below, the window at `o2`. -/
abbrev winRegs (n0 o2 : Nat) : List (BitVec 64 × Nat) :=
  [(r.base, n0), (r.base - 16#64, 16), (r.off o2, 16)]

/-- The environment with a window. -/
abbrev envW (n0 o2 : Nat) (m : MachineData) (vars : Nat → BitVec 64 := fun _ ↦ 0)
    (ret : BitVec 64 := 0) : Sym.Env :=
  Sym.Env.ofMachine m (r.winRegs n0 o2) vars ret

end Run

/-- The writes of a symbolic state are in region 0 below `n0`, or in region 1 or 2. -/
def winWrites (S : Sym.SState) (n0 : Nat) : Bool :=
  S.mem.all fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ n0)) ||
    (w.r == 1 && decide (w.off + w.n ≤ 16)) || (w.r == 2 && decide (w.off + w.n ≤ 16))

/-- No write of a symbolic state in region 0 touches the frame's bytes `o .. o + n`; the writes
are in region 1 below 16 or in region 2. -/
def noWriteW (S : Sym.SState) (o n : Nat) : Bool :=
  S.mem.all fun w ↦ (w.r == 0 && (decide (w.off + w.n ≤ o) || decide (o + n ≤ w.off))) ||
    (w.r == 1 && decide (w.off + w.n ≤ 16)) || (w.r == 2 && decide (w.off + w.n ≤ 16))

end

public section

theorem noWriteW_of_winWrites {S : Sym.SState} {n0 : Nat} (h : winWrites S n0 = true) (n : Nat) :
    noWriteW S n0 n = true := by
  simp only [winWrites, noWriteW, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h ⊢
  intro w hw
  rcases h w hw with (h | h) | h
  · exact Or.inl (Or.inl ⟨h.1, Or.inl h.2⟩)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

namespace Run

variable (r : Run) [Labels]

/-- **The environment with a window is well formed.** -/
theorem wfW (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem) {n0 o2 : Nat}
    (h0 : n0 ≤ o2) (h2 : o2 + 16 ≤ 29384) (vars : Nat → BitVec 64) (ret : BitVec 64) :
    (r.envW n0 o2 m vars ret).WF := by
  have hb := r.base_toNat hpre
  have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
  have ho2 := r.off_toNat hpre (a := o2) (by omega)
  have hr0 : Mapped m.dmem r.base n0 ∧ NoWrap r.base n0 := by
    have := r.frame_mapped hpre hk (a := 0) (n := n0) (by omega)
    simpa [off] using this
  have hr1 : Mapped m.dmem (r.base - 16#64) 16 ∧ NoWrap (r.base - 16#64) 16 := by
    refine ⟨fun i hi ↦ r.area_mapped hpre hk ?_ ?_, ?_⟩
    · rw [Sym.toNat_add_ofNat _ _ (by omega), hlo]
      omega
    · rw [Sym.toNat_add_ofNat _ _ (by omega), hlo]
      omega
    · unfold NoWrap
      omega
  have hr2 := r.frame_mapped hpre hk (a := o2) (n := 16) (by omega)
  refine Sym.Env.wf_of ⟨hr0, hr1, hr2, trivial⟩ ?_
  show List.Pairwise (fun e e' : BitVec 64 × Nat ↦ Apart e.1 e.2 e'.1 e'.2)
    [(r.base, n0), (r.base - 16#64, 16), (r.off o2, 16)]
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true]
  refine ⟨⟨Or.inr ?_, Or.inl ?_⟩, Or.inl ?_, fun _ h ↦ h.elim⟩
  · rw [hlo]; omega
  · rw [ho2]; omega
  · rw [hlo, ho2]; omega

/-- **A fresh symbolic state with a window** for a state of the frame. -/
theorem matchW {m : MachineData} (hF : r.Frame m) {n0 o2 : Nat} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {known : List (Reg64 × Sym)} {bounds : List (Sym × Nat)}
    {aliases : List (Sym × Nat × Int)}
    (hknown : Sym.AllOf (fun p ↦ m.regs.get64 p.1 = p.2.eval (r.envW n0 o2 m vars ret)) known)
    (hbounds : Sym.AllOf (fun p ↦ (p.1.eval (r.envW n0 o2 m vars ret)).toNat < p.2) bounds)
    (haliases : Sym.AllOf (fun p ↦ p.1.eval (r.envW n0 o2 m vars ret) =
      (r.envW n0 o2 m vars ret).base p.2.1 + BitVec.ofInt 64 p.2.2) aliases) :
    Sym.Match (r.envW n0 o2 m vars ret)
      (Sym.init [n0, 16, 16] ((.rsp, .ptr 0 0) :: known) [] bounds (frameAliases ++ aliases)) m :=
  Sym.match_ofMachine ⟨rfl, rfl, rfl, trivial⟩
    ⟨by
      show rspOf m = r.base + BitVec.ofInt 64 0
      simp only [BitVec.ofInt_ofNat, BitVec.add_zero]
      exact hF.1, hknown⟩
    trivial hbounds
    ⟨alias8 r,
    by
      show r.base + BitVec.ofInt 64 (-16) = (r.base - 16#64) + BitVec.ofInt 64 0
      rw [show BitVec.ofInt 64 (-16) = -16#64 by decide, show BitVec.ofInt 64 0 = 0#64 by decide]
      bv_omega, haliases⟩

/-- The places a block's writes (`winWrites`) cover are in the stack area off the saved
registers. -/
theorem written_areaW (hpre : r.Pre) {m : MachineData} {n0 o2 : Nat} (hn0 : n0 ≤ 29336)
    (ho2 : o2 + 16 ≤ 29336) {vars : Nat → BitVec 64} {ret : BitVec 64} {S : Sym.SState}
    (hw : winWrites S n0 = true) :
    ∀ p, Sym.Written (r.envW n0 o2 m vars ret) S p →
      r.StackArea p ∧ ¬InRange (r.off 29336) 48 p := by
  have hb := r.base_toNat hpre
  have hs := r.off_toNat hpre (a := 29336) (by decide)
  have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
  have h2 := r.off_toNat hpre (a := o2) (by omega)
  rintro p ⟨w, hwm, b, sz, hr, h1, h2'⟩
  simp only [winWrites, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hw
  rw [r.stackArea_iff hpre, Sym.inRange_iff (by rw [hs]; omega), hs]
  rcases hw w hwm with (⟨hw0, hwn⟩ | ⟨hw1, hwn⟩) | ⟨hw2, hwn⟩
  · rw [hw0] at hr
    cases hr
    omega
  · rw [hw1] at hr
    cases hr
    rw [hlo] at h1 h2'
    omega
  · rw [hw2] at hr
    cases hr
    rw [h2] at h1 h2'
    omega

theorem rsp_base_of {m' : MachineData} {env : Sym.Env} {S : Sym.SState}
    (hm : Sym.Match env S m') (hb : env.base 0 = r.base) (hsp : S.reg .rsp = some (.ptr 0 0)) :
    rspOf m' = r.base := by
  rw [rspOf, hm.regs .rsp _ hsp]
  show env.base 0 + BitVec.ofInt 64 0 = r.base
  simp [hb]

/-- **The invariant after a block with a window**: RSP the base, the writes in the regions. -/
theorem Frame.of_matchW (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m) {n0 o2 : Nat}
    (hn0 : n0 ≤ 29336) (ho2 : o2 + 16 ≤ 29336) {vars : Nat → BitVec 64} {ret : BitVec 64}
    {S : Sym.SState} (hm : Sym.Match (r.envW n0 o2 m vars ret) S m')
    (hwf : (r.envW n0 o2 m vars ret).WF) (hsp : S.reg .rsp = some (.ptr 0 0))
    (hw : winWrites S n0 = true) : r.Frame m' :=
  Frame.of_change hF.2.1 hF.2.2.1 hF.2.2.2 (r.rsp_base_of hm rfl hsp) (hm.sameOutside hwf)
    (r.written_areaW hpre hn0 ho2 hw) (hm.kept hwf)

/-- **At a call after a block with a window**: RSP 8 below the base. -/
theorem AtCall.of_matchW (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m) {n0 o2 : Nat}
    (hn0 : n0 ≤ 29336) (ho2 : o2 + 16 ≤ 29336) {vars : Nat → BitVec 64} {ret : BitVec 64}
    {S : Sym.SState} (hm : Sym.Match (r.envW n0 o2 m vars ret) S m')
    (hwf : (r.envW n0 o2 m vars ret).WF) (hsp : S.reg .rsp = some (.ptr 0 (-8)))
    (hw : winWrites S n0 = true) : r.AtCall m' := by
  have hF' := Frame.of_change hF.2.1 hF.2.2.1 hF.2.2.2 (m' := { m' with regs := m.regs }) hF.1
    (hm.sameOutside hwf) (r.written_areaW hpre hn0 ho2 hw) (hm.kept hwf)
  refine ⟨?_, hF'.2.1, hF'.2.2.1, hF'.2.2.2⟩
  rw [rspOf, hm.regs .rsp _ hsp]
  show r.base + BitVec.ofInt 64 (-8) + 8#64 = r.base
  rw [show BitVec.ofInt 64 (-8) = -8#64 by decide]
  bv_omega

/-- **Bytes a block with a window does not write are kept**: the frame's bytes at `o`, where no
write of region 0 reaches, apart from the window. -/
theorem bytesAt_keptW (hpre : r.Pre) {m m' : MachineData} {n0 o2 : Nat} (ho2 : o2 + 16 ≤ 29384)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : Sym.SState}
    (hm : Sym.Match (r.envW n0 o2 m vars ret) S m') (hwf : (r.envW n0 o2 m vars ret).WF)
    {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
    (hd : o + bs.length ≤ o2 ∨ o2 + 16 ≤ o) (h : BytesAt m.dmem (r.off o) bs)
    (hn : noWriteW S o bs.length = true) : BytesAt m'.dmem (r.off o) bs := by
  have hb := r.base_toNat hpre
  have hoff := r.off_toNat hpre (a := o) (by omega)
  have h2 := r.off_toNat hpre (a := o2) (by omega)
  refine bytesAt_of_sameOutside h (hm.sameOutside hwf) fun i hi ⟨w, hwm, b, sz, hr, h1, h2'⟩ ↦ ?_
  simp only [noWriteW, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hn
  rw [Sym.toNat_add_ofNat _ _ (by omega), hoff] at h1 h2'
  rcases hn w hwm with (⟨hr', hw⟩ | ⟨hr', hw⟩) | ⟨hr', hw⟩
  · rw [hr'] at hr
    cases hr
    omega
  · rw [hr'] at hr
    cases hr
    have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
    rw [hlo] at h1 h2'
    omega
  · rw [hr'] at hr
    cases hr
    rw [h2] at h1 h2'
    omega

/-- **Bytes a block with a window does not write are kept**: where the block writes neither the
window nor the frame's bytes at `o` (`noWriteIn`). -/
theorem bytesAt_keptW' (hpre : r.Pre) {m m' : MachineData} {n0 o2 : Nat}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : Sym.SState}
    (hm : Sym.Match (r.envW n0 o2 m vars ret) S m') (hwf : (r.envW n0 o2 m vars ret).WF)
    {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384) (h : BytesAt m.dmem (r.off o) bs)
    (hn : noWriteIn S o bs.length = true) : BytesAt m'.dmem (r.off o) bs := by
  have hb := r.base_toNat hpre
  have hoff := r.off_toNat hpre (a := o) (by omega)
  refine bytesAt_of_sameOutside h (hm.sameOutside hwf) fun i hi ⟨w, hwm, b, sz, hr, h1, h2'⟩ ↦ ?_
  simp only [noWriteIn, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hn
  rw [Sym.toNat_add_ofNat _ _ (by omega), hoff] at h1 h2'
  rcases hn w hwm with ⟨hr', hw⟩ | ⟨hr', hw⟩
  · rw [hr'] at hr
    cases hr
    omega
  · rw [hr'] at hr
    cases hr
    have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
    rw [hlo] at h1 h2'
    omega

end Run

end

end NativeRustcX64.SphincsVerifyProof
