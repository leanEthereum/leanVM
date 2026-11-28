module

public import NativeRustcVmArm.Layout.PlacementsOf.Loop2

/-!
# `placements_of`: a placement stored (`b21`, `b27`)

`b21` stores column `c`'s placement `some ⟨X11, X12⟩`, `b27` stores `none`; both count on and
leave the third loop after column `157` (`store21`, `store27`). `stored` is what they share: the
other bytes kept, the invariant at `c + 1`.
-/

namespace NativeRustcVmArm.Layout.PlacementsOf

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PlacementsOf
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf addr_add_add addr_add_zero toNat_add_ofNat)
open NativeRustcVmArm.Arrays (Body calleeRegs inSlots keepsAll restores)
open NativeRustcVmArm.Layout.BuildLayout (not_top_of_apart toNat_toUInt64')

public section

theorem plAt_same {d d' : Mem 64} {a : BitVec 64} {p : Option Placement}
    (h : PlacementWAt d a p) (hs : Same d d' a 24) : PlacementWAt d' a p := by
  cases p with
  | none => exact WordAt.of_same (n := 24) h hs (by decide)
  | some q =>
    obtain ⟨h0, h1, h2, h3, h4⟩ := h
    exact ⟨WordAt.of_same h0 hs (by decide), h1, h2,
      WordAt.of_same h3 (hs.sub (o := 8) (k := 8) (by decide)) (Nat.le_refl _),
      WordAt.of_same h4 (hs.sub (o := 16) (k := 8) (by decide)) (Nat.le_refl _)⟩

theorem not_both {a b p : BitVec 64} {n m : Nat} (hA : Apart a n b m) (ha : NoWrap a n)
    (hb : NoWrap b m) (h1 : InRange a n p) (h2 : InRange b m p) : False := by
  rw [inRange_iff ha] at h1
  rw [inRange_iff hb] at h2
  unfold Apart at hA
  omega

section
variable [Labels]

/-- Placement `c`'s bytes. -/
theorem pl_readable {m0 st : MachineData} (hF : Facts m0) (hb : Bd m0 st) {c : Nat}
    (hc : c < 158) : Readable st (pp m0 + BitVec.ofNat 64 (24 * c)) 24 :=
  Layout.readable_sub hF.pr hb.kept (by unfold placementsBytes placementBytes columnCountW; omega)

theorem pl_in {m0 : MachineData} (hF : Facts m0) {c : Nat} (hc : c < 158) {p : BitVec 64}
    (h : InRange (pp m0 + BitVec.ofNat 64 (24 * c)) 24 p) : InRange (pp m0) placementsBytes p :=
  NativeRustcVm.InRange.of_sub h hF.pr.2
    (by unfold placementsBytes placementBytes columnCountW; omega)

/-- **After a store** of placement `c`: the invariant at `c + 1`. -/
theorem stored {m0 st st' : MachineData} (hF : Facts m0) {c : Nat} (hc : c < 158)
    (hI : I3 m0 c st) (hb : Bd m0 st')
    (hs : ∀ p, ¬InRange (pp m0 + BitVec.ofNat 64 (24 * c)) 24 p → st'.dmem.get? p = st.dmem.get? p)
    (hnew : PlacementWAt st'.dmem (pp m0 + BitVec.ofNat 64 (24 * c)) (plF (κ m0) c))
    (x9 : st'.regs.X9.toNat = c + 1)
    (x10 : st'.regs.X10.toBitVec = pp m0 + BitVec.ofNat 64 (24 * (c + 1) + 16))
    (e : ∀ r ∈ [XReg.X8, .X19, .X20, .X21, .X23, .X24, .X25],
      st'.regs.getXReg r = st.regs.getXReg r) : I3 m0 (c + 1) st' := by
  have hnw := hF.pr.2
  have hpb : placementsBytes = 24 * 158 := rfl
  refine ⟨hb, by omega, x9, x10, ?_, hI.keep.of (e .X19 (by simp)) (e .X20 (by simp))
    (e .X23 (by simp)) (e .X24 (by simp)), ?_, ?_, fun c' hc' ↦ ?_, fun c' hc' ↦ ?_⟩
  · rw [show st'.regs.X8 = st.regs.X8 from e .X8 (by simp)]; exact hI.x8
  · rw [show st'.regs.X21 = st.regs.X21 from e .X21 (by simp)]; exact hI.x21
  · rw [show st'.regs.X25 = st.regs.X25 from e .X25 (by simp)]; exact hI.x25
  · have h158 := lt_of_mem_blockList hc'
    refine NativeRustcVm.Layout.WordAt.of_same (hI.offs c' hc') (n := 8)
      (fun j hj ↦ hs _ fun hin ↦ ?_) (Nat.le_refl _)
    have hin2 := Arrays.inRange_add (NativeRustcVm.NoWrap.sub (fb_noWrap hF)
      (o := 3792 + 8 * c') (m := 8) (by omega)) hj
    obtain ⟨a1, -⟩ := frame_low hF (by omega) hin2
    exact not_both hF.po hnw (Arrays.stack_noWrap hF.stack) (pl_in hF hc hin) a1
  · rcases Nat.lt_or_ge c' c with h | h
    · refine plAt_same (hI.pl c' h) fun j hj ↦ ?_
      rw [addr_add_add]
      exact hs _ (NativeRustcVm.not_inRange_sub hnw (by omega) (by omega) (by omega))
    · obtain rfl : c' = c := by omega
      exact hnew

end

variable [Host] {k : Nat}

/-- **`b21`**: placement `some ⟨X11, X12⟩` stored. -/
theorem store21 (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {c : Nat} (hc : c < 158)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b21Offset)) (hI : I3 m0 c st.data) {idx : Nat}
    (hidx : idx < 2 ^ 64) (x11 : st.data.regs.X11.toNat = κ m0 c)
    (x12 : st.data.regs.X12.toNat = idx) (hpl : plF (κ m0) c = some ⟨κ m0 c, idx⟩) :
    Eventually (step1 Host.exe) (fun s ↦ (c + 1 < 158 ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b22Offset) ∧
      I3 m0 (c + 1) s.data) ∨ (c + 1 = 158 ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b28Offset) ∧
      I3 m0 158 s.data)) st := by
  have hb := hI.body
  have hr := pl_readable hF hb hc
  have hwf := Arrays.wf_one hr.1 hr.2
  have hκ := hF.κ_le hc
  have hm : Match (Env.ofMachine st.data [(pp m0 + BitVec.ofNat 64 (24 * c), 24)]) stS st.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl ⟨by
      show _ = (pp m0 + BitVec.ofNat 64 (24 * c)) + BitVec.ofInt 64 16
      rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, addr_add_add]; exact hI.x10,
      trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b21_in_code (by simp [b21]) hp) run_b21 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨k21, w21, f0, f8, f16⟩ := Arrays.after_eq run_b21 ▸ b21_facts
  have hb1 : Bd m0 st1.data := Bd.of_write hF hb hm hm1 hwf rfl k21 fun p hw ↦ by
    obtain ⟨w, hw', b, sz, hb', hin⟩ := written_in hwf hw fun w hw b sz hb' ↦ by
      obtain ⟨h0, h1⟩ := w21 w hw
      rw [h0] at hb'
      simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hb'
      omega
    obtain ⟨h0, -⟩ := w21 w hw'
    rw [h0] at hb'
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb'
    obtain ⟨rfl, rfl⟩ := hb'
    have := pl_in hF hc hin
    exact ⟨.inl this, not_top_of_apart hF.stack (by decide) hF.po hF.pr.2 this⟩
  have hs := Layout.same_of_region hm1 hwf (r := 0) (b := pp m0 + BitVec.ofNat 64 (24 * c))
    (sz := 24) rfl w21
  have n0 := Layout.Match.wordAt_write hm1 (r := 0) (o := 0) rfl (by omega) f0
  have n8 := Layout.Match.wordAt_write hm1 (r := 0) (o := 8) rfl (by omega) f8
  have n16 := Layout.Match.wordAt_write hm1 (r := 0) (o := 16) rfl (by omega) f16
  rw [addr_add_zero] at n0
  have v11 : UInt64.ofBitVec ((Sym.reg .X11).eval
      (Env.ofMachine st.data [(pp m0 + BitVec.ofNat 64 (24 * c), 24)])) = (κ m0 c).toUInt64 := by
    apply UInt64.toNat.inj
    show st.data.regs.X11.toNat = _
    rw [x11, toNat_toUInt64' (by omega)]
  have v12 : UInt64.ofBitVec ((Sym.reg .X12).eval
      (Env.ofMachine st.data [(pp m0 + BitVec.ofNat 64 (24 * c), 24)])) = idx.toUInt64 := by
    apply UInt64.toNat.inj
    show st.data.regs.X12.toNat = _
    rw [x12, toNat_toUInt64' hidx]
  rw [v11] at n8
  rw [v12] at n16
  have hnew : PlacementWAt st1.data.dmem (pp m0 + BitVec.ofNat 64 (24 * c)) (plF (κ m0) c) := by
    rw [hpl]
    exact ⟨n0, show κ m0 c < 2 ^ 64 by omega, hidx, n8, n16⟩
  have e1 := Arrays.regs_eq_of hm hm1 [.X8, .X19, .X20, .X21, .X23, .X24, .X25] rfl
  have g9 := hm1.regs .X9 _ rfl
  have g10 := hm1.regs .X10 _ rfl
  sym_simp at g9 g10
  have e9 : (Env.ofMachine st.data [(pp m0 + BitVec.ofNat 64 (24 * c), 24)]).regs .X9 =
      BitVec.ofNat 64 c := by
    apply BitVec.eq_of_toNat_eq
    show st.data.regs.X9.toNat = _
    rw [hI.x9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hI' : I3 m0 (c + 1) st1.data := stored hF hc hI hb1 hs hnew (by
      show (st1.data.regs.getXReg .X9).toBitVec.toNat = _
      rw [g9, e9]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega) (by
      show (st1.data.regs.getXReg .X10).toBitVec = _
      rw [g10]
      show (pp m0 + BitVec.ofNat 64 (24 * c)) + BitVec.ofInt 64 40 = _
      rw [show BitVec.ofInt 64 40 = BitVec.ofNat 64 40 from rfl, addr_add_add,
        show 24 * c + 40 = 24 * (c + 1) + 16 by omega]) e1
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  rw [e9, show BitVec.ofNat 64 c + 1#64 = BitVec.ofNat 64 (c + 1) from
    (BitVec.ofNat_add _ _).symm, ofNat_beq' (by omega) (by decide)] at hpc1
  obtain ⟨f, t⟩ := Arrays.pc_cond hpc1
  by_cases hl : c + 1 = 158
  · refine .done _ (.inr ⟨hl, (f (by simp [hl])).trans (hp.label (j := NativeRustcVmArm.Vm.PlacementsOf.b28Offset) NativeRustcVmArm.Vm.PlacementsOf.label_22_at), ?_⟩)
    rw [← hl]; exact hI'
  · exact .done _ (.inl ⟨by omega, pc_of (t (by simp [hl])) rfl, hI'⟩)

/-- **`b27`**: placement `none` stored. -/
theorem store27 (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {c : Nat} (hc : c < 158)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b27Offset)) (hI : I3 m0 c st.data)
    (hpl : plF (κ m0) c = none) :
    Eventually (step1 Host.exe) (fun s ↦ (c + 1 < 158 ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b22Offset) ∧
      I3 m0 (c + 1) s.data) ∨ (c + 1 = 158 ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b28Offset) ∧
      I3 m0 158 s.data)) st := by
  have hb := hI.body
  have hr := pl_readable hF hb hc
  have hwf := Arrays.wf_one hr.1 hr.2
  have hm : Match (Env.ofMachine st.data [(pp m0 + BitVec.ofNat 64 (24 * c), 24)]) stS st.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl ⟨by
      show _ = (pp m0 + BitVec.ofNat 64 (24 * c)) + BitVec.ofInt 64 16
      rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, addr_add_add]; exact hI.x10,
      trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b27_in_code (by simp [b27]) hp) run_b27 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨k27, w27, f0⟩ := Arrays.after_eq run_b27 ▸ b27_facts
  have hb1 : Bd m0 st1.data := Bd.of_write hF hb hm hm1 hwf rfl k27 fun p hw ↦ by
    obtain ⟨w, hw', b, sz, hb', hin⟩ := written_in hwf hw fun w hw b sz hb' ↦ by
      obtain ⟨h0, h1⟩ := w27 w hw
      rw [h0] at hb'
      simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hb'
      omega
    obtain ⟨h0, -⟩ := w27 w hw'
    rw [h0] at hb'
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb'
    obtain ⟨rfl, rfl⟩ := hb'
    have := pl_in hF hc hin
    exact ⟨.inl this, not_top_of_apart hF.stack (by decide) hF.po hF.pr.2 this⟩
  have hs := Layout.same_of_region hm1 hwf (r := 0) (b := pp m0 + BitVec.ofNat 64 (24 * c))
    (sz := 24) rfl w27
  have n0 := Layout.Match.wordAt_write hm1 (r := 0) (o := 0) rfl (by omega) f0
  rw [addr_add_zero] at n0
  have hnew : PlacementWAt st1.data.dmem (pp m0 + BitVec.ofNat 64 (24 * c)) (plF (κ m0) c) := by
    rw [hpl]
    exact n0
  have e1 := Arrays.regs_eq_of hm hm1 [.X8, .X19, .X20, .X21, .X23, .X24, .X25] rfl
  have g9 := hm1.regs .X9 _ rfl
  have g10 := hm1.regs .X10 _ rfl
  sym_simp at g9 g10
  have e9 : (Env.ofMachine st.data [(pp m0 + BitVec.ofNat 64 (24 * c), 24)]).regs .X9 =
      BitVec.ofNat 64 c := by
    apply BitVec.eq_of_toNat_eq
    show st.data.regs.X9.toNat = _
    rw [hI.x9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hI' : I3 m0 (c + 1) st1.data := stored hF hc hI hb1 hs hnew (by
      show (st1.data.regs.getXReg .X9).toBitVec.toNat = _
      rw [g9, e9]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega) (by
      show (st1.data.regs.getXReg .X10).toBitVec = _
      rw [g10]
      show (pp m0 + BitVec.ofNat 64 (24 * c)) + BitVec.ofInt 64 40 = _
      rw [show BitVec.ofInt 64 40 = BitVec.ofNat 64 40 from rfl, addr_add_add,
        show 24 * c + 40 = 24 * (c + 1) + 16 by omega]) e1
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  rw [e9, show BitVec.ofNat 64 c + 1#64 = BitVec.ofNat 64 (c + 1) from
    (BitVec.ofNat_add _ _).symm, ofNat_beq' (by omega) (by decide)] at hpc1
  obtain ⟨f, t⟩ := Arrays.pc_cond hpc1
  by_cases hl : c + 1 = 158
  · refine .done _ (.inr ⟨hl, pc_of (t (by simp [hl])) rfl, ?_⟩)
    rw [← hl]; exact hI'
  · exact .done _ (.inl ⟨by omega, (f (by simp [hl])).trans (hp.label (j := NativeRustcVmArm.Vm.PlacementsOf.b22Offset) NativeRustcVmArm.Vm.PlacementsOf.label_17_at), hI'⟩)

end

end NativeRustcVmArm.Layout.PlacementsOf
