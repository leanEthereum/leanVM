module

public import NativeRustcVmArm.Wire.WriteOpenings.A.Query
public import NativeRustcVmArm.Wire.WriteOpenings.B.Query
public import NativeRustcVmArm.Wire.WriteOpenings.Z.Loop

/-!
# `write_openings` from its entry

The prologue (`b0`, from `entryS`, region 0 the frame and the two stack arguments): the frame
(`fr_entry`), the head written, the registers `Ent`. With levels (`b1`, from `argS`): the
queries' loop head `HeadA`. Without (`b23`): a leaf (`b24`, `HeadB`), or none (`b38`, `HeadZ`).
Hence the postcondition from the entry (`entry_spec`).
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVmArm.Vm.WriteOpenings

@[expose] public section

/-- The registers after the prologue. -/
structure Ent (R : Run) (m : MachineData) : Prop where
  fr : Frm R m
  x0 : rv m .X0 = R.qa
  x1 : rv m .X1 = BitVec.ofNat 64 (8 * R.np)
  x2 : rv m .X2 = R.qa
  x3 : rv m .X3 = R.oa 24
  x4 : rv m .X4 = R.lv
  x5 : rv m .X5 = R.qa + BitVec.ofNat 64 (8 * R.nq)
  x6 : rv m .X6 = BitVec.ofNat 64 R.h
  x7 : rv m .X7 = R.sb
  x10 : rv m .X10 = R.out
  x19 : rv m .X19 = R.pa
  x21 : rv m .X21 = BitVec.ofNat 64 R.lw
  done : R.Done m.dmem 0

/-- The entry's regions: the frame and the stack arguments, the phase's head. -/
abbrev entryRs (R : Run) : List (BitVec 64 × Nat) := [(base R.m0 176, 192), (R.out, 24)]

end

public section

theorem toBitVec_ofNat (x : UInt64) : x.toBitVec = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, UInt64.toNat_toBitVec, Nat.mod_eq_of_lt x.toNat_lt]

theorem toUInt64_toNat (x : UInt64) : x.toNat.toUInt64 = x :=
  UInt64.toNat_inj.mp (toNat_toUInt64_of_lt x.toNat_lt)

theorem lslS (x : BitVec 64) (n : Nat) :
    UnOp.apply (.shift .LSL n) .W64 x = BitVec.ofNat 64 (x.toNat * 2 ^ n) := by
  simp only [UnOp.apply, Sym.low_W64, Sym.ext_W64, shiftW]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem lsl11 (x : BitVec 64) :
    UnOp.apply (.ubfm 53 52) .W64 x = BitVec.ofNat 64 (2048 * x.toNat) := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  apply BitVec.eq_of_toNat_eq
  simp [evalUBFM, toNat_take3, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

variable {R : Run}

theorem big1 : R.big 1 = ⟨R.m0.regs.SP.toBitVec, 16⟩ := rfl

theorem Geo.spNw (G : Geo R) : R.m0.regs.SP.toNat + 16 ≤ 2 ^ 64 := by
  have h := G.noWrap (i := 1) (by omega)
  rw [big1] at h
  exact h

theorem Geo.baseNat (G : Geo R) : (base R.m0 176).toNat = R.m0.regs.SP.toNat - 176 :=
  Ring.base_toNat G.st.2.1

/-- The frame and the stack arguments: 192 bytes from the frame's base, mapped. -/
theorem Geo.args_mapped (G : Geo R) : NativeRustcVm.Mapped R.d0 (base R.m0 176) 192 := by
  intro i hi
  by_cases h : i < 176
  · exact Ring.frame_mapped G.st (le_refl _) i h
  · have hm := (G.ok 1 (by omega)).1
    rw [big1] at hm
    have := hm (i - 176) (by show i - 176 < 16; omega)
    rwa [← Ring.base_add_eq (F := 176), addr_add (show 176 + (i - 176) = i by omega)] at this

theorem Geo.args_noWrap (G : Geo R) : NativeRustcVm.NoWrap (base R.m0 176) 192 := by
  unfold NativeRustcVm.NoWrap
  rw [G.baseNat]
  have := G.spNw
  have := G.st.2.1
  omega

theorem head_inside : Inside R.out 24 (R.big 7) := by
  have := ob_le (j := 0) (by omega)
  exact ⟨le_refl _, by show R.out.toNat + 24 ≤ R.out.toNat + phaseBytes; unfold ob at this; omega⟩

theorem Geo.entry_wf (G : Geo R) : (Env.ofMachine R.m0 (entryRs R)).WF := by
  have hi := head_inside (R := R)
  refine Env.wf_of ⟨⟨G.args_mapped, G.args_noWrap⟩, ⟨hi.mapped (G.ok 7 (by omega)),
    hi.noWrap G.outNw⟩, trivial⟩ (List.pairwise_pair.mpr ?_)
  have h0 := G.apart (i := 0) (j := 7) (by omega) (by omega) (by omega)
  have h1 := G.apart (i := 1) (j := 7) (by omega) (by omega) (by omega)
  rw [big0, big7] at h0
  rw [big1, big7] at h1
  unfold NativeRustcVm.Apart at h0 h1
  unfold NativeRustcArm.Apart
  simp only at h0 h1 ⊢
  have := G.baseNat
  have : R.m0.regs.SP.toBitVec.toNat = R.m0.regs.SP.toNat := UInt64.toNat_toBitVec _
  have := G.st.2.1
  have := ob_le (j := 0) (by omega)
  unfold ob at this
  omega

/-- **After the prologue**: the frame, given the prologue's writes, the slots and the head. -/
theorem fr_entry [Labels] (G : Geo R) {S : SState} {m : MachineData}
    (hm : Match (Env.ofMachine R.m0 (entryRs R)) S m) (hwf : (Env.ofMachine R.m0 (entryRs R)).WF)
    (hsp : S.sp = .ptr 0 0) (hok : Ring.slotsOk S slots = true)
    (hmem : ∀ w ∈ S.mem, (w.r = 0 ∧ w.off + w.n ≤ 176) ∨ (w.r = 1 ∧ w.off + w.n ≤ 24)) :
    Frm R m where
  sp := by rw [hm.sp, hsp]; simp [Sym.eval]
  keep r hr := absurd hr (by simp)
  slots p hp := by
    have hw := hm.bytesAt_write (r := 0) (o := p.1) (n := 8) (b := base R.m0 176) (sz := 192) rfl
      ((show ∀ p ∈ slots, p.1 + 8 ≤ 192 by decide) p hp) (v := .reg p.2)
      fun i hi ↦ Ring.slotsOk_iff hok p hp i hi
    rw [Ring.wordBytes_reg] at hw
    exact hw
  same q hq := by
    refine hm.get?_mem0 hwf fun ⟨w, hw, b, sz, hb, h1, h2⟩ ↦ hq ?_
    have hN := G.st.2.1
    rcases hmem w hw with ⟨hr, hn⟩ | ⟨hr, hn⟩
    · rw [hr] at hb
      cases hb
      refine .inl ?_
      rw [Sym.inRange_iff (Ring.base_noWrap hN), Ring.base_toNat hN]
      rw [Ring.base_toNat hN] at h1 h2
      omega
    · rw [hr] at hb
      cases hb
      refine .inr ?_
      have := ob_le (j := 0) (by omega)
      unfold ob at this
      show InRange R.out phaseBytes q
      rw [Sym.inRange_iff G.outNw]
      omega
  kept := hm.kept hwf

variable [Host]

/-- **The prologue** (`b0`): with levels, `b1`; without, `b23`. -/
theorem b0_step (hp : Placed code R.k) (G : Geo R) {Q : MachineState → Prop}
    (hA : ∀ st, st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b1Offset → Ent R st.data → 0 < R.h → Eventually (step1 Host.exe) Q st)
    (hB : ∀ st, st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b23Offset → Ent R st.data → R.h = 0 →
      Eventually (step1 Host.exe) Q st) :
    Eventually (step1 Host.exe) Q ⟨R.m0, Host.addrOf (R.k + NativeRustcVmArm.Vm.WriteOpenings.b0Offset)⟩ := by
  have hwf := G.entry_wf
  have hN := G.st.2.1
  have hm : Match (Env.ofMachine R.m0 (entryRs R)) entryS R.m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ G.aligned, rfl, nofun, trivial⟩
      (by
        simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]
        rw [show BitVec.ofInt 64 176 = BitVec.ofNat 64 176 from rfl]
        exact Ring.base_add_eq.symm)
      trivial trivial trivial ⟨by
        simp only [Sym.eval]
        rw [Ring.load_word (v := UInt64.ofBitVec R.out) (by
          show WordAt R.d0 (base R.m0 176 + BitVec.ofNat 64 184) _
          rw [← addr_add (show 176 + 8 = 184 by omega), Ring.base_add_eq]
          exact G.outW)]
        show R.out = R.out + BitVec.ofInt 64 0
        rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun s1 hm1 hpc1 ↦ ?_
  have hfr1 : Frm R s1.data := fr_entry G hm1 hwf rfl (by decide +kernel) (by decide)
  have e : ∀ x : XReg, (m : MachineData) → rv m x = (m.regs.getXReg x).toBitVec := fun _ _ ↦ rfl
  have hhead : R.Head s1.data.dmem := by
    have w0 := stored hm1 (r := 1) (o := 0) (sz := 24) (v := .reg .X1) rfl (by omega) (by decide)
    have w8 := stored hm1 (r := 1) (o := 8) (sz := 24) (v := .reg .X6) rfl (by omega) (by decide)
    have w16 := stored hm1 (r := 1) (o := 16) (sz := 24) (v := .reg .X5) rfl (by omega)
      (by decide)
    simp only [Sym.eval, Env.ofMachine_regs] at w0 w8 w16
    refine ⟨?_, ?_, ?_⟩
    · rw [Run.nq, toUInt64_toNat]; exact w0
    · rw [Run.h, toUInt64_toNat]; exact w8
    · rw [Run.lw, toUInt64_toNat]; exact w16
  have E : Ent R s1.data := by
    refine ⟨hfr1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ⟨hhead, fun _ h ↦ absurd h (by omega)⟩⟩
    · rw [hm1.regs .X0 _ rfl]; rfl
    · rw [hm1.regs .X1 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs, lsl3]
      rfl
    · rw [hm1.regs .X2 _ rfl]; rfl
    · rw [hm1.regs .X3 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64]
      rw [Ring.load_word (v := UInt64.ofBitVec R.out) (by
        show WordAt R.d0 (base R.m0 176 + BitVec.ofNat 64 184) _
        rw [← addr_add (show 176 + 8 = 184 by omega), Ring.base_add_eq]
        exact G.outW)]
    · rw [hm1.regs .X4 _ rfl]; rfl
    · rw [hm1.regs .X5 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs, lslS]
      show R.qa + _ = R.qa + _
      congr 2
      show R.m0.regs.X1.toNat * 8 = 8 * R.m0.regs.X1.toNat
      omega
    · rw [hm1.regs .X6 _ rfl]
      exact toBitVec_ofNat _
    · rw [hm1.regs .X7 _ rfl]; rfl
    · rw [hm1.regs .X10 _ rfl]
      simp only [Sym.eval]
      rw [Ring.load_word (v := UInt64.ofBitVec R.out) (by
        show WordAt R.d0 (base R.m0 176 + BitVec.ofNat 64 184) _
        rw [← addr_add (show 176 + 8 = 184 by omega), Ring.base_add_eq]
        exact G.outW)]
    · rw [hm1.regs .X19 _ rfl]; rfl
    · rw [hm1.regs .X21 _ rfl]
      exact toBitVec_ofNat _
  have hc : (SBool.cmp .eq .W64 (.reg .X6) (.lit 0)).eval (Env.ofMachine R.m0 (entryRs R)) =
      decide (R.h = 0) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs]
    rw [ofNat_toNat (by omega)]
    rfl
  simp only [PcOk, hc] at hpc1
  by_cases hh : R.h = 0
  · simp only [hh, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b23Offset) NativeRustcVmArm.Vm.WriteOpenings.label_20_at] at hpc1
    exact hB s1 hpc1 E hh
  · simp only [hh, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    exact hA s1 (hpc1.trans (congrArg Host.addrOf rfl)) E (by omega)

end

end NativeRustcVmArm.Wire.WriteOpenings
