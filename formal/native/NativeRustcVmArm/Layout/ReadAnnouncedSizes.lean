module

public import NativeRustcVmArm.Code.Vm.BuildLayout.Names
public import NativeRustcVmArm.Code.Vm.ReadAnnouncedSizes.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.Layout.ReadAnnouncedSizes.Tail
public import NativeRustcVmArm.Transcript.Callee

/-!
# `read_announced_sizes` on AArch64

**`readAnnouncedSizes_spec`**: rustc's `read_announced_sizes(t, bytecode_len, layout)`, placed
anywhere in the program, meets `ReadAnnouncedSizesPre`/`Post` given `read_scalars`' and
`build_layout`'s contracts. The prologue (`b0`) saves X30, X19-X21 in its 208-byte frame, keeps
`layout` in X19 and `bytecode_len` in X20 and reads the eight scalars into `announced` (frame bytes
`0`-`128`); `b1` returns `0` on `None`; then `checks` (`b2`-`b9`, the high limbs) and `from10`
(`b10`-`b14`: the rate, `build_layout`, the stack's log-size). The model is
`NativeVm.Math.Layout.readAnnouncedSizes_run` with `tailP`.
-/

namespace NativeRustcVmArm.Layout.ReadAnnouncedSizes

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ReadAnnouncedSizes NativeVm.Model
open NativeRustcVm.Layout NativeRustcVm.Transcript
open NativeRustcVm (WordAt EWsAt)
open NativeVm.Math.Layout (readAnnouncedSizes_run)

public section

variable [Host] {k : Nat}

/-- **`read_announced_sizes`' contract.** -/
theorem readAnnouncedSizes_spec (hp : Placed code k)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hbl : ∀ bc, Spec (Labels.label NativeRustcVmArm.Vm.BuildLayout.entryLabel) (BuildLayoutPre bc) (BuildLayoutPost bc))
    (bc : Array UInt64) (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmArm.Vm.ReadAnnouncedSizes.entryLabel) (ReadAnnouncedSizesPre bc a s)
      (ReadAnnouncedSizesPost bc a s) := by
  intro m0 hpre
  obtain ⟨hst, hrc, -, hts0, htok, -⟩ := id hpre
  have hF : 208 ≤ N := by have := le_rs; omega
  have hn : N ≤ m0.regs.SP.toNat := hst.2.1
  obtain ⟨⟨-, hTn⟩, -, -⟩ := hts0.footprint
  obtain ⟨-, hfn, hfb⟩ := Arrays.frame_ok hst hF
  -- `b0`: the prologue, `announced` zeroed, `bl read_scalars`.
  obtain ⟨hwf0, hm0⟩ := Arrays.entry_match hst hF (by decide)
  rw [lbl_entry hp]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hw0, hmem0, hregs0⟩ := b0_frame
  obtain ⟨hsp0, x0, x1, x2, x19, x20⟩ := b0_regs
  rw [after_eq run_b0] at hw0 hmem0 hregs0 hsp0 x0 x1 x2 x19 x20
  have hfr1 : Fr m0 st1.data := Frame.of_entry (rs := []) hst hF hm1 hwf0 hsp0 hw0 hregs0 hmem0
  have hs1 : SameOutside m0.dmem st1.data.dmem (InRange (fbase m0 208) 208) :=
    same_of_region hm1 hwf0 (r := 0) rfl hmem0
  have hX0 : st1.data.regs.X0.toBitVec = tt m0 := hm1.regs .X0 _ x0
  have hX1 : st1.data.regs.X1.toBitVec = fbase m0 208 := by
    rw [show st1.data.regs.X1 = st1.data.regs.getXReg .X1 from rfl, hm1.regs .X1 _ x1]
    show fbase m0 208 + BitVec.ofInt 64 0 = _
    rw [ofInt_zero, BitVec.add_zero]
  have hX2 : st1.data.regs.X2.toNat = 8 := by
    rw [← UInt64.toNat_toBitVec,
      show st1.data.regs.X2 = st1.data.regs.getXReg .X2 from rfl, hm1.regs .X2 _ x2]
    rfl
  have hX19 : st1.data.regs.X19 = m0.regs.X2 := UInt64.toBitVec_inj.mp (hm1.regs .X19 _ x19)
  have hX20 : st1.data.regs.X20 = m0.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X20 _ x20)
  have hts1 : TStateAt st1.data.dmem (tt m0) a s := hts0.frame (hm1.kept hwf0) (frame_tstate hpre) hs1
  have hsp1 : st1.data.regs.SP.toNat = m0.regs.SP.toNat - 208 := by
    rw [← UInt64.toNat_toBitVec, hfr1.sp, hfb]; rfl
  have hrs' : readScalarsStack ≤ N - 208 := by have := le_rs; omega
  have hprs : ReadScalarsPre a s st1.data := by
    show StackOk _ _ ∧ RcAt _ _ ∧ TStateAt _ st1.data.regs.X0.toBitVec a s ∧
      TStateOk _ st1.data.regs.X0.toBitVec a _ ∧
      OutOk _ st1.data.regs.X0.toBitVec a st1.data.regs.X1.toBitVec (16 * st1.data.regs.X2.toNat) _
    rw [hX0, hX1, hX2]
    have hout := NativeRustcVmArm.Transcript.OutOk.frame (n' := readScalarsStack) (ob := 0)
      (l := 16 * 8) hst hF hrs' hfr1.sp hfr1.kept (by decide) htok hrc
    rw [off_zero] at hout
    exact ⟨stackOk_callee hst hfr1 (by decide) le_rs,
      NativeRustcVmArm.Transcript.RcAt.callee hrc
        (NativeRustcVmArm.Transcript.rc_keep hfr1.same (rc_out hpre)) hn hF hsp1 hrs',
      hts1, NativeRustcVmArm.Transcript.TStateOk.callee htok hfr1.sp hn hF hrs', hout⟩
  refine call_then hpc1 (hrs a s) hprs fun st2 hpc2 ⟨hok2, hxs2, hnext2, hs2, hsv2⟩ ↦ ?_
  rw [hX0, hX1, hX2] at hs2
  rw [hX1, hX2] at hxs2
  rw [hX0, hX2] at hnext2
  rw [show (16 * 8 : Nat) = 128 from rfl] at hs2
  have hfr2 : Fr m0 st2.data := by
    refine Frame.call hfr1 hs2 hsv2 (fun p hp ↦ ?_) fun q hq i hi ↦ ?_
    · rcases hp with hp | hp | hp
      · exact Or.inr (frame_in_stack hst hF (NativeRustcVmArm.Transcript.inRange_sub hfn le_rfl
          (by omega) hp))
      · exact Or.inl (Or.inr hp)
      · exact Or.inr (callee_stack hst hfr1.sp le_rs hp)
    · have hq8 : 176 ≤ q.1 ∧ q.1 + 8 ≤ 208 := by
        revert q; decide
      rw [NativeRustcVm.addr_add]
      have hfbN := fbase_toNat hst hF
      have hlt := m0.regs.SP.toNat_lt
      have e : (fbase m0 208 + BitVec.ofNat 64 (q.1 + i)).toNat =
          (fbase m0 208).toNat + (q.1 + i) := Arrays.toNat_add_ofNat' (by omega)
      have hin : InRange (fbase m0 208) 208 (fbase m0 208 + BitVec.ofNat 64 (q.1 + i)) :=
        (Sym.inRange_iff (show NoWrap (fbase m0 208) 208 by unfold NoWrap; omega)).mpr
          (by rw [e]; omega)
      rintro (h | h | h)
      · rw [Sym.inRange_iff (show NoWrap (fbase m0 208) 128 by unfold NoWrap; omega), e] at h
        omega
      · exact (frame_tstate hpre _ hin).1 h
      · exact callee_below hst hfr1.sp le_rs (by omega) h
  have h19 : st2.data.regs.X19 = m0.regs.X2 := (hsv2.1 .X19 rfl).trans hX19
  have h20 : st2.data.regs.X20 = m0.regs.X1 := (hsv2.1 .X20 rfl).trans hX20
  -- `b1`: `None` returns `0`.
  obtain ⟨hwf2, hm2⟩ := fr_match hst hfr2
  obtain ⟨k1, m1, -⟩ := keeps_b1_b9
  rw [after_eq run_b1] at k1 m1
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf2
    (hpc2.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.ReadAnnouncedSizes.b0_next])) hm2 fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hfr3, hd3⟩ := fr_step hst hfr2 hm2 hm3 hwf2 k1 m1
  have he3 := Arrays.regs_eq_of hm2 hm3 _ (show ([XReg.X19, .X20].all fun r ↦
    (frS.reg r).isSome && (after b1 frS).reg r == frS.reg r) = true by
      rw [after_eq run_b1]; decide)
  have hx03 : st3.data.regs.X0 = 0 := UInt64.toBitVec_inj.mp (hm3.regs .X0 _ rfl)
  have h0v : (st2.data.regs.getXReg .X0).toBitVec = (okWord ((readScalars 8).run s).isSome).toBitVec := by
    show st2.data.regs.X0.toBitVec = _; rw [hok2, hX2]
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  simp only [Env.ofMachine_regs, h0v] at hpc3
  cases hr : (readScalars 8).run s with
  | none =>
    simp (config := { decide := true }) only [hr, Option.isSome_none, okWord,
      ↓reduceIte] at hpc3
    refine fail16 hp hst (hpc3.trans (lbl_14 hp)) hfr3 hx03 ?_
    rw [readAnnouncedSizes_run, show 2 + nTables = 8 from rfl, hr]; rfl
  | some p =>
  obtain ⟨xs, s1⟩ := p
  simp (config := { decide := true }) only [hr, Option.isSome_some, okWord, ↓reduceIte] at hpc3
  have hsz := NativeRustcVm.Sumcheck.readScalars_size hr
  have hM : Mid m0 xs st2.data.dmem st3.data :=
    ⟨hfr3, hd3, ⟨(he3 .X19 (by simp)).trans h19, (he3 .X20 (by simp)).trans h20⟩, hx03,
      by rw [hd3]; exact hxs2 xs s1 hr, hsz⟩
  exact checks hp hst hr (hpc3.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.ReadAnnouncedSizes.b1_next]))
    hM fun s' hpc' hM' hc ↦ from10 hp hbl hpre hr (hnext2 xs s1 hr) hpc' hM' hc

end

end NativeRustcVmArm.Layout.ReadAnnouncedSizes
