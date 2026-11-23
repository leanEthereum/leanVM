module

public import NativeRustcVmArm.Code.Vm.DecodedPhaseCount.Names
public import NativeRustcVmArm.Spec.Transcript
public import NativeRustcVmArm.Transcript.PhaseCount.Exec
public import NativeRustcVmArm.Transcript.Arith
public import NativeRustcVm.Transcript.Update

/-!
# `Decoded::phase_count` on AArch64

**`phaseCount_spec`**: X0 becomes the word at `streamEnd l` of the decoded area, the phase count.
`b0` computes `streamEnd l` and compares it with the slice's length, which the decoded area's
`decodedWords l ≤ len` bounds; `b1` loads the word (region 1 of its environment, at the address
`wordAddr` the block computes).
-/

namespace NativeRustcVmArm.Transcript.PhaseCount

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.DecodedPhaseCount
open NativeRustcVm.Transcript NativeVm.Model NativeRustcArm

public section

theorem toBitVec_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toBitVec.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

theorem ult_eq (x y : BitVec 64) : x.ult y = decide (x.toNat < y.toNat) := rfl

variable [Host] {k : Nat}

/-- **`Decoded::phase_count` meets its contract.** -/
theorem phaseCount_spec (hp : Placed code k) (a : DecArea) (stream : Array EW)
    (openings : Array (Array OpeningW)) :
    Spec (Labels.label NativeRustcVmArm.Vm.DecodedPhaseCount.entryLabel) (PhaseCountPre a stream openings)
      (PhaseCountPost openings) := by
  rintro m0 ⟨-, hdf, hmap, hnw, hap, ⟨hrm, hrn⟩, hdec⟩
  have hl64 := hdec.l_lt
  have hlen := hdec.len
  have hse := streamEnd_lt a.l
  have hnw : m0.regs.X0.toBitVec.toNat + 24 ≤ 2 ^ 64 := hnw
  have hrn : a.words.toNat + 8 * a.len ≤ 2 ^ 64 := hrn
  simp only [DecArea.region] at hrm
  have hlen64 : a.len < 2 ^ 64 := by omega
  -- `b0`: `streamEnd l` against the length.
  have hwf0 : (Env.ofMachine m0 [(m0.regs.X0.toBitVec, 24)]).WF :=
    Env.wf_of ⟨⟨hmap, hnw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm0 : Match (Env.ofMachine m0 [(m0.regs.X0.toBitVec, 24)]) entryS m0 :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl ⟨by simp [Sym.eval]; rfl, trivial⟩ trivial trivial
      trivial
  have hL : (Env.ofMachine m0 [(m0.regs.X0.toBitVec, 24)]).load 0 16 8 = a.l.toUInt64.toBitVec :=
    load_of_wordAt hdf.2.2
  have hN : (Env.ofMachine m0 [(m0.regs.X0.toBitVec, 24)]).load 0 8 8 = a.len.toUInt64.toBitVec :=
    load_of_wordAt hdf.2.1
  unfold NativeRustcVmArm.Vm.DecodedPhaseCount.entryLabel
  rw [hp.label (j := NativeRustcVmArm.Vm.DecodedPhaseCount.entryOffset) NativeRustcVmArm.Vm.DecodedPhaseCount.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun st1 hm1 hpc1 => ?_
  have hd1 : st1.data.dmem = m0.dmem := hm1.dmem_eq hwf0 rfl
  have hs1 : Saved m0 st1.data := Match.saved hm0 hm1 hwf0 rfl (after_eq run_b0 ▸ keeps_b0)
  have h30 : st1.data.regs.X30 = m0.regs.X30 := Match.reg_eq (r := .X30) hm0 hm1 rfl rfl
  have hx0 : st1.data.regs.X0 = m0.regs.X0 := Match.reg_eq (r := .X0) hm0 hm1 rfl rfl
  have hx8 : (st1.data.regs.getXReg .X8).toBitVec.toNat = NativeVm.streamEnd a.l := by
    rw [hm1.regs .X8 _ rfl]
    sym_simp
    rw [hL, streamEnd_eval, toBitVec_toUInt64 hl64]
  simp only [PcOk] at hpc1
  split at hpc1
  · rename_i hc
    exfalso
    sym_simp at hc
    rw [hL, hN, ult_eq, streamEnd_eval, toBitVec_toUInt64 hl64, toBitVec_toUInt64 hlen64] at hc
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hc
    omega
  -- `b1`: the word at `streamEnd l`.
  set wa := off a.words (8 * NativeVm.streamEnd a.l) with hwa
  have hwa64 : (off a.words (8 * NativeVm.streamEnd a.l)).toNat =
      a.words.toNat + 8 * NativeVm.streamEnd a.l := toNat_off (by omega)
  have hwf1 : (Env.ofMachine st1.data [(m0.regs.X0.toBitVec, 24), (wa, 8)]).WF := by
    refine Env.wf_of ⟨⟨fun i hi ↦ ?_, hnw⟩, ⟨fun i hi ↦ ?_, ?_⟩, trivial⟩ ?_
    · show (st1.data.dmem.get? (m0.regs.X0.toBitVec + BitVec.ofNat 64 i)).isSome
      rw [hd1]; exact hmap i hi
    · show (st1.data.dmem.get? (wa + BitVec.ofNat 64 i)).isSome
      rw [hd1, hwa, off_add]; exact hrm _ (by omega)
    · show wa.toNat + 8 ≤ 2 ^ 64
      rw [hwa64]; omega
    · refine List.pairwise_pair.mpr ?_
      show m0.regs.X0.toBitVec.toNat + 24 ≤ wa.toNat ∨ wa.toNat + 8 ≤ m0.regs.X0.toBitVec.toNat
      have hap : m0.regs.X0.toBitVec.toNat + 24 ≤ a.words.toNat ∨
        a.words.toNat + 8 * a.len ≤ m0.regs.X0.toBitVec.toNat := hap
      rw [hwa64]
      omega
  have hm1' : Match (Env.ofMachine st1.data [(m0.regs.X0.toBitVec, 24), (wa, 8)]) wordS st1.data := by
    refine match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
      ⟨known_ptr rfl (by show st1.data.regs.X0.toBitVec = _; rw [hx0]), trivial⟩ trivial trivial
      ⟨?_, trivial⟩
    have hw : (Env.ofMachine st1.data [(m0.regs.X0.toBitVec, 24), (wa, 8)]).load 0 0 8 = a.words :=
      load_ofMachine (o := 0) rfl (by rw [hd1, off_zero]; exact hdf.1)
    show _ = (Env.ofMachine st1.data [(m0.regs.X0.toBitVec, 24), (wa, 8)]).base 1 +
      BitVec.ofInt 64 0
    rw [show (Env.ofMachine st1.data [(m0.regs.X0.toBitVec, 24), (wa, 8)]).base 1 = wa from rfl,
      ofInt_zero64, BitVec.add_zero]
    simp only [wordAddr, Sym.eval, BinOp.apply, UnOp.apply, low_W64, ext_W64, hw]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, memExtend3_toNat, Env.ofMachine_regs, hx8]
    simp only [MemWidth.bits]
    rw [hwa64]
    omega
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf1 hpc1 hm1'
    fun st2 hm2 hpc2 => ?_
  have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq hwf1 rfl
  have hs2 : Saved st1.data st2.data := Match.saved hm1' hm2 hwf1 rfl (after_eq run_b1 ▸ keeps_b1)
  have h30' : st2.data.regs.X30 = st1.data.regs.X30 := Match.reg_eq (r := .X30) hm1' hm2 rfl rfl
  refine .done _ ⟨by simp only [PcOk] at hpc2; rw [hpc2]; simp only [retOf, h30', h30], ?_,
    fun q _ ↦ by rw [hd2, hd1], hs1.trans hs2⟩
  apply UInt64.toBitVec_inj.mp
  show (st2.data.regs.getXReg .X0).toBitVec = _
  rw [hm2.regs .X0 _ rfl]
  sym_simp
  exact load_ofMachine (o := 0) (r := 1) rfl (by rw [hd1, off_zero]; exact hdec.phase_count)

end

end NativeRustcVmArm.Transcript.PhaseCount
