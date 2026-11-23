module

public import NativeRustcVmX64.Transcript.PhaseCount.Exec
public import NativeRustcVmX64.Transcript.Arith
public import NativeRustcVmX64.Code.Vm.DecodedPhaseCount.Names

/-!
# `Decoded::phase_count` on x86-64

**`phaseCount_spec`**: RAX becomes the word at `streamEnd l` of the decoded area, the phase count.
`b0` computes `streamEnd l` and compares it with the slice's length, which the decoded area's
`decodedWords l ≤ len` bounds; `b1` loads the word (region 1 of its environment, at the address
`wordAddr` the block computes) and returns.
-/

namespace NativeRustcVmX64.Transcript.PhaseCount

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.DecodedPhaseCount
open NativeRustcVm.Transcript NativeVm.Model

public section

theorem toBitVec_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toBitVec.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

theorem ult_eq (x y : BitVec 64) : x.ult y = decide (x.toNat < y.toNat) := rfl

variable [Host] {k : Nat}

/-- **`Decoded::phase_count` meets its contract.** -/
theorem phaseCount_spec (hp : Placed code k) (a : DecArea) (stream : Array EW)
    (openings : Array (Array OpeningW)) :
    Spec (Labels.label NativeRustcVmX64.Vm.DecodedPhaseCount.entryLabel) (PhaseCountPre a stream openings)
      (PhaseCountPost openings) := by
  rintro m0 ⟨hst, hdf, hmap, hnw, hap, ⟨hrm, hrn⟩, hdec⟩
  set dp := reg m0 .rdi with hdp
  have hl64 := hdec.l_lt
  have hlen := hdec.len
  have hse := streamEnd_lt a.l
  have hnw : dp.toNat + 24 ≤ 2 ^ 64 := hnw
  have hrn : a.words.toNat + 8 * a.len ≤ 2 ^ 64 := hrn
  simp only [DecArea.region] at hrm
  have hlen64 : a.len < 2 ^ 64 := by omega
  -- `b0`: `streamEnd l` against the length.
  have hwf0 : (Env.ofMachine m0 [(dp, 24)]).WF :=
    Env.wf_of ⟨⟨hmap, hnw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hL : (Env.ofMachine m0 [(dp, 24)]).load 0 16 8 = a.l.toUInt64.toBitVec :=
    load_of_wordAt hdf.2.2
  have hN : (Env.ofMachine m0 [(dp, 24)]).load 0 8 8 = a.len.toUInt64.toBitVec :=
    load_of_wordAt hdf.2.1
  have hm0 : Match (Env.ofMachine m0 [(dp, 24)]) entryS m0 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨known_ptr rfl rfl, trivial⟩ trivial trivial trivial
  unfold NativeRustcVmX64.Vm.DecodedPhaseCount.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.DecodedPhaseCount.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 nofun hm0
    fun st1 hm1 hpc1 => ?_
  obtain ⟨hk1, hmem1, hx7, hx6, hx0⟩ := after_eq run_b0 ▸ ok_b0
  have hd1 : st1.data.dmem = m0.dmem := hm1.dmem_eq hwf0 hmem1
  have hs1 : Saved m0 st1.data := Match.saved hm0 hm1 hwf0 rfl hk1
  have hX7 : reg st1.data .rdi = dp := (hm1.regs .rdi _ hx7).trans (eval_ptr rfl)
  have hX6 : rspOf st1.data = rspOf m0 := hm1.regs .rsp _ hx6
  have hX0 : (reg st1.data .rax).toNat = NativeVm.streamEnd a.l := by
    rw [show reg st1.data .rax = _ from hm1.regs .rax _ hx0]
    sym_simp
    rw [hL, streamEnd_eval, toBitVec_toUInt64 hl64]
  simp only [PcOk] at hpc1
  split at hpc1
  · rename_i hc
    exfalso
    sym_simp_at hc
    rw [hL, hN, ult_eq, toBitVec_toUInt64 hlen64] at hc
    have := streamEnd_eval a.l.toUInt64.toBitVec
    rw [toBitVec_toUInt64 hl64] at this
    simp only [this, Bool.not_eq_true', decide_eq_false_iff_not] at hc
    omega
  -- `b1`: the word at `streamEnd l`.
  set wa := off a.words (8 * NativeVm.streamEnd a.l) with hwa
  have hwa64 : wa.toNat = a.words.toNat + 8 * NativeVm.streamEnd a.l := toNat_off (by omega)
  have hwf1 : (Env.ofMachine st1.data [(dp, 24), (wa, 8)]).WF := by
    refine Env.wf_of ⟨⟨fun i hi ↦ ?_, hnw⟩, ⟨fun i hi ↦ ?_, ?_⟩, trivial⟩ ?_
    · show (st1.data.dmem.get? (dp + BitVec.ofNat 64 i)).isSome
      rw [hd1]; exact hmap i hi
    · show (st1.data.dmem.get? (wa + BitVec.ofNat 64 i)).isSome
      rw [hd1, hwa, off_add]; exact hrm _ (by omega)
    · show wa.toNat + 8 ≤ 2 ^ 64
      rw [hwa64]; omega
    · refine List.pairwise_pair.mpr ?_
      show dp.toNat + 24 ≤ wa.toNat ∨ wa.toNat + 8 ≤ dp.toNat
      have hap : dp.toNat + 24 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ dp.toNat := hap
      rw [hwa64]
      omega
  have hm1' : Match (Env.ofMachine st1.data [(dp, 24), (wa, 8)]) wordS st1.data := by
    refine match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨known_ptr rfl hX7, trivial⟩ trivial trivial
      ⟨?_, trivial⟩
    have hw : (Env.ofMachine st1.data [(dp, 24), (wa, 8)]).load 0 0 8 = a.words :=
      load_ofMachine (o := 0) rfl (by rw [hd1, off_zero]; exact hdf.1)
    show _ = (Env.ofMachine st1.data [(dp, 24), (wa, 8)]).base 1 + BitVec.ofInt 64 0
    rw [show (Env.ofMachine st1.data [(dp, 24), (wa, 8)]).base 1 = wa from rfl, ofInt_zero64,
      BitVec.add_zero]
    simp only [wordAddr, Sym.eval, BinOp.apply, low_W64, ext_W64, hw, Env.ofMachine_regs]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_mul, hX0, hwa64]
    simp only [BitVec.toNat_ofNat, show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl]
    omega
  refine exec_at (infix_of ((infix_take b1 2).trans b1_in_code (by simp [b1])) (by simp [b1]) hp)
    run_b1 hwf1 nofun (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.DecodedPhaseCount.b0_next)) hm1'
    fun st2 hm2 hpc2 => ?_
  obtain ⟨hk2, hmem2, hx6', hx0'⟩ := after_eq run_b1 ▸ ok_b1
  have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq hwf1 hmem2
  have hs2 : Saved m0 st2.data := hs1.trans (Match.saved hm1' hm2 hwf1 rfl hk2)
  have hX0' : reg st2.data .rax = openings.size.toUInt64.toBitVec := by
    rw [show reg st2.data .rax = _ from hm2.regs .rax _ hx0']
    exact load_ofMachine (o := 0) (r := 1) rfl (by rw [hd1, off_zero]; exact hdec.phase_count)
  -- The `ret`.
  have hf2 : Frame m0 0 [] 0 st2.data :=
    Frame.of_saved hs2 ((hm2.regs .rsp _ hx6').trans hX6) fun j _ ↦ by rw [hd2, hd1]
  have hwf2 := frame_wf (m0 := m0) (d := st2.data) (F := 0) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst le_rfl) hf2.kept, frame_noWrap hst le_rfl⟩
    (by simp) (List.pairwise_singleton _ _)
  refine exec_at (infix_of ((infix_drop b1 2).trans b1_in_code (by simp [b1])) (by simp [b1]) hp)
    run_b1r hwf2 nofun (hpc2.trans (congrArg Host.addrOf (by simp [b1, Nat.add_assoc])))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf2.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st3 hm3 hpc3 => ?_
  obtain ⟨hepi, hmem3, hx0''⟩ := after_eq run_b1r ▸ ok_b1r
  obtain ⟨hsv3, hrsp3⟩ := Frame.epilogue hf2 hwf2 hm3 hepi
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
  simp only [PcOk] at hpc3
  refine .done _ ⟨by rw [hpc3]; exact hf2.load_ret hst le_rfl, hrsp3,
    (hm3.regs .rax _ hx0'').trans hX0', fun q _ ↦ by rw [hd3, hd2, hd1], hsv3⟩

end

end NativeRustcVmX64.Transcript.PhaseCount
