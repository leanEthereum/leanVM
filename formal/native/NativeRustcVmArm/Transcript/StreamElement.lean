module

public import NativeRustcVmArm.Code.Vm.DecodedStreamElement.Names
public import NativeRustcVmArm.Spec.Transcript
public import NativeRustcVmArm.Transcript.StreamElement.Exec
public import NativeRustcVmArm.Transcript.Arith
public import NativeRustcVm.Transcript.Update

/-!
# `Decoded::stream_element` on AArch64

**`streamElement_spec`**: the `Option<EW>` at X0 becomes `stream[i]?`. The slice is not empty
(`b0`); `i` below the count (`b1`) and `2 i + 3` within the slice (`b2`, never failing below the
count, the stream within `streamEnd l`) lead to `b4`, which copies element `i`; otherwise `b3` stores
the tag `0`. Each block runs from a fresh environment of the state it starts in.
-/

namespace NativeRustcVmArm.Transcript.StreamElement

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.DecodedStreamElement
open NativeRustcVm.Transcript NativeVm.Model NativeRustcArm

public section

theorem toBitVec_toUInt64' {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toBitVec.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-- What a block keeps of the machine state it starts in. -/
structure Kept (m m' : MachineData) : Prop where
  dmem : m'.dmem = m.dmem
  saved : Saved m m'
  x0 : m'.regs.X0 = m.regs.X0
  x1 : m'.regs.X1 = m.regs.X1
  x2 : m'.regs.X2 = m.regs.X2
  x3 : m'.regs.X3 = m.regs.X3
  x30 : m'.regs.X30 = m.regs.X30

/-- `b2`'s bound: `2 i + 3 ≤ len`. -/
theorem ult_or_eq {x3 x2 : BitVec 64} {i n : Nat} (h3 : x3.toNat = i) (h2 : x2.toNat = n)
    (hi : 2 * i + 3 ≤ n) :
    (BitVec.ult (evalUBFM (w := .W64) x3 63 62 + 3#64) x2 ||
      evalUBFM (w := .W64) x3 63 62 + 3#64 == x2) = true := by
  have hv : (evalUBFM (w := .W64) x3 63 62 + 3#64 : BitVec 64).toNat = 2 * i + 3 := by
    rw [BitVec.toNat_add, evalUBFM_lsl1_toNat, h3]
    have := x2.isLt
    simp only [BitVec.toNat_ofNat, MemWidth.bits] at this ⊢
    omega
  rcases Nat.lt_or_eq_of_le hi with h | h
  · simp only [BitVec.ult, hv, h2, h, decide_true, Bool.true_or]
  · have : evalUBFM (w := .W64) x3 63 62 + 3#64 = x2 := BitVec.eq_of_toNat_eq (by rw [hv, h2, h])
    simp only [this, beq_self_eq_true, Bool.or_true]

/-- `b2`'s carry: `2 i + 4` does not wrap. -/
theorem unsigned_add4 {x3 : BitVec 64} {i : Nat} (h3 : x3.toNat = i) (hi : 2 * i + 4 < 2 ^ 64) :
    (BitVec.unsigned (evalUBFM (w := .W64) x3 63 62 + 4#64) !=
      BitVec.unsigned (evalUBFM (w := .W64) x3 63 62) + (4#64).unsigned) = false := by
  have h0 : (evalUBFM (w := .W64) x3 63 62 : BitVec 64).toNat = 2 * i := by
    rw [evalUBFM_lsl1_toNat, h3]; omega
  have hv : (evalUBFM (w := .W64) x3 63 62 + 4#64 : BitVec 64).toNat = 2 * i + 4 := by
    rw [BitVec.toNat_add, h0]
    simp only [BitVec.toNat_ofNat, MemWidth.bits]
    omega
  simp only [BitVec.unsigned, hv, h0, BitVec.toNat_ofNat]
  simp

variable [Host] {k : Nat}

/-- The tag `0` stored at the output: `None`. -/
theorem finish_none {m0 : MachineData} {stream : Array EW} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.DecodedStreamElement.b3Offset)) (hp : Placed code k)
    (hon : NativeRustcVm.NoWrap m0.regs.X0.toBitVec 24) (hom : Mapped m0.dmem m0.regs.X0.toBitVec 24)
    (hK : Kept m0 st.data) (hi : stream.size ≤ m0.regs.X3.toNat) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ StreamElementPost stream m0 st'.data)
      st := by
  set o := m0.regs.X0.toBitVec
  have hwf : (Env.ofMachine st.data [(o, 24)]).WF :=
    Env.wf_of ⟨⟨fun i hi ↦ hK.saved.2.2 _ (hom i hi), hon⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine st.data [(o, 24)]) noneS st.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl ⟨known_ptr rfl (by
      show st.data.regs.X0.toBitVec = _; rw [hK.x0]), trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf hpc hm fun st' hm' hpc' => ?_
  obtain ⟨hw, hws, hkeeps, h30⟩ := after_eq run_b3 ▸ none_b3
  have hx30 : st'.data.regs.X30 = m0.regs.X30 := (Match.reg_eq hm hm' rfl h30).trans hK.x30
  have hsame : SameOutside st.data.dmem st'.data.dmem (InRange o 24) := fun q hq ↦
    hm'.get?_mem0 hwf fun hW ↦ hq (by
      obtain ⟨j, hj, -, rfl⟩ := touch_of_written hwf rfl le_rfl hws hW
      exact inRange_off_self hj (by omega))
  refine .done _ ⟨by simp only [PcOk] at hpc'; rw [hpc']; simp only [retOf, hx30], ?_, ?_,
    hK.saved.trans (Match.saved hm hm' hwf rfl hkeeps)⟩
  · rw [Array.getElem?_eq_none hi]
    have := wordAt_write hm' (r := 0) (o := 0) rfl (by omega) fun i hi ↦ by
      rw [Nat.zero_add]; exact hw i hi
    rwa [off_zero] at this
  · intro q hq
    rw [hsame q hq, hK.dmem]

/-- **`Decoded::stream_element` meets its contract.** -/
theorem streamElement_spec (hp : Placed code k) (a : DecArea) (stream : Array EW)
    (openings : Array (Array OpeningW)) :
    Spec (Labels.label NativeRustcVmArm.Vm.DecodedStreamElement.entryLabel) (StreamElementPre a stream openings)
      (StreamElementPost stream) := by
  rintro m0 ⟨-, hx1, hx2, ⟨hrm, hrn⟩, hdec, hom, hon, hap⟩
  have hl64 := hdec.l_lt
  have hlen := hdec.len
  have hse := streamEnd_lt a.l
  have hsl := hdec.stream_le
  have hrn : a.words.toNat + 8 * a.len ≤ 2 ^ 64 := hrn
  simp only [DecArea.region] at hrm
  simp only [NativeVm.streamEnd, NativeVm.maxStream] at hse hsl
  have hlen64 : a.len < 2 ^ 64 := by omega
  -- `b0`: the slice is not empty.
  unfold NativeRustcVmArm.Vm.DecodedStreamElement.entryLabel
  rw [hp.label (j := NativeRustcVmArm.Vm.DecodedStreamElement.entryOffset) NativeRustcVmArm.Vm.DecodedStreamElement.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 (Env.wf_nil m0) (match_nil m0)
    fun st1 hm1 hpc1 => ?_
  have hK1 : Kept m0 st1.data :=
    { dmem := hm1.dmem_eq (Env.wf_nil _) rfl
      saved := Match.saved (match_nil m0) hm1 (Env.wf_nil _) rfl (after_eq run_b0 ▸ keeps_b0)
      x0 := Match.reg_eq (r := .X0) (match_nil m0) hm1 rfl rfl
      x1 := Match.reg_eq (r := .X1) (match_nil m0) hm1 rfl rfl
      x2 := Match.reg_eq (r := .X2) (match_nil m0) hm1 rfl rfl
      x3 := Match.reg_eq (r := .X3) (match_nil m0) hm1 rfl rfl
      x30 := Match.reg_eq (r := .X30) (match_nil m0) hm1 rfl rfl }
  simp only [PcOk] at hpc1
  split at hpc1
  · rename_i hc
    exfalso
    sym_simp at hc
    simp only [Env.ofMachine_regs, Reg64s.getXReg, beq_iff_eq] at hc
    have : m0.regs.X2.toNat = 0 := by
      show m0.regs.X2.toBitVec.toNat = 0
      rw [hc]; rfl
    simp only [NativeVm.decodedWords, NativeVm.phaseBase] at hlen
    omega
  -- `b1`: `i` against the count.
  have hc0 : 0 < a.len := by simp only [NativeVm.decodedWords, NativeVm.phaseBase] at hlen; omega
  have hwfc : (Env.ofMachine st1.data [(a.words, 8)]).WF :=
    Env.wf_of ⟨⟨fun i hi ↦ by
      show (st1.data.dmem.get? (a.words + BitVec.ofNat 64 i)).isSome
      exact hK1.saved.2.2 _ (hrm i (by omega)), by
        show a.words.toNat + 8 ≤ 2 ^ 64; omega⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hmc : Match (Env.ofMachine st1.data [(a.words, 8)]) countS st1.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl ⟨known_ptr rfl (by
      show st1.data.regs.X1.toBitVec = _; rw [hK1.x1, hx1]), trivial⟩ trivial trivial trivial
  have hd1 : st1.data.dmem = m0.dmem := hK1.dmem
  have hcnt : (Env.ofMachine st1.data [(a.words, 8)]).load 0 0 8 = stream.size.toUInt64.toBitVec :=
    load_ofMachine (o := 0) rfl (by rw [hd1]; exact hdec.stream_count)
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwfc hpc1 hmc
    fun st2 hm2 hpc2 => ?_
  have hK2 : Kept m0 st2.data :=
    { dmem := (hm2.dmem_eq hwfc rfl).trans hd1
      saved := hK1.saved.trans (Match.saved hmc hm2 hwfc rfl (after_eq run_b1 ▸ keeps_b1))
      x0 := (Match.reg_eq (r := .X0) hmc hm2 rfl rfl).trans hK1.x0
      x1 := (Match.reg_eq (r := .X1) hmc hm2 rfl rfl).trans hK1.x1
      x2 := (Match.reg_eq (r := .X2) hmc hm2 rfl rfl).trans hK1.x2
      x3 := (Match.reg_eq (r := .X3) hmc hm2 rfl rfl).trans hK1.x3
      x30 := (Match.reg_eq (r := .X30) hmc hm2 rfl rfl).trans hK1.x30 }
  simp only [PcOk] at hpc2
  split at hpc2
  · rename_i hc
    refine finish_none (hpc2.trans (hp.label (j := NativeRustcVmArm.Vm.DecodedStreamElement.b3Offset) NativeRustcVmArm.Vm.DecodedStreamElement.label_3_at)) hp hon hom hK2 ?_
    sym_simp at hc
    rw [hcnt] at hc
    simp only [Env.ofMachine_regs, Bool.not_eq_true', BitVec.ult] at hc
    have hc := of_decide_eq_false hc
    rw [toBitVec_toUInt64' (by omega)] at hc
    have : (st1.data.regs.getXReg XReg.X3).toBitVec.toNat = m0.regs.X3.toNat := by
      show st1.data.regs.X3.toNat = _; rw [hK1.x3]
    omega
  -- `b2`: `2 i + 3` within the slice.
  rename_i hc
  have hi : m0.regs.X3.toNat < stream.size := by
    sym_simp at hc
    rw [hcnt] at hc
    simp only [Env.ofMachine_regs, Bool.not_eq_true', BitVec.ult, Bool.not_eq_false] at hc
    have hc := of_decide_eq_true hc
    rw [toBitVec_toUInt64' (by omega)] at hc
    have : (st1.data.regs.getXReg XReg.X3).toBitVec.toNat = m0.regs.X3.toNat := by
      show st1.data.regs.X3.toNat = _; rw [hK1.x3]
    omega
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 (Env.wf_nil _) hpc2
    (match_nil _) fun st3 hm3 hpc3 => ?_
  simp only [PcOk] at hpc3
  have hx3 : (st2.data.regs.getXReg .X3).toBitVec.toNat = m0.regs.X3.toNat := by
    show st2.data.regs.X3.toNat = _; rw [hK2.x3]
  have hx2' : (st2.data.regs.getXReg .X2).toBitVec.toNat = a.len := by
    show st2.data.regs.X2.toNat = _; rw [hK2.x2, hx2]
  split at hpc3
  swap
  · rename_i hc
    exfalso
    sym_simp at hc
    simp only [Env.ofMachine_regs] at hc
    simp only [ult_or_eq hx3 hx2' (by omega), unsigned_add4 hx3 (by omega)] at hc
    simp at hc
  -- `b4`: element `i` copied.
  have hK3 : Kept m0 st3.data :=
    { dmem := (hm3.dmem_eq (Env.wf_nil _) rfl).trans hK2.dmem
      saved := hK2.saved.trans (Match.saved (match_nil _) hm3 (Env.wf_nil _) rfl
        (after_eq run_b2 ▸ keeps_b2))
      x0 := (Match.reg_eq (r := .X0) (match_nil _) hm3 rfl rfl).trans hK2.x0
      x1 := (Match.reg_eq (r := .X1) (match_nil _) hm3 rfl rfl).trans hK2.x1
      x2 := (Match.reg_eq (r := .X2) (match_nil _) hm3 rfl rfl).trans hK2.x2
      x3 := (Match.reg_eq (r := .X3) (match_nil _) hm3 rfl rfl).trans hK2.x3
      x30 := (Match.reg_eq (r := .X30) (match_nil _) hm3 rfl rfl).trans hK2.x30 }
  have hx8 : (st3.data.regs.getXReg .X8).toBitVec.toNat = 2 * m0.regs.X3.toNat := by
    rw [hm3.regs .X8 _ rfl]
    sym_simp
    rw [evalUBFM_lsl1_toNat, Env.ofMachine_regs, hx3]
    omega
  set o := m0.regs.X0.toBitVec
  set e := a.word (1 + 2 * m0.regs.X3.toNat)
  have he : e.toNat = a.words.toNat + 8 * (1 + 2 * m0.regs.X3.toNat) := toNat_off (by omega)
  have hon' : o.toNat + 24 ≤ 2 ^ 64 := hon
  have hap' : o.toNat + 24 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ o.toNat := hap
  have hwf4 : (Env.ofMachine st3.data [(o, 24), (e, 16)]).WF := by
    refine Env.wf_of ⟨⟨fun j hj ↦ ?_, hon'⟩, ⟨fun j hj ↦ ?_, ?_⟩, trivial⟩ ?_
    · show (st3.data.dmem.get? (o + BitVec.ofNat 64 j)).isSome
      rw [hK3.dmem]; exact hom j hj
    · show (st3.data.dmem.get? (e + BitVec.ofNat 64 j)).isSome
      rw [hK3.dmem, off_add]; exact hrm _ (by omega)
    · show e.toNat + 16 ≤ 2 ^ 64
      omega
    · refine List.pairwise_pair.mpr ?_
      show o.toNat + 24 ≤ e.toNat ∨ e.toNat + 16 ≤ o.toNat
      omega
  have hm4 : Match (Env.ofMachine st3.data [(o, 24), (e, 16)]) someS st3.data := by
    refine match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
      ⟨known_ptr rfl (by show st3.data.regs.X0.toBitVec = _; rw [hK3.x0]), trivial⟩ trivial trivial
      ⟨?_, trivial⟩
    show _ = (Env.ofMachine st3.data [(o, 24), (e, 16)]).base 1 + BitVec.ofInt 64 (-8)
    rw [show (Env.ofMachine st3.data [(o, 24), (e, 16)]).base 1 = e from rfl]
    simp only [elemAddr, Sym.eval, BinOp.apply, UnOp.apply, low_W64, ext_W64, shiftW]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft, Env.ofMachine_regs,
      Env.ofMachine_regs, hx8, he]
    have : (st3.data.regs.getXReg .X1).toBitVec = a.words := by
      show st3.data.regs.X1.toBitVec = _; rw [hK3.x1, hx1]
    rw [this]
    simp only [BitVec.toNat_ofInt, MemWidth.bits]
    omega
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf4
    (hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.DecodedStreamElement.b4Offset) NativeRustcVmArm.Vm.DecodedStreamElement.label_4_at)) hm4
    fun st4 hm4' hpc4 => ?_
  obtain ⟨hw0, hw1, hw2, hws, hkeeps, h30⟩ := after_eq run_b4 ▸ some_b4
  have hx30 : st4.data.regs.X30 = m0.regs.X30 := (Match.reg_eq hm4 hm4' rfl h30).trans hK3.x30
  have hsame : SameOutside st3.data.dmem st4.data.dmem (InRange o 24) := fun q hq ↦
    hm4'.get?_mem0 hwf4 fun hW ↦ hq (by
      obtain ⟨j, hj, -, rfl⟩ := touch_of_written hwf4 rfl le_rfl hws hW
      exact inRange_off_self hj (by omega))
  have hel := hdec.stream _ hi
  rw [ewAt_iff] at hel
  have hl0 : (Env.ofMachine st3.data [(o, 24), (e, 16)]).load 1 0 8 = stream[m0.regs.X3.toNat].c0.toBitVec :=
    load_ofMachine (o := 0) rfl (by rw [hK3.dmem, off_zero]; exact hel.1)
  have hl1 : (Env.ofMachine st3.data [(o, 24), (e, 16)]).load 1 8 8 = stream[m0.regs.X3.toNat].c1.toBitVec :=
    load_ofMachine (o := 8) rfl (by rw [hK3.dmem]; exact hel.2)
  refine .done _ ⟨by simp only [PcOk] at hpc4; rw [hpc4]; simp only [retOf, hx30], ?_, ?_,
    hK3.saved.trans (Match.saved hm4 hm4' hwf4 rfl hkeeps)⟩
  · rw [Array.getElem?_eq_getElem hi]
    refine ⟨?_, ewAt_iff.mpr ⟨?_, ?_⟩⟩
    · have := wordAt_write hm4' (r := 0) (o := 0) rfl (by omega) fun j hj ↦ by
        rw [Nat.zero_add]; exact hw0 j hj
      rwa [off_zero] at this
    · have := wordAt_write hm4' (r := 0) (o := 8) rfl (by omega) hw1
      rwa [Sym.eval, hl0] at this
    · have := wordAt_write hm4' (r := 0) (o := 16) rfl (by omega) hw2
      rw [Sym.eval, hl1] at this
      rwa [off_off]
  · intro q hq
    rw [hsame q hq, hK3.dmem]

end

end NativeRustcVmArm.Transcript.StreamElement
