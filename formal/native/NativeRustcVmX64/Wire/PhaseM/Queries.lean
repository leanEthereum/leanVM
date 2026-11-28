module

public import NativeRustcVmX64.Wire.PhaseM.First
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names

/-!
# `phase_m`: the queries (x86-64)

`qloop`: from the queries' loop (`AtQ`), each query read by `Reader::le` (`b4`), its tag (`b5`)
and stored at the working area's byte `8 i` (`b6`), to the height's read (`At7`) or to `None`.
-/

namespace NativeRustcVmX64.Wire.PhaseM

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Vm.PhaseM
open NativeRustcVmX64.Transcript (Frame frameEnv after after_eq MidOk wordAt_write load_ofMachine)
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off)
open NativeRustcVmX64.Wire.Decode (eqv_eval)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} [Host] {k : Nat}

/-- **A query**: from the loop's head, query `i` read and stored; to the next head, to the
height's read, or to `None`. -/
theorem q_step (hp : Placed code k) (G : Geo m0 bp B.length)
    (hle : Spec (Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    (hR0 : ReaderAt m0.dmem (RD m0) bp B c) {count i : Nat} {st : MachineState}
    (h : AtQ m0 bp B c k count i st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨ AtQ m0 bp B c k count (i + 1) st' ∨
      ∃ qs c2, At7 m0 bp B c k count qs c2 st') st := by
  obtain ⟨hpc, hbod, h1, hcnt, hi, hf40, h13, h15, qs, hqs, hqW, hrd⟩ := h
  have hsp := G.sp
  have htop := G.top
  have hwn := G.wNw
  have hsW := G.sW
  have hrW := G.rW
  have hbW := G.bW
  have hrn := G.rNw
  have hsR := G.sR
  have hsB := G.sB
  have hlen := (rdU32s_len B i (c + 4) hqs).1
  -- `b4`: `Reader::le`.
  obtain ⟨hmid4, hw4, hsi4, hdi4, hk4⟩ := ok_b4
  refine le4 hp G hle b4_in_code (by simp [b4]) exit_b4 hmid4 hw4 hsi4 hdi4 (hk4 .r12 (by simp))
    (hk4 .r14 (by simp)) hpc hbod hrd fun s1 m2 hb2 hm1 hcs2 hs2 hr2 ↦ ?_
  have rk2 : ∀ x ∈ [Reg64.r13, .r15], reg m2 x = reg st.data x := fun x hx ↦ by
    have hc : calleeSaved x = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> rfl
    exact (hcs2 x hc).trans (hm1.regs x _ (hk4 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl <;> simp)))
  -- `b5`: the tag.
  obtain ⟨hok5, hk5⟩ := ok_b5
  refine fblk hp G b5_in_code (by simp [b5]) exit_b5 nofun hok5 (hk5 .r12 (by simp))
    (hk5 .r14 (by simp)) (st := ⟨m2, _⟩) (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b4_next) hb2
    fun s3 hb3 hd3 hm3 hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  have ea : (frameEnv m0 m2 160 []).regs .rax = reg m2 .rax := rfl
  rcases read4_cases hr2 with ⟨hn, h0⟩ | ⟨v, hv, h0, hdx, hvl, hR4⟩
  · -- No query: `None`.
    rw [and1_eval _ (by rw [ea]; exact .inl h0), ea, h0] at hpc3
    simp only [decide_true, ↓reduceIte] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.PhaseM.label_23_at] at hpc3
    refine Eventually.mono (none_run hp G hR0 hpc3 hb3 ?_) fun _ h ↦ .inl h
    rw [phaseM_eq, h1]
    simp only [show ¬ wireMaxQueries < count by unfold wireMaxQueries; omega, ↓reduceIte]
    rw [show count = i + 1 + (count - i - 1) by omega, rdU32s_none B i (c + 4) _ hqs hn]
  rw [and1_eval _ (by rw [ea]; exact .inr h0), ea, h0] at hpc3
  simp only [show ¬ ((1 : BitVec 64) = 0) by decide, decide_false, Bool.false_eq_true,
    ↓reduceIte] at hpc3
  have rk3 : ∀ x ∈ [Reg64.rdx, .r13, .r15], reg s3.data x = reg m2 x := fun x hx ↦
    hm3.regs x _ (hk5 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp))
  -- `b6`: the store.
  have hon : 8 * i + 8 ≤ 483584 := by omega
  have hwa : (wa m0 (8 * i)).toNat = (WK m0).toNat + 8 * i := G.wa (by omega)
  have h15' : reg s3.data .r15 = BitVec.ofNat 64 (8 * i) := by
    apply BitVec.eq_of_toNat_eq
    rw [rk3 .r15 (by simp), rk2 .r15 (by simp), h15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hm6 : Match (aEnv m0 s3.data (8 * i) 8 (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b6Offset + b6.length)).toBitVec) qS
      s3.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb3.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨by
        show BinOp.apply .add .W64 (reg s3.data .r14) (reg s3.data .r15) =
          wa m0 (8 * i) + BitVec.ofInt 64 0
        rw [NativeRustcVmX64.Transcript.ofInt_zero64, BitVec.add_zero, hb3.r14, h15']
        simp [BinOp.apply], trivial⟩
  obtain ⟨hmid6, hmem6, hww6, h15_6, hk6⟩ := ok_b6
  refine ablk hp G b6_in_code (by simp [b6]) exit_b6 hon (by omega) hmid6
    (fun w hw ↦ by rw [hmem6] at hw; simp only [List.mem_singleton] at hw; subst hw; decide)
    (hk6 .r12 (by simp)) (hk6 .r14 (by simp)) (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b5_next))
    hb3 hm6 fun s4 hb4 hs4 hkeep4 hsw4 hm4 hpc4 ↦ ?_
  have hR3 : ReaderAt s3.data.dmem (RD m0) bp B (c + 4 + 4 * i + 4) := by rw [hd3]; exact hR4
  have hR4' : ReaderAt s4.data.dmem (RD m0) bp B (c + 4 + 4 * (i + 1)) := by
    rw [show c + 4 + 4 * (i + 1) = c + 4 + 4 * i + 4 by omega]
    exact reader_keep hR3 hs4 (fun q hq ↦ by rcases hq with hq | hq <;> omega)
      (fun q hq ↦ by rcases hq with hq | hq <;> omega)
  have hqs' : rdU32s B (i + 1) (c + 4) = some (qs ++ [v], c + 4 + 4 * (i + 1)) := by
    rw [show c + 4 + 4 * (i + 1) = c + 4 + 4 * i + 4 by omega]
    exact rdU32s_snoc B i (c + 4) hqs hv
  have hqW2 : NativeRustcVm.WordsAt m2.dmem (wa m0 0) (qs.map Nat.toUInt64) := by
    refine wordsAt_keep hqW hs2 (by rw [List.length_map, G.wa (by omega)]; omega) fun q hq ↦ ?_
    rw [List.length_map, G.wa (by omega)]
    omega
  have hqW4 : NativeRustcVm.WordsAt s4.data.dmem (wa m0 0) ((qs ++ [v]).map Nat.toUInt64) := by
    rw [List.map_append]
    refine wordsAt_snoc ?_ ?_
    · refine wordsAt_keep (by rw [hd3]; exact hqW2) hs4
        (by rw [List.length_map, G.wa (by omega)]; omega) fun q hq ↦ ?_
      rw [List.length_map, G.wa (by omega)]
      omega
    · have := wordAt_write hm4 (r := 1) (o := 0) (b := wa m0 (8 * i)) (sz := 8) rfl (by omega) hww6
      simp only [Sym.eval, Env.ofMachine_regs, off_zero] at this
      rw [show s3.data.regs.get64 .rdx = reg s3.data .rdx from rfl, rk3 .rdx (by simp),
        toNat_reg_eq hdx] at this
      simp only [List.length_map, hlen, off_off, Nat.zero_add]
      exact this
  have hs4' := hs4
  rw [hd3] at hs4'
  have hf40' : FW m0 s4.data.dmem 40 count.toUInt64 := by
    refine hkeep4 40 _ (by omega) (fun w hw hr ↦ by
      rw [hmem6] at hw; simp only [List.mem_singleton] at hw; subst hw; simp at hr) ?_
    rw [hd3]
    exact hf40.keep G (by omega) hs2 fun q hq ↦ by rcases hq with hq | hq <;> omega
  have e13 : reg s4.data .r13 = reg s3.data .r13 := hm4.regs .r13 _ (hk6 .r13 (by simp))
  have h13' : (reg s4.data .r13).toNat = 8 * count := by
    rw [e13, rk3 .r13 (by simp), rk2 .r13 (by simp)]; exact h13
  have h15'' : (reg s4.data .r15).toNat = 8 * (i + 1) := by
    have e15 : reg s4.data .r15 = BinOp.apply .add .W64 (BitVec.ofNat 64 8) (reg s3.data .r15) :=
      hm4.regs .r15 _ h15_6
    rw [e15]
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, h15', BitVec.toNat_ofNat]
    omega
  simp only [PcOk] at hpc4
  have hc : (SBool.cmp .eq .W64 (.reg .r13) (.bin .add .W64 (.lit 8) (.reg .r15))).not.eval
      (aEnv m0 s3.data (8 * i) 8 (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b6Offset + b6.length)).toBitVec) =
      !decide (count = i + 1) := by
    show (!CmpOp.apply .eq .W64 (reg s3.data .r13)
      (BinOp.apply .add .W64 (BitVec.ofNat 64 8) (reg s3.data .r15))) = _
    rw [eqv_eval, rk3 .r13 (by simp), rk2 .r13 (by simp), h13]
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, h15', BitVec.toNat_ofNat]
    congr 1
    exact decide_eq_decide.mpr (by omega)
  rw [hc] at hpc4
  by_cases hlast : count = i + 1
  · simp only [hlast, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc4
    refine .done _ (.inr (.inr ⟨qs ++ [v], c + 4 + 4 * (i + 1), ⟨hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b6_next), hb4, h1, hcnt, by rw [hlast]; exact hqs', hf40', h13',
      hqW4, hR4'⟩⟩))
  simp only [hlast, decide_false, Bool.not_false, ↓reduceIte] at hpc4
  exact .done _ (.inr (.inl ⟨hpc4.trans (hp.label NativeRustcVmX64.Vm.PhaseM.label_3_at), hb4, h1, hcnt, by omega,
    hf40', h13', h15'', qs ++ [v], hqs', hqW4, hR4'⟩))

/-- **The queries' loop.** -/
theorem qloop (hp : Placed code k) (G : Geo m0 bp B.length)
    (hle : Spec (Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    (hR0 : ReaderAt m0.dmem (RD m0) bp B c) {count i : Nat} {st : MachineState}
    (h : AtQ m0 bp B c k count i st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      ∃ qs c2, At7 m0 bp B c k count qs c2 st') st :=
  Sym.loop (tr := step1 Host.exe) (fun n st ↦ ∃ i, n = count - i ∧ AtQ m0 bp B c k count i st)
    (fun _ st ⟨i, hn, h⟩ ↦ Eventually.mono (q_step hp G hle hR0 h) fun _ h' ↦ by
      rcases h' with h' | h' | h'
      · exact .inl (.inl h')
      · exact .inr ⟨count - (i + 1), by have := h.ilt; omega, i + 1, rfl, h'⟩
      · exact .inl (.inr h'))
    ⟨i, rfl, h⟩

end

end NativeRustcVmX64.Wire.PhaseM
