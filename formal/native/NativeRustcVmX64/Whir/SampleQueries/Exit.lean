module

public import NativeRustcVmX64.Whir.SampleQueries.InnerB

/-!
# `sample_queries` on x86-64: the inner loop's end

`exit_step`: after the chunk's last position (`AtB17`), `b17` jumps to `b8`, which restores the
outer loop's registers from the frame: `b9` next (`AtB9`).
-/

namespace NativeRustcVmX64.Whir.SampleQueries

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.SampleQueries
open NativeRustcVmX64.Transcript (Frame frameEnv)
open NativeRustcVm (BufWordsAt WordsAt WordAt)

public section

variable [Host] {k : Nat} {a : DecArea} {s0 : TState} {m0 : MachineData}

/-- **`b17`, `b8`**: on to `b9`. -/
theorem exit_step (hp : Placed code k) (h : SampleQueriesPre a s0 m0) {j r : Nat} {s : TState}
    {qs : List UInt64} {st : MachineData} (hB : AtB17 a s0 m0 j r s qs st) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b9Offset) ∧
      AtB9 a s0 m0 j r (nOf m0 r) (sq s).2 (qs ++ (chunk (dep m0) (sq s).1 (nOf m0 r)).toList)
        st'.data) ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b17Offset)⟩ := by
  have hcnt := pre_cnt h
  have hlen := hB.len
  have hnle : nOf m0 r ≤ r := Nat.min_le_right _ _
  have hwf := mid_wf (vars := fun _ ↦ 0) (ret := 0) h hB.ctx.fr.kept
  refine exec_then (inf hp b17_in_code (by simp [b17])) run_b17 hwf (by intro l h; cases h)
    (mid_match hB.ctx.fr) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hmem, hk⟩ := after_eq run_b17 ▸ ok_b17
  have hc1 := hB.ctx.block h hm1 (L := 0) (by omega) hmid (wr0_nil hmem 0) (kept_spec hk (by simp))
  have hd1 : st1.data.dmem = st.dmem := hm1.dmem_eq hwf hmem
  have hk1 : ∀ r', r' ∈ [Reg64.rax, .rbx, .rcx, .r12, .r13, .r14, .r15, .rbp] →
      reg st1.data r' = reg st r' := fun r' hr ↦ reg_kept hm1 (kept_spec hk hr)
  simp only [PcOk] at hpc1
  have hwf1 := mid_wf (vars := fun _ ↦ 0) (ret := 0) h hc1.fr.kept
  refine exec_at (inf hp b8_in_code (by simp [b8])) run_b8 hwf1 (by intro l h; cases h)
    (hpc1.trans (hp.label NativeRustcVmX64.Vm.SampleQueries.label_9_at)) (mid_match hc1.fr) fun st2 hm2 hpc2 ↦
      .done _ ⟨hpc2.trans rfl, ?_⟩
  obtain ⟨hmid2, hmem2, hbp, hbx, h15, h12, hax, hk2⟩ := after_eq run_b8 ▸ ok_b8
  have hc2 := hc1.block h hm2 (L := 0) (by omega) hmid2 (wr0_nil hmem2 0) (kept_spec hk2 (by simp))
  have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq hwf1 hmem2
  have hk2' : ∀ r', r' ∈ [Reg64.rcx, .r13, .r14] → reg st2.data r' = reg st1.data r' :=
    fun r' hr ↦ reg_kept hm2 (kept_spec hk2 hr)
  have hdd : st2.data.dmem = st.dmem := hd2.trans hd1
  refine ⟨hc2, hdd ▸ hB.tw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hB.jlt, hnle, ?_, by have := hB.dle; omega,
    hdd ▸ hB.ts, hdd ▸ hB.buf, auxP_next hB.model hB.jlt hB.r0⟩
  · rw [show reg st2.data .rax = _ from hm2.regs .rax _ hax]
    show ((frameEnv m0 st1.data 128 []).load 0 16 8).toNat = r
    rw [loc_load (hd1 ▸ hB.l16)]
    simp; omega
  · rw [hk2' .rcx (by simp), hk1 .rcx (by simp)]; exact hB.rcx
  · rw [show reg st2.data .rbx = _ from hm2.regs .rbx _ hbx]
    show (frameEnv m0 st1.data 128 []).load 0 24 8 = _
    rw [loc_load (hd1 ▸ hB.tw), UInt64.toBitVec_ofBitVec]
  · rw [show reg st2.data .r15 = _ from hm2.regs .r15 _ h15]
    show ((frameEnv m0 st1.data 128 []).load 0 32 8).toNat = j
    rw [loc_load (hd1 ▸ hB.l32)]
    have := hB.jlt
    simp; omega
  · rw [hk2' .r14 (by simp), hk1 .r14 (by simp)]; exact hB.r14
  · rw [show reg st2.data .r12 = _ from hm2.regs .r12 _ h12]
    rfl
  · rw [show reg st2.data .rbp = _ from hm2.regs .rbp _ hbp]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    show (reg st1.data .rbp - BitVec.ofNat 64 1).toNat = _
    rw [hk1 .rbp (by simp), toNat_sub1 hB.rbp (by omega)]
    simp [chunk_size]
  · simp [chunk_size]; omega

end

end NativeRustcVmX64.Whir.SampleQueries
