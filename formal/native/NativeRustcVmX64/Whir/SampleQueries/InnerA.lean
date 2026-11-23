module

public import NativeRustcVmX64.Whir.SampleQueries.Mid
public import NativeRustcVmX64.Code.Vm.QueryBits.Names

/-!
# `sample_queries` on x86-64: the inner loop's head and `query_bits`

`inner_call`: from the inner loop's head (`Inner` at `i`), `b14`'s test (the buffer never full:
`len + i < 230`) and `b15`'s call of `query_bits` give position `i` of the chunk in RAX
(`AtB16`).
-/

namespace NativeRustcVmX64.Whir.SampleQueries

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.SampleQueries
open NativeRustcVmX64.Transcript (Frame frameEnv)
open NativeRustcVmX64.Arrays (pc_cond)
open NativeRustcVm (BufWordsAt WordsAt WordAt)

@[expose] public section

/-- **At `b16`**: position `i` of the chunk in RAX, the chunk's size in RBX. -/
structure AtB16 [Labels] (a : DecArea) (s0 : TState) (m0 : MachineData) (j r : Nat) (s : TState)
    (qs : List UInt64) (i : Nat) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  tw : WordAt st.dmem (off (fb m0) 24) (UInt64.ofBitVec (tA m0))
  l16 : WordAt st.dmem (off (fb m0) 16) r.toUInt64
  l32 : WordAt st.dmem (off (fb m0) 32) j.toUInt64
  l40 : WordAt st.dmem (off (fb m0) 40) (8 * nOf m0 r).toUInt64
  l48 : WordAt st.dmem (off (fb m0) 48)
    (UInt64.ofBitVec (BitVec.ofNat 64 (8 * qs.length) - BitVec.ofNat 64 1840))
  l56 : WordAt st.dmem (off (fb m0) 56) (sq s).1.c1
  l64 : WordAt st.dmem (off (fb m0) 64) (sq s).1.c0
  rax : reg st .rax = (queryBits (sq s).1 (i * dep m0) (dep m0)).toBitVec
  rbx : (reg st .rbx).toNat = nOf m0 r
  r12 : reg st .r12 = 0#64 - BitVec.ofNat 64 (8 * i)
  r14 : (reg st .r14).toNat = cnt m0
  r15 : reg st .r15 = BitVec.ofNat 64 (i * dep m0)
  rbp : (reg st .rbp).toNat = qs.length + i + 1
  jlt : j < cnt m0
  len : qs.length + r = cnt m0
  r0 : r ≠ 0
  dpos : 0 < dep m0
  dle : dep m0 ≤ 128
  ilt : i < nOf m0 r
  ts : TStateAt st.dmem (tA m0) a (sq s).2
  buf : BufWordsAt st.dmem (oA m0) queryCap (qs ++ (chunk (dep m0) (sq s).1 (nOf m0 r)).toList.take i)
  model : auxP (dep m0) (cnt m0) (cnt m0) s0 =
    (qs.toArray ++ (auxP (dep m0) (cnt m0 - j) r s).1, (auxP (dep m0) (cnt m0 - j) r s).2)

end

public section

/-- `b14`'s test: the buffer is not full. -/
theorem full_false {len i : Nat} (h : len + i < 230) :
    (BitVec.ofNat 64 (8 * len) - BitVec.ofNat 64 1840 == 0#64 - BitVec.ofNat 64 (8 * i)) = false := by
  rw [beq_eq_false_iff_ne]
  intro he
  have := congrArg BitVec.toNat he
  rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat] at this
  simp only [BitVec.toNat_zero] at this
  omega

variable [Host] {k : Nat} {a : DecArea} {s0 : TState} {m0 : MachineData}

/-- **`b14`, `b15` and `query_bits`**: position `i` of the chunk. -/
theorem inner_call (hp : Placed code k) (h : SampleQueriesPre a s0 m0)
    (hqb : Spec (Labels.label NativeRustcVmX64.Vm.QueryBits.entryLabel) QueryBitsPre QueryBitsPost) {j r : Nat} {s : TState}
    {qs : List UInt64} {i : Nat} {st : MachineData} (hI : Inner a s0 m0 j r s qs i st) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b16Offset) ∧
      AtB16 a s0 m0 j r s qs i st'.data) ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b14Offset)⟩ := by
  have hcnt := pre_cnt h
  have hlen := hI.len
  have hilt := hI.ilt
  have hnle : nOf m0 r ≤ r := Nat.min_le_right _ _
  have hdle := hI.dle
  have hwf := mid_wf (vars := fun _ ↦ 0) (ret := 0) h hI.ctx.fr.kept
  refine exec_then (inf hp b14_in_code (by simp [b14])) run_b14 hwf (by intro l h; cases h)
    (mid_match hI.ctx.fr) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hmem, hk⟩ := after_eq run_b14 ▸ ok_b14
  have hc1 := hI.ctx.block h hm1 (L := 0) (by omega) hmid (wr0_nil hmem 0) (kept_spec hk (by simp))
  have hd1 : st1.data.dmem = st.dmem := hm1.dmem_eq hwf hmem
  have hk1 : ∀ r', r' ∈ [Reg64.rcx, .r12, .r13, .r14, .r15, .rbp] → reg st1.data r' = reg st r' :=
    fun r' hr ↦ reg_kept hm1 (kept_spec hk hr)
  simp only [PcOk] at hpc1
  have hc : (SBool.cmp .eq .W64 (.load 0 48 8) (.reg .r12)).eval (frameEnv m0 st 128 []) = false := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64]
    rw [loc_load hI.l48, UInt64.toBitVec_ofBitVec]
    show (_ == reg st .r12) = false
    rw [hI.r12]
    exact full_false (by omega)
  rw [hc] at hpc1
  have hpc := (pc_cond hpc1).2 (by simp)
  -- `b15`: `query_bits`' arguments, the call.
  have hwf1 := mid_wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b15Offset + b15.length)).toBitVec) h
    hc1.fr.kept
  refine exec_at (inf hp b15_in_code (by simp [b15])) run_b15 hwf1 (fun _ _ ↦ rfl) (hpc.trans rfl)
    (mid_match hc1.fr) fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hw2, hdi, hsi, hdx, hbx, hcx, hk2⟩ := after_eq run_b15 ▸ ok_b15
  have hs2 := block_same hwf1 hm2 (by omega) hw2
  have hin2 := midOk_writesIn hmid2
  have hrdi : reg st2.data .rdi = (sq s).1.c0.toBitVec := by
    rw [show reg st2.data .rdi = _ from hm2.regs .rdi _ hdi]
    exact loc_load (hd1 ▸ hI.l64)
  have hrsi : reg st2.data .rsi = (sq s).1.c1.toBitVec := by
    rw [show reg st2.data .rsi = _ from hm2.regs .rsi _ hsi]
    exact loc_load (hd1 ▸ hI.l56)
  have hrdx : (reg st2.data .rdx).toNat = i * dep m0 := by
    rw [show reg st2.data .rdx = _ from hm2.regs .rdx _ hdx]
    show (reg st1.data .r15).toNat = _
    rw [hk1 .r15 (by simp), hI.r15, BitVec.toNat_ofNat]
    have h128 : 128 / dep m0 ≤ 128 := Nat.div_le_self _ _
    have hi128 : i ≤ 128 := by simp only [nOf] at hilt; omega
    have : i * dep m0 ≤ 128 * 128 := Nat.mul_le_mul hi128 hdle
    omega
  have hrcx : (reg st2.data .rcx).toNat = dep m0 := by
    rw [show reg st2.data .rcx = _ from hm2.regs .rcx _ hcx]
    show (reg st1.data .r13).toNat = _
    rw [hc1.r13]
  have hw : ∀ {o w}, 16 ≤ o → o + 8 ≤ 136 → WordAt st.dmem (off (fb m0) o) w →
      WordAt st2.data.dmem (off (fb m0) o) w := fun ho hle hw ↦
    loc_keep hwf1 hm2 hin2 hle (miss_of_wr0 hw2 (by omega)) (hd1 ▸ hw)
  refine qb_call h hqb hc1 hm2 hmid2 hw2 (kept_spec hk2 (by simp)) hpc2
    fun st3 hpc3 hc3 hax3 hcs3 hd3 ↦ .done _ ⟨hpc3.trans rfl, ?_⟩
  have hreg : ∀ r', r' ∈ [Reg64.r12, .r14, .r15, .rbp] → calleeSaved r' = true →
      reg st3.data r' = reg st r' := fun r' hr hcs ↦
    (hcs3 r' hcs).trans ((reg_kept hm2 (kept_spec hk2 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp))).trans (hk1 r' (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp)))
  have hs02 : SameOutside st.dmem st2.data.dmem (InRange (fb m0) 8) := hd1 ▸ hs2
  refine ⟨hc3, hd3 ▸ hw (by omega) (by omega) hI.tw, hd3 ▸ hw (by omega) (by omega) hI.l16,
    hd3 ▸ hw (by omega) (by omega) hI.l32, hd3 ▸ hw (by omega) (by omega) hI.l40,
    hd3 ▸ hw (by omega) (by omega) hI.l48, hd3 ▸ hw (by omega) (by omega) hI.l56,
    hd3 ▸ hw (by omega) (by omega) hI.l64, ?_, ?_, (hreg .r12 (by simp) rfl).trans hI.r12,
    (congrArg BitVec.toNat (hreg .r14 (by simp) rfl)).trans hI.r14,
    (hreg .r15 (by simp) rfl).trans hI.r15,
    (congrArg BitVec.toNat (hreg .rbp (by simp) rfl)).trans hI.rbp, hI.jlt, hlen, hI.r0, hI.dpos,
    hdle, hilt, ?_, ?_, hI.model⟩
  · rw [hax3, hrdx, hrcx]
    congr 2
    rw [hrdi, hrsi]
    rfl
  · rw [hcs3 .rbx rfl, show reg st2.data .rbx = _ from hm2.regs .rbx _ hbx]
    show (reg st1.data .rcx).toNat = _
    rw [hk1 .rcx (by simp), hI.rcx]
  · rw [hd3]
    exact TStateAt.block h (hm2.kept hwf1) (L := 8) (by omega) hs2 (hd1 ▸ hI.ts)
  · rw [hd3]
    exact buf_keep h hI.buf hs02 fun q hq ↦ frame_not_o h (Transcript.inRange_mono hq (by omega))

end

end NativeRustcVmX64.Whir.SampleQueries
