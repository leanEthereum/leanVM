module

public import NativeRustcVmX64.Whir.SampleQueries.Steps
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names

/-!
# `sample_queries` on x86-64: the outer loop's head

`outer_step` (`NativeRustcVmX64.Vm.SampleQueries.label_3`, `b10`): no position left returns (`fin`); else `b11` squeezes
the challenge (`AtB12`), `b12` reads `PER_CHALLENGE[depth]`, the chunk's size `n` (a depth `0`
asks for none: `AtB9`), `b13` starts the inner loop (`Inner` at `0`).
-/

namespace NativeRustcVmX64.Whir.SampleQueries

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.SampleQueries
open NativeRustcVmX64.Transcript (Frame frameEnv)
open NativeRustcVmX64.Arrays (pc_cond)
open NativeRustcVm (BufWordsAt WordsAt WordAt)

@[expose] public section

/-- **At `b12`**: the `j`th challenge `(sq s).1` in RAX, RDX, `r` positions left in the frame's
word `16`. -/
structure AtB12 [Labels] (a : DecArea) (s0 : TState) (m0 : MachineData) (j r : Nat) (s : TState)
    (qs : List UInt64) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  tw : WordAt st.dmem (off (fb m0) 24) (UInt64.ofBitVec (tA m0))
  l16 : WordAt st.dmem (off (fb m0) 16) r.toUInt64
  rax : reg st .rax = (sq s).1.c0.toBitVec
  rdx : reg st .rdx = (sq s).1.c1.toBitVec
  rbx : reg st .rbx = tA m0
  r15 : (reg st .r15).toNat = j
  r14 : (reg st .r14).toNat = cnt m0
  r12 : reg st .r12 = rodataAddr .perChallenge
  rbp : (reg st .rbp).toNat = qs.length
  jlt : j < cnt m0
  len : qs.length + r = cnt m0
  dlt : dep m0 < 129
  r0 : r ≠ 0
  ts : TStateAt st.dmem (tA m0) a (sq s).2
  buf : BufWordsAt st.dmem (oA m0) queryCap qs
  model : auxP (dep m0) (cnt m0) (cnt m0) s0 =
    (qs.toArray ++ (auxP (dep m0) (cnt m0 - j) r s).1, (auxP (dep m0) (cnt m0 - j) r s).2)

/-- **At `b13`**: the challenge in the frame's words `64`, `56`, the chunk's size `n` in RCX. -/
structure AtB13 [Labels] (a : DecArea) (s0 : TState) (m0 : MachineData) (j r : Nat) (s : TState)
    (qs : List UInt64) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  tw : WordAt st.dmem (off (fb m0) 24) (UInt64.ofBitVec (tA m0))
  l16 : WordAt st.dmem (off (fb m0) 16) r.toUInt64
  l56 : WordAt st.dmem (off (fb m0) 56) (sq s).1.c1
  l64 : WordAt st.dmem (off (fb m0) 64) (sq s).1.c0
  rcx : (reg st .rcx).toNat = nOf m0 r
  r15 : (reg st .r15).toNat = j
  r14 : (reg st .r14).toNat = cnt m0
  rbp : (reg st .rbp).toNat = qs.length
  jlt : j < cnt m0
  len : qs.length + r = cnt m0
  dlt : dep m0 < 129
  r0 : r ≠ 0
  dpos : 0 < dep m0
  ts : TStateAt st.dmem (tA m0) a (sq s).2
  buf : BufWordsAt st.dmem (oA m0) queryCap qs
  model : auxP (dep m0) (cnt m0) (cnt m0) s0 =
    (qs.toArray ++ (auxP (dep m0) (cnt m0 - j) r s).1, (auxP (dep m0) (cnt m0 - j) r s).2)

end

public section

theorem ofBitVec_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) : UInt64.ofBitVec x = n.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [← h]
  simp

theorem ofBitVec_ofNat (n : Nat) : UInt64.ofBitVec (BitVec.ofNat 64 n) = n.toUInt64 := rfl

/-- `b13`'s word `48`: `8 len - 1840`. -/
theorem f48_eval [Labels] (env : Env) {n : Nat} (h : (env.regs .rbp).toNat = n) (hn : n ≤ 230) :
    f48S.eval env = BitVec.ofNat 64 (8 * n) - BitVec.ofNat 64 1840 := by
  have hm : m23S.eval env = BitVec.ofNat 64 n := by
    simp only [m23S, Sym.eval, SBool.eval, CmpOp.apply, UnOp.apply, low_W64]
    apply BitVec.eq_of_toNat_eq
    split <;> rename_i hc
    · simp only [toNat_ext, toNat_low, Width.bits]
      rw [h, BitVec.toNat_ofNat]; omega
    · simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq, h] at hc
      simp only [toNat_ext, toNat_low, BitVec.toNat_ofNat, Width.bits] at hc ⊢
      omega
  simp only [f48S, Sym.eval, BinOp.apply, low_W64, ext_W64, hm]
  change BitVec.ofNat 64 n * BitVec.ofNat 64 8 + BitVec.ofNat 64 18446744073709549776 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm n 8,
    show BitVec.ofNat 64 18446744073709549776 = -BitVec.ofNat 64 1840 by decide,
    BitVec.sub_eq_add_neg]

/-- `b13`'s word `40`: `8 n` for `n ≥ 1`. -/
theorem f40_eval [Labels] (env : Env) {n : Nat} (h : (env.regs .rcx).toNat = n) (h1 : 1 ≤ n)
    (hn : n < 2 ^ 32) : f40S.eval env = BitVec.ofNat 64 (8 * n) := by
  simp only [f40S, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
  have hu : (env.regs .rcx).ult (BitVec.ofNat 64 1) = false := by
    simp [BitVec.ult, h]; omega
  rw [hu]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hc : shiftCount .W64 (BitVec.ofNat 64 3) = 3 := rfl
  rw [hc]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, h, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  simp only [Width.bits]
  omega

section
variable [Labels] {a : DecArea} {s0 : TState} {m0 : MachineData}

/-- `PER_CHALLENGE` at its label in a context's state. -/
theorem per_at (h : SampleQueriesPre a s0 m0) {st : MachineData} (hc : Ctx m0 st) :
    NativeRustcVm.BytesAt st.dmem (rodataAddr .perChallenge)
      NativeRustcVm.Data.Item.perChallenge.bytes := by
  obtain ⟨hb, hnw, hap⟩ := pre_ro h .perChallenge
  refine NativeRustcVm.BytesAt.of_sameOutside hb hc.same fun i hi hq ↦ ?_
  have hin : InRange (rodataAddr .perChallenge) NativeRustcVm.Data.Item.perChallenge.bytes.length
      (rodataAddr .perChallenge + BitVec.ofNat 64 i) :=
    inRange_off_self hi (by unfold NativeRustcVm.NoWrap at hnw; omega)
  rcases hq with hq | hq | hq
  · exact not_inRange_of_apart (Transcript.Apart.symm' (pre_oro h .perChallenge)) hnw
      (pre_out h).2.1 hin hq
  · exact not_inRange_of_apart (Transcript.Apart.symm' (h.1.2.2.2.2 .perChallenge)) hnw
      (pre_ts h).footprint.1.2 hin hq
  · exact not_inRange_of_apart hap hnw (noWrap_stackBelow (pre_S h)) hin
      (Transcript.inRange_mono hq (by omega))

end

variable [Host] {k : Nat} {a : DecArea} {s0 : TState} {m0 : MachineData}

/-- **`b10`, `b11` and the squeeze**: no position left returns; else the challenge squeezed. -/
theorem outer_step (hp : Placed code k) (h : SampleQueriesPre a s0 m0)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {j r : Nat} {s : TState} {qs : List UInt64} {st : MachineData}
    (hO : Outer a s0 m0 j r s qs st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post a s0 m0 st' ∨ (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b12Offset) ∧
      AtB12 a s0 m0 j r s qs st'.data)) ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b10Offset)⟩ := by
  have hcnt := pre_cnt h
  have hwf := mid_wf (vars := fun _ ↦ 0) (ret := 0) h hO.ctx.fr.kept
  refine exec_then (inf hp b10_in_code (by simp [b10])) run_b10 hwf (by intro l h; cases h)
    (mid_match hO.ctx.fr) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hmem, hk⟩ := after_eq run_b10 ▸ ok_b10
  have hc1 := hO.ctx.block h hm1 (L := 0) (by omega) hmid (wr0_nil hmem 0) (kept_spec hk (by simp))
  have hd1 : st1.data.dmem = st.dmem := hm1.dmem_eq hwf hmem
  have hk1 : ∀ r', r' ∈ [Reg64.rax, .rbx, .r12, .r13, .r14, .r15, .rbp] →
      reg st1.data r' = reg st r' := fun r' hr ↦ reg_kept hm1 (kept_spec hk hr)
  simp only [PcOk] at hpc1
  have hc : (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .rax) (.reg .rax)) (.lit 0)).eval
      (frameEnv m0 st 128 []) = decide (r = 0) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, BitVec.and_self]
    rw [beq_of_toNat]
    show decide ((reg st .rax).toNat = (BitVec.ofNat 64 0).toNat) = _
    rw [hO.rax]
    simp
  rw [hc] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases hr0 : r = 0
  · have hpc := (hT (decide_eq_true hr0)).trans (hp.label NativeRustcVmX64.Vm.SampleQueries.label_12_at)
    refine Eventually.mono (at_pc (fin hp h (qs := qs) (s' := s)
      ⟨hc1, hd1 ▸ hO.ts, hd1 ▸ hO.buf, ?_⟩) rfl hpc) fun _ h ↦ .inl h
    rw [hO.model, hr0, auxP_zero_right]
    simp
  have hpc := hF fun h ↦ hr0 (of_decide_eq_true h)
  -- `b11`: `r` saved, the squeeze.
  have hwf1 := mid_wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b11Offset + b11.length)).toBitVec) h
    hc1.fr.kept
  refine exec_at (inf hp b11_in_code (by simp [b11])) run_b11 hwf1 (fun _ _ ↦ rfl) (hpc.trans rfl)
    (mid_match hc1.fr) fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hw2, h16, hdi, hk2⟩ := after_eq run_b11 ▸ ok_b11
  have hk2' : ∀ r', r' ∈ [Reg64.rbx, .r12, .r13, .r14, .r15, .rbp] →
      reg st2.data r' = reg st1.data r' := fun r' hr ↦ reg_kept hm2 (kept_spec hk2 hr)
  have hs2 := block_same hwf1 hm2 (by omega) hw2
  have hl16 : WordAt st2.data.dmem (off (fb m0) 16) r.toUInt64 := by
    have := loc_write hm2 (by omega) h16
    rwa [show (Sym.reg .rax).eval (frameEnv m0 st1.data 128 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b11Offset + b11.length)).toBitVec) = reg st1.data .rax from rfl,
      ofBitVec_eq ((congrArg BitVec.toNat (hk1 .rax (by simp))).trans hO.rax)] at this
  have htw2 : WordAt st2.data.dmem (off (fb m0) 24) (UInt64.ofBitVec (tA m0)) :=
    loc_keep hwf1 hm2 (midOk_writesIn hmid2) (by omega) (miss_of_wr0 hw2 le_rfl) (hd1 ▸ hO.tw)
  have hbuf2 : BufWordsAt st2.data.dmem (oA m0) queryCap qs :=
    buf_keep h (hd1 ▸ hO.buf) hs2 fun q hq ↦ frame_not_o h (Transcript.inRange_mono hq (by omega))
  refine squeeze_call h hsq hc1 (hd1 ▸ hO.ts) hm2 hmid2 (by omega) hw2 (kept_spec hk2 (by simp))
    ((hm2.regs .rdi _ hdi).trans ((hk1 .rbx (by simp)).trans hO.rbx)) hpc2
    fun st3 hpc3 hc3 hts3 hax3 hdx3 hcs3 hkeep3 hso3 ↦ .done _ (.inr ⟨hpc3.trans rfl, ?_⟩)
  have hw3 : ∀ {o w}, 8 ≤ o → WordAt st2.data.dmem (off (fb m0) o) w →
      o + 8 ≤ 136 → WordAt st3.data.dmem (off (fb m0) o) w := fun ho hw hle i hi ↦ by
    have hi' : i < 8 := hi
    rw [off_add, hkeep3 _ (by omega) (by omega), ← off_add]
    exact hw i hi
  have hreg : ∀ r', r' ∈ [Reg64.rbx, .r12, .r13, .r14, .r15, .rbp] → calleeSaved r' = true →
      reg st3.data r' = reg st r' := fun r' hr hcs ↦
    (hcs3 r' hcs).trans ((hk2' r' hr).trans (hk1 r' (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)))
  refine ⟨hc3, hw3 (by omega) htw2 (by omega), hw3 (by omega) hl16 (by omega), hax3, hdx3,
    (hreg .rbx (by simp) rfl).trans hO.rbx, (congrArg BitVec.toNat (hreg .r15 (by simp) rfl)).trans
      hO.r15, (congrArg BitVec.toNat (hreg .r14 (by simp) rfl)).trans hO.r14,
    (hreg .r12 (by simp) rfl).trans hO.r12, (congrArg BitVec.toNat (hreg .rbp (by simp) rfl)).trans
      hO.rbp, hO.jlt, hO.len, hO.dlt, hr0, hts3, ?_, hO.model⟩
  refine buf_keep h hbuf2 hso3 fun q hq ↦ ?_
  rcases hq with hq | hq
  · exact fun ho ↦ (o_not_t h ho).1 hq
  · exact stack_not_o h hq

end

end NativeRustcVmX64.Whir.SampleQueries
