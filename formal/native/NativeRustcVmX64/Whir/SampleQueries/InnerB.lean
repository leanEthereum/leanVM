module

public import NativeRustcVmX64.Whir.SampleQueries.InnerA

/-!
# `sample_queries` on x86-64: a position pushed

`b16_step`: position `i` of the chunk stored at the buffer's next word and its count raised;
back at the inner loop's head (`Inner` at `i + 1`) or, after the chunk's last, on to `b17`
(`AtB17`).
-/

namespace NativeRustcVmX64.Whir.SampleQueries

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.SampleQueries
open NativeRustcVmX64.Transcript (Frame frameEnv)
open NativeRustcVmX64.Arrays (pc_cond)
open NativeRustcVm (BufWordsAt WordsAt WordAt)

@[expose] public section

/-- **At `b17`**: the chunk's `n` positions pushed after `qs`. -/
structure AtB17 [Labels] (a : DecArea) (s0 : TState) (m0 : MachineData) (j r : Nat) (s : TState)
    (qs : List UInt64) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  tw : WordAt st.dmem (off (fb m0) 24) (UInt64.ofBitVec (tA m0))
  l16 : WordAt st.dmem (off (fb m0) 16) r.toUInt64
  l32 : WordAt st.dmem (off (fb m0) 32) j.toUInt64
  rcx : (reg st .rcx).toNat = nOf m0 r
  r14 : (reg st .r14).toNat = cnt m0
  rbp : (reg st .rbp).toNat = qs.length + nOf m0 r + 1
  jlt : j < cnt m0
  len : qs.length + r = cnt m0
  r0 : r ≠ 0
  dle : dep m0 ≤ 128
  ts : TStateAt st.dmem (tA m0) a (sq s).2
  buf : BufWordsAt st.dmem (oA m0) queryCap (qs ++ (chunk (dep m0) (sq s).1 (nOf m0 r)).toList)
  model : auxP (dep m0) (cnt m0) (cnt m0) s0 =
    (qs.toArray ++ (auxP (dep m0) (cnt m0 - j) r s).1, (auxP (dep m0) (cnt m0 - j) r s).2)

end

public section

theorem mul8 {x : BitVec 64} {n : Nat} (h : x.toNat = n) :
    x * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, h, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem r12_next (i : Nat) :
    BitVec.ofNat 64 18446744073709551608 + (0#64 - BitVec.ofNat 64 (8 * i)) =
      0#64 - BitVec.ofNat 64 (8 * (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem r15_next {x y : BitVec 64} {d i : Nat} (hx : x.toNat = d) (hy : y = BitVec.ofNat 64 (i * d))
    (hb : (i + 1) * d < 2 ^ 64) : x + y = BitVec.ofNat 64 ((i + 1) * d) := by
  subst hy
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, hx, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.succ_mul]
  have : i * d ≤ (i + 1) * d := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.mod_eq_of_lt (show i * d < 2 ^ 64 by omega)]
  omega

theorem cond16 {i n : Nat} (h1 : i + 1 ≤ n) (hn : 8 * n < 2 ^ 64) :
    (BitVec.ofNat 64 18446744073709551608 + (0#64 - BitVec.ofNat 64 (8 * i)) +
      BitVec.ofNat 64 (8 * n) == 0#64) = decide (i + 1 = n) := by
  rw [r12_next i, beq_of_toNat]
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  by_cases hh : i + 1 = n
  · subst hh; simp; omega
  · simp only [hh, decide_false, decide_eq_false_iff_not]; omega

variable [Host] {k : Nat} {a : DecArea} {s0 : TState} {m0 : MachineData}

/-- **`b16`**: the position pushed; the inner loop goes on or ends. -/
theorem b16_step (hp : Placed code k) (h : SampleQueriesPre a s0 m0) {j r : Nat} {s : TState}
    {qs : List UInt64} {i : Nat} {st : MachineData} (hB : AtB16 a s0 m0 j r s qs i st) :
    Eventually (step1 Host.exe) (fun st' ↦
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b14Offset) ∧ Inner a s0 m0 j r s qs (i + 1) st'.data) ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b17Offset) ∧ AtB17 a s0 m0 j r s qs st'.data))
      ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b16Offset)⟩ := by
  have hcnt := pre_cnt h
  have hlen := hB.len
  have hilt := hB.ilt
  have hnle : nOf m0 r ≤ r := Nat.min_le_right _ _
  have hdle := hB.dle
  have hn128 : nOf m0 r ≤ 128 := by
    have : 128 / dep m0 ≤ 128 := Nat.div_le_self _ _
    simp only [nOf]; omega
  set n := nOf m0 r with hndef
  set L := qs.length with hLdef
  have hLi : L + i < 230 := by omega
  have hon : (oA m0).toNat + 1848 ≤ 2 ^ 64 := (pre_out h).2.1
  set wA := oA m0 + BitVec.ofNat 64 (8 + 8 * (L + i)) with hwA
  have hwAn : wA.toNat = (oA m0).toNat + (8 + 8 * (L + i)) := toNat_add_ofNat _ _ (by omega)
  have hfb := fb_toNat h
  have hoS : Apart (oA m0) 1848 (stackBelow m0 128) (128 + 8) :=
    Transcript.apart_frame (pre_out h).2.2.2.2.1 (pre_hn h) N_ge
  have hmo : NativeRustcVm.Mapped st.dmem (oA m0) 1848 :=
    Mapped.keeps (pre_out h).1 hB.ctx.fr.kept
  have hwf : (frameEnv m0 st 128 [(wA, 8), (oA m0, 8)] (fun _ ↦ 0) 0).WF := by
    refine Transcript.frame_wf ⟨Mapped.keeps (Transcript.frame_mapped (pre_S h) N_ge)
      hB.ctx.fr.kept, fb_noWrap h⟩ ?_ (Transcript.pairwise3 ?_ ?_ ?_)
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨Transcript.mapped_off hmo (by omega), show wA.toNat + 8 ≤ 2 ^ 64 by omega⟩
      · exact ⟨fun i hi ↦ hmo i (by omega), show (oA m0).toNat + 8 ≤ 2 ^ 64 by omega⟩
    · show NativeRustcVm.Apart (stackBelow m0 128) (128 + 8) wA 8
      unfold Apart at hoS
      unfold NativeRustcVm.Apart
      rw [hwAn]
      omega
    · show NativeRustcVm.Apart (stackBelow m0 128) (128 + 8) (oA m0) 8
      unfold Apart at hoS
      unfold NativeRustcVm.Apart
      omega
    · show NativeRustcVm.Apart wA 8 (oA m0) 8
      unfold NativeRustcVm.Apart
      rw [hwAn]
      omega
  have hrbp : reg st .rbp = BitVec.ofNat 64 (L + i + 1) :=
    BitVec.eq_of_toNat_eq (by rw [hB.rbp, BitVec.toNat_ofNat]; omega)
  have hm : Match (frameEnv m0 st 128 [(wA, 8), (oA m0, 8)] (fun _ ↦ 0) 0) pushS st := by
    refine match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hB.ctx.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨?_, ?_, trivial⟩
    · show (frameEnv m0 st 128 [(wA, 8), (oA m0, 8)] (fun _ ↦ 0) 0).load 0 72 8 +
          reg st .rbp * BitVec.ofNat 64 8 = wA + BitVec.ofInt 64 0
      rw [loc_load hB.ctx.out, UInt64.toBitVec_ofBitVec, hrbp,
        mul8 (n := L + i + 1) (by rw [BitVec.toNat_ofNat]; omega)]
      simp only [BitVec.ofInt_ofNat, BitVec.add_zero, hwA]
      congr 2
      omega
    · show (frameEnv m0 st 128 [(wA, 8), (oA m0, 8)] (fun _ ↦ 0) 0).load 0 72 8 =
          oA m0 + BitVec.ofInt 64 0
      rw [loc_load hB.ctx.out, UInt64.toBitVec_ofBitVec]
      simp
  refine exec_then (inf hp b16_in_code (by simp [b16])) run_b16 hwf (by intro l h; cases h) hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hwq, hwc, hall, hcx, h12, h15, hbp, hk⟩ := ok_b16
  have hin := midOk_writesIn hmid
  have hall' : ∀ w ∈ (after b16 pushS).mem, (w.r = 1 ∨ w.r = 2) ∧ w.off + w.n ≤ 8 := by
    intro w hw
    rw [List.all_eq_true] at hall
    have := hall w hw
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact this
  rw [← after_eq run_b16] at hm1
  have hmiss : ∀ o, miss (after b16 pushS) o = true := fun o ↦ by
    unfold miss
    rw [List.all_eq_true]
    intro w hw
    have := (hall' w hw).1
    have hr : (w.r != 0) = true := by rcases this with h | h <;> rw [h] <;> rfl
    simp [hr]
  have hso : SameOutside st.dmem st1.data.dmem (fun q ↦ InRange wA 8 q ∨ InRange (oA m0) 8 q) :=
    fun q hq ↦ hm1.get?_mem0 hwf fun hW ↦ hq (by
      obtain ⟨w, hw, b, sz, hb, jj, h1, h2, rfl⟩ := Transcript.written_off hwf hW
      obtain ⟨hr, hle⟩ := hall' w hw
      rcases hr with hr | hr <;> rw [hr] at hb <;> cases hb
      · exact .inl (inRange_off_self (by omega) (by omega))
      · exact .inr (inRange_off_self (by omega) (by omega)))
  have hRo : ∀ q, (InRange wA 8 q ∨ InRange (oA m0) 8 q) → InRange (oA m0) queryBufBytes q := by
    rintro q (hq | hq)
    · exact NativeRustcVm.InRange.of_sub (a := oA m0) (n := 1848) hq (by unfold NativeRustcVm.NoWrap; omega)
        (by omega)
    · exact Transcript.inRange_mono hq (by decide)
  have hfr1 : Frame m0 128 slots 8 st1.data := Frame.of_block hB.ctx.fr hwf hm1 hmid slots_le
  have hkw : ∀ {o w}, o + 8 ≤ 136 → WordAt st.dmem (off (fb m0) o) w →
      WordAt st1.data.dmem (off (fb m0) o) w := fun hle hw ↦ loc_keep hwf hm1 hin hle (hmiss _) hw
  have hc1 : Ctx m0 st1.data :=
    ⟨hfr1, hkw (by omega) hB.ctx.out, same_trans h hB.ctx.same hso fun q hq ↦ .inl (hRo q hq),
      (reg_kept hm1 (kept_spec hk (by simp))).trans hB.ctx.r13⟩
  have hts1 : TStateAt st1.data.dmem (tA m0) a (sq s).2 :=
    hB.ts.frame (hm1.kept hwf) (fun q hq ↦ o_not_t h (hRo q hq)) hso
  -- The buffer.
  have hch : (chunk (dep m0) (sq s).1 n).toList.take (i + 1) =
      (chunk (dep m0) (sq s).1 n).toList.take i ++ [queryBits (sq s).1 (i * dep m0) (dep m0)] :=
    chunk_take_succ _ _ hilt
  have hlt : ((chunk (dep m0) (sq s).1 n).toList.take i).length = i := by
    simp [chunk_size]; omega
  have hbuf1 : BufWordsAt st1.data.dmem (oA m0) queryCap
      (qs ++ (chunk (dep m0) (sq s).1 n).toList.take (i + 1)) := by
    obtain ⟨-, -, hws⟩ := hB.buf
    refine ⟨by simp [chunk_size, queryCap]; omega, ?_, ?_⟩
    · have := Transcript.wordAt_write hm1 (r := 2) (o := 0) rfl (by omega) (wrote_spec hwc)
      rw [off_zero, show (Sym.reg .rbp).eval (frameEnv m0 st 128 [(wA, 8), (oA m0, 8)] (fun _ ↦ 0) 0)
        = reg st .rbp from rfl, hrbp, ofBitVec_ofNat] at this
      rw [hch, List.length_append, List.length_append, hlt]
      simpa [Nat.add_assoc] using this
    · rw [hch, ← List.append_assoc, NativeRustcVm.wordsAt_append_iff]
      refine ⟨NativeRustcVm.BytesAt.of_sameOutside hws hso fun i' hi' hq ↦ ?_, ?_⟩
      · rw [length_flatMap_wordBytes, List.length_append, hlt] at hi'
        have e : (oA m0 + 8#64 + BitVec.ofNat 64 i').toNat = (oA m0).toNat + 8 + i' := by
          rw [toNat_add_ofNat _ _ (by rw [toNat_add_ofNat _ _ (by omega)]; omega),
            toNat_add_ofNat _ _ (by omega)]
        rcases hq with hq | hq
        · rw [Sym.inRange_iff (by omega), e, hwAn] at hq; omega
        · rw [Sym.inRange_iff (by omega), e] at hq; omega
      · rw [NativeRustcVm.wordsAt_singleton_iff, List.length_append, hlt]
        have := Transcript.wordAt_write hm1 (r := 1) (o := 0) rfl (by omega) (wrote_spec hwq)
        rw [off_zero, show (Sym.reg .rax).eval (frameEnv m0 st 128 [(wA, 8), (oA m0, 8)]
          (fun _ ↦ 0) 0) = reg st .rax from rfl, hB.rax, UInt64.ofBitVec_toBitVec] at this
        rwa [show oA m0 + 8#64 + BitVec.ofNat 64 (8 * (L + i)) = wA by
          rw [hwA, BitVec.add_assoc, ← BitVec.ofNat_add]]
  -- The registers.
  have hrcx : (reg st1.data .rcx).toNat = n := by
    rw [show reg st1.data .rcx = _ from hm1.regs .rcx _ hcx]; exact hB.rbx
  have hr12 : reg st1.data .r12 = 0#64 - BitVec.ofNat 64 (8 * (i + 1)) := by
    rw [show reg st1.data .r12 = _ from hm1.regs .r12 _ h12]
    show BitVec.ofNat 64 18446744073709551608 + reg st .r12 = _
    rw [hB.r12, r12_next i]
  have hr15 : reg st1.data .r15 = BitVec.ofNat 64 ((i + 1) * dep m0) := by
    rw [show reg st1.data .r15 = _ from hm1.regs .r15 _ h15]
    show reg st .r13 + reg st .r15 = _
    have : (i + 1) * dep m0 ≤ 128 * 128 := Nat.mul_le_mul (by omega) hdle
    exact r15_next (congrArg BitVec.toNat hB.ctx.r13) hB.r15 (by omega)
  have hrbp1 : (reg st1.data .rbp).toNat = L + (i + 1) + 1 := by
    rw [show reg st1.data .rbp = _ from hm1.regs .rbp _ hbp]
    show (reg st .rbp + BitVec.ofNat 64 1).toNat = _
    rw [toNat_add1 hB.rbp (by omega)]
    omega
  have hr14 : (reg st1.data .r14).toNat = cnt m0 :=
    (congrArg BitVec.toNat (reg_kept hm1 (kept_spec hk (by simp)))).trans hB.r14
  simp only [PcOk] at hpc1
  have hc : (SBool.not (.cmp .eq .W64 (.bin .add .W64 (.bin .add .W64 (.lit 18446744073709551608)
      (.reg .r12)) (.load 0 40 8)) (.lit 0))).eval
      (frameEnv m0 st 128 [(wA, 8), (oA m0, 8)] (fun _ ↦ 0) 0) = decide (i + 1 ≠ n) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
    rw [loc_load hB.l40]
    show (!(BitVec.ofNat 64 18446744073709551608 + reg st .r12 + BitVec.ofNat 64 (8 * n) ==
      BitVec.ofNat 64 0)) = _
    rw [hB.r12, show BitVec.ofNat 64 0 = 0#64 from rfl, cond16 hilt (by omega)]
    by_cases hh : i + 1 = n <;> simp [hh]
  rw [hc] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases hlast : i + 1 = n
  · have hpc := hF (by simp [hlast])
    refine .done _ (.inr ⟨hpc.trans rfl, ⟨hc1, hkw (by omega) hB.tw, hkw (by omega) hB.l16,
      hkw (by omega) hB.l32, hrcx, hr14, by rw [hrbp1, hlast], hB.jlt, hlen, hB.r0, hdle, hts1, ?_,
      hB.model⟩⟩)
    have e : (chunk (dep m0) (sq s).1 (nOf m0 r)).toList =
        (chunk (dep m0) (sq s).1 (nOf m0 r)).toList.take (i + 1) := by
      rw [hlast]; exact (chunk_take_all _ _ _).symm
    rw [e]
    exact hbuf1
  · have hpc := (hT (by simp [hlast])).trans (hp.label NativeRustcVmX64.Vm.SampleQueries.label_6_at)
    exact .done _ (.inl ⟨hpc, ⟨hc1, hkw (by omega) hB.tw, hkw (by omega) hB.l16,
      hkw (by omega) hB.l32, hkw (by omega) hB.l40, hkw (by omega) hB.l48, hkw (by omega) hB.l56,
      hkw (by omega) hB.l64, hrcx, hr12, hr14, hr15, hrbp1, hB.jlt, hlen, hB.r0, hB.dpos, hdle,
      by omega, hts1, hbuf1, hB.model⟩⟩)

end

end NativeRustcVmX64.Whir.SampleQueries
