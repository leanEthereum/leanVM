module

public import NativeRustcVmX64.Whir.SampleQueries.Outer

/-!
# `sample_queries` on x86-64: a challenge's chunk size, the inner loop's start

`b12_step`: `PER_CHALLENGE[depth]` read (`nS_eval`), the chunk's size `n = min(r, 128 / depth)`
in RCX; a depth `0` goes to `b9` (`AtB9`, no position), else to `b13` (`AtB13`). `b13_step`: the
inner loop's locals stored, its head (`Inner` at `0`).
-/

namespace NativeRustcVmX64.Whir.SampleQueries

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.SampleQueries
open NativeRustcVmX64.Transcript (Frame frameEnv)
open NativeRustcVmX64.Arrays (pc_cond)
open NativeRustcVm (BufWordsAt WordsAt WordAt)

public section

/-- A byte loaded. -/
theorem load1_byte [Labels] {env : Env} {r o : Nat} {b : UInt8}
    (h : NativeRustcVm.BytesAt env.mem0 (env.base r + BitVec.ofNat 64 o) [b]) :
    (env.load r o 1).toNat = b.toNat := by
  rw [Env.load_of_bytesAt (n := 1) (bs := [b]) rfl h, ofBytes_natCast, BitVec.ofInt_natCast,
    BitVec.toNat_ofNat, Nat.ofBytes_cons]
  show (0 * 256 + b.toNat) % 2 ^ 64 = _
  have := b.toNat_lt
  omega

/-- **`b12`'s RCX**: the smaller of `r` and the byte. -/
theorem nS_eval [Labels] {env : Env} {r p : Nat} (hr : (env.load 0 16 8).toNat = r)
    (hp : (env.load 1 (0 + (env.regs .r13).toNat) 1).toNat = p) (hp8 : p < 256) :
    (nS.eval env).toNat = min r p := by
  have hz : (UnOp.apply (.zext .W8) .W32 (env.load 1 (0 + (env.regs .r13).toNat) 1)).toNat = p := by
    simp only [UnOp.apply, toNat_ext, BitVec.toNat_setWidth, toNat_low, Width.bits, hp]
    omega
  simp only [nS, Sym.eval, SBool.eval, CmpOp.apply, low_W64]
  split <;> rename_i hc
  · simp only [BitVec.ult, decide_eq_true_eq, hr, hz] at hc
    rw [hr]; omega
  · simp only [BitVec.ult, decide_eq_true_eq, hr, hz] at hc
    rw [hz]; omega

variable [Host] {k : Nat} {a : DecArea} {s0 : TState} {m0 : MachineData}

/-- **`b12`**: the chunk's size; a depth `0` on to `b9`, else to `b13`. -/
theorem b12_step (hp : Placed code k) (h : SampleQueriesPre a s0 m0) {j r : Nat} {s : TState}
    {qs : List UInt64} {st : MachineData} (hB : AtB12 a s0 m0 j r s qs st) :
    Eventually (step1 Host.exe) (fun st' ↦
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b9Offset) ∧ AtB9 a s0 m0 j r (nOf m0 r) (sq s).2
        (qs ++ (chunk (dep m0) (sq s).1 (nOf m0 r)).toList) st'.data) ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b13Offset) ∧ AtB13 a s0 m0 j r s qs st'.data))
      ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b12Offset)⟩ := by
  have hcnt := pre_cnt h
  have hdl := hB.dlt
  have hlen := hB.len
  obtain ⟨hpb, hpnw, hpap⟩ := pre_ro h .perChallenge
  have hplen : NativeRustcVm.Data.Item.perChallenge.bytes.length = 129 := perChallenge_length
  have hper := per_at h hB.ctx
  have hfnw := fb_noWrap h
  have hap : NativeRustcVm.Apart (fb m0) (128 + 8) (rodataAddr .perChallenge) 129 := by
    have := Transcript.apart_frame hpap (pre_hn h) N_ge
    rw [hplen] at this
    exact Transcript.Apart.symm' this
  have hwf : (frameEnv m0 st 128 [(rodataAddr .perChallenge, 129)] (fun _ ↦ 0) 0).WF :=
    Transcript.frame_wf ⟨Mapped.keeps (Transcript.frame_mapped (pre_S h) N_ge) hB.ctx.fr.kept, hfnw⟩
      (by
        intro x hx
        rw [List.mem_singleton] at hx
        subst hx
        exact ⟨hplen ▸ hper.mapped, hplen ▸ hpnw⟩)
      (List.pairwise_pair.mpr hap)
  have hr13 : (reg st .r13).toNat = dep m0 := congrArg BitVec.toNat hB.ctx.r13
  have hm : Match (frameEnv m0 st 128 [(rodataAddr .perChallenge, 129)] (fun _ ↦ 0) 0) perS st :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hB.ctx.fr.rsp_eval, Transcript.known_ptr rfl hB.r12, trivial⟩
      trivial ⟨show (reg st .r13).toNat < 129 by omega, trivial⟩ trivial
  refine exec_then (inf hp b12_in_code (by simp [b12])) run_b12 hwf (by intro l h; cases h) hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hw, hm16, hm24, h64, h56, hax, hcx, h12, hk⟩ := after_eq run_b12 ▸ ok_b12
  have hc1 := hB.ctx.blockW h hwf hm1 (L := 72) le_rfl hmid hw (kept_spec hk (by simp))
  have hs1 : SameOutside st.dmem st1.data.dmem (InRange (fb m0) 72) :=
    Transcript.sameOutside_low hwf hm1 (r := 0) rfl (by omega) (wr0_spec hw)
  have hin := midOk_writesIn hmid
  have hl16 := loc_keep hwf hm1 hin (by omega) hm16 hB.l16
  have hrax : (reg st1.data .rax).toNat = r := by
    rw [show reg st1.data .rax = _ from hm1.regs .rax _ hax]
    show ((frameEnv m0 st 128 [(rodataAddr .perChallenge, 129)] (fun _ ↦ 0) 0).load 0 16 8).toNat = r
    rw [loc_load hB.l16]
    simp; omega
  have hdv : 128 / dep m0 ≤ 128 := Nat.div_le_self _ _
  have hn : (reg st1.data .rcx).toNat = nOf m0 r := by
    rw [show reg st1.data .rcx = _ from hm1.regs .rcx _ hcx]
    have hb := perChallenge_byte hper (d := dep m0) (by omega)
    rw [nS_eval (r := r) (p := 128 / dep m0) (by rw [loc_load hB.l16]; simp; omega)
      (by
        rw [show ((frameEnv m0 st 128 [(rodataAddr .perChallenge, 129)] (fun _ ↦ 0) 0).regs .r13)
          = reg st .r13 from rfl, hr13, Nat.zero_add]
        rw [load1_byte (b := UInt8.ofNat (128 / dep m0)) hb]
        simp; omega)
      (by omega)]
    exact Nat.min_comm _ _
  have hts1 := TStateAt.block h (hm1.kept hwf) (by omega) hs1 hB.ts
  have hbuf1 := buf_keep h hB.buf hs1 fun q hq ↦ frame_not_o h (Transcript.inRange_mono hq (by omega))
  have hk1 : ∀ r', r' ∈ [Reg64.rbx, .r13, .r14, .r15, .rbp] → reg st1.data r' = reg st r' :=
    fun r' hr ↦ reg_kept hm1 (kept_spec hk hr)
  simp only [PcOk] at hpc1
  have hc : (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .r13) (.reg .r13)) (.lit 0)).eval
      (frameEnv m0 st 128 [(rodataAddr .perChallenge, 129)] (fun _ ↦ 0) 0) = decide (dep m0 = 0) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, BitVec.and_self]
    rw [beq_of_toNat]
    show decide ((reg st .r13).toNat = (BitVec.ofNat 64 0).toNat) = _
    rw [hr13]
    simp
  rw [hc] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases hd0 : dep m0 = 0
  · have hpc := (hT (decide_eq_true hd0)).trans (hp.label NativeRustcVmX64.Vm.SampleQueries.label_10_at)
    have hn0 : nOf m0 r = 0 := by simp [nOf, hd0]
    have hch : (chunk (dep m0) (sq s).1 (nOf m0 r)).toList = [] := by rw [hn0]; simp [chunk]
    refine .done _ (.inl ⟨hpc, ⟨hc1, loc_keep hwf hm1 hin (by omega) hm24 hB.tw, hrax, hn,
      (hk1 .rbx (by simp)).trans hB.rbx, (congrArg BitVec.toNat (hk1 .r15 (by simp))).trans hB.r15,
      (congrArg BitVec.toNat (hk1 .r14 (by simp))).trans hB.r14, ?_, ?_, hB.jlt, by omega, ?_, hdl,
      hts1, ?_, ?_⟩⟩)
    · rw [show reg st1.data .r12 = _ from hm1.regs .r12 _ h12]
      exact Transcript.eval_ptr rfl
    · rw [hch, List.append_nil]
      exact (congrArg BitVec.toNat (hk1 .rbp (by simp))).trans hB.rbp
    · rw [hch, List.append_nil, hn0]; omega
    · rw [hch, List.append_nil]; exact hbuf1
    · exact auxP_next hB.model hB.jlt hB.r0
  · have hpc := hF fun h ↦ hd0 (of_decide_eq_true h)
    refine .done _ (.inr ⟨hpc.trans rfl, ⟨hc1, loc_keep hwf hm1 hin (by omega) hm24 hB.tw, hl16, ?_, ?_,
      hn, (congrArg BitVec.toNat (hk1 .r15 (by simp))).trans hB.r15,
      (congrArg BitVec.toNat (hk1 .r14 (by simp))).trans hB.r14,
      (congrArg BitVec.toNat (hk1 .rbp (by simp))).trans hB.rbp, hB.jlt, hlen, hdl, hB.r0,
      Nat.pos_of_ne_zero hd0, hts1, hbuf1, hB.model⟩⟩)
    · have := loc_write hm1 (by omega) h56
      rwa [show (Sym.reg .rdx).eval (frameEnv m0 st 128 [(rodataAddr .perChallenge, 129)]
        (fun _ ↦ 0) 0) = reg st .rdx from rfl, hB.rdx, UInt64.ofBitVec_toBitVec] at this
    · have := loc_write hm1 (by omega) h64
      rwa [show (Sym.reg .rax).eval (frameEnv m0 st 128 [(rodataAddr .perChallenge, 129)]
        (fun _ ↦ 0) 0) = reg st .rax from rfl, hB.rax, UInt64.ofBitVec_toBitVec] at this

/-- **`b13`**: the inner loop's locals; its head. -/
theorem b13_step (hp : Placed code k) (h : SampleQueriesPre a s0 m0) {j r : Nat} {s : TState}
    {qs : List UInt64} {st : MachineData} (hB : AtB13 a s0 m0 j r s qs st) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b14Offset) ∧
      Inner a s0 m0 j r s qs 0 st'.data) ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b13Offset)⟩ := by
  have hcnt := pre_cnt h
  have hdl := hB.dlt
  have hlen := hB.len
  have hwf := mid_wf (vars := fun _ ↦ 0) (ret := 0) h hB.ctx.fr.kept
  refine exec_then (inf hp b13_in_code (by simp [b13])) run_b13 hwf (by intro l h; cases h)
    (mid_match hB.ctx.fr) fun st1 hm1 hpc1 ↦ .done _ ⟨hpc1.trans rfl, ?_⟩
  obtain ⟨hmid, hw, hm16, hm24, h32, h40, h48, hbp, h15, h12, hk⟩ := after_eq run_b13 ▸ ok_b13
  have hc1 := hB.ctx.block h hm1 (L := 56) (by omega) hmid hw (kept_spec hk (by simp))
  have hs1 := block_same hwf hm1 (by omega) hw
  have hin := midOk_writesIn hmid
  have hnpos : 1 ≤ nOf m0 r := by
    have : 1 ≤ 128 / dep m0 := (Nat.le_div_iff_mul_le hB.dpos).mpr (by omega)
    simp only [nOf]; have := hB.r0; omega
  have hnle : nOf m0 r ≤ r := Nat.min_le_right _ _
  have hk1 : ∀ r', r' ∈ [Reg64.rcx, .r13, .r14] → reg st1.data r' = reg st r' :=
    fun r' hr ↦ reg_kept hm1 (kept_spec hk hr)
  refine ⟨hc1, loc_keep hwf hm1 hin (by omega) hm24 hB.tw, loc_keep hwf hm1 hin (by omega) hm16 hB.l16,
    ?_, ?_, ?_, loc_keep hwf hm1 hin (by omega) (miss_of_wr0 hw le_rfl) hB.l56,
    loc_keep hwf hm1 hin (by omega) (miss_of_wr0 hw (by omega)) hB.l64,
    (congrArg BitVec.toNat (hk1 .rcx (by simp))).trans hB.rcx, ?_,
    (congrArg BitVec.toNat (hk1 .r14 (by simp))).trans hB.r14, ?_, ?_, hB.jlt, hlen, hB.r0,
    hB.dpos, by omega, by omega, TStateAt.block h (hm1.kept hwf) (by omega) hs1 hB.ts, ?_, hB.model⟩
  · have := loc_write hm1 (by omega) h32
    rwa [show (Sym.reg .r15).eval (frameEnv m0 st 128 []) = reg st .r15 from rfl,
      ofBitVec_eq hB.r15] at this
  · have := loc_write hm1 (by omega) h40
    rwa [f40_eval _ (n := nOf m0 r) hB.rcx hnpos (by omega), ofBitVec_ofNat] at this
  · have := loc_write hm1 (by omega) h48
    rwa [f48_eval _ (n := qs.length) hB.rbp (by omega)] at this
  · rw [show reg st1.data .r12 = _ from hm1.regs .r12 _ h12]
    simp [Sym.eval]
  · rw [show reg st1.data .r15 = _ from hm1.regs .r15 _ h15]
    simp [Sym.eval]
  · rw [show reg st1.data .rbp = _ from hm1.regs .rbp _ hbp]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    show (reg st .rbp + BitVec.ofNat 64 1).toNat = _
    rw [toNat_add1 hB.rbp (by omega)]
  · rw [List.take_zero, List.append_nil]
    exact buf_keep h hB.buf hs1 fun q hq ↦ frame_not_o h (Transcript.inRange_mono hq (by omega))

end

end NativeRustcVmX64.Whir.SampleQueries
