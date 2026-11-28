module

public import NativeRustcVmX64.Whir.LanesOf.Basic

/-!
# `lanes_of` at level `0`: the row reversed (x86-64)

`b5` returns `None` past 64 words (`b11`), `b6` returns at once for none (`b16`), `b7` starts the
loop `b8`, `b9`: lane `i` is word `len - 1 - i` (R8 its byte offset), RCX the lane, RDI the lanes'
end (`RvLoop`); at the end `b10` returns (`done`).
-/

namespace NativeRustcVmX64.Whir.LanesOf

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.LanesOf
open NativeRustcVmX64.Transcript (frameEnv)
open NativeRustcVmX64.Arrays (eval_reg eval_lit eval_add eval_cmp_eq eval_test pc_cond)

@[expose] public section

/-- **The loop's head** `NativeRustcVmX64.Vm.LanesOf.label_10`, `i` lanes reversed. -/
structure RvLoop (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  body : Body m0 (revL m0) i st
  hi : i < lenOf m0
  hn : lenOf m0 < 65
  rsi : reg st .rsi = rowOf m0
  rcx : reg st .rcx = outOf m0 + BitVec.ofNat 64 (16 * i)
  rdi : reg st .rdi = outOf m0 + BitVec.ofNat 64 (16 * lenOf m0)
  r8 : reg st .r8 = BitVec.ofNat 64 (8 * (lenOf m0 - 1 - i))
  rax : reg st .rax = 1#64
  rdx : (reg st .rdx).toNat = lenOf m0

end

public section

variable [Host] {k : Nat}

/-- The loop turn's environment: the frame, the row's word `len - 1 - i`, lane `i`. -/
abbrev envA (m0 st : MachineData) (i : Nat) : Env :=
  frameEnv m0 st 8 [(rowOf m0 + BitVec.ofNat 64 (8 * (lenOf m0 - 1 - i)), 8),
    (outOf m0 + BitVec.ofNat 64 (16 * i), 16)]

/-- **A turn of the loop**: lane `i` written, back at the head or, at the last, returned. -/
theorem rv_turn (hp : Placed code k) {m0 : MachineData} (hpre : LanesOfPre m0)
    (h0 : (reg m0 .rdi).toNat = 0) {i : Nat} {st : MachineData} (hL : RvLoop m0 i st) :
    Eventually (step1 Host.exe) (fun s ↦ Post m0 s ∨ (RvLoop m0 (i + 1) s.data ∧
      s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LanesOf.b8Offset))) ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.LanesOf.b8Offset)⟩ := by
  have hb := hL.body
  have hi := hL.hi
  have hn := hL.hn
  have hwf : (envA m0 st i).WF := wf3 hpre hb.fr.kept (by omega) (by omega) (by omega) (by omega)
  have hm : Match (envA m0 st i) headA st := by
    refine match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hb.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨?_, ?_, trivial⟩
    · show reg st .rsi + reg st .r8 = _ + BitVec.ofInt 64 0
      rw [hL.rsi, hL.r8]; simp
    · show reg st .rcx = _ + BitVec.ofInt 64 0
      rw [hL.rcx]; simp
  refine exec_then (inf hp b8_in_code (by simp [b8])) run_b8 hwf (by intro l h; cases h) hm
    fun st1 hm1 hpc1 ↦ ?_
  have hout := (pre_out hpre).1.2
  -- the lane
  obtain ⟨hmid, hwr⟩ := after_eq run_b8 ▸ mid_b8
  obtain ⟨hl0, hl1⟩ := after_eq run_b8 ▸ lane_b8
  have hval : (⟨UInt64.ofBitVec ((Sym.load 1 0 8).eval (envA m0 st i)),
      UInt64.ofBitVec ((Sym.lit 0).eval (envA m0 st i))⟩ : EW) = revL m0 i := by
    have := load_row (env := envA m0 st i) (r := 1) (o := lenOf m0 - 1 - i) (t := 0) hpre hb.same
      rfl rfl (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at this
    show (⟨UInt64.ofBitVec ((envA m0 st i).load 1 0 8), UInt64.ofBitVec (BitVec.ofNat 64 0)⟩ : EW) = _
    rw [this]
    rfl
  -- after `b8`: the frame, the changes, the lanes
  have hlanes : ∀ {S : SState} {d : MachineData}, Match (envA m0 st i) S d →
      (∀ t < 8, findWrite 2 (0 + t) S.mem = some (.load 1 0 8, t)) →
      (∀ t < 8, findWrite 2 (0 + 8 + t) S.mem = some (.lit 0, t)) →
      writesBelow S 2 16 = true →
      ChangesIn m0 d lanesOfStack (outs m0) ∧ Lanes m0 (revL m0) (i + 1) d := by
    intro S d hmd h0' h1' hw
    obtain ⟨hc, hso⟩ := same_lanes hpre hb.same hwf hmd hw le_rfl (by omega)
    refine ⟨hc, hb.lanes.extend (w := 1) (pre_out hpre).1.2 (by omega) hso fun t ht ↦ ?_⟩
    obtain rfl : t = 0 := by omega
    have := ewAt_write hmd (r := 2) (o := 0) rfl (by omega) h0' h1'
    rw [hval] at this
    simpa using this
  have hrax1 : reg st1.data .rax = 1#64 := (hm1.regs .rax _ rfl).trans hL.rax
  have hrdx1 : (reg st1.data .rdx).toNat = lenOf m0 :=
    (congrArg BitVec.toNat (hm1.regs .rdx _ rfl)).trans hL.rdx
  simp only [PcOk] at hpc1
  have hc : (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 16) (.reg .rcx)) (.reg .rdi)).eval
      (envA m0 st i) = decide (i + 1 = lenOf m0) := by
    rw [eval_cmp_eq, eval_add, eval_lit, eval_reg, eval_reg]
    show (BitVec.ofNat 64 16 + reg st .rcx == reg st .rdi) = _
    rw [hL.rcx, hL.rdi, Arrays.add16, Arrays.beq_add_left, bv_beq_ofNat _ (by omega),
      toNat_ofNat_lt (by omega)]
    simp only [decide_eq_decide]
    omega
  rw [hc] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases hlast : i + 1 = lenOf m0
  · -- the last lane: return
    have hpc := (hT (decide_eq_true hlast)).trans (hp.label NativeRustcVmX64.Vm.LanesOf.label_14_at)
    obtain ⟨hcs, hls⟩ := hlanes hm1 hl0 hl1 hwr
    have hb1 : Body m0 (revL m0) (i + 1) st1.data :=
      ⟨Transcript.Frame.of_block hb.fr hwf hm1 hmid slots_le, hcs, hls⟩
    obtain ⟨hsz, hf⟩ := lanes_rev h0
    refine Eventually.mono (at_pc (P := fun d ↦ Body m0 (revL m0) (i + 1) d ∧
      reg d .rax = 1#64 ∧ (reg d .rdx).toNat = lenOf m0) (fun d hd ↦ done hp hpre hd.1 (hsz.trans hlast.symm)
      (fun j hj ↦ hf j hj) (by omega) hd.2.1 (hd.2.2.trans hlast.symm)) ⟨⟨hb1, hrax1, hrdx1⟩, hpc⟩)
      fun _ h ↦ .inl h
  · -- `b9`: the next lane
    have hpc := hF fun h ↦ hlast (of_decide_eq_true h)
    refine exec_at (inf hp b9_in_code (by simp [b9])) (exec_after run_b8 run_b9) hwf
      (by intro l h; cases h) hpc hm1 fun st2 hm2 hpc2 ↦ ?_
    obtain ⟨hmid2, hwr2⟩ := after_eq run_b9 ▸ mid_b9
    obtain ⟨hl02, hl12⟩ := after_eq run_b9 ▸ lane_b9
    obtain ⟨hcs, hls⟩ := hlanes hm2 hl02 hl12 hwr2
    simp only [PcOk] at hpc2
    have hc2 : (SBool.not (.cmp .eq .W64 (.bin .and .W64 (.reg .r8) (.reg .r8)) (.lit 0))).eval
        (envA m0 st i) = true := by
      rw [Arrays.eval_not, eval_test, eval_reg]
      show (!(reg st .r8 == BitVec.ofNat 64 0)) = true
      rw [hL.r8, bv_beq_toNat, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
      simp
      omega
    rw [hc2] at hpc2
    have hpc2 := ((pc_cond hpc2).1 rfl).trans (hp.label NativeRustcVmX64.Vm.LanesOf.label_10_at)
    refine .done _ (.inr ⟨⟨⟨Transcript.Frame.of_block hb.fr hwf hm2 hmid2 slots_le, hcs, hls⟩,
      by omega, hn, ?_, ?_, ?_, ?_, ?_, ?_⟩, hpc2⟩)
    · exact (hm2.regs .rsi _ rfl).trans hL.rsi
    · show st2.data.regs.get64 .rcx = _
      rw [hm2.regs .rcx _ rfl, eval_add, eval_lit, eval_reg]
      show BitVec.ofNat 64 16 + reg st .rcx = _
      rw [hL.rcx, Arrays.add16]
    · exact (hm2.regs .rdi _ rfl).trans hL.rdi
    · show st2.data.regs.get64 .r8 = _
      rw [hm2.regs .r8 _ rfl, eval_add, eval_lit, eval_reg]
      show reg st .r8 + BitVec.ofNat 64 18446744073709551608 = _
      rw [hL.r8]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega),
        toNat_ofNat_lt (by omega)]
      omega
    · exact (hm2.regs .rax _ rfl).trans hL.rax
    · exact (congrArg BitVec.toNat (hm2.regs .rdx _ rfl)).trans hL.rdx

/-- The loop's start (`b7`'s end): `RvLoop m0 0`. -/
theorem rv_init {m0 : MachineData} (hpre : LanesOfPre m0) (h65 : lenOf m0 < 65)
    (hz : lenOf m0 ≠ 0) {d : MachineData}
    (hm3 : Match (frameEnv m0 m0 8 []) (after b7 s6) d) : RvLoop m0 0 d := by
  have hwf := wf1 (st := m0) (vars := fun _ ↦ 0) (ret := 0) hpre fun _ h ↦ h
  have hx : ∀ r, (frameEnv m0 m0 8 []).regs r = reg m0 r := fun _ ↦ rfl
  have hl : lenOf m0 = (reg m0 .rdx).toNat := rfl
  obtain ⟨hpro, hw⟩ := after_eq run_b7 ▸ pro_b7
  rw [after_eq run_b7] at hm3
  have hfr := Transcript.Frame.of_prologue Transcript.Frame.entry hwf hm3 hpro slots_le slots_cs
  refine ⟨⟨hfr, chain_same hpre hm3 hw, lanes_zero _⟩, by omega, h65,
    hm3.regs .rsi _ rfl, ?_, ?_, ?_, hm3.regs .rax _ rfl,
    congrArg BitVec.toNat (hm3.regs .rdx _ rfl)⟩
  · show d.regs.get64 .rcx = _
    rw [hm3.regs .rcx _ rfl, Nat.mul_zero, Arrays.add_ofNat_zero]
    rfl
  · show d.regs.get64 .rdi = _
    rw [hm3.regs .rdi _ rfl, eval_add, eval_reg, Arrays.eval_shl_lit _ (by decide), eval_reg]
    show reg m0 .rcx + reg m0 .rdx <<< 4 = _
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, toNat_ofNat_lt (by omega)]
    show lenOf m0 * 2 ^ 4 % 2 ^ 64 = _
    omega
  · show d.regs.get64 .r8 = _
    rw [hm3.regs .r8 _ rfl]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, hx]
    exact r8_eq _ h65 (Nat.pos_of_ne_zero hz)

/-- No lane (`b16`): `Some(0)`. -/
theorem rv_zero {m0 : MachineData} (hpre : LanesOfPre m0) (h0 : (reg m0 .rdi).toNat = 0)
    (hz : lenOf m0 = 0) {st3 : MachineState} {nx : Int64}
    (hm3 : Match (frameEnv m0 m0 8 []) (after b16 s6) st3.data)
    (hpc3 : PcOk (frameEnv m0 m0 8 []) (.ret (.load 0 8 8)) nx st3) : Post m0 st3 := by
  obtain ⟨he, hw⟩ := after_eq run_b16 ▸ epi_b16
  rw [after_eq run_b16] at hm3
  obtain ⟨hpc', hrsp, hc, hs⟩ := chain_ret hpre hm3 hpc3 he hw
  obtain ⟨hsz, hf⟩ := lanes_rev h0
  refine ⟨hpc', hrsp, post_some hc hs (lanes_zero _) (hsz.trans hz) hf (by omega)
    (hm3.regs .rax _ rfl) ?_⟩
  show (st3.data.regs.get64 .rdx).toNat = 0
  rw [hm3.regs .rdx _ rfl]
  rfl

/-- Past 64 words (`b11`): `None`. -/
theorem rv_none {m0 : MachineData} (hpre : LanesOfPre m0) (h0 : (reg m0 .rdi).toNat = 0)
    (h65 : ¬lenOf m0 < 65) {st2 : MachineState} {nx : Int64}
    (hm2 : Match (frameEnv m0 m0 8 []) (after b11 s5) st2.data)
    (hpc2 : PcOk (frameEnv m0 m0 8 []) (.ret (.load 0 8 8)) nx st2) : Post m0 st2 := by
  obtain ⟨he, hw⟩ := after_eq run_b11r ▸ epi_b11r
  rw [after_eq run_b11r] at hm2
  obtain ⟨hpc', hrsp, hc, hs⟩ := chain_ret hpre hm2 hpc2 he hw
  exact ⟨hpc', hrsp, post_none hc hs (by rw [(lanes_rev h0).1]; omega) (hm2.regs .rax _ rfl)⟩

/-- **Level `0`**: from `b5`, the entry's environment. -/
theorem rev (hp : Placed code k) {m0 : MachineData} (hpre : LanesOfPre m0)
    (h0 : (reg m0 .rdi).toNat = 0) {st : MachineState}
    (hm : Match (frameEnv m0 m0 8 []) s0 st.data) (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LanesOf.b5Offset)) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hwf := wf1 (st := m0) (vars := fun _ ↦ 0) (ret := 0) hpre fun _ h ↦ h
  have hx : ∀ r, (frameEnv m0 m0 8 []).regs r = reg m0 r := fun _ ↦ rfl
  refine exec_at (inf hp b5_in_code (by simp [b5])) run_b5 hwf (by intro l h; cases h) hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, hx,
    ult_lit _ (show 65 < 2 ^ 64 by decide)] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases h65 : lenOf m0 < 65
  · have hpc1 := hF (by simpa using h65)
    refine exec_at (inf hp b6_in_code (by simp [b6])) (exec_after run_b5 run_b6) hwf
      (by intro l h; cases h) hpc1 hm1 fun st2 hm2 hpc2 ↦ ?_
    simp only [PcOk] at hpc2
    rw [eval_test, eval_reg, hx, bv_beq_ofNat _ (by decide)] at hpc2
    obtain ⟨hT2, hF2⟩ := pc_cond hpc2
    by_cases hz : lenOf m0 = 0
    · have hpc2 := (hT2 (decide_eq_true hz)).trans (hp.label NativeRustcVmX64.Vm.LanesOf.label_8_at)
      exact exec_at (inf hp b16_in_code (by simp [b16])) (exec_after run_b6 run_b16) hwf
        (by intro l h; cases h) hpc2 hm2 fun st3 hm3 hpc3 ↦
          .done _ (rv_zero hpre h0 hz (after_eq run_b16 ▸ hm3) hpc3)
    · have hpc2 := hF2 fun h ↦ hz (of_decide_eq_true h)
      refine exec_at (inf hp b7_in_code (by simp [b7])) (exec_after run_b6 run_b7) hwf
        (by intro l h; cases h) hpc2 hm2 fun st3 hm3 hpc3 ↦ ?_
      simp only [PcOk] at hpc3
      exact at_pc (fun d hd ↦ run_loop (L := RvLoop m0) (lenOf m0) (fun i _ h ↦ h.hi)
        (fun i d hd ↦ rv_turn hp hpre h0 hd) hd)
        ⟨rv_init hpre h65 hz (after_eq run_b7 ▸ hm3), hpc3⟩
  · have hpc1 := (hT (by simpa using h65)).trans (hp.label NativeRustcVmX64.Vm.LanesOf.label_2_at)
    exact exec_at (inf hp b11_in_code (by simp [b11])) (exec_after run_b5 run_b11r) hwf
      (by intro l h; cases h) hpc1 hm1 fun st2 hm2 hpc2 ↦
        .done _ (rv_none hpre h0 h65 (after_eq run_b11r ▸ hm2) hpc2)

end

end NativeRustcVmX64.Whir.LanesOf
