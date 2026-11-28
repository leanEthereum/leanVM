module

public import NativeRustcVmX64.Whir.LanesOf.Basic

/-!
# `lanes_of` at a later level: the row's pairs (x86-64)

`b1` returns `None` past 129 words (`b11`), `b2` returns at once for no pair (`b10`), `b3` takes
one pair to the tail (`b4`, `b15`), more to the loop (`b12`, then `b13`: two pairs a turn, RDI the
lanes copied, R10 their bytes plus `24`, `CpLoop`); after the loop `b14` returns for an even count
(`b10`) or copies the last pair (`b15`, `tail`).
-/

namespace NativeRustcVmX64.Whir.LanesOf

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.LanesOf
open NativeRustcVmX64.Transcript (frameEnv)
open NativeRustcVmX64.Arrays (eval_reg eval_lit eval_add pc_cond)

@[expose] public section

/-- **The loop's head** `NativeRustcVmX64.Vm.LanesOf.label_16`, `2j` lanes copied. -/
structure CpLoop (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  body : Body m0 (pairL m0) (2 * j) st
  hj : j < nOf m0 / 2
  hn : lenOf m0 < 130
  rsi : reg st .rsi = rowOf m0
  rcx : reg st .rcx = outOf m0
  rdi : (reg st .rdi).toNat = 2 * j
  r10 : reg st .r10 = BitVec.ofNat 64 (32 * j + 24)
  r9 : (reg st .r9).toNat = 2 * (nOf m0 / 2)
  r8 : (reg st .r8).toNat = lenOf m0
  rax : reg st .rax = 1#64
  rdx : (reg st .rdx).toNat = nOf m0

/-- **The last pair** `NativeRustcVmX64.Vm.LanesOf.label_13`: `e = n - 1` lanes copied. -/
structure CpTail (m0 : MachineData) (e : Nat) (st : MachineData) : Prop where
  body : Body m0 (pairL m0) e st
  he : e + 1 = nOf m0
  hn : lenOf m0 < 130
  rsi : reg st .rsi = rowOf m0
  rcx : reg st .rcx = outOf m0
  rdi : (reg st .rdi).toNat = e
  rax : reg st .rax = 1#64
  rdx : (reg st .rdx).toNat = nOf m0

end

public section

/-! ## Values -/

theorem and126 (x : BitVec 64) (h : x.toNat < 65) :
    (BinOp.apply .and .W32 (UnOp.apply .trunc .W32 x) (BitVec.ofNat 64 126)).toNat =
      2 * (x.toNat / 2) := by
  have key : ∀ L < 65, (BinOp.apply .and .W32 (UnOp.apply .trunc .W32 (BitVec.ofNat 64 L))
      (BitVec.ofNat 64 126)).toNat = 2 * (L / 2) := by decide +kernel
  simpa using key x.toNat h

theorem testb2 (x : BitVec 64) (h : x.toNat < 130) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 x (BitVec.ofNat 64 2)) (BitVec.ofNat 64 0) =
      decide (x.toNat / 2 % 2 = 0) := by
  have key : ∀ L < 130, CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (BitVec.ofNat 64 L)
      (BitVec.ofNat 64 2)) (BitVec.ofNat 64 0) = decide (L / 2 % 2 = 0) := by decide +kernel
  simpa using key x.toNat h

theorem add_ofNat_ofInt (a : BitVec 64) (x y : Nat) :
    a + BitVec.ofNat 64 (x + y) = a + BitVec.ofNat 64 x + BitVec.ofInt 64 (y : Int) := by
  rw [BitVec.ofInt_natCast, BitVec.add_assoc, BitVec.ofNat_add]

theorem toNat_add_lit {x : BitVec 64} {c : Nat} (h : x.toNat + c < 2 ^ 64) :
    (BitVec.ofNat 64 c + x).toNat = c + x.toNat := by
  rw [BitVec.add_comm, toNat_add_ofNat _ _ h]
  omega

variable [Host] {k : Nat}

/-! ## The last pair -/

/-- The tail's environment: the frame, the row's pair `e`, lane `e`. -/
abbrev envT (m0 st : MachineData) (e : Nat) : Env :=
  frameEnv m0 st 8 [(rowOf m0 + BitVec.ofNat 64 (8 * (2 * e)), 16),
    (outOf m0 + BitVec.ofNat 64 (16 * e), 16)]

theorem shl4_eval {st : MachineData} {e : Nat} (h : (reg st .rdi).toNat = e) (he : e < 64)
    {env : Env} (henv : env.regs .rdi = reg st .rdi) :
    (Sym.bin .shl .W64 (.reg .rdi) (.lit 4)).eval env = BitVec.ofNat 64 (16 * e) := by
  rw [Arrays.eval_shl_lit _ (by decide), eval_reg, henv]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, h, toNat_ofNat_lt (by omega)]
  omega

/-- **The last pair** copied, and the return. -/
theorem tail (hp : Placed code k) {m0 : MachineData} (hpre : LanesOfPre m0)
    (h0 : (reg m0 .rdi).toNat ≠ 0) {e : Nat} {st : MachineData} (hT : CpTail m0 e st) :
    Eventually (step1 Host.exe) (Post m0) ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.LanesOf.b15Offset)⟩ := by
  have hb := hT.body
  have he := hT.he
  have hn := hT.hn
  have hl : lenOf m0 = (reg m0 .rdx).toNat := rfl
  have hnn : nOf m0 = lenOf m0 / 2 := rfl
  have hwf : (envT m0 st e).WF := wf3 hpre hb.fr.kept (by omega) (by omega) (by omega) (by omega)
  have hsh := shl4_eval (env := envT m0 st e) hT.rdi (by omega) rfl
  have hm : Match (envT m0 st e) tailS st := by
    refine match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hb.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨?_, ?_, trivial⟩
    · dsimp only
      rw [eval_add, hsh, eval_reg]
      show reg st .rsi + _ = _
      rw [hT.rsi, show 8 * (2 * e) = 16 * e by omega]
      simp
    · dsimp only
      rw [eval_add, hsh, eval_reg]
      show reg st .rcx + _ = _
      rw [hT.rcx]
      simp
  refine exec_then (inf hp b15_in_code (by simp [b15])) run_b15 hwf (by intro l h; cases h) hm
    fun st' hm' hpc ↦ .done _ ?_
  obtain ⟨hepi, hw⟩ := after_eq run_b15 ▸ epi_b15
  obtain ⟨hl0, hl1⟩ := after_eq run_b15 ▸ lane_b15
  obtain ⟨hs, hrsp⟩ := Transcript.Frame.epilogue hb.fr hwf hm' hepi
  obtain ⟨hc, hso⟩ := same_lanes hpre hb.same hwf hm' hw le_rfl (by omega)
  have hlane : NativeRustcVm.EWAt st'.data.dmem (outOf m0 + BitVec.ofNat 64 (16 * e))
      (pairL m0 e) := by
    have := ewAt_write hm' (r := 2) (o := 0) rfl (by omega) hl0 hl1
    have e0 := load_row (env := envT m0 st e) (r := 1) (o := 2 * e) (t := 0) hpre hb.same rfl rfl
      (by omega)
    have e1 := load_row (env := envT m0 st e) (r := 1) (o := 2 * e) (t := 1) hpre hb.same rfl rfl
      (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at e0 e1
    rw [show (Sym.load 1 0 8).eval (envT m0 st e) = (envT m0 st e).load 1 0 8 from rfl,
      show (Sym.load 1 8 8).eval (envT m0 st e) = (envT m0 st e).load 1 8 8 from rfl, e0, e1,
      Arrays.add_ofNat_zero] at this
    exact this
  have hls : Lanes m0 (pairL m0) (e + 1) st'.data :=
    hb.lanes.extend (w := 1) (pre_out hpre).1.2 (by omega) hso fun t ht ↦ by
      obtain rfl : t = 0 := by omega
      simpa using hlane
  obtain ⟨hsz, hf⟩ := lanes_pair h0
  refine ⟨?_, hrsp, post_some hc hs hls (hsz.trans he.symm) hf (by omega) ?_ ?_⟩
  · simp only [PcOk] at hpc
    rw [hpc]
    exact Transcript.Frame.load_ret hb.fr (pre_stack hpre) le_rfl
  · exact (hm'.regs .rax _ rfl).trans hT.rax
  · exact (congrArg BitVec.toNat (hm'.regs .rdx _ rfl)).trans (hT.rdx.trans he.symm)

/-! ## The loop -/

/-- The loop turn's environment: the frame, the row's pairs `2j`, `2j + 1`, their lanes. -/
abbrev envB (m0 st : MachineData) (j : Nat) : Env :=
  frameEnv m0 st 8 [(rowOf m0 + BitVec.ofNat 64 (8 * (4 * j)), 32),
    (outOf m0 + BitVec.ofNat 64 (16 * (2 * j)), 32)]

/-- **A turn of the loop**: two lanes, back at the head, or on to the end. -/
theorem cp_turn (hp : Placed code k) {m0 : MachineData} (hpre : LanesOfPre m0)
    (h0 : (reg m0 .rdi).toNat ≠ 0) {j : Nat} {st : MachineData} (hL : CpLoop m0 j st) :
    Eventually (step1 Host.exe) (fun s ↦ Post m0 s ∨ (CpLoop m0 (j + 1) s.data ∧
      s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LanesOf.b13Offset))) ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.LanesOf.b13Offset)⟩ := by
  have hb := hL.body
  have hj := hL.hj
  have hn := hL.hn
  have hl : lenOf m0 = (reg m0 .rdx).toNat := rfl
  have hn' : nOf m0 = lenOf m0 / 2 := rfl
  have hwf : (envB m0 st j).WF := wf3 hpre hb.fr.kept (by omega) (by omega) (by omega) (by omega)
  have hm : Match (envB m0 st j) headB st := by
    refine match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hb.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨?_, ?_, trivial⟩
    · dsimp only
      rw [eval_add, eval_reg, eval_reg]
      show reg st .rsi + reg st .r10 = _
      rw [hL.rsi, hL.r10, show 32 * j + 24 = 8 * (4 * j) + 24 by omega]
      exact add_ofNat_ofInt _ _ 24
    · dsimp only
      rw [eval_add, eval_reg, eval_reg]
      show reg st .rcx + reg st .r10 = _
      rw [hL.rcx, hL.r10, show 32 * j + 24 = 16 * (2 * j) + 24 by omega]
      exact add_ofNat_ofInt _ _ 24
  refine exec_then (inf hp b13_in_code (by simp [b13])) run_b13 hwf (by intro l h; cases h) hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hw⟩ := after_eq run_b13 ▸ mid_b13
  obtain ⟨hl0, hl1, hl2, hl3⟩ := after_eq run_b13 ▸ lane_b13
  obtain ⟨hc, hso⟩ := same_lanes hpre hb.same hwf hm1 hw le_rfl (by omega)
  have hld : ∀ t, t < 4 → UInt64.ofBitVec ((Sym.load 1 (8 * t) 8).eval (envB m0 st j)) =
      rowW m0 (4 * j + t) := fun t ht ↦
    load_row (env := envB m0 st j) (r := 1) (o := 4 * j) (t := t) hpre hb.same rfl rfl (by omega)
  have hla : NativeRustcVm.EWAt st1.data.dmem (outOf m0 + BitVec.ofNat 64 (16 * (2 * j)))
      (pairL m0 (2 * j)) := by
    have := ewAt_write hm1 (r := 2) (o := 0) rfl (by omega) hl0 hl1
    rw [show (Sym.load 1 0 8) = Sym.load 1 (8 * 0) 8 from rfl,
      show (Sym.load 1 8 8) = Sym.load 1 (8 * 1) 8 from rfl, hld 0 (by omega),
      hld 1 (by omega), Arrays.add_ofNat_zero] at this
    rwa [pairL, show 2 * (2 * j) = 4 * j + 0 by omega, show 4 * j + 0 + 1 = 4 * j + 1 by omega]
  have hlb : NativeRustcVm.EWAt st1.data.dmem (outOf m0 + BitVec.ofNat 64 (16 * (2 * j + 1)))
      (pairL m0 (2 * j + 1)) := by
    have := ewAt_write hm1 (r := 2) (o := 16) rfl (by omega) hl2 hl3
    rw [show (Sym.load 1 16 8) = Sym.load 1 (8 * 2) 8 from rfl,
      show (Sym.load 1 24 8) = Sym.load 1 (8 * 3) 8 from rfl, hld 2 (by omega),
      hld 3 (by omega), addr_add, show 16 * (2 * j) + 16 = 16 * (2 * j + 1) by omega] at this
    rwa [pairL, show 2 * (2 * j + 1) = 4 * j + 2 by omega, show 4 * j + 2 + 1 = 4 * j + 3 by omega]
  have hls : Lanes m0 (pairL m0) (2 * (j + 1)) st1.data := by
    have := hb.lanes.extend (w := 2) (pre_out hpre).1.2 (by omega) hso fun t ht ↦ by
      rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
      · simpa using hla
      · simpa using hlb
    rwa [show 2 * j + 2 = 2 * (j + 1) by omega] at this
  have hb1 : Body m0 (pairL m0) (2 * (j + 1)) st1.data :=
    ⟨Transcript.Frame.of_block hb.fr hwf hm1 hmid slots_le, hc, hls⟩
  have hrdi : (reg st1.data .rdi).toNat = 2 * (j + 1) := by
    rw [show reg st1.data .rdi = _ from hm1.regs .rdi _ rfl, eval_add, eval_lit, eval_reg]
    show (BitVec.ofNat 64 2 + reg st .rdi).toNat = _
    rw [toNat_add_lit (by rw [hL.rdi]; omega), hL.rdi]
    omega
  have hr9 : reg st1.data .r9 = reg st .r9 := hm1.regs .r9 _ rfl
  simp only [PcOk] at hpc1
  have hc1 : (SBool.not (.cmp .eq .W64 (.reg .r9) (.bin .add .W64 (.lit 2) (.reg .rdi)))).eval
      (envB m0 st j) = decide (2 * (j + 1) ≠ 2 * (nOf m0 / 2)) := by
    rw [Arrays.eval_not, Arrays.eval_cmp_eq, eval_add, eval_lit, eval_reg, eval_reg]
    show (!(reg st .r9 == BitVec.ofNat 64 2 + reg st .rdi)) = _
    rw [bv_beq_toNat, toNat_add_lit (by rw [hL.rdi]; omega), hL.rdi, hL.r9]
    by_cases h : 2 * (j + 1) = 2 * (nOf m0 / 2)
    · simp [h]; omega
    · simp [h]; omega
  rw [hc1] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases hmore : 2 * (j + 1) ≠ 2 * (nOf m0 / 2)
  · -- back at the head
    have hpc := (hT (decide_eq_true hmore)).trans (hp.label NativeRustcVmX64.Vm.LanesOf.label_16_at)
    refine .done _ (.inr ⟨⟨hb1, by omega, hn, (hm1.regs .rsi _ rfl).trans hL.rsi,
      (hm1.regs .rcx _ rfl).trans hL.rcx, hrdi, ?_, hr9 ▸ hL.r9,
      (congrArg BitVec.toNat (hm1.regs .r8 _ rfl)).trans hL.r8,
      (hm1.regs .rax _ rfl).trans hL.rax,
      (congrArg BitVec.toNat (hm1.regs .rdx _ rfl)).trans hL.rdx⟩, hpc⟩)
    rw [show reg st1.data .r10 = _ from hm1.regs .r10 _ rfl, eval_add, eval_lit, eval_reg]
    show BitVec.ofNat 64 32 + reg st .r10 = _
    rw [hL.r10, ← BitVec.ofNat_add]
    congr 1
    omega
  · -- `b14`: an even count returns, an odd one copies the last pair
    have hpc := hF fun h ↦ hmore (of_decide_eq_true h)
    simp only [show k + NativeRustcVmX64.Vm.LanesOf.b13Offset + b13.length = k + NativeRustcVmX64.Vm.LanesOf.b14Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LanesOf.b13_next]] at hpc
    have hwf1 := wf1 (st := st1.data) (vars := fun _ ↦ 0) (ret := 0) hpre hb1.fr.kept
    have hm2 : Match (frameEnv m0 st1.data 8 [] (fun _ ↦ 0) 0) midS0 st1.data :=
      match_ofMachine ⟨rfl, trivial⟩ ⟨hb1.fr.rsp_eval, trivial⟩ trivial trivial trivial
    refine exec_at (inf hp b14_in_code (by simp [b14])) run_b14 hwf1 (by intro l h; cases h) hpc
      hm2 fun st2 hm2' hpc2 ↦ Eventually.mono ?_ fun _ h ↦ .inl h
    obtain ⟨hmid2, hmem2⟩ := after_eq run_b14 ▸ mid_b14
    have hd2 : st2.data.dmem = st1.data.dmem := hm2'.dmem_eq hwf1 hmem2
    have hb2 : Body m0 (pairL m0) (2 * (j + 1)) st2.data :=
      ⟨Transcript.Frame.of_block hb1.fr hwf1 hm2' hmid2 slots_le,
        fun p hp ↦ by rw [hd2]; exact hb1.same p hp, hb1.lanes.of_dmem hd2⟩
    have hr8 : (reg st1.data .r8).toNat = lenOf m0 :=
      (congrArg BitVec.toNat (hm1.regs .r8 _ rfl)).trans hL.r8
    simp only [PcOk, SBool.eval, Sym.eval, Env.ofMachine_regs] at hpc2
    simp only [testb2 _ (by rw [hr8]; exact hn)] at hpc2
    obtain ⟨hT2, hF2⟩ := pc_cond hpc2
    have hrax : reg st2.data .rax = 1#64 :=
      (hm2'.regs .rax _ rfl).trans ((hm1.regs .rax _ rfl).trans hL.rax)
    have hrdx : (reg st2.data .rdx).toNat = nOf m0 :=
      (congrArg BitVec.toNat (hm2'.regs .rdx _ rfl)).trans
        ((congrArg BitVec.toNat (hm1.regs .rdx _ rfl)).trans hL.rdx)
    obtain ⟨hsz, hf⟩ := lanes_pair h0
    by_cases hev : lenOf m0 / 2 % 2 = 0
    · have hpc' := (hT2 (decide_eq_true (by rw [hr8]; exact hev))).trans
        (hp.label NativeRustcVmX64.Vm.LanesOf.label_14_at)
      have hcnt : 2 * (j + 1) = nOf m0 := by omega
      exact at_pc (P := fun d ↦ d = st2.data) (fun d hd ↦ hd ▸ done hp hpre hb2
        (hsz.trans hcnt.symm) hf (by omega) hrax (hrdx.trans hcnt.symm)) ⟨rfl, hpc'⟩
    · have hpc' := hF2 fun h ↦ hev (by rw [← hr8]; exact of_decide_eq_true h)
      simp only [show k + NativeRustcVmX64.Vm.LanesOf.b14Offset + b14.length = k + NativeRustcVmX64.Vm.LanesOf.b15Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LanesOf.b14_next]] at hpc'
      exact at_pc (P := fun d ↦ d = st2.data) (fun d hd ↦ hd ▸ tail hp hpre h0
        ⟨hb2, by omega, hn, (hm2'.regs .rsi _ rfl).trans ((hm1.regs .rsi _ rfl).trans hL.rsi),
          (hm2'.regs .rcx _ rfl).trans ((hm1.regs .rcx _ rfl).trans hL.rcx),
          (congrArg BitVec.toNat (hm2'.regs .rdi _ rfl)).trans hrdi, hrax, hrdx⟩) ⟨rfl, hpc'⟩

/-! ## From the entry -/

/-- **A later level**: from `b1`, the entry's environment. -/
theorem pairs (hp : Placed code k) {m0 : MachineData} (hpre : LanesOfPre m0)
    (h0 : (reg m0 .rdi).toNat ≠ 0) {st : MachineState}
    (hm : Match (frameEnv m0 m0 8 []) s0 st.data) (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LanesOf.b1Offset)) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hwf := wf1 (st := m0) (vars := fun _ ↦ 0) (ret := 0) hpre fun _ h ↦ h
  have hl : lenOf m0 = (reg m0 .rdx).toNat := rfl
  have hn' : nOf m0 = lenOf m0 / 2 := rfl
  have hx : ∀ r, (frameEnv m0 m0 8 []).regs r = reg m0 r := fun _ ↦ rfl
  obtain ⟨hsz, hf⟩ := lanes_pair h0
  refine exec_at (inf hp b1_in_code (by simp [b1])) run_b1 hwf (by intro l h; cases h) hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, hx,
    ult_lit _ (by decide : 130 < 2 ^ 64)] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases h130 : lenOf m0 < 130
  · have hpc1 := hF (by simpa using h130)
    refine exec_at (inf hp b2_in_code (by simp [b2])) (exec_after run_b1 run_b2) hwf
      (by intro l h; cases h) hpc1 hm1 fun st2 hm2 hpc2 ↦ ?_
    simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, hx] at hpc2
    rw [bv_beq_ofNat _ (by decide), toNat_shr1] at hpc2
    obtain ⟨hT2, hF2⟩ := pc_cond hpc2
    by_cases hz : lenOf m0 / 2 = 0
    · -- no pair: `b10`
      have hpc2 := (hT2 (decide_eq_true hz)).trans (hp.label NativeRustcVmX64.Vm.LanesOf.label_14_at)
      refine exec_at (inf hp b10_in_code (by simp [b10])) (exec_after run_b2 run_b10z) hwf
        (by intro l h; cases h) hpc2 hm2 fun st3 hm3 hpc3 ↦ ?_
      obtain ⟨he, hw⟩ := after_eq run_b10z ▸ epi_b10z
      obtain ⟨hpc', hrsp, hc, hs⟩ := chain_ret hpre hm3 hpc3 he hw
      refine .done _ ⟨hpc', hrsp, post_some hc hs (lanes_zero _) (hsz.trans hz) hf (by omega)
        (hm3.regs .rax _ rfl) ?_⟩
      rw [show reg st3.data .rdx = _ from hm3.regs .rdx _ rfl]
      exact (toNat_shr1 _).trans hz
    · have hpc2 := hF2 fun h ↦ hz (of_decide_eq_true h)
      refine exec_at (inf hp b3_in_code (by simp [b3])) (exec_after run_b2 run_b3) hwf
        (by intro l h; cases h) hpc2 hm2 fun st3 hm3 hpc3 ↦ ?_
      simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, hx] at hpc3
      rw [bv_beq_ofNat _ (by decide), toNat_shr1] at hpc3
      obtain ⟨hT3, hF3⟩ := pc_cond hpc3
      have hrdx : ∀ {S : SState} {d : MachineData}, Match (frameEnv m0 m0 8 []) S d →
          S.reg .rdx = some (.bin .shr .W64 (.reg .rdx) (.lit 1)) → (reg d .rdx).toNat = nOf m0 :=
        fun hmd h ↦ by rw [show reg _ .rdx = _ from hmd.regs .rdx _ h]; exact toNat_shr1 _
      by_cases h1 : lenOf m0 / 2 = 1
      · -- one pair: `b4`, the tail
        have hpc3 := hF3 (by simpa using h1)
        refine exec_at (inf hp b4_in_code (by simp [b4])) (exec_after run_b3 run_b4) hwf
          (by intro l h; cases h) hpc3 hm3 fun st4 hm4 hpc4 ↦ ?_
        simp only [PcOk, hp.label NativeRustcVmX64.Vm.LanesOf.label_13_at] at hpc4
        obtain ⟨hpro, hw⟩ := after_eq run_b4 ▸ pro_b4
        have hfr := Transcript.Frame.of_prologue Transcript.Frame.entry hwf hm4 hpro slots_le
          slots_cs
        exact at_pc (P := fun d ↦ d = st4.data) (fun d hd ↦ hd ▸ tail hp hpre h0
          ⟨⟨hfr, chain_same hpre hm4 hw, lanes_zero _⟩, by omega, h130, hm4.regs .rsi _ rfl,
            hm4.regs .rcx _ rfl, by rw [show reg st4.data .rdi = _ from hm4.regs .rdi _ rfl]; rfl,
            hm4.regs .rax _ rfl, hrdx hm4 rfl⟩) ⟨rfl, hpc4⟩
      · -- the loop: `b12`
        have hpc3 := (hT3 (by simpa using h1)).trans (hp.label NativeRustcVmX64.Vm.LanesOf.label_15_at)
        refine exec_at (inf hp b12_in_code (by simp [b12])) (exec_after run_b3 run_b12) hwf
          (by intro l h; cases h) hpc3 hm3 fun st4 hm4 hpc4 ↦ ?_
        simp only [PcOk, show k + NativeRustcVmX64.Vm.LanesOf.b12Offset + b12.length = k + NativeRustcVmX64.Vm.LanesOf.b13Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LanesOf.b12_next]] at hpc4
        obtain ⟨hpro, hw⟩ := after_eq run_b12 ▸ pro_b12
        have hfr := Transcript.Frame.of_prologue Transcript.Frame.entry hwf hm4 hpro slots_le
          slots_cs
        have hL : CpLoop m0 0 st4.data := by
          refine ⟨⟨hfr, chain_same hpre hm4 hw, lanes_zero _⟩, by omega, h130,
            hm4.regs .rsi _ rfl, hm4.regs .rcx _ rfl,
            by rw [show reg st4.data .rdi = _ from hm4.regs .rdi _ rfl]; rfl,
            hm4.regs .r10 _ rfl, ?_, ?_, hm4.regs .rax _ rfl, hrdx hm4 rfl⟩
          · rw [show reg st4.data .r9 = _ from hm4.regs .r9 _ rfl]
            show (BinOp.apply .and .W32 (UnOp.apply .trunc .W32
              (BinOp.apply .shr .W64 (reg m0 .rdx) (BitVec.ofNat 64 1))) (BitVec.ofNat 64 126)).toNat = _
            rw [and126 _ (by rw [toNat_shr1]; omega), toNat_shr1]
          · exact congrArg BitVec.toNat (hm4.regs .r8 _ rfl)
        exact at_pc (fun d hd ↦ run_loop (L := CpLoop m0) (nOf m0 / 2) (fun i _ h ↦ h.hj)
          (fun i d hd ↦ cp_turn hp hpre h0 hd) hd) ⟨hL, hpc4⟩
  · -- past 129 words: `b11`
    have hpc1 := (hT (by simpa using h130)).trans (hp.label NativeRustcVmX64.Vm.LanesOf.label_2_at)
    refine exec_at (inf hp b11_in_code (by simp [b11])) (exec_after run_b1 run_b11p) hwf
      (by intro l h; cases h) hpc1 hm1 fun st2 hm2 hpc2 ↦ ?_
    obtain ⟨he, hw⟩ := after_eq run_b11p ▸ epi_b11p
    obtain ⟨hpc', hrsp, hc, hs⟩ := chain_ret hpre hm2 hpc2 he hw
    exact .done _ ⟨hpc', hrsp, post_none hc hs (by rw [hsz]; omega) (hm2.regs .rax _ rfl)⟩

end

end NativeRustcVmX64.Whir.LanesOf
