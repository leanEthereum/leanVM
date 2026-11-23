module

public import NativeRustcVmX64.Whir.FinalLevel.Steps
public import NativeRustcVm.Sumcheck.RoundPoly
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names

/-!
# `final_level`: the entry and the folded scalars (x86-64)

`b0` saves the callee-saved registers, keeps the level (RBP) and its rate exponent (RBX); `b1`
zeroes the folded scalars' buffer (`zero_loop`); `b2` and `b3` check `μ < 64` and `2 ^ μ` plus the
level's fold at most `64` (both pass under the precondition), keep `μ` at `40`, `2 ^ μ` (R14) and
the count (R13); `b4` keeps the index (R15), the `TState` (R12), `laneFolds` (`48`), the basis
(`56`) and calls `read_scalars(t, sp + 1600, 2 ^ μ + fold)`; `b5` tests it (`entry`, to `b6` with
`Live`). `Live` is kept by blocks and calls that keep its registers and frame words
(`Live.keep`).
-/

namespace NativeRustcVmX64.Whir.Levels.FL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.FinalLevel

@[expose] public section

/-- **After `read_scalars`**: the frame, the words and registers the rest reads, the folded
scalars at `1600`. -/
structure Live (level : Whir.Level) (m0 d : MachineData) (folded : Array EW) : Prop where
  fr : Fr m0 40 d
  w40 : NativeRustcVm.WordAt d.dmem (loc m0 40) (.ofBitVec (reg m0 .rcx))
  w48 : NativeRustcVm.WordAt d.dmem (loc m0 48) (.ofBitVec (reg m0 .r8))
  w56 : NativeRustcVm.WordAt d.dmem (loc m0 56) (.ofBitVec (reg m0 .r9))
  r12 : reg d .r12 = tA m0
  r13 : (reg d .r13).toNat = 2 ^ mu m0 + level.fold
  r14 : (reg d .r14).toNat = 2 ^ mu m0
  r15 : reg d .r15 = reg m0 .rsi
  size : folded.size = 2 ^ mu m0 + level.fold
  fold : NativeRustcVm.EWsAt d.dmem (loc m0 1600) folded.toList

end

public section

theorem level_words {d : Mem 64} {p : BitVec 64} {l : Whir.Level} (h : LevelAt d p l) :
    NativeRustcVm.WordAt d (off p 0) l.fold.toUInt64 ∧
      NativeRustcVm.WordAt d (off p 8) l.logInvRate.toUInt64 ∧
      NativeRustcVm.WordAt d (off p 16) l.queries.toUInt64 := by
  obtain ⟨-, -, -, hw⟩ := h
  rw [NativeRustcVm.wordsAt_cons_iff, NativeRustcVm.wordsAt_cons_iff,
    NativeRustcVm.wordsAt_singleton_iff] at hw
  refine ⟨by rw [off_zero]; exact hw.1, hw.2.1, ?_⟩
  have := hw.2.2
  rwa [NativeRustcVm.addr_add_add] at this

theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toBitVec.toNat = n := by
  show (BitVec.ofNat 64 n).toNat = n
  rw [BitVec.toNat_ofNat]; omega

theorem not_hi {x c : BitVec 64} (h : x.toNat ≤ c.toNat) : (!x.ult c && !(x == c)) = false := by
  rcases Nat.lt_or_eq_of_le h with hlt | heq
  · have : x.ult c = true := by simp [BitVec.ult, hlt]
    simp [this]
  · simp [BitVec.eq_of_toNat_eq heq]

/-- Bytes of the frame kept byte by byte. -/
theorem bytes_keep {m0 d d' : MachineData} {j : Nat} {bs : List UInt8}
    (hk : ∀ i < bs.length, d'.dmem.get? (loc m0 (j + i)) = d.dmem.get? (loc m0 (j + i)))
    (h : NativeRustcVm.BytesAt d.dmem (loc m0 j) bs) :
    NativeRustcVm.BytesAt d'.dmem (loc m0 j) bs := by
  intro i hi
  have := h i hi
  rw [off_add] at this ⊢
  rw [hk i hi]
  exact this

/-- A frame byte a block in `argEnv` does not write. -/
theorem get_blk [Labels] {m0 d d' : MachineData} {rest : List (BitVec 64 × Nat)} {S : SState}
    {ret : BitVec 64} (hwf : (argEnv m0 d 2672 8 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (argEnv m0 d 2672 8 rest (fun _ ↦ 0) ret) S d')
    (hin : writesIn S = true) {rs : List (Nat × Nat)} (hW : Wr rs S) {j : Nat} (hj : j < 2688)
    (hmiss : ∀ p ∈ rs, p.2 ≤ j ∨ j < p.1) :
    d'.dmem.get? (loc m0 j) = d.dmem.get? (loc m0 j) := by
  refine hm.get?_mem0 hwf (not_written0A hwf hm hin hj fun w hw _ ↦ ?_)
  obtain ⟨-, p, hp, h1, h2⟩ := hW w hw
  rcases hmiss p hp with h' | h'
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- `Live` kept: the frame, its registers and the frame's bytes `40` to `64` and `1600` to
`2624`. -/
theorem Live.keep {level : Whir.Level} {m0 d d' : MachineData} {folded : Array EW}
    (h : Live level m0 d folded) (hf : Fr m0 40 d')
    (hr : ∀ r ∈ [Reg64.r12, .r13, .r14, .r15], reg d' r = reg d r)
    (hk : ∀ j, (40 ≤ j ∧ j < 64) ∨ (1600 ≤ j ∧ j < 2624) →
      d'.dmem.get? (loc m0 j) = d.dmem.get? (loc m0 j)) (h64 : 2 ^ mu m0 + level.fold ≤ 64) :
    Live level m0 d' folded where
  fr := hf
  w40 := bytes_keep (fun i hi ↦ hk _ (Or.inl (by rw [NativeRustcVm.length_wordBytes] at hi; omega))) h.w40
  w48 := bytes_keep (fun i hi ↦ hk _ (Or.inl (by rw [NativeRustcVm.length_wordBytes] at hi; omega))) h.w48
  w56 := bytes_keep (fun i hi ↦ hk _ (Or.inl (by rw [NativeRustcVm.length_wordBytes] at hi; omega))) h.w56
  r12 := (hr .r12 (by simp)).trans h.r12
  r13 := by rw [hr .r13 (by simp)]; exact h.r13
  r14 := by rw [hr .r14 (by simp)]; exact h.r14
  r15 := (hr .r15 (by simp)).trans h.r15
  size := h.size
  fold := bytes_keep (fun i hi ↦ hk _ (Or.inr (by
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList, h.size] at hi; omega))) h.fold

theorem cMu_eval [Labels] (env : Env) (h : (env.regs .rcx).toNat < 64) : cMu.eval env = false := by
  simp only [cMu, SBool.eval, Sym.eval, CmpOp.apply, low_W64]
  exact not_hi (by simp; omega)

theorem s14_toNat [Labels] (env : Env) (h : (env.regs .rcx).toNat < 64) :
    (s14.eval env).toNat = 2 ^ (env.regs .rcx).toNat := by
  simp only [s14, Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  have hs : shiftCount .W64 (env.regs .rcx) = (env.regs .rcx).toNat := by
    unfold shiftCount shiftMask low
    rw [BitVec.toNat_setWidth, show (Width.W8).bits = 8 from rfl,
      show (0x3f : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [hs, Nat.shiftLeft_eq]
  have : 2 ^ (env.regs .rcx).toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) h
  rw [show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl]
  omega

theorem s13_toNat [Labels] (env : Env) (h : (env.regs .rcx).toNat < 64) {f : Nat}
    (hl : env.load 1 0 8 = f.toUInt64.toBitVec) (hf : 2 ^ (env.regs .rcx).toNat + f ≤ 64) :
    (s13.eval env).toNat = 2 ^ (env.regs .rcx).toNat + f := by
  have h14 := s14_toNat env h
  have hft : f.toUInt64.toBitVec.toNat = f := toNat_toUInt64 (by omega)
  show (BinOp.apply .add .W64 (s14.eval env) (env.load 1 0 8)).toNat = _
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, hl, h14, hft]
  omega

theorem cSize_eval [Labels] (env : Env) (h : (env.regs .rcx).toNat < 64) {f : Nat}
    (hl : env.load 1 0 8 = f.toUInt64.toBitVec) (hf : 2 ^ (env.regs .rcx).toNat + f ≤ 64) :
    cSize.eval env = false := by
  have h13 := s13_toNat env h hl hf
  have h14 := s14_toNat env h
  have c1 : CmpOp.apply .ult .W64 (s13.eval env) (BitVec.ofNat 64 65) = true := by
    show (s13.eval env).ult (BitVec.ofNat 64 65) = true
    rw [BitVec.ult, h13, show (BitVec.ofNat 64 65).toNat = 65 from rfl]
    exact decide_eq_true (by omega)
  have c2 : CmpOp.apply .ult .W64 (s13.eval env) (s14.eval env) = false := by
    show (s13.eval env).ult (s14.eval env) = false
    rw [BitVec.ult, h13, h14]
    exact decide_eq_false (by omega)
  simp only [cSize, SBool.eval, Sym.eval, c1, c2, Bool.not_true, Bool.false_eq_true, ite_false]
  simp only [CmpOp.apply, BinOp.apply, low8_merge]
  decide

/-- A block's writes `rs` all below `hi`. -/
theorem Wr.le {rs : List (Nat × Nat)} {S : SState} (h : Wr rs S) {hi : Nat}
    (hrs : ∀ p ∈ rs, p.2 ≤ hi) : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ hi := fun w hw ↦ by
  obtain ⟨h0, p, hp, -, h2⟩ := h w hw
  exact ⟨h0, Nat.le_trans h2 (hrs p hp)⟩

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData}

namespace Ctx

variable (c : Ctx a s level ba b w rounds m0)
include c

/-- The frame (without the argument word) and the level. -/
theorem wfL {d : MachineData} (hk : Kept m0.dmem d.dmem) {ret : BitVec 64} :
    (frameEnv m0 d 2672 [(lA m0, 24)] (fun _ ↦ 0) ret).WF := by
  have g := c.geo
  have hf := c.fa_toNat
  refine frame_wf ⟨(c.region_ok hk).1.mono (by omega), (c.region_ok hk).2.mono (by omega)⟩
    (fun y hy ↦ ?_) (List.pairwise_pair.mpr ?_)
  · rw [List.mem_singleton] at hy; subst hy
    exact ⟨Mapped.keeps c.lin.1.1 hk, c.lin.1.2⟩
  · show (fa m0).toNat + (2672 + 8) ≤ (lA m0).toNat ∨ (lA m0).toNat + 24 ≤ (fa m0).toNat
    rw [hf]; have := g.lS; have := g.hN; omega

/-- **A body block in `frameEnv`** keeps the frame; it writes the frame below `hi ≤ 2624`. -/
theorem blkF {o o' : Nat} {d d' : MachineData} {rest : List (BitVec 64 × Nat)} {S : SState}
    {ret : BitVec 64} (hf : Fr m0 o d) (hwf : (frameEnv m0 d 2672 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 2672 rest (fun _ ↦ 0) ret) S d')
    (hmid : MidOk 2672 o' slots S = true)
    {hi : Nat} (hhi : hi ≤ 2624) (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ hi) :
    Fr m0 o' d' ∧ NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fa m0) hi) := by
  have hs : NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fa m0) hi) :=
    sameOutside_low hwf hm (r := 0) rfl (by omega) hw
  refine ⟨⟨Frame.of_block hf.frame hwf hm hmid slots_le, NativeRustcVm.SameOutside.mono
    (hf.same.trans hs) fun q hq ↦ ?_⟩, hs⟩
  rcases hq with hq | hq
  · exact hq
  · left
    obtain ⟨j, hj, rfl⟩ := NativeRustcVm.InRange.exists hq
    exact c.loc_stk (j := j) (by omega)

end Ctx

end

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The entry and the folded scalars**: `b0` to `b5`, to `b6` with `Live`. -/
theorem entry (hp : Placed code k) (c : Ctx a s level ba b w rounds m0)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (cont : ∀ (st : MachineState) (folded : Array EW) (s1 : TState),
      st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b6Offset) → Live level m0 st.data folded →
      reg st.data .rbx = level.logInvRate.toUInt64.toBitVec → reg st.data .rbp = lA m0 →
      TStateAt st.data.dmem (tA m0) a s1 →
      runF level b w rounds m0 s = (C1 (reg m0 .rsi).toNat level (mu m0) (reg m0 .r8).toNat b w
        rounds folded).run s1 →
      Eventually (step1 Host.exe) (Goal a s level b w rounds m0) st) :
    Eventually (step1 Host.exe) (Goal a s level b w rounds m0) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b0Offset)⟩ := by
  have g := c.geo
  have hfo : 2 ^ mu m0 + level.fold ≤ 64 := c.fold
  have hmu : mu m0 < 64 := c.mu64
  have hlw := level_words c.lv
  -- `b0`: the prologue.
  let env0 := frameEnv m0 m0 2672 [(lA m0, 24)] (fun _ ↦ 0) 0
  have hwf0 : env0.WF := c.wfL (fun _ h ↦ h)
  have hm0 : Match env0 entryS m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial trivial
      trivial
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 nofun hm0
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hw, hrax, hrbx, hrbp, hkr⟩ := ok_b0
  have hfr : Frame m0 2672 slots 40 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le slots_cs
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (fa m0) 2672) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by omega) hw
  have hf1 : Fr m0 40 st1.data := ⟨hfr, NativeRustcVm.SameOutside.mono hs1 fun q hq ↦ by
    obtain ⟨j, hj, rfl⟩ := NativeRustcVm.InRange.exists hq
    exact Or.inl (c.loc_stk (j := j) hj)⟩
  have e1 : ∀ {r : Reg64} {v : Sym}, (after b0 entryS).reg r = some v →
      reg st1.data r = v.eval env0 := fun h ↦ hm1.regs _ _ h
  have hk1 : ∀ r ∈ [Reg64.rcx, .rsi, .rdi, .r8, .r9, .r12, .r13, .r14, .r15],
      reg st1.data r = reg m0 r := fun r hr ↦ e1 (hkr r hr)
  have hbx1 : reg st1.data .rbx = level.logInvRate.toUInt64.toBitVec :=
    (e1 hrbx).trans (load_ofMachine (o := 8) (r := 1) rfl hlw.2.1)
  have hbp1 : reg st1.data .rbp = lA m0 := (e1 hrbp).trans (eval_ptr rfl)
  simp only [PcOk] at hpc1
  rw [show k + NativeRustcVmX64.Vm.FinalLevel.b0Offset + b0.length = k + NativeRustcVmX64.Vm.FinalLevel.b1Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.FinalLevel.b0_next]] at hpc1
  -- `b1`: the zeroing loop.
  refine Eventually.bind (zero_loop hp c hpc1 hf1 (e1 hrax) hs1) fun st2 ⟨hf2, hr2, hd2, hpc2⟩ ↦ ?_
  have hk2 : ∀ r ∈ [Reg64.rcx, .rsi, .rdi, .r8, .r9, .r12, .r13, .r14, .r15],
      reg st2.data r = reg m0 r := fun r hr ↦
    (hr2 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide)).trans (hk1 r hr)
  have hbx2 : reg st2.data .rbx = level.logInvRate.toUInt64.toBitVec :=
    (hr2 .rbx (by decide)).trans hbx1
  have hbp2 : reg st2.data .rbp = lA m0 := (hr2 .rbp (by decide)).trans hbp1
  have hts2 : TStateAt st2.data.dmem (tA m0) a s :=
    c.ts_frame (hi := 2672) le_rfl hf2.frame.kept hd2 c.ts
  -- `b2`: `μ < 64`.
  refine Eventually.bind (cond_spec hp c b2_in_code (by simp [b2]) exit_b2 ok_b2 hf2 hpc2)
    fun st3 ⟨hr3, hd3, hpc3⟩ ↦ ?_
  have hcx2 : (reg st2.data .rcx).toNat < 64 := by rw [hk2 .rcx (by simp)]; exact hmu
  rw [cMu_eval _ hcx2] at hpc3
  simp only [Bool.false_eq_true, ite_false] at hpc3
  rw [show k + NativeRustcVmX64.Vm.FinalLevel.b2Offset + b2.length = k + NativeRustcVmX64.Vm.FinalLevel.b3Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.FinalLevel.b2_next]] at hpc3
  have hf3 := hf2.congr hr3 hd3
  have hk3 : ∀ r ∈ [Reg64.rcx, .rsi, .rdi, .r8, .r9, .r12, .r13, .r14, .r15],
      reg st3.data r = reg m0 r := fun r hr ↦ (hr3 r).trans (hk2 r hr)
  have hts3 : TStateAt st3.data.dmem (tA m0) a s := by rw [hd3]; exact hts2
  -- `b3`: `2 ^ μ` plus the fold at most `64`.
  let env3 := frameEnv m0 st3.data 2672 [(lA m0, 24)] (fun _ ↦ 0) 0
  have hwf3 : env3.WF := c.wfL hf3.frame.kept
  have hbp3 : reg st3.data .rbp = lA m0 := (hr3 .rbp).trans hbp2
  have hm3 : Match env3 levelS st3.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf3.frame.rsp_eval, known_ptr rfl hbp3, trivial⟩
      trivial trivial trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf3 nofun hpc3 hm3
    fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid3, hW3, h40, hr14, hr13, hrbp3, hkr3⟩ := ok_b3
  obtain ⟨hf4, hs4⟩ := c.blkF hf3 hwf3 hm4 hmid3 (hi := 48) (by omega)
    (hW3.le (by decide))
  have hrcx3 : reg st3.data .rcx = reg m0 .rcx := hk3 .rcx (by simp)
  have hc3 : (env3.regs .rcx).toNat < 64 := by
    show (reg st3.data .rcx).toNat < 64; rw [hrcx3]; exact hmu
  have hf3' : 2 ^ (env3.regs .rcx).toNat + level.fold ≤ 64 := by
    show 2 ^ (reg st3.data .rcx).toNat + level.fold ≤ 64; rw [hrcx3]; exact hfo
  have hl0 : env3.load 1 0 8 = level.fold.toUInt64.toBitVec :=
    load_ofMachine (o := 0) (r := 1) rfl (level_words (c.level_at hf3.same)).1
  simp only [PcOk] at hpc4
  rw [cSize_eval env3 hc3 hl0 hf3'] at hpc4
  simp only [Bool.false_eq_true, ite_false] at hpc4
  rw [show k + NativeRustcVmX64.Vm.FinalLevel.b3Offset + b3.length = k + NativeRustcVmX64.Vm.FinalLevel.b4Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.FinalLevel.b3_next]] at hpc4
  have e4 : ∀ {r : Reg64} {v : Sym}, (after b3 levelS).reg r = some v →
      reg st4.data r = v.eval env3 := fun h ↦ hm4.regs _ _ h
  have hmu3 : (env3.regs .rcx).toNat = mu m0 := by
    show (reg st3.data .rcx).toNat = _; rw [hrcx3]
  have h14 : (reg st4.data .r14).toNat = 2 ^ mu m0 := by
    rw [e4 hr14, s14_toNat env3 hc3, hmu3]
  have h13 : (reg st4.data .r13).toNat = 2 ^ mu m0 + level.fold := by
    rw [e4 hr13, s13_toNat env3 hc3 hl0 hf3', hmu3]
  have hbp4 : reg st4.data .rbp = lA m0 := (e4 hrbp3).trans (eval_ptr rfl)
  have hk4 : ∀ r ∈ [Reg64.rsi, .rdi, .r8, .r9],
      reg st4.data r = reg m0 r := fun r hr ↦
    (e4 (hkr3 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> simp))).trans
      (hk3 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> simp))
  have hbx4 : reg st4.data .rbx = level.logInvRate.toUInt64.toBitVec :=
    (e4 (hkr3 .rbx (by simp))).trans ((hr3 .rbx).trans hbx2)
  have hw40 : NativeRustcVm.WordAt st4.data.dmem (loc m0 40) (.ofBitVec (reg m0 .rcx)) :=
    wordAt_written hm4 (r := 0) (o := 40) rfl (by omega) h40 (w := .ofBitVec (reg m0 .rcx)) hrcx3
  have hts4 := c.ts_frame (hi := 48) (by omega) (hm4.kept hwf3) hs4 hts3
  -- `b4`: `read_scalars(t, sp + 1600, 2 ^ μ + fold)`.
  let env4 := argEnv m0 st4.data 2672 8 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b5Offset)).toBitVec
  have hwf4 : env4.WF := c.wf0 hf4.frame.kept
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf4 (fun _ _ ↦ rfl) hpc4
    (match_retS hf4) fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hmid4, hW4, h48, h56, hrsi4, hrdx4, hr12, hr15, hkr4⟩ := ok_b4
  obtain ⟨hf5, hs5⟩ := c.blk hf4 hwf4 hm5 hmid4 (hi := 64) (by omega)
    (hW4.le (by decide))
  have e5 : ∀ {r : Reg64} {v : Sym}, (after b4 retS).reg r = some v →
      reg st5.data r = v.eval env4 := fun h ↦ hm5.regs _ _ h
  have hw40' : NativeRustcVm.WordAt st5.data.dmem (loc m0 40) (.ofBitVec (reg m0 .rcx)) :=
    bytes_blk hwf4 hm5 (writesIn_of_mid hmid4) hW4 (by simp [NativeRustcVm.length_wordBytes])
      (by simp only [NativeRustcVm.length_wordBytes]; decide) hw40
  have hw48 : NativeRustcVm.WordAt st5.data.dmem (loc m0 48) (.ofBitVec (reg m0 .r8)) :=
    wordAt_written hm5 (r := 0) (o := 48) rfl (by omega) h48 (w := .ofBitVec (reg m0 .r8))
      (hk4 .r8 (by simp))
  have hw56 : NativeRustcVm.WordAt st5.data.dmem (loc m0 56) (.ofBitVec (reg m0 .r9)) :=
    wordAt_written hm5 (r := 0) (o := 56) rfl (by omega) h56 (w := .ofBitVec (reg m0 .r9))
      (hk4 .r9 (by simp))
  have ht5 : reg st5.data .rdi = tA m0 :=
    (e5 (hkr4 .rdi (by simp))).trans (hk4 .rdi (by simp))
  have hsi5 : reg st5.data .rsi = loc m0 1600 := (e5 hrsi4).trans (eval_ptr0A 1600)
  have hdx5 : (reg st5.data .rdx).toNat = 2 ^ mu m0 + level.fold := by rw [e5 hrdx4]; exact h13
  have h12 : reg st5.data .r12 = tA m0 := (e5 hr12).trans (hk4 .rdi (by simp))
  have h15 : reg st5.data .r15 = reg m0 .rsi := (e5 hr15).trans (hk4 .rsi (by simp))
  have h13' : (reg st5.data .r13).toNat = 2 ^ mu m0 + level.fold := by
    rw [e5 (hkr4 .r13 (by simp))]; exact h13
  have h14' : (reg st5.data .r14).toNat = 2 ^ mu m0 := by
    rw [e5 (hkr4 .r14 (by simp))]; exact h14
  have hbx5 : reg st5.data .rbx = level.logInvRate.toUInt64.toBitVec :=
    (e5 (hkr4 .rbx (by simp))).trans hbx4
  have hbp5 : reg st5.data .rbp = lA m0 := (e5 (hkr4 .rbp (by simp))).trans hbp4
  have hts5 := c.ts_frame (hi := 64) (by omega) (hm5.kept hwf4) hs5 hts4
  have hat := c.at_call (o := 32) (by omega) hf5
  have hle : 2672 - 32 + readScalarsStack ≤ finalLevelStack := by decide
  have hwt := c.whirT hat hf5.same hle
  have hpre : ReadScalarsPre a s st5.data := by
    refine ⟨hwt.1, hwt.2.1, ?_, ?_, ?_, ?_⟩
    · show TStateAt st5.data.dmem (reg st5.data .rdi) a s
      rw [ht5]; exact hts5
    · show TStateOk st5.data (reg st5.data .rdi) a readScalarsStack
      rw [ht5]; exact hwt.2.2.2.1
    · show OutOk st5.data (reg st5.data .rdi) a (reg st5.data .rsi)
        (16 * (reg st5.data .rdx).toNat) readScalarsStack
      rw [ht5, hsi5, hdx5]
      exact c.outLoc (by omega) hf5 hle (by omega) (by omega)
    · rw [ht5, hsi5, hdx5]
      apply c.got_call hf5 (by omega) hle (by decide)
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl | rfl | rfl
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
      · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
      · exact c.got_loc (by omega) (by omega)
      · exact c.got_rc
  refine call_then hpc5 (hrs a s) hpre fun st6 hpc6 hrsp6 hq ↦ ?_
  obtain ⟨hok, hxs, hnext, hch, hsv⟩ := hq
  rw [hdx5] at hok hxs hnext hch
  rw [ht5] at hnext hch
  rw [hsi5] at hch
  rw [hsi5] at hxs
  obtain ⟨hf6, hkeep6⟩ := c.call (o := 32) (by omega) hf5 hle hsv hrsp6
    (R := fun q ↦ NativeRustcVm.InRange (loc m0 1600) (16 * (2 ^ mu m0 + level.fold)) q ∨
      NativeRustcVm.InRange (tA m0) tstateBytes q) (lo := 1600)
    (n := 16 * (2 ^ mu m0 + level.fold)) (by omega) (by omega)
    (fun q hq ↦ hq.elim Or.inr fun h ↦ Or.inl (Or.inr h))
    (NativeRustcVm.SameOutside.mono hch fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact Or.inl (Or.inl hq)
      · exact Or.inl (Or.inr hq)
      · exact Or.inr hq)
  have hcs6 : ∀ r, calleeSaved r = true → reg st6.data r = reg st5.data r := hsv.1
  rw [show k + NativeRustcVmX64.Vm.FinalLevel.b4Offset + b4.length = k + NativeRustcVmX64.Vm.FinalLevel.b5Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.FinalLevel.b4_next]] at hpc6
  -- `b5`: the verdict.
  refine Eventually.bind (test_spec hp c b5_in_code rfl exit_b5 ok_b5 hf6 hpc6 hok)
    fun st7 ⟨hr7, hd7, hpc7⟩ ↦ ?_
  have hf7 := hf6.congr hr7 hd7
  rcases hres : (readScalars (2 ^ mu m0 + level.fold)).run s with _ | ⟨⟨folded, s1⟩⟩
  · rw [hres] at hpc7
    simp only [Option.isSome_none, Bool.false_eq_true, ite_false] at hpc7
    exact none36 hp c hf7 (hpc7.trans (l5 hp)) (by
      show (finalLevelM _ level (mu m0) _ b w rounds).run s = none
      rw [finalLevelM_eq]; exact run_bind_none hres)
  · rw [hres] at hpc7
    simp only [Option.isSome_some, ite_true] at hpc7
    have k7 : ∀ r, calleeSaved r = true → reg st7.data r = reg st5.data r := fun r hr ↦
      (hr7 r).trans (hcs6 r hr)
    refine cont st7 folded s1 hpc7 ⟨hf7, ?_, ?_, ?_, (k7 .r12 rfl).trans h12,
      (by rw [k7 .r13 rfl]; exact h13'), (by rw [k7 .r14 rfl]; exact h14'),
      (k7 .r15 rfl).trans h15, NativeRustcVm.Sumcheck.readScalars_size hres,
      (by rw [hd7]; exact hxs folded s1 hres)⟩
      ((k7 .rbx rfl).trans hbx5) ((k7 .rbp rfl).trans hbp5)
      (by rw [hd7]; exact hnext folded s1 hres) (by
        show (finalLevelM _ level (mu m0) _ b w rounds).run s = _
        rw [finalLevelM_eq]; exact run_bind_some hres)
    · rw [hd7]
      exact bytes_call hkeep6 (j := 40) (by omega) (by simp [NativeRustcVm.length_wordBytes])
        (Or.inl (by simp [NativeRustcVm.length_wordBytes])) hw40'
    · rw [hd7]
      exact bytes_call hkeep6 (j := 48) (by omega) (by simp [NativeRustcVm.length_wordBytes])
        (Or.inl (by simp [NativeRustcVm.length_wordBytes])) hw48
    · rw [hd7]
      exact bytes_call hkeep6 (j := 56) (by omega) (by simp [NativeRustcVm.length_wordBytes])
        (Or.inl (by simp [NativeRustcVm.length_wordBytes])) hw56

end

end NativeRustcVmX64.Whir.Levels.FL
