module

public import NativeRustcVmArm.Code.Vm.TStateReadCommitment.Names
public import NativeRustcVmArm.Whir.NextLevel.Keep

/-!
# `next_level`: the prologue and `read_commitment`

`b0` saves X19 to X30, keeps the `TState` (X22), the index (X20), the `WhirW` (X19), `μ` (X27 and
the frame's word `88`), the level (X28) and its rate exponent (X29), and calls
`read_commitment(t, (μ - next.fold) + next.logInvRate, 2 << next.fold)` (`entry`).
-/

namespace NativeRustcVmArm.Whir.NextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.NextLevel

@[expose] public section

/-- The callee-saved registers `b0` sets. -/
structure Regs (level : Whir.Level) (m0 st : MachineData) : Prop where
  x19 : st.regs.X19 = m0.regs.X6
  x20 : st.regs.X20 = m0.regs.X1
  x22 : st.regs.X22 = m0.regs.X0
  x27 : st.regs.X27 = m0.regs.X5
  x28 : st.regs.X28 = m0.regs.X2
  x29 : st.regs.X29 = level.logInvRate.toUInt64

end

public section

theorem Regs.of_cs {level : Whir.Level} {m0 st st' : MachineData} (h : Regs level m0 st)
    (hcs : ∀ r, calleeSaved r = true → st'.regs.getXReg r = st.regs.getXReg r) :
    Regs level m0 st' :=
  ⟨(hcs .X19 rfl).trans h.x19, (hcs .X20 rfl).trans h.x20, (hcs .X22 rfl).trans h.x22,
    (hcs .X27 rfl).trans h.x27, (hcs .X28 rfl).trans h.x28, (hcs .X29 rfl).trans h.x29⟩

theorem Regs.of_all {level : Whir.Level} {m0 st st' : MachineData} (h : Regs level m0 st)
    (hr : ∀ r : XReg, st'.regs.getXReg r = st.regs.getXReg r) : Regs level m0 st' :=
  h.of_cs fun r _ ↦ hr r

theorem level_words {d : Mem 64} {p : BitVec 64} {l : Whir.Level} (h : LevelAt d p l) :
    NativeRustcVm.WordAt d p l.fold.toUInt64 ∧
      NativeRustcVm.WordAt d (p + BitVec.ofNat 64 8) l.logInvRate.toUInt64 ∧
      NativeRustcVm.WordAt d (p + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) l.queries.toUInt64 := by
  obtain ⟨-, -, -, hw⟩ := h
  rw [NativeRustcVm.wordsAt_cons_iff, NativeRustcVm.wordsAt_cons_iff,
    NativeRustcVm.wordsAt_singleton_iff] at hw
  exact hw

theorem height_toNat (x3 x4 x5 : BitVec 64) (h5 : x5.toNat ≤ 30) (h4 : x4.toNat < 64) :
    ((if x5.ult x3 = true then BitVec.ofNat 64 0 else x5 - x3) + x4).toNat =
      x5.toNat - x3.toNat + x4.toNat := by
  split
  · rename_i hc
    rw [BitVec.ult_iff_lt, BitVec.lt_def] at hc
    rw [BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_add]
    omega
  · rename_i hc
    rw [BitVec.ult_iff_lt, BitVec.lt_def] at hc
    rw [BitVec.toNat_add, BitVec.toNat_sub]
    omega

theorem width_toNat (x3 : BitVec 64) (h3 : x3.toNat < 63) :
    (BitVec.ofNat 64 2 <<< (x3.toNat % 64)).toNat = 2 * 2 ^ x3.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt (by omega : x3.toNat < 64), Nat.shiftLeft_eq]
  have : 2 ^ x3.toNat < 2 ^ 63 := Nat.pow_lt_pow_right (by decide) h3
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by decide : 2 < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]

section
variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The prologue and `read_commitment`.** -/
theorem entry (hp : Placed code k) (h : NextLevelPre a s level w rounds m0)
    (hrc : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadCommitment.entryLabel) (ReadCommitmentPre a s)
      (ReadCommitmentPost a s))
    {R : MachineState → Prop}
    (cont : ∀ m2 : MachineData, NFr m0 m2 → Regs level m0 m2 →
      m2.regs.X0 = okWord ((readCommitment (m0.regs.X5.toNat - m0.regs.X3.toNat +
        m0.regs.X4.toNat) (2 * 2 ^ m0.regs.X3.toNat)).run s).isSome →
      NextAt m2.dmem (tA m0) a ((readCommitment (m0.regs.X5.toNat - m0.regs.X3.toNat +
        m0.regs.X4.toNat) (2 * 2 ^ m0.regs.X3.toNat)).run s) →
      NativeRustcVm.WordAt m2.dmem (loc m0 88) m0.regs.X5 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b1Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b0Offset)⟩ := by
  have g := geo h
  have c := ctx h
  have hwf : (envL m0 m0).WF := by
    have hb := base_nat (m0 := m0) (F := 8192) (hN8 h)
    refine Env.wf_of ⟨⟨frame_mapped h.1.1 (by rw [stack_eq]; decide), frNoWrap h⟩,
      ⟨(lvlIn h).1.1, (lvlIn h).1.2⟩, trivial⟩ (List.pairwise_pair.mpr ?_)
    show Apart (base m0 8192) 8192 (lA m0) 24
    unfold Apart; rw [hb]; have := g.lS; have := g.hN; omega
  have hm : Match (envL m0 m0) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frAligned h, rfl, fun h ↦ absurd h (by decide), trivial⟩
      (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some]; rw [show BitVec.ofInt 64 8192 = BitVec.ofNat 64 8192 from rfl,
        base_add_eq])
      ⟨by show (m0.regs.getXReg .X2).toBitVec = _; simp [Sym.eval]; rfl, trivial⟩ trivial trivial
      trivial
  refine exec_then (inf hp b0_in_code (by simp [b0])) run_b0 hwf hm fun st1 hm1 hpc1 ↦ ?_
  have hmem : ∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 8192 := by
    rw [after_eq run_b0]; decide
  have hok : slotsOk (after b0 entryS) slots = true := by rw [after_eq run_b0]; decide
  rw [after_eq run_b0] at hmem hok
  have hf1 : NFr m0 st1.data := Fr.ofPrologue (by rw [stack_eq]; exact g.hN)
    (by rw [stack_eq]; decide) hm1 hwf rfl hok slots_le' hmem (fun _ h ↦ by cases h)
  have hs1 : SameOutside m0.dmem st1.data.dmem (InRange (base m0 8192) 8192) :=
    NativeRustcVm.SameOutside.mono (hm1.sameOutside hwf) fun q hq ↦ written_r0 hwf rfl hmem hq
  have hts1 : TStateAt st1.data.dmem (tA m0) a s := tsB h (hm1.kept hwf) hs1 h.2.1
  have hmu1 : NativeRustcVm.WordAt st1.data.dmem (loc m0 88) m0.regs.X5 := by
    have hw := hm1.bytesAt_write (r := 0) (o := 88) (n := 8) (b := base m0 8192) (sz := 8192) rfl
      (by decide) (v := .reg .X5) (by decide)
    rw [wordBytes_reg] at hw
    exact hw
  have hlv := level_words h.2.2.2.2.1
  have hR : Regs level m0 st1.data := by
    refine ⟨reg_of hm1 (r := .X19) (v := .reg .X6) rfl rfl,
      reg_of hm1 (r := .X20) (v := .reg .X1) rfl rfl,
      reg_of hm1 (r := .X22) (v := .reg .X0) rfl rfl,
      reg_of hm1 (r := .X27) (v := .reg .X5) rfl rfl,
      reg_of hm1 (r := .X28) (v := .ptr 1 0) rfl ?_,
      reg_of hm1 (r := .X29) (v := .load 1 8 8) rfl ?_⟩
    · simp [Sym.eval]
    · exact load_word (by simpa using hlv.2.1)
  have hx0 : st1.data.regs.X0 = m0.regs.X0 := reg_of hm1 (r := .X0) (v := .reg .X0) rfl rfl
  have hX1 : st1.data.regs.X1.toNat =
      m0.regs.X5.toNat - m0.regs.X3.toNat + m0.regs.X4.toNat := by
    have e := reg_val hm1 (r := .X1) rfl
    simp only [Sym.eval, SBool.eval, BinOp.apply, CmpOp.apply, low_W64, ext_W64,
      Env.ofMachine_regs] at e
    show (st1.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [e]
    exact height_toNat _ _ _ h.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1
  have hX2 : st1.data.regs.X2.toNat = 2 * 2 ^ m0.regs.X3.toNat := by
    have e := reg_val hm1 (r := .X2) rfl
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs] at e
    show (st1.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [e]
    exact width_toNat _ h.2.2.2.2.2.2.2.2.1
  simp only [PcOk] at hpc1
  have hle : 8192 + readCommitmentStack ≤ nextLevelStack := by decide
  refine ncall c hf1 (N' := readCommitmentStack) (o := 0) (n := 0) hle (by decide) (hrc a s) hpc1
    ?_ (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩)
    fun m2 hf2 hq hs2 hcs ↦ ?_
  · refine ⟨c.stackOk hf1 hle, c.rcAt hf1 hle, ?_, ?_, h.2.2.1⟩
    · show TStateAt st1.data.dmem st1.data.regs.X0.toBitVec a s
      rw [hx0]; exact hts1
    · show TStateOk st1.data st1.data.regs.X0.toBitVec a readCommitmentStack
      rw [hx0]; exact c.tstateOk hf1 hle
  · rcases hq' with hq' | hq'
    · right; right; left
      rw [show st1.data.regs.X0.toBitVec = tA m0 by rw [hx0]] at hq'
      exact hq'
    · exact .inl hq'
  · obtain ⟨h0, hnext, -, -⟩ := hq
    rw [hX1, hX2] at h0 hnext
    refine cont m2 hf2 (hR.of_cs hcs) h0 (by rw [hx0] at hnext; exact hnext) ?_
    exact keepC c hf1 hle (by decide) hs2 (o := 88)
      (by rw [NativeRustcVm.length_wordBytes]; decide) (by simp) hmu1

end

end

end NativeRustcVmArm.Whir.NextLevel
