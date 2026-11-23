module

public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateReadCommitment.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.Whir.NextLevel.Entry
public import NativeRustcVm.Sumcheck.RoundPoly

/-!
# `next_level`: the high part and the first grind

From `read_commitment`'s return: its `Option<()>` tested (`b1`), the level's fold into X21 and
the high part's buffer zeroed (`b2`, at most `6` folds), `read_scalars(t, sp + 96, fold)` (`b3`),
its `Option<()>` tested (`b4`), `grind(t, 15)` (`b5`), tested (`b6`): `head`, to `b7` with `H7`.
-/

namespace NativeRustcVmArm.Whir.NextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.NextLevel

@[expose] public section

/-- The registers `rs` known in `S0` and kept in `S`. -/
def sameRegs (rs : List XReg) (S0 S : SState) : Bool :=
  rs.all fun r ↦ (S0.reg r).isSome && S.reg r == S0.reg r

/-- At `b7`: the frame, the registers, `μ` at `88`, the high part `xs` at `96`, the `TState`. -/
structure H7 [Labels] (a : DecArea) (level : Whir.Level) (m0 : MachineData) (xs : Array EW)
    (s3 : TState) (st : MachineData) : Prop where
  fr : NFr m0 st
  regs : Regs level m0 st
  x21 : st.regs.X21 = level.fold.toUInt64
  mu : NativeRustcVm.WordAt st.dmem (loc m0 88) m0.regs.X5
  high : NativeRustcVm.EWsAt st.dmem (loc m0 96) xs.toList
  size : xs.size = level.fold
  ts : TStateAt st.dmem (tA m0) a s3

end

public section

theorem sameRegs_ok [Labels] {env : Env} {S0 S : SState} {st st' : MachineData}
    (hm0 : Match env S0 st) (hm : Match env S st') {rs : List XReg}
    (h : sameRegs rs S0 S = true) : ∀ r ∈ rs, st'.regs.getXReg r = st.regs.getXReg r := by
  intro r hr
  simp only [sameRegs, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
    Option.isSome_iff_exists] at h
  obtain ⟨⟨v, hv⟩, hS⟩ := h r hr
  exact Match.reg_eq hm0 hm hv (hS.trans hv)

theorem regs6 [Labels] {env : Env} {S0 S : SState} {st st' : MachineData} {level : Whir.Level}
    {m0 : MachineData} (hm0 : Match env S0 st) (hm : Match env S st')
    (h : sameRegs [.X19, .X20, .X22, .X27, .X28, .X29] S0 S = true) (hR : Regs level m0 st) :
    Regs level m0 st' := by
  have := sameRegs_ok hm0 hm h
  exact ⟨(this .X19 (by simp)).trans hR.x19, (this .X20 (by simp)).trans hR.x20,
    (this .X22 (by simp)).trans hR.x22, (this .X27 (by simp)).trans hR.x27,
    (this .X28 (by simp)).trans hR.x28, (this .X29 (by simp)).trans hR.x29⟩

/-- A bound read off `cmp`, `b.hi`: not above. -/
theorem not_hi {x c : BitVec 64} (h : x.toNat ≤ c.toNat) : (!x.ult c && !(x == c)) = false := by
  rcases Nat.lt_or_eq_of_le h with hlt | heq
  · have : x.ult c = true := by simp [BitVec.ult, hlt]
    simp [this]
  · simp [BitVec.eq_of_toNat_eq heq]

theorem bind_none_of {α β : Type} {o : Option α} {f : α → Option β} (h : o.isSome = false) :
    o.bind f = none := by
  cases o <;> simp_all

theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp [Nat.toUInt64]; omega

section
variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

omit [Host] in
theorem runN_eq :
    runN level w rounds m0 s =
      ((readCommitment (m0.regs.X5.toNat - m0.regs.X3.toNat + m0.regs.X4.toNat)
        (2 * 2 ^ m0.regs.X3.toNat)).run s).bind
        fun p1 ↦ ((readScalars level.fold).run p1.2).bind
        fun p2 ↦ ((grind 15).run p2.2).bind
        fun p3 ↦ tail3 m0.regs.X1.toNat m0.regs.X5.toNat level w rounds p2.1 p3.2 :=
  run_eq _ _ _ _ _ _ _

/-- The height `read_commitment` reads. -/
abbrev hgt (m0 : MachineData) : Nat := m0.regs.X5.toNat - m0.regs.X3.toNat + m0.regs.X4.toNat

/-- **`read_commitment` and its test**, to `b2`. -/
theorem head1 (hp : Placed code k) (h : NextLevelPre a s level w rounds m0)
    (hrc : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadCommitment.entryLabel) (ReadCommitmentPre a s)
      (ReadCommitmentPost a s))
    (cont : ∀ st s1, st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b2Offset) → NFr m0 st.data → Regs level m0 st.data →
      NativeRustcVm.WordAt st.data.dmem (loc m0 88) m0.regs.X5 →
      TStateAt st.data.dmem (tA m0) a s1 →
      (readCommitment (hgt m0) (2 * 2 ^ m0.regs.X3.toNat)).run s = some ((), s1) →
      Eventually (step1 Host.exe) (Goal a s level w rounds m0) st) :
    Eventually (step1 Host.exe) (Goal a s level w rounds m0) ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b0Offset)⟩ := by
  refine entry hp h hrc fun m2 hf2 hR2 h0 hnext hmu2 ↦ ?_
  refine chk14 hp h b1_in_code (st := ⟨m2, _⟩) hf2 rfl h0 (fun hn ↦ by
      rw [runN_eq]; exact bind_none_of hn)
    (fun _ h ↦ h) fun hok st3 hpc3 hf3 hd3 hr3 ↦ ?_
  obtain ⟨⟨⟨⟩, s1⟩, hr1⟩ := Option.isSome_iff_exists.mp hok
  exact cont st3 s1 hpc3 hf3 (hR2.of_all hr3) (by rw [hd3]; exact hmu2)
    (by rw [hd3]; exact hnext _ _ hr1) hr1

/-- **The fold, `read_scalars` and its test**, to `b5`. -/
theorem head2 (hp : Placed code k) (h : NextLevelPre a s level w rounds m0)
    (hrss : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s)
      (ReadScalarsPost a s))
    {s1 : TState} (hr1 : (readCommitment (hgt m0) (2 * 2 ^ m0.regs.X3.toNat)).run s = some ((), s1))
    {st3 : MachineState} (hpc3 : st3.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b2Offset)) (hf3 : NFr m0 st3.data)
    (hR3 : Regs level m0 st3.data)
    (hmu3 : NativeRustcVm.WordAt st3.data.dmem (loc m0 88) m0.regs.X5)
    (hts3 : TStateAt st3.data.dmem (tA m0) a s1)
    (cont : ∀ st xs s2, st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b5Offset) → NFr m0 st.data → Regs level m0 st.data →
      st.data.regs.X21 = level.fold.toUInt64 →
      NativeRustcVm.WordAt st.data.dmem (loc m0 88) m0.regs.X5 →
      NativeRustcVm.EWsAt st.data.dmem (loc m0 96) xs.toList →
      TStateAt st.data.dmem (tA m0) a s2 → (readScalars level.fold).run s1 = some (xs, s2) →
      Eventually (step1 Host.exe) (Goal a s level w rounds m0) st) :
    Eventually (step1 Host.exe) (Goal a s level w rounds m0) st3 := by
  have c := ctx h
  have hf6 : level.fold ≤ 6 := h.2.2.2.2.2.1
  -- `b2`: the fold, the buffer zeroed.
  have hlv := level_words (level_keep h hf3)
  have hld : (envL m0 st3.data).load 1 0 8 = level.fold.toUInt64.toBitVec :=
    load_word (by simpa using hlv.1)
  have hfl : level.fold < 2 ^ 64 := (level_keep h hf3).1
  have hle6 : level.fold.toUInt64.toBitVec.toNat ≤ (BitVec.ofNat 64 6).toNat := by
    rw [show (BitVec.ofNat 64 6).toNat = 6 from rfl, UInt64.toNat_toBitVec, toNat_toUInt64 hfl]
    exact hf6
  have hc : (SBool.and (.not (.cmp .ult .W64 (.load 1 0 8) (.lit 6)))
      (.not (.cmp .eq .W64 (.load 1 0 8) (.lit 6)))).eval (envL m0 st3.data) = false := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, hld]
    exact not_hi hle6
  refine blk hp h b2_in_code (by simp [b2]) run_b2 (wfL h hf3) (mL h hf3 hR3.x28) (by decide) rfl
    hf3 hpc3 fun st4 hm4 hpc4 hf4 hs4 ↦ ?_
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc4
  rw [show k + NativeRustcVmArm.Vm.NextLevel.b2Offset + b2.length = k + NativeRustcVmArm.Vm.NextLevel.b3Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.NextLevel.b2_next]] at hpc4
  have hR4 : Regs level m0 st4.data := regs6 (mL h hf3 hR3.x28) hm4 (by decide) hR3
  have h21 : st4.data.regs.X21 = level.fold.toUInt64 := reg_of hm4 (r := .X21) rfl hld
  have hts4 := tsB h (hm4.kept (wfL h hf3)) hs4 hts3
  have hmu4 : NativeRustcVm.WordAt st4.data.dmem (loc m0 88) m0.regs.X5 :=
    keepB hm4 (wfL h hf3) (o := 88) (n := 8) (by decide) (by decide)
      (NativeRustcVm.length_wordBytes _) hmu3
  -- `b3`: `read_scalars(t, sp + 96, fold)`.
  refine blk hp h b3_in_code (by simp [b3]) run_b3 (wfF h hf4) (mF h hf4) (by decide) rfl hf4
    hpc4 fun st5 hm5 hpc5 hf5 hs5 ↦ ?_
  simp only [PcOk] at hpc5
  rw [show k + NativeRustcVmArm.Vm.NextLevel.b3Offset + b3.length = k + NativeRustcVmArm.Vm.NextLevel.b4Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.NextLevel.b3_next]] at hpc5
  have hx0 : st5.data.regs.X0 = m0.regs.X0 :=
    (reg_of hm5 (r := .X0) (v := .reg .X22) rfl rfl).trans hR4.x22
  have hx1 : st5.data.regs.X1.toBitVec = loc m0 96 := by
    rw [show st5.data.regs.X1.toBitVec = (st5.data.regs.getXReg .X1).toBitVec from rfl,
      reg_val hm5 (r := .X1) rfl]
    simp [Sym.eval]
  have hx2 : st5.data.regs.X2 = level.fold.toUInt64 :=
    (reg_of hm5 (r := .X2) (v := .reg .X21) (w := st4.data.regs.X21) rfl rfl).trans h21
  have hx2' : st5.data.regs.X2.toNat = level.fold := by rw [hx2, toNat_toUInt64 hfl]
  have hts5 := tsB h (hm5.kept (wfF h hf4)) hs5 hts4
  have hR5 : Regs level m0 st5.data := regs6 (mF h hf4) hm5 (by decide) hR4
  have h21' : st5.data.regs.X21 = level.fold.toUInt64 :=
    (reg_of hm5 (r := .X21) (v := .reg .X21) (w := st4.data.regs.X21) rfl rfl).trans h21
  have hmu5 : NativeRustcVm.WordAt st5.data.dmem (loc m0 88) m0.regs.X5 := by
    rw [hm5.dmem_eq (wfF h hf4) rfl]; exact hmu4
  have hle : 8192 + readScalarsStack ≤ nextLevelStack := by decide
  have hon : 96 + 16 * level.fold ≤ 8096 := by omega
  refine ncall c hf5 (N' := readScalarsStack) (o := 96) (n := 16 * level.fold) hle hon (hrss a s1)
    hpc5 ?_ (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.2.1 fun q hq' ↦ ?_, hq.2.2.2.2⟩)
    fun m6 hf6' hq hs6 hcs ↦ ?_
  · refine ⟨c.stackOk hf5 hle, c.rcAt hf5 hle, ?_, ?_, ?_⟩
    · show TStateAt st5.data.dmem st5.data.regs.X0.toBitVec a s1
      rw [hx0]; exact hts5
    · show TStateOk st5.data st5.data.regs.X0.toBitVec a readScalarsStack
      rw [hx0]; exact c.tstateOk hf5 hle
    · show OutOk st5.data st5.data.regs.X0.toBitVec a st5.data.regs.X1.toBitVec
        (16 * st5.data.regs.X2.toNat) readScalarsStack
      rw [hx0, hx1, hx2']; exact c.localOk hf5 hle (by omega)
  · rw [hx1, hx2'] at hq'
    rw [show st5.data.regs.X0.toBitVec = tA m0 by rw [hx0]] at hq'
    rcases hq' with hq' | hq' | hq'
    · exact .inr (.inl hq')
    · exact .inr (.inr (.inl hq'))
    · exact .inl hq'
  obtain ⟨h06, hxs6, hnext6, -, -⟩ := hq
  rw [hx2'] at h06 hxs6 hnext6
  rw [hx1] at hxs6
  rw [hx0] at hnext6
  have hmu6 : NativeRustcVm.WordAt m6.dmem (loc m0 88) m0.regs.X5 :=
    keepC c hf5 hle (by omega) hs6 (o := 88) (by rw [NativeRustcVm.length_wordBytes]; decide)
      (by rw [NativeRustcVm.length_wordBytes]; omega) hmu5
  -- `b4`: `read_scalars`' result.
  refine chk14 hp h b4_in (st := ⟨m6, _⟩) hf6' rfl h06 (fun hn ↦ by
      rw [runN_eq, hr1]
      show ((readScalars level.fold).run s1).bind _ = none
      exact bind_none_of hn)
    (fun _ h ↦ h) fun hok st7 hpc7 hf7 hd7 hr7 ↦ ?_
  obtain ⟨⟨xs, s2⟩, hr2⟩ := Option.isSome_iff_exists.mp hok
  exact cont st7 xs s2 hpc7 hf7 ((hR5.of_cs hcs).of_all hr7)
    ((hr7 .X21).trans ((hcs .X21 rfl).trans h21')) (by rw [hd7]; exact hmu6)
    (by rw [hd7]; exact hxs6 _ _ hr2) (by rw [hd7]; exact hnext6 _ _ hr2) hr2

/-- **`grind(t, 15)` and its test**, to `b7`. -/
theorem head3 (hp : Placed code k) (h : NextLevelPre a s level w rounds m0)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    {s1 s2 : TState} {xs : Array EW}
    (hr1 : (readCommitment (hgt m0) (2 * 2 ^ m0.regs.X3.toNat)).run s = some ((), s1))
    (hr2 : (readScalars level.fold).run s1 = some (xs, s2))
    {st7 : MachineState} (hpc7 : st7.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b5Offset)) (hf7 : NFr m0 st7.data)
    (hR7 : Regs level m0 st7.data) (h21_7 : st7.data.regs.X21 = level.fold.toUInt64)
    (hmu7 : NativeRustcVm.WordAt st7.data.dmem (loc m0 88) m0.regs.X5)
    (hxs7 : NativeRustcVm.EWsAt st7.data.dmem (loc m0 96) xs.toList)
    (hts7 : TStateAt st7.data.dmem (tA m0) a s2)
    (cont : ∀ st xs s3, st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b7Offset) → H7 a level m0 xs s3 st.data →
      runN level w rounds m0 s = tail3 m0.regs.X1.toNat m0.regs.X5.toNat level w rounds xs s3 →
      Eventually (step1 Host.exe) (Goal a s level w rounds m0) st) :
    Eventually (step1 Host.exe) (Goal a s level w rounds m0) st7 := by
  have c := ctx h
  have hxsz : xs.size = level.fold := NativeRustcVm.Sumcheck.readScalars_size hr2
  refine blk hp h b5_in_code (by simp [b5]) run_b5 (wfF h hf7) (mF h hf7) (by decide) rfl hf7
    hpc7 fun st8 hm8 hpc8 hf8 hs8 ↦ ?_
  simp only [PcOk] at hpc8
  rw [show k + NativeRustcVmArm.Vm.NextLevel.b5Offset + b5.length = k + NativeRustcVmArm.Vm.NextLevel.b6Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.NextLevel.b5_next]] at hpc8
  have hx0' : st8.data.regs.X0 = m0.regs.X0 :=
    (reg_of hm8 (r := .X0) (v := .reg .X22) rfl rfl).trans hR7.x22
  have hx1 : st8.data.regs.X1 = 15 := reg_of hm8 (r := .X1) (v := .lit 15) rfl rfl
  have hbits : grindBits st8.data = 15 := by unfold grindBits; rw [hx1]; rfl
  have hd8 : st8.data.dmem = st7.data.dmem := hm8.dmem_eq (wfF h hf7) rfl
  have hR8 : Regs level m0 st8.data := regs6 (mF h hf7) hm8 (by decide) hR7
  have h21_8 : st8.data.regs.X21 = level.fold.toUInt64 :=
    (reg_of hm8 (r := .X21) (v := .reg .X21) (w := st7.data.regs.X21) rfl rfl).trans h21_7
  have hleg : 8192 + grindStack ≤ nextLevelStack := by decide
  refine ncall c hf8 (N' := grindStack) (o := 0) (n := 0) hleg (by decide) (hgr a s2) hpc8 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩)
    fun m9 hf9 hq hs9 hcs9 ↦ ?_
  · refine ⟨c.stackOk hf8 hleg, c.rcAt hf8 hleg, ?_, ?_, by rw [hbits]; decide⟩
    · show TStateAt st8.data.dmem st8.data.regs.X0.toBitVec a s2
      rw [hx0', hd8]; exact hts7
    · show TStateOk st8.data st8.data.regs.X0.toBitVec a grindStack
      rw [hx0']; exact c.tstateOk hf8 hleg
  · rw [show st8.data.regs.X0.toBitVec = tA m0 by rw [hx0']] at hq'
    rcases hq' with hq' | hq'
    · exact .inr (.inr (.inl hq'))
    · exact .inl hq'
  obtain ⟨h09, hnext9, -, -⟩ := hq
  rw [hbits] at h09 hnext9
  rw [hx0'] at hnext9
  have keep9 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 8192 →
      NativeRustcVm.BytesAt st8.data.dmem (loc m0 o) bs →
        NativeRustcVm.BytesAt m9.dmem (loc m0 o) bs :=
    fun ho hb ↦ keepC c hf8 hleg (o' := 0) (n' := 0) (by decide) hs9 ho (by omega) hb
  -- `b6`: the grind's result.
  refine chk14 hp h b6_in (st := ⟨m9, _⟩) hf9 rfl h09 (fun hn ↦ by
      rw [runN_eq, hr1]
      show ((readScalars level.fold).run s1).bind _ = none
      rw [hr2]
      show ((grind 15).run s2).bind _ = none
      exact bind_none_of hn)
    (fun _ h ↦ h) fun hok st10 hpc10 hf10 hd10 hr10 ↦ ?_
  obtain ⟨⟨⟨⟩, s3⟩, hr3⟩ := Option.isSome_iff_exists.mp hok
  refine cont st10 xs s3 hpc10 ⟨hf10, (hR8.of_cs hcs9).of_all hr10,
    (hr10 .X21).trans ((hcs9 .X21 rfl).trans h21_8), ?_, ?_, hxsz, ?_⟩ ?_
  · rw [hd10]
    exact keep9 (by rw [NativeRustcVm.length_wordBytes]; decide) (by rw [hd8]; exact hmu7)
  · rw [hd10]
    exact keep9 (by
        rw [NativeRustcVm.length_ewsBytes]; simp [hxsz]
        have : level.fold ≤ 6 := h.2.2.2.2.2.1
        omega)
      (by rw [hd8]; exact hxs7)
  · rw [hd10]; exact hnext9 _ _ hr3
  · rw [runN_eq, hr1]
    show ((readScalars level.fold).run s1).bind _ = _
    rw [hr2]
    show ((grind 15).run s2).bind _ = _
    rw [hr3]
    rfl

/-- **To `b7`.** -/
theorem head (hp : Placed code k) (h : NextLevelPre a s level w rounds m0)
    (hrc : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadCommitment.entryLabel) (ReadCommitmentPre a s)
      (ReadCommitmentPost a s))
    (hrss : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s)
      (ReadScalarsPost a s))
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (cont : ∀ st xs s3, st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b7Offset) → H7 a level m0 xs s3 st.data →
      runN level w rounds m0 s = tail3 m0.regs.X1.toNat m0.regs.X5.toNat level w rounds xs s3 →
      Eventually (step1 Host.exe) (Goal a s level w rounds m0) st) :
    Eventually (step1 Host.exe) (Goal a s level w rounds m0) ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b0Offset)⟩ :=
  head1 hp h hrc fun _ _ hpc3 hf3 hR3 hmu3 hts3 hr1 ↦
    head2 hp h hrss hr1 hpc3 hf3 hR3 hmu3 hts3 fun _ _ _ hpc7 hf7 hR7 h21 hmu7 hxs7 hts7 hr2 ↦
      head3 hp h hgr hr1 hr2 hpc7 hf7 hR7 h21 hmu7 hxs7 hts7 cont

end

end

end NativeRustcVmArm.Whir.NextLevel
