module

public import NativeRustcVmArm.Layout.PlacementsOf.Mid

/-!
# `placements_of`: the second loop (`b15` to `b19`)

At `.L10` (`I2 i`): `b15` loads the `i`th stacked column `c`, `b16` its offset into `offsets[c]`.
After the `94` stacked columns, `b17` loads `offsets[4]` (`q_keccak`'s block) and `b19` starts the
third loop at `.L17` (`I3 0`).
-/

namespace NativeRustcVmArm.Layout.PlacementsOf

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PlacementsOf
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf addr_add_add addr_add_zero toNat_add_ofNat)
open NativeRustcVmArm.Arrays (Body calleeRegs inSlots keepsAll restores)

public section

section
variable [Labels]

/-- **The third loop** at `.L17`: the placements of the columns below `c` written. -/
structure I3 (m0 : MachineData) (c : Nat) (st : MachineData) : Prop where
  body : Bd m0 st
  le : c ≤ 158
  x9 : st.regs.X9.toNat = c
  x10 : st.regs.X10.toBitVec = pp m0 + BitVec.ofNat 64 (24 * c + 16)
  x8 : st.regs.X8.toNat = sumF (κ m0) (keyF (κ m0) 4)
  keep : Keep m0 st
  x21 : st.regs.X21.toNat = log2Ceil (sumF (κ m0) 0)
  x25 : st.regs.X25.toBitVec = fb m0 + BitVec.ofNat 64 3792
  offs : ∀ c' ∈ blockList, WordAt st.dmem (fb m0 + BitVec.ofNat 64 (3792 + 8 * c'))
    (sumF (κ m0) (keyF (κ m0) c')).toUInt64
  pl : ∀ c' < c, PlacementWAt st.dmem (pp m0 + BitVec.ofNat 64 (24 * c')) (plF (κ m0) c')

/-- The sizes of the stacked columns fit a `u64` with room. -/
theorem Facts.sumF_le {m0 : MachineData} (hF : Facts m0) (kr : Nat) :
    sumF (κ m0) kr ≤ 158 * 2 ^ 36 :=
  NativeRustcVmArm.Layout.PlacementsOf.sumF_le _ kr fun _ hc ↦ hF.κ_le hc

theorem I2.keep' {m0 st : MachineData} {i : Nat} (h : I2 m0 i st) : Keep m0 st :=
  ⟨h.x19, h.x20, h.x23, h.x24⟩

end

variable [Host] {k : Nat}

/-- **A turn** of the second loop: the `i`th stacked column's offset into `offsets`. -/
theorem turn2 (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {i : Nat} (hi : i < 94)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b15Offset)) (hI : I2 m0 i st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (i + 1 < 94 ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b15Offset) ∧
      I2 m0 (i + 1) s.data) ∨ (i + 1 = 94 ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b17Offset) ∧ I2 m0 94 s.data)) st := by
  have hb := hI.body
  have hn : blockList.length = 94 := blockList_length
  have hil : i < blockList.length := by omega
  set c := blockList[i] with hc
  have hc158 : c < 158 := lt_of_mem_blockList (List.getElem_mem hil)
  -- `b15`: the column
  have f0 := frame_readable hF hb (o := 8 * i) (n := 8) (by omega)
  have hwf := Arrays.wf_one f0.1 f0.2
  have hm : Match (Env.ofMachine st.data [(fb m0 + BitVec.ofNat 64 (8 * i), 8)]) l15S st.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl ⟨by
      show _ = (fb m0 + BitVec.ofNat 64 (8 * i)) + BitVec.ofInt 64 0
      rw [Layout.ofInt_zero, BitVec.add_zero]; exact hI.x9, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b15_in_code (by simp [b15]) hp) run_b15 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hb1 : Bd m0 st1.data := hb.of_block hm hm1 hwf rfl (Arrays.after_eq run_b15 ▸ b15_keep)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have e1 := Arrays.regs_eq_of hm hm1 [.X8, .X19, .X20, .X21, .X22, .X23, .X24, .X25] rfl
  have g10 := hm1.regs .X10 _ rfl
  have g9 := hm1.regs .X9 _ rfl
  sym_simp at g10 g9
  have hw10 : (Env.ofMachine st.data [(fb m0 + BitVec.ofNat 64 (8 * i), 8)]).load 0 0 8 =
      BitVec.ofNat 64 c := by
    rw [Layout.load_word (v := c.toUInt64) (by
      simp only [Env.ofMachine_mem0, Arrays.base0, addr_add_zero]; exact hI.cols i hil)]
    rfl
  have x10 : (st1.data.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 c := by rw [g10, hw10]
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  rw [hw10, ofNat_ult' (by omega) (by decide)] at hpc1
  have hpc2 := pc_of ((Arrays.pc_cond hpc1).2 (by simp; omega))
    (show k + NativeRustcVmArm.Vm.PlacementsOf.b15Offset + b15.length = k + NativeRustcVmArm.Vm.PlacementsOf.b16Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.PlacementsOf.b15_next])
  -- `b16`: its offset
  have hb1' := hb1
  have f1 := frame_readable hF hb1 (o := 2528 + 8 * i) (n := 8) (by omega)
  have f2 := frame_readable hF hb1 (o := 3792 + 8 * c) (n := 8) (by omega)
  let env := Env.ofMachine st1.data [(fb m0 + BitVec.ofNat 64 (2528 + 8 * i), 8),
    (fb m0 + BitVec.ofNat 64 (3792 + 8 * c), 8)]
  have hwf2 : env.WF := Env.wf_of ⟨⟨f1.1, f1.2⟩, ⟨f2.1, f2.2⟩, trivial⟩
    (List.Pairwise.cons (by
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        subst he
        exact frame_apart hF (by omega) (by omega) (by omega))
      (List.Pairwise.cons nofun .nil))
  have x8 : (st1.data.regs.getXReg .X8).toBitVec = fb m0 + BitVec.ofNat 64 (2528 + 8 * i) := by
    rw [e1 .X8 (by simp)]; exact hI.x8
  have x25 : (st1.data.regs.getXReg .X25).toBitVec = fb m0 + BitVec.ofNat 64 3792 := by
    rw [e1 .X25 (by simp)]; exact hI.x25
  have hm2 : Match env l16S st1.data := match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
    ⟨by
      show _ = (fb m0 + BitVec.ofNat 64 (2528 + 8 * i)) + BitVec.ofInt 64 0
      rw [Layout.ofInt_zero, BitVec.add_zero]; exact x8, trivial⟩ trivial trivial
    ⟨by
      show (idx .X25 .X10).eval env = _
      rw [idx_eval]
      simp only [env, Env.ofMachine_regs, Env.base_ofMachine_eq, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.map_some, Option.getD_some, Layout.ofInt_zero,
        BitVec.add_zero]
      rw [x25, x10, addr_add_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)], trivial⟩
  refine exec_at (infix_of b16_in_code (by simp [b16]) hp) run_b16 hwf2 hpc2 hm2
    fun st2 hm3 hpc3 ↦ ?_
  obtain ⟨k16, w16, f16⟩ := Arrays.after_eq run_b16 ▸ b16_facts
  have hreg : ∀ (r off n : Nat) (b : BitVec 64) (sz : Nat), (r = 1 ∧ off + n ≤ 8) →
      env.regions[r]? = some (b, sz) → off + n ≤ sz ∧
        b = fb m0 + BitVec.ofNat 64 (3792 + 8 * c) ∧ sz = 8 := by
    intro r off n' b sz ⟨hr, hle⟩ hb'
    subst hr
    have e : env.regions[1]? = some (fb m0 + BitVec.ofNat 64 (3792 + 8 * c), 8) := rfl
    rw [e, Option.some.injEq, Prod.mk.injEq] at hb'
    obtain ⟨rfl, rfl⟩ := hb'
    exact ⟨hle, rfl, rfl⟩
  have hb2 : Bd m0 st2.data := Bd.of_write hF hb1 hm2 hm3 hwf2 rfl k16 fun p hw ↦ by
    obtain ⟨w, hw', b, sz, hb', hin⟩ := written_in hwf2 hw fun w hw b sz hb' ↦
      (hreg _ _ _ b sz (w16 w hw) hb').1
    obtain ⟨-, rfl, rfl⟩ := hreg _ _ _ b sz (w16 w hw') hb'
    obtain ⟨a1, a2⟩ := frame_low hF (by omega) hin
    exact ⟨.inr a1, a2⟩
  have keep : ∀ {o : Nat} {v : UInt64}, o + 8 ≤ 5136 → (o + 8 ≤ 3792 + 8 * c ∨ 3800 + 8 * c ≤ o) →
      WordAt st1.data.dmem (fb m0 + BitVec.ofNat 64 o) v →
      WordAt st2.data.dmem (fb m0 + BitVec.ofNat 64 o) v := fun h1 h2 h ↦
    keep_frame hF hm3 hwf2 rfl h1 (fun w hw b sz hb' ↦ by
      obtain ⟨hle, rfl, rfl⟩ := hreg _ _ _ b sz (w16 w hw) hb'
      exact ⟨hle, 3792 + 8 * c, rfl, by omega, by omega⟩) h
  have new : WordAt st2.data.dmem (fb m0 + BitVec.ofNat 64 (3792 + 8 * c))
      (sumF (κ m0) (keyF (κ m0) c)).toUInt64 := by
    have := Layout.Match.wordAt_write hm3 (r := 1) (o := 0) rfl (by omega) f16
    rw [addr_add_zero] at this
    convert this using 1
    simp only [Sym.eval]
    rw [Layout.load_word (v := (sumF (κ m0) (keyF (κ m0) c)).toUInt64) (by
      simp only [env, Env.ofMachine_mem0, Arrays.base0, addr_add_zero, hd1]
      exact hI.offs i hil)]
  have e3 := Arrays.regs_eq_of hm2 hm3 [.X9, .X19, .X20, .X21, .X23, .X24, .X25] rfl
  have g9' := hm3.regs .X9 _ rfl
  have g8' := hm3.regs .X8 _ rfl
  have g22 := hm3.regs .X22 _ rfl
  sym_simp at g9' g8' g22
  have e22 : env.regs .X22 = BitVec.ofNat 64 (94 - i) := by
    show (st1.data.regs.getXReg .X22).toBitVec = _
    rw [e1 .X22 (by simp)]
    apply BitVec.eq_of_toNat_eq
    show st.data.regs.X22.toNat = _
    rw [hI.x22, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hI' : I2 m0 (i + 1) st2.data := by
    refine ⟨hb2, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q h ↦ ?_, fun q h ↦ ?_,
      fun q h hq ↦ ?_⟩
    · show (st2.data.regs.getXReg .X8).toBitVec = _
      rw [g8']
      show (fb m0 + BitVec.ofNat 64 (2528 + 8 * i)) + BitVec.ofInt 64 8 = _
      rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add_add,
        show 2528 + 8 * i + 8 = 2528 + 8 * (i + 1) by omega]
    · show (st2.data.regs.getXReg .X9).toBitVec = _
      rw [e3 .X9 (by simp), g9]
      show (fb m0 + BitVec.ofNat 64 (8 * i)) + BitVec.ofInt 64 8 = _
      rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add_add,
        show 8 * i + 8 = 8 * (i + 1) by omega]
    · show (st2.data.regs.getXReg .X22).toBitVec.toNat = _
      rw [g22, e22]
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · rw [show st2.data.regs.X19 = st.data.regs.X19 from
        (e3 .X19 (by simp)).trans (e1 .X19 (by simp))]; exact hI.x19
    · rw [show st2.data.regs.X20 = st.data.regs.X20 from
        (e3 .X20 (by simp)).trans (e1 .X20 (by simp))]; exact hI.x20
    · rw [show st2.data.regs.X21 = st.data.regs.X21 from
        (e3 .X21 (by simp)).trans (e1 .X21 (by simp))]; exact hI.x21
    · rw [show st2.data.regs.X23 = st.data.regs.X23 from
        (e3 .X23 (by simp)).trans (e1 .X23 (by simp))]; exact hI.x23
    · rw [show st2.data.regs.X24 = st.data.regs.X24 from
        (e3 .X24 (by simp)).trans (e1 .X24 (by simp))]; exact hI.x24
    · rw [show st2.data.regs.X25 = st.data.regs.X25 from
        (e3 .X25 (by simp)).trans (e1 .X25 (by simp))]; exact hI.x25
    · exact keep (by omega) (by omega) (hd1 ▸ hI.cols q h)
    · exact keep (by omega) (by omega) (hd1 ▸ hI.offs q h)
    · rcases Nat.lt_or_ge q i with hq' | hq'
      · have hne : blockList[q] ≠ c := fun he ↦ by
          have := (List.Nodup.getElem_inj_iff blockList_nodup).mp he
          omega
        have h1 := lt_of_mem_blockList (List.getElem_mem h)
        exact keep (by omega) (by omega) (hd1 ▸ hI.done q h hq')
      · obtain rfl : q = i := by omega
        exact new
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  rw [e22, ofNat_beq' (by omega) (by decide)] at hpc3
  obtain ⟨f3, t3⟩ := Arrays.pc_cond hpc3
  by_cases hlast : i + 1 = 94
  · refine .done _ (.inr ⟨hlast, pc_of (t3 (by simp; omega)) rfl, ?_⟩)
    rw [← hlast]; exact hI'
  · exact .done _ (.inl ⟨by omega, (f3 (by simp; omega)).trans (hp.label (j := NativeRustcVmArm.Vm.PlacementsOf.b15Offset) NativeRustcVmArm.Vm.PlacementsOf.label_10_at), hI'⟩)

/-- **The second loop**, from `.L10` to `b17` with every stacked column's offset placed. -/
theorem loop2 (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {i : Nat} (hi : i < 94)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b15Offset)) (hI : I2 m0 i st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b17Offset) ∧ I2 m0 94 s.data) st := by
  refine Sym.loop (fun n s ↦ ∃ i, i < 94 ∧ 94 - i = n ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b15Offset) ∧
      I2 m0 i s.data) (fun n s ⟨i, hi, hn, hpc, hI⟩ ↦ ?_) ⟨i, hi, rfl, hpc, hI⟩
  refine Eventually.mono (turn2 hp hF hi hpc hI) fun s h ↦ ?_
  rcases h with ⟨hlt, hpc', hI'⟩ | ⟨_, hpc', hI'⟩
  · exact Or.inr ⟨94 - (i + 1), by omega, i + 1, hlt, rfl, hpc', hI'⟩
  · exact Or.inl ⟨hpc', hI'⟩

/-- **`b17`, `b19`**: `offsets[4]` loaded; the third loop's head. -/
theorem to3 (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b17Offset)) (hI : I2 m0 94 st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b22Offset) ∧ I3 m0 0 s.data) st := by
  have hb := hI.body
  have hn : blockList.length = 94 := blockList_length
  obtain ⟨hwf, hm⟩ := hb.exit_match hF.stack (by decide) (by decide)
  refine exec_at (infix_of b17_in_code (by simp [b17]) hp) run_b17 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hb1 : Bd m0 st1.data := hb.of_block hm hm1 hwf rfl (Arrays.after_eq run_b17 ▸ b17_keep)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have e1 := Arrays.regs_eq_of hm hm1 [.X19, .X20, .X21, .X23, .X24, .X25] rfl
  have g8 := hm1.regs .X8 _ rfl
  sym_simp at g8
  have w4 : WordAt st.data.dmem (fb m0 + BitVec.ofNat 64 3824)
      (sumF (κ m0) (keyF (κ m0) 4)).toUInt64 := by
    have := hI.done 4 (by omega) (by omega)
    rw [blockList_get4] at this
    exact this
  have x8 : (st1.data.regs.getXReg .X8).toBitVec =
      (sumF (κ m0) (keyF (κ m0) 4)).toUInt64.toBitVec := by
    rw [g8]
    exact Layout.load_word (by
      simp only [Arrays.frameEnv, Env.ofMachine_mem0, Arrays.base0]; exact w4)
  simp only [PcOk] at hpc1
  refine regs_step (infix_of b19_in_code (by simp [b19]) hp) run_b19 (rk run_b19) hb1
    (hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.PlacementsOf.b19Offset) NativeRustcVmArm.Vm.PlacementsOf.label_14_at)) fun st2 hm2 hpc2 hb2 hd2 hr2 ↦ ?_
  have g9 := hm2.regs .X9 _ rfl
  have g10 := hm2.regs .X10 _ rfl
  sym_simp at g9 g10
  simp only [PcOk] at hpc2
  refine .done _ ⟨hpc2.trans (hp.label (j := NativeRustcVmArm.Vm.PlacementsOf.b22Offset) NativeRustcVmArm.Vm.PlacementsOf.label_17_at), hb2, by omega, ?_, ?_, ?_, ?_, ?_, ?_,
    fun c hc ↦ ?_, fun c hc ↦ absurd hc (Nat.not_lt_zero _)⟩
  · show (st2.data.regs.getXReg .X9).toBitVec.toNat = _; rw [g9]; rfl
  · show (st2.data.regs.getXReg .X10).toBitVec = _
    rw [g10]
    show (st1.data.regs.getXReg .X20).toBitVec + _ = _
    rw [e1 .X20 (by simp)]
    show st.data.regs.X20.toBitVec + _ = _
    rw [hI.x20]
  · show (st2.data.regs.getXReg .X8).toBitVec.toNat = _
    rw [hr2 .X8 rfl, x8, UInt64.toNat_toBitVec,
      BuildLayout.toNat_toUInt64' (by have := hF.sumF_le (keyF (κ m0) 4); omega)]
  · refine (I2.keep' hI).of ?_ ?_ ?_ ?_
    · rw [hr2 .X19 rfl, e1 .X19 (by simp)]
    · rw [hr2 .X20 rfl, e1 .X20 (by simp)]
    · rw [hr2 .X23 rfl, e1 .X23 (by simp)]
    · rw [hr2 .X24 rfl, e1 .X24 (by simp)]
  · rw [show st2.data.regs.X21 = st.data.regs.X21 from
      (hr2 .X21 rfl).trans (e1 .X21 (by simp))]; exact hI.x21
  · rw [show st2.data.regs.X25 = st.data.regs.X25 from
      (hr2 .X25 rfl).trans (e1 .X25 (by simp))]; exact hI.x25
  · have hq := List.idxOf_lt_length_of_mem hc
    have := hI.done _ hq (by omega)
    rw [List.getElem_idxOf] at this
    rw [hd2, hd1]; exact this

end

end NativeRustcVmArm.Layout.PlacementsOf
