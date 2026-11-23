module

public import NativeRustcVmX64.Layout.PlacementsOf.Mid

/-!
# `placements_of` on x86-64: the second loop (`b16` to `b19`)

At `.L10` (`I2 m0 i`) the offsets of the first `i` stacked columns are copied into `offsets`; a
turn (`turn2`, `b16`, `b17`) copies the `i`th, `loop2` all `94`; `b18` loads the `q_keccak`
column's offset (column `4`), `b19` starts the third loop at column `0` (`to3`, `I3 m0 0`).
-/

namespace NativeRustcVmX64.Layout.PlacementsOf

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.PlacementsOf NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeRustcVmX64.Layout.BuildFrame
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf)

@[expose] public section

section
variable [Labels]

/-- **The third loop** at `.L16`: the placements of the columns below `c` written. -/
structure I3 (m0 : MachineData) (c : Nat) (d : MachineData) : Prop where
  b : B m0 8 d
  le : c ≤ 158
  rax : (reg d .rax).toNat = c
  rbx : reg d .rbx = off (pp m0) (24 * c + 16)
  r15 : (reg d .r15).toNat = sumF (κ m0) (keyF (κ m0) 4)
  rbp : reg d .rbp = rodataAddr .keccakSlot
  r12 : reg d .r12 = rodataAddr .keccakOutput
  r14 : reg d .r14 = kk m0
  tot : WordAt d.dmem (off (fb m0) 8) (log2Ceil (sumF (κ m0) 0)).toUInt64
  offs : ∀ c' ∈ blockList, WordAt d.dmem (off (fb m0) (16 + 8 * c'))
    (sumF (κ m0) (keyF (κ m0) c')).toUInt64
  pl : ∀ c' < c, PlacementWAt d.dmem (off (pp m0) (24 * c')) (plF (κ m0) c')

end

end

public section

variable [Host] {k : Nat} {m0 : MachineData}

/-- **A turn of the second loop**: the offset of stacked column `i` copied into `offsets`. -/
theorem turn2 (hp : Placed code k) (hF : Facts m0) {i : Nat} (hi : i < 94) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b16Offset)) (hI : I2 m0 i st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (i + 1 < 94 ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b16Offset) ∧
      I2 m0 (i + 1) s.data) ∨ (i + 1 = 94 ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b18Offset) ∧ I2 m0 94 s.data)) st := by
  have hrsp := hF.rsp
  have hbl : i < blockList.length := by rw [blockList_length]; exact hi
  set c := blockList[i] with hc
  have hc158 : c < 158 := lt_of_mem_blockList (List.getElem_mem _)
  have hfb := hF.fb_toNat
  -- `b16`: `c = block_cols[i]`
  have p0 := hF.part (o := 1280 + 8 * i) (l := 8) hI.b (by omega)
  have hwf0 := Env.wf_of (env := Env.ofMachine st.data [(off (fb m0) (1280 + 8 * i), 8)]
    (fun _ ↦ 0) 0) ⟨⟨p0.1, p0.2⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm0 : Match (Env.ofMachine st.data [(off (fb m0) (1280 + 8 * i), 8)] (fun _ ↦ 0) 0)
      (rdS (-1272)) st.data := by
    refine match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨?_, trivial⟩
    beta_reduce
    rw [idx_eval]
    show reg st.data .rsp + BitVec.ofNat 64 (8 * (reg st.data .rax).toNat) =
      off (fb m0) (1280 + 8 * i) + BitVec.ofInt 64 (-1272)
    rw [show reg st.data .rsp = _ from hI.b.fr.sp, hI.rax, add_m1272, off_sub _ (by omega)
      (by omega), off_add, show 1280 + 8 * i - 1272 = 8 + 8 * i by omega]
  obtain ⟨hok16, hmem16, hcx16, hK16⟩ := ok_b16
  refine stepR (b16_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b16 nofun hpc hI.b hwf0 hm0
    hok16 hmem16 fun st1 hm1 hpc1 hb1 hd1 ↦ ?_
  have hld : ((Sym.load 0 0 8).eval (Env.ofMachine st.data [(off (fb m0) (1280 + 8 * i), 8)]
      (fun _ ↦ 0) 0)) = c.toUInt64.toBitVec :=
    load_ofMachine (o := 0) rfl (by rw [off_zero]; exact hI.cols i hi)
  have hc64 : c.toUInt64.toBitVec.toNat = c := toNat_toUInt64 (by omega)
  simp only [PcOk] at hpc1
  obtain ⟨-, hno1⟩ := pc_of (P := ¬ c < 158) hpc1 (by
    rw [SBool.eval, ult_eval, hld, hc64, decide_not]; rfl)
  have hK1 := fun r (hr : r ∈ Reg64.rax :: cs) ↦ kreg hm1 hK16 hr
  have hcx1 : (reg st1.data .rcx).toNat = c := by
    show (st1.data.regs.get64 .rcx).toNat = _; rw [hm1.regs .rcx _ hcx16, hld, hc64]
  -- `b17`: `offsets[c] = block_offsets[i]`
  have pa := hF.part (o := 3808 + 8 * i) (l := 8) hb1 (by omega)
  have pb := hF.part (o := 16 + 8 * c) (l := 8) hb1 (by omega)
  let env := Env.ofMachine st1.data [(off (fb m0) (3808 + 8 * i), 8),
    (off (fb m0) (16 + 8 * c), 8)] (fun _ ↦ 0) 0
  have hwf : env.WF := Env.wf_of ⟨⟨pa.1, pa.2⟩, ⟨pb.1, pb.2⟩, trivial⟩
    (List.pairwise_pair.mpr (hF.part_apart (by omega) (by omega) (by omega)))
  have hm : Match env st17 st1.data := by
    refine match_ofMachine ⟨rfl, rfl, trivial⟩ trivial trivial trivial ⟨?_, ?_, trivial⟩
    · beta_reduce
      rw [idx_eval]
      show reg st1.data .rsp + BitVec.ofNat 64 (8 * (reg st1.data .rax).toNat) =
        off (fb m0) (3808 + 8 * i) + BitVec.ofInt 64 (-3800)
      rw [show reg st1.data .rsp = _ from hb1.fr.sp, hK1 .rax (by simp), hI.rax, add_m3800,
        off_sub _ (by omega) (by omega), off_add, show 3808 + 8 * i - 3800 = 8 + 8 * i by omega]
    · beta_reduce
      rw [idx_eval]
      show reg st1.data .rsp + BitVec.ofNat 64 (8 * (reg st1.data .rcx).toNat) =
        off (fb m0) (16 + 8 * c) + BitVec.ofInt 64 (-8)
      rw [show reg st1.data .rsp = _ from hb1.fr.sp, hcx1, add_m8,
        off_sub _ (by omega) (by omega), off_add, show 16 + 8 * c - 8 = 8 + 8 * c by omega]
  refine exec_at (b17_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b17 hwf nofun
    ((hno1 (by omega)).trans rfl) hm fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hok17, hw17, hv17, hax17, hK17⟩ := ok_b17
  have hok' := hok17
  simp only [AOk, Bool.and_eq_true] at hok'
  have hwr : ∀ q, Written env (after b17 st17) q →
      ∃ x, x < 8 ∧ q = off (off (fb m0) (16 + 8 * c)) x := fun q h ↦ by
    obtain ⟨w, hw, b, sz, hb', hin⟩ := written_in hwf hm2 hok'.2 h
    rw [hw17 w hw] at hb'
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb'
    obtain ⟨rfl, rfl⟩ := hb'
    rw [inRange_iff' pb.2] at hin
    refine ⟨q.toNat - (off (fb m0) (16 + 8 * c)).toNat, by omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [toNat_off (by have := q.isLt; omega)]
    omega
  have hb2 : B m0 8 st2.data := hb1.of_written hF.stack (by decide) hwf hm2 hok17 (L := 5072)
    (by decide) slots_ge slots_le fun q h ↦ by
      obtain ⟨x, hx, rfl⟩ := hwr q h
      rw [off_off]
      exact Or.inr (hF.part_low (o := 16 + 8 * c + x) (l := 1) (by omega)
        (by have := inRange_off_self (b := off (fb m0) (16 + 8 * c + x)) (N := 1) (j := 0)
              (by omega) (by omega)
            rwa [off_zero] at this))
  have keep : ∀ {o : Nat} {v : UInt64}, (o + 8 ≤ 16 + 8 * c ∨ 16 + 8 * c + 8 ≤ o) → o < 5072 →
      WordAt st1.data.dmem (off (fb m0) o) v → WordAt st2.data.dmem (off (fb m0) o) v := by
    intro o v ho ho' h
    refine bytesAt_congr h fun t ht ↦ ?_
    have ht8 : t < 8 := by simpa [NativeRustcVm.length_wordBytes] using ht
    rw [off_add]
    refine hm2.get?_mem0 hwf fun hw ↦ ?_
    obtain ⟨x, hx, he⟩ := hwr _ hw
    rw [off_off] at he
    have := off_inj (b := fb m0) (N := 5128) hF.fnw (by omega) (by omega) he
    omega
  have hnew : WordAt st2.data.dmem (off (fb m0) (16 + 8 * c)) (sumF (κ m0) (keyF (κ m0) c)).toUInt64 := by
    have := wordAt_write hm2 (r := 1) (o := 0) rfl (by decide) (fun t ht ↦ by simpa using hv17 t ht)
    rw [off_zero] at this
    rwa [show (Sym.load 0 0 8).eval env = (sumF (κ m0) (keyF (κ m0) c)).toUInt64.toBitVec from
      load_ofMachine (o := 0) rfl (by rw [off_zero, hd1]; exact hI.offs i hi),
      UInt64.ofBitVec_toBitVec] at this
  have hK2 := fun r (hr : r ∈ cs) ↦ kreg hm2 hK17 hr
  have hax2 : (reg st2.data .rax).toNat = i + 1 := by
    show (st2.data.regs.get64 .rax).toNat = _
    rw [hm2.regs .rax _ hax17]
    show (BinOp.apply .add .W64 (reg st1.data .rax) (BitVec.ofNat 64 1)).toNat = _
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, hK1 .rax (by simp), hI.rax,
      BitVec.toNat_ofNat]
    omega
  have hnd := blockList_nodup
  have hI2 : I2 m0 (i + 1) st2.data :=
    ⟨hb2, by omega, hax2, by rw [hK2 .r13 (by simp [cs]), hK1 .r13 (by simp [cs])]; exact hI.r13,
      by rw [hK2 .rbp (by simp [cs]), hK1 .rbp (by simp [cs])]; exact hI.rbp,
      by rw [hK2 .r12 (by simp [cs]), hK1 .r12 (by simp [cs])]; exact hI.r12,
      by rw [hK2 .r14 (by simp [cs]), hK1 .r14 (by simp [cs])]; exact hI.r14,
      by rw [hK2 .rbx (by simp [cs]), hK1 .rbx (by simp [cs])]; exact hI.rbx,
      keep (by omega) (by omega) (hd1 ▸ hI.tot),
      fun q hq ↦ keep (by omega) (by omega) (hd1 ▸ hI.cols q hq),
      fun q hq ↦ keep (by omega) (by omega) (hd1 ▸ hI.offs q hq),
      fun q hq hqi ↦ by
        rcases Nat.lt_or_ge q i with h' | h'
        · have hne : blockList[q]'(by rw [blockList_length]; exact hq) ≠ c := fun he ↦ by
            have := (List.Nodup.getElem_inj_iff hnd).mp he
            omega
          have hq158 : blockList[q]'(by rw [blockList_length]; exact hq) < 158 :=
            lt_of_mem_blockList (List.getElem_mem _)
          exact keep (by omega) (by omega) (hd1 ▸ hI.done q hq h')
        · obtain rfl : q = i := by omega
          exact hnew⟩
  simp only [PcOk] at hpc2
  obtain ⟨hy, hno⟩ := pc_of (P := ¬ 94 = i + 1) hpc2 (by
    rw [SBool.eval, eq_eval, decide_not]
    have e1 : ((Sym.reg .r13).eval env).toNat = 94 := by
      show (reg st1.data .r13).toNat = _; rw [hK1 .r13 (by simp [cs])]; exact hI.r13
    have e2 : ((Sym.bin .add .W64 (.reg .rax) (.lit 1)).eval env).toNat = i + 1 := by
      show (BinOp.apply .add .W64 (reg st1.data .rax) (BitVec.ofNat 64 1)).toNat = _
      simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, hK1 .rax (by simp), hI.rax,
        BitVec.toNat_ofNat]
      omega
    rw [e1, e2])
  by_cases hl : i + 1 = 94
  · exact .done _ (.inr ⟨hl, hno (by omega), hl ▸ hI2⟩)
  · exact .done _ (.inl ⟨by omega, (hy (by omega)).trans (hp.label NativeRustcVmX64.Vm.PlacementsOf.label_10_at), hI2⟩)

/-- **The second loop**, to `.L13`'s predecessor `b18`. -/
theorem loop2 (hp : Placed code k) (hF : Facts m0) {i : Nat} (hi : i < 94) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b16Offset)) (hI : I2 m0 i st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b18Offset) ∧ I2 m0 94 s.data) st :=
  Sym.loop (fun n s ↦ ∃ i, i < 94 ∧ 94 - i = n ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b16Offset) ∧ I2 m0 i s.data)
    (fun n s ⟨i, hi, hn, hpc, hI⟩ ↦ Eventually.mono (turn2 hp hF hi hpc hI) fun s' h ↦ by
      rcases h with ⟨hlt, hpc', hI'⟩ | ⟨-, hpc', hI'⟩
      · exact Or.inr ⟨94 - (i + 1), by omega, i + 1, hlt, rfl, hpc', hI'⟩
      · exact Or.inl ⟨hpc', hI'⟩)
    ⟨i, hi, rfl, hpc, hI⟩

/-- **`b18`, `b19`**: the `q_keccak` column's offset, the third loop's head. -/
theorem to3 (hp : Placed code k) (hF : Facts m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b18Offset)) (hI : I2 m0 94 st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b22Offset) ∧ I3 m0 0 s.data) st := by
  obtain ⟨hok18, hmem18, h15, hK18⟩ := ok_b18
  refine step0 hF (b18_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b18 nofun hpc hI.b hok18
    hmem18 fun st1 hm1 hpc1 hb1 hd1 ↦ ?_
  have h4 : (4 : Nat) < 94 := by decide
  have hw4 := hI.done 4 h4 h4
  rw [show blockList[4]'(by rw [blockList_length]; exact h4) = 4 from blockList_get4] at hw4
  have hr15 : (reg st1.data .r15).toNat = sumF (κ m0) (keyF (κ m0) 4) := by
    show (st1.data.regs.get64 .r15).toNat = _
    rw [hm1.regs .r15 _ h15]
    show ((frameEnv m0 st.data 5120 [] (fun _ ↦ 0) 0).load 0 48 8).toNat = _
    rw [load_ofMachine (o := 48) rfl hw4, UInt64.toNat_toBitVec, toNat_toUInt64 (by
      have := Facts.sumF_le' hF (keyF (κ m0) 4); omega)]
  obtain ⟨hok19, hmem19, hax19, hbx19, hK19⟩ := ok_b19
  refine step0 hF (b19_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b19 nofun (hpc1.trans rfl)
    hb1 hok19 hmem19 fun st2 hm2 hpc2 hb2 hd2 ↦ .done _
      ⟨hpc2.trans (hp.label NativeRustcVmX64.Vm.PlacementsOf.label_16_at), ?_⟩
  have hK1 := fun r (hr : r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14]) ↦ kreg hm1 hK18 hr
  have hK2 := fun r (hr : r ∈ [Reg64.rbp, .r12, .r13, .r14, .r15]) ↦ kreg hm2 hK19 hr
  have hd := hd2.trans hd1
  refine ⟨hb2, by omega, by show (st2.data.regs.get64 .rax).toNat = _; rw [hm2.regs .rax _ hax19]; rfl,
    ?_, by rw [hK2 .r15 (by simp)]; exact hr15,
    by rw [hK2 .rbp (by simp), hK1 .rbp (by simp)]; exact hI.rbp,
    by rw [hK2 .r12 (by simp), hK1 .r12 (by simp)]; exact hI.r12,
    by rw [hK2 .r14 (by simp), hK1 .r14 (by simp)]; exact hI.r14, by rw [hd]; exact hI.tot,
    fun c' hc' ↦ ?_, fun c' hc' ↦ absurd hc' (by omega)⟩
  · show st2.data.regs.get64 .rbx = _
    rw [hm2.regs .rbx _ hbx19]
    show BinOp.apply .add .W64 (BitVec.ofNat 64 16) (reg st1.data .rbx) = _
    rw [hK1 .rbx (by simp), hI.rbx]
    simp only [BinOp.apply, low_W64, ext_W64, off, Nat.mul_zero, Nat.zero_add]
    exact BitVec.add_comm _ _
  · obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp hc'
    rw [hd]
    exact hI.done q (by rw [blockList_length] at hq; exact hq) (by rw [blockList_length] at hq; exact hq)

end

end NativeRustcVmX64.Layout.PlacementsOf
