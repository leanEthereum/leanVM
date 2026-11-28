module

public import NativeRustcVmX64.Whir.WhirLevels.Mu
public import NativeRustcVmX64.Code.Vm.NextLevel.Names

/-!
# `whir_levels`: `next_level`'s call (x86-64)

`next_step`: from `MidMu k` at `b5` with a level after `k`, `b5` passes the `TState`, the index `k`,
the level `k` (RBX), the next level's fold and rate exponent (its words at RBX + 24), `μ` (R9) and
the state's address as the stack argument, and calls `next_level`; `b6` tests its `bool` and goes
back to the loop's head with `Head (k + 1)`, or returns `None` (the run rejected).
-/

namespace NativeRustcVmX64.Whir.Levels.WL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.WhirLevels

public section

variable [Host] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat} {k0 : Nat}

/-- **`next_level`** at level `k`: `None` returned, or `Head (k + 1)` at the loop's head. -/
theorem next_step (hp : Placed code k0)
    (hnl : ∀ a s level w rounds, Spec (Labels.label NativeRustcVmX64.Vm.NextLevel.entryLabel)
      (NextLevelPre a s level w rounds) (NextLevelPost a s level w rounds))
    (c : Ctx a s0 levels ba b claim m0 rate) {k : Nat} {s : TState} {w : WhirStateW}
    {rs : Array FoldRoundW} {st : MachineState} (hpc : st.pc = Host.addrOf (k0 + NativeRustcVmX64.Vm.WhirLevels.b5Offset))
    (hmm : MidMu a s0 levels b claim m0 rate k s w rs st.data) (hk1 : k + 1 < levels.length) :
    Eventually (step1 Host.exe) (fun st' ↦ Goal a s0 levels b claim m0 st' ∨
      (st'.pc = Host.addrOf (k0 + NativeRustcVmX64.Vm.WhirLevels.b1Offset) ∧
        ∃ s' w', Head a s0 levels b claim m0 (k + 1) s' w' st'.data)) st := by
  have hm := hmm.mid
  have hl := hm.loop
  have hl6 := c.len_le
  have hadm := admissible_iff.mp c.adm
  have hlog := c.logN_le
  have hlv2 : levelBytes * k + 2 * levelBytes ≤ levelBytes * levels.length := by
    have := Nat.mul_le_mul_left levelBytes (show k + 2 ≤ levels.length by omega)
    rw [Nat.mul_add] at this
    omega
  have hin2 := whirIn_sub (o := levelBytes * k) (k := 2 * levelBytes) c.lin hlv2
  let base := lvA m0 + BitVec.ofNat 64 (levelBytes * k)
  let env := frameEnv m0 st.data 112 [(base, 48)] (fun _ ↦ 0) (Host.addrOf (k0 + NativeRustcVmX64.Vm.WhirLevels.b6Offset)).toBitVec
  have hwf : env.WF := c.wf hl.fr.frame.kept (fun x hx ↦ by
      rw [List.mem_singleton] at hx; subst hx
      exact ⟨Mapped.keeps hin2.1.1 hl.fr.frame.kept, hin2.1.2⟩)
    (List.pairwise_pair.mpr (c.apart_fa hin2.2))
  have hmS : Match env nxS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hl.fr.frame.rsp_eval, known_ptr rfl hl.rbx, trivial⟩
      trivial trivial trivial
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf (fun _ _ ↦ rfl) hpc hmS
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid, hlow, harg, krbp, kr15, krdi, krsi, krdx, krcx, kr8, kr9, kr12, kr13, kr14⟩ := ok_b5
  obtain ⟨hf2, hs2⟩ := c.blk hl.fr hwf hm2 hmid (hi := 16) (by omega) hlow
  have hat := c.at_call hf2
  have hsm2 := hf2.same
  have e : ∀ {r : Reg64} {v : Sym}, (after b5 nxS).reg r = some v →
      reg st2.data r = v.eval env := fun h ↦ hm2.regs _ _ h
  have hrsp2 : rspOf st2.data = fa m0 := by rw [hf2.frame.sp, off_zero]
  -- the stack argument
  have hargW : NativeRustcVm.WordAt st2.data.dmem (off (fa m0) 8) (UInt64.ofBitVec (pA m0)) := by
    exact wordAt_written hm2 (r := 0) (o := 8) rfl (by omega) harg
      (w := UInt64.ofBitVec (pA m0)) hl.rbp
  have hpa : stackArg st2.data 0 = pA m0 := by
    show (NativeRustcVm.wordOf st2.data.dmem (rspOf st2.data + BitVec.ofNat 64 (8 + 8 * 0))).toBitVec
      = _
    rw [hrsp2, show fa m0 + BitVec.ofNat 64 (8 + 8 * 0) = off (fa m0) 8 from rfl,
      NativeRustcVm.wordOf_of_wordAt hargW]
  have hfa := c.fa_toNat
  have := c.hN
  have := frame_le
  have hargs : ArgsOk st2.data 1 := by
    refine ⟨fun i hi ↦ ?_, ?_⟩
    · rw [hrsp2, show fa m0 + 8#64 + BitVec.ofNat 64 i = fa m0 + BitVec.ofNat 64 (8 + i) by
        rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add]]
      exact (c.frame_ok hf2.frame.kept).1 _ (by omega)
    · rw [hrsp2, hfa]; have := c.sp8; omega
  have hargT : NativeRustcVm.Apart (rspOf st2.data + 8#64) 8 (tA m0) tstateBytes := by
    have h := c.apart_fa c.wt.2.2.2.1.1
    rw [hrsp2]
    exact NativeRustcVm.Apart.mono h (by rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega)
      (by rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega) le_rfl le_rfl
  have hargP : NativeRustcVm.Apart (rspOf st2.data + 8#64) 8 (pA m0) whirBytes := by
    have h := c.apart_fa c.pout.1.2.2.2.2.1
    rw [hrsp2]
    exact NativeRustcVm.Apart.mono h (by rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega)
      (by rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega) le_rfl le_rfl
  -- the registers
  have ht : reg st2.data .rdi = tA m0 := (e krdi).trans hl.r15
  have hdx : reg st2.data .rdx = base := (e krdx).trans (eval_ptr rfl)
  have hlvk := c.levelAt hsm2 (k := k) (by omega)
  have hlvk1 : LevelAt st2.data.dmem (off base 24) (lvl (logN m0) rate (k + 1)) := by
    have := c.levelAt hsm2 (k := k + 1) hk1
    rwa [show lvA m0 + BitVec.ofNat 64 (levelBytes * (k + 1)) = off base 24 by
      show _ = lvA m0 + BitVec.ofNat 64 (levelBytes * k) + BitVec.ofNat 64 24
      rw [NativeRustcVm.addr_add_add]; rfl] at this
  have hst : LevelAt st.data.dmem (off base 24) (lvl (logN m0) rate (k + 1)) := by
    have := c.levelAt hl.fr.same (k := k + 1) hk1
    rwa [show lvA m0 + BitVec.ofNat 64 (levelBytes * (k + 1)) = off base 24 by
      show _ = lvA m0 + BitVec.ofNat 64 (levelBytes * k) + BitVec.ofNat 64 24
      rw [NativeRustcVm.addr_add_add]; rfl] at this
  obtain ⟨hw0, hw1⟩ := NativeRustcVm.wordsAt_cons_iff.mp hst.2.2.2
  have hw1' := (NativeRustcVm.wordsAt_cons_iff.mp hw1).1
  have hcx : (reg st2.data .rcx).toNat = foldAt (k + 1) := by
    have h0 : NativeRustcVm.WordAt st.data.dmem (off base 24) (foldAt (k + 1)).toUInt64 := hw0
    rw [e krcx, Sym.eval, load_ofMachine (o := 24) (r := 1) rfl h0]
    have : foldAt (k + 1) = 4 := by unfold foldAt; simp
    show (BitVec.ofNat 64 (foldAt (k + 1))).toNat = _
    rw [BitVec.toNat_ofNat]; omega
  have h8 : (reg st2.data .r8).toNat = rate + 3 * (k + 1) := by
    have h1 : NativeRustcVm.WordAt st.data.dmem (off base 32) (rate + 3 * (k + 1)).toUInt64 := by
      have := hw1'
      rw [off_add] at this
      exact this
    rw [e kr8, Sym.eval, load_ofMachine (o := 32) (r := 1) rfl h1]
    show (BitVec.ofNat 64 (rate + 3 * (k + 1))).toNat = _
    rw [BitVec.toNat_ofNat]; omega
  have h9 : (reg st2.data .r9).toNat = logN m0 - w.alphas.size := by
    rw [e kr9]; exact hmm.r9
  have hsi : (reg st2.data .rsi).toNat = k := by
    rw [e krsi]
    show (reg st.data .r13 + BitVec.ofNat 64 1).toNat = k
    rw [hl.r13, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.sub_add_cancel,
      BitVec.toNat_ofNat]
    omega
  have hle := next_le
  have hlv := level_le (show k < levels.length by omega)
  have hpre : NextLevelPre a s (lvl (logN m0) rate k) w rs st2.data := by
    refine ⟨?_, hargs, ?_, by have := hm.roots; omega, ?_, ?_, ?_, ?_, qAt_le _ _ _, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ht]; exact c.whirT hat hsm2 hle
    · rw [ht]; exact c.ts_frame (by omega) (hm2.kept hwf) hs2 hm.ts
    · rw [hpa]
      exact WhirAt.of_same hm.wa (c.same_frame (by omega) hs2)
    · rw [hdx]; exact hlvk
    · show foldAt k ≤ roundCap
      unfold foldAt roundCap; split_ifs <;> omega
    · show rate + 3 * k < 64
      omega
    · rw [hcx]; unfold foldAt; split_ifs <;> omega
    · rw [h8]; omega
    · rw [h9]; unfold stackCap; omega
    · rw [hm.glued]; unfold gluedCap; omega
    · rw [ht, hpa]; exact c.whirOut hat hle c.pout
    · rw [hdx]; exact c.whirIn hat hle (whirIn_sub c.lin hlv)
    · rw [hdx, hpa]; exact apart_sub c.lp c.lin.1.2 hlv
    · rw [hdx, ht]; exact apart_sub c.lt c.lin.1.2 hlv
    · rw [ht]; exact hargT
    · rw [hpa]; exact hargP
    · rw [ht, hpa, hdx, hrsp2]
      apply c.got_call hat hsm2 hle (by decide)
      intro ar har
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with (rfl | rfl | rfl | rfl | rfl) | har
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
      · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
      · exact ⟨(pA m0, whirBytes), by simp, le_rfl, le_rfl⟩
      · exact c.got_level (by omega)
      · exact c.got_loc (j := 8) (n := 8) (by omega)
      · exact ⟨ar, by simp [har], le_rfl, le_rfl⟩
  rw [show k0 + NativeRustcVmX64.Vm.WhirLevels.b5Offset + b5.length = k0 + NativeRustcVmX64.Vm.WhirLevels.b6Offset from rfl] at hpc2
  refine call_then hpc2 (hnl a s _ w rs) hpre fun st3 hpc3 hrsp3 hq ↦ ?_
  obtain ⟨hok, hnext, hwa', hch, hsv⟩ := hq
  have hrs : ∀ q, NativeRustcVm.InAny [⟨stackArg st2.data 0, whirBytes⟩,
      ⟨reg st2.data .rdi, tstateBytes⟩] q → outs m0 q := by
    intro q hq; rw [hpa, ht] at hq; exact inAny_outs hq
  obtain ⟨hf3, hkeep⟩ := c.call hf2 hle hsv hrsp3 hrs hch
  have hcs : ∀ r, calleeSaved r = true → reg st3.data r = reg st2.data r := hsv.1
  have hkw : ∀ {o : Nat} {u : UInt64}, 16 ≤ o → o + 8 ≤ 112 →
      NativeRustcVm.WordAt st.data.dmem (off (fa m0) o) u →
      NativeRustcVm.WordAt st3.data.dmem (off (fa m0) o) u := fun ho ho' hw ↦ by
    have hw2 := keepW hwf hm2 (writesIn_of_mid hmid) (by omega)
      (fun w hw _ ↦ Or.inl (by have := (hlow w hw).2; omega)) hw
    exact bytesAt_congr hw2 fun i hi ↦ by
      rw [off_add]
      exact hkeep _ (by simp [NativeRustcVm.length_wordBytes] at hi; omega)
  rw [hsi, hcx, h8, h9] at hok hnext hwa'
  rw [ht] at hnext
  rw [hpa] at hwa'
  have e' : nextLevelM k (lvl (logN m0) rate k) ⟨foldAt (k + 1), rate + 3 * (k + 1), 0⟩
      (logN m0 - w.alphas.size) w rs =
      nextLevelM k (lvl (logN m0) rate k) (lvl (logN m0) rate (k + 1))
        (logN m0 - w.alphas.size) w rs := rfl
  rw [e'] at hok hnext hwa'
  have hrun := hm.nxt hk1
  -- `b6`
  let env3 := frameEnv m0 st3.data 112 [] (fun _ ↦ 0) 0
  have hwf3 : env3.WF := c.wf hf3.frame.kept (by simp) (List.pairwise_singleton _ _)
  have hm3 : Match env3 retS st3.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hf3.frame.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) exit_b6 hwf3 nofun hpc3 hm3
    fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hmem4, ⟨k12', k13', k15'⟩, krbp', krbx'⟩ := ok_b6
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 hmem4
  have hf4 : Fr m0 8 st4.data :=
    ⟨Frame.of_block hf3.frame hwf3 hm4 hmid4 slots_le, by rw [Sm, hd4]; exact hf3.same⟩
  simp only [PcOk, c6_eval] at hpc4
  have hal : (env3.regs .rax).toNat % 256 = (okWord ((nextLevelM k (lvl (logN m0) rate k)
      (lvl (logN m0) rate (k + 1)) (logN m0 - w.alphas.size) w rs).run s).isSome).toNat := hok
  rcases hres : (nextLevelM k (lvl (logN m0) rate k) (lvl (logN m0) rate (k + 1))
      (logN m0 - w.alphas.size) w rs).run s with _ | ⟨w', s'⟩
  · rw [hres] at hal
    simp only [hal, okWord, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, UInt64.toNat_zero,
      decide_true, Bool.not_true] at hpc4
    rw [show k0 + NativeRustcVmX64.Vm.WhirLevels.b6Offset + b6.length = k0 + NativeRustcVmX64.Vm.WhirLevels.b7Offset from rfl] at hpc4
    rw [hres] at hrun
    exact Eventually.mono (none_exit hp c hf4 hpc4 hrun) fun _ h ↦ Or.inl h
  · rw [hres] at hal
    simp only [hal, okWord, Option.isSome_some, ↓reduceIte] at hpc4
    rw [show (decide ((1 : UInt64).toNat = 0)) = false from rfl] at hpc4
    simp only [Bool.not_false, ↓reduceIte] at hpc4
    obtain ⟨ha', hg', hr'⟩ := nextLevelM_facts hres
    have hwa'' := hwa' w' s' hres
    have hts' := hnext w' s' hres
    rw [hres] at hrun
    have e4 : ∀ {r : Reg64} {v : Sym}, (after b6 retS).reg r = some v →
        reg st4.data r = v.eval env3 := fun h ↦ hm4.regs _ _ h
    refine .done _ (Or.inr ⟨hpc4.trans (hp.label NativeRustcVmX64.Vm.WhirLevels.label_1_at), s', w',
      ⟨hf4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, hk1, ?_, ?_, ?_, ?_⟩)
    · rw [e4 krbx']
      show reg st3.data .r14 = _
      rw [hcs .r14 rfl, e kr14, Sym.eval, show env.base 1 = base from rfl]
      show base + BitVec.ofInt 64 24 = _
      show lvA m0 + BitVec.ofNat 64 (levelBytes * k) + BitVec.ofNat 64 24 = _
      rw [NativeRustcVm.addr_add_add]
      rfl
    · rw [e4 k12']
      show reg st3.data .r12 = _
      rw [hcs .r12 rfl, e kr12]
      show BitVec.ofNat 64 18446744073709551592 + reg st.data .r12 = _
      rw [hl.r12]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, levelBytes]
      omega
    · rw [e4 k13']
      show reg st3.data .r13 = _
      rw [hcs .r13 rfl, e kr13]
      show reg st.data .r13 + BitVec.ofNat 64 1 = _
      rw [hl.r13]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · rw [e4 k15']
      show reg st3.data .r15 = _
      rw [hcs .r15 rfl, e kr15]; exact hl.r15
    · rw [e4 krbp']
      show reg st3.data .rbp = _
      rw [hcs .rbp rfl, e krbp]; exact hl.rbp
    · rw [hd4]; exact hkw (by omega) (by omega) hl.w24
    · rw [hd4]; exact hkw (by omega) (by omega) hl.w32
    · rw [hd4]; exact hkw (by omega) (by omega) hl.w40
    · rw [hd4]; exact hkw (by omega) (by omega) hl.w48
    · rw [hd4]; exact hkw (by omega) (by omega) hl.w56
    · rw [hd4]; exact hts'
    · rw [hd4]; exact hwa''.1
    · rw [ha', hm.alphas]
    · rw [hg', hm.glued]; omega
    · have := hm.roots; omega
    · exact hrun

end

end NativeRustcVmX64.Whir.Levels.WL
