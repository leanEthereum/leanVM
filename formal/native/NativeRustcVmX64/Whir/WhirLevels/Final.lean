module

public import NativeRustcVmX64.Whir.WhirLevels.Mu
public import NativeRustcVmX64.Code.Vm.FinalLevel.Names

/-!
# `whir_levels`: the tail call of `final_level` (x86-64)

`b8` (`NativeRustcVmX64.Vm.WhirLevels.label_6`) passes the `TState`, the last level's index (the frame's word `24`) and
address, `μ`, `laneFolds`, the basis, restores the registers and RSP (`Frame.tail`) and jumps to
`final_level`, whose stack argument is the function's own (the state's address above the return
address); its contract ends the function (`final_tail`).
-/

namespace NativeRustcVmX64.Whir.Levels.WL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.WhirLevels

public section

/-- The variables left at the last level fit its lanes. -/
theorem lanes_fit {μ k : Nat} (h16 : 16 ≤ μ) (h30 : μ ≤ 30) (hk : k + 1 = nOf μ) :
    2 ^ (μ - alphasAt (k + 1)) + foldAt k ≤ laneCap := by
  have h5 := mu_final h16 h30
  rw [← hk] at h5
  have : 2 ^ (μ - alphasAt (k + 1)) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) h5
  have : foldAt k ≤ 6 := by unfold foldAt; split_ifs <;> omega
  unfold laneCap
  omega

theorem stackBelow_zero (m : MachineData) : stackBelow m 0 = rspOf m := by
  simp [stackBelow]

variable [Host] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat} {k0 : Nat}

/-- **The tail call of `final_level`** at the last level `k`. -/
theorem final_tail (hp : Placed code k0)
    (hfl : ∀ a s level ba b w rounds, Spec (Labels.label NativeRustcVmX64.Vm.FinalLevel.entryLabel)
      (FinalLevelPre a s level ba b w rounds) (FinalLevelPost a s level b w rounds))
    (c : Ctx a s0 levels ba b claim m0 rate) {k : Nat} {s : TState} {w : WhirStateW}
    {rs : Array FoldRoundW} {st : MachineState} (hpc : st.pc = Host.addrOf (k0 + NativeRustcVmX64.Vm.WhirLevels.b8Offset))
    (hmm : MidMu a s0 levels b claim m0 rate k s w rs st.data) (hk : k + 1 = levels.length) :
    Eventually (step1 Host.exe) (Goal a s0 levels b claim m0) st := by
  have hm := hmm.mid
  have hl := hm.loop
  have hl6 := c.len_le
  have hadm := admissible_iff.mp c.adm
  have hlog := c.logN_le
  have hlv := level_le (show k < levels.length by omega)
  have hwf := c.wf (d := st.data) (rest := []) (ret := 0) hl.fr.frame.kept (by simp)
    (List.pairwise_singleton _ _)
  have hmS : Match (frameEnv m0 st.data 112 [] (fun _ ↦ 0) 0) retS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hl.fr.frame.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) exit_b8 hwf nofun hpc hmS
    fun st1 hm1 hpc1 ↦ ?_
  have hok := ok_b8
  obtain ⟨hsv, hrsp, hd⟩ := Frame.tail hl.fr.frame hwf hm1 hok
  obtain ⟨-, -, -, -, krdi, krsi, krdx, krcx, kr8, kr9⟩ := hok
  have e : ∀ {r : Reg64} {v : Sym}, (after b8 retS).reg r = some v →
      reg st1.data r = v.eval (frameEnv m0 st.data 112 [] (fun _ ↦ 0) 0) :=
    fun h ↦ hm1.regs _ _ h
  have hsm1 : Sm m0 st1.data := by rw [Sm, hd]; exact hl.fr.same
  have hat : At m0 0 st1.data := ⟨by rw [hrsp, stackBelow_zero], hsv.2, c.rc_keep hsm1⟩
  have hle : 0 + finalLevelStack ≤ whirLevelsStack := by have := final_le; omega
  have ht : reg st1.data .rdi = tA m0 := (e krdi).trans hl.r15
  have hpa : stackArg st1.data 0 = pA m0 := by
    have := c.arg_keep hsm1
    show (NativeRustcVm.wordOf st1.data.dmem (rspOf st1.data + BitVec.ofNat 64 (8 + 8 * 0))).toBitVec
      = _
    rw [hrsp, show rspOf m0 + BitVec.ofNat 64 (8 + 8 * 0) = rspOf m0 + 8#64 from rfl,
      NativeRustcVm.wordOf_of_wordAt this]
  have hdx : reg st1.data .rdx = lvA m0 + BitVec.ofNat 64 (levelBytes * k) := (e krdx).trans hl.rbx
  have hsi : (reg st1.data .rsi).toNat = k := by
    rw [e krsi, Sym.eval, load_ofMachine (o := 24) rfl hl.w24]
    show (BitVec.ofNat 64 (levels.length - 1)).toNat = k
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hcx : (reg st1.data .rcx).toNat = logN m0 - w.alphas.size := by
    rw [e krcx]; exact hmm.r9
  have h8 : (reg st1.data .r8).toNat = lf m0 := by
    rw [e kr8, Sym.eval, load_ofMachine (o := 32) rfl hl.w32]
  have h9 : reg st1.data .r9 = bA m0 := by
    rw [e kr9, Sym.eval, load_ofMachine (o := 40) rfl hl.w40]
  have hal := hm.alphas
  have hargs : ArgsOk st1.data 1 :=
    ⟨by rw [hrsp]; exact Mapped.keeps c.args.1 hsv.2, by rw [hrsp]; exact c.args.2⟩
  have hpre : FinalLevelPre a s (lvl (logN m0) rate k) ba b w rs st1.data := by
    refine ⟨?_, hargs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, qAt_le _ _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · rw [ht]; exact c.whirT hat hsm1 hle
    · rw [ht, hd]; exact hm.ts
    · rw [hpa, hd]; exact hm.wa
    · rw [hdx]; exact c.levelAt hsm1 (by omega)
    · rw [h9]; exact c.basis_at hsm1
    · rw [hcx]; omega
    · rw [hcx, hal]; exact lanes_fit hlog.1 hlog.2 (hk.trans c.len_eq)
    · rw [hcx, hal]
      have : alphasAt (k + 1) ≤ 26 := by unfold alphasAt; split_ifs <;> omega
      unfold stackCap; omega
    · show rate + 3 * k < 64
      omega
    · rw [ht, hpa]; exact c.whirOut hat hle c.pout
    · rw [hdx]; exact c.whirIn hat hle (whirIn_sub c.lin hlv)
    · rw [hdx, hpa]; exact apart_sub c.lp c.lin.1.2 hlv
    · rw [hdx, ht]; exact apart_sub c.lt c.lin.1.2 hlv
    · rw [h9, hpa]; exact c.basisIn hat hle c.bp
    · rw [h9, ht]; exact c.basisIn hat hle c.bt
    · rw [h9]; exact c.bap
    · rw [hrsp, ht]; exact c.at'
    · rw [hrsp, hpa]; exact c.ap
    · rw [ht, hpa, hdx, hrsp]
      apply c.got_call hat hsm1 hle (by decide)
      intro ar har
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with (rfl | rfl | rfl | rfl | rfl) | har
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
      · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
      · exact ⟨(pA m0, whirBytes), by simp, le_rfl, le_rfl⟩
      · exact c.got_level (by omega)
      · exact ⟨(rspOf m0 + 8#64, 8), by simp, le_rfl, le_rfl⟩
      · exact ⟨ar, by simp [har], le_rfl, le_rfl⟩
  simp only [PcOk] at hpc1
  refine Eventually.bind (Spec.apply (hfl a s _ ba b w rs) hpc1 hpre) fun st2 ⟨hpc2, hrsp2, hq⟩ ↦
    .done _ ?_
  obtain ⟨h0, hnext, hch, hsv2⟩ := hq
  rw [hsi, hcx, h8] at h0 hnext
  rw [ht] at hnext
  have hrun := hm.fin hk
  rw [← hrun] at h0 hnext
  have hret : retOf st1.data = retOf m0 := by
    refine retOf_congr hrsp (fun i hi ↦ ?_) fun j hj ↦ ?_
    · have := frame_mapped (F := 112) c.stack frame_le (112 + i) (by omega)
      rwa [show stackBelow m0 112 + BitVec.ofNat 64 (112 + i) = off (stackBelow m0 112) (112 + i)
        from rfl, frame_add] at this
    · rw [hd, ← frame_add]
      exact hl.fr.frame.ret j hj
  refine ⟨hpc2.trans hret, by rw [hrsp2, hrsp], h0, hnext, ?_, hsv.trans hsv2⟩
  refine NativeRustcVm.SameOutside.mono (NativeRustcVm.SameOutside.trans hsm1 hch) fun q hq ↦ ?_
  rcases hq with (hq | hq) | (hq | hq)
  · exact Or.inr hq
  · exact Or.inl (outs_inAny hq)
  · rw [hpa, ht] at hq
    exact Or.inl hq
  · right
    have h1 : stackBelow st1.data finalLevelStack = stackBelow m0 finalLevelStack := by
      unfold stackBelow; rw [hrsp]
    rw [h1] at hq
    have := c.hN
    have := final_le
    have hs1 := stackBelow_toNat (m := m0) (n := finalLevelStack) (by omega)
    have hs2 := c.stk_toNat
    have := c.sp8
    change NativeRustcVm.InRange _ _ _ at hq
    show NativeRustcVm.InRange (stackBelow m0 whirLevelsStack) whirLevelsStack q
    rw [inRange_iff' (n := finalLevelStack) (by unfold NativeRustcVm.NoWrap; rw [hs1]; omega),
      hs1] at hq
    rw [inRange_iff' (n := whirLevelsStack) ((noWrap_stackBelow c.stack).mono (by omega)), hs2]
    omega

end

end NativeRustcVmX64.Whir.Levels.WL
