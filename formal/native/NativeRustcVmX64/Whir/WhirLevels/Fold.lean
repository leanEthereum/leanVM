module

public import NativeRustcVmX64.Whir.WhirLevels.Entry
public import NativeRustcVmX64.Code.Vm.FoldRounds.Names

/-!
# `whir_levels`: a level's fold rounds (x86-64)

`fold_step`: from `Head k` at the loop's head, `b1` (some level left), `b2` calls
`fold_rounds(t, level.fold, &w.state, &w.rounds)`, `b3` tests its `bool`: `None` returned (the run
rejected) or `Mid k` at `b4`.
-/

namespace NativeRustcVmX64.Whir.Levels.WL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.WhirLevels

public section

theorem roundsOff_le : roundsOff + (8 + roundBytes * roundCap) ≤ whirBytes := by decide

section
variable [Labels] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat}

/-- What is apart from the stack is apart from the frame's region and the return address. -/
theorem Ctx.apart_fa (c : Ctx a s0 levels ba b claim m0 rate) {x : BitVec 64} {n : Nat}
    (h : NativeRustcVm.Apart x n (stackBelow m0 whirLevelsStack) (whirLevelsStack + 8)) :
    NativeRustcVm.Apart (fa m0) 120 x n := by
  have hf := c.fa_toNat
  have hs := c.stk_toNat
  have := c.hN
  have := frame_le
  refine NativeRustcVm.Apart.symm (NativeRustcVm.Apart.mono_right h ?_ ?_) <;> rw [hf, hs] <;>
    omega

/-- The level `k` region is mapped, apart from the frame. -/
theorem Ctx.level_region (c : Ctx a s0 levels ba b claim m0 rate) {d : MachineData}
    (hk' : Kept m0.dmem d.dmem) {k : Nat} (hk : k < levels.length) :
    NativeRustcVm.Mapped d.dmem (lvA m0 + BitVec.ofNat 64 (levelBytes * k)) levelBytes ∧
      NativeRustcVm.NoWrap (lvA m0 + BitVec.ofNat 64 (levelBytes * k)) levelBytes ∧
      NativeRustcVm.Apart (fa m0) 120 (lvA m0 + BitVec.ofNat 64 (levelBytes * k)) levelBytes := by
  have hin := whirIn_sub c.lin (level_le hk)
  exact ⟨Mapped.keeps hin.1.1 hk', hin.1.2, c.apart_fa hin.2⟩

/-- The state's first 24 bytes, mapped, apart from the frame. -/
theorem Ctx.state_region (c : Ctx a s0 levels ba b claim m0 rate) {d : MachineData}
    (hk' : Kept m0.dmem d.dmem) :
    NativeRustcVm.Mapped d.dmem (pA m0) 24 ∧ NativeRustcVm.NoWrap (pA m0) 24 ∧
      NativeRustcVm.Apart (fa m0) 120 (pA m0) 24 := by
  have hp := c.pout.1
  refine ⟨NativeRustcVm.Mapped.mono (Mapped.keeps hp.1 hk') (by decide),
    NativeRustcVm.NoWrap.mono hp.2.1 (by decide), ?_⟩
  exact NativeRustcVm.Apart.mono (c.apart_fa hp.2.2.2.2.1) le_rfl le_rfl le_rfl
    (by unfold whirBytes; omega)

end

variable [Host] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat} {k0 : Nat}

/-- **A level's fold rounds**: from `Head k`, `None` returned or `Mid k` at `b4`. -/
theorem fold_step (hp : Placed code k0)
    (hfr : ∀ a s w, Spec (Labels.label NativeRustcVmX64.Vm.FoldRounds.entryLabel) (FoldRoundsPre a s w)
      (FoldRoundsPost a s w))
    (c : Ctx a s0 levels ba b claim m0 rate) {k : Nat} {s : TState} {w : WhirStateW}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k0 + NativeRustcVmX64.Vm.WhirLevels.b1Offset))
    (hh : Head a s0 levels b claim m0 k s w st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ Goal a s0 levels b claim m0 st' ∨
      (st'.pc = Host.addrOf (k0 + NativeRustcVmX64.Vm.WhirLevels.b4Offset) ∧
        ∃ s' w' rs, Mid a s0 levels b claim m0 rate k s' w' rs st'.data)) st := by
  have hl := hh.loop
  have hk := hh.lt
  have hl6 := c.len_le
  obtain ⟨hlm, hlnw, hlap⟩ := c.level_region hl.fr.frame.kept hk
  let env := frameEnv m0 st.data 112 [(lvA m0 + BitVec.ofNat 64 (levelBytes * k), 24)]
    (fun _ ↦ 0) (Host.addrOf (k0 + NativeRustcVmX64.Vm.WhirLevels.b3Offset)).toBitVec
  have hwf : env.WF := c.wf hl.fr.frame.kept (fun x hx ↦ by
      rw [List.mem_singleton] at hx; subst hx; exact ⟨hlm, hlnw⟩)
    (List.pairwise_pair.mpr hlap)
  have hm : Match env lvS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hl.fr.frame.rsp_eval, known_ptr rfl hl.rbx, trivial⟩
      trivial trivial trivial
  -- `b1`: a level left
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  have hr12 : env.regs .r12 ≠ 0 := by
    show reg st.data .r12 ≠ 0
    rw [hl.r12]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold levelBytes; omega)] at this
    unfold levelBytes at this
    simp at this
    omega
  simp only [PcOk, c1_eval env hr12] at hpc1
  rw [show k0 + NativeRustcVmX64.Vm.WhirLevels.b1Offset + b1.length = k0 + NativeRustcVmX64.Vm.WhirLevels.b2Offset from rfl] at hpc1
  -- `b2`: `fold_rounds`' call
  refine exec_at (env := env) (infix_of b2_in_code (by simp [b2]) hp)
    (exec_after exit_b1 exit_b2) hwf (fun _ _ ↦ rfl) hpc1 hm1 fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid, hlow, ⟨k12, k13, k15⟩, krbp, krbx, krdi, krsi, krdx, krcx⟩ := ok_b2
  obtain ⟨hf2, hs2⟩ := c.blk hl.fr hwf hm2 hmid (hi := 16) (by omega) hlow
  have hat := c.at_call hf2
  have hsm2 := hf2.same
  have ht2 : TStateAt st2.data.dmem (tA m0) a s := c.ts_frame (by omega) (hm2.kept hwf) hs2 hh.ts
  have hw2 : WhirStateAt st2.data.dmem (pA m0) w := WhirStateAt.of_same hh.ws fun j hj ↦
    c.same_frame (by omega) hs2 j (by unfold stateBytes at hj; unfold whirBytes; omega)
  have e : ∀ {r : Reg64} {v : Sym}, (after b2 (after b1 lvS)).reg r = some v →
      reg st2.data r = v.eval env := fun h ↦ hm2.regs _ _ h
  have hdi : reg st2.data .rdi = tA m0 := (e krdi).trans hl.r15
  have hdx : reg st2.data .rdx = pA m0 := (e krdx).trans hl.rbp
  have hcx : reg st2.data .rcx = pA m0 + BitVec.ofNat 64 roundsOff := by
    rw [e krcx]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [show env.regs .rbp = reg st.data .rbp from rfl, hl.rbp]
    rfl
  have hlv := c.levelAt hl.fr.same hk
  have hsi : (reg st2.data .rsi).toNat = foldAt k := by
    rw [e krsi]
    have := (NativeRustcVm.wordsAt_cons_iff.mp hlv.2.2.2).1
    rw [show (Sym.load 1 0 8).eval env = _ from load_ofMachine (o := 0) (r := 1) rfl
      (by rw [off_zero]; exact this)]
    have : foldAt k ≤ 6 := by unfold foldAt; split_ifs <;> omega
    show (BitVec.ofNat 64 (foldAt k)).toNat = foldAt k
    rw [BitVec.toNat_ofNat]
    omega
  have hle := fold_le
  have hro := roundsOff_le
  have hpre : FoldRoundsPre a s w st2.data := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdi]; exact c.whirT hat hsm2 hle
    · rw [hdi]; exact ht2
    · rw [hdx]; exact hw2
    · rw [hsi]; unfold foldAt roundCap; split_ifs <;> omega
    · rw [hsi, hh.alphas]; unfold alphasAt foldAt stackCap; split_ifs <;> omega
    · rw [hdi, hdx]
      have := whirOut_sub (o := 0) (k := stateBytes) c.pout (by decide)
      rw [NativeRustcVm.addr_add_zero] at this
      exact c.whirOut hat hle this
    · rw [hdi, hcx]
      exact c.whirOut hat hle (whirOut_sub c.pout hro)
    · rw [hcx, hdx]
      have hnw : (pA m0).toNat + whirBytes ≤ 2 ^ 64 := c.pout.1.2.1
      have haddr := NativeRustcVm.toNat_add_ofNat (a := pA m0) (i := roundsOff)
        (by have : roundsOff < whirBytes := by decide
            omega)
      apply Or.inr
      rw [haddr]
      exact le_rfl
    · rw [hdi, hdx, hcx]
      apply c.got_call hat hsm2 hle (by decide)
      intro ar har
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with (rfl | rfl | rfl | rfl) | har
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
      · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
      · exact ⟨(pA m0, whirBytes), by simp, le_rfl,
          Nat.add_le_add_left (by decide : stateBytes ≤ whirBytes) _⟩
      · have hnw : (pA m0).toNat + whirBytes ≤ 2 ^ 64 := c.pout.1.2.1
        have hadd := NativeRustcVm.toNat_add_ofNat (a := pA m0) (i := roundsOff) (by omega)
        refine ⟨(pA m0, whirBytes), by simp, ?_⟩
        change (pA m0).toNat ≤ (pA m0 + BitVec.ofNat 64 roundsOff).toNat ∧
          (pA m0 + BitVec.ofNat 64 roundsOff).toNat + (8 + roundBytes * roundCap) ≤
            (pA m0).toNat + whirBytes
        rw [hadd]
        constructor <;> omega
      · exact ⟨ar, by simp [har], le_rfl, le_rfl⟩
  refine call_then hpc2 (hfr a s w) hpre fun st3 hpc3 hrsp3 hq ↦ ?_
  obtain ⟨hok, hsome, hch, hsv⟩ := hq
  have hrs : ∀ q, NativeRustcVm.InAny [⟨reg st2.data .rcx, 8 + roundBytes * roundCap⟩,
      ⟨reg st2.data .rdx, stateBytes⟩, ⟨reg st2.data .rdi, tstateBytes⟩] q → outs m0 q := by
    intro q ⟨r, hr, hq⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · left
      have hq' : NativeRustcVm.InRange (pA m0 + BitVec.ofNat 64 roundsOff)
          (8 + roundBytes * roundCap) q := by rw [← hcx]; exact hq
      exact NativeRustcVm.InRange.of_sub hq' c.pout.1.2.1 hro
    · left
      have hq' : NativeRustcVm.InRange (pA m0) stateBytes q := by rw [← hdx]; exact hq
      exact NativeRustcVm.InRange.mono hq' (NativeRustcVm.NoWrap.mono c.pout.1.2.1 (by decide))
        c.pout.1.2.1 le_rfl
        (by unfold stateBytes whirBytes; omega)
    · right; rw [← hdi]; exact hq
  obtain ⟨hf3, hkeep⟩ := c.call hf2 hle hsv hrsp3 hrs hch
  have hcs : ∀ r, calleeSaved r = true → reg st3.data r = reg st2.data r := hsv.1
  have hrsp2 : rspOf st2.data = fa m0 := by rw [hf2.frame.sp, off_zero]
  have hkw : ∀ {o : Nat} {u : UInt64}, 16 ≤ o → o + 8 ≤ 112 →
      NativeRustcVm.WordAt st.data.dmem (off (fa m0) o) u →
      NativeRustcVm.WordAt st3.data.dmem (off (fa m0) o) u := fun ho ho' hw ↦ by
    have hw2 := keepW hwf hm2 (writesIn_of_mid hmid) (by omega)
      (fun w hw _ ↦ Or.inl (by have := (hlow w hw).2; omega)) hw
    exact bytesAt_congr hw2 fun i hi ↦ by
      rw [off_add]
      exact hkeep _ (by simp [NativeRustcVm.length_wordBytes] at hi; omega)
  have hloop3 : Loop levels m0 k 8 st3.data := by
    refine ⟨hf3, ?_, ?_, ?_, ?_, ?_, hkw (by omega) (by omega) hl.w24,
      hkw (by omega) (by omega) hl.w32, hkw (by omega) (by omega) hl.w40,
      hkw (by omega) (by omega) hl.w48, hkw (by omega) (by omega) hl.w56⟩
    · rw [hcs .rbx rfl, e krbx, eval_ptr rfl]
    · rw [hcs .r12 rfl, e k12]; exact hl.r12
    · rw [hcs .r13 rfl, e k13]; exact hl.r13
    · rw [hcs .r15 rfl, e k15]; exact hl.r15
    · rw [hcs .rbp rfl, e krbp]; exact hl.rbp
  -- `b3`: the `bool` tested
  have hrsp3' : rspOf st3.data = off (fa m0) 8 := hf3.frame.sp
  obtain ⟨hwf3m, hwf3n⟩ := c.state_region hf3.frame.kept
  let env3 := frameEnv m0 st3.data 112 [(pA m0, 24)] (fun _ ↦ 0) 0
  have hwf3 : env3.WF := c.wf hf3.frame.kept (fun x hx ↦ by
      rw [List.mem_singleton] at hx; subst hx; exact ⟨hwf3m, hwf3n.1⟩)
    (List.pairwise_pair.mpr hwf3n.2)
  have hm3 : Match env3 wS st3.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf3.frame.rsp_eval, known_ptr rfl hloop3.rbp, trivial⟩
      trivial trivial trivial
  rw [show k0 + NativeRustcVmX64.Vm.WhirLevels.b2Offset + b2.length = k0 + NativeRustcVmX64.Vm.WhirLevels.b3Offset from rfl] at hpc3
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf3 nofun hpc3 hm3
    fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hmem4, hregs4⟩ := ok_b3
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 hmem4
  have hreg4 : ∀ r v, wS.reg r = some v → reg st4.data r = reg st3.data r := fun r v h ↦
    Match.reg_eq hm3 hm4 h (by unfold SState.reg at h ⊢; rw [hregs4]; exact h)
  have hf4 : Fr m0 8 st4.data :=
    ⟨Frame.of_block hf3.frame hwf3 hm4 hmid4 slots_le, by rw [Sm, hd4]; exact hf3.same⟩
  have hloop4 : Loop levels m0 k 8 st4.data :=
    ⟨hf4, (hreg4 .rbx _ rfl).trans hloop3.rbx, (hreg4 .r12 _ rfl).trans hloop3.r12,
      (hreg4 .r13 _ rfl).trans hloop3.r13, (hreg4 .r15 _ rfl).trans hloop3.r15,
      (hreg4 .rbp _ rfl).trans hloop3.rbp, by rw [hd4]; exact hloop3.w24,
      by rw [hd4]; exact hloop3.w32, by rw [hd4]; exact hloop3.w40,
      by rw [hd4]; exact hloop3.w48, by rw [hd4]; exact hloop3.w56⟩
  simp only [PcOk, c3_eval] at hpc4
  have hal : (env3.regs .rax).toNat % 256 = (okWord ((foldRounds (foldAt k) w).run s).isSome).toNat
    := by rw [← hsi]; exact hok
  have hrun := hh.run
  rw [c.drop_eq hk] at hrun
  rcases hres : (foldRounds (foldAt k) w).run s with _ | ⟨⟨w', rs⟩, s'⟩
  · -- rejected
    rw [hres] at hal
    simp only [hal, okWord, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, UInt64.toNat_zero,
      decide_true] at hpc4
    exact Eventually.mono (none_exit hp c hf4 (hpc4.trans (hp.label NativeRustcVmX64.Vm.WhirLevels.label_5_at))
      (hrun.trans (run_none (level := lvl (logN m0) rate k) hres))) fun _ h ↦ Or.inl h
  · rw [hres] at hal
    simp only [hal, okWord, Option.isSome_some, ↓reduceIte] at hpc4
    rw [show (decide ((1 : UInt64).toNat = 0)) = false from rfl] at hpc4
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc4
    rw [show k0 + NativeRustcVmX64.Vm.WhirLevels.b3Offset + b3.length = k0 + NativeRustcVmX64.Vm.WhirLevels.b4Offset from rfl] at hpc4
    rw [hsi] at hsome
    obtain ⟨hws', hrs', hts'⟩ := hsome w' rs s' hres
    obtain ⟨ha', hg', hr'⟩ := foldRounds_facts hres
    refine .done _ (Or.inr ⟨hpc4, s', w', rs, hloop4, ?_, ⟨?_, ?_⟩, hk, ?_, ?_, ?_,
      fun hk1 ↦ ?_, fun hk1 ↦ ?_⟩)
    · rw [hd4, ← hdi]; exact hts'
    · rw [hd4, ← hdx]; exact hws'
    · rw [hd4]
      show BufRoundsAt st3.data.dmem (pA m0 + BitVec.ofNat 64 roundsOff) _
      rw [← hcx]; exact hrs'
    · rw [ha', hh.alphas, alphasAt_succ]
    · rw [hg', hh.glued]
    · rw [hr']; exact hh.roots
    · rw [List.drop_eq_nil_of_le (by omega)] at hrun
      exact hrun.trans (run_final (level := lvl (logN m0) rate k) hres)
    · rw [c.drop_eq hk1] at hrun ⊢
      exact hrun.trans (run_next (level := lvl (logN m0) rate k) hres)

end

end NativeRustcVmX64.Whir.Levels.WL
