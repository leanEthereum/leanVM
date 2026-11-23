module

public import NativeRustcVmArm.Whir.FoldRound.Fin1

/-!
# `fold_round`: the end

`tail`: from `b18` (`AtB18`), the claim written (`b18`), the `α` pushed and the round written
(`b19`), the tag and the epilogue (`b21`): `Some` returned.
-/

namespace NativeRustcVmArm.Whir.FoldRound

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.FoldRound

public section

variable [Host] {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData} {k : Nat}

omit [Host] in
/-- A word an environment's block wrote at offset `o` of region `r`. -/
theorem word_write [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o sz : Nat} {b : BitVec 64} (hb : env.regions[r]? = some (b, sz)) (ho : o + 8 ≤ sz)
    {v : Sym} (hw : ∀ i < 8, findWrite r (o + i) S.mem = some (v, i)) {x : UInt64}
    (hx : v.eval env = x.toBitVec) : NativeRustcVm.WordAt m.dmem (b + BitVec.ofNat 64 o) x := by
  have := hm.bytesAt_write hb ho hw
  rw [wordBytes_reg, hx] at this
  exact this

/-- **The end**: `Some` returned. -/
theorem tail (hp : Placed code k) (h : FoldRoundPre a s0 w m0) {st : MachineState} {s5 : TState}
    {u0 v c0 c1 : EW} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRound.b18Offset))
    (hb : AtB18 a s0 w m0 s5 u0 v c0 c1 st.data) :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st := by
  obtain ⟨g1, g2, g3, g4, g5, hN⟩ := push_geo h
  have hNv : foldRoundStack = 800 := rfl
  have hSv : stateBytes = 61152 := rfl
  have htb := hb.tb
  have hlt : w.alphas.size < stackCap := h.2.2.2.1
  have hc30 : w.alphas.size < 30 := hlt
  have hwf := state_wf h htb.fr
  have hm := state_match h htb
  have hcntw := htb.ws.alphas.2.1
  rw [Array.length_toList] at hcntw
  have hcnt : (stateEnv m0 st.data).load 1 16 8 = w.alphas.size.toUInt64.toBitVec :=
    load_word hcntw
  -- `b18`: the claim
  refine exec_at (inf hp b18_in_code (by simp [b18])) run_b18 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  have hcond : (SBool.and (SBool.not (SBool.cmp CmpOp.ult RegWidth.W64 (Sym.load 1 16 8)
      (Sym.lit 29))) (SBool.not (SBool.cmp CmpOp.eq RegWidth.W64 (Sym.load 1 16 8)
      (Sym.lit 29)))).eval (stateEnv m0 st.data) = false := by
    sym_simp
    rw [hcnt, show w.alphas.size.toUInt64.toBitVec = BitVec.ofNat 64 w.alphas.size from rfl]
    rcases Nat.lt_or_ge w.alphas.size 29 with h29 | h29
    · have : (BitVec.ofNat 64 w.alphas.size).ult 29#64 = true := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.alphas.size < 2 ^ 64
          by omega)]
        simp only [decide_eq_true_eq]; omega
      simp [this]
    · rw [show w.alphas.size = 29 by omega]; decide
  rw [hcond] at hpc1
  simp only [Bool.false_eq_true, ↓reduceIte, show k + NativeRustcVmArm.Vm.FoldRound.b18Offset + b18.length = k + NativeRustcVmArm.Vm.FoldRound.b19Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FoldRound.b18_next]] at hpc1
  have hS1 : ∀ w ∈ (after b18 stateS).mem, w.r = 1 ∧ w.off + w.n ≤ 16 := by
    rw [after_eq run_b18]; decide
  rw [after_eq run_b18] at hS1
  have hf1 : FFr m0 st1.data := Fr.ofBlockW htb.fr hm hm1 hwf rfl rfl
    (fun _ h ↦ absurd h (by simp)) rfl (by decide) (pre_hN h) slots_le
    (writeOk_of (F := 208) (slots := slots) (wr := [1]) hm1 (by decide) fun r hr b sz hb i hi ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact Or.inr (Or.inl (NativeRustcVm.inRange_add (by omega) (by omega))))
  -- values read by `b18`
  have hb0 : (stateEnv m0 st.data).base 0 = base m0 208 := rfl
  have l56 := fw_load hb0 hb.fw (o := 56) (v := (p1 w s5 u0).c0) (by simp)
  have l64 := fw_load hb0 hb.fw (o := 64) (v := (p1 w s5 u0).c1) (by simp)
  have l32 := fw_load hb0 hb.fw (o := 32) (v := (p3 s5 v).c0) (by simp)
  have l40 := fw_load hb0 hb.fw (o := 40) (v := (p3 s5 v).c1) (by simp)
  have l24 := fw_load hb0 hb.fw (o := 24) (v := (p4 s5 c0).c1) (by simp)
  have hcl := foldW_claim w s5 u0 v c0 c1
  have v10 : ((Sym.bin .eor .W64 (.bin .eor .W64 (.load 0 56 8) (.bin .eor .W64 (.load 0 32 8)
      (.reg .X28))) (.bin .eor .W64 (.reg .X0) (.reg .X29))).eval (stateEnv m0 st.data)) =
      (foldW w u0 v c0 c1 (alA s5) (beA s5)).claim.c0.toBitVec := by
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, l56, l32, Env.ofMachine_regs]
    rw [show st.data.regs.getXReg .X28 = _ from hb.x28, show st.data.regs.getXReg .X0 = _ from hb.x0,
      show st.data.regs.getXReg .X29 = _ from hb.x29, hcl]
    simp only [UInt64.toBitVec_xor]
    ac_rfl
  have v9 : ((Sym.bin .eor .W64 (.bin .eor .W64 (.load 0 64 8) (.bin .eor .W64 (.load 0 40 8)
      (.load 0 24 8))) (.bin .eor .W64 (.reg .X1) (.reg .X24))).eval (stateEnv m0 st.data)) =
      (foldW w u0 v c0 c1 (alA s5) (beA s5)).claim.c1.toBitVec := by
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, l64, l40, l24, Env.ofMachine_regs]
    rw [show st.data.regs.getXReg .X1 = _ from hb.x1, show st.data.regs.getXReg .X24 = _ from hb.x24,
      hcl]
    simp only [UInt64.toBitVec_xor]
    ac_rfl
  have wc0 := word_write hm1 (r := 1) (o := 0) (sz := 24) rfl (by decide) (by decide) v10
  have wc1 := word_write hm1 (r := 1) (o := 8) (sz := 24) rfl (by decide) (by decide) v9
  have h8 : st1.data.regs.X8 = w.alphas.size.toUInt64 := reg_of hm1 (r := .X8) rfl hcnt
  have h19 : st1.data.regs.X19 = m0.regs.X0 :=
    (reg_of hm1 (r := .X19) (v := .reg .X19) rfl rfl).trans htb.x19
  have h20 : st1.data.regs.X20 = m0.regs.X2 := by
    apply UInt64.toBitVec_inj.mp
    have := reg_val hm1 (r := .X20) rfl
    simp [Sym.eval] at this
    exact this
  have h22 : st1.data.regs.X22 = (alA s5).c1 :=
    (reg_of hm1 (r := .X22) (v := .reg .X22) rfl rfl).trans hb.x22
  have h23 : st1.data.regs.X23 = (beA s5).c1 :=
    (reg_of hm1 (r := .X23) (v := .reg .X23) rfl rfl).trans hb.x23
  have w8 := bytes_block hm1 hwf rfl (o := 8) (n := 8) (by decide) (by decide)
    (NativeRustcVm.length_wordBytes _) (hb.fw 8 (alA s5).c0 (by simp))
  have w16 := bytes_block hm1 hwf rfl (o := 16) (n := 8) (by decide) (by decide)
    (NativeRustcVm.length_wordBytes _) (hb.fw 16 (beA s5).c0 (by simp))
  -- `b19`, `b21`: the push, the round, the tag, the epilogue
  have hwf2 := push_wf h hf1 hc30
  have hm2 := push_match h hf1 h19 h20 h8
  refine exec_at (inf hp b19_in_code (by simp [b19])) run_b19 hwf2 hpc1 hm2 fun st2 hm2' hpc2 ↦ ?_
  simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.FoldRound.b21Offset) NativeRustcVmArm.Vm.FoldRound.label_8_at] at hpc2
  refine exec_at (inf hp b21_in_code (by simp [b21])) (exec_after run_b19 run_b21p) hwf2 hpc2
    hm2' fun st3 hm3 hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  obtain ⟨hret, hsv⟩ := hf1.exit hm3 hwf2 (by decide)
  -- the values `b19` and `b21` write
  have hb0' : (pushEnv m0 st1.data w.alphas.size).base 0 = base m0 208 := rfl
  have la : (Sym.load 0 8 8).eval (pushEnv m0 st1.data w.alphas.size) = (alA s5).c0.toBitVec :=
    load_word (by rw [hb0']; exact w8)
  have lb : (Sym.load 0 16 8).eval (pushEnv m0 st1.data w.alphas.size) = (beA s5).c0.toBitVec :=
    load_word (by rw [hb0']; exact w16)
  have ra : (Sym.reg .X22).eval (pushEnv m0 st1.data w.alphas.size) = (alA s5).c1.toBitVec :=
    congrArg UInt64.toBitVec h22
  have rb : (Sym.reg .X23).eval (pushEnv m0 st1.data w.alphas.size) = (beA s5).c1.toBitVec :=
    congrArg UInt64.toBitVec h23
  have rc : (Sym.bin .add .W64 (.reg .X8) (.lit 1)).eval (pushEnv m0 st1.data w.alphas.size) =
      (w.alphas.size + 1).toUInt64.toBitVec := by
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st1.data.regs.getXReg .X8 = _ from h8]
    show BitVec.ofNat 64 w.alphas.size + BitVec.ofNat 64 1 = BitVec.ofNat 64 (w.alphas.size + 1)
    rw [BitVec.ofNat_add]
  have o0 := word_write hm3 (r := 3) (o := 0) (sz := 40) rfl (by decide) (by decide)
    (x := 1) (show (Sym.lit 1).eval (pushEnv m0 st1.data w.alphas.size) = (1 : UInt64).toBitVec
      from rfl)
  have o8 := word_write hm3 (r := 3) (o := 8) (sz := 40) rfl (by decide) (by decide) la
  have o16 := word_write hm3 (r := 3) (o := 16) (sz := 40) rfl (by decide) (by decide) ra
  have o24 := word_write hm3 (r := 3) (o := 24) (sz := 40) rfl (by decide) (by decide) lb
  have o32 := word_write hm3 (r := 3) (o := 32) (sz := 40) rfl (by decide) (by decide) rb
  have s0' := word_write hm3 (r := 2) (o := 0) (sz := 16) rfl (by decide) (by decide) la
  have s8 := word_write hm3 (r := 2) (o := 8) (sz := 16) rfl (by decide) (by decide) ra
  have n16 := word_write hm3 (r := 1) (o := 16) (sz := 24) rfl (by decide) (by decide) rc
  have c0' := bytes_region hm3 hwf2 (r := 1) rfl (o := 0) (n := 8) (by decide) (by decide)
    (NativeRustcVm.length_wordBytes _) wc0
  have c8 := bytes_region hm3 hwf2 (r := 1) rfl (o := 8) (n := 8) (by decide) (by decide)
    (NativeRustcVm.length_wordBytes _) wc1
  -- what changed
  have hS3 : ∀ w ∈ (after b21 (after b19 pushS)).mem, (w.r = 1 ∧ w.off + w.n ≤ 24) ∨
      (w.r = 2 ∧ w.off + w.n ≤ 16) ∨ (w.r = 3 ∧ w.off + w.n ≤ 40) := by
    rw [after_eq run_b21p]; decide
  rw [after_eq run_b21p] at hS3
  have hs01 : SameOutside st.data.dmem st1.data.dmem (InRange (pA m0) 24) :=
    NativeRustcVm.SameOutside.mono (hm1.sameOutside hwf) fun q hq ↦ by
      obtain ⟨w', hw, b, sz, hb, hin⟩ := written_inRange hwf (fun w hw b sz hb ↦ by
        obtain ⟨hr, hle⟩ := hS1 w hw
        rw [hr] at hb; simp at hb; omega) hq
      obtain ⟨hr, -⟩ := hS1 w' hw
      rw [hr] at hb; simp at hb; obtain ⟨rfl, rfl⟩ := hb
      exact hin
  have hs13 : SameOutside st1.data.dmem st3.data.dmem (fun q ↦ InRange (pA m0) 24 q ∨
      InRange (off (pA m0) (24 + 16 * w.alphas.size)) 16 q ∨ InRange (oA m0) 40 q) :=
    NativeRustcVm.SameOutside.mono (hm3.sameOutside hwf2) fun q hq ↦ by
      obtain ⟨w', hw, b, sz, hb, hin⟩ := written_inRange hwf2 (fun w hw b sz hb ↦ by
        rcases hS3 w hw with ⟨hr, hle⟩ | ⟨hr, hle⟩ | ⟨hr, hle⟩ <;> rw [hr] at hb <;> simp at hb <;>
          omega) hq
      rcases hS3 w' hw with ⟨hr, -⟩ | ⟨hr, -⟩ | ⟨hr, -⟩ <;> rw [hr] at hb <;> simp at hb <;>
        obtain ⟨rfl, rfl⟩ := hb
      · exact Or.inl hin
      · exact Or.inr (Or.inl hin)
      · exact Or.inr (Or.inr hin)
  have hs : SameOutside st.data.dmem st3.data.dmem (fun q ↦ InRange (pA m0) 24 q ∨
      InRange (off (pA m0) (24 + 16 * w.alphas.size)) 16 q ∨ InRange (oA m0) 40 q) :=
    NativeRustcVm.SameOutside.mono (NativeRustcVm.SameOutside.trans hs01 hs13) fun q hq ↦ by
      rcases hq with hq | hq
      · exact Or.inl hq
      · exact hq
  have hnp : NoWrap (pA m0) stateBytes := g1
  have hno : NoWrap (oA m0) 40 := g2
  have sub_p : ∀ q, InRange (pA m0) 24 q ∨ InRange (off (pA m0) (24 + 16 * w.alphas.size)) 16 q →
      InRange (pA m0) stateBytes q := by
    rintro q (hq | hq)
    · exact NativeRustcVm.InRange.mono hq (NativeRustcVm.NoWrap.mono hnp (by omega)) hnp
        (Nat.le_refl _) (by omega)
    · exact NativeRustcVm.InRange.of_sub hq hnp (by omega)
  have hkeep : Kept st.data.dmem st3.data.dmem := fun q hq ↦ hm3.kept hwf2 q (hm1.kept hwf q hq)
  -- the state
  have hws : WhirStateAt st3.data.dmem (pA m0) (foldW w u0 v c0 c1 (alA s5) (beA s5)) := by
    refine htb.ws.fold hlt (NativeRustcVmArm.Whir.agree_of_sameOutside hs fun j hj hW hq ↦ ?_)
      (NativeRustcVm.ewAt_iff.mpr ⟨?_, ?_⟩) n16 ?_
    · have hj' : (off (pA m0) j).toNat = (pA m0).toNat + j :=
        NativeRustcVm.toNat_add_ofNat (by omega)
      have hsl : (off (pA m0) (24 + 16 * w.alphas.size)).toNat =
          (pA m0).toNat + (24 + 16 * w.alphas.size) := NativeRustcVm.toNat_add_ofNat (by omega)
      rcases hq with hq | hq | hq
      · rw [Sym.inRange_iff (show (pA m0).toNat + 24 ≤ 2 ^ 64 by omega), hj'] at hq; omega
      · rw [Sym.inRange_iff (show (off (pA m0) (24 + 16 * w.alphas.size)).toNat + 16 ≤ 2 ^ 64
          by omega), hj', hsl] at hq; omega
      · rw [Sym.inRange_iff (show (oA m0).toNat + 40 ≤ 2 ^ 64 by omega), hj'] at hq; omega
    · rw [← NativeRustcVm.addr_add_zero (pA m0)]; exact c0'
    · exact c8
    · rw [NativeRustcVm.ewAt_iff]
      refine ⟨?_, ?_⟩
      · rw [← NativeRustcVm.addr_add_zero (off (pA m0) _)]; exact s0'
      · exact s8
  -- the `TState`
  have hpo : OutOk m0 (tA m0) a (pA m0) stateBytes foldRoundStack := h.2.2.2.2.1.1
  have hoo : OutOk m0 (tA m0) a (oA m0) 40 foldRoundStack := h.2.2.2.2.2.1.1
  have hfp := htb.ts.footprint
  have hnt : NoWrap (tA m0) tstateBytes := hfp.1.2
  have hnd : NoWrap a.words (8 * a.len) := hfp.2.1.2
  have hts : TStateAt st3.data.dmem (tA m0) a (sq (sq s5).2).2 := by
    refine htb.ts.frame hkeep (fun q hq ↦ ?_) hs
    rcases hq with hq | hq | hq
    · have hq' := sub_p q (.inl hq)
      exact ⟨fun ht ↦ NativeRustcVm.Apart.not_inRange hpo.2.2.1 hnp hnt hq' ht,
        fun hd ↦ NativeRustcVm.Apart.not_inRange hpo.2.2.2.1 hnp hnd hq' hd⟩
    · have hq' := sub_p q (.inr hq)
      exact ⟨fun ht ↦ NativeRustcVm.Apart.not_inRange hpo.2.2.1 hnp hnt hq' ht,
        fun hd ↦ NativeRustcVm.Apart.not_inRange hpo.2.2.2.1 hnp hnd hq' hd⟩
    · exact ⟨fun ht ↦ NativeRustcVm.Apart.not_inRange hoo.2.2.1 hno hnt hq ht,
        fun hd ↦ NativeRustcVm.Apart.not_inRange hoo.2.2.2.1 hno hnd hq hd⟩
  -- the contract
  refine .done _ ⟨hpc3.trans hret, ?_, ?_, hsv⟩
  · rw [hb.model]
    refine ⟨by have := o0; rwa [NativeRustcVm.addr_add_zero] at this, ?_, hws, hts⟩
    rw [NativeRustcVm.ewsAt_cons_iff, NativeRustcVm.ewsAt_singleton_iff, NativeRustcVm.ewAt_iff,
      NativeRustcVm.ewAt_iff, NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add,
      NativeRustcVm.addr_add_add]
    exact ⟨⟨o8, o16⟩, o24, o32⟩
  · refine NativeRustcVm.SameOutside.mono (NativeRustcVm.SameOutside.trans htb.fr.same hs)
      fun q hq ↦ ?_
    rcases hq with (hq | hq | hq | hq) | hq | hq | hq
    · exact Or.inr hq
    · exact Or.inl ⟨_, List.mem_cons_self, hq⟩
    · exact Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hq⟩
    · exact Or.inl ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), hq⟩
    · exact Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, sub_p q (.inl hq)⟩
    · exact Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, sub_p q (.inr hq)⟩
    · exact Or.inl ⟨_, List.mem_cons_self, hq⟩

end

end NativeRustcVmArm.Whir.FoldRound
