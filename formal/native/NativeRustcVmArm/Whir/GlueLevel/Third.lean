module

public import NativeRustcVmArm.Code.Vm.BufEW230Extend.Names
public import NativeRustcVmArm.Whir.GlueLevel.Second

/-!
# `glue_level`'s second glued claim: its weights

`b8` checks `extend`'s `Some`; `b9` empties the second glued claim's weights and calls
`Buf<EW, 230>::extend` with the query weights. At `b10` (`AtB10`): both new glued claims in place.
-/

namespace NativeRustcVmArm.Whir.GlueLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.GlueLevel
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt EWAt BufEWAt BufWordsAt)
open NativeRustcVm.Transcript (off off_off Agree)

@[expose] public section

/-- The query batch's glued claim. -/
abbrev g2Of (s : WhirStateW) (m0 : MachineData) : GluedClaimW :=
  ⟨lamOf m0 * lamOf m0, s.alphas.size, .induced m0.regs.X3.toNat (glueArgs m0).1 (glueArgs m0).2.1⟩

/-- **At `b10`**, both glued claims in place. -/
structure AtB10 (s : WhirStateW) (m0 m : MachineData) : Prop where
  fr : FR m0 m
  x0 : m.regs.X0 = 1
  x19 : m.regs.getXReg .X19 = m0.regs.X0
  base : Base s (pOf m0) m.dmem
  claim : EWAt m.dmem (off (pOf m0) 0) (claim2 s m0)
  len : WordAt m.dmem (off (pOf m0) gluedOff) (s.glued.size + 1).toUInt64
  g1 : GluedAt m.dmem (off (pOf m0) (o1 s)) (g1Of s m0)
  g2 : GluedAt m.dmem (off (pOf m0) (o2 s)) (g2Of s m0)

end

public section

variable [Host] {k : Nat} {s : WhirStateW} {m0 : MachineData}

/-- **From `b8` to `b10`.** -/
theorem third_step (hp : Placed code k)
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW230Extend.entryLabel) (BufEWExtendPre 230) (BufEWExtendPost 230))
    (hpre : GlueLevelPre s m0) {m : MachineData} (h : AtB8 s m0 m) {R : MachineState → Prop}
    (cont : ∀ m', AtB10 s m0 m' → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.GlueLevel.b10Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GlueLevel.b8Offset)⟩ := by
  have hpre' := hpre
  obtain ⟨hstk, -, hcap, hmu, -, -, hwn, hargs, hpin, -, -, hwin, hapA, -, -, hapW⟩ := hpre'
  let p := pOf m0
  have hn' : s.glued.size ≤ 8 := by have : s.glued.size + 2 ≤ 10 := hcap; omega
  have hsB : stateBytes = 61152 := rfl
  have hpnw : NoWrap p stateBytes := hpin.1.2
  have hto : ∀ j, j < 61152 → (off p j).toNat = p.toNat + j := fun j hj ↦
    toNat_off_state hpnw hj
  have ho2 := o2_eq s
  have ho1 := o1_eq s
  have hgb : gluedBytes = 6064 := rfl
  have hqc : queryCap = 230 := rfl
  have hmap : ∀ j, j ≤ 61152 → ∀ c, j + c ≤ 61152 → NativeRustcVm.Mapped m.dmem (off p j) c :=
    fun j _ c hc i hi ↦ by
      rw [off, NativeRustcVm.addr_add_add]
      exact h.fr.kept _ (hpin.1.1 _ (by rw [hsB]; omega))
  have hSP : 704 ≤ m0.regs.SP.toNat := hstk.2.1
  have hbt : (base m0 112).toNat = m0.regs.SP.toNat - 112 := Ring.base_toNat (by omega)
  have hSPb : m0.regs.SP.toBitVec.toNat = m0.regs.SP.toNat := rfl
  have hfap : Apart p stateBytes (base m0 112) 112 :=
    Ring.apart_frame (F := 112) hstk.2.1 (by decide) hpin.2
  let env := Env.ofMachine m [(base m0 112, 112), (m0.regs.SP.toBitVec, 48), (off p (o2 s), 6064)]
  have hwf : env.WF := by
    refine Env.wf_of ⟨⟨fun i hi ↦ h.fr.kept _ (Ring.frame_mapped hstk (by decide) i hi),
        Ring.base_noWrap (by omega)⟩, ⟨fun i hi ↦ h.fr.kept _ (hargs.1 i hi), hargs.2⟩,
      ⟨hmap _ (by omega) 6064 (by omega), noWrap_off hpnw (by omega) (by omega)⟩, trivial⟩
      (pairwise3 ?_ ?_ ?_)
    · exact Or.inl (by show (base m0 112).toNat + 112 ≤ m0.regs.SP.toBitVec.toNat; omega)
    · exact NativeRustcVm.Apart.symm (apart_off hpnw hfap (by omega) (by omega))
    · exact NativeRustcVm.Apart.symm (apart_off hpnw hapA (by omega) (by omega))
  have hb2 : env.base 2 = off p (o2 s) := rfl
  have hm : Match env weightsS m :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by decide) rfl, rfl,
        fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), trivial⟩
      (by rw [h.fr.sp]; simp [Sym.eval])
      ⟨by show (m.regs.getXReg .X21).toBitVec = _; rw [h.x21]; simp [Sym.eval]; rfl, trivial⟩
      trivial trivial
      ⟨by
          show base m0 112 + BitVec.ofInt 64 128 = m0.regs.SP.toBitVec + BitVec.ofInt 64 16
          simp only [base]; bv_omega,
        by
          show base m0 112 + BitVec.ofInt 64 136 = m0.regs.SP.toBitVec + BitVec.ofInt 64 24
          simp only [base]; bv_omega, trivial⟩
  have hk8 : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.GlueLevel.b8Offset) := b8_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk9 : b9.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.GlueLevel.b9Offset) := b9_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hx0 : env.regs .X0 = 1#64 := by
    show (m.regs.getXReg .X0).toBitVec = _
    rw [show m.regs.getXReg .X0 = m.regs.X0 from rfl, h.x0]
    rfl
  refine exec_then hk8 run_b8 hwf hm fun st8 hm8 hpc8 ↦ ?_
  have hpc8' : st8.pc = Host.addrOf (k + NativeRustcVmArm.Vm.GlueLevel.b9Offset) := by
    simp only [PcOk] at hpc8
    rw [cbz_one hx0] at hpc8
    exact hpc8
  refine exec_at hk9 (exec_after run_b8 run_b9) hwf hpc8' hm8 fun st9 hm9 hpc9 ↦ ?_
  have hb2' : env.regions[2]? = some (off p (o2 s), 6064) := rfl
  obtain ⟨hfr9, hA9⟩ := fr_block hpre h.fr hm hm9 hwf rfl rfl
    (W := fun j ↦ o2 s + 2376 ≤ j ∧ j < o2 s + 2384)
    (foot_two (r₀ := 2) (r₁ := 2) (lo₀ := 2376) (hi₀ := 2384) (lo₁ := 2376) (hi₁ := 2384) hb2' hb2'
      (hto _ (by omega)) (hto _ (by omega)) (by decide) (by omega) (by omega) fun j hj ↦ by omega)
  have hwz : WordAt st9.data.dmem (off p (o2 s + 2376)) 0 := by
    rw [← off_off]
    exact NativeRustcVmArm.Sumcheck.Match.wordAt_write hm9 hb2' (o := 2376) (by decide)
      (v := .lit 0) (by decide)
  have hw2 : env.load 1 16 8 = (whirStackArg m0 2).toBitVec := by
    rw [Ring.load_eq_wordOf]
    exact congrArg UInt64.toBitVec (arg_word hpre h.fr (i := 2) (by decide))
  have hw3 : env.load 1 24 8 = (whirStackArg m0 3).toBitVec := by
    rw [Ring.load_eq_wordOf]
    exact congrArg UInt64.toBitVec (arg_word hpre h.fr (i := 3) (by decide))
  have hx0' : st9.data.regs.X0 = UInt64.ofBitVec (off p (o2 s + 2376)) := by
    refine (rv hm9 (r := .X0) rfl).trans ?_
    show UInt64.ofBitVec (env.base 2 + BitVec.ofNat 64 2376) = _
    rw [hb2, NativeRustcVm.Transcript.off_add]
  have hx1 : st9.data.regs.X1 = whirStackArg m0 2 := (rv hm9 (r := .X1) rfl).trans (by
    show UInt64.ofBitVec (env.load 1 16 8) = _
    rw [hw2])
  have hx2 : st9.data.regs.X2 = whirStackArg m0 3 := (rv hm9 (r := .X2) rfl).trans (by
    show UInt64.ofBitVec (env.load 1 24 8) = _
    rw [hw3])
  have hw0 : NativeRustcVm.wordOf st9.data.dmem (off p (o2 s + 2376)) = 0 :=
    NativeRustcVm.wordOf_of_wordAt hwz
  have hnw : NoWrap (off p (o2 s + 2376)) (8 + 16 * 230) := noWrap_off hpnw (by omega) (by omega)
  have hapW' : Apart p stateBytes (whirStackArg m0 2).toBitVec (16 * (whirStackArg m0 3).toNat) := hapW
  have hap : Apart (off p (o2 s + 2376)) (8 + 16 * 230) (whirStackArg m0 2).toBitVec
      (16 * (whirStackArg m0 3).toNat) := apart_off hpnw hapW' (by omega) (by omega)
  have hin : ∀ q, InRange (off p (o2 s + 2376)) (8 + 16 * 230) q → InRange p stateBytes q :=
    fun q hq ↦ by
      have h1 := (NativeRustcVm.Transcript.inRange_iff' hnw).mp hq
      rw [hto (o2 s + 2376) (by omega)] at h1
      exact (NativeRustcVm.Transcript.inRange_iff' hpnw).mpr ⟨by omega, by omega⟩
  have hwn' : (whirStackArg m0 3).toNat ≤ 230 := hwn
  have hPre : BufEWExtendPre 230 st9.data := by
    unfold BufEWExtendPre
    rw [hx0', hx1, hx2, UInt64.toBitVec_ofBitVec]
    refine ⟨?_, ⟨?_, hnw⟩, ⟨fun i hi ↦ hfr9.kept _ (hwin.1.1 i hi), hwin.1.2⟩, hap⟩
    · rw [hw0]; decide
    · intro i hi
      rw [off, NativeRustcVm.addr_add_add]
      exact hfr9.kept _ (hpin.1.1 _ (by rw [hsB]; omega))
  refine call_then hpc9 hext hPre fun ⟨d10, pc10⟩ hpc10 hq10 ↦ ?_
  simp only at hpc10
  subst hpc10
  obtain ⟨hq10a, hq10b, hq10c⟩ := hq10
  simp only [hx0', hx1, hx2, UInt64.toBitVec_ofBitVec, hw0] at hq10a hq10b
  obtain ⟨hx10, hbuf⟩ : _ ∧ _ := by
    split at hq10a
    · exact hq10a
    · rename_i hc
      exfalso
      apply hc
      simp only [UInt64.toNat_zero, Nat.zero_add]
      omega
  have hA10 := agree_changes hpnw (show o2 s + 2376 + (8 + 16 * 230) ≤ stateBytes by omega) hq10b
  have hfr10 : FR m0 d10 := fr_out hpre hfr9 hin hq10c hq10b
  have hslice : slice st9.data (whirStackArg m0 2) (whirStackArg m0 3) = (glueArgs m0).2.1 := by
    unfold slice
    rw [NativeRustcVm.ewsOf_congr (input_same hpre hfr9 hwin.1.2 hwin.2 hapW)]
    rfl
  rw [hslice] at hbuf
  have hws : BufEWAt d10.dmem (off (off p (o2 s)) 2376) queryCap (glueArgs m0).2.1.toList := by
    rw [off_off]
    simp only [NativeRustcVm.bufEWOf, hw0, NativeRustcVm.ewsOf, UInt64.toNat_zero,
      List.range_zero, List.map_nil, List.nil_append] at hbuf
    exact hbuf
  have hs10 := hq10c.1
  have hW : ∀ j, (o2 s + 2376 ≤ j ∧ j < o2 s + 2384) →
      j < 16 ∨ (504 ≤ j ∧ j < 512) ∨ o1 s ≤ j := fun j hj ↦ by omega
  have hA : ∀ {o c : Nat}, o + c ≤ o2 s + 2376 → (∀ i < c, ¬ ((o2 s + 2376 ≤ o + i ∧
      o + i < o2 s + 2384) )) ∧ ∀ i < c, ¬ (o2 s + 2376 ≤ o + i ∧
      o + i < o2 s + 2376 + (8 + 16 * 230)) := fun hle ↦
    ⟨fun i hi hw ↦ by omega, fun i hi hw ↦ by omega⟩
  refine cont d10 ⟨hfr10, hx10, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs10 .X19 rfl]
    exact (rv hm9 (r := .X19) rfl).trans (by show m.regs.getXReg .X19 = _; exact h.x19)
  · exact (h.base.agree hA9 hcap hW).agree hA10 hcap fun j hj ↦ by omega
  · exact ke hA10 (by decide) (hA (by omega)).2 (ke hA9 (by decide) (hA (by omega)).1 h.claim)
  · exact kw hA10 (by decide) (hA (by simp only [gluedOff]; omega)).2
      (kw hA9 (by decide) (hA (by simp only [gluedOff]; omega)).1 h.len)
  · exact kg hA10 (by omega) (hA (by omega)).2 (kg hA9 (by omega) (hA (by omega)).1 h.g1)
  · refine ⟨ke hA10 (by omega) (hA (by omega)).2 (ke hA9 (by omega) (hA (by omega)).1 h.sc), ?_,
      ?_, ?_, ?_, ?_, ?_, hws⟩
    · show s.alphas.size < 2 ^ 64
      have := h.base.alphas.1
      rw [Array.length_toList] at this
      have : stackCap = 30 := rfl
      omega
    · have := h.fs
      rw [off_off] at this ⊢
      exact kw hA10 (by omega) (hA (by omega)).2 (kw hA9 (by omega) (hA (by omega)).1 this)
    · have := h.kind
      rw [off_off] at this ⊢
      exact kw hA10 (by omega) (hA (by omega)).2 (kw hA9 (by omega) (hA (by omega)).1 this)
    · exact hmu
    · have := h.mu
      rw [off_off] at this ⊢
      show WordAt _ _ (UInt64.ofNat m0.regs.X3.toNat)
      rw [UInt64.ofNat_toNat]
      exact kw hA10 (by omega) (hA (by omega)).2 (kw hA9 (by omega) (hA (by omega)).1 this)
    · have := h.qs
      rw [off_off] at this ⊢
      exact NativeRustcVmArm.Whir.GlueLevel.kbw hA10 (by omega) (hA (by omega)).2
        (NativeRustcVmArm.Whir.GlueLevel.kbw hA9 (by omega) (hA (by omega)).1 this)

end

end NativeRustcVmArm.Whir.GlueLevel
