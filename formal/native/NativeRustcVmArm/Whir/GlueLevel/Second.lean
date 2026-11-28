module

public import NativeRustcVmArm.Code.Vm.BufU64x230Extend.Names
public import NativeRustcVmArm.Whir.GlueLevel.First

/-!
# `glue_level`'s second glued claim: its header and queries

`b5` checks `extend`'s `Some`; `b6` counts the first glued claim and checks there is room for the
second; `b7` writes its `λ²`, fold start, kind `1` and `μ`, empties its queries and calls
`Buf<u64, 230>::extend` with them. At `b8` (`AtB8`): the count one more, the first glued claim, the
second's header and queries in place.
-/

namespace NativeRustcVmArm.Whir.GlueLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.GlueLevel
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt EWAt BufEWAt BufWordsAt)
open NativeRustcVm.Transcript (off off_off Agree)

@[expose] public section

/-- Offset of the second glued claim `glue_level` adds. -/
def o2 (s : WhirStateW) : Nat := gluedOff + 8 + gluedBytes * (s.glued.size + 1)

/-- **At `b8`**, after the second glued claim's queries. -/
structure AtB8 (s : WhirStateW) (m0 m : MachineData) : Prop where
  fr : FR m0 m
  x0 : m.regs.X0 = 1
  x19 : m.regs.getXReg .X19 = m0.regs.X0
  x21 : m.regs.getXReg .X21 = UInt64.ofBitVec (off (pOf m0) (o2 s))
  base : Base s (pOf m0) m.dmem
  claim : EWAt m.dmem (off (pOf m0) 0) (claim2 s m0)
  len : WordAt m.dmem (off (pOf m0) gluedOff) (s.glued.size + 1).toUInt64
  g1 : GluedAt m.dmem (off (pOf m0) (o1 s)) (g1Of s m0)
  sc : EWAt m.dmem (off (pOf m0) (o2 s)) (lamOf m0 * lamOf m0)
  fs : WordAt m.dmem (off (off (pOf m0) (o2 s)) 16) s.alphas.size.toUInt64
  kind : WordAt m.dmem (off (off (pOf m0) (o2 s)) 24) 1
  mu : WordAt m.dmem (off (off (pOf m0) (o2 s)) 32) m0.regs.X3
  qs : BufWordsAt m.dmem (off (off (pOf m0) (o2 s)) 528) queryCap (glueArgs m0).1.toList

end

public section

theorem o2_eq (s : WhirStateW) : o2 s = 512 + 6064 * (s.glued.size + 1) := rfl

variable [Host] {k : Nat} {s : WhirStateW} {m0 : MachineData}

/-- **From `b5` to `b8`.** -/
theorem second_step (hp : Placed code k)
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufU64x230Extend.entryLabel) (BufU64ExtendPre 230) (BufU64ExtendPost 230))
    (hpre : GlueLevelPre s m0) {m : MachineData} (h : AtB5 s m0 m) {R : MachineState → Prop}
    (cont : ∀ m', AtB8 s m0 m' → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.GlueLevel.b8Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GlueLevel.b5Offset)⟩ := by
  have hpre' := hpre
  obtain ⟨hstk, -, hcap, -, -, hqn, -, hargs, hpin, -, hqin, -, -, -, hapQ, -⟩ := hpre'
  let p := pOf m0
  have hn' : s.glued.size ≤ 8 := by have : s.glued.size + 2 ≤ 10 := hcap; omega
  have hsB : stateBytes = 61152 := rfl
  have hpnw : NoWrap p stateBytes := hpin.1.2
  have ho2 := o2_eq s
  have ho1 := o1_eq s
  have hgb : gluedBytes = 6064 := rfl
  have hgo : gluedOff = 504 := rfl
  have hto : ∀ j, j < 61152 → (off p j).toNat = p.toNat + j := fun j hj ↦
    toNat_off_state hpnw hj
  have hmap : ∀ j, j ≤ 61152 → ∀ c, j + c ≤ 61152 → NativeRustcVm.Mapped m.dmem (off p j) c :=
    fun j _ c hc i hi ↦ by
      rw [off, NativeRustcVm.addr_add_add]
      exact h.fr.kept _ (hpin.1.1 _ (by rw [hsB]; omega))
  have hgeo : p.toNat + 61152 ≤ m0.regs.SP.toNat - 704 ∨ m0.regs.SP.toNat + 48 ≤ p.toNat :=
    state_geo hpre
  have hSP : 704 ≤ m0.regs.SP.toNat := hstk.2.1
  have hbt : (base m0 112).toNat = m0.regs.SP.toNat - 112 := Ring.base_toNat (by omega)
  have hSPb : m0.regs.SP.toBitVec.toNat = m0.regs.SP.toNat := rfl
  have ho2' : (off p (o2 s)).toNat = p.toNat + o2 s := hto _ (by omega)
  let env := Env.ofMachine m [(base m0 112, 112), (m0.regs.SP.toBitVec, 48), (p, 512),
    (off p (o2 s), 6064)]
  have hwf : env.WF := by
    refine Env.wf_of ⟨⟨fun i hi ↦ h.fr.kept _ (Ring.frame_mapped hstk (by decide) i hi),
        Ring.base_noWrap (by omega)⟩, ⟨fun i hi ↦ h.fr.kept _ (hargs.1 i hi), hargs.2⟩,
      ⟨by have := hmap 0 (by omega) 512 (by omega); rwa [NativeRustcVm.Transcript.off_zero] at this,
        NativeRustcVm.NoWrap.mono (m := 512) hpnw (by decide)⟩,
      ⟨hmap _ (by omega) 6064 (by omega), noWrap_off hpnw (by omega) (by omega)⟩,
      trivial⟩ (pairwise4 ?_ ?_ ?_ ?_ ?_ ?_) <;> unfold Apart <;> simp only [hbt, hSPb, ho2'] <;>
      omega
  have hb0 : env.base 0 = base m0 112 := rfl
  have hb2 : env.base 2 = p := rfl
  have hl504 : env.load 2 504 8 = BitVec.ofNat 64 s.glued.size := Ring.load_word h.len
  have hg2 : g2Sym.eval env = off p (o2 s) := by
    simp only [g2Sym]
    sym_simp
    rw [hl504, hb2]
    exact glued_addr10 s.glued.size
  have hm : Match env secondS m :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by decide) rfl, rfl,
        fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by rw [h.fr.sp]; simp [Sym.eval])
      ⟨by show (m.regs.getXReg .X19).toBitVec = _; rw [h.x19]; simp [Sym.eval]; rfl,
        by show (m.regs.getXReg .X28).toBitVec = _; rw [h.x28]; rfl, trivial⟩ trivial trivial
      ⟨by
          show base m0 112 + BitVec.ofInt 64 112 = m0.regs.SP.toBitVec + BitVec.ofInt 64 0
          simp only [base]; bv_omega,
        by
          show base m0 112 + BitVec.ofInt 64 120 = m0.regs.SP.toBitVec + BitVec.ofInt 64 8
          simp only [base]; bv_omega,
        by
          show g2Sym.eval env = env.base 3 + BitVec.ofInt 64 0
          rw [hg2]; simp; rfl, trivial⟩
  have hapQ' : Apart p stateBytes (whirStackArg m0 0).toBitVec (8 * (whirStackArg m0 1).toNat) := hapQ
  have hnw528 : NoWrap (off p (o2 s + 528)) (8 + 8 * 230) := noWrap_off hpnw (by omega) (by omega)
  have hap528 : Apart (off p (o2 s + 528)) (8 + 8 * 230) (whirStackArg m0 0).toBitVec
      (8 * (whirStackArg m0 1).toNat) := apart_off hpnw hapQ' (by omega) (by omega)
  have hin528 : ∀ q, InRange (off p (o2 s + 528)) (8 + 8 * 230) q → InRange p stateBytes q :=
    fun q hq ↦ by
      have h1 := (NativeRustcVm.Transcript.inRange_iff' hnw528).mp hq
      rw [hto (o2 s + 528) (by omega)] at h1
      exact (NativeRustcVm.Transcript.inRange_iff' hpnw).mpr ⟨by omega, by omega⟩
  have hk5 : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.GlueLevel.b5Offset) := b5_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk6 : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.GlueLevel.b6Offset) := b6_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk7 : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.GlueLevel.b7Offset) := b7_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hx0 : env.regs .X0 = 1#64 := by
    show (m.regs.getXReg .X0).toBitVec = _
    rw [show m.regs.getXReg .X0 = m.regs.X0 from rfl, h.x0]
    rfl
  refine exec_then hk5 run_b5 hwf hm fun st5 hm5 hpc5 ↦ ?_
  have hpc5' : st5.pc = Host.addrOf (k + NativeRustcVmArm.Vm.GlueLevel.b6Offset) := by
    simp only [PcOk] at hpc5
    rw [cbz_one hx0] at hpc5
    exact hpc5
  refine exec_at hk6 (exec_after run_b5 run_b6) hwf hpc5' hm5 fun st6 hm6 hpc6 ↦ ?_
  have hpc6' : st6.pc = Host.addrOf (k + NativeRustcVmArm.Vm.GlueLevel.b7Offset) := by
    simp only [PcOk] at hpc6
    sym_simp at hpc6
    rw [hl504] at hpc6
    have hc : ((!(BitVec.ofNat 64 s.glued.size + BitVec.ofNat 64 1).ult (BitVec.ofNat 64 9)) &&
        !(BitVec.ofNat 64 s.glued.size + BitVec.ofNat 64 1 == BitVec.ofNat 64 9)) = false := by
      rw [← BitVec.ofNat_add]
      by_cases h9 : s.glued.size + 1 = 9
      · rw [h9]; rfl
      · have : (BitVec.ofNat 64 (s.glued.size + 1)).ult (BitVec.ofNat 64 9) = true := by
          simp only [BitVec.ult, BitVec.toNat_ofNat]
          simp
          omega
        rw [this]
        rfl
    rw [hc] at hpc6
    exact hpc6
  refine exec_at hk7 (exec_after (exec_after run_b5 run_b6) run_b7) hwf hpc6' hm6
    fun st7 hm7 hpc7 ↦ ?_
  have hb3 : env.regions[3]? = some (off p (o2 s), 6064) := rfl
  obtain ⟨hfr7, hA7⟩ := fr_block hpre h.fr hm hm7 hwf rfl rfl
    (W := fun j ↦ (504 ≤ j ∧ j < 512) ∨ (o2 s ≤ j ∧ j < o2 s + 536))
    (foot_two (r₀ := 2) (r₁ := 3) (o₀ := 0) (lo₀ := 504) (hi₀ := 512) (lo₁ := 0) (hi₁ := 536) rfl
      hb3 (Nat.add_zero _).symm ho2' (by decide) (by omega) (by omega) fun j hj ↦ by omega)
  have hlen7 : WordAt st7.data.dmem (off p gluedOff) (s.glued.size + 1).toUInt64 := by
    have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm7 (r := 2) (o := 504) rfl (by decide)
      (v := .bin .add .W64 (.load 2 504 8) (.lit 1)) (by decide)
    have hv : UInt64.ofBitVec ((Sym.bin .add .W64 (.load 2 504 8) (.lit 1)).eval env) =
        (s.glued.size + 1).toUInt64 := by
      sym_simp
      rw [hl504]
      exact count_succ s.glued.size
    rw [hv] at this
    exact this
  have hsc7 : EWAt st7.data.dmem (off p (o2 s)) (lamOf m0 * lamOf m0) := by
    rw [← h.l2, NativeRustcVm.ewAt_iff]
    refine ⟨?_, ?_⟩
    · have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm7 hb3 (o := 0) (by decide)
        (v := .reg .X23) (by decide)
      rw [NativeRustcVm.addr_add_zero] at this
      exact this
    · exact NativeRustcVmArm.Sumcheck.Match.wordAt_write hm7 hb3 (o := 8) (by decide)
        (v := .reg .X24) (by decide)
  have hfs7 : WordAt st7.data.dmem (off (off p (o2 s)) 16) s.alphas.size.toUInt64 := by
    rw [← h.x27]
    exact NativeRustcVmArm.Sumcheck.Match.wordAt_write hm7 hb3 (o := 16) (by decide)
      (v := .reg .X27) (by decide)
  have hkind7 : WordAt st7.data.dmem (off (off p (o2 s)) 24) 1 :=
    NativeRustcVmArm.Sumcheck.Match.wordAt_write hm7 hb3 (o := 24) (by decide) (v := .lit 1)
      (by decide)
  have hmu7 : WordAt st7.data.dmem (off (off p (o2 s)) 32) m0.regs.X3 := by
    have hl8 : env.load 0 8 8 = (m0.regs.getXReg .X3).toBitVec :=
      Ring.load_word (h.fr.slots (8, .X3) (by simp [slots]))
    have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm7 hb3 (o := 32) (by decide)
      (v := .load 0 8 8) (by decide)
    rw [show (Sym.load 0 8 8).eval env = env.load 0 8 8 from rfl, hl8] at this
    exact this
  have hqz : WordAt st7.data.dmem (off p (o2 s + 528)) 0 := by
    rw [← off_off]
    exact NativeRustcVmArm.Sumcheck.Match.wordAt_write hm7 hb3 (o := 528) (by decide)
      (v := .lit 0) (by decide)
  -- the call
  have hq0 : env.load 1 0 8 = (whirStackArg m0 0).toBitVec := by
    rw [Ring.load_eq_wordOf]
    exact congrArg UInt64.toBitVec (arg_word hpre h.fr (i := 0) (by decide))
  have hq1 : env.load 1 8 8 = (whirStackArg m0 1).toBitVec := by
    rw [Ring.load_eq_wordOf]
    exact congrArg UInt64.toBitVec (arg_word hpre h.fr (i := 1) (by decide))
  have hx0' : st7.data.regs.X0 = UInt64.ofBitVec (off p (o2 s + 528)) := by
    have := hm7.regs .X0 _ rfl
    sym_simp at this
    rw [hl504, hb2, glued_addr1] at this
    exact reg_eq this
  have hx1 : st7.data.regs.X1 = whirStackArg m0 0 := (rv hm7 (r := .X1) rfl).trans (by
    show UInt64.ofBitVec (env.load 1 0 8) = _
    rw [hq0])
  have hx2 : st7.data.regs.X2 = whirStackArg m0 1 := (rv hm7 (r := .X2) rfl).trans (by
    show UInt64.ofBitVec (env.load 1 8 8) = _
    rw [hq1])
  have hw0 : NativeRustcVm.wordOf st7.data.dmem (off p (o2 s + 528)) = 0 :=
    NativeRustcVm.wordOf_of_wordAt hqz
  have hqn' : (whirStackArg m0 1).toNat ≤ 230 := hqn
  have hPre : BufU64ExtendPre 230 st7.data := by
    unfold BufU64ExtendPre
    rw [hx0', hx1, hx2, UInt64.toBitVec_ofBitVec]
    refine ⟨?_, ⟨?_, ?_⟩, ⟨fun i hi ↦ hfr7.kept _ (hqin.1.1 i hi), hqin.1.2⟩, ?_⟩
    · rw [hw0]; decide
    · intro i hi
      rw [off, NativeRustcVm.addr_add_add]
      exact hfr7.kept _ (hpin.1.1 _ (by rw [hsB]; omega))
    · exact hnw528
    · exact hap528
  refine call_then hpc7 hext hPre fun ⟨d8, pc8⟩ hpc8 hq8 ↦ ?_
  simp only at hpc8
  subst hpc8
  obtain ⟨hq8a, hq8b, hq8c⟩ := hq8
  simp only [hx0', hx1, hx2, UInt64.toBitVec_ofBitVec, hw0] at hq8a hq8b
  obtain ⟨hx8, hbuf⟩ : _ ∧ _ := by
    split at hq8a
    · exact hq8a
    · rename_i hc
      exfalso
      apply hc
      simp only [UInt64.toNat_zero, Nat.zero_add]
      omega
  have hA8 := agree_changes hpnw (show o2 s + 528 + (8 + 8 * 230) ≤ stateBytes by omega) hq8b
  have hfr8 : FR m0 d8 := fr_out hpre hfr7 hin528 hq8c hq8b
  have hwords : NativeRustcVm.wordsOf st7.data.dmem (whirStackArg m0 0).toBitVec (whirStackArg m0 1).toNat =
      (glueArgs m0).1.toList := by
    rw [NativeRustcVm.wordsOf_congr (input_same hpre hfr7 hqin.1.2 hqin.2 hapQ)]
    simp [glueArgs, wordSlice]
  have hqs : BufWordsAt d8.dmem (off (off p (o2 s)) 528) queryCap (glueArgs m0).1.toList := by
    rw [off_off, ← hwords]
    simp only [NativeRustcVm.bufWordsOf, hw0, NativeRustcVm.wordsOf, UInt64.toNat_zero,
      List.range_zero, List.map_nil, List.nil_append] at hbuf
    exact hbuf
  have hs8 := hq8c.1
  have kr : ∀ r, calleeSaved r = true →
      (after b7 (after b6 (after b5 secondS))).reg r = some (.reg r) →
      d8.regs.getXReg r = m.regs.getXReg r := fun r hc hr ↦ by
    rw [hs8 r hc]
    exact (rv hm7 (by rw [← after_eq (exec_after (exec_after run_b5 run_b6) run_b7)]; exact hr)).trans rfl
  have hW : ∀ j, ((504 ≤ j ∧ j < 512) ∨ (o2 s ≤ j ∧ j < o2 s + 536)) →
      j < 16 ∨ (504 ≤ j ∧ j < 512) ∨ o1 s ≤ j := fun j hj ↦ by rw [o1_eq]; omega
  refine cont d8 ⟨hfr8, hx8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hqs⟩
  · rw [hs8 .X19 rfl]
    refine (rv hm7 (r := .X19) rfl).trans ?_
    show UInt64.ofBitVec (env.base 2 + BitVec.ofInt 64 0) = _
    rw [hb2]
    simp [p]
  · rw [hs8 .X21 rfl]
    exact (rv hm7 (r := .X21) rfl).trans (congrArg UInt64.ofBitVec hg2)
  · exact (h.base.agree hA7 hcap hW).agree hA8 hcap fun j hj ↦ by omega
  · exact ke hA8 (by decide) (fun i hi hw ↦ by omega)
      (ke hA7 (by decide) (fun i hi hw ↦ by omega) h.claim)
  · exact kw hA8 (by decide) (fun i hi hw ↦ by simp only [gluedOff, o2_eq] at hw; omega) hlen7
  · exact kg hA8 (by omega) (fun i hi hw ↦ by simp only [gluedBytes, o2_eq, o1_eq] at hi hw; omega)
      (kg hA7 (by omega) (fun i hi hw ↦ by simp only [gluedBytes, o2_eq, o1_eq] at hi hw; omega) h.g1)
  · exact ke hA8 (by omega) (fun i hi hw ↦ by omega) hsc7
  · rw [off_off] at hfs7 ⊢
    exact kw hA8 (by omega) (fun i hi hw ↦ by omega) hfs7
  · rw [off_off] at hkind7 ⊢
    exact kw hA8 (by omega) (fun i hi hw ↦ by omega) hkind7
  · rw [off_off] at hmu7 ⊢
    exact kw hA8 (by omega) (fun i hi hw ↦ by omega) hmu7

end

end NativeRustcVmArm.Whir.GlueLevel
