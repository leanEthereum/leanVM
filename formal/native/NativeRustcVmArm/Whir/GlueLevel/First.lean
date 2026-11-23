module

public import NativeRustcVmArm.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmArm.Whir.GlueLevel.Head
public import NativeRustcVmArm.Whir.GlueLevel.Facts

/-!
# `glue_level`'s first glued claim

`b3` stores the new claim and checks the glued claims' count (below `9`: room for one more);
`b4` writes the first new glued claim's `λ`, its fold start (the `α`s' count) and kind `0`, empties
its point and calls `Buf<EW, 30>::extend` with the out-of-domain point. At `b5` (`AtB5`): the claim
stored, the first glued claim `⟨λ, |α|, eq oodPoint⟩` in place, the rest of the state kept.
-/

namespace NativeRustcVmArm.Whir.GlueLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.GlueLevel
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt EWAt BufEWAt)
open NativeRustcVm.Transcript (off off_off Agree)

@[expose] public section

/-- The new claim. -/
abbrev claim2 (s : WhirStateW) (m0 : MachineData) : EW :=
  s.claim + lamOf m0 * oodOf m0 + lamOf m0 * lamOf m0 * batOf m0

/-- The out-of-domain glued claim. -/
abbrev g1Of (s : WhirStateW) (m0 : MachineData) : GluedClaimW :=
  ⟨lamOf m0, s.alphas.size, .eq (slice m0 m0.regs.X4 m0.regs.X5)⟩

/-- **At `b5`**, after the first glued claim's point. -/
structure AtB5 (s : WhirStateW) (m0 m : MachineData) : Prop where
  fr : FR m0 m
  x0 : m.regs.X0 = 1
  x19 : m.regs.getXReg .X19 = m0.regs.X0
  l2 : (⟨m.regs.getXReg .X23, m.regs.getXReg .X24⟩ : EW) = lamOf m0 * lamOf m0
  x27 : m.regs.getXReg .X27 = s.alphas.size.toUInt64
  x28 : m.regs.getXReg .X28 = UInt64.ofBitVec (off (pOf m0) 512)
  base : Base s (pOf m0) m.dmem
  claim : EWAt m.dmem (off (pOf m0) 0) (claim2 s m0)
  len : WordAt m.dmem (off (pOf m0) gluedOff) s.glued.size.toUInt64
  g1 : GluedAt m.dmem (off (pOf m0) (o1 s)) (g1Of s m0)

end

public section

variable [Host] {k : Nat} {s : WhirStateW} {m0 : MachineData}

/-- **From `b3` to `b5`.** -/
theorem first_step (hp : Placed code k)
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    (hpre : GlueLevelPre s m0) {m : MachineData} (h : AtB3 s m0 m) {R : MachineState → Prop}
    (cont : ∀ m', AtB5 s m0 m' → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.GlueLevel.b5Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GlueLevel.b3Offset)⟩ := by
  have hpre' := hpre
  obtain ⟨hstk, hst, hcap, -, hood, -, -, -, hpin, hoodok, -, -, -, hapO, -, -⟩ := hpre'
  let p := pOf m0
  let n := s.glued.size
  have hn : n ≤ 8 := by have : n + 2 ≤ 10 := hcap; omega
  have hn' : s.glued.size ≤ 8 := hn
  have hsB : stateBytes = 61152 := rfl
  have hpnw : NoWrap p stateBytes := hpin.1.2
  have hpnw' : p.toNat + 61152 ≤ 2 ^ 64 := hpnw
  have ho1 : o1 s = 512 + 6064 * n := rfl
  have hto : ∀ j, j < 61152 → (off p j).toNat = p.toNat + j := fun j hj ↦
    NativeRustcVm.Transcript.toNat_off (by omega)
  have hmap : ∀ j, j ≤ 61152 → ∀ c, j + c ≤ 61152 → NativeRustcVm.Mapped m.dmem (off p j) c :=
    fun j _ c hc i hi ↦ by
      rw [off, NativeRustcVm.addr_add_add]
      exact h.fr.kept _ (hpin.1.1 _ (by rw [hsB]; omega))
  -- the state at `b3`: as at the entry
  have hA0 : Agree m0.dmem m.dmem p stateBytes (fun _ ↦ False) :=
    agree_of_sameOutside h.so fun j hj _ ↦
      not_inRange_apart hpnw (Ring.base_noWrap hstk.2.1) hpin.2 hj
  have hbase : Base s p m.dmem := (Base.of_state hst).agree hA0 hcap fun _ h ↦ h.elim
  have hlen : WordAt m.dmem (off p gluedOff) n.toUInt64 :=
    kw hA0 (by decide) (fun _ _ h ↦ h) hst.glued_len
  have hac : WordAt m.dmem (off p 16) s.alphas.size.toUInt64 := by
    have := hbase.alphas.2.1
    rwa [Array.length_toList] at this
  -- the run of `b3`, `b4`
  let env := Env.ofMachine m [(p, 512), (off p (o1 s), 6064)]
  have hwf : env.WF := by
    refine Env.wf_of ⟨⟨by
        have := hmap 0 (by omega) 512 (by omega)
        rw [NativeRustcVm.Transcript.off_zero] at this
        exact this,
        show p.toNat + 512 ≤ 2 ^ 64 by omega⟩,
      ⟨hmap _ (by omega) 6064 (by omega), show (off p (o1 s)).toNat + 6064 ≤ 2 ^ 64 by
        rw [hto _ (by omega)]; omega⟩, trivial⟩ (List.pairwise_pair.mpr ?_)
    exact Or.inl (show p.toNat + 512 ≤ (off p (o1 s)).toNat by rw [hto _ (by omega)]; omega)
  have hb0 : env.base 0 = p := rfl
  have hl504 : env.load 0 504 8 = BitVec.ofNat 64 n := Ring.load_word hlen
  have hl16 : env.load 0 16 8 = (s.alphas.size.toUInt64).toBitVec := Ring.load_word hac
  have hg1 : g1Sym.eval env = off p (o1 s) := by
    simp only [g1Sym]
    sym_simp
    rw [hl504, hb0]
    have := glued_addr (p := p) n 0
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, Nat.add_zero] at this
    exact this
  have hm : Match env headS m :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide),
        trivial⟩ rfl
      ⟨by show (m.regs.getXReg .X19).toBitVec = _; rw [h.x19]; simp [Sym.eval]; rfl, trivial⟩
      trivial trivial
      ⟨by show g1Sym.eval env = env.base 1 + BitVec.ofInt 64 0; rw [hg1]; simp; rfl, trivial⟩
  have hk3 : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.GlueLevel.b3Offset) := b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk4 : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.GlueLevel.b4Offset) := b4_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk3 run_b3 hwf hm fun st3 hm3 hpc3 ↦ ?_
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmArm.Vm.GlueLevel.b4Offset) := by
    simp only [PcOk] at hpc3
    sym_simp at hpc3
    rw [hl504] at hpc3
    have hu : (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 9) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat]
      simp
      omega
    simp only [hu, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hpc3
    exact hpc3
  refine exec_at hk4 (exec_after run_b3 run_b4) hwf hpc3' hm3 fun st4 hm4 hpc4 ↦ ?_
  have hb1 : env.regions[1]? = some (off p (o1 s), 6064) := rfl
  -- the block's writes
  obtain ⟨hfr4, hA4⟩ := fr_block hpre h.fr hm hm4 hwf rfl rfl
    (W := fun j ↦ j < 16 ∨ (o1 s ≤ j ∧ j < o1 s + 48))
    (foot_two (r₀ := 0) (r₁ := 1) (o₀ := 0) (lo₀ := 0) (hi₀ := 16) (lo₁ := 0) (hi₁ := 48) rfl hb1
      (Nat.add_zero _).symm (hto _ (by omega)) (by decide) (by omega) (by omega) fun j hj ↦ by omega)
  have hclaim : EWAt st4.data.dmem (off p 0) (claim2 s m0) := by
    have e : claim2 s m0 = ⟨m.regs.getXReg .X29 ^^^ m.regs.X0, m.regs.getXReg .X20 ^^^ m.regs.X1⟩ := by
      rw [claim2, ← h.claim1, ← h.c2]
      rfl
    have hv0 : UInt64.ofBitVec ((Sym.bin .eor .W64 (.reg .X29) (.reg .X0)).eval env) =
        m.regs.getXReg .X29 ^^^ m.regs.X0 := by sym_simp; rfl
    have hv1 : UInt64.ofBitVec ((Sym.bin .eor .W64 (.reg .X20) (.reg .X1)).eval env) =
        m.regs.getXReg .X20 ^^^ m.regs.X1 := by sym_simp; rfl
    rw [e, NativeRustcVm.Transcript.off_zero, NativeRustcVm.ewAt_iff]
    refine ⟨?_, ?_⟩
    · have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm4 (r := 0) (o := 0) rfl (by decide)
        (v := .bin .eor .W64 (.reg .X29) (.reg .X0)) (by decide)
      rw [hv0, NativeRustcVm.addr_add_zero] at this
      exact this
    · have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm4 (r := 0) (o := 8) rfl (by decide)
        (v := .bin .eor .W64 (.reg .X20) (.reg .X1)) (by decide)
      rw [hv1] at this
      exact this
  have hlam : EWAt st4.data.dmem (off p (o1 s)) (lamOf m0) := by
    rw [NativeRustcVm.ewAt_iff]
    refine ⟨?_, ?_⟩
    · have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm4 hb1 (o := 0) (by decide) (v := .reg .X26) (by decide)
      rw [NativeRustcVm.addr_add_zero] at this
      convert this using 1
      show m0.regs.X1 = m.regs.getXReg .X26
      rw [h.x26]
    · have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm4 hb1 (o := 8) (by decide) (v := .reg .X25) (by decide)
      convert this using 1
      show m0.regs.X2 = m.regs.getXReg .X25
      rw [h.x25]
  have hfs : WordAt st4.data.dmem (off (off p (o1 s)) 16) s.alphas.size.toUInt64 := by
    have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm4 hb1 (o := 16) (by decide) (v := .load 0 16 8)
      (by decide)
    convert this using 1
    show _ = UInt64.ofBitVec (env.load 0 16 8)
    rw [hl16]
  have hkind : WordAt st4.data.dmem (off (off p (o1 s)) 24) 0 :=
    NativeRustcVmArm.Sumcheck.Match.wordAt_write hm4 hb1 (o := 24) (by decide) (v := .lit 0) (by decide)
  have hpz : WordAt st4.data.dmem (off p (o1 s + 40)) 0 := by
    rw [← off_off]
    exact NativeRustcVmArm.Sumcheck.Match.wordAt_write hm4 hb1 (o := 40) (by decide) (v := .lit 0) (by decide)
  -- the call
  have hx0 : st4.data.regs.X0 = UInt64.ofBitVec (off p (o1 s + 40)) := by
    have := hm4.regs .X0 _ rfl
    sym_simp at this
    rw [hl504, hb0, glued_addr] at this
    exact reg_eq this
  have hx1 : st4.data.regs.X1 = m0.regs.X4 := (rv hm4 (r := .X1) rfl).trans h.x22
  have hx2 : st4.data.regs.X2 = m0.regs.X5 := (rv hm4 (r := .X2) rfl).trans h.x21
  have hw0 : NativeRustcVm.wordOf st4.data.dmem (off p (o1 s + 40)) = 0 :=
    NativeRustcVm.wordOf_of_wordAt hpz
  have hood' : m0.regs.X5.toNat ≤ 30 := hood
  have hapO' : Apart p stateBytes m0.regs.X4.toBitVec (16 * m0.regs.X5.toNat) := hapO
  have hPre : BufEWExtendPre 30 st4.data := by
    unfold BufEWExtendPre
    rw [hx0, hx1, hx2, UInt64.toBitVec_ofBitVec]
    refine ⟨?_, ⟨?_, ?_⟩, ⟨fun i hi ↦ hfr4.kept _ (hoodok.1.1 i hi), hoodok.1.2⟩, ?_⟩
    · rw [hw0]; decide
    · intro i hi
      rw [off, NativeRustcVm.addr_add_add]
      exact hfr4.kept _ (hpin.1.1 _ (by rw [hsB]; omega))
    · show (off p (o1 s + 40)).toNat + _ ≤ _
      rw [hto _ (by omega)]; omega
    · have := hapO'
      unfold Apart at this ⊢
      rw [hto _ (by omega)]
      rw [hsB] at this
      omega
  refine call_then hpc4 hext hPre fun ⟨d5, pc5⟩ hpc5 hq5 ↦ ?_
  simp only at hpc5
  subst hpc5
  obtain ⟨hq5a, hq5b, hq5c⟩ := hq5
  simp only [hx0, hx1, hx2, UInt64.toBitVec_ofBitVec, hw0] at hq5a hq5b
  obtain ⟨hx5, hbuf⟩ : _ ∧ _ := by
    split at hq5a
    · exact hq5a
    · rename_i hc
      exfalso
      apply hc
      simp only [UInt64.toNat_zero, Nat.zero_add]
      omega
  have hA5 := agree_changes hpnw (show o1 s + 40 + (8 + 16 * 30) ≤ stateBytes by omega) hq5b
  have hfr5 : FR m0 d5 := fr_out hpre hfr4 (fun q hq ↦ by
      have h1 := (NativeRustcVm.Transcript.inRange_iff' (show NativeRustcVm.NoWrap (off p (o1 s + 40))
        (8 + 16 * 30) by unfold NativeRustcVm.NoWrap; rw [hto _ (by omega)]; omega)).mp hq
      rw [hto _ (by omega)] at h1
      exact (NativeRustcVm.Transcript.inRange_iff' hpnw).mpr ⟨by omega, by omega⟩) hq5c hq5b
  have hslice : slice st4.data m0.regs.X4 m0.regs.X5 = slice m0 m0.regs.X4 m0.regs.X5 := by
    unfold slice
    rw [NativeRustcVm.ewsOf_congr (input_same hpre hfr4 hoodok.1.2 hoodok.2 hapO)]
  rw [hslice] at hbuf
  have hbuf' : BufEWAt d5.dmem (off (off p (o1 s)) 40) stackCap
      (slice m0 m0.regs.X4 m0.regs.X5).toList := by
    rw [off_off]
    simp only [NativeRustcVm.bufEWOf, hw0, NativeRustcVm.ewsOf, UInt64.toNat_zero, List.range_zero,
      List.map_nil, List.nil_append] at hbuf
    exact hbuf
  -- the registers `b3`, `b4` and the call keep
  have hs5 := hq5c.1
  have kr : ∀ r, calleeSaved r = true → (after b4 (after b3 headS)).reg r = some (.reg r) →
      d5.regs.getXReg r = m.regs.getXReg r := fun r hc hr ↦ by
    rw [hs5 r hc]
    exact (rv hm4 (by rw [← after_eq (exec_after run_b3 run_b4)]; exact hr)).trans rfl
  refine cont d5 ⟨hfr5, hx5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs5 .X19 rfl]
    refine (rv hm4 (r := .X19) rfl).trans ?_
    show UInt64.ofBitVec (env.base 0 + BitVec.ofInt 64 0) = _
    rw [hb0]
    simp [p]
  · rw [kr .X23 rfl rfl, kr .X24 rfl rfl]
    exact h.l2
  · rw [hs5 .X27 rfl]
    refine (rv hm4 (r := .X27) rfl).trans ?_
    show UInt64.ofBitVec (env.load 0 16 8) = _
    rw [hl16]
  · rw [hs5 .X28 rfl]
    exact (rv hm4 (r := .X28) rfl).trans rfl
  · exact (hbase.agree hA4 hcap fun j hj ↦ by omega).agree hA5 hcap fun j hj ↦ by omega
  · exact ke hA5 (by decide) (fun i hi hw ↦ by omega) hclaim
  · exact kw hA5 (by decide) (fun i hi hw ↦ by simp only [gluedOff, o1_eq] at hw; omega)
      (kw hA4 (by decide)
      (fun i hi hw ↦ by simp only [gluedOff, o1_eq] at hw; omega) hlen)
  · refine ⟨ke hA5 (by omega) (fun i hi hw ↦ by omega) hlam, ?_, ?_, ?_, ?_⟩
    · show s.alphas.size < 2 ^ 64
      have := hbase.alphas.1
      rw [Array.length_toList] at this
      have : stackCap = 30 := rfl
      omega
    · rw [off_off] at hfs ⊢
      exact kw hA5 (by omega) (fun i hi hw ↦ by omega) hfs
    · rw [off_off] at hkind ⊢
      exact kw hA5 (by omega) (fun i hi hw ↦ by omega) hkind
    · exact hbuf'

end

end NativeRustcVmArm.Whir.GlueLevel
