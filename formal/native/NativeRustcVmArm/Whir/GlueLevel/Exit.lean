module

public import NativeRustcVmArm.Code.Vm.GlueLevel.Names
public import NativeRustcVmArm.Whir.GlueLevel.Third

/-!
# `glue_level`'s exit

`b10` checks `extend`'s `Some`; `b11` counts the second glued claim and sets X0 to `1`; `b13`
restores the registers and returns. The state is `glueLevel`'s: the new claim, the `α`s, the glued
claims so far and the two new ones, their count.
-/

namespace NativeRustcVmArm.Whir.GlueLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.GlueLevel
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt EWAt BufEWAt BufWordsAt)
open NativeRustcVm.Transcript (off off_off Agree)

public section

variable [Host] {k : Nat} {s : WhirStateW} {m0 : MachineData}

/-- **From `b10` to the return.** -/
theorem exit_step (hp : Placed code k) (hpre : GlueLevelPre s m0) {m : MachineData}
    (h : AtB10 s m0 m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧ GlueLevelPost s m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GlueLevel.b10Offset)⟩ := by
  have hpre' := hpre
  obtain ⟨hstk, -, hcap, -, -, -, -, -, hpin, -, -, -, -, -, -, -⟩ := hpre'
  let p := pOf m0
  have hn' : s.glued.size ≤ 8 := by have : s.glued.size + 2 ≤ 10 := hcap; omega
  have hsB : stateBytes = 61152 := rfl
  have hpnw : NoWrap p stateBytes := hpin.1.2
  have hSP : 704 ≤ m0.regs.SP.toNat := hstk.2.1
  have hfap : Apart p stateBytes (base m0 112) 112 :=
    Ring.apart_frame (F := 112) hstk.2.1 (by decide) hpin.2
  have hfap' : Apart (base m0 112) 112 p 512 := by
    have := hfap
    unfold Apart at this ⊢
    rw [hsB] at this
    omega
  let env := Env.ofMachine m [(base m0 112, 112), (p, 512)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨fun i hi ↦ h.fr.kept _ (Ring.frame_mapped hstk (by decide) i hi),
        Ring.base_noWrap (by omega)⟩,
      ⟨fun i hi ↦ h.fr.kept _ (hpin.1.1 i (by rw [hsB]; omega)),
        NativeRustcVm.NoWrap.mono (m := 512) hpnw (by decide)⟩, trivial⟩
      (List.pairwise_pair.mpr hfap')
  have hm : Match env exitS m :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by decide) rfl, rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by rw [h.fr.sp]; simp [Sym.eval])
      ⟨by show (m.regs.getXReg .X19).toBitVec = _; rw [h.x19]; simp [Sym.eval]; rfl, trivial⟩
      trivial trivial trivial
  have hk10 : b10.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.GlueLevel.b10Offset) := b10_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk11 : b11.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.GlueLevel.b11Offset) := b11_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk13 : b13.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.GlueLevel.b13Offset) := b13_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hx0 : env.regs .X0 = 1#64 := by
    show (m.regs.getXReg .X0).toBitVec = _
    rw [show m.regs.getXReg .X0 = m.regs.X0 from rfl, h.x0]
    rfl
  refine exec_then hk10 run_b10 hwf hm fun st10 hm10 hpc10 ↦ ?_
  have hpc10' : st10.pc = Host.addrOf (k + NativeRustcVmArm.Vm.GlueLevel.b11Offset) := by
    simp only [PcOk] at hpc10
    rw [cbz_one hx0] at hpc10
    exact hpc10
  refine exec_at hk11 (exec_after run_b10 run_b11) hwf hpc10' hm10 fun st11 hm11 hpc11 ↦ ?_
  have hpc11' : st11.pc = Host.addrOf (k + NativeRustcVmArm.Vm.GlueLevel.b13Offset) := by
    rw [show Host.addrOf (k + NativeRustcVmArm.Vm.GlueLevel.b13Offset) = Labels.label NativeRustcVmArm.Vm.GlueLevel.label_7 from (hp.label (j := NativeRustcVmArm.Vm.GlueLevel.b13Offset) NativeRustcVmArm.Vm.GlueLevel.label_7_at).symm]
    exact hpc11
  refine exec_at hk13 (exec_after (exec_after run_b10 run_b11) run_b13) hwf hpc11' hm11
    fun st hm13 hpc13 ↦ Eventually.done _ ?_
  obtain ⟨hret, hsaved⟩ := Ring.Fr.exit h.fr hm13 hwf (by decide)
  have hb1 : env.regions[1]? = some (p, 512) := rfl
  have hfoot : Foot env (after b13 (after b11 (after b10 exitS))) p stateBytes
      (fun j ↦ 504 ≤ j ∧ j < 512) :=
    foot_two (r₀ := 1) (r₁ := 1) (o₀ := 0) (o₁ := 0) (lo₀ := 504) (hi₀ := 512) (lo₁ := 504)
      (hi₁ := 512) hb1 hb1 (Nat.add_zero _).symm (Nat.add_zero _).symm
      (by rw [after_eq run_b13]; decide) (by decide)
      (by decide) fun j hj ↦ by omega
  rw [after_eq run_b13] at hfoot
  have hA : Agree m.dmem st.data.dmem p stateBytes (fun j ↦ 504 ≤ j ∧ j < 512) :=
    agree_of_foot hm13 hwf hpnw hfoot
  have hl504 : env.load 1 504 8 = (s.glued.size + 1).toUInt64.toBitVec := Ring.load_word h.len
  have hlen : WordAt st.data.dmem (off p gluedOff) (s.glued.size + 2).toUInt64 := by
    have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm13 hb1 (o := 504) (by decide)
      (v := .bin .add .W64 (.load 1 504 8) (.lit 1)) (by decide)
    have hv : UInt64.ofBitVec ((Sym.bin .add .W64 (.load 1 504 8) (.lit 1)).eval env) =
        (s.glued.size + 2).toUInt64 := by
      sym_simp
      rw [hl504]
      exact count_succ (s.glued.size + 1)
    rw [hv] at this
    exact this
  have hbase := h.base.agree hA hcap fun j hj ↦ .inr (.inl hj)
  have hgb : gluedBytes = 6064 := rfl
  have hW : ∀ {o c : Nat}, 512 ≤ o → ∀ i < c, ¬ (504 ≤ o + i ∧ o + i < 512) :=
    fun ho i _ hw ↦ by omega
  refine ⟨hpc13.trans hret, (rv hm13 (r := .X0) (v := .lit 1) (by
      rw [← after_eq run_b13]; rfl)).trans rfl, ?_, ?_,
    hsaved⟩
  · unfold glueLevel
    refine ⟨?_, hbase.alphas, ?_, ?_, ?_⟩
    · have := ke hA (by decide) (fun i hi hw ↦ by omega) h.claim
      rwa [NativeRustcVm.Transcript.off_zero] at this
    · simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil]
      have : gluedCap = 10 := rfl
      omega
    · simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil]
      exact hlen
    · intro i hi
      simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil] at hi
      rcases Nat.lt_or_ge i s.glued.size with hlt | hge
      · rw [Array.getElem_append_left hlt]
        exact hbase.old i hlt
      · rw [Array.getElem_append_right hge]
        rcases (show i = s.glued.size ∨ i = s.glued.size + 1 by omega) with rfl | rfl
        · simp only [Nat.sub_self, List.getElem_toArray, List.getElem_cons_zero]
          exact kg hA (by simp only [gluedOff, gluedBytes, stateBytes]; omega)
            (hW (by simp only [gluedOff, gluedBytes]; omega)) h.g1
        · simp only [Nat.add_sub_cancel_left, List.getElem_toArray, List.getElem_cons_succ,
            List.getElem_cons_zero]
          exact kg hA (by simp only [gluedOff, gluedBytes, stateBytes]; omega)
            (hW (by simp only [gluedOff, gluedBytes]; omega)) h.g2
  · intro q hq
    have hq' : ¬ (InRange (stackBelow m0 glueLevelStack) glueLevelStack q ∨
        InRange p stateBytes q) := fun h' ↦ hq (h'.elim .inr fun h ↦
      .inl ⟨_, List.mem_singleton_self _, h⟩)
    rw [hm13.get?_mem0 hwf fun hw ↦ hq' (.inr (written_of_foot hpnw hfoot hw))]
    exact h.fr.same q hq'

end

end NativeRustcVmArm.Whir.GlueLevel
