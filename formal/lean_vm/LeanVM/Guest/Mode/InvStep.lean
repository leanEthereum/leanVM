module

public import LeanVM.Guest.Mode.InvDefs

/-!
# One step, along the reference

`step_atX`: `step_at` with the states the hints pass through kept in a predicate (`P`, which a hint
preserves), so that a hint's agreement and the residuals are needed only of states the run reaches,
the step's instruction moded and the run's state before it handed to what comes after. `onRef_next`:
an instruction the executor runs along the reference leaves it on the reference, or in the final
state. `stepOk_conj`: a predicate the hints and the instruction preserve joins a step's obligations.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-! ## The reference -/

theorem onRef_moves {prog : LeanIsaProgram} {κ n : ℕ} {img : MemoryImage κ} {M : ℕ → E} {s s1 : St}
    (hm : Moves M s s1) (h : OnRef prog img n s) : OnRef prog img n s1 := by
  unfold OnRef
  rw [hm.steps, hm.pc, hm.fp]
  exact h

theorem onRef_not_halted {prog : LeanIsaProgram} {κ n : ℕ} {img : MemoryImage κ} {s : St}
    (h : OnRef prog img n s) : ¬Halted prog s := by
  intro hH
  obtain ⟨hlt, hrun⟩ := h
  obtain ⟨k, hk⟩ : ∃ k, n - s.steps = k + 1 := ⟨n - s.steps - 1, by omega⟩
  unfold Halted at hH
  rw [hk, run_succ, ite_eq_left hH] at hrun
  cases hrun

theorem halted_of {prog : LeanIsaProgram} {s : St} (hpc : s.pc = 2 ^ prog.logSize - 1) (hfp : s.fp = 0) :
    Halted prog s := by
  unfold Halted Registers.final LeanIsaProgram.pcFinal
  rw [hpc, hfp, pow_zero]

/-- **The next state is on the reference**, or final: an instruction the executor runs, moded,
from a state on the reference. -/
theorem onRef_next {prog : LeanIsaProgram} {adv : Advice} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx}
    (hκ : κ ≤ 28) (hC : Ctx.of prog adv = .ok C) {s s' : St} {op : Op} (hs : Fine (refMem img) s)
    (hon : OnRef prog img n s) (hop : C.ops[s.pc]? = some op) (hmo : OpModed (refMem img) s op)
    (e : runOp C s op = .ok s') :
    OnRef prog img n { s' with steps := s'.steps + 1 } ∨ Halted prog s' := by
  obtain ⟨hsize, hdecC⟩ := ctx_of_spec hC
  have hsz : C.ops.size ≤ 2 ^ 30 := hsize ▸ Nat.pow_le_pow_right (by norm_num) prog.logSize_le
  obtain ⟨hlt, hrun⟩ := hon
  obtain ⟨hpc, hop'⟩ := Array.getElem?_eq_some_iff.mp hop
  subst hop'
  have hpc2 : s.pc < 2 ^ prog.logSize := hsize ▸ hpc
  obtain ⟨k, hk⟩ : ∃ k, n - s.steps = k + 1 := ⟨n - s.steps - 1, by omega⟩
  rw [hk] at hrun
  have hne : (⟨g ^ s.pc, g ^ s.fp⟩ : Registers K) ≠ Registers.final prog := fun h ↦ by
    rw [run_succ, ite_eq_left h] at hrun; cases hrun
  rw [run_succ_of_ne_final hne, Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun
  obtain ⟨r1, hstep, hrun1⟩ := hrun
  rw [step_of_fetch_eq_some (prog.fetch_gpow ⟨s.pc, hpc2⟩), LeanVM.Semantics.execute] at hstep
  obtain ⟨s2, e2, d2⟩ := runOp_complete hs (refRd_img hκ img) (hdecC s.pc hpc2 hpc) (ctx_small hC s.pc hpc)
    hpc hsz (nextOk_of_run hsize hrun1) hstep hmo
  rw [e] at e2
  cases e2
  cases k with
  | zero =>
    right
    rw [run_zero, Option.some.injEq] at hrun1
    exact d2.regs.trans hrun1
  | succ k =>
    left
    refine ⟨by dsimp only; rw [d2.steps]; omega, ?_⟩
    dsimp only
    rw [d2.steps, show n - (s.steps + 1) = k + 1 by omega, d2.regs]
    exact hrun1

/-- The reference's part of an instruction's modedness reads only the frame. -/
theorem RefOk.congr {M : ℕ → E} {s s1 : St} (hfp : s1.fp = s.fp) {op : Op} (h : RefOk M s op) :
    RefOk M s1 op := by
  cases op with
  | deref a o c mode => simpa only [RefOk, hfp] using h
  | jump c d f => simpa only [RefOk, hfp] using h
  | _ => trivial

/-! ## A predicate the step preserves -/

/-- **A predicate the step keeps**: the hints' and the instruction's, joined to the step's
obligations. -/
theorem stepOk_conj {C : Ctx} {M : ℕ → E} {op : Op} {I J : St → Prop} (X : St → Prop) (s0 : St) :
    ∀ (l : List Hint) (s : St), X s → Moves M s0 s →
      (∀ s1 h s2, X s1 → Moves M s0 s1 → h ∈ l → runHint C s1 h = .ok s2 → X s2) →
      (∀ s1 s', X s1 → Moves M s0 s1 → runOp C s1 op = .ok s' → Fine M s' →
        I { s' with steps := s'.steps + 1 } → J { s' with steps := s'.steps + 1 }) →
      StepOk C M I op l s → StepOk C M J op l s
  | [], s, hX, hm, _, hJ, ⟨h1, h2⟩ => ⟨h1, fun s' e hf hle ↦ hJ s s' hX hm e hf (h2 s' e hf hle)⟩
  | x :: l, s, hX, hm, hh, hJ, ⟨h1, h2⟩ => ⟨h1, fun s' e m ↦
      stepOk_conj X s0 l s' (hh s x s' hX hm (List.mem_cons_self ..) e) (hm.trans m)
        (fun s1 h s2 a b c d ↦ hh s1 h s2 a b (List.mem_cons_of_mem _ c) d) hJ (h2 s' e m)⟩

/-! ## The step, the states the hints pass through kept -/

theorem stepOk_hintsX {C : Ctx} {M : ℕ → E} {Inv : St → Prop} {op : Op} (P : St → Prop) (s0 : St) :
    ∀ (hs : List Hint) (s : St) (A A' : Abs), Moves M s0 s → P s → Holds s A → stepHints A hs = some A' →
      (∀ s1 h s2, P s1 → Moves M s0 s1 → h ∈ hs → runHint C s1 h = .ok s2 → P s2) →
      (∀ s1 h, P s1 → Moves M s0 s1 → h ∈ hs → HintIn s1 h → HintOk C M s1 h) →
      (∀ s1, P s1 → Moves M s0 s1 → Holds s1 A' → StepOk C M Inv op [] s1) → StepOk C M Inv op hs s
  | [], s, A, A', hm, hP, hA, h, _, _, hk => by
    cases h
    exact hk s hP hm hA
  | x :: xs, s, A, A', hm, hP, hA, h, hPh, hh, hk => by
    simp only [stepHints, Option.bind_eq_some_iff] at h
    obtain ⟨B, hB, h⟩ := h
    have hs := hm.fine
    have hin := (stepHint_sound (C := C) (s' := s) ⟨hs.agree.wf, hs.dl⟩ hs.fp hs.agree.used hA hB).1
    refine ⟨hh s x hP hm (List.mem_cons_self ..) hin, fun s1 e1 m1 ↦ ?_⟩
    have hrun := (stepHint_sound (C := C) (s' := s1) ⟨hs.agree.wf, hs.dl⟩ hs.fp hs.agree.used hA hB).2
    exact stepOk_hintsX P s0 xs s1 B A' (hm.trans m1) (hPh s x s1 hP hm (List.mem_cons_self ..) e1)
      (hrun e1 m1.fine.agree.used) h
      (fun s2 y s3 a b c d ↦ hPh s2 y s3 a b (List.mem_cons_of_mem _ c) d)
      (fun s2 y a b c d ↦ hh s2 y a b (List.mem_cons_of_mem _ c) d) hk

/-- **A step at an offset the walk reaches**, as `step_at`, the states its hints pass through
satisfying `P`: each hint's agreement and the residuals needed only there, and what comes after
given the state before the instruction, its modedness and its run. -/
theorem step_atX {C : Ctx} {M : ℕ → E} {Inv : St → Prop} {K : Cert} (hK : CertOk C K)
    {s : St} {i : ℕ} (hi : i < K.code.length) (hpc : s.pc = K.F.entry + i)
    (hat : AtOff K.E K.F K.code i s) (hs : Fine M s) (hE : EnvOk s K.E) (P : St → Prop) (hP : P s)
    (hPh : ∀ s1 h s2, P s1 → Moves M s s1 → h ∈ (K.F.hints.get i).getD [] → runHint C s1 h = .ok s2 →
      P s2)
    (hhint : ∀ s1 h, P s1 → Moves M s s1 → h ∈ (K.F.hints.get i).getD [] → HintIn s1 h →
      HintOk C M s1 h)
    (hres : ∀ s1, P s1 → Moves M s s1 → ∀ r ∈ (K.F.res.get i).getD [], ResIn s1 r → ResHolds s1 r)
    (href : RefOk M s (opOfOff K.code[i]))
    (hfall : ∀ s1 s', P s1 → Moves M s s1 → OpModed M s1 (opOfOff K.code[i]) →
      runOp C s1 (opOfOff K.code[i]) = .ok s' → s'.pc = s.pc + 1 → s'.fp = s.fp → Fine M s' →
      s.mem ≤ s'.mem → AtOff K.E K.F K.code (i + 1) s' → Inv { s' with steps := s'.steps + 1 })
    (hjump : ∀ c d f A go A' s1 s', P s1 → K.code[i] = .jump c d f → Moves M s s1 →
      OpModed M s1 (.jump c d f) → Holds s1 A →
      jumpI K.E K.F i A d f = some (go, A') →
      (∀ ts, go = .to ts → ∀ s'' j, j ∈ ts → Holds s'' A' → AtOff K.E K.F K.code j s'') →
      runOp C s1 (.jump c d f) = .ok s' → Fine M s' → s1.mem ≤ s'.mem → s'.pc < C.ops.size →
      s1.mem.get (s1.fp + d) = some (ofK (g ^ s'.pc)) →
      s1.mem.get (s1.fp + f) = some (ofK (g ^ s'.fp)) → Inv { s' with steps := s'.steps + 1 }) :
    StepOk C M Inv (opOfOff K.code[i]) ((C.hints[s.pc]?).getD []) s := by
  have hops := hK.ops i hi
  obtain ⟨A, hA, pa, cs, pb, e, -, hnext, hcov⟩ := atOff_step hK.walk hi hat
  obtain ⟨A1, A2, h1, h2, hc⟩ := offStep_cases e
  have hsz : K.F.entry + i < C.ops.size := cert_pc hK hi
  rw [hpc, hK.hints i hi]
  refine stepOk_hintsX P s _ s A A1 (Moves.refl' hs) hP hA h1 hPh hhint (fun s1 hP1 hm hA1 ↦ ?_)
  have hA2 : Holds s1 A2 :=
    addRes_sound' hm.fine.agree.wf hm.fine.agree.used hA1 (hres s1 hP1 hm) h2
  have hg1 : s1.Good := ⟨hm.fine.agree.wf, hm.fine.dl⟩
  have hpc1 : s1.pc = K.F.entry + i := hm.pc.trans hpc
  have hE1 : EnvOk s1 K.E := EnvOk.mono hm.le hE
  have href1 : RefOk M s1 (opOfOff K.code[i]) := href.congr hm.fp
  rcases hc with ⟨hnj, A3, h3, rfl⟩ | ⟨c, d, f, hins, h3, hc⟩
  · obtain ⟨hreads, hstep⟩ := stepOp_sound (C := C) (s' := s1) hg1 hm.fine.fp (by rw [hpc1]; exact hsz)
      hm.fine.agree.used hE1 hA2 (by rw [hpc1]; exact h3)
    have hmo := opModed_of hm.fine.agree hreads href1
    refine ⟨hmo, fun s' e' hf' hle' ↦ ?_⟩
    have hH' := (stepOp_sound (C := C) (s' := s') hg1 hm.fine.fp (by rw [hpc1]; exact hsz)
      hm.fine.agree.used hE1 hA2 (by rw [hpc1]; exact h3)).2 hnj e'
    obtain ⟨hpc', hfp'⟩ := runOp_nj hg1 hm.fine.fp (by rw [hpc1]; exact hsz) hnj e'
    exact hfall s1 _ hP1 hm hmo e' (by rw [hpc', hm.pc]) (by rw [hfp', hm.fp]) hf'
      (Mem.le_trans hm.le hle') (hnext _ ⟨A3, List.mem_singleton_self _, hH'⟩)
  · have hop : opOfOff K.code[i] = .jump c d f := by rw [hins]; rfl
    obtain ⟨hreads, -⟩ := stepOp_sound (C := C) (s' := s1) hg1 hm.fine.fp (by rw [hpc1]; exact hsz)
      hm.fine.agree.used hE1 hA2 (by rw [hpc1]; exact h3)
    have hmo := opModed_of hm.fine.agree hreads href1
    refine ⟨hmo, fun s' e' hf' hle' ↦ ?_⟩
    have e'' := e'
    rw [hop] at e'' hmo
    obtain ⟨vc, vd, vf, hvc, hvd, hvf, -, hcase⟩ := jump_vals hg1 e''
    rcases hcase with ⟨rfl, hpc', hfp'⟩ | ⟨hne, rfl, rfl, hpcs, -⟩
    · have hL : Holds s1 (A2.learn0 c) := hA2.learn0 hvc
      have hmem : A2.learn0 c ∈ cs := by
        rcases hc with ⟨-, rfl⟩ | ⟨-, -, -, hm', -⟩
        · exact List.mem_singleton_self _
        · exact hm' fun ht ↦ condOf_true hA2 ht hvc rfl
      exact hfall s1 _ hP1 hm (hop ▸ hmo) e' (by rw [hpc', hm.pc]) (by rw [hfp', hm.fp]) hf'
        (Mem.le_trans hm.le hle') (hnext _ ⟨_, hmem, hL.mono hle' hfp'⟩)
    · rcases hc with ⟨hf0, -⟩ | ⟨go, A', hj, -, hcj⟩
      · exact absurd (condOf_false hA2 hf0 hvc) hne
      · exact hjump c d f A2 go A' s1 s' hP1 hins hm hmo hA2 hj
          (fun ts hgo s'' j hj hH ↦ hcov s'' j (hcj ts hgo s'' j hj hH)) e'' hf' hle' hpcs hvd hvf

end

end LeanVM.Guest.Mode
