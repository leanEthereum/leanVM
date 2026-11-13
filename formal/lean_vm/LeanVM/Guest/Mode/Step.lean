module

public import LeanVM.Guest.Mode.Pass
public import LeanVM.Guest.Mode.SoundLoop
public import LeanVM.Guest.Value.Tower
public import LeanVM.Prover.ExecuteComplete

/-!
# One step of a function's walk

A function's certificate (`Cert`: its walk's program, its view and its code) is tied to the
executor's tables by `CertOk`: the walk accepts the code, and the executor's instruction and hints at
each of its pcs are the code's and the walk's. `step_at`: an executor state at an offset the walk
reaches (`AtOff`) has its step's obligations (`StepOk`), given what the walk takes as hypotheses
there (each hint's agreement with the reference once its inputs are written, the residuals once their
cells are, and the reference's part of the instruction's modedness), what falls through being at the
next offset, and a taken `JUMP` handed over with what the walk knows of it (`jumpI`) and where the
executor goes (`jump_vals`).
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-! ## What a `JUMP` does -/

theorem ofK_limbs {x : E} (h1 : x.limb 1 = 0) : x = ofK (x.limb 0) :=
  E.ext fun l ↦ by fin_cases l <;> simp [h1]

/-- A `JUMP` reads three written cells, and falls through on `0` or goes where its target and frame
cells name. -/
theorem jump_vals {C : Ctx} {s s' : St} {c d f : ℕ} (hs : s.Good)
    (e : runOp C s (.jump c d f) = .ok s') :
    ∃ vc vd vf, s.mem.get (s.fp + c) = some vc ∧ s.mem.get (s.fp + d) = some vd ∧
      s.mem.get (s.fp + f) = some vf ∧ s.mem ≤ s'.mem ∧
      ((vc = 0 ∧ s'.pc = s.pc + 1 ∧ s'.fp = s.fp) ∨
        (vc ≠ 0 ∧ vd = ofK (g ^ s'.pc) ∧ vf = ofK (g ^ s'.fp) ∧ s'.pc < C.ops.size ∧
          s'.fp < maxCells)) := by
  simp only [runOp, bind_ok] at e
  obtain ⟨ca, hca, cb, hcb, cc, hcc, wc, hwc, vc, hvc, wd, hwd, vd, hvd, wf, hwf, vf, hvf, s1, hs1,
    e⟩ := e
  obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
  simp only [pure_ok] at hm; subst hm
  obtain ⟨rfl, -⟩ := cellAt_ok hca
  obtain ⟨rfl, -⟩ := cellAt_ok hcb
  obtain ⟨rfl, -⟩ := cellAt_ok hcc
  obtain ⟨hc1, rfl⟩ := inK_ok hvc
  obtain ⟨hd1, rfl⟩ := inK_ok hvd
  obtain ⟨hf1, rfl⟩ := inK_ok hvf
  have hle1 : s.mem ≤ ((s.mem.ensure (s.fp + c)).ensure (s.fp + d)).ensure (s.fp + f) :=
    Mem.le_trans (Mem.le_trans (Mem.le_ensure _ _) (Mem.le_ensure _ _)) (Mem.le_ensure _ _)
  have hwf1 := ((hs.wf.ensure (s.fp + c)).ensure (s.fp + d)).ensure (s.fp + f)
  refine ⟨wc, wd, wf, Mem.read_ok hwc, Mem.read_ok hwd, Mem.read_ok hwf, ?_⟩
  split_ifs at e with h0
  · simp only [pure_ok] at e; subst e
    exact ⟨hle1, Or.inl ⟨eq_zero_of_limbs h0 hc1, rfl, rfl⟩⟩
  · simp only [bind_ok, pure_ok] at e
    obtain ⟨⟨pc', s2⟩, h2, ⟨fp', s3⟩, h3, rfl⟩ := e
    obtain ⟨f2, hg2, hlt2⟩ := St.logOr_ok (by exact ⟨hwf1, hs.dl⟩) h2
    obtain ⟨f3, hg3, hlt3⟩ := St.logOr_ok f2.good h3
    refine ⟨Mem.le_trans hle1 (Mem.le_trans f2.le f3.le),
      Or.inr ⟨fun h ↦ h0 (by rw [h, limb_zero]), ?_, ?_, hlt2, hlt3⟩⟩
    · rw [ofK_limbs hd1, ← hg2]
    · rw [ofK_limbs hf1, ← hg3]

/-! ## Conditions -/

theorem imm_zero : OffsetInstruction.immediateWord 0 0 = 0 :=
  eq_zero_of_limbs (by simp [OffsetInstruction.immediateWord, show K.ofBits 0 = 0 from rfl])
    (by simp [OffsetInstruction.immediateWord, show K.ofBits 0 = 0 from rfl])

theorem imm_ne_zero {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : ¬(a = 0 ∧ b = 0)) :
    OffsetInstruction.immediateWord a b ≠ 0 := by
  intro h0
  have h1 := congrArg (·.limb 0) h0
  have h2 := congrArg (·.limb 1) h0
  simp only [OffsetInstruction.immediateWord, limb_ofLimbs, limb_zero] at h1 h2
  exact h ⟨Value.ofBits_inj ha (by norm_num) (h1.trans rfl), Value.ofBits_inj hb (by norm_num) (h2.trans rfl)⟩

/-- A condition the walk knows `0` is. -/
theorem condOf_false {s : St} {A : Abs} (hA : Holds s A) {c : ℕ} (h : condOf A c = some false)
    {v : E} (hv : s.mem.get (s.fp + c) = some v) : v = 0 := by
  unfold condOf at h
  split_ifs at h with hn
  · cases h
  split at h
  · rename_i a b hab
    by_cases h1 : (a == 0 && b == 0) = true
    swap
    · rw [ite_eq_right h1] at h; split_ifs at h; cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨u, hu, hok⟩ := hA.v c _ hab
    rw [hv] at hu; cases hu
    exact hok.trans imm_zero
  · cases h
  · cases h

/-- A condition the walk knows nonzero is. -/
theorem condOf_true {s : St} {A : Abs} (hA : Holds s A) {c : ℕ} (h : condOf A c = some true)
    {v : E} (hv : s.mem.get (s.fp + c) = some v) : v ≠ 0 := by
  unfold condOf at h
  split_ifs at h with hn
  · obtain ⟨u, hu, hne⟩ := hA.nz c (Abs.hasNz_get hn)
    rw [hv] at hu; cases hu; exact hne
  split at h
  · rename_i a b hab
    by_cases h1 : (a == 0 && b == 0) = true
    · rw [ite_eq_left h1] at h; cases h
    rw [ite_eq_right h1] at h
    by_cases h2 : (decide (a < 2 ^ 64) && decide (b < 2 ^ 64)) = true
    swap
    · rw [ite_eq_right h2] at h; cases h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1 h2
    obtain ⟨u, hu, hok⟩ := hA.v c _ hab
    rw [← Option.some.inj (hu.symm.trans hv), show u = _ from hok]
    exact imm_ne_zero h2.1 h2.2 h1
  · rename_i x y hxy
    obtain ⟨u, hu, w, hw, hok⟩ := hA.v c _ hxy
    rw [← Option.some.inj (hu.symm.trans hv), hok, show w = 1 from hw, mul_one]
    exact mul_ne_zero (pow_ne_zero _ (ofK_gpow_ne_zero _)) (ofK_gpow_ne_zero _)
  · cases h

/-! ## Residuals -/

/-- An exponent's base has a word. -/
def IdxIn (s : St) : Idx → Prop
  | .num _ => True
  | .ex b _ => ∃ v, BaseVal s b v

/-- A residual's cells are written. -/
def ResIn (s : St) : Res → Prop
  | .lt a b => IdxIn s a ∧ IdxIn s b
  | .nz o => s.mem.written (s.fp + o) = true

theorem addRes_idxIn {s : St} {A : Abs} (hA : Holds s A) (hwf : s.mem.WF) (hu : s.mem.used ≤ maxCells)
    {i : Idx} (h : (match i with
      | .ex (.fr o) _ => A.hasW o
      | .ex (.hp q d) _ => A.covered ⟨0, d, [(.fr q, 1)]⟩
      | .num _ => true) = true) : IdxIn s i := by
  match i, h with
  | .num _, _ => trivial
  | .ex (.fr o) _, h => exact Mem.get_of_written (hA.written h)
  | .ex (.hp q d) _, h =>
    obtain ⟨vk, x, hk, hx, hw⟩ := Abs.covered_cell hA hwf hu h
    obtain ⟨p, hp, rfl⟩ := MonoVal.ptr.mp hk
    obtain ⟨v, hv⟩ := Mem.get_of_written hw
    exact ⟨v, p, x, hp, by rw [mul_comm]; exact hx, hv⟩

/-- **The residuals**, holding of their cells once written, keep the walk's set. -/
theorem addRes_sound' {s : St} (hwf : s.mem.WF) (hu : s.mem.used ≤ maxCells) :
    ∀ {A A' : Abs} {rs : List Res}, Holds s A → (∀ r ∈ rs, ResIn s r → ResHolds s r) →
      addRes A rs = some A' → Holds s A'
  | _, _, [], hH, _, h => by cases h; exact hH
  | A, A', .lt a b :: rs, hH, hr, h => by
    simp only [addRes] at h
    split_ifs at h with hab
    simp only [Bool.and_eq_true] at hab
    have hin : ResIn s (.lt a b) := ⟨addRes_idxIn hH hwf hu hab.1, addRes_idxIn hH hwf hu hab.2⟩
    exact addRes_sound' hwf hu (hH.addLt (hr _ (List.mem_cons_self ..) hin))
      (fun r hm ↦ hr r (List.mem_cons_of_mem _ hm)) h
  | A, A', .nz o :: rs, hH, hr, h => by
    simp only [addRes] at h
    split_ifs at h with ho
    exact addRes_sound' hwf hu (hH.addNz (hr _ (List.mem_cons_self ..) (hH.written ho)))
      (fun r hm ↦ hr r (List.mem_cons_of_mem _ hm)) h

/-! ## One path's step, by cases -/

theorem jumpBind_cases {i : ℕ} {pend pend' : Pend} {cs fall : List Abs} {o : Option (Go × Abs)}
    (h : (o.bind fun a ↦ match a.1 with
      | Go.to ts => if ((ts.all fun x ↦ decide (i < x)) && incr ts) = true then
          some (fall, if ts.isEmpty = true then pend else a.2.force fun A' ↦ addGrp ts A' pend) else none
      | Go.out => some (fall, pend)) = some (cs, pend')) :
    cs = fall ∧ ∃ go A', o = some (go, A') ∧
      ∀ ts, go = .to ts → ∀ s j, j ∈ ts → Holds s A' → Cov s pend' j := by
  obtain ⟨⟨go, A'⟩, ho, h⟩ := Option.bind_eq_some_iff.mp h
  rcases go with ts | _
  · dsimp only at h
    split_ifs at h with h1 h2
    · cases h
      refine ⟨rfl, _, A', ho, fun ts' hts s j hj _ ↦ ?_⟩
      cases hts
      rw [List.isEmpty_iff.mp h2] at hj
      exact absurd hj List.not_mem_nil
    · cases h
      refine ⟨rfl, _, A', ho, fun ts' hts s j hj hH ↦ ?_⟩
      cases hts
      rw [Abs.force_eq]
      exact addGrp_new hH hj _
  · cases h
    exact ⟨rfl, _, A', ho, fun _ h ↦ Go.noConfusion h⟩

/-- What one path's step is: its hints, its residuals, and its instruction, a `JUMP` falling through
or taken as `jumpI` says. -/
theorem offStep_cases {E : Env} {F : Fun} {i : ℕ} {A : Abs} {ins : OffsetInstruction}
    {pa pb : Pend} {cs : List Abs} (h : offStep E F i A ins pa = some (cs, pb)) :
    ∃ A1 A2, stepHints A ((F.hints.get i).getD []) = some A1 ∧
      addRes A1 ((F.res.get i).getD []) = some A2 ∧
      (((∀ c d f, ins ≠ .jump c d f) ∧ ∃ A3, stepOp E (F.entry + i) A2 ins = some A3 ∧ cs = [A3]) ∨
       (∃ c d f, ins = .jump c d f ∧ stepOp E (F.entry + i) A2 ins = some A2 ∧
         ((condOf A2 c = some false ∧ cs = [A2.learn0 c]) ∨
          (∃ go A', jumpI E F i A2 d f = some (go, A') ∧
            (condOf A2 c ≠ some true → A2.learn0 c ∈ cs) ∧
            ∀ ts, go = .to ts → ∀ s j, j ∈ ts → Holds s A' → Cov s pb j)))) := by
  unfold offStep at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨A1, h1, A2, h2, h⟩ := h
  refine ⟨A1, A2, h1, h2, ?_⟩
  split at h
  · rename_i c d f
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨A3, h3, h⟩ := h
    have hA3 : A3 = A2 := by
      simp only [stepOp] at h3
      split_ifs at h3
      exact (Option.some.inj h3).symm
    rw [hA3] at h h3
    refine Or.inr ⟨c, d, f, rfl, h3, ?_⟩
    split at h
    · rename_i hk
      cases h
      exact Or.inl ⟨hk, rfl⟩
    · split at h
      · rename_i ht
        obtain ⟨rfl, go, A', ho, hc⟩ := jumpBind_cases h
        exact Or.inr ⟨go, A', ho, fun hne ↦ absurd (beq_iff_eq.mp ht) hne, hc⟩
      · obtain ⟨rfl, go, A', ho, hc⟩ := jumpBind_cases h
        exact Or.inr ⟨go, A', ho, fun _ ↦ List.mem_singleton_self _, hc⟩
  · rename_i hnj
    obtain ⟨A3, h3, h⟩ := Option.map_eq_some_iff.mp h
    cases h
    exact Or.inl ⟨fun c d f he ↦ hnj c d f he, A3, h3, rfl⟩

/-! ## A function's certificate -/

/-- What one function's walk is: its program, its view, and its code. -/
structure Cert where
  E : Env
  F : Fun
  code : List OffsetInstruction

/-- The walk accepts the function's code, which, with the walk's hints, is the executor's at its
pcs. -/
structure CertOk (C : Ctx) (K : Cert) : Prop where
  walk : walk K.E K.F K.code = true
  len : K.F.len = K.code.length
  ops : ∀ i (hi : i < K.code.length), C.ops[K.F.entry + i]? = some (opOfOff K.code[i])
  hints : ∀ i < K.code.length, (C.hints[K.F.entry + i]?).getD [] = (K.F.hints.get i).getD []

/-! ## The step -/

theorem Moves.refl' {M : ℕ → E} {s : St} (hs : Fine M s) : Moves M s s :=
  ⟨hs, Mem.le_refl _, rfl, rfl, rfl⟩

/-- **The hints**: each one's needs, once its inputs are written, and the instruction's
obligations after them. -/
theorem stepOk_hints {C : Ctx} {M : ℕ → E} {Inv : St → Prop} {op : Op} :
    ∀ (hs : List Hint) (s : St) (A A' : Abs), Fine M s → Holds s A → stepHints A hs = some A' →
      (∀ s1 h, Moves M s s1 → h ∈ hs → HintIn s1 h → HintOk C M s1 h) →
      (∀ s1, Moves M s s1 → Holds s1 A' → StepOk C M Inv op [] s1) → StepOk C M Inv op hs s
  | [], s, A, A', hs, hA, h, _, hk => by
    cases h
    exact hk s (Moves.refl' hs) hA
  | x :: xs, s, A, A', hs, hA, h, hh, hk => by
    simp only [stepHints, Option.bind_eq_some_iff] at h
    obtain ⟨B, hB, h⟩ := h
    have hin := (stepHint_sound (C := C) (s' := s) ⟨hs.agree.wf, hs.dl⟩ hs.fp hs.agree.used hA hB).1
    refine ⟨hh s x (Moves.refl' hs) (List.mem_cons_self ..) hin, fun s1 e1 m1 ↦ ?_⟩
    have hrun := (stepHint_sound (C := C) (s' := s1) ⟨hs.agree.wf, hs.dl⟩ hs.fp hs.agree.used hA hB).2
    exact stepOk_hints xs s1 B A' m1.fine (hrun e1 m1.fine.agree.used) h
      (fun s2 y m2 hy hi ↦ hh s2 y (m1.trans m2) (List.mem_cons_of_mem _ hy) hi)
      (fun s2 m2 hB2 ↦ hk s2 (m1.trans m2) hB2)

theorem runOp_nj {C : Ctx} {s s' : St} {ins : OffsetInstruction} (hs : s.Good) (hfp : s.fp < maxCells)
    (hpc : s.pc < C.ops.size) (hnj : ∀ c d f, ins ≠ .jump c d f) (e : runOp C s (opOfOff ins) = .ok s') :
    s'.pc = s.pc + 1 ∧ s'.fp = s.fp := by
  cases ins with
  | keccak =>
    obtain ⟨-, h1, h2, -⟩ := keccak_writes hs e
    exact ⟨h2, h1⟩
  | jump c d f => exact absurd rfl (hnj c d f)
  | xor | mul | set | deref =>
    obtain ⟨h1, h2, -⟩ := runOp_next hs hfp hpc e (fun _ _ _ h ↦ by cases h) (fun _ _ _ _ _ h ↦ by cases h)
    exact ⟨h1, h2⟩

theorem Holds.steps {s : St} {A : Abs} (h : Holds s A) (n : ℕ) : Holds { s with steps := n } A :=
  Holds.mono (s := s) (s' := { s with steps := n }) (Mem.le_refl s.mem) rfl h

theorem fine_steps {M : ℕ → E} {s : St} (h : Fine M s) (n : ℕ) : Fine M { s with steps := n } :=
  ⟨h.agree, h.dl, h.small, h.fp⟩

/-- **A step at an offset the walk reaches** has its obligations: the hints' and the instruction's
needs, and the invariant after it, given it at the next offset (`hfall`) and after a taken `JUMP`
(`hjump`, with what the walk knows there and the edges it adds). -/
theorem step_at {C : Ctx} {M : ℕ → E} {Inv : St → Prop} {K : Cert} (hK : CertOk C K)
    {s : St} {i : ℕ} (hi : i < K.code.length) (hpc : s.pc = K.F.entry + i)
    (hat : AtOff K.E K.F K.code i s) (hs : Fine M s) (hE : EnvOk s K.E)
    (hhint : ∀ s1 h, Moves M s s1 → h ∈ (K.F.hints.get i).getD [] → HintIn s1 h → HintOk C M s1 h)
    (hres : ∀ s1, Moves M s s1 → ∀ r ∈ (K.F.res.get i).getD [], ResIn s1 r → ResHolds s1 r)
    (href : ∀ s1, Moves M s s1 → RefOk M s1 (opOfOff K.code[i]))
    (hfall : ∀ s', s'.pc = s.pc + 1 → s'.fp = s.fp → Fine M s' → s.mem ≤ s'.mem →
      AtOff K.E K.F K.code (i + 1) s' → Inv { s' with steps := s'.steps + 1 })
    (hjump : ∀ c d f A go A' s1 s', K.code[i] = .jump c d f → Moves M s s1 → Holds s1 A →
      jumpI K.E K.F i A d f = some (go, A') →
      (∀ ts, go = .to ts → ∀ s'' j, j ∈ ts → Holds s'' A' → AtOff K.E K.F K.code j s'') →
      runOp C s1 (.jump c d f) = .ok s' → Fine M s' → s1.mem ≤ s'.mem →
      s1.mem.get (s1.fp + d) = some (ofK (g ^ s'.pc)) →
      s1.mem.get (s1.fp + f) = some (ofK (g ^ s'.fp)) → Inv { s' with steps := s'.steps + 1 }) :
    StepOk C M Inv (opOfOff K.code[i]) ((C.hints[s.pc]?).getD []) s := by
  have hops := hK.ops i hi
  obtain ⟨A, hA, pa, cs, pb, e, -, hnext, hcov⟩ := atOff_step hK.walk hi hat
  obtain ⟨A1, A2, h1, h2, hc⟩ := offStep_cases e
  have hsz : K.F.entry + i < C.ops.size := by
    by_contra hn
    rw [Array.getElem?_eq_none (by omega)] at hops
    cases hops
  rw [hpc, hK.hints i hi]
  refine stepOk_hints _ s A A1 hs hA h1 hhint (fun s1 hm hA1 ↦ ?_)
  have hA2 : Holds s1 A2 :=
    addRes_sound' hm.fine.agree.wf hm.fine.agree.used hA1 (hres s1 hm) h2
  have hg1 : s1.Good := ⟨hm.fine.agree.wf, hm.fine.dl⟩
  have hpc1 : s1.pc = K.F.entry + i := hm.pc.trans hpc
  have hE1 : EnvOk s1 K.E := EnvOk.mono hm.le hE
  rcases hc with ⟨hnj, A3, h3, rfl⟩ | ⟨c, d, f, hins, h3, hc⟩
  · obtain ⟨hreads, hstep⟩ := stepOp_sound (C := C) (s' := s1) hg1 hm.fine.fp (by rw [hpc1]; exact hsz)
      hm.fine.agree.used hE1 hA2 (by rw [hpc1]; exact h3)
    refine ⟨opModed_of hm.fine.agree hreads (href s1 hm), fun s' e' hf' hle' ↦ ?_⟩
    have hH' := (stepOp_sound (C := C) (s' := s') hg1 hm.fine.fp (by rw [hpc1]; exact hsz)
      hm.fine.agree.used hE1 hA2 (by rw [hpc1]; exact h3)).2 hnj e'
    obtain ⟨hpc', hfp'⟩ := runOp_nj hg1 hm.fine.fp (by rw [hpc1]; exact hsz) hnj e'
    exact hfall _ (by rw [hpc', hm.pc]) (by rw [hfp', hm.fp]) (fine_steps hf' _)
      (Mem.le_trans hm.le hle') (hnext _ ⟨A3, List.mem_singleton_self _, hH'.steps _⟩)
  · have hop : opOfOff K.code[i] = .jump c d f := by rw [hins]; rfl
    obtain ⟨hreads, -⟩ := stepOp_sound (C := C) (s' := s1) hg1 hm.fine.fp (by rw [hpc1]; exact hsz)
      hm.fine.agree.used hE1 hA2 (by rw [hpc1]; exact h3)
    refine ⟨opModed_of hm.fine.agree hreads (href s1 hm), fun s' e' hf' hle' ↦ ?_⟩
    rw [hop] at e'
    obtain ⟨vc, vd, vf, hvc, hvd, hvf, -, hcase⟩ := jump_vals hg1 e'
    rcases hcase with ⟨rfl, hpc', hfp'⟩ | ⟨hne, rfl, rfl, -, -⟩
    · have hL : Holds s1 (A2.learn0 c) := hA2.learn0 hvc
      have hmem : A2.learn0 c ∈ cs := by
        rcases hc with ⟨-, rfl⟩ | ⟨-, -, -, hm', -⟩
        · exact List.mem_singleton_self _
        · exact hm' fun ht ↦ condOf_true hA2 ht hvc rfl
      exact hfall _ (by rw [hpc', hm.pc]) (by rw [hfp', hm.fp]) (fine_steps hf' _)
        (Mem.le_trans hm.le hle') (hnext _ ⟨_, hmem, (hL.mono hle' hfp').steps _⟩)
    · rcases hc with ⟨hf0, -⟩ | ⟨go, A', hj, -, hcj⟩
      · exact absurd (condOf_false hA2 hf0 hvc) hne
      · exact hjump c d f A2 go A' s1 s' hins hm hA2 hj
          (fun ts hgo s'' j hj hH ↦ hcov s'' j (hcj ts hgo s'' j hj hH)) e' hf' hle' hvd hvf

end

end LeanVM.Guest.Mode
