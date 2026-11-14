module

public import LeanVM.Prover.ExecuteHint
public import LeanVM.Semantics.KeccakCells
public import LeanVM.Parameters.Field

/-!
# The executor's instructions are steps

`Final M rd`: `M` is a well-formed memory whose image `rd` reads, every cell below `used` reading
its value, and whose links' cells agree. `runOp_spec`: a successful instruction, from a good state,
gives a good state extending it, and on every final memory extending that state the ISA steps from
the first state's registers to the second's (`OpSpec`).
-/

namespace LeanVM.Prover.Exec

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- A final memory and a reader of its image. -/
structure Final (M : Mem) (rd : K → Option E) : Prop where
  wf : M.WF
  read : ∀ c, c < M.used → rd (g ^ c) = some (M.peek c)
  links : ∀ p ∈ M.links, M.peek p.1 = M.peek p.2

theorem Final.get {M : Mem} {rd : K → Option E} (hF : Final M rd) {m : Mem} (hm : m ≤ M) {c : ℕ}
    {v : E} (h : m.get c = some v) : rd (g ^ c) = some v := by
  have h' := hm.get c v h
  rw [hF.read c (hF.wf.get_lt h'), Mem.peek, h']
  rfl

/-- What a successful instruction gives. -/
structure OpSpec (ins : LeanIsaInstruction) (nops : ℕ) (s s' : St) : Prop where
  good : s'.Good
  le : s.mem ≤ s'.mem
  steps : s'.steps = s.steps
  pc : s'.pc ≤ nops
  fp : s'.fp < maxCells
  exec : ∀ M rd, s'.mem ≤ M → Final M rd →
    executeWith rd ⟨g ^ s.pc, g ^ s.fp⟩ ins = some ⟨g ^ s'.pc, g ^ s'.fp⟩

theorem next_gpow (pc fp : ℕ) :
    (⟨g ^ pc, g ^ fp⟩ : Registers K).next = ⟨g ^ (pc + 1), g ^ fp⟩ := by
  rw [Registers.next, pow_succ']

theorem xor_spec {C : Ctx} {s s' : St} {a b c : ℕ} (hs : s.Good) (hfp : s.fp < maxCells)
    (hpc : s.pc < C.ops.size) (e : runOp C s (.xor a b c) = .ok s') :
    OpSpec (.xor (g ^ a) (g ^ b) (g ^ c)) C.ops.size s s' := by
  simp only [runOp, bind_ok] at e
  obtain ⟨ca, hca, cb, hcb, cc, hcc, va, hva, vb, hvb, s1, hs1, e⟩ := e
  simp only [pure_ok] at e; subst e
  obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
  rw [bind_ok] at hm
  obtain ⟨m1, hm1, hm⟩ := hm
  simp only [pure_ok] at hm; subst hm
  obtain ⟨hle1, hwf1, hput⟩ := Mem.put_ok hs.wf hm1
  have hle2 : m1 ≤ (m1.ensure ca).ensure cb := Mem.le_trans (Mem.le_ensure _ _) (Mem.le_ensure _ _)
  obtain ⟨rfl, -⟩ := cellAt_ok hca
  obtain ⟨rfl, -⟩ := cellAt_ok hcb
  obtain ⟨rfl, -⟩ := cellAt_ok hcc
  refine ⟨⟨(hwf1.ensure _).ensure _, hs.dl⟩, Mem.le_trans hle1 hle2, rfl, hpc, hfp, ?_⟩
  intro M rd hM hF
  have hleM : s.mem ≤ M := Mem.le_trans (Mem.le_trans hle1 hle2) hM
  have hra := hF.get hleM (Mem.read_ok hva)
  have hrb := hF.get hleM (Mem.read_ok hvb)
  have hrc := hF.get (Mem.le_trans hle2 hM) hput
  simp only [executeWith, ← pow_add, hra, hrb, hrc, guard, Option.pure_def, Option.failure_eq_none,
    next_gpow, Option.bind_eq_bind, Option.bind_some, ↓reduceIte]

theorem mul_spec {C : Ctx} {s s' : St} {a b c : ℕ} (hs : s.Good) (hfp : s.fp < maxCells)
    (hpc : s.pc < C.ops.size) (e : runOp C s (.mul a b c) = .ok s') :
    OpSpec (.mulNative (g ^ a) (g ^ b) (g ^ c)) C.ops.size s s' := by
  simp only [runOp, bind_ok] at e
  obtain ⟨ca, hca, cb, hcb, cc, hcc, s1, hs1, e⟩ := e
  simp only [pure_ok] at e; subst e
  obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
  have key : ∃ m1, s.mem ≤ m1 ∧ m1.WF ∧ ∃ va vb m2, m1.read ca = .ok va ∧ m1.read cb = .ok vb ∧
      m1.put cc (va * vb) = .ok m2 ∧ m = (m2.ensure ca).ensure cb := by
    split_ifs at hm <;> simp only [bind_ok, pure_ok, throw_ok, false_and, exists_false] at hm
    all_goals first
      | (obtain ⟨m1, rfl, va, hva, vb, hvb, m2, hm2, rfl⟩ := hm
         exact ⟨_, Mem.le_refl _, hs.wf, va, vb, m2, hva, hvb, hm2, rfl⟩)
      | (obtain ⟨m1, hm1, va, hva, vb, hvb, m2, hm2, rfl⟩ := hm
         exact ⟨m1, (put_le hs.wf hm1).1, (put_le hs.wf hm1).2, va, vb, m2, hva, hvb, hm2, rfl⟩)
  obtain ⟨m1, hle0, hwf0, va, vb, m2, hva, hvb, hm2, rfl⟩ := key
  obtain ⟨hle1, hwf1, hput⟩ := Mem.put_ok hwf0 hm2
  have hle2 : m2 ≤ (m2.ensure ca).ensure cb := Mem.le_trans (Mem.le_ensure _ _) (Mem.le_ensure _ _)
  obtain ⟨rfl, -⟩ := cellAt_ok hca
  obtain ⟨rfl, -⟩ := cellAt_ok hcb
  obtain ⟨rfl, -⟩ := cellAt_ok hcc
  refine ⟨⟨(hwf1.ensure _).ensure _, hs.dl⟩, Mem.le_trans hle0 (Mem.le_trans hle1 hle2), rfl, hpc,
    hfp, ?_⟩
  intro M rd hM hF
  have hleM : m1 ≤ M := Mem.le_trans (Mem.le_trans hle1 hle2) hM
  have hra := hF.get hleM (Mem.read_ok hva)
  have hrb := hF.get hleM (Mem.read_ok hvb)
  have hrc := hF.get (Mem.le_trans hle2 hM) hput
  simp only [executeWith, ← pow_add, hra, hrb, hrc, guard, Option.pure_def, Option.failure_eq_none,
    next_gpow, Option.bind_eq_bind, Option.bind_some, ↓reduceIte]

theorem set_spec {C : Ctx} {s s' : St} {a : ℕ} {k : E} (hs : s.Good) (hfp : s.fp < maxCells)
    (hpc : s.pc < C.ops.size) (e : runOp C s (.set a k) = .ok s') :
    OpSpec (.setConstant (g ^ a) k) C.ops.size s s' := by
  simp only [runOp, bind_ok] at e
  obtain ⟨ca, hca, s1, hs1, e⟩ := e
  simp only [pure_ok] at e; subst e
  obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
  obtain ⟨hle1, hwf1, hput⟩ := Mem.put_ok hs.wf hm
  obtain ⟨rfl, -⟩ := cellAt_ok hca
  refine ⟨⟨hwf1, hs.dl⟩, hle1, rfl, hpc, hfp, ?_⟩
  intro M rd hM hF
  have hra := hF.get hM hput
  simp only [executeWith, ← pow_add, hra, guard, Option.pure_def, Option.failure_eq_none,
    next_gpow, Option.bind_eq_bind, Option.bind_some, ↓reduceIte]

theorem Mem.peek_of_get {m : Mem} {c : ℕ} {v : E} (h : m.get c = some v) : m.peek c = v := by
  rw [Mem.peek, h]; rfl

theorem Mem.get_of_written {m : Mem} {c : ℕ} (h : m.written c = true) : ∃ v, m.get c = some v :=
  Option.isSome_iff_exists.mp h

theorem Mem.get_of_not_written {m : Mem} {c : ℕ} (h : ¬ m.written c = true) : m.get c = none :=
  Option.not_isSome_iff_eq_none.mp h

theorem deref_exec {rd : K → Option E} {pc fp a b c base : ℕ} {mode : DerefMode} {p v2 v3 : E}
    (hp : rd (g ^ (fp + a)) = some p) (hpK : p.limb 1 = 0) (hgb : g ^ base = p.limb 0)
    (h3 : rd (g ^ (fp + c)) = some v3) (h2 : rd (g ^ (base + b)) = some v2)
    (hv : v2 = derefSource mode ⟨g ^ pc, g ^ fp⟩ v3) :
    executeWith rd ⟨g ^ pc, g ^ fp⟩ (.deref (g ^ a) (g ^ b) (g ^ c) mode) =
      some ⟨g ^ (pc + 1), g ^ fp⟩ := by
  have hpK' : IsInK p := hpK
  simp only [executeWith, ← pow_add, hp, ← hgb, h3, h2, hv, hpK', guard, Option.pure_def,
    Option.failure_eq_none, next_gpow, Option.bind_eq_bind, Option.bind_some, ↓reduceIte]

theorem deref_spec {C : Ctx} {s s' : St} {a b c : ℕ} {mode : DerefMode} (hs : s.Good)
    (hfp : s.fp < maxCells) (hpc : s.pc < C.ops.size) (e : runOp C s (.deref a b c mode) = .ok s') :
    OpSpec (.deref (g ^ a) (g ^ b) (g ^ c) mode) C.ops.size s s' := by
  simp only [runOp, bind_ok] at e
  obtain ⟨a1, ha1, p, hp, e⟩ := e
  split_ifs at e with hpk
  · simp [bind_ok] at e
  simp only [bind_ok] at e
  obtain ⟨⟨base, s2⟩, hlog, a2, ha2, a3, ha3, s3, hs3, e⟩ := e
  simp only [pure_ok] at e; subst e
  obtain ⟨f2, hgb, -⟩ := St.logOr_ok hs hlog
  obtain ⟨m', hm', rfl⟩ := St.withMem_ok hs3
  obtain ⟨rfl, -⟩ := cellAt_ok ha1
  obtain ⟨rfl, -⟩ := cellAt_ok ha2
  obtain ⟨rfl, -⟩ := cellAt_ok ha3
  have hpK : p.limb 1 = 0 := not_not.mp hpk
  have hp' := Mem.read_ok hp
  have hpc2 := f2.pc
  have hfp2 := f2.fp
  have hwf2 := f2.good.wf
  have key : ∃ m0, s2.mem ≤ m0 ∧ m0.WF ∧
      m' = ((m0.ensure (s.fp + a)).ensure (base + b)).ensure (s2.fp + c) ∧
      ∀ M rd, m0 ≤ M → Final M rd → (s2.fp + c < M.used → (base + b) < M.used →
        ∃ v2 v3, rd (g ^ (s2.fp + c)) = some v3 ∧ rd (g ^ (base + b)) = some v2 ∧
          v2 = derefSource mode ⟨g ^ s2.pc, g ^ s2.fp⟩ v3) := by
    cases mode with
    | cell =>
      simp only at hm'
      split_ifs at hm' with hw2 hw3
      · simp only [bind_ok, pure_ok] at hm'
        obtain ⟨m0, hm0, rfl⟩ := hm'
        obtain ⟨w, hw⟩ := Mem.get_of_written hw2
        obtain ⟨h1, h2, h3⟩ := Mem.put_ok hwf2 hm0
        refine ⟨m0, h1, h2, rfl, fun M rd hM hF _ _ ↦
          ⟨w, w, ?_, hF.get (Mem.le_trans h1 hM) hw, rfl⟩⟩
        rw [Mem.peek_of_get hw] at h3
        exact hF.get hM h3
      · simp only [bind_ok, pure_ok] at hm'
        obtain ⟨m0, hm0, rfl⟩ := hm'
        obtain ⟨w, hw⟩ := Mem.get_of_written hw3
        obtain ⟨h1, h2, h3⟩ := Mem.put_ok hwf2 hm0
        refine ⟨m0, h1, h2, rfl, fun M rd hM hF _ _ ↦
          ⟨w, w, hF.get (Mem.le_trans h1 hM) hw, ?_, rfl⟩⟩
        rw [Mem.peek_of_get hw] at h3
        exact hF.get hM h3
      · simp only [bind_ok, pure_ok] at hm'
        obtain ⟨m0, rfl, rfl⟩ := hm'
        obtain ⟨h1, h2, h3, -, -⟩ :=
          Mem.link_ok hwf2 (Mem.get_of_not_written hw2) (Mem.get_of_not_written hw3)
        refine ⟨_, h1, h2, rfl, fun M rd hM hF hu3 hu2 ↦
          ⟨M.peek (base + b), M.peek (s2.fp + c), hF.read _ hu3, hF.read _ hu2, ?_⟩⟩
        exact hF.links _ (hM.links _ h3)
    | pc =>
      simp only [bind_ok, pure_ok] at hm'
      obtain ⟨m0, hm0, rfl⟩ := hm'
      obtain ⟨h1, h2, h3⟩ := Mem.put_ok hwf2 hm0
      refine ⟨m0, h1, h2, rfl, fun M rd hM hF hu3 _ ↦ ⟨_, _, hF.read _ hu3, hF.get hM h3, ?_⟩⟩
      simp only [derefSource, pow_add, mul_comm]
    | fp =>
      simp only [bind_ok, pure_ok] at hm'
      obtain ⟨m0, hm0, rfl⟩ := hm'
      obtain ⟨h1, h2, h3⟩ := Mem.put_ok hwf2 hm0
      exact ⟨m0, h1, h2, rfl, fun M rd hM hF hu3 _ ↦ ⟨_, _, hF.read _ hu3, hF.get hM h3, rfl⟩⟩
  obtain ⟨m0, hle0, hwf0, rfl, hval⟩ := key
  have hle1 : m0 ≤ ((m0.ensure (s.fp + a)).ensure (base + b)).ensure (s2.fp + c) :=
    Mem.le_trans (Mem.le_trans (Mem.le_ensure _ _) (Mem.le_ensure _ _)) (Mem.le_ensure _ _)
  refine ⟨⟨((hwf0.ensure _).ensure _).ensure _, f2.good.dl⟩,
    Mem.le_trans f2.le (Mem.le_trans hle0 hle1),
    f2.steps, by rw [hpc2]; exact hpc, by rw [hfp2]; exact hfp, ?_⟩
  intro M rd hM hF
  obtain ⟨v2, v3, h3, h2, hv⟩ := hval M rd (Mem.le_trans hle1 hM) hF
    (lt_of_lt_of_le (by simp) hM.used) (lt_of_lt_of_le (by simp) hM.used)
  rw [hfp2] at h3
  simp only [hpc2, hfp2] at hv ⊢
  exact deref_exec (hF.get (Mem.le_trans f2.le (Mem.le_trans hle0 (Mem.le_trans hle1 hM))) hp')
    hpK hgb h3 h2 hv

theorem eq_zero_of_limbs {x : E} (h0 : x.limb 0 = 0) (h1 : x.limb 1 = 0) : x = 0 :=
  E.ext fun i ↦ by fin_cases i <;> simp [h0, h1, limb_zero]

theorem jump_spec {C : Ctx} {s s' : St} {a b c : ℕ} (hs : s.Good) (hfp : s.fp < maxCells)
    (hpc : s.pc < C.ops.size) (e : runOp C s (.jump a b c) = .ok s') :
    OpSpec (.jump (g ^ a) (g ^ b) (g ^ c)) C.ops.size s s' := by
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
  have hle1 : s.mem ≤ ((s.mem.ensure (s.fp + a)).ensure (s.fp + b)).ensure (s.fp + c) :=
    Mem.le_trans (Mem.le_trans (Mem.le_ensure _ _) (Mem.le_ensure _ _)) (Mem.le_ensure _ _)
  have hwf1 := ((hs.wf.ensure (s.fp + a)).ensure (s.fp + b)).ensure (s.fp + c)
  have hreads : ∀ M rd, s.mem ≤ M → Final M rd → rd (g ^ (s.fp + a)) = some wc ∧
      rd (g ^ (s.fp + b)) = some wd ∧ rd (g ^ (s.fp + c)) = some wf := fun M rd hM hF ↦
    ⟨hF.get hM (Mem.read_ok hwc), hF.get hM (Mem.read_ok hwd), hF.get hM (Mem.read_ok hwf)⟩
  have hcK : IsInK wc := hc1
  have hdK : IsInK wd := hd1
  have hfK : IsInK wf := hf1
  split_ifs at e with h0
  · simp only [pure_ok] at e; subst e
    refine ⟨⟨hwf1, hs.dl⟩, hle1, rfl, hpc, hfp, fun M rd hM hF ↦ ?_⟩
    obtain ⟨hra, hrb, hrc⟩ := hreads M rd (Mem.le_trans hle1 hM) hF
    have hz : wc = 0 := eq_zero_of_limbs h0 hc1
    subst hz
    simp only [executeWith, ← pow_add, hra, hrb, hrc, hcK, hdK, hfK, and_self, guard,
      Option.pure_def, Option.failure_eq_none, next_gpow, Option.bind_eq_bind, Option.bind_some,
      ↓reduceIte]
  · simp only [bind_ok, pure_ok] at e
    obtain ⟨⟨pc', s2⟩, h2, ⟨fp', s3⟩, h3, rfl⟩ := e
    obtain ⟨f2, hg2, hlt2⟩ := St.logOr_ok (by exact ⟨hwf1, hs.dl⟩) h2
    obtain ⟨f3, hg3, hlt3⟩ := St.logOr_ok f2.good h3
    refine ⟨⟨f3.good.wf, f3.good.dl⟩, Mem.le_trans hle1 (Mem.le_trans f2.le f3.le),
      f3.steps.trans f2.steps,
      hlt2.le, hlt3, fun M rd hM hF ↦ ?_⟩
    obtain ⟨hra, hrb, hrc⟩ :=
      hreads M rd (Mem.le_trans hle1 (Mem.le_trans f2.le (Mem.le_trans f3.le hM))) hF
    have hnz : wc ≠ 0 := fun h ↦ h0 (by rw [h, limb_zero])
    simp only [executeWith, ← pow_add, hra, hrb, hrc, hcK, hdK, hfK, hnz, and_self, guard,
      Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind, Option.bind_some,
      ↓reduceIte, hg2, hg3]

end

end LeanVM.Prover.Exec
