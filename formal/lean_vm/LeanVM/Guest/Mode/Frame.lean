module

public import LeanVM.Prover.ExecuteSound
public import LeanVM.Prover.ExecuteCompleteOp

/-!
# What one executor step writes

`Reads s op`: the cells instruction `op` reads at state `s` are written (a `MUL` either forward or
back-solved, its known operand nonzero), the written part of `OpModed`; with the reference's part
(`RefOk`) it gives `OpModed` (`opModed_of`). A step that is neither a `JUMP` nor a `KECCAK` moves to
the next `pc` in the same frame and extends the memory (`runOp_next`); an `XOR`, a `MUL` or a `SET`
writes its target (`runOp_writes`); a `DEREF` writes both its sides unless it links two unwritten
cells (`deref_writes`).
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Prover.Exec

@[expose] public section

/-- Frame cell `o` holds a nonzero word. -/
def NzAt (s : St) (o : ℕ) : Prop := ∃ u, s.mem.get (s.fp + o) = some u ∧ u ≠ 0

/-- The cells an instruction reads, written: the `written` conjuncts of `OpModed`, a back-solved
`MUL`'s known operand nonzero. -/
def Reads (s : St) : Op → Prop
  | .xor a b _ => s.mem.written (s.fp + a) = true ∧ s.mem.written (s.fp + b) = true
  | .mul a b c => (s.mem.written (s.fp + a) = true ∧ s.mem.written (s.fp + b) = true) ∨
    (s.mem.written (s.fp + c) = true ∧ s.mem.written (s.fp + a) = true ∧ NzAt s a) ∨
    (s.mem.written (s.fp + c) = true ∧ s.mem.written (s.fp + b) = true ∧ NzAt s b)
  | .set _ _ => True
  | .deref a _ _ _ => s.mem.written (s.fp + a) = true
  | .jump c d f => s.mem.written (s.fp + c) = true ∧ s.mem.written (s.fp + d) = true ∧
    s.mem.written (s.fp + f) = true
  | .keccak ins _ _ _ _ => ∀ i ∈ ins.toList, s.mem.written (s.fp + i) = true

/-- The reference's part of `OpModed`: a `DEREF`'s pointer and a taken `JUMP`'s frame are powers
below `maxCells`. -/
def RefOk (M : ℕ → E) (s : St) : Op → Prop
  | .deref a _ _ _ => ∃ b < maxCells, (M (s.fp + a)).limb 0 = g ^ b
  | .jump c _ f => M (s.fp + c) ≠ 0 → ∃ k < maxCells, (M (s.fp + f)).limb 0 = g ^ k
  | _ => True

/-- The reads written and the reference's part give `OpModed`, the memory agreeing with `M`. -/
theorem opModed_of {M : ℕ → E} {s : St} {op : Op} (hag : Agree s.mem M) (h1 : Reads s op)
    (h2 : RefOk M s op) : OpModed M s op := by
  have hnz : ∀ o, NzAt s o → M (s.fp + o) ≠ 0 := fun o ⟨u, hu, hne⟩ ↦ by rw [hag.get _ _ hu]; exact hne
  cases op with
  | xor => exact h1
  | mul =>
    rcases h1 with h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1, h2, hnz _ h3⟩)
    · exact Or.inr (Or.inr ⟨h1, h2, hnz _ h3⟩)
  | set => trivial
  | deref => exact ⟨h1, h2⟩
  | jump => exact ⟨h1.1, h1.2.1, h1.2.2, h2⟩
  | keccak => exact h1

/-! ## Monotonicity -/

theorem written_mono {m m' : Mem} (h : m ≤ m') {c : ℕ} (hw : m.written c = true) :
    m'.written c = true := by
  obtain ⟨v, hv⟩ := Mem.get_of_written hw
  simp [Mem.written, h.get c v hv]

theorem written_of_get {m : Mem} {c : ℕ} {v : E} (h : m.get c = some v) : m.written c = true := by
  simp [Mem.written, h]

/-! ## What a step does to the frame -/

/-- A step that is neither a `JUMP` nor a `KECCAK` moves to the next `pc`, keeps the frame and
extends the memory. -/
theorem runOp_next {C : Ctx} {s s' : St} {op : Op} (hs : s.Good) (hfp : s.fp < maxCells)
    (hpc : s.pc < C.ops.size) (e : runOp C s op = .ok s') (hj : ∀ c d f, op ≠ .jump c d f)
    (hk : ∀ i o a b n, op ≠ .keccak i o a b n) :
    s'.pc = s.pc + 1 ∧ s'.fp = s.fp ∧ s.mem ≤ s'.mem := by
  cases op with
  | xor a b c =>
    refine ⟨?_, ?_, (runOp_spec (ins := .xor (g ^ a) (g ^ b) (g ^ c)) hs hfp hpc
      (by simp [OpOf]) e).le⟩ <;>
    · simp only [runOp, bind_ok] at e
      obtain ⟨_, _, _, _, _, _, _, _, _, _, s1, hs1, e⟩ := e
      simp only [pure_ok] at e; subst e
      obtain ⟨m, -, rfl⟩ := St.withMem_ok hs1
      rfl
  | mul a b c =>
    refine ⟨?_, ?_, (runOp_spec (ins := .mulNative (g ^ a) (g ^ b) (g ^ c)) hs hfp hpc
      (by simp [OpOf]) e).le⟩ <;>
    · simp only [runOp, bind_ok] at e
      obtain ⟨_, _, _, _, _, _, s1, hs1, e⟩ := e
      simp only [pure_ok] at e; subst e
      obtain ⟨m, -, rfl⟩ := St.withMem_ok hs1
      rfl
  | set o k =>
    refine ⟨?_, ?_, (runOp_spec (ins := .setConstant (g ^ o) k) hs hfp hpc (by simp [OpOf]) e).le⟩ <;>
    · simp only [runOp, bind_ok] at e
      obtain ⟨_, _, s1, hs1, e⟩ := e
      simp only [pure_ok] at e; subst e
      obtain ⟨m, -, rfl⟩ := St.withMem_ok hs1
      rfl
  | deref a o c mode =>
    have hle := (runOp_spec (ins := .deref (g ^ a) (g ^ o) (g ^ c) mode) hs hfp hpc
      (by simp [OpOf]) e).le
    simp only [runOp, bind_ok] at e
    obtain ⟨a1, -, p, -, e⟩ := e
    split_ifs at e
    · simp [bind_ok] at e
    simp only [bind_ok] at e
    obtain ⟨⟨base, s2⟩, hlog, a2, -, a3, -, s3, hs3, e⟩ := e
    simp only [pure_ok] at e; subst e
    obtain ⟨f2, -, -⟩ := St.logOr_ok hs hlog
    obtain ⟨m', -, rfl⟩ := St.withMem_ok hs3
    exact ⟨congrArg (· + 1) f2.pc, f2.fp, hle⟩
  | jump c d f => exact absurd rfl (hj c d f)
  | keccak i o a b n => exact absurd rfl (hk i o a b n)

theorem put_written {m m' : Mem} {c : ℕ} {v : E} (hm : m.WF) (e : m.put c v = .ok m') :
    m'.written c = true :=
  written_of_get (Mem.put_ok hm e).2.2

/-- An `XOR`, a `MUL` or a `SET` writes its target. -/
theorem runOp_writes {C : Ctx} {s s' : St} {op : Op} {a b c : ℕ} {k : E} (hs : s.Good)
    (hc : op = .xor a b c ∨ op = .mul a b c ∨ op = .set c k) (e : runOp C s op = .ok s') :
    s'.mem.written (s.fp + c) = true := by
  rcases hc with rfl | rfl | rfl
  · simp only [runOp, bind_ok] at e
    obtain ⟨ca, -, cb, -, cc, hcc, va, -, vb, -, s1, hs1, e⟩ := e
    simp only [pure_ok] at e; subst e
    obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
    rw [bind_ok] at hm
    obtain ⟨m1, hm1, hm⟩ := hm
    simp only [pure_ok] at hm; subst hm
    obtain ⟨rfl, -⟩ := cellAt_ok hcc
    exact written_mono (Mem.le_trans (Mem.le_ensure _ _) (Mem.le_ensure _ _))
      (put_written hs.wf hm1)
  · simp only [runOp, bind_ok] at e
    obtain ⟨ca, -, cb, -, cc, hcc, s1, hs1, e⟩ := e
    simp only [pure_ok] at e; subst e
    obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
    obtain ⟨rfl, -⟩ := cellAt_ok hcc
    have key : ∃ (m1 m2 : Mem) (v : E), m1.WF ∧ m1.put (s.fp + c) v = .ok m2 ∧ m = (m2.ensure ca).ensure cb := by
      split_ifs at hm <;> simp only [bind_ok, pure_ok, throw_ok, false_and, exists_false] at hm
      all_goals first
        | (obtain ⟨m1, rfl, va, -, vb, -, m2, hm2, rfl⟩ := hm
           exact ⟨_, m2, _, hs.wf, hm2, rfl⟩)
        | (obtain ⟨m1, hm1, va, -, vb, -, m2, hm2, rfl⟩ := hm
           exact ⟨m1, m2, _, (put_le hs.wf hm1).2, hm2, rfl⟩)
    obtain ⟨m1, m2, v, hwf, hput, rfl⟩ := key
    exact written_mono (Mem.le_trans (Mem.le_ensure _ _) (Mem.le_ensure _ _)) (put_written hwf hput)
  · simp only [runOp, bind_ok] at e
    obtain ⟨cc, hcc, s1, hs1, e⟩ := e
    simp only [pure_ok] at e; subst e
    obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
    obtain ⟨rfl, -⟩ := cellAt_ok hcc
    exact put_written hs.wf hm

/-- A `DEREF` through frame cell `a`, word `v`, naming cell `base`: cell `base + o` is written
after it when its mode is not `cell` or one side was written, and so is cell `fp + c` in mode
`cell`. -/
theorem deref_writes {C : Ctx} {s s' : St} {a o c : ℕ} {mode : DerefMode} (hs : s.Good)
    (e : runOp C s (.deref a o c mode) = .ok s') :
    ∃ v base, s.mem.get (s.fp + a) = some v ∧ v.limb 0 = g ^ base ∧ base < maxCells ∧
      (mode ≠ .cell ∨ s.mem.written (base + o) = true ∨ s.mem.written (s.fp + c) = true →
        s'.mem.written (base + o) = true ∧
        (mode = .cell → s'.mem.written (s.fp + c) = true)) := by
  simp only [runOp, bind_ok] at e
  obtain ⟨a1, ha1, p, hp, e⟩ := e
  split_ifs at e
  · simp [bind_ok] at e
  simp only [bind_ok] at e
  obtain ⟨⟨base, s2⟩, hlog, a2, ha2, a3, ha3, s3, hs3, e⟩ := e
  simp only [pure_ok] at e; subst e
  obtain ⟨f2, hgb, hbl⟩ := St.logOr_ok hs hlog
  obtain ⟨m', hm', rfl⟩ := St.withMem_ok hs3
  obtain ⟨rfl, -⟩ := cellAt_ok ha1
  obtain ⟨rfl, -⟩ := cellAt_ok ha2
  obtain ⟨rfl, -⟩ := cellAt_ok ha3
  have hmem : s2.mem = s.mem := by
    unfold St.logOr at hlog; rw [St.log_eq] at hlog
    split at hlog
    · rename_i k' s1 hk
      simp only [pure_ok, Prod.mk.injEq] at hlog
      obtain ⟨-, rfl⟩ := hlog
      simp only [Prod.mk.injEq] at hk
      obtain ⟨-, rfl⟩ := hk
      rfl
    · simp at hlog
  have hfp2 : s2.fp = s.fp := f2.fp
  have hwf : s2.mem.WF := f2.good.wf
  refine ⟨p, base, Mem.read_ok hp, hgb.symm, hbl, fun hcase ↦ ?_⟩
  have hens : ∀ m : Mem, m ≤ ((m.ensure (s.fp + a)).ensure (base + o)).ensure (s2.fp + c) :=
    fun m ↦ Mem.le_trans (Mem.le_trans (Mem.le_ensure _ _) (Mem.le_ensure _ _)) (Mem.le_ensure _ _)
  rw [hfp2] at hm' ⊢
  rw [hmem] at hm' hwf
  cases mode with
  | cell =>
    simp only at hm'
    split_ifs at hm' with hw2 hw3
    · simp only [bind_ok, pure_ok] at hm'
      obtain ⟨m0, hm0, rfl⟩ := hm'
      exact ⟨written_mono (Mem.le_trans (put_le hwf hm0).1 (hens _)) hw2,
        fun _ ↦ written_mono (hens _) (put_written hwf hm0)⟩
    · simp only [bind_ok, pure_ok] at hm'
      obtain ⟨m0, hm0, rfl⟩ := hm'
      exact ⟨written_mono (hens _) (put_written hwf hm0),
        fun _ ↦ written_mono (Mem.le_trans (put_le hwf hm0).1 (hens _)) hw3⟩
    · rcases hcase with h | h | h
      · exact absurd rfl h
      · exact absurd h hw2
      · exact absurd h hw3
  | pc =>
    simp only [bind_ok, pure_ok] at hm'
    obtain ⟨m0, hm0, rfl⟩ := hm'
    exact ⟨written_mono (hens _) (put_written hwf hm0), fun h ↦ DerefMode.noConfusion h⟩
  | fp =>
    simp only [bind_ok, pure_ok] at hm'
    obtain ⟨m0, hm0, rfl⟩ := hm'
    exact ⟨written_mono (hens _) (put_written hwf hm0), fun h ↦ DerefMode.noConfusion h⟩

end

end LeanVM.Guest.Mode
