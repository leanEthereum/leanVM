module

public import LeanVM.Prover.ExecuteSound
public import LeanVM.Prover.ExecuteCompleteOp

/-!
# The mode walk on a straight run (prototype)

What a function's walk knows at an instruction (`Abs`): the frame offsets written (`w`), and the
cells `b + o` written, for `(a, o)` in `h`, `g^b` being the word of the written frame cell `a`
(a heap pointer, or a callee's frame pointer). `stepA` is one instruction: the cells it reads must
be known written, and what it surely writes joins. A `DEREF` of mode `cell` writes both its sides
when either was written before, and links them otherwise, learning nothing; of mode `pc` or `fp`, it
writes its target.

`Holds s A`: the state's memory has what `A` says, relative to its frame. Writes are never undone,
so `Holds` survives every step that keeps the frame (`Holds.mono`). `stepA_sound`: from a state
where `A` holds, an instruction that `stepA` accepts finds its reads written (`Reads`, the
`written` conjuncts of `OpModed`), and, if it is not a `JUMP`, leaves a state at the next `pc`, in
the same frame, where the walk's next set holds. `walk_step` is the same along a straight run of
instructions placed from a `pc`, in the shape `InvRule` consumes.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Prover.Exec

@[expose] public section

/-- What the walk knows at an instruction. -/
structure Abs where
  /-- Frame offsets written. -/
  w : List ℕ
  /-- `(a, o)`: frame cell `a` is written, with word `g^b`, and so is cell `b + o`. -/
  h : List (ℕ × ℕ)

/-- One instruction of the walk. -/
def stepA (A : Abs) : Op → Option Abs
  | .xor a b c => if A.w.contains a && A.w.contains b then some ⟨c :: A.w, A.h⟩ else none
  | .mul a b c => if A.w.contains a && A.w.contains b then some ⟨c :: A.w, A.h⟩ else none
  | .set o _ => some ⟨o :: A.w, A.h⟩
  | .deref a o c .cell =>
    if A.w.contains a then
      if A.w.contains c || A.h.contains (a, o) then some ⟨c :: A.w, (a, o) :: A.h⟩ else some A
    else none
  | .deref a o _ _ => if A.w.contains a then some ⟨A.w, (a, o) :: A.h⟩ else none
  | .jump c d f => if A.w.contains c && A.w.contains d && A.w.contains f then some A else none
  | .keccak .. => none

/-- The walk along a straight run. -/
def walkA (A : Abs) (ops : List Op) : Option Abs := ops.foldlM stepA A

/-- The walk's set before instruction `k` of the run. -/
def walkAt (A : Abs) (ops : List Op) (k : ℕ) : Option Abs := walkA A (ops.take k)

/-- The frame offsets `w` are written. -/
def Wr (s : St) (w : List ℕ) : Prop := ∀ o ∈ w, s.mem.written (s.fp + o) = true

/-- For each `(a, o)` of `h`, frame cell `a` holds some `v`, and if `v` names cell `b`, then cell
`b + o` is written. -/
def HeapW (s : St) (h : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ h, ∃ v, s.mem.get (s.fp + p.1) = some v ∧
    ∀ b, v.limb 0 = g ^ b → b < maxCells → s.mem.written (b + p.2) = true

/-- The state's memory has what the walk knows. -/
def Holds (s : St) (A : Abs) : Prop := Wr s A.w ∧ HeapW s A.h

/-- The cells an instruction reads, written: the `written` conjuncts of `OpModed` (a `MUL`'s
forward case). -/
def Reads (s : St) : Op → Prop
  | .xor a b _ => s.mem.written (s.fp + a) = true ∧ s.mem.written (s.fp + b) = true
  | .mul a b _ => s.mem.written (s.fp + a) = true ∧ s.mem.written (s.fp + b) = true
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

/-- The reads written and the reference's part give `OpModed`, for every instruction but a
back-solved `MUL`. -/
theorem opModed_of {M : ℕ → E} {s : St} {op : Op} (h1 : Reads s op) (h2 : RefOk M s op) :
    OpModed M s op := by
  cases op with
  | xor => exact h1
  | mul => exact Or.inl h1
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

theorem Holds.mono {s s' : St} {A : Abs} (hA : Holds s A) (hle : s.mem ≤ s'.mem)
    (hfp : s'.fp = s.fp) : Holds s' A := by
  refine ⟨fun o ho ↦ hfp ▸ written_mono hle (hA.1 o ho), fun p hp ↦ ?_⟩
  obtain ⟨v, hv, hb⟩ := hA.2 p hp
  exact ⟨v, hfp ▸ hle.get _ _ hv, fun b h1 h2 ↦ written_mono hle (hb b h1 h2)⟩

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

/-! ## The walk is sound -/

theorem contains_mem {l : List ℕ} {a : ℕ} (h : l.contains a = true) : a ∈ l := by
  simpa using h

theorem contains_mem₂ {l : List (ℕ × ℕ)} {a : ℕ × ℕ} (h : l.contains a = true) : a ∈ l := by
  simpa using h

/-- **One step of the walk is sound.** -/
theorem stepA_sound {C : Ctx} {s : St} {A A' : Abs} {op : Op} (hs : s.Good) (hfp : s.fp < maxCells)
    (hpc : s.pc < C.ops.size) (hA : Holds s A) (h : stepA A op = some A') :
    Reads s op ∧ ((∀ c d f, op ≠ .jump c d f) → ∀ s', runOp C s op = .ok s' →
      s'.pc = s.pc + 1 ∧ s'.fp = s.fp ∧ Holds s' A') := by
  have hW := hA.1
  cases op with
  | xor a b c =>
    simp only [stepA, Bool.and_eq_true] at h
    split_ifs at h with hc
    cases h
    refine ⟨⟨hW a (contains_mem hc.1), hW b (contains_mem hc.2)⟩, fun hj s' e ↦ ?_⟩
    obtain ⟨h1, h2, h3⟩ := runOp_next hs hfp hpc e hj (fun _ _ _ _ _ ↦ nofun)
    have hm := hA.mono h3 h2
    refine ⟨h1, h2, fun o ho ↦ ?_, hm.2⟩
    rcases List.mem_cons.mp ho with rfl | ho
    · rw [h2]; exact runOp_writes (k := 0) hs (Or.inl rfl) e
    · exact hm.1 o ho
  | mul a b c =>
    simp only [stepA, Bool.and_eq_true] at h
    split_ifs at h with hc
    cases h
    refine ⟨⟨hW a (contains_mem hc.1), hW b (contains_mem hc.2)⟩, fun hj s' e ↦ ?_⟩
    obtain ⟨h1, h2, h3⟩ := runOp_next hs hfp hpc e hj (fun _ _ _ _ _ ↦ nofun)
    have hm := hA.mono h3 h2
    refine ⟨h1, h2, fun o ho ↦ ?_, hm.2⟩
    rcases List.mem_cons.mp ho with rfl | ho
    · rw [h2]; exact runOp_writes (k := 0) hs (Or.inr (Or.inl rfl)) e
    · exact hm.1 o ho
  | set o k =>
    simp only [stepA, Option.some.injEq] at h
    subst h
    refine ⟨trivial, fun hj s' e ↦ ?_⟩
    obtain ⟨h1, h2, h3⟩ := runOp_next hs hfp hpc e hj (fun _ _ _ _ _ ↦ nofun)
    have hm := hA.mono h3 h2
    refine ⟨h1, h2, fun o' ho ↦ ?_, hm.2⟩
    rcases List.mem_cons.mp ho with rfl | ho
    · rw [h2]; exact runOp_writes (a := 0) (b := 0) hs (Or.inr (Or.inr rfl)) e
    · exact hm.1 o' ho
  | deref a o c mode =>
    -- the new fact `(a, o)`, from `base + o` written after the step
    have fact : ∀ s', s'.fp = s.fp → s.mem ≤ s'.mem → ∀ v base, s.mem.get (s.fp + a) = some v →
        v.limb 0 = g ^ base → base < maxCells → s'.mem.written (base + o) = true →
        HeapW s' [(a, o)] := by
      intro s' hfp' hle v base hv hb hbl hw p hp
      rcases List.mem_singleton.mp hp with rfl
      refine ⟨v, hfp' ▸ hle.get _ _ hv, fun b' hb' hlt ↦ ?_⟩
      have : b' = base := gpow_inj (by unfold maxCells at hlt; omega)
        (by unfold maxCells at hbl; omega) (hb'.symm.trans hb)
      subst this; exact hw
    have hcons : ∀ s' (B : Abs) (p : ℕ × ℕ), HeapW s' B.h → HeapW s' [p] → HeapW s' (p :: B.h) :=
      fun s' B p h1 h2 q hq ↦ by
        rcases List.mem_cons.mp hq with rfl | hq
        · exact h2 q (List.mem_singleton_self _)
        · exact h1 q hq
    cases mode with
    | cell =>
      simp only [stepA] at h
      split_ifs at h with ha hc
      · cases h
        refine ⟨hW a (contains_mem ha), fun hj s' e ↦ ?_⟩
        obtain ⟨h1, h2, h3⟩ := runOp_next hs hfp hpc e hj (fun _ _ _ _ _ ↦ nofun)
        have hm := hA.mono h3 h2
        obtain ⟨v, base, hv, hb, hbl, hwr⟩ := deref_writes hs e
        have hside : s.mem.written (base + o) = true ∨ s.mem.written (s.fp + c) = true := by
          rcases Bool.or_eq_true_iff.mp hc with hc | hc
          · exact Or.inr (hW c (contains_mem hc))
          · obtain ⟨v', hv', hb'⟩ := hA.2 _ (contains_mem₂ hc)
            rw [hv] at hv'; cases hv'
            exact Or.inl (hb' base hb hbl)
        obtain ⟨hw2, hw3⟩ := hwr (Or.inr hside)
        refine ⟨h1, h2, fun o' ho ↦ ?_, hcons s' A _ hm.2 (fact s' h2 h3 v base hv hb hbl hw2)⟩
        rcases List.mem_cons.mp ho with rfl | ho
        · rw [h2]; exact hw3 rfl
        · exact hm.1 o' ho
      · cases h
        refine ⟨hW a (contains_mem ha), fun hj s' e ↦ ?_⟩
        obtain ⟨h1, h2, h3⟩ := runOp_next hs hfp hpc e hj (fun _ _ _ _ _ ↦ nofun)
        exact ⟨h1, h2, hA.mono h3 h2⟩
    | pc | fp =>
      simp only [stepA] at h
      split_ifs at h with ha
      cases h
      refine ⟨hW a (contains_mem ha), fun hj s' e ↦ ?_⟩
      obtain ⟨h1, h2, h3⟩ := runOp_next hs hfp hpc e hj (fun _ _ _ _ _ ↦ nofun)
      have hm := hA.mono h3 h2
      obtain ⟨v, base, hv, hb, hbl, hwr⟩ := deref_writes hs e
      obtain ⟨hw2, -⟩ := hwr (Or.inl (fun h ↦ DerefMode.noConfusion h))
      exact ⟨h1, h2, hm.1, hcons s' A _ hm.2 (fact s' h2 h3 v base hv hb hbl hw2)⟩
  | jump c d f =>
    simp only [stepA, Bool.and_eq_true] at h
    split_ifs at h with hc
    exact ⟨⟨hW c (contains_mem hc.1.1), hW d (contains_mem hc.1.2), hW f (contains_mem hc.2)⟩,
      fun hj ↦ absurd rfl (hj c d f)⟩
  | keccak => simp [stepA] at h

/-! ## Along a straight run -/

theorem walkAt_succ {A : Abs} {ops : List Op} {k : ℕ} (hk : k < ops.length) :
    walkAt A ops (k + 1) = (walkAt A ops k).bind (stepA · ops[k]) := by
  unfold walkAt walkA
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldlM_append]
  cases (ops.take k).foldlM stepA A <;> simp

/-- **The walk's step rule**: the instructions `ops` placed from `pc` `e`, the walk accepting them
from `A`; at a state at instruction `k` of the run where the walk's set holds, the instruction
reads written cells, and, if it is not a `JUMP`, steps to instruction `k + 1`, in the same frame,
where the walk's next set holds. -/
theorem walk_step {C : Ctx} {e : ℕ} {ops : List Op} {A : Abs}
    (hcode : ∀ k (hk : k < ops.length), C.ops[e + k]? = some ops[k])
    (hok : (walkA A ops).isSome = true) {s : St} {k : ℕ} {B : Abs} (hk : k < ops.length)
    (hpc : s.pc = e + k) (hB : walkAt A ops k = some B) (hs : s.Good) (hfp : s.fp < maxCells)
    (hH : Holds s B) :
    C.ops[s.pc]? = some ops[k] ∧ Reads s ops[k] ∧ ((∀ c d f, ops[k] ≠ .jump c d f) →
      ∀ s', runOp C s ops[k] = .ok s' → s'.pc = e + (k + 1) ∧ s'.fp = s.fp ∧
        ∃ B', walkAt A ops (k + 1) = some B' ∧ Holds s' B') := by
  have hop : C.ops[s.pc]? = some ops[k] := hpc ▸ hcode k hk
  have hlt : s.pc < C.ops.size := by
    obtain ⟨h, -⟩ := Array.getElem?_eq_some_iff.mp hop; exact h
  -- the walk accepts instruction `k` from `B`, since it accepts the whole run
  have hstep : ∃ B', stepA B ops[k] = some B' := by
    have hall : ∀ j ≤ ops.length, (walkAt A ops j).isSome = true := by
      intro j hj
      have : walkA A ops = walkA A (ops.take j ++ ops.drop j) := by rw [List.take_append_drop]
      unfold walkAt
      unfold walkA at this hok
      rw [this, List.foldlM_append] at hok
      cases h : (ops.take j).foldlM stepA A with
      | none => rw [h] at hok; simp at hok
      | some _ => simp [walkA, h]
    have h1 := hall (k + 1) hk
    rw [walkAt_succ hk, hB] at h1
    simp only [Option.bind_some] at h1
    exact Option.isSome_iff_exists.mp h1
  obtain ⟨B', hB'⟩ := hstep
  obtain ⟨hr, hn⟩ := stepA_sound hs hfp hlt hH hB'
  refine ⟨hop, hr, fun hj s' e' ↦ ?_⟩
  obtain ⟨h1, h2, h3⟩ := hn hj s' e'
  exact ⟨by rw [h1, hpc]; omega, h2, B', by rw [walkAt_succ hk, hB, Option.bind_some, hB'], h3⟩

end

end LeanVM.Guest.Mode
