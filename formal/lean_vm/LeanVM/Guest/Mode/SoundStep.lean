module

public import LeanVM.Guest.Mode.Sem

/-!
# What an executor step writes, and the walk's state updated

The words an instruction leaves (`xor_vals`, `mul_vals`, `set_vals`, `deref_vals`,
`keccak_writes`), and each way the walk adds a fact, sound when the fact holds (`Holds.addW`, …).
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-! ## Adding facts -/

section add

variable {s : St} {A : Abs}

theorem Holds.addW (h : Holds s A) {o : ℕ} (hw : s.mem.written (s.fp + o) = true) :
    Holds s (A.addW o) :=
  { h with
    w := fun o' ho ↦ by
      rcases Exec.Trie.get_set (show (Exec.Trie.set () Exec.envDepth A.w o).get o' = some () from ho)
        with ⟨rfl, -⟩ | ho
      · exact hw
      · exact h.w o' ho }

theorem Holds.addNz (h : Holds s A) {o : ℕ} (hn : NzAt s o) : Holds s (A.addNz o) :=
  { h with
    nz := fun o' ho ↦ by
      rcases Exec.Trie.get_set (show (Exec.Trie.set () Exec.envDepth A.nz o).get o' = some () from ho)
        with ⟨rfl, -⟩ | ho
      · exact hn
      · exact h.nz o' ho }

theorem Holds.addV (h : Holds s A) {o : ℕ} {x : Val}
    (hv : ∃ u, s.mem.get (s.fp + o) = some u ∧ ValOk s x u) : Holds s (A.addV o x) := by
  unfold Abs.addV
  split
  · exact h
  · exact { h with
      v := fun o' x' ho ↦ by
        rcases Exec.Trie.get_set (show (Exec.Trie.set x Exec.envDepth A.v o).get o' = some x' from ho)
          with ⟨rfl, rfl⟩ | ho
        · exact hv
        · exact h.v o' x' ho }

theorem Holds.addLt (h : Holds s A) {a b : Idx} (hl : LTF s a b) : Holds s (A.addLt a b) :=
  { h with
    lt := fun p hp ↦ by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hl
      · exact h.lt p hp }

theorem Holds.setPr (h : Holds s A) {l : List (ℕ × ℕ × ℕ)} (hl : ∀ p ∈ l, PrF s p.1 p.2.1 p.2.2) :
    Holds s { A with pr := l } :=
  { h with pr := hl }

theorem Mono.ownCell_eq {k : Mono} {d : ℕ} (h : k.ownCell = some d) : k = .own d ∧ d < 2 ^ 62 := by
  obtain ⟨fp, kk, bs⟩ := k
  unfold Mono.ownCell at h
  split_ifs at h with hc
  cases h
  simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, decide_eq_true_eq] at hc
  obtain ⟨⟨rfl, rfl⟩, h2⟩ := hc
  exact ⟨rfl, h2⟩

theorem Holds.addH (h : Holds s A) {k : Mono} (hk : HW s k)
    (hown : ∀ d, k.ownCell = some d → s.mem.written (s.fp + d) = true) : Holds s (A.addH k) := by
  unfold Abs.addH
  split
  · rename_i d hd
    exact h.addW (hown d hd)
  · split
    · exact h
    · exact { h with
        h := fun k' hk' ↦ by
          rcases List.mem_cons.mp hk' with rfl | hk'
          · exact hk
          · exact h.h k' hk' }

theorem Holds.addHv (h : Holds s A) {k : Mono} {x : Val} (hk : HVF s k x)
    (hown : ∀ d, k.ownCell = some d → ∃ u, s.mem.get (s.fp + d) = some u ∧ ValOk s x u) :
    Holds s (A.addHv k x) := by
  unfold Abs.addHv
  split
  · rename_i d hd
    exact h.addV (hown d hd)
  · split
    · exact h
    · exact { h with
        hv := fun p hp ↦ by
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hk
          · exact h.hv p hp }

end add

/-! ## Reading the state -/

theorem Abs.hasW_get {A : Abs} {o : ℕ} (h : A.hasW o = true) : A.w.get o = some () := by
  unfold Abs.hasW at h
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h
  cases u; exact hu

theorem Abs.hasNz_get {A : Abs} {o : ℕ} (h : A.hasNz o = true) : A.nz.get o = some () := by
  unfold Abs.hasNz at h
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h
  cases u; exact hu

theorem Holds.written {s : St} {A : Abs} (h : Holds s A) {o : ℕ} (ho : A.hasW o = true) :
    s.mem.written (s.fp + o) = true :=
  h.w o (Abs.hasW_get ho)

theorem Holds.nzAt {s : St} {A : Abs} (h : Holds s A) {o : ℕ} (ho : A.hasNz o = true) : NzAt s o :=
  h.nz o (Abs.hasNz_get ho)

/-- A written frame cell's word, as the product the walk knows it as. -/
theorem Holds.mono_val {s : St} {A : Abs} (h : Holds s A) {o : ℕ} {m : Mono}
    (hm : A.mono o = some m) (hw : s.mem.written (s.fp + o) = true) :
    ∃ u, s.mem.get (s.fp + o) = some u ∧ MonoVal s m u := by
  unfold Abs.mono at hm
  split at hm
  · rename_i x hx
    cases hm
    exact h.v o _ hx
  · cases hm
  · cases hm
    obtain ⟨u, hu⟩ := Mem.get_of_written hw
    exact ⟨u, hu, MonoVal.root hu⟩

/-! ## What instructions write -/

theorem xor_vals {C : Ctx} {s s' : St} {a b c : ℕ} (hs : s.Good)
    (e : runOp C s (.xor a b c) = .ok s') :
    ∃ va vb, s.mem.get (s.fp + a) = some va ∧ s.mem.get (s.fp + b) = some vb ∧
      s'.mem.get (s.fp + c) = some (va + vb) := by
  simp only [runOp, bind_ok] at e
  obtain ⟨ca, hca, cb, hcb, cc, hcc, va, hva, vb, hvb, s1, hs1, e⟩ := e
  simp only [pure_ok] at e; subst e
  obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
  rw [bind_ok] at hm
  obtain ⟨m1, hm1, hm⟩ := hm
  simp only [pure_ok] at hm; subst hm
  obtain ⟨-, -, hput⟩ := Mem.put_ok hs.wf hm1
  obtain ⟨rfl, -⟩ := cellAt_ok hca
  obtain ⟨rfl, -⟩ := cellAt_ok hcb
  obtain ⟨rfl, -⟩ := cellAt_ok hcc
  exact ⟨va, vb, Mem.read_ok hva, Mem.read_ok hvb,
    (Mem.le_trans (Mem.le_ensure _ _) (Mem.le_ensure _ _)).get _ _ hput⟩

theorem mul_vals {C : Ctx} {s s' : St} {a b c : ℕ} (hs : s.Good)
    (e : runOp C s (.mul a b c) = .ok s') :
    ∃ va vb, s'.mem.get (s.fp + a) = some va ∧ s'.mem.get (s.fp + b) = some vb ∧
      s'.mem.get (s.fp + c) = some (va * vb) := by
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
  obtain ⟨m1, -, hwf0, va, vb, m2, hva, hvb, hm2, rfl⟩ := key
  obtain ⟨hle1, -, hput⟩ := Mem.put_ok hwf0 hm2
  have hle2 : m2 ≤ (m2.ensure ca).ensure cb := Mem.le_trans (Mem.le_ensure _ _) (Mem.le_ensure _ _)
  obtain ⟨rfl, -⟩ := cellAt_ok hca
  obtain ⟨rfl, -⟩ := cellAt_ok hcb
  obtain ⟨rfl, -⟩ := cellAt_ok hcc
  exact ⟨va, vb, (Mem.le_trans hle1 hle2).get _ _ (Mem.read_ok hva),
    (Mem.le_trans hle1 hle2).get _ _ (Mem.read_ok hvb), hle2.get _ _ hput⟩

theorem set_vals {C : Ctx} {s s' : St} {o : ℕ} {k : E} (hs : s.Good)
    (e : runOp C s (.set o k) = .ok s') : s'.mem.get (s.fp + o) = some k := by
  simp only [runOp, bind_ok] at e
  obtain ⟨ca, hca, s1, hs1, e⟩ := e
  simp only [pure_ok] at e; subst e
  obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
  obtain ⟨-, -, hput⟩ := Mem.put_ok hs.wf hm
  obtain ⟨rfl, -⟩ := cellAt_ok hca
  exact hput

/-- What a `DEREF` through frame cell `a` leaves: the pointer `p = g^base`, and the heap side
`base + o` and the frame side `fp + c` per its mode. -/
theorem deref_vals {C : Ctx} {s s' : St} {a o c : ℕ} {mode : DerefMode} (hs : s.Good)
    (e : runOp C s (.deref a o c mode) = .ok s') :
    ∃ p base, s.mem.get (s.fp + a) = some p ∧ p = ofK (g ^ base) ∧ base + o < maxCells ∧
      (mode = .pc → s'.mem.get (base + o) = some (ofK (g ^ (s.pc + 2)))) ∧
      (mode = .fp → s'.mem.get (base + o) = some (ofK (g ^ s.fp))) ∧
      (mode = .cell → (∀ v, s.mem.get (base + o) = some v → s'.mem.get (s.fp + c) = some v) ∧
        (∀ v, s.mem.get (s.fp + c) = some v → s'.mem.get (base + o) = some v)) := by
  simp only [runOp, bind_ok] at e
  obtain ⟨a1, ha1, p, hp, e⟩ := e
  split_ifs at e with hl1
  · simp [bind_ok] at e
  simp only [bind_ok] at e
  obtain ⟨⟨base, s2⟩, hlog, a2, ha2, a3, ha3, s3, hs3, e⟩ := e
  simp only [pure_ok] at e; subst e
  obtain ⟨f2, hgb, hbl⟩ := St.logOr_ok hs hlog
  obtain ⟨m', hm', rfl⟩ := St.withMem_ok hs3
  obtain ⟨rfl, -⟩ := cellAt_ok ha1
  obtain ⟨rfl, ha2l⟩ := cellAt_ok ha2
  obtain ⟨rfl, -⟩ := cellAt_ok ha3
  have hmem : s2.mem = s.mem ∧ s2.pc = s.pc := by
    unfold St.logOr at hlog; rw [St.log_eq] at hlog
    split at hlog
    · rename_i k' s1 hk
      simp only [pure_ok, Prod.mk.injEq] at hlog
      obtain ⟨-, rfl⟩ := hlog
      simp only [Prod.mk.injEq] at hk
      obtain ⟨-, rfl⟩ := hk
      exact ⟨rfl, rfl⟩
    · simp at hlog
  have hfp2 : s2.fp = s.fp := f2.fp
  have hwf : s2.mem.WF := f2.good.wf
  have hp' : p = ofK (g ^ base) := by
    refine E.ext fun i ↦ ?_
    fin_cases i
    · simp [hgb]
    · simpa using not_not.mp hl1
  refine ⟨p, base, Mem.read_ok hp, hp', ha2l, ?_⟩
  have hens : ∀ m : Mem, m ≤ ((m.ensure (s.fp + a)).ensure (base + o)).ensure (s2.fp + c) :=
    fun m ↦ Mem.le_trans (Mem.le_trans (Mem.le_ensure _ _) (Mem.le_ensure _ _)) (Mem.le_ensure _ _)
  rw [hfp2] at hm' ⊢
  rw [hmem.1] at hm' hwf
  rw [hmem.2] at hm'
  cases mode with
  | cell =>
    refine ⟨nofun, nofun, fun _ ↦ ?_⟩
    simp only at hm'
    split_ifs at hm' with hw2 hw3
    · simp only [bind_ok, pure_ok] at hm'
      obtain ⟨m0, hm0, rfl⟩ := hm'
      obtain ⟨hle0, -, hput⟩ := Mem.put_ok hwf hm0
      obtain ⟨v2, hv2⟩ := Mem.get_of_written hw2
      refine ⟨fun v hv ↦ ?_, fun v hv ↦ ?_⟩
      · rw [hv2] at hv; cases hv
        rw [Mem.peek_of_get hv2] at hput
        exact (hens _).get _ _ hput
      · have h1 := (hens _).get _ _ hput
        rw [hle0.get _ _ hv] at hput
        rw [Mem.peek_of_get hv2] at hput
        cases hput
        exact (Mem.le_trans hle0 (hens _)).get _ _ hv2
    · simp only [bind_ok, pure_ok] at hm'
      obtain ⟨m0, hm0, rfl⟩ := hm'
      obtain ⟨hle0, -, hput⟩ := Mem.put_ok hwf hm0
      obtain ⟨v3, hv3⟩ := Mem.get_of_written hw3
      refine ⟨fun v hv ↦ absurd (written_of_get hv) hw2, fun v hv ↦ ?_⟩
      rw [hv3] at hv; cases hv
      rw [Mem.peek_of_get hv3] at hput
      exact (hens _).get _ _ hput
    · refine ⟨fun v hv ↦ absurd (written_of_get hv) hw2, fun v hv ↦ absurd (written_of_get hv) hw3⟩
  | pc =>
    refine ⟨fun _ ↦ ?_, nofun, nofun⟩
    simp only [bind_ok, pure_ok] at hm'
    obtain ⟨m0, hm0, rfl⟩ := hm'
    exact (hens _).get _ _ (Mem.put_ok hwf hm0).2.2
  | fp =>
    refine ⟨nofun, fun _ ↦ ?_, nofun⟩
    simp only [bind_ok, pure_ok] at hm'
    obtain ⟨m0, hm0, rfl⟩ := hm'
    exact (hens _).get _ _ (Mem.put_ok hwf hm0).2.2

theorem keccak_writes {C : Ctx} {s s' : St} {ins : Array ℕ} {out : ℕ} {inOdd outOdd : Bool} {n : ℕ}
    (hs : s.Good) (e : runOp C s (.keccak ins out inOdd outOdd n) = .ok s') :
    s.mem ≤ s'.mem ∧ s'.fp = s.fp ∧ s'.pc = s.pc + 1 ∧
      ∀ j < n, s'.mem.written (s.fp + (out + j)) = true := by
  simp only [runOp, bind_ok] at e
  obtain ⟨cells, hcells, input, -, outs, houts, s1, hs1, e⟩ := e
  simp only [pure_ok] at e; subst e
  obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
  rw [bind_ok] at hm
  obtain ⟨m1, hm1, hm⟩ := hm
  simp only [pure_ok] at hm; subst hm
  have hfold := Mem.foldlM_ok _ (fun (x : ℕ × ℕ) (m : Mem) ↦ m.written x.1 = true)
    (fun (x : ℕ × ℕ) (m m' : Mem) (h : m.written x.1 = true) (hle : m ≤ m') ↦ written_mono hle h)
    (fun m x m' hm e ↦ by
      obtain ⟨h1, h2, h3⟩ := Mem.put_ok hm e
      exact ⟨h1, h2, written_of_get h3⟩) _ _ _ hs.wf hm1
  have hens : ∀ (l : List ℕ) (m : Mem), m ≤ l.foldl Mem.ensure m := by
    intro l
    induction l with
    | nil => exact fun m ↦ Mem.le_refl m
    | cons x l ih => exact fun m ↦ Mem.le_trans (Mem.le_ensure _ _) (ih _)
  have hf := exMapM_ok _ _ _ houts
  refine ⟨Mem.le_trans hfold.1 (hens _ _), rfl, rfl, fun j hj ↦ ?_⟩
  have hlen : outs.length = n := by rw [← hf.length_eq, List.length_range]
  have h1 := forall₂_getElem hf (i := j) (by simp; omega) (by omega)
  simp only [List.getElem_range] at h1
  rw [← (cellAt_ok h1).1]
  refine written_mono (hens _ _) (hfold.2.2 (outs[j]'(by omega), j) ?_)
  exact List.mem_iff_getElem.mpr ⟨j, by simp; omega, by simp⟩

end

end LeanVM.Guest.Mode
