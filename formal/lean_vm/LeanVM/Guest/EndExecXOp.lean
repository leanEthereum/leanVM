/-
  LeanVM.Guest.EndExecXOp

  An executor instruction along the reference: what it reads is written, and every cell it touches
  is one the reference step reads.
-/

module

public import LeanVM.Guest.Mode.Frame
public import LeanVM.Prover.ExecuteComplete

/-!
# An executor instruction along the reference

`reads_of_runOp`: an instruction the executor completes found the cells it reads written (`Reads`:
for a `MUL` solved backwards, its known operand nonzero). `runOp_used`: on a state agreeing with
the reference memory of a memory image of at most `2^28` words, an instruction the reference step
executes from the state's registers touches only cells it reads, so it keeps the cells used within
the image (`put_used`, `link_used`: what a write or a link adds to `used`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode
open LeanVM.Prover.Exec

@[expose] public section

/-! ## The cells used -/

theorem setCell_used (m : Mem) (c : ℕ) (x : Cell) : (m.setCell c x).used = m.used := by
  obtain ⟨cells, vals, members, links, used⟩ := m
  rfl

theorem put_used {m m' : Mem} {c : ℕ} {v : E} (e : m.put c v = .ok m') : m'.used = max m.used (c + 1) := by
  have hu : (m.ensure c).used = max m.used (c + 1) := rfl
  simp only [Mem.put] at e
  generalize m.ensure c = m1 at e hu
  obtain ⟨cells, vals, members, links, used⟩ := m1
  simp only at e hu
  rw [← hu]
  split at e
  · split_ifs at e
    simp only [pure_ok] at e; subst e; rfl
  · split at e
    · split_ifs at e
      simp only [pure_ok] at e; subst e; rfl
    · simp only [pure_ok] at e; subst e; rfl
  · simp only [pure_ok] at e; subst e; exact setCell_used _ _ _

theorem merge_used (m : Mem) (i j : ℕ) : (m.merge i j).used = m.used := by
  obtain ⟨cells, vals, members, links, used⟩ := m
  rfl

theorem join_used (m : Mem) (c i : ℕ) : (m.join c i).used = m.used := by
  obtain ⟨cells, vals, members, links, used⟩ := m
  rfl

theorem link_used (m : Mem) (a b : ℕ) : (m.link a b).used = max m.used (max a b + 1) := by
  obtain ⟨cells, vals, members, links, used⟩ := m
  unfold Mem.link
  dsimp only
  split
  · split_ifs
    · rfl
    · exact merge_used _ _ _
    · exact merge_used _ _ _
  · exact join_used _ _ _
  · exact join_used _ _ _
  · rw [join_used, join_used]

theorem foldl_ensure_used {B : ℕ} : ∀ (l : List ℕ) (m : Mem), m.used ≤ B → (∀ c ∈ l, c < B) →
    (l.foldl Mem.ensure m).used ≤ B
  | [], _, h, _ => h
  | c :: l, m, h, hl => foldl_ensure_used l _ (by
      have := hl c List.mem_cons_self
      simp only [Mem.ensure_used]; omega) fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)

theorem foldlM_put_used {B : ℕ} (f : ℕ × ℕ → E) :
    ∀ (l : List (ℕ × ℕ)) (m m' : Mem), l.foldlM (fun m x ↦ m.put x.1 (f x)) m = .ok m' → m.used ≤ B →
      (∀ x ∈ l, x.1 < B) → m'.used ≤ B
  | [], m, m', e, h, _ => by simp only [List.foldlM_nil, pure_ok] at e; subst e; exact h
  | x :: l, m, m', e, h, hl => by
    rw [List.foldlM_cons, bind_ok] at e
    obtain ⟨m1, e1, e⟩ := e
    refine foldlM_put_used f l m1 m' e ?_ fun y hy ↦ hl y (List.mem_cons_of_mem _ hy)
    rw [put_used e1]
    have := hl x List.mem_cons_self
    omega

/-! ## What an instruction reads -/

/-- **An instruction the executor completes found its reads written.** -/
theorem reads_of_runOp {C : Ctx} {s s' : St} {op : Op} (e : runOp C s op = .ok s') : Reads s op := by
  cases op with
  | xor a b c =>
    simp only [runOp, bind_ok] at e
    obtain ⟨ca, hca, cb, hcb, cc, hcc, va, hva, vb, hvb, -⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok hca
    obtain ⟨rfl, -⟩ := cellAt_ok hcb
    exact ⟨written_of_get (Mem.read_ok hva), written_of_get (Mem.read_ok hvb)⟩
  | mul a b c =>
    simp only [runOp, bind_ok] at e
    obtain ⟨ca, hca, cb, hcb, cc, hcc, s1, hs1, -⟩ := e
    obtain ⟨m, hm, -⟩ := St.withMem_ok hs1
    obtain ⟨rfl, -⟩ := cellAt_ok hca
    obtain ⟨rfl, -⟩ := cellAt_ok hcb
    obtain ⟨rfl, -⟩ := cellAt_ok hcc
    have hnz : ∀ o, s.mem.written (s.fp + o) = true → s.mem.peek (s.fp + o) ≠ 0 → NzAt s o := fun o hw hne ↦ by
      obtain ⟨u, hu⟩ := Mem.get_of_written hw
      exact ⟨u, hu, by rw [Mem.peek_of_get hu] at hne; exact hne⟩
    by_cases hwa : s.mem.written (s.fp + a) = true <;> by_cases hwb : s.mem.written (s.fp + b) = true
    · exact Or.inl ⟨hwa, hwb⟩
    · by_cases hwc : s.mem.written (s.fp + c) = true
      · by_cases h0 : s.mem.peek (s.fp + a) = 0
        · simp [hwa, hwb, hwc, h0, bind_ok] at hm
        · exact Or.inr (Or.inl ⟨hwc, hwa, hnz _ hwa h0⟩)
      · simp only [hwc, Bool.false_and, Bool.false_eq_true, ↓reduceIte, bind_ok, pure_ok] at hm
        obtain ⟨m1, rfl, va, hva, vb, hvb, -⟩ := hm
        exact absurd (written_of_get (Mem.read_ok hvb)) hwb
    · by_cases hwc : s.mem.written (s.fp + c) = true
      · by_cases h0 : s.mem.peek (s.fp + b) = 0
        · simp [hwa, hwb, hwc, h0, bind_ok] at hm
        · exact Or.inr (Or.inr ⟨hwc, hwb, hnz _ hwb h0⟩)
      · simp only [hwc, Bool.false_and, Bool.false_eq_true, ↓reduceIte, bind_ok, pure_ok] at hm
        obtain ⟨m1, rfl, va, hva, -⟩ := hm
        exact absurd (written_of_get (Mem.read_ok hva)) hwa
    · simp only [hwa, hwb, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte, bind_ok,
        pure_ok] at hm
      obtain ⟨m1, rfl, va, hva, -⟩ := hm
      exact absurd (written_of_get (Mem.read_ok hva)) hwa
  | set => trivial
  | deref a o c mode =>
    simp only [runOp, bind_ok] at e
    obtain ⟨a1, ha1, p, hp, -⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok ha1
    exact written_of_get (Mem.read_ok hp)
  | jump c d f =>
    simp only [runOp, bind_ok] at e
    obtain ⟨ac, hac, ad, had, af, haf, vc', hvc', vc, -, vd', hvd', vd, -, vf', hvf', -⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok hac
    obtain ⟨rfl, -⟩ := cellAt_ok had
    obtain ⟨rfl, -⟩ := cellAt_ok haf
    exact ⟨written_of_get (Mem.read_ok hvc'), written_of_get (Mem.read_ok hvd'),
      written_of_get (Mem.read_ok hvf')⟩
  | keccak ins out inOdd outOdd count =>
    simp only [runOp, bind_ok] at e
    obtain ⟨cells, hcells, input, hinput, -⟩ := e
    have hc := exMapM_ok _ _ _ hcells
    have hi := exMapM_ok _ _ _ hinput
    intro i hi'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hi'
    have h1 := forall₂_getElem hc (i := j) hj (by rw [← hc.length_eq]; exact hj)
    have h2 := forall₂_getElem hi (i := j) (by rw [← hc.length_eq]; exact hj)
      (by rw [← hi.length_eq, ← hc.length_eq]; exact hj)
    obtain ⟨h3, -⟩ := cellAt_ok h1
    rw [h3] at h2
    exact written_of_get (Mem.read_ok h2)

/-! ## The cells an instruction touches -/

theorem foldlM_used {α : Type} {B : ℕ} (f : Mem → α → Except Fault Mem) (P : α → Prop)
    (hf : ∀ m x m', P x → f m x = .ok m' → m.used ≤ B → m'.used ≤ B) :
    ∀ (l : List α) (m m' : Mem), l.foldlM f m = .ok m' → m.used ≤ B → (∀ x ∈ l, P x) → m'.used ≤ B
  | [], m, m', e, h, _ => by simp only [List.foldlM_nil, pure_ok] at e; subst e; exact h
  | x :: l, m, m', e, h, hl => by
    rw [List.foldlM_cons, bind_ok] at e
    obtain ⟨m1, e1, e⟩ := e
    exact foldlM_used f P hf l m1 m' e (hf m x m1 (hl x List.mem_cons_self) e1 h)
      fun y hy ↦ hl y (List.mem_cons_of_mem _ hy)

theorem logOr_mem {s s' : St} {x : K} {b k : ℕ} {f : Fault} (h : s.logOr x b f = .ok (k, s')) :
    s'.mem = s.mem := by
  unfold St.logOr at h
  rw [St.log_eq] at h
  split at h
  · rename_i k' s1 hk
    simp only [pure_ok, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp only [Prod.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk
    rfl
  · simp at h

/-- A cell the reference reads, below `2^62`, is a word of its image. -/
theorem lt_of_read {κ : ℕ} (hκ : κ ≤ 28) {img : MemoryImage κ} {c : ℕ} {v : E} (hc : c < 2 ^ 62)
    (h : img.read (g ^ c) = some v) : c < 2 ^ κ := by
  obtain ⟨i, hi, -⟩ := (MemoryImage.read_eq_some_iff (by omega) img).mp h
  have hi' : (i : ℕ) < 2 ^ 28 := lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hκ)
  have := gpow_inj (by omega) (by omega) hi
  have := i.isLt
  omega

/-- **An instruction touches only cells the reference step reads**: on a state agreeing with the
reference memory, one the reference step executes keeps the cells used within its image. -/
theorem runOp_used {C : Ctx} {s s' : St} {op : Op} {ins : LeanIsaInstruction} {κ : ℕ}
    {img : MemoryImage κ} {r' : Registers K} (hκ : κ ≤ 28) (hs : Fine (refMem img) s) (hop : OpOf ins op)
    (e : runOp C s op = .ok s') (hex : executeWith img.read ⟨g ^ s.pc, g ^ s.fp⟩ ins = some r')
    (hu : s.mem.used ≤ 2 ^ κ) : s'.mem.used ≤ 2 ^ κ := by
  have hr : ∀ c v, c < maxCells → img.read (g ^ c) = some v → c < 2 ^ κ := fun c v hc h ↦
    lt_of_read hκ (by unfold maxCells at hc; omega) h
  have hgood : s.Good := ⟨hs.agree.wf, hs.dl⟩
  cases op with
  | xor =>
    cases ins <;> simp only [OpOf] at hop
    obtain ⟨rfl, rfl, rfl⟩ := hop
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff, ← pow_add] at hex
    obtain ⟨_, ha, _, hb, _, hc, -⟩ := hex
    simp only [runOp, bind_ok] at e
    obtain ⟨ca, hca, cb, hcb, cc, hcc, va, -, vb, -, s1, hs1, e⟩ := e
    simp only [pure_ok] at e; subst e
    obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
    rw [bind_ok] at hm
    obtain ⟨m1, hm1, hm⟩ := hm
    simp only [pure_ok] at hm; subst hm
    obtain ⟨rfl, ha'⟩ := cellAt_ok hca
    obtain ⟨rfl, hb'⟩ := cellAt_ok hcb
    obtain ⟨rfl, hc'⟩ := cellAt_ok hcc
    have := hr _ _ ha' ha
    have := hr _ _ hb' hb
    have := hr _ _ hc' hc
    simp only [Mem.ensure_used, put_used hm1]
    omega
  | mul =>
    cases ins <;> simp only [OpOf] at hop
    obtain ⟨rfl, rfl, rfl⟩ := hop
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff, ← pow_add] at hex
    obtain ⟨_, ha, _, hb, _, hc, -⟩ := hex
    simp only [runOp, bind_ok] at e
    obtain ⟨ca, hca, cb, hcb, cc, hcc, s1, hs1, e⟩ := e
    simp only [pure_ok] at e; subst e
    obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
    have key : ∃ (m1 m2 : Mem) (x : E), m1.used ≤ max s.mem.used (max (ca + 1) (cb + 1)) ∧
        m1.put cc x = .ok m2 ∧
        m = (m2.ensure ca).ensure cb := by
      split_ifs at hm <;> simp only [bind_ok, pure_ok, throw_ok, false_and, exists_false] at hm
      all_goals first
        | (obtain ⟨m1, rfl, va, -, vb, -, m2, hm2, rfl⟩ := hm
           exact ⟨_, m2, _, by omega, hm2, rfl⟩)
        | (obtain ⟨m1, hm1, va, -, vb, -, m2, hm2, rfl⟩ := hm
           exact ⟨m1, m2, _, by rw [put_used hm1]; omega, hm2, rfl⟩)
    obtain ⟨m1, m2, x, hm1, hm2, rfl⟩ := key
    obtain ⟨rfl, ha'⟩ := cellAt_ok hca
    obtain ⟨rfl, hb'⟩ := cellAt_ok hcb
    obtain ⟨rfl, hc'⟩ := cellAt_ok hcc
    have := hr _ _ ha' ha
    have := hr _ _ hb' hb
    have := hr _ _ hc' hc
    simp only [Mem.ensure_used, put_used hm2]
    omega
  | set =>
    cases ins <;> simp only [OpOf] at hop
    obtain ⟨rfl, rfl⟩ := hop
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff, ← pow_add] at hex
    obtain ⟨_, ha, -⟩ := hex
    simp only [runOp, bind_ok] at e
    obtain ⟨ca, hca, s1, hs1, e⟩ := e
    simp only [pure_ok] at e; subst e
    obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
    obtain ⟨rfl, ha'⟩ := cellAt_ok hca
    have := hr _ _ ha' ha
    simp only [put_used hm]
    omega
  | deref o1 o2 o3 mode =>
    cases ins <;> simp only [OpOf] at hop
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hop
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hex
    obtain ⟨p, hp, -, -, v3, h3, v2, h2, -⟩ := hex
    simp only [runOp, bind_ok] at e
    obtain ⟨a1, ha1, p', hp', e⟩ := e
    split_ifs at e with hl1
    · simp [bind_ok] at e
    simp only [bind_ok] at e
    obtain ⟨⟨base, s2⟩, hlog, a2, ha2, a3, ha3, s3, hs3, e⟩ := e
    simp only [pure_ok] at e; subst e
    obtain ⟨f2, hgb, -⟩ := St.logOr_ok hgood hlog
    have hmem := logOr_mem hlog
    obtain ⟨m', hm', rfl⟩ := St.withMem_ok hs3
    obtain ⟨rfl, ha1'⟩ := cellAt_ok ha1
    obtain ⟨rfl, ha2'⟩ := cellAt_ok ha2
    obtain ⟨rfl, ha3'⟩ := cellAt_ok ha3
    rw [← pow_add] at hp h3
    have hpp : p' = p := by
      rw [← hs.agree.get _ _ (Mem.read_ok hp')]
      exact ((refRd_img hκ img) _ _ (by unfold maxCells at ha1'; omega) hp).2
    rw [hpp] at hgb
    rw [← hgb, ← pow_add] at h2
    have h1 := hr _ _ ha1' hp
    have h2' := hr _ _ ha2' h2
    have h3' := hr _ _ (f2.fp ▸ ha3') h3
    have hfin : ∀ m0 : Mem, m0.used ≤ max s.mem.used (max (base + o2 + 1) (s.fp + o3 + 1)) →
        (((m0.ensure (s.fp + o1)).ensure (base + o2)).ensure (s.fp + o3)).used ≤ 2 ^ κ := fun m0 h0 ↦ by
      simp only [Mem.ensure_used]; omega
    simp only at hm'
    rw [hmem, f2.fp] at hm'
    cases mode with
    | cell =>
      simp only at hm'
      split_ifs at hm'
      · simp only [bind_ok, pure_ok] at hm'
        obtain ⟨m0, hm0, rfl⟩ := hm'
        exact hfin m0 (by rw [put_used hm0]; omega)
      · simp only [bind_ok, pure_ok] at hm'
        obtain ⟨m0, hm0, rfl⟩ := hm'
        exact hfin m0 (by rw [put_used hm0]; omega)
      · simp only [pure_bind, pure_ok] at hm'
        subst hm'
        exact hfin _ (by rw [link_used]; omega)
    | pc =>
      simp only [bind_ok, pure_ok] at hm'
      obtain ⟨m0, hm0, rfl⟩ := hm'
      exact hfin m0 (by rw [put_used hm0]; omega)
    | fp =>
      simp only [bind_ok, pure_ok] at hm'
      obtain ⟨m0, hm0, rfl⟩ := hm'
      exact hfin m0 (by rw [put_used hm0]; omega)
  | jump c d f =>
    cases ins <;> simp only [OpOf] at hop
    obtain ⟨rfl, rfl, rfl⟩ := hop
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff, ← pow_add] at hex
    obtain ⟨_, hc, _, hd, _, hf, -⟩ := hex
    simp only [runOp, bind_ok] at e
    obtain ⟨ca, hca, cb, hcb, cc, hcc, wc, -, vc, -, wd, -, vd, -, wf, -, vf, -, s1, hs1, e⟩ := e
    obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
    simp only [pure_ok] at hm; subst hm
    obtain ⟨rfl, hc'⟩ := cellAt_ok hca
    obtain ⟨rfl, hd'⟩ := cellAt_ok hcb
    obtain ⟨rfl, hf'⟩ := cellAt_ok hcc
    have := hr _ _ hc' hc
    have := hr _ _ hd' hd
    have := hr _ _ hf' hf
    have hu1 : (((s.mem.ensure (s.fp + c)).ensure (s.fp + d)).ensure (s.fp + f)).used ≤ 2 ^ κ := by
      simp only [Mem.ensure_used]; omega
    split_ifs at e
    · simp only [pure_ok] at e; subst e; exact hu1
    · simp only [bind_ok, pure_ok] at e
      obtain ⟨⟨pc', s2⟩, h2, ⟨fp', s3⟩, h3, rfl⟩ := e
      show s3.mem.used ≤ _
      rw [logOr_mem h3, logOr_mem h2]
      exact hu1
  | keccak =>
    cases ins with
    | keccak om otail ob8 ocap oout inOdd' outOdd' outCells =>
      obtain ⟨rfl, rfl, rfl, rfl, L, rfl, hL⟩ := hop
      simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hex
      obtain ⟨input', hin, output', hout', -⟩ := hex
      simp only [runOp, bind_ok] at e
      obtain ⟨cells, hcells, input, hinput, outs, houts, s1, hs1, e⟩ := e
      simp only [pure_ok] at e; subst e
      obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
      rw [bind_ok] at hm
      obtain ⟨m1, hm1, hm⟩ := hm
      simp only [pure_ok] at hm; subst hm
      have hc := exMapM_ok _ _ _ hcells
      have ho := exMapM_ok _ _ _ houts
      have hrin := (readCells_eq_some_iff _ _ _ _).mp hin
      have hrout := (readFirstCells_eq_some_iff _ _ _ _ _).mp hout'
      have hlL : L.length = 13 := by rw [← hL.length_eq, List.length_finRange]
      have hcl : ∀ x ∈ cells, x < 2 ^ κ := fun x hx ↦ by
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
        have hjL : j < L.length := by rw [hc.length_eq]; exact hj
        have h1 := forall₂_getElem hL (i := j) (by simp; omega) hjL
        have h2 := forall₂_getElem hc (i := j) (by simpa using hjL) hj
        simp only [List.getElem_finRange, Fin.cast_mk] at h1 h2
        obtain ⟨h3, h4⟩ := cellAt_ok h2
        have h5 := hrin ⟨j, by omega⟩
        rw [← h1, ← pow_add] at h5
        rw [h3]
        exact hr _ _ (h3 ▸ h4) h5
      have hol : ∀ x ∈ outs, x < 2 ^ κ := fun x hx ↦ by
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
        have hkc : k < outCells.cellCount := by rw [← ho.length_eq, List.length_range] at hk; exact hk
        have h2 := forall₂_getElem ho (i := k) (by rw [List.length_range]; exact hkc) hk
        simp only [List.getElem_range] at h2
        obtain ⟨h3, h4⟩ := cellAt_ok h2
        have h5 := hrout.1 ⟨k, by have := cellCount_le outCells; omega⟩ hkc
        rw [← pow_add, ← pow_add, Nat.add_comm k] at h5
        rw [h3]
        exact hr _ _ (h3 ▸ h4) h5
      refine foldl_ensure_used _ _ (foldlM_used _ (fun x : ℕ × ℕ ↦ x.1 < 2 ^ κ) (fun m x m' hx e hu ↦ ?_) _ _ _
        hm1 hu fun x hx ↦ ?_) fun x hx ↦ ?_
      · obtain ⟨c, k⟩ := x
        rw [put_used e]
        have : c < 2 ^ κ := hx
        omega
      · obtain ⟨c, k⟩ := x
        exact hol c (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hx))
      · rcases List.mem_append.mp hx with hx | hx
        · exact hcl x hx
        · exact hol x hx

    | _ => simp only [OpOf] at hop

end

end LeanVM.Guest.EndExec
