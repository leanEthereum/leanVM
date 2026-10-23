import LeanVM.Arithmetization.Completeness.Theorem
import LeanVMTests.Arithmetization.Completeness.Fixture

/-!
# Tests: no witness represents a run over the row cap

A valid execution is unbounded: its steps are limited only by the memory `κ ≤ 32`, and `JUMP` loads
the frame pointer from memory, so frames `g^(4 j)` can fill all `2^32` cells. For every program
that starts with thirty-three `SET_CONSTANT [g^0] g` and a `JUMP [g^1, g^2, g^3]` and has a
sentinel slot (`Shape`), the run that loops over `2^30` frames, thirty-three steps each, is a valid
execution of `33 * 2^30 + 1` steps (`long_run_valid`).

A witness that satisfies `Caps` has at most `2^32` rows in each of its eight tables, and one that
represents a trace has a row for every step of it, with the state it steps from: distinct steps of
a run that halts are distinct states, so distinct rows. Hence a witness that satisfies `Caps` and
represents a valid trace has at most `8 * 2^32` steps in the trace (`steps_le_rows`), and no
witness represents the long run (`completeness_fails_on_long_run`). So the row cap `hrows` of
`constraintCompleteness_rows` cannot be dropped (`completeness_needs_rows`), on a program whose
sentinel slot is not a `JUMP`.
-/

namespace LeanVMTests.Arithmetization.Completeness.LongRun

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open Air.Flat (EnsembleWitness)
open LeanVMTests.Arithmetization.Completeness.Fixture

/-- The number of frames. -/
def J : ℕ := 2 ^ 30

/-- The image, at `κ = 32`, for the sentinel counter `fin`. -/
def img (fin : K) : MemImage 32 := fun n ↦
  if (n : ℕ) % 4 = 2 then (if (n : ℕ) / 4 = J - 1 then ofK fin else ofK g)
  else if (n : ℕ) % 4 = 3 then
    (if (n : ℕ) / 4 = J - 1 then ofK 1 else ofK (gpow (4 * ((n : ℕ) / 4 + 1))))
  else ofK g

/-- The memory of `2^32` cells holds `4 J` cells, `J` frames of four. -/
theorem two_pow_32 : (2 : ℕ) ^ 32 = 4 * J := by norm_num [J]

/-- Reading the address of a cell of the image gives the cell. -/
theorem read_img (fin : K) (n : ℕ) (hn : n < 2 ^ 32) :
    (img fin).read (gpow n) = some (img fin ⟨n, hn⟩) :=
  MemImage.read_gpow (by decide) (img fin) ⟨n, hn⟩

/-- Cell `4 j` of the image holds `g`: the operand of the `SET_CONSTANT`. -/
theorem img_cell0 (fin : K) (j : ℕ) (hj : j < J) :
    img fin ⟨4 * j, by have := two_pow_32; omega⟩ = ofK g := by
  unfold img
  simp

/-- Cell `4 j + 1` holds `g`: the `JUMP` condition, nonzero. -/
theorem img_cell1 (fin : K) (j : ℕ) (hj : j < J) :
    img fin ⟨4 * j + 1, by have := two_pow_32; omega⟩ = ofK g := by
  unfold img
  simp

/-- Cell `4 j + 2` holds `g`, the `JUMP` destination (slot `1`), except in the last frame. -/
theorem img_cell2 (fin : K) (j : ℕ) (hj : j < J) (hne : j ≠ J - 1) :
    img fin ⟨4 * j + 2, by have := two_pow_32; omega⟩ = ofK g := by
  unfold img
  have h1 : (4 * j + 2) % 4 = 2 := by omega
  have h2 : (4 * j + 2) / 4 ≠ J - 1 := by omega
  simp [h1, h2]

/-- In the last frame that cell holds the sentinel counter. -/
theorem img_cell2_last (fin : K) :
    img fin ⟨4 * (J - 1) + 2, by have := two_pow_32; unfold J at *; omega⟩ = ofK fin := by
  unfold img
  have h1 : (4 * (J - 1) + 2) % 4 = 2 := by unfold J; omega
  have h2 : (4 * (J - 1) + 2) / 4 = J - 1 := by unfold J; omega
  simp [h1, h2]

/-- Cell `4 j + 3` holds the next frame pointer `g^(4 (j + 1))`, except in the last frame. -/
theorem img_cell3 (fin : K) (j : ℕ) (hj : j < J) (hne : j ≠ J - 1) :
    img fin ⟨4 * j + 3, by have := two_pow_32; omega⟩ = ofK (gpow (4 * (j + 1))) := by
  unfold img
  have h1 : (4 * j + 3) % 4 ≠ 2 := by omega
  have h2 : (4 * j + 3) % 4 = 3 := by omega
  have h3 : (4 * j + 3) / 4 ≠ J - 1 := by omega
  have h4 : (4 * j + 3) / 4 = j := by omega
  simp [h2, h4, hne]

/-- In the last frame that cell holds `1`, the final frame pointer. -/
theorem img_cell3_last (fin : K) :
    img fin ⟨4 * (J - 1) + 3, by have := two_pow_32; unfold J at *; omega⟩ = ofK 1 := by
  unfold img
  have h2 : (4 * (J - 1) + 3) % 4 = 3 := by unfold J; omega
  have h3 : (4 * (J - 1) + 3) / 4 = J - 1 := by unfold J; omega
  simp [h2, h3]

/-- Slots `0 … 32` are `SET_CONSTANT [g^0] g`, slot `33` is `JUMP [g^1, g^2, g^3]`, and the
sentinel slot lies beyond them. -/
structure Shape (prog : Program) : Prop where
  /-- The first thirty-three slots set the cell at the frame pointer to `g`. -/
  sets : ∀ s, s ≤ 32 → prog.fetch (gpow s) = some (.setConstant (gpow 0) (ofK g))
  /-- Slot `33` jumps to slot `1` in the frame its third cell names. -/
  jump : prog.fetch (gpow 33) = some (.jump (gpow 1) (gpow 2) (gpow 3))
  /-- The program has at least `2^6` slots, so the sentinel is past slot `33`. -/
  big : 6 ≤ prog.logSize

/-- The sentinel counter is none of the slots `0 … 33`. -/
theorem Shape.finalPc_ne {prog : Program} (h : Shape prog) {s : ℕ} (hs : s ≤ 33) :
    prog.finalPc ≠ gpow s := fun heq ↦
  gpow_ne_finalPc prog (n := s) (by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h.big
    omega) heq.symm

/-! ## Steps -/

theorem set_step (prog : Program) (fin : K) {s j : ℕ}
    (hs : prog.fetch (gpow s) = some (.setConstant (gpow 0) (ofK g))) (hj : j < J) :
    step prog (img fin) ⟨gpow s, gpow (4 * j)⟩ = some ⟨gpow (s + 1), gpow (4 * j)⟩ := by
  have hlt : 4 * j < 2 ^ 32 := by have := two_pow_32; omega
  have hr : (img fin).read (gpow (4 * j)) = some (ofK g) := by
    rw [read_img fin (4 * j) hlt, img_cell0 fin j hj]
  have hmul : gpow (4 * j) * gpow 0 = gpow (4 * j) := by
    show g ^ (4 * j) * g ^ 0 = g ^ (4 * j)
    rw [pow_zero, mul_one]
  rw [step_of_fetch_eq_some (r := ⟨gpow s, gpow (4 * j)⟩) hs]
  have hex := executeWith_set_of_read (read := (img fin).read) (r := ⟨gpow s, gpow (4 * j)⟩) (o := gpow 0)
    (k := ofK g) (by show (img fin).read (gpow (4 * j) * gpow 0) = _; rw [hmul]; exact hr)
  show executeWith (img fin).read ⟨gpow s, gpow (4 * j)⟩ (.setConstant (gpow 0) (ofK g)) = _
  rw [hex, gpow_succ]
  rfl

/-- The `JUMP` in frame `4 j` goes to slot `1` in frame `4 (j + 1)`. -/
theorem jump_loop (prog : Program) (fin : K) {j : ℕ} (hj : j < J) (hne : j ≠ J - 1)
    (h33 : prog.fetch (gpow 33) = some (.jump (gpow 1) (gpow 2) (gpow 3))) :
    step prog (img fin) ⟨gpow 33, gpow (4 * j)⟩ = some ⟨gpow 1, gpow (4 * (j + 1))⟩ := by
  have hlt : ∀ o, o ≤ 3 → 4 * j + o < 2 ^ 32 := by intro o ho; have := two_pow_32; omega
  have m1 : gpow (4 * j) * gpow 1 = gpow (4 * j + 1) := (pow_add g (4 * j) 1).symm
  have m2 : gpow (4 * j) * gpow 2 = gpow (4 * j + 2) := (pow_add g (4 * j) 2).symm
  have m3 : gpow (4 * j) * gpow 3 = gpow (4 * j + 3) := (pow_add g (4 * j) 3).symm
  have hc : (img fin).read (gpow (4 * j) * gpow 1) = some (ofK g) := by
    rw [m1, read_img fin _ (hlt 1 (by norm_num)), img_cell1 fin j hj]
  have hd : (img fin).read (gpow (4 * j) * gpow 2) = some (ofK g) := by
    rw [m2, read_img fin _ (hlt 2 (by norm_num)), img_cell2 fin j hj hne]
  have hf : (img fin).read (gpow (4 * j) * gpow 3) = some (ofK (gpow (4 * (j + 1)))) := by
    rw [m3, read_img fin _ (hlt 3 (by norm_num)), img_cell3 fin j hj hne]
  have hex := executeWith_jump_taken (read := (img fin).read) (r := ⟨gpow 33, gpow (4 * j)⟩)
    (oc := gpow 1) (od := gpow 2) (of := gpow 3) (c := g) (d := g) (f := gpow (4 * (j + 1)))
    hc hd hf g_ne_zero
  rw [step_of_fetch_eq_some (r := ⟨gpow 33, gpow (4 * j)⟩) h33]
  show executeWith (img fin).read ⟨gpow 33, gpow (4 * j)⟩ (.jump (gpow 1) (gpow 2) (gpow 3)) = _
  rw [hex, show gpow 1 = g from pow_one g]

/-- The `JUMP` in the last frame goes to the sentinel with frame pointer `1`. -/
theorem jump_last (prog : Program) (fin : K)
    (h33 : prog.fetch (gpow 33) = some (.jump (gpow 1) (gpow 2) (gpow 3))) :
    step prog (img fin) ⟨gpow 33, gpow (4 * (J - 1))⟩ = some ⟨fin, 1⟩ := by
  have hlt : ∀ o, o ≤ 3 → 4 * (J - 1) + o < 2 ^ 32 := by
    intro o ho; have := two_pow_32; unfold J at *; omega
  have m1 : gpow (4 * (J - 1)) * gpow 1 = gpow (4 * (J - 1) + 1) :=
    (pow_add g (4 * (J - 1)) 1).symm
  have m2 : gpow (4 * (J - 1)) * gpow 2 = gpow (4 * (J - 1) + 2) :=
    (pow_add g (4 * (J - 1)) 2).symm
  have m3 : gpow (4 * (J - 1)) * gpow 3 = gpow (4 * (J - 1) + 3) :=
    (pow_add g (4 * (J - 1)) 3).symm
  have hJ : J - 1 < J := by unfold J; omega
  have hc : (img fin).read (gpow (4 * (J - 1)) * gpow 1) = some (ofK g) := by
    rw [m1, read_img fin _ (hlt 1 (by norm_num)), img_cell1 fin (J - 1) hJ]
  have hd : (img fin).read (gpow (4 * (J - 1)) * gpow 2) = some (ofK fin) := by
    rw [m2, read_img fin _ (hlt 2 (by norm_num)), img_cell2_last fin]
  have hf : (img fin).read (gpow (4 * (J - 1)) * gpow 3) = some (ofK (1 : K)) := by
    rw [m3, read_img fin _ (hlt 3 (by norm_num)), img_cell3_last fin]
  have hex := executeWith_jump_taken (read := (img fin).read) (r := ⟨gpow 33, gpow (4 * (J - 1))⟩)
    (oc := gpow 1) (od := gpow 2) (of := gpow 3) (c := g) (d := fin) (f := 1) hc hd hf g_ne_zero
  rw [step_of_fetch_eq_some (r := ⟨gpow 33, gpow (4 * (J - 1))⟩) h33]
  exact hex

/-! ## Runs -/

theorem run_sets (prog : Program) (fin : K) (sh : Shape prog) {j : ℕ} (hj : j < J) :
    ∀ m s, s + m ≤ 33 →
      run prog (img fin) m ⟨gpow s, gpow (4 * j)⟩ = some ⟨gpow (s + m), gpow (4 * j)⟩ := by
  intro m
  induction m with
  | zero => intro s _; rfl
  | succ m ih =>
    intro s hs
    have hpc : (⟨gpow s, gpow (4 * j)⟩ : Regs K).pc ≠ prog.finalPc :=
      fun h ↦ sh.finalPc_ne (by omega) h.symm
    have h1 := run_one hpc (set_step prog fin (sh.sets s (by omega)) hj)
    have h2 := ih (s + 1) (by omega)
    have := run_trans h1 h2
    rw [show 1 + m = m + 1 by omega, show s + 1 + m = s + (m + 1) by omega] at this
    exact this

/-- The 32 `SET_CONSTANT`s of an iteration. -/
theorem run_body (prog : Program) (fin : K) (sh : Shape prog) {j : ℕ} (hj : j < J) :
    run prog (img fin) 32 ⟨gpow 1, gpow (4 * j)⟩ = some ⟨gpow 33, gpow (4 * j)⟩ :=
  run_sets prog fin sh hj 32 1 (by norm_num)

/-- Slot `33` is not the sentinel. -/
theorem pc33_ne (prog : Program) (sh : Shape prog) (j : ℕ) :
    (⟨gpow 33, gpow (4 * j)⟩ : Regs K).pc ≠ prog.finalPc :=
  fun h ↦ sh.finalPc_ne (le_refl 33) h.symm

/-- One iteration that loops. -/
theorem run_iter (prog : Program) (fin : K) (sh : Shape prog) {j : ℕ} (hj : j < J)
    (hne : j ≠ J - 1) :
    run prog (img fin) 33 ⟨gpow 1, gpow (4 * j)⟩ = some ⟨gpow 1, gpow (4 * (j + 1))⟩ :=
  run_trans (run_body prog fin sh hj)
    (run_one (pc33_ne prog sh j) (jump_loop prog fin hj hne sh.jump))

/-- The last iteration, which jumps to the sentinel. -/
theorem run_last (prog : Program) (fin : K) (sh : Shape prog) :
    run prog (img fin) 33 ⟨gpow 1, gpow (4 * (J - 1))⟩ = some ⟨fin, 1⟩ := by
  have hJ : J - 1 < J := by unfold J; omega
  exact run_trans (run_body prog fin sh hJ)
    (run_one (pc33_ne prog sh (J - 1)) (jump_last prog fin sh.jump))

/-- `m` looping iterations from slot `1` in frame `0` end at slot `1` in frame `4 m`. -/
theorem run_iters (prog : Program) (fin : K) (sh : Shape prog) :
    ∀ m, m ≤ J - 1 →
      run prog (img fin) (33 * m) ⟨gpow 1, gpow (4 * 0)⟩ = some ⟨gpow 1, gpow (4 * m)⟩ := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    have hJ : m < J := by omega
    have := run_trans (ih (by omega)) (run_iter prog fin sh hJ (by omega))
    rw [show 33 * m + 33 = 33 * (m + 1) by ring] at this
    exact this

/-- The whole run: slot `0`, then `J - 1` looping iterations, then the last one. -/
theorem run_full (prog : Program) (sh : Shape prog) :
    run prog (img prog.finalPc) (33 * J + 1) Regs.initial = some (Regs.final prog) := by
  have hJ : 0 < J := by unfold J; omega
  have e : (Regs.initial : Regs K) = ⟨gpow 0, gpow (4 * 0)⟩ := by
    unfold Regs.initial
    rw [Nat.mul_zero]
    simp [gpow]
  have hpc : (⟨gpow 0, gpow (4 * 0)⟩ : Regs K).pc ≠ prog.finalPc :=
    fun h ↦ sh.finalPc_ne (by norm_num : 0 ≤ 33) h.symm
  have h0 := run_one hpc (set_step prog prog.finalPc (sh.sets 0 (by norm_num)) hJ)
  have h1 := run_trans h0 (run_iters prog prog.finalPc sh (J - 1) le_rfl)
  have h2 := run_trans h1 (run_last prog prog.finalPc sh)
  rw [e, show 33 * J + 1 = 1 + 33 * (J - 1) + 33 by omega]
  exact h2

/-- **The long valid execution.**  For every program of the shape, a valid execution with more
than `2^35 = 8 * 2^32` steps. -/
theorem long_run_valid (prog : Program) (sh : Shape prog) :
    ∃ (input : PublicInput) (t : Trace prog), ValidExecution prog input t ∧ 2 ^ 35 < t.steps := by
  have hJ : 0 < J := by unfold J; omega
  refine ⟨⟨![g, 0, g, 0]⟩, ⟨32, img prog.finalPc, 33 * J + 1⟩, ⟨?_, run_full prog sh⟩, ?_⟩
  · refine ⟨by show minLogMem ≤ 32; decide, by show 32 ≤ maxLogMem; decide, ?_, ?_⟩
    · show (img prog.finalPc).read (gpow 0) = some (E.ofLimbs g 0 0)
      have hc : img prog.finalPc ⟨0, by norm_num⟩ = ofK g := img_cell0 prog.finalPc 0 hJ
      rw [read_img prog.finalPc 0 (by norm_num), hc, ofK_eq_ofLimbs]
    · show (img prog.finalPc).read (gpow 1) = some (E.ofLimbs g 0 0)
      have hc : img prog.finalPc ⟨1, by norm_num⟩ = ofK g := img_cell1 prog.finalPc 0 hJ
      rw [read_img prog.finalPc 1 (by norm_num), hc, ofK_eq_ofLimbs]
  · show 2 ^ 35 < 33 * J + 1
    unfold J
    norm_num

/-! ## Distinct states -/

/-- The register states of a run that halts at the sentinel are pairwise distinct. -/
theorem run_inj {κ : ℕ} {prog : Program} {L : MemImage κ} {n : ℕ} {r₀ rf : Regs K}
    (h : run prog L n r₀ = some rf) (hf : rf.pc = prog.finalPc) {a b : ℕ} {r : Regs K}
    (ha : run prog L a r₀ = some r) (hb : run prog L b r₀ = some r) : a = b := by
  -- no run continues past the sentinel
  have hle : ∀ m s, run prog L m r₀ = some s → m ≤ n := by
    intro m s hm
    by_contra hlt
    obtain ⟨k, hk⟩ : ∃ k, m = n + (k + 1) := ⟨m - n - 1, by omega⟩
    rw [hk, run_add, h] at hm
    change run prog L (k + 1) rf = some s at hm
    rw [run_succ_of_eq hf] at hm
    exact absurd hm (by simp)
  -- the case `a < b` is contradictory; symmetry gives the rest
  have key : ∀ a b : ℕ, run prog L a r₀ = some r → run prog L b r₀ = some r → a < b → False := by
    intro a b ha hb hab
    have hbn := hle b r hb
    -- from `r`: `n - a` steps reach `rf`, and `b - a` steps return to `r`
    have h1 : run prog L (n - a) r = some rf := by
      have := h
      rw [show n = a + (n - a) by omega, run_add, ha] at this
      exact this
    have h2 : run prog L (b - a) r = some r := by
      have := hb
      rw [show b = a + (b - a) by omega, run_add, ha] at this
      exact this
    have h3 : run prog L (n - a - (b - a)) r = some rf := by
      have := h1
      rw [show n - a = (b - a) + (n - a - (b - a)) by omega, run_add, h2] at this
      exact this
    obtain ⟨r₁, hr₁, hne⟩ := run_intermediate h1 (m := n - a - (b - a)) (by omega)
    rw [h3] at hr₁
    obtain rfl := Option.some.inj hr₁
    exact hne hf
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact (key a b ha hb hab).elim
  · rfl
  · exact (key b a hb ha hab).elim

/-- The `k`-th register state of a valid trace is the run's state after `k` steps. -/
theorem regs_getElem' {prog : Program} {t : Trace prog}
    (h : run prog t.image t.steps Regs.initial = some (Regs.final prog)) (k : ℕ)
    (hk : k < t.regs.length) : run prog t.image k Regs.initial = some t.regs[k] := by
  have hk' : k ≤ t.steps := by
    have := Trace.regs_length h
    omega
  rw [List.getElem_of_eq (regs_eq_map h) hk, List.getElem_map, List.getElem_range]
  exact run_stateAt h hk'

/-- Two register pairs with the same components are equal. -/
theorem regs_ext' {a b : Regs K} (h1 : a.pc = b.pc) (h2 : a.fp = b.fp) : a = b := by
  cases a; cases b; simp_all

/-! ## The counting bound -/

/-- A witness that satisfies `Caps` and represents a valid trace has at least as many rows as the
trace has steps, over its eight tables: `t.steps ≤ 8 * 2^32`. -/
theorem steps_le_rows {prog : Program} {input : PublicInput}
    {w : EnsembleWitness (leanIsaEnsemble prog)} {t : Trace prog}
    (hv : ValidExecution prog input t) (hc : Caps w) (hr : AssignmentRepresents w t) :
    t.steps ≤ 8 * 2 ^ 32 := by
  obtain ⟨-, hrun⟩ := hv
  have hlen : t.regs.length = t.steps + 1 := Trace.regs_length hrun
  have hrow : ∀ k : Fin t.steps, ∃ (j : Fin 8) (row : Array K), row ∈ (tableAt w j).table ∧
      rowMessagesOn (tableAt w j) row StatePull.toRaw =
        [#[(t.regs[k.val]'(by omega)).pc, (t.regs[k.val]'(by omega)).fp]] := by
    intro k
    have hk : k.val + 1 < t.regs.length := by have := k.isLt; omega
    obtain ⟨tb, htb, row, hrow, hpull, -⟩ := hr.regs_embed k hk
    obtain ⟨j, rfl⟩ := mem_tables_iff.mp htb
    exact ⟨j, row, hrow, hpull⟩
  choose j row hmem hmsg using hrow
  have hinj : Function.Injective fun k : Fin t.steps ↦ (⟨j k, row k⟩ : Σ _ : Fin 8, Array K) := by
    intro k k' h
    have hh := Sigma.mk.inj h
    have hj : j k = j k' := hh.1
    have hr' : row k = row k' := eq_of_heq hh.2
    have h1 := hmsg k
    have h2 := hmsg k'
    rw [← hj, ← hr', h1] at h2
    simp only [List.cons.injEq, and_true, Array.mk.injEq] at h2
    obtain ⟨hpc, hfp⟩ := h2
    have hreg : t.regs[k.val]'(by have := k.isLt; omega) =
        t.regs[k'.val]'(by have := k'.isLt; omega) := regs_ext' hpc hfp
    have ha := regs_getElem' hrun k.val (by have := k.isLt; omega)
    have hb := regs_getElem' hrun k'.val (by have := k'.isLt; omega)
    rw [← hreg] at hb
    exact Fin.ext (run_inj hrun rfl ha hb)
  let T : Finset (Σ _ : Fin 8, Array K) :=
    (Finset.univ : Finset (Fin 8)).sigma fun j ↦ (tableAt w j).table.toFinset
  have hlen' : ∀ j : Fin 8, (tableAt w j).table.length ≤ 2 ^ 32 :=
    fun j ↦ hc.heights (tableAt w j) (mem_tables_iff.mpr ⟨j, rfl⟩)
  calc t.steps = (Finset.univ : Finset (Fin t.steps)).card := by simp
    _ ≤ T.card := Finset.card_le_card_of_injOn (fun k ↦ (⟨j k, row k⟩ : Σ _ : Fin 8, Array K))
        (fun k _ ↦ by
          simp only [T, Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_univ, Set.mem_univ,
            Finset.mem_coe, List.mem_toFinset, true_and]
          exact hmem k)
        hinj.injOn
    _ = ∑ j : Fin 8, ((tableAt w j).table.toFinset).card := Finset.card_sigma _ _
    _ ≤ ∑ _j : Fin 8, 2 ^ 32 := Finset.sum_le_sum fun j _ ↦
        (List.toFinset_card_le _).trans (hlen' j)
    _ = 8 * 2 ^ 32 := by simp


/-! ## The refutation -/

/-- **Completeness fails on long runs without the row cap.**  For every program of the shape, there is a
valid execution that no witness of `SatisfiedBy` represents. -/
theorem completeness_fails_on_long_run (prog : Program) (sh : Shape prog) :
    ∃ (input : PublicInput) (t : Trace prog), ValidExecution prog input t ∧
      ¬ ∃ w : EnsembleWitness (leanIsaEnsemble prog),
          SatisfiedBy prog input w ∧ AssignmentRepresents w t := by
  obtain ⟨input, t, hv, hbig⟩ := long_run_valid prog sh
  refine ⟨input, t, hv, ?_⟩
  rintro ⟨w, hsat, hrep⟩
  have hle := steps_le_rows hv hsat.caps hrep
  norm_num at hle hbig
  omega


/-- A program of `2^11` slots with the shape: `SET_CONSTANT [g^0] g` in slots `0 … 32`, the `JUMP`
in slot `33`, and `SET_CONSTANT` elsewhere, the sentinel included. -/
def shapeProg : Program :=
  ⟨11, by decide, fun i ↦
    if (i : ℕ) = 33 then .jump (gpow 1) (gpow 2) (gpow 3) else .setConstant (gpow 0) (ofK g)⟩

/-- It has the shape. -/
theorem shapeProg_shape : Shape shapeProg where
  sets := fun s hs ↦ by
    have h := shapeProg.fetch_gpow ⟨s, by show s < 2 ^ 11; omega⟩
    rw [h]
    simp only [shapeProg]
    simp [show s ≠ 33 by omega]
  jump := by
    have h := shapeProg.fetch_gpow ⟨33, by show 33 < 2 ^ 11; norm_num⟩
    rw [h]
    simp [shapeProg]
  big := by decide

/-- The sentinel slot is not a `JUMP`. -/
theorem shapeProg_sentinelSafe : SentinelSafe shapeProg := by decide

/-- **The row cap is load-bearing.** A program whose sentinel slot is not a `JUMP` has a valid
execution that no witness of `SatisfiedBy` represents; its run has more than `2^32` rows of some
opcode, so `constraintCompleteness_rows` needs `hrows`. -/
theorem completeness_needs_rows :
    SentinelSafe shapeProg ∧
      ∃ (input : PublicInput) (t : Trace shapeProg), ValidExecution shapeProg input t ∧
        ¬ (∀ op, t.runRows op ≤ 2 ^ maxLogRows) ∧
        ¬ ∃ w : EnsembleWitness (leanIsaEnsemble shapeProg),
            SatisfiedBy shapeProg input w ∧ AssignmentRepresents w t := by
  refine ⟨shapeProg_sentinelSafe, ?_⟩
  obtain ⟨input, t, hv, hbig⟩ := long_run_valid shapeProg shapeProg_shape
  have hno : ¬ ∃ w : EnsembleWitness (leanIsaEnsemble shapeProg),
      SatisfiedBy shapeProg input w ∧ AssignmentRepresents w t := by
    rintro ⟨w, hsat, hrep⟩
    have hle := steps_le_rows hv hsat.caps hrep
    norm_num at hle hbig
    omega
  refine ⟨input, t, hv, fun hrows ↦ hno ?_, hno⟩
  obtain ⟨w, hw, hrep, -⟩ := constraintCompleteness_rows hv hrows
  exact ⟨w, hw, hrep⟩

end LeanVMTests.Arithmetization.Completeness.LongRun
