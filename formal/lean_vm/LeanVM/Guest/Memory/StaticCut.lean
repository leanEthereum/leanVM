/-
  LeanVM.Guest.Memory.StaticCut

  The static checkers' walk of a body, cut into ranges of its statements: each range's result and
  the constants after it, so that a function too large for one kernel check is checked a range at a
  time, by either family (`chkS`, `chkV`).
-/

module

public import LeanVM.Guest.Memory.Family

/-!
# Cutting a checker's walk

Both checkers walk a body statement by statement (`blockR`, `blockRV`): a statement gives its
bound and the constants after it, or stops the walk (`ret`), and the bounds add up. `runB add zero
step` is that walk for any statement step and any associative addition (`blockR_run`,
`blockRV_run`), and `runS` a range's: its bounds added and the constants after it. A walk is its
first range's followed by the rest's (`runB_cut`, `runB_drop`), so a body is checked by ranges
whose constants at each cut, and results, are literals the generator writes, each range one kernel
check. A loop helper's body must also be without `ret`, which the ranges check through its step
(`guardRet`, `runB_guard`), and its tail is checked apart (`loopTail`). `chkS_of_run` and
`chkV_of_run` give a function's check from its walk's result. The generator (`scripts/count`,
`family.write_cuts`) cuts a function costlier than a module of the family, its walk mirrored in
Python (`checker.run_range`) for the literals.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-! ## Runs -/

section Run

variable {σ A : Type} (add : A → A → A) (zero : A) (step : Stmt → σ → Option (A × Option σ))

/-- **A block's walk** from the state `ρ`: its statements' results added, up to its first stop. -/
def runB : List Stmt → σ → Option A
  | [], _ => some zero
  | s :: ss, ρ => match step s ρ with
    | none => none
    | some (r, some ρ') => (runB ss ρ').map (add r)
    | some (r, none) => some r

/-- **A nonempty range's walk**: its results added, and the state after it (`none` once stopped). -/
def runS : List Stmt → σ → Option (A × Option σ)
  | [], _ => none
  | [s], ρ => step s ρ
  | s :: s' :: ss, ρ => match step s ρ with
    | none => none
    | some (r, some ρ') => (runS (s' :: ss) ρ').map fun q => (add r q.1, q.2)
    | some (r, none) => some (r, none)

variable {add zero step}

theorem runB_cut (hassoc : ∀ a b c, add (add a b) c = add a (add b c)) :
    ∀ {l : List Stmt} {ρ : σ} {r : A} {ρ' : σ} (l' : List Stmt), runS add step l ρ = some (r, some ρ') →
      runB add zero step (l ++ l') ρ = (runB add zero step l' ρ').map (add r)
  | [], _, _, _, _, h => by simp [runS] at h
  | [s], ρ, r, ρ', l', h => by
      simp only [runS] at h
      simp only [List.cons_append, List.nil_append, runB, h]
  | s :: s' :: ss, ρ, r, ρ', l', h => by
      simp only [runS] at h
      rcases hs : step s ρ with _ | ⟨r1, _ | ρ1⟩ <;> rw [hs] at h
      · cases h
      · cases h
      · simp only at h
        rcases hq : runS add step (s' :: ss) ρ1 with _ | ⟨q1, q2⟩ <;> rw [hq] at h
        · cases h
        · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have ih := runB_cut hassoc l' hq
          rw [List.cons_append, runB, hs]
          simp only
          rw [ih, Option.map_map]
          congr 1
          funext x
          simp [hassoc]

theorem runB_stop : ∀ {l : List Stmt} {ρ : σ} {r : A} (l' : List Stmt), runS add step l ρ = some (r, none) →
    runB add zero step (l ++ l') ρ = some r
  | [], _, _, _, h => by simp [runS] at h
  | [s], ρ, r, l', h => by
      simp only [runS] at h
      simp only [List.cons_append, List.nil_append, runB, h]
  | s :: s' :: ss, ρ, r, l', h => by
      simp only [runS] at h
      rcases hs : step s ρ with _ | ⟨r1, _ | ρ1⟩ <;> rw [hs] at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rw [List.cons_append, runB, hs]
      · simp only at h
        rcases hq : runS add step (s' :: ss) ρ1 with _ | ⟨q1, q2⟩ <;> rw [hq] at h
        · cases h
        · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have ih := runB_stop l' hq
          rw [List.cons_append, runB, hs]
          simp only
          rw [ih]; rfl

/-- The range from `a` and the walk from `a + n` make the walk from `a`. -/
theorem runB_drop (hassoc : ∀ a b c, add (add a b) c = add a (add b c)) {l : List Stmt} {a n : ℕ}
    {ρ ρ' : σ} {r R : A} (h : runS add step ((l.drop a).take n) ρ = some (r, some ρ'))
    (h' : runB add zero step (l.drop (a + n)) ρ' = some R) :
    runB add zero step (l.drop a) ρ = some (add r R) := by
  rw [← List.take_append_drop n (l.drop a), runB_cut hassoc _ h, List.drop_drop, h']; rfl

/-- A range that stops ends the walk. -/
theorem runB_dropStop {l : List Stmt} {a n : ℕ} {ρ : σ} {r : A}
    (h : runS add step ((l.drop a).take n) ρ = some (r, none)) :
    runB add zero step (l.drop a) ρ = some r := by
  rw [← List.take_append_drop n (l.drop a), runB_stop _ h]

theorem runB_end {l : List Stmt} {a : ℕ} {ρ : σ} (ha : l.length ≤ a) :
    runB add zero step (l.drop a) ρ = some zero := by
  rw [List.drop_eq_nil_of_le ha]; rfl

/-! ### Without `ret` -/

/-- `Stmt.noRet`, by the recursor (`noRetR_eq`). -/
noncomputable def noRetR (s : Stmt) : Bool :=
  Stmt.rec (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool) (motive_3 := fun _ => Bool)
    (fun _ => true) (fun _ _ _ bz bn => bz && bn) (fun _ _ ba => ba) (fun _ _ _ => true)
    (fun _ _ _ => true) (fun _ _ _ _ => true) (fun _ => false) true (fun _ _ b bs => b && bs) true
    (fun _ _ b bs => b && bs) s

/-- `Stmt.noRetListS`, by the recursor. -/
noncomputable def noRetLR (ss : List Stmt) : Bool :=
  Stmt.rec_1 (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool) (motive_3 := fun _ => Bool)
    (fun _ => true) (fun _ _ _ bz bn => bz && bn) (fun _ _ ba => ba) (fun _ _ _ => true)
    (fun _ _ _ => true) (fun _ _ _ _ => true) (fun _ => false) true (fun _ _ b bs => b && bs) true
    (fun _ _ b bs => b && bs) ss

/-- `Stmt.noRetArms`, by the recursor. -/
noncomputable def noRetAR (as : List (List Stmt)) : Bool :=
  Stmt.rec_2 (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool) (motive_3 := fun _ => Bool)
    (fun _ => true) (fun _ _ _ bz bn => bz && bn) (fun _ _ ba => ba) (fun _ _ _ => true)
    (fun _ _ _ => true) (fun _ _ _ _ => true) (fun _ => false) true (fun _ _ b bs => b && bs) true
    (fun _ _ b bs => b && bs) as

theorem noRetR_eq (s : Stmt) : noRetR s = Stmt.noRet s :=
  Stmt.rec (motive_1 := fun s => noRetR s = Stmt.noRet s)
    (motive_2 := fun ss => noRetLR ss = Stmt.noRetListS ss)
    (motive_3 := fun as => noRetAR as = Stmt.noRetArms as)
    (fun _ => rfl)
    (fun _ z n hz hn => by
      show (noRetLR z && noRetLR n) = _
      rw [hz, hn, Stmt.noRet])
    (fun _ arms ha => by
      show noRetAR arms = _
      rw [ha, Stmt.noRet])
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ => rfl) rfl
    (fun s ss hs hss => by
      show (noRetR s && noRetLR ss) = _
      rw [hs, hss, Stmt.noRetListS])
    rfl
    (fun a as ha has => by
      show (noRetLR a && noRetAR as) = _
      rw [ha, has, Stmt.noRetArms])
    s

/-- The step on a statement without `ret`, failing on any other. -/
noncomputable def guardRet (step : Stmt → σ → Option (A × Option σ)) (s : Stmt) (ρ : σ) :
    Option (A × Option σ) :=
  if noRetR s then step s ρ else none

/-- A step stopping only at a `ret`. -/
def StopsAtRet (step : Stmt → σ → Option (A × Option σ)) : Prop :=
  ∀ s ρ r, step s ρ = some (r, none) → Stmt.noRet s = false

/-- **A guarded walk** is the walk of a block without `ret`. -/
theorem runB_guard (hstop : StopsAtRet step) : ∀ {l : List Stmt} {ρ : σ} {R : A},
    runB add zero (guardRet step) l ρ = some R →
      Stmt.noRetListS l = true ∧ runB add zero step l ρ = some R
  | [], _, _, h => ⟨rfl, h⟩
  | s :: ss, ρ, R, h => by
      simp only [runB, guardRet, noRetR_eq] at h
      by_cases hn : Stmt.noRet s = true
      · simp only [hn, ↓reduceIte] at h
        rcases hs : step s ρ with _ | ⟨r, _ | ρ'⟩ <;> rw [hs] at h
        · cases h
        · exact absurd (hstop s ρ r hs) (by rw [hn]; decide)
        · simp only at h
          rcases hq : runB add zero (guardRet step) ss ρ' with _ | R' <;> rw [hq] at h
          · cases h
          · obtain ⟨h1, h2⟩ := runB_guard hstop hq
            refine ⟨by simp [Stmt.noRetListS, hn, h1], ?_⟩
            simp only [runB, hs, h2]
            exact h
      · simp only [hn, Bool.false_eq_true, ↓reduceIte] at h; cases h

end Run

/-! ## The checkers' walks -/

/-- The checkers' constants and bounds, compared: a range's literal result is decided through it, which
instance search does not reach unaided. -/
instance : DecidableEq (Env × BEnv) := inferInstance

theorem Acc.add_assoc (a b c : Acc) : (a.add b).add c = a.add (b.add c) := by
  simp [Acc.add, Aff.add, Nat.add_assoc]

theorem Vec.add_assoc : ∀ a b c : Vec, (a.add b).add c = a.add (b.add c)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | x :: a, y :: b, z :: c => by simp [Vec.add, Nat.add_assoc, Vec.add_assoc a b c]

theorem AccV.add_assoc (a b c : AccV) : (a.add b).add c = a.add (b.add c) := by
  simp [AccV.add, AffV.add, Vec.add_assoc]

section Scalar

variable (cert : String → Cert) (wl : String → Option ℕ) (α : Bool) (ks : List (V × ℕ))
  (ps : List V) (self : String)

/-- **`blockR` is a walk.** -/
theorem blockR_run : ∀ (l : List Stmt) (ρ : Env × BEnv),
    blockR cert wl α ks ps self l ρ = runB Acc.add Acc.zero (stmtR cert wl α ks ps self) l ρ
  | [], _ => rfl
  | s :: ss, ρ => by
      show (match stmtR cert wl α ks ps self s ρ with
        | none => none
        | some (r, some ρ') => Option.addAcc (some r) (blockR cert wl α ks ps self ss ρ')
        | some (r, none) => some r) = _
      simp only [runB]
      rcases stmtR cert wl α ks ps self s ρ with _ | ⟨r, _ | ρ'⟩
      · rfl
      · rfl
      · simp only
        rw [blockR_run ss ρ']
        cases runB Acc.add Acc.zero (stmtR cert wl α ks ps self) ss ρ' with
        | none => rfl
        | some _ => rfl

theorem stmtR_stops : StopsAtRet (stmtR cert wl α ks ps self) := by
  intro s ρ r h
  cases s with
  | ret => rfl
  | atom a => simp [stmtR] at h
  | ite => simp [stmtR] at h
  | match_ => simp [stmtR] at h
  | call => simp [stmtR] at h
  | callIf => simp only [stmtR] at h; split_ifs at h; simp at h
  | dispatch => simp [stmtR] at h

end Scalar

section Vector

variable (cert : String → CertV) (ks : List (V × ℕ)) (ps : List V) (self : String)

/-- **`blockRV` is a walk.** -/
theorem blockRV_run : ∀ (l : List Stmt) (ρ : Env × BEnv),
    blockRV cert ks ps self l ρ = runB AccV.add AccV.zero (stmtRV cert ks ps self) l ρ
  | [], _ => rfl
  | s :: ss, ρ => by
      show (match stmtRV cert ks ps self s ρ with
        | none => none
        | some (r, some ρ') => Option.addAccV (some r) (blockRV cert ks ps self ss ρ')
        | some (r, none) => some r) = _
      simp only [runB]
      rcases stmtRV cert ks ps self s ρ with _ | ⟨r, _ | ρ'⟩
      · rfl
      · rfl
      · simp only
        rw [blockRV_run ss ρ']
        cases runB AccV.add AccV.zero (stmtRV cert ks ps self) ss ρ' with
        | none => rfl
        | some _ => rfl

theorem stmtRV_stops : StopsAtRet (stmtRV cert ks ps self) := by
  intro s ρ r h
  cases s with
  | ret => rfl
  | atom a => simp [stmtRV] at h
  | ite => simp [stmtRV] at h
  | match_ => simp [stmtRV] at h
  | call => simp [stmtRV] at h
  | callIf => simp only [stmtRV] at h; split_ifs at h; simp at h
  | dispatch => simp [stmtRV] at h

end Vector

/-! ## A function's check from its walk -/

/-- A loop helper's body without its tail. -/
def loopBody (fn : Fn) : List Stmt := fn.body.take (fn.body.length - 2)

theorem loopTail_eq {fn : Fn} {endc : Option ℕ} {pre : List Stmt} (h : loopTail fn endc = some pre) :
    pre = loopBody fn := by
  unfold loopTail at h
  split at h
  · rename_i c g i' rest rpre p0 prest hrev hps
    simp only at h
    split_ifs at h
    cases h
    have hb : fn.body = rpre.reverse ++ [.callIf c g (i' :: rest), .ret []] := by
      have := congrArg List.reverse hrev
      rw [List.reverse_reverse] at this
      rw [this]; simp
    unfold loopBody
    rw [hb]; simp
  · cases h

theorem loopShape_of {fn : Fn} {endc : Option ℕ} (ht : (loopTail fn endc).isSome = true)
    (hn : Stmt.noRetListS (loopBody fn) = true) : loopShape fn endc = some (loopBody fn) := by
  rcases h : loopTail fn endc with _ | pre
  · rw [h] at ht; cases ht
  rw [loopTail_eq h] at h
  simp [loopShape, h, hn]

/-- What a scalar certificate's check walks: the body, a loop helper's without its tail. -/
def Cert.walk : Cert → Fn → List Stmt
  | .loop .., fn => loopBody fn
  | _, fn => fn.body

/-- A scalar certificate's constants. -/
def Cert.ks : Cert → List (V × ℕ)
  | .none => []
  | .stat _ _ ks => ks
  | .loop _ _ _ ks => ks

/-- A scalar certificate's check of its walk's result `r` at the frame weight `w`. -/
def Cert.final (w : ℕ) (r : Acc) : Cert → Bool
  | .none => true
  | .stat pre b _ => Aff.leB ⟨w + r.1.c, r.1.cs⟩ b && r.2.all (· ∈ pre)
  | .loop _ pre b _ => Aff.leB ⟨w + r.1.c, r.1.cs⟩ b && r.2.all (· ∈ pre) &&
      b.cs.all (·.1 ≠ 0) && pre.all (·.1 ≠ 0)

/-- A loop helper's tail. -/
def Cert.tail (fn : Fn) : Cert → Bool
  | .loop endc .. => (loopTail fn endc).isSome
  | _ => true

/-- A scalar certificate's step: a loop helper's guarded (`guardRet`). -/
noncomputable def Cert.guard {σ A : Type} (step : Stmt → σ → Option (A × Option σ)) : Cert → Stmt → σ → Option (A × Option σ)
  | .loop .. => guardRet step
  | _ => step

/-- **A function's scalar check from its walk.** -/
theorem chkFn_of_run {look : String → Cert} {wl : String → Option ℕ} {α : Bool} {own : Cert} {w : ℕ}
    {fn : Fn} {r : Acc} (ht : own.tail fn = true)
    (hb : runB Acc.add Acc.zero (own.guard (stmtR look wl α own.ks fn.params fn.name)) (own.walk fn)
      ([], []) = some r)
    (hc : own.final w r = true) : chkFn look wl α own w fn = true := by
  cases own with
  | none => rfl
  | stat pre b ks =>
      simp only [chkFn, Cert.walk, Cert.ks, Cert.guard] at hb ⊢
      rw [← blockR_run] at hb
      rw [hb]; exact hc
  | loop endc pre b ks =>
      simp only [Cert.walk, Cert.ks, Cert.guard, Cert.tail] at hb ht
      obtain ⟨hn, hb⟩ := runB_guard (stmtR_stops _ _ _ _ _ _) hb
      rw [← blockR_run] at hb
      simp only [chkFn]
      rw [loopShape_of ht hn]; simp only; rw [hb]; exact hc

/-- What a vector certificate's check walks. -/
def CertV.walk : CertV → Fn → List Stmt
  | .loop .., fn => loopBody fn
  | _, fn => fn.body

/-- A vector certificate's constants. -/
def CertV.ks : CertV → List (V × ℕ)
  | .none => []
  | .stat _ _ ks => ks
  | .loop _ _ _ ks => ks

/-- A vector certificate's check of its walk's result `r` at the frame weights `w`. -/
def CertV.final (w : Vec) (r : AccV) : CertV → Bool
  | .none => true
  | .stat pre b _ => AffV.leB ⟨w.add r.1.c, r.1.cs⟩ b && r.2.all (· ∈ pre)
  | .loop _ pre b _ => AffV.leB ⟨w.add r.1.c, r.1.cs⟩ b && r.2.all (· ∈ pre) &&
      b.cs.all (·.1 ≠ 0) && pre.all (·.1 ≠ 0)

/-- A vector certificate's loop helper's tail. -/
def CertV.tail (fn : Fn) : CertV → Bool
  | .loop endc .. => (loopTail fn endc).isSome
  | _ => true

/-- A vector certificate's step: a loop helper's guarded (`guardRet`). -/
noncomputable def CertV.guard {σ A : Type} (step : Stmt → σ → Option (A × Option σ)) : CertV → Stmt → σ → Option (A × Option σ)
  | .loop .. => guardRet step
  | _ => step

/-- **A function's vector check from its walk.** -/
theorem chkFnV_of_run {look : String → CertV} {own : CertV} {w : Vec} {fn : Fn} {r : AccV}
    (ht : own.tail fn = true)
    (hb : runB AccV.add AccV.zero (own.guard (stmtRV look own.ks fn.params fn.name)) (own.walk fn)
      ([], []) = some r)
    (hc : own.final w r = true) : chkFnV look own w fn = true := by
  cases own with
  | none => rfl
  | stat pre b ks =>
      simp only [chkFnV, CertV.walk, CertV.ks, CertV.guard] at hb ⊢
      rw [← blockRV_run] at hb
      rw [hb]; exact hc
  | loop endc pre b ks =>
      simp only [CertV.walk, CertV.ks, CertV.guard, CertV.tail] at hb ht
      obtain ⟨hn, hb⟩ := runB_guard (stmtRV_stops _ _ _ _) hb
      rw [← blockRV_run] at hb
      simp only [chkFnV]
      rw [loopShape_of ht hn]; simp only; rw [hb]; exact hc

/-! ## The families' steps -/

/-- The step of function `j`'s check in a scalar family (`chkS`). -/
noncomputable def stepS (α : Bool) (cert : ℕ → Cert) (om : ℕ → ℕ) (j : ℕ) (fn : Fn) :
    Stmt → Env × BEnv → Option (Acc × Option (Env × BEnv)) :=
  (cert j).guard (stmtR (lookS cert j) (omLookS om j) α (cert j).ks fn.params fn.name)

/-- The step of function `j`'s check in a vector family (`chkV`). -/
noncomputable def stepV (cert : ℕ → CertV) (j : ℕ) (fn : Fn) :
    Stmt → Env × BEnv → Option (AccV × Option (Env × BEnv)) :=
  (cert j).guard (stmtRV (lookV cert j) (cert j).ks fn.params fn.name)

theorem chkS_of_run {α : Bool} {cert : ℕ → Cert} {om : ℕ → ℕ} {j : ℕ} {fn : Fn} {r : Acc}
    (ht : (cert j).tail fn = true)
    (hb : runB Acc.add Acc.zero (stepS α cert om j fn) ((cert j).walk fn) ([], []) = some r)
    (hc : (cert j).final (om j) r = true) : chkS α cert om j fn = true :=
  chkFn_of_run ht hb hc

theorem chkV_of_run {cert : ℕ → CertV} {om : ℕ → Vec} {j : ℕ} {fn : Fn} {r : AccV}
    (ht : (cert j).tail fn = true)
    (hb : runB AccV.add AccV.zero (stepV cert j fn) ((cert j).walk fn) ([], []) = some r)
    (hc : (cert j).final (om j) r = true) : chkV cert om j fn = true :=
  chkFnV_of_run ht hb hc

end
end LeanVM.Guest.Memory
