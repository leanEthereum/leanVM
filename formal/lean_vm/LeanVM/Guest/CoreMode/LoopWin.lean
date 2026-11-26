/-
  LeanVM.Guest.CoreMode.LoopWin

  A long loop helper's passes over its body and code, in windows.
-/

module

public import LeanVM.Guest.CoreMode.CoreLoopC

/-!
# A long loop helper's checks in windows

`LoopOkC`'s passes over a body (`loopBB`, `callsBL`, `topOk`, `noPtrL`, `calleePtrOk`, `noFA`, the
conditional calls' conditions, the `match`es' lengths) and over its code (`tgtOk`, `jtdOk`) are each one
kernel evaluation; for `main_loop2` each takes past the memory a module may take. Every one of them is
additive over a split of the body or of the code, so it is checked over consecutive slices (`Wins`), each its own
declaration: `LWins` (the body's statements before its tail call, one predicate `winL` per slice with
the `match`es' lengths it has), `CWins` (the code, from each slice's offset), and the two last
statements apart (`tailL`). `loopFields_of_wins` gives the fields.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (stmtsOf)

@[expose] public section

/-! ## Slices -/

/-- The elements `a` to `b - 1` of a list. -/
def slice {α : Type} (l : List α) (a b : ℕ) : List α := (l.drop a).take (b - a)

theorem slice_split {α : Type} (l : List α) {a b e : ℕ} (_hab : a ≤ b) (hbe : b ≤ e) :
    slice l a e = slice l a b ++ slice l b e := by
  unfold slice
  rw [show e - a = (b - a) + (e - b) by omega, List.take_add, List.drop_drop]
  congr 3
  omega

theorem slice_length {α : Type} {l : List α} {a b : ℕ} (_hab : a ≤ b) (hb : b ≤ l.length) :
    (slice l a b).length = b - a := by
  simp [slice, List.length_take, List.length_drop]
  omega

theorem slice_self {α : Type} (l : List α) (a : ℕ) : slice l a a = [] := by simp [slice]

theorem slice_all {α : Type} (l : List α) : slice l 0 l.length = l := by simp [slice]

/-! ## Windows -/

/-- **Windows from cut `a` to the last cut `e`**: each window, from a cut to the next (`cut x`), passing `P`.
What the long passes are checked over, one declaration per window. -/
def Wins {α : Type} (cut : α → ℕ) (P : ℕ → α → Prop) (e : ℕ) : ℕ → List α → Prop
  | a, [] => a = e
  | a, x :: cs => a ≤ cut x ∧ P a x ∧ Wins cut P e (cut x) cs

/-- **Windows chained**: what holds at the last cut and is carried back over each window holds from the first. -/
theorem wins_fold {α : Type} {cut : α → ℕ} {P : ℕ → α → Prop} {e : ℕ} {Q : ℕ → List α → Prop} (h0 : Q e [])
    (hs : ∀ {a x cs}, a ≤ cut x → cut x ≤ e → P a x → Q (cut x) cs → Q a (x :: cs)) :
    ∀ {a : ℕ} {cs : List α}, Wins cut P e a cs → a ≤ e ∧ Q a cs
  | _, [], h => by subst h; exact ⟨le_rfl, h0⟩
  | _, _ :: _, ⟨hab, hw, hr⟩ =>
    have ⟨hbe, hq⟩ := wins_fold h0 hs hr
    ⟨le_trans hab hbe, hs hab hbe hw hq⟩

/-! ## The body's statements -/

/-- What a long loop helper's checks ask of each statement of its body: a call's callee checked
(`callsBL`), guaranteeing no pointer cell (`calleePtrOk`) and no pointer run (`noPtrL`); no `frameAddr`
(`noFA`); a conditional call's condition at no nonzero constant's cell (`loopShapeOk0`). -/
noncomputable def winP (Cf : CFun) (s : Stmt) : Bool :=
  (match s with
    | .call g args _ => callChk Cf g args && (Cf.sigOf g).postPR.isEmpty
    | _ => true) && calleePtrOk Cf s &&
  (match s with
    | .atom (.frameAddr ..) => false
    | .callIf c _ _ => !Cf.X.nzAt (Cf.X.locAt c.idx)
    | _ => true)

/-- A statement of a window: an atom, a call, a branch or a `match` (no conditional call). -/
def isBW : Stmt → Bool
  | .atom _ | .call .. | .ite .. | .match_ .. => true
  | _ => false

theorem isBS_of_isBW {nm : String} {s : Stmt} (h : isBW s = true) : isBS nm s = true := by
  cases s <;> simp_all [isBW, isBS]

/-- **A slice of the body before the tail call**: its statements (nested ones included) atoms, calls,
branches and `match`es (`isBW`) meeting `winP`, its top-level ones `topOk`, its `match`es' lengths `ml`. -/
noncomputable def winL (Cf : CFun) (l : List Stmt) (ml : List (ℕ × ℕ)) : Bool :=
  (stmtsOf l).all (fun s ↦ isBW s && winP Cf s) && l.all topOk && decide (matchLens l = ml)

theorem matchLens_append (x y : List Stmt) : matchLens (x ++ y) = matchLens x ++ matchLens y := by
  simp [matchLens, stmtsOf_append, List.filterMap_append]

theorem winL_append {Cf : CFun} {x y : List Stmt} {mx my : List (ℕ × ℕ)} (hx : winL Cf x mx = true)
    (hy : winL Cf y my = true) : winL Cf (x ++ y) (mx ++ my) = true := by
  simp only [winL, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hx hy ⊢
  refine ⟨⟨fun s hs ↦ ?_, fun s hs ↦ ?_⟩, by rw [matchLens_append, hx.2, hy.2]⟩
  · rw [stmtsOf_append] at hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hx.1.1 s hs
    · exact hy.1.1 s hs
  · rcases List.mem_append.mp hs with hs | hs
    · exact hx.1.2 s hs
    · exact hy.1.2 s hs

/-- **The body's slices from `a`**, each `winL` with its `match`es' lengths, the last cut `e`. -/
abbrev LWins (Cf : CFun) (l : List Stmt) (e : ℕ) : ℕ → List (ℕ × List (ℕ × ℕ)) → Prop :=
  Wins (·.1) (fun a x ↦ winL Cf (slice l a x.1) x.2 = true) e

theorem lwins_spec {Cf : CFun} {l : List Stmt} {e : ℕ} :
    ∀ {a : ℕ} {cs : List (ℕ × List (ℕ × ℕ))}, LWins Cf l e a cs →
      a ≤ e ∧ winL Cf (slice l a e) (cs.map (·.2)).flatten = true := fun h ↦
  wins_fold (Q := fun (a : ℕ) (cs : List (ℕ × List (ℕ × ℕ))) ↦ winL Cf (slice l a e) (cs.map (·.2)).flatten = true)
    (by simp [winL, slice_self, matchLens, stmtsOf]) (fun {a x cs} hab hbe hw hq ↦ by
      rw [slice_split l hab hbe, List.map_cons, List.flatten_cons]
      exact winL_append hw hq) h

/-! ## The code -/

theorem tgtGo_append {Cf : CFun} {ml : List (ℕ × ℕ)} :
    ∀ (i : ℕ) (x y : List OffsetInstruction), tgtGo Cf ml i (x ++ y) = (tgtGo Cf ml i x && tgtGo Cf ml (i + x.length) y)
  | i, [], y => by simp [tgtGo]
  | i, ins :: x, y => by
    have ih := tgtGo_append (Cf := Cf) (ml := ml) (i + 1) x y
    simp only [List.cons_append, tgtGo, ih, List.length_cons, Bool.and_assoc]
    rw [show i + 1 + x.length = i + (x.length + 1) by omega]

theorem jtdGo_append {Cf : CFun} {E : Mode.Env} {ml : List (ℕ × ℕ)} {dl : List (V × ℕ × List ℕ × List ℕ)} :
    ∀ (x y : List OffsetInstruction), jtdGo Cf E ml dl x = true → jtdGo Cf E ml dl (x ++ y) = jtdGo Cf E ml dl y
  | [], y, _ => rfl
  | ins :: x, y, h => by
    simp only [jtdGo, Bool.and_eq_true] at h
    simp only [List.cons_append, jtdGo, jtdGo_append x y h.2, Bool.and_eq_right_iff_imp]
    intro _
    obtain ⟨h1, -⟩ := h
    cases ins with
    | deref o1 o2 o3 mode =>
      cases mode with
      | cell =>
        cases x with
        | nil =>
          simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1 ⊢
          rcases h1 with h1 | h1
          · exact Or.inl h1
          · cases h1
        | cons i' x => cases i' <;> exact h1
      | _ => rfl
    | _ => rfl

/-- **The code's slices from `a`**, each passing the frame walk's tables' check from its offset and the
jump table's reads' check. -/
abbrev CWins (Cf : CFun) (E : Mode.Env) (ml : List (ℕ × ℕ)) (code : List OffsetInstruction) (e : ℕ) :
    ℕ → List ℕ → Prop :=
  Wins id (fun a b ↦ (tgtGo Cf ml a (slice code a b) && jtdGo Cf E ml [] (slice code a b)) = true) e

theorem cwins_spec {Cf : CFun} {E : Mode.Env} {ml : List (ℕ × ℕ)} {code : List OffsetInstruction} {e : ℕ}
    (he : e ≤ code.length) :
    ∀ {a : ℕ} {cs : List ℕ}, CWins Cf E ml code e a cs →
      a ≤ e ∧ tgtGo Cf ml a (slice code a e) = true ∧ jtdGo Cf E ml [] (slice code a e) = true := fun h ↦
  wins_fold (Q := fun a _ ↦ tgtGo Cf ml a (slice code a e) = true ∧ jtdGo Cf E ml [] (slice code a e) = true)
    (by simp [slice_self, tgtGo, jtdGo]) (fun {a b _} hab hbe hw hq ↦ by
      simp only [id] at hab hbe hw hq
      rw [Bool.and_eq_true] at hw
      refine ⟨?_, ?_⟩
      · rw [slice_split code hab hbe, tgtGo_append, hw.1, slice_length hab (le_trans hbe he),
          show a + (b - a) = b by omega, hq.1]
        rfl
      · rw [slice_split code hab hbe, jtdGo_append _ _ hw.2, hq.2]) h

/-! ## The fields -/

/-- **The body's last two statements**: the tail call to the function itself, one word per parameter,
meeting `winP`, then `ret []`. -/
noncomputable def tailL (Cf : CFun) : Bool :=
  match Cf.fn.body.drop (Cf.fn.body.length - 2) with
  | [.callIf c g args, .ret []] => (g == Cf.fn.name) && Nat.beq args.length Cf.fn.params.length &&
      !Cf.X.nzAt (Cf.X.locAt c.idx)
  | _ => false

theorem tailL_spec {Cf : CFun} (h : tailL Cf = true) : ∃ c args, Cf.fn.body.drop (Cf.fn.body.length - 2) =
    [.callIf c Cf.fn.name args, .ret []] ∧ args.length = Cf.fn.params.length ∧ Cf.X.nzAt (Cf.X.locAt c.idx) = false := by
  unfold tailL at h
  split at h
  · rename_i c g args hd
    simp only [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨rfl, hl⟩, hn⟩ := h
    exact ⟨c, args, hd, hl, hn⟩
  · cases h

/-- **`loopShapeOk0` but its pass over the body.** -/
noncomputable def loopShapeRest0 (Cf : CFun) : Bool :=
  !Cf.X.main && !Cf.X.selfAt 1 && (Cf.X.pcAt 0).isNone && sigsOut Cf.frame.sigs Cf.frame.entry Cf.frame.len &&
    !Cf.frame.F.fpOne &&
    Cf.frame.sig.entry.all (fun o ↦ decide (o + 1 < 2 ^ Exec.envDepth)) &&
    (match Cf.frame.sig.self with
      | some o => decide (o + 1 < 2 ^ Exec.envDepth) && decide (o < 2 ^ 28)
      | none => true) &&
    Cf.frame.sig.entry.contains 0 && Cf.frame.sig.entry.contains 1 &&
    decide (Cf.frame.entry + Cf.frame.len ≤ 2 ^ 30) && Mode.pcsIncr Cf.frame.hints

/-- **`loopShapeOkC` but its pass over the body**, and no residual divisors of the frame walk. -/
noncomputable def loopShapeRest (Cf : CFun) : Bool :=
  loopShapeRest0 Cf && trieNil Cf.frame.nzr && hiRes Cf.frame.sig Cf.gl Cf.fn.params.length Cf.H.sig.ghosts Cf.H.res

/-- **A long loop helper's passes, in windows**: the body's statements before the tail call (`LWins`,
their `match`es' lengths `ml`), its tail (`tailL`), the code (`CWins`), the rest of the shape, the
signatures' pointer runs, or no reader on the body (`rdFree`). -/
structure LoopWins (K : Mode.Cert) (Cf : CFun) (ml : List (ℕ × ℕ)) (cs : List (ℕ × List (ℕ × ℕ))) (ccs : List ℕ) :
    Prop where
  hml : ml = (cs.map (·.2)).flatten
  body : LWins Cf Cf.fn.body (Cf.fn.body.length - 2) 0 cs
  tail : tailL Cf = true
  code : CWins Cf K.E ml K.code K.code.length 0 ccs
  rest : loopShapeRest Cf = true
  ptr : (Cf.H.sig.prePR.isEmpty && Cf.H.sig.postPR.isEmpty || (stmtsOf Cf.fn.body).all rdFree) = true

theorem stmtsOf_all_of {p : Stmt → Bool} {l : List Stmt} (h : ∀ s ∈ stmtsOf l, p s = true) :
    (stmtsOf l).all p = true := List.all_eq_true.mpr h

/-- **The fields of `LoopOkC` the windows give.** -/
theorem loopFields_of_wins {K : Mode.Cert} {Cf : CFun} {ml : List (ℕ × ℕ)} {cs : List (ℕ × List (ℕ × ℕ))}
    {ccs : List ℕ} (h : LoopWins K Cf ml cs ccs) :
    loopBB Cf.fn = true ∧ callsBL Cf = true ∧ Cf.fn.body.all topOk = true ∧
      ((stmtsOf Cf.fn.body).all rdFree || noPtrL Cf) = true ∧ (stmtsOf Cf.fn.body).all (calleePtrOk Cf) = true ∧
      noFA Cf.fn.body = true ∧ tgtOk Cf K.code = true ∧ jtdOk Cf K.E K.code = true ∧ loopShapeOkC Cf = true := by
  obtain ⟨hml, hb, ht, hc, hr, hp⟩ := h
  obtain ⟨-, hw⟩ := lwins_spec hb
  rw [← hml] at hw
  obtain ⟨c, args, hd, hl, hnz⟩ := tailL_spec ht
  set pre := slice Cf.fn.body 0 (Cf.fn.body.length - 2) with hpre
  have hbody : Cf.fn.body = pre ++ [.callIf c Cf.fn.name args, .ret []] := by
    rw [hpre, slice, List.drop_zero, Nat.sub_zero, ← hd, List.take_append_drop]
  simp only [winL, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hw
  obtain ⟨⟨hst, htop⟩, hmlE⟩ := hw
  -- each statement of the body
  have hall : ∀ s ∈ stmtsOf Cf.fn.body, (isBW s = true ∧ winP Cf s = true) ∨ s = .callIf c Cf.fn.name args ∨
      s = .ret [] := fun s hs ↦ by
    rw [hbody] at hs
    rcases stmts_loopB hs with hs | hs | hs
    · exact Or.inl (hst s hs)
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr hs)
  have hP : ∀ s ∈ stmtsOf Cf.fn.body, winP Cf s = true := fun s hs ↦ by
    rcases hall s hs with h | rfl | rfl
    · exact h.2
    · simp [winP, calleePtrOk, hnz]
    · simp [winP, calleePtrOk]
  have hBB : loopBB Cf.fn = true := by
    unfold loopBB
    rw [hbody]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      beq_self_eq_true, hl, Nat.beq_refl, Bool.true_and, List.reverse_reverse]
    exact List.all_eq_true.mpr fun s hs ↦ isBS_of_isBW (hst s hs).1
  have hML : matchLens Cf.fn.body = ml := by
    rw [hbody, matchLens_append, hmlE]
    simp [matchLens, stmtsOf, Bridge.stmtsSub]
  have hDL : dspLens Cf.fn.body = [] := by
    unfold dspLens
    rw [List.filterMap_eq_nil_iff]
    intro s hs
    cases s with
    | dispatch x fs a r => exact absurd hs (loopBB_noDsp hBB)
    | _ => rfl
  obtain ⟨-, htg, hjt⟩ := cwins_spec le_rfl hc
  rw [slice_all] at htg hjt
  refine ⟨hBB, stmtsOf_all_of fun s hs ↦ ?_, ?_, ?_, stmtsOf_all_of fun s hs ↦ ?_, stmtsOf_all_of fun s hs ↦ ?_,
    ?_, ?_, ?_⟩
  · rcases hall s hs with ⟨hbw, hp⟩ | rfl | rfl
    · cases s with
      | call g args' rets => simp only [winP, Bool.and_eq_true] at hp; exact hp.1.1.1
      | callIf => simp [isBW] at hbw
      | _ => rfl
    · simp
    · rfl
  · rw [hbody, List.all_append]
    simp only [Bool.and_eq_true, List.all_eq_true]
    refine ⟨htop, ?_⟩
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> rfl
  · simp only [Bool.or_eq_true]
    rcases Bool.or_eq_true_iff.mp hp with hp | hp
    swap
    · exact Or.inl hp
    right
    simp only [Bool.and_eq_true] at hp
    simp only [noPtrL, hp.1, hp.2, Bool.true_and]
    refine List.all_eq_true.mpr fun s hs ↦ ?_
    rcases hall s hs with ⟨hbw, hp⟩ | rfl | rfl
    · cases s with
      | call g args' rets => simp only [winP, Bool.and_eq_true] at hp; exact hp.1.1.2
      | callIf => simp [isBW] at hbw
      | _ => rfl
    · simp
    · rfl
  · have := hP s hs
    simp only [winP, Bool.and_eq_true] at this
    exact this.1.2
  · have := hP s hs
    cases s with
    | atom a =>
      cases a with
      | frameAddr p r => simp [winP] at this
      | _ => rfl
    | _ => rfl
  · rw [tgtOk, Exec.listSeq_eq, hML]; exact htg
  · rw [jtdOk, Exec.listSeq_eq, Exec.listSeq_eq, hML, hDL]; exact hjt
  · have e : loopShapeOkC Cf = ((loopShapeRest0 Cf && (stmtsOf Cf.fn.body).all fun s ↦ match s with
        | .callIf c _ _ => !Cf.X.nzAt (Cf.X.locAt c.idx)
        | _ => true) && hiRes Cf.frame.sig Cf.gl Cf.fn.params.length Cf.H.sig.ghosts Cf.H.res) := rfl
    rw [loopShapeRest, Bool.and_eq_true, Bool.and_eq_true] at hr
    rw [e, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨hr.1.1, List.all_eq_true.mpr fun s hs ↦ ?_⟩, hr.2⟩
    have := hP s hs
    cases s with
    | callIf c' g' a' => simp only [winP, Bool.and_eq_true] at this; simpa using this.2
    | _ => rfl

/-- **A long loop helper's residual divisors**: none (`loopShapeRest`), so `LoopOkC.nzrc`. -/
theorem nzr_of_wins {K : Mode.Cert} {Cf : CFun} {ml : List (ℕ × ℕ)} {cs : List (ℕ × List (ℕ × ℕ))}
    {ccs : List ℕ} (h : LoopWins K Cf ml cs ccs) : nzrOk Cf K.F.res K.code = true := by
  have hr := h.rest
  rw [loopShapeRest, Bool.and_eq_true, Bool.and_eq_true] at hr
  unfold nzrOk
  exact List.all_eq_true.mpr fun i _ ↦ by rw [trieNil_get hr.1.2]

end

end LeanVM.Guest.CoreMode
