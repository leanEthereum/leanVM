/-
  LeanVM.Guest.Local.Fold

  A walk of every position of a core body in pre-order, for the kernel, and what it shows: a
  state before each position, each statement's step taken from it with its context.
-/

module

public import LeanVM.Guest.Local.Pos

/-!
# The kernel's walk of positions

`foldL step ss c p st ends` visits the positions of block `ss` (starting at `p`, context `c`) in
pre-order, calling `step st q s c'` at each with its statement and context (`AtL`) and threading
the state. Contexts need the end of each arm, which the walk does not compute: it pops each
arm's end from `ends` (the arms in the order they start, which is pre-order) when it enters the
arm, and checks it when the arm ends. It is written with `Stmt.rec` and `List.rec` and binds
`Option` with its recursor, so the kernel reduces it a few steps per position.

`foldL_spec`: if the walk returns `(p', st', ends')`, then `p' = p + sizeL ss` and there are
states `f q`, `f p = st`, `f p' = st'`, with `step (f q) q s c' = some (f (q + 1))` wherever
`AtL c p ss q s c'`: the statements' checks are local, and their states a pre-order sequence.
-/

namespace LeanVM.Guest.Local

open LeanVM.Guest.Core

@[expose] public section

/-- `o`, then `k` of its value, by the recursor. -/
def bindO {α β : Type} (o : Option α) (k : α → Option β) : Option β :=
  Option.rec (motive := fun _ ↦ Option β) none k o

@[simp] theorem bindO_none {α β : Type} (k : α → Option β) : bindO none k = none := rfl
@[simp] theorem bindO_some {α β : Type} (a : α) (k : α → Option β) : bindO (some a) k = k a := rfl

theorem bindO_eq_some {α β : Type} {o : Option α} {k : α → Option β} {b : β} (h : bindO o k = some b) :
    ∃ a, o = some a ∧ k a = some b := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- `k n`, `n` evaluated first (the kernel would otherwise carry `n` as a growing term). -/
def seqN {β : Type} (n : ℕ) (k : ℕ → β) : β :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

@[simp] theorem seqN_eq {β : Type} (n : ℕ) (k : ℕ → β) : seqN n k = k n := by
  cases n <;> rfl

variable {St : Type}

/-- What a walk returns: the position after it, its state, the arm ends left. -/
abbrev FoldR (St : Type) := ℕ × St × List ℕ

/-- An arm's walk `r` from position `a` (arm of the branch at `t`), its end popped from `ends`
and checked. -/
noncomputable def armRun (r : Ctx → ℕ → St → List ℕ → Option (FoldR St)) (t a : ℕ) (st : St) (ends : List ℕ) :
    Option (FoldR St) :=
  List.rec (motive := fun _ ↦ Option (FoldR St)) none
    (fun e es _ ↦ bindO (r ⟨e, t, a⟩ a st es) fun x ↦ bif Nat.beq x.1 e then some x else none) ends

section Minors

variable (step : St → ℕ → Stmt → Ctx → Option St)

/-- A statement without blocks: its step. -/
noncomputable def leafF (s : Stmt) (c : Ctx) (p : ℕ) (st : St) (es : List ℕ) : Option (FoldR St) :=
  bindO (step st p s c) fun st ↦ seqN (p + 1) fun p' ↦ some (p', st, es)

/-- An `ite`: its step, then its zero and nonzero blocks as arms. -/
noncomputable def iteF (x : V) (z n : List Stmt) (rz rn : Ctx → ℕ → St → List ℕ → Option (FoldR St)) (c : Ctx)
    (p : ℕ) (st : St) (es : List ℕ) : Option (FoldR St) :=
  bindO (step st p (.ite x z n) c) fun st ↦
    bindO (armRun rz p (p + 1) st es) fun r ↦ armRun rn p r.1 r.2.1 r.2.2

/-- A `match`: its step, then its arms. -/
noncomputable def matchF (x : V) (arms : List (List Stmt)) (ra : ℕ → ℕ → St → List ℕ → Option (FoldR St)) (c : Ctx)
    (p : ℕ) (st : St) (es : List ℕ) : Option (FoldR St) :=
  bindO (step st p (.match_ x arms) c) fun st ↦ ra p (p + 1) st es

/-- A block's next statement, then the rest. -/
noncomputable def consF (rs rss : Ctx → ℕ → St → List ℕ → Option (FoldR St)) (c : Ctx) (p : ℕ) (st : St)
    (es : List ℕ) : Option (FoldR St) :=
  bindO (rs c p st es) fun r ↦ rss c r.1 r.2.1 r.2.2

/-- An arm, then the next arms. -/
noncomputable def armsF (rb : Ctx → ℕ → St → List ℕ → Option (FoldR St)) (rbs : ℕ → ℕ → St → List ℕ → Option (FoldR St))
    (t a : ℕ) (st : St) (es : List ℕ) : Option (FoldR St) :=
  bindO (armRun rb t a st es) fun r ↦ rbs t r.1 r.2.1 r.2.2

end Minors

/-- **The walk of a block.** -/
noncomputable def foldL (step : St → ℕ → Stmt → Ctx → Option St) (ss : List Stmt) :
    Ctx → ℕ → St → List ℕ → Option (FoldR St) :=
  Stmt.rec_1 (motive_1 := fun _ ↦ Ctx → ℕ → St → List ℕ → Option (FoldR St))
    (motive_2 := fun _ ↦ Ctx → ℕ → St → List ℕ → Option (FoldR St))
    (motive_3 := fun _ ↦ ℕ → ℕ → St → List ℕ → Option (FoldR St))
    (fun a ↦ leafF step (.atom a)) (fun x z n rz rn ↦ iteF step x z n rz rn)
    (fun x arms ra ↦ matchF step x arms ra)
    (fun f args rets ↦ leafF step (.call f args rets)) (fun c f args ↦ leafF step (.callIf c f args))
    (fun x fs args rets ↦ leafF step (.dispatch x fs args rets)) (fun vs ↦ leafF step (.ret vs))
    (fun _ p st es ↦ some (p, st, es)) (fun _ _ rs rss ↦ consF rs rss)
    (fun _ a st es ↦ some (a, st, es)) (fun _ _ rb rbs ↦ armsF rb rbs) ss

/-- The walk of a statement. -/
noncomputable def foldS (step : St → ℕ → Stmt → Ctx → Option St) (s : Stmt) :
    Ctx → ℕ → St → List ℕ → Option (FoldR St) :=
  Stmt.rec (motive_1 := fun _ ↦ Ctx → ℕ → St → List ℕ → Option (FoldR St))
    (motive_2 := fun _ ↦ Ctx → ℕ → St → List ℕ → Option (FoldR St))
    (motive_3 := fun _ ↦ ℕ → ℕ → St → List ℕ → Option (FoldR St))
    (fun a ↦ leafF step (.atom a)) (fun x z n rz rn ↦ iteF step x z n rz rn)
    (fun x arms ra ↦ matchF step x arms ra)
    (fun f args rets ↦ leafF step (.call f args rets)) (fun c f args ↦ leafF step (.callIf c f args))
    (fun x fs args rets ↦ leafF step (.dispatch x fs args rets)) (fun vs ↦ leafF step (.ret vs))
    (fun _ p st es ↦ some (p, st, es)) (fun _ _ rs rss ↦ consF rs rss)
    (fun _ a st es ↦ some (a, st, es)) (fun _ _ rb rbs ↦ armsF rb rbs) s

/-- The walk of a list of arms. -/
noncomputable def foldA (step : St → ℕ → Stmt → Ctx → Option St) (bs : List (List Stmt)) :
    ℕ → ℕ → St → List ℕ → Option (FoldR St) :=
  Stmt.rec_2 (motive_1 := fun _ ↦ Ctx → ℕ → St → List ℕ → Option (FoldR St))
    (motive_2 := fun _ ↦ Ctx → ℕ → St → List ℕ → Option (FoldR St))
    (motive_3 := fun _ ↦ ℕ → ℕ → St → List ℕ → Option (FoldR St))
    (fun a ↦ leafF step (.atom a)) (fun x z n rz rn ↦ iteF step x z n rz rn)
    (fun x arms ra ↦ matchF step x arms ra)
    (fun f args rets ↦ leafF step (.call f args rets)) (fun c f args ↦ leafF step (.callIf c f args))
    (fun x fs args rets ↦ leafF step (.dispatch x fs args rets)) (fun vs ↦ leafF step (.ret vs))
    (fun _ p st es ↦ some (p, st, es)) (fun _ _ rs rss ↦ consF rs rss)
    (fun _ a st es ↦ some (a, st, es)) (fun _ _ rb rbs ↦ armsF rb rbs) bs

section Eqns

variable (step : St → ℕ → Stmt → Ctx → Option St)

theorem foldL_nil : foldL step [] = fun _ p st es ↦ some (p, st, es) := rfl

theorem foldL_cons (s : Stmt) (ss : List Stmt) :
    foldL step (s :: ss) = consF (foldS step s) (foldL step ss) := rfl

theorem foldS_ite (x : V) (z n : List Stmt) :
    foldS step (.ite x z n) = iteF step x z n (foldL step z) (foldL step n) := rfl

theorem foldS_match (x : V) (arms : List (List Stmt)) :
    foldS step (.match_ x arms) = matchF step x arms (foldA step arms) := rfl

theorem foldA_nil : foldA step [] = fun _ a st es ↦ some (a, st, es) := rfl

theorem foldA_cons (b : List Stmt) (bs : List (List Stmt)) :
    foldA step (b :: bs) = armsF (foldL step b) (foldA step bs) := rfl

/-- A statement without blocks walks as its step. -/
theorem foldS_leaf (s : Stmt) (hs : ∀ x z n, s ≠ .ite x z n) (hm : ∀ x arms, s ≠ .match_ x arms) :
    foldS step s = leafF step s := by
  cases s with
  | ite x z n => exact absurd rfl (hs x z n)
  | match_ x arms => exact absurd rfl (hm x arms)
  | _ => rfl

end Eqns

/-! ## What the walk shows -/

section Spec

variable {step : St → ℕ → Stmt → Ctx → Option St}

theorem armRun_spec {r : Ctx → ℕ → St → List ℕ → Option (FoldR St)} {t a : ℕ} {st : St} {es : List ℕ}
    {x : FoldR St} (h : armRun r t a st es = some x) :
    ∃ e es0, es = e :: es0 ∧ x.1 = e ∧ r ⟨e, t, a⟩ a st es0 = some x := by
  cases es with
  | nil => cases h
  | cons e es0 =>
    obtain ⟨y, hy, hx⟩ := bindO_eq_some h
    cases hb : Nat.beq y.1 e
    · rw [hb] at hx; cases hx
    · rw [hb] at hx
      cases hx
      exact ⟨e, es0, rfl, Nat.eq_of_beq_eq_true hb, hy⟩

/-- States agreeing with `f` before `m` and with `g` from `m`. -/
def splice (f g : ℕ → St) (m : ℕ) (q : ℕ) : St := if q < m then f q else g q

theorem splice_lo {f g : ℕ → St} {m q : ℕ} (h : q < m) : splice f g m q = f q := by simp [splice, h]
theorem splice_hi {f g : ℕ → St} {m q : ℕ} (h : m ≤ q) : splice f g m q = g q := by
  simp [splice, Nat.not_lt.mpr h]

mutual
theorem foldS_spec : ∀ (s : Stmt) {c : Ctx} {p : ℕ} {st : St} {es : List ℕ} {x : FoldR St},
    foldS step s c p st es = some x → x.1 = p + size s ∧ ∃ f : ℕ → St, f p = st ∧ f x.1 = x.2.1 ∧
      step (f p) p s c = some (f (p + 1)) ∧
      ∀ q s' c', AtS p s q s' c' → step (f q) q s' c' = some (f (q + 1))
  | .ite y z n, c, p, st, es, x, h => by
      rw [foldS_ite] at h
      obtain ⟨st1, h1, h⟩ := bindO_eq_some h
      obtain ⟨r, hz, hn⟩ := bindO_eq_some h
      obtain ⟨ez, esz, rfl, hez, hz⟩ := armRun_spec hz
      obtain ⟨en, esn, hesn, hen, hn⟩ := armRun_spec hn
      obtain ⟨hz1, fz, hfz0, hfz1, hfz⟩ := foldL_spec z hz
      obtain ⟨hn1, fn, hfn0, hfn1, hfn⟩ := foldL_spec n hn
      have hr1 : r.1 = p + 1 + sizeL z := hz1
      rw [hez] at hz1
      have hx1 : x.1 = p + 1 + sizeL z + sizeL n := by rw [hn1, hr1]
      refine ⟨by rw [hx1]; simp only [size]; omega,
        splice (fun _ ↦ st) (splice fz fn (p + 1 + sizeL z)) (p + 1), splice_lo (by omega), ?_, ?_, ?_⟩
      · rw [splice_hi (by rw [hx1]; omega), splice_hi (by rw [hx1]; omega), hx1, ← hr1, ← hn1, hfn1]
      · rw [splice_lo (Nat.lt_succ_self p), splice_hi le_rfl]
        by_cases hzs : sizeL z = 0
        · rw [splice_hi (by omega), show p + 1 = r.1 by omega, hfn0]
          have : fz (p + 1) = r.2.1 := by rw [← hfz1, hr1, hzs]
          rw [← this, hfz0]; exact h1
        · rw [splice_lo (by omega), hfz0]; exact h1
      · intro q s' c' hq
        have hr := atS_range hq
        cases hq with
        | zero hq =>
          have hq' := atL_range hq
          rw [splice_hi (m := p + 1) (q := q) (by omega), splice_hi (m := p + 1) (q := q + 1) (by omega),
            splice_lo (m := p + 1 + sizeL z) (q := q) (by omega)]
          have := hfz q s' c' (by rw [hz1]; exact hq)
          rw [this]
          by_cases hb : q + 1 < p + 1 + sizeL z
          · rw [splice_lo hb]
          · rw [splice_hi (by omega), show q + 1 = r.1 by omega, hfn0, ← hfz1]
        | nonzero hq =>
          have hq' := atL_range hq
          rw [splice_hi (m := p + 1) (q := q) (by omega), splice_hi (m := p + 1) (q := q + 1) (by omega),
            splice_hi (m := p + 1 + sizeL z) (q := q) (by omega),
            splice_hi (m := p + 1 + sizeL z) (q := q + 1) (by omega)]
          refine hfn q s' c' ?_
          have he : en = p + 1 + sizeL z + sizeL n := by rw [← hen, hn1, hr1]
          rw [hr1, he]; exact hq
  | .match_ y arms, c, p, st, es, x, h => by
      rw [foldS_match] at h
      obtain ⟨st1, h1, h⟩ := bindO_eq_some h
      obtain ⟨ha1, fa, hfa0, hfa1, hfa⟩ := foldA_spec arms h
      refine ⟨by rw [ha1]; simp only [size]; omega, splice (fun _ ↦ st) fa (p + 1), splice_lo (by omega), ?_, ?_, ?_⟩
      · rw [splice_hi (by rw [ha1]; omega), hfa1]
      · rw [splice_lo (Nat.lt_succ_self p), splice_hi le_rfl, hfa0]; exact h1
      · intro q s' c' hq
        have hr := atS_range hq
        cases hq with
        | arm hq =>
          rw [splice_hi (m := p + 1) (q := q) (by omega), splice_hi (m := p + 1) (q := q + 1) (by omega)]
          exact hfa q s' c' hq
  | .atom a, c, p, st, es, x, h => leaf_spec h
  | .call .., c, p, st, es, x, h => leaf_spec h
  | .callIf .., c, p, st, es, x, h => leaf_spec h
  | .dispatch .., c, p, st, es, x, h => leaf_spec h
  | .ret _, c, p, st, es, x, h => leaf_spec h

theorem foldL_spec : ∀ (ss : List Stmt) {c : Ctx} {p : ℕ} {st : St} {es : List ℕ} {x : FoldR St},
    foldL step ss c p st es = some x → x.1 = p + sizeL ss ∧ ∃ f : ℕ → St, f p = st ∧ f x.1 = x.2.1 ∧
      ∀ q s c', AtL c p ss q s c' → step (f q) q s c' = some (f (q + 1))
  | [], c, p, st, es, x, h => by
      rw [foldL_nil] at h
      cases h
      exact ⟨by simp [sizeL], fun _ ↦ st, rfl, rfl, fun q s c' hq ↦ nomatch hq⟩
  | s :: ss, c, p, st, es, x, h => by
      rw [foldL_cons] at h
      obtain ⟨r, hs, hss⟩ := bindO_eq_some h
      obtain ⟨hs1, fs, hfs0, hfs1, hfsp, hfs⟩ := foldS_spec s hs
      obtain ⟨hss1, fss, hfss0, hfss1, hfss⟩ := foldL_spec ss hss
      have hpos := size_pos s
      refine ⟨by rw [hss1, hs1]; simp only [sizeL]; omega, splice fs fss r.1, by rw [splice_lo (by omega), hfs0],
        by rw [splice_hi (by rw [hss1]; omega), hfss1], ?_⟩
      have hb : fs r.1 = fss r.1 := by rw [hfs1, hfss0]
      intro q s' c' hq
      cases hq with
      | head =>
        rw [splice_lo (by omega)]
        by_cases h2 : p + 1 < r.1
        · rw [splice_lo h2]; exact hfsp
        · rw [splice_hi (by omega), show p + 1 = r.1 by omega, ← hb]
          rw [show p + 1 = r.1 by omega] at hfsp; exact hfsp
      | inside hq =>
        have := atS_range hq
        rw [splice_lo (by omega)]
        by_cases h2 : q + 1 < r.1
        · rw [splice_lo h2]; exact hfs q s' c' hq
        · rw [splice_hi (by omega), show q + 1 = r.1 by omega, ← hb]
          have := hfs q s' c' hq; rwa [show q + 1 = r.1 by omega] at this
      | tail hq =>
        have := atL_range hq
        rw [splice_hi (by omega), splice_hi (by omega)]
        exact hfss q s' c' (by rw [hs1]; exact hq)

theorem foldA_spec : ∀ (bs : List (List Stmt)) {t a : ℕ} {st : St} {es : List ℕ} {x : FoldR St},
    foldA step bs t a st es = some x → x.1 = a + sizeA bs ∧ ∃ f : ℕ → St, f a = st ∧ f x.1 = x.2.1 ∧
      ∀ q s c', AtA t a bs q s c' → step (f q) q s c' = some (f (q + 1))
  | [], t, a, st, es, x, h => by
      rw [foldA_nil] at h
      cases h
      exact ⟨by simp [sizeA], fun _ ↦ st, rfl, rfl, fun q s c' hq ↦ nomatch hq⟩
  | b :: bs, t, a, st, es, x, h => by
      rw [foldA_cons] at h
      obtain ⟨r, hb, hbs⟩ := bindO_eq_some h
      obtain ⟨e, es0, rfl, he, hb⟩ := armRun_spec hb
      obtain ⟨hb1, fb, hfb0, hfb1, hfb⟩ := foldL_spec b hb
      obtain ⟨hbs1, fbs, hfbs0, hfbs1, hfbs⟩ := foldA_spec bs hbs
      have hj : fb r.1 = fbs r.1 := by rw [hfb1, hfbs0]
      have he' : e = a + sizeL b := by rw [← he, hb1]
      refine ⟨by rw [hbs1, hb1]; simp only [sizeA]; omega, splice fb fbs r.1, ?_,
        by rw [splice_hi (by rw [hbs1]; omega), hfbs1], ?_⟩
      · by_cases h0 : a < r.1
        · rw [splice_lo h0, hfb0]
        · rw [splice_hi (by omega), show a = r.1 by omega, ← hj, ← show a = r.1 by omega, hfb0]
      · intro q s c' hq
        cases hq with
        | here hq =>
          have := atL_range hq
          rw [splice_lo (by omega)]
          have h2 := hfb q s c' (by rw [he']; exact hq)
          by_cases h3 : q + 1 < r.1
          · rw [splice_lo h3]; exact h2
          · rw [splice_hi (by omega), show q + 1 = r.1 by omega, ← hj, ← show q + 1 = r.1 by omega]; exact h2
        | next hq =>
          have := atA_range hq
          rw [splice_hi (by omega), splice_hi (by omega)]
          exact hfbs q s c' (by rw [hb1]; exact hq)

theorem leaf_spec {s : Stmt} {c : Ctx} {p : ℕ} {st : St} {es : List ℕ} {x : FoldR St}
    (h : leafF step s c p st es = some x) (hs : size s = 1 := by rfl)
    (hn : ∀ q s' c', ¬ AtS p s q s' c' := by intro q s' c' h; nomatch h) :
    x.1 = p + size s ∧ ∃ f : ℕ → St, f p = st ∧ f x.1 = x.2.1 ∧
      step (f p) p s c = some (f (p + 1)) ∧
      ∀ q s' c', AtS p s q s' c' → step (f q) q s' c' = some (f (q + 1)) := by
  obtain ⟨st1, h1, h⟩ := bindO_eq_some h
  rw [seqN_eq] at h
  cases h
  refine ⟨by rw [hs], splice (fun _ ↦ st) (fun _ ↦ st1) (p + 1), splice_lo (Nat.lt_succ_self p),
    splice_hi (by omega), by rw [splice_lo (Nat.lt_succ_self p), splice_hi le_rfl]; exact h1,
    fun q s' c' hq ↦ (hn q s' c' hq).elim⟩
end

/-- **The walk of a body**: from position `p` and context `c`, ending at `c.e` with no arm end
left, it visits every position, `c.e` being the block's exact end. -/
theorem fold_body {ss : List Stmt} {c : Ctx} {p : ℕ} {st st' : St} {es : List ℕ}
    (h : foldL step ss c p st es = some (c.e, st', [])) : c.e = p + sizeL ss ∧
      ∃ f : ℕ → St, f p = st ∧ f c.e = st' ∧ ∀ q s c', AtL c p ss q s c' → step (f q) q s c' = some (f (q + 1)) :=
  foldL_spec ss h

end Spec

/-! ## Walks of pieces -/

section Append

variable (step : St → ℕ → Stmt → Ctx → Option St)

/-- **A block's walk in two pieces.** -/
theorem foldL_append : ∀ (l₁ l₂ : List Stmt) (c : Ctx) (p : ℕ) (st : St) (es : List ℕ),
    foldL step (l₁ ++ l₂) c p st es = bindO (foldL step l₁ c p st es) fun r ↦ foldL step l₂ c r.1 r.2.1 r.2.2
  | [], l₂, c, p, st, es => rfl
  | s :: l₁, l₂, c, p, st, es => by
      rw [List.cons_append, foldL_cons, foldL_cons]
      unfold consF
      cases foldS step s c p st es with
      | none => rfl
      | some r => exact foldL_append l₁ l₂ c r.1 r.2.1 r.2.2

/-- **A list of arms' walk in two pieces.** -/
theorem foldA_append : ∀ (b₁ b₂ : List (List Stmt)) (t a : ℕ) (st : St) (es : List ℕ),
    foldA step (b₁ ++ b₂) t a st es = bindO (foldA step b₁ t a st es) fun r ↦ foldA step b₂ t r.1 r.2.1 r.2.2
  | [], b₂, t, a, st, es => rfl
  | b :: b₁, b₂, t, a, st, es => by
      rw [List.cons_append, foldA_cons, foldA_cons]
      unfold armsF
      cases armRun (foldL step b) t a st es with
      | none => rfl
      | some r => exact foldA_append b₁ b₂ t r.1 r.2.1 r.2.2

end Append

end
end LeanVM.Guest.Local
