/-
  LeanVM.Guest.Backend.Complete.FrameNew

  A block's placement places no value but those its trace makes, the frame addresses among its
  atoms apart.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameLocs
public import LeanVM.Guest.Backend.Complete.FrameBlock

/-!
# The values a block places

Every placement step places no value (`RAt`, the relation `RR` from the step's start), but three:
an `alloc` event of the flush, whose values are the event's (`flushN_r`); an atom made lazily
(`pooled`, `bindTo` under `isLazy`), whose value is the lazy one of the atom's start; and a
frame address shifted as a value, whose pointer is the atom's. So a block from a state with no
lazy value places only the values the trace left at its start makes and the frame addresses
among its atoms (`placeNew : PlaceNew ctx`), and the trace left only shrinks.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- The pointer of a frame address among the atoms `L`. -/
def FA (L : List Atom) (v : V) : Prop := ∃ run, Atom.frameAddr v run ∈ L

theorem FA.self {p : V} {run : List V} : FA [Atom.frameAddr p run] p :=
  ⟨run, List.mem_singleton_self _⟩

theorem FA.mono {L L' : List Atom} {v : V} (h : FA L v) (hL : ∀ a ∈ L, a ∈ L') : FA L' v :=
  let ⟨run, hr⟩ := h; ⟨run, hL _ hr⟩

section R

variable {ctx : Ctx} {S : V → Prop} {α β : Type}

/-- Every value placed from `st` to `st'` was placed, made by an event left at `st`, the value made
lazily at `st`, or one `S` allows; the events left only shrink; a lazily made value is one made
by an event left at `st` or the one there; the shared tables only grow. -/
def RR (S : V → Prop) (st st' : St) : Prop :=
  (∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf st.rest ∨
    (∃ k, st.lazy = some (v, k)) ∨ S v) ∧
  (∀ v ∈ allocsOf st'.rest, v ∈ allocsOf st.rest) ∧
  (∀ v k, st'.lazy = some (v, k) → v ∈ allocsOf st.rest ∨ st.lazy = some (v, k)) ∧
  ∀ x ∈ st.tables.shared, x ∈ st'.tables.shared

theorem RR.refl (st : St) : RR S st st :=
  ⟨fun _ h => Or.inl h, fun _ h => h, fun _ _ h => Or.inr h, fun _ h => h⟩

theorem RR.trans {st₁ st₂ st₃ : St} (h₁ : RR S st₁ st₂) (h₂ : RR S st₂ st₃) : RR S st₁ st₃ := by
  obtain ⟨a₁, b₁, c₁, d₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂⟩ := h₂
  refine ⟨fun v h => ?_, fun v h => b₁ v (b₂ v h), fun v k h => ?_, fun x h => d₂ x (d₁ x h)⟩
  · rcases a₂ v h with h | h | ⟨k, h⟩ | h
    · exact a₁ v h
    · exact Or.inr (Or.inl (b₁ v h))
    · rcases c₁ v k h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨k, h⟩))
    · exact Or.inr (Or.inr (Or.inr h))
  · rcases c₂ v k h with h | h
    · exact Or.inl (b₁ v h)
    · exact c₁ v k h

theorem RR.mono {S' : V → Prop} {st st' : St} (h : RR S st st') (hS : ∀ v, S v → S' v) :
    RR S' st st' :=
  ⟨fun v hv => (h.1 v hv).imp_right fun h' => h'.imp_right fun h'' => h''.imp_right (hS v),
    h.2.1, h.2.2.1, h.2.2.2⟩

/-- Every success of `m` from `st` is `RR S` of `st`. -/
def RAt (S : V → Prop) (ctx : Ctx) (st : St) (m : P α) : Prop :=
  wpP m ctx st fun _ st' => RR S st st'

variable {st : St}

theorem RAt.pure {a : α} : RAt S ctx st (Pure.pure a) := wp_pure.mpr (RR.refl st)

theorem RAt.fail {msg : String} : RAt S ctx st (failP msg : P α) := wp_failP

theorem RAt.fail_bind {msg : String} {f : α → P β} :
    RAt S ctx st ((failP msg : P α) >>= f) := wp_bind.mpr wp_failP

theorem RAt.bind {m : P α} {f : α → P β} (hm : RAt S ctx st m)
    (hf : ∀ a st', RR S st st' → RAt S ctx st' (f a)) : RAt S ctx st (m >>= f) :=
  wp_bind.mpr (wp_mono hm fun a st' h => wp_mono (hf a st' h) fun _ _ h' => h.trans h')

theorem RAt.get_bind {f : St → P β} (h : RAt S ctx st (f st)) : RAt S ctx st (get >>= f) :=
  wp_bind.mpr (wp_get.mpr h)

theorem RAt.read_bind {f : Ctx → P β} (h : RAt S ctx st (f ctx)) :
    RAt S ctx st (read >>= f) := wp_bind.mpr (wp_read.mpr h)

theorem RAt.peek_bind {f : Option Event → P β} (h : RAt S ctx st (f st.rest.head?)) :
    RAt S ctx st (peek >>= f) := wp_bind.mpr (wp_peek.mpr h)

theorem RAt.guard {c : Prop} [Decidable c] {msg : String} {f : PUnit → P β}
    (h : ¬c → RAt S ctx st (f PUnit.unit)) :
    RAt S ctx st (if c then failP msg >>= f else f PUnit.unit) := by
  split
  · exact RAt.fail_bind
  · next hc => exact h hc

theorem RAt.mod {g : St → St} (h : RR S st (g st)) : RAt S ctx st (modify g) :=
  wp_modify.mpr h

theorem RAt.mod_bind {g : St → St} {f : PUnit → P β} (h : RR S st (g st))
    (hf : RAt S ctx (g st) (f ⟨⟩)) : RAt S ctx st (modify g >>= f) :=
  wp_bind.mpr (wp_modify.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem RAt.modG {g : St → α × St} (h : RR S st (g st).2) :
    RAt S ctx st (modifyGet g) := wp_modifyGet.mpr h

theorem RAt.modG_bind {g : St → α × St} {f : α → P β} (h : RR S st (g st).2)
    (hf : RAt S ctx (g st).2 (f (g st).1)) : RAt S ctx st (modifyGet g >>= f) :=
  wp_bind.mpr (wp_modifyGet.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem RAt.setS {s : St} (h : RR S st s) : RAt S ctx st (set s : P PUnit) := wp_set.mpr h

theorem RAt.setS_bind {s : St} {f : PUnit → P β} (h : RR S st s) (hf : RAt S ctx s (f ⟨⟩)) :
    RAt S ctx st (set s >>= f) :=
  wp_bind.mpr (wp_set.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem RAt.discard {m : P α} (h : RAt S ctx st m) : RAt S ctx st (Functor.discard m) := by
  rw [Functor.discard, map_const, Function.comp_apply, map_eq_pure_bind]
  exact RAt.bind h fun _ _ _ => RAt.pure

theorem rR_same {s : St} (hl : s.locs = st.locs) (hr : s.rest = st.rest)
    (hz : s.lazy = st.lazy) (ht : s.tables.shared = st.tables.shared) : RR S st s :=
  ⟨fun _ h => Or.inl (by rwa [hl] at h), fun _ h => by rwa [hr] at h,
    fun _ _ h => Or.inr (by rwa [hz] at h), fun _ h => by rw [ht]; exact h⟩

theorem rR_none {s : St} (hl : s.locs = st.locs) (hr : s.rest = st.rest)
    (hz : s.lazy = none) (ht : s.tables.shared = st.tables.shared) : RR S st s :=
  ⟨fun _ h => Or.inl (by rwa [hl] at h), fun _ h => by rwa [hr] at h,
    fun _ _ h => (by rw [hz] at h; cases h), fun _ h => by rw [ht]; exact h⟩

theorem allocsOf_tail {v : V} : ∀ {l : List Event}, v ∈ allocsOf l.tail → v ∈ allocsOf l
  | [], h => h
  | e :: r, h => by
      simp only [List.tail_cons] at h
      simp only [allocsOf, List.flatMap_cons, List.mem_append] at h ⊢
      exact Or.inr h

theorem rR_tail {s : St} (hl : s.locs = st.locs) (hr : s.rest = st.rest.tail)
    (hz : s.lazy = st.lazy) (ht : s.tables.shared = st.tables.shared) : RR S st s :=
  ⟨fun _ h => Or.inl (by rwa [hl] at h), fun _ h => allocsOf_tail (by rwa [hr] at h),
    fun _ _ h => Or.inr (by rwa [hz] at h), fun _ h => by rw [ht]; exact h⟩

theorem RAt.mono {S' : V → Prop} {α : Type} {m : P α} (h : RAt S ctx st m)
    (hS : ∀ v, S v → S' v) : RAt S' ctx st m := wp_mono h fun _ _ h' => h'.mono hS

theorem forM_r {γ : Type} {f : γ → P PUnit} (hf : ∀ b st, RAt S ctx st (f b)) :
    ∀ (l : List γ) (st : St), RAt S ctx st (l.forM f)
  | [], _ => RAt.pure
  | b :: l, st => by
      show RAt S ctx st (f b >>= fun _ => l.forM f)
      exact RAt.bind (hf b st) fun _ st' _ => forM_r hf l st'

theorem mapM_r {γ δ : Type} {f : γ → P δ} (hf : ∀ b st, RAt S ctx st (f b)) :
    ∀ (l : List γ) (st : St), RAt S ctx st (l.mapM f)
  | [], _ => by rw [List.mapM_nil]; exact RAt.pure
  | b :: l, st => by
      rw [List.mapM_cons]
      exact RAt.bind (hf b st) fun _ st' _ => RAt.bind (mapM_r hf l st') fun _ _ _ =>
        RAt.pure

theorem optionMapM_r {γ δ : Type} {f : γ → P δ} (hf : ∀ b st, RAt S ctx st (f b))
    (o : Option γ) (st : St) : RAt S ctx st (o.mapM f) := by
  cases o with
  | none => exact RAt.pure
  | some v =>
    rw [Option.mapM, map_eq_pure_bind]
    exact RAt.bind (hf v st) fun _ _ _ => RAt.pure

end R

/-- A primitive already shown to be `RR S` of its start. -/
syntax "r_prim" : tactic

set_option hygiene false in
macro_rules | `(tactic| r_prim) => `(tactic| first
  | with_reducible refine RAt.bind fresh_r fun _ _ _ => ?_
  | with_reducible exact fresh_r
  | with_reducible refine RAt.bind pushHint_r fun _ _ _ => ?_
  | with_reducible exact pushHint_r
  | with_reducible refine RAt.bind takeHints_r fun _ _ _ => ?_
  | with_reducible exact takeHints_r
  | with_reducible refine RAt.bind push_r fun _ _ _ => ?_
  | with_reducible exact push_r
  | with_reducible refine RAt.bind emitOp_r fun _ _ _ => ?_
  | with_reducible exact emitOp_r
  | with_reducible refine RAt.bind constCell_r fun _ _ _ => ?_
  | with_reducible exact constCell_r
  | with_reducible refine RAt.bind oneCell_r fun _ _ _ => ?_
  | with_reducible exact oneCell_r
  | with_reducible refine RAt.bind zeroCell_r fun _ _ _ => ?_
  | with_reducible exact zeroCell_r
  | with_reducible refine RAt.bind mulCell_r fun _ _ _ => ?_
  | with_reducible exact mulCell_r
  | with_reducible refine RAt.bind emitDeref_r fun _ _ _ => ?_
  | with_reducible exact emitDeref_r
  | with_reducible refine RAt.bind selfFp_r fun _ _ _ => ?_
  | with_reducible exact selfFp_r
  | with_reducible refine RAt.bind materialize_r fun _ _ _ => ?_
  | with_reducible exact materialize_r
  | with_reducible refine RAt.bind cellAt_r fun _ _ _ => ?_
  | with_reducible exact cellAt_r
  | with_reducible refine RAt.bind cellOf_r fun _ _ _ => ?_
  | with_reducible exact cellOf_r
  | with_reducible refine RAt.bind factor_r fun _ _ _ => ?_
  | with_reducible exact factor_r
  | with_reducible refine RAt.bind pointer_r fun _ _ _ => ?_
  | with_reducible exact pointer_r
  | with_reducible refine RAt.bind pooledCell_r fun _ _ _ => ?_
  | with_reducible exact pooledCell_r
  | with_reducible refine RAt.bind isLazy_r fun _ _ _ => ?_
  | with_reducible exact isLazy_r
  | with_reducible refine RAt.bind isSelfFp_r fun _ _ _ => ?_
  | with_reducible exact isSelfFp_r
  | with_reducible refine RAt.bind advance_r fun _ _ _ => ?_
  | with_reducible exact advance_r
  | with_reducible refine RAt.bind expect_r fun _ _ _ => ?_
  | with_reducible exact expect_r
  | with_reducible refine RAt.bind endStmt_r fun _ _ _ => ?_
  | with_reducible exact endStmt_r
  | with_reducible refine RAt.bind spongeInPlace_r fun _ _ _ => ?_
  | with_reducible exact spongeInPlace_r
  | with_reducible refine RAt.bind flushN_r fun _ _ _ => ?_
  | with_reducible exact flushN_r
  | with_reducible refine RAt.bind flush_r fun _ _ _ => ?_
  | with_reducible exact flush_r
  | with_reducible refine RAt.bind beginStmt_r fun _ _ _ => ?_
  | with_reducible exact beginStmt_r
  | with_reducible refine RAt.bind destBits_r fun _ _ _ => ?_
  | with_reducible exact destBits_r
  | with_reducible refine RAt.bind placeHint_r fun _ _ _ => ?_
  | with_reducible exact placeHint_r
  | with_reducible refine RAt.bind allocTable_r fun _ _ _ => ?_
  | with_reducible exact allocTable_r
  | with_reducible refine RAt.bind sharedTable_r fun _ _ _ => ?_
  | with_reducible exact sharedTable_r
  | with_reducible refine RAt.bind loopCount_r fun _ _ _ => ?_
  | with_reducible exact loopCount_r
  | with_reducible refine RAt.bind placeCall_r fun _ _ _ => ?_
  | with_reducible exact placeCall_r
  | with_reducible refine RAt.bind matchCells_r fun _ _ _ => ?_
  | with_reducible exact matchCells_r)

/-- One step of a walk that places no value. -/
macro "r_step" : tactic => `(tactic| first
  | with_reducible exact RAt.pure
  | with_reducible exact RAt.fail
  | with_reducible exact RAt.fail_bind
  | with_reducible refine RAt.get_bind ?_
  | with_reducible refine RAt.read_bind ?_
  | with_reducible refine RAt.peek_bind ?_
  | with_reducible refine RAt.guard fun _ => ?_
  | with_reducible refine RAt.mod_bind ?_ ?_
  | with_reducible refine RAt.modG_bind ?_ ?_
  | with_reducible refine RAt.setS_bind ?_ ?_
  | with_reducible refine RAt.mod ?_
  | with_reducible refine RAt.modG ?_
  | with_reducible refine RAt.setS ?_
  | exact rR_same rfl rfl rfl rfl
  | exact rR_none rfl rfl rfl rfl
  | exact rR_tail rfl rfl rfl rfl
  | exact RR.refl _
  | with_reducible refine RAt.bind (forM_r ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine RAt.bind (mapM_r ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine RAt.bind (optionMapM_r ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine RAt.bind (‹∀ st, RAt _ _ st _› _) fun _ _ _ => ?_
  | with_reducible exact ‹∀ st, RAt _ _ st _› _
  | with_reducible refine RAt.discard ?_
  | with_reducible refine RAt.bind (RAt.discard ?_) fun _ _ _ => ?_
  | r_prim
  | dsimp only
  | rw [pure_bind]
  | split)

macro "r_straight" : tactic => `(tactic| repeat' r_step)


section RPrims

variable {ctx : Ctx} {S : V → Prop} {st : St}

theorem fresh_r : RAt S ctx st fresh := by
  unfold fresh
  exact RAt.modG (rR_same rfl rfl rfl rfl)


theorem pushHint_r {h : LHint} : RAt S ctx st (pushHint h) := by
  unfold pushHint
  r_straight


theorem takeHints_r  : RAt S ctx st (takeHints) := by
  unfold takeHints
  r_straight


theorem push_r {s : PStmt} : RAt S ctx st (push s) := by
  unfold push
  r_straight


theorem emitOp_r {o : LOp} : RAt S ctx st (emitOp o) := by
  unfold emitOp
  r_straight


theorem constCell_r {k : ℕ × ℕ} : RAt S ctx st (constCell k) := by
  unfold constCell
  r_straight


theorem oneCell_r  : RAt S ctx st (oneCell) := by
  unfold oneCell
  r_straight


theorem zeroCell_r  : RAt S ctx st (zeroCell) := by
  unfold zeroCell
  r_straight


theorem mulCell_r {a b : Cell} : RAt S ctx st (mulCell a b) := by
  unfold mulCell
  r_straight


theorem emitDeref_r {p off d : Cell} : RAt S ctx st (emitDeref p off d) := by
  unfold emitDeref
  r_straight


theorem selfFp_r  : RAt S ctx st (selfFp) := by
  unfold selfFp
  r_straight


theorem materialize_r {c e : Cell} : RAt S ctx st (materialize c e) := by
  unfold materialize
  r_straight


theorem cellAt_r {v : V} : RAt S ctx st (cellAt v) := by
  unfold cellAt
  r_straight


theorem cellOf_r {v : V} : RAt S ctx st (cellOf v) := by
  unfold cellOf
  r_straight


theorem factor_r {v : V} : RAt S ctx st (factor v) := by
  unfold factor
  r_straight


theorem pointer_r {p : V} {off : ℕ} : RAt S ctx st (pointer p off) := by
  unfold pointer
  r_straight


theorem pooledCell_r {find : Scope → Option Cell} {learn : Cell → Scope → Scope} {mk : Cell → LOp} : RAt S ctx st (pooledCell find learn mk) := by
  unfold pooledCell
  r_straight


theorem isLazy_r {v : V} {k : Kind} : RAt S ctx st (isLazy v k) := by
  unfold isLazy
  r_straight


theorem isSelfFp_r {n : Cell} : RAt S ctx st (isSelfFp n) := by
  unfold isSelfFp
  r_straight


theorem advance_r  : RAt S ctx st (advance) := by
  unfold advance
  r_straight


theorem expect_r {e : Event → Bool} {what : String} : RAt S ctx st (expect e what) := by
  unfold expect
  r_straight


theorem endStmt_r  : RAt S ctx st (endStmt) := by
  unfold endStmt
  r_straight


theorem spongeInPlace_r {vs : List V} {up : List Stmt} : RAt S ctx st (spongeInPlace vs up) := by
  unfold spongeInPlace
  r_straight


set_option maxHeartbeats 2000000 in

/-- What an `alloc` event's placement does: places only its values, keeps the trace, and makes
lazy only one of them. -/
def NewA (vs : List V) (st st' : St) : Prop :=
  (∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ vs) ∧ st'.rest = st.rest ∧
    (∀ v k, st'.lazy = some (v, k) → v ∈ vs ∨ st.lazy = some (v, k)) ∧
    st'.tables.shared = st.tables.shared

theorem bindRun_new (vs : List V) (base : Cell) :
    wpP (bindRun vs base) ctx st fun _ s => NewA vs st s := by
  unfold bindRun
  refine wp_mono (bindRun_wp (ctx := ctx) base vs 0 st) fun _ s ⟨he, _, hnew, _⟩ => ?_
  have hz : s.lazy = st.lazy := (congrArg St.lazy he).trans rfl
  refine ⟨fun v hv => ?_, (congrArg St.rest he).trans rfl, fun v k h => Or.inr (by rw [← hz]; exact h),
    (congrArg (fun s : St => s.tables.shared) he).trans rfl⟩
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hv
  rcases hnew v x hx with h | h
  · exact Or.inl (by rw [h]; simp)
  · exact Or.inr h

theorem takeRun_new (vs : List V) : wpP (takeRun vs) ctx st fun _ s => NewA vs st s := by
  unfold takeRun
  exact wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_mono (bindRun_new vs _) fun _ _ h₁ =>
    wp_modify.mpr h₁)))

theorem spongeInPlace_same {vs : List V} {up : List Stmt} :
    wpP (spongeInPlace vs up) ctx st fun _ s => s = st := by
  unfold spongeInPlace
  refine wp_bind.mpr (wp_get.mpr ?_)
  dsimp only
  split <;> exact wp_pure.mpr rfl

theorem onAlloc_new (vs : List V) (kind : Kind) (up : List Stmt) :
    wpP (onAlloc vs kind up) ctx st fun _ s => NewA vs st s := by
  have hsame : NewA vs st st := ⟨fun _ h => Or.inl h, rfl, fun _ _ h => Or.inr h, rfl⟩
  unfold onAlloc
  cases kind
  all_goals dsimp only
  all_goals first
    | exact takeRun_new vs
    | exact wp_pure.mpr hsame
    | exact wp_bind.mpr (wp_read.mpr (bindRun_new vs _))
    | exact wp_bind.mpr (wp_mono (takeRun_new vs) fun _ _ h => wp_modify.mpr h)
    | exact wp_modify.mpr ⟨fun _ h => Or.inl h, rfl, fun v k h => Or.inl (by
        cases vs with
        | nil => simp at h
        | cons a t =>
          simp only [List.head?_cons, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1]
          exact List.mem_cons_self), rfl⟩
    | (refine wp_bind.mpr (wp_mono spongeInPlace_same fun r s hs => ?_)
       subst hs
       split
       · exact wp_bind.mpr (wp_mono (bindRun_new vs _) fun _ _ h => wp_modify.mpr h)
       · exact takeRun_new vs)

theorem mem_allocsOf_head {l : List Event} {vs : List V} {k : Kind} {v : V}
    (h : l.head? = some (.alloc vs k)) (hv : v ∈ vs) : v ∈ allocsOf l := by
  cases l with
  | nil => cases h
  | cons e r =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    simp only [allocsOf, List.flatMap_cons, List.mem_append]
    exact Or.inl hv

theorem rR_alloc {vs : List V} {kind : Kind} {s : St}
    (heq : st.rest.head? = some (.alloc vs kind))
    (h : NewA vs { st with rest := st.rest.tail } s) : RR S st s := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun v hv => ?_, fun v hv => allocsOf_tail (by rwa [h2] at hv), fun v k hk => ?_,
    fun x hx => by rw [h4]; exact hx⟩
  · rcases h1 v hv with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (mem_allocsOf_head heq h))
  · rcases h3 v k hk with h | h
    · exact Or.inl (mem_allocsOf_head heq h)
    · exact Or.inr h

/-- **A flush** places the values of the `alloc` events it passes, and makes lazy one of them. -/
theorem flushN_r {up : List Stmt} : ∀ {fuel : ℕ} {st : St}, RAt S ctx st (flushN up fuel)
  | 0, _ => by unfold flushN; exact RAt.pure
  | fuel + 1, st => by
      have ih : ∀ st, RAt S ctx st (flushN up fuel) := fun _ => flushN_r
      unfold flushN advance
      refine RAt.peek_bind ?_
      split
      · next vs kind heq =>
        exact wp_bind.mpr (wp_modify.mpr (wp_bind.mpr (wp_mono (onAlloc_new vs kind up)
          fun _ s₂ h₂ => wp_mono (ih s₂) fun _ _ h₃ => (rR_alloc heq h₂).trans h₃)))
      all_goals repeat' (first | exact ih _ | r_step)


theorem flush_r {up : List Stmt} : RAt S ctx st (flush up) := by
  unfold flush
  r_straight

theorem beginStmt_r {up : List Stmt} : RAt S ctx st (beginStmt up) := by
  unfold beginStmt
  r_straight

theorem destBits_r {d : Dest} : RAt S ctx st (destBits d) := by
  unfold destBits
  r_straight

set_option maxHeartbeats 2000000 in
theorem placeHint_r {h : Hint} : RAt S ctx st (placeHint h) := by
  have hc : ∀ (b : V) st, RAt S ctx st (cellOf b) := fun _ _ => cellOf_r
  have ha : ∀ (b : V) st, RAt S ctx st (cellAt b) := fun _ _ => cellAt_r
  cases h <;> unfold placeHint <;> r_straight

theorem allocTable_r {n : ℕ} : RAt S ctx st (allocTable n) := by
  unfold allocTable
  r_straight

theorem sharedTable_r {fs : List String} : RAt S ctx st (sharedTable fs) := by
  unfold sharedTable
  refine RAt.get_bind ?_
  split
  · exact RAt.pure
  · exact RAt.setS_bind ⟨fun _ h => Or.inl h, fun _ h => h, fun _ _ h => Or.inr h,
      fun _ h => List.mem_cons_of_mem _ h⟩ RAt.pure

theorem loopCount_r {f : String} {args : List V} {cells : List Cell} :
    RAt S ctx st (loopCount f args cells) := by
  unfold loopCount
  r_straight

theorem placeCall_r {f : String} {argVs : List V} {args rets : List Cell} {cond : Option Cell}
    {tail : Bool} : RAt S ctx st (placeCall f argVs args rets cond tail) := by
  unfold placeCall
  r_straight

theorem matchCells_r {x : V} {rest : List Stmt} {chained : Bool} :
    RAt S ctx st (matchCells x rest chained) := by
  unfold matchCells
  r_straight


end RPrims

/-! ## Atoms -/

section Atoms

variable {ctx : Ctx} {S : V → Prop} {β : Type}

/-- From `s`, every success of `m` is `RR S` of `st₀`, given `s` is. -/
def RF (S : V → Prop) (st₀ : St) (ctx : Ctx) {α : Type} (s : St) (m : P α) : Prop :=
  RR S st₀ s → wpP m ctx s fun _ s'' => RR S st₀ s''

theorem RF.start {α : Type} {st : St} {m : P α} (h : RF S st ctx st m) : RAt S ctx st m :=
  h (RR.refl st)

theorem RF.bind {α : Type} {st₀ s : St} {m : P α} {f : α → P β} (hm : RAt S ctx s m)
    (hf : ∀ a s', RF S st₀ ctx s' (f a)) : RF S st₀ ctx s (m >>= f) := fun hs =>
  wp_bind.mpr (wp_mono hm fun a s' h => hf a s' (hs.trans h))

theorem RF.last {α : Type} {st₀ s : St} {m : P α} (hm : RAt S ctx s m) : RF S st₀ ctx s m :=
  fun hs => wp_mono hm fun _ _ h => hs.trans h

theorem RF.get_bind {st₀ s : St} {f : St → P β} (h : RF S st₀ ctx s (f s)) :
    RF S st₀ ctx s (get >>= f) := fun hs => wp_bind.mpr (wp_get.mpr (h hs))

theorem RF.read_bind {st₀ s : St} {f : Ctx → P β} (h : RF S st₀ ctx s (f ctx)) :
    RF S st₀ ctx s (read >>= f) := fun hs => wp_bind.mpr (wp_read.mpr (h hs))

theorem RF.fail {α : Type} {st₀ s : St} {msg : String} : RF S st₀ ctx s (failP msg : P α) :=
  fun _ => wp_failP

theorem RF.fail_bind {α : Type} {st₀ s : St} {msg : String} {f : α → P β} :
    RF S st₀ ctx s ((failP msg : P α) >>= f) := fun _ => wp_bind.mpr wp_failP

theorem RAt.isLazy_bind {st : St} {v : V} {k : Kind} {f : Bool → P β}
    (h : ∀ b, (b = true → ∃ k', st.lazy = some (v, k')) → RF S st ctx st (f b)) :
    RAt S ctx st (isLazy v k >>= f) := by
  unfold isLazy
  exact wp_bind.mpr (wp_bind.mpr (wp_get.mpr (wp_pure.mpr
    ((h _ fun hb => ⟨k, by simpa using hb⟩) (RR.refl st)))))

theorem RR.bindTo {st₀ s : St} {d : V} {l : Loc} (hs : RR S st₀ s)
    (hd : (∃ k, st₀.lazy = some (d, k)) ∨ S d) :
    RR S st₀ { s with locs := s.locs.insert d l } := by
  obtain ⟨h1, h2, h3, h4⟩ := hs
  refine ⟨fun v hv => ?_, h2, h3, h4⟩
  by_cases hvd : v = d
  · subst hvd
    rcases hd with hd | hd
    · exact Or.inr (Or.inr (Or.inl hd))
    · exact Or.inr (Or.inr (Or.inr hd))
  · refine h1 v ?_
    simpa [KMap.getElem?_insert, hvd] using hv

theorem bindTo_after' {st₀ s : St} {d : V} {l : Loc}
    (hd : (∃ k, st₀.lazy = some (d, k)) ∨ S d) : RF S st₀ ctx s (bindTo d l) := by
  intro hs
  unfold bindTo
  refine wp_bind.mpr (wp_get.mpr ?_)
  split
  · exact wp_bind.mpr wp_failP
  · exact wp_modify.mpr (hs.bindTo hd)

theorem bindTo_after {st₀ s : St} {d : V} {l : Loc} {b : Bool}
    (hl : b = true → ∃ k, st₀.lazy = some (d, k)) (hb : b = true) : RF S st₀ ctx s (bindTo d l) :=
  bindTo_after' (Or.inl (hl hb))

theorem bindTo_afterS {st₀ s : St} {d : V} {l : Loc} (hS : S d) : RF S st₀ ctx s (bindTo d l) :=
  bindTo_after' (Or.inr hS)

theorem bindTo_rS {s : St} {d : V} {l : Loc} (hS : S d) : RAt S ctx s (bindTo d l) :=
  RF.start (bindTo_afterS hS)

theorem pooled_after {st₀ s : St} {d : V} {find : Scope → Option Cell}
    {learn : Cell → Scope → Scope} {mk : Cell → LOp} {b : Bool}
    (hl : b = true → ∃ k, st₀.lazy = some (d, k)) (hb : b = true) :
    RF S st₀ ctx s (pooled d find learn mk) := by
  unfold pooled
  exact RF.bind pooledCell_r fun _ _ => bindTo_after hl hb

/-- One step of an atom's walk: a step that places no value, or the atom's own `bindTo`. -/
macro "pa_step" : tactic => `(tactic| first
  | (with_reducible apply bindTo_after <;> assumption)
  | (with_reducible apply pooled_after <;> assumption)
  | (with_reducible apply bindTo_afterS; exact FA.self)
  | (with_reducible apply bindTo_rS; exact FA.self)
  | with_reducible exact RF.fail
  | with_reducible exact RF.fail_bind
  | with_reducible refine RF.get_bind ?_
  | with_reducible refine RF.read_bind ?_
  | with_reducible refine RAt.isLazy_bind fun _ _ => ?_
  | with_reducible refine RF.bind ?_ fun _ _ => ?_
  | split
  | with_reducible refine RF.last ?_
  | with_reducible exact mapM_r ‹_› _ _
  | r_step)

set_option maxHeartbeats 1000000 in
theorem place_const_r {st : St} (d : V) (c : E) : RAt (FA [.const d c]) ctx st (placeAtom (.const d c)) := by
  have hc : ∀ (b : V) st, RAt (FA [.const d c]) ctx st (cellOf b) := fun _ _ => cellOf_r
  have ha : ∀ (b : V) st, RAt (FA [.const d c]) ctx st (cellAt b) := fun _ _ => cellAt_r
  unfold placeAtom
  dsimp only
  repeat' pa_step

set_option maxHeartbeats 1000000 in
theorem place_add_r {st : St} (d a b : V) : RAt (FA [.add d a b]) ctx st (placeAtom (.add d a b)) := by
  have hc : ∀ (b : V) st, RAt (FA [.add d a b]) ctx st (cellOf b) := fun _ _ => cellOf_r
  have ha : ∀ (b : V) st, RAt (FA [.add d a b]) ctx st (cellAt b) := fun _ _ => cellAt_r
  unfold placeAtom
  dsimp only
  repeat' pa_step

set_option maxHeartbeats 1000000 in
theorem place_mul_r {st : St} (d a b : V) : RAt (FA [.mul d a b]) ctx st (placeAtom (.mul d a b)) := by
  have hc : ∀ (b : V) st, RAt (FA [.mul d a b]) ctx st (cellOf b) := fun _ _ => cellOf_r
  have ha : ∀ (b : V) st, RAt (FA [.mul d a b]) ctx st (cellAt b) := fun _ _ => cellAt_r
  unfold placeAtom
  dsimp only
  repeat' pa_step

set_option maxHeartbeats 1000000 in
theorem place_copy_r {st : St} (d s : V) : RAt (FA [.copy d s]) ctx st (placeAtom (.copy d s)) := by
  have hc : ∀ (b : V) st, RAt (FA [.copy d s]) ctx st (cellOf b) := fun _ _ => cellOf_r
  have ha : ∀ (b : V) st, RAt (FA [.copy d s]) ctx st (cellAt b) := fun _ _ => cellAt_r
  unfold placeAtom
  dsimp only
  repeat' pa_step

set_option maxHeartbeats 1000000 in
theorem place_load_r {st : St} (d p : V) (off : ℕ) : RAt (FA [.load d p off]) ctx st (placeAtom (.load d p off)) := by
  have hc : ∀ (b : V) st, RAt (FA [.load d p off]) ctx st (cellOf b) := fun _ _ => cellOf_r
  have ha : ∀ (b : V) st, RAt (FA [.load d p off]) ctx st (cellAt b) := fun _ _ => cellAt_r
  unfold placeAtom
  dsimp only
  repeat' pa_step

set_option maxHeartbeats 1000000 in
theorem place_assertEq_r {st : St} (a b : V) : RAt (FA [.assertEq a b]) ctx st (placeAtom (.assertEq a b)) := by
  have hc : ∀ (b : V) st, RAt (FA [.assertEq a b]) ctx st (cellOf b) := fun _ _ => cellOf_r
  have ha : ∀ (b : V) st, RAt (FA [.assertEq a b]) ctx st (cellAt b) := fun _ _ => cellAt_r
  unfold placeAtom
  dsimp only
  repeat' pa_step

set_option maxHeartbeats 1000000 in
theorem place_assertNe_r {st : St} (x i p : V) : RAt (FA [.assertNe x i p]) ctx st (placeAtom (.assertNe x i p)) := by
  have hc : ∀ (b : V) st, RAt (FA [.assertNe x i p]) ctx st (cellOf b) := fun _ _ => cellOf_r
  have ha : ∀ (b : V) st, RAt (FA [.assertNe x i p]) ctx st (cellAt b) := fun _ _ => cellAt_r
  unfold placeAtom
  dsimp only
  repeat' pa_step

set_option maxHeartbeats 1000000 in
theorem place_rangeCheck_r {st : St} (x y t1 t2 k : V) : RAt (FA [.rangeCheck x y t1 t2 k]) ctx st (placeAtom (.rangeCheck x y t1 t2 k)) := by
  have hc : ∀ (b : V) st, RAt (FA [.rangeCheck x y t1 t2 k]) ctx st (cellOf b) := fun _ _ => cellOf_r
  have ha : ∀ (b : V) st, RAt (FA [.rangeCheck x y t1 t2 k]) ctx st (cellAt b) := fun _ _ => cellAt_r
  unfold placeAtom
  dsimp only
  repeat' pa_step

set_option maxHeartbeats 1000000 in
theorem place_assertInK_r {st : St} (a b : V) : RAt (FA [.assertInK a b]) ctx st (placeAtom (.assertInK a b)) := by
  have hc : ∀ (b : V) st, RAt (FA [.assertInK a b]) ctx st (cellOf b) := fun _ _ => cellOf_r
  have ha : ∀ (b : V) st, RAt (FA [.assertInK a b]) ctx st (cellAt b) := fun _ _ => cellAt_r
  unfold placeAtom
  dsimp only
  repeat' pa_step

set_option maxHeartbeats 1000000 in
theorem place_keccak_r {st : St} (ins outs : List V) (i o : Bool) : RAt (FA [.keccak ins outs i o]) ctx st (placeAtom (.keccak ins outs i o)) := by
  have hc : ∀ (b : V) st, RAt (FA [.keccak ins outs i o]) ctx st (cellOf b) := fun _ _ => cellOf_r
  have ha : ∀ (b : V) st, RAt (FA [.keccak ins outs i o]) ctx st (cellAt b) := fun _ _ => cellAt_r
  unfold placeAtom
  dsimp only
  repeat' pa_step

set_option maxHeartbeats 1000000 in
theorem place_frameAddr_r {st : St} (p : V) (run : List V) : RAt (FA [.frameAddr p run]) ctx st (placeAtom (.frameAddr p run)) := by
  have hc : ∀ (b : V) st, RAt (FA [.frameAddr p run]) ctx st (cellOf b) := fun _ _ => cellOf_r
  have ha : ∀ (b : V) st, RAt (FA [.frameAddr p run]) ctx st (cellAt b) := fun _ _ => cellAt_r
  unfold placeAtom
  dsimp only
  repeat' pa_step

set_option maxHeartbeats 1000000 in
theorem place_hint_r {st : St} (h : Hint) : RAt (FA [.hint h]) ctx st (placeAtom (.hint h)) := by
  have hc : ∀ (b : V) st, RAt (FA [.hint h]) ctx st (cellOf b) := fun _ _ => cellOf_r
  have ha : ∀ (b : V) st, RAt (FA [.hint h]) ctx st (cellAt b) := fun _ _ => cellAt_r
  unfold placeAtom
  dsimp only
  repeat' pa_step

set_option maxHeartbeats 1000000 in
theorem place_touch_r {st : St} (t p : V) : RAt (FA [.touch t p]) ctx st (placeAtom (.touch t p)) := by
  have hc : ∀ (b : V) st, RAt (FA [.touch t p]) ctx st (cellOf b) := fun _ _ => cellOf_r
  have ha : ∀ (b : V) st, RAt (FA [.touch t p]) ctx st (cellAt b) := fun _ _ => cellAt_r
  unfold placeAtom
  dsimp only
  repeat' pa_step

/-- **An atom** places no value but its own lazy one and a frame address's pointer. -/
theorem placeAtom_r {st : St} : ∀ a : Atom, RAt (FA [a]) ctx st (placeAtom a)
  | .const d c => place_const_r d c
  | .add d a b => place_add_r d a b
  | .mul d a b => place_mul_r d a b
  | .copy d s => place_copy_r d s
  | .load d p off => place_load_r d p off
  | .assertEq a b => place_assertEq_r a b
  | .assertNe x i p => place_assertNe_r x i p
  | .rangeCheck x y t1 t2 k => place_rangeCheck_r x y t1 t2 k
  | .assertInK a b => place_assertInK_r a b
  | .keccak ins outs i o => place_keccak_r ins outs i o
  | .frameAddr p run => place_frameAddr_r p run
  | .hint h => place_hint_r h
  | .touch t p => place_touch_r t p

end Atoms

/-! ## Blocks -/

section Blocks

variable {ctx : Ctx} {S : V → Prop}

theorem inBlock_r {m : P Unit} (hm : ∀ st, RAt S ctx st m) (st : St) :
    RAt S ctx st (inBlock m) := by
  unfold inBlock
  r_straight

theorem placeMatch_r {x : V} {n : ℕ} {rest : List Stmt} {entered : Option (ℕ × Cell)}
    {chained : Bool} {armsAt : Cell → ArmExit → P (List (List PStmt))}
    (harms : ∀ base exit st, RAt S ctx st (armsAt base exit)) (st : St) :
    RAt S ctx st (placeMatch x n rest entered chained armsAt) := by
  unfold placeMatch
  repeat' (first | refine RAt.bind (harms _ _ _) fun _ _ _ => ?_ | r_step)

theorem atom_stmt_r {a : Atom} {rest : List Stmt} (st : St) :
    RAt (FA [a]) ctx st (placeStmt (.atom a) rest) := by
  rw [placeStmt]
  exact RAt.bind beginStmt_r fun _ _ _ => placeAtom_r a

set_option maxHeartbeats 2000000 in
theorem call_stmt_r {f : String} {args rets : List V} {rest : List Stmt} (st : St) :
    RAt S ctx st (placeStmt (.call f args rets) rest) := by
  have hc : ∀ (b : V) st, RAt S ctx st (cellOf b) := fun _ _ => cellOf_r
  have ha : ∀ (b : V) st, RAt S ctx st (cellAt b) := fun _ _ => cellAt_r
  rw [placeStmt]
  r_straight

set_option maxHeartbeats 2000000 in
theorem callIf_stmt_r {c : V} {f : String} {args : List V} {rest : List Stmt} (st : St) :
    RAt S ctx st (placeStmt (.callIf c f args) rest) := by
  have hc : ∀ (b : V) st, RAt S ctx st (cellOf b) := fun _ _ => cellOf_r
  rw [placeStmt]
  r_straight

set_option maxHeartbeats 2000000 in
theorem dispatch_stmt_r {x : V} {fs : List String} {args rets : List V} {rest : List Stmt}
    (st : St) : RAt S ctx st (placeStmt (.dispatch x fs args rets) rest) := by
  have hc : ∀ (b : V) st, RAt S ctx st (cellOf b) := fun _ _ => cellOf_r
  have ha : ∀ (b : V) st, RAt S ctx st (cellAt b) := fun _ _ => cellAt_r
  rw [placeStmt]
  r_straight

theorem ret_stmt_r {vs : List V} {rest : List Stmt} (st : St) :
    RAt S ctx st (placeStmt (.ret vs) rest) := by
  have ha : ∀ (b : V) st, RAt S ctx st (cellAt b) := fun _ _ => cellAt_r
  rw [placeStmt]
  r_straight

mutual
/-- **A block** places no value but those its trace makes, its lazy value at the start and the
frame addresses among its atoms. -/
theorem placeBlock_r : ∀ (ss : List Stmt) (st : St), RAt (FA (atomsIn ss)) ctx st (placeBlock ss)
  | [], st => by
      rw [placeBlock]
      exact RAt.pure
  | s :: rest, st => by
      rw [placeBlock]
      have hs : ∀ v, FA (atomsOf s) v → FA (atomsIn (s :: rest)) v := fun v h =>
        h.mono fun a ha => by rw [atomsIn]; exact List.mem_append_left _ ha
      have hr : ∀ v, FA (atomsIn rest) v → FA (atomsIn (s :: rest)) v := fun v h =>
        h.mono fun a ha => by rw [atomsIn]; exact List.mem_append_right _ ha
      exact RAt.bind ((placeStmt_r s rest st).mono hs) fun _ st₁ _ => RAt.bind endStmt_r
        fun _ st₂ _ => (placeBlock_r rest st₂).mono hr

theorem placeStmt_r : ∀ (s : Stmt) (rest : List Stmt) (st : St),
    RAt (FA (atomsOf s)) ctx st (placeStmt s rest)
  | .atom a, rest, st => by
      have h := atom_stmt_r (ctx := ctx) (rest := rest) (a := a) st
      rw [atomsOf]
      exact h
  | .ite c z nz, rest, st => by
      have hz : ∀ st, RAt (FA (atomsOf (.ite c z nz))) ctx st (inBlock (placeBlock z)) :=
        fun st => inBlock_r (fun st => (placeBlock_r z st).mono fun v h => h.mono fun a ha => by
          rw [atomsOf]; exact List.mem_append_left _ ha) st
      have hnz : ∀ st, RAt (FA (atomsOf (.ite c z nz))) ctx st (inBlock (placeBlock nz)) :=
        fun st => inBlock_r (fun st => (placeBlock_r nz st).mono fun v h => h.mono fun a ha => by
          rw [atomsOf]; exact List.mem_append_right _ ha) st
      rw [placeStmt]
      repeat' (first | refine RAt.bind (hz _) fun _ _ _ => ?_ | refine RAt.bind (hnz _) fun _ _ _ => ?_ | r_step)
  | .match_ x arms, rest, st => by
      rw [placeStmt]
      refine RAt.bind flush_r fun _ st₁ _ => RAt.get_bind (RAt.setS_bind
        (rR_same rfl rfl rfl rfl) (placeMatch_r (fun base exit st => ?_) _))
      have h := placeArms_r arms 0 arms.length base exit st
      rw [atomsOf]
      exact h
  | .call f args rets, rest, st => call_stmt_r st
  | .callIf c f args, rest, st => callIf_stmt_r st
  | .dispatch x fs args rets, rest, st => dispatch_stmt_r st
  | .ret vs, rest, st => ret_stmt_r st

theorem placeArms_r : ∀ (arms : List (List Stmt)) (j n : ℕ) (base : Cell) (exit : ArmExit)
    (st : St), RAt (FA (armsAtoms arms)) ctx st (placeArms arms j n base exit)
  | [], j, n, base, exit, st => by
      rw [placeArms]
      r_straight
  | arm :: more, j, n, base, exit, st => by
      have ha : ∀ st, RAt (FA (armsAtoms (arm :: more))) ctx st (inBlock (placeBlock arm)) :=
        fun st => inBlock_r (fun st => (placeBlock_r arm st).mono fun v h => h.mono fun a ha => by
          rw [armsAtoms]; exact List.mem_append_left _ ha) st
      have hm : ∀ st, RAt (FA (armsAtoms (arm :: more))) ctx st
          (placeArms more (j + 1) n base exit) :=
        fun st => (placeArms_r more (j + 1) n base exit st).mono fun v h => h.mono fun a ha => by
          rw [armsAtoms]; exact List.mem_append_right _ ha
      rw [placeArms]
      repeat' (first | refine RAt.bind (ha _) fun _ _ _ => ?_ | refine RAt.bind (hm _) fun _ _ _ => ?_ | r_step)
end

/-- **`PlaceNew`, the frame addresses apart**: a block from a state with no lazy value places no
value but those its trace makes and the pointers of the frame addresses among its atoms; the
trace left only shrinks and the shared tables only grow. -/
theorem placeNew (ss : List Stmt) (st : St) : wpP (placeBlock ss) ctx st fun _ st' =>
    (st.lazy = none → ∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf st.rest ∨
      ∃ run, Atom.frameAddr v run ∈ atomsIn ss) ∧
    (∀ v ∈ allocsOf st'.rest, v ∈ allocsOf st.rest) ∧ ∀ x ∈ st.tables.shared, x ∈ st'.tables.shared :=
  wp_mono (placeBlock_r ss st) fun _ _ ⟨h1, h2, _, h4⟩ => ⟨fun hz v hv => by
    rcases h1 v hv with h | h | ⟨k, h⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rw [hz] at h; cases h
    · exact Or.inr (Or.inr h), h2, h4⟩

theorem placeNew_ok : PlaceNew ctx := placeNew

/-- **A flush** from a state with no lazy value places only the values the trace left makes. -/
theorem flushNew (up : List Stmt) (st : St) (hz : st.lazy = none) :
    wpP (flush up) ctx st fun _ st' =>
      ∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf st.rest :=
  wp_mono (flush_r (S := fun _ => False) (st := st)) fun _ _ ⟨h1, _⟩ v hv => by
    rcases h1 v hv with h | h | ⟨k, h⟩ | h
    · exact Or.inl h
    · exact Or.inr h
    · rw [hz] at h; cases h
    · exact h.elim

end Blocks

end
end LeanVM.Guest.Backend.Complete
