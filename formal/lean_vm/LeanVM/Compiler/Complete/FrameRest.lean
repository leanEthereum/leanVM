/-
  LeanVM.Compiler.Complete.FrameRest

  A block's placement passes the events the scope walk passes, on and off the path.
-/

module

public import LeanVM.Compiler.Complete.FrameInduct
public import LeanVM.Compiler.Complete.FrameNew
public import LeanVM.Compiler.Complete.FrameLazy
public import LeanVM.Compiler.Complete.ScopedRet

/-!
# The events a placement passes

Every placement step but a flush and an `expect` keeps the events left (`RestAt`). A flush passes
the events `flushS` passes, and an `expect` the one `expectS` passes; so a block's placement
leaves the events its scope walk (`scopeBlock`) leaves (`blockRest`), on any path.
-/

namespace LeanVM.Compiler.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

section Rest

variable {ctx : Ctx} {α β : Type}

/-- The events left as they were. -/
def RestR (st st' : St) : Prop := st'.rest = st.rest

theorem RestR.refl (st : St) : RestR st st := rfl

theorem RestR.trans {st₁ st₂ st₃ : St} (h₁ : RestR st₁ st₂) (h₂ : RestR st₂ st₃) :
    RestR st₁ st₃ := Eq.trans h₂ h₁

/-- Every success of `m` from `st` keeps the events left. -/
def RestAt (ctx : Ctx) (st : St) (m : P α) : Prop := wpP m ctx st fun _ st' => RestR st st'

variable {st : St}

theorem RestAt.pure {a : α} : RestAt ctx st (Pure.pure a) := wp_pure.mpr (RestR.refl st)

theorem RestAt.fail {msg : String} : RestAt ctx st (failP msg : P α) := wp_failP

theorem RestAt.fail_bind {msg : String} {f : α → P β} :
    RestAt ctx st ((failP msg : P α) >>= f) := wp_bind.mpr wp_failP

theorem RestAt.bind {m : P α} {f : α → P β} (hm : RestAt ctx st m)
    (hf : ∀ a st', RestR st st' → RestAt ctx st' (f a)) : RestAt ctx st (m >>= f) :=
  wp_bind.mpr (wp_mono hm fun a st' h => wp_mono (hf a st' h) fun _ _ h' => h.trans h')

theorem RestAt.get_bind {f : St → P β} (h : RestAt ctx st (f st)) : RestAt ctx st (get >>= f) :=
  wp_bind.mpr (wp_get.mpr h)

theorem RestAt.read_bind {f : Ctx → P β} (h : RestAt ctx st (f ctx)) :
    RestAt ctx st (read >>= f) := wp_bind.mpr (wp_read.mpr h)

theorem RestAt.peek_bind {f : Option Event → P β} (h : RestAt ctx st (f st.rest.head?)) :
    RestAt ctx st (peek >>= f) := wp_bind.mpr (wp_peek.mpr h)

theorem RestAt.guard {c : Prop} [Decidable c] {msg : String} {f : PUnit → P β}
    (h : ¬c → RestAt ctx st (f PUnit.unit)) :
    RestAt ctx st (if c then failP msg >>= f else f PUnit.unit) := by
  split
  · exact RestAt.fail_bind
  · next hc => exact h hc

theorem RestAt.mod {g : St → St} (h : RestR st (g st)) : RestAt ctx st (modify g) :=
  wp_modify.mpr h

theorem RestAt.mod_bind {g : St → St} {f : PUnit → P β} (h : RestR st (g st))
    (hf : RestAt ctx (g st) (f ⟨⟩)) : RestAt ctx st (modify g >>= f) :=
  wp_bind.mpr (wp_modify.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem RestAt.modG {g : St → α × St} (h : RestR st (g st).2) :
    RestAt ctx st (modifyGet g) := wp_modifyGet.mpr h

theorem RestAt.modG_bind {g : St → α × St} {f : α → P β} (h : RestR st (g st).2)
    (hf : RestAt ctx (g st).2 (f (g st).1)) : RestAt ctx st (modifyGet g >>= f) :=
  wp_bind.mpr (wp_modifyGet.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem RestAt.setS {s : St} (h : RestR st s) : RestAt ctx st (set s : P PUnit) := wp_set.mpr h

theorem RestAt.setS_bind {s : St} {f : PUnit → P β} (h : RestR st s) (hf : RestAt ctx s (f ⟨⟩)) :
    RestAt ctx st (set s >>= f) :=
  wp_bind.mpr (wp_set.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem RestAt.discard {m : P α} (h : RestAt ctx st m) : RestAt ctx st (Functor.discard m) := by
  rw [Functor.discard, map_const, Function.comp_apply, map_eq_pure_bind]
  exact RestAt.bind h fun _ _ _ => RestAt.pure

theorem restR_same {s : St} (h : s.rest = st.rest) : RestR st s := h

theorem bindTo_rest (v : V) (l : Loc) : RestAt ctx st (bindTo v l) := by
  unfold bindTo
  refine wp_bind.mpr (wp_get.mpr ?_)
  split
  · exact wp_bind.mpr wp_failP
  · exact wp_modify.mpr rfl

theorem forM_rest {γ : Type} {f : γ → P PUnit} (hf : ∀ b st, RestAt ctx st (f b)) :
    ∀ (l : List γ) (st : St), RestAt ctx st (l.forM f)
  | [], _ => RestAt.pure
  | b :: l, st => by
      show RestAt ctx st (f b >>= fun _ => l.forM f)
      exact RestAt.bind (hf b st) fun _ st' _ => forM_rest hf l st'

theorem mapM_rest {γ δ : Type} {f : γ → P δ} (hf : ∀ b st, RestAt ctx st (f b)) :
    ∀ (l : List γ) (st : St), RestAt ctx st (l.mapM f)
  | [], _ => by rw [List.mapM_nil]; exact RestAt.pure
  | b :: l, st => by
      rw [List.mapM_cons]
      exact RestAt.bind (hf b st) fun _ st' _ => RestAt.bind (mapM_rest hf l st') fun _ _ _ =>
        RestAt.pure

theorem optionMapM_rest {γ δ : Type} {f : γ → P δ} (hf : ∀ b st, RestAt ctx st (f b))
    (o : Option γ) (st : St) : RestAt ctx st (o.mapM f) := by
  cases o with
  | none => exact RestAt.pure
  | some v =>
    rw [Option.mapM, map_eq_pure_bind]
    exact RestAt.bind (hf v st) fun _ _ _ => RestAt.pure

end Rest

/-- A primitive already shown to keep the events left. -/
syntax "rest_prim" : tactic

set_option hygiene false in
macro_rules | `(tactic| rest_prim) => `(tactic| first
  | with_reducible refine RestAt.bind fresh_rest fun _ _ _ => ?_
  | with_reducible exact fresh_rest
  | with_reducible refine RestAt.bind pushHint_rest fun _ _ _ => ?_
  | with_reducible exact pushHint_rest
  | with_reducible refine RestAt.bind takeHints_rest fun _ _ _ => ?_
  | with_reducible exact takeHints_rest
  | with_reducible refine RestAt.bind push_rest fun _ _ _ => ?_
  | with_reducible exact push_rest
  | with_reducible refine RestAt.bind emitOp_rest fun _ _ _ => ?_
  | with_reducible exact emitOp_rest
  | with_reducible refine RestAt.bind constCell_rest fun _ _ _ => ?_
  | with_reducible exact constCell_rest
  | with_reducible refine RestAt.bind oneCell_rest fun _ _ _ => ?_
  | with_reducible exact oneCell_rest
  | with_reducible refine RestAt.bind zeroCell_rest fun _ _ _ => ?_
  | with_reducible exact zeroCell_rest
  | with_reducible refine RestAt.bind mulCell_rest fun _ _ _ => ?_
  | with_reducible exact mulCell_rest
  | with_reducible refine RestAt.bind emitDeref_rest fun _ _ _ => ?_
  | with_reducible exact emitDeref_rest
  | with_reducible refine RestAt.bind selfFp_rest fun _ _ _ => ?_
  | with_reducible exact selfFp_rest
  | with_reducible refine RestAt.bind materialize_rest fun _ _ _ => ?_
  | with_reducible exact materialize_rest
  | with_reducible refine RestAt.bind cellAt_rest fun _ _ _ => ?_
  | with_reducible exact cellAt_rest
  | with_reducible refine RestAt.bind cellOf_rest fun _ _ _ => ?_
  | with_reducible exact cellOf_rest
  | with_reducible refine RestAt.bind factor_rest fun _ _ _ => ?_
  | with_reducible exact factor_rest
  | with_reducible refine RestAt.bind pointer_rest fun _ _ _ => ?_
  | with_reducible exact pointer_rest
  | with_reducible refine RestAt.bind pooledCell_rest fun _ _ _ => ?_
  | with_reducible exact pooledCell_rest
  | with_reducible refine RestAt.bind pooled_rest fun _ _ _ => ?_
  | with_reducible exact pooled_rest
  | with_reducible refine RestAt.bind isLazy_rest fun _ _ _ => ?_
  | with_reducible exact isLazy_rest
  | with_reducible refine RestAt.bind isSelfFp_rest fun _ _ _ => ?_
  | with_reducible exact isSelfFp_rest
  | with_reducible refine RestAt.bind endStmt_rest fun _ _ _ => ?_
  | with_reducible exact endStmt_rest
  | with_reducible refine RestAt.bind bindRun_rest fun _ _ _ => ?_
  | with_reducible exact bindRun_rest
  | with_reducible refine RestAt.bind takeRun_rest fun _ _ _ => ?_
  | with_reducible exact takeRun_rest
  | with_reducible refine RestAt.bind spongeInPlace_rest fun _ _ _ => ?_
  | with_reducible exact spongeInPlace_rest
  | with_reducible refine RestAt.bind onAlloc_rest fun _ _ _ => ?_
  | with_reducible exact onAlloc_rest
  | with_reducible refine RestAt.bind destBits_rest fun _ _ _ => ?_
  | with_reducible exact destBits_rest
  | with_reducible refine RestAt.bind placeHint_rest fun _ _ _ => ?_
  | with_reducible exact placeHint_rest
  | with_reducible refine RestAt.bind placeAtom_rest fun _ _ _ => ?_
  | with_reducible exact placeAtom_rest
  | with_reducible refine RestAt.bind allocTable_rest fun _ _ _ => ?_
  | with_reducible exact allocTable_rest
  | with_reducible refine RestAt.bind sharedTable_rest fun _ _ _ => ?_
  | with_reducible exact sharedTable_rest
  | with_reducible refine RestAt.bind loopCount_rest fun _ _ _ => ?_
  | with_reducible exact loopCount_rest
  | with_reducible refine RestAt.bind placeCall_rest fun _ _ _ => ?_
  | with_reducible exact placeCall_rest
  | with_reducible refine RestAt.bind matchCells_rest fun _ _ _ => ?_
  | with_reducible exact matchCells_rest)

/-- One step of a walk that keeps the events left. -/
macro "rest_step" : tactic => `(tactic| first
  | with_reducible exact RestAt.pure
  | with_reducible exact RestAt.fail
  | with_reducible exact RestAt.fail_bind
  | with_reducible refine RestAt.get_bind ?_
  | with_reducible refine RestAt.read_bind ?_
  | with_reducible refine RestAt.peek_bind ?_
  | with_reducible refine RestAt.guard fun _ => ?_
  | with_reducible refine RestAt.mod_bind ?_ ?_
  | with_reducible refine RestAt.modG_bind ?_ ?_
  | with_reducible refine RestAt.setS_bind ?_ ?_
  | with_reducible refine RestAt.mod ?_
  | with_reducible refine RestAt.modG ?_
  | with_reducible refine RestAt.setS ?_
  | exact restR_same rfl
  | exact RestR.refl _
  | with_reducible refine RestAt.bind (bindTo_rest _ _) fun _ _ _ => ?_
  | with_reducible exact bindTo_rest _ _
  | with_reducible refine RestAt.bind (forM_rest ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine RestAt.bind (mapM_rest ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine RestAt.bind (optionMapM_rest ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine RestAt.bind (‹∀ st, RestAt _ st _› _) fun _ _ _ => ?_
  | with_reducible exact ‹∀ st, RestAt _ st _› _
  | with_reducible refine RestAt.discard ?_
  | with_reducible refine RestAt.bind (RestAt.discard ?_) fun _ _ _ => ?_
  | rest_prim
  | dsimp only
  | rw [pure_bind]
  | split)

macro "rest_straight" : tactic => `(tactic| repeat' rest_step)


section RestPrims

variable {ctx : Ctx} {st : St}

theorem fresh_rest : RestAt ctx st fresh := by
  unfold fresh
  exact RestAt.modG (restR_same rfl)


theorem pushHint_rest {h : LHint} : RestAt ctx st (pushHint h) := by
  unfold pushHint
  rest_straight


theorem takeHints_rest  : RestAt ctx st (takeHints) := by
  unfold takeHints
  rest_straight


theorem push_rest {s : PStmt} : RestAt ctx st (push s) := by
  unfold push
  rest_straight


theorem emitOp_rest {o : LOp} : RestAt ctx st (emitOp o) := by
  unfold emitOp
  rest_straight


theorem constCell_rest {k : ℕ × ℕ} : RestAt ctx st (constCell k) := by
  unfold constCell
  rest_straight


theorem oneCell_rest  : RestAt ctx st (oneCell) := by
  unfold oneCell
  rest_straight


theorem zeroCell_rest  : RestAt ctx st (zeroCell) := by
  unfold zeroCell
  rest_straight


theorem mulCell_rest {a b : Cell} : RestAt ctx st (mulCell a b) := by
  unfold mulCell
  rest_straight


theorem emitDeref_rest {p off d : Cell} : RestAt ctx st (emitDeref p off d) := by
  unfold emitDeref
  rest_straight


theorem selfFp_rest  : RestAt ctx st (selfFp) := by
  unfold selfFp
  rest_straight


theorem materialize_rest {c e : Cell} : RestAt ctx st (materialize c e) := by
  unfold materialize
  rest_straight


theorem cellAt_rest {v : V} : RestAt ctx st (cellAt v) := by
  unfold cellAt
  rest_straight


theorem cellOf_rest {v : V} : RestAt ctx st (cellOf v) := by
  unfold cellOf
  rest_straight


theorem factor_rest {v : V} : RestAt ctx st (factor v) := by
  unfold factor
  rest_straight


theorem pointer_rest {p : V} {off : ℕ} : RestAt ctx st (pointer p off) := by
  unfold pointer
  rest_straight


theorem pooledCell_rest {find : Scope → Option Cell} {learn : Cell → Scope → Scope} {mk : Cell → LOp} : RestAt ctx st (pooledCell find learn mk) := by
  unfold pooledCell
  rest_straight


theorem pooled_rest {d : V} {find : Scope → Option Cell} {learn : Cell → Scope → Scope} {mk : Cell → LOp} : RestAt ctx st (pooled d find learn mk) := by
  unfold pooled
  rest_straight


theorem isLazy_rest {v : V} {k : Kind} : RestAt ctx st (isLazy v k) := by
  unfold isLazy
  rest_straight


theorem isSelfFp_rest {n : Cell} : RestAt ctx st (isSelfFp n) := by
  unfold isSelfFp
  rest_straight


theorem endStmt_rest  : RestAt ctx st (endStmt) := by
  unfold endStmt
  rest_straight


theorem bindRun_rest {vs : List V} {base : Cell} : RestAt ctx st (bindRun vs base) := by
  unfold bindRun
  exact forM_rest (fun _ _ => bindTo_rest _ _) _ _


theorem takeRun_rest {vs : List V} : RestAt ctx st (takeRun vs) := by
  unfold takeRun
  rest_straight

theorem spongeInPlace_rest {vs : List V} {up : List Stmt} : RestAt ctx st (spongeInPlace vs up) := by
  unfold spongeInPlace
  rest_straight


theorem onAlloc_rest {vs : List V} {k : Kind} {up : List Stmt} : RestAt ctx st (onAlloc vs k up) := by
  unfold onAlloc
  rest_straight


theorem destBits_rest {d : Dest} : RestAt ctx st (destBits d) := by
  unfold destBits
  rest_straight

set_option maxHeartbeats 2000000 in
theorem placeHint_rest {h : Hint} : RestAt ctx st (placeHint h) := by
  have hc : ∀ (b : V) st, RestAt ctx st (cellOf b) := fun _ _ => cellOf_rest
  have ha : ∀ (b : V) st, RestAt ctx st (cellAt b) := fun _ _ => cellAt_rest
  cases h <;> unfold placeHint <;> rest_straight

set_option maxHeartbeats 2000000 in
theorem placeAtom_rest {a : Atom} : RestAt ctx st (placeAtom a) := by
  have hc : ∀ (b : V) st, RestAt ctx st (cellOf b) := fun _ _ => cellOf_rest
  have ha : ∀ (b : V) st, RestAt ctx st (cellAt b) := fun _ _ => cellAt_rest
  cases a <;> unfold placeAtom <;> rest_straight

theorem allocTable_rest {n : ℕ} : RestAt ctx st (allocTable n) := by
  unfold allocTable
  rest_straight

theorem sharedTable_rest {fs : List String} : RestAt ctx st (sharedTable fs) := by
  unfold sharedTable
  rest_straight

theorem loopCount_rest {f : String} {args : List V} {cells : List Cell} :
    RestAt ctx st (loopCount f args cells) := by
  unfold loopCount
  rest_straight

theorem placeCall_rest {f : String} {argVs : List V} {args rets : List Cell} {cond : Option Cell}
    {tail : Bool} : RestAt ctx st (placeCall f argVs args rets cond tail) := by
  unfold placeCall
  rest_straight

theorem matchCells_rest {x : V} {rest : List Stmt} {chained : Bool} :
    RestAt ctx st (matchCells x rest chained) := by
  unfold matchCells
  rest_straight


end RestPrims

/-! ## In lockstep with the scope walk -/

section Lock

variable {ctx : Ctx} {α β : Type}

theorem Cons.len {rc : ℕ} {r r' : List Event} (h : Cons rc r r') : r'.length ≤ r.length := by
  obtain ⟨p, rfl, _⟩ := h
  simp

/-- From a state whose events left are `r`, every success leaves `r'`. -/
def RS (ctx : Ctx) (r r' : List Event) (s : St) (m : P α) : Prop :=
  s.rest = r → wpP m ctx s fun _ s' => s'.rest = r'

theorem RS.keep_bind {r r' : List Event} {s : St} {m : P α} {f : α → P β} (hm : RestAt ctx s m)
    (hf : ∀ a s', RS ctx r r' s' (f a)) : RS ctx r r' s (m >>= f) := fun hs =>
  wp_bind.mpr (wp_mono hm fun a s' h => hf a s' (Eq.trans h hs))

theorem RS.keep {r : List Event} {s : St} {m : P α} (hm : RestAt ctx s m) : RS ctx r r s m :=
  fun hs => wp_mono hm fun _ _ h => Eq.trans h hs

theorem RS.step_bind {r r₁ r' : List Event} {s : St} {m : P α} {f : α → P β}
    (hm : RS ctx r r₁ s m) (hf : ∀ a s', RS ctx r₁ r' s' (f a)) : RS ctx r r' s (m >>= f) :=
  fun hs => wp_bind.mpr (wp_mono (hm hs) fun a s' h => hf a s' h)

theorem RS.eq {r r' r'' : List Event} {s : St} {m : P α} (h : RS ctx r r' s m) (he : r' = r'') :
    RS ctx r r'' s m := he ▸ h

theorem RS.get_bind {r r' : List Event} {s : St} {f : St → P β} (h : RS ctx r r' s (f s)) :
    RS ctx r r' s (get >>= f) := fun hs => wp_bind.mpr (wp_get.mpr (h hs))

theorem RS.read_bind {r r' : List Event} {s : St} {f : Ctx → P β} (h : RS ctx r r' s (f ctx)) :
    RS ctx r r' s (read >>= f) := fun hs => wp_bind.mpr (wp_read.mpr (h hs))

theorem RS.peek_bind {r r' : List Event} {s : St} {f : Option Event → P β}
    (h : RS ctx r r' s (f r.head?)) : RS ctx r r' s (peek >>= f) := fun hs =>
  wp_bind.mpr (wp_peek.mpr (by rw [hs]; exact h hs))

theorem RS.fail {r r' : List Event} {s : St} {msg : String} : RS ctx r r' s (failP msg : P α) :=
  fun _ => wp_failP

theorem RS.fail_bind {r r' : List Event} {s : St} {msg : String} {f : α → P β} :
    RS ctx r r' s ((failP msg : P α) >>= f) := fun _ => wp_bind.mpr wp_failP

/-- **An `expect`** passes the event `expectS` passes. -/
theorem expect_rs {e e' : Event → Bool} {what what' : String} {sc sc' : SSt} {s : St}
    (h : expectS e what sc = .ok sc') (he : ∀ ev, e ev = true → e' ev = true) :
    RS ctx sc.rest sc'.rest s (expect e' what') := by
  intro hs
  obtain ⟨ev, hr, hev, _, _⟩ := expectS_ok h
  unfold expect advance
  refine wp_bind.mpr (wp_peek.mpr ?_)
  rw [hs, hr]
  simp only [List.head?_cons, he ev hev, ↓reduceIte]
  refine wp_modify.mpr ?_
  show s.rest.tail = sc'.rest
  rw [hs, hr]
  rfl

/-- **A flush, step by step with `flushS`**: it passes the events `flushS` passes. -/
theorem flushN_rs {up : List Stmt} : ∀ (fuel : ℕ) (s : St) (live : VMap Unit) (b : Bool)
    (sc' : SSt), flushS ctx.retCells s.rest live b = .ok sc' → s.rest.length ≤ fuel →
    wpP (flushN up fuel) ctx s fun _ s' => s'.rest = sc'.rest
  | 0, s, live, b, sc', h, hl => by
      have hn : s.rest = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
      rw [hn] at h
      simp only [flushS] at h
      cases h
      unfold flushN
      exact wp_pure.mpr hn
  | fuel + 1, s, live, b, sc', h, hl => by
      unfold flushN advance
      refine wp_bind.mpr (wp_peek.mpr ?_)
      cases hr : s.rest with
      | nil =>
        rw [hr] at h
        simp only [flushS] at h
        cases h
        exact wp_pure.mpr hr
      | cons e es =>
        rw [hr] at h hl
        simp only [List.length_cons] at hl
        have hl' : es.length ≤ fuel := by omega
        simp only [List.head?_cons]
        cases e with
        | alloc vs kind =>
          simp only [flushS] at h
          have h' : ∃ live' b', flushS ctx.retCells es live' b' = .ok sc' := by
            split at h
            · split at h
              · cases h
              · split at h
                · cases h
                · exact ⟨_, _, h⟩
            · exact ⟨_, _, h⟩
          obtain ⟨live', b', h'⟩ := h'
          dsimp only
          refine wp_bind.mpr (wp_modify.mpr (wp_bind.mpr (wp_mono (onAlloc_new vs kind up)
            fun _ s₂ h₂ => flushN_rs fuel s₂ live' b' sc' (by rw [h₂.2.1]; simpa [hr] using h')
              (by rw [h₂.2.1]; simpa [hr] using hl'))))
        | use v =>
          simp only [flushS] at h
          split at h
          · dsimp only
            have hk : ∀ s₂ : St, s₂.rest = es →
                wpP (modify (fun s => { s with used := v :: s.used }) >>= fun _ => flushN up fuel)
                  ctx s₂ fun _ s' => s'.rest = sc'.rest := fun s₂ h₂ =>
              wp_bind.mpr (wp_modify.mpr (flushN_rs fuel _ live b sc' (by simpa [h₂] using h)
                (by simpa [h₂] using hl')))
            refine wp_bind.mpr (wp_modify.mpr (wp_bind.mpr (wp_get.mpr ?_)))
            split
            · exact wp_bind.mpr (wp_mono (LzAt.discard materialize_lz) fun _ s₂ h₂ =>
                hk s₂ (by rw [h₂.2]; simp [hr]))
            · exact hk _ (by simp [hr])
          · cases h
        | shift v exp =>
          simp only [flushS] at h
          split at h
          · exact wp_bind.mpr (wp_modify.mpr (wp_bind.mpr (wp_modify.mpr
              (flushN_rs fuel _ live b sc' (by simp only [hr, List.tail_cons]; exact h)
              (by simp only [hr, List.tail_cons]; exact hl')))))
          · cases h
        | chain =>
          simp only [flushS] at h
          exact wp_bind.mpr (wp_modify.mpr (wp_bind.mpr (wp_modify.mpr
            (flushN_rs fuel _ live b sc' (by simp only [hr, List.tail_cons]; exact h)
              (by simp only [hr, List.tail_cons]; exact hl')))))
        | note n =>
          simp only [flushS] at h
          exact wp_bind.mpr (wp_modify.mpr (wp_bind.mpr (wp_modify.mpr
            (flushN_rs fuel _ live b sc' (by simp only [hr, List.tail_cons]; exact h)
              (by simp only [hr, List.tail_cons]; exact hl')))))
        | _ =>
          simp only [flushS] at h
          cases h
          exact wp_pure.mpr hr

/-- **`FlushRest`**: a flush passes the events `flushAt` passes. -/
theorem flushRest (up : List Stmt) (st : St) (s s' : SSt) (h : flushAt ctx.retCells s = .ok s')
    (hr : st.rest = s.rest) (hf : st.rest.length ≤ ctx.fuel) :
    wpP (flush up) ctx st fun _ st' => st'.rest = s'.rest := by
  unfold flush
  exact wp_bind.mpr (wp_read.mpr (flushN_rs _ st s.live s.retDone s' (by rw [hr]; exact h) hf))

theorem flush_rs {up : List Stmt} {sc sc' : SSt} {s : St} (h : flushAt ctx.retCells sc = .ok sc')
    (hl : sc.rest.length ≤ ctx.fuel) : RS ctx sc.rest sc'.rest s (flush up) := fun hs =>
  flushRest up s sc sc' h hs (by rw [hs]; exact hl)

theorem inBlock_rs {m : P Unit} {blk : SSt → Except String SSt} {sc sc' : SSt} {s : St}
    (hm : ∀ (s₁ s₂ : SSt) (st : St), blk s₁ = .ok s₂ → s₁.rest.length ≤ ctx.fuel →
      RS ctx s₁.rest s₂.rest st m)
    (hc : ∀ s₁ s₂, blk s₁ = .ok s₂ → Cons ctx.retCells s₁.rest s₂.rest)
    (h : scopeInner ctx.retCells blk sc = .ok sc') (hl : sc.rest.length ≤ ctx.fuel) :
    RS ctx sc.rest sc'.rest s (inBlock m) := by
  obtain ⟨s₁, s₂, s₃, s₄, h₁, h₂, h₃, h₄, rfl⟩ := scopeInner_inv h
  have hf₃ := (flushEdge_ok h₃).2
  have l₁ : s₁.rest.length ≤ ctx.fuel :=
    le_trans (expectS_cons (rc := ctx.retCells) noAlloc_enter h₁).len hl
  have l₂ : s₂.rest.length ≤ ctx.fuel := le_trans (hc _ _ h₂).len l₁
  unfold inBlock
  refine RS.step_bind (expect_rs h₁ fun _ h => h) fun _ _ => ?_
  refine RS.get_bind ?_
  refine RS.keep_bind (RestAt.setS (restR_same rfl)) fun _ _ => ?_
  refine RS.step_bind (hm s₁ s₂ _ h₂ l₁) fun _ _ => ?_
  refine RS.step_bind (flush_rs hf₃ l₂) fun _ _ => ?_
  refine RS.step_bind (expect_rs h₄ fun _ h => h) fun _ _ => ?_
  refine RS.get_bind ?_
  show RS ctx s₄.rest s₄.rest _ _
  refine RS.keep ?_
  rest_straight

theorem placeMatch_rs {x : V} {n : ℕ} {rest : List Stmt} {entered : Option (ℕ × Cell)}
    {chained : Bool} {armsAt : Cell → ArmExit → P (List (List PStmt))} {r r₁ r' : List Event}
    {s : St} (harms : ∀ base exit st, RS ctx r r₁ st (armsAt base exit))
    (he : ∀ st, RS ctx r₁ r' st (expect isEmit "a match")) :
    RS ctx r r' s (placeMatch x n rest entered chained armsAt) := by
  unfold placeMatch
  repeat' (first
    | with_reducible refine RS.step_bind (harms _ _ _) fun _ _ => ?_
    | with_reducible refine RS.step_bind (he _) fun _ _ => ?_
    | with_reducible refine RS.get_bind ?_
    | with_reducible refine RS.keep_bind ?_ fun _ _ => ?_
    | with_reducible refine RS.keep ?_
    | rest_step)

/-- **A statement of `scopeFlat`**: its flush and its `emit`, then steps that keep the events left. -/
theorem flat_rs {stm : Stmt} {up : List Stmt} {f : PUnit → P β} {sc sc' : SSt} {s : St}
    (h : scopeFlat ctx.retCells stm sc = .ok sc') (hl : sc.rest.length ≤ ctx.fuel)
    (hm : ∀ s, RestAt ctx s (f ⟨⟩)) : RS ctx sc.rest sc'.rest s (beginStmt up >>= f) := by
  unfold scopeFlat at h
  split at h
  · cases h
  next s₁ h₁ =>
  split at h
  · cases h
  next s₂ h₂ =>
  split at h
  · cases h
  split at h
  · cases h
  cases h
  unfold beginStmt
  rw [bind_assoc]
  exact RS.step_bind (flush_rs h₁ hl) fun _ _ => RS.step_bind (expect_rs h₂ fun _ h => h)
    fun _ _ => RS.keep (hm _)

mutual
/-- **A block in lockstep with its scope walk** passes the events the walk passes. -/
theorem placeBlock_rs : ∀ (ss : List Stmt) (sc sc' : SSt) (s : St),
    scopeBlock ctx.retCells ss sc = .ok sc' → sc.rest.length ≤ ctx.fuel →
    RS ctx sc.rest sc'.rest s (placeBlock ss)
  | [], sc, sc', s, h, _ => by
      simp only [scopeBlock] at h
      cases h
      rw [placeBlock]
      exact RS.keep RestAt.pure
  | st :: rest, sc, sc', s, h, hl => by
      simp only [scopeBlock] at h
      split at h
      · cases h
      next s₁ h₁ =>
      rw [placeBlock]
      exact RS.step_bind (placeStmt_rs st rest sc s₁ s h₁ hl) fun _ _ =>
        RS.keep_bind endStmt_rest fun _ _ =>
          placeBlock_rs rest s₁ sc' _ h (le_trans (scopeStmt_cons _ _ _ _ h₁).len hl)

theorem placeStmt_rs : ∀ (st : Stmt) (rest : List Stmt) (sc sc' : SSt) (s : St),
    scopeStmt ctx.retCells st sc = .ok sc' → sc.rest.length ≤ ctx.fuel →
    RS ctx sc.rest sc'.rest s (placeStmt st rest)
  | .ite c z nz, rest, sc, sc', s, h, hl => by
      simp only [scopeStmt] at h
      split at h
      · cases h
      next s₀ h₀ =>
      split at h
      · cases h
      split at h
      · cases h
      next s₁ h₁ =>
      have hf₀ := (flushEdge_ok h₀).2
      have l₀ : s₀.rest.length ≤ ctx.fuel := le_trans (flushAt_cons hf₀).len hl
      have hc : ∀ (b : List Stmt) s₁ s₂, scopeBlock ctx.retCells b s₁ = .ok s₂ →
          Cons ctx.retCells s₁.rest s₂.rest := fun b => scopeBlock_cons _ b
      have hz := inBlock_rs (m := placeBlock z) (s := s)
        (fun s₁ s₂ st h₂ l => placeBlock_rs z s₁ s₂ st h₂ l) (hc z) h₁ l₀
      have l₁ : s₁.rest.length ≤ ctx.fuel := le_trans (scopeInner_cons (hc z) h₁).len l₀
      rw [placeStmt]
      refine RS.step_bind (flush_rs hf₀ hl) fun _ _ => ?_
      refine RS.keep_bind cellOf_rest fun _ _ => RS.keep_bind selfFp_rest fun _ _ =>
        RS.keep_bind oneCell_rest fun _ _ => RS.keep_bind fresh_rest fun _ _ =>
          RS.keep_bind takeHints_rest fun _ _ => ?_
      refine RS.step_bind (inBlock_rs (fun s₁ s₂ st h₂ l => placeBlock_rs z s₁ s₂ st h₂ l)
        (hc z) h₁ l₀) fun _ _ => ?_
      refine RS.peek_bind ?_
      unfold scopeIteTail at h
      split at h
      · next tl hr =>
        split at h
        · cases h
        next s₂ h₂ =>
        rw [show s₁.rest.head? = some .enter by rw [hr]; rfl]
        have l₁' : ({ s₁ with retDone := s₀.retDone } : SSt).rest.length ≤ ctx.fuel := l₁
        refine RS.keep_bind fresh_rest fun _ _ => ?_
        refine RS.step_bind (inBlock_rs (sc := { s₁ with retDone := s₀.retDone })
          (fun s₁ s₂ st h₂ l => placeBlock_rs nz s₁ s₂ st h₂ l) (hc nz) h₂ l₁') fun _ _ => ?_
        refine RS.step_bind (expect_rs (sc := { s₂ with retDone := s₁.retDone || s₂.retDone }) h
          fun _ h => h) fun _ _ => RS.keep push_rest
      · next hr =>
        have hne : s₁.rest.head? ≠ some .enter := by
          intro he
          cases hq : s₁.rest with
          | nil => rw [hq] at he; cases he
          | cons e es =>
            rw [hq] at he
            simp only [List.head?_cons, Option.some.injEq] at he
            subst he
            exact hr es hq
        split
        · next he => exact absurd he hne
        · split at h
          · cases h
          next hnz =>
          split
          · next h' => exact absurd h' hnz
          · exact RS.step_bind (expect_rs h fun _ h => h) fun _ _ => RS.keep push_rest
  | .match_ x arms, rest, sc, sc', s, h, hl => by
      simp only [scopeStmt] at h
      split at h
      · cases h
      next s₀ h₀ =>
      split at h
      · cases h
      split at h
      · cases h
      next s₁ h₁ =>
      have hf₀ := (flushEdge_ok h₀).2
      have l₀ : s₀.rest.length ≤ ctx.fuel := le_trans (flushAt_cons hf₀).len hl
      rw [placeStmt]
      refine RS.step_bind (flush_rs hf₀ hl) fun _ _ => RS.get_bind ?_
      refine RS.keep_bind (RestAt.setS (restR_same rfl)) fun _ _ => ?_
      exact placeMatch_rs (fun base exit st => placeArms_rs arms 0 arms.length base exit s₀ s₀.retDone
        s₁ st h₁ l₀) fun _ => expect_rs h fun _ h => h
  | .atom a, rest, sc, sc', s, h, hl => by
      simp only [scopeStmt] at h
      rw [placeStmt]
      exact flat_rs h hl fun _ => placeAtom_rest
  | .call f args rets, rest, sc, sc', s, h, hl => by
      simp only [scopeStmt] at h
      have hc : ∀ (b : V) st, RestAt ctx st (cellOf b) := fun _ _ => cellOf_rest
      have ha : ∀ (b : V) st, RestAt ctx st (cellAt b) := fun _ _ => cellAt_rest
      rw [placeStmt]
      exact flat_rs h hl fun _ => by rest_straight
  | .callIf c f args, rest, sc, sc', s, h, hl => by
      simp only [scopeStmt] at h
      have hc : ∀ (b : V) st, RestAt ctx st (cellOf b) := fun _ _ => cellOf_rest
      rw [placeStmt]
      exact flat_rs h hl fun _ => by rest_straight
  | .dispatch x fs args rets, rest, sc, sc', s, h, hl => by
      simp only [scopeStmt] at h
      have hc : ∀ (b : V) st, RestAt ctx st (cellOf b) := fun _ _ => cellOf_rest
      have ha : ∀ (b : V) st, RestAt ctx st (cellAt b) := fun _ _ => cellAt_rest
      rw [placeStmt]
      exact flat_rs h hl fun _ => by rest_straight
  | .ret vs, rest, sc, sc', s, h, hl => by
      simp only [scopeStmt] at h
      have ha : ∀ (b : V) st, RestAt ctx st (cellAt b) := fun _ _ => cellAt_rest
      rw [placeStmt]
      exact flat_rs h hl fun _ => by rest_straight

theorem placeArms_rs : ∀ (arms : List (List Stmt)) (j n : ℕ) (base : Cell) (exit : ArmExit)
    (sc : SSt) (acc : Bool) (sc' : SSt) (s : St), scopeArms ctx.retCells arms sc acc = .ok sc' →
    sc.rest.length ≤ ctx.fuel → RS ctx sc.rest sc'.rest s (placeArms arms j n base exit)
  | [], j, n, base, exit, sc, acc, sc', s, h, _ => by
      simp only [scopeArms] at h
      cases h
      rw [placeArms]
      exact RS.keep_bind (RestAt.mod (restR_same rfl)) fun _ _ => RS.keep RestAt.pure
  | arm :: more, j, n, base, exit, sc, acc, sc', s, h, hl => by
      simp only [scopeArms] at h
      split at h
      · cases h
      next s₁ h₁ =>
      have hc : ∀ s₁ s₂, scopeBlock ctx.retCells arm s₁ = .ok s₂ →
          Cons ctx.retCells s₁.rest s₂.rest := scopeBlock_cons _ arm
      have l₁ : s₁.rest.length ≤ ctx.fuel := le_trans (scopeInner_cons hc h₁).len hl
      rw [placeArms]
      refine RS.keep_bind (RestAt.mod (restR_same rfl)) fun _ _ => ?_
      refine RS.step_bind (inBlock_rs (fun s₁ s₂ st h₂ l => placeBlock_rs arm s₁ s₂ st h₂ l) hc h₁ hl)
        fun _ _ => ?_
      have tail : ∀ (lv : List PStmt) (blk : List PStmt) (s₂ : St), RS ctx s₁.rest sc'.rest s₂ (do
          let top := (← get).next
          let blocks ← placeArms more (j + 1) n base exit
          modify fun s => { s with next := max s.next top }
          pure ((blk ++ lv) :: blocks) : P (List (List PStmt))) := fun lv blk s₂ =>
        RS.get_bind (RS.step_bind (placeArms_rs more (j + 1) n base exit
          { s₁ with retDone := sc.retDone } _ sc' s₂ h l₁) fun _ _ =>
            RS.keep_bind (RestAt.mod (restR_same rfl)) fun _ _ => RS.keep RestAt.pure)
      split
      · exact RS.keep_bind fresh_rest fun _ _ => by simp only [pure_bind]; exact tail _ _ _
      · simp only [pure_bind]
        exact tail _ _ _
end

/-- **`BlockRest`**: a block's placement leaves the events its scope walk leaves. -/
theorem blockRest (ss : List Stmt) (st : St) (s s' : SSt)
    (h : scopeBlock ctx.retCells ss s = .ok s') (hr : st.rest = s.rest)
    (hf : st.rest.length ≤ ctx.fuel) :
    wpP (placeBlock ss) ctx st fun _ st' => st'.rest = s'.rest :=
  placeBlock_rs ss s s' st h (by rw [← hr]; exact hf) hr

end Lock

end
end LeanVM.Compiler.Complete
