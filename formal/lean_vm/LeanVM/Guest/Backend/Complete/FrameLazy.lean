/-
  LeanVM.Guest.Backend.Complete.FrameLazy

  A flush over events that make no value lazily keeps the value made lazily.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameLocs
public import LeanVM.Guest.Backend.Complete.Scoped

/-!
# The value made lazily through a flush

Every placement primitive but an `alloc` of a pooled value or an address and a statement's end
keeps the value made lazily (`LzAt`). A flush whose events `lazyFree` accepts passes no such
`alloc`, so it keeps it (`flushLazy`).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

section Lz

variable {ctx : Ctx} {α β : Type}

/-- The value made lazily and the events left as they were. -/
def LzR (st st' : St) : Prop := st'.lazy = st.lazy ∧ st'.rest = st.rest

theorem LzR.refl (st : St) : LzR st st := ⟨rfl, rfl⟩

theorem LzR.trans {st₁ st₂ st₃ : St} (h₁ : LzR st₁ st₂) (h₂ : LzR st₂ st₃) :
    LzR st₁ st₃ := ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

/-- Every success of `m` from `st` keeps the value made lazily. -/
def LzAt (ctx : Ctx) (st : St) (m : P α) : Prop := wpP m ctx st fun _ st' => LzR st st'

variable {st : St}

theorem LzAt.pure {a : α} : LzAt ctx st (Pure.pure a) := wp_pure.mpr (LzR.refl st)

theorem LzAt.fail {msg : String} : LzAt ctx st (failP msg : P α) := wp_failP

theorem LzAt.fail_bind {msg : String} {f : α → P β} :
    LzAt ctx st ((failP msg : P α) >>= f) := wp_bind.mpr wp_failP

theorem LzAt.bind {m : P α} {f : α → P β} (hm : LzAt ctx st m)
    (hf : ∀ a st', LzR st st' → LzAt ctx st' (f a)) : LzAt ctx st (m >>= f) :=
  wp_bind.mpr (wp_mono hm fun a st' h => wp_mono (hf a st' h) fun _ _ h' => h.trans h')

theorem LzAt.get_bind {f : St → P β} (h : LzAt ctx st (f st)) : LzAt ctx st (get >>= f) :=
  wp_bind.mpr (wp_get.mpr h)

theorem LzAt.read_bind {f : Ctx → P β} (h : LzAt ctx st (f ctx)) :
    LzAt ctx st (read >>= f) := wp_bind.mpr (wp_read.mpr h)

theorem LzAt.peek_bind {f : Option Event → P β} (h : LzAt ctx st (f st.rest.head?)) :
    LzAt ctx st (peek >>= f) := wp_bind.mpr (wp_peek.mpr h)

theorem LzAt.guard {c : Prop} [Decidable c] {msg : String} {f : PUnit → P β}
    (h : ¬c → LzAt ctx st (f PUnit.unit)) :
    LzAt ctx st (if c then failP msg >>= f else f PUnit.unit) := by
  split
  · exact LzAt.fail_bind
  · next hc => exact h hc

theorem LzAt.mod {g : St → St} (h : LzR st (g st)) : LzAt ctx st (modify g) :=
  wp_modify.mpr h

theorem LzAt.mod_bind {g : St → St} {f : PUnit → P β} (h : LzR st (g st))
    (hf : LzAt ctx (g st) (f ⟨⟩)) : LzAt ctx st (modify g >>= f) :=
  wp_bind.mpr (wp_modify.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem LzAt.modG {g : St → α × St} (h : LzR st (g st).2) :
    LzAt ctx st (modifyGet g) := wp_modifyGet.mpr h

theorem LzAt.modG_bind {g : St → α × St} {f : α → P β} (h : LzR st (g st).2)
    (hf : LzAt ctx (g st).2 (f (g st).1)) : LzAt ctx st (modifyGet g >>= f) :=
  wp_bind.mpr (wp_modifyGet.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem LzAt.setS {s : St} (h : LzR st s) : LzAt ctx st (set s : P PUnit) := wp_set.mpr h

theorem LzAt.setS_bind {s : St} {f : PUnit → P β} (h : LzR st s) (hf : LzAt ctx s (f ⟨⟩)) :
    LzAt ctx st (set s >>= f) :=
  wp_bind.mpr (wp_set.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem LzAt.discard {m : P α} (h : LzAt ctx st m) : LzAt ctx st (Functor.discard m) := by
  rw [Functor.discard, map_const, Function.comp_apply, map_eq_pure_bind]
  exact LzAt.bind h fun _ _ _ => LzAt.pure

theorem lzR_same {s : St} (h : s.lazy = st.lazy) (h' : s.rest = st.rest) : LzR st s := ⟨h, h'⟩

theorem bindTo_lz (v : V) (l : Loc) : LzAt ctx st (bindTo v l) := by
  unfold bindTo
  refine wp_bind.mpr (wp_get.mpr ?_)
  split
  · exact wp_bind.mpr wp_failP
  · exact wp_modify.mpr ⟨rfl, rfl⟩

theorem forM_lz {γ : Type} {f : γ → P PUnit} (hf : ∀ b st, LzAt ctx st (f b)) :
    ∀ (l : List γ) (st : St), LzAt ctx st (l.forM f)
  | [], _ => LzAt.pure
  | b :: l, st => by
      show LzAt ctx st (f b >>= fun _ => l.forM f)
      exact LzAt.bind (hf b st) fun _ st' _ => forM_lz hf l st'

theorem mapM_lz {γ δ : Type} {f : γ → P δ} (hf : ∀ b st, LzAt ctx st (f b)) :
    ∀ (l : List γ) (st : St), LzAt ctx st (l.mapM f)
  | [], _ => by rw [List.mapM_nil]; exact LzAt.pure
  | b :: l, st => by
      rw [List.mapM_cons]
      exact LzAt.bind (hf b st) fun _ st' _ => LzAt.bind (mapM_lz hf l st') fun _ _ _ =>
        LzAt.pure

theorem optionMapM_lz {γ δ : Type} {f : γ → P δ} (hf : ∀ b st, LzAt ctx st (f b))
    (o : Option γ) (st : St) : LzAt ctx st (o.mapM f) := by
  cases o with
  | none => exact LzAt.pure
  | some v =>
    rw [Option.mapM, map_eq_pure_bind]
    exact LzAt.bind (hf v st) fun _ _ _ => LzAt.pure

end Lz

/-- A primitive already shown to keep the value made lazily. -/
syntax "lz_prim" : tactic

set_option hygiene false in
macro_rules | `(tactic| lz_prim) => `(tactic| first
  | with_reducible refine LzAt.bind fresh_lz fun _ _ _ => ?_
  | with_reducible exact fresh_lz
  | with_reducible refine LzAt.bind pushHint_lz fun _ _ _ => ?_
  | with_reducible exact pushHint_lz
  | with_reducible refine LzAt.bind takeHints_lz fun _ _ _ => ?_
  | with_reducible exact takeHints_lz
  | with_reducible refine LzAt.bind push_lz fun _ _ _ => ?_
  | with_reducible exact push_lz
  | with_reducible refine LzAt.bind emitOp_lz fun _ _ _ => ?_
  | with_reducible exact emitOp_lz
  | with_reducible refine LzAt.bind constCell_lz fun _ _ _ => ?_
  | with_reducible exact constCell_lz
  | with_reducible refine LzAt.bind oneCell_lz fun _ _ _ => ?_
  | with_reducible exact oneCell_lz
  | with_reducible refine LzAt.bind zeroCell_lz fun _ _ _ => ?_
  | with_reducible exact zeroCell_lz
  | with_reducible refine LzAt.bind mulCell_lz fun _ _ _ => ?_
  | with_reducible exact mulCell_lz
  | with_reducible refine LzAt.bind emitDeref_lz fun _ _ _ => ?_
  | with_reducible exact emitDeref_lz
  | with_reducible refine LzAt.bind selfFp_lz fun _ _ _ => ?_
  | with_reducible exact selfFp_lz
  | with_reducible refine LzAt.bind materialize_lz fun _ _ _ => ?_
  | with_reducible exact materialize_lz
  | with_reducible refine LzAt.bind cellAt_lz fun _ _ _ => ?_
  | with_reducible exact cellAt_lz
  | with_reducible refine LzAt.bind cellOf_lz fun _ _ _ => ?_
  | with_reducible exact cellOf_lz
  | with_reducible refine LzAt.bind factor_lz fun _ _ _ => ?_
  | with_reducible exact factor_lz
  | with_reducible refine LzAt.bind pointer_lz fun _ _ _ => ?_
  | with_reducible exact pointer_lz
  | with_reducible refine LzAt.bind pooledCell_lz fun _ _ _ => ?_
  | with_reducible exact pooledCell_lz
  | with_reducible refine LzAt.bind pooled_lz fun _ _ _ => ?_
  | with_reducible exact pooled_lz
  | with_reducible refine LzAt.bind isLazy_lz fun _ _ _ => ?_
  | with_reducible exact isLazy_lz
  | with_reducible refine LzAt.bind isSelfFp_lz fun _ _ _ => ?_
  | with_reducible exact isSelfFp_lz
  | with_reducible refine LzAt.bind bindRun_lz fun _ _ _ => ?_
  | with_reducible exact bindRun_lz
  | with_reducible refine LzAt.bind takeRun_lz fun _ _ _ => ?_
  | with_reducible exact takeRun_lz
  | with_reducible refine LzAt.bind spongeInPlace_lz fun _ _ _ => ?_
  | with_reducible exact spongeInPlace_lz)

/-- One step of a walk that keeps the value made lazily. -/
macro "lz_step" : tactic => `(tactic| first
  | with_reducible exact LzAt.pure
  | with_reducible exact LzAt.fail
  | with_reducible exact LzAt.fail_bind
  | with_reducible refine LzAt.get_bind ?_
  | with_reducible refine LzAt.read_bind ?_
  | with_reducible refine LzAt.peek_bind ?_
  | with_reducible refine LzAt.guard fun _ => ?_
  | with_reducible refine LzAt.mod_bind ?_ ?_
  | with_reducible refine LzAt.modG_bind ?_ ?_
  | with_reducible refine LzAt.setS_bind ?_ ?_
  | with_reducible refine LzAt.mod ?_
  | with_reducible refine LzAt.modG ?_
  | with_reducible refine LzAt.setS ?_
  | exact lzR_same rfl rfl
  | exact LzR.refl _
  | with_reducible refine LzAt.bind (bindTo_lz _ _) fun _ _ _ => ?_
  | with_reducible exact bindTo_lz _ _
  | with_reducible refine LzAt.bind (forM_lz ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine LzAt.bind (mapM_lz ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine LzAt.bind (optionMapM_lz ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine LzAt.bind (‹∀ st, LzAt _ st _› _) fun _ _ _ => ?_
  | with_reducible exact ‹∀ st, LzAt _ st _› _
  | with_reducible refine LzAt.discard ?_
  | with_reducible refine LzAt.bind (LzAt.discard ?_) fun _ _ _ => ?_
  | lz_prim
  | dsimp only
  | rw [pure_bind]
  | split)

macro "lz_straight" : tactic => `(tactic| repeat' lz_step)


section LzPrims

variable {ctx : Ctx} {st : St}

theorem fresh_lz : LzAt ctx st fresh := by
  unfold fresh
  exact LzAt.modG (lzR_same rfl rfl)


theorem pushHint_lz {h : LHint} : LzAt ctx st (pushHint h) := by
  unfold pushHint
  lz_straight


theorem takeHints_lz  : LzAt ctx st (takeHints) := by
  unfold takeHints
  lz_straight


theorem push_lz {s : PStmt} : LzAt ctx st (push s) := by
  unfold push
  lz_straight


theorem emitOp_lz {o : LOp} : LzAt ctx st (emitOp o) := by
  unfold emitOp
  lz_straight


theorem constCell_lz {k : ℕ × ℕ} : LzAt ctx st (constCell k) := by
  unfold constCell
  lz_straight


theorem oneCell_lz  : LzAt ctx st (oneCell) := by
  unfold oneCell
  lz_straight


theorem zeroCell_lz  : LzAt ctx st (zeroCell) := by
  unfold zeroCell
  lz_straight


theorem mulCell_lz {a b : Cell} : LzAt ctx st (mulCell a b) := by
  unfold mulCell
  lz_straight


theorem emitDeref_lz {p off d : Cell} : LzAt ctx st (emitDeref p off d) := by
  unfold emitDeref
  lz_straight


theorem selfFp_lz  : LzAt ctx st (selfFp) := by
  unfold selfFp
  lz_straight


theorem materialize_lz {c e : Cell} : LzAt ctx st (materialize c e) := by
  unfold materialize
  lz_straight


theorem cellAt_lz {v : V} : LzAt ctx st (cellAt v) := by
  unfold cellAt
  lz_straight


theorem cellOf_lz {v : V} : LzAt ctx st (cellOf v) := by
  unfold cellOf
  lz_straight


theorem factor_lz {v : V} : LzAt ctx st (factor v) := by
  unfold factor
  lz_straight


theorem pointer_lz {p : V} {off : ℕ} : LzAt ctx st (pointer p off) := by
  unfold pointer
  lz_straight


theorem pooledCell_lz {find : Scope → Option Cell} {learn : Cell → Scope → Scope} {mk : Cell → LOp} : LzAt ctx st (pooledCell find learn mk) := by
  unfold pooledCell
  lz_straight


theorem pooled_lz {d : V} {find : Scope → Option Cell} {learn : Cell → Scope → Scope} {mk : Cell → LOp} : LzAt ctx st (pooled d find learn mk) := by
  unfold pooled
  lz_straight


theorem isLazy_lz {v : V} {k : Kind} : LzAt ctx st (isLazy v k) := by
  unfold isLazy
  lz_straight


theorem isSelfFp_lz {n : Cell} : LzAt ctx st (isSelfFp n) := by
  unfold isSelfFp
  lz_straight


theorem bindRun_lz {vs : List V} {base : Cell} : LzAt ctx st (bindRun vs base) := by
  unfold bindRun
  exact forM_lz (fun _ _ => bindTo_lz _ _) _ _


theorem takeRun_lz {vs : List V} : LzAt ctx st (takeRun vs) := by
  unfold takeRun
  lz_straight

theorem spongeInPlace_lz {vs : List V} {up : List Stmt} : LzAt ctx st (spongeInPlace vs up) := by
  unfold spongeInPlace
  lz_straight

end LzPrims

section Flush

variable {ctx : Ctx}

theorem onAlloc_lz {vs : List V} {kind : Kind} {up : List Stmt} {st : St} (h1 : kind ≠ .pooled)
    (h2 : kind ≠ .addr) : LzAt ctx st (onAlloc vs kind up) := by
  unfold onAlloc
  cases kind
  all_goals first | exact absurd rfl h1 | exact absurd rfl h2 | (dsimp only; lz_straight)

/-- **A flush over events that make no value lazily** keeps the value made lazily. -/
theorem flushN_lazy {up : List Stmt} : ∀ (fuel : ℕ) (st : St), lazyFree st.rest = true →
    wpP (flushN up fuel) ctx st fun _ st' => st'.lazy = st.lazy
  | 0, _, _ => by unfold flushN; exact wp_pure.mpr rfl
  | fuel + 1, st, hf => by
      unfold flushN advance
      refine wp_bind.mpr (wp_peek.mpr ?_)
      cases hr : st.rest with
      | nil => exact wp_pure.mpr rfl
      | cons e es =>
        rw [hr] at hf
        simp only [List.head?_cons]
        cases e with
        | alloc vs kind =>
          have hk : kind ≠ .pooled ∧ kind ≠ .addr := by
            constructor <;> rintro rfl <;> simp [lazyFree] at hf
          have hf' : lazyFree es = true := by
            cases kind <;> simp_all [lazyFree]
          dsimp only
          refine wp_bind.mpr (wp_modify.mpr (wp_bind.mpr (wp_mono (onAlloc_lz hk.1 hk.2)
            fun _ s hs => wp_mono (flushN_lazy fuel s (by rw [hs.2, hr]; exact hf')) fun _ _ h =>
              h.trans hs.1)))
        | use v =>
          have hf' : lazyFree es = true := by simpa [lazyFree] using hf
          dsimp only
          refine wp_bind.mpr (wp_modify.mpr (wp_bind.mpr ?_))
          have hk : ∀ (s : St), s.lazy = st.lazy → s.rest = es →
              wpP (modify (fun s => { s with used := v :: s.used }) >>= fun _ => flushN up fuel)
                ctx s fun _ st' => st'.lazy = st.lazy := fun s h1 h2 =>
            wp_bind.mpr (wp_modify.mpr (wp_mono (flushN_lazy fuel _ (by rw [← h2] at hf'; exact hf'))
              fun _ _ h => h.trans h1))
          refine wp_get.mpr ?_
          split
          · exact wp_bind.mpr (wp_mono (LzAt.discard materialize_lz) fun _ s hs =>
              hk s hs.1 (by rw [hs.2]; simp [hr]))
          · exact hk _ rfl (by simp [hr])
        | shift v exp =>
          have hf' : lazyFree es = true := by simpa [lazyFree] using hf
          exact wp_bind.mpr (wp_modify.mpr (wp_bind.mpr (wp_modify.mpr
            (flushN_lazy fuel _ (by simp only [hr, List.tail_cons]; exact hf')))))
        | chain =>
          have hf' : lazyFree es = true := by simpa [lazyFree] using hf
          exact wp_bind.mpr (wp_modify.mpr (wp_bind.mpr (wp_modify.mpr
            (flushN_lazy fuel _ (by simp only [hr, List.tail_cons]; exact hf')))))
        | note n =>
          have hf' : lazyFree es = true := by simpa [lazyFree] using hf
          exact wp_bind.mpr (wp_modify.mpr (wp_bind.mpr (wp_modify.mpr
            (flushN_lazy fuel _ (by simp only [hr, List.tail_cons]; exact hf')))))
        | _ => exact wp_pure.mpr rfl

/-- **`FlushLazy`**: a flush over events that make no value lazily keeps the value made lazily. -/
theorem flushLazy (up : List Stmt) (st : St) (h : lazyFree st.rest = true) :
    wpP (flush up) ctx st fun _ st' => st'.lazy = st.lazy := by
  unfold flush
  exact wp_bind.mpr (wp_read.mpr (flushN_lazy _ st h))

end Flush

end
end LeanVM.Guest.Backend.Complete
