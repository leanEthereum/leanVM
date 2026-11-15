/-
  LeanVM.Guest.Backend.Complete.FrameOpOut

  A flush and a `match`'s cells extend the output by straight-line instructions only.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameOut

/-!
# Straight-line output

`OpAt`: every success only appends straight-line instructions (`.op`) to the output. Every
placement primitive but `push` of a control statement emits through `emitOp`, so a flush
(`flush_op`) and a `match`'s cells (`matchCells_op`) do.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

section Op

variable {ctx : Ctx} {α β : Type}

/-- The output only extended, by straight-line instructions. -/
def OpR (st st' : St) : Prop :=
  ∃ ops : List PStmt, st'.out.toList = st.out.toList ++ ops ∧ ∀ s ∈ ops, ∃ h o, s = PStmt.op h o

theorem OpR.refl (st : St) : OpR st st := ⟨[], by simp, fun _ h => nomatch h⟩

theorem OpR.trans {st₁ st₂ st₃ : St} (h₁ : OpR st₁ st₂) (h₂ : OpR st₂ st₃) :
    OpR st₁ st₃ := by
  obtain ⟨b₁, h₁, w₁⟩ := h₁
  obtain ⟨b₂, h₂, w₂⟩ := h₂
  exact ⟨b₁ ++ b₂, by rw [h₂, h₁, List.append_assoc], fun s hs =>
    (List.mem_append.mp hs).elim (w₁ s) (w₂ s)⟩

/-- Every success of `m` from `st` only extends the output by straight-line instructions. -/
def OpAt (ctx : Ctx) (st : St) (m : P α) : Prop := wpP m ctx st fun _ st' => OpR st st'

variable {st : St}

theorem OpAt.pure {a : α} : OpAt ctx st (Pure.pure a) := wp_pure.mpr (OpR.refl st)

theorem OpAt.fail {msg : String} : OpAt ctx st (failP msg : P α) := wp_failP

theorem OpAt.fail_bind {msg : String} {f : α → P β} :
    OpAt ctx st ((failP msg : P α) >>= f) := wp_bind.mpr wp_failP

theorem OpAt.bind {m : P α} {f : α → P β} (hm : OpAt ctx st m)
    (hf : ∀ a st', OpR st st' → OpAt ctx st' (f a)) : OpAt ctx st (m >>= f) :=
  wp_bind.mpr (wp_mono hm fun a st' h => wp_mono (hf a st' h) fun _ _ h' => h.trans h')

theorem OpAt.get_bind {f : St → P β} (h : OpAt ctx st (f st)) : OpAt ctx st (get >>= f) :=
  wp_bind.mpr (wp_get.mpr h)

theorem OpAt.read_bind {f : Ctx → P β} (h : OpAt ctx st (f ctx)) :
    OpAt ctx st (read >>= f) := wp_bind.mpr (wp_read.mpr h)

theorem OpAt.peek_bind {f : Option Event → P β} (h : OpAt ctx st (f st.rest.head?)) :
    OpAt ctx st (peek >>= f) := wp_bind.mpr (wp_peek.mpr h)

theorem OpAt.guard {c : Prop} [Decidable c] {msg : String} {f : PUnit → P β}
    (h : ¬c → OpAt ctx st (f PUnit.unit)) :
    OpAt ctx st (if c then failP msg >>= f else f PUnit.unit) := by
  split
  · exact OpAt.fail_bind
  · next hc => exact h hc

theorem OpAt.mod {g : St → St} (h : OpR st (g st)) : OpAt ctx st (modify g) :=
  wp_modify.mpr h

theorem OpAt.mod_bind {g : St → St} {f : PUnit → P β} (h : OpR st (g st))
    (hf : OpAt ctx (g st) (f ⟨⟩)) : OpAt ctx st (modify g >>= f) :=
  wp_bind.mpr (wp_modify.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem OpAt.modG {g : St → α × St} (h : OpR st (g st).2) :
    OpAt ctx st (modifyGet g) := wp_modifyGet.mpr h

theorem OpAt.modG_bind {g : St → α × St} {f : α → P β} (h : OpR st (g st).2)
    (hf : OpAt ctx (g st).2 (f (g st).1)) : OpAt ctx st (modifyGet g >>= f) :=
  wp_bind.mpr (wp_modifyGet.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem OpAt.setS {s : St} (h : OpR st s) : OpAt ctx st (set s : P PUnit) := wp_set.mpr h

theorem OpAt.setS_bind {s : St} {f : PUnit → P β} (h : OpR st s) (hf : OpAt ctx s (f ⟨⟩)) :
    OpAt ctx st (set s >>= f) :=
  wp_bind.mpr (wp_set.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem OpAt.discard {m : P α} (h : OpAt ctx st m) : OpAt ctx st (Functor.discard m) := by
  rw [Functor.discard, map_const, Function.comp_apply, map_eq_pure_bind]
  exact OpAt.bind h fun _ _ _ => OpAt.pure

theorem opR_same {s : St} (h : s.out = st.out) : OpR st s :=
  ⟨[], by rw [h]; simp, fun _ h => nomatch h⟩

theorem opR_pushOp {s : St} {hs : List LHint} {o : LOp} (h : s.out = st.out.push (.op hs o)) :
    OpR st s :=
  ⟨[.op hs o], by rw [h]; simp, fun s hm => by
    rw [List.mem_singleton] at hm
    exact ⟨hs, o, hm⟩⟩

theorem bindTo_op (v : V) (l : Loc) : OpAt ctx st (bindTo v l) := by
  unfold bindTo
  refine wp_bind.mpr (wp_get.mpr ?_)
  split
  · exact wp_bind.mpr wp_failP
  · exact wp_modify.mpr (opR_same rfl)

theorem forM_op {γ : Type} {f : γ → P PUnit} (hf : ∀ b st, OpAt ctx st (f b)) :
    ∀ (l : List γ) (st : St), OpAt ctx st (l.forM f)
  | [], _ => OpAt.pure
  | b :: l, st => by
      show OpAt ctx st (f b >>= fun _ => l.forM f)
      exact OpAt.bind (hf b st) fun _ st' _ => forM_op hf l st'

theorem mapM_op {γ δ : Type} {f : γ → P δ} (hf : ∀ b st, OpAt ctx st (f b)) :
    ∀ (l : List γ) (st : St), OpAt ctx st (l.mapM f)
  | [], _ => by rw [List.mapM_nil]; exact OpAt.pure
  | b :: l, st => by
      rw [List.mapM_cons]
      exact OpAt.bind (hf b st) fun _ st' _ => OpAt.bind (mapM_op hf l st') fun _ _ _ =>
        OpAt.pure

theorem optionMapM_op {γ δ : Type} {f : γ → P δ} (hf : ∀ b st, OpAt ctx st (f b))
    (o : Option γ) (st : St) : OpAt ctx st (o.mapM f) := by
  cases o with
  | none => exact OpAt.pure
  | some v =>
    rw [Option.mapM, map_eq_pure_bind]
    exact OpAt.bind (hf v st) fun _ _ _ => OpAt.pure

end Op

/-- A primitive already shown to only extend the output. -/
syntax "op_prim" : tactic

set_option hygiene false in
macro_rules | `(tactic| op_prim) => `(tactic| first
  | with_reducible refine OpAt.bind fresh_op fun _ _ _ => ?_
  | with_reducible exact fresh_op
  | with_reducible refine OpAt.bind pushHint_op fun _ _ _ => ?_
  | with_reducible exact pushHint_op
  | with_reducible refine OpAt.bind takeHints_op fun _ _ _ => ?_
  | with_reducible exact takeHints_op
  | with_reducible refine OpAt.bind pushOp_op fun _ _ _ => ?_
  | with_reducible exact pushOp_op
  | with_reducible refine OpAt.bind emitOp_op fun _ _ _ => ?_
  | with_reducible exact emitOp_op
  | with_reducible refine OpAt.bind constCell_op fun _ _ _ => ?_
  | with_reducible exact constCell_op
  | with_reducible refine OpAt.bind oneCell_op fun _ _ _ => ?_
  | with_reducible exact oneCell_op
  | with_reducible refine OpAt.bind zeroCell_op fun _ _ _ => ?_
  | with_reducible exact zeroCell_op
  | with_reducible refine OpAt.bind mulCell_op fun _ _ _ => ?_
  | with_reducible exact mulCell_op
  | with_reducible refine OpAt.bind emitDeref_op fun _ _ _ => ?_
  | with_reducible exact emitDeref_op
  | with_reducible refine OpAt.bind selfFp_op fun _ _ _ => ?_
  | with_reducible exact selfFp_op
  | with_reducible refine OpAt.bind materialize_op fun _ _ _ => ?_
  | with_reducible exact materialize_op
  | with_reducible refine OpAt.bind cellAt_op fun _ _ _ => ?_
  | with_reducible exact cellAt_op
  | with_reducible refine OpAt.bind cellOf_op fun _ _ _ => ?_
  | with_reducible exact cellOf_op
  | with_reducible refine OpAt.bind factor_op fun _ _ _ => ?_
  | with_reducible exact factor_op
  | with_reducible refine OpAt.bind pointer_op fun _ _ _ => ?_
  | with_reducible exact pointer_op
  | with_reducible refine OpAt.bind pooledCell_op fun _ _ _ => ?_
  | with_reducible exact pooledCell_op
  | with_reducible refine OpAt.bind pooled_op fun _ _ _ => ?_
  | with_reducible exact pooled_op
  | with_reducible refine OpAt.bind isLazy_op fun _ _ _ => ?_
  | with_reducible exact isLazy_op
  | with_reducible refine OpAt.bind isSelfFp_op fun _ _ _ => ?_
  | with_reducible exact isSelfFp_op
  | with_reducible refine OpAt.bind advance_op fun _ _ _ => ?_
  | with_reducible exact advance_op
  | with_reducible refine OpAt.bind expect_op fun _ _ _ => ?_
  | with_reducible exact expect_op
  | with_reducible refine OpAt.bind endStmt_op fun _ _ _ => ?_
  | with_reducible exact endStmt_op
  | with_reducible refine OpAt.bind bindRun_op fun _ _ _ => ?_
  | with_reducible exact bindRun_op
  | with_reducible refine OpAt.bind takeRun_op fun _ _ _ => ?_
  | with_reducible exact takeRun_op
  | with_reducible refine OpAt.bind spongeInPlace_op fun _ _ _ => ?_
  | with_reducible exact spongeInPlace_op
  | with_reducible refine OpAt.bind onAlloc_op fun _ _ _ => ?_
  | with_reducible exact onAlloc_op
  | with_reducible refine OpAt.bind flushN_op fun _ _ _ => ?_
  | with_reducible exact flushN_op
  | with_reducible refine OpAt.bind flush_op fun _ _ _ => ?_
  | with_reducible exact flush_op
  | with_reducible refine OpAt.bind matchCells_op fun _ _ _ => ?_
  | with_reducible exact matchCells_op)

/-- One step of a walk that only extends the output. -/
macro "op_step" : tactic => `(tactic| first
  | with_reducible exact OpAt.pure
  | with_reducible exact OpAt.fail
  | with_reducible exact OpAt.fail_bind
  | with_reducible refine OpAt.get_bind ?_
  | with_reducible refine OpAt.read_bind ?_
  | with_reducible refine OpAt.peek_bind ?_
  | with_reducible refine OpAt.guard fun _ => ?_
  | with_reducible refine OpAt.mod_bind ?_ ?_
  | with_reducible refine OpAt.modG_bind ?_ ?_
  | with_reducible refine OpAt.setS_bind ?_ ?_
  | with_reducible refine OpAt.mod ?_
  | with_reducible refine OpAt.modG ?_
  | with_reducible refine OpAt.setS ?_
  | exact opR_same rfl
  | exact OpR.refl _
  | with_reducible refine OpAt.bind (bindTo_op _ _) fun _ _ _ => ?_
  | with_reducible exact bindTo_op _ _
  | with_reducible refine OpAt.bind (forM_op ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine OpAt.bind (mapM_op ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine OpAt.bind (optionMapM_op ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine OpAt.bind (‹∀ st, OpAt _ st _› _) fun _ _ _ => ?_
  | with_reducible exact ‹∀ st, OpAt _ st _› _
  | with_reducible refine OpAt.discard ?_
  | with_reducible refine OpAt.bind (OpAt.discard ?_) fun _ _ _ => ?_
  | op_prim
  | dsimp only
  | rw [pure_bind]
  | split)

macro "op_straight" : tactic => `(tactic| repeat' op_step)

section OPrims

variable {ctx : Ctx} {st : St}

theorem fresh_op : OpAt ctx st fresh := by
  unfold fresh
  exact OpAt.modG (opR_same rfl)


theorem pushHint_op {h : LHint} : OpAt ctx st (pushHint h) := by
  unfold pushHint
  op_straight


theorem takeHints_op  : OpAt ctx st (takeHints) := by
  unfold takeHints
  op_straight


theorem pushOp_op {hs : List LHint} {o : LOp} : OpAt ctx st (push (.op hs o)) := by
  unfold push
  exact OpAt.mod (opR_pushOp rfl)


theorem emitOp_op {o : LOp} : OpAt ctx st (emitOp o) := by
  unfold emitOp
  op_straight


theorem constCell_op {k : ℕ × ℕ} : OpAt ctx st (constCell k) := by
  unfold constCell
  op_straight


theorem oneCell_op  : OpAt ctx st (oneCell) := by
  unfold oneCell
  op_straight


theorem zeroCell_op  : OpAt ctx st (zeroCell) := by
  unfold zeroCell
  op_straight


theorem mulCell_op {a b : Cell} : OpAt ctx st (mulCell a b) := by
  unfold mulCell
  op_straight


theorem emitDeref_op {p off d : Cell} : OpAt ctx st (emitDeref p off d) := by
  unfold emitDeref
  op_straight


theorem selfFp_op  : OpAt ctx st (selfFp) := by
  unfold selfFp
  op_straight


theorem materialize_op {c e : Cell} : OpAt ctx st (materialize c e) := by
  unfold materialize
  op_straight


theorem cellAt_op {v : V} : OpAt ctx st (cellAt v) := by
  unfold cellAt
  op_straight


theorem cellOf_op {v : V} : OpAt ctx st (cellOf v) := by
  unfold cellOf
  op_straight


theorem factor_op {v : V} : OpAt ctx st (factor v) := by
  unfold factor
  op_straight


theorem pointer_op {p : V} {off : ℕ} : OpAt ctx st (pointer p off) := by
  unfold pointer
  op_straight


theorem pooledCell_op {find : Scope → Option Cell} {learn : Cell → Scope → Scope} {mk : Cell → LOp} : OpAt ctx st (pooledCell find learn mk) := by
  unfold pooledCell
  op_straight


theorem pooled_op {d : V} {find : Scope → Option Cell} {learn : Cell → Scope → Scope} {mk : Cell → LOp} : OpAt ctx st (pooled d find learn mk) := by
  unfold pooled
  op_straight


theorem isLazy_op {v : V} {k : Kind} : OpAt ctx st (isLazy v k) := by
  unfold isLazy
  op_straight


theorem isSelfFp_op {n : Cell} : OpAt ctx st (isSelfFp n) := by
  unfold isSelfFp
  op_straight


theorem advance_op  : OpAt ctx st (advance) := by
  unfold advance
  op_straight


theorem expect_op {e : Event → Bool} {what : String} : OpAt ctx st (expect e what) := by
  unfold expect
  op_straight


theorem endStmt_op  : OpAt ctx st (endStmt) := by
  unfold endStmt
  op_straight


theorem bindRun_op {vs : List V} {base : Cell} : OpAt ctx st (bindRun vs base) := by
  unfold bindRun
  exact forM_op (fun _ _ => bindTo_op _ _) _ _


theorem takeRun_op {vs : List V} : OpAt ctx st (takeRun vs) := by
  unfold takeRun
  op_straight

theorem spongeInPlace_op {vs : List V} {up : List Stmt} : OpAt ctx st (spongeInPlace vs up) := by
  unfold spongeInPlace
  op_straight


theorem onAlloc_op {vs : List V} {k : Kind} {up : List Stmt} : OpAt ctx st (onAlloc vs k up) := by
  unfold onAlloc
  op_straight


theorem flushN_op {up : List Stmt} : ∀ {fuel : ℕ} {st : St}, OpAt ctx st (flushN up fuel)
  | 0, _ => by unfold flushN; exact OpAt.pure
  | fuel + 1, st => by
      have ih : ∀ st, OpAt ctx st (flushN up fuel) := fun _ => flushN_op
      unfold flushN
      repeat' (first | exact ih _ | op_step)

theorem flush_op {up : List Stmt} : OpAt ctx st (flush up) := by
  unfold flush
  op_straight

theorem matchCells_op {x : V} {rest : List Stmt} {chained : Bool} :
    OpAt ctx st (matchCells x rest chained) := by
  unfold matchCells
  op_straight

end OPrims

end

end LeanVM.Guest.Backend.Complete
