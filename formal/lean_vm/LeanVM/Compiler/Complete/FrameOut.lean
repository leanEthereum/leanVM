/-
  LeanVM.Compiler.Complete.FrameOut

  A block's placement only extends the output, and from a state no `match` chains into, no `match`
  chains out of it.
-/

module

public import LeanVM.Compiler.Complete.FrameLocs
public import LeanVM.Compiler.Complete.FrameBlock

/-!
# The output of a block

Every placement primitive only appends to the output (`AppAt`), as `FrameLocs.lean` shows the next
free cell and the places only grow. A block in a scope of its own and the arms of a `match` give
the output back. The one step that takes a node back is an entered `match`, which replaces the
chain node the `match` before it pushed last: while a `match` chains out (`chainIn` set), the
statements after it start with a `match` and the output since the block's start is not empty
(`OutJ`). So a block from a state no `match` chains into ends with no `match` chaining out and its
output extended (`placeMono : PlaceMono ctx`).
-/

namespace LeanVM.Compiler.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

section App

variable {ctx : Ctx} {α β : Type}

/-- The output only extended. -/
def AppR (st st' : St) : Prop := ∃ blk, st'.out.toList = st.out.toList ++ blk

theorem AppR.refl (st : St) : AppR st st := ⟨[], by simp⟩

theorem AppR.trans {st₁ st₂ st₃ : St} (h₁ : AppR st₁ st₂) (h₂ : AppR st₂ st₃) :
    AppR st₁ st₃ := by
  obtain ⟨b₁, h₁⟩ := h₁
  obtain ⟨b₂, h₂⟩ := h₂
  exact ⟨b₁ ++ b₂, by rw [h₂, h₁, List.append_assoc]⟩

/-- Every success of `m` from `st` only extends the output. -/
def AppAt (ctx : Ctx) (st : St) (m : P α) : Prop := wpP m ctx st fun _ st' => AppR st st'

variable {st : St}

theorem AppAt.pure {a : α} : AppAt ctx st (Pure.pure a) := wp_pure.mpr (AppR.refl st)

theorem AppAt.fail {msg : String} : AppAt ctx st (failP msg : P α) := wp_failP

theorem AppAt.fail_bind {msg : String} {f : α → P β} :
    AppAt ctx st ((failP msg : P α) >>= f) := wp_bind.mpr wp_failP

theorem AppAt.bind {m : P α} {f : α → P β} (hm : AppAt ctx st m)
    (hf : ∀ a st', AppR st st' → AppAt ctx st' (f a)) : AppAt ctx st (m >>= f) :=
  wp_bind.mpr (wp_mono hm fun a st' h => wp_mono (hf a st' h) fun _ _ h' => h.trans h')

theorem AppAt.get_bind {f : St → P β} (h : AppAt ctx st (f st)) : AppAt ctx st (get >>= f) :=
  wp_bind.mpr (wp_get.mpr h)

theorem AppAt.read_bind {f : Ctx → P β} (h : AppAt ctx st (f ctx)) :
    AppAt ctx st (read >>= f) := wp_bind.mpr (wp_read.mpr h)

theorem AppAt.peek_bind {f : Option Event → P β} (h : AppAt ctx st (f st.rest.head?)) :
    AppAt ctx st (peek >>= f) := wp_bind.mpr (wp_peek.mpr h)

theorem AppAt.guard {c : Prop} [Decidable c] {msg : String} {f : PUnit → P β}
    (h : ¬c → AppAt ctx st (f PUnit.unit)) :
    AppAt ctx st (if c then failP msg >>= f else f PUnit.unit) := by
  split
  · exact AppAt.fail_bind
  · next hc => exact h hc

theorem AppAt.mod {g : St → St} (h : AppR st (g st)) : AppAt ctx st (modify g) :=
  wp_modify.mpr h

theorem AppAt.mod_bind {g : St → St} {f : PUnit → P β} (h : AppR st (g st))
    (hf : AppAt ctx (g st) (f ⟨⟩)) : AppAt ctx st (modify g >>= f) :=
  wp_bind.mpr (wp_modify.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem AppAt.modG {g : St → α × St} (h : AppR st (g st).2) :
    AppAt ctx st (modifyGet g) := wp_modifyGet.mpr h

theorem AppAt.modG_bind {g : St → α × St} {f : α → P β} (h : AppR st (g st).2)
    (hf : AppAt ctx (g st).2 (f (g st).1)) : AppAt ctx st (modifyGet g >>= f) :=
  wp_bind.mpr (wp_modifyGet.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem AppAt.setS {s : St} (h : AppR st s) : AppAt ctx st (set s : P PUnit) := wp_set.mpr h

theorem AppAt.setS_bind {s : St} {f : PUnit → P β} (h : AppR st s) (hf : AppAt ctx s (f ⟨⟩)) :
    AppAt ctx st (set s >>= f) :=
  wp_bind.mpr (wp_set.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem AppAt.discard {m : P α} (h : AppAt ctx st m) : AppAt ctx st (Functor.discard m) := by
  rw [Functor.discard, map_const, Function.comp_apply, map_eq_pure_bind]
  exact AppAt.bind h fun _ _ _ => AppAt.pure

theorem appR_same {s : St} (h : s.out = st.out) : AppR st s := ⟨[], by rw [h]; simp⟩

theorem appR_push {s : St} {x : PStmt} (h : s.out = st.out.push x) : AppR st s :=
  ⟨[x], by rw [h]; simp⟩

theorem bindTo_app (v : V) (l : Loc) : AppAt ctx st (bindTo v l) := by
  unfold bindTo
  refine wp_bind.mpr (wp_get.mpr ?_)
  split
  · exact wp_bind.mpr wp_failP
  · exact wp_modify.mpr (appR_same rfl)

theorem forM_app {γ : Type} {f : γ → P PUnit} (hf : ∀ b st, AppAt ctx st (f b)) :
    ∀ (l : List γ) (st : St), AppAt ctx st (l.forM f)
  | [], _ => AppAt.pure
  | b :: l, st => by
      show AppAt ctx st (f b >>= fun _ => l.forM f)
      exact AppAt.bind (hf b st) fun _ st' _ => forM_app hf l st'

theorem mapM_app {γ δ : Type} {f : γ → P δ} (hf : ∀ b st, AppAt ctx st (f b)) :
    ∀ (l : List γ) (st : St), AppAt ctx st (l.mapM f)
  | [], _ => by rw [List.mapM_nil]; exact AppAt.pure
  | b :: l, st => by
      rw [List.mapM_cons]
      exact AppAt.bind (hf b st) fun _ st' _ => AppAt.bind (mapM_app hf l st') fun _ _ _ =>
        AppAt.pure

theorem optionMapM_app {γ δ : Type} {f : γ → P δ} (hf : ∀ b st, AppAt ctx st (f b))
    (o : Option γ) (st : St) : AppAt ctx st (o.mapM f) := by
  cases o with
  | none => exact AppAt.pure
  | some v =>
    rw [Option.mapM, map_eq_pure_bind]
    exact AppAt.bind (hf v st) fun _ _ _ => AppAt.pure

end App

/-- A primitive already shown to only extend the output. -/
syntax "app_prim" : tactic

set_option hygiene false in
macro_rules | `(tactic| app_prim) => `(tactic| first
  | with_reducible refine AppAt.bind fresh_app fun _ _ _ => ?_
  | with_reducible exact fresh_app
  | with_reducible refine AppAt.bind pushHint_app fun _ _ _ => ?_
  | with_reducible exact pushHint_app
  | with_reducible refine AppAt.bind takeHints_app fun _ _ _ => ?_
  | with_reducible exact takeHints_app
  | with_reducible refine AppAt.bind push_app fun _ _ _ => ?_
  | with_reducible exact push_app
  | with_reducible refine AppAt.bind emitOp_app fun _ _ _ => ?_
  | with_reducible exact emitOp_app
  | with_reducible refine AppAt.bind constCell_app fun _ _ _ => ?_
  | with_reducible exact constCell_app
  | with_reducible refine AppAt.bind oneCell_app fun _ _ _ => ?_
  | with_reducible exact oneCell_app
  | with_reducible refine AppAt.bind zeroCell_app fun _ _ _ => ?_
  | with_reducible exact zeroCell_app
  | with_reducible refine AppAt.bind mulCell_app fun _ _ _ => ?_
  | with_reducible exact mulCell_app
  | with_reducible refine AppAt.bind emitDeref_app fun _ _ _ => ?_
  | with_reducible exact emitDeref_app
  | with_reducible refine AppAt.bind selfFp_app fun _ _ _ => ?_
  | with_reducible exact selfFp_app
  | with_reducible refine AppAt.bind materialize_app fun _ _ _ => ?_
  | with_reducible exact materialize_app
  | with_reducible refine AppAt.bind cellAt_app fun _ _ _ => ?_
  | with_reducible exact cellAt_app
  | with_reducible refine AppAt.bind cellOf_app fun _ _ _ => ?_
  | with_reducible exact cellOf_app
  | with_reducible refine AppAt.bind factor_app fun _ _ _ => ?_
  | with_reducible exact factor_app
  | with_reducible refine AppAt.bind pointer_app fun _ _ _ => ?_
  | with_reducible exact pointer_app
  | with_reducible refine AppAt.bind pooledCell_app fun _ _ _ => ?_
  | with_reducible exact pooledCell_app
  | with_reducible refine AppAt.bind pooled_app fun _ _ _ => ?_
  | with_reducible exact pooled_app
  | with_reducible refine AppAt.bind isLazy_app fun _ _ _ => ?_
  | with_reducible exact isLazy_app
  | with_reducible refine AppAt.bind isSelfFp_app fun _ _ _ => ?_
  | with_reducible exact isSelfFp_app
  | with_reducible refine AppAt.bind advance_app fun _ _ _ => ?_
  | with_reducible exact advance_app
  | with_reducible refine AppAt.bind expect_app fun _ _ _ => ?_
  | with_reducible exact expect_app
  | with_reducible refine AppAt.bind endStmt_app fun _ _ _ => ?_
  | with_reducible exact endStmt_app
  | with_reducible refine AppAt.bind bindRun_app fun _ _ _ => ?_
  | with_reducible exact bindRun_app
  | with_reducible refine AppAt.bind takeRun_app fun _ _ _ => ?_
  | with_reducible exact takeRun_app
  | with_reducible refine AppAt.bind spongeInPlace_app fun _ _ _ => ?_
  | with_reducible exact spongeInPlace_app
  | with_reducible refine AppAt.bind onAlloc_app fun _ _ _ => ?_
  | with_reducible exact onAlloc_app
  | with_reducible refine AppAt.bind flushN_app fun _ _ _ => ?_
  | with_reducible exact flushN_app
  | with_reducible refine AppAt.bind flush_app fun _ _ _ => ?_
  | with_reducible exact flush_app
  | with_reducible refine AppAt.bind beginStmt_app fun _ _ _ => ?_
  | with_reducible exact beginStmt_app
  | with_reducible refine AppAt.bind destBits_app fun _ _ _ => ?_
  | with_reducible exact destBits_app
  | with_reducible refine AppAt.bind placeHint_app fun _ _ _ => ?_
  | with_reducible exact placeHint_app
  | with_reducible refine AppAt.bind placeAtom_app fun _ _ _ => ?_
  | with_reducible exact placeAtom_app
  | with_reducible refine AppAt.bind allocTable_app fun _ _ _ => ?_
  | with_reducible exact allocTable_app
  | with_reducible refine AppAt.bind sharedTable_app fun _ _ _ => ?_
  | with_reducible exact sharedTable_app
  | with_reducible refine AppAt.bind loopCount_app fun _ _ _ => ?_
  | with_reducible exact loopCount_app
  | with_reducible refine AppAt.bind placeCall_app fun _ _ _ => ?_
  | with_reducible exact placeCall_app
  | with_reducible refine AppAt.bind matchCells_app fun _ _ _ => ?_
  | with_reducible exact matchCells_app)

/-- One step of a walk that only extends the output. -/
macro "app_step" : tactic => `(tactic| first
  | with_reducible exact AppAt.pure
  | with_reducible exact AppAt.fail
  | with_reducible exact AppAt.fail_bind
  | with_reducible refine AppAt.get_bind ?_
  | with_reducible refine AppAt.read_bind ?_
  | with_reducible refine AppAt.peek_bind ?_
  | with_reducible refine AppAt.guard fun _ => ?_
  | with_reducible refine AppAt.mod_bind ?_ ?_
  | with_reducible refine AppAt.modG_bind ?_ ?_
  | with_reducible refine AppAt.setS_bind ?_ ?_
  | with_reducible refine AppAt.mod ?_
  | with_reducible refine AppAt.modG ?_
  | with_reducible refine AppAt.setS ?_
  | exact appR_same rfl
  | exact appR_push rfl
  | exact AppR.refl _
  | with_reducible refine AppAt.bind (bindTo_app _ _) fun _ _ _ => ?_
  | with_reducible exact bindTo_app _ _
  | with_reducible refine AppAt.bind (forM_app ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine AppAt.bind (mapM_app ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine AppAt.bind (optionMapM_app ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine AppAt.bind (‹∀ st, AppAt _ st _› _) fun _ _ _ => ?_
  | with_reducible exact ‹∀ st, AppAt _ st _› _
  | with_reducible refine AppAt.discard ?_
  | with_reducible refine AppAt.bind (AppAt.discard ?_) fun _ _ _ => ?_
  | app_prim
  | dsimp only
  | rw [pure_bind]
  | split)

macro "app_straight" : tactic => `(tactic| repeat' app_step)

section APrims

variable {ctx : Ctx} {st : St}

theorem fresh_app : AppAt ctx st fresh := by
  unfold fresh
  exact AppAt.modG (appR_same rfl)


theorem pushHint_app {h : LHint} : AppAt ctx st (pushHint h) := by
  unfold pushHint
  app_straight


theorem takeHints_app  : AppAt ctx st (takeHints) := by
  unfold takeHints
  app_straight


theorem push_app {s : PStmt} : AppAt ctx st (push s) := by
  unfold push
  app_straight


theorem emitOp_app {o : LOp} : AppAt ctx st (emitOp o) := by
  unfold emitOp
  app_straight


theorem constCell_app {k : ℕ × ℕ} : AppAt ctx st (constCell k) := by
  unfold constCell
  app_straight


theorem oneCell_app  : AppAt ctx st (oneCell) := by
  unfold oneCell
  app_straight


theorem zeroCell_app  : AppAt ctx st (zeroCell) := by
  unfold zeroCell
  app_straight


theorem mulCell_app {a b : Cell} : AppAt ctx st (mulCell a b) := by
  unfold mulCell
  app_straight


theorem emitDeref_app {p off d : Cell} : AppAt ctx st (emitDeref p off d) := by
  unfold emitDeref
  app_straight


theorem selfFp_app  : AppAt ctx st (selfFp) := by
  unfold selfFp
  app_straight


theorem materialize_app {c e : Cell} : AppAt ctx st (materialize c e) := by
  unfold materialize
  app_straight


theorem cellAt_app {v : V} : AppAt ctx st (cellAt v) := by
  unfold cellAt
  app_straight


theorem cellOf_app {v : V} : AppAt ctx st (cellOf v) := by
  unfold cellOf
  app_straight


theorem factor_app {v : V} : AppAt ctx st (factor v) := by
  unfold factor
  app_straight


theorem pointer_app {p : V} {off : ℕ} : AppAt ctx st (pointer p off) := by
  unfold pointer
  app_straight


theorem pooledCell_app {find : Scope → Option Cell} {learn : Cell → Scope → Scope} {mk : Cell → LOp} : AppAt ctx st (pooledCell find learn mk) := by
  unfold pooledCell
  app_straight


theorem pooled_app {d : V} {find : Scope → Option Cell} {learn : Cell → Scope → Scope} {mk : Cell → LOp} : AppAt ctx st (pooled d find learn mk) := by
  unfold pooled
  app_straight


theorem isLazy_app {v : V} {k : Kind} : AppAt ctx st (isLazy v k) := by
  unfold isLazy
  app_straight


theorem isSelfFp_app {n : Cell} : AppAt ctx st (isSelfFp n) := by
  unfold isSelfFp
  app_straight


theorem advance_app  : AppAt ctx st (advance) := by
  unfold advance
  app_straight


theorem expect_app {e : Event → Bool} {what : String} : AppAt ctx st (expect e what) := by
  unfold expect
  app_straight


theorem endStmt_app  : AppAt ctx st (endStmt) := by
  unfold endStmt
  app_straight


theorem bindRun_app {vs : List V} {base : Cell} : AppAt ctx st (bindRun vs base) := by
  unfold bindRun
  exact forM_app (fun _ _ => bindTo_app _ _) _ _


theorem takeRun_app {vs : List V} : AppAt ctx st (takeRun vs) := by
  unfold takeRun
  app_straight

theorem spongeInPlace_app {vs : List V} {up : List Stmt} : AppAt ctx st (spongeInPlace vs up) := by
  unfold spongeInPlace
  app_straight


theorem onAlloc_app {vs : List V} {k : Kind} {up : List Stmt} : AppAt ctx st (onAlloc vs k up) := by
  unfold onAlloc
  app_straight


theorem flushN_app {up : List Stmt} : ∀ {fuel : ℕ} {st : St}, AppAt ctx st (flushN up fuel)
  | 0, _ => by unfold flushN; exact AppAt.pure
  | fuel + 1, st => by
      have ih : ∀ st, AppAt ctx st (flushN up fuel) := fun _ => flushN_app
      unfold flushN
      repeat' (first | exact ih _ | app_step)

theorem flush_app {up : List Stmt} : AppAt ctx st (flush up) := by
  unfold flush
  app_straight

theorem beginStmt_app {up : List Stmt} : AppAt ctx st (beginStmt up) := by
  unfold beginStmt
  app_straight

theorem destBits_app {d : Dest} : AppAt ctx st (destBits d) := by
  unfold destBits
  app_straight

set_option maxHeartbeats 2000000 in
theorem placeHint_app {h : Hint} : AppAt ctx st (placeHint h) := by
  have hc : ∀ (b : V) st, AppAt ctx st (cellOf b) := fun _ _ => cellOf_app
  have ha : ∀ (b : V) st, AppAt ctx st (cellAt b) := fun _ _ => cellAt_app
  cases h <;> unfold placeHint <;> app_straight

set_option maxHeartbeats 2000000 in
theorem placeAtom_app {a : Atom} : AppAt ctx st (placeAtom a) := by
  have hc : ∀ (b : V) st, AppAt ctx st (cellOf b) := fun _ _ => cellOf_app
  have ha : ∀ (b : V) st, AppAt ctx st (cellAt b) := fun _ _ => cellAt_app
  cases a <;> unfold placeAtom <;> app_straight

theorem allocTable_app {n : ℕ} : AppAt ctx st (allocTable n) := by
  unfold allocTable
  app_straight

theorem sharedTable_app {fs : List String} : AppAt ctx st (sharedTable fs) := by
  unfold sharedTable
  app_straight

theorem loopCount_app {f : String} {args : List V} {cells : List Cell} :
    AppAt ctx st (loopCount f args cells) := by
  unfold loopCount
  app_straight

theorem placeCall_app {f : String} {argVs : List V} {args rets : List Cell} {cond : Option Cell}
    {tail : Bool} : AppAt ctx st (placeCall f argVs args rets cond tail) := by
  unfold placeCall
  app_straight

theorem matchCells_app {x : V} {rest : List Stmt} {chained : Bool} :
    AppAt ctx st (matchCells x rest chained) := by
  unfold matchCells
  app_straight

end APrims

/-! ## A block's output -/

section Out

variable {ctx : Ctx}

/-- The statements left start with a `match`. -/
def ChainNext (rest : List Stmt) : Prop := ∃ x arms tl, rest = Stmt.match_ x arms :: tl

/-- The output is `O` extended, by a nonempty run while a `match` chains out. -/
def OutJ (O : List PStmt) (st : St) : Prop :=
  ∃ blk, st.out.toList = O ++ blk ∧ (st.chainIn ≠ none → blk ≠ [])

theorem OutJ.app {O : List PStmt} {st st' : St} (h : OutJ O st) (ha : AppR st st')
    (hk : KeepR st st') : OutJ O st' := by
  obtain ⟨b, hb, hne⟩ := h
  obtain ⟨b', hb'⟩ := ha
  refine ⟨b ++ b', by rw [hb', hb, List.append_assoc], fun hc => ?_⟩
  rw [show st'.chainIn = st.chainIn from hk] at hc
  simp [hne hc]

theorem OutJ.refl (st : St) (h : st.chainIn = none) : OutJ st.out.toList st :=
  ⟨[], by simp, fun h' => absurd h h'⟩

/-- What a statement leaves: the output `O` extended, and a `match` chaining out only into the
statements left when they start with a `match`. -/
def SP (O : List PStmt) (rest : List Stmt) (st : St) : Prop :=
  OutJ O st ∧ (st.chainIn ≠ none → ChainNext rest)

/-- Along a statement from a state no `match` chains into: the output `O` extended, by a nonempty
run if `b`, and no `match` chaining out. -/
def OutG (O : List PStmt) (b : Prop) (st : St) : Prop :=
  (∃ blk, st.out.toList = O ++ blk ∧ (b → blk ≠ [])) ∧ st.chainIn = none

theorem OutG.step {O : List PStmt} {b : Prop} {s s' : St} (h : OutG O b s) (ha : AppR s s')
    (hk : KeepR s s') : OutG O b s' := by
  obtain ⟨⟨blk, hb, hne⟩, hn⟩ := h
  obtain ⟨b', hb'⟩ := ha
  exact ⟨⟨blk ++ b', by rw [hb', hb, List.append_assoc], fun h => by simp [hne h]⟩,
    (show s'.chainIn = s.chainIn from hk).trans hn⟩

theorem OutG.of_out {O : List PStmt} {b : Prop} {s s' : St} (h : OutG O b s)
    (ho : s'.out = s.out) (hn : s'.chainIn = none) : OutG O b s' := by
  obtain ⟨⟨blk, hb, hne⟩, _⟩ := h
  exact ⟨⟨blk, by rw [ho]; exact hb, hne⟩, hn⟩

theorem OutG.push {O : List PStmt} {b : Prop} {s : St} (h : OutG O b s) (x : PStmt) :
    OutG O True { s with out := s.out.push x } := by
  obtain ⟨⟨blk, hb, _⟩, hn⟩ := h
  exact ⟨⟨blk ++ [x], by
    show (s.out.push x).toList = _
    simp [hb], fun _ => by simp⟩, hn⟩

theorem OutG.pop {O : List PStmt} {b : Prop} {s : St} (h : OutG O b s) (hb : b) (x : PStmt) :
    OutG O True { s with out := s.out.pop.push x } := by
  obtain ⟨⟨blk, hbl, hne⟩, hn⟩ := h
  refine ⟨⟨blk.dropLast ++ [x], ?_, fun _ => by simp⟩, hn⟩
  show (s.out.pop.push x).toList = _
  simp [Rev.toList_pop, hbl, List.dropLast_append_of_ne_nil (hne hb)]

theorem OutG.fin {O : List PStmt} {b : Prop} {rest : List Stmt} {s : St} (h : OutG O b s) :
    SP O rest s := by
  obtain ⟨⟨blk, hb, _⟩, hn⟩ := h
  exact ⟨⟨blk, hb, fun h' => absurd hn h'⟩, fun h' => absurd hn h'⟩

theorem OutG.fin_next {O : List PStmt} {rest : List Stmt} {s : St} (h : OutG O True s)
    (hr : ChainNext rest) (c : Option (ℕ × Cell)) : SP O rest { s with chainIn := c } := by
  obtain ⟨⟨blk, hb, hne⟩, _⟩ := h
  exact ⟨⟨blk, hb, fun _ => hne trivial⟩, fun _ => hr⟩

theorem stepG {α β : Type} {m : P α} {f : α → P β} {Q : β → St → Prop} {O : List PStmt}
    {b : Prop} {s : St} (ha : AppAt ctx s m) (hk : KeepAt ctx s m) (hg : OutG O b s)
    (hf : ∀ a s', OutG O b s' → wpP (f a) ctx s' Q) : wpP (m >>= f) ctx s Q :=
  wp_bind.mpr fun a s' he => hf a s' (hg.step (ha a s' he) (hk a s' he))

theorem push_G {x : PStmt} {O : List PStmt} {b : Prop} {s : St} (hg : OutG O b s) :
    wpP (push x) ctx s fun _ s' => OutG O True s' := by
  unfold push
  exact wp_modify.mpr (hg.push x)

theorem chain_none {s : Stmt} {rest : List Stmt} {st : St} (hs : ∀ x arms, s ≠ .match_ x arms)
    (hc : st.chainIn ≠ none → ChainNext (s :: rest)) : st.chainIn = none := by
  by_contra h
  obtain ⟨x, arms, tl, h'⟩ := hc h
  exact hs x arms (List.cons.inj h').1

/-- **A block in a scope of its own** leaves no `match` chaining out when its block leaves none. -/
theorem inBlock_chain {m : P Unit}
    (hm : ∀ st, st.chainIn = none → wpP m ctx st fun _ st' => st'.chainIn = none) (st : St)
    (h : st.chainIn = none) : wpP (inBlock m) ctx st fun _ st' => st'.chainIn = none := by
  unfold inBlock
  refine wp_bind.mpr (wp_mono (expect_keep (st := st)) fun _ st₁ h₁ => ?_)
  refine wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_set.mpr (wp_bind.mpr (wp_mono
    (hm _ ((show st₁.chainIn = st.chainIn from h₁).trans h))
    fun _ st₂ h₂ => wp_bind.mpr (wp_mono flush_keep fun _ st₃ h₃ => wp_bind.mpr
      (wp_mono expect_keep fun _ st₄ h₄ => ?_)))))))
  have h4 : st₄.chainIn = none :=
    (show st₄.chainIn = st₃.chainIn from h₄).trans ((show st₃.chainIn = st₂.chainIn from h₃).trans h₂)
  refine wp_bind.mpr (wp_get.mpr ?_)
  have fin : ∀ st₅ : St, st₅.chainIn = none → wpP (do
      let st ← get
      set { st with out := st₁.out, scope := st₁.scope }
      pure st.out.toList : P (List PStmt)) ctx st₅ fun _ st' => st'.chainIn = none :=
    fun st₅ h₅ => wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_set.mpr (wp_pure.mpr h₅))))
  dsimp only
  split
  · refine wp_bind.mpr (wp_mono fresh_keep fun _ st₅ h₅ => wp_bind.mpr (wp_mono emitOp_keep
      fun _ st₆ h₆ => fin st₆ ?_))
    exact (show st₆.chainIn = st₅.chainIn from h₆).trans ((show st₅.chainIn = st₄.chainIn from h₅).trans h4)
  · exact fin st₄ h4

theorem stepIn {ss : List Stmt} {β : Type} {f : List PStmt → P β} {Q : β → St → Prop}
    {O : List PStmt} {b : Prop} {s : St}
    (hin : ∀ st, st.chainIn = none →
      wpP (inBlock (placeBlock ss)) ctx st fun _ st' => st'.chainIn = none)
    (hg : OutG O b s) (hf : ∀ a s', OutG O b s' → wpP (f a) ctx s' Q) :
    wpP (inBlock (placeBlock ss) >>= f) ctx s Q :=
  wp_bind.mpr fun a s' he => hf a s' (hg.of_out
    (inBlock_mono (fun st => placeBlock_mono ss st) s a s' he).2.1 (hin s hg.2 a s' he))

/-- A `match`'s arms dispatch into the next `match` only when the statements left start with one. -/
theorem matchCells_next {x : V} {rest : List Stmt} {chained : Bool} (st : St) :
    wpP (matchCells x rest chained) ctx st fun r _ => r.2.1 ≠ none → ChainNext rest := by
  by_cases hr : ChainNext rest
  · exact fun _ _ _ _ => hr
  unfold matchCells
  refine wp_bind.mpr fun _ _ _ => ?_
  split
  · split
    · exact absurd ⟨_, _, _, rfl⟩ hr
    · exact wp_bind.mpr wp_failP
  · exact wp_bind.mpr (wp_pure.mpr (wp_bind.mpr fun _ _ _ => wp_bind.mpr
      fun _ _ _ => wp_pure.mpr fun h => absurd rfl h))

theorem atom_stmt_app {a : Atom} {rest : List Stmt} (st : St) :
    AppAt ctx st (placeStmt (.atom a) rest) := by
  rw [placeStmt]
  app_straight

set_option maxHeartbeats 2000000 in
theorem call_stmt_app {f : String} {args rets : List V} {rest : List Stmt} (st : St) :
    AppAt ctx st (placeStmt (.call f args rets) rest) := by
  have hc : ∀ (b : V) st, AppAt ctx st (cellOf b) := fun _ _ => cellOf_app
  have ha : ∀ (b : V) st, AppAt ctx st (cellAt b) := fun _ _ => cellAt_app
  rw [placeStmt]
  app_straight

set_option maxHeartbeats 2000000 in
theorem callIf_stmt_app {c : V} {f : String} {args : List V} {rest : List Stmt} (st : St) :
    AppAt ctx st (placeStmt (.callIf c f args) rest) := by
  have hc : ∀ (b : V) st, AppAt ctx st (cellOf b) := fun _ _ => cellOf_app
  rw [placeStmt]
  app_straight

set_option maxHeartbeats 2000000 in
theorem dispatch_stmt_app {x : V} {fs : List String} {args rets : List V} {rest : List Stmt}
    (st : St) : AppAt ctx st (placeStmt (.dispatch x fs args rets) rest) := by
  have hc : ∀ (b : V) st, AppAt ctx st (cellOf b) := fun _ _ => cellOf_app
  have ha : ∀ (b : V) st, AppAt ctx st (cellAt b) := fun _ _ => cellAt_app
  rw [placeStmt]
  app_straight

theorem ret_stmt_app {vs : List V} {rest : List Stmt} (st : St) :
    AppAt ctx st (placeStmt (.ret vs) rest) := by
  have ha : ∀ (b : V) st, AppAt ctx st (cellAt b) := fun _ _ => cellAt_app
  rw [placeStmt]
  app_straight

theorem atom_stmt_keep {a : Atom} {rest : List Stmt} (st : St) :
    KeepAt ctx st (placeStmt (.atom a) rest) := by
  rw [placeStmt]
  keep_straight

set_option maxHeartbeats 2000000 in
theorem call_stmt_keep {f : String} {args rets : List V} {rest : List Stmt} (st : St) :
    KeepAt ctx st (placeStmt (.call f args rets) rest) := by
  have hc : ∀ (b : V) st, KeepAt ctx st (cellOf b) := fun _ _ => cellOf_keep
  have ha : ∀ (b : V) st, KeepAt ctx st (cellAt b) := fun _ _ => cellAt_keep
  rw [placeStmt]
  keep_straight

set_option maxHeartbeats 2000000 in
theorem callIf_stmt_keep {c : V} {f : String} {args : List V} {rest : List Stmt} (st : St) :
    KeepAt ctx st (placeStmt (.callIf c f args) rest) := by
  have hc : ∀ (b : V) st, KeepAt ctx st (cellOf b) := fun _ _ => cellOf_keep
  rw [placeStmt]
  keep_straight

set_option maxHeartbeats 2000000 in
theorem dispatch_stmt_keep {x : V} {fs : List String} {args rets : List V} {rest : List Stmt}
    (st : St) : KeepAt ctx st (placeStmt (.dispatch x fs args rets) rest) := by
  have hc : ∀ (b : V) st, KeepAt ctx st (cellOf b) := fun _ _ => cellOf_keep
  have ha : ∀ (b : V) st, KeepAt ctx st (cellAt b) := fun _ _ => cellAt_keep
  rw [placeStmt]
  keep_straight

theorem ret_stmt_keep {vs : List V} {rest : List Stmt} (st : St) :
    KeepAt ctx st (placeStmt (.ret vs) rest) := by
  have ha : ∀ (b : V) st, KeepAt ctx st (cellAt b) := fun _ _ => cellAt_keep
  rw [placeStmt]
  keep_straight

/-- A statement other than a `match` or an `ite`: no `match` chains into it, and it only extends
the output. -/
theorem straight_out {s : Stmt} {rest : List Stmt} {st : St} {O : List PStmt}
    (hs : ∀ x arms, s ≠ .match_ x arms) (ha : AppAt ctx st (placeStmt s rest))
    (hk : KeepAt ctx st (placeStmt s rest)) (hj : OutJ O st)
    (hc : st.chainIn ≠ none → ChainNext (s :: rest)) :
    wpP (placeStmt s rest) ctx st fun _ st' => SP O rest st' := fun a st' he => by
  have hn := chain_none hs hc
  have h2 : st'.chainIn = st.chainIn := hk a st' he
  exact ⟨hj.app (ha a st' he) h2, fun h => absurd (h2.trans hn) h⟩

/-- **A `match`**: from a state no `match` chains into, its output `O` extended (by a nonempty run
if it is entered, the chain node it extends last), its arms leaving none chaining out. -/
theorem placeMatch_out {x : V} {n : ℕ} {rest : List Stmt} {entered : Option (ℕ × Cell)}
    {chained : Bool} {armsAt : Cell → ArmExit → P (List (List PStmt))}
    (harms : ∀ base exit st, st.chainIn = none → wpP (armsAt base exit) ctx st fun _ st' =>
      st'.out = st.out ∧ st'.chainIn = none)
    {O : List PStmt} {st : St} (hg : OutG O (entered ≠ none) st) :
    wpP (placeMatch x n rest entered chained armsAt) ctx st fun _ st' => SP O rest st' := by
  unfold placeMatch
  refine wp_bind.mpr (wp_mono (wp_and (wp_and (matchCells_app (st := st))
    (matchCells_keep (st := st))) (matchCells_next st)) fun r s₁ ⟨⟨ha₁, hk₁⟩, hnx⟩ => ?_)
  have g₁ := hg.step ha₁ hk₁
  obtain ⟨lx, nextSel, sfp, one⟩ := r
  dsimp only at hnx ⊢
  cases entered with
  | none =>
    cases nextSel with
    | none =>
      simp only [pure_bind]
      refine stepG fresh_app fresh_keep g₁ fun join s₂ g₂ => ?_
      refine stepG takeHints_app takeHints_keep g₂ fun hints s₃ g₃ => ?_
      refine stepG allocTable_app allocTable_keep g₃ fun first s₄ g₄ => ?_
      refine stepG fresh_app fresh_keep g₄ fun entry s₅ g₅ => ?_
      refine wp_bind.mpr (wp_get.mpr ?_)
      refine wp_bind.mpr (wp_mono (harms _ _ _ g₅.2) fun _ s₆ ⟨ho, hn⟩ => ?_)
      refine stepG expect_app expect_keep (g₅.of_out ho hn) fun _ s₇ g₇ => ?_
      exact wp_bind.mpr (wp_mono (push_G g₇) fun _ s₈ g₈ => wp_pure.mpr g₈.fin)
    | some p =>
      simp only [pure_bind]
      refine stepG fresh_app fresh_keep g₁ fun join s₂ g₂ => ?_
      refine stepG takeHints_app takeHints_keep g₂ fun hints s₃ g₃ => ?_
      refine stepG allocTable_app allocTable_keep g₃ fun first s₄ g₄ => ?_
      refine stepG fresh_app fresh_keep g₄ fun entry s₅ g₅ => ?_
      refine stepG allocTable_app allocTable_keep g₅ fun nf s₅' g₅' => ?_
      refine wp_bind.mpr (wp_get.mpr ?_)
      refine wp_bind.mpr (wp_mono (harms _ _ _ g₅'.2) fun _ s₆ ⟨ho, hn⟩ => ?_)
      refine stepG expect_app expect_keep (g₅'.of_out ho hn) fun _ s₇ g₇ => ?_
      exact wp_bind.mpr (wp_mono (push_G g₇) fun _ s₈ g₈ =>
        wp_modify.mpr (g₈.fin_next (hnx (by simp)) _))
  | some p =>
    have hb : some p ≠ none := by simp
    cases nextSel with
    | none =>
      simp only [pure_bind]
      refine wp_bind.mpr (wp_get.mpr ?_)
      refine wp_bind.mpr (wp_mono (harms _ _ _ g₁.2) fun _ s₆ ⟨ho, hn⟩ => ?_)
      refine stepG expect_app expect_keep (g₁.of_out ho hn) fun _ s₇ g₇ => ?_
      refine wp_bind.mpr (wp_get.mpr ?_)
      split
      · exact wp_bind.mpr (wp_set.mpr (wp_pure.mpr (g₇.pop hb _).fin))
      · exact wp_bind.mpr wp_failP
    | some q =>
      simp only [pure_bind]
      refine stepG allocTable_app allocTable_keep g₁ fun nf s₅' g₅' => ?_
      refine wp_bind.mpr (wp_get.mpr ?_)
      refine wp_bind.mpr (wp_mono (harms _ _ _ g₅'.2) fun _ s₆ ⟨ho, hn⟩ => ?_)
      refine stepG expect_app expect_keep (g₅'.of_out ho hn) fun _ s₇ g₇ => ?_
      refine wp_bind.mpr (wp_get.mpr ?_)
      split
      · exact wp_bind.mpr (wp_set.mpr (wp_modify.mpr
          ((g₇.pop hb _).fin_next (hnx (by simp)) _)))
      · exact wp_bind.mpr wp_failP

mutual
/-- **A block** from a state whose `match` chaining goes into a `match` it starts with extends the
output and leaves no `match` chaining out. -/
theorem placeBlock_out : ∀ (ss : List Stmt) (st : St) (O : List PStmt), OutJ O st →
    (st.chainIn ≠ none → ChainNext ss) →
    wpP (placeBlock ss) ctx st fun _ st' => OutJ O st' ∧ st'.chainIn = none
  | [], st, O, hj, hc => by
      rw [placeBlock]
      refine wp_pure.mpr ⟨hj, ?_⟩
      by_contra h
      obtain ⟨_, _, _, h'⟩ := hc h
      cases h'
  | s :: rest, st, O, hj, hc => by
      rw [placeBlock]
      exact wp_bind.mpr (wp_mono (placeStmt_out s rest st O hj hc) fun _ st₁ ⟨hj₁, hc₁⟩ =>
        wp_bind.mpr (wp_mono (wp_and (endStmt_app (st := st₁)) (endStmt_keep (st := st₁)))
          fun _ st₂ ⟨ha₂, hk₂⟩ => placeBlock_out rest st₂ O (hj₁.app ha₂ hk₂)
            fun h => hc₁ (by rwa [show st₂.chainIn = st₁.chainIn from hk₂] at h)))

theorem placeStmt_out : ∀ (s : Stmt) (rest : List Stmt) (st : St) (O : List PStmt), OutJ O st →
    (st.chainIn ≠ none → ChainNext (s :: rest)) →
    wpP (placeStmt s rest) ctx st fun _ st' => SP O rest st'
  | .atom a, rest, st, O, hj, hc =>
      straight_out (fun _ _ h => by cases h) (atom_stmt_app st) (atom_stmt_keep st) hj hc
  | .ite c z nz, rest, st, O, hj, hc => by
      have hn := chain_none (fun _ _ h => by cases h) hc
      have hz : ∀ st, st.chainIn = none →
          wpP (inBlock (placeBlock z)) ctx st fun _ st' => st'.chainIn = none :=
        inBlock_chain fun st h => wp_mono (placeBlock_out z st _ (OutJ.refl st h)
          fun h' => absurd h h') fun _ _ hh => hh.2
      have hnz : ∀ st, st.chainIn = none →
          wpP (inBlock (placeBlock nz)) ctx st fun _ st' => st'.chainIn = none :=
        inBlock_chain fun st h => wp_mono (placeBlock_out nz st _ (OutJ.refl st h)
          fun h' => absurd h h') fun _ _ hh => hh.2
      have hg : OutG O False st := by
        obtain ⟨blk, hb, _⟩ := hj
        exact ⟨⟨blk, hb, fun h => h.elim⟩, hn⟩
      rw [placeStmt]
      refine stepG flush_app flush_keep hg fun _ s₁ g₁ => ?_
      refine stepG cellOf_app cellOf_keep g₁ fun _ s₂ g₂ => ?_
      refine stepG selfFp_app selfFp_keep g₂ fun _ s₃ g₃ => ?_
      refine stepG oneCell_app oneCell_keep g₃ fun _ s₄ g₄ => ?_
      refine stepG fresh_app fresh_keep g₄ fun _ s₅ g₅ => ?_
      refine stepG takeHints_app takeHints_keep g₅ fun _ s₆ g₆ => ?_
      refine stepIn hz g₆ fun _ s₇ g₇ => ?_
      refine wp_bind.mpr (wp_peek.mpr ?_)
      split
      · refine stepG fresh_app fresh_keep g₇ fun _ s₈ g₈ => ?_
        refine stepIn hnz g₈ fun _ s₉ g₉ => ?_
        refine stepG expect_app expect_keep g₉ fun _ s₁₀ g₁₀ => ?_
        exact wp_mono (push_G g₁₀) fun _ _ h => h.fin
      · split
        · exact wp_bind.mpr wp_failP
        · refine stepG expect_app expect_keep g₇ fun _ s₈ g₈ => ?_
          exact wp_mono (push_G g₈) fun _ _ h => h.fin
  | .match_ x arms, rest, st, O, hj, _ => by
      rw [placeStmt]
      refine wp_bind.mpr (wp_mono (wp_and (flush_app (st := st)) (flush_keep (st := st)))
        fun _ st₁ ⟨ha₁, hk₁⟩ => ?_)
      obtain ⟨blk, hb, hne⟩ := hj.app ha₁ hk₁
      refine wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_set.mpr ?_)))
      exact placeMatch_out (fun base exit st h => wp_and (wp_mono
        (placeArms_mono arms 0 arms.length base exit st) fun _ _ h' => h'.2.2)
        (placeArms_chain arms 0 arms.length base exit st h)) ⟨⟨blk, hb, hne⟩, rfl⟩
  | .call f args rets, rest, st, O, hj, hc =>
      straight_out (fun _ _ h => by cases h) (call_stmt_app st) (call_stmt_keep st) hj hc
  | .callIf c f args, rest, st, O, hj, hc =>
      straight_out (fun _ _ h => by cases h) (callIf_stmt_app st) (callIf_stmt_keep st) hj hc
  | .dispatch x fs args rets, rest, st, O, hj, hc =>
      straight_out (fun _ _ h => by cases h) (dispatch_stmt_app st) (dispatch_stmt_keep st) hj hc
  | .ret vs, rest, st, O, hj, hc =>
      straight_out (fun _ _ h => by cases h) (ret_stmt_app st) (ret_stmt_keep st) hj hc

/-- **The arms of a `match`** from a state no `match` chains into leave none chaining out. -/
theorem placeArms_chain : ∀ (arms : List (List Stmt)) (j n : ℕ) (base : Cell) (exit : ArmExit)
    (st : St), st.chainIn = none →
    wpP (placeArms arms j n base exit) ctx st fun _ st' => st'.chainIn = none
  | [], j, n, base, exit, st, h => by
      rw [placeArms]
      exact wp_bind.mpr (wp_modify.mpr (wp_pure.mpr h))
  | arm :: more, j, n, base, exit, st, h => by
      rw [placeArms]
      refine wp_bind.mpr (wp_modify.mpr (wp_bind.mpr (wp_mono (inBlock_chain
        (fun st h' => wp_mono (placeBlock_out arm st _ (OutJ.refl st h') fun h'' => absurd h' h'')
          fun _ _ hh => hh.2) _ h) fun blk st₁ h₁ => ?_)))
      have tail : ∀ (lv : List PStmt) (st₂ : St), st₂.chainIn = none →
          wpP (do
            let top := (← get).next
            let blocks ← placeArms more (j + 1) n base exit
            modify fun s => { s with next := max s.next top }
            pure ((blk ++ lv) :: blocks) : P (List (List PStmt))) ctx st₂ fun _ st' =>
            st'.chainIn = none := fun lv st₂ h₂ =>
        wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_mono (placeArms_chain more (j + 1) n base
          exit st₂ h₂) fun _ st₃ h₃ => wp_bind.mpr (wp_modify.mpr (wp_pure.mpr h₃)))))
      split
      · unfold fresh
        exact wp_bind.mpr (wp_modifyGet.mpr (wp_bind.mpr (wp_pure.mpr (tail _ _ h₁))))
      · exact wp_bind.mpr (wp_pure.mpr (tail _ _ h₁))
end

/-- **`PlaceMono`**: a block moves neither the next free cell back nor a place, and from a state no
`match` chains into, it only extends the output and leaves no `match` chaining out. -/
theorem placeMono : PlaceMono ctx := fun ss st => by
  by_cases h : st.chainIn = none
  · exact wp_mono (wp_and (placeBlock_mono ss st) (placeBlock_out ss st _ (OutJ.refl st h)
      fun h' => absurd h h')) fun _ _ ⟨hm, ⟨blk, hb, _⟩, hn⟩ => ⟨hm.1, hm.2, fun _ => ⟨hn, blk, hb⟩⟩
  · exact wp_mono (placeBlock_mono ss st) fun _ _ hm => ⟨hm.1, hm.2, fun h' => absurd h' h⟩

end Out

end
end LeanVM.Compiler.Complete
