/-
  LeanVM.Guest.Backend.Complete.FrameLocs

  Every placement step, on the path or off it, moves neither the next free cell back nor a place.
-/

module

public import LeanVM.Guest.Backend.Complete.FramePrims

/-!
# Places only grow

`placeMono`: every success of a block's walk has the next free cell no lower and every place of
the start still there (`LocsLe`); the same for a statement, a block in a scope of its own (which
also gives back the output and the pools) and the arms of a `match` (which rewind the next free
cell to their base, so only the base is below the end).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

section Mono

variable {ctx : Ctx} {α β : Type}

/-- The next free cell no lower and the places kept. -/
def MonoR (st st' : St) : Prop := st.next ≤ st'.next ∧ LocsLe st.locs st'.locs

theorem MonoR.refl (st : St) : MonoR st st := ⟨le_rfl, LocsLe.refl _⟩

theorem MonoR.trans {st₁ st₂ st₃ : St} (h₁ : MonoR st₁ st₂) (h₂ : MonoR st₂ st₃) :
    MonoR st₁ st₃ := ⟨le_trans h₁.1 h₂.1, h₁.2.trans h₂.2⟩

/-- Every success of `m` from `st` is `MonoR` of `st`. -/
def MonoAt (ctx : Ctx) (st : St) (m : P α) : Prop := wpP m ctx st fun _ st' => MonoR st st'

variable {st : St}

theorem MonoAt.pure {a : α} : MonoAt ctx st (Pure.pure a) := wp_pure.mpr (MonoR.refl st)

theorem MonoAt.fail {msg : String} : MonoAt ctx st (failP msg : P α) := wp_failP

theorem MonoAt.fail_bind {msg : String} {f : α → P β} :
    MonoAt ctx st ((failP msg : P α) >>= f) := wp_bind.mpr wp_failP

theorem MonoAt.bind {m : P α} {f : α → P β} (hm : MonoAt ctx st m)
    (hf : ∀ a st', MonoR st st' → MonoAt ctx st' (f a)) : MonoAt ctx st (m >>= f) :=
  wp_bind.mpr (wp_mono hm fun a st' h => wp_mono (hf a st' h) fun _ _ h' => h.trans h')

theorem MonoAt.get_bind {f : St → P β} (h : MonoAt ctx st (f st)) : MonoAt ctx st (get >>= f) :=
  wp_bind.mpr (wp_get.mpr h)

theorem MonoAt.read_bind {f : Ctx → P β} (h : MonoAt ctx st (f ctx)) :
    MonoAt ctx st (read >>= f) := wp_bind.mpr (wp_read.mpr h)

theorem MonoAt.peek_bind {f : Option Event → P β} (h : MonoAt ctx st (f st.rest.head?)) :
    MonoAt ctx st (peek >>= f) := wp_bind.mpr (wp_peek.mpr h)

theorem MonoAt.guard {c : Prop} [Decidable c] {msg : String} {f : PUnit → P β}
    (h : ¬c → MonoAt ctx st (f PUnit.unit)) :
    MonoAt ctx st (if c then failP msg >>= f else f PUnit.unit) := by
  split
  · exact MonoAt.fail_bind
  · next hc => exact h hc

theorem MonoAt.mod {g : St → St} (h : MonoR st (g st)) : MonoAt ctx st (modify g) :=
  wp_modify.mpr h

theorem MonoAt.mod_bind {g : St → St} {f : PUnit → P β} (h : MonoR st (g st))
    (hf : MonoAt ctx (g st) (f ⟨⟩)) : MonoAt ctx st (modify g >>= f) :=
  wp_bind.mpr (wp_modify.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem MonoAt.modG {g : St → α × St} (h : MonoR st (g st).2) :
    MonoAt ctx st (modifyGet g) := wp_modifyGet.mpr h

theorem MonoAt.modG_bind {g : St → α × St} {f : α → P β} (h : MonoR st (g st).2)
    (hf : MonoAt ctx (g st).2 (f (g st).1)) : MonoAt ctx st (modifyGet g >>= f) :=
  wp_bind.mpr (wp_modifyGet.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem MonoAt.setS {s : St} (h : MonoR st s) : MonoAt ctx st (set s : P PUnit) := wp_set.mpr h

theorem MonoAt.setS_bind {s : St} {f : PUnit → P β} (h : MonoR st s) (hf : MonoAt ctx s (f ⟨⟩)) :
    MonoAt ctx st (set s >>= f) :=
  wp_bind.mpr (wp_set.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem MonoAt.discard {m : P α} (h : MonoAt ctx st m) : MonoAt ctx st (Functor.discard m) := by
  rw [Functor.discard, map_const, Function.comp_apply, map_eq_pure_bind]
  exact MonoAt.bind h fun _ _ _ => MonoAt.pure

theorem monoR_same {s : St} (hn : s.next = st.next) (hl : s.locs = st.locs) : MonoR st s :=
  ⟨le_of_eq hn.symm, by rw [hl]; exact LocsLe.refl _⟩

theorem monoR_succ {s : St} (hn : s.next = st.next + 1) (hl : s.locs = st.locs) : MonoR st s :=
  ⟨by rw [hn]; exact Nat.le_succ _, by rw [hl]; exact LocsLe.refl _⟩

theorem bindTo_mono (v : V) (l : Loc) : MonoAt ctx st (bindTo v l) := by
  unfold bindTo
  refine wp_bind.mpr (wp_get.mpr ?_)
  split
  · exact wp_bind.mpr wp_failP
  · next h =>
    refine wp_modify.mpr ⟨le_rfl, fun w x hx => ?_⟩
    show (st.locs.insert v l)[w]? = some x
    rw [KMap.getElem?_insert]
    split
    · next he =>
      subst he
      rw [KMap.getElem?_eq_none_of_contains_eq_false (by simpa using h)] at hx
      cases hx
    · exact hx

theorem forM_mono {γ : Type} {f : γ → P PUnit} (hf : ∀ b st, MonoAt ctx st (f b)) :
    ∀ (l : List γ) (st : St), MonoAt ctx st (l.forM f)
  | [], _ => MonoAt.pure
  | b :: l, st => by
      show MonoAt ctx st (f b >>= fun _ => l.forM f)
      exact MonoAt.bind (hf b st) fun _ st' _ => forM_mono hf l st'

theorem mapM_mono {γ δ : Type} {f : γ → P δ} (hf : ∀ b st, MonoAt ctx st (f b)) :
    ∀ (l : List γ) (st : St), MonoAt ctx st (l.mapM f)
  | [], _ => by rw [List.mapM_nil]; exact MonoAt.pure
  | b :: l, st => by
      rw [List.mapM_cons]
      exact MonoAt.bind (hf b st) fun _ st' _ => MonoAt.bind (mapM_mono hf l st') fun _ _ _ =>
        MonoAt.pure

theorem optionMapM_mono {γ δ : Type} {f : γ → P δ} (hf : ∀ b st, MonoAt ctx st (f b))
    (o : Option γ) (st : St) : MonoAt ctx st (o.mapM f) := by
  cases o with
  | none => exact MonoAt.pure
  | some v =>
    rw [Option.mapM, map_eq_pure_bind]
    exact MonoAt.bind (hf v st) fun _ _ _ => MonoAt.pure

end Mono

/-- A primitive already shown to keep `MonoR` (extended after each primitive). -/
syntax "mono_prim" : tactic

set_option hygiene false in
macro_rules | `(tactic| mono_prim) => `(tactic| first
  | with_reducible refine MonoAt.bind fresh_mono fun _ _ _ => ?_
  | with_reducible exact fresh_mono
  | with_reducible refine MonoAt.bind pushHint_mono fun _ _ _ => ?_
  | with_reducible exact pushHint_mono
  | with_reducible refine MonoAt.bind takeHints_mono fun _ _ _ => ?_
  | with_reducible exact takeHints_mono
  | with_reducible refine MonoAt.bind push_mono fun _ _ _ => ?_
  | with_reducible exact push_mono
  | with_reducible refine MonoAt.bind emitOp_mono fun _ _ _ => ?_
  | with_reducible exact emitOp_mono
  | with_reducible refine MonoAt.bind constCell_mono fun _ _ _ => ?_
  | with_reducible exact constCell_mono
  | with_reducible refine MonoAt.bind oneCell_mono fun _ _ _ => ?_
  | with_reducible exact oneCell_mono
  | with_reducible refine MonoAt.bind zeroCell_mono fun _ _ _ => ?_
  | with_reducible exact zeroCell_mono
  | with_reducible refine MonoAt.bind mulCell_mono fun _ _ _ => ?_
  | with_reducible exact mulCell_mono
  | with_reducible refine MonoAt.bind emitDeref_mono fun _ _ _ => ?_
  | with_reducible exact emitDeref_mono
  | with_reducible refine MonoAt.bind selfFp_mono fun _ _ _ => ?_
  | with_reducible exact selfFp_mono
  | with_reducible refine MonoAt.bind materialize_mono fun _ _ _ => ?_
  | with_reducible exact materialize_mono
  | with_reducible refine MonoAt.bind cellAt_mono fun _ _ _ => ?_
  | with_reducible exact cellAt_mono
  | with_reducible refine MonoAt.bind cellOf_mono fun _ _ _ => ?_
  | with_reducible exact cellOf_mono
  | with_reducible refine MonoAt.bind factor_mono fun _ _ _ => ?_
  | with_reducible exact factor_mono
  | with_reducible refine MonoAt.bind pointer_mono fun _ _ _ => ?_
  | with_reducible exact pointer_mono
  | with_reducible refine MonoAt.bind pooledCell_mono fun _ _ _ => ?_
  | with_reducible exact pooledCell_mono
  | with_reducible refine MonoAt.bind pooled_mono fun _ _ _ => ?_
  | with_reducible exact pooled_mono
  | with_reducible refine MonoAt.bind isLazy_mono fun _ _ _ => ?_
  | with_reducible exact isLazy_mono
  | with_reducible refine MonoAt.bind isSelfFp_mono fun _ _ _ => ?_
  | with_reducible exact isSelfFp_mono
  | with_reducible refine MonoAt.bind advance_mono fun _ _ _ => ?_
  | with_reducible exact advance_mono
  | with_reducible refine MonoAt.bind expect_mono fun _ _ _ => ?_
  | with_reducible exact expect_mono
  | with_reducible refine MonoAt.bind endStmt_mono fun _ _ _ => ?_
  | with_reducible exact endStmt_mono
  | with_reducible refine MonoAt.bind bindRun_mono fun _ _ _ => ?_
  | with_reducible exact bindRun_mono
  | with_reducible refine MonoAt.bind takeRun_mono fun _ _ _ => ?_
  | with_reducible exact takeRun_mono
  | with_reducible refine MonoAt.bind spongeInPlace_mono fun _ _ _ => ?_
  | with_reducible exact spongeInPlace_mono
  | with_reducible refine MonoAt.bind onAlloc_mono fun _ _ _ => ?_
  | with_reducible exact onAlloc_mono
  | with_reducible refine MonoAt.bind flushN_mono fun _ _ _ => ?_
  | with_reducible exact flushN_mono
  | with_reducible refine MonoAt.bind flush_mono fun _ _ _ => ?_
  | with_reducible exact flush_mono
  | with_reducible refine MonoAt.bind beginStmt_mono fun _ _ _ => ?_
  | with_reducible exact beginStmt_mono
  | with_reducible refine MonoAt.bind destBits_mono fun _ _ _ => ?_
  | with_reducible exact destBits_mono
  | with_reducible refine MonoAt.bind placeHint_mono fun _ _ _ => ?_
  | with_reducible exact placeHint_mono
  | with_reducible refine MonoAt.bind placeAtom_mono fun _ _ _ => ?_
  | with_reducible exact placeAtom_mono
  | with_reducible refine MonoAt.bind allocTable_mono fun _ _ _ => ?_
  | with_reducible exact allocTable_mono
  | with_reducible refine MonoAt.bind sharedTable_mono fun _ _ _ => ?_
  | with_reducible exact sharedTable_mono
  | with_reducible refine MonoAt.bind loopCount_mono fun _ _ _ => ?_
  | with_reducible exact loopCount_mono
  | with_reducible refine MonoAt.bind placeCall_mono fun _ _ _ => ?_
  | with_reducible exact placeCall_mono
  | with_reducible refine MonoAt.bind matchCells_mono fun _ _ _ => ?_
  | with_reducible exact matchCells_mono)

/-- One step of a walk that moves neither the next free cell back nor a place. -/
macro "mono_step" : tactic => `(tactic| first
  | with_reducible exact MonoAt.pure
  | with_reducible exact MonoAt.fail
  | with_reducible exact MonoAt.fail_bind
  | with_reducible refine MonoAt.get_bind ?_
  | with_reducible refine MonoAt.read_bind ?_
  | with_reducible refine MonoAt.peek_bind ?_
  | with_reducible refine MonoAt.guard fun _ => ?_
  | with_reducible refine MonoAt.mod_bind ?_ ?_
  | with_reducible refine MonoAt.modG_bind ?_ ?_
  | with_reducible refine MonoAt.setS_bind ?_ ?_
  | with_reducible refine MonoAt.mod ?_
  | with_reducible refine MonoAt.modG ?_
  | with_reducible refine MonoAt.setS ?_
  | exact monoR_same rfl rfl
  | exact monoR_succ rfl rfl
  | exact MonoR.refl _
  | with_reducible refine MonoAt.bind (bindTo_mono _ _) fun _ _ _ => ?_
  | with_reducible exact bindTo_mono _ _
  | with_reducible refine MonoAt.bind (forM_mono ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine MonoAt.bind (mapM_mono ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine MonoAt.bind (optionMapM_mono ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine MonoAt.bind (‹∀ st, MonoAt _ st _› _) fun _ _ _ => ?_
  | with_reducible exact ‹∀ st, MonoAt _ st _› _
  | with_reducible refine MonoAt.discard ?_
  | with_reducible refine MonoAt.bind (MonoAt.discard ?_) fun _ _ _ => ?_
  | mono_prim
  | dsimp only
  | rw [pure_bind]
  | split)

macro "mono_straight" : tactic => `(tactic| repeat' mono_step)


section Prims

variable {ctx : Ctx} {st : St}

theorem fresh_mono : MonoAt ctx st fresh := by
  unfold fresh
  exact MonoAt.modG (monoR_succ rfl rfl)


theorem pushHint_mono {h : LHint} : MonoAt ctx st (pushHint h) := by
  unfold pushHint
  mono_straight


theorem takeHints_mono  : MonoAt ctx st (takeHints) := by
  unfold takeHints
  mono_straight


theorem push_mono {s : PStmt} : MonoAt ctx st (push s) := by
  unfold push
  mono_straight


theorem emitOp_mono {o : LOp} : MonoAt ctx st (emitOp o) := by
  unfold emitOp
  mono_straight


theorem constCell_mono {k : ℕ × ℕ} : MonoAt ctx st (constCell k) := by
  unfold constCell
  mono_straight


theorem oneCell_mono  : MonoAt ctx st (oneCell) := by
  unfold oneCell
  mono_straight


theorem zeroCell_mono  : MonoAt ctx st (zeroCell) := by
  unfold zeroCell
  mono_straight


theorem mulCell_mono {a b : Cell} : MonoAt ctx st (mulCell a b) := by
  unfold mulCell
  mono_straight


theorem emitDeref_mono {p off d : Cell} : MonoAt ctx st (emitDeref p off d) := by
  unfold emitDeref
  mono_straight


theorem selfFp_mono  : MonoAt ctx st (selfFp) := by
  unfold selfFp
  mono_straight


theorem materialize_mono {c e : Cell} : MonoAt ctx st (materialize c e) := by
  unfold materialize
  mono_straight


theorem cellAt_mono {v : V} : MonoAt ctx st (cellAt v) := by
  unfold cellAt
  mono_straight


theorem cellOf_mono {v : V} : MonoAt ctx st (cellOf v) := by
  unfold cellOf
  mono_straight


theorem factor_mono {v : V} : MonoAt ctx st (factor v) := by
  unfold factor
  mono_straight


theorem pointer_mono {p : V} {off : ℕ} : MonoAt ctx st (pointer p off) := by
  unfold pointer
  mono_straight


theorem pooledCell_mono {find : Scope → Option Cell} {learn : Cell → Scope → Scope} {mk : Cell → LOp} : MonoAt ctx st (pooledCell find learn mk) := by
  unfold pooledCell
  mono_straight


theorem pooled_mono {d : V} {find : Scope → Option Cell} {learn : Cell → Scope → Scope} {mk : Cell → LOp} : MonoAt ctx st (pooled d find learn mk) := by
  unfold pooled
  mono_straight


theorem isLazy_mono {v : V} {k : Kind} : MonoAt ctx st (isLazy v k) := by
  unfold isLazy
  mono_straight


theorem isSelfFp_mono {n : Cell} : MonoAt ctx st (isSelfFp n) := by
  unfold isSelfFp
  mono_straight


theorem advance_mono  : MonoAt ctx st (advance) := by
  unfold advance
  mono_straight


theorem expect_mono {e : Event → Bool} {what : String} : MonoAt ctx st (expect e what) := by
  unfold expect
  mono_straight


theorem endStmt_mono  : MonoAt ctx st (endStmt) := by
  unfold endStmt
  mono_straight


theorem bindRun_mono {vs : List V} {base : Cell} : MonoAt ctx st (bindRun vs base) := by
  unfold bindRun
  exact forM_mono (fun _ _ => bindTo_mono _ _) _ _


theorem takeRun_mono {vs : List V} : MonoAt ctx st (takeRun vs) := by
  unfold takeRun bindRun
  refine MonoAt.get_bind (wp_bind.mpr (wp_mono (bindRun_wp st.next vs 0 st)
    fun _ st₁ ⟨he, hg, _⟩ => wp_modify.mpr ⟨?_, hg⟩))
  show st.next ≤ st.next + vs.length
  exact Nat.le_add_right _ _


theorem spongeInPlace_mono {vs : List V} {up : List Stmt} : MonoAt ctx st (spongeInPlace vs up) := by
  unfold spongeInPlace
  mono_straight


theorem onAlloc_mono {vs : List V} {k : Kind} {up : List Stmt} : MonoAt ctx st (onAlloc vs k up) := by
  unfold onAlloc
  mono_straight


theorem flushN_mono {up : List Stmt} : ∀ {fuel : ℕ} {st : St}, MonoAt ctx st (flushN up fuel)
  | 0, _ => by unfold flushN; exact MonoAt.pure
  | fuel + 1, st => by
      have ih : ∀ st, MonoAt ctx st (flushN up fuel) := fun _ => flushN_mono
      unfold flushN
      repeat' (first | exact ih _ | mono_step)

theorem flush_mono {up : List Stmt} : MonoAt ctx st (flush up) := by
  unfold flush
  mono_straight

theorem beginStmt_mono {up : List Stmt} : MonoAt ctx st (beginStmt up) := by
  unfold beginStmt
  mono_straight

theorem destBits_mono {d : Dest} : MonoAt ctx st (destBits d) := by
  unfold destBits
  mono_straight

set_option maxHeartbeats 2000000 in
theorem placeHint_mono {h : Hint} : MonoAt ctx st (placeHint h) := by
  have hc : ∀ (b : V) st, MonoAt ctx st (cellOf b) := fun _ _ => cellOf_mono
  have ha : ∀ (b : V) st, MonoAt ctx st (cellAt b) := fun _ _ => cellAt_mono
  cases h <;> unfold placeHint <;> mono_straight

set_option maxHeartbeats 2000000 in
theorem placeAtom_mono {a : Atom} : MonoAt ctx st (placeAtom a) := by
  have hc : ∀ (b : V) st, MonoAt ctx st (cellOf b) := fun _ _ => cellOf_mono
  have ha : ∀ (b : V) st, MonoAt ctx st (cellAt b) := fun _ _ => cellAt_mono
  cases a <;> unfold placeAtom <;> mono_straight

theorem allocTable_mono {n : ℕ} : MonoAt ctx st (allocTable n) := by
  unfold allocTable
  mono_straight

theorem sharedTable_mono {fs : List String} : MonoAt ctx st (sharedTable fs) := by
  unfold sharedTable
  mono_straight

theorem loopCount_mono {f : String} {args : List V} {cells : List Cell} :
    MonoAt ctx st (loopCount f args cells) := by
  unfold loopCount
  mono_straight

theorem placeCall_mono {f : String} {argVs : List V} {args rets : List Cell} {cond : Option Cell}
    {tail : Bool} : MonoAt ctx st (placeCall f argVs args rets cond tail) := by
  unfold placeCall
  mono_straight

theorem matchCells_mono {x : V} {rest : List Stmt} {chained : Bool} :
    MonoAt ctx st (matchCells x rest chained) := by
  unfold matchCells
  mono_straight

end Prims

/-! ## Blocks, statements, arms -/

section Blocks

variable {ctx : Ctx}

theorem wp_and {α : Type} {m : P α} {st : St} {Q₁ Q₂ : α → St → Prop} (h₁ : wpP m ctx st Q₁)
    (h₂ : wpP m ctx st Q₂) : wpP m ctx st fun a st' => Q₁ a st' ∧ Q₂ a st' :=
  fun a st' he => ⟨h₁ a st' he, h₂ a st' he⟩

/-- **A block in a scope of its own** gives back the output and the pools. -/
theorem inBlock_mono {m : P Unit} (hm : ∀ st, MonoAt ctx st m) (st : St) :
    wpP (inBlock m) ctx st fun _ st' => MonoR st st' ∧ st'.out = st.out ∧
      st'.scope = st.scope := by
  unfold inBlock
  refine wp_bind.mpr (wp_mono (wp_and (expect_mono (st := st)) (wp_expect (Q := fun _ st' => Eqv st st') fun st' h => h))
    fun _ st₁ ⟨h₁, he₁⟩ => ?_)
  refine wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_set.mpr (wp_bind.mpr (wp_mono (hm _)
    fun _ st₂ h₂ => wp_bind.mpr (wp_mono flush_mono fun _ st₃ h₃ => wp_bind.mpr
      (wp_mono expect_mono fun _ st₄ h₄ => ?_)))))))
  have h14 : MonoR st₁ st₄ := (h₂.trans h₃).trans h₄
  refine wp_bind.mpr (wp_get.mpr ?_)
  have fin : ∀ st₅, MonoR st₄ st₅ → wpP (do
      let st ← get
      set { st with out := st₁.out, scope := st₁.scope }
      pure st.out.toList : P (List PStmt)) ctx st₅ fun _ st' => MonoR st st' ∧ st'.out = st.out ∧
        st'.scope = st.scope := fun st₅ h₅ =>
    wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_set.mpr (wp_pure.mpr
      ⟨(h₁.trans (h14.trans h₅)).trans (MonoR.refl _), he₁.out, he₁.scope⟩))))
  dsimp only
  split
  · refine wp_bind.mpr (wp_mono fresh_mono fun _ st₅ h₅ => wp_bind.mpr (wp_mono emitOp_mono
      fun _ st₆ h₆ => fin st₆ (h₅.trans h₆)))
  · exact fin st₄ (MonoR.refl _)

/-- **A `match`**, its arms placed from the next free cell on. -/
theorem placeMatch_mono {x : V} {n : ℕ} {rest : List Stmt} {entered : Option (ℕ × Cell)}
    {chained : Bool} {armsAt : Cell → ArmExit → P (List (List PStmt))}
    (harms : ∀ base exit st, wpP (armsAt base exit) ctx st fun _ st' =>
      base ≤ st'.next ∧ LocsLe st.locs st'.locs) (st : St) :
    MonoAt ctx st (placeMatch x n rest entered chained armsAt) := by
  have hb : ∀ (exit : ArmExit) (st : St) {β : Type} {k : List (List PStmt) → P β},
      (∀ a st', MonoR st st' → MonoAt ctx st' (k a)) → MonoAt ctx st (armsAt st.next exit >>= k) :=
    fun exit st _ k hk => MonoAt.bind (wp_mono (harms st.next exit st) fun _ _ h => h) hk
  unfold placeMatch
  repeat' (first | refine hb _ _ fun _ _ _ => ?_ | mono_step)

theorem atom_stmt_mono {a : Atom} {rest : List Stmt} (st : St) :
    MonoAt ctx st (placeStmt (.atom a) rest) := by
  rw [placeStmt]
  mono_straight

set_option maxHeartbeats 2000000 in
theorem call_stmt_mono {f : String} {args rets : List V} {rest : List Stmt} (st : St) :
    MonoAt ctx st (placeStmt (.call f args rets) rest) := by
  have hc : ∀ (b : V) st, MonoAt ctx st (cellOf b) := fun _ _ => cellOf_mono
  have ha : ∀ (b : V) st, MonoAt ctx st (cellAt b) := fun _ _ => cellAt_mono
  rw [placeStmt]
  mono_straight

set_option maxHeartbeats 2000000 in
theorem callIf_stmt_mono {c : V} {f : String} {args : List V} {rest : List Stmt} (st : St) :
    MonoAt ctx st (placeStmt (.callIf c f args) rest) := by
  have hc : ∀ (b : V) st, MonoAt ctx st (cellOf b) := fun _ _ => cellOf_mono
  rw [placeStmt]
  mono_straight

set_option maxHeartbeats 2000000 in
theorem dispatch_stmt_mono {x : V} {fs : List String} {args rets : List V} {rest : List Stmt}
    (st : St) : MonoAt ctx st (placeStmt (.dispatch x fs args rets) rest) := by
  have hc : ∀ (b : V) st, MonoAt ctx st (cellOf b) := fun _ _ => cellOf_mono
  have ha : ∀ (b : V) st, MonoAt ctx st (cellAt b) := fun _ _ => cellAt_mono
  rw [placeStmt]
  mono_straight

theorem ret_stmt_mono {vs : List V} {rest : List Stmt} (st : St) :
    MonoAt ctx st (placeStmt (.ret vs) rest) := by
  have ha : ∀ (b : V) st, MonoAt ctx st (cellAt b) := fun _ _ => cellAt_mono
  rw [placeStmt]
  mono_straight

mutual
/-- **A block moves neither the next free cell back nor a place.** -/
theorem placeBlock_mono : ∀ (ss : List Stmt) (st : St), MonoAt ctx st (placeBlock ss)
  | [], st => by
      rw [placeBlock]
      exact MonoAt.pure
  | s :: rest, st => by
      rw [placeBlock]
      exact MonoAt.bind (placeStmt_mono s rest st) fun _ st₁ _ => MonoAt.bind endStmt_mono
        fun _ st₂ _ => placeBlock_mono rest st₂

theorem placeStmt_mono : ∀ (s : Stmt) (rest : List Stmt) (st : St),
    MonoAt ctx st (placeStmt s rest)
  | .atom a, rest, st => atom_stmt_mono st
  | .ite c z nz, rest, st => by
      have hz : ∀ st, MonoAt ctx st (inBlock (placeBlock z)) := fun st =>
        wp_mono (inBlock_mono (fun st => placeBlock_mono z st) st) fun _ _ h => h.1
      have hnz : ∀ st, MonoAt ctx st (inBlock (placeBlock nz)) := fun st =>
        wp_mono (inBlock_mono (fun st => placeBlock_mono nz st) st) fun _ _ h => h.1
      rw [placeStmt]
      repeat' (first | refine MonoAt.bind (hz _) fun _ _ _ => ?_ | refine MonoAt.bind (hnz _) fun _ _ _ => ?_ | mono_step)
  | .match_ x arms, rest, st => by
      rw [placeStmt]
      refine MonoAt.bind flush_mono fun _ st₁ _ => MonoAt.get_bind (MonoAt.setS_bind
        (monoR_same rfl rfl) (placeMatch_mono (fun base exit st => wp_mono
          (placeArms_mono arms 0 arms.length base exit st) fun _ _ h => ⟨h.1, h.2.1⟩) _))
  | .call f args rets, rest, st => call_stmt_mono st
  | .callIf c f args, rest, st => callIf_stmt_mono st
  | .dispatch x fs args rets, rest, st => dispatch_stmt_mono st
  | .ret vs, rest, st => ret_stmt_mono st

/-- **The arms of a `match`** rewind the next free cell to their base: only the base is below the
end; the places grow and the output is given back. -/
theorem placeArms_mono : ∀ (arms : List (List Stmt)) (j n : ℕ) (base : Cell) (exit : ArmExit)
    (st : St), wpP (placeArms arms j n base exit) ctx st fun _ st' =>
      base ≤ st'.next ∧ LocsLe st.locs st'.locs ∧ st'.out = st.out
  | [], j, n, base, exit, st => by
      rw [placeArms]
      exact wp_bind.mpr (wp_modify.mpr (wp_pure.mpr ⟨le_rfl, LocsLe.refl _, rfl⟩))
  | arm :: more, j, n, base, exit, st => by
      rw [placeArms]
      refine wp_bind.mpr (wp_modify.mpr (wp_bind.mpr (wp_mono (inBlock_mono
        (fun st => placeBlock_mono arm st) _) fun blk st₁ ⟨h₁, ho₁, _⟩ => ?_)))
      have tail : ∀ (lv : List PStmt) (st₂ : St), MonoR st₁ st₂ → st₂.out = st₁.out →
          wpP (do
            let top := (← get).next
            let blocks ← placeArms more (j + 1) n base exit
            modify fun s => { s with next := max s.next top }
            pure ((blk ++ lv) :: blocks) : P (List (List PStmt))) ctx st₂ fun _ st' =>
            base ≤ st'.next ∧ LocsLe st.locs st'.locs ∧ st'.out = st.out := by
        intro lv st₂ h₂ ho₂
        refine wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_mono (placeArms_mono more (j + 1) n base
          exit st₂) fun _ st₃ ⟨h₃, hl₃, ho₃⟩ => wp_bind.mpr (wp_modify.mpr (wp_pure.mpr
            ⟨le_trans h₃ (le_max_left _ _), (h₁.2.trans h₂.2).trans hl₃, ?_⟩)))))
        show st₃.out = st.out
        rw [ho₃, ho₂, ho₁]
      split
      · unfold fresh
        refine wp_bind.mpr (wp_modifyGet.mpr (wp_bind.mpr (wp_pure.mpr ?_)))
        exact tail _ _ ⟨by simp, LocsLe.refl _⟩ rfl
      · exact wp_bind.mpr (wp_pure.mpr (tail _ _ (MonoR.refl _) rfl))
end

end Blocks

end
end LeanVM.Guest.Backend.Complete
