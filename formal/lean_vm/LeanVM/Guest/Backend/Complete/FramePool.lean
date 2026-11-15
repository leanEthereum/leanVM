/-
  LeanVM.Guest.Backend.Complete.FramePool

  The pools of products and shifted pointers stay off the temporaries' cells through every
  statement's placement.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameLocs
public import LeanVM.Guest.Backend.Complete.FrameStmt

/-!
# The multiplied pool cells

`PoolNT` says no cell of the scope's products or shifted pointers is a temporary's cell. Every
placement step keeps the output's instructions and makes a new such cell only with a `MUL` it
emits (`PK`); `Inst.Ok.tops` keeps a cell a `MUL` of the final placement writes off the
temporaries. A block in a scope of its own gives the scope and the output back, and an entered
`match` replaces only the chain node the output ends with. So every statement keeps `PoolNT` once
the final placement has its instructions (`poolKeepStmt : PoolKeepStmt`).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

section PK

variable {ctx : Ctx} {α β : Type}

/-- A cell a `MUL` of the output writes, or a cell of `st`'s pools of products and shifted
pointers. -/
def NewC (st st' : St) (o : Cell) : Prop :=
  (∃ k, st.scope.muls.get? k = some o) ∨ (∃ c l e, st.scope.mats.get? c = some l ∧ (e, o) ∈ l) ∨
    ∃ h a b, PStmt.op h (.mul a b o) ∈ st'.out.toList

/-- The straight-line instructions of the output kept. -/
def OpsKept (st st' : St) : Prop := ∀ h o, PStmt.op h o ∈ st.out.toList → PStmt.op h o ∈ st'.out.toList

/-- From `st` to `st'`: the output's instructions kept, and every cell of the pools of products and
shifted pointers one of `st`'s or written by a `MUL` of the output. -/
def PK (st st' : St) : Prop :=
  OpsKept st st' ∧ (∀ k o, st'.scope.muls.get? k = some o → NewC st st' o) ∧
    ∀ c l, st'.scope.mats.get? c = some l → ∀ p ∈ l, NewC st st' p.2

theorem NewC.lift {st st' st'' : St} {o : Cell} (h : NewC st st' o) (hk : OpsKept st' st'') :
    NewC st st'' o := by
  rcases h with h | h | ⟨hh, a, b, hm⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hh, a, b, hk _ _ hm⟩)

theorem PK.refl (st : St) : PK st st :=
  ⟨fun _ _ h => h, fun k _ h => Or.inl ⟨k, h⟩, fun c l h p hp => Or.inr (Or.inl ⟨c, l, p.1, h, hp⟩)⟩

theorem NewC.back {st₁ st₂ st₃ : St} {o : Cell} (h₁ : PK st₁ st₂) (hk : OpsKept st₂ st₃)
    (h : NewC st₂ st₃ o) : NewC st₁ st₃ o := by
  rcases h with ⟨k, hk'⟩ | ⟨c, l, e, hc, he⟩ | h
  · exact (h₁.2.1 k o hk').lift hk
  · exact (h₁.2.2 c l hc _ he).lift hk
  · exact Or.inr (Or.inr h)

theorem PK.trans {st₁ st₂ st₃ : St} (h₁ : PK st₁ st₂) (h₂ : PK st₂ st₃) : PK st₁ st₃ := by
  have back : ∀ o, NewC st₂ st₃ o → NewC st₁ st₃ o := fun o h => h.back h₁ h₂.1
  exact ⟨fun h o hm => h₂.1 h o (h₁.1 h o hm), fun k o h => back o (h₂.2.1 k o h),
    fun c l h p hp => back p.2 (h₂.2.2 c l h p hp)⟩

/-- Every success of `m` from `st` is `PK` of `st`. -/
def PKAt (ctx : Ctx) (st : St) (m : P α) : Prop := wpP m ctx st fun _ st' => PK st st'

variable {st : St}

theorem PKAt.pure {a : α} : PKAt ctx st (Pure.pure a) := wp_pure.mpr (PK.refl st)

theorem PKAt.fail {msg : String} : PKAt ctx st (failP msg : P α) := wp_failP

theorem PKAt.fail_bind {msg : String} {f : α → P β} :
    PKAt ctx st ((failP msg : P α) >>= f) := wp_bind.mpr wp_failP

theorem PKAt.bind {m : P α} {f : α → P β} (hm : PKAt ctx st m)
    (hf : ∀ a st', PK st st' → PKAt ctx st' (f a)) : PKAt ctx st (m >>= f) :=
  wp_bind.mpr (wp_mono hm fun a st' h => wp_mono (hf a st' h) fun _ _ h' => h.trans h')

theorem PKAt.get_bind {f : St → P β} (h : PKAt ctx st (f st)) : PKAt ctx st (get >>= f) :=
  wp_bind.mpr (wp_get.mpr h)

theorem PKAt.read_bind {f : Ctx → P β} (h : PKAt ctx st (f ctx)) :
    PKAt ctx st (read >>= f) := wp_bind.mpr (wp_read.mpr h)

theorem PKAt.peek_bind {f : Option Event → P β} (h : PKAt ctx st (f st.rest.head?)) :
    PKAt ctx st (peek >>= f) := wp_bind.mpr (wp_peek.mpr h)

theorem PKAt.guard {c : Prop} [Decidable c] {msg : String} {f : PUnit → P β}
    (h : ¬c → PKAt ctx st (f PUnit.unit)) :
    PKAt ctx st (if c then failP msg >>= f else f PUnit.unit) := by
  split
  · exact PKAt.fail_bind
  · next hc => exact h hc

theorem PKAt.mod {g : St → St} (h : PK st (g st)) : PKAt ctx st (modify g) :=
  wp_modify.mpr h

theorem PKAt.mod_bind {g : St → St} {f : PUnit → P β} (h : PK st (g st))
    (hf : PKAt ctx (g st) (f ⟨⟩)) : PKAt ctx st (modify g >>= f) :=
  wp_bind.mpr (wp_modify.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem PKAt.modG {g : St → α × St} (h : PK st (g st).2) :
    PKAt ctx st (modifyGet g) := wp_modifyGet.mpr h

theorem PKAt.modG_bind {g : St → α × St} {f : α → P β} (h : PK st (g st).2)
    (hf : PKAt ctx (g st).2 (f (g st).1)) : PKAt ctx st (modifyGet g >>= f) :=
  wp_bind.mpr (wp_modifyGet.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem PKAt.setS {s : St} (h : PK st s) : PKAt ctx st (set s : P PUnit) := wp_set.mpr h

theorem PKAt.setS_bind {s : St} {f : PUnit → P β} (h : PK st s) (hf : PKAt ctx s (f ⟨⟩)) :
    PKAt ctx st (set s >>= f) :=
  wp_bind.mpr (wp_set.mpr (wp_mono hf fun _ _ h' => h.trans h'))

theorem PKAt.discard {m : P α} (h : PKAt ctx st m) : PKAt ctx st (Functor.discard m) := by
  rw [Functor.discard, map_const, Function.comp_apply, map_eq_pure_bind]
  exact PKAt.bind h fun _ _ _ => PKAt.pure

theorem pk_same {s : St} (hm : s.scope.muls = st.scope.muls) (ht : s.scope.mats = st.scope.mats)
    (ho : s.out = st.out) : PK st s :=
  ⟨fun _ _ h => by rw [ho]; exact h, fun k _ h => Or.inl ⟨k, by rw [← hm]; exact h⟩,
    fun c l h p hp => Or.inr (Or.inl ⟨c, l, p.1, by rw [← ht]; exact h, hp⟩)⟩

theorem pk_push {s : St} {x : PStmt} (hm : s.scope.muls = st.scope.muls)
    (ht : s.scope.mats = st.scope.mats) (ho : s.out = st.out.push x) : PK st s :=
  ⟨fun _ _ h => by rw [ho, Rev.toList_push]; exact List.mem_append_left _ h,
    fun k _ h => Or.inl ⟨k, by rw [← hm]; exact h⟩,
    fun c l h p hp => Or.inr (Or.inl ⟨c, l, p.1, by rw [← ht]; exact h, hp⟩)⟩

theorem bindTo_pk (v : V) (l : Loc) : PKAt ctx st (bindTo v l) := by
  unfold bindTo
  refine wp_bind.mpr (wp_get.mpr ?_)
  split
  · exact wp_bind.mpr wp_failP
  · exact wp_modify.mpr (pk_same rfl rfl rfl)

theorem forM_pk {γ : Type} {f : γ → P PUnit} (hf : ∀ b st, PKAt ctx st (f b)) :
    ∀ (l : List γ) (st : St), PKAt ctx st (l.forM f)
  | [], _ => PKAt.pure
  | b :: l, st => by
      show PKAt ctx st (f b >>= fun _ => l.forM f)
      exact PKAt.bind (hf b st) fun _ st' _ => forM_pk hf l st'

theorem mapM_pk {γ δ : Type} {f : γ → P δ} (hf : ∀ b st, PKAt ctx st (f b)) :
    ∀ (l : List γ) (st : St), PKAt ctx st (l.mapM f)
  | [], _ => by rw [List.mapM_nil]; exact PKAt.pure
  | b :: l, st => by
      rw [List.mapM_cons]
      exact PKAt.bind (hf b st) fun _ st' _ => PKAt.bind (mapM_pk hf l st') fun _ _ _ =>
        PKAt.pure

theorem optionMapM_pk {γ δ : Type} {f : γ → P δ} (hf : ∀ b st, PKAt ctx st (f b))
    (o : Option γ) (st : St) : PKAt ctx st (o.mapM f) := by
  cases o with
  | none => exact PKAt.pure
  | some v =>
    rw [Option.mapM, map_eq_pure_bind]
    exact PKAt.bind (hf v st) fun _ _ _ => PKAt.pure

end PK
section Learn

/-- A pool's learning that adds to the products only the cell its instruction multiplies into. -/
def LearnOK (learn : Cell → Scope → Scope) (mk : Cell → LOp) : Prop :=
  ∀ o sc, (learn o sc).mats = sc.mats ∧ ∀ k o', (learn o sc).muls.get? k = some o' →
    sc.muls.get? k = some o' ∨ (o' = o ∧ ∃ a b, mk o = .mul a b o)

theorem learnOK_consts {mk : Cell → LOp} {k : ℕ × ℕ} :
    LearnOK (fun o sc => { sc with consts := sc.consts.insert k o }) mk :=
  fun _ _ => ⟨rfl, fun _ _ h => Or.inl h⟩

theorem learnOK_xors {mk : Cell → LOp} {k : ℕ × ℕ} :
    LearnOK (fun o sc => { sc with xors := sc.xors.insert k o }) mk :=
  fun _ _ => ⟨rfl, fun _ _ h => Or.inl h⟩

theorem learnOK_loads {mk : Cell → LOp} {k : ℕ × ℕ} :
    LearnOK (fun o sc => { sc with loads := sc.loads.insertIfNew k o }) mk :=
  fun _ _ => ⟨rfl, fun _ _ h => Or.inl h⟩

theorem learnOK_muls {a b : Cell} {k : ℕ × ℕ} :
    LearnOK (fun o sc => { sc with muls := sc.muls.insert k o }) (fun o => .mul a b o) := by
  intro o sc
  refine ⟨rfl, fun k' o' h => ?_⟩
  have h' : (sc.muls.insert k o).get? k' = some o' := h
  rw [PMap.get?_insert] at h'
  split at h'
  · exact Or.inr ⟨(Option.some.inj h').symm, a, b, rfl⟩
  · exact Or.inl h'

/-- One of the pools' learnings of `placeAtom`. -/
macro "learn_ok" : tactic => `(tactic| first
  | exact learnOK_consts | exact learnOK_xors | exact learnOK_loads | exact learnOK_muls)


end Learn

/-- A primitive already shown to be `PK` of its start. -/
syntax "pk_prim" : tactic

set_option hygiene false in
macro_rules | `(tactic| pk_prim) => `(tactic| first
  | with_reducible refine PKAt.bind fresh_pk fun _ _ _ => ?_
  | with_reducible exact fresh_pk
  | with_reducible refine PKAt.bind pushHint_pk fun _ _ _ => ?_
  | with_reducible exact pushHint_pk
  | with_reducible refine PKAt.bind takeHints_pk fun _ _ _ => ?_
  | with_reducible exact takeHints_pk
  | with_reducible refine PKAt.bind push_pk fun _ _ _ => ?_
  | with_reducible exact push_pk
  | with_reducible refine PKAt.bind emitOp_pk fun _ _ _ => ?_
  | with_reducible exact emitOp_pk
  | with_reducible refine PKAt.bind constCell_pk fun _ _ _ => ?_
  | with_reducible exact constCell_pk
  | with_reducible refine PKAt.bind oneCell_pk fun _ _ _ => ?_
  | with_reducible exact oneCell_pk
  | with_reducible refine PKAt.bind zeroCell_pk fun _ _ _ => ?_
  | with_reducible exact zeroCell_pk
  | with_reducible refine PKAt.bind mulCell_pk fun _ _ _ => ?_
  | with_reducible exact mulCell_pk
  | with_reducible refine PKAt.bind emitDeref_pk fun _ _ _ => ?_
  | with_reducible exact emitDeref_pk
  | with_reducible refine PKAt.bind selfFp_pk fun _ _ _ => ?_
  | with_reducible exact selfFp_pk
  | with_reducible refine PKAt.bind materialize_pk fun _ _ _ => ?_
  | with_reducible exact materialize_pk
  | with_reducible refine PKAt.bind cellAt_pk fun _ _ _ => ?_
  | with_reducible exact cellAt_pk
  | with_reducible refine PKAt.bind cellOf_pk fun _ _ _ => ?_
  | with_reducible exact cellOf_pk
  | with_reducible refine PKAt.bind factor_pk fun _ _ _ => ?_
  | with_reducible exact factor_pk
  | with_reducible refine PKAt.bind pointer_pk fun _ _ _ => ?_
  | with_reducible exact pointer_pk
  | with_reducible refine PKAt.bind (pooledCell_pk ?_) fun _ _ _ => ?_
  | with_reducible refine pooledCell_pk ?_
  | with_reducible refine PKAt.bind (pooled_pk ?_) fun _ _ _ => ?_
  | with_reducible refine pooled_pk ?_
  | with_reducible refine PKAt.bind isLazy_pk fun _ _ _ => ?_
  | with_reducible exact isLazy_pk
  | with_reducible refine PKAt.bind isSelfFp_pk fun _ _ _ => ?_
  | with_reducible exact isSelfFp_pk
  | with_reducible refine PKAt.bind advance_pk fun _ _ _ => ?_
  | with_reducible exact advance_pk
  | with_reducible refine PKAt.bind expect_pk fun _ _ _ => ?_
  | with_reducible exact expect_pk
  | with_reducible refine PKAt.bind endStmt_pk fun _ _ _ => ?_
  | with_reducible exact endStmt_pk
  | with_reducible refine PKAt.bind bindRun_pk fun _ _ _ => ?_
  | with_reducible exact bindRun_pk
  | with_reducible refine PKAt.bind takeRun_pk fun _ _ _ => ?_
  | with_reducible exact takeRun_pk
  | with_reducible refine PKAt.bind spongeInPlace_pk fun _ _ _ => ?_
  | with_reducible exact spongeInPlace_pk
  | with_reducible refine PKAt.bind onAlloc_pk fun _ _ _ => ?_
  | with_reducible exact onAlloc_pk
  | with_reducible refine PKAt.bind flushN_pk fun _ _ _ => ?_
  | with_reducible exact flushN_pk
  | with_reducible refine PKAt.bind flush_pk fun _ _ _ => ?_
  | with_reducible exact flush_pk
  | with_reducible refine PKAt.bind beginStmt_pk fun _ _ _ => ?_
  | with_reducible exact beginStmt_pk
  | with_reducible refine PKAt.bind destBits_pk fun _ _ _ => ?_
  | with_reducible exact destBits_pk
  | with_reducible refine PKAt.bind placeHint_pk fun _ _ _ => ?_
  | with_reducible exact placeHint_pk
  | with_reducible refine PKAt.bind placeAtom_pk fun _ _ _ => ?_
  | with_reducible exact placeAtom_pk
  | with_reducible refine PKAt.bind allocTable_pk fun _ _ _ => ?_
  | with_reducible exact allocTable_pk
  | with_reducible refine PKAt.bind sharedTable_pk fun _ _ _ => ?_
  | with_reducible exact sharedTable_pk
  | with_reducible refine PKAt.bind loopCount_pk fun _ _ _ => ?_
  | with_reducible exact loopCount_pk
  | with_reducible refine PKAt.bind placeCall_pk fun _ _ _ => ?_
  | with_reducible exact placeCall_pk
  | with_reducible refine PKAt.bind matchCells_pk fun _ _ _ => ?_
  | with_reducible exact matchCells_pk)

/-- One step of a walk that keeps the multiplied pool cells known. -/
macro "pk_step" : tactic => `(tactic| first
  | with_reducible exact PKAt.pure
  | with_reducible exact PKAt.fail
  | with_reducible exact PKAt.fail_bind
  | with_reducible refine PKAt.get_bind ?_
  | with_reducible refine PKAt.read_bind ?_
  | with_reducible refine PKAt.peek_bind ?_
  | with_reducible refine PKAt.guard fun _ => ?_
  | with_reducible refine PKAt.mod_bind ?_ ?_
  | with_reducible refine PKAt.modG_bind ?_ ?_
  | with_reducible refine PKAt.setS_bind ?_ ?_
  | with_reducible refine PKAt.mod ?_
  | with_reducible refine PKAt.modG ?_
  | with_reducible refine PKAt.setS ?_
  | exact pk_same rfl rfl rfl
  | exact pk_push rfl rfl rfl
  | exact PK.refl _
  | with_reducible refine PKAt.bind (bindTo_pk _ _) fun _ _ _ => ?_
  | with_reducible exact bindTo_pk _ _
  | with_reducible refine PKAt.bind (forM_pk ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine PKAt.bind (mapM_pk ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine PKAt.bind (optionMapM_pk ‹_› _ _) fun _ _ _ => ?_
  | with_reducible refine PKAt.bind (‹∀ st, PKAt _ st _› _) fun _ _ _ => ?_
  | with_reducible exact ‹∀ st, PKAt _ st _› _
  | with_reducible refine PKAt.discard ?_
  | with_reducible refine PKAt.bind (PKAt.discard ?_) fun _ _ _ => ?_
  | pk_prim
  | learn_ok
  | dsimp only
  | rw [pure_bind]
  | split)

macro "pk_straight" : tactic => `(tactic| repeat' pk_step)


section PKPrims

variable {ctx : Ctx} {st : St}

theorem fresh_pk : PKAt ctx st fresh := by
  unfold fresh
  exact PKAt.modG (pk_same rfl rfl rfl)

theorem pooledCell_pk {find : Scope → Option Cell} {learn : Cell → Scope → Scope}
    {mk : Cell → LOp} (hl : LearnOK learn mk) : PKAt ctx st (pooledCell find learn mk) := by
  unfold pooledCell
  refine wp_bind.mpr (wp_get.mpr ?_)
  split
  · exact wp_pure.mpr (PK.refl st)
  · simp only [fresh, emitOp, takeHints, push, wp_bind, wp_modifyGet, wp_modify, wp_pure]
    refine ⟨fun _ _ h => by simp [h], fun k o' h => ?_, fun c l h p hp => ?_⟩
    · rcases (hl st.next st.scope).2 k o' h with h | ⟨rfl, a, b, hmk⟩
      · exact Or.inl ⟨k, h⟩
      · exact Or.inr (Or.inr ⟨st.pending.toList, a, b, by rw [← hmk]; simp⟩)
    · have h' : (learn st.next st.scope).mats.get? c = some l := h
      rw [(hl st.next st.scope).1] at h'
      exact Or.inr (Or.inl ⟨c, l, p.1, h', hp⟩)

theorem pooled_pk {d : V} {find : Scope → Option Cell} {learn : Cell → Scope → Scope}
    {mk : Cell → LOp} (hl : LearnOK learn mk) : PKAt ctx st (pooled d find learn mk) := by
  unfold pooled
  exact PKAt.bind (pooledCell_pk hl) fun _ _ _ => bindTo_pk _ _

theorem pushHint_pk {h : LHint} : PKAt ctx st (pushHint h) := by
  unfold pushHint
  pk_straight


theorem takeHints_pk  : PKAt ctx st (takeHints) := by
  unfold takeHints
  pk_straight


theorem push_pk {s : PStmt} : PKAt ctx st (push s) := by
  unfold push
  pk_straight


theorem emitOp_pk {o : LOp} : PKAt ctx st (emitOp o) := by
  unfold emitOp
  pk_straight


theorem constCell_pk {k : ℕ × ℕ} : PKAt ctx st (constCell k) := by
  rw [constCell_eq]
  exact pooledCell_pk learnOK_consts

theorem oneCell_pk  : PKAt ctx st (oneCell) := by
  unfold oneCell
  pk_straight


theorem zeroCell_pk  : PKAt ctx st (zeroCell) := by
  unfold zeroCell
  pk_straight


/-- **A pooled product**: its cell is a product of the pool or written by the `MUL` emitted. -/
theorem mulCell_pkR {a b : Cell} : wpP (mulCell a b) ctx st fun o st' => PK st st' ∧ NewC st st' o := by
  unfold mulCell
  refine wp_bind.mpr (wp_get.mpr ?_)
  split
  · next o ho => exact wp_pure.mpr ⟨PK.refl st, Or.inl ⟨_, ho⟩⟩
  · simp only [fresh, emitOp, takeHints, push, wp_bind, wp_modifyGet, wp_modify, wp_pure]
    refine ⟨⟨fun _ _ h => by simp [h], fun k o' h => ?_, fun c l h p hp =>
      Or.inr (Or.inl ⟨c, l, p.1, h, hp⟩)⟩, Or.inr (Or.inr ⟨st.pending.toList, a, b, by simp⟩)⟩
    have h' : (st.scope.muls.insert (sorted a b) st.next).get? k = some o' := h
    rw [PMap.get?_insert] at h'
    split at h'
    · cases h'
      exact Or.inr (Or.inr ⟨st.pending.toList, a, b, by simp⟩)
    · exact Or.inl ⟨k, h'⟩

theorem mulCell_pk {a b : Cell} : PKAt ctx st (mulCell a b) :=
  wp_mono mulCell_pkR fun _ _ h => h.1

theorem emitDeref_pk {p off d : Cell} : PKAt ctx st (emitDeref p off d) := by
  unfold emitDeref
  pk_straight


theorem selfFp_pk  : PKAt ctx st (selfFp) := by
  unfold selfFp
  pk_straight


theorem materialize_pk {c e : Cell} : PKAt ctx st (materialize c e) := by
  unfold materialize
  dsimp only
  split
  · exact wp_pure.mpr (PK.refl st)
  · split
    · exact wp_bind.mpr wp_failP
    · refine wp_bind.mpr (wp_get.mpr ?_)
      split
      · exact wp_pure.mpr (PK.refl st)
      · generalize matStart _ _ _ _ = pr
        obtain ⟨src, dist⟩ := pr
        dsimp only
        refine wp_bind.mpr (wp_mono constCell_pk fun k s₁ h₁ => wp_bind.mpr (wp_mono mulCell_pkR
          fun o s₂ ⟨h₂, hn₂⟩ => wp_bind.mpr (wp_modify.mpr (wp_pure.mpr ?_))))
        have h₁₂ := h₁.trans h₂
        refine ⟨h₁₂.1, fun k o' h => h₁₂.2.1 k o' h, fun c' l h p hp => ?_⟩
        have h' : (s₂.scope.mats.insert c (((st.scope.mats.get? c).getD []) ++ [(e, o)])).get? c' =
          some l := h
        rw [NMap.get?_insert] at h'
        split at h'
        · cases h'
          rcases List.mem_append.mp hp with hp | hp
          · cases hm : st.scope.mats.get? c with
            | none => rw [hm] at hp; simp at hp
            | some l0 =>
              rw [hm] at hp
              exact Or.inr (Or.inl ⟨c, l0, p.1, hm, hp⟩)
          · obtain rfl := List.mem_singleton.mp hp
            exact NewC.back h₁ h₂.1 hn₂
        · exact h₁₂.2.2 c' l h' p hp

theorem cellAt_pk {v : V} : PKAt ctx st (cellAt v) := by
  unfold cellAt
  pk_straight


theorem cellOf_pk {v : V} : PKAt ctx st (cellOf v) := by
  unfold cellOf
  pk_straight


theorem factor_pk {v : V} : PKAt ctx st (factor v) := by
  unfold factor
  pk_straight


theorem pointer_pk {p : V} {off : ℕ} : PKAt ctx st (pointer p off) := by
  unfold pointer
  pk_straight


theorem isLazy_pk {v : V} {k : Kind} : PKAt ctx st (isLazy v k) := by
  unfold isLazy
  pk_straight


theorem isSelfFp_pk {n : Cell} : PKAt ctx st (isSelfFp n) := by
  unfold isSelfFp
  pk_straight


theorem advance_pk  : PKAt ctx st (advance) := by
  unfold advance
  pk_straight


theorem expect_pk {e : Event → Bool} {what : String} : PKAt ctx st (expect e what) := by
  unfold expect
  pk_straight


theorem endStmt_pk  : PKAt ctx st (endStmt) := by
  unfold endStmt
  pk_straight


theorem bindRun_pk {vs : List V} {base : Cell} : PKAt ctx st (bindRun vs base) := by
  unfold bindRun
  exact forM_pk (fun _ _ => bindTo_pk _ _) _ _


theorem takeRun_pk {vs : List V} : PKAt ctx st (takeRun vs) := by
  unfold takeRun
  pk_straight

theorem spongeInPlace_pk {vs : List V} {up : List Stmt} : PKAt ctx st (spongeInPlace vs up) := by
  unfold spongeInPlace
  pk_straight


theorem onAlloc_pk {vs : List V} {k : Kind} {up : List Stmt} : PKAt ctx st (onAlloc vs k up) := by
  unfold onAlloc
  pk_straight


theorem flushN_pk {up : List Stmt} : ∀ {fuel : ℕ} {st : St}, PKAt ctx st (flushN up fuel)
  | 0, _ => by unfold flushN; exact PKAt.pure
  | fuel + 1, st => by
      have ih : ∀ st, PKAt ctx st (flushN up fuel) := fun _ => flushN_pk
      unfold flushN
      repeat' (first | exact ih _ | pk_step)

theorem flush_pk {up : List Stmt} : PKAt ctx st (flush up) := by
  unfold flush
  pk_straight

theorem beginStmt_pk {up : List Stmt} : PKAt ctx st (beginStmt up) := by
  unfold beginStmt
  pk_straight

theorem destBits_pk {d : Dest} : PKAt ctx st (destBits d) := by
  unfold destBits
  pk_straight

set_option maxHeartbeats 2000000 in
theorem placeHint_pk {h : Hint} : PKAt ctx st (placeHint h) := by
  have hc : ∀ (b : V) st, PKAt ctx st (cellOf b) := fun _ _ => cellOf_pk
  have ha : ∀ (b : V) st, PKAt ctx st (cellAt b) := fun _ _ => cellAt_pk
  cases h <;> unfold placeHint <;> pk_straight

set_option maxHeartbeats 2000000 in
theorem placeAtom_pk {a : Atom} : PKAt ctx st (placeAtom a) := by
  have hc : ∀ (b : V) st, PKAt ctx st (cellOf b) := fun _ _ => cellOf_pk
  have ha : ∀ (b : V) st, PKAt ctx st (cellAt b) := fun _ _ => cellAt_pk
  cases a <;> unfold placeAtom <;> pk_straight

theorem allocTable_pk {n : ℕ} : PKAt ctx st (allocTable n) := by
  unfold allocTable
  pk_straight

theorem sharedTable_pk {fs : List String} : PKAt ctx st (sharedTable fs) := by
  unfold sharedTable
  pk_straight

theorem loopCount_pk {f : String} {args : List V} {cells : List Cell} :
    PKAt ctx st (loopCount f args cells) := by
  unfold loopCount
  pk_straight

theorem placeCall_pk {f : String} {argVs : List V} {args rets : List Cell} {cond : Option Cell}
    {tail : Bool} : PKAt ctx st (placeCall f argVs args rets cond tail) := by
  unfold placeCall
  pk_straight

theorem matchCells_pk {x : V} {rest : List Stmt} {chained : Bool} :
    PKAt ctx st (matchCells x rest chained) := by
  unfold matchCells
  pk_straight


end PKPrims

/-! ## Statements -/

section Stmts

variable {ctx : Ctx}

theorem inBlock_pk {m : P Unit} (hm : ∀ st, MonoAt ctx st m) (st : St) :
    PKAt ctx st (inBlock m) :=
  wp_mono (inBlock_mono hm st) fun _ _ ⟨_, ho, hs⟩ => pk_same (by rw [hs]) (by rw [hs]) ho

theorem mem_dropLast_of_ne {α : Type} {x y : α} : ∀ {l : List α}, l.getLast? = some y → x ∈ l →
    x ≠ y → x ∈ l.dropLast
  | [], h, _, _ => nomatch h
  | [a], h, hx, hne => by
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      subst h
      exact absurd (List.mem_singleton.mp hx) hne
  | a :: b :: t, h, hx, hne => by
      rw [List.dropLast_cons_cons]
      rw [List.getLast?_cons_cons] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_dropLast_of_ne h hx hne)

/-- An entered `match` replaces the chain node the output ends with. -/
theorem pk_chain {st s : St} {node : PStmt} {h : List LHint} {j x e o sf : Cell}
    {firsts : List ℕ} {stages : List (List (List PStmt))}
    (hb : st.out.back? = some (.chain h j x e o sf firsts stages))
    (hm : s.scope.muls = st.scope.muls) (ht : s.scope.mats = st.scope.mats)
    (ho : s.out = st.out.pop.push node) : PK st s := by
  refine ⟨fun h' o' hx => ?_, fun k _ hk => Or.inl ⟨k, by rw [← hm]; exact hk⟩,
    fun c l hc p hp => Or.inr (Or.inl ⟨c, l, p.1, by rw [← ht]; exact hc, hp⟩)⟩
  rw [ho, Rev.toList_push, Rev.toList_pop]
  refine List.mem_append_left _ (mem_dropLast_of_ne (by rw [← Rev.back?_eq]; exact hb) hx ?_)
  intro h'
  cases h'

set_option maxHeartbeats 2000000 in
theorem placeMatch_pk {x : V} {n : ℕ} {rest : List Stmt} {entered : Option (ℕ × Cell)}
    {chained : Bool} {armsAt : Cell → ArmExit → P (List (List PStmt))}
    (harms : ∀ base exit st, PKAt ctx st (armsAt base exit)) (st : St) :
    PKAt ctx st (placeMatch x n rest entered chained armsAt) := by
  unfold placeMatch
  repeat' (first | refine PKAt.bind (harms _ _ _) fun _ _ _ => ?_ | (refine PKAt.setS_bind (pk_chain ‹_› rfl rfl rfl) ?_) | pk_step)

theorem placeArms_pk : ∀ (arms : List (List Stmt)) (j n : ℕ) (base : Cell) (exit : ArmExit)
    (st : St), PKAt ctx st (placeArms arms j n base exit)
  | [], j, n, base, exit, st => by
      rw [placeArms]
      pk_straight
  | arm :: more, j, n, base, exit, st => by
      have ha : ∀ st, PKAt ctx st (inBlock (placeBlock arm)) :=
        inBlock_pk fun st => placeBlock_mono arm st
      have hm : ∀ st, PKAt ctx st (placeArms more (j + 1) n base exit) :=
        fun st => placeArms_pk more (j + 1) n base exit st
      rw [placeArms]
      repeat' (first | refine PKAt.bind (ha _) fun _ _ _ => ?_ | refine PKAt.bind (hm _) fun _ _ _ => ?_ | pk_step)

set_option maxHeartbeats 2000000 in
/-- **A statement** keeps the output's instructions and makes new product cells only by `MUL`s. -/
theorem placeStmt_pk (s : Stmt) (rest : List Stmt) (st : St) : PKAt ctx st (placeStmt s rest) := by
  have hc : ∀ (b : V) st, PKAt ctx st (cellOf b) := fun _ _ => cellOf_pk
  have ha : ∀ (b : V) st, PKAt ctx st (cellAt b) := fun _ _ => cellAt_pk
  cases s with
  | ite c z nz =>
    have hz : ∀ st, PKAt ctx st (inBlock (placeBlock z)) := inBlock_pk fun st => placeBlock_mono z st
    have hnz : ∀ st, PKAt ctx st (inBlock (placeBlock nz)) :=
      inBlock_pk fun st => placeBlock_mono nz st
    rw [placeStmt]
    repeat' (first | refine PKAt.bind (hz _) fun _ _ _ => ?_ | refine PKAt.bind (hnz _) fun _ _ _ => ?_ | pk_step)
  | match_ x arms =>
    rw [placeStmt]
    exact PKAt.bind flush_pk fun _ st₁ _ => PKAt.get_bind (PKAt.setS_bind (pk_same rfl rfl rfl)
      (placeMatch_pk (fun base exit st => placeArms_pk arms 0 arms.length base exit st) _))
  | _ => rw [placeStmt]; pk_straight

/-- A cell of `st`'s pools kept off the temporaries, or one a `MUL` of the final placement writes. -/
theorem NewC.nt {I : Inst} {st st' : St} {o : Cell} (hok : I.Ok) (hnt : PoolNT I st.scope)
    (hout : OutOps I st') (h : NewC st st' o) : ¬ I.tc o := by
  rcases h with ⟨k, hk⟩ | ⟨c, l, e, hc, he⟩ | ⟨hh, a, b, hm⟩
  · exact hnt.1 k o hk
  · exact hnt.2 c l hc _ he
  · intro htc
    obtain ⟨p, hp, _⟩ := hok.tops _ htc _ (hout _ _ hm) (by simp [opCells])
    cases hp

theorem PKAt.poolKeep {α : Type} {I : Inst} {st : St} {m : P α} (h : PKAt ctx st m) :
    PoolKeep ctx I st m := fun hok hnt => wp_mono h fun _ _ hpk hout =>
  ⟨fun k o hk => (hpk.2.1 k o hk).nt hok hnt hout,
    fun c l hc p hp => (hpk.2.2 c l hc p hp).nt hok hnt hout⟩

/-- **`PoolKeepStmt`**: a statement's beginning and the whole statement keep the multiplied pool
cells off the temporaries. -/
theorem poolKeepStmt : PoolKeepStmt := fun _ _ st _ s rest =>
  ⟨PKAt.poolKeep beginStmt_pk,
    PKAt.poolKeep (PKAt.bind (placeStmt_pk s rest st) fun _ _ _ => endStmt_pk)⟩

end Stmts

end
end LeanVM.Guest.Backend.Complete
