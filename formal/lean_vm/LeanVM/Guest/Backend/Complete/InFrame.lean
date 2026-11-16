/-
  LeanVM.Guest.Backend.Complete.InFrame

  Placement keeps every cell inside the frame (P5): the cells its values take and every cell of
  this frame an instruction of the placed body names are below the frame size.
-/

module

public import LeanVM.Guest.Backend.Sound.Atoms
public import LeanVM.Guest.Backend.Sound.Cut
public import LeanVM.Guest.Backend.Complete.Scoped
public import LeanVM.Guest.Backend.Complete.Cells

/-!
# Inside the frame

`placeFn` sets a function's frame size to the next free cell at the end of its walk. The next
free cell only grows, but for the arms of a `match`, which each start from the cell the first
arm started from; after the arms it is past the longest. So the frame size is past every cell the
walk gave out, and every cell an instruction names is one it gave out, a cell of the frame's
header, or a cell of a value.

The invariant (`Good ctx n st`) bounds every cell the state holds (the values' places, the pools,
the placed statements) by `n`, the largest next free cell so far; each step of the walk keeps it
at `max n next` (`GrowsAt`). At the end `n` is the frame size.

`opCells` lists the cells of this frame an instruction names (a `KECCAK` names its runs; the
destination of `mulNextFrame` is a cell of the next frame and is not listed). The theorem,
`placeFn_inFrame`, needs of the trace only that a return area is no longer than the return
cells, which a scoped function satisfies (`Scoped`).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-! ## Cells named -/

/-- Every cell of this frame the instructions name is below `n`. -/
def OpsBelow (n : ℕ) (ops : List LOp) : Prop := ∀ o ∈ ops, ∀ c ∈ opCells o, c < n

/-- Every cell of this frame the instructions of a placed statement name is below `n`, wherever
it is laid out. -/
def StmtBelow (n : ℕ) (s : PStmt) : Prop := ∀ pos, OpsBelow n (stmtOps s pos)

/-- A cell of a value or a pool: past the header, below `n`. -/
def GoodCell (n c : ℕ) : Prop := 2 ≤ c ∧ c < n

theorem GoodCell.mono {n n' c : ℕ} (h : GoodCell n c) (hn : n ≤ n') : GoodCell n' c :=
  ⟨h.1, lt_of_lt_of_le h.2 hn⟩

theorem OpsBelow.mono {n n' : ℕ} {ops : List LOp} (h : OpsBelow n ops) (hn : n ≤ n') :
    OpsBelow n' ops :=
  fun o ho c hc => lt_of_lt_of_le (h o ho c hc) hn

theorem StmtBelow.mono {n n' : ℕ} {s : PStmt} (h : StmtBelow n s) (hn : n ≤ n') :
    StmtBelow n' s :=
  fun pos => (h pos).mono hn

theorem opsBelow_append {n : ℕ} {a b : List LOp} :
    OpsBelow n (a ++ b) ↔ OpsBelow n a ∧ OpsBelow n b := by
  simp only [OpsBelow, List.mem_append]
  exact ⟨fun h => ⟨fun o ho => h o (Or.inl ho), fun o ho => h o (Or.inr ho)⟩,
    fun h o ho => by
      rcases ho with ho | ho
      · exact h.1 o ho
      · exact h.2 o ho⟩

theorem opsBelow_cons {n : ℕ} {o : LOp} {l : List LOp} :
    OpsBelow n (o :: l) ↔ (∀ c ∈ opCells o, c < n) ∧ OpsBelow n l := by
  simp only [OpsBelow, List.mem_cons]
  exact ⟨fun h => ⟨h o (Or.inl rfl), fun o' ho => h o' (Or.inr ho)⟩,
    fun h o' ho => by
      rcases ho with rfl | ho
      · exact h.1
      · exact h.2 o' ho⟩

theorem opsBelow_nil {n : ℕ} : OpsBelow n [] := fun _ h => nomatch h

/-- Every statement of a block is below `n`. -/
def BlockBelow (n : ℕ) (b : List PStmt) : Prop := ∀ s ∈ b, StmtBelow n s

theorem BlockBelow.mono {n n' : ℕ} {b : List PStmt} (h : BlockBelow n b) (hn : n ≤ n') :
    BlockBelow n' b :=
  fun s hs => (h s hs).mono hn

theorem blockOps_below {n : ℕ} : ∀ (b : List PStmt), BlockBelow n b → ∀ pos,
    OpsBelow n (blockOps b pos)
  | [], _, _ => opsBelow_nil
  | s :: ss, h, pos => by
      rw [blockOps, opsBelow_append]
      exact ⟨h s List.mem_cons_self pos,
        blockOps_below ss (fun s' hs' => h s' (List.mem_cons_of_mem _ hs')) _⟩

theorem armsOps_below {n : ℕ} : ∀ (as : List (List PStmt)), (∀ a ∈ as, BlockBelow n a) → ∀ pos,
    OpsBelow n (armsOps as pos)
  | [], _, _ => opsBelow_nil
  | a :: as, h, pos => by
      rw [armsOps, opsBelow_append]
      exact ⟨blockOps_below a (h a List.mem_cons_self) pos,
        armsOps_below as (fun a' ha' => h a' (List.mem_cons_of_mem _ ha')) _⟩

theorem stagesOps_below {n : ℕ} : ∀ (ss : List (List (List PStmt))),
    (∀ s ∈ ss, ∀ a ∈ s, BlockBelow n a) → ∀ pos, OpsBelow n (stagesOps ss pos)
  | [], _, _ => opsBelow_nil
  | s :: ss, h, pos => by
      rw [stagesOps, opsBelow_append]
      exact ⟨armsOps_below s (h s List.mem_cons_self) pos,
        stagesOps_below ss (fun s' hs' => h s' (List.mem_cons_of_mem _ hs')) _⟩

/-! ## The invariant -/

/-- Every cell the pools of a scope hold is a good cell below `n`. -/
structure ScopeGood (n : ℕ) (sc : Scope) : Prop where
  consts : ∀ (k : ℕ × ℕ) (o : Cell), sc.consts.get? k = some o → GoodCell n o
  xors : ∀ (k : ℕ × ℕ) (o : Cell), sc.xors.get? k = some o → GoodCell n o
  muls : ∀ (k : ℕ × ℕ) (o : Cell), sc.muls.get? k = some o → GoodCell n o
  loads : ∀ (k : ℕ × ℕ) (o : Cell), sc.loads.get? k = some o → GoodCell n o
  mats : ∀ (c : ℕ) (l : List (ℕ × Cell)), sc.mats.get? c = some l → ∀ p ∈ l, GoodCell n p.2
  selfFp : ∀ (o : Cell), sc.selfFp = some o → GoodCell n o

theorem ScopeGood.mono {n n' : ℕ} {sc : Scope} (h : ScopeGood n sc) (hn : n ≤ n') :
    ScopeGood n' sc where
  consts k o ho := (h.consts k o ho).mono hn
  xors k o ho := (h.xors k o ho).mono hn
  muls k o ho := (h.muls k o ho).mono hn
  loads k o ho := (h.loads k o ho).mono hn
  mats c l hl p hp := (h.mats c l hl p hp).mono hn
  selfFp o ho := (h.selfFp o ho).mono hn

/-- **Every cell the walk's state holds is below `n`**: the values' places, the pools, the placed
statements; the next free cell and the return area are below it too, and a return area still in
the trace is no longer than the return cells. -/
structure Good (ctx : Ctx) (n : ℕ) (st : St) : Prop where
  next : 2 ≤ st.next ∧ st.next ≤ n
  abi : 2 + ctx.argCells + ctx.retCells ≤ n
  locs : ∀ (v : V) (l : Loc), st.locs[v]? = some l → GoodCell n (locBase l)
  scope : ScopeGood n st.scope
  out : ∀ s ∈ st.out.toList, StmtBelow n s
  rest : ∀ (vs : List V), Event.alloc vs .ret ∈ st.rest → vs.length ≤ ctx.retCells
  chainIn : ∀ (nf : ℕ) (j : Cell), st.chainIn = some (nf, j) → GoodCell n j

theorem Good.mono {ctx : Ctx} {n n' : ℕ} {st : St} (h : Good ctx n st) (hn : n ≤ n') :
    Good ctx n' st where
  next := ⟨h.next.1, le_trans h.next.2 hn⟩
  abi := le_trans h.abi hn
  locs v l hl := (h.locs v l hl).mono hn
  scope := h.scope.mono hn
  out s hs := (h.out s hs).mono hn
  rest := h.rest
  chainIn nf j hj := (h.chainIn nf j hj).mono hn

/-- A state that differs in nothing the invariant reads, its trace a part of the old one's. -/
theorem Good.congr {ctx : Ctx} {n : ℕ} {st st' : St} (h : Good ctx n st)
    (hn : st'.next = st.next) (hl : st'.locs = st.locs) (hs : st'.scope = st.scope)
    (ho : st'.out = st.out) (hr : ∀ e ∈ st'.rest, e ∈ st.rest)
    (hc : st'.chainIn = st.chainIn := by rfl) : Good ctx n st' where
  next := hn ▸ h.next
  abi := h.abi
  locs v l hv := h.locs v l (hl ▸ hv)
  scope := hs ▸ h.scope
  out s hs' := h.out s (ho ▸ hs')
  rest vs hv := h.rest vs (hr _ hv)
  chainIn nf j hj := h.chainIn nf j (hc ▸ hj)

variable {ctx : Ctx} {α β : Type}

/-- From `st`, below `n`, every success of `m` keeps the invariant below the larger of `n` and
the next free cell, the next free cell does not go back, and the result satisfies `R` at that
bound. -/
def GrowsAt (ctx : Ctx) (n : ℕ) (st : St) (m : P α) (R : ℕ → α → Prop) : Prop :=
  wpP m ctx st fun a st' =>
    Good ctx (max n st'.next) st' ∧ st.next ≤ st'.next ∧ R (max n st'.next) a

/-- `GrowsAt` from every state that satisfies the invariant. -/
def Grows (ctx : Ctx) (m : P α) (R : ℕ → α → Prop) : Prop :=
  ∀ n st, Good ctx n st → GrowsAt ctx n st m R

variable {n : ℕ} {st : St}

theorem max_eq_of_good {n : ℕ} {st : St} (h : Good ctx n st) : max n st.next = n :=
  Nat.max_eq_left h.next.2

theorem GrowsAt.ofPure {a : α} {R : ℕ → α → Prop} (hg : Good ctx n st) (h : R n a) :
    GrowsAt ctx n st (Pure.pure a) R :=
  wp_pure.mpr ⟨by rw [max_eq_of_good hg]; exact hg, le_refl _, by rw [max_eq_of_good hg]; exact h⟩

theorem GrowsAt.bind {m : P α} {f : α → P β} {R₁ : ℕ → α → Prop} {R₂ : ℕ → β → Prop}
    (hm : GrowsAt ctx n st m R₁)
    (hf : ∀ a st' n', Good ctx n' st' → R₁ n' a → n ≤ n' → st.next ≤ st'.next →
      GrowsAt ctx n' st' (f a) R₂) :
    GrowsAt ctx n st (m >>= f) R₂ := by
  refine wp_bind.mpr fun a st₁ he b st₂ he' => ?_
  obtain ⟨hg₁, hn₁, hr₁⟩ := hm a st₁ he
  obtain ⟨hg₂, hn₂, hr₂⟩ := hf a st₁ _ hg₁ hr₁ (le_max_left _ _) hn₁ b st₂ he'
  have e : max (max n st₁.next) st₂.next = max n st₂.next := by
    rw [Nat.max_assoc, Nat.max_eq_right hn₂]
  rw [e] at hg₂ hr₂
  exact ⟨hg₂, le_trans hn₁ hn₂, hr₂⟩

/-- A call of an action that grows, then the rest. -/
theorem GrowsAt.call {m : P α} {f : α → P β} {R₁ : ℕ → α → Prop} {R₂ : ℕ → β → Prop}
    (hg : Good ctx n st) (hm : Grows ctx m R₁)
    (hf : ∀ a st' n', Good ctx n' st' → R₁ n' a → n ≤ n' → st.next ≤ st'.next →
      GrowsAt ctx n' st' (f a) R₂) :
    GrowsAt ctx n st (m >>= f) R₂ :=
  GrowsAt.bind (hm n st hg) hf

theorem GrowsAt.mono {m : P α} {R R' : ℕ → α → Prop} (h : GrowsAt ctx n st m R)
    (hr : ∀ n' a, R n' a → R' n' a) : GrowsAt ctx n st m R' :=
  wp_mono h fun a _ h' => ⟨h'.1, h'.2.1, hr _ a h'.2.2⟩

theorem GrowsAt.get_bind {f : St → P β} {R : ℕ → β → Prop} (h : GrowsAt ctx n st (f st) R) :
    GrowsAt ctx n st (get >>= f) R :=
  wp_bind.mpr (wp_get.mpr h)

theorem GrowsAt.read_bind {f : Ctx → P β} {R : ℕ → β → Prop} (h : GrowsAt ctx n st (f ctx) R) :
    GrowsAt ctx n st (read >>= f) R :=
  wp_bind.mpr (wp_read.mpr h)

theorem GrowsAt.fail {msg : String} {R : ℕ → α → Prop} : GrowsAt ctx n st (failP msg) R :=
  wp_failP

theorem GrowsAt.fail_bind {msg : String} {f : α → P β} {R : ℕ → β → Prop} :
    GrowsAt ctx n st ((failP msg : P α) >>= f) R :=
  wp_bind.mpr wp_failP

theorem GrowsAt.guard {c : Prop} [Decidable c] {msg : String} {f : PUnit → P β}
    {R : ℕ → β → Prop} (h : ¬c → GrowsAt ctx n st (f PUnit.unit) R) :
    GrowsAt ctx n st (if c then failP msg >>= f else f PUnit.unit) R := by
  split
  · exact GrowsAt.fail_bind
  · next hc => exact h hc

/-- A change of state that keeps the invariant at the larger bound. -/
theorem GrowsAt.ofModify {g : St → St} {R : ℕ → PUnit → Prop}
    (h : Good ctx (max n (g st).next) (g st)) (hn : st.next ≤ (g st).next)
    (hr : R (max n (g st).next) ⟨⟩) : GrowsAt ctx n st (modify g) R :=
  wp_modify.mpr ⟨h, hn, hr⟩

theorem grows_trans {st₁ st₂ : St} {b : β} {R : ℕ → β → Prop} (hn₁ : st.next ≤ st₁.next)
    (h : Good ctx (max (max n st₁.next) st₂.next) st₂ ∧ st₁.next ≤ st₂.next ∧
      R (max (max n st₁.next) st₂.next) b) :
    Good ctx (max n st₂.next) st₂ ∧ st.next ≤ st₂.next ∧ R (max n st₂.next) b := by
  have e : max (max n st₁.next) st₂.next = max n st₂.next := by
    rw [Nat.max_assoc, Nat.max_eq_right h.2.1]
  rw [e] at h
  exact ⟨h.1, le_trans hn₁ h.2.1, h.2.2⟩

theorem GrowsAt.modify_bind {g : St → St} {f : PUnit → P β} {R : ℕ → β → Prop}
    (hn : st.next ≤ (g st).next)
    (hf : GrowsAt ctx (max n (g st).next) (g st) (f ⟨⟩) R) :
    GrowsAt ctx n st (modify g >>= f) R :=
  wp_bind.mpr (wp_modify.mpr fun b st₂ he => grows_trans hn (hf b st₂ he))

theorem GrowsAt.modifyGet_bind {g : St → α × St} {f : α → P β} {R : ℕ → β → Prop}
    (hn : st.next ≤ (g st).2.next)
    (hf : GrowsAt ctx (max n (g st).2.next) (g st).2 (f (g st).1) R) :
    GrowsAt ctx n st (modifyGet g >>= f) R :=
  wp_bind.mpr (wp_modifyGet.mpr fun b st₂ he => grows_trans hn (hf b st₂ he))

theorem GrowsAt.ofModifyGet {g : St → α × St} {R : ℕ → α → Prop}
    (h : Good ctx (max n (g st).2.next) (g st).2) (hn : st.next ≤ (g st).2.next)
    (hr : R (max n (g st).2.next) (g st).1) : GrowsAt ctx n st (modifyGet g) R :=
  wp_modifyGet.mpr ⟨h, hn, hr⟩

theorem GrowsAt.peek_bind {f : Option Event → P β} {R : ℕ → β → Prop}
    (h : GrowsAt ctx n st (f st.rest.head?) R) : GrowsAt ctx n st (peek >>= f) R :=
  wp_bind.mpr (wp_peek.mpr h)

/-! ## Updates of the state -/

theorem pmap_insert_imp {γ : Type} {P : γ → Prop} {m : PMap γ} {k : ℕ × ℕ} {a : γ}
    (h : ∀ k o, m.get? k = some o → P o) (ha : P a) :
    ∀ k' o, (m.insert k a).get? k' = some o → P o := by
  intro k' o ho
  rw [PMap.get?_insert] at ho
  split at ho
  · cases ho; exact ha
  · exact h k' o ho

theorem pmap_insertIfNew_imp {γ : Type} {P : γ → Prop} {m : PMap γ} {k : ℕ × ℕ} {a : γ}
    (h : ∀ k o, m.get? k = some o → P o) (ha : P a) :
    ∀ k' o, (m.insertIfNew k a).get? k' = some o → P o := by
  intro k' o ho
  rw [PMap.get?_insertIfNew] at ho
  split at ho
  · cases ho; exact ha
  · exact h k' o ho

theorem nmap_insert_imp {γ : Type} {P : γ → Prop} {m : NMap γ} {k : ℕ} {a : γ}
    (h : ∀ k o, m.get? k = some o → P o) (ha : P a) :
    ∀ k' o, (m.insert k a).get? k' = some o → P o := by
  intro k' o ho
  rw [NMap.get?_insert] at ho
  split at ho
  · cases ho; exact ha
  · exact h k' o ho

variable {ctx : Ctx} {n : ℕ} {st : St}

theorem Good.bump (h : Good ctx n st) {k : ℕ} (hk : st.next ≤ k) :
    Good ctx (max n k) { st with next := k } where
  next := ⟨le_trans h.next.1 hk, le_max_right _ _⟩
  abi := le_trans h.abi (le_max_left _ _)
  locs v l hl := (h.locs v l hl).mono (le_max_left _ _)
  scope := h.scope.mono (le_max_left _ _)
  out s hs := (h.out s hs).mono (le_max_left _ _)
  rest := h.rest
  chainIn nf j hj := (h.chainIn nf j hj).mono (le_max_left _ _)

theorem Good.push (h : Good ctx n st) {s : PStmt} (hs : StmtBelow n s) :
    Good ctx n { st with out := st.out.push s } where
  next := h.next
  abi := h.abi
  locs := h.locs
  scope := h.scope
  out s' hs' := by
    rw [Rev.toList_push, List.mem_append, List.mem_singleton] at hs'
    rcases hs' with hs' | rfl
    · exact h.out s' hs'
    · exact hs
  rest := h.rest
  chainIn := h.chainIn

theorem Good.withScope (h : Good ctx n st) {sc : Scope} (hs : ScopeGood n sc) :
    Good ctx n { st with scope := sc } where
  next := h.next
  abi := h.abi
  locs := h.locs
  scope := hs
  out := h.out
  rest := h.rest
  chainIn := h.chainIn

theorem Good.insertLoc (h : Good ctx n st) {v : V} {l : Loc} (hl : GoodCell n (locBase l)) :
    Good ctx n { st with locs := st.locs.insert v l } where
  next := h.next
  abi := h.abi
  locs v' l' hv := by
    rw [KMap.getElem?_insert] at hv
    split at hv
    · cases hv; exact hl
    · exact h.locs v' l' hv
  scope := h.scope
  out := h.out
  rest := h.rest
  chainIn := h.chainIn

/-! ## Primitives -/

theorem fresh_grows : Grows ctx fresh (fun n c => GoodCell n c) := fun _ _ hg =>
  GrowsAt.ofModifyGet (hg.bump (Nat.le_succ _)) (Nat.le_succ _)
    ⟨hg.next.1, lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)⟩

/-- A step that changes nothing the invariant reads. -/
theorem GrowsAt.quiet {g : St → St} {R : ℕ → PUnit → Prop} (hg : Good ctx n st)
    (hn : (g st).next = st.next) (hl : (g st).locs = st.locs) (hs : (g st).scope = st.scope)
    (ho : (g st).out = st.out) (hr : ∀ e ∈ (g st).rest, e ∈ st.rest) (hR : R n ⟨⟩)
    (hc : (g st).chainIn = st.chainIn := by rfl) :
    GrowsAt ctx n st (modify g) R := by
  have e : max n (g st).next = n := by rw [hn]; exact max_eq_of_good hg
  exact GrowsAt.ofModify (by rw [e]; exact hg.congr hn hl hs ho hr hc) (le_of_eq hn.symm)
    (by rw [e]; exact hR)

theorem GrowsAt.keep_bind {β : Type} {g : St → St} {f : PUnit → P β} {R : ℕ → β → Prop}
    (hg : Good ctx n st) (hn : (g st).next = st.next) (hf : GrowsAt ctx n (g st) (f ⟨⟩) R) :
    GrowsAt ctx n st (modify g >>= f) R :=
  GrowsAt.modify_bind (le_of_eq hn.symm) (by rw [hn, max_eq_of_good hg]; exact hf)

theorem GrowsAt.keep {g : St → St} {R : ℕ → PUnit → Prop} (hg : Good ctx n st)
    (hn : (g st).next = st.next) (h : Good ctx n (g st)) (hR : R n ⟨⟩) :
    GrowsAt ctx n st (modify g) R :=
  GrowsAt.ofModify (by rw [hn, max_eq_of_good hg]; exact h) (le_of_eq hn.symm)
    (by rw [hn, max_eq_of_good hg]; exact hR)

theorem pushHint_grows (h : LHint) : Grows ctx (pushHint h) (fun _ _ => True) := fun _ _ hg =>
  GrowsAt.quiet hg rfl rfl rfl rfl (fun _ h => h) trivial

theorem takeHints_grows : Grows ctx takeHints (fun _ _ => True) := fun n st hg => by
  have e : max n st.next = n := max_eq_of_good hg
  have hg' : Good ctx (max n st.next) { st with pending := #[] } := by
    rw [e]; exact hg.congr rfl rfl rfl rfl (fun _ h => h)
  exact GrowsAt.ofModifyGet hg' (le_refl _) trivial

theorem push_grows {s : PStmt} (hg : Good ctx n st) (hs : StmtBelow n s) :
    GrowsAt ctx n st (push s) (fun _ _ => True) := by
  have e : max n st.next = n := max_eq_of_good hg
  have hg' : Good ctx (max n st.next) { st with out := st.out.push s } := by
    rw [e]; exact hg.push hs
  exact GrowsAt.ofModify hg' (le_refl _) trivial

theorem stmtBelow_op {h : List LHint} {o : LOp} (ho : ∀ c ∈ opCells o, c < n) :
    StmtBelow n (.op h o) := fun pos => by
  rw [stmtOps, opsBelow_cons]
  exact ⟨ho, opsBelow_nil⟩

theorem emitOp_grows {o : LOp} (hg : Good ctx n st) (ho : ∀ c ∈ opCells o, c < n) :
    GrowsAt ctx n st (emitOp o) (fun _ _ => True) :=
  GrowsAt.call hg takeHints_grows fun _ _ _ hg' _ hn _ =>
    push_grows hg' (stmtBelow_op fun c hc => lt_of_lt_of_le (ho c hc) hn)

/-- A step that keeps the next free cell. -/
theorem GrowsAt.ofSame {α : Type} {m : P α} {R : ℕ → α → Prop} (hg : Good ctx n st)
    (h : wpP m ctx st fun a st' => Good ctx n st' ∧ st'.next = st.next ∧ R n a) :
    GrowsAt ctx n st m R :=
  wp_mono h fun _ st' ⟨hg', hn, hr⟩ => by
    have e : max n st'.next = n := by rw [hn]; exact max_eq_of_good hg
    rw [e]
    exact ⟨hg', le_of_eq hn.symm, hr⟩

theorem bindTo_same {v : V} {l : Loc} (hg : Good ctx n st) (hl : GoodCell n (locBase l)) :
    wpP (bindTo v l) ctx st fun _ st' => Good ctx n st' ∧ st'.next = st.next ∧ True := by
  unfold bindTo
  refine wp_bind.mpr (wp_get.mpr ?_)
  split
  · exact wp_bind.mpr wp_failP
  · exact wp_modify.mpr ⟨hg.insertLoc hl, rfl, trivial⟩

theorem forM_inv {β : Type} {f : β → P PUnit} {I : St → Prop} :
    ∀ (l : List β), (∀ b ∈ l, ∀ st, I st → wpP (f b) ctx st fun _ st' => I st') →
      ∀ st, I st → wpP (l.forM f) ctx st fun _ st' => I st'
  | [], _, st, h => by
      show wpP (pure PUnit.unit) ctx st _
      exact wp_pure.mpr h
  | b :: l, hf, st, h => by
      show wpP (f b >>= fun _ => l.forM f) ctx st _
      exact wp_bind.mpr (wp_mono (hf b List.mem_cons_self st h) fun _ st' h' =>
        forM_inv l (fun b' hb' => hf b' (List.mem_cons_of_mem _ hb')) st' h')

theorem bindRun_same {vs : List V} {base : Cell} (hg : Good ctx n st)
    (hc : ∀ k < vs.length, GoodCell n (base + k)) :
    wpP (bindRun vs base) ctx st fun _ st' => Good ctx n st' ∧ st'.next = st.next ∧ True := by
  unfold bindRun
  refine wp_mono (forM_inv (I := fun st' => Good ctx n st' ∧ st'.next = st.next) _ ?_ st
    ⟨hg, rfl⟩) fun _ _ h => ⟨h.1, h.2, trivial⟩
  rintro ⟨v, k⟩ hm st₁ ⟨hg₁, hn₁⟩
  exact wp_mono (bindTo_same hg₁ (hc k (List.mem_zipIdx' hm).1)) fun _ _ h => ⟨h.1, h.2.1.trans hn₁⟩

theorem takeRun_grows (vs : List V) : Grows ctx (takeRun vs) (fun _ _ => True) := fun n st hg => by
  unfold takeRun
  refine GrowsAt.get_bind (wp_bind.mpr ?_)
  have hg' : Good ctx (max n (st.next + vs.length)) st := hg.mono (le_max_left _ _)
  refine wp_mono (bindRun_same (vs := vs) (base := st.next) hg' fun k hk =>
    ⟨le_trans hg.next.1 (Nat.le_add_right _ _), lt_of_lt_of_le (by omega) (le_max_right _ _)⟩)
    fun _ st₁ ⟨hg₁, hn₁, _⟩ => wp_modify.mpr ?_
  refine ⟨?_, by simp, trivial⟩
  have := hg₁.bump (k := st.next + vs.length) (by rw [hn₁]; exact Nat.le_add_right _ _)
  simpa using this

theorem cellAt_grows (v : V) :
    Grows ctx (cellAt v) (fun n c => GoodCell n c ∧ True) := fun n st hg => by
  unfold cellAt
  refine GrowsAt.get_bind ?_
  split
  · next c hc => exact GrowsAt.ofPure hg ⟨hg.locs v _ hc, trivial⟩
  · exact GrowsAt.fail

theorem constCell_grows (k : ℕ × ℕ) : Grows ctx (constCell k) (fun n c => GoodCell n c) :=
  fun n st hg => by
    unfold constCell
    refine GrowsAt.get_bind ?_
    split
    · next o ho => exact GrowsAt.ofPure hg (hg.scope.consts k o ho)
    · refine GrowsAt.call hg fresh_grows fun o st₁ n₁ hg₁ ho _ _ => ?_
      refine GrowsAt.bind (emitOp_grows hg₁ (by simp [opCells, ho.2]))
        fun _ st₂ n₂ hg₂ _ hn₂ _ => ?_
      refine GrowsAt.keep_bind hg₂ rfl (GrowsAt.ofPure ?_ (ho.mono hn₂))
      exact hg₂.withScope { hg₂.scope with
        consts := pmap_insert_imp hg₂.scope.consts (ho.mono hn₂) }

theorem oneCell_grows : Grows ctx oneCell (fun n c => GoodCell n c) := constCell_grows _

theorem zeroCell_grows : Grows ctx zeroCell (fun n c => GoodCell n c) := constCell_grows _

theorem mulCell_grows {a b : Cell} (hg : Good ctx n st) (ha : a < n) (hb : b < n) :
    GrowsAt ctx n st (mulCell a b) (fun n c => GoodCell n c) := by
  unfold mulCell
  refine GrowsAt.get_bind ?_
  split
  · next o ho => exact GrowsAt.ofPure hg (hg.scope.muls _ o ho)
  · refine GrowsAt.call hg fresh_grows fun o st₁ n₁ hg₁ ho hn₁ _ => ?_
    refine GrowsAt.bind (emitOp_grows hg₁ (by
        simp only [opCells, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl | rfl)
        · exact lt_of_lt_of_le ha hn₁
        · exact lt_of_lt_of_le hb hn₁
        · exact ho.2))
      fun _ st₂ n₂ hg₂ _ hn₂ _ => ?_
    refine GrowsAt.keep_bind hg₂ rfl (GrowsAt.ofPure ?_ (ho.mono hn₂))
    exact hg₂.withScope { hg₂.scope with
      muls := pmap_insert_imp hg₂.scope.muls (ho.mono hn₂) }

theorem emitDeref_grows {ptr off dst : Cell} (hg : Good ctx n st) (hp : ptr < n)
    (hd : GoodCell n dst) : GrowsAt ctx n st (emitDeref ptr off dst) (fun _ _ => True) := by
  unfold emitDeref
  refine GrowsAt.bind (emitOp_grows hg (by
      simp only [opCells, List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl | rfl) <;> [exact hp; exact hd.2])) fun _ st₂ n₂ hg₂ _ hn₂ _ => ?_
  refine GrowsAt.keep hg₂ rfl ?_ trivial
  exact hg₂.withScope { hg₂.scope with
    loads := pmap_insertIfNew_imp hg₂.scope.loads (hd.mono hn₂) }

theorem selfFp_grows : Grows ctx selfFp (fun n c => GoodCell n c) := fun n st hg => by
  unfold selfFp
  refine GrowsAt.read_bind ?_
  by_cases hm : ctx.isMain = true
  · simp only [hm, ↓reduceIte]
    exact oneCell_grows n st hg
  · simp only [hm, Bool.false_eq_true, ↓reduceIte]
    refine GrowsAt.get_bind ?_
    split
    · next o ho => exact GrowsAt.ofPure hg (hg.scope.selfFp o ho)
    · refine GrowsAt.call hg fresh_grows fun q st₁ n₁ hg₁ hq _ _ => ?_
      refine GrowsAt.call hg₁ (pushHint_grows _) fun _ st₂ n₂ hg₂ _ hn₂ _ => ?_
      refine GrowsAt.bind (emitOp_grows hg₂ (by
          simp only [opCells, List.mem_cons, List.not_mem_nil, or_false]
          rintro c (rfl | rfl)
          · exact lt_of_lt_of_le hq.2 hn₂
          · exact lt_of_lt_of_le (lt_of_lt_of_le (by decide) hg₂.next.1) hg₂.next.2))
        fun _ st₃ n₃ hg₃ _ hn₃ _ => ?_
      refine GrowsAt.call hg₃ fresh_grows fun o st₄ n₄ hg₄ ho hn₄ _ => ?_
      refine GrowsAt.bind (emitOp_grows hg₄ (by
          simp only [opCells, List.mem_cons, List.not_mem_nil, or_false]
          rintro c (rfl | rfl)
          · exact lt_of_lt_of_le hq.2 (le_trans hn₂ (le_trans hn₃ hn₄))
          · exact ho.2))
        fun _ st₅ n₅ hg₅ _ hn₅ _ => ?_
      refine GrowsAt.keep_bind hg₅ rfl (GrowsAt.ofPure ?_ (ho.mono hn₅))
      exact hg₅.withScope { hg₅.scope with
        selfFp := fun o' h => by cases h; exact ho.mono hn₅ }

theorem materialize_grows {c : Cell} (exp : ℕ) (hg : Good ctx n st) (hc : GoodCell n c) :
    GrowsAt ctx n st (materialize c exp) (fun n o => GoodCell n o) := by
  unfold materialize
  dsimp only
  split
  · exact GrowsAt.ofPure hg hc
  · refine GrowsAt.guard fun _ => ?_
    refine GrowsAt.get_bind ?_
    have hmats : ∀ p ∈ (st.scope.mats.get? c).getD [], GoodCell n p.2 := by
      intro p hp
      cases hm : st.scope.mats.get? c with
      | none => rw [hm] at hp; simp at hp
      | some l => rw [hm] at hp; exact hg.scope.mats c l hm p hp
    split
    · next e o hfind => exact GrowsAt.ofPure hg (hmats (e, o) (List.mem_of_find?_eq_some hfind))
    · generalize hpair : matStart st.scope c exp ((st.scope.mats.get? c).getD []) = pr
      obtain ⟨src, dist⟩ := pr
      dsimp only
      obtain ⟨e, -, hsrc⟩ := matStart_spec hpair
      have hsrc' : GoodCell n src := by
        rcases hsrc with h0 | hm
        · cases h0; exact hc
        · exact hmats (e, src) hm
      refine GrowsAt.call hg (constCell_grows _) fun k st₁ n₁ hg₁ hk hn₁ _ => ?_
      refine GrowsAt.bind (mulCell_grows hg₁ (lt_of_lt_of_le hsrc'.2 hn₁) hk.2)
        fun o st₂ n₂ hg₂ ho hn₂ _ => ?_
      refine GrowsAt.keep_bind hg₂ rfl (GrowsAt.ofPure ?_ ho)
      refine hg₂.withScope { hg₂.scope with mats := nmap_insert_imp hg₂.scope.mats ?_ }
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact (hmats p hp).mono (le_trans hn₁ hn₂)
      · obtain rfl := List.mem_singleton.mp hp
        exact ho

theorem cellOf_grows (v : V) : Grows ctx (cellOf v) (fun n c => GoodCell n c) := fun n st hg => by
  unfold cellOf
  refine GrowsAt.get_bind ?_
  split
  · next c hc => exact GrowsAt.ofPure hg (hg.locs v _ hc)
  · next c e hc => exact materialize_grows e hg (hg.locs v _ hc)
  · exact GrowsAt.fail

theorem factor_grows (v : V) : Grows ctx (factor v) (fun n r => GoodCell n r.1) :=
  fun n st hg => by
    unfold factor
    refine GrowsAt.get_bind ?_
    split
    · next c e hc =>
      split
      · exact GrowsAt.bind (materialize_grows e hg (hg.locs v _ hc))
          fun o _ n' hg' ho _ _ => GrowsAt.ofPure hg' ho
      · exact GrowsAt.ofPure hg (hg.locs v _ hc)
    · exact GrowsAt.call hg (cellOf_grows v) fun c _ n' hg' hc _ _ => GrowsAt.ofPure hg' hc

theorem pointer_grows (p : V) (off : ℕ) : Grows ctx (pointer p off) (fun n r => GoodCell n r.1) :=
  fun n st hg => by
    unfold pointer
    refine GrowsAt.call hg (factor_grows p) fun r st₁ n₁ hg₁ hr _ _ => ?_
    obtain ⟨c, e⟩ := r
    dsimp only
    exact GrowsAt.guard fun _ => GrowsAt.ofPure hg₁ hr

/-- A pooled result: the pool's cell, or a fresh one the instruction writes and the pool learns. -/
theorem pooledCell_grows {find : Scope → Option Cell} {learn : Cell → Scope → Scope}
    {mk : Cell → LOp} (hg : Good ctx n st)
    (hfind : ∀ o, find st.scope = some o → GoodCell n o)
    (hmk : ∀ n' o, n ≤ n' → GoodCell n' o → ∀ c ∈ opCells (mk o), c < n')
    (hlearn : ∀ n' sc o, n ≤ n' → ScopeGood n' sc → GoodCell n' o → ScopeGood n' (learn o sc)) :
    GrowsAt ctx n st (pooledCell find learn mk) (fun n o => GoodCell n o) := by
  unfold pooledCell
  refine GrowsAt.get_bind ?_
  split
  · next o ho => exact GrowsAt.ofPure hg (hfind o ho)
  · refine GrowsAt.call hg fresh_grows fun o st₁ n₁ hg₁ ho hn₁ _ => ?_
    refine GrowsAt.bind (emitOp_grows hg₁ (hmk n₁ o hn₁ ho)) fun _ st₂ n₂ hg₂ _ hn₂ _ => ?_
    refine GrowsAt.keep_bind hg₂ rfl (GrowsAt.ofPure ?_ (ho.mono hn₂))
    exact hg₂.withScope (hlearn n₂ _ o (le_trans hn₁ hn₂) hg₂.scope (ho.mono hn₂))

theorem bindTo_grows {v : V} {l : Loc} (hg : Good ctx n st) (hl : GoodCell n (locBase l)) :
    GrowsAt ctx n st (bindTo v l) (fun _ _ => True) :=
  GrowsAt.ofSame hg (bindTo_same hg hl)

theorem pooled_grows {d : V} {find : Scope → Option Cell} {learn : Cell → Scope → Scope}
    {mk : Cell → LOp} (hg : Good ctx n st)
    (hfind : ∀ o, find st.scope = some o → GoodCell n o)
    (hmk : ∀ n' o, n ≤ n' → GoodCell n' o → ∀ c ∈ opCells (mk o), c < n')
    (hlearn : ∀ n' sc o, n ≤ n' → ScopeGood n' sc → GoodCell n' o → ScopeGood n' (learn o sc)) :
    GrowsAt ctx n st (pooled d find learn mk) (fun _ _ => True) := by
  unfold pooled
  exact GrowsAt.bind (pooledCell_grows hg hfind hmk hlearn) fun o _ _ hg' ho _ _ =>
    bindTo_grows hg' ho

/-! ## The trace -/

theorem advance_grows : Grows ctx advance (fun _ _ => True) := fun _ _ hg =>
  GrowsAt.quiet hg rfl rfl rfl rfl (fun _ h => List.mem_of_mem_tail h) trivial

theorem expect_grows (e : Event → Bool) (what : String) :
    Grows ctx (expect e what) (fun _ _ => True) := fun n st hg => by
  unfold expect
  refine GrowsAt.peek_bind ?_
  split
  · split
    · exact advance_grows n st hg
    · exact GrowsAt.fail
  · exact GrowsAt.fail

theorem endStmt_grows : Grows ctx endStmt (fun _ _ => True) := fun _ _ hg =>
  GrowsAt.quiet hg rfl rfl rfl rfl (fun _ h => h) trivial

theorem spongeInPlace_cells {vs : List V} {up : List Stmt} (hg : Good ctx n st) :
    wpP (spongeInPlace vs up) ctx st fun r st' => st' = st ∧
      ∀ base, r = some base → ∀ k < vs.length, GoodCell n (base + k) := by
  unfold spongeInPlace
  refine wp_bind.mpr (wp_get.mpr ?_)
  dsimp only
  split
  · exact wp_pure.mpr ⟨rfl, fun _ h => nomatch h⟩
  · next base srcs hsrcs =>
    refine wp_pure.mpr ⟨rfl, fun b hb k hk => ?_⟩
    split at hb
    · next hc =>
      cases hb
      have hmem : ∀ c ∈ base :: srcs, GoodCell n c := by
        intro c hcm
        rw [← hsrcs, List.mem_filterMap] at hcm
        obtain ⟨⟨s, k'⟩, -, hf⟩ := hcm
        split at hf
        · split at hf
          · split at hf
            · next c' hl => cases hf; exact hg.locs _ _ hl
            · cases hf
          · cases hf
        · cases hf
      rw [hsrcs] at hc
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
      obtain ⟨⟨_, hlen⟩, hall⟩ := hc
      have hk' : k < (base :: srcs).length := by rw [hlen]; exact hk
      have hz : ((base :: srcs)[k], k) ∈ (base :: srcs).zipIdx :=
        List.mem_iff_getElem.mpr ⟨k, by simpa using hk', by rw [List.getElem_zipIdx]; simp only [Nat.zero_add]⟩
      have he := hall _ hz
      rw [← he]
      exact hmem _ (List.getElem_mem hk')
    · cases hb

theorem spongeInPlace_grows {vs : List V} {up : List Stmt} (hg : Good ctx n st) :
    GrowsAt ctx n st (spongeInPlace vs up)
      (fun n r => ∀ base, r = some base → ∀ k < vs.length, GoodCell n (base + k)) :=
  GrowsAt.ofSame hg (wp_mono (spongeInPlace_cells hg) fun _ _ h => ⟨h.1 ▸ hg, by rw [h.1], h.2⟩)

theorem onAlloc_grows {vs : List V} {kind : Kind} (up : List Stmt)
    (hret : kind = .ret → vs.length ≤ ctx.retCells) :
    Grows ctx (onAlloc vs kind up) (fun _ _ => True) := fun n st hg => by
  unfold onAlloc
  cases kind with
  | cell => exact takeRun_grows vs n st hg
  | pooled => exact GrowsAt.quiet hg rfl rfl rfl rfl (fun _ h => h) trivial
  | addr => exact GrowsAt.quiet hg rfl rfl rfl rfl (fun _ h => h) trivial
  | site => exact GrowsAt.ofPure hg trivial
  | ret =>
      refine GrowsAt.read_bind (GrowsAt.ofSame hg ?_)
      refine bindRun_same hg fun k hk => ⟨by omega, ?_⟩
      have := hret rfl
      have := hg.abi
      omega
  | padRun =>
      refine GrowsAt.call hg (takeRun_grows vs) fun _ st₁ n₁ hg₁ _ _ _ => ?_
      exact GrowsAt.quiet hg₁ rfl rfl rfl rfl (fun _ h => h) trivial
  | spongeRun =>
      refine GrowsAt.bind (spongeInPlace_grows (vs := vs) (up := up) hg)
        fun r st₁ n₁ hg₁ hr _ _ => ?_
      split
      · next _ base =>
        refine GrowsAt.bind (GrowsAt.ofSame (R := fun _ _ => True) hg₁
          (bindRun_same hg₁ (hr base rfl))) fun _ st₂ n₂ hg₂ _ _ _ => ?_
        exact GrowsAt.quiet hg₂ rfl rfl rfl rfl (fun _ h => h) trivial
      · exact takeRun_grows vs n₁ st₁ hg₁

theorem GrowsAt.discard {α : Type} {m : P α} {R : ℕ → α → Prop} (h : GrowsAt ctx n st m R) :
    GrowsAt ctx n st (discard m) (fun _ _ => True) := by
  rw [Functor.discard, map_const, Function.comp_apply, map_eq_pure_bind]
  exact GrowsAt.bind h fun _ _ _ hg _ _ _ => GrowsAt.ofPure hg trivial

theorem flushN_grows (up : List Stmt) : ∀ fuel, Grows ctx (flushN up fuel) (fun _ _ => True)
  | 0 => fun _ _ hg => GrowsAt.ofPure hg trivial
  | fuel + 1 => fun n st hg => by
      unfold flushN
      refine GrowsAt.peek_bind ?_
      split
      · next vs kind he =>
        have hmem : Event.alloc vs kind ∈ st.rest := by
          cases hr : st.rest with
          | nil => rw [hr] at he; cases he
          | cons e es => rw [hr] at he; cases he; exact List.mem_cons_self
        refine GrowsAt.call hg advance_grows fun _ st₁ n₁ hg₁ _ _ _ => ?_
        refine GrowsAt.call hg₁ (onAlloc_grows up fun hk => hg.rest vs (hk ▸ hmem))
          fun _ st₂ n₂ hg₂ _ _ _ => ?_
        exact flushN_grows up fuel n₂ st₂ hg₂
      · next v he =>
        refine GrowsAt.call hg advance_grows fun _ st₁ n₁ hg₁ _ _ _ => ?_
        refine GrowsAt.get_bind ?_
        split
        · next c e hc =>
          refine GrowsAt.bind (GrowsAt.discard (materialize_grows e hg₁ (hg₁.locs v _ hc)))
            fun _ st₂ n₂ hg₂ _ _ _ => ?_
          refine GrowsAt.keep_bind hg₂ rfl ?_
          exact flushN_grows up fuel n₂ _ (hg₂.congr rfl rfl rfl rfl (fun _ h => h))
        · refine GrowsAt.keep_bind hg₁ rfl ?_
          exact flushN_grows up fuel n₁ _ (hg₁.congr rfl rfl rfl rfl (fun _ h => h))
      · refine GrowsAt.call hg advance_grows fun _ st₁ n₁ hg₁ _ _ _ => ?_
        refine GrowsAt.keep_bind hg₁ rfl ?_
        exact flushN_grows up fuel n₁ _ (hg₁.congr rfl rfl rfl rfl (fun _ h => h))
      · refine GrowsAt.call hg advance_grows fun _ st₁ n₁ hg₁ _ _ _ => ?_
        refine GrowsAt.keep_bind hg₁ rfl ?_
        exact flushN_grows up fuel n₁ _ (hg₁.congr rfl rfl rfl rfl (fun _ h => h))
      · refine GrowsAt.call hg advance_grows fun _ st₁ n₁ hg₁ _ _ _ => ?_
        refine GrowsAt.keep_bind hg₁ rfl ?_
        exact flushN_grows up fuel n₁ _ (hg₁.congr rfl rfl rfl rfl (fun _ h => h))
      · exact GrowsAt.ofPure hg trivial

theorem flush_grows (up : List Stmt) : Grows ctx (flush up) (fun _ _ => True) :=
  fun n st hg => GrowsAt.read_bind (flushN_grows up _ n st hg)

theorem beginStmt_grows (up : List Stmt) : Grows ctx (beginStmt up) (fun _ _ => True) :=
  fun _ _ hg => GrowsAt.call hg (flush_grows up) fun _ _ _ hg' _ _ _ =>
    expect_grows isEmit _ _ _ hg'

theorem mapM_grows {β : Type} {f : β → P Cell} (hf : ∀ b, Grows ctx (f b) (fun n c => GoodCell n c)) :
    ∀ l : List β, Grows ctx (l.mapM f) (fun n cs => cs.length = l.length ∧ ∀ c ∈ cs, GoodCell n c)
  | [] => fun _ _ hg => by
      rw [List.mapM_nil]
      exact GrowsAt.ofPure hg ⟨rfl, fun _ h => nomatch h⟩
  | b :: l => fun _ _ hg => by
      rw [List.mapM_cons]
      refine GrowsAt.call hg (hf b) fun c _ _ hg₁ hc _ _ => ?_
      refine GrowsAt.call hg₁ (mapM_grows hf l) fun cs _ _ hg₂ hcs hn₂ _ => ?_
      refine GrowsAt.ofPure hg₂ ⟨by simp [hcs.1], fun c' hc' => ?_⟩
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hc.mono hn₂
      · exact hcs.2 c' hc'

theorem cellAt_grows' (v : V) : Grows ctx (cellAt v) (fun n c => GoodCell n c) :=
  fun n st hg => (cellAt_grows v n st hg).mono fun _ _ h => h.1

theorem destBits_grows (d : Dest) : Grows ctx (destBits d) (fun _ _ => True) := fun n st hg => by
  unfold destBits
  split
  · split
    · exact GrowsAt.call hg (cellAt_grows' _) fun _ _ _ hg' _ _ _ => GrowsAt.ofPure hg' trivial
    · exact GrowsAt.fail
  · exact GrowsAt.call hg (cellOf_grows _) fun _ _ _ hg' _ _ _ => GrowsAt.ofPure hg' trivial

theorem optionMapM_grows (o : Option V) : Grows ctx (o.mapM cellOf) (fun _ _ => True) :=
  fun n st hg => by
    cases o with
    | none => exact GrowsAt.ofPure hg trivial
    | some v =>
        rw [Option.mapM, map_eq_pure_bind]
        exact GrowsAt.call hg (cellOf_grows v) fun _ _ _ hg' _ _ _ => GrowsAt.ofPure hg' trivial

/-- One step of a walk that keeps the invariant and gives nothing. -/
macro "grows_step" : tactic => `(tactic| first
  | with_reducible exact GrowsAt.fail
  | with_reducible exact GrowsAt.fail_bind
  | with_reducible exact GrowsAt.ofPure (by assumption) trivial
  | with_reducible refine GrowsAt.get_bind ?_
  | with_reducible refine GrowsAt.read_bind ?_
  | with_reducible refine GrowsAt.peek_bind ?_
  | with_reducible refine GrowsAt.guard fun _ => ?_
  | dsimp only
  | rw [pure_bind]
  | exact pushHint_grows _ _ _ (by assumption)
  | exact (cellOf_grows _ _ _ (by assumption)).mono fun _ _ _ => trivial
  | exact (cellAt_grows' _ _ _ (by assumption)).mono fun _ _ _ => trivial
  | exact (pointer_grows _ _ _ _ (by assumption)).mono fun _ _ _ => trivial
  | with_reducible refine GrowsAt.call (by assumption) (cellOf_grows _) fun _ _ _ _ _ _ _ => ?_
  | with_reducible refine GrowsAt.call (by assumption) (cellAt_grows' _) fun _ _ _ _ _ _ _ => ?_
  | with_reducible refine GrowsAt.call (by assumption) (pointer_grows _ _) fun _ _ _ _ _ _ _ => ?_
  | with_reducible refine GrowsAt.call (by assumption) (pushHint_grows _) fun _ _ _ _ _ _ _ => ?_
  | with_reducible refine GrowsAt.call (by assumption) (destBits_grows _) fun _ _ _ _ _ _ _ => ?_
  | with_reducible refine GrowsAt.call (by assumption) (optionMapM_grows _) fun _ _ _ _ _ _ _ => ?_
  | split)

/-- A walk of such steps. -/
macro "grows_straight" : tactic => `(tactic| repeat' grows_step)

theorem placeHint_grows (h : Hint) : Grows ctx (placeHint h) (fun _ _ => True) := fun n st hg => by
  unfold placeHint
  grows_straight


/-! ## Atoms -/

/-- `omega` over cells. -/
macro "comega" : tactic => `(tactic| first | omega | (simp only [Cell] at *; omega))

theorem GoodCell.lt {n n' c : ℕ} (h : GoodCell n c) (hn : n ≤ n') : c < n' :=
  lt_of_lt_of_le h.2 hn

theorem isLazy_grows (v : V) (kind : Kind) : Grows ctx (isLazy v kind) (fun _ _ => True) :=
  fun _ _ hg => by
    unfold isLazy
    exact GrowsAt.get_bind (GrowsAt.ofPure hg trivial)

theorem cells3 {a b c n : ℕ} (ha : a < n) (hb : b < n) (hc : c < n) :
    ∀ x ∈ [a, b, c], x < n := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro x (rfl | rfl | rfl) <;> assumption

theorem cells2 {a b n : ℕ} (ha : a < n) (hb : b < n) : ∀ x ∈ [a, b], x < n := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro x (rfl | rfl) <;> assumption

theorem cells1 {a n : ℕ} (ha : a < n) : ∀ x ∈ [a], x < n := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro x rfl
  exact ha

theorem place_const_grows (d : V) (c : E) : Grows ctx (placeAtom (.const d c)) (fun _ _ => True) :=
  fun n st hg => by
    unfold placeAtom
    dsimp only
    refine GrowsAt.keep_bind hg rfl ?_
    have hg0 := hg.congr (st' := { st with constOf := st.constOf.insert d (limbsOf c) })
      rfl rfl rfl rfl (fun _ h => h)
    refine GrowsAt.call hg0 (isLazy_grows _ _) fun b st₁ n₁ hg₁ _ hn₁ _ => ?_
    split
    · exact pooled_grows hg₁ (fun o ho => hg₁.scope.consts _ o ho)
        (fun n' o _ ho => cells1 ho.2)
        (fun n' sc o _ hs ho => { hs with consts := pmap_insert_imp hs.consts ho })
    · refine GrowsAt.call hg₁ (cellAt_grows' d) fun o st₂ n₂ hg₂ ho hn₂ _ => ?_
      refine GrowsAt.bind (emitOp_grows hg₂ (cells1 ho.2)) fun _ st₃ n₃ hg₃ _ hn₃ _ => ?_
      refine GrowsAt.get_bind ?_
      split
      · refine GrowsAt.keep hg₃ rfl ?_ trivial
        exact hg₃.withScope { hg₃.scope with
          consts := pmap_insertIfNew_imp hg₃.scope.consts (ho.mono hn₃) }
      · exact GrowsAt.ofPure hg₃ trivial

theorem place_add_grows (d a b : V) : Grows ctx (placeAtom (.add d a b)) (fun _ _ => True) :=
  fun n st hg => by
    unfold placeAtom
    dsimp only
    refine GrowsAt.call hg (cellOf_grows a) fun la st₁ n₁ hg₁ ha hn₁ _ => ?_
    refine GrowsAt.call hg₁ (cellOf_grows b) fun lb st₂ n₂ hg₂ hb hn₂ _ => ?_
    refine GrowsAt.call hg₂ (isLazy_grows _ _) fun _ st₃ n₃ hg₃ _ hn₃ _ => ?_
    split
    · exact pooled_grows hg₃ (fun o ho => hg₃.scope.xors _ o ho)
        (fun n' o h ho => cells3 (ha.lt (by comega)) (hb.lt (by comega)) ho.2)
        (fun n' sc o _ hs ho => { hs with xors := pmap_insert_imp hs.xors ho })
    · refine GrowsAt.call hg₃ (cellAt_grows' d) fun o st₄ n₄ hg₄ ho hn₄ _ => ?_
      exact emitOp_grows hg₄ (cells3 (ha.lt (by comega)) (hb.lt (by comega)) ho.2)

theorem place_mul_grows (d a b : V) : Grows ctx (placeAtom (.mul d a b)) (fun _ _ => True) :=
  fun n st hg => by
    unfold placeAtom
    dsimp only
    refine GrowsAt.call hg (isLazy_grows _ _) fun _ st₀ n₀ hg₀ _ hn₀ _ => ?_
    split
    · refine GrowsAt.call hg₀ (factor_grows a) fun ra st₁ n₁ hg₁ ha hn₁ _ => ?_
      refine GrowsAt.call hg₁ (factor_grows b) fun rb st₂ n₂ hg₂ hb hn₂ _ => ?_
      refine GrowsAt.bind (pooledCell_grows hg₂ (fun o ho => hg₂.scope.muls _ o ho)
        (fun n' o h ho => cells3 (ha.lt (by comega)) (hb.lt h) ho.2)
        (fun n' sc o _ hs ho => { hs with muls := pmap_insert_imp hs.muls ho }))
        fun o st₃ n₃ hg₃ ho hn₃ _ => ?_
      refine bindTo_grows hg₃ ?_
      split <;> exact ho
    · refine GrowsAt.call hg₀ (cellOf_grows a) fun la st₁ n₁ hg₁ ha hn₁ _ => ?_
      refine GrowsAt.call hg₁ (cellOf_grows b) fun lb st₂ n₂ hg₂ hb hn₂ _ => ?_
      refine GrowsAt.call hg₂ (cellAt_grows' d) fun o st₃ n₃ hg₃ ho hn₃ _ => ?_
      exact emitOp_grows hg₃ (cells3 (ha.lt (by comega)) (hb.lt hn₃) ho.2)

theorem place_copy_grows (d s' : V) : Grows ctx (placeAtom (.copy d s')) (fun _ _ => True) :=
  fun n st hg => by
    unfold placeAtom
    dsimp only
    refine GrowsAt.call hg (cellOf_grows s') fun ls st₁ n₁ hg₁ hs hn₁ _ => ?_
    refine GrowsAt.get_bind ?_
    split
    · refine GrowsAt.call hg₁ (cellAt_grows' d) fun o st₂ n₂ hg₂ _ _ _ => ?_
      split
      · exact GrowsAt.fail_bind
      · exact GrowsAt.ofPure hg₂ trivial
    · refine GrowsAt.call hg₁ oneCell_grows fun one st₂ n₂ hg₂ h1 hn₂ _ => ?_
      refine GrowsAt.call hg₂ (cellAt_grows' d) fun o st₃ n₃ hg₃ ho hn₃ _ => ?_
      exact emitOp_grows hg₃ (cells3 (hs.lt (by comega)) (h1.lt hn₃) ho.2)

theorem place_load_grows (d p : V) (off : ℕ) :
    Grows ctx (placeAtom (.load d p off)) (fun _ _ => True) := fun n st hg => by
  unfold placeAtom
  dsimp only
  refine GrowsAt.call hg (isLazy_grows _ _) fun _ st₀ n₀ hg₀ _ hn₀ _ => ?_
  split
  · refine GrowsAt.call hg₀ (pointer_grows p off) fun r st₁ n₁ hg₁ hr hn₁ _ => ?_
    exact pooled_grows hg₁ (fun o ho => hg₁.scope.loads _ o ho)
      (fun n' o h ho => cells2 (hr.lt h) ho.2)
      (fun n' sc o _ hs ho => { hs with loads := pmap_insertIfNew_imp hs.loads ho })
  · refine GrowsAt.call hg₀ (cellOf_grows d) fun o st₁ n₁ hg₁ ho hn₁ _ => ?_
    refine GrowsAt.call hg₁ (pointer_grows p off) fun r st₂ n₂ hg₂ hr hn₂ _ => ?_
    exact emitDeref_grows hg₂ hr.2 (ho.mono hn₂)

theorem place_assertEq_grows (a b : V) :
    Grows ctx (placeAtom (.assertEq a b)) (fun _ _ => True) := fun n st hg => by
  unfold placeAtom
  dsimp only
  refine GrowsAt.call hg (cellOf_grows a) fun la st₁ n₁ hg₁ ha hn₁ _ => ?_
  refine GrowsAt.call hg₁ (cellOf_grows b) fun lb st₂ n₂ hg₂ hb hn₂ _ => ?_
  refine GrowsAt.call hg₂ oneCell_grows fun one st₃ n₃ hg₃ h1 hn₃ _ => ?_
  exact emitOp_grows hg₃ (cells3 (ha.lt (by comega)) h1.2 (hb.lt hn₃))

theorem place_assertNe_grows (x inv p : V) :
    Grows ctx (placeAtom (.assertNe x inv p)) (fun _ _ => True) := fun n st hg => by
  unfold placeAtom
  dsimp only
  refine GrowsAt.call hg (cellOf_grows x) fun lx st₁ n₁ hg₁ hx hn₁ _ => ?_
  refine GrowsAt.call hg₁ (cellOf_grows inv) fun li st₂ n₂ hg₂ hi hn₂ _ => ?_
  refine GrowsAt.call hg₂ (cellAt_grows' p) fun lp st₃ n₃ hg₃ hp hn₃ _ => ?_
  refine GrowsAt.bind (emitOp_grows hg₃ (cells3 (hx.lt (by comega)) (hi.lt hn₃) hp.2))
    fun _ st₄ n₄ hg₄ _ hn₄ _ => ?_
  exact emitOp_grows hg₄ (cells1 (hp.lt hn₄))

theorem place_rangeCheck_grows (x y t1 t2 k : V) :
    Grows ctx (placeAtom (.rangeCheck x y t1 t2 k)) (fun _ _ => True) := fun n st hg => by
  unfold placeAtom
  dsimp only
  refine GrowsAt.call hg (cellOf_grows k) fun lk st₁ n₁ hg₁ hk hn₁ _ => ?_
  refine GrowsAt.call hg₁ (cellOf_grows x) fun lx st₂ n₂ hg₂ hx hn₂ _ => ?_
  refine GrowsAt.call hg₂ (cellAt_grows' y) fun ly st₃ n₃ hg₃ hy hn₃ _ => ?_
  refine GrowsAt.call hg₃ (cellAt_grows' t1) fun c1 st₄ n₄ hg₄ h1 hn₄ _ => ?_
  refine GrowsAt.bind (emitDeref_grows hg₄ (hx.lt (by comega)) h1) fun _ st₅ n₅ hg₅ _ hn₅ _ => ?_
  refine GrowsAt.bind (emitOp_grows hg₅ (cells3 (hx.lt (by comega)) (hy.lt (by comega))
    (hk.lt (by comega)))) fun _ st₆ n₆ hg₆ _ hn₆ _ => ?_
  refine GrowsAt.call hg₆ (cellAt_grows' t2) fun c2 st₇ n₇ hg₇ h2 hn₇ _ => ?_
  exact emitDeref_grows hg₇ (hy.lt (by comega)) h2

theorem place_assertInK_grows (a b : V) :
    Grows ctx (placeAtom (.assertInK a b)) (fun _ _ => True) := fun n st hg => by
  unfold placeAtom
  dsimp only
  refine GrowsAt.call hg (cellOf_grows a) fun la st₁ n₁ hg₁ ha hn₁ _ => ?_
  refine GrowsAt.call hg₁ (cellOf_grows b) fun lb st₂ n₂ hg₂ hb hn₂ _ => ?_
  refine GrowsAt.call hg₂ zeroCell_grows fun z st₃ n₃ hg₃ hz hn₃ _ => ?_
  exact emitOp_grows hg₃ (cells3 hz.2 (ha.lt (by comega)) (hb.lt hn₃))

theorem place_touch_grows (t p : V) :
    Grows ctx (placeAtom (.touch t p)) (fun _ _ => True) := fun n st hg => by
  unfold placeAtom
  dsimp only
  refine GrowsAt.call hg (cellOf_grows p) fun lp st₁ n₁ hg₁ hp hn₁ _ => ?_
  refine GrowsAt.call hg₁ (cellAt_grows' t) fun c st₂ n₂ hg₂ hc hn₂ _ => ?_
  exact emitDeref_grows hg₂ (hp.lt hn₂) hc

theorem place_hint_grows (h : Hint) : Grows ctx (placeAtom (.hint h)) (fun _ _ => True) :=
  fun n st hg => by
    unfold placeAtom
    exact placeHint_grows h n st hg

theorem consec_lt {base n : ℕ} {l : List ℕ} (h : consecutiveFrom base l = true)
    (hl : ∀ x ∈ l, GoodCell n x) {j : ℕ} (hj : j < l.length) : base + j < n := by
  rw [← consecutiveFrom_getElem h j hj]
  exact (hl _ (List.getElem_mem hj)).2

theorem getD_lt {n : ℕ} {l : List ℕ} (hl : ∀ x ∈ l, GoodCell n x) (h2 : 2 ≤ n) (i : ℕ) :
    l.getD i 0 < n := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => simp only [Option.getD_none]; omega
  | some x => exact (hl x (List.mem_of_getElem? h)).2

theorem place_keccak_grows (ins outs : List V) (inOdd outOdd : Bool) :
    Grows ctx (placeAtom (.keccak ins outs inOdd outOdd)) (fun _ _ => True) := fun n st hg => by
  unfold placeAtom
  dsimp only
  refine GrowsAt.call hg (mapM_grows cellOf_grows ins) fun cs st₁ n₁ hg₁ hcs hn₁ _ => ?_
  refine GrowsAt.call hg₁ (mapM_grows cellAt_grows' outs) fun los st₂ n₂ hg₂ hlos hn₂ _ => ?_
  split
  · next out hout =>
    refine GrowsAt.guard fun hc => ?_
    simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨h13, h4⟩, h9⟩, hout'⟩, hlen⟩ := hc
    have hcs' : ∀ x ∈ cs, GoodCell n₂ x := fun x hx => (hcs.2 x hx).mono hn₂
    have h2 : 2 ≤ n₂ := le_trans hg₂.next.1 hg₂.next.2
    have hdrop : ∀ x ∈ (cs.drop 4).take 4, GoodCell n₂ x := fun x hx =>
      hcs' x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
    have hdrop9 : ∀ x ∈ (cs.drop 9).take 4, GoodCell n₂ x := fun x hx =>
      hcs' x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
    have hl4 : ((cs.drop 4).take 4).length = 4 := by simp [h13]
    have hl9 : ((cs.drop 9).take 4).length = 4 := by simp [h13]
    refine emitOp_grows hg₂ ?_
    intro x hx
    simp only [opCells, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map, List.mem_range] at hx
    rcases hx with ((((rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩)
    · exact getD_lt hcs' h2 0
    · exact getD_lt hcs' h2 1
    · exact getD_lt hcs' h2 2
    · exact getD_lt hcs' h2 3
    · exact getD_lt hcs' h2 8
    · exact consec_lt h4 hdrop (by rw [hl4]; exact hj)
    · exact consec_lt h9 hdrop9 (by rw [hl9]; exact hj)
    · refine consec_lt hout' hlos.2 ?_
      have hcnt : (if los.length == 1 then KeccakOutputCells.one
          else if los.length == 2 then KeccakOutputCells.two else KeccakOutputCells.all).cellCount =
          los.length := by
        rcases hlen with (h1 | h1) | h1 <;> simp [h1, KeccakOutputCells.cellCount]
      rw [hcnt] at hj
      exact hj
  · exact GrowsAt.fail

theorem isSelfFp_grows (c : Cell) : Grows ctx (isSelfFp c) (fun _ _ => True) := fun _ _ hg => by
  unfold isSelfFp
  refine GrowsAt.read_bind ?_
  split
  · exact GrowsAt.get_bind (GrowsAt.ofPure hg trivial)
  · exact GrowsAt.get_bind (GrowsAt.ofPure hg trivial)

theorem place_frameAddr_grows (p : V) (run : List V) :
    Grows ctx (placeAtom (.frameAddr p run)) (fun _ _ => True) := fun n st hg => by
  unfold placeAtom
  dsimp only
  refine GrowsAt.call hg (isLazy_grows _ _) fun _ st₀ n₀ hg₀ _ hn₀ _ => ?_
  split
  · split
    · refine GrowsAt.call hg₀ (cellAt_grows' _) fun base st₁ n₁ hg₁ hb hn₁ _ => ?_
      refine GrowsAt.call hg₁ (mapM_grows cellAt_grows' run) fun cs st₂ n₂ hg₂ _ hn₂ _ => ?_
      refine GrowsAt.guard fun _ => ?_
      refine GrowsAt.call hg₂ selfFp_grows fun o st₃ n₃ hg₃ ho hn₃ _ => ?_
      exact bindTo_grows hg₃ ho
    · exact GrowsAt.fail
  · refine GrowsAt.get_bind ?_
    split
    · refine GrowsAt.get_bind ?_
      split
      · next c e hc =>
        refine GrowsAt.call hg₀ (isSelfFp_grows _) fun _ st₁ n₁ hg₁ _ hn₁ _ => ?_
        refine GrowsAt.guard fun _ => ?_
        refine GrowsAt.call hg₁ (mapM_grows cellAt_grows' run) fun cs st₂ n₂ hg₂ _ hn₂ _ => ?_
        refine GrowsAt.guard fun _ => ?_
        refine GrowsAt.bind (materialize_grows _ hg₂ ((hg₀.locs _ _ hc).mono (by comega)))
          fun o st₃ n₃ hg₃ ho hn₃ _ => ?_
        exact bindTo_grows hg₃ ho
      · exact GrowsAt.fail
    · exact GrowsAt.fail

theorem placeAtom_grows (a : Atom) : Grows ctx (placeAtom a) (fun _ _ => True) := by
  cases a with
  | const d c => exact place_const_grows d c
  | add d x y => exact place_add_grows d x y
  | mul d x y => exact place_mul_grows d x y
  | copy d x => exact place_copy_grows d x
  | load d p off => exact place_load_grows d p off
  | assertEq x y => exact place_assertEq_grows x y
  | assertNe x i p => exact place_assertNe_grows x i p
  | rangeCheck x y t1 t2 k => exact place_rangeCheck_grows x y t1 t2 k
  | assertInK x y => exact place_assertInK_grows x y
  | keccak ins outs i o => exact place_keccak_grows ins outs i o
  | frameAddr p run => exact place_frameAddr_grows p run
  | hint h => exact place_hint_grows h
  | touch t p => exact place_touch_grows t p

/-! ## Control statements -/

theorem callPre_below {c : CallSite} (h2 : 2 ≤ n) (he : c.entry < n) (hnfp : c.nfp < n)
    (ha : ∀ a ∈ c.args, a < n) : OpsBelow n (callPre c) := by
  intro o ho x hx
  simp only [callPre, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map] at ho
  rcases ho with rfl | ((⟨⟨a, k⟩, hak, rfl⟩ | ho) | ho)
  · simp only [opCells, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; exact he
  · simp only [opCells, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hnfp
    · exact ha _ (List.fst_mem_of_mem_zipIdx hak)
  · split at ho
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      subst ho
      simp only [opCells, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact hnfp
    · simp at ho
  · split at ho <;>
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;>
      · simp only [opCells, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> first | exact hnfp | comega

theorem callRets_below {nfp nargs : ℕ} {rets : List Cell} (hnfp : nfp < n)
    (hr : ∀ r ∈ rets, r < n) : OpsBelow n (callRets nfp nargs rets) := by
  intro o ho x hx
  simp only [callRets, List.mem_map] at ho
  obtain ⟨⟨r, i⟩, hri, rfl⟩ := ho
  simp only [opCells, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact hnfp
  · exact hr _ (List.fst_mem_of_mem_zipIdx hri)

theorem loopPre_below {callee : String} {nfp entry one : Cell} {args : List Cell} (h2 : 2 ≤ n)
    (hnfp : nfp < n) (he : entry < n) (h1 : one < n) (ha : ∀ a ∈ args, a < n) :
    OpsBelow n (loopPre callee nfp entry one args) := by
  intro o ho x hx
  simp only [loopPre, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map] at ho
  rcases ho with (rfl | ⟨⟨a, k⟩, hak, rfl⟩) | (rfl | rfl | rfl) <;>
    simp only [opCells, List.mem_cons, List.not_mem_nil, or_false] at hx
  · subst hx; exact he
  · rcases hx with rfl | rfl
    · exact ha _ (List.fst_mem_of_mem_zipIdx hak)
    · exact h1
  · rcases hx with rfl | rfl <;> comega
  · rcases hx with rfl | rfl <;> comega
  · rcases hx with rfl | rfl <;> comega

theorem dispatchPre_below {pos : ℕ} {nfp joinCell x entry : Cell} {first : ℕ} {args : List Cell}
    (h2 : 2 ≤ n) (hnfp : nfp < n) (hj : joinCell < n) (hx : x < n) (he : entry < n)
    (ha : ∀ a ∈ args, a < n) : OpsBelow n (dispatchPre pos nfp joinCell x entry first args) := by
  intro o ho c hc
  simp only [dispatchPre, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map] at ho
  rcases ho with (⟨⟨a, k⟩, hak, rfl⟩ | rfl) | (rfl | rfl | rfl) <;>
    simp only [opCells, List.mem_cons, List.not_mem_nil, or_false] at hc
  · rcases hc with rfl | rfl
    · exact hnfp
    · exact ha _ (List.fst_mem_of_mem_zipIdx hak)
  · rcases hc with rfl | rfl <;> first | assumption | comega
  · subst hc; exact hj
  · rcases hc with rfl | rfl <;> assumption
  · rcases hc with rfl | rfl <;> assumption

theorem stmtBelow_ite {h : List LHint} {c bdest sfp : Cell} {zero : List PStmt} {hasElse : Bool}
    {edest one : Cell} {nonzero : List PStmt} (hc : c < n) (hb : bdest < n) (hs : sfp < n)
    (he : edest < n) (h1 : one < n) (hz : BlockBelow n zero) (hnz : BlockBelow n nonzero) :
    StmtBelow n (.ite h c bdest sfp zero hasElse edest one nonzero) := fun pos => by
  simp only [stmtOps, opsBelow_append, opsBelow_cons, opCells]
  refine ⟨⟨⟨cells1 hb, cells3 hc hb hs, opsBelow_nil⟩, blockOps_below zero hz _⟩, ?_⟩
  split
  · rw [opsBelow_append, opsBelow_cons, opsBelow_cons]
    exact ⟨⟨cells1 he, cells3 h1 he hs, opsBelow_nil⟩, blockOps_below nonzero hnz _⟩
  · exact opsBelow_nil

theorem stmtBelow_chain {h : List LHint} {join x entry one sfp : Cell} {firsts : List ℕ}
    {stages : List (List (List PStmt))} (hj : join < n) (hx : x < n) (he : entry < n)
    (h1 : one < n) (hs : sfp < n) (hst : ∀ st ∈ stages, ∀ a ∈ st, BlockBelow n a) :
    StmtBelow n (.chain h join x entry one sfp firsts stages) := fun pos => by
  simp only [stmtOps, opsBelow_append, opsBelow_cons, opCells]
  exact ⟨⟨cells1 hj, cells2 hx he, cells3 h1 he hs, opsBelow_nil⟩, stagesOps_below stages hst _⟩

theorem stmtBelow_call {h : List LHint} {c : CallSite} (h2 : 2 ≤ n) (he : c.entry < n)
    (hnfp : c.nfp < n) (hoc : c.oc < n) (ha : ∀ a ∈ c.args, a < n) (hr : ∀ r ∈ c.rets, r < n) :
    StmtBelow n (.call h c) := fun pos => by
  simp only [stmtOps, opsBelow_append, opsBelow_cons, opCells]
  exact ⟨⟨callPre_below h2 he hnfp ha, cells3 hoc he hnfp, opsBelow_nil⟩, callRets_below hnfp hr⟩

theorem stmtBelow_loopNext {h : List LHint} {callee : String} {nfp entry oc one : Cell}
    {args : List Cell} (h2 : 2 ≤ n) (hnfp : nfp < n) (he : entry < n) (hoc : oc < n)
    (h1 : one < n) (ha : ∀ a ∈ args, a < n) :
    StmtBelow n (.loopNext h callee nfp entry oc one args) := fun pos => by
  simp only [stmtOps, opsBelow_append, opsBelow_cons, opCells]
  exact ⟨loopPre_below h2 hnfp he h1 ha, cells3 hoc he hnfp, opsBelow_nil⟩

theorem stmtBelow_dispatch {h : List LHint} {callees : List String} {nfp joinCell x entry one : Cell}
    {first : ℕ} {args rets : List Cell} (h2 : 2 ≤ n) (hnfp : nfp < n) (hj : joinCell < n)
    (hx : x < n) (he : entry < n) (h1 : one < n) (ha : ∀ a ∈ args, a < n)
    (hr : ∀ r ∈ rets, r < n) :
    StmtBelow n (.dispatch h callees nfp joinCell x entry one first args rets) := fun pos => by
  simp only [stmtOps, opsBelow_append, opsBelow_cons, opCells]
  exact ⟨⟨dispatchPre_below h2 hnfp hj hx he ha, cells3 h1 he hnfp, opsBelow_nil⟩,
    callRets_below hnfp hr⟩

theorem stmtBelow_ret {h : List LHint} {one : Cell} (h2 : 2 ≤ n) (h1 : one < n) :
    StmtBelow n (.ret h one) := fun pos => by
  simp only [stmtOps, opsBelow_cons, opCells]
  exact ⟨cells3 h1 (by omega) (by omega), opsBelow_nil⟩

theorem stmtBelow_halt {h : List LHint} {one dest : Cell} (h1 : one < n) (hd : dest < n) :
    StmtBelow n (.halt h one dest) := fun pos => by
  simp only [stmtOps, opsBelow_cons, opCells]
  exact ⟨cells1 hd, cells3 h1 hd h1, opsBelow_nil⟩

/-! ## Blocks, calls, `match`es -/

theorem GrowsAt.set_bind {β : Type} {s : St} {f : PUnit → P β} {R : ℕ → β → Prop}
    (hn : st.next ≤ s.next) (hf : GrowsAt ctx (max n s.next) s (f ⟨⟩) R) :
    GrowsAt ctx n st (set s >>= f) R :=
  wp_bind.mpr (wp_set.mpr fun b st₂ he => grows_trans hn (hf b st₂ he))

theorem Good.withOutScope {n : ℕ} {st : St} (h : Good ctx n st) {out : Rev PStmt} {sc : Scope}
    (ho : ∀ s ∈ out.toList, StmtBelow n s) (hs : ScopeGood n sc) :
    Good ctx n { st with out, scope := sc } where
  next := h.next
  abi := h.abi
  locs := h.locs
  scope := hs
  out := ho
  rest := h.rest
  chainIn := h.chainIn

theorem inBlock_grows {m : P Unit} (hm : Grows ctx m (fun _ _ => True)) :
    Grows ctx (inBlock m) (fun n blk => BlockBelow n blk) := fun n st hg => by
  unfold inBlock
  refine GrowsAt.call hg (expect_grows _ _) fun _ st₁ n₁ hg₁ _ hn₁ _ => ?_
  refine GrowsAt.get_bind ?_
  dsimp only
  have hg₁' : Good ctx n₁ { st₁ with out := {} } :=
    hg₁.withOutScope (by simp) hg₁.scope
  refine GrowsAt.set_bind (le_refl _) ?_
  rw [show ({ st₁ with out := {} } : St).next = st₁.next from rfl, max_eq_of_good hg₁]
  refine GrowsAt.call hg₁' hm fun _ st₂ n₂ hg₂ _ hn₂ _ => ?_
  refine GrowsAt.call hg₂ (flush_grows _) fun _ st₃ n₃ hg₃ _ hn₃ _ => ?_
  refine GrowsAt.call hg₃ (expect_grows _ _) fun _ st₄ n₄ hg₄ _ hn₄ _ => ?_
  have tail : ∀ st₅ n₅, Good ctx n₅ st₅ → n₁ ≤ n₅ →
      GrowsAt ctx n₅ st₅ (do
        let st ← get
        set { st with out := st₁.out, scope := st₁.scope }
        return st.out.toList) (fun n blk => BlockBelow n blk) := by
    intro st₅ n₅ hg₅ hn₅
    refine GrowsAt.get_bind ?_
    refine GrowsAt.set_bind (le_refl _) ?_
    rw [show ({ st₅ with out := st₁.out, scope := st₁.scope } : St).next = st₅.next from rfl,
      max_eq_of_good hg₅]
    refine GrowsAt.ofPure (hg₅.withOutScope (fun s hs => (hg₁.out s hs).mono hn₅)
      (hg₁.scope.mono hn₅)) ?_
    exact fun s hs => hg₅.out s hs
  refine GrowsAt.get_bind ?_
  split
  · refine GrowsAt.call hg₄ fresh_grows fun o st₅ n₅ hg₅ ho hn₅ _ => ?_
    refine GrowsAt.bind (emitOp_grows hg₅ (cells1 ho.2)) fun _ st₆ n₆ hg₆ _ hn₆ _ => ?_
    exact tail st₆ n₆ hg₆ (by comega)
  · exact tail st₄ n₄ hg₄ (by comega)

theorem GrowsAt.set_keep_bind {β : Type} {s : St} {f : PUnit → P β} {R : ℕ → β → Prop}
    (hg : Good ctx n st) (hn : s.next = st.next) (hf : GrowsAt ctx n s (f ⟨⟩) R) :
    GrowsAt ctx n st (set s >>= f) R :=
  GrowsAt.set_bind (le_of_eq hn.symm) (by rw [hn, max_eq_of_good hg]; exact hf)

theorem allocTable_grows (k : ℕ) : Grows ctx (allocTable k) (fun _ _ => True) := fun n st hg => by
  unfold allocTable
  have e : max n st.next = n := max_eq_of_good hg
  have hg' : Good ctx (max n st.next) { st with tables.len := st.tables.len + k } := by
    rw [e]; exact hg.congr rfl rfl rfl rfl (fun _ h => h)
  exact GrowsAt.ofModifyGet hg' (le_refl _) trivial

theorem sharedTable_grows (fs : List String) : Grows ctx (sharedTable fs) (fun _ _ => True) :=
  fun n st hg => by
    unfold sharedTable
    refine GrowsAt.get_bind ?_
    split
    · exact GrowsAt.ofPure hg trivial
    · refine GrowsAt.set_keep_bind hg rfl ?_
      exact GrowsAt.ofPure (hg.congr rfl rfl rfl rfl (fun _ h => h)) trivial

theorem loopCount_grows (f : String) (args : List V) (cells : List Cell) :
    Grows ctx (loopCount f args cells) (fun _ _ => True) := fun n st hg => by
  unfold loopCount
  grows_straight

theorem placeCall_grows {f : String} {argVs : List V} {args rets : List Cell} {cond : Option Cell}
    {tail : Bool} (hg : Good ctx n st) (ha : ∀ a ∈ args, a < n) (hr : ∀ r ∈ rets, r < n)
    (hc : ∀ c, cond = some c → c < n) :
    GrowsAt ctx n st (placeCall f argVs args rets cond tail) (fun _ _ => True) := by
  unfold placeCall
  refine GrowsAt.call hg fresh_grows fun nfp st₁ n₁ hg₁ hnfp hn₁ _ => ?_
  refine GrowsAt.call hg₁ fresh_grows fun entry st₂ n₂ hg₂ he hn₂ _ => ?_
  have rest : ∀ oc st₃ n₃, Good ctx n₃ st₃ → oc < n₃ → n₂ ≤ n₃ →
      GrowsAt ctx n₃ st₃ (do
        let hints ← takeHints
        let loop ← loopCount f argVs args
        push (.call hints { callee := f, nfp, entry, oc, args, rets, loop, tail }))
        (fun _ _ => True) := by
    intro oc st₃ n₃ hg₃ hoc hn₃
    refine GrowsAt.call hg₃ takeHints_grows fun hints st₄ n₄ hg₄ _ hn₄ _ => ?_
    refine GrowsAt.call hg₄ (loopCount_grows _ _ _) fun loop st₅ n₅ hg₅ _ hn₅ _ => ?_
    refine push_grows hg₅ (stmtBelow_call (le_trans hg₅.next.1 hg₅.next.2) (he.lt (by comega))
      (hnfp.lt (by comega)) (lt_of_lt_of_le hoc (by comega)) (fun a h => lt_of_lt_of_le (ha a h)
        (by comega)) (fun a h => lt_of_lt_of_le (hr a h) (by comega)))
  dsimp only
  split
  · next c => rw [pure_bind]; exact rest c st₂ n₂ hg₂ (lt_of_lt_of_le (hc c rfl) (by comega)) le_rfl
  · exact GrowsAt.call hg₂ oneCell_grows fun oc st₃ n₃ hg₃ hoc hn₃ _ => rest oc st₃ n₃ hg₃ hoc.2 hn₃

/-- The cells a `match` jumps with are good cells. -/
def MatchCellsGood (n : ℕ) (r : Cell × Option (Cell × ℕ) × Cell × Cell) : Prop :=
  GoodCell n r.1 ∧ (∀ c k, r.2.1 = some (c, k) → GoodCell n c) ∧ GoodCell n r.2.2.1 ∧
    GoodCell n r.2.2.2

theorem matchCells_grows (x : V) (rest : List Stmt) (chained : Bool) :
    Grows ctx (matchCells x rest chained) (fun n r => MatchCellsGood n r) := fun n st hg => by
  unfold matchCells
  refine GrowsAt.call hg (cellOf_grows x) fun lx st₁ n₁ hg₁ hx hn₁ _ => ?_
  have rest : ∀ ns st₂ n₂, Good ctx n₂ st₂ → (∀ c k, ns = some (c, k) → GoodCell n₂ c) →
      n₁ ≤ n₂ → GrowsAt ctx n₂ st₂ (do
        let sfp ← selfFp
        let one ← oneCell
        pure (lx, ns, sfp, one)) (fun n r => MatchCellsGood n r) := by
    intro ns st₂ n₂ hg₂ hns hn₂
    refine GrowsAt.call hg₂ selfFp_grows fun sfp st₃ n₃ hg₃ hs hn₃ _ => ?_
    refine GrowsAt.call hg₃ oneCell_grows fun one st₄ n₄ hg₄ h1 hn₄ _ => ?_
    exact GrowsAt.ofPure hg₄ ⟨hx.mono (by comega), fun c k h => (hns c k h).mono (by comega),
      hs.mono hn₄, h1⟩
  dsimp only
  split
  · split
    · next x' arms' _ =>
      refine GrowsAt.call hg₁ (cellOf_grows x') fun c st' n' hg' hc' hn' _ => ?_
      rw [pure_bind]
      exact rest _ st' n' hg' (fun c₀ k h => by cases h; exact hc') hn'
    · exact GrowsAt.fail_bind
  · rw [pure_bind]
    exact rest none st₁ n₁ hg₁ (fun _ _ h => nomatch h) le_rfl

/-- `GrowsAt` whose result predicate also reads the final state. -/
def GrowsAtS {α : Type} (ctx : Ctx) (n : ℕ) (st : St) (m : P α) (R : ℕ → α → St → Prop) :
    Prop :=
  wpP m ctx st fun a st' =>
    Good ctx (max n st'.next) st' ∧ st.next ≤ st'.next ∧ R (max n st'.next) a st'

theorem GrowsAt.bindS {α β : Type} {m : P α} {f : α → P β} {R₁ : ℕ → α → Prop}
    {R₂ : ℕ → β → St → Prop} (hm : GrowsAt ctx n st m R₁)
    (hf : ∀ a st' n', Good ctx n' st' → R₁ n' a → n ≤ n' → st.next ≤ st'.next →
      GrowsAtS ctx n' st' (f a) R₂) :
    GrowsAtS ctx n st (m >>= f) R₂ := by
  refine wp_bind.mpr fun a st₁ he b st₂ he' => ?_
  obtain ⟨hg₁, hn₁, hr₁⟩ := hm a st₁ he
  obtain ⟨hg₂, hn₂, hr₂⟩ := hf a st₁ _ hg₁ hr₁ (le_max_left _ _) hn₁ b st₂ he'
  have e : max (max n st₁.next) st₂.next = max n st₂.next := by
    rw [Nat.max_assoc, Nat.max_eq_right hn₂]
  rw [e] at hg₂ hr₂
  exact ⟨hg₂, le_trans hn₁ hn₂, hr₂⟩

/-- The cells an arm leaves by are good cells. -/
def ExitGood (n : ℕ) : ArmExit → Prop
  | .join j o s => GoodCell n j ∧ GoodCell n o ∧ GoodCell n s
  | .next x _ o s => GoodCell n x ∧ GoodCell n o ∧ GoodCell n s

theorem ExitGood.mono {n n' : ℕ} {e : ArmExit} (h : ExitGood n e) (hn : n ≤ n') : ExitGood n' e := by
  cases e with
  | join j o s => exact ⟨h.1.mono hn, h.2.1.mono hn, h.2.2.mono hn⟩
  | next x f o s => exact ⟨h.1.mono hn, h.2.1.mono hn, h.2.2.mono hn⟩

/-- The cells `matchHeadOf` gives are good cells. -/
structure HeadGood (n : ℕ) (mc : MatchHead) : Prop where
  lx : GoodCell n mc.lx
  join : GoodCell n mc.join
  head : ∀ h e, mc.head = some (h, e) → GoodCell n e
  exit : ExitGood n mc.exit
  one : GoodCell n mc.one
  sfp : GoodCell n mc.sfp

theorem matchHead_grows (x : V) (k : ℕ) (rest : List Stmt) (entered : Option (ℕ × Cell))
    (chained : Bool) (hg : Good ctx n st) (he : ∀ nf j, entered = some (nf, j) → GoodCell n j) :
    GrowsAtS ctx n st (matchHeadOf x k rest entered chained)
      (fun n mc st' => HeadGood n mc ∧ mc.base = st'.next) := by
  unfold matchHeadOf
  refine GrowsAt.bindS (matchCells_grows x rest chained n st hg) fun r st₁ n₁ hg₁ hr hn₁ _ => ?_
  obtain ⟨lx, nextSel, sfp, one⟩ := r
  obtain ⟨hx, hns, hs, h1⟩ := hr
  dsimp only
  split
  · next first join =>
    rw [pure_bind]
    dsimp only
    have hgT := hg₁
    have hnT : n₁ ≤ n₁ := le_rfl
    have hjT : GoodCell n₁ join := (he first join rfl).mono hn₁
    have hhT : ∀ h e, (none : Option (List LHint × Cell)) = some (h, e) → GoodCell n₁ e :=
      fun _ _ h => nomatch h
    split
    · next x' k' =>
      refine GrowsAt.bindS (allocTable_grows _ _ _ hgT) fun nf st₄ n₄ hg₄ _ hn₄ _ => ?_
      rw [pure_bind]
      refine wp_bind.mpr (wp_get.mpr (wp_pure.mpr ?_))
      rw [max_eq_of_good hg₄]
      exact ⟨hg₄, le_refl _, ⟨hx.mono (by comega), hjT.mono hn₄,
        fun h e hh => (hhT h e hh).mono hn₄,
        ⟨(hns x' k' rfl).mono (by comega), h1.mono (by comega), hs.mono (by comega)⟩,
        h1.mono (by comega), hs.mono (by comega)⟩, rfl⟩
    · rw [pure_bind]
      refine wp_bind.mpr (wp_get.mpr (wp_pure.mpr ?_))
      rw [max_eq_of_good hgT]
      exact ⟨hgT, le_refl _, ⟨hx.mono (by comega), hjT, hhT,
        ⟨hjT, h1.mono (by comega), hs.mono (by comega)⟩,
        h1.mono (by comega), hs.mono (by comega)⟩, rfl⟩
  · refine GrowsAt.bindS (fresh_grows _ _ hg₁) fun join st₃ n₃ hg₃ hj hn₃ _ => ?_
    refine GrowsAt.bindS (takeHints_grows _ _ hg₃) fun hints st₄ n₄ hg₄ _ hn₄ _ => ?_
    refine GrowsAt.bindS (allocTable_grows _ _ _ hg₄) fun first st₅ n₅ hg₅ _ hn₅ _ => ?_
    refine GrowsAt.bindS (fresh_grows _ _ hg₅) fun entry st₆ n₆ hg₆ hen hn₆ _ => ?_
    rw [pure_bind]
    dsimp only
    have hgT := hg₆
    have hnT : n₁ ≤ n₆ := by comega
    have hjT : GoodCell n₆ join := hj.mono (by comega)
    have hhT : ∀ h e, some (hints, entry) = some (h, e) → GoodCell n₆ e :=
      fun h e hh => by cases hh; exact hen
    split
    · next x' k' =>
      refine GrowsAt.bindS (allocTable_grows _ _ _ hgT) fun nf st₄ n₄ hg₄ _ hn₄ _ => ?_
      rw [pure_bind]
      refine wp_bind.mpr (wp_get.mpr (wp_pure.mpr ?_))
      rw [max_eq_of_good hg₄]
      exact ⟨hg₄, le_refl _, ⟨hx.mono (by comega), hjT.mono hn₄,
        fun h e hh => (hhT h e hh).mono hn₄,
        ⟨(hns x' k' rfl).mono (by comega), h1.mono (by comega), hs.mono (by comega)⟩,
        h1.mono (by comega), hs.mono (by comega)⟩, rfl⟩
    · rw [pure_bind]
      refine wp_bind.mpr (wp_get.mpr (wp_pure.mpr ?_))
      rw [max_eq_of_good hgT]
      exact ⟨hgT, le_refl _, ⟨hx.mono (by comega), hjT, hhT,
        ⟨hjT, h1.mono (by comega), hs.mono (by comega)⟩,
        h1.mono (by comega), hs.mono (by comega)⟩, rfl⟩

theorem stagesOps_append : ∀ (a b : List (List (List PStmt))) (pos : ℕ),
    stagesOps (a ++ b) pos = stagesOps a pos ++ stagesOps b (pos + stagesSize a)
  | [], b, pos => by simp [stagesOps, stagesSize]
  | s :: ss, b, pos => by
      rw [List.cons_append, stagesOps, stagesOps, stagesOps_append ss b, stagesSize,
        List.append_assoc, Nat.add_assoc]

theorem Good.withChainIn {n : ℕ} {st : St} (h : Good ctx n st) {nf : ℕ} {j : Cell}
    (hj : GoodCell n j) : Good ctx n { st with chainIn := some (nf, j) } :=
  { h with chainIn := fun nf' j' hh => by cases hh; exact hj }

theorem stmtBelow_stage {h : List LHint} {j x e o s' : Cell} {firsts : List ℕ}
    {stages : List (List (List PStmt))} {first : ℕ} {blocks : List (List PStmt)}
    (hold : StmtBelow n (.chain h j x e o s' firsts stages)) (hb : ∀ b ∈ blocks, BlockBelow n b) :
    StmtBelow n (.chain h j x e o s' (firsts ++ [first]) (stages ++ [blocks])) := fun pos => by
  have h0 := hold pos
  simp only [stmtOps, opsBelow_append, opsBelow_cons, opCells] at h0 ⊢
  refine ⟨h0.1, ?_⟩
  rw [stagesOps_append, opsBelow_append]
  refine ⟨h0.2, stagesOps_below [blocks] ?_ _⟩
  intro st hst a ha
  rw [List.mem_singleton] at hst
  subst hst
  exact hb a ha

theorem matchTail_grows {mc : MatchHead} {blocks : List (List PStmt)} (hg : Good ctx n st)
    (hm : HeadGood n mc) (hb : ∀ b ∈ blocks, BlockBelow n b) :
    GrowsAt ctx n st (matchTail mc blocks) (fun _ _ => True) := by
  unfold matchTail
  refine GrowsAt.call hg (expect_grows _ _) fun _ st₁ n₁ hg₁ _ hn₁ _ => ?_
  have exitTail : ∀ st₂ n₂, Good ctx n₂ st₂ → n₁ ≤ n₂ →
      GrowsAt ctx n₂ st₂ (match mc.exit with
        | .next _ nf _ _ => modify fun s => { s with chainIn := some (nf, mc.join) }
        | .join .. => pure ()) (fun _ _ => True) := by
    intro st₂ n₂ hg₂ hn₂
    split
    · exact GrowsAt.keep hg₂ rfl (hg₂.withChainIn (hm.join.mono (by comega))) trivial
    · exact GrowsAt.ofPure hg₂ trivial
  dsimp only
  split
  · next hints entry he =>
    refine GrowsAt.bind (push_grows hg₁ (stmtBelow_chain (hm.join.lt hn₁) (hm.lx.lt hn₁)
      ((hm.head hints entry he).lt hn₁) (hm.one.lt hn₁) (hm.sfp.lt hn₁) ?_))
      fun _ st₂ n₂ hg₂ _ hn₂ _ => exitTail st₂ n₂ hg₂ hn₂
    intro st' hst a ha
    rw [List.mem_singleton] at hst
    subst hst
    exact (hb a ha).mono hn₁
  · refine GrowsAt.get_bind ?_
    split
    · next h j x e o s' firsts stages hback =>
      have hmem : PStmt.chain h j x e o s' firsts stages ∈ st₁.out.toList := by
        rw [Rev.back?_eq] at hback
        exact List.mem_of_getLast? hback
      refine GrowsAt.set_keep_bind hg₁ rfl ?_
      refine exitTail _ n₁ ?_ le_rfl
      refine hg₁.withOutScope (fun s hs => ?_) hg₁.scope
      rw [Rev.toList_push, List.mem_append, List.mem_singleton, Rev.toList_pop] at hs
      rcases hs with hs | rfl
      · exact hg₁.out s (List.mem_of_mem_dropLast hs)
      · exact stmtBelow_stage (hg₁.out _ hmem) fun b hb' => (hb b hb').mono hn₁
    · exact GrowsAt.fail_bind

/-! ## Blocks -/

theorem GrowsAtS.get_bind {α : Type} {f : St → P α} {R : ℕ → α → St → Prop}
    (h : GrowsAtS ctx n st (f st) R) : GrowsAtS ctx n st (get >>= f) R :=
  wp_bind.mpr (wp_get.mpr h)

/-- One arm, from the cell `base` on. -/
theorem armStep_grows {arm : List Stmt} {j k : ℕ} {base : Cell} {exit : ArmExit}
    (hblk : Grows ctx (placeBlock arm) (fun _ _ => True)) (hg : Good ctx n st) (hb2 : 2 ≤ base)
    (hb : base ≤ n) (he : ExitGood n exit) :
    wpP (armStep arm j k base exit) ctx st fun r st' => Good ctx (max n st'.next) st' ∧
      base ≤ st'.next ∧ r.2 = st'.next ∧ BlockBelow (max n st'.next) r.1 := by
  unfold armStep
  refine wp_bind.mpr (wp_modify.mpr ?_)
  have hg₀ : Good ctx n { st with next := base } :=
    { hg with next := ⟨hb2, hb⟩ }
  have key : GrowsAtS ctx n { st with next := base } (do
      let blk ← inBlock (placeBlock arm)
      let leave ← match exit with
        | .next x first one sfp => do
            let e ← fresh
            pure [PStmt.op [] (.slot x first e), .op [] (.jump one e sfp)]
        | .join join one sfp =>
            pure (if j + 1 != k then [PStmt.op [] (.jump one join sfp)] else [])
      let top := (← get).next
      pure (blk ++ leave, top)) (fun n r st' => r.2 = st'.next ∧ BlockBelow n r.1) := by
    refine GrowsAt.bindS (inBlock_grows hblk _ _ hg₀) fun blk st₁ n₁ hg₁ hblk₁ hn₁ _ => ?_
    have fin : ∀ (leave : List PStmt) st₂ n₂, Good ctx n₂ st₂ → n₁ ≤ n₂ → BlockBelow n₂ leave →
        GrowsAtS ctx n₂ st₂ (do
          let top := (← get).next
          pure (blk ++ leave, top)) (fun n r st' => r.2 = st'.next ∧ BlockBelow n r.1) := by
      intro leave st₂ n₂ hg₂ hn₂ hl
      refine GrowsAtS.get_bind (wp_pure.mpr ?_)
      rw [max_eq_of_good hg₂]
      refine ⟨hg₂, le_refl _, rfl, fun s hs => ?_⟩
      rcases List.mem_append.mp hs with hs | hs
      · exact (hblk₁ s hs).mono hn₂
      · exact hl s hs
    dsimp only
    split
    · next x first one sfp =>
      refine GrowsAt.bindS (fresh_grows _ _ hg₁) fun e st₂ n₂ hg₂ hc hn₂ _ => ?_
      rw [pure_bind]
      refine fin _ st₂ n₂ hg₂ hn₂ fun s hs => ?_
      have hx : x < n₂ := he.1.lt (by comega)
      have h1 : one < n₂ := he.2.1.lt (by comega)
      have hs' : sfp < n₂ := he.2.2.lt (by comega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact stmtBelow_op (cells2 hx hc.2)
      · exact stmtBelow_op (cells3 h1 hc.2 hs')
    · next join one sfp =>
      rw [pure_bind]
      refine fin _ st₁ n₁ hg₁ le_rfl fun s hs => ?_
      split at hs
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst hs
        exact stmtBelow_op (cells3 (he.2.1.lt hn₁) (he.1.lt hn₁) (he.2.2.lt hn₁))
      · simp at hs
  exact wp_mono key fun r st' ⟨hg', hn', hr, hbl⟩ => ⟨hg', hn', hr, hbl⟩

theorem good_cells_mono {cs : List Cell} {n n' : ℕ} (h : ∀ c ∈ cs, GoodCell n c) (hn : n ≤ n') :
    ∀ c ∈ cs, c < n' := fun c hc => (h c hc).lt hn

/-- A `match` statement, its arms placed by `armsAt`. -/
theorem placeMatch_grows {x : V} {k : ℕ} {rest : List Stmt} {entered : Option (ℕ × Cell)}
    {chained : Bool} {armsAt : Cell → ArmExit → P (List (List PStmt))}
    (harms : ∀ base exit n st, Good ctx n st → 2 ≤ base → base ≤ n → ExitGood n exit →
      wpP (armsAt base exit) ctx st fun blocks st' => Good ctx (max n st'.next) st' ∧
        base ≤ st'.next ∧ ∀ b ∈ blocks, BlockBelow (max n st'.next) b)
    (hg : Good ctx n st) (he : ∀ nf j, entered = some (nf, j) → GoodCell n j) :
    GrowsAt ctx n st (placeMatch x k rest entered chained armsAt) (fun _ _ => True) := by
  rw [placeMatch_eq]
  refine wp_bind.mpr (wp_mono (matchHead_grows x k rest entered chained hg he) ?_)
  rintro mc st₁ ⟨hg₁, hn₁, hh, hbase⟩
  refine wp_bind.mpr (wp_mono (harms mc.base mc.exit _ st₁ hg₁ (hbase ▸ hg₁.next.1)
    (hbase ▸ hg₁.next.2) hh.exit) ?_)
  rintro blocks st₂ ⟨hg₂, hb₂, hbl⟩
  have hn₂ : st₁.next ≤ st₂.next := hbase ▸ hb₂
  have e : max (max n st₁.next) st₂.next = max n st₂.next := by
    rw [Nat.max_assoc, Nat.max_eq_right hn₂]
  rw [e] at hg₂ hbl
  refine wp_mono (matchTail_grows hg₂ (?_) hbl) fun _ st₃ ⟨hg₃, hn₃, _⟩ => ?_
  · exact ⟨hh.lx.mono (by comega), hh.join.mono (by comega), fun h e' he' => (hh.head h e' he').mono
      (by comega), hh.exit.mono (by comega), hh.one.mono (by comega), hh.sfp.mono (by comega)⟩
  · have e' : max (max n st₂.next) st₃.next = max n st₃.next := by
      rw [Nat.max_assoc, Nat.max_eq_right hn₃]
    rw [e'] at hg₃
    exact ⟨hg₃, le_trans hn₁ (le_trans hn₂ hn₃), trivial⟩

/-- What a `placeArms` guarantees. -/
def ArmsGrow (ctx : Ctx) (arms : List (List Stmt)) : Prop :=
  ∀ (j k : ℕ) (base : Cell) (exit : ArmExit) (n : ℕ) (st : St), Good ctx n st → 2 ≤ base →
    base ≤ n → ExitGood n exit →
    wpP (placeArms arms j k base exit) ctx st fun blocks st' => Good ctx (max n st'.next) st' ∧
      base ≤ st'.next ∧ ∀ b ∈ blocks, BlockBelow (max n st'.next) b

theorem atom_stmt_grows (a : Atom) (rest : List Stmt) :
    Grows ctx (placeStmt (.atom a) rest) (fun _ _ => True) := fun n st hg => by
  rw [placeStmt]
  exact GrowsAt.call hg (beginStmt_grows _) fun _ _ _ hg' _ _ _ => placeAtom_grows a _ _ hg'

theorem ite_stmt_grows (c : V) (z nz rest : List Stmt)
    (hz : Grows ctx (placeBlock z) (fun _ _ => True))
    (hnz : Grows ctx (placeBlock nz) (fun _ _ => True)) :
    Grows ctx (placeStmt (.ite c z nz) rest) (fun _ _ => True) := fun n st hg => by
  rw [placeStmt]
  refine GrowsAt.call hg (flush_grows _) fun _ st₁ n₁ hg₁ _ hn₁ _ => ?_
  refine GrowsAt.call hg₁ (cellOf_grows c) fun lc st₂ n₂ hg₂ hc hn₂ _ => ?_
  refine GrowsAt.call hg₂ selfFp_grows fun sfp st₃ n₃ hg₃ hs hn₃ _ => ?_
  refine GrowsAt.call hg₃ oneCell_grows fun one st₄ n₄ hg₄ h1 hn₄ _ => ?_
  refine GrowsAt.call hg₄ fresh_grows fun bdest st₅ n₅ hg₅ hb hn₅ _ => ?_
  refine GrowsAt.call hg₅ takeHints_grows fun hints st₆ n₆ hg₆ _ hn₆ _ => ?_
  refine GrowsAt.call hg₆ (inBlock_grows hz) fun zb st₇ n₇ hg₇ hzb hn₇ _ => ?_
  refine GrowsAt.peek_bind ?_
  split
  · refine GrowsAt.call hg₇ fresh_grows fun edest st₈ n₈ hg₈ hed hn₈ _ => ?_
    refine GrowsAt.call hg₈ (inBlock_grows hnz) fun nzb st₉ n₉ hg₉ hnzb hn₉ _ => ?_
    refine GrowsAt.call hg₉ (expect_grows _ _) fun _ st₁₀ n₁₀ hg₁₀ _ hn₁₀ _ => ?_
    exact push_grows hg₁₀ (stmtBelow_ite (hc.lt (by comega)) (hb.lt (by comega))
      (hs.lt (by comega)) (hed.lt (by comega)) (h1.lt (by comega)) (hzb.mono (by comega))
      (hnzb.mono (by comega)))
  · refine GrowsAt.guard fun _ => ?_
    refine GrowsAt.call hg₇ (expect_grows _ _) fun _ st₈ n₈ hg₈ _ hn₈ _ => ?_
    have h0 : 0 < n₈ := lt_of_lt_of_le (lt_of_lt_of_le (by decide) hg₈.next.1) hg₈.next.2
    exact push_grows hg₈ (stmtBelow_ite (hc.lt (by comega)) (hb.lt (by comega))
      (hs.lt (by comega)) h0 h0 (hzb.mono (by comega)) (fun _ h => nomatch h))

theorem match_stmt_grows (x : V) (arms : List (List Stmt)) (rest : List Stmt)
    (harms : ArmsGrow ctx arms) :
    Grows ctx (placeStmt (.match_ x arms) rest) (fun _ _ => True) := fun n st hg => by
  rw [placeStmt]
  refine GrowsAt.call hg (flush_grows _) fun _ st₁ n₁ hg₁ _ hn₁ _ => ?_
  refine GrowsAt.get_bind ?_
  refine GrowsAt.set_keep_bind hg₁ rfl ?_
  refine placeMatch_grows (fun base exit n' st' hg' hb2 hb he => harms 0 _ base exit n' st' hg' hb2
    hb he) { hg₁ with chainIn := fun _ _ h => nomatch h } fun nf j h => hg₁.chainIn nf j h

theorem call_stmt_grows (f : String) (args rets : List V) (rest : List Stmt) :
    Grows ctx (placeStmt (.call f args rets) rest) (fun _ _ => True) := fun n st hg => by
  rw [placeStmt]
  refine GrowsAt.call hg (beginStmt_grows _) fun _ st₁ n₁ hg₁ _ hn₁ _ => ?_
  refine GrowsAt.read_bind (GrowsAt.guard fun _ => ?_)
  refine GrowsAt.call hg₁ (mapM_grows cellOf_grows args) fun las st₂ n₂ hg₂ ha hn₂ _ => ?_
  refine GrowsAt.call hg₂ (mapM_grows cellAt_grows' rets) fun lrs st₃ n₃ hg₃ hr hn₃ _ => ?_
  exact placeCall_grows hg₃ (good_cells_mono ha.2 hn₃) (good_cells_mono hr.2 le_rfl)
    fun _ h => nomatch h

theorem callIf_stmt_grows (c : V) (f : String) (args : List V) (rest : List Stmt) :
    Grows ctx (placeStmt (.callIf c f args) rest) (fun _ _ => True) := fun n st hg => by
  rw [placeStmt]
  refine GrowsAt.call hg (beginStmt_grows _) fun _ st₁ n₁ hg₁ _ hn₁ _ => ?_
  refine GrowsAt.read_bind (GrowsAt.guard fun _ => ?_)
  refine GrowsAt.call hg₁ (cellOf_grows c) fun lc st₂ n₂ hg₂ hc hn₂ _ => ?_
  refine GrowsAt.call hg₂ (mapM_grows cellOf_grows args) fun las st₃ n₃ hg₃ ha hn₃ _ => ?_
  refine GrowsAt.read_bind ?_
  dsimp only
  have finLoop : GrowsAt ctx n₃ st₃ (do
        let ownFp ← selfFp
        let scale ← fresh
        emitOp (.set scale .frameSize)
        pushHint .nextFrameAddress
        let nfp ← mulCell ownFp scale
        let entry ← fresh
        let one ← oneCell
        let hints ← takeHints
        push (.loopNext hints f nfp entry lc one las)) (fun _ _ => True) := by
    refine GrowsAt.call hg₃ selfFp_grows fun ownFp st₅ n₅ hg₅ ho hn₅ _ => ?_
    refine GrowsAt.call hg₅ fresh_grows fun scale st₆ n₆ hg₆ hsc hn₆ _ => ?_
    refine GrowsAt.bind (emitOp_grows hg₆ (cells1 hsc.2)) fun _ st₇ n₇ hg₇ _ hn₇ _ => ?_
    refine GrowsAt.call hg₇ (pushHint_grows _) fun _ st₈ n₈ hg₈ _ hn₈ _ => ?_
    refine GrowsAt.bind (mulCell_grows hg₈ (ho.lt (by comega)) (hsc.lt (by comega)))
      fun nfp st₉ n₉ hg₉ hnfp hn₉ _ => ?_
    refine GrowsAt.call hg₉ fresh_grows fun entry st₁₀ n₁₀ hg₁₀ he hn₁₀ _ => ?_
    refine GrowsAt.call hg₁₀ oneCell_grows fun one st₁₁ n₁₁ hg₁₁ h1 hn₁₁ _ => ?_
    refine GrowsAt.call hg₁₁ takeHints_grows fun hints st₁₂ n₁₂ hg₁₂ _ hn₁₂ _ => ?_
    exact push_grows hg₁₂ (stmtBelow_loopNext (le_trans hg₁₂.next.1 hg₁₂.next.2)
      (hnfp.lt (by comega)) (he.lt (by comega)) (hc.lt (by comega)) (h1.lt hn₁₂)
      (good_cells_mono ha.2 (by comega)))
  have finCall : ∀ b, GrowsAt ctx n₃ st₃ (placeCall f args las [] (some lc) b)
      (fun _ _ => True) := fun b =>
    placeCall_grows hg₃ (good_cells_mono ha.2 le_rfl) (fun _ h => nomatch h)
      fun c' h => by cases h; exact hc.lt (by comega)
  repeat' split
  all_goals first | exact GrowsAt.fail_bind | exact finLoop | exact finCall _

theorem dispatch_stmt_grows (x : V) (fs : List String) (args rets : List V) (rest : List Stmt) :
    Grows ctx (placeStmt (.dispatch x fs args rets) rest) (fun _ _ => True) := fun n st hg => by
  rw [placeStmt]
  refine GrowsAt.call hg (beginStmt_grows _) fun _ st₁ n₁ hg₁ _ hn₁ _ => ?_
  refine GrowsAt.read_bind (GrowsAt.guard fun _ => GrowsAt.guard fun _ => ?_)
  refine GrowsAt.call hg₁ (mapM_grows cellOf_grows args) fun las st₂ n₂ hg₂ ha hn₂ _ => ?_
  refine GrowsAt.call hg₂ (mapM_grows cellAt_grows' rets) fun lrs st₃ n₃ hg₃ hr hn₃ _ => ?_
  refine GrowsAt.call hg₃ (cellOf_grows x) fun lx st₄ n₄ hg₄ hx hn₄ _ => ?_
  refine GrowsAt.call hg₄ oneCell_grows fun one st₅ n₅ hg₅ h1 hn₅ _ => ?_
  refine GrowsAt.call hg₅ fresh_grows fun nfp st₆ n₆ hg₆ hnfp hn₆ _ => ?_
  refine GrowsAt.call hg₆ takeHints_grows fun hints st₇ n₇ hg₇ _ hn₇ _ => ?_
  refine GrowsAt.call hg₇ fresh_grows fun joinCell st₈ n₈ hg₈ hj hn₈ _ => ?_
  refine GrowsAt.call hg₈ (sharedTable_grows _) fun first st₉ n₉ hg₉ _ hn₉ _ => ?_
  refine GrowsAt.call hg₉ fresh_grows fun entry st₁₀ n₁₀ hg₁₀ he hn₁₀ _ => ?_
  exact push_grows hg₁₀ (stmtBelow_dispatch (le_trans hg₁₀.next.1 hg₁₀.next.2)
    (hnfp.lt (by comega)) (hj.lt (by comega)) (hx.lt (by comega)) he.2 (h1.lt (by comega))
    (good_cells_mono ha.2 (by comega)) (good_cells_mono hr.2 (by comega)))

theorem ret_stmt_grows (vs : List V) (rest : List Stmt) :
    Grows ctx (placeStmt (.ret vs) rest) (fun _ _ => True) := fun n st hg => by
  rw [placeStmt]
  refine GrowsAt.call hg (beginStmt_grows _) fun _ st₁ n₁ hg₁ _ hn₁ _ => ?_
  refine GrowsAt.read_bind ?_
  refine GrowsAt.call hg₁ (mapM_grows cellAt_grows' vs) fun lvs st₂ n₂ hg₂ _ hn₂ _ => ?_
  refine GrowsAt.guard fun _ => ?_
  refine GrowsAt.call hg₂ oneCell_grows fun one st₃ n₃ hg₃ h1 hn₃ _ => ?_
  refine GrowsAt.read_bind ?_
  split
  · refine GrowsAt.call hg₃ fresh_grows fun dest st₄ n₄ hg₄ hd hn₄ _ => ?_
    refine GrowsAt.call hg₄ takeHints_grows fun hints st₅ n₅ hg₅ _ hn₅ _ => ?_
    exact push_grows hg₅ (stmtBelow_halt (h1.lt (by comega)) (hd.lt hn₅))
  · refine GrowsAt.call hg₃ takeHints_grows fun hints st₄ n₄ hg₄ _ hn₄ _ => ?_
    exact push_grows hg₄ (stmtBelow_ret (le_trans hg₄.next.1 hg₄.next.2) (h1.lt hn₄))

mutual
/-- **A block keeps every cell below the bound.** -/
theorem placeBlock_grows : ∀ (ss : List Stmt), Grows ctx (placeBlock ss) (fun _ _ => True)
  | [] => fun _ _ hg => by
      rw [placeBlock]
      exact GrowsAt.ofPure hg trivial
  | s :: rest => fun _ _ hg => by
      rw [placeBlock]
      refine GrowsAt.call hg (placeStmt_grows s rest) fun _ _ _ hg₁ _ _ _ => ?_
      refine GrowsAt.call hg₁ endStmt_grows fun _ _ _ hg₂ _ _ _ => ?_
      exact placeBlock_grows rest _ _ hg₂

theorem placeStmt_grows : ∀ (s : Stmt) (rest : List Stmt),
    Grows ctx (placeStmt s rest) (fun _ _ => True)
  | .atom a, rest => atom_stmt_grows a rest
  | .ite c z nz, rest => ite_stmt_grows c z nz rest (placeBlock_grows z) (placeBlock_grows nz)
  | .match_ x arms, rest => match_stmt_grows x arms rest (placeArms_grows arms)
  | .call f args rets, rest => call_stmt_grows f args rets rest
  | .callIf c f args, rest => callIf_stmt_grows c f args rest
  | .dispatch x fs args rets, rest => dispatch_stmt_grows x fs args rets rest
  | .ret vs, rest => ret_stmt_grows vs rest

theorem placeArms_grows : ∀ (arms : List (List Stmt)), ArmsGrow ctx arms
  | [] => fun j k base exit n st hg hb2 hb _ => by
      rw [placeArms]
      refine wp_bind.mpr (wp_modify.mpr (wp_pure.mpr ?_))
      have e : max n base = n := Nat.max_eq_left hb
      refine ⟨?_, le_refl _, fun _ h => nomatch h⟩
      rw [show ({ st with next := base } : St).next = base from rfl, e]
      exact { hg with next := ⟨hb2, hb⟩ }
  | arm :: more => fun j k base exit n st hg hb2 hb he => by
      rw [placeArms_cons]
      refine wp_bind.mpr (wp_mono (armStep_grows (j := j) (k := k) (placeBlock_grows arm) hg hb2
        hb he) ?_)
      rintro ⟨blk, top⟩ st₁ ⟨hg₁, hb₁, htop, hblk⟩
      dsimp only at htop hblk ⊢
      refine wp_bind.mpr (wp_mono (placeArms_grows more (j + 1) k base exit _ st₁ hg₁ hb2
        (le_trans hb (le_max_left _ _)) (he.mono (le_max_left _ _))) ?_)
      rintro blocks st₂ ⟨hg₂, hb₂, hbl⟩
      refine wp_bind.mpr (wp_modify.mpr (wp_pure.mpr ?_))
      have e : max (max n st₁.next) st₂.next = max n (max st₂.next top) := by
        rw [htop]; comega
      have hnext : max st₂.next top ≤ max (max n st₁.next) st₂.next := by rw [htop]; comega
      refine ⟨?_, le_trans hb₂ (le_max_left _ _), ?_⟩
      · rw [show ({ st₂ with next := max st₂.next top } : St).next = max st₂.next top from rfl,
          ← e]
        exact { hg₂ with next := ⟨le_trans hg₂.next.1 (le_max_left _ _), hnext⟩ }
      · rw [show ({ st₂ with next := max st₂.next top } : St).next = max st₂.next top from rfl,
          ← e]
        intro b hb'
        rcases List.mem_cons.mp hb' with rfl | hb'
        · exact hblk.mono (le_max_left _ _)
        · exact hbl b hb'
end

/-! ## Functions -/

/-- Every return area the trace makes is no longer than the return cells. -/
def RetShort (tf : TracedFn) : Prop :=
  ∀ vs : List V, Event.alloc vs .ret ∈ tf.trace.toList → vs.length ≤ tf.rets

theorem good_initSt {loops : Loops} {sigs : SMap (ℕ × ℕ)} {tables : Tables} {tf : TracedFn}
    (hr : RetShort tf) :
    Good (ctxOf loops sigs tf) (initSt loops tables tf).next (initSt loops tables tf) where
  next := ⟨by simp only [initSt]; split <;> comega, le_refl _⟩
  abi := by simp only [initSt, ctxOf, sigOf]; split <;> comega
  locs v l h := by simp [initSt] at h
  scope := {
    consts := fun _ _ h => by simp [initSt] at h
    xors := fun _ _ h => by simp [initSt] at h
    muls := fun _ _ h => by simp [initSt] at h
    loads := fun _ _ h => by simp [initSt] at h
    mats := fun _ _ h => by simp [initSt] at h
    selfFp := fun o h => by
      simp only [initSt] at h ⊢
      split at h
      · next hl => cases h; simp only [hl, ↓reduceIte]; constructor <;> omega
      · cases h }
  out s h := by simp [initSt] at h
  rest vs h := hr vs h
  chainIn _ _ h := by simp [initSt] at h

theorem placeParams_grows (tf : TracedFn) {loops : Loops} {sigs : SMap (ℕ × ℕ)} {n : ℕ} {st : St}
    (hg : Good (ctxOf loops sigs tf) n st) :
    wpP (tf.core.params.zipIdx.forM fun (v, k) => bindTo v (.cell (2 + k))) (ctxOf loops sigs tf) st
      fun _ st' => Good (ctxOf loops sigs tf) n st' ∧ st'.next = st.next := by
  refine forM_inv (I := fun st' => Good (ctxOf loops sigs tf) n st' ∧ st'.next = st.next) _ ?_ st
    ⟨hg, rfl⟩
  rintro ⟨v, k⟩ hm st₁ ⟨hg₁, hn₁⟩
  have hk := (List.mem_zipIdx' hm).1
  have habi := hg₁.abi
  simp only [ctxOf, sigOf] at habi
  exact wp_mono (bindTo_same hg₁ (l := .cell (2 + k)) ⟨by simp [locBase], by simp only [locBase]; omega⟩)
    fun _ _ h => ⟨h.1, h.2.1.trans hn₁⟩

/-- **P5, placement keeps every cell in the frame**: on any trace whose return areas fit the
return cells, every value's place is past the header and below the frame size, and every cell of
its own frame an instruction of the placed body names is below the frame size. -/
theorem placeFn_cells {loops : Loops} {sigs : SMap (ℕ × ℕ)} {t t' : Tables} {tf : TracedFn}
    {pf : Placed} (h : placeFn loops sigs t tf = .ok (pf, t')) (hr : RetShort tf) :
    (∀ (v : V) (l : Loc), pf.locs[v]? = some l → GoodCell pf.fn.frameSize (locBase l)) ∧
      OpsBelow pf.fn.frameSize (blockOps pf.fn.body 0) := by
  unfold placeFn at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · next u st hst =>
        split at h
        · cases h
        · cases h
          set ctx := ctxOf loops sigs tf
          have hg0 := good_initSt (loops := loops) (sigs := sigs) (tables := t) hr
          unfold placeBody at hst
          obtain ⟨_, st₁, hp, hst⟩ := P.bind_inv hst
          obtain ⟨hg₁, hn₁⟩ := placeParams_grows tf hg0 () st₁ hp
          obtain ⟨_, st₂, hb, hst⟩ := P.bind_inv hst
          obtain ⟨hg₂, hn₂, _⟩ := placeBlock_grows tf.core.body _ st₁ hg₁ () st₂ hb
          obtain ⟨_, st₃, hf, hst⟩ := P.bind_inv hst
          obtain ⟨hg₃, hn₃, _⟩ := flush_grows [] _ st₂ hg₂ () st₃ hf
          have hq : wpP (do if !(← get).rest.isEmpty then failP "the trace goes on past the function")
              ctx st₃ (fun _ s => s = st₃) := by
            refine wp_bind.mpr (wp_get.mpr ?_)
            split
            · exact wp_failP
            · exact wp_pure.mpr rfl
          have e3 : st = st₃ := hq () st hst
          subst e3
          have hb : max (max (initSt loops t tf).next st₂.next) st.next = st.next := by
            have : (initSt loops t tf).next ≤ st₂.next := hn₁ ▸ hn₂
            comega
          rw [hb] at hg₃
          refine ⟨fun v l hl => hg₃.locs v l hl, ?_⟩
          exact blockOps_below _ (fun s hs => hg₃.out s hs) 0
    · cases h

end
end LeanVM.Guest.Backend.Complete
