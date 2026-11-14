/-
  LeanVM.Guest.Backend.Sound.Walk

  Reasoning about the placement walk: what every success of a placement action guarantees, and
  the relation between two states of the walk whose instructions in between run straight.
-/

module

public import LeanVM.Guest.Backend.Sound.Pool
public import LeanVM.Guest.Backend.Sound.Run

/-!
# The placement walk

Placement is one walk in the monad `P`. `wpP m ctx st Q` says every success of `m` from `st`
satisfies `Q`; a failed placement promises nothing, which is what lets a check in `Place` stand
for a hypothesis here.

`Emits st st' Q` relates two states of one walk: `st'` has the statements of `st` and after them
one-instruction statements only, places only grew, the jump tables and the open chain are
unchanged, and whenever the pools of `st` hold and the instructions emitted in between have
their meaning, the pools of `st'` hold, `Q` holds, and the meaning's continuation holds. The
continuation form is what lets a straight-line `JUMP` (`assert_in_k`, on the pooled zero) sit
among the instructions. It is transitive (`Emits.trans`), so a helper's guarantee is the
conjunction of its steps'.

`SpecAt ctx st m Q` is `wpP` with `Emits` as the postcondition, and its rules (`SpecAt.bind`,
`get_bind`, `modify_bind`, …) follow the shape of a `do` block.

The final places `F` are fixed throughout: every value's word is read under the final valuation
`valP Γ.L fp F`, and a state of the walk knows it through `Sub st.locs F` (P1).
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

variable {α β : Type}

/-! ## Successes of an action -/

/-- Every success of `m` from `st` satisfies `Q`. -/
def wpP (m : P α) (ctx : Ctx) (st : St) (Q : α → St → Prop) : Prop :=
  ∀ a st', m ctx st = .ok (a, st') → Q a st'

variable {ctx : Ctx} {st : St}

theorem wp_mono {m : P α} {Q Q' : α → St → Prop} (h : wpP m ctx st Q)
    (hq : ∀ a st', Q a st' → Q' a st') : wpP m ctx st Q' :=
  fun a st' he => hq a st' (h a st' he)

theorem wp_pure {a : α} {Q : α → St → Prop} : wpP (pure a) ctx st Q ↔ Q a st := by
  constructor
  · intro h
    exact h a st rfl
  · intro h a' st' he
    cases he
    exact h

theorem wp_bind {m : P α} {f : α → P β} {Q : β → St → Prop} :
    wpP (m >>= f) ctx st Q ↔ wpP m ctx st (fun a st' => wpP (f a) ctx st' Q) := by
  constructor
  · intro h a st' he b st'' he'
    refine h b st'' ?_
    show (do let (a, s) ← m ctx st; f a ctx s : Except String (β × St)) = _
    rw [he]
    exact he'
  · intro h b st'' he
    have he' : (do let (a, s) ← m ctx st; f a ctx s : Except String (β × St)) = .ok (b, st'') := he
    cases hm : m ctx st with
    | error e => rw [hm] at he'; cases he'
    | ok r =>
        obtain ⟨a, st'⟩ := r
        rw [hm] at he'
        exact h a st' hm b st'' he'

theorem wp_get {Q : St → St → Prop} : wpP (get : P St) ctx st Q ↔ Q st st := by
  constructor
  · intro h
    exact h st st rfl
  · intro h a st' he
    cases he
    exact h

theorem wp_read {Q : Ctx → St → Prop} : wpP (read : P Ctx) ctx st Q ↔ Q ctx st := by
  constructor
  · intro h
    exact h ctx st rfl
  · intro h a st' he
    cases he
    exact h

theorem wp_modify {g : St → St} {Q : Unit → St → Prop} :
    wpP (modify g : P Unit) ctx st Q ↔ Q () (g st) := by
  constructor
  · intro h
    exact h () (g st) rfl
  · intro h a st' he
    cases he
    exact h

theorem wp_modifyGet {g : St → α × St} {Q : α → St → Prop} :
    wpP (modifyGet g : P α) ctx st Q ↔ Q (g st).1 (g st).2 := by
  constructor
  · intro h
    exact h (g st).1 (g st).2 rfl
  · intro h a st' he
    have e : g st = (a, st') := Except.ok.inj he
    rw [e] at h
    exact h

theorem wp_set {s : St} {Q : Unit → St → Prop} : wpP (set s : P Unit) ctx st Q ↔ Q () s := by
  constructor
  · intro h
    exact h () s rfl
  · intro h a st' he
    cases he
    exact h

theorem wp_failP {msg : String} {Q : α → St → Prop} : wpP (failP msg : P α) ctx st Q :=
  fun _ _ he => nomatch he

theorem wp_throw {msg : String} {Q : α → St → Prop} : wpP (throw msg : P α) ctx st Q :=
  fun _ _ he => nomatch he

/-! ## Straight-line emission -/

section

variable {κ : ℕ} (Γ : Site κ) (fp : K) (F : Std.HashMap V Loc)

/-- Every statement is one instruction. -/
def OpsOnly (ops : List PStmt) : Prop := ∀ s ∈ ops, ∃ h o, s = PStmt.op h o

/-- The jump tables and the chain a `match` may be a stage of are unchanged. -/
structure Same (st st' : St) : Prop where
  tables : st'.tables = st.tables
  chainIn : st'.chainIn = st.chainIn

theorem Same.refl (st : St) : Same st st := ⟨rfl, rfl⟩

theorem Same.trans {st st' st'' : St} (h₁ : Same st st') (h₂ : Same st' st'') : Same st st'' :=
  ⟨h₂.tables.trans h₁.tables, h₂.chainIn.trans h₁.chainIn⟩

/-- **The walk went from `st` to `st'` emitting straight-line instructions that give `Q`**, the
facts `H` of the instructions before them known. -/
def Emits (H : Prop) (st st' : St) (Q : Prop) : Prop :=
  ∃ ops : List PStmt, st'.out.toList = st.out.toList ++ ops ∧ OpsOnly ops ∧
    Sub st.locs st'.locs ∧ Same st st' ∧
    ∀ (pos : ℕ) (N : Prop) (kj : E → E → Prop) (kret : Prop) (khalt : E → E → Prop),
      H → Sub st'.locs F → PoolOK Γ.L fp st.scope → PStmt.SemList Γ fp ops pos N kj kret khalt →
        PoolOK Γ.L fp st'.scope ∧ Q ∧ N

variable {Γ fp F} {H : Prop}

theorem semList_append (a b : List PStmt) (pos : ℕ) (N : Prop) (kj : E → E → Prop) (kret : Prop)
    (khalt : E → E → Prop) :
    PStmt.SemList Γ fp (a ++ b) pos N kj kret khalt =
      PStmt.SemList Γ fp a pos (PStmt.SemList Γ fp b (pos + blockSize a) N kj kret khalt) kj kret
        khalt := by
  induction a generalizing pos with
  | nil => simp [PStmt.SemList, blockSize]
  | cons s ss ih =>
      simp only [List.cons_append, PStmt.SemList, ih, blockSize, Nat.add_assoc]

theorem opsOnly_nil : OpsOnly [] := fun _ h => nomatch h

theorem Emits.refl (st : St) : Emits Γ fp F H st st True :=
  ⟨[], by simp, opsOnly_nil, Sub.refl _, Same.refl _,
    fun _ _ _ _ _ _ _ hp hs => ⟨hp, trivial, hs⟩⟩

theorem Emits.trans {st st' st'' : St} {Q₁ Q₂ : Prop} (h₁ : Emits Γ fp F H st st' Q₁)
    (h₂ : Emits Γ fp F (H ∧ Q₁) st' st'' Q₂) : Emits Γ fp F H st st'' (Q₁ ∧ Q₂) := by
  obtain ⟨ops₁, ho₁, hs₁, hl₁, ht₁, hf₁⟩ := h₁
  obtain ⟨ops₂, ho₂, hs₂, hl₂, ht₂, hf₂⟩ := h₂
  refine ⟨ops₁ ++ ops₂, by rw [ho₂, ho₁, List.append_assoc], ?_, hl₁.trans hl₂, ht₁.trans ht₂,
    fun pos N kj kret khalt hH hF hp hs => ?_⟩
  · intro s hs
    rcases List.mem_append.mp hs with h | h
    · exact hs₁ s h
    · exact hs₂ s h
  · rw [semList_append] at hs
    obtain ⟨hp', hq₁, hs'⟩ := hf₁ pos _ kj kret khalt hH (hl₂.trans hF) hp hs
    obtain ⟨hp'', hq₂, hn⟩ := hf₂ _ N kj kret khalt ⟨hH, hq₁⟩ hF hp' hs'
    exact ⟨hp'', ⟨hq₁, hq₂⟩, hn⟩

/-- Weakening, with what the state after knows. -/
theorem Emits.imp {st st' : St} {Q Q' : Prop} (h : Emits Γ fp F H st st' Q)
    (hq : H → Sub st'.locs F → PoolOK Γ.L fp st'.scope → Q → Q') : Emits Γ fp F H st st' Q' := by
  obtain ⟨ops, ho, hs, hl, ht, hf⟩ := h
  refine ⟨ops, ho, hs, hl, ht, fun pos N kj kret khalt hH hF hp hsem => ?_⟩
  obtain ⟨hp', hq', hn⟩ := hf pos N kj kret khalt hH hF hp hsem
  exact ⟨hp', hq hH hF hp' hq', hn⟩

/-- More may be assumed. -/
theorem Emits.weaken {H' : Prop} {st st' : St} {Q : Prop} (h : Emits Γ fp F H st st' Q)
    (hH : H' → H) : Emits Γ fp F H' st st' Q := by
  obtain ⟨ops, ho, hs, hl, ht, hf⟩ := h
  exact ⟨ops, ho, hs, hl, ht, fun pos N kj kret khalt h' => hf pos N kj kret khalt (hH h')⟩

/-- A state that differs in neither statements, places, tables nor open chain, and whose pools
the facts so far justify. -/
theorem Emits.frame {st st' : St} (ho : st'.out = st.out) (hl : st'.locs = st.locs)
    (ht : Same st st')
    (hsc : H → Sub st.locs F → PoolOK Γ.L fp st.scope → PoolOK Γ.L fp st'.scope) :
    Emits Γ fp F H st st' True :=
  ⟨[], by simp [ho], opsOnly_nil, by rw [hl]; exact Sub.refl _, ht,
    fun _ _ _ _ _ hH hF hp hs => ⟨hsc hH (hl ▸ hF) hp, trivial, hs⟩⟩

/-- One straight-line instruction is emitted. -/
theorem Emits.op {st st' : St} {hints : List LHint} {o : LOp} (hj : o.isJump = false)
    (ho : st'.out = st.out.push (.op hints o)) (hl : st'.locs = st.locs)
    (ht : Same st st') (hsc : st'.scope = st.scope) :
    Emits Γ fp F H st st' (∃ pc, Holds Γ.L pc fp (Γ.R o)) := by
  refine ⟨[.op hints o], by simp [ho], fun s hs => ⟨hints, o, List.mem_singleton.mp hs⟩,
    by rw [hl]; exact Sub.refl _, ht, fun pos N kj kret khalt _ _ hp hsem => ?_⟩
  have h : OpSem Γ fp o pos N kj := hsem
  cases o with
  | jump => cases hj
  | _ => exact ⟨hsc ▸ hp, ⟨_, h.1⟩, h.2⟩

/-- A `JUMP` on a zero condition is emitted: it checks its target cells and falls through. -/
theorem Emits.jumpZero {st st' : St} {hints : List LHint} {oc od of : ℕ}
    (hz : H → PoolOK Γ.L fp st.scope → wd Γ.L fp oc = 0)
    (ho : st'.out = st.out.push (.op hints (.jump oc od of))) (hl : st'.locs = st.locs)
    (ht : Same st st') (hsc : st'.scope = st.scope) :
    Emits Γ fp F H st st' (IsInK (wd Γ.L fp od) ∧ IsInK (wd Γ.L fp of)) := by
  refine ⟨[.op hints (.jump oc od of)], by simp [ho],
    fun s hs => ⟨hints, _, List.mem_singleton.mp hs⟩, by rw [hl]; exact Sub.refl _, ht,
    fun pos N kj kret khalt hH _ hp hsem => ?_⟩
  obtain ⟨c, d, f, hrc, hrd, hrf, -, hdK, hfK, hfall, -⟩ : JumpAt Γ fp oc od of N kj := hsem
  have hc0 : c = 0 := by rw [← wd_of_read hrc]; exact hz hH hp
  exact ⟨hsc ▸ hp, ⟨by rw [wd_of_read hrd]; exact hdK, by rw [wd_of_read hrf]; exact hfK⟩,
    hfall hc0⟩

/-- A value is placed. -/
theorem Emits.place {st st' : St} {v : V} {l : Loc} (hnc : st.locs.contains v = false)
    (ho : st'.out = st.out) (hl : st'.locs = st.locs.insert v l) (ht : Same st st')
    (hsc : st'.scope = st.scope) :
    Emits Γ fp F H st st' (valP Γ.L fp F v = locVal Γ.L fp l) :=
  ⟨[], by simp [ho], opsOnly_nil, by rw [hl]; exact Sub.insert l hnc, ht,
    fun _ _ _ _ _ _ hF hp hs => ⟨hsc ▸ hp, valP_of_sub hF (by rw [hl]; simp), hs⟩⟩

/-! ## Specifications -/

/-- From `st`, the facts `H` known, every success of `m` emits straight-line instructions that
give `Q` of its result. -/
def SpecAt (H : Prop) (ctx : Ctx) (st : St) (m : P α) (Q : α → Prop) : Prop :=
  wpP m ctx st (fun a st' => Emits Γ fp F H st st' (Q a))

variable (Γ fp F) in
/-- From every state, every success of `m` emits straight-line instructions that give `Q` of
its result. -/
def Spec (ctx : Ctx) (m : P α) (Q : α → Prop) : Prop :=
  ∀ st, SpecAt (Γ := Γ) (fp := fp) (F := F) True ctx st m Q

theorem SpecAt.pure {a : α} {Q : α → Prop}
    (h : H → Sub st.locs F → PoolOK Γ.L fp st.scope → Q a) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st (Pure.pure a) Q :=
  wp_pure.mpr ((Emits.refl st).imp fun hH hF hp _ => h hH hF hp)

theorem SpecAt.bind {m : P α} {f : α → P β} {Q₁ : α → Prop} {Q₂ : β → Prop}
    (hm : SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st m Q₁)
    (hf : ∀ a st', SpecAt (Γ := Γ) (fp := fp) (F := F) (H ∧ Q₁ a) ctx st' (f a) Q₂) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st (m >>= f) Q₂ :=
  wp_bind.mpr fun a st' he b st'' he' =>
    ((hm a st' he).trans (hf a st' b st'' he')).imp fun _ _ _ h => h.2

/-- A call of an action with a specification, then the rest knowing what it gives. -/
theorem SpecAt.call {m : P α} {f : α → P β} {Q₁ : α → Prop} {Q₂ : β → Prop}
    (hm : Spec Γ fp F ctx m Q₁)
    (hf : ∀ a st', SpecAt (Γ := Γ) (fp := fp) (F := F) (H ∧ Q₁ a) ctx st' (f a) Q₂) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st (m >>= f) Q₂ :=
  SpecAt.bind (fun a st' he => (hm st a st' he).weaken fun _ => trivial) hf

/-- A last call of an action with a specification. -/
theorem SpecAt.last {m : P α} {Q₁ Q₂ : α → Prop} (hm : Spec Γ fp F ctx m Q₁)
    (hq : ∀ a, H → Q₁ a → Q₂ a) : SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st m Q₂ :=
  fun a st' he => ((hm st a st' he).weaken fun _ => trivial).imp fun hH _ _ => hq a hH

theorem SpecAt.get_bind {f : St → P β} {Q : β → Prop}
    (h : SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st (f st) Q) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st (get >>= f) Q :=
  wp_bind.mpr (wp_get.mpr h)

theorem SpecAt.read_bind {f : Ctx → P β} {Q : β → Prop}
    (h : SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st (f ctx) Q) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st (read >>= f) Q :=
  wp_bind.mpr (wp_read.mpr h)

theorem SpecAt.fail {msg : String} {Q : α → Prop} :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st (failP msg) Q :=
  wp_failP

theorem SpecAt.fail_bind {msg : String} {f : α → P β} {Q : β → Prop} :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st ((failP msg : P α) >>= f) Q :=
  wp_bind.mpr wp_failP

/-- A check that fails, or the rest knowing it passed. -/
theorem SpecAt.guard {c : Prop} [Decidable c] {msg : String} {f : PUnit → P β}
    {Q : β → Prop} (h : ¬c → SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st (f PUnit.unit) Q) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st
      (if c then failP msg >>= f else f PUnit.unit) Q := by
  split
  · exact SpecAt.fail_bind
  · next hc => exact h hc

/-- A step that changes the state, then the rest from the changed state. -/
theorem SpecAt.modify_bind {g : St → St} {f : PUnit → P β} {Q₁ : Prop} {Q₂ : β → Prop}
    (hg : Emits Γ fp F H st (g st) Q₁)
    (hf : SpecAt (Γ := Γ) (fp := fp) (F := F) (H ∧ Q₁) ctx (g st) (f ⟨⟩) Q₂) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st (modify g >>= f) Q₂ :=
  wp_bind.mpr (wp_modify.mpr fun b st'' he => (hg.trans (hf b st'' he)).imp fun _ _ _ h => h.2)

/-- A step that changes the state and returns a value, then the rest. -/
theorem SpecAt.modifyGet_bind {g : St → α × St} {f : α → P β} {Q₁ : Prop} {Q₂ : β → Prop}
    (hg : Emits Γ fp F H st (g st).2 Q₁)
    (hf : SpecAt (Γ := Γ) (fp := fp) (F := F) (H ∧ Q₁) ctx (g st).2 (f (g st).1) Q₂) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st (modifyGet g >>= f) Q₂ :=
  wp_bind.mpr (wp_modifyGet.mpr fun b st'' he =>
    (hg.trans (hf b st'' he)).imp fun _ _ _ h => h.2)

theorem SpecAt.modifyGet {g : St → α × St} {Q : α → Prop}
    (hg : Emits Γ fp F H st (g st).2 (Q (g st).1)) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st (modifyGet g) Q :=
  wp_modifyGet.mpr hg

/-- A call whose guarantee the rest does not use. -/
theorem SpecAt.bindT {m : P α} {f : α → P β} {Q₁ : α → Prop} {Q₂ : β → Prop}
    (hm : SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st m Q₁)
    (hf : ∀ a st', SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st' (f a) Q₂) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st (m >>= f) Q₂ :=
  SpecAt.bind hm fun a st' b st'' he => (hf a st' b st'' he).weaken fun h => h.1

/-- A step with no guarantee, then the rest. -/
theorem SpecAt.bindTT {m : P α} {f : α → P β} {Q₂ : β → Prop}
    (hm : SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st m (fun _ => True))
    (hf : ∀ a st', SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st' (f a) Q₂) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st (m >>= f) Q₂ :=
  SpecAt.bindT hm hf

/-- A last call whose guarantee is not used. -/
theorem SpecAt.lastT {m : P α} {Q₁ : α → Prop} (hm : Spec Γ fp F ctx m Q₁) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st m (fun _ => True) :=
  SpecAt.last hm fun _ _ _ => trivial

/-- The event the walk is at. -/
theorem wp_peek {Q : Option Event → St → Prop} :
    wpP peek ctx st Q ↔ Q ctx.trace[st.pos]? st := by
  constructor
  · intro h
    exact h _ st rfl
  · intro h a st' he
    cases he
    exact h

theorem SpecAt.peek_bind {f : Option Event → P β} {Q : β → Prop}
    (h : SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st (f ctx.trace[st.pos]?) Q) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st (peek >>= f) Q :=
  wp_bind.mpr (wp_peek.mpr h)

/-- A weaker postcondition, the places of the state before known. -/
theorem SpecAt.mono' {m : P α} {Q Q' : α → Prop}
    (h : SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st m Q)
    (hq : ∀ a, H → Sub st.locs F → Q a → Q' a) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st m Q' := by
  intro a st' he
  have e := h a st' he
  have hl : Sub st.locs st'.locs := by
    obtain ⟨_, _, _, hl, _⟩ := e
    exact hl
  exact e.imp fun hH hF _ hQ => hq a hH (hl.trans hF) hQ

/-- The pools of the state before hold. -/
theorem SpecAt.withPool {m : P α} {Q : α → Prop}
    (h : SpecAt (Γ := Γ) (fp := fp) (F := F) (H ∧ PoolOK Γ.L fp st.scope) ctx st m Q) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st m Q := by
  intro a st' he
  obtain ⟨ops, ho, hs, hl, ht, hf⟩ := h a st' he
  exact ⟨ops, ho, hs, hl, ht, fun pos N kj kret khalt hH hF hp hsem =>
    hf pos N kj kret khalt ⟨hH, hp⟩ hF hp hsem⟩

/-- The places of the state before are final. -/
theorem SpecAt.withSub {m : P α} {Q : α → Prop}
    (h : SpecAt (Γ := Γ) (fp := fp) (F := F) (H ∧ Sub st.locs F) ctx st m Q) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st m Q := by
  intro a st' he
  obtain ⟨ops, ho, hs, hl, ht, hf⟩ := h a st' he
  exact ⟨ops, ho, hs, hl, ht, fun pos N kj kret khalt hH hF hp hsem =>
    hf pos N kj kret khalt ⟨hH, hl.trans hF⟩ hF hp hsem⟩

/-- A last step that only teaches the pools an entry the facts so far justify. -/
theorem SpecAt.learn {g : St → St} {Q : Prop} (ho : (g st).out = st.out)
    (hl : (g st).locs = st.locs) (ht : Same st (g st))
    (hsc : H → PoolOK Γ.L fp st.scope → PoolOK Γ.L fp (g st).scope) (hq : H → Q) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st (modify g) (fun _ => Q) :=
  wp_modify.mpr ((Emits.frame ho hl ht fun h _ hp => hsc h hp).imp fun h _ _ _ => hq h)

/-- A last step with a guarantee, the facts so far known. -/
theorem SpecAt.lastH {m : P α} {Q₁ Q₂ : α → Prop} (hm : Spec Γ fp F ctx m Q₁)
    (hq : ∀ a, H → Q₁ a → Q₂ a) : SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st m Q₂ :=
  SpecAt.last hm hq

/-- A weaker postcondition. -/
theorem SpecAt.mono {m : P α} {Q Q' : α → Prop}
    (h : SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st m Q) (hq : ∀ a, H → Q a → Q' a) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st m Q' :=
  fun a st' he => (h a st' he).imp fun hH _ _ => hq a hH

/-- More may be assumed. -/
theorem SpecAt.weaken {H' : Prop} {m : P α} {Q : α → Prop}
    (h : SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st m Q) (hH : H' → H) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H' ctx st m Q :=
  fun a st' he => (h a st' he).weaken hH

theorem SpecAt.modify {g : St → St} {Q : Prop} (hg : Emits Γ fp F H st (g st) Q) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st (modify g) (fun _ => Q) :=
  wp_modify.mpr hg

end

end
end LeanVM.Guest.Backend
