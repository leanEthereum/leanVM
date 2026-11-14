/-
  LeanVM.Guest.Backend.Sound.Lays

  The relation between two states of the placement walk across statements with control flow, and
  its rules.
-/

module

public import LeanVM.Guest.Backend.Sound.Atoms

/-!
# The walk across control flow

`Emits` (in `Walk`) relates two states with straight-line instructions between them. `Lays`
does the same for any placed statements. `Lays H st st' G S` says `st'` has the statements of
`st` and after them placed statements `ps`, places and jump tables only grew, and `ps` *means*
the core construct whose obligations are `G` and whose relation is `S` (`Means`):

    from the meaning of `ps` at a position (`PStmt.SemList`), the pools of `st`, the final places,
    the slots its `match`es filled and the shared tables' entries in the program's jump tables,
    the obligations `G g`, and `next` after it given what the code after `ps` gives (`N`), the
    pools of `st'` and the obligations after (`g`): the core relation `S next kret`.

`G` and `S` are the core IR's own transformers (`Obl s`, `Stmt.Holds C rd σ s`, or a block's), so
sequencing two `Lays` is composing them (`Lays.cons`), which is how a block is its statements.

A block of its own (`inBlock`, the branch of an `if`, an arm) leaves the statements and the pools
of the state as they were and returns its placed statements: `inBlock_spec` gives their `Means`.
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

variable {α β : Type}

/-- The shared jump tables only grew. -/
structure TablesLe (t t' : Tables) : Prop where
  shared : ∀ p ∈ t.shared, p ∈ t'.shared

theorem TablesLe.refl (t : Tables) : TablesLe t t := ⟨fun _ h => h⟩

theorem TablesLe.trans {t t' t'' : Tables} (h₁ : TablesLe t t') (h₂ : TablesLe t' t'') :
    TablesLe t t'' :=
  ⟨fun x h => h₂.shared x (h₁.shared x h)⟩

theorem TablesLe.of_eq {t t' : Tables} (h : t' = t) : TablesLe t t' := h ▸ TablesLe.refl t

/-- No chain of `match`es is open. -/
structure Plain (st : St) : Prop where
  chainIn : st.chainIn = none

theorem Plain.of_same {st st' : St} (h : Plain st) (hs : Same st st') : Plain st' :=
  ⟨hs.chainIn.trans h.chainIn⟩

section

variable {κ : ℕ} (Γ : Site κ) (fp : K) (F : Std.HashMap V Loc) (ctx : Ctx) (slots : Array KVal)
  (B : ℕ)

/-- The words a function returns: its frame's return cells. -/
noncomputable def retWords : List E := frameWords Γ.L fp (2 + ctx.argCells) ctx.retCells

/-- **Placed statements mean a core construct**, of obligations `G` and relation `S`. -/
def Means (H : Prop) (locs' : Std.HashMap V Loc) (sc sc' : Scope) (t' : Tables)
    (ps : List PStmt) (G : Prop → Prop) (S : Prop → (List E → Prop) → Prop) : Prop :=
  ∀ (pos : ℕ) (N : Prop) (kj : E → E → Prop) (kretP : Prop) (khalt : E → E → Prop)
    (g next : Prop) (kret : List E → Prop),
    H → Sub locs' F → PoolOK Γ.L fp sc → pos + blockSize ps ≤ B →
    FillsIn slots (blockFills ctx.name ps pos) → SharedIn slots t' →
    PStmt.SemList Γ fp ps pos N kj kretP khalt → G g → (PoolOK Γ.L fp sc' → N → g → next) →
    (ctx.isMain = true ∨ kretP → kret (retWords Γ fp ctx)) → S next kret

/-- **The walk went from `st` to `st'` placing statements that mean a core construct.** -/
def Lays (H : Prop) (st st' : St) (G : Prop → Prop) (S : Prop → (List E → Prop) → Prop) : Prop :=
  ∃ ps : List PStmt, st'.out.toList = st.out.toList ++ ps ∧ Sub st.locs st'.locs ∧
    TablesLe st.tables st'.tables ∧
    Means Γ fp F ctx slots B H st'.locs st.scope st'.scope st'.tables ps G S

/-- From a state with no `match` open, every success of `m` places statements that mean the
construct, and leaves no `match` open. -/
def LaysAt (H : Prop) (st : St) (m : P α) (G : Prop → Prop)
    (S : Prop → (List E → Prop) → Prop) : Prop :=
  Plain st → wpP m ctx st (fun _ st' => Plain st' ∧ Lays Γ fp F ctx slots B H st st' G S)

variable {Γ fp F ctx slots B} {H : Prop} {st st' st'' : St} {G G₁ G₂ : Prop → Prop}
  {S S₁ S₂ : Prop → (List E → Prop) → Prop}

theorem opsOnly_fills {ops : List PStmt} (h : OpsOnly ops) (f : String) (pos : ℕ) :
    blockFills f ops pos = [] := by
  induction ops generalizing pos with
  | nil => rfl
  | cons s ss ih =>
      obtain ⟨hh, o, rfl⟩ := h s List.mem_cons_self
      rw [blockFills, ih (fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))]
      simp [stmtFills]

theorem FillsIn.left {a b : List Fill} (h : FillsIn slots (a ++ b)) : FillsIn slots a :=
  fun x hx => h x (List.mem_append_left _ hx)

theorem FillsIn.right {a b : List Fill} (h : FillsIn slots (a ++ b)) : FillsIn slots b :=
  fun x hx => h x (List.mem_append_right _ hx)

theorem SharedIn.of_le {t t' : Tables} (h : SharedIn slots t') (hle : TablesLe t t') :
    SharedIn slots t :=
  fun p hp => h p (hle.shared p hp)

/-- Straight-line instructions whose facts give the construct. -/
theorem Lays.ofEmits {Q : Prop} (he : Emits Γ fp F H st st' Q)
    (hq : H → Q → ∀ g next kret, G g → (g → next) → S next kret) :
    Lays Γ fp F ctx slots B H st st' G S := by
  obtain ⟨ops, ho, _, hl, hs, hf⟩ := he
  refine ⟨ops, ho, hl, TablesLe.of_eq hs.tables, fun pos N kj kretP khalt g next kret hH hF hp _ _ _
    hsem hG hnext _ => ?_⟩
  obtain ⟨hp', hQ, hN⟩ := hf pos N kj kretP khalt hH hF hp hsem
  exact hq hH hQ g next kret hG fun hg => hnext hp' hN hg

/-- Straight-line instructions, then statements that may use their facts. -/
theorem Lays.prefix {Q : Prop} (he : Emits Γ fp F H st st' Q)
    (hl : Lays Γ fp F ctx slots B (H ∧ Q) st' st'' G S) :
    Lays Γ fp F ctx slots B H st st'' G S := by
  obtain ⟨ops, ho, hops, hl₁, hs, hf⟩ := he
  obtain ⟨ps, ho₂, hl₂, ht₂, hm⟩ := hl
  refine ⟨ops ++ ps, by rw [ho₂, ho, List.append_assoc], hl₁.trans hl₂,
    (TablesLe.of_eq hs.tables).trans ht₂, fun pos N kj kretP khalt g next kret hH hF hp hB
      hfill hent hsem hG hnext hret => ?_⟩
  rw [semList_append] at hsem
  rw [blockFills_append] at hfill
  rw [blockSize_append] at hB
  obtain ⟨hp', hQ, hsem'⟩ := hf pos _ kj kretP khalt hH (hl₂.trans hF) hp hsem
  exact hm _ N kj kretP khalt g next kret ⟨hH, hQ⟩ hF hp' (by omega) hfill.right
    hent hsem' hG hnext hret

/-- Statements, then straight-line instructions with no guarantee. -/
theorem Lays.suffix (hl : Lays Γ fp F ctx slots B H st st' G S)
    (he : Emits Γ fp F True st' st'' True) : Lays Γ fp F ctx slots B H st st'' G S := by
  obtain ⟨ps, ho₁, hl₁, ht₁, hm⟩ := hl
  obtain ⟨ops, ho, hops, hl₂, hs, hf⟩ := he
  refine ⟨ps ++ ops, by rw [ho, ho₁, List.append_assoc], hl₁.trans hl₂,
    ht₁.trans (TablesLe.of_eq hs.tables), fun pos N kj kretP khalt g next kret hH hF hp hB
      hfill hent hsem hG hnext hret => ?_⟩
  rw [semList_append] at hsem
  rw [blockFills_append] at hfill
  rw [blockSize_append] at hB
  refine hm pos _ kj kretP khalt g next kret hH (hl₂.trans hF) hp (by omega) hfill.left
    (hs.tables ▸ hent) hsem hG (fun hp' hsem' hg => ?_) hret
  obtain ⟨hp'', -, hN⟩ := hf _ N kj kretP khalt trivial hF hp' hsem'
  exact hnext hp'' hN hg

/-- **Sequencing**: the statements of one construct, then those of the next. -/
theorem Lays.cons (h₁ : Lays Γ fp F ctx slots B H st st' G₁ S₁)
    (h₂ : Lays Γ fp F ctx slots B H st' st'' G₂ S₂) :
    Lays Γ fp F ctx slots B H st st'' (fun g => G₁ (G₂ g))
      (fun next kret => S₁ (S₂ next kret) kret) := by
  obtain ⟨ps₁, ho₁, hl₁, ht₁, hm₁⟩ := h₁
  obtain ⟨ps₂, ho₂, hl₂, ht₂, hm₂⟩ := h₂
  refine ⟨ps₁ ++ ps₂, by rw [ho₂, ho₁, List.append_assoc], hl₁.trans hl₂, ht₁.trans ht₂,
    fun pos N kj kretP khalt g next kret hH hF hp hB hfill hent hsem hG hnext hret => ?_⟩
  rw [semList_append] at hsem
  rw [blockFills_append] at hfill
  rw [blockSize_append] at hB
  refine hm₁ pos _ kj kretP khalt (G₂ g) _ kret hH (hl₂.trans hF) hp (by omega) hfill.left
    (hent.of_le ht₂) hsem hG (fun hp' hsem' hg => ?_) hret
  exact hm₂ _ N kj kretP khalt g next kret hH hF hp' (by omega) hfill.right hent
    hsem' hg hnext hret

/-- Weaker obligations asked, a weaker relation given. -/
theorem Lays.imp {G' : Prop → Prop} {S' : Prop → (List E → Prop) → Prop}
    (h : Lays Γ fp F ctx slots B H st st' G S) (hG : ∀ g, G' g → G g)
    (hS : ∀ next kret, S next kret → S' next kret) :
    Lays Γ fp F ctx slots B H st st' G' S' := by
  obtain ⟨ps, ho, hl, ht, hm⟩ := h
  exact ⟨ps, ho, hl, ht, fun pos N kj kretP khalt g next kret hH hF hp hB hfill hent hsem hG'
    hnext hret => hS next kret (hm pos N kj kretP khalt g next kret hH hF hp hB hfill hent
      hsem (hG g hG') hnext hret)⟩

/-- What was assumed, with the relation. -/
theorem Lays.withH (h : Lays Γ fp F ctx slots B H st st' G S) :
    Lays Γ fp F ctx slots B H st st' G (fun next kret => H ∧ S next kret) := by
  obtain ⟨ps, ho, hl, ht, hm⟩ := h
  exact ⟨ps, ho, hl, ht, fun pos N kj kretP khalt g next kret hH hF hp hB hfill hent hsem hG
    hnext hret => ⟨hH, hm pos N kj kretP khalt g next kret hH hF hp hB hfill hent hsem hG hnext
      hret⟩⟩

theorem Lays.weaken {H' : Prop} (h : Lays Γ fp F ctx slots B H st st' G S) (hH : H' → H) :
    Lays Γ fp F ctx slots B H' st st' G S := by
  obtain ⟨ps, ho, hl, ht, hm⟩ := h
  exact ⟨ps, ho, hl, ht, fun pos N kj kretP khalt g next kret h' =>
    hm pos N kj kretP khalt g next kret (hH h')⟩

/-- A state that differs in nothing but what the walk does not read and the jump tables. -/
structure Quiet (st st' : St) : Prop where
  out : st'.out = st.out
  locs : Sub st.locs st'.locs
  scope : st'.scope = st.scope
  tables : TablesLe st.tables st'.tables
  chainIn : st'.chainIn = st.chainIn

/-- A quiet step, what it found (`H'`) justified where the final places, the pools and the
program's jump tables are known. -/
theorem Lays.ofQuiet {H' : Prop} (hq : Quiet st st')
    (hH' : SharedIn slots st'.tables → Sub st'.locs F → PoolOK Γ.L fp st.scope → H')
    (h : Lays Γ fp F ctx slots B (H ∧ H') st' st'' G S) :
    Lays Γ fp F ctx slots B H st st'' G S := by
  obtain ⟨ps, ho, hl, ht, hm⟩ := h
  refine ⟨ps, by rw [ho, hq.out], hq.locs.trans hl, hq.tables.trans ht,
    fun pos N kj kretP khalt g next kret hH hF hp hB hfill hent => ?_⟩
  have hp' : PoolOK Γ.L fp st'.scope := hq.scope ▸ hp
  exact hm pos N kj kretP khalt g next kret
    ⟨hH, hH' (hent.of_le ht) (hl.trans hF) hp⟩ hF hp' hB hfill hent

/-- What a block of its own means, the places, pools and tables around it known. -/
def BlockSem (Γ : Site κ) (fp : K) (ctx : Ctx) (slots : Array KVal) (B : ℕ) (blk : List PStmt)
    (G : Prop → Prop) (S : Prop → (List E → Prop) → Prop) : Prop :=
  ∀ (pos : ℕ) (N : Prop) (kj : E → E → Prop) (kretP : Prop) (khalt : E → E → Prop)
    (g next : Prop) (kret : List E → Prop), pos + blockSize blk ≤ B →
    FillsIn slots (blockFills ctx.name blk pos) → PStmt.SemList Γ fp blk pos N kj kretP khalt →
    G g → (N → g → next) → (ctx.isMain = true ∨ kretP → kret (retWords Γ fp ctx)) → S next kret

theorem Means.blockSem {locs' : Std.HashMap V Loc} {sc sc' : Scope} {t' : Tables}
    {blk : List PStmt} (h : Means Γ fp F ctx slots B True locs' sc sc' t' blk G S)
    (hF : Sub locs' F) (hp : PoolOK Γ.L fp sc) (hent : SharedIn slots t') :
    BlockSem Γ fp ctx slots B blk G S :=
  fun pos N kj kretP khalt g next kret hB hfill hsem hG hnext hret =>
    h pos N kj kretP khalt g next kret trivial hF hp hB hfill hent hsem hG
      (fun _ hN hg => hnext hN hg) hret

theorem Emits.same {Q : Prop} (h : Emits Γ fp F H st st' Q) : Same st st' := by
  obtain ⟨_, _, _, _, hs, _⟩ := h
  exact hs

/-! ## Rules -/

theorem LaysAt.bind {m : P α} {f : α → P β} {Q₁ : α → Prop}
    (hm : SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st m Q₁)
    (hf : ∀ a st', LaysAt Γ fp F ctx slots B (H ∧ Q₁ a) st' (f a) G S) :
    LaysAt Γ fp F ctx slots B H st (m >>= f) G S := by
  intro hpl
  refine wp_bind.mpr fun a st₁ he b st₂ he' => ?_
  have e := hm a st₁ he
  have hs : Same st st₁ := by
    obtain ⟨_, _, _, _, hs, _⟩ := e
    exact hs
  obtain ⟨hpl₂, hl⟩ := hf a st₁ (hpl.of_same hs) b st₂ he'
  exact ⟨hpl₂, Lays.prefix e hl⟩

/-- A call of an action with a specification, then the rest knowing what it gives. -/
theorem LaysAt.call {m : P α} {f : α → P β} {Q₁ : α → Prop} (hm : Spec Γ fp F ctx m Q₁)
    (hf : ∀ a st', LaysAt Γ fp F ctx slots B (H ∧ Q₁ a) st' (f a) G S) :
    LaysAt Γ fp F ctx slots B H st (m >>= f) G S :=
  LaysAt.bind (fun a st' he => (hm st a st' he).weaken fun _ => trivial) hf

/-- A step with no guarantee, then the rest. -/
theorem LaysAt.callT {m : P α} {f : α → P β} {Q₁ : α → Prop} (hm : Spec Γ fp F ctx m Q₁)
    (hf : ∀ a st', LaysAt Γ fp F ctx slots B H st' (f a) G S) :
    LaysAt Γ fp F ctx slots B H st (m >>= f) G S :=
  LaysAt.call hm fun a st' hpl b st'' he =>
    let ⟨hp, hl⟩ := hf a st' hpl b st'' he
    ⟨hp, hl.weaken fun h => h.1⟩

theorem LaysAt.get_bind {f : St → P β}
    (h : LaysAt Γ fp F ctx slots B H st (f st) G S) :
    LaysAt Γ fp F ctx slots B H st (get >>= f) G S :=
  fun hpl => wp_bind.mpr (wp_get.mpr (h hpl))

theorem LaysAt.read_bind {f : Ctx → P β}
    (h : LaysAt Γ fp F ctx slots B H st (f ctx) G S) :
    LaysAt Γ fp F ctx slots B H st (read >>= f) G S :=
  fun hpl => wp_bind.mpr (wp_read.mpr (h hpl))

theorem LaysAt.peek_bind {f : Option Event → P β}
    (h : LaysAt Γ fp F ctx slots B H st (f ctx.trace[st.pos]?) G S) :
    LaysAt Γ fp F ctx slots B H st (peek >>= f) G S :=
  fun hpl => wp_bind.mpr (wp_peek.mpr (h hpl))

theorem LaysAt.fail {msg : String} : LaysAt Γ fp F ctx slots B H st (failP msg : P α) G S :=
  fun _ => wp_failP

theorem LaysAt.fail_bind {msg : String} {f : α → P β} :
    LaysAt Γ fp F ctx slots B H st ((failP msg : P α) >>= f) G S :=
  fun _ => wp_bind.mpr wp_failP

/-- A check that fails, or the rest knowing it passed. -/
theorem LaysAt.guard {c : Prop} [Decidable c] {msg : String} {f : PUnit → P β}
    (h : ¬c → LaysAt Γ fp F ctx slots B H st (f PUnit.unit) G S) :
    LaysAt Γ fp F ctx slots B H st (if c then failP msg >>= f else f PUnit.unit) G S := by
  split
  · exact LaysAt.fail_bind
  · next hc => exact h hc

/-- A last straight-line action whose guarantee gives the construct. -/
theorem LaysAt.ofSpec {m : P α} {Q : α → Prop}
    (hm : SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st m Q)
    (hq : ∀ a, H → Q a → ∀ g next kret, G g → (g → next) → S next kret) :
    LaysAt Γ fp F ctx slots B H st m G S := by
  intro hpl a st' he
  have e := hm a st' he
  have hs : Same st st' := by
    obtain ⟨_, _, _, _, hs, _⟩ := e
    exact hs
  exact ⟨hpl.of_same hs, Lays.ofEmits e (hq a)⟩

/-- The pools of the state before hold. -/
theorem LaysAt.withPool {m : P α}
    (h : LaysAt Γ fp F ctx slots B (H ∧ PoolOK Γ.L fp st.scope) st m G S) :
    LaysAt Γ fp F ctx slots B H st m G S := by
  intro hpl a st' he
  obtain ⟨hp, ps, ho, hl, ht, hm⟩ := h hpl a st' he
  exact ⟨hp, ps, ho, hl, ht, fun pos N kj kretP khalt g next kret hH hF hpool =>
    hm pos N kj kretP khalt g next kret ⟨hH, hpool⟩ hF hpool⟩

/-- The places of the state before are final. -/
theorem LaysAt.withSub {m : P α}
    (h : LaysAt Γ fp F ctx slots B (H ∧ Sub st.locs F) st m G S) :
    LaysAt Γ fp F ctx slots B H st m G S := by
  intro hpl a st' he
  obtain ⟨hp, ps, ho, hl, ht, hm⟩ := h hpl a st' he
  exact ⟨hp, ps, ho, hl, ht, fun pos N kj kretP khalt g next kret hH hF =>
    hm pos N kj kretP khalt g next kret ⟨hH, hl.trans hF⟩ hF⟩

/-- A step that changes only what `Quiet` allows, then the rest knowing what it found. -/
theorem LaysAt.step {m : P α} {f : α → P β} {R : α → Prop}
    (hm : wpP m ctx st (fun a st₁ => Quiet st st₁ ∧
      (SharedIn slots st₁.tables → Sub st₁.locs F → PoolOK Γ.L fp st.scope → R a)))
    (hf : ∀ a st₁, LaysAt Γ fp F ctx slots B (H ∧ R a) st₁ (f a) G S) :
    LaysAt Γ fp F ctx slots B H st (m >>= f) G S := by
  intro hpl
  refine wp_bind.mpr fun a st₁ he b st₂ he' => ?_
  obtain ⟨hq, hR⟩ := hm a st₁ he
  obtain ⟨hp, hl⟩ := hf a st₁ ⟨hq.chainIn.trans hpl.chainIn⟩ b st₂ he'
  exact ⟨hp, Lays.ofQuiet hq hR hl⟩

/-- More may be assumed. -/
theorem LaysAt.weaken {H' : Prop} {m : P α} (h : LaysAt Γ fp F ctx slots B H st m G S)
    (hH : H' → H) : LaysAt Γ fp F ctx slots B H' st m G S :=
  fun hpl a st' he => let ⟨hp, hl⟩ := h hpl a st' he; ⟨hp, hl.weaken hH⟩

/-- No `match` is open at the state the walk is at. -/
theorem LaysAt.plain {m : P α}
    (h : Plain st → LaysAt Γ fp F ctx slots B H st m G S) :
    LaysAt Γ fp F ctx slots B H st m G S :=
  fun hpl => h hpl hpl

/-- A placed statement is pushed: it means the construct. -/
theorem LaysAt.push {s : PStmt}
    (hm : Means Γ fp F ctx slots B H st.locs st.scope st.scope st.tables [s] G S) :
    LaysAt Γ fp F ctx slots B H st (push s) G S := by
  intro hpl
  refine wp_modify.mpr ⟨⟨hpl.chainIn⟩, [s], by simp, Sub.refl _, TablesLe.refl _, hm⟩

end

end
end LeanVM.Guest.Backend
