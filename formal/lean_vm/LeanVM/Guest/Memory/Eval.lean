/-
  LeanVM.Guest.Memory.Eval

  An honest evaluation of the core IR as a call tree: one valuation per call instance, the path
  its branches take, its callees in call order; faithful to `Program.Rel`, and moved from one
  memory to another by the words its path reads.
-/

module

public import LeanVM.Guest.CoreLemmas

/-!
# Call trees

`Fn.Sem` hides each call's valuation under an existential. Building the memory of a run needs
them all, one per call instance, so an honest evaluation is a `Tree`: a call instance is a
function, a valuation of all its values, the sizes of the `HeapBuf`s it allocates, and its
callees in call order. A `callIf` that is not taken is a callee too, a `phantom`: the compiler
sets the callee frame up either way (a loop's last iteration writes the arguments of the next
one, a runtime loop entered zero times its first), and only the jump is conditional, so the
memory holds that frame's argument cells although nothing runs there.

**The path.** `walk σ ss` is what a block does under `σ`: the events it runs (atoms, the
branch conditions that must be in `K`, the frames it sets up) and whether it falls through or
returns, the branches decided by `σ` and a `match` taking its first arm `j` with `x = g^j`.
`Tree.Valid P rd t args rets` says that `t`'s function returns `rets` on `args` along its path,
every event holding on the reader `rd`, each taken call's callee a valid tree on its words and
each phantom's parameters the words written. `Tree.Valid.rel` shows that this is a derivation of
`Program.Rel`.

**Memory.** The atoms that read memory are a load, the two loads of a range check and
`frameAddr`; `Tree.eqns` lists the words they read along every path, as `(address, word)`
equations. `Tree.Valid.transfer` moves a valid tree to any reader satisfying its equations, and
`Tree.Valid.eqns_read` shows that a memory a tree is valid on satisfies them wherever they name
an address.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-! ## Trees -/

/-- A call instance of an honest evaluation. -/
inductive Tree where
  /-- A function run on a frame: the valuation of its values, the sizes of the `HeapBuf`s it
  allocates in order, and its callees in call order. -/
  | node (f : String) (σ : Val) (bufs : List ℕ) (kids : List Tree)
  /-- The frame of a `callIf` not taken: set up, not entered. -/
  | phantom (f : String) (σ : Val)

namespace Tree

/-- The function of a call instance. -/
def name : Tree → String
  | node f .. => f
  | phantom f _ => f

/-- The valuation of a call instance. -/
def val : Tree → Val
  | node _ σ .. => σ
  | phantom _ σ => σ

/-- The `HeapBuf` sizes of a call instance. -/
def bufs : Tree → List ℕ
  | node _ _ bufs _ => bufs
  | phantom .. => []

/-- The callees of a call instance. -/
def kids : Tree → List Tree
  | node _ _ _ kids => kids
  | phantom .. => []

end Tree

/-! ## The path of a block -/

/-- What a block runs. -/
inductive Ev where
  /-- An atom. -/
  | atom (a : Atom)
  /-- A branch or call condition, which must be in `K`. -/
  | inK (c : V)
  /-- A call, entered. -/
  | call (f : String) (args rets : List V)
  /-- A `callIf` not taken: the frame set up. -/
  | skip (f : String) (args : List V)

/-- How a block ends: falling through or returning, after its events; `stuck` when a selector
matches no arm. -/
inductive Out where
  | fall (es : List Ev)
  | ret (es : List Ev) (vs : List V)
  | stuck

/-- Events before an outcome. -/
def Out.pre (es : List Ev) : Out → Out
  | .fall es' => .fall (es ++ es')
  | .ret es' vs => .ret (es ++ es') vs
  | .stuck => .stuck

/-- An outcome, then `k` if it falls through. -/
def Out.seq : Out → Out → Out
  | .fall es, k => k.pre es
  | .ret es vs, _ => .ret es vs
  | .stuck, _ => .stuck

section

open Classical

/-- The fused dispatch: the call of the first callee `j` with `x = g^j`. -/
noncomputable def pick (σ : Val) (x : V) (args rets : List V) : ℕ → List String → Out
  | _, [] => .stuck
  | j, f :: fs => if σ x = ofK (gpow j) then .fall [.call f args rets] else pick σ x args rets (j + 1) fs

mutual
/-- What a statement does under `σ`. -/
noncomputable def walk1 (σ : Val) : Stmt → Out
  | .atom a => .fall [.atom a]
  | .ite c z n => (if σ c = 0 then walk σ z else walk σ n).pre [.inK c]
  | .match_ x arms => walkArms σ x 0 arms
  | .call f args rets => .fall [.call f args rets]
  | .callIf c f args => .fall [.inK c, if σ c = 0 then .skip f args else .call f args []]
  | .dispatch x fs args rets => pick σ x args rets 0 fs
  | .ret vs => .ret [] vs

/-- What a block does under `σ`. -/
noncomputable def walk (σ : Val) : List Stmt → Out
  | [] => .fall []
  | s :: ss => (walk1 σ s).seq (walk σ ss)

/-- The first arm `j + i` with `x = g^(j + i)`. -/
noncomputable def walkArms (σ : Val) (x : V) : ℕ → List (List Stmt) → Out
  | _, [] => .stuck
  | j, a :: as => if σ x = ofK (gpow j) then walk σ a else walkArms σ x (j + 1) as
end

end

/-- A frame a call event sets up: the callee, its argument and return values, and whether it
is entered. -/
structure Call where
  f : String
  args : List V
  rets : List V
  taken : Bool

/-- The frame an event sets up, if any. -/
def Ev.call? : Ev → Option Call
  | .call f args rets => some ⟨f, args, rets, true⟩
  | .skip f args => some ⟨f, args, [], false⟩
  | _ => none

/-- The frames events set up, in order. -/
def calls (es : List Ev) : List Call := es.filterMap Ev.call?

/-- What an event checks of the memory and `σ`. -/
def Ev.Holds (rd : Reader) (σ : Val) : Ev → Prop
  | .atom a => a.Holds rd σ
  | .inK c => IsInK (σ c)
  | _ => True

/-! ## Valid trees -/

/-- A phantom of `f`: its parameters hold the words written. -/
def Phantom (P : Core.Program) (t : Tree) (args : List E) : Prop :=
  ∃ fn, P.find? t.name = some fn ∧ fn.params.map t.val = args

mutual
/-- **An honest evaluation**: `t` runs its function on `args` and returns `rets`, along the path
its valuation takes, every event holding on `rd`. -/
def Tree.Valid (P : Core.Program) (rd : Reader) : Tree → List E → List E → Prop
  | .node f σ _ kids, args, rets => ∃ fn, P.find? f = some fn ∧ fn.params.map σ = args ∧
      ∃ es vs, walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧ (∀ e ∈ es, e.Holds rd σ) ∧
        Tree.KidsValid P rd σ (calls es) kids
  | .phantom .., _, _ => False

/-- The callees of the frames set up: a valid tree for each call entered, a phantom for each
not. -/
def Tree.KidsValid (P : Core.Program) (rd : Reader) (σ : Val) : List Call → List Tree → Prop
  | [], [] => True
  | c :: cs, k :: ks => k.name = c.f ∧
      (if c.taken then k.Valid P rd (c.args.map σ) (c.rets.map σ)
        else (∃ f σ', k = .phantom f σ') ∧ Phantom P k (c.args.map σ)) ∧
      Tree.KidsValid P rd σ cs ks
  | _, _ => False
end

/-! ## Faithfulness to `Program.Rel` -/

section Faithful

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- An event's check, and a call entered holds of `C`. -/
def Ev.Ok (C : CallRel) (rd : Reader) (σ : Val) (e : Ev) : Prop :=
  e.Holds rd σ ∧ ∀ f args rets, e = .call f args rets → C f (args.map σ) (rets.map σ)

/-- An outcome's events are `Ok`, and then `next` or the return holds. -/
def Out.Sat (C : CallRel) (rd : Reader) (σ : Val) (next : Prop) (kret : List E → Prop) :
    Out → Prop
  | .fall es => (∀ e ∈ es, e.Ok C rd σ) ∧ next
  | .ret es vs => (∀ e ∈ es, e.Ok C rd σ) ∧ kret (vs.map σ)
  | .stuck => False

theorem Out.sat_pre {es : List Ev} {next : Prop} {kret : List E → Prop} :
    ∀ {o : Out}, (o.pre es).Sat C rd σ next kret ↔ (∀ e ∈ es, e.Ok C rd σ) ∧ o.Sat C rd σ next kret
  | .fall _ => by simp only [Out.pre, Out.Sat, List.forall_mem_append, and_assoc]
  | .ret _ _ => by simp only [Out.pre, Out.Sat, List.forall_mem_append, and_assoc]
  | .stuck => by simp [Out.pre, Out.Sat]

theorem pick_sat {x : V} {args rets : List V} {next : Prop} {kret : List E → Prop} :
    ∀ (fs : List String) (j : ℕ), (pick σ x args rets j fs).Sat C rd σ next kret →
      (∃ (i : ℕ) (h : i < fs.length), σ x = ofK (gpow (j + i)) ∧
        C fs[i] (args.map σ) (rets.map σ)) ∧ next
  | [], _, h => h.elim
  | f :: fs, j, h => by
      unfold pick at h
      split_ifs at h with hx
      · obtain ⟨he, hn⟩ := h
        exact ⟨⟨0, by simp, by simpa using hx, (he _ (List.mem_singleton_self _)).2 _ _ _ rfl⟩, hn⟩
      · obtain ⟨⟨i, hi, hxi, hc⟩, hn⟩ := pick_sat fs (j + 1) h
        exact ⟨⟨i + 1, by simpa using hi, by rw [hxi, show j + 1 + i = j + (i + 1) by omega], by simpa using hc⟩, hn⟩

mutual
theorem holds_of_walk1 : ∀ (s : Stmt) {next : Prop} {kret : List E → Prop},
    (walk1 σ s).Sat C rd σ next kret → Stmt.Holds C rd σ s next kret
  | .atom a, _, _, h => by
      simp only [walk1, Out.Sat, List.mem_singleton, forall_eq] at h
      exact ⟨h.1.1, h.2⟩
  | .ite c z n, _, _, h => by
      rw [walk1, Out.sat_pre] at h
      obtain ⟨hc, h⟩ := h
      have hK : IsInK (σ c) := (hc _ (List.mem_singleton_self _)).1
      by_cases h0 : σ c = 0
      · rw [ite_eq_left h0] at h
        exact ⟨hK, fun _ => holdsList_of_walk z h, fun h' => absurd h0 h'⟩
      · rw [ite_eq_right h0] at h
        exact ⟨hK, fun h' => absurd h' h0, fun _ => holdsList_of_walk n h⟩
  | .match_ x arms, _, _, h => holdsArms_of_walk x arms 0 h
  | .call f args rets, _, _, h => by
      simp only [walk1, Out.Sat, List.mem_singleton, forall_eq] at h
      exact ⟨h.1.2 _ _ _ rfl, h.2⟩
  | .callIf c f args, _, _, h => by
      obtain ⟨he, hn⟩ := h
      refine ⟨(he (.inK c) (by simp)).1, fun h0 => ?_, hn⟩
      have hcall := he (if σ c = 0 then .skip f args else .call f args []) (by simp)
      rw [ite_eq_right h0] at hcall
      exact hcall.2 _ _ _ rfl
  | .dispatch x fs args rets, _, _, h => by
      obtain ⟨⟨i, hi, hx, hc⟩, hn⟩ := pick_sat fs 0 h
      exact ⟨⟨i, hi, by simpa using hx, hc⟩, hn⟩
  | .ret vs, _, _, h => by
      simp only [walk1, Out.Sat] at h
      exact h.2

theorem holdsList_of_walk : ∀ (ss : List Stmt) {next : Prop} {kret : List E → Prop},
    (walk σ ss).Sat C rd σ next kret → Stmt.HoldsList C rd σ ss next kret
  | [], _, _, h => h.2
  | s :: ss, next, kret, h => by
      simp only [walk] at h
      refine holds_of_walk1 s ?_
      cases hs : walk1 σ s with
      | fall es =>
          simp only [hs, Out.seq, Out.sat_pre] at h
          exact ⟨h.1, holdsList_of_walk ss h.2⟩
      | ret es vs => simp only [hs, Out.seq] at h; exact h
      | stuck => simp only [hs, Out.seq, Out.Sat] at h

theorem holdsArms_of_walk (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {next : Prop}
    {kret : List E → Prop}, (walkArms σ x j arms).Sat C rd σ next kret →
      Stmt.HoldsArms C rd σ x j arms next kret
  | [], _, _, _, h => h.elim
  | a :: as, j, _, _, h => by
      unfold walkArms at h
      split_ifs at h with hx
      · exact Or.inl ⟨hx, holdsList_of_walk a h⟩
      · exact Or.inr (holdsArms_of_walk x as (j + 1) h)
end

theorem mem_calls_of_call {es : List Ev} {f : String} {args rets : List V}
    (h : Ev.call f args rets ∈ es) : (⟨f, args, rets, true⟩ : Call) ∈ calls es :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

variable {P : Core.Program}

mutual
/-- **A valid tree is a derivation of `Program.Rel`.** -/
theorem Tree.Valid.rel : ∀ (t : Tree) {args rets : List E}, t.Valid P rd args rets →
    P.Rel rd t.name args rets
  | .node f σ _ kids, args, rets, ⟨fn, hf, hp, es, vs, hw, hr, hes, hk⟩ =>
      (rel_iff P f args rets).mpr ⟨fn, hf, σ, hp, holdsList_of_walk fn.body (by
        rw [hw]
        refine ⟨fun e he => ⟨hes e he, fun g a r hg => ?_⟩, hr⟩
        subst hg
        exact Tree.KidsValid.rel σ kids (calls es) hk _ (mem_calls_of_call he) rfl)⟩
  | .phantom .., _, _, h => h.elim

/-- `Tree.Valid.rel` for the callees: each call entered holds of `Program.Rel`. -/
theorem Tree.KidsValid.rel : ∀ (σ : Val) (ks : List Tree) (cs : List Call),
    Tree.KidsValid P rd σ cs ks → ∀ c ∈ cs, c.taken = true →
      P.Rel rd c.f (c.args.map σ) (c.rets.map σ)
  | _, [], [], _, _, hc, _ => (List.not_mem_nil hc).elim
  | σ, k :: ks, c :: cs, ⟨hn, hk, hks⟩, c', hc', ht => by
      rcases List.mem_cons.mp hc' with rfl | hc'
      · rw [ite_eq_left ht] at hk
        rw [← hn]
        exact Tree.Valid.rel k hk
      · exact Tree.KidsValid.rel σ ks cs hks c' hc' ht
  | _, [], _ :: _, h, _, _, _ => h.elim
  | _, _ :: _, [], h, _, _, _ => h.elim
end

end Faithful

/-! ## Memory equations -/

/-- The `(address, word)` equations of the memory an atom reads: a load, a range check's two
loads at offset `0`, the cells of a frame run. -/
def atomEqns (σ : Val) : Atom → List (K × E)
  | .load d p off => [((σ p).limb 0 * gpow off, σ d)]
  | .rangeCheck x y t1 t2 _ => [((σ x).limb 0 * gpow 0, σ t1), ((σ y).limb 0 * gpow 0, σ t2)]
  | .frameAddr p run => run.mapIdx fun k v => ((σ p).limb 0 * gpow k, σ v)
  | _ => []

/-- The memory equations of events. -/
def evEqns (σ : Val) (es : List Ev) : List (K × E) :=
  es.flatMap fun
    | .atom a => atomEqns σ a
    | _ => []

/-- The events of a call instance's path, if it returns. -/
noncomputable def Tree.events (P : Core.Program) (t : Tree) : List Ev :=
  match P.find? t.name with
  | some fn => match walk t.val fn.body with
    | .ret es _ => es
    | _ => []
  | none => []

mutual
/-- **The memory equations of an evaluation**: those of every path of every call instance run,
phantoms reading nothing. -/
noncomputable def Tree.eqns (P : Core.Program) : Tree → List (K × E)
  | t@(.node _ σ _ kids) => evEqns σ (t.events P) ++ Tree.eqnsKids P kids
  | .phantom .. => []

/-- `Tree.eqns` of the callees. -/
noncomputable def Tree.eqnsKids (P : Core.Program) : List Tree → List (K × E)
  | [] => []
  | k :: ks => k.eqns P ++ Tree.eqnsKids P ks
end

section Transfer

variable {P : Core.Program} {rd rd' : Reader} {σ : Val}

/-- An atom holds on any reader satisfying its equations. -/
theorem holds_transfer : ∀ (a : Atom), a.Holds rd σ →
    (∀ q ∈ atomEqns σ a, rd' q.1 = some q.2) → a.Holds rd' σ
  | .const .., h, _ => h
  | .add .., h, _ => h
  | .mul .., h, _ => h
  | .copy .., h, _ => h
  | .load .., h, he => ⟨h.1, he _ (List.mem_singleton_self _)⟩
  | .assertEq .., h, _ => h
  | .assertNe .., h, _ => h
  | .rangeCheck .., h, he =>
      ⟨⟨h.1.1, he _ List.mem_cons_self⟩, h.2.1,
        ⟨h.2.2.1, he _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩⟩
  | .assertInK .., h, _ => h
  | .blake2s .., h, _ => h
  | .frameAddr p run, h, he => by
      refine ⟨h.1, fun k hk w hw => ?_⟩
      have hm : ((σ p).limb 0 * gpow k, σ run[k]) ∈ run.mapIdx fun k v => ((σ p).limb 0 * gpow k, σ v) :=
        List.mem_mapIdx.mpr ⟨k, hk, rfl⟩
      exact Option.some.inj (hw.symm.trans (he _ hm))
  | .hint _, h, _ => h

/-- An atom's equations hold on a memory it holds on, wherever they name an address. -/
theorem atomEqns_read {κ : ℕ} (hκ : κ < 64) {L : MemImage κ} :
    ∀ (a : Atom), a.Holds L.read σ → ∀ q ∈ atomEqns σ a, (∃ i : Fin (2 ^ κ), q.1 = gpow i) →
      L.read q.1 = some q.2
  | .load .., h, q, hq, _ => by
      rw [List.mem_singleton.mp hq]
      exact h.2
  | .rangeCheck .., h, q, hq, _ => by
      simp only [atomEqns, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact h.1.2
      · exact h.2.2.2
  | .frameAddr p run, h, q, hq, ⟨i, hi⟩ => by
      obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hq
      dsimp only at hi ⊢
      have := h.2 k hk (L i) (by rw [hi]; exact MemImage.read_gpow hκ L i)
      rw [hi, MemImage.read_gpow hκ L i, this]
  | .const .., _, _, hq, _ => (List.not_mem_nil hq).elim
  | .add .., _, _, hq, _ => (List.not_mem_nil hq).elim
  | .mul .., _, _, hq, _ => (List.not_mem_nil hq).elim
  | .copy .., _, _, hq, _ => (List.not_mem_nil hq).elim
  | .assertEq .., _, _, hq, _ => (List.not_mem_nil hq).elim
  | .assertNe .., _, _, hq, _ => (List.not_mem_nil hq).elim
  | .assertInK .., _, _, hq, _ => (List.not_mem_nil hq).elim
  | .blake2s .., _, _, hq, _ => (List.not_mem_nil hq).elim
  | .hint _, _, _, hq, _ => (List.not_mem_nil hq).elim

theorem mem_evEqns {es : List Ev} {a : Atom} (ha : Ev.atom a ∈ es) {q : K × E}
    (hq : q ∈ atomEqns σ a) : q ∈ evEqns σ es :=
  List.mem_flatMap.mpr ⟨_, ha, hq⟩

theorem eqns_node {f : String} {bufs : List ℕ} {kids : List Tree} {fn : Fn} {es : List Ev}
    {vs : List V} (hf : P.find? f = some fn) (hw : walk σ fn.body = .ret es vs) :
    (Tree.node f σ bufs kids).eqns P = evEqns σ es ++ Tree.eqnsKids P kids := by
  have : (Tree.node f σ bufs kids).events P = es := by
    simp only [Tree.events, Tree.name, Tree.val, hf, hw]
  rw [Tree.eqns, this]

/-- The events of a path hold on any reader satisfying their equations. -/
theorem events_transfer {es : List Ev} (h : ∀ e ∈ es, e.Holds rd σ)
    (he : ∀ q ∈ evEqns σ es, rd' q.1 = some q.2) : ∀ e ∈ es, e.Holds rd' σ
  | .atom a, hm => holds_transfer a (h _ hm) fun q hq => he q (mem_evEqns hm hq)
  | .inK _, hm => h _ hm
  | .call .., _ => trivial
  | .skip .., _ => trivial

/-- The equations of a path hold on a memory its events hold on, wherever they name an
address. -/
theorem evEqns_read {κ : ℕ} (hκ : κ < 64) {L : MemImage κ} {es : List Ev}
    (h : ∀ e ∈ es, e.Holds L.read σ) :
    ∀ q ∈ evEqns σ es, (∃ i : Fin (2 ^ κ), q.1 = gpow i) → L.read q.1 = some q.2 := by
  intro q hq hi
  obtain ⟨e, he, hq⟩ := List.mem_flatMap.mp hq
  cases e with
  | atom a => exact atomEqns_read hκ a (h _ he) q hq hi
  | inK _ => exact (List.not_mem_nil hq).elim
  | call _ _ _ => exact (List.not_mem_nil hq).elim
  | skip _ _ => exact (List.not_mem_nil hq).elim

mutual
/-- **Transfer**: a valid tree is valid on any reader satisfying its memory equations. -/
theorem Tree.Valid.transfer : ∀ (t : Tree) {args rets : List E}, t.Valid P rd args rets →
    (∀ q ∈ t.eqns P, rd' q.1 = some q.2) → t.Valid P rd' args rets
  | .node _ σ _ kids, _, _, ⟨fn, hf, hp, es, vs, hw, hr, hes, hk⟩, he => by
      rw [eqns_node hf hw] at he
      exact ⟨fn, hf, hp, es, vs, hw, hr,
        events_transfer hes fun q hq => he q (List.mem_append_left _ hq),
        Tree.KidsValid.transfer σ kids (calls es) hk fun q hq => he q (List.mem_append_right _ hq)⟩
  | .phantom .., _, _, h, _ => h.elim

/-- `Tree.Valid.transfer` for the callees. -/
theorem Tree.KidsValid.transfer : ∀ (σ : Val) (ks : List Tree) (cs : List Call),
    Tree.KidsValid P rd σ cs ks → (∀ q ∈ Tree.eqnsKids P ks, rd' q.1 = some q.2) →
      Tree.KidsValid P rd' σ cs ks
  | _, [], [], _, _ => trivial
  | σ, k :: ks, c :: cs, ⟨hn, hc, hks⟩, he => by
      rw [Tree.eqnsKids] at he
      refine ⟨hn, ?_, Tree.KidsValid.transfer σ ks cs hks fun q hq => he q (List.mem_append_right _ hq)⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc ⊢
        exact Tree.Valid.transfer k hc fun q hq => he q (List.mem_append_left _ hq)
      · rw [ite_eq_right ht] at hc ⊢
        exact hc
  | _, [], _ :: _, h, _ => h.elim
  | _, _ :: _, [], h, _ => h.elim
end

mutual
/-- **The equations of a valid tree hold** on the memory it is valid on, wherever they name an
address. -/
theorem Tree.Valid.eqns_read {κ : ℕ} (hκ : κ < 64) {L : MemImage κ} :
    ∀ (t : Tree) {args rets : List E}, t.Valid P L.read args rets → ∀ q ∈ t.eqns P,
      (∃ i : Fin (2 ^ κ), q.1 = gpow i) → L.read q.1 = some q.2
  | .node _ σ _ kids, _, _, ⟨fn, hf, _, es, vs, hw, _, hes, hk⟩, q, hq, hi => by
      rw [eqns_node hf hw] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact evEqns_read hκ hes q hq hi
      · exact Tree.KidsValid.eqns_read hκ σ kids (calls es) hk q hq hi
  | .phantom .., _, _, h, _, _, _ => h.elim

/-- `Tree.Valid.eqns_read` for the callees. -/
theorem Tree.KidsValid.eqns_read {κ : ℕ} (hκ : κ < 64) {L : MemImage κ} :
    ∀ (σ : Val) (ks : List Tree) (cs : List Call), Tree.KidsValid P L.read σ cs ks →
      ∀ q ∈ Tree.eqnsKids P ks, (∃ i : Fin (2 ^ κ), q.1 = gpow i) → L.read q.1 = some q.2
  | _, [], [], _, _, hq, _ => (List.not_mem_nil hq).elim
  | σ, k :: ks, c :: cs, ⟨_, hc, hks⟩, q, hq, hi => by
      rw [Tree.eqnsKids] at hq
      rcases List.mem_append.mp hq with hq | hq
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hc
          exact Tree.Valid.eqns_read hκ k hc q hq hi
        · rw [ite_eq_right ht] at hc
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
          simp [Tree.eqns] at hq
      · exact Tree.KidsValid.eqns_read hκ σ ks cs hks q hq hi
  | _, [], _ :: _, h, _, _, _ => h.elim
  | _, _ :: _, [], h, _, _, _ => h.elim
end

end Transfer

end
end LeanVM.Guest.Memory
