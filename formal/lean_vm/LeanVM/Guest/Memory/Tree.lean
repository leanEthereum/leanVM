/-
  LeanVM.Guest.Memory.Tree

  The converse of `Tree.Valid.rel`: a derivation of `Program.Rel` is an honest evaluation, a call
  tree whose `HeapBuf` sizes are those of the `alloc` hints on each path and whose untaken
  `callIf`s are phantoms holding the words written; for a program whose `callIf` callees take
  any arguments and whose `match`es have at most `2^64 - 1` arms, the order of `g`.
-/

module

public import LeanVM.Guest.Memory.Eval

/-!
# From `Program.Rel` to a call tree

`Tree.Valid` walks a block as `walk` does, a `match` taking its first arm `j` with `x = g^j`,
where `Stmt.HoldsArms` and a fused dispatch hold of some arm. They agree when the arm is unique:
`g^i ≠ g^j` for `i < j < 2^64 - 1`, the order of `g` (`gpow_injOn`), so a block whose `match`es
and dispatches have at most `2^64 - 1` arms holds exactly when its walk is satisfied
(`walk_sat`, the converse of `holdsList_of_walk`).

A phantom must hold the words its caller wrote in its callee's parameters (`Phantom`), and the
derivation says nothing of an untaken call: its callee need not exist, nor take as many
arguments. So the converse needs that of the program (`Program.Wf`): every `callIf` names a
function of `P` with as many parameters as the call has arguments, all distinct (`Takes`); the
phantom's valuation is then the words written at the parameters, `0` elsewhere (`phantomVal`).
Both conditions are syntactic and decidable; the guest's core IR satisfies them
(`coreProgram_wf`, `Memory/GuestWf.lean`).

`Tree.Valid` leaves the `HeapBuf` sizes free; the tree built here records the path's
(`Tree.BufsOk`): a `HeapBuf(n)` hint's `n` and the exponent of a dynamic one's size word, in
allocation order (`allocs`).

**Results.** `Program.Rel.tree`: for a well-formed program, a derivation of `P.Rel rd f args
rets` is a valid tree `t` of `f` with `t.BufsOk P`; `rel_iff_tree`: with `Tree.Valid.rel`, the
two are equivalent.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-! ## Well-formed programs -/

/-- `f` takes any `n` argument words: a function of `P` with `n` parameters, all distinct. -/
def _root_.LeanVM.Guest.Core.Program.Takes (P : Core.Program) (f : String) (n : ℕ) : Bool :=
  match P.find? f with
  | some fn => fn.params.length == n && decide fn.params.Nodup
  | none => false

mutual
/-- A statement well formed in `P`: every `callIf` in it names a function that `Takes` its
arguments, and every `match` and fused dispatch has at most `2^64 - 1` arms. -/
def Stmt.wf (P : Core.Program) : Stmt → Bool
  | .ite _ z n => Stmt.wfList P z && Stmt.wfList P n
  | .match_ _ arms => decide (arms.length ≤ 2 ^ 64 - 1) && Stmt.wfArms P arms
  | .callIf _ f args => P.Takes f args.length
  | .dispatch _ fs _ _ => decide (fs.length ≤ 2 ^ 64 - 1)
  | _ => true

/-- A block well formed in `P`. -/
def Stmt.wfList (P : Core.Program) : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.wf P s && Stmt.wfList P ss

/-- Arms well formed in `P`. -/
def Stmt.wfArms (P : Core.Program) : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.wfList P a && Stmt.wfArms P as
end

/-- **A well-formed program**: every function's body is well formed in it. -/
def _root_.LeanVM.Guest.Core.Program.Wf (P : Core.Program) : Prop :=
  ∀ fn ∈ P, Stmt.wfList P fn.body = true

/-! ## Arms -/

theorem ofK_gpow_ne {i j : ℕ} (hij : i < j) (hj : j < 2 ^ 64 - 1) :
    ofK (gpow i) ≠ ofK (gpow j) := fun h =>
  absurd (gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
    (ofK_injective h)) (by omega)

/-! ## The walk of a block that holds -/

section Converse

variable {C : CallRel} {rd : Reader} {σ : Val} {P : Core.Program}

theorem pick_sat_of {x : V} {args rets : List V} {next : Prop} {kret : List E → Prop} :
    ∀ (fs : List String) (j : ℕ), j + fs.length ≤ 2 ^ 64 - 1 →
      (∃ (i : ℕ) (h : i < fs.length), σ x = ofK (gpow (j + i)) ∧
        C fs[i] (args.map σ) (rets.map σ)) → next → (pick σ x args rets j fs).Sat C rd σ next kret
  | [], _, _, ⟨i, hi, _⟩, _ => absurd hi (by simp)
  | f :: fs, j, hb, ⟨i, hi, hx, hc⟩, hn => by
      simp only [List.length_cons] at hb hi
      unfold pick
      split_ifs with hxj
      · obtain rfl : i = 0 := by
          by_contra h0
          exact ofK_gpow_ne (show j < j + i by omega) (by omega) (hxj.symm.trans hx)
        refine ⟨fun e he => ?_, hn⟩
        rw [List.mem_singleton] at he
        subst he
        exact ⟨trivial, fun g a r he => by cases he; simpa using hc⟩
      · cases i with
        | zero => exact absurd (by simpa using hx) hxj
        | succ i =>
            exact pick_sat_of fs (j + 1) (by omega)
              ⟨i, by omega, by rw [hx]; congr 2; omega, by simpa using hc⟩ hn

mutual
/-- **The converse of `holds_of_walk1`**: a well-formed statement that holds has a satisfied
walk. -/
theorem walk1_sat : ∀ (s : Stmt), Stmt.wf P s = true → ∀ {next : Prop} {kret : List E → Prop},
    Stmt.Holds C rd σ s next kret → (walk1 σ s).Sat C rd σ next kret
  | .atom a, _, _, _, h => by
      simp only [walk1, Out.Sat, List.mem_singleton, forall_eq]
      exact ⟨⟨h.1, fun _ _ _ h => nomatch h⟩, h.2⟩
  | .ite c z n, hw, _, _, h => by
      simp only [Stmt.wf, Bool.and_eq_true] at hw
      rw [walk1, Out.sat_pre]
      refine ⟨fun e he => ?_, ?_⟩
      · rw [List.mem_singleton] at he
        subst he
        exact ⟨h.1, fun _ _ _ h => nomatch h⟩
      · by_cases h0 : σ c = 0
        · rw [ite_eq_left h0]
          exact walk_sat z hw.1 (h.2.1 h0)
        · rw [ite_eq_right h0]
          exact walk_sat n hw.2 (h.2.2 h0)
  | .match_ x arms, hw, _, _, h => by
      simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
      exact walkArms_sat x arms 0 (by omega) hw.2 h
  | .call f args rets, _, _, _, h => by
      simp only [walk1, Out.Sat, List.mem_singleton, forall_eq]
      exact ⟨⟨trivial, fun g a r he => by cases he; exact h.1⟩, h.2⟩
  | .callIf c f args, _, _, _, h => by
      rw [walk1]
      refine ⟨fun e he => ?_, h.2.2⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact ⟨h.1, fun _ _ _ h => nomatch h⟩
      · by_cases h0 : σ c = 0
        · rw [ite_eq_left h0]
          exact ⟨trivial, fun _ _ _ h => nomatch h⟩
        · rw [ite_eq_right h0]
          exact ⟨trivial, fun g a r he => by cases he; exact h.2.1 h0⟩
  | .dispatch x fs args rets, hw, _, _, h => by
      simp only [Stmt.wf, decide_eq_true_eq] at hw
      obtain ⟨⟨i, hi, hx, hc⟩, hn⟩ := h
      exact pick_sat_of fs 0 (by omega) ⟨i, hi, by simpa using hx, hc⟩ hn
  | .ret vs, _, _, _, h => by
      rw [walk1]
      exact ⟨fun _ he => (List.not_mem_nil he).elim, h⟩

/-- **The converse of `holdsList_of_walk`**: a well-formed block that holds has a satisfied
walk. -/
theorem walk_sat : ∀ (ss : List Stmt), Stmt.wfList P ss = true →
    ∀ {next : Prop} {kret : List E → Prop},
    Stmt.HoldsList C rd σ ss next kret → (walk σ ss).Sat C rd σ next kret
  | [], _, _, _, h => by
      rw [walk]
      exact ⟨fun _ he => (List.not_mem_nil he).elim, h⟩
  | s :: ss, hw, _, _, h => by
      simp only [Stmt.wfList, Bool.and_eq_true] at hw
      have hs := walk1_sat s hw.1 h
      rw [walk]
      cases hs' : walk1 σ s with
      | fall es =>
          rw [hs'] at hs
          rw [Out.seq, Out.sat_pre]
          exact ⟨hs.1, walk_sat ss hw.2 hs.2⟩
      | ret es vs =>
          rw [hs'] at hs
          exact hs
      | stuck =>
          rw [hs'] at hs
          exact hs.elim

/-- **The converse of `holdsArms_of_walk`**: the arm that holds is the first at its power of
`g`. -/
theorem walkArms_sat (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ),
    j + arms.length ≤ 2 ^ 64 - 1 → Stmt.wfArms P arms = true →
    ∀ {next : Prop} {kret : List E → Prop},
    Stmt.HoldsArms C rd σ x j arms next kret → (walkArms σ x j arms).Sat C rd σ next kret
  | [], _, _, _, _, _, h => by simp [Stmt.HoldsArms] at h
  | a :: as, j, hb, hw, _, _, h => by
      simp only [Stmt.wfArms, Bool.and_eq_true] at hw
      simp only [List.length_cons] at hb
      unfold walkArms
      split_ifs with hx
      · rcases h with ⟨-, ha⟩ | h
        · exact walk_sat a hw.1 ha
        · obtain ⟨i, hi, hxi, -⟩ := (holdsArms_iff x as (j + 1) _ _).mp h
          exact absurd (hx.symm.trans hxi) (ofK_gpow_ne (by omega) (by omega))
      · rcases h with ⟨hx', -⟩ | h
        · exact absurd hx' hx
        · exact walkArms_sat x as (j + 1) (by omega) hw.2 h
end

/-! ## The frames a walk sets up -/

/-- What a well-formed program gives of an event: a frame set up and not entered is one its
callee `Takes`. -/
def Ev.Wf (P : Core.Program) : Ev → Prop
  | .skip f args => P.Takes f args.length = true
  | _ => True

/-- Every event of an outcome satisfies `p`. -/
def Out.All (p : Ev → Prop) : Out → Prop
  | .fall es => ∀ e ∈ es, p e
  | .ret es _ => ∀ e ∈ es, p e
  | .stuck => True

theorem Out.all_pre {p : Ev → Prop} {es : List Ev} (h : ∀ e ∈ es, p e) :
    ∀ {o : Out}, o.All p → (o.pre es).All p
  | .fall _, ho => List.forall_mem_append.mpr ⟨h, ho⟩
  | .ret _ _, ho => List.forall_mem_append.mpr ⟨h, ho⟩
  | .stuck, _ => trivial

theorem Out.all_seq {p : Ev → Prop} {k : Out} (hk : k.All p) :
    ∀ {o : Out}, o.All p → (o.seq k).All p
  | .fall _, ho => Out.all_pre ho hk
  | .ret _ _, ho => ho
  | .stuck, _ => trivial

theorem pick_wf {x : V} {args rets : List V} :
    ∀ (fs : List String) (j : ℕ), (pick σ x args rets j fs).All (Ev.Wf P)
  | [], _ => trivial
  | f :: fs, j => by
      unfold pick
      split_ifs
      · intro e he
        rw [List.mem_singleton] at he
        subst he
        trivial
      · exact pick_wf fs (j + 1)

mutual
theorem walk1_wf : ∀ (s : Stmt), Stmt.wf P s = true → (walk1 σ s).All (Ev.Wf P)
  | .atom _, _ => by
      intro e he
      rw [List.mem_singleton] at he
      subst he
      trivial
  | .ite c z n, hw => by
      simp only [Stmt.wf, Bool.and_eq_true] at hw
      rw [walk1]
      refine Out.all_pre (fun e he => by rw [List.mem_singleton] at he; subst he; trivial) ?_
      split_ifs
      · exact walk_wf z hw.1
      · exact walk_wf n hw.2
  | .match_ x arms, hw => by
      simp only [Stmt.wf, Bool.and_eq_true] at hw
      exact walkArms_wf x arms 0 hw.2
  | .call .., _ => by
      intro e he
      rw [List.mem_singleton] at he
      subst he
      trivial
  | .callIf c f args, hw => by
      rw [walk1]
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · trivial
      · split_ifs
        · exact hw
        · trivial
  | .dispatch x fs args rets, _ => pick_wf fs 0
  | .ret _, _ => fun _ he => (List.not_mem_nil he).elim

theorem walk_wf : ∀ (ss : List Stmt), Stmt.wfList P ss = true → (walk σ ss).All (Ev.Wf P)
  | [], _ => fun _ he => (List.not_mem_nil he).elim
  | s :: ss, hw => by
      simp only [Stmt.wfList, Bool.and_eq_true] at hw
      rw [walk]
      exact Out.all_seq (walk_wf ss hw.2) (walk1_wf s hw.1)

theorem walkArms_wf (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ), Stmt.wfArms P arms = true →
    (walkArms σ x j arms).All (Ev.Wf P)
  | [], _, _ => trivial
  | a :: as, j, hw => by
      simp only [Stmt.wfArms, Bool.and_eq_true] at hw
      unfold walkArms
      split_ifs
      · exact walk_wf a hw.1
      · exact walkArms_wf x as (j + 1) hw.2
end

end Converse

/-! ## `HeapBuf` sizes -/

section

open Classical

/-- The least exponent `e` with `w = g^e`, `0` if there is none. -/
noncomputable def logG (w : E) : ℕ :=
  if h : ∃ e, w = ofK (gpow e) then Nat.find h else 0

end

theorem logG_spec {e : ℕ} (he : e < 2 ^ 64 - 1) : logG (ofK (gpow e)) = e := by
  classical
  have h : ∃ e', ofK (gpow e) = ofK (gpow e') := ⟨e, rfl⟩
  rw [logG, dite_eq_left h]
  have hle : Nat.find h ≤ e := Nat.find_min' h rfl
  exact gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
    (ofK_injective (Nat.find_spec h)).symm

/-- The `HeapBuf` size an event allocates: `n` for `HeapBuf(n)`, the exponent of the size word
for a dynamic one. -/
noncomputable def Ev.alloc? (σ : Val) : Ev → Option ℕ
  | .atom (.hint (.alloc _ n)) => some n
  | .atom (.hint (.allocDyn _ s)) => some (logG (σ s))
  | _ => none

/-- The `HeapBuf` sizes of a path, in allocation order. -/
noncomputable def allocs (σ : Val) (es : List Ev) : List ℕ := es.filterMap (Ev.alloc? σ)

mutual
/-- **The `HeapBuf`s of the paths**: every call instance's sizes are those its path allocates. -/
def Tree.BufsOk (P : Core.Program) : Tree → Prop
  | t@(.node _ σ bufs kids) => bufs = allocs σ (t.events P) ∧ Tree.BufsOkKids P kids
  | .phantom .. => True

/-- `Tree.BufsOk` of the callees. -/
def Tree.BufsOkKids (P : Core.Program) : List Tree → Prop
  | [] => True
  | k :: ks => k.BufsOk P ∧ Tree.BufsOkKids P ks
end

/-! ## Phantoms -/

/-- A phantom's valuation: the `k`-th word written at parameter `k`, `0` elsewhere. -/
def phantomVal : List V → List E → Val
  | p :: ps, w :: ws => fun v => if v = p then w else phantomVal ps ws v
  | _, _ => fun _ => 0

theorem map_phantomVal : ∀ (ps : List V) (ws : List E), ps.Nodup → ps.length = ws.length →
    ps.map (phantomVal ps ws) = ws
  | [], [], _, _ => rfl
  | p :: ps, w :: ws, hnd, hl => by
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, phantomVal, ↓reduceIte, List.cons.injEq, true_and]
      rw [List.map_congr_left fun v hv => ite_eq_right (fun he : v = p => hnd.1 (he ▸ hv))]
      exact map_phantomVal ps ws hnd.2 (by simpa using hl)
  | [], _ :: _, _, hl => by simp at hl
  | _ :: _, [], _, hl => by simp at hl

/-- A callee that `Takes` the call's arguments has a phantom on any words written. -/
theorem phantom_of_takes {P : Core.Program} {f : String} {ws : List E}
    (h : P.Takes f ws.length = true) :
    ∃ σ', Phantom P (.phantom f σ') ws := by
  unfold Program.Takes at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨phantomVal fn.params ws, fn, hf, map_phantomVal _ _ h.2 h.1⟩
  · exact absurd h (by simp)

/-! ## The call tree of a derivation -/

section Tree

variable {P : Core.Program} {rd : Reader}

theorem events_node {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {fn : Fn}
    {es : List Ev} {vs : List V} (hf : P.find? f = some fn) (hw : walk σ fn.body = .ret es vs) :
    (Tree.node f σ bufs kids).events P = es := by
  simp only [Tree.events, Tree.name, Tree.val, hf, hw]

/-- The callees of a path whose calls hold of `P.relN rd n`, given trees for those. -/
theorem kids_of_events {n : ℕ} {σ : Val}
    (ih : ∀ f args rets, P.relN rd n f args rets →
      ∃ t : Tree, t.name = f ∧ t.Valid P rd args rets ∧ t.BufsOk P) :
    ∀ es : List Ev, (∀ e ∈ es, e.Ok (P.relN rd n) rd σ) → (∀ e ∈ es, e.Wf P) →
      ∃ ks, Tree.KidsValid P rd σ (calls es) ks ∧ Tree.BufsOkKids P ks
  | [], _, _ => ⟨[], by simp [calls, Tree.KidsValid], trivial⟩
  | e :: es, ho, hw => by
      obtain ⟨ks, hk, hb⟩ := kids_of_events ih es (fun e he => ho e (List.mem_cons_of_mem _ he))
        (fun e he => hw e (List.mem_cons_of_mem _ he))
      have ho := ho e List.mem_cons_self
      have hw := hw e List.mem_cons_self
      cases e with
      | atom _ => exact ⟨ks, by simpa [calls, List.filterMap_cons, Ev.call?] using hk, hb⟩
      | inK _ => exact ⟨ks, by simpa [calls, List.filterMap_cons, Ev.call?] using hk, hb⟩
      | call f args rets =>
          obtain ⟨t, hn, hv, htb⟩ := ih f _ _ (ho.2 f args rets rfl)
          refine ⟨t :: ks, ?_, htb, hb⟩
          simp only [calls, List.filterMap_cons, Ev.call?]
          exact ⟨hn, by simpa using hv, by simpa [calls] using hk⟩
      | skip f args =>
          obtain ⟨σ', hph⟩ := phantom_of_takes (ws := args.map σ) (by rw [List.length_map]; exact hw)
          refine ⟨.phantom f σ' :: ks, ?_, trivial, hb⟩
          simp only [calls, List.filterMap_cons, Ev.call?]
          exact ⟨rfl, by simpa using hph, by simpa [calls] using hk⟩

/-- **A derivation of `Program.relN` is a valid tree**, of a well-formed program. -/
theorem relN_tree (hP : P.Wf) : ∀ (n : ℕ) (f : String) (args rets : List E),
    P.relN rd n f args rets → ∃ t : Tree, t.name = f ∧ t.Valid P rd args rets ∧ t.BufsOk P
  | 0, _, _, _, h => h.elim
  | n + 1, f, args, rets, ⟨fn, hf, σ, hp, hb⟩ => by
      have hwf := hP fn (List.mem_of_find?_eq_some hf)
      have hs := walk_sat (C := P.relN rd n) fn.body hwf hb
      have ha := walk_wf (σ := σ) fn.body hwf
      cases hwk : walk σ fn.body with
      | fall es =>
          rw [hwk] at hs
          exact hs.2.elim
      | stuck =>
          rw [hwk] at hs
          exact hs.elim
      | ret es vs =>
          rw [hwk] at hs ha
          obtain ⟨ks, hk, hkb⟩ := kids_of_events (relN_tree hP n) es hs.1 ha
          refine ⟨.node f σ (allocs σ es) ks, rfl,
            ⟨fn, hf, hp, es, vs, hwk, hs.2, fun e he => (hs.1 e he).1, hk⟩, ?_⟩
          rw [Tree.BufsOk, events_node hf hwk]
          exact ⟨rfl, hkb⟩

/-- **A derivation of `Program.Rel` is a valid tree** of a well-formed program: a call tree of
`f` on its argument and return words, every instance's `HeapBuf`s those of its path and every
untaken `callIf` a phantom holding the words written. -/
theorem _root_.LeanVM.Guest.Core.Program.Rel.tree (hP : P.Wf) {f : String} {args rets : List E}
    (h : P.Rel rd f args rets) :
    ∃ t : Tree, t.name = f ∧ t.Valid P rd args rets ∧ t.BufsOk P :=
  let ⟨n, hn⟩ := h
  relN_tree hP n f args rets hn

/-- **`Program.Rel` is the valid trees** of a well-formed program. -/
theorem rel_iff_tree (hP : P.Wf) {f : String} {args rets : List E} :
    P.Rel rd f args rets ↔ ∃ t : Tree, t.name = f ∧ t.Valid P rd args rets :=
  ⟨fun h => let ⟨t, hn, hv, _⟩ := Program.Rel.tree hP h; ⟨t, hn, hv⟩,
    fun ⟨t, hn, hv⟩ => hn ▸ hv.rel t⟩

end Tree

end
end LeanVM.Guest.Memory
