/-
  LeanVM.Guest.Memory.Placed

  Call trees placed by the bump allocator: every `HeapBuf` pointer the base the allocator gives
  it and every `frameAddr` the address of its frame run, both relative to the instance's own
  frame; `Program.Rel` indexed by that placement (`RelAt`), how a function's placed relation
  composes from its callees' along its path, and the subtrees with nothing to place.
-/

module

public import LeanVM.Guest.Memory.Alloc
public import LeanVM.Guest.Memory.Tree

/-!
# Placed call trees

`Program.Rel.tree` gives some valuation per call instance; the honest memory needs the one whose
`HeapBuf` pointers are where the bump allocator puts them (`Memory/Alloc.lean`), and pointers
cannot be moved after the fact (a counter `g^n` may equal an address, and some buffers hold
pointers). So completeness proofs choose them, and this file says what they choose.

Two kinds of core values depend on where an instance lies, both on its own frame pointer `fp`
and sizes only:

* the pointer of the `j`-th `HeapBuf` hint (`alloc`, `allocDyn`) on the path is `g^(bufBase +
  bufs[0] + … + bufs[j-1])`, `bufBase` right after the frame (after the tail call's region for a
  loop helper);
* the pointer of `frameAddr p (r :: _)` is `g^(fp + cert f r)`, the frame cell holding `r` by the
  certificate `cert`.

Frame pointers themselves are not core values (frame plumbing is not in the IR), so a callee's
frame is free; the allocator puts the `i`-th at `kidPos …[i]`.

`Tree.Placed P fs cert fp t` says this of every instance of `t` placed from `fp`, and
`RelAt P fs cert rd fp n f args rets` is `Program.Rel` by a tree so placed, of `n` words. A
completeness proof of an allocating function concludes `∀ fp, MemAt rd fp → ∃ n, RelAt … fp n f
args rets ∧ n ≤ cost`, its callees' at their placements:

* `relAt_of_walk`: a function that is not a loop helper, from its path: the parameters, the
  `HeapBuf` pointers from `fp + fs f`, the `frameAddr`s, and its callees one after another from
  the end of its `HeapBuf`s (`KidsFrom`), each call entered `RelAt` at its running offset and
  each not entered a phantom of its callee's frame size;
* `relAt_of_walk_loop`: a loop helper, its tail call (its last) at `fp + fs f` first, of `m`
  words, then its `HeapBuf`s from `fp + fs f + m`, then its other callees;
* `relAt_of_rel_pure`: a function whose whole call subtree allocates nothing and takes no
  `frameAddr` (`Program.PureIn`, decidable on the program) is placed anywhere: `Program.Rel`
  gives `∃ n, ∀ fp, RelAt … fp n`.

`insts_placedAt`: every instance of a placed tree is placed at its frame, so its `HeapBuf`
pointers are its `bufBases` and its `frameAddr`s point into its frame (`Inst.nodeAt`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-! ## What a path places -/

/-- The pointer an event's `HeapBuf` hint writes. -/
def Ev.allocDst? : Ev → Option V
  | .atom (.hint (.alloc d _)) => some d
  | .atom (.hint (.allocDyn d _)) => some d
  | _ => none

/-- The `HeapBuf` pointers of a path, in allocation order. -/
def allocDsts (es : List Ev) : List V := es.filterMap Ev.allocDst?

/-- An event's `frameAddr`: its pointer and the first value of its run. -/
def Ev.addr? : Ev → Option (V × V)
  | .atom (.frameAddr p (r :: _)) => some (p, r)
  | _ => none

/-- The `frameAddr`s of a path. -/
def addrs (es : List Ev) : List (V × V) := es.filterMap Ev.addr?

variable (P : Core.Program) (fs : String → ℕ) (cert : String → V → ℕ)

/-- An instance of `f` at `fp` with valuation `σ`, `HeapBuf`s `bufs`, callee regions of sizes
`ns` and path `es` is placed: its `HeapBuf` pointers are the allocator's bases, its `frameAddr`s
the addresses of their runs in its frame. -/
def NodeAt (fp : ℕ) (f : String) (σ : Val) (bufs ns : List ℕ) (es : List Ev) : Prop :=
  (allocDsts es).map σ = (bases (bufBase fs P.loop fp f ns) bufs).map (fun b => ofK (gpow b)) ∧
    ∀ q ∈ addrs es, σ q.1 = ofK (gpow (fp + cert f q.2))

mutual
/-- **A placed tree**: every instance of `t` placed from `fp` is `NodeAt` its frame. -/
def Tree.Placed (fp : ℕ) : Tree → Prop
  | t@(.node f σ bufs kids) =>
      NodeAt P fs cert fp f σ bufs (kids.map (Tree.total fs)) (t.events P) ∧
        Tree.PlacedKids (kidPos fs P.loop fp f bufs (kids.map (Tree.total fs))) kids
  | .phantom .. => True

/-- The callees `ks` placed at `ps`. -/
def Tree.PlacedKids : List ℕ → List Tree → Prop
  | _, [] => True
  | [], _ :: _ => True
  | p :: ps, k :: ks => k.Placed p ∧ Tree.PlacedKids ps ks
end

/-- **`Program.Rel` placed at `fp`**: a valid tree of `f` on `args`, `rets`, its `HeapBuf`s those
of its paths, placed from `fp`, of `n` words. -/
def RelAt (rd : Reader) (fp n : ℕ) (f : String) (args rets : List E) : Prop :=
  ∃ t : Tree, t.name = f ∧ t.Valid P rd args rets ∧ t.BufsOk P ∧ t.Placed P fs cert fp ∧
    t.total fs = n

/-- **The callees of the frames `cs` sets up**, their regions one after another from `b`, `n`
words in all: each call entered `RelAt` its region, each not entered a phantom of its callee's
frame size. -/
def KidsFrom (rd : Reader) (σ : Val) : List Call → ℕ → ℕ → Prop
  | [], _, n => n = 0
  | c :: cs, b, n => ∃ m n', n = m + n' ∧
      (if c.taken then RelAt P fs cert rd b m c.f (c.args.map σ) (c.rets.map σ) else m = fs c.f) ∧
      KidsFrom rd σ cs (b + m) n'

variable {P fs cert}

/-- A placed relation is a relation. -/
theorem RelAt.rel {rd : Reader} {fp n : ℕ} {f : String} {args rets : List E}
    (h : RelAt P fs cert rd fp n f args rets) : P.Rel rd f args rets :=
  let ⟨t, hn, hv, _⟩ := h
  hn ▸ hv.rel t

theorem placed_node {fp : ℕ} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} :
    (Tree.node f σ bufs kids).Placed P fs cert fp ↔
      NodeAt P fs cert fp f σ bufs (kids.map (Tree.total fs)) ((Tree.node f σ bufs kids).events P) ∧
        Tree.PlacedKids P fs cert (kidPos fs P.loop fp f bufs (kids.map (Tree.total fs))) kids := by
  rw [Tree.Placed]

theorem placed_phantom {fp : ℕ} {f : String} {σ : Val} : (Tree.phantom f σ).Placed P fs cert fp := by
  rw [Tree.Placed]; trivial

theorem placedKids_cons {p : ℕ} {ps : List ℕ} {k : Tree} {ks : List Tree} :
    Tree.PlacedKids P fs cert (p :: ps) (k :: ks) ↔ k.Placed P fs cert p ∧ Tree.PlacedKids P fs cert ps ks := by
  rw [Tree.PlacedKids]

theorem placedKids_nil {ps : List ℕ} : Tree.PlacedKids P fs cert ps [] := by
  cases ps <;> (rw [Tree.PlacedKids]; trivial)

theorem placedKids_append : ∀ {ps : List ℕ} {ks : List Tree} {ps' : List ℕ} {ks' : List Tree},
    ps.length = ks.length → Tree.PlacedKids P fs cert ps ks → Tree.PlacedKids P fs cert ps' ks' →
      Tree.PlacedKids P fs cert (ps ++ ps') (ks ++ ks')
  | [], [], _, _, _, _, h => h
  | p :: ps, k :: ks, _, _, hl, h, h' => by
      rw [placedKids_cons] at h
      rw [List.cons_append, List.cons_append, placedKids_cons]
      exact ⟨h.1, placedKids_append (by simpa using hl) h.2 h'⟩
  | [], _ :: _, _, _, hl, _, _ => absurd hl (by simp)
  | _ :: _, [], _, _, hl, _, _ => absurd hl (by simp)

/-! ## Composing a placed relation -/

section Compose

variable {rd : Reader} {σ : Val}

theorem kidsValid_append : ∀ {cs : List Call} {ks : List Tree} {cs' : List Call} {ks' : List Tree},
    Tree.KidsValid P rd σ cs ks → Tree.KidsValid P rd σ cs' ks' →
      Tree.KidsValid P rd σ (cs ++ cs') (ks ++ ks')
  | [], [], _, _, _, h' => h'
  | _ :: _, _ :: _, _, _, ⟨hn, hc, h⟩, h' => ⟨hn, hc, kidsValid_append h h'⟩
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim

theorem bufsOkKids_append : ∀ {ks ks' : List Tree}, Tree.BufsOkKids P ks → Tree.BufsOkKids P ks' →
    Tree.BufsOkKids P (ks ++ ks')
  | [], _, _, h' => h'
  | k :: ks, _, h, h' => by
      rw [Tree.BufsOkKids] at h
      rw [List.cons_append, Tree.BufsOkKids]
      exact ⟨h.1, bufsOkKids_append h.2 h'⟩

/-- The callee of one frame: a placed tree of a call entered, a phantom of one not. -/
theorem kid_of {c : Call} {b m : ℕ} (hc : c.taken = false → P.Takes c.f c.args.length = true)
    (h : if c.taken then RelAt P fs cert rd b m c.f (c.args.map σ) (c.rets.map σ) else m = fs c.f) :
    ∃ k : Tree, Tree.KidsValid P rd σ [c] [k] ∧ k.BufsOk P ∧ k.Placed P fs cert b ∧
      k.total fs = m := by
  by_cases ht : c.taken = true
  · rw [ite_eq_left ht] at h
    obtain ⟨k, hn, hv, hb, hp, htot⟩ := h
    exact ⟨k, ⟨hn, by rw [ite_eq_left ht]; exact hv, trivial⟩, hb, hp, htot⟩
  · rw [ite_eq_right ht] at h
    obtain ⟨σ', hph⟩ := phantom_of_takes (P := P) (f := c.f) (ws := c.args.map σ)
      (by rw [List.length_map]; exact hc (by simpa using ht))
    refine ⟨.phantom c.f σ', ⟨rfl, by rw [ite_eq_right ht]; exact ⟨⟨_, _, rfl⟩, hph⟩, trivial⟩,
      by rw [Tree.BufsOk]; trivial, placed_phantom, by rw [Tree.total, h]⟩

/-- The callees of `KidsFrom`, placed one after another from `b`. -/
theorem kids_of_kidsFrom : ∀ (cs : List Call) (b n : ℕ),
    (∀ c ∈ cs, c.taken = false → P.Takes c.f c.args.length = true) →
    KidsFrom P fs cert rd σ cs b n →
    ∃ ks : List Tree, Tree.KidsValid P rd σ cs ks ∧ Tree.BufsOkKids P ks ∧
      Tree.PlacedKids P fs cert (bases b (ks.map (Tree.total fs))) ks ∧
      (ks.map (Tree.total fs)).sum = n
  | [], _, n, _, h => ⟨[], by simp [Tree.KidsValid], by rw [Tree.BufsOkKids]; trivial,
      placedKids_nil, by rw [KidsFrom] at h; simp [h]⟩
  | c :: cs, b, n, hw, h => by
      rw [KidsFrom] at h
      obtain ⟨m, n', rfl, hc, hcs⟩ := h
      obtain ⟨k, hkv, hkb, hkp, hkt⟩ := kid_of (hw c List.mem_cons_self) hc
      obtain ⟨ks, hv, hb, hp, hs⟩ :=
        kids_of_kidsFrom cs (b + m) n' (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')) hcs
      refine ⟨k :: ks, ⟨hkv.1, hkv.2.1, hv⟩, by rw [Tree.BufsOkKids]; exact ⟨hkb, hb⟩, ?_, ?_⟩
      · rw [List.map_cons, bases, placedKids_cons, hkt]
        exact ⟨hkp, hp⟩
      · rw [List.map_cons, List.sum_cons, hkt, hs]

/-- A frame set up and not entered is one its callee takes, in a well-formed program. -/
theorem takes_of_calls (hP : P.Wf) {fn : Fn} (hfn : fn ∈ P) {es : List Ev} {vs : List V}
    (hw : walk σ fn.body = .ret es vs) :
    ∀ c ∈ calls es, c.taken = false → P.Takes c.f c.args.length = true := by
  have ha := walk_wf (σ := σ) fn.body (hP fn hfn)
  rw [hw] at ha
  intro c hc ht
  obtain ⟨e, he, hce⟩ := List.mem_filterMap.mp hc
  have := ha e he
  cases e with
  | skip f args => cases hce; exact this
  | call f args rets => cases hce; simp at ht
  | atom _ => simp [Ev.call?] at hce
  | inK _ => simp [Ev.call?] at hce

theorem kidPos_not_loop {fp : ℕ} {f : String} {bufs ns : List ℕ} (hl : P.loop f = false ∨ ns = []) :
    bufBase fs P.loop fp f ns = fp + fs f ∧
      kidPos fs P.loop fp f bufs ns = bases (fp + fs f + bufs.sum) ns := by
  rcases hl with hl | rfl
  · simp [bufBase, kidPos, hl]
  · simp [bufBase, kidPos, bases]

/-- **Composition**, a function that is not a loop helper (or whose path calls nothing): its
parameters, its path, its `HeapBuf` pointers from `fp + fs f`, its `frameAddr`s in its frame, and
its callees one after another from the end of its `HeapBuf`s give it `RelAt fp`, of its frame,
`HeapBuf`s and callees' words. -/
theorem relAt_of_walk (hP : P.Wf) {fp N : ℕ} {f : String} {args rets : List E} {fn : Fn}
    {es : List Ev} {vs : List V} (hf : P.find? f = some fn) (hl : P.loop f = false ∨ calls es = [])
    (hp : fn.params.map σ = args) (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets)
    (hes : ∀ e ∈ es, e.Holds rd σ)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f) (allocs σ es)).map fun b => ofK (gpow b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (gpow (fp + cert f q.2)))
    (hk : KidsFrom P fs cert rd σ (calls es) (fp + fs f + (allocs σ es).sum) N) :
    RelAt P fs cert rd fp (fs f + (allocs σ es).sum + N) f args rets := by
  obtain ⟨ks, hkv, hkb, hkp, hks⟩ :=
    kids_of_kidsFrom _ _ _ (takes_of_calls hP (List.mem_of_find?_eq_some hf) hw) hk
  have hl' : P.loop f = false ∨ ks.map (Tree.total fs) = [] := by
    rcases hl with hl | hl
    · exact Or.inl hl
    · rw [hl] at hkv
      cases ks with
      | nil => exact Or.inr rfl
      | cons _ _ => exact hkv.elim
  obtain ⟨hbb, hkpos⟩ := kidPos_not_loop (fs := fs) (fp := fp) (bufs := allocs σ es) hl'
  refine ⟨.node f σ (allocs σ es) ks, rfl, ⟨fn, hf, hp, es, vs, hw, hr, hes, hkv⟩, ?_, ?_, ?_⟩
  · rw [Tree.BufsOk, events_node hf hw]
    exact ⟨rfl, hkb⟩
  · rw [placed_node, events_node hf hw, NodeAt, hbb, hkpos]
    exact ⟨⟨hbuf, haddr⟩, hkp⟩
  · rw [total_node, totalKids_eq_sum, hks]
    omega

/-- **Composition**, a loop helper: as `relAt_of_walk`, its tail call (its last) first, at
`fp + fs f`, of `m` words, then its `HeapBuf`s from `fp + fs f + m`, then its other callees. -/
theorem relAt_of_walk_loop (hP : P.Wf) {fp m N : ℕ} {f : String} {args rets : List E} {fn : Fn}
    {es : List Ev} {vs : List V} {cs : List Call} {c : Call} (hf : P.find? f = some fn)
    (hl : P.loop f = true) (hp : fn.params.map σ = args) (hw : walk σ fn.body = .ret es vs)
    (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.Holds rd σ) (hc : calls es = cs ++ [c])
    (htail : if c.taken then RelAt P fs cert rd (fp + fs f) m c.f (c.args.map σ) (c.rets.map σ)
      else m = fs c.f)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f + m) (allocs σ es)).map fun b => ofK (gpow b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (gpow (fp + cert f q.2)))
    (hk : KidsFrom P fs cert rd σ cs (fp + fs f + m + (allocs σ es).sum) N) :
    RelAt P fs cert rd fp (fs f + m + (allocs σ es).sum + N) f args rets := by
  have htk := takes_of_calls hP (List.mem_of_find?_eq_some hf) hw
  rw [hc] at htk
  obtain ⟨ks, hkv, hkb, hkp, hks⟩ := kids_of_kidsFrom _ _ _
    (fun c' hc' => htk c' (List.mem_append_left _ hc')) hk
  obtain ⟨k, hkv', hkb', hkp', hkt⟩ :=
    kid_of (htk c (List.mem_append_right _ List.mem_cons_self)) htail
  have hns : (ks ++ [k]).map (Tree.total fs) = ks.map (Tree.total fs) ++ [m] := by
    rw [List.map_append, List.map_singleton, hkt]
  have hbb : bufBase fs P.loop fp f ((ks ++ [k]).map (Tree.total fs)) = fp + fs f + m := by
    rw [hns]; simp [bufBase, hl]
  have hkpos : kidPos fs P.loop fp f (allocs σ es) ((ks ++ [k]).map (Tree.total fs)) =
      bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs)) ++ [fp + fs f] := by
    rw [kidPos, ite_eq_left hl, hbb, hns, List.dropLast_concat, List.getLast?_concat]
    rfl
  refine ⟨.node f σ (allocs σ es) (ks ++ [k]), rfl,
    ⟨fn, hf, hp, es, vs, hw, hr, hes, by rw [hc]; exact kidsValid_append hkv hkv'⟩, ?_, ?_, ?_⟩
  · rw [Tree.BufsOk, events_node hf hw]
    refine ⟨rfl, bufsOkKids_append hkb ?_⟩
    rw [Tree.BufsOkKids, Tree.BufsOkKids]
    exact ⟨hkb', trivial⟩
  · rw [placed_node, events_node hf hw, NodeAt, hbb, hkpos]
    refine ⟨⟨hbuf, haddr⟩, placedKids_append (by rw [length_bases, List.length_map]) hkp ?_⟩
    rw [placedKids_cons]
    exact ⟨hkp', placedKids_nil⟩
  · rw [total_node, totalKids_eq_sum, hns, List.sum_append, hks]
    simp only [List.sum_cons, List.sum_nil]
    omega

end Compose

/-! ## Subtrees with nothing to place -/

/-- Neither a `HeapBuf` hint nor a `frameAddr`. -/
def atomUnplaced : Atom → Bool
  | .hint (.alloc ..) => false
  | .hint (.allocDyn ..) => false
  | .frameAddr .. => false
  | _ => true

mutual
/-- A statement places nothing and calls only functions of `S`. -/
def Stmt.pure (S : List String) : Stmt → Bool
  | .atom a => atomUnplaced a
  | .ite _ z n => Stmt.pureList S z && Stmt.pureList S n
  | .match_ _ arms => Stmt.pureArms S arms
  | .call f _ _ => decide (f ∈ S)
  | .callIf _ f _ => decide (f ∈ S)
  | .dispatch _ fs _ _ => fs.all fun f => decide (f ∈ S)
  | .ret _ => true

/-- A block places nothing and calls only functions of `S`. -/
def Stmt.pureList (S : List String) : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.pure S s && Stmt.pureList S ss

/-- Arms placing nothing and calling only functions of `S`. -/
def Stmt.pureArms (S : List String) : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.pureList S a && Stmt.pureArms S as
end

/-- **A set of functions closed under calls that places nothing**: no `HeapBuf` hint and no
`frameAddr` in any of their bodies, and every callee in the set. -/
def _root_.LeanVM.Guest.Core.Program.PureIn (P : Core.Program) (S : List String) : Prop :=
  ∀ g ∈ S, ∀ fn, P.find? g = some fn → Stmt.pureList S fn.body = true

/-- An event placing nothing, a frame it sets up one of `S`'s. -/
def Ev.pure (S : List String) : Ev → Prop
  | .atom a => atomUnplaced a = true
  | .call f _ _ => f ∈ S
  | .skip f _ => f ∈ S
  | .inK _ => True

section Pure

variable {S : List String} {σ : Val}

theorem pick_pure {x : V} {args rets : List V} :
    ∀ (gs : List String) (j : ℕ), (gs.all fun f => decide (f ∈ S)) = true →
      (pick σ x args rets j gs).All (Ev.pure S)
  | [], _, _ => trivial
  | g :: gs, j, h => by
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      unfold pick
      split_ifs
      · intro e he
        rw [List.mem_singleton] at he
        subst he
        exact h.1
      · exact pick_pure gs (j + 1) h.2

mutual
theorem walk1_pure : ∀ (s : Stmt), Stmt.pure S s = true → (walk1 σ s).All (Ev.pure S)
  | .atom _, h => by
      intro e he
      rw [List.mem_singleton] at he
      subst he
      exact h
  | .ite c z n, h => by
      simp only [Stmt.pure, Bool.and_eq_true] at h
      rw [walk1]
      refine Out.all_pre (fun e he => by rw [List.mem_singleton] at he; subst he; trivial) ?_
      split_ifs
      · exact walk_pure z h.1
      · exact walk_pure n h.2
  | .match_ x arms, h => walkArms_pure x arms 0 h
  | .call .., h => by
      intro e he
      rw [List.mem_singleton] at he
      subst he
      simpa [Stmt.pure, Ev.pure] using h
  | .callIf c f args, h => by
      simp only [Stmt.pure, decide_eq_true_eq] at h
      rw [walk1]
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · trivial
      · split_ifs
        · exact h
        · exact h
  | .dispatch x fs args rets, h => pick_pure fs 0 h
  | .ret _, _ => fun _ he => (List.not_mem_nil he).elim

theorem walk_pure : ∀ (ss : List Stmt), Stmt.pureList S ss = true → (walk σ ss).All (Ev.pure S)
  | [], _ => fun _ he => (List.not_mem_nil he).elim
  | s :: ss, h => by
      simp only [Stmt.pureList, Bool.and_eq_true] at h
      rw [walk]
      exact Out.all_seq (walk_pure ss h.2) (walk1_pure s h.1)

theorem walkArms_pure (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ), Stmt.pureArms S arms = true →
    (walkArms σ x j arms).All (Ev.pure S)
  | [], _, _ => trivial
  | a :: as, j, h => by
      simp only [Stmt.pureArms, Bool.and_eq_true] at h
      unfold walkArms
      split_ifs
      · exact walk_pure a h.1
      · exact walkArms_pure x as (j + 1) h.2
end

theorem allocDsts_pure {es : List Ev} (h : ∀ e ∈ es, e.pure S) : allocDsts es = [] := by
  refine List.filterMap_eq_nil_iff.mpr fun e he => ?_
  have := h e he
  rcases e with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩⟩ | _ | _ | _ <;>
    first | rfl | simp [Ev.pure, atomUnplaced] at this

theorem allocs_pure {es : List Ev} (h : ∀ e ∈ es, e.pure S) : allocs σ es = [] := by
  refine List.filterMap_eq_nil_iff.mpr fun e he => ?_
  have := h e he
  rcases e with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩⟩ | _ | _ | _ <;>
    first | rfl | simp [Ev.pure, atomUnplaced] at this

theorem addrs_pure {es : List Ev} (h : ∀ e ∈ es, e.pure S) : addrs es = [] := by
  refine List.filterMap_eq_nil_iff.mpr fun e he => ?_
  have := h e he
  rcases e with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _⟩ | _ | _ | _ <;>
    first | rfl | simp [Ev.pure, atomUnplaced] at this

theorem calls_pure {es : List Ev} (h : ∀ e ∈ es, e.pure S) : ∀ c ∈ calls es, c.f ∈ S := by
  intro c hc
  obtain ⟨e, he, hce⟩ := List.mem_filterMap.mp hc
  have := h e he
  cases e with
  | call f args rets => cases hce; exact this
  | skip f args => cases hce; exact this
  | atom _ => simp [Ev.call?] at hce
  | inK _ => simp [Ev.call?] at hce

variable {rd : Reader}

mutual
/-- A valid tree of a function of a pure set is placed anywhere. -/
theorem placed_of_pure (hS : P.PureIn S) : ∀ (t : Tree) {args rets : List E},
    t.Valid P rd args rets → t.BufsOk P → t.name ∈ S → ∀ fp, t.Placed P fs cert fp
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hb, hn, fp => by
      have hpure : ∀ e ∈ es, e.pure S := by
        have := walk_pure (σ := σ) fn.body (hS f hn fn hf)
        rwa [hw] at this
      rw [Tree.BufsOk, events_node hf hw, allocs_pure hpure] at hb
      obtain ⟨rfl, hkb⟩ := hb
      rw [placed_node, events_node hf hw]
      refine ⟨⟨by rw [allocDsts_pure hpure]; rfl, fun q hq => by
        rw [addrs_pure hpure] at hq; exact (List.not_mem_nil hq).elim⟩, ?_⟩
      exact placedKids_of_pure hS kids σ (calls es) hk hkb (calls_pure hpure) _
  | .phantom .., _, _, h, _, _, _ => h.elim

/-- `placed_of_pure` for the callees. -/
theorem placedKids_of_pure (hS : P.PureIn S) : ∀ (ks : List Tree) (σ : Val) (cs : List Call),
    Tree.KidsValid P rd σ cs ks → Tree.BufsOkKids P ks → (∀ c ∈ cs, c.f ∈ S) →
      ∀ ps, Tree.PlacedKids P fs cert ps ks
  | [], _, _, _, _, _, _ => placedKids_nil
  | _ :: _, _, _, _, _, _, [] => by rw [Tree.PlacedKids]; trivial
  | k :: ks, σ, c :: cs, ⟨hn, hc, hks⟩, hb, hS', p :: ps => by
      rw [Tree.BufsOkKids] at hb
      rw [placedKids_cons]
      refine ⟨?_, placedKids_of_pure hS ks σ cs hks hb.2
        (fun c' hc' => hS' c' (List.mem_cons_of_mem _ hc')) ps⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact placed_of_pure hS k hc hb.1 (hn ▸ hS' c List.mem_cons_self) p
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        exact placed_phantom
  | _ :: _, _, [], h, _, _, _ :: _ => h.elim
end

/-- **A function of a pure set is placed anywhere**: in a well-formed program, `Program.Rel`
gives `RelAt` at every frame pointer, of one size. -/
theorem relAt_of_rel_pure (hP : P.Wf) (hS : P.PureIn S) {g : String} (hg : g ∈ S)
    {args rets : List E} (h : P.Rel rd g args rets) :
    ∃ n, ∀ fp, RelAt P fs cert rd fp n g args rets := by
  obtain ⟨t, hn, hv, hb⟩ := Program.Rel.tree hP h
  exact ⟨t.total fs, fun fp => ⟨t, hn, hv, hb, placed_of_pure hS t hv hb (hn ▸ hg) fp, rfl⟩⟩

end Pure

/-! ## The instances of a placed tree -/

section Insts

variable {lp : String → Bool} {H : Inst → ℕ → E × E}

mutual
/-- **Every instance of a placed tree is placed at its frame.** -/
theorem insts_placedAt : ∀ (t : Tree) (fp : ℕ) (hdr : E × E), t.Placed P fs cert fp →
    ∀ I ∈ t.insts fs P.loop H fp hdr, I.t.Placed P fs cert I.fp
  | .node f σ bufs kids, fp, hdr, hp, I, hI => by
      rw [insts_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact hp
      · rw [placed_node] at hp
        exact instsKids_placedAt kids _ _ 0 hp.2 I hI
  | .phantom .., fp, hdr, _, I, hI => by
      rw [insts_phantom, List.mem_singleton] at hI
      subst hI
      exact placed_phantom

/-- `insts_placedAt` for the callees. -/
theorem instsKids_placedAt : ∀ (ks : List Tree) (ps : List ℕ) (J : Inst) (j : ℕ),
    Tree.PlacedKids P fs cert ps ks → ∀ I ∈ Tree.instsKids fs P.loop H J j ps ks,
      I.t.Placed P fs cert I.fp
  | [], _, _, _, _, I, hI => by rw [instsKids_nil] at hI; exact (List.not_mem_nil hI).elim
  | _ :: _, [], _, _, _, I, hI => by
      rw [instsKids_nil_left] at hI; exact (List.not_mem_nil hI).elim
  | k :: ks, p :: ps, J, j, hp, I, hI => by
      rw [placedKids_cons] at hp
      rw [instsKids_cons, List.mem_append] at hI
      rcases hI with hI | hI
      · exact insts_placedAt k p _ hp.1 I hI
      · exact instsKids_placedAt ks ps J (j + 1) hp.2 I hI
end

/-- **An instance's `HeapBuf` pointers are its `bufBases`, its `frameAddr`s in its frame.** -/
theorem Inst.nodeAt {I : Inst} (hp : I.t.Placed P fs cert I.fp) (hI : I.Placed fs P.loop)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) :
    (allocDsts (I.t.events P)).map σ = I.bufBases.map (fun b => ofK (gpow b)) ∧
      ∀ q ∈ addrs (I.t.events P), σ q.1 = ofK (gpow (I.fp + cert f q.2)) := by
  rw [ht, placed_node] at hp
  rw [hI.2, ht]
  exact hp.1

theorem length_kidPos_kids {fp : ℕ} {f : String} {bufs : List ℕ} {kids : List Tree} :
    (kidPos fs lp fp f bufs (kids.map (Tree.total fs))).length = kids.length := by
  rw [length_kidPos, List.length_map]

mutual
/-- **Every equation is an instance's**: an atom's on the path of a node instance. -/
theorem eqns_insts : ∀ (t : Tree) (fp : ℕ) (hdr : E × E), ∀ q ∈ t.eqns P,
    ∃ I ∈ t.insts fs lp H fp hdr, (∃ f σ bufs kids, I.t = .node f σ bufs kids) ∧
      ∃ a, Ev.atom a ∈ I.t.events P ∧ q ∈ atomEqns I.t.val a
  | .node f σ bufs kids, fp, hdr, q, hq => by
      rw [Tree.eqns, List.mem_append] at hq
      rw [insts_node]
      rcases hq with hq | hq
      · obtain ⟨e, he, hqe⟩ := List.mem_flatMap.mp hq
        cases e with
        | atom a => exact ⟨_, List.mem_cons_self, ⟨f, σ, bufs, kids, rfl⟩, a, he, hqe⟩
        | inK _ => exact (List.not_mem_nil hqe).elim
        | call _ _ _ => exact (List.not_mem_nil hqe).elim
        | skip _ _ => exact (List.not_mem_nil hqe).elim
      · obtain ⟨J, hJ, h⟩ := eqnsKids_insts kids _ _ 0 length_kidPos_kids q hq
        exact ⟨J, List.mem_cons_of_mem _ hJ, h⟩
  | .phantom .., _, _, q, hq => by rw [Tree.eqns] at hq; exact (List.not_mem_nil hq).elim

/-- `eqns_insts` for the callees. -/
theorem eqnsKids_insts : ∀ (ks : List Tree) (ps : List ℕ) (I : Inst) (j : ℕ), ps.length = ks.length →
    ∀ q ∈ Tree.eqnsKids P ks, ∃ J ∈ Tree.instsKids fs lp H I j ps ks,
      (∃ f σ bufs kids, J.t = .node f σ bufs kids) ∧ ∃ a, Ev.atom a ∈ J.t.events P ∧ q ∈ atomEqns J.t.val a
  | [], _, _, _, _, q, hq => by rw [Tree.eqnsKids] at hq; exact (List.not_mem_nil hq).elim
  | _ :: _, [], _, _, hl, _, _ => absurd hl (by simp)
  | k :: ks, p :: ps, I, j, hl, q, hq => by
      rw [Tree.eqnsKids, List.mem_append] at hq
      rw [instsKids_cons]
      rcases hq with hq | hq
      · obtain ⟨J, hJ, h⟩ := eqns_insts k p (H I j) q hq
        exact ⟨J, List.mem_append_left _ hJ, h⟩
      · obtain ⟨J, hJ, h⟩ := eqnsKids_insts ks ps I (j + 1) (by simpa using hl) q hq
        exact ⟨J, List.mem_append_right _ hJ, h⟩
end

end Insts

end
end LeanVM.Guest.Memory
