/-
  LeanVM.Guest.B1.Common.PopsSeg

  A valid node's pops, read statement by statement off its body: a block that cannot return falls through before the rest of the body, so the body's pops split along it, a mute block's are nothing, an atom's its own, a call's or a dispatch's its callee's.
-/

module

public import LeanVM.Guest.B1.Common.MutePops

/-!
# Pops along a body

* `walk_notRet`: a block with no `ret` (`Stmt.noRetList`) never returns;
* `BlockKids P rd σ xs ks ps`: the block `xs` falls through, its frames' callees `ks` valid, popping `ps` with theirs spliced in; `RetKids`: the same for a block that returns;
* `Tree.retKids`: a valid node's body is `RetKids` of its callees and its pops;
* `RetKids.split`, `BlockKids.split`: a block that cannot return, then the rest;
* `BlockKids.mute`, `RetKids.mute`: a block of a mute set pops nothing; `BlockKids.atom`, `.call`, `.dispatch`: one statement's pops;
* `RetKids.dropMute`, `.dropAtom`, `.dropCall`, `.dropDispatch`, `.endMute`: the same on a body's suffixes `l.drop a`, for walking a long body by positions.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- An outcome that is no return. -/
def Out.NotRet (o : Out) : Prop := ∀ es vs, o ≠ .ret es vs

section Walk

variable {σ : Val}

theorem Out.notRet_pre {o : Out} (es : List Ev) (h : o.NotRet) : (o.pre es).NotRet := by
  intro es' vs
  cases o with
  | fall _ => simp [Out.pre]
  | ret e v => exact absurd rfl (h e v)
  | stuck => simp [Out.pre]

theorem Out.notRet_seq {o k : Out} (ho : o.NotRet) (hk : k.NotRet) : (o.seq k).NotRet := by
  cases o with
  | fall es => exact Out.notRet_pre es hk
  | ret e v => exact absurd rfl (ho e v)
  | stuck => intro _ _ h; cases h

theorem pick_notRet {x : V} {args rets : List V} : ∀ (fs : List String) (j : ℕ), (pick σ x args rets j fs).NotRet
  | [], _ => by intro _ _ h; cases h
  | f :: fs, j => by
      unfold pick
      split_ifs
      · intro _ _ h; cases h
      · exact pick_notRet fs (j + 1)

mutual
theorem walk1_notRet : ∀ (s : Stmt), Stmt.noRet s = true → (walk1 σ s).NotRet
  | .atom _, _ => by intro _ _ h; cases h
  | .ite c z n, h => by
      simp only [Stmt.noRet, Bool.and_eq_true] at h
      rw [walk1]
      refine Out.notRet_pre _ ?_
      split_ifs
      · exact walk_notRet z h.1
      · exact walk_notRet n h.2
  | .match_ x arms, h => walkArms_notRet x arms 0 h
  | .call .., _ => by intro _ _ h; cases h
  | .callIf .., _ => by intro _ _ h; cases h
  | .dispatch _ fs _ _, _ => pick_notRet fs 0
  | .ret _, h => by simp [Stmt.noRet] at h

theorem walk_notRet : ∀ (ss : List Stmt), Stmt.noRetList ss = true → (walk σ ss).NotRet
  | [], _ => by intro _ _ h; cases h
  | s :: ss, h => by
      simp only [Stmt.noRetList, Bool.and_eq_true] at h
      rw [walk]
      exact Out.notRet_seq (walk1_notRet s h.1) (walk_notRet ss h.2)

theorem walkArms_notRet (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ), Stmt.noRetArms arms = true →
    (walkArms σ x j arms).NotRet
  | [], _, _ => by intro _ _ h; cases h
  | a :: as, j, h => by
      simp only [Stmt.noRetArms, Bool.and_eq_true] at h
      unfold walkArms
      split_ifs
      · exact walk_notRet a h.1
      · exact walkArms_notRet x as (j + 1) h.2
end

theorem Out.seq_assoc' : ∀ (o k l : Out), (o.seq k).seq l = o.seq (k.seq l)
  | .fall es, .fall es', l => by cases l <;> simp [Out.seq, Out.pre, List.append_assoc]
  | .fall es, .ret es' vs, l => by simp [Out.seq, Out.pre]
  | .fall es, .stuck, l => by simp [Out.seq, Out.pre]
  | .ret es vs, k, l => by simp [Out.seq]
  | .stuck, k, l => by simp [Out.seq]

theorem walk_append_seq : ∀ (l l' : List Stmt), walk σ (l ++ l') = (walk σ l).seq (walk σ l')
  | [], l' => by
      rw [List.nil_append, walk]
      cases walk σ l' <;> simp [Out.seq, Out.pre]
  | s :: l, l' => by rw [List.cons_append, walk, walk, walk_append_seq l l', Out.seq_assoc']

/-- **A block that cannot return falls through before the rest of a returning body.** -/
theorem walk_append_ret {xs ys : List Stmt} {es : List Ev} {vs : List V} (hx : Stmt.noRetList xs = true)
    (h : walk σ (xs ++ ys) = .ret es vs) :
    ∃ e1 e2, walk σ xs = .fall e1 ∧ walk σ ys = .ret e2 vs ∧ es = e1 ++ e2 := by
  rw [walk_append_seq] at h
  have hn := walk_notRet (σ := σ) xs hx
  cases hw : walk σ xs with
  | fall e1 =>
      rw [hw, Out.seq] at h
      cases hy : walk σ ys with
      | fall _ => rw [hy, Out.pre] at h; cases h
      | ret e2 v => rw [hy, Out.pre] at h; cases h; exact ⟨e1, e2, rfl, rfl, rfl⟩
      | stuck => rw [hy, Out.pre] at h; cases h
  | ret e v => exact absurd hw (hn e v)
  | stuck => rw [hw, Out.seq] at h; cases h

/-- **A block falling through falls through in parts.** -/
theorem walk_append_fall {xs ys : List Stmt} {es : List Ev} (h : walk σ (xs ++ ys) = .fall es) :
    ∃ e1 e2, walk σ xs = .fall e1 ∧ walk σ ys = .fall e2 ∧ es = e1 ++ e2 := by
  rw [walk_append_seq] at h
  cases hw : walk σ xs with
  | fall e1 =>
      rw [hw, Out.seq] at h
      cases hy : walk σ ys with
      | fall e2 => rw [hy, Out.pre] at h; cases h; exact ⟨e1, e2, rfl, rfl, rfl⟩
      | ret _ _ => rw [hy, Out.pre] at h; cases h
      | stuck => rw [hy, Out.pre] at h; cases h
  | ret _ _ => rw [hw, Out.seq] at h; cases h
  | stuck => rw [hw, Out.seq] at h; cases h

end Walk

section Kids

variable {P : Core.Program} {rd : Reader} {σ : Val}

theorem kidsValid_split : ∀ {cs cs' : List Call} {ks : List Tree}, Tree.KidsValid P rd σ (cs ++ cs') ks →
    ∃ k1 k2, ks = k1 ++ k2 ∧ Tree.KidsValid P rd σ cs k1 ∧ Tree.KidsValid P rd σ cs' k2
  | [], _, ks, h => ⟨[], ks, rfl, trivial, h⟩
  | _ :: _, _, k :: ks, ⟨hn, hc, h⟩ =>
      let ⟨k1, k2, e, h1, h2⟩ := kidsValid_split h
      ⟨k :: k1, k2, by rw [e]; rfl, ⟨hn, hc, h1⟩, h2⟩
  | _ :: _, _, [], h => h.elim

theorem popsKids_append : ∀ (k1 k2 : List Tree),
    Tree.popsKids P rd (k1 ++ k2) = Tree.popsKids P rd k1 ++ Tree.popsKids P rd k2
  | [], _ => rfl
  | k :: ks, k2 => by rw [List.cons_append, Tree.popsKids, Tree.popsKids, popsKids_append ks k2, List.cons_append]

/-- **A block falls through**, its frames' callees `ks` valid, popping `ps` with theirs spliced in. -/
def BlockKids (P : Core.Program) (rd : Reader) (σ : Val) (xs : List Stmt) (ks : List Tree) (ps : List Pop) : Prop :=
  ∃ es, walk σ xs = .fall es ∧ Tree.KidsValid P rd σ (calls es) ks ∧ splice rd σ es (Tree.popsKids P rd ks) = ps

/-- **A block returns**, its frames' callees `ks` valid, popping `ps` with theirs spliced in. -/
def RetKids (P : Core.Program) (rd : Reader) (σ : Val) (xs : List Stmt) (ks : List Tree) (ps : List Pop) : Prop :=
  ∃ es vs, walk σ xs = .ret es vs ∧ Tree.KidsValid P rd σ (calls es) ks ∧
    splice rd σ es (Tree.popsKids P rd ks) = ps

/-- **A valid node's body** returns with its callees, popping the node's entries. -/
theorem Tree.retKids {f : String} {bufs : List ℕ} {kids : List Tree} {fn : Fn} {args rets : List E}
    (hv : (Tree.node f σ bufs kids).Valid P rd args rets) (hf : P.find? f = some fn) :
    RetKids P rd σ fn.body kids ((Tree.node f σ bufs kids).pops P rd) := by
  obtain ⟨fn', hf', -, es, vs, hw, -, -, hk⟩ := hv
  rw [hf] at hf'
  cases hf'
  exact ⟨es, vs, hw, hk, (Tree.pops_node hf hw).symm⟩

theorem splice_split {e1 e2 : List Ev} {k1 k2 : List Tree} (h1 : Tree.KidsValid P rd σ (calls e1) k1) :
    splice rd σ (e1 ++ e2) (Tree.popsKids P rd (k1 ++ k2)) =
      splice rd σ e1 (Tree.popsKids P rd k1) ++ splice rd σ e2 (Tree.popsKids P rd k2) := by
  rw [popsKids_append]
  exact splice_append e1 e2 _ _ (by rw [length_popsKids, kidsValid_len h1])

/-- **A returning body splits** along a first block that cannot return. -/
theorem RetKids.split {xs ys : List Stmt} {ks : List Tree} {ps : List Pop} (h : RetKids P rd σ (xs ++ ys) ks ps)
    (hx : Stmt.noRetList xs = true) :
    ∃ k1 k2 p1 p2, ks = k1 ++ k2 ∧ ps = p1 ++ p2 ∧ BlockKids P rd σ xs k1 p1 ∧ RetKids P rd σ ys k2 p2 := by
  obtain ⟨es, vs, hw, hk, rfl⟩ := h
  obtain ⟨e1, e2, h1, h2, rfl⟩ := walk_append_ret hx hw
  rw [calls_append'] at hk
  obtain ⟨k1, k2, rfl, hk1, hk2⟩ := kidsValid_split hk
  exact ⟨k1, k2, _, _, rfl, splice_split hk1, ⟨e1, h1, hk1, rfl⟩, ⟨e2, vs, h2, hk2, rfl⟩⟩

/-- **A falling block splits.** -/
theorem BlockKids.split {xs ys : List Stmt} {ks : List Tree} {ps : List Pop} (h : BlockKids P rd σ (xs ++ ys) ks ps) :
    ∃ k1 k2 p1 p2, ks = k1 ++ k2 ∧ ps = p1 ++ p2 ∧ BlockKids P rd σ xs k1 p1 ∧ BlockKids P rd σ ys k2 p2 := by
  obtain ⟨es, hw, hk, rfl⟩ := h
  obtain ⟨e1, e2, h1, h2, rfl⟩ := walk_append_fall hw
  rw [calls_append'] at hk
  obtain ⟨k1, k2, rfl, hk1, hk2⟩ := kidsValid_split hk
  exact ⟨k1, k2, _, _, rfl, splice_split hk1, ⟨e1, h1, hk1, rfl⟩, ⟨e2, h2, hk2, rfl⟩⟩

theorem splice_mute_kids {S : String → Bool} (hS : MuteIn P S) {es : List Ev} {ks : List Tree}
    (hm : ∀ e ∈ es, Ev.Mute rd σ S e) (hk : Tree.KidsValid P rd σ (calls es) ks) :
    splice rd σ es (Tree.popsKids P rd ks) = [] := by
  rw [splice_mute es _ (fun e he => (hm e he).1) (by rw [length_popsKids, kidsValid_len hk]),
    popsKids_flatten_mute hS hk (calls_mem_of_mute hm)]

/-- **A mute block pops nothing.** -/
theorem BlockKids.mute {S : String → Bool} (hS : MuteIn P S) {xs : List Stmt} {ks : List Tree} {ps : List Pop}
    (hm : Stmt.muteList S xs = true) (h : BlockKids P rd σ xs ks ps) : ps = [] := by
  obtain ⟨es, hw, hk, rfl⟩ := h
  have := walk_mute (rd := rd) (σ := σ) xs hm
  rw [hw] at this
  exact splice_mute_kids hS this hk

/-- **A mute returning block pops nothing.** -/
theorem RetKids.mute {S : String → Bool} (hS : MuteIn P S) {xs : List Stmt} {ks : List Tree} {ps : List Pop}
    (hm : Stmt.muteList S xs = true) (h : RetKids P rd σ xs ks ps) : ps = [] := by
  obtain ⟨es, vs, hw, hk, rfl⟩ := h
  have := walk_mute (rd := rd) (σ := σ) xs hm
  rw [hw] at this
  exact splice_mute_kids hS this hk

/-- **An atom pops its entry.** -/
theorem BlockKids.atom {a : Atom} {ks : List Tree} {ps : List Pop} (h : BlockKids P rd σ [.atom a] ks ps) :
    ps = a.pops rd σ := by
  obtain ⟨es, hw, hk, rfl⟩ := h
  simp only [walk, walk1, Out.seq, Out.pre, List.append_nil, Out.fall.injEq] at hw
  subst hw
  match ks, hk with
  | [], _ => simp [splice]

/-- **A call pops its callee's entries.** -/
theorem BlockKids.call {f : String} {args rets : List V} {ks : List Tree} {ps : List Pop}
    (h : BlockKids P rd σ [.call f args rets] ks ps) :
    ∃ t : Tree, t.name = f ∧ t.Valid P rd (args.map σ) (rets.map σ) ∧ ps = t.pops P rd ∧ ks = [t] := by
  obtain ⟨es, hw, hk, rfl⟩ := h
  simp only [walk, walk1, Out.seq, Out.pre, List.append_nil, Out.fall.injEq] at hw
  subst hw
  match ks, hk with
  | [t], ⟨hn, hv, _⟩ => exact ⟨t, hn, hv, by simp [splice, Tree.popsKids], rfl⟩

theorem pick_fall {x : V} {args rets : List V} : ∀ (fs : List String) (j : ℕ) {es : List Ev},
    pick σ x args rets j fs = .fall es →
      ∃ i, ∃ hi : i < fs.length, σ x = ofK (addressOfIndex (j + i)) ∧ es = [.call fs[i] args rets]
  | [], _, _, h => by cases h
  | f :: fs, j, es, h => by
      unfold pick at h
      split_ifs at h with hx
      · cases h
        exact ⟨0, by simp, by simpa using hx, rfl⟩
      · obtain ⟨i, hi, hx', rfl⟩ := pick_fall fs (j + 1) h
        exact ⟨i + 1, by simpa using hi, by rw [hx']; congr 2; omega, rfl⟩

/-- **A dispatch pops its selected callee's entries.** -/
theorem BlockKids.dispatch {x : V} {fs : List String} {args rets : List V} {ks : List Tree} {ps : List Pop}
    (h : BlockKids P rd σ [.dispatch x fs args rets] ks ps) :
    ∃ (t : Tree) (i : ℕ), ∃ hi : i < fs.length, σ x = ofK (addressOfIndex i) ∧ t.name = fs[i] ∧
      t.Valid P rd (args.map σ) (rets.map σ) ∧ ps = t.pops P rd ∧ ks = [t] := by
  obtain ⟨es, hw, hk, rfl⟩ := h
  simp only [walk, walk1] at hw
  cases hp : pick σ x args rets 0 fs with
  | fall e =>
      rw [hp, Out.seq, Out.pre, List.append_nil] at hw
      cases hw
      obtain ⟨i, hi, hx, rfl⟩ := pick_fall fs 0 hp
      match ks, hk with
      | [t], ⟨hn, hv, _⟩ => exact ⟨t, i, hi, by simpa using hx, hn, hv, by simp [splice, Tree.popsKids], rfl⟩
  | ret _ _ => rw [hp, Out.seq] at hw; cases hw
  | stuck => rw [hp, Out.seq] at hw; cases hw

/-! ## Walking a body by positions -/

variable {l : List Stmt} {ks : List Tree} {ps : List Pop}

theorem drop_split (l : List Stmt) (a n : ℕ) : l.drop a = (l.drop a).take n ++ l.drop (a + n) := by
  rw [← List.drop_drop, List.take_append_drop]

theorem drop_cons {l : List Stmt} {a : ℕ} {s : Stmt} (h : l[a]? = some s) : l.drop a = [s] ++ l.drop (a + 1) := by
  obtain ⟨ha, e⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.drop_eq_getElem_cons ha, e]
  rfl

/-- **A mute block of the body pops nothing**: the walk moves past it. -/
theorem RetKids.dropMute {S : String → Bool} (hS : MuteIn P S) {a n : ℕ} (h : RetKids P rd σ (l.drop a) ks ps)
    (hb : (Stmt.noRetList ((l.drop a).take n) && Stmt.muteList S ((l.drop a).take n)) = true) :
    ∃ ks', RetKids P rd σ (l.drop (a + n)) ks' ps ∧ ∀ x ∈ ks', x ∈ ks := by
  simp only [Bool.and_eq_true] at hb
  rw [drop_split l a n] at h
  obtain ⟨k1, k2, p1, p2, rfl, rfl, h1, h2⟩ := h.split hb.1
  rw [h1.mute hS hb.2, List.nil_append]
  exact ⟨k2, h2, fun _ hx => List.mem_append_right _ hx⟩

/-- **An atom of the body pops its entry.** -/
theorem RetKids.dropAtom {a : ℕ} {w : Atom} (h : RetKids P rd σ (l.drop a) ks ps) (hs : l[a]? = some (.atom w)) :
    ∃ ks' ps', RetKids P rd σ (l.drop (a + 1)) ks' ps' ∧ ps = w.pops rd σ ++ ps' ∧ ∀ x ∈ ks', x ∈ ks := by
  rw [drop_cons hs] at h
  obtain ⟨k1, k2, p1, p2, rfl, rfl, h1, h2⟩ := h.split rfl
  exact ⟨k2, p2, h2, by rw [h1.atom], fun _ hx => List.mem_append_right _ hx⟩

/-- **A call of the body pops its callee's entries.** -/
theorem RetKids.dropCall {a : ℕ} {f : String} {args rets : List V} (h : RetKids P rd σ (l.drop a) ks ps)
    (hs : l[a]? = some (.call f args rets)) :
    ∃ (t : Tree) (ks' : List Tree) (ps' : List Pop), t.name = f ∧ t.Valid P rd (args.map σ) (rets.map σ) ∧ RetKids P rd σ (l.drop (a + 1)) ks' ps' ∧
      ps = t.pops P rd ++ ps' ∧ t ∈ ks ∧ ∀ x ∈ ks', x ∈ ks := by
  rw [drop_cons hs] at h
  obtain ⟨k1, k2, p1, p2, rfl, rfl, h1, h2⟩ := h.split rfl
  obtain ⟨t, hn, hv, rfl, rfl⟩ := h1.call
  exact ⟨t, k2, p2, hn, hv, h2, rfl, List.mem_cons_self, fun _ hx => List.mem_append_right _ hx⟩

/-- **A dispatch of the body pops its selected callee's entries.** -/
theorem RetKids.dropDispatch {a : ℕ} {x : V} {fs : List String} {args rets : List V}
    (h : RetKids P rd σ (l.drop a) ks ps) (hs : l[a]? = some (.dispatch x fs args rets)) :
    ∃ (t : Tree) (i : ℕ) (ks' : List Tree) (ps' : List Pop), ∃ hi : i < fs.length, σ x = ofK (addressOfIndex i) ∧ t.name = fs[i] ∧
      t.Valid P rd (args.map σ) (rets.map σ) ∧ RetKids P rd σ (l.drop (a + 1)) ks' ps' ∧ ps = t.pops P rd ++ ps' ∧
      t ∈ ks ∧ ∀ x ∈ ks', x ∈ ks := by
  rw [drop_cons hs] at h
  obtain ⟨k1, k2, p1, p2, rfl, rfl, h1, h2⟩ := h.split rfl
  obtain ⟨t, i, hi, hx, hn, hv, rfl, rfl⟩ := h1.dispatch
  exact ⟨t, i, k2, p2, hi, hx, hn, hv, h2, rfl, List.mem_cons_self, fun _ hx => List.mem_append_right _ hx⟩

/-- **The body's mute end pops nothing.** -/
theorem RetKids.endMute {S : String → Bool} (hS : MuteIn P S) {a : ℕ} (h : RetKids P rd σ (l.drop a) ks ps)
    (hb : Stmt.muteList S (l.drop a) = true) : ps = [] :=
  h.mute hS hb

end Kids

end
end LeanVM.Guest.Memory
