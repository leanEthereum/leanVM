/-
  LeanVM.Guest.Bridge.Track

  The tree track: a stack of call instances of the honest tree, each at a body position, whose moves follow the paths and keep the entries popped so far followed by the frames' remainders equal to the tree's pops.
-/

module

public import LeanVM.Guest.Pops
public import LeanVM.Guest.Memory
public import LeanVM.Guest.Memory.PopsNil

/-!
# The tree track

What the reference run does, read on the honest tree `T`, statement by statement. A frame of the track (`Ent`) is a placed call instance (`Inst`: its tree, frame, cursor, callees' frames and buffers' bases), its function, its **body position** (the statements left to run, `pos`), the events of its path already run and left (`pre`, `es`) and the buffers it has allocated (`nb`, counted apart: the compiler hoists allocations). Its calls made are those of `pre` (`Ent.nc`), so its next callee is `kids[nc]`.

`EntOk`: the instance is one of `Is` (the honest instances), a node, and its path splits at the position: `walk σ body = .ret (pre ++ es) vs` and `walk σ pos = .ret es vs`. A frame's **remainder** (`Ent.rem`) is what is left of its pops: its events left, its callees not yet called spliced in.

`Move`: one statement at the top frame's position: an atom (popping its entry), a branch (to the side `σ` takes), a `match` (to the arm the path takes), a `callIf` not taken (a phantom), a call, a taken `callIf` or a dispatch (pushing the callee, the instance at `kids[nc]`, at its body), a loop's tail call (the callee replacing the frame), a return (popping), a buffer allocated. `TrackOk Is T done st`: every frame `EntOk`, and `done ++ remS st = T.pops`. `TrackOk.move`: moves keep it; `trackOk_init`: `main`'s frame at its body, nothing done.

What it gives at the top frame: `pops_next`, a witness hint at the position is the entry after `done` in `T.pops`, so (`stream_next`) the next of its stream wherever pushes agree with the pops stream by stream; `alloc_at`, the `nb`-th allocation of the path lands at the instance's `nb`-th buffer base, the cursor plus the sizes before it.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## Paths -/

theorem out_pre_nil : ∀ o : Out, o.pre [] = o
  | .fall _ | .ret _ _ | .stuck => by simp [Out.pre]

theorem out_pre_pre (a b : List Ev) : ∀ o : Out, (o.pre b).pre a = o.pre (a ++ b)
  | .fall _ | .ret _ _ | .stuck => by simp [Out.pre]

theorem out_seq_pre (es : List Ev) (k : Out) : ∀ o : Out, (o.pre es).seq k = (o.seq k).pre es
  | .fall _ => by cases k <;> simp [Out.pre, Out.seq, List.append_assoc]
  | .ret _ _ | .stuck => by simp [Out.pre, Out.seq]

theorem out_seq_assoc (k1 k2 : Out) : ∀ o : Out, (o.seq k1).seq k2 = o.seq (k1.seq k2)
  | .fall es => out_seq_pre es k2 k1
  | .ret _ _ | .stuck => rfl

theorem walk_append (σ : Val) : ∀ xs ys : List Stmt, walk σ (xs ++ ys) = (walk σ xs).seq (walk σ ys)
  | [], ys => by simp only [List.nil_append, walk, Out.seq, out_pre_nil]
  | s :: xs, ys => by rw [List.cons_append, walk, walk, walk_append σ xs ys, out_seq_assoc]

theorem seq_eq_ret {o k : Out} {es : List Ev} {vs : List V} (h : o.seq k = .ret es vs) :
    (∃ es1 es2, o = .fall es1 ∧ k = .ret es2 vs ∧ es = es1 ++ es2) ∨ o = .ret es vs := by
  cases o with
  | fall es1 =>
    left
    cases k with
    | fall _ => simp [Out.seq, Out.pre] at h
    | ret es2 vs2 =>
      simp only [Out.seq, Out.pre, Out.ret.injEq] at h
      exact ⟨es1, es2, rfl, by rw [h.2], h.1.symm⟩
    | stuck => simp [Out.seq, Out.pre] at h
  | ret => right; simpa [Out.seq] using h
  | stuck => simp [Out.seq] at h

theorem pre_eq_ret {o : Out} {pre es : List Ev} {vs : List V} (h : o.pre pre = .ret es vs) :
    ∃ es', o = .ret es' vs ∧ es = pre ++ es' := by
  cases o with
  | ret es' vs' =>
    simp only [Out.pre, Out.ret.injEq] at h
    exact ⟨es', by rw [h.2], h.1.symm⟩
  | _ => simp [Out.pre] at h

section Walk

variable {σ : Val}

theorem walk_atom_cons (a : Atom) (ps : List Stmt) : walk σ (.atom a :: ps) = (walk σ ps).pre [.atom a] := by
  rw [walk, walk1, Out.seq]

theorem walk_ite_cons (c : V) (z n ps : List Stmt) :
    walk σ (.ite c z n :: ps) = (walk σ ((if σ c = 0 then z else n) ++ ps)).pre [.inK c] := by
  rw [walk, walk1, out_seq_pre, walk_append]
  split_ifs <;> rfl

theorem walk_call_cons (f : String) (args rets : List V) (ps : List Stmt) :
    walk σ (.call f args rets :: ps) = (walk σ ps).pre [.call f args rets] := by
  rw [walk, walk1, Out.seq]

theorem walk_callIf_cons (c : V) (f : String) (args : List V) (ps : List Stmt) :
    walk σ (.callIf c f args :: ps) =
      (walk σ ps).pre [.inK c, if σ c = 0 then .skip f args else .call f args []] := by
  rw [walk, walk1, Out.seq]

theorem walk_ret_cons (vs : List V) (ps : List Stmt) : walk σ (.ret vs :: ps) = .ret [] vs := by
  rw [walk, walk1, Out.seq]

theorem walk_match_cons (x : V) (arms : List (List Stmt)) (ps : List Stmt) :
    walk σ (.match_ x arms :: ps) = (walkArms σ x 0 arms).seq (walk σ ps) := by
  rw [walk, walk1]

theorem walk_dispatch_cons (x : V) (fs : List String) (args rets : List V) (ps : List Stmt) :
    walk σ (.dispatch x fs args rets :: ps) = (pick σ x args rets 0 fs).seq (walk σ ps) := by
  rw [walk, walk1]

/-- **A `match` takes the arm of its selector**, `g^k`. -/
theorem walkArms_of (x : V) : ∀ (arms : List (List Stmt)) (j k : ℕ) (hk : k < arms.length),
    σ x = ofK (addressOfIndex (j + k)) → j + k < 2 ^ 64 - 1 → walkArms σ x j arms = walk σ arms[k]
  | [], _, _, hk, _, _ => absurd hk (Nat.not_lt_zero _)
  | a :: as, j, k, hk, hx, hlt => by
    rw [walkArms]
    cases k with
    | zero => rw [ite_eq_left (by simpa using hx)]; rfl
    | succ k =>
      rw [ite_eq_right (fun h ↦ by
        have := gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
          (ofK_injective (h.symm.trans hx))
        omega)]
      exact walkArms_of x as (j + 1) k (by simpa using hk) (by rw [hx]; congr 2; omega) (by omega)

/-- **A dispatch calls the callee of its selector**, `g^i`. -/
theorem pick_of (x : V) (args rets : List V) : ∀ (fs : List String) (j i : ℕ) (hi : i < fs.length),
    σ x = ofK (addressOfIndex (j + i)) → j + i < 2 ^ 64 - 1 →
      pick σ x args rets j fs = .fall [.call fs[i] args rets]
  | [], _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | f :: fs, j, i, hi, hx, hlt => by
    rw [pick]
    cases i with
    | zero => rw [ite_eq_left (by simpa using hx)]; rfl
    | succ i =>
      rw [ite_eq_right (fun h ↦ by
        have := gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
          (ofK_injective (h.symm.trans hx))
        omega)]
      exact pick_of x args rets fs (j + 1) i (by simpa using hi) (by rw [hx]; congr 2; omega) (by omega)

end Walk

/-! ## Splicing -/

theorem calls_append' (es es' : List Ev) : calls (es ++ es') = calls es ++ calls es' :=
  List.filterMap_append

theorem popsKids_eq_map (P : Core.Program) (rd : Reader) :
    ∀ ks : List Tree, Tree.popsKids P rd ks = ks.map (Tree.pops P rd)
  | [] => by rw [Tree.popsKids]; rfl
  | k :: ks => by rw [Tree.popsKids, popsKids_eq_map P rd ks, List.map_cons]

/-- Events in turn splice their callees in turn. -/
theorem splice_append (rd : Reader) (σ : Val) : ∀ (es1 es2 : List Ev) (ks : List (List Pop)),
    splice rd σ (es1 ++ es2) ks =
      splice rd σ es1 (ks.take (calls es1).length) ++ splice rd σ es2 (ks.drop (calls es1).length)
  | [], es2, ks => by simp [splice, calls]
  | .atom a :: es1, es2, ks => by
    simp only [List.cons_append, splice, calls, List.filterMap_cons, Ev.call?, List.append_assoc]
    exact congrArg _ (splice_append rd σ es1 es2 ks)
  | .inK _ :: es1, es2, ks => by
    simp only [List.cons_append, splice, calls, List.filterMap_cons, Ev.call?]
    exact splice_append rd σ es1 es2 ks
  | .call .. :: es1, es2, ks => by
    simp only [List.cons_append, splice, calls, List.filterMap_cons, Ev.call?, List.length_cons,
      List.append_assoc]
    rw [splice_append rd σ es1 es2 ks.tail]
    cases ks <;> simp [List.take_succ_cons, List.drop_succ_cons, calls]
  | .skip .. :: es1, es2, ks => by
    simp only [List.cons_append, splice, calls, List.filterMap_cons, Ev.call?, List.length_cons,
      List.append_assoc]
    rw [splice_append rd σ es1 es2 ks.tail]
    cases ks <;> simp [List.take_succ_cons, List.drop_succ_cons, calls]

theorem kidsValid_drop {P : Core.Program} {rd : Reader} {σ : Val} :
    ∀ {cs1 cs2 : List Call} {ks : List Tree}, Tree.KidsValid P rd σ (cs1 ++ cs2) ks →
      Tree.KidsValid P rd σ cs2 (ks.drop cs1.length)
  | [], _, _, h => h
  | _ :: _, _, [], h => h.elim
  | _ :: cs1, _, _ :: ks, h => by
    rw [List.length_cons, List.drop_succ_cons]
    exact kidsValid_drop (cs1 := cs1) h.2.2

/-- Atoms, then the closing `ret []`. -/
theorem walk_atoms_ret (σ : Val) : ∀ as : List Atom,
    walk σ (as.map Stmt.atom ++ [.ret []]) = .ret (as.map Ev.atom) []
  | [] => by simp only [List.map_nil, List.nil_append]; exact walk_ret_cons [] []
  | a :: as => by
    rw [List.map_cons, List.cons_append, walk_atom_cons, walk_atoms_ret σ as]
    rfl

/-- Atoms that pop nothing splice to nothing. -/
theorem splice_atoms_nil {rd : Reader} {σ : Val} : ∀ {as : List Atom}, (∀ a ∈ as, ∀ rd σ, a.pops rd σ = []) →
    ∀ ks : List (List Pop), splice rd σ (as.map Ev.atom) ks = []
  | [], _, ks => by simp [splice]
  | a :: as, h, ks => by
    simp only [List.map_cons, splice, h a List.mem_cons_self, List.nil_append]
    exact splice_atoms_nil (fun b hb ↦ h b (List.mem_cons_of_mem _ hb)) ks

/-! ## Frames -/

/-- **A frame of the track**: a placed instance, its function, its body position, the events of its
path run and left, the buffers it has allocated. -/
structure Ent where
  I : Inst
  fn : Fn
  pos : List Stmt
  pre : List Ev
  es : List Ev
  nb : ℕ

/-- The frame's valuation. -/
abbrev Ent.σ (e : Ent) : Val := e.I.t.val

/-- The calls the frame has made. -/
def Ent.nc (e : Ent) : ℕ := (calls e.pre).length

/-- The frame past `k` events, at position `ps`. -/
def Ent.adv (e : Ent) (ps : List Stmt) (k : ℕ) : Ent :=
  { e with pos := ps, pre := e.pre ++ e.es.take k, es := e.es.drop k }

/-- The frame at entry of instance `J` of function `fn`. -/
noncomputable def Ent.enter (P : Core.Program) (J : Inst) (fn : Fn) : Ent :=
  ⟨J, fn, fn.body, [], J.t.events P, 0⟩

variable (P : Core.Program) (rd : Reader)

/-- **What is left of a frame's pops**: its events left, its callees not yet called spliced in. -/
noncomputable def Ent.rem (e : Ent) : List Pop :=
  splice rd e.σ e.es ((e.I.t.kids.drop e.nc).map (Tree.pops P rd))

/-- What is left of the stack's pops, top first. -/
noncomputable def remS (st : List Ent) : List Pop := st.flatMap (Ent.rem P rd)

/-- **A frame on the honest tree**: an instance of `Is`, a node, its path splitting at the
position. -/
structure EntOk (Is : List Inst) (e : Ent) : Prop where
  mem : e.I ∈ Is
  node : ∃ f bufs kids, e.I.t = .node f e.σ bufs kids
  find : P.find? e.I.t.name = some e.fn
  path : ∃ vs, walk e.σ e.fn.body = .ret (e.pre ++ e.es) vs ∧ walk e.σ e.pos = .ret e.es vs
  kids : ∃ rv, Tree.KidsValid P rv e.σ (calls (e.pre ++ e.es)) e.I.t.kids

/-- **The tree track's invariant**: every frame on the honest tree, and the entries done followed
by the frames' remainders the tree's pops. -/
structure TrackOk (Is : List Inst) (T : Tree) (done : List Pop) (st : List Ent) : Prop where
  ents : ∀ e ∈ st, EntOk P Is e
  pops : done ++ remS P rd st = T.pops P rd


/-- **One move of the tree track**, at the top frame's position. -/
inductive Move (Is : List Inst) : List Pop × List Ent → List Pop × List Ent → Prop
  | atom {done : List Pop} {e : Ent} {st : List Ent} {a : Atom} {ps : List Stmt} :
      e.pos = .atom a :: ps → Move Is (done, e :: st) (done ++ a.pops rd e.σ, e.adv ps 1 :: st)
  | ite {done : List Pop} {e : Ent} {st : List Ent} {c : V} {z n ps : List Stmt} :
      e.pos = .ite c z n :: ps →
      Move Is (done, e :: st) (done, e.adv ((if e.σ c = 0 then z else n) ++ ps) 1 :: st)
  | arm {done : List Pop} {e : Ent} {st : List Ent} {x : V} {arms : List (List Stmt)}
      {ps : List Stmt} {k : ℕ} (hk : k < arms.length) :
      e.pos = .match_ x arms :: ps → walkArms e.σ x 0 arms = walk e.σ arms[k] →
      Move Is (done, e :: st) (done, e.adv (arms[k] ++ ps) 0 :: st)
  | skip {done : List Pop} {e : Ent} {st : List Ent} {c : V} {f : String} {args : List V}
      {ps : List Stmt} :
      e.pos = .callIf c f args :: ps → e.σ c = 0 → Move Is (done, e :: st) (done, e.adv ps 2 :: st)
  | call {done : List Pop} {e : Ent} {st : List Ent} {f : String} {args rets : List V}
      {ps : List Stmt} {J : Inst} {fn : Fn} :
      e.pos = .call f args rets :: ps → J ∈ Is → e.I.t.kids[e.nc]? = some J.t →
      e.I.kidFps[e.nc]? = some J.fp → P.find? J.t.name = some fn →
      Move Is (done, e :: st) (done, Ent.enter P J fn :: e.adv ps 1 :: st)
  | callIf {done : List Pop} {e : Ent} {st : List Ent} {c : V} {f : String} {args : List V}
      {ps : List Stmt} {J : Inst} {fn : Fn} :
      e.pos = .callIf c f args :: ps → e.σ c ≠ 0 → J ∈ Is → e.I.t.kids[e.nc]? = some J.t →
      e.I.kidFps[e.nc]? = some J.fp → P.find? J.t.name = some fn →
      Move Is (done, e :: st) (done, Ent.enter P J fn :: e.adv ps 2 :: st)
  | tail {done : List Pop} {e : Ent} {st : List Ent} {c : V} {f : String} {args : List V}
      {ps : List Stmt} {J : Inst} {fn : Fn} :
      e.pos = .callIf c f args :: ps → e.σ c ≠ 0 →
      (∃ as : List Atom, (∀ a ∈ as, ∀ rd σ, a.pops rd σ = []) ∧ ps = as.map Stmt.atom ++ [.ret []]) → J ∈ Is →
      e.I.t.kids[e.nc]? = some J.t → e.I.kidFps[e.nc]? = some J.fp → P.find? J.t.name = some fn →
      Move Is (done, e :: st) (done, Ent.enter P J fn :: st)
  | dispatch {done : List Pop} {e : Ent} {st : List Ent} {x : V} {fs : List String}
      {args rets : List V} {ps : List Stmt} {i : ℕ} {J : Inst} {fn : Fn} (hi : i < fs.length) :
      e.pos = .dispatch x fs args rets :: ps →
      pick e.σ x args rets 0 fs = .fall [.call fs[i] args rets] →
      J ∈ Is → e.I.t.kids[e.nc]? = some J.t → e.I.kidFps[e.nc]? = some J.fp →
      P.find? J.t.name = some fn →
      Move Is (done, e :: st) (done, Ent.enter P J fn :: e.adv ps 1 :: st)
  | ret {done : List Pop} {e : Ent} {st : List Ent} {vs : List V} {ps : List Stmt} :
      e.pos = .ret vs :: ps → Move Is (done, e :: st) (done, st)
  | alloc {done : List Pop} {e : Ent} {st : List Ent} :
      Move Is (done, e :: st) (done, { e with nb := e.nb + 1 } :: st)

variable {P rd}

/-! ## The moves keep the invariant -/

section Keep

variable {Is : List Inst}

theorem EntOk.kv {e : Ent} (h : EntOk P Is e) :
    ∃ rv, Tree.KidsValid P rv e.σ (calls e.es) (e.I.t.kids.drop e.nc) := by
  obtain ⟨rv, h⟩ := h.kids
  rw [calls_append'] at h
  exact ⟨rv, kidsValid_drop h⟩

theorem EntOk.adv {e : Ent} (h : EntOk P Is e) {ps : List Stmt} {k : ℕ}
    (hw : ∀ vs, walk e.σ e.pos = .ret e.es vs → walk e.σ ps = .ret (e.es.drop k) vs) :
    EntOk P Is (e.adv ps k) := by
  obtain ⟨vs, h1, h2⟩ := h.path
  have hpe : e.pre ++ e.es.take k ++ e.es.drop k = e.pre ++ e.es := by
    rw [List.append_assoc, List.take_append_drop]
  exact ⟨h.mem, h.node, h.find, ⟨vs, by simp only [Ent.adv]; rw [hpe]; exact h1, hw vs h2⟩,
    by simp only [Ent.adv]; rw [hpe]; exact h.kids⟩

/-- A frame's remainder past the events `evs`: their entries, the callees they call spliced in,
then the rest. -/
theorem Ent.rem_split (e : Ent) (ps : List Stmt) {evs rest : List Ev} (he : e.es = evs ++ rest) :
    e.rem P rd = splice rd e.σ evs
        (((e.I.t.kids.drop e.nc).map (Tree.pops P rd)).take (calls evs).length) ++
      (e.adv ps evs.length).rem P rd := by
  have hnc : (e.adv ps evs.length).nc = e.nc + (calls evs).length := by
    simp only [Ent.nc, Ent.adv, he, List.take_left, calls_append', List.length_append]
  have hes : (e.adv ps evs.length).es = rest := by simp only [Ent.adv, he, List.drop_left]
  rw [Ent.rem, Ent.rem, he, splice_append, hes, hnc, ← List.drop_drop]
  simp only [List.map_drop]
  rfl

/-- The callee at the head of the frame's calls left. -/
theorem EntOk.head_kid {e : Ent} (h : EntOk P Is e) {c : Call} {cs : List Call}
    (hc : calls e.es = c :: cs) :
    ∃ k, e.I.t.kids.drop e.nc = k :: e.I.t.kids.drop (e.nc + 1) ∧ e.I.t.kids[e.nc]? = some k ∧
      ∃ rv, (if c.taken then k.Valid P rv (c.args.map e.σ) (c.rets.map e.σ)
        else (∃ f σ', k = .phantom f σ') ∧ Phantom P k (c.args.map e.σ)) := by
  obtain ⟨rv, hkv⟩ := h.kv
  rw [hc] at hkv
  cases hd : e.I.t.kids.drop e.nc with
  | nil => rw [hd] at hkv; exact hkv.elim
  | cons k ks =>
    rw [hd] at hkv
    refine ⟨k, ?_, ?_, rv, hkv.2.1⟩
    · rw [← List.drop_drop, hd]; rfl
    · have := congrArg List.head? hd
      rwa [List.head?_drop, List.head?_cons] at this

/-- **A callee entered**: its frame at its body is on the honest tree, its remainder its pops. -/
theorem enter_ok {J : Inst} {fn : Fn} (hJ : J ∈ Is) (hf : P.find? J.t.name = some fn)
    {rv : Reader} {args rets : List E} (hv : J.t.Valid P rv args rets) :
    EntOk P Is (Ent.enter P J fn) ∧ (Ent.enter P J fn).rem P rd = J.t.pops P rd := by
  rcases hJt : J.t with ⟨f', σ', bufs', kids'⟩ | ⟨f', σ'⟩
  · rw [hJt] at hv hf
    obtain ⟨fn', hf', -, es', vs', hw', -, -, hkv'⟩ := hv
    simp only [Tree.name] at hf
    obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
    have hev : (Memory.Tree.node f' σ' bufs' kids').events P = es' := events_node hf' hw'
    refine ⟨⟨hJ, ⟨f', bufs', kids', by simp [Ent.enter, Ent.σ, hJt, Tree.val]⟩,
      by simpa [Ent.enter, hJt, Tree.name] using hf', ⟨vs', ?_, ?_⟩, ?_⟩, ?_⟩
    · simp only [Ent.enter, Ent.σ, hJt, Tree.val, hev, List.nil_append]; exact hw'
    · simp only [Ent.enter, Ent.σ, hJt, Tree.val, hev]; exact hw'
    · simp only [Ent.enter, Ent.σ, hJt, Tree.val, Tree.kids, hev, List.nil_append]; exact ⟨rv, hkv'⟩
    · simp only [Ent.rem, Ent.enter, Ent.σ, Ent.nc, hJt, Tree.val, Tree.kids, calls, List.filterMap_nil,
        List.length_nil, List.drop_zero]
      rw [Tree.pops, popsKids_eq_map]
  · rw [hJt] at hv; exact hv.elim

private theorem drop_of {es pre es' : List Ev} (h : es = pre ++ es') : es = pre ++ es.drop pre.length := by
  rw [h, List.drop_left]

/-- The top frame past the events `evs` of its first statement. -/
private theorem top_adv {T : Tree} {done : List Pop} {e : Ent} {st : List Ent}
    (h : TrackOk P rd Is T done (e :: st)) {ps : List Stmt} {evs : List Ev}
    (hw : ∀ vs, walk e.σ e.pos = .ret e.es vs → ∃ rest, e.es = evs ++ rest ∧ walk e.σ ps = .ret rest vs) :
    e.es = evs ++ e.es.drop evs.length ∧ EntOk P Is (e.adv ps evs.length) := by
  have he := h.ents e List.mem_cons_self
  obtain ⟨vs, -, h2⟩ := he.path
  obtain ⟨rest, h3, -⟩ := hw vs h2
  refine ⟨drop_of h3, he.adv fun vs' h' ↦ ?_⟩
  obtain ⟨rest', h3', h4'⟩ := hw vs' h'
  rw [h3', List.drop_left]
  exact h4'

theorem trackOk_cons {T : Tree} {done done' : List Pop} {e e' : Ent} {st : List Ent}
    (h : TrackOk P rd Is T done (e :: st)) (he' : EntOk P Is e')
    (hr : done ++ e.rem P rd = done' ++ e'.rem P rd) : TrackOk P rd Is T done' (e' :: st) := by
  refine ⟨fun x hx ↦ ?_, ?_⟩
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact he'
    · exact h.ents x (List.mem_cons_of_mem _ hx)
  · have := h.pops
    simp only [remS, List.flatMap_cons] at this ⊢
    rw [← List.append_assoc, ← hr, List.append_assoc]
    exact this

theorem trackOk_push {T : Tree} {done : List Pop} {e e' J : Ent} {st : List Ent}
    (h : TrackOk P rd Is T done (e :: st)) (he' : EntOk P Is e') (hJ : EntOk P Is J)
    (hr : e.rem P rd = J.rem P rd ++ e'.rem P rd) : TrackOk P rd Is T done (J :: e' :: st) := by
  refine ⟨fun x hx ↦ ?_, ?_⟩
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact hJ
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact he'
      · exact h.ents x (List.mem_cons_of_mem _ hx)
  · have := h.pops
    simp only [remS, List.flatMap_cons] at this ⊢
    rw [hr, List.append_assoc] at this
    exact this

/-- A taken call's callee entered at the head of the calls left. -/
private theorem call_rem {e : Ent} (h : EntOk P Is e) {ps : List Stmt} {evs rest : List Ev}
    {c : Call} (he : e.es = evs ++ rest) (hc : calls evs = [c]) (ht : c.taken = true) {J : Inst} {fn : Fn}
    (hJ : J ∈ Is) (hk : e.I.t.kids[e.nc]? = some J.t) (hf : P.find? J.t.name = some fn)
    (hsp : ∀ k, splice rd e.σ evs [k] = k) :
    EntOk P Is (Ent.enter P J fn) ∧
      e.rem P rd = (Ent.enter P J fn).rem P rd ++ (e.adv ps evs.length).rem P rd := by
  have hc' : calls e.es = c :: calls rest := by rw [he, calls_append', hc]; rfl
  obtain ⟨k, hd, hk', rv, hv⟩ := h.head_kid hc'
  rw [hk] at hk'
  obtain rfl := Option.some.inj hk'
  rw [ite_eq_left ht] at hv
  obtain ⟨hok, hrem⟩ := enter_ok hJ hf hv
  refine ⟨hok, ?_⟩
  rw [e.rem_split ps he, hd, hc, hrem]
  simp only [List.map_cons, List.length_singleton, List.take_succ_cons, List.take_zero]
  rw [hsp]

/-- **The moves keep the invariant.** -/
theorem TrackOk.move {T : Tree} {s s' : List Pop × List Ent} (h : TrackOk P rd Is T s.1 s.2)
    (hm : Move P rd Is s s') : TrackOk P rd Is T s'.1 s'.2 := by
  cases hm with
  | @atom done e st a ps hpos =>
    obtain ⟨he, hok⟩ := top_adv (evs := [.atom a]) (ps := ps) h fun vs hw ↦ by
      rw [hpos, walk_atom_cons] at hw
      obtain ⟨es', h1, h2⟩ := pre_eq_ret hw
      exact ⟨es', h2, h1⟩
    refine trackOk_cons h hok ?_
    rw [e.rem_split ps he]
    simp [splice]
  | @ite done e st c z n ps hpos =>
    obtain ⟨he, hok⟩ := top_adv (evs := [.inK c]) (ps := (if e.σ c = 0 then z else n) ++ ps) h
      fun vs hw ↦ by
        rw [hpos, walk_ite_cons] at hw
        obtain ⟨es', h1, h2⟩ := pre_eq_ret hw
        exact ⟨es', h2, h1⟩
    refine trackOk_cons h hok ?_
    rw [e.rem_split ((if e.σ c = 0 then z else n) ++ ps) he]
    simp [splice]
  | @arm done e st x arms ps k hk hpos hwa =>
    obtain ⟨he, hok⟩ := top_adv (evs := []) (ps := arms[k] ++ ps) h fun vs hw ↦ by
      rw [hpos, walk_match_cons, hwa, ← walk_append] at hw
      exact ⟨e.es, rfl, hw⟩
    refine trackOk_cons h hok ?_
    rw [e.rem_split (arms[k] ++ ps) he]
    simp [splice]
  | @skip done e st c f args ps hpos h0 =>
    obtain ⟨he, hok⟩ := top_adv (evs := [.inK c, .skip f args]) (ps := ps) h fun vs hw ↦ by
      rw [hpos, walk_callIf_cons, ite_eq_left h0] at hw
      obtain ⟨es', h1, h2⟩ := pre_eq_ret hw
      exact ⟨es', h2, h1⟩
    refine trackOk_cons h hok ?_
    have hc' : calls e.es = ⟨f, args, [], false⟩ :: calls (e.es.drop 2) := by
      rw [he]; rfl
    obtain ⟨k, hd, -, _, hv⟩ := (h.ents e List.mem_cons_self).head_kid hc'
    obtain ⟨⟨f', σ', rfl⟩, -⟩ := hv
    rw [e.rem_split ps he, hd]
    simp [splice, pops_phantom, calls, Ev.call?, List.filterMap_cons]
  | @call done e st f args rets ps J fn hpos hJ hk _ hf =>
    obtain ⟨he, hok⟩ := top_adv (evs := [.call f args rets]) (ps := ps) h fun vs hw ↦ by
      rw [hpos, walk_call_cons] at hw
      obtain ⟨es', h1, h2⟩ := pre_eq_ret hw
      exact ⟨es', h2, h1⟩
    obtain ⟨hJ', hr⟩ := call_rem (h.ents e List.mem_cons_self) (ps := ps) he rfl rfl hJ hk hf
      fun k ↦ by simp [splice]
    exact trackOk_push h hok hJ' hr
  | @callIf done e st c f args ps J fn hpos h0 hJ hk _ hf =>
    obtain ⟨he, hok⟩ := top_adv (evs := [.inK c, .call f args []]) (ps := ps) h fun vs hw ↦ by
      rw [hpos, walk_callIf_cons, ite_eq_right h0] at hw
      obtain ⟨es', h1, h2⟩ := pre_eq_ret hw
      exact ⟨es', h2, h1⟩
    obtain ⟨hJ', hr⟩ := call_rem (h.ents e List.mem_cons_self) (ps := ps) he rfl rfl hJ hk hf
      fun k ↦ by simp [splice]
    exact trackOk_push h hok hJ' hr
  | @tail done e st c f args ps J fn hpos h0 hnil hJ hk _ hf =>
    obtain ⟨he, hok⟩ := top_adv (evs := [.inK c, .call f args []]) (ps := ps) h fun vs hw ↦ by
      rw [hpos, walk_callIf_cons, ite_eq_right h0] at hw
      obtain ⟨es', h1, h2⟩ := pre_eq_ret hw
      exact ⟨es', h2, h1⟩
    obtain ⟨hJ', hr⟩ := call_rem (h.ents e List.mem_cons_self) (ps := ps) he rfl rfl hJ hk hf
      fun k ↦ by simp [splice]
    refine trackOk_cons h hJ' ?_
    obtain ⟨as, has, rfl⟩ := hnil
    have hok2 := hok
    rw [show [Ev.inK c, Ev.call f args []].length = 2 from rfl] at hok2
    have : (e.adv (as.map Stmt.atom ++ [.ret []]) 2).rem P rd = [] := by
      obtain ⟨vs, -, hw⟩ := hok2.path
      change walk e.σ (as.map Stmt.atom ++ [.ret []]) = .ret (e.es.drop 2) vs at hw
      rw [walk_atoms_ret] at hw
      change splice rd e.σ (e.es.drop 2) _ = []
      rw [← (Out.ret.inj hw).1]
      exact splice_atoms_nil has _
    rw [hr, show [Ev.inK c, Ev.call f args []].length = 2 from rfl, this, List.append_nil]
  | @dispatch done e st x fs args rets ps i J fn hi hpos hp hJ hk _ hf =>
    obtain ⟨he, hok⟩ := top_adv (evs := [.call fs[i] args rets]) (ps := ps) h fun vs hw ↦ by
      rw [hpos, walk_dispatch_cons, hp, Out.seq] at hw
      obtain ⟨es', h1, h2⟩ := pre_eq_ret hw
      exact ⟨es', h2, h1⟩
    obtain ⟨hJ', hr⟩ := call_rem (h.ents e List.mem_cons_self) (ps := ps) he rfl rfl hJ hk hf
      fun k ↦ by simp [splice]
    exact trackOk_push h hok hJ' hr
  | @ret done e st vs ps hpos =>
    have he := h.ents e List.mem_cons_self
    obtain ⟨vs', -, h2⟩ := he.path
    rw [hpos, walk_ret_cons] at h2
    have hnil : e.es = [] := (Out.ret.inj h2).1.symm
    refine ⟨fun x hx ↦ h.ents x (List.mem_cons_of_mem _ hx), ?_⟩
    have := h.pops
    simp only [remS, List.flatMap_cons, Ent.rem, hnil, splice, List.nil_append] at this ⊢
    exact this
  | @alloc done e st =>
    have he := h.ents e List.mem_cons_self
    exact trackOk_cons h ⟨he.mem, he.node, he.find, he.path, he.kids⟩ rfl

/-- Moves in turn keep the invariant. -/
theorem TrackOk.moves {T : Tree} {s s' : List Pop × List Ent} (h : TrackOk P rd Is T s.1 s.2)
    (hm : Relation.ReflTransGen (Move P rd Is) s s') : TrackOk P rd Is T s'.1 s'.2 := by
  induction hm with
  | refl => exact h
  | tail _ hm ih => exact ih.move hm

/-- **The track starts at `main`'s body**, nothing done. -/
theorem trackOk_init {I : Inst} {fn : Fn} (hI : I ∈ Is) (hf : P.find? I.t.name = some fn)
    {rv : Reader} {args rets : List E} (hv : I.t.Valid P rv args rets) :
    TrackOk P rd Is I.t [] [Ent.enter P I fn] := by
  obtain ⟨hok, hrem⟩ := enter_ok (rd := rd) hI hf hv
  refine ⟨fun x hx ↦ by rw [List.mem_singleton.mp hx]; exact hok, ?_⟩
  simp only [remS, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, hrem]

/-! ## What the track gives at the top frame -/

/-- **The entry a witness hint pops is the next of the tree's**: an atom at the top frame's position
pops the entries after those done. -/
theorem TrackOk.pops_next {T : Tree} {done : List Pop} {e : Ent} {st : List Ent}
    (h : TrackOk P rd Is T done (e :: st)) {a : Atom} {ps : List Stmt} (hpos : e.pos = .atom a :: ps) :
    T.pops P rd = done ++ a.pops rd e.σ ++ remS P rd (e.adv ps 1 :: st) :=
  (h.move (s' := (done ++ a.pops rd e.σ, e.adv ps 1 :: st)) (.atom hpos)).pops.symm

/-- **The next entry of a stream**: where the pushes agree with the pops stream by stream, the entry
after `done` in the pops is its stream's, past as many as `done` has of it. -/
theorem stream_next {pops qs done rest : List Pop} {p : Pop} (hs : SameStreams pops qs)
    (h : pops = done ++ p :: rest) :
    (qs.filter (·.1 == p.1))[(done.filter (·.1 == p.1)).length]? = some p := by
  rw [← hs p.1, h, List.filter_append, List.filter_cons, ite_eq_left (beq_self_eq_true p.1),
    List.getElem?_append_right le_rfl, Nat.sub_self]
  rfl

/-- **A witness hint at the top frame pops the next entry of its stream**, where the pushes agree
with the tree's pops stream by stream. -/
theorem TrackOk.witness_next {T : Tree} {done : List Pop} {e : Ent} {st : List Ent}
    (h : TrackOk P rd Is T done (e :: st)) {s : String} {dst : Dest} {ps : List Stmt}
    (hpos : e.pos = .atom (.hint (.witness s dst)) :: ps) {qs : List Pop} (hs : SameStreams (T.pops P rd) qs) :
    (qs.filter (·.1 == s))[(done.filter (·.1 == s)).length]? = some (s, dst.words rd e.σ) := by
  have := h.pops_next hpos
  simp only [Atom.pops, Core.Hint.pops, List.append_assoc, List.singleton_append] at this
  exact stream_next hs this

/-- **The callee of a call left**: an instance at the frame's next callee frame. -/
theorem EntOk.callee {e : Ent} (h : EntOk P Is e)
    (hIs : ∀ I ∈ Is, ∀ (i : ℕ) (k : Tree), I.t.kids[i]? = some k → ∃ J ∈ Is, J.t = k ∧ I.kidFps[i]? = some J.fp)
    {c : Call} {cs : List Call} (hc : calls e.es = c :: cs) (ht : c.taken = true) :
    ∃ J ∈ Is, ∃ fn, e.I.t.kids[e.nc]? = some J.t ∧ e.I.kidFps[e.nc]? = some J.fp ∧
      P.find? J.t.name = some fn := by
  obtain ⟨k, -, hk, _, hv⟩ := h.head_kid hc
  obtain ⟨J, hJ, rfl, hfp⟩ := hIs e.I h.mem e.nc k hk
  rw [ite_eq_left ht] at hv
  rcases hJt : J.t with ⟨f', σ', bufs', kids'⟩ | ⟨f', σ'⟩
  · rw [hJt] at hv
    obtain ⟨fn', hf', -⟩ := hv
    exact ⟨J, hJ, fn', hk, hfp, by rw [hJt]; exact hf'⟩
  · rw [hJt] at hv; exact hv.elim

theorem bases_length : ∀ (b : ℕ) (ss : List ℕ), (bases b ss).length = ss.length
  | _, [] => rfl
  | b, _ :: ss => by rw [bases, List.length_cons, List.length_cons, bases_length _ ss]

theorem bases_getElem? : ∀ (b : ℕ) (ss : List ℕ) (k : ℕ), k < ss.length →
    (bases b ss)[k]? = some (b + (ss.take k).sum)
  | _, [], _, hk => absurd hk (Nat.not_lt_zero _)
  | b, s :: ss, 0, _ => by simp [bases]
  | b, s :: ss, k + 1, hk => by
    simp only [bases, List.getElem?_cons_succ, List.take_succ_cons, List.sum_cons]
    rw [bases_getElem? (b + s) ss k (by simpa using hk), Nat.add_assoc]

/-- **An allocation lands at its base**: the `nb`-th buffer the path allocates is at the instance's
cursor past the buffers before it, the placement's base. -/
theorem EntOk.alloc_at {fs : String → ℕ} {cert : String → V → ℕ} {e : Ent} (h : EntOk P Is e)
    (hp : e.I.t.Placed P fs cert (e.I.fp, e.I.cur)) (hI : e.I.Placed fs P.loop) {d : V}
    (hd : (allocDsts (e.pre ++ e.es))[e.nb]? = some d) :
    e.σ d = ofK (addressOfIndex (e.I.cur + (e.I.t.bufs.take e.nb).sum)) ∧ e.nb < e.I.t.bufs.length := by
  obtain ⟨f, bufs, kids, ht⟩ := h.node
  obtain ⟨vs, hw, -⟩ := h.path
  have hev : e.I.t.events P = e.pre ++ e.es := by
    have hf := h.find
    rw [ht] at hf ⊢
    exact events_node hf hw
  have hn := (Inst.nodeAt hp hI ht).1
  rw [hev, hI.2.1] at hn
  have h1 := congrArg (·[e.nb]?) hn
  simp only [List.getElem?_map, hd, Option.map_some] at h1
  have hlt : e.nb < e.I.t.bufs.length := by
    by_contra hc
    have : (bases e.I.cur e.I.t.bufs)[e.nb]? = none := by
      rw [List.getElem?_eq_none]
      rw [bases_length]
      omega
    rw [this] at h1
    cases h1
  rw [bases_getElem? _ _ _ hlt] at h1
  refine ⟨?_, hlt⟩
  have := Option.some.inj h1
  rw [ht] at this ⊢
  exact this

end Keep

end

end LeanVM.Guest.Bridge
