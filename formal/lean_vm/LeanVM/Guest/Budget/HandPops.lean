/-
  LeanVM.Guest.Budget.HandPops

  The hand functions' values from the pops: on a valid tree whose pops are within a list `H` (the
  honest pushes, by `SameStreams`), every node's path holds with its own entries within `H` and each
  call it enters related by a valid tree popping within `H` (`every_pathIn`).
-/

module

public import LeanVM.Guest.Budget.HandVals
public import LeanVM.Guest.Pops

/-!
# Values from the pops

A witness hint's words are what the valuation (a stack destination) or the memory (a heap one) hold
at the hint, and its entry is in the tree's pops (`Tree.pops`). When those agree with a known list
stream by stream (`SameStreams`, `MainHonest.pops`), each entry is in the list (`mem_of_sameStreams`),
so every hinted value a node reads is some entry of its stream: `PathIn P rd H f σ` (the node's path
holds, its own entries in `H`, each call it enters a valid tree popping within `H`, `RelIn`) holds at
every node (`every_pathIn`). A range fact on every entry of a stream then holds of every hinted
value, whatever the memory; an equality with the node's items needs the stream to have one entry.

The reads: a stack destination's entry is its cells' values (`hint_stack_mem`); a heap one's word
`k` is what a `load` at offset `off + k` reads (`heap_words_getD`).
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

/-! ## Streams and membership -/

/-- **An entry of pops agreeing with `b` stream by stream is in `b`.** -/
theorem mem_of_sameStreams {a b : List Pop} (h : SameStreams a b) {p : Pop} (hp : p ∈ a) : p ∈ b := by
  have hf : p ∈ a.filter (·.1 == p.1) := List.mem_filter.mpr ⟨hp, by simp⟩
  rw [h p.1] at hf
  exact (List.mem_filter.mp hf).1

section Splice

variable {rd : Reader} {σ : Val}

theorem evPops_cons (e : Ev) (es : List Ev) : evPops rd σ (e :: es) = e.pops rd σ ++ evPops rd σ es :=
  List.flatMap_cons

/-- A node's own entries are spliced in. -/
theorem mem_splice_of_evPops : ∀ {es : List Ev} {ks : List (List Pop)} {p : Pop},
    p ∈ evPops rd σ es → p ∈ splice rd σ es ks
  | [], _, _, h => by simp [evPops] at h
  | .atom a :: es, ks, p, h => by
      rw [evPops_cons, List.mem_append] at h
      rw [splice, List.mem_append]
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (mem_splice_of_evPops h)
  | .inK _ :: es, ks, p, h => by
      rw [evPops_cons] at h
      rw [splice]
      exact mem_splice_of_evPops (by simpa [Ev.pops] using h)
  | .call .. :: es, ks, p, h => by
      rw [evPops_cons] at h
      rw [splice, List.mem_append]
      exact Or.inr (mem_splice_of_evPops (by simpa [Ev.pops] using h))
  | .skip .. :: es, ks, p, h => by
      rw [evPops_cons] at h
      rw [splice, List.mem_append]
      exact Or.inr (mem_splice_of_evPops (by simpa [Ev.pops] using h))

/-- A callee's entries are spliced in, one callee per call event. -/
theorem mem_splice_of_kid : ∀ {es : List Ev} {ks : List (List Pop)} {k : List Pop} {p : Pop},
    (calls es).length = ks.length → k ∈ ks → p ∈ k → p ∈ splice rd σ es ks
  | [], ks, _, _, hl, hk, _ => by
      have : ks = [] := List.eq_nil_of_length_eq_zero (by simpa [calls, List.filterMap_cons] using hl.symm)
      subst this; exact (List.not_mem_nil hk).elim
  | .atom a :: es, ks, k, p, hl, hk, hp => by
      rw [splice, List.mem_append]
      exact Or.inr (mem_splice_of_kid (by simpa [calls, Ev.call?, List.filterMap_cons] using hl) hk hp)
  | .inK _ :: es, ks, k, p, hl, hk, hp => by
      rw [splice]
      exact mem_splice_of_kid (by simpa [calls, Ev.call?, List.filterMap_cons] using hl) hk hp
  | .call .. :: es, ks, k, p, hl, hk, hp => by
      obtain ⟨k0, ks, rfl⟩ : ∃ k0 t, ks = k0 :: t := List.exists_cons_of_ne_nil (by
        rintro rfl; simp [calls, Ev.call?] at hl)
      rw [splice, List.mem_append, List.headD_cons, List.tail_cons]
      rcases List.mem_cons.mp hk with rfl | hk
      · exact Or.inl hp
      · exact Or.inr (mem_splice_of_kid (by simpa [calls, Ev.call?, List.filterMap_cons] using hl) hk hp)
  | .skip .. :: es, ks, k, p, hl, hk, hp => by
      obtain ⟨k0, ks, rfl⟩ : ∃ k0 t, ks = k0 :: t := List.exists_cons_of_ne_nil (by
        rintro rfl; simp [calls, Ev.call?] at hl)
      rw [splice, List.mem_append, List.headD_cons, List.tail_cons]
      rcases List.mem_cons.mp hk with rfl | hk
      · exact Or.inl hp
      · exact Or.inr (mem_splice_of_kid (by simpa [calls, Ev.call?, List.filterMap_cons] using hl) hk hp)

end Splice

section Trees

variable {P : Core.Program} {rd : Reader}

theorem kidsValid_length {σ : Val} : ∀ {cs : List Call} {ks : List Tree}, Tree.KidsValid P rd σ cs ks →
    cs.length = ks.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, _, h⟩ => by rw [List.length_cons, List.length_cons, kidsValid_length h]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem popsKids_length : ∀ ks : List Tree, (Tree.popsKids P rd ks).length = ks.length
  | [] => by rw [Tree.popsKids]; rfl
  | k :: ks => by rw [Tree.popsKids, List.length_cons, List.length_cons, popsKids_length ks]

theorem popsKids_mem : ∀ {ks : List Tree} {k : Tree}, k ∈ ks → k.pops P rd ∈ Tree.popsKids P rd ks
  | [], _, h => (List.not_mem_nil h).elim
  | k' :: ks, k, h => by
      rw [Tree.popsKids]
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (popsKids_mem h)

/-- A call entered has a valid callee among the node's. -/
theorem KidsValid.tree {σ : Val} : ∀ {cs : List Call} {ks : List Tree}, Tree.KidsValid P rd σ cs ks →
    ∀ c ∈ cs, c.taken = true → ∃ k ∈ ks, k.name = c.f ∧ k.Valid P rd (c.args.map σ) (c.rets.map σ)
  | [], [], _, _, hc, _ => (List.not_mem_nil hc).elim
  | c :: cs, k :: ks, ⟨hn, hk, hks⟩, c', hc', ht => by
      rcases List.mem_cons.mp hc' with rfl | hc'
      · rw [ite_eq_left ht] at hk
        exact ⟨k, List.mem_cons_self, hn, hk⟩
      · obtain ⟨k', hk', h⟩ := KidsValid.tree hks c' hc' ht
        exact ⟨k', List.mem_cons_of_mem _ hk', h⟩
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim

/-- A node's entries: its events' spliced with its callees'. -/
theorem pops_node {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {fn : Fn}
    (hf : P.find? f = some fn) {es : List Ev} {vs : List V} (hw : walk σ fn.body = .ret es vs) :
    (Memory.Tree.node f σ bufs kids).pops P rd = splice rd σ es (Tree.popsKids P rd kids) := by
  have he : (Memory.Tree.node f σ bufs kids).events P = es := by
    simp only [Tree.events, Memory.Tree.name, Memory.Tree.val, hf, hw]
  rw [Memory.Tree.pops.eq_def]
  simp only [he]

/-! ## Paths within a list of entries -/

/-- **The call relation of valid trees popping within `H`.** -/
def RelIn (P : Core.Program) (rd : Reader) (H : List Pop) : CallRel :=
  fun f args rets => ∃ t : Tree, t.name = f ∧ t.Valid P rd args rets ∧ ∀ p ∈ t.pops P rd, p ∈ H

/-- **A node's path within `H`**: its body holds at `σ` on `rd`, each call it enters a valid tree
popping within `H`, and its path returns, its events holding and the entries it pops itself in `H`. -/
def PathIn (P : Core.Program) (rd : Reader) (H : List Pop) (f : String) (σ : Val) : Prop :=
  ∃ fn, P.find? f = some fn ∧ Stmt.HoldsList (RelIn P rd H) rd σ fn.body True (fun _ => True) ∧
    ∃ es vs, walk σ fn.body = .ret es vs ∧ (∀ e ∈ es, e.Holds rd σ) ∧ ∀ p ∈ evPops rd σ es, p ∈ H

theorem RelIn.rel {H : List Pop} {f : String} {args rets : List E} (h : RelIn P rd H f args rets) :
    P.Rel rd f args rets := by
  obtain ⟨t, rfl, hv, -⟩ := h
  exact Tree.Valid.rel t hv

mutual
/-- **Every node of a valid tree popping within `H` has its path within `H`.** -/
theorem every_pathIn {H : List Pop} : ∀ (t : Tree) {args rets : List E}, t.Valid P rd args rets →
    (∀ p ∈ t.pops P rd, p ∈ H) → t.Every (PathIn P rd H)
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, hw, _, hes, hk⟩, hH => by
      have hp := pops_node (rd := rd) (bufs := bufs) (kids := kids) hf hw
      have hl : (calls es).length = (Tree.popsKids P rd kids).length := by
        rw [popsKids_length, kidsValid_length hk]
      have hkid : ∀ k ∈ kids, ∀ p ∈ k.pops P rd, p ∈ H := fun k hk' p hp' =>
        hH p (by rw [hp]; exact mem_splice_of_kid hl (popsKids_mem hk') hp')
      rw [Tree.every_node]
      refine ⟨⟨fn, hf, holdsList_of_walk fn.body ?_, es, vs, hw, hes, fun p hp' => ?_⟩,
        everyKids_pathIn σ kids _ hk hkid⟩
      · rw [hw]
        refine ⟨fun e he => ⟨hes e he, fun g a r hg => ?_⟩, trivial⟩
        subst hg
        obtain ⟨k, hkm, hkn, hkv⟩ := KidsValid.tree hk _ (mem_calls_of_call he) rfl
        exact ⟨k, hkn, hkv, hkid k hkm⟩
      · exact hH p (by rw [hp]; exact mem_splice_of_evPops hp')
  | .phantom .., _, _, h, _ => h.elim

/-- `every_pathIn` for the callees. -/
theorem everyKids_pathIn {H : List Pop} : ∀ (σ : Val) (ks : List Tree) (cs : List Call),
    Tree.KidsValid P rd σ cs ks → (∀ k ∈ ks, ∀ p ∈ k.pops P rd, p ∈ H) →
      Tree.EveryKids (PathIn P rd H) ks
  | _, [], [], _, _ => by rw [Tree.EveryKids]; trivial
  | σ, k :: ks, c :: cs, ⟨_, hc, hks⟩, hH => by
      rw [Tree.EveryKids]
      refine ⟨?_, everyKids_pathIn σ ks cs hks fun k' hk' => hH k' (List.mem_cons_of_mem _ hk')⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact every_pathIn k hc (hH k List.mem_cons_self)
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        exact Tree.every_phantom
  | _, _ :: _, [], h, _ => h.elim
end

/-- **On a valid tree whose pops agree with `H` stream by stream, every node's path is within
`H`.** -/
theorem every_pathIn_of_streams {H : List Pop} {t : Tree} {args rets : List E}
    (hv : t.Valid P rd args rets) (hs : SameStreams (t.pops P rd) H) : t.Every (PathIn P rd H) :=
  every_pathIn t hv fun _ hp => mem_of_sameStreams hs hp

/-- A path within `H` holds (`PathHolds`). -/
theorem PathIn.pathHolds {H : List Pop} {f : String} {σ : Val} (h : PathIn P rd H f σ) :
    PathHolds P rd f σ := by
  obtain ⟨fn, hf, hh, -⟩ := h
  exact ⟨fn, hf, holdsList_mono (fun _ _ _ h => RelIn.rel h) fn.body id (fun _ h => h) hh⟩

end Trees

/-! ## Reading a hint's words -/

section Reads

variable {rd : Reader} {σ : Val}

/-- **A stack hint's entry** is its cells' values, among its path's entries. -/
theorem hint_stack_mem {es : List Ev} {s : String} {vs : List V}
    (h : Ev.atom (.hint (.witness s (.stack vs))) ∈ es) : (s, vs.map σ) ∈ evPops rd σ es :=
  List.mem_flatMap.mpr ⟨_, h, by simp [Ev.pops, Atom.pops, Hint.pops, Dest.words]⟩

/-- **A heap hint's entry** is its words, among its path's entries. -/
theorem hint_heap_mem {es : List Ev} {s : String} {p : V} {off len : ℕ}
    (h : Ev.atom (.hint (.witness s (.heap p off len))) ∈ es) :
    (s, (Dest.heap p off len).words rd σ) ∈ evPops rd σ es :=
  List.mem_flatMap.mpr ⟨_, h, by simp [Ev.pops, Atom.pops, Hint.pops]⟩

/-- **A heap hint's word `k` is what a `load` at offset `off + k` reads.** -/
theorem heap_words_getD {p : V} {off len k : ℕ} {v : E} (hk : k < len)
    (hl : LoadHolds rd (σ p) (off + k) v) : ((Dest.heap p off len).words rd σ).getD k 0 = v := by
  simp only [Dest.words, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, Option.getD_some, hl.2]

end Reads

end
end LeanVM.Guest.Budget
