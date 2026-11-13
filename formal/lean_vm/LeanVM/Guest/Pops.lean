/-
  LeanVM.Guest.Pops

  The witness-stream entries an evaluation of the core IR pops, in execution order: a block's (`FallPops`) and a call tree's (`Tree.pops`).
-/

module

public import LeanVM.Guest.Memory.Eval

/-!
# The pops

A hint atom constrains nothing, so the entries a run pops are what the valuation and memory hold at its hints: `Atom.pops rd σ a` is the stream and the words, a stack destination's under `σ`, a heap destination's read through `rd`.

The order is the path's (`walk`), so a block pops its atoms' entries in event order (`evPops`), and a call pops its callee's where its event sits: `splice` interleaves a node's entries with its callees', one per call event (a phantom pops nothing), and `Tree.pops` is that, recursively.

`SameStreams` compares pops with pushes stream by stream, as the streams are grouped by name. `FallPops rd σ ss ps`, the block-level form for templates (`ss` falls through, calls nothing and pops `ps`), composes by `append`, across a `match` or branch taken, and into a node's pops (`Tree.pops_of_body`).
-/

namespace LeanVM.Guest.Core

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- One popped entry: the stream and the words. -/
abbrev Pop : Type := String × List E

/-- The words of a hint's destination: frame cells under `σ`, or memory words through `rd`. -/
def Dest.words (rd : Reader) (σ : Val) : Dest → List E
  | .stack vs => vs.map σ
  | .heap p off len =>
      (List.range len).map fun k => (rd ((σ p).limb 0 * addressOfIndex (off + k))).getD 0

/-- The entry a hint pops: a witness stream's, none for computed advice. -/
def Hint.pops (rd : Reader) (σ : Val) : Hint → List Pop
  | .witness s d => [(s, d.words rd σ)]
  | _ => []

/-- The entries an atom pops. -/
def Atom.pops (rd : Reader) (σ : Val) : Atom → List Pop
  | .hint h => h.pops rd σ
  | _ => []

end
end LeanVM.Guest.Core

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- The entries an event pops itself (a call's are its callee's). -/
def Ev.pops (rd : Reader) (σ : Val) : Ev → List Pop
  | .atom a => a.pops rd σ
  | _ => []

/-- The entries events pop themselves, in order. -/
def evPops (rd : Reader) (σ : Val) (es : List Ev) : List Pop := es.flatMap (Ev.pops rd σ)

/-- Events' entries with each call's callee's spliced in where it is set up, the callees' in call order. -/
def splice (rd : Reader) (σ : Val) : List Ev → List (List Pop) → List Pop
  | [], _ => []
  | .atom a :: es, ks => a.pops rd σ ++ splice rd σ es ks
  | .inK _ :: es, ks => splice rd σ es ks
  | .call .. :: es, ks => ks.headD [] ++ splice rd σ es ks.tail
  | .skip .. :: es, ks => ks.headD [] ++ splice rd σ es ks.tail

mutual
/-- **The entries a call instance pops**, its callees' spliced in at their calls; a phantom pops nothing. -/
noncomputable def Tree.pops (P : Core.Program) (rd : Reader) : Tree → List Pop
  | t@(.node _ σ _ kids) => splice rd σ (t.events P) (Tree.popsKids P rd kids)
  | .phantom .. => []

/-- `Tree.pops` of each callee. -/
noncomputable def Tree.popsKids (P : Core.Program) (rd : Reader) : List Tree → List (List Pop)
  | [] => []
  | k :: ks => k.pops P rd :: Tree.popsKids P rd ks
end

/-- **A block falls through popping `ps`**: its path under `σ` falls through, sets up no call and pops `ps`. -/
def FallPops (rd : Reader) (σ : Val) (ss : List Stmt) (ps : List Pop) : Prop :=
  ∃ es, walk σ ss = .fall es ∧ calls es = [] ∧ evPops rd σ es = ps

/-- **Two pop lists agree stream by stream**: each stream's entries in the same order, what grouping by stream keeps. -/
def SameStreams (a b : List Pop) : Prop := ∀ s, a.filter (·.1 == s) = b.filter (·.1 == s)

/-! ## Streams -/

section Streams

variable {a b c d : List Pop}

theorem SameStreams.append (h : SameStreams a b) (h' : SameStreams c d) : SameStreams (a ++ c) (b ++ d) :=
  fun s => by rw [List.filter_append, List.filter_append, h s, h' s]

/-- Pops of distinct streams commute. -/
theorem sameStreams_append_comm (h : ∀ p ∈ a, ∀ q ∈ b, p.1 ≠ q.1) : SameStreams (a ++ b) (b ++ a) := by
  intro s
  rw [List.filter_append, List.filter_append]
  by_cases ha : a.filter (·.1 == s) = []
  · rw [ha, List.nil_append, List.append_nil]
  · obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ ha
    have hb : b.filter (·.1 == s) = [] := List.filter_eq_nil_iff.mpr fun q hq hqs => by
      obtain ⟨hpa, hps⟩ := List.mem_filter.mp hp
      exact h p hpa q hq (by rw [beq_iff_eq.mp hps, beq_iff_eq.mp hqs])
    rw [hb, List.nil_append, List.append_nil]

end Streams

/-! ## Splicing -/

section Splice

variable {rd : Reader} {σ : Val}

theorem evPops_append (es es' : List Ev) : evPops rd σ (es ++ es') = evPops rd σ es ++ evPops rd σ es' :=
  List.flatMap_append

/-- Events setting up no call splice nothing in. -/
theorem splice_append_of_calls_nil : ∀ {es : List Ev} (es' : List Ev) (ks : List (List Pop)),
    calls es = [] → splice rd σ (es ++ es') ks = evPops rd σ es ++ splice rd σ es' ks
  | [], _, _, _ => rfl
  | .atom a :: es, es', ks, h => by
      rw [List.cons_append, splice, splice_append_of_calls_nil (es := es) es' ks h]
      simp only [evPops, List.flatMap_cons, Ev.pops, List.append_assoc]
  | .inK _ :: es, es', ks, h => by
      rw [List.cons_append, splice, splice_append_of_calls_nil (es := es) es' ks h]
      rfl
  | .call .. :: _, _, _, h => by simp [calls, Ev.call?] at h
  | .skip .. :: _, _, _, h => by simp [calls, Ev.call?] at h

end Splice

/-! ## Blocks -/

section Block

variable {rd : Reader} {σ : Val}

private theorem walk_append_fall : ∀ {xs : List Stmt} {es : List Ev} (ys : List Stmt),
    walk σ xs = .fall es → walk σ (xs ++ ys) = (walk σ ys).pre es
  | [], es, ys, h => by
      rw [walk] at h
      cases h
      rw [List.nil_append]
      cases walk σ ys <;> simp [Out.pre]
  | s :: xs, es, ys, h => by
      rw [walk] at h
      rw [List.cons_append, walk]
      cases hs : walk1 σ s with
      | fall es1 =>
          rw [hs, Out.seq] at h
          cases hx : walk σ xs with
          | fall es2 =>
              rw [hx] at h
              simp only [Out.pre, Out.fall.injEq] at h
              subst h
              rw [Out.seq, walk_append_fall ys hx]
              cases walk σ ys <;> simp [Out.pre]
          | ret _ _ => rw [hx] at h; simp [Out.pre] at h
          | stuck => rw [hx] at h; simp [Out.pre] at h
      | ret _ _ => rw [hs, Out.seq] at h; cases h
      | stuck => rw [hs, Out.seq] at h; cases h

private theorem calls_append (es es' : List Ev) : calls (es ++ es') = calls es ++ calls es' :=
  List.filterMap_append

theorem FallPops.nil : FallPops rd σ [] [] := ⟨[], rfl, rfl, rfl⟩

/-- **Two blocks in turn** pop the first's entries, then the second's. -/
theorem FallPops.append {xs ys : List Stmt} {p q : List Pop} (hx : FallPops rd σ xs p)
    (hy : FallPops rd σ ys q) : FallPops rd σ (xs ++ ys) (p ++ q) := by
  obtain ⟨es, hw, hc, rfl⟩ := hx
  obtain ⟨es', hw', hc', rfl⟩ := hy
  exact ⟨es ++ es', by rw [walk_append_fall ys hw, hw', Out.pre], by rw [calls_append, hc, hc', List.append_nil],
    evPops_append es es'⟩

/-- An atom pops its entry. -/
theorem FallPops.atom (a : Atom) : FallPops rd σ [.atom a] (a.pops rd σ) :=
  ⟨[.atom a], rfl, rfl, by simp [evPops, Ev.pops]⟩

theorem FallPops.cons_atom {a : Atom} {ss : List Stmt} {p : List Pop} (h : FallPops rd σ ss p) :
    FallPops rd σ (.atom a :: ss) (a.pops rd σ ++ p) :=
  (FallPops.atom a).append h

/-- **A `match` pops its taken arm's entries**, arm `k` at `x = g^k`. -/
theorem FallPops.match_ {x : V} {arms : List (List Stmt)} {k : Nat} (hk : k < arms.length)
    (hk64 : k < 2 ^ 64 - 1) (hx : σ x = ofK (addressOfIndex k)) {p : List Pop}
    (h : FallPops rd σ arms[k] p) : FallPops rd σ [.match_ x arms] p := by
  have key : ∀ (arms : List (List Stmt)) (j i : Nat) (hi : i < arms.length),
      σ x = ofK (addressOfIndex (j + i)) → j + i < 2 ^ 64 - 1 → walkArms σ x j arms = walk σ arms[i] := by
    intro arms
    induction arms with
    | nil => intro _ _ hi; exact absurd hi (Nat.not_lt_zero _)
    | cons a as ih =>
        intro j i hi hxi hlt
        unfold walkArms
        cases i with
        | zero => rw [ite_eq_left (by simpa using hxi)]; rfl
        | succ i =>
            rw [ite_eq_right (fun h => by
              have := gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
                (ofK_injective (h.symm.trans hxi))
              omega)]
            exact ih (j + 1) i (by simpa using hi) (by rw [hxi]; congr 2; omega) (by omega)
  obtain ⟨es, hw, hc, hp⟩ := h
  refine ⟨es, ?_, hc, hp⟩
  rw [walk, walk, walk1, key arms 0 k hk (by simpa using hx) (by omega), hw]
  simp [Out.seq, Out.pre]

/-- A branch pops its taken side's entries. -/
theorem FallPops.ite {c : V} {z n : List Stmt} {p : List Pop}
    (h : FallPops rd σ (if σ c = 0 then z else n) p) : FallPops rd σ [.ite c z n] p := by
  obtain ⟨es, hw, hc, hp⟩ := h
  refine ⟨.inK c :: es, ?_, hc, hp⟩
  rw [walk, walk, walk1]
  split_ifs at hw ⊢ <;> simp [hw, Out.seq, Out.pre]

end Block

/-! ## Trees -/

section Tree

variable {P : Core.Program} {rd : Reader}

/-- A node's entries: its path's, its callees' spliced in. -/
theorem Tree.pops_node {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {fn : Fn}
    {es : List Ev} {vs : List V} (hf : P.find? f = some fn) (hw : walk σ fn.body = .ret es vs) :
    (Tree.node f σ bufs kids).pops P rd = splice rd σ es (Tree.popsKids P rd kids) := by
  have : (Tree.node f σ bufs kids).events P = es := by
    simp only [Tree.events, Tree.name, Tree.val, hf, hw]
  rw [Tree.pops, this]

/-- **A node whose body starts with a block popping `p`** pops `p` first. -/
theorem Tree.pops_of_body {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {fn : Fn}
    {xs ys : List Stmt} {p : List Pop} {es : List Ev} {vs : List V} (hf : P.find? f = some fn)
    (hb : fn.body = xs ++ ys) (hx : FallPops rd σ xs p) (hy : walk σ ys = .ret es vs) :
    ∃ es', walk σ fn.body = .ret es' vs ∧
      (Tree.node f σ bufs kids).pops P rd = p ++ splice rd σ es (Tree.popsKids P rd kids) := by
  obtain ⟨es0, hw0, hc0, rfl⟩ := hx
  have hw : walk σ fn.body = .ret (es0 ++ es) vs := by
    rw [hb, walk_append_fall ys hw0, hy, Out.pre]
  exact ⟨_, hw, by rw [Tree.pops_node hf hw, splice_append_of_calls_nil es _ hc0]⟩

end Tree

end
end LeanVM.Guest.Memory
