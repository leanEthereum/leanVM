/-
  LeanVM.Guest.Bridge.Prefix

  The hint bridge on the prefix class: a path's own pops are its leading flow hints', in body order, and an ISA hint compiling a core hint atom meets `HintOk` at the atom's cells.
-/

module

public import LeanVM.Guest.Bridge.Defs
public import LeanVM.Guest.Pops
public import LeanVM.Prover.ExecuteCompleteHint

/-!
# The hint bridge on the prefix class

* **Order.** `prefix_path`: on a function passing `prefixOk`, every path starts with the body's leading atoms, and the rest of it has no witness hint; `prefix_splice`: so the instance's pops are its leading flow hints' entries, in order, then its callees' (`splice` of the rest). `prefix_pairs`: the function's ISA flow hints, in offset order, are at offsets up to its first jump, and the `k`-th compiles the `k`-th leading flow hint. A frame's run passes offsets `0, 1, …` up to the first jump in order (every instruction before it falls through: `step_at`'s fall-through), so the `k`-th flow hint it runs is the `k`-th of the path, and the `k`-th witness hint pops the `k`-th witness entry of the instance.
* **Cells.** An ISA hint compiling a core hint atom meets `HintOk` once the frame holds the atom's values at their cells and the stream's next entry is the atom's: `hintOk_stack` (a witness run into the frame), `hintOk_heap` (into a buffer, its words those `Dest.words` reads at the pointer's cells, `words_heap`), `hintOk_inverse` (a computed hint: the destination holds the formula of the input, which the honest valuation states of every hint atom on its path).
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Prover.Exec (Ctx St HintOk StreamNext RunOk maxCells PtrAt)

public section

/-! ## The path -/

theorem atomPrefix_eq : ∀ body : List Stmt,
    body = (atomPrefix body).1.map Stmt.atom ++ (atomPrefix body).2
  | [] => rfl
  | s :: ss => by
    cases s with
    | atom a =>
      simp only [atomPrefix, List.map_cons, List.cons_append]
      exact congrArg _ (atomPrefix_eq ss)
    | _ => rfl

theorem walk_atoms (σ : Val) : ∀ (as : List Atom) (ss : List Stmt),
    walk σ (as.map Stmt.atom ++ ss) = (walk σ ss).pre (as.map Ev.atom)
  | [], ss => by cases h : walk σ ss <;> simp [Out.pre, h]
  | a :: as, ss => by
    rw [List.map_cons, List.cons_append, walk, walk1, walk_atoms σ as ss, Out.seq]
    cases walk σ ss <;> simp [Out.pre]

theorem calls_atoms : ∀ as : List Atom, calls (as.map Ev.atom) = []
  | [] => rfl
  | _ :: as => by simp only [List.map_cons, calls, List.filterMap_cons, Ev.call?]; exact calls_atoms as

/-- Atoms pop their flow hints' entries. -/
theorem flatMap_pops_atoms (rd : Reader) (σ : Val) : ∀ as : List Atom,
    as.flatMap (Atom.pops rd σ) = (flowOf as).flatMap (Core.Hint.pops rd σ)
  | [] => rfl
  | a :: as => by
    have ih := flatMap_pops_atoms rd σ as
    cases a with
    | hint h => cases h <;> simp [flowOf, coreFlow, Atom.pops, Core.Hint.pops, ih]
    | _ => simp [flowOf, Atom.pops, ih]

/-- **A path of a prefix function**: the body's leading atoms, then a path of its rest, which has
no witness hint. -/
theorem prefix_path {body : List Stmt} (hw : Stmt.noWitList (atomPrefix body).2 = true) {σ : Val}
    {es : List Ev} {vs : List V} (h : walk σ body = .ret es vs) :
    ∃ es', walk σ (atomPrefix body).2 = .ret es' vs ∧
      es = (atomPrefix body).1.map Ev.atom ++ es' ∧ ∀ e ∈ es', e.noWit := by
  rw [atomPrefix_eq body, walk_atoms] at h
  have hall := walk_noWit (σ := σ) _ hw
  cases hr : walk σ (atomPrefix body).2 with
  | fall _ => rw [hr] at h; simp [Out.pre] at h
  | stuck => rw [hr] at h; simp [Out.pre] at h
  | ret es' vs' =>
    rw [hr] at h hall
    simp only [Out.pre, Out.ret.injEq] at h
    exact ⟨es', by rw [h.2], h.1.symm, hall⟩

/-- **An instance's pops on a prefix function**: its leading flow hints' entries, in order, then
the rest's, which are its callees'. -/
theorem prefix_splice {body : List Stmt} (hw : Stmt.noWitList (atomPrefix body).2 = true)
    {σ : Val} {es : List Ev} {vs : List V} (h : walk σ body = .ret es vs) (rd : Reader)
    (ks : List (List Pop)) :
    ∃ es', walk σ (atomPrefix body).2 = .ret es' vs ∧ (∀ e ∈ es', e.noWit) ∧
      splice rd σ es ks = (flowOf (atomPrefix body).1).flatMap (Core.Hint.pops rd σ) ++
        splice rd σ es' ks := by
  obtain ⟨es', h1, rfl, h3⟩ := prefix_path hw h
  refine ⟨es', h1, h3, ?_⟩
  rw [splice_append_of_calls_nil _ _ (calls_atoms _), evPops, List.flatMap_map]
  exact congrArg (· ++ _) (flatMap_pops_atoms rd σ _)

/-- An instance calling nothing on a prefix function pops its leading flow hints' entries. -/
theorem prefix_pops_leaf {body : List Stmt} (hw : Stmt.noWitList (atomPrefix body).2 = true)
    {σ : Val} {es : List Ev} {vs : List V} (h : walk σ body = .ret es vs) (rd : Reader) :
    splice rd σ es [] = (flowOf (atomPrefix body).1).flatMap (Core.Hint.pops rd σ) := by
  obtain ⟨es', -, h3, h⟩ := prefix_splice hw h rd []
  rw [h, splice_nil_of es' [] h3 (fun _ h ↦ (List.not_mem_nil h).elim), List.append_nil]

/-! ## The pairing -/

theorem pairsOk_get {loc : ℕ → ℕ} : ∀ {hs : List Core.Hint} {hs' : List Prover.Exec.Hint},
    pairsOk loc hs hs' = true →
      hs.length = hs'.length ∧ ∀ k (hk : k < hs.length) (hk' : k < hs'.length),
        compiles loc hs[k] hs'[k] = true
  | [], [], _ => ⟨rfl, fun _ hk ↦ (Nat.not_lt_zero _ hk).elim⟩
  | h :: hs, h' :: hs', e => by
    simp only [pairsOk, Bool.and_eq_true] at e
    obtain ⟨hl, hg⟩ := pairsOk_get e.2
    refine ⟨by simp [hl], fun k hk hk' ↦ ?_⟩
    cases k with
    | zero => exact e.1
    | succ k => exact hg k (by simpa using hk) (by simpa using hk')
  | [], _ :: _, e | _ :: _, [], e => by simp [pairsOk] at e

/-- **The per-pc pairing of a prefix function**: its ISA flow hints, in offset order, are at
offsets up to its first jump, as many as its leading flow hints, the `k`-th compiling the `k`-th. -/
theorem prefix_pairs {loc : ℕ → ℕ} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (h : prefixOk loc body code d = true) :
    Stmt.noWitList (atomPrefix body).2 = true ∧ (∀ p ∈ isaFlow d, p.1 ≤ firstJump code) ∧
      (flowOf (atomPrefix body).1).length = (isaFlow d).length ∧
      ∀ k (hk : k < (flowOf (atomPrefix body).1).length) (hk' : k < (isaFlow d).length),
        compiles loc (flowOf (atomPrefix body).1)[k] (isaFlow d)[k].2 = true := by
  simp only [prefixOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, -⟩, -⟩, h2⟩, h3⟩ := h
  obtain ⟨hl, hg⟩ := pairsOk_get h3
  rw [List.length_map] at hl
  exact ⟨h1, h2, hl, fun k hk hk' ↦ by
    have := hg k hk (by rw [List.length_map]; exact hk')
    rwa [List.getElem_map] at this⟩

/-! ## The cells -/

theorem consecutive_get {loc : ℕ → ℕ} : ∀ {b : ℕ} {vs : List V}, consecutive loc b vs = true →
    ∀ k (hk : k < vs.length), loc vs[k].idx = b + k
  | _, [], _, _, hk => (Nat.not_lt_zero _ hk).elim
  | b, v :: vs, e, k, hk => by
    simp only [consecutive, Bool.and_eq_true, beq_iff_eq] at e
    cases k with
    | zero => exact e.1
    | succ k =>
      rw [List.getElem_cons_succ, consecutive_get e.2 k (by simpa using hk)]
      omega

/-- **A witness run into the frame**: the stream, the length, and each value's cell. -/
theorem compiles_stack {loc : ℕ → ℕ} {s s' : String} {vs : List V} {base len : ℕ}
    (h : compiles loc (.witness s (.stack vs)) (.witnessStack s' base len) = true) :
    s' = s ∧ len = vs.length ∧ ∀ k (hk : k < vs.length), loc vs[k].idx = base + k := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.symm, h.1.2.symm, consecutive_get h.2⟩

/-- **The frame's run of a stack witness holds its values**: from the values at their cells. -/
theorem runOk_stack {loc : ℕ → ℕ} {s s' : String} {vs : List V} {base len : ℕ}
    (h : compiles loc (.witness s (.stack vs)) (.witnessStack s' base len) = true) {M : ℕ → E}
    {fp : ℕ} {σ : Val} (hM : ∀ v ∈ vs, M (fp + loc v.idx) = σ v) (hc : fp + base + len ≤ maxCells)
    (rd : Reader) : RunOk M (fp + base) ((Dest.stack vs).words rd σ) := by
  obtain ⟨-, rfl, hl⟩ := compiles_stack h
  intro k hk
  simp only [Dest.words, List.length_map] at hk ⊢
  refine ⟨by omega, ?_⟩
  rw [List.getElem_map, ← hM _ (List.getElem_mem hk), hl k hk, Nat.add_assoc]

/-- **`HintOk` of a stack witness hint**: the stream's next entry the atom's words, its values at
their cells. -/
theorem hintOk_stack {loc : ℕ → ℕ} {s s' : String} {vs : List V} {base len : ℕ}
    (h : compiles loc (.witness s (.stack vs)) (.witnessStack s' base len) = true) {C : Ctx}
    {M : ℕ → E} {st : St} {σ : Val} {rd : Reader}
    (hn : StreamNext C st s ((Dest.stack vs).words rd σ))
    (hM : ∀ v ∈ vs, M (st.fp + loc v.idx) = σ v) (hc : st.fp + base + len ≤ maxCells) :
    HintOk C M st (.witnessStack s' base len) := by
  obtain ⟨rfl, rfl, -⟩ := compiles_stack h
  exact ⟨_, hn, by simp [Dest.words], runOk_stack h hM hc rd⟩

/-- **A witness run into a buffer**: the stream, the pointer's cell, the offset and the length. -/
theorem compiles_heap {loc : ℕ → ℕ} {s s' : String} {p : V} {off len ptr lo len' : ℕ}
    (h : compiles loc (.witness s (.heap p off len)) (.witnessHeap s' ptr lo len') = true) :
    s' = s ∧ ptr = loc p.idx ∧ lo = off ∧ len' = len := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.symm, h.1.1.2.symm, h.1.2.symm, h.2.symm⟩

/-- **A buffer's words are read at the pointer's cells**: `g^(b + off + k)` for a pointer `g^b`. -/
theorem words_heap {rd : Reader} {σ : Val} {p : V} {off len b : ℕ} (hp : σ p = ofK (g ^ b)) :
    (Dest.heap p off len).words rd σ = (List.range len).map fun k ↦ (rd (g ^ (b + off + k))).getD 0 := by
  simp only [Dest.words, hp]
  refine List.map_congr_left fun k _ ↦ ?_
  simp [addressOfIndex, ← pow_add, Nat.add_assoc]

/-- **`HintOk` of a heap witness hint**: the pointer's cell holding `g^b`, the stream's next entry
the atom's words, and the reference holding them from `g^(b + off)`. -/
theorem hintOk_heap {loc : ℕ → ℕ} {s s' : String} {p : V} {off len ptr lo len' : ℕ}
    (h : compiles loc (.witness s (.heap p off len)) (.witnessHeap s' ptr lo len') = true)
    {C : Ctx} {M : ℕ → E} {st : St} {σ : Val} {rd : Reader} {b : ℕ}
    (hp : PtrAt st (st.fp + loc p.idx) b) (hn : StreamNext C st s ((Dest.heap p off len).words rd σ))
    (hr : RunOk M (b + off) ((Dest.heap p off len).words rd σ)) :
    HintOk C M st (.witnessHeap s' ptr lo len') := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := compiles_heap h
  exact ⟨b, _, hp, hn, by simp [Dest.words], hr⟩

/-- **`HintOk` of a computed hint, the inverse**: the input cell holding the input's word, the
destination's holding the output's, and the output the input's inverse (or `0`), as the honest
valuation states of a hint atom on its path. -/
theorem hintOk_inverse {loc : ℕ → ℕ} {x d : V} {x' d' : ℕ}
    (h : compiles loc (.inverse x d) (.inverse x' d') = true) {C : Ctx} {M : ℕ → E} {st : St}
    {σ : Val} (hx : st.mem.peek (st.fp + loc x.idx) = σ x) (hd : M (st.fp + loc d.idx) = σ d)
    (hc : st.fp + loc d.idx < maxCells) (hex : σ d = if σ x = 0 then 0 else (σ x)⁻¹) :
    HintOk C M st (.inverse x' d') := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨hc, by rw [hd, hex, hx]⟩

end

end LeanVM.Guest.Bridge
