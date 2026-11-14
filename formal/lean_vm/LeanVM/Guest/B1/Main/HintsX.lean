/-
  LeanVM.Guest.B1.Main.HintsX

  The heap hints of `main`'s tree in its data or its header: the loop helpers writing into
  `main`'s buffers through a computed pointer write inside them, every other function by the
  check (`Memory.GuestHints`).
-/

module

public import LeanVM.Guest.Memory.GuestHints
public import LeanVM.Guest.Memory.HonestMain
public import LeanVM.Guest.B1.Main.MainAt

/-!
# `main`'s heap hints

`hintsQ_loop`: the trees of a loop helper whose iterations keep an invariant of their arguments and
write their heap hints into a region `Q` (or words they load), their other callees in a closed set
passing the check, are `HintsQ Q`. The claim tables' duplicate slots (`main_loop0`, `main_loop1`,
`dupStep`) and the children's carried claims (`main_loop4`, `l5Step`) write at the iteration's
exponent times the slot's width into a `HeapBuf` of `main` as wide as all iterations' slots.
`main_hintsIn`: `main`'s tree on a memory image, with its loads in its data or its header, has its
heap hints there too.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest (atomsIn)

@[expose] public section

/-! ## Loop helpers -/

section Loop

variable {P : Core.Program} {fs : String → ℕ} {cert : String → V → ℕ} {rd : Reader}
  {S : String → Prop} {Q : ℕ → Prop} {f : String} {fn : Fn} {Inv : List E → Prop}

/-- What an iteration of a loop helper gives: its heap hint words loaded or in `Q`, and the
invariant at its tail call. -/
def LoopStep (rd : Reader) (Q : ℕ → Prop) (f : String) (fn : Fn) (Inv : List E → Prop) : Prop :=
  ∀ σ es vs, walk σ fn.body = .ret es vs → (∀ e ∈ es, e.Holds rd σ) → Inv (fn.params.map σ) →
    (∀ A ∈ heapHintAddrs σ es, A ∈ loadAddrs σ es ∨ ∃ i, A = addressOfIndex i ∧ Q i) ∧
      ∀ c ∈ calls es, c.f = f → c.taken = true → Inv (c.args.map σ)

mutual
/-- `hintsQ_loop` for an iteration's callees. -/
theorem hintsQKids_loop (hf : P.find? f = some fn) (hS : HintsClosed P S)
    (hcl : ∀ c ∈ Stmt.blockCallees fn.body, c = f ∨ S c) (hst : LoopStep rd Q f fn Inv) :
    ∀ (ks : List Tree) (σ : Val) (cs : List Call) (ps : List (ℕ × ℕ)), Tree.KidsValid P rd σ cs ks →
      Tree.BufsOkKids P ks → Tree.PlacedKids P fs cert ps ks → (∀ c ∈ cs, c.f = f ∨ S c.f) →
      (∀ c ∈ cs, c.f = f → c.taken = true → Inv (c.args.map σ)) → Tree.HintsQKids P fs cert Q ps ks
  | [], _, _, _, _, _, _, _, _ => hintsQKids_nil
  | _ :: _, _, _, [], _, _, _, _, _ => by rw [Tree.HintsQKids]; trivial
  | k :: ks, σ, c :: cs, p :: ps, ⟨hn, hc, hks⟩, hb, hp, hS', hI => by
      rw [Tree.BufsOkKids] at hb
      rw [placedKids_cons] at hp
      rw [hintsQKids_cons]
      refine ⟨?_, hintsQKids_loop hf hS hcl hst ks σ cs ps hks hb.2 hp.2
        (fun c' h => hS' c' (List.mem_cons_of_mem _ h)) (fun c' h => hI c' (List.mem_cons_of_mem _ h))⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        rcases hS' c List.mem_cons_self with hcf | hcs
        · exact hintsQ_loop hf hS hcl hst k p hc hb.1 hp.1 (hn.trans hcf)
            (hI c List.mem_cons_self hcf ht)
        · exact hintsQ_of_closed hS Q k p hc hb.1 hp.1 (hn ▸ hcs)
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨_, _, rfl⟩, -⟩ := hc
        exact hintsQ_phantom
  | _ :: _, _, [], _ :: _, h, _, _, _, _ => h.elim
/-- **A loop helper's trees are `HintsQ`**, from its iterations' steps. -/
theorem hintsQ_loop (hf : P.find? f = some fn) (hS : HintsClosed P S)
    (hcl : ∀ c ∈ Stmt.blockCallees fn.body, c = f ∨ S c) (hst : LoopStep rd Q f fn Inv) :
    ∀ (t : Tree) {args rets : List E} (p : ℕ × ℕ), t.Valid P rd args rets → t.BufsOk P →
      t.Placed P fs cert p → t.name = f → Inv args → t.HintsQ P fs cert Q p
  | .node g σ bufs kids, args, rets, p, hv, hb, hp, hn, hI => by
      have hg : g = f := hn
      obtain ⟨fn', hf', hpar, es, vs, hw, -, hes, hk⟩ := hv
      have hfg : P.find? g = some fn := by rw [hg]; exact hf
      have hfn : fn' = fn := Option.some.inj (hf'.symm.trans hfg)
      rw [hfn] at hpar hw
      obtain ⟨h1, h2⟩ := hst σ es vs hw hes (hpar ▸ hI)
      rw [hintsQ_node, events_node hfg hw]
      rw [Tree.BufsOk] at hb
      rw [placed_node] at hp
      refine ⟨fun A hA => (h1 A hA).imp id fun ⟨i, hi, hq⟩ => ⟨i, hi, Or.inr hq⟩, ?_⟩
      exact hintsQKids_loop hf hS hcl hst kids σ (calls es) _ hk hb.2 hp.2
        (fun c hc => hcl c.f (walk_callees (σ := σ) fn.body (by rw [hw]; exact hc))) h2
  | .phantom .., _, _, _, _, _, _, _, _ => hintsQ_phantom

end

end Loop

/-! ## The claim tables' duplicate slots -/

/-- **The duplicate slots' loop** (`main_loop0`, `main_loop1`, `f` naming it), but its return: slot
`x` of the table at parameter `2`, `4` words at `g^(4·(a + x))` past it, `a` the exponent of
parameter `3`. -/
def dupPre (f : String) : List Stmt := [
  .atom (.mul (.n 4) (.n 3) (.n 0)),
  .atom (.mul (.n 5) (.n 4) (.n 4)),
  .atom (.mul (.n 6) (.n 5) (.n 5)),
  .atom (.mul (.n 7) (.n 2) (.n 6)),
  .atom (.hint (.witness "dup_claims" (.heap (.n 7) 0 4))),
  .atom (.const (.n 8) (word 2 0)),
  .atom (.mul (.n 9) (.n 0) (.n 8)),
  .atom (.add (.n 10) (.n 9) (.n 1)),
  .atom (.const (.n 11) (word 2 0)),
  .atom (.mul (.n 12) (.n 0) (.n 11)),
  .callIf (.n 10) f [.n 12, .n 1, .n 2, .n 3]]

theorem loop0_found : coreProgram.find? (name% «main_loop0») = some fn% «main_loop0» ∧
    (fn% «main_loop0»).params = [.n 0, .n 1, .n 2, .n 3] ∧
    (fn% «main_loop0»).body = dupPre (name% «main_loop0») ++ [.ret []] :=
  ⟨coreProgram_find?_at (j := idx% «main_loop0») rfl, rfl, rfl⟩

theorem loop1_found : coreProgram.find? (name% «main_loop1») = some fn% «main_loop1» ∧
    (fn% «main_loop1»).params = [.n 0, .n 1, .n 2, .n 3] ∧
    (fn% «main_loop1»).body = dupPre (name% «main_loop1») ++ [.ret []] :=
  ⟨coreProgram_find?_at (j := idx% «main_loop1») rfl, rfl, rfl⟩

theorem hintAddrs_ite_call {σ : Val} {p : Prop} [Decidable p] {f : String} {a r : List V} :
    Ev.hintAddrs σ (if p then .skip f a else .call f a r) = [] := by
  split <;> rfl

theorem limb_gen_pow (m : ℕ) : (gen ^ m).limb 0 = addressOfIndex m := by
  rw [gen_pow_eq_ofK]; simp

theorem gen_succ_add_ne {x b : ℕ} (h : gen ^ x * gen + gen ^ b ≠ 0) : x + 1 ≠ b := by
  rintro rfl
  rw [← pow_succ, e_add_eq_zero_iff.mpr rfl] at h
  exact h rfl

/-- **An iteration of the duplicate slots' loop**: its slot's words lie in the table's
`4·(a + b)` words, and its tail call is the next slot's, below `b`. -/
theorem dupStep {rd : Reader} {f : String} {σ : Val} {es : List Ev} {vs : List V}
    (hw : walk σ (dupPre f ++ [.ret []]) = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ)
    {x b β a : ℕ} (h0 : σ (.n 0) = gen ^ x) (h1 : σ (.n 1) = gen ^ b) (h2 : σ (.n 2) = gen ^ β)
    (h3 : σ (.n 3) = gen ^ a) (hxb : x < b) :
    (∀ A ∈ heapHintAddrs σ es, ∃ i, A = addressOfIndex i ∧ β ≤ i ∧ i < β + 4 * (a + b)) ∧
      ∀ c ∈ calls es, c.taken = true →
        c.args.map σ = [gen ^ (x + 1), gen ^ b, gen ^ β, gen ^ a] ∧ x + 1 < b := by
  have hst : (dupPre f).all Stmt.straight = true := rfl
  rw [walk_straight σ [] _ hst] at hw
  cases hw
  have hc := (straight_parts σ _ hst).2.2.2
  simp only [dupPre, List.flatMap_cons, List.flatMap_nil, slEvs, List.cons_append,
    List.nil_append, List.forall_mem_cons, Ev.Holds, Atom.Holds] at hh
  obtain ⟨e4, e5, e6, e7, -, e8, e9, e10, e11, e12, -, -⟩ := hh
  rw [word_gen] at e8 e11
  have v7 : σ (.n 7) = gen ^ (β + 4 * (a + x)) := by
    rw [e7, e6, e5, e4, h2, h3, h0, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    congr 1; ring
  refine ⟨fun A hA => ?_, fun c hcm ht => ?_⟩
  · obtain ⟨e, he, hA⟩ := List.mem_flatMap.mp hA
    simp only [dupPre, List.flatMap_cons, List.flatMap_nil, slEvs, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try first | (rw [hintAddrs_ite_call] at hA; exact absurd hA List.not_mem_nil) |
      exact absurd hA List.not_mem_nil
    simp only [Ev.hintAddrs, hintDest?, destHeap?, Option.bind_some, List.mem_map, List.mem_range] at hA
    obtain ⟨k, hk, rfl⟩ := hA
    refine ⟨β + 4 * (a + x) + k, ?_, by omega, by omega⟩
    rw [v7, limb_gen_pow, Parameters.addressOfIndex, Parameters.addressOfIndex, Parameters.addressOfIndex,
      ← pow_add]
    congr 1; omega
  · rw [hc] at hcm
    simp only [dupPre, List.filterMap_cons, Stmt.callS, List.filterMap_nil, List.map_cons,
      List.map_nil, List.mem_cons, List.not_mem_nil, or_false, mkCall] at hcm
    subst hcm
    simp only [decide_eq_true_eq] at ht
    rw [e10, e9, e8, h0, h1] at ht
    have := gen_succ_add_ne ht
    refine ⟨?_, by omega⟩
    simp only [List.map_cons, List.map_nil, e12, e11, h0, h1, h2, h3, pow_succ]

/-! ## The children's carried claims -/

/-- **The children's loop** (`main_loop4`), but its return: child `x`'s carried claim, `24` words at
`g^(24·x)` past the table at parameter `9`, and its DA digest, which it loads. -/
def l5HPre : List Stmt := [
  .atom (.mul (.n 16) (.n 2) (.n 0)),
  .atom (.load (.n 17) (.n 16) 0),
  .atom (.hint (.witness "child_meta" (.stack [.n 18, .n 19]))),
  .atom (.touch (.n 20) (.n 18)),
  .atom (.touch (.n 21) (.n 19)),
  .atom (.mul (.n 22) (.n 18) (.n 19)),
  .call "child_claim_list_digest" [.n 3, .n 4, .n 17, .n 5, .n 18] [.n 23, .n 24],
  .atom (.mul (.n 25) (.n 17) (.n 18)),
  .call "child_claim_list_digest" [.n 6, .n 7, .n 25, .n 8, .n 19] [.n 26, .n 27],
  .atom (.mul (.n 28) (.n 0) (.n 0)),
  .atom (.mul (.n 29) (.n 28) (.n 0)),
  .atom (.mul (.n 30) (.n 29) (.n 29)),
  .atom (.mul (.n 31) (.n 30) (.n 30)),
  .atom (.mul (.n 32) (.n 31) (.n 31)),
  .atom (.mul (.n 33) (.n 9) (.n 32)),
  .atom (.hint (.witness "child_defer" (.heap (.n 33) 0 24))),
  .atom (.mul (.n 34) (.n 0) (.n 0)),
  .atom (.mul (.n 35) (.n 10) (.n 34)),
  .atom (.hint (.witness "child_da" (.heap (.n 35) 0 2))),
  .atom (.load (.n 36) (.n 35) 0),
  .atom (.load (.n 37) (.n 35) 1),
  .call "statement_digest" [.n 11, .n 12, .n 23, .n 24, .n 26, .n 27, .n 36, .n 37, .n 33] [.n 38, .n 39],
  .atom (.mul (.n 40) (.n 0) (.n 0)),
  .atom (.mul (.n 41) (.n 13) (.n 40)),
  .atom (.load (.n 38) (.n 41) 0),
  .atom (.mul (.n 42) (.n 13) (.n 40)),
  .atom (.load (.n 39) (.n 42) 1),
  .atom (.mul (.n 43) (.n 0) (.n 0)),
  .atom (.mul (.n 44) (.n 43) (.n 0)),
  .atom (.mul (.n 45) (.n 44) (.n 44)),
  .atom (.mul (.n 46) (.n 45) (.n 45)),
  .atom (.mul (.n 47) (.n 46) (.n 46)),
  .atom (.mul (.n 48) (.n 15) (.n 47)),
  .call "verify_sub" [.n 38, .n 39, .n 11, .n 12, .n 14, .n 48] [],
  .atom (.mul (.n 49) (.n 17) (.n 22)),
  .atom (.mul (.n 50) (.n 2) (.n 0)),
  .atom (.load (.n 49) (.n 50) 1),
  .atom (.const (.n 51) (word 2 0)),
  .atom (.mul (.n 52) (.n 0) (.n 51)),
  .atom (.add (.n 53) (.n 52) (.n 1)),
  .atom (.const (.n 54) (word 2 0)),
  .atom (.mul (.n 55) (.n 0) (.n 54)),
  .callIf (.n 53) name% «main_loop4» [.n 55, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 12, .n 13, .n 14, .n 15]]

theorem loop4_found : coreProgram.find? (name% «main_loop4») = some fn% «main_loop4» ∧
    (fn% «main_loop4»).params = (List.range 16).map V.n ∧
    (fn% «main_loop4»).body = l5HPre ++ [.ret []] :=
  ⟨coreProgram_find?_at (j := idx% «main_loop4») rfl, rfl, rfl⟩

/-- **An iteration of the children's loop**: its carried claim's words lie in the table's `24·c`
words, its DA digest's it loads, and its tail call is the next child's, below `c`. -/
theorem l5Step {rd : Reader} {σ : Val} {es : List Ev} {vs : List V}
    (hw : walk σ (l5HPre ++ [.ret []]) = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ)
    {x c β : ℕ} (h0 : σ (.n 0) = gen ^ x) (h1 : σ (.n 1) = gen ^ c) (h9 : σ (.n 9) = gen ^ β)
    (hxc : x < c) :
    (∀ A ∈ heapHintAddrs σ es, A ∈ loadAddrs σ es ∨
      ∃ i, A = addressOfIndex i ∧ β ≤ i ∧ i < β + 24 * c) ∧
      ∀ c' ∈ calls es, c'.f = name% «main_loop4» → c'.taken = true →
        (c'.args.map σ).getD 0 0 = gen ^ (x + 1) ∧ (c'.args.map σ).getD 1 0 = gen ^ c ∧
          (c'.args.map σ).getD 9 0 = gen ^ β ∧ x + 1 < c := by
  have hst : l5HPre.all Stmt.straight = true := rfl
  rw [walk_straight σ [] _ hst] at hw
  cases hw
  have hc := (straight_parts σ _ hst).2.2.2
  have hh' := hh
  simp only [l5HPre, List.flatMap_cons, List.flatMap_nil, slEvs, List.cons_append,
    List.nil_append, List.forall_mem_cons, Ev.Holds, Atom.Holds] at hh'
  obtain ⟨-, -, -, -, -, -, -, -, -, e28, e29, e30, e31, e32, e33, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, e51, e52, e53, e54, e55, -, -⟩ := hh'
  rw [word_gen] at e51 e54
  have v33 : σ (.n 33) = gen ^ (β + 24 * x) := by
    rw [e33, e32, e31, e30, e29, e28, h9, h0, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add, ← pow_add]
    congr 1; ring
  refine ⟨fun A hA => ?_, fun c' hcm hf ht => ?_⟩
  · obtain ⟨e, he, hA⟩ := List.mem_flatMap.mp hA
    have hes := he
    simp only [l5HPre, List.flatMap_cons, List.flatMap_nil, slEvs, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try first | (rw [hintAddrs_ite_call] at hA; exact absurd hA List.not_mem_nil) |
      exact absurd hA List.not_mem_nil
    · simp only [Ev.hintAddrs, hintDest?, destHeap?, Option.bind_some, List.mem_map, List.mem_range] at hA
      obtain ⟨k, hk, rfl⟩ := hA
      refine Or.inr ⟨β + 24 * x + k, ?_, by omega, by nlinarith⟩
      rw [v33, limb_gen_pow, Parameters.addressOfIndex, Parameters.addressOfIndex,
        Parameters.addressOfIndex, ← pow_add]
      congr 1; omega
    · simp only [Ev.hintAddrs, hintDest?, destHeap?, Option.bind_some, List.mem_map, List.mem_range] at hA
      obtain ⟨k, hk, rfl⟩ := hA
      left
      refine List.mem_filterMap.mpr ⟨.atom (.load (.n (36 + k)) (.n 35) k), ?_, ?_⟩
      · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;>
          simp [l5HPre, slEvs]
      · simp [Ev.loadAddr?]
  · rw [hc] at hcm
    simp only [l5HPre, List.filterMap_cons, Stmt.callS, List.filterMap_nil, List.map_cons,
      List.map_nil, List.mem_cons, List.not_mem_nil, or_false, mkCall] at hcm
    rcases hcm with rfl | rfl | rfl | rfl | rfl
    all_goals try (exact absurd hf (by decide))
    simp only [decide_eq_true_eq] at ht
    rw [e53, e52, e51, h0, h1] at ht
    have := gen_succ_add_ne ht
    refine ⟨?_, ?_, ?_, by omega⟩
    · simp [e55, e54, h0, pow_succ]
    · simp [h1]
    · simp [h9]


/-! ## The loop helpers' invariants -/

/-- The duplicate slots' loop's arguments: slot `x` of `b`, the table `4·(a + b)` words of `Q` at
`β`. -/
def DupInv (Q : ℕ → Prop) (args : List E) : Prop :=
  ∃ x b β a, args = [gen ^ x, gen ^ b, gen ^ β, gen ^ a] ∧ x < b ∧
    ∀ i, β ≤ i → i < β + 4 * (a + b) → Q i

theorem dupLoopStep {rd : Reader} {Q : ℕ → Prop} {f : String} {fn : Fn}
    (hfn : fn.params = [.n 0, .n 1, .n 2, .n 3] ∧ fn.body = dupPre f ++ [.ret []]) :
    LoopStep rd Q f fn (DupInv Q) := by
  intro σ es vs hw hh hI
  rw [hfn.2] at hw
  rw [hfn.1] at hI
  obtain ⟨x, b, β, a, he, hxb, hQ⟩ := hI
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
  obtain ⟨h0, h1, h2, h3⟩ := he
  have d := dupStep hw hh h0 h1 h2 h3 hxb
  refine ⟨fun A hA => Or.inr ?_, fun c hc _ ht => ?_⟩
  · obtain ⟨i, hi, h1, h2⟩ := d.1 A hA
    exact ⟨i, hi, hQ i h1 h2⟩
  · obtain ⟨h1, h2⟩ := d.2 c hc ht
    exact ⟨x + 1, b, β, a, h1, h2, hQ⟩

/-- The children's loop's arguments: child `x` of `c`, the carried claims' table `24·c` words of
`Q` at `β`. -/
def L5Inv (Q : ℕ → Prop) (args : List E) : Prop :=
  ∃ x c β, args.getD 0 0 = gen ^ x ∧ args.getD 1 0 = gen ^ c ∧ args.getD 9 0 = gen ^ β ∧ x < c ∧
    ∀ i, β ≤ i → i < β + 24 * c → Q i

theorem l5LoopStep {rd : Reader} {Q : ℕ → Prop} :
    LoopStep rd Q (name% «main_loop4») fn% «main_loop4» (L5Inv Q) := by
  intro σ es vs hw hh hI
  rw [loop4_found.2.2] at hw
  rw [loop4_found.2.1] at hI
  obtain ⟨x, c, β, h0, h1, h9, hxc, hQ⟩ := hI
  have d := l5Step hw hh (x := x) (c := c) (β := β) h0 h1 h9 hxc
  refine ⟨fun A hA => (d.1 A hA).imp id fun ⟨i, hi, h1, h2⟩ => ⟨i, hi, hQ i h1 h2⟩,
    fun c' hc hf ht => ?_⟩
  obtain ⟨e0, e1, e9, hlt⟩ := d.2 c' hc hf ht
  exact ⟨x + 1, c, β, e0, e1, e9, hlt, hQ⟩

/-! ## `main` -/

section Main

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- The atoms of `main`'s path its loop helpers' tables rest on. -/
def mHAtoms : List Atom := [
  .touch (.n 8) (.n 0), .touch (.n 9) (.n 1), .touch (.n 11) (.n 3), .touch (.n 12) (.n 4),
  .rangeCheck (.n 6) (.n 15) (.n 16) (.n 17) (.n 14),
  .mul (.n 22) (.n 0) (.n 1), .mul (.n 23) (.n 3) (.n 4),
  .mul (.n 29) (.n 22) (.n 22), .mul (.n 30) (.n 29) (.n 29),
  .mul (.n 32) (.n 23) (.n 23), .mul (.n 33) (.n 32) (.n 32),
  .const (.n 39) (word 1 0), .add (.n 40) (.n 39) (.n 1), .const (.n 41) (word 1 0),
  .const (.n 42) (word 1 0), .add (.n 43) (.n 42) (.n 4), .const (.n 44) (word 1 0),
  .mul (.n 390) (.n 6) (.n 6), .mul (.n 391) (.n 390) (.n 6), .mul (.n 392) (.n 391) (.n 391),
  .mul (.n 393) (.n 392) (.n 392), .mul (.n 394) (.n 393) (.n 393),
  .const (.n 400) (word 1 0), .add (.n 401) (.n 400) (.n 6), .const (.n 402) (word 1 0)]

theorem mHAtoms_mem : ∀ a ∈ mHAtoms, a ∈ atomsIn mPre ∨ a ∈ atomsIn mMid := by decide +kernel

theorem mEvs_atom {σ : Val} {a : Atom} (h : a ∈ atomsIn mPre ∨ a ∈ atomsIn mMid) :
    Ev.atom a ∈ mEvs σ := by
  unfold mEvs
  rcases h with h | h
  · have hm : Ev.atom a ∈ mPre.flatMap (slEvs σ) :=
      List.mem_flatMap.mpr ⟨_, atom_mem_of_atomsIn' h, List.mem_singleton_self _⟩
    exact List.mem_append_left _ hm
  · have hm : Ev.atom a ∈ mMid.flatMap (slEvs σ) :=
      List.mem_flatMap.mpr ⟨_, atom_mem_of_atomsIn' h, List.mem_singleton_self _⟩
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_append_left _ hm)))

theorem mEvs_alloc {σ : Val} {d s : V} (h : ((d, .inr s) : V × (ℕ ⊕ V)) ∈ mPre.filterMap Stmt.allocSz ∨
    ((d, .inr s) : V × (ℕ ⊕ V)) ∈ mMid.filterMap Stmt.allocSz) : Ev.atom (.hint (.allocDyn d s)) ∈ mEvs σ := by
  have hst : ∀ st : Stmt, Stmt.allocSz st = some (d, .inr s) → st = .atom (.hint (.allocDyn d s)) := by
    intro st hs
    rcases st with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _⟩ | _⟩ | _ | _ | _ | _ | _ | _ <;>
      simp_all [Stmt.allocSz]
  apply mEvs_atom
  rcases h with h | h
  · obtain ⟨st, hm, hs⟩ := List.mem_filterMap.mp h
    exact Or.inl (mem_atomsIn' (hst st hs ▸ hm))
  · obtain ⟨st, hm, hs⟩ := List.mem_filterMap.mp h
    exact Or.inr (mem_atomsIn' (hst st hs ▸ hm))

/-- **`main`'s calls of its loop helpers writing into its buffers.** -/
theorem mEvs_callsX {σ : Val} {c : Call} (hc : c ∈ calls (mEvs σ)) (hx : c.f ∈ hintsX) :
    c = ⟨name% «main_loop0», [.n 41, .n 1, .n 31, .n 0], [], decide (σ (.n 40) ≠ 0)⟩ ∨
      c = ⟨name% «main_loop1», [.n 44, .n 4, .n 34, .n 3], [], decide (σ (.n 43) ≠ 0)⟩ ∨
      c = ⟨name% «main_loop4», [.n 402, .n 6, .n 398, .n 31, .n 45, .n 22, .n 34, .n 46, .n 23,
        .n 395, .n 364, .n 26, .n 27, .n 383, .n 28, .n 389], [], decide (σ (.n 401) ≠ 0)⟩ := by
  obtain ⟨s1, s2, s2', s3, s4, s5, s6⟩ := mBlocks_straight
  have e1 := (straight_parts σ _ s1).2.2.2
  have e2 := (straight_parts σ _ s2).2.2.2
  have e2' := (straight_parts σ _ s2').2.2.2
  have e3 := (straight_parts σ _ s3).2.2.2
  have e4 := (straight_parts σ _ s4).2.2.2
  have e5 := (straight_parts σ _ s5).2.2.2
  have e6 := (straight_parts σ _ s6).2.2.2
  rw [mPre_calls] at e1
  rw [mDa_calls] at e2
  rw [mDaZ_calls] at e2'
  rw [mMid_calls] at e3
  rw [mLeaf_calls] at e4
  rw [mAgg_calls] at e5
  rw [mPost_calls] at e6
  unfold mEvs at hc
  simp only [calls, List.filterMap_append] at hc e1 e2 e2' e3 e4 e5 e6
  have hinK : ∀ (c : V) (xs : List Ev), List.filterMap Ev.call? (Ev.inK c :: xs) =
      List.filterMap Ev.call? xs := fun _ _ => rfl
  simp only [hinK] at hc
  simp only [hintsX, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases List.mem_append.mp hc with hc | hc
  · rw [e1] at hc
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, mkCall] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  rcases List.mem_append.mp hc with hc | hc
  · split at hc
    · rw [e2] at hc; simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false, mkCall] at hc; subst hc; simp_all
    · rw [e2'] at hc; exact absurd hc List.not_mem_nil
  rcases List.mem_append.mp hc with hc | hc
  · rw [e3] at hc
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, mkCall] at hc
    subst hc; simp
  rcases List.mem_append.mp hc with hc | hc
  · split at hc
    · rw [e4] at hc; exact absurd hc List.not_mem_nil
    · rw [e5] at hc; simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false, mkCall] at hc; subst hc; simp_all
  · rw [e6] at hc
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, mkCall] at hc
    subst hc; simp_all


theorem gpow_of_loadHolds {κ : ℕ} (hκ : κ < 64) {M : MemoryImage κ} {x d : E}
    (h : LoadHolds M.read x 0 d) : ∃ i < 2 ^ κ, x = gen ^ i := by
  obtain ⟨hk, hr⟩ := h
  obtain ⟨⟨i, hi⟩, he⟩ := read_some_gpow hκ hr
  refine ⟨i, hi, ?_⟩
  obtain ⟨a, rfl⟩ := (isInK_iff x).mp hk
  rw [gen_pow_eq_ofK]
  congr 1
  simpa [Parameters.addressOfIndex] using he

theorem gen_one_add_ne {b : ℕ} (h : 1 + gen ^ b ≠ 0) : 0 < b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [pow_zero, e_add_eq_zero_iff.mpr rfl] at h; exact absurd rfl h
  · exact hb

/-- `main`'s callees, its loop helpers writing into its buffers by trees `HintsQ` on their
arguments. -/
theorem hintsQKids_main {P : Core.Program} {rd : Reader} {Q : ℕ → Prop} {S X : String → Prop}
    (hS : HintsClosed P S) : ∀ (ks : List Tree) (σ : Val) (cs : List Call) (ps : List (ℕ × ℕ)),
      Tree.KidsValid P rd σ cs ks → Tree.BufsOkKids P ks → Tree.PlacedKids P fs cert ps ks →
      (∀ c ∈ cs, X c.f ∨ S c.f) →
      (∀ c ∈ cs, X c.f → c.taken = true → ∀ (k : Tree) (p : ℕ × ℕ), k.name = c.f →
        k.Valid P rd (c.args.map σ) (c.rets.map σ) → k.BufsOk P → k.Placed P fs cert p →
          k.HintsQ P fs cert Q p) →
      Tree.HintsQKids P fs cert Q ps ks
  | [], _, _, _, _, _, _, _, _ => hintsQKids_nil
  | _ :: _, _, _, [], _, _, _, _, _ => by rw [Tree.HintsQKids]; trivial
  | k :: ks, σ, c :: cs, p :: ps, ⟨hn, hc, hks⟩, hb, hp, hS', hX => by
      rw [Tree.BufsOkKids] at hb
      rw [placedKids_cons] at hp
      rw [hintsQKids_cons]
      refine ⟨?_, hintsQKids_main hS ks σ cs ps hks hb.2 hp.2
        (fun c' h => hS' c' (List.mem_cons_of_mem _ h)) (fun c' h => hX c' (List.mem_cons_of_mem _ h))⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        rcases hS' c List.mem_cons_self with hcx | hcs
        · exact hX c List.mem_cons_self hcx ht k p hn hc hb.1 hp.1
        · exact hintsQ_of_closed hS Q k p hc hb.1 hp.1 (hn ▸ hcs)
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨_, _, rfl⟩, -⟩ := hc
        exact hintsQ_phantom
  | _ :: _, _, [], _ :: _, h, _, _, _, _ => h.elim

theorem pow30 {a b : ℕ} (ha : a < 2 ^ 30) (hb : b < 2 ^ 30) : 24 * (a + b) < 2 ^ 64 - 1 := by
  have : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
  have : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  omega

/-- **`main`'s heap hints**: `main`'s tree on a memory image of at most `2^30` words, its loads in
its data or its header, has its heap hints there too. -/
theorem main_hintsIn {κ : ℕ} (hκ : κ ≤ 30) {M : MemoryImage κ} {t : Tree} (hn : t.name = "main")
    (hv : t.Valid coreProgram M.read [] []) (hb : t.BufsOk coreProgram)
    (hp : t.Placed coreProgram fs cert (0, t.block fs coreProgram.loop))
    (hl : t.LoadsIn coreProgram fs cert (fun i => i < 2) (0, t.block fs coreProgram.loop)) :
    t.HintsIn coreProgram fs cert (fun i => i < 2) (0, t.block fs coreProgram.loop) := by
  cases t with
  | phantom f σ => exact hv.elim
  | node f σ bufs kids =>
  have hf : f = "main" := hn
  subst hf
  have hv' := hv
  obtain ⟨fn, hfn, -, es, vs, hw, -, hes, hk⟩ := hv'
  obtain rfl : fn = fn% «main» := Option.some.inj (hfn.symm.trans find_main)
  rw [walk_main] at hw
  obtain ⟨rfl, -⟩ : mEvs σ = es ∧ ([] : List V) = vs := by cases hw; exact ⟨rfl, rfl⟩
  have hev : (Memory.Tree.node "main" σ bufs kids).events coreProgram = mEvs σ :=
    events_node find_main (walk_main σ)
  generalize hp0 : (0, (Memory.Tree.node "main" σ bufs kids).block fs coreProgram.loop) = p at hp hl ⊢
  refine hintsIn_of_hintsQ _ _ (fun i => ownData cert p.1 p.2 "main" bufs (mEvs σ) i) _ hl
    (fun i hi => Or.inl (data_node.mpr (Or.inl (by rw [hev]; exact hi)))) ?_
  rw [hintsQ_node]
  refine ⟨nodeHints_of_check hv hb hp fun fn hf => main_hintsOk hf, ?_⟩
  have hbo := hb
  rw [Tree.BufsOk, hev] at hbo
  have hp' := hp
  rw [placed_node, hev] at hp'
  have hκ64 : κ < 64 := by omega
  have h2κ : (2 : ℕ) ^ κ ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) hκ
  have hall : ∀ a ∈ mHAtoms, a.Holds M.read σ := fun a ha => hes _ (mEvs_atom (mHAtoms_mem a ha))
  simp only [mHAtoms, List.forall_mem_cons, Atom.Holds] at hall
  obtain ⟨t8, t9, t11, t12, ⟨r6, -⟩, m22, m23, m29, m30, m32, m33, c39, a40, c41, c42, a43, c44,
    m390, m391, m392, m393, m394, c400, a401, c402⟩ := hall
  rw [word_one] at c39 c41 c42 c44 c400 c402
  obtain ⟨a, ha, h0⟩ := gpow_of_loadHolds hκ64 t8
  obtain ⟨b, hb1, h1⟩ := gpow_of_loadHolds hκ64 t9
  obtain ⟨a', ha', h3⟩ := gpow_of_loadHolds hκ64 t11
  obtain ⟨b', hb', h4⟩ := gpow_of_loadHolds hκ64 t12
  obtain ⟨c6, hc6, h6⟩ := gpow_of_loadHolds hκ64 r6
  obtain ⟨s1, -, -, s3, -, -, -⟩ := mBlocks_allocs
  have hbuf : ∀ {d s : V}, ((d, .inr s) : V × (ℕ ⊕ V)) ∈ mPre.filterMap Stmt.allocSz ∨
      ((d, .inr s) : V × (ℕ ⊕ V)) ∈ mMid.filterMap Stmt.allocSz → ∀ {n : ℕ}, σ s = gen ^ n →
        n < 2 ^ 64 - 1 → ∃ β, σ d = gen ^ β ∧
          ∀ i, β ≤ i → i < β + n → ownData cert p.1 p.2 "main" bufs (mEvs σ) i := by
    intro d s hm n hs hn
    obtain ⟨β, hβ, hz⟩ := alloc_words hp'.1.1 hbo.1 (mEvs_alloc hm) rfl rfl
    rw [hs, gen_pow_eq_ofK, logG_spec hn] at hz
    exact ⟨β, by rw [hβ, gen_pow_eq_ofK], fun i h1 h2 => Or.inl ⟨_, hz, h1, h2⟩⟩
  obtain ⟨β0, hβ0, hQ0⟩ := hbuf (d := .n 31) (s := .n 30) (Or.inl (by rw [s1]; exact List.mem_cons_self))
    (n := 4 * (a + b)) (by rw [m30, m29, m22, h0, h1, ← pow_add, ← pow_add, ← pow_add]; exact congrArg (gen ^ ·) (by ring))
    (by have := pow30 (lt_of_lt_of_le ha h2κ) (lt_of_lt_of_le hb1 h2κ); omega)
  obtain ⟨β1, hβ1, hQ1⟩ := hbuf (d := .n 34) (s := .n 33)
    (Or.inl (by rw [s1]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    (n := 4 * (a' + b')) (by rw [m33, m32, m23, h3, h4, ← pow_add, ← pow_add, ← pow_add]; exact congrArg (gen ^ ·) (by ring))
    (by have := pow30 (lt_of_lt_of_le ha' h2κ) (lt_of_lt_of_le hb' h2κ); omega)
  obtain ⟨β4, hβ4, hQ4⟩ := hbuf (d := .n 395) (s := .n 394)
    (Or.inr (by rw [s3]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (n := 24 * c6) (by rw [m394, m393, m392, m391, m390, h6, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add, ← pow_add]; exact congrArg (gen ^ ·) (by ring))
    (by have := pow30 (lt_of_lt_of_le hc6 h2κ) (lt_of_lt_of_le hc6 h2κ); omega)
  rw [Tree.BufsOk] at hb
  rw [placed_node] at hp
  refine hintsQKids_main (X := (· ∈ hintsX)) coreProgram_hintsClosed kids σ _ _ hk hb.2 hp.2
    (fun c hc => main_callees find_main c.f (walk_callees (σ := σ) _ (by rw [walk_main]; exact hc)))
    fun c hc hx ht k q hkn hkv hkb hkp => ?_
  rcases mEvs_callsX hc hx with rfl | rfl | rfl
  · simp only [decide_eq_true_eq] at ht
    rw [a40, c39, h1] at ht
    exact hintsQ_loop loop0_found.1 coreProgram_hintsClosed
      (hintsX_callees (by simp [hintsX]) loop0_found.1) (dupLoopStep loop0_found.2) k q hkv hkb hkp hkn
      ⟨0, b, β0, a, by simp [c41, h1, hβ0, h0], gen_one_add_ne ht, hQ0⟩
  · simp only [decide_eq_true_eq] at ht
    rw [a43, c42, h4] at ht
    exact hintsQ_loop loop1_found.1 coreProgram_hintsClosed
      (hintsX_callees (by simp [hintsX]) loop1_found.1) (dupLoopStep loop1_found.2) k q hkv hkb hkp hkn
      ⟨0, b', β1, a', by simp [c44, h4, hβ1, h3], gen_one_add_ne ht, hQ1⟩
  · simp only [decide_eq_true_eq] at ht
    rw [a401, c400, h6] at ht
    exact hintsQ_loop loop4_found.1 coreProgram_hintsClosed
      (hintsX_callees (by simp [hintsX]) loop4_found.1) l5LoopStep k q hkv hkb hkp hkn
      ⟨0, c6, β4, by simp [c402], by simp [h6], by simp [hβ4], gen_one_add_ne ht, hQ4⟩

end Main

end
end LeanVM.Guest.B1.Main
