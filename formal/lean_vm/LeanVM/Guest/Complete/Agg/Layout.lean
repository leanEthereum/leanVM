module

public import LeanVM.Guest.Complete.Agg.Wins
public import LeanVM.Guest.Memory.Straight
public import LeanVM.Guest.Memory.Restrict
public import LeanVM.Guest.Complete.MainRunFacts

/-!
# `aggregate_claims`' `HeapBuf`s

On `m` children, `aggregate_claims` allocates, in order, `bc_msgs` (`51`), `fresh_row` (`m`),
`carried_row` (`m`), `absorb` (`13 (m + 1)`), `col` (`6`), `eq_col_tree` (`126`), `fresh_val` (`m`),
`bc_chain` (`2 (m + 1)`), `bc_point` (`25`), `bc_point1` (`25`) and `bc_wsum` (`m + 1`): `aBufs m`.

`allocs_mapAtom`: a run's sizes are its allocating atoms' (`allocK`), each a constant or a value's
`logG`. `aW_allocK`: each run window's allocating atoms, by the kernel. `aVal_sizes`: on `aVal` with
`n_children_g = g^m` the dynamic sizes are `g^(13 (m + 1))`, `g^(2 (m + 1))`, `g^(m + 1)`.
`aWalk`: the body walks to its windows' events (`evW1`), each guarded call taken or skipped by its
guard. `aAllocs`: its sizes are `aBufs m`.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC LeanVM.Guest.B1.Main LeanVM.Guest.Complete
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

attribute [local instance high] LeanVM.Guest.Core.instDecidableEqAtom

/-! ## A run's sizes -/

/-- An atom's `HeapBuf` size: a constant, or a value's. -/
def allocK : Atom → Option (ℕ ⊕ V)
  | .hint (.alloc _ n) => some (.inl n)
  | .hint (.allocDyn _ s) => some (.inr s)
  | _ => none

/-- A size's words on `σ`. -/
noncomputable def allocSz (σ : Val) : ℕ ⊕ V → ℕ
  | .inl n => n
  | .inr s => logG (σ s)

theorem alloc?_atom (σ : Val) (a : Atom) : Ev.alloc? σ (.atom a) = (allocK a).map (allocSz σ) := by
  cases a <;> try rfl
  rename_i h
  cases h <;> rfl

/-- **A run's sizes** are its allocating atoms'. -/
theorem allocs_mapAtom (σ : Val) : ∀ as : List Atom,
    allocs σ (as.map Ev.atom) = (as.filterMap allocK).map (allocSz σ)
  | [] => rfl
  | a :: as => by
    have ih := allocs_mapAtom σ as
    simp only [allocs] at ih ⊢
    rw [List.map_cons, List.filterMap_cons, alloc?_atom, List.filterMap_cons]
    cases allocK a <;> simp [ih]

/-- `aggregate_claims`' `HeapBuf` sizes on `m` children, in allocation order. -/
def aBufs (m : ℕ) : List ℕ := [51, m, m, 13 * (m + 1), 6, 126, m, 2 * (m + 1), 25, 25, m + 1]

set_option maxRecDepth 200000 in
/-- **The run windows' allocating atoms.** -/
theorem aW_allocK :
    (atomsOf ((aggP.drop 0).take 42)).filterMap allocK = [.inl 51, .inr (.n 0), .inr (.n 0), .inr (.n 29)] ∧
    (atomsOf ((aggP.drop 43).take 433)).filterMap allocK = [.inl 6, .inl 126, .inr (.n 0)] ∧
    (atomsOf ((aggP.drop 477).take 11)).filterMap allocK = [.inr (.n 448)] ∧
    (atomsOf ((aggP.drop 489).take 6)).filterMap allocK = [.inl 25] ∧
    (atomsOf ((aggP.drop 496).take 132)).filterMap allocK = [.inl 25, .inr (.n 567)] ∧
    (atomsOf ((aggP.drop 629).take 55)).filterMap allocK = [] := by
  decide +kernel

/-! ## The sizes' values -/

section
variable {rd0 : Reader} {o : ℕ → E} {args : List E}

theorem aGood_const (hl : args.length = 6) {d : ℕ} {e : E} (hm : Atom.const (.n d) e ∈ atomsOf aggP) :
    aVal rd0 o args (.n d) = e :=
  aVal_good hl _ (atom_mem_of_atomsOf hm)

theorem aGood_mul (hl : args.length = 6) {d x y : ℕ} (hm : Atom.mul (.n d) (.n x) (.n y) ∈ atomsOf aggP)
    (hx : x < d) (hy : y < d) : aVal rd0 o args (.n d) = aVal rd0 o args (.n x) * aVal rd0 o args (.n y) := by
  have h := aVal_good (rd0 := rd0) (o := o) hl _ (atom_mem_of_atomsOf hm)
  simp only [GoodS, Good] at h
  split_ifs at h with hc
  · exact h
  · exact (hc ⟨hx, hy⟩).elim

set_option maxRecDepth 200000 in
theorem aSize_mems :
    Atom.const (.n 23) (word 2 0) ∈ atomsOf aggP ∧ Atom.mul (.n 24) (.n 0) (.n 23) ∈ atomsOf aggP ∧
    Atom.mul (.n 25) (.n 24) (.n 24) ∈ atomsOf aggP ∧ Atom.mul (.n 26) (.n 25) (.n 24) ∈ atomsOf aggP ∧
    Atom.mul (.n 27) (.n 26) (.n 26) ∈ atomsOf aggP ∧ Atom.mul (.n 28) (.n 27) (.n 27) ∈ atomsOf aggP ∧
    Atom.mul (.n 29) (.n 28) (.n 24) ∈ atomsOf aggP ∧ Atom.const (.n 446) (word 2 0) ∈ atomsOf aggP ∧
    Atom.mul (.n 447) (.n 0) (.n 446) ∈ atomsOf aggP ∧ Atom.mul (.n 448) (.n 447) (.n 447) ∈ atomsOf aggP ∧
    Atom.const (.n 566) (word 2 0) ∈ atomsOf aggP ∧ Atom.mul (.n 567) (.n 0) (.n 566) ∈ atomsOf aggP := by
  decide +kernel

/-- **The dynamic sizes' values** on `n_children_g = g^m`. -/
theorem aVal_sizes (hl : args.length = 6) {m : ℕ} (h0 : args.getD 0 0 = gen ^ m) :
    aVal rd0 o args (.n 29) = gen ^ (13 * (m + 1)) ∧ aVal rd0 o args (.n 448) = gen ^ (2 * (m + 1)) ∧
      aVal rd0 o args (.n 567) = gen ^ (m + 1) := by
  obtain ⟨c23, m24, m25, m26, m27, m28, m29, c446, m447, m448, c566, m567⟩ := aSize_mems
  have p0 : aVal rd0 o args (.n 0) = gen ^ m := by rw [aVal_param hl (by omega), h0]
  have v24 : aVal rd0 o args (.n 24) = gen ^ (m + 1) := by
    rw [aGood_mul hl m24 (by omega) (by omega), p0, aGood_const hl c23, word_gen, gen_pow_mul_gen]
  have v567 : aVal rd0 o args (.n 567) = gen ^ (m + 1) := by
    rw [aGood_mul hl m567 (by omega) (by omega), p0, aGood_const hl c566, word_gen, gen_pow_mul_gen]
  have v447 : aVal rd0 o args (.n 447) = gen ^ (m + 1) := by
    rw [aGood_mul hl m447 (by omega) (by omega), p0, aGood_const hl c446, word_gen, gen_pow_mul_gen]
  refine ⟨?_, ?_, v567⟩
  · rw [aGood_mul hl m29 (by omega) (by omega), aGood_mul hl m28 (by omega) (by omega),
      aGood_mul hl m27 (by omega) (by omega), aGood_mul hl m26 (by omega) (by omega),
      aGood_mul hl m25 (by omega) (by omega), v24]
    simp only [← pow_add]
    exact congrArg (gen ^ ·) (by ring)
  · rw [aGood_mul hl m448 (by omega) (by omega), v447]
    simp only [← pow_add]
    exact congrArg (gen ^ ·) (by ring)

end

/-! ## The body's events -/

/-- A window's events on `σ`: a run's atoms; a call statement's call; a guarded call's selector,
then its call or its skip. -/
def evW1 (σ : Val) : W1 → List Ev
  | .run as => as.map Ev.atom
  | .call s => match s with
    | .call g a r => [.call g a r]
    | _ => []
  | .cif c g args => [.inK c, if σ c = 0 then .skip g args else .call g args []]

/-- A `call` statement. -/
def isCallS : Stmt → Bool
  | .call .. => true
  | _ => false

/-- The windows' call statements are `call`s. -/
def callsPlain (ws : List W1) : Bool := ws.all fun
  | .call s => isCallS s
  | _ => true

theorem walk_flatW1 (σ : Val) : ∀ ws : List W1, callsPlain ws = true →
    walk σ (flatW1 ws) = .fall (ws.flatMap (evW1 σ))
  | [], _ => by simp [flatW1, walk]
  | x :: ws, h => by
    simp only [callsPlain, List.all_cons, Bool.and_eq_true] at h
    have ih := walk_flatW1 σ ws h.2
    rw [flatW1_cons, walk_append, List.flatMap_cons, ih]
    cases x with
    | run as =>
      simp only [W1.stmts]
      rw [walk_atomsF]
      simp [Out.seq, Out.pre, evW1]
    | call s =>
      have hx := h.1
      cases s <;> simp only [isCallS, Bool.false_eq_true] at hx
      rename_i g a r
      simp only [W1.stmts]
      rw [walk_call]
      simp [Out.seq, Out.pre, evW1]
    | cif c g args =>
      simp only [W1.stmts]
      rw [walk_callIf]
      simp [Out.seq, Out.pre, evW1]

theorem wAgg_plain : callsPlain wAgg = true := by decide +kernel

/-- **The body's events**: its windows'. -/
theorem aWalk (σ : Val) : aEs σ = wAgg.flatMap (evW1 σ) := by
  rw [aEs, ← wAgg_flat, walk_flatW1 σ wAgg wAgg_plain]
  rfl

/-- **`aggregate_claims`' sizes** on `n_children_g = g^m`, `m < 2^34`. -/
theorem aAllocs {rd0 : Reader} {o : ℕ → E} {args : List E} (hl : args.length = 6) {m : ℕ} (hm : m < 2 ^ 34)
    (h0 : args.getD 0 0 = gen ^ m) : allocs (aVal rd0 o args) (aEs (aVal rd0 o args)) = aBufs m := by
  obtain ⟨k0, k2, k4, k6, k8, k10⟩ := aW_allocK
  obtain ⟨s29, s448, s567⟩ := aVal_sizes (rd0 := rd0) (o := o) hl h0
  have p0 : aVal rd0 o args (.n 0) = gen ^ m := by rw [aVal_param hl (by omega), h0]
  have hc : ∀ (c : V) (g : String) (as : List V) (p : Prop) [Decidable p],
      allocs (aVal rd0 o args) [Ev.inK c, if p then Ev.skip g as else Ev.call g as []] = [] := by
    intro c g as p _
    split <;> rfl
  have hcall : ∀ (g : String) (a r : List V), allocs (aVal rd0 o args) [Ev.call g a r] = [] :=
    fun _ _ _ => rfl
  have h64 : (2 : ℕ) ^ 64 - 1 = 18446744073709551615 := by norm_num
  have hm' : m < 17179869184 := by simpa using hm
  rw [aWalk]
  simp only [wAgg, List.flatMap_cons, List.flatMap_nil, List.append_nil, allocs_append, aW0, aW1, aW2, aW3,
    aW4, aW5, aW6, aW7, aW8, aW9, aW10, evW1, allocs_mapAtom, k0, k2, k4, k6, k8, k10, hc, hcall,
    List.map_cons, List.map_nil, allocSz, p0, s29, s448, s567]
  rw [logG_gen_pow (by rw [h64]; omega), logG_gen_pow (by rw [h64]; omega), logG_gen_pow (by rw [h64]; omega),
    logG_gen_pow (by rw [h64]; omega)]
  rfl

end
end LeanVM.Guest.Complete.Agg
