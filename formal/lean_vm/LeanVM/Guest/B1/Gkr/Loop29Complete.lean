/-
  LeanVM.Guest.B1.Gkr.Loop29Complete

  `__loop36`, completely: eight GKR rounds from the record at `head·x^8` at every iteration give
  its relation from `1` below `half`.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop29
public import LeanVM.Guest.B1.Gkr.GkBody
public import LeanVM.Guest.B1.Common.Loops

/-!
# `__loop36`, completely (G:1869-1888)

An iteration of `__loop36` is B1-a's `gkBody 8` (the eight rounds between records) without its
returned `0`, renamed (`sh6`: the record, the row and the window table to the iteration's, the
others seven values on; `l29Body_eq`, by kernel evaluation), after the record's and the row's
pointers `head·x^8`, `ptrow·x^8`, and before the guard and the next call. The honest
valuation of an iteration (`l29Val`) takes the eight rounds' from `gk_body_holds` (`σgk`,
renamed), the pointers and the guard around them. `l29_complete`: when every iteration's eight
rounds hold (`TbGkrRoundsOut 8` at `head·g^(8j)`, `ptrow·g^(8j)`), the loop holds from `1` below
`g^h`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1

@[expose] public section

/-- `gkBody 8`'s values in an iteration: the record `head·x^8` (`8`), the row `ptrow·x^8` (`9`),
the window table (`4`), the others seven on. -/
def sh6 (v : V) : V :=
  if v.idx = 0 then .n 8 else if v.idx = 1 then .n 9 else if v.idx = 2 then .n 4
  else .n (v.idx + 7)

/-- The iteration's pointers. -/
def l29Pre : List Stmt :=
  [.atom (.mul (.n 5) (.n 0) (.n 0)), .atom (.mul (.n 6) (.n 5) (.n 5)),
    .atom (.mul (.n 7) (.n 6) (.n 6)), .atom (.mul (.n 8) (.n 2) (.n 7)),
    .atom (.mul (.n 9) (.n 3) (.n 7))]

/-- The guard and the next call's argument. -/
def l29Post : List Stmt :=
  [.atom (.const (.n 339) (word 2 0)), .atom (.mul (.n 340) (.n 0) (.n 339)),
    .atom (.add (.n 341) (.n 340) (.n 1)), .atom (.const (.n 342) (word 2 0)),
    .atom (.mul (.n 343) (.n 0) (.n 342))]

/-- `gkBody 8` but its returned `0`: the eight rounds between records. -/
def gk8Pre : List Stmt := ((gkBody 8).dropLast).dropLast

/-- The iteration's atoms. -/
def l29A : List Stmt := l29Pre ++ Stmt.renameList sh6 gk8Pre ++ l29Post

set_option maxRecDepth 100000 in
theorem l29Body_eq' : tbStmtsEqb l29Body
    (l29A ++ [.callIf (.n 341) "__loop36" [.n 343, .n 1, .n 2, .n 3, .n 4], .ret []]) = true := by
  decide +kernel

theorem l29Body_eq : l29Body =
    l29A ++ [.callIf (.n 341) "__loop36" [.n 343, .n 1, .n 2, .n 3, .n 4], .ret []] :=
  tbStmtsEqb_sound l29Body_eq'

/-- Every statement of `gk8Pre` is an atom over values `.n k`, `k ≤ 331`. -/
def gk4Ok : Stmt → Bool
  | .atom a => a.vals.all fun v => decide (v = .n v.idx) && decide (v.idx ≤ 331)
  | _ => false

set_option maxRecDepth 100000 in
theorem gk4_ok : gk8Pre.all gk4Ok = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gkBody4_eq : gkBody 8 = gk8Pre ++ [.atom (.const (.n 332) (word 0 0)), .ret [.n 332]] :=
  tbStmtsEqb_sound (by decide +kernel)

theorem atom_congr' {rd : Reader} {σ σ' : Val} {a : Atom} (h : ∀ v ∈ a.vals, σ v = σ' v) :
    a.Holds rd σ ↔ a.Holds rd σ' := by
  cases a with
  | keccak ins outs inOdd outOdd =>
    simp only [Atom.vals, List.mem_append] at h
    have hi : ins.map σ = ins.map σ' := List.map_congr_left fun v hv ↦ h v (.inl hv)
    have ho : outs.map σ = outs.map σ' := List.map_congr_left fun v hv ↦ h v (.inr hv)
    simp only [Atom.Holds, hi, ho]
  | frameAddr q run =>
    simp only [Atom.vals, List.mem_cons, forall_eq_or_imp] at h
    simp only [Atom.Holds, h.1]
    refine and_congr_right fun _ ↦ forall_congr' fun k ↦ forall_congr' fun hk ↦ ?_
    rw [h.2 _ (List.getElem_mem hk)]
  | hint => simp [Atom.Holds]
  | _ => simp_all [Atom.vals, Atom.Holds]

theorem mem_renameList {r : V → V} : ∀ {ss : List Stmt} {s : Stmt}, s ∈ Stmt.renameList r ss →
    ∃ t ∈ ss, s = t.rename r
  | [], _, h => absurd h (by simp [Stmt.renameList])
  | t :: ss, s, h => by
    simp only [Stmt.renameList, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨t, List.mem_cons_self, rfl⟩
    · obtain ⟨u, hu, rfl⟩ := mem_renameList h
      exact ⟨u, List.mem_cons_of_mem _ hu, rfl⟩

theorem l29A_atoms : AllAtoms l29A := by
  intro s hs
  simp only [l29A, List.mem_append] at hs
  rcases hs with (hs | hs) | hs
  · simp only [l29Pre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · obtain ⟨t, ht, rfl⟩ := mem_renameList hs
    have := List.all_eq_true.mp gk4_ok t ht
    cases t with
    | atom a => exact ⟨_, rfl⟩
    | _ => simp [gk4Ok] at this
  · simp only [l29Post, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- **The honest valuation of an iteration** at `x`, the eight rounds' `σgk` renamed. -/
def l29Val (x N head ptrow tabs : E) (σgk : Val) (v : V) : E :=
  if v.idx < 10 then [x, N, head, ptrow, tabs, x * x, x * x * (x * x),
    x * x * (x * x) * (x * x * (x * x)), head * (x * x * (x * x) * (x * x * (x * x))),
    ptrow * (x * x * (x * x) * (x * x * (x * x)))].getD v.idx 0
  else if v.idx ≤ 338 then σgk (.n (v.idx - 7))
  else [gen, x * gen, x * gen + N, gen, x * gen].getD (v.idx - 339) 0

theorem gkBody4_atoms {C : CallRel} {rd : Reader} {σ : Val}
    (h : Stmt.HoldsList C rd σ (gkBody 8) False (fun rs => rs = [0])) :
    ∀ a, Stmt.atom a ∈ gk8Pre → a.Holds rd σ := by
  have hA : AllAtoms gk8Pre := by
    intro t ht
    have := List.all_eq_true.mp gk4_ok t ht
    cases t with
    | atom a => exact ⟨_, rfl⟩
    | _ => simp [gk4Ok] at this
  rw [gkBody4_eq, holdsList_append, holdsList_atoms hA] at h
  exact h.1

set_option maxRecDepth 10000 in
/-- **An iteration of `__loop36`, completely.** -/
theorem l29_iter {rd : Reader} (x N head ptrow tabs : E)
    (hT : TbGkrRoundsOut 8 rd (head * (x * x * (x * x) * (x * x * (x * x))))
      (ptrow * (x * x * (x * x) * (x * x * (x * x))))) :
    AtomsBody rd [.n 0, .n 1, .n 2, .n 3, .n 4] l29A [x, N, head, ptrow, tabs] := by
  obtain ⟨σgk, hσv, h0, h1, h2, hh⟩ := gk_body_holds 8 (by norm_num) (by norm_num)
    (coreProgram.Rel rd) rd _ _ tabs ⟨rfl, hT⟩
  have hgk := gkBody4_atoms hh
  refine ⟨l29Val x N head ptrow tabs σgk, by simp [l29Val], fun a ha => ?_⟩
  simp only [l29A, List.mem_append] at ha
  rcases ha with (ha | ha) | ha
  · simp only [l29Pre, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp [Atom.Holds, l29Val]
  · obtain ⟨t, ht, he⟩ := mem_renameList ha
    cases t with
    | atom b =>
      simp only [Stmt.rename, Stmt.atom.injEq] at he
      subst he
      rw [Atom.holds_rename]
      refine (atom_congr' fun v hv => ?_).mpr (hgk b ht)
      have hok := List.all_eq_true.mp gk4_ok _ ht
      simp only [gk4Ok, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hvn, hvi⟩ := hok v hv
      show l29Val x N head ptrow tabs σgk (sh6 v) = σgk v
      rw [hσv v]
      by_cases e0 : v.idx = 0
      · simp [sh6, l29Val, e0, h0]
      by_cases e1 : v.idx = 1
      · simp [sh6, l29Val, e1, h1]
      by_cases e2 : v.idx = 2
      · simp [sh6, l29Val, e2, h2]
      have i1 : ¬ v.idx + 7 < 10 := by omega
      have i2 : v.idx + 7 ≤ 338 := by omega
      simp only [sh6, l29Val, e0, e1, e2, i1, i2, ↓reduceIte, Nat.add_sub_cancel]
    | _ =>
      have hok := List.all_eq_true.mp gk4_ok _ ht
      simp [gk4Ok] at hok
  · simp only [l29Post, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp [Atom.Holds, l29Val, tb_word_gen]

set_option maxRecDepth 10000 in
/-- **`__loop36`, completely**: eight rounds from the record at `head·g^(8j)` at every iteration
`j < h` give the loop from `1` below `g^h`. -/
theorem l29_complete {rd : Reader} {head ptrow tabs : E} {h : ℕ} (hpos : 0 < h) (hhb : h < 2 ^ 62)
    (hr : ∀ j < h, TbGkrRoundsOut 8 rd (head * gen ^ (8 * j)) (ptrow * gen ^ (8 * j))) :
    coreProgram.Rel rd "__loop36" [1, gen ^ h, head, ptrow, tabs] [] := by
  obtain ⟨fn, hf, hp, hb⟩ := l29Found
  rw [l29Body_eq] at hb
  have hstep : ∀ d x, coreProgram.relN rd (d + 1) "__loop36" (x :: [gen ^ h, head, ptrow, tabs]) [] ↔
      AtomsBody rd fn.params l29A (x :: [gen ^ h, head, ptrow, tabs]) ∧ IsInK (x * gen + gen ^ h) ∧
        (x * gen + gen ^ h ≠ 0 →
          coreProgram.relN rd d "__loop36" (x * gen :: [gen ^ h, head, ptrow, tabs]) []) := by
    intro d x
    refine loop_step_atoms hf hb l29A_atoms (fun σ hpar hall => ?_) d
    rw [hp] at hpar
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
    obtain ⟨h0, h1, h2, h3, h4⟩ := hpar
    have m := fun a (ha : Stmt.atom a ∈ l29Post) => hall a (by
      simp only [l29A, List.mem_append]; exact Or.inr ha)
    simp only [l29Post, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq,
      forall_eq_or_imp, forall_eq, Atom.Holds] at m
    obtain ⟨c339, m340, a341, c342, m343⟩ := m
    rw [tb_word_gen] at c339 c342
    refine ⟨by rw [a341, m340, c339, h0, h1], ?_⟩
    simp only [List.map_cons, List.map_nil, m343, c342, h0, h1, h2, h3, h4]
  rw [← pow_zero gen]
  refine (loop_iff hstep 0).mpr ⟨h, hpos, rfl, first_hit_of_lt (by unfold ordG; omega) rfl,
    fun j _ hj => ?_⟩
  rw [hp]
  apply l29_iter
  have := hr j hj
  rwa [show gen ^ j * gen ^ j * (gen ^ j * gen ^ j) * (gen ^ j * gen ^ j * (gen ^ j * gen ^ j)) =
    gen ^ (8 * j) by ring]

end
end LeanVM.Guest.B1.Tables
