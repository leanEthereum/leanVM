/-
  LeanVM.Guest.B1.Gkr.Loop29Complete

  `verify_bus_gkr_loop0_loop0`, completely: two GKR rounds from the record at `head·x` at every
  iteration give its relation from `1` below `x_pair`.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop29
public import LeanVM.Guest.B1.Sumcheck.Gkr
public import LeanVM.Guest.B1.Common.Loops
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_bus_gkr_loop0_loop0`, completely (G:1967-1989)

An iteration of `verify_bus_gkr_loop0_loop0` is B1-a's `gkPre true 2` renamed (`l29Sh`, `Loop29`),
after the record's and the row's pointers `head·x`, `ptrow·x²` and before the guard and the next
call. The honest valuation of an iteration (`l29Val`) takes the two rounds' from `gk_pre_holds`
(`σgk`, renamed), the pointers and the guard around them. `l29_complete`: when every iteration's
two rounds hold (`TbGkrRoundsOut 2 1` at `head·g^j`, `ptrow·g^(2j)`), the loop holds from `1`
below `g^h`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1

@[expose] public section

/-- Every statement of `gkPre true 2` is an atom over values `.n k`, `k ≤ 92`, never the window
table's or the stream's. -/
def gk2Ok : Stmt → Bool
  | .atom a => a.vals.all fun v => decide (v = .n v.idx) && decide (v.idx ≤ 92) &&
      decide (v.idx ≠ 3) && decide (v.idx ≠ 4)
  | _ => false

set_option maxRecDepth 100000 in
theorem gk2_ok : (gkPre true 2).all gk2Ok = true := by decide +kernel

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
    rcases hs with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · obtain ⟨t, ht, rfl⟩ := mem_renameList hs
    have := List.all_eq_true.mp gk2_ok t ht
    cases t with
    | atom a => exact ⟨_, rfl⟩
    | _ => simp [gk2Ok] at this
  · simp only [l29Post, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- **The honest valuation of an iteration** at `x`, the two rounds' `σgk` renamed. -/
def l29Val (x N head ptrow tabs : E) (σgk : Val) (v : V) : E :=
  if v.idx < 8 then [x, N, head, ptrow, tabs, head * x, ptrow * x, ptrow * x * x].getD v.idx 0
  else if v.idx < 13 then σgk (.n (v.idx - 3))
  else if v.idx = 13 then σgk (.n 2)
  else if v.idx ≤ 96 then σgk (.n (v.idx - 4))
  else [gen, x * gen, x * gen + N, gen, x * gen].getD (v.idx - 97) 0

/-- Two rounds between records `1` apart, as B1-a's `GkrRoundsOut` on the record's cursor. -/
theorem gkOut_of_tb {rd : Reader} {rec pt : E} (h : TbGkrRoundsOut 2 1 rd rec pt) :
    ∃ cur, GkrRoundsOut 2 rd rec pt cur ∧ LoadHolds rd rec 4310 cur := by
  obtain ⟨cap, cur, claim, cs, es, h1, hc, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨cur, ⟨cap, claim, cs, es, h1, h3, h4, h5, h6, h7, h8, h9, fun h ↦ absurd h (by decide), h10, h11, h12⟩, hc⟩

set_option maxRecDepth 10000 in
/-- **An iteration of `verify_bus_gkr_loop0_loop0`, completely.** -/
theorem l29_iter {rd : Reader} (x N head ptrow tabs : E)
    (hT : TbGkrRoundsOut 2 1 rd (head * x) (ptrow * x * x)) :
    AtomsBody rd [.n 0, .n 1, .n 2, .n 3, .n 4] l29A [x, N, head, ptrow, tabs] := by
  obtain ⟨cur, hout, hcur⟩ := gkOut_of_tb hT
  obtain ⟨σgk, hσv, h0, h1, h2, -, -, -, hh⟩ := gk_pre_holds true 2 (by norm_num) (by norm_num)
    (coreProgram.Rel rd) rd _ _ cur tabs 0 hout (fun _ ↦ hcur)
  have hgk : ∀ a, Stmt.atom a ∈ gkPre true 2 → a.Holds rd σgk := by
    have hA : AllAtoms (gkPre true 2) := by
      intro t ht
      have := List.all_eq_true.mp gk2_ok t ht
      cases t with
      | atom a => exact ⟨_, rfl⟩
      | _ => simp [gk2Ok] at this
    have := hh True (fun _ ↦ True) trivial
    rw [holdsList_atoms hA] at this
    exact this.1
  refine ⟨l29Val x N head ptrow tabs σgk, by simp [l29Val], fun a ha => ?_⟩
  simp only [l29A, List.mem_append] at ha
  rcases ha with (ha | ha) | ha
  · simp only [l29Pre, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl | rfl <;> simp [Atom.Holds, l29Val]
  · obtain ⟨t, ht, he⟩ := mem_renameList ha
    cases t with
    | atom b =>
      simp only [Stmt.rename, Stmt.atom.injEq] at he
      subst he
      rw [Atom.holds_rename]
      refine (atom_congr' fun v hv => ?_).mpr (hgk b ht)
      have hok := List.all_eq_true.mp gk2_ok _ ht
      simp only [gk2Ok, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨hvn, hvi⟩, h3⟩, h4⟩ := hok v hv
      show l29Val x N head ptrow tabs σgk (l29Sh v) = σgk v
      rw [hσv v]
      by_cases e0 : v.idx = 0
      · simp [l29Sh, l29Val, e0, h0]
      by_cases e1 : v.idx = 1
      · simp [l29Sh, l29Val, e1, h1]
      by_cases e2 : v.idx = 2
      · simp [l29Sh, l29Val, e2, h2]
      by_cases e5 : v.idx < 10
      · have i1 : ¬ v.idx + 3 < 8 := by omega
        have i2 : v.idx + 3 < 13 := by omega
        have i5 : ¬ v.idx < 5 := by omega
        simp only [l29Sh, l29Val, e0, e1, e2, e5, i1, i2, i5, ↓reduceIte, Nat.add_sub_cancel]
      · have i1 : ¬ v.idx + 4 < 8 := by omega
        have i2 : ¬ v.idx + 4 < 13 := by omega
        have i3 : ¬ v.idx + 4 = 13 := by omega
        have i4 : v.idx + 4 ≤ 96 := by omega
        have i5 : ¬ v.idx < 5 := by omega
        simp only [l29Sh, l29Val, e0, e1, e2, e5, i1, i2, i3, i4, i5, ↓reduceIte, Nat.add_sub_cancel]
    | _ =>
      have hok := List.all_eq_true.mp gk2_ok _ ht
      simp [gk2Ok] at hok
  · simp only [l29Post, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp [Atom.Holds, l29Val, tb_word_gen]

set_option maxRecDepth 10000 in
/-- **`verify_bus_gkr_loop0_loop0`, completely**: two rounds from the record at `head·g^j` at every
iteration `j < h` give the loop from `1` below `g^h`. -/
theorem l29_complete {rd : Reader} {head ptrow tabs : E} {h : ℕ} (hpos : 0 < h) (hhb : h < 2 ^ 62)
    (hr : ∀ j < h, TbGkrRoundsOut 2 1 rd (head * gen ^ j) (ptrow * gen ^ (2 * j))) :
    coreProgram.Rel rd name% «verify_bus_gkr_loop0_loop0» [1, gen ^ h, head, ptrow, tabs] [] := by
  obtain ⟨fn, hf, hp, hb⟩ := l29Found
  rw [l29Body] at hb
  have hstep : ∀ d x, coreProgram.relN rd (d + 1) name% «verify_bus_gkr_loop0_loop0» (x :: [gen ^
      h, head, ptrow, tabs]) [] ↔
      AtomsBody rd fn.params l29A (x :: [gen ^ h, head, ptrow, tabs]) ∧ IsInK (x * gen + gen ^ h) ∧
        (x * gen + gen ^ h ≠ 0 →
          coreProgram.relN rd d name% «verify_bus_gkr_loop0_loop0» (x * gen :: [gen ^ h, head,
              ptrow, tabs]) []) := by
    intro d x
    refine loop_step_atoms hf hb l29A_atoms (fun σ hpar hall => ?_) d
    rw [hp] at hpar
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
    obtain ⟨h0, h1, h2, h3, h4⟩ := hpar
    have m := fun a (ha : Stmt.atom a ∈ l29Post) => hall a (by
      simp only [l29A, List.mem_append]; exact Or.inr ha)
    simp only [l29Post, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq,
      forall_eq_or_imp, forall_eq, Atom.Holds] at m
    obtain ⟨c97, m98, a99, c100, m101⟩ := m
    rw [tb_word_gen] at c97 c100
    refine ⟨by rw [a99, m98, c97, h0, h1], ?_⟩
    simp only [List.map_cons, List.map_nil, m101, c100, h0, h1, h2, h3, h4]
  rw [← pow_zero gen]
  refine (loop_iff hstep 0).mpr ⟨h, hpos, rfl, first_hit_of_lt (by unfold ordG; omega) rfl,
    fun j _ hj => ?_⟩
  rw [hp]
  apply l29_iter
  have := hr j hj
  rwa [show ptrow * gen ^ j * gen ^ j = ptrow * gen ^ (2 * j) by ring]

end
end LeanVM.Guest.B1.Tables
