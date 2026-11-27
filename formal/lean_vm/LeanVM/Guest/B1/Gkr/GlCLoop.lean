/-
  LeanVM.Guest.B1.Gkr.GlCLoop

  `gkr_layer__L{p}_L{o}`'s loop, completely: eight GKR rounds between the records `head·g^(7y)` and
  `head·g^(7(y+1))` at every iteration give its relation from `1` below `x_m`.
-/

module

public import LeanVM.Guest.B1.Gkr.Rounds
public import LeanVM.Guest.B1.Gkr.GlT
public import LeanVM.Guest.B1.Sumcheck.Gkr
public import LeanVM.Guest.B1.Common.Loops
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.CoreData
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_layer__L_loop0»
import LeanVM.Guest.B1.Tables.Basic
import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.StmtsAppend

/-!
# `gkr_layer__L{p}_L{o}_loop0`, completely

The eight loops (one per layer function) have one body but for the recursive call's name
(`glcBody`, checked against all eight by `glc_check`): the record `head·y^7`, the rows `qrow·y^8`
and `nqrow·y^8`, then `gkPre true 8` (the sumcheck's rounds) renamed by `glcSh`, its challenge stores
`pt[42 + q]` redirected to `npt[q]` (`glcMap`; `npt = pt·g^42`), then the guard and the next
call's argument.

* `glc_iter`: an iteration at `x` holds when its eight rounds do (`TbGkrRoundsOut 8 1` at the
  record `head·x^7` and the row `qrow·x^8`), its valuation the rounds' (`gk_pre_holds`) renamed;
* `glc_complete`: eight rounds at every `y < m` give the loop from `1` below `g^m`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1

@[expose] public section

/-- `gkPre true 8`'s values in an iteration: the record `head·y^7` (`10`), the row `qrow·y^8`
(`14`), the cursor (`21`), the capacity eleven on, the claim and the others twelve on. -/
def glcSh (v : V) : V :=
  if v.idx = 0 then .n 10 else if v.idx = 1 then .n 14 else if v.idx = 2 then .n 21
  else if v.idx < 5 then .n 5 else if v.idx < 10 then .n (v.idx + 11) else .n (v.idx + 12)

/-- A statement of `gkPre true 8` in the loop: renamed, a challenge's store `pt[42 + q]` through
the next row `npt[q]` (`15`). -/
def glcMap : Stmt → Stmt
  | .atom (.load d (.n 1) off) =>
    if 42 ≤ off then .atom (.load (glcSh d) (.n 15) (off - 42))
    else .atom (.load (glcSh d) (.n 14) off)
  | s => s.rename glcSh

/-- The iteration's pointers: the record, `y^8`, the rows. -/
def glcPre : List Stmt :=
  [.atom (.mul (.n 6) (.n (valf% «gkr_layer» «_loop0» "y")) (.n (valf% «gkr_layer» «_loop0» "y"))), .atom (.mul (.n 7) (.n 6) (.n (valf% «gkr_layer» «_loop0» "y"))),
    .atom (.mul (.n 8) (.n 7) (.n 7)), .atom (.mul (.n 9) (.n 8) (.n (valf% «gkr_layer» «_loop0» "y"))),
    .atom (.mul (.n (valf% «gkr_layer» «_loop0» "rd")) (.n (valf% «gkr_layer» «_loop0» "head")) (.n 9)), .atom (.mul (.n (valf% «gkr_layer» «_loop0» "y2")) (.n (valf% «gkr_layer» «_loop0» "y")) (.n (valf% «gkr_layer» «_loop0» "y"))),
    .atom (.mul (.n (valf% «gkr_layer» «_loop0» "y4")) (.n (valf% «gkr_layer» «_loop0» "y2")) (.n (valf% «gkr_layer» «_loop0» "y2"))), .atom (.mul (.n (valf% «gkr_layer» «_loop0» "y8")) (.n (valf% «gkr_layer» «_loop0» "y4")) (.n (valf% «gkr_layer» «_loop0» "y4"))),
    .atom (.mul (.n (valf% «gkr_layer» «_loop0» "pt")) (.n (valf% «gkr_layer» «_loop0» "qrow")) (.n (valf% «gkr_layer» «_loop0» "y8"))), .atom (.mul (.n (valf% «gkr_layer» «_loop0» "npt")) (.n (valf% «gkr_layer» «_loop0» "nqrow")) (.n (valf% «gkr_layer» «_loop0» "y8")))]

/-- The guard and the next call's argument. -/
def glcPost : List Stmt :=
  [.atom (.const (.n (valf% «gkr_layer» «_loop0» "s15#0")) (word 2 0)), .atom (.mul (.n (valf% «gkr_layer» «_loop0» "s15#1")) (.n (valf% «gkr_layer» «_loop0» "y")) (.n (valf% «gkr_layer» «_loop0» "s15#0"))),
    .atom (.add (.n (valf% «gkr_layer» «_loop0» "s15#2")) (.n (valf% «gkr_layer» «_loop0» "s15#1")) (.n (valf% «gkr_layer» «_loop0» "bound"))), .atom (.const (.n (valf% «gkr_layer» «_loop0» "s15#3")) (word 2 0)),
    .atom (.mul (.n (valf% «gkr_layer» «_loop0» "s15#4")) (.n (valf% «gkr_layer» «_loop0» "y")) (.n (valf% «gkr_layer» «_loop0» "s15#3")))]

/-- The iteration's atoms. -/
def glcA : List Stmt := glcPre ⧺ (gkPre true 8).map glcMap ⧺ glcPost

/-- The loop's body, calling `nm`. -/
def glcBody (nm : String) : List Stmt :=
  glcA ⧺ [.callIf (.n (valf% «gkr_layer» «_loop0» "s15#2")) nm [.n (valf% «gkr_layer» «_loop0» "s15#4"), .n (valf% «gkr_layer» «_loop0» "bound"), .n (valf% «gkr_layer» «_loop0» "head"), .n (valf% «gkr_layer» «_loop0» "qrow"), .n (valf% «gkr_layer» «_loop0» "nqrow"), .n (valf% «gkr_layer» «_loop0» "tabs")], .ret []]

/-- The loop's parameters. -/
def glcPar6 : List V := [.n (valf% «gkr_layer» «_loop0» "y"), .n (valf% «gkr_layer» «_loop0» "bound"), .n (valf% «gkr_layer» «_loop0» "head"), .n (valf% «gkr_layer» «_loop0» "qrow"), .n (valf% «gkr_layer» «_loop0» "nqrow"), .n (valf% «gkr_layer» «_loop0» "tabs")]

/-- The loop of `p`, `o` at its index (`glLoopIdx`) is named `glLoopName p o` and has these parameters and body. -/
noncomputable def glcCheck (p o : ℕ) : Bool :=
  match coreProgram[glLoopIdx p o]? with
  | some fn => fn.name == glLoopName p o && decide (fn.params = glcPar6) &&
      stmtsEqb fn.body (glcBody (glLoopName p o))
  | none => false

theorem glc_check : ∀ p < 4, ∀ o < 2, glcCheck p o = true := by decide +kernel

theorem glcFound {p o : ℕ} (hp : p < 4) (ho : o < 2) : ∃ fn : Fn, coreProgram.find? (glLoopName p o) =
    some fn ∧ fn.params = glcPar6 ∧ fn.body = glcBody (glLoopName p o) := by
  have h := glc_check p hp o ho
  unfold glcCheck at h
  split at h
  · rename_i fn hj
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨fn, coreProgram_find?_at hj h.1.1, h.1.2, stmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

/-- Every statement of `gkPre true 8` is an atom over values `.n k`, `k ≤ 324`, never the window
table's or the stream's, its loads through `pt` at `q < 8` or `42 + q`. -/
def gk8Ok : Stmt → Bool
  | .atom a => a.vals.all fun v => decide (v = .n v.idx) && decide (v.idx ≤ 324) &&
      decide (v.idx ≠ 3) && decide (v.idx ≠ 4)
  | _ => false

theorem gk8_ok : (gkPre true 8).all gk8Ok = true := by decide +kernel

theorem glc_atom_congr {rd : Reader} {σ σ' : Val} {a : Atom} (h : ∀ v ∈ a.vals, σ v = σ' v) :
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

theorem glcA_atoms : AllAtoms glcA := by
  intro s hs
  simp only [glcA, List.mem_append, List.mem_map] at hs
  rcases hs with (hs | ⟨t, ht, rfl⟩) | hs
  · simp only [glcPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · have := List.all_eq_true.mp gk8_ok t ht
    cases t with
    | atom a =>
      cases a with
      | load d p off =>
        unfold glcMap
        split
        · split <;> exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
      | _ => exact ⟨_, rfl⟩
    | _ => simp [gk8Ok] at this
  · simp only [glcPost, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- `y^8` as the iteration computes it. -/
def glcY8 (x : E) : E := x * x * (x * x) * (x * x * (x * x))

theorem glcY8_eq (x : E) : glcY8 x = x ^ 8 := by unfold glcY8; ring

/-- `y^7` as the iteration computes it. -/
def glcY7 (x : E) : E := x * x * x * (x * x * x) * x

theorem glcY7_eq (x : E) : glcY7 x = x ^ 7 := by unfold glcY7; ring

/-- **The honest valuation of an iteration** at `x`, the rounds' `σgk` renamed. -/
def glcVal (x N head qrow nqrow tabs : E) (σgk : Val) (v : V) : E :=
  if v.idx < 16 then [x, N, head, qrow, nqrow, tabs, x * x, x * x * x, x * x * x * (x * x * x),
    glcY7 x, head * glcY7 x, x * x, x * x * (x * x), glcY8 x, qrow * glcY8 x,
    nqrow * glcY8 x].getD v.idx 0
  else if v.idx < 21 then σgk (.n (v.idx - 11))
  else if v.idx = 21 then σgk (.n 2)
  else if v.idx ≤ 336 then σgk (.n (v.idx - 12))
  else [gen, x * gen, x * gen + N, gen, x * gen].getD (v.idx - 337) 0

theorem glc_val_sh {x N head qrow nqrow tabs : E} {σgk : Val} (hσv : ∀ v, σgk v = σgk (.n v.idx))
    (h0 : σgk (.n 0) = head * glcY7 x) (h1 : σgk (.n 1) = qrow * glcY8 x) {v : V}
    (hvi : v.idx ≤ 324) (h3 : v.idx ≠ 3) (h4 : v.idx ≠ 4) :
    v.idx ≠ 2 → glcVal x N head qrow nqrow tabs σgk (glcSh v) = σgk v := by
  intro e2
  rw [hσv v]
  by_cases e0 : v.idx = 0
  · simp [glcSh, glcVal, e0, h0]
  by_cases e1 : v.idx = 1
  · simp [glcSh, glcVal, e1, h1]
  by_cases e5 : v.idx < 10
  · have i1 : ¬ v.idx + 11 < 16 := by omega
    have i2 : v.idx + 11 < 21 := by omega
    have i5 : ¬ v.idx < 5 := by omega
    simp only [glcSh, glcVal, e0, e1, e2, e5, i1, i2, i5, ↓reduceIte, Nat.add_sub_cancel]
  · have i1 : ¬ v.idx + 12 < 16 := by omega
    have i2 : ¬ v.idx + 12 < 21 := by omega
    have i3 : ¬ v.idx + 12 = 21 := by omega
    have i4 : v.idx + 12 ≤ 336 := by omega
    have i5 : ¬ v.idx < 5 := by omega
    simp only [glcSh, glcVal, e0, e1, e2, e5, i1, i2, i3, i4, i5, ↓reduceIte, Nat.add_sub_cancel]

/-- Eight rounds between records `1` apart, as `GkrRoundsOut` on the record's cursor. -/
theorem glc_out_of_tb {rd : Reader} {rec pt : E} (h : TbGkrRoundsOut 8 1 rd rec pt) :
    ∃ cur, GkrRoundsOut 8 rd rec pt cur ∧ LoadHolds rd rec 5 cur := by
  obtain ⟨cap, cur, claim, cs, es, h1, hc, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨cur, ⟨cap, claim, cs, es, h1, h3, h4, h5, h6, h7, h8, h9, fun h ↦ absurd h (by decide),
    h10, h11, h12⟩, hc⟩

/-- **An iteration of `gkr_layer__L{p}_L{o}_loop0`, completely.** -/
theorem glc_iter {rd : Reader} (x N head qrow nqrow tabs : E) (hnq : nqrow = qrow * gen ^ 42)
    (hT : TbGkrRoundsOut 8 1 rd (head * x ^ 7) (qrow * x ^ 8)) :
    AtomsBody rd (glcPar6) glcA [x, N, head, qrow, nqrow, tabs] := by
  rw [← glcY8_eq, ← glcY7_eq] at hT
  obtain ⟨cur, hout, hcur⟩ := glc_out_of_tb hT
  obtain ⟨σgk, hσv, h0, h1, h2, -, -, -, hh⟩ := gk_pre_holds true 8 (by norm_num) (by norm_num)
    (coreProgram.Rel rd) rd _ _ cur tabs 0 hout (fun _ ↦ hcur)
  have hgk : ∀ a, Stmt.atom a ∈ gkPre true 8 → a.Holds rd σgk := by
    have hA : AllAtoms (gkPre true 8) := by
      intro t ht
      have := List.all_eq_true.mp gk8_ok t ht
      cases t with
      | atom a => exact ⟨_, rfl⟩
      | _ => simp [gk8Ok] at this
    have := hh True (fun _ ↦ True) trivial
    rw [holdsList_atoms hA] at this
    exact this.1
  set σ := glcVal x N head qrow nqrow tabs σgk with hσ
  -- every value of `gkPre true 8` renamed
  have hv : ∀ v : V, v = .n v.idx → v.idx ≤ 324 → v.idx ≠ 3 → v.idx ≠ 4 →
      σ (glcSh v) = σgk v := by
    intro v _ hvi h3 h4
    by_cases e2 : v.idx = 2
    · rw [hσv v, e2]; simp [σ, glcSh, glcVal, e2, h2]
    · exact glc_val_sh hσv h0 h1 hvi h3 h4 e2
  refine ⟨σ, by simp [glcPar6, σ, glcVal], fun a ha => ?_⟩
  simp only [glcA, List.mem_append, List.mem_map] at ha
  rcases ha with (ha | ⟨t, ht, he⟩) | ha
  · simp only [glcPre, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Atom.Holds, σ, glcVal, glcY8, glcY7]
  · have hok := List.all_eq_true.mp gk8_ok _ ht
    cases t with
    | atom b =>
      have hvs : ∀ v ∈ b.vals, σ (glcSh v) = σgk v := by
        intro v hv'
        simp only [gk8Ok, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨⟨⟨hvn, hvi⟩, h3⟩, h4⟩ := hok v hv'
        exact hv v hvn hvi h3 h4
      have hren : (b.rename glcSh).Holds rd σ := by
        rw [Atom.holds_rename]
        exact (glc_atom_congr fun v hv' => hvs v hv').mpr (hgk b ht)
      cases b with
      | load d p off =>
        have hb := hgk _ ht
        simp only [glcMap] at he
        split at he
        · rename_i d' off' heq
          simp only [Stmt.atom.injEq, Atom.load.injEq] at heq
          obtain ⟨rfl, hp, rfl⟩ := heq
          subst hp
          have hd : σ (glcSh d) = σgk d := hvs d (by simp [Atom.vals])
          have hp1 : σ (.n 14) = σgk (.n 1) := hvs (.n 1) (by simp [Atom.vals])
          split at he
          · rename_i hoff
            simp only [Stmt.atom.injEq] at he
            subst he
            show LoadHolds rd (σ (.n 15)) (off - 42) (σ (glcSh d))
            have h11 : σ (.n 15) = σ (.n 14) * gen ^ 42 := by
              show nqrow * glcY8 x = qrow * glcY8 x * gen ^ 42
              rw [hnq]; ring
            rw [h11, loadHolds_mul_gen_pow, show 42 + (off - 42) = off by omega, hd, hp1]
            exact hb
          · simp only [Stmt.atom.injEq] at he
            subst he
            show LoadHolds rd (σ (.n 14)) off (σ (glcSh d))
            rw [hd, hp1]; exact hb
        · rename_i hne
          simp only [Stmt.rename, Stmt.atom.injEq] at he
          subst he; exact hren
      | _ =>
        simp only [glcMap, Stmt.rename, Stmt.atom.injEq] at he
        subst he; exact hren
    | _ => simp [gk8Ok] at hok
  · simp only [glcPost, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp [Atom.Holds, σ, glcVal, word_gen]

/-- **`gkr_layer__L{p}_L{o}_loop0`, completely**: eight rounds from the record at `head·g^(7y)`, the
row at `qrow·g^(8y)`, at every iteration `y < m` give the loop from `1` below `g^m`. -/
theorem glc_complete {rd : Reader} {p o : ℕ} (hp : p < 4) (ho : o < 2) {head qrow nqrow tabs : E}
    (hnq : nqrow = qrow * gen ^ 42) {m : ℕ} (hpos : 0 < m) (hmb : m < 2 ^ 62)
    (hr : ∀ y < m, TbGkrRoundsOut 8 1 rd (head * gen ^ (7 * y)) (qrow * gen ^ (8 * y))) :
    coreProgram.Rel rd (glLoopName p o) [1, gen ^ m, head, qrow, nqrow, tabs] [] := by
  obtain ⟨fn, hf, hpar, hb⟩ := glcFound hp ho
  rw [glcBody] at hb
  have hstep : ∀ d x, coreProgram.relN rd (d + 1) (glLoopName p o) (x :: [gen ^ m, head, qrow, nqrow,
      tabs]) [] ↔
      AtomsBody rd fn.params glcA (x :: [gen ^ m, head, qrow, nqrow, tabs]) ∧
        IsInK (x * gen + gen ^ m) ∧
        (x * gen + gen ^ m ≠ 0 →
          coreProgram.relN rd d (glLoopName p o) (x * gen :: [gen ^ m, head, qrow, nqrow, tabs]) []) := by
    intro d x
    refine loop_step_atoms hf hb glcA_atoms (fun σ hpa hall => ?_) d
    rw [hpar] at hpa
    simp only [glcPar6, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpa
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := hpa
    have mm := fun a (ha : Stmt.atom a ∈ glcPost) => hall a (by
      simp only [glcA, List.mem_append]; exact Or.inr ha)
    simp only [glcPost, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq,
      forall_eq_or_imp, forall_eq, Atom.Holds] at mm
    obtain ⟨c341, m342, a343, c344, m345⟩ := mm
    rw [word_gen] at c341 c344
    refine ⟨by rw [a343, m342, c341, e0, e1], ?_⟩
    simp only [List.map_cons, List.map_nil, m345, c344, e0, e1, e2, e3, e4, e5]
  rw [← pow_zero gen]
  refine (loop_iff hstep 0).mpr ⟨m, hpos, rfl, first_hit_of_lt (by unfold ordG; omega) rfl,
    fun y _ hy => ?_⟩
  rw [hpar]
  apply glc_iter _ _ _ _ _ _ hnq
  have := hr y hy
  rw [← pow_mul, ← pow_mul, mul_comm y 7, mul_comm y 8]; exact this

end
end LeanVM.Guest.B1.Tables
