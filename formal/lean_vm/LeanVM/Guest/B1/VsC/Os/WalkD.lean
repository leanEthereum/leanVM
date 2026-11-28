/-
  LeanVM.Guest.B1.VsC.Os.WalkD

  The walk of a flat body with `match`es and dispatches, from its relational form.
-/

module

public import LeanVM.Guest.B1.VsC.Oq.WalkMatch
public import LeanVM.Guest.B1.Whir.Flat
import Mathlib.Data.List.GetD

/-!
# Walking `match`es and dispatches

`open_stacked`'s body is atoms, calls, `match`es of quiet arms (the levels' shapes by rate) and
dispatches (the levels' helpers by rate). `Stmt.flatD` extends `Stmt.flatM` by dispatches;
`fdEvs` a dispatch's events: the call of the callee its selector names.

* `walk_flatD`: a flat body whose selectors name an arm (`SelOk`) walks every statement;
* `selOk_of_allOk`: the bus era's relational form (`AllOk`) names them, its arm counts below
  `2^64 - 1` (`Stmt.armsShort`);
* `fdEvs_holds`: every event of a statement the relational form holds of holds.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- A statement of a flat body with `match`es and dispatches. -/
def _root_.LeanVM.Guest.Core.Stmt.flatD : Stmt → Bool
  | .dispatch .. => true
  | .atom a => Stmt.flatM (.atom a)
  | .call f args rets => Stmt.flatM (.call f args rets)
  | .callIf c f args => Stmt.flatM (.callIf c f args)
  | .match_ x arms => Stmt.flatM (.match_ x arms)
  | .ite .. => false
  | .ret _ => false

/-- A `match`'s or dispatch's arms fewer than `2^64 - 1`. -/
def _root_.LeanVM.Guest.Core.Stmt.armsShort : Stmt → Bool
  | .match_ _ arms => decide (arms.length ≤ 2 ^ 64 - 1)
  | .dispatch _ fs _ _ => decide (fs.length ≤ 2 ^ 64 - 1)
  | _ => true

/-- The events of a flat statement with dispatches: a dispatch's taken callee's call. -/
noncomputable def fdEvs (σ : Val) : Stmt → List Ev
  | .dispatch x fs args rets => [.call (fs.getD (logG (σ x)) "") args rets]
  | .atom a => fmEvs σ (.atom a)
  | .call f args rets => fmEvs σ (.call f args rets)
  | .callIf c f args => fmEvs σ (.callIf c f args)
  | .match_ x arms => fmEvs σ (.match_ x arms)
  | .ite .. => []
  | .ret _ => []

/-- A `match`'s or dispatch's selector names one of its arms. -/
def SelOk (σ : Val) : Stmt → Prop
  | .dispatch x fs _ _ => fs.length ≤ 2 ^ 64 - 1 ∧ ∃ j < fs.length, σ x = ofK (addressOfIndex j)
  | .match_ x arms => MatchOk σ (.match_ x arms)
  | _ => True

theorem pick_eqD (σ : Val) (x : V) (args rets : List V) : ∀ (fs : List String) (j i : ℕ) (hi : i < fs.length),
    j + fs.length ≤ 2 ^ 64 - 1 → σ x = ofK (addressOfIndex (j + i)) →
    pick σ x args rets j fs = .fall [.call fs[i] args rets]
  | [], _, _, hi, _, _ => absurd hi (by simp)
  | a :: as, j, i, hi, hb, hx => by
    simp only [List.length_cons] at hi hb
    unfold pick
    by_cases hxj : σ x = ofK (addressOfIndex j)
    · rw [ite_eq_left hxj]
      obtain rfl : i = 0 := by
        by_contra h0
        exact ofK_gpow_ne (show j < j + i by omega) (by omega) (hxj.symm.trans hx)
      rfl
    · rw [ite_eq_right hxj]
      cases i with
      | zero => exact absurd (by simpa using hx) hxj
      | succ i =>
        rw [pick_eqD σ x args rets as (j + 1) i (by simpa using hi) (by omega)
          (by rw [hx]; congr 2; omega)]
        rfl

theorem walk1_flatD (σ : Val) : ∀ s : Stmt, s.flatD = true → SelOk σ s → walk1 σ s = .fall (fdEvs σ s)
  | .atom a, h, hm => walk1_flatM σ (.atom a) h hm
  | .call f args rets, h, hm => walk1_flatM σ (.call f args rets) h hm
  | .callIf c f args, h, hm => walk1_flatM σ (.callIf c f args) h hm
  | .match_ x arms, h, hm => walk1_flatM σ (.match_ x arms) h hm
  | .dispatch x fs args rets, _, ⟨hl, j, hj, hx⟩ => by
    rw [walk1, pick_eqD σ x args rets fs 0 j hj (by omega) (by rw [Nat.zero_add]; exact hx), fdEvs, hx,
      logG_spec (by omega), List.getD_eq_getElem _ _ hj]
  | .ite .., h, _ => by simp [Stmt.flatD] at h
  | .ret _, h, _ => by simp [Stmt.flatD] at h

/-- **A flat body with `match`es and dispatches walks every statement.** -/
theorem walk_flatD (σ : Val) (vs : List V) : ∀ pre : List Stmt, pre.all Stmt.flatD = true →
    (∀ s ∈ pre, SelOk σ s) → walk σ (pre ++ [.ret vs]) = .ret (pre.flatMap (fdEvs σ)) vs
  | [], _, _ => by simp [walk, walk1, Out.seq]
  | s :: pre, h, hd => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.cons_append, walk, walk_flatD σ vs pre h.2 (fun s' hs' => hd s' (by simp [hs'])),
      walk1_flatD σ s h.1 (hd s (by simp)), Out.seq, Out.pre, List.flatMap_cons]

/-- The value a statement's events depend on: a `match`'s or dispatch's selector, a conditional
call's condition. -/
def _root_.LeanVM.Guest.Core.Stmt.selV : Stmt → Option V
  | .match_ x _ => some x
  | .dispatch x _ _ _ => some x
  | .callIf c _ _ => some c
  | _ => none

/-- **A statement's events depend on its selector alone.** -/
theorem fdEvs_congr {σ σ' : Val} : ∀ s : Stmt, (∀ x, s.selV = some x → σ x = σ' x) → fdEvs σ s = fdEvs σ' s
  | .atom _, _ => rfl
  | .call .., _ => rfl
  | .callIf c f args, h => by
    change [Ev.inK c, if σ c = 0 then .skip f args else .call f args []] =
      [Ev.inK c, if σ' c = 0 then .skip f args else .call f args []]
    rw [h c rfl]
  | .match_ x arms, h => by
    change armEvs (arms.getD (logG (σ x)) []) = armEvs (arms.getD (logG (σ' x)) [])
    rw [h x rfl]
  | .dispatch x fs args rets, h => by
    simp only [fdEvs]
    rw [h x rfl]
  | .ite .., _ => rfl
  | .ret _, _ => rfl

/-- **A body's events depend on its selectors alone.** -/
theorem flatMap_fdEvs_congr {σ σ' : Val} {ss : List Stmt}
    (h : ∀ s ∈ ss, ∀ x, s.selV = some x → σ x = σ' x) : ss.flatMap (fdEvs σ) = ss.flatMap (fdEvs σ') :=
  List.flatMap_congr fun s hs ↦ fdEvs_congr s (h s hs)

/-! ## The parts -/

/-- **The parts of a flat body's events** are its straight statements', for a part no quiet atom
and no call has. -/
theorem filterMap_fdEvs {β : Type} {F : Ev → Option β} (hF : QuietF F) (hc : ∀ f a r, F (.call f a r) = none)
    (σ : Val) : ∀ pre : List Stmt, pre.all Stmt.flatD = true →
      (pre.flatMap (fdEvs σ)).filterMap F = ((pre.filter Stmt.straight).flatMap (slEvs σ)).filterMap F
  | [], _ => rfl
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := filterMap_fdEvs hF hc σ pre h.2
    cases s with
    | atom a =>
      simp only [List.flatMap_cons, List.filterMap_append, List.filter_cons, Stmt.straight, ↓reduceIte, ih]
      rfl
    | call f args rets =>
      simp only [List.flatMap_cons, List.filterMap_append, List.filter_cons, Stmt.straight, ↓reduceIte, ih]
      rfl
    | callIf c f args =>
      simp only [List.flatMap_cons, List.filterMap_append, List.filter_cons, Stmt.straight, ↓reduceIte, ih]
      rfl
    | match_ x arms =>
      have hm := h.1
      simp only [Stmt.flatD, Stmt.flatM, List.all_eq_true] at hm
      have hq : (arms.getD (logG (σ x)) []).all Stmt.quietS = true := by
        rw [List.getD_eq_getElem?_getD]
        cases harm : arms[logG (σ x)]? with
        | none => rfl
        | some arm => exact List.all_eq_true.mpr (hm arm (List.mem_of_getElem? harm))
      have e : (fdEvs σ (.match_ x arms)).filterMap F = [] := armEvs_filterMap hF _ hq
      simp only [List.flatMap_cons, List.filterMap_append, List.filter_cons, Stmt.straight,
        Bool.false_eq_true, ↓reduceIte, ih, e, List.nil_append]
    | dispatch x fs args rets =>
      have e : (fdEvs σ (.dispatch x fs args rets)).filterMap F = [] := by
        rw [show fdEvs σ (.dispatch x fs args rets) = [.call (fs.getD (logG (σ x)) "") args rets] from rfl,
          List.filterMap_cons_none (hc _ _ _)]
        rfl
      simp only [List.flatMap_cons, List.filterMap_append, List.filter_cons, Stmt.straight,
        Bool.false_eq_true, ↓reduceIte, ih, e, List.nil_append]
    | ite _ _ _ => simp [Stmt.flatD] at h
    | ret _ => simp [Stmt.flatD] at h

theorem filterMap_filter_straightD {β : Type} {G : Stmt → Option β}
    (hG : ∀ x arms, G (.match_ x arms) = none) (hD : ∀ x fs args rets, G (.dispatch x fs args rets) = none) :
    ∀ pre : List Stmt, pre.all Stmt.flatD = true → (pre.filter Stmt.straight).filterMap G = pre.filterMap G
  | [], _ => rfl
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := filterMap_filter_straightD hG hD pre h.2
    cases s with
    | atom a => simp [List.filter_cons, Stmt.straight, List.filterMap_cons, ih]
    | call _ _ _ => simp [List.filter_cons, Stmt.straight, List.filterMap_cons, ih]
    | callIf _ _ _ => simp [List.filter_cons, Stmt.straight, List.filterMap_cons, ih]
    | match_ x arms => simp [Stmt.straight, ih, hG]
    | dispatch x fs args rets => simp [Stmt.straight, ih, hD]
    | ite _ _ _ => simp [Stmt.flatD] at h
    | ret _ => simp [Stmt.flatD] at h

/-- **A flat body's buffers and frame addresses** are its top-level statements'. -/
theorem flatD_parts (σ : Val) (pre : List Stmt) (h : pre.all Stmt.flatD = true) :
    allocDsts (pre.flatMap (fdEvs σ)) = (pre.filterMap Stmt.allocSz).map Prod.fst ∧
      allocs σ (pre.flatMap (fdEvs σ)) = (pre.filterMap Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) ∧
      addrs (pre.flatMap (fdEvs σ)) = pre.filterMap Stmt.addrS := by
  obtain ⟨i1, i2, i3, -⟩ := straight_parts σ _ (straight_filter pre)
  have gA : (pre.filter Stmt.straight).filterMap Stmt.allocSz = pre.filterMap Stmt.allocSz :=
    filterMap_filter_straightD (fun _ _ => rfl) (fun _ _ _ _ => rfl) pre h
  have gF : (pre.filter Stmt.straight).filterMap Stmt.addrS = pre.filterMap Stmt.addrS :=
    filterMap_filter_straightD (fun _ _ => rfl) (fun _ _ _ _ => rfl) pre h
  refine ⟨?_, ?_, ?_⟩
  · rw [allocDsts, filterMap_fdEvs quietF_allocDst (fun _ _ _ => rfl) σ pre h, ← allocDsts, i1, gA]
  · rw [allocs, filterMap_fdEvs (quietF_alloc σ) (fun _ _ _ => rfl) σ pre h, ← allocs, i2, gA]
  · rw [addrs, filterMap_fdEvs quietF_addr (fun _ _ _ => rfl) σ pre h, ← addrs, i3, gF]

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The relational form names a selector's arm. -/
theorem selOk_of_stmtOk : ∀ {s : Stmt}, s.armsShort = true → StmtOk C rd σ s → SelOk σ s
  | .match_ x arms, hl, ⟨j, hj, hx, _⟩ => ⟨by simpa [Stmt.armsShort] using hl, j, hj, hx⟩
  | .dispatch x fs args rets, hl, ⟨j, hj, hx, _⟩ => ⟨by simpa [Stmt.armsShort] using hl, j, hj, hx⟩
  | .atom _, _, _ => trivial
  | .call .., _, _ => trivial
  | .callIf .., _, _ => trivial
  | .ite .., _, _ => trivial
  | .ret _, _, _ => trivial

theorem selOk_of_allOk {ss : List Stmt} (hl : ss.all Stmt.armsShort = true) (h : AllOk C rd σ ss) :
    ∀ s ∈ ss, SelOk σ s :=
  fun s hs ↦ selOk_of_stmtOk (List.all_eq_true.mp hl s hs) (h s hs)

/-- **A statement's events hold** where the relational form holds of it. -/
theorem fdEvs_holds : ∀ {s : Stmt}, s.armsShort = true → StmtOk C rd σ s → ∀ e ∈ fdEvs σ s, e.Holds rd σ
  | .atom a, _, h, e, he => by
    change e ∈ [Ev.atom a] at he
    rw [List.mem_singleton] at he
    subst he; exact h
  | .call f args rets, _, _, e, he => by
    change e ∈ [Ev.call f args rets] at he
    rw [List.mem_singleton] at he
    subst he; trivial
  | .callIf c f args, _, h, e, he => by
    change e ∈ [Ev.inK c, if σ c = 0 then .skip f args else .call f args []] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact h.1
    · split <;> trivial
  | .match_ x arms, hl, ⟨j, hj, hx, ha⟩, e, he =>
    fmEvs_match hj (by simpa [Stmt.armsShort] using hl) hx ha e he
  | .dispatch x fs args rets, _, _, e, he => by
    simp only [fdEvs, List.mem_singleton] at he
    subst he; trivial
  | .ite .., _, _, e, he => by simp [fdEvs] at he
  | .ret _, _, _, e, he => by simp [fdEvs] at he

theorem fdEvs_holds_all {ss : List Stmt} (hl : ss.all Stmt.armsShort = true) (h : AllOk C rd σ ss) :
    ∀ e ∈ ss.flatMap (fdEvs σ), e.Holds rd σ := by
  intro e he
  obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp he
  exact fdEvs_holds (List.all_eq_true.mp hl s hs) (h s hs) e he

end
end LeanVM.Guest.B1
