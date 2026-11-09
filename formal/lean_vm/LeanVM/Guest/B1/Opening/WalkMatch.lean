/-
  LeanVM.Guest.B1.Opening.WalkMatch

  The walk of a body of atoms, calls, conditional calls and `match`es of quiet atom arms: the
  taken arm's atoms, and the parts the placed form reads are the straight statements'.
-/

module

public import LeanVM.Guest.Memory.Regions
public import LeanVM.Guest.Memory.Straight
import Mathlib.Data.List.GetD

/-!
# Walking `match`es of quiet arms

A query of `opening_queries` (1a379148) walks its Merkle path by `match`es whose arms are
keccaks, constants and copies (`walk_window`): no load, no `HeapBuf`, no `frameAddr`
(`Atom.quiet`). `Stmt.flatM`: an atom, a call, a conditional call, or such a `match`.

* `walk_flatM`: a flat body whose `match` selectors are `g^j` of an arm `j` walks every
  statement, a `match` contributing the taken arm's atoms (`fmEvs`);
* `flatM_parts`, `loadAddrs_flatM`, `runs_flatM`: its buffers, frame addresses, calls, loads and
  runs are its top-level statements' (`straight_parts`' right-hand sides);
* `fmEvs_holds`: its events hold when its statements do.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory

@[expose] public section

/-- An atom that neither loads, allocates nor places a run. -/
def _root_.LeanVM.Guest.Core.Atom.quiet : Atom → Bool
  | .load .. => false
  | .hint (.alloc ..) => false
  | .hint (.allocDyn ..) => false
  | .frameAddr .. => false
  | _ => true

/-- A quiet atom statement. -/
def _root_.LeanVM.Guest.Core.Stmt.quietS : Stmt → Bool
  | .atom a => a.quiet
  | _ => false

/-- A statement of a flat body with `match`es: an atom, a call, a conditional call, or a `match`
of quiet atom arms. -/
def _root_.LeanVM.Guest.Core.Stmt.flatM : Stmt → Bool
  | .atom _ => true
  | .call .. => true
  | .callIf .. => true
  | .match_ _ arms => arms.all fun arm ↦ arm.all Stmt.quietS
  | _ => false

/-- The events of a quiet arm. -/
def armEvs (arm : List Stmt) : List Ev := arm.filterMap fun s ↦ match s with
  | .atom a => some (.atom a)
  | _ => none

/-- The events of a flat statement: a `match`'s taken arm's atoms. -/
noncomputable def fmEvs (σ : Val) : Stmt → List Ev
  | .match_ x arms => armEvs (arms.getD (logG (σ x)) [])
  | s => slEvs σ s

/-- A `match`'s selector names one of its arms. -/
def MatchOk (σ : Val) : Stmt → Prop
  | .match_ x arms => arms.length ≤ 2 ^ 64 - 1 ∧ ∃ j < arms.length, σ x = ofK (addressOfIndex j)
  | _ => True

theorem walk_quiet (σ : Val) : ∀ arm : List Stmt, arm.all Stmt.quietS = true →
    walk σ arm = .fall (armEvs arm)
  | [], _ => rfl
  | s :: arm, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    match s, h.1 with
    | .atom a, _ =>
      rw [walk, walk1, walk_quiet σ arm h.2, Out.seq, Out.pre]
      rfl

theorem walkArms_eq (σ : Val) (x : V) : ∀ (arms : List (List Stmt)) (j i : ℕ) (hi : i < arms.length),
    j + arms.length ≤ 2 ^ 64 - 1 → σ x = ofK (addressOfIndex (j + i)) →
    walkArms σ x j arms = walk σ arms[i]
  | [], _, _, hi, _, _ => absurd hi (by simp)
  | a :: as, j, i, hi, hb, hx => by
    simp only [List.length_cons] at hi hb
    unfold walkArms
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
        rw [walkArms_eq σ x as (j + 1) i (by simpa using hi) (by omega)
          (by rw [hx]; congr 2; omega)]
        rfl

theorem walk1_flatM (σ : Val) : ∀ s : Stmt, s.flatM = true → MatchOk σ s →
    walk1 σ s = .fall (fmEvs σ s)
  | .atom _, _, _ => rfl
  | .call .., _, _ => rfl
  | .callIf .., _, _ => rfl
  | .match_ x arms, h, ⟨hl, j, hj, hx⟩ => by
    simp only [Stmt.flatM, List.all_eq_true] at h
    rw [walk1, walkArms_eq σ x arms 0 j hj (by omega) (by rw [Nat.zero_add]; exact hx),
      walk_quiet σ _ (List.all_eq_true.mpr (h _ (List.getElem_mem hj))), fmEvs, hx, logG_spec (by omega),
      List.getD_eq_getElem _ _ hj]
  | .ite .., h, _ => by simp [Stmt.flatM] at h
  | .dispatch .., h, _ => by simp [Stmt.flatM] at h
  | .ret _, h, _ => by simp [Stmt.flatM] at h

/-- **A flat body with `match`es walks every statement.** -/
theorem walk_flatM (σ : Val) (vs : List V) : ∀ pre : List Stmt, pre.all Stmt.flatM = true →
    (∀ s ∈ pre, MatchOk σ s) → walk σ (pre ++ [.ret vs]) = .ret (pre.flatMap (fmEvs σ)) vs
  | [], _, _ => by simp [walk, walk1, Out.seq]
  | s :: pre, h, hd => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.cons_append, walk, walk_flatM σ vs pre h.2 (fun s' hs' => hd s' (by simp [hs'])),
      walk1_flatM σ s h.1 (hd s (by simp)), Out.seq, Out.pre, List.flatMap_cons]

/-! ## The parts -/

/-- A part of the events that no quiet atom has. -/
def QuietF {β : Type} (F : Ev → Option β) : Prop := ∀ a : Atom, a.quiet = true → F (.atom a) = none

theorem armEvs_filterMap {β : Type} {F : Ev → Option β} (hF : QuietF F) :
    ∀ arm : List Stmt, arm.all Stmt.quietS = true → (armEvs arm).filterMap F = []
  | [], _ => rfl
  | s :: arm, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    match s, h.1 with
    | .atom a, ha =>
      have ih := armEvs_filterMap hF arm h.2
      simp only [armEvs] at ih ⊢
      simp only [List.filterMap_cons, hF a ha, ih]

/-- **The parts of a flat body's events** are its straight statements'. -/
theorem filterMap_fmEvs {β : Type} {F : Ev → Option β} (hF : QuietF F) (σ : Val) :
    ∀ pre : List Stmt, pre.all Stmt.flatM = true →
      (pre.flatMap (fmEvs σ)).filterMap F = ((pre.filter Stmt.straight).flatMap (slEvs σ)).filterMap F
  | [], _ => rfl
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := filterMap_fmEvs hF σ pre h.2
    match s, h.1 with
    | .atom a, _ =>
      simp only [List.flatMap_cons, List.filterMap_append, List.filter_cons, Stmt.straight,
        ↓reduceIte, ih]
      rfl
    | .call f args rets, _ =>
      simp only [List.flatMap_cons, List.filterMap_append, List.filter_cons, Stmt.straight,
        ↓reduceIte, ih]
      rfl
    | .callIf c f args, _ =>
      simp only [List.flatMap_cons, List.filterMap_append, List.filter_cons, Stmt.straight,
        ↓reduceIte, ih]
      rfl
    | .match_ x arms, hm =>
      simp only [Stmt.flatM, List.all_eq_true] at hm
      have hq : (arms.getD (logG (σ x)) []).all Stmt.quietS = true := by
        rw [List.getD_eq_getElem?_getD]
        cases harm : arms[logG (σ x)]? with
        | none => rfl
        | some arm => exact List.all_eq_true.mpr (hm arm (List.mem_of_getElem? harm))
      simp only [List.flatMap_cons, List.filterMap_append, List.filter_cons, Stmt.straight,
        Bool.false_eq_true, ↓reduceIte, ih, fmEvs, armEvs_filterMap hF _ hq, List.nil_append]

theorem filterMap_filter_straight {β : Type} {G : Stmt → Option β}
    (hG : ∀ x arms, G (.match_ x arms) = none) :
    ∀ pre : List Stmt, pre.all Stmt.flatM = true → (pre.filter Stmt.straight).filterMap G = pre.filterMap G
  | [], _ => rfl
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := filterMap_filter_straight hG pre h.2
    match s, h.1 with
    | .atom a, _ => simp [List.filter_cons, Stmt.straight, List.filterMap_cons, ih]
    | .call .., _ => simp [List.filter_cons, Stmt.straight, List.filterMap_cons, ih]
    | .callIf .., _ => simp [List.filter_cons, Stmt.straight, List.filterMap_cons, ih]
    | .match_ x arms, _ => simp [Stmt.straight, ih, hG]

theorem straight_filter (pre : List Stmt) : (pre.filter Stmt.straight).all Stmt.straight = true := by
  rw [List.all_eq_true]; intro s hs; exact (List.mem_filter.mp hs).2

theorem quietF_allocDst : QuietF Ev.allocDst? := fun a h ↦ by
  cases a with
  | hint hk => cases hk <;> first | rfl | simp [Atom.quiet] at h
  | _ => rfl

theorem quietF_alloc (σ : Val) : QuietF (Ev.alloc? σ) := fun a h ↦ by
  cases a with
  | hint hk => cases hk <;> first | rfl | simp [Atom.quiet] at h
  | _ => rfl

theorem quietF_addr : QuietF Ev.addr? := fun a h ↦ by
  cases a with
  | frameAddr => simp [Atom.quiet] at h
  | hint hk => cases hk <;> rfl
  | _ => rfl

theorem quietF_call : QuietF Ev.call? := fun _ _ ↦ rfl

theorem quietF_loadAddr (σ : Val) : QuietF (Ev.loadAddr? σ) := fun a h ↦ by
  cases a with
  | load => simp [Atom.quiet] at h
  | _ => rfl

theorem quietF_run : QuietF Ev.run? := fun a h ↦ by
  cases a with
  | frameAddr => simp [Atom.quiet] at h
  | _ => rfl

/-- **A flat body's buffers, frame addresses and calls** (as `straight_parts`). -/
theorem flatM_parts (σ : Val) (pre : List Stmt) (h : pre.all Stmt.flatM = true) :
    allocDsts (pre.flatMap (fmEvs σ)) = (pre.filterMap Stmt.allocSz).map Prod.fst ∧
    allocs σ (pre.flatMap (fmEvs σ)) =
      (pre.filterMap Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) ∧
    addrs (pre.flatMap (fmEvs σ)) = pre.filterMap Stmt.addrS ∧
    calls (pre.flatMap (fmEvs σ)) = (pre.filterMap Stmt.callS).map (mkCall σ) := by
  obtain ⟨i1, i2, i3, i4⟩ := straight_parts σ _ (straight_filter pre)
  have a1 := filterMap_filter_straight (G := Stmt.allocSz) (fun _ _ ↦ rfl) pre h
  have a3 := filterMap_filter_straight (G := Stmt.addrS) (fun _ _ ↦ rfl) pre h
  have a4 := filterMap_filter_straight (G := Stmt.callS) (fun _ _ ↦ rfl) pre h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [allocDsts, filterMap_fmEvs quietF_allocDst σ pre h, ← allocDsts, i1, a1]
  · rw [allocs, filterMap_fmEvs (quietF_alloc σ) σ pre h, ← allocs, i2, a1]
  · rw [addrs, filterMap_fmEvs quietF_addr σ pre h, ← addrs, i3, a3]
  · rw [calls, filterMap_fmEvs quietF_call σ pre h, ← calls, i4, a4]

/-- **A flat body's loads** are its top-level loads. -/
theorem loadAddrs_flatM (σ : Val) (pre : List Stmt) (h : pre.all Stmt.flatM = true) :
    loadAddrs σ (pre.flatMap (fmEvs σ)) =
      (pre.filterMap stmtLoad?).map fun q => (σ q.1).limb 0 * addressOfIndex q.2 := by
  rw [loadAddrs, filterMap_fmEvs (quietF_loadAddr σ) σ pre h, ← loadAddrs,
    loadAddrs_straight σ _ (straight_filter pre),
    filterMap_filter_straight (G := stmtLoad?) (fun _ _ ↦ rfl) pre h]

/-- **A flat body's runs** are its top-level `frameAddr`s'. -/
theorem runs_flatM (σ : Val) (pre : List Stmt) (h : pre.all Stmt.flatM = true) :
    runs (pre.flatMap (fmEvs σ)) = pre.filterMap stmtRun? := by
  rw [runs, filterMap_fmEvs quietF_run σ pre h, ← runs, runs_straight σ _ (straight_filter pre),
    filterMap_filter_straight (G := stmtRun?) (fun _ _ ↦ rfl) pre h]

/-- **A taken arm's events hold** when its atoms do. -/
theorem armEvs_holds {rd : Reader} {σ : Val} {arm : List Stmt}
    (h : ∀ a, Stmt.atom a ∈ arm → a.Holds rd σ) : ∀ e ∈ armEvs arm, e.Holds rd σ := by
  intro e he
  obtain ⟨s, hs, he⟩ := List.mem_filterMap.mp he
  match s, he with
  | .atom a, he =>
    simp only [Option.some.injEq] at he
    subst he
    exact h a hs

/-- A `match`'s taken arm is the one its selector names. -/
theorem fmEvs_match {rd : Reader} {σ : Val} {x : V} {arms : List (List Stmt)} {j : ℕ}
    (hj : j < arms.length) (hl : arms.length ≤ 2 ^ 64 - 1) (hx : σ x = ofK (addressOfIndex j))
    (h : ∀ a, Stmt.atom a ∈ arms[j] → a.Holds rd σ) : ∀ e ∈ fmEvs σ (.match_ x arms), e.Holds rd σ := by
  rw [fmEvs, hx, logG_spec (by omega), List.getD_eq_getElem _ _ hj]
  exact armEvs_holds h

end
end LeanVM.Guest.B1
