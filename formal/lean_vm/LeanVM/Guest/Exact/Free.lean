/-
  LeanVM.Guest.Exact.Free

  The functions whose subtree's computed hints are all pinned inside their own bodies (`exactFree`, decided by the
  kernel per function): every valid tree of one is exact on every reader (`every_exact_of_free`).
-/

module

public import LeanVM.Guest.Exact.Every
public import LeanVM.Guest.Memory.CalleeIdx
public import LeanVM.Guest.B1.Common.Find

/-!
# Exact for free

A computed hint (`isComputed`: every hint but a witness entry and an allocation) is pinned locally when the next atom
of its block pins it (`pinsInverse`: an `inverse` followed by `assertNe` on its two values). A body passing
`Stmt.blockNextOk isComputed pinsInverse` has every computed hint pinned so; then each of its paths that holds is
exact on every reader (`exact_of_pinned`), a hint other than a computed one being exact by definition;
`exact_of_pinned_except` leaves out the hints satisfying `p2`, which the caller supplies, `exact_of_sites` the atoms of a
list (a leaf's hints pinned only through memory, exact under its honest valuation).

`exactJ d j`: function `j`'s body passes that check, each of its callees has an index, and each callee index is `j`
itself (a loop's tail call) or passes `exactJ (d - 1)`. `exactFree g j` adds that function `j` is named `g`, decided
per function by `decide +kernel` (as `noWitness`); `exactCallee j g` the same of function `j`'s callee `g`. The functions passing it are call-closed (`coreProgram_exactIn`),
so every valid tree of one is exact on every reader (`every_exact_of_free`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- A computed hint: a hint the executor computes from what it reads. -/
def isComputed : Atom → Bool
  | .hint (.witness ..) => false
  | .hint (.alloc ..) => false
  | .hint (.allocDyn ..) => false
  | .hint _ => true
  | _ => false

theorem exact_of_not_computed {rd : Reader} {σ : Val} : ∀ {a : Atom}, isComputed a = false → a.Exact rd σ
  | .hint (.witness ..), _ | .hint (.alloc ..), _ | .hint (.allocDyn ..), _ => trivial
  | .hint (.bits ..), h | .hint (.bitsExp ..), h | .hint (.digitsExp ..), h | .hint (.windowsExp ..), h
  | .hint (.limbs ..), h | .hint (.log2Ceil ..), h | .hint (.inverse ..), h => by simp [isComputed] at h
  | .const .., _ | .add .., _ | .mul .., _ | .copy .., _ | .load .., _ | .assertEq .., _ | .assertNe .., _
  | .rangeCheck .., _ | .assertInK .., _ | .keccak .., _ | .touch .., _ | .frameAddr .., _ => trivial

/-- **A path of a body whose computed hints are pinned locally is exact**, on every reader. -/
theorem exact_of_pinned {rd : Reader} {σ : Val} {body : List Stmt} {es : List Ev} {vs : List V}
    (hpin : Stmt.blockNextOk isComputed pinsInverse body = true) (hw : walk σ body = .ret es vs)
    (hes : ∀ e ∈ es, e.Holds rd σ) (rd' : Reader) : ∀ e ∈ es, e.Exact rd' σ := by
  have hp := walk_partnered (σ := σ) body hpin
  rw [hw] at hp
  intro e he
  cases e with
  | atom a =>
    cases hc : isComputed a with
    | false => exact exact_of_not_computed hc
    | true =>
      obtain ⟨b, hb, hq⟩ := hp a he hc
      cases a with
      | hint h =>
        cases h with
        | inverse x i =>
          cases b with
          | assertNe x' i' p' =>
            simp only [pinsInverse, Bool.and_eq_true, beq_iff_eq] at hq
            obtain ⟨rfl, rfl⟩ := hq
            exact inverse_exact (rd := rd') (hes _ hb)
          | _ => simp [pinsInverse] at hq
        | _ => simp [pinsInverse] at hq
      | _ => simp [pinsInverse] at hq
  | _ => trivial

/-- **A path whose computed hints are pinned locally but those satisfying `p2`** is exact on a reader where those are:
what a function with hints pinned only through memory (or callees) needs of its own valuation. -/
theorem exact_of_pinned_except {rd : Reader} {σ : Val} {body : List Stmt} {es : List Ev} {vs : List V}
    {p2 : Atom → Bool} (hpin : Stmt.blockNextOk (fun a => isComputed a && !p2 a) pinsInverse body = true)
    (hw : walk σ body = .ret es vs) (hes : ∀ e ∈ es, e.Holds rd σ)
    (h2 : ∀ a, Ev.atom a ∈ es → p2 a = true → a.Exact rd σ) : ∀ e ∈ es, e.Exact rd σ := by
  have hp := walk_partnered (σ := σ) body hpin
  rw [hw] at hp
  intro e he
  cases e with
  | atom a =>
    cases h2a : p2 a with
    | true => exact h2 a he h2a
    | false =>
      cases hc : isComputed a with
      | false => exact exact_of_not_computed hc
      | true =>
        obtain ⟨b, hb, hq⟩ := hp a he (by simp only [hc, h2a]; rfl)
        cases a with
        | hint h =>
          cases h with
          | inverse x i =>
            cases b with
            | assertNe x' i' p' =>
              simp only [pinsInverse, Bool.and_eq_true, beq_iff_eq] at hq
              obtain ⟨rfl, rfl⟩ := hq
              exact inverse_exact (rd := rd) (hes _ hb)
            | _ => simp [pinsInverse] at hq
          | _ => simp [pinsInverse] at hq
        | _ => simp [pinsInverse] at hq
  | _ => trivial

/-- **A path whose computed hints are pinned locally but the atoms `sites`** is exact where those are. -/
theorem exact_of_sites {rd : Reader} {σ : Val} {body : List Stmt} {es : List Ev} {vs : List V} {sites : List Atom}
    (hpin : Stmt.blockNextOk (fun a => isComputed a && !decide (a ∈ sites)) pinsInverse body = true)
    (hw : walk σ body = .ret es vs) (hes : ∀ e ∈ es, e.Holds rd σ)
    (h : ∀ a ∈ sites, Ev.atom a ∈ es → a.Exact rd σ) : ∀ e ∈ es, e.Exact rd σ :=
  exact_of_pinned_except (p2 := fun a => decide (a ∈ sites)) hpin hw hes fun a ha h2 => h a (of_decide_eq_true h2) ha

/-- A node is exact when its path is. -/
theorem exactAt_of_walk {P : Core.Program} {rd : Reader} {σ : Val} {f : String} {fn : Fn} {es : List Ev}
    {vs : List V} (hf : P.find? f = some fn) (hw : walk σ fn.body = .ret es vs) (h : ∀ e ∈ es, e.Exact rd σ) :
    ExactAt P rd f σ := by
  have hev : (Tree.node f σ [] []).events P = es := by simp only [Tree.events, Tree.name, Tree.val, hf, hw]
  rw [ExactAt, hev]
  exact h

/-- **Function `j` and its callees, `d` calls deep, have their computed hints pinned locally.** -/
noncomputable def exactJ : ℕ → ℕ → Bool
  | 0, _ => false
  | d + 1, j => match coreProgram[j]? with
    | none => false
    | some fn => Stmt.blockNextOk isComputed pinsInverse fn.body &&
        (Stmt.blockCallees fn.body).all (fun g => (calleeIdx j g).isSome) &&
        (Data.calleesJ j).all fun k => k == j || exactJ d k

/-- **The check**: function `j` is named `g`, and every computed hint in its subtree is pinned locally. -/
noncomputable def exactFree (g : String) (j : ℕ) : Bool :=
  decide ((coreProgram[j]?).map Fn.name = some g) && exactJ 8 j

/-- The functions passing the check at some depth. -/
def ExactFreeG (g : String) : Prop := ∃ d j, (coreProgram[j]?).map Fn.name = some g ∧ exactJ d j = true

theorem exactFreeG_of {g : String} {j : ℕ} (h : exactFree g j = true) : ExactFreeG g := by
  simp only [exactFree, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨8, j, h.1, h.2⟩

/-- **The functions passing the check are call-closed, and their paths that hold are exact on every reader.** -/
theorem coreProgram_exactIn (rd : Reader) :
    coreProgram.EveryIn rd (fun f σ => ∀ rd', ExactAt coreProgram rd' f σ) ExactFreeG := by
  rintro f ⟨d, j, hn, hj⟩ fn hf
  cases d with
  | zero => simp [exactJ] at hj
  | succ d =>
    obtain ⟨fn', hfn', rfl⟩ := Option.map_eq_some_iff.mp hn
    have e : fn = fn' := Option.some.inj (hf.symm.trans (coreProgram_find?_at hfn'))
    subst e
    have hj' := hj
    rw [exactJ, hfn'] at hj'
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hj'
    obtain ⟨⟨hb, hcal⟩, hks⟩ := hj'
    refine ⟨fun g hg => ?_, fun σ es vs hw hes rd' e he => ?_⟩
    · obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (hcal g hg)
      have hs := calleeIdx_spec hk
      rcases hks k (List.mem_of_find?_eq_some hk) with rfl | h
      · exact ⟨d + 1, k, hs, hj⟩
      · exact ⟨d, k, hs, h⟩
    · have hev : (Tree.node fn.name σ [] []).events coreProgram = es := by
        simp only [Tree.events, Tree.name, Tree.val, hf, hw]
      rw [hev] at he
      exact exact_of_pinned hb hw hes rd' e he

/-- Function `j`'s callee `g` has its subtree's computed hints pinned locally. -/
noncomputable def exactCallee (j : ℕ) (g : String) : Bool :=
  match calleeIdx j g with
  | some k => exactJ 8 k
  | none => false

theorem exactFreeG_of_callee {j : ℕ} {g : String} (h : exactCallee j g = true) : ExactFreeG g := by
  unfold exactCallee at h
  split at h
  · next k hk => exact ⟨8, k, calleeIdx_spec hk, h⟩
  · exact absurd h Bool.false_ne_true

/-- **A valid tree of a function passing the check is exact**, on every reader. -/
theorem every_exact_of_free {rd : Reader} {g : String} (hg : ExactFreeG g) {t : Tree} {args rets : List E}
    (hv : t.Valid coreProgram rd args rets) (hn : t.name = g) (rd' : Reader) :
    t.Every (ExactAt coreProgram rd') :=
  (every_of_everyIn (coreProgram_exactIn rd) t hv (hn ▸ hg)).mono fun _ _ h => h rd'

end
end LeanVM.Guest.Memory
