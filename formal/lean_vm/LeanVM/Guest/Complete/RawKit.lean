/-
  LeanVM.Guest.Complete.RawKit

  Tools for the raw signatures' loops placed: a word read where it is defined, a cell of a run read
  at its pointer, a body's loads through named values, streams of a `flatMap`.
-/

module

public import LeanVM.Guest.Complete.LoadVar
public import LeanVM.Guest.Complete.TransferA
public import LeanVM.Guest.Complete.DaPadA
public import LeanVM.Guest.B1.VsC.LoopLeafA

/-!
# The raw loops' kit

* `read_def`: a word defined at index `e` is read at `g^e` (a range check's witness, where the
  memory is defined rather than below `2^k`).
* `loadHolds_ptr`: the cell `j` of a run read at its base `ptrAt b` is read at `ptrAt b · g^j`.
* `loads_of_loadVarB`: on a path of a body every atom of which passes `loadVarB ps`, every load
  reads a cell of `R` and no hint writes a heap word, when each value of `ps` points into `R`.
* `hints_of_quietB`: likewise for the hints of a body every atom of which passes `quietB`.
* `sameStreams_flatMap`: streams compared entry block by entry block.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- **Every atom on a path satisfies what every atom of the body does** (`VsC.Oq.VmcA`'s, whose
module this one cannot import beside `LoopLeafA`). -/
theorem walk_atomsAll' {σ : Val} {body : List Stmt} {es : List Ev} {vs : List V} {p : Atom → Bool}
    (h : Stmt.atomsAll p body = true) (hw : walk σ body = .ret es vs) :
    ∀ a, Ev.atom a ∈ es → p a = true := by
  have h' : Stmt.atomsAll (fun a => !(fun a => !p a) a) body = true := by
    simpa only [Bool.not_not] using h
  have hp := walk_partnered (σ := σ) (p := fun a => !p a) (q := fun _ _ => false) body
    (blockNextOk_of_atomsAll body h')
  rw [hw] at hp
  intro a ha
  by_contra hc
  obtain ⟨b, -, hb⟩ := hp a ha (by simpa using hc)
  exact absurd hb (by simp)

/-- No call on a path of a body placing nothing and calling nothing. -/
theorem calls_nil_of_pure' {σ : Val} {body : List Stmt} {es : List Ev} {vs : List V}
    (h : Stmt.pureList [] body = true) (hw : walk σ body = .ret es vs) : calls es = [] := by
  have hp := walk_pure (σ := σ) body h
  rw [hw] at hp
  refine List.filterMap_eq_nil_iff.mpr fun e he => ?_
  have := hp e he
  cases e with
  | call f _ _ => simp [Ev.pure] at this
  | skip f _ => simp [Ev.pure] at this
  | _ => rfl

/-- **A word defined at index `e` is read at `g^e`.** -/
theorem read_def {rd : Reader} {e : ℕ} (h : (rd (addressOfIndex e)).isSome) :
    LoadHolds rd (gen ^ e) 0 ((rd (addressOfIndex e)).getD 0) := by
  rw [gen_pow_eq_ofK]
  refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
  rw [Main.addr_ofK, Nat.add_zero]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  rw [hv]; rfl

/-- **A run's cell `j`, read at its pointer.** -/
theorem loadHolds_ptr {rd : Reader} {b j : ℕ} {xs : List E} (h : ReadsAt rd (ptrAt b) xs) (hj : j < xs.length) :
    LoadHolds rd (ptrAt b * gen ^ j) 0 xs[j] := by
  obtain ⟨-, hr⟩ := h j hj
  rw [ptrAt_mul_gen_pow]
  refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
  rw [Main.addr_ofK, Nat.add_zero]
  rwa [Main.addr_ofK] at hr

/-- **A body's loads through named values**: on a path, every load reads a cell of `R` and no
hint writes a heap word, when each value `.n v` of `ps` points at `b` with its cells in `R`. -/
theorem loads_of_loadVarB {σ : Val} {body : List Stmt} {es : List Ev} {vs : List V} {ps : List (ℕ × ℕ)}
    (h : Stmt.atomsAll (loadVarB ps) body = true) (hw : walk σ body = .ret es vs) {R : ℕ → Prop}
    (hp : ∀ q ∈ ps, ∃ b, σ (.n q.1) = ptrAt b ∧ ∀ o < q.2, R (b + o)) :
    (∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧ R i) ∧
      ∀ A ∈ heapHintAddrs σ es, ∃ i, A = addressOfIndex i ∧ R i := by
  have hok := walk_atomsAll' h hw
  refine ⟨fun A hA => ?_, fun A hA => ?_⟩
  · obtain ⟨e, he, hA⟩ := List.mem_filterMap.mp hA
    cases e with
    | atom a =>
      have hk := hok a he
      cases a with
      | load d p off =>
        simp only [Ev.loadAddr?, Option.some.injEq] at hA
        simp only [loadVarB, atomUnplaced, Bool.true_and, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq] at hk
        obtain ⟨q, hqm, rfl, hoff⟩ := hk
        obtain ⟨b, hb, hR⟩ := hp q hqm
        exact ⟨b + off, by rw [← hA, hb]; exact Main.addr_ofK b off, hR off hoff⟩
      | _ => simp [Ev.loadAddr?] at hA
    | _ => simp [Ev.loadAddr?] at hA
  · obtain ⟨e, he, hA⟩ := List.mem_flatMap.mp hA
    cases e with
    | atom a =>
      have hk := hok a he
      cases a with
      | hint hh =>
        simp only [loadVarB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hk
        simp [Ev.hintAddrs, hk.2] at hA
      | _ => simp [Ev.hintAddrs] at hA
    | _ => simp [Ev.hintAddrs] at hA

/-- **No hint of a quiet body writes a heap word.** -/
theorem hints_of_quietB {σ : Val} {body : List Stmt} {es : List Ev} {vs : List V}
    (h : Stmt.atomsAll quietB body = true) (hw : walk σ body = .ret es vs) {R : ℕ → Prop} :
    ∀ A ∈ heapHintAddrs σ es, ∃ i, A = addressOfIndex i ∧ R i := by
  have hok := walk_atomsAll' h hw
  intro A hA
  obtain ⟨e, he, hA⟩ := List.mem_flatMap.mp hA
  cases e with
  | atom a =>
    have hk := hok a he
    cases a with
    | hint hh =>
      simp only [quietB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hk
      simp [Ev.hintAddrs, hk.2] at hA
    | _ => simp [Ev.hintAddrs] at hA
  | _ => simp [Ev.hintAddrs] at hA

/-- **Streams compared block by block.** -/
theorem sameStreams_flatMap {α : Type} {F G : α → List Pop} :
    ∀ (l : List α), (∀ x ∈ l, SameStreams (F x) (G x)) → SameStreams (l.flatMap F) (l.flatMap G)
  | [], _ => SameStreams.refl _
  | x :: l, h => by
      simp only [List.flatMap_cons]
      exact (h x List.mem_cons_self).append (sameStreams_flatMap l fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- An entry before streams compared. -/
theorem sameStreams_consR (p : Pop) {a b : List Pop} (h : SameStreams a b) : SameStreams (p :: a) (p :: b) :=
  (SameStreams.refl [p]).append h

theorem count_eq_gen (n : ℕ) : Prover.count n = gen ^ n := by
  simp [Prover.count, LeanVM.Protocol.Verifier.gpow]

/-- A `flatMap` over a zip, by index. -/
theorem flatMap_zip_range {α β γ : Type} (xs : List α) (ys : List β) (hl : ys.length = xs.length) (x0 : α) (y0 : β)
    (f : α × β → List γ) :
    (xs.zip ys).flatMap f = (List.range xs.length).flatMap fun i => f (xs.getD i x0, ys.getD i y0) := by
  have h : xs.zip ys = (List.range xs.length).map fun i => (xs.getD i x0, ys.getD i y0) :=
    List.ext_getElem (by simp [hl]) fun i h1 h2 => by
      have hi : i < xs.length := by simpa using h2
      have hi' : i < ys.length := hl ▸ hi
      simp [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi']
  rw [h, List.flatMap_map]

end
end LeanVM.Guest.Complete
