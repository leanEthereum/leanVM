/-
  LeanVM.Guest.B1.Opening.WalkPops

  The witness-stream entries `walk_path`, inline in a query, pops: its path's siblings
  (`merkle_children`).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesComplete3
public import LeanVM.Guest.B1.Sig.PopsKit
import LeanVM.Guest.StmtsAppend

/-!
# `walk_path`'s pops

* `noWit`, `fallPops_noWit`: a block of atoms none a witness hint pops nothing; `SplicePops.callIf`: a conditional call pops its callee's entries;
* `oqWalkT_fallPops`: the walk, its windows' words arms of their matches, pops its hinted
  siblings' cells, one `merkle_children` entry;
* `WD.wpPops w`: the sibling cells `w.pc` of an honest walk, one `merkle_children` entry.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- Every statement an atom, none a witness hint. -/
def noWit (ss : List Stmt) : Bool := ss.all fun s => match s with
  | .atom (.hint (.witness ..)) => false
  | .atom _ => true
  | _ => false

theorem noWit_append (xs ys : List Stmt) : noWit (xs ++ ys) = (noWit xs && noWit ys) := List.all_append

theorem noWit_iff {ss : List Stmt} : noWit ss = true ↔ ∀ s ∈ ss, (match s with
    | .atom (.hint (.witness ..)) => false
    | .atom _ => true
    | _ => false) = true := List.all_eq_true

/-- **A block of atoms none a witness hint pops nothing.** -/
theorem fallPops_noWit (σ : Val) : ∀ {ss : List Stmt}, noWit ss = true → FallPops rd σ ss []
  | [], _ => FallPops.nil
  | s :: ss, h => by
    simp only [noWit, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have ih := fallPops_noWit σ (ss := ss) h2
    match s, h1 with
    | .atom a, h1 =>
      have hp : a.pops rd σ = [] := by
        cases a with
        | hint x => cases x <;> simp_all [Atom.pops, Hint.pops]
        | _ => rfl
      simpa [hp] using ih.cons_atom (a := a)

theorem fallPops_eq {ss : List Stmt} {p q : List Pop} (h : FallPops rd σ ss p) (e : p = q) : FallPops rd σ ss q :=
  e ▸ h

theorem fallPops_flatten_nil : ∀ {l : List (List Stmt)}, (∀ x ∈ l, FallPops rd σ x []) →
    FallPops rd σ l.flatten []
  | [], _ => FallPops.nil
  | x :: l, h => by
    rw [List.flatten_cons]
    simpa using (h x (by simp)).append (fallPops_flatten_nil fun y hy => h y (by simp [hy]))

/-! ## Blocks and calls -/

theorem noWit_flatten_map {α : Type} {f : α → List Stmt} : ∀ {l : List α}, (∀ a ∈ l, noWit (f a) = true) →
    noWit (l.map f).flatten = true
  | [], _ => rfl
  | a :: l, h => by
    rw [List.map_cons, List.flatten_cons, noWit_append, h a (by simp),
      noWit_flatten_map fun b hb => h b (by simp [hb])]
    rfl

theorem SplicePops.congr_ks {ss : List Stmt} {ks ks' : List (List Pop)} {p : List Pop}
    (h : SplicePops rd σ ss ks p) (e : ks = ks') : SplicePops rd σ ss ks' p := e ▸ h

/-- **A conditional call pops its callee's entries**, a phantom's when not taken. -/
theorem SplicePops.callIf (c : V) (f : String) (args : List V) (k : List Pop) :
    SplicePops rd σ [.callIf c f args] [k] k := by
  refine ⟨[.inK c, if σ c = 0 then .skip f args else .call f args []], ?_, ?_, ?_⟩
  · simp [walk, walk1, Out.seq, Out.pre]
  · split <;> rfl
  · split <;> simp [splice]

/-! ## The walk -/

theorem oqStepT_noWit (pr ch l K n0 n1 : ℕ) (bit : Bool) : noWit (oqStepT pr ch l K n0 n1 bit) = true := rfl

theorem oqArmT_noWit (s : Oq) (pr kN ch i a : ℕ) : noWit (oqArmT s pr kN ch i a) = true := by
  rw [oqArmT, noWit_append, Bool.and_eq_true]
  refine ⟨noWit_iff.mpr fun st hst => ?_, rfl⟩
  obtain ⟨blk, hb, hst⟩ := List.mem_flatten.mp hst
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hb
  exact noWit_iff.mp (oqStepT_noWit _ _ _ _ _ _ _) st hst

theorem oqCapT_noWit (bp cap flags : V) (k n npw : ℕ) : noWit (oqCapT bp cap flags k n npw) = true := rfl

/-- A window, its word an arm of its match, pops nothing. -/
theorem oqWinT_fallPops {s : Oq} {bp : V} {pr kN ch i k : ℕ} (hk : k < 2 ^ oqWw s i)
    (hx : σ (.n (oqWk s ch i)) = ofK (addressOfIndex k)) : FallPops rd σ (oqWinT s bp pr kN ch i) [] := by
  have h6 : 2 ^ oqWw s i ≤ 2 ^ 6 := Nat.pow_le_pow_right (by omega) (oqWw_le s i)
  have e : oqWinT s bp pr kN ch i = [.atom (.load (.n (oqWk s ch i)) bp i),
      .atom (.const (.n (oqWk s ch i + 1)) (word (2 ^ 63) 0))] ⧺
      [.match_ (.n (oqWk s ch i)) ((List.range (2 ^ oqWw s i)).map (oqArmT s pr kN ch i))] := rfl
  rw [e]
  have hm : FallPops rd σ [.match_ (.n (oqWk s ch i))
      ((List.range (2 ^ oqWw s i)).map (oqArmT s pr kN ch i))] [] :=
    FallPops.match_ (k := k) (by simpa using hk) (by omega) hx (by
      rw [List.getElem_map, List.getElem_range]
      exact fallPops_noWit σ (oqArmT_noWit _ _ _ _ _ _))
  exact fallPops_eq ((fallPops_noWit σ (ss := [.atom (.load (.n (oqWk s ch i)) bp i),
    .atom (.const (.n (oqWk s ch i + 1)) (word (2 ^ 63) 0))]) rfl).append hm) rfl

/-- **The walk pops its hinted siblings' cells**, its windows' words arms of their matches. -/
theorem oqWalkT_fallPops {s : Oq} {bp cap flags : V} {pr kN ch : ℕ}
    (hsel : ∀ i < oqNpw s, ∃ k < 2 ^ oqWw s i, σ (.n (oqWk s ch i)) = ofK (addressOfIndex k)) :
    FallPops rd σ (oqWalkT s bp cap flags pr kN ch)
      [("merkle_children", (List.range (2 * s.pd)).map fun j ↦ σ (.n (ch + j)))] := by
  have hh : FallPops rd σ [.atom (.hint (.witness "merkle_children"
      (.stack ((List.range (2 * s.pd)).map fun j ↦ .n (ch + j)))))]
      [("merkle_children", (List.range (2 * s.pd)).map fun j ↦ σ (.n (ch + j)))] := by
    refine fallPops_eq (FallPops.atom _) ?_
    simp only [Atom.pops, Hint.pops, Dest.words, List.map_map]
    rfl
  have hw : FallPops rd σ ((List.range (oqNpw s)).map (oqWinT s bp pr kN ch)).flatten [] :=
    fallPops_flatten_nil fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      obtain ⟨k, hk, hx⟩ := hsel i (List.mem_range.mp hi)
      exact oqWinT_fallPops hk hx
  exact fallPops_eq ((hh.append hw).append (fallPops_noWit σ (oqCapT_noWit _ _ _ _ _ _))) (by simp)

namespace WD

variable (w : WD)

/-- **An honest walk's entries**: its siblings' cells, one `merkle_children` entry. -/
def wpPops : List Pop := [("merkle_children", (List.range (2 * w.pd)).map w.pc)]

variable {w} {ch kN pr : ℕ} {bp cap flags : V}

end WD

end
end LeanVM.Guest.B1
