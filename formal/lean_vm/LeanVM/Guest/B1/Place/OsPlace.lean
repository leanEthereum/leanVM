/-
  LeanVM.Guest.B1.Place.OsPlace

  Helpers for placing a straight-line function returning some of its buffers: its loads' regions, its returned
  buffers' layout, the placed form at an optional words bound.
-/

module

public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.B1.Place.HelperAt
public import LeanVM.Guest.B1.Main.KidsT

/-!
# Straight-line bodies returning buffers, placed

`os_addr_in_regionL`: a load that holds on every memory holding the function's buffers and the caller's words lies
in their region. `osLoutJ`: the returned buffers `js`' layout (`os_bufL_getD`, `os_perm_pick`). `CompleteAtOT`: the
placed form at an optional words bound, by a tree of a predicate; `FlatNodeT`: a flat body's node with its callees'
trees satisfying their predicates (`OsPlaceR.lean` proves it).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A word every memory holding `M` holds at `A` lies in `M`'s region.** -/
theorem os_addr_in_regionL {κ : ℕ} {M : Layout} {A : K} {v : E}
    (hall : ∀ rd, LowDef κ rd → MemL rd M → rd A = some v) {rd : Reader} (hlow : LowDef κ rd)
    (hL : MemL rd M) : ∃ i, A = addressOfIndex i ∧ RegionL M i := by
  classical
  by_contra hn
  simp only [not_exists, not_and] at hn
  let rd2 : Reader := fun B => if B = A then some (v + 1) else rd B
  have hlow2 : LowDef κ rd2 := fun i hi => by
    simp only [rd2]; split
    · rfl
    · exact hlow i hi
  have hL2 : MemL rd2 M := by
    intro q hq k hk
    refine ⟨(hL q hq k hk).1, ?_⟩
    rw [Main.addr_ofK]
    have hne : addressOfIndex (q.1 + k) ≠ A := fun he
        => hn (q.1 + k) he.symm ⟨q, hq, by omega, by omega⟩
    simp only [rd2, hne, ↓reduceIte]
    rw [← Main.addr_ofK]; exact (hL q hq k hk).2
  have := hall rd2 hlow2 hL2
  simp only [rd2, ↓reduceIte, Option.some.injEq] at this
  exact one_ne_zero (by linear_combination this : (1 : E) = 0)

theorem os_bases_getD : ∀ (b : ℕ) (sizes : List ℕ) (j : ℕ), j < sizes.length →
    (bases b sizes).getD j 0 = b + (sizes.take j).sum
  | _, [], _, h => absurd h (by simp)
  | b, s :: sizes, 0, _ => by simp [bases]
  | b, s :: sizes, j + 1, h => by
    simp only [bases, List.getD_cons_succ, List.take_succ_cons, List.sum_cons]
    rw [os_bases_getD (b + s) sizes j (by simpa using h)]; ring

theorem os_length_bases : ∀ (b : ℕ) (sizes : List ℕ), (bases b sizes).length = sizes.length
  | _, [] => rfl
  | b, _ :: sizes => by simp [bases, os_length_bases _ sizes]

theorem os_bufL_getD {b : ℕ} {sizes : List ℕ} {own : List (List E)} {j : ℕ}
    (hown : List.Forall₂ (fun c s => c.length ≤ s) own sizes) (hj : j < sizes.length) :
    (bufL b sizes own).getD j default = ((bases b sizes).getD j 0, own.getD j []) := by
  have hl1 : (bases b sizes).length = sizes.length := os_length_bases b sizes
  have hl2 : own.length = sizes.length := hown.length_eq
  simp only [bufL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hl1 ▸ hj),
    List.getElem?_eq_getElem (hl2 ▸ hj), Option.getD_some]
  rw [List.getElem?_eq_getElem (by simp [hl1, hl2, hj]), Option.getD_some, List.getElem_zip]

theorem os_map_getD_range {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun j => l.getD j d) = l := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2, Option.getD_some]

/-- The entries `js` of `l`, then the others, are `l` permuted. -/
theorem os_perm_pick {α : Type} (l : List α) (d : α) (js : List ℕ) (hjs : js.Nodup)
    (hjl : ∀ j ∈ js, j < l.length) :
    (js.map (fun j => l.getD j d) ++
      ((List.range l.length).filter (fun j => decide (j ∉ js))).map (fun j => l.getD j d)).Perm l := by
  conv_rhs => rw [← os_map_getD_range l d]
  rw [← List.map_append]
  refine List.Perm.map _ ?_
  have h1 : ((List.range l.length).filter (fun j => decide (j ∈ js)) ++
      (List.range l.length).filter (fun j => !decide (j ∈ js))).Perm (List.range l.length) :=
    List.filter_append_perm _ _
  have h2 : ((List.range l.length).filter (fun j => decide (j ∈ js))).Perm js := by
    refine (List.perm_ext_iff_of_nodup ((List.nodup_range).filter _) hjs).mpr fun x => ?_
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hjl x h, h⟩⟩
  have h3 : (List.range l.length).filter (fun j => decide (j ∉ js)) =
      (List.range l.length).filter (fun j => !decide (j ∈ js)) := by
    congr 1
  rw [h3]
  exact (h2.symm.append_right _).trans h1

/-- The layout of the returned buffers `js`. -/
def osLoutJ (b : ℕ) (sizes : List ℕ) (own : List (List E)) (js : List ℕ) : Layout :=
  js.map fun j => (b + (sizes.take j).sum, own.getD j [])



/-- **`CompleteAtO` by a tree satisfying a predicate of the memory.** -/
def CompleteAtOT (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) (Bd : Option ℕ) (T : Reader → Tree → Prop) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ (∀ B ∈ Bd, n ≤ B) ∧ ∀ rd, LowDef k rd →
      MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInT coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp n f args rets (T rd)

theorem CompleteAtOT.toO {k : ℕ} {f : String} {Lin : Layout} {args : List E} {Out : List E → Layout → Prop}
    {Bd : Option ℕ} {T : Reader → Tree → Prop} (h : CompleteAtOT fs cert k f Lin args Out Bd T) :
    CompleteAtO fs cert k f Lin args Out Bd := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, hn, fun rd hl hm => (hr rd hl hm).relAtIn⟩

/-- **A flat function's node**: at a valuation `σ` with `Q σ`, its body's walk returning, its callees' trees
satisfying `Ts σ rd`. -/
def FlatNodeT (f : String) (fn : Fn) (pre : List Stmt) (Q : Val → Prop) (Ts : Val → Reader → List (Tree → Prop))
    (rd : Reader) (t : Tree) : Prop :=
  ∃ (σ : Val) (bufs : List ℕ) (ks : List Tree) (es : List Ev) (vs : List V), t = .node f σ bufs ks ∧
    walk σ fn.body = .ret es vs ∧ calls es = (pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ) ∧ Q σ ∧
    KidsT (calls es) (Ts σ rd) ks

theorem os_kidsFromInT_rmono {rd : Reader} {σ : Val} {R R' : ℕ → Prop} (hR : ∀ i, R i → R' i) :
    ∀ (cs : List Call) (Ts : List (Tree → Prop)) (Dacc : ℕ → Prop) (b n : ℕ) (D : ℕ → Prop),
      KidsFromInT coreProgram fs cert rd σ R Dacc cs Ts b n D →
        KidsFromInT coreProgram fs cert rd σ R' Dacc cs Ts b n D
  | [], _, _, _, _, _, h => h
  | _ :: cs, Ts, _, _, _, _, ⟨m, n', Rk, Dk, hn, hRk, hc, hk⟩ =>
    ⟨m, n', Rk, Dk, hn, fun i hi => (hRk i hi).imp_left (hR i), hc, os_kidsFromInT_rmono hR cs Ts.tail _ _ _ _ hk⟩

end
end LeanVM.Guest.B1
