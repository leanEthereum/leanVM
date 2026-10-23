/-
  LeanVM.Guest.B1.Main.HonestCounts

  The counts of `main`'s honest words within the deployed limits, the sizes of its buffers, and
  where each region's writers stand.
-/

module

public import LeanVM.Guest.B1.Main.HonestWords

/-!
# The honest counts

Within `Limits`, the regions' writers are as many as their slots (`writersX_length`, …), so the
writers' numbers end at the coverage table's size (`hbase_children`), every count is below the
guest's bounds, and the buffers have the sizes `main` allocates. A region's writer is a raw claim
or a child's claim (`writersX_raw`, `writersX_child`), numbered by `gX` (`gX_raw`, `gX_child`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (direct)
open LeanVM.Guest.End (Limits coverage)

@[expose] public section

variable {seed : Digest} {s : NodeStatement} {w : NodeWitness}

/-! ## Flattened lists -/

theorem getElem?_flatten_map {β γ : Type} (f : γ → List β) : ∀ (L : List γ) (c j : ℕ)
    (hc : c < L.length), j < (f L[c]).length →
    ((L.map f).flatten)[((L.take c).map fun x => (f x).length).sum + j]? = (f L[c])[j]?
  | [], _, _, hc, _ => absurd hc (by simp)
  | x :: L, 0, j, _, hj => by
    simp only [List.getElem_cons_zero] at hj
    simp [List.getElem?_append_left hj]
  | x :: L, c + 1, j, hc, hj => by
    simp only [List.getElem_cons_succ] at hj ⊢
    simp only [List.map_cons, List.flatten_cons, List.take_succ_cons, List.sum_cons]
    rw [List.getElem?_append_right (by omega), show (f x).length + ((L.take c).map fun x => (f x).length).sum
      + j - (f x).length = ((L.take c).map fun x => (f x).length).sum + j by omega]
    exact getElem?_flatten_map f L c j (by simpa using hc) hj

theorem sum_take_map_le {γ : Type} (g : γ → ℕ) (L : List γ) (c : ℕ) :
    ((L.take c).map g).sum ≤ (L.map g).sum :=
  calc ((L.take c).map g).sum ≤ ((L.take c).map g).sum + ((L.drop c).map g).sum := Nat.le_add_right _ _
    _ = (L.map g).sum := by rw [← List.sum_append, ← List.map_append, List.take_append_drop]

theorem sum_take_succ {γ : Type} (g : γ → ℕ) (L : List γ) (c : ℕ) (hc : c < L.length) :
    ((L.take (c + 1)).map g).sum = ((L.take c).map g).sum + g L[c] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hc, Option.toList_some, List.map_append,
    List.sum_append]
  simp

theorem length_flatten_map {β γ : Type} (f : γ → List β) (L : List γ) :
    (L.map f).flatten.length = (L.map fun x => (f x).length).sum := by
  simp [List.length_flatten, List.map_map, Function.comp_def]

/-! ## The regions' writers -/

theorem writersX_len : (writersX s w).length = hrx s w + (w.children.map cnx).sum := by
  simp [writersX, hrx, List.length_flatten, Function.comp_def]; rfl

theorem writersS_len : (writersS s w).length = hrs s w + (w.children.map cns).sum := by
  simp [writersS, hrs, List.length_flatten, Function.comp_def]; rfl

theorem writersD_len : (writersD s w).length = hrd s w + (w.children.map cnda).sum := by
  simp [writersD, hrd, List.length_flatten, Function.comp_def]; rfl

theorem sum_cnw (L : List Child) :
    (L.map cnw).sum = (L.map cnx).sum + (L.map cns).sum + (L.map cnda).sum := by
  induction L with
  | nil => rfl
  | cons c L ih => simp only [List.map_cons, List.sum_cons, ih, cnw]; ring

/-- **The children's writers end at the coverage table's size.** -/
theorem hbase_children (hlim : Limits s w) :
    hbase s w w.children.length = (honestWords seed s w).total := by
  have h1 := writersX_length hlim
  have h2 := writersS_length hlim
  have h3 := writersD_length hlim
  rw [writersX_len] at h1
  rw [writersS_len] at h2
  rw [writersD_len] at h3
  simp only [hbase, List.take_length, sum_cnw, MainWords.total, honestWords]
  omega

theorem writersX_raw {i : ℕ} (hi : i < hrx s w) :
    (writersX s w)[i]? = some ((direct s.claims.xmss w.xmss)[i]'hi).1 := by
  rw [writersX, List.getElem?_append_left (by simpa [hrx] using hi)]
  simp only [List.getElem?_map, List.getElem?_eq_getElem (by simpa [hrx] using hi), Option.map_some]

theorem writersS_raw {i : ℕ} (hi : i < hrs s w) :
    (writersS s w)[i]? = some ((direct s.claims.sphincs w.sphincs)[i]'hi).1 := by
  rw [writersS, List.getElem?_append_left (by simpa [hrs] using hi)]
  simp only [List.getElem?_map, List.getElem?_eq_getElem (by simpa [hrs] using hi), Option.map_some]

theorem writersD_raw {i : ℕ} (hi : i < hrd s w) :
    (writersD s w)[i]? = some ((direct s.claims.da w.da)[i]'hi).1 := by
  rw [writersD, List.getElem?_append_left (by simpa [hrd] using hi)]
  simp only [List.getElem?_map, List.getElem?_eq_getElem (by simpa [hrd] using hi), Option.map_some]

theorem writersX_child {c j : ℕ} (hc : c < w.children.length)
    (hj : j < w.children[c].statement.claims.xmss.length) :
    (writersX s w)[hrx s w + ((w.children.take c).map cnx).sum + j]? =
      w.children[c].statement.claims.xmss[j]? := by
  rw [writersX, Nat.add_assoc, List.getElem?_append_right (by simp [hrx]),
    show hrx s w + (((w.children.take c).map cnx).sum + j) -
      ((direct s.claims.xmss w.xmss).map (·.1)).length = ((w.children.take c).map cnx).sum + j by
      simp [hrx]]
  exact getElem?_flatten_map (fun c : Child => c.statement.claims.xmss) w.children c j hc hj

theorem writersS_child {c j : ℕ} (hc : c < w.children.length)
    (hj : j < w.children[c].statement.claims.sphincs.length) :
    (writersS s w)[hrs s w + ((w.children.take c).map cns).sum + j]? =
      w.children[c].statement.claims.sphincs[j]? := by
  rw [writersS, Nat.add_assoc, List.getElem?_append_right (by simp [hrs]),
    show hrs s w + (((w.children.take c).map cns).sum + j) -
      ((direct s.claims.sphincs w.sphincs).map (·.1)).length = ((w.children.take c).map cns).sum + j by
      simp [hrs]]
  exact getElem?_flatten_map (fun c : Child => c.statement.claims.sphincs) w.children c j hc hj

theorem writersD_child {c j : ℕ} (hc : c < w.children.length)
    (hj : j < w.children[c].statement.claims.da.length) :
    (writersD s w)[hrd s w + ((w.children.take c).map cnda).sum + j]? =
      w.children[c].statement.claims.da[j]? := by
  rw [writersD, Nat.add_assoc, List.getElem?_append_right (by simp [hrd]),
    show hrd s w + (((w.children.take c).map cnda).sum + j) -
      ((direct s.claims.da w.da).map (·.1)).length = ((w.children.take c).map cnda).sum + j by
      simp [hrd]]
  exact getElem?_flatten_map (fun c : Child => c.statement.claims.da) w.children c j hc hj

/-! ## The writers' numbers -/

theorem gX_raw {i : ℕ} (hi : i < hrx s w) : gX s w i = i := by simp [gX, hi]

theorem gS_raw {i : ℕ} (hi : i < hrs s w) : gS s w i = hrx s w + i := by simp [gS, hi]

theorem gD_raw {i : ℕ} (hi : i < hrd s w) : gD s w i = hrx s w + hrs s w + i := by simp [gD, hi]

theorem gX_child {c j : ℕ} (hc : c < w.children.length) (hj : j < cnx w.children[c]) :
    gX s w (hrx s w + ((w.children.take c).map cnx).sum + j) = hbase s w c + j := by
  rw [gX, ite_neg' (by omega), show hrx s w + ((w.children.take c).map cnx).sum + j - hrx s w =
    ((w.children.take c).map cnx).sum + j by omega, locIn_at _ _ _ _ c j hc hj, hbase]
  simp

theorem gS_child {c j : ℕ} (hc : c < w.children.length) (hj : j < cns w.children[c]) :
    gS s w (hrs s w + ((w.children.take c).map cns).sum + j) = hbase s w c + cnx w.children[c] + j := by
  rw [gS, ite_neg' (by omega), show hrs s w + ((w.children.take c).map cns).sum + j - hrs s w =
    ((w.children.take c).map cns).sum + j by omega, locIn_at _ _ _ _ c j hc hj, hbase]

theorem gD_child {c j : ℕ} (hc : c < w.children.length) (hj : j < cnda w.children[c]) :
    gD s w (hrd s w + ((w.children.take c).map cnda).sum + j) =
      hbase s w c + (cnx w.children[c] + cns w.children[c]) + j := by
  rw [gD, ite_neg' (by omega), show hrd s w + ((w.children.take c).map cnda).sum + j - hrd s w =
    ((w.children.take c).map cnda).sum + j by omega, locIn_at _ _ _ _ c j hc hj, hbase]

theorem hbase_succ {c : ℕ} (hc : c < w.children.length) :
    hbase s w (c + 1) = hbase s w c + cnw w.children[c] := by
  rw [hbase, hbase, sum_take_succ _ _ _ hc]; ring

end
end LeanVM.Guest.B1.Main
