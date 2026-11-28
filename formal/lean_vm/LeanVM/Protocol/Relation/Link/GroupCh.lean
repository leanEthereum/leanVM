/-
  LeanVM.Protocol.Relation.Link.GroupCh

  Where `verify_link`'s named challenges sit among `(θ_0, drawn)`: each of `θ`, `ε`, `τ`, `ν` is
  one coordinate of the draw.
-/

module

public import LeanVM.Protocol.Relation.Link.Fold
public import LeanVM.Protocol.Relation.Link.GroupPoly

/-!
# The named challenges' positions

`linkCh` slices `θ_0 :: drawn` as `verify_link` does. For a draw of `linkDrawn` challenges, table
`t`'s `θ_t` is coordinate `t` (`chV_theta`), pointer column `j`'s `ε_j` coordinate `epsOff + j`
(`chV_eps`), the row coordinate `τ_k` coordinate `tauOff + k` (`chV_tau`), and chunk `i`'s `ν_i`
coordinate `nuOff + i` (`chV_nu`), all of `v : Fin (linkDrawn + 1) → E`, `θ_0 = v 0`.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link Finset

@[expose] public section

/-- The accesses over all tables. -/
def nAccessesOf (layout : Layout) : ℕ := (layout.tables.map (·.links.memory.length)).sum

/-- The pointer columns over all tables, `Q`. -/
def nPointersOf (layout : Layout) : ℕ := ((layout.tables.map (·.links.pointers)).map List.length).sum

/-- `ε`'s first coordinate in `θ_0 :: drawn`. -/
def epsOff (layout : Layout) : ℕ := nTables + 5 + nAccessesOf layout + bytecodeSlotBits + 2

/-- `τ`'s first coordinate in `θ_0 :: drawn`. -/
def tauOff (layout : Layout) : ℕ := epsOff layout + nPointersOf layout

/-- `ν`'s first coordinate in `θ_0 :: drawn`. -/
def nuOff (layout : Layout) (chunks : Chunks) : ℕ := tauOff layout + linkRows layout + chunks.width

theorem linkDrawn_eq (layout : Layout) (chunks : Chunks) (hch : Chunks.new chunks.width = some chunks) :
    linkDrawn layout chunks + 1 = nuOff layout chunks + chunks.d := by
  simp only [linkDrawn, packedChallenges, hch, Option.map_some, Option.getD_some, nuOff, tauOff,
    epsOff, nAccessesOf, nPointersOf, List.map_map, Function.comp_def]
  have : 1 ≤ nTables := by decide
  omega

theorem mu_fold_snd : ∀ (tables : List Table) (acc : List (List E) × List E),
    (tables.foldl (fun (acc : List (List E) × List E) t ↦
      (acc.1 ++ [acc.2.take t.links.memory.length], acc.2.drop t.links.memory.length)) acc).2 =
      acc.2.drop (tables.map (·.links.memory.length)).sum
  | [], acc => by simp
  | t :: ts, acc => by
    rw [List.foldl_cons, mu_fold_snd ts]
    simp [List.drop_drop]

theorem getD_ofFn_tail {N : ℕ} (v : Fin (N + 1) → E) {k : ℕ} (hk : k < N) :
    (List.ofFn v).tail.getD k 0 = v ⟨k + 1, by omega⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

theorem headD_ofFn {N : ℕ} (v : Fin (N + 1) → E) : (List.ofFn v).headD 0 = v 0 := by
  simp [List.ofFn_succ]

theorem nTables_le_nuOff (layout : Layout) (chunks : Chunks) : nTables ≤ nuOff layout chunks := by
  simp only [nuOff, tauOff, epsOff]; omega

section Positions

variable {layout : Layout} {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
  (v : Fin (linkDrawn layout chunks + 1) → E)
include hch

/-- The named challenges at a draw `v`. -/
abbrev chV (layout : Layout) (chunks : Chunks) (v : Fin (linkDrawn layout chunks + 1) → E) : LinkCh :=
  linkCh layout chunks ((List.ofFn v).headD 0) (List.ofFn v).tail

theorem chV_theta {t : ℕ} (ht : t < nTables) :
    (chV layout chunks v).theta.getD t 0 = v ⟨t, by
      have := linkDrawn_eq layout chunks hch; have := nTables_le_nuOff layout chunks; omega⟩ := by
  have hN := linkDrawn_eq layout chunks hch
  have hT1 : 1 ≤ nTables := by decide
  have hT := nTables_le_nuOff layout chunks
  rcases t with _ | t
  · simp [linkCh]
  · simp only [linkCh, List.getD_cons_succ]
    rw [List.getD_eq_getElem?_getD, List.getElem?_take]
    simp only [show t < nTables - 1 by omega, ↓reduceIte]
    rw [← List.getD_eq_getElem?_getD, getD_ofFn_tail v (by omega)]

theorem chV_eps {j : ℕ} (hj : j < nPointersOf layout) :
    (chV layout chunks v).eps.getD j 0 =
      v ⟨epsOff layout + j, by have := linkDrawn_eq layout chunks hch; simp only [nuOff, tauOff] at this; omega⟩ := by
  have hN := linkDrawn_eq layout chunks hch
  have hT1 : 1 ≤ nTables := by decide
  simp only [nuOff, tauOff] at hN
  simp only [linkCh, mu_fold_snd]
  rw [List.getD_eq_getElem?_getD]
  simp only [List.getElem?_take, List.getElem?_drop, show j < (List.map List.length
    (List.map (fun x ↦ x.links.pointers) layout.tables)).sum from hj, ↓reduceIte]
  rw [← List.getD_eq_getElem?_getD, getD_ofFn_tail v ?hk]
  · congr 1
    simp only [epsOff, nAccessesOf, Fin.mk.injEq]
    omega
  · simp only [epsOff, nAccessesOf, nPointersOf, List.map_map, Function.comp_def] at hN hj ⊢; omega

theorem chV_tau {k : ℕ} (hk : k < linkRows layout) :
    (chV layout chunks v).tau.getD k 0 =
      v ⟨tauOff layout + k, by have := linkDrawn_eq layout chunks hch; simp only [nuOff] at this; omega⟩ := by
  have hN := linkDrawn_eq layout chunks hch
  have hT1 : 1 ≤ nTables := by decide
  simp only [nuOff, tauOff] at hN
  simp only [linkCh, mu_fold_snd]
  rw [List.getD_eq_getElem?_getD]
  simp only [List.getElem?_take, List.getElem?_drop, show k < List.foldl max 0 layout.tableLogHeights
    from hk, ↓reduceIte]
  rw [← List.getD_eq_getElem?_getD, getD_ofFn_tail v ?hk]
  · congr 1
    simp only [tauOff, epsOff, nAccessesOf, nPointersOf, Fin.mk.injEq, List.map_map, Function.comp_def]
    omega
  · simp only [epsOff, nAccessesOf, nPointersOf, linkRows, List.map_map, Function.comp_def] at hN hk ⊢
    omega

theorem chV_tau_length : (chV layout chunks v).tau.length = linkRows layout := by
  have hN := linkDrawn_eq layout chunks hch
  have hT1 : 1 ≤ nTables := by decide
  simp only [nuOff, tauOff, epsOff, nAccessesOf, nPointersOf] at hN
  simp only [linkCh, mu_fold_snd, List.length_take, List.length_drop, List.length_tail, List.length_ofFn]
  simp only [linkRows, List.map_map, Function.comp_def] at hN ⊢
  omega

theorem chV_nu {i : ℕ} (hi : i < chunks.d) :
    (chV layout chunks v).nu.getD i 0 =
      v ⟨nuOff layout chunks + i, by have := linkDrawn_eq layout chunks hch; omega⟩ := by
  have hN := linkDrawn_eq layout chunks hch
  have hT1 : 1 ≤ nTables := by decide
  simp only [linkCh, mu_fold_snd]
  rw [List.getD_eq_getElem?_getD]
  simp only [List.getElem?_take, List.getElem?_drop, show i < chunks.d from hi, ↓reduceIte]
  rw [← List.getD_eq_getElem?_getD, getD_ofFn_tail v ?hk]
  · congr 1
    simp only [nuOff, tauOff, epsOff, nAccessesOf, nPointersOf, linkRows, Fin.mk.injEq, List.map_map,
      Function.comp_def]
    omega
  · simp only [nuOff, tauOff, epsOff, nAccessesOf, nPointersOf, linkRows, List.map_map,
      Function.comp_def] at hN ⊢
    omega

end Positions

end

end LeanVM.Protocol.Relation
