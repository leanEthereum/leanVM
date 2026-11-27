/-
  LeanVM.Guest.B1.Gkr.LayerTail

  The children of a GKR layer: the trees' children read and absorbed four a permutation, and a
  tree's new value at the two new coordinates.
-/

module

public import LeanVM.Guest.B1.Gkr.Layer
import LeanVM.Guest.B1.Tables.Basic
import LeanVM.Guest.StmtsAppend

/-!
# A layer's children (`gkr_children`)

* `chT`, `ch_ev`: a child's read; `ch_perm_block`: four children's permutation;
* `chValT`, `ch_val`: a tree's new value from its four children.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Children (`gkr_children`)

A layer reads every tree's children, tree by tree, with `fs_next` (`fsNextT`, the word then its
two rate cells) and keeps the word's copy; every four reads the sponge permutes. Child `i`'s
values start at `chB b0 i = b0 + 4i + 13⌊i/4⌋` (four values a read, a permutation's thirteen
outputs every four), its read at statement `4i + ⌊i/4⌋` of the block. -/

/-- The first value of child `i`'s read, the block's first at `b0`. -/
def chB (b0 i : ℕ) : ℕ := b0 + 4 * i + 13 * (i / 4)

/-- Child `i`'s read: `fs_next` at the cursor `cur`, `o + i` words on, its word copied. -/
def chT (cur : V) (o b0 i : ℕ) : List Stmt :=
  fsNextT cur (o + i) (chB b0 i) ⧺ [.atom (.copy (.n (chB b0 i + 3)) (.n (chB b0 i)))]

/-- The rate cells of children `4m .. 4m + 3`. -/
def chRate (b0 m : ℕ) : List V :=
  (List.range 4).flatMap fun i ↦ [.n (chB b0 (4 * m + i) + 1), .n (chB b0 (4 * m + i) + 2)]

/-- The words of the children `4m .. 4m + 3`. -/
def chWords (σ : Val) (b0 m : ℕ) : List E := (List.range 4).map fun i ↦ σ (.n (chB b0 (4 * m + i)))

theorem chWords_length (σ : Val) (b0 m : ℕ) : (chWords σ b0 m).length = 4 := by simp [chWords]

theorem chWords_eq (σ : Val) (b0 m : ℕ) : chWords σ b0 m = [σ (.n (chB b0 (4 * m))),
    σ (.n (chB b0 (4 * m + 1))), σ (.n (chB b0 (4 * m + 2))), σ (.n (chB b0 (4 * m + 3)))] := by
  simp [chWords, List.range_succ]

/-- Absorbing four scalars at a full queue: one permutation, then the four waiting. -/
theorem tb_absorbAll_full (s : Fs) (hs : s.pend.length = 4) (xs : List E) (hx : xs.length = 4)
    (t : ℕ) : s.absorbAll xs t = ⟨capOf s.perm, xs.map (·, t)⟩ := by
  match xs, hx with
  | x :: rest, hx =>
    simp only [Fs.absorbAll, List.foldl_cons]
    have h1 : s.absorb x t = ⟨capOf s.perm, [(x, t)]⟩ := by
      simp [Fs.absorb, hs, rateScalars]
    rw [h1]
    have := absorbAll_short ⟨capOf s.perm, [(x, t)]⟩ rest t (by simp at hx ⊢; omega)
    simp only [Fs.absorbAll] at this
    rw [this]
    simp

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- Child `i`'s read: its word at the cursor, packed, and copied. -/
theorem ch_ev {cur : V} {o b0 i : ℕ} (h : Stmt.HoldsList C rd σ (chT cur o b0 i) True kret) :
    LoadHolds rd (σ cur) (o + i) (σ (.n (chB b0 i))) ∧
      FsPackOk σ (.n (chB b0 i)) (chB b0 i + 1) dsObserve ∧
      σ (.n (chB b0 i + 3)) = σ (.n (chB b0 i)) := by
  unfold chT at h
  rw [tb_holdsList_append_noRet (by simp [fsNextT, fsPackT]; rfl), holds_fsNextT] at h
  obtain ⟨⟨⟨hl, hp⟩, -⟩, hc⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hc
  exact ⟨hl, hp, hc⟩

/-- The rate cells of packed words are their scalars' cells. -/
theorem ch_rate {ws : ℕ → ℕ} {n : ℕ}
    (hp : ∀ i < n, FsPackOk σ (.n (ws i)) (ws i + 1) dsObserve) :
    ((List.range n).flatMap fun i ↦ [V.n (ws i + 1), .n (ws i + 2)]).map σ =
      pendCells (((List.range n).map fun i ↦ σ (.n (ws i))).map (·, dsObserve)) := by
  have hcell : ∀ i < n, σ (.n (ws i + 1)) = (Keccak.scalarCells (σ (.n (ws i))) dsObserve).1 ∧
      σ (.n (ws i + 2)) = (Keccak.scalarCells (σ (.n (ws i))) dsObserve).2 :=
    fun i hi => Prod.ext_iff.mp (fsPackT_cells (hp i hi))
  simp only [pendCells, List.map_flatMap, List.flatMap_map, List.map_cons, List.map_nil]
  rw [List.flatMap_def, List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [(hcell i hi).1, (hcell i hi).2]

/-- **Four children's permutation**: their cells over the carried capacity. -/
theorem ch_perm_block {b0 m b : ℕ} {cap : List V}
    (hp : ∀ i < 4, FsPackOk σ (.n (chB b0 (4 * m + i))) (chB b0 (4 * m + i) + 1) dsObserve)
    (hk : (Atom.keccak (chRate b0 m ++ cap) (lyOuts b) false false).Holds rd σ) :
    (∀ k (hk : k < 13), σ (.n (b + k)) =
      cellsOfState (Fs.perm ⟨cap.map σ, (chWords σ b0 m).map (·, dsObserve)⟩) false ⟨k, hk⟩) ∧
      (lyCap b).map σ = capOf (Fs.perm ⟨cap.map σ, (chWords σ b0 m).map (·, dsObserve)⟩) := by
  obtain ⟨hP, hcap⟩ := ly_keccak hk
  have hins : (chRate b0 m ++ cap).map σ =
      rateOf ((chWords σ b0 m).map (·, dsObserve)) ++ cap.map σ := by
    rw [List.map_append, chRate, ch_rate (ws := fun i ↦ chB b0 (4 * m + i)) hp,
      rateOf_eq_cells _ (by simp [chWords_length])]
    simp [chWords]
  rw [hins] at hP hcap
  exact ⟨hP, hcap⟩

/-- Tree `t`'s new value at the two coordinates `c0`, `c1` (`lo + c₁·(lo + hi)`), its children's
reads from `b0`, its values from `b`, stored at `slot`'s `off`. -/
def chValT (b0 c0 c1 slot t b off : ℕ) : List Stmt :=
  let e := fun i ↦ chB b0 (4 * t + i) + 3
  [.atom (.add (.n b) (.n (e 0)) (.n (e 1))), .atom (.mul (.n (b + 1)) (.n c0) (.n b)),
    .atom (.add (.n (b + 2)) (.n (e 0)) (.n (b + 1))),
    .atom (.add (.n (b + 3)) (.n (e 2)) (.n (e 3))), .atom (.mul (.n (b + 4)) (.n c0) (.n (b + 3))),
    .atom (.add (.n (b + 5)) (.n (e 2)) (.n (b + 4))),
    .atom (.add (.n (b + 6)) (.n (b + 2)) (.n (b + 5))), .atom (.mul (.n (b + 7)) (.n c1) (.n (b + 6))),
    .atom (.add (.n (b + 8)) (.n (b + 2)) (.n (b + 7))), .atom (.load (.n (b + 8)) (.n slot) off)]

/-- A tree's new value: its four children's multilinear value at the two new coordinates. -/
theorem ch_val {b0 c0 c1 slot t b off : ℕ}
    (h : Stmt.HoldsList C rd σ (chValT b0 c0 c1 slot t b off) True kret) :
    σ (.n (b + 8)) = multilinearEval [σ (.n (chB b0 (4 * t + 0) + 3)),
      σ (.n (chB b0 (4 * t + 1) + 3)), σ (.n (chB b0 (4 * t + 2) + 3)),
      σ (.n (chB b0 (4 * t + 3) + 3))] [σ (.n c0), σ (.n c1)] ∧
      LoadHolds rd (σ (.n slot)) off (σ (.n (b + 8))) := by
  simp only [chValT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, l⟩ := h
  refine ⟨?_, l⟩
  rw [e8, e7, e6, e5, e4, e3, e2, e1, e0]
  simp only [multilinearEval, List.foldl, foldPairs, List.headD]
  ring

end Sem

end
end LeanVM.Guest.B1.Tables
