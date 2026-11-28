/-
  LeanVM.Guest.B1.Link.Squeeze

  `squeeze_cells`' expansion: permutations of the capacity alone, their rate cells stored.
-/

module

public import LeanVM.Guest.B1.Link.Packed
public import LeanVM.Guest.B1.Link.RoundSound
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Atoms

/-!
# `squeeze_cells`

`squeeze_cells(rec, cells, n)` (G, inlined into `squeeze_packed`'s loop and
`squeeze_packed_last`) permutes the capacity alone `n` times, each output's eight rate cells
stored at `cells[8 j ..]`. `spPermsT o cap z cells off n`: its permutations' outputs from the value
`o` (thirteen a permutation), on the capacity values `cap`, the zero run from `z`, the cells stored
from offset `off`. `spPerms_sound`: the stored cells are `pkSqueeze n`'s and the last capacity its.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The capacity values before permutation `j`. -/
def spCap (o : ℕ) (cap : List ℕ) (j : ℕ) : List ℕ :=
  if j = 0 then cap else (List.range 5).map fun i ↦ o + 13 * (j - 1) + 8 + i

/-- Permutation `j` and its eight cells stored. -/
def spBlk (o : ℕ) (cap : List ℕ) (z cells off j : ℕ) : List Stmt :=
  .atom (.keccak ([.n z, .n z, .n z, .n z, .n z, .n (z + 1), .n (z + 2), .n (z + 3)] ++
      (spCap o cap j).map V.n) ((List.range 13).map fun i ↦ .n (o + 13 * j + i)) false false) ::
    (List.range 8).map fun i ↦ .atom (.load (.n (o + 13 * j + i)) (.n cells) (off + 8 * j + i))

/-- `n` permutations of the capacity alone. -/
def spPermsT (o : ℕ) (cap : List ℕ) (z cells off n : ℕ) : List Stmt :=
  ((List.range n).map (spBlk o cap z cells off)).flatten

theorem spPermsT_atoms (o : ℕ) (cap : List ℕ) (z cells off n : ℕ) : AllAtoms (spPermsT o cap z cells off n) :=
  allAtoms_map_flatten fun j _ ↦ allAtoms_cons fun s hs ↦ by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hs; exact ⟨_, rfl⟩

theorem pkSqueeze_succ' : ∀ (j : ℕ) (cap : List E), pkSqueeze (j + 1) cap =
    ((pkSqueeze j cap).1 ++ (List.range 8).map (cellAt (pkPerm (pkSqueeze j cap).2)),
      capOf (pkPerm (pkSqueeze j cap).2))
  | 0, cap => by simp [pkSqueeze]
  | j + 1, cap => by
    rw [pkSqueeze, pkSqueeze_succ' j (capOf (pkPerm cap))]
    simp [pkSqueeze]

/-- **`n` permutations of the capacity alone**: the cells stored are `pkSqueeze n`'s, and the last
capacity values its. -/
theorem spPerms_sound {rd : Reader} {σ : Val} {o : ℕ} {cap : List ℕ} {z cells off n : ℕ}
    (hz : ∀ i < 4, σ (.n (z + i)) = 0)
    (hA : ∀ a, Stmt.atom a ∈ spPermsT o cap z cells off n → a.Holds rd σ) :
    (∀ i < 8 * n, LoadHolds rd (σ (.n cells)) (off + i) ((pkSqueeze n (cap.map (σ ∘ .n))).1.getD i 0)) ∧
      (spCap o cap n).map (σ ∘ .n) = (pkSqueeze n (cap.map (σ ∘ .n))).2 := by
  induction n with
  | zero => exact ⟨fun i hi ↦ absurd hi (by omega), by simp [spCap, pkSqueeze]⟩
  | succ n ih =>
    have hA' : ∀ a, Stmt.atom a ∈ spPermsT o cap z cells off n → a.Holds rd σ := fun a ha ↦ hA a (by
      unfold spPermsT at ha ⊢
      rw [List.range_succ, List.map_append, List.flatten_append]
      exact List.mem_append_left _ ha)
    obtain ⟨ihc, ihk⟩ := ih hA'
    have hB : ∀ a, Stmt.atom a ∈ spBlk o cap z cells off n → a.Holds rd σ := fun a ha ↦ hA a (by
      unfold spPermsT
      rw [List.range_succ, List.map_append, List.flatten_append]
      exact List.mem_append_right _ (by simpa using ha))
    have hk := hB _ (List.mem_cons_self)
    have hc := keccakA_fs (s := ⟨(spCap o cap n).map (σ ∘ .n), []⟩) hk (by simp) (by
      simp only [List.map_append, List.map_cons, List.map_nil, List.map_map]
      have z0 := hz 0 (by norm_num)
      rw [Nat.add_zero] at z0
      rw [z0, hz 1 (by norm_num), hz 2 (by norm_num), hz 3 (by norm_num)]
      simp [pendCells])
    have ho := outs_cells_of hc
    set S := pkSqueeze n (cap.map (σ ∘ .n))
    have hperm : Fs.perm ⟨(spCap o cap n).map (σ ∘ .n), []⟩ = pkPerm S.2 := by
      rw [ihk, Fs.perm, rateOf_eq_cells [] (by simp)]
      rfl
    rw [hperm] at ho
    refine ⟨fun i hi ↦ ?_, ?_⟩
    · rw [pkSqueeze_succ']
      rcases Nat.lt_or_ge i (8 * n) with h | h
      · rw [List.getD_append _ _ _ _ (by rw [pkSqueeze_length]; exact h)]
        exact ihc i h
      · rw [List.getD_append_right _ _ _ _ (by rw [pkSqueeze_length]; exact h), pkSqueeze_length]
        have hi8 : i - 8 * n < 8 := by omega
        have hs := hB (.load (.n (o + 13 * n + (i - 8 * n))) (.n cells) (off + 8 * n + (i - 8 * n)))
          (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i - 8 * n, List.mem_range.mpr hi8, rfl⟩))
        simp only [Atom.Holds] at hs
        rw [show off + 8 * n + (i - 8 * n) = off + i by omega, ho (i - 8 * n) (by omega)] at hs
        simpa [List.getD_eq_getElem?_getD, hi8, cellAt, show i - 8 * n < 13 by omega] using hs
    · rw [pkSqueeze_succ']
      rw [capOf_outs ho]
      simp only [spCap, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, List.map_map]
      rfl

end
end LeanVM.Guest.B1.Link
