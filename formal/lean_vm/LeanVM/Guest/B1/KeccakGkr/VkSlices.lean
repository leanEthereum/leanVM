/-
  LeanVM.Guest.B1.KeccakGkr.VkSlices

  `verify_keccak`'s 64 slices (G:3060-3069): read at the cursor, stored, absorbed four to a
  permutation, then the ring map's first challenge squeezed.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkT

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

theorem absorbAll_append (s : Fs) (xs ys : List E) (t : ℕ) :
    s.absorbAll (xs ++ ys) t = (s.absorbAll xs t).absorbAll ys t := by
  simp [Fs.absorbAll, List.foldl_append]

/-- The cells of group `g`'s four reads. -/
def slGroup (b g : ℕ) : List (V × V) :=
  (List.range 4).map fun j ↦ (.n (slB b (4 * g + j) + 1), .n (slB b (4 * g + j) + 2))

theorem slGroup_cells (b g : ℕ) : pendCellsV (slGroup b g) = slCells b g := by
  simp [pendCellsV, slGroup, slCells, List.range_succ]

/-- The words of group `g`. -/
def slWords (σ : Val) (b g : ℕ) : List E := (List.range 4).map fun j ↦ σ (.n (slB b (4 * g + j)))

/-- Four reads onto an empty queue. -/
theorem group_absorb {cap : List E} {capV : List V} (hc : cap = capV.map σ) {b g : ℕ}
    (hp : ∀ j < 4, FsPackOk σ (.n (slB b (4 * g + j))) (slB b (4 * g + j) + 1) dsObserve) :
    SpOk σ ((⟨cap, []⟩ : Fs).absorbAll (slWords σ b g) dsObserve) (capV, slGroup b g) := by
  rw [absorbAll_short _ _ _ (by simp [slWords])]
  refine ⟨hc, ?_⟩
  simp only [slWords, slGroup, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, PendOk]
  exact ⟨fsPackT_cells (hp 0 (by omega)), fsPackT_cells (hp 1 (by omega)),
    fsPackT_cells (hp 2 (by omega)), fsPackT_cells (hp 3 (by omega)), trivial⟩

theorem absorbAll_full {s : Fs} (h : s.pend.length = 4) (x : E) (xs : List E) (t : ℕ) :
    s.absorbAll (x :: xs) t = (⟨capOf s.perm, []⟩ : Fs).absorbAll (x :: xs) t := by
  simp only [Fs.absorbAll, List.foldl_cons]
  congr 1
  simp [Fs.absorb, h, rateScalars]

theorem slWords_cons (σ : Val) (b g : ℕ) :
    slWords σ b g = σ (.n (slB b (4 * g))) :: (List.range 3).map fun j ↦ σ (.n (slB b (4 * g + 1 + j))) := by
  simp [slWords, List.range_succ, Nat.add_assoc]

theorem range_map_take (f : ℕ → E) (g : ℕ) :
    (List.range (4 * (g + 1))).map f = (List.range (4 * g)).map f ++
      (List.range 4).map fun j ↦ f (4 * g + j) := by
  rw [show 4 * (g + 1) = 4 * g + 4 by ring, List.range_add, List.map_append, List.map_map]
  rfl

/-- **The slices** (G:3060-3069). -/
theorem slicesT_holds {cur : V} {capb b : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (slicesT cur capb b) next kret) :
    ReadsAt rd (σ cur) ((List.range 64).map fun z ↦ σ (.n (slB b z))) ∧
      (∀ z < 64, LoadHolds rd (σ (.n 10)) z (σ (.n (slB b z)))) ∧
      ((⟨(cap5 capb).map σ, []⟩ : Fs).absorbAll ((List.range 64).map fun z ↦ σ (.n (slB b z)))
        dsObserve).pend.length = rateScalars ∧
      capOf ((⟨(cap5 capb).map σ, []⟩ : Fs).absorbAll ((List.range 64).map fun z ↦ σ (.n (slB b z)))
        dsObserve).perm = (cap5 (slP b 16 + 8)).map σ ∧ next := by
  rw [slicesT, holdsList_append, holdsList_range_flatten _ _ (fun g ↦ by
    rw [noRetList_append, noRetList_flatten_map _ (fun j ↦ rfl)]; split <;> rfl)] at h
  obtain ⟨hg, hfin⟩ := h
  simp only [keccakA, Stmt.HoldsList, Stmt.Holds] at hfin
  obtain ⟨hkf, hn⟩ := hfin
  -- each group
  have G : ∀ g < 16, (g ≠ 0 → (Atom.keccak (slCells b (g - 1) ++ cap5 (slCap capb b (g - 1)))
        ((List.range 13).map fun k ↦ .n (slP b g + k)) false false).Holds rd σ) ∧
      ∀ j < 4, (LoadHolds rd (σ cur) (4 * g + j) (σ (.n (slB b (4 * g + j)))) ∧
        FsPackOk σ (.n (slB b (4 * g + j))) (slB b (4 * g + j) + 1) dsObserve) ∧
        LoadHolds rd (σ (.n 10)) (4 * g + j) (σ (.n (slB b (4 * g + j)))) := by
    intro g hg16
    have hgg := hg g hg16
    rw [holdsList_append, holdsList_range_flatten _ _ (fun j ↦ rfl)] at hgg
    refine ⟨fun hg0 ↦ ?_, fun j hj ↦ ?_⟩
    · simp only [hg0, ↓reduceIte, keccakA, Stmt.HoldsList, Stmt.Holds] at hgg
      exact hgg.1
    · have hr : Stmt.HoldsList C rd σ (fsNextT cur (4 * g + j) (slB b (4 * g + j)) ++
          [.atom (.load (.n (slB b (4 * g + j))) (.n 10) (4 * g + j))]) True kret := by
        split at hgg
        · exact hgg.1 j hj
        · simp only [Stmt.HoldsList] at hgg
          exact hgg.2.1 j hj
      rw [holdsList_append, holds_fsNextT] at hr
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hr
      exact ⟨hr.1, hr.2⟩
  set f : ℕ → E := fun z ↦ σ (.n (slB b z)) with hf
  have hw : ∀ g, slWords σ b g = (List.range 4).map fun j ↦ f (4 * g + j) := fun g ↦ rfl
  -- the invariant
  have inv : ∀ g < 16, SpOk σ ((⟨(cap5 capb).map σ, []⟩ : Fs).absorbAll
      ((List.range (4 * (g + 1))).map f) dsObserve) (cap5 (slCap capb b g), slGroup b g) := by
    intro g
    induction g with
    | zero =>
      intro _
      have := group_absorb (b := b) (g := 0) (rfl : (cap5 capb).map σ = (cap5 capb).map σ)
        (fun j hj ↦ ((G 0 (by omega)).2 j hj).1.2)
      simpa [slCap, slWords, hf] using this
    | succ g ih =>
      intro hg1
      have hs := ih (by omega)
      have hlen : ((⟨(cap5 capb).map σ, []⟩ : Fs).absorbAll ((List.range (4 * (g + 1))).map f)
          dsObserve).pend.length = 4 := by
        rw [pendOk_length hs.2]; simp [slGroup]
      obtain ⟨hperm, hout⟩ := spOk_perm hs ((G (g + 1) hg1).1 (by omega)) (zs := [])
        (by simp [slGroup_cells]) (by simp [slGroup]) (by simp [slGroup])
      rw [range_map_take, absorbAll_append, ← hw, slWords_cons, absorbAll_full hlen, ← slWords_cons]
      have hcap : capOf ((⟨(cap5 capb).map σ, []⟩ : Fs).absorbAll ((List.range (4 * (g + 1))).map f)
          dsObserve).perm = (cap5 (slCap capb b (g + 1))).map σ := by
        rw [capOf_outs hout]
        simp [capOuts, cap5, slCap, List.range_succ, Nat.add_assoc]
      rw [hcap]
      exact group_absorb rfl (fun j hj ↦ ((G (g + 1) hg1).2 j hj).1.2)
  have hz : ∀ z < 64, (LoadHolds rd (σ cur) z (f z) ∧ FsPackOk σ (.n (slB b z)) (slB b z + 1)
      dsObserve) ∧ LoadHolds rd (σ (.n 10)) z (f z) := by
    intro z hz
    have := (G (z / 4) (by omega)).2 (z % 4) (Nat.mod_lt _ (by norm_num))
    rwa [Nat.div_add_mod] at this
  have hs := inv 15 (by omega)
  simp only [show 4 * (15 + 1) = 64 from rfl] at hs
  generalize (⟨(cap5 capb).map σ, []⟩ : Fs).absorbAll (List.map f (List.range 64)) dsObserve = S
    at hs ⊢
  obtain ⟨hperm, hout⟩ := spOk_perm hs hkf (zs := []) (by simp [slGroup_cells, slCap])
    (by simp [slGroup]) (by simp [slGroup])
  refine ⟨fun z hz' ↦ ?_, fun z hz' ↦ (hz z (by simpa using hz')).2, ?_, ?_, hn⟩
  · simp only [List.length_map, List.length_range] at hz'
    simpa using (hz z hz').1.1
  · exact (pendOk_length hs.2).trans rfl
  · rw [capOf_outs hout]
    simp [capOuts, cap5, List.range_succ, Nat.add_assoc]

end
end LeanVM.Guest.B1.VerifySub
