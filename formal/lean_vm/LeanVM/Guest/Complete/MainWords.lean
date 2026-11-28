/-
  LeanVM.Guest.Complete.MainWords

  `main`'s honest words tile its buffers, and a memory holding exactly some disjoint runs.
-/

module

public import LeanVM.Guest.Complete.MainDup
public import LeanVM.Guest.Complete.Compose
import LeanVM.Guest.Memory.LowDef
import LeanVM.Guest.B2C.Table
public import LeanVM.Parameters.Generator

/-!
# `main`'s words

* **A memory holding runs.** `rdW W`: the reader holding the pairwise disjoint runs `W` and nothing
  else; `holdsWords_rdW`. `InW W i`: some run holds index `i`; `isSome_of_inW`: a memory holding `W`
  defines the word at `i`.
* **Runs from a base.** `(bases b (L.map length)).zip L`: the lists `L` one after another from `b`, within
  `[b, b + Σ)` (`bases_zip_in`), pairwise disjoint (`bases_zip_pairwise`), covering it (`bases_zip_cover`).
* **`main`'s words.** `mainLists s w cover`: its buffers' honest contents in allocation order;
  `mainLists_length`: their lengths are `MainCounts.bufs` given the coverage table's length and the
  claims' cells (`55` per fresh claim, `26` per deferred one); then `mainWords_eq` (`mainWords` is the
  zip), `mainWords_in` (within `[B2C.fs "main", mTop)`, disjoint), `mainWords_cover` (every index there
  is defined on a memory holding them), and `fs_main_lt` (`B2C.fs "main" < 2^17`, by the kernel).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## A memory holding runs -/

/-- Runs pairwise disjoint. -/
def Disj (W : Words) : Prop := W.Pairwise fun q q' => q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1

/-- Some run of `W` holds index `i`. -/
def InW (W : Words) (i : ℕ) : Prop := ∃ q ∈ W, q.1 ≤ i ∧ i < q.1 + q.2.length

/-- The word of the first run of `W` holding index `i`. -/
def valAt : Words → ℕ → E
  | [], _ => 0
  | q :: W, i => if q.1 ≤ i ∧ i < q.1 + q.2.length then q.2.getD (i - q.1) 0 else valAt W i

open Classical in
/-- **The reader holding the runs `W`**, and nothing else. -/
noncomputable def rdW (W : Words) : Reader := fun A =>
  if h : ∃ i, i < 2 ^ 64 - 1 ∧ A = addressOfIndex i ∧ InW W i then some (valAt W (Classical.choose h)) else none

theorem valAt_of_mem : ∀ {W : Words}, Disj W → ∀ {q : ℕ × List E}, q ∈ W → ∀ {i : ℕ}, q.1 ≤ i →
    i < q.1 + q.2.length → valAt W i = q.2.getD (i - q.1) 0
  | [], _, _, hq, _, _, _ => by simp at hq
  | q' :: W, hp, q, hq, i, h1, h2 => by
    rw [Disj, List.pairwise_cons] at hp
    rcases List.mem_cons.mp hq with rfl | hq
    · simp [valAt, h1, h2]
    · have hd := hp.1 q hq
      have hn : ¬ (q'.1 ≤ i ∧ i < q'.1 + q'.2.length) := by omega
      rw [valAt]
      simp only [hn, ↓reduceIte]
      exact valAt_of_mem hp.2 hq h1 h2

/-- **`rdW W` holds `W`**, the runs disjoint and below the generator's order. -/
theorem holdsWords_rdW {W : Words} (hp : Disj W) (hb : ∀ q ∈ W, q.1 + q.2.length < 2 ^ 64 - 1) :
    HoldsWords (rdW W) W := by
  intro q hq k hk
  have hqb := hb q hq
  refine ⟨Value.ofK_isInK _, ?_⟩
  rw [Main.addr_ofK]
  have hex : ∃ i, i < 2 ^ 64 - 1 ∧ addressOfIndex (q.1 + k) = addressOfIndex i ∧ InW W i :=
    ⟨q.1 + k, by omega, rfl, q, hq, by omega, by omega⟩
  unfold rdW
  split
  · rename_i hex'
    obtain ⟨hlt, he, -⟩ := Classical.choose_spec hex'
    have e : q.1 + k = Classical.choose hex' :=
      gpow_injOn (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr hlt) he
    rw [← e, valAt_of_mem hp hq (by omega) (by omega), Nat.add_sub_cancel_left]
    simp [hk]
  · exact absurd hex ‹_›

/-- **A memory holding `W` defines every index a run holds.** -/
theorem isSome_of_inW {rd : Reader} {W : Words} (h : HoldsWords rd W) {i : ℕ} (hi : InW W i) :
    (rd (addressOfIndex i)).isSome := by
  obtain ⟨q, hq, h1, h2⟩ := hi
  have := (h q hq (i - q.1) (by omega)).2
  rw [Main.addr_ofK, show q.1 + (i - q.1) = i by omega] at this
  rw [this]; rfl

theorem inW_append_left {W W' : Words} {i : ℕ} (h : InW W i) : InW (W ++ W') i := by
  obtain ⟨q, hq, h⟩ := h
  exact ⟨q, List.mem_append_left _ hq, h⟩

/-! ## Runs from a base -/

theorem bases_zip_in : ∀ (b : ℕ) (L : List (List E)), ∀ q ∈ (bases b (L.map List.length)).zip L,
    b ≤ q.1 ∧ q.1 + q.2.length ≤ b + (L.map List.length).sum
  | _, [] => by simp [bases]
  | b, x :: L => by
    intro q hq
    simp only [List.map_cons, bases, List.zip_cons_cons, List.mem_cons] at hq
    simp only [List.map_cons, List.sum_cons]
    rcases hq with rfl | hq
    · exact ⟨le_rfl, by simp⟩
    · have := bases_zip_in (b + x.length) L q hq
      omega

theorem bases_zip_pairwise : ∀ (b : ℕ) (L : List (List E)), Disj ((bases b (L.map List.length)).zip L)
  | _, [] => by simp [bases, Disj]
  | b, x :: L => by
    simp only [Disj, List.map_cons, bases, List.zip_cons_cons, List.pairwise_cons]
    exact ⟨fun q hq => Or.inl (bases_zip_in (b + x.length) L q hq).1, bases_zip_pairwise _ L⟩

theorem bases_zip_cover : ∀ (b : ℕ) (L : List (List E)) (i : ℕ), b ≤ i → i < b + (L.map List.length).sum →
    InW ((bases b (L.map List.length)).zip L) i
  | _, [], i, h1, h2 => by simp at h2; omega
  | b, x :: L, i, h1, h2 => by
    simp only [List.map_cons, List.sum_cons] at h2
    by_cases hi : i < b + x.length
    · exact ⟨(b, x), by simp [bases], h1, hi⟩
    · obtain ⟨q, hq, h⟩ := bases_zip_cover (b + x.length) L i (by omega) (by omega)
      refine ⟨q, ?_, h⟩
      simp only [List.map_cons, bases, List.zip_cons_cons]
      exact List.mem_cons_of_mem _ hq

/-! ## `main`'s words -/

/-- **`main`'s buffers' honest contents**, in allocation order (`mainWords`'). -/
noncomputable def mainLists (s : NodeStatement) (w : NodeWitness) (cover : List E) : List (List E) :=
  [(s.claims.xmss ++ (xPlan s w).duplicates).flatMap xCells,
    (s.claims.sphincs ++ (sPlan s w).duplicates).flatMap sCells,
    cover,
    (List.range 256).map fun v => word v 0,
    w.children.flatMap (fun ch => Prover.digestCells ch.statement.claims.daDigest) ++ ownDaCells w,
    w.children.flatMap fun ch => Prover.digestCells (statementDigest guestSeed ch.statement),
    w.children.flatMap (·.freshClaim.cells),
    w.children.flatMap (·.statement.deferredClaim.cells),
    (List.range ((mainCounts s w).nc + 1)).map fun c => gen ^ kidBase w c,
    s.deferredClaim.cells]

theorem flatMap_length_const {α : Type} {l : List α} {f : α → List E} {n : ℕ} (h : ∀ a ∈ l, (f a).length = n) :
    (l.flatMap f).length = n * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb), List.length_cons]
    ring

theorem ownDaCells_length (w : NodeWitness) : (ownDaCells w).length = 2 := by
  unfold ownDaCells
  split <;> simp [Prover.digestCells]

theorem xFlat_length (l : List LeanXmssClaim) : (l.flatMap xCells).length = 4 * l.length :=
  flatMap_length_const fun c _ => xCells_length c

theorem sFlat_length (l : List LeanSphincsClaim) : (l.flatMap sCells).length = 4 * l.length :=
  flatMap_length_const fun c _ => sCells_length c

theorem dFlat_length {α : Type} (l : List α) (f : α → Digest) :
    (l.flatMap fun a => Prover.digestCells (f a)).length = 2 * l.length :=
  flatMap_length_const fun _ _ => by simp [Prover.digestCells]

/-- **The buffers' lengths are `main`'s `HeapBuf` sizes**, given the coverage table's length and the
claims' cells. -/
theorem mainLists_length {s : NodeStatement} {w : NodeWitness} {cover : List E}
    (hc : cover.length = (mainCounts s w).sx + (mainCounts s w).ss)
    (hf : ∀ ch ∈ w.children, ch.freshClaim.cells.length = 55)
    (hd : ∀ ch ∈ w.children, ch.statement.deferredClaim.cells.length = 26)
    (hs : s.deferredClaim.cells.length = 26) :
    (mainLists s w cover).map List.length = (mainCounts s w).bufs := by
  have e0 : ((s.claims.xmss ++ (xPlan s w).duplicates).flatMap xCells).length = 4 * (mainCounts s w).sx := by
    rw [xFlat_length, List.length_append]; rfl
  have e1 : ((s.claims.sphincs ++ (sPlan s w).duplicates).flatMap sCells).length = 4 * (mainCounts s w).ss := by
    rw [sFlat_length, List.length_append]; rfl
  have e3 : ((List.range 256).map fun v => word v 0).length = 256 := by simp
  have e4 : (w.children.flatMap (fun ch => Prover.digestCells ch.statement.claims.daDigest) ++ ownDaCells w).length =
      2 * ((mainCounts s w).nc + 1) := by
    rw [List.length_append, dFlat_length, ownDaCells_length]
    show 2 * w.children.length + 2 = 2 * (w.children.length + 1)
    ring
  have e5 : (w.children.flatMap fun ch => Prover.digestCells (statementDigest guestSeed ch.statement)).length =
      2 * (mainCounts s w).nc := dFlat_length _ _
  have e6 : (w.children.flatMap (·.freshClaim.cells)).length = 55 * (mainCounts s w).nc := flatMap_length_const hf
  have e7 : (w.children.flatMap (·.statement.deferredClaim.cells)).length = 26 * (mainCounts s w).nc :=
    flatMap_length_const hd
  have e8 : ((List.range ((mainCounts s w).nc + 1)).map fun c => gen ^ kidBase w c).length =
      (mainCounts s w).nc + 1 := by simp
  simp only [mainLists, List.map_cons, List.map_nil, e0, e1, hc, e3, e4, e5, e6, e7, e8, hs]
  rfl

/-- **`mainWords` is its lists from `main`'s frame's end**, one after another. -/
theorem mainWords_eq {s : NodeStatement} {w : NodeWitness} {cover : List E}
    (hl : (mainLists s w cover).map List.length = (mainCounts s w).bufs) :
    mainWords s w cover = (bases (B2C.fs "main") (mainCounts s w).bufs).zip (mainLists s w cover) := by
  simp only [mainWords, mBase]
  rw [← hl]
  simp [mainLists, bases]

/-- **`main`'s words lie in its buffers**, pairwise disjoint. -/
theorem mainWords_in {s : NodeStatement} {w : NodeWitness} {cover : List E}
    (hl : (mainLists s w cover).map List.length = (mainCounts s w).bufs) :
    (∀ q ∈ mainWords s w cover, B2C.fs "main" ≤ q.1 ∧ q.1 + q.2.length ≤ mTop (mainCounts s w)) ∧
      Disj (mainWords s w cover) := by
  rw [mainWords_eq hl, mTop, ← hl]
  exact ⟨bases_zip_in _ _, bases_zip_pairwise _ _⟩

/-- **Every index of `main`'s buffers is defined** on a memory holding its words. -/
theorem mainWords_cover {s : NodeStatement} {w : NodeWitness} {cover : List E}
    (hl : (mainLists s w cover).map List.length = (mainCounts s w).bufs) {i : ℕ}
    (h1 : B2C.fs "main" ≤ i) (h2 : i < mTop (mainCounts s w)) : InW (mainWords s w cover) i := by
  rw [mainWords_eq hl]
  rw [mTop, ← hl] at h2
  rw [← hl]
  exact bases_zip_cover _ _ i h1 h2

/-- **`main`'s frame is below `2^17`**, by the kernel. -/
theorem fs_main_lt : B2C.fs "main" < 2 ^ 17 := by
  rw [B2C.fs_main]; unfold B2C.mainFrame; decide +kernel

end
end LeanVM.Guest.Complete
