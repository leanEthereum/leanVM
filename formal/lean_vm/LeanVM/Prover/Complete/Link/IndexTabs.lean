/-
  LeanVM.Prover.Complete.Link.IndexTabs

  The index side's tables all have `2^width` entries.
-/

module

public import LeanVM.Prover.Complete.Link.Skeleton
public import LeanVM.Prover.Complete.Keccak.Exec.Mle

/-!
# The index side's shape

The challenges split from a packed draw of `packedChallenges` values have a `ζ` of `width`
coordinates (`length_zeta`); every array of the index side (`indexArrays`) has `2^width` entries:
the scattered arrays (`scatterWords` keeps the size), the memory's and the program's tables, and
`eq(ζ, ·)`. `indexTabs`: `LinkFacts.indexTabs`.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Protocol.Verifier.Defers

/-- The draw after the accesses' `μ`: the fold drops their count. -/
theorem muFold_snd : ∀ (ts : List Table) (l0 : List (List E)) (d0 : List E),
    (ts.foldl (fun (acc : List (List E) × List E) t ↦
      (acc.1 ++ [acc.2.take t.links.memory.length], acc.2.drop t.links.memory.length)) (l0, d0)).2 =
      d0.drop (ts.map (·.links.memory.length)).sum
  | [], _, d0 => by simp
  | t :: ts, l0, d0 => by
    rw [List.foldl_cons, muFold_snd ts, List.drop_drop, List.map_cons, List.sum_cons]

theorem length_zeta (tables' : List Table) (htab : tables' = tables) (nRows width d : ℕ)
    (theta0 : E) (drawn : List E) (hlen : drawn.length = packedChallenges tables nRows width) :
    (LinkChallenges.ofDraw tables' nRows width d theta0 drawn).zeta.length = width := by
  subst htab
  have h1 : (tables.map (·.links.memory.length)).sum = 39 := by decide
  have h2 : (tables.map (·.links.pointers.length)).sum = 33 := by decide
  unfold packedChallenges at hlen
  rw [h1, h2] at hlen
  unfold LinkChallenges.ofDraw
  simp only [muFold_snd, h1, h2, List.length_take, List.length_drop, hlen, bytecodeSlotBits,
    nTables]
  omega

theorem size_scatterWords (chunks : Chunks) (words : Array K) (rows shift : ℕ) (weight : ℕ → E)
    (a : Array E) : (scatterWords chunks words rows shift weight a).size = a.size := by
  unfold scatterWords
  induction rows with
  | zero => simp
  | succ n ih =>
    rw [Nat.fold_succ]
    dsimp only
    split
    · exact ih
    · rw [← ih]
      generalize (Nat.fold n _ a) = b
      suffices h : ∀ (js : List ℕ) (b : Array E), (js.foldl (fun a j ↦
          match chunks.shifted j shift with
          | some j => a.modify j (· + weight n)
          | none => a) b).size = b.size from h _ b
      intro js
      induction js with
      | nil => intro b; rfl
      | cons j js ihj =>
        intro b
        rw [List.foldl_cons, ihj]
        split <;> simp

/-- The index side's scattered arrays keep the size they start with. -/
theorem size_scattered (W : Witness) (ch : LinkChallenges) :
    ∀ (L : List ℕ) (acc : Vector (Array E) 6), (∀ i : Fin 6, acc[i].size = 2 ^ W.chunks.width) →
      ∀ i : Fin 6, (L.foldl (fun (acc : Vector (Array E) 6) t ↦
        let table := tables.getD t default
        let links := table.links
        let cols := W.tableCols t
        let n := W.rows.getD t 0
        let omega := omegaTable (ch.theta.getD t 0) ch.tau (W.layout.tableLogHeights.getD t 0) n
        let mu := ch.mu.getD t []
        let state := links.stateLink
        let cyc := cols.getD state.cycle #[]
        let bcw := cols.getD links.bytecodeLink.pointer #[]
        let states := scatterWords W.chunks cyc n 0
          (fun u ↦ (stateValues ch links (rowValue cols u)).1) acc[0]
        let nexts := scatterWords W.chunks cyc n 0
          (fun u ↦ (stateValues ch links (rowValue cols u)).2) acc[1]
        let wMem := (links.memory.zip mu).foldl (fun a (access, m) ↦
          scatterWords W.chunks (cols.getD access.pointer #[]) n access.shift (fun u ↦
            let w := m * omega.getD u 0
            match access.gate with
            | some g => w * rowValue cols u g
            | none => w) a) acc[2]
        let vWord := (wordReads links mu (ch.gammaMem.getD 1 0)).foldl (fun a (p, scale) ↦
          scatterWords W.chunks (cols.getD p #[]) n 0
            (fun u ↦ scale.evaluate (rowValue cols u) * omega.getD u 0) a) acc[3]
        let wBc := scatterWords W.chunks bcw n 0 (fun u ↦ omega.getD u 0) acc[4]
        let wFp := scatterWords W.chunks bcw n 0
          (fun u ↦ omega.getD u 0 * rowValue cols u state.fp) acc[5]
        #v[states, nexts, wMem, vWord, wBc, wFp]) acc)[i].size = 2 ^ W.chunks.width := by
  intro L
  induction L with
  | nil => intro acc h i; exact h i
  | cons t L ih =>
    intro acc h
    refine ih _ fun i ↦ ?_
    have hfold : ∀ {γ : Type} (l : List γ) (f : γ → Array E → Array E) (a : Array E),
        (∀ x b, (f x b).size = b.size) → (l.foldl (fun a x ↦ f x a) a).size = a.size := by
      intro γ l f a hf
      induction l generalizing a with
      | nil => rfl
      | cons x l ihl => rw [List.foldl_cons, ihl, hf]
    fin_cases i
    · exact (size_scatterWords _ _ _ _ _ _).trans (h 0)
    · exact (size_scatterWords _ _ _ _ _ _).trans (h 1)
    · exact (hfold _ _ _ fun _ _ ↦ size_scatterWords _ _ _ _ _ _).trans (h 2)
    · exact (hfold _ _ _ fun _ _ ↦ size_scatterWords _ _ _ _ _ _).trans (h 3)
    · exact (size_scatterWords _ _ _ _ _ _).trans (h 4)
    · exact (size_scatterWords _ _ _ _ _ _).trans (h 5)

/-- **The index side's tables all have `2^width` entries.** -/
theorem indexTabs_of (W : Witness) (theta0 : E) (drawn : List E)
    (hlen : drawn.length = packedChallenges tables (linkNRows W) W.chunks.width) :
    Tabs W.chunks.width
      (indexProds W (LinkChallenges.ofDraw tables (linkNRows W) W.chunks.width W.chunks.d theta0
        drawn)) := by
  set ch := LinkChallenges.ofDraw tables (linkNRows W) W.chunks.width W.chunks.d theta0 drawn
  have hz : ch.zeta.length = W.chunks.width := length_zeta tables rfl _ _ _ _ _ hlen
  have hsc := size_scattered W ch (List.range nTables) (Vector.replicate 6
    (Array.replicate (2 ^ W.chunks.width) 0)) (fun i ↦ by simp)
  have hall : ∀ t ∈ (indexProds W ch).tables, t.size = 2 ^ W.chunks.width := by
    intro t ht
    simp only [indexProds, indexArrays, List.mem_toArray, List.mem_cons, List.not_mem_nil,
      or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsc 0
    · exact hsc 1
    · exact hsc 2
    · simp
    · exact hsc 4
    · simp
    · rw [Keccak.size_eqTable, hz]
    · simp
    · simp
    · exact hsc 3
    · simp
    · exact hsc 5
    · simp
  exact ⟨hall, hsc 0⟩

end LeanVM.Prover.Complete

end
