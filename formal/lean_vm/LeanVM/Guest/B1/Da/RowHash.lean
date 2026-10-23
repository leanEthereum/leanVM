/-
  LeanVM.Guest.B1.Da.RowHash

  B1 for `__loop93` (G:2937-2948): each row's digest, the hash of its prefix cells' digests.
-/

module

public import LeanVM.Guest.B1.Da.Loops
import LeanVM.Guest.B1.Sig.Decide

/-!
# The row branch's hashing

`__loop93` reads `run = prefix_bases[x]`, hashes the 128 cells at `run` as 32 blocks (counters
`64·(b + 1)`, the last final) and stores the digest as leaf `x` of the row tree, at `rowtree·x²`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- Row `x`'s digest: the 128 cells at `prefix_bases[x]`, hashed, stored at `rowtree·x²`. -/
def L93Step (rd : Reader) (pb rt x : E) : Prop :=
  ∃ P cs, LoadHolds rd (pb * x) 0 P ∧ cs.length = 128 ∧ CellsAt rd P cs ∧ (∀ c ∈ cs, IsCanonical128 c) ∧
    CellsAt rd (rt * (x * x)) [(digestScalars (blake2sBytes (cs.flatMap cellBytes))).1,
      (digestScalars (blake2sBytes (cs.flatMap cellBytes))).2]

/-- Block `b ≥ 1`. -/
def rhBlk (b : ℕ) : List Atom :=
  [.load (.n (7 * b + 8 + 0)) (.n 5) (4 * b), .load (.n (7 * b + 8 + 1)) (.n 5) (4 * b + 1),
   .load (.n (7 * b + 8 + 2)) (.n 5) (4 * b + 2), .load (.n (7 * b + 8 + 3)) (.n 5) (4 * b + 3),
   .const (.n (7 * b + 12)) (word (64 * (b + 1)) (if b + 1 = 32 then 4294967295 else 0) 0),
   .blake2s (.n (7 * b + 8 + 0)) (.n (7 * b + 8 + 1)) (.n (7 * b + 8 + 2)) (.n (7 * b + 8 + 3))
     (.n (7 * b + 6)) (.n (7 * b + 6 + 1)) (.n (7 * (b + 1) + 6)) (.n (7 * (b + 1) + 6 + 1)) (.n (7 * b + 12))]

/-- `__loop93`'s atoms. -/
def rhAtoms : List Atom :=
  [.mul (.n 4) (.n 2) (.n 0), .load (.n 5) (.n 4) 0, .load (.n 6) (.n 5) 0, .load (.n 7) (.n 5) 1,
   .load (.n 8) (.n 5) 2, .load (.n 9) (.n 5) 3,
   .const (.n 10) (word 13503953895743350343 11912009169889063794 0),
   .const (.n 11) (word 11170449402626986623 6620516960021240235 0), .const (.n 12) (word 64 0 0),
   .blake2s (.n 6) (.n 7) (.n 8) (.n 9) (.n 10) (.n 11) (.n 13) (.n 14) (.n 12)] ++
  (List.range 31).flatMap (fun b => rhBlk (b + 1)) ++
  [.mul (.n 232) (.n 0) (.n 0), .mul (.n 233) (.n 3) (.n 232), .load (.n 230) (.n 233) 0,
   .load (.n 231) (.n 233) 1, .const (.n 234) (word 2 0 0), .mul (.n 235) (.n 0) (.n 234),
   .add (.n 236) (.n 235) (.n 1), .const (.n 237) (word 2 0 0), .mul (.n 238) (.n 0) (.n 237)]

/-- `__loop93`'s body. -/
def rhBody : List Stmt :=
  rhAtoms.map .atom ++ [.callIf (.n 236) "__loop93" [.n 238, .n 1, .n 2, .n 3], .ret []]

open scoped LeanVM.Guest.B1.Sig.Dec in
theorem rh_eq : Data.core535.body = rhBody := by decide +kernel

set_option maxRecDepth 100000 in
theorem find_l93 : coreProgram.find? "__loop93" = some ⟨"__loop93", [.n 0, .n 1, .n 2, .n 3], rhBody⟩ := by
  rw [Program.find?_of_indexOf? (j := 535) (by decide +kernel) rfl, ← rh_eq]
  rfl

theorem rhBlk_iff {rd : Reader} {σ : Val} {b : ℕ} :
    (∀ a ∈ rhBlk b, a.Holds rd σ) ↔
      LoadHolds rd (σ (.n 5)) (4 * b) (σ (.n (7 * b + 8 + 0))) ∧
      LoadHolds rd (σ (.n 5)) (4 * b + 1) (σ (.n (7 * b + 8 + 1))) ∧
      LoadHolds rd (σ (.n 5)) (4 * b + 2) (σ (.n (7 * b + 8 + 2))) ∧
      LoadHolds rd (σ (.n 5)) (4 * b + 3) (σ (.n (7 * b + 8 + 3))) ∧
      σ (.n (7 * b + 12)) = word (64 * (b + 1)) (if b + 1 = 32 then 4294967295 else 0) 0 ∧
      CompressCells ![σ (.n (7 * b + 8 + 0)), σ (.n (7 * b + 8 + 1)), σ (.n (7 * b + 8 + 2)),
        σ (.n (7 * b + 8 + 3))] (σ (.n (7 * b + 6))) (σ (.n (7 * b + 6 + 1))) (σ (.n (7 * (b + 1) + 6)))
        (σ (.n (7 * (b + 1) + 6 + 1))) (σ (.n (7 * b + 12))) := by
  simp only [rhBlk, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true]

/-- The chain's metadata cells. -/
def rhMd (j : ℕ) : E := metadataCell (64 * (j + 1)) (decide (j + 1 = 32))

theorem rhMd_word (b : ℕ) : word (64 * (b + 1)) (if b + 1 = 32 then 4294967295 else 0) 0 = rhMd b :=
  word_metadata _ _

/-- The bytes of `n` blocks of a list of `4n` cells are the cells' bytes. -/
theorem blocksOf_bytes (cs : List E) (n : ℕ) (h : cs.length = 4 * n) :
    (List.range n).flatMap (fun j => blockBytes (blocksOf cs j)) = cs.flatMap cellBytes := by
  rw [← flatMap_range_getD cs 0 cellBytes, h, flatMap_range_mul 4]
  refine List.flatMap_congr fun j _ => ?_
  simp [blockBytes, blocksOf, List.range_succ, List.append_assoc]

/-- The loaded words' positions: cell `4b + r` at value `rhLd b r`. -/
def rhLd (b r : ℕ) : ℕ := if b = 0 then 6 + r else 7 * b + 8 + r

/-- The chain's state after `b` blocks (its first cell). -/
def rhSt (b : ℕ) : ℕ := if b = 0 then 10 else 7 * b + 6

theorem rh_fwd {rd : Reader} {σ : Val} (hA : ∀ a ∈ rhAtoms, a.Holds rd σ) :
    L93Step rd (σ (.n 2)) (σ (.n 3)) (σ (.n 0)) ∧ σ (.n 236) = σ (.n 0) * gen + σ (.n 1) ∧
      σ (.n 238) = σ (.n 0) * gen := by
  simp only [rhAtoms, List.forall_mem_append, forall_mem_flatMap_range, List.forall_mem_cons, Atom.Holds,
    forall_mem_nil_iff, and_true] at hA
  obtain ⟨⟨⟨m4, l5, l6, l7, l8, l9, c10, c11, c12, b0⟩, hblk⟩, m232, m233, l230, l231, c234, m235, a236,
    c237, m238⟩ := hA
  set P := σ (.n 5)
  -- every block, uniformly
  have hB : ∀ b < 32, (∀ r < 4, LoadHolds rd P (4 * b + r) (σ (.n (rhLd b r)))) ∧
      σ (.n (7 * b + 12)) = rhMd b ∧
      CompressCells ![σ (.n (rhLd b 0)), σ (.n (rhLd b 1)), σ (.n (rhLd b 2)), σ (.n (rhLd b 3))]
        (σ (.n (rhSt b))) (σ (.n (rhSt b + 1))) (σ (.n (rhSt (b + 1)))) (σ (.n (rhSt (b + 1) + 1)))
        (σ (.n (7 * b + 12))) := by
    intro b hb
    rcases Nat.eq_zero_or_pos b with rfl | hpos
    · refine ⟨fun r hr => ?_, by rw [c12]; rfl, b0⟩
      interval_cases r
      exacts [l6, l7, l8, l9]
    · obtain ⟨i, rfl⟩ : ∃ i, b = i + 1 := ⟨b - 1, by omega⟩
      obtain ⟨a0, a1, a2, a3, am, ac⟩ := rhBlk_iff.mp (hblk i (by omega))
      have e : ∀ r, rhLd (i + 1) r = 7 * (i + 1) + 8 + r := fun r => by
        unfold rhLd; rw [ite_neg' (by omega)]
      have s1 : rhSt (i + 1) = 7 * (i + 1) + 6 := by unfold rhSt; rw [ite_neg' (by omega)]
      have s2 : rhSt (i + 1 + 1) = 7 * (i + 1 + 1) + 6 := by unfold rhSt; rw [ite_neg' (by omega)]
      refine ⟨fun r hr => ?_, by rw [am, rhMd_word], ?_⟩
      · rw [e]
        interval_cases r
        exacts [a0, a1, a2, a3]
      · rw [e, e, e, e, s1, s2]
        exact ac
  let cs : List E := (List.range 128).map (cellAt rd P)
  have hcs : ∀ k < 128, cs.getD k 0 = cellAt rd P k ∧ LoadHolds rd P k (cellAt rd P k) := by
    intro k hk
    refine ⟨by simp [cs, List.getD_eq_getElem?_getD, hk], ?_⟩
    obtain ⟨b, r, hr, rfl⟩ : ∃ b r, r < 4 ∧ k = 4 * b + r := ⟨k / 4, k % 4, by omega, by omega⟩
    exact load_cellAt ((hB b (by omega)).1 r hr)
  have hblkv : ∀ b < 32, ![σ (.n (rhLd b 0)), σ (.n (rhLd b 1)), σ (.n (rhLd b 2)), σ (.n (rhLd b 3))] =
      blocksOf cs b := by
    intro b hb
    have e : ∀ r < 4, σ (.n (rhLd b r)) = cs.getD (4 * b + r) 0 := fun r hr => by
      rw [(hcs _ (by omega)).1, cellAt_of_load ((hB b hb).1 r hr)]
    simp only [blocksOf]
    rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), Nat.add_zero]
  have hch := chain_eq_blake2sBytes_blocks (n := 31) (blocks := blocksOf cs)
    (st := fun b => (σ (.n (rhSt b)), σ (.n (rhSt b + 1)))) (md := fun b => σ (.n (7 * b + 12)))
    (by show (σ (.n 10), σ (.n 11)) = _; rw [c10, c11, iv0_word, iv1_word]; rfl)
    (fun j hj => by rw [(hB j (by omega)).2.1]; unfold rhMd; congr 1; simp only [decide_eq_false_iff_not]; omega)
    (by rw [(hB 31 (by omega)).2.1]; rfl)
    (fun j hj => by rw [← hblkv j (by omega)]; exact (hB j (by omega)).2.2)
  rw [blocksOf_bytes cs 32 (by simp [cs])] at hch
  have hst : rhSt (31 + 1) = 230 := rfl
  simp only [hst] at hch
  have h230 : σ (.n 230) = (digestScalars (blake2sBytes (cs.flatMap cellBytes))).1 := congrArg Prod.fst hch
  have h231 : σ (.n 231) = (digestScalars (blake2sBytes (cs.flatMap cellBytes))).2 := congrArg Prod.snd hch
  refine ⟨⟨P, cs, by rw [m4] at l5; exact l5, by simp [cs], fun k hk => ?_, fun c hc => ?_, ?_⟩,
    by rw [a236, m235, c234, word_gen], by rw [m238, c237, word_gen]⟩
  · have hk' : k < 128 := by simpa [cs] using hk
    have := (hcs k hk').2
    rwa [← (hcs k hk').1, List.getD_eq_getElem _ _ hk] at this
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    have hk' : k < 128 := by simpa [cs] using hk
    obtain ⟨b, r, hr, e⟩ : ∃ b r, r < 4 ∧ k = 4 * b + r := ⟨k / 4, k % 4, by omega, by omega⟩
    have hc' := ((hB b (by omega)).2.2).1
    rw [hblkv b (by omega)] at hc'
    have := hc' ⟨r, hr⟩
    have hg : IsCanonical128 (cs.getD (4 * b + r) 0) := by
      interval_cases r <;> simpa [blocksOf] using this
    rw [← e, List.getD_eq_getElem _ _ hk] at hg
    exact hg
  · rw [m233, m232] at l230 l231
    rw [← h230, ← h231]
    exact cellsAt_two.mpr ⟨l230, l231⟩

/-- The honest values of `__loop93`, over an abstract chain of states. -/
def rhVals (x W pb rt P : E) (cs : List E) (st : ℕ → E × E) (k : ℕ) : E :=
  if k < 6 then [x, W, pb, rt, pb * x, P].getD k 0 else
  if k < 10 then cs.getD (k - 6) 0 else
  if k < 15 then [(st 0).1, (st 0).2, rhMd 0, (st 1).1, (st 1).2].getD (k - 10) 0 else
  if k < 232 then [cs.getD (4 * ((k - 8) / 7)) 0, cs.getD (4 * ((k - 8) / 7) + 1) 0,
    cs.getD (4 * ((k - 8) / 7) + 2) 0, cs.getD (4 * ((k - 8) / 7) + 3) 0, rhMd ((k - 8) / 7),
    (st ((k - 8) / 7 + 1)).1, (st ((k - 8) / 7 + 1)).2].getD ((k - 8) % 7) 0 else
  [x * x, rt * (x * x), gen, x * gen, x * gen + W, gen, x * gen].getD (k - 232) 0

theorem rhVals_blk (x W pb rt P : E) (cs : List E) (st : ℕ → E × E) {b r : ℕ} (hb1 : 1 ≤ b)
    (hb : b < 32) (hr : r < 7) : rhVals x W pb rt P cs st (7 * b + 8 + r) =
      [cs.getD (4 * b) 0, cs.getD (4 * b + 1) 0, cs.getD (4 * b + 2) 0, cs.getD (4 * b + 3) 0, rhMd b,
        (st (b + 1)).1, (st (b + 1)).2].getD r 0 := by
  unfold rhVals
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
    show (7 * b + 8 + r - 8) / 7 = b by omega, show (7 * b + 8 + r - 8) % 7 = r by omega]

theorem rhVals_st (x W pb rt P : E) (cs : List E) (st : ℕ → E × E) {b : ℕ} (hb1 : 1 ≤ b)
    (hb : b ≤ 32) : rhVals x W pb rt P cs st (7 * b + 6) = (st b).1 ∧
      rhVals x W pb rt P cs st (7 * b + 6 + 1) = (st b).2 := by
  rcases Nat.lt_or_ge b 2 with h | h
  · obtain rfl : b = 1 := by omega
    exact ⟨rfl, rfl⟩
  · obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    have a := rhVals_blk x W pb rt P cs st (b := c) (r := 5) (by omega) (by omega) (by omega)
    have a' := rhVals_blk x W pb rt P cs st (b := c) (r := 6) (by omega) (by omega) (by omega)
    rw [show 7 * c + 8 + 5 = 7 * (c + 1) + 6 by ring] at a
    rw [show 7 * c + 8 + 6 = 7 * (c + 1) + 6 + 1 by ring] at a'
    exact ⟨a, a'⟩

theorem rh_bwd {rd : Reader} {x W pb rt P : E} {cs : List E} {st : ℕ → E × E}
    (hlen : cs.length = 128) (hP : LoadHolds rd (pb * x) 0 P) (hcells : CellsAt rd P cs)
    (e0 : st 0 = digestScalars paramIv)
    (hc : ∀ j < 32, CompressCells (blocksOf cs j) (st j).1 (st j).2 (st (j + 1)).1 (st (j + 1)).2 (rhMd j))
    (hout : CellsAt rd (rt * (x * x)) [(st 32).1, (st 32).2]) :
    ∀ a ∈ rhAtoms, a.Holds rd (fun v => rhVals x W pb rt P cs st v.idx) := by
  have hl : ∀ k < 128, LoadHolds rd P k (cs.getD k 0) := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hcells k (by omega)
  obtain ⟨o0, o1⟩ := cellsAt_two.mp hout
  simp only [rhAtoms, List.forall_mem_append, forall_mem_flatMap_range, List.forall_mem_cons, Atom.Holds,
    forall_mem_nil_iff, and_true]
  refine ⟨⟨⟨rfl, hP, hl 0 (by omega), hl 1 (by omega), hl 2 (by omega), hl 3 (by omega), ?_, ?_, rfl, ?_⟩,
    fun i hi => rhBlk_iff.mpr ?_⟩, rfl, rfl, o0, o1, word_gen.symm, rfl, rfl, word_gen.symm, rfl⟩
  · show (st 0).1 = _; rw [e0, iv0_word]
  · show (st 0).2 = _; rw [e0, iv1_word]
  · exact hc 0 (by omega)
  · have v : ∀ r < 7, rhVals x W pb rt P cs st (7 * (i + 1) + 8 + r) = _ := fun r hr =>
      rhVals_blk x W pb rt P cs st (b := i + 1) (by omega) (by omega) hr
    have m : rhVals x W pb rt P cs st (7 * (i + 1) + 12) = rhMd (i + 1) := v 4 (by omega)
    have s0 := rhVals_st x W pb rt P cs st (b := i + 1) (by omega) (by omega)
    have s1 := rhVals_st x W pb rt P cs st (b := i + 1 + 1) (by omega) (by omega)
    have v0 : rhVals x W pb rt P cs st (7 * (i + 1) + 8 + 0) = cs.getD (4 * (i + 1)) 0 := v 0 (by omega)
    have v1 : rhVals x W pb rt P cs st (7 * (i + 1) + 8 + 1) = cs.getD (4 * (i + 1) + 1) 0 := v 1 (by omega)
    have v2 : rhVals x W pb rt P cs st (7 * (i + 1) + 8 + 2) = cs.getD (4 * (i + 1) + 2) 0 := v 2 (by omega)
    have v3 : rhVals x W pb rt P cs st (7 * (i + 1) + 8 + 3) = cs.getD (4 * (i + 1) + 3) 0 := v 3 (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [v0]; exact hl _ (by omega)
    · rw [v1]; exact hl _ (by omega)
    · rw [v2]; exact hl _ (by omega)
    · rw [v3]; exact hl _ (by omega)
    · rw [m, rhMd_word]
    · rw [v0, v1, v2, v3, m, s0.1, s0.2, s1.1, s1.2]
      exact hc (i + 1) (by omega)

theorem l93_step (rd : Reader) (W pb rt : E) (C : CallRel) (x : E) :
    (∃ fn, coreProgram.find? "__loop93" = some fn ∧ fn.Sem C rd (x :: [W, pb, rt]) []) ↔
      L93Step rd pb rt x ∧ IsInK (x * gen + W) ∧ (x * gen + W ≠ 0 → C "__loop93" (x * gen :: [W, pb, rt]) []) := by
  simp only [find_l93, Option.some.injEq, exists_eq_left', Fn.Sem, rhBody, holdsList_atoms, Stmt.HoldsList,
    Stmt.Holds, List.map_cons, List.map_nil]
  constructor
  · rintro ⟨σ, hp, hA, hk, hnext, -⟩
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
    obtain ⟨hS, e236, e238⟩ := rh_fwd hA
    rw [e236] at hk hnext
    rw [e238] at hnext
    exact ⟨hS, hk, hnext⟩
  · rintro ⟨⟨P, cs, hP, hlen, hcells, hcan, hout⟩, hk, hnext⟩
    have hg : ∀ k < 128, IsCanonical128 (cs.getD k 0) := fun k hk => by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hcan _ (List.getElem_mem _)
    have hcanb : ∀ j < 32, ∀ r, IsCanonical128 (blocksOf cs j r) := fun j hj r => by
      fin_cases r
      exacts [hg (4 * j) (by omega), hg (4 * j + 1) (by omega), hg (4 * j + 2) (by omega),
        hg (4 * j + 3) (by omega)]
    have hc : ∀ j < 32, CompressCells (blocksOf cs j)
        (digestScalars (chainRun paramIv (blocksOf cs) rhMd j)).1
        (digestScalars (chainRun paramIv (blocksOf cs) rhMd j)).2
        (digestScalars (chainRun paramIv (blocksOf cs) rhMd (j + 1))).1
        (digestScalars (chainRun paramIv (blocksOf cs) rhMd (j + 1))).2 (rhMd j) :=
      fun j hj => (compressCells_chainRun (hcanb j hj) (isCanonical128_metadataCell _ _)).mpr rfl
    have h32 : chainRun paramIv (blocksOf cs) rhMd 32 = blake2sBytes (cs.flatMap cellBytes) := by
      rw [chainRun_blocks (n := 31) (fun j hj r => hcanb j (by omega) r) (fun j hj => by
        unfold rhMd; congr 1; simp only [decide_eq_false_iff_not]; omega) rfl, blocksOf_bytes cs 32 (by omega)]
    refine ⟨fun v => rhVals x W pb rt P cs (fun j => digestScalars (chainRun paramIv (blocksOf cs) rhMd j)) v.idx,
      rfl, rh_bwd hlen hP hcells rfl hc (by rw [h32]; exact hout), hk, hnext, trivial⟩

theorem l93_iff (rd : Reader) (W pb rt : E) (k : ℕ) :
    coreProgram.Rel rd "__loop93" (gen ^ k :: [W, pb, rt]) [] ↔
      ∃ m, k < m ∧ W = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ W) ∧
        ∀ j, k ≤ j → j < m → L93Step rd pb rt (gen ^ j) :=
  loop_iff (B := fun _ x => L93Step rd pb rt x) (fun _ _ _ _ h => h) (l93_step rd W pb rt) k

end
end LeanVM.Guest.B1.Digest
