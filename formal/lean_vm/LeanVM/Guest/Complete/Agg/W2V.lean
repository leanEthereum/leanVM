module

public import LeanVM.Guest.Complete.Agg.W2A

/-!
# `aggregate_claims`' second run, its values

On the honest valuation `aV`, the values `aW2` computes:

* `freshAt`, `bufLoad`: a load from a buffer at an offset reads, or a store holds, its honest
  content; its address is the node's own data.
* `w2_ptr`, `w2_row`: the last row's pointer and words (`rowW (aggAbs cs)`); `w2_perm`: its
  permutation is the sponge's (`Fs.perm`); `w2_nonce`: the nonce permutation's cells are `aN w`'s.
* `w2_sq`: block `k` of the squeezes holds `sqIter k` of the sponge after `λ`; `w2_col`: its cell `0`
  is the column challenge `k`; `w2_cap`: the last block's capacity is `aggCols`' sponge's.
* `aTree_lvl`: `eq_col_tree`'s level `t` at `2^(t+1) - 2`; `w2_tree235`, `w2_tree156`: every load of
  the tree reads or writes its honest word.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC
open LeanVM.Guest.Complete
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

attribute [local instance high] LeanVM.Guest.Core.instDecidableEqAtom

/-! ## The absorbed sponge -/

theorem padToRate_len (ws : List E) : (padToRate ws).length % 4 = 0 := by
  show (ws ++ List.replicate (Batch.zerosToWholeRate ws.length) 0).length % 4 = 0
  rw [List.length_append, List.length_replicate, Batch.zerosToWholeRate]
  show (ws.length + (4 - ws.length % 4) % 4) % 4 = 0
  omega

theorem flatMap_childCells_len : ∀ cs : List ChildClaims, (cs.flatMap Batch.childCells).length % 4 = 0
  | [] => rfl
  | ch :: cs => by
    rw [List.flatMap_cons, List.length_append]
    have := padToRate_len ch.words
    have := flatMap_childCells_len cs
    rw [Batch.childCells]
    omega

/-- **The absorbed sponge has four scalars waiting.** -/
theorem aggAbs_pend (cs : List ChildClaims) : (aggAbs cs).pend.length = 4 := by
  have h0 : aggS0.absorbAll (Batch.childCountCells cs.length) dsObserve = absSt cs.length cs 0 := by
    rw [absSt, List.take_zero, List.flatMap_nil, List.append_nil]
  rw [aggAbs, Batch.cellsBeforeChallenge, Main.absorbAll_append, h0,
    pend_absorbAll _ _ _ (by rw [absSt_zero]; simp) (by rw [absSt_zero]; simp)]
  have := flatMap_childCells_len cs
  rw [absSt_zero]
  simp only [List.length_map, List.length_cons, List.length_nil]
  omega

section
variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {cover : List E} {c : ℕ}

/-! ## Buffers at an offset -/

/-- **A load into a new value** from buffer `j` at `q + off` reads its honest content. -/
theorem freshAt (hl : (aLists s w).map List.length = aBufs w.children.length) (hc : c < 2 ^ 62)
    (hn : w.children.length ≤ 16) {d p : V} {off j q : ℕ} (hx : Atom.load d p off ∈ atomsOf aggP)
    (hS : Atom.load d p off ∉ storesOf 6 aggP) (hp : aV al s w cover c p = ptrAt (aB c w.children.length j + q))
    (hj : j < 11) (ho : q + off < (aBufs w.children.length).getD j 0) :
    aV al s w cover c d = ((aLists s w).getD j []).getD (q + off) 0 := by
  obtain ⟨hi, hv⟩ := valAt_own (al := al) (cover := cover) (c := c) hl hj ho
  have hsum := aBufs_sum w.children.length
  have hb := (aB_lt (c := c) hj ho).2
  rw [← Nat.add_assoc] at hi hv
  exact (aLoad_fresh hx hS hp hi (by omega)).1.trans hv

/-- **A load or store at its honest content** in buffer `j` at `q + off`: it holds on every memory
holding the own words, its address the node's own data. -/
theorem bufLoad (hl : (aLists s w).map List.length = aBufs w.children.length) {cert : String → V → ℕ}
    {fp : ℕ} {f : String} {es : List Memory.Ev} {R D : ℕ → Prop} {d p : V} {off j q : ℕ}
    (hp : aV al s w cover c p = ptrAt (aB c w.children.length j + q)) (hj : j < 11)
    (ho : q + off < (aBufs w.children.length).getD j 0)
    (hv : aV al s w cover c d = ((aLists s w).getD j []).getD (q + off) 0) :
    (∀ rd, HoldsWords rd (aWo s w c) → LoadHolds rd (aV al s w cover c p) off (aV al s w cover c d)) ∧
      ∀ A, Memory.Ev.loadAddr? (aV al s w cover c) (.atom (.load d p off)) = some A →
        ∃ i, A = addressOfIndex i ∧ (ownData cert fp c f (aBufs w.children.length) es i ∨ R i ∨ D i) := by
  refine ⟨fun rd h => ?_, fun A h => ?_⟩
  · obtain ⟨hq, hlen⟩ := aWo_get (c := c) hl hj
    rw [hp, hv]
    exact loadHolds_of_rd (by rw [Nat.add_assoc]; exact holds_run h hq (by rw [hlen]; exact ho))
  · simp only [Memory.Ev.loadAddr?, Option.some.injEq] at h
    rw [← h, hp, addr_ptr]
    exact ⟨_, rfl, Or.inl (by rw [Nat.add_assoc]; exact own_aB hj ho)⟩

/-! ## The parts' atoms are the body's -/

theorem mem_ptr {x : Atom} (h : x ∈ w2Ptr) : x ∈ atomsOf aggP := w2_mem x (by simp only [w2A, List.mem_append]; tauto)
theorem mem_row {x : Atom} (h : x ∈ w2Row) : x ∈ atomsOf aggP := w2_mem x (by simp only [w2A, List.mem_append]; tauto)
theorem mem_perm {x : Atom} (h : x ∈ w2Perm) : x ∈ atomsOf aggP := w2_mem x (by simp only [w2A, List.mem_append]; tauto)
theorem mem_non {x : Atom} (h : x ∈ w2Non) : x ∈ atomsOf aggP := w2_mem x (by simp only [w2A, List.mem_append]; tauto)
theorem mem_grind {x : Atom} (h : x ∈ aggGrindA) : x ∈ atomsOf aggP :=
  w2_mem x (by simp only [w2A, List.mem_append]; tauto)
theorem mem_sq {x : Atom} (h : x ∈ w2Sq) : x ∈ atomsOf aggP := w2_mem x (by simp only [w2A, List.mem_append]; tauto)
theorem mem_tree {x : Atom} (h : x ∈ w2Tree) : x ∈ atomsOf aggP := w2_mem x (by simp only [w2A, List.mem_append]; tauto)
theorem mem_tail {x : Atom} (h : x ∈ w2Tail) : x ∈ atomsOf aggP := w2_mem x (by simp only [w2A, List.mem_append]; tauto)

/-- A `KECCAK` of the body, evaluated. -/
theorem aV_keccak {ins outs : List V} (h : Atom.keccak ins outs false false ∈ atomsOf aggP) (k : Fin 13)
    (hk : k.val < outs.length) :
    aV al s w cover c outs[k.val] =
      cellsOfState (keccakF1600 (stateOfCells (cells13 (ins.map (aV al s w cover c))) false)) false k :=
  (aV_good (al := al) (s := s) (w := w) (cover := cover) (c := c) h).2.2 k hk

/-! ## The last row and its permutation -/

/-- **The last row's pointer**: `absorb·g^(13m)`. -/
theorem w2_ptr : aV al s w cover c (.n 39) = ptrAt (aB c w.children.length 3 + 13 * w.children.length) := by
  have g : ∀ {d x y : ℕ}, Atom.mul (.n d) (.n x) (.n y) ∈ w2Ptr → x < d → y < d →
      aV al s w cover c (.n d) = aV al s w cover c (.n x) * aV al s w cover c (.n y) := fun h hx hy =>
    aGood_mul (aggArgs_length _ _) (mem_ptr h) hx hy
  have v0 : aV al s w cover c (.n 0) = gen ^ w.children.length := aV_param (by norm_num)
  obtain ⟨-, -, -, p30, -⟩ := aV_ptrs (al := al) (s := s) (w := w) (cover := cover) (c := c)
  have e : ∀ d x y : ℕ, Atom.mul (.n d) (.n x) (.n y) ∈ w2Ptr → x < d → y < d →
      aV al s w cover c (.n d) = aV al s w cover c (.n x) * aV al s w cover c (.n y) := fun _ _ _ h hx hy => g h hx hy
  have v34 : aV al s w cover c (.n 34) = gen ^ (2 * w.children.length) := by
    rw [e 34 0 0 (by simp [w2Ptr]) (by norm_num) (by norm_num), v0, ← pow_add, two_mul]
  have v35 : aV al s w cover c (.n 35) = gen ^ (3 * w.children.length) := by
    rw [e 35 34 0 (by simp [w2Ptr]) (by norm_num) (by norm_num), v34, v0, ← pow_add, show 2 * w.children.length + w.children.length = 3 * w.children.length by ring]
  have v36 : aV al s w cover c (.n 36) = gen ^ (6 * w.children.length) := by
    rw [e 36 35 35 (by simp [w2Ptr]) (by norm_num) (by norm_num), v35, ← pow_add, show 3 * w.children.length + 3 * w.children.length = 6 * w.children.length by ring]
  have v37 : aV al s w cover c (.n 37) = gen ^ (12 * w.children.length) := by
    rw [e 37 36 36 (by simp [w2Ptr]) (by norm_num) (by norm_num), v36, ← pow_add, show 6 * w.children.length + 6 * w.children.length = 12 * w.children.length by ring]
  have v38 : aV al s w cover c (.n 38) = gen ^ (13 * w.children.length) := by
    rw [e 38 37 0 (by simp [w2Ptr]) (by norm_num) (by norm_num), v37, v0, ← pow_add, show 12 * w.children.length + w.children.length = 13 * w.children.length by ring]
  rw [e 39 30 38 (by simp [w2Ptr]) (by norm_num) (by norm_num), v38, p30, ptrAt_mul_gen_pow]

/-- **The last row's words** are the absorbed sponge's row. -/
theorem w2_row (hl : (aLists s w).map List.length = aBufs w.children.length) (hc : c < 2 ^ 62)
    (hn : w.children.length ≤ 16) :
    ∀ i < 13, aV al s w cover c (.n (40 + i)) = (rowW (aggAbs (aCs w))).getD i 0 := by
  intro i hi
  have hx : Atom.load (.n (40 + i)) (.n 39) i ∈ atomsOf aggP :=
    mem_row (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  rw [freshAt hl hc hn hx (w2_fresh.1 i hi) w2_ptr (by norm_num) (by simp [aBufs]; omega)]
  show ((List.range (w.children.length + 1)).flatMap fun j => rowW (absSt w.children.length (aCs w) j)).getD
    (13 * w.children.length + i) 0 = _
  have hlen : ((List.range w.children.length).flatMap fun j => rowW (absSt w.children.length (aCs w) j)).length =
      13 * w.children.length := by
    rw [flatMap_length_const (n := 13) (fun j _ => rowW_length (absSt_ok _ _ j)), List.length_range]
  rw [List.range_succ, List.flatMap_append, List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen,
    Nat.add_sub_cancel_left, List.flatMap_singleton, absSt_last (aCs_length w)]

/-- The permutation's inputs are a row's rate cells, then its capacity cells. -/
theorem w2_kin {S : Fs} (hS : StOk S) {σ : Val} (hrow : ∀ i < 13, σ (.n (40 + i)) = (rowW S).getD i 0)
    (c53 : σ (.n 53) = σ (.n 49)) (c54 : σ (.n 54) = σ (.n 50)) (c55 : σ (.n 55) = σ (.n 51))
    (c56 : σ (.n 56) = σ (.n 52)) :
    cells13 (w2Kin.map σ) = cells13 (rateOf S.pend ++ S.cap) := by
  have hlen : (rateOf S.pend).length = 8 := by simp [rateOf]
  have hR : ∀ c < 8, (rateOf S.pend ++ S.cap).getD c 0 = (rowW S).getD (5 + c) 0 := fun c hc => by
    rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hc), rowW_getD_rate hS hc]
    simp [rateOf, List.getD_eq_getElem?_getD, hc]
  have hC : ∀ i < 5, (rateOf S.pend ++ S.cap).getD (8 + i) 0 = (rowW S).getD i 0 := fun i hi => by
    rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left,
      rowW_getD_cap hS hi]
  funext ⟨k, hk⟩
  simp only [cells13]
  interval_cases k
  · rw [hR 0 (by norm_num)]; exact hrow 5 (by norm_num)
  · rw [hR 1 (by norm_num)]; exact hrow 6 (by norm_num)
  · rw [hR 2 (by norm_num)]; exact hrow 7 (by norm_num)
  · rw [hR 3 (by norm_num)]; exact hrow 8 (by norm_num)
  · rw [hR 4 (by norm_num)]; exact c53.trans (hrow 9 (by norm_num))
  · rw [hR 5 (by norm_num)]; exact c54.trans (hrow 10 (by norm_num))
  · rw [hR 6 (by norm_num)]; exact c55.trans (hrow 11 (by norm_num))
  · rw [hR 7 (by norm_num)]; exact c56.trans (hrow 12 (by norm_num))
  · rw [hC 0 (by norm_num)]; exact hrow 0 (by norm_num)
  · rw [hC 1 (by norm_num)]; exact hrow 1 (by norm_num)
  · rw [hC 2 (by norm_num)]; exact hrow 2 (by norm_num)
  · rw [hC 3 (by norm_num)]; exact hrow 3 (by norm_num)
  · rw [hC 4 (by norm_num)]; exact hrow 4 (by norm_num)

/-- **The last row's permutation** is the absorbed sponge's. -/
theorem w2_perm (hl : (aLists s w).map List.length = aBufs w.children.length) (hc : c < 2 ^ 62)
    (hn : w.children.length ≤ 16) (k : Fin 13) :
    aV al s w cover c (.n (57 + k.val)) = cellsOfState (aggAbs (aCs w)).perm false k := by
  have cp : ∀ {d x : ℕ}, Atom.copy (.n d) (.n x) ∈ w2Perm → aV al s w cover c (.n d) = aV al s w cover c (.n x) :=
    fun h => aV_good (al := al) (s := s) (w := w) (cover := cover) (c := c) (mem_perm h)
  have hk := aV_keccak (al := al) (s := s) (w := w) (cover := cover) (c := c)
    (mem_perm (show Atom.keccak w2Kin ((List.range 13).map fun i => .n (57 + i)) false false ∈ w2Perm by
      simp [w2Perm])) k (by simp)
  simp only [List.getElem_map, List.getElem_range] at hk
  rw [hk, w2_kin (absSt_last (aCs_length w) ▸ absSt_ok _ _ _) (w2_row hl hc hn) (cp (by simp [w2Perm]))
    (cp (by simp [w2Perm])) (cp (by simp [w2Perm])) (cp (by simp [w2Perm]))]
  rfl

/-! ## The nonce -/

/-- **The nonce permutation's cells** are `aN w`'s. -/
theorem w2_nonce (hl : (aLists s w).map List.length = aBufs w.children.length) (hc : c < 2 ^ 62)
    (hn : w.children.length ≤ 16) (k : Fin 13) :
    aV al s w cover c (.n (78 + k.val)) = cellsOfState (aN w) false k := by
  have cst : ∀ {d : ℕ} {e : E}, Atom.const (.n d) e ∈ w2Non → aV al s w cover c (.n d) = e := fun h =>
    aGood_const (aggArgs_length _ _) (mem_non h)
  obtain ⟨p6, -⟩ := aV_ptrs (al := al) (s := s) (w := w) (cover := cover) (c := c)
  have v70 : aV al s w cover c (.n 70) = w.batchingHints.lambdaGrindNonce := by
    rw [freshAt (q := 0) hl hc hn (mem_non (by simp [w2Non])) w2_fresh.2.1 (by rw [p6, Nat.add_zero]) (by norm_num)
      (by simp [aBufs])]
    show (Batch.lambdaGrindNonceCells w.batchingHints ++ _).getD 0 0 = _
    rw [Batch.lambdaGrindNonceCells_eq]
    rfl
  have v71 : aV al s w cover c (.n 71) = w.batchingHints.lambdaGrindNonce :=
    (aV_good (al := al) (s := s) (w := w) (cover := cover) (c := c)
      (mem_non (show Atom.copy (.n 71) (.n 70) ∈ w2Non by simp [w2Non]))).trans v70
  have z : ∀ {d : ℕ}, Atom.const (.n d) (word 0 0) ∈ w2Non → aV al s w cover c (.n d) = 0 := fun h =>
    (cst h).trans word_zero
  have hP := w2_perm (al := al) (cover := cover) hl hc hn
  have hin : w2Nin.map (aV al s w cover c) = [w.batchingHints.lambdaGrindNonce, word 0 dsPowNonce, 0, 0, 0, 0, 0, 0] ++
      capOf (aggAbs (aCs w)).perm := by
    have h65 : aV al s w cover c (.n 65) = cellsOfState (aggAbs (aCs w)).perm false 8 := hP 8
    have h66 : aV al s w cover c (.n 66) = cellsOfState (aggAbs (aCs w)).perm false 9 := hP 9
    have h67 : aV al s w cover c (.n 67) = cellsOfState (aggAbs (aCs w)).perm false 10 := hP 10
    have h68 : aV al s w cover c (.n 68) = cellsOfState (aggAbs (aCs w)).perm false 11 := hP 11
    have h69 : aV al s w cover c (.n 69) = cellsOfState (aggAbs (aCs w)).perm false 12 := hP 12
    show [aV al s w cover c (.n 71), aV al s w cover c (.n 72), aV al s w cover c (.n 74), aV al s w cover c (.n 74),
      aV al s w cover c (.n 74), aV al s w cover c (.n 75), aV al s w cover c (.n 76), aV al s w cover c (.n 77),
      aV al s w cover c (.n 65), aV al s w cover c (.n 66), aV al s w cover c (.n 67), aV al s w cover c (.n 68),
      aV al s w cover c (.n 69)] = _
    rw [v71, cst (e := word 0 4) (by simp [w2Non]), z (d := 74) (by simp [w2Non]), z (d := 75) (by simp [w2Non]),
      z (d := 76) (by simp [w2Non]), z (d := 77) (by simp [w2Non]), h65, h66, h67, h68, h69]
    rfl
  have hk := aV_keccak (al := al) (s := s) (w := w) (cover := cover) (c := c)
    (mem_non (show Atom.keccak w2Nin ((List.range 13).map fun i => .n (78 + i)) false false ∈ w2Non by
      simp [w2Non])) k (by simp)
  simp only [List.getElem_map, List.getElem_range] at hk
  rw [hk, hin, aN, aggN, nonce_ins (aggAbs_pend _)]
  rfl

/-! ## The squeezes -/

/-- The sponge after `λ`: the nonce permutation's capacity, nothing waiting. -/
noncomputable def aS0 (w : NodeWitness) : Fs := ⟨capOf (aN w), []⟩

/-- **The squeezes, block by block**: block `k` reads eight zeros and the capacity of the sponge
after `k` squeezes, and permutes it. -/
theorem w2_sq (hl : (aLists s w).map List.length = aBufs w.children.length) (hc : c < 2 ^ 62)
    (hn : w.children.length ≤ 16) :
    ∀ k < 6, (sqIns w2Zs w2Cap0 157 k).map (aV al s w cover c) = List.replicate 8 0 ++ (sqIter k (aS0 w)).cap ∧
      ∀ q : Fin 13, aV al s w cover c (.n (157 + 13 * k + q.val)) = cellsOfState (sqIter k (aS0 w)).perm false q := by
  have z : ∀ {d : ℕ}, Atom.const (.n d) (word 0 0) ∈ w2Non → aV al s w cover c (.n d) = 0 := fun h =>
    (aGood_const (aggArgs_length _ _) (mem_non h)).trans word_zero
  have hz : w2Zs.map (aV al s w cover c) = List.replicate 8 0 := by
    show [aV al s w cover c (.n 74), aV al s w cover c (.n 74), aV al s w cover c (.n 74), aV al s w cover c (.n 74),
      aV al s w cover c (.n 74), aV al s w cover c (.n 75), aV al s w cover c (.n 76), aV al s w cover c (.n 77)] = _
    rw [z (d := 74) (by simp [w2Non]), z (d := 75) (by simp [w2Non]), z (d := 76) (by simp [w2Non]),
      z (d := 77) (by simp [w2Non])]
    rfl
  have hN := w2_nonce (al := al) (cover := cover) hl hc hn
  have hperm : ∀ k, (sqIter k (aS0 w)).perm = permOf (List.replicate 8 0 ++ (sqIter k (aS0 w)).cap) := fun k => by
    rw [Fs.perm, sqIter_pend k _ rfl, rateOf_nil]
  intro k
  induction k with
  | zero =>
    intro _
    have hin : (sqIns w2Zs w2Cap0 157 0).map (aV al s w cover c) = List.replicate 8 0 ++ (sqIter 0 (aS0 w)).cap := by
      have h86 : aV al s w cover c (.n 86) = cellsOfState (aN w) false 8 := hN 8
      have h87 : aV al s w cover c (.n 87) = cellsOfState (aN w) false 9 := hN 9
      have h88 : aV al s w cover c (.n 88) = cellsOfState (aN w) false 10 := hN 10
      have h89 : aV al s w cover c (.n 89) = cellsOfState (aN w) false 11 := hN 11
      have h90 : aV al s w cover c (.n 90) = cellsOfState (aN w) false 12 := hN 12
      have hc0 : w2Cap0.map (aV al s w cover c) = capOf (aN w) := by
        show [aV al s w cover c (.n 86), aV al s w cover c (.n 87), aV al s w cover c (.n 88),
          aV al s w cover c (.n 89), aV al s w cover c (.n 90)] = _
        rw [h86, h87, h88, h89, h90]
        rfl
      rw [sqIns, List.map_append, hz, hc0]
      rfl
    refine ⟨hin, fun q => ?_⟩
    have hk := aV_keccak (al := al) (s := s) (w := w) (cover := cover) (c := c)
      (mem_sq (show Atom.keccak (sqIns w2Zs w2Cap0 157 0) (sqOuts 157 0) false false ∈ w2Sq by
        simp only [w2Sq, List.mem_append, List.mem_flatMap, List.mem_range]
        exact Or.inr ⟨0, by norm_num, by simp⟩)) q (by simp [sqOuts])
    simp only [sqOuts, List.getElem_map, List.getElem_range] at hk
    rw [hk, hin, hperm, permOf]
  | succ k ih =>
    intro hk6
    obtain ⟨-, hout⟩ := ih (by omega)
    have hin : (sqIns w2Zs w2Cap0 157 (k + 1)).map (aV al s w cover c) =
        List.replicate 8 0 ++ (sqIter (k + 1) (aS0 w)).cap := by
      have hc1 : ((List.range 5).map fun i => V.n (157 + 13 * k + 8 + i)).map (aV al s w cover c) =
          capOf (sqIter k (aS0 w)).perm := by
        have e8 : aV al s w cover c (.n (157 + 13 * k + 8 + 0)) = cellsOfState (sqIter k (aS0 w)).perm false 8 := hout 8
        have e9 : aV al s w cover c (.n (157 + 13 * k + 8 + 1)) = cellsOfState (sqIter k (aS0 w)).perm false 9 := hout 9
        have e10 : aV al s w cover c (.n (157 + 13 * k + 8 + 2)) = cellsOfState (sqIter k (aS0 w)).perm false 10 :=
          hout 10
        have e11 : aV al s w cover c (.n (157 + 13 * k + 8 + 3)) = cellsOfState (sqIter k (aS0 w)).perm false 11 :=
          hout 11
        have e12 : aV al s w cover c (.n (157 + 13 * k + 8 + 4)) = cellsOfState (sqIter k (aS0 w)).perm false 12 :=
          hout 12
        show [aV al s w cover c (.n (157 + 13 * k + 8 + 0)), aV al s w cover c (.n (157 + 13 * k + 8 + 1)),
          aV al s w cover c (.n (157 + 13 * k + 8 + 2)), aV al s w cover c (.n (157 + 13 * k + 8 + 3)),
          aV al s w cover c (.n (157 + 13 * k + 8 + 4))] = _
        rw [e8, e9, e10, e11, e12]
        rfl
      rw [sqIter_succ, sqIns, List.map_append, hz, hc1]
      rfl
    refine ⟨hin, fun q => ?_⟩
    have hk := aV_keccak (al := al) (s := s) (w := w) (cover := cover) (c := c)
      (mem_sq (show Atom.keccak (sqIns w2Zs w2Cap0 157 (k + 1)) (sqOuts 157 (k + 1)) false false ∈ w2Sq by
        simp only [w2Sq, List.mem_append, List.mem_flatMap, List.mem_range]
        exact Or.inr ⟨k + 1, hk6, by simp⟩)) q (by simp [sqOuts])
    simp only [sqOuts, List.getElem_map, List.getElem_range] at hk
    rw [hk, hin, hperm, permOf]

/-- **The column challenges**: block `k`'s cell `0`. -/
theorem w2_col (hl : (aLists s w).map List.length = aBufs w.children.length) (hc : c < 2 ^ 62)
    (hn : w.children.length ≤ 16) {k : ℕ} (hk : k < 6) :
    aV al s w cover c (.n (157 + 13 * k)) = (aCols w).getD k 0 := by
  have := (w2_sq (al := al) (cover := cover) hl hc hn k hk).2 0
  rw [show 157 + 13 * k + (0 : Fin 13).val = 157 + 13 * k from rfl] at this
  rw [this, aCols, aggCols, squeezeN_getD splitLog _ k hk, Fs.squeeze, challengeOf_cells]
  rfl

/-- **The sponge after the squeezes**: the last block's capacity. -/
theorem w2_cap (hl : (aLists s w).map List.length = aBufs w.children.length) (hc : c < 2 ^ 62)
    (hn : w.children.length ≤ 16) :
    [aV al s w cover c (.n 230), aV al s w cover c (.n 231), aV al s w cover c (.n 232), aV al s w cover c (.n 233),
      aV al s w cover c (.n 234)] = (aggCols (aCs w) w.batchingHints.lambdaGrindNonce).2.cap := by
  have hout := (w2_sq (al := al) (cover := cover) hl hc hn 5 (by norm_num)).2
  have e0 : aV al s w cover c (.n 230) = cellsOfState (sqIter 5 (aS0 w)).perm false 8 := hout 8
  have e1 : aV al s w cover c (.n 231) = cellsOfState (sqIter 5 (aS0 w)).perm false 9 := hout 9
  have e2 : aV al s w cover c (.n 232) = cellsOfState (sqIter 5 (aS0 w)).perm false 10 := hout 10
  have e3 : aV al s w cover c (.n 233) = cellsOfState (sqIter 5 (aS0 w)).perm false 11 := hout 11
  have e4 : aV al s w cover c (.n 234) = cellsOfState (sqIter 5 (aS0 w)).perm false 12 := hout 12
  rw [e0, e1, e2, e3, e4, aggCols, squeezeN_snd, show splitLog = 5 + 1 from rfl, sqIter_succ]
  rfl

end

end
end LeanVM.Guest.Complete.Agg
