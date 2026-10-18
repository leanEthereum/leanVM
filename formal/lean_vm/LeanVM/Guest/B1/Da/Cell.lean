/-
  LeanVM.Guest.B1.Da.Cell

  B1 for `da_verify_cell` (G:3000-3014): one cell's 256 hinted symbols, their digest and their
  inner product with the membership vector's cell.
-/

module

public import LeanVM.Guest.B1.Digest.Statement

/-!
# `da_verify_cell`

`da_verify_cell(lvals)` hints 256 symbols, checks each pair in `K` (`assert_in_k`), packs pair `e`
into the canonical cell `sym[2e] + y·sym[2e+1]` (`pack64x2`), sums `lvals[k]·sym[k]` over the 256
words read at `lvals`, and hashes the 128 packed cells as 32 blocks: the BLAKE2s of the symbols'
2048 little-endian bytes.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **`da_verify_cell(lvals)`**: some 256 symbols and the 256 words at `lvals` give the digest of
the symbols' bytes and the inner product `∑ lvals[k]·sym[k]`. -/
def Meaning_da_verify_cell (rd : Reader) (args rets : List E) : Prop :=
  ∃ lv d0 d1 s, args = [lv] ∧ rets = [d0, d1, s] ∧ ∃ (syms : List K) (ws : List E),
    syms.length = 256 ∧ ws.length = 256 ∧ CellsAt rd lv ws ∧
    (d0, d1) = digestScalars (blake2sBytes (syms.flatMap kBytes)) ∧
    s = ∑ k ∈ Finset.range 256, ws.getD k 0 * ofK (syms.getD k 0)

/-! ## The template -/

/-- Pair `0`: the symbols `1, 2` checked and packed, the first two products. -/
def vcPair0 : List Atom :=
  [.assertInK (.n 1) (.n 2), .const (.n 257) wY, .mul (.n 258) (.n 257) (.n 2),
   .add (.n 259) (.n 1) (.n 258), .load (.n 260) (.n 0) 0, .mul (.n 261) (.n 260) (.n 1),
   .load (.n 262) (.n 0) 1, .mul (.n 263) (.n 262) (.n 2), .add (.n 264) (.n 261) (.n 263)]

/-- Pair `e ≥ 1`: the symbols `2e+1, 2e+2` checked and packed, both products added to the sum. -/
def vcPair (e : ℕ) : List Atom :=
  [.assertInK (.n (2 * e + 1)) (.n (2 * e + 2)), .const (.n (256 + 9 * e + 0)) wY,
   .mul (.n (256 + 9 * e + 1)) (.n (256 + 9 * e + 0)) (.n (2 * e + 2)),
   .add (.n (256 + 9 * e + 2)) (.n (2 * e + 1)) (.n (256 + 9 * e + 1)),
   .load (.n (256 + 9 * e + 3)) (.n 0) (2 * e),
   .mul (.n (256 + 9 * e + 4)) (.n (256 + 9 * e + 3)) (.n (2 * e + 1)),
   .add (.n (256 + 9 * e + 5)) (.n (255 + 9 * e)) (.n (256 + 9 * e + 4)),
   .load (.n (256 + 9 * e + 6)) (.n 0) (2 * e + 1),
   .mul (.n (256 + 9 * e + 7)) (.n (256 + 9 * e + 6)) (.n (2 * e + 2)),
   .add (.n (256 + 9 * e + 8)) (.n (256 + 9 * e + 5)) (.n (256 + 9 * e + 7))]

/-- The value of packed cell `e`. -/
def vcP (e : ℕ) : ℕ := if e = 0 then 259 else 258 + 9 * e

/-- Block `b` of the chain. -/
def vcBlk (b : ℕ) : List Atom :=
  [.const (.n (1410 + 3 * b)) (word (64 * (b + 1)) (if b + 1 = 32 then 4294967295 else 0) 0),
   .blake2s (.n (vcP (4 * b))) (.n (vcP (4 * b + 1))) (.n (vcP (4 * b + 2))) (.n (vcP (4 * b + 3)))
     (.n (1408 + 3 * b)) (.n (1409 + 3 * b)) (.n (1411 + 3 * b)) (.n (1412 + 3 * b))
     (.n (1410 + 3 * b))]

/-- `da_verify_cell`'s body. -/
def vcBody : List Stmt :=
  (([.hint (.witness "da_symbols" (.stack ((List.range 256).map fun i => .n (i + 1))))] ++ vcPair0 ++
    (List.range 127).flatMap (fun e => vcPair (e + 1)) ++
    [.const (.n 1408) (word 13503953895743350343 11912009169889063794 0),
     .const (.n 1409) (word 11170449402626986623 6620516960021240235 0)] ++
    (List.range 32).flatMap vcBlk ++
    [.copy (.n 1506) (.n 1504), .copy (.n 1507) (.n 1505), .copy (.n 1508) (.n 1407)] :
      List Atom).map .atom) ++
  [.ret [.n 1506, .n 1507, .n 1508]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem find_da_verify_cell : coreProgram.find? "da_verify_cell" =
    some ⟨"da_verify_cell", [.n 0], vcBody⟩ :=
  Program.find?_of_indexOf? (j := 25) (by decide +kernel) rfl

/-! ## The bytes -/

/-- Packed cell `e` of symbols `sy`. -/
def vcCell (sy : ℕ → K) (e : ℕ) : E := E.ofLimbs (sy (2 * e)) (sy (2 * e + 1)) 0

/-- The 32 blocks of packed cells. -/
def vcBlocks (sy : ℕ → K) (b : ℕ) : Fin 4 → E :=
  ![vcCell sy (4 * b), vcCell sy (4 * b + 1), vcCell sy (4 * b + 2), vcCell sy (4 * b + 3)]

/-- The chain's metadata cells. -/
def vcMd (b : ℕ) : E := metadataCell (64 * (b + 1)) (decide (b + 1 = 32))

theorem vc_bytes (sy : ℕ → K) :
    (List.range 32).flatMap (fun b => blockBytes (vcBlocks sy b)) =
      ((List.range 256).map sy).flatMap kBytes := by
  have e1 : (List.range 32).flatMap (fun b => blockBytes (vcBlocks sy b)) =
      (List.range (4 * 32)).flatMap (fun e => cellBytes (vcCell sy e)) := by
    rw [flatMap_range_mul 4]
    refine List.flatMap_congr fun b _ => ?_
    simp [blockBytes, vcBlocks, List.range_succ, List.append_assoc]
  rw [e1, List.flatMap_map, show 256 = 2 * 128 from rfl, flatMap_range_mul 2]
  refine List.flatMap_congr fun e _ => ?_
  simp [vcCell, cellBytes_ofLimbs, List.range_succ]

theorem vc_chain (sy : ℕ → K) :
    chainRun paramIv (vcBlocks sy) vcMd 32 = blake2sBytes (((List.range 256).map sy).flatMap kBytes) := by
  rw [← vc_bytes sy]
  refine chainRun_blocks (n := 31) (fun j _ r => ?_) (fun j hj => ?_) rfl
  · fin_cases r <;> exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
  · simp only [vcMd]
    congr 1
    simp only [decide_eq_false_iff_not]
    omega

/-! ## Soundness -/

theorem vcPair0_fwd {rd : Reader} {σ : Val} (h : ∀ a ∈ vcPair0, a.Holds rd σ) :
    IsInK (σ (.n 1)) ∧ IsInK (σ (.n 2)) ∧ σ (.n 259) = σ (.n 1) + wY * σ (.n 2) ∧
      LoadHolds rd (σ (.n 0)) 0 (σ (.n 260)) ∧ LoadHolds rd (σ (.n 0)) 1 (σ (.n 262)) ∧
      σ (.n 264) = σ (.n 260) * σ (.n 1) + σ (.n 262) * σ (.n 2) := by
  simp only [vcPair0, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true] at h
  obtain ⟨⟨k1, k2⟩, c0, m1, a2, l3, m4, l6, m7, a8⟩ := h
  exact ⟨k1, k2, by rw [a2, m1, c0], l3, l6, by rw [a8, m4, m7]⟩

theorem vcPair_fwd {rd : Reader} {σ : Val} {e : ℕ} (h : ∀ a ∈ vcPair e, a.Holds rd σ) :
    IsInK (σ (.n (2 * e + 1))) ∧ IsInK (σ (.n (2 * e + 2))) ∧
      σ (.n (256 + 9 * e + 2)) = σ (.n (2 * e + 1)) + wY * σ (.n (2 * e + 2)) ∧
      LoadHolds rd (σ (.n 0)) (2 * e) (σ (.n (256 + 9 * e + 3))) ∧
      LoadHolds rd (σ (.n 0)) (2 * e + 1) (σ (.n (256 + 9 * e + 6))) ∧
      σ (.n (256 + 9 * e + 8)) = σ (.n (255 + 9 * e)) + σ (.n (256 + 9 * e + 3)) * σ (.n (2 * e + 1)) +
        σ (.n (256 + 9 * e + 6)) * σ (.n (2 * e + 2)) := by
  simp only [vcPair, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true] at h
  obtain ⟨⟨k1, k2⟩, c0, m1, a2, l3, m4, a5, l6, m7, a8⟩ := h
  exact ⟨k1, k2, by rw [a2, m1, c0], l3, l6, by rw [a8, a5, m4, m7]⟩

theorem vcBlk_iff {rd : Reader} {σ : Val} {b : ℕ} :
    (∀ a ∈ vcBlk b, a.Holds rd σ) ↔
      σ (.n (1410 + 3 * b)) = word (64 * (b + 1)) (if b + 1 = 32 then 4294967295 else 0) 0 ∧
      CompressCells ![σ (.n (vcP (4 * b))), σ (.n (vcP (4 * b + 1))), σ (.n (vcP (4 * b + 2))),
        σ (.n (vcP (4 * b + 3)))] (σ (.n (1408 + 3 * b))) (σ (.n (1409 + 3 * b)))
        (σ (.n (1411 + 3 * b))) (σ (.n (1412 + 3 * b))) (σ (.n (1410 + 3 * b))) := by
  simp only [vcBlk, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true]

/-- The packed cells of `K` symbols. -/
theorem vc_pack {a b : E} (ha : IsInK a) (hb : IsInK b) : a + wY * b = E.ofLimbs (a.limb 0) (b.limb 0) 0 := by
  rw [wY_eq]; exact pack64x2_eq ha hb

theorem da_verify_cell_fwd {rd : Reader} {args rets : List E}
    (h : coreProgram.Rel rd "da_verify_cell" args rets) : Meaning_da_verify_cell rd args rets := by
  rw [rel_of_find find_da_verify_cell] at h
  obtain ⟨σ, hp, hb⟩ := h
  simp only [vcBody, holdsList_atoms, holdsList_ret, List.forall_mem_append, forall_mem_flatMap_range,
    List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true, true_and, List.map_cons,
    List.map_nil] at hb hp
  obtain ⟨⟨⟨⟨⟨hP0, hPs⟩, h1408, h1409⟩, hblk⟩, h1506, h1507, h1508⟩, hr⟩ := hb
  set lv := σ (.n 0) with hlv
  let x : ℕ → E := fun k => σ (.n (k + 1))
  obtain ⟨k0, k1, p0, l0, l1, s0⟩ := vcPair0_fwd hP0
  -- every pair, uniformly
  have hP : ∀ e < 128, IsInK (x (2 * e)) ∧ IsInK (x (2 * e + 1)) ∧
      σ (.n (vcP e)) = x (2 * e) + wY * x (2 * e + 1) ∧
      (∃ v, LoadHolds rd lv (2 * e) v) ∧ (∃ v, LoadHolds rd lv (2 * e + 1) v) := by
    intro e he
    rcases Nat.eq_zero_or_pos e with rfl | hpos
    · exact ⟨k0, k1, p0, ⟨_, l0⟩, ⟨_, l1⟩⟩
    · obtain ⟨i, rfl⟩ : ∃ i, e = i + 1 := ⟨e - 1, by omega⟩
      obtain ⟨a, b, c, d, f, -⟩ := vcPair_fwd (hPs i (by omega))
      have e1 : vcP (i + 1) = 256 + 9 * (i + 1) + 2 := by unfold vcP; rw [ite_neg' (by omega)]; omega
      refine ⟨a, b, by rw [e1]; exact c, ⟨_, d⟩, ⟨_, f⟩⟩
  have hL : ∀ k < 256, ∃ v, LoadHolds rd lv k v := by
    intro k hk
    obtain ⟨e, r, hr2, rfl⟩ : ∃ e r, r < 2 ∧ k = 2 * e + r := ⟨k / 2, k % 2, by omega, by omega⟩
    interval_cases r
    · exact (hP e (by omega)).2.2.2.1
    · exact (hP e (by omega)).2.2.2.2
  -- the inner product
  have hS : ∀ e < 128, σ (.n (264 + 9 * e)) =
      ∑ k ∈ Finset.range (2 * e + 2), cellAt rd lv k * x k := by
    intro e he
    induction e with
    | zero =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      rw [s0, cellAt_of_load l0, cellAt_of_load l1]
    | succ i ih =>
      obtain ⟨-, -, -, d, f, g⟩ := vcPair_fwd (hPs i (by omega))
      rw [show 264 + 9 * (i + 1) = 256 + 9 * (i + 1) + 8 by omega, g,
        show 255 + 9 * (i + 1) = 264 + 9 * i by omega, ih (by omega),
        show 2 * (i + 1) + 2 = 2 * i + 2 + 1 + 1 by omega, Finset.sum_range_succ _ (2 * i + 2 + 1),
        Finset.sum_range_succ _ (2 * i + 2), ← cellAt_of_load d, ← cellAt_of_load f]
      rfl
  -- the chain
  let sy : ℕ → K := fun k => (x k).limb 0
  have hx : ∀ k < 256, x k = ofK (sy k) := fun k hk => by
    obtain ⟨e, r, hr2, rfl⟩ : ∃ e r, r < 2 ∧ k = 2 * e + r := ⟨k / 2, k % 2, by omega, by omega⟩
    interval_cases r
    · exact eq_ofK_limb (hP e (by omega)).1
    · exact eq_ofK_limb (hP e (by omega)).2.1
  have hcell : ∀ e < 128, σ (.n (vcP e)) = vcCell sy e := fun e he => by
    rw [(hP e he).2.2.1, vc_pack (hP e he).1 (hP e he).2.1]; rfl
  have hch := chain_eq_chainRun (n := 32) (h := paramIv)
    (blocks := fun b => ![σ (.n (vcP (4 * b))), σ (.n (vcP (4 * b + 1))), σ (.n (vcP (4 * b + 2))),
      σ (.n (vcP (4 * b + 3)))])
    (md := fun b => σ (.n (1410 + 3 * b))) (st := fun b => (σ (.n (1408 + 3 * b)), σ (.n (1409 + 3 * b))))
    (by simp only [Nat.mul_zero, Nat.add_zero]; rw [h1408, h1409, iv0_word, iv1_word])
    (fun j hj => by
      simp only [show 1408 + 3 * (j + 1) = 1411 + 3 * j by omega,
        show 1409 + 3 * (j + 1) = 1412 + 3 * j by omega]
      exact (vcBlk_iff.mp (hblk j hj)).2) 32 le_rfl
  rw [chainRun_congr (b' := vcBlocks sy) (md' := vcMd) 32
    (fun b hb => by
      simp only [vcBlocks]
      rw [hcell _ (by omega), hcell _ (by omega), hcell _ (by omega), hcell _ (by omega)])
    (fun b hb => by rw [(vcBlk_iff.mp (hblk b hb)).1, word_metadata]; rfl), vc_chain] at hch
  refine ⟨lv, σ (.n 1506), σ (.n 1507), σ (.n 1508), hp.symm, hr.symm, (List.range 256).map sy,
    (List.range 256).map (cellAt rd lv), by simp, by simp, fun k hk => ?_, ?_, ?_⟩
  · simp only [List.length_map, List.length_range] at hk
    simp only [List.getElem_map, List.getElem_range]
    exact load_cellAt (hL k hk).choose_spec
  · rw [h1506, h1507]; exact hch
  · rw [h1508, show 1407 = 264 + 9 * 127 from rfl, hS 127 (by omega)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [List.getD_eq_getElem _ _ (by simpa using hk'), List.getD_eq_getElem _ _ (by simpa using hk')]
    simp only [List.getElem_map, List.getElem_range]
    rw [hx k hk']

/-! ## Completeness -/

section
variable (lv : E) (x w : ℕ → E) (sy : ℕ → K)

/-- The inner product's partial sum after pair `e`. -/
def vcS (e : ℕ) : E := ∑ k ∈ Finset.range (2 * e + 2), w k * x k

/-- The values of pair `e ≥ 1`, in `vcPair`'s order. -/
def vcPv (e : ℕ) : List E :=
  [wY, wY * x (2 * e + 1), x (2 * e) + wY * x (2 * e + 1), w (2 * e), w (2 * e) * x (2 * e),
   vcS x w (e - 1) + w (2 * e) * x (2 * e), w (2 * e + 1), w (2 * e + 1) * x (2 * e + 1), vcS x w e]

/-- The chain's state after `b` blocks. -/
def vcSt (b : ℕ) : E × E := digestScalars (chainRun paramIv (vcBlocks sy) vcMd b)

/-- The honest values of `da_verify_cell`. -/
def vcVals (k : ℕ) : E :=
  if k = 0 then lv else
  if k < 257 then x (k - 1) else
  if k < 265 then [wY, wY * x 1, x 0 + wY * x 1, w 0, w 0 * x 0, w 1, w 1 * x 1, vcS x w 0].getD (k - 257) 0
  else
  if k < 1408 then (vcPv x w ((k - 256) / 9)).getD ((k - 256) % 9) 0 else
  if k < 1506 then [(vcSt sy ((k - 1408) / 3)).1, (vcSt sy ((k - 1408) / 3)).2,
    vcMd ((k - 1408) / 3)].getD ((k - 1408) % 3) 0 else
  [(vcSt sy 32).1, (vcSt sy 32).2, vcS x w 127].getD (k - 1506) 0

theorem vcVals_sym {k : ℕ} (hk : k < 256) : vcVals lv x w sy (k + 1) = x k := by
  unfold vcVals; rw [ite_neg' (by omega), ite_pos' (by omega), Nat.add_sub_cancel]

theorem vcVals_p0 {r : ℕ} (hr : r < 8) : vcVals lv x w sy (257 + r) =
    [wY, wY * x 1, x 0 + wY * x 1, w 0, w 0 * x 0, w 1, w 1 * x 1, vcS x w 0].getD r 0 := by
  unfold vcVals
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega), Nat.add_sub_cancel_left]

theorem vcVals_p {e r : ℕ} (he : 1 ≤ e) (he' : e < 128) (hr : r < 9) :
    vcVals lv x w sy (256 + 9 * e + r) = (vcPv x w e).getD r 0 := by
  unfold vcVals
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
    show (256 + 9 * e + r - 256) / 9 = e by omega, show (256 + 9 * e + r - 256) % 9 = r by omega]

theorem vcVals_st {b r : ℕ} (hr : r < 3) (hb : 1408 + 3 * b + r < 1506) :
    vcVals lv x w sy (1408 + 3 * b + r) = [(vcSt sy b).1, (vcSt sy b).2, vcMd b].getD r 0 := by
  unfold vcVals
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    ite_pos' hb, show (1408 + 3 * b + r - 1408) / 3 = b by omega,
    show (1408 + 3 * b + r - 1408) % 3 = r by omega]

theorem vcVals_end {r : ℕ} (hr : r < 3) :
    vcVals lv x w sy (1506 + r) = [(vcSt sy 32).1, (vcSt sy 32).2, vcS x w 127].getD r 0 := by
  unfold vcVals
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    ite_neg' (by omega), Nat.add_sub_cancel_left]

theorem vcS_succ (i : ℕ) : vcS x w (i + 1) =
    vcS x w i + w (2 * (i + 1)) * x (2 * (i + 1)) + w (2 * (i + 1) + 1) * x (2 * (i + 1) + 1) := by
  unfold vcS
  rw [show 2 * (i + 1) + 2 = 2 * i + 2 + 1 + 1 by omega, Finset.sum_range_succ _ (2 * i + 2 + 1),
    Finset.sum_range_succ _ (2 * i + 2)]
  rfl

end

theorem vcPair_bwd {rd : Reader} {σ : Val} {e : ℕ} {lv : E} {x w : ℕ → E}
    (hv : ∀ r < 9, σ (.n (256 + 9 * e + r)) = (vcPv x w e).getD r 0)
    (hx0 : σ (.n (2 * e + 1)) = x (2 * e)) (hx1 : σ (.n (2 * e + 2)) = x (2 * e + 1))
    (hprev : σ (.n (255 + 9 * e)) = vcS x w (e - 1)) (h0 : σ (.n 0) = lv)
    (k0 : IsInK (x (2 * e))) (k1 : IsInK (x (2 * e + 1)))
    (l0 : LoadHolds rd lv (2 * e) (w (2 * e))) (l1 : LoadHolds rd lv (2 * e + 1) (w (2 * e + 1)))
    (hS : vcS x w e = vcS x w (e - 1) + w (2 * e) * x (2 * e) + w (2 * e + 1) * x (2 * e + 1)) :
    ∀ a ∈ vcPair e, a.Holds rd σ := by
  simp only [vcPair, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true, h0, hx0, hx1,
    hprev, hv _ (by norm_num : (0 : ℕ) < 9), hv _ (by norm_num : (1 : ℕ) < 9),
    hv _ (by norm_num : (2 : ℕ) < 9), hv _ (by norm_num : (3 : ℕ) < 9),
    hv _ (by norm_num : (4 : ℕ) < 9), hv _ (by norm_num : (5 : ℕ) < 9),
    hv _ (by norm_num : (6 : ℕ) < 9), hv _ (by norm_num : (7 : ℕ) < 9),
    hv _ (by norm_num : (8 : ℕ) < 9), vcPv, List.getD_cons_succ, List.getD_cons_zero, true_and]
  exact ⟨⟨k0, k1⟩, l0, l1, hS⟩

theorem da_verify_cell_bwd {rd : Reader} {args rets : List E} (h : Meaning_da_verify_cell rd args rets) :
    coreProgram.Rel rd "da_verify_cell" args rets := by
  obtain ⟨lv, d0, d1, s, rfl, rfl, syms, ws, hsl, hwl, hws, hd, hs⟩ := h
  let sy : ℕ → K := fun k => syms.getD k 0
  let x : ℕ → E := fun k => ofK (sy k)
  let w : ℕ → E := fun k => ws.getD k 0
  have hload : ∀ k < 256, LoadHolds rd lv k (w k) := fun k hk => by
    have := hws k (by omega)
    rwa [← List.getD_eq_getElem _ 0] at this
  have hsyms : (List.range 256).map sy = syms := by
    rw [← hsl]
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_map, List.getElem_range, sy]
    exact List.getD_eq_getElem _ _ h2
  have hst : vcSt sy 32 = (d0, d1) := by
    rw [vcSt, vc_chain, hsyms, hd]
  have hsum : vcS x w 127 = s := by rw [hs]; rfl
  rw [rel_of_find find_da_verify_cell]
  let σ : Val := fun v => vcVals lv x w sy v.idx
  have hσ : ∀ k, σ (.n k) = vcVals lv x w sy k := fun _ => rfl
  have hsym : ∀ k < 256, σ (.n (k + 1)) = x k := fun k hk => vcVals_sym lv x w sy hk
  have hcell : ∀ e < 128, σ (.n (vcP e)) = vcCell sy e := by
    intro e he
    have hp : σ (.n (vcP e)) = x (2 * e) + wY * x (2 * e + 1) := by
      rcases Nat.eq_zero_or_pos e with rfl | hpos
      · exact vcVals_p0 lv x w sy (r := 2) (by omega)
      · rw [show vcP e = 256 + 9 * e + 2 by unfold vcP; rw [ite_neg' (by omega)]; omega]
        exact vcVals_p lv x w sy (r := 2) hpos he (by omega)
    rw [hp, vc_pack (ofK_isInK _) (ofK_isInK _)]
    simp [vcCell]
  refine ⟨σ, rfl, ?_⟩
  simp only [vcBody, holdsList_atoms, holdsList_ret, List.forall_mem_append, forall_mem_flatMap_range,
    List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true, true_and, List.map_cons,
    List.map_nil]
  refine ⟨⟨⟨⟨⟨?_, fun i hi => ?_⟩, ?_, ?_⟩, fun b hb => ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · -- pair 0
    have hv : ∀ r < 8, σ (.n (257 + r)) =
        [wY, wY * x 1, x 0 + wY * x 1, w 0, w 0 * x 0, w 1, w 1 * x 1, vcS x w 0].getD r 0 :=
      fun r hr => vcVals_p0 lv x w sy hr
    have h1 : σ (.n 1) = x 0 := hsym 0 (by omega)
    have h2 : σ (.n 2) = x 1 := hsym 1 (by omega)
    have h0 : σ (.n 0) = lv := rfl
    simp only [vcPair0, List.forall_mem_cons, forall_mem_nil_iff, and_true, h0, h1, h2,
      hv 0 (by omega), hv 1 (by omega), hv 2 (by omega), hv 3 (by omega), hv 4 (by omega),
      hv 5 (by omega), hv 6 (by omega), hv 7 (by omega), List.getD_cons_succ, List.getD_cons_zero,
      true_and]
    refine ⟨⟨ofK_isInK _, ofK_isInK _⟩, hload 0 (by omega), hload 1 (by omega), ?_⟩
    simp [vcS, Finset.sum_range_succ]
  · -- pair i + 1
    refine vcPair_bwd (e := i + 1) (lv := lv) (fun r hr => vcVals_p lv x w sy (by omega) (by omega) hr)
      (hsym _ (by omega)) (hsym _ (by omega)) ?_ rfl (ofK_isInK _) (ofK_isInK _)
      (hload _ (by omega)) (hload _ (by omega)) (vcS_succ x w i)
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact vcVals_p0 lv x w sy (r := 7) (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [show 255 + 9 * (j + 1 + 1) = 256 + 9 * (j + 1) + 8 by omega]
      exact vcVals_p lv x w sy (by omega) (by omega) (by omega)
  · show vcVals lv x w sy (1408 + 3 * 0 + 0) = _
    rw [vcVals_st lv x w sy (b := 0) (r := 0) (by omega) (by omega), iv0_word]; rfl
  · show vcVals lv x w sy (1408 + 3 * 0 + 1) = _
    rw [vcVals_st lv x w sy (b := 0) (r := 1) (by omega) (by omega), iv1_word]; rfl
  · refine vcBlk_iff.mpr ⟨?_, ?_⟩
    · rw [hσ, show 1410 + 3 * b = 1408 + 3 * b + 2 by omega,
        vcVals_st lv x w sy (b := b) (r := 2) (by omega) (by omega), word_metadata]; rfl
    · rw [hcell _ (by omega), hcell _ (by omega), hcell _ (by omega), hcell _ (by omega)]
      simp only [hσ]
      have e0 := vcVals_st lv x w sy (b := b) (r := 0) (by omega) (by omega)
      have e1 := vcVals_st lv x w sy (b := b) (r := 1) (by omega) (by omega)
      have e2 := vcVals_st lv x w sy (b := b) (r := 2) (by omega) (by omega)
      have e3 := vcVals_st lv x w sy (b := b + 1) (r := 0) (by omega) (by omega)
      have e4 := vcVals_st lv x w sy (b := b + 1) (r := 1) (by omega) (by omega)
      rw [Nat.add_zero, show 1408 + 3 * (b + 1) = 1411 + 3 * b by omega] at e3
      rw [show 1408 + 3 * (b + 1) + 1 = 1412 + 3 * b by omega] at e4
      rw [Nat.add_zero] at e0
      rw [show 1408 + 3 * b + 1 = 1409 + 3 * b by omega] at e1
      rw [show 1408 + 3 * b + 2 = 1410 + 3 * b by omega] at e2
      rw [e0, e1, e2, e3, e4]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      refine (compressCells_chainRun (h := paramIv) (blocks := vcBlocks sy) (md := vcMd) (i := b)
        (fun r => ?_) (isCanonical128_metadataCell _ _)).mpr rfl
      fin_cases r <;> exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
  · show vcVals lv x w sy (1506 + 0) = vcVals lv x w sy (1408 + 3 * 32 + 0)
    rw [vcVals_end lv x w sy (r := 0) (by omega), vcVals_st lv x w sy (b := 32) (r := 0) (by omega) (by omega)]
    rfl
  · show vcVals lv x w sy (1506 + 1) = vcVals lv x w sy (1408 + 3 * 32 + 1)
    rw [vcVals_end lv x w sy (r := 1) (by omega), vcVals_st lv x w sy (b := 32) (r := 1) (by omega) (by omega)]
    rfl
  · show vcVals lv x w sy (1506 + 2) = vcVals lv x w sy (256 + 9 * 127 + 8)
    rw [vcVals_end lv x w sy (r := 2) (by omega), vcVals_p lv x w sy (e := 127) (r := 8) (by omega) (by omega)
      (by omega)]
    rfl
  · show [vcVals lv x w sy (1506 + 0), vcVals lv x w sy (1506 + 1), vcVals lv x w sy (1506 + 2)] = _
    rw [vcVals_end lv x w sy (r := 0) (by omega), vcVals_end lv x w sy (r := 1) (by omega),
      vcVals_end lv x w sy (r := 2) (by omega)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, hst, hsum]

/-- **`da_verify_cell`**, exactly. -/
theorem da_verify_cell_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "da_verify_cell" args rets ↔ Meaning_da_verify_cell rd args rets :=
  ⟨da_verify_cell_fwd, da_verify_cell_bwd⟩

end
end LeanVM.Guest.B1.Digest

namespace LeanVM.Guest.B1
export Digest (Meaning_da_verify_cell da_verify_cell_iff)
end LeanVM.Guest.B1
