/-
  LeanVM.Guest.B1.Da.Vector

  B1 for `da_vector_cell__L0` and `__L1` (G:3045-3076): one cell of the membership vector, its
  256 hinted weights absorbed into the running vector hash.
-/

module

public import LeanVM.Guest.B1.Da.VectorT

/-!
# `da_vector_cell__L{final}`

`da_vector_cell(xb, h0, h1, counters)` hints 256 weights, splits each pair into its six limbs and
packs them into three canonical cells (`sdPair`'s gadget, so pair `s, t` hashes as
`eBytes s ++ eBytes t`), and continues the chain `(h0, h1)` over the 384 cells, 96 blocks in three
windows of 32. Window `w`'s blocks take the counter word `counters[xb³·g^w]` plus their offset,
its last block the next counter word (plus `MD_FINAL` at the last block of `__L1`). It returns the
chain's state and the weights' frame address. The counter words are whatever memory holds at
`counters·xb³`; `da_verify` supplies them.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- Packed cell `q` of the weights `ws`: limbs `3q, 3q+1` of their limb sequence. -/
def vxCell (ws : ℕ → E) (q : ℕ) : E :=
  if q % 3 = 0 then E.ofLimbs ((ws (2 * (q / 3))).limb 0) ((ws (2 * (q / 3))).limb 1) 0
  else if q % 3 = 1 then E.ofLimbs ((ws (2 * (q / 3))).limb 2) ((ws (2 * (q / 3) + 1)).limb 0) 0
  else E.ofLimbs ((ws (2 * (q / 3) + 1)).limb 1) ((ws (2 * (q / 3) + 1)).limb 2) 0

/-- Block `j` of the packed cells. -/
def vxBlocks (ws : ℕ → E) (j : ℕ) : Fin 4 → E :=
  ![vxCell ws (4 * j), vxCell ws (4 * j + 1), vxCell ws (4 * j + 2), vxCell ws (4 * j + 3)]

/-- Block `j`'s metadata cell, from the four counter words `cv`. -/
def vxMd (final : Bool) (cv : ℕ → E) (j : ℕ) : E :=
  if j % 32 = 31 then (if final = true ∧ j = 95 then cv 3 + mdF else cv (j / 32 + 1))
  else cv (j / 32) + word (64 * (j % 32 + 1)) 0 0

/-- `p` is a frame address whose run holds `ws`: what memory holds there is `ws`. -/
def FrameRun (rd : Reader) (p : E) (ws : List E) : Prop :=
  IsInK p ∧ ∀ k < ws.length, ∀ v, rd (p.limb 0 * Parameters.gpow k) = some v → v = ws.getD k 0

/-- **`da_vector_cell__L{final}(xb, h0, h1, counters)`**: some 256 weights, the four counter
words at `counters·xb³`, the chain from `(h0, h1)` over the weights' 96 blocks ending in
`(o0, o1)`, and `wp` the weights' frame address. -/
def Meaning_da_vector_cell (final : Bool) (rd : Reader) (args rets : List E) : Prop :=
  ∃ xb h0 h1 ctr o0 o1 wp, args = [xb, h0, h1, ctr] ∧ rets = [o0, o1, wp] ∧
    ∃ ws cv : List E, ws.length = 256 ∧ cv.length = 4 ∧ CellsAt rd (ctr * (xb * xb * xb)) cv ∧
      ChainCells (h0, h1) (vxBlocks (ws.getD · 0)) (vxMd final (cv.getD · 0)) 96 (o0, o1) ∧
      FrameRun rd wp ws

/-! ## Soundness -/

theorem vxPair_fwd {rd : Reader} {σ : Val} {p : ℕ} (h : ∀ a ∈ vxPair p, a.Holds rd σ) :
    σ (vxv p 8) = E.ofLimbs ((σ (.n (2 * p + 4))).limb 0) ((σ (.n (2 * p + 4))).limb 1) 0 ∧
      σ (vxv p 17) = E.ofLimbs ((σ (.n (2 * p + 4))).limb 2) ((σ (.n (2 * p + 1 + 4))).limb 0) 0 ∧
      σ (vxv p 26) = E.ofLimbs ((σ (.n (2 * p + 1 + 4))).limb 1) ((σ (.n (2 * p + 1 + 4))).limb 2) 0 := by
  simp only [vxPair, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true] at h
  obtain ⟨-, -, k1, c6, m7, a8, a9, c10, m11, a12, c13, m14, k2, c15, m16, a17, a18, c19,
    m20, a21, c22, m23, k3, c24, m25, a26⟩ := h
  have e14 : σ (vxv p 14) = ((σ (.n (2 * p + 4)) + σ (vxv p 2)) * wYi + σ (vxv p 3)) * wYi := by
    rw [m14, a12, m11, a9, c10, c13]
  have e23 : σ (vxv p 23) = ((σ (.n (2 * p + 1 + 4)) + σ (vxv p 4)) * wYi + σ (vxv p 5)) * wYi := by
    rw [m23, a21, m20, a18, c19, c22]
  rw [e14] at k2
  rw [e23] at k3
  obtain ⟨hs0, hs1, ht0, ht1⟩ := pair_spec k1 k2 k3
  obtain ⟨p1, p2, p3⟩ := pair_cells (σ (.n (2 * p + 4))) (σ (.n (2 * p + 1 + 4)))
  refine ⟨?_, ?_, ?_⟩
  · rw [a8, m7, c6, hs0, hs1, p1]
  · rw [a17, m16, c15, e14, hs0, hs1, ht0, p2]
  · rw [a26, m25, c24, e23, ht0, ht1, p3]

theorem vxBlk_fwd {rd : Reader} {σ : Val} {final : Bool} {j : ℕ}
    (h : ∀ a ∈ vxBlk final j, a.Holds rd σ) :
    CompressCells ![σ (.n (vxQ (4 * j))), σ (.n (vxQ (4 * j + 1))), σ (.n (vxQ (4 * j + 2))),
        σ (.n (vxQ (4 * j + 3)))] (σ (.n (vxSt final j))) (σ (.n (vxSt final j + 1)))
        (σ (.n (vxSt final (j + 1)))) (σ (.n (vxSt final (j + 1) + 1))) (σ (.n (vxMdI final j))) ∧
      (j % 32 ≠ 31 → σ (.n (vxMdI final j)) = σ (.n (vxBase (j / 32))) + word (64 * (j % 32 + 1)) 0 0) ∧
      (j % 32 = 31 → ¬(final = true ∧ j = 95) → vxMdI final j = vxEnd (j / 32)) ∧
      (final = true ∧ j = 95 → σ (.n (vxMdI final j)) = σ (.n 3733) + mdF) := by
  by_cases h1 : j % 32 = 31
  · have hm : vxMdI final j = if final = true ∧ j = 95 then 3859 else vxEnd (j / 32) := by
      unfold vxMdI; rw [ite_pos' h1]
    by_cases h2 : final = true ∧ j = 95
    · rw [vxBlk, ite_pos' h1, ite_pos' h2] at h
      simp only [List.cons_append, List.nil_append, List.forall_mem_cons, Atom.Holds,
        forall_mem_nil_iff, and_true] at h
      obtain ⟨c, a, b⟩ := h
      exact ⟨b, fun h' => absurd h1 h', fun _ h' => absurd h2 h', fun _ => by rw [hm, ite_pos' h2, a, c]⟩
    · rw [vxBlk, ite_pos' h1, ite_neg' h2] at h
      simp only [List.nil_append, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff,
        and_true] at h
      exact ⟨h, fun h' => absurd h1 h', fun _ _ => by rw [hm, ite_neg' h2], fun h' => absurd h' h2⟩
  · rw [vxBlk, ite_neg' h1] at h
    simp only [List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true] at h
    obtain ⟨c, a, b⟩ := h
    have hm : vxMdI final j = vxK (j / 32) + 4 * (j % 32) + 1 := by unfold vxMdI; rw [ite_neg' h1]
    refine ⟨b, fun _ => by rw [hm, a, c], fun h' => absurd h' h1, fun h' => absurd (by omega) h1⟩

set_option maxRecDepth 4000 in
theorem word4 : word 4 0 0 = gen ^ 2 := by
  rw [gen_pow_eq_eOfNat (by omega), word_eq_eOfNat]; rfl

theorem vxCell_of_pair {σ : Val} {p : ℕ}
    (h : σ (vxv p 8) = E.ofLimbs ((σ (.n (2 * p + 4))).limb 0) ((σ (.n (2 * p + 4))).limb 1) 0 ∧
      σ (vxv p 17) = E.ofLimbs ((σ (.n (2 * p + 4))).limb 2) ((σ (.n (2 * p + 1 + 4))).limb 0) 0 ∧
      σ (vxv p 26) = E.ofLimbs ((σ (.n (2 * p + 1 + 4))).limb 1) ((σ (.n (2 * p + 1 + 4))).limb 2) 0)
    (r : ℕ) (hr : r < 3) : σ (.n (vxQ (3 * p + r))) = vxCell (fun k => σ (.n (k + 4))) (3 * p + r) := by
  have e1 : (3 * p + r) / 3 = p := by omega
  have e2 : (3 * p + r) % 3 = r := by omega
  unfold vxQ vxCell
  rw [e1, e2]
  interval_cases r
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem vxCell_congr {f g : ℕ → E} (h : ∀ k < 256, f k = g k) {q : ℕ} (hq : q < 384) :
    vxCell f q = vxCell g q := by
  unfold vxCell; rw [h (2 * (q / 3)) (by omega), h (2 * (q / 3) + 1) (by omega)]

theorem vxBlocks_congr {f g : ℕ → E} (h : ∀ k < 256, f k = g k) {j : ℕ} (hj : j < 96) :
    vxBlocks f j = vxBlocks g j := by
  simp only [vxBlocks]
  rw [vxCell_congr h (q := 4 * j) (by omega), vxCell_congr h (q := 4 * j + 1) (by omega),
    vxCell_congr h (q := 4 * j + 2) (by omega), vxCell_congr h (q := 4 * j + 3) (by omega)]

theorem getD_map_range (f : ℕ → E) {n k : ℕ} (hk : k < n) : ((List.range n).map f).getD k 0 = f k := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]; simp

set_option maxRecDepth 10000 in
theorem da_vector_cell_fwd {final : Bool} {rd : Reader} {args rets : List E}
    (h : coreProgram.Rel rd (vxName final) args rets) : Meaning_da_vector_cell final rd args rets := by
  rw [rel_of_find (find_vx final)] at h
  obtain ⟨σ, hp, hb⟩ := h
  simp only [vxBody, vxAtoms, holdsList_atoms, holdsList_ret, List.forall_mem_append, forall_mem_flatMap_range,
    List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true, true_and, List.map_cons,
    List.map_nil] at hb hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hP, c60, c61⟩, hpre0⟩, hb0⟩, hpre1⟩, hb1⟩, hpre2⟩, hb2⟩, ⟨hfk, hfr⟩, o1, o2, o3⟩, hr⟩ := hb
  let wsf : ℕ → E := fun k => σ (.n (k + 4))
  let cvl : List E := [σ (.n 3465), σ (.n 3469), σ (.n 3601), σ (.n 3733)]
  have hB : ∀ j < 96, ∀ a ∈ vxBlk final j, a.Holds rd σ := by
    intro j hj
    rcases (show j < 32 ∨ (32 ≤ j ∧ j < 64) ∨ 64 ≤ j by omega) with h | ⟨h1, h2⟩ | h
    · exact hb0 j h
    · have := hb1 (j - 32) (by omega); rwa [show 32 + (j - 32) = j by omega] at this
    · have := hb2 (j - 64) (by omega); rwa [show 64 + (j - 64) = j by omega] at this
  have hcell : ∀ q < 384, σ (.n (vxQ q)) = vxCell wsf q := fun q hq => by
    have := vxCell_of_pair (σ := σ) (p := q / 3) (vxPair_fwd (hP (q / 3) (by omega)))
      (q % 3) (by omega)
    rwa [show 3 * (q / 3) + q % 3 = q by omega] at this
  -- the counter words
  simp only [vxPre0, List.forall_mem_cons, forall_mem_nil_iff, and_true] at hpre0
  obtain ⟨m62, m63, m64, l65, m66, m67, m68, l69⟩ := hpre0
  simp only [vxPre, vxK, List.forall_mem_cons, forall_mem_nil_iff, and_true,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow] at hpre1 hpre2
  obtain ⟨n1, n2, n3, n4, n5, l1⟩ := hpre1
  obtain ⟨q1, q2, q3, q4, q5, l2⟩ := hpre2
  have hcv : CellsAt rd (σ (.n 3) * (σ (.n 0) * σ (.n 0) * σ (.n 0))) cvl := by
    intro k hk
    simp only [cvl, List.length_cons, List.length_nil] at hk
    interval_cases k
    · rw [m64, m63, m62] at l65; exact l65
    · rw [m68, m67, m66] at l69; exact l69
    · rw [n5, n4, n3, n2, n1, word_gen, ← pow_one gen, ← mul_assoc, loadHolds_mul_gen_pow] at l1
      exact l1
    · rw [q5, q4, q3, q2, q1, word4, ← mul_assoc, loadHolds_mul_gen_pow] at l2
      exact l2
  -- the chain
  have hbase : ∀ w < 3, σ (.n (vxBase w)) = cvl.getD w 0 := fun w hw => by
    interval_cases w <;> rfl
  have hend : ∀ w < 3, σ (.n (vxEnd w)) = cvl.getD (w + 1) 0 := fun w hw => by
    interval_cases w <;> rfl
  have hch := chainCells_of_steps (n := 96)
    (st := fun i => (σ (.n (vxSt final i)), σ (.n (vxSt final i + 1))))
    (blocks := fun j => ![σ (.n (vxQ (4 * j))), σ (.n (vxQ (4 * j + 1))), σ (.n (vxQ (4 * j + 2))),
      σ (.n (vxQ (4 * j + 3)))]) (md := fun j => σ (.n (vxMdI final j)))
    (fun j hj => (vxBlk_fwd (hB j hj)).1)
  rw [chainCells_congr (b' := vxBlocks (((List.range 256).map wsf).getD · 0))
    (md' := vxMd final (cvl.getD · 0))
    (fun j hj => by
      rw [← vxBlocks_congr (fun k hk => (getD_map_range wsf hk).symm) hj]
      simp only [vxBlocks]
      rw [hcell (4 * j) (by omega), hcell (4 * j + 1) (by omega), hcell (4 * j + 2) (by omega),
        hcell (4 * j + 3) (by omega)])
    (fun j hj => by
      obtain ⟨-, e1, e2, e3⟩ := vxBlk_fwd (hB j hj)
      unfold vxMd
      by_cases h1 : j % 32 = 31
      · rw [ite_pos' h1]
        by_cases h2 : final = true ∧ j = 95
        · rw [ite_pos' h2, e3 h2]; rfl
        · rw [ite_neg' h2]; show σ (.n (vxMdI final j)) = _
          rw [e2 h1 h2, hend (j / 32) (by omega)]
      · rw [ite_neg' h1, e1 h1, hbase (j / 32) (by omega)])] at hch
  have hs0 : vxSt final 0 = 3460 := rfl
  simp only [hs0] at hch
  rw [c60, c61] at hch
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n (vxSt final 96)), σ (.n (vxSt final 96 + 1)),
    σ (.n (vxF final)), hp.symm, ?_, (List.range 256).map wsf, cvl, by simp, rfl, hcv, hch, hfk,
    fun k hk v hv => ?_⟩
  · rw [← hr, o1, o2, o3]
  · simp only [List.length_map, List.length_range] at hk
    rw [hfr k (by simpa using hk) v hv, getD_map_range wsf hk]
    simp only [List.getElem_map, List.getElem_range]
    rfl

/-! ## Completeness -/

section
variable (final : Bool) (xb h0 h1 ctr wp : E) (wsf cvf : ℕ → E) (st : ℕ → E × E) (md : ℕ → E)

/-- The values of block `b < 31` of window `w`. -/
def vxBv (w b r : ℕ) : E :=
  [word (64 * (b + 1)) 0 0, md (32 * w + b), (st (32 * w + b + 1)).1, (st (32 * w + b + 1)).2].getD r 0

/-- The values after the last window. -/
def vxTail : List E :=
  if final then [mdF, md 95, (st 96).1, (st 96).2, wp, (st 96).1, (st 96).2, wp]
  else [(st 96).1, (st 96).2, wp, (st 96).1, (st 96).2, wp]

/-- The honest values of `da_vector_cell__L{final}`. -/
def vxVals (k : ℕ) : E :=
  if k < 4 then [xb, h0, h1, ctr].getD k 0 else
  if k < 260 then wsf (k - 4) else
  if k < 3460 then (pairVals (wsf (2 * ((k - 260) / 25))) (wsf (2 * ((k - 260) / 25) + 1))).getD
    ((k - 260) % 25 + 2) 0 else
  if k < 3462 then [h0, h1].getD (k - 3460) 0 else
  if k < 3470 then [xb * xb, xb * xb * xb, ctr * (xb * xb * xb), cvf 0, xb * xb, xb * xb * xb,
    ctr * (xb * xb * xb), cvf 1].getD (k - 3462) 0 else
  if k < 3594 then vxBv st md 0 ((k - 3470) / 4) ((k - 3470) % 4) else
  if k < 3596 then [(st 32).1, (st 32).2].getD (k - 3594) 0 else
  if k < 3602 then [xb * xb, xb * xb * xb, word 2 0 0, xb * xb * xb * word 2 0 0,
    ctr * (xb * xb * xb * word 2 0 0), cvf 2].getD (k - 3596) 0 else
  if k < 3726 then vxBv st md 1 ((k - 3602) / 4) ((k - 3602) % 4) else
  if k < 3728 then [(st 64).1, (st 64).2].getD (k - 3726) 0 else
  if k < 3734 then [xb * xb, xb * xb * xb, word 4 0 0, xb * xb * xb * word 4 0 0,
    ctr * (xb * xb * xb * word 4 0 0), cvf 3].getD (k - 3728) 0 else
  if k < 3858 then vxBv st md 2 ((k - 3734) / 4) ((k - 3734) % 4) else
  (vxTail final wp st md).getD (k - 3858) 0

theorem vxVals_arg {k : ℕ} (hk : k < 4) :
    vxVals final xb h0 h1 ctr wp wsf cvf st md k = [xb, h0, h1, ctr].getD k 0 := by
  unfold vxVals; rw [ite_pos' hk]

theorem vxVals_w {k : ℕ} (hk : k < 256) : vxVals final xb h0 h1 ctr wp wsf cvf st md (k + 4) = wsf k := by
  unfold vxVals; rw [ite_neg' (by omega), ite_pos' (by omega), Nat.add_sub_cancel]

theorem vxVals_pair {p r : ℕ} (hp : p < 128) (hr : r < 27) (hr2 : 2 ≤ r) :
    vxVals final xb h0 h1 ctr wp wsf cvf st md (258 + 25 * p + r) =
      (pairVals (wsf (2 * p)) (wsf (2 * p + 1))).getD r 0 := by
  unfold vxVals
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
    show (258 + 25 * p + r - 260) / 25 = p by omega, show (258 + 25 * p + r - 260) % 25 + 2 = r by omega]

theorem vxVals_h {r : ℕ} (hr : r < 2) :
    vxVals final xb h0 h1 ctr wp wsf cvf st md (3460 + r) = [h0, h1].getD r 0 := by
  unfold vxVals
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
    Nat.add_sub_cancel_left]

/-- The values from `3462` on, by region. -/
theorem vxVals_hi {k : ℕ} (hk : 3462 ≤ k) : vxVals final xb h0 h1 ctr wp wsf cvf st md k =
    if k < 3470 then [xb * xb, xb * xb * xb, ctr * (xb * xb * xb), cvf 0, xb * xb, xb * xb * xb,
      ctr * (xb * xb * xb), cvf 1].getD (k - 3462) 0 else
    if k < 3594 then vxBv st md 0 ((k - 3470) / 4) ((k - 3470) % 4) else
    if k < 3596 then [(st 32).1, (st 32).2].getD (k - 3594) 0 else
    if k < 3602 then [xb * xb, xb * xb * xb, word 2 0 0, xb * xb * xb * word 2 0 0,
      ctr * (xb * xb * xb * word 2 0 0), cvf 2].getD (k - 3596) 0 else
    if k < 3726 then vxBv st md 1 ((k - 3602) / 4) ((k - 3602) % 4) else
    if k < 3728 then [(st 64).1, (st 64).2].getD (k - 3726) 0 else
    if k < 3734 then [xb * xb, xb * xb * xb, word 4 0 0, xb * xb * xb * word 4 0 0,
      ctr * (xb * xb * xb * word 4 0 0), cvf 3].getD (k - 3728) 0 else
    if k < 3858 then vxBv st md 2 ((k - 3734) / 4) ((k - 3734) % 4) else
    (vxTail final wp st md).getD (k - 3858) 0 := by
  unfold vxVals
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega)]

theorem vxVals_bv {w b r : ℕ} (hw : w < 3) (hb : b < 31) (hr : r < 4) :
    vxVals final xb h0 h1 ctr wp wsf cvf st md (vxK w + 4 * b + r) = vxBv st md w b r := by
  rw [vxVals_hi _ _ _ _ _ _ _ _ _ _ (k := vxK w + 4 * b + r) (by unfold vxK; omega)]
  unfold vxK
  interval_cases w
  · rw [ite_neg' (by omega), ite_pos' (by omega), show (3470 + 132 * 0 + 4 * b + r - 3470) / 4 = b by omega,
      show (3470 + 132 * 0 + 4 * b + r - 3470) % 4 = r by omega]
  · rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
      ite_pos' (by omega), show (3470 + 132 * 1 + 4 * b + r - 3602) / 4 = b by omega,
      show (3470 + 132 * 1 + 4 * b + r - 3602) % 4 = r by omega]
  · rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
      ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
      show (3470 + 132 * 2 + 4 * b + r - 3734) / 4 = b by omega,
      show (3470 + 132 * 2 + 4 * b + r - 3734) % 4 = r by omega]

theorem vxVals_tail {r : ℕ} :
    vxVals final xb h0 h1 ctr wp wsf cvf st md (3858 + r) = (vxTail final wp st md).getD r 0 := by
  rw [vxVals_hi _ _ _ _ _ _ _ _ _ _ (k := 3858 + r) (by omega)]
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    Nat.add_sub_cancel_left]

end

theorem vxPair_bwd {rd : Reader} {σ : Val} {p : ℕ} {s t : E}
    (hv : ∀ r < 27, 2 ≤ r → σ (vxv p r) = (pairVals s t).getD r 0) (hs : σ (.n (2 * p + 4)) = s)
    (ht : σ (.n (2 * p + 1 + 4)) = t) :
    ∀ a ∈ vxPair p, a.Holds rd σ := by
  have h3s := (split3_iff s (ofK (s.limb 0)) (ofK (s.limb 1))).mpr ⟨rfl, rfl⟩
  have h3t := (split3_iff t (ofK (t.limb 0)) (ofK (t.limb 1))).mpr ⟨rfl, rfl⟩
  rw [← wYi_eq] at h3s h3t
  simp only [vxPair, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true, hs, ht]
  simp only [hv 2 (by norm_num) (by norm_num), hv 3 (by norm_num) (by norm_num),
    hv 4 (by norm_num) (by norm_num), hv 5 (by norm_num) (by norm_num),
    hv 6 (by norm_num) (by norm_num), hv 7 (by norm_num) (by norm_num),
    hv 8 (by norm_num) (by norm_num), hv 9 (by norm_num) (by norm_num),
    hv 10 (by norm_num) (by norm_num), hv 11 (by norm_num) (by norm_num),
    hv 12 (by norm_num) (by norm_num), hv 13 (by norm_num) (by norm_num),
    hv 14 (by norm_num) (by norm_num), hv 15 (by norm_num) (by norm_num),
    hv 16 (by norm_num) (by norm_num), hv 17 (by norm_num) (by norm_num),
    hv 18 (by norm_num) (by norm_num), hv 19 (by norm_num) (by norm_num),
    hv 20 (by norm_num) (by norm_num), hv 21 (by norm_num) (by norm_num),
    hv 22 (by norm_num) (by norm_num), hv 23 (by norm_num) (by norm_num),
    hv 24 (by norm_num) (by norm_num), hv 25 (by norm_num) (by norm_num),
    hv 26 (by norm_num) (by norm_num), pairVals, List.getD_cons_succ, List.getD_cons_zero,
    and_true, true_and]
  exact ⟨⟨h3s.1, h3s.2.1⟩, ⟨h3s.2.2, h3t.1⟩, ⟨h3t.2.1, h3t.2.2⟩⟩

theorem vxBlk_bwd {rd : Reader} {σ : Val} {final : Bool} {j : ℕ} {m : Fin 4 → E} {s0 s1 o0 o1 d : E}
    (hq : ![σ (.n (vxQ (4 * j))), σ (.n (vxQ (4 * j + 1))), σ (.n (vxQ (4 * j + 2))),
        σ (.n (vxQ (4 * j + 3)))] = m)
    (h0 : σ (.n (vxSt final j)) = s0) (h1 : σ (.n (vxSt final j + 1)) = s1)
    (h2 : σ (.n (vxSt final (j + 1))) = o0) (h3 : σ (.n (vxSt final (j + 1) + 1)) = o1)
    (hmd : σ (.n (vxMdI final j)) = d)
    (hc : j % 32 ≠ 31 → σ (.n (vxK (j / 32) + 4 * (j % 32))) = word (64 * (j % 32 + 1)) 0 0 ∧
      σ (.n (vxK (j / 32) + 4 * (j % 32) + 1)) =
        σ (.n (vxBase (j / 32))) + σ (.n (vxK (j / 32) + 4 * (j % 32))))
    (hf : final = true ∧ j = 95 → σ (.n 3858) = mdF ∧ σ (.n 3859) = σ (.n 3733) + σ (.n 3858))
    (hcomp : CompressCells m s0 s1 o0 o1 d) :
    ∀ a ∈ vxBlk final j, a.Holds rd σ := by
  have hC : CompressCells ![σ (.n (vxQ (4 * j))), σ (.n (vxQ (4 * j + 1))), σ (.n (vxQ (4 * j + 2))),
      σ (.n (vxQ (4 * j + 3)))] (σ (.n (vxSt final j))) (σ (.n (vxSt final j + 1)))
      (σ (.n (vxSt final (j + 1)))) (σ (.n (vxSt final (j + 1) + 1))) (σ (.n (vxMdI final j))) := by
    rw [hq, h0, h1, h2, h3, hmd]; exact hcomp
  unfold vxBlk
  split_ifs with g1 g2
  · simp only [List.cons_append, List.nil_append, List.forall_mem_cons, Atom.Holds,
      forall_mem_nil_iff, and_true]
    exact ⟨(hf g2).1, (hf g2).2, hC⟩
  · simp only [List.nil_append, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true]
    exact hC
  · simp only [List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true]
    exact ⟨(hc g1).1, (hc g1).2, hC⟩

/-- The honest run's atoms hold, over an abstract chain of states. -/
theorem vx_core_holds {final : Bool} {rd : Reader} {xb h0 h1 ctr o0 o1 wp : E} {wsf cvf : ℕ → E}
    {st : ℕ → E × E}
    (hcv : ∀ k < 4, LoadHolds rd (ctr * (xb * xb * xb)) k (cvf k))
    (hfr : IsInK wp ∧ ∀ k < 256, ∀ v, rd (wp.limb 0 * Parameters.gpow k) = some v → v = wsf k)
    (e0 : st 0 = (h0, h1)) (ho : st 96 = (o0, o1))
    (hcomp : ∀ j < 96, CompressCells (vxBlocks wsf j) (st j).1 (st j).2 (st (j + 1)).1
      (st (j + 1)).2 (vxMd final cvf j)) :
    let σ : Val := fun v => vxVals final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) v.idx
    (∀ a ∈ vxAtoms final, a.Holds rd σ) ∧
      [σ (.n (vxF final + 1)), σ (.n (vxF final + 2)), σ (.n (vxF final + 3))] = [o0, o1, wp] ∧
      [Core.V.n 0, .n 1, .n 2, .n 3].map σ = [xb, h0, h1, ctr] := by
  intro σ
  have hσ : ∀ k, σ (.n k) = vxVals final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) k := fun _ => rfl
  -- the states and metadata words
  have hst : ∀ i ≤ 96, σ (.n (vxSt final i)) = (st i).1 ∧ σ (.n (vxSt final i + 1)) = (st i).2 := by
    intro i hi
    unfold vxSt
    by_cases i0 : i = 0
    · subst i0
      rw [ite_pos' rfl, e0]
      exact ⟨rfl, rfl⟩
    rw [ite_neg' i0]
    by_cases i96 : final = true ∧ i = 96
    · rw [ite_pos' i96]
      obtain ⟨hf, rfl⟩ := i96
      subst hf
      exact ⟨rfl, rfl⟩
    rw [ite_neg' i96]
    by_cases l : (i - 1) % 32 = 31
    · rw [ite_pos' l]
      have hw : (i - 1) / 32 < 3 := by omega
      have hi32 : i = 32 * ((i - 1) / 32) + 32 := by omega
      generalize hw' : (i - 1) / 32 = w at hw hi32 ⊢
      subst hi32
      interval_cases w
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
      · cases final
        · exact ⟨rfl, rfl⟩
        · exact absurd ⟨rfl, rfl⟩ i96
    · rw [ite_neg' l]
      have hw : (i - 1) / 32 < 3 := by omega
      have hb : (i - 1) % 32 < 31 := by omega
      have a := vxVals_bv final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) (r := 2) hw hb (by omega)
      have b := vxVals_bv final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) (r := 3) hw hb (by omega)
      have e : 32 * ((i - 1) / 32) + (i - 1) % 32 + 1 = i := by omega
      simp only [vxBv, List.getD_cons_succ, List.getD_cons_zero, e] at a b
      exact ⟨a, b⟩
  have hbase : ∀ w < 3, σ (.n (vxBase w)) = cvf w := fun w hw => by
    interval_cases w <;> rfl
  have hend : ∀ w < 3, σ (.n (vxEnd w)) = cvf (w + 1) := fun w hw => by
    interval_cases w <;> rfl
  have hmd : ∀ j < 96, σ (.n (vxMdI final j)) = vxMd final cvf j := by
    intro j hj
    unfold vxMdI
    by_cases l : j % 32 = 31
    · rw [ite_pos' l]
      by_cases f : final = true ∧ j = 95
      · rw [ite_pos' f]
        obtain ⟨hf, rfl⟩ := f
        subst hf
        rfl
      · rw [ite_neg' f, hend (j / 32) (by omega)]
        unfold vxMd; rw [ite_pos' l, ite_neg' f]
    · rw [ite_neg' l]
      have a := vxVals_bv final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) (r := 1) (w := j / 32)
        (b := j % 32) (by omega) (by omega) (by omega)
      have e : 32 * (j / 32) + j % 32 = j := by omega
      simp only [vxBv, List.getD_cons_succ, List.getD_cons_zero, e] at a
      exact a
  have hpair : ∀ q < 384, σ (.n (vxQ q)) = vxCell wsf q := by
    intro q hq
    obtain ⟨p, r, hr, rfl⟩ : ∃ p r, r < 3 ∧ q = 3 * p + r := ⟨q / 3, q % 3, by omega, by omega⟩
    have e1 : (3 * p + r) / 3 = p := by omega
    have e2 : (3 * p + r) % 3 = r := by omega
    unfold vxQ vxCell
    rw [e1, e2, hσ, vxVals_pair final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) (by omega) (by omega)
      (by omega)]
    obtain ⟨p1, p2, p3⟩ := pair_cells (wsf (2 * p)) (wsf (2 * p + 1))
    interval_cases r
    · simpa [pairVals] using p1
    · simpa [pairVals] using p2
    · simpa [pairVals] using p3
  have hblk : ∀ j < 96, ∀ a ∈ vxBlk final j, a.Holds rd σ := by
    intro j hj
    refine vxBlk_bwd (m := vxBlocks wsf j) ?_ (hst j (by omega)).1 (hst j (by omega)).2
      (hst (j + 1) (by omega)).1 (hst (j + 1) (by omega)).2 (hmd j hj) (fun l => ?_) (fun f => ?_)
      (hcomp j hj)
    · simp only [vxBlocks]
      rw [hpair (4 * j) (by omega), hpair (4 * j + 1) (by omega), hpair (4 * j + 2) (by omega),
        hpair (4 * j + 3) (by omega)]
    · have a := vxVals_bv final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) (r := 0) (w := j / 32)
        (b := j % 32) (by omega) (by omega) (by omega)
      have a1 := vxVals_bv final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) (r := 1) (w := j / 32)
        (b := j % 32) (by omega) (by omega) (by omega)
      have e : 32 * (j / 32) + j % 32 = j := by omega
      simp only [vxBv, List.getD_cons_succ, List.getD_cons_zero, e, Nat.add_zero] at a a1
      refine ⟨a, ?_⟩
      rw [hσ, a1, hbase (j / 32) (by omega), hσ, a]
      unfold vxMd; rw [ite_neg' l]
    · obtain ⟨hf, rfl⟩ := f
      subst hf
      exact ⟨rfl, rfl⟩
  -- the counter words' atoms
  have hpre0 : ∀ a ∈ vxPre0, a.Holds rd σ := by
    simp only [vxPre0, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true]
    exact ⟨rfl, rfl, rfl, hcv 0 (by omega), rfl, rfl, rfl, hcv 1 (by omega)⟩
  have hpre1 : ∀ a ∈ vxPre 1, a.Holds rd σ := by
    simp only [vxPre, vxK, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow,
      List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true]
    have l := (loadHolds_mul_gen_pow (ctr * (xb * xb * xb)) 1 1 (cvf 2)).mpr (hcv 2 (by omega))
    rw [pow_one, ← word_gen, mul_assoc ctr (xb * xb * xb) (word 2 0 0)] at l
    exact ⟨rfl, rfl, rfl, rfl, rfl, l⟩
  have hpre2 : ∀ a ∈ vxPre 2, a.Holds rd σ := by
    simp only [vxPre, vxK, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow,
      List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true]
    have l := (loadHolds_mul_gen_pow (ctr * (xb * xb * xb)) 2 1 (cvf 3)).mpr (hcv 3 (by omega))
    rw [← word4, mul_assoc ctr (xb * xb * xb) (word 4 0 0)] at l
    exact ⟨rfl, rfl, rfl, rfl, rfl, l⟩
  have hF : σ (.n (vxF final + 1)) = σ (.n (vxSt final 96)) ∧
      σ (.n (vxF final + 2)) = σ (.n (vxSt final 96 + 1)) ∧ σ (.n (vxF final + 3)) = σ (.n (vxF final)) ∧
      σ (.n (vxF final)) = wp ∧ [σ (.n (vxF final + 1)), σ (.n (vxF final + 2)), σ (.n (vxF final + 3))] =
        [o0, o1, wp] := by
    cases final
    · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      show [(st 96).1, (st 96).2, wp] = _
      rw [ho]
    · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      show [(st 96).1, (st 96).2, wp] = _
      rw [ho]
  refine ⟨?_, hF.2.2.2.2, rfl⟩
  simp only [vxAtoms, List.forall_mem_append, forall_mem_flatMap_range,
    List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true, true_and]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨fun i hi => ?_, rfl, rfl⟩, hpre0⟩, fun b hb => hblk b (by omega)⟩, hpre1⟩,
    fun b hb => hblk (32 + b) (by omega)⟩, hpre2⟩, fun b hb => hblk (64 + b) (by omega)⟩,
    ⟨?_, fun k hk v hv => ?_⟩, hF.1, hF.2.1, hF.2.2.1⟩
  · exact vxPair_bwd (s := wsf (2 * i)) (t := wsf (2 * i + 1))
      (fun r hr hr2 => vxVals_pair final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) hi hr hr2)
      (vxVals_w final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) (k := 2 * i) (by omega))
      (vxVals_w final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) (k := 2 * i + 1) (by omega))
  · rw [hF.2.2.2.1]; exact hfr.1
  · simp only [List.length_map, List.length_range] at hk
    rw [hF.2.2.2.1] at hv
    simp only [List.getElem_map, List.getElem_range]
    rw [hσ, vxVals_w final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) hk]
    exact hfr.2 k hk v hv

/-- The honest run, over an abstract chain of states. -/
theorem vx_bwd_core {final : Bool} {rd : Reader} {xb h0 h1 ctr o0 o1 wp : E} {wsf cvf : ℕ → E}
    {st : ℕ → E × E}
    (hcv : ∀ k < 4, LoadHolds rd (ctr * (xb * xb * xb)) k (cvf k))
    (hfr : IsInK wp ∧ ∀ k < 256, ∀ v, rd (wp.limb 0 * Parameters.gpow k) = some v → v = wsf k)
    (e0 : st 0 = (h0, h1)) (ho : st 96 = (o0, o1))
    (hcomp : ∀ j < 96, CompressCells (vxBlocks wsf j) (st j).1 (st j).2 (st (j + 1)).1
      (st (j + 1)).2 (vxMd final cvf j)) :
    coreProgram.Rel rd (vxName final) [xb, h0, h1, ctr] [o0, o1, wp] := by
  obtain ⟨ha, hr, hp⟩ := vx_core_holds hcv hfr e0 ho hcomp
  rw [rel_of_find (find_vx final)]
  refine ⟨_, hp, ?_⟩
  rw [vxBody, holdsList_atoms]
  exact ⟨ha, hr⟩

theorem da_vector_cell_bwd {final : Bool} {rd : Reader} {args rets : List E}
    (h : Meaning_da_vector_cell final rd args rets) : coreProgram.Rel rd (vxName final) args rets := by
  obtain ⟨xb, h0, h1, ctr, o0, o1, wp, rfl, rfl, ws, cv, hwl, hcl, hcv, hch, hfr⟩ := h
  rcases hch with ⟨h96, -⟩ | ⟨-, hd, hst0, hcan, hout⟩
  · omega
  refine vx_bwd_core (wsf := (ws.getD · 0)) (cvf := (cv.getD · 0))
    (st := fun i => digestScalars (chainRun hd (vxBlocks (ws.getD · 0)) (vxMd final (cv.getD · 0)) i))
    (fun k hk => ?_) ⟨hfr.1, fun k hk v hv => hfr.2 k (by omega) v hv⟩ hst0.symm hout.symm
    (fun j hj => (compressCells_chainRun (hcan j hj).1 (hcan j hj).2).mpr rfl)
  have := hcv k (by omega)
  rwa [← List.getD_eq_getElem _ 0] at this

/-- **`da_vector_cell__L{final}`**, exactly. -/
theorem da_vector_cell_iff (final : Bool) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (vxName final) args rets ↔ Meaning_da_vector_cell final rd args rets :=
  ⟨da_vector_cell_fwd, da_vector_cell_bwd⟩


end
end LeanVM.Guest.B1.Digest

namespace LeanVM.Guest.B1
export Digest (vxCell vxBlocks vxMd FrameRun Meaning_da_vector_cell da_vector_cell_iff)
end LeanVM.Guest.B1
