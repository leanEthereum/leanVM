/-
  LeanVM.Guest.B1.Da.Columns

  What `da_verify`'s soundness reads off each column and each cell, and the vector hash's chain.
-/

module

public import LeanVM.Guest.B1.Da.Link

/-!
# Columns and cells, soundly

Each column's facts under the honest counter words (`col_facts`, `ColOk`), each cell's
(`cell_facts`, `CellOk`), the vector hash's chain over the columns (`vector_chain`), and the
helpers they share: choices over bounded indices, loops in `LoopTo` form, sums by chunks.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Node

@[expose] public section

/-! ## Helpers -/

theorem choose_lt {α : Type} [Inhabited α] {n : ℕ} {P : ℕ → α → Prop} (h : ∀ b < n, ∃ x, P b x) :
    ∃ f : ℕ → α, ∀ b < n, P b (f b) := by
  classical
  exact ⟨fun b => if hb : b < n then (h b hb).choose else default, fun b hb => by
    simp only [hb, ↓reduceDIte]; exact (h b hb).choose_spec⟩

theorem choose_lt₂ {α : Type} [Inhabited α] {n m : ℕ} {P : ℕ → ℕ → α → Prop}
    (h : ∀ b < n, ∀ i < m, ∃ x, P b i x) : ∃ f : ℕ → ℕ → α, ∀ b < n, ∀ i < m, P b i (f b i) := by
  obtain ⟨f, hf⟩ := choose_lt (α := ℕ → α) (P := fun b g => ∀ i < m, P b i (g i))
    (fun b hb => choose_lt (h b hb))
  exact ⟨f, hf⟩

/-- A `mul_range(1, g^n)` loop's iterations, in `LoopTo` form. -/
theorem loopTo_all {n : ℕ} {B : ℕ → Prop} (hn : n < 2 ^ 33) (h : LoopTo (gen ^ n) B) : ∀ j < n, B j := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · intro j hj; omega
  obtain ⟨m, -, hN, hfirst, hall⟩ := h
  have := loop_end_exact hn hpos hN hfirst
  subst this
  exact hall

theorem vxMd_congr {final : Bool} {f g : ℕ → E} (h : ∀ k < 4, f k = g k) {j : ℕ} (hj : j < 96) :
    vxMd final f j = vxMd final g j := by
  unfold vxMd
  rw [h 3 (by omega), h (j / 32 + 1) (by omega), h (j / 32) (by omega)]

theorem pow_two_mul (x : E) (b : ℕ) (hx : x = gen ^ b) : x * x = gen ^ (2 * b) := by
  rw [hx, ← pow_add]; congr 1; ring

theorem gen_pow_ne_one' {n : ℕ} (h1 : 1 ≤ n) (h2 : n < 2 ^ 33) : gen ^ n ≠ 1 := fun he => by
  have := (gen_pow_eq_one_iff (by omega)).mp he; omega

/-! ## A column -/

/-- What a column's run holds: the vector hash's states, its weights, its tree. -/
structure ColW where
  h0 : E
  h1 : E
  o0 : E
  o1 : E
  lv : E
  node : E
  c0 : E
  c1 : E
  ws : List E
  deriving Inhabited

/-- Column `b`'s facts, under the honest counter words. -/
def ColOk (rd : Reader) (r : ℕ) (pb ct rb hs : E) (b : ℕ) (c : ColW) : Prop :=
  c.ws.length = 256 ∧ CellsAt rd (hs * gen ^ (2 * b)) [c.h0, c.h1] ∧
    CellsAt rd (hs * gen ^ (2 * b + 2)) [c.o0, c.o1] ∧
    ChainCells (c.h0, c.h1) (vxBlocks (c.ws.getD · 0)) (vxMd (decide (b = 127)) (cvOf b)) 96 (c.o0, c.o1) ∧
    FrameRun rd c.lv c.ws ∧
    (∀ i < r, RowCell (decide (b < 64)) rd c.lv rb (gen ^ b) c.node pb (gen ^ i)) ∧
    (∀ d < LeanDa.nPad r - r, GapStep rd c.node (gen ^ r) (gen ^ d)) ∧
    Meaning_da_levels (LeanDa.logPad r) rd [c.node] [c.c0, c.c1] ∧
    CellsAt rd (ct * gen ^ (2 * b)) [c.c0, c.c1]

theorem col_facts {rd : Reader} {r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ LeanDa.maxRows) {pb ct rb hs ctr : E}
    (hctr : ∀ k < 385, ∀ w, rd (ctr.limb 0 * Parameters.gpow k) = some w → w = word (k * 2048) 0 0)
    {b : ℕ} (hb : b < 128)
    (h : Meaning_da_verify_column (decide (b < 64)) rd [gen ^ b, gen ^ r, gen ^ LeanDa.nPad r,
      gen ^ (LeanDa.nPad r - r), gen ^ LeanDa.logPad r, pb, ct, rb, hs, ctr] []) :
    ∃ c : ColW, ColOk rd r pb ct rb hs b c := by
  have hr33 : r < 2 ^ 33 := by unfold LeanDa.maxRows at hr2; omega
  have hlp := logPad_le hr2
  have hN := nPad_le hr2
  obtain ⟨xb, nb, np, gap, glp, pb', ct', rb', hs', ctr', ha, -, h0, h1, o0, o1, lv, node, c0, c1, hh, hdisp,
    ho, -, hrow, -, hgap, ⟨k, hk, hglp, hlv⟩, hc⟩ := h
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ha
  obtain ⟨xb, rest, hxa, -, hvc⟩ := hdisp
  simp only [List.cons.injEq] at hxa
  obtain ⟨rfl, rfl⟩ := hxa
  obtain ⟨_, _, _, _, _, _, wp, ha, hr, ws, cv, hwl, hcl, hcv, hch, hfr⟩ := hvc
  simp only [List.cons.injEq, and_true] at ha hr
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ha
  obtain ⟨rfl, rfl, rfl⟩ := hr
  have hkl : k = LeanDa.logPad r := gen_pow_inj' (by omega) (by omega) hglp.symm
  subst hkl
  have hfinal : decide (gen ^ b = gen ^ 127) = decide (b = 127) := by
    by_cases h127 : b = 127
    · rw [decide_eq_true h127, decide_eq_true (by rw [h127])]
    · rw [decide_eq_false h127, decide_eq_false fun he => h127 (gen_pow_inj' (by omega) (by omega) he)]
  have hcv' : ∀ k < 4, cv.getD k 0 = cvOf b k := by
    intro k hk
    have hl := hcv k (by omega)
    rw [show gen ^ b * gen ^ b * gen ^ b = gen ^ (3 * b) by rw [← pow_add, ← pow_add]; congr 1; ring,
      loadHolds_mul_gen_pow] at hl
    rw [List.getD_eq_getElem _ _ (by omega), hctr (3 * b + k) (by omega) _ hl.2, cvOf, Nat.add_mul]
  rw [hfinal, chainCells_congr (b' := vxBlocks (ws.getD · 0)) (md' := vxMd (decide (b = 127)) (cvOf b))
    (fun _ _ => rfl) (fun j hj => vxMd_congr hcv' hj)] at hch
  refine ⟨⟨h0, h1, o0, o1, lv, node, c0, c1, ws⟩, hwl, ?_, ?_, hch, hfr,
    loopTo_all hr33 (hrow (gen_pow_ne_one' hr1 hr33)), fun d hd => ?_, hlv, ?_⟩
  · have e : gen ^ b * gen ^ b = gen ^ (2 * b) := by rw [← pow_add, two_mul]
    rw [e] at hh; exact hh
  · have e : gen ^ b * gen * (gen ^ b * gen) = gen ^ (2 * b + 2) := by
      rw [← pow_succ, ← pow_add]; congr 1; ring
    rw [e] at ho; exact ho
  · exact loopTo_all (by omega) (hgap (gen_pow_ne_one' (by omega) (by omega))) d hd
  · have e : gen ^ b * gen ^ b = gen ^ (2 * b) := by rw [← pow_add, two_mul]
    rw [e] at hc; exact hc

/-! ## The vector hash -/

theorem vxCell_canonical (f : ℕ → E) (q : ℕ) : IsCanonical128 (vxCell f q) := by
  unfold vxCell
  split_ifs <;> exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl

theorem vxCell_three (f : ℕ → E) (p : ℕ) :
    (List.range 3).flatMap (fun r => cellBytes (vxCell f (3 * p + r))) =
      eBytes (f (2 * p)) ++ eBytes (f (2 * p + 1)) := by
  have e0 : vxCell f (3 * p + 0) = E.ofLimbs ((f (2 * p)).limb 0) ((f (2 * p)).limb 1) 0 := by
    unfold vxCell; rw [ite_pos' (by omega), show (3 * p + 0) / 3 = p by omega]
  have e1 : vxCell f (3 * p + 1) = E.ofLimbs ((f (2 * p)).limb 2) ((f (2 * p + 1)).limb 0) 0 := by
    unfold vxCell; rw [ite_neg' (by omega), ite_pos' (by omega), show (3 * p + 1) / 3 = p by omega]
  have e2 : vxCell f (3 * p + 2) = E.ofLimbs ((f (2 * p + 1)).limb 1) ((f (2 * p + 1)).limb 2) 0 := by
    unfold vxCell; rw [ite_neg' (by omega), ite_neg' (by omega), show (3 * p + 2) / 3 = p by omega]
  rw [show List.range 3 = [0, 1, 2] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [e0, e1, e2, ← List.append_assoc, pair_bytes]

theorem vxBlocks_canonical (f : ℕ → E) (j : ℕ) : ∀ r, IsCanonical128 (vxBlocks f j r) := by
  intro r; fin_cases r <;> simp [vxBlocks, vxCell_canonical]

/-- A column's 96 blocks are its 256 weights' bytes. -/
theorem vx_bytes (ws : List E) (hl : ws.length = 256) :
    (List.range 96).flatMap (fun j => blockBytes (vxBlocks (ws.getD · 0) j)) = ws.flatMap eBytes := by
  have e1 : (List.range 96).flatMap (fun j => blockBytes (vxBlocks (ws.getD · 0) j)) =
      (List.range (4 * 96)).flatMap (fun q => cellBytes (vxCell (ws.getD · 0) q)) := by
    rw [flatMap_range_mul 4]
    refine List.flatMap_congr fun j _ => ?_
    simp [blockBytes, vxBlocks, List.range_succ, List.append_assoc]
  have e2 : (List.range 384).flatMap (fun q => cellBytes (vxCell (ws.getD · 0) q)) =
      (List.range 128).flatMap (fun p => eBytes (ws.getD (2 * p) 0) ++ eBytes (ws.getD (2 * p + 1) 0)) := by
    rw [show 384 = 3 * 128 by rfl, flatMap_range_mul 3]
    refine List.flatMap_congr fun p _ => ?_
    exact vxCell_three _ p
  have e3 : (List.range 256).flatMap (fun k => eBytes (ws.getD k 0)) =
      (List.range 128).flatMap (fun p => eBytes (ws.getD (2 * p) 0) ++ eBytes (ws.getD (2 * p + 1) 0)) := by
    rw [show 256 = 2 * 128 by rfl, flatMap_range_mul 2]
    refine List.flatMap_congr fun p _ => ?_
    rw [show List.range 2 = [0, 1] from rfl]
    simp
  rw [e1, show 4 * 96 = 384 by rfl, e2, ← e3, ← hl, flatMap_range_getD]

theorem chainRun_add (h : Digest) (B : ℕ → Fin 4 → E) (M : ℕ → E) (n : ℕ) : ∀ m,
    chainRun h B M (n + m) = chainRun (chainRun h B M n) (fun i => B (n + i)) (fun i => M (n + i)) m
  | 0 => rfl
  | m + 1 => by rw [← Nat.add_assoc, chainRun, chainRun, chainRun_add h B M n m]

/-- **The vector digest**: the `128` columns' chains, from the IV at `hashes`, are BLAKE2s of
the weights' bytes, which `hashes·g^256` holds. -/
theorem vector_chain {rd : Reader} {r : ℕ} {pb ct rb hs v0 v1 : E} {F : ℕ → ColW}
    (hok : ∀ b < 128, ColOk rd r pb ct rb hs b (F b))
    (hiv0 : LoadHolds rd hs 0 (digestScalars paramIv).1) (hiv1 : LoadHolds rd hs 1 (digestScalars paramIv).2)
    (hv0 : LoadHolds rd hs 256 v0) (hv1 : LoadHolds rd hs 257 v1) :
    (v0, v1) = digestScalars (blake2sBytes (((List.range 128).flatMap fun b => (F b).ws).flatMap eBytes)) := by
  let all : ℕ → Fin 4 → E := fun i => vxBlocks ((F (i / 96)).ws.getD · 0) (i % 96)
  let mdA : ℕ → E := fun i => metadataCell (64 * (i + 1)) (decide (i + 1 = 12288))
  let S : ℕ → E × E := fun b => digestScalars (chainRun paramIv all mdA (96 * b))
  have hcell : ∀ {p : E} {k : ℕ} {a b a' b' : E}, CellsAt rd (p * gen ^ k) [a, b] → CellsAt rd (p * gen ^ k) [a', b'] →
      (a, b) = (a', b') := fun h h' => by
    obtain ⟨x0, x1⟩ := cellsAt_two.mp h
    obtain ⟨y0, y1⟩ := cellsAt_two.mp h'
    rw [loadHolds_unique x0 y0, loadHolds_unique x1 y1]
  have hstep : ∀ b < 128, ((F b).h0, (F b).h1) = S b → ((F b).o0, (F b).o1) = S (b + 1) := by
    intro b hb hh
    obtain ⟨hl, -, -, hch, -⟩ := hok b hb
    rcases hch with ⟨h96, -⟩ | ⟨-, H, hH, -, hout⟩
    · omega
    rw [hh] at hH
    have hHe := digestScalars_injective hH
    show _ = digestScalars (chainRun paramIv all mdA (96 * (b + 1)))
    rw [hout, ← hHe, show 96 * (b + 1) = 96 * b + 96 by ring, chainRun_add]
    have hb1 : ∀ i < 96, vxBlocks ((F b).ws.getD · 0) i = all (96 * b + i) := fun i hi => by
      show vxBlocks _ i = vxBlocks ((F ((96 * b + i) / 96)).ws.getD · 0) ((96 * b + i) % 96)
      rw [show (96 * b + i) / 96 = b by omega, show (96 * b + i) % 96 = i by omega]
    have hm1 : ∀ i < 96, vxMd (decide (b = 127)) (cvOf b) i = mdA (96 * b + i) := fun i hi => by
      rw [vxMd_counters hb hi]
      show _ = metadataCell (64 * (96 * b + i + 1)) (decide (96 * b + i + 1 = 12288))
      rw [decide_eq_decide.mpr (show (b = 127 ∧ i = 95) ↔ 96 * b + i + 1 = 12288 by omega)]
    rw [chainRun_congr (b' := fun i => all (96 * b + i)) (md' := fun i => mdA (96 * b + i)) 96 hb1 hm1]
  have hS : ∀ b < 128, ((F b).h0, (F b).h1) = S b := by
    intro b hb
    induction b with
    | zero =>
      obtain ⟨-, hh, -⟩ := hok 0 hb
      rw [Nat.mul_zero, pow_zero, mul_one] at hh
      obtain ⟨x0, x1⟩ := cellsAt_two.mp hh
      rw [loadHolds_unique x0 hiv0, loadHolds_unique x1 hiv1]
      rfl
    | succ b ih =>
      obtain ⟨-, -, ho, -⟩ := hok b (by omega)
      obtain ⟨-, hh, -⟩ := hok (b + 1) hb
      rw [show 2 * b + 2 = 2 * (b + 1) by ring] at ho
      rw [hcell hh ho]
      exact hstep b (by omega) (ih (by omega))
  have h128 : (v0, v1) = S 128 := by
    obtain ⟨-, -, ho, -⟩ := hok 127 (by omega)
    rw [← hstep 127 (by omega) (hS 127 (by omega))]
    obtain ⟨x0, x1⟩ := cellsAt_two.mp ho
    rw [loadHolds_mul_gen_pow] at x0 x1
    rw [loadHolds_unique hv0 x0, loadHolds_unique hv1 x1]
  rw [h128]
  show digestScalars (chainRun paramIv all mdA (96 * 128)) = _
  rw [show 96 * 128 = 12287 + 1 by rfl, chainRun_blocks (n := 12287)
    (fun j _ r => vxBlocks_canonical _ _ r)
    (fun j hj => by simp only [mdA]; congr 1; simp only [decide_eq_false_iff_not]; omega) rfl]
  have hbytes : (List.range (12287 + 1)).flatMap (fun j => blockBytes (all j)) =
      ((List.range 128).flatMap fun b => (F b).ws).flatMap eBytes := by
    rw [show 12287 + 1 = 96 * 128 by rfl, flatMap_range_mul 96, List.flatMap_assoc]
    refine List.flatMap_congr fun b hb => ?_
    have hb' := List.mem_range.mp hb
    rw [← vx_bytes _ (hok b hb').1]
    refine List.flatMap_congr fun j hj => ?_
    have hj' := List.mem_range.mp hj
    show blockBytes (vxBlocks ((F ((96 * b + j) / 96)).ws.getD · 0) ((96 * b + j) % 96)) = _
    rw [show (96 * b + j) / 96 = b by omega, show (96 * b + j) % 96 = j by omega]
  rw [hbytes]

/-! ## A cell -/

/-- What a row's cell in a column holds: its symbols, digest, inner product and sums. -/
structure CellW where
  d0 : E
  d1 : E
  s : E
  R : E
  a : E
  syms : List K
  wsc : List E
  deriving Inhabited

def CellOk (rd : Reader) (store : Bool) (lv rb xb node pb x : E) (c : CellW) : Prop :=
  c.syms.length = 256 ∧ c.wsc.length = 256 ∧ CellsAt rd lv c.wsc ∧
    (c.d0, c.d1) = digestScalars (blake2sBytes (c.syms.flatMap kBytes)) ∧
    c.s = ∑ k ∈ Finset.range 256, c.wsc.getD k 0 * ofK (c.syms.getD k 0) ∧
    LoadHolds rd (rb * x) 0 c.R ∧ LoadHolds rd (c.R * xb) 0 c.a ∧ LoadHolds rd (c.R * xb) 1 (c.a + c.s) ∧
    CellsAt rd (node * (x * x)) [c.d0, c.d1] ∧
    (store = true → ∃ P, LoadHolds rd (pb * x) 0 P ∧ CellsAt rd (P * (xb * xb)) [c.d0, c.d1])

theorem cell_facts {rd : Reader} {store : Bool} {lv rb xb node pb x : E}
    (h : RowCell store rd lv rb xb node pb x) : ∃ c : CellW, CellOk rd store lv rb xb node pb x c := by
  obtain ⟨d0, d1, s, R, a, hm, hR, ha, has, hn, hst⟩ := h
  obtain ⟨_, _, _, _, hargs, hrets, syms, wsc, hsl, hwl, hws, hd, hs⟩ := hm
  simp only [List.cons.injEq, and_true] at hargs hrets
  obtain ⟨rfl⟩ := hargs
  obtain ⟨rfl, rfl, rfl⟩ := hrets
  exact ⟨⟨_, _, _, R, a, syms, wsc⟩, hsl, hwl, hws, hd, hs, hR, ha, has, hn, hst⟩

/-! ## Sums -/

theorem sum_range_mul (m : ℕ) (f : ℕ → E) : ∀ n,
    ∑ x ∈ Finset.range (m * n), f x = ∑ b ∈ Finset.range n, ∑ k ∈ Finset.range m, f (m * b + k)
  | 0 => by simp
  | n + 1 => by rw [show m * (n + 1) = m * n + m by ring, Finset.sum_range_add, sum_range_mul m f n,
      Finset.sum_range_succ]

theorem getD_flatMap_range {α : Type} {m : ℕ} (L : ℕ → List α) (d : α) {n : ℕ}
    (hl : ∀ b < n, (L b).length = m) {b k : ℕ} (hb : b < n) (hk : k < m) :
    ((List.range n).flatMap L).getD (m * b + k) d = (L b).getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, getElem?_flatMap_range L n hl b hb k hk]

/-! ## Pointers -/

theorem cells_eq {rd : Reader} {p : E} {a b a' b' : E} (h : CellsAt rd p [a, b]) (h' : CellsAt rd p [a', b']) :
    a = a' ∧ b = b' := by
  obtain ⟨x0, x1⟩ := cellsAt_two.mp h
  obtain ⟨y0, y1⟩ := cellsAt_two.mp h'
  exact ⟨loadHolds_unique x0 y0, loadHolds_unique x1 y1⟩

theorem gen_sq (x : ℕ) : gen ^ x * gen ^ x = gen ^ (2 * x) := by rw [← pow_add, two_mul]

theorem pad_ptr (p : E) (r d : ℕ) : p * (gen ^ r * gen ^ r) * (gen ^ d * gen ^ d) = p * gen ^ (2 * (r + d)) := by
  rw [gen_sq, gen_sq, mul_assoc, ← pow_add]; congr 2; ring

end
end LeanVM.Guest.B1.Digest
