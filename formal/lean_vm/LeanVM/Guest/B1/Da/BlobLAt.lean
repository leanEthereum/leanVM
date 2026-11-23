/-
  LeanVM.Guest.B1.Da.BlobLAt

  `da_verify`'s blob loop `da_verify_loop0` placed by trees of its honest shape, within its bound (G:4535-4539).

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Da.PadAt
public import LeanVM.Guest.B1.Da.CellLAt
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify_loop0»

/-!
# The blob loop, within its bound

`da_verify_loop0(x, g^r, w, roots)` (`blobLP`): blob `log x` (`da_verify_blob` on the weights `w`), its root's two
cells at `roots·x²`, then the next counter `x·g` and the tail call while `x·g ≠ g^r`. On a layout holding the roots'
tree at `g^bT` (`rootsCells r L syms`):

* `blobLNH i r Tb Tt`: an iteration's honest shape at the counter `g^i`, its blob by a tree of `Tb`, its tail call
  (taken unless `i + 1 = r`) by a tree of `Tt`; `blobLFrom r Tb t i`: `t` iterations from `i`, blob `j` by `Tb j`;
* `blobL_stepAtTB`, `blobL_completeAtTB`: one iteration, and the loop over the `r` blobs within `r · Kb` and its
  frame, each blob within `Kb` words with the iteration's frame.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Protocol.KeccakHash
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1 (CompleteAtDTB CompleteAtL completeAtL_tail Returns DisjL Within disj_append
  within_append)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)

@[expose] public section

/-- `da_verify_loop0`'s statements before its `ret`. -/
def blobLP : List Stmt :=
  blobLPre ++ [.callIf (.n (val% «da_verify_loop0» "s5#2")) name% «da_verify_loop0» (.n (val% «da_verify_loop0» "s5#4") :: (List.range 3).map fun k => V.n (k + (val% «da_verify_loop0» "bound")))]

theorem blobL_body_split : Fn.body (coreProgram.getD idx% «da_verify_loop0» default) = blobLP ++ [.ret []] := by
  rw [dv_loops_body.1, blobLP, List.append_assoc]
  rfl

theorem blobLP_straight : blobLP.all Main.Stmt.straight = true := rfl

theorem blobL_loop : coreProgram.loop name% «da_verify_loop0» = true := by
  rw [Program.loop_of_find? find_blobL]; decide +kernel

/-- An iteration's calls: the blob, then the tail call, taken unless `i + 1 = r`. -/
def blobLCalls (i r : ℕ) : List Call :=
  [⟨"da_verify_blob", [.n (val% «da_verify_loop0» "weights")], [.n (val% «da_verify_loop0» "b0"), .n (val% «da_verify_loop0» "b1")], true⟩] ++
    [⟨name% «da_verify_loop0», .n (val% «da_verify_loop0» "s5#4") :: (List.range 3).map fun k => V.n (k + (val% «da_verify_loop0» "bound")), [], decide (i + 1 ≠ r)⟩]

/-- **An iteration's honest shape.** -/
def blobLNH (i r : ℕ) (Tb Tt : Tree → Prop) : Tree → Prop :=
  NodeHonest coreProgram name% «da_verify_loop0» (fun σ => σ (.n (val% «da_verify_loop0» "xi")) = gen ^ i) (fun _ => blobLCalls i r)
    (fun _ => []) [Tb, Tt]

/-- **`t` iterations from `i`**, blob `j` by a tree of `Tb j`; none (`False`) past the last. -/
def blobLFrom (r : ℕ) (Tb : ℕ → Tree → Prop) : ℕ → ℕ → Tree → Prop
  | 0, _ => fun _ => False
  | t + 1, i => blobLNH i r (Tb i) (blobLFrom r Tb t (i + 1))

variable (fs : String → ℕ) (cert : String → V → ℕ)

/-- **One iteration of the blob loop, placed, by a tree of its honest shape**: blob `i`, its root among the roots'
leaves. -/
theorem blobL_stepAtTB {Bb Bt : ℕ} {Tb Tt : Tree → Prop} {r L i bw bT : ℕ} {syms : ℕ → ℕ → List E}
    {Lin : Layout} (hi : i + 1 ≤ r) (hrL : r ≤ 2 ^ L) (hL : L ≤ 10) (hTm : (bT, rootsCells r L syms) ∈ Lin)
    (hblob : CompleteAtDTB fs cert 16 "da_verify_blob" Lin [gen ^ bw] (Returns (digestCells (blobLeaf r syms i)))
      Tb Bb)
    (htail : i + 1 < r → CompleteAtL fs cert 16 name% «da_verify_loop0» Lin
      [gen ^ (i + 1), gen ^ r, gen ^ bw, gen ^ bT] (Returns []) Tt (· ≤ Bt))
    (hBt : fs name% «da_verify_loop0» ≤ Bt) :
    CompleteAtL fs cert 16 name% «da_verify_loop0» Lin [gen ^ i, gen ^ r, gen ^ bw, gen ^ bT] (Returns [])
      (blobLNH i r Tb Tt) (· ≤ fs name% «da_verify_loop0» + Bt + Bb) := by
  have hN : 2 ^ L ≤ 1024 := le_trans (Nat.pow_le_pow_right (by norm_num) hL) (by norm_num)
  -- the rest of the loop
  obtain ⟨Bt', hRest⟩ := completeAtL_tail (fs := fs) (cert := cert) (g := name% «da_verify_loop0»)
    (last := i + 1 = r) fun h => htail (by omega)
  refine ⟨fs name% «da_verify_loop0» + Bt', fun fp cur hcur => ?_⟩
  -- the blob
  obtain ⟨nc, Lc, rc, Loc, hncB, ⟨rfl, rfl⟩, hWc, hDc, hRc⟩ := hblob cur
  simp only [List.nil_append] at hWc hDc hRc
  obtain ⟨nt, Lt, hlt, hBdt, hWt, hDt, hRt⟩ :=
    hRest (fp + fs name% «da_verify_loop0») (cur + nc) (by omega)
  refine ⟨nc + nt, Lc ++ Lt, [], [], ?_, ⟨rfl, rfl⟩, ?_,
    by simpa using disj_append hDc hDt hWc hWt le_rfl, fun rd hlow hm => ?_⟩
  · by_cases hlast : i + 1 = r
    · obtain ⟨rfl, rfl⟩ := hlt hlast
      show _ ≤ _
      omega
    · have := hBdt hlast
      show _ ≤ _
      omega
  · rw [List.nil_append, within_append]
    exact ⟨hWc.mono le_rfl (by omega), hWt.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hm
  obtain ⟨hm1, hLin⟩ := memL_append.mp hm
  obtain ⟨hmc, hmt⟩ := memL_append.mp hm1
  have ht := hRt rd hlow (memL_append.mpr ⟨hmt, hLin⟩)
  have hc := hRc rd hlow (memL_append.mpr ⟨hmc, hLin⟩)
  have hT := reads_of_memL hLin hTm
  obtain ⟨hl1, hl2⟩ := roots_leaf (r := r) (L := L) (syms := syms) (i := i) (by omega)
  have h0 : LoadHolds rd (gen ^ bT * (gen ^ i * gen ^ i)) 0 (digestHalves (blobLeaf r syms i)).1 := by
    rw [← pow_add, loadHolds_mul_gen_pow]
    exact loadHolds_of_reads hT (by rw [length_rootsCells]; omega) (by rw [show i + i + 0 = 2 * i by ring, hl1])
  have h1 : LoadHolds rd (gen ^ bT * (gen ^ i * gen ^ i)) 1 (digestHalves (blobLeaf r syms i)).2 := by
    rw [← pow_add, loadHolds_mul_gen_pow]
    exact loadHolds_of_reads hT (by rw [length_rootsCells]; omega) (by rw [show i + i + 1 = 2 * i + 1 by ring, hl2])
  -- the path
  set σ := Val.ofArgs [gen ^ i, gen ^ r, gen ^ bw, gen ^ bT, (digestHalves (blobLeaf r syms i)).1,
    (digestHalves (blobLeaf r syms i)).2, gen ^ i * gen ^ i, gen ^ bT * (gen ^ i * gen ^ i), word 2 0,
    gen ^ i * word 2 0, gen ^ i * word 2 0 + gen ^ r, word 2 0, gen ^ i * word 2 0] with hσ
  have hw' := Main.walk_straight σ [] blobLP blobLP_straight
  rw [← blobL_body_split] at hw'
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ blobLP_straight
  have h10 : σ (.n (val% «da_verify_loop0» "s5#2")) = gen ^ (i + 1) + gen ^ r := by
    show gen ^ i * word 2 0 + gen ^ r = _
    rw [word_gen, gen_pow_mul_gen]
  have htk : decide (σ (.n (val% «da_verify_loop0» "s5#2")) ≠ 0) = decide (i + 1 ≠ r) := by
    rw [h10]; exact gen_pow_add_ne (by omega) (by omega)
  have hcalls : calls (blobLP.flatMap (Main.slEvs σ)) = blobLCalls i r := by
    rw [hpc, show blobLP.filterMap Main.Stmt.callS =
      [(none, "da_verify_blob", [.n (val% «da_verify_loop0» "weights")], [.n (val% «da_verify_loop0» "b0"), .n (val% «da_verify_loop0» "b1")]),
        (some (.n (val% «da_verify_loop0» "s5#2")), name% «da_verify_loop0», .n (val% «da_verify_loop0» "s5#4") :: (List.range 3).map fun k => V.n (k + (val% «da_verify_loop0» "bound")), [])] from rfl]
    simp only [List.map_cons, List.map_nil, Main.mkCall, htk, blobLCalls, List.cons_append, List.nil_append]
  have hal : allocs σ (blobLP.flatMap (Main.slEvs σ)) = [] := by
    rw [hpa, show blobLP.filterMap Main.Stmt.allocSz = [] from rfl]; rfl
  have hev : ∀ e ∈ blobLP.flatMap (Main.slEvs σ), e.Holds rd σ := by
    refine slEvs_holds fun s hs => ?_
    simp only [blobLP, blobLPre, stepAtC, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [SlOk, Atom.Holds, hσ, ofArgs_n, List.getD_cons_succ, List.getD_cons_zero]
    exacts [h0, h1, by rw [word_gen, gen_pow_mul_gen]; exact gen_pow_add_isInK _ _]
  have hargs : (.n (val% «da_verify_loop0» "s5#4") :: (List.range 3).map fun k => V.n (k + (val% «da_verify_loop0» "bound"))).map σ =
      [gen ^ (i + 1), gen ^ r, gen ^ bw, gen ^ bT] := by
    show [gen ^ i * word 2 0, gen ^ r, gen ^ bw, gen ^ bT] = _
    rw [word_gen, gen_pow_mul_gen]
  have hpar : (coreProgram.getD idx% «da_verify_loop0» default).params = (List.range 4).map V.n :=
    params_of_shape dv_loops_shape.1.1 dv_loops_shape.1.2
  have hreg' : ∀ {j : ℕ}, j < 4 * 2 ^ L → RegionL Lin (bT + j) := fun hj =>
    regionL_of_mem hTm (by rw [length_rootsCells]; exact hj)
  have h := relAtInWT_of_walk_loop (P := coreProgram) (Ts := [Tb]) (Tt := Tt) (fs := fs)
    (cert := cert) (σ := σ) (rd := rd) (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False)
    (Rt := RegionL Lin) (Dt := RegionL []) (fp := fp) (c := cur) (Bt := Bt') (m := nt) (N := nc)
    (args := [gen ^ i, gen ^ r, gen ^ bw, gen ^ bT]) coreProgram_wf find_blobL blobL_loop
    (by rw [hpar]; rfl) hw' rfl hev (by rw [hcalls]; rfl)
    (by
      rw [hal, List.sum_nil, Nat.add_zero]
      by_cases hlast : i + 1 = r
      · simpa [hlast] using ht
      · simp only [ne_eq, hlast, not_false_eq_true, decide_true, ↓reduceIte] at ht ⊢
        rw [hargs]; exact ht)
    (by rw [hal, hpd, show blobLP.filterMap Main.Stmt.allocSz = [] from rfl]; rfl)
    (fun q hq => by
      rw [hpad, show blobLP.filterMap Main.Stmt.addrS = [] from rfl] at hq
      simp at hq)
    rfl
    (by
      rw [hal]
      refine ⟨nc, 0, RegionL Lin, fun _ => False, rfl, fun j hj => Or.inl (Or.inl hj), ?_,
        ⟨rfl, fun j hj => hj.elim⟩⟩
      simp only [ite_true, List.sum_nil, Nat.add_zero]
      exact relAtInT_dmono hc fun _ h => h.elim)
    (fun j hj => Or.inl hj)
    (fun A hA => by
      rw [B1.loadAddrs_straight σ _ blobLP_straight,
        show blobLP.filterMap B1.Stmt.loadS = [(.n (val% «da_verify_loop0» "slot"), 0), (.n (val% «da_verify_loop0» "slot"), 1)] from rfl] at hA
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · refine ⟨bT + 2 * i, ?_, Or.inr (Or.inl (hreg' (by omega)))⟩
        show (gen ^ bT * (gen ^ i * gen ^ i)).limb 0 * addressOfIndex 0 = _
        rw [← pow_add, ← pow_add, limb0_gen_pow_mul]; ring_nf
      · refine ⟨bT + (2 * i + 1), ?_, Or.inr (Or.inl (hreg' (by omega)))⟩
        show (gen ^ bT * (gen ^ i * gen ^ i)).limb 0 * addressOfIndex 1 = _
        rw [← pow_add, ← pow_add, limb0_gen_pow_mul]; ring_nf)
    (fun j hj => by obtain ⟨q, hq, -⟩ := hj; simp at hq)
  have h' := relAtInCT_nodeHonest (Q := fun σ => σ (.n (val% «da_verify_loop0» "xi")) = gen ^ i)
    (cs := fun _ => blobLCalls i r) (bs := fun _ => []) (Ts := [Tb, Tt]) h find_blobL hw' rfl
    (by rw [hcalls]) hal (by simp [blobLCalls])
  rw [hal] at h'
  simp only [List.sum_nil, Nat.zero_add] at h'
  exact h'

/-- **The blob loop is complete, placed, by trees of its honest shape** (`blobLFrom`), over the `r` blobs, within
`r · Kb` and its frame, blob `i` by a tree of `Tb i` within `Bb` and `fs loop + Bb ≤ Kb`. -/
theorem blobL_completeAtTB {Bb Kb : ℕ} {Tb : ℕ → Tree → Prop} {r L bw bT : ℕ} {syms : ℕ → ℕ → List E}
    {Lin : Layout} (hr1 : 1 ≤ r) (hrL : r ≤ 2 ^ L) (hL : L ≤ 10) (hTm : (bT, rootsCells r L syms) ∈ Lin)
    (hblob : ∀ i < r, CompleteAtDTB fs cert 16 "da_verify_blob" Lin [gen ^ bw]
      (Returns (digestCells (blobLeaf r syms i))) (Tb i) Bb)
    (hK : fs name% «da_verify_loop0» + Bb ≤ Kb) :
    CompleteAtDTB fs cert 16 name% «da_verify_loop0» Lin [1, gen ^ r, gen ^ bw, gen ^ bT] (Returns [])
      (blobLFrom r Tb r 0) (r * Kb + fs name% «da_verify_loop0») := by
  have key : ∀ t i, i + 1 + t = r →
      CompleteAtL fs cert 16 name% «da_verify_loop0» Lin [gen ^ i, gen ^ r, gen ^ bw, gen ^ bT] (Returns [])
        (blobLFrom r Tb (t + 1) i) (· ≤ (t + 1) * Kb + fs name% «da_verify_loop0») := by
    intro t
    induction t with
    | zero =>
      intro i hi
      have h := blobL_stepAtTB (Tt := blobLFrom r Tb 0 (i + 1)) (Bt := fs name% «da_verify_loop0») fs cert
        (by omega) hrL hL hTm (hblob i (by omega)) (fun h => absurd h (by omega)) le_rfl
      exact h.mono (fun x hx => by omega) fun _ h => h
    | succ t ih =>
      intro i hi
      have h := blobL_stepAtTB fs cert (by omega) hrL hL hTm (hblob i (by omega))
        (fun _ => ih (i + 1) (by omega)) (by nlinarith)
      exact h.mono (fun x hx => by nlinarith) fun _ h => h
  have := key (r - 1) 0 (by omega)
  rw [show r - 1 + 1 = r by omega, pow_zero] at this
  exact this.toDTB

end
end LeanVM.Guest.B1.Da
