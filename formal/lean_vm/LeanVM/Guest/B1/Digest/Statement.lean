/-
  LeanVM.Guest.B1.Digest.Statement

  B1 for `statement_digest` (G:2664-2703; TRIAGE #58): the statement's digest, byte for byte.
-/

module

public import LeanVM.Guest.B1.Digest.Common
public import LeanVM.Spec.Node

/-!
# `statement_digest`

`statement_digest(seed_0, seed_1, signers_hash, da_0, da_1, defer)` hashes 22 blocks of four
cells: the seed's two cells, the signer-set digest's two (read at `signers_hash`), the DA list
digest's two, then the 53 deferred cells (read at `defer`) two at a time as three canonical cells
each (the last paired with a zero cell), then one zero cell. A pair `s, t` is split into its
limbs by `hint_f192_limbs`, pinned by the three `pack64x2` checks (`Tower.split3_iff`), and its
three cells are the 48 bytes `eBytes s ++ eBytes t`. So the digest is `statementDigest`'s
(`stmtDigestOf`, `statementDigest_eq`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Node

@[expose] public section

/-! ## The specification -/

/-- `statementDigest` on its parts: the seed, the signer-set digest, the DA list digest and the
deferred cells. -/
def stmtDigestOf (seed sig da : Digest) (defer : List E) : Digest :=
  let cells := defer ++ if defer.length % 2 = 1 then [0] else []
  let bytes := digestBytes seed ++ digestBytes sig ++ digestBytes da ++ cells.flatMap eBytes
  blake2sBytes (bytes ++ List.replicate ((64 - bytes.length % 64) % 64) 0)

theorem statementDigest_eq (seed : Digest) (s : NodeStatement) :
    statementDigest seed s = stmtDigestOf seed (signersDigest s.claims.xmss s.claims.sphincs)
      (daListDigest s.claims.da) s.defer.cells := rfl

/-- The number of deferred cells a statement carries (`DEFER_STMT_CELLS`). -/
abbrev deferStmtCells : ℕ := 53

/-- **`statement_digest`**: the digest of the statement whose seed and list digests are the
argument cells (the signer-set digest read at `signers_hash`) and whose 53 deferred cells are
read at `defer`. -/
def Meaning_statement_digest (rd : Reader) (args rets : List E) : Prop :=
  ∃ seed0 seed1 sigp da0 da1 dp d0 d1, args = [seed0, seed1, sigp, da0, da1, dp] ∧
    rets = [d0, d1] ∧ ∃ (seed sig da : Digest) (cells : List E), cells.length = deferStmtCells ∧
      (seed0, seed1) = digestScalars seed ∧ LoadHolds rd sigp 0 (digestScalars sig).1 ∧
      LoadHolds rd sigp 1 (digestScalars sig).2 ∧ (da0, da1) = digestScalars da ∧
      CellsAt rd dp cells ∧ (d0, d1) = digestScalars (stmtDigestOf seed sig da cells)

/-! ## The template -/

/-- Value `r` of deferred pair `p < 26`. -/
abbrev pv (p r : ℕ) : V := .n (12 + 27 * p + r)

/-- Value `r` of the chain after block `b`: its state's two cells, then block `b`'s metadata. -/
abbrev bv (b r : ℕ) : V := .n (741 + 3 * b + r)

/-- `y` and `y⁻¹` as the guest's words. -/
abbrev wY : E := word 0 1 0
abbrev wYi : E := word 1 0 1

/-- Deferred pair `p < 26`: two cells read, split, packed into three. -/
def sdPair (p : ℕ) : List Atom :=
  [.load (pv p 0) (.n 5) (2 * p), .load (pv p 1) (.n 5) (2 * p + 1),
   .hint (.limbs (pv p 0) [pv p 2, pv p 3]), .hint (.limbs (pv p 1) [pv p 4, pv p 5]),
   .assertInK (pv p 2) (pv p 3), .const (pv p 6) wY, .mul (pv p 7) (pv p 6) (pv p 3),
   .add (pv p 8) (pv p 2) (pv p 7), .add (pv p 9) (pv p 0) (pv p 2), .const (pv p 10) wYi,
   .mul (pv p 11) (pv p 9) (pv p 10), .add (pv p 12) (pv p 11) (pv p 3), .const (pv p 13) wYi,
   .mul (pv p 14) (pv p 12) (pv p 13), .assertInK (pv p 14) (pv p 4), .const (pv p 15) wY,
   .mul (pv p 16) (pv p 15) (pv p 4), .add (pv p 17) (pv p 14) (pv p 16),
   .add (pv p 18) (pv p 1) (pv p 4), .const (pv p 19) wYi, .mul (pv p 20) (pv p 18) (pv p 19),
   .add (pv p 21) (pv p 20) (pv p 5), .const (pv p 22) wYi, .mul (pv p 23) (pv p 21) (pv p 22),
   .assertInK (pv p 5) (pv p 23), .const (pv p 24) wY, .mul (pv p 25) (pv p 24) (pv p 23),
   .add (pv p 26) (pv p 5) (pv p 25)]

/-- The last deferred cell, paired with the zero cell. -/
def sdLast : List Atom :=
  [.load (.n 714) (.n 5) 52, .hint (.limbs (.n 714) [.n 715, .n 716]),
   .const (.n 717) (word 0 0 0), .hint (.limbs (.n 717) [.n 718, .n 719]),
   .assertInK (.n 715) (.n 716), .const (.n 720) wY, .mul (.n 721) (.n 720) (.n 716),
   .add (.n 722) (.n 715) (.n 721), .add (.n 723) (.n 714) (.n 715), .const (.n 724) wYi,
   .mul (.n 725) (.n 723) (.n 724), .add (.n 726) (.n 725) (.n 716), .const (.n 727) wYi,
   .mul (.n 728) (.n 726) (.n 727), .assertInK (.n 728) (.n 718), .const (.n 729) wY,
   .mul (.n 730) (.n 729) (.n 718), .add (.n 731) (.n 728) (.n 730), .const (.n 732) wYi,
   .mul (.n 733) (.n 718) (.n 732), .add (.n 734) (.n 733) (.n 719), .const (.n 735) wYi,
   .mul (.n 736) (.n 734) (.n 735), .assertInK (.n 719) (.n 736), .const (.n 737) wY,
   .mul (.n 738) (.n 737) (.n 736), .add (.n 739) (.n 719) (.n 738)]

/-- The value of hashed cell `k < 88`: the six header cells, the three cells of each pair, the
zero cell. -/
def cellIdx (k : ℕ) : ℕ :=
  if k < 6 then 6 + k else if k = 86 then 739 else if k = 87 then 740 else
  12 + 27 * ((k - 6) / 3) + (8 + 9 * ((k - 6) % 3))

/-- Block `b` of the chain. -/
def sdBlk (b : ℕ) : List Atom :=
  [.const (bv b 2) (word (64 * (b + 1)) (if b + 1 = 22 then 4294967295 else 0) 0),
   .blake2s (.n (cellIdx (4 * b))) (.n (cellIdx (4 * b + 1))) (.n (cellIdx (4 * b + 2)))
     (.n (cellIdx (4 * b + 3))) (bv b 0) (bv b 1) (bv (b + 1) 0) (bv (b + 1) 1) (bv b 2)]

/-- `statement_digest`'s body. -/
def sdBody : List Stmt :=
  (([.copy (.n 6) (.n 0), .copy (.n 7) (.n 1), .load (.n 8) (.n 2) 0, .load (.n 9) (.n 2) 1,
      .copy (.n 10) (.n 3), .copy (.n 11) (.n 4)] : List Atom) ++
    (List.range 26).flatMap sdPair ++ sdLast ++
    ([.const (.n 740) (word 0 0 0), .const (.n 741) (word 13503953895743350343 11912009169889063794 0),
      .const (.n 742) (word 11170449402626986623 6620516960021240235 0)] : List Atom) ++
    (List.range 22).flatMap sdBlk ++
    ([.copy (.n 809) (.n 807), .copy (.n 810) (.n 808)] : List Atom)).map .atom ++
  [.ret [.n 809, .n 810]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem find_statement_digest : coreProgram.find? "statement_digest" =
    some ⟨"statement_digest", [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5], sdBody⟩ :=
  Program.find?_of_indexOf? (j := 18) (by decide +kernel) rfl

/-! ## Values -/

theorem wY_eq : wY = y := by rw [y_eq]; rfl

theorem wYi_eq : wYi = y⁻¹ := by rw [y_inv]; rfl

theorem cellBytes_ofLimbs (a b : K) : cellBytes (E.ofLimbs a b 0) = kBytes a ++ kBytes b := rfl

/-- **A deferred pair**: the hinted limbs pinned by the three `pack64x2` checks make the three
packed cells the pair's six limbs. -/
theorem pair_spec {s t s0 s1 t0 t1 : E} (h1 : IsInK s0 ∧ IsInK s1)
    (h2 : IsInK (((s + s0) * wYi + s1) * wYi) ∧ IsInK t0)
    (h3 : IsInK t1 ∧ IsInK (((t + t0) * wYi + t1) * wYi)) :
    s0 = ofK (s.limb 0) ∧ s1 = ofK (s.limb 1) ∧ t0 = ofK (t.limb 0) ∧ t1 = ofK (t.limb 1) := by
  rw [wYi_eq] at h2 h3
  obtain ⟨hs0, hs1⟩ := (split3_iff s s0 s1).mp ⟨h1.1, h1.2, h2.1⟩
  obtain ⟨ht0, ht1⟩ := (split3_iff t t0 t1).mp ⟨h2.2, h3.1, h3.2⟩
  exact ⟨hs0, hs1, ht0, ht1⟩

/-- The three cells of a pair, from its limbs. -/
theorem pair_cells (s t : E) :
    ofK (s.limb 0) + wY * ofK (s.limb 1) = E.ofLimbs (s.limb 0) (s.limb 1) 0 ∧
    ((s + ofK (s.limb 0)) * wYi + ofK (s.limb 1)) * wYi + wY * ofK (t.limb 0) =
      E.ofLimbs (s.limb 2) (t.limb 0) 0 ∧
    ofK (t.limb 1) + wY * (((t + ofK (t.limb 0)) * wYi + ofK (t.limb 1)) * wYi) =
      E.ofLimbs (t.limb 1) (t.limb 2) 0 := by
  rw [wY_eq, wYi_eq, split3_top, split3_top]
  refine ⟨?_, ?_, ?_⟩ <;> rw [pack64x2_eq (ofK_isInK _) (ofK_isInK _)] <;> simp

theorem pair_bytes (s t : E) :
    cellBytes (E.ofLimbs (s.limb 0) (s.limb 1) 0) ++ cellBytes (E.ofLimbs (s.limb 2) (t.limb 0) 0) ++
      cellBytes (E.ofLimbs (t.limb 1) (t.limb 2) 0) = eBytes s ++ eBytes t := by
  simp only [cellBytes_ofLimbs, eBytes, List.append_assoc]

theorem length_kBytes (a : K) : (kBytes a).length = 8 := rfl

theorem length_eBytes (x : E) : (eBytes x).length = 24 := rfl

theorem length_digestBytes (d : Digest) : (digestBytes d).length = 32 := by
  rw [digestBytes_eq]; rfl

theorem length_flatMap_eBytes (cs : List E) : (cs.flatMap eBytes).length = 24 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [List.flatMap_cons, List.length_append, ih, length_eBytes, List.length_cons]; ring

/-- `stmtDigestOf` at the guest's cell count: 1392 bytes and 16 zero bytes. -/
theorem stmtDigestOf_eq (seed sig da : Digest) (cells : List E) (hlen : cells.length = 53) :
    stmtDigestOf seed sig da cells = blake2sBytes ((digestBytes seed ++ digestBytes sig ++
      digestBytes da ++ (cells ++ [0]).flatMap eBytes) ++ List.replicate 16 0) := by
  simp only [stmtDigestOf, hlen]
  simp only [↓reduceIte, List.length_append, length_digestBytes,
    length_flatMap_eBytes, hlen, List.length_cons, List.length_nil]

/-- **The hashed bytes**: 22 blocks of cells whose header cells are the three digests', whose
pair cells are the pairs' limbs and whose last cell is zero are the statement's bytes. -/
theorem sd_bytes (c : ℕ → E) (seed sig da : Digest) (cells : List E) (hlen : cells.length = 53)
    (h0 : cellBytes (c 0) ++ cellBytes (c 1) = digestBytes seed)
    (h1 : cellBytes (c 2) ++ cellBytes (c 3) = digestBytes sig)
    (h2 : cellBytes (c 4) ++ cellBytes (c 5) = digestBytes da)
    (hp : ∀ p < 27, cellBytes (c (6 + 3 * p)) ++ cellBytes (c (6 + 3 * p + 1)) ++
      cellBytes (c (6 + 3 * p + 2)) =
        eBytes ((cells ++ [0]).getD (2 * p) 0) ++ eBytes ((cells ++ [0]).getD (2 * p + 1) 0))
    (hz : c 87 = 0) :
    (List.range 22).flatMap (fun b => blockBytes ![c (4 * b), c (4 * b + 1), c (4 * b + 2),
      c (4 * b + 3)]) =
      (digestBytes seed ++ digestBytes sig ++ digestBytes da ++ (cells ++ [0]).flatMap eBytes) ++
        List.replicate 16 0 := by
  have e1 : (List.range 22).flatMap (fun b => blockBytes ![c (4 * b), c (4 * b + 1),
      c (4 * b + 2), c (4 * b + 3)]) = (List.range (4 * 22)).flatMap (fun k => cellBytes (c k)) := by
    rw [flatMap_range_mul 4]
    refine List.flatMap_congr fun b _ => ?_
    simp [blockBytes, List.range_succ, List.append_assoc]
  have e2 : (List.range 81).flatMap (fun k => cellBytes (c (6 + k))) =
      (cells ++ [0]).flatMap eBytes := by
    rw [show 81 = 3 * 27 from rfl, flatMap_range_mul 3]
    rw [List.flatMap_congr (l := List.range 27) (g := fun p =>
      eBytes ((cells ++ [0]).getD (2 * p) 0) ++ eBytes ((cells ++ [0]).getD (2 * p + 1) 0))
      fun p hp' => by
        rw [← hp p (List.mem_range.mp hp')]
        simp [List.range_succ, Nat.add_assoc]]
    rw [← flatMap_range_getD (cells ++ [0]) 0 eBytes, List.length_append, hlen,
      show 53 + [(0 : E)].length = 2 * 27 from rfl, flatMap_range_mul 2]
    refine List.flatMap_congr fun p _ => ?_
    simp [List.range_succ]
  rw [e1, show 4 * 22 = 6 + (81 + 1) from rfl, List.range_add, List.flatMap_append,
    List.flatMap_map, List.range_add, List.flatMap_append, List.flatMap_map]
  rw [e2, show List.range 1 = [0] from rfl, show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, show 6 + (81 + 0) = 87 from rfl,
    hz, cellBytes_zero, ← h0, ← h1, ← h2, List.append_assoc]

/-- The chain over cells satisfying `sd_bytes`'s hypotheses computes `stmtDigestOf`. -/
theorem sd_chainRun (c : ℕ → E) (seed sig da : Digest) (cells : List E) (hlen : cells.length = 53)
    (h0 : cellBytes (c 0) ++ cellBytes (c 1) = digestBytes seed)
    (h1 : cellBytes (c 2) ++ cellBytes (c 3) = digestBytes sig)
    (h2 : cellBytes (c 4) ++ cellBytes (c 5) = digestBytes da)
    (hp : ∀ p < 27, cellBytes (c (6 + 3 * p)) ++ cellBytes (c (6 + 3 * p + 1)) ++
      cellBytes (c (6 + 3 * p + 2)) =
        eBytes ((cells ++ [0]).getD (2 * p) 0) ++ eBytes ((cells ++ [0]).getD (2 * p + 1) 0))
    (hz : c 87 = 0) (hcan : ∀ k < 88, IsCanonical128 (c k)) :
    chainRun paramIv (fun b => ![c (4 * b), c (4 * b + 1), c (4 * b + 2), c (4 * b + 3)])
      (fun b => metadataCell (64 * (b + 1)) (decide (b + 1 = 22))) 22 =
      stmtDigestOf seed sig da cells := by
  rw [stmtDigestOf_eq seed sig da cells hlen, ← sd_bytes c seed sig da cells hlen h0 h1 h2 hp hz]
  refine chainRun_blocks (n := 21) (fun j hj r => ?_) (fun j hj => ?_) (by simp)
  · fin_cases r
    · exact hcan _ (by omega)
    · exact hcan _ (by omega)
    · exact hcan _ (by omega)
    · exact hcan _ (by omega)
  · congr 1
    simp only [decide_eq_false_iff_not]
    omega

theorem cellIdx_hdr (k : ℕ) (hk : k < 6) : cellIdx k = 6 + k := by
  simp [cellIdx, hk]

theorem cellIdx_pair (p r : ℕ) (hp : p < 26) (hr : r < 3) :
    cellIdx (6 + 3 * p + r) = 12 + 27 * p + (8 + 9 * r) := by
  unfold cellIdx
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    show (6 + 3 * p + r - 6) / 3 = p by omega, show (6 + 3 * p + r - 6) % 3 = r by omega]

theorem cellIdx_A (p : ℕ) (hp : p < 26) : cellIdx (6 + 3 * p) = 12 + 27 * p + 8 := by
  simpa using cellIdx_pair p 0 hp (by omega)

theorem cellIdx_B (p : ℕ) (hp : p < 26) : cellIdx (6 + 3 * p + 1) = 12 + 27 * p + 17 := by
  simpa using cellIdx_pair p 1 hp (by omega)

theorem cellIdx_C (p : ℕ) (hp : p < 26) : cellIdx (6 + 3 * p + 2) = 12 + 27 * p + 26 := by
  simpa using cellIdx_pair p 2 hp (by omega)

theorem cellIdx_lt (k : ℕ) : cellIdx k < 741 ∨ 88 ≤ k := by
  unfold cellIdx
  split_ifs <;> omega

/-- The facts of deferred pair `p`. -/
theorem sdPair_fwd {rd : Reader} {σ : Val} {p : ℕ} (h : ∀ a ∈ sdPair p, a.Holds rd σ) :
    LoadHolds rd (σ (.n 5)) (2 * p) (σ (pv p 0)) ∧ LoadHolds rd (σ (.n 5)) (2 * p + 1) (σ (pv p 1)) ∧
      σ (pv p 8) = E.ofLimbs ((σ (pv p 0)).limb 0) ((σ (pv p 0)).limb 1) 0 ∧
      σ (pv p 17) = E.ofLimbs ((σ (pv p 0)).limb 2) ((σ (pv p 1)).limb 0) 0 ∧
      σ (pv p 26) = E.ofLimbs ((σ (pv p 1)).limb 1) ((σ (pv p 1)).limb 2) 0 := by
  simp only [sdPair, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true] at h
  obtain ⟨l0, l1, -, -, k1, c6, m7, a8, a9, c10, m11, a12, c13, m14, k2, c15, m16, a17, a18, c19,
    m20, a21, c22, m23, k3, c24, m25, a26⟩ := h
  have e14 : σ (pv p 14) = ((σ (pv p 0) + σ (pv p 2)) * wYi + σ (pv p 3)) * wYi := by
    rw [m14, a12, m11, a9, c10, c13]
  have e23 : σ (pv p 23) = ((σ (pv p 1) + σ (pv p 4)) * wYi + σ (pv p 5)) * wYi := by
    rw [m23, a21, m20, a18, c19, c22]
  rw [e14] at k2
  rw [e23] at k3
  obtain ⟨hs0, hs1, ht0, ht1⟩ := pair_spec k1 k2 k3
  obtain ⟨p1, p2, p3⟩ := pair_cells (σ (pv p 0)) (σ (pv p 1))
  refine ⟨l0, l1, ?_, ?_, ?_⟩
  · rw [a8, m7, c6, hs0, hs1, p1]
  · rw [a17, m16, c15, e14, hs0, hs1, ht0, p2]
  · rw [a26, m25, c24, e23, ht0, ht1, p3]

/-- The facts of the last deferred cell. -/
theorem sdLast_fwd {rd : Reader} {σ : Val} (h : ∀ a ∈ sdLast, a.Holds rd σ) :
    LoadHolds rd (σ (.n 5)) 52 (σ (.n 714)) ∧
      σ (.n 722) = E.ofLimbs ((σ (.n 714)).limb 0) ((σ (.n 714)).limb 1) 0 ∧
      σ (.n 731) = E.ofLimbs ((σ (.n 714)).limb 2) ((0 : E).limb 0) 0 ∧
      σ (.n 739) = E.ofLimbs ((0 : E).limb 1) ((0 : E).limb 2) 0 := by
  simp only [sdLast, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true] at h
  obtain ⟨l0, -, c717, -, k1, c720, m721, a722, a723, c724, m725, a726, c727, m728, k2, c729, m730,
    a731, c732, m733, a734, c735, m736, k3, c737, m738, a739⟩ := h
  have e728 : σ (.n 728) = ((σ (.n 714) + σ (.n 715)) * wYi + σ (.n 716)) * wYi := by
    rw [m728, a726, m725, a723, c724, c727]
  have e736 : σ (.n 736) = (((0 : E) + σ (.n 718)) * wYi + σ (.n 719)) * wYi := by
    rw [m736, a734, m733, c732, c735, zero_add]
  rw [e728] at k2
  rw [e736] at k3
  obtain ⟨hs0, hs1, ht0, ht1⟩ := pair_spec k1 k2 k3
  obtain ⟨p1, p2, p3⟩ := pair_cells (σ (.n 714)) 0
  refine ⟨l0, ?_, ?_, ?_⟩
  · rw [a722, m721, c720, hs0, hs1, p1]
  · rw [a731, m730, c729, e728, hs0, hs1, ht0, p2]
  · rw [a739, m738, c737, e736, ht0, ht1, p3]

theorem sdBlk_fwd {rd : Reader} {σ : Val} {b : ℕ} (h : ∀ a ∈ sdBlk b, a.Holds rd σ) :
    σ (bv b 2) = word (64 * (b + 1)) (if b + 1 = 22 then 4294967295 else 0) 0 ∧
      CompressCells ![σ (.n (cellIdx (4 * b))), σ (.n (cellIdx (4 * b + 1))),
        σ (.n (cellIdx (4 * b + 2))), σ (.n (cellIdx (4 * b + 3)))] (σ (bv b 0)) (σ (bv b 1))
        (σ (bv (b + 1) 0)) (σ (bv (b + 1) 1)) (σ (bv b 2)) := by
  simpa only [sdBlk, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true] using h

/-! ## The honest values -/

/-- The values of a deferred pair `s, t`, in `sdPair`'s order. -/
def pairVals (s t : E) : List E :=
  let s0 := ofK (s.limb 0)
  let s1 := ofK (s.limb 1)
  let t0 := ofK (t.limb 0)
  let t1 := ofK (t.limb 1)
  let a14 := ((s + s0) * wYi + s1) * wYi
  let a23 := ((t + t0) * wYi + t1) * wYi
  [s, t, s0, s1, t0, t1, wY, wY * s1, s0 + wY * s1, s + s0, wYi, (s + s0) * wYi,
   (s + s0) * wYi + s1, wYi, a14, wY, wY * t0, a14 + wY * t0, t + t0, wYi, (t + t0) * wYi,
   (t + t0) * wYi + t1, wYi, a23, wY, wY * a23, t1 + wY * a23]

/-- The values of the last deferred cell `s`, in `sdLast`'s order. -/
def lastVals (s : E) : List E :=
  let s0 := ofK (s.limb 0)
  let s1 := ofK (s.limb 1)
  let t0 := ofK ((0 : E).limb 0)
  let t1 := ofK ((0 : E).limb 1)
  let a14 := ((s + s0) * wYi + s1) * wYi
  let a23 := (t0 * wYi + t1) * wYi
  [s, s0, s1, 0, t0, t1, wY, wY * s1, s0 + wY * s1, s + s0, wYi, (s + s0) * wYi,
   (s + s0) * wYi + s1, wYi, a14, wY, wY * t0, a14 + wY * t0, wYi, t0 * wYi, t0 * wYi + t1, wYi,
   a23, wY, wY * a23, t1 + wY * a23]

theorem sdPair_bwd {rd : Reader} {σ : Val} {p : ℕ} {s t dp : E}
    (hv : ∀ r < 27, σ (pv p r) = (pairVals s t).getD r 0) (h5 : σ (.n 5) = dp)
    (ls : LoadHolds rd dp (2 * p) s) (lt : LoadHolds rd dp (2 * p + 1) t) :
    ∀ a ∈ sdPair p, a.Holds rd σ := by
  have hs := (split3_iff s (ofK (s.limb 0)) (ofK (s.limb 1))).mpr ⟨rfl, rfl⟩
  have ht := (split3_iff t (ofK (t.limb 0)) (ofK (t.limb 1))).mpr ⟨rfl, rfl⟩
  rw [← wYi_eq] at hs ht
  simp only [sdPair, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true, h5]
  simp only [hv _ (by norm_num : (0 : ℕ) < 27), hv _ (by norm_num : (1 : ℕ) < 27),
    hv _ (by norm_num : (2 : ℕ) < 27), hv _ (by norm_num : (3 : ℕ) < 27),
    hv _ (by norm_num : (4 : ℕ) < 27), hv _ (by norm_num : (5 : ℕ) < 27),
    hv _ (by norm_num : (6 : ℕ) < 27), hv _ (by norm_num : (7 : ℕ) < 27),
    hv _ (by norm_num : (8 : ℕ) < 27), hv _ (by norm_num : (9 : ℕ) < 27),
    hv _ (by norm_num : (10 : ℕ) < 27), hv _ (by norm_num : (11 : ℕ) < 27),
    hv _ (by norm_num : (12 : ℕ) < 27), hv _ (by norm_num : (13 : ℕ) < 27),
    hv _ (by norm_num : (14 : ℕ) < 27), hv _ (by norm_num : (15 : ℕ) < 27),
    hv _ (by norm_num : (16 : ℕ) < 27), hv _ (by norm_num : (17 : ℕ) < 27),
    hv _ (by norm_num : (18 : ℕ) < 27), hv _ (by norm_num : (19 : ℕ) < 27),
    hv _ (by norm_num : (20 : ℕ) < 27), hv _ (by norm_num : (21 : ℕ) < 27),
    hv _ (by norm_num : (22 : ℕ) < 27), hv _ (by norm_num : (23 : ℕ) < 27),
    hv _ (by norm_num : (24 : ℕ) < 27), hv _ (by norm_num : (25 : ℕ) < 27),
    hv _ (by norm_num : (26 : ℕ) < 27), pairVals, List.getD_cons_succ, List.getD_cons_zero,
    and_true, true_and]
  exact ⟨ls, lt, ⟨hs.1, hs.2.1⟩, ⟨hs.2.2, ht.1⟩, ⟨ht.2.1, ht.2.2⟩⟩

theorem sdLast_bwd {rd : Reader} {σ : Val} {s dp : E}
    (hv : ∀ r < 26, σ (.n (714 + r)) = (lastVals s).getD r 0) (h5 : σ (.n 5) = dp)
    (ls : LoadHolds rd dp 52 s) :
    ∀ a ∈ sdLast, a.Holds rd σ := by
  have hs := (split3_iff s (ofK (s.limb 0)) (ofK (s.limb 1))).mpr ⟨rfl, rfl⟩
  have ht := (split3_iff 0 (ofK ((0 : E).limb 0)) (ofK ((0 : E).limb 1))).mpr ⟨rfl, rfl⟩
  rw [← wYi_eq] at hs ht
  rw [zero_add] at ht
  have hv' : ∀ k, (hk : 714 ≤ k ∧ k < 740) → σ (.n k) = (lastVals s).getD (k - 714) 0 := by
    intro k hk
    have := hv (k - 714) (by omega)
    rwa [show 714 + (k - 714) = k by omega] at this
  simp only [sdLast, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true, h5]
  simp only [hv' _ (by norm_num : 714 ≤ 714 ∧ 714 < 740), hv' _ (by norm_num : 714 ≤ 715 ∧ 715 < 740),
    hv' _ (by norm_num : 714 ≤ 716 ∧ 716 < 740), hv' _ (by norm_num : 714 ≤ 717 ∧ 717 < 740),
    hv' _ (by norm_num : 714 ≤ 718 ∧ 718 < 740), hv' _ (by norm_num : 714 ≤ 719 ∧ 719 < 740),
    hv' _ (by norm_num : 714 ≤ 720 ∧ 720 < 740), hv' _ (by norm_num : 714 ≤ 721 ∧ 721 < 740),
    hv' _ (by norm_num : 714 ≤ 722 ∧ 722 < 740), hv' _ (by norm_num : 714 ≤ 723 ∧ 723 < 740),
    hv' _ (by norm_num : 714 ≤ 724 ∧ 724 < 740), hv' _ (by norm_num : 714 ≤ 725 ∧ 725 < 740),
    hv' _ (by norm_num : 714 ≤ 726 ∧ 726 < 740), hv' _ (by norm_num : 714 ≤ 727 ∧ 727 < 740),
    hv' _ (by norm_num : 714 ≤ 728 ∧ 728 < 740), hv' _ (by norm_num : 714 ≤ 729 ∧ 729 < 740),
    hv' _ (by norm_num : 714 ≤ 730 ∧ 730 < 740), hv' _ (by norm_num : 714 ≤ 731 ∧ 731 < 740),
    hv' _ (by norm_num : 714 ≤ 732 ∧ 732 < 740), hv' _ (by norm_num : 714 ≤ 733 ∧ 733 < 740),
    hv' _ (by norm_num : 714 ≤ 734 ∧ 734 < 740), hv' _ (by norm_num : 714 ≤ 735 ∧ 735 < 740),
    hv' _ (by norm_num : 714 ≤ 736 ∧ 736 < 740), hv' _ (by norm_num : 714 ≤ 737 ∧ 737 < 740),
    hv' _ (by norm_num : 714 ≤ 738 ∧ 738 < 740), hv' _ (by norm_num : 714 ≤ 739 ∧ 739 < 740),
    lastVals, Nat.reduceSub, List.getD_cons_succ, List.getD_cons_zero, and_true, true_and]
  exact ⟨ls, word_zero.symm, ⟨hs.1, hs.2.1⟩, ⟨hs.2.2, ht.1⟩, ⟨ht.2.1, ht.2.2⟩⟩

theorem sdBlk_bwd {rd : Reader} {σ : Val} {b : ℕ}
    (h1 : σ (bv b 2) = word (64 * (b + 1)) (if b + 1 = 22 then 4294967295 else 0) 0)
    (h2 : CompressCells ![σ (.n (cellIdx (4 * b))), σ (.n (cellIdx (4 * b + 1))),
        σ (.n (cellIdx (4 * b + 2))), σ (.n (cellIdx (4 * b + 3)))] (σ (bv b 0)) (σ (bv b 1))
        (σ (bv (b + 1) 0)) (σ (bv (b + 1) 1)) (σ (bv b 2))) :
    ∀ a ∈ sdBlk b, a.Holds rd σ := by
  simpa only [sdBlk, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true] using
    And.intro h1 h2

section
variable (args hdr cells : List E)

/-- Deferred cell `q`, the zero cell past the last. -/
def sdD (q : ℕ) : E := (cells ++ [0]).getD q 0

/-- The honest values below the chain. -/
def sdCore (k : ℕ) : E :=
  if k < 6 then args.getD k 0 else if k < 12 then hdr.getD (k - 6) 0 else
  if k < 714 then (pairVals (sdD cells (2 * ((k - 12) / 27))) (sdD cells (2 * ((k - 12) / 27) + 1))).getD
    ((k - 12) % 27) 0 else
  if k < 740 then (lastVals (sdD cells 52)).getD (k - 714) 0 else 0

/-- The metadata cell of block `b`. -/
def sdMd (b : ℕ) : E := metadataCell (64 * (b + 1)) (decide (b + 1 = 22))

/-- The state after `b` blocks. -/
def sdS (b : ℕ) : E × E :=
  digestScalars (chainRun paramIv (fun b => ![sdCore args hdr cells (cellIdx (4 * b)),
    sdCore args hdr cells (cellIdx (4 * b + 1)), sdCore args hdr cells (cellIdx (4 * b + 2)),
    sdCore args hdr cells (cellIdx (4 * b + 3))]) sdMd b)

/-- The honest values of `statement_digest`. -/
def sdVals (k : ℕ) : E :=
  if k < 741 then sdCore args hdr cells k else
  if k < 809 then [(sdS args hdr cells ((k - 741) / 3)).1, (sdS args hdr cells ((k - 741) / 3)).2,
    sdMd ((k - 741) / 3)].getD ((k - 741) % 3) 0 else
  [(sdS args hdr cells 22).1, (sdS args hdr cells 22).2].getD (k - 809) 0

theorem sdVals_core {k : ℕ} (hk : k < 741) : sdVals args hdr cells k = sdCore args hdr cells k := by
  simp [sdVals, hk]

theorem sdVals_bv (b r : ℕ) (hr : r < 3) (hb : 741 + 3 * b + r < 809) :
    sdVals args hdr cells (741 + 3 * b + r) =
      [(sdS args hdr cells b).1, (sdS args hdr cells b).2, sdMd b].getD r 0 := by
  unfold sdVals
  rw [ite_neg' (by omega), ite_pos' hb, show (741 + 3 * b + r - 741) / 3 = b by omega,
    show (741 + 3 * b + r - 741) % 3 = r by omega]

theorem sdCore_pair (p r : ℕ) (hp : p < 26) (hr : r < 27) :
    sdCore args hdr cells (12 + 27 * p + r) =
      (pairVals (sdD cells (2 * p)) (sdD cells (2 * p + 1))).getD r 0 := by
  unfold sdCore
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
    show (12 + 27 * p + r - 12) / 27 = p by omega, show (12 + 27 * p + r - 12) % 27 = r by omega]

theorem sdCore_last (r : ℕ) (hr : r < 26) :
    sdCore args hdr cells (714 + r) = (lastVals (sdD cells 52)).getD r 0 := by
  unfold sdCore
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
    show 714 + r - 714 = r by omega]

end

theorem statement_digest_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "statement_digest" args rets ↔ Meaning_statement_digest rd args rets := by
  rw [rel_of_find find_statement_digest]
  simp only [Fn.Sem, sdBody, holdsList_atoms, holdsList_ret, List.forall_mem_append,
    forall_mem_flatMap_range, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true,
    List.map_cons, List.map_nil, Meaning_statement_digest]
  constructor
  · rintro ⟨σ, hp, ⟨⟨⟨⟨⟨⟨h6, h7, h8, h9, h10, h11⟩, hpair⟩, hlast⟩, h740, h741, h742⟩, hblk⟩,
      h809, h810⟩, hr⟩
    obtain ⟨l714, e722, e731, e739⟩ := sdLast_fwd hlast
    -- the chain
    have hch := chain_eq_chainRun (n := 22) (h := paramIv)
      (blocks := fun b => ![σ (.n (cellIdx (4 * b))), σ (.n (cellIdx (4 * b + 1))),
        σ (.n (cellIdx (4 * b + 2))), σ (.n (cellIdx (4 * b + 3)))])
      (md := fun b => σ (bv b 2)) (st := fun b => (σ (bv b 0), σ (bv b 1)))
      (by simp only [bv, Nat.reduceMul, Nat.reduceAdd]; rw [h741, h742, iv0_word, iv1_word])
      (fun j hj => (sdBlk_fwd (hblk j hj)).2) 22 le_rfl
    have hcan : ∀ k < 88, IsCanonical128 (σ (.n (cellIdx k))) := by
      intro k hk
      have := (sdBlk_fwd (hblk (k / 4) (by omega))).2.1 ⟨k % 4, by omega⟩
      have hk4 : k = 4 * (k / 4) + k % 4 := by omega
      rcases (show k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 by omega) with h | h | h | h <;>
        simp only [h] at this <;> rw [hk4, h] <;> simpa using this
    have hc6 : cellIdx 0 = 6 := rfl
    have can : ∀ k < 6, IsCanonical128 (σ (.n (6 + k))) := fun k hk => by
      have := hcan k (by omega); rwa [cellIdx_hdr k hk] at this
    let seed := cellsDigest (σ (.n 6)) (σ (.n 7))
    let sig := cellsDigest (σ (.n 8)) (σ (.n 9))
    let da := cellsDigest (σ (.n 10)) (σ (.n 11))
    have dseed : digestScalars seed = (σ (.n 6), σ (.n 7)) := digestScalars_cellsDigest (can 0 (by omega)) (can 1 (by omega))
    have dsig : digestScalars sig = (σ (.n 8), σ (.n 9)) := digestScalars_cellsDigest (can 2 (by omega)) (can 3 (by omega))
    have dda : digestScalars da = (σ (.n 10), σ (.n 11)) := digestScalars_cellsDigest (can 4 (by omega)) (can 5 (by omega))
    let cells : List E := (List.range 53).map fun q => if q < 52 then σ (pv (q / 2) (q % 2)) else σ (.n 714)
    have hlen : cells.length = 53 := by simp [cells]
    have hD : ∀ q < 54, (cells ++ [0]).getD q 0 =
        if q < 52 then σ (pv (q / 2) (q % 2)) else if q = 52 then σ (.n 714) else 0 := by
      intro q hq
      rcases (show q < 53 ∨ q = 53 by omega) with h | h
      · rw [List.getD_eq_getElem _ _ (by simp [cells]; omega), List.getElem_append_left (by simp [cells]; omega)]
        simp only [cells, List.getElem_map, List.getElem_range]
        split_ifs <;> first | rfl | omega
      · subst h; simp [cells]
    refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 809), σ (.n 810),
      hp.symm, hr.symm, seed, sig, da, cells, hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [dseed, h6, h7]
    · rw [dsig]; exact h8
    · rw [dsig]; exact h9
    · rw [dda, h10, h11]
    · intro k hk
      have hk' : k < 53 := by simpa [cells] using hk
      simp only [cells, List.getElem_map, List.getElem_range]
      split_ifs with h
      · obtain ⟨q, r, hr2, rfl⟩ : ∃ q r, r < 2 ∧ k = 2 * q + r := ⟨k / 2, k % 2, by omega, by omega⟩
        rw [show (2 * q + r) / 2 = q by omega, show (2 * q + r) % 2 = r by omega]
        obtain ⟨la, lb, -⟩ := sdPair_fwd (hpair q (by omega))
        interval_cases r
        · simpa using la
        · exact lb
      · rw [show k = 52 by omega]; exact l714
    · simp only [bv, Nat.reduceMul, Nat.reduceAdd] at hch
      rw [h809, h810, hch]
      congr 1
      have hpq : ∀ p < 27, cellBytes (σ (.n (cellIdx (6 + 3 * p)))) ++
          cellBytes (σ (.n (cellIdx (6 + 3 * p + 1)))) ++ cellBytes (σ (.n (cellIdx (6 + 3 * p + 2)))) =
          eBytes ((cells ++ [0]).getD (2 * p) 0) ++ eBytes ((cells ++ [0]).getD (2 * p + 1) 0) := by
        intro p hp27
        rw [hD (2 * p) (by omega), hD (2 * p + 1) (by omega)]
        rcases (show p < 26 ∨ p = 26 by omega) with hp26 | rfl
        · obtain ⟨-, -, e8, e17, e26⟩ := sdPair_fwd (hpair p hp26)
          rw [cellIdx_A p hp26, cellIdx_B p hp26, cellIdx_C p hp26, e8, e17, e26, pair_bytes,
            ite_pos' (by omega), ite_pos' (by omega), show 2 * p / 2 = p by omega,
            show 2 * p % 2 = 0 by omega, show (2 * p + 1) / 2 = p by omega,
            show (2 * p + 1) % 2 = 1 by omega]
        · rw [show cellIdx (6 + 3 * 26) = 722 from rfl, show cellIdx (6 + 3 * 26 + 1) = 731 from rfl,
            show cellIdx (6 + 3 * 26 + 2) = 739 from rfl, e722, e731, e739, pair_bytes]
          simp
      rw [← sd_chainRun (fun k => σ (.n (cellIdx k))) seed sig da cells hlen
        (by show cellBytes (σ (.n 6)) ++ cellBytes (σ (.n 7)) = _; rw [digestBytes_eq, dseed])
        (by show cellBytes (σ (.n 8)) ++ cellBytes (σ (.n 9)) = _; rw [digestBytes_eq, dsig])
        (by show cellBytes (σ (.n 10)) ++ cellBytes (σ (.n 11)) = _; rw [digestBytes_eq, dda])
        hpq (by show σ (.n 740) = 0; rw [h740, word_zero]) hcan]
      exact chainRun_congr 22 (fun _ _ => rfl)
        (fun b hb => by rw [(sdBlk_fwd (hblk b hb)).1, word_metadata])
  · rintro ⟨seed0, seed1, sigp, da0, da1, dp, d0, d1, rfl, rfl, seed, sig, da, cells, hlen, hseed,
      hs0, hs1, hda, hcells, hd⟩
    change cells.length = 53 at hlen
    set args := [seed0, seed1, sigp, da0, da1, dp] with hargs
    set hdr := [seed0, seed1, (digestScalars sig).1, (digestScalars sig).2, da0, da1] with hhdr
    have hDq : ∀ q (hq : q < 53), sdD cells q = cells[q]'(by omega) := by
      intro q hq
      rw [sdD, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left]
    have hD53 : sdD cells 53 = 0 := by
      rw [sdD, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by omega)]
      simp [hlen]
    have hload : ∀ q < 53, LoadHolds rd dp q (sdD cells q) := fun q hq => by
      rw [hDq q hq]; exact hcells q (by omega)
    let c := fun k => sdCore args hdr cells (cellIdx k)
    have cA : ∀ p < 26, c (6 + 3 * p) =
        E.ofLimbs ((sdD cells (2 * p)).limb 0) ((sdD cells (2 * p)).limb 1) 0 := fun p hp => by
      show sdCore args hdr cells (cellIdx (6 + 3 * p)) = _
      rw [cellIdx_A p hp, sdCore_pair args hdr cells p 8 hp (by omega)]
      simp only [pairVals, List.getD_cons_succ, List.getD_cons_zero]
      exact (pair_cells (sdD cells (2 * p)) (sdD cells (2 * p + 1))).1
    have cB : ∀ p < 26, c (6 + 3 * p + 1) =
        E.ofLimbs ((sdD cells (2 * p)).limb 2) ((sdD cells (2 * p + 1)).limb 0) 0 := fun p hp => by
      show sdCore args hdr cells (cellIdx (6 + 3 * p + 1)) = _
      rw [cellIdx_B p hp, sdCore_pair args hdr cells p 17 hp (by omega)]
      simp only [pairVals, List.getD_cons_succ, List.getD_cons_zero]
      exact (pair_cells (sdD cells (2 * p)) (sdD cells (2 * p + 1))).2.1
    have cC : ∀ p < 26, c (6 + 3 * p + 2) =
        E.ofLimbs ((sdD cells (2 * p + 1)).limb 1) ((sdD cells (2 * p + 1)).limb 2) 0 := fun p hp => by
      show sdCore args hdr cells (cellIdx (6 + 3 * p + 2)) = _
      rw [cellIdx_C p hp, sdCore_pair args hdr cells p 26 hp (by omega)]
      simp only [pairVals, List.getD_cons_succ, List.getD_cons_zero]
      exact (pair_cells (sdD cells (2 * p)) (sdD cells (2 * p + 1))).2.2
    have cL : c 84 = E.ofLimbs ((sdD cells 52).limb 0) ((sdD cells 52).limb 1) 0 ∧
        c 85 = E.ofLimbs ((sdD cells 52).limb 2) ((0 : E).limb 0) 0 ∧
        c 86 = E.ofLimbs ((0 : E).limb 1) ((0 : E).limb 2) 0 := by
      refine ⟨?_, ?_, ?_⟩
      · show sdCore args hdr cells (714 + 8) = _
        rw [sdCore_last args hdr cells 8 (by omega)]
        simp only [lastVals, List.getD_cons_succ, List.getD_cons_zero]
        exact (pair_cells (sdD cells 52) 0).1
      · show sdCore args hdr cells (714 + 17) = _
        rw [sdCore_last args hdr cells 17 (by omega)]
        simp only [lastVals, List.getD_cons_succ, List.getD_cons_zero]
        have := (pair_cells (sdD cells 52) 0).2.1
        exact this
      · show sdCore args hdr cells (714 + 25) = _
        rw [sdCore_last args hdr cells 25 (by omega)]
        simp only [lastVals, List.getD_cons_succ, List.getD_cons_zero]
        have := (pair_cells (sdD cells 52) 0).2.2
        rwa [zero_add] at this
    have cH : ∀ k < 6, c k = hdr.getD k 0 := fun k hk => by
      show sdCore args hdr cells (cellIdx k) = _
      rw [cellIdx_hdr k hk]
      simp [sdCore, show ¬(6 + k < 6) by omega, show 6 + k < 12 by omega]
    have c87 : c 87 = 0 := by
      show sdCore args hdr cells 740 = 0
      simp [sdCore]
    have hcs := isCanonical128_digestScalars seed
    have hcg := isCanonical128_digestScalars sig
    have hcd := isCanonical128_digestScalars da
    rw [← hseed] at hcs
    rw [← hda] at hcd
    have hcan : ∀ k < 88, IsCanonical128 (c k) := by
      intro k hk
      rcases (show k < 6 ∨ 6 ≤ k ∧ k < 87 ∨ k = 87 by omega) with h | ⟨h1, h2⟩ | rfl
      · rw [cH k h]
        interval_cases k
        exacts [hcs.1, hcs.2, hcg.1, hcg.2, hcd.1, hcd.2]
      · obtain ⟨p, r, hr3, rfl⟩ : ∃ p r, r < 3 ∧ k = 6 + 3 * p + r := ⟨(k - 6) / 3, (k - 6) % 3, by omega, by omega⟩
        rcases (show p < 26 ∨ p = 26 by omega) with hp | rfl
        · interval_cases r
          · rw [Nat.add_zero, cA p hp]; rfl
          · rw [cB p hp]; rfl
          · rw [cC p hp]; rfl
        · interval_cases r
          · rw [cL.1]; rfl
          · rw [cL.2.1]; rfl
          · rw [cL.2.2]; rfl
      · rw [c87]; exact isCanonical128_zero
    have hpq : ∀ p < 27, cellBytes (c (6 + 3 * p)) ++ cellBytes (c (6 + 3 * p + 1)) ++
        cellBytes (c (6 + 3 * p + 2)) =
          eBytes ((cells ++ [0]).getD (2 * p) 0) ++ eBytes ((cells ++ [0]).getD (2 * p + 1) 0) := by
      intro p hp27
      rcases (show p < 26 ∨ p = 26 by omega) with hp | rfl
      · rw [cA p hp, cB p hp, cC p hp, pair_bytes]; rfl
      · rw [cL.1, cL.2.1, cL.2.2, pair_bytes]
        show _ = eBytes (sdD cells 52) ++ eBytes (sdD cells 53)
        rw [hD53]
    have hS22 : sdS args hdr cells 22 = (d0, d1) := by
      rw [hd]
      exact congrArg digestScalars (sd_chainRun c seed sig da cells hlen
        (by rw [cH 0 (by omega), cH 1 (by omega), digestBytes_eq, ← hseed]; rfl)
        (by rw [cH 2 (by omega), cH 3 (by omega), digestBytes_eq]; rfl)
        (by rw [cH 4 (by omega), cH 5 (by omega), digestBytes_eq, ← hda]; rfl) hpq c87 hcan)
    have h5 : sdVals args hdr cells 5 = dp := by simp [sdVals, sdCore, args]
    refine ⟨fun v => sdVals args hdr cells v.idx, rfl,
      ⟨⟨⟨⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun p hp => ?_⟩, ?_⟩, ?_, ?_, ?_⟩, fun b hb => ?_⟩, ?_, ?_⟩, ?_⟩
    · simp [sdVals, sdCore, args, hdr]
    · simp [sdVals, sdCore, args, hdr]
    · show LoadHolds rd (sdVals args hdr cells 2) 0 (sdVals args hdr cells 8)
      simpa [sdVals, sdCore, args, hdr] using hs0
    · show LoadHolds rd (sdVals args hdr cells 2) 1 (sdVals args hdr cells 9)
      simpa [sdVals, sdCore, args, hdr] using hs1
    · simp [sdVals, sdCore, args, hdr]
    · simp [sdVals, sdCore, args, hdr]
    · refine sdPair_bwd (s := sdD cells (2 * p)) (t := sdD cells (2 * p + 1)) (dp := dp)
        (fun r hr => ?_) h5 (hload _ (by omega)) (hload _ (by omega))
      show sdVals args hdr cells (12 + 27 * p + r) = _
      rw [sdVals_core args hdr cells (by omega), sdCore_pair args hdr cells p r hp hr]
    · refine sdLast_bwd (s := sdD cells 52) (dp := dp) (fun r hr => ?_) h5 (hload 52 (by omega))
      show sdVals args hdr cells (714 + r) = _
      rw [sdVals_core args hdr cells (by omega), sdCore_last args hdr cells r hr]
    · show sdVals args hdr cells 740 = _
      rw [sdVals_core args hdr cells (by omega), word_zero]
      simp [sdCore]
    · show sdVals args hdr cells (741 + 3 * 0 + 0) = _
      rw [sdVals_bv args hdr cells 0 0 (by omega) (by omega), iv0_word]
      rfl
    · show sdVals args hdr cells (741 + 3 * 0 + 1) = _
      rw [sdVals_bv args hdr cells 0 1 (by omega) (by omega), iv1_word]
      rfl
    · have hc : ∀ r < 4, sdVals args hdr cells (cellIdx (4 * b + r)) = c (4 * b + r) := by
        intro r hr
        rcases cellIdx_lt (4 * b + r) with h | h
        · exact sdVals_core args hdr cells h
        · omega
      refine sdBlk_bwd ?_ ?_
      · show sdVals args hdr cells (741 + 3 * b + 2) = _
        rw [sdVals_bv args hdr cells b 2 (by omega) (by omega), word_metadata]
        rfl
      · show CompressCells ![sdVals args hdr cells (cellIdx (4 * b + 0)),
          sdVals args hdr cells (cellIdx (4 * b + 1)), sdVals args hdr cells (cellIdx (4 * b + 2)),
          sdVals args hdr cells (cellIdx (4 * b + 3))] (sdVals args hdr cells (741 + 3 * b + 0))
          (sdVals args hdr cells (741 + 3 * b + 1)) (sdVals args hdr cells (741 + 3 * (b + 1) + 0))
          (sdVals args hdr cells (741 + 3 * (b + 1) + 1)) (sdVals args hdr cells (741 + 3 * b + 2))
        rw [hc 0 (by omega), hc 1 (by omega), hc 2 (by omega), hc 3 (by omega),
          sdVals_bv args hdr cells b 0 (by omega) (by omega),
          sdVals_bv args hdr cells b 1 (by omega) (by omega),
          sdVals_bv args hdr cells (b + 1) 0 (by omega) (by omega),
          sdVals_bv args hdr cells (b + 1) 1 (by omega) (by omega),
          sdVals_bv args hdr cells b 2 (by omega) (by omega)]
        refine (compressCells_chainRun (h := paramIv) (blocks := fun b => ![c (4 * b), c (4 * b + 1),
          c (4 * b + 2), c (4 * b + 3)]) (md := sdMd) (i := b) (fun r => ?_)
          (isCanonical128_metadataCell _ _)).mpr rfl
        fin_cases r
        exacts [hcan (4 * b) (by omega), hcan (4 * b + 1) (by omega), hcan (4 * b + 2) (by omega),
          hcan (4 * b + 3) (by omega)]
    · show sdVals args hdr cells 809 = sdVals args hdr cells (741 + 3 * 22 + 0)
      rw [sdVals_bv args hdr cells 22 0 (by omega) (by omega)]
      simp [sdVals]
    · show sdVals args hdr cells 810 = sdVals args hdr cells (741 + 3 * 22 + 1)
      rw [sdVals_bv args hdr cells 22 1 (by omega) (by omega)]
      simp [sdVals]
    · show [sdVals args hdr cells 809, sdVals args hdr cells 810] = _
      simp [sdVals, hS22]

end
end LeanVM.Guest.B1.Digest

namespace LeanVM.Guest.B1
export Digest (Meaning_statement_digest statement_digest_iff stmtDigestOf statementDigest_eq)
end LeanVM.Guest.B1
