/-
  LeanVM.Guest.B1.Merkle.Climb

  The Merkle cap and a query's path below it climb to the root, as `climb` and `openOne` do.
-/

module

public import LeanVM.Guest.B1.Merkle.Meaning
public import LeanVM.Guest.B1.Opening.Meaning
public import LeanVM.Protocol.KeccakHash
public import LeanVM.Protocol.WithHash

/-!
# A query below the cap reaches the root (TRIAGE G #33, #34)

* `cellsBytes_digestScalars`: a digest's two cells are its 32 bytes; `hashesPair_digests`:
  `HashesPair` is `hashPair` (`LeanVM/Protocol/KeccakHash.lean`) of the digests the cells encode.
* `climbD_cons`, `climbD_append`: `climb` (V:492) at the deployed hash, one level and a path in
  two parts.
* `cap_climb`: under `verify_merkle_cap`'s meaning, a digest written at the cap's leaf `p` whose
  parent is flagged climbs, by `D` siblings of the cap, to the root: every flagged node's
  ancestors are flagged (an unflagged one pins its children's flags to zero) and so hashed.
* `query_opens_root`, `query_openOne`: a query's node below the cap (`QueryOpens`'s facts) climbs
  to the root by its path and the cap's siblings; the opening `⟨row, sibs ++ capSibs⟩` passes
  `openOne` (V:501) against the root.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Value.Keccak

@[expose] public section

/-! ## Digests in cells -/

theorem kBytes_ofLane (w : UInt64) : K.toBytes (K.ofLane w) = wordBytes w := rfl

/-- A digest's two cells are its 32 bytes. -/
theorem cellsBytes_digestScalars (d : Digest) :
    cellsBytes [(digestHalves d).1, (digestHalves d).2] = digestBytes d := by
  obtain ⟨⟨l⟩, hl⟩ := d
  match l, hl with
  | [a, b, c, e], _ =>
    simp [cellsBytes, cellBytes, digestHalves, digestBytes, limb_ofLimbs, kBytes_ofLane]

/-- Two cells encode a digest. -/
theorem exists_digest (a b : E) : ∃ d, (a, b) = digestHalves d :=
  ⟨_, (digestScalars_digestOfScalars (a, b)).symm⟩

theorem capDigestScalars_injective : Function.Injective digestHalves := fun a b h => by
  have ha := digestOfScalars_digestScalars a
  rw [h, digestOfScalars_digestScalars] at ha
  exact ha.symm

/-- **A hashed node is `hashPair` of its children's digests.** -/
theorem hashesPair_digests {l0 l1 r0 r1 p0 p1 : E} (h : HashesPair l0 l1 r0 r1 p0 p1) :
    ∃ dl dr, (l0, l1) = digestHalves dl ∧ (r0, r1) = digestHalves dr ∧
      (p0, p1) = digestHalves (hashPair dl dr) := by
  have hd := h
  obtain ⟨dl, hl⟩ := exists_digest l0 l1
  obtain ⟨dr, hr⟩ := exists_digest r0 r1
  refine ⟨dl, dr, hl, hr, ?_⟩
  rw [hd, hashPair, ← cellsBytes_digestScalars, ← cellsBytes_digestScalars, ← cellsBytes_append]
  simp only [Prod.ext_iff] at hl hr
  rw [hl.1, hl.2, hr.1, hr.2]
  rfl

/-! ## `climb` at the deployed hash -/

theorem climbD_nil (x : Digest) (q : ℕ) : climbD x q [] = x := rfl

theorem climbD_cons (x : Digest) (q : ℕ) (s : Digest) (ss : List Digest) :
    climbD x q (s :: ss) =
      climbD (if q % 2 = 0 then hashPair x s else hashPair s x) (q / 2) ss := by
  unfold climbD
  simp only [Compile.climbWithHash]
  split <;> rfl

theorem climbD_append (ss ts : List Digest) (x : Digest) (q : ℕ) :
    climbD x q (ss ++ ts) = climbD (climbD x q ss) (q / 2 ^ ss.length) ts := by
  induction ss generalizing x q with
  | nil => simp [climbD_nil]
  | cons s ss ih =>
    rw [List.cons_append, climbD_cons, climbD_cons, ih, List.length_cons, Nat.div_div_eq_div_mul,
      pow_succ, Nat.mul_comm]

theorem climbD_snoc (cs : List Digest) (s x : Digest) (q : ℕ) :
    climbD x q (cs ++ [s]) =
      if q / 2 ^ cs.length % 2 = 0 then hashPair (climbD x q cs) s
      else hashPair s (climbD x q cs) := by
  rw [climbD_append, climbD_cons, climbD_nil]

/-! ## Up the cap -/

theorem two_pow_sub_succ {D j : ℕ} (h : j < D) : 2 ^ (D - j) = 2 * 2 ^ (D - (j + 1)) := by
  rw [show D - j = D - (j + 1) + 1 by omega, pow_succ, Nat.mul_comm]

/-- The ancestor of the cap's leaf `p` (node `2^D + p`) `j` levels up. -/
def capAnc (D p j : ℕ) : ℕ := 2 ^ (D - j) + p / 2 ^ j

theorem capAnc_bounds {D p j : ℕ} (hp : p < 2 ^ D) (hj : j ≤ D) :
    2 ^ (D - j) ≤ capAnc D p j ∧ capAnc D p j < 2 * 2 ^ (D - j) := by
  have : p / 2 ^ j < 2 ^ (D - j) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos j), ← pow_add, Nat.sub_add_cancel hj]
    exact hp
  unfold capAnc
  generalize p / 2 ^ j = t at this ⊢
  omega

theorem capAnc_succ {D p j : ℕ} (hj : j < D) :
    capAnc D p j = 2 * capAnc D p (j + 1) + p / 2 ^ j % 2 := by
  unfold capAnc
  rw [two_pow_sub_succ hj, pow_succ, ← Nat.div_div_eq_div_mul]
  omega

theorem capAnc_last {D p : ℕ} (hp : p < 2 ^ D) : capAnc D p D = 1 := by
  unfold capAnc; rw [Nat.sub_self, pow_zero, Nat.div_eq_of_lt hp]

/-- **Up the cap**: under `verify_merkle_cap`'s meaning with the root `root`, a digest written at
the cap's leaf `p` whose parent is flagged climbs to the root by `D` siblings of the cap. -/
theorem cap_climb {D : ℕ} (hD : 2 ≤ D) {rd : Reader} {cap flags r0 r1 : E} {root : Digest}
    (hcap : MeaningVerifyMerkleCap D rd [cap, flags] [r0, r1])
    (hroot : (r0, r1) = digestHalves root) {p : ℕ} (hp : p < 2 ^ D) {x : Digest}
    (hx0 : LoadHolds rd cap (2 * (2 ^ D + p)) (digestHalves x).1)
    (hx1 : LoadHolds rd cap (2 * (2 ^ D + p) + 1) (digestHalves x).2)
    (hfl : LoadHolds rd flags (2 ^ (D - 1) + p / 2) 1) :
    ∃ cs : List Digest, cs.length = D ∧ climbD x p cs = root := by
  obtain ⟨cell, fl, hc, hf, hh, hpin, hret⟩ := hcap
  have hD2 : 2 ^ (D + 2) = 4 * 2 ^ D := by rw [pow_add]; ring
  have hpow : ∀ j, j < D → 2 ≤ 2 ^ (D - j) := fun j hj ↦ by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 1 ≤ D - j by omega)
    simpa using this
  have hle : ∀ j, 2 ^ (D - j) ≤ 2 ^ D := fun j ↦ Nat.pow_le_pow_right (by norm_num) (by omega)
  -- every ancestor strictly inside the cap is flagged
  have chain : ∀ j, 1 ≤ j → j < D → fl (capAnc D p j) ≠ 0 := by
    intro j hj1 hjD
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · show fl (capAnc D p 1) ≠ 0
        have hA : capAnc D p 1 = 2 ^ (D - 1) + p / 2 := by simp [capAnc]
        have hb := capAnc_bounds hp (show 1 ≤ D by omega)
        have hD1 := two_pow_sub_succ (show 0 < D by omega)
        simp only [Nat.sub_zero, Nat.zero_add] at hD1
        have h1 := (hf (capAnc D p 1) (by have := hpow 1 (by omega); omega)
          (by omega)).1
        rw [hA] at h1 ⊢
        rw [loadHolds_unique h1 hfl]
        exact one_ne_zero
      · intro h0
        have hprev := ih (by omega) (by omega)
        have hb := capAnc_bounds hp (show j + 1 ≤ D by omega)
        have hs := capAnc_succ (p := p) (show j < D by omega)
        have hD1 := two_pow_sub_succ (show j < D by omega)
        have hle' := hle j
        have hpw := hpow (j + 1) hjD
        have hle2 : 2 * 2 ^ (D - j) ≤ 2 ^ D := by
          rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        generalize p / 2 ^ j = t at hs
        obtain ⟨z0, z1⟩ := hpin (capAnc D p (j + 1)) (by omega) (by omega) h0
        have hbj := capAnc_bounds hp (show j ≤ D by omega)
        have hfj := (hf (capAnc D p j) (by omega) (by omega)).1
        apply hprev
        rcases Nat.mod_two_eq_zero_or_one t with hb0 | hb1
        · rw [hs, hb0, Nat.add_zero] at hfj ⊢
          exact loadHolds_unique hfj z0
        · rw [hs, hb1] at hfj ⊢
          exact loadHolds_unique hfj z1
  -- the cells climb, level by level
  have climb : ∀ j, j ≤ D → ∃ cs : List Digest, cs.length = j ∧
      (cell (2 * capAnc D p j), cell (2 * capAnc D p j + 1)) =
        digestHalves (climbD x p cs) := by
    intro j hjD
    induction j with
    | zero =>
      refine ⟨[], rfl, ?_⟩
      have e : capAnc D p 0 = 2 ^ D + p := by simp [capAnc]
      have hpD := Nat.one_le_two_pow (n := D)
      rw [e, climbD_nil, loadHolds_unique (hc _ (by omega) (by omega)) hx0,
        loadHolds_unique (hc _ (by omega) (by omega)) hx1]
    | succ j ih =>
      obtain ⟨cs, hl, hcs⟩ := ih (by omega)
      have hb := capAnc_bounds hp (show j + 1 ≤ D by omega)
      have hs := capAnc_succ (p := p) (show j < D by omega)
      have hle2 : 2 * 2 ^ (D - (j + 1)) ≤ 2 ^ D := by
        rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hflag : capAnc D p (j + 1) = 1 ∨ fl (capAnc D p (j + 1)) ≠ 0 := by
        rcases Nat.lt_or_ge (j + 1) D with h | h
        · exact Or.inr (chain (j + 1) (by omega) h)
        · left; rw [show j + 1 = D by omega]; exact capAnc_last hp
      obtain ⟨dl, dr, hl', hr', hpar⟩ := hashesPair_digests
        (hh (capAnc D p (j + 1)) (by have := Nat.one_le_two_pow (n := D - (j + 1)); omega)
          (by omega) hflag)
      rcases Nat.mod_two_eq_zero_or_one (p / 2 ^ j) with hb0 | hb1
      · refine ⟨cs ++ [dr], by simp [hl], ?_⟩
        rw [hs, hb0, Nat.add_zero, show 2 * (2 * capAnc D p (j + 1)) = 4 * capAnc D p (j + 1) by
          ring] at hcs
        have hy : dl = climbD x p cs := capDigestScalars_injective (hl'.symm.trans hcs)
        rw [climbD_snoc, hl, ite_pos' hb0, ← hy]
        exact hpar
      · refine ⟨cs ++ [dl], by simp [hl], ?_⟩
        rw [hs, hb1, show 2 * (2 * capAnc D p (j + 1) + 1) = 4 * capAnc D p (j + 1) + 2 by
          ring] at hcs
        have hy : dr = climbD x p cs := capDigestScalars_injective (hr'.symm.trans hcs)
        rw [climbD_snoc, hl, ite_neg' (by omega), ← hy]
        exact hpar
  obtain ⟨cs, hl, hcs⟩ := climb D le_rfl
  rw [capAnc_last hp] at hcs
  simp only [List.cons.injEq, and_true] at hret
  refine ⟨cs, hl, capDigestScalars_injective ?_⟩
  rw [← hcs, ← hroot, hret.1, hret.2]

/-! ## A query reaches the root -/

/-- **A query below the cap reaches the root** (`QueryOpens`'s cap writes and flag): with the cap
checked (`verify_merkle_cap`'s meaning, root `root`), the node a path of `depth - D` siblings
reaches from the leaf `leaf` at the position `q < 2^depth`, written at the cap's leaf
`q / 2^(depth - D)` with its parent flagged, climbs on by `D` siblings of the cap to the root. -/
theorem query_opens_root {D depth : ℕ} (hD : 2 ≤ D) (hDd : D ≤ depth) {rd : Reader}
    {cap flags r0 r1 : E} {root : Digest}
    (hcap : MeaningVerifyMerkleCap D rd [cap, flags] [r0, r1])
    (hroot : (r0, r1) = digestHalves root) {q : ℕ} (hq : q < 2 ^ depth) {leaf : Digest}
    {sibs : List Digest} (hsl : sibs.length = depth - D)
    (h0 : LoadHolds rd cap (2 * (2 ^ D + q / 2 ^ (depth - D)))
      (digestHalves (climbD leaf q sibs)).1)
    (h1 : LoadHolds rd cap (2 * (2 ^ D + q / 2 ^ (depth - D)) + 1)
      (digestHalves (climbD leaf q sibs)).2)
    (hfl : LoadHolds rd flags (2 ^ (D - 1) + q / 2 ^ (depth - D + 1)) 1) :
    ∃ capSibs : List Digest, capSibs.length = D ∧ climbD leaf q (sibs ++ capSibs) = root := by
  have hp : q / 2 ^ (depth - D) < 2 ^ D := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.add_sub_cancel' hDd]
    exact hq
  have hf2 : q / 2 ^ (depth - D + 1) = q / 2 ^ (depth - D) / 2 := by
    rw [Nat.div_div_eq_div_mul, pow_succ]
  rw [hf2] at hfl
  obtain ⟨cs, hcl, hc⟩ := cap_climb hD hcap hroot hp h0 h1 hfl
  exact ⟨cs, hcl, by rw [climbD_append, hsl, hc]⟩

end
end LeanVM.Guest.B1
