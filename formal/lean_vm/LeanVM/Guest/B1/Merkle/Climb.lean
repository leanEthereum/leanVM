/-
  LeanVM.Guest.B1.Merkle.Climb

  Digests held in cells, `climb` at the deployed hash, and a cap leaf's ancestors.
-/

module

public import LeanVM.Guest.B1.Merkle.Meaning
public import LeanVM.Guest.B1.Opening.Meaning
public import LeanVM.Protocol.KeccakHash
public import LeanVM.Protocol.WithHash

/-!
# Climbing at the deployed hash

* `cellsBytes_digestScalars`: a digest's two cells are its 32 bytes; `hashesPair_digests`:
  `HashesPair` is `hashPair` (`LeanVM/Protocol/KeccakHash.lean`) of the digests the cells encode.
* `climbD_cons`, `climbD_append`: `climb` at the deployed hash, one level and a path in
  two parts.
* `capAnc D p j`: the ancestor `j` levels above the cap's leaf `p`, its node index in the cap.
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

end
end LeanVM.Guest.B1
