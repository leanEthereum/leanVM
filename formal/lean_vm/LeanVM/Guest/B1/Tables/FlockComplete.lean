/-
  LeanVM.Guest.B1.Tables.FlockComplete

  `verify_flock` complete, its memory and its loops: the honest words of its buffers, and the two
  loops holding over them.
-/

module

public import LeanVM.Guest.B1.Tables.FlockRun
public import LeanVM.Guest.B1.VerifySub.CBlocks

/-!
# `verify_flock`'s memory and loops, complete

`FlMem`: what the honest memory holds for the run on the state `cv` and the words `xs`: the
words at the cursor, the zerocheck's coordinates at `zerocheck_r` (`flE`), the squeezes' states
at `flock_pts`, round 1's words, the rounds' rows at `flock_rounds`, and the challenges and
slices the caller's buffers receive. `loop81_complete`, `loop82_complete`: the loops hold there.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig

@[expose] public section

/-- The zerocheck's state after `j` rounds. -/
abbrev flScAt (τ : ℕ) (cv : Digest) (xs : List E) (j : ℕ) : E × Digest :=
  scSt (flE τ cv) (flG xs) (flSt0 τ cv xs) j

/-- **The honest memory of `verify_flock`** for the run on the state `cv` and the words `xs`. -/
structure FlMem (rd : Reader) (τ : ℕ) (cv : Digest) (xs : List E)
    (cur zchis lrs zpart p11 p24 p40 p2220 : E) : Prop where
  words : ∀ k < flLen τ, LoadHolds rd cur k (xs.getD k 0)
  zr : ∀ j < τ + 8, LoadHolds rd p11 (6 + j) (flE τ cv j)
  pts : ∀ t ≤ τ + 1, LoadHolds rd p24 (26 + 2 * t) (digestScalars (sqCv^[t] cv)).1 ∧
    LoadHolds rd p24 (27 + 2 * t) (digestScalars (sqCv^[t] cv)).2
  p1 : ∀ i < 64, LoadHolds rd p40 i (xs.getD i 0)
  rnd : ∀ j, 7 ≤ j → j ≤ τ + 8 →
    LoadHolds rd p2220 (4 * j) (digestScalars (flScAt τ cv xs j).2).1 ∧
    LoadHolds rd p2220 (4 * j + 1) (digestScalars (flScAt τ cv xs j).2).2 ∧
    LoadHolds rd p2220 (4 * j + 2) (cur * gen ^ (64 + 2 * j)) ∧
    LoadHolds rd p2220 (4 * j + 3) (flScAt τ cv xs j).1
  chis : ∀ j < τ + 8, LoadHolds rd zchis j (scCh (flE τ cv) (flG xs) (flSt0 τ cv xs) j)
  rcs : ∀ j < 8, LoadHolds rd lrs j (lcCh (flG' τ xs) (flSt0' τ cv xs) j)
  sl : ∀ i < 64, LoadHolds rd zpart i (xs.getD (82 + 2 * (τ + 8) + i) 0)

theorem lh_back {rd : Reader} {p w : E} {a k n : ℕ} (h : LoadHolds rd p n w) (e : a + k = n) :
    LoadHolds rd (p * gen ^ a) k w := (loadHolds_mul_gen_pow rd p a k w).mpr (e ▸ h)

theorem flE_sampled (τ : ℕ) (cv : Digest) {t : ℕ} (ht : t ≤ τ) :
    flE τ cv (7 + t) = challengeOf (sqCv (sqCv^[t] cv)) := by
  simp only [flE]
  rw [show 7 + t = fixedChallenges.length + t by rw [fixedChallenges_length], getD_append_ge,
    sqAll_eq, getD_map_range _ _ (by omega)]

section
variable {rd : Reader} {τ : ℕ} {cv : Digest} {xs : List E} {cur zchis lrs zpart p11 p24 p40 p2220 : E}

/-- **`__loop81` holds** over the honest memory: the sampled coordinates' squeezes. -/
theorem loop81_complete (hτ : τ < 29)
    (hM : FlMem rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220) :
    coreProgram.Rel rd "__loop81" [gen ^ 13, gen ^ (τ + 14), p24, p11] [] := by
  refine (loop_iff (loop81_step rd (gen ^ (τ + 14)) p24 p11) 13).mpr
    ⟨τ + 14, by omega, rfl, fun j h1 h2 he => ?_, fun j h1 h2 => ?_⟩
  · have := gen_pow_inj' (by omega) (by omega) he; omega
  · obtain ⟨t, rfl⟩ : ∃ t, j = 13 + t := ⟨j - 13, by omega⟩
    obtain ⟨a0, a1⟩ := hM.pts t (by omega)
    obtain ⟨b0, b1⟩ := hM.pts (t + 1) (by omega)
    have hz := hM.zr (7 + t) (by omega)
    rw [flE_sampled τ cv (by omega)] at hz
    rw [Function.iterate_succ_apply'] at b0 b1
    unfold L81Body; rw [gen_pow_sq]
    exact ⟨sqCv^[t] cv, lh_back a0 (by omega), lh_back a1 (by omega), lh_back hz (by omega),
      lh_back b0 (by omega), lh_back b1 (by omega)⟩

/-- **`__loop82` holds** over the honest memory: the zerocheck's sampled rounds. -/
theorem loop82_complete (hτ : τ < 29)
    (hM : FlMem rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220) :
    coreProgram.Rel rd "__loop82" [gen ^ 7, gen ^ (τ + 8), p2220, p11, zchis] [] := by
  refine (loop_iff (loop82_step rd (gen ^ (τ + 8)) p2220 p11 zchis) 7).mpr
    ⟨τ + 8, by omega, rfl, fun j h1 h2 he => ?_, fun j h1 h2 => ?_⟩
  · have := gen_pow_inj' (by omega) (by omega) he; omega
  · obtain ⟨r0, r1, r2, r3⟩ := hM.rnd j h1 (by omega)
    obtain ⟨n0, n1, n2, n3⟩ := hM.rnd (j + 1) (by omega) (by omega)
    unfold L82Body; rw [gen_pow_quad]
    refine ⟨(flScAt τ cv xs j).2, cur * gen ^ (64 + 2 * j), (flScAt τ cv xs j).1, flE τ cv j,
      (flG xs j).1, (flG xs j).2, lh_back r0 (by omega), lh_back r1 (by omega),
      lh_back r2 (by omega), lh_back r3 (by omega), lh_back (hM.zr j (by omega)) (by omega),
      lh_back (hM.words _ (by unfold flLen; omega)) (by omega),
      lh_back (hM.words _ (by unfold flLen; omega)) (by omega),
      lh_back (hM.chis j (by omega)) (by omega), lh_back n0 (by omega), lh_back n1 (by omega), ?_,
      lh_back n3 (by omega)⟩
    rw [mul_assoc, ← pow_add]
    exact lh_back n2 (by omega)
end

end
end LeanVM.Guest.B1
