/-
  LeanVM.Guest.B1.Tables.Flock

  B1 for `verify_flock`: soundness in `verify_sub`'s shape (`SoundFlock`).
-/

module

public import LeanVM.Guest.B1.Tables.FlockAlg
public import LeanVM.Guest.B1.VerifySub.Interface
public import LeanVM.Guest.B1.Tables.Placement

/-!
# `verify_flock` (TRIAGE #40)

`verify_flock(fs0, fs1, cursor, g^τ, zerocheck_chis, lincheck_rs, z_partial)` (G:1827-1963) runs
`verifyFlock (.claimed c)` (V:1997) on `14 + τ` variables, in the specification's order. The
proof reads the body's segments (`verify_flock_holds`) phase by phase:

* the prelude and `__loop81`: the `τ + 1` sampled coordinates, `sqAll (τ + 1)` from the state
  (`fl_sampled`);
* round 1's words and the skip challenge `z` (`fl_round1`);
* the interpolation from the numerators (`lag64_phi`, `interp_eq`);
* the seven fixed rounds and `__loop82`'s sampled ones: `scSt` over `fixedChallenges ++ sampled`
  (`fl_rounds`);
* the final evaluations, `alpha`, the lincheck's eight rounds (`lcSt`), the slices;
* the terminal identity from the deferred `matpart` (`cslice_eq`, `colWeight_pin`).

`runs_verifyFlock` assembles the run for every `ev` taking `matpart` for the matrices.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

theorem word_g13 : word 8192 0 0 = gen ^ 13 := word_two_pow (a := 13) (by decide)
theorem word_g14 : word 16384 0 0 = gen ^ 14 := word_two_pow (a := 14) (by decide)
theorem word_g26 : word 67108864 0 0 = gen ^ 26 := word_two_pow (a := 26) (by decide)
theorem word_g7 : word 128 0 0 = gen ^ 7 := word_two_pow (a := 7) (by decide)
theorem word_g8 : word 256 0 0 = gen ^ 8 := word_two_pow (a := 8) (by decide)
theorem word_g28 : word 268435456 0 0 = gen ^ 28 := word_two_pow (a := 28) (by decide)

theorem lh_off {rd : Reader} {p w : E} {a k : ℕ} (h : LoadHolds rd (p * gen ^ a) k w) :
    LoadHolds rd p (a + k) w := (loadHolds_mul_gen_pow rd p a k w).mp h

theorem lh_off0 {rd : Reader} {p w : E} {a : ℕ} (h : LoadHolds rd (p * gen ^ a) 0 w) :
    LoadHolds rd p a w := (loadHolds_mul_gen_pow rd p a 0 w).mp h

theorem lh_off1 {rd : Reader} {p w : E} {a : ℕ} (h : LoadHolds rd (p * gen ^ a) 1 w) :
    LoadHolds rd p (a + 1) w := (loadHolds_mul_gen_pow rd p a 1 w).mp h

theorem lh_at {rd : Reader} {p w : E} {a k n : ℕ} (h : LoadHolds rd (p * gen ^ a) k w)
    (e : a + k = n) : LoadHolds rd p n w := e ▸ lh_off h

theorem lh_eq {rd : Reader} {p w : E} {n m : ℕ} (h : LoadHolds rd p n w) (e : n = m) :
    LoadHolds rd p m w := e ▸ h

theorem gen_pow_quad (j : ℕ) : gen ^ j * gen ^ j * (gen ^ j * gen ^ j) = gen ^ (4 * j) := by
  rw [← pow_add, ← pow_add]; congr 1; omega

theorem gen_pow_sq (j : ℕ) : gen ^ j * gen ^ j = gen ^ (2 * j) := by rw [← pow_add, two_mul]

theorem gen_pow_ne_of_lt {a b : ℕ} (hab : a < b) (hb : b < 2 ^ 63) : gen ^ a + gen ^ b ≠ 0 := by
  intro h
  have := gen_pow_inj' (by omega) hb (e_add_eq_zero_iff.mp h)
  omega

/-- `n` squeezes as an iterate: the challenges and the state. -/
theorem sqAll_eq : ∀ (n : ℕ) (cv : Digest),
    sqAll n cv = ((List.range n).map fun t => challengeOf (sqCv (sqCv^[t] cv)), sqCv^[n] cv)
  | 0, cv => rfl
  | n + 1, cv => by
    rw [sqAll, sqAll_eq n (sqCv cv), List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Function.iterate_zero_apply, Function.iterate_succ_apply, Function.comp_def]

/-! ## The prelude and `__loop81` -/

section
variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- What the prelude asks. -/
theorem fl_p0 {τ : ℕ} (hτ : σ (.n 3) = gen ^ τ) (h : Stmt.HoldsList C rd σ flP0 True kret) :
    σ (.n 7) = σ (.n 0) ∧ σ (.n 8) = σ (.n 1) ∧
      (∀ i < 7, LoadHolds rd (σ (.n 11)) (6 + i) (fixedWords.getD i 0)) ∧
      LoadHolds rd (σ (.n 24)) 26 (σ (.n 7)) ∧ LoadHolds rd (σ (.n 24)) 27 (σ (.n 8)) ∧
      (gen ^ 13 + gen ^ (τ + 14) ≠ 0 →
        C "__loop81" [gen ^ 13, gen ^ (τ + 14), σ (.n 24), σ (.n 11)] []) ∧
      LoadHolds rd (σ (.n 24)) (2 * (τ + 14)) (σ (.n 38)) ∧
      LoadHolds rd (σ (.n 24)) (2 * (τ + 14) + 1) (σ (.n 39)) := by
  simp only [flP0, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and,
    and_true, word_g13, word_g14, word_g26] at h
  obtain ⟨h7, h8, c9, m10, c12, l12, c13, l13, c14, l14, c15, l15, c16, l16, c17, l17, c18, l18,
    c19, m20, c21, m22, m23, c25, m26, l7, l8, c27, c28, m29, a30, c31, c32, m33, -, hcall, c34,
    m35, m36, m37, l38, l39⟩ := h
  have hN : σ (.n 33) = gen ^ (τ + 14) := by rw [m33, hτ, c32, ← pow_add]
  have h37 : σ (.n 37) = σ (.n 24) * gen ^ (2 * (τ + 14)) := by
    rw [m37, m36, m35, hτ, c34, ← pow_add, gen_pow_sq]
  refine ⟨h7, h8, fun i hi => ?_, ?_, ?_, fun hne => ?_, ?_, ?_⟩
  · interval_cases i
    · rw [c12] at l12; exact l12
    · rw [c13] at l13; exact l13
    · rw [c14] at l14; exact l14
    · rw [c15] at l15; exact l15
    · rw [c16] at l16; exact l16
    · rw [c17] at l17; exact l17
    · rw [c18] at l18; exact l18
  · rw [m26, c25] at l7; exact lh_off0 l7
  · rw [m26, c25] at l8; exact lh_off1 l8
  · have := hcall (by rw [a30, c27, m29, hτ, c28, ← pow_add]; exact hne)
    rw [c31, hN] at this; exact this
  · rw [h37] at l38; exact lh_off0 l38
  · rw [h37] at l39; exact lh_off1 l39

end

/-- **The sampled coordinates** (G:1852-1861): from the state `cv0` in row `13` of `pts`, the
loop leaves challenge `t` of `sqAll (τ + 1) cv0` at `zr[13 + t]` and its final state in row
`τ + 14`. -/
theorem fl_sampled {rd : Reader} {τ : ℕ} (hτ : τ < 29) {pts zr : E} {cv0 : Digest}
    (l0 : LoadHolds rd pts 26 (digestScalars cv0).1)
    (l1 : LoadHolds rd pts 27 (digestScalars cv0).2)
    (hloop : coreProgram.Rel rd "__loop81" [gen ^ 13, gen ^ (τ + 14), pts, zr] []) :
    (∀ t ≤ τ, LoadHolds rd zr (13 + t) (challengeOf (sqCv (sqCv^[t] cv0)))) ∧
      LoadHolds rd pts (2 * (τ + 14)) (digestScalars (sqCv^[τ + 1] cv0)).1 ∧
      LoadHolds rd pts (2 * (τ + 14) + 1) (digestScalars (sqCv^[τ + 1] cv0)).2 := by
  obtain ⟨m, hm, hN, hfirst, hall⟩ :=
    (loop_iff (loop81_step rd (gen ^ (τ + 14)) pts zr) 13).mp hloop
  have hm' : m = τ + 14 := by
    rcases Nat.lt_or_ge (τ + 14) m with h | h
    · exact absurd rfl (hfirst (τ + 14) (by omega) h)
    · exact (gen_pow_inj' (by omega) (by omega) hN).symm
  subst hm'
  have key : ∀ t ≤ τ + 1, LoadHolds rd pts (2 * (13 + t)) (digestScalars (sqCv^[t] cv0)).1 ∧
      LoadHolds rd pts (2 * (13 + t) + 1) (digestScalars (sqCv^[t] cv0)).2 ∧
      (t ≤ τ → LoadHolds rd zr (13 + t) (challengeOf (sqCv (sqCv^[t] cv0)))) := by
    intro t ht
    induction t with
    | zero =>
      refine ⟨l0, l1, fun _ => ?_⟩
      obtain ⟨cv, a0, a1, a2, -, -⟩ := hall 13 le_rfl (by omega)
      rw [gen_pow_sq] at a0 a1
      have e0 := loadHolds_unique (lh_off0 a0) l0
      have e1 := loadHolds_unique (lh_off1 a1) l1
      obtain rfl := digestScalars_injective (Prod.ext e0 e1)
      exact lh_off0 a2
    | succ t ih =>
      obtain ⟨i0, i1, -⟩ := ih (by omega)
      obtain ⟨cv, a0, a1, a2, a3, a4⟩ := hall (13 + t) (by omega) (by omega)
      rw [gen_pow_sq] at a0 a1 a3 a4
      obtain rfl := digestScalars_injective
        (Prod.ext (loadHolds_unique (lh_off0 a0) i0) (loadHolds_unique (lh_off1 a1) i1))
      have a3' := lh_off a3
      have a4' := lh_off a4
      rw [show 2 * (13 + t) + 2 = 2 * (13 + (t + 1)) by omega,
        ← Function.iterate_succ_apply' sqCv t cv0] at a3'
      rw [show 2 * (13 + t) + 3 = 2 * (13 + (t + 1)) + 1 by omega,
        ← Function.iterate_succ_apply' sqCv t cv0] at a4'
      refine ⟨a3', a4', fun ht' => ?_⟩
      obtain ⟨cv', b0, b1, b2, -, -⟩ := hall (13 + (t + 1)) (by omega) (by omega)
      rw [gen_pow_sq] at b0 b1
      obtain rfl := digestScalars_injective
        (Prod.ext (loadHolds_unique (lh_off0 b0) a3') (loadHolds_unique (lh_off1 b1) a4'))
      exact lh_off0 b2
  obtain ⟨k0, k1, -⟩ := key (τ + 1) le_rfl
  refine ⟨fun t ht => (key t (by omega)).2.2 ht, ?_, ?_⟩
  · rw [show 2 * (13 + (τ + 1)) = 2 * (τ + 14) by omega] at k0; exact k0
  · rw [show 2 * (13 + (τ + 1)) = 2 * (τ + 14) by omega] at k1; exact k1

/-! ## Runs of `fs_next` blocks -/

section
variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

theorem obsAll_snoc (cv : Digest) (xs : List E) (x : E) :
    obsAll cv (xs ++ [x]) = obsCv (obsAll cv xs) x := by
  simp [obsAll, List.foldl_append]

/-- **A run of `fs_next` blocks** (each followed by its own statements `extra i`): the words are
read and the chain absorbs them in order. -/
theorem fsNext_run (sIdx bIdx off : ℕ → ℕ) (cur : V) (extra : ℕ → List Stmt) {n : ℕ}
    (hblk : ∀ i < n, Stmt.HoldsList C rd σ
      (fsNextT (.n (sIdx i)) (.n (sIdx i + 1)) cur (off i) (bIdx i) ++ extra i) True kret)
    (hs : ∀ i, sIdx (i + 1) = bIdx i + 13) {cv : Digest}
    (h0 : (σ (.n (sIdx 0)), σ (.n (sIdx 0 + 1))) = digestScalars cv) :
    (∀ i < n, LoadHolds rd (σ cur) (off i) (σ (.n (bIdx i))) ∧
      Stmt.HoldsList C rd σ (extra i) True kret) ∧
      (σ (.n (sIdx n)), σ (.n (sIdx n + 1))) =
        digestScalars (obsAll cv ((List.range n).map fun i => σ (.n (bIdx i)))) := by
  induction n with
  | zero => exact ⟨fun i hi => absurd hi (by omega), h0⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hblk i (by omega)
    have hb := hblk n (by omega)
    rw [holdsList_append, holdsList_noRet _ rfl] at hb
    obtain ⟨l, hc⟩ := fsNext_chain hb.1 h2
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases Nat.lt_or_ge i n with h | h
      · exact h1 i h
      · obtain rfl : i = n := by omega
        exact ⟨l, hb.2⟩
    · rw [hs, List.range_succ, List.map_append, List.map_singleton, obsAll_snoc, ← hc]

end

/-! ## Round 1, the skip challenge and the interpolation -/

section
variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- Round 1's words (G:1864-1866), from the state `cv1`. -/
theorem fl_round1 (h : ∀ i < 64, Stmt.HoldsList C rd σ (rd1Blk i) True kret) {cv1 : Digest}
    (hcv : (σ (.n 38), σ (.n 39)) = digestScalars cv1) :
    (∀ i < 64, LoadHolds rd (σ (.n 2)) i (σ (.n (41 + 15 * i))) ∧
      LoadHolds rd (σ (.n 40)) i (σ (.n (41 + 15 * i)))) ∧
      (σ (.n 999), σ (.n 1000)) =
        digestScalars (obsAll cv1 ((List.range 64).map fun i => σ (.n (41 + 15 * i)))) := by
  obtain ⟨h1, h2⟩ := fsNext_run rd1S (fun i => 41 + 15 * i) (fun i => i) (.n 2)
    (fun i => [.atom (.load (.n (41 + 15 * i)) (.n 40) i)]) (n := 64) h
    (fun i => by simp only [rd1S, Nat.add_one_ne_zero, ↓reduceIte]; omega) hcv
  refine ⟨fun i hi => ⟨(h1 i hi).1, ?_⟩, h2⟩
  have := (h1 i hi).2
  simpa [Stmt.HoldsList, Stmt.Holds, Atom.Holds] using this

theorem lgOut_hi : lgOut (.n 1014) (phi8From 64) 1015 = 1401 := by decide +kernel

theorem lgOut_lo : lgOut (.n 1014) (phi8From 0) 2273 = 2655 := by decide +kernel

theorem phi_zero : phi 0 = 0 := by
  have := word_phi8Words (j := 0) (by decide)
  rw [← this]; exact word_zero

/-- The interpolation's sum (G:1873-1875): the lower half's product of `z + φ(j)` and the
numerators against round 1's words. -/
theorem fl_interp (h : ∀ i < 64, Stmt.HoldsList C rd σ (ipBlk i) True kret) {p : ℕ → E}
    (hp : ∀ i < 64, LoadHolds rd (σ (.n 40)) i (p i)) :
    σ (.n 1841) = ∏ j ∈ Finset.range 64, (σ (.n 1014) + phi j) ∧
      σ (.n 1844) = ∑ j ∈ Finset.range 64, σ (.n (1401 + j)) * p j := by
  have key : ∀ i < 64,
      σ (.n (if i = 0 then 1014 else 1463 + 6 * i)) =
        ∏ j ∈ Finset.range (i + 1), (σ (.n 1014) + phi j) ∧
      σ (.n (1466 + 6 * i)) = ∑ j ∈ Finset.range (i + 1), σ (.n (1401 + j)) * p j := by
    intro i hi
    induction i with
    | zero =>
      have h0 := h 0 (by omega)
      simp only [ipBlk, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h0
      obtain ⟨l, m⟩ := h0
      refine ⟨by simp [phi_zero], ?_⟩
      rw [Finset.sum_range_one, m, loadHolds_unique l (hp 0 (by omega))]
    | succ i ih =>
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hi1 := h (i + 1) hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · simp only [ipBlk, Nat.reduceAdd, Nat.reduceMul, ↓reduceIte, Stmt.HoldsList, Stmt.Holds,
          Atom.Holds, and_true, Nat.one_ne_zero] at hi1 ih1 ih2
        obtain ⟨c0, a1, m2, l3, m4, a5⟩ := hi1
        refine ⟨?_, ?_⟩
        · show σ (.n 1469) = _
          rw [m2, a1, c0, word_phi8Words (by omega), Finset.prod_range_succ, Finset.prod_range_one,
            phi_zero, add_zero]
        · show σ (.n 1472) = _
          rw [a5, m4, loadHolds_unique l3 (hp 1 hi), Finset.sum_range_succ, ih2]
      · have n1 : i + 1 ≠ 1 := by omega
        have n0 : i ≠ 0 := by omega
        simp only [ipBlk, Nat.add_one_ne_zero, n1, n0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds,
          Atom.Holds, and_true] at hi1 ih1
        obtain ⟨c0, a1, m2, l3, m4, a5⟩ := hi1
        rw [show 1457 + 6 * (i + 1) = 1463 + 6 * i by omega] at m2
        rw [show 1460 + 6 * (i + 1) = 1466 + 6 * i by omega] at a5
        refine ⟨?_, ?_⟩
        · rw [ite_neg' (Nat.add_one_ne_zero i), m2, a1, c0, word_phi8Words (by omega),
            Finset.prod_range_succ, ih1]
        · rw [a5, m4, loadHolds_unique l3 (hp (i + 1) hi), Finset.sum_range_succ, ih2]
  obtain ⟨k1, -⟩ := key 63 (by omega)
  obtain ⟨-, k2⟩ := key 63 (by omega)
  exact ⟨k1, k2⟩

end

/-! ## The fixed rounds -/

section
variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

theorem hl_app {a b : List Stmt} (ha : Stmt.noRetList a = true) :
    Stmt.HoldsList C rd σ (a ++ b) True kret ↔
      Stmt.HoldsList C rd σ a True kret ∧ Stmt.HoldsList C rd σ b True kret := by
  rw [holdsList_append, holdsList_noRet _ ha]

/-- **Fixed round `i`** (G:1879-1886) from the state `cv`: its equality factor at
`zerocheck_r[g^(6+i)]`, its two words at the cursor's offsets `64 + 2i`, `65 + 2i`, and
`scStep`'s challenge (stored at `zerocheck_chis[g^i]`), claim and state. -/
theorem frBlk_step (i : ℕ) (h : Stmt.HoldsList C rd σ (frBlk i) True kret) {cv : Digest}
    (hcv : (σ (.n (frS i)), σ (.n (frS i + 1))) = digestScalars cv) :
    LoadHolds rd (σ (.n 11)) (6 + i) (σ (.n (frB i))) ∧
      LoadHolds rd (σ (.n 2)) (64 + 2 * i) (σ (.n (frB i + 1))) ∧
      LoadHolds rd (σ (.n 2)) (65 + 2 * i) (σ (.n (frB i + 16))) ∧
      LoadHolds rd (σ (.n 4)) i
        (scStep (σ (.n (frB i))) (σ (.n (frB i + 1)), σ (.n (frB i + 16))) (σ (.n (frC i)), cv)).1 ∧
      σ (.n (frB i + 51)) =
        (scStep (σ (.n (frB i))) (σ (.n (frB i + 1)), σ (.n (frB i + 16))) (σ (.n (frC i)), cv)).2.1 ∧
      (σ (.n (frB i + 39)), σ (.n (frB i + 40))) = digestScalars
        (scStep (σ (.n (frB i))) (σ (.n (frB i + 1)), σ (.n (frB i + 16))) (σ (.n (frC i)), cv)).2.2 := by
  simp only [frBlk, holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
  obtain ⟨lB, g1l, f1⟩ := h
  rw [holds_fsCompressT _ _ _ _ (by decide)] at f1
  obtain ⟨⟨cv1, hcv1, e1⟩, f2⟩ := f1
  rw [holds_fsNextT] at f2
  obtain ⟨⟨g2l, cv2, hcv2, e2⟩, a31, m32, a33, sq⟩ := f2
  rw [holds_squeezeT] at sq
  obtain ⟨⟨cv3, hcv3, e3⟩, l47, m48, a49, m50, a51⟩ := sq
  have q1 : cv1 = cv := digestScalars_injective (hcv1.symm.trans hcv)
  rw [q1] at e1
  have c1 : (σ (.n (frB i + 14)), σ (.n (frB i + 15))) =
      digestScalars (obsCv cv (σ (.n (frB i + 1)))) := by
    have a := e1 12 (by omega) (by omega)
    have b := e1 13 (by omega) (by omega)
    rw [show frB i + 1 + 1 + 12 = frB i + 14 by omega] at a
    rw [show frB i + 1 + 1 + 13 = frB i + 15 by omega] at b
    exact Prod.ext a b
  have q2 := digestScalars_injective (hcv2.symm.trans c1)
  rw [q2] at e2
  have c2 : (σ (.n (frB i + 29)), σ (.n (frB i + 30))) =
      digestScalars (obsCv (obsCv cv (σ (.n (frB i + 1)))) (σ (.n (frB i + 16)))) := by
    have a := e2 12 (by omega) (by omega)
    have b := e2 13 (by omega) (by omega)
    rw [show frB i + 16 + 1 + 12 = frB i + 29 by omega] at a
    rw [show frB i + 16 + 1 + 13 = frB i + 30 by omega] at b
    exact Prod.ext a b
  have q3 := digestScalars_injective (hcv3.symm.trans c2)
  rw [q3] at e3
  have c3 : (σ (.n (frB i + 39)), σ (.n (frB i + 40))) = digestScalars
      (sqCv (obsCv (obsCv cv (σ (.n (frB i + 1)))) (σ (.n (frB i + 16))))) := by
    have a := e3 5 (by omega)
    have b := e3 6 (by omega)
    rw [show frB i + 34 + 5 = frB i + 39 by omega] at a
    rw [show frB i + 34 + 6 = frB i + 40 by omega] at b
    exact Prod.ext a b
  have ch : σ (.n (frB i + 47)) =
      challengeOf (sqCv (obsCv (obsCv cv (σ (.n (frB i + 1)))) (σ (.n (frB i + 16))))) := by
    have a := e3 13 (by omega)
    rw [show frB i + 34 + 13 = frB i + 47 by omega] at a
    exact a
  refine ⟨lB, g1l, g2l, ?_, ?_, c3⟩
  · show LoadHolds rd (σ (.n 4)) i
      (challengeOf (sqCv (obsCv (obsCv cv (σ (.n (frB i + 1)))) (σ (.n (frB i + 16))))))
    rw [← ch]; exact l47
  · show σ (.n (frB i + 51)) = σ (.n (frC i)) + σ (.n (frB i)) * (σ (.n (frB i + 1)) +
      σ (.n (frB i + 16))) +
      challengeOf (sqCv (obsCv (obsCv cv (σ (.n (frB i + 1)))) (σ (.n (frB i + 16))))) *
        (σ (.n (frB i + 1)) +
          challengeOf (sqCv (obsCv (obsCv cv (σ (.n (frB i + 1)))) (σ (.n (frB i + 16))))) *
            σ (.n (frB i + 16)))
    rw [← ch, a51, m50, a49, m48, a33, m32, a31]

end

/-! ## The lincheck's rounds -/

section
variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **Lincheck round `i`** (G:1931-1937) from the state `cv`: its two words at offsets
`2 + 2i`, `3 + 2i` of the cursor `σ 2240`, and `lcStep`'s challenge (stored at
`lincheck_rs[g^i]`), claim and state. -/
theorem lcBlk_step (i : ℕ) (h : Stmt.HoldsList C rd σ (lcBlk i) True kret) {cv : Digest}
    (hcv : (σ (.n (lcS i)), σ (.n (lcS i + 1))) = digestScalars cv) :
    LoadHolds rd (σ (.n 2240)) (2 + 2 * i) (σ (.n (lcB i))) ∧
      LoadHolds rd (σ (.n 2240)) (3 + 2 * i) (σ (.n (lcB i + 15))) ∧
      LoadHolds rd (σ (.n 5)) i
        (lcStep (σ (.n (lcB i)), σ (.n (lcB i + 15))) (σ (.n (lcC i)), cv)).1 ∧
      σ (.n (lcB i + 48)) = (lcStep (σ (.n (lcB i)), σ (.n (lcB i + 15))) (σ (.n (lcC i)), cv)).2.1 ∧
      (σ (.n (lcB i + 36)), σ (.n (lcB i + 37))) = digestScalars
        (lcStep (σ (.n (lcB i)), σ (.n (lcB i + 15))) (σ (.n (lcC i)), cv)).2.2 := by
  simp only [lcBlk, holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
  obtain ⟨g1l, f1⟩ := h
  rw [holds_fsCompressT _ _ _ _ (by decide)] at f1
  obtain ⟨⟨cv1, hcv1, e1⟩, f2⟩ := f1
  rw [holds_fsNextT] at f2
  obtain ⟨⟨g2l, cv2, hcv2, e2⟩, a30, sq⟩ := f2
  rw [holds_squeezeT] at sq
  obtain ⟨⟨cv3, hcv3, e3⟩, l44, m45, a46, m47, a48⟩ := sq
  have q1 : cv1 = cv := digestScalars_injective (hcv1.symm.trans hcv)
  rw [q1] at e1
  have c1 : (σ (.n (lcB i + 13)), σ (.n (lcB i + 14))) =
      digestScalars (obsCv cv (σ (.n (lcB i)))) := by
    have a := e1 12 (by omega) (by omega)
    have b := e1 13 (by omega) (by omega)
    rw [show lcB i + 1 + 12 = lcB i + 13 by omega] at a
    rw [show lcB i + 1 + 13 = lcB i + 14 by omega] at b
    exact Prod.ext a b
  have q2 := digestScalars_injective (hcv2.symm.trans c1)
  rw [q2] at e2
  have c2 : (σ (.n (lcB i + 28)), σ (.n (lcB i + 29))) =
      digestScalars (obsCv (obsCv cv (σ (.n (lcB i)))) (σ (.n (lcB i + 15)))) := by
    have a := e2 12 (by omega) (by omega)
    have b := e2 13 (by omega) (by omega)
    rw [show lcB i + 15 + 1 + 12 = lcB i + 28 by omega] at a
    rw [show lcB i + 15 + 1 + 13 = lcB i + 29 by omega] at b
    exact Prod.ext a b
  have q3 := digestScalars_injective (hcv3.symm.trans c2)
  rw [q3] at e3
  have c3 : (σ (.n (lcB i + 36)), σ (.n (lcB i + 37))) = digestScalars
      (sqCv (obsCv (obsCv cv (σ (.n (lcB i)))) (σ (.n (lcB i + 15))))) := by
    have a := e3 5 (by omega)
    have b := e3 6 (by omega)
    rw [show lcB i + 31 + 5 = lcB i + 36 by omega] at a
    rw [show lcB i + 31 + 6 = lcB i + 37 by omega] at b
    exact Prod.ext a b
  have ch : σ (.n (lcB i + 44)) =
      challengeOf (sqCv (obsCv (obsCv cv (σ (.n (lcB i)))) (σ (.n (lcB i + 15))))) := by
    have a := e3 13 (by omega)
    rw [show lcB i + 31 + 13 = lcB i + 44 by omega] at a
    exact a
  refine ⟨g1l, g2l, ?_, ?_, c3⟩
  · show LoadHolds rd (σ (.n 5)) i
      (challengeOf (sqCv (obsCv (obsCv cv (σ (.n (lcB i)))) (σ (.n (lcB i + 15))))))
    rw [← ch]; exact l44
  · show σ (.n (lcB i + 48)) = σ (.n (lcB i)) +
      challengeOf (sqCv (obsCv (obsCv cv (σ (.n (lcB i)))) (σ (.n (lcB i + 15))))) *
        (σ (.n (lcC i)) + σ (.n (lcB i + 15)) +
          challengeOf (sqCv (obsCv (obsCv cv (σ (.n (lcB i)))) (σ (.n (lcB i + 15))))) *
            σ (.n (lcB i + 15)))
    rw [← ch, a48, m47, a46, m45, a30]

end

/-! ## The sampled rounds -/

section
variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- What `flP7` asks (G:1888-1910). -/
theorem fl_p7 {τ : ℕ} (hτ : σ (.n 3) = gen ^ τ) (h : Stmt.HoldsList C rd σ flP7 True kret) :
    LoadHolds rd (σ (.n 2220)) 28 (σ (.n 2203)) ∧ LoadHolds rd (σ (.n 2220)) 29 (σ (.n 2204)) ∧
      LoadHolds rd (σ (.n 2220)) 30 (σ (.n 2) * gen ^ 78) ∧
      LoadHolds rd (σ (.n 2220)) 31 (σ (.n 2215)) ∧
      (gen ^ 7 + gen ^ (τ + 8) ≠ 0 →
        C "__loop82" [gen ^ 7, gen ^ (τ + 8), σ (.n 2220), σ (.n 11), σ (.n 4)] []) ∧
      LoadHolds rd (σ (.n 2220)) (4 * (τ + 8)) (σ (.n 2237)) ∧
      LoadHolds rd (σ (.n 2220)) (4 * (τ + 8) + 1) (σ (.n 2238)) ∧
      LoadHolds rd (σ (.n 2220)) (4 * (τ + 8) + 3) (σ (.n 2239)) ∧
      LoadHolds rd (σ (.n 2220)) (4 * (τ + 8) + 2) (σ (.n 2240)) := by
  simp only [flP7, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and,
    and_true, word_g7, word_g8, word_g28, word_g78] at h
  obtain ⟨c2216, m2217, m2218, m2219, c2221, m2222, l2203, l2204, c2223, m2224, l2224, l2215,
    c2225, c2226, m2227, a2228, c2229, c2230, m2231, -, hcall, c2232, m2233, m2234, m2235, m2236,
    l2237, l2238, l2239, l2240⟩ := h
  have h2236 : σ (.n 2236) = σ (.n 2220) * gen ^ (4 * (τ + 8)) := by
    rw [m2236, m2235, m2234, m2233, hτ, c2232, ← pow_add, gen_pow_quad]
  rw [m2222, c2221] at l2203 l2204 l2224 l2215
  rw [h2236] at l2237 l2238 l2239 l2240
  rw [m2224, c2223] at l2224
  refine ⟨lh_at l2203 rfl, lh_at l2204 rfl, lh_at l2224 rfl, lh_at l2215 rfl, fun hne => ?_,
    lh_at l2237 rfl, lh_at l2238 rfl, lh_at l2239 rfl, lh_at l2240 rfl⟩
  have := hcall (by rw [a2228, c2225, m2227, hτ, c2226, ← pow_add]; exact hne)
  rw [c2229, m2231, hτ, c2230, ← pow_add] at this
  exact this

end

/-- **The zerocheck's rounds** (G:1878-1910): the seven fixed rounds then `__loop82`'s `τ + 1`,
each a round of `scSt` with the equality factor `e j` at `zerocheck_r[g^(6+j)]`; their words at
the cursor's offsets `64 + 2j`, `65 + 2j`, their challenges at `zerocheck_chis[g^j]`, and the
final claim, state and cursor. -/
theorem fl_rounds {rd : Reader} {σ : Val} {kret : List E → Prop} {τ : ℕ} (hτ : τ < 29)
    (e : ℕ → E) (st0 : E × Digest)
    (hfr : ∀ i < 7, Stmt.HoldsList (coreProgram.Rel rd) rd σ (frBlk i) True kret)
    (he : ∀ j < τ + 8, LoadHolds rd (σ (.n 11)) (6 + j) (e j))
    (h0 : σ (.n 1847) = st0.1) (hs0 : (σ (.n 1006), σ (.n 1007)) = digestScalars st0.2)
    (l28 : LoadHolds rd (σ (.n 2220)) 28 (σ (.n 2203)))
    (l29 : LoadHolds rd (σ (.n 2220)) 29 (σ (.n 2204)))
    (l30 : LoadHolds rd (σ (.n 2220)) 30 (σ (.n 2) * gen ^ 78))
    (l31 : LoadHolds rd (σ (.n 2220)) 31 (σ (.n 2215)))
    (hloop : coreProgram.Rel rd "__loop82"
      [gen ^ 7, gen ^ (τ + 8), σ (.n 2220), σ (.n 11), σ (.n 4)] [])
    (lE0 : LoadHolds rd (σ (.n 2220)) (4 * (τ + 8)) (σ (.n 2237)))
    (lE1 : LoadHolds rd (σ (.n 2220)) (4 * (τ + 8) + 1) (σ (.n 2238)))
    (lE3 : LoadHolds rd (σ (.n 2220)) (4 * (τ + 8) + 3) (σ (.n 2239)))
    (lE2 : LoadHolds rd (σ (.n 2220)) (4 * (τ + 8) + 2) (σ (.n 2240))) :
    ∃ g : ℕ → E × E,
      (∀ j < τ + 8, LoadHolds rd (σ (.n 2)) (64 + 2 * j) (g j).1 ∧
        LoadHolds rd (σ (.n 2)) (65 + 2 * j) (g j).2 ∧
        LoadHolds rd (σ (.n 4)) j (scCh e g st0 j)) ∧
      σ (.n 2239) = (scSt e g st0 (τ + 8)).1 ∧
      (σ (.n 2237), σ (.n 2238)) = digestScalars (scSt e g st0 (τ + 8)).2 ∧
      σ (.n 2240) = σ (.n 2) * gen ^ (64 + 2 * (τ + 8)) := by
  -- the loop's iterations
  obtain ⟨m, hm, hN, hfirst, hall⟩ :=
    (loop_iff (loop82_step rd (gen ^ (τ + 8)) (σ (.n 2220)) (σ (.n 11)) (σ (.n 4))) 7).mp hloop
  have hm' : m = τ + 8 := by
    rcases Nat.lt_or_ge (τ + 8) m with h | h
    · exact absurd rfl (hfirst (τ + 8) (by omega) h)
    · exact (gen_pow_inj' (by omega) (by omega) hN).symm
  subst hm'
  obtain ⟨F, hF⟩ := exists_fun_of_forall (n := τ + 8) (α := Digest × E × E × E × E × E)
    (P := fun j x => 7 ≤ j →
      LoadHolds rd (σ (.n 2220) * gen ^ (4 * j)) 0 (digestScalars x.1).1 ∧
      LoadHolds rd (σ (.n 2220) * gen ^ (4 * j)) 1 (digestScalars x.1).2 ∧
      LoadHolds rd (σ (.n 2220) * gen ^ (4 * j)) 2 x.2.1 ∧
      LoadHolds rd (σ (.n 2220) * gen ^ (4 * j)) 3 x.2.2.1 ∧
      LoadHolds rd (σ (.n 11) * gen ^ j) 6 x.2.2.2.1 ∧ LoadHolds rd x.2.1 0 x.2.2.2.2.1 ∧
      LoadHolds rd x.2.1 1 x.2.2.2.2.2 ∧
      LoadHolds rd (σ (.n 4) * gen ^ j) 0
        (scStep x.2.2.2.1 (x.2.2.2.2.1, x.2.2.2.2.2) (x.2.2.1, x.1)).1 ∧
      LoadHolds rd (σ (.n 2220) * gen ^ (4 * j)) 4
        (digestScalars (scStep x.2.2.2.1 (x.2.2.2.2.1, x.2.2.2.2.2) (x.2.2.1, x.1)).2.2).1 ∧
      LoadHolds rd (σ (.n 2220) * gen ^ (4 * j)) 5
        (digestScalars (scStep x.2.2.2.1 (x.2.2.2.2.1, x.2.2.2.2.2) (x.2.2.1, x.1)).2.2).2 ∧
      LoadHolds rd (σ (.n 2220) * gen ^ (4 * j)) 6 (x.2.1 * gen ^ 2) ∧
      LoadHolds rd (σ (.n 2220) * gen ^ (4 * j)) 7
        (scStep x.2.2.2.1 (x.2.2.2.2.1, x.2.2.2.2.2) (x.2.2.1, x.1)).2.1) fun j hj => by
    by_cases h7 : 7 ≤ j
    · obtain ⟨cv, cur, claim, e', g1, g2, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ :=
        hall j h7 hj
      rw [gen_pow_quad] at a0 a1 a2 a3 a8 a9 a10 a11
      exact ⟨(cv, cur, claim, e', g1, g2), fun _ => ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
        a11⟩⟩
    · exact ⟨default, fun h => absurd h h7⟩
  set g : ℕ → E × E := fun j => if j < 7 then (σ (.n (frB j + 1)), σ (.n (frB j + 16)))
    else ((F j).2.2.2.2.1, (F j).2.2.2.2.2) with hg
  refine ⟨g, ?_⟩
  -- the fixed rounds
  have fixed : ∀ i ≤ 7, σ (.n (frC i)) = (scSt e g st0 i).1 ∧
      (σ (.n (frS i)), σ (.n (frS i + 1))) = digestScalars (scSt e g st0 i).2 ∧
      (∀ j < i, LoadHolds rd (σ (.n 2)) (64 + 2 * j) (g j).1 ∧
        LoadHolds rd (σ (.n 2)) (65 + 2 * j) (g j).2 ∧
        LoadHolds rd (σ (.n 4)) j (scCh e g st0 j)) := by
    intro i hi
    induction i with
    | zero => exact ⟨h0, hs0, fun j hj => absurd hj (by omega)⟩
    | succ i ih =>
      obtain ⟨c, sv, prev⟩ := ih (by omega)
      obtain ⟨lB, g1l, g2l, lch, hc, hsv⟩ := frBlk_step i (hfr i (by omega)) sv
      have eB : σ (.n (frB i)) = e i := loadHolds_unique lB (he i (by omega))
      have eg : (σ (.n (frB i + 1)), σ (.n (frB i + 16))) = g i := by
        simp only [hg, show i < 7 by omega, ↓reduceIte]
      rw [eB, eg, c, Prod.mk.eta] at lch hc hsv
      refine ⟨?_, ?_, fun j hj => ?_⟩
      · rw [show frC (i + 1) = frB i + 51 by
          simp only [frC, frB, Nat.add_one_ne_zero, ↓reduceIte]; omega]; exact hc
      · rw [show frS (i + 1) = frB i + 39 by
          simp only [frS, frB, Nat.add_one_ne_zero, ↓reduceIte]; omega]; exact hsv
      · rcases Nat.lt_or_ge j i with h | h
        · exact prev j h
        · obtain rfl : j = i := by omega
          rw [← eg]
          exact ⟨g1l, g2l, lch⟩
  -- the sampled rounds
  obtain ⟨c7, sv7, prev7⟩ := fixed 7 le_rfl
  have hrow : ∀ j, 7 ≤ j → j ≤ τ + 8 →
      LoadHolds rd (σ (.n 2220)) (4 * j) (digestScalars (scSt e g st0 j).2).1 ∧
      LoadHolds rd (σ (.n 2220)) (4 * j + 1) (digestScalars (scSt e g st0 j).2).2 ∧
      LoadHolds rd (σ (.n 2220)) (4 * j + 2) (σ (.n 2) * gen ^ (64 + 2 * j)) ∧
      LoadHolds rd (σ (.n 2220)) (4 * j + 3) (scSt e g st0 j).1 ∧
      (∀ i < j, LoadHolds rd (σ (.n 2)) (64 + 2 * i) (g i).1 ∧
        LoadHolds rd (σ (.n 2)) (65 + 2 * i) (g i).2 ∧
        LoadHolds rd (σ (.n 4)) i (scCh e g st0 i)) := by
    intro j h7 hj
    induction j, h7 using Nat.le_induction with
    | base =>
      have s1 : σ (.n 2203) = (digestScalars (scSt e g st0 7).2).1 := congrArg Prod.fst sv7
      have s2 : σ (.n 2204) = (digestScalars (scSt e g st0 7).2).2 := congrArg Prod.snd sv7
      rw [← s1, ← s2, ← c7]
      exact ⟨l28, l29, l30, l31, prev7⟩
    | succ j h7 ih =>
      obtain ⟨r0, r1, r2, r3, prev⟩ := ih (by omega)
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hF j (by omega) h7
      have ecv : (F j).1 = (scSt e g st0 j).2 := digestScalars_injective
        (Prod.ext (loadHolds_unique (lh_at a0 rfl) r0) (loadHolds_unique (lh_at a1 rfl) r1))
      have ecur : (F j).2.1 = σ (.n 2) * gen ^ (64 + 2 * j) := loadHolds_unique (lh_at a2 rfl) r2
      have ecl : (F j).2.2.1 = (scSt e g st0 j).1 := loadHolds_unique (lh_at a3 rfl) r3
      have ee : (F j).2.2.2.1 = e j := loadHolds_unique (lh_at a4 (by omega)) (he j (by omega))
      have eg : ((F j).2.2.2.2.1, (F j).2.2.2.2.2) = g j := by
        simp only [hg, show ¬ j < 7 by omega, ↓reduceIte]
      rw [ecv, ecl, ee, eg, Prod.mk.eta] at a7 a8 a9 a11
      rw [ecur] at a5 a6 a10
      refine ⟨lh_at a8 (by ring), lh_at a9 (by ring), ?_, lh_at a11 (by ring), fun i hi => ?_⟩
      · have := lh_at a10 (show 4 * j + 6 = 4 * (j + 1) + 2 by ring)
        rwa [mul_assoc, ← pow_add, show 64 + 2 * j + 2 = 64 + 2 * (j + 1) by ring] at this
      · rcases Nat.lt_or_ge i j with h | h
        · exact prev i h
        · obtain rfl : i = j := by omega
          rw [← eg]
          refine ⟨?_, ?_, lh_at a7 (by ring)⟩
          · have := lh_off a5
            rw [show 64 + 2 * i + 0 = 64 + 2 * i by ring] at this; exact this
          · have := lh_off a6
            rw [show 64 + 2 * i + 1 = 65 + 2 * i by ring] at this; exact this
  obtain ⟨r0, r1, r2, r3, words⟩ := hrow (τ + 8) (by omega) le_rfl
  refine ⟨words, loadHolds_unique lE3 r3, Prod.ext (loadHolds_unique lE0 r0)
    (loadHolds_unique lE1 r1), loadHolds_unique lE2 r2⟩

/-! ## The final evaluations, `alpha` and the lincheck -/

section
variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- The final evaluations `a`, `b` and `c = claim + a·b` (G:1914-1916). -/
theorem fl_s8 (h : Stmt.HoldsList C rd σ flS8 True kret) {cv : Digest}
    (hcv : (σ (.n 2237), σ (.n 2238)) = digestScalars cv) :
    LoadHolds rd (σ (.n 2240)) 0 (σ (.n 2241)) ∧ LoadHolds rd (σ (.n 2240)) 1 (σ (.n 2256)) ∧
      (σ (.n 2269), σ (.n 2270)) =
        digestScalars (obsCv (obsCv cv (σ (.n 2241))) (σ (.n 2256))) ∧
      σ (.n 2272) = σ (.n 2239) + σ (.n 2241) * σ (.n 2256) := by
  simp only [flS8] at h
  rw [hl_app rfl, hl_app rfl] at h
  obtain ⟨⟨f1, f2⟩, h⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
  obtain ⟨m, a⟩ := h
  obtain ⟨l1, c1⟩ := fsNext_chain f1 hcv
  obtain ⟨l2, c2⟩ := fsNext_chain f2 c1
  exact ⟨l1, l2, c2, by rw [a, m]⟩

/-- `alpha` and the lincheck's claim `a + α·b + α²·c + α³` (G:1927-1930). -/
theorem fl_s10 (h : Stmt.HoldsList C rd σ flS10 True kret) {cv : Digest}
    (hcv : (σ (.n 2269), σ (.n 2270)) = digestScalars cv) :
    σ (.n 2733) = challengeOf (sqCv cv) ∧ (σ (.n 2725), σ (.n 2726)) = digestScalars (sqCv cv) ∧
      σ (.n 2734) = σ (.n 2733) ^ 2 ∧ σ (.n 2735) = σ (.n 2733) ^ 3 ∧
      σ (.n 2740) = σ (.n 2241) + σ (.n 2733) * σ (.n 2256) + σ (.n 2733) ^ 2 * σ (.n 2272) +
        σ (.n 2733) ^ 3 := by
  simp only [flS10] at h
  rw [hl_app rfl] at h
  obtain ⟨⟨-, hsq⟩, h⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
  obtain ⟨m34, m35, m36, a37, m38, a39, a40⟩ := h
  obtain ⟨c, ch⟩ := squeeze_chain hsq hcv
  have e2 : σ (.n 2734) = σ (.n 2733) ^ 2 := by rw [m34, sq]
  have e3 : σ (.n 2735) = σ (.n 2733) ^ 3 := by rw [m35, e2]; ring
  exact ⟨ch, c, e2, e3, by rw [a40, a39, a37, m38, m36, e2, e3]⟩

/-- **The lincheck's eight rounds** (G:1931-1937): `lcSt` from the claim at `2740` and the state
`cv`; their words at offsets `2 .. 17` of `σ 2240`, their challenges at `lincheck_rs`, the final
claim at `3132` and state at `3120`. -/
theorem fl_lincheck (h : ∀ i < 8, Stmt.HoldsList C rd σ (lcBlk i) True kret) {cv : Digest}
    (hcv : (σ (.n 2725), σ (.n 2726)) = digestScalars cv) :
    (∀ i < 8, LoadHolds rd (σ (.n 2240)) (2 + 2 * i) (σ (.n (lcB i))) ∧
      LoadHolds rd (σ (.n 2240)) (3 + 2 * i) (σ (.n (lcB i + 15))) ∧
      LoadHolds rd (σ (.n 5)) i
        (lcCh (fun i => (σ (.n (lcB i)), σ (.n (lcB i + 15)))) (σ (.n 2740), cv) i)) ∧
      σ (.n 3132) = (lcSt (fun i => (σ (.n (lcB i)), σ (.n (lcB i + 15)))) (σ (.n 2740), cv) 8).1 ∧
      (σ (.n 3120), σ (.n 3121)) =
        digestScalars (lcSt (fun i => (σ (.n (lcB i)), σ (.n (lcB i + 15)))) (σ (.n 2740), cv) 8).2 := by
  set g : ℕ → E × E := fun i => (σ (.n (lcB i)), σ (.n (lcB i + 15)))
  have key : ∀ i ≤ 8, σ (.n (lcC i)) = (lcSt g (σ (.n 2740), cv) i).1 ∧
      (σ (.n (lcS i)), σ (.n (lcS i + 1))) = digestScalars (lcSt g (σ (.n 2740), cv) i).2 ∧
      (∀ j < i, LoadHolds rd (σ (.n 2240)) (2 + 2 * j) (σ (.n (lcB j))) ∧
        LoadHolds rd (σ (.n 2240)) (3 + 2 * j) (σ (.n (lcB j + 15))) ∧
        LoadHolds rd (σ (.n 5)) j (lcCh g (σ (.n 2740), cv) j)) := by
    intro i hi
    induction i with
    | zero => exact ⟨rfl, hcv, fun j hj => absurd hj (by omega)⟩
    | succ i ih =>
      obtain ⟨c, sv, prev⟩ := ih (by omega)
      obtain ⟨g1l, g2l, lch, hc, hsv⟩ := lcBlk_step i (h i (by omega)) sv
      rw [c, Prod.mk.eta] at lch hc hsv
      refine ⟨?_, ?_, fun j hj => ?_⟩
      · rw [show lcC (i + 1) = lcB i + 48 by
          simp only [lcC, lcB, Nat.add_one_ne_zero, ↓reduceIte]; omega]; exact hc
      · rw [show lcS (i + 1) = lcB i + 36 by
          simp only [lcS, lcB, Nat.add_one_ne_zero, ↓reduceIte]; omega]; exact hsv
      · rcases Nat.lt_or_ge j i with hlt | hge
        · exact prev j hlt
        · obtain rfl : j = i := by omega
          exact ⟨g1l, g2l, lch⟩
  obtain ⟨c8, s8, words⟩ := key 8 le_rfl
  exact ⟨words, c8, s8⟩

/-- The slices (G:1939-1941), from the state `cv`. -/
theorem fl_slices (h : ∀ i < 64, Stmt.HoldsList C rd σ (zpBlk i) True kret) {cv : Digest}
    (hcv : (σ (.n 3120), σ (.n 3121)) = digestScalars cv) :
    (∀ i < 64, LoadHolds rd (σ (.n 2240)) (18 + i) (σ (.n (3133 + 15 * i))) ∧
      LoadHolds rd (σ (.n 6)) i (σ (.n (3133 + 15 * i)))) ∧
      (σ (.n 4091), σ (.n 4092)) =
        digestScalars (obsAll cv ((List.range 64).map fun i => σ (.n (3133 + 15 * i)))) := by
  obtain ⟨h1, h2⟩ := fsNext_run zpS (fun i => 3133 + 15 * i) (fun i => 18 + i) (.n 2240)
    (fun i => [.atom (.load (.n (3133 + 15 * i)) (.n 6) i)]) (n := 64) h
    (fun i => by simp only [zpS, Nat.add_one_ne_zero, ↓reduceIte]; omega) hcv
  refine ⟨fun i hi => ⟨(h1 i hi).1, ?_⟩, h2⟩
  have := (h1 i hi).2
  simpa [Stmt.HoldsList, Stmt.Holds, Atom.Holds] using this

/-- The pin term (G:1945-1946): `α³` times the pin column's equality weight times `s[0]`. -/
theorem fl_p13 (h : Stmt.HoldsList C rd σ flP13 True kret) {rc : ℕ → E} {s0 : E}
    (hr : ∀ j < 8, LoadHolds rd (σ (.n 5)) j (rc j)) (hs : LoadHolds rd (σ (.n 6)) 0 s0) :
    σ (.n 4124) = σ (.n 2735) * ((1 + rc 0) * (1 + rc 1) * (1 + rc 2) * (1 + rc 3) * rc 4 *
      (1 + rc 5) * (1 + rc 6) * (1 + rc 7)) * s0 := by
  simp only [flP13, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one] at h
  obtain ⟨l0, c0, a0, l1, c1, a1, m1, l2, c2, a2, m2, l3, c3, a3, m3, l4, m4, l5, c5, a5, m5, l6,
    c6, a6, m6, l7, c7, a7, m7, m8, ls, m9⟩ := h
  rw [m9, m8, m7, a7, c7, m6, a6, c6, m5, a5, c5, m4, m3, a3, c3, m2, a2, c2, m1, a1, c1, a0, c0,
    loadHolds_unique l0 (hr 0 (by omega)), loadHolds_unique l1 (hr 1 (by omega)),
    loadHolds_unique l2 (hr 2 (by omega)), loadHolds_unique l3 (hr 3 (by omega)),
    loadHolds_unique l4 (hr 4 (by omega)), loadHolds_unique l5 (hr 5 (by omega)),
    loadHolds_unique l6 (hr 6 (by omega)), loadHolds_unique l7 (hr 7 (by omega)),
    loadHolds_unique ls hs]

/-- The points' equality (G:1951-1952): `Π_t (1 + chi_t + rc_{7-t})`. -/
theorem fl_cpe (h : ∀ t < 8, Stmt.HoldsList C rd σ (cpeBlk t) True kret) {chi rc : ℕ → E}
    (hc : ∀ t < 8, LoadHolds rd (σ (.n 4)) t (chi t))
    (hr : ∀ j < 8, LoadHolds rd (σ (.n 5)) j (rc j)) :
    σ (.n 4171) = ∏ t ∈ Finset.range 8, (1 + chi t + rc (7 - t)) := by
  have key : ∀ t < 8, σ (.n (if t = 0 then 4129 else 4129 + 6 * t)) =
      ∏ u ∈ Finset.range (t + 1), (1 + chi u + rc (7 - u)) := by
    intro t ht
    induction t with
    | zero =>
      have h0 := h 0 (by omega)
      simp only [cpeBlk, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true,
        word_one] at h0
      obtain ⟨c, l1, a1, l2, a2⟩ := h0
      rw [ite_pos' rfl, a2, a1, c, loadHolds_unique l1 (hc 0 (by omega)),
        loadHolds_unique l2 (hr 7 (by omega)), Finset.prod_range_one]
    | succ t ih =>
      have ih' := ih (by omega)
      have h1 := h (t + 1) ht
      rcases Nat.eq_zero_or_pos t with rfl | hpos
      · simp only [cpeBlk, Nat.reduceAdd, Nat.reduceMul, ↓reduceIte, Stmt.HoldsList, Stmt.Holds,
          Atom.Holds, and_true, word_one, Nat.one_ne_zero] at h1 ih'
        obtain ⟨c, l1, a1, l2, a2, m⟩ := h1
        show σ (.n 4135) = _
        rw [m, a2, a1, c, loadHolds_unique l1 (hc 1 ht), loadHolds_unique l2 (hr 6 (by omega)),
          Finset.prod_range_succ, ih']
      · have n1 : t + 1 ≠ 1 := by omega
        have n0 : t ≠ 0 := by omega
        simp only [cpeBlk, Nat.add_one_ne_zero, n1, n0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds,
          Atom.Holds, and_true, word_one] at h1 ih'
        obtain ⟨c, l1, a1, l2, a2, m⟩ := h1
        rw [show 4123 + 6 * (t + 1) = 4129 + 6 * t by omega] at m
        rw [ite_neg' (Nat.add_one_ne_zero t), m, a2, a1, c, loadHolds_unique l1 (hc (t + 1) ht),
          loadHolds_unique l2 (hr (7 - (t + 1)) (by omega)), Finset.prod_range_succ, ih']
  have := key 7 (by omega)
  simpa using this

/-- The slices' Lagrange sum (G:1953-1954). -/
theorem fl_cs (h : ∀ i < 64, Stmt.HoldsList C rd σ (csBlk i) True kret) {s : ℕ → E}
    (hs : ∀ i < 64, LoadHolds rd (σ (.n 6)) i (s i)) :
    σ (.n 4362) = ∑ i ∈ Finset.range 64, σ (.n (2655 + i)) * s i := by
  have key : ∀ i < 64, σ (.n (if i = 0 then 4173 else 4173 + 3 * i)) =
      ∑ j ∈ Finset.range (i + 1), σ (.n (2655 + j)) * s j := by
    intro i hi
    induction i with
    | zero =>
      have h0 := h 0 (by omega)
      simp only [csBlk, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h0
      obtain ⟨l, m⟩ := h0
      rw [ite_pos' rfl, m, loadHolds_unique l (hs 0 (by omega)), Finset.sum_range_one]
    | succ i ih =>
      have ih' := ih (by omega)
      have h1 := h (i + 1) hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · simp only [csBlk, Nat.reduceAdd, Nat.reduceMul, ↓reduceIte, Stmt.HoldsList, Stmt.Holds,
          Atom.Holds, and_true, Nat.one_ne_zero] at h1 ih'
        obtain ⟨l, m, a⟩ := h1
        show σ (.n 4176) = _
        rw [a, m, loadHolds_unique l (hs 1 hi), Finset.sum_range_succ, ih']
      · have n1 : i + 1 ≠ 1 := by omega
        have n0 : i ≠ 0 := by omega
        simp only [csBlk, Nat.add_one_ne_zero, n1, n0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds,
          Atom.Holds, and_true] at h1 ih'
        obtain ⟨l, m, a⟩ := h1
        rw [show 4170 + 3 * (i + 1) = 4173 + 3 * i by omega] at a
        rw [ite_neg' (Nat.add_one_ne_zero i), a, m, loadHolds_unique l (hs (i + 1) hi),
          Finset.sum_range_succ, ih']
  have := key 63 (by omega)
  simpa using this

/-- The final check and the returns (G:1955-1963). -/
theorem fl_end (h : Stmt.HoldsList C rd σ flPEnd True kret) :
    σ (.n 3132) = σ (.n 2719) + σ (.n 4124) +
        σ (.n 2734) * σ (.n 4171) * (σ (.n 4362) * word 11666641484232641359 0 0) ∧
      σ (.n 4369) = σ (.n 4091) ∧ σ (.n 4370) = σ (.n 4092) ∧
      σ (.n 4373) = σ (.n 2240) * gen ^ 82 ∧ σ (.n 4374) = σ (.n 1014) ∧
      σ (.n 4375) = σ (.n 2733) ∧ σ (.n 4376) = σ (.n 2719) := by
  simp only [flPEnd, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_g82] at h
  obtain ⟨c63, m64, a65, m66, m67, a68, hq, e69, e70, c71, m72, e73, e74, e75, e76⟩ := h
  refine ⟨?_, e69, e70, by rw [e73, m72, c71], e74, e75, e76⟩
  rw [e_add_eq_zero_iff.mp hq, a68, m67, m66, a65, m64, c63]

end

/-! ## Reading the words -/

theorem readsAt_iff_getD {rd : Reader} {p : E} {l : List E} :
    ReadsAt rd p l ↔ ∀ k < l.length, LoadHolds rd p k (l.getD k 0) := by
  refine ⟨fun h k hk => ?_, fun h k hk => ?_⟩
  · rw [List.getD_eq_getElem _ _ hk]; exact h k hk
  · have := h k hk; rwa [List.getD_eq_getElem _ _ hk] at this

theorem readsAt_append_iff {rd : Reader} {p : E} {l1 l2 : List E} :
    ReadsAt rd p (l1 ++ l2) ↔
      ReadsAt rd p l1 ∧ ∀ k < l2.length, LoadHolds rd p (l1.length + k) (l2.getD k 0) := by
  rw [readsAt_iff_getD, readsAt_iff_getD, List.length_append]
  constructor
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · have := h k (by omega)
      rwa [List.getD_eq_getElem?_getD, List.getElem?_append_left hk,
        ← List.getD_eq_getElem?_getD] at this
    · have := h (l1.length + k) (by omega)
      rwa [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD] at this
  · rintro ⟨h1, h2⟩ k hk
    rcases Nat.lt_or_ge k l1.length with h | h
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]
      exact h1 k h
    · have := h2 (k - l1.length) (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, ← List.getD_eq_getElem?_getD]
      rwa [show l1.length + (k - l1.length) = k by omega] at this

theorem roundWords_getD (g : ℕ → E × E) : ∀ (n m k : ℕ), k < 2 * n →
    (roundWords g n m).getD k 0 = if k % 2 = 0 then (g (m + k / 2)).1 else (g (m + k / 2)).2
  | 0, _, _, hk => absurd hk (by omega)
  | n + 1, m, k, hk => by
    rw [roundWords_succ]
    match k with
    | 0 => simp
    | 1 => simp
    | k + 2 =>
      rw [List.getD_cons_succ, List.getD_cons_succ, roundWords_getD g n (m + 1) k (by omega),
        show (k + 2) % 2 = k % 2 by omega, show m + (k + 2) / 2 = m + 1 + k / 2 by omega]

theorem map_some_range (l : List E) :
    l.map some = (List.range l.length).map fun j => some (l.getD j 0) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]

theorem getD_map_range {α : Type} (f : ℕ → α) (d : α) {n k : ℕ} (hk : k < n) :
    ((List.range n).map f).getD k d = f k := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range]

/-! ## Soundness -/

theorem getD_append_lt {l1 l2 : List E} {k : ℕ} (h : k < l1.length) :
    (l1 ++ l2).getD k 0 = l1.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

theorem getD_append_ge {l1 l2 : List E} {k : ℕ} :
    (l1 ++ l2).getD (l1.length + k) 0 = l2.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    ← List.getD_eq_getElem?_getD]

set_option maxHeartbeats 1000000 in
/-- **`verify_flock` is sound** (TRIAGE #40): `SoundFlock`. -/
theorem verify_flock_sound (rd : Reader) : SoundFlock rd := by
  intro τ fs0 fs1 cur zchis lrs zpart rets hτ h
  obtain ⟨σ, hp, hseg, hret⟩ := verify_flock_holds h
  simp only [List.cons.injEq, and_true] at hp
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := hp
  simp only [flSegs, List.forall_mem_cons] at hseg
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, -⟩ := hseg
  rw [holdsList_range_flatten 64 rd1Blk (fun _ => rfl), and_true] at g1
  rw [holds_lag64T, and_true] at g3 g9
  rw [holdsList_range_flatten 64 ipBlk (fun i => by unfold ipBlk; split <;> rfl), and_true] at g4
  rw [holdsList_range_flatten 7 frBlk (fun _ => rfl), and_true] at g6
  rw [holdsList_range_flatten 8 lcBlk (fun _ => rfl), and_true] at g11
  rw [holdsList_range_flatten 64 zpBlk (fun _ => rfl), and_true] at g12
  rw [holdsList_range_flatten 8 cpeBlk (fun i => by unfold cpeBlk; split <;> rfl), and_true] at g14
  rw [holdsList_range_flatten 64 csBlk (fun i => by unfold csBlk; split <;> rfl), and_true] at g15
  -- the prelude and the sampled coordinates
  obtain ⟨h7, h8, hzr, l26, l27, hc81, l38, l39⟩ := fl_p0 e3 g0
  have hloop81 := hc81 (gen_pow_ne_of_lt (by omega) (by omega))
  obtain ⟨cv0, hcv0⟩ : ∃ cv0, (σ (.n 0), σ (.n 1)) = digestScalars cv0 := by
    obtain ⟨m, hm, -, -, hall⟩ := (loop_iff (loop81_step rd _ _ _) 13).mp hloop81
    obtain ⟨cv, a0, a1, -⟩ := hall 13 le_rfl hm
    rw [gen_pow_sq] at a0 a1
    exact ⟨cv, Prod.ext (by rw [← h7]; exact loadHolds_unique l26 (lh_at a0 rfl))
      (by rw [← h8]; exact loadHolds_unique l27 (lh_at a1 rfl))⟩
  have l0 : LoadHolds rd (σ (.n 24)) 26 (digestScalars cv0).1 := by
    rw [← congrArg Prod.fst hcv0, ← h7]; exact l26
  have l1 : LoadHolds rd (σ (.n 24)) 27 (digestScalars cv0).2 := by
    rw [← congrArg Prod.snd hcv0, ← h8]; exact l27
  obtain ⟨hsam, k0, k1⟩ := fl_sampled hτ l0 l1 hloop81
  have hcv1 : (σ (.n 38), σ (.n 39)) = digestScalars (sqCv^[τ + 1] cv0) :=
    Prod.ext (loadHolds_unique l38 k0) (loadHolds_unique l39 k1)
  have hsq1 : (sqAll (τ + 1) cv0).2 = sqCv^[τ + 1] cv0 := by rw [sqAll_eq]
  -- round 1, the skip challenge, the interpolation
  obtain ⟨hr1, hcv2⟩ := fl_round1 g1 hcv1
  set p := (List.range 64).map fun i => σ (.n (41 + 15 * i)) with hpdef
  have hpl : p.length = 64 := by simp [p]
  obtain ⟨hcv3, hz⟩ := squeeze_chain g2 hcv2
  set z := challengeOf (sqCv (obsAll (sqCv^[τ + 1] cv0) p)) with hzdef
  have hz' : σ (.n 1014) = z := hz
  have hnum := lag64_phi (σ := σ) (b := 64) (by norm_num) g3
  rw [lgOut_hi] at hnum
  obtain ⟨hsh, hsum⟩ := fl_interp g4 (p := fun i => σ (.n (41 + 15 * i))) (fun i hi => (hr1 i hi).2)
  simp only [flP5, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at g5
  obtain ⟨c1845, m1846, m1847, -, -, -, -⟩ := g5
  have hvP : σ (.n 1847) = lagrangeInterpolate 128 (List.replicate 64 0 ++ p) z := by
    rw [interp_eq _ p hpl, m1847, m1846, c1845, hsh, hsum, hz']
    refine congrArg (fun x => x * _) (Finset.sum_congr rfl fun i hi => ?_)
    rw [hnum i (Finset.mem_range.mp hi), hz', getD_map_range _ _ (Finset.mem_range.mp hi)]
  -- the rounds
  obtain ⟨l28, l29, l30, l31, hc82, lE0, lE1, lE3, lE2⟩ := fl_p7 e3 g7
  have hloop82 := hc82 (gen_pow_ne_of_lt (by omega) (by omega))
  set e : ℕ → E := fun j => (fixedChallenges ++ (sqAll (τ + 1) cv0).1).getD j 0 with hedef
  set st0 : E × Digest := (lagrangeInterpolate 128 (List.replicate 64 0 ++ p) z,
    sqCv (obsAll (sqCv^[τ + 1] cv0) p)) with hst0
  have he : ∀ j < τ + 8, LoadHolds rd (σ (.n 11)) (6 + j) (e j) := by
    intro j hj
    rcases Nat.lt_or_ge j 7 with h7' | h7'
    · have := hzr j h7'
      rw [fixed_words] at this
      simp only [e]
      rw [getD_append_lt (by rw [fixedChallenges_length]; exact h7')]
      exact this
    · obtain ⟨t, rfl⟩ : ∃ t, j = 7 + t := ⟨j - 7, by omega⟩
      have := hsam t (by omega)
      simp only [e]
      rw [show 7 + t = fixedChallenges.length + t by rw [fixedChallenges_length], getD_append_ge,
        sqAll_eq, getD_map_range _ _ (by omega),
        show 6 + (fixedChallenges.length + t) = 13 + t by rw [fixedChallenges_length]; omega]
      exact this
  obtain ⟨g, hwords, hclaim, hst, hcur⟩ := fl_rounds hτ e st0 g6 he (by rw [hvP])
    (by exact hcv3) l28 l29 l30 l31 hloop82 lE0 lE1 lE3 lE2
  -- the final evaluations, alpha, the lincheck, the slices
  obtain ⟨la, lb, hcv5, hc⟩ := fl_s8 g8 hst
  have hcn := lag64_phi (σ := σ) (b := 0) (by norm_num) g9
  rw [lgOut_lo] at hcn
  obtain ⟨hα, hcv6, h2734, h2735, h2740⟩ := fl_s10 g10 hcv5
  obtain ⟨hlc, hrlc, hcv7⟩ := fl_lincheck g11 hcv6
  set g' : ℕ → E × E := fun i => (σ (.n (lcB i)), σ (.n (lcB i + 15))) with hg'
  set st0' : E × Digest := (σ (.n 2740), sqCv (obsCv (obsCv (scSt e g st0 (τ + 8)).2
    (σ (.n 2241))) (σ (.n 2256)))) with hst0'
  obtain ⟨hsl, hcv8⟩ := fl_slices g12 hcv7
  have hpin := fl_p13 g13 (rc := lcCh g' st0') (fun j hj => (hlc j hj).2.2) (hsl 0 (by omega)).2
  have hcpe := fl_cpe g14 (chi := scCh e g st0) (rc := lcCh g' st0')
    (fun t ht => (hwords t (by omega)).2.2) (fun j hj => (hlc j hj).2.2)
  have hcs := fl_cs g15 (s := fun i => σ (.n (3133 + 15 * i))) (fun i hi => (hsl i hi).2)
  obtain ⟨hfin, r69, r70, r73, r74, r75, r76⟩ := fl_end g16
  -- the outcome
  set chi := (List.range (τ + 8)).map (scCh e g st0) with hchi
  set rcs := (List.range 8).map (lcCh g' st0') with hrcs
  set sl := (List.range 64).map fun i => σ (.n (3133 + 15 * i)) with hsl'
  set ys := roundWords g (τ + 8) 0 with hys
  set zs := roundWords g' 8 0 with hzs
  have hchil : chi.length = τ + 8 := by simp [chi]
  have hrcsl : rcs.length = 8 := by simp [rcs]
  have hsll : sl.length = 64 := by simp [sl]
  have hysl : ys.length = 2 * (τ + 8) := roundWords_length _ _ _
  have hzsl : zs.length = 2 * 8 := roundWords_length _ _ _
  have h2240 : σ (.n 2240) = cur * gen ^ (64 + 2 * (τ + 8)) := by rw [hcur, e2]
  have h2739 : σ (.n 2239) = (scSt e g st0 (τ + 8)).1 := hclaim
  have hα' : σ (.n 2733) = challengeOf (sqCv (obsCv (obsCv (scSt e g st0 (τ + 8)).2
      (σ (.n 2241))) (σ (.n 2256)))) := hα
  have h2740' : σ (.n 2740) = σ (.n 2241) + challengeOf (sqCv (obsCv (obsCv
      (scSt e g st0 (τ + 8)).2 (σ (.n 2241))) (σ (.n 2256)))) * σ (.n 2256) +
      challengeOf (sqCv (obsCv (obsCv (scSt e g st0 (τ + 8)).2 (σ (.n 2241))) (σ (.n 2256)))) ^ 2 *
        ((scSt e g st0 (τ + 8)).1 + σ (.n 2241) * σ (.n 2256)) +
      challengeOf (sqCv (obsCv (obsCv (scSt e g st0 (τ + 8)).2 (σ (.n 2241))) (σ (.n 2256)))) ^ 3 := by
    rw [h2740, hc, h2739, hα']
  refine ⟨cv0, p ++ ys ++ [σ (.n 2241), σ (.n 2256)] ++ zs ++ sl, obsAll (lcSt g' st0' 8).2 sl, z,
    σ (.n 2733), σ (.n 2719), chi, rcs, sl, by rw [← e0, ← e1]; exact hcv0, ?_,
    by rw [hchil]; omega, hrcsl, hsll, ?_, ?_, ?_, fun ev hmv => ?_, ?_⟩
  · -- the words at the cursor
    rw [readsAt_append_iff, readsAt_append_iff, readsAt_append_iff, readsAt_append_iff]
    refine ⟨⟨⟨⟨?_, fun k hk => ?_⟩, fun k hk => ?_⟩, fun k hk => ?_⟩, fun k hk => ?_⟩
    · refine readsAt_iff_getD.mpr fun k hk => ?_
      rw [hpl] at hk
      rw [← e2, getD_map_range _ _ hk]
      exact (hr1 k hk).1
    · rw [hysl] at hk
      rw [roundWords_getD g _ _ _ hk, ← e2, hpl]
      obtain ⟨w1, w2, -⟩ := hwords (k / 2) (by omega)
      split_ifs with h2
      · rw [show 64 + k = 64 + 2 * (k / 2) by omega]; simpa using w1
      · rw [show 64 + k = 65 + 2 * (k / 2) by omega]; simpa using w2
    · have hk' : k < 2 := by simpa using hk
      rw [List.length_append, hpl, hysl]
      have l2 := lh_at (h2240 ▸ la) (show 64 + 2 * (τ + 8) + 0 = 64 + 2 * (τ + 8) + k - k by omega)
      have l3 := lh_at (h2240 ▸ lb) rfl
      interval_cases k
      · simpa using l2
      · exact l3
    · rw [hzsl] at hk
      rw [List.length_append, List.length_append, hpl, hysl, roundWords_getD g' _ _ _ hk,
        List.length_cons, List.length_cons, List.length_nil, Nat.zero_add]
      obtain ⟨w1, w2, -⟩ := hlc (k / 2) (by omega)
      rw [h2240] at w1 w2
      have w1' := lh_off w1
      have w2' := lh_off w2
      split_ifs with h2
      · simp only [Nat.zero_add]; exact lh_eq w1' (by omega)
      · simp only [Nat.zero_add]; exact lh_eq w2' (by omega)
    · rw [hsll] at hk
      rw [List.length_append, List.length_append, List.length_append, hpl, hysl, hzsl,
        getD_map_range _ _ hk, List.length_cons, List.length_cons, List.length_nil]
      have w := (hsl k hk).1
      rw [h2240] at w
      exact lh_eq (lh_off w) (by omega)
  · -- the zerocheck's point
    rw [← e4]
    refine readsAt_iff_getD.mpr fun k hk => ?_
    rw [hchil] at hk
    rw [getD_map_range _ _ hk]
    exact (hwords k hk).2.2
  · -- the lincheck's challenges
    rw [← e5]
    refine readsAt_iff_getD.mpr fun k hk => ?_
    rw [hrcsl] at hk
    rw [getD_map_range _ _ hk]
    exact (hlc k hk).2.2
  · -- the slices
    rw [← e6]
    refine readsAt_iff_getD.mpr fun k hk => ?_
    rw [hsll] at hk
    rw [getD_map_range _ _ hk]
    exact (hsl k hk).2
  · -- the run
    have hlen : (fixedChallenges ++ (sqAll (τ + 1) cv0).1).length = τ + 8 := by
      rw [List.length_append, fixedChallenges_length, sqAll_eq]; simp; omega
    refine runs_verifyFlock ev τ cv0 p hpl ys chi (scSt e g st0 (τ + 8)).1 (scSt e g st0 (τ + 8)).2
      (fun rest os roots => ?_) (σ (.n 2241)) (σ (.n 2256)) zs rcs (lcSt g' st0' 8).1
      (lcSt g' st0' 8).2 (fun rest os roots => ?_) sl hsll (σ (.n 2719)) ?_ ?_
    · have := runs_sumcheck_eq e g st0 (τ + 8) 0 rest os roots
      simp only [Nat.zero_add] at this
      rw [hsq1, map_some_range, hlen]
      exact this
    · have := runs_sumcheck_plain g' st0' 8 0 rest os roots
      simp only [Nat.zero_add] at this
      rw [← h2740', show List.replicate 8 (none : Option E) = (List.range 8).map (fun _ => none)
        from rfl]
      exact this
    · rw [hsq1]; rw [hα'] at hmv; exact hmv
    · have hdot : σ (.n 4362) * word 11666641484232641359 0 0 = dot (lagrangeWeights 64 z) sl := by
        rw [hcs, ← cslice_eq z sl hsll]
        refine congrArg (fun x => x * _) (Finset.sum_congr rfl fun i hi => ?_)
        rw [hcn i (Finset.mem_range.mp hi), hz', getD_map_range _ _ (Finset.mem_range.mp hi)]
        simp only [Nat.zero_add]
      have heq : eqEval (chi.take 8) rcs.reverse =
          ∏ t ∈ Finset.range 8, (1 + scCh e g st0 t + lcCh g' st0' (7 - t)) := by
        rw [Main.eqEval_prod _ _ 8 (by simp [hchil]) (by simp [hrcsl])]
        refine Finset.prod_congr rfl fun t ht => ?_
        have ht' := Finset.mem_range.mp ht
        rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_pos' ht',
          ← List.getD_eq_getElem?_getD,
          getD_map_range _ _ (by omega), List.getD_eq_getElem?_getD,
          List.getElem?_reverse (by omega), hrcsl, ← List.getD_eq_getElem?_getD,
          getD_map_range _ _ (by omega), show 8 - 1 - t = 7 - t by omega]
      rw [hsq1, ← hα', ← hrlc, hfin, hpin, hcpe, h2735, h2734, hdot, heq,
        colWeight_pin rcs sl hrcsl hsll]
      simp only [hrcs, hsl', getD_map_range _ _ (show 0 < 8 by omega),
        getD_map_range _ _ (show 1 < 8 by omega), getD_map_range _ _ (show 2 < 8 by omega),
        getD_map_range _ _ (show 3 < 8 by omega), getD_map_range _ _ (show 4 < 8 by omega),
        getD_map_range _ _ (show 5 < 8 by omega), getD_map_range _ _ (show 6 < 8 by omega),
        getD_map_range _ _ (show 7 < 8 by omega), getD_map_range _ _ (show 0 < 64 by omega)]
      ring
  · -- the returns
    rw [← hret, r69, r70, r73, r74, r75, r76, hz', h2240]
    simp only [List.cons.injEq, and_true]
    refine ⟨congrArg Prod.fst hcv8, congrArg Prod.snd hcv8, ?_⟩
    rw [mul_assoc, ← pow_add]
    refine congrArg (fun n => cur * gen ^ n) ?_
    simp only [List.length_append, hpl, hysl, hzsl, hsll, List.length_cons, List.length_nil]

end
end LeanVM.Guest.B1
