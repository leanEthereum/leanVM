/-
  LeanVM.Guest.B1.Tables.FlockCBody

  `verify_flock`'s body, complete, segment by segment: the prelude, round 1, the skip challenge
  and the interpolation.
-/

module

public import LeanVM.Guest.B1.Tables.FlockComplete

/-!
# `verify_flock`'s first segments, complete

Each lemma completes one segment of `flSegs` on its range of values over the honest memory
(`FlMem`), from the values it reads (`Fixes`) to the values later segments read.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig

@[expose] public section

/-- Evaluate an updated valuation at value numbers differing by literals. -/
macro "fl_ev" : tactic =>
  `(tactic| simp only [upds_n, upds_nil, Nat.add_right_cancel_iff, Nat.add_left_cancel_iff,
    Nat.reduceEqDiff, add_eq_left, left_eq_add, OfNat.ofNat_ne_zero, one_ne_zero, ↓reduceIte])

section
variable {rd : Reader} {τ : ℕ} {cv : Digest} {xs : List E} {cur zchis lrs zpart p11 p24 p40 p2220 : E}

/-- The arguments. -/
def flArgs (τ : ℕ) (cv : Digest) (cur zchis lrs zpart : E) : List (ℕ × E) :=
  [(0, (digestScalars cv).1), (1, (digestScalars cv).2), (2, cur), (3, gen ^ τ), (4, zchis),
    (5, lrs), (6, zpart)]

/-- What the prelude leaves. -/
def flP0Out (τ : ℕ) (cv : Digest) (p11 p24 p40 : E) : List (ℕ × E) :=
  [(11, p11), (24, p24), (38, (digestScalars (sqCv^[τ + 1] cv)).1),
    (39, (digestScalars (sqCv^[τ + 1] cv)).2), (40, p40), (10, gen ^ τ * word 16384 0 0),
    (23, gen ^ τ * word 16384 0 0 * word 4 0 0 * (gen ^ τ * word 16384 0 0 * word 4 0 0)),
    (26, p24 * word 67108864 0 0), (37, p24 * (gen ^ τ * word 16384 0 0 * (gen ^ τ * word 16384 0 0))),
    (30, word 8192 0 0 + gen ^ τ * word 16384 0 0), (31, word 8192 0 0), (33, gen ^ τ * word 16384 0 0)]

theorem fixed_getD (τ : ℕ) (cv : Digest) {i : ℕ} (hi : i < 7) :
    flE τ cv i = fixedWords.getD i 0 := by
  simp only [flE]
  rw [getD_append_lt (by rw [fixedChallenges_length]; exact hi), fixed_words]

/-- **The prelude** (G:1843-1858). -/
theorem c_p0 (hτ : τ < 29) (hM : FlMem rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220)
    (σ : Val) (hσ : Fixes σ (flArgs τ cv cur zchis lrs zpart)) :
    Completes (coreProgram.Rel rd) rd 7 41 flP0 σ (fun σ' => Fixes σ' (flP0Out τ cv p11 p24 p40)) := by
  have h0 : σ (.n 0) = (digestScalars cv).1 := hσ.get (by simp [flArgs])
  have h1 : σ (.n 1) = (digestScalars cv).2 := hσ.get (by simp [flArgs])
  have h3 : σ (.n 3) = gen ^ τ := hσ.get (by simp [flArgs])
  have hz : ∀ i < 7, LoadHolds rd p11 (6 + i) (fixedWords.getD i 0) := fun i hi => by
    rw [← fixed_getD τ cv hi]; exact hM.zr i (by omega)
  obtain ⟨a0, a1⟩ := hM.pts 0 (by omega)
  obtain ⟨b0, b1⟩ := hM.pts (τ + 1) le_rfl
  refine completes_upds [(7, (digestScalars cv).1), (8, (digestScalars cv).2),
    (9, word 16384 0 0), (10, gen ^ τ * word 16384 0 0), (11, p11),
    (12, word 5772811086190238293 0 0), (13, word 18376177690117868746 0 0),
    (14, word 1537792354547671042 0 0),
    (15, word 3877548338577296374 1367482035892397521 13373126565067795492),
    (16, word 7200243516802924451 16251485319816311889 13522021764491415548),
    (17, word 14498505783250251438 16564499533431716054 16770611540025040673),
    (18, word 3934799921294095118 853327055063395975 1309330797735322834),
    (19, word 16384 0 0), (20, gen ^ τ * word 16384 0 0), (21, word 4 0 0),
    (22, gen ^ τ * word 16384 0 0 * word 4 0 0),
    (23, gen ^ τ * word 16384 0 0 * word 4 0 0 * (gen ^ τ * word 16384 0 0 * word 4 0 0)),
    (24, p24), (25, word 67108864 0 0), (26, p24 * word 67108864 0 0), (27, word 8192 0 0),
    (28, word 16384 0 0), (29, gen ^ τ * word 16384 0 0), (30, word 8192 0 0 + gen ^ τ * word 16384 0 0),
    (31, word 8192 0 0), (32, word 16384 0 0), (33, gen ^ τ * word 16384 0 0), (34, word 16384 0 0),
    (35, gen ^ τ * word 16384 0 0), (36, gen ^ τ * word 16384 0 0 * (gen ^ τ * word 16384 0 0)),
    (37, p24 * (gen ^ τ * word 16384 0 0 * (gen ^ τ * word 16384 0 0))),
    (38, (digestScalars (sqCv^[τ + 1] cv)).1), (39, (digestScalars (sqCv^[τ + 1] cv)).2),
    (40, p40)] (by simp) (fun next kret hn => ?_) ?_
  · simp only [flP0, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
    vs_ev
    rw [h0, h1, h3]
    simp only [true_and, word_g13, word_g14, word_g26]
    refine ⟨hz 0 (by omega), hz 1 (by omega), hz 2 (by omega), hz 3 (by omega), hz 4 (by omega),
      hz 5 (by omega), hz 6 (by omega), lh_back a0 (by omega), lh_back a1 (by omega), ?_, ?_, ?_,
      ?_, hn⟩
    · exact isInK_add (gen_pow_isInK _) (isInK_mul (gen_pow_isInK _) (gen_pow_isInK _))
    · intro _
      rw [← pow_add]
      exact loop81_complete hτ hM
    · rw [← pow_add, gen_pow_sq]
      exact lh_back b0 (by omega)
    · rw [← pow_add, gen_pow_sq]
      exact lh_back b1 (by omega)
  · intro p hp
    simp only [flP0Out, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [upds_n]

/-! ## Round 1 -/

theorem obsAll_take_succ (cv : Digest) (l : List E) {i : ℕ} (hi : i < l.length) :
    obsAll cv (l.take (i + 1)) = obsCv (obsAll cv (l.take i)) (l.getD i 0) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, obsAll_snoc,
    List.getD_eq_getElem _ _ hi]

theorem rd1_below : ∀ i < 64, numBelowB (41 + 15 * (i + 1)) (Stmt.valsList (rd1Blk i)) = true := by
  decide +kernel

/-- **Round 1's words** (G:1864-1866): read, absorbed, stored at `flock_pts_r1`. -/
theorem c_rd1 (hM : FlMem rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220)
    (hlen : xs.length = flLen τ) (σ : Val) (hF : Fixes σ [(2, cur), (40, p40)])
    (hs : (σ (.n 38), σ (.n 39)) = digestScalars (sqCv^[τ + 1] cv)) :
    Completes (coreProgram.Rel rd) rd 41 1001 ((List.range 64).map rd1Blk).flatten σ
      (fun σ' => Fixes σ' [(2, cur), (40, p40)] ∧
        (σ' (.n 999), σ' (.n 1000)) = digestScalars (obsAll (sqCv^[τ + 1] cv) (flP xs))) := by
  have := Completes.flatten (C := coreProgram.Rel rd) (rd := rd) (blk := rd1Blk)
    (st := fun i => 41 + 15 * i)
    (Inv := fun i σ => Fixes σ [(2, cur), (40, p40)] ∧ (σ (.n (rd1S i)), σ (.n (rd1S i + 1))) =
      digestScalars (obsAll (sqCv^[τ + 1] cv) (xs.take i))) 64 (fun i _ => by omega)
    (fun i hi => numBelow_of_B (rd1_below i hi)) (fun i hi σ ⟨hF, hs⟩ => ?_) σ
    ⟨hF, by show (σ (.n 38), σ (.n 39)) = _; rw [List.take_zero]; exact hs⟩
  · exact this
  · rw [show 41 + 15 * (i + 1) = 41 + 15 * i + 15 by ring]
    have hb : rd1S i + 1 < 41 + 15 * i := by unfold rd1S; split <;> omega
    refine Completes.append_atom (P := fun σ' => Ext (41 + 15 * i) (41 + 15 * i + 15) σ σ' ∧
      σ' (.n (41 + 15 * i)) = xs.getD i 0 ∧ (σ' (.n (41 + 15 * i + 13)), σ' (.n (41 + 15 * i + 14))) =
        digestScalars (obsCv (obsAll (sqCv^[τ + 1] cv) (xs.take i)) (xs.getD i 0)))
      (completes_fsNextT ⟨_, by omega, rfl⟩ ⟨_, hb, rfl⟩ ⟨2, by omega, rfl⟩ hs
        (by rw [hF.get (k := 2) (e := cur) (by simp)]; exact hM.words i (by unfold flLen; omega))
        fun σ' he hb ho => ⟨he, hb, ho⟩) fun σ' ⟨he, hx, ho⟩ => ⟨?_, ?_, ?_⟩
    · show LoadHolds rd (σ' (.n 40)) i (σ' (.n (41 + 15 * i)))
      rw [he.apply (Or.inl (by omega)), hF.get (k := 40) (e := p40) (by simp), hx]
      exact hM.p1 i hi
    · exact hF.of_ext he (by simp; omega)
    · rw [show rd1S (i + 1) = 41 + 15 * i + 13 by unfold rd1S; simp; omega,
        obsAll_take_succ _ _ (by unfold flLen at hlen; omega)]
      exact ho

/-- **The skip challenge** (G:1868). -/
theorem c_sq1 (σ : Val) {cvP : Digest} (hs : (σ (.n 999), σ (.n 1000)) = digestScalars cvP) :
    Completes (coreProgram.Rel rd) rd 1001 1015 (squeezeT (.n 999) (.n 1000) 1001) σ
      (fun σ' => (σ' (.n 1006), σ' (.n 1007)) = digestScalars (sqCv cvP) ∧
        σ' (.n 1014) = challengeOf (sqCv cvP)) :=
  completes_squeezeT ⟨999, by omega, rfl⟩ ⟨1000, by omega, rfl⟩ hs fun _ _ h1 h2 => ⟨h1, h2⟩

/-! ## The numerators -/

/-- The words of a chain of `lag64`. -/
def lgLenN (node : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | i, n + 1 => (if node i = 0 then 1 else 3) + lgLenN node (i + 1) n

theorem lgRunV_length (x : E) (node : ℕ → ℕ) :
    ∀ i n P, (lgRunV x node i n P).length = lgLenN node i n
  | _, 0, _ => rfl
  | i, n + 1, P => by
    rw [lgRunV, List.length_append, lgRunV_length x node (i + 1) n, lgLenN, lgStepV]
    split <;> rfl

theorem lag64V_length (x : E) (node : ℕ → ℕ) :
    (lag64V x node).length = 66 + lgLenN node 0 64 + lgLenN (fun i => node (63 - i)) 0 64 := by
  simp only [lag64V, List.length_append, List.length_cons, List.length_nil, lgRunV_length,
    List.length_map, List.length_range]
  omega

theorem lgLen_hi : lgLenN (phi8From 64) 0 64 = 192 ∧
    lgLenN (fun i => phi8From 64 (63 - i)) 0 64 = 192 := by decide +kernel

theorem lgLen_lo : lgLenN (phi8From 0) 0 64 = 190 ∧
    lgLenN (fun i => phi8From 0 (63 - i)) 0 64 = 190 := by decide +kernel

/-- **`lag64` complete** at `z = σ zv` from `k`: its honest words give the numerators over the
skip nodes from `b`. -/
theorem c_lag {zv : ℕ} {z : E} {b k n : ℕ} (hb : b + 64 ≤ 128) (hzk : zv < k)
    (hn : (lag64V z (phi8From b)).length = n) (σ : Val) (hz : σ (.n zv) = z) :
    Completes (coreProgram.Rel rd) rd k (k + n) (lag64T (.n zv) (phi8From b) k) σ
      (fun σ' => ∀ i < 64, σ' (.n (lgOut (.n zv) (phi8From b) k + i)) =
        ∏ j ∈ (Finset.range 64).erase i, (z + phi (b + j))) := by
  have hz1 : setv σ k n (fun i => (lag64V z (phi8From b)).getD i 0) (.n zv) = z := by
    rw [set_n_lt hzk, hz]
  have hok : Lag64Ok (setv σ k n fun i => (lag64V z (phi8From b)).getD i 0) (.n zv) (phi8From b) k :=
    lag64_of_agree hz1 fun i hi => by
      rw [set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  refine completes_setv _ (fun next kret hnx => (holds_lag64T _ _ _ _ _).mpr ⟨hok, hnx⟩) ?_
  intro i hi
  rw [lag64_phi hb hok i hi, hz1]

/-! ## The interpolation -/

/-- The numerators over the upper skip nodes. -/
def numHi (z : E) (i : ℕ) : E := ∏ j ∈ (Finset.range 64).erase i, (z + phi (64 + j))

/-- The interpolation's invariant before term `i`. -/
def IpInv (p40 z : E) (xs : List E) (i : ℕ) (σ : Val) : Prop :=
  Fixes σ [(40, p40), (1014, z)] ∧ (∀ j < 64, σ (.n (1401 + j)) = numHi z j) ∧
    (0 < i → σ (.n (if i = 1 then 1014 else 1457 + 6 * i)) = ∏ j ∈ Finset.range i, (z + phi j) ∧
      σ (.n (if i = 1 then 1466 else 1460 + 6 * i)) =
        ∑ j ∈ Finset.range i, numHi z j * xs.getD j 0)

/-- The values of term `i ≥ 1`, from the product `P` and the sum `S` so far. -/
def ipVals (z P S : E) (xs : List E) (i : ℕ) : List (ℕ × E) :=
  [(1461 + 6 * i, word (phi8Words.getD i 0) 0 0), (1462 + 6 * i, z + word (phi8Words.getD i 0) 0 0),
    (1463 + 6 * i, P * (z + word (phi8Words.getD i 0) 0 0)), (1464 + 6 * i, xs.getD i 0),
    (1465 + 6 * i, numHi z i * xs.getD i 0), (1466 + 6 * i, S + numHi z i * xs.getD i 0)]

theorem ipVals_range (z P S : E) (xs : List E) (i : ℕ) :
    ∀ p ∈ ipVals z P S xs i, 1461 + 6 * i ≤ p.1 ∧ p.1 < 1461 + 6 * i + 6 := by
  simp only [ipVals, List.mem_cons, List.not_mem_nil, or_false]
  rintro p (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp <;> omega

/-- The interpolation's ranges. -/
def ipSt (i : ℕ) : ℕ := if i = 0 then 1465 else 1461 + 6 * i

theorem ip_below : ∀ i < 64, numBelowB (ipSt (i + 1)) (Stmt.valsList (ipBlk i)) = true := by
  decide +kernel

theorem ipInv_keep {p40 z : E} {xs : List E} {i lo hi : ℕ} {σ σ' : Val} (h : IpInv p40 z xs i σ)
    (he : Ext lo hi σ σ') (hlo : 1465 ≤ lo) :
    Fixes σ' [(40, p40), (1014, z)] ∧ ∀ j < 64, σ' (.n (1401 + j)) = numHi z j :=
  ⟨h.1.of_ext he (by simp; omega), fun j hj => by rw [he.apply (Or.inl (by omega)), h.2.1 j hj]⟩

/-- **The interpolation's terms** (G:1873-1875). -/
theorem c_ip (hM : FlMem rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220) {z : E} (σ : Val)
    (h0 : IpInv p40 z xs 0 σ) :
    Completes (coreProgram.Rel rd) rd 1465 1845 ((List.range 64).map ipBlk).flatten σ
      (fun σ' => IpInv p40 z xs 64 σ') := by
  refine Completes.flatten (st := ipSt) (Inv := IpInv p40 z xs) 64
    (fun i _ => by unfold ipSt; split <;> split <;> omega)
    (fun i hi => numBelow_of_B (ip_below i hi)) (fun i hi σ hI => ?_) σ h0
  have h40 : σ (.n 40) = p40 := hI.1.get (k := 40) (e := p40) (by simp)
  have hz : σ (.n 1014) = z := hI.1.get (k := 1014) (e := z) (by simp)
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · refine completes_upds [(1465, xs.getD 0 0), (1466, numHi z 0 * xs.getD 0 0)] (by simp [ipSt])
      (fun next kret hn => ?_) ?_
    · simp only [ipBlk, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
      vs_ev
      rw [h40, hI.2.1 0 (by omega)]
      exact ⟨hM.p1 0 (by omega), rfl, hn⟩
    · have he := upds_ext (lo := 1465) (hi := 1467) σ [(1465, xs.getD 0 0),
        (1466, numHi z 0 * xs.getD 0 0)] (by simp)
      refine ⟨(ipInv_keep hI he le_rfl).1, (ipInv_keep hI he le_rfl).2, fun _ => ⟨?_, ?_⟩⟩
      · simp only [Nat.zero_add, ↓reduceIte, Finset.prod_range_one, phi_zero, add_zero]
        rw [upds_of_not_mem σ _ (by simp), hz]
      · simp only [Nat.zero_add, ↓reduceIte, Finset.sum_range_one]
        vs_ev
  · obtain ⟨hP, hS⟩ := hI.2.2 hpos
    have hi' : ¬ i = 0 := by omega
    set P := σ (.n (if i = 1 then 1014 else 1457 + 6 * i))
    set S := σ (.n (if i = 1 then 1466 else 1460 + 6 * i))
    have hsi : ipSt i = 1461 + 6 * i := by simp [ipSt, hi']
    have hsi1 : ipSt (i + 1) = 1461 + 6 * i + 6 := by simp [ipSt]; omega
    rw [hsi, hsi1]
    refine completes_upds (ipVals z P S xs i) (ipVals_range z P S xs i) (fun next kret hn => ?_) ?_
    · simp only [ipBlk, hi', ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
      have e1 : ∀ k < 1461 + 6 * i, upds σ (ipVals z P S xs i) (.n k) = σ (.n k) := fun k hk =>
        upds_of_not_mem σ _ fun p hp => by
          have := ipVals_range z P S xs i p hp
          simp only [ne_eq, V.mk.injEq, true_and]; omega
      rw [e1 1014 (by omega), e1 40 (by omega), e1 (1401 + i) (by omega),
        e1 (if i = 1 then 1014 else 1457 + 6 * i) (by split <;> omega),
        e1 (if i = 1 then 1466 else 1460 + 6 * i) (by split <;> omega), hz, h40,
        hI.2.1 i (by omega)]
      simp only [ipVals]
      fl_ev
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hn⟩ <;> first | trivial | rfl | exact hM.p1 i hi
    · have he := upds_ext σ _ (ipVals_range z P S xs i)
      obtain ⟨k1, k2⟩ := ipInv_keep hI he (by omega)
      refine ⟨k1, k2, fun _ => ⟨?_, ?_⟩⟩
      · rw [ite_neg' (by omega), show 1457 + 6 * (i + 1) = 1463 + 6 * i by ring]
        simp only [ipVals]
        fl_ev
        rw [hP, word_phi8Words (by omega), Finset.prod_range_succ]
      · rw [ite_neg' (by omega), show 1460 + 6 * (i + 1) = 1466 + 6 * i by ring]
        simp only [ipVals]
        fl_ev
        rw [hS, Finset.sum_range_succ]

end

end
end LeanVM.Guest.B1
