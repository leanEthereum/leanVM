/-
  LeanVM.Guest.B1.Tables.FlockCTail

  `verify_flock`'s middle segments, complete: the interpolation's scaling, the sampled rounds by
  `__loop82`, the final evaluations, `alpha` and the lincheck's claim, the slices.
-/

module

public import LeanVM.Guest.B1.Tables.FlockCRounds

/-!
# The middle segments, complete

`c_p5` scales the interpolation (the zerocheck's first claim), `c_p7` hands the sampled rounds to
`__loop82` and reads their last row, `c_s8` reads the final evaluations, `c_s10` takes the
matrices' value as its hint, squeezes `alpha` and forms the lincheck's claim, `c_zp` reads the
slices.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig

@[expose] public section

section
variable {rd : Reader} {τ : ℕ} {cv : Digest} {xs : List E} {cur zchis lrs zpart p11 p24 p40 p2220 : E}

theorem getD_take' (l : List E) {n t : ℕ} (h : t < n) : (l.take n).getD t 0 = l.getD t 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-- **The interpolation scaled** (G:1876-1877): the zerocheck's first claim. -/
theorem c_p5 (hlen : xs.length = flLen τ) (σ : Val) (h3 : σ (.n 3) = gen ^ τ)
    (hP : σ (.n 1841) = ∏ j ∈ Finset.range 64, (flZ τ cv xs + phi j))
    (hS : σ (.n 1844) = ∑ j ∈ Finset.range 64, numHi (flZ τ cv xs) j * xs.getD j 0) :
    Completes (coreProgram.Rel rd) rd 1845 1852 flP5 σ
      (fun σ' => σ' (.n 1847) = (flSt0 τ cv xs).1 ∧
        σ' (.n 1851) = gen ^ τ * word 16384 0 0 * word 2017612633061982209 0 0) := by
  refine completes_upds [(1845, word 233317187178767959 0 0),
    (1846, σ (.n 1841) * word 233317187178767959 0 0),
    (1847, σ (.n 1844) * (σ (.n 1841) * word 233317187178767959 0 0)), (1848, word 16384 0 0),
    (1849, gen ^ τ * word 16384 0 0), (1850, word 2017612633061982209 0 0),
    (1851, gen ^ τ * word 16384 0 0 * word 2017612633061982209 0 0)] (by simp)
    (fun next kret hn => ?_) ?_
  · simp only [flP5, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    vs_ev
    rw [h3]
    simp only [true_and]
    exact hn
  · refine ⟨?_, by vs_ev⟩
    vs_ev
    rw [hP, hS, flSt0, interp_eq _ _ (by simp [flP]; unfold flLen at hlen; omega)]
    refine congrArg (· * _) (Finset.sum_congr rfl fun i hi => ?_)
    rw [flP, getD_take' _ (Finset.mem_range.mp hi)]
    rfl

/-! ## The sampled rounds -/

/-- What `flP7` leaves: the zerocheck's last row. -/
def flP7Out (τ : ℕ) (cv : Digest) (xs : List E) (cur p2220 v : E) : List (ℕ × E) :=
  [(2237, (digestScalars (flScAt τ cv xs (τ + 8)).2).1),
    (2238, (digestScalars (flScAt τ cv xs (τ + 8)).2).2), (2239, (flScAt τ cv xs (τ + 8)).1),
    (2240, cur * gen ^ (64 + 2 * (τ + 8))), (2220, p2220),
    (2219, v * word 4 0 0 * (v * word 4 0 0) * (v * word 4 0 0 * (v * word 4 0 0))),
    (2222, p2220 * word 268435456 0 0),
    (2236, p2220 * (gen ^ τ * word 256 0 0 * (gen ^ τ * word 256 0 0) *
      (gen ^ τ * word 256 0 0 * (gen ^ τ * word 256 0 0)))),
    (2228, word 128 0 0 + gen ^ τ * word 256 0 0), (2229, word 128 0 0), (2231, gen ^ τ * word 256 0 0)]

/-- **The sampled rounds** (G:1888-1910): row 7 of `flock_rounds` checked, `__loop82`, the last
row read. -/
theorem c_p7 (hτ : τ < 29) (hM : FlMem rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220) (σ : Val)
    (hF : Fixes σ [(2, cur), (3, gen ^ τ), (4, zchis), (11, p11)])
    (hI : FrInv τ cv xs cur zchis p11 7 σ) :
    Completes (coreProgram.Rel rd) rd 2216 2241 flP7 σ (fun σ' => Fixes σ' (flP7Out τ cv xs cur p2220 (σ (.n 1851)))) := by
  have h2 : σ (.n 2) = cur := hF.get (k := 2) (e := cur) (by simp)
  have h3 : σ (.n 3) = gen ^ τ := hF.get (k := 3) (e := gen ^ τ) (by simp)
  have h4 : σ (.n 4) = zchis := hF.get (k := 4) (e := zchis) (by simp)
  have h11 : σ (.n 11) = p11 := hF.get (k := 11) (e := p11) (by simp)
  obtain ⟨-, hc7, hs7⟩ := hI
  have e2203 : σ (.n 2203) = (digestScalars (flScAt τ cv xs 7).2).1 := congrArg Prod.fst hs7
  have e2204 : σ (.n 2204) = (digestScalars (flScAt τ cv xs 7).2).2 := congrArg Prod.snd hs7
  have e2215 : σ (.n 2215) = (flScAt τ cv xs 7).1 := hc7
  obtain ⟨r0, r1, r2, r3⟩ := hM.rnd 7 le_rfl (by omega)
  obtain ⟨n0, n1, n2, n3⟩ := hM.rnd (τ + 8) (by omega) le_rfl
  set g := gen ^ τ * word 256 0 0
  refine completes_upds [(2216, word 4 0 0), (2217, σ (.n 1851) * word 4 0 0),
    (2218, σ (.n 1851) * word 4 0 0 * (σ (.n 1851) * word 4 0 0)),
    (2219, σ (.n 1851) * word 4 0 0 * (σ (.n 1851) * word 4 0 0) *
      (σ (.n 1851) * word 4 0 0 * (σ (.n 1851) * word 4 0 0))),
    (2220, p2220), (2221, word 268435456 0 0), (2222, p2220 * word 268435456 0 0),
    (2223, word 442368 0 0), (2224, cur * word 442368 0 0), (2225, word 128 0 0),
    (2226, word 256 0 0), (2227, g), (2228, word 128 0 0 + g), (2229, word 128 0 0),
    (2230, word 256 0 0), (2231, g), (2232, word 256 0 0), (2233, g), (2234, g * g),
    (2235, g * g * (g * g)), (2236, p2220 * (g * g * (g * g))),
    (2237, (digestScalars (flScAt τ cv xs (τ + 8)).2).1),
    (2238, (digestScalars (flScAt τ cv xs (τ + 8)).2).2), (2239, (flScAt τ cv xs (τ + 8)).1),
    (2240, cur * gen ^ (64 + 2 * (τ + 8)))] (by simp) (fun next kret hn => ?_) ?_
  · simp only [flP7, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
    vs_ev
    rw [h2, h3, h4, h11, e2203, e2204, e2215]
    have hg : g = gen ^ (τ + 8) := by simp only [g, word_g8, ← pow_add]
    have hq : g * g * (g * g) = gen ^ (4 * (τ + 8)) := by rw [hg, gen_pow_quad]
    simp only [true_and, word_g28, word_g78, word_g7, hq]
    refine ⟨lh_back r0 (by omega), lh_back r1 (by omega), lh_back r2 (by omega),
      lh_back r3 (by omega), rfl, rfl, ?_, fun _ => ?_, rfl, lh_back n0 (by omega),
      lh_back n1 (by omega), lh_back n3 (by omega), lh_back n2 (by omega), hn⟩
    · rw [hg]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
    · rw [hg]; exact loop82_complete hτ hM
  · intro p hp
    simp only [flP7Out, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [upds_n, g]

/-! ## The final evaluations and `alpha` -/

/-- **The final evaluations** (G:1914-1916). -/
theorem c_s8 (hM : FlMem rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220) (σ : Val)
    {v : E} (hF : Fixes σ (flP7Out τ cv xs cur p2220 v)) :
    Completes (coreProgram.Rel rd) rd 2241 2273 flS8 σ (fun σ' =>
      σ' (.n 2241) = flA τ xs ∧ σ' (.n 2256) = flB τ xs ∧
      (σ' (.n 2269), σ' (.n 2270)) = digestScalars (flCv5 τ cv xs) ∧
      σ' (.n 2272) = (flSc τ cv xs).1 + flA τ xs * flB τ xs) := by
  have hcu : σ (.n 2240) = cur * gen ^ (64 + 2 * (τ + 8)) := hF.get (by simp [flP7Out])
  have hcl : σ (.n 2239) = (flSc τ cv xs).1 := hF.get (k := 2239) (by simp [flP7Out]; rfl)
  have hs : (σ (.n 2237), σ (.n 2238)) = digestScalars (flScAt τ cv xs (τ + 8)).2 :=
    Prod.ext (hF.get (by simp [flP7Out])) (hF.get (by simp [flP7Out]))
  simp only [flS8, List.append_assoc]
  refine Completes.append (m := 2256) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (completes_fsNextT (x := flA τ xs) (cv := (flSc τ cv xs).2) ⟨_, by omega, rfl⟩
      ⟨_, by omega, rfl⟩ ⟨2240, by omega, rfl⟩ hs
      (by rw [hcu]; exact lh_back (hM.words _ (by unfold flLen; omega)) (by omega))
      (Post := fun σ' => Ext 2241 2256 σ σ' ∧ σ' (.n 2241) = flA τ xs ∧
        (σ' (.n (2241 + 13)), σ' (.n (2241 + 14))) =
          digestScalars (obsCv (flSc τ cv xs).2 (flA τ xs)))
      fun σ' he hb ho => ⟨he, hb, ho⟩) fun σ2 _ ⟨he2, ha, ho2⟩ => ?_
  refine Completes.append (m := 2271) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (completes_fsNextT (x := flB τ xs) (cv := obsCv (flSc τ cv xs).2 (flA τ xs)) ⟨_, by omega, rfl⟩
      ⟨_, by omega, rfl⟩ ⟨2240, by omega, rfl⟩ ho2
      (by rw [he2.apply (Or.inl (by omega)), hcu]
          exact lh_back (hM.words _ (by unfold flLen; omega)) (by omega))
      (Post := fun σ' => Ext 2256 2271 σ2 σ' ∧ σ' (.n 2256) = flB τ xs ∧
        (σ' (.n (2256 + 13)), σ' (.n (2256 + 14))) = digestScalars (flCv5 τ cv xs))
      fun σ' he hb ho => ⟨he, hb, ho⟩) fun σ3 _ ⟨he3, hb, ho3⟩ => ?_
  have f2241 : σ3 (.n 2241) = flA τ xs := by rw [he3.apply (Or.inl (by omega))]; exact ha
  have f2239 : σ3 (.n 2239) = (flSc τ cv xs).1 := by
    rw [he3.apply (Or.inl (by omega)), he2.apply (Or.inl (by omega)), hcl]
  refine completes_upds [(2271, flA τ xs * flB τ xs), (2272, (flSc τ cv xs).1 + flA τ xs * flB τ xs)]
    (by simp) (fun next kret hn => ?_) ⟨?_, ?_, ?_, ?_⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    vs_ev
    rw [f2241, hb, f2239]
    exact ⟨rfl, rfl, hn⟩
  · vs_ev; exact f2241
  · vs_ev; exact hb
  · vs_ev; exact ho3
  · vs_ev

/-- What `alpha`'s segment leaves: the matrices' value, `alpha`, its powers, the lincheck's
start. -/
def flS10Out (τ : ℕ) (cv : Digest) (xs : List E) (mv : E) : List (ℕ × E) :=
  [(2719, mv), (2725, (digestScalars (flSt0' τ cv xs).2).1),
    (2726, (digestScalars (flSt0' τ cv xs).2).2), (2733, flAlpha τ cv xs),
    (2734, flAlpha τ cv xs * flAlpha τ cv xs),
    (2735, flAlpha τ cv xs * flAlpha τ cv xs * flAlpha τ cv xs), (2740, (flSt0' τ cv xs).1)]

/-- **The matrices' value, `alpha` and the lincheck's claim** (G:1926-1930). -/
theorem c_s10 (mv : E) (σ : Val) (ha : σ (.n 2241) = flA τ xs) (hb : σ (.n 2256) = flB τ xs)
    (hs : (σ (.n 2269), σ (.n 2270)) = digestScalars (flCv5 τ cv xs))
    (hc : σ (.n 2272) = (flSc τ cv xs).1 + flA τ xs * flB τ xs) :
    Completes (coreProgram.Rel rd) rd 2719 2741 flS10 σ (fun σ' => Fixes σ' (flS10Out τ cv xs mv)) := by
  simp only [flS10]
  rw [List.cons_append]
  refine Completes.atom_cons mv (by omega) (NumBelow.cons ⟨2719, by omega, rfl⟩ (NumBelow.nil _))
    trivial ?_
  set σ1 := Function.update σ (.n 2719) mv
  have k1 : ∀ j < 2719, σ1 (.n j) = σ (.n j) := fun j hj => upd_ne (by omega)
  set α := flAlpha τ cv xs
  refine Completes.append (m := 2734) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (completes_squeezeT (cv := flCv5 τ cv xs) ⟨2269, by omega, rfl⟩ ⟨2270, by omega, rfl⟩
      (by rw [k1 _ (by omega), k1 _ (by omega)]; exact hs)
      (Post := fun σ' => Ext 2720 2734 σ1 σ' ∧
        (σ' (.n (2720 + 5)), σ' (.n (2720 + 6))) = digestScalars (sqCv (flCv5 τ cv xs)) ∧
        σ' (.n (2720 + 13)) = α) fun σ' he h1 h2 => ⟨he, h1, h2⟩) fun σ2 _ ⟨he2, hs2, hα⟩ => ?_
  have a2 : ∀ j < 2719, σ2 (.n j) = σ (.n j) := fun j hj => by
    rw [he2.apply (Or.inl (by omega)), k1 j hj]
  have f2719 : σ2 (.n 2719) = mv := by rw [he2.apply (Or.inl (by omega))]; simp [σ1]
  have fα : σ2 (.n 2733) = α := hα
  refine completes_upds [(2734, α * α), (2735, α * α * α), (2736, α * flB τ xs),
    (2737, flA τ xs + α * flB τ xs), (2738, α * α * ((flSc τ cv xs).1 + flA τ xs * flB τ xs)),
    (2739, flA τ xs + α * flB τ xs + α * α * ((flSc τ cv xs).1 + flA τ xs * flB τ xs)),
    (2740, flA τ xs + α * flB τ xs + α * α * ((flSc τ cv xs).1 + flA τ xs * flB τ xs) + α * α * α)]
    (by simp) (fun next kret hn => ?_) ?_
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    vs_ev
    rw [fα, a2 _ (by omega), a2 _ (by omega), a2 _ (by omega), ha, hb, hc]
    simp only [true_and]
    exact hn
  · intro p hp
    simp only [flS10Out, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · vs_ev; exact f2719
    · vs_ev; exact congrArg Prod.fst hs2
    · vs_ev; exact congrArg Prod.snd hs2
    · vs_ev; exact fα
    · vs_ev; rfl
    · vs_ev; rfl
    · vs_ev
      simp only [flSt0', α]
      ring

/-! ## The slices -/

theorem flS_getD (τ : ℕ) (xs : List E) {i : ℕ} (hi : i < 64) :
    (flS τ xs).getD i 0 = xs.getD (82 + 2 * (τ + 8) + i) 0 := by
  simp [flS, List.getD_eq_getElem?_getD, hi]

theorem zp_below : ∀ i < 64, numBelowB (3133 + 15 * (i + 1)) (Stmt.valsList (zpBlk i)) = true := by
  decide +kernel

/-- **The slices** (G:1939-1941): read, absorbed, checked against `z_partial`. -/
theorem c_zp (hM : FlMem rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220)
    (hlen : xs.length = flLen τ) (σ : Val)
    (hF : Fixes σ [(6, zpart), (2240, cur * gen ^ (64 + 2 * (τ + 8)))])
    (hs : (σ (.n 3120), σ (.n 3121)) = digestScalars (flLc τ cv xs).2) :
    Completes (coreProgram.Rel rd) rd 3133 4093 ((List.range 64).map zpBlk).flatten σ
      (fun σ' => Fixes σ' [(6, zpart), (2240, cur * gen ^ (64 + 2 * (τ + 8)))] ∧
        (σ' (.n 4091), σ' (.n 4092)) = digestScalars (obsAll (flLc τ cv xs).2 (flS τ xs))) := by
  have hsl : (flS τ xs).length = 64 := by simp [flS]; unfold flLen at hlen; omega
  have := Completes.flatten (C := coreProgram.Rel rd) (rd := rd) (blk := zpBlk)
    (st := fun i => 3133 + 15 * i)
    (Inv := fun i σ => Fixes σ [(6, zpart), (2240, cur * gen ^ (64 + 2 * (τ + 8)))] ∧
      (σ (.n (zpS i)), σ (.n (zpS i + 1))) =
        digestScalars (obsAll (flLc τ cv xs).2 ((flS τ xs).take i))) 64 (fun i _ => by omega)
    (fun i hi => numBelow_of_B (zp_below i hi)) (fun i hi σ ⟨hF, hs⟩ => ?_) σ
    ⟨hF, by show (σ (.n 3120), σ (.n 3121)) = _; rw [List.take_zero]; exact hs⟩
  · have ht : (flS τ xs).take 64 = flS τ xs := by rw [List.take_of_length_le (by omega)]
    rw [ht] at this
    exact this
  · rw [show 3133 + 15 * (i + 1) = 3133 + 15 * i + 15 by ring]
    have hb : zpS i + 1 < 3133 + 15 * i := by unfold zpS; split <;> omega
    have hcu : σ (.n 2240) = cur * gen ^ (64 + 2 * (τ + 8)) := hF.get (by simp)
    refine Completes.append_atom (P := fun σ' => Ext (3133 + 15 * i) (3133 + 15 * i + 15) σ σ' ∧
      σ' (.n (3133 + 15 * i)) = (flS τ xs).getD i 0 ∧
      (σ' (.n (3133 + 15 * i + 13)), σ' (.n (3133 + 15 * i + 14))) =
        digestScalars (obsCv (obsAll (flLc τ cv xs).2 ((flS τ xs).take i)) ((flS τ xs).getD i 0)))
      (completes_fsNextT ⟨_, by omega, rfl⟩ ⟨_, hb, rfl⟩ ⟨2240, by omega, rfl⟩ hs
        (by rw [hcu, flS_getD τ xs hi]; exact lh_back (hM.words _ (by unfold flLen; omega)) (by omega))
        fun σ' he hb ho => ⟨he, hb, ho⟩) fun σ' ⟨he, hx, ho⟩ => ⟨?_, ?_, ?_⟩
    · show LoadHolds rd (σ' (.n 6)) i (σ' (.n (3133 + 15 * i)))
      rw [he.apply (Or.inl (by omega)), hF.get (k := 6) (e := zpart) (by simp), hx, flS_getD τ xs hi]
      exact hM.sl i hi
    · exact hF.of_ext he (by simp; omega)
    · rw [show zpS (i + 1) = 3133 + 15 * i + 13 by unfold zpS; simp; omega,
        obsAll_take_succ _ _ (by omega)]
      exact ho

end

end
end LeanVM.Guest.B1
