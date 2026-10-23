/-
  LeanVM.Guest.B1.Tables.FlockCAll

  `verify_flock` complete (TRIAGE #40): its segments in sequence over the honest memory, and
  `CompleteFlock`.
-/

module

public import LeanVM.Guest.B1.Tables.FlockCEnd
public import LeanVM.Guest.B1.VerifySub.CompleteIface

/-!
# `verify_flock`, complete

`c_end`: the final check and the returns. `flock_body_complete`: the seventeen segments of
`flSegs` complete in sequence from the arguments over the honest memory `FlMem`, the matrices'
value `mv` passing the terminal check (`flTerm`). `verify_flock_rel`: then `verify_flock` holds of
the run's returns.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig

@[expose] public section

section
variable {rd : Reader} {τ : ℕ} {cv : Digest} {xs : List E} {cur zchis lrs zpart p11 p24 p40 p2220 : E}

/-- **The final check and the returns** (G:1955-1963). -/
theorem c_end {mv pinT a2 cpe S s0 s1 c z α : E} (σ : Val) (h3132 : σ (.n 3132) =
      mv + pinT + a2 * cpe * (S * word 11666641484232641359 0 0))
    (h4362 : σ (.n 4362) = S) (h2719 : σ (.n 2719) = mv) (h4124 : σ (.n 4124) = pinT)
    (h2734 : σ (.n 2734) = a2) (h4171 : σ (.n 4171) = cpe) (h4091 : σ (.n 4091) = s0)
    (h4092 : σ (.n 4092) = s1) (h2240 : σ (.n 2240) = c) (h1014 : σ (.n 1014) = z)
    (h2733 : σ (.n 2733) = α) :
    Completes (coreProgram.Rel rd) rd 4363 4377 flPEnd σ (fun σ' =>
      [σ' (.n 4369), σ' (.n 4370), σ' (.n 4373), σ' (.n 4374), σ' (.n 4375), σ' (.n 4376)] =
        [s0, s1, c * gen ^ 82, z, α, mv]) := by
  refine completes_upds [(4363, word 11666641484232641359 0 0),
    (4364, S * word 11666641484232641359 0 0), (4365, mv + pinT), (4366, a2 * cpe),
    (4367, a2 * cpe * (S * word 11666641484232641359 0 0)),
    (4368, mv + pinT + a2 * cpe * (S * word 11666641484232641359 0 0)), (4369, s0), (4370, s1),
    (4371, word 7077888 0 0), (4372, c * word 7077888 0 0), (4373, c * word 7077888 0 0), (4374, z),
    (4375, α), (4376, mv)] (by simp) (fun next kret hn => ?_) ?_
  · simp only [flPEnd, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    vs_ev
    rw [h4362, h2719, h4124, h2734, h4171, h3132, h4091, h4092, h2240, h1014, h2733]
    simp only [true_and]
    exact ⟨e_add_eq_zero_iff.mpr rfl, hn⟩
  · vs_ev
    rw [word_g82]

theorem _root_.LeanVM.Guest.B1.Sig.Ext.get {lo hi k : ℕ} {σ σ' : Val} (he : Ext lo hi σ σ') (hk : k < lo) {v : E}
    (h : σ (.n k) = v) : σ' (.n k) = v := by rw [he.apply (Or.inl hk)]; exact h

theorem _root_.LeanVM.Guest.B1.Sig.Ext.get64 {lo hi b : ℕ} {σ σ' : Val} (he : Ext lo hi σ σ') (hb : b + 64 ≤ lo) {f : ℕ → E}
    (h : ∀ j < 64, σ (.n (b + j)) = f j) : ∀ j < 64, σ' (.n (b + j)) = f j := fun j hj =>
  he.get (by omega) (h j hj)

theorem flCvS_eq (τ : ℕ) (cv : Digest) : flCvS τ cv = sqCv^[τ + 1] cv := by rw [flCvS, sqAll_eq]

theorem fixes_sub {σ : Val} {G L : List (ℕ × E)} (h : Fixes σ G) (hs : ∀ p ∈ L, p ∈ G) :
    Fixes σ L := fun p hp => h p (hs p hp)

theorem fixes_two {σ : Val} {a b : ℕ} {x y : E} (ha : σ (.n a) = x) (hb : σ (.n b) = y) :
    Fixes σ [(a, x), (b, y)] := by
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact ha
  · exact hb


/-- **The terminal check in the guest's form**: the matrices' value, the pin term, the points'
equality times the slices' Lagrange sum. -/
theorem flTerm_guest (hlen : xs.length = flLen τ) {mv : E} (hterm : flTerm τ cv xs mv) :
    (flLc τ cv xs).1 = mv + flAlpha τ cv xs * flAlpha τ cv xs * flAlpha τ cv xs *
        pinW (lcCh (flG' τ xs) (flSt0' τ cv xs)) * xs.getD (82 + 2 * (τ + 8)) 0 +
      flAlpha τ cv xs * flAlpha τ cv xs *
        (∏ t ∈ Finset.range 8, (1 + scCh (flE τ cv) (flG xs) (flSt0 τ cv xs) t +
          lcCh (flG' τ xs) (flSt0' τ cv xs) (7 - t))) *
        ((∑ j ∈ Finset.range 64, numLo (flZ τ cv xs) j * xs.getD (82 + 2 * (τ + 8) + j) 0) *
          word 11666641484232641359 0 0) := by
  have hsl : (flS τ xs).length = 64 := by simp [flS]; unfold flLen at hlen; omega
  have hrl : (flRc τ cv xs).length = 8 := by simp [flRc]
  have hcl : (flChi τ cv xs).length = τ + 8 := by simp [flChi]
  rw [← (show _ = (flLc τ cv xs).1 from hterm), ← cslice_eq _ _ hsl, colWeight_pin _ _ hrl hsl,
    Main.eqEval_prod _ _ 8 (by simp [hcl]) (by simp [hrl])]
  have hS : ∑ i ∈ Finset.range 64, (∏ j ∈ (Finset.range 64).erase i, (flZ τ cv xs + phi j)) *
      (flS τ xs).getD i 0 =
      ∑ j ∈ Finset.range 64, numLo (flZ τ cv xs) j * xs.getD (82 + 2 * (τ + 8) + j) 0 :=
    Finset.sum_congr rfl fun i hi => by
      rw [flS_getD τ xs (Finset.mem_range.mp hi), numLo]
      simp only [Nat.zero_add]
  have hE : ∏ k ∈ Finset.range 8, (1 + ((flChi τ cv xs).take 8).getD k 0 +
      (flRc τ cv xs).reverse.getD k 0) = ∏ t ∈ Finset.range 8,
        (1 + scCh (flE τ cv) (flG xs) (flSt0 τ cv xs) t + lcCh (flG' τ xs) (flSt0' τ cv xs) (7 - t)) :=
    Finset.prod_congr rfl fun t ht => by
      have ht' := Finset.mem_range.mp ht
      rw [getD_take' _ ht', flChi, getD_map_range _ _ (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_reverse (by omega), hrl, ← List.getD_eq_getElem?_getD, flRc,
        getD_map_range _ _ (by omega), show 8 - 1 - t = 7 - t by omega]
  rw [hS, hE, flS_getD τ xs (by omega)]
  simp only [flRc, getD_map_range _ _ (show 0 < 8 by omega), getD_map_range _ _ (show 1 < 8 by omega),
    getD_map_range _ _ (show 2 < 8 by omega), getD_map_range _ _ (show 3 < 8 by omega),
    getD_map_range _ _ (show 4 < 8 by omega), getD_map_range _ _ (show 5 < 8 by omega),
    getD_map_range _ _ (show 6 < 8 by omega), getD_map_range _ _ (show 7 < 8 by omega), pinW,
    Nat.add_zero]
  ring

set_option maxHeartbeats 4000000 in
/-- **`verify_flock`'s body completes** from its arguments over the honest memory, the
matrices' value `mv` passing the terminal check: its returns are the run's. -/
theorem flock_body_complete (hτ : τ < 29) (hM : FlMem rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220)
    (hlen : xs.length = flLen τ) {mv : E} (hterm : flTerm τ cv xs mv) (σ0 : Val)
    (hσ0 : Fixes σ0 (flArgs τ cv cur zchis lrs zpart)) :
    Completes (coreProgram.Rel rd) rd 7 4377 flSegs.flatten σ0 (fun σ' =>
      [σ' (.n 4369), σ' (.n 4370), σ' (.n 4373), σ' (.n 4374), σ' (.n 4375), σ' (.n 4376)] =
        [(digestScalars (obsAll (flLc τ cv xs).2 (flS τ xs))).1,
          (digestScalars (obsAll (flLc τ cv xs).2 (flS τ xs))).2,
          cur * gen ^ (64 + 2 * (τ + 8)) * gen ^ 82, flZ τ cv xs, flAlpha τ cv xs, mv] ∧
      Fixes σ' (flP0Out τ cv p11 p24 p40) ∧ Fixes σ' (flP7Out τ cv xs cur p2220
        (gen ^ τ * word 16384 0 0 * word 2017612633061982209 0 0))) := by
  simp only [flSegs, List.flatten_cons, List.flatten_nil, List.append_nil]
  have a0 : ∀ k < 7, ∀ v, (k, v) ∈ flArgs τ cv cur zchis lrs zpart → σ0 (.n k) = v :=
    fun k _ v hv => hσ0 _ hv
  -- the prelude
  refine Completes.append (m := 41) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_p0 hτ hM σ0 hσ0) fun σ1 e1 p1 => ?_
  have E1 := e1
  have g2 : σ1 (.n 2) = cur := E1.get (by omega) (a0 2 (by omega) _ (by simp [flArgs]))
  -- round 1
  refine Completes.append (m := 1001) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_rd1 hM hlen σ1 (fixes_two g2 (p1.get (by simp [flP0Out])))
      (Prod.ext (p1.get (by simp [flP0Out])) (p1.get (by simp [flP0Out])))) fun σ2 e2 ⟨q2, p2⟩ => ?_
  have E2 := E1.trans e2 (by omega) (by omega)
  -- the skip challenge
  refine Completes.append (m := 1015) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_sq1 σ2 p2) fun σ3 e3 ⟨p3a, p3b⟩ => ?_
  have E3 := E2.trans e3 (by omega) (by omega)
  have hZ : σ3 (.n 1014) = flZ τ cv xs := by rw [p3b, flZ, flCvS_eq]
  -- the upper numerators
  refine Completes.append (m := 1465) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_lag (n := 450) (by omega) (by omega) (by rw [lag64V_length, lgLen_hi.1, lgLen_hi.2]) σ3 hZ)
    fun σ4 e4 p4 => ?_
  rw [lgOut_hi] at p4
  have E4 := E3.trans e4 (by omega) (by omega)
  -- the interpolation
  refine Completes.append (m := 1845) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_ip hM σ4 ⟨fixes_two (e4.get (by omega) (e3.get (by omega) (q2.get (by simp))))
      (e4.get (by omega) hZ), p4, fun h => absurd h (by omega)⟩) fun σ5 e5 p5 => ?_
  have E5 := E4.trans e5 (by omega) (by omega)
  obtain ⟨-, -, p5'⟩ := p5
  obtain ⟨hP, hS⟩ := p5' (by omega)
  simp only [Nat.reduceEqDiff, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd] at hP hS
  -- the first claim
  refine Completes.append (m := 1852) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_p5 hlen σ5 (E5.get (by omega) (a0 3 (by omega) _ (by simp [flArgs]))) hP hS)
    fun σ6 e6 ⟨p6, p6b⟩ => ?_
  have E6 := E5.trans e6 (by omega) (by omega)
  have g11 : σ6 (.n 11) = p11 := e6.get (by omega) (e5.get (by omega) (e4.get (by omega)
    (e3.get (by omega) (e2.get (by omega) (p1.get (by simp [flP0Out]))))))
  have fF6 : Fixes σ6 [(2, cur), (3, gen ^ τ), (4, zchis), (11, p11)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact E6.get (by omega) (a0 2 (by omega) _ (by simp [flArgs]))
    · exact E6.get (by omega) (a0 3 (by omega) _ (by simp [flArgs]))
    · exact E6.get (by omega) (a0 4 (by omega) _ (by simp [flArgs]))
    · exact g11
  -- the fixed rounds
  refine Completes.append (m := 2216) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (Completes.flatten (st := frB) (Inv := FrInv τ cv xs cur zchis p11) 7
      (fun i _ => by simp only [frB]; omega)
      (fun i hi => numBelow_of_B (by revert i hi; decide +kernel))
      (fun i hi σ hI => c_fr hM hτ hi σ hI) σ6
      ⟨fixes_sub fF6 (by simp), p6, by
        show (σ6 (.n 1006), σ6 (.n 1007)) = _
        rw [e6.get (by omega) (e5.get (by omega) (e4.get (by omega) (congrArg Prod.fst p3a))),
          e6.get (by omega) (e5.get (by omega) (e4.get (by omega) (congrArg Prod.snd p3a)))]
        simp only [flScAt, scSt, flSt0, flCvS_eq]⟩) fun σ7 e7 p7 => ?_
  have E7 := E6.trans e7 (by omega) (by omega)
  -- the sampled rounds
  refine Completes.append (m := 2241) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_p7 hτ hM σ7 (fF6.of_ext e7 (by simp)) p7) fun σ8 e8 p8 => ?_
  have E8 := E7.trans e8 (by omega) (by omega)
  -- the final evaluations
  refine Completes.append (m := 2273) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_s8 hM σ8 p8) fun σ9 e9 ⟨q9a, q9b, q9c, q9d⟩ => ?_
  have E9 := E8.trans e9 (by omega) (by omega)
  have hZ9 : σ9 (.n 1014) = flZ τ cv xs :=
    e9.get (by omega) (e8.get (by omega) (e7.get (by omega) (e6.get (by omega) (e5.get (by omega)
      (e4.get (by omega) hZ)))))
  -- the lower numerators
  refine Completes.append (m := 2719) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_lag (n := 446) (b := 0) (by omega) (by omega) (by rw [lag64V_length, lgLen_lo.1, lgLen_lo.2])
      σ9 hZ9) fun σ10 e10 p10 => ?_
  rw [lgOut_lo] at p10
  have E10 := E9.trans e10 (by omega) (by omega)
  -- alpha
  refine Completes.append (m := 2741) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_s10 mv σ10 (e10.get (by omega) q9a) (e10.get (by omega) q9b)
      (Prod.ext (e10.get (by omega) (congrArg Prod.fst q9c)) (e10.get (by omega) (congrArg Prod.snd q9c)))
      (e10.get (by omega) q9d)) fun σ11 e11 p11' => ?_
  have E11 := E10.trans e11 (by omega) (by omega)
  have g2240 : σ11 (.n 2240) = cur * gen ^ (64 + 2 * (τ + 8)) :=
    e11.get (by omega) (e10.get (by omega) (e9.get (by omega) (p8.get (by simp [flP7Out]))))
  -- the lincheck
  refine Completes.append (m := 3133) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (Completes.flatten (st := lcB) (Inv := LcInv τ cv xs cur lrs) 8
      (fun i _ => by simp only [lcB]; omega)
      (fun i hi => numBelow_of_B (by revert i hi; decide +kernel))
      (fun i hi σ hI => c_lc hM hi σ hI) σ11
      ⟨fixes_two (E11.get (by omega) (a0 5 (by omega) _ (by simp [flArgs]))) g2240,
        p11'.get (k := 2740) (e := (flSt0' τ cv xs).1) (by simp [flS10Out]),
        Prod.ext (p11'.get (k := 2725) (e := (digestScalars (flSt0' τ cv xs).2).1) (by simp [flS10Out]))
          (p11'.get (k := 2726) (e := (digestScalars (flSt0' τ cv xs).2).2) (by simp [flS10Out]))⟩)
    fun σ12 e12 ⟨p12a, p12b, p12c⟩ => ?_
  have E12 := E11.trans e12 (by omega) (by omega)
  -- the slices
  refine Completes.append (m := 4093) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_zp hM hlen σ12 (fixes_two (E12.get (by omega) (a0 6 (by omega) _ (by simp [flArgs])))
      (e12.get (by omega) g2240)) p12c) fun σ13 e13 ⟨_, p13⟩ => ?_
  have E13 := E12.trans e13 (by omega) (by omega)
  have g2735 : σ13 (.n 2735) = flAlpha τ cv xs * flAlpha τ cv xs * flAlpha τ cv xs :=
    e13.get (by omega) (e12.get (by omega) (p11'.get (by simp [flS10Out])))
  -- the pin term
  refine Completes.append (m := 4125) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_p13 (rc := lcCh (flG' τ xs) (flSt0' τ cv xs)) hM.rcs (by simpa using hM.sl 0 (by omega)) σ13
      (E13.get (by omega) (a0 5 (by omega) _ (by simp [flArgs])))
      (E13.get (by omega) (a0 6 (by omega) _ (by simp [flArgs]))) g2735) fun σ14 e14 p14 => ?_
  have E14 := E13.trans e14 (by omega) (by omega)
  -- the points' equality
  refine Completes.append (m := 4172) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_cpe (chi := scCh (flE τ cv) (flG xs) (flSt0 τ cv xs)) (fun t ht => hM.chis t (by omega))
      hM.rcs σ14 ⟨fixes_two (E14.get (by omega) (a0 4 (by omega) _ (by simp [flArgs])))
        (E14.get (by omega) (a0 5 (by omega) _ (by simp [flArgs]))), fun h => absurd h (by omega)⟩)
    fun σ15 e15 ⟨_, p15⟩ => ?_
  have E15 := E14.trans e15 (by omega) (by omega)
  have p15' := p15 (by omega)
  simp only [Nat.reduceEqDiff, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd] at p15'
  -- the slices' sum
  refine Completes.append (m := 4363) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_cs (z := flZ τ cv xs) (s := fun i => xs.getD (82 + 2 * (τ + 8) + i) 0) hM.sl σ15
      ⟨(fun p hp => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        subst hp
        exact E15.get (by omega) (a0 6 (by omega) _ (by simp [flArgs]))),
        e15.get64 (by omega) (e14.get64 (by omega) (e13.get64 (by omega) (e12.get64 (by omega)
          (e11.get64 (by omega) p10)))), fun h => absurd h (by omega)⟩)
    fun σ16 e16 ⟨_, _, p16⟩ => ?_
  have p16' := p16 (by omega)
  simp only [Nat.reduceEqDiff, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd] at p16'
  -- the final check and the returns
  have p6b' : σ7 (.n 1851) = gen ^ τ * word 16384 0 0 * word 2017612633061982209 0 0 :=
    e7.get (by omega) p6b
  have fx0 : ∀ {σa σb : Val} {lo hi : ℕ}, Fixes σa (flP0Out τ cv p11 p24 p40) → Ext lo hi σa σb →
      41 ≤ lo → Fixes σb (flP0Out τ cv p11 p24 p40) := fun h he hlo =>
    h.of_ext he (by simp [flP0Out]; omega)
  have fx7 : ∀ {σa σb : Val} {lo hi : ℕ} {v : E}, Fixes σa (flP7Out τ cv xs cur p2220 v) →
      Ext lo hi σa σb → 2241 ≤ lo → Fixes σb (flP7Out τ cv xs cur p2220 v) := fun h he hlo =>
    h.of_ext he (by simp [flP7Out]; omega)
  have t13 : ∀ {k : ℕ} {v : E}, k < 4093 → σ13 (.n k) = v → σ16 (.n k) = v := fun hk h =>
    e16.get (by omega) (e15.get (by omega) (e14.get (by omega) h))
  have t11 : ∀ {k : ℕ} {v : E}, k < 2741 → σ11 (.n k) = v → σ16 (.n k) = v := fun hk h =>
    t13 (by omega) (e13.get (by omega) (e12.get (by omega) h))
  refine (c_end (mv := mv) (z := flZ τ cv xs) (α := flAlpha τ cv xs) σ16
    (t13 (by omega) (e13.get (by omega) (p12b.trans (flTerm_guest hlen hterm))))
    p16' (t11 (by omega) (p11'.get (k := 2719) (e := mv) (by simp [flS10Out])))
    (e16.get (by omega) (e15.get (by omega) p14))
    (t11 (by omega) (p11'.get (k := 2734) (e := flAlpha τ cv xs * flAlpha τ cv xs) (by simp [flS10Out])))
    (e16.get (by omega) p15')
    (t13 (by omega) (congrArg Prod.fst p13)) (t13 (by omega) (congrArg Prod.snd p13))
    (t11 (by omega) g2240)
    (t11 (by omega) (e11.get (by omega) (e10.get (by omega) hZ9)))
    (t11 (by omega) (p11'.get (k := 2733) (e := flAlpha τ cv xs) (by simp [flS10Out])))).withExt.mono
    le_rfl le_rfl fun σ' ⟨h, he⟩ => ⟨by rw [h], (fx0 (fx0 (fx0 (fx0 (fx0 (fx0 (fx0 (fx0 (fx0 (fx0 (fx0 (fx0 (fx0 (fx0 (fx0 (fx0 p1 e2 (by omega)) e3 (by omega)) e4 (by omega)) e5 (by omega)) e6 (by omega)) e7 (by omega)) e8 (by omega)) e9 (by omega)) e10 (by omega)) e11 (by omega)) e12 (by omega)) e13 (by omega)) e14 (by omega)) e15 (by omega)) e16 (by omega)) he (by omega)),
    (fx7 (fx7 (fx7 (fx7 (fx7 (fx7 (fx7 (fx7 (fx7 (by rw [← p6b']; exact p8) e9 (by omega)) e10 (by omega)) e11 (by omega)) e12 (by omega)) e13 (by omega)) e14 (by omega)) e15 (by omega)) e16 (by omega)) he (by omega))⟩

/-- **`verify_flock` holds** over the honest memory of the run on `cv` and `xs`, the matrices'
value `mv` passing the terminal check: it returns the run's final state, the cursor past the
words, the skip challenge, `alpha` and `mv`. -/
theorem verify_flock_rel (hτ : τ < 29) (hM : FlMem rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220)
    (hlen : xs.length = flLen τ) {mv : E} (hterm : flTerm τ cv xs mv) :
    coreProgram.Rel rd "verify_flock"
      [(digestScalars cv).1, (digestScalars cv).2, cur, gen ^ τ, zchis, lrs, zpart]
      [(digestScalars (obsAll (flLc τ cv xs).2 (flS τ xs))).1,
        (digestScalars (obsAll (flLc τ cv xs).2 (flS τ xs))).2, cur * gen ^ flLen τ, flZ τ cv xs,
        flAlpha τ cv xs, mv] := by
  rw [rel_iff_sem find_verify_flock, core12_body, core12_params]
  set args := [(digestScalars cv).1, (digestScalars cv).2, cur, gen ^ τ, zchis, lrs, zpart]
  obtain ⟨σ', he, hp, hh⟩ := flock_body_complete hτ hM hlen hterm (Val.ofArgs args) (by
    intro p hp
    simp only [flArgs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine ⟨σ', ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]
    rw [he.apply (Or.inl (by omega)), he.apply (Or.inl (by omega)), he.apply (Or.inl (by omega)),
      he.apply (Or.inl (by omega)), he.apply (Or.inl (by omega)), he.apply (Or.inl (by omega)),
      he.apply (Or.inl (by omega))]
    rfl
  · rw [holdsList_append]
    refine hh _ _ ?_
    simp only [flRet, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil]
    rw [hp.1, mul_assoc, ← pow_add, show 64 + 2 * (τ + 8) + 82 = flLen τ by unfold flLen; omega]

/-- The buffers `verify_flock` allocates hold the honest words of the run on `cv` and `xs`. -/
structure FlBufs (rd : Reader) (τ : ℕ) (cv : Digest) (xs : List E) (cur p11 p24 p40 p2220 : E) :
    Prop where
  zr : ∀ j < τ + 8, LoadHolds rd p11 (6 + j) (flE τ cv j)
  pts : ∀ t ≤ τ + 1, LoadHolds rd p24 (26 + 2 * t) (digestScalars (sqCv^[t] cv)).1 ∧
    LoadHolds rd p24 (27 + 2 * t) (digestScalars (sqCv^[t] cv)).2
  p1 : ∀ i < 64, LoadHolds rd p40 i (xs.getD i 0)
  rnd : ∀ j, 7 ≤ j → j ≤ τ + 8 →
    LoadHolds rd p2220 (4 * j) (digestScalars (flScAt τ cv xs j).2).1 ∧
    LoadHolds rd p2220 (4 * j + 1) (digestScalars (flScAt τ cv xs j).2).2 ∧
    LoadHolds rd p2220 (4 * j + 2) (cur * gen ^ (64 + 2 * j)) ∧
    LoadHolds rd p2220 (4 * j + 3) (flScAt τ cv xs j).1

/-- **`verify_flock`'s honest memory** at its `HeapBuf` pointers `[zerocheck_r, flock_pts,
flock_pts_r1, flock_rounds]`: for the state `cv` its first arguments name and the words `xs` at
its cursor, the buffers hold the run's words. -/
def FlockMem (rd : Reader) : List E → List E → List E → Prop
  | [p11, p24, p40, p2220], [fs0, fs1, cur, gt, _, _, _], _ =>
      ∃ (τ : ℕ) (cv : Digest) (xs : List E), τ < 29 ∧ gt = gen ^ τ ∧ (fs0, fs1) = digestScalars cv ∧
        ReadsAt rd cur xs ∧ xs.length = flLen τ ∧ FlBufs rd τ cv xs cur p11 p24 p40 p2220
  | _, _, _ => False

theorem readsAt_unique {p : E} {l l' : List E} (h : ReadsAt rd p l) (h' : ReadsAt rd p l')
    (hl : l.length = l'.length) : l = l' :=
  List.ext_getElem hl fun k h1 h2 => loadHolds_unique (h k h1) (h' k h2)

/-- **`verify_flock` is complete** (TRIAGE #40): `CompleteFlock` over `FlockMem`. -/
theorem verify_flock_complete (rd : Reader) : CompleteFlock rd FlockMem := by
  intro ptrs τ fs0 fs1 cur zchis lrs zpart rets hτ hout hmem
  obtain ⟨cv, xs, cv', zSkip, alpha, mv, chi, rcs, s, hcv, hxs, hcl, hrl, hsl, hchi, hrc, hs, hrun,
    hret⟩ := hout
  obtain ⟨hlen, hz, ha, hchiE, hrcE, hsE, hterm, hcv'⟩ :=
    flock_inv (hrun _ (flockEv_at alpha zSkip (chi.take 8) rcs.reverse s mv))
  match ptrs, hmem with
  | [p11, p24, p40, p2220], ⟨τ', cv0, xs0, hτ', hgt, hcv0, hxs0, hlen0, hB⟩ => ?_
  obtain rfl : τ' = τ := (gen_pow_inj' (by omega) (by omega) hgt).symm
  obtain rfl : cv0 = cv := digestScalars_injective (hcv0.symm.trans hcv)
  obtain rfl : xs0 = xs := readsAt_unique hxs0 hxs (by rw [hlen0, hlen])
  have hM : FlMem rd τ' cv0 xs0 cur zchis lrs zpart p11 p24 p40 p2220 :=
    { words := fun k hk => readsAt_iff_getD.mp hxs k (by omega)
      zr := hB.zr
      pts := hB.pts
      p1 := hB.p1
      rnd := hB.rnd
      chis := fun j hj => by
        have := readsAt_iff_getD.mp hchi j (by omega)
        rwa [hchiE, flChi, getD_map_range _ _ hj] at this
      rcs := fun j hj => by
        have := readsAt_iff_getD.mp hrc j (by omega)
        rwa [hrcE, flRc, getD_map_range _ _ hj] at this
      sl := fun i hi => by
        have := readsAt_iff_getD.mp hs i (by omega)
        rwa [hsE, flS_getD τ' xs0 hi] at this }
  rw [hret, hcv', hz, ha, hlen, show fs0 = (digestScalars cv0).1 from congrArg Prod.fst hcv,
    show fs1 = (digestScalars cv0).2 from congrArg Prod.snd hcv]
  exact verify_flock_rel hτ hM hlen hterm

end

end
end LeanVM.Guest.B1

