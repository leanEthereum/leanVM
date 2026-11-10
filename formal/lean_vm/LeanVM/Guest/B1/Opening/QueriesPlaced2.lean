/-
  LeanVM.Guest.B1.Opening.QueriesPlaced2

  The pointers an honest query loads through, and an iteration's honest valuation.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesComplete4
public import LeanVM.Guest.B1.Opening.QueriesPlaced1

/-!
# Pointers of an honest query; an iteration's valuation

`WD.ptr_flag`, `WD.ptr_cap`: at the honest values a walk loads its flag through `flags·g^Q` and
its cap leaf through `cap·g^(4Q + 2b_pd)` (`Q = q / 2^(pd+1)`).

`oqQD`: the honest query from `b` of a witness `(q, row, sibs)`; `oqResV`: its result, its fold or
(final level) `0`. `oqGuardA_okC`: a loop's guard at its honest values (`oqGuardV`).

`oqIter1F`, `oqIter0F`: an iteration's honest values, from its queries, their window pointers and
the chain's word. `oqIter1_at`, `oqIter0_at`: its body holds statement by statement (`BlockOkC`,
any call), its tail's guard and arguments, its loads' pointers, its walks' leaf cells.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace WD

variable (w : WD) {σ : Val}

/-- The flag a walk loads through: `flags·g^Q`. -/
theorem ptr_flag (hv : w.Hv σ) :
    σ (.n (w.Cq + 2)) = w.flagsv * gen ^ (w.q / 2 ^ (w.s.pd + 1)) := by
  rw [hv, val_cap]
  rfl

/-- The cap leaf a walk loads through: `cap·g^(4Q + 2b_pd)`. -/
theorem ptr_cap (hv : w.Hv σ) :
    σ (.n (w.Cq + 8)) = w.capv * gen ^ (4 * (w.q / 2 ^ (w.s.pd + 1)) +
      (if w.q.testBit w.s.pd then 2 else 0)) := by
  rw [hv, val_cap]
  simp only [capV, qV, wbV, List.getD_cons_succ, List.getD_cons_zero]
  split <;> ring

end WD

/-- The call relation asking nothing of a call. -/
def anyCall : CallRel := fun _ _ _ ↦ True

/-- **The honest query from `b`** of the witness `w = (q, row, sibs)`. -/
def oqQD (s : Oq) (b : ℕ) (emit : Bool) (pr : ℕ) (cap flags : E) (rounds : List FoldRound)
    (hsv : List E) (w : QW) : QD :=
  ⟨s, b, emit, pr, w.2.1, w.1, w.2.2, cap, flags, rounds, hsv⟩

/-- A query's result: its fold, or `0` at the final level. -/
def oqResV (s : Oq) (rounds : List FoldRound) (w : QW) : E :=
  if s.final = 1 then 0 else qwFold s.base rounds w

/-- A loop's guard values: `2`, `x·2`, `x·2 + N`, `2`, `x·2`. -/
def oqGuardV (x N : E) : List E := [word 2 0, x * word 2 0, x * word 2 0 + N, word 2 0, x * word 2 0]

variable {rd : Reader}

/-- **A loop's guard at its honest values.** -/
theorem oqGuardA_okC {C : CallRel} {σ : Val} {g : ℕ} {x N : E} (h0 : σ (.n 0) = x)
    (h1 : σ (.n 1) = N) (hg : ∀ o < 5, σ (.n (g + o)) = (oqGuardV x N).getD o 0) :
    BlockOkC C rd σ (oqGuardA g) ∧ σ (.n (g + 2)) = x * gen + N ∧ σ (.n (g + 4)) = x * gen := by
  have g0 : σ (.n g) = word 2 0 := hg 0 (by omega)
  have g1 : σ (.n (g + 1)) = x * word 2 0 := hg 1 (by omega)
  have g2 : σ (.n (g + 2)) = x * word 2 0 + N := hg 2 (by omega)
  have g3 : σ (.n (g + 3)) = word 2 0 := hg 3 (by omega)
  have g4 : σ (.n (g + 4)) = x * word 2 0 := hg 4 (by omega)
  refine ⟨fun a ha ↦ ?_, by rw [g2, word_gen], by rw [g4, word_gen]⟩
  simp only [oqGuardA, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact g0
  · show σ (.n (g + 1)) = σ (.n 0) * σ (.n g)
    rw [g1, h0, g0]
  · show σ (.n (g + 2)) = σ (.n (g + 1)) + σ (.n 1)
    rw [g2, g1, h1]
  · exact g3
  · show σ (.n (g + 4)) = σ (.n 0) * σ (.n (g + 3))
    rw [g4, h0, g3]

/-! ## A level-0 iteration -/

/-- The chain step's values of a level-0 iteration. -/
def oqStep1V (x ch mu v d1 d2 : E) : List E :=
  [ch * x, v, v + d1, (v + d1) * mu, (v + d1) * mu + d2, ((v + d1) * mu + d2) * mu, ch * x]

/-- The tail's values of a level-0 iteration: the chain step (non-final levels), the guard. -/
def oqIter1C (fin : ℕ) (x N ch mu v d1 d2 : E) : List E :=
  (if fin = 1 then [] else oqStep1V x ch mu v d1 d2) ++ oqGuardV x N

theorem oqG1_eq (s : Oq) : oqG1 s = oqC1 s + (if s.final = 1 then 0 else 7) := by
  unfold oqG1; split <;> rfl

theorem oqIter1C_guard (fin : ℕ) (x N ch mu v d1 d2 : E) (o : ℕ) :
    (oqIter1C fin x N ch mu v d1 d2).getD ((if fin = 1 then 0 else 7) + o) 0 =
      (oqGuardV x N).getD o 0 := by
  unfold oqIter1C
  split
  · rw [List.nil_append, Nat.zero_add]
  · rw [List.getD_append_right _ _ _ _ (by simp [oqStep1V])]
    simp [oqStep1V]

theorem oqIter1C_step {fin : ℕ} (hf : fin ≠ 1) (x N ch mu v d1 d2 : E) {o : ℕ} (ho : o < 7) :
    (oqIter1C fin x N ch mu v d1 d2).getD o 0 = (oqStep1V x ch mu v d1 d2).getD o 0 := by
  unfold oqIter1C
  simp only [hf, ↓reduceIte]
  exact List.getD_append _ _ _ _ (by simp [oqStep1V, ho])

/-- **A level-0 iteration's honest values**, from its arguments, its queries, their window pointers
and the chain's word `v`. -/
def oqIter1F (s : Oq) (args : List E) (D1 D2 : QD) (bp1 bp2 v : E) (i : ℕ) : E :=
  let x := args.getD 0 0
  if i < 10 then args.getD i 0
  else if i = 10 then args.getD 2 0 * x
  else if i = 11 then args.getD 2 0 * x * x
  else if i = 12 then args.getD 3 0 * x
  else if i = 13 then args.getD 3 0 * x * x
  else if i = 14 then D1.x
  else if i = 15 then bp1
  else if i < oqE1 s then D1.val i
  else if i = oqE1 s then D2.x
  else if i = oqE1 s + 1 then bp2
  else if i < oqC1 s then D2.val i
  else (oqIter1C s.final x (args.getD 1 0) (args.getD 8 0) (args.getD 9 0) v
    (oqResV s D1.rounds (D1.q, D1.row, D1.sibs)) (oqResV s D2.rounds (D2.q, D2.row, D2.sibs))).getD
      (i - oqC1 s) 0

/-- **A level-0 iteration at its honest values**: at a valuation holding `oqIter1F` (its queries
`D1` at `16`, emitting the padding run, and `D2` after it), its body holds statement by statement,
its parameters are its arguments, and its tail's guard and arguments, its loads' pointers, its
queries' leaf cells (the walks' first arguments). -/
theorem oqIter1_at {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) {odd j : ℕ} {walk : String}
    {N positions qptrs cap flags coefs hsp ch mu : E} {rounds : List FoldRound} {hsv : List E}
    {w1 w2 : QW} {bp1 bp2 v : E}
    (hok1 : (oqQD s 16 true 0 cap flags rounds hsv w1).Ok rd coefs hsp bp1)
    (hok2 : (oqQD s (oqE1 s + 2) false (oqK1 s 16) cap flags rounds hsv w2).Ok rd coefs hsp bp2)
    (hx1 : LoadHolds rd positions (2 * j + odd) (eOfNat w1.1))
    (hx2 : LoadHolds rd positions (2 * j + odd + 1) (eOfNat w2.1))
    (hb1 : LoadHolds rd qptrs (2 * j + odd) bp1) (hb2 : LoadHolds rd qptrs (2 * j + odd + 1) bp2)
    (hv : s.final ≠ 1 → LoadHolds rd ch j v ∧
      LoadHolds rd ch (j + 1) (((v + oqResV s rounds w1) * mu + oqResV s rounds w2) * mu))
    {σ : Val} (hσ : ∀ i, σ (.n i) = oqIter1F s
      [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu]
      (oqQD s 16 true 0 cap flags rounds hsv w1)
      (oqQD s (oqE1 s + 2) false (oqK1 s 16) cap flags rounds hsv w2) bp1 bp2 v i) :
    oqLoopParams.map σ = [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] ∧
      BlockOkC anyCall rd σ (oqLoop1A s odd walk) ∧
      (oqQD s 16 true 0 cap flags rounds hsv w1).Hv σ ∧
      (oqQD s (oqE1 s + 2) false (oqK1 s 16) cap flags rounds hsv w2).Hv σ ∧
      σ (.n 11) = positions * gen ^ j * gen ^ j ∧ σ (.n 13) = qptrs * gen ^ j * gen ^ j ∧
      σ (.n 15) = bp1 ∧ σ (.n (oqE1 s + 1)) = bp2 ∧
      (s.final ≠ 1 → σ (.n (oqC1 s)) = ch * gen ^ j ∧ σ (.n (oqC1 s + 6)) = ch * gen ^ j) ∧
      σ (.n (oqG1 s + 2)) = gen ^ j * gen + N ∧ σ (.n (oqG1 s + 4)) = gen ^ j * gen ∧
      (σ (.n (oqOut s (oqKL s 16 true) (s.B - 1) 0)), σ (.n (oqOut s (oqKL s 16 true) (s.B - 1) 1))) =
        digestHalves (merkleLeafDigest w1.2.1) ∧
      (σ (.n (oqOut s (oqKL s (oqE1 s + 2) false) (s.B - 1) 0)),
        σ (.n (oqOut s (oqKL s (oqE1 s + 2) false) (s.B - 1) 1))) =
        digestHalves (merkleLeafDigest w2.2.1) := by
  set D1 := oqQD s 16 true 0 cap flags rounds hsv w1 with hD1
  set D2 := oqQD s (oqE1 s + 2) false (oqK1 s 16) cap flags rounds hsv w2 with hD2
  set args : List E := [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] with hargs
  have hb1' : D1.b = 16 := rfl
  have he1' : D1.e = oqE1 s := rfl
  have hb2' : D2.b = oqE1 s + 2 := rfl
  have he2' : D2.e = oqC1 s := rfl
  have i1 := D1.b_le_ch
  have i2 := D1.ch_lt_e
  have i3 := D2.b_le_ch
  have i4 := D2.ch_lt_e
  have eP : ∀ i < 10, σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; simp only [oqIter1F, hi, ↓reduceIte]
  have e10 : σ (.n 10) = positions * gen ^ j := by rw [hσ]; simp [oqIter1F, hargs]
  have e11 : σ (.n 11) = positions * gen ^ j * gen ^ j := by rw [hσ]; simp [oqIter1F, hargs]
  have e12 : σ (.n 12) = qptrs * gen ^ j := by rw [hσ]; simp [oqIter1F, hargs]
  have e13 : σ (.n 13) = qptrs * gen ^ j * gen ^ j := by rw [hσ]; simp [oqIter1F, hargs]
  have e14 : σ (.n 14) = D1.x := by rw [hσ]; simp [oqIter1F]
  have e15 : σ (.n 15) = bp1 := by rw [hσ]; simp [oqIter1F]
  have eQ1 : D1.Hv σ := fun i h1 h2 => by
    rw [hσ]
    simp only [oqIter1F, show ¬ i < 10 by omega, show i ≠ 10 by omega, show i ≠ 11 by omega,
      show i ≠ 12 by omega, show i ≠ 13 by omega, show i ≠ 14 by omega, show i ≠ 15 by omega,
      show i < oqE1 s by omega, ↓reduceIte]
  have eX2 : σ (.n (oqE1 s)) = D2.x := by
    rw [hσ]
    simp only [oqIter1F, show ¬ oqE1 s < 10 by omega, show oqE1 s ≠ 10 by omega,
      show oqE1 s ≠ 11 by omega, show oqE1 s ≠ 12 by omega, show oqE1 s ≠ 13 by omega,
      show oqE1 s ≠ 14 by omega, show oqE1 s ≠ 15 by omega, lt_irrefl, ↓reduceIte]
  have eB2 : σ (.n (oqE1 s + 1)) = bp2 := by
    rw [hσ]
    simp only [oqIter1F, show ¬ oqE1 s + 1 < 10 by omega, show oqE1 s + 1 ≠ 10 by omega,
      show oqE1 s + 1 ≠ 11 by omega, show oqE1 s + 1 ≠ 12 by omega, show oqE1 s + 1 ≠ 13 by omega,
      show oqE1 s + 1 ≠ 14 by omega, show oqE1 s + 1 ≠ 15 by omega,
      show ¬ oqE1 s + 1 < oqE1 s by omega, show oqE1 s + 1 ≠ oqE1 s by omega, ↓reduceIte]
  have eQ2 : D2.Hv σ := fun i h1 h2 => by
    rw [hσ]
    simp only [oqIter1F, show ¬ i < 10 by omega, show i ≠ 10 by omega, show i ≠ 11 by omega,
      show i ≠ 12 by omega, show i ≠ 13 by omega, show i ≠ 14 by omega, show i ≠ 15 by omega,
      show ¬ i < oqE1 s by omega, show i ≠ oqE1 s by omega, show i ≠ oqE1 s + 1 by omega,
      show i < oqC1 s by omega, ↓reduceIte]
  have eC : ∀ o, σ (.n (oqC1 s + o)) = (oqIter1C s.final (gen ^ j) N ch mu v
      (oqResV s rounds w1) (oqResV s rounds w2)).getD o 0 := fun o => by
    rw [hσ]
    simp only [oqIter1F, show ¬ oqC1 s + o < 10 by omega, show oqC1 s + o ≠ 10 by omega,
      show oqC1 s + o ≠ 11 by omega, show oqC1 s + o ≠ 12 by omega, show oqC1 s + o ≠ 13 by omega,
      show oqC1 s + o ≠ 14 by omega, show oqC1 s + o ≠ 15 by omega,
      show ¬ oqC1 s + o < oqE1 s by omega, show oqC1 s + o ≠ oqE1 s by omega,
      show oqC1 s + o ≠ oqE1 s + 1 by omega, show ¬ oqC1 s + o < oqC1 s by omega, ↓reduceIte,
      Nat.add_sub_cancel_left]
    rfl
  have hp1 := D1.pad_of_emit rfl eQ1
  have hpr : D2.prV = D1.prV := rfl
  obtain ⟨hA1, hres1, hl1⟩ := D1.query_complete (σ := σ) (x := .n 14) (bp := .n 15) (cap := .n 4)
    (flags := .n 5) (coefs := .n 6) (hsp := .n 7) (walk := walk) (C := anyCall) hs hfin
    (by rw [eP 6 (by omega), eP 7 (by omega), e15]; exact hok1) eQ1 e14 hp1.1 hp1.2
    (eP 4 (by omega)) (eP 5 (by omega)) trivial
  obtain ⟨hA2, hres2, hl2⟩ := D2.query_complete (σ := σ) (x := .n (oqE1 s)) (bp := .n (oqE1 s + 1))
    (cap := .n 4) (flags := .n 5) (coefs := .n 6) (hsp := .n 7) (walk := walk) (C := anyCall) hs hfin
    (by rw [eP 6 (by omega), eP 7 (by omega), eB2]; exact hok2) eQ2 eX2 (hpr ▸ hp1.1) (hpr ▸ hp1.2)
    (eP 4 (by omega)) (eP 5 (by omega)) trivial
  change σ (.n (oqRes s 16 true)) = oqResV s rounds w1 at hres1
  change σ (.n (oqRes s (oqE1 s + 2) false)) = oqResV s rounds w2 at hres2
  have eG : ∀ o < 5, σ (.n (oqG1 s + o)) = (oqGuardV (gen ^ j) N).getD o 0 := fun o _ ↦ by
    rw [oqG1_eq, Nat.add_assoc, eC, oqIter1C_guard]
  obtain ⟨hG, eG2, eG4⟩ := oqGuardA_okC (rd := rd) (C := anyCall) (eP 0 (by omega))
    (eP 1 (by omega)) eG
  have eS : s.final ≠ 1 → ∀ o < 7, σ (.n (oqC1 s + o)) =
      (oqStep1V (gen ^ j) ch mu v (oqResV s rounds w1) (oqResV s rounds w2)).getD o 0 :=
    fun hf o ho ↦ by rw [eC, oqIter1C_step hf _ _ _ _ _ _ _ ho]
  refine ⟨?_, fun a ha => ?_, eQ1, eQ2, e11, e13, e15, eB2, fun hf ↦ ⟨?_, ?_⟩, eG2, eG4, hl1, hl2⟩
  · simp only [oqLoopParams, List.map_cons, List.map_nil]
    rw [eP 0 (by omega), eP 1 (by omega), eP 2 (by omega), eP 3 (by omega), eP 4 (by omega),
      eP 5 (by omega), eP 6 (by omega), eP 7 (by omega), eP 8 (by omega), eP 9 (by omega)]
    rfl
  rotate_left
  · have := eS hf 0 (by omega); rw [Nat.add_zero] at this; exact this
  · exact eS hf 6 (by omega)
  simp only [oqLoop1A, List.mem_append] at ha
  rcases ha with ((((ha | ha) | ha) | ha) | ha) | ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · show σ (.n 10) = σ (.n 2) * σ (.n 0)
      rw [e10, eP 2 (by omega), eP 0 (by omega)]; rfl
    · show σ (.n 11) = σ (.n 10) * σ (.n 0)
      rw [e11, e10, eP 0 (by omega)]; rfl
    · show σ (.n 12) = σ (.n 3) * σ (.n 0)
      rw [e12, eP 3 (by omega), eP 0 (by omega)]; rfl
    · show σ (.n 13) = σ (.n 12) * σ (.n 0)
      rw [e13, e12, eP 0 (by omega)]; rfl
    · show LoadHolds rd (σ (.n 11)) odd (σ (.n 14))
      rw [e11, e14, mul_assoc, ← pow_add, ← two_mul, loadHolds_mul_gen_pow]
      exact hx1
    · show LoadHolds rd (σ (.n 13)) odd (σ (.n 15))
      rw [e13, e15, mul_assoc, ← pow_add, ← two_mul, loadHolds_mul_gen_pow]
      exact hb1
  · exact hA1 a ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · show LoadHolds rd (σ (.n 11)) (odd + 1) (σ (.n (oqE1 s)))
      rw [e11, eX2, mul_assoc, ← pow_add, ← two_mul, loadHolds_mul_gen_pow, ← Nat.add_assoc]
      exact hx2
    · show LoadHolds rd (σ (.n 13)) (odd + 1) (σ (.n (oqE1 s + 1)))
      rw [e13, eB2, mul_assoc, ← pow_add, ← two_mul, loadHolds_mul_gen_pow, ← Nat.add_assoc]
      exact hb2
  · exact hA2 a ha
  · split at ha
    · simp at ha
    · rename_i hf
      obtain ⟨hv0, hv1⟩ := hv hf
      have c0 := eS hf 0 (by omega)
      have c1 : σ (.n (oqC1 s + 1)) = v := eS hf 1 (by omega)
      have c2 : σ (.n (oqC1 s + 2)) = v + oqResV s rounds w1 := eS hf 2 (by omega)
      have c3 : σ (.n (oqC1 s + 3)) = (v + oqResV s rounds w1) * mu := eS hf 3 (by omega)
      have c4 : σ (.n (oqC1 s + 4)) = (v + oqResV s rounds w1) * mu + oqResV s rounds w2 :=
        eS hf 4 (by omega)
      have c5 : σ (.n (oqC1 s + 5)) =
          ((v + oqResV s rounds w1) * mu + oqResV s rounds w2) * mu := eS hf 5 (by omega)
      have c6 : σ (.n (oqC1 s + 6)) = ch * gen ^ j := eS hf 6 (by omega)
      rw [Nat.add_zero] at c0
      change σ (.n (oqC1 s)) = ch * gen ^ j at c0
      set c := oqC1 s with hc'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show σ (.n c) = σ (.n 8) * σ (.n 0)
        rw [c0, eP 8 (by omega), eP 0 (by omega)]; rfl
      · show LoadHolds rd (σ (.n c)) 0 (σ (.n (c + 1)))
        rw [c0, c1, loadHolds_mul_gen_pow]; exact hv0
      · show σ (.n (c + 2)) = σ (.n (c + 1)) + σ (.n (oqRes s 16 true))
        rw [c2, c1, hres1]
      · show σ (.n (c + 3)) = σ (.n (c + 2)) * σ (.n 9)
        rw [c3, c2, eP 9 (by omega)]; rfl
      · show σ (.n (c + 4)) = σ (.n (c + 3)) + σ (.n (oqRes s (oqE1 s + 2) false))
        rw [c4, c3, hres2]
      · show σ (.n (c + 5)) = σ (.n (c + 4)) * σ (.n 9)
        rw [c5, c4, eP 9 (by omega)]; rfl
      · show σ (.n (c + 6)) = σ (.n 8) * σ (.n 0)
        rw [c6, eP 8 (by omega), eP 0 (by omega)]; rfl
      · show LoadHolds rd (σ (.n (c + 6))) 1 (σ (.n (c + 5)))
        rw [c6, c5, loadHolds_mul_gen_pow]; exact hv1
  · exact hG a ha

/-! ## A deeper iteration -/

/-- The chain step's values of a deeper iteration. -/
def oqStep0V (x ch mu v d : E) : List E := [ch * x, v, v + d, (v + d) * mu, ch * x]

/-- The tail's values of a deeper iteration: the chain step (non-final levels), the guard. -/
def oqIter0C (fin : ℕ) (x N ch mu v d : E) : List E :=
  (if fin = 1 then [] else oqStep0V x ch mu v d) ++ oqGuardV x N

theorem oqG0_eq (s : Oq) : oqG0 s = oqC0 s + (if s.final = 1 then 0 else 5) := by
  unfold oqG0; split <;> rfl

theorem oqIter0C_guard (fin : ℕ) (x N ch mu v d : E) (o : ℕ) :
    (oqIter0C fin x N ch mu v d).getD ((if fin = 1 then 0 else 5) + o) 0 =
      (oqGuardV x N).getD o 0 := by
  unfold oqIter0C
  split
  · rw [List.nil_append, Nat.zero_add]
  · rw [List.getD_append_right _ _ _ _ (by simp [oqStep0V])]
    simp [oqStep0V]

theorem oqIter0C_step {fin : ℕ} (hf : fin ≠ 1) (x N ch mu v d : E) {o : ℕ} (ho : o < 5) :
    (oqIter0C fin x N ch mu v d).getD o 0 = (oqStep0V x ch mu v d).getD o 0 := by
  unfold oqIter0C
  simp only [hf, ↓reduceIte]
  exact List.getD_append _ _ _ _ (by simp [oqStep0V, ho])

/-- **A deeper iteration's honest values**, from its arguments, its query, its window pointer and
the chain's word. -/
def oqIter0F (s : Oq) (args : List E) (D : QD) (bp v : E) (i : ℕ) : E :=
  let x := args.getD 0 0
  if i < 10 then args.getD i 0
  else if i = 10 then args.getD 2 0 * x
  else if i = 11 then D.x
  else if i = 12 then args.getD 3 0 * x
  else if i = 13 then bp
  else if i < oqC0 s then D.val i
  else (oqIter0C s.final x (args.getD 1 0) (args.getD 8 0) (args.getD 9 0) v
    (oqResV s D.rounds (D.q, D.row, D.sibs))).getD (i - oqC0 s) 0

/-- **A deeper iteration at its honest values.** -/
theorem oqIter0_at {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) {j : ℕ} {walk : String}
    {N positions qptrs cap flags coefs hsp ch mu : E} {rounds : List FoldRound} {hsv : List E}
    {w : QW} {bp v : E}
    (hok : (oqQD s 14 true 0 cap flags rounds hsv w).Ok rd coefs hsp bp)
    (hx : LoadHolds rd positions j (eOfNat w.1)) (hb : LoadHolds rd qptrs j bp)
    (hv : s.final ≠ 1 → LoadHolds rd ch j v ∧ LoadHolds rd ch (j + 1) ((v + oqResV s rounds w) * mu))
    {σ : Val} (hσ : ∀ i, σ (.n i) = oqIter0F s
      [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu]
      (oqQD s 14 true 0 cap flags rounds hsv w) bp v i) :
    oqLoopParams.map σ = [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] ∧
      BlockOkC anyCall rd σ (oqLoop0A s walk) ∧ (oqQD s 14 true 0 cap flags rounds hsv w).Hv σ ∧
      σ (.n 10) = positions * gen ^ j ∧ σ (.n 12) = qptrs * gen ^ j ∧ σ (.n 13) = bp ∧
      (s.final ≠ 1 → σ (.n (oqC0 s)) = ch * gen ^ j ∧ σ (.n (oqC0 s + 4)) = ch * gen ^ j) ∧
      σ (.n (oqG0 s + 2)) = gen ^ j * gen + N ∧ σ (.n (oqG0 s + 4)) = gen ^ j * gen ∧
      (σ (.n (oqOut s (oqKL s 14 true) (s.B - 1) 0)), σ (.n (oqOut s (oqKL s 14 true) (s.B - 1) 1))) =
        digestHalves (merkleLeafDigest w.2.1) := by
  set D := oqQD s 14 true 0 cap flags rounds hsv w with hD
  set args : List E := [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] with hargs
  have hb' : D.b = 14 := rfl
  have he' : D.e = oqC0 s := rfl
  have i1 := D.b_le_ch
  have i2 := D.ch_lt_e
  have eP : ∀ i < 10, σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; simp only [oqIter0F, hi, ↓reduceIte]
  have e10 : σ (.n 10) = positions * gen ^ j := by rw [hσ]; simp [oqIter0F, hargs]
  have e11 : σ (.n 11) = D.x := by rw [hσ]; simp [oqIter0F]
  have e12 : σ (.n 12) = qptrs * gen ^ j := by rw [hσ]; simp [oqIter0F, hargs]
  have e13 : σ (.n 13) = bp := by rw [hσ]; simp [oqIter0F]
  have eQ : D.Hv σ := fun i h1 h2 => by
    rw [hσ]
    simp only [oqIter0F, show ¬ i < 10 by omega, show i ≠ 10 by omega, show i ≠ 11 by omega,
      show i ≠ 12 by omega, show i ≠ 13 by omega, show i < oqC0 s by omega, ↓reduceIte]
  have eC : ∀ o, σ (.n (oqC0 s + o)) = (oqIter0C s.final (gen ^ j) N ch mu v
      (oqResV s rounds w)).getD o 0 := fun o => by
    rw [hσ]
    simp only [oqIter0F, show ¬ oqC0 s + o < 10 by omega, show oqC0 s + o ≠ 10 by omega,
      show oqC0 s + o ≠ 11 by omega, show oqC0 s + o ≠ 12 by omega, show oqC0 s + o ≠ 13 by omega,
      show ¬ oqC0 s + o < oqC0 s by omega, ↓reduceIte, Nat.add_sub_cancel_left]
    rfl
  have hp := D.pad_of_emit rfl eQ
  obtain ⟨hA, hres, hl⟩ := D.query_complete (σ := σ) (x := .n 11) (bp := .n 13) (cap := .n 4)
    (flags := .n 5) (coefs := .n 6) (hsp := .n 7) (walk := walk) (C := anyCall) hs hfin
    (by rw [eP 6 (by omega), eP 7 (by omega), e13]; exact hok) eQ e11 hp.1 hp.2
    (eP 4 (by omega)) (eP 5 (by omega)) trivial
  change σ (.n (oqRes s 14 true)) = oqResV s rounds w at hres
  have eG : ∀ o < 5, σ (.n (oqG0 s + o)) = (oqGuardV (gen ^ j) N).getD o 0 := fun o _ ↦ by
    rw [oqG0_eq, Nat.add_assoc, eC, oqIter0C_guard]
  obtain ⟨hG, eG2, eG4⟩ := oqGuardA_okC (rd := rd) (C := anyCall) (eP 0 (by omega))
    (eP 1 (by omega)) eG
  have eS : s.final ≠ 1 → ∀ o < 5, σ (.n (oqC0 s + o)) =
      (oqStep0V (gen ^ j) ch mu v (oqResV s rounds w)).getD o 0 :=
    fun hf o ho ↦ by rw [eC, oqIter0C_step hf _ _ _ _ _ _ ho]
  refine ⟨?_, fun a ha => ?_, eQ, e10, e12, e13, fun hf ↦ ⟨?_, ?_⟩, eG2, eG4, hl⟩
  · simp only [oqLoopParams, List.map_cons, List.map_nil]
    rw [eP 0 (by omega), eP 1 (by omega), eP 2 (by omega), eP 3 (by omega), eP 4 (by omega),
      eP 5 (by omega), eP 6 (by omega), eP 7 (by omega), eP 8 (by omega), eP 9 (by omega)]
    rfl
  rotate_left
  · have := eS hf 0 (by omega); rw [Nat.add_zero] at this; exact this
  · exact eS hf 4 (by omega)
  simp only [oqLoop0A, List.mem_append] at ha
  rcases ha with (((ha | ha) | ha) | ha)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · show σ (.n 10) = σ (.n 2) * σ (.n 0)
      rw [e10, eP 2 (by omega), eP 0 (by omega)]; rfl
    · show LoadHolds rd (σ (.n 10)) 0 (σ (.n 11))
      rw [e10, e11, loadHolds_mul_gen_pow, Nat.add_zero]
      exact hx
    · show σ (.n 12) = σ (.n 3) * σ (.n 0)
      rw [e12, eP 3 (by omega), eP 0 (by omega)]; rfl
    · show LoadHolds rd (σ (.n 12)) 0 (σ (.n 13))
      rw [e12, e13, loadHolds_mul_gen_pow, Nat.add_zero]
      exact hb
  · exact hA a ha
  · split at ha
    · simp at ha
    · rename_i hf
      obtain ⟨hv0, hv1⟩ := hv hf
      have c0 := eS hf 0 (by omega)
      have c1 : σ (.n (oqC0 s + 1)) = v := eS hf 1 (by omega)
      have c2 : σ (.n (oqC0 s + 2)) = v + oqResV s rounds w := eS hf 2 (by omega)
      have c3 : σ (.n (oqC0 s + 3)) = (v + oqResV s rounds w) * mu := eS hf 3 (by omega)
      have c4 : σ (.n (oqC0 s + 4)) = ch * gen ^ j := eS hf 4 (by omega)
      rw [Nat.add_zero] at c0
      change σ (.n (oqC0 s)) = ch * gen ^ j at c0
      set c := oqC0 s with hc'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
      · show σ (.n c) = σ (.n 8) * σ (.n 0)
        rw [c0, eP 8 (by omega), eP 0 (by omega)]; rfl
      · show LoadHolds rd (σ (.n c)) 0 (σ (.n (c + 1)))
        rw [c0, c1, loadHolds_mul_gen_pow]; exact hv0
      · show σ (.n (c + 2)) = σ (.n (c + 1)) + σ (.n (oqRes s 14 true))
        rw [c2, c1, hres]
      · show σ (.n (c + 3)) = σ (.n (c + 2)) * σ (.n 9)
        rw [c3, c2, eP 9 (by omega)]; rfl
      · show σ (.n (c + 4)) = σ (.n 8) * σ (.n 0)
        rw [c4, eP 8 (by omega), eP 0 (by omega)]; rfl
      · show LoadHolds rd (σ (.n (c + 4))) 1 (σ (.n (c + 3)))
        rw [c4, c3, loadHolds_mul_gen_pow]; exact hv1
  · exact hG a ha

end
end LeanVM.Guest.B1
