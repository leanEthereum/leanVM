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

`oqIter1F`, `oqIter0F`: an iteration's honest values, from its queries' `QD`s, their window
pointers and the chain's word. `oqIter1_at`, `oqIter0_at`: its body holds statement by statement
(`BlockOkC`, any call), its tail's guard and arguments, its loads' pointers, its walks' leaf cells.
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

/-! ## A level-0 iteration -/

/-- The chain step's values of a level-0 iteration. -/
def oqIter1C (x N ch mu v d0 d1 : E) : List E :=
  [ch * x, v, v + d0, (v + d0) * mu, (v + d0) * mu + d1, ((v + d0) * mu + d1) * mu,
    ch * x, word 2 0 0, x * word 2 0 0, x * word 2 0 0 + N, word 2 0 0, x * word 2 0 0]

/-- **A level-0 iteration's honest values**, from its arguments, its queries, their window pointers
and the chain's word `v`. -/
def oqIter1F (s : Oq) (args : List E) (D1 D2 : QD) (bp1 bp2 v : E) (i : ℕ) : E :=
  let x := args.getD 0 0
  if i < 8 then args.getD i 0
  else if i = 8 then args.getD 2 0 * x
  else if i = 9 then args.getD 2 0 * x * x
  else if i = 10 then bp1
  else if i < oqE1 s then D1.val i
  else if i = oqE1 s then bp2
  else if i < oqC1 s then D2.val i
  else (oqIter1C x (args.getD 1 0) (args.getD 6 0) (args.getD 7 0) v
    (rowDot s.base s.I D1.row D1.w) (rowDot s.base s.I D2.row D2.w)).getD (i - oqC1 s) 0

variable {rd : Reader}

/-- **A level-0 iteration at its honest values**: at a valuation holding `oqIter1F` (its queries
`D1` at `11`, emitting the padding run, and `D2` after it), its body holds statement by statement,
its parameters are its arguments, and its tail's guard and arguments, its loads' pointers, its
queries' leaf cells (the walks' first arguments). -/
theorem oqIter1_at {s : Oq} (hs : s.RowShape) {odd j : ℕ} {walk : String}
    {N qptrs cap flags wp ch mu : E} {r1 r2 : List K} {w1 w2 : ℕ → E} {q1 q2 : ℕ}
    {sb1 sb2 : List Digest} {bp1 bp2 v : E}
    (hok1 : (⟨s, 11, true, 0, r1, w1, q1, sb1, cap, flags⟩ : QD).Ok rd wp bp1)
    (hok2 : (⟨s, oqE1 s + 1, false, oqK1 11 s.R + s.D, r2, w2, q2, sb2, cap, flags⟩ : QD).Ok rd wp bp2)
    (hb1 : LoadHolds rd qptrs (2 * j + odd) bp1) (hb2 : LoadHolds rd qptrs (2 * j + odd + 1) bp2)
    (hv : LoadHolds rd ch j v)
    (hv1 : LoadHolds rd ch (j + 1) (((v + rowDot s.base s.I r1 w1) * mu +
      rowDot s.base s.I r2 w2) * mu))
    {σ : Val} (hσ : ∀ i, σ (.n i) = oqIter1F s [gen ^ j, N, qptrs, cap, flags, wp, ch, mu]
      ⟨s, 11, true, 0, r1, w1, q1, sb1, cap, flags⟩
      ⟨s, oqE1 s + 1, false, oqK1 11 s.R + s.D, r2, w2, q2, sb2, cap, flags⟩ bp1 bp2 v i) :
    oqLoopParams.map σ = [gen ^ j, N, qptrs, cap, flags, wp, ch, mu] ∧
      BlockOkC anyCall rd σ (oqLoop1A s odd walk) ∧
      (⟨s, 11, true, 0, r1, w1, q1, sb1, cap, flags⟩ : QD).Hv σ ∧
      (⟨s, oqE1 s + 1, false, oqK1 11 s.R + s.D, r2, w2, q2, sb2, cap, flags⟩ : QD).Hv σ ∧
      σ (.n 9) = qptrs * gen ^ j * gen ^ j ∧ σ (.n 10) = bp1 ∧ σ (.n (oqE1 s)) = bp2 ∧
      σ (.n (oqC1 s)) = ch * gen ^ j ∧ σ (.n (oqC1 s + 6)) = ch * gen ^ j ∧
      σ (.n (oqC1 s + 9)) = gen ^ j * gen + N ∧ σ (.n (oqC1 s + 11)) = gen ^ j * gen ∧
      (σ (.n (oqOut s (oqKL s 11 true) (s.B - 1) 0)), σ (.n (oqOut s (oqKL s 11 true) (s.B - 1) 1))) =
        digestHalves (merkleLeafDigest r1) ∧
      (σ (.n (oqOut s (oqKL s (oqE1 s + 1) false) (s.B - 1) 0)),
        σ (.n (oqOut s (oqKL s (oqE1 s + 1) false) (s.B - 1) 1))) =
        digestHalves (merkleLeafDigest r2) := by
  set D1 : QD := ⟨s, 11, true, 0, r1, w1, q1, sb1, cap, flags⟩ with hD1
  set D2 : QD := ⟨s, oqE1 s + 1, false, oqK1 11 s.R + s.D, r2, w2, q2, sb2, cap, flags⟩ with hD2
  have he1 : oqE1 s = D1.e := QD.end_eq D1
  have hc : oqC1 s = D2.e := QD.end_eq D2
  obtain ⟨a1, a2, a3, a4, a5⟩ := D1.places
  obtain ⟨b1, b2, b3, b4, b5⟩ := D2.places
  have hk1 := QD.k1_eq D1
  have hk2 := QD.k1_eq D2
  have hD1b : D1.b = 11 := rfl
  have hD2b : D2.b = oqE1 s + 1 := rfl
  have hE : 11 < oqE1 s := by omega
  have hC : oqE1 s < oqC1 s := by omega
  have eP : ∀ i < 8, σ (.n i) = [gen ^ j, N, qptrs, cap, flags, wp, ch, mu].getD i 0 := fun i hi => by
    rw [hσ]; simp only [oqIter1F, hi, ↓reduceIte]
  have e8 : σ (.n 8) = qptrs * gen ^ j := by rw [hσ]; simp [oqIter1F]
  have e9 : σ (.n 9) = qptrs * gen ^ j * gen ^ j := by rw [hσ]; simp [oqIter1F]
  have e10 : σ (.n 10) = bp1 := by rw [hσ]; simp [oqIter1F]
  have eQ1 : D1.Hv σ := fun i h1 h2 => by
    have : D1.b = 11 := rfl
    rw [hσ]
    simp only [oqIter1F, show ¬ i < 8 by omega, show i ≠ 8 by omega, show i ≠ 9 by omega,
      show i ≠ 10 by omega, show i < oqE1 s by omega, ↓reduceIte]
  have eE1 : σ (.n (oqE1 s)) = bp2 := by
    rw [hσ]
    simp only [oqIter1F, show ¬ oqE1 s < 8 by omega, show oqE1 s ≠ 8 by omega,
      show oqE1 s ≠ 9 by omega, show oqE1 s ≠ 10 by omega, lt_irrefl, ↓reduceIte]
  have eQ2 : D2.Hv σ := fun i h1 h2 => by
    have : D2.b = oqE1 s + 1 := rfl
    rw [hσ]
    simp only [oqIter1F, show ¬ i < 8 by omega, show i ≠ 8 by omega, show i ≠ 9 by omega,
      show i ≠ 10 by omega, show ¬ i < oqE1 s by omega, show i ≠ oqE1 s by omega,
      show i < oqC1 s by omega, ↓reduceIte]
  have eC : ∀ o, σ (.n (oqC1 s + o)) = (oqIter1C (gen ^ j) N ch mu v
      (rowDot s.base s.I r1 w1) (rowDot s.base s.I r2 w2)).getD o 0 := fun o => by
    have : D2.b = oqE1 s + 1 := rfl
    rw [hσ]
    simp only [oqIter1F, show ¬ oqC1 s + o < 8 by omega, show oqC1 s + o ≠ 8 by omega,
      show oqC1 s + o ≠ 9 by omega, show oqC1 s + o ≠ 10 by omega,
      show ¬ oqC1 s + o < oqE1 s by omega, show oqC1 s + o ≠ oqE1 s by omega,
      show ¬ oqC1 s + o < oqC1 s by omega, ↓reduceIte, Nat.add_sub_cancel_left]
    rfl
  have hp1 := D1.pad_of_emit rfl eQ1
  have hw : σ (.n 5) = wp := eP 5 (by omega)
  obtain ⟨hA1, hdot1, hl1⟩ := D1.query_complete (σ := σ) (bp := .n 10) (cap := .n 3) (flags := .n 4)
    (wp := .n 5) (walk := walk) (C := anyCall) hs (by rw [hw, e10]; exact hok1) eQ1 hp1.1 hp1.2
    (eP 3 (by omega)) (eP 4 (by omega)) trivial
  obtain ⟨hA2, hdot2, hl2⟩ := D2.query_complete (σ := σ) (bp := .n (oqE1 s)) (cap := .n 3)
    (flags := .n 4) (wp := .n 5) (walk := walk) (C := anyCall) hs (by rw [hw, eE1]; exact hok2) eQ2
    hp1.1 hp1.2 (eP 3 (by omega)) (eP 4 (by omega)) trivial
  change σ (.n (oqDot s 11)) = rowDot s.base s.I r1 w1 at hdot1
  change σ (.n (oqDot s (oqE1 s + 1))) = rowDot s.base s.I r2 w2 at hdot2
  have c0 := eC 0
  simp only [Nat.add_zero] at c0
  refine ⟨?_, fun a ha => ?_, eQ1, eQ2, e9, e10, eE1, c0,
    by rw [eC 6]; rfl, by rw [eC 9]; simp [oqIter1C, word_gen], by rw [eC 11]; simp [oqIter1C, word_gen],
    hl1, hl2⟩
  · simp only [oqLoopParams, List.map_cons, List.map_nil]
    rw [eP 0 (by omega), eP 1 (by omega), eP 2 (by omega), eP 3 (by omega), eP 4 (by omega),
      eP 5 (by omega), eP 6 (by omega), eP 7 (by omega)]
    rfl
  simp only [oqLoop1A, List.mem_append] at ha
  rcases ha with (((ha | ha) | ha) | ha) | ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · show σ (.n 8) = σ (.n 2) * σ (.n 0)
      rw [e8, eP 2 (by omega), eP 0 (by omega)]; rfl
    · show σ (.n 9) = σ (.n 8) * σ (.n 0)
      rw [e9, e8, eP 0 (by omega)]; rfl
    · show LoadHolds rd (σ (.n 9)) odd (σ (.n 10))
      rw [e9, e10, mul_assoc, ← pow_add, ← two_mul, loadHolds_mul_gen_pow]
      exact hb1
  · exact hA1 a ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    show LoadHolds rd (σ (.n 9)) (odd + 1) (σ (.n (oqE1 s)))
    rw [e9, eE1, mul_assoc, ← pow_add, ← two_mul, loadHolds_mul_gen_pow, ← Nat.add_assoc]
    exact hb2
  · exact hA2 a ha
  · set c := oqC1 s with hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show σ (.n c) = σ (.n 6) * σ (.n 0)
      rw [c0, eP 6 (by omega), eP 0 (by omega)]; rfl
    · show LoadHolds rd (σ (.n c)) 0 (σ (.n (c + 1)))
      rw [c0, eC 1]
      show LoadHolds rd (ch * gen ^ j) 0 v
      rw [loadHolds_mul_gen_pow]; exact hv
    · show σ (.n (c + 2)) = σ (.n (c + 1)) + σ (.n (oqDot s 11))
      rw [eC 2, eC 1, hdot1]; rfl
    · show σ (.n (c + 3)) = σ (.n (c + 2)) * σ (.n 7)
      rw [eC 3, eC 2, eP 7 (by omega)]; rfl
    · show σ (.n (c + 4)) = σ (.n (c + 3)) + σ (.n (oqDot s (oqE1 s + 1)))
      rw [eC 4, eC 3, hdot2]; rfl
    · show σ (.n (c + 5)) = σ (.n (c + 4)) * σ (.n 7)
      rw [eC 5, eC 4, eP 7 (by omega)]; rfl
    · show σ (.n (c + 6)) = σ (.n 6) * σ (.n 0)
      rw [eC 6, eP 6 (by omega), eP 0 (by omega)]; rfl
    · show LoadHolds rd (σ (.n (c + 6))) 1 (σ (.n (c + 5)))
      rw [eC 6, eC 5]
      show LoadHolds rd (ch * gen ^ j) 1 (((v + rowDot s.base s.I r1 w1) * mu +
        rowDot s.base s.I r2 w2) * mu)
      rw [loadHolds_mul_gen_pow]; exact hv1
    · exact eC 7
    · show σ (.n (c + 8)) = σ (.n 0) * σ (.n (c + 7))
      rw [eC 8, eC 7, eP 0 (by omega)]; rfl
    · show σ (.n (c + 9)) = σ (.n (c + 8)) + σ (.n 1)
      rw [eC 9, eC 8, eP 1 (by omega)]; rfl
    · exact eC 10
    · show σ (.n (c + 11)) = σ (.n 0) * σ (.n (c + 10))
      rw [eC 11, eC 10, eP 0 (by omega)]; rfl

/-! ## A deeper iteration -/

/-- The chain step's values of a deeper iteration. -/
def oqIter0C (x N ch mu v d : E) : List E :=
  [ch * x, v, v + d, (v + d) * mu, ch * x, word 2 0 0, x * word 2 0 0, x * word 2 0 0 + N,
    word 2 0 0, x * word 2 0 0]

/-- **A deeper iteration's honest values**, from its arguments, its query, its window pointer and the
chain's word `v`. -/
def oqIter0F (s : Oq) (args : List E) (D : QD) (bp v : E) (i : ℕ) : E :=
  let x := args.getD 0 0
  if i < 8 then args.getD i 0
  else if i = 8 then args.getD 2 0 * x
  else if i = 9 then bp
  else if i < oqC0 s then D.val i
  else (oqIter0C x (args.getD 1 0) (args.getD 6 0) (args.getD 7 0) v
    (rowDot s.base s.I D.row D.w)).getD (i - oqC0 s) 0

/-- **A deeper iteration at its honest values.** -/
theorem oqIter0_at {s : Oq} (hs : s.RowShape) {j : ℕ} {walk : String}
    {N qptrs cap flags wp ch mu : E} {r : List K} {w : ℕ → E} {q : ℕ} {sb : List Digest} {bp v : E}
    (hok : (⟨s, 10, true, 0, r, w, q, sb, cap, flags⟩ : QD).Ok rd wp bp)
    (hb : LoadHolds rd qptrs j bp)
    (hv : LoadHolds rd ch j v)
    (hv1 : LoadHolds rd ch (j + 1) ((v + rowDot s.base s.I r w) * mu))
    {σ : Val} (hσ : ∀ i, σ (.n i) = oqIter0F s [gen ^ j, N, qptrs, cap, flags, wp, ch, mu]
      ⟨s, 10, true, 0, r, w, q, sb, cap, flags⟩ bp v i) :
    oqLoopParams.map σ = [gen ^ j, N, qptrs, cap, flags, wp, ch, mu] ∧
      BlockOkC anyCall rd σ (oqLoop0A s walk) ∧ (⟨s, 10, true, 0, r, w, q, sb, cap, flags⟩ : QD).Hv σ ∧
      σ (.n 8) = qptrs * gen ^ j ∧ σ (.n 9) = bp ∧
      σ (.n (oqC0 s)) = ch * gen ^ j ∧ σ (.n (oqC0 s + 4)) = ch * gen ^ j ∧
      σ (.n (oqC0 s + 7)) = gen ^ j * gen + N ∧ σ (.n (oqC0 s + 9)) = gen ^ j * gen ∧
      (σ (.n (oqOut s (oqKL s 10 true) (s.B - 1) 0)), σ (.n (oqOut s (oqKL s 10 true) (s.B - 1) 1))) =
        digestHalves (merkleLeafDigest r) := by
  set D1 : QD := ⟨s, 10, true, 0, r, w, q, sb, cap, flags⟩ with hD1
  have hc : oqC0 s = D1.e := QD.end_eq D1
  obtain ⟨a1, a2, a3, a4, a5⟩ := D1.places
  have hk1 := QD.k1_eq D1
  have eP : ∀ i < 8, σ (.n i) = [gen ^ j, N, qptrs, cap, flags, wp, ch, mu].getD i 0 := fun i hi => by
    rw [hσ]; simp only [oqIter0F, hi, ↓reduceIte]
  have e8 : σ (.n 8) = qptrs * gen ^ j := by rw [hσ]; simp [oqIter0F]
  have e9 : σ (.n 9) = bp := by rw [hσ]; simp [oqIter0F]
  have eQ1 : D1.Hv σ := fun i h1 h2 => by
    have : D1.b = 10 := rfl
    rw [hσ]
    simp only [oqIter0F, show ¬ i < 8 by omega, show i ≠ 8 by omega, show i ≠ 9 by omega,
      show i < oqC0 s by omega, ↓reduceIte]
  have eC : ∀ o, σ (.n (oqC0 s + o)) = (oqIter0C (gen ^ j) N ch mu v
      (rowDot s.base s.I r w)).getD o 0 := fun o => by
    have : D1.b = 10 := rfl
    rw [hσ]
    simp only [oqIter0F, show ¬ oqC0 s + o < 8 by omega, show oqC0 s + o ≠ 8 by omega,
      show oqC0 s + o ≠ 9 by omega, show ¬ oqC0 s + o < oqC0 s by omega, ↓reduceIte,
      Nat.add_sub_cancel_left]
    rfl
  have hp1 := D1.pad_of_emit rfl eQ1
  have hw : σ (.n 5) = wp := eP 5 (by omega)
  obtain ⟨hA1, hdot1, hl1⟩ := D1.query_complete (σ := σ) (bp := .n 9) (cap := .n 3) (flags := .n 4)
    (wp := .n 5) (walk := walk) (C := anyCall) hs (by rw [hw, e9]; exact hok) eQ1 hp1.1 hp1.2
    (eP 3 (by omega)) (eP 4 (by omega)) trivial
  change σ (.n (oqDot s 10)) = rowDot s.base s.I r w at hdot1
  have c0 := eC 0
  simp only [Nat.add_zero] at c0
  refine ⟨?_, fun a ha => ?_, eQ1, e8, e9, c0,
    by rw [eC 4]; rfl, by rw [eC 7]; simp [oqIter0C, word_gen],
    by rw [eC 9]; simp [oqIter0C, word_gen], hl1⟩
  · simp only [oqLoopParams, List.map_cons, List.map_nil]
    rw [eP 0 (by omega), eP 1 (by omega), eP 2 (by omega), eP 3 (by omega), eP 4 (by omega),
      eP 5 (by omega), eP 6 (by omega), eP 7 (by omega)]
    rfl
  simp only [oqLoop0A, List.mem_append] at ha
  rcases ha with (ha | ha) | ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · show σ (.n 8) = σ (.n 2) * σ (.n 0)
      rw [e8, eP 2 (by omega), eP 0 (by omega)]; rfl
    · show LoadHolds rd (σ (.n 8)) 0 (σ (.n 9))
      rw [e8, e9, loadHolds_mul_gen_pow, Nat.add_zero]
      exact hb
  · exact hA1 a ha
  · set c := oqC0 s with hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show σ (.n c) = σ (.n 6) * σ (.n 0)
      rw [c0, eP 6 (by omega), eP 0 (by omega)]; rfl
    · show LoadHolds rd (σ (.n c)) 0 (σ (.n (c + 1)))
      rw [c0, eC 1]
      show LoadHolds rd (ch * gen ^ j) 0 v
      rw [loadHolds_mul_gen_pow]; exact hv
    · show σ (.n (c + 2)) = σ (.n (c + 1)) + σ (.n (oqDot s 10))
      rw [eC 2, eC 1, hdot1]; rfl
    · show σ (.n (c + 3)) = σ (.n (c + 2)) * σ (.n 7)
      rw [eC 3, eC 2, eP 7 (by omega)]; rfl
    · show σ (.n (c + 4)) = σ (.n 6) * σ (.n 0)
      rw [eC 4, eP 6 (by omega), eP 0 (by omega)]; rfl
    · show LoadHolds rd (σ (.n (c + 4))) 1 (σ (.n (c + 3)))
      rw [eC 4, eC 3]
      show LoadHolds rd (ch * gen ^ j) 1 ((v + rowDot s.base s.I r w) * mu)
      rw [loadHolds_mul_gen_pow]; exact hv1
    · exact eC 5
    · show σ (.n (c + 6)) = σ (.n 0) * σ (.n (c + 5))
      rw [eC 6, eC 5, eP 0 (by omega)]; rfl
    · show σ (.n (c + 7)) = σ (.n (c + 6)) + σ (.n 1)
      rw [eC 7, eC 6, eP 1 (by omega)]; rfl
    · exact eC 8
    · show σ (.n (c + 9)) = σ (.n 0) * σ (.n (c + 8))
      rw [eC 9, eC 8, eP 0 (by omega)]; rfl

end
end LeanVM.Guest.B1
