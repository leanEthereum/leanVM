/-
  LeanVM.Guest.B1.Opening.QueriesPlaced7

  The honest valuation of `opening_queries`' own body, its chain buffer and its odd query's frame
  address given.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced6

/-!
# The function's honest valuation

`oqMainF`: the honest values of `oqMainT`'s body: its parameters, `1`, `μ = λ⁻¹`, `g`, `nG·g`, the
chain's pointer `ch` (the placement's `HeapBuf`), the odd first query (`D`, its window pointer
`bp`, its value times `μ`) or `0`, then `1, 1 + nG, 1, ch·nG`, the chain's end `hN`, `hN·λ_n`.
`oqMain_at`: its start holds at these values, statement by statement.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The function's values from `oqMK`: `1, 1 + nG, 1`, then `rest`. -/
def oqMainTl (nG : E) (rest : List E) : List E := [word 1 0, word 1 0 + nG, word 1 0] ++ rest

/-- **The function's honest values**, from its arguments, the chain's pointer `ch`, the odd first
query `D` and its window pointer `bp`, and its values `rest` after `1, 1 + nG, 1`. -/
def oqMainF (s : Oq) (odd : ℕ) (args : List E) (ch bp : E) (D : QD) (rest : List E) (i : ℕ) : E :=
  let lam := args.getD 2 0
  let nG := args.getD 6 0
  let k := oqMK s odd
  if i < 7 then args.getD i 0
  else if i = 7 then word 1 0 else if i = 8 then lam⁻¹ else if i = 9 then word 2 0
  else if i = 10 then nG * word 2 0 else if i = 11 then ch
  else if odd = 1 then
    (if i = 12 then bp else if i < k - 1 then D.val i
      else if i = k - 1 then rowDot s.base s.I D.row D.w * lam⁻¹
      else (oqMainTl nG rest).getD (i - k) 0)
  else (if i = 12 then word 0 0 else (oqMainTl nG rest).getD (i - k) 0)

variable {rd : Reader}

/-- **The function's start at its honest values**: it holds statement by statement. -/
theorem oqMain_at {s : Oq} (hs : s.RowShape) {odd : ℕ} (hodd : odd ≤ 1) {walk : String}
    {cap flags lam lamN qptrs wp nG ch bp : E}
    (hlam : lam ≠ 0) {r : List K} {w : ℕ → E} {q : ℕ} {sb : List Digest}
    (h1 : odd = 1 → LoadHolds rd qptrs 0 bp ∧
      (⟨s, 13, true, 0, r, w, q, sb, cap, flags⟩ : QD).Ok rd wp bp ∧
      LoadHolds rd ch 0 (rowDot s.base s.I r w * lam⁻¹))
    (h0 : odd ≠ 1 → LoadHolds rd ch 0 0) (rest : List E) {σ : Val}
    (hσ : ∀ i, σ (.n i) = oqMainF s odd [cap, flags, lam, lamN, qptrs, wp, nG] ch bp
      ⟨s, 13, true, 0, r, w, q, sb, cap, flags⟩ rest i) :
    [V.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6].map σ = [cap, flags, lam, lamN, qptrs, wp, nG] ∧
      σ (.n 8) = lam⁻¹ ∧ σ (.n 10) = nG * gen ∧ σ (.n 11) = ch ∧
      (∀ o, σ (.n (oqMK s odd + o)) = (oqMainTl nG rest).getD o 0) ∧
      (odd = 1 → σ (.n 12) = bp ∧ (⟨s, 13, true, 0, r, w, q, sb, cap, flags⟩ : QD).Hv σ ∧
        (σ (.n (oqOut s (oqKL s 13 true) (s.B - 1) 0)), σ (.n (oqOut s (oqKL s 13 true) (s.B - 1) 1))) =
          digestHalves (merkleLeafDigest r)) ∧
      BlockOkC anyCall rd σ (oqMainA s odd walk) := by
  set tl := oqMainTl nG rest with htl
  have mu1 : word 1 0 = lam⁻¹ * lam := by rw [word_one, inv_mul_cancel₀ hlam]
  have eP : ∀ i < 7, σ (.n i) = [cap, flags, lam, lamN, qptrs, wp, nG].getD i 0 := fun i hi => by
    rw [hσ]; simp only [oqMainF, hi, ↓reduceIte]
  have e7 : σ (.n 7) = word 1 0 := by rw [hσ]; simp [oqMainF]
  have e8 : σ (.n 8) = lam⁻¹ := by rw [hσ]; simp [oqMainF]
  have e9 : σ (.n 9) = word 2 0 := by rw [hσ]; simp [oqMainF]
  have e10 : σ (.n 10) = nG * word 2 0 := by rw [hσ]; simp [oqMainF]
  have e11 : σ (.n 11) = ch := by rw [hσ]; simp [oqMainF]
  have hpar : [V.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6].map σ =
      [cap, flags, lam, lamN, qptrs, wp, nG] := by
    simp only [List.map_cons, List.map_nil, eP 0 (by omega), eP 1 (by omega), eP 2 (by omega),
      eP 3 (by omega), eP 4 (by omega), eP 5 (by omega), eP 6 (by omega)]
    rfl
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hodd with rfl | rfl
  · have hk : oqMK s 0 = 13 := rfl
    have eT : ∀ o, σ (.n (oqMK s 0 + o)) = tl.getD o 0 := fun o => by
      rw [hσ]
      simp only [oqMainF, hk, show ¬ 13 + o < 7 by omega, show 13 + o ≠ 7 by omega,
        show 13 + o ≠ 8 by omega, show 13 + o ≠ 9 by omega, show 13 + o ≠ 10 by omega,
        show 13 + o ≠ 11 by omega, show (0 : ℕ) ≠ 1 by decide, show 13 + o ≠ 12 by omega,
        ↓reduceIte, Nat.add_sub_cancel_left]
      rfl
    have e12 : σ (.n 12) = word 0 0 := by rw [hσ]; simp [oqMainF]
    have t0 : σ (.n (oqMK s 0)) = word 1 0 := by simpa [htl, oqMainTl] using eT 0
    have t1 : σ (.n (oqMK s 0 + 1)) = word 1 0 + nG := by simpa [htl, oqMainTl] using eT 1
    have t2 : σ (.n (oqMK s 0 + 2)) = word 1 0 := by simpa [htl, oqMainTl] using eT 2
    refine ⟨hpar, e8, by rw [e10, word_gen], e11, eT, fun h ↦ absurd h (by decide), fun a ha => ?_⟩
    simp only [oqMainA, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at ha
    rcases ha with ((rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) | (rfl | rfl | rfl)
    · exact e7
    · show σ (.n 7) = σ (.n 8) * σ (.n 2)
      rw [e7, e8, eP 2 (by omega)]; exact mu1
    · exact e9
    · show σ (.n 10) = σ (.n 6) * σ (.n 9)
      rw [e10, e9, eP 6 (by omega)]; rfl
    · trivial
    · exact e12
    · show LoadHolds rd (σ (.n 11)) 0 (σ (.n 12))
      rw [e11, e12, word_zero]; exact h0 (by decide)
    · exact t0
    · show σ (.n (oqMK s 0 + 1)) = σ (.n (oqMK s 0)) + σ (.n 6)
      rw [t1, t0, eP 6 (by omega)]; rfl
    · exact t2
  · obtain ⟨hb, hok, hc0⟩ := h1 rfl
    set D : QD := ⟨s, 13, true, 0, r, w, q, sb, cap, flags⟩ with hD
    have hk : oqMK s 1 = D.e + 1 := by show oqEnd D.s D.b D.emit + 1 = _; rw [QD.end_eq D]
    obtain ⟨a1, a2, a3, a4, a5⟩ := D.places
    have hk1 := QD.k1_eq D
    have hDb : D.b = 13 := rfl
    set k := oqMK s 1 with hk'
    have hk13 : 13 < k - 1 := by omega
    have eQ : D.Hv σ := fun i h1 h2 => by
      rw [hσ]
      simp only [oqMainF, ← hk', show ¬ i < 7 by omega, show i ≠ 7 by omega, show i ≠ 8 by omega,
        show i ≠ 9 by omega, show i ≠ 10 by omega, show i ≠ 11 by omega, show i ≠ 12 by omega,
        show i < k - 1 by omega, ↓reduceIte]
    have eD : σ (.n (k - 1)) = rowDot s.base s.I r w * lam⁻¹ := by
      rw [hσ]
      simp only [oqMainF, ← hk', show ¬ k - 1 < 7 by omega, show k - 1 ≠ 7 by omega,
        show k - 1 ≠ 8 by omega, show k - 1 ≠ 9 by omega, show k - 1 ≠ 10 by omega,
        show k - 1 ≠ 11 by omega, show k - 1 ≠ 12 by omega, lt_irrefl, ↓reduceIte]
      rfl
    have eT : ∀ o, σ (.n (k + o)) = tl.getD o 0 := fun o => by
      rw [hσ]
      simp only [oqMainF, ← hk', show ¬ k + o < 7 by omega, show k + o ≠ 7 by omega,
        show k + o ≠ 8 by omega, show k + o ≠ 9 by omega, show k + o ≠ 10 by omega,
        show k + o ≠ 11 by omega, show k + o ≠ 12 by omega, show ¬ k + o < k - 1 by omega,
        show k + o ≠ k - 1 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
      rfl
    have e12 : σ (.n 12) = bp := by rw [hσ]; simp [oqMainF]
    have hp := D.pad_of_emit rfl eQ
    obtain ⟨hA, hdot, hl⟩ := D.query_complete (σ := σ) (bp := .n 12) (cap := .n 0) (flags := .n 1)
      (wp := .n 5) (walk := walk) (C := anyCall) hs (by rw [eP 5 (by omega), e12]; exact hok) eQ hp.1
      hp.2 (eP 0 (by omega)) (eP 1 (by omega)) trivial
    change σ (.n (oqDot s 13)) = rowDot s.base s.I r w at hdot
    have t0 : σ (.n k) = word 1 0 := by simpa [htl, oqMainTl] using eT 0
    have t1 : σ (.n (k + 1)) = word 1 0 + nG := by simpa [htl, oqMainTl] using eT 1
    have t2 : σ (.n (k + 2)) = word 1 0 := by simpa [htl, oqMainTl] using eT 2
    refine ⟨hpar, e8, by rw [e10, word_gen], e11, eT, fun _ ↦ ⟨e12, eQ, hl⟩, fun a ha => ?_⟩
    simp only [oqMainA, ↓reduceIte, List.mem_append] at ha
    rcases ha with (ha | ((ha | ha) | ha)) | ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl
      · exact e7
      · show σ (.n 7) = σ (.n 8) * σ (.n 2)
        rw [e7, e8, eP 2 (by omega)]; exact mu1
      · exact e9
      · show σ (.n 10) = σ (.n 6) * σ (.n 9)
        rw [e10, e9, eP 6 (by omega)]; rfl
      · trivial
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha
      show LoadHolds rd (σ (.n 4)) 0 (σ (.n 12))
      rw [e12, eP 4 (by omega)]; exact hb
    · exact hA a ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · show σ (.n (k - 1)) = σ (.n (oqDot s 13)) * σ (.n 8)
        rw [eD, hdot, e8]
      · show LoadHolds rd (σ (.n 11)) 0 (σ (.n (k - 1)))
        rw [eD, e11]; exact hc0
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact t0
      · show σ (.n (k + 1)) = σ (.n k) + σ (.n 6)
        rw [t1, t0, eP 6 (by omega)]; rfl
      · exact t2

end
end LeanVM.Guest.B1
