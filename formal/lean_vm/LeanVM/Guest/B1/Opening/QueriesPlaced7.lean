/-
  LeanVM.Guest.B1.Opening.QueriesPlaced7

  The honest valuation of `opening_queries`' own body, its chain buffer given.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced6
import LeanVM.Guest.Value.FieldBits

/-!
# The function's honest valuation

`oqMainF`: the honest values of `oqMainT`'s body: its parameters, `g`, `nG·g`, the chain's
pointer `ch` (the placement's `HeapBuf`); at level 0 the branch's word `odd_g + 1`, the even
start's `0`, the odd first query (its point, its window pointer, the query `D`, its result times
`λ⁻¹`) and the loop's moved positions and windows; deeper the chain's first word `0`; then `1,
1 + nG, 1` and the tail's values `rest`. `oqMain_at`: its start holds at these values
(`OqStartOk`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The function's values from `oqMK`: `1, 1 + nG, 1`, then `rest`. -/
def oqMainTl (nG : E) (rest : List E) : List E := [word 1 0, word 1 0 + nG, word 1 0] ++ rest

/-- **The function's honest values**, from its arguments, the chain's pointer `ch`, the odd first
query `D` (its window pointer `D.bpv`), and its values `rest` after `1, 1 + nG, 1`. -/
def oqMainF (s : Oq) (args : List E) (ch : E) (D : QD) (rest : List E) (i : ℕ) : E :=
  let lamInv := args.getD 2 0
  let nG := args.getD 7 0
  let oddG := args.getD 8 0
  let e := oqEnd s 17 true
  if i < 9 then args.getD i 0
  else if i = 9 then word 2 0 else if i = 10 then nG * word 2 0 else if i = 11 then ch
  else if s.base = 1 then
    (if i = 12 then word 1 0 else if i = 13 then oddG + word 1 0 else if i = 14 then word 0 0
      else if i = 15 then D.x else if i = 16 then D.bpv else if i < e then D.val i
      else if i = e then oqResV s D.rounds (D.q, D.row, D.sibs) * lamInv
      else if i = e + 1 then args.getD 5 0 * oddG else if i = e + 2 then args.getD 6 0 * oddG
      else (oqMainTl nG rest).getD (i - oqMK s) 0)
  else (if i = 12 then word 0 0 else (oqMainTl nG rest).getD (i - oqMK s) 0)

/-- The branch's word `g^odd + 1` is `0` exactly at `odd = 0`. -/
theorem gen_pow_add_one {odd : ℕ} (h : odd ≤ 1) : gen ^ odd + 1 = 0 ↔ odd = 0 := by
  constructor
  · intro h0
    by_contra hne
    obtain rfl : odd = 1 := by omega
    have h1 : gen ^ 1 = gen ^ 0 := by rw [pow_zero]; exact e_add_eq_zero_iff.mp h0
    exact absurd (gen_pow_inj (by norm_num) (by norm_num) h1) (by decide)
  · rintro rfl; rw [pow_zero]; exact e_add_self 1

variable {rd : Reader}

/-- **The function's start at its honest values**: it holds (`OqStartOk`), its parameters are its
arguments, and its chain's size and pointer, the loop's guard and start, at level 0 the branch's
word and the loop's moved positions and windows, and the odd query's values. -/
theorem oqMain_at {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) {odd cd : ℕ} (hodd : odd ≤ s.base)
    {cap flags lamInv coefs hsp positions qptrs nG ch bp : E}
    {rounds : List FoldRound} {hsv : List E} {w : QW}
    (h1 : odd = 1 → LoadHolds rd positions 0 (eOfNat w.1) ∧ LoadHolds rd qptrs 0 bp ∧
      (oqQD s cd 17 true 0 bp cap flags rounds hsv w).Ok rd coefs hsp ∧
      LoadHolds rd ch 0 (oqResV s rounds w * lamInv))
    (h0 : odd ≠ 1 → LoadHolds rd ch 0 0) (rest : List E) {σ : Val}
    (hσ : ∀ i, σ (.n i) = oqMainF s [cap, flags, lamInv, coefs, hsp, positions, qptrs, nG, gen ^ odd]
      ch (oqQD s cd 17 true 0 bp cap flags rounds hsv w) rest i) :
    oqMainParams.map σ = [cap, flags, lamInv, coefs, hsp, positions, qptrs, nG, gen ^ odd] ∧
      σ (.n 10) = nG * gen ∧ σ (.n 11) = ch ∧
      (∀ o, σ (.n (oqMK s + o)) = (oqMainTl nG rest).getD o 0) ∧
      (s.base = 1 → σ (.n 13) = gen ^ odd + 1 ∧ σ (.n (oqMK s - 2)) = positions * gen ^ odd ∧
        σ (.n (oqMK s - 1)) = qptrs * gen ^ odd) ∧
      (odd = 1 → σ (.n 16) = bp ∧ (oqQD s cd 17 true 0 bp cap flags rounds hsv w).Hv σ) ∧
      OqStartOk anyCall rd σ s := by
  set tl := oqMainTl nG rest with htl
  set args : List E := [cap, flags, lamInv, coefs, hsp, positions, qptrs, nG, gen ^ odd] with hargs
  set D := oqQD s cd 17 true 0 bp cap flags rounds hsv w with hD
  have eP : ∀ i < 9, σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; simp only [oqMainF, hi, ↓reduceIte]
  have e9 : σ (.n 9) = word 2 0 := by rw [hσ]; simp [oqMainF]
  have e10 : σ (.n 10) = nG * word 2 0 := by rw [hσ]; simp [oqMainF, hargs]
  have e11 : σ (.n 11) = ch := by rw [hσ]; simp [oqMainF]
  have hpar : oqMainParams.map σ = args := by
    simp only [oqMainParams, List.map_cons, List.map_nil, eP 0 (by omega), eP 1 (by omega),
      eP 2 (by omega), eP 3 (by omega), eP 4 (by omega), eP 5 (by omega), eP 6 (by omega),
      eP 7 (by omega), eP 8 (by omega)]
    rfl
  have hb01 : s.base = 0 ∨ s.base = 1 := by rcases hs with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  by_cases hb : s.base = 1
  · have hk : oqMK s = oqEnd s 17 true + 3 := by simp [oqMK, hb]
    set e := oqEnd s 17 true with he
    have i1 := D.b_le_ch
    have i2 := D.ch_lt_e
    have hDb : D.b = 17 := rfl
    have hDe : D.e = e := rfl
    have eT : ∀ o, σ (.n (oqMK s + o)) = tl.getD o 0 := fun o => by
      rw [hσ]
      simp only [oqMainF, hb, ← he, show ¬ oqMK s + o < 9 by omega, show oqMK s + o ≠ 9 by omega,
        show oqMK s + o ≠ 10 by omega, show oqMK s + o ≠ 11 by omega, show oqMK s + o ≠ 12 by omega,
        show oqMK s + o ≠ 13 by omega, show oqMK s + o ≠ 14 by omega, show oqMK s + o ≠ 15 by omega,
        show oqMK s + o ≠ 16 by omega, show ¬ oqMK s + o < e by omega, show oqMK s + o ≠ e by omega,
        show oqMK s + o ≠ e + 1 by omega, show oqMK s + o ≠ e + 2 by omega, ↓reduceIte,
        Nat.add_sub_cancel_left]
      rfl
    have e12 : σ (.n 12) = word 1 0 := by rw [hσ]; simp [oqMainF, hb]
    have e13 : σ (.n 13) = gen ^ odd + word 1 0 := by rw [hσ]; simp [oqMainF, hb, hargs]
    have e14 : σ (.n 14) = word 0 0 := by rw [hσ]; simp [oqMainF, hb]
    have e15 : σ (.n 15) = D.x := by rw [hσ]; simp [oqMainF, hb]
    have e16 : σ (.n 16) = bp := by rw [hσ]; simp [oqMainF, hb, hD, oqQD]
    have eQ : D.Hv σ := fun i h1 h2 => by
      rw [hσ]
      simp only [oqMainF, hb, ← he, show ¬ i < 9 by omega, show i ≠ 9 by omega, show i ≠ 10 by omega,
        show i ≠ 11 by omega, show i ≠ 12 by omega, show i ≠ 13 by omega, show i ≠ 14 by omega,
        show i ≠ 15 by omega, show i ≠ 16 by omega, show i < e by omega, ↓reduceIte]
    have eE : σ (.n e) = oqResV s rounds w * lamInv := by
      rw [hσ]
      simp only [oqMainF, hb, ← he, show ¬ e < 9 by omega, show e ≠ 9 by omega, show e ≠ 10 by omega,
        show e ≠ 11 by omega, show e ≠ 12 by omega, show e ≠ 13 by omega, show e ≠ 14 by omega,
        show e ≠ 15 by omega, show e ≠ 16 by omega, lt_irrefl, ↓reduceIte]
      rfl
    have eE1 : σ (.n (oqMK s - 2)) = positions * gen ^ odd := by
      rw [hσ, hk, show e + 3 - 2 = e + 1 by omega]
      simp only [oqMainF, hb, ← he, show ¬ e + 1 < 9 by omega, show e + 1 ≠ 9 by omega,
        show e + 1 ≠ 10 by omega, show e + 1 ≠ 11 by omega, show e + 1 ≠ 12 by omega,
        show e + 1 ≠ 13 by omega, show e + 1 ≠ 14 by omega, show e + 1 ≠ 15 by omega,
        show e + 1 ≠ 16 by omega, show ¬ e + 1 < e by omega, show e + 1 ≠ e by omega, ↓reduceIte]
      rfl
    have eE2 : σ (.n (oqMK s - 1)) = qptrs * gen ^ odd := by
      rw [hσ, hk, show e + 3 - 1 = e + 2 by omega]
      simp only [oqMainF, hb, ← he, show ¬ e + 2 < 9 by omega, show e + 2 ≠ 9 by omega,
        show e + 2 ≠ 10 by omega, show e + 2 ≠ 11 by omega, show e + 2 ≠ 12 by omega,
        show e + 2 ≠ 13 by omega, show e + 2 ≠ 14 by omega, show e + 2 ≠ 15 by omega,
        show e + 2 ≠ 16 by omega, show ¬ e + 2 < e by omega, show e + 2 ≠ e by omega, show e + 2 ≠ e + 1 by omega, ↓reduceIte]
      rfl
    have t0 : σ (.n (oqMK s)) = word 1 0 := by simpa [htl, oqMainTl] using eT 0
    have t1 : σ (.n (oqMK s + 1)) = word 1 0 + nG := by simpa [htl, oqMainTl] using eT 1
    have t2 : σ (.n (oqMK s + 2)) = word 1 0 := by simpa [htl, oqMainTl] using eT 2
    have e13' : σ (.n 13) = gen ^ odd + 1 := by rw [e13, word_one]
    have hodd1 : odd ≤ 1 := by omega
    refine ⟨hpar, by rw [e10, word_gen], e11, eT, fun _ ↦ ⟨e13', eE1, eE2⟩,
      fun _ ↦ ⟨e16, eQ⟩, ?_⟩
    unfold OqStartOk
    simp only [hb, ↓reduceIte]
    refine ⟨fun a ha => ?_, ?_, fun h13 => ?_, fun h13 => ?_⟩
    · simp only [oqMainPre, oqMainPost, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at ha
      rcases ha with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl)
      · exact e9
      · show σ (.n 10) = σ (.n oqMN) * σ (.n 9)
        rw [e10, e9, eP 7 (by omega)]; rfl
      · trivial
      · exact e12
      · show σ (.n 13) = σ (.n oqMOdd) + σ (.n 12)
        rw [e13, e12, eP 8 (by omega)]; rfl
      · show σ (.n (oqMK s - 2)) = σ (.n oqMPos) * σ (.n oqMOdd)
        rw [eE1, eP 5 (by omega), eP 8 (by omega)]; rfl
      · show σ (.n (oqMK s - 1)) = σ (.n oqMQp) * σ (.n oqMOdd)
        rw [eE2, eP 6 (by omega), eP 8 (by omega)]; rfl
      · exact t0
      · show σ (.n (oqMK s + 1)) = σ (.n (oqMK s)) + σ (.n oqMN)
        rw [t1, t0, eP 7 (by omega)]; rfl
      · exact t2
    · rw [e13', gen_pow_eq_ofK, ← ofK_one, ← ofK_add]; exact ofK_isInK _
    · have ho : odd ≠ 1 := fun h => by
        rw [e13'] at h13
        have := (gen_pow_add_one hodd1).mp h13
        omega
      intro a ha
      simp only [oqEvenT, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact e14
      · show LoadHolds rd (σ (.n 11)) 0 (σ (.n 14))
        rw [e11, e14, word_zero]; exact h0 ho
    · have ho : odd = 1 := by
        by_contra hne
        exact h13 (by rw [e13']; exact (gen_pow_add_one hodd1).mpr (by omega))
      obtain ⟨hx, hbp, hok, hc0⟩ := h1 ho
      have hp := D.pad_of_emit rfl eQ
      obtain ⟨hA, hres, -⟩ := D.query_complete (σ := σ) (x := .n 15) (bp := .n 16) (cap := .n oqMCap)
        (flags := .n oqMFlags) (coefs := .n oqMCoefs) (hsp := .n oqMHs) (C := anyCall) hs hfin
        (by rw [eP 3 (by omega), eP 4 (by omega)]; exact hok) eQ e15 hp.1 hp.2 e16
        (eP 0 (by omega)) (eP 1 (by omega))
      intro a ha
      simp only [oqOddT, List.mem_append] at ha
      rcases ha with (ha | ha) | ha
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · show LoadHolds rd (σ (.n oqMPos)) 0 (σ (.n 15))
          rw [e15, eP 5 (by omega)]; exact hx
        · show LoadHolds rd (σ (.n oqMQp)) 0 (σ (.n 16))
          rw [e16, eP 6 (by omega)]; exact hbp
      · exact hA a ha
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · show σ (.n e) = σ (.n (oqRes s 17 true)) * σ (.n oqMLamInv)
          by_cases hf : s.final = 1
          · have h' : oqRes s 17 true = e := by rw [he]; unfold oqEnd; simp [hf]
            rw [h', eE, eP 2 (by omega)]
            simp [oqResV, hf]
          · have hres' : σ (.n (oqRes s 17 true)) = oqResV s rounds w := by
              simp only [oqResV, hf, ↓reduceIte]; exact hres hf
            rw [eE, hres', eP 2 (by omega)]; rfl
        · show LoadHolds rd (σ (.n 11)) 0 (σ (.n e))
          rw [eE, e11]; exact hc0
  · have hb0 : s.base = 0 := by omega
    have hk : oqMK s = 13 := by simp [oqMK, hb]
    have eT : ∀ o, σ (.n (oqMK s + o)) = tl.getD o 0 := fun o => by
      rw [hσ]
      simp only [oqMainF, hb, hk, show ¬ 13 + o < 9 by omega, show 13 + o ≠ 9 by omega,
        show 13 + o ≠ 10 by omega, show 13 + o ≠ 11 by omega, show 13 + o ≠ 12 by omega,
        ↓reduceIte, Nat.add_sub_cancel_left]
      rfl
    have e12 : σ (.n 12) = word 0 0 := by rw [hσ]; simp [oqMainF, hb]
    have t0 : σ (.n (oqMK s)) = word 1 0 := by simpa [htl, oqMainTl] using eT 0
    have t1 : σ (.n (oqMK s + 1)) = word 1 0 + nG := by simpa [htl, oqMainTl] using eT 1
    have t2 : σ (.n (oqMK s + 2)) = word 1 0 := by simpa [htl, oqMainTl] using eT 2
    refine ⟨hpar, by rw [e10, word_gen], e11, eT, fun h ↦ absurd h hb,
      fun h ↦ absurd h (by omega), ?_⟩
    unfold OqStartOk
    simp only [hb, ↓reduceIte]
    intro a ha
    simp only [oqMainA, hb, ↓reduceIte, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at ha
    rcases ha with ((rfl | rfl | rfl) | (rfl | rfl)) | (rfl | rfl | rfl)
    · exact e9
    · show σ (.n 10) = σ (.n oqMN) * σ (.n 9)
      rw [e10, e9, eP 7 (by omega)]; rfl
    · trivial
    · exact e12
    · show LoadHolds rd (σ (.n 11)) 0 (σ (.n 12))
      rw [e11, e12, word_zero]; exact h0 (by omega)
    · exact t0
    · show σ (.n (oqMK s + 1)) = σ (.n (oqMK s)) + σ (.n oqMN)
      rw [t1, t0, eP 7 (by omega)]; rfl
    · exact t2

end
end LeanVM.Guest.B1
