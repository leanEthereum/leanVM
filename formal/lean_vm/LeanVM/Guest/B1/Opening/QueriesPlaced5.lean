/-
  LeanVM.Guest.B1.Opening.QueriesPlaced5

  A deeper iteration's honest valuation.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced4

/-!
# A deeper iteration's valuation

`oqIter0F`: a deeper iteration's honest values (one query, its point `positions[x]` and its window
pointer `qptrs[x]`), from its query and the chain's word. `oqIter0_at`: its body holds statement by
statement, its tail's guard and arguments, its loads' pointers.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}


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
def oqIter0F (s : Oq) (args : List E) (D : QD) (v : E) (i : ℕ) : E :=
  let x := args.getD 0 0
  if i < 10 then args.getD i 0
  else if i = 10 then args.getD 2 0 * x
  else if i = 11 then D.x
  else if i = 12 then args.getD 3 0 * x
  else if i = 13 then D.bpv
  else if i < oqC0 s then D.val i
  else (oqIter0C s.final x (args.getD 1 0) (args.getD 8 0) (args.getD 9 0) v
    (oqResV s D.rounds (D.q, D.row, D.sibs))).getD (i - oqC0 s) 0

/-- **A deeper iteration at its honest values.** -/
theorem oqIter0_at {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) {cd j : ℕ}
    {N positions qptrs cap flags coefs hsp ch mu : E} {rounds : List FoldRound} {hsv : List E}
    {w : QW} {bp v : E}
    (hok : (oqQD s cd 14 true 0 bp cap flags rounds hsv w).Ok rd coefs hsp)
    (hx : LoadHolds rd positions j (eOfNat w.1)) (hb : LoadHolds rd qptrs j bp)
    (hv : s.final ≠ 1 → LoadHolds rd ch j v ∧ LoadHolds rd ch (j + 1) ((v + oqResV s rounds w) * mu))
    {σ : Val} (hσ : ∀ i, σ (.n i) = oqIter0F s
      [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu]
      (oqQD s cd 14 true 0 bp cap flags rounds hsv w) v i) :
    oqLoopParams.map σ = [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] ∧
      BlockOkC anyCall rd σ (oqLoop0A s) ∧ (oqQD s cd 14 true 0 bp cap flags rounds hsv w).Hv σ ∧
      σ (.n 10) = positions * gen ^ j ∧ σ (.n 12) = qptrs * gen ^ j ∧ σ (.n 13) = bp ∧
      (s.final ≠ 1 → σ (.n (oqC0 s)) = ch * gen ^ j ∧ σ (.n (oqC0 s + 4)) = ch * gen ^ j) ∧
      σ (.n (oqG0 s + 2)) = gen ^ j * gen + N ∧ σ (.n (oqG0 s + 4)) = gen ^ j * gen := by
  set D := oqQD s cd 14 true 0 bp cap flags rounds hsv w with hD
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
  have e13 : σ (.n 13) = bp := by rw [hσ]; simp [oqIter0F, hD, oqQD]
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
  obtain ⟨hA, hres, -⟩ := D.query_complete (σ := σ) (x := .n 11) (bp := .n 13) (cap := .n oqCap)
    (flags := .n oqFlags) (coefs := .n oqCoefs) (hsp := .n oqHs) (C := anyCall) hs hfin
    (by rw [eP 6 (by omega), eP 7 (by omega)]; exact hok) eQ e11 hp.1 hp.2 e13
    (eP 4 (by omega)) (eP 5 (by omega))
  replace hres : s.final ≠ 1 → σ (.n (oqRes s 14 true)) = oqResV s rounds w := fun hf ↦ by
    simp only [oqResV, hf, ↓reduceIte]; exact hres hf
  have eG : ∀ o < 5, σ (.n (oqG0 s + o)) = (oqGuardV (gen ^ j) N).getD o 0 := fun o _ ↦ by
    rw [oqG0_eq, Nat.add_assoc, eC, oqIter0C_guard]
  obtain ⟨hG, eG2, eG4⟩ := oqGuardA_okC (rd := rd) (C := anyCall) (eP 0 (by omega))
    (eP 1 (by omega)) eG
  have eS : s.final ≠ 1 → ∀ o < 5, σ (.n (oqC0 s + o)) =
      (oqStep0V (gen ^ j) ch mu v (oqResV s rounds w)).getD o 0 :=
    fun hf o ho ↦ by rw [eC, oqIter0C_step hf _ _ _ _ _ _ ho]
  refine ⟨?_, fun a ha => ?_, eQ, e10, e12, e13, fun hf ↦ ⟨?_, ?_⟩, eG2, eG4⟩
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
    · show σ (.n 10) = σ (.n oqPos) * σ (.n oqX)
      rw [e10, eP 2 (by omega), eP 0 (by omega)]; rfl
    · show LoadHolds rd (σ (.n 10)) 0 (σ (.n 11))
      rw [e10, e11, loadHolds_mul_gen_pow, Nat.add_zero]
      exact hx
    · show σ (.n 12) = σ (.n oqQp) * σ (.n oqX)
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
      · show σ (.n c) = σ (.n oqChainP) * σ (.n oqX)
        rw [c0, eP 8 (by omega), eP 0 (by omega)]; rfl
      · show LoadHolds rd (σ (.n c)) 0 (σ (.n (c + 1)))
        rw [c0, c1, loadHolds_mul_gen_pow]; exact hv0
      · show σ (.n (c + 2)) = σ (.n (c + 1)) + σ (.n (oqRes s 14 true))
        rw [c2, c1, hres hf]
      · show σ (.n (c + 3)) = σ (.n (c + 2)) * σ (.n oqLamInv)
        rw [c3, c2, eP 9 (by omega)]; rfl
      · show σ (.n (c + 4)) = σ (.n oqChainP) * σ (.n oqX)
        rw [c4, eP 8 (by omega), eP 0 (by omega)]; rfl
      · show LoadHolds rd (σ (.n (c + 4))) 1 (σ (.n (c + 3)))
        rw [c4, c3, loadHolds_mul_gen_pow]; exact hv1
  · exact hG a ha


end
end LeanVM.Guest.B1
