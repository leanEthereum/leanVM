/-
  LeanVM.Guest.B1.Tables.TermAtMem

  `check_opening_terminal`'s own buffers, placed: their honest words and the memory they make.
-/

module

public import LeanVM.Guest.B1.Tables.TerminalCAll
public import LeanVM.Guest.B1.Tables.FlockAt

/-!
# The terminal's buffers

The terminal's five `HeapBuf`s hold, honestly, three prefix chains (`twChain`), the public
input's chain (`twPi`) and the ring switch's rows (`twRows`). `termMem_of`: a memory holding them
and the words the chains read is `TermMem`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- A prefix chain of `as` against `bs`, `m` entries past the seed `1`. -/
def twChain (as bs : List E) (m : ℕ) : List E :=
  (List.range 35).map fun j => if j ≤ m then 1 * eqEval (as.take j) (bs.take j) else 0

/-- The public input's chain at the point's words `X`. -/
def twPi (rm : E) (X : ℕ → E) (n : ℕ) : List E :=
  (List.range 35).map fun j => if j = 0 then 1 else if j ≤ n then
    (1 + rm + X 0) * ∏ i ∈ Finset.Ico 1 j, (1 + X i) else 0

/-- The ring switch's rows over `zs` and `ps`, `τ + 9` of them. -/
def twRows (zs ps : List E) (τ : ℕ) : List E :=
  (List.range (64 * (τ + 9))).map fun i => ringRow 1 (zs.take (i / 64)) (ps.take (i / 64)) (i % 64)

section
variable {rd : Reader}

theorem readsAt_take {p : E} {l : List E} (h : ReadsAt rd p l) (k : ℕ) : ReadsAt rd p (l.take k) :=
  fun j hj => by
    simp only [List.length_take] at hj
    rw [List.getElem_take]; exact h j (by omega)

theorem readsAt_drop {p : E} {l : List E} (h : ReadsAt rd p l) (k : ℕ) :
    ReadsAt rd (p * gen ^ k) (l.drop k) := fun j hj => by
  simp only [List.length_drop] at hj
  rw [List.getElem_drop]
  exact lh_back (h (k + j) (by omega)) rfl

theorem memL_one {L : Main.Layout} (h : MemL rd L) {b : ℕ} {w : List E} (hq : (b, w) ∈ L) :
    ReadsAt rd (ofK (Parameters.gpow b)) w := h _ hq

/-- **A prefix chain** from its buffer's words. -/
theorem chain_of {b : ℕ} {as bs : List E} {m : ℕ} (hm : m ≤ 34)
    (h : ReadsAt rd (ofK (Parameters.gpow b)) (twChain as bs m)) {a bb : E}
    (ha : ReadsAt rd a as) (hb : ReadsAt rd bb bs) (hal : as.length = m) (hbl : bs.length = m) :
    MeaningEqPrefixChain rd [ofK (Parameters.gpow b), 1, a, bb, gen ^ m] [] := by
  refine ⟨rfl, m, by unfold ordG; omega, rfl, as, bs, hal, hbl, ha, hb, fun j hj => ?_⟩
  have := readsAt_get h (k := j) (by simp [twChain]; omega)
  rwa [twChain, getD_map_range _ _ (by omega), ite_pos' hj] at this

/-- **The ring switch's rows** from their buffer's words. -/
theorem rows_of {b : ℕ} {zs ps : List E} {τ : ℕ} (hτ : τ < 29) (h : ReadsAt rd (ofK (Parameters.gpow b)) (twRows zs ps τ))
    {z pt : E} (hz : ReadsAt rd z zs) (hp : ReadsAt rd pt ps) (hzl : zs.length = τ + 8)
    (hpl : ps.length = τ + 8) :
    MeaningRsEqRun rd [ofK (Parameters.gpow b), z, pt, gen ^ (τ + 8)] [] ∧
      ∀ k < 64, LoadHolds rd (ofK (Parameters.gpow b)) k 1 := by
  refine ⟨⟨rfl, τ + 8, by unfold ordG; omega, rfl, zs, ps, hzl, hpl, hz, hp, List.replicate 64 1,
    by simp, fun _ j hj k hk => ?_⟩, fun k hk => ?_⟩
  · have := readsAt_get h (k := 64 * j + k) (by simp [twRows]; nlinarith)
    rw [twRows, getD_map_range _ _ (by nlinarith), show (64 * j + k) / 64 = j by omega,
      show (64 * j + k) % 64 = k by omega] at this
    rwa [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_replicate]
  · have := readsAt_get h (k := k) (by simp [twRows]; omega)
    rwa [twRows, getD_map_range _ _ (by omega), show k / 64 = 0 by omega, show k % 64 = k by omega,
      List.take_zero, List.take_zero, show ringRow 1 [] [] k = 1 from rfl] at this

/-- **The public input's chain** from its buffer's words. -/
theorem pi_of {b : ℕ} {a2 : E} {X : ℕ → E} {n : ℕ} (hn : n < 33) (h1 : 1 ≤ n)
    (h : ReadsAt rd (ofK (Parameters.gpow b)) (twPi a2 X n)) {pt : E}
    (hX : ∀ k < n, LoadHolds rd pt k (X k)) :
    LoadHolds rd (ofK (Parameters.gpow b)) 0 1 ∧
      (∀ n', gen ^ n = gen ^ n' → n' < 33 → ∀ X' : ℕ → E, (∀ k < n', LoadHolds rd pt k (X' k)) →
        ∀ j, 1 ≤ j → j ≤ n' →
          LoadHolds rd (ofK (Parameters.gpow b)) j ((1 + a2 + X' 0) * ∏ i ∈ Finset.Ico 1 j, (1 + X' i))) := by
  refine ⟨?_, fun n' hn' hn33 X' hX' j hj1 hj => ?_⟩
  · have := readsAt_get h (k := 0) (by simp [twPi])
    rwa [twPi, getD_map_range _ _ (by omega), ite_pos' rfl] at this
  · obtain rfl : n = n' := gen_pow_inj' (by omega) (by omega) hn'
    have hXX : ∀ i < n, X' i = X i := fun i hi => loadHolds_unique (hX' i hi) (hX i hi)
    have := readsAt_get h (k := j) (by simp [twPi]; omega)
    rw [twPi, getD_map_range _ _ (by omega), ite_neg' (by omega), ite_pos' hj] at this
    rw [hXX 0 (by omega), Finset.prod_congr rfl fun i hi => by
      rw [hXX i (by simp at hi; omega)]]
    exact this

/-- The sizes of the terminal's `HeapBuf`s. -/
def termSizes (τ : ℕ) : List ℕ := [35, 35, 35, 35, 64 * (τ + 9)]

/-- The terminal's buffers' honest words. -/
def termOwn (bp chis ptw zs : List E) (rm : E) (n τ : ℕ) : List (List E) :=
  [twChain bp (ptw.take bp.length) bp.length, twChain chis (ptw.take chis.length) chis.length,
    twChain (chis.take τ) ((ptw.drop 8).take τ) τ, twPi rm (fun k => ptw.getD k 0) n,
    twRows zs (ptw.take (τ + 8)) τ]

theorem termOwn_fit (bp chis ptw zs : List E) (rm : E) (n τ : ℕ) :
    List.Forall₂ (fun c s => c.length ≤ s) (termOwn bp chis ptw zs rm n τ) (termSizes τ) := by
  simp [termOwn, termSizes, twChain, twPi, twRows]

theorem termBases (τ b : ℕ) : bases b (termSizes τ) = [b, b + 35, b + 35 + 35, b + 35 + 35 + 35,
    b + 35 + 35 + 35 + 35] := rfl

/-- **The terminal's honest memory** from its buffers and the words its chains read. -/
theorem termMem_of {b : ℕ} {bp chis ptw zs : List E} {n τ : ℕ}
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 : E}
    (hB : MemL rd (bufL b (termSizes τ) (termOwn bp chis ptw zs a2 n τ)))
    (hbp : ReadsAt rd a0 bp) (hch : ReadsAt rd a1 chis) (hpt : ReadsAt rd a13 ptw)
    (hzs : ReadsAt rd a11 zs) (hptl : ptw.length = 42) (h3 : a3 = gen ^ bp.length)
    (h4 : a4 = gen ^ chis.length) (h5 : a5 = gen ^ n) (h6 : a6 = gen ^ τ) (hbpl : bp.length < 33)
    (hchl : chis.length < 33) (hτc : τ ≤ chis.length) (hτ : τ + 8 ≤ 28) (hn : n < 33) (hn1 : 1 ≤ n)
    (hzl : zs.length = τ + 8) :
    TermMem rd [ofK (Parameters.gpow b), ofK (Parameters.gpow (b + 35)),
      ofK (Parameters.gpow (b + 35 + 35)), ofK (Parameters.gpow (b + 35 + 35 + 35)),
      ofK (Parameters.gpow (b + 35 + 35 + 35 + 35))]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16] := by
  rw [bufL, termBases, termOwn] at hB
  simp only [List.zip_cons_cons, List.zip_nil_right] at hB
  have r0 := memL_one hB (b := b) (w := twChain bp (ptw.take bp.length) bp.length) (by simp)
  have r1 := memL_one hB (b := b + 35) (w := twChain chis (ptw.take chis.length) chis.length) (by simp)
  have r2 := memL_one hB (b := b + 35 + 35) (w := twChain (chis.take τ) ((ptw.drop 8).take τ) τ)
    (by simp)
  have r3 := memL_one hB (b := b + 35 + 35 + 35) (w := twPi a2 (fun k => ptw.getD k 0) n) (by simp)
  have r4 := memL_one hB (b := b + 35 + 35 + 35 + 35) (w := twRows zs (ptw.take (τ + 8)) τ) (by simp)
  have hX : ∀ k < n, LoadHolds rd a13 k (ptw.getD k 0) := fun k hk => readsAt_get hpt (by omega)
  obtain ⟨p0, p1⟩ := pi_of hn hn1 r3 hX
  obtain ⟨q0, q1⟩ := rows_of (by omega) r4 hzs (readsAt_take hpt (τ + 8)) hzl (by simp; omega)
  refine ⟨?_, ?_, ?_, p0, fun n' hn' hn33 X' hX' => p1 n' (by rw [← h5, hn']) hn33 X' hX', ?_, q1⟩
  · rw [h3]
    exact chain_of (by omega) r0 hbp (readsAt_take hpt _) rfl (by simp; omega)
  · rw [h4]
    exact chain_of (by omega) r1 hch (readsAt_take hpt _) rfl (by simp; omega)
  · rw [h6]
    exact chain_of (by omega) r2 (readsAt_take hch τ) (readsAt_take (readsAt_drop hpt 8) τ)
      (by simp; omega) (by simp; omega)
  · rw [h6, ← pow_add]; exact q0

end

end
end LeanVM.Guest.B1
