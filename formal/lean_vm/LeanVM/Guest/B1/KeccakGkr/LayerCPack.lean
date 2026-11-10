/-
  LeanVM.Guest.B1.KeccakGkr.LayerCPack

  A layer's pack rounds, honestly: the round records in memory give every iteration's meaning,
  of the eight-round loop (`Pack8Hon`) and of the remainder loop (`PackRemHon`).
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCHon
public import LeanVM.Guest.B1.KeccakGkr.PackComplete

/-!
# The pack rounds, honestly

With the records' buffer (`recWords`), the claim's point, the stream words and the challenges
(`chs`) in memory:

* `recWords_rec`: record `j` is a `RoundRec`;
* `pack8_honest`: iteration `j < ⌊y/8⌋` of the eight-round loop has its meaning;
* `packRem_honest`: iteration `i < y mod 8` of the remainder loop, from record `⌊y/8⌋`, has its
  meaning.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

theorem flatPairs_get : ∀ (ms : List (E × E)) (k : ℕ) (hk : k < ms.length),
    (ms.flatMap fun m ↦ [m.1, m.2]).getD (2 * k) 0 = ms[k].1 ∧
      (ms.flatMap fun m ↦ [m.1, m.2]).getD (2 * k + 1) 0 = ms[k].2
  | [], _, hk => absurd hk (by simp)
  | m :: ms, 0, _ => by simp
  | m :: ms, k + 1, hk => by
    have := flatPairs_get ms k (by simpa using hk)
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.getElem_cons_succ]
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, show 2 * k + 1 + 1 + 1 = 2 * k + 1 + 1 + 1 from rfl,
      List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
    exact this

theorem kk_readsAt_getD {p : E} {xs : List E} (h : ReadsAt rd p xs) {k : ℕ} (hk : k < xs.length) :
    LoadHolds rd p k (xs.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

namespace LayerData

variable {D : LayerData} {first : ℕ}

/-- The pack rounds' messages, read at `cur·g^48`. -/
theorem xs_packReads (hpl : D.product.length = 47) {cur : E} (hxs : ReadsAt rd cur D.xs) {k : ℕ}
    (hk : k < D.packMsgs.length) :
    LoadHolds rd cur (48 + 2 * k) (D.packMsgs[k]).1 ∧
      LoadHolds rd cur (48 + 2 * k + 1) (D.packMsgs[k]).2 := by
  have h := hxs
  simp only [xs, List.append_assoc] at h
  rw [readsAt_append, hpl] at h
  obtain ⟨-, h⟩ := h
  rw [readsAt_append, List.length_singleton] at h
  obtain ⟨-, h⟩ := h
  rw [readsAt_append] at h
  obtain ⟨h, -⟩ := h
  rw [mul_assoc, ← pow_add] at h
  obtain ⟨h1, h2⟩ := flatPairs_get D.packMsgs k hk
  have hl := flatMap_pairs_length D.packMsgs
  have l1 := kk_readsAt_getD h (k := 2 * k) (by omega)
  have l2 := kk_readsAt_getD h (k := 2 * k + 1) (by omega)
  rw [h1, loadHolds_mul_gen_pow] at l1
  rw [h2, loadHolds_mul_gen_pow] at l2
  exact ⟨l1, by rwa [Nat.add_assoc]⟩

theorem xs_length (hpl : D.product.length = 47) (hpm : D.packMsgs.length = D.y)
    (hlm : D.localMsgs.length = 11) : D.xs.length = 48 + 2 * D.y + 36 := by
  simp only [xs, List.length_append, hpl, flatMap_pairs_length, flatMap_triples_length, hpm, hlm,
    List.length_cons, List.length_nil]

/-- **Record `j` in memory.** -/
theorem recWords_rec {base cur : E} (h : ReadsAt rd base (D.recWords first cur)) {j : ℕ}
    (hj : j < 16) (hjy : j ≤ D.y / 8 + D.y % 8) :
    RoundRec rd (base * gen ^ j) 0 (D.run first (D.recK j)).2.cap (D.recCur cur j)
      (D.run first (D.recK j)).1.1 (D.run first (D.recK j)).1.2.1 := by
  have field : ∀ f < 8, LoadHolds rd (base * gen ^ j) (16 * f) (D.recField first cur f j) := by
    intro f hf
    rw [loadHolds_mul_gen_pow]
    have hl : j + 16 * f < (D.recWords first cur).length := by simp [recWords]; omega
    have := h _ hl
    simp only [recWords, List.getElem_map, List.getElem_range] at this
    rw [show (j + 16 * f) % 16 = j by omega, show (j + 16 * f) / 16 = f by omega] at this
    simp only [hjy, ↓reduceIte] at this
    exact this
  obtain ⟨hcl, -⟩ := run_cap (D := D) (first := first) (D.recK j)
  refine ⟨⟨hcl, fun i hi ↦ ?_⟩, ?_, ?_, ?_⟩
  · have := field i (by omega)
    simp only [recField, show i < 5 by omega, ↓reduceIte] at this
    rw [List.getD_eq_getElem _ _ hi] at this
    rwa [zero_add, show i * krCap = 16 * i by simp [krCap]; ring]
  · have := field 5 (by norm_num)
    simpa [recField, krCap] using this
  · have := field 6 (by norm_num)
    simpa [recField, krCap] using this
  · have := field 7 (by norm_num)
    simpa [recField, krCap] using this

/-- A record at `rec·g^(j+1)` is the one written at offset `1` from `rec·g^j`. -/
theorem roundRec_pred {rec : E} {j : ℕ} {cap : List E} {cur cl sc : E}
    (h : RoundRec rd (rec * gen ^ (j + 1)) 0 cap cur cl sc) :
    RoundRec rd (rec * gen ^ j) 1 cap cur cl sc := by
  obtain ⟨⟨hl, hc⟩, h1, h2, h3⟩ := h
  refine ⟨⟨hl, fun i hi => ?_⟩, ?_, ?_, ?_⟩
  · have := hc i hi
    rw [show 1 + i * krCap = 1 + (0 + i * krCap) by omega, loadHolds_rec_succ]
    exact this
  · rw [show 1 + 5 * krCap = 1 + (0 + 5 * krCap) by omega, loadHolds_rec_succ]; exact h1
  · rw [show 1 + 6 * krCap = 1 + (0 + 6 * krCap) by omega, loadHolds_rec_succ]; exact h2
  · rw [show 1 + 7 * krCap = 1 + (0 + 7 * krCap) by omega, loadHolds_rec_succ]; exact h3

theorem getD_append_two {l : List E} {a b : E} {n : ℕ} (hl : l.length = n) :
    (l ++ [a, b]).getD n 0 = a ∧ (l ++ [a, b]).getD (n + 1) 0 = b := by
  subst hl
  simp

/-- The challenges of rounds `k .. k + n`, as the continuation's. -/
theorem chs_cont (hpm : D.packMsgs.length = D.y) {k n : ℕ} (hk : k + n ≤ D.y) {q : ℕ}
    (hq : q < n) :
    (D.chs first).getD (k + q) 0 = (packRunF ((D.c.point.drop k).take n)
      ((D.packMsgs.drop k).take n) (D.run first k).1.1 (D.run first k).1.2.1
      ⟨(D.run first k).2.cap, []⟩).1.2.2.getD q 0 := by
  rw [run_chsD (D := D) (first := first) hpm hk (by omega), run_add hpm hk]
  simp only [cont]
  rw [List.getD_append_right _ _ _ _ (by rw [run_chs_length hpm (by omega)]; omega),
    run_chs_length hpm (by omega), Nat.add_sub_cancel_left]

/-- **An iteration of the eight-round loop, honestly.** -/
theorem pack8_honest (hpl : D.product.length = 47) (hpm : D.packMsgs.length = D.y)
    {rec pp pt cur : E} (hrec : ReadsAt rd rec (D.recWords first cur))
    (hpp : ReadsAt rd pp D.c.point) (hxs : ReadsAt rd cur D.xs)
    (hpt : ReadsAt rd pt (D.chs first)) (hy30 : D.y ≤ 30) {j : ℕ} (hj : j < D.y / 8) :
    Pack8Hon rd rec pp pt (gen ^ j) := by
  have hy : D.y = D.c.point.length := rfl
  have hk0 : D.recK j = 8 * j := by unfold recK; split <;> omega
  have hk1 : D.recK (j + 1) = 8 * j + 8 := by unfold recK; split <;> omega
  have r0 := recWords_rec hrec (j := j) (by omega) (by omega)
  have r1 := recWords_rec hrec (j := j + 1) (by omega) (by omega)
  rw [hk0] at r0
  have e8 := run_add (D := D) (first := first) hpm (k := 8 * j) (n := 8) (by omega)
  rw [hk1, e8] at r1
  have hrsl : ((D.c.point.drop (8 * j)).take 8).length = 8 := by simp; omega
  have hmsl : ((D.packMsgs.drop (8 * j)).take 8).length = 8 := by simp; omega
  have hPl := packRunF_chs_length ((D.c.point.drop (8 * j)).take 8)
    ((D.packMsgs.drop (8 * j)).take 8) (D.run first (8 * j)).1.1 (D.run first (8 * j)).1.2.1
    ⟨(D.run first (8 * j)).2.cap, []⟩ (by rw [hrsl, hmsl])
  refine ⟨_, D.recCur cur j, _, _, _, _, _, _, _, _, by simpa [recCur, hk0] using r0,
    hrsl, ?_, ?_, eqChain_of_packRunF _ _ _ _ _ (by rw [hrsl, hmsl]), ?_, ?_⟩
  · intro k hk
    rw [hrsl] at hk
    rw [← pow_mul, show j * 8 = 8 * j by ring, loadHolds_mul_gen_pow]
    have := hpp (8 * j + k) (by omega)
    simpa [List.getElem_take, List.getElem_drop] using this
  · have h := readsAt_pairs (rd := rd) (p := D.recCur cur j) ((D.packMsgs.drop (8 * j)).take 8) 0
      fun q hq ↦ by
        rw [hmsl] at hq
        obtain ⟨g1e, g2e⟩ := xs_packReads hpl hxs (k := 8 * j + q) (by omega)
        have e : ((D.packMsgs.drop (8 * j)).take 8).getD q (0, 0) = D.packMsgs[8 * j + q] := by
          rw [List.getD_eq_getElem _ _ (by omega)]
          simp [List.getElem_take, List.getElem_drop]
        rw [e, recCur, hk0, loadHolds_mul_gen_pow, loadHolds_mul_gen_pow]
        refine ⟨?_, ?_⟩
        · rw [show 48 + 2 * (8 * j) + (0 + 2 * q) = 48 + 2 * (8 * j + q) by ring]; exact g1e
        · rw [show 48 + 2 * (8 * j) + (0 + 2 * q + 1) = 48 + 2 * (8 * j + q) + 1 by ring]
          exact g2e
    simpa using h
  · intro k hk
    rw [hPl, hrsl] at hk
    rw [← pow_mul, show j * 8 = 8 * j by ring, loadHolds_mul_gen_pow]
    have := kk_readsAt_getD hpt (k := 8 * j + k) (by rw [chs_length hpm]; omega)
    rw [chs_cont hpm (by omega) hk, List.getD_eq_getElem _ _ (by rw [hPl, hrsl]; exact hk)] at this
    exact this
  · refine roundRec_pred ?_
    simp only [recCur, hk1, cont] at r1
    rw [recCur, hk0, mul_assoc, ← pow_add, show 48 + 2 * (8 * j) + 16 = 48 + 2 * (8 * j + 8) by ring]
    exact r1

/-- **An iteration of the remainder loop, honestly**: at `g^i`, `i < y mod 8`, from the record
`⌊y/8⌋`, one round. -/
theorem packRem_honest (hpl : D.product.length = 47) (hpm : D.packMsgs.length = D.y)
    {rec pp pt cur : E} (hrec : ReadsAt rd rec (D.recWords first cur))
    (hpp : ReadsAt rd pp D.c.point) (hxs : ReadsAt rd cur D.xs)
    (hpt : ReadsAt rd pt (D.chs first)) (hy30 : D.y ≤ 30) {i : ℕ} (hi : i < D.y % 8) :
    PackRemHon rd (rec * gen ^ (D.y / 8)) (pp * (gen ^ (D.y / 8)) ^ 8)
      (pt * (gen ^ (D.y / 8)) ^ 8) (gen ^ i) := by
  have hy : D.y = D.c.point.length := rfl
  set k := 8 * (D.y / 8) + i with hkd
  have hk0 : D.recK (D.y / 8 + i) = k := by unfold recK; split <;> omega
  have hk1 : D.recK (D.y / 8 + i + 1) = k + 1 := by unfold recK; split <;> omega
  have r0 := recWords_rec hrec (j := D.y / 8 + i) (by omega) (by omega)
  have r1 := recWords_rec hrec (j := D.y / 8 + i + 1) (by omega) (by omega)
  rw [hk0] at r0
  have e1 := run_add (D := D) (first := first) hpm (k := k) (n := 1) (by omega)
  rw [hk1, e1] at r1
  have hr : (D.c.point.drop k).take 1 = [D.c.point.getD k 0] := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    simp [List.take_one, List.head?_drop, List.getElem?_eq_getElem (show k < D.c.point.length by omega)]
  have hm : (D.packMsgs.drop k).take 1 = [((D.packMsgs.getD k (0, 0)).1,
      (D.packMsgs.getD k (0, 0)).2)] := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    simp [List.take_one, List.head?_drop, List.getElem?_eq_getElem (show k < D.packMsgs.length by omega)]
  rw [hr, hm] at r1
  simp only [cont, packRunF_eqRound, packRunF_nil] at r1
  have hrec' : rec * gen ^ (D.y / 8) * gen ^ i = rec * gen ^ (D.y / 8 + i) := by
    rw [mul_assoc, ← pow_add]
  have hgk : ∀ p : E, p * (gen ^ (D.y / 8)) ^ 8 * gen ^ i = p * gen ^ k := fun p ↦ by
    rw [mul_assoc, ← pow_mul, ← pow_add, hkd, show D.y / 8 * 8 = 8 * (D.y / 8) by ring]
  obtain ⟨g1e, g2e⟩ := xs_packReads hpl hxs (k := k) (by omega)
  rw [← List.getD_eq_getElem (d := (0, 0))] at g1e g2e
  refine ⟨(D.run first k).2.cap, D.recCur cur (D.y / 8 + i), (D.run first k).1.1,
    (D.run first k).1.2.1, D.c.point.getD k 0, (D.packMsgs.getD k (0, 0)).1,
    (D.packMsgs.getD k (0, 0)).2, by rw [hrec']; simpa [recCur, hk0] using r0, ?_, ?_, ?_, ?_⟩
  · rw [hgk, loadHolds_mul_gen_pow, Nat.add_zero]
    exact kk_readsAt_getD hpp (by omega)
  · rw [recCur, hk0]
    intro q hq
    simp only [List.length_cons, List.length_nil] at hq
    rw [loadHolds_mul_gen_pow]
    interval_cases q
    · simpa using g1e
    · simpa [Nat.add_assoc] using g2e
  · rw [hgk, loadHolds_mul_gen_pow, Nat.add_zero]
    have := kk_readsAt_getD hpt (k := k + 0) (by rw [chs_length hpm]; omega)
    rw [chs_cont hpm (by omega) (show 0 < 1 by norm_num), hr, hm, packRunF_eqRound,
      packRunF_nil] at this
    exact this
  · rw [hrec']
    refine roundRec_pred ?_
    simp only [recCur, hk1] at r1
    rw [recCur, hk0, mul_assoc, ← pow_add, show 48 + 2 * k + 2 = 48 + 2 * (k + 1) by ring]
    exact r1

end LayerData

end
end LeanVM.Guest.B1.VerifySub
