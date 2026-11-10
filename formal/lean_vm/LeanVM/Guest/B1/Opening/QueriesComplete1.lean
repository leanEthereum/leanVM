/-
  LeanVM.Guest.B1.Opening.QueriesComplete1

  The completeness of one query's row: its packs, its padding run, its fold and, at the final
  level, its check, at the honest values.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesHonest
public import LeanVM.Guest.B1.Opening.QueriesW

/-!
# A query's row, completeness

With the valuation `σ` the honest values `d.val` on the query's range (`d.Hv σ`):

* `oqPacks_complete`: every atom of the packs (level 0);
* `oqPad_complete`: of the padding run, when emitted;
* `oqFold_complete`: of the fold, the rounds in memory at `coefs` (`RoundsAt`), the point `x`,
  no combiner `t_j` zero;
* `oqFin_complete`: of the final check, the coefficients at `hs` (`WordsAt`), the fold's value
  their novel sum over the chain (`finEq`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `novel_eval`'s later levels' statements' next free value is past their first. -/
theorem nvLevelsT_ge {ws : ℕ → ℕ} : ∀ (c i : ℕ) (ins : List ℕ) (k : ℕ), k ≤ (nvLevelsT ws c i ins k).2.2 := by
  intro c i ins k
  rw [QD.nvLevelsT_next (fun _ ↦ 0) c i ins (ins.map fun _ ↦ 0) k (by simp)]
  omega

namespace QD

variable (d : QD) {rd : Reader} {σ : Val}

/-! ## The places -/

theorem b_le_ch : d.b ≤ d.ch := by rw [ch_off]; omega

theorem ch_le_v : d.ch ≤ d.v := by rw [v_eq]; omega

theorem v_lt_oqNovel (s : Oq) (hs : V) (v : ℕ) : v < (oqNovel s hs v).2.2 := by
  simp only [oqNovel]
  exact lt_of_lt_of_le (by omega) (nvLevelsT_ge _ _ _ _)

theorem v_lt_e : d.v < d.e := by
  show d.v < oqRes d.s d.b d.emit + 1
  unfold oqRes
  split
  · exact Nat.lt_succ_of_lt (v_lt_oqNovel _ _ _)
  · exact Nat.lt_succ_self _

/-- The query's index `i` before the fold's value. -/
theorem hv_of {σ : Val} (hv : d.Hv σ) {i : ℕ} (h1 : d.b ≤ i) (h2 : i ≤ d.v) : σ (.n i) = d.val i :=
  hv i h1 (by have := d.v_lt_e; omega)

/-! ## The packs -/

theorem oqPacks_complete (hb : d.s.base = 1) (hv : d.Hv σ) :
    ∀ a, Stmt.atom a ∈ oqPacksT d.b d.s.I → a.Holds rd σ := by
  have hk1 := d.k1_eq
  have hc := d.ch_off
  have hcv := d.ch_le_v
  have hpl : d.packVals.length = 3 * (d.s.I / 2) := by rw [packVals_length]; simp [hb]
  have hrl := d.rowVals_length
  intro a ha
  simp only [oqPacksT, List.mem_flatten, List.mem_map, List.mem_range] at ha
  obtain ⟨_, ⟨j, hj, rfl⟩, ha⟩ := ha
  have r0 : σ (.n (d.b + 2 * j)) = d.cell (2 * j) := by
    rw [d.hv_of hv (by omega) (by omega), val_row d (by omega)]
  have r1 : σ (.n (d.b + 2 * j + 1)) = d.cell (2 * j + 1) := by
    rw [d.hv_of hv (by omega) (by omega), Nat.add_assoc, val_row d (by omega)]
  have vt : ∀ t < 3, σ (.n (d.b + d.s.I + 3 * j + t)) = (d.packV j).getD t 0 := fun t ht => by
    rw [d.hv_of hv (by omega) (by omega), val_pack d hb hj ht]
  have v0 := vt 0 (by omega); have v1 := vt 1 (by omega); have v2 := vt 2 (by omega)
  simp only [packV, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2
  have hcell : ∀ i, d.cell i = ofK (d.row.getD i 0) := fun i ↦ by simp [cell, hb]
  simp only [oqPackT, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact ⟨by rw [r0, hcell]; exact ofK_isInK _, by rw [r1, hcell]; exact ofK_isInK _⟩
  · exact v0
  · show σ _ = σ _ * σ _
    rw [v1, v0, r1]
  · show σ _ = σ _ + σ _
    rw [v2, r0, v1, pk, hcell, hcell, word_y, ofK_add_y_mul_ofK]

/-! ## The padding run -/

theorem oqPad_complete (he : d.emit = true) (hv : d.Hv σ) :
    ∀ a, Stmt.atom a ∈ oqPadT (oqK1 d.s d.b) → a.Holds rd σ := by
  have hk1 := d.k1_eq
  have hkL := d.kL_eq
  have hc := d.ch_eq
  have hcv := d.ch_le_v
  have hpl : d.padVals.length = 5 := by rw [padVals_length, he]; rfl
  have v : ∀ i < 5, σ (.n (d.k1 + i)) =
      [word 1 0, word 0 0, word 0 0, word 0 0, word 0 0].getD i 0 := fun i hi => by
    rw [d.hv_of hv (by omega) (by omega), val_pad d he hi]
  intro a ha
  simp only [oqPadT, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · show σ (.n d.k1) = _
    simpa using v 0 (by omega)
  · show σ (.n (d.k1 + 1)) = _
    simpa using v 1 (by omega)
  · show σ (.n (d.k1 + 2)) = _
    simpa using v 2 (by omega)
  · show σ (.n (d.k1 + 3)) = _
    simpa using v 3 (by omega)
  · show σ (.n (d.k1 + 4)) = _
    simpa using v 4 (by omega)

/-! ## The fold -/

/-- The offset of round `j`'s outputs in its values. -/
def oH (j : ℕ) : ℕ := 8 + (if j = 0 then 0 else 1)

theorem roundVals_head (j : ℕ) {o : ℕ} (ho : o < 8) :
    (d.roundVals j).getD o 0 = [(d.rd j).alpha, (d.rd j).beta, (d.rd j).beta * d.x, d.t j,
      (d.rd j).theta, word 1 0, (d.t j)⁻¹, d.r j].getD o 0 := by
  rw [roundVals, List.append_assoc, List.getD_append _ _ _ _ (by simpa using ho)]

theorem roundVals_scale {j : ℕ} (hj : j ≠ 0) : (d.roundVals j).getD 8 0 = d.scale j := by
  rw [roundVals, List.getD_append _ _ _ _ (by simp [hj]), List.getD_append_right _ _ _ _ (by simp)]
  simp [hj]

theorem roundVals_out (j : ℕ) {m c : ℕ} (hm : m < 2 ^ (d.s.folds - 1 - j)) (hc : c < 2) :
    (d.roundVals j).getD (oH j + (2 * m + c)) 0 = [d.r j * d.hiV j m, d.acc j m].getD c 0 := by
  have hl : ([(d.rd j).alpha, (d.rd j).beta, (d.rd j).beta * d.x, d.t j, (d.rd j).theta, word 1 0,
      (d.t j)⁻¹, d.r j] ++ (if j = 0 then [] else [d.scale j])).length = oH j := by
    unfold oH; split <;> simp
  rw [roundVals, List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, Nat.add_sub_cancel_left]
  exact getD_flatMap_const _ (c := 2) (fun _ ↦ rfl) 0 hm hc

theorem oqRO_eq (F j : ℕ) : oqRO d.s F j = oqRK d.s F j + oH j := by
  simp only [oqRO, oH]; omega

/-- **The fold's atoms hold** at the honest values, the rounds at `coefs`, the point `x`, every
combiner nonzero. -/
theorem oqFold_complete {coefs x : V} (hf1 : 1 ≤ d.s.folds) (hv : d.Hv σ)
    (hR : RoundsAt rd (σ coefs) d.rounds) (hrl : d.rounds.length = d.s.folds) (hx : σ x = d.x)
    (hnz : ∀ j < d.s.folds, d.t j ≠ 0) :
    ∀ a, Stmt.atom a ∈ oqFoldT d.s coefs x d.b d.ch → a.Holds rd σ := by
  have hbc := d.b_le_ch
  have hvv := d.v_eq
  have hrk := d.oqRK_eq d.ch
  -- a round's value at offset `o`
  have hvr : ∀ j < d.s.folds, ∀ o < (d.roundVals j).length,
      σ (.n (oqRK d.s d.ch j + o)) = (d.roundVals j).getD o 0 := by
    intro j hj o ho
    have h1 : offOf d.roundVals (j + 1) ≤ offOf d.roundVals d.s.folds := offOf_mono _ hj
    simp only [offOf] at h1
    rw [d.hv_of hv (by rw [hrk]; omega) (by rw [hrk, hvv]; omega), val_round d hj ho]
  have hlen : ∀ j, oH j + 2 * 2 ^ (d.s.folds - 1 - j) = (d.roundVals j).length := fun j ↦ by
    rw [roundVals_length]; simp only [oH]
  have hhead : ∀ j < d.s.folds, ∀ o < 8,
      σ (.n (oqRK d.s d.ch j + o)) = [(d.rd j).alpha, (d.rd j).beta, (d.rd j).beta * d.x, d.t j,
        (d.rd j).theta, word 1 0, (d.t j)⁻¹, d.r j].getD o 0 := fun j hj o ho ↦ by
    rw [hvr j hj o (by rw [← hlen]; unfold oH; split <;> omega), roundVals_head d j ho]
  have hout : ∀ j < d.s.folds, ∀ m < 2 ^ (d.s.folds - 1 - j), ∀ c < 2,
      σ (.n (oqRO d.s d.ch j + 2 * m + c)) = [d.r j * d.hiV j m, d.acc j m].getD c 0 := by
    intro j hj m hm c hc
    rw [oqRO_eq, Nat.add_assoc, Nat.add_assoc, hvr j hj _ (by rw [← hlen]; omega),
      roundVals_out d j hm hc]
  -- the scale after round `j`
  have hsc : ∀ j < d.s.folds, σ (.n (oqScale d.s d.ch j)) = d.scale j := by
    intro j hj
    rcases j with _ | j
    · simp only [oqScale, ↓reduceIte]
      rw [hhead 0 hj 3 (by omega)]
      rfl
    · simp only [oqScale, Nat.succ_ne_zero, ↓reduceIte]
      rw [hvr _ hj 8 (by rw [← hlen]; simp only [oH, Nat.succ_ne_zero, ↓reduceIte]; omega),
        roundVals_scale d (Nat.succ_ne_zero j)]
  -- the lanes round `j` reads
  have hlohi : ∀ j < d.s.folds, ∀ m < 2 ^ (d.s.folds - 1 - j),
      σ (.n (oqLoHi d.s d.b d.ch j m).1) + d.r j * σ (.n (oqLoHi d.s d.b d.ch j m).2) = d.acc j m ∧
        σ (.n (oqLoHi d.s d.b d.ch j m).2) = d.hiV j m := by
    intro j hj m hm
    have hI : d.s.I = 2 ^ d.s.folds := rfl
    rcases j with _ | j
    · have h2 : 2 * m + 1 < d.s.I := by
        rw [hI]
        have : 2 ^ d.s.folds = 2 * 2 ^ (d.s.folds - 1) := by
          rw [← pow_succ']; congr 1; omega
        simp only [Nat.sub_zero] at hm; omega
      have hrow : ∀ i < d.s.I, σ (.n (d.b + i)) = d.cell i := fun i hi ↦ by
        rw [d.hv_of hv (by omega) (by have := d.ch_off; rw [rowVals_length] at this; omega),
          val_row d hi]
      simp only [oqLoHi, ↓reduceIte, hiV, acc, lane0]
      split
      · rw [show d.b + d.s.I - 1 - 2 * m = d.b + (d.s.I - 1 - 2 * m) by omega,
          show d.b + d.s.I - 2 - 2 * m = d.b + (d.s.I - 2 - 2 * m) by omega, hrow _ (by omega),
          hrow _ (by omega)]
        exact ⟨rfl, rfl⟩
      · rw [hrow _ (by omega), Nat.add_assoc, hrow _ (by omega)]
        exact ⟨rfl, rfl⟩
    · have hm2 : 2 * m + 1 < 2 ^ (d.s.folds - 1 - j) := by
        have : 2 ^ (d.s.folds - 1 - j) = 2 * 2 ^ (d.s.folds - 1 - (j + 1)) := by
          rw [← pow_succ']; congr 1; omega
        omega
      simp only [oqLoHi, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, oqAcc, hiV, acc]
      have e0 := hout j (by omega) (2 * m) (by omega) 1 (by omega)
      have e1 := hout j (by omega) (2 * m + 1) hm2 1 (by omega)
      simp only [List.getD_cons_succ, List.getD_cons_zero] at e0 e1
      rw [e0, e1]
      exact ⟨rfl, rfl⟩
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · simp only [List.mem_flatten, List.mem_map, List.mem_range] at ha
    obtain ⟨_, ⟨j, hj, rfl⟩, ha⟩ := ha
    have hRj := hR j (by rw [hrl]; exact hj)
    have g0 := hhead j hj 0 (by omega); have g1 := hhead j hj 1 (by omega)
    have g2 := hhead j hj 2 (by omega); have g3 := hhead j hj 3 (by omega)
    have g4 := hhead j hj 4 (by omega); have g5 := hhead j hj 5 (by omega)
    have g6 := hhead j hj 6 (by omega); have g7 := hhead j hj 7 (by omega)
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at g0 g1 g2 g3 g4 g5 g6 g7
    unfold oqRoundT at ha
    dsimp only at ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · show LoadHolds rd _ _ _
          rw [g0]; exact hRj.1
        · show LoadHolds rd _ _ _
          rw [g1]; exact hRj.2.1
        · show σ _ = σ _ * σ _
          rw [g2, g1, hx]
        · show σ _ = σ _ + σ _
          rw [g3, g0, g2]; rfl
        · show LoadHolds rd _ _ _
          rw [g4]; exact hRj.2.2
        · exact g5
        · show σ _ = σ _ * σ _
          rw [g5, g6, g3, word_one, inv_mul_cancel₀ (hnz j hj)]
        · show σ _ = σ _ + σ _
          rw [g7, g4, g6]; rfl
      · rcases j with _ | j
        · simp at ha
        · simp only [Nat.succ_ne_zero, ↓reduceIte, List.mem_singleton, Stmt.atom.injEq] at ha
          subst ha
          show σ _ = σ _ * σ _
          rw [hvr _ hj 8 (by rw [← hlen]; simp only [oH, Nat.succ_ne_zero, ↓reduceIte]; omega),
            roundVals_scale d (Nat.succ_ne_zero j), Nat.add_sub_cancel, hsc j (by omega), g3]
          rfl
    · simp only [List.mem_flatten, List.mem_map, List.mem_range] at ha
      obtain ⟨_, ⟨m, hm, rfl⟩, ha⟩ := ha
      have o0 := hout j hj m hm 0 (by omega)
      have o1 := hout j hj m hm 1 (by omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at o0 o1
      obtain ⟨hl1, hl2⟩ := hlohi j hj m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      rcases ha with rfl | rfl
      · show σ _ = σ _ * σ _
        rw [o0, g7, hl2]
      · show σ _ = σ _ + σ _
        rw [o1, o0, ← hl1, hl2]
  · simp only [List.mem_singleton, Stmt.atom.injEq] at ha
    subst ha
    show σ _ = σ _ * σ _
    have h0 := hout (d.s.folds - 1) (by omega) 0 (by positivity) 1 (by omega)
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.mul_zero, Nat.add_zero] at h0
    rw [show oqVal d.s d.ch = d.v from rfl, d.hv_of hv (by have := d.ch_le_v; omega) le_rfl, val_v,
      hsc _ (by omega), show oqAcc d.s d.ch (d.s.folds - 1) 0 = oqRO d.s d.ch (d.s.folds - 1) + 1
        by simp [oqAcc], h0]
    rfl

/-! ## The final check -/

theorem nvLevelT_complete {w : V} : ∀ (ins : List ℕ) (k : ℕ),
    (∀ p < ins.length, σ (.n (k + p)) =
      (nvLevelVals (σ w) (ins.map fun u ↦ σ (.n u))).getD p 0) →
      (∀ a, Stmt.atom a ∈ (nvLevelT w ins k).1 → a.Holds rd σ) ∧
        (nvLevelT w ins k).2.1.map (fun u ↦ σ (.n u)) = nvPair (σ w) (ins.map fun u ↦ σ (.n u))
  | lo :: hi :: rest, k, hval => by
    have v0 := hval 0 (by simp)
    have v1 := hval 1 (by simp)
    simp only [List.map_cons, nvLevelVals, List.cons_append, List.getD_cons_zero,
      List.getD_cons_succ, Nat.add_zero] at v0 v1
    have ih := nvLevelT_complete (w := w) rest (k + 2) fun p hp ↦ by
      have := hval (p + 2) (by simp; omega)
      simpa [nvLevelVals, show k + (p + 2) = k + 2 + p by omega] using this
    rw [nvLevelT]
    refine ⟨fun a ha ↦ ?_, ?_⟩
    · rcases List.mem_append.mp ha with ha | ha
      · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
        rcases ha with rfl | rfl
        · exact v0
        · show σ _ = σ _ + σ _
          rw [v1, v0]
      · exact ih.1 a ha
    · simp only [List.map_cons, nvPair]
      rw [ih.2, v1]
  | [lo], k, hval => by
    have v0 := hval 0 (by simp)
    simp only [List.map_cons, List.map_nil, nvLevelVals, List.getD_cons_zero, Nat.add_zero] at v0
    refine ⟨fun a ha ↦ ?_, by simp [nvLevelT, nvPair, v0]⟩
    simp only [nvLevelT, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    subst ha
    exact v0
  | [], _, _ => ⟨fun a ha ↦ by simp [nvLevelT] at ha, by simp [nvLevelT, nvPair]⟩

theorem nvLevelsT_complete {ws : ℕ → ℕ} (W : ℕ → E) : ∀ (c i : ℕ) (ins : List ℕ) (k : ℕ),
    (∀ j, i ≤ j → j < i + c → σ (.n (ws j)) = W j) →
    (∀ p < (nvVals W c i (ins.map fun u ↦ σ (.n u))).length, σ (.n (k + p)) =
      (nvVals W c i (ins.map fun u ↦ σ (.n u))).getD p 0) →
      (∀ a, Stmt.atom a ∈ (nvLevelsT ws c i ins k).1 → a.Holds rd σ) ∧
        (nvLevelsT ws c i ins k).2.1.map (fun u ↦ σ (.n u)) = nvTree W c i (ins.map fun u ↦ σ (.n u))
  | 0, _, _, _, _, _ => ⟨fun a ha ↦ by simp [nvLevelsT] at ha, rfl⟩
  | c + 1, i, ins, k, hws, hval => by
    have hw : σ (.n (ws i)) = W i := hws i le_rfl (by omega)
    have hlen := length_nvLevelVals (W i) (ins.map fun u ↦ σ (.n u))
    have hl := nvLevelT_complete (rd := rd) (σ := σ) (w := .n (ws i)) ins k fun p hp ↦ by
      have := hval p (by simp only [nvVals, List.length_append, hlen, List.length_map]; omega)
      rw [this, hw, nvVals, List.getD_append _ _ _ _ (by rw [hlen]; simpa using hp)]
    have hout := length_nvLevelT_out (w := .n (ws i)) ins k
    have ih := nvLevelsT_complete W c (i + 1) (nvLevelT (.n (ws i)) ins k).2.1
      (nvLevelT (.n (ws i)) ins k).2.2 (fun j h1 h2 ↦ hws j (by omega) (by omega)) fun p hp ↦ by
        rw [hl.2, hw] at hp ⊢
        have hlt : ins.length + p < (nvVals W (c + 1) i (ins.map fun u ↦ σ (.n u))).length := by
          simp only [nvVals, List.length_append, hlen, List.length_map]; omega
        have := hval (ins.length + p) hlt
        rw [hout.2, Nat.add_assoc, this, nvVals, List.getD_append_right _ _ _ _ (by simp [hlen]),
          hlen, List.length_map, Nat.add_sub_cancel_left]
    rw [nvLevelsT]
    refine ⟨fun a ha ↦ ?_, ?_⟩
    · rcases List.mem_append.mp ha with ha | ha
      · exact hl.1 a ha
      · exact ih.1 a ha
    · rw [ih.2, hl.2, hw, nvTree]

/-- The final check's honest equation: the fold's value is the novel sum of the coefficients over
the chain. -/
def finEq : Prop := d.foldVal = novelSum d.hsv d.W d.s.nHs d.s.hsBits

theorem hsv_take_eq {l : List E} {n : ℕ} (h : n ≤ l.length) :
    l.take n = (List.range' 0 n).map fun c ↦ l.getD c 0 := by
  refine List.ext_getElem (by simp; omega) fun i h1 h2 ↦ ?_
  simp [List.getD_eq_getElem?_getD, show i < l.length by simp at h1; omega]

/-- **The final check's atoms hold** at the honest values, the coefficients at `hs`, the fold's
value their novel sum (`finEq`). -/
theorem oqFin_complete {x hs : V} (hfinal : d.s.final = 1) (hfin : d.s.FinOk) (hv : d.Hv σ)
    (hx : σ x = d.x) (hW : WordsAt rd (σ hs) d.hsv) (hlen : d.hsv.length = d.s.nHs) (heq : d.finEq) :
    ∀ a, Stmt.atom a ∈ oqFinT d.s x hs d.v → a.Holds rd σ := by
  obtain ⟨hev, hn2, hb1, hbm⟩ := hfin hfinal
  have he := d.e_eq fun _ ↦ ⟨hev, by omega⟩
  have hvv := d.v_eq
  have hc := d.ch_off
  have hfl := d.foldVals_length
  set nv := nvVals d.W (d.s.hsBits - 1) 1 (nvPair (d.W 0) (d.hsv.take d.s.nHs)) with hnv
  have hcl := d.chainVals_length
  have hnl := d.nv0Vals_length
  have hfinL : d.finVals.length = 1 + 3 * d.s.mu + 4 * (d.s.nHs / 2) + nv.length + 1 := by
    simp only [finVals, hfinal, ↓reduceIte, List.length_append, hcl, hnl, List.length_cons,
      List.length_nil, hnv]
  have hvf : ∀ o < d.finVals.length, σ (.n (d.v + 1 + o)) = d.finVals.getD o 0 := fun o ho ↦ by
    rw [hv _ (by omega) (by rw [he]; simp only [vals, List.length_append]; omega), val_fin]
  have hfv : d.finVals = [d.x] ++ (d.chainVals ++ (d.nv0Vals ++ (nv ++ [word 0 0]))) := by
    simp only [finVals, hfinal, ↓reduceIte, List.append_assoc, hnv]
  -- the pieces' values
  have fx : σ (.n (d.v + 1)) = d.x := by
    have := hvf 0 (by omega); rw [hfv] at this; simpa using this
  have fch : ∀ i < d.s.mu, ∀ c < 3, σ (.n (d.v + 1 + (1 + (3 * i + c)))) =
      [word (d.s.vs.getD i 0) 0, d.W i + word (d.s.vs.getD i 0) 0, d.W (i + 1)].getD c 0 := by
    intro i hi c hcc
    rw [hvf _ (by omega), hfv, List.getD_append_right _ _ _ _ (by simp), List.length_singleton,
      Nat.add_sub_cancel_left, List.getD_append _ _ _ _ (by omega), chainVals]
    exact getD_flatMap_const _ (c := 3) (fun _ ↦ rfl) 0 hi hcc
  have fnv0 : ∀ m < d.s.nHs / 2, ∀ c < 4, σ (.n (d.v + 1 + (1 + (3 * d.s.mu + (4 * m + c))))) =
      [d.hsv.getD (2 * m) 0, d.hsv.getD (2 * m + 1) 0, d.W 0 * d.hsv.getD (2 * m + 1) 0,
        d.hsv.getD (2 * m) 0 + d.W 0 * d.hsv.getD (2 * m + 1) 0].getD c 0 := by
    intro m hm c hcc
    rw [hvf _ (by omega), hfv, List.getD_append_right _ _ _ _ (by simp), List.length_singleton,
      Nat.add_sub_cancel_left, List.getD_append_right _ _ _ _ (by omega), hcl,
      Nat.add_sub_cancel_left, List.getD_append _ _ _ _ (by omega), nv0Vals]
    exact getD_flatMap_const _ (c := 4) (fun _ ↦ rfl) 0 hm hcc
  have fnv : ∀ p < nv.length, σ (.n (d.v + 1 + (1 + (3 * d.s.mu + (4 * (d.s.nHs / 2) + p))))) =
      nv.getD p 0 := by
    intro p hp
    rw [hvf _ (by omega), hfv, List.getD_append_right _ _ _ _ (by simp), List.length_singleton,
      Nat.add_sub_cancel_left, List.getD_append_right _ _ _ _ (by omega), hcl,
      Nat.add_sub_cancel_left, List.getD_append_right _ _ _ _ (by omega), hnl,
      Nat.add_sub_cancel_left, List.getD_append _ _ _ _ hp]
  have flast : σ (.n (d.v + 1 + (1 + (3 * d.s.mu + (4 * (d.s.nHs / 2) + nv.length))))) = word 0 0 := by
    rw [hvf _ (by omega), hfv, List.getD_append_right _ _ _ _ (by simp), List.length_singleton,
      Nat.add_sub_cancel_left, List.getD_append_right _ _ _ _ (by omega), hcl,
      Nat.add_sub_cancel_left, List.getD_append_right _ _ _ _ (by omega), hnl,
      Nat.add_sub_cancel_left, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    rfl
  -- the chain's words
  have hws : ∀ i ≤ d.s.mu, σ (.n (oqWs d.v i)) = d.W i := by
    intro i hi
    rcases i with _ | i
    · simp only [oqWs, ↓reduceIte]; rw [fx]; rfl
    · have := fch i (by omega) 2 (by omega)
      simp only [List.getD_cons_succ, List.getD_cons_zero] at this
      simp only [oqWs, Nat.succ_ne_zero, ↓reduceIte]
      rw [← this]; congr 2; omega
  have hWs : ∀ i < d.s.mu, d.W (i + 1) = d.W i * (d.W i + word (d.s.vs.getD i 0) 0) := by
    intro i hi
    rw [W, W, wsChain, word_eOfNat, eOfNat]
    congr 3
    simp [List.getD_eq_getElem?_getD, show i < d.s.vs.length from hi]
  -- the novel sum's inputs after level 0
  have hins : ((List.range (d.s.nHs / 2)).map fun m ↦ d.v + 2 + 3 * d.s.mu + 4 * m + 3).map
      (fun u ↦ σ (.n u)) = nvPair (d.W 0) (d.hsv.take d.s.nHs) := by
    have h2 : d.s.nHs = 2 * (d.s.nHs / 2) := by omega
    rw [hsv_take_eq (by omega), h2, nvPair_range', ← h2, List.map_map]
    refine List.map_congr_left fun m hm ↦ ?_
    have := fnv0 m (List.mem_range.mp hm) 3 (by omega)
    simp only [List.getD_cons_succ, List.getD_cons_zero] at this
    simp only [Function.comp_apply, Nat.zero_add]
    rw [← this]; congr 2; omega
  have hnvT := nvLevelsT_complete (rd := rd) (σ := σ) (ws := oqWs d.v) d.W (d.s.hsBits - 1) 1
    ((List.range (d.s.nHs / 2)).map fun m ↦ d.v + 2 + 3 * d.s.mu + 4 * m + 3)
    (d.v + 2 + 3 * d.s.mu + 4 * (d.s.nHs / 2)) (fun j h1 h2 ↦ hws j (by omega)) (fun p hp ↦ by
      rw [hins] at hp ⊢
      rw [← fnv p hp]; congr 2; omega)
  have hnext : (oqNovel d.s hs d.v).2.2 = d.v + 2 + 3 * d.s.mu + 4 * (d.s.nHs / 2) + nv.length :=
    d.oqNovel_next hev (by omega)
  intro a ha
  unfold oqFinT at ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · -- the chain
      unfold oqWsT at ha
      rcases List.mem_append.mp ha with ha | ha
      · simp only [List.mem_singleton, Stmt.atom.injEq] at ha
        subst ha
        show σ _ = σ _
        rw [fx, hx]
      · simp only [List.mem_flatten, List.mem_map, List.mem_range] at ha
        obtain ⟨_, ⟨i, hi, rfl⟩, ha⟩ := ha
        have c0 := fch i hi 0 (by omega)
        have c1 := fch i hi 1 (by omega)
        have c2 := fch i hi 2 (by omega)
        simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at c0 c1 c2
        simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
        rcases ha with rfl | rfl | rfl
        · show σ _ = _
          rw [← c0]; congr 2; omega
        · show σ _ = σ _ + σ _
          rw [show d.v + 3 + 3 * i = d.v + 1 + (1 + (3 * i + 1)) by omega, c1,
            show d.v + 2 + 3 * i = d.v + 1 + (1 + 3 * i) by omega, c0, hws i (by omega)]
        · show σ _ = σ _ * σ _
          rw [show d.v + 4 + 3 * i = d.v + 1 + (1 + (3 * i + 2)) by omega, c2,
            show d.v + 3 + 3 * i = d.v + 1 + (1 + (3 * i + 1)) by omega, c1, hws i (by omega),
            hWs i hi]
    · -- the novel sum
      unfold oqNovel at ha
      dsimp only at ha
      rcases List.mem_append.mp ha with ha | ha
      · simp only [nvLevel0T, List.mem_flatten, List.mem_map, List.mem_range] at ha
        obtain ⟨_, ⟨m, hm, rfl⟩, ha⟩ := ha
        have n0 := fnv0 m hm 0 (by omega)
        have n1 := fnv0 m hm 1 (by omega)
        have n2 := fnv0 m hm 2 (by omega)
        have n3 := fnv0 m hm 3 (by omega)
        simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at n0 n1 n2 n3
        have e0 : d.v + 2 + 3 * d.s.mu + 4 * m = d.v + 1 + (1 + (3 * d.s.mu + 4 * m)) := by omega
        have e : ∀ c, d.v + 2 + 3 * d.s.mu + 4 * m + c =
            d.v + 1 + (1 + (3 * d.s.mu + (4 * m + c))) := fun c ↦ by omega
        simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
        rcases ha with rfl | rfl | rfl | rfl
        · show LoadHolds rd _ _ _
          rw [e0, n0]
          exact hW _ (by omega)
        · show LoadHolds rd _ _ _
          rw [e, n1]
          exact hW _ (by omega)
        · show σ _ = σ _ * σ _
          rw [e, n2, e, n1, hws 0 (by omega)]
        · show σ _ = σ _ + σ _
          rw [e, n3, e, n2, e0, n0]
      · exact hnvT.1 a ha
  · -- the check and the result
    simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl
    · show σ _ + σ _ = 0
      have hne := nvLevelsT_ne (ws := oqWs d.v) (d.s.hsBits - 1) 1
        ((List.range (d.s.nHs / 2)).map fun m ↦ d.v + 2 + 3 * d.s.mu + 4 * m + 3)
        (d.v + 2 + 3 * d.s.mu + 4 * (d.s.nHs / 2)) (by simp; omega)
      have hout : σ (.n ((oqNovel d.s hs d.v).2.1.headD 0)) =
          novelSum d.hsv d.W d.s.nHs d.s.hsBits := by
        rw [novelSum, show d.s.hsBits = d.s.hsBits - 1 + 1 by omega, nvTree, Nat.zero_add, ← hins,
          ← hnvT.2]
        simp only [oqNovel]
        revert hne
        generalize (nvLevelsT (oqWs d.v) (d.s.hsBits - 1) 1 _ _).2.1 = outs
        intro hne
        cases outs with
        | nil => exact absurd rfl hne
        | cons o _ => rfl
      rw [hout, d.hv_of hv (by have := d.b_le_ch; have := d.ch_le_v; omega) le_rfl, val_v,
        show d.foldVal = _ from heq, CharTwo.add_self_eq_zero]
    · show σ _ = _
      rw [hnext, show d.v + 2 + 3 * d.s.mu + 4 * (d.s.nHs / 2) + nv.length =
        d.v + 1 + (1 + (3 * d.s.mu + (4 * (d.s.nHs / 2) + nv.length))) by omega, flast]

end QD

end
end LeanVM.Guest.B1
