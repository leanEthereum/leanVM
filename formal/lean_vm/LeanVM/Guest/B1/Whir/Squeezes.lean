/-
  LeanVM.Guest.B1.Whir.Squeezes

  The query positions of a level: the Spec's `sampleQueries` from the query grind's challenge, and
  the template's squeezes and decodes (`osSqueezes`), soundly.
-/

module

public import LeanVM.Guest.B1.Whir.Commit

/-!
# The query positions

* `sqPositions d w count`: query `k` is the position `k % P` of sample `k / P`, `P = 128 / d`
  (`qwPosOf`), the samples `w`;
* `sampleQueriesAux_run`: from a sponge with nothing waiting, `sampleQueriesAux` squeezes
  `⌈rem / P⌉` samples, the positions theirs; `sampleQueries_runG`: from a grind's ground challenge
  `c` and capacity `cap`, the first sample is `c`, the rest squeezed from `cap`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The Spec's positions -/

theorem RunsFromG.of_eq {α : Type} {p : VerifierProgram α} {cap : List E} {c : E} {xs xs' : List E}
    {a a' : α} {t t' : Fs} (h : RunsFromG p cap c xs a t) (hx : xs = xs') (ha : a = a')
    (ht : t = t') : RunsFromG p cap c xs' a' t' := by
  subst hx ha ht; exact h

/-- The positions of `count` queries of depth `d` from the samples `w`: query `k` is position
`k % P` of sample `k / P`, `P = 128 / d`. -/
def sqPositions (d : ℕ) (w : ℕ → E) (count : ℕ) : List ℕ :=
  (List.range count).map fun k ↦ qwPosOf d (w (k / (128 / d))) (k % (128 / d))

/-- The samples `rem` positions take, `⌈rem / P⌉`. -/
def sqCount (P rem : ℕ) : ℕ := (rem + P - 1) / P

theorem sqCount_zero (P : ℕ) (hP : 1 ≤ P) : sqCount P 0 = 0 := by
  unfold sqCount; rw [Nat.zero_add]; exact Nat.div_eq_of_lt (by omega)

theorem sqCount_step {P rem : ℕ} (hP : 1 ≤ P) (h0 : rem ≠ 0) :
    sqCount P rem = sqCount P (rem - min P rem) + 1 := by
  unfold sqCount
  by_cases hr : rem ≤ P
  · rw [min_eq_right hr, Nat.sub_self, Nat.zero_add,
      Nat.div_eq_of_lt (show P - 1 < P by omega), Nat.zero_add]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · rw [min_eq_left (by omega), show rem + P - 1 = rem - P + P - 1 + P by omega,
      Nat.add_div_right _ (by omega)]

/-- **`sampleQueriesAux` from a sponge with nothing waiting**: `⌈rem / P⌉` squeezes, the positions
theirs. -/
theorem sampleQueriesAux_run (d : ℕ) (hP : 1 ≤ 128 / d) :
    ∀ (fuel rem : ℕ) (F : Fs), rem ≤ 128 / d * fuel →
      RunsTo (sampleQueriesAux d fuel rem) F []
        (sqPositions d (fun j ↦ (F.squeezeN j).2.squeeze.1) rem)
        (F.squeezeN (sqCount (128 / d) rem)).2
  | 0, rem, F, h => by
    obtain rfl : rem = 0 := by simpa using h
    rw [sqCount_zero _ hP]
    exact runsTo_ret _ _
  | fuel + 1, rem, F, h => by
    by_cases h0 : rem = 0
    · subst h0
      rw [sqCount_zero _ hP]
      simp only [sampleQueriesAux, ↓reduceIte]
      exact runsTo_ret _ _
    · set P := 128 / d with hPd
      have hrest : rem - min P rem ≤ P * fuel := by
        rcases Nat.le_total rem P with hr | hr
        · rw [min_eq_right hr]; omega
        · rw [min_eq_left hr]; rw [Nat.mul_succ] at h; omega
      have ih := sampleQueriesAux_run d hP fuel (rem - min P rem) F.squeeze.2 hrest
      have hrun := (runsTo_sampleE F).bind (f := fun x ↦ do
          let rest ← sampleQueriesAux d fuel (rem - min P rem)
          return (List.range (min P rem)).map (fun c ↦ (eToNat x >>> (c * d)) % 2 ^ d) ++ rest)
        (ih.bind (f := fun rest ↦ (pure ((List.range (min P rem)).map
          (fun c ↦ (eToNat F.squeeze.1 >>> (c * d)) % 2 ^ d) ++ rest) : VerifierProgram (List ℕ)))
          (runsTo_ret _ _))
      simp only [sampleQueriesAux, h0, ↓reduceIte]
      refine RunsTo.of_eq hrun rfl rfl ?_ ?_
      · apply List.ext_getElem (by simp [sqPositions])
        intro k h1 h2
        simp only [sqPositions, List.getElem_map, List.getElem_range]
        by_cases hk : k < min P rem
        · rw [List.getElem_append_left (by simpa using hk)]
          simp only [List.getElem_map, List.getElem_range]
          have hkP : k < P := lt_of_lt_of_le hk (min_le_left _ _)
          rw [Nat.div_eq_of_lt hkP, Nat.mod_eq_of_lt hkP]
          rfl
        · rw [List.getElem_append_right (by simp only [List.length_map, List.length_range]; omega)]
          simp only [List.length_map, List.length_range, List.getElem_map, List.getElem_range]
          have hmin : min P rem = P := by
            simp only [sqPositions, List.length_map, List.length_range] at h2
            exact min_eq_left (by omega)
          rw [hmin] at hk ⊢
          obtain ⟨j, rfl⟩ : ∃ j, k = j + P := ⟨k - P, by omega⟩
          rw [Nat.add_sub_cancel, Nat.add_div_right _ (by omega), Nat.add_mod_right]
          rfl
      · rw [sqCount_step hP h0]
        rfl

/-- **`sampleQueries` from a grind's ground challenge** `c` at the capacity `cap`: the first
sample is `c`, the next squeezed from `cap`; `⌈count / P⌉` samples. -/
theorem sampleQueries_runG (d count : ℕ) (hP : 1 ≤ 128 / d) (hc : 0 < count) (cap : List E)
    (c : E) :
    RunsFromG (sampleQueries d count) cap c []
      (sqPositions d (fun j ↦ if j = 0 then c else
        (((⟨cap, []⟩ : Fs).squeezeN (j - 1)).2.squeeze.1)) count)
      ((⟨cap, []⟩ : Fs).squeezeN (sqCount (128 / d) count - 1)).2 := by
  obtain ⟨fuel, rfl⟩ : ∃ fuel, count = fuel + 1 := ⟨count - 1, by omega⟩
  set P := 128 / d with hPd
  have hrest : fuel + 1 - min P (fuel + 1) ≤ P * fuel := by
    rcases Nat.le_total (fuel + 1) P with hr | hr
    · rw [min_eq_right hr]; omega
    · rw [min_eq_left hr]
      have : P * fuel ≥ 1 * fuel := Nat.mul_le_mul_right _ hP
      omega
  have ih := sampleQueriesAux_run d hP fuel (fuel + 1 - min P (fuel + 1)) ⟨cap, []⟩ hrest
  have hrun := (runsFromG_sample cap c).bind (f := fun x ↦ do
      let rest ← sampleQueriesAux d fuel (fuel + 1 - min P (fuel + 1))
      return (List.range (min P (fuel + 1))).map (fun i ↦ (eToNat x >>> (i * d)) % 2 ^ d) ++ rest)
    (ih.bind (f := fun rest ↦ (pure ((List.range (min P (fuel + 1))).map
      (fun i ↦ (eToNat c >>> (i * d)) % 2 ^ d) ++ rest) : VerifierProgram (List ℕ)))
      (runsTo_ret _ _))
  simp only [sampleQueries, sampleQueriesAux, Nat.add_one_ne_zero, ↓reduceIte]
  refine RunsFromG.of_eq hrun rfl ?_ ?_
  · apply List.ext_getElem (by simp [sqPositions])
    intro k h1 h2
    simp only [sqPositions, List.getElem_map, List.getElem_range]
    by_cases hk : k < min P (fuel + 1)
    · rw [List.getElem_append_left (by simpa using hk)]
      simp only [List.getElem_map, List.getElem_range]
      have hkP : k < P := lt_of_lt_of_le hk (min_le_left _ _)
      rw [Nat.div_eq_of_lt hkP, Nat.mod_eq_of_lt hkP]
      rfl
    · rw [List.getElem_append_right (by simp only [List.length_map, List.length_range]; omega)]
      simp only [List.length_map, List.length_range, List.getElem_map, List.getElem_range]
      have hmin : min P (fuel + 1) = P := by
        simp only [sqPositions, List.length_map, List.length_range] at h2
        exact min_eq_left (by omega)
      rw [hmin] at hk ⊢
      obtain ⟨j, rfl⟩ : ∃ j, k = j + P := ⟨k - P, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_div_right _ (by omega), Nat.add_mod_right]
      simp [hPd]
  · rw [sqCount_step hP (Nat.add_one_ne_zero fuel), Nat.add_sub_cancel]

/-! ## The template's squeezes -/

/-- Sample `j` of a level's positions: the query grind's challenge `w0`, then the squeezes from the
capacity `cap`. -/
def sqSample (w0 : E) (cap : List E) (j : ℕ) : E :=
  if j = 0 then w0 else ((⟨cap, []⟩ : Fs).squeezeN (j - 1)).2.squeeze.1

/-- The name of a level's `decode_query_windows`. -/
def decName (lv : OsLv) : String :=
  "decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth

/-- What a level's squeezes leave (`level_positions`' dispatch, `osPositions_sound` in
`Whir/LpSound.lean`): sample `j < S` decoded at `posOff + j·P` of `query_positions` and
`query_win_ptrs`; the sponge after the `S - 1` squeezes. -/
structure SqOut (rd : Reader) (σ : Val) (lv : OsLv) (st st' : OsSt) (w0 : E) (cap : List E) :
    Prop where
  dec : ∀ j < lv.squeezes, MeaningDecodeQueryWindows lv.depth lv.capDepth rd
    [sqSample w0 cap j, σ (.n osQpos) * gen ^ (lv.posOff + j * (128 / lv.depth)),
      σ (.n osQbp) * gen ^ (lv.posOff + j * (128 / lv.depth)), σ (.n osTabs)] []
  F : st'.F σ = ((⟨cap, []⟩ : Fs).squeezeN (lv.squeezes - 1)).2
  fs : st'.fs.length = 5
  mats : MatsOk σ st'.mats
  cur : st'.cur σ = st.cur σ
  co : st'.co = st.co
  claim : st'.claim = st.claim
  pad : st'.pad = st.pad

end
end LeanVM.Guest.B1.Whir
