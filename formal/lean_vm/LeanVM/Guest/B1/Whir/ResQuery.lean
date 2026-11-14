/-
  LeanVM.Guest.B1.Whir.ResQuery

  The template's inline `residual_query` computes the prefix product `residualProd` and the high
  part's share, the chain's last value times `novelSum` of the high coefficients over its first
  values.
-/

module

public import LeanVM.Guest.B1.Whir.Flat
public import LeanVM.Guest.B1.Opening.Residual
public import LeanVM.Guest.B1.Opening.NovelSum

/-!
# `residual_query` inline (G:1462-1479)

`osResQuery pos bd ro hp ho vo ncols nhs hbits k` (`Template.lean`) walks the chain
`chain_0 = x` (the position), `chain_(t+1) = chain_t·(chain_t + VALS[vo + t])` (`osVals vo n`, the
words of `LIG_VANISH_VALS`) over `t < ncols`, multiplies `d_t + chain_t` over `t < ncols` (the row's
words `d_t` at `bd·g^(ro + t)`; the last chain step has no factor), keeps `chain_0 .. chain_2` as
`ws`, and returns the product and `chain_ncols · novel_eval(hs, ws, nhs, hbits)` (the coefficients
at `hp·g^(ho + ·)`):

* `osResChain_sound`: the chain's block;
* `osNovelEval_sound`: `novel_eval`'s levels are `nvTree` (`nvPair` a level);
* `osResQuery_val`: the product is `residualProd (osVals vo ncols) x D ncols`, the share
  `residualChain … ncols · novelSum hsv (residualChain …) nhs hbits`, for `1 ≤ ncols`,
  `1 ≤ nhs`, `hbits ≤ 3` and `hbits ≤ ncols + 1`.

`NovelEval.residual_high_eq` and `residualChain_vanishing` read these against the verifier.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The vanishing values `VALS[vo + t]`, `t < n`, as words. -/
def osVals (vo n : ℕ) : List E := (List.range n).map fun t ↦ word (vanishVal (vo + t)) 0

theorem osVals_getD {vo n t : ℕ} (h : t < n) :
    (osVals vo n).getD t 0 = word (vanishVal (vo + t)) 0 := by
  simp [osVals, List.getD_eq_getElem?_getD, h]

/-! ## The chain -/

/-- **The chain's block** from coordinate `t ≥ 1` with `f = ncols + 1 - t` steps left: the chain
so far at `ch` (`chain_(t-1)`), the product so far at `pe` (over `s < min t ncols`), the `ws` so
far (`chain_0 ..`, `min 3 t` of them); after it, the chain is `chain_ncols`, the product over
`s < ncols` and the `ws` are `min 3 (ncols + 1)` values `chain_0 ..`. -/
theorem osResChain_sound {bd ro vo ncols : ℕ} {x : E} {D : ℕ → E}
    (hD : ∀ s < ncols, LoadHolds rd (σ (.n bd)) (ro + s) (D s)) :
    ∀ (f t ch pe : ℕ) (ws : List ℕ) (k : ℕ), 1 ≤ t → t + f = ncols + 1 →
      σ (.n ch) = residualChain (osVals vo ncols) x (t - 1) →
      σ (.n pe) = residualProd (osVals vo ncols) x D (min t ncols) →
      ws.length = min 3 t → (∀ i < ws.length, σ (.n (ws.getD i 0)) = residualChain (osVals vo ncols) x i) →
      AllOk C rd σ (osResChain bd ro vo ncols f t ch pe ws k).1 →
      σ (.n (osResChain bd ro vo ncols f t ch pe ws k).2.1) = residualChain (osVals vo ncols) x ncols ∧
        σ (.n (osResChain bd ro vo ncols f t ch pe ws k).2.2.1) =
          residualProd (osVals vo ncols) x D ncols ∧
        (osResChain bd ro vo ncols f t ch pe ws k).2.2.2.1.length = min 3 (ncols + 1) ∧
        ∀ i < (osResChain bd ro vo ncols f t ch pe ws k).2.2.2.1.length,
          σ (.n ((osResChain bd ro vo ncols f t ch pe ws k).2.2.2.1.getD i 0)) =
            residualChain (osVals vo ncols) x i
  | 0, t, ch, pe, ws, k, _, htf, hch, hpe, hwl, hws, _ => by
    simp only [osResChain]
    obtain rfl : t = ncols + 1 := by omega
    refine ⟨by simpa using hch, by rw [hpe, min_eq_right (by omega)], hwl, hws⟩
  | f + 1, t, ch, pe, ws, k, ht, htf, hch, hpe, hwl, hws, hok => by
    set V := osVals vo ncols
    have htn : t ≤ ncols := by omega
    -- the chain step
    have hstep : ∀ ss : List Stmt, AllOk C rd σ
        ([osCst k (word (vanishVal (vo + t - 1)) 0), osAdd (k + 1) ch k, osMul (k + 2) ch (k + 1)] ++ ss) →
        σ (.n (k + 2)) = residualChain V x t ∧ AllOk C rd σ ss := fun ss h ↦ by
      rw [allOk_append] at h
      obtain ⟨hA, hR⟩ := h
      simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hA
      obtain ⟨c0, c1, c2⟩ := hA
      refine ⟨?_, hR⟩
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      rw [c2, c1, c0, hch, residualChain, osVals_getD (by omega), Nat.add_sub_cancel,
        show vo + (t' + 1) - 1 = vo + t' by omega]
    -- the `ws` after the step
    have hws' : ∀ (w2 : ℕ), σ (.n w2) = residualChain V x t →
        (if t < 3 then ws ++ [w2] else ws).length = min 3 (t + 1) ∧
        ∀ i < (if t < 3 then ws ++ [w2] else ws).length,
          σ (.n ((if t < 3 then ws ++ [w2] else ws).getD i 0)) = residualChain V x i := by
      intro w2 hw2
      by_cases h3 : t < 3
      · simp only [h3, ↓reduceIte, List.length_append, List.length_singleton]
        refine ⟨by rw [hwl]; omega, fun i hi ↦ ?_⟩
        rcases Nat.lt_or_ge i ws.length with hi' | hi'
        · rw [List.getD_append _ _ _ _ hi']; exact hws i hi'
        · obtain rfl : i = ws.length := by omega
          rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero, hw2, hwl,
            min_eq_right (by omega)]
      · simp only [h3, ↓reduceIte]
        exact ⟨by rw [hwl]; omega, hws⟩
    simp only [osResChain] at hok ⊢
    by_cases hlast : t = ncols
    · simp only [eq_true hlast, ↓reduceIte] at hok ⊢
      obtain ⟨hc, hR⟩ := hstep _ hok
      obtain ⟨hl, hw⟩ := hws' (k + 2) hc
      exact osResChain_sound hD f (t + 1) (k + 2) pe _ (k + 3) (by omega) (by omega)
        (by rw [Nat.add_sub_cancel]; exact hc)
        (by rw [hpe, min_eq_right (by omega), min_eq_right (by omega)]) hl hw hR
    · simp only [eq_false hlast, ↓reduceIte] at hok ⊢
      rw [List.append_assoc] at hok
      obtain ⟨hc, hR⟩ := hstep _ hok
      rw [allOk_append] at hR
      obtain ⟨hB, hR⟩ := hR
      simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hB
      obtain ⟨l3, a4, m5⟩ := hB
      have hd : σ (.n (k + 3)) = D t := loadHolds_unique l3 (hD t (by omega))
      obtain ⟨hl, hw⟩ := hws' (k + 2) hc
      exact osResChain_sound hD f (t + 1) (k + 2) (k + 5) _ (k + 6) (by omega) (by omega)
        (by rw [Nat.add_sub_cancel]; exact hc)
        (by rw [m5, a4, hd, hc, hpe, min_eq_left (by omega), min_eq_left (by omega), residualProd])
        hl hw hR

/-! ## `novel_eval` -/

theorem length_nvPair (w : E) : ∀ l : List E, (nvPair w l).length = (l.length + 1) / 2
  | _ :: _ :: rest => by
    simp only [nvPair, List.length_cons, length_nvPair w rest]
    omega
  | [_] => by simp [nvPair]
  | [] => by simp [nvPair]

/-- A level's inputs: loaded from `hp·g^(ho + ·)` before level `0`, else the values `vs`. -/
def NvIns (rd : Reader) (σ : Val) (hp ho : ℕ) (L : List E) : Option (List ℕ) → Prop
  | none => ∀ i < L.length, LoadHolds rd (σ (.n hp)) (ho + i) (L.getD i 0)
  | some vs => vs.length = L.length ∧ ∀ i < L.length, σ (.n (vs.getD i 0)) = L.getD i 0

/-- One output of a level: the statements before the rest of the level, and the output's value
`nvPair`'s at `m = M - (f + 1)`. -/
theorem osNovelLevel_step {hp ho w : ℕ} {ins : Option (List ℕ)} {L : List E}
    (hL : NvIns rd σ hp ho L ins) (f k : ℕ) (hf : f + 1 ≤ (L.length + 1) / 2) :
    ∃ (ss : List Stmt) (o k' : ℕ), osNovelLevel hp ho ins L.length w (f + 1) k =
        (ss ++ (osNovelLevel hp ho ins L.length w f k').1,
          o :: (osNovelLevel hp ho ins L.length w f k').2.1,
          (osNovelLevel hp ho ins L.length w f k').2.2) ∧
      (AllOk C rd σ ss → σ (.n o) =
        (nvPair (σ (.n w)) L).getD ((L.length + 1) / 2 - (f + 1)) 0) := by
  rw [osNovelLevel.eq_def, getD_nvPair]
  dsimp only
  have hm2 : 2 * ((L.length + 1) / 2 - (f + 1)) < L.length := by omega
  generalize (L.length + 1) / 2 - (f + 1) = m at hm2 ⊢
  by_cases two : 2 * m + 1 < L.length
  · cases ins with
    | none =>
      simp only [two, ↓reduceIte]
      refine ⟨_, _, _, rfl, fun h ↦ ?_⟩
      simp only [allOk_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at h
      obtain ⟨⟨l0, l1⟩, m2, a3⟩ := h
      have l1' := hL _ two
      rw [show ho + (2 * m + 1) = ho + 2 * m + 1 by omega] at l1'
      rw [a3, m2, loadHolds_unique l0 (hL _ hm2), loadHolds_unique l1 l1']
    | some vs =>
      simp only [two, ↓reduceIte]
      refine ⟨_, _, _, rfl, fun h ↦ ?_⟩
      simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.nil_append] at h
      obtain ⟨m2, a3⟩ := h
      rw [a3, m2, hL.2 _ hm2, hL.2 _ two]
  · have h0 : L.getD (2 * m + 1) 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
    rw [h0, mul_zero, add_zero]
    cases ins with
    | none =>
      simp only [two, ↓reduceIte]
      refine ⟨_, _, _, rfl, fun h ↦ ?_⟩
      simp only [allOk_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.append_nil]
        at h
      obtain ⟨l0, c1⟩ := h
      rw [c1, loadHolds_unique l0 (hL _ hm2)]
    | some vs =>
      simp only [two, ↓reduceIte]
      refine ⟨_, _, _, rfl, fun h ↦ ?_⟩
      simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.nil_append] at h
      rw [h, hL.2 _ hm2]

/-- **One level of `novel_eval`** from output `M - f` on: its outputs are `nvPair`'s from there. -/
theorem osNovelLevel_sound {hp ho w : ℕ} {ins : Option (List ℕ)} {L : List E}
    (hL : NvIns rd σ hp ho L ins) :
    ∀ (f k : ℕ), f ≤ (L.length + 1) / 2 →
      AllOk C rd σ (osNovelLevel hp ho ins L.length w f k).1 →
      (osNovelLevel hp ho ins L.length w f k).2.1.length = f ∧
        ∀ j < f, σ (.n ((osNovelLevel hp ho ins L.length w f k).2.1.getD j 0)) =
          (nvPair (σ (.n w)) L).getD ((L.length + 1) / 2 - f + j) 0
  | 0, k, _, _ => by simp [osNovelLevel]
  | f + 1, k, hf, hok => by
    obtain ⟨ss, o, k', he, ho⟩ := osNovelLevel_step (C := C) (w := w) hL f k hf
    rw [he] at hok ⊢
    rw [allOk_append] at hok
    obtain ⟨hs, hr⟩ := osNovelLevel_sound hL f k' (by omega) hok.2
    refine ⟨by simp [hs], fun j hj ↦ ?_⟩
    rcases j with _ | j
    · simpa using ho hok.1
    · rw [List.getD_cons_succ, hr j (by omega)]
      congr 1
      omega

/-- `nvTree` reads `ws` at its levels only. -/
theorem nvTree_congr {W W' : ℕ → E} : ∀ (f i : ℕ) (l : List E),
    (∀ j, i ≤ j → j < i + f → W j = W' j) → nvTree W f i l = nvTree W' f i l
  | 0, _, _, _ => rfl
  | f + 1, i, l, h => by
    rw [nvTree, nvTree, h i le_rfl (by omega)]
    exact nvTree_congr f (i + 1) _ fun j h1 h2 ↦ h j (by omega) (by omega)

theorem novelSum_congr {W W' : ℕ → E} (hs : List E) (n nbits : ℕ) (h : ∀ j < nbits, W j = W' j) :
    novelSum hs W n nbits = novelSum hs W' n nbits := by
  rw [novelSum, novelSum, nvTree_congr nbits 0 _ fun j _ h2 ↦ h j (by omega)]

theorem ceil_div_two_pow (n i : ℕ) :
    ((n + 2 ^ i - 1) / 2 ^ i + 1) / 2 = (n + 2 ^ (i + 1) - 1) / 2 ^ (i + 1) := by
  have h1 := Nat.one_le_two_pow (n := i)
  rw [pow_succ, ← Nat.div_div_eq_div_mul,
    show n + 2 ^ i * 2 - 1 = n + 2 ^ i - 1 + 2 ^ i * 1 by omega,
    Nat.add_mul_div_left _ _ (by omega)]

/-- **`novel_eval`'s levels** from level `i`, their input `L`: the result is `nvTree`'s. -/
theorem osNovelLevels_sound {hp ho n nbits : ℕ} {ws : List ℕ} : ∀ (f i : ℕ) (ins : Option (List ℕ))
    (L : List E) (k : ℕ), NvIns rd σ hp ho L ins → L.length = (n + 2 ^ i - 1) / 2 ^ i →
      1 ≤ L.length → (ins = none → 1 ≤ f) →
      AllOk C rd σ (osNovelLevels hp ho n nbits ws f i ins k).1 →
      σ (.n (osNovelLevels hp ho n nbits ws f i ins k).2.1) =
        (nvTree (fun j ↦ σ (.n (ws.getD j 0))) f i L).headD 0
  | 0, i, ins, L, k, hL, _, h1, hf, _ => by
    cases ins with
    | none => exact absurd (hf rfl) (by omega)
    | some vs =>
      simp only [osNovelLevels, Option.getD_some, nvTree]
      obtain ⟨hlen, hv⟩ := hL
      rw [List.headD_eq_getD, List.headD_eq_getD, hv 0 h1]
  | f + 1, i, ins, L, k, hL, hlen, h1, _, hok => by
    simp only [osNovelLevels] at hok ⊢
    rw [← hlen] at hok ⊢
    rw [allOk_append] at hok
    have hl := osNovelLevel_sound (C := C) (w := ws.getD i 0) hL ((L.length + 1) / 2) k le_rfl hok.1
    rw [Nat.sub_self] at hl
    have hL' : NvIns rd σ hp ho (nvPair (σ (.n (ws.getD i 0))) L)
        (some (osNovelLevel hp ho ins L.length (ws.getD i 0) ((L.length + 1) / 2) k).2.1) :=
      ⟨by rw [hl.1, length_nvPair], fun j hj ↦ by
        rw [length_nvPair] at hj
        rw [hl.2 j hj, Nat.zero_add]⟩
    rw [osNovelLevels_sound f (i + 1) _ _ _ hL' (by rw [length_nvPair, hlen, ceil_div_two_pow])
      (by rw [length_nvPair]; omega) (by simp) hok.2, nvTree]

/-- **`novel_eval`** of the `nhs ≥ 1` coefficients `hsv` at `hp·g^(ho + ·)` over the values `ws`. -/
theorem osNovelEval_sound {hp ho nhs nbits : ℕ} {ws : List ℕ} {k : ℕ} {hsv : List E}
    (hn : 1 ≤ nhs) (hlen : hsv.length = nhs)
    (hload : ∀ c < nhs, LoadHolds rd (σ (.n hp)) (ho + c) (hsv.getD c 0))
    (hok : AllOk C rd σ (osNovelEval hp ho nhs nbits ws k).1) :
    σ (.n (osNovelEval hp ho nhs nbits ws k).2.1) =
      novelSum hsv (fun j ↦ σ (.n (ws.getD j 0))) nhs nbits := by
  have htake : (hsv.take nhs).length = nhs := by simp [hlen]
  have hL : NvIns rd σ hp ho (hsv.take nhs) none := fun i hi ↦ by
    rw [htake] at hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi, ← List.getD_eq_getElem?_getD]
    exact hload i hi
  unfold osNovelEval at hok ⊢
  by_cases h0 : nbits = 0
  · subst h0
    simp only [↓reduceIte, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hok ⊢
    rw [novelSum, nvTree, List.headD_eq_getD]
    have := hL 0 (by omega)
    rw [Nat.add_zero] at this
    exact loadHolds_unique hok this
  · simp only [h0, ↓reduceIte] at hok ⊢
    rw [novelSum]
    exact osNovelLevels_sound nbits 0 none _ k hL (by simp [htake]) (by omega)
      (fun _ ↦ by omega) hok

/-! ## `residual_query` -/

/-- **The inline `residual_query`** over `ncols ≥ 1` coordinates from the position `x = σ pos`,
the row's words `D t` at `bd·g^(ro + t)` and the high coefficients `hsv` at `hp·g^(ho + ·)`: the
product is `Π_(t < ncols) (D t + chain_t)` and the share is `chain_ncols` times `novelSum` of `hsv`
over the chain. -/
theorem osResQuery_val {pos bd ro hp ho vo ncols nhs hbits k : ℕ} (hn : 1 ≤ ncols) (hh : 1 ≤ nhs)
    (hb3 : hbits ≤ 3) (hbn : hbits ≤ ncols + 1) {D : ℕ → E} {hsv : List E}
    (hD : ∀ s < ncols, LoadHolds rd (σ (.n bd)) (ro + s) (D s)) (hlen : hsv.length = nhs)
    (hload : ∀ c < nhs, LoadHolds rd (σ (.n hp)) (ho + c) (hsv.getD c 0))
    (hok : AllOk C rd σ (osResQuery pos bd ro hp ho vo ncols nhs hbits k).1) :
    σ (.n (osResQuery pos bd ro hp ho vo ncols nhs hbits k).2.1) =
        residualProd (osVals vo ncols) (σ (.n pos)) D ncols ∧
      σ (.n (osResQuery pos bd ro hp ho vo ncols nhs hbits k).2.2.1) =
        residualChain (osVals vo ncols) (σ (.n pos)) ncols *
          novelSum hsv (residualChain (osVals vo ncols) (σ (.n pos))) nhs hbits := by
  simp only [osResQuery] at hok ⊢
  simp only [allOk_append, allOk_cons, allOk_nil, and_true] at hok
  obtain ⟨⟨⟨⟨c0, l1, a2⟩, hc⟩, hne⟩, hm⟩ := hok
  simp only [StmtOk, Atom.Holds] at c0 l1 a2 hm
  have hd0 : σ (.n (k + 1)) = D 0 := loadHolds_unique l1 (by simpa using hD 0 hn)
  obtain ⟨hch, hpr, hwl, hws⟩ := osResChain_sound (C := C) (x := σ (.n pos)) (vo := vo) hD ncols 1 pos
    (k + 2) [k] (k + 3) le_rfl (by omega) (by simp [residualChain])
    (by rw [min_eq_left hn, a2, hd0]; simp [residualProd, residualChain]) (by simp)
    (fun i hi ↦ by
      obtain rfl : i = 0 := by simpa using hi
      simp [c0, residualChain]) hc
  refine ⟨hpr, ?_⟩
  rw [hm, osNovelEval_sound hh hlen hload hne, hch]
  congr 1
  exact novelSum_congr _ _ _ fun j hj ↦ hws j (by rw [hwl]; omega)

end
end LeanVM.Guest.B1.Whir
