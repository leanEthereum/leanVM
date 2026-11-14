/-
  LeanVM.Guest.B1.Eq.EqTree

  The expansion of the guest's inline `eqtree`: the equality kernel of a point, built by doubling
  into a heap run.
-/

module

public import LeanVM.Guest.B1.Common.Atoms

/-!
# `eqtree` (G:954-968, TRIAGE #23)

`eqtree(point_ptr, out, n)` writes `1 + r0`, `r0` at `out[0]`, `out[1]`, then for each coordinate
`t = 1 .. n-1` doubles the previous level (the `2^t` words at `out[2^t - 2 ..]`) by `1 + r_t` and
`r_t` into the next (`out[2^(t+1) - 2 ..]`). Its expansion from the value `b`, the point read at
`p` from the offset `po` (`verify_keccak`, G:2929-2998, numbers it):

* `eqtreeT p o po b n`: `r0` at `b`, `1 + r0` at `b + 2`; level `t` from `eqtreeS b t`
  (`r_t`, `1 + r_t`, then five values per word of the previous level).
* `eqtree_sound`: with the point's words `rs` at `p` from `po`, level `t ≤ n` holds
  `eqKernel (rs.take t)` at `out[2^t - 2 ..]` (`eqKernel`, V:642), in particular the last level.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The first value of level `t ≥ 1`. -/
def eqtreeS (b t : ℕ) : ℕ := b + 3 * t + 3 * 2 ^ t - 6

/-- Word `i` of level `t ≥ 1`: the previous level's word `i` doubled. -/
def eqtreeWordT (o : V) (S t i : ℕ) : List Stmt :=
  let P := S + 3 + 3 * i
  [.atom (.load (.n P) o (2 ^ t - 2 + i)), .atom (.mul (.n (P + 1)) (.n P) (.n (S + 2))),
    .atom (.load (.n (P + 1)) o (2 ^ (t + 1) - 2 + i)), .atom (.mul (.n (P + 2)) (.n P) (.n S)),
    .atom (.load (.n (P + 2)) o (2 ^ (t + 1) - 2 + 2 ^ t + i))]

/-- Level `t ≥ 1`. -/
def eqtreeLevelT (p o : V) (po b t : ℕ) : List Stmt :=
  [.atom (.load (.n (eqtreeS b t)) p (po + t)), .atom (.const (.n (eqtreeS b t + 1)) (word 1 0)),
    .atom (.add (.n (eqtreeS b t + 2)) (.n (eqtreeS b t + 1)) (.n (eqtreeS b t)))] ++
    ((List.range (2 ^ t)).map (eqtreeWordT o (eqtreeS b t) t)).flatten

/-- **`eqtree(point, out, n)`** from the value `b`. -/
def eqtreeT (p o : V) (po b n : ℕ) : List Stmt :=
  [.atom (.load (.n b) p po), .atom (.const (.n (b + 1)) (word 1 0)),
    .atom (.add (.n (b + 2)) (.n (b + 1)) (.n b)), .atom (.load (.n (b + 2)) o 0),
    .atom (.load (.n b) o 1)] ++
    ((List.range (n - 1)).map fun t ↦ eqtreeLevelT p o po b (t + 1)).flatten

theorem eqtreeT_atoms (p o : V) (po b n : ℕ) : AllAtoms (eqtreeT p o po b n) := by
  unfold eqtreeT
  refine allAtoms_append ?_ (allAtoms_map_flatten fun t _ => ?_)
  · exact allAtoms_cons (allAtoms_cons (allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil))))
  · unfold eqtreeLevelT
    refine allAtoms_append (allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil)))
      (allAtoms_map_flatten fun i _ => ?_)
    exact allAtoms_cons (allAtoms_cons (allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil))))

theorem eqKernel_snoc (pt : List E) (r : E) :
    eqKernel (pt ++ [r]) = (eqKernel pt).map (· * (1 + r)) ++ (eqKernel pt).map (· * r) := by
  unfold eqKernel
  rw [List.foldl_concat]

theorem getD_map_mul_eq (l : List E) (c : E) (w : ℕ) :
    (l.map (· * c)).getD w 0 = l.getD w 0 * c := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[w]? <;> simp

theorem length_eqKernel_eq (pt : List E) : (eqKernel pt).length = 2 ^ pt.length := by
  induction pt using List.reverseRecOn with
  | nil => rfl
  | append_singleton pt r ih =>
    rw [eqKernel_snoc, List.length_append, List.length_map, List.length_map, ih,
      List.length_append, List.length_singleton, pow_succ]
    ring

/-- **`eqtree`** (G:954-968): with the point's words `rs` (`n ≥ 1` of them) at `p` from `po`,
level `t`, `1 ≤ t ≤ n`, of the run at `o` is `eqKernel (rs.take t)`. -/
theorem eqtree_sound {p o : V} {po b n : ℕ} (hn : 1 ≤ n)
    (hA : ∀ a, Stmt.atom a ∈ eqtreeT p o po b n → a.Holds rd σ) {rs : List E}
    (hrs : rs.length = n) (hpt : ∀ t < n, LoadHolds rd (σ p) (po + t) (rs.getD t 0)) :
    ∀ t, 1 ≤ t → t ≤ n → ∀ i < 2 ^ t,
      LoadHolds rd (σ o) (2 ^ t - 2 + i) ((eqKernel (rs.take t)).getD i 0) := by
  intro t ht1 htn
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · -- level 1: `1 + r0`, `r0`
      have a0 := hA _ (by simp [eqtreeT] : Stmt.atom (.load (.n b) p po) ∈ _)
      have a1 := hA _ (by simp [eqtreeT] : Stmt.atom (.const (.n (b + 1)) (word 1 0)) ∈ _)
      have a2 := hA _ (by simp [eqtreeT] : Stmt.atom (.add (.n (b + 2)) (.n (b + 1)) (.n b)) ∈ _)
      have a3 := hA _ (by simp [eqtreeT] : Stmt.atom (.load (.n (b + 2)) o 0) ∈ _)
      have a4 := hA _ (by simp [eqtreeT] : Stmt.atom (.load (.n b) o 1) ∈ _)
      simp only [Atom.Holds] at a1 a2 a3 a4
      have hr0 : σ (.n b) = rs.getD 0 0 := loadHolds_unique a0 (by simpa using hpt 0 hn)
      rcases rs with _ | ⟨r0, rest⟩
      · simp at hrs; omega
      simp only [List.getD_cons_zero] at hr0
      have h2 : σ (.n (b + 2)) = 1 + r0 := by rw [a2, a1, word_one, hr0]
      intro i hi
      have hk : eqKernel ((r0 :: rest).take (0 + 1)) = [1 + r0, r0] := by
        simp [eqKernel]
      rw [hk]
      interval_cases i
      · rw [h2] at a3; simpa using a3
      · rw [hr0] at a4; simpa using a4
    · -- level `t + 1` from level `t` by the template's level `t`
      have memL : ∀ a, Stmt.atom a ∈ eqtreeLevelT p o po b t → a.Holds rd σ := fun a ha =>
        hA a (by
          unfold eqtreeT
          refine List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr
            ⟨t - 1, List.mem_range.mpr (by omega), ?_⟩, ha⟩)
          rw [Nat.sub_add_cancel (by omega)])
      set S := eqtreeS b t with hS
      have l0 := memL _ (by simp [eqtreeLevelT, ← hS] : Stmt.atom (.load (.n S) p (po + t)) ∈ _)
      have l1 := memL _ (by simp [eqtreeLevelT, ← hS] : Stmt.atom (.const (.n (S + 1)) (word 1 0)) ∈ _)
      have l2 := memL _ (by simp [eqtreeLevelT, ← hS] :
        Stmt.atom (.add (.n (S + 2)) (.n (S + 1)) (.n S)) ∈ _)
      simp only [Atom.Holds] at l1 l2
      have hrt : σ (.n S) = rs.getD t 0 := loadHolds_unique l0 (hpt t (by omega))
      have hrt1 : σ (.n (S + 2)) = 1 + rs.getD t 0 := by rw [l2, l1, word_one, hrt]
      have hprev := ih (by omega) (by omega)
      have htake : rs.take (t + 1) = rs.take t ++ [rs.getD t 0] := by
        rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        simp
      have hlen : (eqKernel (rs.take t)).length = 2 ^ t := by
        rw [length_eqKernel_eq]; simp [hrs]; omega
      intro i hi
      rw [htake, eqKernel_snoc]
      have word := fun j (hj : j < 2 ^ t) (a : Atom) (ha : Stmt.atom a ∈ eqtreeWordT o S t j) =>
        memL a (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr
          ⟨j, List.mem_range.mpr hj, rfl⟩, ha⟩))
      by_cases hlo : i < 2 ^ t
      · have w0 := word i hlo _ (by simp [eqtreeWordT] : Stmt.atom (.load (.n (S + 3 + 3 * i)) o
          (2 ^ t - 2 + i)) ∈ _)
        have w1 := word i hlo _ (by simp [eqtreeWordT] : Stmt.atom (.mul (.n (S + 3 + 3 * i + 1))
          (.n (S + 3 + 3 * i)) (.n (S + 2))) ∈ _)
        have w2 := word i hlo _ (by simp [eqtreeWordT] : Stmt.atom (.load (.n (S + 3 + 3 * i + 1)) o
          (2 ^ (t + 1) - 2 + i)) ∈ _)
        simp only [Atom.Holds] at w1
        have e := loadHolds_unique w0 (hprev i hlo)
        rw [List.getD_append _ _ _ _ (by rw [List.length_map, hlen]; exact hlo), getD_map_mul_eq,
          ← e, ← hrt1, ← w1]
        exact w2
      · obtain ⟨j, hj, rfl⟩ : ∃ j < 2 ^ t, i = 2 ^ t + j := ⟨i - 2 ^ t, by rw [pow_succ] at hi; omega, by omega⟩
        have w0 := word j hj _ (by simp [eqtreeWordT] : Stmt.atom (.load (.n (S + 3 + 3 * j)) o
          (2 ^ t - 2 + j)) ∈ _)
        have w3 := word j hj _ (by simp [eqtreeWordT] : Stmt.atom (.mul (.n (S + 3 + 3 * j + 2))
          (.n (S + 3 + 3 * j)) (.n S)) ∈ _)
        have w4 := word j hj _ (by simp [eqtreeWordT] : Stmt.atom (.load (.n (S + 3 + 3 * j + 2)) o
          (2 ^ (t + 1) - 2 + 2 ^ t + j)) ∈ _)
        simp only [Atom.Holds] at w3
        have e := loadHolds_unique w0 (hprev j hj)
        rw [List.getD_append_right _ _ _ _ (by rw [List.length_map, hlen]; omega), List.length_map,
          hlen, Nat.add_sub_cancel_left, getD_map_mul_eq, ← e, ← hrt, ← w3,
          show 2 ^ (t + 1) - 2 + (2 ^ t + j) = 2 ^ (t + 1) - 2 + 2 ^ t + j by omega]
        exact w4

/-! ## The honest values -/

/-- The honest value at offset `o` of level `t ≥ 1`'s block: `r_t`, `1`, `1 + r_t`, then per word
`e`, `e·(1 + r_t)`, `e·r_t`, `e` entry `i` of `eqKernel (rs.take t)`. -/
def eqtreeLvlVal (rs : List E) (t o : ℕ) : E :=
  if o = 0 then rs.getD t 0 else if o = 1 then 1 else if o = 2 then 1 + rs.getD t 0
  else
    let e := (eqKernel (rs.take t)).getD ((o - 3) / 3) 0
    if (o - 3) % 3 = 0 then e else if (o - 3) % 3 = 1 then e * (1 + rs.getD t 0)
    else e * rs.getD t 0

theorem eqtreeLvlVal_word (rs : List E) (t i j : ℕ) (hj : j < 3) :
    eqtreeLvlVal rs t (3 + 3 * i + j) =
      [(eqKernel (rs.take t)).getD i 0, (eqKernel (rs.take t)).getD i 0 * (1 + rs.getD t 0),
        (eqKernel (rs.take t)).getD i 0 * rs.getD t 0].getD j 0 := by
  have e1 : (3 + 3 * i + j - 3) / 3 = i := by omega
  have e2 : (3 + 3 * i + j - 3) % 3 = j := by omega
  simp only [eqtreeLvlVal, show ¬ 3 + 3 * i + j = 0 by omega, show ¬ 3 + 3 * i + j = 1 by omega,
    show ¬ 3 + 3 * i + j = 2 by omega, ↓reduceIte, e1, e2]
  interval_cases j <;> simp

/-- The honest valuation of `eqtreeT … b n` over `σ`, through level `m`. -/
def eqtreeSig (σ : Val) (rs : List E) (b : ℕ) : ℕ → Val
  | 0 => setv σ b 3 fun o ↦ [rs.getD 0 0, 1, 1 + rs.getD 0 0].getD o 0
  | m + 1 => setv (eqtreeSig σ rs b m) (eqtreeS b (m + 1)) (3 + 3 * 2 ^ (m + 1))
      (eqtreeLvlVal rs (m + 1))

/-- **The honest values satisfy `eqtree`**: with the point's words at `p`, the run `o` holding
every level's `eqKernel` entries, and the template's values those of `eqtreeSig`. -/
theorem eqtreeT_complete {p o : V} {po b n : ℕ} (hn : 1 ≤ n) {rs : List E} (hrs : rs.length = n)
    (hpt : ∀ t < n, LoadHolds rd (σ p) (po + t) (rs.getD t 0))
    (hout : ∀ t, 1 ≤ t → t ≤ n → ∀ i < 2 ^ t,
      LoadHolds rd (σ o) (2 ^ t - 2 + i) ((eqKernel (rs.take t)).getD i 0))
    (hhead : ∀ k < 3, σ (.n (b + k)) = [rs.getD 0 0, 1, 1 + rs.getD 0 0].getD k 0)
    (hlvl : ∀ t, 1 ≤ t → t < n → ∀ k < 3 + 3 * 2 ^ t,
      σ (.n (eqtreeS b t + k)) = eqtreeLvlVal rs t k) :
    ∀ a, Stmt.atom a ∈ eqtreeT p o po b n → a.Holds rd σ := by
  intro a ha
  have h0 : σ (.n b) = rs.getD 0 0 := hhead 0 (by omega)
  have h1 : σ (.n (b + 1)) = 1 := hhead 1 (by omega)
  have h2 : σ (.n (b + 2)) = 1 + rs.getD 0 0 := hhead 2 (by omega)
  simp only [eqtreeT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatten, List.mem_map, List.mem_range] at ha
  rcases ha with (h | h | h | h | h) | ⟨blk, ⟨t', ht', rfl⟩, hb⟩
  all_goals try (obtain rfl := Stmt.atom.inj h)
  · show LoadHolds rd (σ p) po (σ (.n b)); rw [h0]; simpa using hpt 0 (by omega)
  · show σ (.n (b + 1)) = word 1 0; rw [h1, word_one]
  · show σ (.n (b + 2)) = σ (.n (b + 1)) + σ (.n b); rw [h2, h1, h0]
  · show LoadHolds rd (σ o) 0 (σ (.n (b + 2)))
    have := hout 1 le_rfl hn 0 (by norm_num)
    rcases rs with _ | ⟨r0, rest⟩
    · simp at hrs; omega
    simpa [h2, eqKernel] using this
  · show LoadHolds rd (σ o) 1 (σ (.n b))
    have := hout 1 le_rfl hn 1 (by norm_num)
    rcases rs with _ | ⟨r0, rest⟩
    · simp at hrs; omega
    simpa [h0, eqKernel] using this
  · -- a level
    set t := t' + 1 with ht
    have htn : t < n := by omega
    set S := eqtreeS b t with hS
    have v : ∀ k < 3 + 3 * 2 ^ t, σ (.n (S + k)) = eqtreeLvlVal rs t k := hlvl t (by omega) htn
    have vr : σ (.n S) = rs.getD t 0 := by simpa [eqtreeLvlVal] using v 0 (by omega)
    have v1 : σ (.n (S + 1)) = 1 := by simpa [eqtreeLvlVal] using v 1 (by omega)
    have v2 : σ (.n (S + 2)) = 1 + rs.getD t 0 := by simpa [eqtreeLvlVal] using v 2 (by omega)
    have htake : rs.take (t + 1) = rs.take t ++ [rs.getD t 0] := by
      rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      simp
    have hlen : (eqKernel (rs.take t)).length = 2 ^ t := by
      rw [length_eqKernel_eq]; simp [hrs]; omega
    simp only [eqtreeLevelT, ← hS, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatten, List.mem_map, List.mem_range] at hb
    rcases hb with (h | h | h) | ⟨w, ⟨i, hi, rfl⟩, hw⟩
    all_goals try (obtain rfl := Stmt.atom.inj h)
    · show LoadHolds rd (σ p) (po + t) (σ (.n S)); rw [vr]; exact hpt t htn
    · show σ (.n (S + 1)) = word 1 0; rw [v1, word_one]
    · show σ (.n (S + 2)) = σ (.n (S + 1)) + σ (.n S); rw [v2, v1, vr]
    · have wv : ∀ j < 3, σ (.n (S + 3 + 3 * i + j)) = [(eqKernel (rs.take t)).getD i 0,
          (eqKernel (rs.take t)).getD i 0 * (1 + rs.getD t 0),
          (eqKernel (rs.take t)).getD i 0 * rs.getD t 0].getD j 0 := fun j hj => by
        rw [show S + 3 + 3 * i + j = S + (3 + 3 * i + j) by ring, v _ (by omega),
          eqtreeLvlVal_word rs t i j hj]
      have e0 : σ (.n (S + 3 + 3 * i)) = (eqKernel (rs.take t)).getD i 0 := wv 0 (by omega)
      have e1 : σ (.n (S + 3 + 3 * i + 1)) = (eqKernel (rs.take t)).getD i 0 * (1 + rs.getD t 0) :=
        wv 1 (by omega)
      have e2 : σ (.n (S + 3 + 3 * i + 2)) = (eqKernel (rs.take t)).getD i 0 * rs.getD t 0 :=
        wv 2 (by omega)
      have hlo : (eqKernel (rs.take (t + 1))).getD i 0 =
          (eqKernel (rs.take t)).getD i 0 * (1 + rs.getD t 0) := by
        rw [htake, eqKernel_snoc, List.getD_append _ _ _ _ (by rw [List.length_map, hlen]; exact hi),
          getD_map_mul_eq]
      have hhi : (eqKernel (rs.take (t + 1))).getD (2 ^ t + i) 0 =
          (eqKernel (rs.take t)).getD i 0 * rs.getD t 0 := by
        rw [htake, eqKernel_snoc, List.getD_append_right _ _ _ _ (by rw [List.length_map, hlen]; omega),
          List.length_map, hlen, Nat.add_sub_cancel_left, getD_map_mul_eq]
      simp only [eqtreeWordT, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with h | h | h | h | h <;> obtain rfl := Stmt.atom.inj h
      · show LoadHolds rd (σ o) (2 ^ t - 2 + i) (σ (.n (S + 3 + 3 * i)))
        rw [e0]; exact hout t (by omega) (by omega) i hi
      · show σ (.n (S + 3 + 3 * i + 1)) = σ (.n (S + 3 + 3 * i)) * σ (.n (S + 2))
        rw [e1, e0, v2]
      · show LoadHolds rd (σ o) (2 ^ (t + 1) - 2 + i) (σ (.n (S + 3 + 3 * i + 1)))
        have hp2 : 2 ^ (t + 1) = 2 * 2 ^ t := by ring
        rw [e1, ← hlo]; exact hout (t + 1) (by omega) (by omega) i (by omega)
      · show σ (.n (S + 3 + 3 * i + 2)) = σ (.n (S + 3 + 3 * i)) * σ (.n S)
        rw [e2, e0, vr]
      · show LoadHolds rd (σ o) (2 ^ (t + 1) - 2 + 2 ^ t + i) (σ (.n (S + 3 + 3 * i + 2)))
        rw [e2, ← hhi, Nat.add_assoc]
        have hp2 : 2 ^ (t + 1) = 2 * 2 ^ t := by ring
        exact hout (t + 1) (by omega) (by omega) (2 ^ t + i) (by omega)

end
end LeanVM.Guest.B1
