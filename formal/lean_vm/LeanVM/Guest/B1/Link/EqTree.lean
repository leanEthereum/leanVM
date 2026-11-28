/-
  LeanVM.Guest.B1.Link.EqTree

  The expansion of the guest's inline `eqtree`: the equality kernel of a point, built by doubling
  into a heap run.
-/

module

public import LeanVM.Guest.B1.Common.Atoms
public import LeanVM.Guest.B1.Common.Basic

/-!
# `eqtree`, at an offset

`eqtree(point_ptr, out, n)` (G) writes `1 + r0`, `r0` at `out[0]`, `out[1]`, then for each
coordinate `t = 1 .. n-1` doubles the previous level (the `2^t` words at `out[2^t - 2 ..]`) by
`1 + r_t` and `r_t` into the next (`out[2^(t+1) - 2 ..]`). The bus era's template
(`B1/Eq/EqTree.lean`, tag `formal-bus-archive`), with the run's offset `oo` that the compiler folds
into the stores where `out` is a buffer's interior (`link_terminal`'s `eqs·g^(step·i)`):

* `eqtreeAt p o po oo b n`: `r0` at `b`, `1 + r0` at `b + 2`; level `t` from `eqtreeS b t`
  (`r_t`, `1 + r_t`, then three values per word of the previous level).
* `eqtreeAt_sound`: with the point's words `rs` at `p` from `po`, level `t ≤ n` holds
  `eqKernel (rs.take t)` at `out[oo + 2^t - 2 ..]`, in particular the last level.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The first value of level `t ≥ 1`. -/
def eqtreeS (b t : ℕ) : ℕ := b + 3 * t + 3 * 2 ^ t - 6

/-- Word `i` of level `t ≥ 1`: the previous level's word `i` doubled. -/
def eqtreeWordAt (o : V) (oo S t i : ℕ) : List Stmt :=
  let P := S + 3 + 3 * i
  [.atom (.load (.n P) o (oo + (2 ^ t - 2 + i))), .atom (.mul (.n (P + 1)) (.n P) (.n (S + 2))),
    .atom (.load (.n (P + 1)) o (oo + (2 ^ (t + 1) - 2 + i))), .atom (.mul (.n (P + 2)) (.n P) (.n S)),
    .atom (.load (.n (P + 2)) o (oo + (2 ^ (t + 1) - 2 + 2 ^ t + i)))]

/-- Level `t ≥ 1`. -/
def eqtreeLevelAt (p o : V) (po oo b t : ℕ) : List Stmt :=
  [.atom (.load (.n (eqtreeS b t)) p (po + t)), .atom (.const (.n (eqtreeS b t + 1)) (word 1 0)),
    .atom (.add (.n (eqtreeS b t + 2)) (.n (eqtreeS b t + 1)) (.n (eqtreeS b t)))] ++
    ((List.range (2 ^ t)).map (eqtreeWordAt o oo (eqtreeS b t) t)).flatten

/-- **`eqtree(point, out, n)`** from the value `b`. -/
def eqtreeAt (p o : V) (po oo b n : ℕ) : List Stmt :=
  [.atom (.load (.n b) p po), .atom (.const (.n (b + 1)) (word 1 0)),
    .atom (.add (.n (b + 2)) (.n (b + 1)) (.n b)), .atom (.load (.n (b + 2)) o oo),
    .atom (.load (.n b) o (oo + 1))] ++
    ((List.range (n - 1)).map fun t ↦ eqtreeLevelAt p o po oo b (t + 1)).flatten

theorem eqtreeAt_atoms (p o : V) (po oo b n : ℕ) : AllAtoms (eqtreeAt p o po oo b n) := by
  unfold eqtreeAt
  refine allAtoms_append ?_ (allAtoms_map_flatten fun t _ => ?_)
  · exact allAtoms_cons (allAtoms_cons (allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil))))
  · unfold eqtreeLevelAt
    refine allAtoms_append (allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil)))
      (allAtoms_map_flatten fun i _ => ?_)
    exact allAtoms_cons (allAtoms_cons (allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil))))

theorem eqKernel_snoc' (pt : List E) (r : E) :
    eqKernel (pt ++ [r]) = (eqKernel pt).map (· * (1 + r)) ++ (eqKernel pt).map (· * r) := by
  unfold eqKernel
  rw [List.foldl_concat]

theorem getD_map_mul_eq' (l : List E) (c : E) (w : ℕ) :
    (l.map (· * c)).getD w 0 = l.getD w 0 * c := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[w]? <;> simp

theorem length_eqKernel_eq' (pt : List E) : (eqKernel pt).length = 2 ^ pt.length := by
  induction pt using List.reverseRecOn with
  | nil => rfl
  | append_singleton pt r ih =>
    rw [eqKernel_snoc', List.length_append, List.length_map, List.length_map, ih,
      List.length_append, List.length_singleton, pow_succ]
    ring

/-- **`eqtree`**: with the point's words `rs` (`n ≥ 1` of them) at `p` from `po`,
level `t`, `1 ≤ t ≤ n`, of the run at `o` is `eqKernel (rs.take t)`. -/
theorem eqtreeAt_sound {p o : V} {po oo b n : ℕ} (hn : 1 ≤ n)
    (hA : ∀ a, Stmt.atom a ∈ eqtreeAt p o po oo b n → a.Holds rd σ) {rs : List E}
    (hrs : rs.length = n) (hpt : ∀ t < n, LoadHolds rd (σ p) (po + t) (rs.getD t 0)) :
    ∀ t, 1 ≤ t → t ≤ n → ∀ i < 2 ^ t,
      LoadHolds rd (σ o) (oo + (2 ^ t - 2 + i)) ((eqKernel (rs.take t)).getD i 0) := by
  intro t ht1 htn
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · -- level 1: `1 + r0`, `r0`
      have a0 := hA _ (by simp [eqtreeAt] : Stmt.atom (.load (.n b) p po) ∈ _)
      have a1 := hA _ (by simp [eqtreeAt] : Stmt.atom (.const (.n (b + 1)) (word 1 0)) ∈ _)
      have a2 := hA _ (by simp [eqtreeAt] : Stmt.atom (.add (.n (b + 2)) (.n (b + 1)) (.n b)) ∈ _)
      have a3 := hA _ (by simp [eqtreeAt] : Stmt.atom (.load (.n (b + 2)) o oo) ∈ _)
      have a4 := hA _ (by simp [eqtreeAt] : Stmt.atom (.load (.n b) o (oo + 1)) ∈ _)
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
      have memL : ∀ a, Stmt.atom a ∈ eqtreeLevelAt p o po oo b t → a.Holds rd σ := fun a ha =>
        hA a (by
          unfold eqtreeAt
          refine List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr
            ⟨t - 1, List.mem_range.mpr (by omega), ?_⟩, ha⟩)
          rw [Nat.sub_add_cancel (by omega)])
      set S := eqtreeS b t with hS
      have l0 := memL _ (by simp [eqtreeLevelAt, ← hS] : Stmt.atom (.load (.n S) p (po + t)) ∈ _)
      have l1 := memL _ (by simp [eqtreeLevelAt, ← hS] : Stmt.atom (.const (.n (S + 1)) (word 1 0)) ∈ _)
      have l2 := memL _ (by simp [eqtreeLevelAt, ← hS] :
        Stmt.atom (.add (.n (S + 2)) (.n (S + 1)) (.n S)) ∈ _)
      simp only [Atom.Holds] at l1 l2
      have hrt : σ (.n S) = rs.getD t 0 := loadHolds_unique l0 (hpt t (by omega))
      have hrt1 : σ (.n (S + 2)) = 1 + rs.getD t 0 := by rw [l2, l1, word_one, hrt]
      have hprev := ih (by omega) (by omega)
      have htake : rs.take (t + 1) = rs.take t ++ [rs.getD t 0] := by
        rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        simp
      have hlen : (eqKernel (rs.take t)).length = 2 ^ t := by
        rw [length_eqKernel_eq']; simp [hrs]; omega
      intro i hi
      rw [htake, eqKernel_snoc']
      have word := fun j (hj : j < 2 ^ t) (a : Atom) (ha : Stmt.atom a ∈ eqtreeWordAt o oo S t j) =>
        memL a (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr
          ⟨j, List.mem_range.mpr hj, rfl⟩, ha⟩))
      by_cases hlo : i < 2 ^ t
      · have w0 := word i hlo _ (by simp [eqtreeWordAt] : Stmt.atom (.load (.n (S + 3 + 3 * i)) o
          (oo + (2 ^ t - 2 + i))) ∈ _)
        have w1 := word i hlo _ (by simp [eqtreeWordAt] : Stmt.atom (.mul (.n (S + 3 + 3 * i + 1))
          (.n (S + 3 + 3 * i)) (.n (S + 2))) ∈ _)
        have w2 := word i hlo _ (by simp [eqtreeWordAt] : Stmt.atom (.load (.n (S + 3 + 3 * i + 1)) o
          (oo + (2 ^ (t + 1) - 2 + i))) ∈ _)
        simp only [Atom.Holds] at w1
        have e := loadHolds_unique w0 (hprev i hlo)
        rw [List.getD_append _ _ _ _ (by rw [List.length_map, hlen]; exact hlo), getD_map_mul_eq',
          ← e, ← hrt1, ← w1]
        exact w2
      · obtain ⟨j, hj, rfl⟩ : ∃ j < 2 ^ t, i = 2 ^ t + j := ⟨i - 2 ^ t, by rw [pow_succ] at hi; omega, by omega⟩
        have w0 := word j hj _ (by simp [eqtreeWordAt] : Stmt.atom (.load (.n (S + 3 + 3 * j)) o
          (oo + (2 ^ t - 2 + j))) ∈ _)
        have w3 := word j hj _ (by simp [eqtreeWordAt] : Stmt.atom (.mul (.n (S + 3 + 3 * j + 2))
          (.n (S + 3 + 3 * j)) (.n S)) ∈ _)
        have w4 := word j hj _ (by simp [eqtreeWordAt] : Stmt.atom (.load (.n (S + 3 + 3 * j + 2)) o
          (oo + (2 ^ (t + 1) - 2 + 2 ^ t + j))) ∈ _)
        simp only [Atom.Holds] at w3
        have e := loadHolds_unique w0 (hprev j hj)
        rw [List.getD_append_right _ _ _ _ (by rw [List.length_map, hlen]; omega), List.length_map,
          hlen, Nat.add_sub_cancel_left, getD_map_mul_eq', ← e, ← hrt, ← w3,
          show oo + (2 ^ (t + 1) - 2 + (2 ^ t + j)) = oo + (2 ^ (t + 1) - 2 + 2 ^ t + j) by omega]
        exact w4

