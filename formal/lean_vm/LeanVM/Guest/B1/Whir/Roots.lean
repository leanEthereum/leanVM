/-
  LeanVM.Guest.B1.Whir.Roots

  The subspace roots in `K`, and the vanishing tables checked against them.
-/

module

public import LeanVM.Guest.B1.Whir.InnerSpec

/-!
# The vanishing tables (`LIG_VANISH_VALS`, `LIG_VANISH_INVS`)

`subspaceRoots` (V:1709) lies in `K` (`subspaceRoots_ofK`: it is `kRoots` embedded), so the
tables are checked against it by computing in `K` (`vanishOk`, decided by the kernel per level);
`vanish_val`, `vanish_inv` give the facts `inner_eq` takes.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-- `subspaceRootsAux` in `K`. -/
def kRootsAux : ℕ → K → List K → List K
  | 0, _, _ => []
  | n + 1, last, layer =>
    match layer.map fun value ↦ value ^ 2 + last * value with
    | [] => []
    | root :: rest => root :: kRootsAux n root rest

/-- `subspaceRoots` in `K`. -/
def kRoots (logN : ℕ) : List K :=
  1 :: kRootsAux logN 1 ((List.range logN).map fun i ↦ K.ofBits (2 ^ (i + 1)))

theorem ofK_add' (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

theorem ofK_mul' (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

theorem subspaceRootsAux_ofK : ∀ (n : ℕ) (last : K) (layer : List K),
    subspaceRootsAux n (ofK last) (layer.map ofK) = (kRootsAux n last layer).map ofK
  | 0, _, _ => rfl
  | n + 1, last, layer => by
    have e : (layer.map ofK).map (fun value ↦ value ^ 2 + ofK last * value) =
        (layer.map fun value ↦ value ^ 2 + last * value).map ofK := by
      simp only [List.map_map]
      refine List.map_congr_left fun u _ ↦ ?_
      simp only [Function.comp_apply, ofK_add', ofK_mul', ofK_pow]
    simp only [subspaceRootsAux, kRootsAux, e]
    cases layer.map fun value ↦ value ^ 2 + last * value with
    | nil => rfl
    | cons root rest =>
      simp only [List.map_cons, subspaceRootsAux_ofK n root rest]

theorem subspaceRoots_ofK (n : ℕ) : subspaceRoots n = (kRoots n).map ofK := by
  have e : (List.range n).map (fun i ↦ eOfNat (2 ^ (i + 1))) =
      ((List.range n).map fun i ↦ K.ofBits (2 ^ (i + 1))).map ofK := by
    simp only [List.map_map]; rfl
  rw [subspaceRoots, kRoots, e, ← ofK_one, subspaceRootsAux_ofK, List.map_cons]

/-- A level's vanishing tables, checked in `K`: the values are the roots, the inverses theirs. -/
def vanishOk (vo ml : ℕ) : Bool :=
  ((List.range ml).map fun t ↦ K.ofBits (vanishVal (vo + t))) == (kRoots ml).take ml &&
    (List.range ml).all fun t ↦ K.ofBits (vanishInv (vo + t)) * K.ofBits (vanishVal (vo + t)) == 1

theorem vanish_val {vo ml : ℕ} (h : vanishOk vo ml = true) :
    ∀ t < ml, word (vanishVal (vo + t)) 0 0 = (subspaceRoots ml).getD t 0 := by
  intro t ht
  simp only [vanishOk, Bool.and_eq_true, beq_iff_eq] at h
  have h1 := congrArg (fun l ↦ l.getD t 0) h.1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht,
    Option.map_some, Option.getD_some, List.getElem?_take, ht, ↓reduceIte] at h1
  rw [word_eOfNat, eOfNat, h1, subspaceRoots_ofK, List.getD_eq_getElem?_getD,
    List.getElem?_map]
  cases (kRoots ml)[t]? <;> simp

theorem vanish_inv {vo ml : ℕ} (h : vanishOk vo ml = true) :
    ∀ t < ml, word (vanishInv (vo + t)) 0 0 = (invsOf ml).getD t 0 ∧
      word (vanishInv (vo + t)) 0 0 ≠ 0 := by
  intro t ht
  have hv := vanish_val h t ht
  simp only [vanishOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hm := h.2 t ht
  have hm' : word (vanishInv (vo + t)) 0 0 * word (vanishVal (vo + t)) 0 0 = 1 := by
    rw [word_eOfNat, word_eOfNat, eOfNat, eOfNat, ← ofK_mul', hm, ofK_one]
  have hne : word (vanishVal (vo + t)) 0 0 ≠ 0 := right_ne_zero_of_mul_eq_one hm'
  refine ⟨?_, left_ne_zero_of_mul_eq_one hm'⟩
  have hl : t < (subspaceRoots ml).length := by
    rw [subspaceRoots_ofK, List.length_map]
    have : (kRoots ml).take ml = (List.range ml).map fun t ↦ K.ofBits (vanishVal (vo + t)) :=
      h.1.symm
    have hlen := congrArg List.length this
    simp only [List.length_take, List.length_map, List.length_range] at hlen
    omega
  rw [invsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl,
    Option.map_some, Option.getD_some]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some] at hv
  rw [← hv]
  simp only [hne, ↓reduceIte]
  exact (eq_inv_of_mul_eq_one_left hm')

end
end LeanVM.Guest.B1.Whir
