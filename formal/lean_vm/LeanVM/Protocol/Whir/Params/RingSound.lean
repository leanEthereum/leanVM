/-
  LeanVM.Protocol.Whir.Params.RingSound

  Ring switching's soundness on the stack: the merged claim of two ring claims, paired with a
  stack, is the map of the true merged slices; a false slice survives at a fraction `3/|E|` of the
  challenges.
-/

module

public import LeanVM.Protocol.Whir.Params.RingMerge
public import LeanVM.Protocol.Relation.Bridge
public import LeanVM.Protocol.Relation.Iface
import LeanVM.Protocol.Tables

/-!
# Ring switching, sound

For two ring claims `a`, `b` (the Keccak reduction's and the link's) whose pieces lie on aligned
placements (`PlacedOK`) and whose slices are `64`:

* `pair_flatWeight`: a placed piece's weight paired with the stack is
  `Σ_i x^i Φ(s · ẑ_i)`, `ẑ_i` its column's bit slice `i` at its point;
* `holds_merge_imp`: the merged claim holds of `q` only where the map of the claimed merged slices
  `S = s_a + ρ s_b` meets that of the true ones `Z = z_a + ρ z_b`;
* `ringFacts_two`: `RingFacts` for `[a, b]`, the count `3|E|^16` of `17` challenges (`1` for `ρ`,
  `2/|E|` for the map, `RingMap.card_ringTarget_bad_le`).
-/

namespace LeanVM.Protocol.Whir.Params

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
  Finset
open scoped ENNReal

@[expose] public section

/-! ## The statement's ring switching is `RingMap`'s -/

theorem frobenius_fold (n : ℕ) (l : List E) (y : E) :
    (List.range n).foldl (fun (acc : List E × E) _ ↦ (acc.1 ++ [acc.2], acc.2 * acc.2)) (l, y) =
      (l ++ (List.range n).map fun i ↦ y ^ 2 ^ i, y ^ 2 ^ n) := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, Prod.mk.injEq, true_and]
    rw [← sq, ← pow_mul, ← pow_succ]

theorem frobenius_getD (a : E) {k : ℕ} (hk : k < 64) :
    (Verifier.frobenius a).getD k 0 = a ^ 2 ^ k := by
  unfold Verifier.frobenius
  rw [frobenius_fold]
  simp [List.getD_eq_getElem?_getD, List.getElem?_range hk, kBits]

theorem verifier_frobenius8 : (Verifier.frobenius8 : E → ℕ → E) = Ring.frobenius8 := by
  funext v p
  rw [Ring.frobenius8_eq]
  rfl

theorem verifier_ringTarget : (Verifier.ringTarget : List E → List E → List E → E) =
    Ring.ringTarget := by
  funext s f g
  unfold Verifier.ringTarget Ring.ringTarget
  rw [verifier_frobenius8]
  rfl

theorem verifier_ringCoefficients :
    (Verifier.ringCoefficients : List E → List E → List E) = Ring.ringCoefficients := by
  funext f g
  unfold Verifier.ringCoefficients Ring.ringCoefficients
  rw [verifier_frobenius8]

/-! ## Sums over a list's positions -/

theorem zipIdx_sum {α : Type} (G : E → ℕ → α → E) (a : α) :
    ∀ (l : List E) (s : ℕ), ((l.zipIdx s).map fun (c, k) ↦ G c k a).sum =
      ∑ k ∈ range l.length, G (l.getD k 0) (s + k) a
  | [], s => by simp
  | c :: l, s => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, zipIdx_sum G a l (s + 1),
      List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun k _ ↦ by rw [show s + 1 + k = s + (k + 1) by omega]

/-! ## The Frobenius at a cube point -/

theorem eqEval_boolPoint_frob (k : ℕ) :
    ∀ (n y : ℕ) (pt : List E), pt.length = n →
      eqEval (Tables.boolPoint n y) (pt.map fun a ↦ a ^ 2 ^ k) =
        eqEval (Tables.boolPoint n y) pt ^ 2 ^ k
  | 0, y, pt, h => by
    obtain rfl : pt = [] := List.eq_nil_of_length_eq_zero h
    simp [eqEval]
  | n + 1, y, a :: pt, h => by
    rw [Tables.boolPoint_succ, List.map_cons, Tables.eqEval_cons, Tables.eqEval_cons,
      eqEval_boolPoint_frob k n (y / 2) pt (by simpa using h), mul_pow, add_pow_char_pow,
      add_pow_char_pow, one_pow]
    congr 2
    split_ifs <;> simp

/-! ## A placed piece paired with the stack -/

/-- **A piece placed on an aligned placement within the stack.** -/
def PlacedOK (μ : ℕ) (piece : RingPiece) : Prop :=
  ∃ p : Placement, piece.placement = some p ∧ piece.point.length = p.variableCount ∧
    2 ^ p.variableCount ∣ p.index ∧ p.index + 2 ^ p.variableCount ≤ 2 ^ μ

theorem placedOK_pieceOK {μ : ℕ} {piece : RingPiece} (h : PlacedOK μ piece) :
    PieceOK μ piece := by
  obtain ⟨p, hp, hl, -, hfit⟩ := h
  exact ⟨p, hp, hl, Relation.le_of_two_pow_le (by omega)⟩

/-- The bit `i` of a word, as the statement reads it. -/
theorem bitOf_eq (a : K) (i : Fin 64) : Ring.bitOf a i = Relation.bitOf a i := rfl

private theorem frobPhi_mul_bit' (f g : Fin 8 → E) (e : E) (b : Bool) :
    Ring.frobPhi 8 f g (e * if b then 1 else 0) = (if b then 1 else 0) * Ring.frobPhi 8 f g e := by
  cases b <;> simp [Ring.frobPhi_zero]

/-- The pairing's bit expansion: `Σ_y Φ(s·e_y) w_y = Σ_i x^i Φ(s·Σ_y e_y bit_i(w_y))`. -/
theorem sum_frobPhi_ofK (f g : Fin 8 → E) (S : Finset ℕ) (e : ℕ → E) (w : ℕ → K) (s : E) :
    ∑ y ∈ S, Ring.frobPhi 8 f g (s * e y) * ofK (w y) =
      ∑ i : Fin 64, Ring.ringW i * Ring.frobPhi 8 f g (s * ∑ y ∈ S, e y * Ring.bitOf (w y) i) := by
  simp only [Ring.ofK_eq_sum_bitOf, Finset.mul_sum, Ring.frobPhi_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  unfold Ring.bitOf
  rw [← mul_assoc s, frobPhi_mul_bit']
  ring

/-- The map as a sum over the statement's coefficients. -/
theorem frobPhi_eq_coefs (f g : Fin 8 → E) (a : E) :
    Ring.frobPhi 8 f g a = ∑ k ∈ range 64,
      (Verifier.ringCoefficients (List.ofFn f) (List.ofFn g)).getD k 0 * a ^ 2 ^ k := by
  rw [Ring.frobPhi_eq_idxSum, Ring.idxSum_eq_sum_range, verifier_ringCoefficients,
    Ring.length_ringCoefficients]

/-- The rows of a placed piece's column, bit `i`, at its point. -/
theorem rowMle_bit {μ : ℕ} (q : Column μ) {p : Placement} (point : List E)
    (hlen : point.length = p.variableCount) (i : ℕ) :
    Relation.rowMle point (fun j ↦ Relation.bitOf (Relation.pieceRow q (some p) j) i) =
      ∑ y ∈ range (2 ^ p.variableCount),
        eqEval (Tables.boolPoint p.variableCount y) point *
          Relation.bitOf (Relation.cell q (p.index + y)) i := by
  unfold Relation.rowMle
  rw [Tables.multilinearEval_eq_sum p.variableCount _ point (by simp [hlen]) hlen]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  rw [mul_comm, Tables.eqEval_comm]
  congr 1
  rw [hlen]
  simp [List.getD_eq_getElem?_getD, List.getElem?_range (mem_range.mp hy), Relation.pieceRow]

/-- **A placed piece's weight paired with the stack** is `Σ_i x^i Φ(s · ẑ_i)`. -/
theorem pair_flatWeight {μ : ℕ} (f g : Fin 8 → E) (q : Column μ) (piece : RingPiece)
    (h : PlacedOK μ piece) :
    ∑ x : Fin (2 ^ μ), flatWeight (Verifier.ringCoefficients (List.ofFn f) (List.ofFn g))
        (Tables.boolPoint μ x) piece * ofK (Relation.cell q x) =
      ∑ i : Fin 64, Ring.ringW i * Ring.frobPhi 8 f g (piece.scale *
        Relation.rowMle piece.point (fun j ↦ Relation.bitOf (Relation.pieceRow q piece.placement j) i)) := by
  obtain ⟨p, hp, hlen, ⟨s, hs⟩, hfit⟩ := h
  set vc := p.variableCount with hvcdef
  have hvc : vc ≤ μ := Relation.le_of_two_pow_le (by omega)
  have hsμ : s < 2 ^ (μ - vc) := by
    have h1 : 2 ^ μ = 2 ^ vc * 2 ^ (μ - vc) := by rw [← pow_add]; congr 1; omega
    have h3 : 2 ^ vc * (s + 1) ≤ 2 ^ vc * 2 ^ (μ - vc) := by
      rw [mul_add, mul_one, ← h1, ← hs]; exact hfit
    have := Nat.le_of_mul_le_mul_left h3 (by positivity)
    omega
  have hsel : p.index >>> vc = s := by
    rw [Nat.shiftRight_eq_div_pow, hs, Nat.mul_div_cancel_left _ (by positivity)]
  set coefs := Verifier.ringCoefficients (List.ofFn f) (List.ofFn g) with hcoefs
  have hclen : coefs.length = 64 := by
    rw [hcoefs, verifier_ringCoefficients, Ring.length_ringCoefficients]
  -- Each weight, as a sum over the Frobenius powers.
  have h1 : ∀ x : Fin (2 ^ μ), flatWeight coefs (Tables.boolPoint μ x) piece =
      ∑ k ∈ range 64, coefs.getD k 0 * piece.scale ^ 2 ^ k *
        eqEval ((piece.point.map fun a ↦ a ^ 2 ^ k) ++ selectorPoint s (μ - vc))
          (Tables.boolPoint μ x) := by
    intro x
    rw [flatWeight_eq coefs piece hp hlen hvc _ (Tables.length_boolPoint _ _), hsel,
      zipIdx_sum (fun c k x ↦ c * (Verifier.frobenius piece.scale).getD k 0 *
        eqEval (piece.point.map (fun a ↦ (Verifier.frobenius a).getD k 0) ++
          selectorPoint s (μ - vc)) (Tables.boolPoint μ x)) x coefs 0, hclen]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' := mem_range.mp hk
    rw [zero_add, frobenius_getD _ hk', show piece.point.map
      (fun a ↦ (Verifier.frobenius a).getD k 0) = piece.point.map (fun a ↦ a ^ 2 ^ k) from
        List.map_congr_left fun a _ ↦ frobenius_getD a hk']
  -- The stack's sum under each Frobenius power.
  have h2 : ∀ k, ∑ x : Fin (2 ^ μ), eqEval ((piece.point.map fun a ↦ a ^ 2 ^ k) ++
        selectorPoint s (μ - vc)) (Tables.boolPoint μ x) * ofK (Relation.cell q x) =
      ∑ y ∈ range (2 ^ vc), (eqEval (Tables.boolPoint vc y) piece.point) ^ 2 ^ k *
        ofK (Relation.cell q (p.index + y)) := by
    intro k
    rw [Relation.sum_stackPoint μ vc s q _ (by simp [hlen]) hvc hsμ, hs]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [eqEval_boolPoint_frob k vc y piece.point hlen]
  calc ∑ x : Fin (2 ^ μ), flatWeight coefs (Tables.boolPoint μ x) piece * ofK (Relation.cell q x)
      = ∑ k ∈ range 64, coefs.getD k 0 * piece.scale ^ 2 ^ k *
          ∑ x : Fin (2 ^ μ), eqEval ((piece.point.map fun a ↦ a ^ 2 ^ k) ++
            selectorPoint s (μ - vc)) (Tables.boolPoint μ x) * ofK (Relation.cell q x) := by
        simp only [h1, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring
    _ = ∑ y ∈ range (2 ^ vc), Ring.frobPhi 8 f g
          (piece.scale * eqEval (Tables.boolPoint vc y) piece.point) *
            ofK (Relation.cell q (p.index + y)) := by
        simp only [h2, frobPhi_eq_coefs, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun k _ ↦ by
          rw [mul_pow]; ring
    _ = _ := by
        rw [sum_frobPhi_ofK f g (range (2 ^ vc)) (fun y ↦ eqEval (Tables.boolPoint vc y) piece.point)
          (fun y ↦ Relation.cell q (p.index + y)) piece.scale]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hp, rowMle_bit q piece.point hlen i]
        rfl

/-! ## Two claims merged -/

/-- A claim's true slice `i` on the stack: what `RingClaimHolds` asks the slice to be. -/
def trueSlice {μ : ℕ} (q : Column μ) (c : RingClaim) (i : ℕ) : E :=
  sumE (c.pieces.map fun piece ↦
    piece.scale * Relation.rowMle piece.point fun j ↦
      Relation.bitOf (Relation.pieceRow q piece.placement j) i)

theorem frobPhi_listSum (f g : Fin 8 → E) (l : List E) :
    Ring.frobPhi 8 f g l.sum = (l.map (Ring.frobPhi 8 f g)).sum := by
  induction l with
  | nil => simp [Ring.frobPhi_zero]
  | cons a l ih => simp [Ring.frobPhi_add, ih]

theorem sum_listSum {α : Type} {n : ℕ} (L : List α) (F : α → Fin n → E) :
    ∑ x : Fin n, (L.map fun a ↦ F a x).sum = (L.map fun a ↦ ∑ x : Fin n, F a x).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [Finset.sum_add_distrib, ih]

theorem sum_listSum_mul {α : Type} {n : ℕ} (L : List α) (F : α → Fin n → E) (w : Fin n → E) :
    ∑ x : Fin n, (L.map fun a ↦ F a x).sum * w x =
      (L.map fun a ↦ ∑ x : Fin n, F a x * w x).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [add_mul, Finset.sum_add_distrib, ih]

/-- **Two claims merged, paired with the stack**: `Σ_i x^i Φ(z_a,i + ρ z_b,i)`. -/
theorem pair_merge {μ : ℕ} (f g : Fin 8 → E) (rho : E) (q : Column μ) (a b : RingClaim)
    (h : ∀ piece ∈ a.pieces ++ b.pieces, PlacedOK μ piece) :
    ∑ x : Fin (2 ^ μ), (ringMerge [a, b] (List.ofFn f) (List.ofFn g) rho).1
        (Tables.boolPoint μ x) * ofK (Relation.cell q x) =
      ∑ i : Fin 64, Ring.ringW i * Ring.frobPhi 8 f g (trueSlice q a i + rho * trueSlice q b i) := by
  simp only [ringMerge_weight]
  rw [sum_listSum_mul (flatPieces rho [a, b] 1) (fun piece x ↦ flatWeight
    (ringCoefficients (List.ofFn f) (List.ofFn g)) (Tables.boolPoint μ x) piece)
    (fun x ↦ ofK (Relation.cell q x))]
  have hflat : ∀ piece ∈ flatPieces rho [a, b] 1, PlacedOK μ piece := by
    intro piece hp
    simp only [flatPieces, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hp
    rcases hp with ⟨pc, hpc, rfl⟩ | ⟨pc, hpc, rfl⟩
    · exact h pc (List.mem_append_left _ hpc)
    · exact h pc (List.mem_append_right _ hpc)
  rw [List.map_congr_left fun piece hp ↦ pair_flatWeight f g q piece (hflat piece hp)]
  rw [show ∀ (L : List RingPiece), (L.map fun piece ↦ ∑ i : Fin 64, Ring.ringW i *
      Ring.frobPhi 8 f g (piece.scale * Relation.rowMle piece.point fun j ↦
        Relation.bitOf (Relation.pieceRow q piece.placement j) i)).sum =
      ∑ i : Fin 64, Ring.ringW i * Ring.frobPhi 8 f g ((L.map fun piece ↦ piece.scale *
        Relation.rowMle piece.point fun j ↦
          Relation.bitOf (Relation.pieceRow q piece.placement j) i).sum) from fun L ↦ by
    rw [← sum_listSum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [frobPhi_listSum, List.sum_map_mul_left]
    simp only [List.map_map, Function.comp_def]]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 2
  simp only [flatPieces, trueSlice, sumE_eq_sum', List.map_append, List.sum_append,
    List.map_map, Function.comp_def, List.map_nil, List.sum_nil, add_zero, one_mul]
  rw [list_sum_map_mul_left]
  exact congrArg (_ + ·) (congrArg List.sum (List.map_congr_left fun _ _ ↦ by ring))

/-- **Two claims' slices merged**: `s_a + ρ s_b`. -/
theorem mergeSlices_eq (a b : RingClaim) (ha : a.slices.length = 64) (hb : b.slices.length = 64)
    (rho : E) :
    ([a, b].foldl (claimStep rho) (List.replicate kBits 0, [], [], 1)).1 =
      List.ofFn fun i : Fin 64 ↦ a.slices.getD i 0 + rho * b.slices.getD i 0 := by
  rw [List.foldl_cons, List.foldl_cons, List.foldl_nil, claimStep_eq, claimStep_eq]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_zipIdx, List.length_replicate, List.length_ofFn]
    rfl
  · intro i h1 h2
    have hi : i < 64 := by rw [List.length_ofFn] at h2; exact h2
    have hia : i < a.slices.length := by omega
    have hib : i < b.slices.length := by omega
    have ea : a.slices[i]? = some a.slices[i] := List.getElem?_eq_getElem hia
    have eb : b.slices[i]? = some b.slices[i] := List.getElem?_eq_getElem hib
    rw [List.getElem_map, List.getElem_zipIdx, List.getElem_map, List.getElem_zipIdx,
      List.getElem_replicate, List.getElem_ofFn]
    dsimp only
    rw [Nat.zero_add, ea, eb]
    dsimp only
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, ea, eb, Option.getD_some,
      Option.getD_some, zero_add, one_mul, one_mul]

/-- **The merged claim holds only where the maps of the claimed and the true slices meet.** -/
theorem holds_merge_imp {μ : ℕ} (f g : Fin 8 → E) (rho : E) (q : Column μ) (a b : RingClaim)
    (h : ∀ piece ∈ a.pieces ++ b.pieces, PlacedOK μ piece) (ha : a.slices.length = 64)
    (hb : b.slices.length = 64)
    (hh : StackClaim.Holds μ (ringMerge [a, b] (List.ofFn f) (List.ofFn g) rho) q) :
    Ring.ringTarget (List.ofFn fun i : Fin 64 ↦ a.slices.getD i 0 + rho * b.slices.getD i 0)
        (List.ofFn f) (List.ofFn g) =
      ∑ i : Fin 64, Ring.ringW i * Ring.frobPhi 8 f g (trueSlice q a i + rho * trueSlice q b i) := by
  rw [← pair_merge f g rho q a b h, ← mergeSlices_eq a b ha hb rho, ← verifier_ringTarget]
  exact hh.symm

/-! ## The count -/

open Classical in
/-- `ρ` makes two different pairs of slice vectors meet at most once. -/
theorem card_rho_bad_le (sa sb za zb : Fin 64 → E) (hne : sa ≠ za ∨ sb ≠ zb) :
    (univ.filter fun r : E ↦ (fun i ↦ sa i + r * sb i) = fun i ↦ za i + r * zb i).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro r1 h1 r2 h2
  simp only [mem_filter, mem_univ, true_and] at h1 h2
  by_contra hne12
  have hb : ∀ i, sb i = zb i := fun i ↦ by
    have e1 := congrFun h1 i
    have e2 := congrFun h2 i
    have : (r1 - r2) * (sb i - zb i) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hne12
    · exact sub_eq_zero.mp h
  have ha : ∀ i, sa i = za i := fun i ↦ by
    have e1 := congrFun h1 i
    rw [hb i] at e1
    exact add_right_cancel e1
  rcases hne with h | h
  · exact h (funext ha)
  · exact h (funext hb)

open Classical in
/-- **The bad challenges of two merged claims are few**: at most `3|E|^16` of the `|E|^17`
lists `(f, g, ρ)`, for claimed slices different from the true ones. -/
theorem card_ring_bad_le (sa sb za zb : Fin 64 → E) (hne : sa ≠ za ∨ sb ≠ zb) :
    (univ.filter fun x : ((Fin 8 → E) × (Fin 8 → E)) × E ↦
      Ring.ringTarget (List.ofFn fun i ↦ sa i + x.2 * sb i) (List.ofFn x.1.1) (List.ofFn x.1.2) =
        ∑ i : Fin 64, Ring.ringW i * Ring.frobPhi 8 x.1.1 x.1.2 (za i + x.2 * zb i)).card ≤
      3 * Fintype.card E ^ 16 := by
  set P := fun (fg : (Fin 8 → E) × (Fin 8 → E)) (r : E) ↦
    Ring.ringTarget (List.ofFn fun i ↦ sa i + r * sb i) (List.ofFn fg.1) (List.ofFn fg.2) =
      ∑ i : Fin 64, Ring.ringW i * Ring.frobPhi 8 fg.1 fg.2 (za i + r * zb i)
  have hcard : Fintype.card ((Fin 8 → E) × (Fin 8 → E)) = Fintype.card E ^ 16 := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ← pow_add]
  have hper : ∀ r : E, (univ.filter fun fg ↦ P fg r).card ≤
      (if (fun i ↦ sa i + r * sb i) = (fun i ↦ za i + r * zb i) then Fintype.card E ^ 16 else 0) +
        2 * Fintype.card E ^ 15 := by
    intro r
    split_ifs with hs
    · rw [← hcard]
      exact (Finset.card_le_univ _).trans (Nat.le_add_right _ _)
    · have hc := Ring.card_ringTarget_bad_le hs
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card] at hc
      rw [zero_add]
      exact hc
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  calc ∑ r : E, ∑ fg : (Fin 8 → E) × (Fin 8 → E), (if P fg r then 1 else 0)
      = ∑ r : E, (univ.filter fun fg ↦ P fg r).card := by
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        rw [Finset.card_filter]
    _ ≤ ∑ r : E, ((if (fun i ↦ sa i + r * sb i) = (fun i ↦ za i + r * zb i) then
          Fintype.card E ^ 16 else 0) + 2 * Fintype.card E ^ 15) :=
        Finset.sum_le_sum fun r _ ↦ hper r
    _ = (univ.filter fun r : E ↦ (fun i ↦ sa i + r * sb i) = fun i ↦ za i + r * zb i).card *
          Fintype.card E ^ 16 + Fintype.card E * (2 * Fintype.card E ^ 15) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, Finset.card_univ]
    _ ≤ 1 * Fintype.card E ^ 16 + Fintype.card E * (2 * Fintype.card E ^ 15) := by
        gcongr
        exact card_rho_bad_le sa sb za zb hne
    _ = 3 * Fintype.card E ^ 16 := by ring

/-! ## Ring switching's facts for two claims -/

theorem ringChallengeCount_two (a b : RingClaim) : ringChallengeCount [a, b] = 17 := rfl

/-- The challenges of a list of `17`, sliced as ring switching slices them. -/
def splitV (v : Fin 17 → E) : ((Fin 8 → E) × (Fin 8 → E)) × E :=
  ((fun i ↦ v ⟨i, by omega⟩, fun i ↦ v ⟨8 + i, by omega⟩), v ⟨16, by omega⟩)

theorem ringClaimAt_two (a b : RingClaim) (v : Fin 17 → E) :
    ringClaimAt [a, b] (List.ofFn v) =
      ringMerge [a, b] (List.ofFn (splitV v).1.1) (List.ofFn (splitV v).1.2) (splitV v).2 := by
  have h1 : (List.ofFn v).take ringMapWidth = List.ofFn (splitV v).1.1 := by
    apply List.ext_getElem (by simp [ringMapWidth])
    intro i h1 h2
    simp only [List.getElem_take, List.getElem_ofFn, splitV]
  have h2 : ((List.ofFn v).drop ringMapWidth).take ringMapWidth = List.ofFn (splitV v).1.2 := by
    apply List.ext_getElem (by simp [ringMapWidth])
    intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn, splitV]
    rfl
  have h3 : (List.ofFn v).getD (2 * ringMapWidth) 0 = (splitV v).2 := by
    simp [splitV, ringMapWidth, List.getD_eq_getElem?_getD]
  have hm : 1 < [a, b].length := by simp
  unfold ringClaimAt
  simp only [hm, ↓reduceIte]
  rw [h1, h2, h3]

theorem splitV_injective : Function.Injective splitV := by
  intro v w h
  simp only [splitV, Prod.mk.injEq] at h
  obtain ⟨⟨hf, hg⟩, hr⟩ := h
  funext j
  by_cases j8 : j.val < 8
  · exact congrFun hf ⟨j.val, j8⟩
  · by_cases j16 : j.val < 16
    · have := congrFun hg ⟨j.val - 8, by omega⟩
      simp only at this
      rwa [show (⟨8 + (j.val - 8), by omega⟩ : Fin 17) = j from Fin.ext (by simp; omega)] at this
    · rwa [show (⟨16, by omega⟩ : Fin 17) = j from Fin.ext (by simp; omega)] at hr

open Classical in
/-- **Ring switching's facts for two claims** whose pieces are placed and whose slices are `64`. -/
theorem ringFacts_two {μ : ℕ} (a b : RingClaim)
    (h : ∀ piece ∈ a.pieces ++ b.pieces, PlacedOK μ piece) (ha : a.slices.length = 64)
    (hb : b.slices.length = 64) : RingFacts μ [a, b] := by
  refine ringFacts_of (fun c hc piece hp ↦ placedOK_pieceOK (h piece ?_)) fun q hq ↦ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact List.mem_append_left _ hp
    · exact List.mem_append_right _ hp
  set sa : Fin 64 → E := fun i ↦ a.slices.getD i 0
  set sb : Fin 64 → E := fun i ↦ b.slices.getD i 0
  set za : Fin 64 → E := fun i ↦ trueSlice q a i
  set zb : Fin 64 → E := fun i ↦ trueSlice q b i
  have hne : sa ≠ za ∨ sb ≠ zb := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    obtain ⟨rc, hrc, hn⟩ := hq
    have key : ∀ c : RingClaim, c.slices.length = 64 → ¬ Relation.RingClaimHolds q c →
        (fun i : Fin 64 ↦ c.slices.getD i 0) ≠ fun i : Fin 64 ↦ trueSlice q c i := by
      intro c hl hc heq
      exact hc ⟨hl, fun i hi ↦ congrFun heq ⟨i, hi⟩⟩
    rcases hrc with rfl | rfl
    · exact .inl (key rc ha hn)
    · exact .inr (key rc hb hn)
  rw [ringChallengeCount_two]
  have hc := avgPk_le_card (N := 3) (by norm_num : 1 ≤ 17)
    (fun pre ↦ StackClaim.Holds μ (ringClaimAt [a, b] pre) q) ?_
  · refine le_trans (le_of_eq (avgPk_congr fun pre _ ↦ rfl)) (hc.trans (le_of_eq ?_))
    norm_num
  refine (Finset.card_le_card_of_injOn splitV ?_ splitV_injective.injOn).trans
    (card_ring_bad_le sa sb za zb hne)
  intro v hv
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
  rw [ringClaimAt_two] at hv
  exact holds_merge_imp _ _ _ q a b h ha hb hv

/-! ## From the layout and the phases' shapes -/

/-- A placement of a layout `buildLayout` gives fills its column's `kappa` variables. -/
theorem variableCount_eq {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode lm rows = some layout) {c : ℕ} {p : Placement}
    (hp : layout.placements.getD c none = some p) :
    p.variableCount = (columnKappas tables lm layout.tableLogHeights).getD c 0 := by
  unfold buildLayout at h
  split at h
  · cases h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      dsimp only at hp ⊢
      generalize columnKappas tables lm _ = kappas at hp ⊢
      generalize stack kappas = st at hp
      obtain ⟨offsets, stackLog⟩ := st
      dsimp only at hp
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx, zero_add] at hp
      rcases hkc : kappas[c]? with _ | kappa
      · simp [hkc] at hp
      simp only [hkc, Option.map_some, Option.getD_some] at hp ⊢
      obtain ⟨o, -, rfl⟩ := Option.map_eq_some_iff.mp hp
      simp [List.getD_eq_getElem?_getD, hkc]
    · cases h

/-- **`q_keccak`'s placement fills the `KECCAK` table's height and the slot bits.** -/
theorem variableCount_qkeccak {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode lm rows = some layout) {qk : Placement}
    (hqk : layout.placements.getD qkeccak none = some qk) :
    qk.variableCount = Relation.keccakHeight layout + qkeccakSlotBits := by
  rw [variableCount_eq h hqk]
  simp [columnKappas, qkeccak, Relation.keccakHeight, List.getD_eq_getElem?_getD]

/-- A piece on a layout placement, its point filling the placement, is placed. -/
theorem placedOK_of {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode lm rows = some layout) {piece : RingPiece} {c : ℕ} {p : Placement}
    (hp : layout.placements.getD c none = some p) (hpl : piece.placement = some p)
    (hlen : piece.point.length = p.variableCount) : PlacedOK layout.stackLog piece :=
  ⟨p, hpl, hlen, placement_aligned h hp⟩

/-- **Ring switching's facts for the walk's two ring claims**: the Keccak reduction's on
`q_keccak` and the link's, from the layout and the phases' shapes. -/
theorem ringFacts_of_shape {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode lm rows = some layout) {link : LinkEnd}
    (hl : Relation.LinkShape layout link) {kr : List ColumnClaim × List E × List E}
    (hk : Relation.KeccakShape layout kr) {qk : Placement}
    (hqk : layout.placements.getD qkeccak none = some qk) :
    RingFacts layout.stackLog [keccakRingClaim qk kr.2.1 kr.2.2, link.ring] := by
  obtain ⟨-, -, -, -, hpieces, hslices⟩ := hl
  obtain ⟨-, hpt, hsl, -⟩ := hk
  refine ringFacts_two _ _ (fun piece hp ↦ ?_) hsl hslices
  rcases List.mem_append.mp hp with hp | hp
  · simp only [keccakRingClaim, List.mem_singleton] at hp
    subst hp
    exact placedOK_of h hqk rfl (by rw [variableCount_qkeccak h hqk]; exact hpt)
  · obtain ⟨c, p, hcp, hpl, hlen⟩ := hpieces piece hp
    exact placedOK_of h hcp hpl hlen

end
end LeanVM.Protocol.Whir.Params
