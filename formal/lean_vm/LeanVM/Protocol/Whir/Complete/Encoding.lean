/-
  LeanVM.Protocol.Whir.Complete.Encoding

  The honest words of a WHIR opening and what the verifier reads from them: the stack's level-0
  word and the folded levels' words, the rows an opening returns, the sum a level's queries
  enforce, and the query weight that the verifier's `inducedWeight` evaluates.
-/

module

public import LeanVM.Protocol.Whir.Complete.Tables
public import LeanVM.Protocol.Whir.ColumnWeight
public import LeanVM.Protocol.EndToEnd.Candidates
public import LeanVM.Protocol.Verifier
public import LeanVM.Protocol.Whir.SubspaceAt

/-!
# The honest words

A WHIR level commits an interleaved Reed-Solomon codeword: the message on `k + κ` variables is
cut into `2^k` *lanes* along its first `k` variables, lane `j` being the message
`x ↦ g[j + 2^k·⟨x⟩]` on the remaining `κ`, and each lane is encoded by `enc κ R`
(`LeanVM.Protocol.Whir.NovelBasis`). Leaf `p` of the word holds the `2^k` lanes' codeword
entries at the domain point `x_p = K.ofBits p`, for `p < 2^(κ+R)`. A run reads no leaf off the
domain; there the words hold zeros, as the executable prover's arrays read past their end, so
that the two words are equal (`LeanVM.Prover.Enc.stackWordFast_eq`).

* `stackWord μ R q`: the stack's level-0 word (`verify_execution` step 2, `commitStack`): the
  lanes are the stack's `64` blocks (`blockOf`, `LeanVM.Protocol.EndToEnd.Candidates`), the
  leaf stores their `K`-valued codeword entries in reverse lane order. `stackWord_agrees`: it is
  the encoding of the stack in the sense of `Agrees`, on every column.
* `levelWord κ k R g`: a deeper level's word, each `E` entry written as its two limbs, the layout
  `ext_row` regroups (`crates/verifier/src/whir.rs:72-75`).
* `stackTable μ q`: the stack as a table in the WHIR variable order: the six lane variables
  first, then the block offset (`f(u, x) = q(x, u)`), i.e. the stack's index rotated by six
  bits.

What the verifier computes from an honest opening:

* `readRow_stackWord`, `extRow_levelWord`: the rows it reads are the lanes' codeword entries
  (`laneCodes`);
* `subspaceAt_eq`: the verifier's `subspaceAt n x` is `[Ŵ_0(x), …, Ŵ_n(x)]`;
* `queryTable_eq`: the table of the verifier's `inducedWeight` is the batched column weights
  `Σ_q w_q X_i(x_q)` of `lem:colweight`;
* `inducedWeight_eq_sum`, `isMultilinearFn_inducedWeight`: the verifier's `inducedWeight` is a
  sum of products of affine factors, hence multilinear, so its value at the terminal point is the
  extension of that table.
-/

namespace LeanVM.Protocol.Whir.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
  LeanVM.Protocol.Compile LeanVM.Protocol.Whir Finset

@[expose] public section

/-! ## The encoder at a position -/

/-- `Enc(g)` at the domain point `x_p = K.ofBits p`, for every `p`. -/
def encAt (κ : ℕ) (g : (Fin κ → Bool) → E) (p : ℕ) : E :=
  ∑ u, g u * ofK (novelAt (bitsToNat u) (K.ofBits p))

/-- The encoder on a `K`-valued message, at a position. -/
def encKAt (κ : ℕ) (g : (Fin κ → Bool) → K) (p : ℕ) : K :=
  ∑ u, g u * novelAt (bitsToNat u) (K.ofBits p)

/-- The `K`-valued encoder lifted to `E` is the encoder of the lifted message. -/
theorem ofK_encKAt (κ : ℕ) (g : (Fin κ → Bool) → K) (p : ℕ) :
    ofK (encKAt κ g p) = encAt κ (fun u ↦ ofK (g u)) p := by
  rw [encKAt, encAt]
  change algebraMap K E _ = _
  rw [map_sum]
  exact sum_congr rfl fun u _ ↦ ofK_mul _ _

/-- A sum over the cube `Fin κ → Bool` as a sum over the indices. -/
theorem sum_cube (κ : ℕ) (F : (Fin κ → Bool) → E) :
    ∑ u, F u = ∑ i ∈ range (2 ^ κ), F fun k ↦ i.testBit k := by
  rw [← Equiv.sum_comp (bitsEquiv κ).symm,
    ← Fin.sum_univ_eq_sum_range (fun i ↦ F fun k ↦ i.testBit k)]
  exact sum_congr rfl fun j _ ↦ by
    congr 1; funext k; exact bitsEquiv_symm_apply j k

/-- A message read from a table: `u ↦ t[⟨u⟩]`. -/
def msgOf (κ : ℕ) (t : List E) : (Fin κ → Bool) → E := fun u ↦ t.getD (bitsToNat u) 0

/-! ## Lanes -/

/-- Lane `j` of a table cut along its first `k` variables: `x ↦ t[j + 2^k·⟨x⟩]`. -/
def laneMsg (κ k : ℕ) (t : List E) (j : ℕ) : (Fin κ → Bool) → E :=
  fun x ↦ t.getD (j + 2 ^ k * bitsToNat x) 0

/-- The `2^k` lanes' codeword entries at the position `p`. -/
def laneCodes (κ k : ℕ) (t : List E) (p : ℕ) : List E :=
  (List.range (2 ^ k)).map fun j ↦ encAt κ (laneMsg κ k t j) p

/-! ## The level words -/

/-- The two limbs of an entry, the order `ext_row` reads them. -/
def limbsOf (e : E) : List K := [e.limb 0, e.limb 1]

/-- **A deeper level's word**: leaf `p` holds the `2^k` lanes' entries at `x_p`, two limbs
each, on the domain `p < 2^(κ+R)`; zero entries off it, as the executable prover's arrays read
past their end (the run reads the leaves below the committed height only). -/
def levelWord (κ k R : ℕ) (g : List E) : Word :=
  fun p ↦ ((List.range (2 ^ k)).map fun j ↦
    if p < 2 ^ (κ + R) then encAt κ (laneMsg κ k g j) p else 0).flatMap limbsOf

/-- `ext_row` regroups limbs written by `limbsOf`. -/
theorem extRow_flatMap_limbsOf : ∀ l : List E, extRow (l.flatMap limbsOf) = l
  | [] => by simp [extRow]
  | e :: l => by
    simp only [List.flatMap_cons, limbsOf, List.cons_append, List.nil_append, extRow,
      ofLimbs_limb, extRow_flatMap_limbsOf l]

/-- Two limbs per entry. -/
theorem length_flatMap_limbsOf : ∀ l : List E, (l.flatMap limbsOf).length = 2 * l.length
  | [] => rfl
  | e :: l => by
    rw [List.flatMap_cons, List.length_append, length_flatMap_limbsOf l]
    simp [limbsOf]; ring

/-- A level word has `2·2^k` words per leaf, the width the verifier announces. -/
theorem wellShaped_levelWord (κ k R : ℕ) (g : List E) :
    WellShaped (2 * 2 ^ k) (levelWord κ k R g) := by
  intro p
  rw [levelWord, length_flatMap_limbsOf]
  simp

/-- The verifier reads a level word's leaf on the domain as the lanes' entries. -/
theorem extRow_levelWord (κ k R : ℕ) (g : List E) {p : ℕ} (hp : p < 2 ^ (κ + R)) :
    extRow (levelWord κ k R g p) = laneCodes κ k g p := by
  simp only [levelWord, hp, ite_true, extRow_flatMap_limbsOf]
  rfl

/-! ## The stack's word -/

/-- Block `u` of the stack as a `K`-valued message: cell `⟨x⟩ + 2^(μ−6)·u`. -/
def blockK (μ : ℕ) (q : Column μ) (u : ℕ) : (Fin (μ - laneBits) → Bool) → K :=
  fun x ↦ q.values.getD (bitsToNat x + 2 ^ (μ - laneBits) * u) 0

/-- **The stack's level-0 word**: leaf `p` holds the `64` blocks' codeword entries at `x_p`, in
reverse lane order, on the domain `p < 2^(μ−6+R)`; zero entries off it (as `levelWord`). -/
def stackWord (μ R : ℕ) (q : Column μ) : Word :=
  fun p ↦ ((List.range (2 ^ laneBits)).map fun u ↦
    if p < 2 ^ (μ - laneBits + R) then encKAt (μ - laneBits) (blockK μ q u) p else 0).reverse

/-- The stack word has `64` words per leaf, the width `commitStack` announces. -/
theorem wellShaped_stackWord (μ R : ℕ) (q : Column μ) :
    WellShaped (2 ^ laneBits) (stackWord μ R q) := by
  intro p
  simp [stackWord]

/-- The stack's word is its encoding: it agrees with the encoding of `q` on every column. -/
theorem stackWord_agrees (μ R : ℕ) (q : Column μ) :
    Agrees μ R (stackWord μ R q) q Finset.univ := by
  have h0 : ofK (0 : K) = 0 := map_zero (algebraMap K E)
  refine ⟨fun _ ↦ 0, fun _ ↦ by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _,
    fun v _ u ↦ ?_⟩
  simp only [laneOf, laneValue, stackWord, List.reverse_reverse, v.isLt, ite_true,
    Polynomial.eval_zero, mul_zero, h0, add_zero]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range, ofK_encKAt]
  rfl

/-- The stack in the WHIR variable order: entry `i` is the cell at the index rotated by the six
lane bits, `⌊i / 64⌋ + 2^(μ−6)·(i mod 64)`. -/
def stackTable (μ : ℕ) (q : Column μ) : List E :=
  (List.range (2 ^ μ)).map fun i ↦ ofK (q.values.getD (rotIndex laneBits (μ - laneBits) i) 0)

@[simp] theorem length_stackTable (μ : ℕ) (q : Column μ) : (stackTable μ q).length = 2 ^ μ := by
  simp [stackTable]

/-- The rows the verifier reads from the stack's word (`row.reverse`, lifted to `E`) are the
lanes' entries of the stack table. -/
theorem readRow_stackWord {μ R : ℕ} (hμ : laneBits ≤ μ) (q : Column μ) {p : ℕ}
    (hp : p < 2 ^ (μ - laneBits + R)) :
    (stackWord μ R q p).reverse.map ofK =
      laneCodes (μ - laneBits) laneBits (stackTable μ q) p := by
  simp only [stackWord, hp, ite_true, List.reverse_reverse, List.map_map, laneCodes]
  refine List.map_congr_left fun u hu ↦ ?_
  have hu' : u < 2 ^ laneBits := List.mem_range.mp hu
  simp only [Function.comp_apply, ofK_encKAt]
  congr 1
  funext x
  have hx := bitsToNat_lt x
  have hlt : u + 2 ^ laneBits * bitsToNat x < 2 ^ μ := by
    have := add_mul_lt hu' hx
    rwa [← pow_add, Nat.add_sub_cancel' hμ] at this
  simp only [laneMsg, stackTable, blockK]
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, List.getElem_range]
  congr 2
  rw [rotIndex, add_comm u, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hu', add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hu']

/-! ## The verifier's induced weight -/

private theorem ofK_one : ofK 1 = 1 := map_one (algebraMap K E)

/-- A left fold that adds `f a` at every step is a sum. -/
theorem foldl_eq_add_sum {α : Type} (F : E → α → E) (f : α → E) (hF : ∀ t a, F t a = t + f a) :
    ∀ (l : List α) (t : E), l.foldl F t = t + (l.map f).sum
  | [], t => by simp
  | a :: l, t => by
    rw [List.foldl_cons, foldl_eq_add_sum F f hF l, hF, List.map_cons, List.sum_cons, add_assoc]

/-- `affProd` reads its factors' coefficients below the point's length only. -/
theorem affProd_congr {a b b' : ℕ → E} : ∀ {p : List E}, (∀ c < p.length, b c = b' c) →
    affProd a b p = affProd a b' p
  | [], _ => rfl
  | _ :: p, h => by
    rw [affProd, affProd, h 0 (by simp),
      affProd_congr (p := p) fun c hc ↦ h (c + 1) (by simp; omega)]

/-- The product loop of `inducedWeight` as a product of affine factors. -/
theorem foldl_zip_affProd : ∀ (point : List E) (what : List K) (weight : E),
    point.length ≤ what.length →
    (List.zip point what).foldl (fun product (cv : E × K) ↦ product * (1 + cv.1 * ofK (1 + cv.2)))
        weight = weight * affProd (fun _ ↦ 1) (fun i ↦ 1 + ofK (what.getD i 0)) point
  | [], _, weight, _ => by simp [affProd]
  | c :: p, [], _, h => by simp at h
  | c :: p, v :: what, weight, h => by
    rw [List.zip_cons_cons, List.foldl_cons,
      foldl_zip_affProd p what _ (by simpa using h), affProd]
    simp only [List.getD_cons_zero, List.getD_cons_succ, ofK_add, ofK_one]
    ring

/-- **The verifier's induced weight** at a point of at most `n + 1` coordinates is
`Σ_q w_q·Π_c (1 + (1 + Ŵ_c(x_q))·p_c)`, the batched column weights of `lem:colweight`. -/
theorem inducedWeight_eq_sum (n : ℕ) (queries : List ℕ) (queryWeights point : List E)
    (hp : point.length ≤ n) :
    Verifier.inducedWeight n queries queryWeights point =
      ((List.zip queryWeights queries).map fun wq ↦
        wq.1 * affProd (fun _ ↦ 1) (fun c ↦ 1 + ofK (normVanishingAt c (K.ofBits wq.2)))
          point).sum := by
  simp only [Verifier.inducedWeight]
  rw [foldl_eq_add_sum _ (fun wq : E × ℕ ↦ wq.1 * affProd (fun _ ↦ 1)
    (fun c ↦ 1 + ofK (normVanishingAt c (K.ofBits wq.2))) point) (fun t wq ↦ ?_), zero_add]
  obtain ⟨w, q⟩ := wq
  simp only
  rw [foldl_zip_affProd point _ w (by rw [subspaceAt_eq]; simp; omega)]
  congr 2
  refine affProd_congr fun c hc ↦ ?_
  rw [subspaceAt_eq, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map,
    List.getElem_range]

/-- **The induced weight is multilinear** on points of `n` coordinates. -/
theorem isMultilinearFn_inducedWeight (n : ℕ) (queries : List ℕ) (queryWeights : List E) :
    IsMultilinearFn n (Verifier.inducedWeight n queries queryWeights) := by
  refine isMultilinearFn_congr (isMultilinearFn_list_sum (List.zip queryWeights queries)
    (fun wq ↦ wq.1)
    (fun wq ↦ affProd (fun _ ↦ 1) (fun c ↦ 1 + ofK (normVanishingAt c (K.ofBits wq.2))))
    fun _ _ ↦ isMultilinearFn_affProd n _ _) fun p hp ↦ ?_
  rw [inducedWeight_eq_sum n _ _ _ hp.le]

/-- A product of affine factors on a cube point. -/
theorem affProd_boolPoint (φ : ℕ → E) : ∀ (κ i : ℕ),
    affProd (fun _ ↦ 1) φ (boolPoint κ i) = ∏ k : Fin κ, if i.testBit k then 1 + φ k else 1
  | 0, i => by simp [affProd]
  | κ + 1, i => by
    rw [boolPoint_succ, affProd, affProd_boolPoint (fun c ↦ φ (c + 1)) κ (i / 2),
      Fin.prod_univ_succ]
    congr 1
    · by_cases h : i.testBit 0 <;> simp [h]
    · refine prod_congr rfl fun k _ ↦ ?_
      simp [Nat.testBit_div_two]

/-- The column weight at a cube point, through the novel basis: `X_i(a)` lifted is the product
of affine factors `1 + (1 + Ŵ_c(a))·p_c` on the point of `i`. -/
theorem ofK_novelAt_eq_affProd {κ : ℕ} (hκ : κ ≤ 64) (i : ℕ) (hi : i < 2 ^ κ) (a : K) :
    ofK (novelAt i a) =
      affProd (fun _ ↦ 1) (fun c ↦ 1 + ofK (normVanishingAt c a)) (boolPoint κ i) := by
  rw [affProd_boolPoint, ← bitsToNat_testBit hi, novelAt_bitsToNat hκ]
  change algebraMap K E _ = _
  rw [map_prod]
  refine prod_congr rfl fun k _ ↦ ?_
  rw [testBit_bitsToNat]
  split
  · rw [← add_assoc, one_add_one_E, zero_add]; rfl
  · exact map_one _

/-- The induced weight at a cube point. -/
theorem inducedWeight_boolPoint {κ : ℕ} (hκ : κ ≤ 64) (queries : List ℕ) (queryWeights : List E)
    (i : ℕ) (hi : i < 2 ^ κ) :
    Verifier.inducedWeight κ queries queryWeights (boolPoint κ i) =
      ((List.zip queryWeights queries).map fun wq ↦
        wq.1 * ofK (novelAt i (K.ofBits wq.2))).sum := by
  rw [inducedWeight_eq_sum κ _ _ _ (le_of_eq (length_boolPoint κ i))]
  refine congrArg List.sum (List.map_congr_left fun wq _ ↦ ?_)
  rw [ofK_novelAt_eq_affProd hκ i hi]

/-- The table a level's query claim puts on the message cube: entry `i` is
`Σ_q w_q·X_i(x_q)`, the batched column weights at the queried points (`lem:colweight`), computed
in `K` as the prover does. -/
def queryTable (κ : ℕ) (queries : List ℕ) (queryWeights : List E) : List E :=
  (List.range (2 ^ κ)).map fun i ↦
    ((List.zip queryWeights queries).map fun wq ↦ wq.1 * ofK (novelAt i (K.ofBits wq.2))).sum

/-- The query table is the table of the verifier's induced weight. -/
theorem queryTable_eq {κ : ℕ} (hκ : κ ≤ 64) (queries : List ℕ) (queryWeights : List E) :
    queryTable κ queries queryWeights = tableOf κ (Verifier.inducedWeight κ queries queryWeights) :=
  List.map_congr_left fun i hi ↦
    (inducedWeight_boolPoint hκ queries queryWeights i (List.mem_range.mp hi)).symm

end
end LeanVM.Protocol.Whir.Complete
