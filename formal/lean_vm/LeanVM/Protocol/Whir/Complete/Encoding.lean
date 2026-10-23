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

/-!
# The honest words

A WHIR level commits an interleaved Reed-Solomon codeword: the message on `k + κ` variables is
cut into `2^k` *lanes* along its first `k` variables, lane `j` being the message
`x ↦ g[j + 2^k·⟨x⟩]` on the remaining `κ`, and each lane is encoded by `enc κ R`
(`LeanVM.Protocol.Whir.NovelBasis`). Leaf `p` of the word holds the `2^k` lanes' codeword
entries at the domain point `x_p = K.ofBits p`.

* `stackWord μ q`: the stack's level-0 word (`verify_execution` step 2, `commitStack`): the
  lanes are the stack's `64` blocks (`blockOf`, `LeanVM.Protocol.EndToEnd.Candidates`), the
  leaf stores their `K`-valued codeword entries in reverse lane order. `stackWord_agrees`: it is
  the encoding of the stack in the sense of `Agrees`, on every column.
* `levelWord κ k g`: a deeper level's word, each `E` entry written as its three limbs, the layout
  `_ext_row` regroups (`verifier.py:940-942`).
* `stackTable μ q`: the stack as a table in the WHIR variable order: the six lane variables
  first, then the block offset (`f(u, x) = q(x, u)`), i.e. the stack's index rotated by six
  bits.

What the verifier computes from an honest opening:

* `readRow_stackWord`, `extRow_levelWord`: the rows it reads are the lanes' codeword entries
  (`laneCodes`);
* `dot_laneCodes_eqKernel`: folding them with the level's challenges gives the codeword entry of
  the folded message (folding commutes with the encoder, entrywise);
* `enforcedSum_honest`: the sum a level's queries enforce is the pairing of the folded message
  with the table of the verifier's `inducedWeight` (the column weights of `lem:colweight`);
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

/-- `enc` at a domain point is `encAt` at its index. -/
theorem enc_eq_encAt (κ R : ℕ) (g : (Fin κ → Bool) → E) (v : Fin (2 ^ (κ + R))) :
    enc κ R g v = encAt κ g v := rfl

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

/-- `Enc(t)` at a position as a sum over the table. -/
theorem encAt_msgOf (κ : ℕ) (t : List E) (p : ℕ) :
    encAt κ (msgOf κ t) p = ∑ i ∈ range (2 ^ κ), t.getD i 0 * ofK (novelAt i (K.ofBits p)) := by
  rw [encAt, sum_cube]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [msgOf, bitsToNat_testBit (mem_range.mp hi)]

/-! ## Lanes -/

/-- Lane `j` of a table cut along its first `k` variables: `x ↦ t[j + 2^k·⟨x⟩]`. -/
def laneMsg (κ k : ℕ) (t : List E) (j : ℕ) : (Fin κ → Bool) → E :=
  fun x ↦ t.getD (j + 2 ^ k * bitsToNat x) 0

/-- The `2^k` lanes' codeword entries at the position `p`. -/
def laneCodes (κ k : ℕ) (t : List E) (p : ℕ) : List E :=
  (List.range (2 ^ k)).map fun j ↦ encAt κ (laneMsg κ k t j) p

/-- **Folding commutes with the encoder.** Folding the lanes' entries at a position with the
equality kernel of `r` gives the entry of the encoding of the table folded at `r`. -/
theorem dot_laneCodes_eqKernel (κ : ℕ) (t r : List E) (p : ℕ)
    (ht : t.length = 2 ^ (r.length + κ)) :
    dot (laneCodes κ r.length t p) (eqKernel r) = encAt κ (msgOf κ (foldAll t r)) p := by
  rw [dot_eqKernel _ _ (by simp [laneCodes])]
  have hl : ∀ j ∈ range (2 ^ r.length), (laneCodes κ r.length t p).getD j 0 =
      encAt κ (laneMsg κ r.length t j) p := fun j hj ↦ by
    simp [laneCodes, mem_range.mp hj]
  rw [sum_congr rfl fun j hj ↦ by rw [hl j hj]]
  simp only [encAt, laneMsg, msgOf, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun u _ ↦ ?_
  rw [getD_foldAll r t κ _ ht (bitsToNat_lt u), sum_mul]
  exact sum_congr rfl fun j _ ↦ by ring

/-! ## The level words -/

/-- The three limbs of an entry, the order `_ext_row` reads them. -/
def limbsOf (e : E) : List K := [e.limb 0, e.limb 1, e.limb 2]

/-- `_ext_row` regroups limbs written by `limbsOf`. -/
theorem extRow_flatMap_limbsOf : ∀ l : List E, extRow (l.flatMap limbsOf) = l
  | [] => by simp [extRow]
  | e :: l => by
    simp only [List.flatMap_cons, limbsOf, List.cons_append, List.nil_append, extRow,
      ofLimbs_limb, extRow_flatMap_limbsOf l]

/-- A deeper level's word: leaf `p` holds the `2^k` lanes' entries at `x_p`, three limbs
each. -/
def levelWord (κ k : ℕ) (g : List E) : Word :=
  fun p ↦ (laneCodes κ k g p).flatMap limbsOf

/-- Three limbs per entry. -/
theorem length_flatMap_limbsOf : ∀ l : List E, (l.flatMap limbsOf).length = 3 * l.length
  | [] => rfl
  | e :: l => by
    rw [List.flatMap_cons, List.length_append, length_flatMap_limbsOf l]
    simp [limbsOf]; ring

/-- A level word has `3·2^k` words per leaf, the width the verifier announces. -/
theorem wellShaped_levelWord (κ k : ℕ) (g : List E) : WellShaped (3 * 2 ^ k) (levelWord κ k g) := by
  intro p
  rw [levelWord, length_flatMap_limbsOf]
  simp [laneCodes]

/-- The verifier reads a level word's leaf as the lanes' entries. -/
theorem extRow_levelWord (κ k : ℕ) (g : List E) (p : ℕ) :
    extRow (levelWord κ k g p) = laneCodes κ k g p :=
  extRow_flatMap_limbsOf _

/-! ## The stack's word -/

/-- Block `u` of the stack as a `K`-valued message: cell `⟨x⟩ + 2^(μ−6)·u`. -/
def blockK (μ : ℕ) (q : Column μ) (u : ℕ) : (Fin (μ - laneBits) → Bool) → K :=
  fun x ↦ q.values.getD (bitsToNat x + 2 ^ (μ - laneBits) * u) 0

/-- **The stack's level-0 word**: leaf `p` holds the `64` blocks' codeword entries at `x_p`, in
reverse lane order. -/
def stackWord (μ : ℕ) (q : Column μ) : Word :=
  fun p ↦ ((List.range (2 ^ laneBits)).map fun u ↦ encKAt (μ - laneBits) (blockK μ q u) p).reverse

/-- The stack word has `64` words per leaf, the width `commitStack` announces. -/
theorem wellShaped_stackWord (μ : ℕ) (q : Column μ) :
    WellShaped (2 ^ laneBits) (stackWord μ q) := by
  intro p
  simp [stackWord]

/-- The stack's word is its encoding: it agrees with the encoding of `q` on every column. -/
theorem stackWord_agrees (μ R : ℕ) (q : Column μ) : Agrees μ R (stackWord μ q) q Finset.univ := by
  intro v _ u
  simp only [laneOf, stackWord, List.reverse_reverse]
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
theorem readRow_stackWord {μ : ℕ} (hμ : laneBits ≤ μ) (q : Column μ) (p : ℕ) :
    (stackWord μ q p).reverse.map ofK = laneCodes (μ - laneBits) laneBits (stackTable μ q) p := by
  simp only [stackWord, List.reverse_reverse, List.map_map, laneCodes]
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

private theorem ofK_pow (a : K) (n : ℕ) : ofK (a ^ n) = ofK a ^ n := map_pow (algebraMap K E) a n

private theorem ofK_inv (a : K) : ofK a⁻¹ = (ofK a)⁻¹ := map_inv₀ (algebraMap K E) a

private theorem ofK_one : ofK 1 = 1 := map_one (algebraMap K E)

/-- The verifier's `subspaceRoots`: `[W_0(e_0), …, W_n(e_n)]`. -/
theorem verifier_subspaceRoots_eq (n : ℕ) :
    Verifier.subspaceRoots n =
      (List.range (n + 1)).map fun i ↦ ofK (vanishingAt i (basisVec i)) := by
  have hstep : ∀ j c, ofK (vanishingAt j (basisVec c)) ^ 2 +
      ofK (vanishingAt j (basisVec j)) * ofK (vanishingAt j (basisVec c)) =
        ofK (vanishingAt (j + 1) (basisVec c)) := by
    intro j c
    rw [vanishingAt_succ, ofK_add, ofK_mul, ofK_pow]
  have key : ∀ k j, subspaceRootsAux k (ofK (vanishingAt j (basisVec j)))
      ((List.range' (j + 1) k).map fun c ↦ ofK (vanishingAt j (basisVec c))) =
        (List.range' (j + 1) k).map fun i ↦ ofK (vanishingAt i (basisVec i)) := by
    intro k
    induction k with
    | zero => intro j; simp [subspaceRootsAux]
    | succ k ih =>
      intro j
      simp only [List.range'_succ, List.map_cons, List.map_map, Function.comp_def, hstep,
        subspaceRootsAux]
      rw [← ih (j + 1)]
  have h0 : ∀ a : K, vanishingAt 0 a = a := fun a ↦ by simp [vanishingAt]
  have e1 : ofK (vanishingAt 0 (basisVec 0)) = 1 := by rw [h0, basisVec_zero, ofK_one]
  have hl : (List.range n).map (fun i ↦ eOfNat (2 ^ (i + 1))) =
      (List.range' (0 + 1) n).map fun c ↦ ofK (vanishingAt 0 (basisVec c)) := by
    rw [List.range'_eq_map_range, List.map_map]
    exact List.map_congr_left fun i _ ↦ by simp [h0, eOfNat, basisVec, Nat.add_comm]
  have hr : (List.range n).map ((fun i ↦ ofK (vanishingAt i (basisVec i))) ∘ Nat.succ) =
      (List.range' (0 + 1) n).map fun i ↦ ofK (vanishingAt i (basisVec i)) := by
    rw [List.range'_eq_map_range, List.map_map]
    exact List.map_congr_left fun i _ ↦ by simp [Nat.add_comm]
  rw [Verifier.subspaceRoots, List.range_succ_eq_map, List.map_cons, List.map_map, hl, hr,
    ← key n 0, e1]

/-- The inner loop of `inducedWeight`: from coordinate `s` with `basis = W_s(x)`, the product
gains the affine factors `1 + (1 + Ŵ_c(x))·p_c` and the basis becomes `W_{s+|l|}(x)`. -/
private theorem inducedWeight_inner (roots inverses : List E) (x : K) :
    ∀ (l : List E) (s : ℕ) (p : E),
      (∀ c, s ≤ c → c < s + l.length → roots.getD c 0 = ofK (vanishingAt c (basisVec c))) →
      (∀ c, s ≤ c → c < s + l.length →
        inverses.getD c 0 = (ofK (vanishingAt c (basisVec c)))⁻¹) →
      (l.zipIdx s).foldl (fun (acc : E × E) (cc : E × ℕ) ↦
          (acc.1 * (1 + cc.1 * (1 + acc.2 * inverses.getD cc.2 0)),
            acc.2 ^ 2 + roots.getD cc.2 0 * acc.2)) (p, ofK (vanishingAt s x)) =
        (p * affProd (fun _ ↦ 1) (fun c ↦ 1 + ofK (normVanishingAt (s + c) x)) l,
          ofK (vanishingAt (s + l.length) x))
  | [], s, p, _, _ => by simp [affProd]
  | a :: l, s, p, hr, hi => by
    rw [List.zipIdx_cons, List.foldl_cons]
    have hs : s < s + (a :: l).length := by simp
    simp only [hr s le_rfl hs, hi s le_rfl hs]
    have hW : ofK (vanishingAt s x) ^ 2 + ofK (vanishingAt s (basisVec s)) * ofK (vanishingAt s x) =
        ofK (vanishingAt (s + 1) x) := by
      rw [vanishingAt_succ, ofK_add, ofK_mul, ofK_pow]
    have hn : ofK (vanishingAt s x) * (ofK (vanishingAt s (basisVec s)))⁻¹ =
        ofK (normVanishingAt s x) := by
      rw [normVanishingAt, ofK_mul, ofK_inv]
    rw [hW, hn, inducedWeight_inner roots inverses x l (s + 1) _
      (fun c h1 h2 ↦ hr c (by omega) (by simp; omega))
      (fun c h1 h2 ↦ hi c (by omega) (by simp; omega))]
    simp only [affProd, add_zero, List.length_cons]
    refine Prod.ext ?_ ?_
    · simp only
      rw [show (fun c ↦ 1 + ofK (normVanishingAt (s + 1 + c) x)) =
        fun c ↦ 1 + ofK (normVanishingAt (s + (c + 1)) x) by
          funext c; rw [Nat.add_assoc, Nat.add_comm 1 c]]
      ring
    · simp only
      rw [Nat.add_assoc, Nat.add_comm 1 l.length]

/-- A left fold that adds `f a` at every step is a sum. -/
theorem foldl_eq_add_sum {α : Type} (F : E → α → E) (f : α → E) (hF : ∀ t a, F t a = t + f a) :
    ∀ (l : List α) (t : E), l.foldl F t = t + (l.map f).sum
  | [], t => by simp
  | a :: l, t => by
    rw [List.foldl_cons, foldl_eq_add_sum F f hF l, hF, List.map_cons, List.sum_cons, add_assoc]

/-- **The verifier's induced weight** at a point of at most `n` coordinates is
`Σ_q w_q·Π_c (1 + (1 + Ŵ_c(x_q))·p_c)`, the batched column weights of `lem:colweight`. -/
theorem inducedWeight_eq_sum (n : ℕ) (queries : List ℕ) (queryWeights point : List E)
    (hp : point.length ≤ n) :
    Verifier.inducedWeight n queries queryWeights point =
      ((List.zip queryWeights queries).map fun wq ↦
        wq.1 * affProd (fun _ ↦ 1) (fun c ↦ 1 + ofK (normVanishingAt c (K.ofBits wq.2)))
          point).sum := by
  have hroots : ∀ c, c < n + 1 →
      (Verifier.subspaceRoots n).getD c 0 = ofK (vanishingAt c (basisVec c)) := by
    intro c hc
    rw [verifier_subspaceRoots_eq, List.getD_eq_getElem _ _ (by simpa using hc)]
    simp
  have hinv : ∀ c, c < n + 1 →
      ((Verifier.subspaceRoots n).map fun value ↦ if value = 0 then 0 else value⁻¹).getD c 0 =
        (ofK (vanishingAt c (basisVec c)))⁻¹ := by
    intro c hc
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map, verifier_subspaceRoots_eq]; simpa
      using hc), List.getElem_map]
    have := hroots c hc
    rw [List.getD_eq_getElem _ _ (by rw [verifier_subspaceRoots_eq]; simpa using hc)] at this
    rw [this]
    split
    · rename_i h0; rw [h0, inv_zero]
    · rfl
  simp only [Verifier.inducedWeight]
  rw [foldl_eq_add_sum _ (fun wq : E × ℕ ↦ wq.1 * affProd (fun _ ↦ 1)
    (fun c ↦ 1 + ofK (normVanishingAt c (K.ofBits wq.2))) point) (fun t wq ↦ ?_), zero_add]
  obtain ⟨w, q⟩ := wq
  have h0 : eOfNat q = ofK (vanishingAt 0 (K.ofBits q)) := by simp [eOfNat, vanishingAt]
  have := inducedWeight_inner (Verifier.subspaceRoots n)
    ((Verifier.subspaceRoots n).map fun value ↦ if value = 0 then 0 else value⁻¹) (K.ofBits q)
    point 0 w (fun c _ h2 ↦ hroots c (by omega)) (fun c _ h2 ↦ hinv c (by omega))
  simp only [zero_add] at this
  simp only
  rw [h0, this]

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

/-! ## The enforced sum -/

private theorem list_sum_finset_sum {α : Type} (L : List α) (s : Finset ℕ) (f : α → ℕ → E) :
    (L.map fun a ↦ ∑ i ∈ s, f a i).sum = ∑ i ∈ s, (L.map fun a ↦ f a i).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, sum_add_distrib]

/-- `_enforced_sum` as a sum over the queries. -/
theorem enforcedSum_eq (rows : List (List E)) (folds queryWeights : List E) :
    enforcedSum rows folds queryWeights =
      ((List.zip queryWeights rows).map fun wr ↦ wr.1 * dot wr.2 (eqKernel folds)).sum := by
  rw [enforcedSum, foldl_eq_add_sum _ (fun wr : E × List E ↦ wr.1 * dot wr.2 (eqKernel folds))
    (fun _ _ ↦ rfl), zero_add]

/-- **The sum an honest level's queries enforce.** Reading the lanes of `g` at the query
positions, the enforced sum is the pairing of the table of the verifier's induced weight with
`g` folded at the level's challenges. -/
theorem enforcedSum_honest {κ : ℕ} (hκ : κ ≤ 64) (g r : List E) (queries : List ℕ)
    (queryWeights : List E) (hg : g.length = 2 ^ (r.length + κ)) :
    enforcedSum (queries.map (laneCodes κ r.length g)) r queryWeights =
      dot (tableOf κ (Verifier.inducedWeight κ queries queryWeights)) (foldAll g r) := by
  have hlen : (foldAll g r).length = 2 ^ κ := length_foldAll r g κ hg
  rw [enforcedSum_eq, dot_tableOf _ _ _ hlen, List.zip_map_right, List.map_map]
  have : ∀ wq ∈ List.zip queryWeights queries,
      ((fun wr : E × List E ↦ wr.1 * dot wr.2 (eqKernel r)) ∘ Prod.map id (laneCodes κ r.length g))
        wq = ∑ i ∈ range (2 ^ κ),
          wq.1 * ofK (novelAt i (K.ofBits wq.2)) * (foldAll g r).getD i 0 := by
    intro wq _
    simp only [Function.comp_apply, Prod.map_fst, id_eq, Prod.map_snd]
    rw [dot_laneCodes_eqKernel κ g r _ hg, encAt_msgOf, mul_sum]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [List.map_congr_left this, list_sum_finset_sum]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [inducedWeight_boolPoint hκ _ _ i (mem_range.mp hi), ← List.sum_map_mul_right]

end
end LeanVM.Protocol.Whir.Complete
