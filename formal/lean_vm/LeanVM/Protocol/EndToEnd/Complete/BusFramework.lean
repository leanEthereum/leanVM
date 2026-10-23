/-
  LeanVM.Protocol.EndToEnd.Complete.BusFramework

  The framework blocks of the bus, honestly: the leaves of the state, memory and bytecode
  blocks of each side, their multilinear extensions at the bus point (the verifier's
  fingerprints from the honest claims), and their equality with the instance's boundary tuples.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.BusSide
public import LeanVM.Protocol.EndToEnd.Front.LayoutInstance
public import LeanVM.Protocol.LeanIsa.Bus

/-!
# The framework blocks

The bus phase (`verify_bus_balance`, `python-verifier/verifier.py:534-593` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) evaluates the three framework blocks of each side
itself (`fingerprints`, `verifier.py:560-568`): the state boundary, the memory's `2^logMemory`
rows and the bytecode's `2^logBytecode` rows. The honest leaves of these blocks are, row by row,
`β` plus the fingerprint of the row's tuple (`stateTab`, `memTab`, `bcTab`). This module proves

* `multilinearEval_memTab`, `multilinearEval_bcTab`: their extensions at the block's own
  coordinates are `β` plus the verifier's fingerprint computed from the honest claims (the
  memory limbs' and the counts' extensions there, the index column's `index_mle`, and the
  bytecode's `multilinear_eval` at the point followed by the fingerprint challenges);
* `memTab_eq`, `bcTab_eq`, `stateTab_eq`: every leaf is the fingerprint of the instance's boundary
  tuple of that row (`LeanIsa.boundary`), so the framework's product is the boundary tuples'.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Complete
open LeanVM.Arithmetization Finset CompPoly CMlPolynomialEval

@[expose] public section

/-! ## Extensions of tables of functions -/

/-- The extension of the table of a function on `2^n` rows. -/
theorem multilinearEval_range (n : ℕ) (F : ℕ → E) (z : List E) (hz : z.length = n) :
    multilinearEval ((List.range (2 ^ n)).map F) z =
      ∑ y ∈ range (2 ^ n), F y * eqEval (boolPoint n y) z := by
  rw [multilinearEval_eq_sum n _ z (by simp) hz]
  refine sum_congr rfl fun y hy ↦ ?_
  rw [List.getD_eq_getElem _ _ (by simpa using mem_range.mp hy)]
  simp

/-- `dot` against a prefix of the weights, as a sum. -/
theorem dot_take (w l : List E) (h : l.length ≤ w.length) :
    dot (w.take l.length) l = ∑ i ∈ range l.length, w.getD i 0 * l.getD i 0 := by
  rw [dot_eq_sum _ _ (by simp; omega)]
  simp only [List.length_take, min_eq_left h]
  refine sum_congr rfl fun i hi ↦ ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, mem_range.mp hi, ↓reduceIte]

/-- **The extension of a fingerprint table**: `β + Σ_i u_i · c_i(y) + g(y)` extends to
`β + Σ_i u_i · c̃_i + g̃`. -/
theorem multilinearEval_fingerprint (n : ℕ) (β : E) (u : List E) (cs : List (ℕ → E))
    (hcs : cs.length ≤ u.length) (g : ℕ → E) (z : List E) (hz : z.length = n) :
    multilinearEval ((List.range (2 ^ n)).map fun y ↦
        β + dot (u.take cs.length) (cs.map (· y)) + g y) z =
      β + dot (u.take cs.length)
          (cs.map fun c ↦ ∑ y ∈ range (2 ^ n), c y * eqEval (boolPoint n y) z) +
        ∑ y ∈ range (2 ^ n), g y * eqEval (boolPoint n y) z := by
  rw [multilinearEval_range n _ z hz]
  have h1 := dot_take u (cs.map fun c ↦ ∑ y ∈ range (2 ^ n), c y * eqEval (boolPoint n y) z)
    (by simpa using hcs)
  have h2 : ∀ y, dot (u.take cs.length) (cs.map (· y)) =
      ∑ i ∈ range cs.length, u.getD i 0 * (cs.map (· y)).getD i 0 := fun y ↦ by
    simpa using dot_take u (cs.map (· y)) (by simpa using hcs)
  simp only [List.length_map] at h1
  rw [h1]
  simp only [h2, add_mul, sum_add_distrib, sum_mul]
  rw [← mul_sum, sum_eqEval_boolPoint n z hz, mul_one, sum_comm]
  refine congrArg (· + _) (congrArg (β + ·) (sum_congr rfl fun i hi ↦ ?_))
  have hi' := mem_range.mp hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi',
    Option.map_some, Option.getD_some, mul_sum]
  exact sum_congr rfl fun y _ ↦ by ring

/-- The table's coordinate functions' extensions: a constant. -/
theorem sum_const_eqEval (n : ℕ) (a : E) (z : List E) (hz : z.length = n) :
    ∑ y ∈ range (2 ^ n), a * eqEval (boolPoint n y) z = a := by
  rw [← mul_sum, sum_eqEval_boolPoint n z hz, mul_one]

/-- The table's coordinate functions' extensions: a list's entries. -/
theorem sum_getD_eqEval (n : ℕ) (t : List E) (ht : t.length = 2 ^ n) (z : List E)
    (hz : z.length = n) :
    ∑ y ∈ range (2 ^ n), t.getD y 0 * eqEval (boolPoint n y) z = multilinearEval t z :=
  (multilinearEval_eq_sum n t z ht hz).symm

/-! ## The index column -/

/-- Scaling a table scales its fold. -/
theorem foldPairs_map_mul (r c : E) : ∀ t : List E,
    foldPairs r (t.map (c * ·)) = (foldPairs r t).map (c * ·)
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
    simp only [List.map_cons, foldPairs, foldPairs_map_mul r c t]
    congr 1
    ring

/-- Scaling a table scales its extension. -/
theorem multilinearEval_map_mul (c : E) : ∀ (p t : List E),
    multilinearEval (t.map (c * ·)) p = c * multilinearEval t p
  | [], [] => by simp [multilinearEval]
  | [], a :: t => by simp [multilinearEval]
  | r :: p, t => by
    rw [Whir.Complete.multilinearEval_cons, foldPairs_map_mul, multilinearEval_map_mul c p,
      Whir.Complete.multilinearEval_cons]

/-- The powers of `a`, `2^n` of them. -/
def powList (a : E) (n : ℕ) : List E := (List.range (2 ^ n)).map (a ^ ·)

theorem foldPairs_powList (r a : E) (n : ℕ) :
    foldPairs r (powList a (n + 1)) = (powList (a ^ 2) n).map ((1 + r * (1 + a)) * ·) := by
  apply List.ext_getElem
  · simp [powList, Whir.Complete.length_foldPairs, pow_succ]
  · intro j h1 h2
    simp only [List.length_map, powList, List.length_range] at h2
    have h := getD_foldPairs r (powList a (n + 1)) j (by simp [powList, pow_succ]; omega)
    rw [List.getD_eq_getElem _ _ h1] at h
    rw [h]
    simp only [powList, List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by simp [pow_succ]; omega),
      List.getD_eq_getElem _ _ (by simp [pow_succ]; omega)]
    simp only [List.getElem_map, List.getElem_range]
    rw [pow_succ, ← pow_mul, mul_comm 2 j]
    ring

/-- **`index_mle` is the extension of the powers**, with the accumulator. -/
theorem indexMleFrom_eq : ∀ (p : List E) (a acc : E),
    indexMleFrom a p acc = acc * multilinearEval (powList a p.length) p
  | [], a, acc => by simp [indexMleFrom, powList, multilinearEval]
  | r :: p, a, acc => by
    rw [indexMleFrom, indexMleFrom_eq p, List.length_cons, Whir.Complete.multilinearEval_cons,
      foldPairs_powList, multilinearEval_map_mul]
    ring

/-- `index_mle(z)` is the extension of `[1, g, g², …]` at `z`. -/
theorem indexMle_eq (z : List E) :
    indexMle z = ∑ y ∈ range (2 ^ z.length), Verifier.gpow y * eqEval (boolPoint z.length y) z := by
  rw [indexMle, indexMleFrom_eq, one_mul, powList, multilinearEval_range _ _ z rfl]
  rfl

/-! ## The columns of the stack -/

section Stack

variable (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- An instance column read off the stack, as a list in `E`. -/
def colList (c : Col) : List E := ((inst prog s).column q c).values.toList.map ofK

theorem length_colList (c : Col) : (colList prog s q c).length = 2 ^ kappa prog s c := by
  simp [colList]; rfl

theorem getD_colList (c : Col) (y : ℕ) (hy : y < 2 ^ kappa prog s c) :
    (colList prog s q c).getD y 0 = ofK (((inst prog s).column q c).values.get ⟨y, hy⟩) := by
  rw [List.getD_eq_getElem _ _ (by rw [length_colList]; exact hy)]
  simp [colList, Vector.get_eq_getElem]

/-- The list's extension is the column's true value. -/
theorem multilinearEval_colList (c : Col) (z : Vector E (kappa prog s c)) :
    multilinearEval (colList prog s q c) z.toList = colEval prog s q c z := by
  unfold colEval eval₂Mle
  refine Eq.trans ?_ (multilinearEval_eq_evalMle (n := kappa prog s c)
    (CMlPolynomialEval.map (algebraMap K E) ((inst prog s).column q c).values) z)
  congr 1
  have h : ∀ {n : ℕ} (v : Vector K n),
      v.toList.map ofK = (Vector.map (fun a ↦ algebraMap K E a) v).toList := fun v ↦ by
    rw [Vector.toList_map]; rfl
  exact h _

/-! ## The framework tables -/

/-- The state block's one leaf: `β` plus the fingerprint of `(SEP_STATE, pc, g⁰)`. -/
def stateTab (β : E) (w : List E) (pc : E) : List E := [β + dot (w.take 3) [sepState, pc, gpow 0]]

/-- The memory block's leaves: `β` plus the fingerprint of `(SEP_MEM, gⁱ, count_i, m_i)`. -/
def memTab (β : E) (w : List E) (cnt : List E) : List E :=
  (List.range (2 ^ s.logMem)).map fun y ↦ β + dot (w.take 6)
    ([sepMem, Verifier.gpow y, cnt.getD y 0] ++
      [(colList prog s q (memCol 0)).getD y 0, (colList prog s q (memCol 1)).getD y 0,
        (colList prog s q (memCol 2)).getD y 0])

/-- The bytecode block's leaves: `β` plus the fingerprint of `(SEP_BYTECODE, gⁱ, count_i)` and
of the instruction's sixteen slots. -/
def bcTab (β : E) (w : List E) (cnt : List E) : List E :=
  (List.range (2 ^ prog.logSize)).map fun y ↦
    β + (dot (w.take 3) [sepBytecode, Verifier.gpow y, cnt.getD y 0] +
      ((List.range 16).map fun k ↦
        w.getD k 0 * ((bytecodeWords prog).map ofK).getD (y + 2 ^ prog.logSize * k) 0).sum)

theorem length_memTab (β : E) (w cnt : List E) :
    (memTab prog s q β w cnt).length = 2 ^ s.logMem := by simp [memTab]

theorem length_bcTab (β : E) (w cnt : List E) :
    (bcTab prog β w cnt).length = 2 ^ prog.logSize := by simp [bcTab]

/-- **The memory block's extension** is `β` plus the verifier's memory fingerprint at the honest
claims. -/
theorem multilinearEval_memTab (β : E) (w : List E) (hw : 6 ≤ w.length) (cnt : List E)
    (hcnt : cnt.length = 2 ^ s.logMem) (z : List E) (hz : z.length = s.logMem) :
    multilinearEval (memTab prog s q β w cnt) z =
      β + dot (w.take 6) ([sepMem, indexMle z, multilinearEval cnt z] ++
        [multilinearEval (colList prog s q (memCol 0)) z,
          multilinearEval (colList prog s q (memCol 1)) z,
          multilinearEval (colList prog s q (memCol 2)) z]) := by
  have h := multilinearEval_fingerprint s.logMem β w
    [fun _ ↦ sepMem, Verifier.gpow, fun y ↦ cnt.getD y 0,
      fun y ↦ (colList prog s q (memCol 0)).getD y 0,
      fun y ↦ (colList prog s q (memCol 1)).getD y 0,
      fun y ↦ (colList prog s q (memCol 2)).getD y 0] (by simpa using hw) (fun _ ↦ 0) z hz
  have hm : ∀ i : Fin 4, (colList prog s q (memCol i)).length = 2 ^ s.logMem := fun i ↦
    length_colList prog s q (memCol i)
  simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil, zero_mul,
    sum_const_zero, add_zero, sum_const_eqEval s.logMem _ z hz,
    sum_getD_eqEval s.logMem _ hcnt z hz, sum_getD_eqEval s.logMem _ (hm 0) z hz,
    sum_getD_eqEval s.logMem _ (hm 1) z hz, sum_getD_eqEval s.logMem _ (hm 2) z hz] at h
  rw [show ∑ y ∈ range (2 ^ s.logMem), Verifier.gpow y * eqEval (boolPoint s.logMem y) z =
    indexMle z by rw [indexMle_eq, hz]] at h
  exact h

/-- The bytecode's slots against the fingerprint weights extend to the bytecode's extension at
the point followed by the weights' challenges. -/
theorem sum_bytecode_eqEval (alphas : List E) (halpha : alphas.length = 4) (z : List E)
    (hz : z.length = prog.logSize) :
    ∑ y ∈ range (2 ^ prog.logSize), ((List.range 16).map fun k ↦
        (eqKernel alphas).getD k 0 *
          ((bytecodeWords prog).map ofK).getD (y + 2 ^ prog.logSize * k) 0).sum *
        eqEval (boolPoint prog.logSize y) z =
      multilinearEval ((bytecodeWords prog).map ofK) (z ++ alphas) := by
  have hlen : ((bytecodeWords prog).map ofK).length = 2 ^ (z.length + 4) := by
    rw [List.length_map, length_bytecodeWords, hz]
  rw [multilinearEval_eq_foldAll, foldAll_append, ← multilinearEval_eq_foldAll,
    multilinearEval_eq_sum 4 _ alphas (length_foldAll z _ 4 hlen) halpha]
  simp only [← sum_range_eq_list, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [getD_foldAll z _ 4 k hlen (mem_range.mp hk), sum_mul, hz]
  refine sum_congr rfl fun y _ ↦ ?_
  rw [getD_eqKernel alphas k (by rw [halpha]; exact mem_range.mp hk), halpha]
  ring

/-- **The bytecode block's extension** is `β` plus the verifier's bytecode fingerprint at the
honest claim. -/
theorem multilinearEval_bcTab (β : E) (alphas : List E) (halpha : alphas.length = 4)
    (cnt : List E) (hcnt : cnt.length = 2 ^ prog.logSize) (z : List E)
    (hz : z.length = prog.logSize) :
    multilinearEval (bcTab prog β (eqKernel alphas) cnt) z =
      β + (dot ((eqKernel alphas).take 3) [sepBytecode, indexMle z, multilinearEval cnt z] +
        multilinearEval ((bytecodeWords prog).map ofK) (z ++ alphas)) := by
  have hw : 3 ≤ (eqKernel alphas).length := by rw [length_eqKernel, halpha]; norm_num
  have h := multilinearEval_fingerprint prog.logSize β (eqKernel alphas)
    [fun _ ↦ sepBytecode, Verifier.gpow, fun y ↦ cnt.getD y 0] (by simpa using hw)
    (fun y ↦ ((List.range 16).map fun k ↦
        (eqKernel alphas).getD k 0 *
          ((bytecodeWords prog).map ofK).getD (y + 2 ^ prog.logSize * k) 0).sum) z hz
  simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil,
    sum_const_eqEval prog.logSize _ z hz, sum_getD_eqEval prog.logSize _ hcnt z hz,
    sum_bytecode_eqEval prog alphas halpha z hz] at h
  rw [show ∑ y ∈ range (2 ^ prog.logSize), Verifier.gpow y * eqEval (boolPoint prog.logSize y) z =
    indexMle z by rw [indexMle_eq, hz]] at h
  rw [← add_assoc, ← h, bcTab]
  congr 1
  exact List.map_congr_left fun y _ ↦ by ring

/-! ## The framework leaves are the boundary tuples' fingerprints -/

/-- The fingerprint of a tuple: `β` plus the weights against its sixteen slots in `E`. -/
def fpV (β : E) (w : List E) (v : Vector K 16) : E := β + dot w (v.toList.map ofK)

/-- The slots of a tuple of a separator and a message, in `E`. -/
theorem getD_tupleOf (σ : K) (m : Array K) (k : ℕ) (hk : k < 16) :
    ((tupleOf σ m).toList.map ofK).getD k 0 =
      if k = 0 then ofK σ else ofK (m[k - 1]?.getD 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simp only [List.getElem_map, Vector.getElem_toList, tupleOf, Vector.getElem_ofFn]
  split_ifs <;> rfl

/-- The fingerprint of a separator and a message. -/
theorem fpV_tupleOf (β : E) (w : List E) (hw : w.length = 16) (σ : K) (m : Array K)
    (hm : m.size ≤ 15) :
    fpV β w (tupleOf σ m) =
      β + (w.getD 0 0 * ofK σ + ∑ i ∈ range m.size, w.getD (i + 1) 0 * ofK (m[i]?.getD 0)) := by
  rw [fpV, dot_eq_sum _ _ (by simp [hw]), hw, sum_range_succ']
  refine congrArg (β + ·) ?_
  rw [add_comm]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [getD_tupleOf σ m 0 (by norm_num), ite_eq_left rfl]
  · rw [show 15 = m.size + (15 - m.size) by omega, sum_range_add]
    have hz : ∑ x ∈ range (15 - m.size), w.getD (m.size + x + 1) 0 *
        ((tupleOf σ m).toList.map ofK).getD (m.size + x + 1) 0 = 0 := by
      refine sum_eq_zero fun x hx ↦ ?_
      have := mem_range.mp hx
      rw [getD_tupleOf σ m _ (by omega), ite_eq_right (by omega), Nat.add_sub_cancel,
        Array.getElem?_eq_none (by omega)]
      simp
    rw [hz, add_zero]
    refine sum_congr rfl fun i hi ↦ ?_
    have := mem_range.mp hi
    rw [getD_tupleOf σ m _ (by omega), ite_eq_right (by omega), Nat.add_sub_cancel]

/-- `dot` against a prefix of the weights, expanded. -/
theorem dot_take_eq (w l : List E) (n : ℕ) (hn : l.length = n) (h : n ≤ w.length) :
    dot (w.take n) l = ∑ i ∈ range n, w.getD i 0 * l.getD i 0 := by
  subst hn; exact dot_take w l h

/-- A bytecode word: instruction `i`'s slot `k`. -/
theorem getD_bytecodeWords (i : Fin (2 ^ prog.logSize)) (k : ℕ) (hk : k < 16) :
    ((bytecodeWords prog).map ofK).getD (i.val + 2 ^ prog.logSize * k) 0 =
      ofK ((encodeSlots (prog.code i)).toList.getD k 0) := by
  rw [List.getD_eq_getElem (encodeSlots (prog.code i)).toList _ (by simpa using hk),
    Vector.getElem_toList]
  have hlt : i.val + 2 ^ prog.logSize * k < 2 ^ (prog.logSize + 4) := by
    rw [pow_add]; exact add_mul_lt i.isLt (by norm_num; omega)
  rw [List.getD_eq_getElem _ _ (by simpa [length_bytecodeWords] using hlt)]
  simp only [List.getElem_map, bytecodeWords_eq_column, Vector.getElem_toList, bytecodeColumn,
    Vector.getElem_ofFn]
  have hs : (cubeSplit prog.logSize 4).symm ⟨i.val + 2 ^ prog.logSize * k, hlt⟩ =
      (i, ⟨k, by norm_num; omega⟩) := by
    rw [Equiv.symm_apply_eq, cubeSplit_apply]
    rfl
  simp only [hs]
  rfl

/-- `ofK` of a power of the generator. -/
theorem ofK_gpow (n : ℕ) : ofK (Parameters.gpow n) = Verifier.gpow n := by
  show algebraMap K E (g ^ n) = gen ^ n
  rw [map_pow]
  rfl

/-- A memory column's entry is the instance's cell. -/
theorem getD_colList_mem (i : Fin 4) (x : Fin (2 ^ s.logMem)) :
    (colList prog s q (memCol i)).getD x 0 =
      ofK (cell Blake2sFlock.blake2sFlockSpec prog s q (memCol i) x) :=
  getD_colList prog s q (memCol i) x x.isLt

variable {prog s q} in
/-- **The memory block's leaves are the boundary tuples' fingerprints.** -/
theorem memTab_getD (β : E) (w : List E) (hw : w.length = 16) (cnt : List E)
    (x : Fin (2 ^ s.logMem)) (c : K) (hc : cnt.getD x 0 = ofK c) :
    (memTab prog s q β w cnt).getD x 0 =
      fpV β w (tupleOf (Parameters.gpow 1)
        (#[Parameters.gpow x, c] ++ (memLimbs Blake2sFlock.blake2sFlockSpec s q x).toArray)) := by
  rw [fpV_tupleOf β w hw _ _ (by simp), List.getD_eq_getElem _ _ (by simp [memTab])]
  simp only [memTab, List.getElem_map, List.getElem_range]
  rw [dot_take_eq w _ 6 rfl (by omega)]
  simp only [List.length_cons, List.length_nil, Array.size_append, List.size_toArray, memLimbs]
  simp only [sum_range_succ, sum_range_zero, zero_add, List.getD_cons_zero,
    List.getD_cons_succ, List.cons_append, List.nil_append]
  rw [hc, getD_colList_mem prog s q 0 x, getD_colList_mem prog s q 1 x,
    getD_colList_mem prog s q 2 x]
  simp only [ofK_gpow, sepMem, Fin.isValue, Array.getElem?_append, List.getElem?_toArray]
  simp [gen, Verifier.gpow]
  simp only [ofK_gpow, Verifier.gpow, gen]
  ring

/-- The eight entry coordinates of an instruction, listed. -/
theorem entryList_eq (i : Fin (2 ^ prog.logSize)) :
    entryList i = [(entry (prog.code i))[0], (entry (prog.code i))[1], (entry (prog.code i))[2],
      (entry (prog.code i))[3], (entry (prog.code i))[4], (entry (prog.code i))[5],
      (entry (prog.code i))[6], (entry (prog.code i))[7]] := rfl

variable {prog} in
/-- **The bytecode block's leaves are the boundary tuples' fingerprints.** -/
theorem bcTab_getD (β : E) (w : List E) (hw : w.length = 16) (cnt : List E)
    (i : Fin (2 ^ prog.logSize)) (c : K) (hc : cnt.getD i 0 = ofK c) :
    (bcTab prog β w cnt).getD i 0 =
      fpV β w (tupleOf (Parameters.gpow 2) (#[Parameters.gpow i, c] ++ (entryList i).toArray)) := by
  rw [fpV_tupleOf β w hw _ _ (by simp [entryList_eq]),
    List.getD_eq_getElem _ _ (by simp [bcTab])]
  simp only [bcTab, List.getElem_map, List.getElem_range]
  rw [dot_take_eq w _ 3 rfl (by omega)]
  have h16 : ((List.range 16).map fun k ↦
      w.getD k 0 * ((bytecodeWords prog).map ofK).getD (i.val + 2 ^ prog.logSize * k) 0).sum =
      ∑ k ∈ range 16, w.getD k 0 * ofK ((encodeSlots (prog.code i)).toList.getD k 0) := by
    rw [← sum_range_eq_list]
    exact sum_congr rfl fun k hk ↦ by rw [getD_bytecodeWords prog i k (mem_range.mp hk)]
  rw [h16]
  simp only [entryList_eq, List.length_cons, List.length_nil, Array.size_append, List.size_toArray]
  simp only [sum_range_succ, sum_range_zero, zero_add, List.getD_cons_zero,
    List.getD_cons_succ, hc]
  simp [encodeSlots, ofK_gpow, sepBytecode, Verifier.gpow, gen]
  ring

/-- The state block's leaf on the push side is the initial state's fingerprint. -/
theorem stateTab_push (β : E) (w : List E) (hw : w.length = 16) :
    stateTab β w (Verifier.gpow 0) = [fpV β w (tupleOf (Parameters.gpow 0) #[1, 1])] := by
  rw [stateTab, fpV_tupleOf β w hw _ _ (by simp), dot_take_eq w _ 3 rfl (by omega)]
  simp [sum_range_succ, sepState, Verifier.gpow, Parameters.gpow]
  ring

/-- The state block's leaf on the pull side is the final state's fingerprint. -/
theorem stateTab_pull (β : E) (w : List E) (hw : w.length = 16) :
    stateTab β w (Verifier.gpow (2 ^ prog.logSize - 1)) =
      [fpV β w (tupleOf (Parameters.gpow 0) #[prog.finalPc, 1])] := by
  rw [stateTab, fpV_tupleOf β w hw _ _ (by simp), dot_take_eq w _ 3 rfl (by omega)]
  simp [sum_range_succ, sepState, Program.finalPc, ofK_gpow]
  simp [Verifier.gpow]
  ring

/-- A list read entry by entry from a function of the indices. -/
theorem eq_map_finRange (l : List E) (n : ℕ) (hl : l.length = n) (f : Fin n → E)
    (h : ∀ x : Fin n, l.getD x 0 = f x) : l = (List.finRange n).map f := by
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  have := h ⟨i, by omega⟩
  rw [List.getD_eq_getElem _ _ h1] at this
  simp [this]

/-- The honest counts of the push side: ones. -/
def onesList (n : ℕ) : List E := List.replicate (2 ^ n) 1

theorem getD_onesList (n x : ℕ) (hx : x < 2 ^ n) : (onesList n).getD x 0 = ofK 1 := by
  rw [onesList, List.getD_eq_getElem _ _ (by simpa using hx), List.getElem_replicate]
  exact (map_one (algebraMap K E)).symm

/-- **The push side's framework product** is the push boundary tuples' fingerprint product. -/
theorem prod_framework_push (β : E) (w : List E) (hw : w.length = 16) :
    (stateTab β w (Verifier.gpow 0)).prod * (memTab prog s q β w (onesList s.logMem)).prod *
        (bcTab prog β w (onesList prog.logSize)).prod =
      (((inst prog s).boundaryTuples q .push).map (fpV β w)).prod := by
  rw [boundaryTuples_push Blake2sFlock.blake2sFlockSpec s q, stateTab_push β w hw]
  simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, List.map_map]
  rw [eq_map_finRange (memTab prog s q β w (onesList s.logMem)) _ (length_memTab ..) _
      fun x ↦ memTab_getD β w hw _ x 1 (getD_onesList _ _ x.isLt),
    eq_map_finRange (bcTab prog β w (onesList prog.logSize)) _ (length_bcTab ..) _
      fun i ↦ bcTab_getD β w hw _ i 1 (getD_onesList _ _ i.isLt)]
  rfl

/-- **The pull side's framework product** is the pull boundary tuples' fingerprint product. -/
theorem prod_framework_pull (β : E) (w : List E) (hw : w.length = 16) :
    (stateTab β w (Verifier.gpow (2 ^ prog.logSize - 1))).prod *
        (memTab prog s q β w (colList prog s q (memCol 3))).prod *
        (bcTab prog β w (colList prog s q bfcntCol)).prod =
      (((inst prog s).boundaryTuples q .pull).map (fpV β w)).prod := by
  rw [boundaryTuples_pull Blake2sFlock.blake2sFlockSpec s q, stateTab_pull prog β w hw]
  simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, List.map_map]
  rw [eq_map_finRange (memTab prog s q β w (colList prog s q (memCol 3))) _ (length_memTab ..) _
      fun x ↦ memTab_getD β w hw _ x _ (getD_colList_mem prog s q 3 x),
    eq_map_finRange (bcTab prog β w (colList prog s q bfcntCol)) _ (length_bcTab ..) _
      fun i ↦ bcTab_getD β w hw _ i _ (getD_colList prog s q bfcntCol i i.isLt)]
  rfl

end Stack

end
end LeanVM.Protocol.EndToEnd.Complete
