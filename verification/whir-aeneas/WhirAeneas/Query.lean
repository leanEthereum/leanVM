import WhirAeneas.Fold
import Whir.WHIRNativeArithmetic

/-! The query phase of the actual generated replay: the level-0 and later-level
enforced sums of the opened rows are the model's `Protocol.enforced`, under
`ArithModel` and the opening verifier's word arithmetic `RowModel`. -/
namespace WhirAeneas.Query
open Aeneas Aeneas.Std ReplaySource Whir Whir.Concrete WhirAeneas.Fold

/-- The opening verifier's word operations: a word of `K` scales an element as the
model's `E.ofK`, three words are an element's limbs through `ofLimbs`, and a query
is the `K` element whose bits are its index. All leave the state unchanged. -/
structure RowModel {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)
    (encode : E → Concrete.E) (encodeK : K → Concrete.K)
    (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E) (index : Q → Nat) : Prop where
  mul_k_add : ∀ s a k d, ∃ y, inst.mul_k_add s a k d = .ok (y, s) ∧
    encode y = encode a * Concrete.E.ofK (encodeK k) + encode d
  e_of_limbs : ∀ s (limbs : Array K 3#usize) k0 k1 k2, limbs.val = [k0, k1, k2] →
    ∃ y, inst.e_of_limbs s limbs = .ok (y, s) ∧ encode y = ofLimbs (encodeK k0) (encodeK k1) (encodeK k2)
  query_point : ∀ s q, ∃ y, inst.query_point s q = .ok (y, s) ∧
    encode y = Concrete.E.ofK (UInt64.ofNat (index q))

theorem foldl_range_map (n : Nat) (f : Nat → Concrete.E) :
    ((List.range n).map f).foldl (· + ·) 0 = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, List.range_succ, List.map_append, List.foldl_append]
    simp

theorem foldl_tab (n : Nat) (f : Nat → Concrete.E) :
    (Concrete.tab n f).foldl (· + ·) 0 = ∑ i ∈ Finset.range n, f i := by
  rw [← foldl_range_map, Concrete.tab, ← Array.foldl_toList]
  simp



theorem map_getElem! {α β : Type} [Inhabited β] (l : List α) (f : α → β) (i : Nat)
    (h : i < l.length) : (l.map f)[i]! = f l[i] := by
  rw [getElem!_pos (l.map f) i (by simpa using h)]
  simp

theorem toArray_getElem! {α : Type} [Inhabited α] (l : List α) (i : Nat) : l.toArray[i]! = l[i]! := by
  by_cases h : i < l.length
  · rw [getElem!_pos l.toArray i (by simpa using h), getElem!_pos l i h]; simp
  · rw [getElem!_neg l.toArray i (by simpa using h), getElem!_neg l i h]
/-! ## Level-0 rows of words -/

section Base
variable {V R K Q E : Type} (copyE : core.marker.Copy E) (copyK : core.marker.Copy K)
  (inst : verifier.OpeningVerifier V R K Q E) (encode : E → Concrete.E)
  (const : primitives.field.gf2_64x3.F192 → Concrete.E) (encodeK : K → Concrete.K)
  (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E) (index : Q → Nat)

theorem base_inner_loop_eq (hr : RowModel inst encode encodeK ofLimbs index)
    (eq : Slice E) (row : Slice K) (s0 : E) :
    ∀ (m : Nat) (j : Usize) (s : E) (v : V), min eq.val.length row.val.length - j.val = m →
      j.val ≤ min eq.val.length row.val.length →
      encode s = encode s0 + ∑ i ∈ Finset.range j.val,
        (eq.val.map encode)[i]! * Concrete.E.ofK (row.val.map encodeK)[i]! →
      ∃ y, whir.verify.base_inner_loop inst v eq row s j = .ok (y, v) ∧
        encode y = encode s0 + ∑ i ∈ Finset.range (min eq.val.length row.val.length),
          (eq.val.map encode)[i]! * Concrete.E.ofK (row.val.map encodeK)[i]! := by
  intro m
  induction m with
  | zero =>
    intro j s v hm hj hs
    have hjl : j.val = min eq.val.length row.val.length := by omega
    refine ⟨s, ?_, by rw [← hjl]; exact hs⟩
    unfold whir.verify.base_inner_loop
    apply loop_done
    have hge : ¬ (j < core.cmp.impls.OrdUsize.min (Slice.len eq) (Slice.len row)) := by
      simp only [UScalar.lt_equiv, core.cmp.impls.OrdUsize.min_val, Slice.len_val, Slice.length]; omega
    simp only [whir.verify.base_inner_loop.body, lift, Std.bind_ok, hge, ↓reduceIte]
  | succ k ih =>
    intro j s v hm hj hs
    have hjl : j.val < min eq.val.length row.val.length := by omega
    have hje : j.val < eq.val.length := by omega
    have hjr : j.val < row.val.length := by omega
    obtain ⟨s1, hs1, es1⟩ := hr.mul_k_add v eq.val[j.val] row.val[j.val] s
    have hbody : whir.verify.base_inner_loop.body inst eq row v s j =
        .ok (.cont (v, s1, Std.Usize.wrapping_add j 1#usize)) := by
      have hlt : j < core.cmp.impls.OrdUsize.min (Slice.len eq) (Slice.len row) := by
        simp only [UScalar.lt_equiv, core.cmp.impls.OrdUsize.min_val, Slice.len_val, Slice.length]; omega
      simp only [whir.verify.base_inner_loop.body, lift, Std.bind_ok, hlt, ↓reduceIte,
        slice_index eq j hje, slice_index row j hjr, hs1]
      all_goals rfl
    have hsucc := succ_val j _ hjl (by scalar_tac)
    obtain ⟨y, hy, ey⟩ := ih (Std.Usize.wrapping_add j 1#usize) s1 v (by omega) (by omega) (by
      rw [hsucc, Finset.sum_range_succ, es1, hs]
      simp [getElem!_pos, hje, hjr]
      ring)
    refine ⟨y, ?_, ey⟩
    unfold whir.verify.base_inner_loop
    rw [loop_cont hbody]
    unfold whir.verify.base_inner_loop at hy
    exact hy

/-- One row's inner product, interpreted: `sum_j eq_j k_j` over the common length. -/
def baseInner (eqE : List Concrete.E) (row : List Concrete.K) : Concrete.E :=
  ∑ j ∈ Finset.range (min eqE.length row.length), eqE[j]! * Concrete.E.ofK row[j]!

theorem base_inner_eq (hr : RowModel inst encode encodeK ofLimbs index) (v : V)
    (eq : Slice E) (row : Slice K) (zero : E) (hz : encode zero = 0) :
    ∃ y, whir.verify.base_inner copyE copyK inst v eq row zero = .ok (y, v) ∧
      encode y = baseInner (eq.val.map encode) (row.val.map encodeK) := by
  obtain ⟨y, hy, ey⟩ := base_inner_loop_eq inst encode encodeK ofLimbs index hr eq row zero _ 0#usize
    zero v rfl (by simp) (by simp)
  refine ⟨y, by simpa [whir.verify.base_inner] using hy, ?_⟩
  rw [ey, hz, zero_add, baseInner]
  simp

/-- The level-0 loop without padding (a configuration with no padding never folds one): each
row's inner product starts from zero. -/
theorem base_loop_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (weights : Slice E) (queries : Slice Q)
    (rows : alloc.vec.Vec (alloc.vec.Vec K)) (eq : alloc.vec.Vec E) (zero : E)
    (hz : encode zero = 0) :
    ∀ (m : Nat) (i : Usize) (acc : E) (v : V),
      min (min rows.val.length weights.val.length) queries.val.length - i.val = m →
      i.val ≤ min (min rows.val.length weights.val.length) queries.val.length →
      encode acc = ∑ i' ∈ Finset.range i.val, (weights.val.map encode)[i']! *
        baseInner (eq.val.map encode) ((rows.val.map fun r => r.val.map encodeK)[i']!) →
      ∃ y, whir.verify.BaseRows.enforced_sum_loop copyK inst v weights queries none rows eq zero acc i =
          .ok (y, v) ∧
        encode y = ∑ i' ∈ Finset.range (min (min rows.val.length weights.val.length) queries.val.length),
          (weights.val.map encode)[i']! *
            baseInner (eq.val.map encode) ((rows.val.map fun r => r.val.map encodeK)[i']!) := by
  intro m
  induction m with
  | zero =>
    intro i acc v hm hi hacc
    have hil : i.val = min (min rows.val.length weights.val.length) queries.val.length := by omega
    refine ⟨acc, ?_, by rw [← hil]; exact hacc⟩
    unfold whir.verify.BaseRows.enforced_sum_loop
    apply loop_done
    have : ¬ (i < core.cmp.impls.OrdUsize.min (core.cmp.impls.OrdUsize.min (alloc.vec.Vec.len rows)
        (Slice.len weights)) (Slice.len queries)) := by
      simp only [UScalar.lt_equiv, core.cmp.impls.OrdUsize.min_val, Slice.len_val, Slice.length,
        alloc.vec.Vec.len_val, alloc.vec.Vec.length]; omega
    simp only [whir.verify.BaseRows.enforced_sum_loop.body, lift, Std.bind_ok, bind_tc_ok, this,
      ↓reduceIte]
  | succ k ih =>
    intro i acc v hm hi hacc
    have hil : i.val < min (min rows.val.length weights.val.length) queries.val.length := by omega
    have hir : i.val < rows.val.length := by omega
    have hiw : i.val < weights.val.length := by omega
    obtain ⟨inner, hin, ein⟩ := base_inner_eq inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst
      copyK inst encode encodeK ofLimbs index hr v
      (alloc.vec.Vec.deref eq) (alloc.vec.Vec.deref rows.val[i.val]) zero hz
    obtain ⟨acc1, hacc1, eacc1⟩ := h.mul_add v weights.val[i.val] inner acc
    have hbody : whir.verify.BaseRows.enforced_sum_loop.body copyK inst weights queries rows eq zero v none
        acc i = .ok (.cont (v, none, acc1, Std.Usize.wrapping_add i 1#usize)) := by
      have hlt : i < core.cmp.impls.OrdUsize.min (core.cmp.impls.OrdUsize.min (alloc.vec.Vec.len rows)
          (Slice.len weights)) (Slice.len queries) := by
        simp only [UScalar.lt_equiv, core.cmp.impls.OrdUsize.min_val, Slice.len_val, Slice.length,
          alloc.vec.Vec.len_val, alloc.vec.Vec.length]; omega
      simp only [whir.verify.BaseRows.enforced_sum_loop.body, lift, Std.bind_ok, hlt,
        ↓reduceIte, vec_index rows i hir, slice_index weights i hiw]
      all_goals simp [hin, hacc1]
    have hsucc := succ_val i _ hil (by scalar_tac)
    obtain ⟨y, hy, ey⟩ := ih (Std.Usize.wrapping_add i 1#usize) acc1 v (by omega) (by omega) (by
      rw [hsucc, Finset.sum_range_succ, eacc1, hacc, ein]
      simp [getElem!_pos, hir, hiw, alloc.vec.Vec.deref]
      ring)
    refine ⟨y, ?_, ey⟩
    unfold whir.verify.BaseRows.enforced_sum_loop
    rw [loop_cont hbody]
    unfold whir.verify.BaseRows.enforced_sum_loop at hy
    exact hy

/-- The level-0 enforced sum over rows of words, each row of length `width`, is the
model's `Protocol.enforced` with the rows as given (the caller reverses them). -/
theorem base_enforced_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (v : V) (rows : whir.verify.BaseRows K)
    (point weights : Slice E) (queries : Slice Q) (width : Nat) (hne : rows.val ≠ [])
    (hwidth : ∀ r ∈ rows.val, r.val.length = width) (hpoint : point.val.length < 64)
    (hfit : width ≤ 2 ^ point.val.length) (hcount : weights.val.length = rows.val.length)
    (hqcount : queries.val.length = rows.val.length) :
    ∃ y, whir.verify.BaseRows.enforced_sum copyK inst rows v point weights queries none = .ok (y, v) ∧
      encode y = Protocol.enforced
        (rows.val.map fun r => (r.val.map fun k => Concrete.E.ofK (encodeK k)).toArray).toArray
        (point.val.map encode).toArray (weights.val.map encode).toArray false := by
  have h0 : 0 < rows.val.length := List.length_pos_of_ne_nil hne
  have hw0 : rows.val[0].val.length = width := hwidth _ (List.getElem_mem h0)
  obtain ⟨eq, heq, eeq⟩ := h.eq_table_prefix v point (alloc.vec.Vec.len rows.val[0]) hpoint
    (by simp [alloc.vec.Vec.len_val, hw0, hfit])
  obtain ⟨zero, hzero, ezero⟩ := h.zero v
  obtain ⟨y, hy, ey⟩ := base_loop_eq copyK inst encode const encodeK ofLimbs index h hr weights queries
    rows eq zero ezero _ 0#usize zero v rfl (by simp) (by simp [ezero])
  refine ⟨y, ?_, ?_⟩
  · simp only [whir.verify.BaseRows.enforced_sum, vec_index rows 0#usize h0, Std.bind_ok]
    simp [heq, hzero, hy]
  · rw [ey, Protocol.enforced, foldl_tab]
    have hmin : min (min rows.val.length weights.val.length) queries.val.length = rows.val.length := by
      omega
    have hsz : (Concrete.eqTable (point.val.map encode).toArray).size = 2 ^ point.val.length := by
      simpa using TerminalRefinement.size_eqTable (point.val.map encode).toArray
    simp only [List.size_toArray, List.length_map, hmin]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi : i < rows.val.length := Finset.mem_range.mp hi
    have hri : rows.val[i].val.length = width := hwidth _ (List.getElem_mem hi)
    have heqlen : eq.val.length = width := by
      have := congrArg List.length eeq
      simp only [List.length_map, List.length_take, Array.length_toList, alloc.vec.Vec.len_val,
        alloc.vec.Vec.length, hw0, hsz] at this
      omega
    rw [toArray_getElem!, toArray_getElem!, map_getElem! _ _ i (by omega), map_getElem! _ _ i hi]
    simp only [Bool.false_eq_true, ↓reduceIte, Concrete.dot, foldl_tab]
    congr 1
    rw [map_getElem! _ _ i hi, baseInner]
    have hmin1 : min (eq.val.map encode).length (rows.val[i].val.map encodeK).length = width := by
      simp [heqlen, hri]
    have hmin2 : min (rows.val[i].val.map fun k => Concrete.E.ofK (encodeK k)).toArray.size
        (Concrete.eqTable (point.val.map encode).toArray).size = width := by
      simp only [List.size_toArray, List.length_map, hri, hsz]; omega
    rw [hmin1, hmin2]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj : j < width := Finset.mem_range.mp hj
    have heqj : (eq.val.map encode)[j]! = (Concrete.eqTable (point.val.map encode).toArray)[j]! := by
      rw [eeq, getElem!_pos _ j (by simp [alloc.vec.Vec.len_val, hw0, hsz]; omega),
        getElem!_pos _ j (by omega)]
      simp
    have hr' : (rows.val[i].val.map fun k => Concrete.E.ofK (encodeK k)).toArray[j]! =
        Concrete.E.ofK (encodeK rows.val[i].val[j]) := by
      rw [toArray_getElem!, map_getElem! _ _ j (by omega)]
    have hk : (rows.val[i].val.map encodeK)[j]! = encodeK rows.val[i].val[j] :=
      map_getElem! _ _ j (by omega)
    rw [heqj, hr', hk, mul_comm]

end Base

/-! ## Later-level rows of elements -/

section Ext
variable {E S : Type} (copy : core.marker.Copy E) (inst : fiat_shamir.arith.Arith S E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E)

/-- Column `l` of the opened rows, weighted: `sum_i w_i row_i[l]`. -/
def extColumn (rowsE : List (List Concrete.E)) (ws : List Concrete.E) (l : Nat) : Concrete.E :=
  ∑ i ∈ Finset.range (min rowsE.length ws.length), ws[i]! * (rowsE[i]!)[l]!

theorem ext_column_loop_eq (h : ArithModel inst encode const) (rows : Slice (alloc.vec.Vec E))
    (weights : Slice E) (l : Usize) (s0 : E)
    (hl : ∀ r ∈ rows.val, l.val < r.val.length) :
    ∀ (m : Nat) (i : Usize) (s : E) (a : S), min rows.val.length weights.val.length - i.val = m →
      i.val ≤ min rows.val.length weights.val.length →
      encode s = encode s0 + ∑ i' ∈ Finset.range i.val, (weights.val.map encode)[i']! *
        ((rows.val.map fun r => r.val.map encode)[i']!)[l.val]! →
      ∃ y, whir.verify.ext_column_loop inst a rows weights l s i = .ok (y, a) ∧
        encode y = encode s0 + ∑ i' ∈ Finset.range (min rows.val.length weights.val.length),
          (weights.val.map encode)[i']! * ((rows.val.map fun r => r.val.map encode)[i']!)[l.val]! := by
  intro m
  induction m with
  | zero =>
    intro i s a hm hi hs
    have hil : i.val = min rows.val.length weights.val.length := by omega
    refine ⟨s, ?_, by rw [← hil]; exact hs⟩
    unfold whir.verify.ext_column_loop
    apply loop_done
    have hge : ¬ (i < core.cmp.impls.OrdUsize.min (Slice.len rows) (Slice.len weights)) := by
      simp only [UScalar.lt_equiv, core.cmp.impls.OrdUsize.min_val, Slice.len_val, Slice.length]; omega
    simp only [whir.verify.ext_column_loop.body, lift, Std.bind_ok, hge, ↓reduceIte]
  | succ k ih =>
    intro i s a hm hi hs
    have hil : i.val < min rows.val.length weights.val.length := by omega
    have hir : i.val < rows.val.length := by omega
    have hiw : i.val < weights.val.length := by omega
    have hlr : l.val < rows.val[i.val].val.length := hl _ (List.getElem_mem hir)
    obtain ⟨s1, hs1, es1⟩ := h.mul_add a weights.val[i.val] rows.val[i.val].val[l.val] s
    have hbody : whir.verify.ext_column_loop.body inst rows weights l a s i =
        .ok (.cont (a, s1, Std.Usize.wrapping_add i 1#usize)) := by
      have hlt : i < core.cmp.impls.OrdUsize.min (Slice.len rows) (Slice.len weights) := by
        simp only [UScalar.lt_equiv, core.cmp.impls.OrdUsize.min_val, Slice.len_val, Slice.length]; omega
      simp only [whir.verify.ext_column_loop.body, lift, Std.bind_ok, hlt, ↓reduceIte,
        slice_index weights i hiw, slice_index rows i hir, vec_index _ l hlr]
      all_goals simp [hs1]
    have hsucc := succ_val i _ hil (by scalar_tac)
    obtain ⟨y, hy, ey⟩ := ih (Std.Usize.wrapping_add i 1#usize) s1 a (by omega) (by omega) (by
      rw [hsucc, Finset.sum_range_succ, es1, hs, map_getElem! _ _ _ hiw, map_getElem! _ _ _ hir,
        map_getElem! _ _ _ hlr]
      ring)
    refine ⟨y, ?_, ey⟩
    unfold whir.verify.ext_column_loop
    rw [loop_cont hbody]
    unfold whir.verify.ext_column_loop at hy
    exact hy

theorem ext_sum_loop_eq (h : ArithModel inst encode const) (rows : Slice (alloc.vec.Vec E))
    (weights eq : Slice E) (zero : E) (hz : encode zero = 0)
    (hl : ∀ r ∈ rows.val, eq.val.length ≤ r.val.length) :
    ∀ (m : Nat) (l : Usize) (acc : E) (a : S), eq.val.length - l.val = m → l.val ≤ eq.val.length →
      encode acc = ∑ l' ∈ Finset.range l.val, (eq.val.map encode)[l']! *
        extColumn (rows.val.map fun r => r.val.map encode) (weights.val.map encode) l' →
      ∃ y, whir.verify.ext_sum_loop copy inst a rows weights eq zero acc l = .ok (y, a) ∧
        encode y = ∑ l' ∈ Finset.range eq.val.length, (eq.val.map encode)[l']! *
          extColumn (rows.val.map fun r => r.val.map encode) (weights.val.map encode) l' := by
  intro m
  induction m with
  | zero =>
    intro l acc a hm hl' hacc
    have hll : l.val = eq.val.length := by omega
    refine ⟨acc, ?_, by rw [← hll]; exact hacc⟩
    unfold whir.verify.ext_sum_loop
    apply loop_done
    have hge : ¬ (l < Slice.len eq) := by
      simp only [UScalar.lt_equiv, Slice.len_val, Slice.length]; omega
    simp only [whir.verify.ext_sum_loop.body, hge, ↓reduceIte]
  | succ k ih =>
    intro l acc a hm hl' hacc
    have hle : l.val < eq.val.length := by omega
    obtain ⟨col, hcol, ecol⟩ := ext_column_loop_eq inst encode const h rows weights l zero
      (fun r hr => by have := hl r hr; omega) _ 0#usize zero a rfl (by simp) (by simp)
    obtain ⟨acc1, hacc1, eacc1⟩ := h.mul_add a eq.val[l.val] col acc
    have hbody : whir.verify.ext_sum_loop.body copy inst rows weights eq zero a acc l =
        .ok (.cont (a, acc1, Std.Usize.wrapping_add l 1#usize)) := by
      have hlt : l < Slice.len eq := by simp only [UScalar.lt_equiv, Slice.len_val, Slice.length]; omega
      simp only [whir.verify.ext_sum_loop.body, hlt, ↓reduceIte, whir.verify.ext_column, hcol,
        Std.bind_ok, slice_index eq l hle, lift]
      all_goals simp [hacc1]
    have hsucc := succ_val l _ hle (by scalar_tac)
    obtain ⟨y, hy, ey⟩ := ih (Std.Usize.wrapping_add l 1#usize) acc1 a (by omega) (by omega) (by
      rw [hsucc, Finset.sum_range_succ, eacc1, hacc, ecol, hz, zero_add, map_getElem! _ _ _ hle,
        extColumn]
      simp only [List.length_map]
      ring)
    refine ⟨y, ?_, ey⟩
    unfold whir.verify.ext_sum_loop
    rw [loop_cont hbody]
    unfold whir.verify.ext_sum_loop at hy
    exact hy

end Ext

section ExtRows
variable {V R K Q E : Type} (copyE : core.marker.Copy E) (inst : verifier.OpeningVerifier V R K Q E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E)

/-- A later level's enforced sum over rows of elements, each of length `width`, is the
model's `Protocol.enforced`: the source's column-first order is the same finite sum. -/
theorem ext_enforced_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (v : V) (rows : whir.verify.ExtRows E) (point weights : Slice E) (width : Nat)
    (hne : rows.val ≠ []) (hwidth : ∀ r ∈ rows.val, r.val.length = width)
    (hpoint : point.val.length < 64) (hfit : width ≤ 2 ^ point.val.length)
    (hcount : weights.val.length = rows.val.length) :
    ∃ y, whir.verify.ExtRows.enforced_sum copyE inst rows v point weights = .ok (y, v) ∧
      encode y = Protocol.enforced (rows.val.map fun r => (r.val.map encode).toArray).toArray
        (point.val.map encode).toArray (weights.val.map encode).toArray false := by
  have h0 : 0 < rows.val.length := List.length_pos_of_ne_nil hne
  have hw0 : rows.val[0].val.length = width := hwidth _ (List.getElem_mem h0)
  have hsz : (Concrete.eqTable (point.val.map encode).toArray).size = 2 ^ point.val.length := by
    simpa using TerminalRefinement.size_eqTable (point.val.map encode).toArray
  obtain ⟨eq, heq, eeq⟩ := h.eq_table_prefix v point (alloc.vec.Vec.len rows.val[0]) hpoint
    (by simp [hw0, hfit])
  have heqlen : eq.val.length = width := by
    have := congrArg List.length eeq
    simp only [List.length_map, List.length_take, Array.length_toList, alloc.vec.Vec.len_val,
      alloc.vec.Vec.length, hw0, hsz] at this
    omega
  obtain ⟨zero, hzero, ezero⟩ := h.zero v
  obtain ⟨y, hy, ey⟩ := ext_sum_loop_eq copyE inst.fiat_shamirarithVerifierInst.ArithInst encode const h
    (alloc.vec.Vec.deref rows) weights (alloc.vec.Vec.deref eq) zero ezero
    (fun r hr => by
      simp only [alloc.vec.Vec.deref, Slice.from_val] at hr ⊢
      rw [hwidth r hr, heqlen]) _ 0#usize zero v rfl (by simp) (by simp [ezero])
  refine ⟨y, ?_, ?_⟩
  · simp only [whir.verify.ExtRows.enforced_sum, vec_index rows 0#usize h0, Std.bind_ok]
    simp [heq, hzero, whir.verify.ext_sum, hy]
  · rw [ey, Protocol.enforced, foldl_tab]
    simp only [alloc.vec.Vec.deref, Slice.from_val, List.size_toArray, List.length_map, extColumn]
    have hmin : min rows.val.length weights.val.length = rows.val.length := by omega
    rw [hmin, heqlen]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi : i < rows.val.length := Finset.mem_range.mp hi
    have hri : rows.val[i].val.length = width := hwidth _ (List.getElem_mem hi)
    rw [toArray_getElem!, toArray_getElem!, map_getElem! _ _ i (by omega), map_getElem! _ _ i hi,
      map_getElem! _ _ i hi]
    simp only [Bool.false_eq_true, ↓reduceIte, Concrete.dot, foldl_tab, List.size_toArray,
      List.length_map, hri, hsz, Finset.mul_sum]
    rw [show min width (2 ^ point.val.length) = width by omega]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj : j < width := Finset.mem_range.mp hj
    have heqj : (eq.val.map encode)[j]! = (Concrete.eqTable (point.val.map encode).toArray)[j]! := by
      rw [eeq, getElem!_pos _ j (by simp [alloc.vec.Vec.len_val, hw0, hsz]; omega),
        getElem!_pos _ j (by omega)]
      simp
    have hr' : (rows.val[i].val.map encode).toArray[j]! = encode rows.val[i].val[j] := by
      rw [toArray_getElem!, map_getElem! _ _ j (by omega)]
    have hr'' : (rows.val[i].val.map encode)[j]! = encode rows.val[i].val[j] :=
      map_getElem! _ _ j (by omega)
    rw [heqj, hr', hr'']
    ring

end ExtRows

/-! ## Batching a level's claims -/

theorem push_ok {α : Type} (v : alloc.vec.Vec α) (x : α) (h : v.val.length < Usize.max) :
    ∃ w, alloc.vec.Vec.push v x = .ok w ∧ w.val = v.val ++ [x] := by
  have : v.val.length + 1 ≤ Usize.max := by omega
  refine ⟨alloc.vec.Vec.from (v.val ++ [x]) (by simp; omega), ?_, alloc.vec.Vec.from_val _ _⟩
  unfold alloc.vec.Vec.push
  simp [this, List.concat_eq_append]

theorem next_cons {α : Type} (it : alloc.vec.into_iter.IntoIter α) (o : α) (rest : List α)
    (h : it.val = o :: rest) :
    ∃ it', alloc.vec.into_iter.IteratorIntoIter.next it = .ok (some o, it') ∧ it'.val = rest := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split
  next hn => rw [h] at hn; cases hn
  next hd tl hc =>
    rw [h] at hc
    cases hc
    exact ⟨_, rfl, by simp [Slice.from_val]⟩

section Batch
open AccumulatedTerminalRefinement WHIRNativeArithmetic
variable {V R K Q E : Type} (copyE : core.marker.Copy E) (inst : verifier.OpeningVerifier V R K Q E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E) (index : Q → Nat)

/-- A saved out-of-domain context of the source is the model's saved context. -/
def OodMatch (c : whir.verify.OodCtx E) (sv : Saved) : Prop :=
  sv.risStart = c.ris_start.val ∧ sv.basis = .ood (c.z.val.map encode).toArray ∧ sv.beta = encode c.beta

/-- A saved query context of the source is the model's: its weights are the powers of the
batch challenge the model keeps instead. -/
def LevelMatch (c : whir.verify.LevelCtx Q E) (sv : Saved) : Prop :=
  sv.risStart = c.ris_start.val ∧ sv.beta = encode c.beta ∧
    ∃ lambda, sv.basis = .query c.log_msg_cols.val (c.queries.val.map index).toArray lambda ∧
      c.weights.val.map encode = (Concrete.powers lambda c.queries.val.length).toList

def isOod (sv : Saved) : Bool :=
  match sv.basis with
  | .ood _ => true
  | .query _ _ _ => false

@[simp] theorem isOod_ood (r : Nat) (z : Array Concrete.E) (b : Concrete.E) :
    isOod ⟨r, .ood z, b⟩ = true := rfl

@[simp] theorem isOod_query (r n : Nat) (qs : Array Nat) (l b : Concrete.E) :
    isOod ⟨r, .query n qs l, b⟩ = false := rfl

theorem next_nil {α : Type} (it : alloc.vec.into_iter.IntoIter α) (h : it.val = []) :
    alloc.vec.into_iter.IteratorIntoIter.next it = .ok (none, it) := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split
  next => rfl
  next hd tl hc => rw [h] at hc; cases hc

/-- The source replay state is the model's scalar state: the running claim, the round
quadratic with its linear coefficient fixed by the claim, the fold challenges, and the
saved contexts, which the source keeps in two lists and the model interleaves. -/
structure StateRel (w : whir.verify.WhirReplay V R K Q E) (s : State) : Prop where
  claim : encode w.t_r = s.claim
  message : (⟨encode w.quad.c, encode w.quad.a⟩ : Protocol.Message Concrete.E) = s.message
  linear : encode w.quad.b = s.claim + encode w.quad.a
  ris : w.ris.val.map encode = s.source.ris
  oods : List.Forall₂ (OodMatch encode) w.oods.val (s.source.saved.filter isOod)
  levels : List.Forall₂ (LevelMatch encode index) w.levels.val
    (s.source.saved.filter fun sv => !isOod sv)

/-- The model's batching of a level's out-of-domain claims, each at the next power. -/
def oodFold (lambda : Concrete.E) : List (Array Concrete.E × Concrete.E × Protocol.Message Concrete.E) →
    State × Concrete.E → State × Concrete.E
  | [], acc => acc
  | (z, y, m) :: rest, (st, beta) =>
    oodFold lambda rest (batchScalar st (.ood z) y (beta * lambda) m, beta * lambda)

/-- The interpreted out-of-domain claims of the source. -/
def oodData (oods : List (whir.verify.Ood E)) :
    List (Array Concrete.E × Concrete.E × Protocol.Message Concrete.E) :=
  oods.map fun o => ((o.z.val.map encode).toArray, encode o.y, ⟨encode o.intro.c, encode o.intro.a⟩)

theorem finish_loop_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (lambda : E) (ris_start : Usize) :
    ∀ (oods : List (whir.verify.Ood E)) (iter : alloc.vec.into_iter.IntoIter (whir.verify.Ood E))
      (t : E) (q : whir.sumcheck.RoundQuad E) (saved : alloc.vec.Vec (whir.verify.OodCtx E)) (v : V)
      (scalar : E) (st : State),
      iter.val = oods →
      (∀ o ∈ oods, encode o.intro.b = encode o.y + encode o.intro.a) →
      saved.val.length + oods.length < Usize.max →
      encode t = st.claim → (⟨encode q.c, encode q.a⟩ : Protocol.Message Concrete.E) = st.message →
      encode q.b = st.claim + encode q.a → ris_start.val = st.source.ris.length →
      List.Forall₂ (OodMatch encode) saved.val (st.source.saved.filter isOod) →
      ∃ t' q' saved' scalar',
        whir.verify.batch_oods_loop inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst
            inst.fiat_shamirarithVerifierInst.ArithInst iter v lambda ris_start q t saved scalar =
          .ok (scalar', v, q', t', saved') ∧
        encode t' = (oodFold (encode lambda) (oodData encode oods) (st, encode scalar)).1.claim ∧
        (⟨encode q'.c, encode q'.a⟩ : Protocol.Message Concrete.E) =
          (oodFold (encode lambda) (oodData encode oods) (st, encode scalar)).1.message ∧
        encode q'.b = (oodFold (encode lambda) (oodData encode oods) (st, encode scalar)).1.claim +
          encode q'.a ∧
        (oodFold (encode lambda) (oodData encode oods) (st, encode scalar)).1.n = st.n ∧
        encode scalar' = (oodFold (encode lambda) (oodData encode oods) (st, encode scalar)).2 ∧
        (oodFold (encode lambda) (oodData encode oods) (st, encode scalar)).1.source.ris = st.source.ris ∧
        List.Forall₂ (OodMatch encode) saved'.val
          ((oodFold (encode lambda) (oodData encode oods) (st, encode scalar)).1.source.saved.filter isOod) ∧
        (oodFold (encode lambda) (oodData encode oods) (st, encode scalar)).1.source.saved.filter
          (fun sv => !isOod sv) = st.source.saved.filter (fun sv => !isOod sv) := by
  intro oods
  induction oods with
  | nil =>
    intro iter t q saved v scalar st hiter _ _ ht hq hb _ hsv
    refine ⟨t, q, saved, scalar, ?_, ht, hq, hb, rfl, rfl, rfl, hsv, rfl⟩
    unfold whir.verify.batch_oods_loop
    apply loop_done
    simp [whir.verify.batch_oods_loop.body, next_nil iter hiter]
  | cons o rest ih =>
    intro iter t q saved v scalar st hiter hoods hcap ht hq hb hris hsv
    obtain ⟨scalar1, hs1, es1⟩ := h.mul v scalar lambda
    obtain ⟨q1, hq1, eq1, eb1⟩ := WhirAeneas.Fold.quad_fold
      inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst inst encode const h q o.intro v
      scalar1 st.claim (encode o.y) hb (hoods o (by simp))
    obtain ⟨t1, ht1, et1⟩ := h.mul_add v scalar1 o.y t
    obtain ⟨saved1, hpush, esaved1⟩ := push_ok saved
      ({ z := o.z, ris_start, beta := scalar1 } : whir.verify.OodCtx E) (by simp at hcap; omega)
    obtain ⟨iter1, hnext, eiter1⟩ := next_cons iter o rest hiter
    have hbody : whir.verify.batch_oods_loop.body inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst
        inst.fiat_shamirarithVerifierInst.ArithInst lambda ris_start iter v q t saved scalar =
        .ok (.cont (iter1, v, q1, t1, saved1, scalar1)) := by
      simp [whir.verify.batch_oods_loop.body, hnext, hs1, hq1, ht1, hpush]
    let st1 : State := batchScalar st (.ood (o.z.val.map encode).toArray) (encode o.y)
      (encode scalar * encode lambda) ⟨encode o.intro.c, encode o.intro.a⟩
    obtain ⟨t', q', saved', scalar', hloop, e1, e2, e3, e4, e5, e6, e7, e8⟩ := ih iter1 t1 q1 saved1 v
      scalar1 st1 eiter1 (fun o' ho' => hoods o' (by simp [ho']))
      (by rw [esaved1]; simp at hcap ⊢; omega)
      (by rw [et1, es1]; simp only [st1, batchScalar]; rw [← ht]; ring)
      (by
        rw [eq1]
        simp only [st1, batchScalar]
        rw [← hq, es1])
      (by rw [eb1, es1]; simp only [st1, batchScalar])
      (by simp only [st1, batchScalar, SourceState.step]; exact hris)
      (by
        rw [esaved1]
        simp only [st1, batchScalar, SourceState.step, List.filter_append]
        refine List.rel_append hsv ?_
        simp only [isOod_ood, List.filter_cons, List.filter_nil, ↓reduceIte]
        exact List.Forall₂.cons ⟨by rw [hris], rfl, by rw [es1]⟩ List.Forall₂.nil)
    have hfold : oodFold (encode lambda) (oodData encode (o :: rest)) (st, encode scalar) =
        oodFold (encode lambda) (oodData encode rest) (st1, encode scalar1) := by
      simp only [oodData, List.map_cons, oodFold, st1, es1]
    refine ⟨t', q', saved', scalar', ?_, ?_⟩
    · unfold whir.verify.batch_oods_loop
      rw [loop_cont hbody]
      unfold whir.verify.batch_oods_loop at hloop
      exact hloop
    · rw [hfold]
      refine ⟨e1, e2, e3, by rw [e4]; rfl, e5, by rw [e6]; rfl, e7, ?_⟩
      rw [e8]
      simp only [st1, batchScalar, SourceState.step, List.filter_append, isOod_ood, List.filter_cons,
        List.filter_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.append_nil]

/-- `finish_query` with an accepted opening batches the level's out-of-domain claims,
then its query batch, each at the next power of the batch challenge, exactly as the
model's `oodBatch` then `batchScalar` on the query basis, and saves the same contexts. -/
theorem finish_query_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (self : whir.verify.WhirReplay V R K Q E) (st : State) (hrel : StateRel encode index self st)
    (v v1 v2 : V) (batch : whir.verify.PendingQuery Q E) (oods : alloc.vec.Vec (whir.verify.Ood E))
    (log_msg_cols : Usize) (sum : E) (intro : whir.sumcheck.RoundQuad E)
    (hend : inst.fiat_shamirarithVerifierInst.end_scope v = .ok v1)
    (hrecv : whir.sumcheck.RoundQuad.read inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst
      inst.fiat_shamirarithVerifierInst v1 sum = .ok (.Ok intro, v2))
    (hintro : encode intro.b = encode sum + encode intro.a)
    (hoods : ∀ o ∈ oods.val, encode o.intro.b = encode o.y + encode o.intro.a)
    (hweights : batch.weights.val.map encode =
      (Concrete.powers (encode batch.lambda) batch.queries.val.length).toList)
    (hcap : self.oods.val.length + oods.val.length < Usize.max)
    (hcapl : self.levels.val.length < Usize.max) :
    ∃ self', whir.verify.WhirReplay.finish_query inst self v batch oods log_msg_cols (.Ok sum) =
        .ok (.Ok (), self', v2) ∧ self'.ris = self.ris ∧
      StateRel encode index self'
        (batchScalar (oodFold (encode batch.lambda) (oodData encode oods.val) (st, 1)).1
          (.query log_msg_cols.val (batch.queries.val.map index).toArray (encode batch.lambda))
          (encode sum) ((oodFold (encode batch.lambda) (oodData encode oods.val) (st, 1)).2 *
            encode batch.lambda) ⟨encode intro.c, encode intro.a⟩) := by
  obtain ⟨one, hone, eone⟩ := h.one v2
  have hris : (alloc.vec.Vec.len self.ris).val = st.source.ris.length := by
    rw [alloc.vec.Vec.len_val, ← hrel.ris]; simp
  obtain ⟨t', q', saved', scalar', hloop, e1, e2, e3, _, e5, e6, e7, e8⟩ :=
    finish_loop_eq inst encode const h batch.lambda (alloc.vec.Vec.len self.ris) oods.val oods
      self.t_r self.quad self.oods v2 one st rfl hoods hcap hrel.claim hrel.message hrel.linear hris
      hrel.oods
  rw [eone] at e1 e2 e3 e5 e6 e7 e8
  have hbo : whir.verify.batch_oods inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst
      inst.fiat_shamirarithVerifierInst.ArithInst v2 oods batch.lambda (alloc.vec.Vec.len self.ris)
      self.quad self.t_r self.oods = .ok (scalar', v2, q', t', saved') := by
    simp only [whir.verify.batch_oods, hone, Std.bind_ok, alloc.vec.IntoIteratorVec.into_iter]
    exact hloop
  obtain ⟨scalar2, hs2, es2⟩ := h.mul v2 scalar' batch.lambda
  obtain ⟨q1, hq1, eq1, eb1⟩ := WhirAeneas.Fold.quad_fold
    inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst inst encode const h q' intro v2
    scalar2 _ (encode sum) e3 hintro
  obtain ⟨t1, ht1, et1⟩ := h.mul_add v2 scalar2 sum t'
  obtain ⟨levels1, hpush, elevels1⟩ := push_ok self.levels
    ({ log_msg_cols := log_msg_cols, queries := batch.queries, weights := batch.weights,
       ris_start := alloc.vec.Vec.len self.ris, beta := scalar2 } : whir.verify.LevelCtx Q E) hcapl
  refine ⟨{ self with t_r := t1, quad := q1, levels := levels1, oods := saved' }, ?_, rfl, ?_⟩
  · simp [whir.verify.WhirReplay.finish_query, hend, core.result.Result.Insts.CoreOpsTry.branch, hrecv,
      hbo, hs2, hq1, ht1, hpush]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [batchScalar]; rw [et1, es2, e1, e5]; ring
    · simp only [batchScalar]; rw [eq1, e2, es2, e5]
    · simp only [batchScalar]; rw [eb1, es2, e5]
    · simp only [batchScalar, SourceState.step]; rw [e6, ← hrel.ris]
    · simp only [batchScalar, SourceState.step, List.filter_append, isOod_query, List.filter_cons,
        List.filter_nil, Bool.false_eq_true, ↓reduceIte, List.append_nil]
      exact e7
    · simp only [batchScalar, SourceState.step, List.filter_append, List.filter_cons,
        List.filter_nil, isOod_query, Bool.not_false, ↓reduceIte]
      rw [e8, elevels1]
      refine List.rel_append hrel.levels (List.Forall₂.cons ⟨by rw [e6, ← hris], by rw [es2, e5], ?_⟩
        List.Forall₂.nil)
      exact ⟨encode batch.lambda, rfl, hweights⟩

end Batch

end WhirAeneas.Query
