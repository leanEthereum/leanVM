/-
  LeanVM.Protocol.Relation.Link.GroupLinksDegSum

  The row summand at Boolean points, then the index claim less the index side's sum, as
  polynomials of degree at most `linkGroupError` in the draw.
-/

module

public import LeanVM.Protocol.Relation.Link.GroupLinksDeg

/-!
# The drawn group's polynomial

`polyFn_groupF`: `v ↦ indexClaim(v) − Σ_{r Boolean} linkIdxAt(v, r)` is of total degree at most
`linkGroupError`, from each share of `lk_rowSummand` at Boolean `(r, χ, q)`.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link LeanVM.Protocol.Hotwire Finset

@[expose] public section

theorem lkIdx_xBc {layout : Layout} {chunks : Chunks} {μ : ℕ} (q : Column μ) (ch : LinkCh) (r : List E) : (lkIdx layout chunks q ch r).xBc =
    ch.etaBc * (eqKernel ch.alpha).getD 1 0 * indexMle r + belowAt chunks r layout.logBytecode *
      (ch.etaBc * (eqKernel ch.alpha).getD 2 0 + (programSums layout ch (linkSplit layout r)).1) := rfl

section Shares

variable {layout : Layout} {chunks : Chunks} {μ : ℕ} (q : Column μ) {n : ℕ} {ch : (Fin n → E) → LinkCh}
  (hL : LinCh n ch) (hα : (ch 0).alpha.length ≤ bytecodeSlotBits)
  (hζ : (ch 0).zeta.length = chunks.width) {jr : ℕ}
include hL hα

theorem polyFn_xBc (r : List E) :
    PolyFn n (bytecodeSlotBits + 1) fun v ↦ (lkIdx layout chunks q (ch v) r).xBc := by
  refine ((((hL.etaBc.mul (polyFn_slot hL hα 1)).mul (PolyFn.const (indexMle r))).mono (by omega)).add_le
    ((PolyFn.const (belowAt chunks r layout.logBytecode)).mul_le
      (((hL.etaBc.mul (polyFn_slot hL hα 2)).mono (by omega)).add_le
      (polyFn_programSums hL hα layout (linkSplit layout r)).1) (by omega))).congr fun v ↦ ?_
  rw [lkIdx_xBc]

theorem polyFn_pFp (r : List E) :
    PolyFn n (bytecodeSlotBits + 1) fun v ↦ (lkIdx layout chunks q (ch v) r).pFp :=
  ((PolyFn.const (belowAt chunks r layout.logBytecode)).mul_le
    (polyFn_programSums hL hα layout (linkSplit layout r)).2 (by omega)).congr fun v ↦ rfl

omit hα in
theorem polyFn_yMem (r : List E) : PolyFn n 1 fun v ↦ (lkIdx layout chunks q (ch v) r).yMem :=
  ((((polyFn_gm hL 0).mul_le (PolyFn.const _) (by omega)).add_le
    ((polyFn_gm hL 3).mul_le (PolyFn.const _) (by omega))).add_le
    ((polyFn_gm hL 1).mul_le (PolyFn.const _) (by omega))).congr fun v ↦ rfl

omit hα in
include hζ in
theorem polyFn_eqZetaR {r : List E} (hr : r.length = chunks.width) :
    PolyFn n chunks.width fun v ↦ (lkIdx layout chunks q (ch v) r).eqZetaR :=
  hζ ▸ (polyFn_eqEval hL.zeta r (by rw [hζ, hr])).congr fun v ↦ rfl

omit hα in
include hζ in
theorem polyFn_shiftZetaR {r : List E} (hr : r.length = chunks.width) :
    PolyFn n chunks.width fun v ↦ (lkIdx layout chunks q (ch v) r).shiftZetaR :=
  hζ ▸ (polyFn_linkShiftEq hL.zeta r (by rw [hζ, hr])).congr fun v ↦ rfl

omit hα in
/-- The row weight at a Boolean row point is of degree at most `m + 1`. -/
theorem polyFn_omegaOf (hτ : (ch 0).tau.length = linkRows layout) (t jx : ℕ)
    (hrows : layout.tableRows.getD t 0 ≤ 2 ^ heightOf layout t) :
    PolyFn n (linkRows layout + 1) fun v ↦ omegaOf layout (ch v) (boolL (linkRows layout) jx) t := by
  have hh := heightOf_le layout t
  have hτv : ∀ v, ((ch v).tau.take (heightOf layout t)).length = heightOf layout t := fun v ↦ by
    rw [List.length_take, hL.tau.1 v 0, hτ]; omega
  have hjx : jx % 2 ^ heightOf layout t < 2 ^ heightOf layout t := Nat.mod_lt _ (Nat.two_pow_pos _)
  have he := polyFn_eqAt (heightOf layout t) (fun v ↦ (ch v).tau.take (heightOf layout t)) hτv
    (fun k _ ↦ (hL.tau.take _).getD k) (jx % 2 ^ heightOf layout t)
  have hite : PolyFn n (heightOf layout t) fun v ↦ if jx % 2 ^ heightOf layout t < layout.tableRows.getD t 0 then
      eqAt ((ch v).tau.take (heightOf layout t)) (jx % 2 ^ heightOf layout t) else 0 := by
    split_ifs
    · exact he
    · exact (PolyFn.const 0).mono (Nat.zero_le _)
  refine ((hL.theta.getD t).mul_le hite (by omega)).congr fun v ↦ ?_
  rw [omegaOf, take_boolL hh, omegaAt_boolL _ _ (hτv v) hjx hrows]

end Shares

/-- The base terms at no `JUMP` coefficient: the payload under `ω`. -/
def lkRBc (ch : LinkCh) (table : Table) (values : List E) : E :=
  let col := fun (c : ℕ) ↦ values.getD c 0
  let slot := eqKernel ch.alpha
  let bc := table.links.bytecodeLink
  slot.getD 1 0 * col bc.pc + slot.getD 2 0 + slot.getD 3 0 * gpow bc.opcode +
    (bc.operands.map fun op ↦ slot.getD (op.1.headD 0) 0 * op.2.evaluate col).sum

theorem tableBaseOf_nil (ch : LinkCh) (a : IdxAt) (point : List E) (height : ℕ) (omega : E)
    (table : Table) (t : ℕ) (values : List E) :
    tableBaseOf ch a [] point height omega table t values = omega * a.eq0R * (ch.etaMem *
      ((table.links.memory.zip (ch.mu.getD t [])).map fun x ↦ x.2 * lkGate (fun c ↦ values.getD c 0) x.1 *
        (ch.gammaMem.getD 0 0 * x.1.address.evaluate (fun c ↦ values.getD c 0) + ch.gammaMem.getD 3 0 +
          ch.gammaMem.getD 1 0 * x.1.value.evaluate (fun c ↦ values.getD c 0))).sum +
      ch.etaBc * lkRBc ch table values) := by
  unfold tableBaseOf
  simp only [List.zipWith_nil_left, sumE_eq_sum', List.sum_nil, mul_zero, add_zero, ite_self]
  rfl

/-- A shifted access's functional value: `D_0` at shift `0`, `T_s` past it. -/
def lkShW (d0 : E) (ts : List E) (N s : ℕ) : E :=
  match s with
  | 0 => d0
  | s + 1 => if s < N then ts.getD s 0 else 0

section Gen

variable {n : ℕ} {ch : (Fin n → E) → LinkCh} (hL : LinCh n ch) (hα : (ch 0).alpha.length ≤ bytecodeSlotBits)
include hL hα

theorem polyFn_tableBase {a : (Fin n → E) → IdxAt} {omega : (Fin n → E) → E} {M : ℕ}
    (hω : PolyFn n (M + 1) omega) (h0 : ∀ v, (a v).eq0R = (a 0).eq0R) (point : List E) (height : ℕ)
    (table : Table) (t : ℕ) (values : List E) :
    PolyFn n (M + 2 + bytecodeSlotBits) fun v ↦
      tableBaseOf (ch v) (a v) [] point height (omega v) table t values := by
  have hmem := polyFn_zip_sum' (D := 2) (fun (b : Access) m v ↦ m * lkGate (fun c ↦ values.getD c 0) b *
      ((ch v).gammaMem.getD 0 0 * b.address.evaluate (fun c ↦ values.getD c 0) + (ch v).gammaMem.getD 3 0 +
        (ch v).gammaMem.getD 1 0 * b.value.evaluate (fun c ↦ values.getD c 0)))
    (fun b m hm ↦ (hm.mul (PolyFn.const _)).mul_le ((((polyFn_gm hL 0).mul (PolyFn.const _)).mono (by omega)).add_le
      (polyFn_gm hL 3) |>.add_le (((polyFn_gm hL 1).mul (PolyFn.const _)).mono (by omega))) (by omega))
    table.links.memory (hL.mu t)
  have hr : PolyFn n bytecodeSlotBits fun v ↦ lkRBc (ch v) table values :=
    (((((polyFn_slot hL hα 1).mul (PolyFn.const _)).mono (by omega)).add_le (polyFn_slot hL hα 2)).add_le
      (((polyFn_slot hL hα 3).mul (PolyFn.const _)).mono (by omega))).add_le
      (polyFn_list_sum _ _ fun op _ ↦ ((polyFn_slot hL hα _).mul (PolyFn.const _)).mono (by omega))
  refine ((hω.mul (PolyFn.const (a 0).eq0R)).mul_le (((hL.etaMem.mul hmem).mono (by decide)).add_le
    (hL.etaBc.mul hr)) (by omega)).congr fun v ↦ ?_
  rw [tableBaseOf_nil, h0 v]

omit hα in
theorem polyFn_lkPtr {a : (Fin n → E) → IdxAt} {omega sH sN : (Fin n → E) → E} {M W : ℕ}
    (hω : PolyFn n (M + 1) omega) (hsH : PolyFn n 1 sH) (hsN : PolyFn n 1 sN)
    (hZ : PolyFn n W fun v ↦ (a v).eqZetaR) (hS : PolyFn n W fun v ↦ (a v).shiftZetaR)
    (hX : PolyFn n (bytecodeSlotBits + 1) fun v ↦ (a v).xBc)
    (hP : PolyFn n (bytecodeSlotBits + 1) fun v ↦ (a v).pFp)
    (hY : PolyFn n 1 fun v ↦ (a v).yMem) (hm1 : ∀ v, (a v).m1 = (a 0).m1)
    (act : E) (table : Table) (t : ℕ) (col : ℕ → E) (d0 rest : E) (ts : List E) (N pointer k : ℕ) :
    PolyFn n (max (W + 1) (M + 3 + bytecodeSlotBits)) fun v ↦
      lkPtr (ch v) (a v) (omega v) act (sH v) (sN v) table t col d0 rest ts N pointer k := by
  rcases k with _ | _ | k
  · refine (((((PolyFn.const act).mul ((hZ.mul hsH).add_le (hS.mul hsN))).mul (PolyFn.const d0)).mul
      (PolyFn.const rest)).mono (by omega)).congr fun v ↦ rfl
  · refine ((((hω.mul (hX.add_le (((PolyFn.const _).mul hP).mono (by omega)))).mul (PolyFn.const d0)).mul
      (PolyFn.const rest)).mono (by omega)).congr fun v ↦ rfl
  · have hreads := polyFn_zip_sum' (D := M + 4) (fun (b : Access) m v ↦ (b.reads.map (lkRead pointer
        (fun m scale ↦ omega v * (ch v).etaMem * m * (ch v).gammaMem.getD 1 0 * (a v).m1 * scale.evaluate col)
        m)).sum)
      (fun b m hm ↦ polyFn_list_sum _ _ fun rd _ ↦ polyFn_lkRead pointer _ (fun m' sc hm' ↦
        ((((((hω.mul hL.etaMem).mul hm').mul (polyFn_gm hL 1)).mul (PolyFn.const (a 0).m1)).mul
          (PolyFn.const (sc.evaluate col))).mono (by omega)).congr fun v ↦ by rw [hm1 v]) m hm rd)
      table.links.memory (hL.mu t)
    have hacc := polyFn_zip_sum (D := M + 4) (fun (b : Access) ↦ decide (b.pointer = pointer))
      (fun (b : Access) m v ↦ omega v * lkGate col b * (ch v).etaMem * m * (a v).yMem * lkShW d0 ts N b.shift)
      (fun b m hm ↦ (((((hω.mul (PolyFn.const (lkGate col b))).mul hL.etaMem).mul hm).mul hY).mul
        (PolyFn.const (lkShW d0 ts N b.shift))).mono (by omega))
      table.links.memory (hL.mu t)
    refine (((((hreads.mul (PolyFn.const d0)).add_le hacc).mul (PolyFn.const rest)).mono
      (by have : bytecodeSlotBits = 4 := rfl; omega))).congr
      fun v ↦ rfl

end Gen

theorem chV_zeta_length {layout : Layout} {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
    (v : Fin (linkDrawn layout chunks + 1) → E) : (chV layout chunks v).zeta.length = chunks.width := by
  have hN := linkDrawn_eq layout chunks hch
  have hT1 : 1 ≤ nTables := by decide
  simp only [nuOff, tauOff, epsOff, nAccessesOf, nPointersOf] at hN
  simp only [linkCh, mu_fold_snd, List.length_take, List.length_drop, List.length_tail, List.length_ofFn]
  simp only [linkRows, List.map_map, Function.comp_def] at hN ⊢
  omega

/-- The index side's table at no index challenge is its sum over the Boolean points. -/
theorem linkIdx_nil_eq (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (theta0 : E)
    (drawn : List E) :
    linkIdx layout chunks q theta0 drawn [] = ∑ jr ∈ range (2 ^ chunks.width),
      ∑ jx ∈ range (2 ^ linkRows layout), ∑ jq ∈ range (2 ^ linkQVars layout),
        rowSummand layout chunks q theta0 drawn (boolL chunks.width jr) []
          (boolL (linkRows layout) jx ++ boolL (linkQVars layout) jq) := by
  simp only [linkIdx, cube, List.length_nil, Nat.sub_zero]
  rw [sumTail_eq_sum]
  refine sum_congr rfl fun jr _ ↦ ?_
  simp only [List.nil_append, linkIdxAt, linkRow, cube, List.length_nil, Nat.sub_zero, linkRowVars]
  rw [sumTail_split]
  refine sum_congr rfl fun jx _ ↦ ?_
  rw [sumTail_eq_sum]
  simp only [List.nil_append]

theorem indexClaim_eq_ch (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn : List E) :
    indexClaim layout chunks drawn =
      eqAt (linkCh layout chunks theta0 drawn).zeta 0 * (linkCh layout chunks theta0 drawn).stateGamma 1 1 +
      eqAt (linkCh layout chunks theta0 drawn).zeta (linkCycles layout) *
        (linkCh layout chunks theta0 drawn).stateGamma (gpow (2 ^ layout.logBytecode - 1)) 1 := by
  simp only [indexClaim, linkCh, LinkCh.stateGamma, linkEqAt, linkEqAt_eq, mu_fold_snd, linkCycles]

section Final

variable {layout : Layout} {chunks : Chunks} {μ : ℕ} (q : Column μ)
  (hch : Chunks.new chunks.width = some chunks)
include hch

omit hch in
theorem polyFn_stateGamma {n : ℕ} {ch : (Fin n → E) → LinkCh} (hL : LinCh n ch) (c c' : E) :
    PolyFn n 1 fun v ↦ (ch v).stateGamma c c' :=
  ((((PolyFn.const 1).mono (by omega)).add_le (((hL.gammaState.getD 0).mul (PolyFn.const c)).mono (by omega))).add_le
    (((hL.gammaState.getD 1).mul (PolyFn.const c')).mono (by omega))).congr fun v ↦ rfl

omit hch in
theorem polyFn_indexClaim (hch : Chunks.new chunks.width = some chunks) :
    PolyFn (linkDrawn layout chunks + 1) (chunks.width + 1) fun v ↦
      indexClaim layout chunks (List.ofFn v).tail := by
  have hL := linCh_draw layout chunks (n := linkDrawn layout chunks)
  have hζ := chV_zeta_length (layout := layout) hch
  have hz : ∀ j, PolyFn (linkDrawn layout chunks + 1) chunks.width fun v ↦ eqAt (chV layout chunks v).zeta j :=
    fun j ↦ polyFn_eqAt chunks.width (fun v ↦ (chV layout chunks v).zeta) hζ (fun k _ ↦ hL.zeta.getD k) j
  refine (((hz 0).mul (polyFn_stateGamma hL 1 1)).add_le ((hz _).mul (polyFn_stateGamma hL _ 1))).congr
    fun v ↦ (indexClaim_eq_ch layout chunks _ _).symm

set_option maxHeartbeats 800000 in
/-- **The row summand at a Boolean point** is of degree at most `linkGroupError` in the draw. -/
theorem polyFn_rowSummand_bool
    (hrows : ∀ t < layout.tables.length, layout.tableRows.getD t 0 ≤ 2 ^ heightOf layout t)
    {jr : ℕ} (jx jq : ℕ) :
    PolyFn (linkDrawn layout chunks + 1) (linkGroupError layout chunks) fun v ↦
      rowSummand layout chunks q ((List.ofFn v).headD 0) (List.ofFn v).tail (boolL chunks.width jr) []
        (boolL (linkRows layout) jx ++ boolL (linkQVars layout) jq) := by
  have hL := linCh_draw layout chunks (n := linkDrawn layout chunks)
  have hα : (chV layout chunks 0).alpha.length ≤ bytecodeSlotBits := by
    simp only [linkCh]; exact List.length_take_le _ _
  have hτ := chV_tau_length hch (layout := layout) 0
  have hζ := chV_zeta_length (layout := layout) hch 0
  have hx1 : (boolL (linkRows layout) jx ++ boolL (linkQVars layout) jq).take (linkRows layout) =
      boolL (linkRows layout) jx := List.take_left' (length_boolL _ _)
  have hx2 : (boolL (linkRows layout) jx ++ boolL (linkQVars layout) jq).drop (linkRows layout) =
      boolL (linkQVars layout) jq := List.drop_left' (length_boolL _ _)
  have hr := length_boolL chunks.width jr
  have hD1 : linkRows layout + 2 + bytecodeSlotBits ≤ linkGroupError layout chunks := by
    unfold linkGroupError; omega
  have hD2 : max (chunks.width + 1) (linkRows layout + 3 + bytecodeSlotBits) ≤ linkGroupError layout chunks := by
    unfold linkGroupError; omega
  set chi := boolL (linkRows layout) jx
  set qP := boolL (linkQVars layout) jq
  set r := boolL chunks.width jr
  set msg := honestMessage layout q chi qP
  set vals := lkFVals layout chunks q r (chi ++ qP)
  refine (PolyFn.finsetSum _ fun t ht ↦ ?_).congr fun v ↦ by rw [lk_rowSummand, hx1, hx2]
  have hω := polyFn_omegaOf hL hτ t jx (hrows t (mem_range.mp ht))
  set col := fun c ↦ (lkVals layout msg t).getD c 0
  set st := (layout.tables.getD t default).links.stateLink
  have hB : PolyFn (linkDrawn layout chunks + 1) (linkGroupError layout chunks) fun v ↦
      lkBase layout (chV layout chunks v) (lkIdx layout chunks q (chV layout chunks v) r) [] chi msg t :=
    ((polyFn_tableBase hL hα hω (fun v ↦ rfl) (chi.take (heightOf layout t)) (heightOf layout t)
      (layout.tables.getD t default) t (lkVals layout msg t)).mono hD1).congr fun v ↦ rfl
  have hP : ∀ k, PolyFn (linkDrawn layout chunks + 1) (linkGroupError layout chunks) fun v ↦
      lkPtrAt layout (chV layout chunks v) (lkIdx layout chunks q (chV layout chunks v) r) chi msg
        (vals.getD 0 0) (prodE ((vals.drop 1).take (chunks.d - 1))) (vals.drop (2 * chunks.d)) t k := fun k ↦
    ((polyFn_lkPtr hL hω (polyFn_stateGamma hL (col st.pc) (col st.fp))
      (polyFn_stateGamma hL (st.next.1.evaluate col) (st.next.2.evaluate col))
      (polyFn_eqZetaR q hL hζ hr) (polyFn_shiftZetaR q hL hζ hr) (polyFn_xBc q hL hα r)
      (polyFn_pFp q hL hα r) (polyFn_yMem q hL r) (fun v ↦ rfl)
      (lessThan (chi.take (heightOf layout t)) (layout.tableRows.getD t 0)) (layout.tables.getD t default) t col
      (vals.getD 0 0) (prodE ((vals.drop 1).take (chunks.d - 1))) (vals.drop (2 * chunks.d))
      (lkMaxShift layout) ((ptrsOf layout t).getD k 0) k).mono hD2).congr fun v ↦ rfl
  exact ((PolyFn.const _).mul_le hB (Nat.zero_add _).le).add_le
    (PolyFn.finsetSum _ fun k _ ↦ (PolyFn.const _).mul_le (hP k) (Nat.zero_add _).le)

/-- **The drawn group's polynomial**: the index claim less the index side's sum is of degree at most
`linkGroupError` in the draw. -/
theorem polyFn_groupF
    (hrows : ∀ t < layout.tables.length, layout.tableRows.getD t 0 ≤ 2 ^ heightOf layout t) :
    PolyFn (linkDrawn layout chunks + 1) (linkGroupError layout chunks) fun v ↦
      indexClaim layout chunks (List.ofFn v).tail -
        linkIdx layout chunks q ((List.ofFn v).headD 0) (List.ofFn v).tail [] := by
  have hs := PolyFn.finsetSum _ fun jr (_ : jr ∈ range (2 ^ chunks.width)) ↦
    PolyFn.finsetSum _ fun jx (_ : jx ∈ range (2 ^ linkRows layout)) ↦
      PolyFn.finsetSum _ fun jq (_ : jq ∈ range (2 ^ linkQVars layout)) ↦
        polyFn_rowSummand_bool q hch hrows (jr := jr) jx jq
  refine (((polyFn_indexClaim hch).sub hs).mono (max_le (by unfold linkGroupError; omega) le_rfl)).congr
    fun v ↦ by rw [linkIdx_nil_eq]

end Final


end

end LeanVM.Protocol.Relation
