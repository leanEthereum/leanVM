/-
  LeanVM.Guest.B1.Tables.VtC.AMain

  **`verify_tables` is complete at the `Rel` level**: on the honest memory and oracle, every
  statement holds, its loads read inside the layout, its allocations are the allocator's and it
  returns the honest words.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ADefs
public import LeanVM.Guest.B1.Tables.VtC.AOracle
public import LeanVM.Guest.B1.Tables.VtC.AGlue
public import LeanVM.Guest.B1.Tables.VtC.SLoads
public import LeanVM.Guest.B1.Tables.VtC.ZTail
public import LeanVM.Guest.B1.Tables.VtC.ZInBuf
public import LeanVM.Guest.B1.Tables.VtC.FComplete
public import LeanVM.Guest.B1.Tables.VtC.FInBuf

/-!
# Assembly

`VtShape`: the deployed shapes the ranges need. `vt_rel_complete`: from the specification's
accepting run (`VtHonest.Ok`), on a memory defined below `2^14` (the rank keys' range check
against `g^8635`) holding the caller's buffers (`linL`) and the own buffers at the allocator's
positions (`ownL`), with the oracle's answers (`VtWOk`), the honest valuation satisfies every
statement of `verify_tables` (`vtS_complete` `0 ..< 769`, `vtB_complete` `769 ..< 2589`,
`vtZ_complete` `2589 ..< 2688`, `vtF_complete` `2688 ..< 6353`, `vtZt_complete` `6353 ..< 6398`),
its loads read inside the layout, and it returns the honest words. `vt_rel_complete_vtW`: the
same with the explicit oracle `vtW`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (termsPure blockSel)
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- **The deployed shapes.** -/
structure VtShape (H : VtHonest) : Prop where
  hlm : H.lm ≤ 32
  hlmμ : H.lm ≤ H.point.length
  h19 : 19 ≤ H.point.length
  hμ33 : H.point.length < 33
  hr : H.rows.length = 6
  hτ29 : ∀ t < 6, vtHt H.rows t < 29
  hτμ : ∀ t < 6, vtHt H.rows t ≤ H.point.length
  hal : H.alphas.length = 4
  hf : H.f.length = 5
  hfcan : ∀ i < 5, IsCanonical128 (H.f.getD i 0)
  hfitP : ((vtSizesP H.lm (vtHt H.rows)).map (2 ^ ·)).sum ≤ 2 ^ H.point.length
  hfitC : ((vtSizesC (vtHt H.rows)).map (2 ^ ·)).sum ≤ 2 ^ H.point.length
  hbc : H.bc.length = 2 ^ 23

/-! ## Facts of the data -/

theorem vtHt_eq {rows : List ℕ} (hr : rows.length = 6) {t : ℕ} (ht : t < 6) :
    vtHt rows t = max (log2Ceil (vtRw rows t)) (tableLogFloors.getD t 0) := by
  unfold vtHt vtRw tableHeightsOf
  rw [List.getD_eq_getElem _ _ (by simp [hr, tableLogFloors]; omega)]
  simp only [List.getElem_zipWith]
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by simp [tableLogFloors]; omega)]

theorem foldl_max_ge : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => ⟨le_rfl, by simp⟩
  | y :: l, a => by
    obtain ⟨h1, h2⟩ := foldl_max_ge l (max a y)
    refine ⟨le_trans (le_max_left _ _) h1, fun x hx ↦ ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (le_max_right _ _) h1
    · exact h2 x hx

theorem foldl_max_mem : ∀ (l : List ℕ) (a : ℕ), l.foldl max a = a ∨ l.foldl max a ∈ l
  | [], a => Or.inl rfl
  | y :: l, a => by
    rcases foldl_max_mem l (max a y) with h | h
    · simp only [List.foldl_cons, h]
      rcases max_choice a y with e | e
      · exact Or.inl e
      · exact Or.inr (by rw [e]; exact List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem vt_n_ge {H : VtHonest} (hr : H.rows.length = 6) {t : ℕ} (ht : t < 6) : H.τ t ≤ H.n := by
  have := (foldl_max_ge (tableHeightsOf H.rows) 0).2 (H.τ t) (by
    rw [vt_tableHeights_eq hr]; exact List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)
  exact this

theorem vt_n_ex {H : VtHonest} (hr : H.rows.length = 6) : ∃ t < 6, H.τ t = H.n := by
  rcases foldl_max_mem (tableHeightsOf H.rows) 0 with h | h
  · refine ⟨0, by norm_num, ?_⟩
    have := vt_n_ge hr (t := 0) (by norm_num)
    unfold VtHonest.n at this ⊢; rw [h] at this ⊢; omega
  · rw [vt_tableHeights_eq hr] at h
    obtain ⟨t, ht, e⟩ := List.mem_map.mp h
    refine ⟨t, List.mem_range.mp ht, ?_⟩
    show vtHt H.rows t = (tableHeightsOf H.rows).foldl max 0
    rw [vt_tableHeights_eq hr]; exact e

theorem vt_target_eq (H : VtHonest) (ξ T0 T1 T2 : E)
    (h0 : T0 = H.busH.totals.getD 0 0) (h1 : T1 = H.busH.totals.getD 1 0)
    (h2 : T2 = H.busH.totals.getD 2 0) (hξ : ξ = H.ξ) :
    ξ ^ 2 * T0 + ξ ^ 3 * T1 + ξ ^ 4 * T2 = H.target := by
  subst h0 h1 h2 hξ
  simp only [VtHonest.target, VtHonest.busH, vtBus, vt_nConstraints, Nat.reduceAdd, vt_powers5, dot]
  simp only [List.drop_succ_cons, List.drop_zero, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.foldl_cons, List.foldl_nil, List.getD_cons_zero, List.getD_cons_succ]
  ring

theorem lists_eq_of_flatten : ∀ (l1 l2 : List (List E)), l1.length = l2.length →
    (∀ i, (l1.getD i []).length = (l2.getD i []).length) → l1.flatten = l2.flatten → l1 = l2
  | [], [], _, _, _ => rfl
  | a :: l1, b :: l2, hl, hi, hf => by
    have hab : a.length = b.length := by simpa using hi 0
    simp only [List.flatten_cons] at hf
    have ha : a = b := by
      have := congrArg (List.take a.length) hf
      rwa [List.take_left' rfl, hab, List.take_left' rfl] at this
    subst ha
    rw [lists_eq_of_flatten l1 l2 (by simpa using hl) (fun i ↦ by simpa using hi (i + 1))
      (List.append_cancel_left hf)]
  | [], _ :: _, hl, _, _ => absurd hl (by simp)
  | _ :: _, [], hl, _, _ => absurd hl (by simp)

theorem tables_widths : ∀ t < 6, (tables.getD t default).width = vtW6.getD t 0 := by decide

theorem vt_rowsT_length {H : VtHonest} (hr : H.rows.length = 6) : H.rowsT.length = 6 := by
  have hf : H.busH.forms.length = 6 :=
    (vt_forms3_shape H.bc H.lm hr H.alphas H.beta H.point (H.xs5.take 3) (H.xs5.getD 3 0)
      (H.xs5.getD 4 0) H.bv (H.values.getD 0 0) (H.values.getD 1 0) (H.values.getD 2 0)).1
  have hh : H.L.tableLogHeights.length = 6 := vt_tableHeights_length hr
  have ht : tables.length = 6 := rfl
  simp only [VtHonest.rowsT, vtRows, List.length_zip, hh, hf, ht,
    LeanVM.Protocol.EndToEnd.Complete.length_tableWeights]
  rfl

theorem vt_evsT_shape {H : VtHonest} (h : H.Ok) (hr : H.rows.length = 6) :
    H.evsT.length = 6 ∧ ∀ t < 6, (H.evsT.getD t []).length = vtW6.getD t 0 := by
  have hl := h.hevl
  rw [vt_rowsT_length hr] at hl
  refine ⟨hl, fun t ht ↦ ?_⟩
  have hz : (H.rowsT[t]'(by rw [vt_rowsT_length hr]; exact ht), H.evsT[t]'(by omega)) ∈
      List.zip H.rowsT H.evsT := by
    rw [List.mem_iff_getElem]
    exact ⟨t, by simp [vt_rowsT_length hr, hl, ht], by simp⟩
  have hw := h.hevw _ hz
  simp only at hw
  have ht1 : (H.rowsT[t]'(by rw [vt_rowsT_length hr]; exact ht)).1 = tables.getD t default := by
    simp [VtHonest.rowsT, vtRows, List.getElem_zip, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show t < tables.length from ht)]
  rw [List.getD_eq_getElem _ _ (by omega), hw, ht1, tables_widths t ht]

theorem cap0_length (H : VtHonest) : H.cap0.length = 5 := by
  simp [VtHonest.cap0, Fs.squeeze, capOf]

theorem ownW_length (H : VtHonest) (B : VtBases) : (H.ownW B).length = 111 := by
  simp [VtHonest.ownW]

theorem ownB_length (H : VtHonest) (B : VtBases) : (H.ownB B).length = 111 := by
  simp [VtHonest.ownB, VtHonest.sizes, LeanVM.Guest.Memory.length_bases]

/-- The own buffers' honest words fill their allocations. -/
theorem ownW_lengths (H : VtHonest) (B : VtBases) : (H.ownW B).map List.length = H.sizes := by
  have h5 := cap0_length H
  have r : ∀ (m : ℕ) (f : ℕ → List E) (k : ℕ), (∀ i, (f i).length = k) →
      ((List.range m).map f).map List.length = List.replicate m k := fun m f k hf ↦ by
    apply List.ext_getElem (by simp)
    intro j _ _
    simp [hf]
  simp only [VtHonest.ownW, VtHonest.sizes, List.map_append,
    r 3 _ 34 (fun _ ↦ offBits_length _), r 51 _ 9 (fun _ ↦ offDigits_length _ _),
    r 45 _ 9 (fun _ ↦ offDigits_length _ _)]
  rw [show List.replicate 96 9 = List.replicate 51 9 ++ List.replicate 45 9 from
    (List.replicate_add 51 45 9).symm]
  simp [VtHonest.μ, vtGKeyW, vtGSizeW, vtGBaseW, vtGOrdW, vtIdxcW, vtShEqW_length, vtShGW_length,
    vtIdxBufW, zcRoundsW_len h5, zcCprodW]

theorem tb_load_of {rd : Reader} {p : E} {l : List E} (h : TbReadsAt rd p l) {k : ℕ}
    (hk : k < l.length) : LoadHolds rd p k (l.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

theorem vtAllocVars_head : vtAllocVars.take 9 = [36, 37, 38, 39, 668, 703, 705, 706, 781] := by
  decide
theorem vtAllocVars_F : ∀ b < 3, vtAllocVars.getD (9 + b) 0 = vtFwW b + 6 := by decide
theorem vtAllocVars_P : ∀ i < 51, vtAllocVars.getD (12 + i) 0 = (vtPushSel.getD i default).2.2.1 := by
  decide
theorem vtAllocVars_C : ∀ i < 45, vtAllocVars.getD (63 + i) 0 =
    (vtCountSel.getD i default).2.2.1 := by decide
theorem vtAllocVars_Z : vtAllocVars.getD 108 0 = 2605 ∧ vtAllocVars.getD 109 0 = 2608 ∧
    vtAllocVars.getD 110 0 = 2629 := by decide

section
variable (H : VtHonest) (B : VtBases)

theorem ownW_getD_head {j : ℕ} (hj : j < 9) : (H.ownW B).getD j [] =
    [vtGKeyW H.lm H.τ, vtGSizeW H.lm H.τ, vtGBaseW H.lm H.τ, vtGOrdW H.lm H.τ, vtIdxcW,
      H.point.map (1 + ·), vtShEqW H.point H.τ, vtShGW H.point H.τ,
      vtIdxBufW H.point H.lm].getD j [] := by
  unfold VtHonest.ownW
  rw [List.append_assoc, List.append_assoc, List.append_assoc,
    List.getD_append _ _ _ _ (by simpa using hj)]

theorem ownW_getD_F {b : ℕ} (hb : b < 3) : (H.ownW B).getD (9 + b) [] = offBits (H.offP.getD b 0) := by
  unfold VtHonest.ownW
  rw [List.append_assoc, List.append_assoc, List.append_assoc,
    List.getD_append_right _ _ _ _ (by simp), List.getD_append _ _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, hb]

theorem ownW_getD_P {i : ℕ} (hi : i < 51) : (H.ownW B).getD (12 + i) [] =
    offDigits (H.offP.getD (3 + i) 0) (H.τ (vtPushSel.getD i default).2.2.2.1) := by
  unfold VtHonest.ownW
  rw [List.append_assoc, List.append_assoc, List.append_assoc,
    List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega),
    List.getD_append _ _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, show 12 + i - 9 - 3 = i by omega, hi]

theorem ownW_getD_C {i : ℕ} (hi : i < 45) : (H.ownW B).getD (63 + i) [] =
    offDigits (H.offC.getD i 0) (H.τ (vtCountSel.getD i default).2.2.2.1) := by
  unfold VtHonest.ownW
  rw [List.append_assoc, List.append_assoc, List.append_assoc,
    List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega),
    List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, show 63 + i - 9 - 3 - 51 = i by omega, hi]

theorem ownW_getD_Z {k : ℕ} (_hk : k < 3) : (H.ownW B).getD (108 + k) [] =
    [zcRoundsW H.cap0 H.target (ofK (addressOfIndex B.cur) * gen ^ 5) H.xsR H.n,
      zcCprodW H.cap0 H.target H.xsR H.n,
      (List.range (H.n + 1)).map (prefixProd 1 H.chiW ((H.point.map (1 + ·)).take H.n))].getD k
      [] := by
  unfold VtHonest.ownW
  rw [List.getD_append_right _ _ _ _ (by simp)]
  congr 1
  simp

end

theorem loadsInBuf_mono {σ : Val} {b1 b2 : List (E × ℕ)} {blk : List Stmt}
    (hsub : ∀ q ∈ b1, ∃ q' ∈ b2, q'.1 = q.1 ∧ q.2 ≤ q'.2) (h : LoadsInBuf σ b1 blk) :
    LoadsInBuf σ b2 blk := by
  intro d p off hm
  obtain ⟨q, hq, j, hp, hj⟩ := h d p off hm
  obtain ⟨q', hq', e1, e2⟩ := hsub q hq
  exact ⟨q', hq', j, by rw [e1]; exact hp, by omega⟩

theorem multilinearEval_zero2 (x : E) : multilinearEval [0, 0] [x] = 0 := by
  simp [multilinearEval, foldPairs]

theorem vt_alloc_vals {rd : Reader} {w : ℕ → E} {args : List E} (hl : args.length = 20) :
    ∀ x ∈ vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz, vtσ rd w args x.1 = w x.1.idx := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := List.mem_filterMap.mp hx
  have hg := vt_goodS (rd := rd) (w := w) hl hs
  cases s with
  | atom a =>
    cases a with
    | hint hk =>
      cases hk with
      | alloc d n =>
        simp only [LeanVM.Guest.Memory.Stmt.allocSz, Option.some.injEq] at hsx
        subst hsx; exact hg
      | allocDyn d n =>
        simp only [LeanVM.Guest.Memory.Stmt.allocSz, Option.some.injEq] at hsx
        subst hsx; exact hg
      | _ => simp [LeanVM.Guest.Memory.Stmt.allocSz] at hsx
    | _ => simp [LeanVM.Guest.Memory.Stmt.allocSz] at hsx
  | _ => simp [LeanVM.Guest.Memory.Stmt.allocSz] at hsx

theorem vt_alloc_var {rd : Reader} {w : ℕ → E} {args : List E} (hl : args.length = 20) {v : ℕ}
    (hv : v ∈ vtAllocVars) : vtσ rd w args (.n v) = w v := by
  have : V.n v ∈ (vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map (fun x ↦ x.1) := by
    rw [vt_allocs]; exact List.mem_map.mpr ⟨v, hv, rfl⟩
  obtain ⟨x, hx, e⟩ := List.mem_map.mp this
  have := vt_alloc_vals (rd := rd) (w := w) hl x hx
  rw [e] at this
  exact this

theorem word_g34 : word 17179869184 0 0 = gen ^ 34 := by
  rw [tb_word_eOfNat, gen_pow_eq_ofK]
  show ofK (K.ofBits 17179869184) = ofK (Parameters.addressOfIndex 34)
  rw [show K.ofBits 17179869184 = Parameters.addressOfIndex 34 by decide +kernel]

theorem logG_gen_pow {e : ℕ} (he : e < 2 ^ 64 - 1) : LeanVM.Guest.Memory.logG (gen ^ e) = e := by
  rw [gen_pow_eq_ofK]; exact LeanVM.Guest.Memory.logG_spec he

theorem vt_evsT_flat_length {H : VtHonest} (h : H.Ok) (hr : H.rows.length = 6) :
    H.evsT.flatten.length = 159 := by
  obtain ⟨hevT6, hevTw⟩ := vt_evsT_shape h hr
  rw [List.length_flatten]
  match H.evsT, hevT6, hevTw with
  | [a, b, c, d, e, f], _, hw' =>
    have := hw' 0 (by norm_num); have := hw' 1 (by norm_num); have := hw' 2 (by norm_num)
    have := hw' 3 (by norm_num); have := hw' 4 (by norm_num); have := hw' 5 (by norm_num)
    simp_all [vtW6]

theorem forall_slice_split {P : Stmt → Prop} (a l1 l2 : ℕ)
    (h1 : ∀ s ∈ (vtPre.drop a).take l1, P s) (h2 : ∀ s ∈ (vtPre.drop (a + l1)).take l2, P s) :
    ∀ s ∈ (vtPre.drop a).take (l1 + l2), P s := forall_slice_join h1 h2

theorem forall_vtPre {P : Stmt → Prop} (h1 : ∀ s ∈ (vtPre.drop 0).take 769, P s)
    (h2 : ∀ s ∈ (vtPre.drop 769).take 1820, P s) (h3 : ∀ s ∈ (vtPre.drop 2589).take 99, P s)
    (h4 : ∀ s ∈ (vtPre.drop 2688).take (6353 - 2688), P s)
    (h5 : ∀ s ∈ (vtPre.drop 6353).take 45, P s) : ∀ s ∈ vtPre, P s := by
  have hlen : vtPre.length = 6398 := by decide +kernel
  have h := forall_slice_split 0 769 (1820 + (99 + (3665 + 45))) h1
    (forall_slice_split 769 1820 (99 + (3665 + 45)) h2
      (forall_slice_split 2589 99 (3665 + 45) h3 (forall_slice_split 2688 3665 45 h4 h5)))
  intro s hs
  apply h
  rw [List.drop_zero, List.take_of_length_le (by omega)]
  exact hs

set_option maxRecDepth 100000 in
theorem vt_allocSz : (vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map (fun x ↦ x.2) =
    [.inl 24, .inl 24, .inl 24, .inl 24, .inl 34, .inr (.n 9), .inl 1728, .inl 864, .inl 153,
      .inr (.n 789), .inr (.n 812), .inr (.n 882)] ++ List.replicate 96 (.inl 9) ++
      [.inr (.n 2604), .inr (.n 2607), .inr (.n 2628)] := by decide +kernel

set_option maxRecDepth 100000 in
theorem vt_bits_consts : tbStmtsEqb [.atom (.const (.n 789) (word 17179869184 0 0))]
      ((vtPre.drop 775).take 1) = true ∧
    tbStmtsEqb [.atom (.const (.n 812) (word 17179869184 0 0))] ((vtPre.drop 797).take 1) = true ∧
    tbStmtsEqb [.atom (.const (.n 882) (word 17179869184 0 0))] ((vtPre.drop 867).take 1) = true := by
  simp only [vtPre_drop]; decide +kernel

section
variable {H : VtHonest} {B : VtBases} {w : ℕ → E} {rd : Reader}

theorem vt_lin_reads (hm : MemLay rd (H.linL B ++ H.ownL B)) {q : ℕ × List E}
    (hq : q ∈ H.linL B) : TbReadsAt rd (ofK (addressOfIndex q.1)) q.2 :=
  hm q (List.mem_append_left _ hq)

theorem vt_own_reads (hm : MemLay rd (H.linL B ++ H.ownL B)) (hw : VtWOk H B w) {j : ℕ}
    (hj : j < 111) : TbReadsAt rd (w (vtAllocVars.getD j 0)) ((H.ownW B).getD j []) := by
  rw [hw.alloc j hj]
  have hb := ownB_length H B
  have ho := ownW_length H B
  have hmem : ((H.ownB B).getD j 0, (H.ownW B).getD j []) ∈ H.ownL B := by
    rw [VtHonest.ownL, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    exact List.mem_iff_getElem.mpr ⟨j, by simp [hb, ho]; omega, by simp⟩
  have := hm _ (List.mem_append_right _ hmem)
  exact this

theorem vt_own_reads' (hm : MemLay rd (H.linL B ++ H.ownL B)) (hw : VtWOk H B w) {j v : ℕ}
    (hj : j < 111) (hv : vtAllocVars.getD j 0 = v) {ws : List E} (he : (H.ownW B).getD j [] = ws) :
    TbReadsAt rd (w v) ws := hv ▸ he ▸ vt_own_reads hm hw hj

end

/-- The buffers the loads read: the layout's. -/
noncomputable def VtHonest.bufs (H : VtHonest) (B : VtBases) : List (E × ℕ) :=
  (H.linL B ++ H.ownL B).map fun q ↦ (ofK (addressOfIndex q.1), q.2.length)

/-- The honest returns: the capacity, the cursor past the stream, `g^n`, the bytecode value, the
public input's challenge and the evaluations' cursor (`col_eval_words`). -/
noncomputable def VtHonest.retsH (H : VtHonest) (B : VtBases) : List E :=
  H.s3.squeeze.2.cap ++ [ofK (addressOfIndex B.cur) * gen ^ 5 * gen ^ (3 * H.n) * gen ^ 159,
    gen ^ H.n, H.bv, H.rm, ofK (addressOfIndex B.cur) * gen ^ 5 * gen ^ (3 * H.n)]

/-- What the calls' placement reads of the valuation: `kappa_base` and the shared lengths. -/
def VtKbSh (H : VtHonest) (σ : Val) : Prop :=
  (∀ i < 8, σ (.n (28 + i)) = gen ^ ([0, H.lm] ++ vtTauList H.τ).getD i 0) ∧
    ∀ t < 6, σ (.n (vtShLen t)) = gen ^ (H.μ - H.τ t)

set_option maxRecDepth 20000 in
/-- **`verify_tables` is complete at the `Rel` level**, with `kappa_base` and the shared
lengths. -/
theorem vt_rel_completeF {H : VtHonest} (h : H.Ok) (hs : VtShape H) (B : VtBases) {w : ℕ → E}
    (hw : VtWOk H B w) {rd : Reader} (hlow : LowDefB 14 rd)
    (hm : MemLay rd (H.linL B ++ H.ownL B)) :
    ((∀ s ∈ vtPre, VSH (coreProgram.Rel rd) rd (vtσ rd w (H.args B)) s) ∧
      LoadsInBuf (vtσ rd w (H.args B)) (H.bufs B) vtPre ∧
      (vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map
        (fun x ↦ x.2.elim id fun s ↦ LeanVM.Guest.Memory.logG (vtσ rd w (H.args B) s)) = H.sizes ∧
      ((vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map Prod.fst).map (vtσ rd w (H.args B)) =
        (H.ownB B).map (fun b ↦ ofK (addressOfIndex b)) ∧
      vtRets.map (vtσ rd w (H.args B)) = H.retsH B) ∧ VtKbSh H (vtσ rd w (H.args B)) := by
  obtain ⟨hlm, hlmμ, h19, hμ33, hr, hτ29, hτμ, hal, hf, hfcan, hfitP, hfitC, hbc⟩ := hs
  have hl : (H.args B).length = 20 := rfl
  have p : ∀ i < 20, (vtσ rd w (H.args B)) (.n i) = (H.args B).getD i 0 := fun i hi ↦ vt_param hl hi
  -- the caller's buffers
  have mCur : TbReadsAt rd (ofK (addressOfIndex B.cur)) H.curW :=
    vt_lin_reads (q := (B.cur, H.curW)) hm (by simp [VtHonest.linL])
  have mZeta : TbReadsAt rd (ofK (addressOfIndex B.zeta)) H.point :=
    vt_lin_reads (q := (B.zeta, H.point)) hm (by simp [VtHonest.linL])
  have mDims : TbReadsAt rd (ofK (addressOfIndex B.dims)) H.dimsW :=
    vt_lin_reads (q := (B.dims, H.dimsW)) hm (by simp [VtHonest.linL])
  have mRows : TbReadsAt rd (ofK (addressOfIndex B.rows)) (H.rows.map eOfNat) :=
    vt_lin_reads (q := (B.rows, H.rows.map eOfNat)) hm (by simp [VtHonest.linL])
  have mSq : TbReadsAt rd (ofK (addressOfIndex B.sq)) expTableWords :=
    vt_lin_reads (q := (B.sq, expTableWords)) hm (by simp [VtHonest.linL])
  have mFpw : TbReadsAt rd (ofK (addressOfIndex B.fpw)) (eqKernel H.alphas) :=
    vt_lin_reads (q := (B.fpw, eqKernel H.alphas)) hm (by simp [VtHonest.linL])
  have mPool : TbReadsAt rd (ofK (addressOfIndex B.pool)) H.poolW :=
    vt_lin_reads (q := (B.pool, H.poolW)) hm (by simp [VtHonest.linL])
  have mChi : TbReadsAt rd (ofK (addressOfIndex B.chi)) H.chiW :=
    vt_lin_reads (q := (B.chi, H.chiW)) hm (by simp [VtHonest.linL])
  -- the own buffers
  have hd := fun j (hj : j < 9) ↦ ownW_getD_head H B hj
  have o36 : TbReadsAt rd (w 36) (vtGKeyW H.lm H.τ) := vt_own_reads' hm hw (j := 0) (by norm_num) rfl (hd 0 (by norm_num))
  have o37 : TbReadsAt rd (w 37) (vtGSizeW H.lm H.τ) := vt_own_reads' hm hw (j := 1) (by norm_num) rfl (hd 1 (by norm_num))
  have o38 : TbReadsAt rd (w 38) (vtGBaseW H.lm H.τ) := vt_own_reads' hm hw (j := 2) (by norm_num) rfl (hd 2 (by norm_num))
  have o39 : TbReadsAt rd (w 39) (vtGOrdW H.lm H.τ) := vt_own_reads' hm hw (j := 3) (by norm_num) rfl (hd 3 (by norm_num))
  have o668 : TbReadsAt rd (w 668) vtIdxcW := vt_own_reads' hm hw (j := 4) (by norm_num) rfl (hd 4 (by norm_num))
  have o703 : TbReadsAt rd (w 703) (H.point.map (1 + ·)) := vt_own_reads' hm hw (j := 5) (by norm_num) rfl (hd 5 (by norm_num))
  have o705 : TbReadsAt rd (w 705) (vtShEqW H.point H.τ) := vt_own_reads' hm hw (j := 6) (by norm_num) rfl (hd 6 (by norm_num))
  have o706 : TbReadsAt rd (w 706) (vtShGW H.point H.τ) := vt_own_reads' hm hw (j := 7) (by norm_num) rfl (hd 7 (by norm_num))
  have o781 : TbReadsAt rd (w 781) (vtIdxBufW H.point H.lm) := vt_own_reads' hm hw (j := 8) (by norm_num) rfl (hd 8 (by norm_num))
  have oF : ∀ b < 3, TbReadsAt rd (w (vtFwW b + 6)) (offBits (H.offP.getD b 0)) := fun b hb ↦
    vt_own_reads' hm hw (j := 9 + b) (by omega) (vtAllocVars_F b hb) (ownW_getD_F H B hb)
  have oP : ∀ i < 51, TbReadsAt rd (w (vtPushSel.getD i default).2.2.1)
      (offDigits (H.offP.getD (3 + i) 0) (H.τ (vtPushSel.getD i default).2.2.2.1)) := fun i hi ↦
    vt_own_reads' hm hw (j := 12 + i) (by omega) (vtAllocVars_P i hi) (ownW_getD_P H B hi)
  have oC : ∀ i < 45, TbReadsAt rd (w (vtCountSel.getD i default).2.2.1)
      (offDigits (H.offC.getD i 0) (H.τ (vtCountSel.getD i default).2.2.2.1)) := fun i hi ↦
    vt_own_reads' hm hw (j := 63 + i) (by omega) (vtAllocVars_C i hi) (ownW_getD_C H B hi)
  have oZ := fun k (hk : k < 3) ↦ vt_own_reads hm hw (j := 108 + k) (by omega)
  have oR : TbReadsAt rd (w 2605)
      (zcRoundsW H.cap0 H.target (ofK (addressOfIndex B.cur) * gen ^ 5) H.xsR H.n) := by
    have := oZ 0 (by norm_num); rwa [vtAllocVars_Z.1, ownW_getD_Z H B (by norm_num)] at this
  have oCp : TbReadsAt rd (w 2608) (zcCprodW H.cap0 H.target H.xsR H.n) := by
    have := oZ 1 (by norm_num); rwa [vtAllocVars_Z.2.1, ownW_getD_Z H B (by norm_num)] at this
  have oPe : TbReadsAt rd (w 2629)
      ((List.range (H.n + 1)).map (prefixProd 1 H.chiW ((H.point.map (1 + ·)).take H.n))) := by
    have := oZ 2 (by norm_num); rwa [vtAllocVars_Z.2.2, ownW_getD_Z H B (by norm_num)] at this
  have hrows : ∀ t < 6, LoadHolds rd ((vtσ rd w (H.args B)) (.n 11)) t (eOfNat (vtRw H.rows t)) := by
    intro t ht
    rw [p 11 (by norm_num)]
    have := tb_load_of mRows (k := t) (by simp [hr]; omega)
    rwa [List.getD_eq_getElem _ _ (by simp [hr]; omega), List.getElem_map,
      ← List.getD_eq_getElem _ 0 (by omega)] at this
  have hrun : ∀ t < 6, RunTables rd (w 705 * gen ^ (288 * t)) (w 706 * gen ^ (144 * t))
      (H.point.length - H.τ t) (H.point.drop (H.τ t)) ((H.point.map (1 + ·)).drop (H.τ t))
      ((gSquaresList.drop (H.τ t)).take (H.point.length - H.τ t)) :=
    fun t ht ↦ vt_runTables hμ33 o705 o706 ht
  -- statements `0 ..< 769`
  obtain ⟨sV, s20, s25, skb, s36, sP, sC, sPad, sSh, s581, s668, s703, s705, s706⟩ :=
    vtS_complete (rd := rd) (w := w) (args := H.args B) hl hlow hlm H.point hμ33 H.τ (vtRw H.rows)
      (fun t ht ↦ vtHt_eq hr ht) hτ29 hτμ (by rw [p 8 (by norm_num)]; exact mZeta)
      (p 9 (by norm_num)) (by rw [p 10 (by norm_num)]; exact mDims) hrows
      (by rw [p 12 (by norm_num)]; exact vt_expTablesAt mSq) o36 o37 o38 o39 o668 o703 hrun
      hw.pads hw.w704
  rw [vt_sizesP_eq] at sP
  rw [vt_sizesC_eq] at sC
  -- statements `769 ..< 2589`
  have hcurs := mCur
  rw [VtHonest.curW, tbReadsAt_append, tbReadsAt_append] at hcurs
  obtain ⟨⟨mX5, mXR⟩, mEv⟩ := hcurs
  have hx5 := h.hx5
  have hpool5 : ∀ i < 5, LoadHolds rd ((H.args B).getD 15 0) i (H.xs5.getD i 0) := by
    intro i hi
    have := tb_load_of mPool (k := i) (by simp [VtHonest.poolW, VtHonest.pcW, hx5]; omega)
    rwa [VtHonest.poolW, List.append_assoc, List.getD_append _ _ _ _ (by omega)] at this
  have hcan5 : ∀ i < 5, IsCanonical128 ((H.args B).getD i 0) := by
    intro i hi; interval_cases i <;> exact hfcan _ (by norm_num)
  have HB : VtBHyp rd w (H.args B) ⟨H.point, H.lm, H.rows, H.alphas, H.xs5, H.bc⟩ :=
    { hl := hl, hlow := hlow, hml := hμ33, hlmμ := hlmμ, h19 := h19, hr := hr, hτμ := hτμ,
      hmu := rfl, hz := mZeta, hal := hal, hW := mFpw, hxl := hx5, hcur := mX5,
      hpool := hpool5, hcan := hcan5, e20 := s20, ekb := skb, eoP := sP, eoC := sC, eSh := sSh,
      e668 := s668, e703 := s703, e705 := s705, e706 := s706, hpw := sPad, hidxc := o668,
      hz1 := o703, hrun := hrun, hidxB := o781, hfitP := hfitP, hfitC := hfitC, hbitsF := oF,
      hdigP := oP, hdigC := oC, hwF := hw.hwF, hwP := hw.hwP, hwC := hw.hwC, hwI := hw.hwI,
      hbc := hbc }
  obtain ⟨bV, bLd, bFresh, b1812, b2057, b2499, -, -, -, -, -, -, bP, bC⟩ := vtB_complete HB
  -- values the bus fixes
  have e14 : (vtσ rd w (H.args B)) (.n 14) = H.beta := p 14 (by norm_num)
  have bF : vtFreshWords (vtσ rd w (H.args B)) = H.xs5 := bFresh
  have eMem : [(vtσ rd w (H.args B)) (.n 830), (vtσ rd w (H.args B)) (.n 843), (vtσ rd w (H.args B)) (.n 856)] = H.xs5.take 3 := by
    rw [← bF]; rfl
  have e1835 : (vtσ rd w (H.args B)) (.n 1843) = H.xs5.getD 3 0 := by
    rw [← bF]; simp only [vtFreshWords, List.getD_cons_succ, List.getD_cons_zero]
  have e1890 : (vtσ rd w (H.args B)) (.n 1898) = H.xs5.getD 4 0 := by
    rw [← bF]; simp only [vtFreshWords, List.getD_cons_succ, List.getD_cons_zero]
  have e581 : (vtσ rd w (H.args B)) (.n 581) = H.bv := s581.trans hw.w581
  have ev : ∀ i < 3, (vtσ rd w (H.args B)) (.n (25 + i)) = H.values.getD i 0 := fun i hi ↦ by
    rw [s25 i hi, p (17 + i) (by omega)]
    interval_cases i <;> rfl
  have e25 := ev 0 (by norm_num)
  have e26 := ev 1 (by norm_num)
  have e27 := ev 2 (by norm_num)
  simp only [Nat.add_zero] at e25
  rw [e14, eMem, e581, e25] at b1812
  rw [e14, eMem, e1835, e1890, e581, e25, e26] at b2057
  rw [e14, eMem, e1835, e1890, e581, e25, e26, e27] at b2499
  -- the sponge after the framework words
  obtain ⟨fF, fR, fC⟩ := vt_fresh_good (rd := rd) (w := w) hl
  have hS1 : vtFreshFs (vtσ rd w (H.args B)) = H.s1 := by
    have hfl : [(vtσ rd w (H.args B)) (.n 0), (vtσ rd w (H.args B)) (.n 1), (vtσ rd w (H.args B)) (.n 2), (vtσ rd w (H.args B)) (.n 3), (vtσ rd w (H.args B)) (.n 4)] = H.f := by
      rw [p 0 (by norm_num), p 1 (by norm_num), p 2 (by norm_num), p 3 (by norm_num),
        p 4 (by norm_num)]
      show [H.f.getD 0 0, H.f.getD 1 0, H.f.getD 2 0, H.f.getD 3 0, H.f.getD 4 0] = H.f
      match H.f, hf with
      | [a, b, c, d, e], _ => rfl
    unfold vtFreshFs VtHonest.s1 VtHonest.s0
    rw [hfl, bF]
  have hzt : zTarget (vtσ rd w (H.args B)) H.s1.squeeze.1 = H.target := by
    unfold zTarget
    exact vt_target_eq H _ _ _ _ b1812 b2057 b2499 rfl
  -- statements `2589 ..< 2688`
  have hn := vt_n_ex (H := H) hr
  have hnμ : H.n ≤ H.point.length := by
    obtain ⟨t, ht, e⟩ := hn; rw [← e]; exact hτμ t ht
  have hlow64 : ∀ i < 64, (rd (Parameters.addressOfIndex i)).isSome := fun i hi ↦ hlow i
    (by norm_num; omega)
  have hkbt : ∀ t < 6, (vtσ rd w (H.args B)) (.n (30 + t)) = gen ^ H.τ t := by
    intro t ht
    have := skb (2 + t) (by omega)
    rw [show 28 + (2 + t) = 30 + t by omega, show 2 + t = t + 1 + 1 by omega] at this
    rw [this]
    simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
    rw [vtTauList_getD ht]
  have hxs : TbReadsAt rd ((vtσ rd w (H.args B)) (.n 5) * gen ^ 5) H.xsR := by
    rw [p 5 (by norm_num)]
    have := mXR
    rw [hx5] at this
    exact this
  have hS1' : H.s1 = vtFreshFs (vtσ rd w (H.args B)) := hS1.symm
  obtain ⟨zV, zOut⟩ := vtZ_complete (rd := rd) (w := w) hl (m := H.point.length) (n := H.n)
    (τ := H.τ) (fun t ht ↦ vt_n_ge hr ht) hn hnμ (by omega) (p 9 (by norm_num)) hkbt hlow64
    hw.w2500 (S := H.s1) (by rw [hS1', fF]; exact fR) (by rw [hS1', fF]; rfl)
    (by rw [hS1', fF, fR]; exact fC) h.hxR hxs
    (by rw [hzt, p 5 (by norm_num)]; exact oR) (by rw [hzt]; exact oCp)
    (by rw [hzt, p 16 (by norm_num)]; exact mChi)
    (zs1 := H.point.map (1 + ·)) (by rw [s703]; exact o703) (by simpa using hnμ)
    (by rw [hzt]; exact oPe)
  obtain ⟨z2500, z2572, -, z2582, z2588, z2591, z2612, z2589, z2592, z2613, zRec, z2609,
    z2610⟩ := zOut
  rw [hzt] at zRec z2610
  change _ = (zcRec H.cap0 H.target H.xsR H.n).1 at zRec
  change _ = (zcRec H.cap0 H.target H.xsR H.n).2 at z2610
  -- statements `2688 ..< 6353`
  obtain ⟨hevT6, hevTw⟩ := vt_evsT_shape h hr
  have hev157 := vt_evsT_flat_length h hr
  have hevC : TbReadsAt rd ((vtσ rd w (H.args B)) (.n 2625)) H.evsT.flatten := by
    rw [z2609, p 5 (by norm_num), mul_assoc, ← pow_add]
    have : (H.xs5 ++ H.xsR).length = 5 + 3 * H.n := by simp [hx5, h.hxR]
    rw [← this]; exact mEv
  have hevs : vtEvs (vtσ rd w (H.args B)) = H.evsT.flatten := by
    apply List.ext_getElem (by rw [vtEvs_length, hev157])
    intro k h1 _
    have hk : k < 159 := by simpa [vtEvs_length] using h1
    have e := (vtF_evRead hl hevC (by omega) hk).2
    simp only [vtEvs, List.getElem_map, List.getElem_range]
    rw [e, List.getD_eq_getElem _ _ (by omega)]
  have hevsT : vtEvsT (vtσ rd w (H.args B)) = H.evsT := by
    apply lists_eq_of_flatten _ _ (by rw [vtEvsT_length, hevT6]) (fun i ↦ ?_)
      (by rw [vt_evsT_flatten, hevs])
    rcases Nat.lt_or_ge i 6 with hi | hi
    · rw [hevTw i hi]; simp [vtEvsT, vtEvT]; interval_cases i <;> rfl
    · rw [List.getD_eq_default _ _ (by simp [vtEvsT]; omega),
        List.getD_eq_default _ _ (by omega)]
  have hpts : H.pts.length = H.n := by simp [VtHonest.pts]
  have hcap0 : AllCanonical H.cap0 := by
    intro c hc
    simp only [VtHonest.cap0, Fs.squeeze, capOf, List.mem_cons, List.mem_nil_iff,
      or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> exact canon_cellsOfState _ _ _
  have hcapR := zcRec_canon (cl0 := H.target) (xs := H.xsR) hcap0 H.n
  have hfinσ := (vt_spec h).1
  have z1 : TbReadsAt rd ((vtσ rd w (H.args B)) (.n 703)) (H.point.map (1 + ·)) := by rw [s703]; exact o703
  obtain ⟨fV, -, -, fSp, -⟩ := vtF_complete (rd := rd) (w := w) hl H.bc hbc hr hkbt bP bC
    (vt_pull_good hl) z1 (vt_xi_good hl) hal (by rw [p 13 (by norm_num)]; exact mFpw)
    z2500 (fun t ht ↦ vt_n_ge hr ht) hnμ hpts
    (by
      intro j hj
      rw [z2592]
      have := tb_load_of oCp (k := j) (by simp [zcCprodW]; omega)
      rw [zcCprodW, List.getD_eq_getElem _ _ (by simp; omega)] at this
      simpa [VtHonest.pts, ← List.map_take, List.take_range, min_eq_left hj] using this)
    (by
      refine ⟨H.chiW, (H.point.map (1 + ·)).take H.n, by simp [VtHonest.chiW, zcChis],
        by simp; omega, by rw [p 16 (by norm_num)]; exact mChi,
        tbReadsAt_take z1 _, fun j hj ↦ ?_⟩
      rw [z2613]
      have := tb_load_of oPe (k := j) (by simp; omega)
      simpa [List.getD_eq_getElem?_getD, Nat.lt_succ_of_le hj] using this)
    (by
      intro i hi
      rw [p 16 (by norm_num)]
      show LoadHolds rd (ofK (addressOfIndex B.chi)) _ _
      have := tb_load_of mChi (k := H.n - 1 - i) (by simp [VtHonest.chiW, zcChis]; omega)
      simpa [VtHonest.chiW, zcChis, VtHonest.pts, List.getD_eq_getElem?_getD, List.getElem?_reverse,
        hi, show H.n - 1 - (H.n - 1 - i) = i by omega, show H.n - 1 - i < H.n by omega] using this)
    hev157 hevC
    (by
      intro i hi
      have hm : (vtσ rd w (H.args B)) (.n (2620 + i)) ∈ (zcRec H.cap0 H.target H.xsR H.n).1 := by
        rw [← zRec]; interval_cases i <;> simp
      exact hcapR _ hm)
    (by
      rw [z2610, hevsT, z2572, e14, eMem, e1835, e1890, e581, e25, e26, e27, ← hS1]
      have hf := hfinσ
      unfold VtHonest.terms VtHonest.nC at hf
      rw [vt_nConstraints] at hf
      rw [hS1]
      exact hf)
  -- statements `6353 ..< 6398`
  have hcv : vtCapV (vtσ rd w (H.args B)) 0 = (zcRec H.cap0 H.target H.xsR H.n).1 := by
    rw [← zRec]; simp [vtCapV, vtPermCap, List.range_succ]
  have hS3 : vtEvalFs (vtσ rd w (H.args B)) = H.s3 := by
    unfold VtHonest.s3 VtHonest.s2
    rw [vtEvalFs, hcv, hevs]
  obtain ⟨-, eR, eC, eCan⟩ := vt_evalFs_good (rd := rd) (w := w) hl fSp
  rw [hS3] at eR eC eCan
  have hc6 : IsCanonical128 ((vtσ rd w (H.args B)) (.n 6)) := by
    rw [p 6 (by norm_num)]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
  have hc7 : IsCanonical128 ((vtσ rd w (H.args B)) (.n 7)) := by
    rw [p 7 (by norm_num)]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
  have hpc : ∀ i < 3, LoadHolds rd (ofK (addressOfIndex B.pool)) (164 + i) (H.pcW.getD i 0) := by
    intro i hi
    have := tb_load_of mPool (k := 164 + i)
      (by simp [VtHonest.poolW, VtHonest.pcW, hx5, hev157]; omega)
    rwa [VtHonest.poolW, List.getD_append_right _ _ _ _ (by simp [hx5, hev157]),
      show 164 + i - (H.xs5 ++ H.evsT.flatten).length = i by simp [hx5, hev157]] at this
  obtain ⟨tV, tOut⟩ := vtZt_complete (rd := rd) (w := w) hl (S2 := H.s3) eR eC eCan hc6 hc7
    (by rw [p 15 (by norm_num), p 6 (by norm_num), p 7 (by norm_num)]; exact hpc 0 (by norm_num))
    (by rw [p 15 (by norm_num), p 6 (by norm_num), p 7 (by norm_num)]; exact hpc 1 (by norm_num))
    (by
      rw [p 15 (by norm_num)]
      have := hpc 2 (by norm_num)
      simp only [VtHonest.pcW, List.map_cons, List.map_nil, List.getD_cons_succ,
        List.getD_cons_zero] at this
      rw [show ((digestHalves H.pi).1.limb 2) = 0 from rfl,
        show ((digestHalves H.pi).2.limb 2) = 0 from rfl, ofK_zero, multilinearEval_zero2] at this
      exact this)
  obtain ⟨-, tCap, t6862, t6863, t6864, t6865, t6866⟩ := tOut
  -- every statement
  refine ⟨⟨forall_vtPre sV bV (z_slice_tail zV) fV tV, ?_, ?_, ?_, ?_⟩, skb, sSh⟩
  rotate_left
  · -- the sizes
    have hm1 : (vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map
        (fun x ↦ x.2.elim id fun s ↦ LeanVM.Guest.Memory.logG ((vtσ rd w (H.args B)) s)) =
        ((vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map (fun x ↦ x.2)).map
          (fun y ↦ y.elim id fun s ↦ LeanVM.Guest.Memory.logG ((vtσ rd w (H.args B)) s)) := by
      rw [List.map_map]; rfl
    rw [hm1, vt_allocSz]
    obtain ⟨c1, c2, c3⟩ := vt_bits_consts
    have hb : ∀ (v n : ℕ), tbStmtsEqb [.atom (.const (.n v) (word 17179869184 0 0))]
        ((vtPre.drop n).take 1) = true → LeanVM.Guest.Memory.logG ((vtσ rd w (H.args B)) (.n v)) = 34 := by
      intro v n hc
      have g := (vt_goodL (rd := rd) (w := w) hl _ _ hc).1
      simp only [GoodS, fixNe, Good] at g
      rw [g, word_g34, logG_gen_pow (by norm_num)]
    simp only [List.map_append, List.map_cons, List.map_nil, List.map_replicate, Sum.elim_inl,
      Sum.elim_inr, id]
    rw [hb _ _ c1, hb _ _ c2, hb _ _ c3, p 9 (by norm_num), z2588, z2591, z2612]
    simp only [VtHonest.args, List.getD_cons_succ, List.getD_cons_zero]
    rw [logG_gen_pow (e := H.μ) (by unfold VtHonest.μ; omega),
      logG_gen_pow (e := 7 * (H.n + 1)) (by omega), logG_gen_pow (e := H.n + 1) (by omega)]
    rfl
  · -- the allocations' pointers
    rw [show (vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map Prod.fst =
      vtAllocVars.map V.n from vt_allocs, List.map_map]
    apply List.ext_getElem (by simp [vtAllocVars_length, ownB_length])
    intro j h1 h2
    have hj : j < 111 := by simpa [vtAllocVars_length] using h1
    simp only [List.getElem_map, Function.comp]
    rw [vt_alloc_var hl (List.getElem_mem _), ← List.getD_eq_getElem _ 0 (by
      simpa [vtAllocVars_length] using h1), hw.alloc j hj, List.getD_eq_getElem _ _ (by
      rw [ownB_length]; exact hj)]
  · -- the returns
    rw [VtHonest.retsH, ← tCap]
    simp only [vtRets, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [t6862, t6863, t6864, t6865, t6866, z2609, z2500, s581, hw.w581, p 5 (by norm_num)]
    rfl
  · -- the loads
    have mem : ∀ q ∈ H.linL B ++ H.ownL B, (ofK (addressOfIndex q.1), q.2.length) ∈ H.bufs B :=
      fun q hq ↦ List.mem_map.mpr ⟨q, hq, rfl⟩
    have lin : ∀ q ∈ H.linL B, (ofK (addressOfIndex q.1), q.2.length) ∈ H.bufs B :=
      fun q hq ↦ mem q (List.mem_append_left _ hq)
    have own : ∀ j < 111, (w (vtAllocVars.getD j 0), ((H.ownW B).getD j []).length) ∈ H.bufs B := by
      intro j hj
      rw [hw.alloc j hj]
      refine mem ((H.ownB B).getD j 0, (H.ownW B).getD j []) (List.mem_append_right _ ?_)
      rw [VtHonest.ownL, List.getD_eq_getElem _ _ (by rw [ownB_length]; omega),
        List.getD_eq_getElem _ _ (by rw [ownW_length]; omega)]
      exact List.mem_iff_getElem.mpr ⟨j, by simp [ownB_length, ownW_length]; omega, by simp⟩
    have own' : ∀ j < 111, ∀ v, vtAllocVars.getD j 0 = v → ∀ ws, (H.ownW B).getD j [] = ws →
        (w v, ws.length) ∈ H.bufs B := fun j hj v e ws e' ↦ e ▸ e' ▸ own j hj
    have conv : ∀ {blk : List Stmt}, LoadsInBuf (vtσ rd w (H.args B)) (H.bufs B) blk →
        ∀ s ∈ blk, ∀ d p' off, s = .atom (.load d p' off) → InBuf (vtσ rd w (H.args B)) (H.bufs B) p' off :=
      fun h s hs d p' off e ↦ h d p' off (e ▸ hs)
    have lens : H.dimsW.length = 7 ∧ (H.rows.map eOfNat).length = 6 ∧
        expTableWords.length = 236 ∧ (eqKernel H.alphas).length = 16 ∧ H.poolW.length = 167 ∧
        H.curW.length = 5 + 3 * H.n + 159 := by
      refine ⟨by simp [VtHonest.dimsW, vtTauList], by simp [hr],
        by simp [expTableWords, length_etWordsN], by rw [vt_length_eqKernel, hal]; rfl,
        by simp [VtHonest.poolW, VtHonest.pcW, hx5, hev157],
        by rw [VtHonest.curW, List.length_append, List.length_append, hx5, h.hxR, hev157]⟩
    obtain ⟨lD, lR, lS, lF, lP, lCu⟩ := lens
    have mD := lin (B.dims, H.dimsW) (by simp [VtHonest.linL])
    have mR := lin (B.rows, H.rows.map eOfNat) (by simp [VtHonest.linL])
    have mS := lin (B.sq, expTableWords) (by simp [VtHonest.linL])
    have mF := lin (B.fpw, eqKernel H.alphas) (by simp [VtHonest.linL])
    have mP := lin (B.pool, H.poolW) (by simp [VtHonest.linL])
    have mCu := lin (B.cur, H.curW) (by simp [VtHonest.linL])
    simp only [lD, lR, lS, lF, lP, lCu] at mD mR mS mF mP mCu
    have hd' := fun j (hj : j < 9) ↦ ownW_getD_head H B hj
    have gb : ∀ i < 4, ((vtσ rd w (H.args B)) (.n (36 + i)), 24) ∈ H.bufs B := by
      intro i hi
      have e : vtAllocVars.getD i 0 = 36 + i := by interval_cases i <;> rfl
      have hlen : ((H.ownW B).getD i []).length = 24 := by
        rw [hd' i (by omega)]; interval_cases i <;> simp [vtGKeyW, vtGSizeW, vtGBaseW, vtGOrdW]
      rw [s36 i hi, ← e, ← hlen]; exact own i (by omega)
    have g668 : ((vtσ rd w (H.args B)) (.n 668), 34) ∈ H.bufs B := by
      have := own' 4 (by norm_num) 668 rfl _ (hd' 4 (by norm_num))
      rw [s668]; simpa [vtIdxcW] using this
    have LS := vtS_loads (bufs := H.bufs B) sV (fun q hq ↦ by
        simp only [vtBufsSIdx, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
        · rw [p 10 (by norm_num)]; exact mD
        · rw [p 11 (by norm_num)]; exact mR
        · rw [p 12 (by norm_num)]; exact mS
        · exact gb 0 (by norm_num)
        · exact gb 1 (by norm_num)
        · exact gb 2 (by norm_num)
        · exact gb 3 (by norm_num)
        · exact g668) hlm hτ29 (by rw [p 10 (by norm_num)]; exact mDims)
      (by rw [show (39 : ℕ) = 36 + 3 from rfl, s36 3 (by norm_num)]; exact o39)
    have LB : LoadsInBuf (vtσ rd w (H.args B)) (H.bufs B) ((vtPre.drop 769).take 1820) := by
      refine loadsInBuf_mono (fun q hq ↦ ?_) bLd
      simp only [vtBufsB, vtBufsBIdx, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff,
        or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact ⟨_, mCu, by simp only [p 5 (by norm_num)]; rfl, by simp only; omega⟩
      · exact ⟨_, mF, by simp only [p 13 (by norm_num)]; rfl, le_rfl⟩
      · exact ⟨_, mP, by simp only [p 15 (by norm_num)]; rfl, by simp only; omega⟩
      · refine ⟨_, own' 8 (by norm_num) 781 rfl _ (hd' 8 (by norm_num)), ?_,
          by simp [vtIdxBufW]⟩
        simp only [vt_alloc_var hl (v := 781) (by unfold vtAllocVars; simp)]
    have mR108 : (w 2605, 7 * (H.n + 1)) ∈ H.bufs B := by
      have := own' 108 (by norm_num) _ vtAllocVars_Z.1 _ (ownW_getD_Z H B (k := 0) (by norm_num))
      rwa [List.getD_cons_zero, zcRoundsW_len (cap0_length H) H.n] at this
    have mR109 : (w 2608, H.n + 1) ∈ H.bufs B := by
      have := own' 109 (by norm_num) _ vtAllocVars_Z.2.1 _ (ownW_getD_Z H B (k := 1) (by norm_num))
      simpa [zcCprodW] using this
    have mR110 : (w 2629, H.n + 1) ∈ H.bufs B := by
      have := own' 110 (by norm_num) _ vtAllocVars_Z.2.2 _ (ownW_getD_Z H B (k := 2) (by norm_num))
      simpa using this
    have LZ := z_slice_tail (conv (vtZ_inBuf (rd := rd) hl hw.w2500 (bufs := H.bufs B) mR108 mR109))
    have LF := vtF_loadsInBuf (rd := rd) (w := w) hl (bufs := H.bufs B)
      ⟨_, mF, 0, by rw [p 13 (by norm_num), pow_zero, mul_one]; rfl, by omega⟩
      ⟨_, mCu, 5 + 3 * H.n, by rw [z2609, p 5 (by norm_num), mul_assoc, ← pow_add]; rfl, by omega⟩
      hkbt z2500 (fun t ht ↦ vt_n_ge hr ht)
      (BufWin.of_mem (by rw [z2592]; exact mR109)) (BufWin.of_mem (by rw [z2613]; exact mR110))
    have LT := vtZt_inBuf (rd := rd) (w := w) (args := H.args B) (bufs := H.bufs B)
      (by rw [p 15 (by norm_num)]; exact mP)
    intro d p' off hs
    exact forall_vtPre (P := fun s ↦ ∀ d p' off, s = .atom (.load d p' off) →
      InBuf (vtσ rd w (H.args B)) (H.bufs B) p' off) (conv LS) (conv LB) LZ (conv LF)
      (conv LT) _ hs d p' off rfl

/-- **`verify_tables` is complete at the `Rel` level.** -/
theorem vt_rel_complete {H : VtHonest} (h : H.Ok) (hs : VtShape H) (B : VtBases) {w : ℕ → E}
    (hw : VtWOk H B w) {rd : Reader} (hlow : LowDefB 14 rd)
    (hm : MemLay rd (H.linL B ++ H.ownL B)) :
    (∀ s ∈ vtPre, VSH (coreProgram.Rel rd) rd (vtσ rd w (H.args B)) s) ∧
      LoadsInBuf (vtσ rd w (H.args B)) (H.bufs B) vtPre ∧
      (vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map
        (fun x ↦ x.2.elim id fun s ↦ LeanVM.Guest.Memory.logG (vtσ rd w (H.args B) s)) = H.sizes ∧
      ((vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map Prod.fst).map (vtσ rd w (H.args B)) =
        (H.ownB B).map (fun b ↦ ofK (addressOfIndex b)) ∧
      vtRets.map (vtσ rd w (H.args B)) = H.retsH B :=
  (vt_rel_completeF h hs B hw hlow hm).1

/-- **`vt_rel_complete` with the explicit oracle** `vtW`. -/
theorem vt_rel_complete_vtW {H : VtHonest} (h : H.Ok) (hs : VtShape H) (B : VtBases)
    {rd : Reader} (hlow : LowDefB 14 rd) (hm : MemLay rd (H.linL B ++ H.ownL B)) :
    (∀ s ∈ vtPre, VSH (coreProgram.Rel rd) rd (vtσ rd (vtW H B) (H.args B)) s) ∧
      LoadsInBuf (vtσ rd (vtW H B) (H.args B)) (H.bufs B) vtPre ∧
      (vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map (fun x ↦ x.2.elim id fun s ↦
        LeanVM.Guest.Memory.logG (vtσ rd (vtW H B) (H.args B) s)) = H.sizes ∧
      ((vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map Prod.fst).map
        (vtσ rd (vtW H B) (H.args B)) = (H.ownB B).map (fun b ↦ ofK (addressOfIndex b)) ∧
      vtRets.map (vtσ rd (vtW H B) (H.args B)) = H.retsH B :=
  vt_rel_complete h hs B (vtW_ok H B) hlow hm

end
end LeanVM.Guest.B1.Tables
