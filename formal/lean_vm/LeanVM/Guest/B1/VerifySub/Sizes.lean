/-
  LeanVM.Guest.B1.VerifySub.Sizes

  The announced sizes and the layout's logarithms, on the specification's side: `readAnnouncedSizes`
  on honest words, the stack's and the push side's log-sizes as `log2Ceil` of sums of powers of two.
-/

module

public import LeanVM.Guest.B1.Tables.Interface
public import LeanVM.Guest.B1.Common.Run

/-!
# The sizes and the layout's logarithms

* `stackOffsets_snd`: `stack_offsets`' log-size is `log2Ceil` of the blocks' total, whatever their
  order (the merge sort permutes the blocks).
* `stackLog_eq`, `logBytecode_eq`: the layout's stack log-size and bytecode log-size, for the
  guest's bytecode of `2^23` words.
* `pushDepth_eq`: the push side's bus cube is `log2Ceil` of the sum of `2^κ` over the guest's
  `54` push blocks (`BLOCK_KAPPA_SRC`, `BLOCK_KAPPA_ADJ`, G:126-127, 3351-3363).
* `readSizes_runsTo`: on the words `logMem`, the six row counts, `lir`, `readAnnouncedSizes` returns
  the layout `layoutOf` and `lir`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `stack_offsets` -/

theorem placed_snd (sz : ℕ → ℕ) : ∀ (l : List ℕ) (acc : List ℕ × ℕ),
    (l.foldl (fun (acc : List ℕ × ℕ) i ↦ (acc.1.set i acc.2, acc.2 + 2 ^ sz i)) acc).2 =
      acc.2 + (l.map fun i ↦ 2 ^ sz i).sum
  | [], acc => by simp
  | i :: l, acc => by
    rw [List.foldl_cons, placed_snd sz l, List.map_cons, List.sum_cons]
    simp only
    omega

theorem map_range_getD (sizes : List ℕ) (f : ℕ → ℕ) :
    (List.range sizes.length).map (fun i ↦ f (sizes.getD i 0)) = sizes.map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]

/-- **`stack_offsets`' log-size** is `log2Ceil` of the blocks' total. -/
theorem stackOffsets_snd (sizes : List ℕ) :
    (stackOffsets sizes).2 = log2Ceil ((sizes.map (2 ^ ·)).sum) := by
  unfold stackOffsets
  simp only
  rw [placed_snd, zero_add, ((List.mergeSort_perm _ _).map _).sum_eq,
    map_range_getD sizes (2 ^ ·)]

/-! ## The layout's logarithms -/

theorem log2_bytecode {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) :
    Nat.log2 bytecode.length - busBits = 19 := by
  rw [hbl, Nat.log2_two_pow]; rfl

theorem sz_placementsOf_snd (kappas : List ℕ) :
    (placementsOf kappas).2 = max 15 (log2Ceil (Tables.stackTotal kappas)) := by
  unfold placementsOf
  simp only []
  rw [stackOffsets_snd]
  simp only [Tables.stackTotal, Tables.committedKappas, Tables.committedCols, List.map_map]
  rfl

/-- **The bytecode's log-size**: `19` for the guest's `2^23` words. -/
theorem logBytecode_eq {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) (logMem : ℕ)
    (rowsN : List ℕ) : (Tables.layoutOf bytecode logMem rowsN).logBytecode = 19 := by
  unfold Tables.layoutOf
  simp only []
  exact log2_bytecode hbl

/-- **The stack's log-size**: at least `15`, else `log2Ceil` of the committed columns' total. -/
theorem stackLog_eq {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) (logMem : ℕ)
    (rowsN : List ℕ) : (Tables.layoutOf bytecode logMem rowsN).stackLog =
      max 15 (log2Ceil (Tables.stackTotal (columnKappas logMem 19 (Tables.tableHeightsOf rowsN)))) := by
  unfold Tables.layoutOf
  simp only []
  rw [sz_placementsOf_snd, log2_bytecode hbl]

/-! ## The push side's cube -/

/-- Push block `b`'s log-height (G:3352-3356, 3363): source `BLOCK_KAPPA_SRC[b]` of
`[0, log_mem, τ_0, …, τ_5]`, plus `BLOCK_KAPPA_ADJ[b]`. -/
def pushKappa (logMem : ℕ) (hs : List ℕ) (b : ℕ) : ℕ :=
  ([0, logMem] ++ hs).getD (Tables.blockKappaSrc.getD b 0) 0 + Tables.blockKappaAdj b

theorem tables_push_lengths :
    tables.map (fun t ↦ t.flushes.push.length) = [5, 5, 3, 5, 5, 28] := by decide +kernel

theorem busLayout_depth (fw : List ℕ) (blocks : List BusBlock) :
    (busLayout fw blocks).depth = log2Ceil (((fw ++ blocks.map (·.logRows)).map (2 ^ ·)).sum) := by
  unfold busLayout
  simp only []
  rw [stackOffsets_snd]

theorem layoutOf_push (bytecode : List K) (logMem : ℕ) (rowsN : List ℕ) :
    (Tables.layoutOf bytecode logMem rowsN).push =
      (busBlocks (Tables.tableHeightsOf rowsN) rowsN).1 := by
  unfold Tables.layoutOf
  simp only []

theorem push_logRows (h0 h1 h2 h3 h4 h5 r0 r1 r2 r3 r4 r5 : ℕ) :
    (busBlocks [h0, h1, h2, h3, h4, h5] [r0, r1, r2, r3, r4, r5]).1.map (·.logRows) =
      List.replicate 5 h0 ++ List.replicate 5 h1 ++ List.replicate 3 h2 ++ List.replicate 5 h3 ++
        List.replicate 5 h4 ++ List.replicate 28 h5 := by
  have hl := tables_push_lengths
  simp only [tables, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hl
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := hl
  simp only [busBlocks, tables, List.zip_cons_cons, List.zip_nil_right,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc, List.map_append]
  simp only [List.map_map, Function.comp_def, List.map_const', l0, l1, l2, l3, l4, l5]

theorem pushKappas_eq (logMem h0 h1 h2 h3 h4 h5 : ℕ) :
    (List.range 54).map (pushKappa logMem [h0, h1, h2, h3, h4, h5]) =
      [0, logMem, 19] ++ (List.replicate 5 h0 ++ List.replicate 5 h1 ++ List.replicate 3 h2 ++
        List.replicate 5 h3 ++ List.replicate 5 h4 ++ List.replicate 28 h5) := rfl

/-- **The push side's cube** (G:3176-3179): its log-size is `log2Ceil` of the sum of `2^κ` over
the guest's `54` push blocks. -/
theorem pushDepth_eq {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) (logMem : ℕ)
    (rowsN : List ℕ) (hlen : rowsN.length = 6) :
    (busLayout [0, logMem, (Tables.layoutOf bytecode logMem rowsN).logBytecode]
      (Tables.layoutOf bytecode logMem rowsN).push).depth =
      log2Ceil (((List.range 54).map fun b ↦
        2 ^ pushKappa logMem (Tables.tableHeightsOf rowsN) b).sum) := by
  rw [busLayout_depth, logBytecode_eq hbl, layoutOf_push,
    show (List.range 54).map (fun b ↦ 2 ^ pushKappa logMem (Tables.tableHeightsOf rowsN) b) =
      ((List.range 54).map (pushKappa logMem (Tables.tableHeightsOf rowsN))).map (2 ^ ·) from
      (List.map_map ..).symm]
  match rowsN, hlen with
  | [r0, r1, r2, r3, r4, r5], _ =>
    simp only [Tables.tableHeightsOf, tableLogFloors, List.zipWith_cons_cons, List.zipWith_nil_left]
    rw [push_logRows, pushKappas_eq]

/-! ## `readAnnouncedSizes` -/

theorem sz_runsTo_require_bind {β : Type} {c : Prop} [Decidable c] (h : c) {f : Unit →
    VerifierProgram β}
    {s s' : Fs} {xs : List E} {b : β} (hf : RunsTo (f ()) s xs b s') :
    RunsTo (VerifierProgram.require c >>= f) s xs b s' := by
  have hr : RunsTo (VerifierProgram.require c) s [] () s := by
    simp only [VerifierProgram.require, h, ↓reduceIte]
    exact runsTo_ret () s
  exact (hr.bind hf).of_eq rfl (List.nil_append _) rfl rfl

theorem sz_runsTo_liftOption_bind {α β : Type} {o : Option α} {a : α} (h : o = some a)
    {f : α → VerifierProgram β} {s s' : Fs} {xs : List E} {b : β} (hf : RunsTo (f a) s xs b s') :
    RunsTo (liftOption o >>= f) s xs b s' := by
  subst h
  exact ((runsTo_ret a s).bind hf).of_eq rfl (List.nil_append _) rfl rfl

theorem le_pow_of_log2Ceil {r k : ℕ} (h : log2Ceil r ≤ k) : r ≤ 2 ^ k := by
  unfold log2Ceil bitLength at h
  split at h
  · have := Nat.one_le_two_pow (n := k); omega
  · have h1 := Nat.lt_log2_self (n := r - 1)
    have h2 : 2 ^ ((r - 1).log2 + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega

theorem eOfNat_limb1 (n : ℕ) : (eOfNat n).limb 1 = 0 := by simp [eOfNat]

theorem kToNat_eOfNat {n : ℕ} (h : n < 2 ^ 64) : kToNat ((eOfNat n).limb 0) = n := by
  simp [eOfNat, kToNat_ofBits]
  omega

/-- `buildLayout` accepts the honest sizes, with the layout `layoutOf`. -/
theorem buildLayout_eq {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {logMem : ℕ}
    {rowsN : List ℕ} (h16 : 16 ≤ logMem) (h32 : logMem ≤ 32) (hlen : rowsN.length = 6)
    (hrows : ∀ r ∈ rowsN, r ≤ 2 ^ 32) :
    buildLayout bytecode logMem rowsN = some (Tables.layoutOf bytecode logMem rowsN) := by
  have hls : log2Strict bytecode.length = some 23 := by rw [hbl]; decide
  have hc : busBits ≤ 23 ∧ 16 ≤ logMem ∧ logMem ≤ 32 ∧ rowsN.all (· ≤ 2 ^ 32) ∧
      23 - busBits ≤ 32 ∧ rowsN.length = tables.length :=
    ⟨by decide, h16, h32, by simpa using hrows, by decide, by rw [hlen]; rfl⟩
  unfold buildLayout
  rw [hls]
  simp only [hc, and_self, ↓reduceIte]
  unfold Tables.layoutOf Tables.tableHeightsOf
  rw [hbl, Nat.log2_two_pow]

theorem rows_le {rowsN : List ℕ} (hlen : rowsN.length = 6)
    (hh : ∀ h ∈ Tables.tableHeightsOf rowsN, h < 29) : ∀ r ∈ rowsN, r ≤ 2 ^ 28 := by
  match rowsN, hlen with
  | [r0, r1, r2, r3, r4, r5], _ =>
    simp only [Tables.tableHeightsOf, tableLogFloors, List.zipWith_cons_cons,
      List.zipWith_nil_left, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hh
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hh
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact le_pow_of_log2Ceil (by omega)

/-- **`readAnnouncedSizes` on the honest words**: `logMem`, the six row counts and `lir` give the
layout
`layoutOf` and `lir`. -/
theorem readSizes_runsTo {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {logMem lir : ℕ}
    {rowsN : List ℕ} (h16 : 16 ≤ logMem) (h32 : logMem ≤ 32) (hlen : rowsN.length = 6)
    (hh : ∀ h ∈ Tables.tableHeightsOf rowsN, h < 29) (hl1 : 1 ≤ lir) (hl4 : lir ≤ 4)
    (hst : (Tables.layoutOf bytecode logMem rowsN).stackLog ≤ 28) (s : Fs) :
    RunsTo (readAnnouncedSizes bytecode) s (eOfNat logMem :: rowsN.map eOfNat ++ [eOfNat lir])
      (Tables.layoutOf bytecode logMem rowsN, lir)
      (s.absorbAll (eOfNat logMem :: rowsN.map eOfNat ++ [eOfNat lir]) dsObserve) := by
  have hrows := rows_le hlen hh
  set xs := eOfNat logMem :: rowsN.map eOfNat ++ [eOfNat lir] with hxs
  have hxl : xs.length = 2 + tables.length := by simp [xs, hlen]; rfl
  have r := runsTo_readN s xs
  rw [hxl] at r
  have e1 : kToNat ((xs.headD 0).limb 0) = logMem := kToNat_eOfNat (by omega)
  have e2 : ((xs.drop 1).take tables.length).map (fun v ↦ kToNat (v.limb 0)) = rowsN := by
    rw [hxs, List.cons_append, List.drop_succ_cons, List.drop_zero,
      List.take_left' (l₁ := List.map eOfNat rowsN) (by rw [List.length_map, hlen]; rfl),
      List.map_map]
    conv_rhs => rw [← List.map_id rowsN]
    refine List.map_congr_left fun r hr ↦ ?_
    have := hrows r hr
    exact kToNat_eOfNat (by
      calc r ≤ 2 ^ 28 := this
        _ < 2 ^ 64 := by norm_num)
  have e3 : kToNat ((xs.getLastD 0).limb 0) = lir := by
    rw [hxs, List.getLastD_eq_getLast?, List.getLast?_append, List.getLast?_singleton]
    exact kToNat_eOfNat (by omega)
  have hall : (xs.all fun value ↦ decide (value.limb 1 = 0)) = true := by
    simp [xs, eOfNat_limb1]
  unfold readAnnouncedSizes
  refine (r.bind ?_).of_eq rfl (List.append_nil _) rfl rfl
  simp only [e1, e2, e3]
  refine sz_runsTo_require_bind hall (sz_runsTo_require_bind ⟨hl1, hl4⟩
    (sz_runsTo_liftOption_bind (buildLayout_eq hbl h16 h32 hlen fun r hr ↦ ?_)
      (sz_runsTo_require_bind ⟨?_, hst⟩ (runsTo_ret _ _))))
  · exact (hrows r hr).trans (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  · rw [stackLog_eq hbl]; exact le_max_left _ _

end
end LeanVM.Guest.B1.VerifySub
