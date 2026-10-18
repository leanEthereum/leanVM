/-
  LeanVM.Guest.B1.VerifySub.Layout

  The layout's sizes as `verify_sub` computes them: the bus depth and the stack's log from sums
  of block sizes.
-/

module

public import LeanVM.Guest.B1.VerifySub.Run

/-!
# The layout's sizes

* `stackOffsets_snd`: `stack_offsets` rounds the total of its blocks, in any order;
* `pushDepth_eq`: the push side's depth is `log2Ceil` of `Σ 2^κ` over `[0, log_mem, 18]` and
  the tables' push blocks, the list `verify_sub`'s `block_kappa[0..37]` holds (`pushKappas`);
* `stackLog_eq`: the stack's log is `max 15 (log2Ceil (stackTotal …))`;
* `le_two_pow_log2Ceil`, `log2Ceil_ge`: the bounds of `log2Ceil`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `log2Ceil` -/

theorem le_two_pow_log2Ceil (n : ℕ) : n ≤ 2 ^ log2Ceil n := by
  unfold log2Ceil bitLength
  split
  · omega
  · have := Nat.lt_log2_self (n := n - 1)
    rw [pow_succ] at this ⊢
    omega

theorem log2Ceil_ge {n k : ℕ} (h : 2 ^ k < n) : k + 1 ≤ log2Ceil n := by
  have h1 := Nat.one_le_two_pow (n := k)
  unfold log2Ceil bitLength
  split
  · omega
  · have : k ≤ Nat.log2 (n - 1) := (Nat.le_log2 (by omega)).mpr (by omega)
    omega

/-! ## `stack_offsets` -/

theorem foldl_place_snd (w : ℕ → ℕ) :
    ∀ (l : List ℕ) (acc : List ℕ × ℕ),
      (l.foldl (fun (acc : List ℕ × ℕ) i ↦ (acc.1.set i acc.2, acc.2 + w i)) acc).2 =
        acc.2 + (l.map w).sum
  | [], acc => by simp
  | i :: l, acc => by
    rw [List.foldl_cons, foldl_place_snd w l, List.map_cons, List.sum_cons]
    simp only
    omega

theorem map_getD_range (sizes : List ℕ) (f : ℕ → ℕ) :
    (List.range sizes.length).map (fun i ↦ f (sizes.getD i 0)) = sizes.map f := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h2)]

theorem stackOffsets_snd (sizes : List ℕ) :
    (stackOffsets sizes).2 = log2Ceil ((sizes.map (2 ^ ·)).sum) := by
  unfold stackOffsets
  simp only
  rw [foldl_place_snd, zero_add,
    ((List.mergeSort_perm (List.range sizes.length) _).map _).sum_eq, map_getD_range]

theorem busLayout_depth (fw : List ℕ) (blocks : List BusBlock) :
    (busLayout fw blocks).depth = log2Ceil (((fw ++ blocks.map (·.logRows)).map (2 ^ ·)).sum) := by
  rw [← stackOffsets_snd]
  rfl

theorem placementsOf_snd (kappas : List ℕ) :
    (placementsOf kappas).2 = max minStackedLog (log2Ceil (stackTotal kappas)) := by
  unfold placementsOf
  simp only
  rw [stackOffsets_snd, stackTotal, blockCols, List.map_map]
  rfl

/-! ## The push side -/

theorem tables_push_counts : tables.map (·.flushes.push.length) = [5, 5, 3, 5, 5, 11] := by
  decide +kernel

theorem push_logRows (ts : List Table) :
    ∀ (hs ns : List ℕ), hs.length = ts.length → ns.length = ts.length →
      ((List.zip ts (List.zip hs ns)).flatMap fun (x : Table × ℕ × ℕ) ↦
          x.1.flushes.push.map fun c ↦ (⟨x.2.1, x.2.2, c, x.1.opcode⟩ : BusBlock)).map (·.logRows) =
        (List.zip (ts.map (·.flushes.push.length)) hs).flatMap fun x ↦ List.replicate x.1 x.2 := by
  induction ts with
  | nil => intro hs ns _ _; rfl
  | cons t ts ih =>
    intro hs ns h1 h2
    match hs, ns, h1, h2 with
    | h :: hs, n :: ns, h1, h2 =>
      simp only [List.zip_cons_cons, List.flatMap_cons, List.map_append, List.map_map,
        List.map_cons]
      rw [ih hs ns (by simpa using h1) (by simpa using h2)]
      congr 1
      simp [Function.comp_def, List.map_const']

/-- The kappas of the push side's blocks, in `verify_sub`'s block order (`block_kappa[0..37]`). -/
def pushKappas (m : ℕ) (hs : List ℕ) : List ℕ :=
  [0, m, 18] ++ (List.zip [5, 5, 3, 5, 5, 11] hs).flatMap fun x ↦ List.replicate x.1 x.2

theorem pushDepth_eq {bytecode : List K} (hb : bytecode.length = 2 ^ 22) (m : ℕ)
    (rows : List ℕ) (hr : rows.length = 6) :
    pushDepth (layoutOf bytecode m rows) =
      log2Ceil (((pushKappas m (rows.map log2Ceil)).map (2 ^ ·)).sum) := by
  have hlog : Nat.log2 bytecode.length = 22 := by rw [hb, Nat.log2_two_pow]
  unfold pushDepth
  rw [busLayout_depth]
  unfold layoutOf busBlocks
  simp only [hlog]
  rw [push_logRows tables _ _ (by simp [hr]; rfl) (by rw [hr]; rfl), tables_push_counts]
  rfl

/-- The push kappas from the bus's base `[0, log_mem, h_0, …, h_5]`, as `block_kappa` derives
them. -/
theorem pushKappas_eq (m : ℕ) (hs : List ℕ) (hl : hs.length = 6) :
    pushKappas m hs = (List.range 37).map fun b ↦
      (0 :: m :: hs).getD (blockKappaSrc.getD b 0) 0 + blockKappaAdj.getD b 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, rfl⟩ : ∃ h0 h1 h2 h3 h4 h5, hs = [h0, h1, h2, h3, h4, h5] := by
    match hs, hl with
    | [h0, h1, h2, h3, h4, h5], _ => exact ⟨h0, h1, h2, h3, h4, h5, rfl⟩
  simp [pushKappas, blockKappaSrc, blockKappaAdj, List.range_succ]

theorem stackLog_eq {bytecode : List K} (hb : bytecode.length = 2 ^ 22) (m : ℕ) (rows : List ℕ) :
    (layoutOf bytecode m rows).stackLog =
      max minStackedLog (log2Ceil (stackTotal (columnKappas m 18 (rows.map log2Ceil)))) := by
  have hlog : Nat.log2 bytecode.length = 22 := by rw [hb, Nat.log2_two_pow]
  unfold layoutOf
  simp only [hlog]
  rw [← placementsOf_snd]
  rfl

/-! ## The stack's total is small -/

theorem stackTotal_le (kappas : List ℕ) (B : ℕ) (h : ∀ x ∈ kappas, x ≤ B) :
    stackTotal kappas ≤ kappas.length * 2 ^ B := by
  unfold stackTotal blockCols
  have hb : ∀ y ∈ ((List.range kappas.length).filter fun c ↦ (limbSlot c).isNone).map
      (fun c ↦ 2 ^ kappas.getD c 0), y ≤ 2 ^ B := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
    have hc' : c < kappas.length := List.mem_range.mp (List.mem_filter.mp hc).1
    exact Nat.pow_le_pow_right (by decide) (h _ (by rw [List.getD_eq_getElem _ _ hc']; simp))
  have := List.sum_le_length_nsmul _ _ hb
  simp only [List.length_map, smul_eq_mul] at this
  have hl := List.length_filter_le (fun c ↦ (limbSlot c).isNone) (List.range kappas.length)
  rw [List.length_range] at hl
  exact le_trans this (Nat.mul_le_mul_right _ hl)

theorem tables_width_sum : (tables.map fun t ↦ t.columns.length).sum ≤ 120 := by decide +kernel

theorem columnKappas_length (m lb : ℕ) (hs : List ℕ) :
    (columnKappas m lb hs).length = 6 + (tables.map fun t ↦ t.columns.length).sum := by
  simp only [columnKappas, List.length_append, List.length_cons, List.length_nil,
    List.length_flatMap, List.length_replicate, Table.width]

theorem columnKappas_le (m : ℕ) (hs : List ℕ) (hm : m ≤ 32) (hh : ∀ h ∈ hs, h < 29) :
    ∀ x ∈ columnKappas m 18 hs, x ≤ 40 := by
  have hg : ∀ i, hs.getD i 0 < 29 := fun i => by
    rw [List.getD_eq_getElem?_getD]
    cases e : hs[i]? with
    | none => simp
    | some v => simpa using hh v (List.mem_of_getElem? e)
  have hq : qflockSlotBits = 8 := by decide
  intro x hx
  unfold columnKappas at hx
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    have := hg opBlake2s
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · obtain ⟨t, -, ht⟩ := List.mem_flatMap.mp hx
    rw [(List.mem_replicate.mp ht).2]
    have := hg t.opcode
    omega

theorem stackTotal_lt (m : ℕ) (hs : List ℕ) (hm : m ≤ 32) (hh : ∀ h ∈ hs, h < 29) :
    stackTotal (columnKappas m 18 hs) < 2 ^ 64 - 1 := by
  have h1 := stackTotal_le _ 40 (columnKappas_le m hs hm hh)
  rw [columnKappas_length] at h1
  have h2 := tables_width_sum
  have : (6 + (tables.map fun t ↦ t.columns.length).sum) * 2 ^ 40 ≤ 126 * 2 ^ 40 := Nat.mul_le_mul_right _ (by omega)
  omega

end
end LeanVM.Guest.B1.VerifySub
