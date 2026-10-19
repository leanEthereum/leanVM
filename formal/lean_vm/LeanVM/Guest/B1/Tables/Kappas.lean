/-
  LeanVM.Guest.B1.Tables.Kappas

  What `certify_placement` hands `check_opening_terminal` (`PCtx`), its soundness in
  `verify_sub`'s shape (`soundPlace`), and the bound on the committed columns' log sizes that the
  terminal's 92 column selector dispatches rest on (`hypKappa`).
-/

module

public import LeanVM.Guest.B1.Tables.Placement
public import LeanVM.Guest.B1.VerifySub.Interface
public import LeanVM.Guest.B1.VerifySub.Layout
public import LeanVM.Guest.B1.VerifySub.CompleteIface

/-!
# The placement's context and every column's `κ` below 29

`certify_placement` lays out the 92 committed columns, `blockCols 110` in global order, at the
offsets `stackOffsets` gives their sizes `committedKappas kappas` (V:906-916); `PCtx` says its
two output buffers hold `g^κ` and `g^offset` per committed column. The guest's sources
(`cpSrc`, `cpAdj`) over the base `[0, log_mem, h_0, …, h_5]` are exactly
`committedKappas (columnKappas log_mem 18 h)` (`committedKappas_columnKappas`).

`check_opening_terminal` (G:2034-2037) dispatches each committed column's selector on its `κ`
over the 29 arms of `column_selector` without a range check of its own. `verify_sub` (G:2232-2240)
derives the stack's log `m = max 15 (log2Ceil (stackTotal kappas))` from the placement's total
and range-checks `m - 22 < 7`, so `m ≤ 28`; every `κ_c` is at most `log2Ceil (stackTotal kappas)`
since `2^κ_c` is one of its summands (`hypKappa`). That is the precondition the B2 checker gives
the terminal's dispatch sites.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-! ## The committed columns -/

/-- The committed columns' sizes, in compact order (`blockCols`, V:906-907). -/
def committedKappas (kappas : List ℕ) : List ℕ := (blockCols kappas.length).map (kappas.getD · 0)

/-- **What `certify_placement` hands `check_opening_terminal`**: `kappas` are the 110 columns'
sizes, `kap` holds `g^κ` and `off` holds `g^offset` per committed column, the offsets
`stackOffsets`'s (V:908-909). -/
def PCtx (rd : Reader) (kappas : List ℕ) (off kap : E) : Prop :=
  kappas.length = 110 ∧ ReadsAt rd kap ((committedKappas kappas).map (gen ^ ·)) ∧
    ReadsAt rd off ((stackOffsets (committedKappas kappas)).1.map (gen ^ ·))

/-- The committed columns: all but `BLAKE2S`'s 18 value limbs, global columns `82 .. 99`. -/
theorem blockCols_110 : blockCols 110 = List.range 82 ++ (List.range 10).map (· + 100) := by
  decide +kernel

theorem blockCols_110_length : (blockCols 110).length = 92 := by
  rw [blockCols_110]; simp

theorem columnKappas_length_110 (lm lb : ℕ) (hs : List ℕ) :
    (columnKappas lm lb hs).length = 110 := by
  rw [columnKappas_length]; decide +kernel

theorem committedKappas_length (kappas : List ℕ) (h : kappas.length = 110) :
    (committedKappas kappas).length = 92 := by
  rw [committedKappas, List.length_map, h, blockCols_110_length]

theorem stackTotal_eq (kappas : List ℕ) :
    stackTotal kappas = ((committedKappas kappas).map (2 ^ ·)).sum := by
  rw [stackTotal, committedKappas, List.map_map]; rfl

theorem tables_shape :
    tables.map (fun t ↦ (t.width, t.opcode)) =
      [(15, 0), (15, 1), (8, 2), (15, 3), (14, 4), (37, 5)] := by
  decide +kernel

theorem columnKappas_eq (lm lb h0 h1 h2 h3 h4 h5 : ℕ) :
    columnKappas lm lb [h0, h1, h2, h3, h4, h5] = [lm, lm, lm, lm, lb, h5 + 8] ++
      List.replicate 15 h0 ++ List.replicate 15 h1 ++ List.replicate 8 h2 ++
      List.replicate 15 h3 ++ List.replicate 14 h4 ++ List.replicate 37 h5 := by
  have e : ∀ hs : List ℕ, tables.flatMap (fun t ↦ List.replicate t.width (hs.getD t.opcode 0)) =
      (tables.map fun t ↦ (t.width, t.opcode)).flatMap
        (fun p ↦ List.replicate p.1 (hs.getD p.2 0)) := fun hs => by
    rw [List.flatMap_map]
  unfold columnKappas
  rw [e, tables_shape]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
    List.nil_append, List.append_assoc]
  rfl

/-- **The guest's sizes are the specification's**: column `c`'s source and adjustment over the
base `[0, log_mem, h_0, …, h_5]` give `committedKappas (columnKappas log_mem 18 h)`. -/
theorem committedKappas_columnKappas (lm : ℕ) (hs : List ℕ) (hl : hs.length = 6) :
    committedKappas (columnKappas lm 18 hs) =
      (List.range 92).map fun c ↦ (0 :: lm :: hs).getD (cpSrc c) 0 + cpAdj c := by
  obtain ⟨h0, h1, h2, h3, h4, h5, rfl⟩ : ∃ h0 h1 h2 h3 h4 h5, hs = [h0, h1, h2, h3, h4, h5] := by
    match hs, hl with
    | [h0, h1, h2, h3, h4, h5], _ => exact ⟨h0, h1, h2, h3, h4, h5, rfl⟩
  rw [committedKappas, columnKappas_length_110, blockCols_110, columnKappas_eq]
  rfl

/-! ## Every column's `κ` is below 29 -/

theorem le_log2Ceil_of_two_pow_le {k N : ℕ} (h : 2 ^ k ≤ N) : k ≤ log2Ceil N := by
  by_contra hlt
  have h1 := log2Ceil_le_iff.mp (show log2Ceil N ≤ k - 1 by omega)
  have : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by decide) (by omega)
  omega

theorem single_le_sum_map (l : List ℕ) (c : ℕ) (hc : c < l.length) :
    2 ^ l.getD c 0 ≤ (l.map (2 ^ ·)).sum := by
  rw [List.getD_eq_getElem _ _ hc]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨_, List.getElem_mem hc, rfl⟩)

/-- **Every committed column's `κ` is below 29** once the stack is at most `2^28`
(`HypKappa`, the control-flow obligation of `check_opening_terminal`'s dispatches). -/
theorem hypKappa (rd : Reader) : HypKappa PCtx rd := by
  rintro kappas off kap ⟨hl, hkap, -⟩ h28 c hc
  have hcl : c < (committedKappas kappas).length := by
    rw [committedKappas_length _ hl]; exact hc
  refine ⟨(committedKappas kappas).getD c 0, ?_, readsAt_map_iff.mp hkap c hcl⟩
  have := le_log2Ceil_of_two_pow_le (stackTotal_eq kappas ▸ single_le_sum_map _ c hcl)
  omega

/-! ## `certify_placement` in `verify_sub`'s shape -/

/-- The guest's sizes from `kappa_base`: over `[1, g^log_mem, g^h_0, …, g^h_5]`, sizes below 34
built as `kappa_base[src]·g^adj` are `committedKappas (columnKappas log_mem 18 h)`. -/
theorem kappas_of_base {rd : Reader} {kb : E} {lm : ℕ} {hs κs : List ℕ} (hlm : lm ≤ 32)
    (hl : hs.length = 6) (hh : ∀ h ∈ hs, h < 29)
    (hkb : ReadsAt rd kb (1 :: gen ^ lm :: hs.map (gen ^ ·))) (hlen : κs.length = 92)
    (hκ : ∀ c < 92, κs.getD c 0 < 34 ∧
      ∃ w, LoadHolds rd kb (cpSrc c) w ∧ w * gen ^ cpAdj c = gen ^ κs.getD c 0) :
    κs = committedKappas (columnKappas lm 18 hs) := by
  have hbase : ∀ s < 8, LoadHolds rd kb s (gen ^ (0 :: lm :: hs).getD s 0) := fun s hs8 => by
    have := hkb s (by simp [hl]; omega)
    rcases s with _ | _ | s
    · simpa using this
    · simpa using this
    · simp only [List.getElem_cons_succ, List.getElem_map] at this
      simp only [List.getD_cons_succ]
      rwa [List.getD_eq_getElem _ _ (by omega)]
  have hb32 : ∀ s < 8, (0 :: lm :: hs).getD s 0 ≤ 32 := fun s hs8 => by
    rcases s with _ | _ | s
    · simp
    · simpa using hlm
    · simp only [List.getD_cons_succ]
      rw [List.getD_eq_getElem _ _ (by omega)]
      have := hh _ (List.getElem_mem (show s < hs.length by omega))
      omega
  have hsrc : ∀ c, cpSrc c < 8 := fun c => by unfold cpSrc; split_ifs <;> omega
  have hadj : ∀ c, cpAdj c ≤ 18 := fun c => by unfold cpAdj; split_ifs <;> omega
  rw [committedKappas_columnKappas lm hs hl]
  refine List.ext_getElem (by simp [hlen]) fun c h1 h2 => ?_
  have hc : c < 92 := by omega
  obtain ⟨hlt, w, lw, ew⟩ := hκ c hc
  rw [loadHolds_unique lw (hbase _ (hsrc c)), ← pow_add] at ew
  have := gen_pow_inj' (by have := hb32 _ (hsrc c); have := hadj c; omega) (by omega) ew
  rw [List.getElem_map, List.getElem_range, this, List.getD_eq_getElem _ _ h1]

/-- **`certify_placement` is sound** (`SoundPlace`) on any memory image of at most `2^32`
words. -/
theorem soundPlace {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemImage μ) : SoundPlace PCtx Lm.read := by
  intro lp sq kb lm hs rets hexp hlm hl hh hkb h
  have hsq : ∀ j < 34, LoadHolds Lm.read sq j (gen ^ 2 ^ j) := fun j hj => (hexp j hj).2
  have hm := cp_sound hμ Lm hsq _ h
  obtain ⟨gT, offs, kaps, rfl⟩ : ∃ gT offs kaps, rets = [gT, offs, kaps] := by
    match rets, hm with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
    | [], hm | [_], hm | [_, _], hm | _ :: _ :: _ :: _ :: _, hm => exact hm.elim
  obtain ⟨κs, hlen, hκ, -, hkaps, hoffs, hgT⟩ := hm
  obtain rfl := kappas_of_base hlm hl hh hkb hlen hκ
  refine ⟨offs, kaps, ?_, columnKappas_length_110 _ _ _, hkaps, hoffs⟩
  rw [hgT, stackTotal_eq]

/-! ## Completeness -/

/-- **`certify_placement`'s honest memory**: `col_sort_order` at `p99` holds `stackOffsets`'s
order of the sizes `κs` that `kappa_base` gives, and the returned buffers their logs and
offsets. -/
def PMem (rd : Reader) : List E → List E → List E → Prop
  | [p99], [kb, _], [_, off, kap] => ∃ κs : List ℕ, κs.length = 92 ∧
      (∀ c < 92, κs.getD c 0 < 34 ∧
        ∃ w, LoadHolds rd kb (cpSrc c) w ∧ w * gen ^ cpAdj c = gen ^ κs.getD c 0) ∧
      ReadsAt rd p99 ((stackOrder κs).map (gen ^ ·)) ∧ ReadsAt rd kap (κs.map (gen ^ ·)) ∧
      ReadsAt rd off ((stackOffsets κs).1.map (gen ^ ·))
  | _, _, _ => False

/-- **`certify_placement` is complete** (`CompletePlace`) on a memory image of `2^μ` words,
`7 ≤ μ ≤ 32`. -/
theorem completePlace {μ : ℕ} (hμ7 : 7 ≤ μ) (hμ : μ ≤ 32) (Lm : MemImage μ) :
    CompletePlace Lm.read PMem := by
  intro ptrs lp sq kb lm hs off kap hexp hlm hl hh hkb hm
  match ptrs, hm with
  | [], hm => exact hm.elim
  | _ :: _ :: _, hm => exact hm.elim
  | [p99], hm =>
  obtain ⟨κs, hlen, hκ, h99, h2, h100⟩ := hm
  have e := kappas_of_base hlm hl hh hkb hlen hκ
  have h := cp_complete hμ7 hμ Lm (fun j hj => (hexp j hj).2) κs hlen hκ kap p99 off h99 h2 h100
  rwa [e, ← stackTotal_eq] at h

/-- Over `certify_placement`'s honest memory, the terminal's context holds (`HypPCtx`). -/
theorem hypPCtx (rd : Reader) : HypPCtx PCtx rd PMem := by
  intro ptrs lp sq kb lm hs off kap hexp hlm hl hh hkb hm
  match ptrs, hm with
  | [], hm => exact hm.elim
  | _ :: _ :: _, hm => exact hm.elim
  | [p99], hm =>
  obtain ⟨κs, hlen, hκ, -, h2, h100⟩ := hm
  obtain rfl := kappas_of_base hlm hl hh hkb hlen hκ
  exact ⟨columnKappas_length_110 _ _ _, h2, h100⟩

end
end LeanVM.Guest.B1
