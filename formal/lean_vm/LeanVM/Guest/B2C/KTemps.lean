/-
  LeanVM.Guest.B2C.KTemps

  Checker K's facts about the temporaries' cells: within the frame past the header, distinct, and
  holding only their temporaries.
-/

module

public import LeanVM.Guest.B2C.KRetemp
public import LeanVM.Guest.B2C.KTemps.Big16
public import LeanVM.Guest.B2C.KTemps.Big17
public import LeanVM.Guest.B2C.KTemps.Part0
public import LeanVM.Guest.B2C.KTemps.Part1
public import LeanVM.Guest.B2C.KTemps.Part2
public import LeanVM.Guest.B2C.KTemps.Part3
public import LeanVM.Guest.B2C.KTemps.Part4
public import LeanVM.Guest.B2C.KTemps.Part5
public import LeanVM.Guest.B2C.KTemps.Part6

/-!
# The temporaries' cells

Every core function's temporaries pass `tmpCellsB` (`tmpsOk_all`: the kernel's ranges, and for
functions `16`, `17` their temporaries' indices `temps16`, `temps17`). So their certificate
cells lie in `[2, fs f)` (`kfacts_cert_lt`) and are distinct (`kfacts_cert_inj`), and since a
frame's candidates start with its temporaries' and `dedupC` keeps the first at each cell, a
temporary's cell holds only it (`kfacts_tmp`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **Every core function's temporaries pass the check.** -/
theorem tmpsOk_all {i : ℕ} (hi : i < coreProgram.length) : TmpsOk i := by
  rw [coreProgram_length] at hi
  by_cases h0 : i < 12
  · exact tmpsRange_0.ok (by omega) (by omega)
  by_cases h1 : i < 15
  · exact tmpsRange_12.ok (by omega) (by omega)
  by_cases h2 : i < 16
  · exact tmpsRange_15.ok (by omega) (by omega)
  by_cases h3 : i = 16
  · subst h3; exact tmpsOk_16
  by_cases h4 : i = 17
  · subst h4; exact tmpsOk_17
  by_cases h5 : i < 58
  · exact tmpsRange_18.ok (by omega) (by omega)
  by_cases h6 : i < 70
  · exact tmpsRange_58.ok (by omega) (by omega)
  by_cases h7 : i < 110
  · exact tmpsRange_70.ok (by omega) (by omega)
  by_cases h8 : i < 150
  · exact tmpsRange_110.ok (by omega) (by omega)
  by_cases h9 : i < 178
  · exact tmpsRange_150.ok (by omega) (by omega)
  by_cases h10 : i < 182
  · exact tmpsRange_178.ok (by omega) (by omega)
  by_cases h11 : i < 186
  · exact tmpsRange_182.ok (by omega) (by omega)
  by_cases h12 : i < 190
  · exact tmpsRange_186.ok (by omega) (by omega)
  by_cases h13 : i < 194
  · exact tmpsRange_190.ok (by omega) (by omega)
  by_cases h14 : i < 198
  · exact tmpsRange_194.ok (by omega) (by omega)
  by_cases h15 : i < 203
  · exact tmpsRange_198.ok (by omega) (by omega)
  by_cases h16 : i < 243
  · exact tmpsRange_203.ok (by omega) (by omega)
  by_cases h17 : i < 283
  · exact tmpsRange_243.ok (by omega) (by omega)
  by_cases h18 : i < 310
  · exact tmpsRange_283.ok (by omega) (by omega)
  by_cases h19 : i < 350
  · exact tmpsRange_310.ok (by omega) (by omega)
  by_cases h20 : i < 390
  · exact tmpsRange_350.ok (by omega) (by omega)
  by_cases h21 : i < 430
  · exact tmpsRange_390.ok (by omega) (by omega)
  by_cases h22 : i < 460
  · exact tmpsRange_430.ok (by omega) (by omega)
  by_cases h23 : i < 500
  · exact tmpsRange_460.ok (by omega) (by omega)
  by_cases h24 : i < 519
  · exact tmpsRange_500.ok (by omega) (by omega)
  by_cases h25 : i < 548
  · exact tmpsRange_519.ok (by omega) (by omega)
  by_cases h26 : i < 572
  · exact tmpsRange_548.ok (by omega) (by omega)
  by_cases h27 : i < 612
  · exact tmpsRange_572.ok (by omega) (by omega)
  by_cases h28 : i < 652
  · exact tmpsRange_612.ok (by omega) (by omega)
  by_cases h29 : i < 688
  · exact tmpsRange_652.ok (by omega) (by omega)
  by_cases h30 : i < 728
  · exact tmpsRange_688.ok (by omega) (by omega)
  by_cases h31 : i < 768
  · exact tmpsRange_728.ok (by omega) (by omega)
  by_cases h32 : i < 808
  · exact tmpsRange_768.ok (by omega) (by omega)
  by_cases h33 : i < 838
  · exact tmpsRange_808.ok (by omega) (by omega)
  by_cases h34 : i < 878
  · exact tmpsRange_838.ok (by omega) (by omega)
  by_cases h35 : i < 918
  · exact tmpsRange_878.ok (by omega) (by omega)
  by_cases h36 : i < 958
  · exact tmpsRange_918.ok (by omega) (by omega)
  by_cases h37 : i < 977
  · exact tmpsRange_958.ok (by omega) (by omega)
  by_cases h38 : i < 992
  · exact tmpsRange_977.ok (by omega) (by omega)
  by_cases h39 : i < 1009
  · exact tmpsRange_992.ok (by omega) (by omega)
  by_cases h40 : i < 1024
  · exact tmpsRange_1009.ok (by omega) (by omega)
  by_cases h41 : i < 1038
  · exact tmpsRange_1024.ok (by omega) (by omega)
  by_cases h42 : i < 1043
  · exact tmpsRange_1038.ok (by omega) (by omega)
  omega

/-- What the check gives: the temporaries index the cells, within the frame past the header, and
distinct temporaries have distinct cells. -/
theorem tmpsOk_spec {i : ℕ} (h : TmpsOk i) :
    (∀ t ∈ Stmt.tmpsList (coreOf (i + 1)).body, ∃ ht : t.idx < (certOf (i + 1)).locs.length,
      2 ≤ (certOf (i + 1)).locs[t.idx] ∧ (certOf (i + 1)).locs[t.idx] < fsN (i + 1)) ∧
    ∀ t ∈ Stmt.tmpsList (coreOf (i + 1)).body, ∀ t' ∈ Stmt.tmpsList (coreOf (i + 1)).body,
      (certOf (i + 1)).locs.getD t.idx 0 = (certOf (i + 1)).locs.getD t'.idx 0 → t = t' := by
  unfold TmpsOk tmpCellsB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  set tm := Stmt.tmpsList (coreOf (i + 1)).body
  set L := (certOf (i + 1)).locs
  have hnd : (tm.map V.idx).Nodup := (List.Nodup.of_map V.n (idxNodup_spec h1).1)
  have hbit : ∀ t ∈ tm, (idxMask ((tm.map V.idx).map V.n)).testBit (0 + t.idx) = true := by
    intro t ht
    rw [Nat.zero_add]
    exact testBit_idxMask (v := V.n t.idx) (List.mem_map_of_mem (List.mem_map_of_mem ht))
  refine ⟨fun t ht ↦ ?_, fun t ht t' ht' he ↦ ?_⟩
  · obtain ⟨hx, g1, g2, -, -⟩ := tmpScan_spec h2 t.idx (hbit t ht)
    exact ⟨hx, g1, g2⟩
  · obtain ⟨hx, -, -, -, g4⟩ := tmpScan_spec h2 t.idx (hbit t ht)
    obtain ⟨hx', -, -, -, -⟩ := tmpScan_spec h2 t'.idx (hbit t' ht')
    rw [List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hx'] at he
    exact List.inj_on_of_nodup_map hnd ht ht' (g4 t'.idx hx' (hbit t' ht') he.symm).symm

private theorem temps_none {f : String} (h : idxOf f = none) : coreProgram.temps f = [] := by
  unfold idxOf at h
  rw [Option.map_eq_none_iff] at h
  rw [Program.temps, find?_none h]

private theorem temps_some {f : String} {j : ℕ} (h : idxOf f = some j) :
    ∃ i, j = i + 1 ∧ i < coreProgram.length ∧ coreProgram.temps f = Stmt.tmpsList (coreOf j).body ∧
      fs f = fsN j ∧ ∀ v, cert f v = (certOf j).locs.getD v.idx 0 := by
  obtain ⟨i, rfl, hi, -, hfind, hcore, hfs, hcert, -, -⟩ := fn_of_idx h
  exact ⟨i, rfl, hi, by rw [Program.temps, hfind, hcore], hfs, hcert⟩

/-- **The temporaries' cells lie in the frame past the header.** -/
theorem kfacts_cert_lt : ∀ f, ∀ t ∈ coreProgram.temps f, 2 ≤ cert f t ∧ cert f t < fs f := by
  intro f t ht
  cases hj : idxOf f with
  | none => rw [temps_none hj] at ht; cases ht
  | some j =>
    obtain ⟨i, rfl, hi, htm, hfs, hcert⟩ := temps_some hj
    rw [htm] at ht
    obtain ⟨hx, g1, g2⟩ := (tmpsOk_spec (tmpsOk_all hi)).1 t ht
    rw [hcert, hfs, List.getD_eq_getElem _ _ hx]
    exact ⟨g1, g2⟩

/-- **Distinct temporaries have distinct cells.** -/
theorem kfacts_cert_inj : ∀ f, ∀ t ∈ coreProgram.temps f, ∀ t' ∈ coreProgram.temps f,
    cert f t = cert f t' → t = t' := by
  intro f t ht t' ht' he
  cases hj : idxOf f with
  | none => rw [temps_none hj] at ht; cases ht
  | some j =>
    obtain ⟨i, rfl, hi, htm, -, hcert⟩ := temps_some hj
    rw [htm] at ht ht'
    rw [hcert, hcert] at he
    exact (tmpsOk_spec (tmpsOk_all hi)).2 t ht t' ht' he

/-- **A temporary's cell holds only it**, in every instance of a re-chosen tree. -/
theorem kfacts_tmp (hdr : E × E) (T : Tree) :
    ∀ ν, ∀ I' ∈ honestInsts coreProgram fs H hdr (T.retemp coreProgram fs ν 0), ∀ f σ bufs kids,
      I'.t = .node f σ bufs kids → ∀ t ∈ coreProgram.temps f, ∀ q ∈ C I', q.1 = cert f t →
        q.2 = σ t := by
  intro ν I' _ f σ bufs kids ht t htm q hq hqt
  cases hj : idxOf f with
  | none => rw [temps_none hj] at htm; cases htm
  | some j =>
    rw [C_node ht hj, nodeE_split, frameE_append] at hq
    have hlt := kfacts_cert_lt f t htm
    have hmem := dedupC_first hq ⟨(cert f t, σ t), List.mem_filter.mpr
      ⟨List.mem_map_of_mem (f := fun v => (cert f v, σ v)) htm, by
        simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]; exact hlt⟩, hqt.symm⟩
    obtain ⟨hq1, -⟩ := List.mem_filter.mp hmem
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hq1
    obtain rfl := kfacts_cert_inj f t' ht' t htm hqt
    rfl

end
end LeanVM.Guest.B2C
