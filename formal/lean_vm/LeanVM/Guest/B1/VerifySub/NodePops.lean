/-
  LeanVM.Guest.B1.VerifySub.NodePops

  The witness-stream entries a valid call instance of `verify_sub`, `certify_placement` or `verify_tables` pops: its own hints' words, its noisy callees' entries spliced in.
-/

module

public import LeanVM.Guest.B1.VerifySub.NodeShapes
public import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«certify_placement»
import LeanVM.Guest.Data.ValNames.«verify_sub»
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# The nodes' pops

* `cp_pops`: `certify_placement` pops its group order's buffer (`col_group_order`);
* `vt_pops`: `verify_tables` pops its block group order's buffer (`block_group_order`), then its round count (`zc_tau_max`);
* `vs_pops`: `verify_sub` pops its stream's buffer (`stream`) and `dims_g`'s heights (`table_logs`), then its `certify_placement`'s, `verify_tables`' and `open_stacked`'s entries; every other callee pops nothing (`noWitS_mute`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1

@[expose] public section

theorem find_cp : coreProgram.find? name% «certify_placement» = some fn% «certify_placement» :=
  coreProgram_find?_at (j := idx% «certify_placement») rfl

theorem find_vt : coreProgram.find? name% «verify_tables» = some fn% «verify_tables» :=
  coreProgram_find?_at (j := idx% «verify_tables») rfl

theorem find_vsub : coreProgram.find? name% «verify_sub» = some fn% «verify_sub» :=
  coreProgram_find?_at (j := idx% «verify_sub») rfl

variable {rd : Reader} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} {args rets : List E}

theorem segOk_parts {j : ℕ} {l : List Stmt} {a n : ℕ} (h : segOk j l a n = true) :
    (Stmt.noRetList ((l.drop a).take n) && Stmt.muteList noWitS ((l.drop a).take n)) = true := by
  simp only [segOk, Bool.and_eq_true] at h ⊢
  exact ⟨h.1, noWitBlock_mute h.2⟩

/-- `certify_placement`'s entry: its group order's buffer. -/
def cpPop (rd : Reader) (σ : Val) : Pop := ("col_group_order", (Dest.heap (.n (val% «certify_placement» "group_order")) 0 9).words rd σ)

/-- **`certify_placement` pops its group order's buffer.** -/
theorem cp_pops (hv : (Memory.Tree.node "certify_placement" σ bufs kids).Valid coreProgram rd args rets) :
    (Memory.Tree.node "certify_placement" σ bufs kids).pops coreProgram rd = [cpPop rd σ] := by
  have h := cpShape_ok
  simp only [cpShapeOk, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h0 := Memory.Tree.retKids hv find_cp
  rw [← List.drop_zero (l := Fn.body _)] at h0
  obtain ⟨k1, h0, -⟩ := h0.dropMute noWitS_mute (segOk_parts h1)
  obtain ⟨k2, p2, h0, e, -⟩ := h0.dropAtom (a := 135) (stmtAt_sound h2)
  rw [e, h0.endMute noWitS_mute (noWitBlock_mute h3)]
  rfl

/-- `verify_tables`' entries: its block group order's buffer, its round count. -/
def vtPops (rd : Reader) (σ : Val) : List Pop :=
  [("block_group_order", (Dest.heap (.n (val% «verify_tables» "group_order")) 0 24).words rd σ), ("zc_tau_max", [σ (.n (val% «verify_tables» "g_zc_n"))])]

/-- **`verify_tables` pops its block group order's buffer, then its round count.** -/
theorem vt_pops (hv : (Memory.Tree.node "verify_tables" σ bufs kids).Valid coreProgram rd args rets) :
    (Memory.Tree.node "verify_tables" σ bufs kids).pops coreProgram rd = vtPops rd σ := by
  have h := vtShape_ok
  simp only [vtShapeOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have h0 := Memory.Tree.retKids hv find_vt
  rw [← List.drop_zero (l := Fn.body _)] at h0
  obtain ⟨k1, h0, -⟩ := h0.dropMute noWitS_mute (segOk_parts h1)
  obtain ⟨k2, p2, h0, e2, -⟩ := h0.dropAtom (a := 17) (stmtAt_sound h2)
  obtain ⟨k3, h0, -⟩ := h0.dropMute noWitS_mute (segOk_parts h3)
  obtain ⟨k4, p4, h0, e4, -⟩ := h0.dropAtom (a := 2286) (stmtAt_sound h4)
  rw [e2, e4, h0.endMute noWitS_mute (noWitBlock_mute h5)]
  rfl

/-- `verify_sub`'s own entries: its stream's buffer, `dims_g`'s heights. -/
def vsPops (rd : Reader) (σ : Val) : List Pop :=
  [("stream", (Dest.heap (.n (val% «verify_sub» "stream")) 0 8192).words rd σ), ("table_logs", (Dest.heap (.n (val% «verify_sub» "dims_g")) 1 6).words rd σ)]

/-- **`verify_sub` pops its stream and its tables' heights, then its `certify_placement`'s, `verify_tables`' and
`open_stacked`'s entries.** -/
theorem vs_pops (hv : (Memory.Tree.node "verify_sub" σ bufs kids).Valid coreProgram rd args rets) :
    ∃ (tcp tvt tos : Memory.Tree) (i : ℕ), ∃ hi : i < vsOpen.length, σ (.n (val% «verify_sub» "size_sel")) = ofK (addressOfIndex i) ∧
      tcp.name = "certify_placement" ∧ tcp.Valid coreProgram rd [σ (.n (val% «verify_sub» "kappa_base")), σ (.n (val% «verify_sub» "g_squares"))] [σ (.n (val% «verify_sub» "g_total")), σ (.n (val% «verify_sub» "col_offsets"))] ∧
      tvt.name = "verify_tables" ∧
      tvt.Valid coreProgram rd
        (([597, 598, 599, 600, 601, 602, 0, 1, 254, 253, 71, 26, 4, 386, 582, 6, 604, 603, 607, 605, 25].map V.n).map σ)
        (((List.range 10).map fun k => V.n ((val% «verify_sub» "fs0@4") + k)).map σ) ∧
      tos.name = vsOpen[i] ∧
      tos.Valid coreProgram rd (([66, 1441, 1442, 1443, 1444, 1445, 1987, 268, 271, 1989, 1991].map V.n).map σ)
        (((List.range 5).map fun k => V.n ((val% «verify_sub» "sumcheck_target") + k)).map σ) ∧ tcp ∈ kids ∧ tvt ∈ kids ∧ tos ∈ kids ∧
      (Memory.Tree.node "verify_sub" σ bufs kids).pops coreProgram rd =
        vsPops rd σ ++ tcp.pops coreProgram rd ++ tvt.pops coreProgram rd ++ tos.pops coreProgram rd := by
  have h := vsShape_ok
  simp only [vsShapeOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  have h0 := Memory.Tree.retKids hv find_vsub
  rw [← List.drop_zero (l := Fn.body _)] at h0
  obtain ⟨q1, h0, m1⟩ := h0.dropMute noWitS_mute (segOk_parts h1)
  obtain ⟨q2, p2, h0, e2, m2⟩ := h0.dropAtom (a := 8) (stmtAt_sound h2)
  obtain ⟨q3, h0, m3⟩ := h0.dropMute noWitS_mute (segOk_parts h3)
  obtain ⟨q4, p4, h0, e4, m4⟩ := h0.dropAtom (a := 55) (stmtAt_sound h4)
  obtain ⟨q5, h0, m5⟩ := h0.dropMute noWitS_mute (segOk_parts h5)
  obtain ⟨tcp, qa, p6, ncp, vcp, h0, e6, icp, m6⟩ := h0.dropCall (a := 243) (stmtAt_sound h6)
  obtain ⟨q6, h0, m7⟩ := h0.dropMute noWitS_mute (segOk_parts h7)
  obtain ⟨tvt, qb, p8, nvt, vvt, h0, e8, ivt, m8⟩ := h0.dropCall (a := 355) (stmtAt_sound h8)
  obtain ⟨q7, h0, m9⟩ := h0.dropMute noWitS_mute (segOk_parts h9)
  obtain ⟨tos, i, qc, p10, hi, hx, nos, vos, h0, e10, ios, -⟩ := h0.dropDispatch (a := 1588) (stmtAt_sound h10)
  have m5' : ∀ x ∈ q5, x ∈ kids := fun x hx => m1 _ (m2 _ (m3 _ (m4 _ (m5 _ hx))))
  have m7' : ∀ x ∈ q6, x ∈ kids := fun x hx => m5' _ (m6 _ (m7 _ hx))
  refine ⟨tcp, tvt, tos, i, hi, hx, ncp, vcp, nvt, vvt, nos, vos, m5' _ icp, m7' _ ivt,
    m7' _ (m8 _ (m9 _ ios)), ?_⟩
  rw [e2, e4, e6, e8, e10, h0.endMute noWitS_mute (noWitBlock_mute h11)]
  simp [vsPops, vsStreamA, vsLogsA, Atom.pops, Hint.pops]

end
end LeanVM.Guest.B1.VerifySub
