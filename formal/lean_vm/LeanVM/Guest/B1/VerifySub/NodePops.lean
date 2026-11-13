/-
  LeanVM.Guest.B1.VerifySub.NodePops

  The witness-stream entries a valid call instance of `verify_sub`, `certify_placement` or `verify_tables` pops: its own hints' words, its noisy callees' entries spliced in.
-/

module

public import LeanVM.Guest.B1.VerifySub.NodeShapes
public import LeanVM.Guest.B1.Common.Find

/-!
# The nodes' pops

* `cp_pops`: `certify_placement` pops its group order's buffer (`col_group_order`);
* `vt_pops`: `verify_tables` pops its block group order's buffer (`block_group_order`), then its round count (`zc_tau_max`);
* `vs_pops`: `verify_sub` pops its stream's buffer (`stream`) and `dims_g`'s heights (`table_logs`), then its `certify_placement`'s, `verify_tables`' and `open_stacked`'s entries; every other callee pops nothing (`vsMute`).
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

theorem segOk_parts {l : List Stmt} {a n : ℕ} (h : segOk l a n = true) :
    (Stmt.noRetList ((l.drop a).take n) && Stmt.muteList vsMuteSet.contains ((l.drop a).take n)) = true := h

/-- `certify_placement`'s entry: its group order's buffer. -/
def cpPop (rd : Reader) (σ : Val) : Pop := ("col_group_order", (Dest.heap (.n 136) 0 9).words rd σ)

/-- **`certify_placement` pops its group order's buffer.** -/
theorem cp_pops (hv : (Memory.Tree.node "certify_placement" σ bufs kids).Valid coreProgram rd args rets) :
    (Memory.Tree.node "certify_placement" σ bufs kids).pops coreProgram rd = [cpPop rd σ] := by
  have h := cpShape_ok
  simp only [cpShapeOk, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h0 := Memory.Tree.retKids hv find_cp
  rw [← List.drop_zero (l := Fn.body _)] at h0
  obtain ⟨k1, h0⟩ := h0.dropMute vsMute (segOk_parts h1)
  obtain ⟨k2, p2, h0, e⟩ := h0.dropAtom (a := 135) (stmtAt_sound h2)
  rw [e, h0.endMute vsMute h3]
  rfl

/-- `verify_tables`' entries: its block group order's buffer, its round count. -/
def vtPops (rd : Reader) (σ : Val) : List Pop :=
  [("block_group_order", (Dest.heap (.n 36) 0 24).words rd σ), ("zc_tau_max", [σ (.n 2544)])]

/-- **`verify_tables` pops its block group order's buffer, then its round count.** -/
theorem vt_pops (hv : (Memory.Tree.node "verify_tables" σ bufs kids).Valid coreProgram rd args rets) :
    (Memory.Tree.node "verify_tables" σ bufs kids).pops coreProgram rd = vtPops rd σ := by
  have h := vtShape_ok
  simp only [vtShapeOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have h0 := Memory.Tree.retKids hv find_vt
  rw [← List.drop_zero (l := Fn.body _)] at h0
  obtain ⟨k1, h0⟩ := h0.dropMute vsMute (segOk_parts h1)
  obtain ⟨k2, p2, h0, e2⟩ := h0.dropAtom (a := 17) (stmtAt_sound h2)
  obtain ⟨k3, h0⟩ := h0.dropMute vsMute (segOk_parts h3)
  obtain ⟨k4, p4, h0, e4⟩ := h0.dropAtom (a := 2591) (stmtAt_sound h4)
  rw [e2, e4, h0.endMute vsMute h5]
  rfl

/-- `verify_sub`'s own entries: its stream's buffer, `dims_g`'s heights. -/
def vsPops (rd : Reader) (σ : Val) : List Pop :=
  [("stream", (Dest.heap (.n 25) 0 8192).words rd σ), ("table_logs", (Dest.heap (.n 71) 1 6).words rd σ)]

/-- **`verify_sub` pops its stream and its tables' heights, then its `certify_placement`'s, `verify_tables`' and
`open_stacked`'s entries.** -/
theorem vs_pops (hv : (Memory.Tree.node "verify_sub" σ bufs kids).Valid coreProgram rd args rets) :
    ∃ (tcp tvt tos : Memory.Tree) (i : ℕ), ∃ hi : i < vsOpen.length, σ (.n 278) = ofK (addressOfIndex i) ∧
      tcp.name = "certify_placement" ∧ tcp.Valid coreProgram rd [σ (.n 83), σ (.n 4)] [σ (.n 274), σ (.n 275)] ∧
      tvt.name = "verify_tables" ∧
      tvt.Valid coreProgram rd
        (([562, 563, 564, 565, 566, 567, 0, 1, 254, 253, 71, 26, 4, 335, 559, 6, 569, 568, 572, 570].map V.n).map σ)
        (((List.range 10).map fun k => V.n (573 + k)).map σ) ∧
      tos.name = vsOpen[i] ∧
      tos.Valid coreProgram rd (([66, 1370, 1371, 1372, 1373, 1374, 1917, 268, 271, 1919, 1921].map V.n).map σ)
        (((List.range 5).map fun k => V.n (1922 + k)).map σ) ∧
      (Memory.Tree.node "verify_sub" σ bufs kids).pops coreProgram rd =
        vsPops rd σ ++ tcp.pops coreProgram rd ++ tvt.pops coreProgram rd ++ tos.pops coreProgram rd := by
  have h := vsShape_ok
  simp only [vsShapeOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  have h0 := Memory.Tree.retKids hv find_vsub
  rw [← List.drop_zero (l := Fn.body _)] at h0
  obtain ⟨q1, h0⟩ := h0.dropMute vsMute (segOk_parts h1)
  obtain ⟨q2, p2, h0, e2⟩ := h0.dropAtom (a := 8) (stmtAt_sound h2)
  obtain ⟨q3, h0⟩ := h0.dropMute vsMute (segOk_parts h3)
  obtain ⟨q4, p4, h0, e4⟩ := h0.dropAtom (a := 55) (stmtAt_sound h4)
  obtain ⟨q5, h0⟩ := h0.dropMute vsMute (segOk_parts h5)
  obtain ⟨tcp, qa, p6, ncp, vcp, h0, e6⟩ := h0.dropCall (a := 243) (stmtAt_sound h6)
  obtain ⟨q6, h0⟩ := h0.dropMute vsMute (segOk_parts h7)
  obtain ⟨tvt, qb, p8, nvt, vvt, h0, e8⟩ := h0.dropCall (a := 333) (stmtAt_sound h8)
  obtain ⟨q7, h0⟩ := h0.dropMute vsMute (segOk_parts h9)
  obtain ⟨tos, i, qc, p10, hi, hx, nos, vos, h0, e10⟩ := h0.dropDispatch (a := 1544) (stmtAt_sound h10)
  refine ⟨tcp, tvt, tos, i, hi, hx, ncp, vcp, nvt, vvt, nos, vos, ?_⟩
  rw [e2, e4, e6, e8, e10, h0.endMute vsMute h11]
  simp [vsPops, vsStreamA, vsLogsA, Atom.pops, Hint.pops]

end
end LeanVM.Guest.B1.VerifySub
