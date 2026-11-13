/-
  LeanVM.Guest.B1.VerifySub.ChildPopsHon

  `verify_sub`'s honest valuation on an honest child (`vsσ` on the oracle `vsW`, its own buffers holding `ChildSegs.ownW`) pops the child's stream and heights as `Hints.childHints` pushes them.
-/

module

public import LeanVM.Guest.B1.VerifySub.ChildPops
public import LeanVM.Guest.B1.VerifySub.CSig

/-!
# The honest valuation's own entries

`vs_hon_ptrs`: the honest valuation points the stream and `dims_g` at their buffers' bases (`vs_alloc_bases`). `vs_hon_child_pops`: on a memory holding the own buffers, a valid `verify_sub` node of the honest valuation pops `childHints` past its sizes, stream by stream, given its `certify_placement`, `verify_tables` and `open_stacked` callees pop theirs (`vs_child_pops`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- **The honest valuation's stream and `dims_g` pointers** are their buffers' bases. -/
theorem vs_hon_ptrs {rd : Reader} {args : List E} (hl : args.length = 6) (bs : List ℕ)
    (outs : List (List E × Main.Layout)) (hbs : bs.length = 15) :
    vsσ rd (vsW bs outs) args (.n 25) = ofK (addressOfIndex (bs.getD 1 0)) ∧
      vsσ rd (vsW bs outs) args (.n 71) = ofK (addressOfIndex (bs.getD 3 0)) := by
  have h := vs_alloc_bases (rd := rd) hl bs outs hbs
  rw [vs_allocs] at h
  have h1 := congrArg (·[1]?) h
  have h3 := congrArg (·[3]?) h
  simp only [vsAllocVars, List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
    List.getElem?_cons_succ, List.getElem?_cons_zero, List.getElem?_map] at h1 h3
  obtain ⟨b0, b1, b2, b3, rest, rfl⟩ : ∃ b0 b1 b2 b3 rest, bs = b0 :: b1 :: b2 :: b3 :: rest := by
    match bs, hbs with
    | b0 :: b1 :: b2 :: b3 :: rest, _ => exact ⟨b0, b1, b2, b3, rest, rfl⟩
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at h1 h3
  exact ⟨h1, h3⟩

/-- **The honest valuation pops the child's stream and heights**, then its callees' entries: on a memory holding
the own buffers, a valid `verify_sub` node of `vsσ` pops `childHints` past its sizes, stream by stream, given its
`certify_placement`, `verify_tables` and `open_stacked` callees pop theirs. -/
theorem vs_hon_child_pops {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    {rd : Reader} {args : List E} (hl : args.length = 6) (b : ℕ) (outs : List (List E × Main.Layout))
    (hB : Main.MemL rd (bufL b (vsSizes S.d) S.ownW)) (hst : c.proof.stream.length ≤ Coverage.childStreamCap)
    {bufs : List ℕ} {kids : List Memory.Tree} {args' rets : List E}
    (hv : (Memory.Tree.node "verify_sub" (vsσ rd (vsW (bases b (vsSizes S.d)) outs) args) bufs kids).Valid
      coreProgram rd args' rets) :
    ∃ (tcp tvt tos : Memory.Tree), tcp.name = "certify_placement" ∧ tvt.name = "verify_tables" ∧
      tos.name ∈ vsOpen ∧
      (tcp.pops coreProgram rd = [("col_group_order", Hints.colGroupOrder S.layout)] →
        tvt.pops coreProgram rd = [("block_group_order", Hints.blockGroupOrder S.layout),
          ("zc_tau_max", [Hints.count (S.layout.tableLogHeights.foldl max 0)])] →
        SameStreams (tos.pops coreProgram rd)
          (Hints.merkleHints true (Hints.childQueries bytecode seed c) c.proof.openings) →
        SameStreams ((Memory.Tree.node "verify_sub" (vsσ rd (vsW (bases b (vsSizes S.d)) outs) args) bufs
          kids).pops coreProgram rd) ((Hints.childHints bytecode seed c).drop 4)) := by
  have hbl : (bases b (vsSizes S.d)).length = 15 := by rw [bases_length]; rfl
  obtain ⟨p1, p3⟩ := vs_hon_ptrs (rd := rd) hl _ outs hbl
  have hm1 := hB _ (vs_own_mem S b (i := 1) (by norm_num))
  have hm3 := hB _ (vs_own_mem S b (i := 3) (by norm_num))
  have hh : S.layout.tableLogHeights = S.hs := by rw [S.hlayout]; rfl
  have hl6 : S.layout.tableLogHeights.length = 6 := by
    rw [hh, ChildSegs.hs]
    simp [Tables.tableHeightsOf, S.hrowsL, tableLogFloors]
  obtain ⟨tcp, tvt, tos, i, hi, -, ncp, -, nvt, -, nos, -, h⟩ := vs_child_pops S.hann hv p1 p3 hm1
    (by rw [hh]; exact hm3) hst hl6
  exact ⟨tcp, tvt, tos, ncp, nvt, by rw [nos]; exact List.getElem_mem hi, h⟩

end
end LeanVM.Guest.B1.VerifySub
