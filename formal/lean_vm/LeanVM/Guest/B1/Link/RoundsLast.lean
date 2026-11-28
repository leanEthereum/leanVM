/-
  LeanVM.Guest.B1.Link.RoundsLast

  B1 for `link_rounds_last` (24 specializations): the last `k < 4` rounds, record to record.
-/

module

public import LeanVM.Guest.B1.Link.RoundsSound
public import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.CoreRef

/-!
# `link_rounds_last`

`link_rounds_last(rd, out, pts, tabs, n_tail, bits, k)` (G) reads a record (the capacity's five
cells, the cursor, the claim) at `rd`, runs `k < 4` rounds and stores the record after them at
`out`, the challenges at `pts[0 .. k)`. Its meaning (`MeaningLRLast`): a chain of `k` rounds from
the record read to the record stored, given `grind_check`'s soundness (`GcSound1`) and, when the
rounds grind, the windows table at `tabs`.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A round state's record: the capacity, the cursor, the claim. -/
def RSt.cells (st : RSt) : List E := st.cap ++ [st.cur, st.cl]

/-- **`link_rounds_last__L{nt}_L{bits}_L{k}(rd, out, pts, tabs)`**: it returns `0`; when the
rounds grind, with `tabs` the windows table, for the record `st` at `rd` a chain of `k` rounds to
the record at `out`, the challenges at `pts`. -/
def MeaningLRLast (nt bits k : ℕ) (rd : Reader) : List E → List E → Prop
  | [rp, out, pts, tabs], rets => rets = [0] ∧ ((bits ≠ 0 → WinTabs rd tabs) →
      ∃ (st : RSt) (l : List (E × RSt)), st.cap.length = 5 ∧ ReadsAt rd rp st.cells ∧
        l.length = k ∧ RoundChain rd nt bits st l ∧ ReadsAt rd pts (l.map Prod.fst) ∧
        ReadsAt rd out (chainLast st l).cells)
  | _, _ => False

theorem readsAt_cells {rd : Reader} {p : E} {σ : Val} {cap : List ℕ} {cur cl : ℕ} (hcap : cap.length = 5)
    (h : ∀ j (hj : j < 5), LoadHolds rd p j (σ (.n (cap[j]'(by omega)))))
    (h5 : LoadHolds rd p 5 (σ (.n cur))) (h6 : LoadHolds rd p 6 (σ (.n cl))) :
    ReadsAt rd p (rstOf σ cap cur cl).cells := by
  match cap, hcap with
  | [a, b, c, d, e], _ =>
    intro j hj
    simp only [RSt.cells, rstOf, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.length_cons, List.length_nil] at hj ⊢
    interval_cases j
    · exact h 0 (by norm_num)
    · exact h 1 (by norm_num)
    · exact h 2 (by norm_num)
    · exact h 3 (by norm_num)
    · exact h 4 (by norm_num)
    · exact h5
    · exact h6

/-- **`k = 0`**: the record copied. -/
theorem lrl0_sound {nt bits : ℕ} {name : String} {f : Fn} (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3]) (hbody : f.body = lrLastBody nt bits 0)
    (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd name args rets → MeaningLRLast nt bits 0 rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams]
  simp only [lrLastBody, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
    List.map_nil, word_zero]
  rintro ⟨σ, rfl, l0, l1, l2, l3, l4, s0, s1, s2, s3, s4, l5, s5, l6, s6, h11, hret⟩
  refine ⟨by rw [← hret, h11], fun _ ↦ ⟨rstOf σ [4, 5, 6, 7, 8] 9 10, [], rfl, ?_, rfl, trivial,
    readsAt_nil _ _, ?_⟩⟩
  · exact readsAt_cells rfl (fun j hj ↦ match j, hj with
      | 0, _ => l0 | 1, _ => l1 | 2, _ => l2 | 3, _ => l3 | 4, _ => l4) l5 l6
  · exact readsAt_cells rfl (fun j hj ↦ match j, hj with
      | 0, _ => s0 | 1, _ => s1 | 2, _ => s2 | 3, _ => s3 | 4, _ => s4) s5 s6

/-- **`k ≥ 1`**: the record read, `k` rounds, the record stored. -/
theorem lrl_sound {nt bits k : ℕ} {rd : Reader} (hnt : 1 ≤ nt) (hnt' : nt ≤ 32)
    (hk : bits = 0 ∨ (bits = 1 ∧ nt % 4 ≠ 3)) (hk0 : k ≠ 0) (hgc : bits ≠ 0 → GcSound1 rd)
    {name : String} {f : Fn} (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3]) (hbody : f.body = lrLastBody nt bits k)
    (args rets : List E) :
    coreProgram.Rel rd name args rets → MeaningLRLast nt bits k rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams]
  simp only [lrLastBody, hk0, ↓reduceIte]
  rintro ⟨σ, rfl, h⟩
  generalize hrs : lrRounds nt bits 2 3 k 11 [4, 5, 6, 7, 8] 9 10 none = rs at h
  have hlen : rs.2.1.length = 5 := by rw [← hrs]; exact lrRounds_cap_length _ _ _ _ _ _ _ _ _ _ rfl
  have hatR : AllAtoms rs.1 := by rw [← hrs]; exact lrRounds_atoms _ _ _ _ _ _ _ _ _ _
  simp only [holdsList_append] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, h⟩ := h
  obtain ⟨hR, h⟩ := (holdsList_atoms hatR _ _).mp h
  have hatS : AllAtoms ((List.range 5).map fun j ↦ Stmt.atom (.load (.n (rs.2.1.getD j 0)) (.n 1) j)) := by
    intro s hs
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hs
    exact ⟨_, rfl⟩
  obtain ⟨hS, s5, s6, h0, hret⟩ := (holdsList_atoms hatS _ _).mp h
  simp only [word_zero, List.map_cons, List.map_nil] at h0 hret
  have hR' : ∀ a, Stmt.atom a ∈ (lrRounds nt bits 2 3 k 11 [4, 5, 6, 7, 8] 9 10 none).1 → a.Holds rd σ := by
    rw [hrs]; exact hR
  simp only [List.map_cons, List.map_nil]
  refine ⟨by rw [← hret, h0], fun hw ↦ ?_⟩
  obtain ⟨l, hl, hc, hlast, hpts, -⟩ := lrRounds_sound hnt hnt' hk (fun hb ↦ ⟨hgc hb, hw hb⟩) k 11
    [4, 5, 6, 7, 8] 9 10 none hR' (fun z hz ↦ absurd hz (by simp))
  rw [hrs] at hlast
  refine ⟨_, l, rfl, readsAt_cells rfl (fun j hj ↦ match j, hj with
      | 0, _ => l0 | 1, _ => l1 | 2, _ => l2 | 3, _ => l3 | 4, _ => l4) l5 l6, hl, hc,
    hpts, ?_⟩
  rw [hlast]
  refine readsAt_cells hlen (fun j hj ↦ ?_) s5 s6
  have := hS (.load (.n (rs.2.1.getD j 0)) (.n 1) j) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  simpa [Atom.Holds, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < rs.2.1.length by omega)]
    using this

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem lrl_L1_L0_L0_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L1_L0_L0" args rets → MeaningLRLast 1 0 0 rd args rets :=
  lrl0_sound (coreProgram_find?_at (j := idx% «link_rounds_last__L1_L0_L0») rfl) rfl lrl_L1_L0_L0_body rd args rets

set_option maxRecDepth 100000 in
theorem lrl_L1_L0_L1_sound (rd : Reader) (hgc : 0 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L1_L0_L1" args rets → MeaningLRLast 1 0 1 rd args rets :=
  lrl_sound (by decide) (by decide) (Or.inl rfl) (by decide) hgc
    (coreProgram_find?_at (j := idx% «link_rounds_last__L1_L0_L1») rfl) rfl lrl_L1_L0_L1_body args rets

set_option maxRecDepth 100000 in
theorem lrl_L1_L0_L2_sound (rd : Reader) (hgc : 0 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L1_L0_L2" args rets → MeaningLRLast 1 0 2 rd args rets :=
  lrl_sound (by decide) (by decide) (Or.inl rfl) (by decide) hgc
    (coreProgram_find?_at (j := idx% «link_rounds_last__L1_L0_L2») rfl) rfl lrl_L1_L0_L2_body args rets

set_option maxRecDepth 100000 in
theorem lrl_L1_L0_L3_sound (rd : Reader) (hgc : 0 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L1_L0_L3" args rets → MeaningLRLast 1 0 3 rd args rets :=
  lrl_sound (by decide) (by decide) (Or.inl rfl) (by decide) hgc
    (coreProgram_find?_at (j := idx% «link_rounds_last__L1_L0_L3») rfl) rfl lrl_L1_L0_L3_body args rets

set_option maxRecDepth 100000 in
theorem lrl_L7_L0_L0_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L7_L0_L0" args rets → MeaningLRLast 7 0 0 rd args rets :=
  lrl0_sound (coreProgram_find?_at (j := idx% «link_rounds_last__L7_L0_L0») rfl) rfl lrl_L7_L0_L0_body rd args rets

set_option maxRecDepth 100000 in
theorem lrl_L7_L0_L1_sound (rd : Reader) (hgc : 0 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L7_L0_L1" args rets → MeaningLRLast 7 0 1 rd args rets :=
  lrl_sound (by decide) (by decide) (Or.inl rfl) (by decide) hgc
    (coreProgram_find?_at (j := idx% «link_rounds_last__L7_L0_L1») rfl) rfl lrl_L7_L0_L1_body args rets

set_option maxRecDepth 100000 in
theorem lrl_L7_L0_L2_sound (rd : Reader) (hgc : 0 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L7_L0_L2" args rets → MeaningLRLast 7 0 2 rd args rets :=
  lrl_sound (by decide) (by decide) (Or.inl rfl) (by decide) hgc
    (coreProgram_find?_at (j := idx% «link_rounds_last__L7_L0_L2») rfl) rfl lrl_L7_L0_L2_body args rets

set_option maxRecDepth 100000 in
theorem lrl_L7_L0_L3_sound (rd : Reader) (hgc : 0 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L7_L0_L3" args rets → MeaningLRLast 7 0 3 rd args rets :=
  lrl_sound (by decide) (by decide) (Or.inl rfl) (by decide) hgc
    (coreProgram_find?_at (j := idx% «link_rounds_last__L7_L0_L3») rfl) rfl lrl_L7_L0_L3_body args rets

set_option maxRecDepth 100000 in
theorem lrl_L6_L0_L0_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L6_L0_L0" args rets → MeaningLRLast 6 0 0 rd args rets :=
  lrl0_sound (coreProgram_find?_at (j := idx% «link_rounds_last__L6_L0_L0») rfl) rfl lrl_L6_L0_L0_body rd args rets

set_option maxRecDepth 100000 in
theorem lrl_L6_L0_L1_sound (rd : Reader) (hgc : 0 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L6_L0_L1" args rets → MeaningLRLast 6 0 1 rd args rets :=
  lrl_sound (by decide) (by decide) (Or.inl rfl) (by decide) hgc
    (coreProgram_find?_at (j := idx% «link_rounds_last__L6_L0_L1») rfl) rfl lrl_L6_L0_L1_body args rets

set_option maxRecDepth 100000 in
theorem lrl_L6_L0_L2_sound (rd : Reader) (hgc : 0 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L6_L0_L2" args rets → MeaningLRLast 6 0 2 rd args rets :=
  lrl_sound (by decide) (by decide) (Or.inl rfl) (by decide) hgc
    (coreProgram_find?_at (j := idx% «link_rounds_last__L6_L0_L2») rfl) rfl lrl_L6_L0_L2_body args rets

set_option maxRecDepth 100000 in
theorem lrl_L6_L0_L3_sound (rd : Reader) (hgc : 0 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L6_L0_L3" args rets → MeaningLRLast 6 0 3 rd args rets :=
  lrl_sound (by decide) (by decide) (Or.inl rfl) (by decide) hgc
    (coreProgram_find?_at (j := idx% «link_rounds_last__L6_L0_L3») rfl) rfl lrl_L6_L0_L3_body args rets

set_option maxRecDepth 100000 in
theorem lrl_L8_L1_L0_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L8_L1_L0" args rets → MeaningLRLast 8 1 0 rd args rets :=
  lrl0_sound (coreProgram_find?_at (j := idx% «link_rounds_last__L8_L1_L0») rfl) rfl lrl_L8_L1_L0_body rd args rets

set_option maxRecDepth 100000 in
theorem lrl_L8_L1_L1_sound (rd : Reader) (hgc : 1 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L8_L1_L1" args rets → MeaningLRLast 8 1 1 rd args rets :=
  lrl_sound (by decide) (by decide) (Or.inr ⟨rfl, by decide⟩) (by decide) hgc
    (coreProgram_find?_at (j := idx% «link_rounds_last__L8_L1_L1») rfl) rfl lrl_L8_L1_L1_body args rets

set_option maxRecDepth 100000 in
theorem lrl_L8_L1_L2_sound (rd : Reader) (hgc : 1 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L8_L1_L2" args rets → MeaningLRLast 8 1 2 rd args rets :=
  lrl_sound (by decide) (by decide) (Or.inr ⟨rfl, by decide⟩) (by decide) hgc
    (coreProgram_find?_at (j := idx% «link_rounds_last__L8_L1_L2») rfl) rfl lrl_L8_L1_L2_body args rets

set_option maxRecDepth 100000 in
theorem lrl_L8_L1_L3_sound (rd : Reader) (hgc : 1 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L8_L1_L3" args rets → MeaningLRLast 8 1 3 rd args rets :=
  lrl_sound (by decide) (by decide) (Or.inr ⟨rfl, by decide⟩) (by decide) hgc
    (coreProgram_find?_at (j := idx% «link_rounds_last__L8_L1_L3») rfl) rfl lrl_L8_L1_L3_body args rets

set_option maxRecDepth 100000 in
theorem lrl_L9_L1_L0_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L9_L1_L0" args rets → MeaningLRLast 9 1 0 rd args rets :=
  lrl0_sound (coreProgram_find?_at (j := idx% «link_rounds_last__L9_L1_L0») rfl) rfl lrl_L9_L1_L0_body rd args rets

set_option maxRecDepth 100000 in
theorem lrl_L9_L1_L1_sound (rd : Reader) (hgc : 1 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L9_L1_L1" args rets → MeaningLRLast 9 1 1 rd args rets :=
  lrl_sound (by decide) (by decide) (Or.inr ⟨rfl, by decide⟩) (by decide) hgc
    (coreProgram_find?_at (j := idx% «link_rounds_last__L9_L1_L1») rfl) rfl lrl_L9_L1_L1_body args rets

set_option maxRecDepth 100000 in
theorem lrl_L9_L1_L2_sound (rd : Reader) (hgc : 1 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L9_L1_L2" args rets → MeaningLRLast 9 1 2 rd args rets :=
  lrl_sound (by decide) (by decide) (Or.inr ⟨rfl, by decide⟩) (by decide) hgc
    (coreProgram_find?_at (j := idx% «link_rounds_last__L9_L1_L2») rfl) rfl lrl_L9_L1_L2_body args rets

set_option maxRecDepth 100000 in
theorem lrl_L9_L1_L3_sound (rd : Reader) (hgc : 1 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L9_L1_L3" args rets → MeaningLRLast 9 1 3 rd args rets :=
  lrl_sound (by decide) (by decide) (Or.inr ⟨rfl, by decide⟩) (by decide) hgc
    (coreProgram_find?_at (j := idx% «link_rounds_last__L9_L1_L3») rfl) rfl lrl_L9_L1_L3_body args rets

set_option maxRecDepth 100000 in
theorem lrl_L10_L1_L0_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L10_L1_L0" args rets → MeaningLRLast 10 1 0 rd args rets :=
  lrl0_sound (coreProgram_find?_at (j := idx% «link_rounds_last__L10_L1_L0») rfl) rfl lrl_L10_L1_L0_body rd args rets

set_option maxRecDepth 100000 in
theorem lrl_L10_L1_L1_sound (rd : Reader) (hgc : 1 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L10_L1_L1" args rets → MeaningLRLast 10 1 1 rd args rets :=
  lrl_sound (by decide) (by decide) (Or.inr ⟨rfl, by decide⟩) (by decide) hgc
    (coreProgram_find?_at (j := idx% «link_rounds_last__L10_L1_L1») rfl) rfl lrl_L10_L1_L1_body args rets

set_option maxRecDepth 100000 in
theorem lrl_L10_L1_L2_sound (rd : Reader) (hgc : 1 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L10_L1_L2" args rets → MeaningLRLast 10 1 2 rd args rets :=
  lrl_sound (by decide) (by decide) (Or.inr ⟨rfl, by decide⟩) (by decide) hgc
    (coreProgram_find?_at (j := idx% «link_rounds_last__L10_L1_L2») rfl) rfl lrl_L10_L1_L2_body args rets

set_option maxRecDepth 100000 in
theorem lrl_L10_L1_L3_sound (rd : Reader) (hgc : 1 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds_last__L10_L1_L3" args rets → MeaningLRLast 10 1 3 rd args rets :=
  lrl_sound (by decide) (by decide) (Or.inr ⟨rfl, by decide⟩) (by decide) hgc
    (coreProgram_find?_at (j := idx% «link_rounds_last__L10_L1_L3») rfl) rfl lrl_L10_L1_L3_body args rets

end
end LeanVM.Guest.B1.Link
