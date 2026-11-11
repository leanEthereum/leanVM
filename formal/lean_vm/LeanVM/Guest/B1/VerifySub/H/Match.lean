/-
  LeanVM.Guest.B1.VerifySub.H.Match

  `verify_sub`'s frames on an honest child are its callees: names, arguments, results; its
  dispatch's selector; its allocations' sizes and pointers.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Sigma

/-!
# The frames

`vs_rets`: a call's results are its result variables' values. `vs_callsMatch`: the thirteen
frames are the callees (`ChildSegs.kids`) on their results. `vs_dispOk`: the dispatch's selector
names one of its callees. `vs_alloc_sizes`, `vs_alloc_bases`: the allocations are the own buffers.
`ChildSegs.ownW_lens`: the own buffers' lengths the loads need.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

variable {bytecode : List K} {seed : Digest} {c : Child} {S : ChildSegs bytecode seed c}
  {bs : List ℕ} {sqE : ℕ} {outs : List (List E × Main.Layout)} {args : List E} {σ : Val}

/-- **A call's results** are its result variables' values. -/
theorem vs_rets (G : VsSig S bs sqE outs args σ) (j : ℕ) (hj : j < 13)
    (hlen : (vsRetVars.getD j []).length = (outs.getD j ([], [])).1.length) :
    ((vsRetVars.getD j []).map V.n).map σ = (outs.getD j ([], [])).1 := by
  apply List.ext_getElem (by simp only [List.length_map]; exact hlen)
  intro k h1 h2
  have hk : k < (vsRetVars.getD j []).length := by simpa using h1
  rw [List.getElem_map, List.getElem_map, ← List.getD_eq_getElem _ 0 hk, G.ret j hj k hk,
    List.getD_eq_getElem _ _ h2]

/-- The size's index is below the dispatch's `13` callees. -/
theorem ChildSegs.size_lt (S : ChildSegs bytecode seed c) :
    S.μs - B1.Whir.minOpenLog < 13 := by
  have h1 : S.μs ≤ 32 := S.hmu32
  have h2 : 20 ≤ S.μs := S.hmu20
  unfold B1.Whir.minOpenLog
  omega

set_option maxRecDepth 100000 in
/-- **`verify_sub`'s frames are its callees.** -/
theorem vs_callsMatch (hbl : bytecode.length = 2 ^ 23) {outE : ℕ}
    (hargs : args = [(digestHalves (statementDigest seed c.statement)).1,
      (digestHalves (statementDigest seed c.statement)).2, (digestHalves seed).1,
      (digestHalves seed).2, ofK (addressOfIndex sqE), ofK (addressOfIndex outE)])
    (G : VsSig S bs sqE outs args σ) (O : VsOuts S bs sqE outs) :
    CallsMatch σ ((vsCPre.filterMap (Core.Stmt.callSF σ)).map (mkCall σ))
      (kidsAt (S.kids bs sqE) [] outs) outs := by
  have R := G.ret
  have P := G.ptr
  -- the parameters
  have a0 : σ (.n 0) = (digestHalves (statementDigest seed c.statement)).1 := by
    rw [G.par 0 (by norm_num), hargs]; rfl
  have a1 : σ (.n 1) = (digestHalves (statementDigest seed c.statement)).2 := by
    rw [G.par 1 (by norm_num), hargs]; rfl
  have a4 : σ (.n 4) = ofK (addressOfIndex sqE) := by rw [G.par 4 (by norm_num), hargs]; rfl
  -- the pointers
  have q6 : σ (.n 6) = ofK (addressOfIndex (vb bs 0)) := P 0 (by norm_num)
  have q26 : σ (.n 26) = ofK (addressOfIndex (vb bs 2)) := P 2 (by norm_num)
  have q127 : σ (.n 127) = ofK (addressOfIndex (vb bs 3)) := P 3 (by norm_num)
  have q139 : σ (.n 139) = ofK (addressOfIndex (vb bs 4)) := P 4 (by norm_num)
  have q310 : σ (.n 310) = ofK (addressOfIndex (vb bs 5)) := P 5 (by norm_num)
  have q427 : σ (.n 427) = ofK (addressOfIndex (vb bs 7)) := P 7 (by norm_num)
  have q635 : σ (.n 635) = ofK (addressOfIndex (vb bs 8)) := P 8 (by norm_num)
  have q647 : σ (.n 647) = ofK (addressOfIndex (vb bs 9)) := P 9 (by norm_num)
  have q648 : σ (.n 648) = ofK (addressOfIndex (vb bs 10)) := P 10 (by norm_num)
  have q664 : σ (.n 664) = ofK (addressOfIndex (vb bs 11)) := P 11 (by norm_num)
  have q665 : σ (.n 665) = ofK (addressOfIndex (vb bs 12)) := P 12 (by norm_num)
  -- the results
  obtain ⟨-, -, -, ⟨K5, hK5⟩⟩ := S.runG' hbl
  obtain ⟨K7, hK7⟩ := S.s7_capOf hbl
  obtain ⟨e10, e11, e138, e139, e295, h9, -⟩ := O.o9
  obtain ⟨pb, pb1, h11, -⟩ := O.o11
  have r130 : σ (.n 128) = gen ^ S.logMem := by
    rw [show σ (.n 128) = _ from R 1 (by norm_num) 0 (by decide), O.o1]; rfl
  have r522 : σ (.n 309) = gen ^ S.μ := by
    rw [show σ (.n 309) = _ from R 2 (by norm_num) 0 (by decide), O.o2]; simp [ChildSegs.μ]
  have r5 : ∀ i < 9, σ (.n (626 + i)) = (outs.getD 5 ([], [])).1.getD i 0 := fun i hi ↦ by
    rw [← vsRetVars_runs.1 i hi]; exact R 5 (by norm_num) i (by rw [vsRetVars_lens.1]; exact hi)
  have r6 : ∀ i < 10, σ (.n (636 + i)) = (outs.getD 6 ([], [])).1.getD i 0 := fun i hi ↦ by
    rw [← vsRetVars_runs.2.1 i hi]; exact R 6 (by norm_num) i (by rw [vsRetVars_lens.2.1]; exact hi)
  have r631 : σ (.n 631) = ofK (addressOfIndex (S.cT bs)) := by
    rw [show σ (.n 631) = _ from r5 5 (by norm_num), O.o5, hK5]
    exact Tables.tb_ofK_gpow_mul _ _
  have r641 : σ (.n 641) = ofK (addressOfIndex (S.cK bs)) := by
    rw [show σ (.n 641) = _ from r6 5 (by norm_num), O.o6]
    show ofK (addressOfIndex (S.cT bs)) * gen ^ 5 * gen ^ (3 * S.H.n) * gen ^ 159 = _
    rw [Tables.tb_ofK_gpow_mul, Tables.tb_ofK_gpow_mul, Tables.tb_ofK_gpow_mul, ChildSegs.cK,
      (S.H_run hbl).2.2.2, show S.cT bs + 5 + 3 * S.H.n + 159 = S.cT bs + (5 + 3 * S.H.n + 159) by
        omega]
  have r642 : σ (.n 642) = gen ^ S.H.n := by
    rw [show σ (.n 642) = _ from r6 6 (by norm_num), O.o6]; rfl
  have r644 : σ (.n 644) = S.H.rm := by
    rw [show σ (.n 644) = _ from r6 8 (by norm_num), O.o6]; rfl
  have r656 : σ (.n 656) = ofK (addressOfIndex (S.cW bs)) := by
    rw [show σ (.n 656) = _ from R 7 (by norm_num) 5 (by decide), O.o7, hK7]
    exact Tables.tb_ofK_gpow_mul _ _
  have r1674 : σ (.n 1682) = gen ^ Tables.stackTotal S.kappas := by
    rw [show σ (.n 1682) = _ from R 9 (by norm_num) 0 (by decide), h9]; rfl
  have e6 : [σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640)] = S.s6.cap := by
    rw [S.s6_capOf hbl, show σ (.n 636) = _ from r6 0 (by norm_num),
      show σ (.n 637) = _ from r6 1 (by norm_num), show σ (.n 638) = _ from r6 2 (by norm_num),
      show σ (.n 639) = _ from r6 3 (by norm_num), show σ (.n 640) = _ from r6 4 (by norm_num),
      O.o6]
    rfl
  have hpl : S.point.length = S.μ := (S.runG' hbl).2.2.1
  have hvl := S.vals_length hbl
  have hc14 := S.size_lt
  -- the frames
  rw [vs_calls σ]
  refine callsMatch_kidsAt _ _ _ _ (by simp [vsCallsA, vsCallsB, ChildSegs.kids])
    (by rw [ChildSegs.kids_length, O.len]) fun j hj ↦ ?_
  have hj' : j < 13 := by simpa [vsCallsA, vsCallsB] using hj
  interval_cases j
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 0 (by norm_num)
      (by rw [O.o0]; simp only [List.length_cons, List.length_nil]; rfl)⟩⟩
    show [σ (.n 110)] = [eOfNat S.rate]
    rw [G.e112]
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 1 (by norm_num)
      (by rw [O.o1]; simp only [List.length_cons, List.length_nil]; rfl)⟩⟩
    show [σ (.n 27)] = [eOfNat S.logMem]
    rw [G.e29]
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 2 (by norm_num)
      (by rw [O.o2]; simp only [List.length_cons, List.length_nil]; rfl)⟩⟩
    show [σ (.n 308), σ (.n 4)] = [gen ^ pushTotal S.logMem S.hs, ofK (addressOfIndex sqE)]
    rw [G.e521, a4]
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 3 (by norm_num)
      (by rw [O.o3]; simp only [List.length_cons, List.length_nil]; rfl)⟩⟩
    show [σ (.n 324)] = [S.x0]
    rw [G.e537]
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 4 (by norm_num)
      (by rw [O.o4]; simp only [List.length_cons, List.length_nil]; rfl)⟩⟩
    show [σ (.n 334)] = [S.x1]
    rw [G.e547]
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 5 (by norm_num)
      (by rw [vsRetVars_lens.1, O.o5, hK5]; simp [capOf, hvl])⟩⟩
    show [σ (.n 612), σ (.n 613), σ (.n 614), σ (.n 615), σ (.n 616), σ (.n 625), σ (.n 309),
      σ (.n 310)] = S.capS ++ [ofK (addressOfIndex (vcG bs)), gen ^ S.μ,
        ofK (addressOfIndex (vb bs 5))]
    rw [← G.e825, G.e838, r522, q310]; rfl
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 6 (by norm_num)
      (by rw [vsRetVars_lens.2.1, O.o6]; simp [ChildSegs.vtRetsOf, Fs.squeeze, capOf])⟩⟩
    show [σ (.n 626), σ (.n 627), σ (.n 628), σ (.n 629), σ (.n 630), σ (.n 631), σ (.n 0),
      σ (.n 1), σ (.n 310), σ (.n 309), σ (.n 127), σ (.n 26), σ (.n 4), σ (.n 427),
      σ (.n 623), σ (.n 6), σ (.n 635), σ (.n 632), σ (.n 633), σ (.n 634)] =
      [S.s5.cap.getD 0 0, S.s5.cap.getD 1 0, S.s5.cap.getD 2 0, S.s5.cap.getD 3 0,
        S.s5.cap.getD 4 0, ofK (addressOfIndex (S.cT bs)),
        (digestHalves (statementDigest seed c.statement)).1,
        (digestHalves (statementDigest seed c.statement)).2, ofK (addressOfIndex (vb bs 5)),
        gen ^ S.point.length, ofK (addressOfIndex (vb bs 3)), ofK (addressOfIndex (vb bs 2)),
        ofK (addressOfIndex sqE), ofK (addressOfIndex (vb bs 7)), S.β,
        ofK (addressOfIndex (vb bs 0)), ofK (addressOfIndex (vb bs 8)), S.vals.getD 0 0,
        S.vals.getD 1 0, S.vals.getD 2 0]
    rw [show σ (.n 626) = _ from r5 0 (by norm_num), show σ (.n 627) = _ from r5 1 (by norm_num),
      show σ (.n 628) = _ from r5 2 (by norm_num), show σ (.n 629) = _ from r5 3 (by norm_num),
      show σ (.n 630) = _ from r5 4 (by norm_num), show σ (.n 632) = _ from r5 6 (by norm_num),
      show σ (.n 633) = _ from r5 7 (by norm_num), show σ (.n 634) = _ from r5 8 (by norm_num),
      r631, a0, a1, q310, r522, hpl, q127, q26, a4, q427, G.e836, q6, q635, O.o5, hK5]
    rfl
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 7 (by norm_num)
      (by rw [vsRetVars_lens.2.2.1, O.o7, hK7]; simp [capOf])⟩⟩
    show [σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640), σ (.n 641), σ (.n 646),
      σ (.n 635), σ (.n 650), σ (.n 647), σ (.n 648)] =
      S.s6.cap ++ [ofK (addressOfIndex (S.cK bs)), gen ^ S.τ, ofK (addressOfIndex (vb bs 8)),
        ofK (addressOfIndex (S.cL bs)), ofK (addressOfIndex (vb bs 9)),
        ofK (addressOfIndex (vb bs 10))]
    rw [← e6, r641, G.e858, q635, G.e862, q647, q648]; rfl
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 8 (by norm_num)
      (by rw [O.o8]; simp only [List.length_cons, List.length_nil]; rfl)⟩⟩
    show [σ (.n 648), σ (.n 664)] = [ofK (addressOfIndex (vb bs 10)), ofK (addressOfIndex (vb
        bs 11))]
    rw [q648, q664]
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 9 (by norm_num)
      (by rw [h9]; simp only [List.length_cons, List.length_nil]; rfl)⟩⟩
    show [σ (.n 139), σ (.n 4)] = [ofK (addressOfIndex (vb bs 4)), ofK (addressOfIndex sqE)]
    rw [q139, a4]
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 10 (by norm_num)
      (by rw [O.o10]; simp only [List.length_cons, List.length_nil]; rfl)⟩⟩
    show [σ (.n 1682), σ (.n 4)] = [gen ^ Tables.stackTotal S.kappas, ofK (addressOfIndex sqE)]
    rw [r1674, a4]
  · refine ⟨?_, rfl, fun _ ↦ ⟨?_, vs_rets G 11 (by norm_num)
      (by rw [h11]; simp only [List.length_cons, List.length_nil]; rfl)⟩⟩
    · show vsOpenNames.getD (logG (σ (.n 1686))) "" = B1.Whir.openName S.μs
      rw [G.e1686, logG_gen_pow (by have := S.size_lt; omega), vsOpenNames_eq]
      rfl
    · show [σ (.n 122), σ (.n 1100), σ (.n 1101), σ (.n 1102), σ (.n 1103), σ (.n 1104),
        σ (.n 1681), σ (.n 324), σ (.n 334), σ (.n 656)] = B1.Whir.rateSel S.rate ::
          (capOf S.s8.perm ++ [S.target,
          (digestHalves S.root).1, (digestHalves S.root).2, ofK (addressOfIndex (S.cW bs))])
      rw [G.e122, ← G.e1312, G.e1886, G.e537, G.e547, r656, S.root_cells]
      rfl
  · refine ⟨rfl, ?_, fun _ ↦ ⟨?_, vs_rets G 12 (by norm_num)
      (by rw [O.o12, List.length_nil]; rfl)⟩⟩
    · show true = @decide (S.termOk (outs.take 12)) (Classical.propDecidable _)
      exact (@decide_eq_true _ (Classical.propDecidable _) O.term).symm
    · show [σ (.n 4), σ (.n 310), σ (.n 635), σ (.n 644), σ (.n 309), σ (.n 642), σ (.n 128),
        σ (.n 646), σ (.n 139), σ (.n 1111), σ (.n 1683), σ (.n 647), σ (.n 665),
        σ (.n 1692), σ (.n 1693), σ (.n 1694), σ (.n 1695), σ (.n 1691)] =
        [ofK (addressOfIndex sqE), ofK (addressOfIndex (vb bs 5)), ofK (addressOfIndex (vb bs 8)),
          S.H.rm, gen ^ S.μ, gen ^ S.H.n, gen ^ S.logMem, gen ^ S.τ,
          ofK (addressOfIndex (vb bs 4)), S.lam, ((outs.take 12).getD 9 ([], [])).1.getD 1 0,
          ofK (addressOfIndex (vb bs 9)), ofK (addressOfIndex (vb bs 12)),
          ((outs.take 12).getD 11 ([], [])).1.getD 1 0, ((outs.take 12).getD 11 ([], [])).1.getD 2 0,
          ((outs.take 12).getD 11 ([], [])).1.getD 3 0, ((outs.take 12).getD 11 ([], [])).1.getD 4 0,
          ((outs.take 12).getD 11 ([], [])).1.getD 0 0]
      rw [take_getD _ _ (by norm_num : 9 < 12), take_getD _ _ (by norm_num : 11 < 12), a4, q310,
        q635, r644, r522, r642, r130, G.e858, q139, G.e1111,
        show σ (.n 1683) = _ from R 9 (by norm_num) 1 (by decide), q647, q665,
        show σ (.n 1691) = _ from R 11 (by norm_num) 0 (by decide),
        show σ (.n 1692) = _ from R 11 (by norm_num) 1 (by decide),
        show σ (.n 1693) = _ from R 11 (by norm_num) 2 (by decide),
        show σ (.n 1694) = _ from R 11 (by norm_num) 3 (by decide),
        show σ (.n 1695) = _ from R 11 (by norm_num) 4 (by decide)]

/-- **The dispatch's selector names one of its callees.** -/
theorem vs_dispOk (S : ChildSegs bytecode seed c)
    (h1686 : σ (.n 1686) = gen ^ (S.μs - B1.Whir.minOpenLog)) :
    ∀ s ∈ vsCPre, DispOk σ s := by
  intro s hs
  rw [vs_split_disp] at hs
  simp only [List.mem_append, List.mem_singleton] at hs
  have hc := S.size_lt
  rcases hs with (h | rfl) | h
  · have := List.all_eq_true.mp vs_noDisp.1 s h
    cases s with
    | dispatch => simp [noDispatchB] at this
    | _ => trivial
  · exact ⟨_, by simp [vsOpenNames]; exact hc, by omega, by rw [h1686, gen_pow_eq_ofK]⟩
  · have := List.all_eq_true.mp vs_noDisp.2 s h
    cases s with
    | dispatch => simp [noDispatchB] at this
    | _ => trivial

/-- **The allocations' sizes** are the own buffers'. -/
theorem vs_alloc_sizes (hbl : bytecode.length = 2 ^ 23) (G : VsSig S bs sqE outs args σ)
    (O : VsOuts S bs sqE outs) :
    (vsCPre.filterMap Main.Stmt.allocSz).map (fun x ↦ x.2.elim id fun s ↦ logG (σ s)) =
      vsSizes S.μ := by
  have r522 : σ (.n 309) = gen ^ S.μ := by
    rw [show σ (.n 309) = _ from G.ret 2 (by norm_num) 0 (by decide), O.o2]; simp [ChildSegs.μ]
  have hμ : S.μ < 2 ^ 64 - 1 := by
    have := (S.μ_bounds hbl).2
    omega
  rw [vs_allocs]
  show [167, 8192, 6, 7, 8, logG (σ (.n 309)), 4, 16, 34, 78, 64, 6, 64] = _
  rw [r522, logG_gen_pow hμ]
  rfl

/-- **The allocations' pointers** are the own buffers' first words. -/
theorem vs_alloc_bases (G : VsSig S bs sqE outs args σ) {b : ℕ} (hbs : bs = bases b (vsSizes S.μ)) :
    ((vsCPre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
      (bases b (vsSizes S.μ)).map (fun x ↦ ofK (addressOfIndex x)) := by
  have e : (vsCPre.filterMap Main.Stmt.allocSz).map Prod.fst = vsAllocVars.map V.n := by
    rw [vs_allocs]; rfl
  have hl : (bases b (vsSizes S.μ)).length = 13 := by rw [bases_length]; rfl
  have hv : vsAllocVars.length = 13 := rfl
  rw [e, ← hbs]
  apply List.ext_getElem (by simp [hv, hbs, hl])
  intro i h1 h2
  have hi : i < 13 := by simpa [hv] using h1
  simp only [List.getElem_map]
  rw [← List.getD_eq_getElem _ 0 (by omega : i < vsAllocVars.length), G.ptr i hi, vb,
    List.getD_eq_getElem _ _ (by rw [hbs, hl]; exact hi)]

/-- **The own buffers' lengths** the loads need. -/
theorem ChildSegs.ownW_lens (S : ChildSegs bytecode seed c) (hbl : bytecode.length = 2 ^ 23) :
    167 ≤ (S.ownW.getD 0 []).length ∧ 10 ≤ (S.ownW.getD 1 []).length ∧
      6 ≤ (S.ownW.getD 2 []).length ∧ 7 ≤ (S.ownW.getD 3 []).length ∧
      8 ≤ (S.ownW.getD 4 []).length ∧ 19 ≤ (S.ownW.getD 5 []).length ∧
      4 ≤ (S.ownW.getD 6 []).length ∧ 16 ≤ (S.ownW.getD 7 []).length ∧
      6 ≤ (S.ownW.getD 11 []).length ∧ 64 ≤ (S.ownW.getD 12 []).length := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 167 ≤ S.H.poolW.length
    rw [S.poolW_length hbl]
  · show 10 ≤ (vsStreamW c.proof.stream).length
    have := S.stream_length
    simp only [vsStreamW, List.length_append, List.length_replicate]
    omega
  · show 6 ≤ (S.rowsN.map eOfNat).length
    simp [S.hrowsL]
  · show 7 ≤ (vsDimsW S.logMem S.hs).length
    simp [vsDimsW, S.hs_length]
  · show 8 ≤ (vsKbW S.logMem S.hs).length
    simp [vsKbW, S.hs_length]
  · show 19 ≤ S.point.length
    rw [(S.runG' hbl).2.2.1]
    have := (S.μ_bounds hbl).1
    omega
  · show 4 ≤ S.alphas.length
    rw [S.alphas_length]
  · show 16 ≤ (eqKernel S.alphas).length
    rw [KeccakGkr.eqKernel_length, S.alphas_length]
    norm_num
  · show 6 ≤ S.rchs.length
    rw [S.rchs_length]
  · show 64 ≤ (ringCoefficients S.rchs).length
    simp [ringCoefficients, kBits]

end
end LeanVM.Guest.B1.VerifySub
