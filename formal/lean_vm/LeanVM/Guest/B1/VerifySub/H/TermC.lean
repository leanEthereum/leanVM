/-
  LeanVM.Guest.B1.VerifySub.H.TermC

  `check_opening_terminal` on an honest child: the WHIR terminal equation, its precondition on
  the honest memory, and its placed completeness within its bound as `verify_sub`'s last callee.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Regions
public import LeanVM.Guest.B1.VerifySub.H.Keccak
public import LeanVM.Guest.B1.VerifySub.H.TermCtx
public import LeanVM.Guest.B1.VerifySub.H.WhirLen
public import LeanVM.Guest.B1.VerifySub.TermGlue
public import LeanVM.Guest.B1.Terminal.TermCompleteB
public import LeanVM.Guest.B1.Terminal.TermWeight

/-!
# The terminal, honestly

`batchBasis_eq`: the stacked opening's batched weight is the terminal's `stackWeight`.
`ChildSegs.fin`: the WHIR terminal equation on the honest child (`ChildSegs.acc`).
`ChildSegs.termPre`: on a memory holding `certify_placement`'s buffers, `open_stacked`'s points
and the terminal's words (`termLin`), `TermPre` holds of the honest child.
`ChildSegs.term_via`: the terminal callee, entered (`termOk`), is a call on those words and
arguments, its precondition and regions holding. `ChildSegs.term_kidB`,
`ChildSegs.term_kidBW`: it is complete within `termBound` (by a tree within its weights).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- **The batched weight is the terminal's.** -/
theorem batchBasis_eq (L : Layout) (cl : List ColumnClaim) (t : E) (rp coeffs z : List E)
    (v lam : E) (x : List E) :
    batchBasis (stackClaims L cl t (fun r ↦ ringWeight rp r coeffs) (fun y ↦ eqEval z y, v)) lam x =
      stackWeight L cl rp coeffs z lam x := by
  simp [batchBasis, stackWeight, stackClaims, ringSwitchClaim]

theorem ringCoeffs_fold_length : ∀ (f a b : List E),
    (f.foldl (fun (acc : List E × List E) fP ↦
      (acc.1 ++ acc.2.map (fP * ·), acc.2.map (frobenius8 · 1))) (a, b)).1.length =
      a.length + f.length * b.length
  | [], a, b => by simp
  | x :: f, a, b => by
    rw [List.foldl_cons, ringCoeffs_fold_length f]
    simp only [List.length_append, List.length_map, List.length_cons]
    ring

theorem ringCoefficients_length {f g : List E} (hf : f.length = 8) (hg : g.length = 8) :
    (ringCoefficients f g).length = 64 := by
  unfold ringCoefficients
  rw [ringCoeffs_fold_length, hf, hg]; rfl

/-- A committed column's log is at most the log of the stack's total. -/
theorem committed_lt29 {kappas : List ℕ} (h : Tables.stackTotal kappas ≤ 2 ^ 28) :
    Tables.KappasBelow kappas := by
  intro c _
  rw [List.getD_eq_getElem?_getD]
  cases hc : (Tables.committedKappas kappas)[c]? with
  | none => simp
  | some x =>
    have hm := List.mem_of_getElem? hc
    have : 2 ^ x ≤ Tables.stackTotal kappas :=
      List.le_sum_of_mem (List.mem_map.2 ⟨x, hm, rfl⟩)
    have : 2 ^ x ≤ 2 ^ 28 := this.trans h
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    simp only [Option.getD_some]
    omega

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- **The WHIR terminal equation**, on the honest child. -/
theorem fin (hbl : bytecode.length = 2 ^ 23) :
    (S.w.inner + stackWeight S.layout (openedClaims S.claims [S.kOut]) S.kc.2.1 S.ctab S.oodZ
      S.lam S.w.point) * S.w.residual = S.w.target := by
  have h := S.acc
  obtain ⟨hk1, -, -⟩ := S.keccak_run hbl
  unfold Whir.WhirEnd.Accepts at h
  rw [S.ood_inv.2.2.1, S.ring_inv.2.2.2.2, hk1, batchBasis_eq] at h
  exact h

theorem layout_logMemory : S.layout.logMemory = S.logMem := by rw [S.hlayout]; rfl

theorem layout_heights : S.layout.tableLogHeights = S.hs := by rw [S.hlayout]; rfl

theorem stackLog_eq' (hbl : bytecode.length = 2 ^ 23) :
    S.layout.stackLog = max 15 (log2Ceil (Tables.stackTotal S.kappas)) := by
  rw [S.hlayout, stackLog_eq hbl]; rfl

/-- The terminal's bases at `certify_placement`'s offsets `e` and `open_stacked`'s points. -/
def termBases (bs : List ℕ) (sqE e pb pb1 : ℕ) : TermBases :=
  ⟨sqE, vb bs 5, vb bs 9, vb bs 4, e, vb bs 11, vb bs 14, pb, pb1, vb bs 6⟩

/-- The terminal's arguments at its bases. -/
noncomputable def termArgsH (B : TermBases) : List E :=
  termArgs B S.H.rm (gen ^ S.d) (gen ^ S.nT) (gen ^ S.logMem) (gen ^ S.τ) S.lam S.w.inner
    S.w.residual S.w.target (gen ^ max 15 (log2Ceil (Tables.stackTotal S.kappas)))

/-- **The terminal's precondition on the honest child.** -/
theorem termPre (hbl : bytecode.length = 2 ^ 23) (bs : List ℕ) (sqE e10 e11 e136 e137 e293 pb pb1 : ℕ)
    {rd : Reader} (hcp : Main.MemL rd (Tables.cpOwn S.logMem S.hs e10 e11 e136 e137 e293))
    (hpt : ReadsAt rd (ptr pb) (S.w.point ++ List.replicate (Whir.pointCap - S.μs) 0))
    (hpt1 : ReadsAt rd (ptr pb1) (S.w.point.map (1 + ·) ++ List.replicate (Whir.pointCap - S.μs) 1))
    (ht : Main.MemL rd (S.termLin bs sqE)) :
    TermPre rd S.layout S.bus S.claims S.kOut S.lam S.kc.2.1 S.ctab S.oodZ S.w.point
      (S.termArgsH (termBases bs sqE e293 pb pb1)) := by
  have hm : ∀ q ∈ S.termLin bs sqE, ReadsAt rd (ptr q.1) q.2 := ht
  have mZ := hm (vb bs 5, S.rG.2.1) (by simp [ChildSegs.termLin])
  have mC := hm (vb bs 9, S.H.chiW) (by simp [ChildSegs.termLin])
  have mK := hm (vb bs 4, 1 :: gen ^ S.logMem :: S.hs.map (gen ^ ·)) (by simp [ChildSegs.termLin])
  have mE := hm (sqE, expTabAllWords) (by simp [ChildSegs.termLin])
  have mV := hm (vb bs 11, S.kOut.point ++ List.replicate (qkeccakVarsCap - S.kOut.point.length) 0 ++
    S.kc.2.1) (by simp [ChildSegs.termLin])
  have mT := hm (vb bs 14, S.ctab) (by simp [ChildSegs.termLin, ChildSegs.ctab])
  have mO := hm (vb bs 6, S.oodZ) (by simp [ChildSegs.termLin])
  obtain ⟨hτ9, hτ22, -, -, -, hopl, hkpl, -⟩ := S.keccak_facts hbl
  obtain ⟨-, hkO, -⟩ := S.keccak_run hbl
  have hd := S.d_bounds hbl
  obtain ⟨-, -, -, -, hpl, -⟩ := S.gkr_inv hbl
  obtain ⟨hbus, -, -⟩ := S.H_spec hbl
  obtain ⟨hhs, -⟩ := S.hs_bounds hbl
  have hwl := S.w_point_length
  -- `z_vals`
  have mV' := Main.readsAt_append'.mp mV
  have mOp : ReadsAt rd (ptr (vb bs 11)) S.kOut.point := (Main.readsAt_append'.mp mV'.1).1
  have mKp : ReadsAt rd (ptr (vb bs 11) * gen ^ qkeccakVarsCap) S.kc.2.1 := by
    have := mV'.2
    rwa [List.length_append, List.length_replicate,
      show S.kOut.point.length + (qkeccakVarsCap - S.kOut.point.length) = qkeccakVarsCap by
        simp only [qkeccakVarsCap]; omega] at this
  -- the exponent table
  have hexp : ExpTables rd (ptr sqE) := ((expTabAll_iff rd _).2 fun o ho ↦ by
    have := mE o (by rw [length_expTabAllWords]; exact ho)
    simpa [expTabAllWords] using this).1
  -- `certify_placement`'s offsets
  have hP := Tables.cp_out_ctx (show Tables.cpOut S.logMem S.hs
    [gen ^ Tables.stackTotal (columnKappas S.logMem Tables.guestLogBytecode S.hs), ptr e293]
    (Tables.cpOwn S.logMem S.hs e10 e11 e136 e137 e293) from ⟨_, _, _, _, _, rfl, rfl⟩) hcp
  have hct := S.H_tctx hbl mZ mC
  have hτ : S.τ = S.hs.getD opKeccak 0 := by
    show S.layout.tableLogHeights.getD opKeccak 0 = _; rw [S.layout_heights]
  have hsl := S.stackLog_eq' hbl
  have hμ : S.μs = S.layout.stackLog := rfl
  simp only [TermPre, ChildSegs.termArgsH, termArgs, termBases]
  rw [S.layout_logMemory, S.layout_heights]
  refine ⟨hct, hP, committed_lt29 (S.stackTotal_le hbl), ?_, ?_, S.hmu28,
    by have := S.h16; omega, S.h32, ?_, heights_length6 S.rowsN S.hrowsL, hhs, by trivial, by rw [hτ],
    mK, gTabs_of_exp hexp, by trivial, by rw [hkO], ?_, mOp, ?_, mKp,
    by rw [ChildSegs.ctab, ringCoefficients_length (by simp [S.rchs_length, ringMapWidth])
      (by simp [S.rchs_length, ringMapWidth])]; rfl, mT, hwl, ?_, ?_, S.oodZ_length, mO,
    by rw [hsl]⟩
  · rw [← S.layout_logMemory, ← S.layout_heights, S.hlayout]
    exact layoutOf_placements hbl _ _
  · rw [S.hlayout]; exact layoutOf_stackLog hbl _ _
  · rw [hbus]; show S.rG.2.1.length ≤ 40; omega
  · rw [hopl, Tables.qkeccakSlotBits_eq, hτ]
  · rw [hkpl, Tables.qkeccakSlotBits_eq, hτ]
  · unfold padPoint
    rw [hwl, show termPointCap = Whir.pointCap from rfl]; exact hpt
  · unfold padPoint
    rw [hwl, show termPointCap = Whir.pointCap from rfl, List.map_append, List.map_replicate,
      add_zero]
    exact hpt1

theorem regionL_of {L : Main.Layout} {q : ℕ × List E} (hq : q ∈ L) {i : ℕ} (h1 : q.1 ≤ i)
    (h2 : i < q.1 + q.2.length) : Main.RegionL L i := ⟨q, hq, h1, h2⟩

/-- **The terminal callee, entered, is a call on its honest words**: any property `Q` of a call of
`check_opening_terminal` on words `Lin` holding its precondition and its regions, at its honest
arguments. -/
theorem term_via (hbl : bytecode.length = 2 ^ 23) (bs : List ℕ) (sqE : ℕ)
    (pv : List (List E × Main.Layout)) (ht : ((S.kids bs sqE).getD 15 noKid pv).taken = true)
    (Q : String → Main.Layout → List E → (List E → Main.Layout → Prop) → Prop)
    (hQ : ∀ (Lin : Main.Layout) (B : TermBases),
      (∀ rd, Main.MemL rd Lin → TermPre rd S.layout S.bus S.claims S.kOut S.lam S.kc.2.1 S.ctab
        S.oodZ S.w.point (S.termArgsH B)) →
      (∀ i, TermRegion B S.bus.point.length S.nT (S.layout.tableLogHeights.getD opKeccak 0)
        S.layout.stackLog i → Main.RegionL Lin i) →
      Q "check_opening_terminal" Lin (S.termArgsH B) (Returns [])) :
    Q ((S.kids bs sqE).getD 15 noKid pv).f ((S.kids bs sqE).getD 15 noKid pv).Lin
      ((S.kids bs sqE).getD 15 noKid pv).args ((S.kids bs sqE).getD 15 noKid pv).Out := by
  have hok : S.termOk pv := @of_decide_eq_true _ (Classical.propDecidable _) ht
  have hLin : ((S.kids bs sqE).getD 15 noKid pv).Lin =
      (ChildSegs.cpRes pv).2 ++ (ChildSegs.osRes pv).2 ++ S.termLin bs sqE := by
    show @ite _ _ (Classical.propDecidable _) _ _ = _
    rw [@ite_pos' _ _ (Classical.propDecidable _) _ _ hok]
  obtain ⟨⟨e10, e11, e136, e137, e293, -, hL3⟩, ⟨pb, pb1, -, hL14⟩⟩ := hok
  have hargs : ((S.kids bs sqE).getD 15 noKid pv).args =
      S.termArgsH (termBases bs sqE e293 pb pb1) := by
    show termArgs (ChildSegs.termB bs sqE pv) _ _ _ _ _ _ _ _ _ _ = _
    simp only [ChildSegs.termB, ChildSegs.termBs, hL3, hL14]
    rfl
  rw [hLin, hargs, hL3, hL14]
  show Q "check_opening_terminal" _ _ (Returns [])
  have hd := S.d_bounds hbl
  obtain ⟨-, -, -, -, hpl, -⟩ := S.gkr_inv hbl
  obtain ⟨hbus, -, -⟩ := S.H_spec hbl
  have hbp : S.bus.point.length = S.d := by rw [hbus]; exact hpl
  obtain ⟨-, -, -, -, -, hopl, hkpl, -⟩ := S.keccak_facts hbl
  have hwl := S.w_point_length
  have hμ28 : S.μs ≤ 28 := S.hmu28
  refine hQ _ (termBases bs sqE e293 pb pb1) (fun rd hm ↦ ?_) (fun i hi ↦ ?_)
  · obtain ⟨h12, hT⟩ := Main.memL_append.mp hm
    obtain ⟨hC, hO⟩ := Main.memL_append.mp h12
    exact S.termPre hbl bs sqE e10 e11 e136 e137 e293 pb pb1 hC
      (hO (pb, S.w.point ++ List.replicate (Whir.pointCap - S.μs) 0) (by simp))
      (hO (pb1, S.w.point.map (1 + ·) ++ List.replicate (Whir.pointCap - S.μs) 1) (by simp)) hT
  · have hτl : S.layout.tableLogHeights.getD opKeccak 0 = S.τ := rfl
    simp only [TermRegion, termBases, hbp, hτl] at hi
    have hcl := S.chiW_length
    have hzl : (S.kOut.point ++ List.replicate (qkeccakVarsCap - S.kOut.point.length) 0 ++
        S.kc.2.1).length = 39 + (S.τ + 6) := by
      simp only [List.length_append, List.length_replicate, hopl, hkpl, qkeccakVarsCap]
      have := (S.keccak_facts hbl).2.1
      omega
    have hT : ∀ q ∈ S.termLin bs sqE, q ∈ Tables.cpOwn S.logMem S.hs e10 e11 e136 e137 e293 ++
        [(pb, S.w.point ++ List.replicate (Whir.pointCap - S.μs) 0),
          (pb1, S.w.point.map (1 + ·) ++ List.replicate (Whir.pointCap - S.μs) 1)] ++
        S.termLin bs sqE := fun q hq ↦ List.mem_append_right _ hq
    have hctl : S.ctab.length = 64 := by
      rw [ChildSegs.ctab, ringCoefficients_length (by simp [S.rchs_length, ringMapWidth])
        (by simp [S.rchs_length, ringMapWidth])]
    rcases hi with h | h | h | h | h | h | h | h | h | h | h
    · exact regionL_of (hT (vb bs 5, S.rG.2.1) (by simp [ChildSegs.termLin])) h.1 (by simp [hpl]; omega)
    · exact regionL_of (hT (vb bs 9, S.H.chiW) (by simp [ChildSegs.termLin])) h.1
        (by simp [hcl]; omega)
    · exact regionL_of (hT (vb bs 4, 1 :: gen ^ S.logMem :: S.hs.map (gen ^ ·))
        (by simp [ChildSegs.termLin])) h.1 (by simp [heights_length6 S.rowsN S.hrowsL, ChildSegs.hs]; omega)
    · exact regionL_of (q := (e293, (stackOffsets (Tables.cpKs S.logMem S.hs)).1.map (gen ^ ·)))
        (by simp [Tables.cpOwn]) h.1
        (by have : Tables.nCommittedCols = 94 := rfl
            simp [Tables.tb_stackOffsets_length, Tables.cpKs_length]; omega)
    · exact regionL_of (hT (sqE, expTabAllWords) (by simp [ChildSegs.termLin])) (by omega)
        (by simp [length_expTabAllWords]; omega)
    · exact regionL_of (hT (vb bs 11, S.kOut.point ++ List.replicate (qkeccakVarsCap -
        S.kOut.point.length) 0 ++ S.kc.2.1) (by simp [ChildSegs.termLin])) h.1 (by rw [hzl]; omega)
    · exact regionL_of (hT (vb bs 11, S.kOut.point ++ List.replicate (qkeccakVarsCap -
        S.kOut.point.length) 0 ++ S.kc.2.1) (by simp [ChildSegs.termLin])) (by omega)
        (by rw [hzl]; omega)
    · exact regionL_of (hT (vb bs 14, S.ctab) (by simp [ChildSegs.termLin, ChildSegs.ctab])) h.1
        (by rw [hctl]; omega)
    · exact regionL_of (q := (pb, S.w.point ++ List.replicate (Whir.pointCap - S.μs) 0))
        (by simp) h.1 (by simp [hwl, Whir.pointCap]; omega)
    · exact regionL_of (q := (pb1, S.w.point.map (1 + ·) ++ List.replicate (Whir.pointCap - S.μs) 1))
        (by simp) h.1 (by simp [hwl, Whir.pointCap]; omega)
    · exact regionL_of (hT (vb bs 6, S.oodZ) (by simp [ChildSegs.termLin])) h.1
        (by rw [S.oodZ_length]; exact h.2)

theorem bus_point_le34 (hbl : bytecode.length = 2 ^ 23) : S.bus.point.length ≤ 34 := by
  have hd := S.d_bounds hbl
  obtain ⟨-, -, -, -, hpl, -⟩ := S.gkr_inv hbl
  obtain ⟨hbus, -, -⟩ := S.H_spec hbl
  rw [hbus]; show S.rG.2.1.length ≤ 34; omega

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **The terminal on an honest child, entered, within `termBound`.** -/
theorem term_kidB (hbl : bytecode.length = 2 ^ 23) {κ : ℕ} (hκ : 6 ≤ κ) (W : VsWordsOs fs)
    (bs : List ℕ) (sqE : ℕ) (pv : List (List E × Main.Layout))
    (ht : ((S.kids bs sqE).getD 15 noKid pv).taken = true) :
    CompleteAtB fs cert κ ((S.kids bs sqE).getD 15 noKid pv).f
      ((S.kids bs sqE).getD 15 noKid pv).Lin ((S.kids bs sqE).getD 15 noKid pv).args
      ((S.kids bs sqE).getD 15 noKid pv).Out (termBound fs W.Beqc W.K15 W.Bcs W.Brs) :=
  S.term_via hbl bs sqE pv ht (fun f L a O ↦ CompleteAtB fs cert κ f L a O
    (termBound fs W.Beqc W.K15 W.Bcs W.Brs)) fun Lin B hpre hreg ↦
    check_opening_terminal_completeAtB κ hκ B Lin (nc := S.nT) (by have := S.nT_le hbl; omega) rfl
      (fun rd _ hm ↦ hpre rd hm) hreg (S.bus_point_le34 hbl) (S.fin hbl) W.hEqc W.hL15 W.hCsF
      W.hrs

/-- **The terminal on an honest child, entered, within `termBound` by a tree within its
weights.** -/
theorem term_kidBW (hbl : bytecode.length = 2 ^ 23) {κ : ℕ} (hκ : 6 ≤ κ) (W : VsWordsOs fs)
    (bs : List ℕ) (sqE : ℕ) (pv : List (List E × Main.Layout))
    (ht : ((S.kids bs sqE).getD 15 noKid pv).taken = true) :
    CompleteAtDTB fs cert κ ((S.kids bs sqE).getD 15 noKid pv).f
      ((S.kids bs sqE).getD 15 noKid pv).Lin ((S.kids bs sqE).getD 15 noKid pv).args
      ((S.kids bs sqE).getD 15 noKid pv).Out
      (fun t ↦ ∀ op, Budget.WeighsLe coreProgram (W.ωv op) (termWB W.toVsWords op) t)
      (termBound fs W.Beqc W.K15 W.Bcs W.Brs) :=
  S.term_via hbl bs sqE pv ht (fun f L a O ↦ CompleteAtDTB fs cert κ f L a O
    (fun t ↦ ∀ op, Budget.WeighsLe coreProgram (W.ωv op) (termWB W.toVsWords op) t)
    (termBound fs W.Beqc W.K15 W.Bcs W.Brs)) fun Lin B hpre hreg ↦
    check_opening_terminal_completeAtBW κ hκ B Lin (nc := S.nT) (by have := S.nT_le hbl; omega) rfl
      (fun rd _ hm ↦ hpre rd hm) hreg (S.bus_point_le34 hbl) (S.fin hbl) W.hEqc W.hL15 W.hCsF
      W.hrs W.ωv W.Weqc W.W15 W.Wst W.Wcs W.Wrsw W.hEqcW W.hStW W.hCsW W.h15W W.hrswW

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
