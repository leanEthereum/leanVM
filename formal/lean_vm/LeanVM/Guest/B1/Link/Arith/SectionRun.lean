/-
  LeanVM.Guest.B1.Link.Arith.SectionRun

  `linkSecStatement` from the two runs' soundness instead of every atom of the section.
-/

module

public import LeanVM.Guest.B1.Link.Arith.Section

/-!
# The link section's values from its runs

`linkSecProgram`, `linkSecRow` and `linkSecStatement` use the section's atoms only through
`exec_eval` on the two runs (`runP`, `runR`) and through the twelve stores at `shifts`.
`LinkSecRuns rd σ`: the two runs are sound at `(rd, σ)` (`TrieSound`). **`linkSecStatementRun`**:
`linkSecStatement`'s conclusions from it, the shift coefficients as the values the stores write
(`shiftStores`' values), not as the words read at `shifts`.
-/

namespace LeanVM.Guest.B1.Link.Arith

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Protocol.Verifier LeanVM.Protocol.Link

@[expose] public section

/-- **The two runs are sound** at `(rd, σ)`. -/
def LinkSecRuns (rd : Reader) (σ : Val) : Prop := TrieSound rd σ runP ∧ TrieSound rd σ runR

section

variable {rd : Reader} {σ : Val} {v : LinkIn E}

theorem out_evalP' {t : Trie} (hT : TrieSound rd σ t) (h : IRReads rd σ v)
    {n : ℕ} {g : Ex} (hok : outOk 10010 t n g) : σ (.n n) = g.eval (envOf v) := by
  rw [← symOf_eval hT n, eval_congr (ρ' := envOf v ∘ ren) (fun i hi ↦ ren_reads h i (by simpa using hi))
    _ hok.1, ← eval_rename, eval_eq_of_norm hok.2]

theorem out_evalR' {t : Trie} (hT : TrieSound rd σ t) (h : IRAgree rd σ v)
    {n : ℕ} {g : Ex} (hok : outOk 20000 t n g) : σ (.n n) = g.eval (envOf v) := by
  rw [← symOf_eval hT n, eval_congr (ρ' := envOf v ∘ ren) (fun i hi ↦ ren_all h i (by simpa using hi))
    _ hok.1, ← eval_rename, eval_eq_of_norm hok.2]

/-- `linkSecProgram` from `runP`'s soundness. -/
theorem linkSecProgramRun (hT : TrieSound rd σ runP) (h : IRReads rd σ v) :
    σ (.n 764) = gClaim v ∧ σ (.n 967) = (gProgram v).1 ∧ σ (.n 1044) = (gProgram v).2 ∧
      σ (.n 1049) = gYMem v ∧ σ (.n 1057) = gXBc v ∧ σ (.n 1058) = gPFp v := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := secP_norm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [out_evalP' hT h p1, ← gClaim_eval]
  · rw [out_evalP' hT h p2, ← gProgram_eval1]
  · rw [out_evalP' hT h p3, ← gProgram_eval2]
  · rw [out_evalP' hT h p4, ← gYMem_eval]
  · rw [out_evalP' hT h p5, ← gXBc_eval]
  · rw [out_evalP' hT h p6, ← gPFp_eval]

/-- `linkSecRow` from `runR`'s soundness, the shift coefficients as the stored values. -/
theorem linkSecRowRun (hT : TrieSound rd σ runR) (h : IRAgree rd σ v) :
    σ (.n 2846) = gCoef v ∧ σ (.n 2655) = gBase v ∧ σ (.n 2890) = gRest v ∧
      σ (.n 2733) = gCertW v ∧ σ (.n 2891) = gCertW v * v.cert ∧
      ∀ s < 12, σ (.n (shiftStores.getD s (0, 0)).2) = gShift v s := by
  obtain ⟨b1, b2⟩ := secR_base
  obtain ⟨c1, c2⟩ := secR_cert
  refine ⟨?_, ?_, ?_, ?_, ?_, fun s hs ↦ ?_⟩
  · rw [out_evalR' hT h secR_coef, ← gCoef_eval]
  · rw [out_evalR' hT h b1, ← gBase_eval]
  · rw [out_evalR' hT h b2, ← gRest_eval]
  · rw [out_evalR' hT h c1, ← gCertW_eval]
  · rw [out_evalR' hT h c2, Ex.eval_mul', ← gCertW_eval]
    rfl
  · rw [out_evalR' hT h (secR_shifts s hs).2, ← gShift_eval v s hs]

end

/-- **The link section's values are `linkTail`'s, from its runs** (`linkSecStatement` with `LinkSecRuns` for
the section's atoms, the shift coefficients the values the stores at `shifts` write). -/
theorem linkSecStatementRun (rd : Reader) (σ : Val) (layout : Layout) (chunks : Chunks) (theta0 : E)
    (drawn r : List E) (m1 : E) (fresh splitv chi qPoint message : List E) (hT : LinkSecRuns rd σ)
    (hr : IRReads rd σ (tailIn layout chunks theta0 drawn r m1 fresh splitv chi qPoint message))
    (hs : TailShape layout drawn fresh splitv qPoint message)
    (hlb : layout.logBytecode = guest_const% BYTECODE_LOG) :
    let L := tailLets layout chunks theta0 drawn r m1 fresh (Split.ofColumns tables splitv) qPoint
    let R := tailRowSide layout chunks theta0 drawn r m1 fresh (Split.ofColumns tables splitv) chi
      qPoint message
    σ (.n 764) = indexClaim layout chunks drawn ∧ σ (.n 967) = L.program ∧
    σ (.n 1044) = L.frameProgram ∧ σ (.n 1049) = L.yMem ∧ σ (.n 1057) = L.xBc ∧
    σ (.n 1058) = L.pFp ∧ σ (.n 2846) = R.coef ∧ σ (.n 2655) = R.base ∧
    σ (.n 2890) = prodE (qPoint.map (1 + ·)) * R.base ∧ σ (.n 2733) = R.certWeight ∧
    σ (.n 2891) = R.certWeight * L.cert ∧ ∀ s < 12, σ (.n (shiftStores.getD s (0, 0)).2) = R.shifts.getD s 0 := by
  have hclaim := claimIdentity layout chunks theta0 drawn r m1 fresh splitv chi qPoint message hlb
  have hprog := programIdentity layout chunks theta0 drawn r m1 fresh splitv chi qPoint message hs
  have hside := sideIdentity layout chunks theta0 drawn r m1 fresh splitv chi qPoint message hs
  have hrow := rowIdentity layout chunks theta0 drawn r m1 fresh splitv chi qPoint message hs
  have hterm := terminalIdentity layout chunks theta0 drawn r m1 fresh splitv chi qPoint message hs
  dsimp only at hprog hside hrow hterm ⊢
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := linkSecProgramRun hT.1 hr
  have hag : IRAgree rd σ (tailIn layout chunks theta0 drawn r m1 fresh splitv chi qPoint message) :=
    { hr with
      xBc := p5.trans hside.2.1
      pFp := p6.trans hside.2.2
      yMem := p4.trans hside.1 }
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := linkSecRowRun hT.2 hag
  refine ⟨p1.trans hclaim, p2.trans (congrArg Prod.fst hprog), p3.trans (congrArg Prod.snd hprog),
    p4.trans hside.1, p5.trans hside.2.1, p6.trans hside.2.2, r1.trans hrow.1, r2.trans hrow.2.2.2,
    r3.trans hterm.1, r4.trans hrow.2.2.1, r5.trans (by rw [hrow.2.2.1]; rfl), fun s hsl ↦ ?_⟩
  rw [r6 s hsl, ← hrow.2.1, gShifts_getD _ hsl]

end

end LeanVM.Guest.B1.Link.Arith
