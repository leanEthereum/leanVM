/-
  LeanVM.Guest.B1.Main.Final

  B1 for `main` (G:4482-4658; TRIAGE #96): `main_sound_w`, a run of `main` establishes `NodeRelation` of
  what its decoders read.
-/

module

public import LeanVM.Guest.B1.Main.Holders
public import LeanVM.Guest.Batch.Node
public import LeanVM.Guest.B1.Bits.Tables

/-!
# `main`, soundly

`main_sound_w bytecode : main_sound_Spec bytecode`: on a memory image whose public input cells hold
`D`, given the callees' contracts with witness functions (`CalleesW`), a run of `main`'s body gives
the decoded seed and statement of digest `D` (`own_digest`), and `NodeRelation` of the decoded witness:
the deferred claim's shape, every child's proof accepted by the deferring verifier for the child's
decoded statement (`kid_sub`, `kid_digest`), every raw signature verifying and every declared
signature claim held (`signatures_held`), the DA digest the direct DA check's, zeros or a child's (`da_rel`), and the
deferred claim the leaf's zero point or the batching of the
children's claims (`aggregate_claims`' contract). `exponent_tables` is B1-a's
(`exponent_tables_holds`); every other deterministic callee is this family's.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {C : CallRel}

theorem deferOfCells_of {d : DeferredClaim} (hl : d.bytecodePoint.length = bytecodeVars) :
    deferOfCells d.cells = d := by
  have hb : bytecodeVars = 23 := rfl
  unfold deferOfCells DeferredClaim.cells
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl]
  simp

set_option maxRecDepth 100000 in
/-- `tabs = g_squares · g^236`'s word. -/
theorem word_g236 : word 133823759239872512 0 = gen ^ 236 := by
  rw [word_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

theorem length_readCells (rd : Reader) (p : E) (n : ℕ) : (readCells rd p n).length = n := by
  rw [readCells_eq_memRun, length_memRun]

theorem log2_bytecode {bytecode : List K} (h : bytecode.length = 2 ^ bytecodeVars) :
    Nat.log2 bytecode.length = bytecodeVars := by
  rw [h, Nat.log2_two_pow]

variable {rd : Reader} {σ : Val} {Kr : ℕ → KidRec}

instance : Nonempty KidRec :=
  ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, fun _ => 0, [], fun _ => 0, [], [], false, false⟩⟩

/-- **A child's proof**: its fresh claim at `child_fresh · g^(24c)`, and the deferring verifier
accepts its proof for the decoded child's statement under the decoded seed. -/
theorem kid_sub {bytecode : List K} {wX : List E → LeanXmss.Signature} {wS : E → Sphincs.Signature}
    {wD : List E → List E → LeanVM.Da.MatrixWitness} {wV : List E → Proof} {wA : List E → BatchingHints}
    (cw : CalleesWC bytecode C rd (σ (.n 68)) wX wS wD wV wA) (MF : MainFacts C rd σ)
    (hK : ∀ c < lg σ 6, KidOk C rd σ c (Kr c))
    {rx rs : ℕ → ℕ} (hW : Writers rd (σ (.n 66)) (segsOf σ Kr) (LXS σ) (LSS σ) (slOf σ Kr rx rs))
    {c : ℕ}
    (hc : c < lg σ 6) :
    (decKid rd σ wV c).freshClaim.bytecodePoint.length = bytecodeVars ∧
      ReadsAt rd (σ (.n 410) * gen ^ (24 * c)) (DeferredClaim.cells (decKid rd σ wV c).freshClaim) ∧
      verifyDeferred bytecode (decSeed σ) (statementDigest (decSeed σ) (kidStmt rd σ c))
        (decKid rd σ wV c).freshClaim (decKid rd σ wV c).proof = true := by
  have k := hK c hc
  obtain ⟨pi0, pi1, s0, s1, gsq, out, hargs, seed, pi, fresh, hs, hp, hfl, hfr, hvd⟩ :=
    cw.sub _ _ _ _ _ _ k.sub ⟨MF.exp, MF.win⟩
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  have hseed : decSeed σ = seed := by
    unfold decSeed; rw [show σ (.n 47) = (digestHalves seed).1 by rw [← hs],
      show σ (.n 48) = (digestHalves seed).2 by rw [← hs], digestOfCells_scalars]
  have hpi : pi = statementDigest (decSeed σ) (kidStmt rd σ c) := by
    apply digestCells_inj
    rw [← kid_digest MF hK hW hc, digestCells, ← hp]
  have hlen : (DeferredClaim.cells fresh).length = 24 := by
    simp [DeferredClaim.cells, hfl, bytecodeVars]
  have hfresh : (decKid rd σ wV c).freshClaim = fresh := by
    show fixedOfCells (readCells rd (σ (.n 410) * gen ^ (24 * c)) 24) = fresh
    rw [readCells_of_readsAt hfr hlen, fixedOfCells_cells hfl]
  have hargs : subArgs rd σ c = [(Kr c).p0, (Kr c).p1, σ (.n 47), σ (.n 48), σ (.n 49),
      σ (.n 410) * gen ^ (24 * c)] := by
    unfold subArgs
    rw [cellAt_eq_memAt, memAt_of_load k.pi0, memAt_of_load k.pi1]
  refine ⟨by rw [hfresh]; exact hfl, by rw [hfresh]; exact hfr, ?_⟩
  rw [hfresh, ← hpi, hseed]
  show verifyDeferred bytecode seed pi fresh (wV (subArgs rd σ c)) = true
  rw [hargs]
  exact hvd

/-- **`main`, soundly, its witness decoded, under a call relation `C`** that unfolds and lies
below `coreProgram.Rel` (G:4482-4658, TRIAGE #96), given the callees' contracts on `C`'s calls. -/
theorem main_sound_C {bytecode : List K}
    (hbl : bytecode.length = 2 ^ bytecodeVars) (hm : MemOk rd) (hCu : Unfolds rd C) (hle : CallRel.Le C (coreProgram.Rel rd))
    {wX : List E → LeanXmss.Signature} {wS : E → Sphincs.Signature}
    {wD : List E → List E → LeanVM.Da.MatrixWitness} {wV : List E → Proof} {wA : List E → BatchingHints}
    (cw : CalleesWC bytecode C rd (σ (.n 68)) wX wS wD wV wA) {D : Digest}
    (hp0 : LoadHolds rd 1 0 (digestHalves D).1) (hp1 : LoadHolds rd 1 1 (digestHalves D).2)
    (hb : Stmt.HoldsList C rd σ Data.core0.body False (fun rs => rs = [])) :
    statementDigest (decSeed σ) (decStmt σ rd) = D ∧
      NodeRelation bytecode (decSeed σ) (decStmt σ rd) (decWit σ rd wX wS wD wV wA) := by
  have MF := main_facts hCu hle hm exponent_tables_holds (fun _ h => ⟨_, cw.xmss _ h⟩) (σ := σ) hb
  obtain ⟨Kr, hK⟩ : ∃ Kr : ℕ → KidRec, ∀ c < lg σ 6, KidOk C rd σ c (Kr c) := by
    have hex : ∀ c, c < lg σ 6 → ∃ k : KidRec, KidOk C rd σ c k := kid_rec hm MF
    choose! Kr hK using hex
    exact ⟨Kr, hK⟩
  obtain ⟨rx, rs, hrx, hrs⟩ := raw_slots MF
  have hW := writers MF hK hrx hrs
  have hown := own_digest MF
  have hlog := log2_bytecode hbl
  -- the statement's digest
  have hdig : statementDigest (decSeed σ) (decStmt σ rd) = D := by
    apply digestCells_inj
    rw [← hown, loadHolds_unique MF.pub.1 hp0, loadHolds_unique MF.pub.2 hp1]
    rfl
  have hdlen : (readCells rd (σ (.n 437)) 24).length = 24 := length_readCells _ _ _
  refine ⟨hdig, nodeRel_iff.mpr ⟨?_, ?_, signatures_held MF hK hW hm cw, ?_, ?_⟩⟩
  · -- the deferred claim's shape
    show (deferOfCells (readCells rd (σ (.n 437)) 24)).bytecodePoint.length = _
    rw [deferOfCells_point hdlen, hlog]
  · -- the children
    intro ch hch
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hch
    rw [List.mem_range, nKids_eq] at hc
    refine ⟨?_, (kid_sub cw MF hK hW hc).2.2⟩
    show (deferOfCells (readCells rd (σ (.n 416) * gen ^ (24 * c)) 24)).bytecodePoint.length = _
    rw [deferOfCells_point (length_readCells _ _ _), hlog]
  · -- the DA digest
    obtain ⟨hsome, hnone⟩ := da_rel MF cw
    cases hd : (decWit σ rd wX wS wD wV wA).daMatrix with
    | none => exact hnone hd
    | some p => exact hsome p.1 p.2 hd
  · -- the deferred claim
    by_cases h6 : lg σ 6 = 0
    · have hnil : (decWit σ rd wX wS wD wV wA).children = [] := by
        show (List.range (nKids σ)).map _ = []
        rw [nKids_eq, h6]; rfl
      rw [ite_pos' hnil]
      show (deferOfCells (readCells rd (σ (.n 437)) 24)).bytecodePoint = _
      rw [hlog]
      unfold deferOfCells
      simp only
      apply List.ext_getElem (by simp [length_readCells, bytecodeVars])
      intro i h1 h2
      simp only [List.getElem_take, List.getElem_replicate]
      simp only [List.length_replicate] at h2
      simp only [readCells, List.getElem_map, List.getElem_range]
      exact memAt_of_load (MF.leaf h6 i (by simp [bytecodeVars] at h2; omega))
    · have hne : (decWit σ rd wX wS wD wV wA).children ≠ [] := by
        show (List.range (nKids σ)).map _ ≠ []
        rw [nKids_eq]
        simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
        exact h6
      rw [ite_neg' hne]
      obtain ⟨htab, hcall⟩ := MF.agg h6
      have hwin : WinTabs rd (σ (.n 465)) := by
        rw [htab, word_g236]; exact winTabs_of_expWinTab MF.win
      obtain ⟨out, hol, hor, hb⟩ := cw.agg _ _ _ _ _ _ hcall hwin (lg σ 6) (by omega) MF.kids.2
        MF.kids.1
      have hdef : (decStmt σ rd).deferredClaim = out := by
        show deferOfCells (readCells rd (σ (.n 437)) 24) = out
        rw [readCells_of_readsAt hor (by simp [DeferredClaim.cells, hol, bytecodeVars]),
          deferOfCells_of hol]
      have hch : (decWit σ rd wX wS wD wV wA).children = (List.range (lg σ 6)).map (decKid rd σ wV) := by
        show (List.range (nKids σ)).map _ = _
        rw [nKids_eq]
      rw [hdef, hch]
      refine hb _ (by simp) fun c hc => ?_
      simp only [List.length_map, List.length_range] at hc
      simp only [List.getElem_map, List.getElem_range]
      obtain ⟨hfl, hfr, -⟩ := kid_sub cw MF hK hW hc
      have k := hK c hc
      have hkd := kid_digest MF hK hW hc
      simp only [digestCells, List.cons.injEq, and_true] at hkd
      refine ⟨hfl, ?_, ?_, ?_, hfr, ?_⟩
      · show (deferOfCells (readCells rd (σ (.n 416) * gen ^ (24 * c)) 24)).bytecodePoint.length = _
        exact deferOfCells_point (length_readCells _ _ _)
      · show LoadHolds rd (σ (.n 404)) (2 * c)
          (digestHalves (statementDigest (decSeed σ) (kidStmt rd σ c))).1
        rw [← hkd.1]; exact k.pi0
      · show LoadHolds rd (σ (.n 404)) (2 * c + 1)
          (digestHalves (statementDigest (decSeed σ) (kidStmt rd σ c))).2
        rw [← hkd.2]; exact k.pi1
      · show ReadsAt rd _ (deferOfCells (readCells rd (σ (.n 416) * gen ^ (24 * c)) 24)).cells
        rw [readCells_of_readsAt k.defreads k.deflen, deferOfCells_cells k.deflen]
        exact k.defreads

/-- **`main`, soundly, its witness decoded** (`coreProgram.Rel`'s instance of `main_sound_C`). -/
theorem main_sound_w (bytecode : List K) :
    main_sound_Spec bytecode := by
  intro hbl rd hm wX wS wD wV wA cw D σ hp0 hp1 hb
  exact main_sound_C hbl hm (unfolds_rel rd) (fun _ _ _ h => h)
    ⟨cw.xmss, fun p h hb => cw.sphincs p _ h hb, cw.da, cw.sub, cw.agg⟩ hp0 hp1 hb

end
end LeanVM.Guest.B1.Main
