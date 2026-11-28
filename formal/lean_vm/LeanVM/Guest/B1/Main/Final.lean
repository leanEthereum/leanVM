/-
  LeanVM.Guest.B1.Main.Final

  B1 for `main` (TRIAGE #96): `main_sound_C`, a run of `main` establishes `NodeRelation` of
  what its decoders read.
-/

module

public import LeanVM.Guest.B1.Main.Holders
public import LeanVM.Guest.B1.Bits.Tables
import LeanVM.Guest.ValRef
import LeanVM.Guest.Batch.Split
import LeanVM.Guest.Data.ValNames.«main»

/-!
# `main`, soundly

`main_sound_C`: on a memory image whose public input cells hold `D`, under a call relation `C` that
unfolds and lies below `coreProgram.Rel`, given the callees' contracts on `C`'s calls with witness
functions (`CalleesWC`), a run of `main`'s body gives the decoded seed and statement of digest `D`
(`own_digest`), and `NodeRelation` of the decoded witness, for a stacked program of
`2^(BYTECODE_LOG + BYTECODE_SLOT_BITS)` words: every raw signature verifying and every declared
signature claim held (`signatures_held`), the DA digest the direct DA check's, zeros or a child's
(`da_rel`), every child's statement's deferred claim of the split program's shape and its proof
accepted by the deferring verifier for the child's decoded statement with its fresh claim
(`kid_sub`, `kid_digest`), and the deferred claim the leaf's zero point or the outcome of the
batching program on the children's stream (`aggregate_claims`' contract). `exponent_tables` is B1-a's
(`exponent_tables_holds`); every other deterministic callee is this family's.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {C : CallRel}

theorem deferOfCells_of {d : DeferredBytecodeClaim} (hl : d.bytecodePoint.length = bytecodeVars) :
    deferOfCells d.cells = d := by
  have hb : bytecodeVars = 25 := rfl
  unfold deferOfCells DeferredBytecodeClaim.cells
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl]
  simp

set_option maxRecDepth 100000 in
/-- `tabs = g_squares · g^178`'s word (`WIN_TAB_AT = 178`). -/
theorem word_g178 : word 365917469723852800 0 = gen ^ 178 := by
  rw [word_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

theorem length_readCells (rd : Reader) (p : E) (n : ℕ) : (readCells rd p n).length = n := by
  rw [readCells_eq_memRun, length_memRun]

/-- A stacked program of `2^(19 + BYTECODE_SLOT_BITS)` words has `2^19` instructions. -/
theorem ivc_bytecode {bytecode : List K} (h : bytecode.length = 2 ^ (bytecodeLog + bytecodeSlotBits)) :
    instructionVariableCount bytecode = bytecodeLog := by
  rw [instructionVariableCount, h, Nat.shiftRight_eq_div_pow, Nat.pow_add,
    Nat.mul_div_cancel _ (by positivity), Nat.log2_two_pow]

/-- Its deferred claims have `BYTECODE_VARS = 19 + SPLIT_LOG` coordinates. -/
theorem dvc_bytecode {bytecode : List K} (h : bytecode.length = 2 ^ (bytecodeLog + bytecodeSlotBits)) :
    deferredVariableCount bytecode = bytecodeVars := by
  rw [deferredVariableCount, ivc_bytecode h]
  rfl

theorem length_splitColumns' : (splitColumns tables).length = nSplit := by
  rw [Batch.length_splitColumns]

variable {rd : Reader} {σ : Val} {Kr : ℕ → KidRec}

instance : Nonempty KidRec :=
  ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, fun _ => 0, [], fun _ => 0, [], [], false, false⟩⟩

/-- **A child's proof**: its fresh claim at `child_fresh · g^(55c)`, of `19` coordinates and `36`
values, and the deferring verifier accepts its proof for the decoded child's statement under the
decoded seed with that fresh claim. -/
theorem kid_sub {bytecode : List K} (hbl : bytecode.length = 2 ^ (bytecodeLog + bytecodeSlotBits))
    {wX : List E → LeanXmss.Signature} {wS : E → Sphincs.Signature}
    {wD : List E → List E → LeanVM.Da.MatrixWitness} {wV : List E → Proof} {wA : List E → BatchingHints}
    (cw : CalleesWC bytecode C rd (σ (.n (val% «main» "byte_bits"))) wX wS wD wV wA) (MF : MainFacts C rd σ)
    (hK : ∀ c < lg σ 6, KidOk C rd σ c (Kr c))
    {rx rs : ℕ → ℕ} (hW : Writers rd (σ (.n (val% «main» "cover"))) (segsOf σ Kr) (LXS σ) (LSS σ) (slOf σ Kr rx rs))
    {c : ℕ}
    (hc : c < lg σ 6) :
    ((decKid rd σ wV c).freshClaim.point.length = bytecodeLog ∧
      (decKid rd σ wV c).freshClaim.values.length = nSplit) ∧
      ReadsAt rd (σ (.n (val% «main» "child_fresh")) * gen ^ (55 * c)) (decKid rd σ wV c).freshClaim.cells ∧
      verifyDeferred bytecode (decSeed σ) (statementDigest (decSeed σ) (kidStmt rd σ c))
        (decKid rd σ wV c).freshClaim (decKid rd σ wV c).proof = true := by
  have k := hK c hc
  obtain ⟨pi0, pi1, s0, s1, gsq, out, hargs, seed, pi, fresh, hs, hp, hfl, hvl, hfr, hvd⟩ :=
    cw.sub _ _ _ _ _ _ k.sub ⟨MF.exp, MF.win⟩
  rw [ivc_bytecode hbl] at hfl
  rw [length_splitColumns'] at hvl
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  have hseed : decSeed σ = seed := by
    unfold decSeed; rw [show σ (.n (val% «main» "fs_seed[0]")) = (digestHalves seed).1 by rw [← hs],
      show σ (.n (val% «main» "fs_seed[1]")) = (digestHalves seed).2 by rw [← hs], digestOfCells_scalars]
  have hpi : pi = statementDigest (decSeed σ) (kidStmt rd σ c) := by
    apply digestCells_inj
    rw [← kid_digest MF hK hW hc, digestCells, ← hp]
  have hfresh : (decKid rd σ wV c).freshClaim = fresh := by
    show freshOfCells (readCells rd (σ (.n (val% «main» "child_fresh")) * gen ^ (55 * c)) 55) = fresh
    rw [readCells_of_readsAt hfr (length_freshCells hfl hvl), freshOfCells_cells hfl hvl]
  have hargs : subArgs rd σ c = [(Kr c).p0, (Kr c).p1, σ (.n (val% «main» "fs_seed[0]")), σ (.n (val% «main» "fs_seed[1]")), σ (.n (val% «main» "g_squares")),
      σ (.n (val% «main» "child_fresh")) * gen ^ (55 * c)] := by
    unfold subArgs
    rw [cellAt_eq_memAt, memAt_of_load k.pi0, memAt_of_load k.pi1]
  refine ⟨by rw [hfresh]; exact ⟨hfl, hvl⟩, by rw [hfresh]; exact hfr, ?_⟩
  rw [hfresh, ← hpi, hseed]
  show verifyDeferred bytecode seed pi fresh (wV (subArgs rd σ c)) = true
  rw [hargs]
  exact hvd

/-- `DaDigestHeld` from its two cases. -/
theorem daDigestHeld_of {s : NodeStatement} {w : NodeWitness}
    (h1 : ∀ c m, w.daMatrix = some (c, m) →
      s.claims.daDigest = daClaimDigest c ∧ m.Opens c.daRoot c.membershipChallenge)
    (h2 : w.daMatrix = none → s.claims.daDigest = zeroDigest ∨
      ∃ c ∈ w.children, c.statement.claims.daDigest = s.claims.daDigest) :
    DaDigestHeld s w := by
  unfold DaDigestHeld
  split
  · rename_i c m hd
    exact h1 c m hd
  · rename_i hd
    exact h2 hd

/-- **`main`, soundly, its witness decoded, under a call relation `C`** that unfolds and lies
below `coreProgram.Rel` (TRIAGE #96), given the callees' contracts on `C`'s calls, for a stacked
program of `2^(19 + BYTECODE_SLOT_BITS)` words. -/
theorem main_sound_C {bytecode : List K}
    (hbl : bytecode.length = 2 ^ (bytecodeLog + bytecodeSlotBits)) (hm : MemOk rd) (hCu : Unfolds rd C)
    (hle : CallRel.Le C (coreProgram.Rel rd))
    {wX : List E → LeanXmss.Signature} {wS : E → Sphincs.Signature}
    {wD : List E → List E → LeanVM.Da.MatrixWitness} {wV : List E → Proof} {wA : List E → BatchingHints}
    (cw : CalleesWC bytecode C rd (σ (.n (val% «main» "byte_bits"))) wX wS wD wV wA) {D : Digest}
    (hp0 : LoadHolds rd 1 0 (digestHalves D).1) (hp1 : LoadHolds rd 1 1 (digestHalves D).2)
    (hb : Stmt.HoldsList C rd σ (fn% «main»).body False (fun rs => rs = [])) :
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
  have hdv := dvc_bytecode hbl
  -- the statement's digest
  have hdig : statementDigest (decSeed σ) (decStmt σ rd) = D := by
    apply digestCells_inj
    rw [← hown, loadHolds_unique MF.pub.1 hp0, loadHolds_unique MF.pub.2 hp1]
    rfl
  refine ⟨hdig, signatures_held MF hK hW hm cw, ?_, ?_, ?_⟩
  · -- the DA digest
    obtain ⟨hsome, hnone⟩ := da_rel MF cw
    exact daDigestHeld_of hsome hnone
  · -- the children
    intro ch hch
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hch
    rw [List.mem_range, nKids_eq] at hc
    refine ⟨?_, (kid_sub hbl cw MF hK hW hc).2.2⟩
    show (deferOfCells (readCells rd (σ (.n (val% «main» "child_carried")) * gen ^ (26 * c)) 26)).bytecodePoint.length = _
    rw [deferOfCells_point (length_readCells _ _ _), hdv]
  · -- the deferred claim
    unfold DeferredClaimBatched
    by_cases h6 : lg σ 6 = 0
    · have hnil : (decWit σ rd wX wS wD wV wA).children = [] := by
        show (List.range (nKids σ)).map _ = []
        rw [nKids_eq, h6]; rfl
      rw [ite_pos' hnil]
      show (deferOfCells (readCells rd (σ (.n (val% «main» "defer_stmt"))) 26)).bytecodePoint = _
      rw [hdv]
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
      have hwin : WinTabs rd (σ (.n (val% «main» "s63.e.s0#1"))) := by
        rw [htab, word_g178]; exact winTabs_of_expWinTab MF.win
      obtain ⟨out, hol, hor, hb⟩ := cw.agg _ _ _ _ _ _ hcall hwin (lg σ 6) (by omega) MF.kids.2
        MF.kids.1
      have hdef : (decStmt σ rd).deferredClaim = out := by
        show deferOfCells (readCells rd (σ (.n (val% «main» "defer_stmt"))) 26) = out
        rw [readCells_of_readsAt hor (by simp [DeferredBytecodeClaim.cells, hol, bytecodeVars]),
          deferOfCells_of hol]
      have hch : (decWit σ rd wX wS wD wV wA).children = (List.range (lg σ 6)).map (decKid rd σ wV) := by
        show (List.range (nKids σ)).map _ = _
        rw [nKids_eq]
      have hh : (decWit σ rd wX wS wD wV wA).batchingHints = wA [σ (.n (val% «main» "meta[6]")),
          σ (.n (val% «main» "child_pi")), σ (.n (val% «main» "child_fresh")),
          σ (.n (val% «main» "child_carried")), σ (.n (val% «main» "defer_stmt")),
          σ (.n (val% «main» "s63.e.s0#1"))] := rfl
      rw [hdef, hch, hh]
      refine hb _ (by rw [List.length_map, List.length_map, List.length_range]) fun c hc => ?_
      simp only [List.length_map, List.length_range] at hc
      simp only [List.getElem_map, List.getElem_range]
      obtain ⟨hfl, hfr, -⟩ := kid_sub hbl cw MF hK hW hc
      have k := hK c hc
      have hkd := kid_digest MF hK hW hc
      simp only [digestCells, List.cons.injEq, and_true] at hkd
      refine ⟨hfl, ?_, ?_, ?_, hfr, ?_⟩
      · show (deferOfCells (readCells rd (σ (.n (val% «main» "child_carried")) * gen ^ (26 * c)) 26)).bytecodePoint.length = _
        exact deferOfCells_point (length_readCells _ _ _)
      · show LoadHolds rd (σ (.n (val% «main» "child_pi"))) (2 * c)
          (digestHalves (statementDigest (decSeed σ) (kidStmt rd σ c))).1
        rw [← hkd.1]; exact k.pi0
      · show LoadHolds rd (σ (.n (val% «main» "child_pi"))) (2 * c + 1)
          (digestHalves (statementDigest (decSeed σ) (kidStmt rd σ c))).2
        rw [← hkd.2]; exact k.pi1
      · show ReadsAt rd _ (deferOfCells (readCells rd (σ (.n (val% «main» "child_carried")) * gen ^ (26 * c)) 26)).cells
        rw [readCells_of_readsAt k.defreads k.deflen, deferOfCells_cells k.deflen]
        exact k.defreads

end
end LeanVM.Guest.B1.Main
