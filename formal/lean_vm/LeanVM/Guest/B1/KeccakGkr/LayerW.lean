/-
  LeanVM.Guest.B1.KeccakGkr.LayerW

  What a `keccak_layer` specialization's relation establishes (`LayerW`), and that it is the
  layer's meaning: the specification's layer runs, and the next claim's record is written.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.PackChain
public import LeanVM.Guest.B1.KeccakGkr.Algebra
public import LeanVM.Guest.B1.KeccakGkr.LocalRounds

/-!
# A layer, from its facts

`LayerW` collects, for one reading of `keccak_layer`'s arguments (the claim `c`, `y`, the waiting
word `w`), the facts its body gives (G:2694-2875): the product read, the projection check, the
squeeze after the product, the instance weights written, the pack rounds' records and calls, the
eleven position rounds, `t`, the final check, the squeeze `β` and the next claim's record.
`layer_of_w` turns them into the meaning: `layer_runsTo` with `pack_chain`'s messages, and the
record of `layerClaim` (`batch_factor`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr

@[expose] public section

/-- The facts of a `keccak_layer` specialization's body, for one reading of its arguments. -/
structure LayerW (first : ℕ) (rd : Reader) (f0 f1 f2 f3 f4 cur sg rg claim out iota : E)
    (rets : List E) (c : KeccakClaim) (w : E) : Type where
  prod : List E
  hprodL : prod.length = productBits
  hprod : ReadsAt rd cur prod
  hproj : projectedOf c prod + iota * sumE c.mu = c.value
  nonce : E
  hnonce : LoadHolds rd cur productBits nonce
  hgrind : ((plainStart first [f0, f1, f2, f3, f4] w).absorbAll prod dsObserve).GrindOk sGrindBits
    nonce
  sv : E
  capS : List E
  hsq : layerSq (plainStart first [f0, f1, f2, f3, f4] w) prod nonce = (sv, ⟨capS, []⟩)
  hmuOut : ∀ i < 16, LoadHolds rd out (6 + i) ((keccakInstanceWeights sv).getD i 0)
  hkapOut : LoadHolds rd out 1 (sumE (keccakInstanceWeights sv))
  rc : E
  pt : E
  pp : E
  hpp : LoadHolds rd claim 2 pp
  tb : E
  h0 : RoundRec rd rc 0 capS (cur * gen ^ (productBits + 1)) (polyEval prod sv) 1
  hloop : IsInK (1 + sg) ∧
    (1 + sg ≠ 0 → coreProgram.Rel rd (packLoopName first) [1, sg, rc, pp, pt, tb] [])
  hrem : IsInK (1 + rg) ∧
    (1 + rg ≠ 0 → coreProgram.Rel rd (remLoopName first) [1, rg, rc * sg, pp * sg ^ 8, tb,
      pt * sg ^ 8] [])
  capL : List E
  curL : E
  vL : E
  scL : E
  hlast : RoundRec rd (rc * sg * rg) 0 capL curL vL scL
  msgs : List (E × E × E)
  hmsgsL : msgs.length = keccakLocalBits
  hmsgs : ReadsAt rd curL (msgs.flatMap fun m ↦ [m.1, m.2.1, m.2.2])
  loc : E
  locPt : List E
  vR : E
  capR : List E
  hlocal : localRunF msgs vL ⟨capL, []⟩ = ((locPt, vR), ⟨capR, []⟩)
  hloc : ReadsAt rd loc locPt
  t0 : E
  t1 : E
  t2 : E
  ht : ReadsAt rd (curL * gen ^ 33) [t0, t1, t2]
  hfin : scL * dot ((eqKernel locPt).take keccakBits) c.weights *
    (sumE (keccakInstanceWeights sv) * t0 + (sumE (keccakInstanceWeights sv) + t1) * t2) = vR
  beta : E
  capB : List E
  hbeta : ((⟨capR, []⟩ : Fs).absorbAll [t0, t1, t2] dsObserve).squeeze = (beta, ⟨capB, []⟩)
  hout0 : LoadHolds rd out 0 (t0 + beta * (t1 + beta * t2))
  hout2 : LoadHolds rd out 2 pt
  hout4 : LoadHolds rd out 4 loc
  lo : E
  fl : E
  hout3 : LoadHolds rd out 3 lo
  hlanes : ReadsAt rd lo (lanesOut locPt beta)
  hout5 : LoadHolds rd out 5 fl
  hflips : ReadsAt rd fl (flipsOf (laterWeights (lanesOut locPt beta) (eqKernel (locPt.take 6))))
  hrets : rets = capB ++ [curL * gen ^ 36]

theorem lanesOut_length (loc : List E) (beta : E) : (lanesOut loc beta).length = 25 := by
  simp [lanesOut]

/-- **A layer, from its facts** (G:2694-2875 against V:1983-2019). -/
theorem layer_of_w {first : ℕ} (hf : first < 2) {rd : Reader}
    {f0 f1 f2 f3 f4 cur sg rg claim out iota : E} {rets : List E} {y step : ℕ} {c : KeccakClaim}
    {w : E} (hy32 : y < 32) (hsg : sg = gen ^ (y / krStep)) (hrg : rg = gen ^ (y % krStep))
    (hcr : ClaimRec rd (first = 1) claim c y) (hiota : iota = keccakIota (y + 3) step c)
    (W : LayerW first rd f0 f1 f2 f3 f4 cur sg rg claim out iota rets c w) :
    ∃ (xs : List E) (c' : KeccakClaim) (cap' : List E), ReadsAt rd cur xs ∧
      RunsTo (verifyKeccakLayer (y + 3) step c) (plainStart first [f0, f1, f2, f3, f4] w) xs c'
        ⟨cap', []⟩ ∧
      ClaimRec rd false out c' y ∧ rets = cap' ++ [cur * gen ^ xs.length] := by
  obtain ⟨-, hptL, -, -, -, ⟨pp', hpp', hppR⟩, -⟩ := hcr
  have epp : W.pp = pp' := loadHolds_unique W.hpp hpp'
  obtain ⟨msgsP, chs, hmL, hmR, hchR, hchL, hcurL, hrun1, hrun2⟩ :=
    pack_chain hf hsg hrg hy32 hptL (epp ▸ hppR) W.h0 W.hloop W.hrem W.hlast
  have hpack : packRunF c.point msgsP (polyEval W.prod W.sv) 1 ⟨W.capS, []⟩ =
      ((W.vL, W.scL, chs), ⟨W.capL, []⟩) := Prod.ext hrun1 hrun2
  have hsq1 : (layerSq (plainStart first [f0, f1, f2, f3, f4] w) W.prod W.nonce).1 = W.sv := by
    rw [W.hsq]
  have hsq2 : (layerSq (plainStart first [f0, f1, f2, f3, f4] w) W.prod W.nonce).2 = ⟨W.capS, []⟩ := by
    rw [W.hsq]
  have hP : layerPack c (plainStart first [f0, f1, f2, f3, f4] w) W.prod W.nonce msgsP =
      ((W.vL, W.scL, chs), ⟨W.capL, []⟩) := by
    rw [layerPack, hsq1, hsq2, hpack]
  have hL : layerLocal c (plainStart first [f0, f1, f2, f3, f4] w) W.prod W.nonce msgsP W.msgs =
      ((W.locPt, W.vR), ⟨W.capR, []⟩) := by
    rw [layerLocal, hP]; exact W.hlocal
  have hB : layerBeta c (plainStart first [f0, f1, f2, f3, f4] w) W.prod W.nonce msgsP W.msgs
      (W.t0, W.t1, W.t2) = (W.beta, ⟨W.capB, []⟩) := by
    rw [layerBeta, hL]; exact W.hbeta
  have hfin : LayerFinal c (plainStart first [f0, f1, f2, f3, f4] w) W.prod W.nonce msgsP W.msgs
      (W.t0, W.t1, W.t2) := by
    unfold LayerFinal
    rw [hsq1, hP, hL]
    exact W.hfin
  have hrun := layer_runsTo (y + 3) step c (plainStart first [f0, f1, f2, f3, f4] w) W.prod
    W.hprodL W.nonce W.hgrind msgsP (by rw [hmL, hptL]) W.msgs W.hmsgsL (W.t0, W.t1, W.t2)
    (by rw [← hiota]; exact W.hproj) hfin
  rw [hB] at hrun
  have hlocL : W.locPt.length = 11 := by
    have := localRunF_length W.msgs W.vL ⟨W.capL, []⟩
    rw [W.hlocal, W.hmsgsL] at this
    exact this
  have hc' : W.curL = cur * gen ^ (48 + 2 * y) := by
    rw [hcurL, mul_assoc, ← pow_add]; rfl
  refine ⟨_, _, W.capB, ?_, hrun, ?_, ?_⟩
  · simp only [List.append_assoc]
    rw [readsAt_append, readsAt_append, readsAt_append, readsAt_append, W.hprodL,
      List.length_singleton, flatMap_pairs_length, hmL, flatMap_triples_length, W.hmsgsL]
    refine ⟨W.hprod, fun k hk => ?_, ?_, ?_, ?_⟩
    · simp only [List.length_singleton, Nat.lt_one_iff] at hk
      subst hk
      rw [loadHolds_mul_gen_pow]
      exact W.hnonce
    · rw [mul_assoc, ← pow_add]
      exact hmR
    · rw [mul_assoc, ← pow_add, mul_assoc, ← pow_add, show productBits + (1 + 2 * y) = 48 + 2 * y by
        show 47 + (1 + 2 * y) = 48 + 2 * y; ring, ← hc']
      exact W.hmsgs
    · rw [mul_assoc, ← pow_add, mul_assoc, ← pow_add, mul_assoc, ← pow_add,
        show productBits + (1 + (2 * y + 3 * keccakLocalBits)) = 48 + 2 * y + 33 by
          show 47 + (1 + (2 * y + 3 * 11)) = 48 + 2 * y + 33; ring,
        pow_add, ← mul_assoc, ← hc']
      exact W.ht
  · simp only [ClaimRec, layerClaim, hsq1, hP, hL, hB, Bool.false_eq_true, ↓reduceIte]
    refine ⟨keccakInstanceWeights_length _, hchL, W.hout0, W.hkapOut, W.hmuOut, ⟨W.pt, W.hout2, hchR⟩,
      W.lo, lanesOut W.locPt W.beta, W.hout3, lanesOut_length _ _, W.hlanes, W.loc, W.fl, W.locPt,
      W.hout4, hlocL, W.hloc, W.hout5, ?_, ?_⟩
    · have := W.hflips
      rwa [laterWeights, ← batch_factor W.locPt hlocL W.beta] at this
    · rw [laterWeights, ← batch_factor W.locPt hlocL W.beta]
  · refine W.hrets.trans ?_
    rw [hc']
    simp only [List.length_append, List.length_cons, List.length_nil, W.hprodL,
      flatMap_pairs_length, hmL, flatMap_triples_length, W.hmsgsL]
    rw [mul_assoc, ← pow_add]
    congr 3

end
end LeanVM.Guest.B1.VerifySub
