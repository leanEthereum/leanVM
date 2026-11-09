/-
  LeanVM.Guest.B1.KeccakGkr.VkSpec

  `verifyKeccak` (V:2061-2087) as a run on the carried sponge, from its parts.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerSpec
public import LeanVM.Protocol.Keccak.SlotWeights

/-!
# `verify_keccak`'s specification on the carried sponge

* `runsTo_sumcheck3`: `sumcheck v 3 (replicate n none)` is `plainRun` (`keccak_plain_rounds`);
* `runsTo_keccakLayers`: the layers, one after the other;
* `vk_runsTo`: `keccakSeg` runs, reading the committed outputs' value, the layers' words, the
  three openings' rounds, the word and the slices, once its two checks hold.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr


@[expose] public section

/-- **Plain rounds of degree two** are `plainRun`. -/
theorem runsTo_sumcheck3 :
    ∀ (ms : List (E × E)) (v : E) (s : Fs),
      RunsTo (sumcheck v 3 (List.replicate ms.length none)) s (ms.flatMap fun m ↦ [m.1, m.2])
        ((plainRun ms v s).1, (plainRun ms v s).2.1) (plainRun ms v s).2.2
  | [], v, s => runsTo_ret _ _
  | (c0, c2) :: ms, v, s => by
    have hmsg : RunsTo (sumcheckRoundPoly 3 v none) s [c0, c2]
        [c0, v + sumE [c2], c2] ((s.absorb c0 dsObserve).absorb c2 dsObserve) := by
      have h0 := runsTo_readE s c0
      have h1 := runsTo_readN (s.absorb c0 dsObserve) [c2]
      have h2 := h1.bind (f := fun tail ↦ (pure (c0 :: (v + sumE tail) :: tail) : VerifierProgram
          (List E)))
        (runsTo_ret _ _)
      have h3 := h0.bind (f := fun constant ↦ VerifierProgram.readScalars 1 >>= fun tail ↦
        (pure (constant :: (v + sumE tail) :: tail) : VerifierProgram (List E))) h2
      simpa [sumcheckRoundPoly, Fs.absorbAll] using h3
    set q := ((s.absorb c0 dsObserve).absorb c2 dsObserve).squeeze with hq
    have hs := runsTo_sampleE ((s.absorb c0 dsObserve).absorb c2 dsObserve)
    rw [← hq] at hs
    have hev : polyEval [c0, v + sumE [c2], c2] q.1 = c0 + q.1 * ((v + c2) + q.1 * c2) := by
      simp [polyEval, sumE]; ring
    have hrest := runsTo_sumcheck3 ms (c0 + q.1 * ((v + c2) + q.1 * c2)) q.2
    have key : sumcheck v 3 (List.replicate ((c0, c2) :: ms).length none) =
        (sumcheckRoundPoly 3 v none >>= fun message ↦ VerifierProgram.sampleChallenge >>=
            fun challenge ↦
          sumcheck (polyEval message challenge) 3 (List.replicate ms.length none) >>= fun x ↦
            (pure (challenge :: x.1, x.2) : VerifierProgram (List E × E))) := rfl
    rw [key]
    have h3 := hrest.bind (f := fun x ↦ (pure (q.1 :: x.1, x.2) : VerifierProgram (List E × E)))
      (runsTo_ret _ _)
    rw [← hev] at h3
    have h2 := hs.bind (f := fun challenge ↦
      sumcheck (polyEval [c0, v + sumE [c2], c2] challenge) 3 (List.replicate ms.length none) >>=
        fun x ↦ (pure (challenge :: x.1, x.2) : VerifierProgram (List E × E))) h3
    have h1 := hmsg.bind (f := fun message ↦ VerifierProgram.sampleChallenge >>= fun challenge ↦
          sumcheck (polyEval message challenge) 3 (List.replicate ms.length none) >>= fun x ↦
            (pure (challenge :: x.1, x.2) : VerifierProgram (List E × E))) h2
    simpa [plainRun, ← hq, hev] using h1

/-- **The layers**, one after the other. -/
theorem runsTo_keccakLayers_cons {L a : ℕ} {rest : List ℕ} {c c' c'' : KeccakClaim}
    {s s' s'' : Fs} {xs ys : List E} (h1 : RunsTo (verifyKeccakLayer L a c) s xs c' s')
    (h2 : RunsTo (keccakLayers L rest c') s' ys c'' s'') :
    RunsTo (keccakLayers L (a :: rest) c) s (xs ++ ys) c'' s'' :=
  h1.bind (f := fun c ↦ keccakLayers L rest c) h2

theorem runsTo_keccakLayers_nil (L : ℕ) (c : KeccakClaim) (s : Fs) :
    RunsTo (keccakLayers L [] c) s [] c s := runsTo_ret _ _

/-- The first claim (V:2068-2072): the committed outputs' part and the last segment's, the
instance weights at the low coordinates, the point, a word's position weights. -/
def vkFirst (inst outs : List E) (committed : E) (seg rl : List E) : KeccakClaim :=
  ⟨committed + (eqKernel seg).getD (keccakSegments - 1) 0 * dot ((eqKernel rl).take 25) outs,
    eqKernel (inst.take 4), inst.drop 4 ++ seg,
    (List.range keccakBits).map fun j ↦ (eqKernel rl).getD (j / 64) 0 * eOfNat (2 ^ (j % 64))⟩

theorem keccakSegments_eq : keccakSegments = 2 := rfl
theorem keccakSegmentBits_eq : keccakSegmentBits = 1 := by decide
theorem qkeccakSlotBits_eq' : qkeccakSlotBits = 6 := by decide

/-- `verifyKeccak` with its two segments' branches taken. -/
theorem verifyKeccak_eq (τ : ℕ) (inst outs : List E) :
    verifyKeccak τ inst outs =
      (VerifierProgram.sampleChallenges keccakSegmentBits >>= fun seg ↦ VerifierProgram.sampleChallenges keccakLaneBits >>= fun rl ↦
        VerifierProgram.readScalar >>= fun committed ↦
        keccakLayers τ (List.range keccakDepth) (vkFirst inst outs committed seg rl) >>= fun claim ↦
        keccakOpen τ (vkFirst inst outs committed seg rl) 1 1 committed >>= fun o ↦
        VerifierProgram.readScalar >>= fun word ↦ VerifierProgram.require (o.2.1.headD 0 * word =
            o.2.2) >>= fun _ ↦
        sumcheck claim.value 3 (List.replicate 4 none) >>= fun x ↦
        keccakOpen τ claim 0 2 x.2 >>= fun y ↦ VerifierProgram.readScalars kBits >>= fun slices ↦
        VerifierProgram.require (multilinearEval claim.mu x.1 * dot y.2.1 slices = y.2.2) >>=
            fun _ ↦
        (pure ([⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ o.1, word⟩], x.1 ++ claim.point.take (τ - 4) ++ y.1,
          slices) : VerifierProgram (List ColumnClaim × List E × List E))) := rfl

/-- **`keccakSeg` on the carried sponge** (V:2061-2087, then the ring map's first challenge). -/
theorem vk_runsTo (τ : ℕ) (inst outs : List E) {s0 s1 s2 s3 s4 s5 s6 s7 : Fs} {seg rl : List E}
    {committed word m0 valO valL valI : E} {claim : KeccakClaim} {xsL slotO low slotI slices : List E}
    {mO mI mS : List (E × E)}
    (h1 : s0.squeezeN keccakSegmentBits = (seg, s1)) (h2 : s1.squeezeN keccakLaneBits = (rl, s2))
    (hL : RunsTo (keccakLayers τ (List.range keccakDepth) (vkFirst inst outs committed seg rl))
      (s2.absorb committed dsObserve) xsL claim s3)
    (hmO : mO.length = 6) (hO : plainRun mO committed s3 = (slotO, valO, s4))
    (hw : ((foldAll slotO (keccakSlotWeights τ (vkFirst inst outs committed seg rl) 1 1)).headD
      []).headD 0 * word = valO)
    (hmI : mI.length = 4) (hI : plainRun mI claim.value (s4.absorb word dsObserve) = (low, valL, s5))
    (hmS : mS.length = 6) (hS : plainRun mS valL s5 = (slotI, valI, s6))
    (hsl : slices.length = 64)
    (hfin : multilinearEval claim.mu low *
      dot ((foldAll slotI (keccakSlotWeights τ claim 0 2)).headD []) slices = valI)
    (hm : (s6.absorbAll slices dsObserve).squeeze = (m0, s7)) :
    RunsTo (keccakSeg τ inst outs) s0
      ([committed] ++ xsL ++ mO.flatMap (fun m ↦ [m.1, m.2]) ++ [word] ++
        mI.flatMap (fun m ↦ [m.1, m.2]) ++ mS.flatMap (fun m ↦ [m.1, m.2]) ++ slices)
      (([⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ slotO, word⟩], low ++ claim.point.take (τ - 4) ++
        slotI, slices), m0) s7 := by
  have r1 := runsTo_sampleN keccakSegmentBits s0
  rw [h1] at r1
  have r2 := runsTo_sampleN keccakLaneBits s1
  rw [h2] at r2
  have r3 := runsTo_readE s2 committed
  have rO := runsTo_sumcheck3 mO committed s3
  rw [hmO, hO] at rO
  have rw' := runsTo_readE s4 word
  have rI := runsTo_sumcheck3 mI claim.value (s4.absorb word dsObserve)
  rw [hmI, hI] at rI
  have rS := runsTo_sumcheck3 mS valL s5
  rw [hmS, hS] at rS
  have rsl := runsTo_readN s6 slices
  rw [hsl] at rsl
  have rm := runsTo_sampleE (s6.absorbAll slices dsObserve)
  rw [hm] at rm
  simp only [List.append_assoc, List.singleton_append]
  have rO' : RunsTo (keccakOpen τ (vkFirst inst outs committed seg rl) 1 1 committed) s3
      (mO.flatMap fun m ↦ [m.1, m.2])
      (slotO, (foldAll slotO (keccakSlotWeights τ (vkFirst inst outs committed seg rl) 1 1)).headD [],
        valO) s4 := by
    rw [keccakOpen_eq, qkeccakSlotBits_eq']
    refine (rO.bind (f := fun x ↦ VerifierProgram.ret (x.1, (foldAll x.1
      (keccakSlotWeights τ (vkFirst inst outs committed seg rl) 1 1)).headD [], x.2))
      (runsTo_ret _ _)).of_eq rfl ?_ rfl rfl
    simp
  have rS' : RunsTo (keccakOpen τ claim 0 2 valL) s5 (mS.flatMap fun m ↦ [m.1, m.2])
      (slotI, (foldAll slotI (keccakSlotWeights τ claim 0 2)).headD [], valI) s6 := by
    rw [keccakOpen_eq, qkeccakSlotBits_eq']
    refine (rS.bind (f := fun x ↦ VerifierProgram.ret (x.1, (foldAll x.1
      (keccakSlotWeights τ claim 0 2)).headD [], x.2)) (runsTo_ret _ _)).of_eq rfl ?_ rfl rfl
    simp

  have hV : RunsTo (verifyKeccak τ inst outs) s0
      (committed :: (xsL ++ (mO.flatMap (fun m ↦ [m.1, m.2]) ++ (word ::
        (mI.flatMap (fun m ↦ [m.1, m.2]) ++ (mS.flatMap (fun m ↦ [m.1, m.2]) ++ slices))))))
      ([⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ slotO, word⟩], low ++ claim.point.take (τ - 4) ++
        slotI, slices) (s6.absorbAll slices dsObserve) := by
    rw [verifyKeccak_eq]
    refine RunsTo.of_eq (xs := [committed] ++ (xsL ++ (mO.flatMap (fun m ↦ [m.1, m.2]) ++ ([word] ++
      (mI.flatMap (fun m ↦ [m.1, m.2]) ++ (mS.flatMap (fun m ↦ [m.1, m.2]) ++ (slices ++ [])))))))
      ?main rfl ?hx rfl rfl
    case main =>
      refine RunsTo.bind_nil r1 ?_
      refine RunsTo.bind_nil r2 ?_
      refine RunsTo.bind r3 ?_
      refine RunsTo.bind hL ?_
      refine RunsTo.bind rO' ?_
      refine RunsTo.bind rw' ?_
      refine RunsTo.bind_nil (runsTo_require hw _) ?_
      refine RunsTo.bind rI ?_
      refine RunsTo.bind rS' ?_
      refine RunsTo.bind rsl ?_
      refine RunsTo.bind_nil (runsTo_require hfin _) ?_
      exact runsTo_ret _ _
    case hx => simp
  unfold keccakSeg
  refine (hV.bind (f := fun r ↦ VerifierProgram.sampleChallenge >>= fun m ↦ (pure (r, m) :
      VerifierProgram _))
    (rm.bind (f := fun m ↦ (pure (([(⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ slotO, word⟩ : ColumnClaim)],
      low ++ claim.point.take (τ - 4) ++ slotI, slices), m) : VerifierProgram _)) (runsTo_ret _
          _))).of_eq
    rfl ?_ ?_ ?_
  · simp
  · simp [← List.append_assoc]
  · rfl

end
end LeanVM.Guest.B1.VerifySub
