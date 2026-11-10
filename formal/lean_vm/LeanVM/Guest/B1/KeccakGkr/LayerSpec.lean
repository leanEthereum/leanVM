/-
  LeanVM.Guest.B1.KeccakGkr.LayerSpec

  `verifyKeccakLayer` as a run on the carried sponge: its rounds as pure functions of the
  sponge and the stream words, and the layer's run once its two checks hold.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Lib
public import LeanVM.Guest.B1.Common.Run
public import LeanVM.Guest.B1.Gkr.Spec

/-!
# A layer on the carried sponge

The specification's layer (`verifyKeccakLayer`) reads the product polynomial, checks the
projection, grinds `grindingBits (productBits - 1) = 3` bits (`sGrindBits`) and samples `s`, runs
the pack rounds (`keccakPackRounds`) and the eleven rounds over the bit position (`sumcheck _ 4`),
reads `t`, checks the final claim and samples `β`; every other grind is of `0` bits. On the
sponge the guest carries (`Fs`, `RunsTo`, B1-a's `Common/Run`):

* `packRunF`: `keccakPackRounds` as a function of the round messages `(g₁, g₂)`;
* `localRunF`: `sumcheck _ 4 (replicate n none)` as a function of the messages `(c₀, c₂, c₃)`;
* `projectedOf`: the layer's projection of the product;
* `layer_runsTo`: the layer runs, reading the product, the messages and `t`, once the two checks
  hold, to the claim `layerClaim`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Tables (grindingBits_le_eight)

@[expose] public section

/-- The bits of the grind before `s`: the product polynomial has degree `productBits - 1`. -/
abbrev sGrindBits : ℕ := grindingBits (productBits - 1)

theorem sGrindBits_eq : sGrindBits = 3 := by decide

/-! ## Checks -/

theorem runsTo_require {c : Prop} [Decidable c] (h : c) (s : Fs) :
    RunsTo (VerifierProgram.require c) s [] () s := by
  simp only [VerifierProgram.require, h, ↓reduceIte]
  exact runsTo_ret () s

/-! ## The pack rounds -/

/-- `keccakPackRounds` on the carried sponge, round `i` reading `(g₁, g₂)`: the value,
the scale, the challenges, and the sponge after them. -/
def packRunF : List E → List (E × E) → E → E → Fs → (E × E × List E) × Fs
  | r :: rs, (g1, g2) :: ms, v, sc, s =>
    let q := (s.absorbAll [g1, g2] dsObserve).squeeze
    let res := packRunF rs ms ((1 + r + q.1) * polyEval [v + r * sumE [g1, g2], g1, g2] q.1)
      (sc * (1 + r + q.1)) q.2
    ((res.1.1, res.1.2.1, q.1 :: res.1.2.2), res.2)
  | _, _, v, sc, s => ((v, sc, []), s)

theorem runsTo_readN2 (s : Fs) (a b : E) :
    RunsTo (VerifierProgram.readScalars 2) s [a, b] [a, b] (s.absorbAll [a, b] dsObserve) :=
  runsTo_readN s [a, b]

theorem runsTo_packRounds :
    ∀ (rs : List E) (ms : List (E × E)) (v sc : E) (s : Fs), ms.length = rs.length →
      RunsTo (keccakPackRounds rs v sc) s (ms.flatMap fun m ↦ [m.1, m.2])
        (packRunF rs ms v sc s).1 (packRunF rs ms v sc s).2
  | [], [], v, sc, s, _ => runsTo_ret _ _
  | r :: rs, (g1, g2) :: ms, v, sc, s, h => by
    have hl : ms.length = rs.length := by simpa using h
    have hmsg : RunsTo (sumcheckRoundPoly 3 v (some r)) s [g1, g2]
        [v + r * sumE [g1, g2], g1, g2] (s.absorbAll [g1, g2] dsObserve) := by
      have := (runsTo_readN2 s g1 g2).bind (f := fun tail ↦ (pure ((v + r * sumE tail) :: tail) :
        VerifierProgram (List E))) (runsTo_ret _ _)
      simpa (disch := omega) [sumcheckRoundPoly, grindingBits_le_eight,
        VerifierProgram.grindProofOfWork] using this
    set q := (s.absorbAll [g1, g2] dsObserve).squeeze with hq
    have hs := runsTo_sampleE (s.absorbAll [g1, g2] dsObserve)
    rw [← hq] at hs
    have hrest := runsTo_packRounds rs ms ((1 + r + q.1) *
        polyEval [v + r * sumE [g1, g2], g1, g2] q.1) (sc * (1 + r + q.1)) q.2 hl
    have key : keccakPackRounds (r :: rs) v sc = (sumcheckRoundPoly 3 v (some r) >>= fun message ↦
        VerifierProgram.sampleChallenge >>= fun challenge ↦
          keccakPackRounds rs ((1 + r + challenge) * polyEval message challenge)
            (sc * (1 + r + challenge)) >>= fun x ↦
            (pure (x.1, x.2.1, challenge :: x.2.2) : VerifierProgram (E × E × List E))) := rfl
    rw [key]
    have h3 := hrest.bind (f := fun x ↦ (pure (x.1, x.2.1, q.1 :: x.2.2) : VerifierProgram (E × E ×
        List E)))
      (runsTo_ret _ _)
    have h2 := hs.bind (f := fun challenge ↦
      keccakPackRounds rs ((1 + r + challenge) * polyEval [v + r * sumE [g1, g2], g1, g2] challenge)
        (sc * (1 + r + challenge)) >>= fun x ↦
        (pure (x.1, x.2.1, challenge :: x.2.2) : VerifierProgram (E × E × List E))) h3
    have h1 := hmsg.bind (f := fun message ↦ VerifierProgram.sampleChallenge >>= fun challenge ↦
          keccakPackRounds rs ((1 + r + challenge) * polyEval message challenge)
            (sc * (1 + r + challenge)) >>= fun x ↦
            (pure (x.1, x.2.1, challenge :: x.2.2) : VerifierProgram (E × E × List E))) h2
    simpa [packRunF, ← hq] using h1
  | [], _ :: _, _, _, _, h | _ :: _, [], _, _, _, h => by simp at h

/-! ## Plain rounds of degree three -/

/-- `sumcheck v 4 (replicate n none)` on the carried sponge, round `i` reading
`(c₀, c₂, c₃)`: the challenges and final value, and the sponge after them. -/
def localRunF : List (E × E × E) → E → Fs → (List E × E) × Fs
  | [], v, s => (([], v), s)
  | (c0, c2, c3) :: ms, v, s =>
    let q := (s.absorbAll [c0, c2, c3] dsObserve).squeeze
    let res := localRunF ms (polyEval [c0, v + sumE [c2, c3], c2, c3] q.1) q.2
    ((q.1 :: res.1.1, res.1.2), res.2)

theorem runsTo_sumcheck4 :
    ∀ (ms : List (E × E × E)) (v : E) (s : Fs),
      RunsTo (sumcheck v 4 (List.replicate ms.length none)) s
        (ms.flatMap fun m ↦ [m.1, m.2.1, m.2.2]) (localRunF ms v s).1 (localRunF ms v s).2
  | [], v, s => runsTo_ret _ _
  | (c0, c2, c3) :: ms, v, s => by
    have hmsg : RunsTo (sumcheckRoundPoly 4 v none) s [c0, c2, c3]
        [c0, v + sumE [c2, c3], c2, c3] (s.absorbAll [c0, c2, c3] dsObserve) := by
      have h0 := runsTo_readE s c0
      have h1 := runsTo_readN (s.absorb c0 dsObserve) [c2, c3]
      have h2 := h1.bind (f := fun tail ↦ (pure (c0 :: (v + sumE tail) :: tail) : VerifierProgram
          (List E)))
        (runsTo_ret _ _)
      have h3 := h0.bind (f := fun constant ↦ VerifierProgram.readScalars 2 >>= fun tail ↦
        (pure (constant :: (v + sumE tail) :: tail) : VerifierProgram (List E))) h2
      simpa (disch := omega) [sumcheckRoundPoly, Fs.absorbAll, grindingBits_le_eight,
        VerifierProgram.grindProofOfWork] using h3
    set q := (s.absorbAll [c0, c2, c3] dsObserve).squeeze with hq
    have hs := runsTo_sampleE (s.absorbAll [c0, c2, c3] dsObserve)
    rw [← hq] at hs
    have hrest := runsTo_sumcheck4 ms (polyEval [c0, v + sumE [c2, c3], c2, c3] q.1) q.2
    have key : sumcheck v 4 (List.replicate ((c0, c2, c3) :: ms).length none) =
        (sumcheckRoundPoly 4 v none >>= fun message ↦ VerifierProgram.sampleChallenge >>=
            fun challenge ↦
          sumcheck (polyEval message challenge) 4 (List.replicate ms.length none) >>= fun x ↦
            (pure (challenge :: x.1, x.2) : VerifierProgram (List E × E))) := rfl
    rw [key]
    have h3 := hrest.bind (f := fun x ↦ (pure (q.1 :: x.1, x.2) : VerifierProgram (List E × E)))
      (runsTo_ret _ _)
    have h2 := hs.bind (f := fun challenge ↦
      sumcheck (polyEval [c0, v + sumE [c2, c3], c2, c3] challenge) 4
        (List.replicate ms.length none) >>= fun x ↦
        (pure (challenge :: x.1, x.2) : VerifierProgram (List E × E))) h3
    have h1 := hmsg.bind (f := fun message ↦ VerifierProgram.sampleChallenge >>= fun challenge ↦
          sumcheck (polyEval message challenge) 4 (List.replicate ms.length none) >>= fun x ↦
            (pure (challenge :: x.1, x.2) : VerifierProgram (List E × E))) h2
    simpa [localRunF, ← hq] using h1

/-! ## The layer -/

theorem RunsTo.bind_nil {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} {s s1 s2 :
    Fs} {ys : List E}
    {a : α} {b : β} (h1 : RunsTo p s [] a s1) (h2 : RunsTo (f a) s1 ys b s2) :
    RunsTo (p >>= f) s ys b s2 := by
  simpa using h1.bind h2

/-- Runs of `m >>= g`, then of `f`, are a run of `m >>= fun x ↦ g x >>= f`. -/
theorem RunsTo.bind_assoc' {α β γ : Type} {m : VerifierProgram α} {g : α → VerifierProgram β}
    {f : β → VerifierProgram γ} {s s1 s2 : Fs} {xs ys : List E} {a : β} {b : γ}
    (h1 : RunsTo (m >>= g) s xs a s1) (h2 : RunsTo (f a) s1 ys b s2) :
    RunsTo (m >>= fun x ↦ g x >>= f) s (xs ++ ys) b s2 := by
  have := h1.bind h2
  rwa [bind_assoc] at this

/-- The projection of the product onto the claim's instance weights. -/
def projectedOf (c : KeccakClaim) (product : List E) : E :=
  sumE ((List.range productBits).map fun b ↦
    sumE ((List.zip c.mu rmfeProject).filterMap fun (m, mask) ↦
      if mask.testBit b then some m else none) * product.getD b 0)

/-- The grind and the squeeze after the product, on the nonce `n`: `s`, and the sponge. -/
def layerSq (s0 : Fs) (product : List E) (n : E) : E × Fs :=
  (s0.absorbAll product dsObserve).grindSqueeze sGrindBits n

/-- The pack rounds from the product's value at `s`. -/
def layerPack (c : KeccakClaim) (s0 : Fs) (product : List E) (n : E) (packMsgs : List (E × E)) :
    (E × E × List E) × Fs :=
  packRunF c.point packMsgs (polyEval product (layerSq s0 product n).1) 1 (layerSq s0 product n).2

/-- The rounds over the bit position. -/
def layerLocal (c : KeccakClaim) (s0 : Fs) (product : List E) (n : E) (packMsgs : List (E × E))
    (localMsgs : List (E × E × E)) : (List E × E) × Fs :=
  localRunF localMsgs (layerPack c s0 product n packMsgs).1.1 (layerPack c s0 product n packMsgs).2

/-- The squeeze after `t`: `β`, and the sponge. -/
def layerBeta (c : KeccakClaim) (s0 : Fs) (product : List E) (n : E) (packMsgs : List (E × E))
    (localMsgs : List (E × E × E)) (t : E × E × E) : E × Fs :=
  ((layerLocal c s0 product n packMsgs localMsgs).2.absorbAll [t.1, t.2.1, t.2.2] dsObserve).squeeze

/-- The final check of a layer. -/
def LayerFinal (c : KeccakClaim) (s0 : Fs) (product : List E) (n : E) (packMsgs : List (E × E))
    (localMsgs : List (E × E × E)) (t : E × E × E) : Prop :=
  let kappa := sumE (keccakInstanceWeights (layerSq s0 product n).1)
  (layerPack c s0 product n packMsgs).1.2.1 *
      dot ((eqKernel (layerLocal c s0 product n packMsgs localMsgs).1.1).take keccakBits)
        c.weights * (kappa * t.1 + (kappa + t.2.1) * t.2.2) =
    (layerLocal c s0 product n packMsgs localMsgs).1.2

/-- The claim a layer returns. -/
def layerClaim (c : KeccakClaim) (s0 : Fs) (product : List E) (n : E) (packMsgs : List (E × E))
    (localMsgs : List (E × E × E)) (t : E × E × E) : KeccakClaim :=
  let beta := (layerBeta c s0 product n packMsgs localMsgs t).1
  let eq := eqKernel (layerLocal c s0 product n packMsgs localMsgs).1.1
  ⟨t.1 + beta * (t.2.1 + beta * t.2.2), keccakInstanceWeights (layerSq s0 product n).1,
    (layerPack c s0 product n packMsgs).1.2.2,
    keccakLinearTranspose ((List.range keccakBits).map fun j ↦
      eq.getD j 0 + beta * (eq.getD (keccakAlong j 4) 0 + beta * eq.getD (keccakAlong j 3) 0))⟩

/-- **A layer on the carried sponge**: once the projection check, the grind before `s` and the
final check hold, the layer reads the product, the nonce, the pack and position rounds' messages
and `t`, and returns `layerClaim`. -/
theorem layer_runsTo (logSteps step : ℕ) (c : KeccakClaim) (s0 : Fs) (product : List E)
    (hp : product.length = productBits) (n : E)
    (hg : (s0.absorbAll product dsObserve).GrindOk sGrindBits n) (packMsgs : List (E × E))
    (hpm : packMsgs.length = c.point.length) (localMsgs : List (E × E × E))
    (hlm : localMsgs.length = keccakLocalBits) (t : E × E × E)
    (hproj : projectedOf c product + keccakIota logSteps step c * sumE c.mu = c.value)
    (hfin : LayerFinal c s0 product n packMsgs localMsgs t) :
    RunsTo (verifyKeccakLayer logSteps step c) s0
      (product ++ [n] ++ packMsgs.flatMap (fun m ↦ [m.1, m.2]) ++
        localMsgs.flatMap (fun m ↦ [m.1, m.2.1, m.2.2]) ++ [t.1, t.2.1, t.2.2])
      (layerClaim c s0 product n packMsgs localMsgs t)
      (layerBeta c s0 product n packMsgs localMsgs t).2 := by
  have r1 : RunsTo (VerifierProgram.readScalars productBits) s0 product product (s0.absorbAll product dsObserve) :=
    hp ▸ runsTo_readN s0 product
  have r2 := runsTo_grindSample sGrindBits (s0.absorbAll product dsObserve) n hg
  rw [show grindWords sGrindBits n = [n] by simp [grindWords, sGrindBits_eq]] at r2
  have r3 := runsTo_packRounds c.point packMsgs (polyEval product (layerSq s0 product n).1) 1
    (layerSq s0 product n).2 hpm
  have r4 := runsTo_sumcheck4 localMsgs (layerPack c s0 product n packMsgs).1.1
    (layerPack c s0 product n packMsgs).2
  rw [hlm] at r4
  have r5 := runsTo_readN (layerLocal c s0 product n packMsgs localMsgs).2 [t.1, t.2.1, t.2.2]
  have hb : grindingBits 2 = 0 := grindingBits_le_eight (by norm_num)
  simp only [List.append_assoc]
  unfold verifyKeccakLayer
  refine RunsTo.bind r1 ?_
  refine RunsTo.bind_nil (runsTo_require hproj _) ?_
  refine RunsTo.bind_assoc' (m := VerifierProgram.grindProofOfWork (grindingBits (productBits - 1)))
    (g := fun _ ↦ VerifierProgram.sampleChallenge) r2 ?_
  refine RunsTo.bind r3 ?_
  refine RunsTo.bind r4 ?_
  refine RunsTo.bind r5 ?_
  refine RunsTo.bind_nil (runsTo_require ?_ _) ?_
  · exact hfin
  simp only [hb, VerifierProgram.grindProofOfWork, ↓reduceIte]
  refine RunsTo.bind_nil (runsTo_ret () _) ?_
  refine RunsTo.bind_nil (runsTo_sampleE _) ?_
  exact runsTo_ret _ _

end
end LeanVM.Guest.B1.VerifySub
