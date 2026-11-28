/-
  LeanVM.Guest.B1.VsC.KLayerA

  `keccak_layer`'s placed completeness, stated, and `verify_keccak`'s from it.
-/

module

public import LeanVM.Guest.B1.VsC.Vsc8CalleesA
public import LeanVM.Guest.B1.KeccakGkr.LayerSpec

/-!
# `keccak_layer`, placed: the statement

`keccak_layer__L{first}` on the honest transcript of one layer (`layer_runsTo`'s data: the product,
the nonce, the pack and position rounds' messages, `t`, with the projection check, the grind and
the final check passing), at frame `fp` with its cursor `cb = fp + fs (layerName first)` right after
its frame:

* its own words are its four `HeapBuf`s from `cb`: the pack point (`y` words, `packRunF`'s
  challenges, which it hands its two `layer_rounds` dispatches), the local point (`11`), the next
  claim's lanes (`25`) and its flips (`7`); it claims them as its data (`klOwn`), so the next layer
  may load them;
* its caller holds the claim's record at `claim` with the pointers `cpt`, `clp`, `clc`, `cfl` to its
  point, lanes, local point and flips (`ClaimRecAt`), the stream words at the cursor, the window
  table at `tabs`, and at `out` the next claim's record pointing into the layer's buffers
  (`klOutW`);
* the claim's point has `y` coordinates, and every word of the arrays it reads is at the address
  of a word index of the region `R` it loads from (`InRegion`);
* on any memory holding its words and that record, the record is the next claim's (`ClaimRec … out`);
* it returns the capacity after `β` and the cursor past the layer's words, quiet, and ends past
  its buffers, within `2^18` of its cursor when every frame is below `2^16`.

`KeccakLayerCompleteA` is that statement; `VkFromLayerA` says `verify_keccak`'s placed completeness
follows from it (its other callees are `layer_rounds_placed`, `plain60_placed`, `plain41_placed`,
`cl_placed`, `index_mle`'s). Both are proved (`KL.keccakLayerCompleteA`, `vkFromLayerAE`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.VerifySub LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **A claim's record at `rec`, its pointers given**: `ClaimRec` with the point at `cpt`, the lanes
at `clp`, and after the first layer the local point at `clc` and the flips at `cfl`. -/
def ClaimRecAt (rd : Reader) (first : Bool) (rec cpt clp clc cfl : E) (c : KeccakClaim) (y : ℕ) : Prop :=
  c.mu.length = pack ∧ c.point.length = y ∧
  LoadHolds rd rec 0 c.value ∧ LoadHolds rd rec 1 (sumE c.mu) ∧
  (∀ i < pack, LoadHolds rd rec (6 + i) (c.mu.getD i 0)) ∧
  LoadHolds rd rec 2 cpt ∧ ReadsAt rd cpt c.point ∧
  ∃ lanes : List E, LoadHolds rd rec 3 clp ∧ lanes.length = 25 ∧ ReadsAt rd clp lanes ∧
    if first then c.weights = firstWeights lanes
    else ∃ loc : List E, LoadHolds rd rec 4 clc ∧ loc.length = keccakLocalBits ∧
      ReadsAt rd clc loc ∧ LoadHolds rd rec 5 cfl ∧ ReadsAt rd cfl (flipsOf c.weights) ∧
      c.weights = laterWeights lanes (eqKernel (loc.take 6))

/-- A layer's stream words (`layer_runsTo`). -/
def klXs (product : List E) (n : E) (packMsgs : List (E × E)) (localMsgs : List (E × E × E)) (t : E × E × E) :
    List E :=
  product ++ [n] ++ packMsgs.flatMap (fun m ↦ [m.1, m.2]) ++
    localMsgs.flatMap (fun m ↦ [m.1, m.2.1, m.2.2]) ++ [t.1, t.2.1, t.2.2]

/-- The next claim's record the layer writes at `out`, its buffers from `cb` (`y` the point's
length): `KC_VALUE`, `KC_KAPPA`, `KC_POINT`, `KC_LANES`, `KC_LOCAL`, `KC_FLIPS`, then the sixteen
instance weights. -/
def klOutW (c' : KeccakClaim) (cb y : ℕ) : List E :=
  [c'.value, sumE c'.mu, ptrAtV cb, ptrAtV (cb + y + 11), ptrAtV (cb + y), ptrAtV (cb + y + 36)] ++ c'.mu

/-- The layer's own buffers from its cursor `cb`. -/
def klOwn (cb y : ℕ) (i : ℕ) : Prop := cb ≤ i ∧ i < cb + y + 43

/-- The arrays the layer reads and writes of its caller's (and of the earlier layers'). -/
def klArrays (claim cpt clp clc cfl cur out tabs : E) (y nx : ℕ) : List (E × ℕ) :=
  [(claim, kcSize), (cpt, y), (clp, 25), (clc, keccakLocalBits), (cfl, 7), (cur, nx), (out, kcSize),
    (tabs, 2 ^ winTabBits)]

/-- Every word of the arrays `arrs` is at the address of an index of `R`. -/
def InRegion (arrs : List (E × ℕ)) (R : ℕ → Prop) : Prop :=
  ∀ q ∈ arrs, ∀ t < q.2, ∃ i, q.1.limb 0 * addressOfIndex t = addressOfIndex i ∧ R i

/-- **`keccak_layer` completes placed** on a layer's honest transcript. -/
def KeccakLayerCompleteA (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) : Prop :=
  ∀ (first : ℕ), first < 2 →
  ∀ (f0 f1 f2 f3 f4 p0 p1 cur claim out iota tabs w cpt clp clc cfl : E) (y step : ℕ) (c : KeccakClaim)
    (product : List E) (n : E) (packMsgs : List (E × E)) (localMsgs : List (E × E × E)) (t : E × E × E)
    (R : ℕ → Prop) (fp : ℕ),
    1 ≤ y → y < 32 → product.length = productBits → packMsgs.length = y →
    localMsgs.length = keccakLocalBits →
    ((plainStart first [f0, f1, f2, f3, f4] w).absorbAll product dsObserve).GrindOk sGrindBits n →
    projectedOf c product + keccakIota (y + 3) step c * sumE c.mu = c.value →
    LayerFinal c (plainStart first [f0, f1, f2, f3, f4] w) product n packMsgs localMsgs t →
    (first = 1 → (p0, p1) = Keccak.scalarCells w dsObserve) → iota = keccakIota (y + 3) step c →
    c.point.length = y →
    InRegion (klArrays claim cpt clp clc cfl cur out tabs y (klXs product n packMsgs localMsgs t).length) R →
    ∃ e, fp + fs (layerName first) + y + 43 ≤ e ∧
      ((∀ f, fs f < 2 ^ 16) → e ≤ fp + fs (layerName first) + 2 ^ 18) ∧ CallAtA fs al cert k (layerName first)
      [f0, f1, f2, f3, f4, p0, p1, cur, gen ^ y, gen ^ (y / krStep), gen ^ (y % krStep), claim, out, iota, tabs]
      ((layerBeta c (plainStart first [f0, f1, f2, f3, f4] w) product n packMsgs localMsgs t).2.cap ++
        [cur * gen ^ (klXs product n packMsgs localMsgs t).length])
      R (klOwn (fp + fs (layerName first)) y)
      (fun rd => ReadsAt rd out (klOutW (layerClaim c (plainStart first [f0, f1, f2, f3, f4] w) product n
          packMsgs localMsgs t) (fp + fs (layerName first)) y) →
        ClaimRec rd false out (layerClaim c (plainStart first [f0, f1, f2, f3, f4] w) product n packMsgs
          localMsgs t) y)
      (fun rd => WinTabs rd tabs ∧ ClaimRecAt rd (first = 1) claim cpt clp clc cfl c y ∧
        ReadsAt rd cur (klXs product n packMsgs localMsgs t) ∧
        ReadsAt rd out (klOutW (layerClaim c (plainStart first [f0, f1, f2, f3, f4] w) product n
          packMsgs localMsgs t) (fp + fs (layerName first)) y))
      PostQuiet (fs (layerName first)) fp (fp + fs (layerName first)) e

/-- **`verify_keccak`'s placed completeness from its layers'**: its other callees are placed
(`layer_rounds_placed`, `plain60_placed`, `plain41_placed`, `cl_placed`, `index_mle`'s). -/
def VkFromLayerA (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) : Prop :=
  KeccakLayerCompleteA fs al cert k → VerifyKeccakCompleteA fs al cert k

end
end LeanVM.Guest.B1.VsC
