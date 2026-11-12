module

public import LeanVM.Guest.Fast.SpWots
public import LeanVM.Guest.Fast.Common
public import LeanVM.Guest.Fast.FunctionIdx
public import LeanVM.Guest.B1.Sig.Interface
public import LeanVM.Guest.B1.Sig.SphincsSig
public import LeanVM.Guest.B1.Sig.Bytes
public import LeanVM.Cost.Rules

/-!
# leanSPHINCS's signature reader, computable

`verify_sig_lean_sphincs` (`Data.core20`, compiled function `21`, its template
`B1/Sig/SphincsT.lean`, at leanVM main 40f877dc) hints the randomizer, each FORS tree's secret and the
ordered children on its climb, each layer's counter and the ordered children on its path into its
own frame, at cells its body fixes, and calls `sp_wots` (`Data.core19`, function `20`) once a
layer, whose frame holds the layer's chain starts at cells its digit words select (`spStartAt`,
`Fast/SpWots.lean`). The reader takes `verify_sig_lean_sphincs`' valuation `σ` and the three
`sp_wots` frames `w0`, `w1`, `w2`:

* `forsOpeningA T σ c`: FORS tree `c`'s opening, its secret at `spForsBase c`, at each height
  `z` the hinted child the bit does not name (`sibN`), the pair's and the bit's cells off the
  tables `T.forsKid`, `T.forsBit` (row `c`, entry `z`);
* `layerA T σ w l layer`: layer `l`'s counter (the cell `sp_from_bytes` folds), its chain
  starts off `sp_wots`' frame `w` (`cwCellA` over `sp_wots`' tables), its path (the pairs' and
  bits' cells off `T.pathKid`, `T.pathBit`, row `l`);
* `sphincsSigOfA T σ w0 w1 w2`, its layers by `depFin3` (the compiler's dependent function of
  `Fin 3`); `spWotsArgs σ l`, `spWotsRets σ l`: the words of layer `l`'s call of `sp_wots`
  (`PK.seed`, the key's two address cells, the encoding's first cell; the leaf), by which the
  frame map finds its frame;
* **`sphincsSigOfN_eq`**: off the frame map re-keyed by index, the reader is B1's witness
  `sphincsSigOf` (`B1/Sig/SphincsSig.lean`): the template's positions checked by the kernel
  (`sForsPositions`, `sPathPositions`, `sLayerPositions`), the chain starts by
  `spStartAt_eq_cwCell`.

`SpTabs`, `spTabs`: the tables as arrays, built once by the caller.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Sig

@[expose] public section

/-- FORS tree `c`'s hinted pair at height `z` (`sForsKid c z`): row `c`, entry `z`. -/
def spForsKids : List (List Nat) := [
  [1393, 1410, 1424, 1438, 1452, 1466, 1480, 1494, 1508, 1522],
  [1542, 1559, 1575, 1589, 1603, 1617, 1631, 1645, 1659, 1673],
  [1695, 1712, 1728, 1744, 1758, 1772, 1786, 1800, 1814, 1828],
  [1850, 1867, 1883, 1899, 1913, 1927, 1941, 1955, 1969, 1983],
  [2005, 2022, 2038, 2054, 2070, 2084, 2098, 2112, 2126, 2140],
  [2162, 2179, 2195, 2211, 2227, 2241, 2255, 2269, 2283, 2297],
  [2319, 2336, 2352, 2368, 2384, 2398, 2412, 2426, 2440, 2454],
  [2476, 2493, 2509, 2525, 2541, 2555, 2569, 2583, 2597, 2611],
  [2633, 2650, 2666, 2682, 2698, 2714, 2728, 2742, 2756, 2770],
  [2792, 2809, 2825, 2841, 2857, 2873, 2887, 2901, 2915, 2929],
  [2951, 2968, 2984, 3000, 3016, 3032, 3046, 3060, 3074, 3088],
  [3110, 3127, 3143, 3159, 3175, 3191, 3205, 3219, 3233, 3247],
  [3269, 3286, 3302, 3318, 3334, 3350, 3364, 3378, 3392, 3406],
  [3428, 3445, 3461, 3477, 3493, 3509, 3523, 3537, 3551, 3565],
  [3587, 3604, 3620, 3636, 3652, 3668, 3682, 3696, 3710, 3724],
  [3746, 3763, 3779, 3795, 3811, 3827, 3841, 3855, 3869, 3883],
  [3905, 3922, 3938, 3954, 3970, 3986, 4002, 4016, 4030, 4044],
  [4066, 4083, 4099, 4115, 4131, 4147, 4163, 4177, 4191, 4205],
  [4227, 4244, 4260, 4276, 4292, 4308, 4324, 4338, 4352, 4366],
  [4388, 4405, 4421, 4437, 4453, 4469, 4485, 4499, 4513, 4527],
  [4549, 4566, 4582, 4598, 4614, 4630, 4646, 4660, 4674, 4688],
  [4710, 4727, 4743, 4759, 4775, 4791, 4807, 4821, 4835, 4849],
  [4871, 4888, 4904, 4920, 4936, 4952, 4968, 4982, 4996, 5010],
  [5032, 5049, 5065, 5081, 5097, 5113, 5129, 5143, 5157, 5171]]

/-- The bit `is_child` reads at FORS tree `c`'s height `z` (`sForsBit (10 c + z)`). -/
def spForsBits : List (List Nat) := [
  [42, 43, 28, 29, 30, 31, 32, 33, 34, 35],
  [48, 49, 50, 51, 36, 37, 38, 39, 40, 41],
  [54, 55, 56, 57, 58, 59, 44, 45, 46, 47],
  [60, 61, 62, 63, 64, 65, 66, 67, 52, 53],
  [82, 83, 68, 69, 70, 71, 72, 73, 74, 75],
  [88, 89, 90, 91, 76, 77, 78, 79, 80, 81],
  [94, 95, 96, 97, 98, 99, 84, 85, 86, 87],
  [100, 101, 102, 103, 104, 105, 106, 107, 92, 93],
  [122, 123, 108, 109, 110, 111, 112, 113, 114, 115],
  [128, 129, 130, 131, 116, 117, 118, 119, 120, 121],
  [134, 135, 136, 137, 138, 139, 124, 125, 126, 127],
  [140, 141, 142, 143, 144, 145, 146, 147, 132, 133],
  [162, 163, 148, 149, 150, 151, 152, 153, 154, 155],
  [168, 169, 170, 171, 156, 157, 158, 159, 160, 161],
  [174, 175, 176, 177, 178, 179, 164, 165, 166, 167],
  [180, 181, 182, 183, 184, 185, 186, 187, 172, 173],
  [202, 203, 188, 189, 190, 191, 192, 193, 194, 195],
  [208, 209, 210, 211, 196, 197, 198, 199, 200, 201],
  [214, 215, 216, 217, 218, 219, 204, 205, 206, 207],
  [220, 221, 222, 223, 224, 225, 226, 227, 212, 213],
  [242, 243, 228, 229, 230, 231, 232, 233, 234, 235],
  [248, 249, 250, 251, 236, 237, 238, 239, 240, 241],
  [254, 255, 256, 257, 258, 259, 244, 245, 246, 247],
  [260, 261, 262, 263, 264, 265, 266, 267, 252, 253]]

/-- Layer `l`'s hinted pair at path level `j` (`sPathKid l j`). -/
def spPathKids : List (List Nat) := [
  [5297, 5310, 5323, 5336, 5349, 5362, 5375, 5388],
  [5455, 5468, 5481, 5494, 5507, 5520, 5533, 5546],
  [5610, 5626, 5639, 5652, 5665, 5678, 5691, 5704, 5717, 5730]]

/-- The bit `is_child` reads at layer `l`'s level `j` (`sLeafBit (8 l + j)`). -/
def spPathBits : List (List Nat) := [
  [292, 293, 294, 295, 296, 297, 298, 299],
  [284, 285, 286, 287, 288, 289, 290, 291],
  [276, 277, 278, 279, 280, 281, 282, 283, 268, 269]]


/-- `verify_sig_lean_sphincs`' and `sp_wots`' tables, as arrays: the lanes of `g^k` (`gLanes`),
`sp_wots`' groups' selector cells and chain starts' tables, the FORS trees' and the layers' pairs
and bits. -/
structure SpTabs where
  lanes : List ℕ
  sel : Array ℕ
  first : Array (Array ℕ)
  rest : Array (Array ℕ)
  last : Array (Array ℕ)
  forsKid : Array (Array ℕ)
  forsBit : Array (Array ℕ)
  pathKid : Array (Array ℕ)
  pathBit : Array (Array ℕ)

/-- **The tables**, built from the literals. -/
def spTabs : SpTabs := ⟨gLanes, spSel.toArray, tabA spFirst, tabA spRest, tabA spLast,
  tabA spForsKids, tabA spForsBits, tabA spPathKids, tabA spPathBits⟩

/-- FORS tree `c`'s base: its secret's cell (`sForsBase`), 9 values before its first pair. Tree
`k`'s width is `149 + 2·([k ≠ 0] + bitlen k)` (`sp_fors_at`'s constants, nonzero at the root for
`k ≠ 0` and at heights `2..9` while `k >>> (z - 2) ≠ 0`), so the bases are linear on each run of
equal bit lengths; arithmetic, as the decoder computes it cheaply (`sForsPositions` checks it). -/
def spForsBase (c : ℕ) : ℕ :=
  if c = 0 then 1384 else if c < 2 then 1533 else if c < 4 then 1686 + 155 * (c - 2)
  else if c < 8 then 1996 + 157 * (c - 4) else if c < 16 then 2624 + 159 * (c - 8)
  else 3896 + 161 * (c - 16)

/-- **FORS tree `c`'s opening**, off `verify_sig_lean_sphincs`' valuation. -/
def forsOpeningA (T : SpTabs) (σ : Val) (c : ℕ) : Sphincs.ForsTreeOpening :=
  ⟨cellVal (σ (.n (spForsBase c))),
    fun z ↦ cellVal (sibN σ (offAtA T.forsBit c z.val) (offAtA T.forsKid c z.val))⟩

/-- Layer `l`'s base (`sLayerBase`): its counter at `+ 36`, its encoding at `+ 46`, its leaf at
`+ 47`. -/
def spLayerBase (l : ℕ) : ℕ := if l = 0 then 5249 else if l = 1 then 5407 else 5562
def spCtr (l : ℕ) : ℕ := spLayerBase l + 36
def spEnc (l : ℕ) : ℕ := spLayerBase l + 46
def spLeaf (l : ℕ) : ℕ := spLayerBase l + 47

/-- Layer `l`'s key's address cells (`sA0Of`, `sA1Of`). -/
def spA0 (l : ℕ) : ℕ := if l = 0 then 1379 else if l = 1 then 5404 else 5561
def spA1 (l : ℕ) : ℕ := if l = 0 then 1381 else if l = 1 then 5406 else 5560

/-- **Layer `l`'s signature**: its counter's cell, its `sp_wots` frame `w`, its path's pairs and
bits (row `l` of the tables). -/
def layerA (T : SpTabs) (σ w : Val) (l : ℕ) (layer : Sphincs.Layer) :
    Sphincs.LayerSignature layer :=
  ⟨BitVec.ofNat 32 (beWordAt 0 (cellNat (σ (.n (spCtr l))))),
    fun i ↦ cellVal (w (.n (cwCellA T.lanes 21 T.sel T.first T.rest T.last w i.val))),
    fun j ↦ cellVal (sibN σ (offAtA T.pathBit l j.val) (offAtA T.pathKid l j.val))⟩

/-- Layer `l`'s call of `sp_wots`: its arguments (`PK.seed`, the key's two address cells, the
encoding's first cell) and its return (the leaf). -/
def spWotsArgs (σ : Val) (l : ℕ) : List E :=
  [σ (.n 2), σ (.n (spA0 l)), σ (.n (spA1 l)), σ (.n (spEnc l))]
def spWotsRets (σ : Val) (l : ℕ) : List E := [σ (.n (spLeaf l))]

/-- **The layers as the reader builds them** (`LeanVM.Cost.depFin3`, a dependent function of
`Fin 3`), encoded as the statement encodes a signature's layers: the array of their values
(`depFinEncoding`). Stated here, at `Fin 3`: `depFin3`'s domain is `Fin 3`, which instance search
does not unify with `Sphincs.Layer = Fin layerCount` (`layerCount` is not reducible), so neither
`depFinEncoding` nor the statement's encoding of a layer's signature is found for it; and
`Cost/Rules.lean`, where `depFin3` is, does not see the statement's schemes. -/
instance layersEncodingFin3 :
    LeanVM.Cost.MachineEncoding ((i : Fin 3) → Sphincs.LayerSignature i) :=
  @LeanVM.Cost.depFinEncoding 3 (fun i ↦ Sphincs.LayerSignature i)
    fun i ↦ LeanVM.Cost.instMachineEncodingLayerSignature_1 i

/-- **The leanSPHINCS signature `verify_sig_lean_sphincs` checks**, off its valuation `σ` and its
three `sp_wots` frames. -/
def sphincsSigOfA (T : SpTabs) (σ w0 w1 w2 : Val) : Sphincs.Signature :=
  ⟨cellVal (σ (.n 6)), fun c ↦ forsOpeningA T σ c.val,
    LeanVM.Cost.depFin3 (layerA T σ w0 0 0) (layerA T σ w1 1 1) (layerA T σ w2 2 2)⟩

/-- **The signature off the frame map keyed by index**: `sp_wots` is function `20`. -/
def sphincsSigOfN (σ : Val) (Vn : NFrames) : Sphincs.Signature :=
  sphincsSigOfA spTabs σ (Vn 20 (spWotsArgs σ 0) (spWotsRets σ 0))
    (Vn 20 (spWotsArgs σ 1) (spWotsRets σ 1)) (Vn 20 (spWotsArgs σ 2) (spWotsRets σ 2))

/-! ## The reader is the witness's -/

/-- The template's positions (`SphincsT.lean`, `SphincsSig.lean`): each FORS tree's secret, and
at each height its hinted pair and the bit `is_child` reads. -/
theorem sForsPositions : ∀ c < 24, sForsBase c = spForsBase c ∧ ∀ z < 10,
    offAt spForsKids c z = sForsKid c z ∧ sForsBit (10 * c + z) = .n (offAt spForsBits c z) := by
  decide +kernel

/-- The template's positions: each layer's path's hinted pairs and bits. -/
theorem sPathPositions : ∀ l < 3, ∀ j < 10, l = 2 ∨ j < 8 →
    offAt spPathKids l j = sPathKid l j ∧ sLeafBit (sOffOf l + j) = .n (offAt spPathBits l j) := by
  decide +kernel

/-- The template's positions: each layer's call, counter. -/
theorem sLayerPositions : ∀ l < 3, sA0Of l = .n (spA0 l) ∧ sA1Of l = .n (spA1 l) ∧
    sEncOf l = .n (spEnc l) ∧ sLeafOf l = .n (spLeaf l) ∧ sCtrOf l = .n (spCtr l) := by
  decide +kernel

theorem forsTreeOpening_ext {a b : Sphincs.ForsTreeOpening} (h1 : a.secret = b.secret)
    (h2 : a.path = b.path) : a = b := by
  cases a; cases b; cases h1; cases h2; rfl

theorem forsOpeningA_eq (σ : Val) {c : ℕ} (hc : c < 24) :
    forsOpeningA spTabs σ c = sForsOpeningOf σ c := by
  obtain ⟨hb, hz⟩ := sForsPositions c hc
  have e1 : spTabs.forsBit = tabA spForsBits := rfl
  have e2 : spTabs.forsKid = tabA spForsKids := rfl
  apply forsTreeOpening_ext
  · show cellVal (σ (.n (spForsBase c))) = cellVal (σ (.n (sForsBase c)))
    rw [hb]
  funext z
  show cellVal (sibN σ (offAtA spTabs.forsBit c z.val) (offAtA spTabs.forsKid c z.val)) =
    cellVal (siblingOf σ (sForsBit (10 * c + z.val)) (sForsKid c z.val))
  rw [e1, e2]
  obtain ⟨hk, hbit⟩ := hz z.val (by have := z.isLt; simpa [Sphincs.forsTreeHeight] using this)
  rw [offAtA_tabA, offAtA_tabA, hk, hbit]
  rfl

/-- `sp_wots`' tables off arrays read the chain starts `sChainValuesOf` reads. -/
theorem layerChains_eq (w : Val) (i : Sphincs.ChainIndex) :
    cellVal (w (.n (cwCellA spTabs.lanes 21 spTabs.sel spTabs.first spTabs.rest spTabs.last w
      i.val))) = sChainValuesOf w i := by
  show _ = cellVal (w (spRen (spStartAt (spK w) i.val)))
  rw [spStartAt_eq_cwCell w i.isLt]
  exact congrArg (fun k ↦ cellVal (w (.n k))) (cwCellA_eq 21 spSel spFirst spRest spLast w i.val)

theorem layerSignature_ext {l : Sphincs.Layer} {a b : Sphincs.LayerSignature l}
    (h1 : a.counter = b.counter) (h2 : a.chainValues = b.chainValues)
    (h3 : a.authenticationPath = b.authenticationPath) : a = b := by
  cases a; cases b; cases h1; cases h2; cases h3; rfl

theorem signature_ext {a b : Sphincs.Signature} (h1 : a.randomizer = b.randomizer)
    (h2 : a.forsOpening = b.forsOpening) (h3 : a.layers = b.layers) : a = b := by
  cases a; cases b; cases h1; cases h2; cases h3; rfl

theorem layerA_eq (σ : Val) (V : FrameMap) (l : Sphincs.Layer) :
    layerA spTabs σ (V "sp_wots" (spWotsArgs σ l.val) (spWotsRets σ l.val)) l.val l =
      sLayerOf σ V l := by
  obtain ⟨ha, hb, he, hf, hc⟩ := sLayerPositions l.val l.isLt
  apply layerSignature_ext
  · simp only [layerA, sLayerOf, hc]
    rfl
  · funext i
    simp only [layerA, sLayerOf, spWotsArgs, spWotsRets, layerChains_eq, ha, hb, he, hf, sPP]
  · funext j
    have hj := j.isLt
    unfold Sphincs.layerHeight at hj
    obtain ⟨hk, hbit⟩ := sPathPositions l.val l.isLt j.val (by split at hj <;> omega)
      (by split at hj <;> omega)
    have e1 : spTabs.pathBit = tabA spPathBits := rfl
    have e2 : spTabs.pathKid = tabA spPathKids := rfl
    simp only [layerA, sLayerOf, e1, e2, offAtA_tabA, hk, hbit, siblingOf, sibN]
    rfl

/-- **The readers are equal**: off the frame map re-keyed by index, the reader is the witness
`sphincsSigOf` (`B1/Sig/SphincsSig.lean`). -/
theorem sphincsSigOfN_eq (σ : Val) (V : FrameMap) :
    sphincsSigOfN σ (fun k ↦ V (decoderFunctionName k)) = sphincsSigOf σ V := by
  apply signature_ext
  · rfl
  · exact funext fun c ↦ forsOpeningA_eq σ c.isLt
  · funext l
    simp only [sphincsSigOfN, sphincsSigOfA, sphincsSigOf, name_sp_wots]
    match l with
    | ⟨0, _⟩ => exact layerA_eq σ V 0
    | ⟨1, _⟩ => exact layerA_eq σ V 1
    | ⟨2, _⟩ => exact layerA_eq σ V 2

end
end LeanVM.Guest.Fast
