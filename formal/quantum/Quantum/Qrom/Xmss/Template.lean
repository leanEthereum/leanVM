module

public import Quantum.Qrom.Xmss.Classify
public import Quantum.Qrom.Xmss.GameReads
public import Quantum.Xmss.Assembly.Template

@[expose] public section

/-!
# leanXMSS's runtime-2 game in the QROM, as a template program

Runtime 2 of the QROM hybrid (design, section 2.1, G4): no cell hardwired at the start; a cell of
the honest table is hardwired (program port) only once its input and value are public; the hidden
values enter the game only through reveal ports. The template machinery is the QRPM's
(`Quantum.Xmss.Assembly.Template`: `tmplSpec`, `revealThen`, `progThen`, `readLiftQ`, `realizeT`,
`runtimeR`, `Disc`), at `X := HashOutput`, `Z := HashDomain`; no public data, no
reparametrization.

**Hidden coordinates** (`HPos := Option Pos × Bool`, a `Digest` each): the low (`false`) and high
(`true`) 128-bit halves of the master seed `S_0` (`none`) and of each position's value. The halves
matter at the chain-start derivations: one hash output starts two chains, and a signature opening
one of them at `0` reveals only its half. `tabOf θ`, `seedOf θ`: the table and master seed of the
hidden values `θ`; `thetaOf S0 v` is their inverse (`thetaEquiv`).

**Ports.** `progT p` hardwires the cell of a structural position `p` (chain step, leaf, node) with
its value, both functions of the coordinates `progNeed p` (the parameter, the values the input
reads, and `p`'s two halves); at `θ` it realizes `programH (cellOf S0 p (tabOf θ)) (tabOf θ p)`
for every `S0` (`realize_progT`). A trial read of key `(l, e)` reads the message-digest cell
through a read port updating the memory with `upd l e z` (`TrialUpd`; the canonical `cwUpd` at
`SelMem` records codeword selections).

* `selectT`: reveal the randomizer base's low half, then the randomizer search through read
  ports (`grindT`). `publishT`: reveal `layerReveal l e x` (the coordinates of the positions the
  layer signature makes public, `layerPos`, and of the opened values and the path), program those
  positions, and read the layer signature from the revealed values. `signT`: the bottom layer's
  search, the bottom root revealed (`rootReveal`), the top layer's search on it; both layers are
  published only when both searches succeed (the signer returns `none` otherwise, disclosing
  nothing). Both searches always run, so that the memory records every request's selections.
* `gameT M upd A`: reveal the public key (parameter and root), the adversary against
  `challengeT` (hash calls on port `h`, signing requests by `signT`), the verification through
  read ports, the winning condition. `prefixT`, `verifyT`, `gameT_eq_prefixT_bind`.
* `disc_gameT`, `disc_prefixT`, `viewBy_gameT`, `viewByOn_gameT`: the game reveals before it
  programs, hence the lazy-sampling property of the realized games in `runtimeR`.
-/

open Matrix
open scoped ENNReal

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open LeanXmss HashSig
open Quantum.Xmss (leafKey leafKey_val)
open Quantum.Xmss.Assembly (tmplSpec recHwSpec recSpec runtimeR realizeT revealThen progThen
  readLift readLiftQ RevealVals Disc disc_revealThen disc_progThen disc_readLift disc_act
  disc_bind disc₂_bind disc_substitute viewBy_runtimeR_of_disc revealThen_bind)

/-! ## Halves of a hash output -/

/-- The hash output with low half `lo` and high half `hi`. -/
def joinHalves (lo hi : Digest) : HashOutput :=
  hi ++ lo

theorem getLsbD_joinHalves (lo hi : Digest) (j : ℕ) :
    (joinHalves lo hi).getLsbD j = if j < 128 then lo.getLsbD j else hi.getLsbD (j - 128) :=
  BitVec.getLsbD_append (x := hi) (y := lo) (i := j)

theorem truncateHash_joinHalves (lo hi : Digest) : truncateHash (joinHalves lo hi) = lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj : j < 128 := hj
  simp only [truncateHash, digestBits, BitVec.getLsbD_extractLsb', getLsbD_joinHalves]
  simp [hj]

theorem upperHalfOfHash_joinHalves (lo hi : Digest) :
    upperHalfOfHash (joinHalves lo hi) = hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj : j < 128 := hj
  simp only [upperHalfOfHash, digestBits, BitVec.getLsbD_extractLsb', getLsbD_joinHalves]
  simp [hj]

theorem joinHalves_halves (y : HashOutput) :
    joinHalves (truncateHash y) (upperHalfOfHash y) = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj : j < 256 := hj
  rw [getLsbD_joinHalves]
  by_cases h : j < 128
  · simp only [h, ↓reduceIte, truncateHash, digestBits, BitVec.getLsbD_extractLsb']
    simp
  · simp only [h, ↓reduceIte, upperHalfOfHash, digestBits, BitVec.getLsbD_extractLsb']
    rw [show 128 + (j - 128) = j by omega]
    simp [show j - 128 < 128 by omega]

/-! ## Hidden coordinates and values -/

/-- **The hidden coordinates**: the low (`false`) and high (`true`) halves of the master seed
(`none`) and of each position's value. -/
abbrev HPos : Type := Option Pos × Bool

/-- A digest per hidden coordinate. -/
abbrev HD : HPos → Type :=
  fun _ ↦ Digest

/-- The table of the hidden values. -/
def tabOf (θ : HPos → Digest) : QTable :=
  fun p ↦ joinHalves (θ (some p, false)) (θ (some p, true))

/-- The master seed of the hidden values. -/
def seedOf (θ : HPos → Digest) : MasterSeed :=
  joinHalves (θ (none, false)) (θ (none, true))

/-- The hidden values of a master seed and a table. -/
def thetaOf (S0 : MasterSeed) (v : QTable) : HPos → Digest
  | (none, false) => truncateHash S0
  | (none, true) => upperHalfOfHash S0
  | (some p, false) => truncateHash (v p)
  | (some p, true) => upperHalfOfHash (v p)

@[simp]
theorem tabOf_thetaOf (S0 : MasterSeed) (v : QTable) : tabOf (thetaOf S0 v) = v :=
  funext fun p ↦ joinHalves_halves (v p)

@[simp]
theorem seedOf_thetaOf (S0 : MasterSeed) (v : QTable) : seedOf (thetaOf S0 v) = S0 :=
  joinHalves_halves S0

theorem thetaOf_seedOf_tabOf (θ : HPos → Digest) : thetaOf (seedOf θ) (tabOf θ) = θ := by
  funext s
  rcases s with ⟨_ | p, _ | _⟩
  · exact truncateHash_joinHalves _ _
  · exact upperHalfOfHash_joinHalves _ _
  · exact truncateHash_joinHalves _ _
  · exact upperHalfOfHash_joinHalves _ _

/-- **The hidden values are the master seed and the table.** -/
def thetaEquiv : (HPos → Digest) ≃ MasterSeed × QTable where
  toFun θ := (seedOf θ, tabOf θ)
  invFun p := thetaOf p.1 p.2
  left_inv θ := thetaOf_seedOf_tabOf θ
  right_inv p := Prod.ext (seedOf_thetaOf p.1 p.2) (tabOf_thetaOf p.1 p.2)

/-- The low half of a position's value. -/
def loC (p : Pos) : HPos :=
  (some p, false)

/-- The high half of a position's value. -/
def hiC (p : Pos) : HPos :=
  (some p, true)

/-- The coordinate of the public parameter. -/
def paramC : HPos :=
  loC .param

/-- **The coordinate of a symbolic position's value** (`QTable.value`): the low half of its chain
step, leaf or node, and at chain position `0` the half of the seed derivation that starts the
chain (the parameter's coordinate out of range, where the value is `0`). -/
def vcoord : Quantum.Xmss.Pos → HPos
  | .chain l e i 0 => (some (.prf l e (chainPair i)), decide (i.val % 2 ≠ 0))
  | .chain l e i (j + 1) => if h : j < chainLength - 1 then loC (.chain l e i ⟨j, h⟩) else paramC
  | .tree l 0 index => loC (.leaf l (leafKey index))
  | .tree l (level + 1) index =>
      if h : level < layerHeight ∧ index < 2 ^ (31 - level) then
        loC (.node l ⟨level, h.1⟩ ⟨index, h.2⟩)
      else paramC

theorem param_tabOf (θ : HPos → Digest) : (tabOf θ).param = θ paramC :=
  truncateHash_joinHalves _ _

theorem vcoord_tree_succ (l : Layer) (level index : ℕ)
    (h : level < layerHeight ∧ index < 2 ^ (31 - level)) :
    vcoord (.tree l (level + 1) index) = loC (.node l ⟨level, h.1⟩ ⟨index, h.2⟩) :=
  dite_eq_left h

/-- **A value of the table reads one coordinate.** -/
theorem value_tabOf_congr {θ θ' : HPos → Digest} :
    ∀ q : Quantum.Xmss.Pos, θ (vcoord q) = θ' (vcoord q) →
      (tabOf θ).value q = (tabOf θ').value q
  | .chain l e i 0, h => by
    change hashHalfForChain i.val (tabOf θ _) = hashHalfForChain i.val (tabOf θ' _)
    unfold hashHalfForChain tabOf
    by_cases hi : i.val % 2 = 0
    · simp only [hi, ↓reduceIte]
      rw [truncateHash_joinHalves, truncateHash_joinHalves]
      simpa [vcoord, hi] using h
    · simp only [hi, ↓reduceIte]
      rw [upperHalfOfHash_joinHalves, upperHalfOfHash_joinHalves]
      simpa [vcoord, hi] using h
  | .chain l e i (j + 1), h => by
    change QTable.chainValue _ l e i (j + 1) = QTable.chainValue _ l e i (j + 1)
    simp only [QTable.chainValue]
    split_ifs with hj
    · simp only [vcoord, dite_eq_left hj, loC] at h
      simp only [tabOf, truncateHash_joinHalves]
      exact h
    · rfl
  | .tree l 0 index, h => by
    change truncateHash (tabOf θ _) = truncateHash (tabOf θ' _)
    simp only [tabOf, truncateHash_joinHalves]
    exact h
  | .tree l (level + 1) index, h => by
    change QTable.treeValue _ l (level + 1) index = QTable.treeValue _ l (level + 1) index
    simp only [QTable.treeValue]
    split_ifs with hl
    · simp only [vcoord, dite_eq_left hl, loC] at h
      simp only [tabOf, truncateHash_joinHalves]
      exact h
    · rfl

/-! ## Structural positions and their cells -/

/-- A structural position: a chain step, a leaf or a node. -/
def Pos.IsStruct : Pos → Prop
  | .chain .. | .leaf .. | .node .. => True
  | _ => False

/-- The symbolic positions whose values a structural position's input reads. -/
def cellDeps : Pos → Finset Quantum.Xmss.Pos
  | .chain l e i step => {.chain l e i step.val}
  | .leaf l e => Finset.univ.image fun i ↦ .chain l e i (chainLength - 1)
  | .node l k x => {.tree l k.val (2 * x.val), .tree l k.val (2 * x.val + 1)}
  | _ => ∅

/-- The coordinates a structural position's cell reads: the parameter and its input's values. -/
def cellNeed (p : Pos) : Finset HPos :=
  insert paramC ((cellDeps p).image vcoord)

/-- The coordinates a structural position's program port reads: its cell's and its value's. -/
def progNeed (p : Pos) : Finset HPos :=
  cellNeed p ∪ {loC p, hiC p}

theorem paramC_mem_cellNeed (p : Pos) : paramC ∈ cellNeed p :=
  Finset.mem_insert_self _ _

theorem vcoord_mem_cellNeed {p : Pos} {q : Quantum.Xmss.Pos} (hq : q ∈ cellDeps p) :
    vcoord q ∈ cellNeed p :=
  Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hq)

theorem cellNeed_subset_progNeed (p : Pos) : cellNeed p ⊆ progNeed p :=
  Finset.subset_union_left

theorem loC_mem_progNeed (p : Pos) : loC p ∈ progNeed p :=
  Finset.mem_union_right _ (by simp)

theorem hiC_mem_progNeed (p : Pos) : hiC p ∈ progNeed p :=
  Finset.mem_union_right _ (by simp)

/-- **A structural position's cell reads the coordinates `cellNeed p`**, not the master seed. -/
theorem cellOf_tabOf_congr {p : Pos} (hp : p.IsStruct) (S0 S0' : MasterSeed)
    {θ θ' : HPos → Digest} (h : ∀ s ∈ cellNeed p, θ s = θ' s) :
    cellOf S0 p (tabOf θ) = cellOf S0' p (tabOf θ') := by
  have hP : (tabOf θ).param = (tabOf θ').param := by
    rw [param_tabOf, param_tabOf]
    exact h _ (paramC_mem_cellNeed p)
  have hv : ∀ q ∈ cellDeps p, (tabOf θ).value q = (tabOf θ').value q := fun q hq ↦
    value_tabOf_congr q (h _ (vcoord_mem_cellNeed hq))
  unfold cellOf
  rw [hP]
  congr 1
  cases p with
  | chain l e i step => exact hv _ (Finset.mem_singleton_self _)
  | leaf l e =>
    exact funext fun i ↦ hv _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  | node l k x =>
    exact Prod.ext (hv _ (Finset.mem_insert_self _ _))
      (hv _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  | seed | param | prf | rndBottom | rndTop => exact absurd hp id

/-! ## Revealed values -/

/-- The values revealed on `T`, extended by `0`. -/
def extendT {T : Finset HPos} (w : RevealVals HD T) : HPos → Digest :=
  fun s ↦ if h : s ∈ T then w ⟨s, h⟩ else 0

theorem extendT_restrictTo {T : Finset HPos} {s : HPos} (h : s ∈ T) (θ : HPos → Digest) :
    extendT (restrictTo T θ) s = θ s := by
  rw [extendT, dite_eq_left h]
  rfl

/-- The table of the values revealed on `T`. -/
def tabR {T : Finset HPos} (w : RevealVals HD T) : QTable :=
  tabOf (extendT w)

/-! ## Template program ports -/

/-- Every template program port is allowed. -/
def goodQ : LazyProg HashOutput HashDomain HPos HD → Prop :=
  fun _ ↦ True

/-- **The program port of a structural position**: hardwire its cell to its value, both read
from the coordinates `progNeed p` (the master seed is not read: `0` stands for it). -/
def progT (p : Pos) : LazyProg HashOutput HashDomain HPos HD :=
  .programH (progNeed p) fun w ↦ (cellOf 0 p (tabR w), tabR w p)

theorem need_progT (p : Pos) : (progT p).need = progNeed p :=
  rfl

/-- **The program port of a structural position, realized**: its cell at any master seed, with
its value. -/
theorem realize_progT {p : Pos} (hp : p.IsStruct) (S0 : MasterSeed) (θ : HPos → Digest) :
    (progT p).realize θ = .programH (cellOf S0 p (tabOf θ)) (tabOf θ p) := by
  have hc : cellOf 0 p (tabR (restrictTo (progNeed p) θ)) = cellOf S0 p (tabOf θ) :=
    cellOf_tabOf_congr hp 0 S0 fun s hs ↦
      extendT_restrictTo (cellNeed_subset_progNeed p hs) θ
  have hv : tabR (restrictTo (progNeed p) θ) p = tabOf θ p :=
    congrArg₂ joinHalves (extendT_restrictTo (loC_mem_progNeed p) θ)
      (extendT_restrictTo (hiC_mem_progNeed p) θ)
  simp only [progT, LazyProg.realize, hc, hv]

/-! ## Layer signatures -/

theorem nodeIndex_lt (e : KeyIndex) (lev : Fin layerHeight) :
    e.val / 2 ^ (lev.val + 1) < 2 ^ (31 - lev.val) := by
  have he : e.val < 2 ^ 32 := e.isLt
  have hl : lev.val < 16 := lev.isLt
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
    show 31 - lev.val + (lev.val + 1) = 32 by omega]
  exact he

/-- The node at tree level `lev + 1` on key `e`'s path to the root. -/
def pathNode (l : Layer) (e : KeyIndex) (lev : Fin layerHeight) : Pos :=
  .node l lev ⟨e.val / 2 ^ (lev.val + 1), nodeIndex_lt e lev⟩

/-- **The positions a layer signature by key `e` with codeword `x` makes public**: the chain steps
from the opened positions, the leaf, and the nodes on the path to the root. -/
def layerPos (l : Layer) (e : KeyIndex) (x : Encoding) : List Pos :=
  (List.finRange chainCount).flatMap (fun i ↦ ((List.finRange (chainLength - 1)).filter
      fun step ↦ decide ((x i).val ≤ step.val)).map fun step ↦ Pos.chain l e i step) ++
    Pos.leaf l e :: (List.finRange layerHeight).map (pathNode l e)

theorem isStruct_of_mem_layerPos {l : Layer} {e : KeyIndex} {x : Encoding} {p : Pos}
    (hp : p ∈ layerPos l e x) : p.IsStruct := by
  simp only [layerPos, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_cons, List.mem_finRange, true_and] at hp
  rcases hp with ⟨i, step, -, rfl⟩ | rfl | ⟨lev, rfl⟩ <;> trivial

/-- The coordinates of a list of positions' program ports. -/
def needUnion : List Pos → Finset HPos
  | [] => ∅
  | p :: ps => progNeed p ∪ needUnion ps

theorem progNeed_subset_needUnion {p : Pos} {ps : List Pos} (h : p ∈ ps) :
    progNeed p ⊆ needUnion ps := by
  induction ps with
  | nil => exact absurd h List.not_mem_nil
  | cons p' ps ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Finset.subset_union_left
    · exact (ih h).trans Finset.subset_union_right

/-- The authentication-path sibling at `level` of key `e`. -/
def siblingQ (l : Layer) (e : KeyIndex) (level : Fin layerHeight) : Quantum.Xmss.Pos :=
  .tree l level.val (Nat.xor (e.val / 2 ^ level.val) 1)

/-- **The coordinates a layer signature reveals**: those of the positions it makes public, of the
opened chain values and of the authentication path. -/
def layerReveal (l : Layer) (e : KeyIndex) (x : Encoding) : Finset HPos :=
  needUnion (layerPos l e x) ∪ Finset.univ.image (fun i ↦ vcoord (.chain l e i (x i).val)) ∪
    Finset.univ.image (fun level ↦ vcoord (siblingQ l e level))

/-- The layer signature with randomizer `ρ` and codeword `x`, read from the table `t`. -/
def layerSigOf (t : QTable) (l : Layer) (e : KeyIndex) (ρ : Randomizer) (x : Encoding) :
    LayerSignature :=
  ⟨ρ, fun i ↦ t.chainValue l e i (x i).val, t.authPath l e⟩

/-! ## The template game -/

variable (M : Type) [Fintype M] [DecidableEq M]

/-- leanXMSS's template signature in the QROM, with inner memory `M`. -/
abbrev XSpec : QuantumOracleSpec.{0, 0} :=
  tmplSpec HashOutput HashDomain HPos HD M goodQ

/-- **The memory update of a trial read** of key `e` of layer `l` at the cell `z`. -/
abbrev TrialUpd : Type :=
  Layer → KeyIndex → HashDomain → M → Option HashOutput → M

/-- The trial update that keeps the memory. -/
def keepUpd : TrialUpd M :=
  fun _ _ _ ↦ keepMem

/-- The message-digest cell of trial `trial` of key `e` of layer `l` from the base `base`. -/
def trialCell (P : PublicParameter) (l : Layer) (e : KeyIndex) (message : MsgBytes)
    (base : Randomizer) (trial : ℕ) : HashDomain :=
  cell P (.msg l e) (message, base + BitVec.ofNat digestBits trial)

variable (upd : TrialUpd M)

/-- **The randomizer search through read ports**, as `otsSignFrom`: trials `base + c`, each
message digest read at its cell (updating the memory with `upd l e`), until a codeword. -/
noncomputable def grindT (P : PublicParameter) (B : QReg) (l : Layer) (e : KeyIndex)
    (message : MsgBytes) (base : Randomizer) :
    ℕ → ℕ → QComp (hwReadSpec HashOutput HashDomain M) B B (Option (Randomizer × Encoding))
  | 0, _ => QuantumComp₂.pure none
  | n + 1, trial =>
    (readCall (.readH (trialCell P l e message base trial)
      (upd l e (trialCell P l e message base trial))) B).bind fun r ↦
      match Codeword.decode (truncateHash (r.1.getD 0)) with
      | some x => QuantumComp₂.pure (some (base + BitVec.ofNat digestBits trial, x))
      | none => grindT P B l e message base n (trial + 1)

/-- Call the program ports of the positions `ps` in order. -/
noncomputable def progPos (B : QReg) : List Pos → QComp (XSpec M) B B Unit
  | [] => QuantumComp₂.pure ()
  | p :: ps => progThen (progT p) trivial (progPos B ps)

/-- **A layer's randomizer search in runtime 2**, by key `e` of layer `l` on `message`, the
randomizer base at position `rnd`: reveal the base, then search through read ports. -/
noncomputable def selectT (P : PublicParameter) (B : QReg) (l : Layer) (e : KeyIndex)
    (message : MsgBytes) (rnd : Pos) : QComp (XSpec M) B B (Option (Randomizer × Encoding)) :=
  revealThen goodQ {loC rnd} fun r₀ ↦
    readLiftQ goodQ (grindT M upd P B l e message (truncateHash (tabR r₀.1 rnd))
      randomizerAttemptLimit 0)

/-- **Publishing a layer signature** with randomizer `ρ` and codeword `x`: reveal the layer's
coordinates, hardwire the positions it makes public, and read the signature from the revealed
values. -/
noncomputable def publishT (B : QReg) (l : Layer) (e : KeyIndex) (ρ : Randomizer)
    (x : Encoding) : QComp (XSpec M) B B LayerSignature :=
  revealThen goodQ (layerReveal l e x) fun r ↦
    (progPos M B (layerPos l e x)).bind fun _ ↦ QuantumComp₂.pure (layerSigOf (tabR r.1) l e ρ x)

/-- The coordinate of the bottom root under a request's top key. -/
def rootReveal (r : SigningRequest) : Finset HPos :=
  {vcoord (.tree bottomLayer layerHeight (keyIndexOnLayer r.leafIndex topLayer).val)}

/-- **A signature in runtime 2**, as `sign`: the bottom layer's search on the message, the bottom
root revealed, the top layer's search on it; only when both find a codeword are the two layer
signatures published (the signer returns nothing otherwise). -/
noncomputable def signT (P : PublicParameter) (B : QReg) (r : SigningRequest) :
    QComp (XSpec M) B B (Option Signature) :=
  (selectT M upd P B bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer)
    (messageBytes r.message) (.rndBottom (keyIndexOnLayer r.leafIndex bottomLayer) r.message)).bind
    fun gb ↦ revealThen goodQ (rootReveal r) fun rr ↦
      (selectT M upd P B topLayer (keyIndexOnLayer r.leafIndex topLayer)
        (rootBytes ((tabR rr.1).bottomRoot r.leafIndex))
        (.rndTop (keyIndexOnLayer r.leafIndex topLayer)
          ((tabR rr.1).bottomRoot r.leafIndex))).bind fun gt ↦
        match gb, gt with
        | some (ρb, xb), some (ρt, xt) =>
          (publishT M B bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer) ρb xb).bind
            fun bottom ↦
            (publishT M B topLayer (keyIndexOnLayer r.leafIndex topLayer) ρt xt).bind fun top ↦
              QuantumComp₂.pure
                (some ⟨r.leafIndex, fun lay ↦ if lay = bottomLayer then bottom else top⟩)
        | _, _ => QuantumComp₂.pure none

/-- The answer to the signing request `r` with the adversary's register held. -/
noncomputable def signAt (P : PublicParameter) (r : SigningRequest) (E : QReg) {A : QReg}
    (ℓ : A ≃ (SufCma.advSpec SigningRequest (Option Signature)).In (.sign r) × E) :
    QComp (XSpec M) A
      (QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E))
      (Option Signature) :=
  (QComp.act (spec := XSpec M)
    (B := QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ signT M upd P _ r

/-- A secret key carrying nothing: the challenger's local operations and hash calls do not read
the key. -/
def noKey : SecretKey :=
  ⟨0, 0⟩

/-- **The challenger of runtime 2**: a local operation and a hash call as in `challengeReads`
(hash calls on port `h`), a signing request answered by `signT`. -/
noncomputable def challengeT (P : PublicParameter) :
    IPFunctor.CommandSubstitution
      (QuantumComp.toIPFunctor LocalSig.instruments.{0}
        (SufCma.advSpec SigningRequest (Option Signature)))
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (XSpec M))
  | A, .prim o => readLift goodQ ((liftH (SufCma.challenge xmssRom noKey A (.prim o))).liftOrdinary
      (t := hwReadCmdSpec HashOutput HashDomain M))
  | A, .query .hash E ℓ => readLift goodQ ((liftH (SufCma.challenge xmssRom noKey A
      (.query .hash E ℓ))).liftOrdinary (t := hwReadCmdSpec HashOutput HashDomain M))
  | _, .query (.sign r) E ℓ =>
      QuantumComp.bind (signAt M upd P r E ℓ) fun _ l ↦ QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- The adversary's program against the challenger of runtime 2. -/
noncomputable def challengedT (P : PublicParameter) {A B : QReg} {α : Type}
    (x : QComp (SufCma.advSpec SigningRequest (Option Signature)) A B α) : QComp (XSpec M) A B α :=
  IPFunctor.IFreeM.substitute (challengeT M upd P) x

/-- The root's position: the top layer's node at tree level `16`. -/
def rootPos : Pos :=
  .node topLayer ⟨15, by decide⟩ ⟨0, by decide⟩

/-- The coordinates of the public key: the parameter and the root. -/
def pkReveal : Finset HPos :=
  {paramC, loC rootPos}

/-- The public key read from revealed values. -/
def pkT {T : Finset HPos} (w : RevealVals HD T) : PublicKey :=
  (tabR w).publicKey

/-- **The SUF-CMA game as runtime 2 runs it, as a template**: reveal the public key, run the
adversary on it against the challenger of runtime 2 with its signing transcript (trial reads
updating the memory with `upd`), verify the forgery through read ports, and return the winning
condition. `realizeT θ (gameT M upd A)` is the game at the hidden values `θ`. -/
noncomputable def gameT (A : Adversary) : QComp (XSpec M) (QReg.of Unit) (QReg.of Unit) Bool :=
  revealThen goodQ pkReveal fun r₀ ↦
    (challengedT M upd (pkT r₀.1).parameter (SufCma.withSignLog (A (pkT r₀.1)))).bind
      fun run ↦
      (readLiftQ goodQ ((readsProgram M _ (xmssRom.verify (pkT r₀.1) run.1)).map
        Prod.fst)).bind fun verified ↦
        QuantumComp₂.pure (xmssRom.winningCondition run.2 run.1 && verified)

/-- **The challenge prefix of the game**: reveal the public key and run the adversary on it
against the challenger of runtime 2 with its signing transcript; return the public key, the
forgery and the transcript. -/
noncomputable def prefixT (A : Adversary) :
    QComp (XSpec M) (QReg.of Unit) (QReg.of Unit) (PublicKey × (Forgery × SignLog)) :=
  revealThen goodQ pkReveal fun r₀ ↦
    (challengedT M upd (pkT r₀.1).parameter (SufCma.withSignLog (A (pkT r₀.1)))).bind
      fun run ↦ QuantumComp₂.pure (pkT r₀.1, run)

/-- **The verification of the game** through read ports, and the winning condition. -/
noncomputable def verifyT (x : PublicKey × (Forgery × SignLog)) :
    QComp (XSpec M) (QReg.of Unit) (QReg.of Unit) Bool :=
  (readLiftQ goodQ ((readsProgram M _ (xmssRom.verify x.1 x.2.1)).map Prod.fst)).bind
    fun verified ↦ QuantumComp₂.pure (xmssRom.winningCondition x.2.2 x.2.1 && verified)

omit [Fintype M] [DecidableEq M] in
/-- **The game is its challenge prefix, then the verification.** -/
theorem gameT_eq_prefixT_bind (A : Adversary) :
    gameT M upd A = (prefixT M upd A).bind (verifyT M) := by
  simp only [gameT, prefixT, revealThen_bind, QuantumComp₂.bind_assoc, QuantumComp₂.pure_bind]
  rfl

/-! ## The game reveals before it programs -/

attribute [local irreducible] xmssRom

omit [Fintype M] [DecidableEq M] in
theorem disc_progPos (B : QReg) (ps : List Pos) (T : Finset HPos)
    (h : ∀ p ∈ ps, progNeed p ⊆ T) : Disc (progPos M B ps) T := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact disc_progThen _ trivial _ T (h p List.mem_cons_self)
      (ih fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

omit [Fintype M] [DecidableEq M] in
theorem disc_selectT (P : PublicParameter) (B : QReg) (l : Layer) (e : KeyIndex)
    (message : MsgBytes) (rnd : Pos) (T : Finset HPos) :
    Disc (selectT M upd P B l e message rnd) T :=
  disc_revealThen _ _ T fun _ ↦ disc_readLift _ _

omit [Fintype M] [DecidableEq M] in
theorem disc_publishT (B : QReg) (l : Layer) (e : KeyIndex) (ρ : Randomizer) (x : Encoding)
    (T : Finset HPos) : Disc (publishT M B l e ρ x) T := by
  refine disc_revealThen _ _ T fun r ↦
    disc₂_bind _ _ (disc_progPos M B _ _ fun p hp ↦ ?_) fun _ _ _ ↦ trivial
  exact ((progNeed_subset_needUnion hp).trans (Finset.subset_union_left.trans
    Finset.subset_union_left)).trans Finset.subset_union_right

omit [Fintype M] [DecidableEq M] in
theorem disc_signT (P : PublicParameter) (B : QReg) (r : SigningRequest) (T : Finset HPos) :
    Disc (signT M upd P B r) T := by
  refine disc₂_bind _ _ (disc_selectT M upd P B _ _ _ _ T) fun gb T' _ ↦ ?_
  refine disc_revealThen _ _ T' fun _ ↦
    disc₂_bind _ _ (disc_selectT M upd P B _ _ _ _ _) fun gt T'' _ ↦ ?_
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  · trivial
  · trivial
  · trivial
  · exact disc₂_bind _ _ (disc_publishT M B _ _ _ _ T'') fun _ T₃ _ ↦
      disc₂_bind _ _ (disc_publishT M B _ _ _ _ T₃) fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem disc_challengeT (P : PublicParameter) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0}
      (SufCma.advSpec SigningRequest (Option Signature)) A) (T : Finset HPos) :
    Disc (challengeT M upd P A c) T := by
  rcases c with o | ⟨_ | r, E, ℓ⟩
  · exact disc_readLift _ _
  · exact disc_readLift _ _
  · exact disc_bind _ _ (disc₂_bind _ _ (disc_act _ _) fun _ T' _ ↦ disc_signT M upd P _ r T')
      fun _ _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- The challenge prefix reveals before it programs. -/
theorem disc_prefixT (A : Adversary) (T : Finset HPos) : Disc (prefixT M upd A) T :=
  disc_revealThen _ _ T fun _ ↦ disc₂_bind _ _
    (disc_substitute _ (disc_challengeT M upd _) _ _) fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- The verification never programs. -/
theorem disc_verifyT (x : PublicKey × (Forgery × SignLog)) (T : Finset HPos) :
    Disc (verifyT M x) T := by
  unfold verifyT
  generalize (readsProgram M _ (xmssRom.verify x.1 x.2.1)).map Prod.fst = y
  exact disc₂_bind _ _ (disc_readLift _ T) fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- **The game reveals before it programs**: every program port hardwires a position whose
coordinates the layer signature revealed just before. -/
theorem disc_gameT (A : Adversary) (T : Finset HPos) : Disc (gameT M upd A) T := by
  rw [gameT_eq_prefixT_bind]
  exact disc₂_bind (prefixT M upd A) (verifyT M) (disc_prefixT M upd A T) fun x T' _ ↦
    disc_verifyT M x T'

/-- **The lazy-sampling property of the runtime-2 game.** For every initial state that does not
depend on the hidden values, the realized games satisfy `ViewBy` for runtime 2 with record ports
and the memory label, at every call. -/
theorem viewBy_gameT (A : Adversary) (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset HPos × M))) ℂ) (j : ℕ) :
    ViewBy (runtimeR m₀) LocalSig.Interp.instruments (fun r ↦ r.2.2.1)
      (fun θ ↦ realizeT θ (gameT M upd A)) (fun _ ↦ ρ) j :=
  viewBy_runtimeR_of_disc _ m₀ (gameT M upd A) ∅ (disc_gameT M upd A ∅) (fun _ ↦ ρ)
    (lazy_const _ ρ) (fun _ ↦ suppAt_empty _ ρ) j

/-- **`ViewByOn` for the runtime-2 game**: the `hview` hypothesis of the hidden-mass bounds, for
weights vanishing on the program ports. -/
theorem viewByOn_gameT (A : Adversary) (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset HPos × M))) ℂ) (j : ℕ) :
    ViewByOn (runtimeR m₀) LocalSig.Interp.instruments (fun i ↦ i.isLeft = true)
      (fun r ↦ r.2.2.1) (fun θ ↦ realizeT θ (gameT M upd A)) (fun _ ↦ ρ) j :=
  (viewBy_gameT M upd A m₀ ρ j).viewByOn _

/-! ## The canonical game -/

/-- **The canonical runtime-2 game** at the hidden values `θ`: the trials' reads record codeword
selections in `SelMem` (`cwUpd`). -/
noncomputable def gameQ (A : Adversary) (θ : HPos → Digest) :
    QComp (recHwSpec HashOutput HashDomain HPos SelMem) (QReg.of Unit) (QReg.of Unit) Bool :=
  realizeT θ (gameT SelMem cwUpd A)

/-- The canonical challenge prefix at `θ`. -/
noncomputable def prefixQ (A : Adversary) (θ : HPos → Digest) :
    QComp (recHwSpec HashOutput HashDomain HPos SelMem) (QReg.of Unit) (QReg.of Unit)
      (PublicKey × (Forgery × SignLog)) :=
  realizeT θ (prefixT SelMem cwUpd A)

end Quantum.Qrom.Xmss

end
