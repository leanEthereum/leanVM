module

public import Quantum.Qrom.Sphincs.Stream
public import Quantum.Qrom.Sphincs.GameReads
public import Quantum.Qrom.Sphincs.Classify

@[expose] public section

/-!
# leanSPHINCS's runtime-2 game in the QROM, as a template program

Runtime 2 of the QROM hybrid (design, section 2.1, G4) for leanSPHINCS: no cell hardwired at the
start; a cell of the honest table is hardwired (program port) only once its input and value are
public; the hidden values enter the game only through reveal ports. The template machinery is the
QRPM's (`Quantum.Xmss.Assembly.Template`: `tmplSpec`, `revealThen`, `progThen`, `readLiftQ`,
`realizeT`, `runtimeR`, `Disc`), at `X := PairOut`, `Z := HashDomain` (the regrouped function, a
pair per cell); no public data, no reparametrization.

**Hidden coordinates** (`TPos := SPos (Option Pos) Message N`, `N = signatureLimit`, a pair each,
nothing at a mark; `Quantum.Qrom.Sphincs.Stream`): the master seed `S_0` (`.val none`, its first
component), each position's value (`.val (some p)`), each message's digest cell (`.dig M`), the
digest stream (`.str j`) and the stream marks (`.asg M j`). `tabOf θ`, `seedOf θ`: the table (a
digest cell's value at `.dig M`) and the master seed of the hidden values `θ`; `thetaOf S0 v`
inverts them (`tabOf_thetaOf`, `seedOf_thetaOf`). The coordinates `.val (some (digPos M))`, the
second component of the seed's, the stream and the marks do not enter the table.

**Coordinates of values** (`rawC`, `chainC`, `treeC`, `forsC`, `vcoord`, mirroring `QTable.out`,
`chainValue`, `treeValue`, `forsValue`, `valuePos`): a value of `tabOf θ` reads one coordinate
(`chainValue_tabOf_congr`, ...). `seedC`, `rootC`, `rndC M`: `PK.seed`, `PK.root`, `R(M)`.

**Ports.** `progT p` hardwires the cell of a structural position `p` (`RawPos.IsStruct`: chain
step, leaf, node, FORS leaf, node, roots) with its value, both functions of the coordinates
`progNeed p` (`PK.seed`, the values the input reads, `p`'s own); at `θ` it realizes
`programH (cellOf S0 p (tabOf θ)) (tabOf θ p)` for every `S0` (`realize_progT`). `digPort pol L M`
hardwires `M`'s digest cell with the pair at the digest policy's coordinate `pol.out L M`; at
`msgPol` it realizes the digest cell's program port (`realize_digPort_msgPol`). A trial read of key
`K` reads the encoding cell through a read port updating the memory with `upd K z` (`TrialUpd`).

**Digest policies** (`DigestPolicy`): from the memory label `L` before a signature, the coordinate
holding `M`'s digest pair and the coordinates revealed with it. `msgPol` (hybrid side): `.dig M`.
`strPol` (event side): the stream entry of `M` in first-request order, marked (`strNeed`,
`strOut`), `.dig M` past `N` entries.

* `signT pol M`: reveal `PK.seed`, `PK.root`, `R(M)` (the label before is `L`), reveal
  `pol.need L M`, program the digest cell; the counter searches of the three layers' keys
  (`selectT`: reveal the value the key signs, the trials through read ports, `grindT`); when all
  three succeed (`publishAllT`), the FORS opening (`forsOpenT`: reveal `forsReveal`, program
  `forsPos`) and the layer signatures (`publishT`: reveal `layerReveal`, program `layerPos`). A
  failed search publishes nothing, as the signer then discloses nothing.
* `gameT M upd pol A`: reveal the public key, the adversary against `challengeT` (local operations
  and hash calls regrouped and lifted, signing requests by `signT`), the verification through read
  ports, the winning condition. `prefixT`, `verifyT`, `gameT_eq_prefixT_bind`.
* `disc_gameT`, `disc_prefixT`, `keepsLab_gameT`, `keepsLab_prefixT`, `viewBy_gameT`,
  `viewByOn_gameT`: the game reveals before it programs and its reads keep the label, hence the
  lazy-sampling property of the realized games in `runtimeR`.
-/

open Matrix
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime
open Quantum.Sponge (hwReadSpec hwReadCmdSpec HwReg keepMem readCall)
open Quantum.Sphincs (ValPos Key keyOf msgPos)
open Quantum.Xmss.Hybrid (LazyProg restrictTo ViewBy ViewByOn lazy_const suppAt_empty KeepsLab
  keepsLab_bind keepsLab₂_bind keepsLab_substitute keepsLab_act keepsLab_revealThen
  keepsLab_progThen keepsLab_readLift)
open Quantum.Xmss.Assembly (tmplSpec runtimeR realizeT revealThen progThen readLift readLiftQ
  RevealVals Disc disc_revealThen disc_progThen disc_readLift disc_act disc_bind disc₂_bind
  disc_substitute viewBy_runtimeR_of_disc revealThen_bind)

/-! ## Hidden coordinates and values -/

/-- **The hidden coordinates**: the master seed (`.val none`), the table's positions
(`.val (some p)`), each message's digest cell, the digest stream and the stream marks. -/
abbrev TPos : Type :=
  SPos (Option Pos) Message signatureLimit

/-- A pair of hash outputs per coordinate, nothing at a mark. -/
abbrev TVal : TPos → Type :=
  SVal PairOut

/-- **The hidden values.** -/
abbrev TVals : Type :=
  (s : TPos) → TVal s

/-- The pair a coordinate holds (`0` at a mark). -/
def pairAt (θ : TVals) : TPos → PairOut
  | .val p => θ (.val p)
  | .dig m => θ (.dig m)
  | .str j => θ (.str j)
  | .asg _ _ => 0

/-- **The coordinate of a position's value**: the digest coordinate for a digest cell, the
position's own otherwise. -/
def coordOf (p : Pos) : TPos :=
  match p.1 with
  | .hmsg m => .dig m
  | _ => .val (some p)

/-- **The table of the hidden values.** -/
def tabOf (θ : TVals) : QTable :=
  fun p ↦ pairAt θ (coordOf p)

/-- **The master seed of the hidden values.** -/
def seedOf (θ : TVals) : MasterSeed :=
  (θ (.val none) : PairOut).1

/-- **The hidden values of a master seed and a table**: the pads are `0`. -/
def thetaOf (S0 : MasterSeed) (v : QTable) : TVals
  | .val none => ((S0, 0) : PairOut)
  | .val (some p) => v p
  | .dig m => v (digPos m)
  | .str _ => (0 : PairOut)
  | .asg _ _ => ()

@[simp]
theorem tabOf_thetaOf (S0 : MasterSeed) (v : QTable) : tabOf (thetaOf S0 v) = v := by
  funext p
  obtain ⟨q, hq⟩ := p
  cases q <;> rfl

@[simp]
theorem seedOf_thetaOf (S0 : MasterSeed) (v : QTable) : seedOf (thetaOf S0 v) = S0 :=
  rfl

theorem tabOf_digPos (θ : TVals) (m : Message) : tabOf θ (digPos m) = pairAt θ (.dig m) :=
  rfl

/-! ## Revealed values -/

/-- The table of the values revealed on `T` (a default value off `T`). -/
noncomputable def tabR {T : Finset TPos} (w : RevealVals TVal T) : QTable :=
  tabOf (extW w)

/-- The pair revealed at a coordinate (a default value off `T`). -/
noncomputable def pairR {T : Finset TPos} (w : RevealVals TVal T) (s : TPos) : PairOut :=
  pairAt (extW w) s

theorem extW_restrictTo {T : Finset TPos} {s : TPos} (h : s ∈ T) (θ : TVals) :
    extW (restrictTo T θ) s = θ s :=
  extW_of_mem _ h

theorem pairAt_extW_restrictTo {T : Finset TPos} {s : TPos} (h : s ∈ T) (θ : TVals) :
    pairAt (extW (restrictTo T θ)) s = pairAt θ s := by
  cases s with
  | val p => exact extW_restrictTo h θ
  | dig m => exact extW_restrictTo h θ
  | str j => exact extW_restrictTo h θ
  | asg m j => rfl

theorem pairR_restrictTo {T : Finset TPos} {s : TPos} (h : s ∈ T) (θ : TVals) :
    pairR (restrictTo T θ) s = pairAt θ s :=
  pairAt_extW_restrictTo h θ

/-! ## Coordinates of values -/

/-- The coordinate of `PK.seed`. -/
def seedC : TPos :=
  .val (some ⟨.publicSeed, trivial⟩)

/-- **The coordinate of a hash call's value**, `seedC` out of range (where the value is `0`). -/
def rawC (q : RawPos) : TPos :=
  if h : q.InRange then coordOf ⟨q, h⟩ else seedC

/-- The coordinate of position `j` of chain `i` of the key `(l, τ, e)` (as `chainValue`). -/
def chainC (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) : ℕ → TPos
  | 0 => rawC (.chainStart l τ e i)
  | j + 1 => if h : j < chainLength - 1 then rawC (.chain l τ e i ⟨j, h⟩) else seedC

/-- The coordinate of a tree value (as `treeValue`). -/
def treeC (l : Layer) (τ : TreeIndex) : ℕ → ℕ → TPos
  | 0, index => rawC (.leaf l τ (leafOfNat index))
  | level + 1, index =>
      if h : level < layerHeight topLayer ∧ index < 2 ^ layerHeight topLayer then
        rawC (.node l τ ⟨level, h.1⟩ ⟨index, h.2⟩)
      else seedC

/-- The coordinate of a FORS tree value (as `forsValue`). -/
def forsC (idx : Index) (κ : ForsTreeIndex) : ℕ → ℕ → TPos
  | 0, j => rawC (.forsLeaf idx κ (forsLeafOfNat j))
  | h + 1, j =>
      if hh : h < forsTreeHeight ∧ j < 2 ^ forsTreeHeight then
        rawC (.forsNode idx κ ⟨h, hh.1⟩ ⟨j, hh.2⟩)
      else seedC

/-- **The coordinate of a symbolic position's value** (`QTable.valuePos`). -/
def vcoord : ValPos → TPos
  | .chain l τ e i j => chainC l τ e i j.val
  | .tree l τ level index => treeC l τ level.val index.val
  | .forsSecret idx κ s => rawC (.forsSecret idx κ s)
  | .forsTree idx κ height node => forsC idx κ height.val node.val
  | .forsKey idx => rawC (.forsRoots idx)

/-- The coordinate of `PK.root`. -/
def rootC : TPos :=
  treeC topLayer 0 (layerHeight topLayer) 0

/-- The coordinate of the randomizer `R(M)`. -/
def rndC (msg : Message) : TPos :=
  rawC (.prfMsg msg)

theorem rawC_publicSeed : rawC .publicSeed = seedC :=
  rfl

section congr

variable {θ θ' : TVals}

theorem out_tabOf_congr {q : RawPos} (h : pairAt θ (rawC q) = pairAt θ' (rawC q)) :
    (tabOf θ).out q = (tabOf θ').out q := by
  unfold QTable.out
  split_ifs with hq
  · simp only [rawC, hq, ↓reduceDIte] at h
    exact congrArg Prod.fst h
  · rfl

theorem dig_tabOf_congr {q : RawPos} (h : pairAt θ (rawC q) = pairAt θ' (rawC q)) :
    (tabOf θ).dig q = (tabOf θ').dig q :=
  congrArg truncateHash (out_tabOf_congr h)

theorem publicSeed_tabOf_congr (h : pairAt θ seedC = pairAt θ' seedC) :
    (tabOf θ).publicSeed = (tabOf θ').publicSeed :=
  dig_tabOf_congr h

theorem chainValue_tabOf_congr {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} {i : ChainIndex}
    {j : ℕ} (h : pairAt θ (chainC l τ e i j) = pairAt θ' (chainC l τ e i j)) :
    (tabOf θ).chainValue l τ e i j = (tabOf θ').chainValue l τ e i j := by
  cases j with
  | zero => exact dig_tabOf_congr h
  | succ j =>
    change (if h : j < chainLength - 1 then (tabOf θ).dig (.chain l τ e i ⟨j, h⟩) else 0) =
      if h : j < chainLength - 1 then (tabOf θ').dig (.chain l τ e i ⟨j, h⟩) else 0
    change pairAt θ (if h : j < chainLength - 1 then rawC (.chain l τ e i ⟨j, h⟩) else seedC) =
      pairAt θ' (if h : j < chainLength - 1 then rawC (.chain l τ e i ⟨j, h⟩) else seedC) at h
    by_cases hj : j < chainLength - 1
    · simp only [hj, ↓reduceDIte] at h ⊢
      exact dig_tabOf_congr h
    · simp only [hj, ↓reduceDIte]

theorem treeValue_tabOf_congr {l : Layer} {τ : TreeIndex} {level index : ℕ}
    (h : pairAt θ (treeC l τ level index) = pairAt θ' (treeC l τ level index)) :
    (tabOf θ).treeValue l τ level index = (tabOf θ').treeValue l τ level index := by
  cases level with
  | zero => exact dig_tabOf_congr h
  | succ level =>
    change (if h : level < layerHeight topLayer ∧ index < 2 ^ layerHeight topLayer then
        (tabOf θ).dig (.node l τ ⟨level, h.1⟩ ⟨index, h.2⟩) else 0) =
      if h : level < layerHeight topLayer ∧ index < 2 ^ layerHeight topLayer then
        (tabOf θ').dig (.node l τ ⟨level, h.1⟩ ⟨index, h.2⟩) else 0
    change pairAt θ (if h : level < layerHeight topLayer ∧ index < 2 ^ layerHeight topLayer then
        rawC (.node l τ ⟨level, h.1⟩ ⟨index, h.2⟩) else seedC) =
      pairAt θ' (if h : level < layerHeight topLayer ∧ index < 2 ^ layerHeight topLayer then
        rawC (.node l τ ⟨level, h.1⟩ ⟨index, h.2⟩) else seedC) at h
    by_cases hl : level < layerHeight topLayer ∧ index < 2 ^ layerHeight topLayer
    · simp only [hl, and_self, ↓reduceDIte] at h ⊢
      exact dig_tabOf_congr h
    · simp only [hl, ↓reduceDIte]

theorem forsValue_tabOf_congr {idx : Index} {κ : ForsTreeIndex} {height node : ℕ}
    (h : pairAt θ (forsC idx κ height node) = pairAt θ' (forsC idx κ height node)) :
    (tabOf θ).forsValue idx κ height node = (tabOf θ').forsValue idx κ height node := by
  cases height with
  | zero => exact dig_tabOf_congr h
  | succ height =>
    change (if hh : height < forsTreeHeight ∧ node < 2 ^ forsTreeHeight then
        (tabOf θ).dig (.forsNode idx κ ⟨height, hh.1⟩ ⟨node, hh.2⟩) else 0) =
      if hh : height < forsTreeHeight ∧ node < 2 ^ forsTreeHeight then
        (tabOf θ').dig (.forsNode idx κ ⟨height, hh.1⟩ ⟨node, hh.2⟩) else 0
    change pairAt θ (if hh : height < forsTreeHeight ∧ node < 2 ^ forsTreeHeight then
        rawC (.forsNode idx κ ⟨height, hh.1⟩ ⟨node, hh.2⟩) else seedC) =
      pairAt θ' (if hh : height < forsTreeHeight ∧ node < 2 ^ forsTreeHeight then
        rawC (.forsNode idx κ ⟨height, hh.1⟩ ⟨node, hh.2⟩) else seedC) at h
    by_cases hh : height < forsTreeHeight ∧ node < 2 ^ forsTreeHeight
    · simp only [hh, and_self, ↓reduceDIte] at h ⊢
      exact dig_tabOf_congr h
    · simp only [hh, ↓reduceDIte]

/-- **A symbolic position's value reads one coordinate.** -/
theorem valuePos_tabOf_congr (q : ValPos) (h : pairAt θ (vcoord q) = pairAt θ' (vcoord q)) :
    (tabOf θ).valuePos q = (tabOf θ').valuePos q := by
  cases q with
  | chain l τ e i j => exact chainValue_tabOf_congr h
  | tree l τ level index => exact treeValue_tabOf_congr h
  | forsSecret idx κ s => exact dig_tabOf_congr h
  | forsTree idx κ height node => exact forsValue_tabOf_congr h
  | forsKey idx => exact dig_tabOf_congr h

theorem root_tabOf_congr (h : pairAt θ rootC = pairAt θ' rootC) :
    (tabOf θ).root = (tabOf θ').root :=
  treeValue_tabOf_congr h

theorem randomizer_tabOf_congr {msg : Message} (h : pairAt θ (rndC msg) = pairAt θ' (rndC msg)) :
    (tabOf θ).randomizer msg = (tabOf θ').randomizer msg :=
  dig_tabOf_congr h

end congr

/-! ## Structural positions and their cells -/

/-- **The coordinates a position's input reads**: `PK.seed` and its payload's values. -/
def cellNeed : RawPos → Finset TPos
  | .chain l τ e i step => {seedC, chainC l τ e i step.val}
  | .leaf l τ e => insert seedC (Finset.univ.image fun i ↦ chainC l τ e i (chainLength - 1))
  | .node l τ level index =>
      {seedC, treeC l τ level.val (2 * index.val), treeC l τ level.val (2 * index.val + 1)}
  | .forsLeaf idx κ s => {seedC, rawC (.forsSecret idx κ s)}
  | .forsNode idx κ level node =>
      {seedC, forsC idx κ level.val (2 * node.val), forsC idx κ level.val (2 * node.val + 1)}
  | .forsRoots idx => insert seedC (Finset.univ.image fun κ ↦ forsC idx κ forsTreeHeight 0)
  | _ => {seedC}

theorem seedC_mem_cellNeed (q : RawPos) : seedC ∈ cellNeed q := by
  cases q <;> simp [cellNeed]

/-- **A structural position's cell reads the coordinates `cellNeed p`**, not the master seed. -/
theorem cellOf_tabOf_congr {p : Pos} (hp : p.1.IsStruct) (S0 S0' : MasterSeed) {θ θ' : TVals}
    (h : ∀ s ∈ cellNeed p.1, pairAt θ s = pairAt θ' s) :
    cellOf S0 p (tabOf θ) = cellOf S0' p (tabOf θ') := by
  have hs : (tabOf θ).publicSeed = (tabOf θ').publicSeed :=
    publicSeed_tabOf_congr (h _ (seedC_mem_cellNeed p.1))
  obtain ⟨q, hq⟩ := p
  cases q with
  | chain l τ e i step =>
    change cell ((tabOf θ).expandedKey S0) (tabOf θ).root (.chain l τ e i step)
        ((tabOf θ).chainValue l τ e i step.val) =
      cell ((tabOf θ').expandedKey S0') (tabOf θ').root (.chain l τ e i step)
        ((tabOf θ').chainValue l τ e i step.val)
    rw [chainValue_tabOf_congr (h _ (by simp [cellNeed]))]
    exact cell_congr (by simp only [slotInput, QTable.expandedKey_publicSeed, hs])
  | leaf l τ e =>
    change cell ((tabOf θ).expandedKey S0) (tabOf θ).root (.leaf l τ e)
        ((tabOf θ).endpoints l τ e) =
      cell ((tabOf θ').expandedKey S0') (tabOf θ').root (.leaf l τ e)
        ((tabOf θ').endpoints l τ e)
    have he : (tabOf θ).endpoints l τ e = (tabOf θ').endpoints l τ e := funext fun i ↦
      chainValue_tabOf_congr (h _ (Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
    rw [he]
    exact cell_congr (by simp only [slotInput, QTable.expandedKey_publicSeed, hs])
  | node l τ level index =>
    change cell ((tabOf θ).expandedKey S0) (tabOf θ).root (.node l τ (level.val + 1) index.val)
        ((tabOf θ).treeValue l τ level.val (2 * index.val),
          (tabOf θ).treeValue l τ level.val (2 * index.val + 1)) =
      cell ((tabOf θ').expandedKey S0') (tabOf θ').root (.node l τ (level.val + 1) index.val)
        ((tabOf θ').treeValue l τ level.val (2 * index.val),
          (tabOf θ').treeValue l τ level.val (2 * index.val + 1))
    rw [treeValue_tabOf_congr (h _ (by simp [cellNeed])),
      treeValue_tabOf_congr (h _ (by simp [cellNeed]))]
    exact cell_congr (by simp only [slotInput, QTable.expandedKey_publicSeed, hs])
  | forsLeaf idx κ s =>
    change cell ((tabOf θ).expandedKey S0) (tabOf θ).root (.forsLeaf idx κ s)
        ((tabOf θ).forsSecret idx κ s) =
      cell ((tabOf θ').expandedKey S0') (tabOf θ').root (.forsLeaf idx κ s)
        ((tabOf θ').forsSecret idx κ s)
    rw [show (tabOf θ).forsSecret idx κ s = (tabOf θ').forsSecret idx κ s from
      dig_tabOf_congr (h _ (by simp [cellNeed]))]
    exact cell_congr (by simp only [slotInput, QTable.expandedKey_publicSeed, hs])
  | forsNode idx κ level node =>
    change cell ((tabOf θ).expandedKey S0) (tabOf θ).root (.forsNode idx κ (level.val + 1) node.val)
        ((tabOf θ).forsValue idx κ level.val (2 * node.val),
          (tabOf θ).forsValue idx κ level.val (2 * node.val + 1)) =
      cell ((tabOf θ').expandedKey S0') (tabOf θ').root (.forsNode idx κ (level.val + 1) node.val)
        ((tabOf θ').forsValue idx κ level.val (2 * node.val),
          (tabOf θ').forsValue idx κ level.val (2 * node.val + 1))
    rw [forsValue_tabOf_congr (h _ (by simp [cellNeed])),
      forsValue_tabOf_congr (h _ (by simp [cellNeed]))]
    exact cell_congr (by simp only [slotInput, QTable.expandedKey_publicSeed, hs])
  | forsRoots idx =>
    change cell ((tabOf θ).expandedKey S0) (tabOf θ).root (.forsRoots idx)
        ((tabOf θ).forsRoot idx) =
      cell ((tabOf θ').expandedKey S0') (tabOf θ').root (.forsRoots idx)
        ((tabOf θ').forsRoot idx)
    have hr : (tabOf θ).forsRoot idx = (tabOf θ').forsRoot idx := funext fun κ ↦
      forsValue_tabOf_congr (h _ (Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ (Finset.mem_univ κ))))
    rw [hr]
    exact cell_congr (by simp only [slotInput, QTable.expandedKey_publicSeed, hs])
  | _ => exact absurd hp id

/-- **The digest cell of `M`** at a table: call 0 of `H_msg` at `PK.seed`, `PK.root`, `R(M)`. -/
theorem cellOf_digPos (S0 : MasterSeed) (v : QTable) (msg : Message) :
    cellOf S0 (digPos msg) v = digestCell v.publicSeed v.root (v.randomizer msg) msg 0 :=
  cell_congr rfl

/-! ## Template program ports -/

/-- **The coordinates of a position's program port**: its input's and its own value's. -/
def progNeed (p : Pos) : Finset TPos :=
  insert (coordOf p) (cellNeed p.1)

theorem cellNeed_subset_progNeed (p : Pos) : cellNeed p.1 ⊆ progNeed p :=
  Finset.subset_insert _ _

theorem coordOf_mem_progNeed (p : Pos) : coordOf p ∈ progNeed p :=
  Finset.mem_insert_self _ _

/-- Every template program port is allowed. -/
def goodQ : LazyProg PairOut Qrom.HashDomain TPos TVal → Prop :=
  fun _ ↦ True

/-- **The program port of a structural position**: hardwire its cell to its value, both read from
the coordinates `progNeed p` (the master seed is not read: `0` stands for it). -/
noncomputable def progT (p : Pos) : LazyProg PairOut Qrom.HashDomain TPos TVal :=
  .programH (progNeed p) fun w ↦ (cellOf 0 p (tabR w), tabR w p)

theorem need_progT (p : Pos) : (progT p).need = progNeed p :=
  rfl

/-- **The program port of a structural position, realized**: its cell at any master seed, with
its value. -/
theorem realize_progT {p : Pos} (hp : p.1.IsStruct) (S0 : MasterSeed) (θ : TVals) :
    (progT p).realize θ = .programH (cellOf S0 p (tabOf θ)) (tabOf θ p) := by
  have hc : cellOf 0 p (tabR (restrictTo (progNeed p) θ)) = cellOf S0 p (tabOf θ) :=
    cellOf_tabOf_congr hp 0 S0 fun s hs ↦
      pairAt_extW_restrictTo (cellNeed_subset_progNeed p hs) θ
  have hv : tabR (restrictTo (progNeed p) θ) p = tabOf θ p :=
    pairAt_extW_restrictTo (coordOf_mem_progNeed p) θ
  simp only [progT, LazyProg.realize, hc, hv]

/-! ## Digest policies and the digest port -/

/-- **A digest policy**: from the memory label `L` before a signature and the message `M`, the
coordinate holding `M`'s digest pair and the coordinates revealed with it. -/
structure DigestPolicy where
  /-- The coordinate holding the digest pair. -/
  out : Finset TPos → Message → TPos
  /-- The coordinates revealed for the digest. -/
  need : Finset TPos → Message → Finset TPos
  /-- The digest pair is revealed. -/
  out_mem : ∀ L msg, out L msg ∈ need L msg

/-- **The hybrid side's policy**: `M`'s digest cell. -/
def msgPol : DigestPolicy where
  out _ msg := .dig msg
  need _ msg := msgNeed msg
  out_mem _ _ := Finset.mem_singleton_self _

/-- **The event side's policy**: the stream entry of `M` in first-request order, with its mark;
past the stream, `M`'s digest cell. -/
noncomputable def strPol : DigestPolicy where
  out := strOut
  need := strNeed
  out_mem L msg := by
    unfold strOut strNeed
    rcases streamIdx L msg with _ | j
    · exact Finset.mem_singleton_self _
    · exact Finset.mem_insert_self _ _

/-- The coordinates of the digest port: `PK.seed`, `PK.root`, `R(M)`, the digest pair. -/
def digNeed (pol : DigestPolicy) (L : Finset TPos) (msg : Message) : Finset TPos :=
  {seedC, rootC, rndC msg, pol.out L msg}

/-- The cell and pair of the digest port, from the revealed values `w`. -/
noncomputable def digFun (pol : DigestPolicy) (L : Finset TPos) (msg : Message) {T : Finset TPos}
    (w : RevealVals TVal T) : Qrom.HashDomain × PairOut :=
  (digestCell (tabR w).publicSeed (tabR w).root ((tabR w).randomizer msg) msg 0,
    pairR w (pol.out L msg))

/-- **The digest port of `M`**: hardwire `M`'s digest cell (call 0 of `H_msg`) to the pair at the
policy's coordinate. -/
noncomputable def digPort (pol : DigestPolicy) (L : Finset TPos) (msg : Message) :
    LazyProg PairOut Qrom.HashDomain TPos TVal :=
  .programH (digNeed pol L msg) (digFun pol L msg)

/-- **The digest port's cell and pair at revealed values**: those of the hidden values. -/
theorem digFun_restrictTo (pol : DigestPolicy) (L : Finset TPos) (msg : Message)
    {T : Finset TPos} (hT : digNeed pol L msg ⊆ T) (θ : TVals) :
    digFun pol L msg (restrictTo T θ) =
      (digestCell (tabOf θ).publicSeed (tabOf θ).root ((tabOf θ).randomizer msg) msg 0,
        pairAt θ (pol.out L msg)) := by
  have hm : ∀ s ∈ digNeed pol L msg, pairAt (extW (restrictTo T θ)) s = pairAt θ s :=
    fun s hs ↦ pairAt_extW_restrictTo (hT hs) θ
  have hs : (tabR (restrictTo T θ)).publicSeed = (tabOf θ).publicSeed :=
    publicSeed_tabOf_congr (hm _ (by simp [digNeed]))
  have hr : (tabR (restrictTo T θ)).root = (tabOf θ).root :=
    root_tabOf_congr (hm _ (by simp [digNeed]))
  have hR : (tabR (restrictTo T θ)).randomizer msg = (tabOf θ).randomizer msg :=
    randomizer_tabOf_congr (hm _ (by simp [digNeed]))
  have ho : pairR (restrictTo T θ) (pol.out L msg) = pairAt θ (pol.out L msg) :=
    hm _ (by simp [digNeed])
  simp only [digFun, hs, hr, hR, ho]

/-- **The digest port, realized**: the digest cell at the hidden values with the policy's pair. -/
theorem realize_digPort (pol : DigestPolicy) (L : Finset TPos) (msg : Message) (θ : TVals) :
    (digPort pol L msg).realize θ =
      .programH (digestCell (tabOf θ).publicSeed (tabOf θ).root ((tabOf θ).randomizer msg) msg 0)
        (pairAt θ (pol.out L msg)) := by
  simp only [digPort, LazyProg.realize, digFun_restrictTo pol L msg subset_rfl θ]

/-- **At `msgPol` the digest port is the digest cell's program port** at any master seed. -/
theorem realize_digPort_msgPol (L : Finset TPos) (msg : Message) (S0 : MasterSeed) (θ : TVals) :
    (digPort msgPol L msg).realize θ =
      .programH (cellOf S0 (digPos msg) (tabOf θ)) (tabOf θ (digPos msg)) := by
  rw [realize_digPort, cellOf_digPos]
  rfl

/-- The message digest of a digest pair. -/
def digestOfPair (y : PairOut) : MessageDigest :=
  truncateMessageDigest (pairCalls y)

theorem messageDigest_eq_digestOfPair (v : QTable) (msg : Message) :
    v.messageDigest msg = digestOfPair (v (digPos msg)) :=
  rfl

/-! ## Positions a signature makes public -/

/-- A position, if in range. -/
def mkPos (q : RawPos) : List Pos :=
  if h : q.InRange then [⟨q, h⟩] else []

theorem mem_mkPos {q : RawPos} {p : Pos} (h : p ∈ mkPos q) : p.1 = q := by
  unfold mkPos at h
  split_ifs at h with hq
  · rw [List.mem_singleton.mp h]
  · exact absurd h List.not_mem_nil

/-- The hypertree node at `level + 1`, index `index`, if in range (as `treeC`). -/
def nodePos (l : Layer) (τ : TreeIndex) (level index : ℕ) : List Pos :=
  if h : level < layerHeight topLayer ∧ index < 2 ^ layerHeight topLayer then
    mkPos (.node l τ ⟨level, h.1⟩ ⟨index, h.2⟩)
  else []

/-- The FORS node at `height + 1`, node `j`, if in range (as `forsC`). -/
def forsNodePos (idx : Index) (κ : ForsTreeIndex) (height j : ℕ) : List Pos :=
  if hh : height < forsTreeHeight ∧ j < 2 ^ forsTreeHeight then
    mkPos (.forsNode idx κ ⟨height, hh.1⟩ ⟨j, hh.2⟩)
  else []

/-- **The positions a layer signature by `K = (l, τ, e)` with codeword `x` makes public**: the
chain steps from the opened positions, the leaf, and the nodes on the path to the root. -/
def layerPos (K : Key) (x : Encoding) : List Pos :=
  (List.finRange chainCount).flatMap (fun i ↦ ((List.finRange (chainLength - 1)).filter
      fun step ↦ decide ((x i).val ≤ step.val)).flatMap fun step ↦
        mkPos (.chain K.1 K.2.1 K.2.2 i step)) ++
    mkPos (.leaf K.1 K.2.1 K.2.2) ++
    (List.range (layerHeight K.1)).flatMap fun lev ↦
      nodePos K.1 K.2.1 lev (K.2.2.val >>> (lev + 1))

/-- **The positions a FORS opening of instance `idx` at the leaves `lv` makes public**: the opened
leaves, the nodes on their paths, the roots compression. -/
def forsPos (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) : List Pos :=
  (List.finRange forsTreeCount).flatMap (fun κ ↦ mkPos (.forsLeaf idx κ (lv κ)) ++
      (List.range forsTreeHeight).flatMap fun h ↦ forsNodePos idx κ h ((lv κ).val >>> (h + 1))) ++
    mkPos (.forsRoots idx)

theorem isStruct_of_mem_nodePos {l : Layer} {τ : TreeIndex} {level index : ℕ} {p : Pos}
    (hp : p ∈ nodePos l τ level index) : p.1.IsStruct := by
  unfold nodePos at hp
  split_ifs at hp
  · rw [mem_mkPos hp]
    trivial
  · exact absurd hp List.not_mem_nil

theorem isStruct_of_mem_forsNodePos {idx : Index} {κ : ForsTreeIndex} {height j : ℕ} {p : Pos}
    (hp : p ∈ forsNodePos idx κ height j) : p.1.IsStruct := by
  unfold forsNodePos at hp
  split_ifs at hp
  · rw [mem_mkPos hp]
    trivial
  · exact absurd hp List.not_mem_nil

theorem isStruct_of_mem_layerPos {K : Key} {x : Encoding} {p : Pos} (hp : p ∈ layerPos K x) :
    p.1.IsStruct := by
  simp only [layerPos, List.mem_append, List.mem_flatMap] at hp
  rcases hp with (⟨i, -, step, -, hp⟩ | hp) | ⟨lev, -, hp⟩
  · rw [mem_mkPos hp]
    trivial
  · rw [mem_mkPos hp]
    trivial
  · exact isStruct_of_mem_nodePos hp

theorem isStruct_of_mem_forsPos {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex} {p : Pos}
    (hp : p ∈ forsPos idx lv) : p.1.IsStruct := by
  simp only [forsPos, List.mem_append, List.mem_flatMap] at hp
  rcases hp with ⟨κ, -, hp | ⟨h, -, hp⟩⟩ | hp
  · rw [mem_mkPos hp]
    trivial
  · exact isStruct_of_mem_forsNodePos hp
  · rw [mem_mkPos hp]
    trivial

/-- The coordinates of a list of positions' program ports. -/
def needUnion : List Pos → Finset TPos
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

/-- **The coordinates a layer signature reveals**: those of the positions it makes public, of the
opened chain values and of the authentication path. -/
def layerReveal (K : Key) (x : Encoding) : Finset TPos :=
  needUnion (layerPos K x) ∪ Finset.univ.image (fun i ↦ chainC K.1 K.2.1 K.2.2 i (x i).val) ∪
    Finset.univ.image fun z : Fin (layerHeight K.1) ↦
      treeC K.1 K.2.1 z.val ((K.2.2.val >>> z.val) ^^^ 1)

/-- **The coordinates a FORS opening reveals**: those of the positions it makes public, of the
secrets at the leaves and of the paths. -/
def forsReveal (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) : Finset TPos :=
  needUnion (forsPos idx lv) ∪ Finset.univ.image (fun κ ↦ rawC (.forsSecret idx κ (lv κ))) ∪
    Finset.univ.image fun q : ForsTreeIndex × Fin forsTreeHeight ↦
      forsC idx q.1 q.2.val (((lv q.1).val >>> q.2.val) ^^^ 1)

/-- The coordinates of the public key. -/
def pkReveal : Finset TPos :=
  {seedC, rootC}

/- Instance search for the registers over `Finset TPos` exceeds the default size: found once
here. -/
set_option synthInstance.maxSize 1000 in
instance instDecidableEqHwRegTPos {M : Type} [DecidableEq M] :
    DecidableEq (HwReg PairOut Qrom.HashDomain (Finset TPos × M)) :=
  inferInstance

/-! ## The template game -/

variable (M : Type) [Fintype M] [DecidableEq M]

/-- **leanSPHINCS's template signature in the QROM**, with inner memory `M`. -/
abbrev SSpecQ : QuantumOracleSpec.{0, 0} :=
  tmplSpec PairOut Qrom.HashDomain TPos TVal M goodQ

/-- **The memory update of a trial read** of key `K` at the cell `z`. -/
abbrev TrialUpd : Type :=
  Key → Qrom.HashDomain → M → Option PairOut → M

/-- The trial update that keeps the memory. -/
def keepUpd : TrialUpd M :=
  fun _ _ ↦ keepMem

variable (upd : TrialUpd M)

/-- The encoding cell of trial `c` of key `K` on the value `m`. -/
def trialCell (seed : PublicParameter) (K : Key) (m : Digest) (c : ℕ) : Qrom.HashDomain :=
  encCell seed K.1 K.2.1 K.2.2 m (BitVec.ofNat counterBits c)

/-- **The WOTS+C counter search through read ports**, as `otsSignFrom` until a codeword: trials
`c, c + 1, ...` on the value `m`, each reading the encoding cell (updating the memory with
`upd K`). -/
noncomputable def grindT (seed : PublicParameter) (B : QReg) (K : Key) (m : Digest) :
    ℕ → ℕ → QComp (hwReadSpec PairOut Qrom.HashDomain M) B B
      (Option (EncodingCounter × Encoding))
  | 0, _ => QuantumComp₂.pure none
  | n + 1, c =>
    (readCall (.readH (trialCell seed K m c) (upd K (trialCell seed K m c))) B).bind fun r ↦
      match TargetSum.decodeDigest (truncateHash (r.1.getD 0).1) with
      | some x => QuantumComp₂.pure (some (BitVec.ofNat counterBits c, x))
      | none => grindT seed B K m n (c + 1)

/-- Call the program ports of the positions `ps` in order. -/
noncomputable def progPos (B : QReg) : List Pos → QComp (SSpecQ M) B B Unit
  | [] => QuantumComp₂.pure ()
  | p :: ps => progThen (progT p) trivial (progPos B ps)

/-- **The FORS opening of instance `idx` at the leaves `lv`**: reveal its coordinates, hardwire
the positions it makes public, and read the opening from the revealed values. -/
noncomputable def forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    QComp (SSpecQ M) B B (ForsTreeIndex → ForsTreeOpening) :=
  revealThen goodQ (forsReveal idx lv) fun r ↦
    (progPos M B (forsPos idx lv)).bind fun _ ↦
      QuantumComp₂.pure ((tabR r.1).forsOpening idx lv)

/-- **The counter search of the key `K = (l, τ, e)`** under `PK.seed = seed`: reveal the value `K`
signs (at `msgPos K`), then the trials on it through reads. -/
noncomputable def selectT (seed : PublicParameter) (B : QReg) (K : Key) :
    QComp (SSpecQ M) B B (Option (EncodingCounter × Encoding)) :=
  revealThen goodQ {vcoord (msgPos K)} fun r₀ ↦
    readLiftQ goodQ (grindT M upd seed B K ((tabR r₀.1).valuePos (msgPos K))
      encodingAttemptLimit 0)

/-- **The publication of a layer signature by `K` with counter `c` and codeword `x`**: reveal the
layer's coordinates, hardwire the positions it makes public, and read the opened chain values and
the path from the revealed values. -/
noncomputable def publishT (B : QReg) (K : Key) (c : EncodingCounter) (x : Encoding) :
    QComp (SSpecQ M) B B (LayerSignature K.1) :=
  revealThen goodQ (layerReveal K x) fun r ↦
    (progPos M B (layerPos K x)).bind fun _ ↦
      QuantumComp₂.pure ⟨c, fun i ↦ (tabR r.1).chainValue K.1 K.2.1 K.2.2 i (x i).val,
        (tabR r.1).authPath K.1 K.2.1 K.2.2⟩

/-- The digest of `M` from the revealed values `w` on the policy's coordinates at the label `L`. -/
noncomputable def digestT (pol : DigestPolicy) (L : Finset TPos) (msg : Message)
    {T : Finset TPos} (w : RevealVals TVal T) : MessageDigest :=
  digestOfPair (pairR w (pol.out L msg))

/-- **The publication of a signature** of index `idx`, FORS leaves `lv` and randomizer `R`, from the
three counter searches' results: when all three succeed, the FORS opening and the three layer
signatures (revealed, hardwired, read); `none` otherwise, with nothing revealed or hardwired. -/
noncomputable def publishAllT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (R : Randomizer) :
    Option (EncodingCounter × Encoding) → Option (EncodingCounter × Encoding) →
      Option (EncodingCounter × Encoding) → QComp (SSpecQ M) B B (Option Signature)
  | some (c₀, x₀), some (c₁, x₁), some (c₂, x₂) =>
    (forsOpenT M B idx lv).bind fun fo ↦
    (publishT M B (keyOf 0 idx) c₀ x₀).bind fun bottom ↦
    (publishT M B (keyOf 1 idx) c₁ x₁).bind fun middle ↦
    (publishT M B (keyOf 2 idx) c₂ x₂).bind fun top ↦
      QuantumComp₂.pure (some ⟨R, fo, KeyGenerationAndSigning.layerSignatures bottom middle top⟩)
  | _, _, _ => QuantumComp₂.pure none

/-- **A signature in runtime 2**, as `signWithExpandedKey`: reveal `PK.seed`, `PK.root` and `R(M)`
(the result carries the label `L` before), the digest's coordinates under the policy, hardwire the
digest cell; the counter searches of the three layers' keys; when all succeed, the FORS opening at
the digest's index and leaves and the three layer signatures (`publishAllT`). -/
noncomputable def signT (pol : DigestPolicy) (B : QReg) (msg : Message) :
    QComp (SSpecQ M) B B (Option Signature) :=
  revealThen goodQ {seedC, rootC, rndC msg} fun r₁ ↦
  revealThen goodQ (pol.need r₁.2.1 msg) fun r₂ ↦
  progThen (digPort pol r₁.2.1 msg) trivial <|
  (selectT M upd (tabR r₁.1).publicSeed B
      (keyOf 0 (digestIndex (digestT pol r₁.2.1 msg r₂.1)))).bind fun g₀ ↦
  (selectT M upd (tabR r₁.1).publicSeed B
      (keyOf 1 (digestIndex (digestT pol r₁.2.1 msg r₂.1)))).bind fun g₁ ↦
  (selectT M upd (tabR r₁.1).publicSeed B
      (keyOf 2 (digestIndex (digestT pol r₁.2.1 msg r₂.1)))).bind fun g₂ ↦
  publishAllT M B (digestIndex (digestT pol r₁.2.1 msg r₂.1))
    (digestForsLeaves (digestT pol r₁.2.1 msg r₂.1)) ((tabR r₁.1).randomizer msg) g₀ g₁ g₂

/-- The adversary signature of the SUF-CMA game. -/
abbrev sAdvSpec : QuantumOracleSpec.{0, 0} :=
  SufCma.advSpec Message (Option Signature)

/-- leanSPHINCS's adversaries. -/
abbrev SAdversary : Type 1 :=
  SufCma.Adversary PublicKey Message (Option Signature) Forgery

/-- The answer to the signing request `M` with the adversary's register held. -/
noncomputable def signAt (pol : DigestPolicy) (msg : Message) (E : QReg) {A : QReg}
    (ℓ : A ≃ sAdvSpec.In (.sign msg) × E) :
    QComp (SSpecQ M) A (QReg.of (sAdvSpec.Out (.sign msg) × E)) (Option Signature) :=
  (QComp.act (spec := SSpecQ M) (B := QReg.of (sAdvSpec.Out (.sign msg) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ signT M upd pol _ msg

/-- A secret key carrying nothing: the challenger's local operations and hash calls do not read
the key. -/
def noKey : SecretKey :=
  0

/-- **The challenger of runtime 2**: a local operation and a hash call as in `challengeReads`
(regrouped, lifted to port `h`), a signing request answered by `signT`. -/
noncomputable def challengeT (pol : DigestPolicy) :
    IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (SSpecQ M))
  | A, .prim o => readLift goodQ ((liftH (regroupCalls hmsgRoute
      (SufCma.challenge sphincsRom noKey A (.prim o)))).liftOrdinary
        (t := hwReadCmdSpec PairOut Qrom.HashDomain M))
  | A, .query .hash E ℓ => readLift goodQ ((liftH (regroupCalls hmsgRoute
      (SufCma.challenge sphincsRom noKey A (.query .hash E ℓ)))).liftOrdinary
        (t := hwReadCmdSpec PairOut Qrom.HashDomain M))
  | _, .query (.sign msg) E ℓ =>
      QuantumComp.bind (signAt M upd pol msg E ℓ) fun _ l ↦
        QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- The adversary's program against the challenger of runtime 2. -/
noncomputable def challengedT (pol : DigestPolicy) {A B : QReg} {α : Type}
    (x : QComp sAdvSpec A B α) : QComp (SSpecQ M) A B α :=
  IPFunctor.IFreeM.substitute (challengeT M upd pol) x

/-- **A computation's read program, then a pure step**: the reads of `oa` (its result), then `f`
of the result. Irreducible: unfolding a concrete `oa` evaluates the hashed inputs' encodings
(`hashQ`), so proofs unfold it explicitly (`readsThenT_eq`). -/
@[irreducible]
noncomputable def readsThenT {α β : Type} (oa : OracleComp RomOracles α) (f : α → β) :
    QComp (SSpecQ M) (QReg.of Unit) (QReg.of Unit) β :=
  (readLiftQ goodQ ((readsProgram M _ oa).map Prod.fst)).bind fun a ↦ QuantumComp₂.pure (f a)

omit [Fintype M] [DecidableEq M] in
theorem readsThenT_eq {α β : Type} (oa : OracleComp RomOracles α) (f : α → β) :
    readsThenT M oa f =
      (readLiftQ goodQ ((readsProgram M _ oa).map Prod.fst)).bind fun a ↦
        QuantumComp₂.pure (f a) := by
  unfold readsThenT
  rfl

/-- **The verification of the game** through read ports, and the winning condition. -/
noncomputable def verifyT (x : PublicKey × (Forgery × SufCma.SignLog Message (Option Signature))) :
    QComp (SSpecQ M) (QReg.of Unit) (QReg.of Unit) Bool :=
  readsThenT M (sphincsRom.verify x.1 x.2.1) fun verified ↦
    sphincsRom.winningCondition x.2.2 x.2.1 && verified

/-- **The SUF-CMA game as runtime 2 runs it, as a template**: reveal the public key, run the
adversary on it against the challenger of runtime 2 with its signing transcript, verify the
forgery through read ports, and return the winning condition. `realizeT θ (gameT M upd pol A)` is
the game at the hidden values `θ`. -/
noncomputable def gameT (pol : DigestPolicy) (A : SAdversary) :
    QComp (SSpecQ M) (QReg.of Unit) (QReg.of Unit) Bool :=
  revealThen goodQ pkReveal fun r₀ ↦
    (challengedT M upd pol (SufCma.withSignLog (A (tabR r₀.1).publicKey))).bind fun run ↦
      verifyT M ((tabR r₀.1).publicKey, run)

/-- **The challenge prefix of the game**: reveal the public key and run the adversary on it
against the challenger of runtime 2 with its signing transcript; return the public key, the
forgery and the transcript. -/
noncomputable def prefixT (pol : DigestPolicy) (A : SAdversary) :
    QComp (SSpecQ M) (QReg.of Unit) (QReg.of Unit)
      (PublicKey × (Forgery × SufCma.SignLog Message (Option Signature))) :=
  revealThen goodQ pkReveal fun r₀ ↦
    (challengedT M upd pol (SufCma.withSignLog (A (tabR r₀.1).publicKey))).bind fun run ↦
      QuantumComp₂.pure ((tabR r₀.1).publicKey, run)

omit [Fintype M] [DecidableEq M] in
/-- **The game is its challenge prefix, then the verification.** -/
theorem gameT_eq_prefixT_bind (pol : DigestPolicy) (A : SAdversary) :
    gameT M upd pol A = (prefixT M upd pol A).bind (verifyT M) := by
  simp only [gameT, prefixT, revealThen_bind, QuantumComp₂.bind_assoc, QuantumComp₂.pure_bind]

/-! ## The game reveals before it programs -/

omit [Fintype M] [DecidableEq M] in
theorem disc_progPos (B : QReg) (ps : List Pos) (T : Finset TPos)
    (h : ∀ p ∈ ps, progNeed p ⊆ T) : Disc (progPos M B ps) T := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact disc_progThen _ trivial _ T (h p List.mem_cons_self)
      (ih fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

omit [Fintype M] [DecidableEq M] in
theorem disc_forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (T : Finset TPos) : Disc (forsOpenT M B idx lv) T :=
  disc_revealThen _ _ T fun _ ↦ disc₂_bind _ _ (disc_progPos M B _ _ fun _ hp ↦
    ((progNeed_subset_needUnion hp).trans (Finset.subset_union_left.trans
      Finset.subset_union_left)).trans Finset.subset_union_right) fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem disc_selectT (seed : PublicParameter) (B : QReg) (K : Key) (T : Finset TPos) :
    Disc (selectT M upd seed B K) T :=
  disc_revealThen _ _ T fun _ ↦ disc_readLift _ _

omit [Fintype M] [DecidableEq M] in
theorem disc_publishT (B : QReg) (K : Key) (c : EncodingCounter) (x : Encoding)
    (T : Finset TPos) : Disc (publishT M B K c x) T :=
  disc_revealThen _ _ T fun _ ↦ disc₂_bind _ _ (disc_progPos M B _ _ fun _ hp ↦
    ((progNeed_subset_needUnion hp).trans (Finset.subset_union_left.trans
      Finset.subset_union_left)).trans Finset.subset_union_right) fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem disc_publishAllT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (R : Randomizer) (g₀ g₁ g₂ : Option (EncodingCounter × Encoding)) (T : Finset TPos) :
    Disc (publishAllT M B idx lv R g₀ g₁ g₂) T := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try trivial
  exact disc₂_bind _ _ (disc_forsOpenT M B _ _ T) fun _ T₁ _ ↦
    disc₂_bind _ _ (disc_publishT M B _ _ _ T₁) fun _ T₂ _ ↦
      disc₂_bind _ _ (disc_publishT M B _ _ _ T₂) fun _ T₃ _ ↦
        disc₂_bind _ _ (disc_publishT M B _ _ _ T₃) fun _ _ _ ↦ trivial

theorem digNeed_subset (pol : DigestPolicy) (T L : Finset TPos) (msg : Message) :
    digNeed pol L msg ⊆ T ∪ {seedC, rootC, rndC msg} ∪ pol.need L msg := by
  intro s hs
  simp only [digNeed, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
  · exact Finset.mem_union_right _ (pol.out_mem L msg)

omit [Fintype M] [DecidableEq M] in
theorem disc_signT (pol : DigestPolicy) (B : QReg) (msg : Message) (T : Finset TPos) :
    Disc (signT M upd pol B msg) T :=
  disc_revealThen _ _ T fun r₁ ↦ disc_revealThen _ _ _ fun _ ↦
    disc_progThen _ trivial _ _ (digNeed_subset pol T r₁.2.1 msg)
      (disc₂_bind _ _ (disc_selectT M upd _ B _ _) fun _ T₁ _ ↦
        disc₂_bind _ _ (disc_selectT M upd _ B _ T₁) fun _ T₂ _ ↦
          disc₂_bind _ _ (disc_selectT M upd _ B _ T₂) fun _ T₃ _ ↦
            disc_publishAllT M B _ _ _ _ _ _ T₃)

omit [Fintype M] [DecidableEq M] in
theorem disc_challengeT (pol : DigestPolicy) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) (T : Finset TPos) :
    Disc (challengeT M upd pol A c) T := by
  rcases c with o | ⟨_ | msg, E, ℓ⟩
  · exact disc_readLift _ _
  · exact disc_readLift _ _
  · exact disc_bind _ _ (disc₂_bind _ _ (disc_act _ _) fun _ T' _ ↦ disc_signT M upd pol _ msg T')
      fun _ _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- The challenge prefix reveals before it programs. -/
theorem disc_prefixT (pol : DigestPolicy) (A : SAdversary) (T : Finset TPos) :
    Disc (prefixT M upd pol A) T :=
  disc_revealThen _ _ T fun _ ↦ disc₂_bind _ _
    (disc_substitute _ (disc_challengeT M upd pol) _ _) fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- A read program followed by a pure step never programs. -/
theorem disc_readsThenT {α β : Type} (oa : OracleComp RomOracles α) (f : α → β)
    (T : Finset TPos) : Disc (readsThenT M oa f) T := by
  rw [readsThenT_eq]
  exact disc₂_bind _ _ (disc_readLift _ _) fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- The verification never programs. -/
theorem disc_verifyT (x : PublicKey × (Forgery × SufCma.SignLog Message (Option Signature)))
    (T : Finset TPos) : Disc (verifyT M x) T :=
  disc_readsThenT M _ _ T

omit [Fintype M] [DecidableEq M] in
/-- **The game reveals before it programs**: every program port hardwires a cell whose
coordinates the signature revealed just before. -/
theorem disc_gameT (pol : DigestPolicy) (A : SAdversary) (T : Finset TPos) :
    Disc (gameT M upd pol A) T := by
  rw [gameT_eq_prefixT_bind]
  exact disc₂_bind (prefixT M upd pol A) (verifyT M) (disc_prefixT M upd pol A T)
    fun x T' _ ↦ disc_verifyT M x T'

/-! ## The game's reads keep the label -/

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_progPos (B : QReg) (ps : List Pos) : KeepsLab (progPos M B ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact keepsLab_progThen _ trivial _ ih

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    KeepsLab (forsOpenT M B idx lv) :=
  keepsLab_revealThen _ _ fun _ ↦ keepsLab₂_bind _ _ (keepsLab_progPos M B _) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_selectT (seed : PublicParameter) (B : QReg) (K : Key) :
    KeepsLab (selectT M upd seed B K) :=
  keepsLab_revealThen _ _ fun _ ↦ keepsLab_readLift _

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_publishT (B : QReg) (K : Key) (c : EncodingCounter) (x : Encoding) :
    KeepsLab (publishT M B K c x) :=
  keepsLab_revealThen _ _ fun _ ↦ keepsLab₂_bind _ _ (keepsLab_progPos M B _) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_publishAllT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (R : Randomizer) (g₀ g₁ g₂ : Option (EncodingCounter × Encoding)) :
    KeepsLab (publishAllT M B idx lv R g₀ g₁ g₂) := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try trivial
  exact keepsLab₂_bind _ _ (keepsLab_forsOpenT M B _ _) fun _ ↦
    keepsLab₂_bind _ _ (keepsLab_publishT M B _ _ _) fun _ ↦
      keepsLab₂_bind _ _ (keepsLab_publishT M B _ _ _) fun _ ↦
        keepsLab₂_bind _ _ (keepsLab_publishT M B _ _ _) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_signT (pol : DigestPolicy) (B : QReg) (msg : Message) :
    KeepsLab (signT M upd pol B msg) :=
  keepsLab_revealThen _ _ fun _ ↦ keepsLab_revealThen _ _ fun _ ↦
    keepsLab_progThen _ trivial _ (keepsLab₂_bind _ _ (keepsLab_selectT M upd _ B _) fun _ ↦
      keepsLab₂_bind _ _ (keepsLab_selectT M upd _ B _) fun _ ↦
        keepsLab₂_bind _ _ (keepsLab_selectT M upd _ B _) fun _ ↦
          keepsLab_publishAllT M B _ _ _ _ _ _)

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_challengeT (pol : DigestPolicy) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    KeepsLab (challengeT M upd pol A c) := by
  rcases c with o | ⟨_ | msg, E, ℓ⟩
  · exact keepsLab_readLift _
  · exact keepsLab_readLift _
  · exact keepsLab_bind _ _ (keepsLab₂_bind _ _ (keepsLab_act _) fun _ ↦
      keepsLab_signT M upd pol _ msg) fun _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- The challenge prefix's reads keep the label. -/
theorem keepsLab_prefixT (pol : DigestPolicy) (A : SAdversary) :
    KeepsLab (prefixT M upd pol A) :=
  keepsLab_revealThen _ _ fun _ ↦ keepsLab₂_bind _ _
    (keepsLab_substitute _ (keepsLab_challengeT M upd pol) _) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- A read program followed by a pure step keeps the label. -/
theorem keepsLab_readsThenT {α β : Type} (oa : OracleComp RomOracles α) (f : α → β) :
    KeepsLab (readsThenT M oa f) := by
  rw [readsThenT_eq]
  exact keepsLab₂_bind _ _ (keepsLab_readLift _) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- The verification's reads keep the label. -/
theorem keepsLab_verifyT (x : PublicKey × (Forgery × SufCma.SignLog Message (Option Signature))) :
    KeepsLab (verifyT M x) :=
  keepsLab_readsThenT M _ _

omit [Fintype M] [DecidableEq M] in
/-- **The game's reads keep the label** (Mismatch's `KeepsLab`). -/
theorem keepsLab_gameT (pol : DigestPolicy) (A : SAdversary) :
    KeepsLab (gameT M upd pol A) := by
  rw [gameT_eq_prefixT_bind]
  exact keepsLab₂_bind (prefixT M upd pol A) (verifyT M) (keepsLab_prefixT M upd pol A)
    fun x ↦ keepsLab_verifyT M x

/-! ## Lazy sampling -/

/-- **The lazy-sampling property of the runtime-2 game.** For every initial state that does not
depend on the hidden values, the realized games satisfy `ViewBy` for runtime 2 with record ports
and the memory label, at every call. -/
theorem viewBy_gameT (pol : DigestPolicy) (A : SAdversary) (m₀ : Finset TPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × M)))
      (QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × M))) ℂ) (j : ℕ) :
    ViewBy (runtimeR m₀) LocalSig.Interp.instruments (fun r ↦ r.2.2.1)
      (fun θ ↦ realizeT θ (gameT M upd pol A)) (fun _ ↦ ρ) j :=
  viewBy_runtimeR_of_disc _ m₀ (gameT M upd pol A) ∅ (disc_gameT M upd pol A ∅) (fun _ ↦ ρ)
    (lazy_const _ ρ) (fun _ ↦ suppAt_empty _ ρ) j

/-- **`ViewByOn` for the runtime-2 game**: the `hview` hypothesis of the hidden-mass bounds, for
weights vanishing on the program ports. -/
theorem viewByOn_gameT (pol : DigestPolicy) (A : SAdversary) (m₀ : Finset TPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × M)))
      (QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × M))) ℂ) (j : ℕ) :
    ViewByOn (runtimeR m₀) LocalSig.Interp.instruments (fun i ↦ i.isLeft = true)
      (fun r ↦ r.2.2.1) (fun θ ↦ realizeT θ (gameT M upd pol A)) (fun _ ↦ ρ) j :=
  (viewBy_gameT M upd pol A m₀ ρ j).viewByOn _

end Quantum.Qrom.Sphincs

end
