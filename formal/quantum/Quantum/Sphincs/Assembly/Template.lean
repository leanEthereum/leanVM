module

public import Quantum.Xmss.Hybrid.Mismatch
public import Quantum.Sphincs.Events
public import Quantum.Sphincs.CoverStream
public import Quantum.Sphincs.Assembly.PathBad

@[expose] public section

/-!
# Runtime 2 of leanSPHINCS as a template program

leanSPHINCS's SUF-CMA game as runtime 2 runs it, written as a template program
(`Quantum.Xmss.Assembly.tmplSpec`: runtime 2's ports, program ports whose cells and values are
functions of hidden coordinates, and reveal ports) over the hidden values `v : (s : HPos) → XD s`.
The generic machinery (`realizeT`, `runtimeR`, `Disc`, `viewBy_runtimeR_of_disc`, Mismatch's
`KeepsLab`) is leanXMSS's; this file is leanSPHINCS's instance.

## Contract C2: template data

* **Hidden coordinates** `HPos` and their values `XD`: `.val p` the 128-bit value at the position
  `p : ValPos` (contract C1); `.rnd M` the randomizer `R(M) = PRF_msg(SK.prf, PK.seed, M)`;
  `.dig M i` the output of `H_msg` call `i` on `M` at `R(M)` (256 bits); `.str j i` entry `j` of
  the digest stream (`Fin signatureLimit`, 256 bits); `.asg M j` (no value) records that `M` uses
  stream entry `j`. At a table `L` (`valueAt L`): `valuePos L`, `L.randomizer`, `L.digestOutput`,
  the stream and the marks are pads (`0`, `()`).
* **Public data** `Pub`: `PK.seed`, `π`, the keys `(h, k, k')`; `pubOf L`. `PK.root` is the value
  at `.val rootPos`. The event's data (contract C3) at `(p, v)` is `evData p v`: the values
  `valsOf v = v ∘ .val` and the static coverage set `coverOf v = streamCover (v ∘ .str)` (`S★`).
* **Digest policies** `DigestPolicy`: from the memory label `T` before a signature (the coordinates
  revealed so far) and the message `M`, the coordinate `out T M i` holding `H_msg` call `i`'s output
  and further coordinates `marks T M` revealed with it. `msgPol` (hybrid side): `.dig M i`.
  `strPol` (event side): the stream entry `j` assigned to `M` (`streamIdx`: `.asg M j` already in
  `T`, otherwise the next one, `j` the number of `.asg` marks in `T`), `out = .str j i`,
  `marks = {.asg M j}`; past `signatureLimit` messages, `.dig M i`.
* **Program ports** (`pathPorts`): per round `j` of an absorption of the blocks `b`, the cells
  `cellK`, `cellK'`, `cellH` (`Quantum.Xmss.Assembly.rnK`, `rnR`, `rnZ` under the public keys) with
  their public values, except the last round's `h` value, corrected (`cor r w`, `r` the rate after
  `π`, `w` the public value) so that the output is a hidden value: `cor128 d` (a structural slot:
  the digest `trunc128` is the value `d` at the output position, by `embed128`), `cor256 y`
  (`H_msg`: `out256` is the output `y`, by `embed256`). The realized ports are `pathCells`
  (`realize_pathPorts`). `slotPorts pub s`: slot `s`'s cells at `slotBlk pub.seed s` (contract C1
  inputs; the `h` cells are `Quantum.Sphincs.Assembly.PathBad`'s `sCellZ`, the last one
  `sOutCap`), coordinates `valSet (slotNeed s)`. `hmsgPorts`: call `i`'s one block at
  `R = v (.rnd M)` and `PK.root = v (.val rootPos)`, output `v (out T M i)`.
* **The signer** `signT pol pub B M` (after the inner memory type and the trial update
  `upd : TrialUpd`: `signT Mem upd pol pub B M`): reveal `{.val rootPos, .rnd M}` (its result
  carries the label `T`), reveal `pol.need T M`, program both `H_msg` calls (`hmsgPorts`), compute
  the digest's index `idx` and leaves; the FORS opening (`forsOpenT`: reveal `forsNeed`, program
  `forsSlots`: the opened leaves, the nodes on their paths, the roots compression); then each
  layer's signature by `K_l(idx)` (`signLayerT`: reveal `.val (msgPos K)`, the value `K` signs;
  the counter search `grindK` through read ports, the trial `h`-reads updating the memory with
  `upd K b xi`, `b` the block, `xi` the rate after `π`, Events' `cwUpd` at `Selections`; reveal
  `layerNeed`, program `layerSlots`: the chain steps from the opened positions, the leaf, the nodes
  on the path). A repeated message re-runs the signer: the reveals are idempotent, the programs
  rewrite the same cells.
* **The game** `gameT pol pub A`: reveal `.val rootPos`, run the adversary on
  `⟨pub.seed, root⟩` against `challengeT` (local operations and permutation calls simulated given
  `π`, a signing request answered by `signT`), verify the forgery through read ports
  (`readsProgram`), return the winning condition. `prefixT`, `verifyT`, `gameT_eq_prefixT_bind`.
* `disc_gameT pol`, `disc_prefixT pol`: the game reveals before it programs (`Disc _ T` from every
  `T`); `keepsLab_gameT pol`, `keepsLab_prefixT pol`: its reads keep the label (the hypotheses of
  `Quantum.Sig.Sampled`); `viewBy_gameT`, `viewByOn_gameT`: the lazy-sampling property.

The exemption facts the event needs from the template (Events' `exS`, `covEx`) are in
`Quantum.Sphincs.Assembly.Template.Exempt`.
-/

open Matrix
open scoped ENNReal ComplexOrder Kronecker

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message PublicParameter Randomizer HashInput MasterSeed ChainStep
  chainLength littleEndianBytes truncateHash)
open Quantum.Xmss (X Z blocks trunc128 out256 bitOf keccakStateEquiv)
open Quantum.Xmss.Hybrid (LazyProg restrictTo ViewBy ViewByOn Lazy lazy_const suppAt_empty
  KeepsLab keepsLab_bind keepsLab₂_bind keepsLab_substitute keepsLab_act keepsLab_revealThen
  keepsLab_progThen keepsLab_readLift)
open Quantum.Xmss.Assembly (tmplSpec RevealVals revealThen progThen readLift readLiftQ realizeT
  runtimeR Disc disc_mono disc_bind disc₂_bind disc_substitute disc_act disc_revealThen
  disc_progThen disc_readLift revealThen_bind viewBy_runtimeR_of_disc embed128 hashTrial rnK rnR
  rnZ)

namespace Quantum.Sphincs.Assembly

/-! ## Hidden coordinates and public data -/

/-- **leanSPHINCS's hidden coordinates**: the values at the positions, the randomizers, the `H_msg`
outputs, the digest stream, and the stream marks. -/
inductive HPos where
  /-- The 128-bit value at a position. -/
  | val (p : ValPos)
  /-- The randomizer `R(M)` of a message. -/
  | rnd (M : Message)
  /-- The output of `H_msg` call `i` on a message at its randomizer. -/
  | dig (M : Message) (i : DigestCall)
  /-- Call `i` of entry `j` of the digest stream. -/
  | str (j : Fin signatureLimit) (i : DigestCall)
  /-- The mark: the message `M` uses stream entry `j`. -/
  | asg (M : Message) (j : Fin signatureLimit)
  deriving DecidableEq, Fintype

/-- **The hidden values' types**: a digest at a position, a randomizer, a hash output for an
`H_msg` output or a stream entry, nothing for a mark. -/
def XD : HPos → Type
  | .val _ => Digest
  | .rnd _ => Randomizer
  | .dig _ _ => HashOutput
  | .str _ _ => HashOutput
  | .asg _ _ => Unit

instance instFintypeXD : ∀ s, Fintype (XD s)
  | .val _ => inferInstanceAs (Fintype Digest)
  | .rnd _ => inferInstanceAs (Fintype Randomizer)
  | .dig _ _ => inferInstanceAs (Fintype HashOutput)
  | .str _ _ => inferInstanceAs (Fintype HashOutput)
  | .asg _ _ => inferInstanceAs (Fintype Unit)

instance instDecidableEqXD : ∀ s, DecidableEq (XD s)
  | .val _ => inferInstanceAs (DecidableEq Digest)
  | .rnd _ => inferInstanceAs (DecidableEq Randomizer)
  | .dig _ _ => inferInstanceAs (DecidableEq HashOutput)
  | .str _ _ => inferInstanceAs (DecidableEq HashOutput)
  | .asg _ _ => inferInstanceAs (DecidableEq Unit)

instance instNonemptyXD : ∀ s, Nonempty (XD s)
  | .val _ => inferInstanceAs (Nonempty Digest)
  | .rnd _ => inferInstanceAs (Nonempty Randomizer)
  | .dig _ _ => inferInstanceAs (Nonempty HashOutput)
  | .str _ _ => inferInstanceAs (Nonempty HashOutput)
  | .asg _ _ => inferInstanceAs (Nonempty Unit)

/-- The hash output a hidden value carries: an `H_msg` output or a stream entry, `0` otherwise. -/
def hashOut : (s : HPos) → XD s → HashOutput
  | .dig _ _, y => y
  | .str _ _, y => y
  | .val _, _ => 0
  | .rnd _, _ => 0
  | .asg _ _, _ => 0

/-- **The hidden values of a table** under `msgPol`: the values at the positions, the randomizers,
the `H_msg` outputs; the stream and the marks are pads. -/
def valueAt (L : HonestTable) : (s : HPos) → XD s
  | .val p => valuePos L p
  | .rnd M => L.randomizer M
  | .dig M i => L.digestOutput M i
  | .str _ _ => (0 : HashOutput)
  | .asg _ _ => ()

/-- **The public data**: `PK.seed`, the permutation `π`, the keys `(h, k, k')`. -/
structure Pub where
  /-- `PK.seed`. -/
  seed : PublicParameter
  /-- The permutation `π` of the sponge decomposition. -/
  perm : Equiv.Perm (X × Z)
  /-- The keys `(h, k, k')`. -/
  keys : SpongeKeys X Z

/-- The public data of a table. -/
def pubOf (L : HonestTable) : Pub :=
  ⟨L.publicSeed, L.perm, L.keys⟩

/-- **The static coverage set** `S★(v)` of the digest stream. -/
noncomputable def coverOf (v : (s : HPos) → XD s) : Disclosures :=
  streamCover fun j i ↦ (v (.str j i) : HashOutput)

/-- The values at the positions. -/
def valsOf (v : (s : HPos) → XD s) (q : ValPos) : Digest :=
  v (.val q)

/-- **The event's data at `(p, v)`** (contract C3): the public data, the values at the positions,
the static coverage set. -/
noncomputable def evData (pub : Pub) (v : (s : HPos) → XD s) : EvData :=
  ⟨pub.seed, pub.perm, pub.keys, valsOf v, coverOf v⟩

/-- Value positions as hidden coordinates. -/
def valSet (T : Finset ValPos) : Finset HPos :=
  T.map ⟨HPos.val, fun _ _ h ↦ HPos.val.inj h⟩

@[simp]
theorem val_mem_valSet {T : Finset ValPos} {p : ValPos} : HPos.val p ∈ valSet T ↔ p ∈ T := by
  rw [valSet, Finset.mem_map]
  exact ⟨fun ⟨a, ha, he⟩ ↦ HPos.val.inj he ▸ ha, fun h ↦ ⟨p, h, rfl⟩⟩

theorem valSet_mono {T T' : Finset ValPos} (h : T ⊆ T') : valSet T ⊆ valSet T' :=
  Finset.map_subset_map.mpr h

/-! ## Values revealed -/

/-- The values revealed on `T` at the positions, extended by `0`. -/
def extendVals {T : Finset HPos} (w : RevealVals XD T) (p : ValPos) : Digest :=
  if h : HPos.val p ∈ T then w ⟨.val p, h⟩ else 0

/-- The randomizer of `M` revealed on `T`, `0` if not revealed. -/
def extendRnd {T : Finset HPos} (w : RevealVals XD T) (msg : Message) : Randomizer :=
  if h : HPos.rnd msg ∈ T then w ⟨.rnd msg, h⟩ else 0

/-- The hash output revealed on `T` at the coordinate `s`, `0` if not revealed. -/
def extendOut {T : Finset HPos} (w : RevealVals XD T) (s : HPos) : HashOutput :=
  if h : s ∈ T then hashOut s (w ⟨s, h⟩) else 0

theorem extendVals_restrictTo {T : Finset HPos} {p : ValPos} (h : HPos.val p ∈ T)
    (v : (s : HPos) → XD s) : extendVals (restrictTo T v) p = v (.val p) := by
  unfold extendVals
  exact dite_eq_left h

theorem extendRnd_restrictTo {T : Finset HPos} {msg : Message} (h : HPos.rnd msg ∈ T)
    (v : (s : HPos) → XD s) : extendRnd (restrictTo T v) msg = v (.rnd msg) := by
  unfold extendRnd
  exact dite_eq_left h

theorem extendOut_restrictTo {T : Finset HPos} {s : HPos} (h : s ∈ T) (v : (s : HPos) → XD s) :
    extendOut (restrictTo T v) s = hashOut s (v s) := by
  rw [extendOut, dite_eq_left h]
  rfl

/-! ## Digest policies -/

/-- **A digest policy**: from the memory label `T` before a signature and the message `M`, the
coordinate holding `H_msg` call `i`'s output, and further coordinates revealed with it. -/
structure DigestPolicy where
  /-- The coordinate holding call `i`'s output. -/
  out : Finset HPos → Message → DigestCall → HPos
  /-- Further coordinates revealed with the outputs. -/
  marks : Finset HPos → Message → Finset HPos

/-- The coordinates a policy reveals for the digest of `M`. -/
def DigestPolicy.need (pol : DigestPolicy) (T : Finset HPos) (msg : Message) : Finset HPos :=
  insert (pol.out T msg 0) (insert (pol.out T msg 1) (pol.marks T msg))

theorem DigestPolicy.out_mem_need (pol : DigestPolicy) (T : Finset HPos) (msg : Message)
    (i : DigestCall) : pol.out T msg i ∈ pol.need T msg := by
  fin_cases i
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

/-- **The hybrid side's policy**: call `i`'s output is `.dig M i`. -/
def msgPol : DigestPolicy where
  out _ msg i := .dig msg i
  marks _ _ := ∅

/-- A mark coordinate. -/
def HPos.isAsg : HPos → Bool
  | .asg _ _ => true
  | _ => false

/-- The number of marks in `T`: the stream entries assigned so far. -/
def asgCount (T : Finset HPos) : ℕ :=
  (T.filter fun s ↦ s.isAsg = true).card

/-- **The stream entry of `M`** at the label `T`: the entry its mark names, otherwise the next one
(the number of marks), none past `signatureLimit` entries. -/
noncomputable def streamIdx (T : Finset HPos) (msg : Message) : Option (Fin signatureLimit) :=
  @dite _ (∃ j, HPos.asg msg j ∈ T) (Classical.propDecidable _) (fun h ↦ some (Classical.choose h))
    fun _ ↦ if h : asgCount T < signatureLimit then some ⟨asgCount T, h⟩ else none

/-- **The event side's policy**: call `i`'s output is entry `streamIdx T M` of the stream, marked
for `M`; past the stream, `.dig M i`. -/
noncomputable def strPol : DigestPolicy where
  out T msg i := match streamIdx T msg with
    | some j => .str j i
    | none => .dig msg i
  marks T msg := match streamIdx T msg with
    | some j => {.asg msg j}
    | none => ∅

/-! ## Program ports -/

/-- Every template program port is allowed. -/
def goodAll : LazyProg X Z HPos XD → Prop :=
  fun _ ↦ True

/-- A hash output in the first 256 bits of a rate (the bits `out256` reads). -/
def embed256 (y : HashOutput) : X :=
  fun j ↦ if j.val < 256 then bitOf (y.getLsbD j.val) else 0

/-- The last `h` value corrected so that the digest of the output rate `r + w` is `d`. -/
def cor128 (d : Digest) (r w : X) : X :=
  w + embed128 (d ^^^ trunc128 (r + w))

/-- The last `h` value corrected so that the output `out256 (r + w)` is `y`. -/
def cor256 (y : HashOutput) (r w : X) : X :=
  w + embed256 (y ^^^ out256 (r + w))

section ports

variable (pub : Pub)

/-- The `k`-cell of round `j` of the absorption of the blocks `b` under the public keys, with its
value. -/
def cellK (b : ℕ → X) (j : ℕ) : X × Z :=
  (rnK pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 b j,
    pub.keys.2.1 (rnK pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 b j))

/-- The `k'`-cell of round `j`, with its value. -/
def cellK' (b : ℕ → X) (j : ℕ) : X × Z :=
  (rnR pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 b j,
    pub.keys.2.2 (rnR pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 b j))

/-- The `h`-cell of round `j`, with its value: the public `h` value, corrected by `cor` at the last
round `last` (`cor r w`, `r` the rate after `π`, `w` the public value). -/
def cellH (b : ℕ → X) (last : ℕ) (cor : X → X → X) (j : ℕ) : Z × X :=
  if j = last then
    (rnZ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 b j,
      cor (rnR pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 b j)
        (pub.keys.1 (rnZ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 b j)))
  else
    (rnZ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 b j,
      pub.keys.1 (rnZ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 b j))

theorem cellH_fst (b : ℕ → X) (last : ℕ) (cor : X → X → X) (j : ℕ) :
    (cellH pub b last cor j).1 = rnZ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 b j := by
  unfold cellH
  split_ifs <;> rfl

theorem cellH_snd (b : ℕ → X) (last : ℕ) (cor : X → X → X) (j : ℕ) :
    (cellH pub b last cor j).2 = if j = last then
      cor (rnR pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 b j)
        (pub.keys.1 (rnZ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 b j))
      else pub.keys.1 (rnZ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 b j) := by
  unfold cellH
  split_ifs <;> rfl

/-- **The program ports of an absorption of `n` blocks**: the `k`, `k'`, `h` cells of every round
with their values, the blocks `b` and the correction `cor` functions of the values on `T₀`. -/
def pathPorts (T₀ : Finset HPos) (b : RevealVals XD T₀ → ℕ → X)
    (cor : RevealVals XD T₀ → X → X → X) (n : ℕ) : List (LazyProg X Z HPos XD) :=
  (List.range n).flatMap fun j ↦
    [.programK T₀ fun w ↦ cellK pub (b w) j, .programK' T₀ fun w ↦ cellK' pub (b w) j,
      .programH T₀ fun w ↦ cellH pub (b w) (n - 1) (cor w) j]

theorem need_of_mem_pathPorts {T₀ : Finset HPos} {b : RevealVals XD T₀ → ℕ → X}
    {cor : RevealVals XD T₀ → X → X → X} {n : ℕ} {p : LazyProg X Z HPos XD}
    (h : p ∈ pathPorts pub T₀ b cor n) : p.need = T₀ := by
  simp only [pathPorts, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at h
  obtain ⟨j, -, h | h | h⟩ := h <;> subst h <;> rfl

/-- The program ports of runtime 2 that an absorption's template ports realize: its cells with
their values, the blocks `b`, the correction `cor`. -/
def pathCells (b : ℕ → X) (cor : X → X → X) (n : ℕ) : List (HwProg X Z) :=
  (List.range n).flatMap fun j ↦
    [.programK (cellK pub b j).1 (cellK pub b j).2,
      .programK' (cellK' pub b j).1 (cellK' pub b j).2,
      .programH (cellH pub b (n - 1) cor j).1 (cellH pub b (n - 1) cor j).2]

/-- **The realized ports of an absorption** are its cells at the revealed values. -/
theorem realize_pathPorts (T₀ : Finset HPos) (b : RevealVals XD T₀ → ℕ → X)
    (cor : RevealVals XD T₀ → X → X → X) (n : ℕ) (v : (s : HPos) → XD s) :
    (pathPorts pub T₀ b cor n).map (LazyProg.realize v) =
      pathCells pub (b (restrictTo T₀ v)) (cor (restrictTo T₀ v)) n := by
  rw [pathPorts, pathCells, List.map_flatMap]
  rfl

/-- **The program ports of a structural slot**: its honest path's cells at the values at
`slotNeed s`, the last `h` value corrected to the value at the output position. -/
def slotPorts (s : Slot) : List (LazyProg X Z HPos XD) :=
  pathPorts pub (valSet (slotNeed s)) (fun w ↦ slotBlk pub.seed s (extendVals w))
    (fun w ↦ cor128 (extendVals w (slotOutPos s))) (nBlk pub.seed s)

theorem need_of_mem_slotPorts {s : Slot} {p : LazyProg X Z HPos XD} (h : p ∈ slotPorts pub s) :
    p.need = valSet (slotNeed s) :=
  need_of_mem_pathPorts pub h

/-- The coordinates of `H_msg` call `i`'s ports: `PK.root`, the randomizer, the output. -/
def hmsgNeed (pol : DigestPolicy) (T : Finset HPos) (msg : Message) (i : DigestCall) :
    Finset HPos :=
  {.val rootPos, .rnd msg, pol.out T msg i}

/-- **The program ports of `H_msg` call `i`** on `M` (one block), from the label `T`: the input at
the randomizer `v (.rnd M)` and the root `v (.val rootPos)`, the output `v (pol.out T M i)`. -/
def hmsgPorts (pol : DigestPolicy) (T : Finset HPos) (msg : Message) (i : DigestCall) :
    List (LazyProg X Z HPos XD) :=
  pathPorts pub (hmsgNeed pol T msg i)
    (fun w ↦ slotBlk pub.seed (.hmsg (extendRnd w msg) msg i) (extendVals w))
    (fun w ↦ cor256 (extendOut w (pol.out T msg i))) 1

theorem need_of_mem_hmsgPorts {pol : DigestPolicy} {T : Finset HPos} {msg : Message}
    {i : DigestCall} {p : LazyProg X Z HPos XD} (h : p ∈ hmsgPorts pub pol T msg i) :
    p.need = hmsgNeed pol T msg i :=
  need_of_mem_pathPorts pub h

/-- The program ports of both `H_msg` calls. -/
def digestPorts (pol : DigestPolicy) (T : Finset HPos) (msg : Message) :
    List (LazyProg X Z HPos XD) :=
  hmsgPorts pub pol T msg 0 ++ hmsgPorts pub pol T msg 1

/-! ## The slots a signature makes public -/

/-- The coordinates of a list of slots. -/
def needUnion : List Slot → Finset ValPos
  | [] => ∅
  | s :: ss => slotNeed s ∪ needUnion ss

theorem slotNeed_subset_needUnion {s : Slot} {ss : List Slot} (h : s ∈ ss) :
    slotNeed s ⊆ needUnion ss := by
  induction ss with
  | nil => exact absurd h List.not_mem_nil
  | cons s' ss ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Finset.subset_union_left
    · exact (ih h).trans Finset.subset_union_right

/-- **The slots a FORS opening of instance `idx` at the leaves `lv` makes public**: the opened
leaves, the nodes on their paths, the roots compression. -/
def forsSlots (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) : List Slot :=
  (List.finRange forsTreeCount).flatMap (fun κ ↦ Slot.forsLeaf idx κ (lv κ) ::
      (List.range forsTreeHeight).map fun h ↦
        Slot.forsNode idx κ (h + 1) ((lv κ).val >>> (h + 1))) ++
    [Slot.forsRoots idx]

/-- The FORS sibling of tree `κ` at height `z` of the opening at `lv`. -/
def forsSibPos (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) (κ : ForsTreeIndex)
    (z : Fin forsTreeHeight) : ValPos :=
  fpos idx κ z.val (((lv κ).val >>> z.val) ^^^ 1)

/-- **The coordinates a FORS opening reveals**: those of the slots it makes public, the secrets at
the leaves, and the paths. -/
def forsNeed (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) : Finset ValPos :=
  needUnion (forsSlots idx lv) ∪ Finset.univ.image (fun κ ↦ ValPos.forsSecret idx κ (lv κ)) ∪
    Finset.univ.image (fun p : ForsTreeIndex × Fin forsTreeHeight ↦ forsSibPos idx lv p.1 p.2)

/-- **The slots the layer signature by key `(l, τ, e)` with codeword `x` makes public**: the chain
steps from the opened positions, the leaf, the nodes on the path to the root. -/
def layerSlots (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (x : Encoding) : List Slot :=
  (List.finRange chainCount).flatMap (fun i ↦ ((List.finRange (chainLength - 1)).filter
      fun step ↦ decide ((x i).val ≤ step.val)).map fun step ↦ Slot.chain l τ e i step) ++
    Slot.leaf l τ e :: (List.range (layerHeight l)).map fun lev ↦
      Slot.node l τ (lev + 1) (e.val >>> (lev + 1))

/-- The authentication-path sibling at `z` of key `(l, τ, e)`. -/
def siblingPos (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (z : Fin (layerHeight l)) :
    ValPos :=
  tpos l τ z.val ((e.val >>> z.val) ^^^ 1)

/-- **The coordinates a layer signature reveals**: those of the slots it makes public, the opened
chain positions, and the authentication path. -/
def layerNeed (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (x : Encoding) : Finset ValPos :=
  needUnion (layerSlots l τ e x) ∪ Finset.univ.image (fun i ↦ cpos l τ e i (x i).val) ∪
    Finset.univ.image (siblingPos l τ e)

end ports

/-! ## Programs -/

/- Instance search for the registers over `Finset HPos` exceeds the default size: found once
here. -/
set_option synthInstance.maxSize 1000 in
instance hwRegHPosDecEq {M : Type} [DecidableEq M] : DecidableEq (HwReg X Z (Finset HPos × M)) :=
  inferInstance

variable (M : Type) [Fintype M] [DecidableEq M]

/-- leanSPHINCS's template signature, with inner memory `M`. -/
abbrev SSpec : QuantumOracleSpec.{0, 0} :=
  tmplSpec X Z HPos XD M goodAll

/-- Call the program ports `ps` in order. -/
noncomputable def progPorts (B : QReg) : List (LazyProg X Z HPos XD) → QComp (SSpec M) B B Unit
  | [] => QuantumComp₂.pure ()
  | p :: ps => progThen p trivial (progPorts B ps)

/-- **The memory update of a counter trial's final `h`-read** for key `K`, from the block `b` and
the rate `xi` after `π` (Events' `cwUpd` at the memory `Selections`). -/
abbrev TrialUpd : Type :=
  Key → X → X → M → Option X → M

/-- The trial update that keeps the memory. -/
def keepUpd : TrialUpd M :=
  fun _ _ _ ↦ keepMem

variable (upd : TrialUpd M) (pol : DigestPolicy) (pub : Pub)

/-- Program the honest paths of the slots `ss`. -/
noncomputable def progSlots (B : QReg) : List Slot → QComp (SSpec M) B B Unit
  | [] => QuantumComp₂.pure ()
  | s :: ss => (progPorts M B (slotPorts pub s)).bind fun _ ↦ progSlots B ss

/-- The input of the counter trial `c` of key `K` on the value `m`:
`PK.seed ‖ ADRS_enc(K) ‖ m ‖ BE32(c)`. -/
def trialInput (K : Key) (m : Digest) (c : ℕ) : HashInput :=
  addressedHashInput pub.seed (hashDomainFields (.encoding K.1 K.2.1 K.2.2))
    (littleEndianBytes 16 m ++ bigEndianBytes 4 (BitVec.ofNat counterBits c))

/-- **The WOTS+C counter search through read ports**, as `otsSignFrom` until a codeword: trials
`c, c + 1, …` on the value `m`, each trial's `h`-reads updating the memory with `upd K`. -/
noncomputable def grindK (B : QReg) (K : Key) (m : Digest) :
    ℕ → ℕ → QComp (hwReadSpec X Z M) B B (Option (EncodingCounter × Encoding))
  | 0, _ => QuantumComp₂.pure none
  | n + 1, c =>
    (hashTrial M (upd K) pub.perm B (trialInput pub K m c)).bind fun out ↦
      match TargetSum.decodeDigest (truncateHash out) with
      | some x => QuantumComp₂.pure (some (BitVec.ofNat counterBits c, x))
      | none => grindK B K m n (c + 1)

/-- **The FORS opening of instance `idx` at the leaves `lv`**: reveal its coordinates, hardwire
the honest paths of the slots it makes public, and read the secrets and paths. -/
noncomputable def forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    QComp (SSpec M) B B (ForsTreeIndex → ForsTreeOpening) :=
  revealThen goodAll (valSet (forsNeed idx lv)) fun r ↦
    (progSlots M pub B (forsSlots idx lv)).bind fun _ ↦
      QuantumComp₂.pure fun κ ↦ ⟨extendVals r.1 (.forsSecret idx κ (lv κ)),
        fun z ↦ extendVals r.1 (forsSibPos idx lv κ z)⟩

/-- **A layer signature by the key `K = (l, τ, e)`**: reveal the value `K` signs (at `msgPos K`),
the counter search on it through reads; then reveal the layer's coordinates, hardwire the honest
paths of the slots it makes public, and read the opened chain values and the path. -/
noncomputable def signLayerT (B : QReg) (K : Key) :
    QComp (SSpec M) B B (Option (LayerSignature K.1)) :=
  revealThen goodAll {.val (msgPos K)} fun r₀ ↦
  (readLiftQ goodAll
    (grindK M upd pub B K (extendVals r₀.1 (msgPos K)) encodingAttemptLimit 0)).bind
    fun g ↦ match g with
    | none => QuantumComp₂.pure none
    | some (c, x) => revealThen goodAll (valSet (layerNeed K.1 K.2.1 K.2.2 x)) fun r ↦
        (progSlots M pub B (layerSlots K.1 K.2.1 K.2.2 x)).bind fun _ ↦
          QuantumComp₂.pure (some ⟨c, fun i ↦ extendVals r.1 (cpos K.1 K.2.1 K.2.2 i (x i).val),
            fun z ↦ extendVals r.1 (siblingPos K.1 K.2.1 K.2.2 z)⟩)

/-- The digest of `M` from the revealed values `w` on the policy's coordinates at the label `T`. -/
def digestOf (T : Finset HPos) (msg : Message) {T' : Finset HPos}
    (w : RevealVals XD T') : MessageDigest :=
  truncateMessageDigest fun i ↦ extendOut w (pol.out T msg i)

/-- **A signature in runtime 2**, as `signWithExpandedKey`: reveal `PK.root` and `R(M)` (the result
carries the label `T`), the digest's coordinates under the policy, hardwire both `H_msg` calls;
the FORS opening at the digest's index and leaves; the three layers. -/
noncomputable def signT (B : QReg) (msg : Message) :
    QComp (SSpec M) B B (Option Signature) :=
  revealThen goodAll {.val rootPos, .rnd msg} fun r₁ ↦
  revealThen goodAll (pol.need r₁.2.1 msg) fun r₂ ↦
  (progPorts M B (digestPorts pub pol r₁.2.1 msg)).bind fun _ ↦
  (forsOpenT M pub B (digestIndex (digestOf pol r₁.2.1 msg r₂.1))
      (digestForsLeaves (digestOf pol r₁.2.1 msg r₂.1))).bind fun fo ↦
  (signLayerT M upd pub B (keyOf 0 (digestIndex (digestOf pol r₁.2.1 msg r₂.1)))).bind fun s₀ ↦
    match s₀ with
    | none => QuantumComp₂.pure none
    | some bottom =>
      (signLayerT M upd pub B (keyOf 1 (digestIndex (digestOf pol r₁.2.1 msg r₂.1)))).bind
        fun s₁ ↦ match s₁ with
        | none => QuantumComp₂.pure none
        | some middle =>
          (signLayerT M upd pub B (keyOf 2 (digestIndex (digestOf pol r₁.2.1 msg r₂.1)))).bind
            fun s₂ ↦ match s₂ with
            | none => QuantumComp₂.pure none
            | some top => QuantumComp₂.pure (some ⟨extendRnd r₁.1 msg, fo,
                KeyGenerationAndSigning.layerSignatures bottom middle top⟩)

/-- leanSPHINCS's adversary over the sponge's state. -/
abbrev SAdversary : Type 1 :=
  Adversary PublicKey Message (Option Signature) Forgery (X × Z)

/-- leanSPHINCS's adversary signature over the sponge's state. -/
abbrev sAdvSpec : QuantumOracleSpec.{0, 0} :=
  advSpec Message (Option Signature) (X × Z)

/-- The answer to the signing request `M` with the adversary's register held. -/
noncomputable def signAt (msg : Message) (E : QReg) {A : QReg}
    (ℓ : A ≃ sAdvSpec.In (.sign msg) × E) :
    QComp (SSpec M) A (QReg.of (sAdvSpec.Out (.sign msg) × E)) (Option Signature) :=
  (QComp.act (spec := SSpec M) (B := QReg.of (sAdvSpec.Out (.sign msg) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ signT M upd pol pub _ msg

/-- **The challenger of runtime 2**: a local operation and a permutation call simulated given `π`
(the adversary's calls become sponge ports; the challenger's calls there read no key), a signing
request answered by `signT`. -/
noncomputable def challengeT :
    IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (SSpec M))
  | A, .prim o => readLift goodAll ((simulate LocalSig.Interp.instruments pub.perm
      (challenge RandomPermutationModel.sufCmaScheme keccakStateEquiv (0 : SecretKey) A
        (.prim o))).liftOrdinary (t := hwReadCmdSpec X Z M))
  | A, .query (.perm p) E ℓ => readLift goodAll ((simulate LocalSig.Interp.instruments pub.perm
      (challenge RandomPermutationModel.sufCmaScheme keccakStateEquiv (0 : SecretKey) A
        (.query (.perm p) E ℓ))).liftOrdinary (t := hwReadCmdSpec X Z M))
  | _, .query (.sign msg) E ℓ =>
      QuantumComp.bind (signAt M upd pol pub msg E ℓ) fun _ l ↦
        QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- The adversary's program against the challenger of runtime 2. -/
noncomputable def challengedT {A B : QReg} {α : Type}
    (x : QComp sAdvSpec A B α) : QComp (SSpec M) A B α :=
  IPFunctor.IFreeM.substitute (challengeT M upd pol pub) x

/-- The public key at the revealed values: `PK.seed` and the value at `rootPos`. -/
def pkOf {T : Finset HPos} (w : RevealVals XD T) : PublicKey :=
  ⟨pub.seed, extendVals w rootPos⟩

/-- **The SUF-CMA game as runtime 2 runs it, as a template**: reveal the root, run the adversary on
the public key against the challenger of runtime 2 with its signing transcript, verify the forgery
through read ports, and return the winning condition. `realizeT v (gameT M upd pol pub A)` is the
game at the hidden values `v`. -/
noncomputable def gameT (A : SAdversary) :
    QComp (SSpec M) (QReg.of Unit) (QReg.of Unit) Bool :=
  revealThen goodAll {.val rootPos} fun r₀ ↦
    (challengedT M upd pol pub (withSignLog (A (pkOf pub r₀.1)))).bind fun run ↦
      (readLiftQ goodAll ((readsProgram M pub.perm _
        (schemeWithHash.verify (pkOf pub r₀.1) run.1)).map Prod.fst)).bind fun verified ↦
        QuantumComp₂.pure (RandomPermutationModel.sufCmaScheme.winningCondition run.2 run.1 &&
          verified)

/-- **The challenge prefix of the game**: reveal the root and run the adversary on the public key
against the challenger of runtime 2 with its signing transcript; return the public key, the
forgery and the transcript. -/
noncomputable def prefixT (A : SAdversary) :
    QComp (SSpec M) (QReg.of Unit) (QReg.of Unit)
      (PublicKey × (Forgery × SignLog Message (Option Signature))) :=
  revealThen goodAll {.val rootPos} fun r₀ ↦
    (challengedT M upd pol pub (withSignLog (A (pkOf pub r₀.1)))).bind fun run ↦
      QuantumComp₂.pure (pkOf pub r₀.1, run)

/-- **The verification of the game**: verify the forgery under the public key through read ports
and return the winning condition. -/
noncomputable def verifyT (x : PublicKey × (Forgery × SignLog Message (Option Signature))) :
    QComp (SSpec M) (QReg.of Unit) (QReg.of Unit) Bool :=
  (readLiftQ goodAll ((readsProgram M pub.perm _ (schemeWithHash.verify x.1 x.2.1)).map
    Prod.fst)).bind fun verified ↦
    QuantumComp₂.pure (RandomPermutationModel.sufCmaScheme.winningCondition x.2.2 x.2.1 && verified)

omit [Fintype M] [DecidableEq M] in
/-- **The game is its challenge prefix, then the verification.** -/
theorem gameT_eq_prefixT_bind (A : SAdversary) :
    gameT M upd pol pub A = (prefixT M upd pol pub A).bind (verifyT M pub) := by
  simp only [gameT, prefixT, revealThen_bind, QuantumComp₂.bind_assoc, QuantumComp₂.pure_bind]
  rfl

/-! ## The game reveals before it programs -/

omit [Fintype M] [DecidableEq M] in
theorem disc_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) (T : Finset HPos)
    (h : ∀ p ∈ ps, p.need ⊆ T) : Disc (progPorts M B ps) T := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact disc_progThen p trivial _ T (h p List.mem_cons_self)
      (ih fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

omit [Fintype M] [DecidableEq M] in
theorem disc_progSlots (B : QReg) (ss : List Slot) (T : Finset HPos)
    (h : ∀ s ∈ ss, valSet (slotNeed s) ⊆ T) : Disc (progSlots M pub B ss) T := by
  induction ss generalizing T with
  | nil => trivial
  | cons s ss ih =>
    refine disc₂_bind _ _ (disc_progPorts M B _ T fun p hp ↦ ?_) fun _ T' hT' ↦
      ih T' fun s' hs' ↦ (h s' (List.mem_cons_of_mem _ hs')).trans hT'
    rw [need_of_mem_slotPorts pub hp]
    exact h s List.mem_cons_self

omit [Fintype M] [DecidableEq M] in
theorem disc_forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (T : Finset HPos) : Disc (forsOpenT M pub B idx lv) T :=
  disc_revealThen _ _ T fun _ ↦ disc₂_bind _ _ (disc_progSlots M pub B _ _ fun _ hs ↦
    (valSet_mono ((slotNeed_subset_needUnion hs).trans (Finset.subset_union_left.trans
      Finset.subset_union_left))).trans Finset.subset_union_right) fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem disc_signLayerT (B : QReg) (K : Key) (T : Finset HPos) :
    Disc (signLayerT M upd pub B K) T := by
  refine disc_revealThen _ _ T fun _ ↦ disc₂_bind _ _ (disc_readLift _ _) fun g T' _ ↦ ?_
  rcases g with _ | ⟨c, x⟩
  · trivial
  · refine disc_revealThen _ _ T' fun r ↦ disc₂_bind _ _ (disc_progSlots M pub B _ _ fun s hs ↦ ?_)
      fun _ _ _ ↦ trivial
    exact (valSet_mono ((slotNeed_subset_needUnion hs).trans (Finset.subset_union_left.trans
      Finset.subset_union_left))).trans Finset.subset_union_right

theorem hmsgNeed_subset (T T' : Finset HPos) (msg : Message) (i : DigestCall) :
    hmsgNeed pol T msg i ⊆ T' ∪ {.val rootPos, .rnd msg} ∪ pol.need T msg := by
  intro s hs
  simp only [hmsgNeed, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
  · exact Finset.mem_union_right _ (pol.out_mem_need T msg i)

omit [Fintype M] [DecidableEq M] in
theorem disc_signT (B : QReg) (msg : Message) (T : Finset HPos) :
    Disc (signT M upd pol pub B msg) T := by
  refine disc_revealThen _ _ T fun r₁ ↦ disc_revealThen _ _ _ fun r₂ ↦
    disc₂_bind _ _ (disc_progPorts M B _ _ fun p hp ↦ ?_) fun _ T₁ _ ↦
      disc₂_bind _ _ (disc_forsOpenT M pub B _ _ T₁) fun _ T₂ _ ↦
        disc₂_bind _ _ (disc_signLayerT M upd pub B _ T₂) fun s₀ T₃ _ ↦ ?_
  · rcases List.mem_append.mp hp with hp | hp <;>
      exact (need_of_mem_hmsgPorts pub hp).symm ▸ hmsgNeed_subset pol _ T msg _
  · rcases s₀ with _ | bottom
    · trivial
    · refine disc₂_bind _ _ (disc_signLayerT M upd pub B _ T₃) fun s₁ T₄ _ ↦ ?_
      rcases s₁ with _ | middle
      · trivial
      · refine disc₂_bind _ _ (disc_signLayerT M upd pub B _ T₄) fun s₂ _ _ ↦ ?_
        rcases s₂ with _ | top <;> trivial

omit [Fintype M] [DecidableEq M] in
theorem disc_challengeT (A : QReg) (c : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A)
    (T : Finset HPos) : Disc (challengeT M upd pol pub A c) T := by
  rcases c with o | ⟨p | msg, E, ℓ⟩
  · exact disc_readLift _ _
  · exact disc_readLift _ _
  · exact disc_bind _ _ (disc₂_bind _ _ (disc_act _ _) fun _ T' _ ↦
      disc_signT M upd pol pub _ msg T') fun _ _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- **The game reveals before it programs**: every program port hardwires a cell whose coordinates
the signature revealed just before. -/
theorem disc_gameT (A : SAdversary) (T : Finset HPos) : Disc (gameT M upd pol pub A) T :=
  disc_revealThen _ _ T fun _ ↦ disc₂_bind _ _
    (disc_substitute _ (disc_challengeT M upd pol pub) _ _)
    fun _ _ _ ↦ disc₂_bind _ _ (disc_readLift _ _) fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- The challenge prefix reveals before it programs. -/
theorem disc_prefixT (A : SAdversary) (T : Finset HPos) : Disc (prefixT M upd pol pub A) T :=
  disc_revealThen _ _ T fun _ ↦ disc₂_bind _ _
    (disc_substitute _ (disc_challengeT M upd pol pub) _ _) fun _ _ _ ↦ trivial

/-! ## The game's reads keep the label -/

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    KeepsLab (progPorts M B ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact keepsLab_progThen p trivial _ ih

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_progSlots (B : QReg) (ss : List Slot) : KeepsLab (progSlots M pub B ss) := by
  induction ss with
  | nil => trivial
  | cons s ss ih => exact keepsLab₂_bind _ _ (keepsLab_progPorts M B _) fun _ ↦ ih

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    KeepsLab (forsOpenT M pub B idx lv) :=
  keepsLab_revealThen _ _ fun _ ↦ keepsLab₂_bind _ _ (keepsLab_progSlots M pub B _) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_signLayerT (B : QReg) (K : Key) : KeepsLab (signLayerT M upd pub B K) := by
  refine keepsLab_revealThen _ _ fun _ ↦ keepsLab₂_bind _ _ (keepsLab_readLift _) fun g ↦ ?_
  rcases g with _ | ⟨c, x⟩
  · trivial
  · exact keepsLab_revealThen _ _ fun _ ↦ keepsLab₂_bind _ _ (keepsLab_progSlots M pub B _)
      fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_signT (B : QReg) (msg : Message) : KeepsLab (signT M upd pol pub B msg) := by
  refine keepsLab_revealThen _ _ fun _ ↦ keepsLab_revealThen _ _ fun _ ↦
    keepsLab₂_bind _ _ (keepsLab_progPorts M B _) fun _ ↦
      keepsLab₂_bind _ _ (keepsLab_forsOpenT M pub B _ _) fun _ ↦
        keepsLab₂_bind _ _ (keepsLab_signLayerT M upd pub B _) fun s₀ ↦ ?_
  rcases s₀ with _ | bottom
  · trivial
  · refine keepsLab₂_bind _ _ (keepsLab_signLayerT M upd pub B _) fun s₁ ↦ ?_
    rcases s₁ with _ | middle
    · trivial
    · refine keepsLab₂_bind _ _ (keepsLab_signLayerT M upd pub B _) fun s₂ ↦ ?_
      rcases s₂ with _ | top <;> trivial

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_challengeT (A : QReg) (c : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    KeepsLab (challengeT M upd pol pub A c) := by
  rcases c with o | ⟨p | msg, E, ℓ⟩
  · exact keepsLab_readLift _
  · exact keepsLab_readLift _
  · exact keepsLab_bind _ _ (keepsLab₂_bind _ _ (keepsLab_act _) fun _ ↦
      keepsLab_signT M upd pol pub _ msg) fun _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- **The game's reads keep the label** (Mismatch's `KeepsLab`). -/
theorem keepsLab_gameT (A : SAdversary) : KeepsLab (gameT M upd pol pub A) :=
  keepsLab_revealThen _ _ fun _ ↦ keepsLab₂_bind _ _
    (keepsLab_substitute _ (keepsLab_challengeT M upd pol pub) _) fun _ ↦
      keepsLab₂_bind _ _ (keepsLab_readLift _) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- The challenge prefix's reads keep the label. -/
theorem keepsLab_prefixT (A : SAdversary) : KeepsLab (prefixT M upd pol pub A) :=
  keepsLab_revealThen _ _ fun _ ↦ keepsLab₂_bind _ _
    (keepsLab_substitute _ (keepsLab_challengeT M upd pol pub) _) fun _ ↦ trivial

/-! ## Lazy sampling -/

/-- **The lazy-sampling property of the runtime-2 game.** For every initial state that does not
depend on the hidden values, the realized games satisfy `ViewBy` for runtime 2 with record ports
and the memory label, at every call. -/
theorem viewBy_gameT (A : SAdversary) (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (j : ℕ) :
    ViewBy (runtimeR m₀) LocalSig.Interp.instruments (fun r ↦ r.2.2.1)
      (fun v ↦ realizeT v (gameT M upd pol pub A)) (fun _ ↦ ρ) j :=
  viewBy_runtimeR_of_disc _ m₀ (gameT M upd pol pub A) ∅ (disc_gameT M upd pol pub A ∅)
    (fun _ ↦ ρ) (lazy_const _ ρ) (fun _ ↦ suppAt_empty _ ρ) j

/-- **`ViewByOn` for the runtime-2 game**, for the weights vanishing on the program ports. -/
theorem viewByOn_gameT (A : SAdversary) (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (j : ℕ) :
    ViewByOn (runtimeR m₀) LocalSig.Interp.instruments (fun i ↦ i.isLeft = true)
      (fun r ↦ r.2.2.1) (fun v ↦ realizeT v (gameT M upd pol pub A)) (fun _ ↦ ρ) j :=
  (viewBy_gameT M upd pol pub A m₀ ρ j).viewByOn _

end Quantum.Sphincs.Assembly

end
