module

public import Quantum.Qrom.Sphincs.GameT
public import Quantum.Qrom.Sphincs.StreamGame
public import Quantum.Xmss.Assembly.Masses
public import Quantum.Xmss.Assembly.PrefixRun

@[expose] public section

/-!
# The call invariants of leanSPHINCS's runtime-2 game in the QROM

**The hybrid's invariant** (`SrcInv`, Masses' `hinv`): at every call of the ports `Q` (no program
or record port; the adversary's calls of `F` and the reads), every table position whose source is
revealed has its cell hardwired. The source `srcOf p` of a position is the coordinate of the
input value its cell carries in full (`inPos`): the chain value before a chain step, chain `0`'s
end for a one-time leaf, the left child for a node or a FORS node, the secret for a FORS leaf,
FORS tree `0`'s root for the roots compression, `SK.prf` for `R(M)`, `R(M)` for a digest cell; the
master seed for `SK.prf`, `PK.seed` and the PRF positions.

* **Combinatorics**: a source in `layerReveal K x` is a source of a position of `layerPos K x`
  (`mem_layerPos_of_srcOf_mem`), one in `forsReveal idx lv` of a position of `forsPos idx lv`
  (`mem_forsPos_of_srcOf_mem`); `PK.seed`, `PK.root` and the values the keys sign are no source
  (`revealSet_pkReveal`, `revealSet_msgPos`), `R(M)` is the digest cell's
  (`revealSet_sigReveal`), and a digest policy revealing no value coordinate reveals none
  (`DigestPolicy.NoVal`, `noVal_msgPol`, `noVal_strPol`).
* **Pending ports** (`InvP`, `HP`): between a reveal and the end of its program calls the cells it
  discloses are pending (QRPM `Quantum.Sphincs.Assembly.GameTCalls`). `forallQueries_gameT`,
  `hinv_gameT`: from states with an empty memory label.
-/

open Matrix IPFunctor
open scoped Kronecker
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

universe u v w w₁

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key keyOf msgPos indexBelow layerBelow)
open Quantum.Xmss.Hybrid (LazyProg restrictTo ReadMono querySupportedOn_queryStep progUpdate
  hwProgKraus_ne_zero_snd clsKraus_ne_zero_cls)
open Quantum.Xmss.Assembly (tmplSpec recHwSpec recSpec readLift readLens realizeT revealThen
  progThen RevealVals memLab liftRead invSupp recKraus_ne_zero runtimeR)

attribute [local irreducible] sphincsRom

/- Instance search for the run families over the register exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## Sources -/

section sources

/-- Chain `0` of a one-time key. -/
def chainZero : ChainIndex :=
  ⟨0, by decide⟩

/-- The last chain step (leaving position `chainLength - 2`). -/
def stepLast : ChainStep :=
  ⟨chainLength - 2, by decide⟩

/-- FORS tree `0`. -/
def forsZero : ForsTreeIndex :=
  ⟨0, by decide⟩

/-- The top FORS node level (height `a`). -/
def forsTop : Fin forsTreeHeight :=
  ⟨forsTreeHeight - 1, by decide⟩

/-- The FORS root node index. -/
def forsRootNode : ForsLeafIndex :=
  ⟨0, by decide⟩

/-- **The input position whose value a position's input carries in full**: the chain value
before a chain step, chain `0`'s end for a one-time leaf, the left child for a node or a FORS node,
the secret for a FORS leaf, FORS tree `0`'s root for the roots compression, `SK.prf` for `R(M)`,
`R(M)` for a digest cell; none for the positions keyed by the master seed. -/
def inPos : RawPos → Option RawPos
  | .chain l τ e i step =>
      if step.val = 0 then some (.chainStart l τ e i)
      else some (.chain l τ e i ⟨step.val - 1, by have := step.isLt; omega⟩)
  | .leaf l τ e => some (.chain l τ e chainZero stepLast)
  | .node l τ level j =>
      if level.val = 0 then some (.leaf l τ (leafOfNat (2 * j.val)))
      else if hj : 2 * j.val < 2 ^ layerHeight topLayer then
        some (.node l τ ⟨level.val - 1, by have := level.isLt; omega⟩ ⟨2 * j.val, hj⟩)
      else none
  | .forsLeaf idx κ s => some (.forsSecret idx κ s)
  | .forsNode idx κ level j =>
      if level.val = 0 then some (.forsLeaf idx κ (forsLeafOfNat (2 * j.val)))
      else if hj : 2 * j.val < 2 ^ forsTreeHeight then
        some (.forsNode idx κ ⟨level.val - 1, by have := level.isLt; omega⟩ ⟨2 * j.val, hj⟩)
      else none
  | .forsRoots idx => some (.forsNode idx forsZero forsTop forsRootNode)
  | .prfMsg _ => some .prfKey
  | .hmsg m => some (.prfMsg m)
  | _ => none

/-- **The source of a position's cell**: the coordinate of `inPos`, the master seed's
otherwise. -/
def srcOf (p : Pos) : TPos :=
  match inPos p.1 with
  | some q => if h : q.InRange then .val (some ⟨q, h⟩) else .val none
  | none => .val none

/-- The cell of a position at the hidden values `θ`. -/
def cellQ (θ : TVals) (p : Pos) : Qrom.HashDomain :=
  cellOf (seedOf θ) p (tabOf θ)

variable (M : Type) in
/-- **The hybrid's invariant**: every position whose source is in the memory label has its cell
hardwired. -/
def SrcInv (θ : TVals) (r : HwReg PairOut Qrom.HashDomain (Finset TPos × M)) : Prop :=
  ∀ p, srcOf p ∈ r.2.2.1 → r.2.1.1 (cellQ θ p) ≠ none

/-- **The inversion of `inPos`.** -/
theorem inPos_spec {q r : RawPos} (h : inPos q = some r) :
    (∃ (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) (s : ChainStep),
      s.val = 0 ∧ q = .chain l τ e i s ∧ r = .chainStart l τ e i) ∨
    (∃ (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) (s s' : ChainStep),
      s.val = s'.val + 1 ∧ q = .chain l τ e i s ∧ r = .chain l τ e i s') ∨
    (∃ (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex),
      q = .leaf l τ e ∧ r = .chain l τ e chainZero stepLast) ∨
    (∃ (l : Layer) (τ : TreeIndex) (k : Fin (layerHeight topLayer)) (j : TreeLeafIndex),
      k.val = 0 ∧ q = .node l τ k j ∧ r = .leaf l τ (leafOfNat (2 * j.val))) ∨
    (∃ (l : Layer) (τ : TreeIndex) (k k' : Fin (layerHeight topLayer)) (j j' : TreeLeafIndex),
      k.val = k'.val + 1 ∧ j'.val = 2 * j.val ∧ q = .node l τ k j ∧ r = .node l τ k' j') ∨
    (∃ (idx : Index) (κ : ForsTreeIndex) (s : ForsLeafIndex),
      q = .forsLeaf idx κ s ∧ r = .forsSecret idx κ s) ∨
    (∃ (idx : Index) (κ : ForsTreeIndex) (k : Fin forsTreeHeight) (j : ForsLeafIndex),
      k.val = 0 ∧ q = .forsNode idx κ k j ∧ r = .forsLeaf idx κ (forsLeafOfNat (2 * j.val))) ∨
    (∃ (idx : Index) (κ : ForsTreeIndex) (k k' : Fin forsTreeHeight) (j j' : ForsLeafIndex),
      k.val = k'.val + 1 ∧ j'.val = 2 * j.val ∧ q = .forsNode idx κ k j ∧
        r = .forsNode idx κ k' j') ∨
    (∃ idx : Index, q = .forsRoots idx ∧ r = .forsNode idx forsZero forsTop forsRootNode) ∨
    (∃ m : Message, q = .prfMsg m ∧ r = .prfKey) ∨
    (∃ m : Message, q = .hmsg m ∧ r = .prfMsg m) := by
  cases q with
  | chain l τ e i s =>
    simp only [inPos] at h
    split_ifs at h with hs
    · exact Or.inl ⟨l, τ, e, i, s, hs, rfl, (Option.some.inj h).symm⟩
    · refine Or.inr (Or.inl ⟨l, τ, e, i, s, _, ?_, rfl, (Option.some.inj h).symm⟩)
      simp only
      omega
  | leaf l τ e => exact Or.inr (Or.inr (Or.inl ⟨l, τ, e, rfl, (Option.some.inj h).symm⟩))
  | node l τ k j =>
    simp only [inPos] at h
    split_ifs at h with hk hj
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨l, τ, k, j, hk, rfl, (Option.some.inj h).symm⟩)))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, τ, k, _, j, _, ?_, rfl, rfl,
        (Option.some.inj h).symm⟩))))
      simp only
      omega
  | forsLeaf idx κ s =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨idx, κ, s, rfl,
      (Option.some.inj h).symm⟩)))))
  | forsNode idx κ k j =>
    simp only [inPos] at h
    split_ifs at h with hk hj
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨idx, κ, k, j, hk, rfl,
        (Option.some.inj h).symm⟩))))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨idx, κ, k, _, j, _,
        ?_, rfl, rfl, (Option.some.inj h).symm⟩)))))))
      simp only
      omega
  | forsRoots idx =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨idx, rfl,
      (Option.some.inj h).symm⟩))))))))
  | prfMsg m =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl,
      (Option.some.inj h).symm⟩)))))))))
  | hmsg m =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, rfl,
      (Option.some.inj h).symm⟩)))))))))
  | prfKey => simp [inPos] at h
  | publicSeed => simp [inPos] at h
  | chainStart => simp [inPos] at h
  | forsSecret => simp [inPos] at h

theorem inPos_ne_publicSeed (q : RawPos) : inPos q ≠ some .publicSeed := fun h ↦ by
  rcases inPos_spec h with ⟨_, _, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, _, h⟩ |
    ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, _, _, h⟩ |
    ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, _, _, h⟩ | ⟨_, _, h⟩ |
    ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h

theorem rawC_ne_val_none (r : RawPos) : rawC r ≠ .val none := by
  unfold rawC
  split_ifs with hr
  · cases r <;> simp [coordOf]
  · simp [seedC]

/-- A value coordinate that is `rawC r` is `r`'s, or `PK.seed`'s. -/
theorem rawC_eq_val {r : RawPos} {q : Pos} (h : rawC r = .val (some q)) :
    r = q.1 ∨ q.1 = .publicSeed := by
  unfold rawC at h
  split_ifs at h with hr
  · cases r with
    | hmsg m => simp [coordOf] at h
    | _ =>
      simp only [coordOf, SPos.val.injEq, Option.some.injEq] at h
      exact Or.inl (congrArg Subtype.val h)
  · simp only [seedC, SPos.val.injEq, Option.some.injEq] at h
    exact Or.inr (congrArg Subtype.val h).symm

/-- **A source that is `rawC r` is `inPos`'s position `r`.** -/
theorem inPos_of_srcOf {p : Pos} {r : RawPos} (h : srcOf p = rawC r) : inPos p.1 = some r := by
  unfold srcOf at h
  rcases hp : inPos p.1 with _ | q
  · rw [hp] at h
    exact absurd h.symm (rawC_ne_val_none r)
  · rw [hp] at h
    dsimp only at h
    split_ifs at h with hq
    · rcases rawC_eq_val h.symm with h' | h'
      · rw [h']
      · exact absurd (hp.trans (congrArg some h')) (inPos_ne_publicSeed _)
    · exact absurd h.symm (rawC_ne_val_none r)

theorem coordOf_eq_rawC (q : Pos) : coordOf q = rawC q.1 := by
  unfold rawC
  simp [q.2]

theorem seedC_eq_rawC : seedC = rawC .publicSeed :=
  rfl

theorem inPos_eq_chainStart {q : RawPos} {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex}
    {i : ChainIndex} (h : inPos q = some (.chainStart l τ e i)) :
    ∃ s : ChainStep, s.val = 0 ∧ q = .chain l τ e i s := by
  rcases inPos_spec h with ⟨_, _, _, _, s, hs, rfl, hr⟩ | ⟨_, _, _, _, _, _, _, _, hr⟩ |
    ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, hr⟩ |
    ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, hr⟩ | ⟨_, _, hr⟩ |
    ⟨_, _, hr⟩ | ⟨_, _, hr⟩ <;> cases hr
  exact ⟨s, hs, rfl⟩

theorem inPos_eq_chain {q : RawPos} {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex}
    {i : ChainIndex} {s' : ChainStep} (h : inPos q = some (.chain l τ e i s')) :
    (∃ s : ChainStep, s.val = s'.val + 1 ∧ q = .chain l τ e i s) ∨ q = .leaf l τ e := by
  rcases inPos_spec h with ⟨_, _, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, s, _, hs, rfl, hr⟩ |
    ⟨_, _, _, rfl, hr⟩ | ⟨_, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, hr⟩ |
    ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, hr⟩ | ⟨_, _, hr⟩ |
    ⟨_, _, hr⟩ | ⟨_, _, hr⟩ <;> cases hr
  · exact Or.inl ⟨s, hs, rfl⟩
  · exact Or.inr rfl

theorem inPos_eq_leaf {q : RawPos} {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex}
    (h : inPos q = some (.leaf l τ e)) :
    ∃ (k : Fin (layerHeight topLayer)) (j : TreeLeafIndex), k.val = 0 ∧ q = .node l τ k j ∧
      leafOfNat (2 * j.val) = e := by
  rcases inPos_spec h with ⟨_, _, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, hr⟩ |
    ⟨_, _, _, _, hr⟩ | ⟨_, _, k, j, hk, rfl, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, hr⟩ |
    ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, hr⟩ | ⟨_, _, hr⟩ |
    ⟨_, _, hr⟩ | ⟨_, _, hr⟩ <;> cases hr
  exact ⟨k, j, hk, rfl, rfl⟩

theorem inPos_eq_node {q : RawPos} {l : Layer} {τ : TreeIndex} {k' : Fin (layerHeight topLayer)}
    {j' : TreeLeafIndex} (h : inPos q = some (.node l τ k' j')) :
    ∃ (k : Fin (layerHeight topLayer)) (j : TreeLeafIndex), k.val = k'.val + 1 ∧
      j'.val = 2 * j.val ∧ q = .node l τ k j := by
  rcases inPos_spec h with ⟨_, _, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, hr⟩ |
    ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, hr⟩ | ⟨_, _, k, _, j, _, hk, hj, rfl, hr⟩ |
    ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, hr⟩ | ⟨_, _, hr⟩ |
    ⟨_, _, hr⟩ | ⟨_, _, hr⟩ <;> cases hr
  exact ⟨k, j, hk, hj, rfl⟩

theorem inPos_eq_forsSecret {q : RawPos} {idx : Index} {κ : ForsTreeIndex} {s : ForsLeafIndex}
    (h : inPos q = some (.forsSecret idx κ s)) : q = .forsLeaf idx κ s := by
  rcases inPos_spec h with ⟨_, _, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, hr⟩ |
    ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, hr⟩ |
    ⟨_, _, _, rfl, hr⟩ | ⟨_, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, hr⟩ | ⟨_, _, hr⟩ |
    ⟨_, _, hr⟩ | ⟨_, _, hr⟩ <;> cases hr
  rfl

theorem inPos_eq_forsLeaf {q : RawPos} {idx : Index} {κ : ForsTreeIndex} {s : ForsLeafIndex}
    (h : inPos q = some (.forsLeaf idx κ s)) :
    ∃ (k : Fin forsTreeHeight) (j : ForsLeafIndex), k.val = 0 ∧ q = .forsNode idx κ k j ∧
      forsLeafOfNat (2 * j.val) = s := by
  rcases inPos_spec h with ⟨_, _, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, hr⟩ |
    ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, hr⟩ |
    ⟨_, _, _, _, hr⟩ | ⟨_, _, k, j, hk, rfl, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, hr⟩ | ⟨_, _, hr⟩ |
    ⟨_, _, hr⟩ | ⟨_, _, hr⟩ <;> cases hr
  exact ⟨k, j, hk, rfl, rfl⟩

theorem inPos_eq_forsNode {q : RawPos} {idx : Index} {κ : ForsTreeIndex}
    {k' : Fin forsTreeHeight} {j' : ForsLeafIndex} (h : inPos q = some (.forsNode idx κ k' j')) :
    (∃ (k : Fin forsTreeHeight) (j : ForsLeafIndex), k.val = k'.val + 1 ∧ j'.val = 2 * j.val ∧
      q = .forsNode idx κ k j) ∨ q = .forsRoots idx := by
  rcases inPos_spec h with ⟨_, _, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, hr⟩ |
    ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, hr⟩ |
    ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, hr⟩ | ⟨_, _, k, _, j, _, hk, hj, rfl, hr⟩ |
    ⟨_, rfl, hr⟩ | ⟨_, _, hr⟩ | ⟨_, _, hr⟩ <;> cases hr
  · exact Or.inl ⟨k, j, hk, hj, rfl⟩
  · exact Or.inr rfl

theorem inPos_ne_forsRoots (q : RawPos) (idx : Index) : inPos q ≠ some (.forsRoots idx) :=
  fun h ↦ by
  rcases inPos_spec h with ⟨_, _, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, hr⟩ |
    ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, hr⟩ |
    ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, hr⟩ | ⟨_, _, hr⟩ |
    ⟨_, _, hr⟩ | ⟨_, _, hr⟩ <;> cases hr

theorem inPos_eq_prfMsg {q : RawPos} {m : Message} (h : inPos q = some (.prfMsg m)) :
    q = .hmsg m := by
  rcases inPos_spec h with ⟨_, _, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, hr⟩ |
    ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, hr⟩ |
    ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, hr⟩ | ⟨_, _, hr⟩ |
    ⟨_, _, hr⟩ | ⟨_, rfl, hr⟩ <;> cases hr
  rfl

/-! ### Arithmetic of the paths -/

theorem two_mul_lt_pow {j h k : ℕ} (hk : k < h) (hj : j < 2 ^ (h - (k + 1))) :
    2 * j < 2 ^ (h - k) := by
  have : 2 ^ (h - k) = 2 * 2 ^ (h - (k + 1)) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

theorem two_mul_lt_1024 {j h k : ℕ} (hh : h ≤ 10) (hk : k < h) (hj : j < 2 ^ (h - (k + 1))) :
    2 * j < 2 ^ 10 :=
  lt_of_lt_of_le (two_mul_lt_pow hk hj) (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem shiftRight_succ_le (e k : ℕ) : e >>> (k + 1) ≤ e / 2 := by
  rw [Nat.shiftRight_eq_div_pow, pow_succ', ← Nat.div_div_eq_div_mul]
  exact Nat.div_le_self _ _

theorem xor_one_div_two' (n : ℕ) : (n ^^^ 1) / 2 = n / 2 := by
  rcases Nat.even_or_odd n with h | h
  · rw [Nat.xor_one_of_even h]
    have := Nat.even_iff.1 h
    omega
  · rw [Nat.xor_one_of_odd h]
    have := Nat.odd_iff.1 h
    omega

theorem xor_one_lt_1024 {n : ℕ} (h : n < 2 ^ 10) : n ^^^ 1 < 2 ^ 10 := by
  rcases Nat.even_or_odd n with he | ho
  · rw [Nat.xor_one_of_even he]
    have := Nat.even_iff.1 he
    omega
  · rw [Nat.xor_one_of_odd ho]
    omega

theorem shiftRight_lt_1024 (e : TreeLeafIndex) (z : ℕ) : e.val >>> z < 2 ^ 10 :=
  lt_of_le_of_lt (Nat.shiftRight_le _ _) e.isLt

theorem leafOfNat_two_mul {j a : ℕ} (hj : 2 * j < 2 ^ 10) (ha : a < 2 ^ 10)
    (h : leafOfNat (2 * j) = leafOfNat a) : 2 * j = a := by
  have h' := congrArg Fin.val h
  have hT : 2 ^ layerHeight topLayer = 2 ^ 10 := rfl
  simp only [leafOfNat, hT] at h'
  rwa [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt ha] at h'

theorem forsLeafOfNat_two_mul {j a : ℕ} (hj : 2 * j < 2 ^ 10) (ha : a < 2 ^ 10)
    (h : forsLeafOfNat (2 * j) = forsLeafOfNat a) : 2 * j = a := by
  have h' := congrArg Fin.val h
  have hT : 2 ^ forsTreeHeight = 2 ^ 10 := rfl
  simp only [forsLeafOfNat, hT] at h'
  rwa [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt ha] at h'

/-! ### Positions of a publication -/

theorem mem_mkPos_of {p : Pos} {q : RawPos} (h : p.1 = q) : p ∈ mkPos q := by
  unfold mkPos
  split_ifs with hq
  · exact List.mem_singleton.2 (Subtype.ext h)
  · exact absurd (h ▸ p.2) hq

theorem chain_mem_layerPos {K : Key} {x : Encoding} {p : Pos} {i : ChainIndex} {s : ChainStep}
    (h : p.1 = .chain K.1 K.2.1 K.2.2 i s) (hs : (x i).val ≤ s.val) : p ∈ layerPos K x := by
  unfold layerPos
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨i,
    List.mem_finRange _, List.mem_flatMap.2 ⟨s, List.mem_filter.2 ⟨List.mem_finRange _,
      decide_eq_true hs⟩, mem_mkPos_of h⟩⟩))

theorem leaf_mem_layerPos {K : Key} {x : Encoding} {p : Pos}
    (h : p.1 = .leaf K.1 K.2.1 K.2.2) : p ∈ layerPos K x := by
  unfold layerPos
  exact List.mem_append_left _ (List.mem_append_right _ (mem_mkPos_of h))

theorem node_mem_layerPos {K : Key} {x : Encoding} {p : Pos} {k : Fin (layerHeight topLayer)}
    {j : TreeLeafIndex} (h : p.1 = .node K.1 K.2.1 k j) (hk : k.val < layerHeight K.1)
    (hj : j.val = K.2.2.val >>> (k.val + 1)) : p ∈ layerPos K x := by
  unfold layerPos
  refine List.mem_append_right _ (List.mem_flatMap.2 ⟨k.val, List.mem_range.2 hk, ?_⟩)
  unfold nodePos
  rw [← hj]
  split_ifs with hc
  · exact mem_mkPos_of h
  · exact absurd ⟨k.isLt, j.isLt⟩ hc

/-- The positions of a layer publication. -/
theorem mem_layerPos_cases {K : Key} {x : Encoding} {q : Pos} (h : q ∈ layerPos K x) :
    (∃ (i : ChainIndex) (s : ChainStep), (x i).val ≤ s.val ∧ q.1 = .chain K.1 K.2.1 K.2.2 i s) ∨
      q.1 = .leaf K.1 K.2.1 K.2.2 ∨
      ∃ (k : Fin (layerHeight topLayer)) (j : TreeLeafIndex), q.1 = .node K.1 K.2.1 k j ∧
        k.val < layerHeight K.1 ∧ j.val = K.2.2.val >>> (k.val + 1) := by
  unfold layerPos at h
  rcases List.mem_append.1 h with h | h
  · rcases List.mem_append.1 h with h | h
    · obtain ⟨i, -, h⟩ := List.mem_flatMap.1 h
      obtain ⟨s, hs, h⟩ := List.mem_flatMap.1 h
      exact Or.inl ⟨i, s, by simpa using (List.mem_filter.1 hs).2, mem_mkPos h⟩
    · exact Or.inr (Or.inl (mem_mkPos h))
  · obtain ⟨lev, hl, h⟩ := List.mem_flatMap.1 h
    unfold nodePos at h
    split_ifs at h with hc
    · exact Or.inr (Or.inr ⟨⟨lev, hc.1⟩, ⟨_, hc.2⟩, mem_mkPos h, List.mem_range.1 hl, rfl⟩)
    · exact absurd h List.not_mem_nil

theorem forsLeaf_mem_forsPos {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex} {p : Pos}
    {κ : ForsTreeIndex} (h : p.1 = .forsLeaf idx κ (lv κ)) : p ∈ forsPos idx lv := by
  unfold forsPos
  exact List.mem_append_left _ (List.mem_flatMap.2 ⟨κ, List.mem_finRange _,
    List.mem_append_left _ (mem_mkPos_of h)⟩)

theorem forsNode_mem_forsPos {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex} {p : Pos}
    {κ : ForsTreeIndex} {k : Fin forsTreeHeight} {j : ForsLeafIndex}
    (h : p.1 = .forsNode idx κ k j) (hj : j.val = (lv κ).val >>> (k.val + 1)) :
    p ∈ forsPos idx lv := by
  unfold forsPos
  refine List.mem_append_left _ (List.mem_flatMap.2 ⟨κ, List.mem_finRange _,
    List.mem_append_right _ (List.mem_flatMap.2 ⟨k.val, List.mem_range.2 k.isLt, ?_⟩)⟩)
  unfold forsNodePos
  rw [← hj]
  split_ifs with hc
  · exact mem_mkPos_of h
  · exact absurd ⟨k.isLt, j.isLt⟩ hc

theorem forsRoots_mem_forsPos {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex} {p : Pos}
    (h : p.1 = .forsRoots idx) : p ∈ forsPos idx lv := by
  unfold forsPos
  exact List.mem_append_right _ (mem_mkPos_of h)

/-- The positions of a FORS opening. -/
theorem mem_forsPos_cases {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex} {q : Pos}
    (h : q ∈ forsPos idx lv) :
    (∃ κ, q.1 = .forsLeaf idx κ (lv κ)) ∨
      (∃ (κ : ForsTreeIndex) (k : Fin forsTreeHeight) (j : ForsLeafIndex),
        q.1 = .forsNode idx κ k j ∧ j.val = (lv κ).val >>> (k.val + 1)) ∨
      q.1 = .forsRoots idx := by
  unfold forsPos at h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨κ, -, h⟩ := List.mem_flatMap.1 h
    rcases List.mem_append.1 h with h | h
    · exact Or.inl ⟨κ, mem_mkPos h⟩
    · obtain ⟨k, hk, h⟩ := List.mem_flatMap.1 h
      unfold forsNodePos at h
      split_ifs at h with hc
      · exact Or.inr (Or.inl ⟨κ, ⟨k, hc.1⟩, ⟨_, hc.2⟩, mem_mkPos h, rfl⟩)
      · exact absurd h List.not_mem_nil
  · exact Or.inr (Or.inr (mem_mkPos h))

theorem mem_needUnion {s : TPos} : ∀ {ps : List Pos}, s ∈ needUnion ps → ∃ q ∈ ps, s ∈ progNeed q
  | [], h => absurd h (Finset.notMem_empty _)
  | q :: ps, h => by
    rcases Finset.mem_union.1 h with h | h
    · exact ⟨q, List.mem_cons_self, h⟩
    · obtain ⟨q', hq', h'⟩ := mem_needUnion h
      exact ⟨q', List.mem_cons_of_mem _ hq', h'⟩

/-! ### Sources revealed by a publication -/

/-- **A revealed chain value** at or past the opened position is the source of a position of the
layer publication. -/
theorem mem_layerPos_of_chainC {K : Key} {x : Encoding} {p : Pos} {i : ChainIndex} {j : ℕ}
    (h : srcOf p = chainC K.1 K.2.1 K.2.2 i j) (hj : (x i).val ≤ j) : p ∈ layerPos K x := by
  cases j with
  | zero =>
    obtain ⟨s, hs, hp⟩ := inPos_eq_chainStart (inPos_of_srcOf h)
    exact chain_mem_layerPos hp (by omega)
  | succ j =>
    by_cases hj' : j < chainLength - 1
    · have h' : srcOf p = rawC (.chain K.1 K.2.1 K.2.2 i ⟨j, hj'⟩) := by
        rw [h]
        simp only [chainC, hj', ↓reduceDIte]
      rcases inPos_eq_chain (inPos_of_srcOf h') with ⟨s, hs, hp⟩ | hp
      · exact chain_mem_layerPos hp (by simp only at hs; omega)
      · exact leaf_mem_layerPos hp
    · have h' : srcOf p = rawC .publicSeed := by
        rw [h]
        simp only [chainC, hj', ↓reduceDIte]
        rfl
      exact absurd (inPos_of_srcOf h') (inPos_ne_publicSeed _)

/-- **A revealed tree value** whose parent is on the publication's path is the source of a
position of the layer publication. -/
theorem mem_layerPos_of_treeC {K : Key} {x : Encoding} {p : Pos} {lev a : ℕ}
    (h : srcOf p = treeC K.1 K.2.1 lev a) (ha : a < 2 ^ 10)
    (hpar : lev < layerHeight K.1 → a / 2 = K.2.2.val >>> (lev + 1)) : p ∈ layerPos K x := by
  have hH := Quantum.Sphincs.layerHeight_le K.1
  cases lev with
  | zero =>
    obtain ⟨k, j, hk, hp, hl⟩ :=
      inPos_eq_leaf (inPos_of_srcOf (r := .leaf K.1 K.2.1 (leafOfNat a)) h)
    have hpr : RawPos.InRange _ := hp ▸ p.2
    obtain ⟨-, hk', hj'⟩ := hpr
    rw [hk] at hk' hj'
    have h2 := leafOfNat_two_mul (two_mul_lt_1024 hH hk' hj') ha hl
    refine node_mem_layerPos hp (by omega) ?_
    have := hpar (by omega)
    rw [hk]
    omega
  | succ lev =>
    by_cases hc : lev < layerHeight topLayer ∧ a < 2 ^ layerHeight topLayer
    · have h' : srcOf p = rawC (.node K.1 K.2.1 ⟨lev, hc.1⟩ ⟨a, hc.2⟩) := by
        rw [h]
        simp only [treeC, hc, and_self, ↓reduceDIte]
      obtain ⟨k, j, hk, hj, hp⟩ := inPos_eq_node (inPos_of_srcOf h')
      have hpr : RawPos.InRange _ := hp ▸ p.2
      obtain ⟨-, hk', -⟩ := hpr
      simp only at hk hj
      refine node_mem_layerPos hp hk' ?_
      have := hpar (by omega)
      rw [hk]
      omega
    · have h' : srcOf p = rawC .publicSeed := by
        rw [h]
        simp only [treeC, hc, ↓reduceDIte]
        rfl
      exact absurd (inPos_of_srcOf h') (inPos_ne_publicSeed _)

/-- **A revealed FORS secret** of an opened leaf is the source of that leaf. -/
theorem mem_forsPos_of_secret {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex} {p : Pos}
    {κ : ForsTreeIndex} (h : srcOf p = rawC (.forsSecret idx κ (lv κ))) : p ∈ forsPos idx lv :=
  forsLeaf_mem_forsPos (inPos_eq_forsSecret (inPos_of_srcOf h))

/-- **A revealed FORS value** whose parent is on an opened path is the source of a position of the
opening. -/
theorem mem_forsPos_of_forsC {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex} {p : Pos}
    {κ : ForsTreeIndex} {lev a : ℕ} (h : srcOf p = forsC idx κ lev a) (ha : a < 2 ^ 10)
    (hpar : lev < forsTreeHeight → a / 2 = (lv κ).val >>> (lev + 1)) : p ∈ forsPos idx lv := by
  have hF : forsTreeHeight = 10 := rfl
  cases lev with
  | zero =>
    obtain ⟨k, j, hk, hp, hl⟩ :=
      inPos_eq_forsLeaf (inPos_of_srcOf (r := .forsLeaf idx κ (forsLeafOfNat a)) h)
    have hpr : RawPos.InRange _ := hp ▸ p.2
    have hj' : j.val < 2 ^ (forsTreeHeight - (k.val + 1)) := hpr
    rw [hk] at hj'
    have h2 := forsLeafOfNat_two_mul (two_mul_lt_1024 (le_of_eq hF) (by omega) hj') ha hl
    refine forsNode_mem_forsPos hp ?_
    have := hpar (by omega)
    rw [hk]
    omega
  | succ lev =>
    by_cases hc : lev < forsTreeHeight ∧ a < 2 ^ forsTreeHeight
    · have h' : srcOf p = rawC (.forsNode idx κ ⟨lev, hc.1⟩ ⟨a, hc.2⟩) := by
        rw [h]
        simp only [forsC, hc, and_self, ↓reduceDIte]
      rcases inPos_eq_forsNode (inPos_of_srcOf h') with ⟨k, j, hk, hj, hp⟩ | hp
      · simp only at hk hj
        refine forsNode_mem_forsPos hp ?_
        have := hpar (by have := k.isLt; omega)
        rw [hk]
        omega
      · exact forsRoots_mem_forsPos hp
    · have h' : srcOf p = rawC .publicSeed := by
        rw [h]
        simp only [forsC, hc, ↓reduceDIte]
        rfl
      exact absurd (inPos_of_srcOf h') (inPos_ne_publicSeed _)

theorem leafOfNat_val (e : TreeLeafIndex) : leafOfNat e.val = e :=
  Fin.ext (Nat.mod_eq_of_lt e.isLt)

theorem forsLeafOfNat_val (s : ForsLeafIndex) : forsLeafOfNat s.val = s :=
  Fin.ext (Nat.mod_eq_of_lt s.isLt)

theorem shiftRight_succ_div (e k : ℕ) : (e >>> (k + 1)) / 2 = e >>> (k + 2) :=
  (Nat.shiftRight_succ e (k + 1)).symm

/-- **A source revealed by a layer publication is a source of one of its positions.** -/
theorem mem_layerPos_of_srcOf_mem {K : Key} {x : Encoding} {p : Pos}
    (h : srcOf p ∈ layerReveal K x) : p ∈ layerPos K x := by
  have he : K.2.2.val < 2 ^ 10 := K.2.2.isLt
  have hH := Quantum.Sphincs.layerHeight_le K.1
  simp only [layerReveal, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h
  rcases h with (h | ⟨i, h⟩) | ⟨z, h⟩
  · obtain ⟨q, hq, hn⟩ := mem_needUnion h
    simp only [progNeed, Finset.mem_insert] at hn
    rcases mem_layerPos_cases hq with ⟨i, s, hs, hq1⟩ | hq1 | ⟨k, j, hq1, hk, hj⟩
    · rcases hn with hn | hn
      · refine mem_layerPos_of_chainC (i := i) (j := s.val + 1) ?_ (by omega)
        rw [hn, coordOf_eq_rawC, hq1]
        simp only [chainC, s.isLt, ↓reduceDIte]
      · rw [hq1] at hn
        simp only [cellNeed, Finset.mem_insert, Finset.mem_singleton] at hn
        rcases hn with hn | hn
        · exact absurd (inPos_of_srcOf (hn.trans seedC_eq_rawC)) (inPos_ne_publicSeed _)
        · exact mem_layerPos_of_chainC hn hs
    · rcases hn with hn | hn
      · refine mem_layerPos_of_treeC (lev := 0) (a := K.2.2.val) ?_ he fun _ ↦ ?_
        · rw [hn, coordOf_eq_rawC, hq1]
          simp only [treeC, leafOfNat_val]
        · simp [Nat.shiftRight_eq_div_pow]
      · rw [hq1] at hn
        simp only [cellNeed, Finset.mem_insert, Finset.mem_image, Finset.mem_univ,
          true_and] at hn
        rcases hn with hn | ⟨i, hn⟩
        · exact absurd (inPos_of_srcOf (hn.trans seedC_eq_rawC)) (inPos_ne_publicSeed _)
        · exact mem_layerPos_of_chainC hn.symm (by have := (x i).isLt; omega)
    · have hj2 : j.val ≤ K.2.2.val / 2 := hj ▸ shiftRight_succ_le _ _
      rcases hn with hn | hn
      · refine mem_layerPos_of_treeC (lev := k.val + 1) (a := j.val) ?_ j.isLt fun _ ↦ ?_
        · rw [hn, coordOf_eq_rawC, hq1]
          simp only [treeC, k.isLt, j.isLt, and_self, ↓reduceDIte]
        · rw [hj, shiftRight_succ_div]
      · rw [hq1] at hn
        simp only [cellNeed, Finset.mem_insert, Finset.mem_singleton] at hn
        rcases hn with hn | hn | hn
        · exact absurd (inPos_of_srcOf (hn.trans seedC_eq_rawC)) (inPos_ne_publicSeed _)
        · exact mem_layerPos_of_treeC hn (by omega) fun _ ↦ by rw [← hj]; omega
        · exact mem_layerPos_of_treeC hn (by omega) fun _ ↦ by rw [← hj]; omega
  · exact mem_layerPos_of_chainC h.symm le_rfl
  · refine mem_layerPos_of_treeC h.symm (xor_one_lt_1024 (shiftRight_lt_1024 _ _)) fun _ ↦ ?_
    rw [xor_one_div_two', ← Nat.shiftRight_succ]

/-- **A source revealed by a FORS opening is a source of one of its positions.** -/
theorem mem_forsPos_of_srcOf_mem {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex} {p : Pos}
    (h : srcOf p ∈ forsReveal idx lv) : p ∈ forsPos idx lv := by
  have hF : forsTreeHeight = 10 := rfl
  simp only [forsReveal, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h
  rcases h with (h | ⟨κ, h⟩) | ⟨⟨κ, z⟩, h⟩
  · obtain ⟨q, hq, hn⟩ := mem_needUnion h
    simp only [progNeed, Finset.mem_insert] at hn
    rcases mem_forsPos_cases hq with ⟨κ, hq1⟩ | ⟨κ, k, j, hq1, hj⟩ | hq1
    · have hl : (lv κ).val < 2 ^ 10 := (lv κ).isLt
      rcases hn with hn | hn
      · refine mem_forsPos_of_forsC (κ := κ) (lev := 0) (a := (lv κ).val) ?_ hl fun _ ↦ ?_
        · rw [hn, coordOf_eq_rawC, hq1]
          simp only [forsC, forsLeafOfNat_val]
        · rw [Nat.shiftRight_succ, Nat.shiftRight_zero]
      · rw [hq1] at hn
        simp only [cellNeed, Finset.mem_insert, Finset.mem_singleton] at hn
        rcases hn with hn | hn
        · exact absurd (inPos_of_srcOf (hn.trans seedC_eq_rawC)) (inPos_ne_publicSeed _)
        · exact mem_forsPos_of_secret hn
    · have hj2 : j.val ≤ (lv κ).val / 2 := hj ▸ shiftRight_succ_le _ _
      have hl : (lv κ).val < 2 ^ 10 := (lv κ).isLt
      rcases hn with hn | hn
      · refine mem_forsPos_of_forsC (κ := κ) (lev := k.val + 1) (a := j.val) ?_ j.isLt
          fun _ ↦ ?_
        · rw [hn, coordOf_eq_rawC, hq1]
          simp only [forsC, k.isLt, j.isLt, and_self, ↓reduceDIte]
        · rw [hj, shiftRight_succ_div]
      · rw [hq1] at hn
        simp only [cellNeed, Finset.mem_insert, Finset.mem_singleton] at hn
        rcases hn with hn | hn | hn
        · exact absurd (inPos_of_srcOf (hn.trans seedC_eq_rawC)) (inPos_ne_publicSeed _)
        · exact mem_forsPos_of_forsC hn (by omega) fun _ ↦ by rw [← hj]; omega
        · exact mem_forsPos_of_forsC hn (by omega) fun _ ↦ by rw [← hj]; omega
    · rcases hn with hn | hn
      · rw [coordOf_eq_rawC, hq1] at hn
        exact absurd (inPos_of_srcOf hn) (inPos_ne_forsRoots _ _)
      · rw [hq1] at hn
        simp only [cellNeed, Finset.mem_insert, Finset.mem_image, Finset.mem_univ,
          true_and] at hn
        rcases hn with hn | ⟨κ, hn⟩
        · exact absurd (inPos_of_srcOf (hn.trans seedC_eq_rawC)) (inPos_ne_publicSeed _)
        · exact mem_forsPos_of_forsC hn.symm (Nat.two_pow_pos _) fun h ↦ absurd h (lt_irrefl _)
  · exact mem_forsPos_of_secret h.symm
  · refine mem_forsPos_of_forsC h.symm (xor_one_lt_1024 (lt_of_le_of_lt (Nat.shiftRight_le _ _)
      (lv κ).isLt)) fun _ ↦ ?_
    rw [xor_one_div_two', ← Nat.shiftRight_succ]

/-! ### The other reveals -/

theorem srcOf_ne_seedC (p : Pos) : srcOf p ≠ seedC := fun h ↦
  inPos_ne_publicSeed _ (inPos_of_srcOf (h.trans seedC_eq_rawC))

/-- **The root of a tree is no source.** -/
theorem srcOf_ne_treeC_top (p : Pos) (l : Layer) (τ : TreeIndex) (a : ℕ) :
    srcOf p ≠ treeC l τ (layerHeight l) a := fun h ↦ by
  have hl : layerHeight l = layerHeight l - 1 + 1 := by unfold layerHeight; split <;> rfl
  have hH := Quantum.Sphincs.layerHeight_le l
  rw [hl] at h
  by_cases hc : layerHeight l - 1 < layerHeight topLayer ∧ a < 2 ^ layerHeight topLayer
  · have h' : srcOf p = rawC (.node l τ ⟨_, hc.1⟩ ⟨a, hc.2⟩) := by
      rw [h]
      simp only [treeC, hc, and_self, ↓reduceDIte]
    obtain ⟨k, j, hk, -, hp⟩ := inPos_eq_node (inPos_of_srcOf h')
    have hpr : RawPos.InRange _ := hp ▸ p.2
    obtain ⟨-, hk', -⟩ := hpr
    simp only at hk
    omega
  · have h' : srcOf p = rawC .publicSeed := by
      rw [h]
      simp only [treeC, hc, ↓reduceDIte]
      rfl
    exact absurd (inPos_of_srcOf h') (inPos_ne_publicSeed _)

theorem srcOf_ne_rootC (p : Pos) : srcOf p ≠ rootC :=
  srcOf_ne_treeC_top p topLayer 0 0

/-- **The value a key signs is no source.** -/
theorem srcOf_ne_msgPos (p : Pos) (K : Key) : srcOf p ≠ vcoord (msgPos K) := by
  obtain ⟨l, τ, e⟩ := K
  show srcOf p ≠ vcoord (if l.val = 0 then .forsKey (indexBelow l τ e)
    else Quantum.Sphincs.tpos (layerBelow l) (indexBelow l τ e) (layerHeight (layerBelow l)) 0)
  split_ifs
  · exact fun h ↦ inPos_ne_forsRoots _ _ (inPos_of_srcOf h)
  · have hv : vcoord (Quantum.Sphincs.tpos (layerBelow l) (indexBelow l τ e)
        (layerHeight (layerBelow l)) 0) =
        treeC (layerBelow l) (indexBelow l τ e) (layerHeight (layerBelow l)) 0 := by
      show treeC _ _ (layerHeight (layerBelow l) % (layerHeight topLayer + 1))
        (0 % 2 ^ layerHeight topLayer) = _
      rw [Nat.mod_eq_of_lt (show layerHeight (layerBelow l) < layerHeight topLayer + 1 from
        Nat.lt_succ_of_le (Quantum.Sphincs.layerHeight_le _)), Nat.zero_mod]
    rw [hv]
    exact srcOf_ne_treeC_top p _ _ _

/-- **`R(M)` is the source of `M`'s digest cell only.** -/
theorem eq_digPos_of_srcOf (p : Pos) (msg : Message) (h : srcOf p = rndC msg) : p = digPos msg :=
  Subtype.ext (inPos_eq_prfMsg (inPos_of_srcOf h))

theorem srcOf_isVal (p : Pos) : ∃ q, srcOf p = .val q := by
  unfold srcOf
  split
  · split_ifs <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

end sources

/-! ## Digest policies revealing no value coordinate -/

/-- **A digest policy revealing no value coordinate.** -/
def DigestPolicy.NoVal (pol : DigestPolicy) : Prop :=
  ∀ L msg (q : Option Pos), SPos.val q ∉ pol.need L msg

theorem noVal_msgPol : msgPol.NoVal := fun L msg q h ↦ by
  simp [msgPol, msgNeed] at h

theorem noVal_strPol : strPol.NoVal := fun L msg q h ↦ by
  simp only [strPol] at h
  rcases hs : streamIdx L msg with _ | j
  · rw [mem_strNeed_none hs] at h
    cases h
  · rw [mem_strNeed_some hs] at h
    rcases h with h | h <;> cases h

/-! ## The invariant with pending cells -/

section pending

variable {M : Type} (θ : TVals)

/-- The cells whose source is revealed by `T`. -/
def revealSet (T : Finset TPos) : Set Qrom.HashDomain :=
  {z | ∃ p, srcOf p ∈ T ∧ cellQ θ p = z}

/-- The cell a program port hardwires in `h`. -/
def progCells : HwProg PairOut Qrom.HashDomain → Set Qrom.HashDomain
  | .programH z _ => {z}
  | _ => ∅

/-- **The invariant with pending cells `C`**: every position whose source is in the memory label
has its cell hardwired or pending. -/
def InvP (C : Set Qrom.HashDomain) (r : HwReg PairOut Qrom.HashDomain (Finset TPos × M)) : Prop :=
  ∀ p, srcOf p ∈ r.2.2.1 → r.2.1.1 (cellQ θ p) ≠ none ∨ cellQ θ p ∈ C

theorem revealSet_pkReveal : revealSet θ pkReveal ⊆ ∅ := by
  rintro z ⟨p, hp, -⟩
  simp only [pkReveal, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with hp | hp
  · exact srcOf_ne_seedC p hp
  · exact srcOf_ne_rootC p hp

theorem revealSet_sigReveal (msg : Message) :
    revealSet θ {seedC, rootC, rndC msg} ⊆ {cellQ θ (digPos msg)} := by
  rintro z ⟨p, hp, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with hp | hp | hp
  · exact absurd hp (srcOf_ne_seedC p)
  · exact absurd hp (srcOf_ne_rootC p)
  · rw [eq_digPos_of_srcOf p msg hp]
    rfl

theorem revealSet_msgPos (K : Key) : revealSet θ {vcoord (msgPos K)} ⊆ ∅ := by
  rintro z ⟨p, hp, -⟩
  exact srcOf_ne_msgPos p K (Finset.mem_singleton.1 hp)

theorem revealSet_noVal {pol : DigestPolicy} (hpol : pol.NoVal) (L : Finset TPos)
    (msg : Message) : revealSet θ (pol.need L msg) ⊆ ∅ := by
  rintro z ⟨p, hp, -⟩
  obtain ⟨q, hq⟩ := srcOf_isVal p
  exact hpol L msg q (hq ▸ hp)

theorem revealSet_layerReveal (K : Key) (x : Encoding) :
    revealSet θ (layerReveal K x) ⊆ {z | ∃ p ∈ layerPos K x, cellQ θ p = z} := by
  rintro z ⟨p, hp, rfl⟩
  exact ⟨p, mem_layerPos_of_srcOf_mem hp, rfl⟩

theorem revealSet_forsReveal (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    revealSet θ (forsReveal idx lv) ⊆ {z | ∃ p ∈ forsPos idx lv, cellQ θ p = z} := by
  rintro z ⟨p, hp, rfl⟩
  exact ⟨p, mem_forsPos_of_srcOf_mem hp, rfl⟩

variable {θ}

theorem invP_of_label_empty {C : Set Qrom.HashDomain}
    {r : HwReg PairOut Qrom.HashDomain (Finset TPos × M)} (h : r.2.2.1 = ∅) : InvP θ C r := by
  intro p hl
  rw [h] at hl
  exact absurd hl (Finset.notMem_empty _)

/-- A step keeping the hardwired cells and the label keeps the invariant. -/
theorem invP_of_eq {C : Set Qrom.HashDomain}
    {r r' : HwReg PairOut Qrom.HashDomain (Finset TPos × M)} (h1 : r'.2.1 = r.2.1)
    (h2 : r'.2.2.1 = r.2.2.1) (hr : InvP θ C r) : InvP θ C r' := by
  intro p hl
  rw [h1]
  exact hr p (h2 ▸ hl)

theorem progUpdate_ne_none {c : HwProg PairOut Qrom.HashDomain}
    {W : Hw PairOut Qrom.HashDomain} {z : Qrom.HashDomain} (h : W.1 z ≠ none) :
    (progUpdate c W).1 z ≠ none := by
  cases c with
  | programH z' a =>
    show Function.update W.1 z' (some a) z ≠ none
    by_cases hz : z = z'
    · subst hz
      rw [Function.update_self]
      exact Option.some_ne_none a
    · rwa [Function.update_of_ne hz]
  | programK => exact h
  | programK' => exact h

theorem progUpdate_self_ne_none {c : HwProg PairOut Qrom.HashDomain}
    {W : Hw PairOut Qrom.HashDomain} {z : Qrom.HashDomain} (h : z ∈ progCells c) :
    (progUpdate c W).1 z ≠ none := by
  cases c with
  | programH z' a =>
    rw [Set.mem_singleton_iff.1 h]
    show Function.update W.1 z' (some a) z' ≠ none
    rw [Function.update_self]
    exact Option.some_ne_none a
  | programK => exact absurd h (Set.notMem_empty _)
  | programK' => exact absurd h (Set.notMem_empty _)

/-- A program port hardwires its cell and keeps the others: it leaves the pending set. -/
theorem invP_prog {C : Set Qrom.HashDomain} (c : HwProg PairOut Qrom.HashDomain)
    {r r' : HwReg PairOut Qrom.HashDomain (Finset TPos × M)}
    (h : r'.2 = (progUpdate c r.2.1, r.2.2)) (hr : InvP θ C r) : InvP θ (C \ progCells c) r' := by
  intro p hl
  rw [h] at hl ⊢
  rcases hr p hl with hc | hc
  · exact Or.inl (progUpdate_ne_none hc)
  · by_cases he : cellQ θ p ∈ progCells c
    · exact Or.inl (progUpdate_self_ne_none he)
    · exact Or.inr ⟨hc, he⟩

/-- A reveal of `T` adds the cells whose source is in `T` to the pending set. -/
theorem invP_reveal {C : Set Qrom.HashDomain} (T : Finset TPos)
    {r r' : HwReg PairOut Qrom.HashDomain (Finset TPos × M)}
    (h : r'.2 = (r.2.1, (r.2.2.1 ∪ T, r.2.2.2))) (hr : InvP θ C r) :
    InvP θ (C ∪ revealSet θ T) r' := by
  intro p hl
  rw [h] at hl ⊢
  rcases Finset.mem_union.1 hl with hl | hl
  · exact (hr p hl).imp_right Or.inl
  · exact Or.inr (Or.inr ⟨p, hl, rfl⟩)

theorem srcInv_of_invP {r : HwReg PairOut Qrom.HashDomain (Finset TPos × M)}
    (h : InvP θ ∅ r) : SrcInv M θ r :=
  fun p hl ↦ (h p hl).resolve_right (Set.notMem_empty _)

end pending

/-! ## The steps of `runtimeR` -/

section steps

variable {M : Type} [Fintype M] [DecidableEq M]

/-- A read port whose memory update keeps the memory label (Template's `liftRead`). -/
def LabKeep : HwRead PairOut Qrom.HashDomain (Finset TPos × M) → Prop
  | .readH _ u => ∀ m o, (u m o).1 = m.1
  | .readK _ u => ∀ m o, (u m o).1 = m.1
  | .readK' _ u => ∀ m o, (u m o).1 = m.1

omit [Fintype M] [DecidableEq M] in
theorem labKeep_liftRead (c : HwRead PairOut Qrom.HashDomain M) :
    LabKeep (liftRead (S := TPos) c) := by
  cases c <;> intro _ _ <;> rfl

omit [Fintype M] in
/-- A read port keeping the label keeps the hardwired cells and the label. -/
theorem hwReadKraus_ne_zero_keep {c : HwRead PairOut Qrom.HashDomain (Finset TPos × M)}
    (hc : LabKeep c) (r : c.Result) {u u' : Unit}
    {s s' : HwReg PairOut Qrom.HashDomain (Finset TPos × M)}
    (h : hwReadKraus c r (u', s') (u, s) ≠ 0) : s'.2.1 = s.2.1 ∧ s'.2.2.1 = s.2.2.1 := by
  cases c with
  | readH z upd =>
    simp only [hwReadKraus, readKrausH] at h
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
    exact ⟨rfl, (hc _ _).trans (congrArg Prod.fst hp).symm⟩
  | readK x upd =>
    simp only [hwReadKraus, readKrausK] at h
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
    exact ⟨rfl, (hc _ _).trans (congrArg Prod.fst hp).symm⟩
  | readK' x upd =>
    simp only [hwReadKraus, readKrausK'] at h
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
    exact ⟨rfl, (hc _ _).trans (congrArg Prod.fst hp).symm⟩

/-- A step of `runtimeR` at port `i` carries support on `P` to support on `P'`. -/
def StepR (m₀ : Finset TPos × M) (i : (recHwSpec PairOut Qrom.HashDomain TPos M).Port)
    (P P' : HwReg PairOut Qrom.HashDomain (Finset TPos × M) → Prop) : Prop :=
  ∀ r σ, QuerySupportedOn (fun m : (recHwSpec PairOut Qrom.HashDomain TPos M).In i ×
      (runtimeR m₀).D ↦ m.2) {s | P s} σ →
    QuerySupportedOn (fun m : (recHwSpec PairOut Qrom.HashDomain TPos M).Out i ×
      (runtimeR m₀).D ↦ m.2) {s | P' s} (((runtimeR m₀).step i).branch r σ)

variable {P P' : HwReg PairOut Qrom.HashDomain (Finset TPos × M) → Prop}

theorem stepR_sponge (m₀ : Finset TPos × M) (i : SpongePort)
    (hP : ∀ r r', r'.2 = r.2 → P r → P' r') : StepR m₀ (.inl (.inl (.inl i))) P P' := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inl i)))).branch r σ =
      MatrixMap.conj ((spongeHardwired PairOut Qrom.HashDomain
        (hwEmpty PairOut Qrom.HashDomain) m₀).U i) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty PairOut Qrom.HashDomain)
      m₀ i r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    hP _ _ (snd_eq_of_spongeHardwired_U_ne_zero (hwEmpty PairOut Qrom.HashDomain) m₀ i q.1 q'.1
      q.2 q'.2 hK) hq

theorem stepR_readKeep (m₀ : Finset TPos × M)
    (c : {c : HwRead PairOut Qrom.HashDomain (Finset TPos × M) //
      ReadMono (memLab PairOut Qrom.HashDomain TPos M) c})
    (hc : LabKeep c.1) (hP : ∀ r r', r'.2.1 = r.2.1 → r'.2.2.1 = r.2.2.1 → P r → P' r') :
    StepR m₀ (.inl (.inl (.inr c.1))) P P' := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inr c.1)))).branch r σ =
      MatrixMap.conj (hwReadKraus c.1 r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty PairOut Qrom.HashDomain) m₀
      c.1 r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    obtain ⟨h1, h2⟩ := hwReadKraus_ne_zero_keep hc r (u := q.1) (s := q.2) (u' := q'.1)
      (s' := q'.2) hK
    exact hP _ _ h1 h2 hq

theorem stepR_prog (m₀ : Finset TPos × M) (c : HwProg PairOut Qrom.HashDomain)
    (hP : ∀ r r', r'.2 = (progUpdate c r.2.1, r.2.2) → P r → P' r') :
    StepR m₀ (.inl (.inr c)) P P' := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inr c))).branch r σ =
      MatrixMap.conj (hwProgKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty PairOut Qrom.HashDomain) m₀
      c r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    hP _ _ (hwProgKraus_ne_zero_snd c r (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK) hq

theorem stepR_rec (m₀ : Finset TPos × M) (T : Finset TPos)
    (hP : ∀ r r', r'.2 = (r.2.1, (r.2.2.1 ∪ T, r.2.2.2)) → P r → P' r') :
    StepR m₀ (.inr T) P P' := by
  intro r σ hσ
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    hP _ _ (recKraus_ne_zero (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK) hq

/-- An operator supported on a set of register states presents, at a call, no diagonal mass
outside it. -/
theorem relabel_diag_eq_zero_of_supp (m₀ : Finset TPos × M)
    {S : Set (HwReg PairOut Qrom.HashDomain (Finset TPos × M))} {A : QReg}
    {i : (recHwSpec PairOut Qrom.HashDomain TPos M).Port} (E : QReg)
    (ℓ : A ≃ (recHwSpec PairOut Qrom.HashDomain TPos M).In i × E)
    {ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) S ρ)
    (a : ((recHwSpec PairOut Qrom.HashDomain TPos M).In i × (runtimeR m₀).D) × E)
    (ha : a.1.2 ∉ S) :
    (SubInstrument.relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).branch () ρ a a =
      0 := by
  by_contra h
  have h₁ := (hρ.branch_relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).imp
    (q' := fun m : ((recHwSpec PairOut Qrom.HashDomain TPos M).In i × (runtimeR m₀).D) × E ↦
      m.1.2)
    (S' := S) fun m hm ↦ by
      obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D).surjective m
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
  exact ha (h₁ a a h).1

end steps

/-! ## Templates that keep the invariant

`HP θ y C C'`: run from states on the pending invariant `C`, the template `y` calls the
adversary's and read ports with nothing pending, its read ports keep the label, a program port
leaves the pending set, a reveal of `T` adds the cells whose source is in `T`; it ends on `C'`. -/

section hp

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- The condition of `HP` on the pending set before a call. -/
def portPre : (SSpecQ M).Port → Set Qrom.HashDomain → Prop
  | .inl (.inl (.inl _)), C => C = ∅
  | .inl (.inl (.inr c)), C => C = ∅ ∧ LabKeep c.1
  | .inl (.inr _), _ => True
  | .inr _, _ => True

/-- The pending set after a call. -/
def portPost (θ : TVals) : (SSpecQ M).Port → Set Qrom.HashDomain → Set Qrom.HashDomain
  | .inl (.inl (.inl _)), C => C
  | .inl (.inl (.inr _)), C => C
  | .inl (.inr p), C => C \ progCells (p.1.realize θ)
  | .inr T, C => C ∪ revealSet θ T

/-- The condition before a command. -/
def cmdPre {A : QReg} : QuantumComp.Cmd L (SSpecQ M) A → Set Qrom.HashDomain → Prop
  | .prim _, _ => True
  | .query i _ _, C => portPre i C

/-- The pending set after a command. -/
def cmdPost (θ : TVals) {A : QReg} :
    QuantumComp.Cmd L (SSpecQ M) A → Set Qrom.HashDomain → Set Qrom.HashDomain
  | .prim _, C => C
  | .query i _ _, C => portPost θ i C

/-- **A template that keeps the invariant**, from the pending set `C` to the pending set `C'`. -/
def HP (θ : TVals) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor L (SSpecQ M)) Ω A → Set Qrom.HashDomain →
      Set Qrom.HashDomain → Prop
  | _, .pure _, C, C' => C ⊆ C'
  | _, .liftBind c next, C, C' => cmdPre c C ∧ ∀ b, HP θ (next b) (cmdPost θ c C) C'

omit [Fintype M] [DecidableEq M] in
theorem cmdPre_anti {A : QReg} (c : QuantumComp.Cmd L (SSpecQ M) A)
    {C D : Set Qrom.HashDomain} (hD : D ⊆ C) (h : cmdPre c C) : cmdPre c D := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · trivial
  · exact Set.subset_empty_iff.1 (h ▸ hD)
  · exact ⟨Set.subset_empty_iff.1 (h.1 ▸ hD), h.2⟩
  · trivial
  · trivial

omit [Fintype M] [DecidableEq M] in
theorem cmdPost_mono (θ : TVals) {A : QReg} (c : QuantumComp.Cmd L (SSpecQ M) A)
    {C D : Set Qrom.HashDomain} (hD : D ⊆ C) : cmdPost θ c D ⊆ cmdPost θ c C := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · exact hD
  · exact hD
  · exact hD
  · exact Set.sdiff_subset_sdiff_left hD
  · exact Set.union_subset_union_left _ hD

variable (θ : TVals)

omit [Fintype M] [DecidableEq M] in
theorem hp_mono {A : QReg} (y : IFreeM (QuantumComp.toIPFunctor L (SSpecQ M)) Ω A)
    {C C' D D' : Set Qrom.HashDomain} (hy : HP θ y C C') (hD : D ⊆ C) (hD' : C' ⊆ D') :
    HP θ y D D' := by
  induction y using IFreeM.inductionOn generalizing C D with
  | pure _ _ => exact hD.trans (hy.trans hD')
  | liftBind _ c next ih =>
    exact ⟨cmdPre_anti c hD hy.1, fun b ↦ ih b (hy.2 b) (cmdPost_mono θ c hD)⟩

omit [Fintype M] [DecidableEq M] in
theorem hp_cast {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor L (SSpecQ M)) Ω A) (C C' : Set Qrom.HashDomain) :
    HP θ (e ▸ y) C C' ↔ HP θ y C C' := by
  subst e
  rfl

omit [Fintype M] [DecidableEq M] in
theorem hp_bind {A : QReg} {Y : QReg → Type w₁}
    (x : IFreeM (QuantumComp.toIPFunctor L (SSpecQ M)) Ω A)
    (g : ∀ u, Ω u → IFreeM (QuantumComp.toIPFunctor L (SSpecQ M)) Y u)
    {C D C' : Set Qrom.HashDomain} (hx : HP θ x C D) (hg : ∀ u a, HP θ (g u a) D C') :
    HP θ (x.bind g) C C' := by
  induction x using IFreeM.inductionOn generalizing C with
  | pure _ a => exact hp_mono θ _ (hg _ a) hx subset_rfl
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

omit [Fintype M] [DecidableEq M] in
theorem hp₂_bind {A B B' : QReg} {α : Type w} {β : Type w₁}
    (x : QuantumComp₂ L (SSpecQ M) A B α) (g : α → QuantumComp₂ L (SSpecQ M) B B' β)
    {C D C' : Set Qrom.HashDomain} (hx : HP θ x C D) (hg : ∀ a, HP θ (g a) D C') :
    HP θ (x.bind g) C C' := by
  refine hp_bind θ x _ hx fun u p ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hg a

omit [Fintype M] [DecidableEq M] in
/-- Substituting trees that keep the invariant with nothing pending. -/
theorem hp_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor L spec)
      (QuantumComp.toIPFunctor L (SSpecQ M)))
    (hσ : ∀ A c, HP θ (σ A c) ∅ ∅) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor L spec) Ω A) : HP θ (x.substitute σ) ∅ ∅ := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind s c next ih =>
    rw [IFreeM.substitute_liftBind]
    exact hp_bind θ _ _ (hσ s c) fun u ans ↦ (hp_cast θ ans.2 _ _ _).mpr (ih ans.1)

omit [Fintype M] [DecidableEq M] in
/-- **Runtime 1's programs keep the invariant**: their adversary and read ports (the reads
lifted, keeping the label) leave nothing pending. -/
theorem hp_readLift {A : QReg} (y : QuantumComp L (hwReadSpec PairOut Qrom.HashDomain M) Ω A) :
    HP θ (readLift goodQ y) ∅ ∅ := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind _ c next ih =>
    show HP θ (IFreeM.mapLens (readLens goodQ) (IFreeM.liftBind c next)) ∅ ∅
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · refine ⟨trivial, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨rfl, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨⟨rfl, labKeep_liftRead c⟩, fun b ↦ ?_⟩
      dsimp only
      exact ih _

omit [Fintype M] [DecidableEq M] in
theorem hp_act {A B : QReg} {α : Type} (p : SubInstrument A B α) (C : Set Qrom.HashDomain) :
    HP θ (QComp.act (spec := SSpecQ M) p) C C :=
  ⟨trivial, fun _ ↦ subset_rfl⟩

omit [Fintype M] [DecidableEq M] in
/-- A reveal adds the cells whose source is in `T` to the pending set. -/
theorem hp_revealThen {B B' : QReg} {α : Type} (T : Finset TPos)
    (k : RevealVals TVal T × (Finset TPos × M) → QComp (SSpecQ M) B B' α)
    {C C' : Set Qrom.HashDomain} (hk : ∀ r, HP θ (k r) (C ∪ revealSet θ T) C') :
    HP θ (revealThen goodQ T k) C C' :=
  ⟨trivial, fun r ↦ hp₂_bind θ _ _ (hp_act θ _ _) fun _ ↦ hk r.down⟩

omit [Fintype M] [DecidableEq M] in
theorem hp_progThen {B B' : QReg} {α : Type} (p : LazyProg PairOut Qrom.HashDomain TPos TVal)
    (hp : goodQ p) (k : QComp (SSpecQ M) B B' α) {C C' : Set Qrom.HashDomain}
    (hk : HP θ k (C \ progCells (p.realize θ)) C') : HP θ (progThen p hp k) C C' :=
  ⟨trivial, fun _ ↦ hp₂_bind θ _ _ (hp_act θ _ _) fun _ ↦ hk⟩

omit [Fintype M] [DecidableEq M] in
theorem hp_progPos (B : QReg) (ps : List Pos) (hps : ∀ p ∈ ps, p.1.IsStruct)
    (C : Set Qrom.HashDomain) :
    HP θ (progPos M B ps) C (C \ {z | ∃ p ∈ ps, cellQ θ p = z}) := by
  induction ps generalizing C with
  | nil => exact fun z hz ↦ ⟨hz, fun ⟨_, hp, _⟩ ↦ absurd hp List.not_mem_nil⟩
  | cons p ps ih =>
    refine hp_progThen θ (progT p) trivial _ (hp_mono θ _ (ih (fun q hq ↦ hps q
      (List.mem_cons_of_mem _ hq)) _) subset_rfl ?_)
    rw [realize_progT (hps p List.mem_cons_self) (seedOf θ) θ]
    rintro z ⟨⟨hz, hne⟩, hn⟩
    refine ⟨hz, ?_⟩
    rintro ⟨q, hq, rfl⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hne rfl
    · exact hn ⟨q, hq, rfl⟩

omit [Fintype M] [DecidableEq M] in
/-- **A FORS opening keeps the invariant**: the cells with a revealed source are the opening's,
which it then programs. -/
theorem hp_forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    HP θ (forsOpenT M B idx lv) ∅ ∅ :=
  hp_revealThen θ _ _ fun _ ↦ hp₂_bind θ _ _ (hp_progPos θ B _
    (fun _ hp ↦ isStruct_of_mem_forsPos hp) _) fun _ ↦ by
    rintro z ⟨hz, hn⟩
    rcases hz with hz | hz
    · exact hz
    · exact hn (revealSet_forsReveal θ idx lv hz)

omit [Fintype M] [DecidableEq M] in
/-- **A layer publication keeps the invariant.** -/
theorem hp_publishT (B : QReg) (K : Key) (c : EncodingCounter) (x : Encoding) :
    HP θ (publishT M B K c x) ∅ ∅ :=
  hp_revealThen θ _ _ fun _ ↦ hp₂_bind θ _ _ (hp_progPos θ B _
    (fun _ hp ↦ isStruct_of_mem_layerPos hp) _) fun _ ↦ by
    rintro z ⟨hz, hn⟩
    rcases hz with hz | hz
    · exact hz
    · exact hn (revealSet_layerReveal θ K x hz)

variable (upd : TrialUpd M)

omit [Fintype M] [DecidableEq M] in
/-- **A counter search keeps the invariant**: the value the key signs is no source. -/
theorem hp_selectT (seed : PublicParameter) (B : QReg) (K : Key) :
    HP θ (selectT M upd seed B K) ∅ ∅ :=
  hp_revealThen θ _ _ fun _ ↦ hp_mono θ _ (hp_readLift θ _)
    (Set.union_subset (subset_refl _) (revealSet_msgPos θ K)) subset_rfl

omit [Fintype M] [DecidableEq M] in
theorem hp_publishAllT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (R : Randomizer) (g₀ g₁ g₂ : Option (EncodingCounter × Encoding)) :
    HP θ (publishAllT M B idx lv R g₀ g₁ g₂) ∅ ∅ := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try exact subset_rfl
  simp only [publishAllT]
  refine hp₂_bind θ _ _ (hp_forsOpenT θ B _ _) fun _ ↦ ?_
  refine hp₂_bind θ _ _ (hp_publishT θ B _ _ _) fun _ ↦ ?_
  refine hp₂_bind θ _ _ (hp_publishT θ B _ _ _) fun _ ↦ ?_
  exact hp₂_bind θ _ _ (hp_publishT θ B _ _ _) fun _ ↦ subset_rfl

omit [Fintype M] [DecidableEq M] in
/-- **A signature keeps the invariant**, for a digest policy revealing no value coordinate: the
reveal of `R(M)` makes the digest cell pending, which the digest port then programs. -/
theorem hp_signT {pol : DigestPolicy} (hpol : pol.NoVal) (B : QReg) (msg : Message) :
    HP θ (signT M upd pol B msg) ∅ ∅ := by
  unfold signT
  refine hp_revealThen θ _ _ fun r₁ ↦ hp_revealThen θ _ _ fun r₂ ↦ ?_
  refine hp_progThen θ _ trivial _ (hp_mono θ _ (C := ∅) ?_ ?_ subset_rfl)
  · refine hp₂_bind θ _ _ (hp_selectT θ upd _ B _) fun _ ↦ ?_
    refine hp₂_bind θ _ _ (hp_selectT θ upd _ B _) fun _ ↦ ?_
    exact hp₂_bind θ _ _ (hp_selectT θ upd _ B _) fun _ ↦ hp_publishAllT θ B _ _ _ _ _ _
  · rw [realize_digPort, ← cellOf_digPos]
    rintro z ⟨(hz | hz) | hz, hn⟩
    · exact hz
    · exact hn (revealSet_sigReveal θ msg hz)
    · exact revealSet_noVal θ hpol _ msg hz

omit [Fintype M] [DecidableEq M] in
/-- **The challenger keeps the invariant**, with nothing pending between commands. -/
theorem hp_challengeT {pol : DigestPolicy} (hpol : pol.NoVal) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    HP θ (challengeT M upd pol A c) ∅ ∅ := by
  rcases c with o | ⟨p | msg, E, ℓ⟩
  · exact hp_readLift θ _
  · exact hp_readLift θ _
  · exact hp_bind θ _ _ (hp₂_bind θ _ _ (hp_act θ _ _) fun _ ↦
      hp_signT θ upd hpol _ msg) fun _ _ ↦ subset_rfl

omit [Fintype M] [DecidableEq M] in
/-- **The game keeps the invariant**: the public key is no source, then the challenged
adversary and the verification. -/
theorem hp_gameT {pol : DigestPolicy} (hpol : pol.NoVal) (A : SAdversary) :
    HP θ (gameT M upd pol A) ∅ ∅ := by
  rw [gameT_eq_prefixT_bind]
  refine hp₂_bind θ _ _ (hp_revealThen θ _ _ fun _ ↦ hp_mono θ _
    (hp₂_bind θ _ _ (hp_substitute θ _ (hp_challengeT θ upd hpol) _) fun _ ↦ subset_rfl)
    (Set.union_subset (subset_refl _) (revealSet_pkReveal θ)) subset_rfl) fun x ↦ ?_
  rw [verifyT, readsThenT_eq]
  exact hp₂_bind θ _ _ (hp_readLift θ _) fun _ ↦ subset_rfl

end hp

/-! ## `hinv` -/

section hinv

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- One call of a realized program on the pending invariant. -/
theorem forallQueries_queryBind_of_stepInv {Q : (recHwSpec PairOut Qrom.HashDomain TPos M).Port →
    Prop} (m₀ : Finset TPos × M) (I : L.Interp) (θ : TVals) {A : QReg}
    (i : (recHwSpec PairOut Qrom.HashDomain TPos M).Port) (E : QReg)
    (ℓ : A ≃ (recHwSpec PairOut Qrom.HashDomain TPos M).In i × E)
    (k' : (recHwSpec PairOut Qrom.HashDomain TPos M).Result i →
      QuantumComp L (recHwSpec PairOut Qrom.HashDomain TPos M) Ω
        (QReg.of ((recHwSpec PairOut Qrom.HashDomain TPos M).Out i × E)))
    {C C' : Set Qrom.HashDomain} (hpre : Q i → C = ∅)
    (hstep : StepR m₀ i (fun s ↦ InvP θ C s) (fun s ↦ InvP θ C' s))
    (hk : ∀ r ρ', QuerySupportedOn
        (fun m : QReg.of ((recHwSpec PairOut Qrom.HashDomain TPos M).Out i × E) ×
          (runtimeR m₀).D ↦ m.2) {s | InvP θ C' s} ρ' →
      (runtimeR m₀).ForallQueries I (invSupp (runtimeR m₀) Q (SrcInv M θ)) (k' r) ρ')
    (ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ)
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | InvP θ C s} ρ) :
    (runtimeR m₀).ForallQueries I (invSupp (runtimeR m₀) Q (SrcInv M θ))
      (QuantumComp.queryBind i E ℓ k') ρ :=
  ⟨fun hq a ha ↦ relabel_diag_eq_zero_of_supp m₀ E ℓ (hpre hq ▸ hρ) a
    fun h ↦ ha (srcInv_of_invP h), fun r ↦
      hk r _ (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s) i r (hstep r) E ℓ hρ)⟩

/-- **The realized program of a template keeping the invariant presents, at every call of the
ports `Q` (no program or record port), only states of the invariant.** -/
theorem forallQueries_of_hp {Q : (recHwSpec PairOut Qrom.HashDomain TPos M).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (hQ' : ∀ T, ¬Q (.inr T)) (m₀ : Finset TPos × M)
    (I : L.Interp) (θ : TVals) {A : QReg} (y : QuantumComp L (SSpecQ M) Ω A) :
    ∀ C C', HP θ y C C' → ∀ ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | InvP θ C s} ρ →
      (runtimeR m₀).ForallQueries I (invSupp (runtimeR m₀) Q (SrcInv M θ))
        (realizeT θ y) ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _ _ _; trivial
  | primBind _ o k ih =>
    intro C C' hy ρ hρ b
    exact ih b C C' (hy.2 (ULift.up b)) _ (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _)
  | queryBind _ i E ℓ k ih =>
    intro C C' hy ρ hρ
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · exact forallQueries_queryBind_of_stepInv m₀ I θ (.inl (.inl (.inl i))) E ℓ
        (fun r ↦ realizeT θ (k r)) (fun _ ↦ hy.1)
        (stepR_sponge m₀ i fun _ _ he hr ↦ invP_of_eq (congrArg Prod.fst he)
          (congrArg (fun t ↦ t.2.1) he) hr)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepInv m₀ I θ (.inl (.inl (.inr c.1))) E ℓ
        (fun r ↦ realizeT θ (k r)) (fun _ ↦ hy.1.1)
        (stepR_readKeep m₀ c hy.1.2 fun _ _ h1 h2 hr ↦ invP_of_eq h1 h2 hr)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · cases p with
      | programH T₀ c =>
        exact forallQueries_queryBind_of_stepInv m₀ I θ
          (.inl (.inr ((LazyProg.programH T₀ c).realize θ))) E ℓ (fun r ↦ realizeT θ (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepR_prog m₀ _ fun _ _ h hr ↦ invP_prog _ h hr)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK T₀ c =>
        exact forallQueries_queryBind_of_stepInv m₀ I θ
          (.inl (.inr ((LazyProg.programK T₀ c).realize θ))) E ℓ (fun r ↦ realizeT θ (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepR_prog m₀ _ fun _ _ h hr ↦ invP_prog _ h hr)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK' T₀ c =>
        exact forallQueries_queryBind_of_stepInv m₀ I θ
          (.inl (.inr ((LazyProg.programK' T₀ c).realize θ))) E ℓ (fun r ↦ realizeT θ (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepR_prog m₀ _ fun _ _ h hr ↦ invP_prog _ h hr)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepInv m₀ I θ (.inr T) E ℓ
        (fun m ↦ realizeT θ (k (restrictTo T θ, m))) (fun hq ↦ absurd hq (hQ' _))
        (stepR_rec m₀ T fun _ _ h hr ↦ invP_reveal T h hr)
        (fun m ↦ ih (restrictTo T θ, m) _ C' (hy.2 (ULift.up (restrictTo T θ, m)))) ρ hρ

variable (upd : TrialUpd M)

/-- **`hinv` for the realized template game**, for every digest policy revealing no value
coordinate (`msgPol`, `strPol`): from states with an empty memory label, every call of ports `Q`
other than the program and record ports (the adversary's calls of `F`, the reads) sees the
invariant `SrcInv`: every position whose source is revealed has its cell hardwired. -/
theorem forallQueries_gameT {pol : DigestPolicy} (hpol : pol.NoVal)
    {Q : (recHwSpec PairOut Qrom.HashDomain TPos M).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (hQ' : ∀ T, ¬Q (.inr T)) (m₀ : Finset TPos × M)
    (A : SAdversary) (θ : TVals)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × M)))
      (QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × M))) ℂ)
    (hρ : QuerySupportedOn
      (fun a : QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × M)) ↦
        a.2.2.2.1) {∅} ρ) :
    (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m₀) Q (SrcInv M θ)) (realizeT θ (gameT M upd pol A)) ρ :=
  forallQueries_of_hp hQ hQ' m₀ _ θ _ ∅ ∅ (hp_gameT θ upd hpol A) ρ
    (hρ.imp fun _ ha ↦ invP_of_label_empty (Set.mem_singleton_iff.1 ha))

/-- **Masses' `hinv`** with `Inv θ := SrcInv M θ`. -/
theorem hinv_gameT {pol : DigestPolicy} (hpol : pol.NoVal)
    {Q : (recHwSpec PairOut Qrom.HashDomain TPos M).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (hQ' : ∀ T, ¬Q (.inr T)) (m₀ : Finset TPos × M)
    (A : SAdversary)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × M)))
      (QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × M))) ℂ)
    (hρ : QuerySupportedOn
      (fun a : QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × M)) ↦
        a.2.2.2.1) {∅} ρ) :
    ∀ θ, (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m₀) Q (SrcInv M θ)) (realizeT θ (gameT M upd pol A)) ρ :=
  fun θ ↦ forallQueries_gameT upd hpol hQ hQ' m₀ A θ ρ hρ

/-- **An initial state whose memory label is empty**: the basis state of runtime 2's start. -/
theorem querySupportedOn_init (m₀ : Finset TPos × M) (hm₀ : m₀.1 = ∅) {A : QReg}
    (σ : Matrix A A ℂ) :
    QuerySupportedOn
      (fun a : A × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × M)) ↦ a.2.2.2.1) {∅}
      (σ ⊗ₖ (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m₀).init.matrix) := by
  intro a b h
  change (σ ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
    hwEmpty PairOut Qrom.HashDomain, m₀) :
      HwReg PairOut Qrom.HashDomain (Finset TPos × M))).matrix) a b ≠ 0 at h
  rw [SubState.matrix_basis, kroneckerMap_apply] at h
  have h' := right_ne_zero_of_mul h
  rw [Matrix.single_apply] at h'
  split_ifs at h' with he
  · show a.2.2.2.1 ∈ ({∅} : Set (Finset TPos)) ∧ b.2.2.2.1 ∈ ({∅} : Set (Finset TPos))
    rw [← he.1, ← he.2]
    exact ⟨hm₀, hm₀⟩
  · exact absurd rfl h'

end hinv

/-! ## Support semantics in the decompressed basis

The QRPM's `PrefixRun` at `X := PairOut`, `Z := HashDomain`, as for leanXMSS
(`Quantum.Qrom.Xmss.GameTFacts`). -/

open Quantum.Xmss.Assembly (recStep_branch decR decR_branch_apply decR_step_noBot NoBot
  querySupportedOn_run querySupportedOn_queryStep_imp clsKraus_dec_ne_zero dbs_dec_ne_zero
  cellRead_dec_ne_zero one_dec_ne_zero compressAll_mul_cellDiscard_mul_compressAll_ne_zero
  snd_eq_of_hwPort dbs_one_dec_eq liftAns lowerRes lowerRes_liftAns realizeT_readLift_readCall
  realizeT_bind realizeT_bind₂ readLift_bind₂ realizeT_substitute querySupportedOn_inter initU
  noBot_init querySupportedOn_conj_compressReg or_isSome readLiftQ)
open Quantum.Xmss.Hybrid (runtime2_branch)

/-- The register of runtime 2 with record ports at the memory `Finset TPos × M`. -/
abbrev RRegS (M : Type) : Type :=
  HwReg PairOut Qrom.HashDomain (Finset TPos × M)

/-- The signature of runtime 2 with record ports at the memory `Finset TPos × M`. -/
abbrev RSpecS (M : Type) : QuantumOracleSpec.{0, 0} :=
  recHwSpec PairOut Qrom.HashDomain TPos M

section hoare

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset TPos × M)

/-- **Support semantics of a program in the decompressed basis**: from an operator supported on
registers in `P`, the branch at every leaf `p` is supported on `Q p`. -/
def HTS {Ω : QReg → Type} {A : QReg} (y : QuantumComp LocalSig.instruments.{0} (RSpecS M) Ω A)
    (P : Set (RRegS M)) (Q : (Σ u, Ω u) → Set (RRegS M)) : Prop :=
  ∀ ρ : Matrix (A × RRegS M) (A × RRegS M) ℂ,
    QuerySupportedOn (fun m : A × RRegS M ↦ m.2) P ρ →
    ∀ p, QuerySupportedOn (fun m : p.1 × RRegS M ↦ m.2) (Q p)
      (((decR (X := PairOut) (Z := Qrom.HashDomain) m₀).run .instruments y).branch p ρ)

/-- `HTS` for programs on a fixed final register. -/
def HTS₂ {A B : QReg} {α : Type} (y : QComp (RSpecS M) A B α) (P : Set (RRegS M))
    (Q : α → Set (RRegS M)) : Prop :=
  ∀ ρ : Matrix (A × RRegS M) (A × RRegS M) ℂ,
    QuerySupportedOn (fun m : A × RRegS M ↦ m.2) P ρ →
    ∀ a, QuerySupportedOn (fun m : B × RRegS M ↦ m.2) (Q a)
      (((decR (X := PairOut) (Z := Qrom.HashDomain) m₀).run₂ .instruments y).branch a ρ)

variable {m₀}

theorem HTS.mono {Ω : QReg → Type} {A : QReg}
    {y : QuantumComp LocalSig.instruments.{0} (RSpecS M) Ω A}
    {P P' : Set (RRegS M)} {Q Q' : (Σ u, Ω u) → Set (RRegS M)} (h : HTS m₀ y P Q)
    (hP : P' ⊆ P) (hQ : ∀ p, Q p ⊆ Q' p) : HTS m₀ y P' Q' :=
  fun ρ hρ p ↦ (h ρ (hρ.mono hP) p).mono (hQ p)

theorem HTS₂.mono {A B : QReg} {α : Type} {y : QComp (RSpecS M) A B α}
    {P P' : Set (RRegS M)} {Q Q' : α → Set (RRegS M)} (h : HTS₂ m₀ y P Q) (hP : P' ⊆ P)
    (hQ : ∀ a, Q a ⊆ Q' a) : HTS₂ m₀ y P' Q' :=
  fun ρ hρ a ↦ (h ρ (hρ.mono hP) a).mono (hQ a)

theorem htS₂_iff {A B : QReg} {α : Type} (y : QComp (RSpecS M) A B α) (P : Set (RRegS M))
    (Q : α → Set (RRegS M)) : HTS₂ m₀ y P Q ↔ HTS m₀ y P fun p ↦ Q p.2.2 := by
  constructor
  · intro h ρ hρ p
    obtain ⟨u, hu, a⟩ := p
    subst hu
    exact h ρ hρ a
  · intro h ρ hρ a
    exact h ρ hρ ⟨B, rfl, a⟩

theorem htS_of_htS₂ {A B : QReg} {α : Type} {y : QComp (RSpecS M) A B α}
    {P : Set (RRegS M)} {Q : α → Set (RRegS M)} (h : HTS₂ m₀ y P Q) :
    HTS m₀ y P fun p ↦ Q p.2.2 :=
  (htS₂_iff y P Q).mp h

theorem htS₂_of_htS {A B : QReg} {α : Type} {y : QComp (RSpecS M) A B α}
    {P : Set (RRegS M)} {Q : α → Set (RRegS M)} (h : HTS m₀ y P fun p ↦ Q p.2.2) :
    HTS₂ m₀ y P Q :=
  (htS₂_iff y P Q).mpr h

theorem htS_pure {Ω : QReg → Type} {A : QReg} (y : Ω A) {P : Set (RRegS M)}
    {Q : (Σ u, Ω u) → Set (RRegS M)} (h : P ⊆ Q ⟨A, y⟩) :
    HTS m₀ (QuantumComp.pure (L := LocalSig.instruments.{0}) (spec := RSpecS M) y) P Q := by
  classical
  intro ρ hρ p
  rw [QuantumRuntime.run_pure]
  by_cases hp : p = ⟨A, y⟩
  · subst hp
    rw [DSubInstrument.branch_ret_self]
    exact hρ.mono h
  · rw [DSubInstrument.branch_ret_of_ne _ hp]
    exact querySupportedOn_zero _ _

theorem htS₂_pure {A : QReg} {α : Type} (a : α) {P : Set (RRegS M)} {Q : α → Set (RRegS M)}
    (h : P ⊆ Q a) : HTS₂ m₀ (QuantumComp₂.pure a : QComp (RSpecS M) A A α) P Q := by
  intro ρ hρ a'
  rw [QuantumRuntime.run₂_pure]
  by_cases ha : a' = a
  · subst ha
    rw [SubInstrument.branch_pure_self]
    exact hρ.mono h
  · rw [SubInstrument.branch_pure_of_ne ha]
    exact querySupportedOn_zero _ _

theorem HTS.bind {Ω Ω' : QReg → Type} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (RSpecS M) Ω A}
    {P : Set (RRegS M)} {Q : (Σ u, Ω u) → Set (RRegS M)} (hx : HTS m₀ x P Q)
    {k : ∀ u, Ω u → QuantumComp LocalSig.instruments.{0} (RSpecS M) Ω' u}
    {R : (Σ u, Ω' u) → Set (RRegS M)} (hk : ∀ u a, HTS m₀ (k u a) (Q ⟨u, a⟩) R) :
    HTS m₀ (x.bind k) P R := by
  intro ρ hρ p
  rw [QuantumRuntime.run_bind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun q ↦ hk q.1 q.2 _ (hx ρ hρ q) p

theorem HTS₂.bind {A B C : QReg} {α β : Type} {x : QComp (RSpecS M) A B α}
    {P : Set (RRegS M)} {Q : α → Set (RRegS M)} (hx : HTS₂ m₀ x P Q)
    {k : α → QComp (RSpecS M) B C β} {R : β → Set (RRegS M)}
    (hk : ∀ a, HTS₂ m₀ (k a) (Q a) R) : HTS₂ m₀ (x.bind k) P R := by
  intro ρ hρ b
  erw [QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun a ↦ hk a _ (hx ρ hρ a) b

theorem htS_primBind {Ω : QReg → Type} {A : QReg} (o : LocalSig.instruments.{0}.Op A)
    {k : (b : LocalSig.instruments.{0}.Outcome o) →
      QuantumComp LocalSig.instruments.{0} (RSpecS M) Ω (LocalSig.instruments.{0}.next o b)}
    {P : Set (RRegS M)} {Q : (Σ u, Ω u) → Set (RRegS M)} (hk : ∀ b, HTS m₀ (k b) P Q) :
    HTS m₀ (QuantumComp.primBind o k) P Q := by
  intro ρ hρ p
  rw [QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun b ↦ hk b _ (QuerySupportedOn.amplify_snd (q := id) hρ _) p

/-- **A local operation keeps the register.** -/
theorem htS₂_act_bind {A B C : QReg} {α β : Type} (p : SubInstrument A B β)
    {k : β → QComp (RSpecS M) B C α} {P : Set (RRegS M)} {Q : α → Set (RRegS M)}
    (hk : ∀ b, HTS₂ m₀ (k b) P Q) : HTS₂ m₀ ((QComp.act p).bind k) P Q := by
  intro ρ hρ a
  rw [QuantumRuntime.run₂_act_bind]
  erw [DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun b ↦ hk b _ (QuerySupportedOn.amplify_snd (q := id) hρ _) a

theorem htS₂_act {A B : QReg} {β : Type} (p : SubInstrument A B β) (P : Set (RRegS M)) :
    HTS₂ m₀ (QComp.act (spec := RSpecS M) p) P fun _ ↦ P := by
  rw [← QuantumComp₂.bind_pure (QComp.act (spec := RSpecS M) p)]
  exact htS₂_act_bind p fun b ↦ htS₂_pure b subset_rfl

/-- A call whose step moves the support from `P` to `P' r` at the result `r`. -/
theorem htS_queryBind {Ω : QReg → Type} {A : QReg} (i : (RSpecS M).Port)
    (E : QReg) (ℓ : A ≃ (RSpecS M).In i × E)
    {k : (RSpecS M).Result i →
      QuantumComp LocalSig.instruments.{0} (RSpecS M) Ω (QReg.of ((RSpecS M).Out i × E))}
    {P : Set (RRegS M)} (P' : (RSpecS M).Result i → Set (RRegS M))
    {Q : (Σ u, Ω u) → Set (RRegS M)}
    (hstep : ∀ r (σ : Matrix ((RSpecS M).In i × RRegS M) ((RSpecS M).In i × RRegS M) ℂ),
      QuerySupportedOn (fun m : (RSpecS M).In i × RRegS M ↦ m.2) P σ →
        QuerySupportedOn (fun m : (RSpecS M).Out i × RRegS M ↦ m.2) (P' r)
          (((decR (X := PairOut) (Z := Qrom.HashDomain) m₀).step i).branch r σ))
    (hk : ∀ r, HTS m₀ (k r) (P' r) Q) : HTS m₀ (QuantumComp.queryBind i E ℓ k) P Q := by
  intro ρ hρ p
  rw [QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun r ↦ hk r _
    (querySupportedOn_queryStep_imp (decR (X := PairOut) (Z := Qrom.HashDomain) m₀) i E ℓ r P
      (P' r) (hstep r) hρ) p

theorem htS₂_queryBind {A B : QReg} {α : Type} (i : (RSpecS M).Port)
    (E : QReg) (ℓ : A ≃ (RSpecS M).In i × E)
    {k : (RSpecS M).Result i → QComp (RSpecS M) (QReg.of ((RSpecS M).Out i × E)) B α}
    {P : Set (RRegS M)} (P' : (RSpecS M).Result i → Set (RRegS M)) {Q : α → Set (RRegS M)}
    (hstep : ∀ r (σ : Matrix ((RSpecS M).In i × RRegS M) ((RSpecS M).In i × RRegS M) ℂ),
      QuerySupportedOn (fun m : (RSpecS M).In i × RRegS M ↦ m.2) P σ →
        QuerySupportedOn (fun m : (RSpecS M).Out i × RRegS M ↦ m.2) (P' r)
          (((decR (X := PairOut) (Z := Qrom.HashDomain) m₀).step i).branch r σ))
    (hk : ∀ r, HTS₂ m₀ (k r) (P' r) Q) :
    HTS₂ m₀ (QuantumComp₂.queryBind (L := LocalSig.instruments) i E ℓ k) P Q := by
  intro ρ hρ a
  erw [QuantumRuntime.run₂_queryBind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun r ↦ hk r _
    (querySupportedOn_queryStep_imp (decR (X := PairOut) (Z := Qrom.HashDomain) m₀) i E ℓ r P
      (P' r) (hstep r) hρ) a

variable (m₀) in
/-- **Every run keeps `NoBot`.** -/
theorem htS_noBot {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (RSpecS M) Ω A) :
    HTS m₀ y {s | NoBot s} fun _ ↦ {s | NoBot s} :=
  fun _ hρ p ↦ querySupportedOn_run (decR (X := PairOut) (Z := Qrom.HashDomain) m₀)
    {s | NoBot s} (decR_step_noBot m₀) .instruments y hρ p

theorem HTS₂.and_noBot {A B : QReg} {α : Type} {y : QComp (RSpecS M) A B α}
    {P : Set (RRegS M)} {Q : α → Set (RRegS M)} (h : HTS₂ m₀ y P Q)
    (hP : ∀ s ∈ P, NoBot s) : HTS₂ m₀ y P fun a ↦ Q a ∩ {s | NoBot s} :=
  fun ρ hρ a ↦ querySupportedOn_inter (h ρ hρ a)
    (htS₂_of_htS (Q := fun _ ↦ {s | NoBot s}) (htS_noBot m₀ y) ρ (hρ.mono hP) a)

end hoare

section ports

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset TPos × M)

/-- **A sponge port keeps the decompressed register.** -/
theorem decR_sponge_suppS (i : SpongePort) (r : (RSpecS M).Result (.inl (.inl (.inl i))))
    (P : Set (RRegS M))
    (σ : Matrix ((RSpecS M).In (.inl (.inl (.inl i))) × RRegS M)
      ((RSpecS M).In (.inl (.inl (.inl i))) × RRegS M) ℂ)
    (hσ : QuerySupportedOn (fun m : (RSpecS M).In (.inl (.inl (.inl i))) × RRegS M ↦ m.2) P σ) :
    QuerySupportedOn (fun m : (RSpecS M).Out (.inl (.inl (.inl i))) × RRegS M ↦ m.2) P
      (((decR (X := PairOut) (Z := Qrom.HashDomain) m₀).step (.inl (.inl (.inl i)))).branch r
        σ) := by
  rw [decR_branch_apply m₀ _ r _ (runtime2_branch m₀ (.inl (.inl i)) r)]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
  cases i <;> (rw [snd_eq_of_hwPort _ m' m hK]; exact hm)

omit [Fintype M] [DecidableEq M] in
/-- The registers after recording `T` from `P` with memory `mem` before. -/
def RecSetS (P : Set (RRegS M)) (T : Finset TPos) (mem : Finset TPos × M) : Set (RRegS M) :=
  {s | ∃ s₀ ∈ P, s₀.2.2 = mem ∧ s = (s₀.1, s₀.2.1, (s₀.2.2.1 ∪ T, s₀.2.2.2))}

/-- **A record of `T` adds `T` to the label** and keeps everything else. -/
theorem decR_rec_suppS (T : Finset TPos) (mem : (RSpecS M).Result (.inr T)) (P : Set (RRegS M))
    (σ : Matrix ((RSpecS M).In (.inr T) × RRegS M) ((RSpecS M).In (.inr T) × RRegS M) ℂ)
    (hσ : QuerySupportedOn (fun m : (RSpecS M).In (.inr T) × RRegS M ↦ m.2) P σ) :
    QuerySupportedOn (fun m : (RSpecS M).Out (.inr T) × RRegS M ↦ m.2) (RecSetS P T mem)
      (((decR (X := PairOut) (Z := Qrom.HashDomain) m₀).step (.inr T)).branch mem σ) := by
  obtain ⟨lab, mm⟩ := mem
  rw [decR_branch_apply m₀ (.inr T) (lab, mm) _ (recStep_branch T (lab, mm))]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
  obtain ⟨hp, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
  exact ⟨m.2, hm, hp, Prod.ext (dbs_one_dec_eq hR) hφ⟩

omit [Fintype M] [DecidableEq M] in
/-- **The effect of hardwiring the `h`-cell `z` to `a`** on the decompressed register: the
hardwired cells updated, no empty cell kept, every other `h` database cell kept. -/
def ProgRelS (z : Qrom.HashDomain) (a : PairOut) (s s' : RRegS M) : Prop :=
  s'.2 = (progUpdate (.programH z a) s.2.1, s.2.2) ∧ (NoBot s → NoBot s') ∧
    ∀ z', z' ≠ z → s'.1.1 z' = s.1.1 z'

/-- **A program call of an `h`-cell in the decompressed basis** (`ProgRelS`). -/
theorem decR_progH_suppS (z : Qrom.HashDomain) (a : PairOut)
    (r : (RSpecS M).Result (.inl (.inr (.programH z a)))) (P : Set (RRegS M))
    (σ : Matrix ((RSpecS M).In (.inl (.inr (.programH z a))) × RRegS M)
      ((RSpecS M).In (.inl (.inr (.programH z a))) × RRegS M) ℂ)
    (hσ : QuerySupportedOn
      (fun m : (RSpecS M).In (.inl (.inr (.programH z a))) × RRegS M ↦ m.2) P σ) :
    QuerySupportedOn (fun m : (RSpecS M).Out (.inl (.inr (.programH z a))) × RRegS M ↦ m.2)
      {s' | ∃ s ∈ P, ProgRelS z a s s'}
      (((decR (X := PairOut) (Z := Qrom.HashDomain) m₀).step
        (.inl (.inr (.programH z a)))).branch r σ) := by
  rw [decR_branch_apply m₀ _ r _ (runtime2_branch m₀ (.inr (.programH z a)) r)]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ⟨m.2, hm, ?_⟩
  obtain ⟨-, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
  rw [show (cellDiscard z r.1 ⊗ₖ (1 : Matrix (Database PairOut Qrom.HashDomain ×
    Database PairOut Qrom.HashDomain) (Database PairOut Qrom.HashDomain ×
      Database PairOut Qrom.HashDomain) ℂ)) = cellDiscard z r.1 ⊗ₖ
      ((1 : Matrix (Database PairOut Qrom.HashDomain) (Database PairOut Qrom.HashDomain) ℂ) ⊗ₖ
        1) by rw [one_kronecker_one]] at hR
  obtain ⟨h₁, h₂, h₃⟩ := dbs_dec_ne_zero hR
  obtain ⟨hc, hs⟩ := compressAll_mul_cellDiscard_mul_compressAll_ne_zero h₁
  have e₂ := one_dec_ne_zero h₂
  have e₃ := one_dec_ne_zero h₃
  refine ⟨hφ, fun hnb ↦ ⟨fun z' ↦ ?_, by rw [e₂]; exact hnb.2.1, by rw [e₃]; exact hnb.2.2⟩,
    fun z' hz' ↦ hc z' hz'⟩
  by_cases hz : z' = z
  · subst hz
    exact hs
  · rw [hc z' hz]
    exact hnb.1 z'

omit [Fintype M] [DecidableEq M] in
/-- The register after a read of the `h`-cell `z` updating the inner memory with `upd`. -/
def readFinS (s : RRegS M) (z : Qrom.HashDomain) (upd : M → Option PairOut → M) : RRegS M :=
  (s.1, s.2.1, (s.2.2.1, upd s.2.2.2 ((hwView s.2.1 s.1).1 z)))

/-- **A read of an `h`-cell in the decompressed basis**: it returns the view's cell with the
memory before, keeps the databases and hardwired cells, and updates the memory. -/
theorem decR_readH_suppS (z : Qrom.HashDomain) (upd : M → Option PairOut → M)
    (r : (RSpecS M).Result (.inl (.inl (.inr (liftRead (.readH z upd)))))) (U : Set (RRegS M))
    (σ : Matrix ((RSpecS M).In (.inl (.inl (.inr (liftRead (.readH z upd))))) × RRegS M)
      ((RSpecS M).In (.inl (.inl (.inr (liftRead (.readH z upd))))) × RRegS M) ℂ)
    (hσ : QuerySupportedOn
      (fun p : (RSpecS M).In (.inl (.inl (.inr (liftRead (.readH z upd))))) × RRegS M ↦ p.2)
        U σ) :
    QuerySupportedOn
      (fun p : (RSpecS M).Out (.inl (.inl (.inr (liftRead (.readH z upd))))) × RRegS M ↦ p.2)
      {s' | ∃ s ∈ U, r = liftAns s (.readH z upd) ∧ s' = readFinS s z upd}
      (((decR (X := PairOut) (Z := Qrom.HashDomain) m₀).step
        (.inl (.inl (.inr (liftRead (.readH z upd)))))).branch r σ) := by
  rw [decR_branch_apply m₀ (.inl (.inl (.inr (liftRead (.readH z upd))))) r _
    (runtime2_branch m₀ (.inl (.inr (liftRead (.readH z upd)))) r)]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ⟨m.2, hm, ?_⟩
  obtain ⟨o, mm⟩ := r
  obtain ⟨hp, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
  rw [show (cellRead m.2.2.1.1 z o ⊗ₖ (1 : Matrix (Database PairOut Qrom.HashDomain ×
    Database PairOut Qrom.HashDomain) (Database PairOut Qrom.HashDomain ×
      Database PairOut Qrom.HashDomain) ℂ)) = cellRead m.2.2.1.1 z o ⊗ₖ
      ((1 : Matrix (Database PairOut Qrom.HashDomain) (Database PairOut Qrom.HashDomain) ℂ) ⊗ₖ
        1) by rw [one_kronecker_one]] at hR
  obtain ⟨h₁, h₂, h₃⟩ := dbs_dec_ne_zero hR
  obtain ⟨e₁, hr⟩ := cellRead_dec_ne_zero h₁
  have hD : m'.2.1 = m.2.1 := Prod.ext e₁ (Prod.ext (one_dec_ne_zero h₂) (one_dec_ne_zero h₃))
  subst hp hr
  exact ⟨rfl, Prod.ext hD hφ⟩

end ports

section template

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset TPos × M) (θ : TVals)

theorem htS_realizeT_bind {Ω Ω' : QReg → Type} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (SSpecQ M) Ω A}
    {g : ∀ u, Ω u → QuantumComp LocalSig.instruments.{0} (SSpecQ M) Ω' u}
    {P : Set (RRegS M)} {Q : (Σ u, Ω u) → Set (RRegS M)} {R : (Σ u, Ω' u) → Set (RRegS M)}
    (hx : HTS m₀ (realizeT θ x) P Q) (hg : ∀ u a, HTS m₀ (realizeT θ (g u a)) (Q ⟨u, a⟩) R) :
    HTS m₀ (realizeT θ (x.bind g)) P R := by
  rw [realizeT_bind]
  exact HTS.bind hx hg

theorem htS₂_realizeT_bind {A B C : QReg} {α β : Type} {x : QComp (SSpecQ M) A B α}
    {k : α → QComp (SSpecQ M) B C β} {P : Set (RRegS M)} {Q : α → Set (RRegS M)}
    {R : β → Set (RRegS M)} (hx : HTS₂ m₀ (realizeT θ x) P Q)
    (hk : ∀ a, HTS₂ m₀ (realizeT θ (k a)) (Q a) R) : HTS₂ m₀ (realizeT θ (x.bind k)) P R := by
  rw [realizeT_bind₂]
  exact HTS₂.bind hx hk

/-- **A realized reveal is the record port**: the values of `θ` on `T`, the label grown by `T`. -/
theorem htS₂_revealThen {B C : QReg} {α : Type} (T : Finset TPos)
    (k : RevealVals TVal T × (Finset TPos × M) → QComp (SSpecQ M) B C α)
    (P : Set (RRegS M)) (Q : α → Set (RRegS M))
    (hk : ∀ mem, HTS₂ m₀ (realizeT θ (k (restrictTo T θ, mem)))
      {s | ∃ s₀ ∈ P, s₀.2.2 = mem ∧ s = (s₀.1, s₀.2.1, (s₀.2.2.1 ∪ T, s₀.2.2.2))} Q) :
    HTS₂ m₀ (realizeT θ (revealThen goodQ T k)) P Q := by
  have e : realizeT θ (revealThen goodQ T k) =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := RSpecS M) (.inr T) B
        (Equiv.uniqueProd B Unit).symm fun mem ↦
          (QComp.act (A := QReg.of ((RSpecS M).Out (.inr T) × B)) (B := B)
            (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
              realizeT θ (k (restrictTo T θ, mem)) :=
    rfl
  rw [e]
  exact htS₂_queryBind (.inr T) B _ (RecSetS P T) (fun mem σ hσ ↦ decR_rec_suppS m₀ T mem P σ hσ)
    fun mem ↦ htS₂_act_bind _ fun _ ↦ hk mem

/-- **A realized program port hardwiring `z` with `a`** moves the register by `ProgRelS`. -/
theorem htS₂_progThen {B C : QReg} {α : Type} (p : LazyProg PairOut Qrom.HashDomain TPos TVal)
    {z : Qrom.HashDomain} {a : PairOut} (hr : p.realize θ = .programH z a)
    (k : QComp (SSpecQ M) B C α) (P : Set (RRegS M)) (Q : α → Set (RRegS M))
    (hk : HTS₂ m₀ (realizeT θ k) {s' | ∃ s ∈ P, ProgRelS z a s s'} Q) :
    HTS₂ m₀ (realizeT θ (progThen p trivial k)) P Q := by
  have e : realizeT θ (progThen p trivial k) =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := RSpecS M)
        (.inl (.inr (p.realize θ))) B (Equiv.uniqueProd B Unit).symm fun _ ↦
          (QComp.act (A := QReg.of ((RSpecS M).Out (.inl (.inr (p.realize θ))) × B))
            (B := B) (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
              realizeT θ k :=
    rfl
  rw [e]
  revert hk
  generalize p.realize θ = c at hr ⊢
  subst hr
  intro hk
  exact htS₂_queryBind _ B _ (fun _ ↦ {s' | ∃ s ∈ P, ProgRelS _ _ s s'})
    (fun r σ hσ ↦ decR_progH_suppS m₀ _ _ r P σ hσ) fun _ ↦ htS₂_act_bind _ fun _ ↦ hk

/-- **Sponge-only steps keep every register set**. -/
theorem htS_sponge {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (spongeSpec PairOut Qrom.HashDomain) Ω A)
    (P : Set (RRegS M)) :
    HTS m₀ (realizeT θ (readLift goodQ (y.liftOrdinary
      (t := hwReadCmdSpec PairOut Qrom.HashDomain M)))) P fun _ ↦ P := by
  induction y using QuantumComp.inductionOn with
  | pure A y => exact htS_pure y subset_rfl
  | primBind A o k ih =>
    have e : realizeT θ (readLift goodQ ((QuantumComp.primBind o k).liftOrdinary
        (t := hwReadCmdSpec PairOut Qrom.HashDomain M))) =
        QuantumComp.primBind o fun b ↦
          realizeT θ (readLift goodQ ((k b).liftOrdinary
            (t := hwReadCmdSpec PairOut Qrom.HashDomain M))) :=
      rfl
    rw [e]
    exact htS_primBind o fun b ↦ ih b
  | queryBind A i E ℓ k ih =>
    have e : realizeT θ (readLift goodQ ((QuantumComp.queryBind i E ℓ k).liftOrdinary
        (t := hwReadCmdSpec PairOut Qrom.HashDomain M))) =
        QuantumComp.queryBind (spec := RSpecS M) (.inl (.inl (.inl i))) E ℓ
          fun r ↦ realizeT θ (readLift goodQ ((k r).liftOrdinary
            (t := hwReadCmdSpec PairOut Qrom.HashDomain M))) :=
      rfl
    rw [e]
    exact htS_queryBind _ E ℓ (fun _ ↦ P) (fun r σ hσ ↦ decR_sponge_suppS m₀ i r P σ hσ)
      fun r ↦ ih r

end template

section det

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset TPos × M) (θ : TVals)

/-- **A read program answers as a function of the register**: from registers without empty cell,
run lifted, realized and in the decompressed basis, it returns `out s` and leaves `fin s`. -/
def DetS {B : QReg} {α : Type} (y : QComp (hwReadSpec PairOut Qrom.HashDomain M) B B α)
    (out : RRegS M → α) (fin : RRegS M → RRegS M) : Prop :=
  ∀ P : Set (RRegS M), (∀ s ∈ P, NoBot s) →
    HTS₂ m₀ (realizeT θ (readLiftQ goodQ y)) P fun a ↦ {s' | ∃ s ∈ P, a = out s ∧ s' = fin s}

variable {m₀ θ}

theorem DetS.congr {B : QReg} {α : Type} {y : QComp (hwReadSpec PairOut Qrom.HashDomain M) B B α}
    {out out' : RRegS M → α} {fin fin' : RRegS M → RRegS M} (h : DetS m₀ θ y out fin)
    (e : ∀ s, NoBot s → out s = out' s ∧ fin s = fin' s) : DetS m₀ θ y out' fin' := by
  intro P hP
  refine (h P hP).mono subset_rfl fun a ↦ ?_
  rintro s' ⟨s, hs, ha, rfl⟩
  obtain ⟨e₁, e₂⟩ := e s (hP s hs)
  exact ⟨s, hs, ha.trans e₁, e₂⟩

theorem detS_pure {B : QReg} {α : Type} (a : α) :
    DetS m₀ θ (QuantumComp₂.pure a : QComp (hwReadSpec PairOut Qrom.HashDomain M) B B α)
      (fun _ ↦ a) fun s ↦ s :=
  fun _ _ ↦ htS₂_pure a fun s hs ↦ ⟨s, hs, rfl, rfl⟩

theorem DetS.bind {B : QReg} {α β : Type}
    {x : QComp (hwReadSpec PairOut Qrom.HashDomain M) B B α}
    {out : RRegS M → α} {fin : RRegS M → RRegS M} (hx : DetS m₀ θ x out fin)
    {k : α → QComp (hwReadSpec PairOut Qrom.HashDomain M) B B β} {out' : α → RRegS M → β}
    {fin' : α → RRegS M → RRegS M} (hk : ∀ a, DetS m₀ θ (k a) (out' a) (fin' a)) :
    DetS m₀ θ (x.bind k) (fun s ↦ out' (out s) (fin s)) fun s ↦ fin' (out s) (fin s) := by
  intro P hP
  rw [readLift_bind₂, realizeT_bind₂]
  refine HTS₂.bind ((hx P hP).and_noBot hP) fun a ↦
    ((hk a) _ fun s hs ↦ hs.2).mono subset_rfl fun b ↦ ?_
  rintro s'' ⟨s', ⟨⟨s, hs, rfl, rfl⟩, -⟩, rfl, rfl⟩
  exact ⟨s, hs, rfl, rfl⟩

/-- **A read of an `h`-cell answers the view's cell with the memory and updates the memory.** -/
theorem detS_readH (z : Qrom.HashDomain) (upd : M → Option PairOut → M) (B : QReg) :
    DetS m₀ θ (readCall (.readH z upd) B) (fun s ↦ ((hwView s.2.1 s.1).1 z, s.2.2.2))
      fun s ↦ readFinS s z upd := by
  intro P _ ρ hρ a
  rw [realizeT_readLift_readCall]
  erw [QuantumRuntime.run₂_queryBind, DSubInstrument.branch_bind_apply]
  refine QuerySupportedOn.tsum fun r ↦ ?_
  have hq := querySupportedOn_queryStep_imp (decR (X := PairOut) (Z := Qrom.HashDomain) m₀)
    (.inl (.inl (.inr (liftRead (.readH z upd))))) B
    (Equiv.uniqueProd B Unit).symm r P
    {s' | ∃ s ∈ P, r = liftAns s (.readH z upd) ∧ s' = readFinS s z upd}
    (fun τ hτ ↦ decR_readH_suppS m₀ z upd r P τ hτ) hρ
  rw [QuantumRuntime.run₂_act_bind]
  erw [DSubInstrument.branch_bind_apply]
  refine QuerySupportedOn.tsum fun u ↦ ?_
  rw [QuantumRuntime.run₂_pure]
  by_cases ha : a = lowerRes (.readH z upd) r
  · subst ha
    rw [SubInstrument.branch_pure_self, LinearMap.id_apply, DSubInstrument.branch_frame_apply]
    refine (QuerySupportedOn.amplify_snd (q := fun s : RRegS M ↦ s) hq _).mono ?_
    rintro s' ⟨s, hs, hr, rfl⟩
    exact ⟨s, hs, by rw [hr, lowerRes_liftAns]; rfl, rfl⟩
  · rw [SubInstrument.branch_pure_of_ne ha]
    exact querySupportedOn_zero _ _

end det

/-! ## The counter search as a function of the view -/

section grind

/-- **The pair of the register's view**: the hardwired pair of a cell, else its database pair
(`0` on an empty cell, which the decompressed registers do not have). -/
def hvwS {M : Type} (s : RRegS M) (z : Qrom.HashDomain) : PairOut :=
  ((hwView s.2.1 s.1).1 z).getD 0

/-- The hash of the register's view: the first component of the pair. -/
def hHS {M : Type} (s : RRegS M) (z : Qrom.HashDomain) : HashOutput :=
  (hvwS s z).1

theorem hwView_eq_some_hvwS {M : Type} {s : RRegS M} (hs : NoBot s) (z : Qrom.HashDomain) :
    (hwView s.2.1 s.1).1 z = some (hvwS s z) := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (or_isSome (s.2.1.1 z) (hs.1 z))
  show (s.2.1.1 z).or (s.1.1 z) = some (((s.2.1.1 z).or (s.1.1 z)).getD 0)
  rw [ha]
  rfl

/-- **The memory after a counter search** of `K` against the view pairs `P`: each trial's read
updates the memory with `cwUpd`, until a codeword. -/
def grindMemS (P : Qrom.HashDomain → PairOut) (seed : PublicParameter) (K : Key) (m : Digest) :
    ℕ → ℕ → SelMem → SelMem
  | 0, _, mem => mem
  | n + 1, c, mem =>
    match TargetSum.decodeDigest (truncateHash (P (trialCell seed K m c)).1) with
    | some _ => cwUpd K (trialCell seed K m c) mem (some (P (trialCell seed K m c)))
    | none => grindMemS P seed K m n (c + 1)
        (cwUpd K (trialCell seed K m c) mem (some (P (trialCell seed K m c))))

variable {m₀ : Finset TPos × SelMem} {θ : TVals}

/-- **The counter search answers the view's selection** and updates the memory by `grindMemS`. -/
theorem det_grindS (v : QTable) (B : QReg) (K : Key) (m : Digest) (n c : ℕ) :
    DetS m₀ θ (grindT SelMem cwUpd v.publicSeed B K m n c)
      (fun s ↦ v.selectFrom (hHS s) K.1 K.2.1 K.2.2 m n c)
      (fun s ↦ (s.1, s.2.1, (s.2.2.1, grindMemS (hvwS s) v.publicSeed K m n c s.2.2.2))) := by
  induction n generalizing c with
  | zero => exact (detS_pure none).congr fun s _ ↦ ⟨rfl, rfl⟩
  | succ n ih =>
    rw [grindT]
    refine DetS.congr (DetS.bind (detS_readH _ _ B)
      (out' := fun r s ↦ (TargetSum.decodeDigest (truncateHash (r.1.getD 0).1)).elim
        (v.selectFrom (hHS s) K.1 K.2.1 K.2.2 m n (c + 1))
        fun x ↦ some (BitVec.ofNat counterBits c, x))
      (fin' := fun r s ↦ (TargetSum.decodeDigest (truncateHash (r.1.getD 0).1)).elim
        (s.1, s.2.1, (s.2.2.1, grindMemS (hvwS s) v.publicSeed K m n (c + 1) s.2.2.2))
        fun _ ↦ s) fun r ↦ ?_) fun s hs ↦ ⟨?_, ?_⟩
    · rcases TargetSum.decodeDigest (truncateHash (r.1.getD 0).1) with _ | x
      · exact ih (c + 1)
      · exact detS_pure _
    · have e : v.encDigest (hHS s) K.1 K.2.1 K.2.2 m (BitVec.ofNat counterBits c) =
          truncateHash (hvwS s (trialCell v.publicSeed K m c)).1 :=
        rfl
      simp only [readFinS, hwView_eq_some_hvwS hs, Option.getD_some]
      rw [QTable.selectFrom, e]
      rcases TargetSum.decodeDigest (truncateHash (hvwS s (trialCell v.publicSeed K m c)).1)
        with _ | x <;> rfl
    · simp only [readFinS, hwView_eq_some_hvwS hs, Option.getD_some]
      rw [grindMemS]
      rcases TargetSum.decodeDigest (truncateHash (hvwS s (trialCell v.publicSeed K m c)).1)
        with _ | x <;> rfl

variable (P : Qrom.HashDomain → PairOut) (seed : PublicParameter) (K : Key) (m : Digest)

/-- The search changes only its key's memory. -/
theorem grindMemS_of_ne {K' : Key} (h : K' ≠ K) :
    ∀ n c mem, grindMemS P seed K m n c mem K' = mem K'
  | 0, _, _ => rfl
  | n + 1, c, mem => by
    have hc : ∀ mem' : SelMem, cwUpd K (trialCell seed K m c) mem'
        (some (P (trialCell seed K m c))) K' = mem' K' := fun mem' ↦ by
      show (if mem' K = none then cwSel mem' K _ _ else mem') K' = mem' K'
      split_ifs
      · unfold cwSel
        split_ifs
        · exact SelMem.select_of_ne _ _ _ h
        · rfl
      · rfl
    simp only [grindMemS]
    rcases TargetSum.decodeDigest (truncateHash (P (trialCell seed K m c)).1) with _ | x
    · exact (grindMemS_of_ne h n (c + 1) _).trans (hc mem)
    · exact hc mem

/-- The search keeps a selected key's memory. -/
theorem grindMemS_of_some {c₀ : Qrom.HashDomain × Digest} :
    ∀ n c mem, mem K = some c₀ → grindMemS P seed K m n c mem K = some c₀
  | 0, _, _, hm => hm
  | n + 1, c, mem, hm => by
    have hc : cwUpd K (trialCell seed K m c) mem (some (P (trialCell seed K m c))) = mem := by
      show (if mem K = none then cwSel mem K _ _ else mem) = mem
      rw [ite_eq_right (by rw [hm]; exact Option.some_ne_none c₀)]
    simp only [grindMemS, hc]
    rcases TargetSum.decodeDigest (truncateHash (P (trialCell seed K m c)).1) with _ | x
    · exact grindMemS_of_some n (c + 1) mem hm
    · exact hm

theorem grindMemS_of_ne_none {K' : Key} (n c : ℕ) (mem : SelMem) (hm : mem K' ≠ none) :
    grindMemS P seed K m n c mem K' = mem K' := by
  by_cases h : K' = K
  · subst h
    obtain ⟨c₀, hc₀⟩ := Option.ne_none_iff_exists'.mp hm
    rw [hc₀]
    exact grindMemS_of_some P seed K' m n c mem hc₀
  · exact grindMemS_of_ne P seed K m h n c mem

/-- **The search records its selection** in an unselected key's memory: the cell of the selected
trial and its digest, or nothing when the search fails. -/
theorem grindMemS_self (v : QTable) :
    ∀ n c (mem : SelMem), mem K = none →
      grindMemS P v.publicSeed K m n c mem K =
        (v.selectFrom (fun z ↦ (P z).1) K.1 K.2.1 K.2.2 m n c).map fun sel ↦
          (encCell v.publicSeed K.1 K.2.1 K.2.2 m sel.1,
            v.encDigest (fun z ↦ (P z).1) K.1 K.2.1 K.2.2 m sel.1)
  | 0, _, _, hm => by
    rw [grindMemS, hm]
    rfl
  | n + 1, c, mem, hm => by
    rw [QTable.selectFrom]
    have e : v.encDigest (fun z ↦ (P z).1) K.1 K.2.1 K.2.2 m (BitVec.ofNat counterBits c) =
        truncateHash (P (trialCell v.publicSeed K m c)).1 :=
      rfl
    rw [e]
    simp only [grindMemS]
    rcases hd : TargetSum.decodeDigest (truncateHash (P (trialCell v.publicSeed K m c)).1)
      with _ | x
    · have hc : cwUpd K (trialCell v.publicSeed K m c) mem
          (some (P (trialCell v.publicSeed K m c))) = mem := by
        rw [cwUpd_some_of_none K _ hm, cwSel, ite_eq_right (show ¬Quantum.Sphincs.Codeword.Valid
          (pairDigest (P (trialCell v.publicSeed K m c))) from
            Quantum.Sphincs.Codeword.decode_eq_none_iff.1 hd)]
      dsimp only
      rw [hc]
      exact grindMemS_self v n (c + 1) mem hm
    · dsimp only
      rw [cwUpd_some_of_none K _ hm, cwSel, ite_eq_left (show Quantum.Sphincs.Codeword.Valid
        (pairDigest (P (trialCell v.publicSeed K m c))) from
          Quantum.Sphincs.Codeword.valid_of_decode hd), SelMem.select_self]
      rfl

end grind

/-! ## Tables differing at the digest cells only -/

section offDig

/-- **Two tables agreeing off the digest cells.** -/
def OffDig (w v : QTable) : Prop :=
  ∀ p : Pos, (∀ m, p.1 ≠ .hmsg m) → w p = v p

variable {w v : QTable} (h : OffDig w v)
include h

theorem OffDig.dig {r : RawPos} (hr : ∀ m, r ≠ .hmsg m) : w.dig r = v.dig r :=
  QTable.dig_congr fun hp ↦ h ⟨r, hp⟩ hr

theorem OffDig.out {r : RawPos} (hr : ∀ m, r ≠ .hmsg m) : w.out r = v.out r :=
  QTable.out_congr fun hp ↦ h ⟨r, hp⟩ hr

theorem OffDig.publicSeed : w.publicSeed = v.publicSeed :=
  h.dig fun _ hm ↦ by cases hm

theorem OffDig.randomizer (msg : Message) : w.randomizer msg = v.randomizer msg :=
  h.dig fun _ hm ↦ by cases hm

theorem OffDig.chainValue (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex)
    (j : ℕ) : w.chainValue l τ e i j = v.chainValue l τ e i j := by
  cases j with
  | zero => exact h.dig fun _ hm ↦ by cases hm
  | succ j =>
    simp only [QTable.chainValue]
    split_ifs
    · exact h.dig fun _ hm ↦ by cases hm
    · rfl

theorem OffDig.treeValue (l : Layer) (τ : TreeIndex) (level index : ℕ) :
    w.treeValue l τ level index = v.treeValue l τ level index := by
  cases level with
  | zero => exact h.dig fun _ hm ↦ by cases hm
  | succ level =>
    simp only [QTable.treeValue]
    split_ifs
    · exact h.dig fun _ hm ↦ by cases hm
    · rfl

theorem OffDig.forsValue (idx : Index) (κ : ForsTreeIndex) (height node : ℕ) :
    w.forsValue idx κ height node = v.forsValue idx κ height node := by
  cases height with
  | zero => exact h.dig fun _ hm ↦ by cases hm
  | succ height =>
    simp only [QTable.forsValue]
    split_ifs
    · exact h.dig fun _ hm ↦ by cases hm
    · rfl

theorem OffDig.root : w.root = v.root := by
  unfold QTable.root QTable.treeRoot
  exact h.treeValue _ _ _ _

theorem OffDig.publicKey : w.publicKey = v.publicKey := by
  unfold QTable.publicKey
  rw [h.publicSeed, h.root]

theorem OffDig.layerMessage (idx : Index) (l : Layer) :
    w.layerMessage idx l = v.layerMessage idx l := by
  unfold QTable.layerMessage QTable.forsKey QTable.treeRoot
  split_ifs
  · exact h.dig fun _ hm ↦ by cases hm
  · exact h.treeValue _ _ _ _

theorem OffDig.forsOpening (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    w.forsOpening idx lv = v.forsOpening idx lv := by
  funext κ
  unfold QTable.forsOpening QTable.forsSecret
  rw [h.dig fun _ hm ↦ by cases hm]
  simp only [h.forsValue]

theorem OffDig.encDigest (H : Qrom.HashDomain → HashOutput) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (msg : Digest) (c : EncodingCounter) :
    w.encDigest H l τ e msg c = v.encDigest H l τ e msg c := by
  unfold QTable.encDigest
  rw [h.publicSeed]

theorem OffDig.selectFrom (H : Qrom.HashDomain → HashOutput) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (msg : Digest) :
    ∀ n c, w.selectFrom H l τ e msg n c = v.selectFrom H l τ e msg n c
  | 0, _ => rfl
  | n + 1, c => by
    simp only [QTable.selectFrom, h.encDigest, OffDig.selectFrom H l τ e msg n (c + 1)]

theorem OffDig.layerSelect (H : Qrom.HashDomain → HashOutput) (idx : Index) (l : Layer) :
    w.layerSelect H idx l = v.layerSelect H idx l := by
  unfold QTable.layerSelect QTable.select
  rw [h.layerMessage, h.selectFrom]

theorem OffDig.layerSig (H : Qrom.HashDomain → HashOutput) (idx : Index) (l : Layer) :
    w.layerSig H idx l = v.layerSig H idx l := by
  unfold QTable.layerSig QTable.layerSignature QTable.select QTable.authPath
  rw [h.layerMessage, h.selectFrom]
  simp only [h.chainValue, h.treeValue]

theorem OffDig.cellOf (S0 : MasterSeed) (p : Pos) : cellOf S0 p w = cellOf S0 p v := by
  refine cellOf_congr S0 fun q hq ↦ h q fun m hm ↦ ?_
  obtain ⟨p, hp⟩ := p
  rw [hm] at hq
  have hT : layerHeight topLayer = 10 := rfl
  have hC : chainLength = 4 := rfl
  have hF : forsTreeHeight = 10 := rfl
  cases p with
  | chain _ _ _ _ s => have := s.isLt; simp [RawPos.rank, hT, hC] at hq; omega
  | node _ _ k _ => have := k.isLt; simp [RawPos.rank, hT, hC] at hq; omega
  | forsNode _ _ k _ => have := k.isLt; simp [RawPos.rank, hT, hC] at hq; omega
  | _ => simp [RawPos.rank, hT, hC, hF] at hq

end offDig

/-- **A signature from its parts**: the randomizer, the FORS opening and the three layer
signatures, when all are present. -/
def sigOf3 (R : Randomizer) (fo : ForsTreeIndex → ForsTreeOpening) :
    Option (LayerSignature 0) → Option (LayerSignature 1) → Option (LayerSignature 2) →
      Option Signature
  | some bottom, some middle, some top =>
      some ⟨R, fo, KeyGenerationAndSigning.layerSignatures bottom middle top⟩
  | _, _, _ => none

theorem signature_eq_sigOf3 (v : QTable) (H : Qrom.HashDomain → HashOutput) (msg : Message) :
    v.signature H msg = sigOf3 (v.randomizer msg) (v.forsOpening (v.index msg) (v.leaves msg))
      (v.layerSig H (v.index msg) 0) (v.layerSig H (v.index msg) 1)
      (v.layerSig H (v.index msg) 2) := by
  unfold QTable.signature
  cases v.layerSig H (v.index msg) 0 <;> cases v.layerSig H (v.index msg) 1 <;>
    cases v.layerSig H (v.index msg) 2 <;> rfl

/-- A layer signature is its selection's opening. -/
theorem layerSig_eq_map (v : QTable) (H : Qrom.HashDomain → HashOutput) (idx : Index)
    (l : Layer) :
    v.layerSig H idx l = (v.layerSelect H idx l).map fun sel ↦
      ⟨sel.1, fun i ↦ v.chainValue l (treeOfIndex l idx) (leafOfIndex l idx) i (sel.2 i).val,
        v.authPath l (treeOfIndex l idx) (leafOfIndex l idx)⟩ :=
  rfl

/-! ## Views agreeing at the encoding cells -/

section enc

/-- Two hash functions agree at the encoding cells under `PK.seed = seed`. -/
def EncAgree (seed : PublicParameter) (H H' : Qrom.HashDomain → HashOutput) : Prop :=
  ∀ l τ e msg c, H (encCell seed l τ e msg c) = H' (encCell seed l τ e msg c)

variable {v : QTable} {H H' : Qrom.HashDomain → HashOutput} (h : EncAgree v.publicSeed H H')
include h

theorem EncAgree.encDigest (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (msg : Digest)
    (c : EncodingCounter) : v.encDigest H l τ e msg c = v.encDigest H' l τ e msg c := by
  unfold QTable.encDigest
  rw [h]

theorem EncAgree.selectFrom (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (msg : Digest) :
    ∀ n c, v.selectFrom H l τ e msg n c = v.selectFrom H' l τ e msg n c
  | 0, _ => rfl
  | n + 1, c => by
    simp only [QTable.selectFrom, h.encDigest, EncAgree.selectFrom l τ e msg n (c + 1)]

theorem EncAgree.layerSelect (idx : Index) (l : Layer) :
    v.layerSelect H idx l = v.layerSelect H' idx l := by
  unfold QTable.layerSelect QTable.select
  rw [h.selectFrom]

theorem EncAgree.layerSig (idx : Index) (l : Layer) :
    v.layerSig H idx l = v.layerSig H' idx l := by
  rw [layerSig_eq_map, layerSig_eq_map, h.layerSelect]

end enc

/-! ## The cells of the table and the encoding cells -/

theorem cellOf_ne_encCell (S0 : MasterSeed) (v : QTable) (p : Pos) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (msg : Digest) (c : EncodingCounter) :
    cellOf S0 p v ≠ encCell v.publicSeed l τ e msg c := fun hc ↦ by
  have he : encCell v.publicSeed l τ e msg c =
      cell (v.expandedKey S0) v.root (.enc l τ e) (msg, c) :=
    cell_congr rfl
  rw [he] at hc
  exact posSlot_ne_enc v p.1 l τ e (slot_eq_of_cell_eq _ _ (slotInRange_posSlot v p) trivial hc)

theorem hmsgCall_cellOf_ne_zero (S0 : MasterSeed) (v : QTable) {p : Pos}
    (hp : ∀ m, p.1 ≠ .hmsg m) : hmsgCall (cellOf S0 p v) ≠ some 0 := fun h ↦ by
  obtain ⟨R, M, c, hs⟩ := exists_hmsg_of_hmsgCall (slotInRange_posSlot v p) h
  obtain ⟨p, hpr⟩ := p
  cases p with
  | hmsg m => exact hp m rfl
  | _ => cases hs

theorem hvwS_congr {s s' : RRegS SelMem} {z : Qrom.HashDomain} (h1 : s'.2.1.1 z = s.2.1.1 z)
    (h2 : s'.1.1 z = s.1.1 z) : hvwS s' z = hvwS s z := by
  show ((s'.2.1.1 z).or (s'.1.1 z)).getD 0 = ((s.2.1.1 z).or (s.1.1 z)).getD 0
  rw [h1, h2]

theorem hvwS_tuple {M : Type} (s : RRegS M) (L : Finset TPos) (m : M) :
    hvwS (s.1, s.2.1, (L, m)) = hvwS s :=
  rfl

theorem progUpdate_programH_fst (z : Qrom.HashDomain) (a : PairOut)
    (W : Hw PairOut Qrom.HashDomain) :
    (progUpdate (.programH z a) W).1 = Function.update W.1 z (some a) :=
  rfl

theorem noBot_of_fst_eq {s s' : RRegS SelMem} (h : s'.1 = s.1) (hs : NoBot s) : NoBot s' := by
  show Quantum.Xmss.Assembly.NoBotDb s'.1
  rw [h]
  exact hs

/-! ## The signer in the decompressed basis -/

section signer

variable (θ : TVals)

/-- **A step of the signer changing only the cells of the positions `C`**: no empty cell kept, the
inner memory kept, the label grown by value coordinates, and the hardwired and database
`h`-cells kept off the positions' cells. -/
def StepRel (C : Set Pos) (s s' : RRegS SelMem) : Prop :=
  (NoBot s → NoBot s') ∧ s'.2.2.2 = s.2.2.2 ∧ s.2.2.1 ⊆ s'.2.2.1 ∧
    (∀ t ∈ s'.2.2.1, t ∈ s.2.2.1 ∨ t.IsVal) ∧
    ∀ z, (∀ p ∈ C, z ≠ cellQ θ p) → s'.2.1.1 z = s.2.1.1 z ∧ s'.1.1 z = s.1.1 z

variable {θ}

theorem StepRel.refl (C : Set Pos) (s : RRegS SelMem) : StepRel θ C s s :=
  ⟨id, rfl, subset_rfl, fun _ ht ↦ .inl ht, fun _ _ ↦ ⟨rfl, rfl⟩⟩

theorem StepRel.trans {C C' : Set Pos} {s s₁ s₂ : RRegS SelMem} (h₁ : StepRel θ C s s₁)
    (h₂ : StepRel θ C' s₁ s₂) : StepRel θ (C ∪ C') s s₂ :=
  ⟨fun h ↦ h₂.1 (h₁.1 h), h₂.2.1.trans h₁.2.1, h₁.2.2.1.trans h₂.2.2.1,
    fun t ht ↦ (h₂.2.2.2.1 t ht).elim (fun ht ↦ h₁.2.2.2.1 t ht) .inr, fun z hz ↦ by
      obtain ⟨a₁, b₁⟩ := h₁.2.2.2.2 z fun p hp ↦ hz p (.inl hp)
      obtain ⟨a₂, b₂⟩ := h₂.2.2.2.2 z fun p hp ↦ hz p (.inr hp)
      exact ⟨a₂.trans a₁, b₂.trans b₁⟩⟩

theorem StepRel.mono {C C' : Set Pos} {s s' : RRegS SelMem} (h : StepRel θ C s s')
    (hC : C ⊆ C') : StepRel θ C' s s' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun z hz ↦ h.2.2.2.2 z fun p hp ↦ hz p (hC hp)⟩

theorem stepRel_reveal {T : Finset TPos} (hT : ValOnly T) (s : RRegS SelMem) :
    StepRel θ ∅ s (s.1, s.2.1, (s.2.2.1 ∪ T, s.2.2.2)) :=
  ⟨id, rfl, Finset.subset_union_left, fun t ht ↦ (Finset.mem_union.1 ht).imp_right (hT t),
    fun _ _ ↦ ⟨rfl, rfl⟩⟩

theorem stepRel_prog {p : Pos} {s s' : RRegS SelMem}
    (h : ProgRelS (cellQ θ p) (tabOf θ p) s s') : StepRel θ {p} s s' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h2, congrArg (·.2.2) h1, ?_, fun t ht ↦ .inl ?_, fun z hz ↦ ⟨?_, h3 z (hz p rfl)⟩⟩
  · rw [show s'.2.2.1 = s.2.2.1 from congrArg (·.2.1) h1]
  · rwa [show s'.2.2.1 = s.2.2.1 from congrArg (·.2.1) h1] at ht
  · rw [show s'.2.1 = progUpdate (.programH (cellQ θ p) (tabOf θ p)) s.2.1 from
      congrArg Prod.fst h1]
    exact Function.update_of_ne (hz p rfl) _ _

variable {m₀ : Finset TPos × SelMem}

variable (θ) in
/-- **Program calls of structural positions** move the register by `StepRel`. -/
theorem htS₂_progPosS (B : QReg) : ∀ (ps : List Pos), (∀ p ∈ ps, p.1.IsStruct) →
    ∀ P : Set (RRegS SelMem), HTS₂ m₀ (realizeT θ (progPos SelMem B ps)) P
      fun _ ↦ {s' | ∃ s ∈ P, StepRel θ {p | p ∈ ps} s s'}
  | [], _, P => htS₂_pure () fun s hs ↦ ⟨s, hs, StepRel.refl _ s⟩
  | p :: ps, hps, P => by
    refine htS₂_progThen m₀ θ (progT p) (realize_progT (hps p List.mem_cons_self) (seedOf θ) θ)
      _ P _ ((htS₂_progPosS B ps (fun q hq ↦ hps q (List.mem_cons_of_mem _ hq)) _).mono
        subset_rfl fun _ ↦ ?_)
    rintro s₂ ⟨s₁, ⟨s, hs, hR⟩, hS⟩
    refine ⟨s, hs, ((stepRel_prog hR).trans hS).mono ?_⟩
    rintro q (hq | hq)
    · exact List.mem_cons.2 (.inl hq)
    · exact List.mem_cons_of_mem _ hq

variable (θ) in
/-- **A counter search in the decompressed basis**: the view's selection, the memory updated by
`grindMemS`, the label grown by the value the key signs. -/
theorem htS₂_selectS (B : QReg) (K : Key) (P : Set (RRegS SelMem)) (hP : ∀ s ∈ P, NoBot s) :
    HTS₂ m₀ (realizeT θ (selectT SelMem cwUpd (tabOf θ).publicSeed B K)) P
      fun g ↦ {s' | ∃ s ∈ P, g = (tabOf θ).selectFrom (hHS s) K.1 K.2.1 K.2.2
          ((tabOf θ).valuePos (msgPos K)) encodingAttemptLimit 0 ∧
        s'.1 = s.1 ∧ s'.2.1 = s.2.1 ∧ s'.2.2.1 = s.2.2.1 ∪ {vcoord (msgPos K)} ∧
        s'.2.2.2 = grindMemS (hvwS s) (tabOf θ).publicSeed K ((tabOf θ).valuePos (msgPos K))
          encodingAttemptLimit 0 s.2.2.2} := by
  rw [selectT]
  refine htS₂_revealThen m₀ θ _ _ P _ fun mem ↦ ?_
  have hb : (tabR (restrictTo {vcoord (msgPos K)} θ)).valuePos (msgPos K) =
      (tabOf θ).valuePos (msgPos K) :=
    valuePos_tabOf_congr _ (pairAt_extW_restrictTo (Finset.mem_singleton_self _) θ)
  dsimp only
  rw [hb]
  refine ((det_grindS (m₀ := m₀) (θ := θ) (tabOf θ) B K _ encodingAttemptLimit 0) _ ?_).mono
    subset_rfl fun g ↦ ?_
  · rintro s ⟨s₀, hs₀, -, rfl⟩
    exact hP s₀ hs₀
  · rintro s' ⟨s, ⟨s₀, hs₀, -, rfl⟩, hg, hs'⟩
    refine ⟨s₀, hs₀, hg, by rw [hs'], by rw [hs'], by rw [hs'], ?_⟩
    simp only [hs', hvwS_tuple]

variable (θ) in
/-- **Publishing a layer signature in the decompressed basis.** -/
theorem htS₂_publishS (B : QReg) (K : Key) (c : EncodingCounter) (x : Encoding)
    (P : Set (RRegS SelMem)) :
    HTS₂ m₀ (realizeT θ (publishT SelMem B K c x)) P
      fun sig ↦ {s' | ∃ s ∈ P, sig = layerSigD θ K c x ∧
        StepRel θ {p | p ∈ layerPos K x} s s'} := by
  rw [publishT]
  refine htS₂_revealThen m₀ θ _ _ P _ fun mem ↦ ?_
  refine htS₂_realizeT_bind m₀ θ (htS₂_progPosS θ B _ (fun p hp ↦ isStruct_of_mem_layerPos hp) _)
    fun _ ↦ htS₂_pure _ ?_
  rintro s₂ ⟨s₁, ⟨s, hs, -, rfl⟩, hS⟩
  exact ⟨s, hs, rfl, ((stepRel_reveal (valOnly_layerReveal K x) s).trans hS).mono
    fun p hp ↦ hp.resolve_left id⟩

variable (θ) in
/-- **A FORS opening in the decompressed basis.** -/
theorem htS₂_forsOpenS (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (P : Set (RRegS SelMem)) :
    HTS₂ m₀ (realizeT θ (forsOpenT SelMem B idx lv)) P
      fun fo ↦ {s' | ∃ s ∈ P, fo = forsD θ idx lv ∧ StepRel θ {p | p ∈ forsPos idx lv} s s'} := by
  rw [forsOpenT]
  refine htS₂_revealThen m₀ θ _ _ P _ fun mem ↦ ?_
  refine htS₂_realizeT_bind m₀ θ (htS₂_progPosS θ B _ (fun p hp ↦ isStruct_of_mem_forsPos hp) _)
    fun _ ↦ htS₂_pure _ ?_
  rintro s₂ ⟨s₁, ⟨s, hs, -, rfl⟩, hS⟩
  exact ⟨s, hs, rfl, ((stepRel_reveal (valOnly_forsReveal idx lv) s).trans hS).mono
    fun p hp ↦ hp.resolve_left id⟩

/-- The positions a signature's publication programs, when all three searches succeed. -/
def pubSet (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    Option (EncodingCounter × Encoding) → Option (EncodingCounter × Encoding) →
      Option (EncodingCounter × Encoding) → Set Pos
  | some (_, x₀), some (_, x₁), some (_, x₂) => {p | p ∈ forsPos idx lv ∨
      p ∈ layerPos (keyOf 0 idx) x₀ ∨ p ∈ layerPos (keyOf 1 idx) x₁ ∨ p ∈ layerPos (keyOf 2 idx) x₂}
  | _, _, _ => ∅

variable (θ) in
/-- **The publication of a signature in the decompressed basis**: when all three searches
succeed, the signature from the revealed values and the program calls of its positions; nothing
otherwise. -/
theorem htS₂_publishAllS (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (R : Randomizer) (g₀ g₁ g₂ : Option (EncodingCounter × Encoding)) (P : Set (RRegS SelMem)) :
    HTS₂ m₀ (realizeT θ (publishAllT SelMem B idx lv R g₀ g₁ g₂)) P
      fun sig ↦ {s' | ∃ s ∈ P, sig = sigOf3 R (forsD θ idx lv)
          (g₀.map fun g ↦ layerSigD θ (keyOf 0 idx) g.1 g.2)
          (g₁.map fun g ↦ layerSigD θ (keyOf 1 idx) g.1 g.2)
          (g₂.map fun g ↦ layerSigD θ (keyOf 2 idx) g.1 g.2) ∧
        StepRel θ (pubSet idx lv g₀ g₁ g₂) s s'} := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;>
    try exact htS₂_pure _ fun s hs ↦ ⟨s, hs, rfl, StepRel.refl _ s⟩
  simp only [publishAllT]
  refine htS₂_realizeT_bind m₀ θ (htS₂_forsOpenS θ B idx lv P) fun fo ↦ ?_
  refine htS₂_realizeT_bind m₀ θ (htS₂_publishS θ B _ _ _ _) fun b ↦ ?_
  refine htS₂_realizeT_bind m₀ θ (htS₂_publishS θ B _ _ _ _) fun mi ↦ ?_
  refine htS₂_realizeT_bind m₀ θ (htS₂_publishS θ B _ _ _ _) fun t ↦ htS₂_pure _ ?_
  rintro s₄ ⟨s₃, ⟨s₂, ⟨s₁, ⟨s, hs, rfl, h1⟩, rfl, h2⟩, rfl, h3⟩, rfl, h4⟩
  refine ⟨s, hs, rfl, (((h1.trans h2).trans h3).trans h4).mono ?_⟩
  rintro p (((hp | hp) | hp) | hp)
  · exact Or.inl hp
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr (Or.inl hp))
  · exact Or.inr (Or.inr (Or.inr hp))

/-- The event side's digest pair of `msg` at the label `L`. -/
noncomputable def dgS (θ : TVals) (L : Finset TPos) (msg : Message) : PairOut :=
  pairAt θ (strOut L msg)

/-- The index of `msg`'s signature at the label `L`. -/
noncomputable def idxS (θ : TVals) (L : Finset TPos) (msg : Message) : Index :=
  digestIndex (digestOfPair (dgS θ L msg))

/-- The FORS leaves of `msg`'s signature at the label `L`. -/
noncomputable def lvS (θ : TVals) (L : Finset TPos) (msg : Message) :
    ForsTreeIndex → ForsLeafIndex :=
  digestForsLeaves (digestOfPair (dgS θ L msg))

/-- The memory after the three counter searches of a signature of index `idx`. -/
def grind3 (θ : TVals) (P : Qrom.HashDomain → PairOut) (idx : Index) (mem : SelMem) : SelMem :=
  grindMemS P (tabOf θ).publicSeed (keyOf 2 idx) ((tabOf θ).layerMessage idx 2)
    encodingAttemptLimit 0
    (grindMemS P (tabOf θ).publicSeed (keyOf 1 idx) ((tabOf θ).layerMessage idx 1)
      encodingAttemptLimit 0
      (grindMemS P (tabOf θ).publicSeed (keyOf 0 idx) ((tabOf θ).layerMessage idx 0)
        encodingAttemptLimit 0 mem))

/-- **The effect of a signature of `msg`** on the decompressed register, at the event side's
digest policy: no empty cell, the view kept at the encoding cells, the label grown by value
coordinates and the digest's reveal, the memory moved by the three searches, the table's
signature from the view, and the hardwired cells: the earlier ones, the digest cell with its
stream pair, and, when all three searches succeed, the published positions' cells. -/
def SignEff (θ : TVals) (msg : Message) (s : RRegS SelMem) (sig : Option Signature)
    (s' : RRegS SelMem) : Prop :=
  NoBot s' ∧
  (∀ l τ e m c, hvwS s' (encCell (tabOf θ).publicSeed l τ e m c) =
    hvwS s (encCell (tabOf θ).publicSeed l τ e m c)) ∧
  s.2.2.1 ⊆ s'.2.2.1 ∧ (∀ t ∈ s'.2.2.1, t ∈ s.2.2.1 ∨ t.IsVal ∨ t ∈ strNeed s.2.2.1 msg) ∧
  strNeed s.2.2.1 msg ⊆ s'.2.2.1 ∧
  s'.2.2.2 = grind3 θ (hvwS s) (idxS θ s.2.2.1 msg) s.2.2.2 ∧
  sig = sigOf3 ((tabOf θ).randomizer msg)
    ((tabOf θ).forsOpening (idxS θ s.2.2.1 msg) (lvS θ s.2.2.1 msg))
    ((tabOf θ).layerSig (hHS s) (idxS θ s.2.2.1 msg) 0)
    ((tabOf θ).layerSig (hHS s) (idxS θ s.2.2.1 msg) 1)
    ((tabOf θ).layerSig (hHS s) (idxS θ s.2.2.1 msg) 2) ∧
  ∀ z ω, s'.2.1.1 z = some ω → s.2.1.1 z = some ω ∨
    (z = cellQ θ (digPos msg) ∧ ω = dgS θ s.2.2.1 msg) ∨
    ∃ sel₀ sel₁ sel₂ : EncodingCounter × Encoding,
      (tabOf θ).layerSelect (hHS s) (idxS θ s.2.2.1 msg) 0 = some sel₀ ∧
      (tabOf θ).layerSelect (hHS s) (idxS θ s.2.2.1 msg) 1 = some sel₁ ∧
      (tabOf θ).layerSelect (hHS s) (idxS θ s.2.2.1 msg) 2 = some sel₂ ∧
      ∃ p, (p ∈ forsPos (idxS θ s.2.2.1 msg) (lvS θ s.2.2.1 msg) ∨
        p ∈ layerPos (keyOf 0 (idxS θ s.2.2.1 msg)) sel₀.2 ∨
        p ∈ layerPos (keyOf 1 (idxS θ s.2.2.1 msg)) sel₁.2 ∨
        p ∈ layerPos (keyOf 2 (idxS θ s.2.2.1 msg)) sel₂.2) ∧ z = cellQ θ p

theorem grindMemS_congr {P P' : Qrom.HashDomain → PairOut} {seed : PublicParameter} {K : Key}
    {m : Digest} (h : ∀ c, P (trialCell seed K m c) = P' (trialCell seed K m c)) :
    ∀ n c mem, grindMemS P seed K m n c mem = grindMemS P' seed K m n c mem
  | 0, _, _ => rfl
  | n + 1, c, mem => by
    simp only [grindMemS, h c, grindMemS_congr h n (c + 1)]

theorem cellQ_ne_encCell (θ : TVals) (p : Pos) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (msg : Digest) (c : EncodingCounter) : cellQ θ p ≠ encCell (tabOf θ).publicSeed l τ e msg c :=
  cellOf_ne_encCell (seedOf θ) (tabOf θ) p l τ e msg c

theorem pubSet_cases {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex}
    {g₀ g₁ g₂ : Option (EncodingCounter × Encoding)} {p : Pos} (h : p ∈ pubSet idx lv g₀ g₁ g₂) :
    ∃ sel₀ sel₁ sel₂, g₀ = some sel₀ ∧ g₁ = some sel₁ ∧ g₂ = some sel₂ ∧
      (p ∈ forsPos idx lv ∨ p ∈ layerPos (keyOf 0 idx) sel₀.2 ∨
        p ∈ layerPos (keyOf 1 idx) sel₁.2 ∨ p ∈ layerPos (keyOf 2 idx) sel₂.2) := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try exact absurd h (Set.notMem_empty _)
  exact ⟨_, _, _, rfl, rfl, rfl, h⟩

variable {m₀ : Finset TPos × SelMem}

/-- **The assembly of a signature's effect** from its steps: the reveals and the digest program
(`s₃`), the three counter searches (`s₄`, `s₅`, `s₆`) and the publication (`s₇`). -/
theorem signEff_of {msg : Message} {s s₃ s₄ s₅ s₆ s₇ : RRegS SelMem} {sig : Option Signature}
    {g₀ g₁ g₂ : Option (EncodingCounter × Encoding)}
    (hp1 : s₃.2 = (progUpdate (.programH (cellQ θ (digPos msg)) (dgS θ s.2.2.1 msg)) s.2.1,
      ((s.2.2.1 ∪ {seedC, rootC, rndC msg}) ∪ strNeed s.2.2.1 msg, s.2.2.2)))
    (hp2 : NoBot s → NoBot s₃) (hp3 : ∀ z', z' ≠ cellQ θ (digPos msg) → s₃.1.1 z' = s.1.1 z')
    (hg₀ : g₀ = (tabOf θ).selectFrom (hHS s₃) (keyOf 0 (idxS θ s.2.2.1 msg)).1
      (keyOf 0 (idxS θ s.2.2.1 msg)).2.1 (keyOf 0 (idxS θ s.2.2.1 msg)).2.2
      ((tabOf θ).valuePos (msgPos (keyOf 0 (idxS θ s.2.2.1 msg)))) encodingAttemptLimit 0)
    (e41 : s₄.1 = s₃.1) (e42 : s₄.2.1 = s₃.2.1)
    (e43 : s₄.2.2.1 = s₃.2.2.1 ∪ {vcoord (msgPos (keyOf 0 (idxS θ s.2.2.1 msg)))})
    (e44 : s₄.2.2.2 = grindMemS (hvwS s₃) (tabOf θ).publicSeed (keyOf 0 (idxS θ s.2.2.1 msg))
      ((tabOf θ).valuePos (msgPos (keyOf 0 (idxS θ s.2.2.1 msg)))) encodingAttemptLimit 0
        s₃.2.2.2)
    (hg₁ : g₁ = (tabOf θ).selectFrom (hHS s₄) (keyOf 1 (idxS θ s.2.2.1 msg)).1
      (keyOf 1 (idxS θ s.2.2.1 msg)).2.1 (keyOf 1 (idxS θ s.2.2.1 msg)).2.2
      ((tabOf θ).valuePos (msgPos (keyOf 1 (idxS θ s.2.2.1 msg)))) encodingAttemptLimit 0)
    (e51 : s₅.1 = s₄.1) (e52 : s₅.2.1 = s₄.2.1)
    (e53 : s₅.2.2.1 = s₄.2.2.1 ∪ {vcoord (msgPos (keyOf 1 (idxS θ s.2.2.1 msg)))})
    (e54 : s₅.2.2.2 = grindMemS (hvwS s₄) (tabOf θ).publicSeed (keyOf 1 (idxS θ s.2.2.1 msg))
      ((tabOf θ).valuePos (msgPos (keyOf 1 (idxS θ s.2.2.1 msg)))) encodingAttemptLimit 0
        s₄.2.2.2)
    (hg₂ : g₂ = (tabOf θ).selectFrom (hHS s₅) (keyOf 2 (idxS θ s.2.2.1 msg)).1
      (keyOf 2 (idxS θ s.2.2.1 msg)).2.1 (keyOf 2 (idxS θ s.2.2.1 msg)).2.2
      ((tabOf θ).valuePos (msgPos (keyOf 2 (idxS θ s.2.2.1 msg)))) encodingAttemptLimit 0)
    (e61 : s₆.1 = s₅.1) (e62 : s₆.2.1 = s₅.2.1)
    (e63 : s₆.2.2.1 = s₅.2.2.1 ∪ {vcoord (msgPos (keyOf 2 (idxS θ s.2.2.1 msg)))})
    (e64 : s₆.2.2.2 = grindMemS (hvwS s₅) (tabOf θ).publicSeed (keyOf 2 (idxS θ s.2.2.1 msg))
      ((tabOf θ).valuePos (msgPos (keyOf 2 (idxS θ s.2.2.1 msg)))) encodingAttemptLimit 0
        s₅.2.2.2)
    (hsig : sig = sigOf3 ((tabOf θ).randomizer msg)
      (forsD θ (idxS θ s.2.2.1 msg) (lvS θ s.2.2.1 msg))
      (g₀.map fun g ↦ layerSigD θ (keyOf 0 (idxS θ s.2.2.1 msg)) g.1 g.2)
      (g₁.map fun g ↦ layerSigD θ (keyOf 1 (idxS θ s.2.2.1 msg)) g.1 g.2)
      (g₂.map fun g ↦ layerSigD θ (keyOf 2 (idxS θ s.2.2.1 msg)) g.1 g.2))
    (h7 : StepRel θ (pubSet (idxS θ s.2.2.1 msg) (lvS θ s.2.2.1 msg) g₀ g₁ g₂) s₆ s₇)
    (hs : NoBot s) : SignEff θ msg s sig s₇ := by
  have hv3 : ∀ l τ e m c, hvwS s₃ (encCell (tabOf θ).publicSeed l τ e m c) =
      hvwS s (encCell (tabOf θ).publicSeed l τ e m c) := fun l τ e m c ↦ by
    have hz : encCell (tabOf θ).publicSeed l τ e m c ≠ cellQ θ (digPos msg) :=
      fun h ↦ cellQ_ne_encCell θ _ l τ e m c h.symm
    refine hvwS_congr ?_ (hp3 _ hz)
    rw [show s₃.2.1 = progUpdate (.programH (cellQ θ (digPos msg)) (dgS θ s.2.2.1 msg)) s.2.1
      from congrArg Prod.fst hp1, progUpdate_programH_fst, Function.update_of_ne hz]
  have hv4 : ∀ l τ e m c, hvwS s₄ (encCell (tabOf θ).publicSeed l τ e m c) =
      hvwS s (encCell (tabOf θ).publicSeed l τ e m c) := fun l τ e m c ↦
    (hvwS_congr (by rw [e42]) (by rw [e41])).trans (hv3 l τ e m c)
  have hv5 : ∀ l τ e m c, hvwS s₅ (encCell (tabOf θ).publicSeed l τ e m c) =
      hvwS s (encCell (tabOf θ).publicSeed l τ e m c) := fun l τ e m c ↦
    (hvwS_congr (by rw [e52]) (by rw [e51])).trans (hv4 l τ e m c)
  have hv6 : ∀ l τ e m c, hvwS s₆ (encCell (tabOf θ).publicSeed l τ e m c) =
      hvwS s (encCell (tabOf θ).publicSeed l τ e m c) := fun l τ e m c ↦
    (hvwS_congr (by rw [e62]) (by rw [e61])).trans (hv5 l τ e m c)
  have hv7 : ∀ l τ e m c, hvwS s₇ (encCell (tabOf θ).publicSeed l τ e m c) =
      hvwS s (encCell (tabOf θ).publicSeed l τ e m c) := fun l τ e m c ↦ by
    obtain ⟨a, b⟩ := h7.2.2.2.2 _ fun p _ ↦ fun h ↦ cellQ_ne_encCell θ p l τ e m c h.symm
    exact (hvwS_congr a b).trans (hv6 l τ e m c)
  have hea : ∀ s' : RRegS SelMem, (∀ l τ e m c, hvwS s' (encCell (tabOf θ).publicSeed l τ e m c)
      = hvwS s (encCell (tabOf θ).publicSeed l τ e m c)) →
      EncAgree (tabOf θ).publicSeed (hHS s') (hHS s) := fun s' hs' l τ e m c ↦
    congrArg Prod.fst (hs' l τ e m c)
  have hsel : ∀ (s' : RRegS SelMem), (∀ l τ e m c, hvwS s' (encCell (tabOf θ).publicSeed
      l τ e m c) = hvwS s (encCell (tabOf θ).publicSeed l τ e m c)) → ∀ l g,
      g = (tabOf θ).selectFrom (hHS s') (keyOf l (idxS θ s.2.2.1 msg)).1
        (keyOf l (idxS θ s.2.2.1 msg)).2.1 (keyOf l (idxS θ s.2.2.1 msg)).2.2
        ((tabOf θ).valuePos (msgPos (keyOf l (idxS θ s.2.2.1 msg)))) encodingAttemptLimit 0 →
      g = (tabOf θ).layerSelect (hHS s) (idxS θ s.2.2.1 msg) l := fun s' hs' l g hg ↦ by
    rw [QTable.layerSelect_eq]
    unfold QTable.select
    rw [hg, EncAgree.selectFrom (hea s' hs')]
    rfl
  have h0 := hsel s₃ hv3 0 g₀ hg₀
  have h1 := hsel s₄ hv4 1 g₁ hg₁
  have h2 := hsel s₅ hv5 2 g₂ hg₂
  have hgr : ∀ (s' : RRegS SelMem), (∀ l τ e m c, hvwS s' (encCell (tabOf θ).publicSeed
      l τ e m c) = hvwS s (encCell (tabOf θ).publicSeed l τ e m c)) → ∀ l mem,
      grindMemS (hvwS s') (tabOf θ).publicSeed (keyOf l (idxS θ s.2.2.1 msg))
        ((tabOf θ).valuePos (msgPos (keyOf l (idxS θ s.2.2.1 msg)))) encodingAttemptLimit 0 mem =
      grindMemS (hvwS s) (tabOf θ).publicSeed (keyOf l (idxS θ s.2.2.1 msg))
        ((tabOf θ).layerMessage (idxS θ s.2.2.1 msg) l) encodingAttemptLimit 0 mem :=
    fun s' hs' l mem ↦ by
      rw [QTable.msgPos_eq]
      exact grindMemS_congr (fun c ↦ hs' _ _ _ _ _) _ _ _
  have hmem3 : s₃.2.2.2 = s.2.2.2 := congrArg (·.2.2) hp1
  have hlab3 : s₃.2.2.1 = s.2.2.1 ∪ {seedC, rootC, rndC msg} ∪ strNeed s.2.2.1 msg :=
    congrArg (·.2.1) hp1
  have hsub : s.2.2.1 ∪ strNeed s.2.2.1 msg ⊆ s₇.2.2.1 := by
    refine subset_trans ?_ h7.2.2.1
    rw [e63, e53, e43, hlab3]
    intro t ht
    simp only [Finset.mem_union] at ht ⊢
    tauto
  refine ⟨h7.1 (noBot_of_fst_eq (by rw [e61, e51, e41]) (hp2 hs)), hv7,
    subset_trans Finset.subset_union_left hsub, ?_, subset_trans Finset.subset_union_right hsub,
    ?_, ?_, ?_⟩
  · intro t ht
    rcases h7.2.2.2.1 t ht with ht | ht
    · rw [e63, e53, e43, hlab3] at ht
      simp only [Finset.mem_union, Finset.mem_singleton] at ht
      rcases ht with ((((ht | ht) | ht) | ht) | ht) | ht
      · exact Or.inl ht
      · exact Or.inr (Or.inl (valOnly_sigReveal msg t ht))
      · exact Or.inr (Or.inr ht)
      · exact Or.inr (Or.inl (ht ▸ isVal_vcoord _))
      · exact Or.inr (Or.inl (ht ▸ isVal_vcoord _))
      · exact Or.inr (Or.inl (ht ▸ isVal_vcoord _))
    · exact Or.inr (Or.inl ht)
  · rw [h7.2.1, e64, e54, e44, hmem3, hgr s₅ hv5, hgr s₄ hv4, hgr s₃ hv3]
    rfl
  · rw [hsig, forsD_eq, layerSig_eq_map, layerSig_eq_map, layerSig_eq_map, ← h0, ← h1, ← h2]
    simp only [layerSigD_eq]
    rfl
  · intro z ω hz
    by_cases hp : ∃ p ∈ pubSet (idxS θ s.2.2.1 msg) (lvS θ s.2.2.1 msg) g₀ g₁ g₂, z = cellQ θ p
    · obtain ⟨p, hpm, rfl⟩ := hp
      obtain ⟨sel₀, sel₁, sel₂, e0, e1, e2, hcase⟩ := pubSet_cases hpm
      exact Or.inr (Or.inr ⟨sel₀, sel₁, sel₂, h0.symm.trans e0, h1.symm.trans e1,
        h2.symm.trans e2, p, hcase, rfl⟩)
    · simp only [not_exists, not_and] at hp
      have hz6 : s₇.2.1.1 z = s₆.2.1.1 z := (h7.2.2.2.2 z fun p hp' h ↦ hp p hp' h).1
      rw [hz6, e62, e52, e42, show s₃.2.1 = progUpdate (.programH (cellQ θ (digPos msg))
        (dgS θ s.2.2.1 msg)) s.2.1 from congrArg Prod.fst hp1, progUpdate_programH_fst] at hz
      by_cases hzd : z = cellQ θ (digPos msg)
      · rw [hzd, Function.update_self] at hz
        exact Or.inr (Or.inl ⟨hzd, (Option.some.inj hz).symm⟩)
      · rw [Function.update_of_ne hzd] at hz
        exact Or.inl hz

variable (θ) in
/-- **A signature at the event side's digest policy, in the decompressed basis** (`SignEff`). -/
theorem htS₂_signS (B : QReg) (msg : Message) (P : Set (RRegS SelMem))
    (hP : ∀ s ∈ P, NoBot s) :
    HTS₂ m₀ (realizeT θ (signT SelMem cwUpd strPol B msg)) P
      fun sig ↦ {s' | ∃ s ∈ P, SignEff θ msg s sig s'} := by
  rw [signT]
  refine htS₂_revealThen m₀ θ _ _ P _ fun mem₁ ↦ ?_
  refine htS₂_revealThen m₀ θ _ _ _ _ fun mem₂ ↦ ?_
  have hd : digestT strPol mem₁.1 msg (restrictTo (strPol.need mem₁.1 msg) θ) =
      digestOfPair (dgS θ mem₁.1 msg) :=
    congrArg digestOfPair (pairR_restrictTo (strPol.out_mem mem₁.1 msg) θ)
  have hr : (digPort strPol mem₁.1 msg).realize θ =
      .programH (cellQ θ (digPos msg)) (dgS θ mem₁.1 msg) := by
    rw [realize_digPort, ← cellOf_digPos (seedOf θ)]
    rfl
  have hs₀ : (tabR (restrictTo {seedC, rootC, rndC msg} θ)).publicSeed = (tabOf θ).publicSeed :=
    sigTabD_publicSeed msg
  have hR₀ : (tabR (restrictTo {seedC, rootC, rndC msg} θ)).randomizer msg =
      (tabOf θ).randomizer msg :=
    sigTabD_randomizer msg
  dsimp only
  rw [hs₀, hR₀, hd]
  refine htS₂_progThen m₀ θ _ hr _ _ _ ?_
  refine htS₂_realizeT_bind m₀ θ (htS₂_selectS θ B _ _ ?_) fun g₀ ↦ ?_
  · rintro s₃ ⟨s₂, ⟨s₁, ⟨s, hs, -, rfl⟩, -, rfl⟩, hpr⟩
    exact hpr.2.1 (hP s hs)
  refine htS₂_realizeT_bind m₀ θ (htS₂_selectS θ B _ _ ?_) fun g₁ ↦ ?_
  · rintro s₄ ⟨s₃, ⟨s₂, ⟨s₁, ⟨s, hs, -, rfl⟩, -, rfl⟩, hpr⟩, -, h41, -⟩
    exact noBot_of_fst_eq h41 (hpr.2.1 (hP s hs))
  refine htS₂_realizeT_bind m₀ θ (htS₂_selectS θ B _ _ ?_) fun g₂ ↦ ?_
  · rintro s₅ ⟨s₄, ⟨s₃, ⟨s₂, ⟨s₁, ⟨s, hs, -, rfl⟩, -, rfl⟩, hpr⟩, -, h41, -⟩, -, h51, -⟩
    exact noBot_of_fst_eq (h51.trans h41) (hpr.2.1 (hP s hs))
  refine (htS₂_publishAllS θ B _ _ _ g₀ g₁ g₂ _).mono subset_rfl fun sig ↦ ?_
  rintro s₇ ⟨s₆, ⟨s₅, ⟨s₄, ⟨s₃, ⟨s₂, ⟨s₁, ⟨s, hs, rfl, rfl⟩, rfl, rfl⟩, hpr⟩, hg₀, e41, e42,
    e43, e44⟩, hg₁, e51, e52, e53, e54⟩, hg₂, e61, e62, e63, e64⟩, hsig, h7⟩
  exact ⟨s, hs, signEff_of hpr.1 hpr.2.1 hpr.2.2 hg₀ e41 e42 e43 e44 hg₁ e51 e52 e53 e54 hg₂ e61
    e62 e63 e64 hsig h7 (hP s hs)⟩

end signer

/-! ## The stream bookkeeping of the event side -/

section stream

/-- The signing transcripts. -/
abbrev SLogS : Type :=
  SufCma.SignLog Message (Option Signature)

/-- **The coordinate of the event side's digest of `m` at the label `L`**: its marked stream
entry, else its digest cell. -/
noncomputable def markC (L : Finset TPos) (m : Message) : TPos :=
  (markOf L m).elim (.dig m) .str

/-- **The stream bookkeeping**: one mark per message, marks only of signed messages, a fallback
digest only once the stream is used up and for an unmarked message, and every signed message
marked or, past the stream, fallen back. -/
def StrOk (L : Finset TPos) (log : SLogS) : Prop :=
  OneMark L ∧ (∀ m j, SPos.asg m j ∈ L → ∃ q ∈ log, q.1 = m) ∧
    (∀ m, SPos.dig m ∈ L → signatureLimit ≤ asgCount L ∧ ∀ j, SPos.asg m j ∉ L) ∧
    ∀ q ∈ log, (∃ j, SPos.asg q.1 j ∈ L) ∨ (SPos.dig q.1 ∈ L ∧ signatureLimit < log.length)

/-- The message of a mark. -/
def asgMsg : TPos → Option Message
  | .asg m _ => some m
  | _ => none

/-- **The marks are at most the signed requests.** -/
theorem asgCount_le_length {L : Finset TPos} {log : SLogS} (h : StrOk L log) :
    asgCount L ≤ log.length := by
  unfold asgCount
  refine (Finset.card_le_card_of_injOn asgMsg
    (t := (log.map fun q ↦ some q.1).toFinset) ?_ ?_).trans
    ((List.toFinset_card_le _).trans (List.length_map _).le)
  · intro t ht
    obtain ⟨ht, ha⟩ := Finset.mem_filter.1 ht
    cases t with
    | asg m j =>
      obtain ⟨q, hq, rfl⟩ := h.2.1 m j ht
      exact List.mem_toFinset.2 (List.mem_map_of_mem hq)
    | _ => cases ha
  · intro t ht t' ht' he
    obtain ⟨ht, ha⟩ := Finset.mem_filter.1 ht
    obtain ⟨ht', ha'⟩ := Finset.mem_filter.1 ht'
    cases t with
    | asg m j =>
      cases t' with
      | asg m' j' =>
        obtain rfl : m = m' := Option.some.inj he
        rw [h.1 m j j' ht ht']
      | _ => cases ha'
    | _ => cases ha

theorem asgCount_mono {L L' : Finset TPos} (h : L ⊆ L') : asgCount L ≤ asgCount L' :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem oneMark_anti {L L' : Finset TPos} (h : OneMark L') (hsub : L ⊆ L') : OneMark L :=
  fun m j j' hj hj' ↦ h m j j' (hsub hj) (hsub hj')

theorem streamIdx_some_facts' {L : Finset TPos} {msg : Message} {j : Fin signatureLimit}
    (hs : streamIdx L msg = some j) :
    SPos.asg msg j ∈ L ∨ ((∀ j', SPos.asg msg j' ∉ L) ∧ j.val = asgCount L) := by
  have h := streamIdx_some_facts (U := (∅ : Finset TPos)) hs fun _ _ h ↦
    Finset.notMem_empty _ h
  rwa [Finset.union_empty] at h

theorem streamIdx_none_facts' {L : Finset TPos} {msg : Message} (hs : streamIdx L msg = none) :
    (∀ j, SPos.asg msg j ∉ L) ∧ signatureLimit ≤ asgCount L := by
  have h := streamIdx_none_facts (U := (∅ : Finset TPos)) hs fun _ _ h ↦
    Finset.notMem_empty _ h
  rwa [Finset.union_empty] at h

section step

variable {L L' : Finset TPos} {msg : Message}
  (hnew : ∀ t ∈ L', t ∈ L ∨ t.IsVal ∨ t ∈ strNeed L msg)
include hnew

theorem asg_mem_step {m : Message} {j : Fin signatureLimit} (h : SPos.asg m j ∈ L') :
    SPos.asg m j ∈ L ∨ (m = msg ∧ streamIdx L msg = some j) := by
  rcases hnew _ h with h | h | h
  · exact .inl h
  · exact h.elim
  · rcases hs : streamIdx L msg with _ | j'
    · rw [mem_strNeed_none hs] at h
      cases h
    · rw [mem_strNeed_some hs] at h
      rcases h with h | h
      · cases h
      · cases h
        exact .inr ⟨rfl, rfl⟩

theorem dig_mem_step {m : Message} (h : SPos.dig m ∈ L') :
    SPos.dig m ∈ L ∨ (m = msg ∧ streamIdx L msg = none) := by
  rcases hnew _ h with h | h | h
  · exact .inl h
  · exact h.elim
  · rcases hs : streamIdx L msg with _ | j'
    · rw [mem_strNeed_none hs] at h
      cases h
      exact .inr ⟨rfl, rfl⟩
    · rw [mem_strNeed_some hs] at h
      rcases h with h | h <;> cases h

/-- **A signature keeps the stream bookkeeping.** -/
theorem strOk_step {log : SLogS} {sig : Option Signature} (h : StrOk L log) (hsub : L ⊆ L')
    (hstr : strNeed L msg ⊆ L') : StrOk L' (log ++ [⟨msg, sig⟩]) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hlen : (log ++ ([⟨msg, sig⟩] : SLogS)).length = log.length + 1 := by simp
  refine ⟨fun m j j' hj hj' ↦ ?_, fun m j hj ↦ ?_, fun m hd ↦ ?_, fun q hq ↦ ?_⟩
  · rcases asg_mem_step hnew hj with hj | ⟨rfl, hs⟩ <;>
      rcases asg_mem_step hnew hj' with hj' | ⟨hm, hs'⟩
    · exact h1 m j j' hj hj'
    · subst hm
      rcases streamIdx_some_facts' hs' with hj'' | ⟨hf, -⟩
      · exact h1 _ j j' hj hj''
      · exact absurd hj (hf j)
    · rcases streamIdx_some_facts' hs with hj'' | ⟨hf, -⟩
      · exact h1 _ j j' hj'' hj'
      · exact absurd hj' (hf j')
    · exact Option.some.inj (hs.symm.trans hs')
  · rcases asg_mem_step hnew hj with hj | ⟨rfl, -⟩
    · obtain ⟨q, hq, hqm⟩ := h2 m j hj
      exact ⟨q, List.mem_append_left _ hq, hqm⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
  · rcases dig_mem_step hnew hd with hd | ⟨rfl, hs⟩
    · obtain ⟨hN, hf⟩ := h3 m hd
      refine ⟨hN.trans (asgCount_mono hsub), fun j hj ↦ ?_⟩
      rcases asg_mem_step hnew hj with hj | ⟨rfl, hs⟩
      · exact hf j hj
      · rcases streamIdx_some_facts' hs with hj' | ⟨-, hjv⟩
        · exact hf j hj'
        · have := j.isLt
          omega
    · obtain ⟨hf, hN⟩ := streamIdx_none_facts' hs
      refine ⟨hN.trans (asgCount_mono hsub), fun j hj ↦ ?_⟩
      rcases asg_mem_step hnew hj with hj | ⟨-, hs'⟩
      · exact hf j hj
      · rw [hs] at hs'
        cases hs'
  · rw [hlen]
    rcases List.mem_append.1 hq with hq | hq
    · rcases h4 q hq with ⟨j, hj⟩ | ⟨hd, hlt⟩
      · exact .inl ⟨j, hsub hj⟩
      · exact .inr ⟨hsub hd, by omega⟩
    · obtain rfl := List.mem_singleton.1 hq
      rcases hs : streamIdx L msg with _ | j
      · refine .inr ⟨hstr ((mem_strNeed_none hs _).2 rfl), ?_⟩
        have := (streamIdx_none_facts' hs).2
        have := asgCount_le_length ⟨h1, h2, h3, h4⟩
        omega
      · exact .inl ⟨j, hstr ((mem_strNeed_some hs _).2 (.inr rfl))⟩

end step

theorem markC_of_asg {L : Finset TPos} (hL : OneMark L) {m : Message} {j : Fin signatureLimit}
    (h : SPos.asg m j ∈ L) : markC L m = .str j := by
  unfold markC
  rw [markOf_of_mem hL h]
  rfl

theorem markC_of_free {L : Finset TPos} {m : Message} (h : ∀ j, SPos.asg m j ∉ L) :
    markC L m = .dig m := by
  unfold markC
  rw [markOf_of_free h]
  rfl

/-- **A signed message's digest coordinate is stable** as the label grows. -/
theorem markC_stable {L L' : Finset TPos} {log' : SLogS} (h' : StrOk L' log') (hsub : L ⊆ L')
    {m : Message} (hm : (∃ j, SPos.asg m j ∈ L) ∨ SPos.dig m ∈ L) : markC L' m = markC L m := by
  rcases hm with ⟨j, hj⟩ | hd
  · rw [markC_of_asg h'.1 (hsub hj), markC_of_asg (oneMark_anti h'.1 hsub) hj]
  · have hfree := (h'.2.2.1 m (hsub hd)).2
    rw [markC_of_free hfree, markC_of_free fun j hj ↦ hfree j (hsub hj)]

/-- **The signed message's digest at the label after**: the stream pair the signer used. -/
theorem pairAt_markC_step {θ : TVals} {L L' : Finset TPos} {log' : SLogS} {msg : Message}
    (h' : StrOk L' log') (hstr : strNeed L msg ⊆ L') :
    ((∃ j, SPos.asg msg j ∈ L') ∨ SPos.dig msg ∈ L') ∧
      pairAt θ (markC L' msg) = dgS θ L msg := by
  unfold dgS
  rcases hs : streamIdx L msg with _ | j
  · have hd : SPos.dig msg ∈ L' := hstr ((mem_strNeed_none hs _).2 rfl)
    rw [strOut_none hs, markC_of_free (h'.2.2.1 msg hd).2]
    exact ⟨.inr hd, rfl⟩
  · have ha : SPos.asg msg j ∈ L' := hstr ((mem_strNeed_some hs _).2 (.inr rfl))
    rw [strOut_some hs, markC_of_asg h'.1 ha]
    exact ⟨.inl ⟨j, ha⟩, rfl⟩

/-- **A table compatible with the label `L`**: the table off the digest cells, and at each
signed message's digest cell the pair at its digest coordinate. -/
def CompatS (θ : TVals) (L : Finset TPos) (w : QTable) : Prop :=
  OffDig w (tabOf θ) ∧
    ∀ m, ((∃ j, SPos.asg m j ∈ L) ∨ SPos.dig m ∈ L) → w (digPos m) = pairAt θ (markC L m)

theorem compatS_anti {θ : TVals} {L L' : Finset TPos} {log' : SLogS} {w : QTable}
    (hw : CompatS θ L' w) (h' : StrOk L' log') (hsub : L ⊆ L') : CompatS θ L w :=
  ⟨hw.1, fun m hm ↦ (hw.2 m (hm.imp (fun ⟨j, hj⟩ ↦ ⟨j, hsub hj⟩) fun hd ↦ hsub hd)).trans
    (by rw [markC_stable h' hsub hm])⟩

end stream

/-! ## The invariant of the challenge prefix at the event side's policy -/

section inv

/-- The record of the selection `sel` of `K_l(idx)`: its encoding cell and digest. -/
def recOfS (w : QTable) (H : Qrom.HashDomain → HashOutput) (l : Layer) (idx : Index)
    (sel : EncodingCounter × Encoding) : Qrom.HashDomain × Digest :=
  (encCell w.publicSeed l (treeOfIndex l idx) (leafOfIndex l idx) (w.layerMessage idx l) sel.1,
    w.encDigest H l (treeOfIndex l idx) (leafOfIndex l idx) (w.layerMessage idx l) sel.1)

/-- **Every recorded selection is a key's selection.** -/
def MemOkS (w : QTable) (H : Qrom.HashDomain → HashOutput) (mem : SelMem) : Prop :=
  ∀ K c, mem K = some c → ∃ l idx sel, keyOf l idx = K ∧ w.layerSelect H idx l = some sel ∧
    c = recOfS w H l idx sel

/-- **The position `p` is published by the signature of `msg`**: all three searches succeed and
`p` is a position of the FORS opening or of a layer signature. -/
def PubBy (w : QTable) (H : Qrom.HashDomain → HashOutput) (msg : Message) (p : Pos) : Prop :=
  ∃ sel₀ sel₁ sel₂ : EncodingCounter × Encoding,
    w.layerSelect H (w.index msg) 0 = some sel₀ ∧ w.layerSelect H (w.index msg) 1 = some sel₁ ∧
    w.layerSelect H (w.index msg) 2 = some sel₂ ∧
    (p ∈ forsPos (w.index msg) (w.leaves msg) ∨ p ∈ layerPos (keyOf 0 (w.index msg)) sel₀.2 ∨
      p ∈ layerPos (keyOf 1 (w.index msg)) sel₁.2 ∨ p ∈ layerPos (keyOf 2 (w.index msg)) sel₂.2)

/-- **The facts of a register** against the table `w` and the hash `H`: the transcript's
signatures are the table's, the memory records every request's selections and only selections,
and every hardwired cell is a signed message's digest cell with its pair or a published
position's cell. -/
def FactsS (S0 : MasterSeed) (w : QTable) (H : Qrom.HashDomain → HashOutput) (log : SLogS)
    (s : RRegS SelMem) : Prop :=
  (∀ q ∈ log, q.2 = w.signature H q.1) ∧ (∀ q ∈ log, Records w H s.2.2.2 q.1) ∧
    MemOkS w H s.2.2.2 ∧
    ∀ z ω, s.2.1.1 z = some ω → (∃ q ∈ log, z = cellOf S0 (digPos q.1) w ∧ ω = w (digPos q.1)) ∨
      ∃ q ∈ log, ∃ p, PubBy w H q.1 p ∧ z = cellOf S0 p w

/-- **The invariant along the challenge prefix** at the event side's policy: no empty cell, the
stream bookkeeping, and the facts against every table compatible with the label, with the hash of
the register's view. -/
def InvS (θ : TVals) (log : SLogS) : Set (RRegS SelMem) :=
  {s | NoBot s ∧ StrOk s.2.2.1 log ∧
    ∀ w, CompatS θ s.2.2.1 w → FactsS (seedOf θ) w (hHS s) log s}

section congrH

variable {w : QTable} {H H' : Qrom.HashDomain → HashOutput} (h : EncAgree w.publicSeed H H')
include h

theorem recOfS_congrH (l : Layer) (idx : Index) (sel : EncodingCounter × Encoding) :
    recOfS w H l idx sel = recOfS w H' l idx sel := by
  unfold recOfS
  rw [h.encDigest]

theorem signature_congrH (msg : Message) : w.signature H msg = w.signature H' msg := by
  rw [signature_eq_sigOf3, signature_eq_sigOf3, h.layerSig, h.layerSig, h.layerSig]

theorem records_congrH {mem : SelMem} {msg : Message} (hR : Records w H mem msg) :
    Records w H' mem msg := by
  intro l sel hs
  rw [← h.layerSelect] at hs
  rw [hR l sel hs, h.encDigest]

theorem memOkS_congrH {mem : SelMem} (hM : MemOkS w H mem) : MemOkS w H' mem := by
  intro K c hc
  obtain ⟨l, idx, sel, hK, hs, rfl⟩ := hM K c hc
  exact ⟨l, idx, sel, hK, (h.layerSelect idx l).symm.trans hs, recOfS_congrH h l idx sel⟩

theorem pubBy_congrH {msg : Message} {p : Pos} (hp : PubBy w H msg p) : PubBy w H' msg p := by
  obtain ⟨a, b, c, h0, h1, h2, hp⟩ := hp
  exact ⟨a, b, c, (h.layerSelect _ _).symm.trans h0, (h.layerSelect _ _).symm.trans h1,
    (h.layerSelect _ _).symm.trans h2, hp⟩

end congrH

theorem recOfS_offDig {w v : QTable} (h : OffDig w v) (H : Qrom.HashDomain → HashOutput)
    (l : Layer) (idx : Index) (sel : EncodingCounter × Encoding) :
    recOfS w H l idx sel = recOfS v H l idx sel := by
  unfold recOfS
  rw [h.publicSeed, h.layerMessage, h.encDigest]

theorem recOfS_key {w : QTable} {H : Qrom.HashDomain → HashOutput} {l : Layer} {idx idx' : Index}
    (hk : keyOf l idx' = keyOf l idx) (sel : EncodingCounter × Encoding) :
    recOfS w H l idx' sel = recOfS w H l idx sel := by
  have h1 : treeOfIndex l idx' = treeOfIndex l idx := congrArg (fun K : Key ↦ K.2.1) hk
  have h2 : leafOfIndex l idx' = leafOfIndex l idx := congrArg (fun K : Key ↦ K.2.2) hk
  unfold recOfS
  rw [h1, h2, layerMessage_congr hk]

/-! ### The memory after the three searches -/

section grind3

variable (θ : TVals) (P : Qrom.HashDomain → PairOut) (idx : Index)

theorem keyOf_ne_layer {l l' : Layer} (h : l ≠ l') : keyOf l idx ≠ keyOf l' idx :=
  fun hk ↦ h (congrArg Prod.fst hk)

theorem grind3_of_ne_none {mem : SelMem} {K : Key} (hm : mem K ≠ none) :
    grind3 θ P idx mem K = mem K := by
  unfold grind3
  have h1 : grindMemS P (tabOf θ).publicSeed (keyOf 0 idx) ((tabOf θ).layerMessage idx 0)
      encodingAttemptLimit 0 mem K = mem K :=
    grindMemS_of_ne_none _ _ _ _ _ _ _ hm
  have h2 : grindMemS P (tabOf θ).publicSeed (keyOf 1 idx) ((tabOf θ).layerMessage idx 1)
      encodingAttemptLimit 0 (grindMemS P (tabOf θ).publicSeed (keyOf 0 idx)
        ((tabOf θ).layerMessage idx 0) encodingAttemptLimit 0 mem) K = mem K :=
    (grindMemS_of_ne_none _ _ _ _ _ _ _ (by rw [h1]; exact hm)).trans h1
  rw [grindMemS_of_ne_none _ _ _ _ _ _ _ (by rw [h2]; exact hm), h2]

theorem grind3_of_ne {mem : SelMem} {K : Key} (hK : ∀ l, K ≠ keyOf l idx) :
    grind3 θ P idx mem K = mem K := by
  unfold grind3
  rw [grindMemS_of_ne _ _ _ _ (hK 2), grindMemS_of_ne _ _ _ _ (hK 1),
    grindMemS_of_ne _ _ _ _ (hK 0)]

theorem grind3_key0 {mem : SelMem} (hm : mem (keyOf 0 idx) = none) :
    grind3 θ P idx mem (keyOf 0 idx) = ((tabOf θ).layerSelect (fun z ↦ (P z).1) idx 0).map
      (recOfS (tabOf θ) (fun z ↦ (P z).1) 0 idx) := by
  unfold grind3
  rw [grindMemS_of_ne _ _ _ _ (keyOf_ne_layer idx (by decide)),
    grindMemS_of_ne _ _ _ _ (keyOf_ne_layer idx (by decide)), grindMemS_self _ _ _ _ _ _ _ hm]
  rfl

theorem grind3_key1 {mem : SelMem} (hm : mem (keyOf 1 idx) = none) :
    grind3 θ P idx mem (keyOf 1 idx) = ((tabOf θ).layerSelect (fun z ↦ (P z).1) idx 1).map
      (recOfS (tabOf θ) (fun z ↦ (P z).1) 1 idx) := by
  unfold grind3
  have h0 := grindMemS_of_ne P (tabOf θ).publicSeed (keyOf 0 idx) ((tabOf θ).layerMessage idx 0)
    (keyOf_ne_layer idx (by decide : (1 : Layer) ≠ 0)) encodingAttemptLimit 0 mem
  rw [grindMemS_of_ne _ _ _ _ (keyOf_ne_layer idx (by decide)),
    grindMemS_self _ _ _ _ _ _ _ (h0.trans hm)]
  rfl

theorem grind3_key2 {mem : SelMem} (hm : mem (keyOf 2 idx) = none) :
    grind3 θ P idx mem (keyOf 2 idx) = ((tabOf θ).layerSelect (fun z ↦ (P z).1) idx 2).map
      (recOfS (tabOf θ) (fun z ↦ (P z).1) 2 idx) := by
  unfold grind3
  have h0 := grindMemS_of_ne P (tabOf θ).publicSeed (keyOf 0 idx) ((tabOf θ).layerMessage idx 0)
    (keyOf_ne_layer idx (by decide : (2 : Layer) ≠ 0)) encodingAttemptLimit 0 mem
  have h1 := grindMemS_of_ne P (tabOf θ).publicSeed (keyOf 1 idx) ((tabOf θ).layerMessage idx 1)
    (keyOf_ne_layer idx (by decide : (2 : Layer) ≠ 1)) encodingAttemptLimit 0
    (grindMemS P (tabOf θ).publicSeed (keyOf 0 idx) ((tabOf θ).layerMessage idx 0)
      encodingAttemptLimit 0 mem)
  rw [grindMemS_self _ _ _ _ _ _ _ ((h1.trans h0).trans hm)]
  rfl

/-- **A search records its selection** at an unselected key. -/
theorem grind3_key {mem : SelMem} (l : Layer) (hm : mem (keyOf l idx) = none) :
    grind3 θ P idx mem (keyOf l idx) = ((tabOf θ).layerSelect (fun z ↦ (P z).1) idx l).map
      (recOfS (tabOf θ) (fun z ↦ (P z).1) l idx) := by
  fin_cases l
  · exact grind3_key0 θ P idx hm
  · exact grind3_key1 θ P idx hm
  · exact grind3_key2 θ P idx hm

end grind3

end inv

end Quantum.Qrom.Sphincs

end
