module

public import Quantum.Xmss.Assembly.PathBad
public import Quantum.Sphincs.HonestTable

@[expose] public section

/-!
# The path-collision event of leanSPHINCS's in-table paths

The round-by-round count of `Quantum.Xmss.Assembly.PathBad` (`frac_pathColl_le`: the `h`-cells of
paths with distinct first blocks collide for at most `N² / |X| + N² (G + 1) / |Z|` of the keys),
applied to leanSPHINCS's structural slots (contract C1, `Quantum.Sphincs.HonestTable`).

**The in-table paths.** The paths are stated over the public data `w = (PK.seed, π, k, k')`
(`XW`), the key `h` and the values `v : ValPos → Digest`, without a template: `slotBlk P s v` are
the blocks of slot `s`'s input `slotInput P s v`, `nBlk P s` their number (`nBlk_le`: at most `8`,
the one-time leaf; the FORS roots take `4`), and `sCellK`, `sCellR`, `sCellZ` the `k`-, `k'`- and
`h`-cells of a round (`rnK`, `rnR`, `rnZ` of the generic count), `sOutCap` the output cell (the last
`h`-cell). The in-table outputs are the positions `p` with `InPos p` (`outSlot p` in the table and
outputting `p`), `xI` their set; `outSlot_slotOutPos`: every structural slot is one. First blocks
name their slot (`slotOfBlock_slotBlk`), so distinct in-table outputs have distinct first blocks
(`xBlk_injOn`).

**The event.** `OutSep`: distinct in-table outputs have distinct output cells; `PathsAvoid`: no
`h`-cell of a round before the last of an in-table path is an output cell; `PathBad`: one of them
fails. Distinct `h`-cells over all rounds exclude it (`not_injOn_of_pathBad`). With
`N = 8 |xI|`:

* `pathBad_good_frac_le`: `PermGood π G ∧ PathBad` for at most `N² / |X| + N² (G + 1) / |Z|`;
* `pathBad_frac_le`: `PathBad` for at most the bad permutations plus that bound;
* `pathBad_frac_le_keccak`: at most `2^-400` (`|ValPos| ≤ 2^47`, `G = 18`).
-/

open scoped ENNReal

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest PublicParameter HashInput ChainStep chainLength littleEndianBytes
  digestsPayload hasherInput)
open HashSig.OverPermutation (nodePayload)
open Quantum.Xmss (X Z blocks blockOf firstBlock head?_blocks length_blocks
  length_littleEndianBytes length_flatMap_littleEndianBytes)
open Quantum.Xmss.Assembly (rnK rnR rnZ famK famR famZ rnds mem_rnds card_rnds_le frac_pathColl_le
  XW card_filter_le_add_of_imp inv_card_mul_card_filter_comp_fst natCast_div_eq_ofReal rnCard_X
  rnCard_Z permTerm_le_keccak)

namespace Quantum.Sphincs.Assembly

/-! ## The slots' paths -/

/-- Block `j` of slot `s`'s input from the values `v`, under `PK.seed = P`. -/
def slotBlk (P : PublicParameter) (s : Slot) (v : ValPos → Digest) (j : ℕ) : X :=
  (blocks (slotInput P s v)).getD j 0

/-- The number of blocks of slot `s`'s input (it does not depend on the values). -/
def nBlk (P : PublicParameter) (s : Slot) : ℕ :=
  (blocks (slotInput P s fun _ ↦ 0)).length

/-- The `k`-cell of round `j` of slot `s`'s path at `w = (PK.seed, π, k, k')`, `h` and `v`. -/
def sCellK (w : XW) (h : Z → X) (s : Slot) (v : ValPos → Digest) (j : ℕ) : X :=
  rnK w.2.1 h w.2.2.1 w.2.2.2 (slotBlk w.1 s v) j

/-- The `k'`-cell of round `j` of slot `s`'s path. -/
def sCellR (w : XW) (h : Z → X) (s : Slot) (v : ValPos → Digest) (j : ℕ) : X :=
  rnR w.2.1 h w.2.2.1 w.2.2.2 (slotBlk w.1 s v) j

/-- The `h`-cell of round `j` of slot `s`'s path. -/
def sCellZ (w : XW) (h : Z → X) (s : Slot) (v : ValPos → Digest) (j : ℕ) : Z :=
  rnZ w.2.1 h w.2.2.1 w.2.2.2 (slotBlk w.1 s v) j

/-- **The output cell** of slot `s`: the `h`-cell of its last round. -/
def sOutCap (w : XW) (h : Z → X) (s : Slot) (v : ValPos → Digest) : Z :=
  sCellZ w h s v (nBlk w.1 s - 1)

/-! ### Lengths -/

theorem length_digestsPayload {n : ℕ} (g : Fin n → Digest) : (digestsPayload g).length = 16 * n :=
  (length_flatMap_littleEndianBytes (List.ofFn g)).trans
    (congrArg (16 * ·) (List.length_ofFn (f := g)))

theorem length_le16 (a : Digest) : (littleEndianBytes 16 a).length = 16 :=
  length_littleEndianBytes 16 a

theorem length_nodePayload (a b : Digest) : (nodePayload a b).length = 32 := by
  rw [nodePayload, List.length_append, length_le16, length_le16]

theorem length_slotPayload (f g : ValPos → Digest) (s : Slot) :
    (slotPayload f s).length = (slotPayload g s).length := by
  cases s with
  | chain => simp only [slotPayload, length_le16]
  | leaf => simp only [slotPayload, length_digestsPayload]
  | node => simp only [slotPayload, length_nodePayload]
  | forsLeaf => simp only [slotPayload, length_le16]
  | forsNode => simp only [slotPayload, length_nodePayload]
  | forsRoots => simp only [slotPayload, length_digestsPayload]
  | _ => rfl

theorem length_slotPayload_le (f : ValPos → Digest) (s : Slot) :
    (slotPayload f s).length ≤ 1024 := by
  cases s with
  | chain => simp only [slotPayload, length_le16]; omega
  | leaf => simp only [slotPayload, length_digestsPayload, chainCount]; omega
  | node => simp only [slotPayload, length_nodePayload]; omega
  | forsLeaf => simp only [slotPayload, length_le16]; omega
  | forsNode => simp only [slotPayload, length_nodePayload]; omega
  | forsRoots => simp only [slotPayload, length_digestsPayload, forsTreeCount]; omega
  | _ => exact Nat.zero_le _

/-- The input of a slot other than `H_msg` is its addressed input. -/
theorem slotInput_of_ne {s : Slot} (hs : ∀ r m c, s ≠ .hmsg r m c) (P : PublicParameter)
    (v : ValPos → Digest) :
    slotInput P s v = addressedHashInput P (hashDomainFields (slotDomain s)) (slotPayload v s) := by
  cases s with
  | hmsg r m c => exact absurd rfl (hs r m c)
  | _ => rfl

theorem ne_hmsg_of_inTable {s : Slot} (hs : InTable s) : ∀ r m c, s ≠ .hmsg r m c := by
  rintro r m c rfl
  exact hs

theorem length_slotInput (P : PublicParameter) (s : Slot) (f g : ValPos → Digest) :
    (slotInput P s f).length = (slotInput P s g).length := by
  by_cases hs : ∀ r m c, s ≠ .hmsg r m c
  · rw [slotInput_of_ne hs, slotInput_of_ne hs, length_addressedHashInput,
      length_addressedHashInput, length_slotPayload f g]
  · push Not at hs
    obtain ⟨r, m, c, rfl⟩ := hs
    show (messageDigestInput _ _ _ _ _).length = (messageDigestInput _ _ _ _ _).length
    rw [length_messageDigestInput, length_messageDigestInput]

theorem length_slotInput_le (P : PublicParameter) (s : Slot) (f : ValPos → Digest) :
    (slotInput P s f).length ≤ 1072 := by
  by_cases hs : ∀ r m c, s ≠ .hmsg r m c
  · rw [slotInput_of_ne hs, length_addressedHashInput]
    have := length_slotPayload_le f s
    omega
  · push Not at hs
    obtain ⟨r, m, c, rfl⟩ := hs
    show (messageDigestInput _ _ _ _ _).length ≤ 1072
    rw [length_messageDigestInput]
    omega

theorem length_blocks_slotInput (P : PublicParameter) (s : Slot) (f : ValPos → Digest) :
    (blocks (slotInput P s f)).length = nBlk P s := by
  rw [nBlk, length_blocks, length_blocks, length_slotInput P s f fun _ ↦ 0]

theorem nBlk_pos (P : PublicParameter) (s : Slot) : 1 ≤ nBlk P s := by
  rw [nBlk, length_blocks]
  omega

/-- **At most `8` blocks per slot** (the one-time leaf's `64` chain ends). -/
theorem nBlk_le (P : PublicParameter) (s : Slot) : nBlk P s ≤ 8 := by
  have := length_slotInput_le P s fun _ ↦ 0
  rw [nBlk, length_blocks]
  omega

/-! ### First blocks -/

theorem slotBlk_zero (P : PublicParameter) (s : Slot) (v : ValPos → Digest) :
    slotBlk P s v 0 = blockOf (firstBlock (slotInput P s v)) := by
  rw [slotBlk, List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, head?_blocks,
    Option.getD_some]

theorem domainSlot_slotDomain {s : Slot} (hs : InTable s) : domainSlot (slotDomain s) = s := by
  cases s <;> first | rfl | exact hs.elim

theorem domainInRange_slotDomain {s : Slot} (hs : InTable s) : DomainInRange (slotDomain s) := by
  cases s with
  | node l τ height index =>
    obtain ⟨-, h1, h2, h3⟩ := hs
    have hl := layerHeight_le l
    have hi := lt_two_pow_of_lt h3
    have hp : 2 ^ layerHeight l ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact ⟨lt_of_le_of_lt (h2.trans hl) (by norm_num), lt_of_lt_of_le hi hp⟩
  | forsNode idx κ height node =>
    obtain ⟨h1, h2, h3⟩ := hs
    exact ⟨h1, h2, h3⟩
  | _ => trivial

/-- **An in-table slot's first block names it**, for any `PK.root`. -/
theorem slotOfBlock_slotBlk (P : PublicParameter) (root : Digest) (v : ValPos → Digest)
    {s : Slot} (hs : InTable s) : slotOfBlock ⟨P, root⟩ (slotBlk P s v 0) = some s := by
  rw [slotBlk_zero, slotInput_of_ne (ne_hmsg_of_inTable hs), slotOfBlock_addressedHashInput,
    ite_eq_left rfl, slotOfAddress_hashDomainFields _ (domainInRange_slotDomain hs),
    domainSlot_slotDomain hs]

/-! ### The in-table outputs -/

/-- The step leaving the chain position before `j`. -/
def predStep (j : Fin chainLength) : ChainStep :=
  ⟨j.val - 1, by
    have := j.isLt
    simp only [chainLength, HashSig.winternitzBits] at *
    omega⟩

/-- **The slot whose output a position is**: a chain step, a one-time leaf or a tree node, a FORS
leaf or node, the FORS roots compression (a secret's `PRF` slot for a FORS secret). -/
def outSlot : ValPos → Slot
  | .chain l τ e i j => .chain l τ e i (predStep j)
  | .tree l τ level index =>
      if level.val = 0 then .leaf l τ index else .node l τ level.val index.val
  | .forsSecret idx κ s => .prf (.forsSecret idx κ s)
  | .forsTree idx κ height node =>
      if height.val = 0 then .forsLeaf idx κ node else .forsNode idx κ height.val node.val
  | .forsKey idx => .forsRoots idx

/-- **An in-table output position**: its slot is structural and outputs it. -/
def InPos (p : ValPos) : Prop :=
  InTable (outSlot p) ∧ slotOutPos (outSlot p) = p

instance instDecidablePredInPos : DecidablePred InPos := fun _ ↦ by
  unfold InPos
  infer_instance

/-- The in-table output positions (irreducible after `mem_xI`). -/
def xI : Finset ValPos :=
  Finset.univ.filter InPos

theorem mem_xI {p : ValPos} : p ∈ xI ↔ InPos p := by
  simp only [xI, Finset.mem_filter, Finset.mem_univ, true_and]

attribute [irreducible] xI

theorem inTable_outSlot {p : ValPos} (hp : InPos p) : InTable (outSlot p) :=
  hp.1

theorem slotOutPos_outSlot {p : ValPos} (hp : InPos p) : slotOutPos (outSlot p) = p :=
  hp.2

/-- **Every structural slot is the slot of its output.** -/
theorem outSlot_slotOutPos {s : Slot} (hs : InTable s) : outSlot (slotOutPos s) = s := by
  cases s with
  | chain l τ e i step =>
    have h := step.isLt
    simp only [chainLength, HashSig.winternitzBits] at h
    show Slot.chain l τ e i (predStep ⟨(step.val + 1) % chainLength, _⟩) = _
    refine congrArg _ (Fin.ext ?_)
    show ((step.val + 1) % chainLength) - 1 = step.val
    simp only [chainLength, HashSig.winternitzBits]
    omega
  | leaf l τ e =>
    show (if (0 % (layerHeight topLayer + 1)) = 0 then _ else _) = _
    rw [ite_eq_left (Nat.zero_mod _)]
    exact congrArg _ (Fin.ext (Nat.mod_eq_of_lt e.isLt))
  | node l τ height index =>
    obtain ⟨-, h1, h2, h3⟩ := hs
    have hl := layerHeight_le l
    have ht : layerHeight topLayer = 10 := rfl
    have hh : height % (layerHeight topLayer + 1) = height := Nat.mod_eq_of_lt (by omega)
    have hi : index % 2 ^ layerHeight topLayer = index :=
      Nat.mod_eq_of_lt (lt_of_lt_of_le (lt_two_pow_of_lt h3) (two_pow_layerHeight_le l))
    show (if height % (layerHeight topLayer + 1) = 0 then _ else
      Slot.node l τ (height % (layerHeight topLayer + 1))
        (index % 2 ^ layerHeight topLayer)) = _
    rw [hh, ite_eq_right (show ¬height = 0 by omega), hi]
  | forsLeaf idx κ s =>
    show (if (0 % (forsTreeHeight + 1)) = 0 then _ else _) = _
    rw [ite_eq_left (Nat.zero_mod _)]
    exact congrArg _ (Fin.ext (Nat.mod_eq_of_lt s.isLt))
  | forsNode idx κ height node =>
    obtain ⟨h1, h2, h3⟩ := hs
    have hh : height % (forsTreeHeight + 1) = height := Nat.mod_eq_of_lt (by omega)
    have hn : node % 2 ^ forsTreeHeight = node := Nat.mod_eq_of_lt (lt_two_pow_of_lt h3)
    show (if height % (forsTreeHeight + 1) = 0 then _ else
      Slot.forsNode idx κ (height % (forsTreeHeight + 1)) (node % 2 ^ forsTreeHeight)) = _
    rw [hh, ite_eq_right (show ¬height = 0 by omega), hn]
  | forsRoots idx => rfl
  | _ => exact hs.elim

theorem inPos_slotOutPos {s : Slot} (hs : InTable s) : InPos (slotOutPos s) :=
  ⟨by rw [outSlot_slotOutPos hs]; exact hs, by rw [outSlot_slotOutPos hs]⟩

/-- The blocks of an in-table output's slot input. -/
def xBlk (P : PublicParameter) (v : ValPos → Digest) (p : ValPos) : ℕ → X :=
  slotBlk P (outSlot p) v

/-- The number of blocks of an in-table output's slot input. -/
def xLen (P : PublicParameter) (p : ValPos) : ℕ :=
  nBlk P (outSlot p)

theorem xLen_le (P : PublicParameter) (p : ValPos) : xLen P p ≤ 8 :=
  nBlk_le P (outSlot p)

/-- **Distinct in-table outputs have distinct first blocks.** -/
theorem xBlk_injOn (P : PublicParameter) (v : ValPos → Digest) :
    Set.InjOn (fun p ↦ xBlk P v p 0) xI := fun a ha b hb e ↦ by
  have ha' := mem_xI.mp (Finset.mem_coe.mp ha)
  have hb' := mem_xI.mp (Finset.mem_coe.mp hb)
  have h1 := slotOfBlock_slotBlk P 0 v (inTable_outSlot ha')
  rw [show slotBlk P (outSlot a) v 0 = slotBlk P (outSlot b) v 0 from e,
    slotOfBlock_slotBlk P 0 v (inTable_outSlot hb')] at h1
  have hab : outSlot a = outSlot b := (Option.some.inj h1).symm
  rw [← slotOutPos_outSlot ha', hab, slotOutPos_outSlot hb']

/-! ## The path-collision event -/

/-- **Separated output cells**: distinct in-table outputs have distinct output cells. -/
def OutSep (w : XW) (h : Z → X) (v : ValPos → Digest) : Prop :=
  ∀ p ∈ xI, ∀ q ∈ xI, p ≠ q → sOutCap w h (outSlot p) v ≠ sOutCap w h (outSlot q) v

/-- **The paths avoid the output cells**: no `h`-cell of a round before the last of an in-table
output's path is an output cell. -/
def PathsAvoid (w : XW) (h : Z → X) (v : ValPos → Digest) : Prop :=
  ∀ p ∈ xI, ∀ q ∈ xI, ∀ j, j + 1 < xLen w.1 p →
    sCellZ w h (outSlot p) v j ≠ sOutCap w h (outSlot q) v

/-- **The path-collision event** of the public coordinates `((h, w), v)`: two output cells
collide, or an `h`-cell of a path's earlier round is an output cell. -/
def PathBad (y : ((Z → X) × XW) × (ValPos → Digest)) : Prop :=
  ¬OutSep y.1.2 y.1.1 y.2 ∨ ¬PathsAvoid y.1.2 y.1.1 y.2

/-- **Distinct `h`-cells over all rounds exclude `PathBad`.** -/
theorem not_injOn_of_pathBad {w : XW} {h : Z → X} {v : ValPos → Digest}
    (hbad : PathBad ((h, w), v)) :
    ¬Set.InjOn (famZ w.2.1 (xBlk w.1 v) h w.2.2.1 w.2.2.2) (rnds xI (xLen w.1)) := by
  intro hinj
  have hbad' : ¬OutSep w h v ∨ ¬PathsAvoid w h v := hbad
  have hmem : ∀ p ∈ xI, ∀ j < nBlk w.1 (outSlot p),
      ((p, j) : ValPos × ℕ) ∈ (↑(rnds xI (xLen w.1)) : Set (ValPos × ℕ)) :=
    fun p hp j hj ↦ Finset.mem_coe.mpr (mem_rnds.mpr ⟨hp, hj⟩)
  have hpos : ∀ p, 1 ≤ nBlk w.1 (outSlot p) := fun p ↦ nBlk_pos w.1 (outSlot p)
  rcases hbad' with hL | hP
  · refine hL fun p hp q hq hne e ↦ hne ?_
    exact congrArg Prod.fst (hinj (hmem p hp _ (by have := hpos p; omega))
      (hmem q hq _ (by have := hpos q; omega)) e)
  · refine hP fun p hp q hq j hj e ↦ ?_
    have hj' : j + 1 < nBlk w.1 (outSlot p) := hj
    have hpq := hinj (hmem p hp j (by omega)) (hmem q hq _ (by have := hpos q; omega)) e
    have h1 : p = q := congrArg Prod.fst hpq
    have h2 : j = nBlk w.1 (outSlot q) - 1 := congrArg Prod.snd hpq
    subst h1
    omega

/-! ### The fraction -/

/-- The coordinates other than the keys: `PK.seed`, `π`, the values. -/
abbrev RnQ : Type :=
  PublicParameter × Equiv.Perm (X × Z) × (ValPos → Digest)

/-- The public coordinates as `(q, (h, k, k'))`. -/
def rnEquiv : RnQ × ((Z → X) × (X → Z) × (X → Z)) ≃ ((Z → X) × XW) × (ValPos → Digest) where
  toFun x := ((x.2.1, (x.1.1, x.1.2.1, x.2.2.1, x.2.2.2)), x.1.2.2)
  invFun y := ((y.1.2.1, y.1.2.2.1, y.2), (y.1.1, y.1.2.2.2.1, y.1.2.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The public coordinates other than `π`. -/
abbrev XR : Type :=
  (Z → X) × PublicParameter × (X → Z) × (X → Z) × (ValPos → Digest)

/-- The public coordinates as `(π, rest)`. -/
def permEquiv : ((Z → X) × XW) × (ValPos → Digest) ≃ Equiv.Perm (X × Z) × XR where
  toFun y := (y.1.2.2.1, (y.1.1, y.1.2.1, y.1.2.2.2.1, y.1.2.2.2.2, y.2))
  invFun x := ((x.2.1, (x.2.2.1, x.1, x.2.2.2.1, x.2.2.2.2.1)), x.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_rnds_xI_le (P : PublicParameter) : (rnds xI (xLen P)).card ≤ 8 * xI.card :=
  card_rnds_le xI (xLen P) (xLen_le P)

open scoped Classical in
/-- **The path-collision event on good permutations**: `PermGood π G ∧ PathBad` for at most a
fraction `N² / |X| + N² (G + 1) / |Z|` of the public coordinates, `N = 8 |xI|` the rounds of the
in-table paths. -/
theorem pathBad_good_frac_le (G : ℕ) :
    (Fintype.card (((Z → X) × XW) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          PermGood y.1.2.2.1 G ∧ PathBad y).card ≤
      ((8 * xI.card * (8 * xI.card) : ℕ) : ℝ≥0∞) / Fintype.card X +
        ((8 * xI.card * (8 * xI.card) * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z :=
  frac_pathColl_le rnEquiv (fun q ↦ q.2.1) (fun q ↦ xBlk q.1 q.2.2) (fun q ↦ xLen q.1) xI
    (fun q ↦ xBlk_injOn q.1 q.2.2) G _ (fun q ↦ card_rnds_xI_le q.1) _ fun q t hb ↦
      ⟨hb.1, not_injOn_of_pathBad (w := (q.1, q.2.1, t.2.1, t.2.2)) (h := t.1) (v := q.2.2) hb.2⟩

open scoped Classical in
/-- **The path-collision fraction of leanSPHINCS**: `PathBad` for at most the bad permutations
plus `N² / |X| + N² (G + 1) / |Z|`, `N = 8 |xI|`. -/
theorem pathBad_frac_le (G : ℕ) :
    (Fintype.card (((Z → X) × XW) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y ↦ PathBad y).card ≤
      ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) +
        (((8 * xI.card * (8 * xI.card) : ℕ) : ℝ≥0∞) / Fintype.card X +
          ((8 * xI.card * (8 * xI.card) * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z) := by
  set N := Fintype.card (((Z → X) × XW) × (ValPos → Digest))
  have hsub := card_filter_le_add_of_imp (fun y ↦ PathBad y)
    (fun y : ((Z → X) × XW) × (ValPos → Digest) ↦ ¬PermGood (permEquiv y).1 G)
    (fun y : ((Z → X) × XW) × (ValPos → Digest) ↦ PermGood y.1.2.2.1 G ∧ PathBad y)
    fun y hy ↦ by
      by_cases hG : PermGood y.1.2.2.1 G
      · exact Or.inr ⟨hG, hy⟩
      · exact Or.inl hG
  calc (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y ↦ PathBad y).card
      ≤ (N : ℝ≥0∞)⁻¹ * (((Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          ¬PermGood (permEquiv y).1 G).card : ℝ≥0∞) +
        (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          PermGood y.1.2.2.1 G ∧ PathBad y).card) := by
        gcongr
        exact_mod_cast hsub
    _ = (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          ¬PermGood (permEquiv y).1 G).card +
        (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          PermGood y.1.2.2.1 G ∧ PathBad y).card := mul_add _ _ _
    _ ≤ _ := by
        rw [inv_card_mul_card_filter_comp_fst permEquiv fun π ↦ ¬PermGood π G]
        exact add_le_add le_rfl (pathBad_good_frac_le G)

/-! ### At Keccak's sizes -/

/-- Positions as tuples of their indices. -/
def vpCode : ValPos → ((Layer × TreeIndex × TreeLeafIndex × ChainIndex × Fin chainLength) ⊕
    (Layer × TreeIndex × Fin (layerHeight topLayer + 1) × TreeLeafIndex)) ⊕
    ((Index × ForsTreeIndex × ForsLeafIndex) ⊕
      ((Index × ForsTreeIndex × Fin (forsTreeHeight + 1) × ForsLeafIndex) ⊕ Index))
  | .chain l τ e i j => .inl (.inl (l, τ, e, i, j))
  | .tree l τ level index => .inl (.inr (l, τ, level, index))
  | .forsSecret idx κ s => .inr (.inl (idx, κ, s))
  | .forsTree idx κ height node => .inr (.inr (.inl (idx, κ, height, node)))
  | .forsKey idx => .inr (.inr (.inr idx))

theorem vpCode_injective : Function.Injective vpCode := by
  intro a b hab
  cases a <;> cases b <;> simp_all [vpCode]

/-- **At most `2^47` positions** (`1089 · 2^36 + 2^26`). -/
theorem card_valPos_le : Fintype.card ValPos ≤ 2 ^ 47 := by
  refine (Fintype.card_le_of_injective _ vpCode_injective).trans ?_
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  norm_num [layerCount, indexBits, layerHeight, topLayer, chainCount, chainLength,
    HashSig.winternitzBits, forsTreeCount, forsTreeHeight]

theorem card_xI_le : xI.card ≤ 2 ^ 47 :=
  (Finset.card_le_univ _).trans card_valPos_le

set_option exponentiation.threshold 4096 in
/-- The collision terms at Keccak's sizes, for `n ≤ 2^47` paths and `G = 18`. -/
theorem collTerms_le {n cX cZ : ℕ} (hn : n ≤ 2 ^ 47) (hX : cX = 2 ^ 1088) (hZ : cZ = 2 ^ 512) :
    ((8 * n * (8 * n) : ℕ) : ℝ≥0∞) / cX + ((8 * n * (8 * n) * (18 + 1) : ℕ) : ℝ≥0∞) / cZ ≤
      ENNReal.ofReal (1 / 2 ^ 407) := by
  subst hX hZ
  have hNN : 8 * n * (8 * n) ≤ 2 ^ 100 := by
    have h8 : 8 * n ≤ 8 * 2 ^ 47 := Nat.mul_le_mul_left 8 hn
    calc 8 * n * (8 * n) ≤ 8 * 2 ^ 47 * (8 * 2 ^ 47) := Nat.mul_le_mul h8 h8
      _ = 2 ^ 100 := by norm_num
  have hNN' : 8 * n * (8 * n) * (18 + 1) ≤ 2 ^ 100 * 19 :=
    (Nat.mul_le_mul_right _ hNN).trans_eq (by norm_num)
  rw [natCast_div_eq_ofReal (8 * n * (8 * n)) (2 ^ 1088) (by positivity),
    natCast_div_eq_ofReal (8 * n * (8 * n) * (18 + 1)) (2 ^ 512) (by positivity),
    ← ENNReal.ofReal_add (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  apply ENNReal.ofReal_le_ofReal
  have hb : ((8 * n * (8 * n) : ℕ) : ℝ) / ((2 ^ 1088 : ℕ) : ℝ) ≤ 2 ^ 100 / 2 ^ 1088 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hNN) (by positivity)
  have hc : ((8 * n * (8 * n) * (18 + 1) : ℕ) : ℝ) / ((2 ^ 512 : ℕ) : ℝ) ≤
      2 ^ 100 * 19 / 2 ^ 512 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hNN') (by positivity)
  calc _ ≤ 2 ^ 100 / 2 ^ 1088 + 2 ^ 100 * 19 / 2 ^ 512 := add_le_add hb hc
    _ ≤ 1 / 2 ^ 407 := by norm_num

set_option exponentiation.threshold 4096 in
open scoped Classical in
/-- **The path-collision fraction at Keccak's sizes**: at most `2^-400` (with `G = 18`: the bad
permutations `2^-777`, the collisions `2^-407` from `|xI| ≤ 2^47`). -/
theorem pathBad_frac_le_keccak :
    (Fintype.card (((Z → X) × XW) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y ↦ PathBad y).card ≤ ENNReal.ofReal (1 / 2 ^ 400) := by
  refine ((pathBad_frac_le 18).trans (add_le_add permTerm_le_keccak
    (collTerms_le card_xI_le rnCard_X rnCard_Z))).trans ?_
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 777)
    (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 407)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

end Quantum.Sphincs.Assembly

end
