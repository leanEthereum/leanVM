module

public import Quantum.Xmss.Assembly.SrcBad
public import Quantum.Sphincs.Assembly.PathBad

@[expose] public section

/-!
# The source-goodness bad fraction of leanSPHINCS's in-table paths

`SrcGood w h v`: a cell of an in-table slot's path is never the cell of another in-table slot's, or
of the same slot with its designated source changed (`PairGood` for the `k`-, `k'`- and `h`-cells,
with no excluded pair of rounds). It is bounded by the sequential count of
`Quantum.Xmss.Assembly.SrcBad` (`frac_srcColl_le`: real paths `I` and virtual paths `V`, all with
distinct first blocks).

**leanSPHINCS.** The designated source of a structural slot is its first payload value (`dsrc`):
the chain position a step leaves, the first chain end of a one-time leaf, the left child of a tree
or FORS node, the secret of a FORS leaf, the root of FORS tree `0` for the roots compression. It
lies in bytes `48` to `63` of the first block (`payloadLo_slotBlk`). Paths are indexed by (in-table
output position, designated-source value) (`sBlk`, `sLen`, `sReal`, `sVirt`); their first blocks
name the slot and carry the source value (`sBlk_injOn`), so `¬SrcGood` is a source collision
(`sColl_of_not_srcGood`). The coordinates are `((h, w), ρ)` and the values `v`, with any padding
`ρ : W`. With `N = 8 |xI|`, `m = 8`, `|V| ≤ |xI| · 2^128`:

* `srcBad_good_frac_le`: `PermGood π G ∧ ¬SrcGood` for at most `K / |X| + K (G + 1) / |Z|`,
  `K = N² + |xI| |Digest| · 2 · 8 (N + 8)`;
* `srcBad_frac_le`: `¬SrcGood` for at most the bad permutations plus that bound;
* `srcBad_frac_le_keccak`: at most `2^-277` (`K ≤ 2^230`, `G = 18`).
-/

open scoped ENNReal

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest PublicParameter HashInput chainLength littleEndianBytes digestsPayload
  hasherInput)
open HashSig.OverPermutation (nodePayload)
open Quantum.Xmss (X Z blockOf firstBlock length_littleEndianBytes rateSlice)
open Quantum.Xmss.Assembly (famK famR famZ rnds mem_rnds card_rnds_le XW InjAll SColl
  frac_srcColl_le card_filter_le_add_of_imp inv_card_mul_card_filter_comp_fst
  natCast_div_eq_ofReal rnCard_X rnCard_Z permTerm_le_keccak card_digest)

namespace Quantum.Sphincs.Assembly

/-! ## Designated sources -/

/-- **The designated source of a structural slot**: its first payload value. -/
def dsrc : Slot → ValPos
  | .chain l τ e i step => cpos l τ e i step.val
  | .leaf l τ e => cpos l τ e ⟨0, by decide⟩ (chainLength - 1)
  | .node l τ height index => tpos l τ (height - 1) (2 * index)
  | .forsLeaf idx κ s => .forsSecret idx κ s
  | .forsNode idx κ height node => fpos idx κ (height - 1) (2 * node)
  | .forsRoots idx => fpos idx ⟨0, by decide⟩ forsTreeHeight 0
  | _ => rootPos

/-- The first value of a concatenation of values starts it. -/
theorem le16_prefix_digestsPayload {n : ℕ} (g : Fin n → Digest) (i₀ : Fin n) (h₀ : i₀.val = 0) :
    littleEndianBytes 16 (g i₀) <+: digestsPayload g := by
  cases n with
  | zero => exact i₀.elim0
  | succ n =>
    obtain rfl : i₀ = 0 := Fin.ext h₀
    rw [digestsPayload, List.ofFn_succ]
    exact List.prefix_append _ _

/-- **A structural slot's payload starts with its designated source's value.** -/
theorem le16_dsrc_prefix {s : Slot} (hs : InTable s) (v : ValPos → Digest) :
    littleEndianBytes 16 (v (dsrc s)) <+: slotPayload v s := by
  cases s with
  | chain => exact List.prefix_refl _
  | leaf l τ e =>
    exact le16_prefix_digestsPayload (fun i ↦ v (cpos l τ e i (chainLength - 1))) _ rfl
  | node => exact List.prefix_append _ _
  | forsLeaf => exact List.prefix_refl _
  | forsNode => exact List.prefix_append _ _
  | forsRoots idx =>
    exact le16_prefix_digestsPayload (fun κ ↦ v (fpos idx κ forsTreeHeight 0)) _ rfl
  | _ => exact hs.elim

/-- The value in bytes `48` to `63` of a block: an addressed input's first payload value. -/
def payloadLo (x : X) : Digest :=
  rateSlice x 384 (8 * 16) (by norm_num)

/-- **An in-table slot's first block carries its designated source's value.** -/
theorem payloadLo_slotBlk (P : PublicParameter) (v : ValPos → Digest) {s : Slot}
    (hs : InTable s) : payloadLo (slotBlk P s v 0) = v (dsrc s) := by
  rw [slotBlk_zero, slotInput_of_ne (ne_hmsg_of_inTable hs)]
  obtain ⟨t, ht⟩ := le16_dsrc_prefix hs v
  refine rateSlice_firstBlock
    (a := littleEndianBytes 16 P ++ (hashDomainFields (slotDomain s)).toBytes) (n := 16)
    ⟨t, ?_⟩ ?_ _
  · show _ = hasherInput _ _ _
    rw [hasherInput, List.append_assoc, ht]
  · rw [List.length_append, length_littleEndianBytes 16 P, length_toBytes]

/-! ## Source goodness -/

section pairs

variable {C : Type} (nB : Slot → ℕ) (c : Slot → (ValPos → Digest) → ℕ → C)

/-- **Pair goodness** of the values `v` for the cell family `c` (rounds `j < nB s`), off the pairs
of rounds `ex`: no cell of an in-table slot is a cell of another in-table slot, or of the same slot
with its designated source changed. -/
def PairGood (ex : ℕ → ℕ → Prop) (v : ValPos → Digest) : Prop :=
  ∀ s s', InTable s → InTable s' → ∀ j < nB s, ∀ j' < nB s', ¬ex j j' → ∀ d : Digest,
    (s ≠ s' ∨ d ≠ v (dsrc s)) → c s' v j' ≠ c s (Function.update v (dsrc s) d) j

end pairs

/-- **Source goodness** at `w = (PK.seed, π, k, k')` and `h`: pair goodness of the `k`-, `k'`-
and `h`-cells of the in-table paths, every pair of rounds included. -/
def SrcGood (w : XW) (h : Z → X) (v : ValPos → Digest) : Prop :=
  PairGood (nBlk w.1) (sCellK w h) (fun _ _ ↦ False) v ∧
    PairGood (nBlk w.1) (sCellR w h) (fun _ _ ↦ False) v ∧
    PairGood (nBlk w.1) (sCellZ w h) (fun _ _ ↦ False) v

/-! ## Paths indexed by (output position, designated-source value) -/

/-- The blocks of the in-table output `a.1`'s slot input, with its designated source set to
`a.2`. -/
def sBlk (P : PublicParameter) (v : ValPos → Digest) (a : ValPos × Digest) : ℕ → X :=
  xBlk P (Function.update v (dsrc (outSlot a.1)) a.2) a.1

/-- The number of blocks of such a path. -/
def sLen (P : PublicParameter) (a : ValPos × Digest) : ℕ :=
  xLen P a.1

/-- **The real paths**: every in-table output with its designated source's value. -/
def sReal (v : ValPos → Digest) : Finset (ValPos × Digest) :=
  xI.image fun p ↦ (p, v (dsrc (outSlot p)))

theorem mem_sReal {v : ValPos → Digest} {a : ValPos × Digest} :
    a ∈ sReal v ↔ a.1 ∈ xI ∧ a.2 = v (dsrc (outSlot a.1)) := by
  unfold sReal
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨hp, rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨a.1, h1, Prod.ext rfl h2.symm⟩

theorem card_sReal_le (v : ValPos → Digest) : (sReal v).card ≤ xI.card := by
  unfold sReal
  exact Finset.card_image_le

/-- **The virtual paths**: every in-table output with its designated source changed. -/
def sVirt (v : ValPos → Digest) : Finset (ValPos × Digest) :=
  (xI ×ˢ Finset.univ).filter fun a ↦ a.2 ≠ v (dsrc (outSlot a.1))

theorem mem_sVirt {v : ValPos → Digest} {a : ValPos × Digest} :
    a ∈ sVirt v ↔ a.1 ∈ xI ∧ a.2 ≠ v (dsrc (outSlot a.1)) := by
  unfold sVirt
  rw [Finset.mem_filter, Finset.mem_product]
  exact ⟨fun hh ↦ ⟨hh.1.1, hh.2⟩, fun hh ↦ ⟨⟨hh.1, Finset.mem_univ _⟩, hh.2⟩⟩

theorem card_sVirt_le (v : ValPos → Digest) :
    (sVirt v).card ≤ xI.card * Fintype.card Digest := by
  unfold sVirt
  exact (Finset.card_filter_le _ _).trans
    (le_of_eq (by rw [Finset.card_product, Finset.card_univ]))

attribute [irreducible] sReal sVirt

theorem sLen_le (P : PublicParameter) (a : ValPos × Digest) : sLen P a ≤ 8 :=
  xLen_le P a.1

theorem card_rnds_sReal_le (P : PublicParameter) (v : ValPos → Digest) :
    (rnds (sReal v) (sLen P)).card ≤ 8 * xI.card := by
  have h1 : (rnds (sReal v) (sLen P)).card ≤ 8 * (sReal v).card :=
    card_rnds_le (sReal v) (sLen P) (m := 8) (sLen_le P)
  have h2 := card_sReal_le v
  omega

theorem card_rnds_single_le (P : PublicParameter) (w : ValPos × Digest) :
    (rnds {w} (sLen P)).card ≤ 8 := by
  have h1 : (rnds {w} (sLen P)).card ≤ 8 * ({w} : Finset (ValPos × Digest)).card :=
    card_rnds_le {w} (sLen P) (m := 8) (sLen_le P)
  rw [Finset.card_singleton, mul_one] at h1
  exact h1

/-- **The paths' first blocks are distinct**: they name the slot and carry the source value. -/
theorem sBlk_injOn (P : PublicParameter) (v : ValPos → Digest) :
    Set.InjOn (fun a ↦ sBlk P v a 0) ↑(sReal v ∪ sVirt v) := by
  have hx : ∀ a ∈ (↑(sReal v ∪ sVirt v) : Set (ValPos × Digest)), InPos a.1 := fun a ha ↦ by
    rcases Finset.mem_union.mp (Finset.mem_coe.mp ha) with h | h
    · exact mem_xI.mp (mem_sReal.mp h).1
    · exact mem_xI.mp (mem_sVirt.mp h).1
  intro a ha b hb e
  have hpa := hx a ha
  have hpb := hx b hb
  have e' : slotBlk P (outSlot a.1) (Function.update v (dsrc (outSlot a.1)) a.2) 0 =
      slotBlk P (outSlot b.1) (Function.update v (dsrc (outSlot b.1)) b.2) 0 := e
  have h1 := slotOfBlock_slotBlk P 0 (Function.update v (dsrc (outSlot a.1)) a.2)
    (inTable_outSlot hpa)
  rw [e', slotOfBlock_slotBlk P 0 _ (inTable_outSlot hpb)] at h1
  have hab : outSlot a.1 = outSlot b.1 := (Option.some.inj h1).symm
  have h11 : a.1 = b.1 := by
    rw [← slotOutPos_outSlot hpa, hab, slotOutPos_outSlot hpb]
  have h2 := payloadLo_slotBlk P (Function.update v (dsrc (outSlot a.1)) a.2)
    (inTable_outSlot hpa)
  rw [Function.update_self, e', payloadLo_slotBlk P _ (inTable_outSlot hpb),
    Function.update_self] at h2
  exact Prod.ext h11 h2.symm

/-! ## A source-bad table is a source collision -/

/-- **A failure of pair goodness is a collision** of the real rounds, or of the real rounds and a
virtual path's. -/
theorem not_pairGood_cases {C : Type} {w : XW} {v : ValPos → Digest}
    {c : Slot → (ValPos → Digest) → ℕ → C} {ex : ℕ → ℕ → Prop}
    {F : (ValPos × Digest) × ℕ → C}
    (hc : ∀ p ∈ xI, ∀ d j, j < xLen w.1 p →
      c (outSlot p) (Function.update v (dsrc (outSlot p)) d) j = F ((p, d), j))
    (hn : ¬PairGood (nBlk w.1) c ex v) :
    ¬Set.InjOn F ↑(rnds (sReal v) (sLen w.1)) ∨
      ∃ a ∈ sVirt v, ¬Set.InjOn F ↑(rnds (insert a (sReal v)) (sLen w.1)) := by
  by_contra hcon
  have hI : Set.InjOn F ↑(rnds (sReal v) (sLen w.1)) := by
    by_contra h1
    exact hcon (Or.inl h1)
  have hV : ∀ a ∈ sVirt v, Set.InjOn F ↑(rnds (insert a (sReal v)) (sLen w.1)) :=
    fun a ha ↦ by
      by_contra h1
      exact hcon (Or.inr ⟨a, ha, h1⟩)
  apply hn
  intro s s' hs hs' j hj j' hj' _ d hd he
  obtain ⟨p, hp, rfl⟩ : ∃ p ∈ xI, outSlot p = s :=
    ⟨slotOutPos s, mem_xI.mpr (inPos_slotOutPos hs), outSlot_slotOutPos hs⟩
  obtain ⟨p', hp', rfl⟩ : ∃ p ∈ xI, outSlot p = s' :=
    ⟨slotOutPos s', mem_xI.mpr (inPos_slotOutPos hs'), outSlot_slotOutPos hs'⟩
  have hb := hc p' hp' (v (dsrc (outSlot p'))) j' hj'
  rw [Function.update_eq_self] at hb
  have heq : F ((p, d), j) = F ((p', v (dsrc (outSlot p'))), j') := by
    rw [← hc p hp d j hj, ← hb]
    exact he.symm
  have hne : ((p, d), j) ≠ ((p', v (dsrc (outSlot p'))), j') := by
    intro e
    have e1 : p = p' := congrArg (fun x ↦ x.1.1) e
    have e2 : d = v (dsrc (outSlot p')) := congrArg (fun x ↦ x.1.2) e
    subst e1
    rcases hd with h1 | h1
    · exact h1 rfl
    · exact h1 e2
  have hbI : (p', v (dsrc (outSlot p'))) ∈ sReal v := mem_sReal.mpr ⟨hp', rfl⟩
  have hbR : ∀ T : Finset (ValPos × Digest), (p', v (dsrc (outSlot p'))) ∈ T →
      (((p', v (dsrc (outSlot p'))), j') : (ValPos × Digest) × ℕ) ∈
        (↑(rnds T (sLen w.1)) : Set ((ValPos × Digest) × ℕ)) :=
    fun T hT ↦ Finset.mem_coe.mpr (mem_rnds.mpr ⟨hT, hj'⟩)
  by_cases hdv : d = v (dsrc (outSlot p))
  · exact hne (hI (Finset.mem_coe.mpr (mem_rnds.mpr ⟨mem_sReal.mpr ⟨hp, hdv⟩, hj⟩))
      (hbR _ hbI) heq)
  · exact hne (hV (p, d) (mem_sVirt.mpr ⟨hp, hdv⟩)
      (Finset.mem_coe.mpr (mem_rnds.mpr ⟨Finset.mem_insert_self _ _, hj⟩))
      (hbR _ (Finset.mem_insert_of_mem hbI)) heq)

/-- **A source-bad datum is a source collision.** -/
theorem sColl_of_not_srcGood {w : XW} {h : Z → X} {v : ValPos → Digest}
    (hn : ¬SrcGood w h v) :
    SColl w.2.1 (sBlk w.1 v) (sLen w.1) (sReal v) (sVirt v) h w.2.2.1 w.2.2.2 := by
  by_contra hcon
  have hI : InjAll w.2.1 (sBlk w.1 v) (rnds (sReal v) (sLen w.1)) h w.2.2.1 w.2.2.2 := by
    by_contra h1
    exact hcon (Or.inl h1)
  have hV : ∀ a ∈ sVirt v,
      InjAll w.2.1 (sBlk w.1 v) (rnds (insert a (sReal v)) (sLen w.1)) h w.2.2.1 w.2.2.2 :=
    fun a ha ↦ by
      by_contra h1
      exact hcon (Or.inr ⟨a, ha, h1⟩)
  obtain ⟨hIK, hIR, hIZ⟩ := hI
  apply hn
  refine ⟨?_, ?_, ?_⟩
  · by_contra hK
    rcases not_pairGood_cases (F := famK w.2.1 (sBlk w.1 v) h w.2.2.1 w.2.2.2)
      (fun _ _ _ _ _ ↦ rfl) hK with h1 | ⟨a, ha, h1⟩
    · exact h1 hIK
    · exact h1 (hV a ha).1
  · by_contra hR
    rcases not_pairGood_cases (F := famR w.2.1 (sBlk w.1 v) h w.2.2.1 w.2.2.2)
      (fun _ _ _ _ _ ↦ rfl) hR with h1 | ⟨a, ha, h1⟩
    · exact h1 hIR
    · exact h1 (hV a ha).2.1
  · by_contra hZ
    rcases not_pairGood_cases (F := famZ w.2.1 (sBlk w.1 v) h w.2.2.1 w.2.2.2)
      (fun _ _ _ _ _ ↦ rfl) hZ with h1 | ⟨a, ha, h1⟩
    · exact h1 hIZ
    · exact h1 (hV a ha).2.2

/-! ## The fraction -/

section fraction

variable (W : Type) [Fintype W] [Nonempty W]

/-- The public data and hidden values other than the keys, with the padding `W`. -/
abbrev SQ : Type :=
  PublicParameter × Equiv.Perm (X × Z) × W × (ValPos → Digest)

/-- The public data and hidden values as `(q, (h, k, k'))`. -/
def sEquiv : SQ W × ((Z → X) × (X → Z) × (X → Z)) ≃ (((Z → X) × XW) × W) × (ValPos → Digest) where
  toFun x := (((x.2.1, (x.1.1, x.1.2.1, x.2.2.1, x.2.2.2)), x.1.2.2.1), x.1.2.2.2)
  invFun y := ((y.1.1.2.1, y.1.1.2.2.1, y.1.2, y.2), (y.1.1.1, y.1.1.2.2.2.1, y.1.1.2.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The public data and hidden values as `(π, rest)`. -/
def pxPermEquiv : (((Z → X) × XW) × W) × (ValPos → Digest) ≃
    Equiv.Perm (X × Z) × ((Z → X) × PublicParameter × (X → Z) × (X → Z) × W ×
      (ValPos → Digest)) where
  toFun y := (y.1.1.2.2.1, (y.1.1.1, y.1.1.2.1, y.1.1.2.2.2.1, y.1.1.2.2.2.2, y.1.2, y.2))
  invFun x := (((x.2.1, (x.2.2.1, x.1, x.2.2.2.1, x.2.2.2.2.1)), x.2.2.2.2.2.1), x.2.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

open scoped Classical in
/-- **The source-bad event on good permutations**: `PermGood π G ∧ ¬SrcGood` for at most a
fraction `K / |X| + K (G + 1) / |Z|` of the public data and hidden values,
`K = (8 |xI|)² + |xI| |Digest| · 2 · 8 (8 |xI| + 8)`. -/
theorem srcBad_good_frac_le (G : ℕ) :
    (Fintype.card ((((Z → X) × XW) × W) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
          PermGood y.1.1.2.2.1 G ∧ ¬SrcGood y.1.1.2 y.1.1.1 y.2).card ≤
      ((8 * xI.card * (8 * xI.card) +
          xI.card * Fintype.card Digest * (2 * (8 * (8 * xI.card + 8))) : ℕ) : ℝ≥0∞) /
          Fintype.card X +
        (((8 * xI.card * (8 * xI.card) +
          xI.card * Fintype.card Digest * (2 * (8 * (8 * xI.card + 8)))) * (G + 1) : ℕ) :
            ℝ≥0∞) / Fintype.card Z :=
  frac_srcColl_le (sEquiv W) (fun q ↦ q.2.1) (fun q ↦ sBlk q.1 q.2.2.2) (fun q ↦ sLen q.1)
    (fun q ↦ sReal q.2.2.2) (fun q ↦ sVirt q.2.2.2) (fun q ↦ sBlk_injOn q.1 q.2.2.2) G _ 8 _
    (fun q ↦ card_rnds_sReal_le q.1 q.2.2.2) (fun q w _ ↦ card_rnds_single_le q.1 w)
    (fun q ↦ card_sVirt_le q.2.2.2) _ fun q t hb ↦
      ⟨hb.1, sColl_of_not_srcGood (w := (q.1, q.2.1, t.2.1, t.2.2)) (h := t.1) (v := q.2.2.2)
        hb.2⟩

open scoped Classical in
/-- **The source-bad fraction of leanSPHINCS**: `¬SrcGood` for at most the bad permutations plus
`K / |X| + K (G + 1) / |Z|`. -/
theorem srcBad_frac_le (G : ℕ) :
    (Fintype.card ((((Z → X) × XW) × W) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
          ¬SrcGood y.1.1.2 y.1.1.1 y.2).card ≤
      ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) +
        (((8 * xI.card * (8 * xI.card) +
            xI.card * Fintype.card Digest * (2 * (8 * (8 * xI.card + 8))) : ℕ) : ℝ≥0∞) /
            Fintype.card X +
          (((8 * xI.card * (8 * xI.card) +
            xI.card * Fintype.card Digest * (2 * (8 * (8 * xI.card + 8)))) * (G + 1) : ℕ) :
              ℝ≥0∞) / Fintype.card Z) := by
  set N := Fintype.card ((((Z → X) × XW) × W) × (ValPos → Digest))
  have hsub := card_filter_le_add_of_imp
    (fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦ ¬SrcGood y.1.1.2 y.1.1.1 y.2)
    (fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦ ¬PermGood (pxPermEquiv W y).1 G)
    (fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
      PermGood y.1.1.2.2.1 G ∧ ¬SrcGood y.1.1.2 y.1.1.1 y.2)
    fun y hy ↦ by
      by_cases hG : PermGood y.1.1.2.2.1 G
      · exact Or.inr ⟨hG, hy⟩
      · exact Or.inl hG
  calc (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
        ¬SrcGood y.1.1.2 y.1.1.1 y.2).card
      ≤ (N : ℝ≥0∞)⁻¹ * (((Finset.univ.filter fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
          ¬PermGood (pxPermEquiv W y).1 G).card : ℝ≥0∞) +
        (Finset.univ.filter fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
          PermGood y.1.1.2.2.1 G ∧ ¬SrcGood y.1.1.2 y.1.1.1 y.2).card) := by
        gcongr
        exact_mod_cast hsub
    _ = (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
          ¬PermGood (pxPermEquiv W y).1 G).card +
        (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
          PermGood y.1.1.2.2.1 G ∧ ¬SrcGood y.1.1.2 y.1.1.1 y.2).card := mul_add _ _ _
    _ ≤ _ := by
        rw [inv_card_mul_card_filter_comp_fst (pxPermEquiv W) fun π ↦ ¬PermGood π G]
        exact add_le_add le_rfl (srcBad_good_frac_le W G)

end fraction

/-! ## At Keccak's sizes -/

set_option exponentiation.threshold 4096 in
/-- The source-collision terms at Keccak's sizes, for `n ≤ 2^47` outputs and `G = 18`:
`K ≤ 2^230`. -/
theorem srcCollTerms_le {n cD cX cZ : ℕ} (hn : n ≤ 2 ^ 47) (hD : cD = 2 ^ 128)
    (hX : cX = 2 ^ 1088) (hZ : cZ = 2 ^ 512) :
    ((8 * n * (8 * n) + n * cD * (2 * (8 * (8 * n + 8))) : ℕ) : ℝ≥0∞) / cX +
        (((8 * n * (8 * n) + n * cD * (2 * (8 * (8 * n + 8)))) * (18 + 1) : ℕ) : ℝ≥0∞) / cZ ≤
      ENNReal.ofReal (2 ^ 230 / 2 ^ 1088 + 2 ^ 230 * 19 / 2 ^ 512) := by
  subst hD hX hZ
  have hK : 8 * n * (8 * n) + n * 2 ^ 128 * (2 * (8 * (8 * n + 8))) ≤ 2 ^ 230 :=
    calc 8 * n * (8 * n) + n * 2 ^ 128 * (2 * (8 * (8 * n + 8)))
        ≤ 8 * 2 ^ 47 * (8 * 2 ^ 47) + 2 ^ 47 * 2 ^ 128 * (2 * (8 * (8 * 2 ^ 47 + 8))) := by
          gcongr
      _ ≤ 2 ^ 230 := by norm_num
  have hK' : (8 * n * (8 * n) + n * 2 ^ 128 * (2 * (8 * (8 * n + 8)))) * (18 + 1) ≤
      2 ^ 230 * 19 :=
    (Nat.mul_le_mul_right _ hK).trans_eq (by norm_num)
  rw [natCast_div_eq_ofReal _ (2 ^ 1088) (by positivity),
    natCast_div_eq_ofReal _ (2 ^ 512) (by positivity),
    ← ENNReal.ofReal_add (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  apply ENNReal.ofReal_le_ofReal
  have hb : ((8 * n * (8 * n) + n * 2 ^ 128 * (2 * (8 * (8 * n + 8))) : ℕ) : ℝ) /
      ((2 ^ 1088 : ℕ) : ℝ) ≤ 2 ^ 230 / 2 ^ 1088 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hK) (by positivity)
  have hc : (((8 * n * (8 * n) + n * 2 ^ 128 * (2 * (8 * (8 * n + 8)))) * (18 + 1) : ℕ) : ℝ) /
      ((2 ^ 512 : ℕ) : ℝ) ≤ 2 ^ 230 * 19 / 2 ^ 512 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hK') (by positivity)
  exact add_le_add hb hc

set_option exponentiation.threshold 4096 in
open scoped Classical in
/-- **The source-bad fraction at Keccak's sizes**: at most `2^-277` (with `G = 18`: the bad
permutations `2^-777`, the source collisions `19 · 2^230 / 2^512 + 2^230 / 2^1088`, from
`|xI| ≤ 2^47` and `2^128` source values). -/
theorem srcBad_frac_le_keccak (W : Type) [Fintype W] [Nonempty W] :
    (Fintype.card ((((Z → X) × XW) × W) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
          ¬SrcGood y.1.1.2 y.1.1.1 y.2).card ≤
      ENNReal.ofReal (1 / 2 ^ 277) := by
  refine ((srcBad_frac_le W 18).trans (add_le_add permTerm_le_keccak
    (srcCollTerms_le card_xI_le card_digest rnCard_X rnCard_Z))).trans ?_
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 777) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

end Quantum.Sphincs.Assembly

end
