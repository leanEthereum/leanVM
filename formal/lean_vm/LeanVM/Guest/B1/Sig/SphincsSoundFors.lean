/-
  LeanVM.Guest.B1.Sig.SphincsSoundFors

  The FORS block of `verify_sig_lean_sphincs` (`sp_fors_tree`, `lean_ethereum.py`, and
  `T_k`, `lean_ethereum.py`) is sound: whatever secrets and children
  are hinted, each tree's root is the fold of its hinted secret and siblings, and the FORS key their
  `T_k`.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsSoundPath

/-!
# FORS, sound

Tree `c` (`c < 24`) at the leaf `s < 2^10`, `A1` the trees' address cell (`fors_at`):

* `fAdrE A1 c z s`: the address of the node at height `z` on the leaf's path, its index across the
  trees `2^(10-z) c + s >> z`; `sForsAt_sound`: `sp_fors_at` computes it;
* `fLeafE`, `fNodeE`, `fRootE`: the leaf hashed from the secret, a node from its children, the
  root;
* `forsLevelWidth`, `sForsSib`: a level's width and the hinted siblings; `forsLeafWidth`,
  `forsTreeBase b0 c`: tree `c`'s base in the block from `b0` (its secret's cell);
* `sForsLevels_sound`, `sForsTree_sound`, `sForsTrees_sound`: the levels, a tree, the trees;
* `sForsBlock_sound`: the FORS key, `T_k` of `P`, `A0`, `key + FORS_ROOTS` and the roots.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

/-! ## Addresses -/

/-- Tree `c`'s node at height `z` on the path of leaf `s`: its index across the trees. -/
def fIdx (c z s : Nat) : Nat := 2 ^ (10 - z) * c + s >>> z

/-- The address of tree `c`'s node at height `z` on the path of leaf `s`, `A1` the trees'. -/
def fAdrE (A1 : E) (c z s : Nat) : E := A1 + word 0 (a1Hi z (fIdx c z s))

theorem fIdx_lt {c z s : Nat} (hc : c < 24) (hz : z ≤ 10) (hs : s < 2 ^ 10) :
    fIdx c z s < 2 ^ 16 := by
  have h1 : s >>> z < 2 ^ (10 - z) := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rw [← pow_add, show z + (10 - z) = 10 by omega]; exact hs)
  have h2 : 2 ^ (10 - z) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold fIdx
  have : 2 ^ (10 - z) * c + 2 ^ (10 - z) ≤ 2 ^ 10 * 24 := by
    calc 2 ^ (10 - z) * c + 2 ^ (10 - z) = 2 ^ (10 - z) * (c + 1) := by ring
      _ ≤ 2 ^ 10 * 24 := Nat.mul_le_mul h2 (by omega)
  omega

theorem a1Hi_lt {h i : Nat} (hh : h < 2 ^ 8) (hi : i < 2 ^ 16) : a1Hi h i < 2 ^ 64 := by
  unfold a1Hi
  omega

/-- A FORS level's width: its children, `is_child`'s two, the address (`sp_fors_at` at height
`z + 1`, `forsAtW`) and the node. -/
def forsLevelWidth (c z : Nat) : Nat := forsLevelW c z

/-- A FORS tree's leaf part's width: its secret, its leaf's address (six values, the place in
`vals`) and the leaf's hash. -/
def forsLeafWidth (_c : Nat) : Nat := 9

/-- Tree `c`'s base in the FORS block from `b0`: its secret's cell. -/
def forsTreeBase (b0 c : Nat) : Nat := b0 + 2 + ((List.range c).map forsTreeW).sum

/-- Tree `c`'s root in the FORS block from `b0`. -/
def forsRootPos (b0 c : Nat) : Nat := forsTreeBase b0 c + forsTreeW c - 1

/-- The hinted sibling of level `j` of `sForsLevels … c m z cur x` (`0` outside its levels). -/
def sForsSib (σ : Val) (bit : Nat → V) (c : Nat) : Nat → Nat → Nat → Nat → E
  | 0, _, _, _ => 0
  | m + 1, z, x, j => if j = z then siblingOf σ (bit (10 * c + z)) x
      else sForsSib σ bit c m (z + 1) (x + forsLevelWidth c z) j

/-- **Tree `c`'s siblings** in the FORS block from `b0`, level by level. -/
def forsSib (σ : Val) (bit : Nat → V) (b0 c : Nat) : Nat → E :=
  sForsSib σ bit c 10 0 (forsTreeBase b0 c + forsLeafWidth c)

/-- Tree `c`'s leaf hashed from its secret. -/
def fLeafE (pp a0 A1 : E) (c s : Nat) (secret : E) : E := (hcell [pp, a0, fAdrE A1 c 0 s, secret]).1

/-- Tree `c`'s node at height `z + 1` from the one at `z`, its sibling `sib z`. -/
def fNodeE (pp a0 A1 : E) (c s : Nat) (sib : Nat → E) (z : Nat) (v : E) : E :=
  (hcell [pp, a0, fAdrE A1 c (z + 1) s, (mPair (s.testBit z) v (sib z)).1,
    (mPair (s.testBit z) v (sib z)).2]).1

/-- **Tree `c`'s root**: the leaf climbed ten levels. -/
def fRootE (pp a0 A1 : E) (c s : Nat) (secret : E) (sib : Nat → E) : E :=
  pFold (fNodeE pp a0 A1 c s sib) 10 (fLeafE pp a0 A1 c s secret)

variable {rd : Reader} {σ : Val}

/-- `a + const(w)`, sound: `w` added (nothing for `k = 0`, where `w` is `0`). -/
theorem sAddK_sound {a : V} {k : Nat} {w : E} {x : Nat} (hw : k = 0 → w = 0)
    (h : AtomsHold rd σ (sAddK a k w x).1) : σ (sAddK a k w x).2.2 = σ a + w := by
  unfold sAddK at h ⊢
  by_cases h0 : k = 0
  · simp only [h0, ↓reduceIte]
    rw [hw h0, add_zero]
  · simp only [h0, ↓reduceIte] at h ⊢
    have c0 : σ (.n x) = w := h.atom (a := .const _ _) (by simp [cst])
    have a1' : σ (.n (x + 1)) = σ a + σ (.n x) := h.atom (a := .add _ _ _) (by simp [addS])
    rw [a1', c0]

theorem sAddK_next (a : V) (k : Nat) (w : E) (x : Nat) :
    (sAddK a k w x).2.1 = x + (if k = 0 then 0 else 2) := by
  unfold sAddK; split <;> rfl

/-- The height's constant: `z · 2^88`, the height at bit `24` of limb `1`. -/
theorem lit_height (z : Nat) (hz : z < 2 ^ 8) : lit (2 ^ 88 * z) = word 0 (a1Hi z 0) := by
  rw [show 2 ^ 88 * z = 2 ^ 64 * (2 ^ 24 * z) by ring, lit_hi (by omega)]
  simp [a1Hi]

open scoped Dec in
theorem forsHiW_eq_aux : ∀ k < 24, forsHiW k = eOfNat k * be16HiW := by
  intro k hk
  rw [forsHiW, be16HiW, mul_comm, eOfNat, word, word, ofLimbs_mul_ofK, ofLimbs_inj]
  revert k
  decide +kernel

/-- `sp_fors_at`'s high byte: `const(k) · (g^8 · 2^120 + 2^112)`. -/
theorem forsHiW_eq {k : Nat} (hk : k < 24) : forsHiW k = eOfNat k * be16HiW := forsHiW_eq_aux k hk

theorem fIdx_div {c z s : Nat} (hz : 2 ≤ z) (hz10 : z ≤ 10) (hs : s < 2 ^ 10) :
    fIdx c z s / 256 = c / 2 ^ (z - 2) := by
  have hr : s >>> z < 2 ^ (10 - z) := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rw [← pow_add, show z + (10 - z) = 10 by omega]; exact hs)
  have h256 : (256 : Nat) = 2 ^ (10 - z) * 2 ^ (z - 2) := by
    rw [← pow_add, show 10 - z + (z - 2) = 8 by omega]; norm_num
  unfold fIdx
  rw [h256, ← Nat.div_div_eq_div_mul, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hr,
    Nat.add_zero]

theorem fIdx_shift8 {c z s : Nat} (hz : z ≤ 2) :
    fIdx c (z + 8) s = fIdx c z s / 256 := by
  unfold fIdx
  rw [show 2 ^ (10 - z) * c = 256 * (2 ^ (10 - (z + 8)) * c) by
      rw [← mul_assoc, show (256 : Nat) = 2 ^ 8 from rfl, ← pow_add]; congr 2; omega,
    Nat.mul_add_div (by norm_num), Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (s >>> z) 8]

/-- **`sp_fors_at`, sound**: tree `c`'s node at height `z` on the path of the leaf `s`, its shifts
with the tree's place `val (10 c + j)`. -/
theorem sForsAt_sound {a1 : V} {val : Nat → V} {c z x s : Nat} (hc : c < 24) (hz : z ≤ 10)
    (hs : s < 2 ^ 10) (hval : ∀ j < 10, σ (val (10 * c + j)) = eOfNat (fIdx c j s))
    (h : AtomsHold rd σ (sForsAt a1 val c z x).1) :
    σ (sForsAt a1 val c z x).2.2 = fAdrE (σ a1) c z s := by
  have hI := fIdx_lt hc hz hs
  have hz0 : z = 0 → lit (2 ^ 88 * z) = 0 := fun h0 => by
    rw [h0, Nat.mul_zero]; simp [lit, word_zero]
  by_cases hz10 : z = 10
  · subst hz10
    simp only [sForsAt, ↓reduceIte] at h ⊢
    have h1 := sAddK_sound (rd := rd) (σ := σ) (fun h0 => absurd h0 (by norm_num)) h.left
    have h2 := sAddK_sound (rd := rd) (σ := σ) (k := c) (w := lit (2 ^ 120 * c)) (fun h0 => by
      rw [h0, Nat.mul_zero]; simp [lit, word_zero]) h.right
    rw [h2, h1, fAdrE, lit_height 10 (by norm_num), add_assoc, show 2 ^ 120 * c = 2 ^ 64 * (2 ^ 56 * c)
      by ring, lit_hi (by omega), word_add_word, Nat.xor_zero]
    have hf : fIdx c 10 s = c := by
      have : s >>> 10 = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hs
      simp [fIdx, this]
    rw [hf]
    congr 2
    unfold a1Hi
    rw [Nat.div_eq_of_lt (by omega : c < 256), Nat.mod_eq_of_lt (by omega : c < 256)]
    simp only [Nat.zero_div, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
    rw [Nat.xor_comm, two_pow_mul_xor (by omega)]
    ring
  · by_cases hz2 : z / 2 = 0
    · simp only [sForsAt, hz10, hz2, ↓reduceIte] at h ⊢
      have h1 := sAddK_sound (rd := rd) (σ := σ) hz0 h.left.left
      have hbe := sBe16_sound (rd := rd) (n := 16) (v := fIdx c z s) (le_refl _) hI
        (hval z (by omega))
        (fun _ => by
          rw [show 10 * c + z + 8 = 10 * c + (z + 8) by omega, hval (z + 8) (by omega),
            fIdx_shift8 (by omega)])
        h.left.right
      have ha : σ (.n (sBe16 val (10 * c + z) 16 (sAddK a1 z (lit (2 ^ 88 * z)) x).2.1).2.1) =
          σ (sAddK a1 z (lit (2 ^ 88 * z)) x).2.2 +
            σ (sBe16 val (10 * c + z) 16 (sAddK a1 z (lit (2 ^ 88 * z)) x).2.1).2.2 :=
        h.right.atom (a := .add _ _ _) (by simp [addS])
      rw [ha, h1, hbe, lit_height z (by omega), add_assoc, word_add_word, Nat.xor_self,
        a1Hi_xor (by omega) (by norm_num) hI, Nat.zero_xor, fAdrE]
    · simp only [sForsAt, hz10, hz2, ↓reduceIte] at h ⊢
      have hK : c / 2 ^ (z - 2) < 24 := lt_of_le_of_lt (Nat.div_le_self _ _) hc
      have h1 := sAddK_sound (rd := rd) (σ := σ) hz0 h.left.left.left
      have h2 := sAddK_sound (rd := rd) (σ := σ) (k := c / 2 ^ (z - 2))
        (w := forsHiW (c / 2 ^ (z - 2))) (fun h0 => by
          rw [h0, forsHiW_eq (by norm_num), Value.eOfNat_zero, zero_mul]) h.left.left.right
      set x2 := (sAddK (sAddK a1 z (lit (2 ^ 88 * z)) x).2.2 (c / 2 ^ (z - 2))
        (forsHiW (c / 2 ^ (z - 2))) (sAddK a1 z (lit (2 ^ 88 * z)) x).2.1).2.1 with hx2
      have hB := h.left.right
      simp only [sBe16, show ¬ (8 + 7) / 8 = 2 by norm_num, ↓reduceIte] at hB ⊢
      have c0 : σ (.n x2) = lit (2 ^ 120) := hB.atom (a := .const (.n x2) _) (by simp [cst])
      have m1 : σ (.n (x2 + 1)) = σ (val (10 * c + z)) * σ (.n x2) :=
        hB.atom (a := .mul (.n (x2 + 1)) _ _) (by simp [mulS])
      have ha : σ (.n (x2 + 2)) = σ (sAddK (sAddK a1 z (lit (2 ^ 88 * z)) x).2.2 (c / 2 ^ (z - 2))
          (forsHiW (c / 2 ^ (z - 2))) (sAddK a1 z (lit (2 ^ 88 * z)) x).2.1).2.2 +
            σ (.n (x2 + 1)) :=
        h.right.atom (a := .add _ _ _) (by simp [addS, sBe16])
      rw [ha, h2, h1, m1, c0, hval z (by omega), forsHiW_eq hK, ← fIdx_div (by omega) hz hs,
        add_assoc, add_assoc, add_comm (eOfNat (fIdx c z s / 256) * be16HiW), be16_split hI,
        lit_height z (by omega), word_add_word, Nat.xor_self, a1Hi_xor (by omega) (by norm_num) hI,
        Nat.zero_xor, fAdrE]

/-- The values `sp_fors_at` takes. -/
theorem sForsAt_width (a1 : V) (val : Nat → V) (c z x : Nat) (hz : z ≤ 10) :
    (sForsAt a1 val c z x).2.1 = x + forsAtW c z := by
  unfold sForsAt forsAtW
  by_cases hz10 : z = 10
  · subst hz10
    by_cases hc0 : c = 0 <;> simp [sAddK_next, hc0]
  · by_cases hz2 : z / 2 = 0
    · by_cases hz0 : z = 0 <;> simp [hz10, hz2, sAddK_next, sBe16_next, hz0]
    · have hz0 : z ≠ 0 := by omega
      by_cases hk : c / 2 ^ (z - 2) = 0 <;> simp [hz10, hz2, sAddK_next, sBe16_next, hz0, hk]

/-- The address part of FORS level `z` ends `forsLevelWidth c z - 5` after its base. -/
theorem sForsAt_next (a1 : V) (val : Nat → V) (c z x : Nat) (hz : z ≤ 9) :
    (sForsAt a1 val c (z + 1) (x + 4)).2.1 = x + forsLevelWidth c z - 5 := by
  rw [sForsAt_width a1 val c (z + 1) (x + 4) (by omega), forsLevelWidth, forsLevelW]
  omega

theorem sForsLevel_eq (pad : Nat) (pp a0 a1 : V) (bit val : Nat → V) (c z : Nat) (cur : V)
    (x : Nat) : sForsLevel pad pp a0 a1 bit val c z cur x =
      ([hintW "sp_fors_nodes" [.n x, .n (x + 1)]] ++
        isChildS cur (.n x) (.n (x + 1)) (bit (10 * c + z)) (x + 2) ++
        (sForsAt a1 val c (z + 1) (x + 4)).1 ++
        (kNode pad pp a0 (sForsAt a1 val c (z + 1) (x + 4)).2.2 (.n x) (.n (x + 1))
          (sForsAt a1 val c (z + 1) (x + 4)).2.1).1,
        (sForsAt a1 val c (z + 1) (x + 4)).2.1 + 5,
        .n ((sForsAt a1 val c (z + 1) (x + 4)).2.1 + 4)) := by
  simp only [sForsLevel, (kNode_shape ..).1, (kNode_shape ..).2]

theorem sForsLevels_succ (pad : Nat) (pp a0 a1 : V) (bit val : Nat → V) (c m z : Nat) (cur : V)
    (x : Nat) : sForsLevels pad pp a0 a1 bit val c (m + 1) z cur x =
      ((sForsLevel pad pp a0 a1 bit val c z cur x).1 ++
        (sForsLevels pad pp a0 a1 bit val c m (z + 1)
          (.n ((sForsAt a1 val c (z + 1) (x + 4)).2.1 + 4))
          ((sForsAt a1 val c (z + 1) (x + 4)).2.1 + 5)).1,
        (sForsLevels pad pp a0 a1 bit val c m (z + 1)
          (.n ((sForsAt a1 val c (z + 1) (x + 4)).2.1 + 4))
          ((sForsAt a1 val c (z + 1) (x + 4)).2.1 + 5)).2.1,
        (sForsLevels pad pp a0 a1 bit val c m (z + 1)
          (.n ((sForsAt a1 val c (z + 1) (x + 4)).2.1 + 4))
          ((sForsAt a1 val c (z + 1) (x + 4)).2.1 + 5)).2.2) := by
  rw [sForsLevels, sForsLevel_eq]

/-- **A FORS tree's levels, sound**: from level `z` (base `x`), `m` levels up to `10`, the node
reached is `nIter` of `fNodeE`, the siblings those hinted (`sForsSib`). -/
theorem sForsLevels_sound {pad : Nat} (hp : PadOK σ pad) {pp a0 a1 : V} {bit val : Nat → V}
    {c s : Nat} (hc : c < 24) (hs : s < 2 ^ 10)
    (hbit : ∀ z < 10, σ (bit (10 * c + z)) = if s.testBit z then 1 else 0)
    (hval : ∀ j < 10, σ (val (10 * c + j)) = eOfNat (fIdx c j s)) :
    ∀ (m z : Nat) (cur : V) (x : Nat), z + m ≤ 10 →
      AtomsHold rd σ (sForsLevels pad pp a0 a1 bit val c m z cur x).1 →
      σ (sForsLevels pad pp a0 a1 bit val c m z cur x).2.2 =
        nIter (fNodeE (σ pp) (σ a0) (σ a1) c s (sForsSib σ bit c m z x)) z m (σ cur)
  | 0, _, _, _, _, _ => rfl
  | m + 1, z, cur, x, hm, hA => by
      rw [sForsLevels_succ] at hA ⊢
      have hL : AtomsHold rd σ (sForsLevel pad pp a0 a1 bit val c z cur x).1 := hA.left
      rw [sForsLevel_eq] at hL
      obtain ⟨hib, hd⟩ := bit_facts (hbit z (by omega))
      have hadr := sForsAt_sound (a1 := a1) (x := x + 4) hc (by omega) hs hval hL.left.right
      have hc' : AtomsHold rd σ (isChildS cur (.n x) (.n (x + 1)) (bit (10 * c + z)) (x + 2)) :=
        hL.left.left.sub fun t ht => List.mem_append_right _ ht
      have hlv := level_sound hp hib hc' hL.right
      have hnext := sForsAt_next a1 val c z x (by omega)
      have hrest := sForsLevels_sound hp hc hs hbit hval m (z + 1) _ _ (by omega) hA.right
      rw [hrest, nIter]
      have hfirst : σ (.n ((sForsAt a1 val c (z + 1) (x + 4)).2.1 + 4)) =
          fNodeE (σ pp) (σ a0) (σ a1) c s (sForsSib σ bit c (m + 1) z x) z (σ cur) := by
        rw [hlv, hd, hadr]
        simp [fNodeE, sForsSib]
      rw [hfirst, hnext, show x + forsLevelWidth c z - 5 + 5 = x + forsLevelWidth c z by
        unfold forsLevelWidth forsLevelW; omega]
      refine nIter_congr _ _ _ fun j hj => ?_
      unfold fNodeE
      simp only [sForsSib, show j ≠ z by omega, ite_false]

theorem forsLevels_shape (pad : Nat) (pp a0 a1 : V) (bit val : Nat → V) (c : Nat) :
    ∀ (m z : Nat) (cur : V) (x : Nat), z + m ≤ 10 →
      (sForsLevels pad pp a0 a1 bit val c m z cur x).2.1 =
        x + ∑ j ∈ Finset.range m, forsLevelWidth c (z + j)
  | 0, _, _, _, _ => by simp [sForsLevels]
  | m + 1, z, cur, x, hm => by
      rw [sForsLevels_succ, forsLevels_shape pad pp a0 a1 bit val c m (z + 1) _ _ (by omega),
        sForsAt_next a1 val c z x (by omega), Finset.sum_range_succ']
      have e : ∀ j ∈ Finset.range m, forsLevelWidth c (z + 1 + j) = forsLevelWidth c (z + (j + 1)) :=
        fun j _ => by rw [show z + 1 + j = z + (j + 1) by omega]
      rw [Finset.sum_congr rfl e]
      simp only [Nat.add_zero]
      have : x + forsLevelWidth c z - 5 + 5 = x + forsLevelWidth c z := by
        unfold forsLevelWidth forsLevelW; omega
      omega

theorem forsLevels_out (pad : Nat) (pp a0 a1 : V) (bit val : Nat → V) (c : Nat) :
    ∀ (m z : Nat) (cur : V) (x : Nat), z + m ≤ 9 →
      (sForsLevels pad pp a0 a1 bit val c (m + 1) z cur x).2.2 =
        .n ((sForsLevels pad pp a0 a1 bit val c (m + 1) z cur x).2.1 - 1)
  | 0, z, cur, x, _ => by
      rw [sForsLevels_succ]
      simp only [sForsLevels]
      congr 1
  | m + 1, z, cur, x, hm => by
      rw [sForsLevels_succ]
      exact forsLevels_out pad pp a0 a1 bit val c m (z + 1) _ _ (by omega)

theorem forsLevelWidth_sum (c : Nat) :
    ∑ j ∈ Finset.range 10, forsLevelWidth c (0 + j) = forsTreeW c - 9 := by
  simp only [Nat.zero_add, forsLevelWidth, forsTreeW, Finset.sum_range_succ, Finset.sum_range_zero,
    List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil]
  omega

theorem sForsAt_leaf_next (a1 : V) (val : Nat → V) (c b : Nat) :
    (sForsAt a1 val c 0 (b + 1)).2.1 = b + forsLeafWidth c - 2 := by
  rw [sForsAt_width a1 val c 0 (b + 1) (by norm_num)]
  simp [forsAtW, forsLeafWidth]

/-- **FORS tree `c` from base `b`, sound**: at the leaf `s`, its root is `fRootE` of the hinted
secret (at `b`) and siblings. -/
theorem sForsTree_sound {pad : Nat} (hp : PadOK σ pad) {pp a0 a1 : V} {bit val : Nat → V}
    {c s b : Nat} (hc : c < 24) (hs : s < 2 ^ 10)
    (hbit : ∀ z < 10, σ (bit (10 * c + z)) = if s.testBit z then 1 else 0)
    (hval : ∀ j < 10, σ (val (10 * c + j)) = eOfNat (fIdx c j s))
    (h : AtomsHold rd σ (sForsTree pad pp a0 a1 bit val c b).1) :
    σ (sForsTree pad pp a0 a1 bit val c b).2.2 =
      fRootE (σ pp) (σ a0) (σ a1) c s (σ (.n b)) (sForsSib σ bit c 10 0 (b + forsLeafWidth c)) := by
  simp only [sForsTree] at h ⊢
  have hy := sForsAt_leaf_next a1 val c b
  have hadr := sForsAt_sound (a1 := a1) (x := b + 1) hc (by norm_num) hs hval h.left.left.right
  have hk := k64_sound hp h.left.right
  have hlv := sForsLevels_sound hp hc hs hbit hval 10 0 _ _ (by norm_num) h.right
  rw [hlv, nIter_zero, fRootE, hk, hadr,
    show (sForsAt a1 val c 0 (b + 1)).2.1 + 2 = b + forsLeafWidth c by
      rw [hy]; unfold forsLeafWidth; omega]
  rfl

theorem forsTreeW_ge (c : Nat) : 9 + 1 ≤ forsTreeW c := by
  unfold forsTreeW
  have : 1 ≤ ((List.range 10).map (forsLevelW c)).sum := by
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons]
    have : 9 ≤ forsLevelW c 0 := by unfold forsLevelW; omega
    omega
  omega

theorem sForsTree_shape (pad : Nat) (pp a0 a1 : V) (bit val : Nat → V) (c b : Nat) :
    (sForsTree pad pp a0 a1 bit val c b).2.1 = b + forsTreeW c ∧
      (sForsTree pad pp a0 a1 bit val c b).2.2 = .n (b + forsTreeW c - 1) := by
  have hW : 9 + 1 ≤ forsTreeW c := forsTreeW_ge c
  have hy := sForsAt_leaf_next a1 val c b
  have hw : (sForsAt a1 val c 0 (b + 1)).2.1 + 2 = b + forsLeafWidth c := by
    rw [hy]; unfold forsLeafWidth; omega
  have h1 := forsLevels_shape pad pp a0 a1 bit val c 10 0
    (.n ((sForsAt a1 val c 0 (b + 1)).2.1 + 1)) ((sForsAt a1 val c 0 (b + 1)).2.1 + 2)
    (by norm_num)
  rw [forsLevelWidth_sum c] at h1
  have h2 : (sForsLevels pad pp a0 a1 bit val c 10 0 (.n ((sForsAt a1 val c 0 (b + 1)).2.1 + 1))
      ((sForsAt a1 val c 0 (b + 1)).2.1 + 2)).2.2 =
      .n ((sForsLevels pad pp a0 a1 bit val c 10 0 (.n ((sForsAt a1 val c 0 (b + 1)).2.1 + 1))
        ((sForsAt a1 val c 0 (b + 1)).2.1 + 2)).2.1 - 1) :=
    forsLevels_out pad pp a0 a1 bit val c 9 0 _ _ (by norm_num)
  rw [h1] at h2
  unfold forsLeafWidth at hw
  have e1 : (sForsAt a1 val c 0 (b + 1)).2.1 + 2 + (forsTreeW c - 9) = b + forsTreeW c := by omega
  rw [e1] at h1 h2
  exact ⟨h1, h2⟩

theorem forsTreeBase_succ (b0 c : Nat) :
    forsTreeBase b0 (c + 1) = forsTreeBase b0 c + forsTreeW c := by
  simp [forsTreeBase, List.range_succ, Nat.add_assoc]

theorem sForsTrees_succ (pad : Nat) (pp a0 a1 : V) (bit val : Nat → V) (m c b : Nat) :
    sForsTrees pad pp a0 a1 bit val (m + 1) c b =
      ((sForsTree pad pp a0 a1 bit val c b).1 ++
          (sForsTrees pad pp a0 a1 bit val m (c + 1) (sForsTree pad pp a0 a1 bit val c b).2.1).1,
        (sForsTrees pad pp a0 a1 bit val m (c + 1) (sForsTree pad pp a0 a1 bit val c b).2.1).2.1,
        (sForsTree pad pp a0 a1 bit val c b).2.2 ::
          (sForsTrees pad pp a0 a1 bit val m (c + 1)
            (sForsTree pad pp a0 a1 bit val c b).2.1).2.2) :=
  rfl

/-- The trees' next base and roots. -/
theorem sForsTrees_shape (pad : Nat) (pp a0 a1 : V) (bit val : Nat → V) (b0 : Nat) :
    ∀ (m c : Nat), (sForsTrees pad pp a0 a1 bit val m c (forsTreeBase b0 c)).2.1 =
        forsTreeBase b0 (c + m) ∧
      (sForsTrees pad pp a0 a1 bit val m c (forsTreeBase b0 c)).2.2 =
        (List.range m).map fun k => V.n (forsRootPos b0 (c + k))
  | 0, c => by simp [sForsTrees]
  | m + 1, c => by
      rw [sForsTrees_succ]
      obtain ⟨t1, t2⟩ := sForsTree_shape pad pp a0 a1 bit val c (forsTreeBase b0 c)
      rw [t1, ← forsTreeBase_succ]
      obtain ⟨r1, r2⟩ := sForsTrees_shape pad pp a0 a1 bit val b0 m (c + 1)
      rw [r1, r2, t2, List.range_succ_eq_map, List.map_cons, List.map_map]
      refine ⟨by rw [show c + 1 + m = c + (m + 1) by omega], ?_⟩
      simp only [Nat.add_zero, forsRootPos, Function.comp_def,
        show ∀ k, c + 1 + k = c + (k + 1) from fun k => by omega]

/-- **The FORS trees, sound**: `m` trees from tree `c` at its base, tree `c + k`'s root is `fRootE`
of its hinted secret and siblings. -/
theorem sForsTrees_sound {pad : Nat} (hp : PadOK σ pad) {pp a0 a1 : V} {bit val : Nat → V}
    {b0 : Nat} {s : Nat → Nat} (hs : ∀ c < 24, s c < 2 ^ 10)
    (hbit : ∀ c < 24, ∀ z < 10, σ (bit (10 * c + z)) = if (s c).testBit z then 1 else 0)
    (hval : ∀ c < 24, ∀ j < 10, σ (val (10 * c + j)) = eOfNat (fIdx c j (s c))) :
    ∀ (m c : Nat), c + m ≤ 24 →
      AtomsHold rd σ (sForsTrees pad pp a0 a1 bit val m c (forsTreeBase b0 c)).1 → ∀ k < m,
        σ (.n (forsRootPos b0 (c + k))) = fRootE (σ pp) (σ a0) (σ a1) (c + k) (s (c + k))
          (σ (.n (forsTreeBase b0 (c + k)))) (forsSib σ bit b0 (c + k))
  | 0, _, _, _, k, hk => absurd hk (by omega)
  | m + 1, c, hcm, hA, k, hk => by
      rw [sForsTrees_succ] at hA
      rcases k with _ | k
      · have := sForsTree_sound hp (by omega) (hs c (by omega)) (hbit c (by omega))
          (hval c (by omega)) hA.left
        rw [(sForsTree_shape pad pp a0 a1 bit val c (forsTreeBase b0 c)).2] at this
        simpa [forsRootPos, forsSib] using this
      · have hR := hA.right
        rw [(sForsTree_shape pad pp a0 a1 bit val c (forsTreeBase b0 c)).1, ← forsTreeBase_succ]
          at hR
        have := sForsTrees_sound hp hs hbit hval m (c + 1) (by omega) hR k (by omega)
        rwa [show c + 1 + k = c + (k + 1) by omega] at this

theorem sForsBlock_eq (pad : Nat) (pp a0 key : V) (bit val : Nat → V) (b0 : Nat) :
    sForsBlock pad pp a0 key bit val b0 =
      ([cst b0 (lit (3 * 2 ^ 24)), addS (.n (b0 + 1)) key (.n b0)] ++
          (sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).1 ++
          [cst (sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.1 (lit (4 * 2 ^ 24)),
            addS (.n ((sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.1 + 1)) key
              (.n (sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.1)] ++
          (kMsg pad (([pp, a0,
            .n ((sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.1 + 1)]
            ++ (sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.2).map KC.cell) 432
            true none ((sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.1 + 2)).1,
        (kMsg pad (([pp, a0,
            .n ((sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.1 + 1)]
            ++ (sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.2).map KC.cell) 432
            true none ((sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.1 + 2)).2.1,
        (kMsg pad (([pp, a0,
            .n ((sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.1 + 1)]
            ++ (sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.2).map KC.cell) 432
            true none ((sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.1 + 2)).2.2) :=
  rfl

/-- **The FORS block, sound**: at the leaves `s c`, the FORS key (`fors_pk`) is `T_k` of `P`, `A0`,
`key + FORS_ROOTS` and the trees' roots, the trees' `A1` being `key + FORS_TREE`. -/
theorem sForsBlock_sound {pad : Nat} (hp : PadOK σ pad) {pp a0 key : V} {bit val : Nat → V}
    {b0 : Nat} {s : Nat → Nat} (hs : ∀ c < 24, s c < 2 ^ 10)
    (hbit : ∀ c < 24, ∀ z < 10, σ (bit (10 * c + z)) = if (s c).testBit z then 1 else 0)
    (hval : ∀ c < 24, ∀ j < 10, σ (val (10 * c + j)) = eOfNat (fIdx c j (s c)))
    (h : AtomsHold rd σ (sForsBlock pad pp a0 key bit val b0).1) :
    σ (.n (sForsBlock pad pp a0 key bit val b0).2.2) =
      (hcell ([σ pp, σ a0, σ key + lit (4 * 2 ^ 24)] ++ (List.range 24).map fun c =>
        fRootE (σ pp) (σ a0) (σ key + lit (3 * 2 ^ 24)) c (s c) (σ (.n (forsTreeBase b0 c)))
          (forsSib σ bit b0 c))).1 := by
  obtain ⟨t1, t2⟩ := sForsTrees_shape pad pp a0 (.n (b0 + 1)) bit val b0 24 0
  have e0 : forsTreeBase b0 0 = b0 + 2 := by simp [forsTreeBase]
  have e24 : forsTreeBase b0 (0 + 24) = b0 + 3802 := by
    have : ((List.range 24).map forsTreeW).sum = 3800 := by decide +kernel
    simp only [forsTreeBase, Nat.zero_add, this]
  rw [e0, e24] at t1
  rw [e0] at t2
  have hT := sForsTrees_sound (rd := rd) hp hs hbit hval (pp := pp) (a0 := a0) (a1 := .n (b0 + 1))
    (b0 := b0) 24 0 (by norm_num)
  rw [e0] at hT
  rw [sForsBlock_eq] at h ⊢
  have hT' := hT h.left.left.right
  generalize sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2) = tr at h ⊢ t1 t2
  rw [t1, t2] at h ⊢
  have ha0 : σ (.n b0) = lit (3 * 2 ^ 24) := h.atom (a := .const (.n b0) _) (by simp [cst])
  have ha1 : σ (.n (b0 + 1)) = σ key + σ (.n b0) :=
    h.atom (a := .add (.n (b0 + 1)) _ _) (by simp [addS])
  have hr0 : σ (.n (b0 + 3802)) = lit (4 * 2 ^ 24) :=
    h.atom (a := .const (.n (b0 + 3802)) _) (by simp [cst])
  have hr1 : σ (.n (b0 + 3802 + 1)) = σ key + σ (.n (b0 + 3802)) :=
    h.atom (a := .add (.n (b0 + 3802 + 1)) _ _) (by simp [addS])
  have hK := kMsg_cells_sound (len := 432) hp (by simp) (fun _ => by simp) h.right
  rw [hK]
  congr 2
  simp only [List.map_cons, List.map_map, Function.comp_def,
    Nat.zero_add, hr1, hr0, List.cons_append, List.nil_append, List.cons.injEq, true_and]
  refine List.map_congr_left fun k hk => ?_
  have := hT' k (List.mem_range.mp hk)
  simp only [Nat.zero_add] at this
  rw [this, ha1, ha0]

end
end LeanVM.Guest.B1.Sig
