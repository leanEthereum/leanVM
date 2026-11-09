/-
  LeanVM.Guest.B1.Sig.XmssWindows

  leanXMSS's leaf index, a window at a time (`lx_window`, `lx_top_window`, `lean_ethereum.py:
  3613-3653`): the windows pin the hinted shifts, and the path's addresses and bits are the index's.
  The chain indices a chain step hashes (`walk`, `lean_ethereum.py:3545-3570`).
-/

module

public import LeanVM.Guest.B1.Sig.Codeword

/-!
# The leaf index's windows, and the chain indices

`verify_lean_xmss` (`lean_ethereum.py:3656-3728`, inline in `main`'s `__loop2`) hints the leaf
index's shifts `his[v] = L >>> 8v` (`lx_index`) and its four 8-bit windows in the exponent
(`lx_windows`), and dispatches the path a window at a time: arm `k` of window `w` walks the
window's eight levels, its bit `r` the order of level `r`'s node against its hinted sibling, and
writes `his[w + 1] · g^8 + k` (the top window `k`) where the hinted `his[w]` is.

* `lxIndex k`: the integer of the windows `k 0, …, k 3`, low first, below `2^32`;
* `lx_his`: arms below `2^8` that pin the shifts make `his[w]` the word of `lxIndex k >>> 8w`;
  `lx_his_honest`: an index's windows (`lxWin`) and shifts pin each other (completeness);
* `lx_at`: the address of level `r` of window `w`, `his[w + 1] · g^(7 - r)` plus the constant
  `lxNodeConst w r + k >>> (r + 1)` (`his[w + 1]` alone at `r = 7`, the constant alone in the top
  window), is the node's address over the index (`lxNodeAddr`), the root's at index `0`;
* `lx_bit`: arm `k`'s bit `r` is the index's bit `8w + r`;
* `lx_layer_idx`: a layer's index cell (`his[0]`, `his[2] + LX_TOP`) is the index's key with the
  layer's bit;
* `lxTagCarried`, `lxTagSlot`, `lxTagLog` (`LX_TAG_SLOT`, `LX_TAG_LOG`, `aggregation/placeholders.rs:900-914`):
  chain `i`'s index cell is the zero cell (`i = 0`), `powers[log₂ i]` (a power of two) or carried
  tag `lxTagSlot i - 1` (`LX_N_TAGS = 51` of them); `lx_tag`: each holds `i`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The index and its shifts -/

/-- The leaf index of the four windows `k 0, …, k 3`, low first. -/
def lxIndex (k : Nat → Nat) : Nat := k 0 + 256 * k 1 + 65536 * k 2 + 16777216 * k 3

/-- Window `w` of the index `L`. -/
def lxWin (L w : Nat) : Nat := L >>> (8 * w) % 256

theorem lxIndex_lt {k : Nat → Nat} (hk : ∀ w < 4, k w < 256) : lxIndex k < 2 ^ 32 := by
  have := hk 0 (by omega); have := hk 1 (by omega); have := hk 2 (by omega); have := hk 3 (by omega)
  unfold lxIndex; omega

theorem lxIndex_shift {k : Nat → Nat} (hk : ∀ w < 4, k w < 256) :
    lxIndex k >>> 24 = k 3 ∧ ∀ w < 3, lxIndex k >>> (8 * w) = k w + 256 * (lxIndex k >>> (8 * (w + 1))) := by
  have := hk 0 (by omega); have := hk 1 (by omega); have := hk 2 (by omega); have := hk 3 (by omega)
  simp only [Nat.shiftRight_eq_div_pow]
  refine ⟨by unfold lxIndex; norm_num; omega, fun w hw => ?_⟩
  interval_cases w <;> unfold lxIndex <;> norm_num <;> omega

/-- `x · g^s` for a word `x = E(v)` without reduction. -/
theorem eOfNat_mul_two_pow {v s : Nat} (h : 2 ^ s * v < 2 ^ 64) :
    eOfNat v * eOfNat (2 ^ s) = eOfNat (2 ^ s * v) := by
  rw [mul_comm, eOfNat_two_pow_mul h]

/-- One pin: `his[w + 1] · g^8 + k` is the word of `k + 256 · his[w + 1]`. -/
theorem lx_pin {x k : Nat} (hx : x < 2 ^ 32) (hk : k < 256) :
    eOfNat x * eOfNat (2 ^ 8) + eOfNat k = eOfNat (k + 256 * x) := by
  rw [eOfNat_mul_two_pow (by omega), eOfNat_add_of_lt (s := 8) (by norm_num; omega)]
  congr 1; norm_num; omega

/-- **The windows pin the shifts**: when the top shift is its window and each other shift is the
next one times `g^8` plus its window, shift `w` is the word of the windows' index shifted by `8w`. -/
theorem lx_his {h : Nat → E} {k : Nat → Nat} (hk : ∀ w < 4, k w < 256) (htop : h 3 = eOfNat (k 3))
    (hstep : ∀ w < 3, h w = h (w + 1) * eOfNat (2 ^ 8) + eOfNat (k w)) :
    ∀ w < 4, h w = eOfNat (lxIndex k >>> (8 * w)) := by
  obtain ⟨h24, hs⟩ := lxIndex_shift hk
  have hL := lxIndex_lt hk
  have hlt : ∀ w, lxIndex k >>> w < 2 ^ 32 := fun w => lt_of_le_of_lt (Nat.shiftRight_le _ _) hL
  have e3 : h 3 = eOfNat (lxIndex k >>> (8 * 3)) := by rw [htop, show 8 * 3 = 24 from rfl, h24]
  have step : ∀ w < 3, h (w + 1) = eOfNat (lxIndex k >>> (8 * (w + 1))) →
      h w = eOfNat (lxIndex k >>> (8 * w)) := by
    intro w hw ih
    rw [hstep w hw, ih, lx_pin (hlt _) (hk w (by omega)), hs w hw]
  have e2 := step 2 (by omega) e3
  have e1 := step 1 (by omega) e2
  have e0 := step 0 (by omega) e1
  intro w hw
  interval_cases w
  exacts [e0, e1, e2, e3]

theorem lxWin_lt (L w : Nat) : lxWin L w < 256 := Nat.mod_lt _ (by norm_num)

theorem lxIndex_lxWin {L : Nat} (hL : L < 2 ^ 32) : lxIndex (lxWin L) = L := by
  simp only [lxIndex, lxWin, Nat.shiftRight_eq_div_pow]
  norm_num
  omega

/-- **An index's windows and shifts pin each other** (completeness): the shift `L >>> 8w` is the
next one times `g^8` plus window `w`, and the top shift is the top window. -/
theorem lx_his_honest {L : Nat} (hL : L < 2 ^ 32) :
    eOfNat (L >>> 24) = eOfNat (lxWin L 3) ∧ ∀ w < 3,
      eOfNat (L >>> (8 * w)) = eOfNat (L >>> (8 * (w + 1))) * eOfNat (2 ^ 8) + eOfNat (lxWin L w) := by
  have hk : ∀ w < 4, lxWin L w < 256 := fun w _ => lxWin_lt L w
  obtain ⟨h24, hs⟩ := lxIndex_shift hk
  rw [lxIndex_lxWin hL] at h24 hs
  refine ⟨by rw [h24], fun w hw => ?_⟩
  rw [lx_pin (lt_of_le_of_lt (Nat.shiftRight_le _ _) hL) (lxWin_lt L w), ← hs w hw]

/-! ## The path's addresses and bits -/

/-- The constant of level `r` of window `w`'s parent address (`lx_levels`): the node type, the
level in its layer plus one above bit `32`, the layer's bit `55`. -/
def lxNodeConst (w r : Nat) : Nat :=
  tw 3 + ((8 * w + r) % 16 + 1) * hiMul + (8 * w + r) / 16 * lxTop

/-- The address of level `r` of window `w`'s parent over the index `L`: the constant plus
`L >>> (8w + r + 1)`, the top layer's root at index `0`. -/
def lxNodeAddr (L w r : Nat) : E :=
  word (lxNodeConst w r) 0 0 + if 8 * w + r + 1 = 32 then 0 else eOfNat (L >>> (8 * w + r + 1))

/-- The address `lx_levels` computes at level `r` of window `w` in arm `k`, from the next shift
`hi` and the power `g^(7 - r)` `pw`. -/
def lxAt (hi pw : E) (w r k : Nat) : E :=
  if w + 1 = 4 then word (lxNodeConst w r + k / 2 ^ (r + 1)) 0 0
  else if r + 1 = 8 then hi + word (lxNodeConst w r + k / 2 ^ (r + 1)) 0 0
  else hi * pw + word (lxNodeConst w r + k / 2 ^ (r + 1)) 0 0

theorem lxNodeConst_eq (w r : Nat) :
    lxNodeConst w r = 2 ^ 32 * (3 * 2 ^ 24 + ((8 * w + r) % 16 + 1) + 2 ^ 23 * ((8 * w + r) / 16)) := by
  simp only [lxNodeConst, tw, hiMul, lxTop]
  ring

/-- A constant above bit `32` plus a value below it. -/
theorem word_split {q x : Nat} (hx : x < 2 ^ 32) :
    word (2 ^ 32 * q + x) 0 0 = word (2 ^ 32 * q) 0 0 + eOfNat x := by
  rw [word_eq_eOfNat, word_eq_eOfNat, eOfNat_add_of_lt hx]

theorem lxNodeConst_lt {w r : Nat} (hw : w < 4) (hr : r < 8) : lxNodeConst w r + 2 ^ 32 < 2 ^ 64 := by
  rw [lxNodeConst_eq]
  have : (8 * w + r) % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have : (8 * w + r) / 16 ≤ 1 := by omega
  have h1 : 2 ^ 32 * (3 * 2 ^ 24 + ((8 * w + r) % 16 + 1) + 2 ^ 23 * ((8 * w + r) / 16)) ≤
      2 ^ 32 * (3 * 2 ^ 24 + 16 + 2 ^ 23) := Nat.mul_le_mul_left _ (by omega)
  have h2 : 2 ^ 32 * (3 * 2 ^ 24 + 16 + 2 ^ 23) + 2 ^ 32 < 2 ^ 64 := by norm_num
  omega

/-- The shifts of an index, in a window. -/
theorem lx_shift_window (L w r : Nat) (hr : r < 8) :
    (L >>> (8 * w + 8)) * 2 ^ (7 - r) + lxWin L w / 2 ^ (r + 1) = L >>> (8 * w + r + 1) := by
  simp only [lxWin, Nat.shiftRight_eq_div_pow]
  rw [show 8 * w + 8 = 8 * w + 8 by rfl, pow_add, ← Nat.div_div_eq_div_mul,
    show 8 * w + r + 1 = 8 * w + (r + 1) by omega, pow_add (a := 2) (8 * w) (r + 1),
    ← Nat.div_div_eq_div_mul]
  generalize L / 2 ^ (8 * w) = M
  interval_cases r <;> norm_num <;> omega

/-- **The path's addresses**: with the shifts `his[v] = E(L >>> 8v)` and `L` below `2^32`, the
address arm `lxWin L w` computes at level `r` of window `w` is the node's. -/
theorem lx_at {L : Nat} (hL : L < 2 ^ 32) {his : Nat → E}
    (hhis : ∀ v < 4, his v = eOfNat (L >>> (8 * v))) {w r : Nat} (hw : w < 4) (hr : r < 8) :
    lxAt (his (w + 1)) (eOfNat (2 ^ (7 - r))) w r (lxWin L w) = lxNodeAddr L w r := by
  have hc := lxNodeConst_lt hw hr
  have hsw := lx_shift_window L w r hr
  have hk : lxWin L w / 2 ^ (r + 1) < 2 ^ 32 :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans (lxWin_lt L w) (by norm_num))
  have hlt : ∀ s, L >>> s < 2 ^ 32 := fun s => lt_of_le_of_lt (Nat.shiftRight_le _ _) hL
  unfold lxAt lxNodeAddr
  rw [lxNodeConst_eq] at hc ⊢
  rw [word_split hk]
  by_cases hw3 : w + 1 = 4
  · have hw' : w = 3 := by omega
    subst hw'
    have h32 : L >>> (8 * 3 + 8) = 0 := by
      rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt (lt_of_lt_of_le hL (by norm_num))
    rw [h32, zero_mul, zero_add] at hsw
    simp only [hw3, ↓reduceIte]
    split
    · rename_i h
      have : r = 7 := by omega
      subst this
      have : lxWin L 3 / 2 ^ (7 + 1) = 0 := Nat.div_eq_of_lt (lxWin_lt L 3)
      rw [this, eOfNat_zero]
    · rw [hsw]
  · simp only [hw3, ↓reduceIte, show 8 * w + r + 1 ≠ 32 by omega]
    rw [hhis (w + 1) (by omega), show 8 * (w + 1) = 8 * w + 8 by ring]
    split
    · rename_i h7
      have : r = 7 := by omega
      subst this
      rw [show 7 - 7 = 0 from rfl, pow_zero, mul_one] at hsw
      have h0 : lxWin L w / 2 ^ (7 + 1) = 0 := Nat.div_eq_of_lt (lxWin_lt L w)
      rw [h0, add_zero] at hsw
      rw [h0, eOfNat_zero, add_zero, hsw, add_comm]
    · have hk7 : lxWin L w / 2 ^ (r + 1) < 2 ^ (7 - r) := by
        apply Nat.div_lt_of_lt_mul
        rw [← pow_add, show r + 1 + (7 - r) = 8 by omega]
        exact lxWin_lt L w
      have hm : 2 ^ (7 - r) * (L >>> (8 * w + 8)) < 2 ^ 64 := by
        have := hlt (8 * w + 8)
        have : 2 ^ (7 - r) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
        calc 2 ^ (7 - r) * (L >>> (8 * w + 8)) ≤ 2 ^ 7 * 2 ^ 32 := Nat.mul_le_mul this (by omega)
          _ < 2 ^ 64 := by norm_num
      have e1 : eOfNat (L >>> (8 * w + 8)) * eOfNat (2 ^ (7 - r)) + eOfNat (lxWin L w / 2 ^ (r + 1)) =
          eOfNat (L >>> (8 * w + r + 1)) := by
        rw [eOfNat_mul_two_pow hm, eOfNat_add_of_lt hk7, ← hsw, mul_comm]
      rw [← e1]
      ring

/-- **The path's bits**: arm `lxWin L w`'s bit `r` is the index's bit `8w + r`. -/
theorem lx_bit (L w r : Nat) (hr : r < 8) :
    lxWin L w / 2 ^ r % 2 = 1 ↔ L.testBit (8 * w + r) = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff, lxWin, Nat.shiftRight_eq_div_pow,
    pow_add, ← Nat.div_div_eq_div_mul]
  generalize L / 2 ^ (8 * w) = M
  interval_cases r <;> norm_num <;> omega

/-! ## The layers' indices -/

/-- **A layer's index cell**: `his[0]` at the bottom, `his[2] + LX_TOP` at the top, the index's key
on the layer with the top layer's bit `55`. -/
theorem lx_layer_idx {L : Nat} (hL : L < 2 ^ 32) :
    eOfNat (L >>> (8 * 0)) = eOfNat (2 ^ 32 * (2 ^ 23 * 0) + L >>> (16 * 0)) ∧
      eOfNat (L >>> (8 * 2)) + word lxTop 0 0 = eOfNat (2 ^ 32 * (2 ^ 23 * 1) + L >>> (16 * 1)) := by
  refine ⟨by simp, ?_⟩
  rw [word_eq_eOfNat, add_comm, show lxTop = 2 ^ 32 * (2 ^ 23 * 1) by simp [lxTop],
    eOfNat_add_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) hL)]

/-! ## The chain indices -/

/-- Whether chain `i`'s index is carried as a tag: neither `0` nor a power of two
(`aggregation/placeholders.rs:905-910`). -/
def lxTagCarried (i : Nat) : Bool := i != 0 && (i &&& (i - 1)) != 0

/-- Chain `i`'s tag slot, one past its carried tag (`LX_TAG_SLOT`), `0` if not carried. -/
def lxTagSlot (i : Nat) : Nat :=
  if lxTagCarried i then ((List.range (i + 1)).filter lxTagCarried).length else 0

/-- `⌊log₂ i⌋` (`LX_TAG_LOG`), the power a power of two's index is. -/
def lxTagLog (i : Nat) : Nat := Nat.log2 i

/-- The number of carried tags (`LX_N_TAGS`). -/
def lxNTags : Nat := ((List.range 58).filter lxTagCarried).length

theorem lxNTags_eq : lxNTags = 51 := by decide

/-- The carried tags' slots are below `LX_N_TAGS` and distinct. -/
theorem lxTagSlot_spec : ∀ i < 58, lxTagCarried i = true → 1 ≤ lxTagSlot i ∧ lxTagSlot i ≤ 51 := by
  decide

theorem lxTagSlot_inj : ∀ i < 58, ∀ j < 58, lxTagCarried i = true → lxTagCarried j = true →
    lxTagSlot i = lxTagSlot j → i = j := by
  decide

/-- An index neither `0` nor carried is a power of two below `2^6`. -/
theorem lxTagLog_spec : ∀ i < 58, i ≠ 0 → lxTagCarried i = false → 2 ^ lxTagLog i = i ∧ lxTagLog i < 6 := by
  decide

/-- The cell `walk` hashes as chain `i`'s index: the zero cell `z`, `powers[log₂ i]` or the carried
tag `tags[slot - 1]`. -/
def lxTagOf (z : E) (powers tags : Nat → E) (i : Nat) : E :=
  if i = 0 then z else if lxTagCarried i then tags (lxTagSlot i - 1) else powers (lxTagLog i)

/-- **The carried tags hold their indices** (`main`'s `lx_tags`, `lean_ethereum.py:4576-4581`). -/
def LxTagsHold (tags : Nat → E) : Prop :=
  ∀ i < 58, lxTagCarried i = true → tags (lxTagSlot i - 1) = eOfNat i

/-- **Each chain's index cell holds the index.** -/
theorem lx_tag {z : E} (hz : z = 0) {powers : Nat → E} (hpw : ∀ s < 6, powers s = gen ^ s)
    {tags : Nat → E} (ht : LxTagsHold tags) : ∀ i < 58, lxTagOf z powers tags i = eOfNat i := by
  intro i hi
  unfold lxTagOf
  split
  · rename_i h0; rw [hz, h0, eOfNat_zero]
  · rename_i h0
    split
    · rename_i hc; exact ht i hi hc
    · rename_i hc
      obtain ⟨e, hlt⟩ := lxTagLog_spec i hi h0 (by simpa using hc)
      rw [hpw _ hlt, gen_pow_eq_eOfNat (by omega), e]

end
end LeanVM.Guest.B1.Sig
