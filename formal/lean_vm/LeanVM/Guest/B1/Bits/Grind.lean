/-
  LeanVM.Guest.B1.Bits.Grind

  B1 for `grind_check`: the low bits of the permutation's proof-of-work lane are zero.
-/

module

public import LeanVM.Guest.B1.Bits.GrindData

/-!
# `grind_check` (TRIAGE #21)

`grind_check__L{b}` is `gcBodyT b` (`grind_check_found`). Soundness: each window is `g^e` with
`e` below its width (`rc_sound`, the range check on a memory image of `2^κ ≥ 2^11` words), the
table reads it as `E(e)` (`winTab_read`), and Horner's rule in `x^11` does not reduce, so the
running value after step `i` is `E(V)` with `V < 2^(top + 11 i)` (`gc_acc`); shifted by `x^b` it
is `E(2^b·N)`, and the final split (`split_iff`) makes it the word's low limb. Completeness: the
windows of the low limb above bit `b` (`gcVals`), the range checks' complements and touched words
chosen (`rcWit`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Range checks and table reads -/

theorem wBound_eq {w : ℕ} (hw : w ≤ 11) : wBound w = gen ^ (2 ^ w - 1) := by
  rw [wBound, ← ofK_eq_ofLimbs, gpowK_eq, gen_pow_eq_ofK]
  calc 2 ^ w - 1 < 2 ^ 128 := lt_of_le_of_lt (Nat.sub_le _ _)
        (Nat.pow_lt_pow_right (by decide) (by omega))
    _ = u128Bound := rfl

/-- **A window's range check**: on a memory image of `2^κ ≥ 2^w` words, `x = g^e`, `e < 2^w`. -/
theorem rc_sound {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {w : ℕ} (hw : w ≤ 11) (hwk : w ≤ κ)
    {x y t1 t2 : E} (h1 : LoadHolds L.read x 0 t1) (h2 : wBound w = x * y)
    (h3 : LoadHolds L.read y 0 t2) : ∃ e < 2 ^ w, x = gen ^ e := by
  obtain ⟨e, he, hx⟩ := (rangeCheck_iff hκ L x (K := 2 ^ w) Nat.one_le_two_pow
    (Nat.pow_le_pow_right (by decide) hwk)).mp
      ⟨y, t1, t2, h1, by rw [← gen_pow_eq_ofK, ← wBound_eq hw, h2], h3⟩
  exact ⟨e, he, by rw [hx, gen_pow_eq_ofK]⟩

/-- **A window's range check is met** by `g^e`, `e < 2^w`. -/
theorem rc_complete {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {w : ℕ} (hw : w ≤ 11)
    (hwk : w ≤ κ) {e : ℕ} (he : e < 2 ^ w) :
    ∃ y t1 t2 : E, LoadHolds L.read (gen ^ e) 0 t1 ∧ wBound w = gen ^ e * y ∧
      LoadHolds L.read y 0 t2 := by
  obtain ⟨y, t1, t2, h1, h2, h3⟩ := (rangeCheck_iff hκ L (gen ^ e) (K := 2 ^ w)
    Nat.one_le_two_pow (Nat.pow_le_pow_right (by decide) hwk)).mpr ⟨e, he, gen_pow_eq_ofK e⟩
  exact ⟨y, t1, t2, h1, by rw [wBound_eq hw, gen_pow_eq_ofK, h2], h3⟩

/-- **A table read**: the word at `tabs·g^e`, `e < 2^11`, is `E(e)`. -/
theorem winTab_read {rd : Reader} {tabs v : E} (ht : WinTabs rd tabs) {e : ℕ} (he : e < 2 ^ 11)
    (h : LoadHolds rd (tabs * gen ^ e) 0 v) : v = eOfNat e :=
  loadHolds_unique (by simpa using (loadHolds_mul_gen_pow rd tabs e 0 v).mp h) (ht e he)

theorem winTab_load {rd : Reader} {tabs : E} (ht : WinTabs rd tabs) {e : ℕ} (he : e < 2 ^ 11) :
    LoadHolds rd (tabs * gen ^ e) 0 (eOfNat e) :=
  (loadHolds_mul_gen_pow rd tabs e 0 _).mpr (by simpa using ht e he)

/-- One Horner step without reduction: `E(V)·x^11 + E(e) = E(2^11 V + e)`. -/
theorem horner_step {V e : ℕ} (hV : 2 ^ 11 * V < 2 ^ 64) (he : e < 2 ^ 11) :
    eOfNat V * word 2048 0 + eOfNat e = eOfNat (2 ^ 11 * V + e) := by
  rw [word_eOfNat, show (2048 : ℕ) = 2 ^ 11 by norm_num, mul_comm, eOfNat_two_pow_mul hV,
    eOfNat_add_of_lt he]

/-! ## The blocks -/

/-- What Horner step `i` asks of a valuation. -/
def GcIterOk (rd : Reader) (σ : Val) (W i : ℕ) : Prop :=
  σ (.n (W + 9 * i)) = wBound 11 ∧
    (LoadHolds rd (σ (.n (W + 2 - i))) 0 (σ (.n (W + 9 * i + 2))) ∧
      σ (.n (W + 9 * i)) = σ (.n (W + 2 - i)) * σ (.n (W + 9 * i + 1)) ∧
      LoadHolds rd (σ (.n (W + 9 * i + 1))) 0 (σ (.n (W + 9 * i + 3)))) ∧
    σ (.n (W + 9 * i + 4)) = word 2048 0 ∧
    σ (.n (W + 9 * i + 5)) = σ (.n (W + 9 * i - 1)) * σ (.n (W + 9 * i + 4)) ∧
    σ (.n (W + 9 * i + 6)) = σ (.n 1) * σ (.n (W + 2 - i)) ∧
    LoadHolds rd (σ (.n (W + 9 * i + 6))) 0 (σ (.n (W + 9 * i + 7))) ∧
    σ (.n (W + 9 * i + 8)) = σ (.n (W + 9 * i + 5)) + σ (.n (W + 9 * i + 7))

theorem holds_gcIterAt {C : CallRel} {rd : Reader} {σ : Val} (W i : ℕ) (next : Prop)
    (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (gcIterAt W i) next kret ↔ GcIterOk rd σ W i ∧ next := by
  simp only [gcIterAt, GcIterOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_assoc]

/-- What the head asks of a valuation. -/
def GcHeadOk (rd : Reader) (σ : Val) (W T : ℕ) : Prop :=
  σ (.n (W + 3)) = wBound T ∧
    (LoadHolds rd (σ (.n (W + 2))) 0 (σ (.n (W + 5))) ∧
      σ (.n (W + 3)) = σ (.n (W + 2)) * σ (.n (W + 4)) ∧
      LoadHolds rd (σ (.n (W + 4))) 0 (σ (.n (W + 6)))) ∧
    σ (.n (W + 7)) = σ (.n 1) * σ (.n (W + 2)) ∧
    LoadHolds rd (σ (.n (W + 7))) 0 (σ (.n (W + 8)))

/-- What the tail asks of a valuation. -/
def GcTailOk (σ : Val) (W b : ℕ) : Prop :=
  σ (.n (10 * W + 9)) = word (2 ^ b) 0 ∧
    σ (.n (10 * W + 10)) = σ (.n (10 * W + 8)) * σ (.n (10 * W + 9)) ∧
    σ (.n (10 * W + 11)) = σ (.n 0) + σ (.n (10 * W + 10)) ∧
    σ (.n (10 * W + 12)) = word 2 1 ∧
    σ (.n (10 * W + 13)) = σ (.n (10 * W + 11)) * σ (.n (10 * W + 12)) ∧
    σ (.n (10 * W + 14)) = word (2 ^ b) 0 ∧
    σ (.n (10 * W + 15)) = σ (.n (10 * W + 8)) * σ (.n (10 * W + 14)) ∧
    IsInK (σ (.n (10 * W + 13))) ∧ IsInK (σ (.n (10 * W + 15)))

theorem holds_gcBodyT {C : CallRel} {rd : Reader} {σ : Val} (b : ℕ) (rets : List E) :
    Stmt.HoldsList C rd σ (gcBodyT b) False (fun rs => rs = rets) ↔
      GcHeadOk rd σ (gcW b) (gcTop b) ∧
        (∀ i < gcW b, GcIterOk rd σ (gcW b) (i + 1)) ∧ GcTailOk σ (gcW b) b ∧ [] = rets := by
  rw [gcBodyT, holdsList_append, holdsList_append,
    holdsList_range_flatten _ _ (fun i => rfl)]
  simp only [gcHead, gcTail, GcHeadOk, GcTailOk, holds_gcIterAt, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds, List.map_nil, true_and, and_true, and_assoc]

/-! ## Soundness -/

/-- **The running value**: after Horner step `i ≤ W` it is `E(V)` with `V < 2^(T + 11 i)`. -/
theorem gc_acc {κ : ℕ} (hκ : κ ≤ 32) (hκ11 : 11 ≤ κ) (L : MemoryImage κ) {σ : Val} {W T : ℕ}
    (hT : T ≤ 11) (hWT : T + 11 * W ≤ 64) (ht : WinTabs L.read (σ (.n 1)))
    (hh : GcHeadOk L.read σ W T) (hi : ∀ i < W, GcIterOk L.read σ W (i + 1)) :
    ∀ i ≤ W, ∃ V < 2 ^ (T + 11 * i), σ (.n (W + 9 * i + 8)) = eOfNat V := by
  intro i
  induction i with
  | zero =>
    intro _
    obtain ⟨h1, ⟨r1, r2, r3⟩, h3, h4⟩ := hh
    obtain ⟨e, he, hx⟩ := rc_sound hκ L hT (by omega) r1 (by rw [← h1, r2]) r3
    have he' : e < 2 ^ 11 := lt_of_lt_of_le he (Nat.pow_le_pow_right (by decide) hT)
    rw [h3, hx] at h4
    exact ⟨e, by simpa using he, winTab_read ht he' h4⟩
  | succ i ih =>
    intro hiW
    obtain ⟨V, hV, hacc⟩ := ih (by omega)
    obtain ⟨g1, ⟨r1, r2, r3⟩, g4, g5, g6, g7, g8⟩ := hi i (by omega)
    obtain ⟨e, he, hx⟩ := rc_sound hκ L (le_refl 11) hκ11 r1 (by rw [← g1, r2]) r3
    rw [g6, hx] at g7
    have hr := winTab_read ht he g7
    have hidx : W + 9 * (i + 1) - 1 = W + 9 * i + 8 := by omega
    rw [hidx, hacc, g4] at g5
    have hV64 : 2 ^ 11 * V < 2 ^ 64 := by
      calc 2 ^ 11 * V < 2 ^ 11 * 2 ^ (T + 11 * i) := Nat.mul_lt_mul_of_pos_left hV (by positivity)
        _ = 2 ^ (T + 11 * (i + 1)) := by rw [← pow_add]; ring_nf
        _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
    refine ⟨2 ^ 11 * V + e, ?_, ?_⟩
    · calc 2 ^ 11 * V + e < 2 ^ 11 * V + 2 ^ 11 := by omega
        _ = 2 ^ 11 * (V + 1) := by ring
        _ ≤ 2 ^ 11 * 2 ^ (T + 11 * i) := Nat.mul_le_mul_left _ hV
        _ = 2 ^ (T + 11 * (i + 1)) := by rw [← pow_add]; ring_nf
    · rw [g8, g5, hr, horner_step hV64 he]

/-- **`grind_check` is sound.** -/
theorem gc_sound {κ : ℕ} (hκ : κ ≤ 32) (hκ11 : 11 ≤ κ) (L : MemoryImage κ) {σ : Val} {b : ℕ}
    (hs : 1 ≤ gcTop b ∧ gcTop b ≤ 11 ∧ b + 11 * gcW b + gcTop b = 64)
    (ht : WinTabs L.read (σ (.n 1))) (hh : GcHeadOk L.read σ (gcW b) (gcTop b))
    (hi : ∀ i < gcW b, GcIterOk L.read σ (gcW b) (i + 1)) (htl : GcTailOk σ (gcW b) b) :
    ((σ (.n 0)).limb 0).lane.toNat % 2 ^ b = 0 := by
  obtain ⟨-, hT, hsum⟩ := hs
  obtain ⟨N, hN, hacc⟩ := gc_acc hκ hκ11 L hT (by omega) ht hh hi (gcW b) le_rfl
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, k13, k15⟩ := htl
  have hidx : 10 * gcW b + 8 = gcW b + 9 * gcW b + 8 := by ring
  have hbN : 2 ^ b * N < 2 ^ 64 := by
    calc 2 ^ b * N < 2 ^ b * 2 ^ (gcTop b + 11 * gcW b) :=
          Nat.mul_lt_mul_of_pos_left hN (by positivity)
      _ = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hL : σ (.n (10 * gcW b + 15)) = eOfNat (2 ^ b * N) := by
    rw [t7, hidx, hacc, t6, word_eOfNat, mul_comm, eOfNat_two_pow_mul hbN]
  have hD : σ (.n (10 * gcW b + 13)) = (σ (.n 0) + eOfNat (2 ^ b * N)) * y⁻¹ := by
    rw [t5, t3, t4, t2, t1, hidx, hacc, word_eOfNat, mul_comm (eOfNat N),
      eOfNat_two_pow_mul hbN, word_y_inv]
  rw [hL] at k15
  rw [hD] at k13
  have hl := (split_iff _ _).mp ⟨k15, k13⟩
  have hk : (σ (.n 0)).limb 0 = K.ofBits (2 ^ b * N) := (ofK_injective hl).symm
  show kToNat ((σ (.n 0)).limb 0) % 2 ^ b = 0
  rw [hk, kToNat_ofBits, Nat.mod_eq_of_lt hbN, Nat.mul_mod_right]

/-! ## Completeness -/

/-- A range check's complement and touched words, chosen. -/
noncomputable def rcWit (rd : Reader) (x k : E) : E × E × E :=
  @Classical.epsilon _ ⟨(0, 0, 0)⟩ fun p : E × E × E =>
    LoadHolds rd x 0 p.2.1 ∧ k = x * p.1 ∧ LoadHolds rd p.1 0 p.2.2

theorem rcWit_spec {rd : Reader} {x k : E}
    (h : ∃ y t1 t2 : E, LoadHolds rd x 0 t1 ∧ k = x * y ∧ LoadHolds rd y 0 t2) :
    LoadHolds rd x 0 (rcWit rd x k).2.1 ∧ k = x * (rcWit rd x k).1 ∧
      LoadHolds rd (rcWit rd x k).1 0 (rcWit rd x k).2.2 := by
  obtain ⟨y, t1, t2, h⟩ := h
  exact @Classical.epsilon_spec _ (fun p : E × E × E =>
    LoadHolds rd x 0 p.2.1 ∧ k = x * p.1 ∧ LoadHolds rd p.1 0 p.2.2) ⟨(y, t1, t2), h⟩

/-- The integer the windows from step `i` on spell: the low limb from bit `b + 11 (W - i)`. -/
def gcV (b : ℕ) (w : E) (i : ℕ) : ℕ := kToNat (w.limb 0) / 2 ^ (b + 11 * (gcW b - i))

/-- Horner step `i`'s honest values, by offset. -/
noncomputable def gcIterVal (rd : Reader) (b : ℕ) (w tabs : E) (i r : ℕ) : E :=
  match r with
  | 0 => wBound 11
  | 1 => (rcWit rd (gen ^ (gcV b w i % 2 ^ 11)) (wBound 11)).1
  | 2 => (rcWit rd (gen ^ (gcV b w i % 2 ^ 11)) (wBound 11)).2.1
  | 3 => (rcWit rd (gen ^ (gcV b w i % 2 ^ 11)) (wBound 11)).2.2
  | 4 => word 2048 0
  | 5 => eOfNat (gcV b w (i - 1)) * word 2048 0
  | 6 => tabs * gen ^ (gcV b w i % 2 ^ 11)
  | 7 => eOfNat (gcV b w i % 2 ^ 11)
  | _ => eOfNat (gcV b w i)

/-- The tail's honest values, by offset. -/
def gcTailVal (b : ℕ) (w : E) (r : ℕ) : E :=
  match r with
  | 0 => word (2 ^ b) 0
  | 1 => eOfNat (gcV b w (gcW b)) * word (2 ^ b) 0
  | 2 => w + eOfNat (gcV b w (gcW b)) * word (2 ^ b) 0
  | 3 => word 2 1
  | 4 => (w + eOfNat (gcV b w (gcW b)) * word (2 ^ b) 0) * word 2 1
  | 5 => word (2 ^ b) 0
  | _ => eOfNat (gcV b w (gcW b)) * word (2 ^ b) 0

/-- **The honest valuation of `grind_check__L{b}`** on the word `w` and the table `tabs`. -/
noncomputable def gcVals (rd : Reader) (b : ℕ) (w tabs : E) (k : ℕ) : E :=
  if k = 0 then w
  else if k = 1 then tabs
  else if k < gcW b + 2 then gen ^ (gcV b w (gcW b + 2 - k) % 2 ^ 11)
  else if k = gcW b + 2 then gen ^ gcV b w 0
  else if k = gcW b + 3 then wBound (gcTop b)
  else if k = gcW b + 4 then (rcWit rd (gen ^ gcV b w 0) (wBound (gcTop b))).1
  else if k = gcW b + 5 then (rcWit rd (gen ^ gcV b w 0) (wBound (gcTop b))).2.1
  else if k = gcW b + 6 then (rcWit rd (gen ^ gcV b w 0) (wBound (gcTop b))).2.2
  else if k = gcW b + 7 then tabs * gen ^ gcV b w 0
  else if k = gcW b + 8 then eOfNat (gcV b w 0)
  else if k < 10 * gcW b + 9 then gcIterVal rd b w tabs ((k - gcW b) / 9) ((k - gcW b) % 9)
  else gcTailVal b w (k - (10 * gcW b + 9))

section Eval

variable {rd : Reader} {b : ℕ} {w tabs : E}

theorem gv_win {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ gcW b) :
    gcVals rd b w tabs (gcW b + 2 - i) = gen ^ (gcV b w i % 2 ^ 11) := by
  unfold gcVals
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
    show gcW b + 2 - (gcW b + 2 - i) = i by omega]

theorem gv_iter {i r : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ gcW b) (hr : r < 9) :
    gcVals rd b w tabs (gcW b + 9 * i + r) = gcIterVal rd b w tabs i r := by
  unfold gcVals
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left (by omega), show (gcW b + 9 * i + r - gcW b) / 9 = i by omega,
    show (gcW b + 9 * i + r - gcW b) % 9 = r by omega]

theorem gv_tail {r : ℕ} : gcVals rd b w tabs (10 * gcW b + 9 + r) = gcTailVal b w r := by
  unfold gcVals
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), show 10 * gcW b + 9 + r - (10 * gcW b + 9) = r by omega]

/-- The running value after step `i`. -/
theorem gv_acc {i : ℕ} (h : i ≤ gcW b) :
    gcVals rd b w tabs (gcW b + 9 * i + 8) = eOfNat (gcV b w i) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · unfold gcVals
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left (by omega)]
  · rw [gv_iter hi h (by omega)]
    rfl

end Eval

/-- Step `i - 1`'s value is step `i`'s without its low window. -/
theorem gcV_pred {b : ℕ} (w : E) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ gcW b) :
    gcV b w (i - 1) = gcV b w i / 2 ^ 11 := by
  unfold gcV
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  congr 2
  omega

theorem gcV_lt {b : ℕ} (w : E) (i : ℕ) : gcV b w i < 2 ^ 64 :=
  lt_of_le_of_lt (Nat.div_le_self _ _) (kToNat_lt _)

/-- **`grind_check` is complete**: the honest valuation meets every block. -/
theorem gc_complete {κ : ℕ} (hκ : κ ≤ 32) (hκ11 : 11 ≤ κ) (L : MemoryImage κ) {b : ℕ}
    (hs : 1 ≤ gcTop b ∧ gcTop b ≤ 11 ∧ b + 11 * gcW b + gcTop b = 64) (hW : 1 ≤ gcW b)
    {w tabs : E} (ht : WinTabs L.read tabs) (hlow : ((w.limb 0).lane.toNat % 2 ^ b = 0)) :
    let σ : Val := fun v => gcVals L.read b w tabs v.idx
    GcHeadOk L.read σ (gcW b) (gcTop b) ∧ (∀ i < gcW b, GcIterOk L.read σ (gcW b) (i + 1)) ∧
      GcTailOk σ (gcW b) b := by
  intro σ
  obtain ⟨hT1, hT, hsum⟩ := hs
  have ev : ∀ k, σ (.n k) = gcVals L.read b w tabs k := fun _ => rfl
  have hlow' : kToNat (w.limb 0) % 2 ^ b = 0 := hlow
  have hV0 : gcV b w 0 < 2 ^ gcTop b := by
    unfold gcV
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_zero,
      show gcTop b + (b + 11 * gcW b) = 64 by omega]
    exact kToNat_lt _
  have hV0' : gcV b w 0 < 2 ^ 11 := lt_of_lt_of_le hV0 (Nat.pow_le_pow_right (by decide) hT)
  refine ⟨?_, fun i hi => ?_, ?_⟩
  · obtain ⟨y, t1, t2, r1, r2, r3⟩ := rc_complete hκ L hT (by omega) hV0
    have hrc := rcWit_spec (rd := L.read) ⟨y, t1, t2, r1, r2, r3⟩
    have e2 : σ (.n (gcW b + 2)) = gen ^ gcV b w 0 := by
      rw [ev]; unfold gcVals
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
    have e3 : σ (.n (gcW b + 3)) = wBound (gcTop b) := by
      rw [ev]; unfold gcVals
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
    have e4 : σ (.n (gcW b + 4)) = (rcWit L.read (gen ^ gcV b w 0) (wBound (gcTop b))).1 := by
      rw [ev]; unfold gcVals
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_left rfl]
    have e5 : σ (.n (gcW b + 5)) = (rcWit L.read (gen ^ gcV b w 0) (wBound (gcTop b))).2.1 := by
      rw [ev]; unfold gcVals
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
    have e6 : σ (.n (gcW b + 6)) = (rcWit L.read (gen ^ gcV b w 0) (wBound (gcTop b))).2.2 := by
      rw [ev]; unfold gcVals
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
    have e7 : σ (.n (gcW b + 7)) = tabs * gen ^ gcV b w 0 := by
      rw [ev]; unfold gcVals
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
    have e8 : σ (.n (gcW b + 8)) = eOfNat (gcV b w 0) := by
      rw [ev, show gcW b + 8 = gcW b + 9 * 0 + 8 by ring]; exact gv_acc (i := 0) (by omega)
    have e1 : σ (.n 1) = tabs := by rw [ev]; unfold gcVals; rw [ite_eq_right (by omega), ite_eq_left rfl]
    rw [GcHeadOk, e2, e3, e4, e5, e6, e7, e8, e1]
    exact ⟨rfl, hrc, rfl, winTab_load ht hV0'⟩
  · have h1 : 1 ≤ i + 1 := by omega
    have h2 : i + 1 ≤ gcW b := by omega
    have hwin : gcV b w (i + 1) % 2 ^ 11 < 2 ^ 11 := Nat.mod_lt _ (by positivity)
    obtain ⟨y, t1, t2, r1, r2, r3⟩ := rc_complete hκ L (le_refl 11) hκ11 hwin
    have hrc := rcWit_spec (rd := L.read) ⟨y, t1, t2, r1, r2, r3⟩
    have ew : σ (.n (gcW b + 2 - (i + 1))) = gen ^ (gcV b w (i + 1) % 2 ^ 11) := by
      rw [ev]; exact gv_win h1 h2
    have ei : ∀ r < 9, σ (.n (gcW b + 9 * (i + 1) + r)) = gcIterVal L.read b w tabs (i + 1) r :=
      fun r hr => by rw [ev]; exact gv_iter h1 h2 hr
    have e0 : σ (.n (gcW b + 9 * (i + 1))) = wBound 11 := ei 0 (by omega)
    have ep : σ (.n (gcW b + 9 * (i + 1) - 1)) = eOfNat (gcV b w i) := by
      rw [ev, show gcW b + 9 * (i + 1) - 1 = gcW b + 9 * i + 8 by omega]
      exact gv_acc (i := i) (by omega)
    have e1 : σ (.n 1) = tabs := by rw [ev]; unfold gcVals; rw [ite_eq_right (by omega), ite_eq_left rfl]
    rw [GcIterOk, ew, e0, ei 1 (by omega), ei 2 (by omega), ei 3 (by omega), ei 4 (by omega),
      ei 5 (by omega), ei 6 (by omega), ei 7 (by omega), ei 8 (by omega), ep, e1]
    refine ⟨rfl, hrc, rfl, ?_, rfl, winTab_load ht hwin, ?_⟩
    · show eOfNat (gcV b w (i + 1 - 1)) * word 2048 0 = eOfNat (gcV b w i) * word 2048 0
      rw [Nat.add_sub_cancel]
    · show eOfNat (gcV b w (i + 1)) =
        eOfNat (gcV b w (i + 1 - 1)) * word 2048 0 + eOfNat (gcV b w (i + 1) % 2 ^ 11)
      have hp := gcV_pred (b := b) w h1 h2
      have h64 : 2 ^ 11 * gcV b w (i + 1 - 1) < 2 ^ 64 := by
        rw [hp]
        exact lt_of_le_of_lt (Nat.mul_div_le _ _) (gcV_lt w _)
      rw [horner_step h64 hwin, hp, Nat.div_add_mod]
  · have ea : σ (.n (10 * gcW b + 8)) = eOfNat (gcV b w (gcW b)) := by
      rw [ev, show 10 * gcW b + 8 = gcW b + 9 * gcW b + 8 by ring]
      exact gv_acc (i := gcW b) le_rfl
    have et : ∀ r, σ (.n (10 * gcW b + 9 + r)) = gcTailVal b w r := fun r => by rw [ev]; exact gv_tail
    have e0 : σ (.n 0) = w := by rw [ev]; unfold gcVals; rw [ite_eq_left rfl]
    have hVW : 2 ^ b * gcV b w (gcW b) = kToNat (w.limb 0) := by
      unfold gcV
      rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
      exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hlow')
    have hL : eOfNat (gcV b w (gcW b)) * word (2 ^ b) 0 = ofK (w.limb 0) := by
      rw [word_eOfNat, mul_comm, eOfNat_two_pow_mul (by rw [hVW]; exact kToNat_lt _), hVW,
        eOfNat, ofBits_kToNat]
    have hsp := (split_iff w (ofK (w.limb 0))).mpr rfl
    rw [GcTailOk, et 0, show 10 * gcW b + 10 = 10 * gcW b + 9 + 1 by ring, et 1,
      show 10 * gcW b + 11 = 10 * gcW b + 9 + 2 by ring, et 2,
      show 10 * gcW b + 12 = 10 * gcW b + 9 + 3 by ring, et 3,
      show 10 * gcW b + 13 = 10 * gcW b + 9 + 4 by ring, et 4,
      show 10 * gcW b + 14 = 10 * gcW b + 9 + 5 by ring, et 5,
      show 10 * gcW b + 15 = 10 * gcW b + 9 + 6 by ring, et 6, ea, e0]
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · show IsInK ((w + eOfNat (gcV b w (gcW b)) * word (2 ^ b) 0) * word 2 1)
      rw [hL, word_y_inv]; exact hsp.2
    · show IsInK (eOfNat (gcV b w (gcW b)) * word (2 ^ b) 0)
      rw [hL]; exact hsp.1

/-! ## The meaning -/

/-- **`grind_check__L{b}`'s core IR is its meaning**, for every deployed grind. -/
theorem grind_check_holds : grind_check_all_Spec := by
  intro b hb κ hκ hκ11 L w tabs ht rets
  obtain ⟨fn, hfind, hpar, hbody⟩ := grind_check_found b hb
  have hs := gc_shape b hb
  have hW : 1 ≤ gcW b := by
    simp only [grindBitsDeployed, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [rel_iff_sem hfind, hpar, hbody]
  simp only [holds_gcBodyT, List.map_cons, List.map_nil, MeaningGrindCheck]
  constructor
  · rintro ⟨σ, hp, hh, hi, htl, hr⟩
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨h0, h1⟩ := hp
    refine ⟨hr.symm, ?_⟩
    rw [← h0]
    exact gc_sound hκ hκ11 L hs (by rw [h1]; exact ht) hh hi htl
  · rintro ⟨hr, hlow⟩
    obtain ⟨hh, hi, htl⟩ := gc_complete hκ hκ11 L hs hW ht hlow
    refine ⟨fun v => gcVals L.read b w tabs v.idx, ?_, hh, hi, htl, hr.symm⟩
    show [gcVals L.read b w tabs 0, gcVals L.read b w tabs 1] = [w, tabs]
    unfold gcVals
    simp

/-- **A `grind_check` call passing** (`grindCallT`): the proof-of-work lane's low `bits` bits are
zero. -/
theorem grindCall_pow {bits : ℕ} (hb : bits ∈ grindBitsDeployed) {κ : ℕ} (hκ : κ ≤ 32)
    (h11 : winTabBits ≤ κ) (L : MemoryImage κ) {w tabs : E} (ht : WinTabs L.read tabs)
    (h : coreProgram.Rel L.read (grindCheckName bits) [w, tabs] []) :
    (w.limb 0).lane.toNat % 2 ^ bits = 0 :=
  ((grind_check_holds bits hb hκ h11 L w tabs ht []).mp h).2

end
end LeanVM.Guest.B1
