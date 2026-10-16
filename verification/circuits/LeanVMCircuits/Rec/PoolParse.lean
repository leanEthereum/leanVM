module

public import LeanVMCircuits.Rec.Ext

@[expose] public section

/-!
Parse uniqueness of a union's pool (`rec::tree::union::PoolShape::rows`), on the values its rows give an assignment.

A pool is `n` items, each one compression: its row's input ports are the counter and finalization words, the
chaining value's four words and the block's eight, its output ports the next chaining value. Some items start a run
(`σ`): the pool's first, and a chunk's first whose begin bit is set; the begin bits are inputs of the union's
transcript, so `σ` is the same in every assignment considered. What the rows say of one assignment is `Sem`:

- the kind bits `b0`, `b1`, `pair` are bits, and with the start bit they spell the counter word's low limb;
- an item that does not start a run chains from the previous item's output;
- padding (`b0 · b1`) follows an end or padding and never starts a run, and a run starts only after an end or
  padding, as the pool's last item is;
- the second member bit is zero outside a block of members;
- an end (`b1 + b0 · b1`) outputs the digest its run must have, `X`, which a run's items share.

`parse_unique`: two assignments of one pool, with the same `σ` and `X`, whose compressions do not collide, give every
item the same kind bits, and every item but padding the same row inputs, its block among them. So under collision
resistance the digests and begin bits fix what a pool reads.
-/

namespace LeanVMCircuits.Rec.PoolParse

/-- A `K` value that is a bit. -/
def IsBit (x : K) : Prop := x = 0 ∨ x = 1

/-- A bit as a `K` value. -/
noncomputable def bitK (b : Bool) : K := if b then 1 else 0

theorem IsBit.exists {x : K} (h : IsBit x) : ∃ b, x = bitK b := by
  rcases h with rfl | rfl
  · exact ⟨false, by simp [bitK]⟩
  · exact ⟨true, by simp [bitK]⟩

/-- The counter word's low limb: the start bit, then the kind bits `b0`, `b1`, `pair` at codes 2, 4, 8. -/
noncomputable def code (σ : Bool) (b0 b1 p : K) : K := bitK σ + ofWord 2 * b0 + ofWord 4 * b1 + ofWord 8 * p

/-- The code's word. -/
def codeN (σ b0 b1 p : Bool) : ℕ :=
  (if σ then 1 else 0) ^^^ (if b0 then 2 else 0) ^^^ (if b1 then 4 else 0) ^^^ (if p then 8 else 0)

theorem ofWord_add {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : ofWord a + ofWord b = ofWord (a ^^^ b) := by
  have hab : a ^^^ b < 2 ^ 64 := Nat.xor_lt_two_pow ha hb
  simp only [ofWord, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hab, ev_xor]

theorem ofWord_zero' : ofWord 0 = 0 := by simp [ofWord, ev_zero]

theorem ofWord_one' : ofWord 1 = 1 := by simp [ofWord, ev_one]

theorem bitK_eq (x : Bool) : bitK x = ofWord (if x then 1 else 0) := by
  cases x <;> simp [bitK, ofWord_zero', ofWord_one']

theorem mul_bitK (c : ℕ) (x : Bool) : ofWord c * bitK x = ofWord (if x then c else 0) := by
  cases x <;> simp [bitK, ofWord_zero']

theorem ofWord_add16 {a b : ℕ} (ha : a < 16) (hb : b < 16) : ofWord a + ofWord b = ofWord (a ^^^ b) :=
  ofWord_add (by omega) (by omega)

theorem code_bits (σ b0 b1 p : Bool) : code σ (bitK b0) (bitK b1) (bitK p) = ofWord (codeN σ b0 b1 p) := by
  rw [code, bitK_eq, mul_bitK, mul_bitK, mul_bitK]
  cases σ <;> cases b0 <;> cases b1 <;> cases p <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> rw [ofWord_add16, ofWord_add16, ofWord_add16] <;>
    first | rfl | decide

theorem codeN_lt (σ b0 b1 p : Bool) : codeN σ b0 b1 p < 2 ^ 64 := by
  cases σ <;> cases b0 <;> cases b1 <;> cases p <;> decide

theorem codeN_inj : ∀ σ b0 b1 p σ' b0' b1' p' : Bool, codeN σ b0 b1 p = codeN σ' b0' b1' p' →
    σ = σ' ∧ b0 = b0' ∧ b1 = b1' ∧ p = p' := by decide

theorem bitK_inj {a b : Bool} (h : bitK a = bitK b) : a = b := by
  cases a <;> cases b <;> simp_all [bitK]

/-- A counter limb names its start and kind bits. -/
theorem code_inj {σ σ' : Bool} {b0 b1 p b0' b1' p' : K} (h0 : IsBit b0) (h1 : IsBit b1) (hp : IsBit p)
    (h0' : IsBit b0') (h1' : IsBit b1') (hp' : IsBit p') (h : code σ b0 b1 p = code σ' b0' b1' p') :
    σ = σ' ∧ b0 = b0' ∧ b1 = b1' ∧ p = p' := by
  obtain ⟨c0, rfl⟩ := h0.exists
  obtain ⟨c1, rfl⟩ := h1.exists
  obtain ⟨cp, rfl⟩ := hp.exists
  obtain ⟨c0', rfl⟩ := h0'.exists
  obtain ⟨c1', rfl⟩ := h1'.exists
  obtain ⟨cp', rfl⟩ := hp'.exists
  rw [code_bits, code_bits] at h
  have := congrArg toWord h
  rw [toWord_ofWord _ (codeN_lt ..), toWord_ofWord _ (codeN_lt ..)] at this
  obtain ⟨rfl, rfl, rfl, rfl⟩ := codeN_inj _ _ _ _ _ _ _ _ this
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! One assignment's pool. -/

/-- One assignment's values of a pool's items: the kind bits, and each item's row's input ports (the counter and
finalization words' limbs, the chaining value's four words, the block's eight words) and output ports. -/
structure Vals where
  b0 : ℕ → K
  b1 : ℕ → K
  p : ℕ → K
  ins : ℕ → ℕ → K
  outs : ℕ → ℕ → K

/-- An item's padding bit. -/
noncomputable def Vals.pad (v : Vals) (i : ℕ) : K := v.b0 i * v.b1 i

/-- An item's end bit. -/
noncomputable def Vals.isEnd (v : Vals) (i : ℕ) : K := v.b1 i + v.b0 i * v.b1 i

/-- An output's two 128-bit halves, as `E` elements. -/
noncomputable def halves (o : ℕ → K) : E × E := (toE (o 0) (o 1) 0, toE (o 2) (o 3) 0)

/-- What a pool's rows say of one assignment: `n` items, `σ` the items that start a run, `X` the halves of the
digest each item's run must end in. -/
structure Sem (n : ℕ) (σ : ℕ → Bool) (X : ℕ → E × E) (v : Vals) : Prop where
  bits : ∀ i < n, IsBit (v.b0 i) ∧ IsBit (v.b1 i) ∧ IsBit (v.p i)
  counter : ∀ i < n, v.ins i 0 = code (σ i) (v.b0 i) (v.b1 i) (v.p i)
  chain : ∀ i < n, 0 < i → σ i = false → ∀ k < 4, v.ins i (2 + k) = v.outs (i - 1) k
  startPad : ∀ i < n, σ i = true → v.pad i = 0
  startEnded : ∀ i < n, 0 < i → σ i = true → v.b1 (i - 1) = 1
  padAfter : ∀ i < n, 0 < i → σ i = false → v.pad i = v.b1 (i - 1)
  last : v.b1 (n - 1) = 1
  pair : ∀ i < n, v.p i = (v.b0 i + v.pad i) * v.p i
  ends : ∀ i < n, v.isEnd i = 1 → halves (v.outs i) = X i


/-- `Sem` reads `σ` and `X` only at the pool's items. -/
theorem Sem.congr {σ' : ℕ → Bool} {X' : ℕ → E × E} (h : Sem n σ X v) (hσ : ∀ i < n, σ i = σ' i)
    (hX : ∀ i < n, X i = X' i) : Sem n σ' X' v where
  bits := h.bits
  counter i hi := by rw [← hσ i hi]; exact h.counter i hi
  chain i hi hi0 hs := h.chain i hi hi0 (by rw [hσ i hi]; exact hs)
  startPad i hi hs := h.startPad i hi (by rw [hσ i hi]; exact hs)
  startEnded i hi hi0 hs := h.startEnded i hi hi0 (by rw [hσ i hi]; exact hs)
  padAfter i hi hi0 hs := h.padAfter i hi hi0 (by rw [hσ i hi]; exact hs)
  last := h.last
  pair := h.pair
  ends i hi he := by rw [← hX i hi]; exact h.ends i hi he

/-! Runs. -/

/-- The start of item `i`'s run: the last item up to it that starts one. -/
def seg (σ : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if σ (i + 1) then i + 1 else seg σ i

theorem seg_le (σ : ℕ → Bool) : ∀ i, seg σ i ≤ i
  | 0 => le_rfl
  | i + 1 => by
    unfold seg
    split
    · exact le_rfl
    · exact (seg_le σ i).trans (Nat.le_succ i)

theorem seg_true {σ : ℕ → Bool} {i : ℕ} (h : σ i = true) : seg σ i = i := by
  cases i with
  | zero => rfl
  | succ i => simp [seg, h]

theorem seg_false {σ : ℕ → Bool} {i : ℕ} (h : σ (i + 1) = false) : seg σ (i + 1) = seg σ i := by
  simp [seg, h]

/-- A run's items share their expected digest. -/
theorem X_seg {n : ℕ} {σ : ℕ → Bool} {X : ℕ → E × E} (steady : ∀ i < n, 0 < i → σ i = false → X i = X (i - 1)) :
    ∀ i < n, X i = X (seg σ i)
  | 0, _ => rfl
  | i + 1, hi => by
    cases hσ : σ (i + 1) with
    | true => rw [seg_true hσ]
    | false =>
      rw [seg_false hσ, steady (i + 1) hi (Nat.succ_pos i) hσ, Nat.add_sub_cancel]
      exact X_seg steady i (by omega)

theorem two_K' : (1 : K) + 1 = 0 := by rw [← two_K]; norm_num

section Bits

variable {b0 b1 : K}

theorem pad_one (h0 : IsBit b0) (h1 : IsBit b1) (h : b0 * b1 = 1) : b0 = 1 ∧ b1 = 1 := by
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> simp_all

theorem end_one (h1 : b1 = 1) (h : b0 * b1 = 0) : b1 + b0 * b1 = 1 := by
  rw [h, add_zero, h1]

theorem pad_bit (h0 : IsBit b0) (h1 : IsBit b1) : IsBit (b0 * b1) := by
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> simp [IsBit]

end Bits

variable {n : ℕ} {σ : ℕ → Bool} {X : ℕ → E × E} {v v' : Vals}

/-- An item before its run's end: the end comes later in the run. -/
theorem end_after (hS : Sem n σ X v) :
    ∀ d i, n - i = d → i < n → v.b1 i = 0 →
      ∃ e < n, i < e ∧ seg σ e = seg σ i ∧ v.b1 e = 1 ∧ v.pad e = 0 := by
  intro d
  induction d with
  | zero => intro i hd hi; omega
  | succ d ih =>
    intro i hd hi hb
    have hi1 : i + 1 < n := by
      by_contra hc
      have : i = n - 1 := by omega
      rw [this, hS.last] at hb
      exact one_ne_zero hb
    have hσ : σ (i + 1) = false := by
      cases hs : σ (i + 1) with
      | false => rfl
      | true =>
        have := hS.startEnded (i + 1) hi1 (Nat.succ_pos i) hs
        rw [Nat.add_sub_cancel, hb] at this
        exact absurd this zero_ne_one
    have hpad : v.pad (i + 1) = 0 := by
      rw [hS.padAfter (i + 1) hi1 (Nat.succ_pos i) hσ, Nat.add_sub_cancel, hb]
    rcases (hS.bits (i + 1) hi1).2.1 with h | h
    · obtain ⟨e, he, hie, hseg, h1, h0⟩ := ih (i + 1) (by omega) hi1 h
      exact ⟨e, he, by omega, by rw [hseg, seg_false hσ], h1, h0⟩
    · exact ⟨i + 1, hi1, Nat.lt_succ_self i, seg_false hσ, h, hpad⟩

/-- Every item's run has an end, and the item is at or before it, or padding. -/
theorem end_exists (hS : Sem n σ X v) (hσ0 : σ 0 = true) :
    ∀ i < n, ∃ e < n, seg σ e = seg σ i ∧ v.b1 e = 1 ∧ v.pad e = 0 ∧ (i ≤ e ∨ v.pad i = 1)
  | i, hi => by
    obtain ⟨h0, h1, -⟩ := hS.bits i hi
    rcases h1 with hb | hb
    · obtain ⟨e, he, hie, hseg, h1, hp⟩ := end_after hS _ i rfl hi hb
      exact ⟨e, he, hseg, h1, hp, Or.inl hie.le⟩
    · rcases pad_bit h0 (Or.inr hb) with hp | hp
      · exact ⟨i, hi, rfl, hb, hp, Or.inl le_rfl⟩
      · have hσ : σ i = false := by
          cases hs : σ i with
          | false => rfl
          | true => have := hS.startPad i hi hs; rw [Vals.pad] at this; rw [this] at hp; exact absurd hp zero_ne_one
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := by
          cases i with
          | zero => rw [hσ0] at hσ; exact absurd hσ (by decide)
          | succ i' => exact ⟨i', rfl⟩
        obtain ⟨e, he, hseg, h1, hpe, -⟩ := end_exists hS hσ0 i' (by omega)
        exact ⟨e, he, by rw [hseg, seg_false hσ], h1, hpe, Or.inr hp⟩

/-- Two items of one run whose outputs agree across the two assignments are the same item, and the rows from the
run's start up to it have the same inputs, unless two compressions collide. -/
theorem chain_eq (hS : Sem n σ X v) (hS' : Sem n σ X v') (hσ0 : σ 0 = true)
    (hcr : ∀ i < n, ∀ j < n, (∀ k < 4, v.outs i k = v'.outs j k) → ∀ c < 14, v.ins i c = v'.ins j c) :
    ∀ i < n, ∀ j < n, seg σ i = seg σ j → (∀ k < 4, v.outs i k = v'.outs j k) →
      i = j ∧ ∀ l, seg σ i ≤ l → l ≤ i → ∀ c < 14, v.ins l c = v'.ins l c
  | i, hi, j, hj, hseg, hout => by
    have hin := hcr i hi j hj hout
    have hcode := hin 0 (by norm_num)
    rw [hS.counter i hi, hS'.counter j hj] at hcode
    obtain ⟨b0, b1, bp⟩ := hS.bits i hi
    obtain ⟨b0', b1', bp'⟩ := hS'.bits j hj
    obtain ⟨hσ, -⟩ := code_inj b0 b1 bp b0' b1' bp' hcode
    cases hs : σ i with
    | true =>
      have hj' : σ j = true := hσ ▸ hs
      rw [seg_true hs, seg_true hj'] at hseg
      subst hseg
      refine ⟨rfl, fun l hl hl' => ?_⟩
      rw [seg_true hs] at hl
      obtain rfl : l = i := le_antisymm hl' hl
      exact hin
    | false =>
      have hj' : σ j = false := hσ ▸ hs
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := by
        cases i with
        | zero => rw [hσ0] at hs; exact absurd hs (by decide)
        | succ i' => exact ⟨i', rfl⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := by
        cases j with
        | zero => rw [hσ0] at hj'; exact absurd hj' (by decide)
        | succ j' => exact ⟨j', rfl⟩
      rw [seg_false hs, seg_false hj'] at hseg
      have hout' : ∀ k < 4, v.outs i' k = v'.outs j' k := by
        intro k hk
        have := hin (2 + k) (by omega)
        rw [hS.chain (i' + 1) hi (Nat.succ_pos i') hs k hk, hS'.chain (j' + 1) hj (Nat.succ_pos j') hj' k hk,
          Nat.add_sub_cancel, Nat.add_sub_cancel] at this
        exact this
      obtain ⟨rfl, hrest⟩ := chain_eq hS hS' hσ0 hcr i' (by omega) j' (by omega) hseg hout'
      refine ⟨rfl, fun l hl hl' => ?_⟩
      rw [seg_false hs] at hl
      rcases Nat.lt_or_ge l (i' + 1) with h | h
      · exact hrest l hl (by omega)
      · obtain rfl : l = i' + 1 := le_antisymm hl' h
        exact hin

theorem halves_inj {o o' : ℕ → K} (h : halves o = halves o') : ∀ k < 4, o k = o' k := by
  simp only [halves, Prod.mk.injEq] at h
  obtain ⟨a0, a1, -⟩ := toE_injective _ _ _ _ _ _ h.1
  obtain ⟨c0, c1, -⟩ := toE_injective _ _ _ _ _ _ h.2
  intro k hk
  interval_cases k <;> assumption

/-- Parse uniqueness: two assignments of one pool, with the same run starts and expected digests, whose compressions
do not collide, give every item the same kind bits, and every item but padding the same row inputs. -/
theorem parse_unique (hS : Sem n σ X v) (hS' : Sem n σ X v') (hσ0 : σ 0 = true)
    (steady : ∀ i < n, 0 < i → σ i = false → X i = X (i - 1))
    (hcr : ∀ i < n, ∀ j < n, (∀ k < 4, v.outs i k = v'.outs j k) → ∀ c < 14, v.ins i c = v'.ins j c) :
    ∀ i < n, v.b0 i = v'.b0 i ∧ v.b1 i = v'.b1 i ∧ v.p i = v'.p i ∧
      (v.pad i = 0 → ∀ c < 14, v.ins i c = v'.ins i c) := by
  intro i hi
  obtain ⟨e, he, hseg, h1, hp, hie⟩ := end_exists hS hσ0 i hi
  obtain ⟨e', he', hseg', h1', hp', hie'⟩ := end_exists hS' hσ0 i hi
  have hx : halves (v.outs e) = halves (v'.outs e') := by
    rw [hS.ends e he (end_one h1 hp), hS'.ends e' he' (end_one h1' hp'),
      X_seg steady e he, X_seg steady e' he', hseg, hseg']
  obtain ⟨rfl, hins⟩ := chain_eq hS hS' hσ0 hcr e he e' he' (hseg.trans hseg'.symm) (halves_inj hx)
  by_cases hle : i ≤ e
  · have hin := hins i (hseg ▸ seg_le σ i) hle
    have hcode := hin 0 (by norm_num)
    rw [hS.counter i hi, hS'.counter i hi] at hcode
    obtain ⟨b0, b1, bp⟩ := hS.bits i hi
    obtain ⟨b0', b1', bp'⟩ := hS'.bits i hi
    obtain ⟨-, r0, r1, rp⟩ := code_inj b0 b1 bp b0' b1' bp' hcode
    exact ⟨r0, r1, rp, fun _ => hin⟩
  · have hpd := hie.resolve_left hle
    have hpd' := hie'.resolve_left hle
    obtain ⟨a0, a1⟩ := pad_one (hS.bits i hi).1 (hS.bits i hi).2.1 hpd
    obtain ⟨a0', a1'⟩ := pad_one (hS'.bits i hi).1 (hS'.bits i hi).2.1 hpd'
    have hpz : ∀ {w : Vals}, Sem n σ X w → w.pad i = 1 → w.b0 i = 1 → w.p i = 0 := by
      intro w hw hpw hb
      have := hw.pair i hi
      rw [hpw, hb, two_K', zero_mul] at this
      exact this
    refine ⟨a0.trans a0'.symm, a1.trans a1'.symm, (hpz hS hpd a0).trans (hpz hS' hpd' a0').symm, fun h => ?_⟩
    rw [hpd] at h
    exact absurd h one_ne_zero

end LeanVMCircuits.Rec.PoolParse
