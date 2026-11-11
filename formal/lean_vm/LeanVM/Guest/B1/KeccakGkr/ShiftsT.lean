/-
  LeanVM.Guest.B1.KeccakGkr.ShiftsT

  `keccak_shifts_eq`'s statements (`shiftsT`, G:2556-2609) compute the shift sums
  `Σ_z eq(a, z + r) eq(b, z)`.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT
public import LeanVM.Guest.B1.KeccakGkr.ShiftMath

/-!
# `keccak_shifts_eq`

`carryT_holds`: a `carry_step` extends the carry sums `carryK` by one bit; `carryWrapT_holds`: a
`carry_wrap` gives both carries, `modK`; `shOutT_holds`: the used shifts combine the low and the
high bits. `shiftsT_holds`: from the two points' first six coordinates, read at `aP` and `bP`, the
shift `r`'s value is `Σ_z eq(a, (z + r) mod 64)·eq(b, z)`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- **One bit's weights** (G:2577-2595): `e = (1 + a)(1 + b) + ab = 1 + a + b`, and below the
top bit `u = a(1 + b) = a + ab`, `v = (1 + a)b = b + ab`, at the top bit `s = a + b`. -/
theorem bitT_holds {aP bP : V} {t B : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (bitT aP bP t B) next kret) :
    LoadHolds rd (σ aP) t (σ (.n B)) ∧ LoadHolds rd (σ bP) t (σ (.n (B + 1))) ∧
      σ (.n (B + 8)) = 1 + σ (.n B) + σ (.n (B + 1)) ∧
      (t = 5 → σ (.n (B + 9)) = σ (.n B) + σ (.n (B + 1))) ∧
      (t ≠ 5 → σ (.n (B + 9)) = σ (.n B) + σ (.n B) * σ (.n (B + 1)) ∧
        σ (.n (B + 10)) = σ (.n (B + 1)) + σ (.n B) * σ (.n (B + 1))) ∧ next := by
  rw [bitT, holdsList_append] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨la, lb, e2, e3, e4, e5, e6, e7, e8, h⟩ := h
  have he : σ (.n (B + 8)) = 1 + σ (.n B) + σ (.n (B + 1)) := by
    rw [e8, e6, e7, e3, e5, e2, e4, word_one]
    have : (1 + σ (.n B)) * (1 + σ (.n (B + 1))) + σ (.n B) * σ (.n (B + 1)) =
        1 + σ (.n B) + σ (.n (B + 1)) + (σ (.n B) * σ (.n (B + 1)) + σ (.n B) * σ (.n (B + 1))) := by
      ring
    rw [this, e_add_self, add_zero]
  by_cases ht : t = 5
  · simp only [ht, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
    exact ⟨la, lb, he, fun _ ↦ h.1, fun h' ↦ absurd ht h', h.2⟩
  · simp only [ht, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
    obtain ⟨e9, e10, hn⟩ := h
    refine ⟨la, lb, he, fun h' ↦ absurd h' ht, fun _ ↦ ⟨?_, ?_⟩, hn⟩
    · rw [e9, e5, e4, word_one]; ring
    · rw [e10, e3, e2, word_one]; ring

/-- **A `carry_step`** (G:2530-2544): from the carry sums of `t` bits, those of `t + 1`. -/
theorem carryT_holds {c0 c1 : ℕ → ℕ} {e u v t B : ℕ} {as bs : List E} {α β : E}
    (hl : bs.length = as.length) (ht : as.length = t)
    (hc0 : ∀ p < 2 ^ t, σ (.n (c0 p)) = carryK as bs 0 p)
    (hc1 : ∀ p, 1 ≤ p → p < 2 ^ t → σ (.n (c1 p)) = carryK as bs 1 p)
    (he : σ (.n e) = 1 + α + β) (hu : σ (.n u) = α + α * β) (hv : σ (.n v) = β + α * β)
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (carryT c0 c1 e u v t B) next kret) :
    (∀ q < 2 ^ (t + 1), σ (.n (carryN0 t B q)) = carryK (as ++ [α]) (bs ++ [β]) 0 q) ∧
      (∀ q, 1 ≤ q → q < 2 ^ (t + 1) →
        σ (.n (carryN1 t B q)) = carryK (as ++ [α]) (bs ++ [β]) 1 q) ∧ next := by
  subst ht
  rw [carryT, holdsList_append, holdsList_range_flatten _ _ (fun _ ↦ rfl)] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨m0, m1, m2, hblk, hn⟩ := h
  obtain ⟨w000, w001, w100, w101, w010, w011, w110, w111⟩ := carryW_vals α β
  have k10 := carryK_one_zero as bs
  have hpos : (2 : ℕ) ^ as.length ≠ 0 := by positivity
  have snoc : ∀ p r c', p < 2 ^ as.length → r < 2 → c' < 2 →
      carryK (as ++ [α]) (bs ++ [β]) c' (p + 2 ^ as.length * r) =
        carryK as bs 0 p * carryW α β 0 r c' + carryK as bs 1 p * carryW α β 1 r c' :=
    fun p r c' hp hr hc ↦ carryK_snoc as bs hl α β hp hr hc
  have blk : ∀ i < 2 ^ as.length - 1,
      σ (.n (B + 5 + 8 * i)) = σ (.n (c0 (i + 1))) * σ (.n e) + σ (.n (c1 (i + 1))) * σ (.n u) ∧
      σ (.n (B + 6 + 8 * i)) = σ (.n (c1 (i + 1))) * σ (.n v) ∧
      σ (.n (B + 7 + 8 * i)) = σ (.n (c0 (i + 1))) * σ (.n u) ∧
      σ (.n (B + 10 + 8 * i)) = σ (.n (c0 (i + 1))) * σ (.n v) +
        σ (.n (c1 (i + 1))) * σ (.n e) := by
    intro i hi
    obtain ⟨b3, b4, b5, b6, b7, b8, b9, b10, -⟩ := hblk i hi
    exact ⟨by rw [b5, b3, b4], b6, b7, by rw [b10, b8, b9]⟩
  refine ⟨fun q hq ↦ ?_, fun q hq1 hq ↦ ?_, hn⟩
  · rw [pow_succ] at hq
    rcases (show q = 0 ∨ q = 2 ^ as.length ∨ (1 ≤ q ∧ q < 2 ^ as.length) ∨
        (2 ^ as.length < q) by omega) with rfl | rfl | ⟨h1, h2⟩ | h3
    · have := snoc 0 0 0 (by omega) (by omega) (by omega)
      simp only [mul_zero, add_zero] at this
      simp only [carryN0, ↓reduceIte]
      rw [this, m0, hc0 0 (by omega), he, w000, k10]
      ring
    · have := snoc 0 1 0 (by omega) (by omega) (by omega)
      simp only [mul_one, zero_add] at this
      simp only [carryN0, hpos, ↓reduceIte]
      rw [this, m1, hc0 0 (by omega), hu, w010, k10]
      ring
    · have := snoc q 0 0 (by omega) (by omega) (by omega)
      simp only [mul_zero, add_zero] at this
      obtain ⟨b5, -, -, -⟩ := blk (q - 1) (by omega)
      simp only [show q ≠ 0 by omega, show q ≠ 2 ^ as.length by omega, h2, carryN0, ↓reduceIte]
      rw [this, b5, show q - 1 + 1 = q by omega, hc0 q h2, hc1 q h1 h2, he, hu, w000, w100]
    · have := snoc (q - 2 ^ as.length) 1 0 (by omega) (by omega) (by omega)
      rw [show q - 2 ^ as.length + 2 ^ as.length * 1 = q by omega] at this
      obtain ⟨-, -, b7, -⟩ := blk (q - 2 ^ as.length - 1) (by omega)
      simp only [show q ≠ 0 by omega, show q ≠ 2 ^ as.length by omega,
        show ¬ q < 2 ^ as.length by omega, carryN0, ↓reduceIte]
      rw [this, b7, show q - 2 ^ as.length - 1 + 1 = q - 2 ^ as.length by omega,
        hc0 _ (by omega), hu, w010, w110]
      ring
  · rw [pow_succ] at hq
    rcases (show q = 2 ^ as.length ∨ (1 ≤ q ∧ q < 2 ^ as.length) ∨
        (2 ^ as.length < q) by omega) with rfl | ⟨h1, h2⟩ | h3
    · have := snoc 0 1 1 (by omega) (by omega) (by omega)
      simp only [mul_one, zero_add] at this
      simp only [carryN1, ↓reduceIte]
      rw [this, m2, hc0 0 (by omega), hv, w011, k10]
      ring
    · have := snoc q 0 1 (by omega) (by omega) (by omega)
      simp only [mul_zero, add_zero] at this
      obtain ⟨-, b6, -, -⟩ := blk (q - 1) (by omega)
      simp only [show q ≠ 2 ^ as.length by omega, h2, carryN1, ↓reduceIte]
      rw [this, b6, show q - 1 + 1 = q by omega, hc1 q h1 h2, hv, w001, w101]
      ring
    · have := snoc (q - 2 ^ as.length) 1 1 (by omega) (by omega) (by omega)
      rw [show q - 2 ^ as.length + 2 ^ as.length * 1 = q by omega] at this
      obtain ⟨-, -, -, b10⟩ := blk (q - 2 ^ as.length - 1) (by omega)
      simp only [show q ≠ 2 ^ as.length by omega, show ¬ q < 2 ^ as.length by omega, carryN1,
        ↓reduceIte]
      rw [this, b10, show q - 2 ^ as.length - 1 + 1 = q - 2 ^ as.length by omega,
        hc0 _ (by omega), hc1 _ (by omega) (by omega), hv, he, w011, w111]

theorem uv_sum (α β : E) : (α + α * β) + (β + α * β) = α + β := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  linear_combination (α * β) * h2

/-- **A `carry_wrap`** (G:2548-2557): the last bit, both carries out (`modK`). -/
theorem carryWrapT_holds {c0 c1 : ℕ → ℕ} {e s t B : ℕ} {as bs : List E} {α β : E}
    (hl : bs.length = as.length) (ht : as.length = t)
    (hc0 : ∀ p < 2 ^ t, σ (.n (c0 p)) = carryK as bs 0 p)
    (hc1 : ∀ p, 1 ≤ p → p < 2 ^ t → σ (.n (c1 p)) = carryK as bs 1 p)
    (he : σ (.n e) = 1 + α + β) (hs : σ (.n s) = α + β)
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (carryWrapT c0 c1 e s t B) next kret) :
    (∀ q < 2 ^ (t + 1), σ (.n (wrapOut t B q)) = modK (as ++ [α]) (bs ++ [β]) q) ∧ next := by
  subst ht
  rw [carryWrapT, holdsList_append, holdsList_range_flatten _ _ (fun _ ↦ rfl)] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨m0, m1, hblk, hn⟩ := h
  obtain ⟨w000, w001, w100, w101, w010, w011, w110, w111⟩ := carryW_vals α β
  have k10 := carryK_one_zero as bs
  have hpos : (2 : ℕ) ^ as.length ≠ 0 := by positivity
  have hlen : (as ++ [α]).length = as.length + 1 := by simp
  have both : ∀ p r, p < 2 ^ as.length → r < 2 →
      modK (as ++ [α]) (bs ++ [β]) (p + 2 ^ as.length * r) =
        carryK as bs 0 p * (carryW α β 0 r 0 + carryW α β 0 r 1) +
          carryK as bs 1 p * (carryW α β 1 r 0 + carryW α β 1 r 1) := by
    intro p r hp hr
    rw [modK_eq _ _ (by rw [hlen, pow_succ]; rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;> omega), carryK_snoc as bs hl α β hp hr (by omega),
      carryK_snoc as bs hl α β hp hr (by omega)]
    ring
  refine ⟨fun q hq ↦ ?_, hn⟩
  rw [pow_succ] at hq
  rcases (show q = 0 ∨ q = 2 ^ as.length ∨ (1 ≤ q ∧ q < 2 ^ as.length) ∨
      (2 ^ as.length < q) by omega) with rfl | rfl | ⟨h1, h2⟩ | h3
  · have := both 0 0 (by omega) (by omega)
    simp only [mul_zero, add_zero] at this
    simp only [wrapOut, ↓reduceIte]
    rw [this, m0, hc0 0 (by omega), he, w000, w001, k10]
    ring
  · have := both 0 1 (by omega) (by omega)
    simp only [mul_one, zero_add] at this
    simp only [wrapOut, hpos, ↓reduceIte]
    rw [this, m1, hc0 0 (by omega), hs, w010, w011, k10, uv_sum]
    ring
  · have := both q 0 (by omega) (by omega)
    simp only [mul_zero, add_zero] at this
    obtain ⟨b2, b3, b4, -, -, -, -⟩ := hblk (q - 1) (by omega)
    simp only [show q ≠ 0 by omega, show q ≠ 2 ^ as.length by omega, h2, wrapOut, ↓reduceIte]
    rw [this, show B + 4 + 6 * (q - 1) = B + 4 + 6 * (q - 1) from rfl, b4, b2, b3,
      show q - 1 + 1 = q by omega, hc0 q h2, hc1 q h1 h2, he, hs, w000, w001, w100, w101, uv_sum]
    ring
  · have := both (q - 2 ^ as.length) 1 (by omega) (by omega)
    rw [show q - 2 ^ as.length + 2 ^ as.length * 1 = q by omega] at this
    obtain ⟨-, -, -, b5, b6, b7, -⟩ := hblk (q - 2 ^ as.length - 1) (by omega)
    simp only [show q ≠ 0 by omega, show q ≠ 2 ^ as.length by omega,
      show ¬ q < 2 ^ as.length by omega, wrapOut, ↓reduceIte]
    rw [this, b7, b5, b6, show q - 2 ^ as.length - 1 + 1 = q - 2 ^ as.length by omega,
      hc0 _ (by omega), hc1 _ (by omega) (by omega), he, hs, w010, w011, w110, w111, uv_sum]
    ring

/-- **The used shifts** (G:2599-2604). -/
theorem shOutT_holds {low0 low1 high : ℕ → ℕ} : ∀ (rs : List ℕ) (b : ℕ) {next : Prop}
    {kret : List E → Prop}, Stmt.HoldsList C rd σ (shOutT low0 low1 high rs b) next kret →
    (∀ r ∈ rs, σ (.n (shOutV rs b r)) = σ (.n (low0 (r % 8))) * σ (.n (high (r / 8))) +
      (if r % 8 = 0 then 0 else σ (.n (low1 (r % 8))) * σ (.n (high ((r / 8 + 1) % 8))))) ∧ next
  | [], _, _, _, h => ⟨fun _ hr ↦ absurd hr (by simp), h⟩
  | r :: rs, b, next, kret, h => by
    by_cases h0 : r % 8 = 0
    · simp only [shOutT, h0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
      obtain ⟨e, h⟩ := h
      obtain ⟨ih, hn⟩ := shOutT_holds rs (b + 1) h
      refine ⟨fun q hq ↦ ?_, hn⟩
      by_cases hqr : q = r
      · subst hqr
        simp only [shOutV, h0, ↓reduceIte, e, add_zero]
      · simp only [shOutV, h0, hqr, ↓reduceIte]
        exact ih q (by simpa [hqr] using hq)
    · simp only [shOutT, h0, ↓reduceIte, holdsList_append, Stmt.HoldsList, Stmt.Holds,
        Atom.Holds] at h
      obtain ⟨e0, e1, e2, h⟩ := h
      obtain ⟨ih, hn⟩ := shOutT_holds rs (b + 3) h
      refine ⟨fun q hq ↦ ?_, hn⟩
      by_cases hqr : q = r
      · subst hqr
        simp only [shOutV, h0, ↓reduceIte, e2, e0, e1]
      · simp only [shOutV, h0, hqr, ↓reduceIte]
        exact ih q (by simpa [hqr] using hq)

theorem carryK_single (α β : E) {c r : ℕ} (hr : r < 2) (hc : c < 2) :
    carryK [α] [β] c r = carryW α β 0 r c := by
  have := carryK_snoc [] [] rfl α β (p := 0) (r := r) (c' := c) (by simp) hr hc
  simpa [carryK_nil, carryK_one_zero] using this

theorem shiftUsed_lt : ∀ r ∈ shiftUsed, r < 64 := by decide

/-- **`keccak_shifts_eq`** (G:2561-2615): the points' first six coordinates read at `aP`, `bP`,
and every used shift `r`'s value `Σ_z eq(a, (z + r) mod 64)·eq(b, z)`. -/
theorem shiftsT_holds {aP bP : V} {B0 : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (shiftsT aP bP B0) next kret) :
    (∀ t < 6, LoadHolds rd (σ aP) t (σ (.n (B0 + 11 * t))) ∧
      LoadHolds rd (σ bP) t (σ (.n (B0 + 11 * t + 1)))) ∧
    (∀ r ∈ shiftUsed, σ (.n (shiftsV B0 r)) = ∑ z ∈ range 64,
      eqAt ((List.range 6).map fun t ↦ σ (.n (B0 + 11 * t))) ((z + r) % 64) *
        eqAt ((List.range 6).map fun t ↦ σ (.n (B0 + 11 * t + 1))) z) ∧ next := by
  rw [shiftsT, holdsList_append, holdsList_append, holdsList_append, holdsList_append,
    holdsList_append, holdsList_range_flatten _ _ (fun t ↦ by
      unfold bitT; split <;> rfl)] at h
  obtain ⟨hbits, h⟩ := h
  have bit := fun t (ht : t < 6) ↦ bitT_holds (hbits t ht)
  set a : ℕ → E := fun t ↦ σ (.n (B0 + 11 * t)) with ha
  set b : ℕ → E := fun t ↦ σ (.n (B0 + 11 * t + 1)) with hb
  have be : ∀ t < 6, σ (.n (bitEv B0 t)) = 1 + a t + b t := fun t ht ↦ by
    have := (bit t ht).2.2.1
    exact this
  have bu : ∀ t < 5, σ (.n (bitUv B0 t)) = a t + a t * b t := fun t ht ↦ by
    have := ((bit t (by omega)).2.2.2.2.1 (by omega)).1
    exact this
  have bv : ∀ t < 5, σ (.n (bitVv B0 t)) = b t + a t * b t := fun t ht ↦ by
    have := ((bit t (by omega)).2.2.2.2.1 (by omega)).2
    exact this
  have bs : σ (.n (bitSv B0 5)) = a 5 + b 5 := by
    have := (bit 5 (by omega)).2.2.2.1 rfl
    exact this
  obtain ⟨w000, w001, w100, w101, w010, w011, w110, w111⟩ := carryW_vals (a 0) (b 0)
  obtain ⟨x000, -, -, -, x010, x011, -, -⟩ := carryW_vals (a 3) (b 3)
  -- the low bits
  obtain ⟨m0, m1, h⟩ := carryT_holds (t := 1) (as := [a 0]) (bs := [b 0]) (α := a 1) (β := b 1) rfl rfl
    (fun p hp ↦ by
      interval_cases p
      · simp only [↓reduceIte]; rw [be 0 (by omega), carryK_single _ _ (by omega) (by omega), w000]
      · simp only [one_ne_zero, ↓reduceIte]
        rw [bu 0 (by omega), carryK_single _ _ (by omega) (by omega), w010])
    (fun p hp1 hp ↦ by
      obtain rfl : p = 1 := by simp at hp; omega
      rw [bv 0 (by omega), carryK_single _ _ (by omega) (by omega), w011])
    (be 1 (by omega)) (bu 1 (by omega)) (bv 1 (by omega)) h
  obtain ⟨l0, l1, h⟩ := carryT_holds (t := 2) (as := [a 0] ++ [a 1]) (bs := [b 0] ++ [b 1]) (α := a 2)
    (β := b 2) rfl rfl m0 m1 (be 2 (by omega)) (bu 2 (by omega)) (bv 2 (by omega)) h
  -- the high bits
  obtain ⟨n0, n1, h⟩ := carryT_holds (t := 1) (as := [a 3]) (bs := [b 3]) (α := a 4) (β := b 4) rfl rfl
    (fun p hp ↦ by
      interval_cases p
      · simp only [↓reduceIte]; rw [be 3 (by omega), carryK_single _ _ (by omega) (by omega), x000]
      · simp only [one_ne_zero, ↓reduceIte]
        rw [bu 3 (by omega), carryK_single _ _ (by omega) (by omega), x010])
    (fun p hp1 hp ↦ by
      obtain rfl : p = 1 := by simp at hp; omega
      rw [bv 3 (by omega), carryK_single _ _ (by omega) (by omega), x011])
    (be 4 (by omega)) (bu 4 (by omega)) (bv 4 (by omega)) h
  obtain ⟨hw, h⟩ := carryWrapT_holds (t := 2) (as := [a 3] ++ [a 4]) (bs := [b 3] ++ [b 4]) (α := a 5)
    (β := b 5) rfl rfl n0 n1 (be 5 (by omega)) bs h
  -- the shifts
  obtain ⟨hsh, hn⟩ := shOutT_holds shiftUsed (B0 + 134) h
  refine ⟨fun t ht ↦ ⟨(bit t ht).1, (bit t ht).2.1⟩, fun r hr ↦ ?_, hn⟩
  have hr64 := shiftUsed_lt r hr
  have hL : (List.range 6).map a = ([a 0] ++ [a 1] ++ [a 2]) ++ ([a 3] ++ [a 4] ++ [a 5]) := rfl
  have hR : (List.range 6).map b = ([b 0] ++ [b 1] ++ [b 2]) ++ ([b 3] ++ [b 4] ++ [b 5]) := rfl
  rw [shiftsV, hsh r hr, hL, hR, shiftSum_eq _ _ (by rfl),
    modK_split _ _ _ _ (by rfl) (by rfl) (by rfl), l0 (r % 8) (by norm_num; omega),
    hw (r / 8) (by norm_num; omega), hw ((r / 8 + 1) % 8) (by norm_num; omega),
    show r / 8 % 8 = r / 8 by omega]
  by_cases h0 : r % 8 = 0
  · simp only [h0, ↓reduceIte, add_zero, carryK_one_zero, zero_mul]
  · simp only [h0, ↓reduceIte]
    rw [l1 (r % 8) (by omega) (by norm_num; omega)]

end
end LeanVM.Guest.B1.VerifySub
