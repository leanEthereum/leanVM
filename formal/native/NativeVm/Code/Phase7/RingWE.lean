module

public import NativeVm.Code.Phase7.RingWloop

/-!
# `weightRing`: a ring-switched claim's weight at a point

`A := Placement.eqAbove ⟨vc, idx⟩ x · ringWeight r (x.take vc) c`, `StackWeight.eval (.ring p r c)`
on lists of `E`: the buffer filled (`ringSetup`), `eqAbove` stored (`ringAbove`), one pass of
`kBody` per coefficient, then the product of the two. Registers: `r` at `r13` (`r15` elements),
`x` at `r14` (`rbp`), `c` at `r11` (`r12`), the placement's index in `rsi` and variable count in
`rdx`, the buffer at `rbx`. It writes only the buffer's `bufWords` words.
-/

@[expose] public section

namespace NativeVm.Code.Ring

open Native NativeVm.Field LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeVm.Transcript (wdisp wdisp_toUInt64 wp_load wp_store wp_storei)

variable {s : QState} {F : QState → Prop}

/-- **A ring-switched claim's weight.** -/
def weightRing : Stmt := blk [
  ringSetup, ringAbove, I (.mov .rbp .r13), I (.movi .rsi 0), I (.load .rax (at_ .rbp (wdisp 1))),
  .loop (.cmp .ltu .rsi (.reg .rax)) kBody,
  I (.load .r11 (at_ .rbp (wdisp 4))), I (.load .r12 (at_ .rbp (wdisp 5))),
  I (.load .r9 (at_ .rbp (wdisp 6))), I (.load .r10 (at_ .rbp (wdisp 7))), emul]

theorem lane_zero0 : ((0 : E).limb 0).lane = 0 := by
  rw [← eOf_zero, limb0_eOf]; rfl

theorem lane_zero1 : ((0 : E).limb 1).lane = 0 := by
  rw [← eOf_zero, limb1_eOf]; rfl

theorem rwAt_zero (R C rP : List E) : rwAt R C rP 0 = (0, R) := by simp [rwAt]

theorem rwAt_all (R C rP : List E) : (rwAt R C rP C.length).1 = ringWeight R rP C := by
  rw [rwAt, List.take_length, ringWeight_eq]

theorem toNat_2k {k : Nat} (h : k < 2 ^ 32) : (2 * k).toUInt64.toNat = 2 * k :=
  toNat_toUInt64 (by omega)

/-- The loop over the coefficients. -/
theorem kLoop_spec {s0 t : QState} {b cp xp : UInt64} {R C X : List E} {vc m : Nat} {e : E}
    (hI : KInv s0 t b cp xp R C X vc m 0 e) (hm : m = min (min R.length vc) X.length)
    (hRl : R.length ≤ 36) (hCl : C.length < 2 ^ 32) (hC : EArr s0.mem cp C) (hX : EArr s0.mem xp X)
    (hsC : ∀ j < bufWords, ∀ i < 2 * C.length, ew b j ≠ ew cp i)
    (hsX : ∀ j < bufWords, ∀ i < 2 * X.length, ew b j ≠ ew xp i) :
    WP (.loop (.cmp .ltu .rsi (.reg .rax)) kBody) t
      (fun t' ↦ KInv s0 t' b cp xp R C X vc m C.length e) F := by
  apply WP.loop (fun u ↦ ∃ k, KInv s0 u b cp xp R C X vc m k e)
    (fun u ↦ C.length - (u.reg .rsi).toNat / 2) ⟨0, hI⟩
  · intro u ⟨k, hk⟩ hc
    have hlt : k < C.length := by
      simp only [Cond.eval, Rhs.eval, hk.rsi, hk.rax, decide_eq_true_eq,
        UInt64.lt_iff_toNat_lt, toNat_2k (show k < 2 ^ 32 by have := hk.k_le; omega),
        toNat_2k hCl] at hc
      omega
    refine WP.mono (kBody_spec hk hlt hm hRl hC hX hsC hsX) (fun u' h ↦ ⟨⟨k + 1, h⟩, ?_⟩)
      fun _ h ↦ h
    rw [h.rsi, hk.rsi, toNat_2k (by omega), toNat_2k (by omega)]
    omega
  · intro u ⟨k, hk⟩ hc
    have : C.length ≤ k := by
      simp only [Cond.eval, Rhs.eval, hk.rsi, hk.rax, decide_eq_false_iff_not,
        UInt64.lt_iff_toNat_lt, toNat_2k (show k < 2 ^ 32 by have := hk.k_le; omega),
        toNat_2k hCl] at hc
      omega
    obtain rfl : k = C.length := by have := hk.k_le; omega
    exact hk

/-- **`weightRing` computes the ring-switched weight**, on lists of `E`. -/
theorem weightRing_specE {R C X : List E} {b rp cp xp : UInt64} {vc idx : Nat}
    (hbx : s.reg .rbx = b) (h13 : s.reg .r13 = rp) (h15 : s.reg .r15 = R.length.toUInt64)
    (h14 : s.reg .r14 = xp) (hbp : s.reg .rbp = X.length.toUInt64) (h11 : s.reg .r11 = cp)
    (h12 : s.reg .r12 = C.length.toUInt64) (hsi : s.reg .rsi = idx.toUInt64)
    (hdx : s.reg .rdx = vc.toUInt64) (hR : EArr s.mem rp R) (hX : EArr s.mem xp X)
    (hC : EArr s.mem cp C) (hRl : R.length ≤ 36) (hXl : X.length < 2 ^ 32)
    (hCl : C.length < 2 ^ 32) (hvc : vc < 2 ^ 64) (hidx : idx < 2 ^ 64)
    (hdom : ∀ k < bufWords, (s.mem (ew b k)).isSome)
    (hsR : ∀ k < bufWords, ∀ j < 2 * R.length, ew b k ≠ ew rp j)
    (hsX : ∀ k < bufWords, ∀ j < 2 * X.length, ew b k ≠ ew xp j)
    (hsC : ∀ k < bufWords, ∀ j < 2 * C.length, ew b k ≠ ew cp j) :
    WP weightRing s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) =
        Placement.eqAbove ⟨vc, idx⟩ X * ringWeight R (X.take vc) C ∧
      ∀ a, (∀ k < bufWords, a ≠ ew b k) → s'.mem a = s.mem a) F := by
  set m := min (min R.length vc) X.length with hm
  unfold weightRing
  refine WP.then (WP.withDom (WP.withWrites (ringSetup_spec (F := F) hbx h11 h12 h13 h14 h15 hdx
    hbp hR hRl hXl hvc hdom hsR))) fun t1 ⟨⟨h1, w1⟩, d1⟩ ↦ ?_
  have r1 : ∀ r, ringSetup.writes r = false → t1.reg r = s.reg r := w1
  have hX1 : EArr t1.mem xp X := EArr_apart h1.frame hsX hX
  refine WP.then (WP.withDom (ringAbove_spec (F := F) (X := X) (b := b) (xp := xp) (vc := vc)
    (idx := idx) (by rw [r1 .rbx (by decide)]; exact hbx) (by rw [r1 .r14 (by decide)]; exact h14)
    (by rw [r1 .rbp (by decide)]; exact hbp) (by rw [r1 .rsi (by decide)]; exact hsi)
    (by rw [r1 .rdx (by decide)]; exact hdx) hX1 hXl hvc hidx
    (by rw [d1]; exact hdom 6 (by decide)) (by rw [d1]; exact hdom 7 (by decide))))
    fun t2 ⟨⟨h2bx, h2e, h2f⟩, d2⟩ ↦ ?_
  have m2 : ∀ j, j < 2 ^ 61 → j ≠ 6 → j ≠ 7 → t2.mem (ew b j) = t1.mem (ew b j) := fun j hj h6 h7 ↦
    h2f _ (fun e ↦ h6 ((ew_inj hj (by omega)).mp e)) (fun e ↦ h7 ((ew_inj hj (by omega)).mp e))
  have hw1 : t2.mem (ew b 1) = some (2 * C.length).toUInt64 := by
    rw [m2 1 (by omega) (by omega) (by omega)]; exact h1.words 1 (by decide)
  fstep; fstep
  refine wp_load (eval_w (by rsimp; exact h2bx) 1) (by rsimp; exact hw1) ?_
  refine WP.then (kLoop_spec (e := Placement.eqAbove ⟨vc, idx⟩ X) ?hI hm hRl hCl hC hX hsC hsX)
    fun t3 h3 ↦ ?_
  case hI =>
    refine ⟨Nat.zero_le _, by rsimp; exact h2bx, by rsimp; rfl, by rsimp, fun j hj ↦ ?_, ?_, ?_,
      ?_, fun a ha ↦ ?_, fun j hj ↦ ?_⟩
    · rsimp; rw [m2 j (by omega) (by omega) (by omega)]; exact h1.words j (by omega)
    · rw [rwAt_zero]
      constructor <;> rsimp
      · rw [m2 _ (by omega) (by omega) (by omega), lane_zero0]; exact h1.words 4 (by decide)
      · rw [m2 _ (by omega) (by omega) (by omega), lane_zero1]; exact h1.words 5 (by decide)
    · rsimp; exact h2e
    · rw [rwAt_zero]
      rsimp
      refine EArr_congr (fun j hj ↦ ?_) h1.rs
      rw [List.length_take] at hj
      rw [ew8, m2 _ (by omega) (by omega) (by omega)]
    · rsimp
      rw [h2f a (ha 6 (by decide)) (ha 7 (by decide))]
      exact h1.frame a ha
    · rsimp; rw [d2, d1]; exact hdom j hj
  have tot := h3.tot
  have ab := h3.above
  simp only [EW, Nat.reduceMul, Nat.reduceAdd] at tot ab
  refine wp_load (eval_w h3.rbp 4) tot.1 ?_
  refine wp_load (eval_w (by rsimp; exact h3.rbp) 5) (by rsimp; exact tot.2) ?_
  refine wp_load (eval_w (by rsimp; exact h3.rbp) 6) (by rsimp; exact ab.1) ?_
  refine wp_load (eval_w (by rsimp; exact h3.rbp) 7) (by rsimp; exact ab.2) ?_
  refine WP.then (emul_spec _) fun t4 ⟨e4, m4, _⟩ ↦ ?_
  fdone
  refine ⟨?_, fun a ha ↦ ?_⟩
  · rw [e4]
    rsimp
    rw [eOf_lanes, eOf_lanes, rwAt_all]
  · rw [m4]
    rsimp
    exact h3.frame a ha

end NativeVm.Code.Ring
