module

public import NativeVm.Code.Phase6.Claim
public import NativeVm.Field.Mle

/-!
# `multilinearEval` over the scratch

`emle_scr`: `emle` over the table of `2^m` elements from `a`, at the point of `m` coordinates from
`c`, its work area from `b`, all in the scratch: `A` is `multilinearEval` of their values, and the
scratch is the same outside the work area's `2^m / 2` elements (`Agree`). `emle_st`: the same from
a state of phase 6, `ldSb` after it giving the phase's state back.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters LeanVM.Protocol
open NativeVm.Transcript (wd wdisp Env wd_inj rf_trans)
open NativeVm.Field (eOf emle emle_spec arrRegs ew)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW}

/-- `g'` is `g` outside the elements `[b, b + n)`. -/
def Agree (g g' : Nat → EW) (b n : Nat) : Prop := ∀ i, (i < b ∨ b + n ≤ i) → g' i = g i

theorem Scr.isSome {mem : UInt64 → Option UInt64} {p : UInt64} (hs : Scr mem p g) {k : Nat}
    (hk : k < 2 * scrN) : (mem (wd p k)).isSome := by
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show j + j = 2 * j by omega, (hs j (by omega)).1]; rfl
  · rw [(hs j (by omega)).2]; rfl

/-- The scratch after a run that writes only the elements `[b, b + n)` and keeps the memory's
domain. -/
theorem Scr.after {mem mem' : UInt64 → Option UInt64} {p : UInt64} (hs : Scr mem p g) {b n : Nat}
    (hn : b + n ≤ scrN) (hd : ∀ a, (mem' a).isSome = (mem a).isSome)
    (hm : ∀ a, (∀ k < 2 * n, a ≠ wd p (2 * b + k)) → mem' a = mem a) :
    ∃ g', Scr mem' p g' ∧ Agree g g' b n := by
  have hN := scrN_lt
  refine ⟨fun i ↦ if b ≤ i ∧ i < b + n then ⟨(mem' (wd p (2 * i))).getD 0,
    (mem' (wd p (2 * i + 1))).getD 0⟩ else g i, fun k hk ↦ ?_, fun i hi ↦ ?_⟩
  · by_cases h : b ≤ k ∧ k < b + n
    · simp only [h, and_self, ite_true]
      have h0 := hd (wd p (2 * k))
      have h1 := hd (wd p (2 * k + 1))
      rw [(hs k hk).1] at h0
      rw [(hs k hk).2] at h1
      refine ⟨?_, ?_⟩
      · cases e : mem' (wd p (2 * k)) with
        | none => rw [e] at h0; simp at h0
        | some v => rfl
      · cases e : mem' (wd p (2 * k + 1)) with
        | none => rw [e] at h1; simp at h1
        | some v => rfl
    · simp only [h, ite_false]
      have ne : ∀ l < 2, ∀ j < 2 * n, wd p (2 * k + l) ≠ wd p (2 * b + j) := fun l hl j hj e ↦ by
        have := (wd_inj (by omega) (by omega)).mp e
        omega
      have n0 := ne 0 (by omega)
      rw [Nat.add_zero] at n0
      rw [hm _ n0, hm _ (ne 1 (by omega))]
      exact hs k hk
  · simp only
    split
    · omega
    · rfl

theorem ew_wd (p : UInt64) (a k : Nat) : ew (wd p a) k = wd p (a + k) := NativeVm.Code.wd_wd p a k

/-- **`emle` over the scratch.** -/
theorem emle_scr {p : UInt64} {a b c m : Nat} {E : QState → Prop} (hs : Scr s.mem p g)
    (h13 : s.reg .r13 = wd p (2 * a)) (h14 : s.reg .r14 = wd p (2 * b))
    (hsi : s.reg .rsi = wd p (2 * c)) (h15 : s.reg .r15 = (2 ^ m).toUInt64) (hm : m < 60)
    (ha : a + 2 ^ m ≤ scrN) (hb : b + 2 ^ m / 2 ≤ scrN) (hc : c + m ≤ scrN)
    (hab : b + 2 ^ m / 2 ≤ a ∨ a + 2 ^ m ≤ b) (hbc : b + 2 ^ m / 2 ≤ c ∨ c + m ≤ b) :
    WP emle s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) =
        Verifier.multilinearEval (vals g a (2 ^ m)) (vals g c m) ∧
      (∃ g', Scr s'.mem p g' ∧ Agree g g' b (2 ^ m / 2)) ∧
      (∀ x, ¬ InScr p x → s'.mem x = s.mem x) ∧
      (∀ x, (s'.mem x).isSome = (s.mem x).isSome) ∧ RegsFrame arrRegs s s') E := by
  have hN := scrN_lt
  have hlen : ∀ o n, (vals g o n).length = n := fun o n ↦ by simp [vals]
  have hW : 2 * ((vals g a (2 ^ m)).length / 2) = 2 * (2 ^ m / 2) := by rw [hlen]
  refine WP.mono (NativeVm.Transcript.WP.frame (emle_spec (mle := vals g a (2 ^ m))
    (point := vals g c m) h13 h14 hsi (hs.earr ha) (hs.earr hc) (by rw [hlen]; exact h15)
    (by rw [hlen, hlen]) (by rw [hlen]; exact hm) (fun k hk ↦ ?_) ?_ ?_))
    (fun s' ⟨⟨e, hmem, hf⟩, hd, _⟩ ↦ ⟨e, ?_, fun x hx ↦ hmem x fun k hk e' ↦ hx ?_, hd, hf⟩)
    (fun _ h ↦ h.1)
  · rw [hW] at hk
    rw [ew_wd]
    exact hs.isSome (by omega)
  · intro k j l l' hkj hj hl hl' e
    rw [hlen] at hj
    rw [ew_wd, ew_wd, wd_inj (by omega) (by omega)] at e
    omega
  · intro k hk j hj e
    rw [hW] at hk
    rw [hlen] at hj
    rw [ew_wd, ew_wd, wd_inj (by omega) (by omega)] at e
    omega
  · exact hs.after hb hd fun x hx ↦ hmem x fun k hk ↦ by
      rw [hW] at hk; rw [ew_wd]; exact hx k hk
  · rw [hW] at hk
    rw [ew_wd] at e'
    exact ⟨2 * b + k, by omega, e'⟩

/-- **`emle` over the scratch, then `ldSb`**, from a state of phase 6. -/
theorem emle_st (hin : Inputs env inp s0.mem) {a b c m : Nat} {xs : List Stmt}
    {P E : QState → Prop} (h : St env s0 g t s)
    (h13 : s.reg .r13 = wd (sb env) (2 * a)) (h14 : s.reg .r14 = wd (sb env) (2 * b))
    (hsi : s.reg .rsi = wd (sb env) (2 * c)) (h15 : s.reg .r15 = (2 ^ m).toUInt64) (hm : m < 60)
    (ha : a + 2 ^ m ≤ scrN) (hb : b + 2 ^ m / 2 ≤ scrN) (hc : c + m ≤ scrN)
    (hab : b + 2 ^ m / 2 ≤ a ∨ a + 2 ^ m ≤ b) (hbc : b + 2 ^ m / 2 ≤ c ∨ c + m ≤ b)
    (k : ∀ s' g', St env s0 g' t s' → Agree g g' b (2 ^ m / 2) →
      eOf (s'.reg .r9) (s'.reg .r10) = Verifier.multilinearEval (vals g a (2 ^ m)) (vals g c m) →
      RegsFrame arrRegs s s' → WP (blk xs) s' P E) :
    WP (blk (emle :: (ldSb ++ xs))) s P E := by
  refine WP.blk_cons (WP.mono (emle_scr h.2.2.2 h13 h14 hsi h15 hm ha hb hc hab hbc)
    (fun s1 ⟨e, ⟨g', hs', hag⟩, hmem, hd, hf⟩ ↦ ?_) (fun _ h ↦ h))
  have hrdi : s1.reg .rdi = s.reg .rdi := hf .rdi (by decide)
  refine ldSb_st (codeRel_scr h.1 hin hrdi hmem hd) (base_scr h.2.1 hrdi hmem hd) hs'
    fun s' hst _ hrf ↦ k s' g' hst hag ?_ (rf_trans hf hrf)
  rw [hrf .r9 (by decide), hrf .r10 (by decide)]
  exact e

end NativeVm.Code.P6
