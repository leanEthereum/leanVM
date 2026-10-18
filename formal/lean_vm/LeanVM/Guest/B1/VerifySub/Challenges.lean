/-
  LeanVM.Guest.B1.VerifySub.Challenges

  `verify_sub`'s inline challenges: the bus's `alpha`s, their equality weights and `beta`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Front

/-!
# The bus challenges (G:2137-2153)

* `sqAll_eq`: `n` squeezes are the challenges of the `n` next states;
* `vs_alphas`: the four `alpha`s squeezed into `bus_alpha`;
* `vs_fpw`: `fp_w[x] = eq_weight(bus_alpha, 4, x, 0)`, the equality weights `eqKernel alphas`
  (each `eq_weight` expanded, `eqwEntry`);
* `vs_beta`: `beta` and the state GKR starts from, and the cursor past the ten words.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## Squeezes -/

theorem sqAll_eq (n : ℕ) (cv : Digest) :
    sqAll n cv = ((List.range n).map fun k ↦ challengeOf (sqCv^[k + 1] cv), sqCv^[n] cv) := by
  induction n generalizing cv with
  | zero => rfl
  | succ n ih =>
    simp only [sqAll, ih, List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def,
      Function.iterate_succ_apply, Function.iterate_zero_apply]

/-- `m` squeezes from the state `(s0, s0 + 1)` of `cv`, each stored: the `k`-th at statement
`nk k`, its values from `st k` (the next state at `st k + 5`, the challenge at `st k + 13`),
stored at `out[k]` by the next statement. -/
theorem squeezes {h : VsHolds rd σ} {m s0 : ℕ} {nk st : ℕ → ℕ} {out : V} {cv : Digest}
    (hblk : ∀ k < m, stmtsEqb (squeezeT (.n (if k = 0 then s0 else st (k - 1) + 5))
      (.n ((if k = 0 then s0 else st (k - 1) + 5) + 1)) (st k)) ((vsPre.drop (nk k)).take 14)
        = true)
    (hst : ∀ k < m, stmtsEqb [.atom (.load (.n (st k + 13)) out k)]
      ((vsPre.drop (nk k + 14)).take 1) = true)
    (h0 : (σ (.n s0), σ (.n (s0 + 1))) = digestScalars cv) :
    (∀ k < m, LoadHolds rd (σ out) k (challengeOf (sqCv^[k + 1] cv))) ∧
      ∀ k < m, (σ (.n (st k + 5)), σ (.n (st k + 6))) = digestScalars (sqCv^[k + 1] cv) := by
  have hs : ∀ k < m, (σ (.n (st k + 5)), σ (.n (st k + 6))) = digestScalars (sqCv^[k + 1] cv) ∧
      σ (.n (st k + 13)) = challengeOf (sqCv^[k + 1] cv) := by
    intro k hk
    induction k with
    | zero =>
      obtain ⟨c, hc, h5, h13⟩ := h.squeeze _ _ _ _ (hblk 0 hk)
      simp only [↓reduceIte] at hc
      rw [h0] at hc
      rw [← digestScalars_injective hc] at h5 h13
      exact ⟨h5, h13⟩
    | succ k ih =>
      obtain ⟨c, hc, h5, h13⟩ := h.squeeze _ _ _ _ (hblk (k + 1) hk)
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hc
      rw [(ih (by omega)).1] at hc
      rw [← digestScalars_injective hc] at h5 h13
      rw [Function.iterate_succ_apply' sqCv (k + 1)]
      exact ⟨h5, h13⟩
  refine ⟨fun k hk => ?_, fun k hk => (hs k hk).1⟩
  have := h.atom _ _ (hst k hk)
  rw [← (hs k hk).2]
  exact this

/-! ## The `alpha`s and `beta` -/

/-- **The four `alpha`s** (G:2141-2144), squeezed into `bus_alpha` from the state after the root. -/
theorem vs_alphas (h : VsHolds rd σ) {cv : Digest}
    (h0 : (σ (.n 447), σ (.n 448)) = digestScalars cv) :
    ReadsAt rd (σ (.n 451)) (sqAll 4 cv).1 ∧ (σ (.n 499), σ (.n 500)) = digestScalars (sqAll 4 cv).2 := by
  obtain ⟨hl, hc⟩ := squeezes (h := h) (m := 4) (s0 := 447) (nk := fun k ↦ 537 + 15 * k)
    (st := fun k ↦ 452 + 14 * k) (out := .n 451) (by decide +kernel) (by decide +kernel) h0
  rw [sqAll_eq]
  refine ⟨fun k hk => ?_, hc 3 (by omega)⟩
  simp only [List.length_map, List.length_range] at hk
  simpa using hl k hk

/-- **`beta`** (G:2147) and the state and cursor GKR starts from (G:2150): the cursor ten words
on. -/
theorem vs_beta (h : VsHolds rd σ) {cv : Digest}
    (h0 : (σ (.n 499), σ (.n 500)) = digestScalars cv) :
    (σ (.n 690), σ (.n 691)) = digestScalars (sqCv cv) ∧ σ (.n 698) = challengeOf (sqCv cv) ∧
      σ (.n 700) = σ (.n 14) * gen ^ 10 := by
  obtain ⟨c, hc, h5, h13⟩ := h.squeeze 790 (.n 499) (.n 500) 685 (by decide +kernel)
  rw [h0] at hc
  rw [← digestScalars_injective hc] at h5 h13
  have hs := h.slice 804 [.atom (.const (.n 699) (word 1024 0 0)),
    .atom (.mul (.n 700) (.n 14) (.n 699))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
  have w10 : word 1024 0 0 = gen ^ 10 := word_two_pow (a := 10) (by decide)
  exact ⟨h5, h13, by rw [hs.2, hs.1, w10]⟩

/-! ## `fp_w`: `eq_weight` expanded -/

/-- `eq_weight`'s coordinate `c` of index `x` (G:747-758), from the free value `v`, the running
weight at `w`: the statements, the next free value and the new weight's value. At `c = 0` the
weight `g^0` is folded away. -/
def eqwCoord (x c v w : ℕ) : List Stmt × ℕ × ℕ :=
  if x.testBit c then
    if c = 0 then ([.atom (.load (.n v) (.n 451) c)], v + 1, v)
    else ([.atom (.load (.n v) (.n 451) c), .atom (.mul (.n (v + 1)) (.n w) (.n v))], v + 2, v + 1)
  else
    if c = 0 then
      ([.atom (.load (.n v) (.n 451) c), .atom (.const (.n (v + 1)) (word 1 0 0)),
        .atom (.add (.n (v + 2)) (.n (v + 1)) (.n v))], v + 3, v + 2)
    else
      ([.atom (.load (.n v) (.n 451) c), .atom (.const (.n (v + 1)) (word 1 0 0)),
        .atom (.add (.n (v + 2)) (.n (v + 1)) (.n v)), .atom (.mul (.n (v + 3)) (.n w) (.n (v + 2)))],
        v + 4, v + 3)

/-- `fp_w[x] = eq_weight(bus_alpha, 4, x, 0)` from the free value `v`: its statements and the
next free value. -/
def eqwEntry (x v : ℕ) : List Stmt × ℕ :=
  let r0 := eqwCoord x 0 v 0
  let r1 := eqwCoord x 1 r0.2.1 r0.2.2
  let r2 := eqwCoord x 2 r1.2.1 r1.2.2
  let r3 := eqwCoord x 3 r2.2.1 r2.2.2
  (r0.1 ++ r1.1 ++ r2.1 ++ r3.1 ++ [.atom (.load (.n r3.2.2) (.n 508) x)], r3.2.1)

/-- Entry `x`'s first value. -/
def eqwStart : ℕ → ℕ
  | 0 => 509
  | x + 1 => (eqwEntry x (eqwStart x)).2

/-- Entry `x`'s first statement. -/
def eqwIdx : ℕ → ℕ
  | 0 => 598
  | x + 1 => eqwIdx x + (eqwEntry x (eqwStart x)).1.length

theorem vs_eqw_blocks : ∀ x < 16,
    (decide (eqwIdx x + (eqwEntry x (eqwStart x)).1.length ≤ 790) && stmtsEqb (eqwEntry x (eqwStart x)).1
      ((vsPre.drop (eqwIdx x)).take (eqwEntry x (eqwStart x)).1.length)) = true := by decide +kernel

/-- The factor of coordinate `c` at index `x`. -/
def eqFactor (a : ℕ → E) (x c : ℕ) : E := if x.testBit c then a c else 1 + a c

theorem holds_eqwCoord {C : CallRel} {k : List E → Prop} {a : ℕ → E}
    (ha : ∀ c < 4, ∀ u, LoadHolds rd (σ (.n 451)) c u → u = a c) (x c v w : ℕ) (hc : c < 4)
    (next : Prop)
    (h : Stmt.HoldsList C rd σ (eqwCoord x c v w).1 next k) :
    σ (.n (eqwCoord x c v w).2.2) = (if c = 0 then 1 else σ (.n w)) * eqFactor a x c ∧ next := by
  unfold eqwCoord at h ⊢
  unfold eqFactor
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · by_cases hb : x.testBit 0 <;>
      simp only [hb, ↓reduceIte, Bool.false_eq_true, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
        word_one] at h ⊢
    · obtain ⟨l, hn⟩ := h
      exact ⟨by rw [ha 0 hc _ l, one_mul], hn⟩
    · obtain ⟨l, h1, ha', hn⟩ := h
      exact ⟨by rw [ha', h1, ha 0 hc _ l, one_mul], hn⟩
  · have h0 : c ≠ 0 := by omega
    by_cases hb : x.testBit c <;>
      simp only [hb, h0, ↓reduceIte, Bool.false_eq_true, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
        word_one] at h ⊢
    · obtain ⟨l, hm, hn⟩ := h
      exact ⟨by rw [hm, ha c hc _ l], hn⟩
    · obtain ⟨l, h1, ha', hm, hn⟩ := h
      exact ⟨by rw [hm, ha', h1, ha c hc _ l], hn⟩

theorem holds_eqwEntry {C : CallRel} {k : List E → Prop} {a : ℕ → E}
    (ha : ∀ c < 4, ∀ u, LoadHolds rd (σ (.n 451)) c u → u = a c) (x v : ℕ)
    (h : Stmt.HoldsList C rd σ (eqwEntry x v).1 True k) :
    LoadHolds rd (σ (.n 508)) x (eqFactor a x 0 * eqFactor a x 1 * eqFactor a x 2 * eqFactor a x 3) := by
  simp only [eqwEntry, holdsList_append] at h
  obtain ⟨e0, h⟩ := holds_eqwCoord ha x 0 v 0 (by omega) _ h
  obtain ⟨e1, h⟩ := holds_eqwCoord ha x 1 _ _ (by omega) _ h
  obtain ⟨e2, h⟩ := holds_eqwCoord ha x 2 _ _ (by omega) _ h
  obtain ⟨e3, h⟩ := holds_eqwCoord ha x 3 _ _ (by omega) _ h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
  simp only [Nat.one_ne_zero, OfNat.ofNat_ne_zero, ↓reduceIte, one_mul] at e0 e1 e2 e3
  rw [e3, e2, e1, e0] at h
  exact h

theorem eqKernel4 (a : ℕ → E) (x : ℕ) (hx : x < 16) :
    (eqKernel [a 0, a 1, a 2, a 3]).getD x 0 =
      eqFactor a x 0 * eqFactor a x 1 * eqFactor a x 2 * eqFactor a x 3 := by
  interval_cases x <;> simp (config := { decide := true }) [eqKernel, eqFactor]

/-- **`fp_w`** (G:2145-2146): the equality weights of the `alpha`s. -/
theorem vs_fpw {N : ℕ} (h : VsHoldsTo N rd σ) (hN : 790 ≤ N) {alphas : List E}
    (hl : alphas.length = 4) (ha : ReadsAt rd (σ (.n 451)) alphas) :
    ReadsAt rd (σ (.n 508)) (eqKernel alphas) := by
  replace h := h.mono hN
  have ha' : ∀ c < 4, ∀ u, LoadHolds rd (σ (.n 451)) c u → u = alphas.getD c 0 := fun c hc u hu => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact loadHolds_unique hu (ha c (by omega))
  obtain ⟨a0, a1, a2, a3, rfl⟩ : ∃ a0 a1 a2 a3, alphas = [a0, a1, a2, a3] := by
    match alphas, hl with
    | [a0, a1, a2, a3], _ => exact ⟨a0, a1, a2, a3, rfl⟩
  intro x hx
  have hlen : (eqKernel [a0, a1, a2, a3]).length = 16 := by simp [eqKernel]
  rw [hlen] at hx
  have := holds_eqwEntry ha' x _ (h.slice' _ _ (vs_eqw_blocks x hx))
  rw [← List.getD_eq_getElem _ 0]
  have e := eqKernel4 (fun c ↦ [a0, a1, a2, a3].getD c 0) x hx
  simp only [List.getD_cons_zero, List.getD_cons_succ] at e
  rw [e]
  exact this

end
end LeanVM.Guest.B1.VerifySub
