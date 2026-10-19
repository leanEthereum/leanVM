/-
  LeanVM.Guest.B1.VerifySub.CBus

  `verify_sub`'s bus challenges, complete: the `alpha`s, `fp_w` (each `eq_weight` expanded) and
  `beta`.
-/

module

public import LeanVM.Guest.B1.VerifySub.CFront

/-!
# The bus challenges, complete (G:2137-2153)

* `c_squeezes`: `m` squeezes stored at `out`, from a state of `cv`;
* `c_eqwCoord`, `c_eqwEntry`: one coordinate of `eq_weight`, one entry of `fp_w`;
* `c_bus`: the block.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

variable {C : CallRel} {rd : Reader} {D : VsData} {P : VsPtrs}

/-! ## Squeezes, stored -/

/-- Squeeze `k` of `bSqueezes m s0 b0 out`. -/
def sqBlk (s0 b0 : ℕ) (out : V) (k : ℕ) : List Stmt :=
  squeezeT (.n (if k = 0 then s0 else b0 + 14 * (k - 1) + 5))
    (.n ((if k = 0 then s0 else b0 + 14 * (k - 1) + 5) + 1)) (b0 + 14 * k) ++
    [.atom (.load (.n (b0 + 14 * k + 13)) out k)]

theorem bSqueezes_eq (m s0 b0 : ℕ) (out : V) :
    bSqueezes m s0 b0 out = ((List.range m).map (sqBlk s0 b0 out)).flatten := rfl

/-- **`m` squeezes stored at `out`** (`out` a value below `b0` holding the pointer `po`), from the
state of `cv` at `s0`: the `k`-th challenge stored at `po[k]`, the state after them at
`b0 + 14(m-1) + 5`. -/
theorem c_squeezes {m s0 b0 : ℕ} {out : V} {po : E} {cv : Digest} (hm : 0 < m) (hs : s0 + 1 < b0)
    (ho : ∃ k < b0, out = .n k)
    (hst : ∀ k < m, LoadHolds rd po k (challengeOf (sqCv^[k + 1] cv)))
    (hnb : ∀ k < m, NumBelow (b0 + 14 * (k + 1)) (Stmt.valsList (sqBlk s0 b0 out k))) (σ : Val)
    (hout : σ out = po) (h0 : (σ (.n s0), σ (.n (s0 + 1))) = digestScalars cv) :
    Completes C rd b0 (b0 + 14 * m) (bSqueezes m s0 b0 out) σ (fun σ' =>
      σ' out = po ∧ (σ' (.n (b0 + 14 * (m - 1) + 5)), σ' (.n (b0 + 14 * (m - 1) + 6))) =
        digestScalars (sqCv^[m] cv)) := by
  obtain ⟨ko, hko, rfl⟩ := ho
  rw [bSqueezes_eq]
  have key := Completes.flatten (C := C) (rd := rd) (blk := sqBlk s0 b0 (.n ko))
    (st := fun k ↦ b0 + 14 * k) (Inv := fun k σ' ↦ σ' (.n ko) = po ∧
      (σ' (.n (if k = 0 then s0 else b0 + 14 * (k - 1) + 5)),
        σ' (.n ((if k = 0 then s0 else b0 + 14 * (k - 1) + 5) + 1))) = digestScalars (sqCv^[k] cv))
    m (fun k _ => by omega) hnb (fun k hk σ' ⟨io, is⟩ => ?_) σ ⟨hout, by simpa using h0⟩
  · refine key.post fun σ' _ ⟨io, is⟩ => ⟨io, ?_⟩
    have : m ≠ 0 := by omega
    simpa [this, show b0 + 14 * (m - 1) + 5 + 1 = b0 + 14 * (m - 1) + 6 by omega] using is
  · have hlt : (if k = 0 then s0 else b0 + 14 * (k - 1) + 5) + 1 < b0 + 14 * k := by
      split <;> omega
    have c := completes_squeezeT (C := C) (rd := rd) (b := b0 + 14 * k)
      ⟨_, by omega, rfl⟩ ⟨_, hlt, rfl⟩ is (Post := fun σ'' => σ'' (.n ko) = po ∧
        (σ'' (.n (b0 + 14 * k + 5)), σ'' (.n (b0 + 14 * k + 6))) = digestScalars (sqCv^[k + 1] cv) ∧
        σ'' (.n (b0 + 14 * k + 13)) = challengeOf (sqCv^[k + 1] cv))
      fun σ'' e h5 h13 => ⟨by rw [e.apply (by omega)]; exact io,
        by rw [h5, Function.iterate_succ_apply'], by rw [h13, Function.iterate_succ_apply']⟩
    rw [show b0 + 14 * (k + 1) = b0 + 14 * k + 14 by omega]
    refine c.append_atom fun σ'' ⟨jo, js, jc⟩ => ⟨?_, jo, ?_⟩
    · show LoadHolds rd (σ'' (.n ko)) k (σ'' (.n (b0 + 14 * k + 13)))
      rw [jo, jc]; exact hst k hk
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [show b0 + 14 * k + 5 + 1 = b0 + 14 * k + 6 by omega]; exact js

/-! ## `eq_weight` -/

/-- **One coordinate of `eq_weight`**: from the running weight `acc` at `w` (unused at `c = 0`),
the new weight at the block's last value. -/
theorem c_eqwCoord {a : ℕ → E} {x c v w : ℕ} {acc : E} (hv : 451 < v) (hw : c ≠ 0 → w < v)
    (ha : LoadHolds rd P.alpha c (a c)) (σ : Val) (h451 : σ (.n 451) = P.alpha)
    (hacc : c ≠ 0 → σ (.n w) = acc) :
    Completes C rd v (eqwCoord x c v w).2.1 (eqwCoord x c v w).1 σ (fun σ' =>
      σ' (.n 451) = P.alpha ∧
        σ' (.n (eqwCoord x c v w).2.2) = (if c = 0 then 1 else acc) * eqFactor a x c) := by
  have n0 : (451 : ℕ) ≠ v := by omega
  have n1 : (451 : ℕ) ≠ v + 1 := by omega
  have n2 : (451 : ℕ) ≠ v + 2 := by omega
  have n3 : (451 : ℕ) ≠ v + 3 := by omega
  unfold eqwCoord eqFactor
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · by_cases hb : x.testBit 0
    · simp only [hb, ↓reduceIte]
      refine completes_upds [(v, a 0)] (by simp) (fun next kret hn => ?_) ?_
      · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, upds_n, upds_nil, n0, ↓reduceIte, h451]
        exact ⟨ha, hn⟩
      · simp only [upds_n, upds_nil, n0, ↓reduceIte, h451, one_mul, and_self]
    · simp only [hb, ↓reduceIte, Bool.false_eq_true]
      refine completes_upds [(v, a 0), (v + 1, word 1 0 0), (v + 2, word 1 0 0 + a 0)]
        (by simp) (fun next kret hn => ?_) ?_
      · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, upds_n, upds_nil, n0, n1, n2,
          show v + 1 ≠ v by omega, show v + 2 ≠ v by omega, show v + 2 ≠ v + 1 by omega,
          ↓reduceIte, h451, true_and]
        exact ⟨ha, hn⟩
      · simp only [upds_n, upds_nil, n0, n1, n2, show v + 2 ≠ v by omega,
          show v + 2 ≠ v + 1 by omega, ↓reduceIte, h451, word_one, one_mul, and_self]
  · have hc : c ≠ 0 := by omega
    have hw' := hw hc
    by_cases hb : x.testBit c
    · simp only [hb, hc, ↓reduceIte]
      refine completes_upds [(v, a c), (v + 1, acc * a c)] (by simp)
        (fun next kret hn => ?_) ?_
      · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, upds_n, upds_nil, n0, n1,
          show w ≠ v by omega, show w ≠ v + 1 by omega, show v + 1 ≠ v by omega, ↓reduceIte, h451,
          hacc hc, true_and]
        exact ⟨ha, hn⟩
      · simp only [upds_n, upds_nil, n0, n1, show v + 1 ≠ v by omega, ↓reduceIte, h451, and_self]
    · simp only [hb, hc, ↓reduceIte, Bool.false_eq_true]
      refine completes_upds [(v, a c), (v + 1, word 1 0 0), (v + 2, word 1 0 0 + a c),
        (v + 3, acc * (word 1 0 0 + a c))] (by simp) (fun next kret hn => ?_) ?_
      · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, upds_n, upds_nil, n0, n1, n2, n3,
          show v + 1 ≠ v by omega, show v + 2 ≠ v by omega, show v + 2 ≠ v + 1 by omega,
          show v + 3 ≠ v by omega, show v + 3 ≠ v + 1 by omega, show v + 3 ≠ v + 2 by omega,
          show w ≠ v by omega, show w ≠ v + 1 by omega, show w ≠ v + 2 by omega,
          show w ≠ v + 3 by omega, ↓reduceIte, h451, hacc hc, true_and]
        exact ⟨ha, hn⟩
      · simp only [upds_n, upds_nil, n0, n1, n2, n3, show v + 3 ≠ v by omega,
          show v + 3 ≠ v + 1 by omega, show v + 3 ≠ v + 2 by omega, ↓reduceIte, h451, word_one,
          and_self]

theorem eqwCoord_next (x c v w : ℕ) : v + 1 ≤ (eqwCoord x c v w).2.1 ∧
    (eqwCoord x c v w).2.2 < (eqwCoord x c v w).2.1 ∧ v ≤ (eqwCoord x c v w).2.2 := by
  unfold eqwCoord; split <;> split <;> simp

theorem numBelow_eqwCoord (x c v w : ℕ) (hw : w < v) (hv : 451 < v) :
    NumBelow (eqwCoord x c v w).2.1 (Stmt.valsList (eqwCoord x c v w).1) := by
  apply numBelow_of_B
  unfold eqwCoord
  split <;> split <;> simp [numBelowB, Stmt.vals, Atom.vals] <;> omega

theorem c_eqwCoord8 {a : ℕ → E} {x c v w : ℕ} {acc : E} (hv : 508 < v) (hw : c ≠ 0 → w < v)
    (ha : LoadHolds rd P.alpha c (a c)) (σ : Val) (h451 : σ (.n 451) = P.alpha)
    (h508 : σ (.n 508) = P.fpw) (hacc : c ≠ 0 → σ (.n w) = acc) :
    Completes C rd v (eqwCoord x c v w).2.1 (eqwCoord x c v w).1 σ (fun σ' =>
      σ' (.n 451) = P.alpha ∧ σ' (.n 508) = P.fpw ∧
        σ' (.n (eqwCoord x c v w).2.2) = (if c = 0 then 1 else acc) * eqFactor a x c) :=
  (c_eqwCoord (by omega) hw ha σ h451 hacc).post fun σ' e ⟨j1, j2⟩ =>
    ⟨j1, by rw [e.apply (Or.inl hv)]; exact h508, j2⟩

/-- **One entry of `fp_w`** (G:2145-2146): `eq_weight(bus_alpha, 4, x, 0)` stored at `fp_w[x]`. -/
theorem c_eqwEntry {a : ℕ → E} (x v : ℕ) (hv : 508 < v) (ha : ∀ c < 4, LoadHolds rd P.alpha c (a c))
    (hfw : LoadHolds rd P.fpw x (eqFactor a x 0 * eqFactor a x 1 * eqFactor a x 2 * eqFactor a x 3))
    (σ : Val) (h451 : σ (.n 451) = P.alpha) (h508 : σ (.n 508) = P.fpw) :
    Completes C rd v (eqwEntry x v).2 (eqwEntry x v).1 σ
      (fun σ' => σ' (.n 451) = P.alpha ∧ σ' (.n 508) = P.fpw) := by
  have hE : eqwEntry x v = ((eqwCoord x 0 v 0).1 ++ (eqwCoord x 1 (eqwCoord x 0 v 0).2.1
      (eqwCoord x 0 v 0).2.2).1 ++ (eqwCoord x 2 (eqwCoord x 1 (eqwCoord x 0 v 0).2.1
      (eqwCoord x 0 v 0).2.2).2.1 (eqwCoord x 1 (eqwCoord x 0 v 0).2.1 (eqwCoord x 0 v 0).2.2).2.2).1 ++
      (eqwCoord x 3 (eqwCoord x 2 (eqwCoord x 1 (eqwCoord x 0 v 0).2.1 (eqwCoord x 0 v 0).2.2).2.1
      (eqwCoord x 1 (eqwCoord x 0 v 0).2.1 (eqwCoord x 0 v 0).2.2).2.2).2.1
      (eqwCoord x 2 (eqwCoord x 1 (eqwCoord x 0 v 0).2.1 (eqwCoord x 0 v 0).2.2).2.1
      (eqwCoord x 1 (eqwCoord x 0 v 0).2.1 (eqwCoord x 0 v 0).2.2).2.2).2.2).1 ++
      [.atom (.load (.n (eqwCoord x 3 (eqwCoord x 2 (eqwCoord x 1 (eqwCoord x 0 v 0).2.1
      (eqwCoord x 0 v 0).2.2).2.1 (eqwCoord x 1 (eqwCoord x 0 v 0).2.1 (eqwCoord x 0 v 0).2.2).2.2).2.1
      (eqwCoord x 2 (eqwCoord x 1 (eqwCoord x 0 v 0).2.1 (eqwCoord x 0 v 0).2.2).2.1
      (eqwCoord x 1 (eqwCoord x 0 v 0).2.1 (eqwCoord x 0 v 0).2.2).2.2).2.2).2.2) (.n 508) x)],
      (eqwCoord x 3 (eqwCoord x 2 (eqwCoord x 1 (eqwCoord x 0 v 0).2.1 (eqwCoord x 0 v 0).2.2).2.1
      (eqwCoord x 1 (eqwCoord x 0 v 0).2.1 (eqwCoord x 0 v 0).2.2).2.2).2.1
      (eqwCoord x 2 (eqwCoord x 1 (eqwCoord x 0 v 0).2.1 (eqwCoord x 0 v 0).2.2).2.1
      (eqwCoord x 1 (eqwCoord x 0 v 0).2.1 (eqwCoord x 0 v 0).2.2).2.2).2.2).2.1) := rfl
  rw [hE]
  generalize hr0 : eqwCoord x 0 v 0 = r0
  have ⟨a0, b0, c0⟩ := eqwCoord_next x 0 v 0
  have nb0 := numBelow_eqwCoord x 0 v 0 (by omega) (by omega)
  rw [hr0] at a0 b0 c0 nb0
  generalize hr1 : eqwCoord x 1 r0.2.1 r0.2.2 = r1
  have ⟨a1, b1, c1⟩ := eqwCoord_next x 1 r0.2.1 r0.2.2
  have nb1 := numBelow_eqwCoord x 1 r0.2.1 r0.2.2 b0 (by omega)
  rw [hr1] at a1 b1 c1 nb1
  generalize hr2 : eqwCoord x 2 r1.2.1 r1.2.2 = r2
  have ⟨a2, b2, c2⟩ := eqwCoord_next x 2 r1.2.1 r1.2.2
  have nb2 := numBelow_eqwCoord x 2 r1.2.1 r1.2.2 b1 (by omega)
  rw [hr2] at a2 b2 c2 nb2
  generalize hr3 : eqwCoord x 3 r2.2.1 r2.2.2 = r3
  have ⟨a3, b3, c3⟩ := eqwCoord_next x 3 r2.2.1 r2.2.2
  rw [hr3] at a3 b3 c3
  refine Completes.append_atom (P := fun σ' => σ' (.n 451) = P.alpha ∧ σ' (.n 508) = P.fpw ∧
      σ' (.n r3.2.2) = eqFactor a x 0 * eqFactor a x 1 * eqFactor a x 2 * eqFactor a x 3) ?_
    fun σ' ⟨j451, j508, j3⟩ =>
      ⟨(show LoadHolds rd (σ' (.n 508)) x (σ' (.n r3.2.2)) by rw [j508, j3]; exact hfw), j451, j508⟩
  refine Completes.append (m := r2.2.1) (P := fun σ' => σ' (.n 451) = P.alpha ∧
      σ' (.n 508) = P.fpw ∧ σ' (.n r2.2.2) = eqFactor a x 0 * eqFactor a x 1 * eqFactor a x 2)
    (by omega) (by omega) (by
      rw [valsList_append, valsList_append]
      exact ((nb0.mono (by omega)).append (nb1.mono (by omega))).append (nb2.mono le_rfl))
    ?_ fun σ' _ ⟨j451, j508, j2⟩ => ?_
  · refine Completes.append (m := r1.2.1) (P := fun σ' => σ' (.n 451) = P.alpha ∧
        σ' (.n 508) = P.fpw ∧ σ' (.n r1.2.2) = eqFactor a x 0 * eqFactor a x 1)
      (by omega) (by omega) (by rw [valsList_append]; exact (nb0.mono (by omega)).append (nb1.mono le_rfl))
      ?_ fun σ' _ ⟨j451, j508, j1⟩ => ?_
    · refine Completes.append (m := r0.2.1) (P := fun σ' => σ' (.n 451) = P.alpha ∧
          σ' (.n 508) = P.fpw ∧ σ' (.n r0.2.2) = eqFactor a x 0)
        (by omega) (by omega) nb0 ?_ fun σ' _ ⟨j451, j508, j0⟩ => ?_
      · rw [← hr0]
        exact (c_eqwCoord8 (x := x) (acc := 1) hv (fun h => absurd rfl h) (ha 0 (by omega)) σ h451 h508
          (fun h => absurd rfl h)).post fun σ' _ ⟨k1, k2, k3⟩ => ⟨k1, k2, by rw [k3]; simp⟩
      · rw [← hr1]
        exact (c_eqwCoord8 (x := x) (acc := eqFactor a x 0) (by omega) (fun _ => b0) (ha 1 (by omega)) σ' j451
          j508 (fun _ => j0)).post fun σ' _ ⟨k1, k2, k3⟩ => ⟨k1, k2, by rw [k3]; simp⟩
    · rw [← hr2]
      exact (c_eqwCoord8 (x := x) (acc := eqFactor a x 0 * eqFactor a x 1) (by omega) (fun _ => b1)
        (ha 2 (by omega)) σ' j451 j508 (fun _ => j1)).post fun σ' _ ⟨k1, k2, k3⟩ =>
          ⟨k1, k2, by rw [k3]; simp⟩
  · dsimp only
    rw [← hr3]
    exact (c_eqwCoord8 (x := x) (acc := eqFactor a x 0 * eqFactor a x 1 * eqFactor a x 2) (by omega)
      (fun _ => b2) (ha 3 (by omega)) σ' j451 j508 (fun _ => j2)).post fun σ' _ ⟨k1, k2, k3⟩ =>
        ⟨k1, k2, by rw [k3]; simp⟩

/-! ## The block -/

theorem eqwStart_16 : eqwStart 16 = 685 := by decide

theorem eqwStart_mono : ∀ x < 16, 508 < eqwStart x ∧ eqwStart x ≤ eqwStart (x + 1) := by decide

theorem numBelow_eqw : ∀ x < 16, NumBelow (eqwStart (x + 1)) (Stmt.valsList (eqwEntry x (eqwStart x)).1) :=
  fun x hx => numBelow_of_B (by revert x hx; decide +kernel)

theorem numBelow_sq451 : ∀ k < 4, NumBelow (452 + 14 * (k + 1)) (Stmt.valsList (sqBlk 447 452 (.n 451) k)) :=
  fun k hk => numBelow_of_B (by revert k hk; decide +kernel)

theorem bBus_eq : bBus = (.atom (.hint (.alloc (.n 451) 4)) :: bSqueezes 4 447 452 (.n 451)) ++
    (.atom (.hint (.alloc (.n 508) 16)) :: ((List.range 16).map fun x ↦ (eqwEntry x (eqwStart x)).1).flatten) ++
    squeezeT (.n 499) (.n 500) 685 ++
    [.atom (.const (.n 699) (word 1024 0 0)), .atom (.mul (.n 700) (.n 14) (.n 699))] := rfl

/-- The values the bus challenges leave. -/
def busOut (D : VsData) (P : VsPtrs) : List (ℕ × E) :=
  [(451, P.alpha), (508, P.fpw), (690, (digestScalars D.cvB).1), (691, (digestScalars D.cvB).2),
    (698, D.beta), (700, P.stream * gen ^ 10)]

/-- The `c`-th bus challenge. -/
def busA (D : VsData) (c : ℕ) : E := challengeOf (sqCv^[c + 1] D.cv10)

/-- **The bus challenges** (G:2137-2153): the four `alpha`s stored, `fp_w`, `beta`, the cursor. -/
theorem c_bus (σ : Val) (hσ : Fixes σ ((14, P.stream) :: (rootOut D).drop 2))
    (ha : ∀ c < 4, LoadHolds rd P.alpha c (busA D c))
    (hfw : ∀ x < 16, LoadHolds rd P.fpw x (eqFactor (busA D) x 0 * eqFactor (busA D) x 1 *
      eqFactor (busA D) x 2 * eqFactor (busA D) x 3)) :
    Completes C rd 451 701 bBus σ (fun σ' => Fixes σ' (busOut D P)) := by
  have h14 : σ (.n 14) = P.stream := hσ.get (by simp)
  have h447 : σ (.n 447) = (digestScalars D.cv10).1 := hσ.get (by simp [rootOut])
  have h448 : σ (.n 448) = (digestScalars D.cv10).2 := hσ.get (by simp [rootOut])
  rw [bBus_eq]
  refine Completes.append (m := 699) (P := fun σ' => (σ' (.n 451) = P.alpha ∧ σ' (.n 508) = P.fpw ∧
      (σ' (.n 690), σ' (.n 691)) = digestScalars D.cvB ∧ σ' (.n 698) = D.beta) ∧
        Fixes σ' [(14, P.stream)]) (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_
    fun σ3 _ ⟨⟨j451, j508, j690, j698⟩, j14⟩ => ?_
  · refine Completes.keep (l := [(14, P.stream)]) ?_ (by intro p hp; simp at hp; subst hp; exact h14)
      (by simp)
    refine Completes.append (m := 685) (P := fun σ' => σ' (.n 451) = P.alpha ∧ σ' (.n 508) = P.fpw ∧
        (σ' (.n 499), σ' (.n 500)) = digestScalars (sqCv^[4] D.cv10)) (by omega) (by omega)
      (numBelow_of_B (by decide +kernel)) ?_ fun σ2 _ ⟨j451, j508, j499⟩ => ?_
    · refine Completes.append (m := 508) (P := fun σ' => σ' (.n 451) = P.alpha ∧
          (σ' (.n 499), σ' (.n 500)) = digestScalars (sqCv^[4] D.cv10)) (by omega) (by omega)
        (numBelow_of_B (by decide +kernel)) ?_ fun σ1 _ ⟨j451, j499⟩ => ?_
      · rw [← List.singleton_append]
        refine Completes.append (m := 452) (P := fun σ' => σ' (.n 451) = P.alpha ∧
            (σ' (.n 447), σ' (.n 448)) = digestScalars D.cv10) (by omega) (by omega)
          (numBelow_of_B (by decide +kernel))
          (completes_hint (k := 451) P.alpha (by vs_ev; rw [h447, h448]; exact ⟨trivial, rfl⟩))
          fun σ' _ ⟨i451, i447⟩ => ?_
        exact c_squeezes (m := 4) (s0 := 447) (b0 := 452) (by omega) (by omega) ⟨451, by omega, rfl⟩
          ha numBelow_sq451 σ' i451 i447
      · rw [← List.singleton_append]
        refine Completes.append (m := 509) (P := fun σ' => σ' (.n 451) = P.alpha ∧
            σ' (.n 508) = P.fpw ∧ (σ' (.n 499), σ' (.n 500)) = digestScalars (sqCv^[4] D.cv10))
          (by omega) (by omega) (numBelow_of_B (by decide +kernel))
          (completes_hint (k := 508) P.fpw (by vs_ev; exact ⟨j451, trivial, j499⟩))
          fun σ' _ ⟨i451, i508, i499⟩ => ?_
        have key := Completes.flatten (C := C) (rd := rd)
          (blk := fun x ↦ (eqwEntry x (eqwStart x)).1) (st := eqwStart)
          (Inv := fun _ σ'' ↦ σ'' (.n 451) = P.alpha ∧ σ'' (.n 508) = P.fpw) 16
          (fun x hx => (eqwStart_mono x hx).2) numBelow_eqw
          (fun x hx σ'' ⟨k451, k508⟩ => c_eqwEntry x (eqwStart x) (eqwStart_mono x hx).1 ha
            (hfw x hx) σ'' k451 k508) σ' ⟨i451, i508⟩
        rw [eqwStart_16] at key
        refine (key.keep (l := [(499, (digestScalars (sqCv^[4] D.cv10)).1),
          (500, (digestScalars (sqCv^[4] D.cv10)).2)]) ?_ (by simp; decide)).post
          fun σ'' _ ⟨⟨k451, k508⟩, kf⟩ => ⟨k451, k508, ?_⟩
        · intro p hp
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with rfl | rfl
          · exact congrArg Prod.fst i499
          · exact congrArg Prod.snd i499
        · rw [kf.get (k := 499) (e := (digestScalars (sqCv^[4] D.cv10)).1) (by simp),
            kf.get (k := 500) (e := (digestScalars (sqCv^[4] D.cv10)).2) (by simp)]
    · exact completes_squeezeT (b := 685) ⟨499, by omega, rfl⟩ ⟨500, by omega, rfl⟩ j499
        fun σ' e h5 h13 => ⟨by rw [e.apply (by omega)]; exact j451, by rw [e.apply (by omega)]; exact j508,
          by rw [h5]; simp [VsData.cvB, sqAll_eq], by rw [h13]; simp [VsData.beta, VsData.cvB, sqAll_eq]⟩
  · refine completes_upds [(699, word 1024 0 0), (700, P.stream * gen ^ 10)] (by simp)
      (fun next kret hn => ?_) ?_
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
      vs_ev
      have w10 : word 1024 0 0 = gen ^ 10 := word_two_pow (a := 10) (by decide)
      rw [j14.get (k := 14) (e := P.stream) (by simp), w10]
      exact ⟨trivial, rfl, hn⟩
    · intro p hp
      simp only [busOut, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> vs_ev
      · exact j451
      · exact j508
      · exact congrArg Prod.fst j690
      · exact congrArg Prod.snd j690
      · exact j698

end
end LeanVM.Guest.B1.VerifySub
