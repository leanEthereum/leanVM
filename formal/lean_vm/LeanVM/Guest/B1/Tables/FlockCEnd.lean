/-
  LeanVM.Guest.B1.Tables.FlockCEnd

  `verify_flock`'s last segments, complete: the pin term, the points' equality, the slices'
  Lagrange sum, the final check and the returns.
-/

module

public import LeanVM.Guest.B1.Tables.FlockCTail

/-!
# The last segments, complete

`c_p13`: the pin term `α³ · eq_weight · s[0]`. `c_cpe`: the product `Π_t (1 + χ_t + r_{7-t})`.
`c_cs`: the slices' sum against the lower numerators. `c_end`: the final check and the returns.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig

@[expose] public section

section
variable {rd : Reader} {τ : ℕ} {cv : Digest} {xs : List E} {cur zchis lrs zpart p11 p24 p40 p2220 : E}

/-- The pin column's equality weight at the challenges `rc`. -/
def pinW (rc : ℕ → E) : E :=
  (1 + rc 0) * (1 + rc 1) * (1 + rc 2) * (1 + rc 3) * rc 4 * (1 + rc 5) * (1 + rc 6) * (1 + rc 7)

/-- **The pin term** (G:1945-1946). -/
theorem c_p13 {rc : ℕ → E} {a3 s0 : E} (hr : ∀ j < 8, LoadHolds rd lrs j (rc j))
    (hs0 : LoadHolds rd zpart 0 s0) (σ : Val) (h5 : σ (.n 5) = lrs) (h6 : σ (.n 6) = zpart)
    (h2735 : σ (.n 2735) = a3) :
    Completes (coreProgram.Rel rd) rd 4093 4125 flP13 σ (fun σ' => σ' (.n 4124) = a3 * pinW rc * s0) := by
  refine completes_upds [(4093, rc 0),
    (4094, word 1 0 0),
    (4095, word 1 0 0 + rc 0),
    (4096, rc 1),
    (4097, word 1 0 0),
    (4098, word 1 0 0 + rc 1),
    (4099, (word 1 0 0 + rc 0) * (word 1 0 0 + rc 1)),
    (4100, rc 2),
    (4101, word 1 0 0),
    (4102, word 1 0 0 + rc 2),
    (4103, (word 1 0 0 + rc 0) * (word 1 0 0 + rc 1) * (word 1 0 0 + rc 2)),
    (4104, rc 3),
    (4105, word 1 0 0),
    (4106, word 1 0 0 + rc 3),
    (4107, (word 1 0 0 + rc 0) * (word 1 0 0 + rc 1) * (word 1 0 0 + rc 2) * (word 1 0 0 + rc 3)),
    (4108, rc 4),
    (4109, (word 1 0 0 + rc 0) * (word 1 0 0 + rc 1) * (word 1 0 0 + rc 2) * (word 1 0 0 + rc 3) * rc 4),
    (4110, rc 5),
    (4111, word 1 0 0),
    (4112, word 1 0 0 + rc 5),
    (4113, (word 1 0 0 + rc 0) * (word 1 0 0 + rc 1) * (word 1 0 0 + rc 2) * (word 1 0 0 + rc 3) * rc 4 * (word 1 0 0 + rc 5)),
    (4114, rc 6),
    (4115, word 1 0 0),
    (4116, word 1 0 0 + rc 6),
    (4117, (word 1 0 0 + rc 0) * (word 1 0 0 + rc 1) * (word 1 0 0 + rc 2) * (word 1 0 0 + rc 3) * rc 4 * (word 1 0 0 + rc 5) * (word 1 0 0 + rc 6)),
    (4118, rc 7),
    (4119, word 1 0 0),
    (4120, word 1 0 0 + rc 7),
    (4121, (word 1 0 0 + rc 0) * (word 1 0 0 + rc 1) * (word 1 0 0 + rc 2) * (word 1 0 0 + rc 3) * rc 4 * (word 1 0 0 + rc 5) * (word 1 0 0 + rc 6) * (word 1 0 0 + rc 7)),
    (4122, a3 * ((word 1 0 0 + rc 0) * (word 1 0 0 + rc 1) * (word 1 0 0 + rc 2) * (word 1 0 0 + rc 3) * rc 4 * (word 1 0 0 + rc 5) * (word 1 0 0 + rc 6) * (word 1 0 0 + rc 7))),
    (4123, s0),
    (4124, a3 * ((word 1 0 0 + rc 0) * (word 1 0 0 + rc 1) * (word 1 0 0 + rc 2) * (word 1 0 0 + rc 3) * rc 4 * (word 1 0 0 + rc 5) * (word 1 0 0 + rc 6) * (word 1 0 0 + rc 7)) * s0)] (by simp) (fun next kret hn => ?_) ?_
  · simp only [flP13, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    vs_ev
    rw [h5, h6, h2735]
    simp only [true_and]
    exact ⟨hr 0 (by omega), hr 1 (by omega), hr 2 (by omega), hr 3 (by omega), hr 4 (by omega),
      hr 5 (by omega), hr 6 (by omega), hr 7 (by omega), hs0, hn⟩
  · vs_ev
    simp only [word_one, pinW]

/-! ## The points' equality -/

/-- The equality's invariant before factor `t`. -/
def CpeInv (zchis lrs : E) (chi rc : ℕ → E) (t : ℕ) (σ : Val) : Prop :=
  Fixes σ [(4, zchis), (5, lrs)] ∧
    (0 < t → σ (.n (if t = 1 then 4129 else 4123 + 6 * t)) =
      ∏ u ∈ Finset.range t, (1 + chi u + rc (7 - u)))

def cpeSt (t : ℕ) : ℕ := if t = 0 then 4125 else 4124 + 6 * t

theorem cpe_below : ∀ t < 8, numBelowB (cpeSt (t + 1)) (Stmt.valsList (cpeBlk t)) = true := by
  decide +kernel

/-- The values of factor `t ≥ 1`. -/
def cpeVals (chi rc : ℕ → E) (P : E) (t : ℕ) : List (ℕ × E) :=
  [(4124 + 6 * t, word 1 0 0), (4125 + 6 * t, chi t), (4126 + 6 * t, word 1 0 0 + chi t),
    (4127 + 6 * t, rc (7 - t)), (4128 + 6 * t, word 1 0 0 + chi t + rc (7 - t)),
    (4129 + 6 * t, P * (word 1 0 0 + chi t + rc (7 - t)))]

theorem cpeVals_range (chi rc : ℕ → E) (P : E) (t : ℕ) :
    ∀ p ∈ cpeVals chi rc P t, 4124 + 6 * t ≤ p.1 ∧ p.1 < 4124 + 6 * t + 6 := by
  simp only [cpeVals, List.mem_cons, List.not_mem_nil, or_false]
  rintro p (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp <;> omega

/-- **The points' equality** (G:1951-1952). -/
theorem c_cpe {chi rc : ℕ → E} (hc : ∀ t < 8, LoadHolds rd zchis t (chi t))
    (hr : ∀ j < 8, LoadHolds rd lrs j (rc j)) (σ : Val) (h0 : CpeInv zchis lrs chi rc 0 σ) :
    Completes (coreProgram.Rel rd) rd 4125 4172 ((List.range 8).map cpeBlk).flatten σ
      (CpeInv zchis lrs chi rc 8) := by
  refine Completes.flatten (st := cpeSt) (Inv := CpeInv zchis lrs chi rc) 8
    (fun i _ => by unfold cpeSt; split <;> split <;> omega)
    (fun i hi => numBelow_of_B (cpe_below i hi)) (fun t ht σ hI => ?_) σ h0
  have h4 : σ (.n 4) = zchis := hI.1.get (k := 4) (e := zchis) (by simp)
  have h5 : σ (.n 5) = lrs := hI.1.get (k := 5) (e := lrs) (by simp)
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · have he := upds_ext (lo := 4125) (hi := 4130) σ [(4125, word 1 0 0), (4126, chi 0),
      (4127, word 1 0 0 + chi 0), (4128, rc 7), (4129, word 1 0 0 + chi 0 + rc 7)] (by simp)
    refine completes_upds _ (by simp [cpeSt]) (fun next kret hn => ?_) ⟨hI.1.of_ext he (by simp), ?_⟩
    · simp only [cpeBlk, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
      vs_ev
      rw [h4, h5]
      simp only [true_and]
      exact ⟨hc 0 (by omega), hr 7 (by omega), hn⟩
    · intro _
      simp only [Nat.zero_add, ↓reduceIte, Finset.prod_range_one]
      vs_ev
      rw [word_one]
  · obtain hP := hI.2 hpos
    have ht' : ¬ t = 0 := by omega
    set P := σ (.n (if t = 1 then 4129 else 4123 + 6 * t))
    rw [show cpeSt t = 4124 + 6 * t by simp [cpeSt, ht'],
      show cpeSt (t + 1) = 4124 + 6 * t + 6 by simp [cpeSt]; omega]
    have e1 : ∀ k < 4124 + 6 * t, upds σ (cpeVals chi rc P t) (.n k) = σ (.n k) := fun k hk =>
      upds_of_not_mem σ _ fun p hp => by
        have := cpeVals_range chi rc P t p hp
        simp only [ne_eq, V.mk.injEq, true_and]; omega
    refine completes_upds (cpeVals chi rc P t) (cpeVals_range chi rc P t) (fun next kret hn => ?_)
      ⟨hI.1.of_ext (upds_ext σ _ (cpeVals_range chi rc P t)) (by simp; omega), fun _ => ?_⟩
    · simp only [cpeBlk, ht', ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
      rw [e1 4 (by omega), e1 5 (by omega), e1 (if t = 1 then 4129 else 4123 + 6 * t)
        (by split <;> omega), h4, h5]
      simp only [cpeVals]
      fl_ev
      exact ⟨trivial, hc t ht, trivial, hr (7 - t) (by omega), trivial, rfl, hn⟩
    · rw [ite_neg' (by omega), show 4123 + 6 * (t + 1) = 4129 + 6 * t by ring]
      simp only [cpeVals]
      fl_ev
      rw [hP, Finset.prod_range_succ, word_one]

/-! ## The slices' Lagrange sum -/

/-- The numerators over the lower skip nodes. -/
def numLo (z : E) (i : ℕ) : E := ∏ j ∈ (Finset.range 64).erase i, (z + phi (0 + j))

/-- The sum's invariant before term `i`. -/
def CsInv (zpart z : E) (s : ℕ → E) (i : ℕ) (σ : Val) : Prop :=
  Fixes σ [(6, zpart)] ∧ (∀ j < 64, σ (.n (2655 + j)) = numLo z j) ∧
    (0 < i → σ (.n (if i = 1 then 4173 else 4170 + 3 * i)) = ∑ j ∈ Finset.range i, numLo z j * s j)

def csSt (i : ℕ) : ℕ := if i = 0 then 4172 else 4171 + 3 * i

theorem cs_below : ∀ i < 64, numBelowB (csSt (i + 1)) (Stmt.valsList (csBlk i)) = true := by
  decide +kernel

def csVals (z S : E) (s : ℕ → E) (i : ℕ) : List (ℕ × E) :=
  [(4171 + 3 * i, s i), (4172 + 3 * i, numLo z i * s i), (4173 + 3 * i, S + numLo z i * s i)]

theorem csVals_range (z S : E) (s : ℕ → E) (i : ℕ) :
    ∀ p ∈ csVals z S s i, 4171 + 3 * i ≤ p.1 ∧ p.1 < 4171 + 3 * i + 3 := by
  simp only [csVals, List.mem_cons, List.not_mem_nil, or_false]
  rintro p (rfl | rfl | rfl) <;> simp <;> omega

theorem csInv_keep {zpart z : E} {s : ℕ → E} {i lo hi : ℕ} {σ σ' : Val} (h : CsInv zpart z s i σ)
    (he : Ext lo hi σ σ') (hlo : 4172 ≤ lo) :
    Fixes σ' [(6, zpart)] ∧ ∀ j < 64, σ' (.n (2655 + j)) = numLo z j :=
  ⟨h.1.of_ext he (by simp; omega), fun j hj => by rw [he.apply (Or.inl (by omega)), h.2.1 j hj]⟩

/-- **The slices' Lagrange sum** (G:1953-1954). -/
theorem c_cs {z : E} {s : ℕ → E} (hs : ∀ i < 64, LoadHolds rd zpart i (s i)) (σ : Val)
    (h0 : CsInv zpart z s 0 σ) :
    Completes (coreProgram.Rel rd) rd 4172 4363 ((List.range 64).map csBlk).flatten σ
      (CsInv zpart z s 64) := by
  refine Completes.flatten (st := csSt) (Inv := CsInv zpart z s) 64
    (fun i _ => by unfold csSt; split <;> split <;> omega)
    (fun i hi => numBelow_of_B (cs_below i hi)) (fun i hi σ hI => ?_) σ h0
  have h6 : σ (.n 6) = zpart := hI.1.get (k := 6) (e := zpart) (by simp)
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · have he := upds_ext (lo := 4172) (hi := 4174) σ [(4172, s 0), (4173, numLo z 0 * s 0)] (by simp)
    refine completes_upds _ (by simp [csSt]) (fun next kret hn => ?_)
      ⟨(csInv_keep hI he le_rfl).1, (csInv_keep hI he le_rfl).2, fun _ => ?_⟩
    · simp only [csBlk, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
      vs_ev
      rw [h6, hI.2.1 0 (by omega)]
      exact ⟨hs 0 (by omega), rfl, hn⟩
    · simp only [Nat.zero_add, ↓reduceIte, Finset.sum_range_one]
      vs_ev
  · obtain hS := hI.2.2 hpos
    have hi' : ¬ i = 0 := by omega
    set S := σ (.n (if i = 1 then 4173 else 4170 + 3 * i))
    rw [show csSt i = 4171 + 3 * i by simp [csSt, hi'],
      show csSt (i + 1) = 4171 + 3 * i + 3 by simp [csSt]; omega]
    have e1 : ∀ k < 4171 + 3 * i, upds σ (csVals z S s i) (.n k) = σ (.n k) := fun k hk =>
      upds_of_not_mem σ _ fun p hp => by
        have := csVals_range z S s i p hp
        simp only [ne_eq, V.mk.injEq, true_and]; omega
    have he := upds_ext σ _ (csVals_range z S s i)
    refine completes_upds (csVals z S s i) (csVals_range z S s i) (fun next kret hn => ?_)
      ⟨(csInv_keep hI he (by omega)).1, (csInv_keep hI he (by omega)).2, fun _ => ?_⟩
    · simp only [csBlk, hi', ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
      rw [e1 6 (by omega), e1 (2655 + i) (by omega),
        e1 (if i = 1 then 4173 else 4170 + 3 * i) (by split <;> omega), h6, hI.2.1 i hi]
      simp only [csVals]
      fl_ev
      exact ⟨hs i hi, trivial, rfl, hn⟩
    · rw [ite_neg' (by omega), show 4170 + 3 * (i + 1) = 4173 + 3 * i by ring]
      simp only [csVals]
      fl_ev
      rw [hS, Finset.sum_range_succ]

end

end
end LeanVM.Guest.B1
