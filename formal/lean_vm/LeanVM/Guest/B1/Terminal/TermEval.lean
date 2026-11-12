/-
  LeanVM.Guest.B1.Terminal.TermEval

  `check_opening_terminal`'s head, selectors and tail on their evaluated valuation: every
  statement holds, every load lies in a region, and the values the terminal's check uses.
-/

module

public import LeanVM.Guest.B1.Terminal.ClaimsComplete
public import LeanVM.Guest.B1.Terminal.TermKids

/-!
# The head, the selectors and the tail, evaluated

The oracle `termW b0 outs`: the buffers at `b0`, `b0 + 35`, `b0 + 70`, `b0 + 105`, `b0 + 146`,
and the callees' results `outs` (`selector_tables`' at `43`, column `c`'s selector at `selV c`, the
ring switch's weight at `1702`). On a valuation satisfying the evaluator's equations (`GoodS`):
`head_complete`, `sel_complete`, `tail_complete`, as `zrT_complete` for the claims.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol.Verifier hiding gpow
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- The trivial call relation (the callees' relations come from their placement). -/
abbrev TrivC : CallRel := fun _ _ _ => True

/-- The committed column whose selector's value is `i`, if any. -/
def selOfV (i : ℕ) : Option ℕ := (List.range Tables.nCommittedCols).find? fun c => selV c == i

theorem selOfV_selV_all : (List.range Tables.nCommittedCols).all (fun c => selOfV (selV c) == some c) =
    true := by decide +kernel

theorem selOfV_selV {c : ℕ} (hc : c < Tables.nCommittedCols) : selOfV (selV c) = some c := by
  have := List.all_eq_true.mp selOfV_selV_all c (List.mem_range.mpr hc)
  simpa using this

/-- The values the head and the tail set from outside the selectors (`selV c ≥ 44`, below the
claims). -/
theorem selV_bounds : ∀ c < Tables.nCommittedCols, 43 < selV c ∧ selV c < claimsStart := by
  decide +kernel

/-- **The oracle of `check_opening_terminal`'s evaluation**: its buffers, its callees' results. -/
noncomputable def termW (b0 : ℕ) (outs : List (List E × Main.Layout)) : ℕ → E := fun i =>
  if i = 20 then ofK (addressOfIndex b0) else if i = 22 then ofK (addressOfIndex (b0 + 35)) else
  if i = 26 then ofK (addressOfIndex (b0 + 70)) else
  if i = 1694 then ofK (addressOfIndex (b0 + 105)) else
  if i = 1709 then ofK (addressOfIndex (b0 + 146)) else
  if i = 43 then (stRes outs).1.getD 0 0 else
  if i = 1702 then (outs.getD 99 ([], [])).1.getD 0 0 else
  match selOfV i with
  | some c => (outs.getD (4 + c) ([], [])).1.getD 0 0
  | none => 0

theorem termW_sel (b0 : ℕ) (outs : List (List E × Main.Layout)) {c : ℕ}
    (hc : c < Tables.nCommittedCols) :
    termW b0 outs (selV c) = (outs.getD (4 + c) ([], [])).1.getD 0 0 := by
  obtain ⟨h1, h2⟩ := selV_bounds c hc
  simp only [claimsStart] at h2
  simp only [termW]
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), selOfV_selV hc]

variable {rd : Reader} {S : List Atom} {σ : Val} {R : ℕ → Prop}

theorem good_hint_alloc {w : ℕ → E} {d n : ℕ} (h : GoodS rd S w σ (.atom (.hint (.alloc (.n d) n)))) :
    σ (.n d) = w d := h

theorem good_rets {w : ℕ → E} {s : Stmt} (h : GoodS rd S w σ s) :
    match s with
    | .call _ _ rets | .dispatch _ _ _ rets => ∀ v ∈ rets, σ v = w v.idx
    | _ => True := by
  cases s <;> first | exact h | trivial

/-! ## The head -/

/-- **The head, completely**: the chains' buffers, the slot points, the public input's chain (its
first two words stored, its loop, its value at `g^m`), the base `kappa_base`, the selector
tables. -/
theorem head_complete (hS : StoresAtPi S) {b0 : ℕ} {outs : List (List E × Main.Layout)}
    (hg : ∀ s ∈ termHeadT, GoodS rd S (termW b0 outs) σ s) {m : ℕ} {rm : E} {ps kbw : List E}
    (hm1 : 1 ≤ m) (e6 : σ (.n 6) = gen ^ m) (e3 : σ (.n 3) = rm)
    (h14 : LoadHolds rd (σ (.n 14)) 0 (ps.getD 0 0)) (a14 : AddrIn R (σ (.n 14)) 0)
    (hpi : ReadsAt rd (ofK (addressOfIndex (b0 + 70))) (piW rm ps m))
    (api : ∀ k ≤ m, R (b0 + 70 + k))
    (hkb : ∀ i < 8, LoadHolds rd (σ (.n 8)) i (kbw.getD i 0)) (akb : ∀ i < 8, AddrIn R (σ (.n 8)) i) :
    (∀ s ∈ termHeadT, Fwd.SHolds TrivC rd σ s) ∧
      (∀ q ∈ termHeadT.filterMap Stmt.loadS, AddrIn R (σ q.1) q.2) ∧
      σ (.n 20) = ofK (addressOfIndex b0) ∧ σ (.n 21) = word 1 0 ∧
      σ (.n 22) = ofK (addressOfIndex (b0 + 35)) ∧ σ (.n 23) = word 1 0 ∧
      σ (.n 24) = σ (.n 13) * σ (.n 7) ∧ σ (.n 25) = σ (.n 14) * σ (.n 7) ∧
      σ (.n 26) = ofK (addressOfIndex (b0 + 70)) ∧
      σ (.n 31) = word 2 0 + gen ^ m ∧ σ (.n 32) = word 2 0 ∧
      σ (.n 34) = (piW rm ps m).getD m 0 ∧ (∀ i < 8, σ (.n (kbV i)) = kbw.getD i 0) ∧
      σ (.n 43) = (stRes outs).1.getD 0 0 := by
  have mm : ∀ s, s ∈ termHeadT → GoodS rd S (termW b0 outs) σ s := hg
  simp only [termHeadT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at mm
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18,
    g19, k0, k1, k2, k3, k4, k5, k6, k7, g28⟩ := mm
  have e20 : σ (.n 20) = ofK (addressOfIndex b0) := by rw [good_hint_alloc g0]; simp [termW]
  have e21 := good_const g1
  have e22 : σ (.n 22) = ofK (addressOfIndex (b0 + 35)) := by
    rw [good_hint_alloc g3]; simp [termW]
  have e23 := good_const g4
  have e24 := goodS_mul g6 (by omega) (by omega)
  have e25 := goodS_mul g7 (by omega) (by omega)
  have e26 : σ (.n 26) = ofK (addressOfIndex (b0 + 70)) := by
    rw [good_hint_alloc g8]; simp [termW]
  have e27 := good_const g9
  obtain ⟨e28, l26⟩ := good_load_eq hS (n_ne_26 (by decide)) g11 h14
  have e29 := good_add g12
  have e30 := good_const g14
  have e31 := good_add g15
  have e32 := good_const g16
  have e33 := goodS_mul g18 (by omega) (by omega)
  have hpk : ∀ k ≤ m, LoadHolds rd (ofK (addressOfIndex (b0 + 70))) k ((piW rm ps m).getD k 0) :=
    fun k hk => by
      rw [List.getD_eq_getElem _ _ (by rw [piW_length]; omega)]
      exact hpi k (by rw [piW_length]; omega)
  have h31 : LoadHolds rd (σ (.n 33)) 0 ((piW rm ps m).getD m 0) := by
    rw [e33, e26, e6, loadHolds_mul_gen_pow, Nat.add_zero]; exact hpk m le_rfl
  obtain ⟨e34, l32⟩ := good_load_eq hS (n_ne_26 (by decide)) g19 h31
  have kl : ∀ {i : ℕ}, i < 8 → GoodS rd S (termW b0 outs) σ (.atom (.load (.n (kbV i)) (.n 8) i)) →
      σ (.n (kbV i)) = kbw.getD i 0 ∧ (Atom.load (.n (kbV i)) (.n 8) i).Holds rd σ :=
    fun hi g => good_load_eq hS (n_ne_26 (by decide)) g (hkb _ hi)
  obtain ⟨f0, m0⟩ := kl (i := 0) (by decide) k0
  obtain ⟨f1, m1⟩ := kl (i := 1) (by decide) k1
  obtain ⟨f2, m2⟩ := kl (i := 2) (by decide) k2
  obtain ⟨f3, m3⟩ := kl (i := 3) (by decide) k3
  obtain ⟨f4, m4⟩ := kl (i := 4) (by decide) k4
  obtain ⟨f5, m5⟩ := kl (i := 5) (by decide) k5
  obtain ⟨f6, m6⟩ := kl (i := 6) (by decide) k6
  obtain ⟨f7, m7⟩ := kl (i := 7) (by decide) k7
  have ekb : ∀ i < 8, σ (.n (kbV i)) = kbw.getD i 0
    | 0, _ => f0 | 1, _ => f1 | 2, _ => f2 | 3, _ => f3 | 4, _ => f4 | 5, _ => f5 | 6, _ => f6
    | 7, _ => f7 | _ + 8, h => absurd h (by omega)
  have r28 := good_rets g28
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at r28
  have e43 : σ (.n 43) = (stRes outs).1.getD 0 0 := by rw [r28]; simp [termW]
  have s0 : LoadHolds rd (σ (.n 26)) 0 (σ (.n 27)) := by
    rw [e26, e27, word_one]
    have := hpk 0 (by omega)
    rwa [piW_getD (by omega), ite_pos' rfl] at this
  have s1 : LoadHolds rd (σ (.n 26)) 1 (σ (.n 29)) := by
    rw [e26, e29, e28, e3]
    have := hpk 1 hm1
    rwa [piW_getD hm1, ite_neg' (by omega), Finset.Ico_self, Finset.prod_empty, mul_one] at this
  have a24 : ∀ k ≤ m, AddrIn R (σ (.n 26)) k := fun k hk =>
    ⟨b0 + 70 + k, by rw [e26, Main.addr_ofK], api k hk⟩
  have hw2 : word 2 0 = gen := word_gen
  refine ⟨fun s hs => ?_, fun q hq => ?_, e20, e21, e22, e23, e24, e25, e26,
    by rw [e31, e30, e6], e32, e34, ekb, e43⟩
  · simp only [termHeadT, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · trivial
    · exact e21
    · trivial
    · trivial
    · exact e23
    · trivial
    · exact e24
    · exact e25
    · trivial
    · exact e27
    · exact s0
    · exact l26
    · exact e29
    · exact s1
    · exact e30
    · exact e31
    · exact e32
    · refine ⟨?_, fun _ => trivial⟩
      rw [e31, e30, e6, hw2]
      exact isInK_add (by simpa using gen_pow_isInK 1) (gen_pow_isInK m)
    · exact e33
    · exact l32
    · exact m0
    · exact m1
    · exact m2
    · exact m3
    · exact m4
    · exact m5
    · exact m6
    · exact m7
    · trivial
  · simp only [termHeadT, List.filterMap_cons, Stmt.loadS, List.filterMap_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact a24 0 (by omega)
    · exact a14
    · exact a24 1 hm1
    · refine ⟨b0 + 70 + m, ?_, api m le_rfl⟩
      show (σ (.n 33)).limb 0 * addressOfIndex 0 = _
      rw [e33, e26, e6, ofK_gpow_mul_gen, Main.addr_ofK, Nat.add_zero]
    all_goals exact akb _ (by decide)

/-! ## The selectors -/

/-- **Committed column `c`'s selector block, completely**: its offset `g^o` from `col_offsets`,
its `g^κ` from the base, `sel_g = g_squares·g^34`, the dispatch to `column_selector__L{κ}`. -/
theorem sel_complete (hS : StoresAtPi S) {b0 : ℕ} {outs : List (List E × Main.Layout)} {c : ℕ}
    (hc : c < Tables.nCommittedCols) (hg : ∀ s ∈ selBlockT c, GoodS rd S (termW b0 outs) σ s)
    {o κ : ℕ} (hκ : κ < 31)
    (hoff : LoadHolds rd (σ (.n 10)) c (gen ^ o)) (aoff : AddrIn R (σ (.n 10)) c)
    (hkap : σ (.n (kbV (Tables.colKappaSrc c))) * gen ^ Tables.colKappaAdj c = gen ^ κ) :
    (∀ s ∈ selBlockT c, Fwd.SHolds TrivC rd σ s) ∧ (∀ s ∈ selBlockT c, DispOk σ s) ∧
      (∀ q ∈ (selBlockT c).filterMap Stmt.loadS, AddrIn R (σ q.1) q.2) ∧
      σ (.n (selStart c)) = gen ^ o ∧ σ (.n (selKap c).2.1) = gen ^ κ ∧
      σ (.n ((selKap c).2.2 + 1)) = σ (.n 0) * gen ^ 34 ∧
      σ (.n (selV c)) = (outs.getD (4 + c) ([], [])).1.getD 0 0 := by
  have hsrc : Tables.colKappaSrc c < 8 := by unfold Tables.colKappaSrc; split_ifs <;> omega
  have hadj : Tables.colKappaAdj c < 64 := by unfold Tables.colKappaAdj; split_ifs <;> omega
  have hs44 : 44 ≤ selStart c := by unfold selStart; split_ifs <;> omega
  have hss : 42 < selStart c + 1 := by omega
  have mm : ∀ s, s ∈ selBlockT c → GoodS rd S (termW b0 outs) σ s := hg
  simp only [selBlockT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mm
  have g0 := mm _ (Or.inl (Or.inl rfl))
  have gk : ∀ s ∈ (selKap c).1, GoodS rd S (termW b0 outs) σ s := fun s h => mm s (Or.inl (Or.inr h))
  have g1 := mm _ (Or.inr (Or.inl rfl))
  have g2 := mm _ (Or.inr (Or.inr (Or.inl rfl)))
  have g3 := mm _ (Or.inr (Or.inr (Or.inr rfl)))
  obtain ⟨k1, k2, k3, k4, k5⟩ := kapT_complete (C := TrivC) hsrc hadj hss gk
  obtain ⟨e0, l0⟩ := good_load_eq hS (n_ne_26 (by omega)) g0 hoff
  have e1 := good_const g1
  have e2 := goodS_mul g2 (by omega) (by omega)
  have r3 := good_rets g3
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at r3
  have e3 : σ (.n (selV c)) = (outs.getD (4 + c) ([], [])).1.getD 0 0 := by
    rw [r3]; exact termW_sel b0 outs hc
  have hw34 : word 17179869184 0 = gen ^ 34 := word_two_pow (a := 34) (by decide)
  have ek : σ (.n (selKap c).2.1) = gen ^ κ := by rw [selKap, k3, hkap]
  have hl : colSelNames.length = 31 := by simp [colSelNames]
  have hd : σ (.n (selKap c).2.1) = ofK (addressOfIndex κ) := by rw [ek, gen_pow_eq_ofK]
  refine ⟨fun s hs => ?_, fun s hs => ?_, fun q hq => ?_, e0, ek, by rw [e2, e1, hw34], e3⟩
  · simp only [selBlockT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with (rfl | hs) | rfl | rfl | rfl
    · exact l0
    · exact k1 s hs
    · exact e1
    · exact e2
    · exact ⟨κ, by omega, hd, trivial⟩
  · simp only [selBlockT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with (rfl | hs) | rfl | rfl | rfl
    · trivial
    · revert hs; unfold selKap kapT; split
      · simp
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (rfl | rfl) <;> trivial
    · trivial
    · trivial
    · exact ⟨κ, by omega, by omega, hd⟩
  · simp only [selBlockT, List.filterMap_append, List.filterMap_cons, Stmt.loadS,
      List.filterMap_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [selKap, k2] at hq
    simp only [List.not_mem_nil, or_false] at hq
    rcases hq with rfl
    exact aoff

/-! ## The tail -/

theorem termTailPre_eq : termTailPre =
    [.atom (.hint (.alloc (.n 1694) 41)), .atom (.const (.n 1695) (word 1 0)),
      .atom (.const (.n 1696) (word 64 0)), .atom (.mul (.n 1697) (.n 7) (.n 1696)),
      .call "eq_prefix_chain" [.n 1694, .n 1695, .n 11, .n 14, .n 1697] [],
      .atom (.const (.n 1698) (word 549755813888 0)), .atom (.mul (.n 1699) (.n 11) (.n 1698)),
      .atom (.const (.n 1700) (word 64 0)), .atom (.mul (.n 1701) (.n 7) (.n 1700)),
      .call "ring_switch_weight" [.n 1699, .n 14, .n 12, .n 1701] [.n 1702],
      .atom (.mul (.n 1703) (.n 1694) (.n 7)), .atom (.load (.n 1704) (.n 1703) 6),
      .atom (.mul (.n 1705) (.n 1693) (.n 1704)), .atom (.add (.n 1706) (.n 1702) (.n 1705)),
      .atom (.mul (.n 1707) (.n 1706) (.n (selV 4))), .atom (.add (.n 1708) (.n 1692) (.n 1707)),
      .atom (.hint (.alloc (.n 1709) 31)), .atom (.mul (.n 1710) (.n 1693) (.n 9)),
      .call "eq_prefix_chain" [.n 1709, .n 1710, .n 18, .n 14, .n 19] [],
      .atom (.mul (.n 1711) (.n 1709) (.n 19)), .atom (.load (.n 1712) (.n 1711) 0),
      .atom (.add (.n 1713) (.n 1708) (.n 1712)), .atom (.mul (.n 1714) (.n 1713) (.n 16)),
      .atom (.assertEq (.n 1714) (.n 17))] := rfl

/-- **The tail, completely**: the outputs' chain, the ring switch's weight, the out-of-domain
claim's chain, the terminal's check (given its value). -/
theorem tail_complete (hS : StoresAtPi S) {b0 : ℕ} {outs : List (List E × Main.Layout)}
    (hg : ∀ s ∈ termTailPre, GoodS rd S (termW b0 outs) σ s) {τ n : ℕ} {v v' : E}
    (e7 : σ (.n 7) = gen ^ τ) (e19 : σ (.n 19) = gen ^ n)
    (hch : LoadHolds rd (ofK (addressOfIndex (b0 + 105))) (τ + 6) v)
    (ach : R (b0 + 105 + (τ + 6)))
    (hod : LoadHolds rd (ofK (addressOfIndex (b0 + 146))) n v') (aod : R (b0 + 146 + n)) :
    (σ (.n 1714) = σ (.n 17) → ∀ s ∈ termTailPre, Fwd.SHolds TrivC rd σ s) ∧
      (∀ q ∈ termTailPre.filterMap Stmt.loadS, AddrIn R (σ q.1) q.2) ∧
      σ (.n 1694) = ofK (addressOfIndex (b0 + 105)) ∧ σ (.n 1695) = word 1 0 ∧
      σ (.n 1697) = gen ^ τ * word 64 0 ∧ σ (.n 1699) = σ (.n 11) * word 549755813888 0 ∧
      σ (.n 1701) = gen ^ τ * word 64 0 ∧ σ (.n 1702) = (outs.getD 99 ([], [])).1.getD 0 0 ∧
      σ (.n 1704) = v ∧ σ (.n 1709) = ofK (addressOfIndex (b0 + 146)) ∧
      σ (.n 1710) = σ (.n 1693) * σ (.n 9) ∧ σ (.n 1712) = v' ∧
      σ (.n 1714) = (σ (.n 1692) + (σ (.n 1702) + σ (.n 1693) * σ (.n 1704)) * σ (.n (selV 4)) +
        σ (.n 1712)) * σ (.n 16) := by
  have mm : ∀ s, s ∈ termTailPre → GoodS rd S (termW b0 outs) σ s := hg
  simp only [termTailPre_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at mm
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18,
    g19, g20, g21, g22, g23⟩ := mm
  have h4 : selV 4 < 1707 := by decide
  have e0 : σ (.n 1694) = ofK (addressOfIndex (b0 + 105)) := by
    rw [good_hint_alloc g0]; simp [termW]
  have e1 := good_const g1
  have e2 := good_const g2
  have e3 := goodS_mul g3 (by omega) (by omega)
  have e5 := good_const g5
  have e6 := goodS_mul g6 (by omega) (by omega)
  have e7' := good_const g7
  have e8 := goodS_mul g8 (by omega) (by omega)
  have r9 := good_rets g9
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at r9
  have e9 : σ (.n 1702) = (outs.getD 99 ([], [])).1.getD 0 0 := by rw [r9]; simp [termW]
  have e10 := goodS_mul g10 (by omega) (by omega)
  have h11 : LoadHolds rd (σ (.n 1703)) 6 v := by
    rw [e10, e0, e7, loadHolds_mul_gen_pow]; exact hch
  obtain ⟨e11, l11⟩ := good_load_eq hS (n_ne_26 (by decide)) g11 h11
  have e12 := goodS_mul g12 (by omega) (by omega)
  have e13 := good_add g13
  have e14 := goodS_mul g14 (by omega) h4
  have e15 := good_add g15
  have e16 : σ (.n 1709) = ofK (addressOfIndex (b0 + 146)) := by
    rw [good_hint_alloc g16]; simp [termW]
  have e17 := goodS_mul g17 (by omega) (by omega)
  have e19' := goodS_mul g19 (by omega) (by omega)
  have h20 : LoadHolds rd (σ (.n 1711)) 0 v' := by
    rw [e19', e16, e19, loadHolds_mul_gen_pow, Nat.add_zero]; exact hod
  obtain ⟨e20, l20⟩ := good_load_eq hS (n_ne_26 (by decide)) g20 h20
  have e21 := good_add g21
  have e22 := goodS_mul g22 (by omega) (by omega)
  refine ⟨fun hfin s hs => ?_, fun q hq => ?_, e0, e1, by rw [e3, e2, e7], by rw [e6, e5],
    by rw [e8, e7', e7], e9, e11, e16, e17, e20, by rw [e22, e21, e15, e14, e13, e12]⟩
  · simp only [termTailPre_eq, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · trivial
    · exact e1
    · exact e2
    · exact e3
    · trivial
    · exact e5
    · exact e6
    · exact e7'
    · exact e8
    · trivial
    · exact e10
    · exact l11
    · exact e12
    · exact e13
    · exact e14
    · exact e15
    · trivial
    · exact e17
    · trivial
    · exact e19'
    · exact l20
    · exact e21
    · exact e22
    · show σ (.n 1714) + σ (.n 17) = 0
      rw [hfin]; exact e_add_self _
  · simp only [termTailPre_eq, List.filterMap_cons, Stmt.loadS, List.filterMap_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · refine ⟨b0 + 105 + (τ + 6), ?_, ach⟩
      show (σ (.n 1703)).limb 0 * addressOfIndex 6 = _
      rw [e10, e0, e7, ofK_gpow_mul_gen, Main.addr_ofK, Nat.add_assoc]
    · refine ⟨b0 + 146 + n, ?_, aod⟩
      show (σ (.n 1711)).limb 0 * addressOfIndex 0 = _
      rw [e19', e16, e19, ofK_gpow_mul_gen, Main.addr_ofK, Nat.add_zero]

end
end LeanVM.Guest.B1.VerifySub
