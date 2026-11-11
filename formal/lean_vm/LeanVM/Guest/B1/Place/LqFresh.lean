/-
  LeanVM.Guest.B1.Place.LqFresh

  `level_queries`' words bound, from a valid tree of a fresh instance.
-/

module

public import LeanVM.Guest.B1.Place.LqVmc
public import LeanVM.Guest.B1.Place.LqSem

/-!
# The words bound from a fresh instance

`lqBnd`: `level_queries`' frame, its two buffers, `verify_merkle_cap`'s frame and
`opening_queries`' exact words `oqBound`. `lq_node`: the node of `level_queries` over a tree of
each callee is valid, its words its frame, its buffers and its callees'. `lqBnd_le`: every bound of
the valid trees of `level_queries` (`TotalLe`) is at least `lqBnd`, since a fresh instance (the
words `opening_queries` reads laid out from `g^0`, `frV`, then the cap, the flags and its chain
buffer, in the memory `cellRd`) has a valid tree of at least `lqBnd` words: no memory the caller
gives is needed, so the bound holds whatever the frame sizes.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir (lqIters lqTable natStr oqName digitsVal osPowDigits osPowLen osPowSteps
  lqBody lqAtoms lqVal lqOqArgs lqVal_facts lqVal_holds lqAtoms_straight lqAtoms_calls
  lqAtoms_allocs lqBody_atoms FnIs osParams gw)
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- `level_queries`' words: its frame, its two buffers, `verify_merkle_cap`'s frame and
`opening_queries`' words. -/
def lqBnd (fs : String → ℕ) (name : String) (q base il leaf d cd : ℕ) : ℕ :=
  fs name + (4 * 2 ^ cd + 2 ^ cd) + (fs (vmcName cd) +
    oqBound fs (oqName q base il leaf d cd) (oqLoopOf (oqName q base il leaf d cd)) (lqIters q base))

theorem lqLogG_gw {e : ℕ} (he : e < 2 ^ 64 - 1) : logG (gw e) = e := by
  rw [Whir.gw_eq (by unfold u128Bound; omega), logG_gen_pow he]

/-- **The node of `level_queries`** over a valid tree of each callee, at the honest valuation. -/
theorem lq_node (fs : String → ℕ) {name : String} {q base il leaf d cd : ℕ}
    (hfn : FnIs name (osParams 3) (lqBody q base il leaf d cd))
    (hpw : digitsVal (osPowDigits q) 1 = q) (hcd8 : cd ≤ 8) {rd : Reader}
    {lam WP RW CAP FL r0 r1 sum : E} {t1 t2 : Memory.Tree} (h1n : t1.name = vmcName cd)
    (h1 : t1.Valid coreProgram rd [CAP, FL] [r0, r1]) (h1b : t1.BufsOk coreProgram)
    (h2n : t2.name = oqName q base il leaf d cd)
    (h2 : t2.Valid coreProgram rd [CAP, FL, lam, lam ^ q, WP, RW, gw (lqIters q base)] [sum])
    (h2b : t2.BufsOk coreProgram) :
    let t := Memory.Tree.node name (lqVal q cd (lqIters q base) lam WP RW CAP FL r0 r1 sum)
      [4 * 2 ^ cd, 2 ^ cd] [t1, t2]
    t.name = name ∧ t.Valid coreProgram rd [lam, WP, RW] [r0, r1, sum, lam ^ q] ∧
      t.BufsOk coreProgram ∧ t.total fs = fs name + (t1.total fs + t2.total fs) + (4 * 2 ^ cd + 2 ^ cd) := by
  intro t
  obtain ⟨fn, hf, hps, hb⟩ := hfn
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, e0, e1, e2, e3, e4, e5, hp2, -⟩ :=
    lqVal_facts (C := fun _ _ _ ↦ True) (rd := rd) q cd (lqIters q base) hpw lam WP RW CAP FL r0 r1
      sum
  have hhold := lqVal_holds (C := fun _ _ _ ↦ True) (rd := rd) q base il leaf d cd hpw
    (lam := lam) (WP := WP) (RW := RW) (CAP := CAP) (FL := FL) (r0 := r0) (r1 := r1) (sum := sum)
    trivial trivial
  dsimp only [t]
  generalize lqVal q cd (lqIters q base) lam WP RW CAP FL r0 r1 sum = σ at *
  have hst := lqAtoms_straight q base il leaf d cd
  have hw : walk σ fn.body = .ret ((lqAtoms q base il leaf d cd).flatMap (Main.slEvs σ))
      [.n (9 + osPowLen q + 2), .n (9 + osPowLen q + 3), .n (9 + osPowLen q + 4),
        .n (9 + osPowLen q + 5)] := by
    rw [hb, lqBody_atoms]; exact Main.walk_straight σ _ _ hst
  obtain ⟨-, i2, -, i4⟩ := Main.straight_parts σ _ hst
  rw [← hb] at hhold
  have hsat := walk_sat (P := coreProgram) fn.body
    (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hhold
  rw [hw] at hsat
  refine ⟨rfl, ⟨fn, hf, ?_, _, _, hw, hsat.2, fun e he ↦ (hsat.1 e he).1, ?_⟩, ⟨?_, h1b, h2b, trivial⟩,
    ?_⟩
  · rw [hps]
    simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, a0, a1, a2]
  · rw [i4, lqAtoms_calls]
    simp only [List.map_cons, List.map_nil, Main.mkCall, Tree.KidsValid, ↓reduceIte, a4, a6, a7,
      a8, lqOqArgs, a0, a1, a2, hp2, e0, e1]
    exact ⟨h1n, h1, h2n, h2, trivial⟩
  · rw [events_node hf hw, i2, lqAtoms_allocs]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, a3, a5]
    have hc : 2 ^ cd ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) hcd8
    rw [lqLogG_gw (by omega), lqLogG_gw (by omega)]
  · simp only [total_node, Tree.totalKids, List.sum_cons, List.sum_nil]
    omega

/-! ## A fresh instance -/

section Fresh

variable (s : Oq) (q : ℕ)

/-- The row weights' words. -/
def frW : ℕ := s.lo + s.I / s.lo

/-- A query's window words. -/
def frQn : ℕ := qwN (s.pd + s.cd) s.cd

/-- Query `k`'s windows. -/
def frEb (k : ℕ) : ℕ := frW s + q + k * frQn s

/-- The cap. -/
def frC : ℕ := frW s + q + q * frQn s

/-- The flags. -/
def frFl : ℕ := frC s q + 4 * 2 ^ s.cd

/-- The chain buffer. -/
def frCh : ℕ := frFl s q + 2 ^ s.cd

/-- The fresh instance's words: the row weights `w`, the window pointers, query `k`'s windows of
its position `qs k`, the cap, the flags and the chain. -/
def frV (w : ℕ → E) (qs : ℕ → ℕ) (capW flW chain : List E) (x : ℕ) : E :=
  if x < frW s then w x
  else if x < frW s + q then ofK (addressOfIndex (frEb s q (x - frW s)))
  else if x < frC s q then
    gen ^ qwVal (s.pd + s.cd) s.cd (qs ((x - frW s - q) / frQn s)) ((x - frW s - q) % frQn s)
  else if x < frFl s q then capW.getD (x - frC s q) 0
  else if x < frCh s q then flW.getD (x - frFl s q) 0
  else chain.getD (x - frCh s q) 0

variable {s q} {w : ℕ → E} {qs : ℕ → ℕ} {capW flW chain : List E}

theorem frV_w {l : ℕ} (hl : l < frW s) : frV s q w qs capW flW chain l = w l := by
  simp [frV, hl]

theorem frV_p {k : ℕ} (hk : k < q) :
    frV s q w qs capW flW chain (frW s + k) = ofK (addressOfIndex (frEb s q k)) := by
  unfold frV
  rw [ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

theorem frV_win {k i : ℕ} (hk : k < q) (hi : i < frQn s) :
    frV s q w qs capW flW chain (frEb s q k + i) = gen ^ qwVal (s.pd + s.cd) s.cd (qs k) i := by
  have h1 : k * frQn s + i < q * frQn s := by
    calc k * frQn s + i < k * frQn s + frQn s := by omega
      _ = (k + 1) * frQn s := by ring
      _ ≤ q * frQn s := Nat.mul_le_mul_right _ hk
  have h2 : frEb s q k + i - frW s - q = i + frQn s * k := by unfold frEb; rw [mul_comm]; omega
  unfold frV
  rw [ite_eq_right (by unfold frEb; omega), ite_eq_right (by unfold frEb; omega),
    ite_eq_left (by unfold frEb frC; omega), h2, Nat.add_mul_div_left _ _ (by omega),
    Nat.add_mul_mod_self_left, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, Nat.zero_add]

theorem frV_cap {j : ℕ} (hj : j < 4 * 2 ^ s.cd) :
    frV s q w qs capW flW chain (frC s q + j) = capW.getD j 0 := by
  unfold frV
  rw [ite_eq_right (by unfold frC; omega), ite_eq_right (by unfold frC; omega), ite_eq_right (by omega),
    ite_eq_left (by unfold frFl; omega), Nat.add_sub_cancel_left]

theorem frV_fl {j : ℕ} (hj : j < 2 ^ s.cd) :
    frV s q w qs capW flW chain (frFl s q + j) = flW.getD j 0 := by
  unfold frV
  rw [ite_eq_right (by unfold frFl frC; omega), ite_eq_right (by unfold frFl frC; omega),
    ite_eq_right (by unfold frFl; omega), ite_eq_right (by omega), ite_eq_left (by unfold frCh; omega),
    Nat.add_sub_cancel_left]

theorem frV_ch (j : ℕ) : frV s q w qs capW flW chain (frCh s q + j) = chain.getD j 0 := by
  unfold frV
  rw [ite_eq_right (by unfold frCh frFl frC; omega), ite_eq_right (by unfold frCh frFl frC; omega),
    ite_eq_right (by unfold frCh frFl; omega),
    ite_eq_right (by unfold frCh; generalize 2 ^ s.cd = t; omega), ite_eq_right (by omega),
    Nat.add_sub_cancel_left]

end Fresh

theorem cap_lt {pd cd x : ℕ} (hx : x < 2 ^ (pd + cd)) (e : ℕ) (he : e < 2) :
    2 * (2 ^ cd + x / 2 ^ pd) + e < 4 * 2 ^ cd := by
  have : x / 2 ^ pd < 2 ^ cd := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_comm]; exact hx
  omega

theorem flag_lt {pd cd x : ℕ} (hcd : 1 ≤ cd) (hx : x < 2 ^ (pd + cd)) :
    2 ^ (cd - 1) + x / 2 ^ (pd + 1) < 2 ^ cd := by
  have h2 : 2 ^ cd = 2 * 2 ^ (cd - 1) := by
    rw [← pow_succ']; congr 1; omega
  have : x / 2 ^ (pd + 1) < 2 ^ (cd - 1) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    rwa [show cd - 1 + (pd + 1) = pd + cd by omega]
  omega

theorem lq_count {q base : ℕ} (hb : base ≤ 1) : oqCount (q % 2 * base) base (lqIters q base) = q := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl
  · simp [oqCount, lqIters]
  · simp [oqCount, lqIters]; omega

/-- **`opening_queries`' words on a memory**: the caller's (`LqMem`), the cap and the flags word by
word at `g^ecap` and `g^eflags`, on the honest cap and flags (`LqCaps`). -/
theorem oqLinMem_of {rd : Reader} {s : Oq} {q : ℕ} {capW flW : List E} {r0 r1 : E} {qs : ℕ → ℕ}
    {rows : ℕ → List K} {sibs : ℕ → List Digest} (hc : LqCaps s q capW flW r0 r1 qs rows sibs)
    (hcd : 1 ≤ s.cd) {ecap eflags eqp ewp : ℕ} {w : ℕ → E} {eb : ℕ → ℕ}
    (hlm : LqMem rd s q eqp ewp w eb qs)
    (hcap : ∀ j < 4 * 2 ^ s.cd, rd (addressOfIndex (ecap + j)) = some (capW.getD j 0))
    (hfl : ∀ j < 2 ^ s.cd, rd (addressOfIndex (eflags + j)) = some (flW.getD j 0)) :
    OqLinMem rd s (ofK (addressOfIndex ecap)) (ofK (addressOfIndex eflags))
      (ofK (addressOfIndex ewp)) (ofK (addressOfIndex eqp)) w eb qs rows sibs q := by
  obtain ⟨-, -, -, hk⟩ := hc
  refine ⟨hlm.1, fun k hkq ↦ ?_⟩
  obtain ⟨hp, hwin⟩ := hlm.2 k hkq
  obtain ⟨hqs, -, -, c0, c1, f1⟩ := hk k hkq
  refine ⟨hp, hwin, ?_, ?_, ?_⟩
  · have h0 := cap_lt hqs 0 (by decide)
    rw [Nat.add_zero] at h0
    rw [loadHolds_addr, hcap _ h0, c0]
  · rw [loadHolds_addr, hcap _ (cap_lt hqs 1 (by decide)), c1]
  · rw [loadHolds_addr, hfl _ (flag_lt hcd hqs), f1]

/-- **`opening_queries`' words in a region**: the caller's (`LqReg`), the cap and the flags. -/
theorem oqLinReg_of {R : ℕ → Prop} {s : Oq} {q : ℕ} {capW flW : List E} {r0 r1 : E}
    {qs : ℕ → ℕ} {rows : ℕ → List K} {sibs : ℕ → List Digest}
    (hc : LqCaps s q capW flW r0 r1 qs rows sibs) (hcd : 1 ≤ s.cd) {ecap eflags eqp ewp : ℕ}
    {eb : ℕ → ℕ} (hlr : LqReg R s q eqp ewp eb) (hcap : ∀ j < 4 * 2 ^ s.cd, R (ecap + j))
    (hfl : ∀ j < 2 ^ s.cd, R (eflags + j)) : OqLinReg R s ecap eflags eqp ewp eb qs q := by
  obtain ⟨-, -, -, hk⟩ := hc
  refine ⟨hlr.1, fun k hkq ↦ ⟨(hlr.2 k hkq).1, (hlr.2 k hkq).2, ?_, fun e he ↦ ?_⟩⟩
  · have := hfl _ (flag_lt hcd (hk k hkq).1)
    rwa [Nat.add_comm (2 ^ (s.cd - 1))] at this
  · exact hcap _ (cap_lt (hk k hkq).1 e he)

end
end LeanVM.Guest.B1
