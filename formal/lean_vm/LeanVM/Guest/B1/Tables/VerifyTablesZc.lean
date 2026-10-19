/-
  LeanVM.Guest.B1.Tables.VerifyTablesZc

  `verify_tables`' table sumcheck: its round count pinned to the largest height, its rounds,
  the reduced point stored reversed in `chi`, and the tables' weights.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesPad
public import LeanVM.Guest.B1.Tables.VerifyTablesPoly

/-!
# The table sumcheck (G:1706-1745)

`verify_tables` hints `g_zc_n = g^n` and pins `n` to the largest of the six heights, at most the
bus point's length; squeezes `ξ` and its powers; runs `n` rounds of `sumcheck_round4`
(`__loop79`), storing round `j`'s challenge at `chi[n - 1 - j]` and the running product of the
challenges in `zc_cprod`; and fills `zc_peq` with the prefix products of
`1 + zeta[k] + chi[k]` (`__loop80`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `__loop80`: the equality prefix chain -/

theorem find_loop80 : coreProgram.find? "__loop80" = some Data.core139 :=
  Program.find?_of_indexOf? (j := 139) (by decide +kernel) rfl

/-- `__loop80`'s statements before its `ret`. -/
noncomputable def l80Pre : List Stmt := (Fn.body Data.core139).take 18

theorem core139_body : Fn.body Data.core139 = l80Pre ++ [.ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem l80Pre_noRet : Stmt.noRetList l80Pre = true := by decide +kernel

/-- **`__loop80`**, one iteration (G:1741-1742): `peq[x·g] = peq[x]·(1 + zeta[x] + chi[x])`. -/
theorem loop80_step {rd : Reader} {N peq zeta chi x : E}
    (h : coreProgram.Rel rd "__loop80" [x, N, peq, zeta, chi] []) :
    (∃ p z c, LoadHolds rd (peq * x) 0 p ∧ LoadHolds rd (zeta * x) 0 z ∧
      LoadHolds rd (chi * x) 0 c ∧ LoadHolds rd (peq * x) 1 (p * (1 + z + c))) ∧
      (x * gen + N ≠ 0 → coreProgram.Rel rd "__loop80" [x * gen, N, peq, zeta, chi] []) := by
  obtain ⟨σ, hp, hb, -⟩ := rel_pre find_loop80 core139_body l80Pre_noRet h
  simp only [show Fn.params Data.core139 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hp
  have hnr := l80Pre_noRet
  have a5 := holds_atom hnr hb 0 (.mul (.n 5) (.n 2) (.n 0)) (by decide +kernel)
  have l6 := holds_atom hnr hb 1 (.load (.n 6) (.n 5) 0) (by decide +kernel)
  have a7 := holds_atom hnr hb 2 (.const (.n 7) (word 1 0 0)) (by decide +kernel)
  have a8 := holds_atom hnr hb 3 (.mul (.n 8) (.n 3) (.n 0)) (by decide +kernel)
  have l9 := holds_atom hnr hb 4 (.load (.n 9) (.n 8) 0) (by decide +kernel)
  have a10 := holds_atom hnr hb 5 (.add (.n 10) (.n 7) (.n 9)) (by decide +kernel)
  have a11 := holds_atom hnr hb 6 (.mul (.n 11) (.n 4) (.n 0)) (by decide +kernel)
  have l12 := holds_atom hnr hb 7 (.load (.n 12) (.n 11) 0) (by decide +kernel)
  have a13 := holds_atom hnr hb 8 (.add (.n 13) (.n 10) (.n 12)) (by decide +kernel)
  have a14 := holds_atom hnr hb 9 (.mul (.n 14) (.n 6) (.n 13)) (by decide +kernel)
  have a15 := holds_atom hnr hb 10 (.mul (.n 15) (.n 2) (.n 0)) (by decide +kernel)
  have l14 := holds_atom hnr hb 11 (.load (.n 14) (.n 15) 1) (by decide +kernel)
  have a16 := holds_atom hnr hb 12 (.const (.n 16) (word 2 0 0)) (by decide +kernel)
  have a17 := holds_atom hnr hb 13 (.mul (.n 17) (.n 0) (.n 16)) (by decide +kernel)
  have a18 := holds_atom hnr hb 14 (.add (.n 18) (.n 17) (.n 1)) (by decide +kernel)
  have a19 := holds_atom hnr hb 15 (.const (.n 19) (word 2 0 0)) (by decide +kernel)
  have a20 := holds_atom hnr hb 16 (.mul (.n 20) (.n 0) (.n 19)) (by decide +kernel)
  have hc := holds_callIf hnr hb 17 (.n 18) "__loop80" [.n 20, .n 1, .n 2, .n 3, .n 4]
    (by decide +kernel)
  simp only [Atom.Holds, word_one, word_gen, List.map_cons, List.map_nil] at *
  refine ⟨⟨σ (.n 6), σ (.n 9), σ (.n 12), by rw [← a5]; exact l6, by rw [← a8]; exact l9,
    by rw [← a11]; exact l12, ?_⟩, fun hne => ?_⟩
  · have e14 : σ (.n 14) = σ (.n 6) * (1 + σ (.n 9) + σ (.n 12)) := by rw [a14, a13, a10, a7]
    rw [← e14, ← a15]; exact l14
  · have := hc (by rw [a18, a17, a16]; exact hne)
    rw [a20, a19] at this
    exact this

/-- **`zc_peq`** (G:1739-1742): over `n` coordinates of `zeta` and `chi`, `peq[k]` is
`eqEval` of their first `k`. -/
theorem loop80_sound {rd : Reader} {peq zeta chi : E} {n : ℕ} (hn : n < ordG)
    {zs cs : List E} (hz : ReadsAt rd zeta zs) (hc : ReadsAt rd chi cs) (hzl : n ≤ zs.length)
    (hcl : n ≤ cs.length) (h0 : LoadHolds rd peq 0 1)
    (h : 1 + gen ^ n ≠ 0 → coreProgram.Rel rd "__loop80" [1, gen ^ n, peq, zeta, chi] []) :
    ∀ k ≤ n, LoadHolds rd peq k (eqEval (zs.take k) (cs.take k)) := by
  have hb := Main.loop_sound (ps := [gen ^ n, peq, zeta, chi]) hn rfl
    (fun x hx => loop80_step hx) h
  intro k hk
  induction k with
  | zero => simpa [eqEval] using h0
  | succ k ih =>
    obtain ⟨p, z, c, lp, lz, lc, lp1⟩ := hb k (by omega)
    rw [loadHolds_gen_pow_mul, Nat.add_zero] at lp lz lc
    rw [loadHolds_gen_pow_mul] at lp1
    rw [loadHolds_unique lp (ih (by omega)), loadHolds_unique lz (hz k (by omega)),
      loadHolds_unique lc (hc k (by omega)), ← eqEval_take_succ _ _ _ (by omega) (by omega)] at lp1
    exact lp1

/-! ## `__loop79`: the rounds -/

theorem find_loop79 : coreProgram.find? "__loop79" = some Data.core138 :=
  Program.find?_of_indexOf? (j := 138) (by decide +kernel) rfl

/-- `__loop79`'s statements before its `ret`. -/
noncomputable def l79Pre : List Stmt := (Fn.body Data.core138).take 28

theorem core138_body : Fn.body Data.core138 = l79Pre ++ [.ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem l79Pre_noRet : Stmt.noRetList l79Pre = true := by decide +kernel

/-- `g⁻¹`, the guest's `INV_GEN`. -/
abbrev wInvG : E := word 9223372036854775821 0 0

/-- **Round `x` of the table sumcheck** (G:1727-1736): the slot at `rounds·x⁴` holds the state of
`cv`, the cursor and the claim; the three words at the cursor run `roundPoly 4` to `claim'` and the
challenge `rk`, stored at `chi[q]` with `q·x = g^n·g⁻¹`; the next slot holds the new state, the
cursor three words on and `claim'`; and `cprod[x·g] = cprod[x]·rk`. -/
def ZcRound (rd : Reader) (rounds chi gn cprod x : E) : Prop :=
  ∃ (cv : Digest) (cur claim c0 c2 c3 claim' rk : E) (cv' : Digest) (q c : E),
    LoadHolds rd (rounds * x ^ 4) 0 (digestScalars cv).1 ∧
    LoadHolds rd (rounds * x ^ 4) 1 (digestScalars cv).2 ∧
    LoadHolds rd (rounds * x ^ 4) 2 cur ∧ LoadHolds rd (rounds * x ^ 4) 3 claim ∧
    ReadsAt rd cur [c0, c2, c3] ∧ RunsTo (roundPoly 4 claim none) cv [c0, c2, c3] (claim', rk) cv' ∧
    gn * wInvG = q * x ∧ LoadHolds rd (chi * q) 0 rk ∧
    LoadHolds rd (rounds * x ^ 4) 4 (digestScalars cv').1 ∧
    LoadHolds rd (rounds * x ^ 4) 5 (digestScalars cv').2 ∧
    LoadHolds rd (rounds * x ^ 4) 6 (cur * gen ^ 3) ∧ LoadHolds rd (rounds * x ^ 4) 7 claim' ∧
    LoadHolds rd (cprod * x) 0 c ∧ LoadHolds rd (cprod * x) 1 (c * rk)

/-- **`__loop79`**, one iteration: the round, then the loop at `x·g` while `x·g ≠ g^n`. -/
theorem loop79_step {rd : Reader} {N rounds chi gn cprod x : E}
    (h : coreProgram.Rel rd "__loop79" [x, N, rounds, chi, gn, cprod] []) :
    ZcRound rd rounds chi gn cprod x ∧
      (x * gen + N ≠ 0 → coreProgram.Rel rd "__loop79" [x * gen, N, rounds, chi, gn, cprod] []) := by
  obtain ⟨σ, hp, hb, -⟩ := rel_pre find_loop79 core138_body l79Pre_noRet h
  simp only [show Fn.params Data.core138 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hp
  have hnr := l79Pre_noRet
  have a6 := holds_atom hnr hb 0 (.mul (.n 6) (.n 0) (.n 0)) (by decide +kernel)
  have a7 := holds_atom hnr hb 1 (.mul (.n 7) (.n 6) (.n 6)) (by decide +kernel)
  have a8 := holds_atom hnr hb 2 (.mul (.n 8) (.n 2) (.n 7)) (by decide +kernel)
  have l9 := holds_atom hnr hb 3 (.load (.n 9) (.n 8) 0) (by decide +kernel)
  have l10 := holds_atom hnr hb 4 (.load (.n 10) (.n 8) 1) (by decide +kernel)
  have l11 := holds_atom hnr hb 5 (.load (.n 11) (.n 8) 2) (by decide +kernel)
  have l12 := holds_atom hnr hb 6 (.load (.n 12) (.n 8) 3) (by decide +kernel)
  have c7 := holds_call hnr hb 7 "sumcheck_round4" [.n 9, .n 10, .n 11, .n 12]
    [.n 13, .n 14, .n 15, .n 16, .n 17] (by decide +kernel)
  have a18 := holds_atom hnr hb 8 (.const (.n 18) wInvG) (by decide +kernel)
  have a19 := holds_atom hnr hb 9 (.mul (.n 19) (.n 4) (.n 18)) (by decide +kernel)
  have a19' := holds_atom hnr hb 10 (.mul (.n 19) (.n 20) (.n 0)) (by decide +kernel)
  have a21 := holds_atom hnr hb 11 (.mul (.n 21) (.n 3) (.n 20)) (by decide +kernel)
  have l17 := holds_atom hnr hb 12 (.load (.n 17) (.n 21) 0) (by decide +kernel)
  have l13 := holds_atom hnr hb 13 (.load (.n 13) (.n 8) 4) (by decide +kernel)
  have l14 := holds_atom hnr hb 14 (.load (.n 14) (.n 8) 5) (by decide +kernel)
  have l15 := holds_atom hnr hb 15 (.load (.n 15) (.n 8) 6) (by decide +kernel)
  have l16 := holds_atom hnr hb 16 (.load (.n 16) (.n 8) 7) (by decide +kernel)
  have a22 := holds_atom hnr hb 17 (.mul (.n 22) (.n 5) (.n 0)) (by decide +kernel)
  have l23 := holds_atom hnr hb 18 (.load (.n 23) (.n 22) 0) (by decide +kernel)
  have a24 := holds_atom hnr hb 19 (.mul (.n 24) (.n 23) (.n 17)) (by decide +kernel)
  have a25 := holds_atom hnr hb 20 (.mul (.n 25) (.n 5) (.n 0)) (by decide +kernel)
  have l24 := holds_atom hnr hb 21 (.load (.n 24) (.n 25) 1) (by decide +kernel)
  have a26 := holds_atom hnr hb 22 (.const (.n 26) (word 2 0 0)) (by decide +kernel)
  have a27 := holds_atom hnr hb 23 (.mul (.n 27) (.n 0) (.n 26)) (by decide +kernel)
  have a28 := holds_atom hnr hb 24 (.add (.n 28) (.n 27) (.n 1)) (by decide +kernel)
  have a29 := holds_atom hnr hb 25 (.const (.n 29) (word 2 0 0)) (by decide +kernel)
  have a30 := holds_atom hnr hb 26 (.mul (.n 30) (.n 0) (.n 29)) (by decide +kernel)
  have hc := holds_callIf hnr hb 27 (.n 28) "__loop79" [.n 30, .n 1, .n 2, .n 3, .n 4, .n 5]
    (by decide +kernel)
  simp only [Atom.Holds, word_gen, List.map_cons, List.map_nil] at *
  obtain ⟨cv, c0, c2, c3, claim', r, cv', hcv, hrd, hrun, hret⟩ :=
    (sumcheck_round4_iff rd _ _).mp c7
  simp only [List.cons.injEq] at hret
  obtain ⟨e13, e14, e15, e16, e17, -⟩ := hret
  have hq : σ (.n 8) = σ (.n 2) * σ (.n 0) ^ 4 := by rw [a8, a7, a6]; ring
  rw [hq] at l9 l10 l11 l12 l13 l14 l15 l16
  refine ⟨⟨cv, σ (.n 11), σ (.n 12), c0, c2, c3, claim', r, cv', σ (.n 20), σ (.n 23), ?_, ?_, l11,
    l12, hrd, hrun, by rw [← a19', a19, a18], ?_, ?_, ?_, ?_, ?_, by rw [← a22]; exact l23, ?_⟩,
    fun hne => ?_⟩
  · have e9 : σ (.n 9) = (digestScalars cv).1 := congrArg Prod.fst hcv
    rw [← e9]; exact l9
  · have e10 : σ (.n 10) = (digestScalars cv).2 := congrArg Prod.snd hcv
    rw [← e10]; exact l10
  · rw [← e17, ← a21]; exact l17
  · rw [← e13]; exact l13
  · rw [← e14]; exact l14
  · rw [← e15]; exact l15
  · rw [← e16]; exact l16
  · rw [← e17, ← a24, ← a25]; exact l24
  · have := hc (by rw [a28, a27, a26]; exact hne)
    rw [a30, a29] at this
    exact this

/-! ## The rounds, chained -/

theorem vt_prodE_eq (l : List E) : prodE l = l.prod := by
  suffices h : ∀ a : E, l.foldl (· * ·) a = a * l.prod by rw [prodE, h, one_mul]
  induction l with
  | nil => simp
  | cons x l ih => intro a; rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]

theorem wInvG_mul_gen : word 9223372036854775821 0 0 * gen = 1 := by
  rw [word_ofK, show gen = ofK (K.ofBits 2) from rfl, ← ofK_mul', ← ofK_one]
  exact congrArg ofK (by decide +kernel)

/-- Round `j` with its pointers resolved: slot `j` of `rounds`, `chi[n - 1 - j]`, `cprod[j]`. -/
def ZcAt (rd : Reader) (rounds chi cprod : E) (n j : ℕ) : Prop :=
  ∃ (cv : Digest) (cur claim c0 c2 c3 claim' rk : E) (cv' : Digest) (c : E),
    LoadHolds rd rounds (4 * j) (digestScalars cv).1 ∧
    LoadHolds rd rounds (4 * j + 1) (digestScalars cv).2 ∧
    LoadHolds rd rounds (4 * j + 2) cur ∧ LoadHolds rd rounds (4 * j + 3) claim ∧
    ReadsAt rd cur [c0, c2, c3] ∧ RunsTo (roundPoly 4 claim none) cv [c0, c2, c3] (claim', rk) cv' ∧
    LoadHolds rd chi (n - 1 - j) rk ∧
    LoadHolds rd rounds (4 * j + 4) (digestScalars cv').1 ∧
    LoadHolds rd rounds (4 * j + 5) (digestScalars cv').2 ∧
    LoadHolds rd rounds (4 * j + 6) (cur * gen ^ 3) ∧ LoadHolds rd rounds (4 * j + 7) claim' ∧
    LoadHolds rd cprod j c ∧ LoadHolds rd cprod (j + 1) (c * rk)

theorem vt_gen_ne_zero : gen ≠ 0 := by
  intro h
  apply g_ne_zero
  apply ofK_injective
  rw [ofK_zero]
  exact h

/-- `q·g^j = g^n·g⁻¹`, `j < n`: `q = g^(n - 1 - j)`. -/
theorem chi_slot {q : E} {n j : ℕ} (hj : j < n) (hq : gen ^ n * wInvG = q * gen ^ j) :
    q = gen ^ (n - 1 - j) := by
  have hg : gen ^ (j + 1) ≠ 0 := pow_ne_zero _ vt_gen_ne_zero
  have : q * gen ^ (j + 1) = gen ^ (n - 1 - j) * gen ^ (j + 1) := by
    rw [← pow_add, show n - 1 - j + (j + 1) = n by omega, pow_succ, ← mul_assoc, ← hq, mul_assoc,
      wInvG_mul_gen, mul_one]
  exact mul_right_cancel₀ hg this

theorem zcAt_of_round {rd : Reader} {rounds chi cprod : E} {n j : ℕ} (hj : j < n)
    (h : ZcRound rd rounds chi (gen ^ n) cprod (gen ^ j)) : ZcAt rd rounds chi cprod n j := by
  obtain ⟨cv, cur, claim, c0, c2, c3, claim', rk, cv', q, c, i0, i1, i2, i3, hrd, hrun, hq, hchi,
    o4, o5, o6, o7, hc0, hc1⟩ := h
  have hr : ∀ k w, LoadHolds rd (rounds * (gen ^ j) ^ 4) k w ↔ LoadHolds rd rounds (4 * j + k) w := by
    intro k w; rw [← pow_mul, show j * 4 = 4 * j by ring, loadHolds_gen_pow_mul]
  rw [chi_slot hj hq, loadHolds_gen_pow_mul, Nat.add_zero] at hchi
  rw [loadHolds_gen_pow_mul, Nat.add_zero] at hc0
  rw [loadHolds_gen_pow_mul] at hc1
  rw [hr] at i0 i1 i2 i3 o4 o5 o6 o7
  rw [Nat.add_zero] at i0
  exact ⟨cv, cur, claim, c0, c2, c3, claim', rk, cv', c, i0, i1, i2, i3, hrd, hrun, hchi, o4, o5,
    o6, o7, hc0, hc1⟩

/-- **The table sumcheck's rounds, chained**: from slot `b` (the state of `cv0`, the cursor, the
claim) and `cprod[b] = c0`, the words `ws` at the cursor run `L` plain rounds to the challenges `rs`
and the claim `cl`; `rs[j]` is at `chi[n - 1 - (b + j)]`, the challenges' prefix products times `c0`
are in `cprod`, and slot `b + L` holds the final state, the cursor `3L` words on and `cl`. -/
theorem zc_rounds {rd : Reader} {rounds chi cprod : E} {n : ℕ} : ∀ (L b : ℕ) (cv0 : Digest)
    (cur claim0 c0 : E), (∀ j < L, ZcAt rd rounds chi cprod n (b + j)) →
    LoadHolds rd rounds (4 * b) (digestScalars cv0).1 →
    LoadHolds rd rounds (4 * b + 1) (digestScalars cv0).2 →
    LoadHolds rd rounds (4 * b + 2) cur → LoadHolds rd rounds (4 * b + 3) claim0 →
    LoadHolds rd cprod b c0 →
    ∃ (ws rs : List E) (cl : E) (cvS : Digest), ws.length = 3 * L ∧ ReadsAt rd cur ws ∧
      rs.length = L ∧ RunsTo (sumcheck claim0 4 (List.replicate L none)) cv0 ws (rs, cl) cvS ∧
      (∀ j (hj : j < rs.length), LoadHolds rd chi (n - 1 - (b + j)) rs[j]) ∧
      (∀ j ≤ L, LoadHolds rd cprod (b + j) (c0 * prodE (rs.take j))) ∧
      LoadHolds rd rounds (4 * (b + L)) (digestScalars cvS).1 ∧
      LoadHolds rd rounds (4 * (b + L) + 1) (digestScalars cvS).2 ∧
      LoadHolds rd rounds (4 * (b + L) + 2) (cur * gen ^ (3 * L)) ∧
      LoadHolds rd rounds (4 * (b + L) + 3) cl := by
  intro L
  induction L with
  | zero =>
    intro b cv0 cur claim0 c0 _ h0 h1 h2 h3 hc
    refine ⟨[], [], claim0, cv0, rfl, readsAt_nil _ _, rfl, runsTo_ret _ _,
      fun j hj => absurd hj (by simp), fun j hj => ?_, h0, h1, ?_, h3⟩
    · obtain rfl : j = 0 := by omega
      simpa [prodE] using hc
    · rw [Nat.mul_zero, pow_zero, mul_one]; exact h2
  | succ L ih =>
    intro b cv0 cur claim0 c0 hR h0 h1 h2 h3 hc
    obtain ⟨cv, cur', claim', a0, a2, a3, claim'', rk, cv', c, i0, i1, i2, i3, hrd, hrun, hchi,
      o4, o5, o6, o7, hc0, hc1⟩ := hR 0 (by omega)
    simp only [Nat.add_zero] at i0 i1 i2 i3 hchi o4 o5 o6 o7 hc0 hc1
    have ecv : cv0 = cv := digestScalars_injective (Prod.ext (loadHolds_unique h0 i0)
      (loadHolds_unique h1 i1))
    have ecur : cur = cur' := loadHolds_unique h2 i2
    have ecl : claim0 = claim' := loadHolds_unique h3 i3
    have ec : c0 = c := loadHolds_unique hc hc0
    subst ecv ecur ecl ec
    obtain ⟨ws', rs', cl, cvS, hwl', hws', hrl', hrun', hchi', hcp', t0, t1, t2, t3⟩ :=
      ih (b + 1) cv' (cur * gen ^ 3) claim'' (c0 * rk)
        (fun j hj => by rw [show b + 1 + j = b + (j + 1) by ring]; exact hR (j + 1) (by omega))
        (by rw [show 4 * (b + 1) = 4 * b + 4 by ring]; exact o4)
        (by rw [show 4 * (b + 1) + 1 = 4 * b + 5 by ring]; exact o5)
        (by rw [show 4 * (b + 1) + 2 = 4 * b + 6 by ring]; exact o6)
        (by rw [show 4 * (b + 1) + 3 = 4 * b + 7 by ring]; exact o7) hc1
    refine ⟨[a0, a2, a3] ++ ws', rk :: rs', cl, cvS, by simp [hwl']; ring,
      readsAt_append_pow hrd (by simp only [List.length_cons, List.length_nil]; exact hws'),
      by simp [hrl'], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact RunsTo.sumcheck_cons hrun hrun'
    · intro j hj
      cases j with
      | zero => simpa using hchi
      | succ j =>
        have := hchi' j (by simp at hj; omega)
        rw [show b + 1 + j = b + (j + 1) by ring] at this
        simpa using this
    · intro j hj
      cases j with
      | zero => simpa [prodE] using hc0
      | succ j =>
        have := hcp' j (by omega)
        rw [show b + 1 + j = b + (j + 1) by ring] at this
        rw [List.take_succ_cons, vt_prodE_eq, List.prod_cons, ← mul_assoc, ← vt_prodE_eq]
        exact this
    · rw [show b + (L + 1) = b + 1 + L by ring]; exact t0
    · rw [show b + (L + 1) = b + 1 + L by ring]; exact t1
    · rw [show b + (L + 1) = b + 1 + L by ring, mul_assoc, ← pow_add,
        show 3 + 3 * L = 3 * (L + 1) by ring] at *
      exact t2
    · rw [show b + (L + 1) = b + 1 + L by ring]; exact t3

/-! ## The phase -/

/-- Table `t ≥ 1`'s term of the round count's checks, from value `4562 + 8·(t - 1)`. -/
def vtZcTau (t : ℕ) : List Stmt :=
  let v := 4562 + 8 * (t - 1)
  [.atom (.load (.n v) (.n 7) (t + 1)), .atom (.const (.n (v + 1)) (word 4294967296 0 0)),
    .atom (.mul (.n 4554) (.n (v + 2)) (.n v)),
    .atom (.rangeCheck (.n (v + 2)) (.n (v + 3)) (.n (v + 4)) (.n (v + 5)) (.n (v + 1))),
    .atom (.add (.n (v + 6)) (.n 4554) (.n v)),
    .atom (.mul (.n (v + 7)) (.n (if t = 1 then 4561 else v - 1)) (.n (v + 6)))]

theorem vt_zc_taus : ∀ t < 5, stmtsEqb (vtZcTau (t + 1)) ((vtPre.drop (4279 + 6 * t)).take 6) = true := by
  decide +kernel

theorem word_g32' : word 4294967296 0 0 = ofK (Parameters.gpow 32) := by
  have h : word 4294967296 0 0 = gen ^ 32 := word_two_pow (a := 32) (by decide)
  rw [h, gen_pow_eq_ofK]

theorem foldl_max_eq {l : List ℕ} {n : ℕ} (hle : ∀ x ∈ l, x ≤ n) (hmem : n ∈ l) :
    l.foldl max 0 = n := by
  have key : ∀ (l : List ℕ) (a : ℕ), a ≤ n → (∀ x ∈ l, x ≤ n) → (n = a ∨ n ∈ l) →
      l.foldl max a = n := by
    intro l
    induction l with
    | nil => intro a ha _ h; simp at h ⊢; omega
    | cons x l ih =>
      intro a ha hl h
      simp only [List.foldl_cons]
      apply ih (max a x) (by have := hl x (by simp); omega) (fun y hy => hl y (by simp [hy]))
      rcases h with h | h
      · left; have := hl x (by simp); omega
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · left; omega
        · right; exact h
  exact key l 0 (Nat.zero_le _) hle (Or.inr hmem)

set_option maxHeartbeats 4000000 in
/-- **The table sumcheck** (G:1706-1745): with `dims_g[t + 1] = g^(τ t)`, `τ t < 29`, the bus point
at `zeta` with `g_bus_mu = g^|point|`, and the chain at `(3422, 3423)` the state of `cvB`: the
round count is `n = max τ ≤ |point|`; `ξ` is squeezed from `cvB`; the words at the cursor (five
words on) run the `n` plain rounds from the bus target to the challenges `rs` and the claim `cl`;
`chi` holds `rs` reversed; `cprod[j]` and `peq[k]` are the prefix products; and the chain, the
cursor and the claim the phase leaves are the rounds'. -/
theorem vt_zc {κ : ℕ} (hκ : κ ≤ 32) (Lm : MemImage κ) {σ : Val} (h : VtHolds Lm.read σ)
    (τ : ℕ → ℕ) (hτ : ∀ t < 6, τ t < 29)
    (hdims : ∀ t < 6, LoadHolds Lm.read (σ (.n 7)) (t + 1) (gen ^ τ t))
    {point : List E} (hz : ReadsAt Lm.read (σ (.n 5)) point) (hmu : σ (.n 6) = gen ^ point.length)
    (hml : point.length < 33) {cvB : Digest} (hst : (σ (.n 3422), σ (.n 3423)) = digestScalars cvB) :
    ∃ (n : ℕ) (ws rs : List E) (cl : E) (cvS : Digest),
      n = ((List.range 6).map τ).foldl max 0 ∧ n ≤ point.length ∧ σ (.n 4554) = gen ^ n ∧
      σ (.n 4621) = challengeOf (sqCv cvB) ∧ σ (.n 4622) = 1 ∧
      σ (.n 4623) = challengeOf (sqCv cvB) ∧ σ (.n 4624) = challengeOf (sqCv cvB) ^ 2 ∧
      σ (.n 4625) = challengeOf (sqCv cvB) ^ 3 ∧ σ (.n 4626) = challengeOf (sqCv cvB) ^ 4 ∧
      ws.length = 3 * n ∧ ReadsAt Lm.read (σ (.n 2) * gen ^ 5) ws ∧ rs.length = n ∧
      RunsTo (sumcheck (σ (.n 4631)) 4 (List.replicate n none)) (sqCv cvB) ws (rs, cl) cvS ∧
      ReadsAt Lm.read (σ (.n 15)) rs.reverse ∧
      (∀ j ≤ n, LoadHolds Lm.read (σ (.n 4639)) j (prodE (rs.take j))) ∧
      (∀ k ≤ n, LoadHolds Lm.read (σ (.n 4655)) k (eqEval (point.take k) (rs.reverse.take k))) ∧
      (σ (.n 4649), σ (.n 4650)) = digestScalars cvS ∧
      σ (.n 4651) = σ (.n 2) * gen ^ 5 * gen ^ (3 * n) ∧ σ (.n 4652) = cl := by
  -- the round count
  have a4554 := h.atom 4276 (.mul (.n 4554) (.n 4557) (.n 4555)) (by decide +kernel)
  have l4555 := h.atom 4274 (.load (.n 4555) (.n 7) 1) (by decide +kernel)
  have c4556 := h.atom 4275 (.const (.n 4556) (word 4294967296 0 0)) (by decide +kernel)
  have rc0 := h.atom 4277 (.rangeCheck (.n 4557) (.n 4558) (.n 4559) (.n 4560) (.n 4556))
    (by decide +kernel)
  have a4561 := h.atom 4278 (.add (.n 4561) (.n 4554) (.n 4555)) (by decide +kernel)
  simp only [Atom.Holds] at a4554 l4555 c4556 rc0 a4561
  have e4555 : σ (.n 4555) = gen ^ τ 0 := loadHolds_unique l4555 (hdims 0 (by omega))
  obtain ⟨e0, he0, he0'⟩ := rc_sound' hκ Lm (K := 33) (by omega) (by decide)
    (by rw [c4556]; exact word_g32') rc0.1 rc0.2.1 rc0.2.2
  set n := e0 + τ 0 with hn
  have hgn : σ (.n 4554) = gen ^ n := by rw [a4554, he0', e4555, ← pow_add]
  have hτ0 := hτ 0 (by omega)
  -- each height is at most `n`
  have htau : ∀ t, t < 5 → ∃ e < 33, n = e + τ (t + 1) ∧
      σ (.n (4562 + 8 * t + 6)) = gen ^ n + gen ^ τ (t + 1) ∧
      σ (.n (4562 + 8 * t + 7)) =
        σ (.n (if t + 1 = 1 then 4561 else 4562 + 8 * t - 1)) * σ (.n (4562 + 8 * t + 6)) := by
    intro t ht
    obtain ⟨k, hb⟩ := h.slice _ _ (vt_zc_taus t ht)
    simp only [vtZcTau, Nat.add_sub_cancel, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hb
    obtain ⟨l0, c1, m2, rc, a6, a7⟩ := hb
    have ev := loadHolds_unique l0 (hdims (t + 1) (by omega))
    obtain ⟨e, he, he'⟩ := rc_sound' hκ Lm (K := 33) (by omega) (by decide)
      (by rw [c1]; exact word_g32') rc.1 rc.2.1 rc.2.2
    rw [hgn, he', ev, ← pow_add] at m2
    refine ⟨e, he, gen_pow_inj' (by omega) (by have := hτ (t + 1) (by omega); omega) m2, ?_, a7⟩
    rw [a6, hgn, ev]
  obtain ⟨f1, hf1, hn1, s1, p1⟩ := htau 0 (by omega)
  obtain ⟨f2, hf2, hn2, s2, p2⟩ := htau 1 (by omega)
  obtain ⟨f3, hf3, hn3, s3, p3⟩ := htau 2 (by omega)
  obtain ⟨f4, hf4, hn4, s4, p4⟩ := htau 3 (by omega)
  obtain ⟨f5, hf5, hn5, s5, p5⟩ := htau 4 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, ↓reduceIte,
    OfNat.ofNat_ne_one] at s1 s2 s3 s4 s5 p1 p2 p3 p4 p5
  simp only [Nat.reduceAdd] at hn1 hn2 hn3 hn4 hn5
  have c4602 := h.atom 4309 (.const (.n 4602) (word 0 0 0)) (by decide +kernel)
  have ae := h.atom 4310 (.assertEq (.n 4601) (.n 4602)) (by decide +kernel)
  simp only [Atom.Holds, word_zero] at c4602 ae
  rw [c4602, add_zero] at ae
  have hmax : ∃ t < 6, τ t = n := by
    rw [p5, p4, p3, p2, p1, a4561, s1, s2, s3, s4, s5, hgn, e4555] at ae
    simp only [mul_eq_zero, e_add_eq_zero_iff] at ae
    have hinj : ∀ t < 6, gen ^ n = gen ^ τ t → τ t = n := fun t ht he =>
      (gen_pow_inj' (by omega) (by have := hτ t ht; omega) he).symm
    rcases ae with ((((h0 | h1) | h2) | h3) | h4) | h5
    · exact ⟨0, by omega, hinj 0 (by omega) h0⟩
    · exact ⟨1, by omega, hinj 1 (by omega) h1⟩
    · exact ⟨2, by omega, hinj 2 (by omega) h2⟩
    · exact ⟨3, by omega, hinj 3 (by omega) h3⟩
    · exact ⟨4, by omega, hinj 4 (by omega) h4⟩
    · exact ⟨5, by omega, hinj 5 (by omega) h5⟩
  have hnmax : n = ((List.range 6).map τ).foldl max 0 := by
    obtain ⟨t0, ht0, hτt0⟩ := hmax
    refine (foldl_max_eq (fun x hx => ?_) ?_).symm
    · simp only [List.mem_map, List.mem_range] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      interval_cases t <;> omega
    · exact List.mem_map.mpr ⟨t0, List.mem_range.mpr ht0, hτt0⟩
  -- the bus point's length bounds it
  have c4603 := h.atom 4311 (.const (.n 4603) (word 4294967296 0 0)) (by decide +kernel)
  have m6 := h.atom 4312 (.mul (.n 6) (.n 4604) (.n 4554)) (by decide +kernel)
  have rcm := h.atom 4313 (.rangeCheck (.n 4604) (.n 4605) (.n 4606) (.n 4607) (.n 4603))
    (by decide +kernel)
  simp only [Atom.Holds] at c4603 m6 rcm
  obtain ⟨em, hem, hem'⟩ := rc_sound' hκ Lm (K := 33) (by omega) (by decide)
    (by rw [c4603]; exact word_g32') rcm.1 rcm.2.1 rcm.2.2
  rw [hmu, hem', hgn, ← pow_add] at m6
  have hnmu : n ≤ point.length := by
    have := gen_pow_inj' (by omega) (by omega) m6; omega
  -- `ξ` and its powers
  obtain ⟨cv0, hcv0, hsq, hxi⟩ := h.squeeze 4314 (.n 3422) (.n 3423) 4608 (by decide +kernel)
  rw [hst] at hcv0
  obtain rfl := (digestScalars_injective hcv0).symm
  have c4622 := h.atom 4328 (.const (.n 4622) (word 1 0 0)) (by decide +kernel)
  have m4623 := h.atom 4329 (.mul (.n 4623) (.n 4622) (.n 4621)) (by decide +kernel)
  have m4624 := h.atom 4330 (.mul (.n 4624) (.n 4623) (.n 4621)) (by decide +kernel)
  have m4625 := h.atom 4331 (.mul (.n 4625) (.n 4624) (.n 4621)) (by decide +kernel)
  have m4626 := h.atom 4332 (.mul (.n 4626) (.n 4625) (.n 4621)) (by decide +kernel)
  simp only [Atom.Holds, word_one] at c4622 m4623 m4624 m4625 m4626
  rw [c4622, one_mul, hxi] at m4623
  rw [m4623, hxi, ← pow_two] at m4624
  rw [m4624, hxi, ← pow_succ] at m4625
  rw [m4625, hxi, ← pow_succ] at m4626
  -- the rounds' first slot and `cprod[0]`
  have s0 := h.atom 4346 (.load (.n 4613) (.n 4636) 0) (by decide +kernel)
  have s1 := h.atom 4347 (.load (.n 4614) (.n 4636) 1) (by decide +kernel)
  have c4640 := h.atom 4348 (.const (.n 4640) (word 32 0 0)) (by decide +kernel)
  have m4641 := h.atom 4349 (.mul (.n 4641) (.n 2) (.n 4640)) (by decide +kernel)
  have s2 := h.atom 4350 (.load (.n 4641) (.n 4636) 2) (by decide +kernel)
  have s3 := h.atom 4351 (.load (.n 4631) (.n 4636) 3) (by decide +kernel)
  have c4642 := h.atom 4352 (.const (.n 4642) (word 1 0 0)) (by decide +kernel)
  have sc := h.atom 4353 (.load (.n 4642) (.n 4639) 0) (by decide +kernel)
  have c4643 := h.atom 4354 (.const (.n 4643) (word 1 0 0)) (by decide +kernel)
  have a4644 := h.atom 4355 (.add (.n 4644) (.n 4643) (.n 4554)) (by decide +kernel)
  have c4645 := h.atom 4356 (.const (.n 4645) (word 1 0 0)) (by decide +kernel)
  have c79 := h.callIf 4357 (.n 4644) "__loop79" [.n 4645, .n 4554, .n 4636, .n 15, .n 4554, .n 4639]
    (by decide +kernel)
  simp only [Atom.Holds] at s0 s1 c4640 m4641 s2 s3 sc a4644
  simp only [Atom.Holds, word_one, List.map_cons, List.map_nil] at c4642 c4643 c4645 c79
  rw [m4641, c4640, show (32 : ℕ) = 2 ^ 5 by norm_num, word_two_pow (by decide)] at s2
  rw [c4642] at sc
  have e4613 : σ (.n 4613) = (digestScalars (sqCv cv0)).1 := congrArg Prod.fst hsq
  have e4614 : σ (.n 4614) = (digestScalars (sqCv cv0)).2 := congrArg Prod.snd hsq
  rw [e4613] at s0
  rw [e4614] at s1
  have hR : ∀ j < n, ZcRound Lm.read (σ (.n 4636)) (σ (.n 15)) (σ (.n 4554)) (σ (.n 4639)) (gen ^ j) :=
    Main.loop_sound (ps := [σ (.n 4554), σ (.n 4636), σ (.n 15), σ (.n 4554), σ (.n 4639)])
      (N := σ (.n 4554)) (by unfold ordG; omega) hgn (fun x hx => loop79_step hx) (fun hne => by
        have := c79 (by rw [a4644, c4643]; exact hne)
        rw [c4645] at this
        exact this)
  rw [hgn] at hR
  obtain ⟨ws, rs, cl, cvS, hwl, hws, hrl, hrun, hchi, hcp, t0, t1, t2, t3⟩ :=
    zc_rounds (rounds := σ (.n 4636)) (chi := σ (.n 15)) (cprod := σ (.n 4639)) n 0 (sqCv cv0)
      (σ (.n 2) * gen ^ 5) (σ (.n 4631)) 1
      (fun j hj => by rw [Nat.zero_add]; exact zcAt_of_round hj (hR j hj)) s0 s1 s2 s3 sc
  simp only [Nat.zero_add, one_mul] at hchi hcp t0 t1 t2 t3
  -- the last slot
  have m4646 := h.atom 4358 (.mul (.n 4646) (.n 4554) (.n 4554)) (by decide +kernel)
  have m4647 := h.atom 4359 (.mul (.n 4647) (.n 4646) (.n 4646)) (by decide +kernel)
  have m4648 := h.atom 4360 (.mul (.n 4648) (.n 4636) (.n 4647)) (by decide +kernel)
  have l4649 := h.atom 4361 (.load (.n 4649) (.n 4648) 0) (by decide +kernel)
  have l4650 := h.atom 4362 (.load (.n 4650) (.n 4648) 1) (by decide +kernel)
  have l4651 := h.atom 4363 (.load (.n 4651) (.n 4648) 2) (by decide +kernel)
  have l4652 := h.atom 4364 (.load (.n 4652) (.n 4648) 3) (by decide +kernel)
  simp only [Atom.Holds] at m4646 m4647 m4648 l4649 l4650 l4651 l4652
  have e4648 : σ (.n 4648) = σ (.n 4636) * gen ^ (4 * n) := by
    rw [m4648, m4647, m4646, hgn]; ring
  rw [e4648, loadHolds_gen_pow_mul] at l4649 l4650 l4651 l4652
  -- `zc_peq`
  have c4656 := h.atom 4368 (.const (.n 4656) (word 1 0 0)) (by decide +kernel)
  have sp := h.atom 4369 (.load (.n 4656) (.n 4655) 0) (by decide +kernel)
  have c4657 := h.atom 4370 (.const (.n 4657) (word 1 0 0)) (by decide +kernel)
  have a4658 := h.atom 4371 (.add (.n 4658) (.n 4657) (.n 4554)) (by decide +kernel)
  have c4659 := h.atom 4372 (.const (.n 4659) (word 1 0 0)) (by decide +kernel)
  have c80 := h.callIf 4373 (.n 4658) "__loop80" [.n 4659, .n 4554, .n 4655, .n 5, .n 15]
    (by decide +kernel)
  simp only [Atom.Holds, word_one, List.map_cons, List.map_nil] at c4656 sp c4657 a4658 c4659 c80
  rw [c4656] at sp
  have hrev : ReadsAt Lm.read (σ (.n 15)) rs.reverse := by
    intro k hk
    have hk' : k < n := by simp [hrl] at hk; omega
    have := hchi (n - 1 - k) (by omega)
    rw [show n - 1 - (n - 1 - k) = k by omega] at this
    rw [List.getElem_reverse]
    convert this using 2
    congr 1
    simp [hrl]
  have hpeq := loop80_sound (rd := Lm.read) (peq := σ (.n 4655)) (zeta := σ (.n 5)) (chi := σ (.n 15))
    (n := n) (by unfold ordG; omega) hz hrev hnmu (by simp [hrl]) sp (fun hne => by
      have := c80 (by rw [a4658, c4657, hgn]; exact hne)
      rw [c4659, hgn] at this
      exact this)
  refine ⟨n, ws, rs, cl, cvS, hnmax, hnmu, hgn, hxi, c4622, m4623, m4624, m4625, m4626, hwl, hws,
    hrl, hrun, hrev, hcp, hpeq, ?_, ?_, ?_⟩
  · rw [loadHolds_unique l4649 (by simpa using t0), loadHolds_unique l4650 t1]
  · exact loadHolds_unique l4651 t2
  · exact loadHolds_unique l4652 t3

end
end LeanVM.Guest.B1.VerifySub
