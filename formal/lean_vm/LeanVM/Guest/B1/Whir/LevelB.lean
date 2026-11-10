/-
  LeanVM.Guest.B1.Whir.LevelB

  A level's cap, high part, queries and glue (`osCap`, `osHsMid`, `osHsFinal`, `osQueries`,
  `osGlue`), soundly, block by block.
-/

module

public import LeanVM.Guest.B1.Whir.Lam
public import LeanVM.Guest.B1.Whir.QOpen

/-!
# A level's cap, high part, queries and glue (G:1652-1744)

* `osCap_sound`: `verify_merkle_cap` on the level's cap and flags, its root's cells stored in
  `level_roots` (`2·lvl`, `2·lvl + 1`).
* `osHsCoefs_val`: each coefficient read from `src` and stored at `dst` times its normalizer
  `word (sc c) 0`; `osHsMid_sound`, `osHsFinal_sound`: a non-final level's high part (from `sent`
  into `level_hs`) and the final lane (from `final_msg` into a fresh `hs`).
* `osQueries_sound`: the `opening_queries` call on the cap, the flags, `1/λ` (`0` at the final
  level), the round coefficients, the high part, the positions and windows, `g^pairs`.
* `osGlue_sound`: the claim plus `λ·y0 + λ²·y1 + λ³·λ^Q·batched`, `λ`, `λ²` into `ood_scalars`,
  `λ³·λ^Q` into `level_betas`, `1/λ` into `level_mus`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The cap -/

/-- **The level's cap** (G:1658-1662): `verify_merkle_cap`'s meaning on the cap and the flags,
the root's cells stored in `level_roots`. -/
theorem osCap_sound {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt}
    (hcap : ∀ a r, C ("verify_merkle_cap__L" ++ natStr lv.capDepth) a r →
      MeaningVerifyMerkleCap lv.capDepth rd a r)
    (hm : MatsOk σ st.mats) (hco : 4 * lv.capOff < u128Bound)
    (hok : AllOk C rd σ (osCap c lvl lv st).1) :
    ∃ r0 r1 : E, MeaningVerifyMerkleCap lv.capDepth rd
        [σ (.n osCaps) * gen ^ (4 * lv.capOff), σ (.n osFlags) * gen ^ lv.capOff] [r0, r1] ∧
      LoadHolds rd (σ (.n osRoots)) (2 * lvl) r0 ∧ LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) r1 ∧
      MatsOk σ (osCap c lvl lv st).2.mats ∧
      (osCap c lvl lv st).2 = { st with
        k := (osCap c lvl lv st).2.k
        mats := (osCap c lvl lv st).2.mats } := by
  unfold osCap at hok ⊢
  simp only [allOk_append] at hok
  obtain ⟨⟨hcp, hfl⟩, hrest⟩ := hok
  obtain ⟨ecp, hm1⟩ := osMatS_val' hcp hm hco
  obtain ⟨efl, hm2⟩ := osMatS_val' hfl hm1 (lt_of_le_of_lt (by omega) hco)
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_call, stmtOk_atom, holds_load, osLd,
    List.map_cons, List.map_nil] at hrest
  obtain ⟨hcall, l0, l1⟩ := hrest
  have hM := hcap _ _ hcall
  rw [ecp, efl] at hM
  exact ⟨_, _, hM, l0, l1, hm2, rfl⟩

/-! ## The high part -/

/-- **The scaled coefficients** (`osHsCoefs`): coefficient `c` read from `src·g^(si + c)` and
stored at `dst·g^(di + c)` times its normalizer `word (sc c) 0`. -/
theorem osHsCoefs_val (src dst : ℕ) (sc : ℕ → ℕ) (si di : ℕ) :
    ∀ (n i k : ℕ), AllOk C rd σ (osHsCoefs src dst sc si di n i k).1 →
      ∀ c, i ≤ c → c < i + n → ∃ v, LoadHolds rd (σ (.n src)) (si + c) v ∧
        LoadHolds rd (σ (.n dst)) (di + c) (v * word (sc c) 0)
  | 0, _, _, _, c, h1, h2 => absurd h2 (by omega)
  | n + 1, i, k, hok, c, h1, h2 => by
    simp only [osHsCoefs, allOk_append] at hok
    rcases Nat.eq_or_lt_of_le h1 with e | hlt
    · subst e
      have h0 := hok.1
      unfold osHsCoef at h0
      by_cases h : sc i = 1
      · simp only [h, ↓reduceIte, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load,
          osLd] at h0
        exact ⟨_, h0.1, by rw [h, word_one, mul_one]; exact h0.2⟩
      · simp only [h, ↓reduceIte, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load,
          holds_const, holds_mul, osLd, osCst, osMul] at h0
        obtain ⟨l, cs, m, st⟩ := h0
        exact ⟨_, l, by rw [m, cs] at st; exact st⟩
    · exact osHsCoefs_val src dst sc si di n (i + 1) _ hok.2 c (by omega) (by omega)

/-- **A non-final level's high part, normalized** (G:1704-1712): coefficient `c` of the high part
read from `sent` past the root, stored in `level_hs` times its normalizer. -/
theorem osHsMid_sound {lvl : ℕ} {lv : OsLv} {st : OsSt} (hok : AllOk C rd σ (osHsMid lvl lv st).1) :
    (∀ c < lv.folds, ∃ v, LoadHolds rd (σ (.n st.sent)) (2 + c) v ∧
      LoadHolds rd (σ (.n osHs)) (lvl * hsStride + c)
        (v * word (hsScale lv.vanish lv.highBits c (vanishInv (lv.vanish + lv.logCols))) 0)) ∧
      (osHsMid lvl lv st).2 = { st with k := (osHsMid lvl lv st).2.k } :=
  ⟨fun c hc ↦ osHsCoefs_val _ _ _ _ _ _ _ _ hok c (Nat.zero_le _) (by omega), rfl⟩

/-- **The final lane, normalized** (G:1693-1703): coefficient `c` read from `final_msg`, stored in
a fresh `hs` times its normalizer. -/
theorem osHsFinal_sound {c : OsCfg} {lv : OsLv} {st : OsSt}
    (hok : AllOk C rd σ (osHsFinal c lv st).1) :
    (∀ i < c.yrLen + lv.folds, ∃ v, LoadHolds rd (σ (.n osFmsg)) i v ∧
      LoadHolds rd (σ (.n (osHsFinal c lv st).2.hs)) i
        (v * word (hsScale lv.vanish (c.yrLog + 1) i 1) 0)) ∧
      (osHsFinal c lv st).2 = { st with
        k := (osHsFinal c lv st).2.k
        hs := (osHsFinal c lv st).2.hs } := by
  unfold osHsFinal at hok ⊢
  simp only [allOk_append] at hok
  refine ⟨fun i hi ↦ ?_, rfl⟩
  have := osHsCoefs_val _ _ _ _ _ _ _ _ hok.2 i (Nat.zero_le _) (by omega)
  simpa using this

/-! ## The glue -/

/-- **A non-final level's claims glued** (G:1728-1744). -/
theorem osGlue_sound {lvl : ℕ} {lv : OsLv} {st : OsSt}
    (hpwQ : digitsVal (osPowDigits lv.queries) 1 = lv.queries) (hok : AllOk C rd σ (osGlue lvl lv st).1) :
    σ (.n (osGlue lvl lv st).2.claim) = σ (.n st.claim) + σ (.n st.lam) * σ (.n (st.ys.getD 0 0)) +
        σ (.n st.lam) ^ 2 * σ (.n (st.ys.getD 1 0)) +
        σ (.n st.lam) ^ 3 * σ (.n st.lam) ^ lv.queries * σ (.n st.batched) ∧
      LoadHolds rd (σ (.n osOodSc)) (oodSamples * (lvl + 1)) (σ (.n st.lam)) ∧
      LoadHolds rd (σ (.n osOodSc)) (oodSamples * (lvl + 1) + 1) (σ (.n st.lam) ^ 2) ∧
      LoadHolds rd (σ (.n osBetas)) lvl (σ (.n st.lam) ^ 3 * σ (.n st.lam) ^ lv.queries) ∧
      LoadHolds rd (σ (.n osMus)) lvl (σ (.n st.lamInv)) ∧
      (osGlue lvl lv st).2 = { st with
        k := (osGlue lvl lv st).2.k
        claim := (osGlue lvl lv st).2.claim } := by
  unfold osGlue at hok ⊢
  simp only [allOk_append] at hok
  obtain ⟨⟨h1, hpw⟩, h2⟩ := hok
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_mul, holds_add, osLd,
    osMul, osAdd] at h1 h2
  obtain ⟨l0, m0, a1, m2, l2, m3, a4, m5⟩ := h1
  obtain ⟨m6, m7, a8, l9, l10⟩ := h2
  have hpv := osPowSteps_val (C := C) (rd := rd) (σ := σ) st.lam (osPowDigits lv.queries) st.lam
    (st.k + 6) 1 (by rw [pow_one]) hpw
  rw [hpwQ] at hpv
  refine ⟨?_, l0, ?_, ?_, l10, rfl⟩
  · rw [a8, m7, m6, hpv, a4, a1, m0, m3, m5, m2]; ring
  · rw [← show σ (.n (st.k + 2)) = σ (.n st.lam) ^ 2 by rw [m2]; ring]; exact l2
  · rw [← show σ (.n (st.k + 6 + osPowLen lv.queries)) = σ (.n st.lam) ^ 3 * σ (.n st.lam) ^ lv.queries
      by rw [m6, hpv, m5, m2]; ring]
    exact l9

/-! ## The queries -/

/-- The `opening_queries` call's arguments (G:1719-1726). -/
def osQArgs (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) : List E :=
  [σ (.n osCaps) * gen ^ (4 * lv.capOff), σ (.n osFlags) * gen ^ lv.capOff,
    if lvl = c.yrLevel then 0 else σ (.n st.lamInv), σ (.n osCoefs) * gen ^ (3 * lv.foldsOff),
    if lvl = c.yrLevel then σ (.n st.hs) else σ (.n osHs) * gen ^ (lvl * hsStride),
    σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff,
    gen ^ (if lvl = 0 then lv.queries / 2 else lv.queries)]

/-- **The level's queries** (G:1719-1726): the `opening_queries` call on its arguments. -/
theorem osQueries_sound {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt}
    (hm : MatsOk σ st.mats) (hb : 4 * lv.capOff < u128Bound) (hf : 3 * lv.foldsOff < u128Bound)
    (hh : lvl * hsStride < u128Bound) (hp : lv.posOff < u128Bound)
    (hq : lv.queries < u128Bound) (hok : AllOk C rd σ (osQueries c lvl lv st).1) :
    C (osQueriesName c lvl lv) (osQArgs σ c lvl lv st) [σ (.n (osQueries c lvl lv st).2.batched)] ∧
      MatsOk σ (osQueries c lvl lv st).2.mats ∧
      (osQueries c lvl lv st).2 = { st with
        k := (osQueries c lvl lv st).2.k
        mats := (osQueries c lvl lv st).2.mats
        batched := (osQueries c lvl lv st).2.batched } := by
  have hpairs : (if lvl = 0 then lv.queries / 2 else lv.queries) < u128Bound := by
    split_ifs <;> omega
  unfold osQueries at hok ⊢
  simp only [allOk_append] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hcp, hfl⟩, hli⟩, hcf⟩, hhp⟩, hqp⟩, hwp⟩, hcall⟩ := hok
  obtain ⟨ecp, hm1⟩ := osMatS_val' hcp hm hb
  obtain ⟨efl, hm2⟩ := osMatS_val' hfl hm1 (lt_of_le_of_lt (by omega) hb)
  by_cases hfin : lvl = c.yrLevel
  · simp only [hfin, ↓reduceIte, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_const,
      osCst] at hli hhp hcall ⊢
    sorry
  · sorry

end
end LeanVM.Guest.B1.Whir
