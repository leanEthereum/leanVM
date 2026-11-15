/-
  LeanVM.Guest.B1.Whir.LevelB

  A level's high part, queries and glue (`osHsMid`, `osHsFinal`, `osQueries`, `osGlue`), soundly,
  block by block.
-/

module

public import LeanVM.Guest.B1.Whir.Lam
public import LeanVM.Guest.B1.Whir.QOpen
public import LeanVM.Guest.B1.Whir.RateCfg

/-!
# A level's high part, queries and glue

* `osHsCoefs_val`: each coefficient read from `src` and stored at `dst` times its normalizer
  `word (sc c) 0`; `osHsMid_sound`, `osHsFinal_sound`: a non-final level's high part (from `sent`
  into `level_hs`) and the final lane (from `final_msg` into a fresh `hs`).
* `osQueries_sound`: the dispatch on the rate into `level_queries` on `λ`, `1/λ` (both `0` at the
  final level), the round coefficients, the high part, the positions and windows; its returned
  root's cells those in `level_roots`.
* `osGlue_sound`: the claim plus `λ·y0 + λ²·λ^n·batched`, `λ` into `ood_scalars`, `λ²·λ^n`
  into `level_scales`, `1/λ` into `level_lam_invs`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

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

/-- **A non-final level's high part, normalized**: coefficient `c` of the high part
read from `sent` past the root, stored in `level_hs` times its normalizer. -/
theorem osHsMid_sound {lvl : ℕ} {lv : OsLv} {st : OsSt} (hok : AllOk C rd σ (osHsMid lvl lv st).1) :
    (∀ c < lv.folds, ∃ v, LoadHolds rd (σ (.n st.sent)) (2 + c) v ∧
      LoadHolds rd (σ (.n osHs)) (lvl * hsStride + c)
        (v * word (hsScale lv.vanish lv.highBits c (vanishInv (lv.vanish + lv.logCols))) 0)) ∧
      (osHsMid lvl lv st).2 = { st with k := (osHsMid lvl lv st).2.k } :=
  ⟨fun c hc ↦ osHsCoefs_val _ _ _ _ _ _ _ _ hok c (Nat.zero_le _) (by omega), rfl⟩

/-- **The final lane, normalized**: coefficient `c` read from `final_msg`, stored in
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

/-- **A non-final level's claims glued.** -/
theorem osGlue_sound {lvl : ℕ} {st : OsSt} (hok : AllOk C rd σ (osGlue lvl st).1) :
    σ (.n (osGlue lvl st).2.claim) = σ (.n st.claim) + σ (.n st.lam) * σ (.n (st.ys.getD 0 0)) +
        σ (.n st.lam) ^ 2 * σ (.n st.lamPow) * σ (.n st.batched) ∧
      LoadHolds rd (σ (.n osOodSc)) (lvl + 1) (σ (.n st.lam)) ∧
      LoadHolds rd (σ (.n osBetas)) lvl (σ (.n st.lam) ^ 2 * σ (.n st.lamPow)) ∧
      LoadHolds rd (σ (.n osMus)) lvl (σ (.n st.lamInv)) ∧
      (osGlue lvl st).2 = { st with
        k := (osGlue lvl st).2.k
        claim := (osGlue lvl st).2.claim } := by
  unfold osGlue at hok ⊢
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_mul, holds_add, osLd,
    osMul, osAdd] at hok
  obtain ⟨l0, m0, a1, m2, m3, m4, a5, l6, l7⟩ := hok
  refine ⟨?_, l0, ?_, l7, rfl⟩
  · rw [a5, a1, m0, m4, m3, m2]; ring
  · rw [m3, m2, ← sq] at l6; exact l6

/-! ## The queries -/

/-- The `level_queries` call's arguments. -/
def osQArgs (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) : List E :=
  [if lvl = c.yrLevel then 0 else σ (.n st.lam), if lvl = c.yrLevel then 0 else σ (.n st.lamInv),
    σ (.n osCoefs) * gen ^ (2 * lv.foldsOff),
    if lvl = c.yrLevel then σ (.n st.hs) else σ (.n osHs) * gen ^ (lvl * hsStride),
    σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff]

/-- **The level's queries**: the dispatch on the rate into `level_queries` on its arguments,
the root it returns that in `level_roots`. -/
theorem osQueries_sound {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (hr : LvRate σ c lvl lv)
    (hm : MatsOk σ st.mats) (hf : 2 * lv.foldsOff < u128Bound)
    (hh : lvl * hsStride < u128Bound) (hp : lv.posOff < u128Bound)
    (hok : AllOk C rd σ (osQueries c lvl lv st).1) :
    (osQCallOf c lvl lv st).1.map σ = osQArgs σ c lvl lv st ∧
      C (osQueriesName c lvl lv) (osQArgs σ c lvl lv st) ((osQCallOf c lvl lv st).2.map σ) ∧
      (∃ r0 r1 : E, (osQCallOf c lvl lv st).2.map σ =
          [r0, r1, σ (.n (osQueries c lvl lv st).2.batched), σ (.n (osQueries c lvl lv st).2.lamPow)] ∧
        LoadHolds rd (σ (.n osRoots)) (2 * lvl) r0 ∧ LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) r1) ∧
      MatsOk σ (osQueries c lvl lv st).2.mats ∧
      (osQueries c lvl lv st).2 = { st with
        k := (osQueries c lvl lv st).2.k
        mats := (osQueries c lvl lv st).2.mats
        batched := (osQueries c lvl lv st).2.batched
        lamPow := (osQueries c lvl lv st).2.lamPow } := by
  unfold osQueries at hok ⊢
  unfold osQCallOf
  simp only [allOk_append] at hok
  obtain ⟨⟨⟨⟨⟨hli, hcf⟩, hhp⟩, hqp⟩, hwp⟩, hrest⟩ := hok
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, osLd] at hrest
  obtain ⟨hd, l0, l1⟩ := hrest
  have hC := dispatch_rate hr (osQueriesName c lvl) hd
  by_cases hfin : lvl = c.yrLevel
  · subst hfin
    simp only [↓reduceIte] at hcf hhp hqp hwp hli hC l0 l1 ⊢
    simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_const, osCst] at hli
    obtain ⟨z0, z1⟩ := hli
    obtain ⟨ecf, hm3⟩ := osMatS_val' hcf hm hf
    obtain ⟨eqp, hm4⟩ := osMatS_val' hqp hm3 hp
    obtain ⟨ewp, hm5⟩ := osMatS_val' hwp hm4 hp
    refine (fun ha ↦ ⟨ha, ha ▸ hC, ⟨_, _, ?_, l0, l1⟩, hm5, rfl⟩) ?_
    · simp only [List.map_cons, List.map_nil, osQArgs, ↓reduceIte]
      rw [z0, z1, ecf, eqp, ewp, word_zero]
    · simp [osRun, List.range_succ]
  · simp only [hfin, ↓reduceIte] at hcf hhp hqp hwp hli hC l0 l1 ⊢
    obtain ⟨ecf, hm3⟩ := osMatS_val' hcf hm hf
    obtain ⟨ehp, hm4⟩ := osMatS_val' hhp hm3 hh
    obtain ⟨eqp, hm5⟩ := osMatS_val' hqp hm4 hp
    obtain ⟨ewp, hm6⟩ := osMatS_val' hwp hm5 hp
    refine (fun ha ↦ ⟨ha, ha ▸ hC, ⟨_, _, ?_, l0, l1⟩, hm6, rfl⟩) ?_
    · simp only [List.map_cons, List.map_nil, osQArgs, hfin, ↓reduceIte]
      rw [ecf, ehp, eqp, ewp]
    · simp [osRun, List.range_succ]

end
end LeanVM.Guest.B1.Whir
