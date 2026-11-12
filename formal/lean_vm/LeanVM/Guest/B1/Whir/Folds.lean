/-
  LeanVM.Guest.B1.Whir.Folds

  The template's fold rounds (`opening_round` calls) run the Spec's `foldRounds`.
-/

module

public import LeanVM.Guest.B1.Whir.Round
public import LeanVM.Guest.B1.Whir.Loops

/-!
# The fold rounds (TRIAGE G #35, #42; G:1538-1541)

The guest's running values, read through a valuation `σ` (`OsSt.F`, `OsSt.cur`): the sponge it
carries (its five capacity cells, nothing waiting), the cursor `cb·g^co`. `osRound_sound`: one
`opening_round` call (its meaning, `MeaningOpeningRound`) runs `foldRound` (`opening_round_run`);
`osRounds_sound`: `n` of them run `foldRounds n` from a Spec state whose claim is the guest's plus
a deficit `D`, which the rounds scale by their `α`s (the claim enters a round linearly with the
factor `α`, `roundClaim_add`), reading the words at the cursor, `α` stored in `fold_challenges`
and `α, β` in `round_coefs`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The running values through a valuation -/

/-- The sponge the guest carries: its five capacity cells, nothing waiting. -/
def OsSt.F (σ : Val) (st : OsSt) : Fs := ⟨st.fs.map fun i ↦ σ (.n i), []⟩

/-- The cursor: its base value times `g^co`. -/
def OsSt.cur (σ : Val) (st : OsSt) : E := σ (.n st.cb) * gen ^ st.co

/-- Words read from `p`, then from past them. -/
theorem readsAt_append {p : E} {xs ys : List E} (h1 : ReadsAt rd p xs)
    (h2 : ReadsAt rd (p * gen ^ xs.length) ys) : ReadsAt rd p (xs ++ ys) := by
  intro k hk
  by_cases h : k < xs.length
  · rw [List.getElem_append_left h]; exact h1 k h
  · rw [List.getElem_append_right (by omega)]
    have := h2 (k - xs.length) (by simp at hk; omega)
    rwa [loadHolds_mul_gen_pow, Nat.add_sub_cancel' (by omega)] at this

/-! ## Materialized pointers in the running state -/

theorem osMatS_val {P : List (ℕ × ℕ × ℕ)} {base off : ℕ} {s : OsSt} (hm : MatsOk σ s.mats)
    (h : off < u128Bound) (hok : AllOk C rd σ (osMatS P base off s).1) :
    σ (.n (osMatS P base off s).2.1) = σ (.n base) * gen ^ off ∧
      MatsOk σ (osMatS P base off s).2.2.mats :=
  ⟨osMatP_val hm h hok, osMatsAfter_ok hm h hok⟩

theorem osCurS_val {s : OsSt} (h : s.co < u128Bound) (hok : AllOk C rd σ (osCurS s).1) :
    σ (.n (osCurS s).2.1) = s.cur σ := osMat_val h hok

/-! ## One round -/

/-- The claim enters a round linearly, with the factor `α`. -/
theorem roundClaim_add (claim D alpha beta u0 w c0 c1 : E) :
    roundClaim (claim + D) alpha beta u0 w c0 c1 =
      roundClaim claim alpha beta u0 w c0 c1 + alpha * D := by
  unfold roundClaim; ring

theorem fs_five (st : OsSt) (hfs : st.fs.length = 5) :
    ∃ f0 f1 f2 f3 f4, st.fs = [f0, f1, f2, f3, f4] := by
  match h : st.fs, hfs with
  | [f0, f1, f2, f3, f4], _ => exact ⟨f0, f1, f2, f3, f4, rfl⟩

/-- **One `opening_round` call** (G:1540-1541) runs `foldRound` from a Spec state whose claim is
the guest's plus `D`: the five words at the cursor; the new claim the guest's plus `α·D`; `α`
stored at `fold_challenges·g^i`, `α, β` at `round_coefs·g^(2i)`. -/
theorem osRound_sound
    (hR : ∀ a r, WinTabs rd (a.getD 7 0) → C "opening_round" a r → MeaningOpeningRound rd a r)
    (hwt : WinTabs rd (σ (.n osTabs)))
    {P : List (ℕ × ℕ × ℕ)} {i : ℕ} {st : OsSt} (ws : WhirState) (D : E) (hfs : st.fs.length = 5)
    (hm : MatsOk σ st.mats) (hco : st.co < u128Bound) (hi : 2 * i < u128Bound)
    (hc : ws.claim = σ (.n st.claim) + D) (hok : AllOk C rd σ (osRound P i st).1) :
    ∃ (xs : List E) (alpha : E) (round : FoldRound), xs.length = 5 ∧ ReadsAt rd (st.cur σ) xs ∧
      RunsTo (foldRound ws) (st.F σ) xs
        ({ ws with
            claim := σ (.n (osRound P i st).2.claim) + alpha * D
            alphas := ws.alphas ++ [alpha] }, round) ((osRound P i st).2.F σ) ∧
      (osRound P i st).2.cur σ = st.cur σ * gen ^ 5 ∧ (osRound P i st).2.fs.length = 5 ∧
      MatsOk σ (osRound P i st).2.mats ∧ (osRound P i st).2.co = 0 ∧
      (osRound P i st).2.pad = st.pad ∧
      LoadHolds rd (σ (.n osFch)) i alpha ∧ LoadHolds rd (σ (.n osCoefs)) (2 * i) round.alpha ∧
      LoadHolds rd (σ (.n osCoefs)) (2 * i + 1) round.beta := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fs_five st hfs
  unfold osRound at hok ⊢
  simp only [allOk_append] at hok
  obtain ⟨⟨⟨hcu, hfp⟩, hcp⟩, hcall⟩ := hok
  have ecu := osCurS_val hco hcu
  have hi1 : i < u128Bound := lt_of_le_of_lt (by omega) hi
  obtain ⟨efp, hm1⟩ := osMatS_val (s := (osCurS st).2.2) (off := i) hm hi1 hfp
  obtain ⟨ecp, hm2⟩ := osMatS_val hm1 hi hcp
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_call] at hcall
  have hM := hR _ _ (by simpa [hf] using hwt) hcall
  simp only [hf, List.cons_append, List.nil_append, List.map_cons, List.map_nil, osRun,
    List.range_succ, List.range_zero, Nat.add_zero] at hM
  simp only [MeaningOpeningRound] at hM
  obtain ⟨u0, w, c0, c1, n2, hrd, g2, lg, la, lb, hret⟩ := hM
  rw [ecu] at hrd hret
  rw [efp] at lg
  rw [ecp] at la lb
  rw [loadHolds_mul_gen_pow, Nat.add_zero] at lg la
  rw [loadHolds_mul_gen_pow] at lb
  set fs := [σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)] with hfsv
  have hF : st.F σ = ⟨fs, []⟩ := by simp [OsSt.F, hf, fs]
  have hrun := opening_round_run ws fs u0 w c0 c1 n2 g2
  simp only [Fs.squeeze, capOf, List.cons_append, List.nil_append, List.cons.injEq] at hret
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, -⟩ := hret
  refine ⟨[u0, w, c0, c1, n2], (rdG2 fs [u0, w, c0, c1] n2).1,
    ⟨(rdG2 fs [u0, w, c0, c1] n2).1,
      (rdG2 fs [u0, w, c0, c1] n2).2.squeeze.1⟩, rfl, hrd, ?_, ?_, rfl, ?_, rfl,
    rfl, lg, la, lb⟩
  · rw [hF]
    refine RunsTo.of_eq hrun rfl rfl ?_ ?_
    · rw [hc, roundClaim_add, e6]
      rfl
    · simp only [OsSt.F, List.map_cons, List.map_nil, e0, e1, e2, e3, e4]
      rfl
  · simp only [OsSt.cur, pow_zero, mul_one]; exact e5
  · exact hm2

/-! ## The rounds -/

instance : Inhabited FoldRound := ⟨⟨0, 0⟩⟩

/-- **The template's `n` rounds run `foldRounds n`** from a Spec state whose claim is the guest's
plus `D`: the `5n` words at the cursor; the Spec's claim after them the guest's plus `D` times the
`α`s; the `α`s stored from `fold_challenges·g^i`, the rounds' `α, β` from
`round_coefs·g^(2i)`. -/
theorem osRounds_sound
    (hR : ∀ a r, WinTabs rd (a.getD 7 0) → C "opening_round" a r → MeaningOpeningRound rd a r)
    (hwt : WinTabs rd (σ (.n osTabs))) (P : List (ℕ × ℕ × ℕ)) : ∀ (n i : ℕ) (st : OsSt) (ws : WhirState) (D : E),
      st.fs.length = 5 → MatsOk σ st.mats → st.co < u128Bound → 2 * (i + n) < u128Bound →
      ws.claim = σ (.n st.claim) + D → AllOk C rd σ (osRounds P i n st).1 →
      ∃ (xs gs : List E) (rounds : List FoldRound), xs.length = 5 * n ∧ gs.length = n ∧
        rounds.length = n ∧ ReadsAt rd (st.cur σ) xs ∧
        RunsTo (foldRounds n ws) (st.F σ) xs
          ({ ws with
              claim := σ (.n (osRounds P i n st).2.claim) + gs.prod * D
              alphas := ws.alphas ++ gs }, rounds) ((osRounds P i n st).2.F σ) ∧
        (osRounds P i n st).2.cur σ = st.cur σ * gen ^ (5 * n) ∧
        (osRounds P i n st).2.fs.length = 5 ∧ MatsOk σ (osRounds P i n st).2.mats ∧
        (osRounds P i n st).2.co < u128Bound ∧ (osRounds P i n st).2.pad = st.pad ∧
        (∀ j < n, LoadHolds rd (σ (.n osFch)) (i + j) gs[j]!) ∧
        (∀ j < n, LoadHolds rd (σ (.n osCoefs)) (2 * (i + j)) rounds[j]!.alpha ∧
          LoadHolds rd (σ (.n osCoefs)) (2 * (i + j) + 1) rounds[j]!.beta)
  | 0, i, st, ws, D, hfs, hm, hco, _, hc, _ => by
    refine ⟨[], [], [], rfl, rfl, rfl, readsAt_nil _ _, ?_, by simp [osRounds], hfs, hm, hco, rfl,
      fun j h ↦ absurd h (Nat.not_lt_zero _), fun j h ↦ absurd h (Nat.not_lt_zero _)⟩
    refine RunsTo.of_eq (runsTo_ret _ _) rfl rfl ?_ rfl
    obtain ⟨c, g, gl⟩ := ws
    simp only at hc
    simp [hc, osRounds]
  | n + 1, i, st, ws, D, hfs, hm, hco, hi, hc, hok => by
    simp only [osRounds] at hok ⊢
    rw [allOk_append] at hok
    obtain ⟨xs0, g0, r0, hx0, hrd0, hrun0, hcur0, hfs0, hm0, hco0, hpad0, lg0, la0, lb0⟩ :=
      osRound_sound hR hwt ws D hfs hm hco (by omega) hc hok.1
    obtain ⟨xs, gs, rounds, hxl, hgl, hrl, hrd, hrun, hcur, hfs', hm', hco', hpad', lg, lc⟩ :=
      osRounds_sound hR hwt P n (i + 1) (osRound P i st).2
        { ws with
          claim := σ (.n (osRound P i st).2.claim) + g0 * D
          alphas := ws.alphas ++ [g0] } (g0 * D) hfs0 hm0 (by rw [hco0]; unfold u128Bound; positivity)
        (by omega) rfl hok.2
    refine ⟨xs0 ++ xs, g0 :: gs, r0 :: rounds, by simp [hx0, hxl]; ring, by simp [hgl],
      by simp [hrl], ?_, ?_, ?_, hfs', hm', hco', by rw [hpad', hpad0], ?_, ?_⟩
    · exact readsAt_append hrd0 (by rw [hx0, ← hcur0]; exact hrd)
    · have h := hrun0.bind (f := fun p ↦ do
          let (s, round) := p
          let (s, rounds) ← foldRounds n s
          return (s, round :: rounds))
        (hrun.bind (f := fun p ↦ (pure (p.1, r0 :: p.2) : VerifierProgram _)) (runsTo_ret _ _))
      refine RunsTo.of_eq h rfl (by simp) ?_ rfl
      have e : gs.prod * (g0 * D) = g0 * (gs.prod * D) := by ring
      simp only [List.prod_cons, List.append_assoc, List.singleton_append, mul_assoc, e]
    · rw [hcur, hcur0, mul_assoc, ← pow_add]; ring_nf
    · intro j h
      rcases j with _ | j
      · simpa using lg0
      · have := lg j (by omega)
        rw [show i + 1 + j = i + (j + 1) by ring] at this
        simpa using this
    · intro j h
      rcases j with _ | j
      · simpa using ⟨la0, lb0⟩
      · have := lc j (by omega)
        rw [show i + 1 + j = i + (j + 1) by ring] at this
        simpa using this

end
end LeanVM.Guest.B1.Whir
