/-
  LeanVM.Guest.B1.Whir.Folds

  The template's fold rounds (`opening_round`, inline) run the Spec's `foldRounds`.
-/

module

public import LeanVM.Guest.B1.Whir.RoundSound
public import LeanVM.Guest.B1.Whir.Loops

/-!
# The fold rounds (TRIAGE G #35, #42)

The guest's running values, read through a valuation `σ` (`OsSt.F`, `OsSt.cur`): the sponge it
carries (its five capacity cells, nothing waiting), the cursor `cb·g^co`. `osRound_sound`: one
round inline (its meaning, `MeaningOpeningRound`, `osRoundCore_mean`) runs `foldRound`
(`opening_round_run`);
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

theorem readsAt_getD' {p : E} {xs : List E} (h : ReadsAt rd p xs) {j : ℕ} (hj : j < xs.length) :
    LoadHolds rd p j (xs.getD j 0) := by
  rw [List.getD_eq_getElem _ _ hj]; exact h j hj

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

/-- The zero run's cells past its first are zero. -/
def PadZ (σ : Val) (p : ℕ) : Prop :=
  σ (.n (p + 1)) = 0 ∧ σ (.n (p + 2)) = 0 ∧ σ (.n (p + 3)) = 0 ∧ σ (.n (p + 4)) = 0

/-- **One round, inline,** runs `foldRound` from a Spec state whose claim is the guest's plus `D`:
the five words at the cursor; the new claim the guest's plus `α·D`; `α` stored at
`fold_challenges·g^i`, `α, β` at `round_coefs·g^(2i)`. -/
theorem osRound_sound (hgc : GcOk C rd σ) (hwt : WinTabs rd (σ (.n osTabs)))
    {cp last : Bool} {i : ℕ} {st : OsSt} (ws : WhirState) (D : E) (hfs : st.fs.length = 5)
    (hpz : PadZ σ (st.pad.getD osPadV)) (hc : ws.claim = σ (.n st.claim) + D)
    (hok : AllOk C rd σ (osRound cp last i st).1) :
    ∃ (xs : List E) (alpha : E) (round : FoldRound), xs.length = 5 ∧ ReadsAt rd (st.cur σ) xs ∧
      RunsTo (foldRound ws) (st.F σ) xs
        ({ ws with
            claim := σ (.n (osRound cp last i st).2.claim) + alpha * D
            alphas := ws.alphas ++ [alpha] }, round) ((osRound cp last i st).2.F σ) ∧
      (osRound cp last i st).2.cur σ = st.cur σ * gen ^ 5 ∧ (osRound cp last i st).2.fs.length = 5 ∧
      (osRound cp last i st).2.mats = st.mats ∧ (osRound cp last i st).2.co = st.co + 5 ∧
      (osRound cp last i st).2.cb = st.cb ∧ (osRound cp last i st).2.pad = st.pad ∧
      LoadHolds rd (σ (.n osFch)) i alpha ∧ LoadHolds rd (σ (.n osCoefs)) (2 * i) round.alpha ∧
      LoadHolds rd (σ (.n osCoefs)) (2 * i + 1) round.beta := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fs_five st hfs
  set b := if cp then st.k else st.k - 5 with hb
  set cap := if cp then (List.range 5).map (st.k + ·) else st.fs with hcapd
  have hstm : (osRound cp last i st).1 =
      (if cp then (List.range 5).map (fun i ↦ osCp (st.k + i) (st.fs.getD i 0)) else []) ++
        osRoundCore b (st.pad.getD osPadV) st.cb st.co st.claim i cap ++
        (if last then [] else
          (List.range 5).map (fun i ↦ osCp (osRoundD b + 10 + i) (osRoundC b + 8 + i))) := rfl
  rw [hstm, allOk_append, allOk_append] at hok
  obtain ⟨⟨hcp, hcore⟩, hend⟩ := hok
  have hcap : cap.map (fun j ↦ σ (.n j)) = [σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)] := by
    rw [hcapd]
    cases cp
    · simp [hf]
    · simp only [↓reduceIte, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
        List.nil_append, List.cons_append, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_copy,
        osCp, hf, List.getD_cons_zero, List.getD_cons_succ] at hcp ⊢
      obtain ⟨e0, e1, e2, e3, e4⟩ := hcp
      simp only [Nat.add_zero] at e0
      simp [e0, e1, e2, e3, e4]
  have hM := osRoundCore_mean hgc hwt hcap hpz hcore
  simp only [MeaningOpeningRound] at hM
  obtain ⟨u0, w, c0, c1, n2, hrd, g2, lg, la, lb, hret⟩ := hM
  rw [loadHolds_mul_gen_pow, Nat.add_zero] at lg la
  rw [loadHolds_mul_gen_pow] at lb
  set fs := [σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)] with hfsv
  have hF : st.F σ = ⟨fs, []⟩ := by simp [OsSt.F, hf, fs]
  have hrun := opening_round_run ws fs u0 w c0 c1 n2 g2
  simp only [Fs.squeeze] at hret
  have hcapE : capOf (rdG2 fs [u0, w, c0, c1] n2).2.perm =
      (List.range 5).map (fun j ↦ σ (.n (osRoundC b + 8 + j))) := by
    have := congrArg (List.take 5) hret
    simpa [capOf, List.range_succ] using this.symm
  have hcl : σ (.n (osRoundD b + 9)) =
      roundClaim (σ (.n st.claim)) (rdG2 fs [u0, w, c0, c1] n2).1 (rdG2 fs [u0, w, c0, c1] n2).2.squeeze.1
        u0 w c0 c1 := by
    have := congrArg (fun l ↦ l.getD 6 0) hret
    simpa [capOf, List.range_succ, Fs.squeeze] using this
  have hF' : (osRound cp last i st).2.F σ = (rdG2 fs [u0, w, c0, c1] n2).2.squeeze.2 := by
    unfold osRound; dsimp only; rw [← hb]
    simp only [Fs.squeeze, hcapE]
    cases last
    · simp only [Bool.false_eq_true, ↓reduceIte, OsSt.F] at hend ⊢
      simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
        List.cons_append, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_copy, osCp] at hend
      obtain ⟨e0, e1, e2, e3, e4⟩ := hend
      simp only [Nat.add_zero] at e0
      simp [List.range_succ, e0, e1, e2, e3, e4]
    · simp [OsSt.F, List.map_map, Function.comp_def]
  refine ⟨[u0, w, c0, c1, n2], (rdG2 fs [u0, w, c0, c1] n2).1,
    ⟨(rdG2 fs [u0, w, c0, c1] n2).1, (rdG2 fs [u0, w, c0, c1] n2).2.squeeze.1⟩, rfl,
    by simpa [OsSt.cur] using hrd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, lg, la, lb⟩
  · rw [hF, hF']
    refine RunsTo.of_eq hrun rfl rfl ?_ rfl
    have hcl' : σ (.n (osRound cp last i st).2.claim) = σ (.n (osRoundD b + 9)) := by
      unfold osRound; dsimp only; cases last <;> rfl
    rw [hc, roundClaim_add, hcl', hcl]
  · unfold osRound; dsimp only; cases last <;> simp [OsSt.cur, mul_assoc, ← pow_add]
  · unfold osRound; dsimp only; cases last <;> simp
  · unfold osRound; dsimp only; cases last <;> rfl
  · unfold osRound; dsimp only; cases last <;> rfl
  · unfold osRound; dsimp only; cases last <;> rfl
  · unfold osRound; dsimp only; cases last <;> rfl

/-! ## The rounds -/

instance : Inhabited FoldRound := ⟨⟨0, 0⟩⟩

/-- **The template's `n` rounds run `foldRounds n`** from a Spec state whose claim is the guest's
plus `D`: the `5n` words at the cursor; the Spec's claim after them the guest's plus `D` times the
`α`s; the `α`s stored from `fold_challenges·g^i`, the rounds' `α, β` from
`round_coefs·g^(2i)`. -/
theorem osRounds_sound (hgc : GcOk C rd σ) (hwt : WinTabs rd (σ (.n osTabs))) :
    ∀ (cp : Bool) (n i : ℕ) (st : OsSt) (ws : WhirState) (D : E),
      st.fs.length = 5 → PadZ σ (st.pad.getD osPadV) →
      ws.claim = σ (.n st.claim) + D → AllOk C rd σ (osRounds cp i n st).1 →
      ∃ (xs gs : List E) (rounds : List FoldRound), xs.length = 5 * n ∧ gs.length = n ∧
        rounds.length = n ∧ ReadsAt rd (st.cur σ) xs ∧
        RunsTo (foldRounds n ws) (st.F σ) xs
          ({ ws with
              claim := σ (.n (osRounds cp i n st).2.claim) + gs.prod * D
              alphas := ws.alphas ++ gs }, rounds) ((osRounds cp i n st).2.F σ) ∧
        (osRounds cp i n st).2.cur σ = st.cur σ * gen ^ (5 * n) ∧
        (osRounds cp i n st).2.fs.length = 5 ∧ (osRounds cp i n st).2.mats = st.mats ∧
        (osRounds cp i n st).2.co = st.co + 5 * n ∧ (osRounds cp i n st).2.cb = st.cb ∧
        (osRounds cp i n st).2.pad = st.pad ∧
        (∀ j < n, LoadHolds rd (σ (.n osFch)) (i + j) gs[j]!) ∧
        (∀ j < n, LoadHolds rd (σ (.n osCoefs)) (2 * (i + j)) rounds[j]!.alpha ∧
          LoadHolds rd (σ (.n osCoefs)) (2 * (i + j) + 1) rounds[j]!.beta)
  | _, 0, i, st, ws, D, hfs, _, hc, _ => by
    refine ⟨[], [], [], rfl, rfl, rfl, readsAt_nil _ _, ?_, by simp [osRounds], hfs, rfl, rfl, rfl,
      rfl, fun j h ↦ absurd h (Nat.not_lt_zero _), fun j h ↦ absurd h (Nat.not_lt_zero _)⟩
    refine RunsTo.of_eq (runsTo_ret _ _) rfl rfl ?_ rfl
    obtain ⟨c, g, gl⟩ := ws
    simp only at hc
    simp [hc, osRounds]
  | cp, n + 1, i, st, ws, D, hfs, hpz, hc, hok => by
    simp only [osRounds] at hok ⊢
    rw [allOk_append] at hok
    obtain ⟨xs0, g0, r0, hx0, hrd0, hrun0, hcur0, hfs0, hm0, hco0, hcb0, hpad0, lg0, la0, lb0⟩ :=
      osRound_sound hgc hwt ws D hfs hpz hc hok.1
    obtain ⟨xs, gs, rounds, hxl, hgl, hrl, hrd, hrun, hcur, hfs', hm', hco', hcb', hpad', lg, lc⟩ :=
      osRounds_sound hgc hwt false n (i + 1) (osRound cp (n == 0) i st).2
        { ws with
          claim := σ (.n (osRound cp (n == 0) i st).2.claim) + g0 * D
          alphas := ws.alphas ++ [g0] } (g0 * D) hfs0 (by rw [hpad0]; exact hpz) rfl hok.2
    refine ⟨xs0 ++ xs, g0 :: gs, r0 :: rounds, by simp [hx0, hxl]; ring, by simp [hgl],
      by simp [hrl], ?_, ?_, ?_, hfs', by rw [hm', hm0], by rw [hco', hco0]; ring,
      by rw [hcb', hcb0], by rw [hpad', hpad0], ?_, ?_⟩
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

/-- A run of rounds changes the state's next value, sponge, cursor offset and claim alone. -/
theorem osRounds_snd : ∀ (cp : Bool) (i n : ℕ) (st : OsSt), ∃ k fs co claim,
    (osRounds cp i n st).2 = { st with k := k, fs := fs, co := co, claim := claim }
  | _, _, 0, st => ⟨st.k, st.fs, st.co, st.claim, rfl⟩
  | cp, i, n + 1, st => by
    obtain ⟨k, fs, co, cl, h⟩ := osRounds_snd false (i + 1) n (osRound cp (n == 0) i st).2
    refine ⟨k, fs, co, cl, ?_⟩
    show (osRounds false (i + 1) n (osRound cp (n == 0) i st).2).2 = _
    rw [h]
    generalize (n == 0) = b
    cases cp <;> cases b <;> rfl

end
end LeanVM.Guest.B1.Whir
