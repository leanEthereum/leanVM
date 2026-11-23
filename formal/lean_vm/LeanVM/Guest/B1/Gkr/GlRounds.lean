/-
  LeanVM.Guest.B1.Gkr.GlRounds

  A run of inlined GKR rounds (`glRounds`) is a run of `gkrRun`: soundly.
-/

module

public import LeanVM.Guest.B1.Gkr.GlT
import LeanVM.Guest.B1.Tables.Basic

/-!
# A run of rounds, soundly

`GlRun rd n cur pt claim cap cap' claim'`: `n` rounds from the capacity `cap` (nothing waiting)
and the claim `claim` read the `4n` words at `cur`, their eq factors at `pt[0 .. n]`, store their
challenges at `pt[42 ..]`, and end at the capacity `cap'` and the claim `claim'` (`gkrRun`).

* `glRun_append`: two runs in sequence are one;
* `glRounds_sound`: `glRounds B n` is a run, from `claim0`, `cap0` to the last round's values
  (`glClaimAfter`, `glCapAfter`), when `npt·g^noff = pt·g^42`;
* `glRun_of_out`, `glOut_of_run`: a run between two records (`TbGkrRoundsOut`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **`n` rounds** from `cap`, `claim` at the cursor `cur` and the point row `pt`, to `cap'`,
`claim'`. -/
def GlRun (rd : Reader) (n : ℕ) (cur pt claim : E) (cap cap' : List E) (claim' : E) : Prop :=
  ∃ (cs : List (List E)) (es : List E),
    cs.length = n ∧ (∀ c ∈ cs, c.length = 4) ∧ TbReadsAt rd cur cs.flatten ∧
    es.length = n ∧ TbReadsAt rd pt es ∧
    TbReadsAt rd (pt * gen ^ 42) (gkrRun cs es claim ⟨cap, []⟩).1 ∧
    cap' = (gkrRun cs es claim ⟨cap, []⟩).2.2.cap ∧ claim' = (gkrRun cs es claim ⟨cap, []⟩).2.1

theorem glRun_zero {rd : Reader} {cur pt claim : E} {cap : List E} :
    GlRun rd 0 cur pt claim cap cap claim :=
  ⟨[], [], rfl, by simp, tbReadsAt_nil _ _, rfl, tbReadsAt_nil _ _, tbReadsAt_nil _ _, rfl, rfl⟩

/-- **Two runs in sequence.** -/
theorem glRun_append {rd : Reader} {n1 n2 : ℕ} {cur pt claim claim1 claim2 : E}
    {cap cap1 cap2 : List E} (h1 : GlRun rd n1 cur pt claim cap cap1 claim1)
    (h2 : GlRun rd n2 (cur * gen ^ (4 * n1)) (pt * gen ^ n1) claim1 cap1 cap2 claim2) :
    GlRun rd (n1 + n2) cur pt claim cap cap2 claim2 := by
  obtain ⟨cs1, es1, hl1, h4, hr1, he1, hre1, hch1, hc1, hcl1⟩ := h1
  obtain ⟨cs2, es2, hl2, h42, hr2, he2, hre2, hch2, hc2, hcl2⟩ := h2
  subst hc1 hcl1 hc2 hcl2
  have hrun := tb_gkrRun_append cs1 cs2 es1 es2 claim ⟨cap, []⟩ (hl1.trans he1.symm)
  refine ⟨cs1 ++ cs2, es1 ++ es2, by simp [hl1, hl2], fun c hc' => ?_, ?_, by simp [he1, he2],
    ?_, ?_, ?_, ?_⟩
  · rcases List.mem_append.mp hc' with h | h
    · exact h4 c h
    · exact h42 c h
  · rw [List.flatten_append, tbReadsAt_append, flatten_length_four h4, hl1]
    exact ⟨hr1, hr2⟩
  · rw [tbReadsAt_append, he1]
    exact ⟨hre1, hre2⟩
  · rw [hrun, tbReadsAt_append, tb_gkrRun_length _ _ _ _ (hl1.trans he1.symm), hl1]
    refine ⟨hch1, ?_⟩
    rw [tb_gkrRun_eta _ _ _ _ rfl]
    rw [show pt * gen ^ 42 * gen ^ n1 = pt * gen ^ n1 * gen ^ 42 by ring]
    exact hch2
  · rw [hrun, tb_gkrRun_eta cs1 es1 claim cap rfl]
  · rw [hrun, tb_gkrRun_eta cs1 es1 claim cap rfl]

/-- The capacity after `n` rounds from value `B`. -/
def glCapAfter (B n : ℕ) (cap0 : List V) : List V := if n = 0 then cap0 else glCap (B + 39 * n - 19)

/-- The claim after `n` rounds from value `B`. -/
def glClaimAfter (B n : ℕ) (claim0 : V) : V := if n = 0 then claim0 else .n (B + 39 * n - 1)

theorem glRound_noRet (B : ℕ) (cur pt npt : V) (noff : ℕ) (claim0 : V) (cap0 : List V) (q : ℕ) :
    Stmt.noRetList (glRound B cur pt npt noff claim0 cap0 q) = true := gkRoundN_noRet ..

theorem glRounds_noRet (B n : ℕ) (cur pt npt : V) (noff : ℕ) (claim0 : V) (cap0 : List V) :
    Stmt.noRetList (glRounds B n cur pt npt noff claim0 cap0) = true := by
  unfold glRounds
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, tb_noRetList_append, ih]
    simp [glRound_noRet]

theorem glRounds_succ (B n : ℕ) (cur pt npt : V) (noff : ℕ) (claim0 : V) (cap0 : List V) :
    glRounds B (n + 1) cur pt npt noff claim0 cap0 =
      glRounds B n cur pt npt noff claim0 cap0 ++
        gkRoundN (B + 39 * n) n cur pt npt noff (glClaimAfter B n claim0) (glCapAfter B n cap0) := by
  simp only [glRounds, List.range_succ, List.map_append, List.flatten_append, List.map_cons,
    List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, glRound, glClaimAfter,
    glCapAfter]

/-- A record's capacity cells, `glCap b`'s values. -/
theorem tbCapAt_glCap {rd : Reader} {σ : Val} {rec : E} {off b : ℕ}
    (h : ∀ k < 5, LoadHolds rd rec (off + k) (σ (.n (b + k)))) :
    TbCapAt rd rec off 1 ((glCap b).map σ) := by
  refine ⟨by simp [glCap], fun j hj => ?_⟩
  have hj5 : j < 5 := by simpa [glCap] using hj
  simp only [glCap, List.getElem_map, List.getElem_range, Nat.mul_one]
  exact h j hj5

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **One round** is a run of one. -/
theorem glRun_one {B q : ℕ} {cur pt npt : V} {noff : ℕ} {claimV : V} {cap : List V}
    (h : Stmt.HoldsList C rd σ (gkRoundN B q cur pt npt noff claimV cap) True kret)
    (hnpt : σ npt * gen ^ noff = σ pt * gen ^ 42) :
    GlRun rd 1 (σ cur * gen ^ (4 * q)) (σ pt * gen ^ q) (σ claimV) (cap.map σ)
      ((glCap (B + 20)).map σ) (σ (.n (B + 38))) := by
  obtain ⟨xs, hl, hrd, hch, hcap, hst, e, he, hcl⟩ := holds_gkRoundN h
  have hst' : LoadHolds rd (σ pt * gen ^ q) 42 (σ (.n (B + 12))) := by
    rw [tb_loadHolds_mul_gen_pow, Nat.add_comm, ← tb_loadHolds_mul_gen_pow, ← hnpt,
      tb_loadHolds_mul_gen_pow]
    exact hst
  refine ⟨[xs], [e], rfl, by simp [hl], ?_, rfl, ?_, ?_, ?_, ?_⟩
  · intro k hk
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hk ⊢
    rw [tb_loadHolds_mul_gen_pow]
    have := hrd k (by omega)
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] using this
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    obtain rfl : k = 0 := by omega
    rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]
    exact he
  · intro k hk
    simp only [gkrRun, List.length_cons, List.length_nil] at hk
    obtain rfl : k = 0 := by omega
    simp only [gkrRun, List.getElem_cons_zero]
    rw [← hch, tb_loadHolds_mul_gen_pow, Nat.add_zero]
    exact hst'
  · simp only [gkrRun]
    rw [← hcap]
    simp [glCap, Nat.add_assoc]
  · simp only [gkrRun]
    rw [hcl, hch]

/-- **A run of rounds, soundly.** -/
theorem glRounds_sound {B : ℕ} {cur pt npt : V} {noff : ℕ} {claim0 : V} {cap0 : List V} :
    ∀ n, Stmt.HoldsList C rd σ (glRounds B n cur pt npt noff claim0 cap0) True kret →
      σ npt * gen ^ noff = σ pt * gen ^ 42 →
      GlRun rd n (σ cur) (σ pt) (σ claim0) (cap0.map σ) ((glCapAfter B n cap0).map σ)
        (σ (glClaimAfter B n claim0))
  | 0, _, _ => by simpa [glCapAfter, glClaimAfter] using glRun_zero
  | n + 1, h, hnpt => by
    rw [glRounds_succ, tb_holdsList_append_noRet (glRounds_noRet ..)] at h
    have ih := glRounds_sound n h.1 hnpt
    have h1 := glRun_one h.2 hnpt
    have e1 : glCapAfter B (n + 1) cap0 = glCap (B + 39 * n + 20) := by
      simp only [glCapAfter, Nat.add_one_ne_zero, ↓reduceIte]
      rw [show B + 39 * (n + 1) - 19 = B + 39 * n + 20 by omega]
    have e2 : glClaimAfter B (n + 1) claim0 = .n (B + 39 * n + 38) := by
      simp only [glClaimAfter, Nat.add_one_ne_zero, ↓reduceIte]
      rw [show B + 39 * (n + 1) - 1 = B + 39 * n + 38 by omega]
    rw [e1, e2]
    exact glRun_append ih h1

end Sem

/-! ## Runs between records -/

/-- **Rounds between records** are a run from the first record's values to the second's. -/
theorem glRun_of_out {rd : Reader} {n s : ℕ} {rec pt : E} (h : TbGkrRoundsOut n s rd rec pt) :
    ∃ (cap cap' : List E) (cur claim claim' : E),
      TbCapAt rd rec 0 1 cap ∧ LoadHolds rd rec 5 cur ∧
      LoadHolds rd rec 6 claim ∧ GlRun rd n cur pt claim cap cap' claim' ∧
      TbCapAt rd rec (7 * s) 1 cap' ∧ LoadHolds rd rec (7 * s + 5) (cur * gen ^ (4 * n)) ∧
      LoadHolds rd rec (7 * s + 6) claim' := by
  obtain ⟨cap, cur, claim, cs, es, hc, hcur, hcl, hl, h4, hrd, hel, hes, hre, hcap, hcur', hcl'⟩ := h
  exact ⟨cap, _, cur, claim, _, hc, hcur, hcl, ⟨cs, es, hl, h4, hrd, hel, hes, hre, rfl, rfl⟩, hcap,
    hcur', hcl'⟩

/-- **A run whose ends are stored** in two records is rounds between them. -/
theorem glOut_of_run {rd : Reader} {n s : ℕ} {rec pt cur claim claim' : E} {cap cap' : List E}
    (hc : TbCapAt rd rec 0 1 cap) (hcur : LoadHolds rd rec 5 cur)
    (hcl : LoadHolds rd rec 6 claim) (hr : GlRun rd n cur pt claim cap cap' claim')
    (hc' : TbCapAt rd rec (7 * s) 1 cap') (hcur' : LoadHolds rd rec (7 * s + 5) (cur * gen ^ (4 * n)))
    (hcl' : LoadHolds rd rec (7 * s + 6) claim') : TbGkrRoundsOut n s rd rec pt := by
  obtain ⟨cs, es, hl, h4, hrd, hel, hes, hre, rfl, rfl⟩ := hr
  exact ⟨cap, cur, claim, cs, es, hc, hcur, hcl, hl, h4, hrd, hel, hes, hre, hc', hcur', hcl'⟩

end
end LeanVM.Guest.B1.Tables
