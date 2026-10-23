/-
  LeanVM.Guest.B1.Tables.GkrLoops

  `verify_bus_gkr`'s inner loops: a layer's sumcheck rounds (`__loop101`) and the copy of the
  final point into `zeta` (`__loop11`).
-/

module

public import LeanVM.Guest.B1.Tables.GkrBase

/-!
# `verify_bus_gkr`'s inner loops (TRIAGE #37)

* `__loop101(x, g^L, rounds, round_pos, point_row, nextrow)` (G:1388-1396): round `x` of a
  layer's sumcheck reads the round slot at `round_pos·x`, runs `sumcheck_round5` with the eq
  factor `point_row[x]`, stores the challenge at `nextrow[x·g²]` and the next state at the next
  slot (`GkrRound`).
* `__loop11(x, g_bus_mu, zeta, final_point_row)` (G:1435-1436): `zeta[x] = final_point_row[x]`.

Both are read for soundness only (`Main.loop_sound`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `__loop11` -/

theorem find_loop11 : coreProgram.find? "__loop11" = some Data.core41 :=
  Program.find?_of_indexOf? (j := 41) (by decide +kernel) rfl

/-- **`__loop11`**, one iteration: the word of `row` at `x` is stored in `zeta` at `x`, and the
loop goes on at `x·g` while `x·g ≠ g_bus_mu`. -/
theorem loop11_step {rd : Reader} {gmu zeta row x : E}
    (h : coreProgram.Rel rd "__loop11" [x, gmu, zeta, row] []) :
    (∃ v, LoadHolds rd (row * x) 0 v ∧ LoadHolds rd (zeta * x) 0 v) ∧
      (x * gen + gmu ≠ 0 → coreProgram.Rel rd "__loop11" [x * gen, gmu, zeta, row] []) := by
  rw [rel_iff_sem find_loop11, show Fn.params Data.core41 = [.n 0, .n 1, .n 2, .n 3] from rfl,
    show Fn.body Data.core41 = Data.core41.body from rfl, Data.core41.body] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, and_true,
    word_gen] at h
  obtain ⟨σ, hp, h4, l5, h6, l5', h7, h8, h9, h10, h11, -, hcall⟩ := h
  simp only [List.cons.injEq] at hp
  obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hp
  refine ⟨⟨σ (.n 5), by rwa [h4] at l5, by rwa [h6] at l5'⟩, fun hne => ?_⟩
  have := hcall (by rwa [h9, h8, h7])
  rwa [h11, h10] at this

/-- **`__loop11` behind its guard**: `zeta` holds the `m` first words of `row`, `g_bus_mu = g^m`. -/
theorem loop11_sound {rd : Reader} {zeta row : E} {m : ℕ} (hm : m < ordG) {pt : List E}
    (hpt : ReadsAt rd row pt) (hl : pt.length = m)
    (h : 1 + gen ^ m ≠ 0 → coreProgram.Rel rd "__loop11" [1, gen ^ m, zeta, row] []) :
    ReadsAt rd zeta pt := by
  have hb := Main.loop_sound (B := fun x => ∃ v, LoadHolds rd (row * x) 0 v ∧
      LoadHolds rd (zeta * x) 0 v) (ps := [gen ^ m, zeta, row]) hm rfl
    (fun x hx => loop11_step hx) h
  intro k hk
  obtain ⟨v, h1, h2⟩ := hb k (by omega)
  rw [loadHolds_gen_pow_mul, Nat.add_zero] at h1 h2
  rwa [← loadHolds_unique (hpt k hk) h1] at h2

/-! ## `__loop101` -/

set_option maxRecDepth 100000 in
theorem find_loop101 : coreProgram.find? "__loop101" = some Data.core574 :=
  Program.find?_of_indexOf? (j := 574) (by decide +kernel) rfl

/-- `__loop101`'s statements before its `ret`. -/
noncomputable def l101Pre : List Stmt := (Fn.body Data.core574).take 23

theorem core574_body : Fn.body Data.core574 = l101Pre ++ [.ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem l101Pre_noRet : Stmt.noRetList l101Pre = true := by decide +kernel

/-- **Round `x` of a layer's sumcheck**: the slot at `round_pos·x` holds the state of `cv`, the
cursor, the claim; the eq factor `e` is `point_row[x]`; the four words at the cursor run the
round to `claim'` and the challenge `rk`, stored at `nextrow[x·g²]`; the next slot holds the new
state, the cursor four words on and `claim'`. -/
def GkrRound (rd : Reader) (rounds pos prow nrow x : E) : Prop :=
  ∃ (cv : Digest) (cur claim e : E) (ws : List E) (claim' rk : E) (cv' : Digest),
    LoadHolds rd (rounds * (pos * x) ^ 4) 0 (digestScalars cv).1 ∧
    LoadHolds rd (rounds * (pos * x) ^ 4) 1 (digestScalars cv).2 ∧
    LoadHolds rd (rounds * (pos * x) ^ 4) 2 cur ∧ LoadHolds rd (rounds * (pos * x) ^ 4) 3 claim ∧
    LoadHolds rd (prow * x) 0 e ∧ ws.length = 4 ∧ ReadsAt rd cur ws ∧
    RunsTo (roundPoly 5 claim (some e)) cv ws (claim', rk) cv' ∧ LoadHolds rd (nrow * x) 2 rk ∧
    LoadHolds rd (rounds * (pos * x) ^ 4) 4 (digestScalars cv').1 ∧
    LoadHolds rd (rounds * (pos * x) ^ 4) 5 (digestScalars cv').2 ∧
    LoadHolds rd (rounds * (pos * x) ^ 4) 6 (cur * gen ^ 4) ∧
    LoadHolds rd (rounds * (pos * x) ^ 4) 7 claim'

/-- **`__loop101`**, one iteration: the round, then the loop at `x·g` while `x·g ≠ g^L`. -/
theorem loop101_step {rd : Reader} {N rounds pos prow nrow x : E}
    (h : coreProgram.Rel rd "__loop101" [x, N, rounds, pos, prow, nrow] []) :
    GkrRound rd rounds pos prow nrow x ∧
      (x * gen + N ≠ 0 →
        coreProgram.Rel rd "__loop101" [x * gen, N, rounds, pos, prow, nrow] []) := by
  obtain ⟨σ, hp, hb, -⟩ := rel_pre find_loop101 core574_body l101Pre_noRet h
  simp only [show Fn.params Data.core574 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hp
  have hnr := l101Pre_noRet
  have a6 := holds_atom hnr hb 0 (.mul (.n 6) (.n 3) (.n 0)) (by decide +kernel)
  have a7 := holds_atom hnr hb 1 (.mul (.n 7) (.n 6) (.n 6)) (by decide +kernel)
  have a8 := holds_atom hnr hb 2 (.mul (.n 8) (.n 7) (.n 7)) (by decide +kernel)
  have a9 := holds_atom hnr hb 3 (.mul (.n 9) (.n 2) (.n 8)) (by decide +kernel)
  have l10 := holds_atom hnr hb 4 (.load (.n 10) (.n 9) 0) (by decide +kernel)
  have l11 := holds_atom hnr hb 5 (.load (.n 11) (.n 9) 1) (by decide +kernel)
  have l12 := holds_atom hnr hb 6 (.load (.n 12) (.n 9) 2) (by decide +kernel)
  have l13 := holds_atom hnr hb 7 (.load (.n 13) (.n 9) 3) (by decide +kernel)
  have a14 := holds_atom hnr hb 8 (.mul (.n 14) (.n 4) (.n 0)) (by decide +kernel)
  have l15 := holds_atom hnr hb 9 (.load (.n 15) (.n 14) 0) (by decide +kernel)
  have c10 := holds_call hnr hb 10 "sumcheck_round5" [.n 10, .n 11, .n 12, .n 13, .n 15]
    [.n 16, .n 17, .n 18, .n 19, .n 20] (by decide +kernel)
  have a21 := holds_atom hnr hb 11 (.mul (.n 21) (.n 5) (.n 0)) (by decide +kernel)
  have l20 := holds_atom hnr hb 12 (.load (.n 20) (.n 21) 2) (by decide +kernel)
  have l16 := holds_atom hnr hb 13 (.load (.n 16) (.n 9) 4) (by decide +kernel)
  have l17 := holds_atom hnr hb 14 (.load (.n 17) (.n 9) 5) (by decide +kernel)
  have l18 := holds_atom hnr hb 15 (.load (.n 18) (.n 9) 6) (by decide +kernel)
  have l19 := holds_atom hnr hb 16 (.load (.n 19) (.n 9) 7) (by decide +kernel)
  have a22 := holds_atom hnr hb 17 (.const (.n 22) (word 2 0 0)) (by decide +kernel)
  have a23 := holds_atom hnr hb 18 (.mul (.n 23) (.n 0) (.n 22)) (by decide +kernel)
  have a24 := holds_atom hnr hb 19 (.add (.n 24) (.n 23) (.n 1)) (by decide +kernel)
  have a25 := holds_atom hnr hb 20 (.const (.n 25) (word 2 0 0)) (by decide +kernel)
  have a26 := holds_atom hnr hb 21 (.mul (.n 26) (.n 0) (.n 25)) (by decide +kernel)
  have hc := holds_callIf hnr hb 22 (.n 24) "__loop101" [.n 26, .n 1, .n 2, .n 3, .n 4, .n 5]
    (by decide +kernel)
  simp only [Atom.Holds, word_gen, List.map_cons, List.map_nil] at *
  obtain ⟨cv, c1, c2, c3, c4, claim', r, cv', hcv, hrd, hrun, hret⟩ :=
    (sumcheck_round5_iff rd _ _).mp c10
  simp only [List.cons.injEq] at hret
  obtain ⟨e16, e17, e18, e19, e20, -⟩ := hret
  have hq : σ (.n 9) = σ (.n 2) * (σ (.n 3) * σ (.n 0)) ^ 4 := by
    rw [a9, a8, a7, a6]; ring
  rw [hq] at l10 l11 l12 l13 l16 l17 l18 l19
  rw [a14] at l15
  rw [a21] at l20
  refine ⟨⟨cv, σ (.n 12), σ (.n 13), σ (.n 15), [c1, c2, c3, c4], claim', r, cv', ?_, ?_, l12, l13,
    l15, rfl, hrd, hrun, by rwa [e20] at l20, by rwa [e16] at l16, by rwa [e17] at l17,
    by rw [← e18]; exact l18, by rwa [e19] at l19⟩, fun hne => ?_⟩
  · have e10 : σ (.n 10) = (digestScalars cv).1 := congrArg Prod.fst hcv
    rw [← e10]; exact l10
  · have e11 : σ (.n 11) = (digestScalars cv).2 := congrArg Prod.snd hcv
    rw [← e11]; exact l11
  · have := hc (by rwa [a24, a23, a22])
    rwa [a26, a25] at this

/-! ## A layer's rounds -/

theorem gkrRound_succ {rd : Reader} {rounds pos prow nrow : E} {r : ℕ}
    (h : GkrRound rd rounds pos prow nrow (gen ^ (r + 1))) :
    GkrRound rd rounds (pos * gen) (prow * gen) (nrow * gen) (gen ^ r) := by
  unfold GkrRound at h ⊢
  rwa [show pos * gen ^ (r + 1) = pos * gen * gen ^ r by ring,
    show prow * gen ^ (r + 1) = prow * gen * gen ^ r by ring,
    show nrow * gen ^ (r + 1) = nrow * gen * gen ^ r by ring] at h

theorem gkrRound_zero {rd : Reader} {rounds pos prow nrow : E}
    (h : GkrRound rd rounds pos prow nrow (gen ^ 0)) : GkrRound rd rounds pos prow nrow 1 := by
  rwa [pow_zero] at h

theorem rounds_shift (rounds pos : E) (k : ℕ) :
    rounds * (pos * gen ^ k) ^ 4 = rounds * pos ^ 4 * gen ^ (4 * k) := by
  rw [mul_pow, ← pow_mul, mul_assoc, Nat.mul_comm k 4]

/-- **A layer's `L` rounds** from the slot at `rounds·pos⁴` (the state of `cv0`, the cursor, the
claim): the words `ws` at the cursor run the sumcheck over `pt` (`point_row`) to the challenges
`chs` (at `nextrow[g²..]`) and the claim `cl`, and the slot `L` rounds on holds the final state,
the cursor `4L` words on and `cl`. -/
theorem gkr_rounds {rd : Reader} {rounds : E} : ∀ (L : ℕ) (pos prow nrow : E) (cv0 : Digest)
    (cur claim0 : E) (pt : List E), (∀ r < L, GkrRound rd rounds pos prow nrow (gen ^ r)) →
    pt.length = L → ReadsAt rd prow pt →
    LoadHolds rd (rounds * pos ^ 4) 0 (digestScalars cv0).1 →
    LoadHolds rd (rounds * pos ^ 4) 1 (digestScalars cv0).2 →
    LoadHolds rd (rounds * pos ^ 4) 2 cur → LoadHolds rd (rounds * pos ^ 4) 3 claim0 →
    ∃ (ws chs : List E) (cl : E) (cvS : Digest), ws.length = 4 * L ∧ ReadsAt rd cur ws ∧
      chs.length = L ∧ ReadsAt rd (nrow * gen ^ 2) chs ∧
      RunsTo (sumcheck claim0 5 (pt.map some)) cv0 ws (chs, cl) cvS ∧
      LoadHolds rd (rounds * pos ^ 4) (4 * L) (digestScalars cvS).1 ∧
      LoadHolds rd (rounds * pos ^ 4) (4 * L + 1) (digestScalars cvS).2 ∧
      LoadHolds rd (rounds * pos ^ 4) (4 * L + 2) (cur * gen ^ (4 * L)) ∧
      LoadHolds rd (rounds * pos ^ 4) (4 * L + 3) cl := by
  intro L
  induction L with
  | zero =>
    intro pos prow nrow cv0 cur claim0 pt _ hl _ h0 h1 h2 h3
    rw [List.length_eq_zero_iff] at hl
    subst hl
    refine ⟨[], [], claim0, cv0, rfl, readsAt_nil _ _, rfl, readsAt_nil _ _, runsTo_ret _ _, h0, h1,
      ?_, h3⟩
    rw [Nat.mul_zero, pow_zero, mul_one]; exact h2
  | succ L ih =>
    intro pos prow nrow cv0 cur claim0 pt hR hl hpt h0 h1 h2 h3
    obtain ⟨p0, pt', rfl⟩ : ∃ p0 pt', pt = p0 :: pt' := by
      cases pt with
      | nil => simp at hl
      | cons p0 pt' => exact ⟨p0, pt', rfl⟩
    obtain ⟨cv, cur', claim', e, ws0, claim'', rk, cv', i0, i1, i2, i3, he, hwl, hws, hrun, hrk,
      o4, o5, o6, o7⟩ := gkrRound_zero (hR 0 (by omega))
    simp only [mul_one] at i0 i1 i2 i3 he hrk o4 o5 o6 o7
    have ecv : cv0 = cv := digestScalars_injective (Prod.ext (loadHolds_unique h0 i0)
      (loadHolds_unique h1 i1))
    have ecur : cur = cur' := loadHolds_unique h2 i2
    have ecl : claim0 = claim' := loadHolds_unique h3 i3
    have ee : p0 = e := loadHolds_unique (hpt 0 (by simp)) he
    subst ecv ecur ecl ee
    have hsh : ∀ k w, LoadHolds rd (rounds * (pos * gen) ^ 4) k w ↔
        LoadHolds rd (rounds * pos ^ 4) (4 + k) w := fun k w => by
      rw [show rounds * (pos * gen) ^ 4 = rounds * pos ^ 4 * gen ^ 4 by ring,
        loadHolds_gen_pow_mul]
    have hpt' : ReadsAt rd (prow * gen) pt' := by
      intro k hk
      have := hpt (k + 1) (by simp; omega)
      rw [← pow_one gen, loadHolds_gen_pow_mul, Nat.add_comm]; exact this
    obtain ⟨ws', chs', cl, cvS, hwl', hws', hcl', hch', hrun', t0, t1, t2, t3⟩ :=
      ih (pos * gen) (prow * gen) (nrow * gen) cv' (cur * gen ^ 4) claim'' pt'
        (fun r hr => gkrRound_succ (hR (r + 1) (by omega))) (by simpa using hl) hpt'
        ((hsh 0 _).mpr o4) ((hsh 1 _).mpr o5) ((hsh 2 _).mpr o6) ((hsh 3 _).mpr o7)
    rw [hsh] at t0 t1 t2 t3
    refine ⟨ws0 ++ ws', rk :: chs', cl, cvS, by simp [hwl, hwl']; ring,
      readsAt_append_pow hws (by rw [hwl]; exact hws'), by simp [hcl'], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      cases k with
      | zero => rw [loadHolds_gen_pow_mul]; exact hrk
      | succ k =>
        have := hch' k (by simp at hk; omega)
        rw [show nrow * gen * gen ^ 2 = nrow * gen ^ 2 * gen ^ 1 by ring, loadHolds_gen_pow_mul,
          Nat.add_comm] at this
        exact this
    · exact RunsTo.sumcheck_cons hrun hrun'
    · rw [show 4 + 4 * L = 4 * (L + 1) by ring] at t0; exact t0
    · rw [show 4 + (4 * L + 1) = 4 * (L + 1) + 1 by ring] at t1; exact t1
    · rw [show 4 + (4 * L + 2) = 4 * (L + 1) + 2 by ring, mul_assoc, ← pow_add,
        show 4 + 4 * L = 4 * (L + 1) by ring] at t2
      exact t2
    · rw [show 4 + (4 * L + 3) = 4 * (L + 1) + 3 by ring] at t3; exact t3

end
end LeanVM.Guest.B1.VerifySub
