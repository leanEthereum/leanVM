/-
  LeanVM.Guest.CoreMode.Fn.link_rounds_last.SoundA

  `link_rounds_last`'s arms of `k > 0` rounds at the honest instances of b2c's aligned tree: their record's cursor lies
  `4W·h` words past `link_rounds`' `cursor`, `k = r` rounds left of `count = 4h + r` (`lrl_stOk`, the cursor-run
  family's `StLoopOkA`).
-/

module

public import LeanVM.Guest.CoreMode.Fn.link_rounds.LrChain
public import LeanVM.Guest.CoreMode.Fn.link_rounds_last.Data
public import LeanVM.Guest.EndExecAFrSize
public import LeanVM.Guest.CoreMode.Fn.link_rounds.Fam

/-!
# `link_rounds_last` down the honest tree

`link_rounds__L{t}_L{b}` splits `count_g = g^(4h + r)`, runs its loop over `h` iterations from the record at `recs`,
each storing the next record `7` cells on with the cursor `4W` words further (`lrLoop_cur`, by the loop's relation),
then dispatches on `g^r` to `link_rounds_last__L{t}_L{b}_L{r}` on the record at `recs·g^(7h)` (`lrMain_lastCall`: the
dispatch's call event is the arm the selector names). So that arm's cursor, the word at its record's cell `5`, is
`cursor·g^(W·4h)` with `4h + r = count` (`LrlQ`, `lrlQ_allA`): a cursor-run arm (`lrl_stOk`).
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

public section

/-- **The loop's records' cursors**: entered at `g^0` with end `g^q`, from the record at `recs` holding the cursor `c`
at cell `5`, the record at `recs·g^(7q)` holds `c·g^(4W·q)` there. -/
theorem lrLoop_cur {rd : Reader} {nt bits : ℕ} (hW : EndExec.lrW nt bits < 64) {name : String} {fn : Fn}
    (hf : coreProgram.find? name = some fn) (hparams : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4])
    (hbody : fn.body = lrLoopBody nt bits name) {q : ℕ} (hq1 : 1 ≤ q) (hq : q < ordG) (recs point tabs c : E)
    (h : coreProgram.Rel rd name [gen ^ 0, gen ^ q, recs, point, tabs] []) (h5 : LoadHolds rd recs 5 c) :
    LoadHolds rd (recs * gen ^ (7 * q)) 5 (c * gen ^ (4 * EndExec.lrW nt bits * q)) := by
  have hstep : ∀ d x, coreProgram.relN rd (d + 1) name (x :: [gen ^ q, recs, point, tabs]) [] ↔
      AtomsBody rd fn.params (lrLoopA nt bits) (x :: gen ^ q :: [recs, point, tabs]) ∧
        IsInK (x * gen + gen ^ q) ∧
        (x * gen + gen ^ q ≠ 0 → coreProgram.relN rd d name (x * gen :: [gen ^ q, recs, point, tabs]) []) := by
    intro d x
    refine loop_step_atoms hf (by rw [hbody, lrLoopBody_eq]) (lrLoopA_atoms nt bits) (fun σ hp hall ↦ ?_) d
    rw [hparams] at hp
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
    obtain ⟨h0, h1, h2, h3, h4, -⟩ := hp
    set V := (lrLoopRounds nt bits).2.2.2.2.1
    have mem : ∀ a ∈ [Atom.const (.n V) (word 2 0), .mul (.n (V + 1)) (.n 0) (.n V),
        .add (.n (V + 2)) (.n (V + 1)) (.n 1), .const (.n (V + 3)) (word 2 0),
        .mul (.n (V + 4)) (.n 0) (.n (V + 3))], a.Holds rd σ := fun a ha ↦ hall a (by
      unfold lrLoopA
      refine List.mem_append_right _ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp [V])
    have a0 := mem (.const (.n V) (word 2 0)) (by simp)
    have a1 := mem (.mul (.n (V + 1)) (.n 0) (.n V)) (by simp)
    have a2 := mem (.add (.n (V + 2)) (.n (V + 1)) (.n 1)) (by simp)
    have a3 := mem (.const (.n (V + 3)) (word 2 0)) (by simp)
    have a4 := mem (.mul (.n (V + 4)) (.n 0) (.n (V + 3))) (by simp)
    simp only [Atom.Holds, word_gen] at a0 a1 a2 a3 a4
    refine ⟨by rw [a2, a1, a0, h0, h1], ?_⟩
    simp only [List.map_cons, List.map_nil, a4, a3, h0, h1, h2, h3, h4]
  have hl := (loop_iff (P := coreProgram) (f := name) (B := fun x ↦
    AtomsBody rd fn.params (lrLoopA nt bits) (x :: gen ^ q :: [recs, point, tabs])) hstep 0).mp h
  obtain ⟨m, hm0, hN, hfirst, hall⟩ := hl
  have hmq : m = q := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hm' : m < ordG := by omega
      exact absurd (gen_pow_inj (by unfold ordG at hm'; omega) (by unfold ordG at hq; omega) hN) (by omega)
    · exact hfirst q (by omega) hgt rfl
  have key : ∀ j ≤ q, LoadHolds rd (recs * gen ^ (7 * j)) 5 (c * gen ^ (4 * EndExec.lrW nt bits * j)) := by
    intro j hj
    induction j with
    | zero => simpa using h5
    | succ j ih =>
      obtain ⟨σ, hp, hall'⟩ := hall j (by omega) (by omega)
      rw [hparams] at hp
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
      obtain ⟨h0, -, h2, -, -, -⟩ := hp
      obtain ⟨h9, l5, l12⟩ := EndExec.lrIter hW hall'
      rw [h9, h0, h2, ← pow_mul, mul_comm j 7] at l5 l12
      have h18 := loadHolds_unique l5 (ih (by omega))
      rw [h18, loadHolds_mul_gen_pow, mul_assoc, ← pow_add] at l12
      rw [loadHolds_mul_gen_pow, show 7 * (j + 1) + 5 = 7 * j + 12 by ring,
        show 4 * EndExec.lrW nt bits * (j + 1) = 4 * EndExec.lrW nt bits * j + 4 * EndExec.lrW nt bits by ring]
      exact l12
  exact key q le_rfl

end

end LeanVM.Guest.B1.Link

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf FrameHolds fsN fn_of_idx cellJ namedOf kidHdr siteOf)
open LeanVM.Guest.Value (gen_pow_eq_ofK gen_pow_inj)
open LeanVM.Guest.B1.Digest (find_of_idx)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

/-- **A returning walk's calls come from its top-level statements**: each call event is one of a statement's own. -/
theorem walk_calls_top {σ : Val} : ∀ {ss : List Stmt} {es : List Ev} {vs : List V}, walk σ ss = .ret es vs →
    ∀ c ∈ calls es, ∃ s ∈ ss, ∃ es1, (walk1 σ s = .fall es1 ∨ ∃ vs1, walk1 σ s = .ret es1 vs1) ∧ c ∈ calls es1
  | [], _, _, h => by simp [walk] at h
  | s :: ss, es, vs, h => by
    intro c hc
    simp only [walk] at h
    cases h1 : walk1 σ s with
    | fall es1 =>
      rw [h1] at h
      simp only [Out.seq] at h
      cases h2 : walk σ ss with
      | fall _ => rw [h2] at h; simp [Out.pre] at h
      | stuck => rw [h2] at h; simp [Out.pre] at h
      | ret es2 vs2 =>
        rw [h2] at h
        simp only [Out.pre, Out.ret.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rw [calls, List.filterMap_append] at hc
        rcases List.mem_append.mp hc with hc | hc
        · exact ⟨s, List.mem_cons_self, es1, Or.inl h1, hc⟩
        · obtain ⟨s', hs', es1', h1', hc'⟩ := walk_calls_top h2 c hc
          exact ⟨s', List.mem_cons_of_mem _ hs', es1', h1', hc'⟩
    | ret es1 vs1 =>
      rw [h1] at h
      simp only [Out.seq, Out.ret.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨s, List.mem_cons_self, es1, Or.inr ⟨vs1, h1⟩, hc⟩
    | stuck => rw [h1] at h; simp [Out.seq] at h

/-- `link_rounds`' body's statements: atoms, its loop's conditional call, its last arms' dispatch, its return. -/
theorem lrMain_stmts (loop : String) (lasts : List String) : ∀ s ∈ B1.Link.lrMainBody loop lasts,
    (∃ a, s = .atom a) ∨ s = .callIf (.n 55) loop [.n 56, .n 43, .n 53, .n 7, .n 9] ∨
      s = .dispatch (.n 24) lasts [.n 61, .n 63, .n 66, .n 9] [.n 67] ∨ ∃ vs, s = .ret vs := by
  simp [B1.Link.lrMainBody]

/-- **`link_rounds`' call of a last arm** is its dispatch's: on the record and its cursor's arguments, the arm the
selector `g^i` names. -/
theorem lrMain_lastCall {loop : String} {lasts : List String} (hl : loop ∉ lasts) {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ (B1.Link.lrMainBody loop lasts) = .ret es vs) {c : Call} (hc : c ∈ calls es)
    (hf : c.f ∈ lasts) :
    c.args = [.n 61, .n 63, .n 66, .n 9] ∧ ∃ i, lasts[i]? = some c.f ∧ σ (.n 24) = ofK (addressOfIndex i) := by
  obtain ⟨s, hs, es1, hw1, hc1⟩ := walk_calls_top hw c hc
  rcases lrMain_stmts loop lasts s hs with ⟨a, rfl⟩ | rfl | rfl | ⟨vs', rfl⟩
  · rcases hw1 with h | ⟨_, h⟩ <;> simp only [walk1, Out.fall.injEq, reduceCtorEq] at h
    subst h
    simp [calls, Ev.call?] at hc1
  · rcases hw1 with h | ⟨_, h⟩ <;> simp only [walk1, Out.fall.injEq, reduceCtorEq] at h
    subst h
    split_ifs at hc1 <;> simp [calls, Ev.call?] at hc1 <;> (subst hc1; exact absurd hf hl)
  · have hpk : ∀ (o : Out), o = pick σ (.n 24) [.n 61, .n 63, .n 66, .n 9] [.n 67] 0 lasts →
        (o = .fall es1 ∨ ∃ vs1, o = .ret es1 vs1) → c ∈ calls es1 → c ∈ calls o.evs := by
      rintro o - (rfl | ⟨vs1, rfl⟩) h <;> exact h
    have hm := hpk _ rfl (by simpa only [walk1] using hw1) hc1
    obtain ⟨ha, -, -, i, hi, hσ⟩ := pick_callOf lasts 0 c hm
    exact ⟨ha, i, hi, by rw [hσ, Nat.zero_add]⟩
  · rcases hw1 with h | ⟨_, h⟩ <;> simp only [walk1, Out.ret.injEq, reduceCtorEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [calls] at hc1

/-- **`link_rounds`' specializations with their last arms**: `n_tail`, `bits`, the function, its loop, its arms. -/
def lrlSpecs : List (ℕ × ℕ × String × String × List String) :=
  [(1, 0, name% «link_rounds__L1_L0», name% «link_rounds__L1_L0_loop0»,
      [name% «link_rounds_last__L1_L0_L0», name% «link_rounds_last__L1_L0_L1», name% «link_rounds_last__L1_L0_L2»,
        name% «link_rounds_last__L1_L0_L3»]),
    (6, 0, name% «link_rounds__L6_L0», name% «link_rounds__L6_L0_loop0»,
      [name% «link_rounds_last__L6_L0_L0», name% «link_rounds_last__L6_L0_L1», name% «link_rounds_last__L6_L0_L2»,
        name% «link_rounds_last__L6_L0_L3»]),
    (7, 0, name% «link_rounds__L7_L0», name% «link_rounds__L7_L0_loop0»,
      [name% «link_rounds_last__L7_L0_L0», name% «link_rounds_last__L7_L0_L1», name% «link_rounds_last__L7_L0_L2»,
        name% «link_rounds_last__L7_L0_L3»]),
    (8, 1, name% «link_rounds__L8_L1», name% «link_rounds__L8_L1_loop0»,
      [name% «link_rounds_last__L8_L1_L0», name% «link_rounds_last__L8_L1_L1», name% «link_rounds_last__L8_L1_L2»,
        name% «link_rounds_last__L8_L1_L3»]),
    (9, 1, name% «link_rounds__L9_L1», name% «link_rounds__L9_L1_loop0»,
      [name% «link_rounds_last__L9_L1_L0», name% «link_rounds_last__L9_L1_L1», name% «link_rounds_last__L9_L1_L2»,
        name% «link_rounds_last__L9_L1_L3»]),
    (10, 1, name% «link_rounds__L10_L1», name% «link_rounds__L10_L1_loop0»,
      [name% «link_rounds_last__L10_L1_L0», name% «link_rounds_last__L10_L1_L1», name% «link_rounds_last__L10_L1_L2»,
        name% «link_rounds_last__L10_L1_L3»])]

/-- **What a specialization's last arms are**: its body's dispatch's, distinct, not its loop nor `main`, each of `k`
rounds of the template `lrLastBody`, not a loop, called by the specialization only, on the record and cursor's
arguments at its sites. -/
structure LrlSpec (nt bits : ℕ) (main loop : String) (lasts : List String) : Prop where
  spec : (nt, bits, main, loop) ∈ lrSpecs
  body : (coreProgram.find? main).map Fn.body = some (B1.Link.lrMainBody loop lasts)
  nodup : lasts.Nodup
  loop_not : loop ∉ lasts
  len : lasts.length = 4
  not_main : "main" ∉ lasts
  lastF : ∀ k (hk : k < lasts.length), ∃ fl : Fn, coreProgram.find? lasts[k] = some fl ∧
    fl.params = [.n 0, .n 1, .n 2, .n 3] ∧ fl.body = B1.Link.lrLastBody nt bits k ∧ fl.loop = false
  callers : ∀ g ∈ lasts.drop 1, (g, main) ∈ Res.termCallers
  sites : ∀ (fM : Fn) jm, coreProgram.find? main = some fM → idxOf main = some jm →
    Res.sitesB (fun g args rets ↦ !(lasts.contains g) ||
      (args == [.n 61, .n 63, .n 66, .n 9] && Res.siteB jm args rets)) fM.body = true

end

public section

set_option maxRecDepth 100000 in
theorem lrlSpec_L1_L0 : LrlSpec 1 0 name% «link_rounds__L1_L0» name% «link_rounds__L1_L0_loop0»
    [name% «link_rounds_last__L1_L0_L0», name% «link_rounds_last__L1_L0_L1», name% «link_rounds_last__L1_L0_L2»,
      name% «link_rounds_last__L1_L0_L3»] := by
  refine ⟨by decide, by rw [coreProgram_find?_at (j := idx% «link_rounds__L1_L0») rfl, Option.map_some,
    B1.Link.lrMain_L1_L0_body], by decide, by decide, rfl, by decide, ?_, by decide +kernel, ?_⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L1_L0_L0») rfl, rfl, B1.Link.lrl_L1_L0_L0_body,
        by decide +kernel⟩
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L1_L0_L1») rfl, rfl, B1.Link.lrl_L1_L0_L1_body,
        by decide +kernel⟩
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L1_L0_L2») rfl, rfl, B1.Link.lrl_L1_L0_L2_body,
        by decide +kernel⟩
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L1_L0_L3») rfl, rfl, B1.Link.lrl_L1_L0_L3_body,
        by decide +kernel⟩
  · intro fM jm hf hj
    obtain rfl : fM = fn% «link_rounds__L1_L0» :=
      Option.some.inj (hf.symm.trans (coreProgram_find?_at (j := idx% «link_rounds__L1_L0») rfl))
    obtain rfl : jm = fn_idx% «link_rounds__L1_L0» := Option.some.inj (hj.symm.trans (by decide +kernel))
    decide +kernel

set_option maxRecDepth 100000 in
theorem lrlSpec_L6_L0 : LrlSpec 6 0 name% «link_rounds__L6_L0» name% «link_rounds__L6_L0_loop0»
    [name% «link_rounds_last__L6_L0_L0», name% «link_rounds_last__L6_L0_L1», name% «link_rounds_last__L6_L0_L2»,
      name% «link_rounds_last__L6_L0_L3»] := by
  refine ⟨by decide, by rw [coreProgram_find?_at (j := idx% «link_rounds__L6_L0») rfl, Option.map_some,
    B1.Link.lrMain_L6_L0_body], by decide, by decide, rfl, by decide, ?_, by decide +kernel, ?_⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L6_L0_L0») rfl, rfl, B1.Link.lrl_L6_L0_L0_body,
        by decide +kernel⟩
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L6_L0_L1») rfl, rfl, B1.Link.lrl_L6_L0_L1_body,
        by decide +kernel⟩
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L6_L0_L2») rfl, rfl, B1.Link.lrl_L6_L0_L2_body,
        by decide +kernel⟩
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L6_L0_L3») rfl, rfl, B1.Link.lrl_L6_L0_L3_body,
        by decide +kernel⟩
  · intro fM jm hf hj
    obtain rfl : fM = fn% «link_rounds__L6_L0» :=
      Option.some.inj (hf.symm.trans (coreProgram_find?_at (j := idx% «link_rounds__L6_L0») rfl))
    obtain rfl : jm = fn_idx% «link_rounds__L6_L0» := Option.some.inj (hj.symm.trans (by decide +kernel))
    decide +kernel

set_option maxRecDepth 100000 in
theorem lrlSpec_L7_L0 : LrlSpec 7 0 name% «link_rounds__L7_L0» name% «link_rounds__L7_L0_loop0»
    [name% «link_rounds_last__L7_L0_L0», name% «link_rounds_last__L7_L0_L1», name% «link_rounds_last__L7_L0_L2»,
      name% «link_rounds_last__L7_L0_L3»] := by
  refine ⟨by decide, by rw [coreProgram_find?_at (j := idx% «link_rounds__L7_L0») rfl, Option.map_some,
    B1.Link.lrMain_L7_L0_body], by decide, by decide, rfl, by decide, ?_, by decide +kernel, ?_⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L7_L0_L0») rfl, rfl, B1.Link.lrl_L7_L0_L0_body,
        by decide +kernel⟩
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L7_L0_L1») rfl, rfl, B1.Link.lrl_L7_L0_L1_body,
        by decide +kernel⟩
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L7_L0_L2») rfl, rfl, B1.Link.lrl_L7_L0_L2_body,
        by decide +kernel⟩
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L7_L0_L3») rfl, rfl, B1.Link.lrl_L7_L0_L3_body,
        by decide +kernel⟩
  · intro fM jm hf hj
    obtain rfl : fM = fn% «link_rounds__L7_L0» :=
      Option.some.inj (hf.symm.trans (coreProgram_find?_at (j := idx% «link_rounds__L7_L0») rfl))
    obtain rfl : jm = fn_idx% «link_rounds__L7_L0» := Option.some.inj (hj.symm.trans (by decide +kernel))
    decide +kernel

set_option maxRecDepth 100000 in
theorem lrlSpec_L8_L1 : LrlSpec 8 1 name% «link_rounds__L8_L1» name% «link_rounds__L8_L1_loop0»
    [name% «link_rounds_last__L8_L1_L0», name% «link_rounds_last__L8_L1_L1», name% «link_rounds_last__L8_L1_L2»,
      name% «link_rounds_last__L8_L1_L3»] := by
  refine ⟨by decide, by rw [coreProgram_find?_at (j := idx% «link_rounds__L8_L1») rfl, Option.map_some,
    B1.Link.lrMain_L8_L1_body], by decide, by decide, rfl, by decide, ?_, by decide +kernel, ?_⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L8_L1_L0») rfl, rfl, B1.Link.lrl_L8_L1_L0_body,
        by decide +kernel⟩
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L8_L1_L1») rfl, rfl, B1.Link.lrl_L8_L1_L1_body,
        by decide +kernel⟩
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L8_L1_L2») rfl, rfl, B1.Link.lrl_L8_L1_L2_body,
        by decide +kernel⟩
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L8_L1_L3») rfl, rfl, B1.Link.lrl_L8_L1_L3_body,
        by decide +kernel⟩
  · intro fM jm hf hj
    obtain rfl : fM = fn% «link_rounds__L8_L1» :=
      Option.some.inj (hf.symm.trans (coreProgram_find?_at (j := idx% «link_rounds__L8_L1») rfl))
    obtain rfl : jm = fn_idx% «link_rounds__L8_L1» := Option.some.inj (hj.symm.trans (by decide +kernel))
    decide +kernel

set_option maxRecDepth 100000 in
theorem lrlSpec_L9_L1 : LrlSpec 9 1 name% «link_rounds__L9_L1» name% «link_rounds__L9_L1_loop0»
    [name% «link_rounds_last__L9_L1_L0», name% «link_rounds_last__L9_L1_L1», name% «link_rounds_last__L9_L1_L2»,
      name% «link_rounds_last__L9_L1_L3»] := by
  refine ⟨by decide, by rw [coreProgram_find?_at (j := idx% «link_rounds__L9_L1») rfl, Option.map_some,
    B1.Link.lrMain_L9_L1_body], by decide, by decide, rfl, by decide, ?_, by decide +kernel, ?_⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L9_L1_L0») rfl, rfl, B1.Link.lrl_L9_L1_L0_body,
        by decide +kernel⟩
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L9_L1_L1») rfl, rfl, B1.Link.lrl_L9_L1_L1_body,
        by decide +kernel⟩
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L9_L1_L2») rfl, rfl, B1.Link.lrl_L9_L1_L2_body,
        by decide +kernel⟩
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L9_L1_L3») rfl, rfl, B1.Link.lrl_L9_L1_L3_body,
        by decide +kernel⟩
  · intro fM jm hf hj
    obtain rfl : fM = fn% «link_rounds__L9_L1» :=
      Option.some.inj (hf.symm.trans (coreProgram_find?_at (j := idx% «link_rounds__L9_L1») rfl))
    obtain rfl : jm = fn_idx% «link_rounds__L9_L1» := Option.some.inj (hj.symm.trans (by decide +kernel))
    decide +kernel

set_option maxRecDepth 100000 in
theorem lrlSpec_L10_L1 : LrlSpec 10 1 name% «link_rounds__L10_L1» name% «link_rounds__L10_L1_loop0»
    [name% «link_rounds_last__L10_L1_L0», name% «link_rounds_last__L10_L1_L1», name% «link_rounds_last__L10_L1_L2»,
      name% «link_rounds_last__L10_L1_L3»] := by
  refine ⟨by decide, by rw [coreProgram_find?_at (j := idx% «link_rounds__L10_L1») rfl, Option.map_some,
    B1.Link.lrMain_L10_L1_body], by decide, by decide, rfl, by decide, ?_, by decide +kernel, ?_⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L10_L1_L0») rfl, rfl, B1.Link.lrl_L10_L1_L0_body,
        by decide +kernel⟩
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L10_L1_L1») rfl, rfl, B1.Link.lrl_L10_L1_L1_body,
        by decide +kernel⟩
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L10_L1_L2») rfl, rfl, B1.Link.lrl_L10_L1_L2_body,
        by decide +kernel⟩
    · exact ⟨_, coreProgram_find?_at (j := idx% «link_rounds_last__L10_L1_L3») rfl, rfl, B1.Link.lrl_L10_L1_L3_body,
        by decide +kernel⟩
  · intro fM jm hf hj
    obtain rfl : fM = fn% «link_rounds__L10_L1» :=
      Option.some.inj (hf.symm.trans (coreProgram_find?_at (j := idx% «link_rounds__L10_L1») rfl))
    obtain rfl : jm = fn_idx% «link_rounds__L10_L1» := Option.some.inj (hj.symm.trans (by decide +kernel))
    decide +kernel

theorem lrlSpec_all {nt bits : ℕ} {main loop : String} {lasts : List String}
    (h : (nt, bits, main, loop, lasts) ∈ lrlSpecs) : LrlSpec nt bits main loop lasts := by
  simp only [lrlSpecs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact lrlSpec_L1_L0
  · exact lrlSpec_L6_L0
  · exact lrlSpec_L7_L0
  · exact lrlSpec_L8_L1
  · exact lrlSpec_L9_L1
  · exact lrlSpec_L10_L1

end

public section

/-- `link_rounds`' specializations with a returned-cursor equation are `lrlSpecs`' (`retSpecs`), `W` their round's
words. -/
theorem retSpecs_lrl {p : String × ℕ} (hp : p ∈ CoreMode.Own.link_rounds.retSpecs) :
    ∃ nt bits loop lasts, (nt, bits, p.1, loop, lasts) ∈ lrlSpecs ∧ lrW nt bits = p.2 := by
  simp only [CoreMode.Own.link_rounds.retSpecs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, name% «link_rounds__L1_L0_loop0», [name% «link_rounds_last__L1_L0_L0», name% «link_rounds_last__L1_L0_L1», name% «link_rounds_last__L1_L0_L2», name% «link_rounds_last__L1_L0_L3»],
      by unfold lrlSpecs; simp, rfl⟩
  · exact ⟨6, 0, name% «link_rounds__L6_L0_loop0», [name% «link_rounds_last__L6_L0_L0», name% «link_rounds_last__L6_L0_L1», name% «link_rounds_last__L6_L0_L2», name% «link_rounds_last__L6_L0_L3»],
      by unfold lrlSpecs; simp, rfl⟩
  · exact ⟨7, 0, name% «link_rounds__L7_L0_loop0», [name% «link_rounds_last__L7_L0_L0», name% «link_rounds_last__L7_L0_L1», name% «link_rounds_last__L7_L0_L2», name% «link_rounds_last__L7_L0_L3»],
      by unfold lrlSpecs; simp, rfl⟩
  · exact ⟨8, 1, name% «link_rounds__L8_L1_loop0», [name% «link_rounds_last__L8_L1_L0», name% «link_rounds_last__L8_L1_L1», name% «link_rounds_last__L8_L1_L2», name% «link_rounds_last__L8_L1_L3»],
      by unfold lrlSpecs; simp, rfl⟩
  · exact ⟨9, 1, name% «link_rounds__L9_L1_loop0», [name% «link_rounds_last__L9_L1_L0», name% «link_rounds_last__L9_L1_L1», name% «link_rounds_last__L9_L1_L2», name% «link_rounds_last__L9_L1_L3»],
      by unfold lrlSpecs; simp, rfl⟩
  · exact ⟨10, 1, name% «link_rounds__L10_L1_loop0», [name% «link_rounds_last__L10_L1_L0», name% «link_rounds_last__L10_L1_L1», name% «link_rounds_last__L10_L1_L2», name% «link_rounds_last__L10_L1_L3»],
      by unfold lrlSpecs; simp, rfl⟩

end

@[expose] public section

/-- **`link_rounds`' last arms at an instance**: for arm `k > 0` of a specialization, the header names `link_rounds`'
frame `a`, its cell `10` holding `g^n`, `n < 64`, the arm's cursor (value `9`) the word at the frame's cell `7` times
`g^(W·m)`, `m + k ≤ n`. -/
def LrlQ (r : Ref) (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids → ∀ nt bits main loop lasts, (nt, bits, main, loop, lasts) ∈ lrlSpecs →
    ∀ k, 1 ≤ k → lasts[k]? = some f →
    ∃ a m n, J.hdr.2 = ofK (addressOfIndex a) ∧ a + 7 < maxCells ∧ a + 10 < maxCells ∧
      σ (.n 9) = refMem r.img (a + 7) * gen ^ (lrW nt bits * m) ∧ refMem r.img (a + 10) = gen ^ n ∧ n < 64 ∧
      m + k ≤ n

end

public section

variable {al : String → Bool} {D : Ref → RefD} {r : Ref}

set_option maxHeartbeats 1000000 in
/-- **`LrlQ` passes down a call**: from `link_rounds`' split count, its loop's records and its dispatch. -/
theorem lrlQ_stepA (hR : RefH (layB al) (D r) r) (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (instsR al D r) (LrlQ r) := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ hhdr hname hval hph _
    f σ bufs kids hJt nt bits main loop lasts hmem k hk1 hkf
  have hS := lrlSpec_all hmem
  obtain ⟨hW, ⟨fL, hfL, -, -, hparL, hbodyL⟩, ⟨fM, jm, lasts', hfM, hjm, -, hloopM, hm5, hm8, hc5, hc8, hfs, -⟩, -⟩ :=
    lrSpec_all hS.spec
  have hkl : k < lasts.length := by
    rcases Nat.lt_or_ge k lasts.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hkf; cases hkf
  have hfk : lasts[k] = f := Option.some.inj ((List.getElem?_eq_getElem hkl).symm.trans hkf)
  obtain ⟨fl, hfl, hparl, hbodyl, hloopl⟩ := hS.lastF k hkl
  rw [hfk] at hfl
  have hcf : c.f = f := by rw [← hname, hJt]; rfl
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  have hnI : fnI.name = fI := find_name' hfI
  have hcaller : fI = main ∨ (fI = f ∧ fnI.loop = true) := by
    have hmemC : (f, main) ∈ Res.termCallers := hS.callers f (by
      have h2 : (lasts.drop 1)[k - 1]? = some f := by
        rw [List.getElem?_drop, show 1 + (k - 1) = k by omega]; exact hkf
      exact List.mem_of_getElem? h2)
    have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI))
      hw c hc) _ hmemC
    rw [hcf] at hcal
    simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
    rcases hcal with h | ⟨h, hl⟩
    · exact Or.inl (by rw [← hnI, h])
    · exact Or.inr ⟨by rw [← hnI, h], hl⟩
  rcases hcaller with rfl | ⟨rfl, hl'⟩
  swap
  · obtain rfl : fnI = fl := Option.some.inj (hfI.symm.trans hfl)
    rw [hloopl] at hl'; cases hl'
  obtain rfl : fnI = fM := Option.some.inj (hfI.symm.trans hfM)
  have hbodyM : fnI.body = B1.Link.lrMainBody loop lasts := by
    have := hS.body
    rw [hfM, Option.map_some] at this
    exact Option.some.inj this
  obtain ⟨i', hji, hi', -, hf', hc', -⟩ := fn_of_idx hjm
  have hcj : coreOf jm = fnI := by rw [hc']; exact Option.some.inj (hf'.symm.trans hfI)
  -- the call is the dispatch's, at the arm the selector names
  have hfin : c.f ∈ lasts := by rw [hcf, ← hfk]; exact List.getElem_mem hkl
  rw [hbodyM] at hw
  obtain ⟨hargs, ii, hii, hσ24⟩ := lrMain_lastCall hS.loop_not hw hc hfin
  have hik : ii = k := by
    rw [hcf] at hii
    obtain ⟨h1, e1⟩ := List.getElem?_eq_some_iff.mp hii
    exact (List.Nodup.getElem_inj_iff hS.nodup).mp (e1.trans hfk.symm)
  subst hik
  have hs : (!(lasts.contains c.f) || (c.args == [.n 61, .n 63, .n 66, .n 9] && Res.siteB jm c.args c.rets)) =
      true := Res.calls_sites (hS.sites _ _ hfM hjm) (by rw [hbodyM]; exact hw) c hc
  have hcon : lasts.contains c.f = true := by simpa using hfin
  rw [hcon] at hs
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hs
  obtain ⟨-, hsb⟩ := hs
  -- the specialization's body
  obtain ⟨args, rets, hvI⟩ := inst_validA hR hI hIt
  obtain ⟨-, hbI⟩ := Res.holds_of_valid Res.fs_pos hvI hfI
  rw [hbodyM] at hbI
  simp only [B1.Link.lrMainBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    true_and] at hbI
  obtain ⟨b0, c16, c17, m18, a19, b1, c20, c21, m22, a23, m24, b2, c25, c26, m27, a28, b3, c29, c30,
    m31, a32, m33, b4, c34, c35, m36, a37, m38, b5, c39, c40, m41, a42, m43, m44, m45, m46, hassert,
    c47, m48, m49, m50, m51, m52, s0, s1, s2, s3, s4, s5, s6, c54, a55, c56, hK55, hcall, m57, m58, m59,
    m60, m61, -⟩ := hbI
  have w3 : word 3 0 = gen ^ 1 + 1 := B1.Link.word_two_pow_xor_one (a := 1) (by norm_num)
  have w5 : word 5 0 = gen ^ 2 + 1 := B1.Link.word_two_pow_xor_one (a := 2) (by norm_num)
  have w17 : word 17 0 = gen ^ 4 + 1 := B1.Link.word_two_pow_xor_one (a := 4) (by norm_num)
  have w257 : word 257 0 = gen ^ 8 + 1 := B1.Link.word_two_pow_xor_one (a := 8) (by norm_num)
  have hrg : σI (.n 24) = gen ^ (B1.Link.bv (σI (.n 10)) + 2 * B1.Link.bv (σI (.n 11))) := by
    rw [m24, a19, a23, m18, m22, c16, c17, c20, c21, w3, w5, B1.word_one, B1.Link.bit_factor b0,
      B1.Link.bit_factor b1, ← pow_add]
    simp only [B1.Link.bv, one_mul]
  have hqg : σI (.n 43) = gen ^ (B1.Link.bv (σI (.n 12)) + 2 * B1.Link.bv (σI (.n 13)) +
      4 * B1.Link.bv (σI (.n 14)) + 8 * B1.Link.bv (σI (.n 15))) := by
    rw [m43, m38, m33, a28, a32, a37, a42, m27, m31, m36, m41, c25, c26, c29, c30, c34, c35, c39, c40, w3, w5,
      w17, w257, B1.word_one, B1.Link.bit_factor b2, B1.Link.bit_factor b3, B1.Link.bit_factor b4,
      B1.Link.bit_factor b5, ← pow_add, ← pow_add, ← pow_add]
    simp only [B1.Link.bv, one_mul]
  set rv := B1.Link.bv (σI (.n 10)) + 2 * B1.Link.bv (σI (.n 11)) with hrv
  set qv := B1.Link.bv (σI (.n 12)) + 2 * B1.Link.bv (σI (.n 13)) + 4 * B1.Link.bv (σI (.n 14)) +
    8 * B1.Link.bv (σI (.n 15)) with hqv
  have hrv4 : rv < 4 := by
    have := B1.Link.bv_le (σI (.n 10)); have := B1.Link.bv_le (σI (.n 11)); omega
  have hqv16 : qv < 16 := by
    have := B1.Link.bv_le (σI (.n 12)); have := B1.Link.bv_le (σI (.n 13)); have := B1.Link.bv_le (σI (.n 14))
    have := B1.Link.bv_le (σI (.n 15)); omega
  have hcg : σI (.n 8) = gen ^ (4 * qv + rv) := by
    have : σI (.n 8) = σI (.n 46) := by linear_combination hassert.symm + σI (.n 8) * B1.Link.two_eq_zero_E
    rw [this, m46, m45, m44, hqg, hrg]
    ring
  have hkr : ii = rv := by
    have hlen := hS.len
    rw [hrg, ← gen_pow_eq_ofK] at hσ24
    exact (gen_pow_inj (by omega) (by omega) hσ24).symm
  -- the record the arm reads: the loop's last, or the first
  have hrec : LoadHolds r.img.read (σI (.n 53) * gen ^ (7 * qv)) 5 (σI (.n 5) * gen ^ (4 * lrW nt bits * qv)) := by
    rcases Nat.eq_zero_or_pos qv with h0 | hq1
    · rw [h0]; simpa using s5
    · have hq0 : σI (.n 55) ≠ 0 := by
        rw [a55, c54, B1.word_one, hqg]
        intro h0
        have : gen ^ qv = 1 := by linear_combination h0 - B1.Link.two_eq_zero_E
        rw [Value.gen_pow_eq_one_iff (by omega)] at this
        omega
      have hrel := (hcall hq0).rel
      rw [c56, B1.word_one, hqg, ← pow_zero gen] at hrel
      exact B1.Link.lrLoop_cur hW hfL hparL hbodyL hq1 (by unfold B1.ordG; omega) _ _ _ _ hrel s5
  have h61 : σI (.n 61) = σI (.n 53) * gen ^ (7 * qv) := by
    rw [m61, m60, m59, m58, m57, hqg]
    ring
  -- the arm's cursor
  obtain ⟨hpJ, hbJ⟩ := Res.holds_of_valid Res.fs_pos hJv hfl
  rw [hparl, hargs] at hpJ
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpJ
  obtain ⟨hp0, -⟩ := hpJ
  rw [hbodyl] at hbJ
  have hk0 : ii ≠ 0 := by omega
  simp only [B1.Link.lrLastBody, hk0, ↓reduceIte] at hbJ
  obtain ⟨-, -, -, -, -, l9, -⟩ := hbJ
  simp only [Atom.Holds] at l9
  rw [hp0, h61] at l9
  have hcur := B1.loadHolds_unique l9 hrec
  -- the frame's cells
  have hfb := inst_fbA hR hr hI hIt hjm
  have hF0 := inst_frameA hR hI hIt hjm (by rw [hcj, hbodyM]; exact hw)
  have hval' : ∀ u ∈ (coreOf jm).params, 2 ≤ cellJ jm u → cellJ jm u < fsN jm →
      I.fp + cellJ jm u < maxCells ∧ refMem r.img (I.fp + cellJ jm u) = σI u := fun u hu h2 hlt ↦
    ref_readA hr (by omega) (hF0.val u (List.mem_append_left _ (List.mem_append_left _ hu)) h2 hlt)
  obtain ⟨hlt7, hr7⟩ := hval' (.n 5) (by rw [hcj]; exact hm5) (by omega) (by omega)
  obtain ⟨hlt10, hr10⟩ := hval' (.n 8) (by rw [hcj]; exact hm8) (by omega) (by omega)
  rw [hc5] at hr7 hlt7
  rw [hc8] at hr10 hlt10
  -- the header
  obtain ⟨s, hs'⟩ : ∃ s, siteOf jm c = some s := Option.isSome_iff_exists.mp hsb
  have hH := B2C.H_eq_kidHdr hIt hjm (by rw [hcj, hbodyM]; exact hw) i
  unfold kidHdr at hH
  rw [hci] at hH
  dsimp only at hH
  rw [ite_eq_right (by rw [hcj, hloopM]; simp), hs'] at hH
  refine ⟨I.fp, 4 * qv, 4 * qv + rv, by rw [hhdr, hH], hlt7, hlt10, ?_, by rw [hr10, hcg], by omega, by omega⟩
  rw [hcur, hr7]
  congr 2
  ring

/-- **`LrlQ` at every honest instance.** -/
theorem lrlQ_allA (hR : RefH (layB al) (D r) r) (hr : r.Ok) : ∀ J ∈ instsR al D r, LrlQ r J := by
  refine insts_allA hR (lrlQ_stepA hR hr) fun J hm ↦ ?_
  intro f σ bufs kids hJt nt bits main loop lasts hmem k _ hkf
  have hn := hm _ _ _ _ hJt
  subst hn
  exact absurd (List.mem_of_getElem? hkf) (lrlSpec_all hmem).not_main

/-- **A last arm of `k > 0` rounds is a cursor-run arm** (`StLoopOkA`): its cursor, its record's, lies `4W·h` words
past `cursor` (the caller's cell `7`), with `W·k` words of room below `W·n`, `g^n` the caller's cell `10`. -/
theorem lrl_stOk {nt bits : ℕ} {main loop : String} {lasts : List String}
    (hmem : (nt, bits, main, loop, lasts) ∈ lrlSpecs) {k : ℕ} (hk1 : 1 ≤ k) {f : String} (hkf : lasts[k]? = some f)
    {W S : ℕ} (hWd : lrW nt bits = W) (hS : S = W * k) : StLoopOkA al D (f, 7, 10, W, 9, S) := by
  subst hWd hS
  refine ⟨by dsimp only; decide, by dsimp only; decide, by dsimp only; unfold CoreMode.GB; decide, ?_, ?_⟩
  · have : 0 < lrW nt bits := by unfold lrW; omega
    dsimp only
    exact Nat.mul_pos this hk1
  intro r hR hr I hI σ bufs kids ht fn hf
  dsimp only
  obtain ⟨a, m, n, hh2, h7, h10, hcur, hm10, hn64, hmn⟩ := lrlQ_allA hR hr I hI f σ bufs kids ht nt bits main loop
    lasts hmem k hk1 hkf
  refine ⟨a, m, n, hh2, h7, h10, hcur, hm10, by unfold CoreMode.capE; omega, ?_⟩
  rw [← Nat.mul_add]
  exact Nat.mul_le_mul_left _ hmn

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.CoreMode.Own.link_rounds_last

open LeanVM.Guest LeanVM.Guest.EndExec

public section

/-- **Its arms' cursors** (`lrl_stOk`). -/
theorem stLoops_okA {al : String → Bool} {D : Ref → RefD} : ∀ c ∈ stLoops, StLoopOkA al D c := by
  intro c hc
  simp only [stLoops, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact lrl_stOk (nt := 1) (bits := 0) (main := name% «link_rounds__L1_L0»)
      (loop := name% «link_rounds__L1_L0_loop0»)
      (lasts := [name% «link_rounds_last__L1_L0_L0», name% «link_rounds_last__L1_L0_L1»,
        name% «link_rounds_last__L1_L0_L2», name% «link_rounds_last__L1_L0_L3»])
      (by decide) (k := 1) (by decide) rfl rfl rfl
  · exact lrl_stOk (nt := 1) (bits := 0) (main := name% «link_rounds__L1_L0»)
      (loop := name% «link_rounds__L1_L0_loop0»)
      (lasts := [name% «link_rounds_last__L1_L0_L0», name% «link_rounds_last__L1_L0_L1»,
        name% «link_rounds_last__L1_L0_L2», name% «link_rounds_last__L1_L0_L3»])
      (by decide) (k := 2) (by decide) rfl rfl rfl
  · exact lrl_stOk (nt := 1) (bits := 0) (main := name% «link_rounds__L1_L0»)
      (loop := name% «link_rounds__L1_L0_loop0»)
      (lasts := [name% «link_rounds_last__L1_L0_L0», name% «link_rounds_last__L1_L0_L1»,
        name% «link_rounds_last__L1_L0_L2», name% «link_rounds_last__L1_L0_L3»])
      (by decide) (k := 3) (by decide) rfl rfl rfl
  · exact lrl_stOk (nt := 6) (bits := 0) (main := name% «link_rounds__L6_L0»)
      (loop := name% «link_rounds__L6_L0_loop0»)
      (lasts := [name% «link_rounds_last__L6_L0_L0», name% «link_rounds_last__L6_L0_L1»,
        name% «link_rounds_last__L6_L0_L2», name% «link_rounds_last__L6_L0_L3»])
      (by decide) (k := 1) (by decide) rfl rfl rfl
  · exact lrl_stOk (nt := 6) (bits := 0) (main := name% «link_rounds__L6_L0»)
      (loop := name% «link_rounds__L6_L0_loop0»)
      (lasts := [name% «link_rounds_last__L6_L0_L0», name% «link_rounds_last__L6_L0_L1»,
        name% «link_rounds_last__L6_L0_L2», name% «link_rounds_last__L6_L0_L3»])
      (by decide) (k := 2) (by decide) rfl rfl rfl
  · exact lrl_stOk (nt := 6) (bits := 0) (main := name% «link_rounds__L6_L0»)
      (loop := name% «link_rounds__L6_L0_loop0»)
      (lasts := [name% «link_rounds_last__L6_L0_L0», name% «link_rounds_last__L6_L0_L1»,
        name% «link_rounds_last__L6_L0_L2», name% «link_rounds_last__L6_L0_L3»])
      (by decide) (k := 3) (by decide) rfl rfl rfl
  · exact lrl_stOk (nt := 7) (bits := 0) (main := name% «link_rounds__L7_L0»)
      (loop := name% «link_rounds__L7_L0_loop0»)
      (lasts := [name% «link_rounds_last__L7_L0_L0», name% «link_rounds_last__L7_L0_L1»,
        name% «link_rounds_last__L7_L0_L2», name% «link_rounds_last__L7_L0_L3»])
      (by decide) (k := 1) (by decide) rfl rfl rfl
  · exact lrl_stOk (nt := 7) (bits := 0) (main := name% «link_rounds__L7_L0»)
      (loop := name% «link_rounds__L7_L0_loop0»)
      (lasts := [name% «link_rounds_last__L7_L0_L0», name% «link_rounds_last__L7_L0_L1»,
        name% «link_rounds_last__L7_L0_L2», name% «link_rounds_last__L7_L0_L3»])
      (by decide) (k := 2) (by decide) rfl rfl rfl
  · exact lrl_stOk (nt := 7) (bits := 0) (main := name% «link_rounds__L7_L0»)
      (loop := name% «link_rounds__L7_L0_loop0»)
      (lasts := [name% «link_rounds_last__L7_L0_L0», name% «link_rounds_last__L7_L0_L1»,
        name% «link_rounds_last__L7_L0_L2», name% «link_rounds_last__L7_L0_L3»])
      (by decide) (k := 3) (by decide) rfl rfl rfl
  · exact lrl_stOk (nt := 8) (bits := 1) (main := name% «link_rounds__L8_L1»)
      (loop := name% «link_rounds__L8_L1_loop0»)
      (lasts := [name% «link_rounds_last__L8_L1_L0», name% «link_rounds_last__L8_L1_L1»,
        name% «link_rounds_last__L8_L1_L2», name% «link_rounds_last__L8_L1_L3»])
      (by decide) (k := 1) (by decide) rfl rfl rfl
  · exact lrl_stOk (nt := 8) (bits := 1) (main := name% «link_rounds__L8_L1»)
      (loop := name% «link_rounds__L8_L1_loop0»)
      (lasts := [name% «link_rounds_last__L8_L1_L0», name% «link_rounds_last__L8_L1_L1»,
        name% «link_rounds_last__L8_L1_L2», name% «link_rounds_last__L8_L1_L3»])
      (by decide) (k := 2) (by decide) rfl rfl rfl
  · exact lrl_stOk (nt := 8) (bits := 1) (main := name% «link_rounds__L8_L1»)
      (loop := name% «link_rounds__L8_L1_loop0»)
      (lasts := [name% «link_rounds_last__L8_L1_L0», name% «link_rounds_last__L8_L1_L1»,
        name% «link_rounds_last__L8_L1_L2», name% «link_rounds_last__L8_L1_L3»])
      (by decide) (k := 3) (by decide) rfl rfl rfl
  · exact lrl_stOk (nt := 9) (bits := 1) (main := name% «link_rounds__L9_L1»)
      (loop := name% «link_rounds__L9_L1_loop0»)
      (lasts := [name% «link_rounds_last__L9_L1_L0», name% «link_rounds_last__L9_L1_L1»,
        name% «link_rounds_last__L9_L1_L2», name% «link_rounds_last__L9_L1_L3»])
      (by decide) (k := 1) (by decide) rfl rfl rfl
  · exact lrl_stOk (nt := 9) (bits := 1) (main := name% «link_rounds__L9_L1»)
      (loop := name% «link_rounds__L9_L1_loop0»)
      (lasts := [name% «link_rounds_last__L9_L1_L0», name% «link_rounds_last__L9_L1_L1»,
        name% «link_rounds_last__L9_L1_L2», name% «link_rounds_last__L9_L1_L3»])
      (by decide) (k := 2) (by decide) rfl rfl rfl
  · exact lrl_stOk (nt := 9) (bits := 1) (main := name% «link_rounds__L9_L1»)
      (loop := name% «link_rounds__L9_L1_loop0»)
      (lasts := [name% «link_rounds_last__L9_L1_L0», name% «link_rounds_last__L9_L1_L1»,
        name% «link_rounds_last__L9_L1_L2», name% «link_rounds_last__L9_L1_L3»])
      (by decide) (k := 3) (by decide) rfl rfl rfl
  · exact lrl_stOk (nt := 10) (bits := 1) (main := name% «link_rounds__L10_L1»)
      (loop := name% «link_rounds__L10_L1_loop0»)
      (lasts := [name% «link_rounds_last__L10_L1_L0», name% «link_rounds_last__L10_L1_L1»,
        name% «link_rounds_last__L10_L1_L2», name% «link_rounds_last__L10_L1_L3»])
      (by decide) (k := 1) (by decide) rfl rfl rfl
  · exact lrl_stOk (nt := 10) (bits := 1) (main := name% «link_rounds__L10_L1»)
      (loop := name% «link_rounds__L10_L1_loop0»)
      (lasts := [name% «link_rounds_last__L10_L1_L0», name% «link_rounds_last__L10_L1_L1»,
        name% «link_rounds_last__L10_L1_L2», name% «link_rounds_last__L10_L1_L3»])
      (by decide) (k := 2) (by decide) rfl rfl rfl
  · exact lrl_stOk (nt := 10) (bits := 1) (main := name% «link_rounds__L10_L1»)
      (loop := name% «link_rounds__L10_L1_loop0»)
      (lasts := [name% «link_rounds_last__L10_L1_L0», name% «link_rounds_last__L10_L1_L1»,
        name% «link_rounds_last__L10_L1_L2», name% «link_rounds_last__L10_L1_L3»])
      (by decide) (k := 3) (by decide) rfl rfl rfl

end

end LeanVM.Guest.CoreMode.Own.link_rounds_last
