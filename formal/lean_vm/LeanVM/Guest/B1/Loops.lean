/-
  LeanVM.Guest.B1.Loops

  B1 for the guest's `mul_range` loops over the multilinear helpers: `eq_prefix_chain` and its
  helper `__loop7`.
-/

module

public import LeanVM.Guest.B1.Sumcheck

/-!
# `mul_range` loops (TRIAGE #22)

A `for x in mul_range(1, N)` is a guard `callIf (1 + N)` and a helper `__loopK` that runs the
body at `x` and calls itself at `x·g` while `x·g ≠ N`. Its step lemma (`relN` at depth `d + 1`,
`loop*_step`) feeds `guarded_loop_iff`: the loop holds exactly when `N = g^m`, `m` below the
order of `g`, and the body holds at every `g^j`, `j < m`.

* `eq_prefix_chain(chain, seed, a, b, N)` (G:788-796): `chain[j] = seed · eqEval (a[..j]) (b[..j])`
  for `j ≤ m` (`eqEval`, V:703).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Lists of words read by a loop -/

theorem loadHolds_unique {rd : Reader} {p : E} {k : ℕ} {w w' : E} (h : LoadHolds rd p k w)
    (h' : LoadHolds rd p k w') : w = w' :=
  Option.some.inj (h.2.symm.trans h'.2)

/-- Choices below `m` as a list. -/
theorem exists_list_of_forall {P : ℕ → E → Prop} {m : ℕ} (h : ∀ j < m, ∃ v, P j v) :
    ∃ l : List E, l.length = m ∧ ∀ j (hj : j < l.length), P j l[j] := by
  classical
  refine ⟨(List.range m).map fun j => if hj : j < m then Classical.choose (h j hj) else 0,
    by simp, fun j hj => ?_⟩
  simp only [List.length_map, List.length_range] at hj
  simp only [List.getElem_map, List.getElem_range, hj, ↓reduceDIte]
  exact Classical.choose_spec (h j hj)

theorem eqEval_take_succ (as bs : List E) (j : ℕ) (ha : j < as.length) (hb : j < bs.length) :
    eqEval (as.take (j + 1)) (bs.take (j + 1)) =
      eqEval (as.take j) (bs.take j) * (1 + as[j] + bs[j]) := by
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem ha,
    List.getElem?_eq_getElem hb]
  simp only [eqEval, Option.toList_some]
  rw [List.zipWith_append (by simp; omega), List.foldl_append]
  rfl

/-! ## `eq_prefix_chain` and `__loop7` -/

/-- The body of `__loop7` at `x`: `chain[x·g] = chain[x] · (1 + a[x] + b[x])`. -/
def Loop7Body (rd : Reader) (chain a b x : E) : Prop :=
  ∃ c av bv, LoadHolds rd (chain * x) 0 c ∧ LoadHolds rd (a * x) 0 av ∧
    LoadHolds rd (b * x) 0 bv ∧ LoadHolds rd (chain * x) 1 (c * (1 + av + bv))

theorem find_loop7 : coreProgram.find? "__loop7" = some Data.core37 :=
  Program.find?_of_indexOf? (j := 37) (by decide +kernel) rfl

theorem loop7_step (rd : Reader) (N chain a b : E) (d : ℕ) (x : E) :
    coreProgram.relN rd (d + 1) "__loop7" (x :: [N, chain, a, b]) [] ↔
      Loop7Body rd chain a b x ∧ IsInK (x * gen + N) ∧
        (x * gen + N ≠ 0 → coreProgram.relN rd d "__loop7" (x * gen :: [N, chain, a, b]) []) := by
  rw [relN_succ_iff find_loop7, show Fn.params Data.core37 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl,
    show Fn.body Data.core37 = Data.core37.body from rfl, Data.core37.body]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    and_true, word_one, word_gen]
  constructor
  · rintro ⟨σ, hp, h5, l6, h7, h8, l9, h10, h11, l12, h13, h14, h15, l14,
      h16, h17, h18, h19, h20, hK, hcall⟩
    simp only [List.cons.injEq] at hp
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hp
    refine ⟨⟨σ (.n 6), σ (.n 9), σ (.n 12), by rwa [h5] at l6, by rwa [h8] at l9,
      by rwa [h11] at l12, ?_⟩, by rwa [h18, h17, h16] at hK, fun hne => ?_⟩
    · rw [h15, h14, h13, h10, h7] at l14; exact l14
    · have := hcall (by rwa [h18, h17, h16])
      rwa [h20, h19] at this
  · rintro ⟨⟨c, av, bv, l6, l9, l12, l14⟩, hK, hcall⟩
    refine ⟨setl (Val.ofArgs [x, N, chain, a, b]) 5 [chain * x, c, 1, a * x, av, 1 + av, b * x,
      bv, 1 + av + bv, c * (1 + av + bv), chain * x, gen, x * gen, x * gen + N, gen, x * gen],
      ?_, ?_⟩
    · b1_look
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (try b1_look)
      exacts [l6, l9, l12, l14, hK, hcall]

/-- **`eq_prefix_chain(chain, seed, a, b, N)`** (G:788-796; TRIAGE #22): `N = g^m` below the
order of `g`, the words `as`, `bs` read at `a`, `b` below `m`, and `chain` holds the prefix
products `seed · eqEval (as[..j]) (bs[..j])` (V:703) for every `j ≤ m`. -/
def MeaningEqPrefixChain (rd : Reader) : List E → List E → Prop
  | [chain, seed, a, b, N], rets =>
      rets = [] ∧ ∃ m < ordG, N = gen ^ m ∧ ∃ as bs : List E, as.length = m ∧ bs.length = m ∧
        ReadsAt rd a as ∧ ReadsAt rd b bs ∧
        ∀ j ≤ m, LoadHolds rd chain j (seed * eqEval (as.take j) (bs.take j))
  | _, _ => False

theorem find_eq_prefix_chain : coreProgram.find? "eq_prefix_chain" = some Data.core4 :=
  Program.find?_of_indexOf? (j := 4) (by decide +kernel) rfl

/-- The loop's bodies at `g^j`, `j < m`, with the seed: the prefix products. -/
theorem loop7_bodies_iff (rd : Reader) (chain seed a b : E) (m : ℕ) :
    (LoadHolds rd chain 0 seed ∧ ∀ j < m, Loop7Body rd chain a b (gen ^ j)) ↔
      ∃ as bs : List E, as.length = m ∧ bs.length = m ∧ ReadsAt rd a as ∧ ReadsAt rd b bs ∧
        ∀ j ≤ m, LoadHolds rd chain j (seed * eqEval (as.take j) (bs.take j)) := by
  simp only [Loop7Body, loadHolds_mul_gen_pow, Nat.add_zero]
  constructor
  · rintro ⟨h0, hB⟩
    obtain ⟨as, has, hA⟩ := exists_list_of_forall (P := fun j v => LoadHolds rd a j v)
      fun j hj => by obtain ⟨_, av, _, _, h, _⟩ := hB j hj; exact ⟨av, h⟩
    obtain ⟨bs, hbs, hBs⟩ := exists_list_of_forall (P := fun j v => LoadHolds rd b j v)
      fun j hj => by obtain ⟨_, _, bv, _, _, h, _⟩ := hB j hj; exact ⟨bv, h⟩
    refine ⟨as, bs, has, hbs, hA, hBs, fun j hj => ?_⟩
    induction j with
    | zero =>
      have e0 : eqEval (List.take 0 as) (List.take 0 bs) = 1 := by simp [eqEval]
      rw [e0, mul_one]
      exact h0
    | succ j ih =>
      obtain ⟨c, av, bv, lc, la, lb, lc1⟩ := hB j (by omega)
      have ec := loadHolds_unique lc (ih (by omega))
      have ea := loadHolds_unique la (hA j (by omega))
      have eb := loadHolds_unique lb (hBs j (by omega))
      rw [eqEval_take_succ as bs j (by omega) (by omega), ← mul_assoc, ← ec, ← ea, ← eb]
      exact lc1
  · rintro ⟨as, bs, has, hbs, hA, hBs, hc⟩
    have h0 := hc 0 (Nat.zero_le _)
    have e0 : eqEval (List.take 0 as) (List.take 0 bs) = 1 := by simp [eqEval]
    rw [e0, mul_one] at h0
    refine ⟨h0, fun j hj => ⟨_, as[j]'(by omega),
      bs[j]'(by omega), hc j (by omega), hA j (by omega), hBs j (by omega), ?_⟩⟩
    have := hc (j + 1) (by omega)
    rwa [eqEval_take_succ as bs j (by omega) (by omega), ← mul_assoc] at this

theorem eq_prefix_chain_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "eq_prefix_chain" args rets ↔ MeaningEqPrefixChain rd args rets := by
  rw [rel_iff_sem find_eq_prefix_chain,
    show Fn.params Data.core4 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl,
    show Fn.body Data.core4 = Data.core4.body from rfl, Data.core4.body]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_one]
  constructor
  · rintro ⟨σ, hp, l1, h5, h6, h7, hK, hcall, hret⟩
    subst hp
    rw [h6, h5] at hK hcall
    rw [h7] at hcall
    obtain ⟨m, hm, hN, hB⟩ := (guarded_loop_iff (loop7_step rd (σ (.n 4)) (σ (.n 0)) (σ (.n 2))
      (σ (.n 3)))).mp ⟨hK, hcall⟩
    exact ⟨hret.symm, m, hm, hN, (loop7_bodies_iff rd _ _ _ _ m).mp ⟨l1, hB⟩⟩
  · intro hm
    obtain ⟨chain, seed, a, b, N, rfl⟩ : ∃ chain seed a b N, args = [chain, seed, a, b, N] := by
      match args, hm with
      | [c, s, x, y, z], _ => exact ⟨c, s, x, y, z, rfl⟩
    obtain ⟨rfl, m, hm, hN, hbody⟩ := hm
    obtain ⟨l0, hB⟩ := (loop7_bodies_iff rd chain seed a b m).mpr hbody
    obtain ⟨hK, hcall⟩ := (guarded_loop_iff (loop7_step rd N chain a b)).mpr ⟨m, hm, hN, hB⟩
    refine ⟨setl (Val.ofArgs [chain, seed, a, b, N]) 5 [1, 1 + N, 1], ?_, ?_⟩
    · b1_look
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (try b1_look)
      exacts [l0, hK, hcall]

/-! ## `rs_eq_run` and `__loop8` -/

/-- `__loop8`'s squarings `zv^(2^k)`: their value numbers. -/
def l8z : ℕ → ℕ
  | 0 => 6
  | k + 1 => 21 + 4 * k

/-- `__loop8`'s coordinate `k`: square the `z` power, read the row, multiply, store. -/
def l8Blk : ℕ → List Stmt
  | 0 => [.atom (.load (.n 18) (.n 17) 0), .atom (.add (.n 19) (.n 6) (.n 10)),
      .atom (.mul (.n 20) (.n 18) (.n 19)), .atom (.load (.n 20) (.n 17) 64)]
  | k + 1 => [.atom (.mul (.n (21 + 4 * k)) (.n (l8z k)) (.n (l8z k))),
      .atom (.load (.n (22 + 4 * k)) (.n 17) (k + 1)),
      .atom (.add (.n (23 + 4 * k)) (.n (21 + 4 * k)) (.n 10)),
      .atom (.mul (.n (24 + 4 * k)) (.n (22 + 4 * k)) (.n (23 + 4 * k))),
      .atom (.load (.n (24 + 4 * k)) (.n 17) (65 + k))]

/-- The expansion of `__loop8`. -/
def l8Body : List Stmt :=
  [.atom (.mul (.n 5) (.n 2) (.n 0)), .atom (.load (.n 6) (.n 5) 0),
    .atom (.const (.n 7) (word 1 0 0)), .atom (.mul (.n 8) (.n 3) (.n 0)),
    .atom (.load (.n 9) (.n 8) 0), .atom (.add (.n 10) (.n 7) (.n 9)),
    .atom (.mul (.n 11) (.n 0) (.n 0)), .atom (.mul (.n 12) (.n 11) (.n 11)),
    .atom (.mul (.n 13) (.n 12) (.n 12)), .atom (.mul (.n 14) (.n 13) (.n 13)),
    .atom (.mul (.n 15) (.n 14) (.n 14)), .atom (.mul (.n 16) (.n 15) (.n 15)),
    .atom (.mul (.n 17) (.n 4) (.n 16))] ++
  ((List.range 64).map l8Blk).flatten ++
  [.atom (.const (.n 273) (word 2 0 0)), .atom (.mul (.n 274) (.n 0) (.n 273)),
    .atom (.add (.n 275) (.n 274) (.n 1)), .atom (.const (.n 276) (word 2 0 0)),
    .atom (.mul (.n 277) (.n 0) (.n 276)),
    .callIf (.n 275) "__loop8" [.n 277, .n 1, .n 2, .n 3, .n 4], .ret []]

theorem core38_body : Fn.body Data.core38 = l8Body := stmtsEqb_sound (by decide +kernel)

/-- What coordinate `k` asks of a valuation. -/
def L8Ok (rd : Reader) (σ : Val) : ℕ → Prop
  | 0 => LoadHolds rd (σ (.n 17)) 0 (σ (.n 18)) ∧ σ (.n 19) = σ (.n 6) + σ (.n 10) ∧
      σ (.n 20) = σ (.n 18) * σ (.n 19) ∧ LoadHolds rd (σ (.n 17)) 64 (σ (.n 20))
  | k + 1 => σ (.n (21 + 4 * k)) = σ (.n (l8z k)) * σ (.n (l8z k)) ∧
      LoadHolds rd (σ (.n 17)) (k + 1) (σ (.n (22 + 4 * k))) ∧
      σ (.n (23 + 4 * k)) = σ (.n (21 + 4 * k)) + σ (.n 10) ∧
      σ (.n (24 + 4 * k)) = σ (.n (22 + 4 * k)) * σ (.n (23 + 4 * k)) ∧
      LoadHolds rd (σ (.n 17)) (65 + k) (σ (.n (24 + 4 * k)))

theorem holds_l8Blk {C : CallRel} {rd : Reader} {σ : Val} (k : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (l8Blk k) True kret ↔ L8Ok rd σ k := by
  cases k <;> simp only [l8Blk, L8Ok, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

/-- The body of `__loop8` at `x`: with `zv = z[x]`, `p = point[x]` and the row `chain·x^64`,
every coordinate `k < 64` of the next row is the row's times `zv^(2^k) + (1 + p)`. -/
def Loop8Body (rd : Reader) (zs ps chain x : E) : Prop :=
  ∃ zv pv, LoadHolds rd (zs * x) 0 zv ∧ LoadHolds rd (ps * x) 0 pv ∧
    ∀ k < 64, ∃ w, LoadHolds rd (chain * x ^ 64) k w ∧
      LoadHolds rd (chain * x ^ 64) (64 + k) (w * (zv ^ 2 ^ k + (1 + pv)))

theorem find_loop8 : coreProgram.find? "__loop8" = some Data.core38 :=
  Program.find?_of_indexOf? (j := 38) (by decide +kernel) rfl

/-- The squarings: `.n (l8z k)` is `zv^(2^k)`. -/
theorem l8z_pow {rd : Reader} {σ : Val} (h : ∀ k < 64, L8Ok rd σ k) :
    ∀ k < 64, σ (.n (l8z k)) = σ (.n 6) ^ 2 ^ k
  | 0, _ => by simp [l8z]
  | k + 1, hk => by
    have := (h (k + 1) hk).1
    rw [l8z, this, l8z_pow h k (by omega), ← pow_add, ← two_mul, pow_succ, Nat.mul_comm]

/-- The honest values of `__loop8`'s coordinates, from `.n 18`. -/
def l8Vals (zv pv : E) (w : ℕ → E) (i : ℕ) : E :=
  if i = 0 then w 0 else if i = 1 then zv + (1 + pv) else if i = 2 then w 0 * (zv + (1 + pv))
  else
    let k := (i - 3) / 4 + 1
    let c := (i - 3) % 4
    if c = 0 then zv ^ 2 ^ k else if c = 1 then w k
    else if c = 2 then zv ^ 2 ^ k + (1 + pv) else w k * (zv ^ 2 ^ k + (1 + pv))

theorem l8Vals_at (zv pv : E) (w : ℕ → E) (k c : ℕ) (hc : c < 4) :
    l8Vals zv pv w (3 + 4 * k + c) =
      if c = 0 then zv ^ 2 ^ (k + 1) else if c = 1 then w (k + 1)
      else if c = 2 then zv ^ 2 ^ (k + 1) + (1 + pv) else w (k + 1) * (zv ^ 2 ^ (k + 1) + (1 + pv)) := by
  simp only [l8Vals]
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    show (3 + 4 * k + c - 3) / 4 = k by omega, show (3 + 4 * k + c - 3) % 4 = c by omega]

theorem loop8_step (rd : Reader) (N zs ps chain : E) (d : ℕ) (x : E) :
    coreProgram.relN rd (d + 1) "__loop8" (x :: [N, zs, ps, chain]) [] ↔
      Loop8Body rd zs ps chain x ∧ IsInK (x * gen + N) ∧
        (x * gen + N ≠ 0 → coreProgram.relN rd d "__loop8" (x * gen :: [N, zs, ps, chain]) []) := by
  rw [relN_succ_iff find_loop8, show Fn.params Data.core38 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl,
    core38_body, l8Body]
  simp only [holdsList_append, holdsList_range_flatten 64 l8Blk (fun k => by cases k <;> rfl),
    holds_l8Blk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, and_true,
    word_one, word_gen]
  constructor
  · rintro ⟨σ, hp, h5, l6, h7, h8, l9, h10, h11, h12, h13, h14, h15, h16, h17, hblk, h273, h274,
      h275, h276, h277, hK, hcall⟩
    simp only [List.cons.injEq] at hp
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hp
    have hrow : σ (.n 17) = σ (.n 4) * σ (.n 0) ^ 64 := by
      rw [h17, h16, h15, h14, h13, h12, h11]; ring
    have hz := l8z_pow hblk
    refine ⟨⟨σ (.n 6), σ (.n 9), by rwa [h5] at l6, by rwa [h8] at l9, fun k hk => ?_⟩,
      by rwa [h275, h274, h273] at hK, fun hne => ?_⟩
    · rw [← hrow]
      cases k with
      | zero =>
        obtain ⟨la, e19, e20, lb⟩ := hblk 0 (by omega)
        refine ⟨σ (.n 18), la, ?_⟩
        rw [e20, e19, h10, h7] at lb
        simpa only [pow_zero, pow_one, Nat.add_zero] using lb
      | succ k =>
        obtain ⟨-, la, e23, e24, lb⟩ := hblk (k + 1) hk
        refine ⟨σ (.n (22 + 4 * k)), la, ?_⟩
        have hzk := hz (k + 1) hk
        simp only [l8z] at hzk
        rw [e24, e23, hzk, h10, h7] at lb
        rw [show 64 + (k + 1) = 65 + k by omega]
        exact lb
    · have := hcall (by rwa [h275, h274, h273])
      rwa [h277, h276] at this
  · rintro ⟨⟨zv, pv, l6, l9, hrows⟩, hK, hcall⟩
    obtain ⟨ws, hws, hw⟩ := exists_list_of_forall (P := fun k w =>
      LoadHolds rd (chain * x ^ 64) k w ∧
        LoadHolds rd (chain * x ^ 64) (64 + k) (w * (zv ^ 2 ^ k + (1 + pv)))) hrows
    set w := fun k => ws.getD k 0
    have hw' : ∀ k < 64, LoadHolds rd (chain * x ^ 64) k (w k) ∧
        LoadHolds rd (chain * x ^ 64) (64 + k) (w k * (zv ^ 2 ^ k + (1 + pv))) := fun k hk => by
      have := hw k (by omega)
      simp only [w, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < ws.length by omega),
        Option.getD_some]
      exact this
    set τ := setl (setv (setl (Val.ofArgs [x, N, zs, ps, chain]) 5
      [zs * x, zv, 1, ps * x, pv, 1 + pv, x ^ 2, x ^ 4, x ^ 8, x ^ 16, x ^ 32, x ^ 64,
        chain * x ^ 64]) 18 255 (l8Vals zv pv w)) 273 [gen, x * gen, x * gen + N, gen, x * gen]
    have hv : ∀ k c, c < 4 → k < 63 → τ (.n (21 + 4 * k + c)) =
        if c = 0 then zv ^ 2 ^ (k + 1) else if c = 1 then w (k + 1)
        else if c = 2 then zv ^ 2 ^ (k + 1) + (1 + pv)
        else w (k + 1) * (zv ^ 2 ^ (k + 1) + (1 + pv)) := fun k c hc hk => by
      simp only [τ, setl, List.length_cons, List.length_nil]
      rw [set_n_lt (by omega), set_n_in (by omega) (by omega),
        show 21 + 4 * k + c - 18 = 3 + 4 * k + c by omega, l8Vals_at _ _ _ _ _ hc]
    have h17 : τ (.n 17) = chain * x ^ 64 := by simp only [τ]; b1_look
    have h10 : τ (.n 10) = 1 + pv := by simp only [τ]; b1_look
    refine ⟨τ, ?_, ?_⟩
    · simp only [τ]; b1_look
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      case refine_14 =>
        cases k with
        | zero =>
          have e18 : τ (.n 18) = w 0 := by simp only [τ]; b1_look; rfl
          have e19 : τ (.n 19) = zv + (1 + pv) := by simp only [τ]; b1_look; rfl
          have e20 : τ (.n 20) = w 0 * (zv + (1 + pv)) := by simp only [τ]; b1_look; rfl
          have e6 : τ (.n 6) = zv := by simp only [τ]; b1_look
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [h17, e18]; exact ((hw' 0 (by omega)).1)
          · rw [e19, e6, h10]
          · rw [e20, e18, e19]
          · rw [h17, e20]
            have := (hw' 0 (by omega)).2
            simpa using this
        | succ k =>
          have ez := hv k 0 (by omega) (by omega)
          have ew := hv k 1 (by omega) (by omega)
          have ea := hv k 2 (by omega) (by omega)
          have em := hv k 3 (by omega) (by omega)
          simp only [Nat.add_zero, ite_true, show (1 = 0) = False by decide, ite_false,
            show (2 = 0) = False by decide, show (2 = 1) = False by decide, show (3 = 0) = False by decide,
            show (3 = 1) = False by decide, show (3 = 2) = False by decide,
            show 21 + 4 * k + 1 = 22 + 4 * k by omega, show 21 + 4 * k + 2 = 23 + 4 * k by omega,
            show 21 + 4 * k + 3 = 24 + 4 * k by omega] at ez ew ea em
          have hzk : τ (.n (l8z k)) = zv ^ 2 ^ k := by
            cases k with
            | zero => simp only [l8z, τ]; b1_look; rw [pow_zero, pow_one]
            | succ k =>
              have := hv k 0 (by omega) (by omega)
              simp only [Nat.add_zero, ite_true] at this
              simp only [l8z]; exact this
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · rw [ez, hzk, ← pow_add, ← two_mul, pow_succ, Nat.mul_comm]
          · rw [h17, ew]; exact (hw' (k + 1) hk).1
          · rw [ea, ez, h10]
          · rw [em, ew, ea]
          · rw [h17, em, show 65 + k = 64 + (k + 1) by omega]; exact (hw' (k + 1) hk).2
      all_goals (try (simp only [τ]; b1_look))
      all_goals (try ring1)
      · exact l6
      · exact l9
      · exact hK
      · exact hcall

/-- Coordinate `k` of the telescoped ring-switch product: `c · Π_n (1 + z_n^(2^k) + p_n)`,
`ringWeight`'s inner product (V:2011) from the coefficient `c`. -/
def ringRow (c : E) (zs ps : List E) (k : ℕ) : E :=
  (List.zip (zs.map (· ^ 2 ^ k)) ps).foldl (fun product (value, challenge) =>
    product * (1 + value + challenge)) c

theorem ringRow_take_succ (c : E) (zs ps : List E) (k j : ℕ) (hz : j < zs.length)
    (hp : j < ps.length) :
    ringRow c (zs.take (j + 1)) (ps.take (j + 1)) k =
      ringRow c (zs.take j) (ps.take j) k * (1 + zs[j] ^ 2 ^ k + ps[j]) := by
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hz,
    List.getElem?_eq_getElem hp]
  simp only [ringRow, Option.toList_some, List.map_append, List.map_cons, List.map_nil]
  rw [List.zip_append (by simp; omega), List.foldl_append]
  rfl

theorem ringRow_zero (c : E) (zs ps : List E) (k : ℕ) :
    ringRow c (zs.take 0) (ps.take 0) k = c := by
  simp [ringRow]

/-- **`rs_eq_run(chain, z, point, N)`** (G:799-813; TRIAGE #23): `N = g^m` below the order of
`g`, the words `zs`, `ps` read at `z`, `point` below `m`, and row `j ≤ m` of `chain` (64 words
from `chain·g^(64·j)`) is the first row times the telescoped products `ringRow` (V:2011), when
the loop runs (`m > 0`). -/
def MeaningRsEqRun (rd : Reader) : List E → List E → Prop
  | [chain, z, point, N], rets =>
      rets = [] ∧ ∃ m < ordG, N = gen ^ m ∧ ∃ zs ps : List E, zs.length = m ∧ ps.length = m ∧
        ReadsAt rd z zs ∧ ReadsAt rd point ps ∧ ∃ c : List E, c.length = 64 ∧
        (0 < m → ∀ j ≤ m, ∀ k < 64,
          LoadHolds rd chain (64 * j + k) (ringRow (c.getD k 0) (zs.take j) (ps.take j) k))
  | _, _ => False

theorem loop8_bodies_iff (rd : Reader) (z point chain : E) (m : ℕ) :
    (∀ j < m, Loop8Body rd z point chain (gen ^ j)) ↔
      ∃ zs ps : List E, zs.length = m ∧ ps.length = m ∧ ReadsAt rd z zs ∧ ReadsAt rd point ps ∧
        ∃ c : List E, c.length = 64 ∧ (0 < m → ∀ j ≤ m, ∀ k < 64,
          LoadHolds rd chain (64 * j + k) (ringRow (c.getD k 0) (zs.take j) (ps.take j) k)) := by
  have hpow : ∀ j, (gen ^ j) ^ 64 = gen ^ (64 * j) := fun j => by rw [← pow_mul, Nat.mul_comm]
  simp only [Loop8Body, loadHolds_mul_gen_pow, hpow, Nat.add_zero]
  constructor
  · intro hB
    obtain ⟨zs, hzs, hZ⟩ := exists_list_of_forall (P := fun j v => LoadHolds rd z j v)
      fun j hj => by obtain ⟨zv, _, h, _⟩ := hB j hj; exact ⟨zv, h⟩
    obtain ⟨ps, hps, hP⟩ := exists_list_of_forall (P := fun j v => LoadHolds rd point j v)
      fun j hj => by obtain ⟨_, pv, _, h, _⟩ := hB j hj; exact ⟨pv, h⟩
    refine ⟨zs, ps, hzs, hps, hZ, hP, ?_⟩
    rcases Nat.eq_zero_or_pos m with hm | hm
    · exact ⟨List.replicate 64 0, by simp, fun h => absurd h (by omega)⟩
    obtain ⟨c, hc, hC⟩ := exists_list_of_forall (P := fun k v => LoadHolds rd chain k v)
      fun k hk => by
        obtain ⟨_, _, _, _, hrow⟩ := hB 0 hm
        obtain ⟨w, hw, -⟩ := hrow k hk
        exact ⟨w, by simpa using hw⟩
    refine ⟨c, hc, fun _ j hj k hk => ?_⟩
    induction j with
    | zero =>
      rw [ringRow_zero, Nat.mul_zero, Nat.zero_add, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact hC k (by omega)
    | succ j ih =>
      obtain ⟨zv, pv, lz, lp, hrow⟩ := hB j (by omega)
      obtain ⟨w, hw, hw'⟩ := hrow k hk
      have ew := loadHolds_unique hw (ih (by omega))
      have ez := loadHolds_unique lz (hZ j (by omega))
      have ep := loadHolds_unique lp (hP j (by omega))
      rw [ringRow_take_succ _ _ _ _ _ (by omega) (by omega), ← ew, ← ez, ← ep,
        show 64 * (j + 1) + k = 64 * j + (64 + k) by ring]
      have : w * (zv ^ 2 ^ k + (1 + pv)) = w * (1 + zv ^ 2 ^ k + pv) := by ring
      rw [← this]
      exact hw'
  · rintro ⟨zs, ps, hzs, hps, hZ, hP, c, hc, hC⟩ j hj
    refine ⟨zs[j]'(by omega), ps[j]'(by omega), hZ j (by omega), hP j (by omega),
      fun k hk => ⟨_, hC (by omega) j (by omega) k hk, ?_⟩⟩
    have := hC (by omega) (j + 1) (by omega) k hk
    rw [ringRow_take_succ _ _ _ _ _ (by omega) (by omega),
      show 64 * (j + 1) + k = 64 * j + (64 + k) by ring] at this
    have e : ∀ w : E, w * (1 + zs[j] ^ 2 ^ k + ps[j]) = w * (zs[j] ^ 2 ^ k + (1 + ps[j])) :=
      fun w => by ring
    rwa [e] at this

theorem find_rs_eq_run : coreProgram.find? "rs_eq_run" = some Data.core5 :=
  Program.find?_of_indexOf? (j := 5) (by decide +kernel) rfl

theorem rs_eq_run_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "rs_eq_run" args rets ↔ MeaningRsEqRun rd args rets := by
  rw [rel_iff_sem find_rs_eq_run, show Fn.params Data.core5 = [.n 0, .n 1, .n 2, .n 3] from rfl,
    show Fn.body Data.core5 = Data.core5.body from rfl, Data.core5.body]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_one]
  constructor
  · rintro ⟨σ, hp, h4, h5, h6, hK, hcall, hret⟩
    subst hp
    rw [h5, h4] at hK hcall
    rw [h6] at hcall
    obtain ⟨m, hm, hN, hB⟩ := (guarded_loop_iff (loop8_step rd (σ (.n 3)) (σ (.n 1)) (σ (.n 2))
      (σ (.n 0)))).mp ⟨hK, hcall⟩
    exact ⟨hret.symm, m, hm, hN, (loop8_bodies_iff rd _ _ _ m).mp hB⟩
  · intro hm
    obtain ⟨chain, z, point, N, rfl⟩ : ∃ chain z point N, args = [chain, z, point, N] := by
      match args, hm with
      | [c, s, x, y], _ => exact ⟨c, s, x, y, rfl⟩
    obtain ⟨rfl, m, hm, hN, hbody⟩ := hm
    obtain ⟨hK, hcall⟩ := (guarded_loop_iff (loop8_step rd N z point chain)).mpr
      ⟨m, hm, hN, (loop8_bodies_iff rd z point chain m).mpr hbody⟩
    refine ⟨setl (Val.ofArgs [chain, z, point, N]) 4 [1, 1 + N, 1], ?_, ?_⟩
    · b1_look
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (try b1_look)
      exacts [hK, hcall]

end
end LeanVM.Guest.B1
