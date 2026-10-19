/-
  LeanVM.Guest.B1.VerifySub.CLoops

  `verify_sub`'s two `mul_range` loops, complete: `__loop84` (the ring switch's target) and
  `__loop85` (Flock's point copied into `z_vals`).
-/

module

public import LeanVM.Guest.B1.VerifySub.CCalls

/-!
# `__loop84`, `__loop85`, complete

* `loop_complete`: `loop_iff`'s backward direction, from the body's completeness alone;
* `loop85_complete`: `__loop85` from `g^k` to its end, every copy honest;
* `loop84_complete`: `__loop84` from `g^0` to `g^64`, every body honest (`Loop84Body`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

/-- **A loop completes** when its body does at every `g^j`, `k ≤ j < m`, and it ends at `g^m`. -/
theorem loop_complete {P : Core.Program} {rd : Reader} {f : String} {ps : List E} {N : E}
    {B : E → Prop}
    (hstep : ∀ d x, B x → IsInK (x * gen + N) → (x * gen + N ≠ 0 → P.relN rd d f (x * gen :: ps) []) →
      P.relN rd (d + 1) f (x :: ps) [])
    {k m : ℕ} (hkm : k < m) (hN : N = gen ^ m) (hfirst : ∀ j, k < j → j < m → gen ^ j ≠ N)
    (hall : ∀ j, k ≤ j → j < m → B (gen ^ j)) : P.Rel rd f (gen ^ k :: ps) [] := by
  obtain ⟨t, rfl⟩ : ∃ t, m = k + 1 + t := ⟨m - k - 1, by omega⟩
  have hK : ∀ j, IsInK (gen ^ j * gen + N) := fun j => by
    rw [hN]; exact isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _)
  refine ⟨t + 1, ?_⟩
  induction t generalizing k with
  | zero =>
    exact hstep 0 _ (hall k le_rfl (by omega)) (hK k)
      (fun h => absurd ((gen_pow_add_eq_zero_iff k).mpr hN) h)
  | succ t ih =>
    refine hstep (t + 1) _ (hall k le_rfl (by omega)) (hK k) fun _ => ?_
    rw [gen_pow_mul_gen]
    exact ih (by omega) (by rw [hN]; congr 1; omega)
      (fun j h1 h2 => hfirst j (by omega) (by omega)) (fun j h1 h2 => hall j (by omega) (by omega))

/-! ## `__loop85` -/

theorem core175_body : Fn.body Data.core175 = Data.core175.body := rfl

theorem loop85_step_complete (rd : Reader) (N zv zr : E) (d : ℕ) (x : E)
    (hb : ∃ v, LoadHolds rd (zr * x) 0 v ∧ LoadHolds rd (zv * x) 0 v) (hK : IsInK (x * gen + N))
    (hn : x * gen + N ≠ 0 → coreProgram.relN rd d "__loop85" (x * gen :: [N, zv, zr]) []) :
    coreProgram.relN rd (d + 1) "__loop85" (x :: [N, zv, zr]) [] := by
  obtain ⟨v, l1, l2⟩ := hb
  rw [relN_succ_iff find_loop85, show Fn.params Data.core175 = [.n 0, .n 1, .n 2, .n 3] from rfl,
    core175_body, Data.core175.body]
  refine ⟨upds (fun _ => 0) [(0, x), (1, N), (2, zv), (3, zr), (4, zr * x), (5, v), (6, zv * x),
    (7, word 2 0 0), (8, x * word 2 0 0), (9, x * word 2 0 0 + N), (10, word 2 0 0),
    (11, x * word 2 0 0)], ?_, ?_⟩
  · simp [upds_n]
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
    vs_ev
    rw [word_gen]
    exact ⟨trivial, l1, trivial, l2, trivial, trivial, trivial, trivial, trivial, ⟨hK, hn, trivial⟩⟩

/-- **`__loop85` from `g^k` to `N = g^m`**, every copy `zv[x] = zr[x]` honest. -/
theorem loop85_complete {rd : Reader} {N zv zr : E} {k m : ℕ} (hkm : k < m) (hm : m < ordG)
    (hN : N = gen ^ m) (hb : ∀ j, k ≤ j → j < m →
      ∃ v, LoadHolds rd (zr * gen ^ j) 0 v ∧ LoadHolds rd (zv * gen ^ j) 0 v) :
    coreProgram.Rel rd "__loop85" (gen ^ k :: [N, zv, zr]) [] :=
  loop_complete (fun d x hx hK hn => loop85_step_complete rd N zv zr d x hx hK hn) hkm hN
    (first_hit_of_lt hm hN) hb

/-! ## `__loop84` -/

/-- Value `i` of a stage of the ring map from `u` with challenge `c` and `d` squarings. -/
def stV (u c : E) (d i : ℕ) : E :=
  if i ≤ d then u ^ 2 ^ i else if i = d + 1 then c else if i = d + 2 then c * u ^ 2 ^ d
  else u + c * u ^ 2 ^ d

theorem holds_l84Stage_complete {C : CallRel} {rd : Reader} {σ : Val} {k : List E → Prop}
    (w d st : ℕ) (u c : E) (hσ : ∀ i ≤ d + 3, σ (.n (w + i)) = stV u c d i)
    (hc : LoadHolds rd (σ (.n 2)) st c) (next : Prop) (hn : next) :
    Stmt.HoldsList C rd σ (l84Stage w d st) next k := by
  rw [holdsList_noRet _ (l84Stage_noRet w d st)]
  refine ⟨?_, hn⟩
  rw [l84Stage, holdsList_append, holdsList_noRet _ (sqChain_noRet _ _), sqChain,
    holdsList_range_flatten d _ (fun _ => rfl)]
  have hs : ∀ i ≤ d, σ (.n (w + i)) = u ^ 2 ^ i := fun i hi => by
    rw [hσ i (by omega)]; simp [stV, hi]
  refine ⟨⟨fun i hi => ⟨?_, trivial⟩, trivial⟩, ?_⟩
  · show σ (.n (w + 1 + i)) = σ (.n (w + i)) * σ (.n (w + i))
    rw [show w + 1 + i = w + (i + 1) by omega, hs (i + 1) (by omega), hs i (by omega), ← pow_two,
      ← pow_mul, pow_succ]
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    have e1 := hσ (d + 1) (by omega)
    have e2 := hσ (d + 2) (by omega)
    have e3 := hσ (d + 3) (by omega)
    simp only [stV, show ¬ d + 1 ≤ d by omega, show ¬ d + 2 ≤ d by omega, show ¬ d + 3 ≤ d by omega,
      show d + 2 ≠ d + 1 by omega, show d + 3 ≠ d + 1 by omega, show d + 3 ≠ d + 2 by omega,
      ↓reduceIte] at e1 e2 e3
    rw [show w + d + 1 = w + (d + 1) by omega, show w + d + 2 = w + (d + 2) by omega,
      show w + d + 3 = w + (d + 3) by omega, e1, e2, e3, ← Nat.add_zero w, Nat.add_assoc,
      Nat.zero_add, hs 0 (by omega), hs d le_rfl]
    simp only [pow_zero, pow_one]
    exact ⟨hc, by first | rfl | trivial, by first | rfl | trivial⟩

/-- The six stages' inputs. -/
def stIn (lin : E) (cs : List E) : ℕ → E
  | 0 => lin
  | k + 1 => stIn lin cs k + cs.getD k 0 * stIn lin cs k ^ 2 ^ (32 >>> k)

theorem phiMap_stIn (lin : E) (cs : List E) (hl : cs.length = 6) : phiMap lin cs = stIn lin cs 6 := by
  obtain ⟨a, b, c, d, e, f, rfl⟩ : ∃ a b c d e f, cs = [a, b, c, d, e, f] := by
    match cs, hl with
    | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩
  rfl

/-- The honest values of `__loop84`'s body at `x` outside the stages. -/
def l84base (x zp mc rs lin xp sm : E) (cs : List E) : Val :=
  upds (fun _ => 0) [(0, x), (1, zp), (2, mc), (3, rs), (4, zp * x), (87, x * x), (88, rs * (x * x)),
    (89, xp), (90, word 2 0 0), (91, xp * word 2 0 0), (92, sm), (93, xp * stIn lin cs 6),
    (94, sm + xp * stIn lin cs 6), (95, word 2 0 0), (96, x * word 2 0 0), (97, word 27 0 0),
    (98, x * word 2 0 0 + word 27 0 0), (99, word 2 0 0), (100, x * word 2 0 0)]

/-- Stage `st`'s values. -/
def l84f (lin : E) (cs : List E) (st : ℕ) : ℕ → E :=
  stV (stIn lin cs st) (cs.getD st 0) (32 >>> st)

/-- The honest valuation of `__loop84`'s body at `x`. -/
def l84σ (x zp mc rs lin xp sm : E) (cs : List E) : Val :=
  setv (setv (setv (setv (setv (setv (l84base x zp mc rs lin xp sm cs) 5 35 (l84f lin cs 0)) 40 19
    (l84f lin cs 1)) 59 11 (l84f lin cs 2)) 70 7 (l84f lin cs 3)) 77 5 (l84f lin cs 4)) 82 5
    (l84f lin cs 5)

theorem core174_params : Fn.params Data.core174 = [.n 0, .n 1, .n 2, .n 3] := rfl

theorem loop84_step_complete (rd : Reader) (zp mc rs : E) (d : ℕ) (x : E)
    (hb : Loop84Body rd zp mc rs x) (hK : IsInK (x * gen + gen ^ 64))
    (hn : x * gen + gen ^ 64 ≠ 0 → coreProgram.relN rd d "__loop84" (x * gen :: [zp, mc, rs]) []) :
    coreProgram.relN rd (d + 1) "__loop84" (x :: [zp, mc, rs]) [] := by
  obtain ⟨lin, xp, sm, cs, hcl, hcs, hlin, h0, h1, h2, h3⟩ := hb
  rw [relN_succ_iff find_loop84, core174_params, core174_body]
  set σ := l84σ x zp mc rs lin xp sm cs
  have hlow : ∀ k, k < 5 → σ (.n k) = l84base x zp mc rs lin xp sm cs (.n k) := fun k hk => by
    simp only [σ, l84σ]
    rw [set_n_lt (b := 82) (n := 5) (show k < 82 by omega), set_n_lt (b := 77) (n := 5) (show k < 77 by omega), set_n_lt (b := 70) (n := 7) (show k < 70 by omega), set_n_lt (b := 59) (n := 11) (show k < 59 by omega), set_n_lt (b := 40) (n := 19) (show k < 40 by omega), set_n_lt (b := 5) (n := 35) (show k < 5 by omega)]
  have hhigh : ∀ k, 87 ≤ k → σ (.n k) = l84base x zp mc rs lin xp sm cs (.n k) := fun k hk => by
    simp only [σ, l84σ]
    rw [set_n_ge (b := 82) (n := 5) (show 82 + 5 ≤ k by omega), set_n_ge (b := 77) (n := 5) (show 77 + 5 ≤ k by omega), set_n_ge (b := 70) (n := 7) (show 70 + 7 ≤ k by omega), set_n_ge (b := 59) (n := 11) (show 59 + 11 ≤ k by omega), set_n_ge (b := 40) (n := 19) (show 40 + 19 ≤ k by omega), set_n_ge (b := 5) (n := 35) (show 5 + 35 ≤ k by omega)]
  have s0' : ∀ i ≤ 32 + 2, σ (.n (5 + i)) = l84f lin cs 0 i := fun i hi => by
    simp only [σ, l84σ]
    rw [set_n_lt (b := 82) (n := 5) (show 5 + i < 82 by omega), set_n_lt (b := 77) (n := 5) (show 5 + i < 77 by omega), set_n_lt (b := 70) (n := 7) (show 5 + i < 70 by omega), set_n_lt (b := 59) (n := 11) (show 5 + i < 59 by omega), set_n_lt (b := 40) (n := 19) (show 5 + i < 40 by omega), set_n_in (show 5 ≤ 5 + i by omega) (show 5 + i < 5 + 35 by omega), Nat.add_sub_cancel_left]
  have s1' : ∀ i ≤ 16 + 2, σ (.n (40 + i)) = l84f lin cs 1 i := fun i hi => by
    simp only [σ, l84σ]
    rw [set_n_lt (b := 82) (n := 5) (show 40 + i < 82 by omega), set_n_lt (b := 77) (n := 5) (show 40 + i < 77 by omega), set_n_lt (b := 70) (n := 7) (show 40 + i < 70 by omega), set_n_lt (b := 59) (n := 11) (show 40 + i < 59 by omega), set_n_in (show 40 ≤ 40 + i by omega) (show 40 + i < 40 + 19 by omega), Nat.add_sub_cancel_left]
  have s2' : ∀ i ≤ 8 + 2, σ (.n (59 + i)) = l84f lin cs 2 i := fun i hi => by
    simp only [σ, l84σ]
    rw [set_n_lt (b := 82) (n := 5) (show 59 + i < 82 by omega), set_n_lt (b := 77) (n := 5) (show 59 + i < 77 by omega), set_n_lt (b := 70) (n := 7) (show 59 + i < 70 by omega), set_n_in (show 59 ≤ 59 + i by omega) (show 59 + i < 59 + 11 by omega), Nat.add_sub_cancel_left]
  have s3' : ∀ i ≤ 4 + 2, σ (.n (70 + i)) = l84f lin cs 3 i := fun i hi => by
    simp only [σ, l84σ]
    rw [set_n_lt (b := 82) (n := 5) (show 70 + i < 82 by omega), set_n_lt (b := 77) (n := 5) (show 70 + i < 77 by omega), set_n_in (show 70 ≤ 70 + i by omega) (show 70 + i < 70 + 7 by omega), Nat.add_sub_cancel_left]
  have s4' : ∀ i ≤ 2 + 2, σ (.n (77 + i)) = l84f lin cs 4 i := fun i hi => by
    simp only [σ, l84σ]
    rw [set_n_lt (b := 82) (n := 5) (show 77 + i < 82 by omega), set_n_in (show 77 ≤ 77 + i by omega) (show 77 + i < 77 + 5 by omega), Nat.add_sub_cancel_left]
  have s5 : ∀ i ≤ 1 + 3, σ (.n (82 + i)) = l84f lin cs 5 i := fun i hi => by
    simp only [σ, l84σ]
    rw [set_n_in (show 82 ≤ 82 + i by omega) (show 82 + i < 82 + 5 by omega), Nat.add_sub_cancel_left]
  have s0 : ∀ i ≤ 32 + 3, σ (.n (5 + i)) = l84f lin cs 0 i := fun i hi => by
    rcases Nat.lt_or_ge i (32 + 3) with h | h
    · exact s0' i (by omega)
    · rw [show i = 32 + 3 by omega, show 5 + (32 + 3) = 40 + 0 by omega, s1' 0 (by omega)]
      simp [l84f, stV, stIn]
  have s1 : ∀ i ≤ 16 + 3, σ (.n (40 + i)) = l84f lin cs 1 i := fun i hi => by
    rcases Nat.lt_or_ge i (16 + 3) with h | h
    · exact s1' i (by omega)
    · rw [show i = 16 + 3 by omega, show 40 + (16 + 3) = 59 + 0 by omega, s2' 0 (by omega)]
      simp [l84f, stV, stIn]
  have s2 : ∀ i ≤ 8 + 3, σ (.n (59 + i)) = l84f lin cs 2 i := fun i hi => by
    rcases Nat.lt_or_ge i (8 + 3) with h | h
    · exact s2' i (by omega)
    · rw [show i = 8 + 3 by omega, show 59 + (8 + 3) = 70 + 0 by omega, s3' 0 (by omega)]
      simp [l84f, stV, stIn]
  have s3 : ∀ i ≤ 4 + 3, σ (.n (70 + i)) = l84f lin cs 3 i := fun i hi => by
    rcases Nat.lt_or_ge i (4 + 3) with h | h
    · exact s3' i (by omega)
    · rw [show i = 4 + 3 by omega, show 70 + (4 + 3) = 77 + 0 by omega, s4' 0 (by omega)]
      simp [l84f, stV, stIn]
  have s4 : ∀ i ≤ 2 + 3, σ (.n (77 + i)) = l84f lin cs 4 i := fun i hi => by
    rcases Nat.lt_or_ge i (2 + 3) with h | h
    · exact s4' i (by omega)
    · rw [show i = 2 + 3 by omega, show 77 + (2 + 3) = 82 + 0 by omega, s5 0 (by omega)]
      simp [l84f, stV, stIn]
  have h2v : σ (.n 2) = mc := by rw [hlow 2 (by omega)]; simp [l84base, upds_n]
  have hc : ∀ st < 6, LoadHolds rd (σ (.n 2)) st (cs.getD st 0) := fun st hs => by
    rw [h2v, List.getD_eq_getElem _ _ (by omega)]; exact hcs st (by omega)
  have h86 : σ (.n 86) = stIn lin cs 6 := by
    have := s5 4 (by omega)
    rw [this]; simp [l84f, stV, stIn]
  have h5 : σ (.n 5) = lin := by
    have := s0 0 (by omega)
    rw [this]; simp [l84f, stV, stIn]
  refine ⟨σ, by simp [hlow, l84base, upds_n], ?_⟩
  rw [l84Body]
  simp only [holdsList_append]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨by rw [hlow 4 (by omega), hlow 1 (by omega), hlow 0 (by omega)]; simp [l84base, upds_n],
    by rw [hlow 4 (by omega), h5]; simp only [l84base]; vs_ev; exact hlin, ?_⟩
  refine holds_l84Stage_complete 5 32 0 _ _ s0 (hc 0 (by omega)) _ ?_
  refine holds_l84Stage_complete 40 16 1 _ _ s1 (hc 1 (by omega)) _ ?_
  refine holds_l84Stage_complete 59 8 2 _ _ s2 (hc 2 (by omega)) _ ?_
  refine holds_l84Stage_complete 70 4 3 _ _ s3 (hc 3 (by omega)) _ ?_
  refine holds_l84Stage_complete 77 2 4 _ _ s4 (hc 4 (by omega)) _ ?_
  refine holds_l84Stage_complete 82 1 5 _ _ s5 (hc 5 (by omega)) _ ?_
  simp only [List.map_cons, List.map_nil, h86, hlow _ (show 0 < 5 by omega), hlow _ (show 1 < 5 by omega), hlow _ (show 2 < 5 by omega),
    hlow _ (show 3 < 5 by omega)]
  simp only [hhigh _ (show 87 ≤ 87 by omega), hhigh _ (show 87 ≤ 88 by omega),
    hhigh _ (show 87 ≤ 89 by omega), hhigh _ (show 87 ≤ 90 by omega), hhigh _ (show 87 ≤ 91 by omega),
    hhigh _ (show 87 ≤ 92 by omega), hhigh _ (show 87 ≤ 93 by omega), hhigh _ (show 87 ≤ 94 by omega),
    hhigh _ (show 87 ≤ 95 by omega), hhigh _ (show 87 ≤ 96 by omega), hhigh _ (show 87 ≤ 97 by omega),
    hhigh _ (show 87 ≤ 98 by omega), hhigh _ (show 87 ≤ 99 by omega),
    hhigh _ (show 87 ≤ 100 by omega), l84base]
  vs_ev
  rw [word_gen, word27, ← phiMap_stIn lin cs hcl]
  exact ⟨trivial, trivial, h0, trivial, trivial, h2, h1, trivial, trivial, h3, trivial, trivial,
    trivial, trivial, trivial, trivial, ⟨hK, hn, trivial⟩⟩

/-- **`__loop84` from `g^0` to `g^64`**, every body honest. -/
theorem loop84_complete {rd : Reader} {zp mc rs : E}
    (hb : ∀ j < 64, Loop84Body rd zp mc rs (gen ^ j)) :
    coreProgram.Rel rd "__loop84" (gen ^ 0 :: [zp, mc, rs]) [] :=
  loop_complete (fun d x hx hK hn => loop84_step_complete rd zp mc rs d x hx hK hn) (by omega) rfl
    (first_hit_of_lt (by decide) rfl) fun j _ hj => hb j hj

end
end LeanVM.Guest.B1.VerifySub
