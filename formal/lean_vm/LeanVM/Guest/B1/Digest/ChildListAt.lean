/-
  LeanVM.Guest.B1.Digest.ChildListAt

  `child_claim_list_digest` complete in the uniform placed form (`CompleteRel` on `CclPreAt`):
  `__loop87`'s iterations and the list itself on explicit runs.
-/

module

public import LeanVM.Guest.B1.Digest.ChildAt

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1 (LowDef CompleteAt CompleteRel Within Returns)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## `__loop87` -/

/-- The honest values of `__loop87` at `x`. -/
def l87List (x W c base entries cover origin limit gsq s0 s1 bs o0 o1 nxt : E) : List E :=
  [x, W, c, base, entries, cover, origin, limit, gsq, x * x, x * x * (x * x),
    c * (x * x * (x * x)), x * x, x * x * (x * x), x * x * (x * x) * (x * x * (x * x)),
    x * x * (x * x) * (x * x * (x * x)) * (x * x * (x * x) * (x * x * (x * x))), pow32 x,
    base * pow32 x, s0, s1, bs, o0, o1, nxt, word 2 0 0, x * word 2 0 0,
    x * word 2 0 0 * (x * word 2 0 0),
    x * word 2 0 0 * (x * word 2 0 0) * (x * word 2 0 0 * (x * word 2 0 0)),
    c * (x * word 2 0 0 * (x * word 2 0 0) * (x * word 2 0 0 * (x * word 2 0 0))), word 2 0 0,
    x * word 2 0 0, x * word 2 0 0 + W, word 2 0 0, x * word 2 0 0]

theorem l87_holds {rd : Reader} {C : CallRel} {x W c base entries cover origin limit gsq s0 s1 bs o0 o1 nxt : E}
    (hs : CellsAt rd (c * (x * x * (x * x))) [s0, s1, bs])
    (hcall : C "child_claims_window" [s0, s1, bs, entries, cover, base * pow32 x, origin, limit, x, gsq] [o0, o1, nxt])
    (ho : CellsAt rd (c * (x * gen * (x * gen) * (x * gen * (x * gen)))) [o0, o1, nxt])
    (hk : IsInK (x * gen + W))
    (hnext : x * gen + W ≠ 0 → C "__loop87" (x * gen :: [W, c, base, entries, cover, origin, limit, gsq]) []) :
    Stmt.HoldsList C rd (listVal (l87List x W c base entries cover origin limit gsq s0 s1 bs o0 o1 nxt)) l87Body
      False (fun rs => rs = []) := by
  rw [cellsAt_three] at hs ho
  obtain ⟨l18, l19, l20⟩ := hs
  obtain ⟨l21, l22, l23⟩ := ho
  simp only [l87Body, List.cons_append, List.nil_append, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  simp only [l87List, listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
  rw [← word_gen] at l21 l22 l23 hk hnext
  exact ⟨rfl, l18, l19, l20, hcall, l21, l22, l23, hk, hnext, trivial⟩

def l87S : List Stmt := l87Body.dropLast

theorem l87Body_eq : l87Body = l87S ++ [.ret []] := rfl

theorem l87S_straight : l87S.all Main.Stmt.straight = true := by decide +kernel

theorem l87_events (σ : Val) :
    calls (l87S.flatMap (Main.slEvs σ)) = [⟨"child_claims_window",
        [.n 18, .n 19, .n 20, .n 4, .n 5, .n 17, .n 6, .n 7, .n 0, .n 8], [.n 21, .n 22, .n 23], true⟩,
      ⟨"__loop87", [.n 33, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8], [], decide (σ (.n 31) ≠ 0)⟩] ∧
    addrs (l87S.flatMap (Main.slEvs σ)) = [] ∧ allocs σ (l87S.flatMap (Main.slEvs σ)) = [] ∧
    allocDsts (l87S.flatMap (Main.slEvs σ)) = [] ∧
    loadAddrs σ (l87S.flatMap (Main.slEvs σ)) = ([(.n 11, 0), (.n 11, 1), (.n 11, 2), (.n 28, 0), (.n 28, 1),
      (.n 28, 2)] : List (V × ℕ)).map fun q => (σ q.1).limb 0 * gpow q.2 := by
  obtain ⟨h1, h2, h3, h4⟩ := Main.straight_parts σ _ l87S_straight
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h4, show l87S.filterMap Main.Stmt.callS = [(none, "child_claims_window",
        [.n 18, .n 19, .n 20, .n 4, .n 5, .n 17, .n 6, .n 7, .n 0, .n 8], [.n 21, .n 22, .n 23]),
        (some (.n 31), "__loop87", [.n 33, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8], [])] by decide +kernel]
    rfl
  · rw [h3]; decide +kernel
  · rw [h2, show l87S.filterMap Main.Stmt.allocSz = [] by decide +kernel]; rfl
  · rw [h1, show l87S.filterMap Main.Stmt.allocSz = [] by decide +kernel]; rfl
  · rw [loadAddrs_straight σ _ l87S_straight, show l87S.filterMap stmtLoad? = [(.n 11, 0), (.n 11, 1), (.n 11, 2),
      (.n 28, 0), (.n 28, 1), (.n 28, 2)] by decide +kernel]

/-- **The windows hold** on a memory defined below `2^16` holding the squares table, the reads and
the scratch table. -/
theorem l87_steps_low {rd : Reader} (hl : Low16 rd) {gsq : E} (hT : SquaresAt rd gsq) {c base entries cover origin : E}
    {L n w : ℕ} (hL16 : L ≤ 2 ^ 16) (hn : n < 2 ^ 16) (hw : 32 * w ≤ n) {off : ℕ → ℕ} {cs : List E}
    (hlen : cs.length = 4 * n) (hR : ChildReads rd entries cover base origin (gen ^ L) off cs n)
    (hcan : ∀ x ∈ cs, IsCanonical128 x) (hscr : ChildScratch rd c cs w) :
    ∀ j < w, L87Step rd c base entries cover origin (gen ^ L) gsq (coreProgram.Rel rd) (gen ^ j) := by
  have hb := blocks_canonical hlen hcan
  intro j hj
  have h0 := cellsAt_three.mp (hscr j (by omega))
  have h1 := hscr (j + 1) (by omega)
  rw [show 32 * (j + 1) = 32 * j + 32 by ring] at h1
  refine ⟨_, _, _, (digestScalars (prefixDigest cs (32 * j + 32))).1,
    (digestScalars (prefixDigest cs (32 * j + 32))).2, eOfNat (2 ^ 11 * (j + 1)),
    by rw [pow4_eq _ j rfl]; exact cellsAt_three.mpr h0, ?_,
    by rw [← pow_succ, pow4_eq _ (j + 1) rfl]; exact h1⟩
  obtain ⟨σ, hp, hH, -, -, -, -⟩ := ccw_run hl hT hL16 rfl (marks := base * pow32 (gen ^ j)) (entries := entries)
    (cover := cover) (origin := origin) (xq := gen ^ j) (N := j + 1) (by omega) (pow_succ gen j).symm rfl
    (off := fun k => off (32 * j + k)) (cs := sliceOf cs (32 * j) 32)
    (by rw [pow32_eq]; exact childReads_slice hR (32 * j) 32 (by omega))
    ((chainCells_prefix (blocksOf_sliceOf cs (32 * j) 32) (fun i hi => windowMd_eq j i hi)).mpr
      ⟨fun i hi r => hb _ (by omega) r, rfl⟩)
  exact (rel_of_find find_child_claims_window _ _).mpr ⟨σ, hp, hH⟩

theorem childLoad_shift {entries cover origin : E} {off : ℕ → ℕ} {b m n : ℕ} (h : b + m ≤ n) {A : K}
    (hA : ChildLoad entries cover origin (fun k => off (b + k)) m A) : ChildLoad entries cover origin off n A := by
  rcases hA with ⟨j, hj, rfl⟩ | ⟨j, hj, r, hr, rfl⟩
  · exact Or.inl ⟨b + j, by omega, rfl⟩
  · exact Or.inr ⟨b + j, by omega, r, hr, rfl⟩

/-- The windows' scratch slot `q` of a child's list. -/
def cclSlot (cs : List E) (q : ℕ) : List E :=
  [(digestScalars (prefixDigest cs (32 * q))).1, (digestScalars (prefixDigest cs (32 * q))).2, eOfNat (2 ^ 11 * q)]

/-- **One iteration of `__loop87`, complete**, from the next one's. -/
theorem l87_iter (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (KL : Layout)
    {gsq base entries cover origin : E} {cx L n w : ℕ} (hL16 : L ≤ 2 ^ 16) (hn : n < 2 ^ 16) (hw : 32 * w ≤ n)
    {off : ℕ → ℕ} {cs : List E} (hlen : cs.length = 4 * n) (hcan : ∀ x ∈ cs, IsCanonical128 x)
    (hR : ∀ rd, LowDef κ rd → MemL rd KL → ChildReads rd entries cover base origin (gen ^ L) off cs n)
    (hsq : ∀ rd, MemL rd KL → SquaresAt rd gsq)
    (hscr : ∀ rd, MemL rd KL → ChildScratch rd (gen ^ cx) cs w)
    (hreg : ∀ A, ChildLoad entries cover origin off n A → ∃ i, A = gpow i ∧ RegionL KL i)
    (hsR : ∀ q ≤ w, ∀ r < 3, RegionL KL (cx + 4 * q + r)) {j : ℕ} (hj : j < w)
    (hnext : j + 1 < w → CompleteAt fs cert κ "__loop87" KL
      [gen ^ (j + 1), gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq] (Returns [])) :
    CompleteAt fs cert κ "__loop87" KL
      [gen ^ j, gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq] (Returns []) := by
  have hb := blocks_canonical hlen hcan
  have hlow : ∀ rd, LowDef κ rd → Low16 rd := fun rd hl i hi =>
    hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ))
  have hch : ChainCells ((digestScalars (prefixDigest cs (32 * j))).1, (digestScalars (prefixDigest cs (32 * j))).2)
      (blocksOf (sliceOf cs (32 * j) 32)) (windowMd (eOfNat (2 ^ 11 * j)) (eOfNat (2 ^ 11 * (j + 1)))) 32
      ((digestScalars (prefixDigest cs (32 * j + 32))).1, (digestScalars (prefixDigest cs (32 * j + 32))).2) :=
    (chainCells_prefix (blocksOf_sliceOf cs (32 * j) 32) (fun i hi => windowMd_eq j i hi)).mpr
      ⟨fun i hi r => hb _ (by omega) r, rfl⟩
  have hRj : ∀ rd, LowDef κ rd → MemL rd KL → ChildReads rd entries cover (base * pow32 (gen ^ j)) origin (gen ^ L)
      (fun k => off (32 * j + k)) (sliceOf cs (32 * j) 32) 32 := fun rd hl hL => by
    rw [pow32_eq]; exact childReads_slice (hR rd hl hL) (32 * j) 32 (by omega)
  refine completeAt_loop find_loop87 (by rw [Program.loop_of_find? find_loop87]; decide +kernel) κ KL _ []
    [⟨"child_claims_window", true, cclSlot cs j ++ [entries, cover, base * pow32 (gen ^ j), origin, gen ^ L, gen ^ j, gsq],
      KL, [(digestScalars (prefixDigest cs (32 * j + 32))).1, (digestScalars (prefixDigest cs (32 * j + 32))).2,
        eOfNat (2 ^ 11 * (j + 1))]⟩]
    ⟨"__loop87", decide (gen ^ j * word 2 0 0 + gen ^ w ≠ 0),
      [gen ^ (j + 1), gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq], KL, []⟩ ?_ ?_ ?_ ?_
  · intro k hk _
    simp only [List.mem_singleton] at hk
    subst hk
    exact ccw_completeAt fs cert hκ KL hL16 rfl (N := j + 1) (by omega) (pow_succ gen j).symm rfl hRj hsq
      (fun A hA => hreg A (childLoad_shift (by omega) hA)) hch
  · intro ht
    refine hnext ?_
    have : gen ^ j * word 2 0 0 + gen ^ w ≠ 0 := by simpa using ht
    rw [word_gen, ← pow_succ] at this
    by_contra h
    exact this (by rw [show w = j + 1 by omega]; exact e_add_self _)
  · intro k _ _ i hi
    simp only [List.mem_append, List.mem_singleton] at *
    rcases ‹_ ∨ _› with rfl | rfl <;> exact hi
  intro rd hl hL
  refine ⟨fun k hk => by simp only [List.mem_append, List.mem_singleton] at hk; rcases hk with rfl | rfl <;> exact hL, ?_⟩
  have hT := hsq rd hL
  have hs := hscr rd hL j (by omega)
  have ho := hscr rd hL (j + 1) (by omega)
  obtain ⟨σw, hpw, hHw, -, -, -, -⟩ := ccw_run (hlow rd hl) hT hL16 rfl (marks := base * pow32 (gen ^ j))
    (entries := entries) (cover := cover) (origin := origin) (xq := gen ^ j) (N := j + 1) (by omega)
    (pow_succ gen j).symm rfl (hRj rd hl hL) hch
  have hcall := (rel_of_find find_child_claims_window _ _).mpr ⟨σw, hpw, hHw⟩
  have hsteps := l87_steps_low (hlow rd hl) hT hL16 hn hw hlen (hR rd hl hL) hcan (hscr rd hL)
  have hk : IsInK (gen ^ j * gen + gen ^ w) := by
    rw [← pow_succ, gen_pow_eq_ofK, gen_pow_eq_ofK, ← ofK_add]; exact ofK_isInK _
  have hnx : gen ^ j * gen + gen ^ w ≠ 0 → coreProgram.Rel rd "__loop87"
      (gen ^ j * gen :: [gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq]) [] := fun h => by
    rw [← pow_succ] at h ⊢
    have hjw : j + 1 < w := by
      by_contra h'
      exact h (by rw [show w = j + 1 by omega]; exact e_add_self _)
    exact (loop87_iff rd _ _ _ _ _ _ _ _ (j + 1)).mpr ⟨w, hjw, rfl,
      fun i h1 h2 he => by have := gen_pow_inj' (by omega) (by omega) he; omega, fun i _ h2 => hsteps i h2⟩
  have hh := l87_holds (C := coreProgram.Rel rd) (W := gen ^ w)
    (by rw [pow4_eq _ j rfl]; exact hs) hcall (by rw [← pow_succ, pow4_eq _ (j + 1) rfl]; exact ho) hk hnx
  set σ := listVal (l87List (gen ^ j) (gen ^ w) (gen ^ cx) base entries cover origin (gen ^ L) gsq
    (digestScalars (prefixDigest cs (32 * j))).1 (digestScalars (prefixDigest cs (32 * j))).2 (eOfNat (2 ^ 11 * j))
    (digestScalars (prefixDigest cs (32 * j + 32))).1 (digestScalars (prefixDigest cs (32 * j + 32))).2
    (eOfNat (2 ^ 11 * (j + 1)))) with hσ
  have hwk : walk σ l87Body = .ret (l87S.flatMap (Main.slEvs σ)) [] := by
    rw [l87Body_eq]; exact Main.walk_straight σ _ _ l87S_straight
  obtain ⟨e1, e2, e3, e4, e5⟩ := l87_events σ
  refine ⟨σ, _, [], rfl, hwk, rfl, holds_of_holdsList find_loop87 hh hwk, ?_, e2, e3, e4, fun A hA => ?_⟩
  · rw [e1]
    refine ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩, rfl, rfl, fun _ => ⟨?_, rfl⟩, trivial⟩
    show [gen ^ j * word 2 0 0, _, _, _, _, _, _, _, _] = _
    rw [word_gen, ← pow_succ]
    rfl
  · rw [e5] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    have g11 : σ (.n 11) = gen ^ (cx + 4 * j) := by
      show gen ^ cx * (gen ^ j * gen ^ j * (gen ^ j * gen ^ j)) = _
      rw [pow4_eq _ j rfl, ← pow_add]
    have g28 : σ (.n 28) = gen ^ (cx + 4 * (j + 1)) := by
      show gen ^ cx * (gen ^ j * word 2 0 0 * (gen ^ j * word 2 0 0) *
        (gen ^ j * word 2 0 0 * (gen ^ j * word 2 0 0))) = _
      rw [word_gen, ← pow_succ, pow4_eq _ (j + 1) rfl, ← pow_add]
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by rw [g11, limb0_gen_pow, gpow_add'], hsR j (by omega) 0 (by omega)⟩
    · exact ⟨_, by rw [g11, limb0_gen_pow, gpow_add'], hsR j (by omega) 1 (by omega)⟩
    · exact ⟨_, by rw [g11, limb0_gen_pow, gpow_add'], hsR j (by omega) 2 (by omega)⟩
    · exact ⟨_, by rw [g28, limb0_gen_pow, gpow_add'], hsR (j + 1) (by omega) 0 (by omega)⟩
    · exact ⟨_, by rw [g28, limb0_gen_pow, gpow_add'], hsR (j + 1) (by omega) 1 (by omega)⟩
    · exact ⟨_, by rw [g28, limb0_gen_pow, gpow_add'], hsR (j + 1) (by omega) 2 (by omega)⟩

/-- **`__loop87`'s iterations are complete, uniformly placed.** -/
theorem l87_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (KL : Layout)
    {gsq base entries cover origin : E} {cx L n w : ℕ} (hL16 : L ≤ 2 ^ 16) (hn : n < 2 ^ 16) (hw : 32 * w ≤ n)
    {off : ℕ → ℕ} {cs : List E} (hlen : cs.length = 4 * n) (hcan : ∀ x ∈ cs, IsCanonical128 x)
    (hR : ∀ rd, LowDef κ rd → MemL rd KL → ChildReads rd entries cover base origin (gen ^ L) off cs n)
    (hsq : ∀ rd, MemL rd KL → SquaresAt rd gsq)
    (hscr : ∀ rd, MemL rd KL → ChildScratch rd (gen ^ cx) cs w)
    (hreg : ∀ A, ChildLoad entries cover origin off n A → ∃ i, A = gpow i ∧ RegionL KL i)
    (hsR : ∀ q ≤ w, ∀ r < 3, RegionL KL (cx + 4 * q + r)) :
    ∀ j < w, CompleteAt fs cert κ "__loop87" KL
      [gen ^ j, gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq] (Returns []) := by
  suffices H : ∀ d j, j + d + 1 = w → CompleteAt fs cert κ "__loop87" KL
      [gen ^ j, gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq] (Returns []) from
    fun j hj => H (w - j - 1) j (by omega)
  intro d
  induction d with
  | zero =>
    exact fun j hj => l87_iter fs cert hκ KL hL16 hn hw hlen hcan hR hsq hscr hreg hsR (j := j) (by omega)
      (fun h => absurd h (by omega))
  | succ d ih =>
    exact fun j hj => l87_iter fs cert hκ KL hL16 hn hw hlen hcan hR hsq hscr hreg hsR (j := j) (by omega)
      (fun _ => ih (j + 1) (by omega))

end
end LeanVM.Guest.B1.Digest
