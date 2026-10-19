/-
  LeanVM.Guest.B1.Digest.ChildListAt

  `child_claim_list_digest` complete in the uniform placed form (`CompleteRel` on `CclPreAt`):
  `__loop87`'s iterations and the list itself on explicit runs.
-/

module

public import LeanVM.Guest.Memory.Size
public import LeanVM.Guest.B1.Digest.ChildAt

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1 (LowDef CompleteAt CompleteAtD CompleteAtB kidsBound CompleteRel CompleteRelD DisjL disj_nil disj_append Within Returns)
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

/-- The bound of `__loop87` from iteration `j`: the iterations left, each its frame and one window
(at most `Kc`), plus the skipped tail's frame. -/
def l87Bound (fs : String → ℕ) (Kc w j : ℕ) : ℕ := (w - j) * (fs "__loop87" + Kc) + fs "__loop87"

theorem l87Bound_step (fs : String → ℕ) (Kc w j : ℕ) (hj : j < w) :
    fs "__loop87" + max (l87Bound fs Kc w (j + 1)) (fs "__loop87") + Kc ≤ l87Bound fs Kc w j := by
  obtain ⟨d, hd⟩ : ∃ d, w - j = d + 1 := ⟨w - j - 1, by omega⟩
  have e : w - (j + 1) = d := by omega
  have hm : max (l87Bound fs Kc w (j + 1)) (fs "__loop87") = l87Bound fs Kc w (j + 1) :=
    Nat.max_eq_left (Nat.le_add_left _ _)
  rw [hm]
  simp only [l87Bound, hd, e, Nat.succ_mul]
  omega

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

/-- **One iteration of `__loop87`, complete**, from the next one's. -/
theorem l87_iterD (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (KL : Layout)
    {gsq base entries cover origin : E} {cx L n w : ℕ} (hL16 : L ≤ 2 ^ 16) (hn : n < 2 ^ 16) (hw : 32 * w ≤ n)
    {off : ℕ → ℕ} {cs : List E} (hlen : cs.length = 4 * n) (hcan : ∀ x ∈ cs, IsCanonical128 x)
    (hR : ∀ rd, LowDef κ rd → MemL rd KL → ChildReads rd entries cover base origin (gen ^ L) off cs n)
    (hsq : ∀ rd, MemL rd KL → SquaresAt rd gsq)
    (hscr : ∀ rd, MemL rd KL → ChildScratch rd (gen ^ cx) cs w)
    (hreg : ∀ A, ChildLoad entries cover origin off n A → ∃ i, A = gpow i ∧ RegionL KL i)
    (hsR : ∀ q ≤ w, ∀ r < 3, RegionL KL (cx + 4 * q + r)) {j : ℕ} (hj : j < w)
    (hnext : j + 1 < w → CompleteAtD fs cert κ "__loop87" KL
      [gen ^ (j + 1), gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq] (Returns [])) :
    CompleteAtD fs cert κ "__loop87" KL
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
  refine completeAt_loopD find_loop87 (by rw [Program.loop_of_find? find_loop87]; decide +kernel) κ KL _ []
    [⟨"child_claims_window", true, cclSlot cs j ++ [entries, cover, base * pow32 (gen ^ j), origin, gen ^ L, gen ^ j, gsq],
      KL, [(digestScalars (prefixDigest cs (32 * j + 32))).1, (digestScalars (prefixDigest cs (32 * j + 32))).2,
        eOfNat (2 ^ 11 * (j + 1))]⟩]
    ⟨"__loop87", decide (gen ^ j * word 2 0 0 + gen ^ w ≠ 0),
      [gen ^ (j + 1), gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq], KL, []⟩ ?_ ?_ ?_ ?_
  · intro k hk _
    simp only [List.mem_singleton] at hk
    subst hk
    exact ccw_completeAtD fs cert hκ KL hL16 rfl (N := j + 1) (by omega) (pow_succ gen j).symm rfl hRj hsq
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

/-- **`__loop87`'s iterations are complete, uniformly placed.** -/
theorem l87_completeAtD (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (KL : Layout)
    {gsq base entries cover origin : E} {cx L n w : ℕ} (hL16 : L ≤ 2 ^ 16) (hn : n < 2 ^ 16) (hw : 32 * w ≤ n)
    {off : ℕ → ℕ} {cs : List E} (hlen : cs.length = 4 * n) (hcan : ∀ x ∈ cs, IsCanonical128 x)
    (hR : ∀ rd, LowDef κ rd → MemL rd KL → ChildReads rd entries cover base origin (gen ^ L) off cs n)
    (hsq : ∀ rd, MemL rd KL → SquaresAt rd gsq)
    (hscr : ∀ rd, MemL rd KL → ChildScratch rd (gen ^ cx) cs w)
    (hreg : ∀ A, ChildLoad entries cover origin off n A → ∃ i, A = gpow i ∧ RegionL KL i)
    (hsR : ∀ q ≤ w, ∀ r < 3, RegionL KL (cx + 4 * q + r)) :
    ∀ j < w, CompleteAtD fs cert κ "__loop87" KL
      [gen ^ j, gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq] (Returns []) := by
  suffices H : ∀ d j, j + d + 1 = w → CompleteAtD fs cert κ "__loop87" KL
      [gen ^ j, gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq] (Returns []) from
    fun j hj => H (w - j - 1) j (by omega)
  intro d
  induction d with
  | zero =>
    exact fun j hj => l87_iterD fs cert hκ KL hL16 hn hw hlen hcan hR hsq hscr hreg hsR (j := j) (by omega)
      (fun h => absurd h (by omega))
  | succ d ih =>
    exact fun j hj => l87_iterD fs cert hκ KL hL16 hn hw hlen hcan hR hsq hscr hreg hsR (j := j) (by omega)
      (fun _ => ih (j + 1) (by omega))

/-! ## `child_claim_list_digest` -/

/-- **One iteration of `__loop87`, complete**, from the next one's. -/
theorem l87_iterB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (KL : Layout)
    {gsq base entries cover origin : E} {cx L n w : ℕ} (hL16 : L ≤ 2 ^ 16) (hn : n < 2 ^ 16) (hw : 32 * w ≤ n)
    {off : ℕ → ℕ} {cs : List E} (hlen : cs.length = 4 * n) (hcan : ∀ x ∈ cs, IsCanonical128 x)
    (hR : ∀ rd, LowDef κ rd → MemL rd KL → ChildReads rd entries cover base origin (gen ^ L) off cs n)
    (hsq : ∀ rd, MemL rd KL → SquaresAt rd gsq)
    (hscr : ∀ rd, MemL rd KL → ChildScratch rd (gen ^ cx) cs w)
    (hreg : ∀ A, ChildLoad entries cover origin off n A → ∃ i, A = gpow i ∧ RegionL KL i)
    (hsR : ∀ q ≤ w, ∀ r < 3, RegionL KL (cx + 4 * q + r)) (Bsl : ℕ)
    (hsl : TotalLe coreProgram fs "scaled_log__L11" fun _ => Bsl) {j : ℕ} (hj : j < w)
    (hnext : j + 1 < w → CompleteAtB fs cert κ "__loop87" KL
      [gen ^ (j + 1), gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq] (Returns [])
      (l87Bound fs (fs "child_claims_window" + Bsl) w (j + 1))) :
    CompleteAtB fs cert κ "__loop87" KL
      [gen ^ j, gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq] (Returns [])
      (l87Bound fs (fs "child_claims_window" + Bsl) w j) := by
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
  refine completeAt_loopB find_loop87 (by rw [Program.loop_of_find? find_loop87]; decide +kernel) κ KL _ []
    [⟨"child_claims_window", true, cclSlot cs j ++ [entries, cover, base * pow32 (gen ^ j), origin, gen ^ L, gen ^ j, gsq],
      KL, [(digestScalars (prefixDigest cs (32 * j + 32))).1, (digestScalars (prefixDigest cs (32 * j + 32))).2,
        eOfNat (2 ^ 11 * (j + 1))]⟩]
    ⟨"__loop87", decide (gen ^ j * word 2 0 0 + gen ^ w ≠ 0),
      [gen ^ (j + 1), gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq], KL, []⟩
    (fun _ => fs "child_claims_window" + Bsl) (l87Bound fs (fs "child_claims_window" + Bsl) w (j + 1)) ?_ ?_
    (l87Bound fs (fs "child_claims_window" + Bsl) w j)
    (by simpa [kidsBound, KidR.kid] using l87Bound_step fs (fs "child_claims_window" + Bsl) w j hj) ?_ ?_
  · intro k hk _
    simp only [List.mem_singleton] at hk
    subst hk
    exact ccw_completeAtB fs cert hκ KL hL16 rfl (N := j + 1) (by omega) (pow_succ gen j).symm rfl hRj hsq
      (fun A hA => hreg A (childLoad_shift (by omega) hA)) hch Bsl hsl
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
theorem l87_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (KL : Layout)
    {gsq base entries cover origin : E} {cx L n w : ℕ} (hL16 : L ≤ 2 ^ 16) (hn : n < 2 ^ 16) (hw : 32 * w ≤ n)
    {off : ℕ → ℕ} {cs : List E} (hlen : cs.length = 4 * n) (hcan : ∀ x ∈ cs, IsCanonical128 x)
    (hR : ∀ rd, LowDef κ rd → MemL rd KL → ChildReads rd entries cover base origin (gen ^ L) off cs n)
    (hsq : ∀ rd, MemL rd KL → SquaresAt rd gsq)
    (hscr : ∀ rd, MemL rd KL → ChildScratch rd (gen ^ cx) cs w)
    (hreg : ∀ A, ChildLoad entries cover origin off n A → ∃ i, A = gpow i ∧ RegionL KL i)
    (hsR : ∀ q ≤ w, ∀ r < 3, RegionL KL (cx + 4 * q + r)) (Bsl : ℕ)
    (hsl : TotalLe coreProgram fs "scaled_log__L11" fun _ => Bsl) :
    ∀ j < w, CompleteAtB fs cert κ "__loop87" KL
      [gen ^ j, gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq] (Returns [])
      (l87Bound fs (fs "child_claims_window" + Bsl) w j) := by
  suffices H : ∀ d j, j + d + 1 = w → CompleteAtB fs cert κ "__loop87" KL
      [gen ^ j, gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq] (Returns [])
      (l87Bound fs (fs "child_claims_window" + Bsl) w j) from
    fun j hj => H (w - j - 1) j (by omega)
  intro d
  induction d with
  | zero =>
    exact fun j hj => l87_iterB fs cert hκ KL hL16 hn hw hlen hcan hR hsq hscr hreg hsR Bsl hsl (j := j) (by omega)
      (fun h => absurd h (by omega))
  | succ d ih =>
    exact fun j hj => l87_iterB fs cert hκ KL hL16 hn hw hlen hcan hR hsq hscr hreg hsR Bsl hsl (j := j) (by omega)
      (fun _ => ih (j + 1) (by omega))

/-! ## `child_claim_list_digest` -/

theorem cct_rel_low {rd : Reader} (hl : Low16 rd) (k : ℕ) (hk : k < 32)
    {s0 s1 base entries cover marks origin limit o0 o1 : E} {L : ℕ} (hL16 : L ≤ 2 ^ 16)
    (hlim : limit = gen ^ L) {off : ℕ → ℕ} {cs : List E}
    (hR : ChildReads rd entries cover marks origin limit off cs k)
    (hch : ChainCells (s0, s1) (blocksOf cs) (baseMd base) k (o0, o1)) :
    coreProgram.Rel rd (cctNames.getD k "") [s0, s1, base, entries, cover, marks, origin, limit] [o0, o1] := by
  rw [rel_of_find (find_child_claims_tail k hk)]
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact (child_tail_zero_iff rd _ _ _).mpr ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, off, [], rfl,
      fun j hj => absurd hj (by omega), by
        rcases hch with ⟨_, h⟩ | ⟨h, _⟩
        · exact Or.inl ⟨rfl, h⟩
        · omega⟩
  · obtain ⟨σ, hp, hh, hr, -⟩ := cct_run hl k hk1 hk hL16 hlim hR hch
    refine ⟨σ, hp, ?_⟩
    simp only [show ¬k = 0 by omega, ↓reduceIte]
    rw [cctBody_eq, holdsList_atoms, holdsList_ret]
    exact ⟨hh, hr⟩

/-- **`child_claim_list_digest`'s body holds**, `n ≥ 1`, at its honest values, on a memory defined
below `2^16` holding the squares table, the reads and the windows' scratch table at `c`. -/
theorem ccld_holds_pos {rd : Reader} (hl : Low16 rd) {gsq : E} (hT : SquaresAt rd gsq)
    {entries cover base origin c : E} {L n : ℕ} (hL16 : L ≤ 2 ^ 16) (hn : n < 2 ^ 16) (hn1 : 0 < n)
    {off : ℕ → ℕ} {cs : List E} (hlen : cs.length = 4 * n)
    (hR : ChildReads rd entries cover base origin (gen ^ L) off cs n) (hcan : ∀ x ∈ cs, IsCanonical128 x)
    (hscr : ChildScratch rd c cs ((n - 1) / 32)) {d0 d1 : E}
    (hd : (d0, d1) = digestScalars (blake2sBytes (cs.flatMap cellBytes))) :
    ∃ t1 t2 t3 t4 t5 t6, Stmt.HoldsList (coreProgram.Rel rd) rd
      (listVal (cclList entries cover base origin (gen ^ L) gsq c d0 d1 cs (off (n - 1)) L n ((n - 1) / 32)
        ((n - 1) % 32) t1 t2 t3 t4 t5 t6)) ccldBody False (fun rs => rs = [d0, d1]) := by
  set w := (n - 1) / 32 with hw
  set t := (n - 1) % 32 with ht
  have hwt : n = 32 * w + t + 1 := by omega
  have ht32 : t < 32 := by omega
  have hw2 : w < 2048 := by omega
  have hoff : ∀ j < n, off j < L := fun j hj => by
    obtain ⟨⟨L', hL', hlim', ho⟩, -⟩ := hR j hj
    have := gen_pow_inj (a := L) (b := L') (by omega) (by omega) hlim'
    omega
  obtain ⟨t1, t2, l22, -, l23⟩ := rangeCheck_complete_low hl (e := t) (e' := 31 - t) (by omega) (by omega)
  obtain ⟨t3, t4, l26, -, l27⟩ := rangeCheck_complete_low hl (e := w) (e' := 2047 - w) (by omega) (by omega)
  obtain ⟨t5, t6, l65, -, l66⟩ := rangeCheck_complete_low hl (e := off (n - 1)) (e' := L - 1 - off (n - 1))
    (lt_of_lt_of_le (hoff _ (by omega)) hL16) (by omega)
  have hS := fun q (hq : q ≤ w) => cellsAt_three.mp (hscr q hq)
  obtain ⟨s00, s01, s02⟩ := hS 0 (by omega)
  obtain ⟨sw0, sw1, sw2⟩ := hS w le_rfl
  simp only [Nat.mul_zero, pow_zero, mul_one, eOfNat_zero] at s00 s01 s02
  rw [← pow4_eq _ w rfl] at sw0 sw1 sw2
  have hb := blocks_canonical hlen hcan
  have hsteps := l87_steps_low hl hT hL16 hn (by omega) hlen hR hcan hscr
  have hlast : ![cs.getD (4 * (n - 1) + 0) 0, cs.getD (4 * (n - 1) + 1) 0,
      cs.getD (4 * (n - 1) + 2) 0, cs.getD (4 * (n - 1) + 3) 0] = blocksOf cs (n - 1) := by
    simp [blocksOf]
  have hmd : eOfNat (2 ^ 6 * n) + word 0 4294967295 0 = metadataCell (64 * n) true := by
    rw [md_final_word, eOfNat_add_metadataCell, Nat.xor_zero]; rfl
  have hinv : gen ^ n * wInv = gen ^ (n - 1) := by
    rw [show gen ^ n = gen ^ (n - 1) * gen by rw [← pow_succ]; congr 1; omega, mul_assoc, mul_comm gen,
      ginv_mul_gen, mul_one]
  obtain ⟨-, hmark, hcl⟩ := hR (n - 1) (by omega)
  refine ⟨t1, t2, t3, t4, t5, t6, ?_⟩
  simp only [ccldBody, List.cons_append, List.nil_append, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, true_and, List.map_cons, List.map_nil]
  refine ⟨rfl, rfl, ?_, fun h => ?_, fun _ => ?_⟩
  · show IsInK (gen ^ n + word 1 0 0)
    rw [word_one, gen_pow_eq_ofK, ← ofK_one, ← ofK_add]; exact ofK_isInK _
  · exfalso
    have h' : gen ^ n + word 1 0 0 = 0 := h
    rw [word_one] at h'
    have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h')
    omega
  refine ⟨rfl, ⟨l22, ?_, l23⟩, rfl, ⟨l26, ?_, l27⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_,
    rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_, rfl, ?_, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, ⟨l65, ?_, l66⟩, rfl, rfl, rfl, rfl, rfl, ?_, rfl,
    rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  all_goals simp only [listVal, cclList, List.getD_cons_succ, List.getD_cons_zero]
  · rw [word_g31, ← pow_add]; congr 1; omega
  · rw [word_g2047, ← pow_add]; congr 1; omega
  · rw [pow32_eq, hinv, ← pow_add, show 32 * w + t = n - 1 by omega, e_add_self]
  · rw [iv0_word]; exact s00
  · rw [iv1_word]; exact s01
  · rw [word_zero]; exact s02
  · rw [word_one, gen_pow_eq_ofK, ← ofK_one, ← ofK_add]; exact ofK_isInK _
  · intro h
    rw [word_one, ← pow_zero gen]
    have hw0 : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · exfalso; apply h; rw [h0, word_one, pow_zero, e_add_self]
      · exact h0
    exact (loop_iff (l87Step_mono rd c base entries cover origin (gen ^ L) gsq)
      (l87_step rd (gen ^ w) c base entries cover origin (gen ^ L) gsq) 0).mpr
      ⟨w, hw0, rfl, fun j h1 h2 he => by have := gen_pow_inj' (by omega) (by omega) he; omega,
        fun j _ h2 => hsteps j h2⟩
  · exact sw0
  · exact sw1
  · exact sw2
  · refine ⟨t, by simp [cctNames]; omega, gen_pow_eq_ofK t, ?_⟩
    rw [← List.getD_eq_getElem _ "" (by simp [cctNames]; omega)]
    refine cct_rel_low hl t ht32 hL16 rfl (by rw [pow32_eq]; exact childReads_slice hR (32 * w) t (by omega)) ?_
    refine (chainCells_prefix (blocksOf_sliceOf cs (32 * w) t)
      (fun j hj => baseMd_eq w j (by omega))).mpr ⟨fun j hj r => hb _ (by omega) r, ?_⟩
    rw [show 32 * w + t = n - 1 by omega]
  · exact limit_mul_inv (hoff _ (by omega))
  · rw [hinv]; exact hmark
  · exact (scaled_log_6_iff hT _ _).mpr ⟨_, rfl, n, hn, rfl, rfl⟩
  all_goals try (rw [pow4_eq _ (off (n - 1)) rfl])
  · exact (cellsAt_four.mp hcl).1
  · exact (cellsAt_four.mp hcl).2.1
  · exact (cellsAt_four.mp hcl).2.2.1
  · exact (cellsAt_four.mp hcl).2.2.2
  · rw [hlast, hmd]
    exact (final_iff hlen (by omega) (hb (n - 1) (by omega))).mpr hd

/-! ## The path of `child_claim_list_digest` -/

def ccldZ : List Stmt := match ccldBody with | _ :: _ :: .ite _ z _ :: _ => z | _ => []
def ccldE : List Stmt := match ccldBody with | _ :: _ :: .ite _ _ e :: _ => e | _ => []
def ccldPre : List Stmt := ccldE.take 41
def ccldPost : List Stmt := ccldE.drop 42

theorem ccldBody_split : ccldBody = [.atom (.const (.n 7) (word 1 0 0)), .atom (.add (.n 8) (.n 5) (.n 7)),
    .ite (.n 8) ccldZ (ccldPre ++ .dispatch (.n 19) cctNames [.n 56, .n 57, .n 58, .n 0, .n 1, .n 55, .n 3, .n 4]
      [.n 59, .n 60] :: ccldPost), .atom (.copy (.n 82) (.n 16)), .atom (.copy (.n 83) (.n 17)),
    .ret [.n 82, .n 83]] := rfl

theorem ccldZ_straight : ccldZ.all Main.Stmt.straight = true := by decide +kernel
theorem ccldPre_straight : ccldPre.all Main.Stmt.straight = true := by decide +kernel
theorem ccldPost_straight : ccldPost.all Main.Stmt.straight = true := by decide +kernel

def ccldHead : List Ev := [.atom (.const (.n 7) (word 1 0 0)), .atom (.add (.n 8) (.n 5) (.n 7)), .inK (.n 8)]
def ccldTail : List Ev := [.atom (.copy (.n 82) (.n 16)), .atom (.copy (.n 83) (.n 17))]

theorem walk_ccld_zero (σ : Val) (h8 : σ (.n 8) = 0) :
    walk σ ccldBody = .ret (ccldHead ++ ccldZ.flatMap (Main.slEvs σ) ++ ccldTail) [.n 82, .n 83] := by
  rw [ccldBody_split]
  simp only [walk, walk1, h8, ↓reduceIte, walk_straight_fall σ ccldZ ccldZ_straight, Out.seq, Out.pre]
  simp [ccldHead, ccldTail]

/-- The path of a non-empty child list, its tail `cctNames[t]!`. -/
noncomputable def ccldEs (σ : Val) (t : ℕ) : List Ev :=
  ccldHead ++ (ccldPre.flatMap (Main.slEvs σ) ++
    .call cctNames[t]! [.n 56, .n 57, .n 58, .n 0, .n 1, .n 55, .n 3, .n 4] [.n 59, .n 60] ::
      ccldPost.flatMap (Main.slEvs σ)) ++ ccldTail

theorem walk_ccld_pos (σ : Val) (h8 : σ (.n 8) ≠ 0) {t : ℕ} (ht : t < 32) (h19 : σ (.n 19) = ofK (gpow t)) :
    walk σ ccldBody = .ret (ccldEs σ t) [.n 82, .n 83] := by
  rw [ccldBody_split, ccldEs]
  simp only [walk, walk1, h8, ↓reduceIte, walk_dispatch_fall σ ccldPre ccldPost ccldPre_straight ccldPost_straight
    (.n 19) cctNames _ _ (i := t) (by simp [cctNames]; omega) (by simp [cctNames]) h19, Out.seq, Out.pre]
  simp [ccldHead, ccldTail]

theorem ccld_zero_events (σ : Val) :
    allocDsts (ccldHead ++ ccldZ.flatMap (Main.slEvs σ) ++ ccldTail) = [] ∧
    allocs σ (ccldHead ++ ccldZ.flatMap (Main.slEvs σ) ++ ccldTail) = [] ∧
    addrs (ccldHead ++ ccldZ.flatMap (Main.slEvs σ) ++ ccldTail) = [] ∧
    calls (ccldHead ++ ccldZ.flatMap (Main.slEvs σ) ++ ccldTail) = [] ∧
    loadAddrs σ (ccldHead ++ ccldZ.flatMap (Main.slEvs σ) ++ ccldTail) = [] := by
  obtain ⟨h1, h2, h3, h4⟩ := Main.straight_parts σ _ ccldZ_straight
  have h5 := loadAddrs_straight σ _ ccldZ_straight
  simp only [allocDsts_append, allocs_append, addrs_append, calls_append, loadAddrs_append, h1, h2, h3, h4, h5,
    show ccldZ.filterMap Main.Stmt.allocSz = [] by decide +kernel,
    show ccldZ.filterMap Main.Stmt.addrS = [] by decide +kernel,
    show ccldZ.filterMap Main.Stmt.callS = [] by decide +kernel,
    show ccldZ.filterMap stmtLoad? = [] by decide +kernel]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ccld_pos_events (σ : Val) (t : ℕ) :
    allocDsts (ccldEs σ t) = [.n 40] ∧ allocs σ (ccldEs σ t) = [logG (σ (.n 39))] ∧ addrs (ccldEs σ t) = [] ∧
    calls (ccldEs σ t) = [⟨"__loop87", [.n 46, .n 18, .n 40, .n 2, .n 0, .n 1, .n 3, .n 4, .n 6], [],
        decide (σ (.n 45) ≠ 0)⟩,
      ⟨cctNames[t]!, [.n 56, .n 57, .n 58, .n 0, .n 1, .n 55, .n 3, .n 4], [.n 59, .n 60], true⟩,
      ⟨"scaled_log__L6", [.n 5, .n 6], [.n 75], true⟩] ∧
    loadAddrs σ (ccldEs σ t) = ([(.n 40, 0), (.n 40, 1), (.n 40, 2), (.n 49, 0), (.n 49, 1), (.n 49, 2),
      (.n 71, 0), (.n 74, 0), (.n 74, 1), (.n 74, 2), (.n 74, 3)] : List (V × ℕ)).map
        fun q => (σ q.1).limb 0 * gpow q.2 := by
  obtain ⟨h1, h2, h3, h4⟩ := Main.straight_parts σ _ ccldPre_straight
  obtain ⟨g1, g2, g3, g4⟩ := Main.straight_parts σ _ ccldPost_straight
  have h5 := loadAddrs_straight σ _ ccldPre_straight
  have g5 := loadAddrs_straight σ _ ccldPost_straight
  unfold ccldEs
  simp only [allocDsts_append, allocs_append, addrs_append, calls_append, loadAddrs_append]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [show allocDsts (Ev.call cctNames[t]! [.n 56, .n 57, .n 58, .n 0, .n 1, .n 55, .n 3, .n 4] [.n 59, .n 60] ::
      ccldPost.flatMap (Main.slEvs σ)) = allocDsts (ccldPost.flatMap (Main.slEvs σ)) from rfl, h1, g1,
      show ccldPre.filterMap Main.Stmt.allocSz = [(.n 40, .inr (.n 39))] by decide +kernel,
      show ccldPost.filterMap Main.Stmt.allocSz = [] by decide +kernel]
    rfl
  · rw [show allocs σ (Ev.call cctNames[t]! [.n 56, .n 57, .n 58, .n 0, .n 1, .n 55, .n 3, .n 4] [.n 59, .n 60] ::
      ccldPost.flatMap (Main.slEvs σ)) = allocs σ (ccldPost.flatMap (Main.slEvs σ)) from rfl, h2, g2,
      show ccldPre.filterMap Main.Stmt.allocSz = [(.n 40, .inr (.n 39))] by decide +kernel,
      show ccldPost.filterMap Main.Stmt.allocSz = [] by decide +kernel]
    rfl
  · rw [show addrs (Ev.call cctNames[t]! [.n 56, .n 57, .n 58, .n 0, .n 1, .n 55, .n 3, .n 4] [.n 59, .n 60] ::
      ccldPost.flatMap (Main.slEvs σ)) = addrs (ccldPost.flatMap (Main.slEvs σ)) from rfl, h3, g3,
      show ccldPre.filterMap Main.Stmt.addrS = [] by decide +kernel,
      show ccldPost.filterMap Main.Stmt.addrS = [] by decide +kernel]
    rfl
  · rw [show calls (Ev.call cctNames[t]! [.n 56, .n 57, .n 58, .n 0, .n 1, .n 55, .n 3, .n 4] [.n 59, .n 60] ::
      ccldPost.flatMap (Main.slEvs σ)) = ⟨cctNames[t]!, [.n 56, .n 57, .n 58, .n 0, .n 1, .n 55, .n 3, .n 4],
        [.n 59, .n 60], true⟩ :: calls (ccldPost.flatMap (Main.slEvs σ)) from rfl, h4, g4,
      show ccldPre.filterMap Main.Stmt.callS = [(some (.n 45), "__loop87",
        [.n 46, .n 18, .n 40, .n 2, .n 0, .n 1, .n 3, .n 4, .n 6], [])] by decide +kernel,
      show ccldPost.filterMap Main.Stmt.callS = [(none, "scaled_log__L6", [.n 5, .n 6], [.n 75])] by decide +kernel]
    rfl
  · rw [show loadAddrs σ (Ev.call cctNames[t]! [.n 56, .n 57, .n 58, .n 0, .n 1, .n 55, .n 3, .n 4] [.n 59, .n 60] ::
      ccldPost.flatMap (Main.slEvs σ)) = loadAddrs σ (ccldPost.flatMap (Main.slEvs σ)) from rfl, h5, g5,
      show ccldPre.filterMap stmtLoad? = [(.n 40, 0), (.n 40, 1), (.n 40, 2), (.n 49, 0), (.n 49, 1),
        (.n 49, 2)] by decide +kernel,
      show ccldPost.filterMap stmtLoad? = [(.n 71, 0), (.n 74, 0), (.n 74, 1), (.n 74, 2), (.n 74, 3)] by
        decide +kernel]
    rfl

def ccldZeroList (entries cover base origin limit gsq d0 d1 : E) : List E :=
  [entries, cover, base, origin, limit, 1, gsq, word 1 0 0, 1 + word 1 0 0,
    word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0, word 13503953895743350343 11912009169889063794 0,
    word 11170449402626986623 6620516960021240235 0, word 0 4294967295 0, d0, d1] ++
    List.replicate 64 0 ++ [d0, d1]

theorem ccld_holds_zero (rd : Reader) (entries cover base origin limit gsq : E) {d0 d1 : E}
    (hd : (d0, d1) = digestScalars (blake2sBytes (([] : List E).flatMap cellBytes))) :
    Stmt.HoldsList (coreProgram.Rel rd) rd (listVal (ccldZeroList entries cover base origin limit gsq d0 d1))
      ccldBody False (fun rs => rs = [d0, d1]) := by
  simp only [ccldBody, List.cons_append, List.nil_append, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, true_and, List.map_cons, List.map_nil]
  have h11 : (1 : E) + word 1 0 0 = 0 := by rw [word_one, e_add_self]
  refine ⟨rfl, rfl, ?_, fun _ => ?_, fun h => ?_⟩
  · show IsInK ((1 : E) + word 1 0 0)
    rw [h11, ← ofK_zero]; exact ofK_isInK _
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
    show CompressCells ![word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0]
      (word 13503953895743350343 11912009169889063794 0)
      (word 11170449402626986623 6620516960021240235 0) d0 d1 (word 0 4294967295 0)
    rw [word_zero, iv0_word, iv1_word, md_final_word]
    exact compressCells_empty_iff.mpr hd
  · exfalso; apply h; show (1 : E) + word 1 0 0 = 0; exact h11

theorem cctNames_getElem! {t : ℕ} (ht : t < 32) : cctNames[t]! = cctNames.getD t "" := by
  interval_cases t <;> rfl

/-- `child_claim_list_digest`'s precondition at the indices `off` and the claims `cs`. -/
def CclPreAt (off : ℕ → ℕ) (cs : List E) (rd : Reader) : List E → List E → Prop
  | [entries, cover, base, origin, limit, ng, gsq], [d0, d1] => SquaresAt rd gsq ∧
      (∃ L ≤ 2 ^ 16, limit = gen ^ L) ∧ ∃ n < 2 ^ 16, ng = gen ^ n ∧ cs.length = 4 * n ∧
        ChildReads rd entries cover base origin limit off cs n ∧ (∀ c ∈ cs, IsCanonical128 c) ∧
          (d0, d1) = digestScalars (blake2sBytes (cs.flatMap cellBytes))
  | _, _ => False

theorem cclPreAt_shape {off : ℕ → ℕ} {cs : List E} {rd : Reader} {args rets : List E} (h : CclPreAt off cs rd args rets) :
    ∃ entries cover base origin limit ng gsq d0 d1, args = [entries, cover, base, origin, limit, ng, gsq] ∧
      rets = [d0, d1] := by
  unfold CclPreAt at h
  split at h
  · exact ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩
  · exact h.elim

/-- The child's reads pinned at their words of the caller's layout. -/
def ccldPins (cs : List E) (base : E) (n : ℕ) (cidx : ℕ → ℕ → ℕ) (midx : ℕ → ℕ) : Layout :=
  (List.range n).flatMap (fun j => (List.range 4).map fun r => (cidx j r, [cs.getD (4 * j + r) 0])) ++
    (List.range n).map fun j => (midx j, [base * gen ^ j])

theorem getElem_four (cs : List E) (j : ℕ) : ∀ (r : ℕ) (h : r < 4),
    ([cs.getD (4 * j) 0, cs.getD (4 * j + 1) 0, cs.getD (4 * j + 2) 0, cs.getD (4 * j + 3) 0] : List E)[r]'
      (by simpa using h) = cs.getD (4 * j + r) 0
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | _ + 4, h => absurd h (by omega)

/-- The windows' scratch table of a child's list at `b`. -/
def cclScratchL (cs : List E) (b w : ℕ) : Layout := (List.range (w + 1)).map fun q => (b + 4 * q, cclSlot cs q)

theorem cclScratchL_disj {cs : List E} {b w : ℕ} : DisjL (cclScratchL cs b w) := by
  unfold DisjL cclScratchL
  rw [List.pairwise_map]
  exact (List.pairwise_lt_range (n := w + 1)).imp fun {a c} h => Or.inl (by simp only [cclSlot]; simp; omega)

theorem cclScratch_slot {cs : List E} {b w q r : ℕ} (hq : q ≤ w) (hr : r < 3) :
    RegionL (cclScratchL cs b w) (b + 4 * q + r) :=
  ⟨(b + 4 * q, cclSlot cs q), List.mem_map.mpr ⟨q, List.mem_range.mpr (by omega), rfl⟩, by omega,
    by simp only [cclSlot, List.length_cons, List.length_nil]; omega⟩

theorem cclScratch_region {cs : List E} {b w i : ℕ} (h : RegionL (cclScratchL cs b w) i) :
    b ≤ i ∧ i < b + 4 * (w + 1) := by
  obtain ⟨q, hq, h1, h2⟩ := h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
  have := List.mem_range.mp hj
  simp only [cclSlot, List.length_cons, List.length_nil] at h1 h2
  omega

theorem cclScratch_of_memL {rd : Reader} {L : Layout} (h : MemL rd L) {cs : List E} {b w : ℕ}
    (hs : ∀ q ∈ cclScratchL cs b w, q ∈ L) : ChildScratch rd (gen ^ b) cs w := fun q hq => by
  rw [← pow_add]
  exact cells_of_memL h (hs _ (List.mem_map.mpr ⟨q, List.mem_range.mpr (by omega), rfl⟩))

/-- The bound of `child_claim_list_digest` on `n` claims: its frame, the scratch table, the window
loop, the tail and the scaled log. -/
def ccldBound (fs : String → ℕ) (Kc Bsl6 n : ℕ) : ℕ :=
  fs "child_claim_list_digest" + 4 * ((n - 1) / 32 + 1) +
    (l87Bound fs Kc ((n - 1) / 32) 0 + fs (cctNames.getD ((n - 1) % 32) "") + Bsl6)

theorem cct_ne : ∀ t < 32, cctNames[t]! ≠ "__loop87" ∧ cctNames[t]! ≠ "scaled_log__L6" := by decide

/-- **`child_claim_list_digest` is complete, uniformly placed**, at the indices `off` and the claims
`cs`, on a memory defined below `2^κ`, `κ ≥ 16`. -/
theorem ccld_completeRelAt (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ)
    (off : ℕ → ℕ) (cs : List E) : CompleteRel fs cert κ "child_claim_list_digest" (CclPreAt off cs) := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨entries, cover, base, origin, limit, ng, gsq, d0, d1, rfl, rfl⟩ := cclPreAt_shape (hpre rd1 hl1 hL1)
  obtain ⟨hT1, ⟨L, hL16, rfl⟩, n, hn, rfl, hlen, hR1, hcan, hd⟩ := hpre rd1 hl1 hL1
  have hpre' : ∀ rd, LowDef κ rd → MemL rd Lin →
      SquaresAt rd gsq ∧ ChildReads rd entries cover base origin (gen ^ L) off cs n := by
    intro rd hl hL
    obtain ⟨hT, -, n', hn', hng', -, hR', -, -⟩ := hpre rd hl hL
    obtain rfl : n = n' := gen_pow_inj' (by omega) (by omega) hng'
    exact ⟨hT, hR'⟩
  have hFc : ∀ j r, ∃ i, j < n → r < 4 →
      (entries * gen ^ (4 * off j)).limb 0 * gpow r = gpow i ∧ RegionL Lin i := by
    intro j r
    by_cases h : j < n ∧ r < 4
    · obtain ⟨hj, hr⟩ := h
      have hall : ∀ rd, LowDef κ rd → MemL rd Lin →
          LoadHolds rd (entries * gen ^ (4 * off j)) r (cs.getD (4 * j + r) 0) := by
        intro rd hl hL
        have hc4 := ((hpre' rd hl hL).2 j hj).2.2
        exact match r, hr with
          | 0, _ => by simpa using hc4 0 (by simp)
          | 1, _ => by simpa using hc4 1 (by simp)
          | 2, _ => by simpa using hc4 2 (by simp)
          | 3, _ => by simpa using hc4 3 (by simp)
          | _ + 4, hr => absurd hr (by omega)
      obtain ⟨i, hi⟩ := forced_load hall hl1 hL1
      exact ⟨i, fun _ _ => hi⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose cidx hcidx using hFc
  have hFm : ∀ j, ∃ i, j < n → (cover * (origin * gen ^ off j)).limb 0 * gpow 0 = gpow i ∧ RegionL Lin i := by
    intro j
    by_cases h : j < n
    · obtain ⟨i, hi⟩ := forced_load (fun rd hl hL => ((hpre' rd hl hL).2 j h).2.1) hl1 hL1
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h1 => absurd h1 h⟩
  choose midx hmidx using hFm
  have hSq : ∀ j, ∃ i, j < 16 → gsq.limb 0 * gpow j = gpow i ∧ RegionL Lin i := by
    intro j
    by_cases hj : j < 16
    · obtain ⟨i, hi⟩ := forced_load (fun rd hl hL => (hpre' rd hl hL).1 j hj) hl1 hL1
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose sidx hsidx using hSq
  have hgK : IsInK gsq := (hT1 0 (by norm_num)).1
  have hlow : ∀ rd, LowDef κ rd → Low16 rd := fun rd hl i hi =>
    hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ))
  set PL : Layout := ccldPins cs base n cidx midx ++ pinL (fun j => gen ^ 2 ^ j) sidx 16 with hPL
  -- the pins read back as the reads and the squares table
  have hPLr : ∀ rd', MemL rd' PL → SquaresAt rd' gsq ∧ ChildReads rd' entries cover base origin (gen ^ L) off cs n := by
    intro rd' h
    refine ⟨fun j hj => pin_loads h hgK (fun j hj => (hsidx j hj).1) (fun q hq => List.mem_append_right _ hq) j hj,
      fun j hj => ⟨(hR1 j hj).1, load_of_pin h (hR1 j hj).2.1.1 (hmidx j hj).1
        (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))),
        fun r hr => ?_⟩⟩
    have hr4 : r < 4 := by simpa using hr
    have := load_of_pin h ((hR1 j hj).2.2 0 (by simp)).1 (hcidx j r hj hr4).1 (v := cs.getD (4 * j + r) 0)
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj,
        List.mem_map.mpr ⟨r, List.mem_range.mpr hr4, rfl⟩⟩)))
    have key : ([cs.getD (4 * j) 0, cs.getD (4 * j + 1) 0, cs.getD (4 * j + 2) 0, cs.getD (4 * j + 3) 0] :
        List E)[r]'hr = cs.getD (4 * j + r) 0 := getElem_four cs j r hr4
    rw [key]; exact this
  have hPLm : ∀ rd, MemL rd Lin → MemL rd PL := by
    intro rd hL q hq k hk
    have e : ∀ {i : ℕ} {v : E}, RegionL Lin i → rd1 (gpow i) = some v → q = (i, [v]) →
        LoadHolds rd (ofK (gpow q.1)) k (q.2[k]'hk) := fun {i v} hR hv hqe => by
      subst hqe
      simp only [List.length_cons, List.length_nil] at hk
      obtain rfl : k = 0 := by omega
      refine ⟨ofK_isInK _, ?_⟩
      rw [Main.addr_ofK, Nat.add_zero, Main.memL_agree hL hL1 _ hR, hv]
      rfl
    rw [hPL, List.mem_append, ccldPins, List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · obtain ⟨j, hj, hq⟩ := List.mem_flatMap.mp hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      have hj := List.mem_range.mp hj
      have hr := List.mem_range.mp hr
      refine e (hcidx j r hj hr).2 ?_ rfl
      have := ((hR1 j hj).2.2 r (by simp; omega)).2
      rw [(hcidx j r hj hr).1] at this
      rw [this]
      exact match r, hr with
        | 0, _ => by simp
        | 1, _ => by simp
        | 2, _ => by simp
        | 3, _ => by simp
        | _ + 4, hr => absurd hr (by omega)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      have hj := List.mem_range.mp hj
      refine e (hmidx j hj).2 ?_ rfl
      have := (hR1 j hj).2.1.2
      rwa [(hmidx j hj).1] at this
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      have hj := List.mem_range.mp hj
      refine e (hsidx j hj).2 ?_ rfl
      have := (hT1 j hj).2
      rwa [(hsidx j hj).1] at this
  have hPLR : ∀ i, RegionL PL i → RegionL Lin i := by
    intro i ⟨q, hq, h1, h2⟩
    rw [hPL, List.mem_append, ccldPins, List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · obtain ⟨j, hj, hq⟩ := List.mem_flatMap.mp hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      simp only [List.length_cons, List.length_nil] at h1 h2
      rw [show i = cidx j r by omega]
      exact (hcidx j r (List.mem_range.mp hj) (List.mem_range.mp hr)).2
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      simp only [List.length_cons, List.length_nil] at h1 h2
      rw [show i = midx j by omega]
      exact (hmidx j (List.mem_range.mp hj)).2
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      simp only [List.length_cons, List.length_nil] at h1 h2
      rw [show i = sidx j by omega]
      exact (hsidx j (List.mem_range.mp hj)).2
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · obtain rfl : cs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    refine ⟨fs "child_claim_list_digest", [], [d0, d1], [], ⟨rfl, rfl⟩, by simp [Within], fun rd hl hL => ?_⟩
    have h8 : listVal (ccldZeroList entries cover base origin (gen ^ L) gsq d0 d1) (.n 8) = 0 := by
      show (1 : E) + word 1 0 0 = 0; rw [word_one, e_add_self]
    have hw := walk_ccld_zero _ h8
    have hev := holds_of_holdsList find_child_claim_list_digest
      (ccld_holds_zero rd entries cover base origin (gen ^ L) gsq hd) hw
    obtain ⟨e1, e2, e3, e4, e5⟩ := ccld_zero_events (listVal (ccldZeroList entries cover base origin (gen ^ L) gsq d0 d1))
    have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (rd := rd) coreProgram_wf
      (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (fp := fp) (N := 0)
      find_child_claim_list_digest (Or.inl (by decide +kernel)) rfl hw rfl hev (by rw [e1, e2]; rfl) (by rw [e3]; simp)
      (by rw [e4]; exact ⟨rfl, fun _ h => h⟩) (by rw [e5]; simp) (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
    rwa [e2, List.sum_nil, Nat.add_zero, Nat.add_zero] at h
  obtain ⟨w, hw⟩ : ∃ w, w = (n - 1) / 32 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = (n - 1) % 32 := ⟨_, rfl⟩
  have ht32 : t < 32 := by omega
  have hwt : n = 32 * w + t + 1 := by omega
  have hb := blocks_canonical hlen hcan
  let KL : ℕ → Layout := fun fp => cclScratchL cs (fp + fs "child_claim_list_digest") w ++ PL
  have hKL : ∀ fp rd', MemL rd' (KL fp) → SquaresAt rd' gsq ∧
      ChildReads rd' entries cover base origin (gen ^ L) off cs n ∧ ChildScratch rd' (gen ^ (fp + fs "child_claim_list_digest")) cs w :=
    fun fp rd' h => ⟨(hPLr rd' (Main.memL_append.mp h).2).1, (hPLr rd' (Main.memL_append.mp h).2).2,
      cclScratch_of_memL h fun q hq => List.mem_append_left _ hq⟩
  have hKLreg : ∀ fp i, RegionL (KL fp) i → RegionL (cclScratchL cs (fp + fs "child_claim_list_digest") w) i ∨ RegionL Lin i := by
    intro fp i ⟨q, hq, h1, h2⟩
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inl ⟨q, hq, h1, h2⟩
    · exact Or.inr (hPLR i ⟨q, hq, h1, h2⟩)
  have hregKL : ∀ fp A, ChildLoad entries cover origin off n A → ∃ i, A = gpow i ∧ RegionL (KL fp) i := by
    intro fp A hA
    rcases hA with ⟨j, hj, rfl⟩ | ⟨j, hj, r, hr, rfl⟩
    · refine ⟨midx j, (hmidx j hj).1, ⟨(midx j, [base * gen ^ j]), ?_, le_refl _, by simp⟩⟩
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
    · refine ⟨cidx j r, (hcidx j r hj hr).1, ⟨(cidx j r, [cs.getD (4 * j + r) 0]), ?_, le_refl _, by simp⟩⟩
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩⟩)))
  have hch : ChainCells ((digestScalars (prefixDigest cs (32 * w))).1, (digestScalars (prefixDigest cs (32 * w))).2)
      (blocksOf (sliceOf cs (32 * w) t)) (baseMd (eOfNat (2 ^ 11 * w))) t
      ((digestScalars (prefixDigest cs (n - 1))).1, (digestScalars (prefixDigest cs (n - 1))).2) := by
    refine (chainCells_prefix (blocksOf_sliceOf cs (32 * w) t)
      (fun j hj => baseMd_eq w j (by omega))).mpr ⟨fun j hj r => hb _ (by omega) r, ?_⟩
    rw [show 32 * w + t = n - 1 by omega]
  refine completeAt_node find_child_claim_list_digest (by
      rw [Program.loop_of_find? find_child_claim_list_digest]; decide +kernel) κ Lin _ _ [4 * (w + 1)]
    (fun fp => cclScratchL cs (fp + fs "child_claim_list_digest") w)
    (fun fp i hi => ⟨(4 * (w + 1), fp + fs "child_claim_list_digest"), List.mem_singleton_self _, (cclScratch_region hi).1,
      (cclScratch_region hi).2⟩)
    (fun fp q hq => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      have := List.mem_range.mp hj
      simp only [cclSlot, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
      omega)
    (fun fp => [⟨"__loop87", decide (word 1 0 0 + gen ^ w ≠ 0),
        [gen ^ 0, gen ^ w, gen ^ (fp + fs "child_claim_list_digest"), base, entries, cover, origin, gen ^ L, gsq], KL fp, []⟩,
      ⟨cctNames[t]!, true, cclSlot cs w ++ [entries, cover, base * pow32 (gen ^ w), origin, gen ^ L], KL fp,
        [(digestScalars (prefixDigest cs (n - 1))).1, (digestScalars (prefixDigest cs (n - 1))).2]⟩,
      ⟨"scaled_log__L6", true, [gen ^ n, gsq], KL fp, [eOfNat (2 ^ 6 * n)]⟩]) ?_ ?_ ?_ fp
  · intro fp k hk htk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · have hw0 : 0 < w := by
        rcases Nat.eq_zero_or_pos w with h0 | h0
        · simp [h0, word_one, e_add_self] at htk
        · exact h0
      exact l87_completeAt fs cert hκ (KL fp) hL16 hn (by omega) hlen hcan (fun rd _ h => (hKL fp rd h).2.1)
        (fun rd h => (hKL fp rd h).1) (fun rd h => (hKL fp rd h).2.2) (hregKL fp)
        (fun q hq r hr => by
          obtain ⟨e, he, h1, h2⟩ := cclScratch_slot (cs := cs) (b := fp + fs "child_claim_list_digest") (w := w) hq hr
          exact ⟨e, List.mem_append_left _ he, h1, h2⟩) 0 hw0
    · show CompleteAt fs cert κ cctNames[t]! _ _ _
      rw [cctNames_getElem! ht32]
      exact cct_completeAt fs cert hκ t ht32 (KL fp) hL16 rfl (off := fun k => off (32 * w + k))
        (cs := sliceOf cs (32 * w) t)
        (fun rd _ h => by rw [pow32_eq]; exact childReads_slice (hKL fp rd h).2.1 (32 * w) t (by omega))
        (fun A hA => hregKL fp A (childLoad_shift (by omega) hA)) hch
    · exact LeanVM.Guest.B1.completeAt_of_rel_pure cldKid_pure (by simp [cldKidSet])
        (fun rd h => (scaled_log_6_iff (hKL fp rd h).1 _ _).mpr ⟨_, rfl, n, hn, rfl, rfl⟩) κ
  · intro fp k hk _ i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> exact hKLreg fp i hi
  · intro fp' rd hl hLb hLin
    have hPL := hPLm rd hLin
    refine ⟨fun k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact Main.memL_append.mpr ⟨hLb, hPL⟩, ?_⟩
    obtain ⟨hT, hR⟩ := hpre' rd hl hLin
    have hscr : ChildScratch rd (gen ^ (fp' + fs "child_claim_list_digest")) cs ((n - 1) / 32) := by
      rw [← hw]; exact cclScratch_of_memL hLb fun q hq => hq
    obtain ⟨t1, t2, t3, t4, t5, t6, hh⟩ := ccld_holds_pos (hlow rd hl) hT hL16 hn hn1 hlen hR hcan hscr hd
    rw [← hw, ← ht] at hh
    set σ := listVal (cclList entries cover base origin (gen ^ L) gsq (gen ^ (fp' + fs "child_claim_list_digest"))
      d0 d1 cs (off (n - 1)) L n w t t1 t2 t3 t4 t5 t6) with hσ
    have h8 : σ (.n 8) ≠ 0 := fun h' => by
      have h'' : gen ^ n + word 1 0 0 = 0 := h'
      rw [word_one] at h''
      have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h'')
      omega
    have hw' := walk_ccld_pos σ h8 ht32 (gen_pow_eq_ofK t)
    have hev := holds_of_holdsList find_child_claim_list_digest hh hw'
    obtain ⟨e1, e2, e3, e4, e5⟩ := ccld_pos_events σ t
    have h39 : logG (σ (.n 39)) = 4 * (w + 1) := by
      rw [show σ (.n 39) = gen ^ (4 * (w + 1)) by
        show gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0) * (gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0)) = _
        rw [word_gen]; ring]
      exact logG_gen_pow (by omega)
    refine ⟨σ, _, _, rfl, hw', rfl, hev, ?_, e3, by rw [e2, h39], ?_, fun A hA => ?_⟩
    · rw [e4]
      refine ⟨rfl, rfl, fun _ => ⟨?_, rfl⟩, rfl, rfl, fun _ => ⟨rfl, rfl⟩, rfl, rfl, fun _ => ⟨rfl, rfl⟩, trivial⟩
      show [word 1 0 0, gen ^ w, gen ^ (fp' + fs "child_claim_list_digest"), base, entries, cover, origin, gen ^ L,
        gsq] = _
      rw [word_one, pow_zero]
    · rw [e1]
      simp only [List.map_cons, List.map_nil, bases]
      rw [← gen_pow_eq_ofK]; rfl
    · rw [e5] at hA
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
      set cx := fp' + fs "child_claim_list_digest" with hcx
      have g40 : σ (.n 40) = gen ^ cx := rfl
      have g49 : σ (.n 49) = gen ^ (cx + 4 * w) := by
        show gen ^ cx * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) = _
        ring
      have g71 : σ (.n 71) = cover * (origin * gen ^ off (n - 1)) := rfl
      have g74 : σ (.n 74) = entries * gen ^ (4 * off (n - 1)) := by
        show entries * (gen ^ off (n - 1) * gen ^ off (n - 1) * (gen ^ off (n - 1) * gen ^ off (n - 1))) = _
        rw [pow4_eq _ _ rfl]
      have sl : ∀ q r, q ≤ w → r < 3 → RegionL (cclScratchL cs cx w) (cx + 4 * q + r) :=
        fun q r hq hr => cclScratch_slot hq hr
      rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨cx + 4 * 0 + 0, by rw [g40, limb0_gen_pow, gpow_add'], Or.inl (sl 0 0 (by omega) (by omega))⟩
      · exact ⟨cx + 4 * 0 + 1, by rw [g40, limb0_gen_pow, gpow_add'], Or.inl (sl 0 1 (by omega) (by omega))⟩
      · exact ⟨cx + 4 * 0 + 2, by rw [g40, limb0_gen_pow, gpow_add'], Or.inl (sl 0 2 (by omega) (by omega))⟩
      · exact ⟨cx + 4 * w + 0, by rw [g49, limb0_gen_pow, gpow_add'], Or.inl (sl w 0 le_rfl (by omega))⟩
      · exact ⟨cx + 4 * w + 1, by rw [g49, limb0_gen_pow, gpow_add'], Or.inl (sl w 1 le_rfl (by omega))⟩
      · exact ⟨cx + 4 * w + 2, by rw [g49, limb0_gen_pow, gpow_add'], Or.inl (sl w 2 le_rfl (by omega))⟩
      · exact ⟨_, by rw [g71]; exact (hmidx (n - 1) (by omega)).1, Or.inr (hmidx (n - 1) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 0 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 0 (by omega) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 1 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 1 (by omega) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 2 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 2 (by omega) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 3 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 3 (by omega) (by omega)).2⟩

/-- **`child_claim_list_digest` is complete, uniformly placed**, at the indices `off` and the claims
`cs`, on a memory defined below `2^κ`, `κ ≥ 16`. -/
theorem ccld_completeRelAtD (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ)
    (off : ℕ → ℕ) (cs : List E) : CompleteRelD fs cert κ "child_claim_list_digest" (CclPreAt off cs) := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨entries, cover, base, origin, limit, ng, gsq, d0, d1, rfl, rfl⟩ := cclPreAt_shape (hpre rd1 hl1 hL1)
  obtain ⟨hT1, ⟨L, hL16, rfl⟩, n, hn, rfl, hlen, hR1, hcan, hd⟩ := hpre rd1 hl1 hL1
  have hpre' : ∀ rd, LowDef κ rd → MemL rd Lin →
      SquaresAt rd gsq ∧ ChildReads rd entries cover base origin (gen ^ L) off cs n := by
    intro rd hl hL
    obtain ⟨hT, -, n', hn', hng', -, hR', -, -⟩ := hpre rd hl hL
    obtain rfl : n = n' := gen_pow_inj' (by omega) (by omega) hng'
    exact ⟨hT, hR'⟩
  have hFc : ∀ j r, ∃ i, j < n → r < 4 →
      (entries * gen ^ (4 * off j)).limb 0 * gpow r = gpow i ∧ RegionL Lin i := by
    intro j r
    by_cases h : j < n ∧ r < 4
    · obtain ⟨hj, hr⟩ := h
      have hall : ∀ rd, LowDef κ rd → MemL rd Lin →
          LoadHolds rd (entries * gen ^ (4 * off j)) r (cs.getD (4 * j + r) 0) := by
        intro rd hl hL
        have hc4 := ((hpre' rd hl hL).2 j hj).2.2
        exact match r, hr with
          | 0, _ => by simpa using hc4 0 (by simp)
          | 1, _ => by simpa using hc4 1 (by simp)
          | 2, _ => by simpa using hc4 2 (by simp)
          | 3, _ => by simpa using hc4 3 (by simp)
          | _ + 4, hr => absurd hr (by omega)
      obtain ⟨i, hi⟩ := forced_load hall hl1 hL1
      exact ⟨i, fun _ _ => hi⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose cidx hcidx using hFc
  have hFm : ∀ j, ∃ i, j < n → (cover * (origin * gen ^ off j)).limb 0 * gpow 0 = gpow i ∧ RegionL Lin i := by
    intro j
    by_cases h : j < n
    · obtain ⟨i, hi⟩ := forced_load (fun rd hl hL => ((hpre' rd hl hL).2 j h).2.1) hl1 hL1
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h1 => absurd h1 h⟩
  choose midx hmidx using hFm
  have hSq : ∀ j, ∃ i, j < 16 → gsq.limb 0 * gpow j = gpow i ∧ RegionL Lin i := by
    intro j
    by_cases hj : j < 16
    · obtain ⟨i, hi⟩ := forced_load (fun rd hl hL => (hpre' rd hl hL).1 j hj) hl1 hL1
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose sidx hsidx using hSq
  have hgK : IsInK gsq := (hT1 0 (by norm_num)).1
  have hlow : ∀ rd, LowDef κ rd → Low16 rd := fun rd hl i hi =>
    hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ))
  set PL : Layout := ccldPins cs base n cidx midx ++ pinL (fun j => gen ^ 2 ^ j) sidx 16 with hPL
  -- the pins read back as the reads and the squares table
  have hPLr : ∀ rd', MemL rd' PL → SquaresAt rd' gsq ∧ ChildReads rd' entries cover base origin (gen ^ L) off cs n := by
    intro rd' h
    refine ⟨fun j hj => pin_loads h hgK (fun j hj => (hsidx j hj).1) (fun q hq => List.mem_append_right _ hq) j hj,
      fun j hj => ⟨(hR1 j hj).1, load_of_pin h (hR1 j hj).2.1.1 (hmidx j hj).1
        (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))),
        fun r hr => ?_⟩⟩
    have hr4 : r < 4 := by simpa using hr
    have := load_of_pin h ((hR1 j hj).2.2 0 (by simp)).1 (hcidx j r hj hr4).1 (v := cs.getD (4 * j + r) 0)
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj,
        List.mem_map.mpr ⟨r, List.mem_range.mpr hr4, rfl⟩⟩)))
    have key : ([cs.getD (4 * j) 0, cs.getD (4 * j + 1) 0, cs.getD (4 * j + 2) 0, cs.getD (4 * j + 3) 0] :
        List E)[r]'hr = cs.getD (4 * j + r) 0 := getElem_four cs j r hr4
    rw [key]; exact this
  have hPLm : ∀ rd, MemL rd Lin → MemL rd PL := by
    intro rd hL q hq k hk
    have e : ∀ {i : ℕ} {v : E}, RegionL Lin i → rd1 (gpow i) = some v → q = (i, [v]) →
        LoadHolds rd (ofK (gpow q.1)) k (q.2[k]'hk) := fun {i v} hR hv hqe => by
      subst hqe
      simp only [List.length_cons, List.length_nil] at hk
      obtain rfl : k = 0 := by omega
      refine ⟨ofK_isInK _, ?_⟩
      rw [Main.addr_ofK, Nat.add_zero, Main.memL_agree hL hL1 _ hR, hv]
      rfl
    rw [hPL, List.mem_append, ccldPins, List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · obtain ⟨j, hj, hq⟩ := List.mem_flatMap.mp hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      have hj := List.mem_range.mp hj
      have hr := List.mem_range.mp hr
      refine e (hcidx j r hj hr).2 ?_ rfl
      have := ((hR1 j hj).2.2 r (by simp; omega)).2
      rw [(hcidx j r hj hr).1] at this
      rw [this]
      exact match r, hr with
        | 0, _ => by simp
        | 1, _ => by simp
        | 2, _ => by simp
        | 3, _ => by simp
        | _ + 4, hr => absurd hr (by omega)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      have hj := List.mem_range.mp hj
      refine e (hmidx j hj).2 ?_ rfl
      have := (hR1 j hj).2.1.2
      rwa [(hmidx j hj).1] at this
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      have hj := List.mem_range.mp hj
      refine e (hsidx j hj).2 ?_ rfl
      have := (hT1 j hj).2
      rwa [(hsidx j hj).1] at this
  have hPLR : ∀ i, RegionL PL i → RegionL Lin i := by
    intro i ⟨q, hq, h1, h2⟩
    rw [hPL, List.mem_append, ccldPins, List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · obtain ⟨j, hj, hq⟩ := List.mem_flatMap.mp hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      simp only [List.length_cons, List.length_nil] at h1 h2
      rw [show i = cidx j r by omega]
      exact (hcidx j r (List.mem_range.mp hj) (List.mem_range.mp hr)).2
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      simp only [List.length_cons, List.length_nil] at h1 h2
      rw [show i = midx j by omega]
      exact (hmidx j (List.mem_range.mp hj)).2
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      simp only [List.length_cons, List.length_nil] at h1 h2
      rw [show i = sidx j by omega]
      exact (hsidx j (List.mem_range.mp hj)).2
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · obtain rfl : cs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    refine ⟨fs "child_claim_list_digest", [], [d0, d1], [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, fun rd hl hL => ?_⟩
    have h8 : listVal (ccldZeroList entries cover base origin (gen ^ L) gsq d0 d1) (.n 8) = 0 := by
      show (1 : E) + word 1 0 0 = 0; rw [word_one, e_add_self]
    have hw := walk_ccld_zero _ h8
    have hev := holds_of_holdsList find_child_claim_list_digest
      (ccld_holds_zero rd entries cover base origin (gen ^ L) gsq hd) hw
    obtain ⟨e1, e2, e3, e4, e5⟩ := ccld_zero_events (listVal (ccldZeroList entries cover base origin (gen ^ L) gsq d0 d1))
    have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (rd := rd) coreProgram_wf
      (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (fp := fp) (N := 0)
      find_child_claim_list_digest (Or.inl (by decide +kernel)) rfl hw rfl hev (by rw [e1, e2]; rfl) (by rw [e3]; simp)
      (by rw [e4]; exact ⟨rfl, fun _ h => h⟩) (by rw [e5]; simp) (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
    rwa [e2, List.sum_nil, Nat.add_zero, Nat.add_zero] at h
  obtain ⟨w, hw⟩ : ∃ w, w = (n - 1) / 32 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = (n - 1) % 32 := ⟨_, rfl⟩
  have ht32 : t < 32 := by omega
  have hwt : n = 32 * w + t + 1 := by omega
  have hb := blocks_canonical hlen hcan
  let KL : ℕ → Layout := fun fp => cclScratchL cs (fp + fs "child_claim_list_digest") w ++ PL
  have hKL : ∀ fp rd', MemL rd' (KL fp) → SquaresAt rd' gsq ∧
      ChildReads rd' entries cover base origin (gen ^ L) off cs n ∧ ChildScratch rd' (gen ^ (fp + fs "child_claim_list_digest")) cs w :=
    fun fp rd' h => ⟨(hPLr rd' (Main.memL_append.mp h).2).1, (hPLr rd' (Main.memL_append.mp h).2).2,
      cclScratch_of_memL h fun q hq => List.mem_append_left _ hq⟩
  have hKLreg : ∀ fp i, RegionL (KL fp) i → RegionL (cclScratchL cs (fp + fs "child_claim_list_digest") w) i ∨ RegionL Lin i := by
    intro fp i ⟨q, hq, h1, h2⟩
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inl ⟨q, hq, h1, h2⟩
    · exact Or.inr (hPLR i ⟨q, hq, h1, h2⟩)
  have hregKL : ∀ fp A, ChildLoad entries cover origin off n A → ∃ i, A = gpow i ∧ RegionL (KL fp) i := by
    intro fp A hA
    rcases hA with ⟨j, hj, rfl⟩ | ⟨j, hj, r, hr, rfl⟩
    · refine ⟨midx j, (hmidx j hj).1, ⟨(midx j, [base * gen ^ j]), ?_, le_refl _, by simp⟩⟩
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
    · refine ⟨cidx j r, (hcidx j r hj hr).1, ⟨(cidx j r, [cs.getD (4 * j + r) 0]), ?_, le_refl _, by simp⟩⟩
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩⟩)))
  have hch : ChainCells ((digestScalars (prefixDigest cs (32 * w))).1, (digestScalars (prefixDigest cs (32 * w))).2)
      (blocksOf (sliceOf cs (32 * w) t)) (baseMd (eOfNat (2 ^ 11 * w))) t
      ((digestScalars (prefixDigest cs (n - 1))).1, (digestScalars (prefixDigest cs (n - 1))).2) := by
    refine (chainCells_prefix (blocksOf_sliceOf cs (32 * w) t)
      (fun j hj => baseMd_eq w j (by omega))).mpr ⟨fun j hj r => hb _ (by omega) r, ?_⟩
    rw [show 32 * w + t = n - 1 by omega]
  refine completeAt_nodeD find_child_claim_list_digest (by
      rw [Program.loop_of_find? find_child_claim_list_digest]; decide +kernel) κ Lin _ _ [4 * (w + 1)]
    (fun fp => cclScratchL cs (fp + fs "child_claim_list_digest") w)
    (fun fp i hi => ⟨(4 * (w + 1), fp + fs "child_claim_list_digest"), List.mem_singleton_self _, (cclScratch_region hi).1,
      (cclScratch_region hi).2⟩)
    (fun fp q hq => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      have := List.mem_range.mp hj
      simp only [cclSlot, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
      omega) (fun _ => cclScratchL_disj)
    (fun fp => [⟨"__loop87", decide (word 1 0 0 + gen ^ w ≠ 0),
        [gen ^ 0, gen ^ w, gen ^ (fp + fs "child_claim_list_digest"), base, entries, cover, origin, gen ^ L, gsq], KL fp, []⟩,
      ⟨cctNames[t]!, true, cclSlot cs w ++ [entries, cover, base * pow32 (gen ^ w), origin, gen ^ L], KL fp,
        [(digestScalars (prefixDigest cs (n - 1))).1, (digestScalars (prefixDigest cs (n - 1))).2]⟩,
      ⟨"scaled_log__L6", true, [gen ^ n, gsq], KL fp, [eOfNat (2 ^ 6 * n)]⟩]) ?_ ?_ ?_ fp
  · intro fp k hk htk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · have hw0 : 0 < w := by
        rcases Nat.eq_zero_or_pos w with h0 | h0
        · simp [h0, word_one, e_add_self] at htk
        · exact h0
      exact l87_completeAtD fs cert hκ (KL fp) hL16 hn (by omega) hlen hcan (fun rd _ h => (hKL fp rd h).2.1)
        (fun rd h => (hKL fp rd h).1) (fun rd h => (hKL fp rd h).2.2) (hregKL fp)
        (fun q hq r hr => by
          obtain ⟨e, he, h1, h2⟩ := cclScratch_slot (cs := cs) (b := fp + fs "child_claim_list_digest") (w := w) hq hr
          exact ⟨e, List.mem_append_left _ he, h1, h2⟩) 0 hw0
    · show CompleteAtD fs cert κ cctNames[t]! _ _ _
      rw [cctNames_getElem! ht32]
      exact cct_completeAtD fs cert hκ t ht32 (KL fp) hL16 rfl (off := fun k => off (32 * w + k))
        (cs := sliceOf cs (32 * w) t)
        (fun rd _ h => by rw [pow32_eq]; exact childReads_slice (hKL fp rd h).2.1 (32 * w) t (by omega))
        (fun A hA => hregKL fp A (childLoad_shift (by omega) hA)) hch
    · exact LeanVM.Guest.B1.completeAt_of_rel_pureD cldKid_pure (by simp [cldKidSet])
        (fun rd h => (scaled_log_6_iff (hKL fp rd h).1 _ _).mpr ⟨_, rfl, n, hn, rfl, rfl⟩) κ
  · intro fp k hk _ i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> exact hKLreg fp i hi
  · intro fp' rd hl hLb hLin
    have hPL := hPLm rd hLin
    refine ⟨fun k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact Main.memL_append.mpr ⟨hLb, hPL⟩, ?_⟩
    obtain ⟨hT, hR⟩ := hpre' rd hl hLin
    have hscr : ChildScratch rd (gen ^ (fp' + fs "child_claim_list_digest")) cs ((n - 1) / 32) := by
      rw [← hw]; exact cclScratch_of_memL hLb fun q hq => hq
    obtain ⟨t1, t2, t3, t4, t5, t6, hh⟩ := ccld_holds_pos (hlow rd hl) hT hL16 hn hn1 hlen hR hcan hscr hd
    rw [← hw, ← ht] at hh
    set σ := listVal (cclList entries cover base origin (gen ^ L) gsq (gen ^ (fp' + fs "child_claim_list_digest"))
      d0 d1 cs (off (n - 1)) L n w t t1 t2 t3 t4 t5 t6) with hσ
    have h8 : σ (.n 8) ≠ 0 := fun h' => by
      have h'' : gen ^ n + word 1 0 0 = 0 := h'
      rw [word_one] at h''
      have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h'')
      omega
    have hw' := walk_ccld_pos σ h8 ht32 (gen_pow_eq_ofK t)
    have hev := holds_of_holdsList find_child_claim_list_digest hh hw'
    obtain ⟨e1, e2, e3, e4, e5⟩ := ccld_pos_events σ t
    have h39 : logG (σ (.n 39)) = 4 * (w + 1) := by
      rw [show σ (.n 39) = gen ^ (4 * (w + 1)) by
        show gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0) * (gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0)) = _
        rw [word_gen]; ring]
      exact logG_gen_pow (by omega)
    refine ⟨σ, _, _, rfl, hw', rfl, hev, ?_, e3, by rw [e2, h39], ?_, fun A hA => ?_⟩
    · rw [e4]
      refine ⟨rfl, rfl, fun _ => ⟨?_, rfl⟩, rfl, rfl, fun _ => ⟨rfl, rfl⟩, rfl, rfl, fun _ => ⟨rfl, rfl⟩, trivial⟩
      show [word 1 0 0, gen ^ w, gen ^ (fp' + fs "child_claim_list_digest"), base, entries, cover, origin, gen ^ L,
        gsq] = _
      rw [word_one, pow_zero]
    · rw [e1]
      simp only [List.map_cons, List.map_nil, bases]
      rw [← gen_pow_eq_ofK]; rfl
    · rw [e5] at hA
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
      set cx := fp' + fs "child_claim_list_digest" with hcx
      have g40 : σ (.n 40) = gen ^ cx := rfl
      have g49 : σ (.n 49) = gen ^ (cx + 4 * w) := by
        show gen ^ cx * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) = _
        ring
      have g71 : σ (.n 71) = cover * (origin * gen ^ off (n - 1)) := rfl
      have g74 : σ (.n 74) = entries * gen ^ (4 * off (n - 1)) := by
        show entries * (gen ^ off (n - 1) * gen ^ off (n - 1) * (gen ^ off (n - 1) * gen ^ off (n - 1))) = _
        rw [pow4_eq _ _ rfl]
      have sl : ∀ q r, q ≤ w → r < 3 → RegionL (cclScratchL cs cx w) (cx + 4 * q + r) :=
        fun q r hq hr => cclScratch_slot hq hr
      rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨cx + 4 * 0 + 0, by rw [g40, limb0_gen_pow, gpow_add'], Or.inl (sl 0 0 (by omega) (by omega))⟩
      · exact ⟨cx + 4 * 0 + 1, by rw [g40, limb0_gen_pow, gpow_add'], Or.inl (sl 0 1 (by omega) (by omega))⟩
      · exact ⟨cx + 4 * 0 + 2, by rw [g40, limb0_gen_pow, gpow_add'], Or.inl (sl 0 2 (by omega) (by omega))⟩
      · exact ⟨cx + 4 * w + 0, by rw [g49, limb0_gen_pow, gpow_add'], Or.inl (sl w 0 le_rfl (by omega))⟩
      · exact ⟨cx + 4 * w + 1, by rw [g49, limb0_gen_pow, gpow_add'], Or.inl (sl w 1 le_rfl (by omega))⟩
      · exact ⟨cx + 4 * w + 2, by rw [g49, limb0_gen_pow, gpow_add'], Or.inl (sl w 2 le_rfl (by omega))⟩
      · exact ⟨_, by rw [g71]; exact (hmidx (n - 1) (by omega)).1, Or.inr (hmidx (n - 1) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 0 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 0 (by omega) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 1 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 1 (by omega) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 2 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 2 (by omega) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 3 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 3 (by omega) (by omega)).2⟩


/-- **`child_claim_list_digest` is complete, uniformly placed**, at the indices `off` and the claims
`cs`, on a memory defined below `2^κ`, `κ ≥ 16`. -/
theorem ccld_completeRelAtB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ)
    (off : ℕ → ℕ) (cs : List E) (Bsl Bsl6 : ℕ)
    (hsl : TotalLe coreProgram fs "scaled_log__L11" fun _ => Bsl)
    (hsl6 : TotalLe coreProgram fs "scaled_log__L6" fun _ => Bsl6) :
    ∀ (args rets : List E) (Lin : Layout), (∀ rd, LowDef κ rd → MemL rd Lin → CclPreAt off cs rd args rets) →
      CompleteAtB fs cert κ "child_claim_list_digest" Lin args (Returns rets)
        (ccldBound fs (fs "child_claims_window" + Bsl) Bsl6 (cs.length / 4)) := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _, fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨entries, cover, base, origin, limit, ng, gsq, d0, d1, rfl, rfl⟩ := cclPreAt_shape (hpre rd1 hl1 hL1)
  obtain ⟨hT1, ⟨L, hL16, rfl⟩, n, hn, rfl, hlen, hR1, hcan, hd⟩ := hpre rd1 hl1 hL1
  have hpre' : ∀ rd, LowDef κ rd → MemL rd Lin →
      SquaresAt rd gsq ∧ ChildReads rd entries cover base origin (gen ^ L) off cs n := by
    intro rd hl hL
    obtain ⟨hT, -, n', hn', hng', -, hR', -, -⟩ := hpre rd hl hL
    obtain rfl : n = n' := gen_pow_inj' (by omega) (by omega) hng'
    exact ⟨hT, hR'⟩
  have hFc : ∀ j r, ∃ i, j < n → r < 4 →
      (entries * gen ^ (4 * off j)).limb 0 * gpow r = gpow i ∧ RegionL Lin i := by
    intro j r
    by_cases h : j < n ∧ r < 4
    · obtain ⟨hj, hr⟩ := h
      have hall : ∀ rd, LowDef κ rd → MemL rd Lin →
          LoadHolds rd (entries * gen ^ (4 * off j)) r (cs.getD (4 * j + r) 0) := by
        intro rd hl hL
        have hc4 := ((hpre' rd hl hL).2 j hj).2.2
        exact match r, hr with
          | 0, _ => by simpa using hc4 0 (by simp)
          | 1, _ => by simpa using hc4 1 (by simp)
          | 2, _ => by simpa using hc4 2 (by simp)
          | 3, _ => by simpa using hc4 3 (by simp)
          | _ + 4, hr => absurd hr (by omega)
      obtain ⟨i, hi⟩ := forced_load hall hl1 hL1
      exact ⟨i, fun _ _ => hi⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose cidx hcidx using hFc
  have hFm : ∀ j, ∃ i, j < n → (cover * (origin * gen ^ off j)).limb 0 * gpow 0 = gpow i ∧ RegionL Lin i := by
    intro j
    by_cases h : j < n
    · obtain ⟨i, hi⟩ := forced_load (fun rd hl hL => ((hpre' rd hl hL).2 j h).2.1) hl1 hL1
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h1 => absurd h1 h⟩
  choose midx hmidx using hFm
  have hSq : ∀ j, ∃ i, j < 16 → gsq.limb 0 * gpow j = gpow i ∧ RegionL Lin i := by
    intro j
    by_cases hj : j < 16
    · obtain ⟨i, hi⟩ := forced_load (fun rd hl hL => (hpre' rd hl hL).1 j hj) hl1 hL1
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose sidx hsidx using hSq
  have hgK : IsInK gsq := (hT1 0 (by norm_num)).1
  have hlow : ∀ rd, LowDef κ rd → Low16 rd := fun rd hl i hi =>
    hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ))
  set PL : Layout := ccldPins cs base n cidx midx ++ pinL (fun j => gen ^ 2 ^ j) sidx 16 with hPL
  -- the pins read back as the reads and the squares table
  have hPLr : ∀ rd', MemL rd' PL → SquaresAt rd' gsq ∧ ChildReads rd' entries cover base origin (gen ^ L) off cs n := by
    intro rd' h
    refine ⟨fun j hj => pin_loads h hgK (fun j hj => (hsidx j hj).1) (fun q hq => List.mem_append_right _ hq) j hj,
      fun j hj => ⟨(hR1 j hj).1, load_of_pin h (hR1 j hj).2.1.1 (hmidx j hj).1
        (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))),
        fun r hr => ?_⟩⟩
    have hr4 : r < 4 := by simpa using hr
    have := load_of_pin h ((hR1 j hj).2.2 0 (by simp)).1 (hcidx j r hj hr4).1 (v := cs.getD (4 * j + r) 0)
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj,
        List.mem_map.mpr ⟨r, List.mem_range.mpr hr4, rfl⟩⟩)))
    have key : ([cs.getD (4 * j) 0, cs.getD (4 * j + 1) 0, cs.getD (4 * j + 2) 0, cs.getD (4 * j + 3) 0] :
        List E)[r]'hr = cs.getD (4 * j + r) 0 := getElem_four cs j r hr4
    rw [key]; exact this
  have hPLm : ∀ rd, MemL rd Lin → MemL rd PL := by
    intro rd hL q hq k hk
    have e : ∀ {i : ℕ} {v : E}, RegionL Lin i → rd1 (gpow i) = some v → q = (i, [v]) →
        LoadHolds rd (ofK (gpow q.1)) k (q.2[k]'hk) := fun {i v} hR hv hqe => by
      subst hqe
      simp only [List.length_cons, List.length_nil] at hk
      obtain rfl : k = 0 := by omega
      refine ⟨ofK_isInK _, ?_⟩
      rw [Main.addr_ofK, Nat.add_zero, Main.memL_agree hL hL1 _ hR, hv]
      rfl
    rw [hPL, List.mem_append, ccldPins, List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · obtain ⟨j, hj, hq⟩ := List.mem_flatMap.mp hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      have hj := List.mem_range.mp hj
      have hr := List.mem_range.mp hr
      refine e (hcidx j r hj hr).2 ?_ rfl
      have := ((hR1 j hj).2.2 r (by simp; omega)).2
      rw [(hcidx j r hj hr).1] at this
      rw [this]
      exact match r, hr with
        | 0, _ => by simp
        | 1, _ => by simp
        | 2, _ => by simp
        | 3, _ => by simp
        | _ + 4, hr => absurd hr (by omega)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      have hj := List.mem_range.mp hj
      refine e (hmidx j hj).2 ?_ rfl
      have := (hR1 j hj).2.1.2
      rwa [(hmidx j hj).1] at this
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      have hj := List.mem_range.mp hj
      refine e (hsidx j hj).2 ?_ rfl
      have := (hT1 j hj).2
      rwa [(hsidx j hj).1] at this
  have hPLR : ∀ i, RegionL PL i → RegionL Lin i := by
    intro i ⟨q, hq, h1, h2⟩
    rw [hPL, List.mem_append, ccldPins, List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · obtain ⟨j, hj, hq⟩ := List.mem_flatMap.mp hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      simp only [List.length_cons, List.length_nil] at h1 h2
      rw [show i = cidx j r by omega]
      exact (hcidx j r (List.mem_range.mp hj) (List.mem_range.mp hr)).2
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      simp only [List.length_cons, List.length_nil] at h1 h2
      rw [show i = midx j by omega]
      exact (hmidx j (List.mem_range.mp hj)).2
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      simp only [List.length_cons, List.length_nil] at h1 h2
      rw [show i = sidx j by omega]
      exact (hsidx j (List.mem_range.mp hj)).2
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · obtain rfl : cs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    refine ⟨fs "child_claim_list_digest", [], [d0, d1], [], ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      by unfold ccldBound; omega, fun rd hl hL => ?_⟩
    have h8 : listVal (ccldZeroList entries cover base origin (gen ^ L) gsq d0 d1) (.n 8) = 0 := by
      show (1 : E) + word 1 0 0 = 0; rw [word_one, e_add_self]
    have hw := walk_ccld_zero _ h8
    have hev := holds_of_holdsList find_child_claim_list_digest
      (ccld_holds_zero rd entries cover base origin (gen ^ L) gsq hd) hw
    obtain ⟨e1, e2, e3, e4, e5⟩ := ccld_zero_events (listVal (ccldZeroList entries cover base origin (gen ^ L) gsq d0 d1))
    have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (rd := rd) coreProgram_wf
      (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (fp := fp) (N := 0)
      find_child_claim_list_digest (Or.inl (by decide +kernel)) rfl hw rfl hev (by rw [e1, e2]; rfl) (by rw [e3]; simp)
      (by rw [e4]; exact ⟨rfl, fun _ h => h⟩) (by rw [e5]; simp) (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
    rwa [e2, List.sum_nil, Nat.add_zero, Nat.add_zero] at h
  obtain ⟨w, hw⟩ : ∃ w, w = (n - 1) / 32 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = (n - 1) % 32 := ⟨_, rfl⟩
  have ht32 : t < 32 := by omega
  have hwt : n = 32 * w + t + 1 := by omega
  have hb := blocks_canonical hlen hcan
  let KL : ℕ → Layout := fun fp => cclScratchL cs (fp + fs "child_claim_list_digest") w ++ PL
  have hKL : ∀ fp rd', MemL rd' (KL fp) → SquaresAt rd' gsq ∧
      ChildReads rd' entries cover base origin (gen ^ L) off cs n ∧ ChildScratch rd' (gen ^ (fp + fs "child_claim_list_digest")) cs w :=
    fun fp rd' h => ⟨(hPLr rd' (Main.memL_append.mp h).2).1, (hPLr rd' (Main.memL_append.mp h).2).2,
      cclScratch_of_memL h fun q hq => List.mem_append_left _ hq⟩
  have hKLreg : ∀ fp i, RegionL (KL fp) i → RegionL (cclScratchL cs (fp + fs "child_claim_list_digest") w) i ∨ RegionL Lin i := by
    intro fp i ⟨q, hq, h1, h2⟩
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inl ⟨q, hq, h1, h2⟩
    · exact Or.inr (hPLR i ⟨q, hq, h1, h2⟩)
  have hregKL : ∀ fp A, ChildLoad entries cover origin off n A → ∃ i, A = gpow i ∧ RegionL (KL fp) i := by
    intro fp A hA
    rcases hA with ⟨j, hj, rfl⟩ | ⟨j, hj, r, hr, rfl⟩
    · refine ⟨midx j, (hmidx j hj).1, ⟨(midx j, [base * gen ^ j]), ?_, le_refl _, by simp⟩⟩
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
    · refine ⟨cidx j r, (hcidx j r hj hr).1, ⟨(cidx j r, [cs.getD (4 * j + r) 0]), ?_, le_refl _, by simp⟩⟩
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩⟩)))
  have hch : ChainCells ((digestScalars (prefixDigest cs (32 * w))).1, (digestScalars (prefixDigest cs (32 * w))).2)
      (blocksOf (sliceOf cs (32 * w) t)) (baseMd (eOfNat (2 ^ 11 * w))) t
      ((digestScalars (prefixDigest cs (n - 1))).1, (digestScalars (prefixDigest cs (n - 1))).2) := by
    refine (chainCells_prefix (blocksOf_sliceOf cs (32 * w) t)
      (fun j hj => baseMd_eq w j (by omega))).mpr ⟨fun j hj r => hb _ (by omega) r, ?_⟩
    rw [show 32 * w + t = n - 1 by omega]
  refine completeAt_nodeB find_child_claim_list_digest (by
      rw [Program.loop_of_find? find_child_claim_list_digest]; decide +kernel) κ Lin _ _ [4 * (w + 1)]
    (fun fp => cclScratchL cs (fp + fs "child_claim_list_digest") w)
    (fun fp i hi => ⟨(4 * (w + 1), fp + fs "child_claim_list_digest"), List.mem_singleton_self _, (cclScratch_region hi).1,
      (cclScratch_region hi).2⟩)
    (fun fp q hq => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      have := List.mem_range.mp hj
      simp only [cclSlot, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
      omega) (fun _ => cclScratchL_disj)
    (fun fp => [⟨"__loop87", decide (word 1 0 0 + gen ^ w ≠ 0),
        [gen ^ 0, gen ^ w, gen ^ (fp + fs "child_claim_list_digest"), base, entries, cover, origin, gen ^ L, gsq], KL fp, []⟩,
      ⟨cctNames[t]!, true, cclSlot cs w ++ [entries, cover, base * pow32 (gen ^ w), origin, gen ^ L], KL fp,
        [(digestScalars (prefixDigest cs (n - 1))).1, (digestScalars (prefixDigest cs (n - 1))).2]⟩,
      ⟨"scaled_log__L6", true, [gen ^ n, gsq], KL fp, [eOfNat (2 ^ 6 * n)]⟩])
    (fun k => if k.f = "__loop87" then l87Bound fs (fs "child_claims_window" + Bsl) w 0
      else if k.f = "scaled_log__L6" then Bsl6 else fs k.f) ?_ ?_
    (ccldBound fs (fs "child_claims_window" + Bsl) Bsl6 (cs.length / 4)) ?_ ?_ fp
  · intro fp k hk htk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · have hw0 : 0 < w := by
        rcases Nat.eq_zero_or_pos w with h0 | h0
        · simp [h0, word_one, e_add_self] at htk
        · exact h0
      refine (l87_completeAtB fs cert hκ (KL fp) hL16 hn (by omega) hlen hcan (fun rd _ h => (hKL fp rd h).2.1)
        (fun rd h => (hKL fp rd h).1) (fun rd h => (hKL fp rd h).2.2) (hregKL fp)
        (fun q hq r hr => by
          obtain ⟨e, he, h1, h2⟩ := cclScratch_slot (cs := cs) (b := fp + fs "child_claim_list_digest") (w := w) hq hr
          exact ⟨e, List.mem_append_left _ he, h1, h2⟩) Bsl hsl 0 hw0).mono le_rfl (by simp [KidR.kid])
    · show CompleteAtB fs cert κ cctNames[t]! _ _ _ _
      have hne := cct_ne t ht32
      rw [cctNames_getElem! ht32] at hne ⊢
      refine (cct_completeAtB fs cert hκ t ht32 (KL fp) hL16 rfl (off := fun k => off (32 * w + k))
        (cs := sliceOf cs (32 * w) t)
        (fun rd _ h => by rw [pow32_eq]; exact childReads_slice (hKL fp rd h).2.1 (32 * w) t (by omega))
        (fun A hA => hregKL fp A (childLoad_shift (by omega) hA)) hch).mono le_rfl
        (by simp only [hne.1, hne.2, ↓reduceIte, KidR.kid, le_refl])
    · exact LeanVM.Guest.B1.completeAt_of_rel_pureB cldKid_pure (by simp [cldKidSet])
        (fun rd h => (scaled_log_6_iff (hKL fp rd h).1 _ _).mpr ⟨_, rfl, n, hn, rfl, rfl⟩) κ hsl6
  · intro fp k hk _ i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> exact hKLreg fp i hi
  · intro fp
    obtain ⟨hw0, hl87⟩ : True ∧ fs "__loop87" ≤ l87Bound fs (fs "child_claims_window" + Bsl) w 0 :=
      ⟨trivial, by unfold l87Bound; omega⟩
    have hc : n = cs.length / 4 := by omega
    have hw' : w = (n - 1) / 32 := hw
    simp only [kidsBound, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, KidR.kid, ccldBound,
      ← hc, ← hw']
    have hne := cct_ne t ht32
    have e1 : ("scaled_log__L6" = "__loop87") = False := by decide
    rw [show (n - 1) % 32 = t from ht.symm, cctNames_getElem! ht32] at *
    simp only [↓reduceIte, hne.1, hne.2, e1, Nat.add_zero]
    split <;> omega
  · intro fp' rd hl hLb hLin
    have hPL := hPLm rd hLin
    refine ⟨fun k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact Main.memL_append.mpr ⟨hLb, hPL⟩, ?_⟩
    obtain ⟨hT, hR⟩ := hpre' rd hl hLin
    have hscr : ChildScratch rd (gen ^ (fp' + fs "child_claim_list_digest")) cs ((n - 1) / 32) := by
      rw [← hw]; exact cclScratch_of_memL hLb fun q hq => hq
    obtain ⟨t1, t2, t3, t4, t5, t6, hh⟩ := ccld_holds_pos (hlow rd hl) hT hL16 hn hn1 hlen hR hcan hscr hd
    rw [← hw, ← ht] at hh
    set σ := listVal (cclList entries cover base origin (gen ^ L) gsq (gen ^ (fp' + fs "child_claim_list_digest"))
      d0 d1 cs (off (n - 1)) L n w t t1 t2 t3 t4 t5 t6) with hσ
    have h8 : σ (.n 8) ≠ 0 := fun h' => by
      have h'' : gen ^ n + word 1 0 0 = 0 := h'
      rw [word_one] at h''
      have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h'')
      omega
    have hw' := walk_ccld_pos σ h8 ht32 (gen_pow_eq_ofK t)
    have hev := holds_of_holdsList find_child_claim_list_digest hh hw'
    obtain ⟨e1, e2, e3, e4, e5⟩ := ccld_pos_events σ t
    have h39 : logG (σ (.n 39)) = 4 * (w + 1) := by
      rw [show σ (.n 39) = gen ^ (4 * (w + 1)) by
        show gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0) * (gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0)) = _
        rw [word_gen]; ring]
      exact logG_gen_pow (by omega)
    refine ⟨σ, _, _, rfl, hw', rfl, hev, ?_, e3, by rw [e2, h39], ?_, fun A hA => ?_⟩
    · rw [e4]
      refine ⟨rfl, rfl, fun _ => ⟨?_, rfl⟩, rfl, rfl, fun _ => ⟨rfl, rfl⟩, rfl, rfl, fun _ => ⟨rfl, rfl⟩, trivial⟩
      show [word 1 0 0, gen ^ w, gen ^ (fp' + fs "child_claim_list_digest"), base, entries, cover, origin, gen ^ L,
        gsq] = _
      rw [word_one, pow_zero]
    · rw [e1]
      simp only [List.map_cons, List.map_nil, bases]
      rw [← gen_pow_eq_ofK]; rfl
    · rw [e5] at hA
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
      set cx := fp' + fs "child_claim_list_digest" with hcx
      have g40 : σ (.n 40) = gen ^ cx := rfl
      have g49 : σ (.n 49) = gen ^ (cx + 4 * w) := by
        show gen ^ cx * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) = _
        ring
      have g71 : σ (.n 71) = cover * (origin * gen ^ off (n - 1)) := rfl
      have g74 : σ (.n 74) = entries * gen ^ (4 * off (n - 1)) := by
        show entries * (gen ^ off (n - 1) * gen ^ off (n - 1) * (gen ^ off (n - 1) * gen ^ off (n - 1))) = _
        rw [pow4_eq _ _ rfl]
      have sl : ∀ q r, q ≤ w → r < 3 → RegionL (cclScratchL cs cx w) (cx + 4 * q + r) :=
        fun q r hq hr => cclScratch_slot hq hr
      rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨cx + 4 * 0 + 0, by rw [g40, limb0_gen_pow, gpow_add'], Or.inl (sl 0 0 (by omega) (by omega))⟩
      · exact ⟨cx + 4 * 0 + 1, by rw [g40, limb0_gen_pow, gpow_add'], Or.inl (sl 0 1 (by omega) (by omega))⟩
      · exact ⟨cx + 4 * 0 + 2, by rw [g40, limb0_gen_pow, gpow_add'], Or.inl (sl 0 2 (by omega) (by omega))⟩
      · exact ⟨cx + 4 * w + 0, by rw [g49, limb0_gen_pow, gpow_add'], Or.inl (sl w 0 le_rfl (by omega))⟩
      · exact ⟨cx + 4 * w + 1, by rw [g49, limb0_gen_pow, gpow_add'], Or.inl (sl w 1 le_rfl (by omega))⟩
      · exact ⟨cx + 4 * w + 2, by rw [g49, limb0_gen_pow, gpow_add'], Or.inl (sl w 2 le_rfl (by omega))⟩
      · exact ⟨_, by rw [g71]; exact (hmidx (n - 1) (by omega)).1, Or.inr (hmidx (n - 1) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 0 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 0 (by omega) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 1 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 1 (by omega) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 2 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 2 (by omega) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 3 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 3 (by omega) (by omega)).2⟩

end
end LeanVM.Guest.B1.Digest
