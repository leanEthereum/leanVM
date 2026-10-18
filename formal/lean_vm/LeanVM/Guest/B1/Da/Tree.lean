/-
  LeanVM.Guest.B1.Da.Tree

  B1 for `da_levels` (11 specializations; G:3022-3031; TRIAGE #70) and its 55 level loops.
-/

module

public import LeanVM.Guest.B1.Da.Levels

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## One step of a level loop -/

/-- Iteration `x` of a level loop: the pair at `tree·g^ao·x⁴` hashed into the node at
`tree·g^bo·x²`. -/
def LvStep (rd : Reader) (tree : E) (ao bo : ℕ) (x : E) : Prop :=
  ∃ c0 c1 c2 c3 o0 o1, CellsAt rd (tree * gen ^ ao * (x * x * (x * x))) [c0, c1, c2, c3] ∧
    CompressCells ![c0, c1, c2, c3] (digestScalars paramIv).1 (digestScalars paramIv).2 o0 o1
      (metadataCell 64 true) ∧
    CellsAt rd (tree * gen ^ bo * (x * x)) [o0, o1]

theorem md64_word : word 64 4294967295 0 = metadataCell 64 true := rfl

theorem cellsAt_two {rd : Reader} {p r0 r1 : E} :
    CellsAt rd p [r0, r1] ↔ LoadHolds rd p 0 r0 ∧ LoadHolds rd p 1 r1 := by
  constructor
  · intro h
    exact ⟨h 0 (by simp), h 1 (by simp)⟩
  · rintro ⟨h0, h1⟩ k hk
    simp only [List.length_cons, List.length_nil] at hk
    rcases k with _ | _ | k
    exacts [h0, h1, absurd hk (by omega)]

theorem lv_step {rd : Reader} {k l : ℕ} (hk : k ≤ 10) (hl : l < k) (W tree : E) (C : CallRel) (x : E) :
    (∃ fn, coreProgram.find? (lvName k l) = some fn ∧ fn.Sem C rd (x :: [W, tree]) []) ↔
      LvStep rd tree (lvOff k l) (lvOff k (l + 1)) x ∧ IsInK (x * gen + W) ∧
        (x * gen + W ≠ 0 → C (lvName k l) (x * gen :: [W, tree]) []) := by
  have hf : ∀ fn, coreProgram.find? (lvName k l) = some fn ↔
      fn = ⟨lvName k l, [.n 0, .n 1, .n 2], if l = 0 then lvBody0 k else lvBody k l⟩ := fun fn => by
    rw [find_lv k l hk hl]; exact ⟨fun h => (Option.some.inj h).symm, fun h => by rw [h]⟩
  have hgw : ∀ m, 1 ≤ m → m ≤ k → word (gw (lvOff k m)) 0 0 = gen ^ lvOff k m := fun m hm1 hm => by
    refine gw_spec ?_ (by unfold lvOff; have := Nat.pow_le_pow_right (n := 2) (by norm_num) hk; omega)
    interval_cases k <;> interval_cases m <;> decide
  simp only [hf, exists_eq_left]
  rcases Nat.eq_zero_or_pos l with rfl | hl1
  · simp only [↓reduceIte, Fn.Sem, lvBody0, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds, LvStep, cellsAt_four, cellsAt_two,
      iv0_word, iv1_word, md64_word, Nat.zero_add]
    have h0 : lvOff k 0 = 0 := by simp [lvOff]
    rw [h0, pow_zero, mul_one, ← hgw 1 (by omega) (by omega)]
    constructor
    · rintro ⟨σ, hp, m3, m4, m5, c6, m7, m8, m9, l10, l11, l12, l13, c14, c15, c16, hc, l17, l18,
        c19, m20, a21, c22, m23, hk21, hnext, -⟩
      simp only [List.cons.injEq, and_true] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      rw [m5, m4, m3] at l10 l11 l12 l13
      rw [m9, m8, m7, c6] at l17 l18
      rw [c14, c15, c16] at hc
      rw [a21, m20, c19, word_gen] at hk21 hnext
      rw [m23, c22, word_gen] at hnext
      exact ⟨⟨_, _, _, _, _, _, ⟨l10, l11, l12, l13⟩, hc, ⟨l17, l18⟩⟩, hk21, hnext⟩
    · rintro ⟨⟨c0, c1, c2, c3, o0, o1, ⟨l10, l11, l12, l13⟩, hc, ⟨l17, l18⟩⟩, hk21, hnext⟩
      refine ⟨listVal [x, W, tree, x * x, x * x * (x * x), tree * (x * x * (x * x)),
        word (gw (lvOff k 1)) 0 0, tree * word (gw (lvOff k 1)) 0 0, x * x,
        tree * word (gw (lvOff k 1)) 0 0 * (x * x), c0, c1, c2, c3, (digestScalars paramIv).1,
        (digestScalars paramIv).2, metadataCell 64 true, o0, o1, word 2 0 0, x * word 2 0 0,
        x * word 2 0 0 + W, word 2 0 0, x * word 2 0 0], rfl, ?_⟩
      simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
      rw [word_gen]
      exact ⟨l10, l11, l12, l13, hc, l17, l18, hk21, hnext, trivial⟩
  · simp only [show l ≠ 0 by omega, ↓reduceIte, Fn.Sem, lvBody, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds, LvStep,
      cellsAt_four, cellsAt_two, iv0_word, iv1_word, md64_word]
    rw [← hgw l (by omega) (by omega), ← hgw (l + 1) (by omega) (by omega)]
    constructor
    · rintro ⟨σ, hp, c3, m4, m5, m6, m7, c8, m9, m10, m11, l12, l13, l14, l15, c16, c17, c18, hc,
        l19, l20, c21, m22, a23, c24, m25, hk23, hnext, -⟩
      simp only [List.cons.injEq, and_true] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      rw [m7, m6, m5, m4, c3] at l12 l13 l14 l15
      rw [m11, m10, m9, c8] at l19 l20
      rw [c16, c17, c18] at hc
      rw [a23, m22, c21, word_gen] at hk23 hnext
      rw [m25, c24, word_gen] at hnext
      exact ⟨⟨_, _, _, _, _, _, ⟨l12, l13, l14, l15⟩, hc, ⟨l19, l20⟩⟩, hk23, hnext⟩
    · rintro ⟨⟨c0, c1, c2, c3, o0, o1, ⟨l12, l13, l14, l15⟩, hc, ⟨l19, l20⟩⟩, hk23, hnext⟩
      refine ⟨listVal [x, W, tree, word (gw (lvOff k l)) 0 0, tree * word (gw (lvOff k l)) 0 0,
        x * x, x * x * (x * x), tree * word (gw (lvOff k l)) 0 0 * (x * x * (x * x)),
        word (gw (lvOff k (l + 1))) 0 0, tree * word (gw (lvOff k (l + 1))) 0 0, x * x,
        tree * word (gw (lvOff k (l + 1))) 0 0 * (x * x), c0, c1, c2, c3, (digestScalars paramIv).1,
        (digestScalars paramIv).2, metadataCell 64 true, o0, o1, word 2 0 0, x * word 2 0 0,
        x * word 2 0 0 + W, word 2 0 0, x * word 2 0 0], rfl, ?_⟩
      simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
      rw [word_gen]
      exact ⟨l12, l13, l14, l15, hc, l19, l20, hk23, hnext, trivial⟩

/-- **A level loop** runs its `2^(k-l-1)` iterations. -/
theorem lv_rel {rd : Reader} {k l : ℕ} (hk : k ≤ 10) (hl : l < k) (tree : E) :
    coreProgram.Rel rd (lvName k l) [gen ^ 0, gen ^ 2 ^ (k - l - 1), tree] [] ↔
      ∀ j < 2 ^ (k - l - 1), LvStep rd tree (lvOff k l) (lvOff k (l + 1)) (gen ^ j) := by
  have hc : 2 ^ (k - l - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : 1 ≤ 2 ^ (k - l - 1) := Nat.one_le_two_pow
  rw [loop_iff (B := fun _ x => LvStep rd tree (lvOff k l) (lvOff k (l + 1)) x)
    (fun _ _ _ _ h => h) (lv_step hk hl _ tree) 0]
  constructor
  · rintro ⟨m, hm0, hmN, hfirst, hall⟩ j hj
    have hmw : m = 2 ^ (k - l - 1) := by
      rcases Nat.lt_or_ge (2 ^ (k - l - 1)) m with hlt | hge
      · exact absurd rfl (hfirst _ (by omega) hlt)
      · exact (gen_pow_inj' (by omega) (by omega) hmN).symm
    exact hall j (by omega) (by omega)
  · intro h
    exact ⟨2 ^ (k - l - 1), by omega, rfl, fun j h1 h2 he => by
      have := gen_pow_inj' (by omega) (by omega) he; omega, fun j _ hj => h j hj⟩

/-! ## The tree -/

/-- Node `i` of level `l` over the leaves `leaf`. -/
def nodeD (leaf : ℕ → Digest) : ℕ → ℕ → Digest
  | 0, i => leaf i
  | l + 1, i => hashPair (nodeD leaf l (2 * i)) (nodeD leaf l (2 * i + 1))

/-- **`da_levels__L{2^k}_L{k}(tree)`**: for `k = 0` the root is the cells at `tree`; otherwise
the `2^k` leaves at `tree` are digests, every level of the tree is in memory, and the root is
returned. -/
def Meaning_da_levels (k : ℕ) (rd : Reader) (args rets : List E) : Prop :=
  ∃ tree r0 r1, args = [tree] ∧ rets = [r0, r1] ∧
    (k = 0 ∧ CellsAt rd tree [r0, r1] ∨ 1 ≤ k ∧ ∃ leaf : ℕ → Digest,
      (∀ l ≤ k, ∀ i < 2 ^ (k - l), CellsAt rd (tree * gen ^ (lvOff k l + 2 * i))
        [(digestScalars (nodeD leaf l i)).1, (digestScalars (nodeD leaf l i)).2]) ∧
      (r0, r1) = digestScalars (nodeD leaf k 0))

theorem blockBytes_pair (a b : Digest) :
    blockBytes ![(digestScalars a).1, (digestScalars a).2, (digestScalars b).1, (digestScalars b).2] =
      digestBytes a ++ digestBytes b := by
  rw [digestBytes_eq, digestBytes_eq]
  simp [blockBytes]

/-- One hash of a tree level, as a compression. -/
theorem compress_pair {a b : Digest} {o0 o1 : E} :
    CompressCells ![(digestScalars a).1, (digestScalars a).2, (digestScalars b).1,
        (digestScalars b).2] (digestScalars paramIv).1 (digestScalars paramIv).2 o0 o1
        (metadataCell 64 true) ↔ (o0, o1) = digestScalars (hashPair a b) := by
  rw [show (digestScalars paramIv) = Value.ivCells from rfl, blake2s_default_iff, blockBytes_pair]
  · rfl
  · intro r; fin_cases r
    exacts [(isCanonical128_digestScalars a).1, (isCanonical128_digestScalars a).2,
      (isCanonical128_digestScalars b).1, (isCanonical128_digestScalars b).2]

theorem lvOff_succ (k l : ℕ) (hl : l < k) : lvOff k (l + 1) = lvOff k l + 2 * 2 ^ (k - l) := by
  unfold lvOff
  have h1 : 2 ^ (k - l) = 2 * 2 ^ (k - (l + 1)) := by
    rw [← pow_succ']; congr 1; omega
  have h2 : 2 ^ (k - l) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem ptr_pow4 (tree : E) (a j : ℕ) :
    tree * gen ^ a * (gen ^ j * gen ^ j * (gen ^ j * gen ^ j)) = tree * gen ^ (a + 4 * j) := by
  rw [pow4_eq _ j rfl, mul_assoc, ← pow_add]

theorem ptr_pow2 (tree : E) (a j : ℕ) : tree * gen ^ a * (gen ^ j * gen ^ j) = tree * gen ^ (a + 2 * j) := by
  rw [mul_assoc, ← pow_add, ← pow_add, show j + j = 2 * j by ring]

/-- A level step, as reads of the tree. -/
theorem lvStep_iff {rd : Reader} {tree : E} {ao bo j : ℕ} :
    LvStep rd tree ao bo (gen ^ j) ↔ ∃ c0 c1 c2 c3 o0 o1,
      LoadHolds rd tree (ao + 4 * j) c0 ∧ LoadHolds rd tree (ao + 4 * j + 1) c1 ∧
      LoadHolds rd tree (ao + 4 * j + 2) c2 ∧ LoadHolds rd tree (ao + 4 * j + 3) c3 ∧
      CompressCells ![c0, c1, c2, c3] (digestScalars paramIv).1 (digestScalars paramIv).2 o0 o1
        (metadataCell 64 true) ∧
      LoadHolds rd tree (bo + 2 * j) o0 ∧ LoadHolds rd tree (bo + 2 * j + 1) o1 := by
  simp only [LvStep, ptr_pow4]
  simp only [ptr_pow2, cellsAt_four, cellsAt_two, loadHolds_mul_gen_pow, Nat.add_zero, and_assoc]

/-- The tree levels in memory, as reads. -/
def TreeMem (rd : Reader) (tree : E) (k : ℕ) (leaf : ℕ → Digest) (l : ℕ) : Prop :=
  ∀ i < 2 ^ (k - l), LoadHolds rd tree (lvOff k l + 2 * i) (digestScalars (nodeD leaf l i)).1 ∧
    LoadHolds rd tree (lvOff k l + 2 * i + 1) (digestScalars (nodeD leaf l i)).2

theorem treeMem_iff {rd : Reader} {tree : E} {k : ℕ} {leaf : ℕ → Digest} {l : ℕ} :
    TreeMem rd tree k leaf l ↔ ∀ i < 2 ^ (k - l), CellsAt rd (tree * gen ^ (lvOff k l + 2 * i))
      [(digestScalars (nodeD leaf l i)).1, (digestScalars (nodeD leaf l i)).2] := by
  simp only [TreeMem, cellsAt_two, loadHolds_mul_gen_pow, Nat.add_zero]

/-- **The levels, forward**: the loops' iterations make every level the tree of its leaves. -/
theorem treeMem_of_steps {rd : Reader} {tree : E} {k : ℕ} (hk1 : 1 ≤ k)
    (hsteps : ∀ l < k, ∀ j < 2 ^ (k - l - 1), LvStep rd tree (lvOff k l) (lvOff k (l + 1)) (gen ^ j)) :
    ∃ leaf, ∀ l ≤ k, TreeMem rd tree k leaf l := by
  refine ⟨fun i => cellsDigest (cellAt rd tree (2 * i)) (cellAt rd tree (2 * i + 1)), fun l hl => ?_⟩
  have h0 : lvOff k 0 = 0 := by simp [lvOff]
  induction l with
  | zero =>
    intro i hi
    obtain ⟨c0, c1, c2, c3, o0, o1, l0, l1, l2, l3, hc, -, -⟩ :=
      lvStep_iff.mp (hsteps 0 hk1 (i / 2) (by
        have : 2 ^ (k - 0) = 2 * 2 ^ (k - 0 - 1) := by rw [← pow_succ']; congr 1; omega
        omega))
    have hcan := hc.1
    rw [h0, Nat.zero_add] at l0 l1 l2 l3
    rw [h0, Nat.zero_add]
    simp only [nodeD]
    rcases Nat.mod_two_eq_zero_or_one i with hr | hr
    · rw [show 4 * (i / 2) = 2 * i by omega] at l0 l1
      rw [cellAt_of_load l0, cellAt_of_load l1,
        digestScalars_cellsDigest (by simpa using hcan 0) (by simpa using hcan 1)]
      exact ⟨l0, l1⟩
    · rw [show 4 * (i / 2) + 2 = 2 * i by omega] at l2
      rw [show 4 * (i / 2) + 3 = 2 * i + 1 by omega] at l3
      rw [cellAt_of_load l2, cellAt_of_load l3,
        digestScalars_cellsDigest (by simpa using hcan 2) (by simpa using hcan 3)]
      exact ⟨l2, l3⟩
  | succ l ih =>
    have hP := ih (by omega)
    intro i hi
    obtain ⟨c0, c1, c2, c3, o0, o1, l0, l1, l2, l3, hc, s0, s1⟩ :=
      lvStep_iff.mp (hsteps l (by omega) i (by rwa [show k - l - 1 = k - (l + 1) by omega]))
    obtain ⟨n0, n1⟩ := hP (2 * i) (by
      have : 2 ^ (k - l) = 2 * 2 ^ (k - (l + 1)) := by rw [← pow_succ']; congr 1; omega
      omega)
    obtain ⟨n2, n3⟩ := hP (2 * i + 1) (by
      have : 2 ^ (k - l) = 2 * 2 ^ (k - (l + 1)) := by rw [← pow_succ']; congr 1; omega
      omega)
    rw [show lvOff k l + 2 * (2 * i) = lvOff k l + 4 * i by ring] at n0 n1
    rw [show lvOff k l + 2 * (2 * i + 1) = lvOff k l + 4 * i + 2 by ring] at n2 n3
    rw [show lvOff k l + 4 * i + 2 + 1 = lvOff k l + 4 * i + 3 by ring] at n3
    rw [loadHolds_unique l0 n0, loadHolds_unique l1 n1, loadHolds_unique l2 n2,
      loadHolds_unique l3 n3, compress_pair] at hc
    have e0 := congrArg Prod.fst hc
    have e1 := congrArg Prod.snd hc
    simp only at e0 e1
    rw [e0] at s0
    rw [e1] at s1
    exact ⟨s0, s1⟩

/-- **The levels, backward**: a tree in memory makes every loop iteration hold. -/
theorem steps_of_treeMem {rd : Reader} {tree : E} {k : ℕ} {leaf : ℕ → Digest}
    (hP : ∀ l ≤ k, TreeMem rd tree k leaf l) :
    ∀ l < k, ∀ j < 2 ^ (k - l - 1), LvStep rd tree (lvOff k l) (lvOff k (l + 1)) (gen ^ j) := by
  intro l hl j hj
  have hpow : 2 ^ (k - l) = 2 * 2 ^ (k - l - 1) := by rw [← pow_succ']; congr 1; omega
  obtain ⟨n0, n1⟩ := hP l hl.le (2 * j) (by omega)
  obtain ⟨n2, n3⟩ := hP l hl.le (2 * j + 1) (by omega)
  obtain ⟨s0, s1⟩ := hP (l + 1) hl (j) (by rwa [show k - (l + 1) = k - l - 1 by omega])
  rw [show lvOff k l + 2 * (2 * j) = lvOff k l + 4 * j by ring] at n0 n1
  rw [show lvOff k l + 2 * (2 * j + 1) = lvOff k l + 4 * j + 2 by ring] at n2 n3
  rw [show lvOff k l + 4 * j + 2 + 1 = lvOff k l + 4 * j + 3 by ring] at n3
  refine lvStep_iff.mpr ⟨_, _, _, _, _, _, n0, n1, n2, n3, compress_pair.mpr rfl, s0, s1⟩

theorem gw_end {k l : ℕ} (hk : k ≤ 10) (hl : l < k) :
    word (gw (2 ^ (k - l - 1))) 0 0 = gen ^ 2 ^ (k - l - 1) := by
  refine gw_spec ?_ (by have : 2 ^ (k - l - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega); omega)
  interval_cases k <;> interval_cases l <;> decide

/-! ## The specification's tree -/

theorem toBytes_toList (d : Digest) : (Da.toBytes d).toList = digestBytes d := by
  simp [Da.toBytes]

/-- A tree level's hash, as LeanDA's. -/
theorem blake2s_pairBytes (a b : Digest) :
    Da.blake2s (LeanDa.pairBytes (Da.toBytes a) (Da.toBytes b)) = Da.toBytes (hashPair a b) := by
  rw [Da.blake2s, LeanDa.pairBytes, toBytes_toList, toBytes_toList, hashPair]

theorem nodeD_succ (leaf : ℕ → Digest) : ∀ l i,
    nodeD leaf (l + 1) i = nodeD (fun i => hashPair (leaf (2 * i)) (leaf (2 * i + 1))) l i
  | 0, i => rfl
  | l + 1, i => by rw [nodeD, nodeD_succ leaf l, nodeD_succ leaf l, nodeD]

/-- **The root is LeanDA's** (`treeRoot`, `tree_from_leaves`). -/
theorem treeRoot_nodeD : ∀ (k : ℕ) (leaf : ℕ → Digest),
    LeanDa.treeRoot Da.blake2s ((List.range (2 ^ k)).map fun i => Da.toBytes (leaf i)) =
      Da.toBytes (nodeD leaf k 0)
  | 0, leaf => by rw [LeanDa.treeRoot]; simp [nodeD]
  | k + 1, leaf => by
    rw [LeanDa.treeRoot, ite_neg' (by simp), nodeD_succ,
      ← treeRoot_nodeD k]
    congr 1
    simp only [LeanDa.treeLevel, List.length_map, List.length_range]
    rw [show 2 ^ (k + 1) / 2 = 2 ^ k by rw [pow_succ]; omega]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    simp only [LeanDa.up]
    rw [List.getD_eq_getElem _ _ (by simp; rw [pow_succ]; omega),
      List.getD_eq_getElem _ _ (by simp; rw [pow_succ]; omega)]
    simp only [List.getElem_map, List.getElem_range]
    exact blake2s_pairBytes _ _

/-- The honest values of `da_levels__L{2^k}_L{k}`. -/
def dlVals (k : ℕ) (tree r0 r1 : E) (i : ℕ) : E :=
  if i = 0 then tree else
  if i ≤ 5 * k then
    [word 1 0 0, word (gw (2 ^ (k - (i - 1) / 5 - 1))) 0 0,
      word 1 0 0 + word (gw (2 ^ (k - (i - 1) / 5 - 1))) 0 0, word 1 0 0,
      word (gw (2 ^ (k - (i - 1) / 5 - 1))) 0 0].getD ((i - 1) % 5) 0 else
  [r0, r1].getD (i - 1 - 5 * k) 0

theorem dlVals_blk (k : ℕ) (tree r0 r1 : E) (l r : ℕ) (hl : l < k) (hr : r < 5) :
    dlVals k tree r0 r1 (1 + 5 * l + r) =
      [word 1 0 0, word (gw (2 ^ (k - l - 1))) 0 0, word 1 0 0 + word (gw (2 ^ (k - l - 1))) 0 0,
        word 1 0 0, word (gw (2 ^ (k - l - 1))) 0 0].getD r 0 := by
  simp only [dlVals, show 1 + 5 * l + r ≠ 0 by omega, show 1 + 5 * l + r ≤ 5 * k by omega,
    show (1 + 5 * l + r - 1) / 5 = l by omega, show (1 + 5 * l + r - 1) % 5 = r by omega, ↓reduceIte]

theorem dlVals_end (k : ℕ) (tree r0 r1 : E) :
    dlVals k tree r0 r1 (1 + 5 * k) = r0 ∧ dlVals k tree r0 r1 (2 + 5 * k) = r1 := by
  constructor <;> simp [dlVals]

/-- **`da_levels__L{2^k}_L{k}`**. -/
theorem da_levels_iff {rd : Reader} (k : ℕ) (hk : k ≤ 10) (args rets : List E) :
    coreProgram.Rel rd (dlNames.getD k "") args rets ↔ Meaning_da_levels k rd args rets := by
  rw [rel_of_find (find_dl k hk)]
  have hnr : ∀ l, Stmt.noRetList (dlBlk k l) = true := fun l => by
    simp [dlBlk, Stmt.noRetList, Stmt.noRet]
  simp only [Fn.Sem, dlBody, holdsList_flatMap k (dlBlk k) hnr]
  simp only [dlBlk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, List.map_cons,
    List.map_nil, Meaning_da_levels, ← treeMem_iff]
  constructor
  · rintro ⟨σ, hp, hlev, l1, l2, hr⟩
    refine ⟨σ (.n 0), σ (.n (1 + 5 * k)), σ (.n (2 + 5 * k)), hp.symm, hr.symm, ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · refine Or.inl ⟨rfl, cellsAt_two.mpr ⟨by simpa using l1, by simpa using l2⟩⟩
    have hsteps : ∀ l < k, ∀ j < 2 ^ (k - l - 1),
        LvStep rd (σ (.n 0)) (lvOff k l) (lvOff k (l + 1)) (gen ^ j) := by
      intro l hl
      obtain ⟨c1, c2, a3, c4, c5, -, hnext⟩ := hlev l hl
      rw [a3, c1, c2, word_one, gw_end hk hl] at hnext
      have hne : (1 : E) + gen ^ 2 ^ (k - l - 1) ≠ 0 := by
        rw [add_comm]
        exact gen_pow_ne_one Nat.one_le_two_pow
          (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega : k - l - 1 ≤ 10)) (by norm_num))
      have h := hnext hne
      rw [c4, c5, word_one, gw_end hk hl, ← pow_zero gen] at h
      exact (lv_rel hk hl _).mp h
    obtain ⟨leaf, hP⟩ := treeMem_of_steps hk1 hsteps
    refine Or.inr ⟨hk1, leaf, fun l hl => hP l hl, ?_⟩
    obtain ⟨n0, n1⟩ := hP k le_rfl 0 (by simp)
    have hoff : lvOff k k + 2 * 0 = 4 * 2 ^ k - 4 := by simp [lvOff]
    rw [hoff] at n0 n1
    rw [show 4 * 2 ^ k - 4 + 1 = 4 * 2 ^ k - 3 by have := Nat.one_le_two_pow (n := k); omega] at n1
    rw [loadHolds_unique l1 n0, loadHolds_unique l2 n1]
  · rintro ⟨tree, r0, r1, rfl, rfl, h⟩
    have e := dlVals_blk k tree r0 r1
    obtain ⟨e1, e2⟩ := dlVals_end k tree r0 r1
    refine ⟨fun v => dlVals k tree r0 r1 v.idx, rfl, fun l hl => ?_, ?_, ?_, ?_⟩
    · have hne : (1 : E) + gen ^ 2 ^ (k - l - 1) ≠ 0 := by
        rw [add_comm]
        exact gen_pow_ne_one Nat.one_le_two_pow
          (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega : k - l - 1 ≤ 10)) (by norm_num))
      dsimp only
      rw [show 1 + 5 * l = 1 + 5 * l + 0 by rfl, e l 0 hl (by omega),
        show 2 + 5 * l = 1 + 5 * l + 1 by omega, e l 1 hl (by omega),
        show 3 + 5 * l = 1 + 5 * l + 2 by omega, e l 2 hl (by omega),
        show 4 + 5 * l = 1 + 5 * l + 3 by omega, e l 3 hl (by omega),
        show 5 + 5 * l = 1 + 5 * l + 4 by omega, e l 4 hl (by omega)]
      simp only [List.getD_cons_succ, List.getD_cons_zero, true_and]
      rw [word_one, gw_end hk hl]
      refine ⟨by rw [gen_pow_eq_ofK, ← ofK_one, ← ofK_add]; exact ofK_isInK _, fun _ => ?_⟩
      rw [← pow_zero gen, lv_rel hk hl]
      rcases h with ⟨rfl, -⟩ | ⟨-, leaf, hP, -⟩
      · omega
      · exact steps_of_treeMem hP l hl
    · show LoadHolds rd tree (4 * 2 ^ k - 4) (dlVals k tree r0 r1 (1 + 5 * k))
      rw [e1]
      rcases h with ⟨rfl, hc⟩ | ⟨-, leaf, hP, hr⟩
      · exact (cellsAt_two.mp hc).1
      · obtain ⟨n0, -⟩ := hP k le_rfl 0 (by simp)
        rw [show lvOff k k + 2 * 0 = 4 * 2 ^ k - 4 by simp [lvOff]] at n0
        rw [show r0 = (digestScalars (nodeD leaf k 0)).1 from congrArg Prod.fst hr]
        exact n0
    · show LoadHolds rd tree (4 * 2 ^ k - 3) (dlVals k tree r0 r1 (2 + 5 * k))
      rw [e2]
      rcases h with ⟨rfl, hc⟩ | ⟨-, leaf, hP, hr⟩
      · exact (cellsAt_two.mp hc).2
      · obtain ⟨-, n1⟩ := hP k le_rfl 0 (by simp)
        rw [show lvOff k k + 2 * 0 + 1 = 4 * 2 ^ k - 3 by
          simp [lvOff]; have := Nat.one_le_two_pow (n := k); omega] at n1
        rw [show r1 = (digestScalars (nodeD leaf k 0)).2 from congrArg Prod.snd hr]
        exact n1
    · show [dlVals k tree r0 r1 (1 + 5 * k), dlVals k tree r0 r1 (2 + 5 * k)] = _
      rw [e1, e2]

end
end LeanVM.Guest.B1.Digest
