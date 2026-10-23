/-
  LeanVM.Guest.B1.Da.LevelsIn

  `da_levels__L{2^k}_L{k}` and its level loops loading from a region: the tree's own `4·2^k`
  words, by trees of known words (`RelInT`).
-/

module

public import LeanVM.Guest.B1.Da.RowsIn
public import LeanVM.Guest.B1.Da.Tree

/-!
# The trees, by region

A tree of `2^k` leaves at `g^nd` lays out its levels in the words `nd ≤ i < nd + 4·2^k`
(`TreeR`): level `l`'s loop reads the pair at `nd + lvOff k l + 4j` and writes the node at
`nd + lvOff k (l + 1) + 2j`, and the tree reads the root at `nd + 4·2^k - 4`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- The words of a tree of `2^k` leaves at `g^nd`. -/
def TreeR (nd k : ℕ) (i : ℕ) : Prop := nd ≤ i ∧ i < nd + 4 * 2 ^ k

theorem gw_lvOff {k m : ℕ} (hk : k ≤ 10) (hm1 : 1 ≤ m) (hm : m ≤ k) :
    word (gw (lvOff k m)) 0 0 = gen ^ lvOff k m := by
  refine gw_spec ?_ (by unfold lvOff; have := Nat.pow_le_pow_right (n := 2) (by norm_num) hk; omega)
  interval_cases k <;> interval_cases m <;> decide

theorem lvBody_split (k l : ℕ) :
    (if l = 0 then lvBody0 k else lvBody k l) = (if l = 0 then lvBody0 k else lvBody k l).dropLast ++ [.ret []] := by
  split_ifs <;> simp [lvBody0, lvBody]

theorem lvPre_straight (k l : ℕ) :
    (if l = 0 then lvBody0 k else lvBody k l).dropLast.all Main.Stmt.straight = true := by
  split_ifs <;> simp [lvBody0, lvBody, Main.Stmt.straight]

/-- The words of level `l`'s loop from `g^j` on, of `2^(k-l-1)` iterations. -/
def lvTot (fs : String → ℕ) (f : String) (W j : ℕ) : ℕ := (W - j) * fs f + fs f

/-- **An iteration of a level loop.** -/
theorem lv_inst {rd : Reader} {k l : ℕ} (hk : k ≤ 10) (hl : l < k) {σ : Val} {fn : Fn} {es : List Ev}
    {vs : List V} {j nd : ℕ} (hf : coreProgram.find? (lvName k l) = some fn)
    (hp : fn.params.map σ = [gen ^ j, gen ^ 2 ^ (k - l - 1), gen ^ nd])
    (hw : walk σ fn.body = .ret es vs) (hok : ∀ e ∈ es, e.Ok (coreProgram.Rel rd) rd σ)
    (hj : j < 2 ^ (k - l - 1)) :
    (∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ TreeR nd k i) ∧
      calls es = [⟨lvName k l, [if l = 0 then .n 23 else .n 25, .n 1, .n 2], [],
        decide (j + 1 ≠ 2 ^ (k - l - 1))⟩] ∧
      [if l = 0 then Core.V.n 23 else .n 25, .n 1, .n 2].map σ = [gen ^ (j + 1), gen ^ 2 ^ (k - l - 1), gen ^ nd] ∧
      allocs σ es = [] := by
  rw [find_lv k l hk hl, Option.some.injEq] at hf
  subst hf
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2⟩ := hp
  rw [lvBody_split, Main.walk_straight σ _ _ (lvPre_straight k l)] at hw
  obtain ⟨rfl, -⟩ : (if l = 0 then lvBody0 k else lvBody k l).dropLast.flatMap (Main.slEvs σ) = es ∧ _ := by
    injection hw; exact ⟨by assumption, by assumption⟩
  obtain ⟨-, hal, -, hcl⟩ := Main.straight_parts σ _ (lvPre_straight k l)
  have hA : ∀ {x : Atom}, Stmt.atom x ∈ (if l = 0 then lvBody0 k else lvBody k l).dropLast → x.Holds rd σ :=
    fun hx => atom_holds_of_ok hx hok
  set P := 2 ^ (k - l - 1) with hP
  have hP1 : 2 ^ (k - l) = 2 * P := by
    rw [hP, ← pow_succ']; congr 1; omega
  have hPk : 2 * P ≤ 2 ^ k := by rw [← hP1]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlo : lvOff k l + 8 * P ≤ 4 * 2 ^ k := by unfold lvOff; rw [hP1]; omega
  have hlo1 : lvOff k (l + 1) = lvOff k l + 4 * P := by
    unfold lvOff; rw [hP1, show k - (l + 1) = k - l - 1 by omega, ← hP]; omega
  have hjP : j + 1 < 2 ^ 64 - 1 := by have := Nat.pow_le_pow_right (n := 2) (by norm_num) hk; omega
  have hdec : ∀ {c : V}, σ c = gen ^ (j + 1) + gen ^ P → decide (σ c ≠ 0) = decide (j + 1 ≠ P) :=
    fun hc => by
      rw [hc]
      have hPb : P < 2 ^ 33 := by have := Nat.pow_le_pow_right (n := 2) (by norm_num) hk; omega
      refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he, e_add_eq_zero_iff]), fun h he => h ?_⟩
      exact gen_pow_inj' (by omega) (by omega) (e_add_eq_zero_iff.mp he)
  rcases Nat.eq_zero_or_pos l with rfl | hl1
  · simp only [↓reduceIte] at hA hal hcl ⊢
    have m3 : σ (.n 3) = σ (.n 0) * σ (.n 0) := hA (x := .mul (.n 3) (.n 0) (.n 0)) (by simp [lvBody0])
    have m4 : σ (.n 4) = σ (.n 3) * σ (.n 3) := hA (x := .mul (.n 4) (.n 3) (.n 3)) (by simp [lvBody0])
    have m5 : σ (.n 5) = σ (.n 2) * σ (.n 4) := hA (x := .mul (.n 5) (.n 2) (.n 4)) (by simp [lvBody0])
    have c6 : σ (.n 6) = word (gw (lvOff k 1)) 0 0 := hA (x := .const (.n 6) _) (by simp [lvBody0])
    have m7 : σ (.n 7) = σ (.n 2) * σ (.n 6) := hA (x := .mul (.n 7) (.n 2) (.n 6)) (by simp [lvBody0])
    have m8 : σ (.n 8) = σ (.n 0) * σ (.n 0) := hA (x := .mul (.n 8) (.n 0) (.n 0)) (by simp [lvBody0])
    have m9 : σ (.n 9) = σ (.n 7) * σ (.n 8) := hA (x := .mul (.n 9) (.n 7) (.n 8)) (by simp [lvBody0])
    have c19 : σ (.n 19) = word 2 0 0 := hA (x := .const (.n 19) (word 2 0 0)) (by simp [lvBody0])
    have m20 : σ (.n 20) = σ (.n 0) * σ (.n 19) := hA (x := .mul (.n 20) (.n 0) (.n 19)) (by simp [lvBody0])
    have a21 : σ (.n 21) = σ (.n 20) + σ (.n 1) := hA (x := .add (.n 21) (.n 20) (.n 1)) (by simp [lvBody0])
    have c22 : σ (.n 22) = word 2 0 0 := hA (x := .const (.n 22) (word 2 0 0)) (by simp [lvBody0])
    have m23 : σ (.n 23) = σ (.n 0) * σ (.n 22) := hA (x := .mul (.n 23) (.n 0) (.n 22)) (by simp [lvBody0])
    have h00 : lvOff k 0 = 0 := by simp [lvOff]
    have g5 : σ (.n 5) = gen ^ (nd + lvOff k 0 + 4 * j) := by
      rw [m5, m4, m3, h2, h0, h00]; ring
    have g9 : σ (.n 9) = gen ^ (nd + lvOff k 1 + 2 * j) := by
      rw [m9, m8, m7, c6, h2, h0, gw_lvOff hk (by omega) (by omega)]; ring
    have hlo1' : lvOff k 1 = lvOff k 0 + 4 * P := by rw [← hlo1]
    refine ⟨fun A hA' => ?_, ?_, ?_, by rw [hal]; rfl⟩
    · rw [loadAddrs_straight σ _ (by simpa using lvPre_straight k 0),
        show (lvBody0 k).dropLast.filterMap stmtLoad? =
          [(.n 5, 0), (.n 5, 1), (.n 5, 2), (.n 5, 3), (.n 9, 0), (.n 9, 1)] from rfl] at hA'
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA'
      rcases hA' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, by rw [g5, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g5, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g5, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g5, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g9, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g9, addr_gen], by unfold TreeR; omega⟩
    · rw [hcl, show (lvBody0 k).dropLast.filterMap Main.Stmt.callS =
        [(some (.n 21), lvName k 0, [.n 23, .n 1, .n 2], [])] from rfl]
      simp only [List.map_cons, List.map_nil, Main.mkCall]
      rw [hdec (by rw [a21, m20, c19, h0, h1, word_gen, pow_succ])]
    · simp only [List.map_cons, List.map_nil]
      rw [m23, c22, h0, h1, h2, word_gen, pow_succ]
  · have hl0 : l ≠ 0 := by omega
    simp only [hl0, ↓reduceIte] at hA hal hcl ⊢
    have c3 : σ (.n 3) = word (gw (lvOff k l)) 0 0 := hA (x := .const (.n 3) _) (by simp [lvBody])
    have m4 : σ (.n 4) = σ (.n 2) * σ (.n 3) := hA (x := .mul (.n 4) (.n 2) (.n 3)) (by simp [lvBody])
    have m5 : σ (.n 5) = σ (.n 0) * σ (.n 0) := hA (x := .mul (.n 5) (.n 0) (.n 0)) (by simp [lvBody])
    have m6 : σ (.n 6) = σ (.n 5) * σ (.n 5) := hA (x := .mul (.n 6) (.n 5) (.n 5)) (by simp [lvBody])
    have m7 : σ (.n 7) = σ (.n 4) * σ (.n 6) := hA (x := .mul (.n 7) (.n 4) (.n 6)) (by simp [lvBody])
    have c8 : σ (.n 8) = word (gw (lvOff k (l + 1))) 0 0 := hA (x := .const (.n 8) _) (by simp [lvBody])
    have m9 : σ (.n 9) = σ (.n 2) * σ (.n 8) := hA (x := .mul (.n 9) (.n 2) (.n 8)) (by simp [lvBody])
    have m10 : σ (.n 10) = σ (.n 0) * σ (.n 0) := hA (x := .mul (.n 10) (.n 0) (.n 0)) (by simp [lvBody])
    have m11 : σ (.n 11) = σ (.n 9) * σ (.n 10) := hA (x := .mul (.n 11) (.n 9) (.n 10)) (by simp [lvBody])
    have c21 : σ (.n 21) = word 2 0 0 := hA (x := .const (.n 21) (word 2 0 0)) (by simp [lvBody])
    have m22 : σ (.n 22) = σ (.n 0) * σ (.n 21) := hA (x := .mul (.n 22) (.n 0) (.n 21)) (by simp [lvBody])
    have a23 : σ (.n 23) = σ (.n 22) + σ (.n 1) := hA (x := .add (.n 23) (.n 22) (.n 1)) (by simp [lvBody])
    have c24 : σ (.n 24) = word 2 0 0 := hA (x := .const (.n 24) (word 2 0 0)) (by simp [lvBody])
    have m25 : σ (.n 25) = σ (.n 0) * σ (.n 24) := hA (x := .mul (.n 25) (.n 0) (.n 24)) (by simp [lvBody])
    have g7 : σ (.n 7) = gen ^ (nd + lvOff k l + 4 * j) := by
      rw [m7, m6, m5, m4, c3, h2, h0, gw_lvOff hk (by omega) (by omega)]; ring
    have g11 : σ (.n 11) = gen ^ (nd + lvOff k (l + 1) + 2 * j) := by
      rw [m11, m10, m9, c8, h2, h0, gw_lvOff hk (by omega) (by omega)]; ring
    refine ⟨fun A hA' => ?_, ?_, ?_, by rw [hal]; rfl⟩
    · rw [loadAddrs_straight σ _ (by simpa [hl0] using lvPre_straight k l),
        show (lvBody k l).dropLast.filterMap stmtLoad? =
          [(.n 7, 0), (.n 7, 1), (.n 7, 2), (.n 7, 3), (.n 11, 0), (.n 11, 1)] from rfl] at hA'
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA'
      rcases hA' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, by rw [g7, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g7, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g7, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g7, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g11, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g11, addr_gen], by unfold TreeR; omega⟩
    · rw [hcl, show (lvBody k l).dropLast.filterMap Main.Stmt.callS =
        [(some (.n 23), lvName k l, [.n 25, .n 1, .n 2], [])] from rfl]
      simp only [List.map_cons, List.map_nil, Main.mkCall]
      rw [hdec (by rw [a23, m22, c21, h0, h1, word_gen, pow_succ])]
    · simp only [List.map_cons, List.map_nil]
      rw [m25, c24, h0, h1, h2, word_gen, pow_succ]

/-! ## The tree -/

/-- The tree's statements before its return. -/
def dlPre (k : ℕ) : List Stmt :=
  (List.range k).flatMap (dlBlk k) ++
  [.atom (.load (.n (1 + 5 * k)) (.n 0) (4 * 2 ^ k - 4)), .atom (.load (.n (2 + 5 * k)) (.n 0) (4 * 2 ^ k - 3))]

theorem dlBody_split (k : ℕ) : dlBody k = dlPre k ++ [.ret [.n (1 + 5 * k), .n (2 + 5 * k)]] := by
  simp [dlBody, dlPre]

theorem dlPre_straight (k : ℕ) : (dlPre k).all Main.Stmt.straight = true := by
  simp [dlPre, dlBlk, Main.Stmt.straight, List.all_flatMap]

theorem dlPre_loads (k : ℕ) : (dlPre k).filterMap stmtLoad? = [(.n 0, 4 * 2 ^ k - 4), (.n 0, 4 * 2 ^ k - 3)] := by
  simp [dlPre, dlBlk, stmtLoad?, List.filterMap_flatMap]

theorem dlPre_calls (k : ℕ) : (dlPre k).filterMap Main.Stmt.callS =
    (List.range k).map fun l => (some (.n (3 + 5 * l)), lvName k l, [.n (4 + 5 * l), .n (5 + 5 * l), .n 0], []) := by
  have e : ∀ l, (dlBlk k l).filterMap Main.Stmt.callS =
      [(some (.n (3 + 5 * l)), lvName k l, [.n (4 + 5 * l), .n (5 + 5 * l), .n 0], [])] := fun _ => rfl
  rw [dlPre, List.filterMap_append, List.filterMap_flatMap]
  simp only [e]
  rw [show List.filterMap Main.Stmt.callS [Stmt.atom (.load (.n (1 + 5 * k)) (.n 0) (4 * 2 ^ k - 4)),
    Stmt.atom (.load (.n (2 + 5 * k)) (.n 0) (4 * 2 ^ k - 3))] = [] from rfl, List.append_nil]
  induction (List.range k) with
  | nil => rfl
  | cons a as ih => rw [List.flatMap_cons, ih]; rfl

theorem dlPre_allocs (k : ℕ) : (dlPre k).filterMap Main.Stmt.allocSz = [] := by
  simp [dlPre, dlBlk, Main.Stmt.allocSz, List.filterMap_flatMap]

/-- **An instance of the tree `da_levels__L{2^k}_L{k}` at `g^nd`.** -/
theorem dl_inst {rd : Reader} {k : ℕ} (hk : k ≤ 10) {σ : Val} {fn : Fn} {es : List Ev} {vs : List V}
    {nd : ℕ} (hf : coreProgram.find? (dlNames.getD k "") = some fn) (hp : fn.params.map σ = [gen ^ nd])
    (hw : walk σ fn.body = .ret es vs) (hok : ∀ e ∈ es, e.Ok (coreProgram.Rel rd) rd σ) :
    (∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ TreeR nd k i) ∧
      calls es = (List.range k).map (fun l => ⟨lvName k l, [.n (4 + 5 * l), .n (5 + 5 * l), .n 0], [], true⟩) ∧
      (∀ l < k, [Core.V.n (4 + 5 * l), .n (5 + 5 * l), .n 0].map σ = [gen ^ 0, gen ^ 2 ^ (k - l - 1), gen ^ nd]) ∧
      allocs σ es = [] := by
  rw [find_dl k hk, Option.some.injEq] at hf
  subst hf
  have h0 : σ (.n 0) = gen ^ nd := by simpa using hp
  rw [dlBody_split, Main.walk_straight σ _ _ (dlPre_straight k)] at hw
  obtain ⟨rfl, -⟩ : (dlPre k).flatMap (Main.slEvs σ) = es ∧ _ := by
    injection hw; exact ⟨by assumption, by assumption⟩
  obtain ⟨-, hal, -, hcl⟩ := Main.straight_parts σ _ (dlPre_straight k)
  have hA : ∀ {x : Atom}, Stmt.atom x ∈ dlPre k → x.Holds rd σ := fun hx => atom_holds_of_ok hx hok
  have hblk : ∀ l < k, ∀ {x : Atom}, Stmt.atom x ∈ dlBlk k l → x.Holds rd σ := fun l hl x hx =>
    hA (List.mem_append_left _ (List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl, hx⟩))
  have hvals : ∀ l < k, σ (.n (1 + 5 * l)) = 1 ∧ σ (.n (2 + 5 * l)) = gen ^ 2 ^ (k - l - 1) ∧
      σ (.n (3 + 5 * l)) = σ (.n (1 + 5 * l)) + σ (.n (2 + 5 * l)) ∧ σ (.n (4 + 5 * l)) = 1 ∧
      σ (.n (5 + 5 * l)) = gen ^ 2 ^ (k - l - 1) := fun l hl => by
    have c1 : σ (.n (1 + 5 * l)) = word 1 0 0 := hblk l hl (x := .const _ _) (by simp [dlBlk])
    have c2 : σ (.n (2 + 5 * l)) = word (gw (2 ^ (k - l - 1))) 0 0 := hblk l hl (x := .const _ _) (by simp [dlBlk])
    have a3 : σ (.n (3 + 5 * l)) = σ (.n (1 + 5 * l)) + σ (.n (2 + 5 * l)) :=
      hblk l hl (x := .add _ _ _) (by simp [dlBlk])
    have c4 : σ (.n (4 + 5 * l)) = word 1 0 0 := hblk l hl (x := .const (.n (4 + 5 * l)) _) (by simp [dlBlk])
    have c5 : σ (.n (5 + 5 * l)) = word (gw (2 ^ (k - l - 1))) 0 0 :=
      hblk l hl (x := .const (.n (5 + 5 * l)) _) (by simp [dlBlk])
    rw [word_one] at c1 c4
    rw [gw_end hk hl] at c2 c5
    exact ⟨c1, c2, a3, c4, c5⟩
  refine ⟨fun A hA' => ?_, ?_, fun l hl => ?_, by rw [hal, dlPre_allocs]; rfl⟩
  · rw [loadAddrs_straight σ _ (dlPre_straight k), dlPre_loads] at hA'
    have hpk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA'
    rcases hA' with rfl | rfl
    · exact ⟨_, by rw [h0, addr_gen], by unfold TreeR; omega⟩
    · exact ⟨_, by rw [h0, addr_gen], by unfold TreeR; omega⟩
  · rw [hcl, dlPre_calls, List.map_map]
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    obtain ⟨e1, e2, e3, -, -⟩ := hvals l hl'
    simp only [Function.comp_apply, Main.mkCall]
    congr 1
    rw [e3, e1, e2, decide_eq_true_iff, ne_eq, e_add_eq_zero_iff]
    intro he
    have hb : 2 ^ (k - l - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := (gen_pow_eq_one_iff (show 2 ^ (k - l - 1) < 2 ^ 64 - 1 by omega)).mp he.symm
    exact absurd this (by positivity)
  · obtain ⟨-, -, -, e4, e5⟩ := hvals l hl
    simp only [List.map_cons, List.map_nil, e4, e5, h0, pow_zero]

/-- The words of the tree of `2^k` leaves: its frame and its level loops'. -/
def dlTot (fs : String → ℕ) (k : ℕ) : ℕ :=
  fs (dlNames.getD k "") + ((List.range k).map fun l => lvTot fs (lvName k l) (2 ^ (k - l - 1)) 0).sum

theorem lvName_ne {k l : ℕ} (hk : k ≤ 10) (hl : l < k) : lvName k l ≠ dlNames.getD k "" := by
  interval_cases k <;> interval_cases l <;> decide

/-- **A tree by region**: `da_levels__L{2^k}_L{k}` at `g^nd` loads only its own words. -/
theorem levels_relInT (fs : String → ℕ) {rd : Reader} {k : ℕ} (hk : k ≤ 10) {nd : ℕ} {R : ℕ → Prop}
    (hR : ∀ i, TreeR nd k i → R i) {rets : List E} (h : coreProgram.Rel rd (dlNames.getD k "") [gen ^ nd] rets) :
    RelInTW fs rd R (dlTot fs k) (dlNames.getD k "") [gen ^ nd] rets fun θ => dlTot θ k := by
  have hb : ∀ l < k, 2 ^ (k - l - 1) < 2 ^ 64 - 2 := fun l hl => by
    have : 2 ^ (k - l - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have key := relInTW_of_inv fs (R := R)
    (fun f args => (f = dlNames.getD k "" ∧ args = [gen ^ nd]) ∨
      (∃ l < k, f = lvName k l ∧ ∃ j < 2 ^ (k - l - 1), args = [gen ^ j, gen ^ 2 ^ (k - l - 1), gen ^ nd]))
    (fun θ f args => if f = dlNames.getD k "" then dlTot θ k
      else lvTot θ f (logG (args.getD 1 0)) (logG (args.getD 0 0)))
    (fun f args σ fn es vs hI hf hp hw hok => ?_) (Or.inl ⟨rfl, rfl⟩) h
  · simpa using key
  rcases hI with ⟨rfl, rfl⟩ | ⟨l, hl, rfl, j, hj, rfl⟩
  · obtain ⟨hld, hc, hargs, ha⟩ := dl_inst hk hf hp hw hok
    refine ⟨fun A hA => ?_, fun c hc' _ => ?_, ?_⟩
    · obtain ⟨i, hi, hT⟩ := hld A hA
      exact ⟨i, hi, hR i hT⟩
    · rw [hc] at hc'
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc'
      have hl' := List.mem_range.mp hl
      exact Or.inr ⟨l, hl', rfl, 0, by positivity, hargs l hl'⟩
    · intro θ
      rw [hc, ha, callsTot, List.map_map, List.sum_nil, Nat.add_zero]
      simp only [↓reduceIte, dlTot]
      congr 2
      refine List.map_congr_left fun l hl => ?_
      have hl' := List.mem_range.mp hl
      simp only [Function.comp_apply, ↓reduceIte, hargs l hl', lvName_ne hk hl', List.getD_cons_succ,
        List.getD_cons_zero, logG_gen_pow (show 0 < 2 ^ 64 - 1 by norm_num),
        logG_gen_pow (show 2 ^ (k - l - 1) < 2 ^ 64 - 1 by have := hb l hl'; omega)]
  · obtain ⟨hld, hc, hnext, ha⟩ := lv_inst hk hl hf hp hw hok hj
    refine ⟨fun A hA => ?_, fun c hc' ht => ?_, ?_⟩
    · obtain ⟨i, hi, hT⟩ := hld A hA
      exact ⟨i, hi, hR i hT⟩
    · rw [hc] at hc'
      obtain rfl := List.mem_singleton.mp hc'
      simp only [decide_eq_true_eq] at ht
      exact Or.inr ⟨l, hl, rfl, j + 1, by omega, hnext⟩
    · intro θ
      have hbl := hb l hl
      rw [hc, ha, callsTot]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, lvName_ne hk hl,
        ↓reduceIte, hnext, List.getD_cons_succ, List.getD_cons_zero]
      rw [logG_gen_pow (show j < 2 ^ 64 - 1 by omega), logG_gen_pow (show 2 ^ (k - l - 1) < 2 ^ 64 - 1 by omega)]
      by_cases hj1 : j + 1 = 2 ^ (k - l - 1)
      · simp only [hj1, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, lvTot]
        rw [show 2 ^ (k - l - 1) - j = 1 by omega]
        ring
      · simp only [ne_eq, hj1, not_false_eq_true, decide_true, ↓reduceIte, lvTot]
        rw [logG_gen_pow (show j + 1 < 2 ^ 64 - 1 by omega),
          show 2 ^ (k - l - 1) - j = (2 ^ (k - l - 1) - (j + 1)) + 1 by omega]
        ring

end
end LeanVM.Guest.B1.Digest
