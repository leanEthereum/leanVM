/-
  LeanVM.Guest.B1.Gkr.GlCTail

  The layer's tail (`glTail o`, canonically numbered), completely: on its equations, the children
  read and absorbed, their check, the two new coordinates and the next slot hold.
-/

module

public import LeanVM.Guest.B1.Gkr.GlCRound
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_layer__L0_L0»

/-!
# The layer's tail, completely

On a valuation `τ` (the layer's honest valuation renamed by `glRho p o`) satisfying the tail's
equations (`GoodS` with no stores; the stores' equations are not asked):

* `glct_kids`: the twelve children read at `τ 80·g^off`, packed and copied, absorbed four at a
  permutation over the last round's capacity (`141 ..`);
* `glct_check`: the last claim (`159`) is the children's products' polynomial at the combiner;
* `glct_y`: the two new coordinates squeezed and stored at `pt[40]`, `pt[41]`;
* `glct_next`: the next slot stored.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1 LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {τ : Val} {kret : List E → Prop} {w : ℕ → E}

theorem glKids_chT {off i : ℕ} (hi : i < 12) {s : Stmt} (hs : s ∈ chT (.n (val% «gkr_layer__L0_L0» "tcur")) off (val% «gkr_layer__L0_L0» "x@9") i) :
    s ∈ glKids off := by
  unfold glKids
  simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_range]
  rcases (by omega : i < 4 ∨ (4 ≤ i ∧ i < 8) ∨ 8 ≤ i) with h | h | h
  · exact .inl (.inl (.inl (.inl ⟨_, ⟨i, h, rfl⟩, hs⟩)))
  · refine .inl (.inl (.inr ⟨_, ⟨i - 4, by omega, ?_⟩, hs⟩))
    rw [show 4 + (i - 4) = i by omega]
  · refine .inr ⟨_, ⟨i - 8, by omega, ?_⟩, hs⟩
    rw [show 8 + (i - 8) = i by omega]

theorem glKids_atoms (off : ℕ) : ∀ s ∈ glKids off, ∃ a, s = .atom a := by
  intro s hs
  unfold glKids at hs
  simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (((⟨_, ⟨i, -, rfl⟩, hs⟩ | rfl) | ⟨_, ⟨i, -, rfl⟩, hs⟩) | rfl) | ⟨_, ⟨i, -, rfl⟩, hs⟩
  all_goals first
    | exact ⟨_, rfl⟩
    | (simp only [chT, fsNextT, fsPackT, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hs
       rcases hs with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩)

theorem straight_of_atoms {ss : List Stmt} (h : ∀ s ∈ ss, ∃ a, s = .atom a) :
    ss.all straightB = true :=
  List.all_eq_true.mpr fun s hs ↦ by obtain ⟨a, rfl⟩ := h s hs; rfl

/-- **The children** read at `τ 80·g^off` and absorbed four at a permutation over `cap`. -/
theorem glct_kids {off : ℕ} (hG : ∀ s ∈ glKids off, GoodS rd [] w τ s) {cap : List E}
    (hcap : (glCap (val% «gkr_layer__L0_L0» "nxt[8]@3")).map τ = cap) {ch : List E} (hch : ch.length = 12)
    (hr : ReadsAt rd (τ (.n (val% «gkr_layer__L0_L0» "tcur")) * gen ^ off) ch) :
    Stmt.HoldsList C rd τ (glKids off) True kret ∧
      (∀ i < 12, τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") i)) = ch.getD i 0 ∧ τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") i + 3)) = τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") i)) ∧
        FsPackOk τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") i)) (chB (val% «gkr_layer__L0_L0» "x@9") i + 1) dsObserve) ∧
      (lyCap (val% «gkr_layer__L0_L0» "nxt[0]@5")).map τ = capOf (Fs.perm ⟨capOf (Fs.perm ⟨cap,
        (chWords τ (val% «gkr_layer__L0_L0» "x@9") 0).map (·, dsObserve)⟩), (chWords τ (val% «gkr_layer__L0_L0» "x@9") 1).map (·, dsObserve)⟩) := by
  have EV : ∀ i < 12, (∀ s ∈ chT (.n (val% «gkr_layer__L0_L0» "tcur")) off (val% «gkr_layer__L0_L0» "x@9") i, SHolds C rd τ s) ∧
      τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") i)) = ch.getD i 0 ∧ τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") i + 3)) = τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") i)) ∧
      FsPackOk τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") i)) (chB (val% «gkr_layer__L0_L0» "x@9") i + 1) dsObserve := by
    intro i hi
    have gb : ∀ s ∈ chT (.n (val% «gkr_layer__L0_L0» "tcur")) off (val% «gkr_layer__L0_L0» "x@9") i, GoodS rd [] w τ s := fun s hs ↦ hG s (glKids_chT hi hs)
    have hl : LoadHolds rd (τ (.n (val% «gkr_layer__L0_L0» "tcur"))) (off + i) (ch.getD i 0) := by
      have := hr i (by rw [hch]; exact hi)
      rw [← List.getD_eq_getElem _ 0, loadHolds_mul_gen_pow] at this
      exact this
    obtain ⟨e0, -, hfs⟩ := fsNextT_good (C := C) (kret := kret) (S := [])
      (fun s hs ↦ gb s (by unfold chT; exact List.mem_append_left _ hs)) (by simp) hl
    have cp : τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") i + 3)) = τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") i)) :=
      gb (.atom (.copy (.n (chB (val% «gkr_layer__L0_L0» "x@9") i + 3)) (.n (chB (val% «gkr_layer__L0_L0» "x@9") i)))) (by simp [chT])
    obtain ⟨⟨hld, hok⟩, -⟩ := (holds_fsNextT _ _ _ _ _).mp hfs
    refine ⟨?_, e0, cp, hok⟩
    simp only [chT, fsNextT, fsPackT, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro s (rfl | rfl | rfl | rfl)
    · exact hld
    · exact hok.1
    · exact hok.2
    · exact cp
  have hp : ∀ m < 3, ∀ i < 4,
      FsPackOk τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * m + i))) (chB (val% «gkr_layer__L0_L0» "x@9") (4 * m + i) + 1) dsObserve :=
    fun m hm i hi => (EV (4 * m + i) (by omega)).2.2.2
  obtain ⟨k1, -⟩ := keccak_good (rd := rd) (S := []) (w := w) (hG (.atom (.keccak (chRate (val% «gkr_layer__L0_L0» "x@9") 0 ++ glCap (val% «gkr_layer__L0_L0» "nxt[8]@3")) (lyOuts (val% «gkr_layer__L0_L0» "nxt[0]@4"))
    false false)) (by simp [glKids]))
  obtain ⟨-, B0⟩ := ch_perm_block (hp 0 (by omega)) k1
  rw [hcap] at B0
  obtain ⟨k2, -⟩ := keccak_good (rd := rd) (S := []) (w := w) (hG (.atom (.keccak (chRate (val% «gkr_layer__L0_L0» "x@9") 1 ++ lyCap (val% «gkr_layer__L0_L0» "nxt[0]@4")) (lyOuts (val% «gkr_layer__L0_L0» "nxt[0]@5"))
    false false)) (by simp [glKids]))
  obtain ⟨-, B1⟩ := ch_perm_block (hp 1 (by omega)) k2
  rw [B0] at B1
  refine ⟨?_, fun i hi => (EV i hi).2, B1⟩
  refine holdsList_straightN _ (straight_of_atoms (glKids_atoms off)) (fun s hs ↦ ?_) trivial
  unfold glKids at hs
  simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (((⟨_, ⟨i, hi, rfl⟩, hs⟩ | rfl) | ⟨_, ⟨i, hi, rfl⟩, hs⟩) | rfl) |
    ⟨_, ⟨i, hi, rfl⟩, hs⟩
  · exact (EV i (by omega)).1 s hs
  · exact k1
  · exact (EV (4 + i) (by omega)).1 s hs
  · exact k2
  · exact (EV (8 + i) (by omega)).1 s hs

theorem glCheck_atoms : ∀ s ∈ glCheck, ∃ a, s = .atom a := by
  intro s hs; simp only [glCheck, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    exact ⟨_, h⟩

/-- **The check**: the last claim is the children's products' polynomial at the combiner. -/
theorem glct_check (hG : ∀ s ∈ glCheck, GoodS rd [] w τ s)
    (cp : ∀ i < 12, τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") i + 3)) = τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") i)))
    (hcl : τ (.n (val% «gkr_layer__L0_L0» "nclaim@2")) = polyEval [prodE (chWords τ (val% «gkr_layer__L0_L0» "x@9") 0), prodE (chWords τ (val% «gkr_layer__L0_L0» "x@9") 1),
      prodE (chWords τ (val% «gkr_layer__L0_L0» "x@9") 2)] (τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@1")))) :
    Stmt.HoldsList C rd τ glCheck True kret := by
  have g : ∀ a, Stmt.atom a ∈ glCheck → Good rd [] w τ a := fun a ha ↦ hG _ ha
  have m233 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "product@1")) (.n (val% «gkr_layer__L0_L0» "evals[8]")) (.n (val% «gkr_layer__L0_L0» "evals[9]"))) (by simp [glCheck])) (by omega) (by omega)
  have m234 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "product@2")) (.n (val% «gkr_layer__L0_L0» "product@1")) (.n (val% «gkr_layer__L0_L0» "evals[10]"))) (by simp [glCheck])) (by omega) (by omega)
  have m235 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "product@3")) (.n (val% «gkr_layer__L0_L0» "product@2")) (.n (val% «gkr_layer__L0_L0» "evals[11]"))) (by simp [glCheck])) (by omega) (by omega)
  have c236 : τ (.n (val% «gkr_layer__L0_L0» "combined@1~0")) = word 0 0 := g (.const (.n (val% «gkr_layer__L0_L0» "combined@1~0")) (word 0 0)) (by simp [glCheck])
  have m237 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "combined@1~1")) (.n (val% «gkr_layer__L0_L0» "nxt[0]@1")) (.n (val% «gkr_layer__L0_L0» "combined@1~0"))) (by simp [glCheck])) (by omega) (by omega)
  have a238 : τ (.n (val% «gkr_layer__L0_L0» "combined@1")) = τ (.n (val% «gkr_layer__L0_L0» "product@3")) + τ (.n (val% «gkr_layer__L0_L0» "combined@1~1")) :=
    g (.add (.n (val% «gkr_layer__L0_L0» "combined@1")) (.n (val% «gkr_layer__L0_L0» "product@3")) (.n (val% «gkr_layer__L0_L0» "combined@1~1"))) (by simp [glCheck])
  have m239 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "product@4")) (.n (val% «gkr_layer__L0_L0» "evals[4]")) (.n (val% «gkr_layer__L0_L0» "evals[5]"))) (by simp [glCheck])) (by omega) (by omega)
  have m240 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "product@5")) (.n (val% «gkr_layer__L0_L0» "product@4")) (.n (val% «gkr_layer__L0_L0» "evals[6]"))) (by simp [glCheck])) (by omega) (by omega)
  have m241 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "product@6")) (.n (val% «gkr_layer__L0_L0» "product@5")) (.n (val% «gkr_layer__L0_L0» "evals[7]"))) (by simp [glCheck])) (by omega) (by omega)
  have m242 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "combined@2~0")) (.n (val% «gkr_layer__L0_L0» "nxt[0]@1")) (.n (val% «gkr_layer__L0_L0» "combined@1"))) (by simp [glCheck])) (by omega) (by omega)
  have a243 : τ (.n (val% «gkr_layer__L0_L0» "combined@2")) = τ (.n (val% «gkr_layer__L0_L0» "product@6")) + τ (.n (val% «gkr_layer__L0_L0» "combined@2~0")) :=
    g (.add (.n (val% «gkr_layer__L0_L0» "combined@2")) (.n (val% «gkr_layer__L0_L0» "product@6")) (.n (val% «gkr_layer__L0_L0» "combined@2~0"))) (by simp [glCheck])
  have m244 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "product@7")) (.n (val% «gkr_layer__L0_L0» "evals[0]")) (.n (val% «gkr_layer__L0_L0» "evals[1]"))) (by simp [glCheck])) (by omega) (by omega)
  have m245 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "product@8")) (.n (val% «gkr_layer__L0_L0» "product@7")) (.n (val% «gkr_layer__L0_L0» "evals[2]"))) (by simp [glCheck])) (by omega) (by omega)
  have m246 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "product@9")) (.n (val% «gkr_layer__L0_L0» "product@8")) (.n (val% «gkr_layer__L0_L0» "evals[3]"))) (by simp [glCheck])) (by omega) (by omega)
  have m247 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "combined@3~0")) (.n (val% «gkr_layer__L0_L0» "nxt[0]@1")) (.n (val% «gkr_layer__L0_L0» "combined@2"))) (by simp [glCheck])) (by omega) (by omega)
  have a248 : τ (.n (val% «gkr_layer__L0_L0» "combined@3")) = τ (.n (val% «gkr_layer__L0_L0» "product@9")) + τ (.n (val% «gkr_layer__L0_L0» "combined@3~0")) :=
    g (.add (.n (val% «gkr_layer__L0_L0» "combined@3")) (.n (val% «gkr_layer__L0_L0» "product@9")) (.n (val% «gkr_layer__L0_L0» "combined@3~0"))) (by simp [glCheck])
  have e248 : τ (.n (val% «gkr_layer__L0_L0» "combined@3")) = τ (.n (val% «gkr_layer__L0_L0» "nclaim@2")) := by
    rw [hcl, a248, m247, a243, m242, a238, m237, c236, word_zero, m235, m234, m233, m241, m240,
      m239, m246, m245, m244, chWords_eq, chWords_eq, chWords_eq,
      show τ (.n (val% «gkr_layer__L0_L0» "evals[0]")) = τ (.n (val% «gkr_layer__L0_L0» "x@9")) from cp 0 (by omega), show τ (.n (val% «gkr_layer__L0_L0» "evals[1]")) = τ (.n (val% «gkr_layer__L0_L0» "x@10")) from cp 1 (by omega),
      show τ (.n (val% «gkr_layer__L0_L0» "evals[2]")) = τ (.n (val% «gkr_layer__L0_L0» "x@11")) from cp 2 (by omega), show τ (.n (val% «gkr_layer__L0_L0» "evals[3]")) = τ (.n (val% «gkr_layer__L0_L0» "x@12")) from cp 3 (by omega),
      show τ (.n (val% «gkr_layer__L0_L0» "evals[4]")) = τ (.n (val% «gkr_layer__L0_L0» "x@13")) from cp 4 (by omega), show τ (.n (val% «gkr_layer__L0_L0» "evals[5]")) = τ (.n (val% «gkr_layer__L0_L0» "x@14")) from cp 5 (by omega),
      show τ (.n (val% «gkr_layer__L0_L0» "evals[6]")) = τ (.n (val% «gkr_layer__L0_L0» "x@15")) from cp 6 (by omega), show τ (.n (val% «gkr_layer__L0_L0» "evals[7]")) = τ (.n (val% «gkr_layer__L0_L0» "x@16")) from cp 7 (by omega),
      show τ (.n (val% «gkr_layer__L0_L0» "evals[8]")) = τ (.n (val% «gkr_layer__L0_L0» "x@17")) from cp 8 (by omega), show τ (.n (val% «gkr_layer__L0_L0» "evals[9]")) = τ (.n (val% «gkr_layer__L0_L0» "x@18")) from cp 9 (by omega),
      show τ (.n (val% «gkr_layer__L0_L0» "evals[10]")) = τ (.n (val% «gkr_layer__L0_L0» "x@19")) from cp 10 (by omega),
      show τ (.n (val% «gkr_layer__L0_L0» "evals[11]")) = τ (.n (val% «gkr_layer__L0_L0» "x@20")) from cp 11 (by omega)]
    simp only [chB, polyEval, prodE, List.foldr, List.foldl]
    norm_num
    ring
  refine holdsList_straightN _ (straight_of_atoms glCheck_atoms) (fun s hs ↦ ?_) trivial
  simp only [glCheck, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals first
    | assumption
    | (show τ (.n (val% «gkr_layer__L0_L0» "nclaim@2")) + τ (.n (val% «gkr_layer__L0_L0» "combined@3")) = 0; rw [e248, e_add_self])

theorem glY_atoms : ∀ s ∈ glY, ∃ a, s = .atom a := by
  intro s hs; simp only [glY, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h | h | h <;> exact ⟨_, h⟩

/-- **The two new coordinates**: squeezed after the last four children over `cap`, stored at
`pt[40]`, `pt[41]`; the capacity after them at `271 ..`. -/
theorem glct_y (hG : ∀ s ∈ glY, (∀ d p off, s ≠ .atom (.load d p off)) → GoodS rd [] w τ s)
    (hp : ∀ i < 4, FsPackOk τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") (8 + i))) (chB (val% «gkr_layer__L0_L0» "x@9") (8 + i) + 1) dsObserve)
    {cap : List E} (hB : (lyCap (val% «gkr_layer__L0_L0» "nxt[0]@5")).map τ = cap)
    (z23 : τ (.n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]")) = 0) (z24 : τ (.n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[2]")) = 0) (z25 : τ (.n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[3]")) = 0) (z26 : τ (.n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[4]")) = 0)
    (h40 : LoadHolds rd (τ (.n (val% «gkr_layer__L0_L0» "point_row"))) 40
      (challengeOf (Fs.perm ⟨cap, (chWords τ (val% «gkr_layer__L0_L0» "x@9") 2).map (·, dsObserve)⟩)))
    (h41 : LoadHolds rd (τ (.n (val% «gkr_layer__L0_L0» "point_row"))) 41 (challengeOf (permOf (rateOf [] ++
      capOf (Fs.perm ⟨cap, (chWords τ (val% «gkr_layer__L0_L0» "x@9") 2).map (·, dsObserve)⟩))))) :
    Stmt.HoldsList C rd τ glY True kret ∧
      τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@6")) = challengeOf (Fs.perm ⟨cap, (chWords τ (val% «gkr_layer__L0_L0» "x@9") 2).map (·, dsObserve)⟩) ∧
      τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@7")) = challengeOf (permOf (rateOf [] ++
        capOf (Fs.perm ⟨cap, (chWords τ (val% «gkr_layer__L0_L0» "x@9") 2).map (·, dsObserve)⟩))) ∧
      ((List.range 5).map fun k ↦ τ (.n ((val% «gkr_layer__L0_L0» "nxt[8]@7") + k))) = capOf (permOf (rateOf [] ++
        capOf (Fs.perm ⟨cap, (chWords τ (val% «gkr_layer__L0_L0» "x@9") 2).map (·, dsObserve)⟩))) := by
  have g : ∀ a, Stmt.atom a ∈ glY → (∀ d p off, a ≠ .load d p off) → Good rd [] w τ a :=
    fun a ha hn ↦ hG _ ha (fun d p off h ↦ hn d p off (by injection h))
  obtain ⟨k1, -⟩ := keccak_good (rd := rd) (S := []) (w := w) (g (.keccak (chRate (val% «gkr_layer__L0_L0» "x@9") 2 ++ lyCap (val% «gkr_layer__L0_L0» "nxt[0]@5"))
    (lyOuts (val% «gkr_layer__L0_L0» "nxt[0]@6")) false false) (by simp [glY]) (by intros; simp))
  obtain ⟨P1, hc249⟩ := ch_perm_block (b0 := (val% «gkr_layer__L0_L0» "x@9")) (m := 2) (b := val% «gkr_layer__L0_L0» "nxt[0]@6")
    (fun i hi ↦ by simpa using hp i hi) k1
  rw [hB] at P1 hc249
  have e262 : τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@6")) = challengeOf (Fs.perm ⟨cap, (chWords τ (val% «gkr_layer__L0_L0» "x@9") 2).map (·, dsObserve)⟩) := by
    exact challengeT_value (σ := τ) (s0 := .n (val% «gkr_layer__L0_L0» "nxt[0]@6")) (b := val% «gkr_layer__L0_L0» "nxt[0]@6") rfl (P1 0 (by omega))
  obtain ⟨k2, -⟩ := keccak_good (rd := rd) (S := []) (w := w) (g (.keccak ([.n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"),
    .n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[2]"), .n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[3]"), .n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[4]")] ++ lyCap (val% «gkr_layer__L0_L0» "nxt[0]@6")) (lyOuts (val% «gkr_layer__L0_L0» "nxt[0]@7")) false false) (by simp [glY])
    (by intros; simp))
  obtain ⟨P2, Q2⟩ := ly_keccak k2
  rw [ly_zero_rate z23 z24 z25 z26] at P2 Q2
  rw [hc249] at P2 Q2
  have e276 : τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@7")) = challengeOf (permOf (rateOf [] ++
      capOf (Fs.perm ⟨cap, (chWords τ (val% «gkr_layer__L0_L0» "x@9") 2).map (·, dsObserve)⟩))) := by
    exact challengeT_value (σ := τ) (s0 := .n (val% «gkr_layer__L0_L0» "nxt[0]@7")) (b := val% «gkr_layer__L0_L0» "nxt[0]@7") rfl (P2 0 (by omega))
  refine ⟨?_, e262, e276, ?_⟩
  · refine holdsList_straightN _ (straight_of_atoms glY_atoms) (fun s hs ↦ ?_) trivial
    simp only [glY, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact k1
    · exact k2
    · show LoadHolds rd (τ (.n (val% «gkr_layer__L0_L0» "point_row"))) 40 (τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@6"))); rw [e262]; exact h40
    · show LoadHolds rd (τ (.n (val% «gkr_layer__L0_L0» "point_row"))) 41 (τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@7"))); rw [e276]; exact h41
  · rw [← Q2]
    simp [lyCap, List.range_succ]

/-- **A tree's new value** stored, on its equations. -/
theorem glct_val {c0 c1 slot t b off : ℕ}
    (hG : ∀ a, Stmt.atom a ∈ chValT (val% «gkr_layer__L0_L0» "x@9") c0 c1 slot t b off → (∀ d p o', a ≠ .load d p o') →
      Good rd [] w τ a)
    (hc0 : c0 < b) (hc1 : c1 < b) (he : ∀ i < 4, chB (val% «gkr_layer__L0_L0» "x@9") (4 * t + i) + 3 < b)
    (cp : ∀ i < 4, τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * t + i) + 3)) = τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * t + i))))
    (hs : LoadHolds rd (τ (.n slot)) off (multilinearEval (chWords τ (val% «gkr_layer__L0_L0» "x@9") t) [τ (.n c0), τ (.n c1)])) :
    Stmt.HoldsList C rd τ (chValT (val% «gkr_layer__L0_L0» "x@9") c0 c1 slot t b off) True kret := by
  have g : ∀ a, Stmt.atom a ∈ chValT (val% «gkr_layer__L0_L0» "x@9") c0 c1 slot t b off → (∀ d p o', a ≠ .load d p o') →
      Good rd [] w τ a := hG
  have e0 := he 0 (by omega)
  have e1 := he 1 (by omega)
  have e2 := he 2 (by omega)
  have e3 := he 3 (by omega)
  have a0 : τ (.n b) = τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * t + 0) + 3)) + τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * t + 1) + 3)) :=
    g (.add (.n b) (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * t + 0) + 3)) (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * t + 1) + 3))) (by simp [chValT]) (by intros; simp)
  have m1 := good_mul (g (.mul (.n (b + 1)) (.n c0) (.n b)) (by simp [chValT]) (by intros; simp))
    (by omega) (by omega)
  have a2 : τ (.n (b + 2)) = τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * t + 0) + 3)) + τ (.n (b + 1)) :=
    g (.add (.n (b + 2)) (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * t + 0) + 3)) (.n (b + 1))) (by simp [chValT]) (by intros; simp)
  have a3 : τ (.n (b + 3)) = τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * t + 2) + 3)) + τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * t + 3) + 3)) :=
    g (.add (.n (b + 3)) (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * t + 2) + 3)) (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * t + 3) + 3))) (by simp [chValT]) (by intros; simp)
  have m4 := good_mul (g (.mul (.n (b + 4)) (.n c0) (.n (b + 3))) (by simp [chValT]) (by intros; simp))
    (by omega) (by omega)
  have a5 : τ (.n (b + 5)) = τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * t + 2) + 3)) + τ (.n (b + 4)) :=
    g (.add (.n (b + 5)) (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * t + 2) + 3)) (.n (b + 4))) (by simp [chValT]) (by intros; simp)
  have a6 : τ (.n (b + 6)) = τ (.n (b + 2)) + τ (.n (b + 5)) :=
    g (.add (.n (b + 6)) (.n (b + 2)) (.n (b + 5))) (by simp [chValT]) (by intros; simp)
  have m7 := good_mul (g (.mul (.n (b + 7)) (.n c1) (.n (b + 6))) (by simp [chValT]) (by intros; simp))
    (by omega) (by omega)
  have a8 : τ (.n (b + 8)) = τ (.n (b + 2)) + τ (.n (b + 7)) :=
    g (.add (.n (b + 8)) (.n (b + 2)) (.n (b + 7))) (by simp [chValT]) (by intros; simp)
  have hv : τ (.n (b + 8)) = multilinearEval (chWords τ (val% «gkr_layer__L0_L0» "x@9") t) [τ (.n c0), τ (.n c1)] := by
    rw [a8, m7, a6, a5, m4, a3, a2, m1, a0, cp 0 (by omega), cp 1 (by omega), cp 2 (by omega),
      cp 3 (by omega), chWords_eq]
    simp only [multilinearEval, List.foldl, foldPairs, List.headD, Nat.add_zero]
    ring
  simp only [chValT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
  exact ⟨a0, m1, a2, a3, m4, a5, a6, m7, a8, by rw [hv]; exact hs⟩

/-- **The next slot**: the capacity, the cursor `cw` words on, the three values and the position
stored `20` words on. -/
theorem glct_next {cw : ℕ} (hcw : cw < 64)
    (hG : ∀ a, Stmt.atom a ∈ glNext cw → (∀ d p off, a ≠ .load d p off) → Good rd [] w τ a)
    (cp : ∀ i < 12, τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") i + 3)) = τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") i)))
    (s20 : ∀ k < 5, LoadHolds rd (τ (.n (val% «gkr_layer__L0_L0» "layer"))) (20 + k) (τ (.n ((val% «gkr_layer__L0_L0» "nxt[8]@7") + k))))
    (s25 : LoadHolds rd (τ (.n (val% «gkr_layer__L0_L0» "layer"))) 25 (τ (.n (val% «gkr_layer__L0_L0» "tcur")) * gen ^ cw))
    (sv : ∀ t < 3, LoadHolds rd (τ (.n (val% «gkr_layer__L0_L0» "layer"))) (26 + t)
      (multilinearEval (chWords τ (val% «gkr_layer__L0_L0» "x@9") t) [τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@6")), τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@7"))]))
    (s29 : LoadHolds rd (τ (.n (val% «gkr_layer__L0_L0» "layer"))) 29 (τ (.n (val% «gkr_layer__L0_L0» "round_pos")) * (τ (.n (val% «gkr_layer__L0_L0» "x_m")) * gen) ^ 7)) :
    Stmt.HoldsList C rd τ (glNext cw) True kret := by
  have g := hG
  have c277 : τ (.n (val% «gkr_layer__L0_L0» "s42#0")) = word (2 ^ cw) 0 :=
    g (.const (.n (val% «gkr_layer__L0_L0» "s42#0")) (word (2 ^ cw) 0)) (by simp [glNext]) (by intros; simp)
  have m278 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "s42#1")) (.n (val% «gkr_layer__L0_L0» "tcur")) (.n (val% «gkr_layer__L0_L0» "s42#0"))) (by simp [glNext]) (by intros; simp))
    (by omega) (by omega)
  have c305 : τ (.n (val% «gkr_layer__L0_L0» "s44#0")) = word 2 0 :=
    g (.const (.n (val% «gkr_layer__L0_L0» "s44#0")) (word 2 0)) (by simp [glNext]) (by intros; simp)
  have m306 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "s44#1")) (.n (val% «gkr_layer__L0_L0» "x_m")) (.n (val% «gkr_layer__L0_L0» "s44#0"))) (by simp [glNext]) (by intros; simp))
    (by omega) (by omega)
  have m307 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "s44#2")) (.n (val% «gkr_layer__L0_L0» "s44#1")) (.n (val% «gkr_layer__L0_L0» "s44#1"))) (by simp [glNext]) (by intros; simp))
    (by omega) (by omega)
  have m308 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "s44#3")) (.n (val% «gkr_layer__L0_L0» "s44#2")) (.n (val% «gkr_layer__L0_L0» "s44#1"))) (by simp [glNext]) (by intros; simp))
    (by omega) (by omega)
  have m309 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "s44#4")) (.n (val% «gkr_layer__L0_L0» "s44#3")) (.n (val% «gkr_layer__L0_L0» "s44#3"))) (by simp [glNext]) (by intros; simp))
    (by omega) (by omega)
  have m310 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "s44#5")) (.n (val% «gkr_layer__L0_L0» "s44#4")) (.n (val% «gkr_layer__L0_L0» "s44#1"))) (by simp [glNext]) (by intros; simp))
    (by omega) (by omega)
  have m311 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "s44#6")) (.n (val% «gkr_layer__L0_L0» "round_pos")) (.n (val% «gkr_layer__L0_L0» "s44#5"))) (by simp [glNext]) (by intros; simp))
    (by omega) (by omega)
  have V : ∀ t < 3, Stmt.HoldsList C rd τ (chValT (val% «gkr_layer__L0_L0» "x@9") (val% «gkr_layer__L0_L0» "nxt[0]@6") (val% «gkr_layer__L0_L0» "nxt[0]@7") (val% «gkr_layer__L0_L0» "layer") t (278 + 9 * t) (26 + t)) True kret := by
    intro t ht
    refine glct_val (fun a ha hn ↦ g a (by
        unfold glNext; simp only [List.mem_append]
        interval_cases t
        · exact .inl (.inl (.inl (.inr ha)))
        · exact .inl (.inl (.inr ha))
        · exact .inl (.inr ha)) hn)
      (by omega) (by omega) (fun i hi ↦ by simp only [chB]; omega)
      (fun i hi ↦ cp _ (by omega)) (sv t ht)
  unfold glNext
  rw [tb_holdsList_append_noRet (by rfl), tb_holdsList_append_noRet (by rfl),
    tb_holdsList_append_noRet (by rfl), tb_holdsList_append_noRet (by rfl),
    tb_holdsList_append_noRet (by rfl)]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, V 0 (by omega)⟩, V 1 (by omega)⟩, V 2 (by omega)⟩, ?_⟩
  · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨s20 0 (by omega), s20 1 (by omega), s20 2 (by omega), s20 3 (by omega), s20 4 (by omega)⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    refine ⟨c277, m278, ?_⟩
    rw [m278, c277, word_two_pow hcw]; exact s25
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    refine ⟨c305, m306, m307, m308, m309, m310, m311, ?_⟩
    rw [show τ (.n (val% «gkr_layer__L0_L0» "s44#6")) = τ (.n (val% «gkr_layer__L0_L0» "round_pos")) * (τ (.n (val% «gkr_layer__L0_L0» "x_m")) * gen) ^ 7 by
      rw [m311, m310, m309, m308, m307, m306, c305, word_gen]; ring]
    exact s29

end
end LeanVM.Guest.B1.Tables
