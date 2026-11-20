/-
  LeanVM.Guest.B1.Whir.RoundSound

  `opening_round`'s core IR is `roundBody`, and gives its meaning in every program that finds it.
-/

module

public import LeanVM.Guest.B1.Whir.Round
public import LeanVM.Guest.Pack.P0.Core
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«opening_round»

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
theorem opening_round_body : (Fn.«opening_round».core).body = roundBody :=
  stmtsEqb_sound (by decide +kernel)

theorem opening_round_params : (Fn.«opening_round».core).params = (List.range 10).map V.n := rfl

/-- **`opening_round`'s core IR gives its meaning**, in every program that finds it, on a memory
image of `2^κ` words, `11 ≤ κ ≤ 32`, whose `tabs` holds the bit windows. -/
theorem opening_round_soundP (P : Program) [Finds P "opening_round" Fn.«opening_round».core]
    (hg : grind_check_SpecP P 7) {κ : ℕ} (hκ : κ ≤ 32) (hw : winTabBits ≤ κ)
    (L : MemoryImage κ) (args rets : List E) (ht : WinTabs L.read (args.getD 7 0))
    (h : P.Rel L.read "opening_round" args rets) : MeaningOpeningRound L.read args rets := by
  rw [rel_iff_sem (Finds.find (P := P) (name := "opening_round") (fn := Fn.«opening_round».core)),
    opening_round_body, opening_round_params] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [roundBody, holdsList_append, holds_fsNonceT, holds_fsNextT, holds_padRunT,
    Stmt.HoldsList, Stmt.Holds, holds_const, holds_add, holds_mul,
    holds_copy, holds_load, List.map_cons, List.map_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, osLd, osMul, osAdd, osCp, osCst, and_assoc,
    Nat.reduceAdd] at h
  obtain ⟨c10, c11, c12, c13, c14, lu0, pu0, lw, pw, lc0, pc0, lc1, pc1, k1, ln2, pn2,
    pad, k2, g2, k3, sg, sa, sb, e74, e75, e76, e77, e78, e79, e80, e81, e82, e83,
    c84, c85, c86, c87, c88, e89, e90, e91, e92, hret⟩ := h
  subst hp hret
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.getD_cons_succ, List.getD_cons_zero] at ht ⊢
  have hb : _root_.LeanVM.Parameters.Whir.foldGrindingBits ≠ 0 := by decide
  obtain ⟨pd, z1, z2, z3, z4⟩ := pad
  have p15 := fsPackT_cells pu0
  have p18 := fsPackT_cells pw
  have p21 := fsPackT_cells pc0
  have p24 := fsPackT_cells pc1
  have p40 := fsPackT_cells pn2
  simp only [Prod.ext_iff, Nat.reduceAdd] at p15 p18 p21 p24 p40 z1 z2 z3 z4
  set fs := [σ (V.n (val% «opening_round» "fs0")), σ (V.n (val% «opening_round» "fs1")), σ (V.n (val% «opening_round» "fs2")), σ (V.n (val% «opening_round» "fs3")), σ (V.n (val% «opening_round» "fs4"))] with hfs
  -- the four scalars
  have K1 := keccakA_fs (s := ⟨fs, [(σ (.n (val% «opening_round» "x@1")), dsObserve), (σ (.n (val% «opening_round» "x@2")), dsObserve),
      (σ (.n (val% «opening_round» "x@3")), dsObserve), (σ (.n (val% «opening_round» "x@4")), dsObserve)]⟩) k1 (by simp) (by
    simp [permIns, osRun, pendCells, p15.1, p15.2, p18.1, p18.2, p21.1, p21.2, p24.1, p24.2, c10,
      c11, c12, c13, c14, fs, List.range_succ])
  set S1 := (⟨fs, [(σ (.n (val% «opening_round» "x@1")), dsObserve), (σ (.n (val% «opening_round» "x@2")), dsObserve), (σ (.n (val% «opening_round» "x@3")), dsObserve),
    (σ (.n (val% «opening_round» "x@4")), dsObserve)]⟩ : Fs).perm with hS1
  have hs2 : rdS2 fs [σ (.n (val% «opening_round» "x@1")), σ (.n (val% «opening_round» "x@2")), σ (.n (val% «opening_round» "x@3")), σ (.n (val% «opening_round» "x@4"))] =
      ⟨fs, [(σ (.n (val% «opening_round» "x@1")), dsObserve), (σ (.n (val% «opening_round» "x@2")), dsObserve), (σ (.n (val% «opening_round» "x@3")), dsObserve),
        (σ (.n (val% «opening_round» "x@4")), dsObserve)]⟩ := by
    rw [rdS2, absorbAll_four]
  have cap1 : capOf S1 = [σ (.n (val% «opening_round» "nxt[8]@1")), σ (.n (val% «opening_round» "nxt[9]@1")), σ (.n (val% «opening_round» "nxt[10]@1")), σ (.n (val% «opening_round» "nxt[11]@1")), σ (.n (val% «opening_round» "nxt[12]@1"))] := by
    simp only [capOf, ← outCell K1 8, ← outCell K1 9, ← outCell K1 10, ← outCell K1 11,
      ← outCell K1 12]
    rfl
  -- the grind
  have K2 := keccakA_fs (s := ⟨capOf S1, [(σ (.n (val% «opening_round» "s6.i0:fs_grind_squeeze.s0.e.s0.t.s2#0")), dsPowNonce)]⟩) k2
    (by simp) (by
    simp [permIns, osRun, pendCells, p40.1, p40.2, z1, z2, z3, z4, cap1, List.range_succ])
  have hn2 : (rdS2 fs [σ (.n (val% «opening_round» "x@1")), σ (.n (val% «opening_round» "x@2")), σ (.n (val% «opening_round» "x@3")), σ (.n (val% «opening_round» "x@4"))]).nonceState
      (σ (.n (val% «opening_round» "s6.i0:fs_grind_squeeze.s0.e.s0.t.s2#0"))) = (⟨capOf S1, [(σ (.n (val% «opening_round» "s6.i0:fs_grind_squeeze.s0.e.s0.t.s2#0")), dsPowNonce)]⟩ : Fs).perm := by
    rw [hs2]; simp [Fs.nonceState, Fs.absorb, rateScalars, hS1]
  rw [← hn2] at K2
  have G2 := ((hg hκ hw L _ _ ht) []).mp (grindCheckName_seven ▸ g2)
  obtain ⟨gok2, hα, hs3⟩ := grindSqueeze_cells hb (σ (.n (val% «opening_round» "s6.i0:fs_grind_squeeze.s0.e.s0.t.s2#0"))) _ _ (outCell K2 0) (outCell K2 1) G2.2
  set S3 := (rdS2 fs [σ (.n (val% «opening_round» "x@1")), σ (.n (val% «opening_round» "x@2")), σ (.n (val% «opening_round» "x@3")), σ (.n (val% «opening_round» "x@4"))]).nonceState
    (σ (.n (val% «opening_round» "s6.i0:fs_grind_squeeze.s0.e.s0.t.s2#0"))) with hS3
  have cap3 : capOf S3 = [σ (.n (val% «opening_round» "nxt[8]@2")), σ (.n (val% «opening_round» "nxt[9]@2")), σ (.n (val% «opening_round» "nxt[10]@2")), σ (.n (val% «opening_round» "nxt[11]@2")), σ (.n (val% «opening_round» "nxt[12]@2"))] := by
    simp only [capOf, ← outCell K2 8, ← outCell K2 9, ← outCell K2 10, ← outCell K2 11,
      ← outCell K2 12]
    rfl
  -- β
  have K3 := keccakA_fs (s := ⟨capOf S3, []⟩) k3 (by simp) (by
    simp [permIns, osRun, pendCells, z1, z2, z3, z4, cap3, List.range_succ])
  set S4 := (⟨capOf S3, []⟩ : Fs).perm with hS4
  have hβ : σ (.n (val% «opening_round» "nxt[0]@3")) = challengeOf S4 := challengeT_value (s0 := .n (val% «opening_round» "nxt[0]@3")) (b := 61) rfl (outCell K3 0)
  have hG2 : rdG2 fs [σ (.n (val% «opening_round» "x@1")), σ (.n (val% «opening_round» "x@2")), σ (.n (val% «opening_round» "x@3")), σ (.n (val% «opening_round» "x@4"))] (σ (.n (val% «opening_round» "s6.i0:fs_grind_squeeze.s0.e.s0.t.s2#0"))) =
      (σ (.n (val% «opening_round» "nxt[0]@2")), ⟨capOf S3, []⟩) := by
    rw [rdG2, Prod.ext_iff]; exact ⟨hα, hs3⟩
  refine ⟨σ (.n (val% «opening_round» "x@1")), σ (.n (val% «opening_round» "x@2")), σ (.n (val% «opening_round» "x@3")), σ (.n (val% «opening_round» "x@4")), σ (.n (val% «opening_round» "s6.i0:fs_grind_squeeze.s0.e.s0.t.s2#0")), ?_, ?_⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact lu0
    · exact lw
    · exact lc0
    · exact lc1
    · exact ln2
  · simp only [← hfs]
    simp only [hG2, Fs.squeeze, ← hS4]
    refine ⟨gok2, ?_, ?_, ?_, ?_⟩
    · exact sg
    · exact sa
    · rw [← hβ]; exact sb
    · rw [e91, e90, e89, show (32 : ℕ) = 2 ^ 5 by rfl, word_two_pow (by decide), c84, c85,
        c86, c87, c88, e92, e83, e82, e81, e80, e79, e78, e77, e76, e75, e74, ← hβ]
      simp only [capOf, ← outCell K3 8, ← outCell K3 9, ← outCell K3 10, ← outCell K3 11,
        ← outCell K3 12, roundClaim]
      rfl

end
end LeanVM.Guest.B1.Whir
