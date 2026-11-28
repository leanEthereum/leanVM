/-
  LeanVM.Guest.B1.VerifySub.PhLinkRun

  The Statement's moves `verify_link` makes besides those its callees cover, as runs on the
  carried sponge: an option lifted, a requirement, the five fresh coefficients' packed draw, and
  the link's grinds' bit counts.
-/

module

public import LeanVM.Guest.B1.Link.Packed
public import LeanVM.Protocol.Link.Skeleton

/-!
# The link's other moves

* `lkRunsTo_liftOption`, `lkRunsTo_require`: `liftOption (some a)` and `require c` with `c` true read
  nothing and keep the sponge.
* `runsTo_samplePacked5`: a packed draw of five challenges on any carried sponge is the cells
  `0 .. 4` of its next permutation (`Fs.perm`), the capacity after it.
* `grindingBits_of`: `grindingBits N = k + 1 - 3` for `2^k < N ≤ 2^(k+1)`; the link's grind is
  `2` bits (`linkGrind_bits`), its index rounds' `0`, its row rounds' as `link_row_side`'s arms.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem lkRunsTo_liftOption {α : Type} (a : α) (s : Fs) : RunsTo (liftOption (some a)) s [] a s :=
  runsTo_ret a s

theorem lkRunsTo_require {c : Prop} [Decidable c] (h : c) (s : Fs) :
    RunsTo (VerifierProgram.require c) s [] () s := by
  unfold VerifierProgram.require
  simp only [h, ↓reduceIte]
  exact runsTo_ret () s

/-- **The fresh coefficients' draw**: five challenges, packed, from any carried sponge, are the
cells `0 .. 4` of its next permutation. -/
theorem runsTo_samplePacked5 (s : Fs) :
    RunsTo (VerifierProgram.sampleChallengesPacked 5) s []
      ((List.range 5).map (Link.cellAt s.perm)) ⟨capOf s.perm, []⟩ := by
  intro sp hs rest os roots
  have hp := perm_eq hs
  obtain ⟨st, pd, gr⟩ := sp
  have hg : gr = none := hs.2.2
  subst hg
  have e := Link.spc_step 4 4 ⟨st, pd, none⟩
  rw [hp, show 4 + 1 - min 8 (4 + 1) = 0 from rfl, Link.spc_zero, show min 8 (4 + 1) = 5 from rfl] at e
  have e1 : (List.range 5).map (Link.cellAt s.perm) =
      (squeezePackedChunks (m := Id) keccakF1600 5 ⟨st, pd, none⟩ 5).1 := by
    rw [e]
    simp only [List.append_nil]
    exact List.map_congr_left fun i hi ↦ (Link.packedChallengeOf_cell _ (by simp at hi; omega)).symm
  have e2 : (⟨s.perm, [], none⟩ : Sponge) =
      (squeezePackedChunks (m := Id) keccakF1600 5 ⟨st, pd, none⟩ 5).2 := by
    rw [e]
  refine ⟨⟨s.perm, [], none⟩, ⟨rfl, rfl, rfl⟩, ?_⟩
  rw [e1, e2]
  rfl

/-- `grindingBits` between powers of two. -/
theorem grindingBits_of {N k : ℕ} (h1 : 2 ^ k < N) (h2 : N ≤ 2 ^ (k + 1)) :
    grindingBits N = k + 1 - 3 := by
  unfold grindingBits
  have hN : ¬ N ≤ 1 := by have := Nat.one_le_two_pow (n := k); omega
  simp only [hN, ↓reduceIte]
  have h0 : N - 1 ≠ 0 := by omega
  have a1 := (Nat.le_log2 h0).mpr (show 2 ^ k ≤ N - 1 by omega)
  have a2 := (Nat.log2_lt h0).mpr (show N - 1 < 2 ^ (k + 1) by omega)
  have : Nat.log2 (N - 1) = k := by omega
  rw [this]
  rfl

/-- **The link's grind**: `2` bits at every shape the guest accepts. -/
theorem linkGrind_bits {n w : ℕ} (hn : n ≤ 24) (hw1 : 19 ≤ w) (hw2 : w ≤ 24) :
    grindingBits (max (n + 3 + bytecodeSlotBits) (w + 1)) = 2 := by
  have h1 : 2 ^ 4 < max (n + 3 + bytecodeSlotBits) (w + 1) := by
    simp only [bytecodeSlotBits, Nat.max_def]; split_ifs <;> omega
  have h2 : max (n + 3 + bytecodeSlotBits) (w + 1) ≤ 2 ^ (4 + 1) := by
    simp only [bytecodeSlotBits, Nat.max_def]; split_ifs <;> omega
  rw [grindingBits_of h1 h2]

theorem gb2 : grindingBits (1 + 1) = 0 := by
  rw [grindingBits_of (k := 0) (by norm_num) (by norm_num)]

theorem gb7 : grindingBits (6 + 1) = 0 := by
  rw [grindingBits_of (k := 2) (by norm_num) (by norm_num)]

theorem gb8 : grindingBits (7 + 1) = 0 := by
  rw [grindingBits_of (k := 2) (by norm_num) (by norm_num)]

theorem gb9 : grindingBits (8 + 1) = 1 := by
  rw [grindingBits_of (k := 3) (by norm_num) (by norm_num)]

theorem gb10 : grindingBits (9 + 1) = 1 := by
  rw [grindingBits_of (k := 3) (by norm_num) (by norm_num)]

theorem gb11 : grindingBits (10 + 1) = 1 := by
  rw [grindingBits_of (k := 3) (by norm_num) (by norm_num)]

/-- `packedChallenges` at the concrete tables. -/
theorem linkDrawn_tables {layout : Layout} (h : layout.tables = tables) (chunks : Chunks) :
    Link.linkDrawn layout chunks =
      88 + Link.linkRows layout + chunks.width + ((Chunks.new chunks.width).map Chunks.d).getD 0 := by
  have h1 : (tables.map (·.links.memory.length)).sum = 39 := by decide +kernel
  have h2 : (tables.map fun x ↦ x.links.pointers.length).sum = 33 := by decide +kernel
  simp only [Link.linkDrawn, packedChallenges, h, h1, h2, nTables, bytecodeSlotBits]

theorem linkQVars_tables {layout : Layout} (h : layout.tables = tables) : Link.linkQVars layout = 6 := by
  rw [Link.linkQVars, h]
  decide +kernel

end
end LeanVM.Guest.B1.VerifySub
