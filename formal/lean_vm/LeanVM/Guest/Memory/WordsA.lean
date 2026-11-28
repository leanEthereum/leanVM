/-
  LeanVM.Guest.Memory.WordsA

  The aligned allocator's words (`Tree.wordsA`) are the bus era's (`Tree.total`) plus at most `15`
  per instance allocated aligned, and so at most the static checker's cost at the frame weights
  `fsPad`, each aligned frame's padding added to its frame.
-/

module

public import LeanVM.Guest.Memory.AllocA
public import LeanVM.Guest.Memory.StaticSound

/-!
# The aligned words, counted

`Memory/AllocA.lean` places a fresh callee at `allocBase (al k) c`, at most `15` words after the
cursor when `al k` and at it otherwise (`allocBase_le_pad`); a loop helper's tail call reuses its
caller's block. So a subtree's end is at most its cursor plus its words, less its block, plus
`15` for each instance below it whose function is allocated aligned (`Tree.padIn`):
`endA_add_block_le`, and `wordsA_le_total : t.wordsA ≤ t.total fs + t.padIn al`.

Counting words at `fsPad fs al` (`fs f`, plus `15` if `al f`), each instance and each phantom costs
its frame and its padding, a phantom's frame at least its tail's (`htl`): `total_padIn_le_cost`,
and `wordsA_le_cost : t.wordsA ≤ t.cost P true (fsPad fs al)`. A certificate the static checker
accepts at `fsPad fs al` therefore bounds the aligned words.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core
open LeanVM.Prover.Exec (allocBase keccakWindow)

@[expose] public section

/-- A region's padding: `15` words if aligned. -/
def padOf (a : Bool) : ℕ := if a then 15 else 0

theorem allocBase_le_pad (a : Bool) (n : ℕ) : allocBase a n ≤ n + padOf a := by
  unfold allocBase keccakWindow padOf
  split <;> omega

/-- **The frame weights with their padding**: `fs f`, plus `15` for a frame allocated aligned. -/
def fsPad (fs : String → ℕ) (al : String → Bool) (f : String) : ℕ := fs f + padOf (al f)

section

variable (al : String → Bool)

mutual
/-- **The padding below a subtree**: `15` for each instance and phantom under its root whose
function is allocated aligned. -/
def Tree.padIn : Tree → ℕ
  | .node _ _ _ kids => Tree.padKids kids
  | .phantom .. => 0

/-- The padding of a list of subtrees, their roots included. -/
def Tree.padKids : List Tree → ℕ
  | [] => 0
  | k :: ks => padOf (al k.name) + k.padIn + Tree.padKids ks
end

end

variable {fs : String → ℕ} {lp al : String → Bool}

mutual
/-- **A subtree's end**: from `c`, at most its words less its block, plus its padding. -/
theorem endA_add_block_le : ∀ (t : Tree) (c : ℕ),
    t.endA fs lp al c + t.block fs lp ≤ c + t.total fs + t.padIn al
  | .node f σ bufs kids, c => by
      rw [endA_node, Tree.block, Tree.total, Tree.padIn]
      by_cases hl : lp f = true
      · simp only [hl, ↓reduceIte]
        have := endL_add_blockLast_le kids (c + bufs.sum)
        omega
      · simp only [hl, Bool.false_eq_true, ↓reduceIte]
        have := endF_le kids (c + bufs.sum)
        omega
  | .phantom f σ, c => by
      rw [endA_phantom, Tree.block, Tree.total, Tree.padIn]
      omega

/-- Callees entered fresh. -/
theorem endF_le : ∀ (ks : List Tree) (c : ℕ),
    Tree.endF fs lp al c ks ≤ c + Tree.totalKids fs ks + Tree.padKids al ks
  | [], c => by rw [endF_nil, Tree.totalKids, Tree.padKids]; omega
  | k :: ks, c => by
      rw [endF_cons, Tree.totalKids, Tree.padKids]
      have h1 := endF_le ks (k.endA fs lp al (allocBase (al k.name) c + k.block fs lp))
      have h2 := endA_add_block_le k (allocBase (al k.name) c + k.block fs lp)
      have h3 := allocBase_le_pad (al k.name) c
      omega

/-- A loop iteration's callees, the last its tail call in its caller's block. -/
theorem endL_add_blockLast_le : ∀ (ks : List Tree) (c : ℕ),
    Tree.endL fs lp al c ks + Tree.blockLast fs lp ks ≤ c + Tree.totalKids fs ks + Tree.padKids al ks
  | [], c => by rw [endL_nil, Tree.blockLast, Tree.totalKids, Tree.padKids]
  | [k], c => by
      rw [endL_one, Tree.blockLast, Tree.totalKids, Tree.totalKids, Tree.padKids, Tree.padKids]
      have := endA_add_block_le k c
      omega
  | k :: k' :: ks, c => by
      rw [endL_cons, Tree.blockLast, Tree.totalKids, Tree.padKids]
      have h1 := endL_add_blockLast_le (k' :: ks)
        (k.endA fs lp al (allocBase (al k.name) c + k.block fs lp))
      have h2 := endA_add_block_le k (allocBase (al k.name) c + k.block fs lp)
      have h3 := allocBase_le_pad (al k.name) c
      omega
end

/-- **The aligned words**: the bus era's words plus the padding. -/
theorem wordsA_le_total (t : Tree) : t.wordsA fs lp al ≤ t.total fs + t.padIn al := by
  have := endA_add_block_le (fs := fs) (lp := lp) (al := al) t (t.block fs lp)
  unfold Tree.wordsA
  omega

section Cost

variable {P : Core.Program}

mutual
/-- **The words and padding within the cost at the padded frame weights.** -/
theorem total_padIn_le_cost (htl : ∀ f, fs (tailKey f) ≤ fs f) :
    ∀ t : Tree, t.BufsOk P → t.total fs + padOf (al t.name) + t.padIn al ≤ t.cost P true (fsPad fs al)
  | t@(.node f σ bufs kids), hb => by
      simp only [Tree.BufsOk] at hb
      obtain ⟨hbufs, hbk⟩ := hb
      have := totalKids_padKids_le_costKids htl kids hbk
      rw [Tree.total, Tree.cost, Tree.padIn, ← hbufs, Tree.name]
      simp only [↓reduceIte, fsPad]
      omega
  | .phantom f _, _ => by
      rw [Tree.total, Tree.cost, Tree.padIn, Tree.name]
      simp only [↓reduceIte, fsPad]
      have := htl f
      omega

theorem totalKids_padKids_le_costKids (htl : ∀ f, fs (tailKey f) ≤ fs f) :
    ∀ ks : List Tree, Tree.BufsOkKids P ks →
      Tree.totalKids fs ks + Tree.padKids al ks ≤ Tree.costKids P true (fsPad fs al) ks
  | [], _ => by rw [Tree.totalKids, Tree.padKids, Tree.costKids]
  | k :: ks, hb => by
      simp only [Tree.BufsOkKids] at hb
      have h1 := total_padIn_le_cost htl k hb.1
      have h2 := totalKids_padKids_le_costKids htl ks hb.2
      rw [Tree.totalKids, Tree.padKids, Tree.costKids]
      omega
end

/-- **The aligned words within the cost at the padded frame weights.** -/
theorem wordsA_le_cost (htl : ∀ f, fs (tailKey f) ≤ fs f) {t : Tree} (hb : t.BufsOk P) :
    t.wordsA fs lp al ≤ t.cost P true (fsPad fs al) := by
  have h1 := wordsA_le_total (fs := fs) (lp := lp) (al := al) t
  have h2 := total_padIn_le_cost (al := al) htl t hb
  omega

end Cost

end
end LeanVM.Guest.Memory
