/-
  LeanVM.Guest.Bridge.WitDefs

  The data check the witness hints' destinations read of each function: every frame value a
  witness hint writes, and every heap pointer it writes through, at its certificate cell; the
  atoms on the spine that pin a heap pointer as a word of the memory.
-/

module

public import LeanVM.Guest.Bridge.PairDefs
public import LeanVM.Guest.Bridge.ProgAlDefs

/-!
# The witness hints' cells

`witChk X n body`, for a function's alignment context `X` (its cell map, the certificate's but at
its hint-only cells, a trie the kernel reads in a few steps) and frame size `n`, checks every
witness hint atom of the body at any depth: each value of a stack destination, and the pointer of a
heap one, at its cell in `[2, n)` and no hint-only cell (`cellOkX`), a heap pointer possibly at a
hint-only cell instead.

`ptrOk sp p`: the spine `sp` pins the heap pointer `p`. In `K` by its allocation or a load through
it; a word of the memory by a load through it at offset `0`, or a heap hint writing through it from
offset `0`. A heap witness pointer the spine does not pin is left to the caller.

`WitJ j`: compiled function `j` passes the check over its alignment's context `ctxOf j`; `witJ_of` from
its pack's.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- A load's pointer. -/
def loadPtr : Atom → Option V
  | .load _ p _ => some p
  | _ => none

/-- A load's pointer, at offset `0`. -/
def loadPtr0 : Atom → Option V
  | .load _ p 0 => some p
  | _ => none

/-- A heap hint's pointer, writing from offset `0` at least one word. -/
def heapPtr0 (a : Atom) : Option V :=
  match atomHeapDest? a with
  | some (p, 0, _ + 1) => some p
  | _ => none

/-- **The spine pins a heap pointer**: in `K` by its allocation or a load through it, a word of
the memory by a load through it at offset `0` or a heap hint writing from offset `0`. -/
def ptrOk (sp : List Atom) (p : V) : Bool :=
  (sp.any (fun a ↦ allocOf a == some p) || sp.any (fun a ↦ loadPtr a == some p)) &&
    (sp.any (fun a ↦ loadPtr0 a == some p) || sp.any (fun a ↦ heapPtr0 a == some p))

/-- A frame value at its cell of the context's map, in `[2, n)`, no hint-only cell, its number below
`2^30`. -/
noncomputable def cellOkX (X : AlignCtx) (n : ℕ) (v : V) : Bool :=
  (X.extra.lookup v.idx).isNone && Nat.blt v.idx (2 ^ 30) && Nat.ble 2 (X.locAt v.idx) && Nat.blt (X.locAt v.idx) n

/-- **A witness hint atom's cells**: a stack destination's values, a heap one's pointer, at their
cells in the frame, the pointer possibly at a hint-only cell. -/
noncomputable def witAtomOk (X : AlignCtx) (n : ℕ) : Atom → Bool
  | .hint (.witness _ (.stack vs)) => vs.all (cellOkX X n)
  | .hint (.witness _ (.heap p _ _)) => cellOkX X n p || (X.extra.lookup p.idx).isSome
  | _ => true

/-- **The witness hints' check of a function**: its alignment's context (cell map and hint-only
cells), frame size and body, the context's tables evaluated first. -/
noncomputable def witChk (X : AlignCtx) (n : ℕ) (body : List Stmt) : Bool :=
  X.seq fun X ↦ blockAll (witAtomOk X n) body

/-- **Compiled function `j`'s witness hints pass the data check.** -/
def WitJ (j : ℕ) : Prop := witChk (ctxOf j) (B2C.fsN j) (coreOf j).body = true

end

public section

/-- **A function's witness check from its pack's**, by its code, core IR, certificate, plumbing,
tables and frame size. -/
theorem witJ_of {j : ℕ} {f : CompiledFunction} {cf : Core.Fn} {C : Check.Cert} {P : B2C.Plumb}
    {ex : List (ℕ × ℕ)} {en : List (String × ℕ)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} {main : Bool}
    {n : ℕ} (hf : fnOf j = f) (hcf : coreOf j = cf) (hC : certOf j = C.withPows Data.powTree) (hP : B2C.plumbOf j = P)
    (ht : (extraOf j, entsOf j, adviceOf j) = (ex, en, d)) (hm : (j == 1) = main) (hn : B2C.fsN j = n)
    (h : witChk (AlignCtx.ofData C.locs ex f.entryPc main P Data.powTree Data.jtTrie en alignHalt f.instructionCount)
      n cf.body = true) : WitJ j := by
  simp only [Prod.mk.injEq] at ht
  obtain ⟨hex, hen, -⟩ := ht
  have hl : (certOf j).locs = C.locs := by rw [hC]; cases C; rfl
  rw [WitJ, ctxOf, hl, hex, hen, hf, hcf, hP, hm, hn]
  exact h

end

end LeanVM.Guest.Bridge
