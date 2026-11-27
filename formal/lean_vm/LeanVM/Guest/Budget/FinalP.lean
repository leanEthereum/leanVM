/-
  LeanVM.Guest.Budget.FinalP

  `MainComplete` with the tree's pops: `main`'s tree within the budget also pops the honest pushes, stream by stream.
-/

module

public import LeanVM.Guest.Budget.Final
public import LeanVM.Guest.B1.Main.MainHonestBudgetBR
public import LeanVM.Guest.B1.Main.MainPushes

/-!
# `main` within the budget, with its pops

`MainCompleteP`: `MainComplete`, the tree popping `Hints.honestPushes`, stream by stream (`SameStreams`); `MainCompleteP.toMain` forgets the pops. `MainSegs`: `main`'s callees' entries against their segments of the honest pushes (`main_pops_honest`'s hypotheses).
-/

namespace LeanVM.Guest.Budget

open LeanVM.Guest.Completeness
open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.End (MainComplete Budget work hdrOf bytecode)
open LeanVM.Guest.B1 (LowDef)
open LeanVM.Guest.B1.Main (hm MainPops childSeg daSeg LConsistent Layout MemL)

@[expose] public section

/-- **`MainComplete` with the pops**: the tree also pops `Hints.honestPushes`, stream by stream. -/
def MainCompleteP (fs : String → ℕ) (cert : String → V → ℕ) (cnt : Tree → Opcode → ℕ) (b : Budget) : Prop :=
  ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w →
    b.size (work s w) ≤ 2 ^ 30 →
    ∃ (N : ℕ) (L : Layout), LConsistent L ∧ (∀ q ∈ L, 2 ≤ q.1 ∧ q.1 + q.2.length ≤ N) ∧
      N ≤ 2 ^ 30 ∧ N ≤ b.words.eval (work s w) ∧
      ∀ rd, LowDef (logMem N) rd → MemL rd L → rd 1 = some (hdrOf (statementDigest seed s)).1 →
        rd g = some (hdrOf (statementDigest seed s)).2 →
          ∃ t : Tree, t.name = "main" ∧ t.Valid coreProgram rd [] [] ∧ t.BufsOk coreProgram ∧
            t.Placed coreProgram fs cert (0, t.block fs coreProgram.loop) ∧ t.total fs = N ∧
            t.LoadsIn coreProgram fs cert (fun i => i < 2) (0, t.block fs coreProgram.loop) ∧
            (∀ op, cnt t op ≤ (b.instrs op).eval (work s w)) ∧
            SameStreams (t.pops coreProgram rd)
              (Hints.honestPushes bytecode seed s w)

/-- **`main`'s callees' entries against their segments of the honest pushes** on the memory `rd`, a loop not
entered popping `[]`. -/
structure MainSegs (fs : String → ℕ) (seed : Digest) (s : NodeStatement) (w : NodeWitness) (q : MainPops)
    (rd : Reader) : Prop where
  cx : SameStreams (q.px rd) (Hints.listPushes "claims"
    (s.claims.xmss.map fun c ↦ Hints.claimCells (xmssRoot c) (xmssParam c) c.2))
  cs : SameStreams (q.ps rd) (Hints.listPushes "claims"
    (s.claims.sphincs.map fun c ↦ Hints.claimCells c.1.publicSeed c.1.root c.2))
  d0 : SameStreams (if (hm fs 0 seed s w).nxd = 0 then [] else q.p0 rd)
    ((B1.Main.xPlan s w).duplicates.map fun c ↦ ("dup_claims",
        Hints.claimCells (xmssRoot c) (xmssParam c) c.2))
  d1 : SameStreams (if (hm fs 0 seed s w).nsd = 0 then [] else q.p1 rd)
    ((B1.Main.sPlan s w).duplicates.map fun c ↦ ("dup_claims", Hints.claimCells c.1.publicSeed c.1.root c.2))
  r2 : SameStreams (if (hm fs 0 seed s w).nrx = 0 then [] else q.p2 rd)
    ((w.xmssSignatures.zip (B1.Main.xPlan s w).directSlots).flatMap
      (fun (c, slot) ↦ ("raw_index", [Hints.count slot]) :: Hints.xmssHints c.1.1 c.1.2 c.2))
  r3 : SameStreams (if (hm fs 0 seed s w).nrs = 0 then [] else q.p3 rd)
    ((w.sphincsSignatures.zip (B1.Main.sPlan s w).directSlots).flatMap
      (fun (c, slot) ↦ ("sp_raw_index", [Hints.count slot]) :: Hints.sphincsHints c.1.1 c.1.2 c.2))
  da : w.daMatrix.isSome → SameStreams (q.pd rd) (daSeg w)
  kids : SameStreams (if (hm fs 0 seed s w).nc = 0 then [] else q.p5 rd)
    (childSeg bytecode seed s w)
  agg : w.children ≠ [] → SameStreams (q.pa rd) (Hints.batchPushes w.batchingHints)

/-- `MainCompleteP` without the pops. -/
theorem MainCompleteP.toMain {fs : String → ℕ} {cert : String → V → ℕ} {cnt : Tree → Opcode → ℕ} {b : Budget}
    (h : MainCompleteP fs cert cnt b) : MainComplete fs cert cnt b := fun seed s w h1 h2 h3 h4 =>
  let ⟨N, L, a1, a2, a3, a4, hr⟩ := h seed s w h1 h2 h3 h4
  ⟨N, L, a1, a2, a3, a4, fun rd hl hL h0 h1 =>
    let ⟨t, b1, b2, b3, b4, b5, b6, b7, _⟩ := hr rd hl hL h0 h1
    ⟨t, b1, b2, b3, b4, b5, b6, b7⟩⟩

end
end LeanVM.Guest.Budget
