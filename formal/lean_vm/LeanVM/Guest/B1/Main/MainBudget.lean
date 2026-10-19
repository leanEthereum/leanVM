/-
  LeanVM.Guest.B1.Main.MainBudget

  End's `MainComplete` from `main_complete`: the layout at `0`, its consistency, its size within
  `mainBound`, and the budget's clauses on that bound.
-/

module

public import LeanVM.Guest.EndComplete

/-!
# `main` within the budget

`mainComplete_of`: s's `MainComplete fs cert cnt b` (EndComplete.lean) from `main_complete` at
`fp = 0` and `κ = 16`, its layout consistent by disjointness (`lConsistent_of_pairwise`), given the
callees' completeness within the bounds `Bd` (`CalleesAt`), each child's run and fresh shape
(from `verifyDeferred`'s inversion and the caps), and the budget's two clauses: `mainBound` of the
honest words within the budget's words (`hwords`), and the counts of every valid tree of that size
on the image. The words are within `2^32` since the budget's size is within `2^28`
(`words_le_of_size`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.End (MainComplete Limits CapsAgree Budget work hdrOf bytecode bytecode_length words_le_of_size)
open LeanVM.Guest.B1 (LowDef DisjL Within)

@[expose] public section

/-- **`main` is complete within the budget** (group 7's piece of `CompleteParts`), given its
callees' completeness, every child's run and the budget's clauses. -/
theorem mainComplete_of (fs : String → ℕ) (cert : String → V → ℕ) (cnt : Tree → Opcode → ℕ)
    (b : Budget) {VsGood : VerifySub.VsData → Prop} {Bd : CalleeBounds} (H : CalleesAt fs cert 16 VsGood Bd)
    (hfs : 2 ≤ fs "main")
    (hacc : ∀ seed s w, NodeRel bytecode seed s w → Limits s w → CapsAgree seed w →
      ∀ c ∈ w.children, FreshShaped c.fresh ∧ ∃ D : VerifySub.VsData, VsGood D ∧
        D.pi = statementDigest seed c.statement ∧ D.seed = seed ∧ D.fresh = c.fresh)
    (hwords : ∀ seed s w, NodeRel bytecode seed s w → Limits s w → CapsAgree seed w →
      mainBound fs Bd (honestWords seed s w) ≤ b.words.eval (work s w))
    (hcnt : ∀ seed s w, NodeRel bytecode seed s w → Limits s w → CapsAgree seed w →
      ∀ (N : ℕ) (L : Layout) (t : Tree), N ≤ b.words.eval (work s w) → t.name = "main" →
        t.total fs = N →
        t.Valid coreProgram (imageOf (logMem N) L (hdrOf (statementDigest seed s))).read [] [] →
          ∀ op, cnt t op ≤ (b.instrs op).eval (work s w)) :
    MainComplete fs cert cnt b := by
  intro seed s w hN hlim hcaps hbs
  have hc := hacc seed s w hN hlim hcaps
  obtain ⟨m, L, hW, hD, hmB, hrel⟩ := main_complete fs (cert := cert) H le_rfl bytecode_length hN hlim
    (fun c hc' => (hc c hc').1) (fun c hc' => (hc c hc').2) 0
  rw [Nat.zero_add] at hW
  have hbw := hwords seed s w hN hlim hcaps
  have hb32 : b.words.eval (work s w) ≤ 2 ^ 32 := le_trans (words_le_of_size hbs) (by norm_num)
  have hin : ∀ q ∈ L, 2 ≤ q.1 ∧ q.1 + q.2.length ≤ fs "main" + m := fun q hq => by
    have := hW q hq; omega
  exact ⟨fs "main" + m, L, lConsistent_of_pairwise hD, hin, le_trans (le_trans hmB hbw) hb32, le_trans hmB hbw,
    fun rd hl hL h0 h1 => hrel rd hl hL h0 h1,
    fun t hn ht hv op => hcnt seed s w hN hlim hcaps _ L t (le_trans hmB hbw) hn ht hv op⟩

end
end LeanVM.Guest.B1.Main
