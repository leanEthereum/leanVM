/-
  LeanVM.Guest.Budget.End

  `MainComplete` from `main`'s completeness at `0` within a words bound before the memory, and its
  tree's instruction counts within the budget on every memory.
-/

module

public import LeanVM.Guest.EndComplete
public import LeanVM.Guest.B1.Main.KidsT
public import LeanVM.Guest.Budget.Static
public import LeanVM.Guest.AcceptableChild

/-!
# `main` within the budget

`mainComplete_of_bounds`: `End.MainComplete fs cert cnt b` from
* `main`'s placed completeness at `0` (B1-f's `main_honest_budgetB`): a size `n` within `Bm s w`,
  before the memory, a layout above `main`'s frame, disjoint, and on every memory holding it and
  the statement's digest at words `0`, `1` a tree of `main` satisfying `T`;
* the counts: every tree satisfying `T`, valid, within the budget's instructions;
* the words: `Bm s w` within the budget's words.
The layout is consistent by disjointness, at least `2` since `main`'s frame is.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Guest.Completeness

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.End (MainComplete Budget work hdrOf bytecode words_le_of_size)
open LeanVM.Guest.B1 (LowDef DisjL Within)
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

theorem loadHolds_one {rd : Reader} {x : E} (h : rd 1 = some x) : LoadHolds rd 1 0 x := by
  rw [one_eq_ofK]
  refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
  rw [B1.Main.addr_ofK]
  simpa [Parameters.addressOfIndex] using h

theorem loadHolds_gen {rd : Reader} {x : E} (h : rd g = some x) : LoadHolds rd gen 0 x := by
  have e : gen = ofK (addressOfIndex 1) := by rw [← Value.gen_pow_eq_ofK, pow_one]
  rw [e]
  refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
  rw [B1.Main.addr_ofK]
  simpa [Parameters.addressOfIndex] using h

/-- **`MainComplete` from `main`'s completeness within a words bound and its tree's counts.** -/
theorem mainComplete_of_bounds (fs : String → ℕ) (cert : String → V → ℕ)
    (cnt : Tree → Opcode → ℕ) (b : Budget)
    (T : Digest → NodeStatement → NodeWitness → Reader → Tree → Prop) (Bm : Digest → NodeStatement → NodeWitness → ℕ)
    (hfs : 2 ≤ fs "main")
    (hmain : ∀ seed s w, NodeRelation bytecode seed s w → DeployedLimits s w → ChildrenOk bytecode seed w →
      ∃ (n : ℕ) (L : B1.Main.Layout), n ≤ Bm seed s w ∧ Within L 0 n ∧ (∀ q ∈ L, fs "main" ≤ q.1) ∧
        DisjL L ∧ ∀ rd, LowDef 16 rd → B1.Main.MemL rd L →
          LoadHolds rd 1 0 (digestHalves (statementDigest seed s)).1 →
          LoadHolds rd gen 0 (digestHalves (statementDigest seed s)).2 →
          RelAtInT coreProgram fs cert rd (fun i => i < 2) (fun _ => False) 0 n "main" [] []
            (T seed s w rd))
    (hcnt : ∀ seed s w, NodeRelation bytecode seed s w → DeployedLimits s w →
      ∀ (rd : Reader) (t : Tree), T seed s w rd t → t.Valid coreProgram rd [] [] →
        t.BufsOk coreProgram → ∀ op, cnt t op ≤ (b.instrs op).eval (work s w))
    (hwords : ∀ seed s w, NodeRelation bytecode seed s w → DeployedLimits s w →
      Bm seed s w ≤ b.words.eval (work s w)) :
    MainComplete fs cert cnt b := by
  intro seed s w hrel hlim hok hbs
  obtain ⟨n, L, hnB, hW, hab, hD, hR⟩ := hmain seed s w hrel hlim hok
  have hw := hwords seed s w hrel hlim
  have h26 := words_le_of_size hbs
  refine ⟨n, L, B1.Main.lConsistent_of_pairwise hD, fun q hq => ?_, by omega, by omega,
    fun rd hl hL h0 h1 => ?_⟩
  · have := hW q hq
    have := hab q hq
    omega
  · obtain ⟨t, ⟨hn, hv, hb, hp, ht, hli, -⟩, hT⟩ :=
      hR rd hl hL (loadHolds_one h0) (loadHolds_gen h1)
    exact ⟨t, hn, hv, hb, hp, ht, hli, hcnt seed s w hrel hlim rd t hT hv hb⟩

end
end LeanVM.Guest.Budget
