/-
  LeanVM.Guest.B1.Main.MainGoals

  What `main`'s placed completeness asks of its callees on an honest run: each callee
  `CompleteAtD` at the words `main` passes it, reading `main`'s honest words (`hLmain`).
-/

module

public import LeanVM.Guest.B1.Main.MainHonest

/-!
# `main`'s callees on an honest run

`hm`, `hLmain`: `main`'s honest oracle and words at `fp` (its buffers `hOwn`, then
`exponent_tables`' table). One statement per callee (`MainGoalClX` … `MainGoalSt`), each the
`CompleteAtD` `mKids` asks for; `completeAtD_lin_mono` moves a callee's completeness to a
larger caller layout.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (CompleteAtD Returns bufL)

@[expose] public section

/-- A callee's completeness reading fewer words holds reading more. -/
theorem completeAtD_lin_mono {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {f : String}
    {Lin Lin' : B1.Main.Layout} {args : List E} {Out : List E → B1.Main.Layout → Prop}
    (hm : ∀ rd, B1.Main.MemL rd Lin' → B1.Main.MemL rd Lin)
    (hr : ∀ i, B1.Main.RegionL Lin i → B1.Main.RegionL Lin' i)
    (h : CompleteAtD fs cert κ f Lin args Out) : CompleteAtD fs cert κ f Lin' args Out := by
  intro fp
  obtain ⟨n, Lown, rets, Lout, ho, hw, hd, hR⟩ := h fp
  refine ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hM => (hR rd hl ?_).mono hr⟩
  rw [B1.Main.memL_append] at hM ⊢
  exact ⟨hM.1, hm rd hM.2⟩

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement)
  (w : NodeWitness)

/-- `main`'s honest oracle at `fp`. -/
abbrev hm : MainIn := (hData seed s w).toIn fs fp

/-- **`main`'s honest words at `fp`**: its buffers, then `exponent_tables`' table. -/
abbrev hLmain : B1.Main.Layout :=
  bufL (fp + fs "main") (mSizes (hData seed s w)) (hOwn seed s w) ++ etL (hData seed s w) fs fp

/-! ## The callees -/

def MainGoalClX : Prop :=
  CompleteAtD fs cert 20 "claim_list_digest" (hLmain fs fp seed s w)
    [(hm fs fp seed s w).a77, gen ^ (hm fs fp seed s w).nlx] (Returns (B1.Digest.digestCells (hm fs fp seed s w).xd))

def MainGoalClS : Prop :=
  CompleteAtD fs cert 20 "claim_list_digest" (hLmain fs fp seed s w)
    [(hm fs fp seed s w).a80, gen ^ (hm fs fp seed s w).nls] (Returns (B1.Digest.digestCells (hm fs fp seed s w).sd))

def MainGoalL1 : Prop :=
  (hm fs fp seed s w).nxd ≠ 0 →
    CompleteAtD fs cert 20 "__loop0" (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nxd, (hm fs fp seed s w).a77, gen ^ (hm fs fp seed s w).nlx] (Returns [])

def MainGoalL2 : Prop :=
  (hm fs fp seed s w).nsd ≠ 0 →
    CompleteAtD fs cert 20 "__loop1" (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nsd, (hm fs fp seed s w).a80, gen ^ (hm fs fp seed s w).nls] (Returns [])

def MainGoalL3 : Prop :=
  (hm fs fp seed s w).nrx ≠ 0 →
    CompleteAtD fs cert 23 "__loop2" (hLmain fs fp seed s w)
      ([1, gen ^ (hm fs fp seed s w).nrx, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hm fs fp seed s w).a117, (hm fs fp seed s w).a77] ++ lxTagWords) (Returns [])

def MainGoalL4 : Prop :=
  (hm fs fp seed s w).nrs ≠ 0 →
    CompleteAtD fs cert 23 "__loop3" (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nrs, gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ (hm fs fp seed s w).nrx, (hm fs fp seed s w).a80, (hm fs fp seed s w).a119] (Returns [])

def MainGoalDv : Prop :=
  (hm fs fp seed s w).nd = 1 →
    CompleteAtD fs cert 20 "da_verify" (hLmain fs fp seed s w) [(hm fs fp seed s w).et]
      (Returns (hm fs fp seed s w).daR)

def MainGoalL5 : Prop :=
  (hm fs fp seed s w).nc ≠ 0 →
    CompleteAtD fs cert 23 "__loop4" (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a409, (hm fs fp seed s w).a77,
        (hm fs fp seed s w).a117, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hm fs fp seed s w).a80,
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a406, (hm fs fp seed s w).aDa,
        (digestHalves (hm fs fp seed s w).seed).1, (digestHalves (hm fs fp seed s w).seed).2,
        (hm fs fp seed s w).a394, (hm fs fp seed s w).et, (hm fs fp seed s w).a400] (Returns [])

def MainGoalAg : Prop :=
  (hm fs fp seed s w).nc ≠ 0 →
    CompleteAtD fs cert 20 "aggregate_claims" (hLmain fs fp seed s w)
      [gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a394, (hm fs fp seed s w).a400,
        (hm fs fp seed s w).a406, (hm fs fp seed s w).a417] (Returns [])

def MainGoalSt : Prop :=
  CompleteAtD fs cert 20 "statement_digest" (hLmain fs fp seed s w)
    [(digestHalves (hm fs fp seed s w).seed).1, (digestHalves (hm fs fp seed s w).seed).2,
      (digestHalves (hm fs fp seed s w).xd).1, (digestHalves (hm fs fp seed s w).xd).2,
      (digestHalves (hm fs fp seed s w).sd).1, (digestHalves (hm fs fp seed s w).sd).2,
      (digestHalves (hm fs fp seed s w).dap).1, (digestHalves (hm fs fp seed s w).dap).2,
      (hm fs fp seed s w).a417]
    (Returns (B1.Digest.digestCells (hm fs fp seed s w).sdg))

end
end LeanVM.Guest.B1.Main
