/-
  LeanVM.Guest.B1.Terminal.TermComplete

  What the terminal's completeness proofs read from `TermPre` on one memory holding the caller's
  words.
-/

module

public import LeanVM.Guest.B1.Terminal.TermSigma

/-!
# `check_opening_terminal`, its data fixed

The honest direction of `MeaningTerminal` (`check_opening_terminal_completeAtBWE`) has these
hypotheses:

* `hpre`: `TermPre` (what `verify_sub` establishes, soundness's precondition) on every memory
  holding the caller's words `Lin` (defined below `2^κ`);
* `hreg`: the words it reads lie in `Lin` (`TermRegion`: the bus point, the tables' point of
  `nc` words, `g^nc` being its argument `g_zc_n`, the base `kappa_base`, the columns' offsets, the
  nibble shares at `g_squares·g^34`, the outputs' and the ring switch's points, the coefficients,
  the terminal point and its complements);
* `hbus`: the bus point has at most `34` coordinates, so its prefix chain (`|bus.point| + 1` words)
  fits the guest's `35`-word buffer (`TermPre` allows `40`);
* `hfin`: the WHIR terminal equation `(inner + basis(x))·residual = target`, `MeaningTerminal`'s
  conclusion;
* `6 ≤ κ`: the memory is defined below `64`, where `eq_prefix_chain`'s range checks read.

The data that do not depend on the memory (the tables' point `chis`, the lengths) come from one
memory holding `Lin`, as do the facts about them the callees' completeness and the
honest buffers (`termOwn`) need (`TermFacts`); without such a memory the statement is empty.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol
open LeanVM.Protocol.Verifier hiding gpow
open LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

theorem readsAt_transfer {rd rd' : Reader} {L : Main.Layout} (h : MemL rd L) (h' : MemL rd' L)
    {b : ℕ} {xs : List E} (hr : ReadsAt rd (ofK (addressOfIndex b)) xs)
    (hreg : ∀ k < xs.length, RegionL L (b + k)) : ReadsAt rd' (ofK (addressOfIndex b)) xs :=
        fun k hk =>
  ⟨(hr k hk).1, by
    rw [Main.addr_ofK, ← Main.memL_agree h h' _ (hreg k hk), ← Main.addr_ofK]; exact (hr k hk).2⟩

/-- **The facts about the terminal's data** its callees' completeness (`termKids_completeB`,
`termKids_regions`, `termKids_mem`) and its honest buffers read. -/
structure TermFacts (κ : ℕ) (Lin : Main.Layout) (D : TermData) : Prop where
  own : List.Forall₂ (fun c s => c.length ≤ s) (termOwn D) [35, 35, 35, 41, 31]
  reg : ∀ i, TermRegion D.B D.zs.length D.chis.length D.τ D.ood.length i → RegionL Lin i
  zl : D.zs.length ≤ 34
  cl : D.chis.length ≤ 34
  xl : D.x.length ≤ 32
  τl : D.τ + 6 ≤ 34
  ol : D.outPt.length = D.τ + 6
  rl : D.ringPoint.length = D.τ + 6
  cf : D.coeffs.length = 64
  gmu : D.gmu = gen ^ D.zs.length
  gz : D.gzcn = gen ^ D.chis.length
  glm : D.glm = gen ^ D.m
  gtau : D.gtau = gen ^ D.τ
  m1 : 1 ≤ D.m
  m : D.m ≤ 32
  KC : ∀ c < Tables.nCommittedCols, D.KC.getD c 0 < 31
  OF : ∀ c < Tables.nCommittedCols, D.OF.getD c 0 < 2 ^ 32 ∧ 2 ^ D.KC.getD c 0 ∣ D.OF.getD c 0
  rd : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (addressOfIndex D.B.zeta)) D.zs ∧
    ReadsAt rd (ofK (addressOfIndex D.B.chi)) D.chis ∧
    ReadsAt rd (ofK (addressOfIndex D.B.zv)) D.outPt ∧ ReadsAt rd (ofK (addressOfIndex D.B.pt1)) (p1Of D.x)
  odl : D.ood.length ≤ 30
  gm : D.gm = gen ^ D.ood.length
  rdO : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (addressOfIndex D.B.oz)) D.ood
  mem : ∀ b0 outs rd, LowDef κ rd → MemL rd (bufL b0 [35, 35, 35, 41, 31] (termOwn D)) → MemL rd Lin →
    MemL rd (outsL (kidsAt (termKids Lin D b0) [] outs) outs) →
    MemL rd (Kid.lins (kidsAt (termKids Lin D b0) [] outs))

end
end LeanVM.Guest.B1.VerifySub
