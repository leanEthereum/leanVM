/-
  LeanVM.Guest.B1.VsC.VsNatOpenCtx

  `natOpen`'s stacked opening and terminal at `verify_sub`'s context: `D3.Ok`'s `hsid` from `open_stacked`'s
  returns, its `hos` from `open_stacked`'s completeness at the native run.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatOpen
public import LeanVM.Guest.B1.VsC.VsOrcSpec
public import LeanVM.Guest.B1.VsC.VsOrcPhOpen
public import LeanVM.Guest.B1.VsC.VsOrcPhC

/-!
# The stacked opening at the context

* **`VsCtx.hsid_nat`**: `D3.Ok.hsid` (the stacked identity at `check_stack_terminal`'s arguments) from the
  returns `ro` gives `open_stacked`'s words `3991 … 3996` and the terminal's identity `NatOpen.Ok.hacc`.
* **`VsCtx.hos_nat`**: `D3.Ok.hos`'s call (`open_stacked__L{μ - 16}` at the native WHIR run, its queries the
  child's `childQueries`), from `OpenStackedCompleteA` and the guest's values equal to the native ones: the
  rate's selector, the capacity `ringCap`, the target, the stream's words `8`, `9` (the root's halves).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Complete LeanVM.Guest.B1.Stack
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

theorem cstArgs_19 (σ : Val) (w : ℕ → E) : (cstArgsOf σ w).getD 19 0 = w 3994 := rfl

theorem cstArgs_20 (σ : Val) (w : ℕ → E) : (cstArgsOf σ w).getD 20 0 = w 3995 := rfl

theorem cstArgs_21 (σ : Val) (w : ℕ → E) : (cstArgsOf σ w).getD 21 0 = w 3991 := rfl

/-- **The stacked identity at `check_stack_terminal`'s arguments**: words `19`, `20`, `21` are `open_stacked`'s
returns `inner`, `residual`, `target`. -/
theorem VsCtx.hsid_nat (x : VsCtx) (D : D3) (hret : CausalRule x.ret) {ie : ℕ}
    (ro : ∀ j < 6, ∀ σ, x.ret (3991 + j) σ = (osRets D.wE D.bp D.bp1 ie).getD j 0)
    (hacc : (D.wE.inner + stackedBasis D.claims D.lam D.wE.point) * D.wE.residual = D.wE.target)
    (hxq : D.xq = D.wE.point) :
    ((cstArgsOf x.σ0 x.w).getD 19 0 + stackedBasis D.claims D.lam D.xq) * (cstArgsOf x.σ0 x.w).getD 20 0 =
      (cstArgsOf x.σ0 x.w).getD 21 0 := by
  have ha : x.args.length = 6 := rfl
  have e19 : x.w 3994 = D.wE.inner := vsW_retC ha hret (i := 3991 + 3) (by decide) (ro 3 (by norm_num))
  have e20 : x.w 3995 = D.wE.residual := vsW_retC ha hret (i := 3991 + 4) (by decide) (ro 4 (by norm_num))
  have e21 : x.w 3991 = D.wE.target := vsW_retC ha hret (i := 3991 + 0) (by decide) (ro 0 (by norm_num))
  rw [cstArgs_19, cstArgs_20, cstArgs_21, e19, e20, e21, hxq]
  exact hacc

/-- **`open_stacked`'s call at the native run**: at the guest's values equal to `natOpen`'s (the rate's selector,
the capacity the ring switch's draw leaves, the target, the stream's words `8`, `9`), from `open_stacked`'s completeness;
its post pops the child's Merkle hints. -/
theorem VsCtx.hos_nat (x : VsCtx) (hO : ∀ m, m ≤ 14 → OpenStackedCompleteA B2C.fs x.al B2C.cert 17 m)
    {seed : Digest} {c : Child} {N : NatOpen} (hN : N.Ok seed c) {tgt : E} {ic : ℕ} {Rg : ℕ → Prop}
    (h96 : x.σ0 (.n 96) = rateSel N.r)
    (hfsv : [x.σ0 (.n 3033), x.σ0 (.n 3034), x.σ0 (.n 3035), x.σ0 (.n 3036), x.σ0 (.n 3037)] = ringCap N.S)
    (htg : tgt = N.target seed c) (h134 : x.σ0 (.n 134) = c.proof.stream.getD 8 0)
    (h137 : x.σ0 (.n 137) = c.proof.stream.getD 9 0)
    (hxs : ∀ i < N.ws.length, Rg (ic + i)) (hit : ∀ n < 2 ^ winTabBits, Rg (x.qt + 178 + n)) (kc : ℕ) :
    ∃ bp bp1 e : ℕ, CallAtA B2C.fs x.al B2C.cert 17 (openName N.layout.stackLog)
      (x.σ0 (.n 96) :: [x.σ0 (.n 3033), x.σ0 (.n 3034), x.σ0 (.n 3035), x.σ0 (.n 3036), x.σ0 (.n 3037)] ++
        [tgt, x.σ0 (.n 134), x.σ0 (.n 137), ptrAt ic, ptrAt (x.qt + 178)])
      (osRets N.wE bp bp1 (ic + N.ws.length)) Rg
      (fun i => (bp ≤ i ∧ i < bp + pointCap) ∨ (bp1 ≤ i ∧ i < bp1 + pointCap))
      (fun rd => ReadsAt rd (ptrAt bp) (N.wE.point ++ List.replicate (pointCap - N.layout.stackLog) 0) ∧
        ReadsAt rd (ptrAt bp1) (N.wE.point.map (1 + ·) ++ List.replicate (pointCap - N.layout.stackLog) 1))
      (fun rd => ReadsAt rd (ptrAt ic) N.ws ∧ WinTabs rd (ptrAt (x.qt + 178)))
      (fun rd t => SameStreams (t.pops coreProgram rd)
          (Prover.merkleHints true (Prover.childQueries guestBytecode seed c) c.proof.openings) ∧
        t.Every (ExactAt coreProgram rd))
      (B2C.fs (openName N.layout.stackLog)) (allocBase (x.al (openName N.layout.stackLog)) kc)
      (allocBase (x.al (openName N.layout.stackLog)) kc + B2C.fs (openName N.layout.stackLog)) e := by
  have hh := digestScalars_digestOfScalars (c.proof.stream.getD 8 0, c.proof.stream.getD 9 0)
  rw [h96, hfsv, htg, h134, h137, show c.proof.stream.getD 8 0 = (digestHalves (natRoot c)).1 by rw [natRoot, hh],
    show c.proof.stream.getD 9 0 = (digestHalves (natRoot c)).2 by rw [natRoot, hh]]
  have hsp : ∃ sp : Sponge, (⟨ringCap N.S, []⟩ : Fs).Carries sp :=
    carries_capOf (Link.pkPerm (capOf (Link.pkPerm (capOf N.S))))
  exact openCall_of hO hN.shape.stack_ge hN.shape.stack_le hN.shape.rate_ge hN.shape.rate_le (ringCap_length _) hsp
    hN.hos hN.hq hxs hit kc

end
end LeanVM.Guest.B1.VsC
