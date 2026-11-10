import Rv64Verifier.Proofs.Pcs.VsoRowed
import Rv64Verifier.Proofs.Pcs.VsoRound
import Rv64Verifier.Proofs.Pcs.VsoFinalSpec
import Rv64Verifier.Proofs.Pcs.VsoOpenOA

/-!
# `verify_stacked_opening`'s level loop, whole

A level from its head (`Head`): the fold rounds, the opening and the Merkle checks (`Merkled`),
the slices, `eq_kernel` (`Kerneled`), the rows (`RowsZero`, `RowsDeep`, to `Rowed`), and the tail
to the next level's head or the final level's tail (`LevelTail`). `LeavesSpec` is what the rows
read, from the Merkle checks. `levels` is the induction on the levels left, `loopSpec_of` the loop
from the entry.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

/-- What the rows read at `eq_kernel`'s return: the leaves the Merkle checks read, the
quadratic's length in `s7`, the constant of the division by three. -/
def LeavesSpec : Prop :=
  ∀ (s : MachineState) (x : LCtx) (h t u v w m t' k : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) (lf q res : List E)
    (pend : List (List E × Model.Pcs.GluedWeightRust)) (d : Digest) (qs : List Word),
    VsoPre s → Merkled s x h t u v w m ℓ Wl lf q res pend d qs → Slices s m t' →
    Kerneled s t' k lf →
    LeavesAt s k (wordsAt s w) ∧ k.getMem (s.getReg .x2 - 808) = k.getReg .x23 ∧
      k.getMem (s.getReg .x2 - 880) = 0xffffffffaaaaaaab

/-- **A level's tail**, from the rows' values to the next level's head, the final level's tail,
or an `Err`. -/
def LevelTail : Prop :=
  ∀ (s : MachineState) (x : LCtx) (h t u v w m t' k r : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) (lf q res : List E)
    (pend : List (List E × Model.Pcs.GluedWeightRust)) (d : Digest) (qs : List Word),
    VsoPre s → Cfg s x.QP x.QL →
    Wl.folds.length = ((Model.Pcs.ladderFolds (K0 s + 1)).take ℓ).sum →
    Merkled s x h t u v w m ℓ Wl lf q res pend d qs → Slices s m t' → Kerneled s t' k lf →
    Rowed s k r (Model.Pcs.rowValuesRust ℓ (wordsAt s w) (Model.eqKernelRust lf)) →
    ∃ u', Reaches Image.code r u' ∧ (FailR s u' ∨
      (∃ Wl', Head s x u' (ℓ + 1) Wl' ∧
        Wl'.folds.length = ((Model.Pcs.ladderFolds (K0 s + 1)).take (ℓ + 1)).sum) ∨
      ∃ Wl' residual, VsoFinalIn Transcript.OpeningsAt s x u' Wl' residual)

/-- The callees' contracts a level needs. -/
structure LevelCallees : Prop where
  hD : DuplexSpec
  hG : GrowOneFreshSpec 0x80011c78 24 8
  hPE : PolyEvalSpec
  hRP : RoundPolyErrSpec
  hNS : NextScalarsSpec
  hSm : SamplesSpec
  hN : NextScalarSpec
  hG80 : GrowOneFreshSpec 0x8000c7d0 80 8
  hA : AbsorbSpec
  hTA : TryAllocZeroedSpec
  hP : MultilinearContracts.PowersSpec
  hRF : ReserveFastSpec 0x8000c898
  hM : Runtime.MemcpySpec 0x800126e4
  hK : KeccakHashSpec
  hC : MemcmpSpec
  hE : MultilinearContracts.EqKernelSpec

/-- **A level**, from its head: an `Err`, the next level's head, or the final level's tail. -/
theorem level (hc' : LevelCallees) (h0 : RowsZero) (hDp : RowsDeep) (hLv : LeavesSpec)
    (hTl : LevelTail) {s : MachineState} {x : LCtx} {h : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} (hpre : VsoPre s) (hc : Cfg s x.QP x.QL)
    (hnf : Wl.folds.length = ((Model.Pcs.ladderFolds (K0 s + 1)).take ℓ).sum)
    (hh : Head s x h ℓ Wl) :
    ∃ u', Reaches Image.code h u' ∧ (FailR s u' ∨
      (∃ Wl', Head s x u' (ℓ + 1) Wl' ∧
        Wl'.folds.length = ((Model.Pcs.ladderFolds (K0 s + 1)).take (ℓ + 1)).sum) ∨
      ∃ Wl' residual, VsoFinalIn Transcript.OpeningsAt s x u' Wl' residual) := by
  obtain ⟨t, r1, ht⟩ := foldRounds hc'.hD hc'.hG hc'.hPE hc'.hRP hpre hh
  rcases ht with hf | ⟨lf, q, hf⟩
  · exact ⟨t, r1, Or.inl hf⟩
  obtain ⟨m, r2, hm⟩ := levelFoldedMerkle hc'.hNS hc'.hSm hc'.hN hc'.hRP hc'.hG80 hc'.hD hc'.hA
    hc'.hTA hc'.hP hc'.hRF hc'.hM hc'.hK hc'.hC hpre (vsoOpenMem_of hpre) hc hnf hf
  rcases hm with hm | ⟨u, v, w, res, pend, d, qs, hm⟩
  · exact ⟨m, r1.trans r2, Or.inl hm⟩
  have hP := (hm.mi.phase hm.mo.hdr).paths
  obtain ⟨t', r3, ht'⟩ := slices hc'.hTA hpre (lo := heapNext w) hm.mo.pc hm.mo.sp hm.mo.inv
    hm.mo.mono (by rw [hm.mo.x20, hm.mo.x22]; exact hP)
  rcases ht' with hd | hsl
  · exact ⟨t', r1.trans (r2.trans r3), Or.inl (Or.inl hd)⟩
  obtain ⟨k, r4, hk⟩ := kernel hc'.hE hpre hm hsl
  rcases hk with hd | hk
  · exact ⟨k, r1.trans (r2.trans (r3.trans r4)), Or.inl (Or.inl hd)⟩
  have hlt := hh.lvl
  have hK := K0_lt s
  obtain ⟨k', r5, hmem, hregs, hbr⟩ := rowsBranch hpre hk (hk.lvl hpre hm hsl) (by omega)
  obtain ⟨hLA, h808, h880⟩ := hLv s x h t u v w m t' k ℓ Wl lf q res pend d qs hpre hm hsl hk
  have r15 := r1.trans (r2.trans (r3.trans (r4.trans r5)))
  rcases hbr with ⟨rfl, hpc'⟩ | ⟨hne, hpc'⟩
  · obtain ⟨r, r6, hr⟩ := h0 s t' k k' lf (wordsAt s w) hpre hk hLA h808 hpc' hmem hregs
    rcases hr with hf | hr
    · exact ⟨r, r15.trans r6, Or.inl hf⟩
    obtain ⟨u', r7, hu'⟩ := hTl s x h t u v w m t' k r 0 Wl lf q res pend d qs hpre hc hnf hm hsl
      hk hr
    exact ⟨u', r15.trans (r6.trans r7), hu'⟩
  · obtain ⟨r, r6, hr⟩ := hDp s t' k k' lf (wordsAt s w) ℓ hpre hne hk hLA h880 hpc' hmem hregs
    rcases hr with hf | hr
    · exact ⟨r, r15.trans r6, Or.inl hf⟩
    obtain ⟨u', r7, hu'⟩ := hTl s x h t u v w m t' k r ℓ Wl lf q res pend d qs hpre hc hnf hm hsl
      hk hr
    exact ⟨u', r15.trans (r6.trans r7), hu'⟩

/-- **The levels from `ℓ` on.** -/
theorem levels (hc' : LevelCallees) (h0 : RowsZero) (hDp : RowsDeep) (hLv : LeavesSpec)
    (hTl : LevelTail) {s : MachineState} {x : LCtx} (hpre : VsoPre s) (hc : Cfg s x.QP x.QL) :
    ∀ n ℓ (h : MachineState) (Wl : Model.Pcs.WhirLocals), K0 s + 2 - ℓ = n →
      Head s x h ℓ Wl → Wl.folds.length = ((Model.Pcs.ladderFolds (K0 s + 1)).take ℓ).sum →
      ∃ u, Reaches Image.code h u ∧
        (FailR s u ∨ ∃ Wl' residual, VsoFinalIn Transcript.OpeningsAt s x u Wl' residual)
  | 0, ℓ, h, Wl, hn, hh, _ => absurd hh.lvl (by omega)
  | n + 1, ℓ, h, Wl, hn, hh, hnf => by
    obtain ⟨u, r1, hu⟩ := level hc' h0 hDp hLv hTl hpre hc hnf hh
    rcases hu with hf | ⟨Wl', hh', hnf'⟩ | hfin
    · exact ⟨u, r1, Or.inl hf⟩
    · obtain ⟨v, r2, hv⟩ := levels hc' h0 hDp hLv hTl hpre hc n (ℓ + 1) u Wl' (by omega) hh' hnf'
      exact ⟨v, r1.trans r2, hv⟩
    · exact ⟨u, r1, Or.inr hfin⟩

/-- **The level loop**, from the entry. -/
theorem loopSpec_of (hc' : LevelCallees) (hDot : MultilinearContracts.DotSpec) (hAl : AllocSpec)
    (hG8 : GrowOneFreshSpec 0x8000d7bc 8 8) (h0 : RowsZero) (hDp : RowsDeep) (hLv : LeavesSpec)
    (hTl : LevelTail) : LoopSpec Transcript.OpeningsAt := by
  intro s hpc hpre
  obtain ⟨v, r1, hv⟩ := toLevels hc'.hTA hc'.hD hc'.hP hDot hAl hG8 hc'.hRP hpc hpre
  rcases hv with hf | ⟨b, nxb, QP, QL, FP, RP, hc, hcf⟩
  · exact ⟨v, r1, Or.inl (Fail.toR hf)⟩
  obtain ⟨L, h, r2, hh⟩ := init hpre hcf
  obtain ⟨u, r3, hu⟩ := levels hc' h0 hDp hLv hTl hpre (x := ⟨b, v, nxb, QP, QL, FP, RP, L⟩) hc
    (K0 s + 2) 0 h _ (by omega) hh rfl
  rcases hu with hf | ⟨Wl', residual, hfin⟩
  · exact ⟨u, r1.trans (r2.trans r3), Or.inl hf⟩
  · exact ⟨u, r1.trans (r2.trans r3), Or.inr ⟨_, Wl', residual, hfin⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
