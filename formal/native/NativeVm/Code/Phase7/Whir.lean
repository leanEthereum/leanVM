module

public import NativeVm.Code.Phase7.Loop
public import NativeVm.Code.Phase7.Final

/-!
# The stacked opening

`whirC_b`: from the state the ring switching leaves (`p.s1`, the regions phase 7 reads there:
`Regs`), the batching, the opening's start, the non-final levels' loop and the final level refine
`verifyStackedOpening` of the stack claims (`verifyStackedOpening_eq`).
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters

variable {p : Par}

theorem stackClaims_size_le (layout : LayoutW) (target : EW) (point coeffs : Array EW)
    (claims : Array ColumnClaimW) (ood : StackClaimW) :
    (stackClaims layout target point coeffs claims ood).size ≤ claims.size + 2 := by
  have : (claims.filterMap (·.onStack layout)).size ≤ claims.size := Array.size_filterMap_le
  simp only [stackClaims, Array.size_append, List.size_toArray, List.length_cons,
    List.length_nil]
  omega

theorem ladder_head {μ : Nat} {L : List Whir.Level} (hok : LadderOk μ L) :
    (L.head?.map (·.fold)).getD 0 = Whir.initialFold := by
  cases L with
  | nil => exact absurd hok.len.1 (by simp)
  | cons a L' =>
    have := hok.head (by simp)
    simpa using this

theorem wOk_zero (L : List Whir.Level) (target : EW) : WOk L 0 ⟨target, #[], #[]⟩ :=
  ⟨rfl, rfl, fun _ h ↦ absurd h (by simp)⟩

/-- **The stacked opening.** -/
theorem whirC_b {bc : Array UInt64} {layout : LayoutW} {rate : Nat} {claims : Array ColumnClaimW}
    {ood : StackClaimW} {target : EW} {coeffs point slices : Array EW}
    (hR : Regs p.s1.mem p.env.work bc layout rate claims ood target coeffs point slices) :
    Refines (fun t s ↦ Base p t s ∧ s.mem = p.s1.mem ∧ t.roots.size ≤ 1)
      (blk [batchingC, initC, .loop (.cmp .ne .r15 (.imm 0)) levelC, finalC])
      (verifyStackedOpening layout.stackLog rate (stackClaims layout target point coeffs claims ood))
      (fun _ t s ↦ Base p t s) (Err p) := by
  have hadm : Whir.Admissible layout.stackLog rate :=
    ⟨hR.lay.stackLogBound.1, hR.lay.stackLogBound.2, hR.lay.rateBound.1, hR.lay.rateBound.2⟩
  have hbd := Admissible.bounds hadm
  obtain ⟨L, hL⟩ : ∃ L, Whir.ladder layout.stackLog rate = some L :=
    ⟨_, ladder_table _ (by omega) _ (by omega) hadm⟩
  have hok := ladder_ok hadm hL
  have hq := ladder_queries_pos hadm hL
  have hl := hok.len
  have hcs : claims.size ≤ claimCap := hR.cl.1
  have hcl : (stackClaims layout target point coeffs claims ood).size ≤
      LeanVM.Protocol.Verifier.maxStackedClaims := by
    have := stackClaims_size_le layout target point coeffs claims ood
    rw [claimCap_val] at hcs
    have : LeanVM.Protocol.Verifier.maxStackedClaims = 512 := rfl
    omega
  rw [verifyStackedOpening_eq hL hcl (by omega) (ladder_head hok)]
  -- the batching
  refine Refines.blk_cons ((Refines.keepRoots KeepsRoots.sampleChallenge (fun r ↦ r.size ≤ 1)
    (batchingC_spec (p := p) (m0 := p.s1.mem) hR.lay hR.cl hR.ood hR.ring hR.kec)).mono
    (fun t s ⟨hb, hm, hr⟩ ↦ ⟨⟨hb, hm⟩, hr⟩) (fun _ _ _ h ↦ h) (fun _ h ↦ h)) fun lam ↦ ?_
  set cl := stackClaims layout target point coeffs claims ood
  -- the opening's start
  refine Refines.pre_blk (P' := LInv p L layout.stackLog (powers lam cl.size) 0
    ⟨dot (powers lam cl.size) (cl.map (·.value)), #[], #[]⟩) ?_ ?_
  · rintro t s ⟨⟨hb, hsc, htg, -, -⟩, hr⟩
    have hR' := hR.congr fun _ _ h1 h2 ↦ low_of_base hb h1 h2
    refine WP.mono (initC_spec (F := fun _ ↦ False) hb.rdi hb.inp hb.workPtr hR'.lay htg) ?_
      fun _ h ↦ h
    rintro s' ⟨L', hL', hlv, hlog, hw, hidx, hn, h15, hf, ho⟩
    have e : L' = L := Option.some.inj (hL'.symm.trans hL)
    rw [e] at hlv hn h15
    refine ⟨⟨hb.frM hf, ⟨⟨hlv, hidx, hn, hlog, ?_⟩, hw⟩, h15⟩, wOk_zero L _, hr⟩
    refine keepX (dep_evec (p := p) basisR.off stackClaimCap _) (by ltac)
      (fun j hj hw ↦ by
        simp only [initW, levelsWords_val, vecWords, stackClaimCap, claimCap_val] at hj hw
        oomega) ho hsc
  -- the non-final levels
  refine Refines.blk_cons (levelsC_b hok (by omega) hq) fun sW ↦ ?_
  -- the final level
  rw [← bind_pure (finalM layout.stackLog Whir.initialFold ⟨powers lam cl.size, cl⟩ (L.length - 1)
    (L.getD (L.length - 1) ⟨0, 0, 0⟩) sW)]
  refine Refines.blk_cons (by
    intro t s hI
    exact finalC_b hok hq rfl (by omega) (by omega) hI.2.1 hR (powers_size' _ _) t s
      ⟨hI.1.1, hI.1.2.1, trivial⟩) fun _ ↦ Refines.pure fun t s h ↦ WP.blk_nil h

end NativeVm.Code.P7
