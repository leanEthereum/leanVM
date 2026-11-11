/-
  LeanVM.Guest.B1.VerifySub.H.Sigma

  `verify_sub`'s honest valuation on an honest child: its parameters, pointers, the callees'
  results, and the values its calls pass (the batched target among them).
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.B1.VerifySub.H.Outs
public import LeanVM.Guest.B1.VerifySub.H.Sec

/-!
# The honest valuation

`ChildSegs.vals_length`: the GKR's three values. `ChildSegs.target_eq`: the opening's target is the
batch `verify_sub` computes at `1886`. `VsSig`: what the honest valuation holds;
`vs_sig`: it holds, with the section data `vsCPre_complete` takes.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- The GKR's three values. -/
theorem vals_length (hbl : bytecode.length = 2 ^ 23) : S.vals.length = 3 := by
  obtain ⟨hrun, -, -, -⟩ := S.runG' hbl
  obtain ⟨sp, hsp⟩ := S.capS_carries
  have hsc : capOf sp.state = S.capS := hsp.1
  have hcl : S.capS.length = 5 := S.capS_length
  have hcan : AllCanonical S.capS := by rw [← hsc]; exact Tables.tb_capOf_canonical _
  obtain ⟨-, -, -, -, -, -, hr, -⟩ := Tables.gk_walk hrun ⟨sp, hsp⟩
  show S.rG.2.2.length = 3
  rw [hr]
  exact (Tables.gkSl_inv hcl hcan _).2.2.2

/-- The bus challenges. -/
theorem alphas_length : S.alphas.length = 4 := by
  have e := congrArg (fun p ↦ p.1.length) S.halphas
  simp only [squeezeN_len] at e
  rw [← e]; rfl

/-- **The opening's target** is the batch `verify_sub` computes. -/
theorem target_eq (hbl : bytecode.length = 2 ^ 23) :
    S.target = polyEval (S.slices.map (phiMap · S.rchs)) gen +
      ∑ i ∈ Finset.range 142, S.lam ^ (i + 1) * S.H.poolW.getD (vsKept i) 0 +
        S.lam ^ 143 * S.word := by
  have hok := (S.H_run hbl).1
  have hr : S.H.rows.length = 6 := S.hrowsL
  have hk := kept_values (Tables.VtHonest.vtH_columns hok hr)
  rw [Tables.VtHonest.vtH_values hok hr, S.H_claims] at hk
  have hn : (notLanes S.claims).length = 142 := by
    have := congrArg List.length hk
    simpa [notLanes] using this
  unfold ChildSegs.target batchTarget
  rw [S.km_eq hbl]
  dsimp only
  have hv : (stackClaims S.layout S.claims [⟨qkeccak, S.op, S.word⟩] S.kpt S.slices
      (S.m0 :: S.chs)).map (·.2) =
      polyEval (S.slices.map (phiMap · (S.m0 :: S.chs))) gen ::
        ((notLanes S.claims).map (·.value) ++ [S.word]) := by
    simp [stackClaims, ringSwitchClaim, ColumnClaim.stackClaim, notLanes]
  have hl : (stackClaims S.layout S.claims [⟨qkeccak, S.op, S.word⟩] S.kpt S.slices
      (S.m0 :: S.chs)).length = 142 + 2 := by
    rw [← hn]; simp [stackClaims, notLanes]
  rw [show (notLanes S.claims).map (·.value) = _ from hk] at hv
  rw [hl, hv, dot_powers_batch]
  rfl

end ChildSegs

/-- **What the honest valuation holds.** -/
structure VsSig {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    (bs : List ℕ) (sqE : ℕ) (outs : List (List E × Main.Layout)) (args : List E) (σ : Val) :
    Prop where
  par : ∀ i < 6, σ (.n i) = args.getD i 0
  ptr : ∀ i < 13, σ (.n (vsAllocVars.getD i 0)) = ofK (addressOfIndex (vb bs i))
  ret : ∀ j < 13, ∀ k < (vsRetVars.getD j []).length,
    σ (.n ((vsRetVars.getD j []).getD k 0)) = (outs.getD j ([], [])).1.getD k 0
  e112 : σ (.n 110) = eOfNat S.rate
  e29 : σ (.n 27) = eOfNat S.logMem
  e521 : σ (.n 308) = gen ^ pushTotal S.logMem S.hs
  e537 : σ (.n 324) = S.x0
  e547 : σ (.n 334) = S.x1
  e825 : [σ (.n 612), σ (.n 613), σ (.n 614), σ (.n 615), σ (.n 616)] = S.capS
  e836 : σ (.n 623) = S.β
  e838 : σ (.n 625) = ofK (addressOfIndex (vcG bs))
  e645 : σ (.n 645) = ofK (addressOfIndex (S.cT bs + 5 + 3 * S.H.n))
  e858 : σ (.n 646) = gen ^ S.τ
  e862 : σ (.n 650) = ofK (addressOfIndex (S.cL bs))
  e1312 : [σ (.n 1100), σ (.n 1101), σ (.n 1102), σ (.n 1103), σ (.n 1104)] = capOf S.s8.perm
  e1111 : σ (.n 1111) = S.lam
  e1886 : σ (.n 1681) = S.target
  e1686 : σ (.n 1686) = gen ^ (S.μs - B1.Whir.minOpenLog)
  e122 : σ (.n 122) = B1.Whir.rateSel S.rate
  push : ∀ b < 54, ∃ κ, κ + Tables.blockKappaAdj b < 34 ∧
    σ (.n (vsPushM b)) = ofK (addressOfIndex (sqE + κ))

variable {rd : Reader} {args : List E}

/-- **The honest valuation holds `VsSig`**, with the section data. -/
theorem vs_sig {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest} {c : Child}
    (S : ChildSegs bytecode seed c) {sqE outE : ℕ}
    (hargs : args = [(digestHalves (statementDigest seed c.statement)).1,
      (digestHalves (statementDigest seed c.statement)).2, (digestHalves seed).1,
      (digestHalves seed).2, ofK (addressOfIndex sqE), ofK (addressOfIndex outE)])
    (bs : List ℕ) (outs : List (List E × Main.Layout)) (O : VsOuts S bs sqE outs) {κ : ℕ}
    (hκ : 14 ≤ κ) (hlow : LowDef κ rd)
    (hmem : ∀ i < 13, ReadsAt rd (ofK (addressOfIndex (bs.getD i 0))) (S.ownW.getD i []))
    (hsq : ReadsAt rd (ofK (addressOfIndex sqE)) expTableWords)
    (hfx : ReadsAt rd (ofK (addressOfIndex outE)) (DeferredClaim.cells c.freshClaim)) :
    Nonempty (VsSecData rd (vsW bs outs) args) ∧
      VsSig S bs sqE outs args (vsσ rd (vsW bs outs) args) := by
  have hl : args.length = 6 := by rw [hargs]; rfl
  obtain ⟨D, hv, hlir, hlm, hhs, hm, hr, hτ, F, elam, es8, -, -⟩ :=
    vsSec hbl S hargs bs outs hκ hlow hmem hsq hfx O.o0 O.o1 O.o6 O.o7 O.o10
  refine ⟨⟨D⟩, ?_⟩
  have par := fun i (hi : i < 6) ↦ vsC_param (rd := rd) (w := vsW bs outs) hl hi
  have ptr := fun i (hi : i < 13) ↦ vs_alloc_ptr (rd := rd) hl bs outs hi
  have ret := fun j (hj : j < 13) k (hk : k < (vsRetVars.getD j []).length) ↦
    vs_ret_val (rd := rd) hl bs outs hj hk
  have e112 := D.e112
  have e29 := D.e29
  rw [hlir] at e112
  rw [hlm] at e29
  have hS := (vsSizesT_complete (C := fun _ _ _ ↦ True) (next := True) (kret := fun _ ↦ True) hl
    D.hκ6 D.hlow D.hl1 D.hl4 D.hlm1 D.hm30 D.e112 D.e29 D.e122 D.e130 D.hsl D.hdims D.hkb trivial
    trivial trivial).1
  have hkbv : ∀ s < 8, vsσ rd (vsW bs outs) args (.n (140 + s)) =
      gen ^ (([0, D.logMem] ++ D.hs).getD s 0) :=
    fun s hs8 ↦ by rw [hS s hs8, D.hcount, kbase_getD D.hsl hs8]
  have hpush := (vsPushT_complete (C := fun _ _ _ ↦ True) (next := True) (kret := fun _ ↦ True) hl
    D.hh (by have := D.hm30; omega) hkbv D.hexp (fun _ _ ↦ trivial) trivial).1
  rw [hlm, hhs] at hpush
  have hpp : ∀ b < 54, vsσ rd (vsW bs outs) args (.n (vsPushM b)) =
      vsσ rd (vsW bs outs) args (.n 4) *
        gen ^ ([0, D.logMem] ++ D.hs).getD (Tables.blockKappaSrc.getD b 0) 0 :=
    fun b hb ↦ vs_push_ptr hl hkbv hb
  have hpk : ∀ b < 54, pushKappa D.logMem D.hs b < 34 := fun b hb ↦ pushKappa_lt D.hh (by have := D.hm30; omega) hb
  have hcalls := vsCallsT_complete (C := fun _ _ _ ↦ True) (next := True) (kret := fun _ ↦ True) hl
    D.hd6 trivial trivial trivial trivial
  rw [hτ] at hcalls
  have hlam := vsLamT_complete (C := fun _ _ _ ↦ True) (next := True) (kret := fun _ ↦ True) hl
    D.hz D.hcap966 D.hpool trivial
  rw [hv] at hlam
  have htail := (vsTailPre_complete (C := fun _ _ _ ↦ True) (next := True) (kret := fun _ ↦ True)
    hl D.hκ6 D.hlow D.hmu20 D.hmu30 D.e1684 D.hzeta D.halpha D.hout D.hout'
    D.hout23 trivial trivial trivial trivial trivial).1
  rw [hm] at htail
  have h122 := D.e124
  rw [hr] at h122
  have hL := vsH_lam (rd := rd) (w := vsW bs outs) hl D.hcap966
  obtain ⟨K7, hK7⟩ := S.s7_capOf hbl
  generalize vsσ rd (vsW bs outs) args = σ at *
  have p1 : σ (.n 25) = ofK (addressOfIndex (vb bs 1)) := ptr 1 (by norm_num)
  have e5 : σ (.n 4) = ofK (addressOfIndex sqE) := by rw [par 4 (by norm_num), hargs]; rfl
  have e1303 : σ (.n 1091) = polyEval (S.slices.map (phiMap · S.rchs)) gen := by
    have := ret 8 (by norm_num) 0 (by decide); rw [O.o8] at this; exact this
  have e869 : σ (.n 657) = S.word := by
    have := ret 7 (by norm_num) 6 (by decide); rw [O.o7, hK7] at this; exact this
  have e645 : σ (.n 645) = ofK (addressOfIndex (S.cT bs + 5 + 3 * S.H.n)) := by
    have := ret 6 (by norm_num) 9 (by rw [vsRetVars_lens.2.1]; omega)
    rw [vsRetVars_runs.2.1 9 (by norm_num), O.o6, ChildSegs.vtRetsOf_getD9] at this
    rw [this, Tables.tb_ofK_gpow_mul, Tables.tb_ofK_gpow_mul]
  rw [← es8] at hL
  exact {
    par := par
    ptr := ptr
    ret := ret
    e112 := e112
    e29 := e29
    e521 := hpush
    e537 := F.h537
    e547 := F.h547
    e825 := (congrArg Fs.cap F.hs4).symm
    e836 := F.hβ
    e838 := by rw [hcalls.1, p1, Tables.tb_ofK_gpow_mul]; rfl
    e645 := e645
    e858 := hcalls.2.1
    e862 := by rw [hcalls.2.2.1, e645, Tables.tb_ofK_gpow_mul]; rfl
    e1312 := (congrArg (fun p ↦ p.2.cap) hL).symm
    e1111 := elam
    e1886 := by rw [hlam.2.1, elam, e1303, e869, S.target_eq hbl]
    e1686 := htail
    e122 := by rw [h122, gen_pow_eq_ofK]; rfl
    push := fun b hb ↦ ⟨_, hpk b hb, by rw [hpp b hb, e5, Tables.tb_ofK_gpow_mul]⟩ }

end
end LeanVM.Guest.B1.VerifySub
