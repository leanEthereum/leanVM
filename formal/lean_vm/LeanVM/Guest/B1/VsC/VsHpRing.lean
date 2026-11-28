/-
  LeanVM.Guest.B1.VsC.VsHpRing

  `HonParts`' `b2`, `b21`, `b22` and `D3.Ok`'s ring fields at the honest choices: the guest's ring challenges are
  the native verifier's.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatHos
public import LeanVM.Guest.B1.VsC.VsNatLk
public import LeanVM.Guest.B1.VsC.VsOrcFront
public import LeanVM.Guest.B1.VsC.VsOrcFront2
public import LeanVM.Guest.B1.VsC.VsOrcPhD
public import LeanVM.Guest.B1.VsC.VsPh3
public import LeanVM.Guest.B1.VsC.TableSizeC

/-!
# The ring switch's buffers and the cycle count's bits, natively

* **`VsCtx.b2_honest`**: `HonParts.b2` from `Bw1F.b2` (`bw 2 = cbL N`, `N` the row counts' sum) and `Ret1F`: `.n 240`
  is `g^N` (`table_size`'s returns, `g_cycles`' product), `N < 2^24` (`FrontNum`'s `N < 2^wd`, `wd ≤ 24`).
* **`VsCtx.ringVals_nat`**: at `ring_nat`'s hypotheses (`verify_keccak`'s returns `rvk` from `s'`, its full queue,
  the nonce `n` at the cursor), `mcW σ0 = ringF S ++ ringG S`, `.n 3026 = ringRho S`, `mcRc σ0` the native ring
  coefficients, `S = s'.nonceState n`.
* **`VsCtx.ringBufs_nat`** (`b21`, `b22`, `D3.Ok.b23`), **`VsCtx.r3810_nat`** (`D3.Ok.r3810`), **`VsCtx.hrt_nat`**
  (`D3.Ok.hrt`): each from its native form, the buffer or return as an explicit equation.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Link
open LeanVM.Prover.Exec (bitWord)

@[expose] public section

/-! ## The native ring challenges' lists -/

theorem ringChs_take16 (S : KeccakState) : (ringChs S).take 16 = ringF S ++ ringG S := by
  show (ringChs S).take (8 + 8) = (ringChs S).take 8 ++ ((ringChs S).drop 8).take 8
  exact List.take_add ..

theorem ringF_length (S : KeccakState) : (ringF S).length = 8 := by
  simp [ringF, ringChs, Link.pkSqueeze_length, ringMapWidth]

section
variable {x : VsCtx}

/-! ## `b2`: the cycle count's bits -/

/-- **`HonParts.b2`** from the front's buffer `bw 2 = cbL N` (`Bw1F.b2`) and returns (`Ret1F`). -/
theorem VsCtx.b2_honest (hok : x.Ok) (hret : CausalRule x.ret) (hR : x.Ret1F)
    (hb2 : x.bw.getD 2 [] = cbL (x.rows 0 + x.rows 1 + x.rows 2 + x.rows 3 + x.rows 4 + x.rows 5)) :
    ∃ n, n < 2 ^ 24 ∧ x.σ0 (.n 240) = ofK (g ^ n) ∧
      x.bw.getD 2 [] = (List.range 24).map fun j => bitWord (n.testBit j) := by
  have ha : x.args.length = 6 := rfl
  obtain ⟨layout, r, hann, -, hF⟩ := frontNum_of_child hok.child
  have hl : x.lay = layout := VsCtx.lay_of hann
  have hN : x.rows 0 + x.rows 1 + x.rows 2 + x.rows 3 + x.rows 4 + x.rows 5 < 2 ^ 24 := by
    unfold VsCtx.rows
    rw [hl]
    exact lt_of_lt_of_le hF.hN (Nat.pow_le_pow_right (by norm_num) hF.hw24)
  unfold VsCtx.Ret1F at hR
  have hw : ∀ t < 6, x.w (tsRet t) = gen ^ x.rows t := fun t ht => by
    have hi : VsRetIdx (tsRet t) := by interval_cases t <;> decide
    exact (vsW_ret' ha hret hi).trans (hR.rts t ht _).1
  obtain ⟨h216, h224⟩ := vsVal_216 (rd0 := x.rd0) (w := x.w) ha x.rows hw
  have e240 : vsVal x.rd0 x.w x.args (.n 240) =
      gen ^ (x.rows 0 + x.rows 1 + x.rows 2 + x.rows 3 + x.rows 4 + x.rows 5) := by
    rw [good_mulF (vsB0_good (rd0 := x.rd0) (w := x.w) ha (.mul (.n 240) (.n 216) (.n 224)) (by simp [vsB0]))
      (by omega) (by omega), h216, h224, ← pow_add]
  refine ⟨_, hN, ?_, ?_⟩
  · show vsVal x.rd0 x.w x.args (.n 240) = _
    rw [e240, LeanVM.Guest.Value.gen_pow_eq_ofK]
  · rw [hb2, cbL]
    exact List.map_congr_left fun j _ => (bitWord_testBit _ j).symm

/-! ## The ring switch's challenges -/

/-- **The ring switch's words, natively** (`ring_nat`'s, as lists): the map challenges `mcW σ0` are `f ++ g`, their
halves `f` and `g`, the coefficients `mcRc σ0` the native ones, `.n 3026` the merging challenge `ρ`. -/
theorem VsCtx.ringVals_nat {s' : Fs} {bm nx : ℕ} {kw n : E} {S : KeccakState} (hS : s'.nonceState n = S)
    (hret : CausalRule x.ret)
    (rvk : ∀ j < 7, ∀ σ, x.ret (2915 + j) σ = (vkRets s' (ptrAt (bm + 144)) nx kw).getD j 0)
    (hpend : s'.pend.length = rateScalars) (hrd : ReadsAt x.rd0 (ptrAt (bm + 144 + nx)) [n]) :
    mcW x.σ0 = ringF S ++ ringG S ∧ (mcW x.σ0).take 8 = ringF S ∧ (mcW x.σ0).drop 8 = ringG S ∧
      mcRc x.σ0 = ringCoefficients (ringF S) (ringG S) ∧ x.σ0 (.n 3026) = ringRho S := by
  obtain ⟨-, hrho, -, hmc⟩ := x.ring_nat hret rvk hpend hrd
  rw [hS, ringChs_take16] at hmc
  rw [hS] at hrho
  have ht : (mcW x.σ0).take 8 = ringF S := by rw [hmc]; exact List.take_left' (ringF_length S)
  have hd : (mcW x.σ0).drop 8 = ringG S := by rw [hmc]; exact List.drop_left' (ringF_length S)
  exact ⟨hmc, ht, hd, by rw [mcRc, ht, hd], hrho⟩

/-- **`HonParts.b21`, `b22` and `D3.Ok.b23`** from the buffers' native words: `f ++ g`, the native ring
coefficients, the merged slices at the native `ρ`. -/
theorem VsCtx.ringBufs_nat {s' : Fs} {bm nx : ℕ} {kw n : E} {S : KeccakState} (hS : s'.nonceState n = S)
    (hret : CausalRule x.ret)
    (rvk : ∀ j < 7, ∀ σ, x.ret (2915 + j) σ = (vkRets s' (ptrAt (bm + 144)) nx kw).getD j 0)
    (hpend : s'.pend.length = rateScalars) (hrd : ReadsAt x.rd0 (ptrAt (bm + 144 + nx)) [n])
    (hb21 : x.bw.getD 21 [] = ringF S ++ ringG S)
    (hb22 : x.bw.getD 22 [] = ringCoefficients (ringF S) (ringG S))
    (hb23 : x.bw.getD 23 [] = rsW (x.bw.getD 15 []) (x.sw bm 0 144) (ringRho S)) :
    x.bw.getD 21 [] = mcW x.σ0 ∧ x.bw.getD 22 [] = mcRc x.σ0 ∧
      x.bw.getD 23 [] = rsW (x.bw.getD 15 []) (x.sw bm 0 144) (x.σ0 (.n 3026)) := by
  obtain ⟨hmc, -, -, hrc, hrho⟩ := x.ringVals_nat hS hret rvk hpend hrd
  exact ⟨hb21.trans hmc.symm, hb22.trans hrc.symm, by rw [hb23, hrho]⟩

/-- **`D3.Ok.r3810`** from `ring_switch_target`'s native return. -/
theorem VsCtx.r3810_nat {s' : Fs} {bm nx : ℕ} {kw n : E} {S : KeccakState} (hS : s'.nonceState n = S)
    (hret : CausalRule x.ret)
    (rvk : ∀ j < 7, ∀ σ, x.ret (2915 + j) σ = (vkRets s' (ptrAt (bm + 144)) nx kw).getD j 0)
    (hpend : s'.pend.length = rateScalars) (hrd : ReadsAt x.rd0 (ptrAt (bm + 144 + nx)) [n])
    (hr : ∀ σ, x.ret 3810 σ = ringTarget (rsW (x.bw.getD 15 []) (x.sw bm 0 144) (ringRho S)) (ringF S) (ringG S)) :
    ∀ σ, x.ret 3810 σ = ringTarget (rsW (x.bw.getD 15 []) (x.sw bm 0 144) (x.σ0 (.n 3026)))
      ((mcW x.σ0).take 8) ((mcW x.σ0).drop 8) := by
  obtain ⟨-, ht, hd, -, hrho⟩ := x.ringVals_nat hS hret rvk hpend hrd
  intro σ
  rw [hr σ, ht, hd, hrho]

/-- **`D3.Ok.hrt`** from `ring_switch_target`'s call at the native words. -/
theorem VsCtx.hrt_nat {s' : Fs} {bm nx : ℕ} {kw n : E} {S : KeccakState} (hS : s'.nonceState n = S)
    (hret : CausalRule x.ret)
    (rvk : ∀ j < 7, ∀ σ, x.ret (2915 + j) σ = (vkRets s' (ptrAt (bm + 144)) nx kw).getD j 0)
    (hpend : s'.pend.length = rateScalars) (hrd : ReadsAt x.rd0 (ptrAt (bm + 144 + nx)) [n])
    {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k a fp er : ℕ} {sl m : List E}
    (h : RtCall fs al cert k a (rsW sl m (ringRho S)) (ringF S ++ ringG S) fp er) :
    RtCall fs al cert k a (rsW sl m (x.σ0 (.n 3026))) (mcW x.σ0) fp er := by
  obtain ⟨hmc, -, -, -, hrho⟩ := x.ringVals_nat hS hret rvk hpend hrd
  rw [hmc, hrho]
  exact h

end

end
end LeanVM.Guest.B1.VsC
