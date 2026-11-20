/-
  LeanVM.Guest.B1.Sig.SpWotsSound

  `sp_wots` is sound: whenever its body holds (under any call relation: it calls nothing), it
  returns one word, the WOTS+C leaf of the chain values its frame holds at the key whose
  address is its second and third arguments and the digits the encoding digest, its fourth, holds
  (`base_2b`), of digit sum `T = 128`; over cells.
-/

module

public import LeanVM.Guest.Pack.sp_wots.Core
public import LeanVM.Guest.B1.Sig.SpWotsGroups
public import LeanVM.Guest.B1.Sig.XmssCore
import LeanVM.Guest.Fast.SpWots
import LeanVM.Guest.B1.Sig.SpWotsLinksAll

/-!
# `sp_wots`, sound

A valuation `σ` of `sp_wots`'s body is a valuation of its reference function's names, each group's
digit word and each chain's start at the value the decoder reads (`sp_wots_fwd`), and on the names
the commands give the digits, their sum, their encoding and the leaf (`spWotsRef_sat`). In the
guest's valuation `σ`, `spDigitR σ i` is chain `i`'s digit and `spStartR σ i` the value its start
is hinted into, read through the template's layout (`SpWotsLayout`), which the decoder reads
too.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Ref LeanVM.Guest.Fast

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- **Chain `i`'s digit** in the guest's valuation `σ`. -/
noncomputable def spDigitR (σ : Val) (i : Nat) : Nat := spDigit (σ ∘ spRen) i

/-- **Where chain `i`'s start is hinted** in the guest's valuation `σ`: the guest's value of the
template's. -/
noncomputable def spStartR (σ : Val) (i : Nat) : V := spRen (spStart (σ ∘ spRen) i)

/-- **`sp_wots` is sound**: whenever its body holds of `σ`, it returns one word `leaf`:
the digits `spDigitR σ` sum to `128`, the fourth argument is their encoding (`spX`: digit `i` at
`spDigitPos i`, `spX_digit`), and `leaf` is the one-time leaf of the chain values at `spStartR σ`
(`spLeafCell`) at the address `(σ n1, σ n2)`. -/
theorem sp_wots_sound_cells {rets : List E}
    (h : Stmt.HoldsList C rd σ (Fn.«sp_wots».core).body False (fun rs => rs = rets)) :
    ∃ leaf, rets = [leaf] ∧ (∀ i, spDigitR σ i < 4) ∧
      ∑ i ∈ Finset.range 64, spDigitR σ i = 128 ∧ σ (.n 3) = eOfNat128 (spX (spDigitR σ) 64) ∧
      leaf = spLeafCell (σ (.n 0)) (σ (.n 1)) (σ (.n 2)) (spDigitR σ) fun i => σ (spStartR σ i) := by
  obtain ⟨ρ, hp, hpos, hsat, hret⟩ := sp_wots_fwd h
  have hp' : [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3)] = [ρ .pp, ρ .a0, ρ .a1, ρ .encoding] := hp
  simp only [List.cons.injEq, and_true] at hp'
  obtain ⟨h0, h1, h2, h3⟩ := hp'
  obtain ⟨hg, hsum, henc, hleaf⟩ := spWotsRef_sat hsat
  have mem : ∀ p < 22, ∀ k < 4 ^ spN p, ∀ r < spN p,
      (spSel.getD p 0 + offAt (spTabOf p) r k, spStartN (3 * p + r) k) ∈ spPositions :=
    fun p hp k hk r hr => by
      simp only [spPositions, List.mem_flatMap, List.mem_cons, List.mem_map, List.mem_range]
      exact ⟨p, hp, .inr ⟨k, hk, r, hr, rfl⟩⟩
  have hsel : ∀ p < 22, σ (.n (spSel.getD p 0)) = ρ (.group p) := fun p hp =>
    (hpos (spSel.getD p 0, .group p)
      (List.mem_flatMap.mpr ⟨p, List.mem_range.mpr hp, List.mem_cons_self ..⟩)).symm
  have harm : ∀ p < 22, spK σ p = spArm ρ p := fun p hp => by
    rw [spK, spRen_n, ← spSel_eq p hp, hsel p hp, spArm]
  have hdig : ∀ i < 64, spDigitR σ i = spDig ρ i := fun i hi => by
    rw [spDigitR, spDigit, spDig, ← harm (i / 3) (by omega)]
    rfl
  have hst : ∀ i < 64, σ (spStartR σ i) = ρ (spStartN i (spArm ρ (i / 3))) := fun i hi => by
    have hp : i / 3 < 22 := by omega
    have hr : i % 3 < spN (i / 3) := by unfold spN; split <;> omega
    have hc : cwCell 21 spSel spFirst spRest spLast σ i =
        spSel.getD (i / 3) 0 + offAt (spTabOf (i / 3)) (i % 3) (spArm ρ (i / 3)) := by
      rw [← harm _ hp]
      unfold cwCell spTabOf spK
      rw [spRen_n, ← spSel_eq _ hp]
      by_cases h21 : i / 3 < 21
      · by_cases h0 : i / 3 = 0 <;> simp [h0, h21, spN, logG_eq_logGT]
      · simp [h21, spN, logG_eq_logGT, show ¬i < 3 by omega]
    have e := hpos _ (mem _ hp _ (hg _ hp).1 _ hr)
    rw [Nat.div_add_mod] at e
    rw [spStartR, spStart, show spDigitWord (σ ∘ spRen) = spK σ from rfl, spStartAt_eq_cwCell σ hi,
      hc, e]
  refine ⟨ρ .leaf, hret.symm, fun i => Nat.mod_lt _ (by norm_num), ?_, ?_, ?_⟩
  · exact (Finset.sum_congr rfl fun i hi => hdig i (Finset.mem_range.mp hi)).trans hsum
  · rw [h3, henc, spX_congr hdig]
  · rw [hleaf, h0, h1, h2]
    exact spLeafCell_congr (fun i hi => (hdig i hi).symm) fun i hi => (hst i hi).symm

end
end LeanVM.Guest.B1.Sig
