/-
  LeanVM.Guest.B1.Whir.CRoundsA

  The fold rounds as blocks at fixed values, their calls at their exact arguments.
-/

module

public import LeanVM.Guest.B1.Whir.CAtoms

/-!
# The fold rounds at fixed values

`RoundsC C fch coefs tabs n i fs cl cur xs`: the `n` rounds' `opening_round` calls from `i` hold
of `C` at their exact arguments and returns (the round's capacity, cursor, claim, `γ` and
`α, β, θ` slots); `osRounds_completeA`: the rounds as a block at fixed values (`BlkA`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

/-- The rounds' calls at their exact arguments. -/
def RoundsC (C : CallRel) (fch coefs tabs : E) : ℕ → ℕ → List E → E → E → List E → Prop
  | 0, _, _, _, _, _ => True
  | n + 1, i, fs, cl, cur, xs =>
    C "opening_round" (fs ++ [cur, cl, tabs, fch * gen ^ i, coefs * gen ^ (3 * i)])
        (roundRets fs cur cl (xs.take 7)) ∧
      RoundsC C fch coefs tabs n (i + 1) ((roundRets fs 0 cl (xs.take 7)).take 5)
        ((roundRets fs 0 cl (xs.take 7)).getD 6 0) (cur * gen ^ 7) (xs.drop 7)

/-- The state after a round lies below its next free value. -/
theorem osRound_below (P : List (ℕ × ℕ × ℕ)) (i : ℕ) (st : OsSt) (hb : st.Below) (hk : 36 ≤ st.k) :
    (osRound P i st).2.Below := by
  set cu := osCurS st
  set fp := osMatS P osFch i cu.2.2
  set cp := osMatS P osCoefs (3 * i) fp.2.2
  have k1 : st.k ≤ cu.2.2.k := osCurS_k st
  have k2 : cu.2.2.k ≤ fp.2.2.k := osMatS_k _ _ _ _
  have k3 : fp.2.2.k ≤ cp.2.2.k := osMatS_k _ _ _ _
  have hmb1 : MatsBelow cu.2.2.k cu.2.2.mats := show MatsBelow cu.2.2.k st.mats from fun m hm ↦ by
    obtain ⟨a, b, d⟩ := hb.mats m hm; exact ⟨by omega, by omega, by omega⟩
  have hmb3 : MatsBelow cp.2.2.k cp.2.2.mats :=
    osMatS_below (osMatS_below hmb1 (show 19 < cu.2.2.k by omega)) (show 21 < fp.2.2.k by omega)
  have ek : (osRound P i st).2.k = cp.2.2.k + 7 := rfl
  refine ⟨fun f hf ↦ ?_, ?_, ?_, fun m hm ↦ ?_⟩
  · have hf' : f ∈ [cp.2.2.k, cp.2.2.k + 1, cp.2.2.k + 2, cp.2.2.k + 3, cp.2.2.k + 4] := hf
    rw [ek]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
    rcases hf' with rfl | rfl | rfl | rfl | rfl <;> omega
  · show cp.2.2.k + 5 < cp.2.2.k + 7; omega
  · show cp.2.2.k + 6 < cp.2.2.k + 7; omega
  · obtain ⟨a, b, d⟩ := hmb3 m hm; rw [ek]; exact ⟨by omega, by omega, by omega⟩

/-- **`n` rounds as a block at fixed values.** -/
theorem osRounds_completeA {P : List (ℕ × ℕ × ℕ)} :
    ∀ (n i : ℕ) (st : OsSt) (σ : Val) (xs : List E), st.co < u128Bound → 3 * (i + n) < u128Bound →
      st.Below → (∀ C rd, H C rd → MatsOk σ st.mats) → 36 ≤ st.k → st.fs.length = 5 →
      (∀ C rd, H C rd → RoundsC C (σ (.n osFch)) (σ (.n osCoefs)) (σ (.n osTabs)) n i (st.fsv σ)
        (σ (.n st.claim)) (st.cur σ) xs) →
      BlkA H σ st.k (osRounds P i n st).2.k (osRounds P i n st).1
        (fun σ' ↦ RoundsOut σ σ' st (osRounds P i n st).2
          (roundsTr n (st.fsv σ) (σ (.n st.claim)) xs) n ∧ AgreeBelow st.k σ σ') := by
  intro n
  induction n with
  | zero =>
    intro i st σ xs hco _ hb hm _ hfs _
    rw [show osRounds P i 0 st = ([], st) from rfl]
    refine ⟨fun _ ↦ 0, fun C rd hH ↦ BlkF.nil fun σ' ha ↦ ⟨?_, ha⟩⟩
    obtain ⟨e1, e2, e3, e4⟩ := OsSt.agree hb ha
    exact ⟨by rw [e2]; rfl, by rw [e4]; simp, e3, hfs, hco, hb,
      matsOk_agree (hm C rd hH) hb.mats fun i hi ↦ ha i hi, rfl, le_rfl⟩
  | succ n ih =>
    intro i st σ xs hco hi hb hm hk hfs hR
    set w := xs.take 7 with hw
    have hA : BlkA H σ st.k (osRound P i st).2.k (osRound P i st).1
        (fun σ' ↦ RoundOut σ σ' st (osRound P i st).2 w ∧ AgreeBelow st.k σ σ') :=
      BlkA.ofF (osRoundF P i st w σ) fun C rd hH ↦
        osRound_complete σ w hco (by omega) hb (hm C rd hH) hk (by
          have := (hR C rd hH).1
          simpa [OsSt.cur] using this)
    set st1 := (osRound P i st).2 with hst1
    have hk1 : st.k ≤ st1.k := osRound_k P i st
    have hk2 : st1.k ≤ (osRounds P (i + 1) n st1).2.k := osRounds_k P n (i + 1) st1
    have e : osRounds P i (n + 1) st = ((osRound P i st).1 ++ (osRounds P (i + 1) n st1).1,
        (osRounds P (i + 1) n st1).2) := rfl
    rw [e]
    set fsv := st.fsv σ with hfsv
    set cl := σ (.n st.claim) with hcl
    have hRt : roundsTr (n + 1) fsv cl xs =
        roundsTr n ((roundRets fsv 0 cl w).take 5) ((roundRets fsv 0 cl w).getD 6 0) (xs.drop 7) :=
      rfl
    refine BlkA.mono (BlkA.seq hk1 hk2 hA fun σ1 ha1 ho1 ↦ ?_) fun σ' ⟨⟨_, ha'⟩, ho⟩ ↦ ⟨ho, ha'⟩
    have sb : st1.Below := osRound_below P i st hb hk
    have hih := ih (i + 1) st1 σ1 (xs.drop 7) (by show 0 < u128Bound; unfold u128Bound; positivity)
      (by omega) sb (fun C rd hH ↦ (ho1 C rd hH).1.mats) (le_trans hk hk1) rfl fun C rd hH ↦ by
        obtain ⟨ro, ha1'⟩ := ho1 C rd hH
        have ef : st1.fsv σ1 = (roundRets fsv 0 cl w).take 5 := by
          have := congrArg Fs.cap ro.F
          simp only [OsSt.F, roundF] at this
          rw [roundRets_take _ _ 0] at this
          exact this
        have ec : σ1 (.n st1.claim) = (roundRets fsv 0 cl w).getD 6 0 := by
          rw [ro.claim, roundRets_claim _ _ 0]
        rw [ef, ec, ro.cur, ha1 osFch (by show 19 < st.k; omega), ha1 osCoefs (by show 21 < st.k; omega),
          ha1 osTabs (by show 9 < st.k; omega)]
        exact (hR C rd hH).2
    refine BlkA.monoH hih fun C rd hH σ' ha ⟨ho, _⟩ ↦ ?_
    obtain ⟨ro, _⟩ := ho1 C rd hH
    have ef : st1.fsv σ1 = (roundRets fsv 0 cl w).take 5 := by
      have := congrArg Fs.cap ro.F
      simp only [OsSt.F, roundF] at this
      rw [roundRets_take _ _ 0] at this
      exact this
    have ec : σ1 (.n st1.claim) = (roundRets fsv 0 cl w).getD 6 0 := by
      rw [ro.claim, roundRets_claim _ _ 0]
    rw [ef, ec, ← hRt] at ho
    refine ⟨ho.F, ?_, ho.claim, ho.fs, ho.co, ho.below, ho.mats, by rw [ho.pad, ro.pad],
      le_trans hk1 ho.k⟩
    rw [ho.cur, ro.cur, mul_assoc, ← pow_add]
    ring_nf

end
end LeanVM.Guest.B1.Whir
