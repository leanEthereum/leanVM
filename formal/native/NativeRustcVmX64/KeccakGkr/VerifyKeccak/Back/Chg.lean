module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.Common

/-!
# `verify_keccak`'s back half: coarser changes (x86-64)

A change within ranges `L`, `O` is one within ranges covering them (`Chg.mono`), checked by
`decide` (`coverL`, `coverO`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.KeccakGkr.SeqZ NativeVm.Model
open NativeRustcVm.Transcript (DecArea TStateAt)
open NativeRustcVm.KeccakGkr (off)

@[expose] public section

/-- Every frame range of `L` within one of `L'`. -/
def coverL (L L' : List (Nat × Nat)) : Bool :=
  L.all fun p ↦ L'.any fun p' ↦ decide (p'.1 ≤ p.1 ∧ p.1 + p.2 ≤ p'.1 + p'.2)

/-- Every region range of `O` within one of `O'` of the same region. -/
def coverO (O O' : List (Nat × Nat × Nat)) : Bool :=
  O.all fun o ↦ O'.any fun o' ↦
    decide (o'.1 = o.1 ∧ o'.2.1 ≤ o.2.1 ∧ o.2.1 + o.2.2 ≤ o'.2.1 + o'.2.2)

end

public section

variable [Labels] {m0 : MachineData} {a : DecArea} {inst : Array EW}

theorem ChgR.mono (c : Ctx a inst m0) {L L' : List (Nat × Nat)} {O O' : List (Nat × Nat × Nat)}
    (hL : okL L = true) (hO : okO O = true) (hL' : okL L' = true) (hO' : okO O' = true)
    (hcL : coverL L L' = true) (hcO : coverO O O' = true) {q : BitVec 64}
    (h : ChgR m0 L O q) : ChgR m0 L' O' q := by
  have := c.sp
  have := c.top
  have := vk_eq
  rcases ChgR.nat c hL hO h with hc | ⟨p, hp, hc⟩ | ⟨o, ho, hc⟩
  · have hK := c.K
    exact .inl (by rw [NativeRustcX64.Sym.inRange_iff (by omega), hK]; omega)
  · have := List.all_eq_true.mp hcL p hp
    obtain ⟨p', hp', hc'⟩ := List.any_eq_true.mp this
    simp only [decide_eq_true_eq] at hc'
    have := okL_mem hL' hp'
    have e := off_fb c (o := p'.1) (by omega)
    exact .inr (.inl ⟨p', hp', by rw [NativeRustcX64.Sym.inRange_iff (by rw [e]; omega), e]; omega⟩)
  · have := List.all_eq_true.mp hcO o ho
    obtain ⟨o', ho', hc'⟩ := List.any_eq_true.mp this
    simp only [decide_eq_true_eq] at hc'
    obtain ⟨h1, h4, hs, -⟩ := okO_mem hO' ho'
    have hw := ob_W c h1 h4
    have e : (off (ob m0 o'.1) o'.2.1).toNat = (ob m0 o'.1).toNat + o'.2.1 :=
      toNat_add_ofNat _ _ (by omega)
    refine .inr (.inr ⟨o', ho', ?_⟩)
    rw [NativeRustcX64.Sym.inRange_iff (by rw [e]; omega), e, hc'.1]
    omega

/-- **A coarser change.** -/
theorem Chg.mono (c : Ctx a inst m0) {d d' : DataMem} {L L' : List (Nat × Nat)}
    {O O' : List (Nat × Nat × Nat)} (h : Chg m0 d d' L O)
    (hL : okL L = true) (hO : okO O = true) (hL' : okL L' = true) (hO' : okO O' = true)
    (hcL : coverL L L' = true) (hcO : coverO O O' = true) : Chg m0 d d' L' O' :=
  fun q hq ↦ h q fun hc ↦ hq (ChgR.mono c hL hO hL' hO' hcL hcO hc)

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
