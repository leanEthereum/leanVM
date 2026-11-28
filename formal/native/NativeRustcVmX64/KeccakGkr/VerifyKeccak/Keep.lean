module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Chg
public import NativeRustcVm.Top.Same

/-!
# Representations a change misses (x86-64)

The `TState` (`Chg.ts`), the column claims (`Chg.cls`), the `KeccakOutW` (`Chg.kout`), bytes of
the read-only regions (`ChgR.ro`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.KeccakGkr.SeqZ NativeVm.Model
open NativeRustcVm.Transcript (DecArea TStateAt)
open NativeRustcVm.KeccakGkr (off)

public section

variable [Labels] {m0 : MachineData} {a : DecArea} {inst : Array EW}

theorem ob_w (c : Ctx a inst m0) {i : Nat} (h1 : 1 ≤ i) (h4 : i ≤ 4) :
    Sep (ob m0 i).toNat (rsz i) a.words.toNat (8 * a.len) := by
  rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
  · exact c.tw
  · exact c.sw
  · exact c.cw
  · exact c.ow

/-- **A read-only range** (apart from the stack and the written regions) misses a change. -/
theorem ChgR.ro (c : Ctx a inst m0) {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)}
    (hL : okL L = true) (hO : okO O = true) {A : BitVec 64} {n : Nat}
    (hst : Sep A.toNat n (stackBelow m0 verifyKeccakStack).toNat (verifyKeccakStack + 8))
    (hreg : ∀ i, 1 ≤ i → i ≤ 4 → Sep (ob m0 i).toNat (rsz i) A.toNat n) {q : BitVec 64}
    (hq : ChgR m0 L O q) : q.toNat < A.toNat ∨ A.toNat + n ≤ q.toNat := by
  have hK := c.K
  have := c.sp
  have := vk_eq
  unfold Sep at hst
  rcases ChgR.nat c hL hO hq with hc | ⟨p, hp, hc⟩ | ⟨o, ho, hc⟩
  · omega
  · have := okL_mem hL hp; omega
  · obtain ⟨h1, h4, hs, -⟩ := okO_mem hO ho
    have := hreg o.1 h1 h4
    unfold Sep at this
    omega

/-- **A region's range a change misses**, as numbers. -/
theorem ChgR.regN (c : Ctx a inst m0) {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)}
    (hL : okL L = true) (hO : okO O = true) {i o n : Nat} (h1 : 1 ≤ i) (h4 : i ≤ 4)
    (hm : missO O i o n = true) (hon : o + n ≤ rsz i) {q : BitVec 64} (hq : ChgR m0 L O q) :
    q.toNat < (ob m0 i).toNat + o ∨ (ob m0 i).toNat + o + n ≤ q.toNat := by
  have hS := ob_S c h1 h4
  have := vk_eq
  have := c.sp
  rcases ChgR.nat c hL hO hq with hc | ⟨p, hp, hc⟩ | ⟨r, hr, hc⟩
  · omega
  · have := okL_mem hL hp; omega
  · obtain ⟨h1', h4', hs, -⟩ := okO_mem hO hr
    have hmr := missO_mem hm hr
    obtain ⟨ri, ro, rn⟩ := r
    simp only at h1' h4' hs hc hmr
    by_cases hij : ri = i
    · subst hij
      omega
    · have := ob_sep c h1 h4 h1' h4' (Ne.symm hij)
      unfold Sep at this
      omega

/-- **The `TState`** stays where a change misses it. -/
theorem Chg.ts (c : Ctx a inst m0) {d d' : DataMem} {L : List (Nat × Nat)}
    {O : List (Nat × Nat × Nat)} (h : Chg m0 d d' L O) (hL : okL L = true) (hO : okO O = true)
    (hm : missO O 1 0 760 = true) (hk : Kept d d') {s' : TState}
    (hts : TStateAt d (reg m0 .rdi) a s') : TStateAt d' (reg m0 .rdi) a s' := by
  refine hts.frame hk (fun q hq ↦ ⟨fun hin ↦ ?_, fun hin ↦ ?_⟩) h
  · have := ChgR.regN c hL hO (i := 1) (by omega) (by omega) hm (by decide) hq
    rw [tsz, NativeRustcVm.inRange_iff c.tW] at hin
    simp only [ob] at this
    omega
  · have := ChgR.ro c hL hO (A := a.words) (n := 8 * a.len) c.wS
      (fun i h1 h4 ↦ ob_w c h1 h4) hq
    rw [NativeRustcVm.inRange_iff c.wW] at hin
    omega

/-- **The column claims** stay where a change misses them. -/
theorem Chg.cls (c : Ctx a inst m0) {d d' : DataMem} {L : List (Nat × Nat)}
    {O : List (Nat × Nat × Nat)} (h : Chg m0 d d' L O) (hL : okL L = true) (hO : okO O = true)
    (hm : missO O 3 0 97288 = true) {xs : Array ColumnClaimW}
    (hc : NativeRustcVm.Layout.ClaimsWAt d (keccakClaims m0) xs) :
    NativeRustcVm.Layout.ClaimsWAt d' (keccakClaims m0) xs := by
  have hs := Chg.regS c h hL hO (i := 3) (o := 0) (n := 97288) (by omega) (by omega) hm (by decide)
  simp only [ob, off, BitVec.add_zero] at hs
  exact NativeRustcVm.Tables.ClaimsWAt.of_same hc hs

/-- **The `KeccakOutW`** stays where a change misses it. -/
theorem Chg.kout (c : Ctx a inst m0) {d d' : DataMem} {L : List (Nat × Nat)}
    {O : List (Nat × Nat × Nat)} (h : Chg m0 d d' L O) (hL : okL L = true) (hO : okO O = true)
    (hm : missO O 4 0 1608 = true) {pt sl : Array EW}
    (hc : NativeRustcVm.KeccakGkr.KeccakOutAt d (keccakOutArg m0) pt sl) :
    NativeRustcVm.KeccakGkr.KeccakOutAt d' (keccakOutArg m0) pt sl := by
  have hs := Chg.regS c h hL hO (i := 4) (o := 0) (n := 1608) (by omega) (by omega) hm (by decide)
  simp only [ob, off, BitVec.add_zero] at hs
  exact NativeRustcVm.Top.KeccakOutAt.of_same hc hs

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
