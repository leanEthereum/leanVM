module

public import NativeVm.Wire.RunPhases
public import NativeVm.Wire.ModelSpec

/-!
# The decoder

`decode` checks the areas' sizes, reads the stream (`stream_ok`) and the phases (`phases_ok`) and
checks that no byte is left: it writes `Proof.fromBytes` of the wire bytes to the decoded area
(`Decoded`), or fails where `Proof.fromBytes` refuses them (`decode_ok`), through the word model
(`decodeM_spec`).
-/

@[expose] public section

namespace NativeVm.Wire

open Native LeanVM.Parameters LeanVM.Protocol.Compile
open Native.SphincsVerifier (toUInt64_add toUInt64_shl toUInt64_shr)

/-- The decoded area's words `D` as `Decoded` reads them. -/
theorem decoded_of {mem : UInt64 → Option UInt64} {a : UInt64} {L : Nat} {D : Nat → UInt64}
    (hm : At mem a (decodedWords L) D) {str : List E} {phs : List PhaseOut}
    (hsl : str.length ≤ maxStream L) (h0 : D 0 = str.length.toUInt64)
    (hs : ∀ i (h : i < str.length), ∀ l < 2, D (1 + 2 * i + l) = (eWords str[i]).getD l 0)
    (hpl : phs.length ≤ wireMaxPhases) (hpe : D (streamEnd L) = phs.length.toUInt64)
    (hat : ∀ k (hk : k < phs.length), PhaseAt D (phaseBase L k) phs[k]) :
    Decoded mem a L (toProof (str, phs)) := by
  have hdn : decodedWords L = phaseBase L wireMaxPhases := rfl
  have hse := streamEnd_lt_dn L
  have hw : ∀ i, i < decodedWords L → mem (a + (8 * i).toUInt64) = some (D i) := hm
  unfold Decoded
  dsimp only [toProof]
  refine ⟨hsl, by rw [hw 0 (by omega), h0], fun i hi l hl ↦ ?_, by simpa using hpl,
    by rw [hw _ hse, hpe, List.length_map], fun k hk ↦ ?_⟩
  · have : 1 + 2 * i + l < decodedWords L := by unfold streamEnd at hse; omega
    rw [hw _ this, hs i hi l hl]
  · simp only [List.length_map] at hk
    simp only [List.getElem_map]
    have hml : wireMaxLeafWords = 64 := rfl
    have hmh : wireMaxHeight = 32 := rfl
    have hop := openingWords_val
    have hb : phaseBase L k + phaseWords ≤ decodedWords L := by
      rw [hdn, ← phaseBase_succ]; exact phaseBase_mono _ (by omega)
    have hpw : 3 ≤ phaseWords := by rw [phaseWords_val]; omega
    obtain ⟨a1, a2, a3, d0, d1, d2, hj⟩ := hat k hk
    refine ⟨_, _, a1, a2, a3, by rw [hw _ (by omega), d0], by rw [hw _ (by omega), d1],
      by rw [hw _ (by omega), d2], fun j hj' ↦ ?_⟩
    obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hj j hj'
    have hjq : j < wireMaxQueries := by omega
    refine ⟨x1, x2, x3, ?_, fun t ht ↦ ?_, fun d hd l hl ↦ ?_⟩
    · have := ob_lt hjq (k := 0) (by omega)
      rw [hw _ (by omega), x4]
    · have := ob_lt hjq (k := 1 + t) (by omega)
      rw [hw _ (by omega), x5 t ht]
    · have := ob_lt hjq (k := 1 + wireMaxLeafWords + 4 * d + l) (by omega)
      rw [hw _ (by omega), x6 d hd l hl]

section Run

variable {e : Env} (P : Pre e)
include P

variable {s : QState} {D W : Nat → UInt64}

/-- The stream, the phases and the check that no byte is left, from the reader's start. -/
theorem decode_tail (hI : Inv e s D W) (hp : s.reg .r15 = (0 : Nat).toUInt64) :
    WP (blk [stream, phases, I (.load .rax (cw cLen)), failIf (.cmp .ne .rax (.reg .r15))]) s
      (fun s' ↦ ∃ π, (decodeM e.B).map toProof = some π ∧ Decoded s'.mem e.da e.L π ∧ Kept e s')
      (fun s' ↦ (decodeM e.B).map toProof = none ∧ Kept e s') := by
  have hL := P.L32
  have hBl := B_length P
  rw [decodeM_eq]
  apply WP.blk_cons
  refine WP.mono (stream_ok P hI hp)
    (fun s1 ⟨str, c1, hstr, hc1, hsl, D1, h1, hd0, hds, hsame1, hr15, _⟩ ↦ ?_)
    (fun s1 ⟨hno, hk⟩ ↦ ⟨by rw [hno]; rfl, hk⟩)
  apply WP.blk_cons
  refine WP.mono (phases_ok P h1 hr15 hc1)
    (fun s2 ⟨phs, c2, hph, hc2, D2, W2, h2, hpl, hpe, hat, hsame2, hr15'⟩ ↦ ?_)
    (fun s2 ⟨hno, hk⟩ ↦ ⟨by simp [hstr, hno], hk⟩)
  refine blk_load_ctx P h2 (eval_cw s2 h2.rdi cLen) (by decide) P.c1 ?_
  apply WP.blk_cons
  have hse := streamEnd_lt_dn e.L
  refine wp_failIf (fun hc ↦ ⟨?_, (h2.setReg (by decide) _).kept⟩) fun hc ↦ WP.blk_nil ?_
  · have hne : c2 ≠ e.L := fun he ↦ by simp [Cond.eval, Rhs.eval, hr15', he] at hc
    simp [hstr, hph, hBl, hne]
  · have heq : c2 = e.L := by
      simp only [Cond.eval, Rhs.eval, QState.setReg_reg, reduceCtorEq, ite_true, ite_false, hr15',
        bne_eq_false_iff_eq] at hc
      exact (Native.SphincsVerifier.toUInt64_inj (by omega) (by omega) hc).symm
    refine ⟨_, by simp [hstr, hph, hBl, heq], decoded_of (h2.setReg (by decide) _).dec hsl ?_ ?_
      hpl hpe hat, (h2.setReg (by decide) _).kept⟩
    · rw [hsame2 0 (by show ¬ streamEnd e.L ≤ 0; unfold streamEnd; omega), hd0]
    · intro i hi l hl
      rw [hsame2 _ (by show ¬ streamEnd e.L ≤ _; unfold streamEnd; omega), hds i hi l hl]

end Run

/-- **The decoder**: `Proof.fromBytes` of the wire bytes in the decoded area, or a failure where it
refuses them; either way `rdi` and every word outside the scratch and the areas kept. -/
theorem decode_ok {e : Env} (P : Pre e) {s : QState} (hr : s.reg .rdi = e.x) (hm : s.mem = e.m0) :
    WP decode s (fun s' ↦ ∃ π, Id.run (Proof.fromBytes (m := Id) LeanVM.Semantics.keccakF1600 e.B) =
        some π ∧ Decoded s'.mem e.da e.L π ∧ Kept e s')
      (fun s' ↦ Id.run (Proof.fromBytes (m := Id) LeanVM.Semantics.keccakF1600 e.B) = none ∧
        Kept e s') := by
  rw [decodeM_spec]
  have hL := P.L32
  have hI := P.inv0 hm hr
  unfold decode
  refine blk_load_ctx P hI (eval_cw s hI.rdi cLen) (by decide) P.c1 ?_
  step; step; step
  obtain ⟨v9, hv9, hdn9⟩ := P.c9
  refine blk_load_ctx P (hI.setReg (d := .rax) (by decide) _)
    (eval_cw _ (by simp [hI.rdi]) cDecN) (by decide) hv9 ?_
  have hdv : decodedWords e.L = 2 * (e.L / 16) + 2 + 8 * phaseWords := by
    unfold decodedWords phaseBase streamEnd maxStream
    rw [show wireMaxPhases = 8 from rfl]
    omega
  have hdl : decodedWords e.L < 2 ^ 64 := by rw [hdv, phaseWords_val]; omega
  have hV : e.L.toUInt64 >>> Nat.toUInt64 4 <<< Nat.toUInt64 1 +
      (Int64.ofNat (2 + 8 * phaseWords)).toUInt64 = (decodedWords e.L).toUInt64 := by
    rw [toUInt64_shr (by norm_num) (by omega), toUInt64_shl (by norm_num) (by omega),
      Int64.toUInt64_ofNat', toUInt64_add, hdv]
    congr 1
    rw [show (2 : Nat) ^ 4 = 16 from rfl, show (2 : Nat) ^ 1 = 2 from rfl]
    omega
  have hdn9' : decodedWords e.L ≤ v9.toNat := hdn9
  apply WP.blk_cons
  refine wp_failIf (fun hc ↦ absurd hc ?_) fun _ ↦ ?_
  · rw [Native.SphincsVerifier.cond_ltu_reg (n := v9.toNat) (K := decodedWords e.L) (by simp)
      (by simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false]; exact hV)
      v9.toNat_lt hdl, decide_eq_true_iff]
    omega
  obtain ⟨v11, hv11, hwk11⟩ := P.c11
  refine blk_load_ctx P ((hI.setReg (d := .rax) (by decide) _).setReg (d := .rbx) (by decide) _)
    (eval_cw _ (by simp [hI.rdi]) cWorkN) (by decide) hv11 ?_
  apply WP.blk_cons
  refine wp_failIf (fun hc ↦ absurd hc ?_) fun _ ↦ ?_
  · rw [Native.SphincsVerifier.cond_ltu_imm (n := v11.toNat) (K := workWords) (by simp)
      Int64.toUInt64_ofNat' v11.toNat_lt (by have := workWords_lt; omega), decide_eq_true_iff]
    omega
  step
  exact decode_tail P ⟨by simp [hI.rdi], hI.out, hI.scr, hI.dec, hI.work⟩ (by simp; rfl)

end NativeVm.Wire
