/-
  LeanVM.Guest.Count.StaticW

  The instruction counts of `verify_tables`' and `check_opening_terminal`'s statically bounded
  callees, `__loop9`, `__loop8` and `__loop14`, by name, read off the `W` count certificates
  (`Memory/GuestCntW*`), per opcode at `B2C.ωArm B2C.xmssArmC op`.
-/

module

public import LeanVM.Guest.Memory.GuestCntWX
public import LeanVM.Guest.Memory.GuestCntWM
public import LeanVM.Guest.Memory.GuestCntWS
public import LeanVM.Guest.Memory.GuestCntWD
public import LeanVM.Guest.Memory.GuestCntWJ
public import LeanVM.Guest.Memory.GuestCntWK
public import LeanVM.Guest.Count.Words

/-!
# Counts by name, from the `W` certificates

`kuSB op f` is the constant of `f`'s certificate counting `op`'s instructions, `kuSK op f` a loop
helper's per iteration (`0` otherwise). `kuOkB op j f` (`kuOkK op j f`) checks that core function
`j` is `f` and its certificate a constant (a loop's per iteration, ending at its argument `1`);
then `kuSB_weightLe` (`kuSK_loop`) bounds `f`'s weight.
-/

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest
open LeanVM.Guest.Data

@[expose] public section

/-- The `W` certificates counting `op`'s instructions, by name. -/
noncomputable def kuCert : Opcode → String → Cert
  | .xor => kuxcertOf
  | .mulNative => kumcertOf
  | .setConstant => kuscertOf
  | .deref => kudcertOf
  | .jump => kujcertOf
  | .keccak => kukcertOf

/-- The `W` certificates counting `op`'s instructions, by core index. -/
noncomputable def kuCertJ : Opcode → ℕ → Cert
  | .xor => kuxcertJ
  | .mulNative => kumcertJ
  | .setConstant => kuscertJ
  | .deref => kudcertJ
  | .jump => kujcertJ
  | .keccak => kukcertJ

/-- **The `W` certificates counting `op`'s instructions check** at `B2C.ωArm B2C.xmssArmC op`. -/
theorem ku_checked (op : Opcode) :
    Checked coreProgram false (kuCert op) (B2C.ωArm B2C.xmssArmC op) := by
  cases op
  · exact kux_checked
  · exact kum_checked
  · exact kus_checked
  · exact kud_checked
  · exact kuj_checked
  · exact kuk_checked

theorem kuCert_idx {op : Opcode} {j : ℕ} {f : String} (h : (coreProgram[j]?).map Fn.name = some f) :
    kuCert op f = kuCertJ op j := by
  cases op
  · exact kuxcertOf_of_idx h
  · exact kumcertOf_of_idx h
  · exact kuscertOf_of_idx h
  · exact kudcertOf_of_idx h
  · exact kujcertOf_of_idx h
  · exact kukcertOf_of_idx h

/-- The constant of `f`'s certificate counting `op`'s instructions, `0` if none. -/
noncomputable def kuSB (op : Opcode) (f : String) : ℕ :=
  match kuCert op f with
  | .stat _ b _ => b.c
  | _ => 0

/-- A loop helper's instructions of `op` per iteration, `0` if none. -/
noncomputable def kuSK (op : Opcode) (f : String) : ℕ :=
  match kuCert op f with
  | .loop _ _ b _ => b.c
  | _ => 0

/-- `kuSB` by core index. -/
noncomputable def kuSBJ (op : Opcode) (j : ℕ) : ℕ :=
  match kuCertJ op j with
  | .stat _ b _ => b.c
  | _ => 0

/-- `kuSK` by core index. -/
noncomputable def kuSKJ (op : Opcode) (j : ℕ) : ℕ :=
  match kuCertJ op j with
  | .loop _ _ b _ => b.c
  | _ => 0

theorem kuSB_idx {op : Opcode} {j : ℕ} {f : String} (h : (coreProgram[j]?).map Fn.name = some f) :
    kuSB op f = kuSBJ op j := by
  unfold kuSB kuSBJ; rw [kuCert_idx h]

theorem kuSK_idx {op : Opcode} {j : ℕ} {f : String} (h : (coreProgram[j]?).map Fn.name = some f) :
    kuSK op f = kuSKJ op j := by
  unfold kuSK kuSKJ; rw [kuCert_idx h]

/-- Core function `j` is `f`, its certificate counting `op`'s instructions constant. -/
noncomputable def kuOkB (op : Opcode) (j : ℕ) (f : String) : Bool :=
  decide ((coreProgram[j]?).map Fn.name = some f) && certConstB (kuCertJ op j)

/-- Core function `j` is `f`, its certificate counting `op`'s instructions a loop's, constant per
iteration and ending at its argument `1`. -/
noncomputable def kuOkK (op : Opcode) (j : ℕ) (f : String) : Bool :=
  decide ((coreProgram[j]?).map Fn.name = some f) && certLoopB (kuCertJ op j)

/-- **`f`'s instructions of `op` within `kuSB op f`.** -/
theorem kuSB_weightLe {op : Opcode} {j : ℕ} {f : String} (h : kuOkB op j f = true) :
    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) f fun _ => kuSB op f := by
  simp only [kuOkB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hn, hk⟩ := h
  have hc := kuCert_idx (op := op) hn
  rcases hw : kuCertJ op j with _ | ⟨pre, ⟨B, cs⟩, ks⟩ | _
  · rw [hw] at hk; cases hk
  · rw [hw] at hk
    simp only [certConstB, Bool.and_eq_true, List.isEmpty_iff] at hk
    obtain ⟨rfl, rfl⟩ := hk
    have hf : kuCert op f = .stat [] ⟨B, []⟩ ks := hc.trans hw
    have hB : kuSB op f = B := by unfold kuSB; rw [hf]
    rw [hB]
    exact weightLe_of_stat (ku_checked op) hf
  · rw [hw] at hk; cases hk

/-- **Loop helper `f`'s instructions of `op` within `kuSK op f` per iteration.** -/
theorem kuSK_loop {op : Opcode} {j : ℕ} {f : String} (h : kuOkK op j f = true) :
    LoopWeightLe (B2C.ωArm B2C.xmssArmC op) f (kuSK op f) := by
  simp only [kuOkK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hn, hk⟩ := h
  have hc := kuCert_idx (op := op) hn
  rcases hw : kuCertJ op j with _ | _ | ⟨endc, pre, ⟨K, cs⟩, ks⟩
  · rw [hw] at hk; cases hk
  · rw [hw] at hk; cases hk
  · rw [hw] at hk
    simp only [certLoopB, Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at hk
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hk
    have hf : kuCert op f = .loop none [] ⟨K, []⟩ ks := hc.trans hw
    have hK : kuSK op f = K := by unfold kuSK; rw [hf]
    rw [hK]
    intro rd t args rets a e hn' hv hb ha he hae heo
    have := weight_le_of_loop (ku_checked op) hf hn' hv hb ha he hae heo
      (fun _ h => (List.not_mem_nil h).elim)
    simpa [Aff.eval] using this

end
end LeanVM.Guest.Count
