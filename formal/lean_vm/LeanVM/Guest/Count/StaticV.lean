/-
  LeanVM.Guest.Count.StaticV

  The instruction counts of `verify_sub`'s statically bounded callees and of
  `child_claim_list_digest`'s callees, by name, read off the `V` count certificates
  (`Memory/GuestCntV*`), per opcode at `B2C.ωArm B2C.xmssArmC op`.
-/

module

public import LeanVM.Guest.Memory.GuestCntVX
public import LeanVM.Guest.Memory.GuestCntVM
public import LeanVM.Guest.Memory.GuestCntVS
public import LeanVM.Guest.Memory.GuestCntVD
public import LeanVM.Guest.Memory.GuestCntVJ
public import LeanVM.Guest.Memory.GuestCntVK
public import LeanVM.Guest.Count.Words

/-!
# Counts by name, from the `V` certificates

`kvSB op f` is the constant of `f`'s certificate counting `op`'s instructions, `kvSK op f` a loop
helper's per iteration (`0` otherwise). `kvOkB op j f` (`kvOkK op j f`) checks that core function
`j` is `f` and its certificate a constant (a loop's per iteration, ending at its argument `1`);
then `kvSB_weightLe` (`kvSK_loop`) bounds `f`'s weight. `ωArm_idx`: a frame's weight by its core
index.
-/

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest
open LeanVM.Guest.Data

@[expose] public section

/-- The `V` certificates counting `op`'s instructions, by name. -/
noncomputable def kvCert : Opcode → String → Cert
  | .xor => kvxcertOf
  | .mulNative => kvmcertOf
  | .setConstant => kvscertOf
  | .deref => kvdcertOf
  | .jump => kvjcertOf
  | .keccak => kvkcertOf

/-- The `V` certificates counting `op`'s instructions, by core index. -/
noncomputable def kvCertJ : Opcode → ℕ → Cert
  | .xor => kvxcertJ
  | .mulNative => kvmcertJ
  | .setConstant => kvscertJ
  | .deref => kvdcertJ
  | .jump => kvjcertJ
  | .keccak => kvkcertJ

/-- **The `V` certificates counting `op`'s instructions check** at `B2C.ωArm B2C.xmssArmC op`. -/
theorem kv_checked (op : Opcode) :
    Checked coreProgram false (kvCert op) (B2C.ωArm B2C.xmssArmC op) := by
  cases op
  · exact kvx_checked
  · exact kvm_checked
  · exact kvs_checked
  · exact kvd_checked
  · exact kvj_checked
  · exact kvk_checked

theorem kvCert_idx {op : Opcode} {j : ℕ} {f : String} (h : (coreProgram[j]?).map Fn.name = some f) :
    kvCert op f = kvCertJ op j := by
  cases op
  · exact kvxcertOf_of_idx h
  · exact kvmcertOf_of_idx h
  · exact kvscertOf_of_idx h
  · exact kvdcertOf_of_idx h
  · exact kvjcertOf_of_idx h
  · exact kvkcertOf_of_idx h

/-- The constant of `f`'s certificate counting `op`'s instructions, `0` if none. -/
noncomputable def kvSB (op : Opcode) (f : String) : ℕ :=
  match kvCert op f with
  | .stat _ b _ => b.c
  | _ => 0

/-- A loop helper's instructions of `op` per iteration, `0` if none. -/
noncomputable def kvSK (op : Opcode) (f : String) : ℕ :=
  match kvCert op f with
  | .loop _ _ b _ => b.c
  | _ => 0

/-- `kvSB` by core index. -/
noncomputable def kvSBJ (op : Opcode) (j : ℕ) : ℕ :=
  match kvCertJ op j with
  | .stat _ b _ => b.c
  | _ => 0

/-- `kvSK` by core index. -/
noncomputable def kvSKJ (op : Opcode) (j : ℕ) : ℕ :=
  match kvCertJ op j with
  | .loop _ _ b _ => b.c
  | _ => 0

theorem kvSB_idx {op : Opcode} {j : ℕ} {f : String} (h : (coreProgram[j]?).map Fn.name = some f) :
    kvSB op f = kvSBJ op j := by
  unfold kvSB kvSBJ; rw [kvCert_idx h]

theorem kvSK_idx {op : Opcode} {j : ℕ} {f : String} (h : (coreProgram[j]?).map Fn.name = some f) :
    kvSK op f = kvSKJ op j := by
  unfold kvSK kvSKJ; rw [kvCert_idx h]

/-- Core function `j` is `f`, its certificate counting `op`'s instructions constant. -/
noncomputable def kvOkB (op : Opcode) (j : ℕ) (f : String) : Bool :=
  decide ((coreProgram[j]?).map Fn.name = some f) && certConstB (kvCertJ op j)

/-- Core function `j` is `f`, its certificate counting `op`'s instructions a loop's, constant per
iteration and ending at its argument `1`. -/
noncomputable def kvOkK (op : Opcode) (j : ℕ) (f : String) : Bool :=
  decide ((coreProgram[j]?).map Fn.name = some f) && certLoopB (kvCertJ op j)

/-- **`f`'s instructions of `op` within `kvSB op f`.** -/
theorem kvSB_weightLe {op : Opcode} {j : ℕ} {f : String} (h : kvOkB op j f = true) :
    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) f fun _ => kvSB op f := by
  simp only [kvOkB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hn, hk⟩ := h
  have hc := kvCert_idx (op := op) hn
  rcases hw : kvCertJ op j with _ | ⟨pre, ⟨B, cs⟩, ks⟩ | _
  · rw [hw] at hk; cases hk
  · rw [hw] at hk
    simp only [certConstB, Bool.and_eq_true, List.isEmpty_iff] at hk
    obtain ⟨rfl, rfl⟩ := hk
    have hf : kvCert op f = .stat [] ⟨B, []⟩ ks := hc.trans hw
    have hB : kvSB op f = B := by unfold kvSB; rw [hf]
    rw [hB]
    exact weightLe_of_stat (kv_checked op) hf
  · rw [hw] at hk; cases hk

/-- **Loop helper `f`'s instructions of `op` within `kvSK op f` per iteration.** -/
theorem kvSK_loop {op : Opcode} {j : ℕ} {f : String} (h : kvOkK op j f = true) :
    LoopWeightLe (B2C.ωArm B2C.xmssArmC op) f (kvSK op f) := by
  simp only [kvOkK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hn, hk⟩ := h
  have hc := kvCert_idx (op := op) hn
  rcases hw : kvCertJ op j with _ | _ | ⟨endc, pre, ⟨K, cs⟩, ks⟩
  · rw [hw] at hk; cases hk
  · rw [hw] at hk; cases hk
  · rw [hw] at hk
    simp only [certLoopB, Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at hk
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hk
    have hf : kvCert op f = .loop none [] ⟨K, []⟩ ks := hc.trans hw
    have hK : kvSK op f = K := by unfold kvSK; rw [hf]
    rw [hK]
    intro rd t args rets a e hn' hv hb ha he hae heo
    have := weight_le_of_loop (kv_checked op) hf hn' hv hb ha he hae heo
      (fun _ h => (List.not_mem_nil h).elim)
    simpa [Aff.eval] using this

/-- **A frame's weight by its core index**: `B2C.pathMax`'s entry, but at `__loop2`. -/
theorem ωArm_idx {C : Opcode → ℕ} {op : Opcode} {j : ℕ} {f : String}
    (h : (coreProgram[j]?).map Fn.name = some f) (hx : f ≠ "__loop2") :
    B2C.ωArm C op f = (B2C.plumbOf (j + 1)).pmax.getD (B2C.opIdx op) 0 := by
  rcases hj : coreProgram[j]? with _ | fn
  · rw [hj] at h; cases h
  · rw [hj] at h
    obtain ⟨hlt, hfn⟩ := List.getElem?_eq_some_iff.mp hj
    simp only [Option.map_some, Option.some.injEq] at h
    have hi := kcv_idxOf hlt
    rw [hfn, h] at hi
    unfold B2C.ωArm B2C.pathMax
    rw [hi]
    simp [hx]

end
end LeanVM.Guest.Count
