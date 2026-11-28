module

public import NativeRustcX64.Basic
public import NativeRustcX64.Code.Sphincs.Offsets

/-!
# The functions placed in `sphincs_verify`'s program

In `NativeRustcX64.Sphincs.code`, each function sits where `Code/Sphincs/Offsets.lean` says and
each of its labels is the first of its name (`placed_of`: the labels checked by the kernel on the
program, `labelsOk`); their positions are generated scheme-qualified `programOffset` constants.
-/

namespace NativeRustcX64.SphincsVerifyProof

public section

/-- Each label of `F`, from index `i` of the program `P`, is the first of its name in `P`. -/
def labelsOk (P : List Directive) : List Directive → Nat → Bool
  | [], _ => true
  | d :: F, i =>
    (match d with
      | .label l => P.findIdx? (· = .label l) == some i
      | _ => true) && labelsOk P F (i + 1)

theorem labelsOk_spec (P : List Directive) :
    ∀ (F : List Directive) (i : Nat), labelsOk P F i = true → ∀ j (h : j < F.length),
      ∀ l, F[j] = .label l → P.findIdx? (· = .label l) = some (i + j)
  | [], _, _, j, h, _, _ => absurd h (by simp)
  | d :: F, i, hok, 0, _, l, hl => by
    simp only [labelsOk, Bool.and_eq_true] at hok
    simp only [List.getElem_cons_zero] at hl
    subst hl
    simpa using hok.1
  | d :: F, i, hok, j + 1, h, l, hl => by
    simp only [labelsOk, Bool.and_eq_true] at hok
    rw [labelsOk_spec P F (i + 1) hok.2 j (by simpa using h) l (by simpa using hl)]
    congr 1
    omega

/-- **A function placed in the program**, its labels checked. -/
theorem placed_of [Host] (hP : Host.prog = Sphincs.code) {F : List Directive}
    {k : Nat} (hF : F.IsInfixAt Sphincs.code k) (hok : labelsOk Sphincs.code F k = true) :
    Placed F k := by
  refine ⟨hP ▸ hF, fun j h ↦ ?_⟩
  have hs := labelsOk_spec _ _ _ hok j h
  generalize hd : F[j] = d at hs ⊢
  cases d with
  | label l => exact (show Host.prog.findIdx? (· = .label l) = some (k + j) by
      rw [hP]; exact hs l rfl)
  | _ => trivial

set_option Elab.async false

theorem labelsOk_sphincsVerify : labelsOk Sphincs.code Sphincs.SphincsVerify.code NativeRustcX64.Sphincs.SphincsVerify.programOffset = true := by
  decide +kernel
theorem labelsOk_memcpy : labelsOk Sphincs.code Common.Memcpy.code NativeRustcX64.Sphincs.Memcpy.programOffset = true := by decide +kernel
theorem labelsOk_memset : labelsOk Sphincs.code Common.Memset.code NativeRustcX64.Sphincs.Memset.programOffset = true := by decide +kernel
theorem labelsOk_keccakF : labelsOk Sphincs.code Common.KeccakF.code NativeRustcX64.Sphincs.KeccakF.programOffset = true := by
  decide +kernel
theorem labelsOk_update : labelsOk Sphincs.code Common.Update.code NativeRustcX64.Sphincs.Update.programOffset = true := by
  decide +kernel
theorem labelsOk_finalize : labelsOk Sphincs.code Common.Finalize.code NativeRustcX64.Sphincs.Finalize.programOffset = true := by
  decide +kernel

variable [Host] (hP : Host.prog = Sphincs.code)
include hP

/-- **`sphincs_verify` is placed** at its generated program position. -/
theorem placed : Placed Sphincs.SphincsVerify.code NativeRustcX64.Sphincs.SphincsVerify.programOffset :=
  placed_of hP Sphincs.SphincsVerify.code_at labelsOk_sphincsVerify
theorem placed_memcpy : Placed Common.Memcpy.code NativeRustcX64.Sphincs.Memcpy.programOffset :=
  placed_of hP Sphincs.Memcpy.code_at labelsOk_memcpy
theorem placed_memset : Placed Common.Memset.code NativeRustcX64.Sphincs.Memset.programOffset :=
  placed_of hP Sphincs.Memset.code_at labelsOk_memset
theorem placed_keccakF : Placed Common.KeccakF.code NativeRustcX64.Sphincs.KeccakF.programOffset :=
  placed_of hP Sphincs.KeccakF.code_at labelsOk_keccakF
theorem placed_update : Placed Common.Update.code NativeRustcX64.Sphincs.Update.programOffset :=
  placed_of hP Sphincs.Update.code_at labelsOk_update
theorem placed_finalize : Placed Common.Finalize.code NativeRustcX64.Sphincs.Finalize.programOffset :=
  placed_of hP Sphincs.Finalize.code_at labelsOk_finalize

end

end NativeRustcX64.SphincsVerifyProof
