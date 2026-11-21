module

public import LeanVM.Guest.Mode.SoundStep

/-!
# Words an instruction's immediates name

`immNz_ne`, `ofBits_ne_zero_of`, `ofK_gpow_ne_zero`: the nonzero words an instruction's immediates
name.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

theorem PowTree.find_ok' {t : Exec.PowTree} (ht : t.Ok) {k e : ℕ} (h : t.find k = some e) :
    K.ofBits k = addressOfIndex e := by
  induction t with
  | leaf => exact absurd h (by simp [Exec.PowTree.find])
  | node k' e' l r ihl ihr =>
    have hf : (Exec.PowTree.node k' e' l r).find k =
        (bif k == k' then some e' else bif Nat.blt k k' then l.find k else r.find k) := rfl
    rw [hf] at h
    simp only [Bool.cond_eq_ite, beq_iff_eq] at h
    split_ifs at h with h1 h2
    · subst h1
      obtain rfl := Option.some.inj h
      exact ht.1
    · exact ihl ht.2.1 h
    · exact ihr ht.2.2 h

theorem imm_of_ofBits' {k : ℕ} {a : K} (h : K.ofBits k = a) :
    OffsetInstruction.immediateWord k 0 = ofK a := by
  rw [OffsetInstruction.immediateWord, h, ofK_eq_ofLimbs]
  rfl

theorem ofK_gpow_ne_zero (e : ℕ) : ofK (g ^ e) ≠ 0 :=
  (map_ne_zero (algebraMap K E)).mpr (pow_ne_zero _ g_ne_zero)

theorem ofBits_ne_zero_of {n : ℕ} (h0 : n ≠ 0) (hn : n < 2 ^ 64) : K.ofBits n ≠ 0 := fun h ↦ by
  have h' : K.ofBits n = K.ofBits 0 := h.trans (by decide +kernel)
  have := congrArg (fun z : K ↦ z.toBitVec.toNat) h'
  simp only [K.ofBits, BF64.toBitVec_ofBitVec, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt hn] at this
  exact h0 (by simpa using this)

theorem immNz_ne {k0 k1 : ℕ} (h : immNz k0 k1 = true) : OffsetInstruction.immediateWord k0 k1 ≠ 0 := by
  intro hz
  have h0 := congrArg (fun x : E ↦ x.limb 0) hz
  have h1 := congrArg (fun x : E ↦ x.limb 1) hz
  simp only [OffsetInstruction.immediateWord, limb_ofLimbs, limb_zero] at h0 h1
  simp only [immNz, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  rcases h with ⟨a, b⟩ | ⟨a, b⟩
  · exact ofBits_ne_zero_of a b (by simpa using h0)
  · exact ofBits_ne_zero_of a b (by simpa using h1)

end

end LeanVM.Guest.Mode
