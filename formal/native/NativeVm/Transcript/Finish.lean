module

public import NativeVm.Transcript.Commit

/-!
# `runProof`'s check

`finish_spec`: from a state that simulates `st`, `finish` ends normally exactly when the stream and
the openings are consumed (`runProof`'s `s.stream.isEmpty && s.openings.isEmpty`), writing no word.
-/

@[expose] public section

namespace NativeVm.Transcript

open Native LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile

variable {env : Env} {st : VerifierProgramState} {s : QState} {P Q : QState → Prop}

theorem drop_isEmpty {α : Type} {l : List α} {c : Nat} (hc : c ≤ l.length) :
    (l.drop c).isEmpty = true ↔ c = l.length := by
  rw [List.isEmpty_iff, List.drop_eq_nil_iff]
  omega

/-- **`runProof`'s check**: the stream and the openings consumed. -/
theorem finish_spec (h : SimState env st s) :
    WP finish s (fun s' ↦ (st.stream.isEmpty && st.openings.isEmpty) = true ∧ s'.mem = s.mem ∧
      RegsFrame [.rax, .rcx, .rdx, .r11] s s')
      (fun _ ↦ (st.stream.isEmpty && st.openings.isEmpty) = false) := by
  obtain ⟨c, hc, hcw, hst⟩ := h.cursor
  obtain ⟨p, hp, hpw, -, hop⟩ := h.phase
  have hL := h.layout
  obtain ⟨hsl, h0, -⟩ := h.decoded
  have hfit := hL.fitDec
  have hdw := decodedWords_eq env.L
  have hsl' : env.proof.stream.length ≤ env.L / 16 := hsl
  have hfitn : 8 * decodedWords env.L ≤ 2 ^ 64 := by unfold Fits at hfit; omega
  have hpl : env.proof.openings.length ≤ 8 := h.decoded.2.2.2.1
  unfold finish
  refine wp_load (eval_cw h.rdi _) hL.workPtr ?_
  refine wp_load (eval_cw (by reg_simp; exact h.rdi) _) hL.decPtr ?_
  refine wp_load (work_reg (env := env) (by reg_simp) _) hcw ?_
  refine wp_load (by rw [eval_at0]; reg_simp; exact (wd_zero _).symm) h0 ?_
  by_cases hce : c = env.proof.stream.length
  · refine wp_failIf ?_ ?_
    · rw [cond_ne, rhs_reg]
      reg_simp
      rw [hce]
      exact bne_self_eq_false _
    refine wp_load (work_reg (env := env) (by reg_simp) _) hpw ?_
    refine wp_load (work_reg (env := env) (by reg_simp) _) h.phaseCount ?_
    by_cases hpe : p = env.proof.openings.length
    · refine wp_failIf ?_ (wp_done ⟨?_, rfl, by rf_tac⟩)
      · rw [cond_ne, rhs_reg]
        reg_simp
        rw [hpe]
        exact bne_self_eq_false _
      · rw [hst, hop, (drop_isEmpty hc).mpr hce, (drop_isEmpty hp).mpr hpe]
        rfl
    · refine wp_failIf_fail ?_ ?_
      · rw [cond_ne, rhs_reg]
        reg_simp
        rw [bne_iff_ne, ne_eq, toUInt64_inj (by omega) (by omega)]
        exact hpe
      · rw [hop, Bool.and_eq_false_iff]
        right
        rw [Bool.eq_false_iff, ne_eq, drop_isEmpty hp]
        exact hpe
  · refine wp_failIf_fail ?_ ?_
    · rw [cond_ne, rhs_reg]
      reg_simp
      rw [bne_iff_ne, ne_eq, toUInt64_inj (by omega) (by omega)]
      exact hce
    · rw [hst, Bool.and_eq_false_iff]
      left
      rw [Bool.eq_false_iff, ne_eq, drop_isEmpty hc]
      exact hce

end NativeVm.Transcript
