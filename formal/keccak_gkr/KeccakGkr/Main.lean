import KeccakGkr.Completeness

/-!
# Keccak-f[1600] by GKR

The protocol for Keccak-f[1600] with two segments of twelve rounds, as the VM runs it, over any
finite field `E` of characteristic two holding a word basis `x` (in the VM, `E = GF(2^192)` and
`x` generates `K = GF(2^64)`). The steps have `κ = n + 4` variables.

* `keccak_sound`: the error is `(37 κ + 902) / |E|`, the bound of `§keccak:soundness`;
* `keccak_complete`: an honest prover is always accepted;
* `statement_iff`: the statement is that the main protocol's values are, at its point, the
  multilinear extensions of the lanes of Keccak-f[1600] applied to the committed inputs, and that
  the committed state after twelve rounds is the one Keccak computes.
-/

open OracleComp
open scoped ENNReal

namespace KeccakGkr

variable {E : Type} [Field E] [CharP E 2] [Fintype E] [DecidableEq E] [SampleableType E]
variable {n : ℕ} (Q : Column n) (x : E)

theorem Perm.rounds_add (P : Perm) (r₀ a b : ℕ) (s : State) :
    P.rounds r₀ (a + b) s = P.rounds (r₀ + a) b (P.rounds r₀ a s) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    show P.round (r₀ + (a + b)) (P.rounds r₀ (a + b) s) = _
    rw [ih, ← Nat.add_assoc]
    rfl

/-- Under `Chain`, the second segment's output is Keccak-f[1600] of the committed input. -/
theorem output_eq_keccakF (hc : Chain keccak 12 Q) (i : Cube 4) (p : Cube n) :
    segState keccak 12 Q true 12 i p = keccakF (segInput Q false i p) := by
  have h := hc i p
  simp only [segState, Bool.toNat_false, Bool.toNat_true, mul_zero, mul_one] at h ⊢
  rw [← h, keccakF, show 24 = 12 + 12 from rfl, Perm.rounds_add]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The statement, for Keccak: the committed state after twelve rounds is right, and the main
protocol's values are the output lanes of Keccak-f[1600] on the committed inputs. -/
theorem statement_iff (rl : Fin 4 → E) (rp : Fin n → E) (v : Lane → E) :
    Statement keccak 12 Q x rl rp v ↔ Chain keccak 12 Q ∧
      ∀ ℓ, v ℓ = mleStep (fun i p => word x (keccakF (segInput Q false i p)) ℓ) rl rp := by
  constructor
  · rintro ⟨hc, hv⟩
    refine ⟨hc, fun ℓ => (hv ℓ).trans ?_⟩
    simp only [outEval, output_eq_keccakF Q hc]
  · rintro ⟨hc, hv⟩
    refine ⟨hc, fun ℓ => (hv ℓ).trans ?_⟩
    simp only [outEval, output_eq_keccakF Q hc]

/-- **Soundness for Keccak.** For any committed column and any prover, the verifier ends holding
true claims on the column while the statement is false with probability at most
`(37 κ + 902) / |E|`, `κ = n + 4`. -/
theorem keccak_sound (hx : WordBasis x) :
    (protocol keccak 12 Q x).Sound (fun _ => True) (Fooled keccak 12 Q x)
      ((37 * (n + 4) + 902) / Fintype.card E) :=
  (protocol_sound keccak 12 Q x hx).mono (fun _ h => h) (fun _ h => h) (le_of_eq (by
    congr 1
    push_cast
    ring))

omit [Fintype E] in
/-- **Completeness for Keccak.** If the committed state after twelve rounds is right, an honest
prover is always accepted, with true claims on the column and a true statement. -/
theorem keccak_complete (hc : Chain keccak 12 Q) :
    (protocol keccak 12 Q x).Complete (fun _ => True) (Accepted keccak 12 Q x) :=
  protocol_complete keccak 12 Q x hc

end KeccakGkr
