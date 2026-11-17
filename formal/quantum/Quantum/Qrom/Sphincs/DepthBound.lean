module

public import Quantum.Qrom.Sphincs.Security

@[expose] public section

/-!
# The depth-aware leanSPHINCS QROM bound

Security's bound for an adversary making `q` calls of `H` in `d` rounds of parallel calls, with
`d' = min d q`: the two Grover-type terms change, every other term is kept.

* `advBarQD q d = √(6 · epsBarQ · d' · q)` replaces `advBarQ q = √(6 · epsBarQ · q²)` (the event
  bound graded by rounds, averaged over the stream: linear in `epsBarQ`);
* `hybTermQD q d = √(4 · d' · q · κ) + √(clsCapQ · κ)` replaces `hybTermQ q` (the hidden-value
  hybrid graded by rounds).

`sphincsQromDepthBound q d = (√eventTermQD q d + hybTermQD q d)²`.
-/

open scoped ENNReal

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Xmss.Hybrid

/-- **The averaged adversary term with rounds**: `√(6 · epsBarQ · min d q · q)`. -/
noncomputable def advBarQD (q d : ℕ) : ℝ≥0∞ :=
  (6 * epsBarQ * ((min d q : ℕ) : ℝ≥0∞) * q) ^ (2⁻¹ : ℝ)

/-- **The hybrid term with rounds**: `√(4 · min d q · q κ) + √(clsCapQ · κ)`
(`= 2√(q · min d q)·2^-64 + √(clsCapQ · 2^-128)`). -/
noncomputable def hybTermQD (q d : ℕ) : ℝ≥0∞ :=
  (4 * (((min d q : ℕ) : ℝ≥0∞) * (q * kappaQ))) ^ (2⁻¹ : ℝ) + (clsCapQ * kappaQ) ^ (2⁻¹ : ℝ)

/-- **The bound on runtime 2's averaged win, with rounds.** -/
noncomputable def eventTermQD (q d : ℕ) : ℝ≥0∞ :=
  (advBarQD q d + verBarQ + (clsBoundQ q + verLinBarQ) ^ (2⁻¹ : ℝ)) ^ 2 + readErrQ

/-- **The depth-aware leanSPHINCS QROM bound**: `(√eventTermQD q d + hybTermQD q d)²` for `q`
calls of `H` in `d` rounds. -/
noncomputable def sphincsQromDepthBound (q d : ℕ) : ℝ≥0∞ :=
  (eventTermQD q d ^ (2⁻¹ : ℝ) + hybTermQD q d) ^ 2

end Quantum.Qrom.Sphincs

end
