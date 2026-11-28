/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.OsCur

  `OsCurSpec`: `open_stacked` returns its cursor argument times `g^(osWordsLen c)`, past the words its contract reads.
-/

module

public import LeanVM.Guest.CoreMode.Fn.verify_sub.StreamQ
public import LeanVM.Guest.B1.Whir.Sound

/-!
# `open_stacked`'s returned cursor

`open_stacked_sound_cur` (`B1/Whir/Sound.lean`): at `open_stacked_sound_w_Spec`'s hypotheses the sixth return is the
cursor argument times `g^k`, `k = osWordsLen (osCfgR m (r - 1))`, the stream words the size `m` reads at the rate `r`.
`osWords_room`: at every size and rate, `osRoom[m] ≤ k < 2^32`. So `osCurSpec : OsCurSpec`, and
`vsStreamQ : VsStreamQ al D` for every `al`, `D`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open LeanVM.Guest.CoreMode.Own.verify_sub (osRoom)

@[expose] public section

set_option maxRecDepth 100000 in
/-- At every size `m` and rate index `ri`, the words `open_stacked` reads cover `osRoom[m]` and stay below `2^32`. -/
theorem osWords_room : ∀ m < 15, ∀ ri < 4,
    osRoom.getD m 0 ≤ osWordsLen (osCfgR m ri) ∧ osWordsLen (osCfgR m ri) < 2 ^ 32 := by
  decide +kernel

/-- **`open_stacked`'s returned cursor**: its cursor argument times `g^k`, `osRoom[μ - 16] ≤ k < 2^32`. -/
theorem osCurSpec : OsCurSpec := by
  unfold OsCurSpec
  intro κ hκ hwb L C V hU hle μ r h1 h2 h3 h4 root fs target root0 root1 cur tabs rets fn σ hfs hroot hwt hfind
    hp hh
  have e := (open_stacked_sound_cur hκ hwb L C V hU hle μ r h1 h2 h3 h4 root fs target root0 root1 cur tabs rets fn σ
    hfs hroot hwt hfind hp hh).2
  obtain ⟨a, b⟩ := osWords_room (μ - minOpenLog) (by simp only [minOpenLog] at *; omega) (r - 1) (by omega)
  exact ⟨_, b, a, e⟩

/-- **`verify_sub`'s stream reads lie before its end**, at every allocator flag and reference. -/
theorem vsStreamQ {al : String → Bool} {D : Ref → RefD} : VsStreamQ al D :=
  vsStreamQ_of osCurSpec

end

end LeanVM.Guest.EndExec
