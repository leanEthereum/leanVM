/-
  LeanVM.Guest.B1.VsC.IndexMleC

  `index_mle__L{w}` completes, layout-free.
-/

module

public import LeanVM.Guest.B1.VsC.Fwd
public import LeanVM.Guest.B1.KeccakGkr.IndexMle
import LeanVM.Guest.CoreRef

/-!
# `index_mle`, complete

`index_mle__L{w}(zeta)` loads `w` words at `zeta` and multiplies their factors; its body is pure
(`pureChecks`, by the kernel). `index_mle_complete`: at every width `19 ≤ w ≤ 24`, on every memory
holding `zs` at `zeta`, the call returns `[indexMle zs]` (the soundness stream's `IndexMleOut` pins
it), popping nothing, exact.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.KeccakGkr
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- What `index_mle__L{w}`'s completeness gives. -/
def IndexMleComplete (kd w : ℕ) (name : String) : Prop :=
  ∀ (zeta : E) (zs : List E), zs.length = w →
    CallCompletes0 kd name [zeta] [indexMle zs] (fun rd ↦ ReadsAt rd zeta zs) PostQuiet

theorem im_complete {kd w : ℕ} {name : String} {f : Fn} (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0]) (hck : pureChecks 1 [(0, w)] f.body = true)
    (hs : ∀ rd args rets, coreProgram.Rel rd name args rets → IndexMleOut w rd args rets) :
    IndexMleComplete kd w name := by
  intro zeta zs hzs
  refine callCompletes0_pure [(0, w)] hfind (by rw [hparams]; rfl) hck (by simp) ?_ ?_
  · rintro rd - hz q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact ⟨zs, by simp [hzs], hz⟩
  · rintro rd - hz rets' hR
    have h := hs rd _ _ hR
    rcases rets' with _ | ⟨v, _ | ⟨v', t⟩⟩
    · simp [IndexMleOut] at h
    · obtain ⟨zs', hl, hr, hv⟩ := h
      rw [hv, readsAt_eq hr hz (by rw [hl, hzs])]
    · simp [IndexMleOut] at h

set_option maxRecDepth 100000 in
theorem index_mle_L19_complete (kd : ℕ) : IndexMleComplete kd 19 (imSpecNames.getD 0 "") :=
  im_complete (coreProgram_find?_at (j := idx% «index_mle__L19») rfl) rfl (by decide +kernel)
    index_mle_L19_sound

set_option maxRecDepth 100000 in
theorem index_mle_L20_complete (kd : ℕ) : IndexMleComplete kd 20 (imSpecNames.getD 1 "") :=
  im_complete (coreProgram_find?_at (j := idx% «index_mle__L20») rfl) rfl (by decide +kernel)
    index_mle_L20_sound

set_option maxRecDepth 100000 in
theorem index_mle_L21_complete (kd : ℕ) : IndexMleComplete kd 21 (imSpecNames.getD 2 "") :=
  im_complete (coreProgram_find?_at (j := idx% «index_mle__L21») rfl) rfl (by decide +kernel)
    index_mle_L21_sound

set_option maxRecDepth 100000 in
theorem index_mle_L22_complete (kd : ℕ) : IndexMleComplete kd 22 (imSpecNames.getD 3 "") :=
  im_complete (coreProgram_find?_at (j := idx% «index_mle__L22») rfl) rfl (by decide +kernel)
    index_mle_L22_sound

set_option maxRecDepth 100000 in
theorem index_mle_L23_complete (kd : ℕ) : IndexMleComplete kd 23 (imSpecNames.getD 4 "") :=
  im_complete (coreProgram_find?_at (j := idx% «index_mle__L23») rfl) rfl (by decide +kernel)
    index_mle_L23_sound

set_option maxRecDepth 100000 in
theorem index_mle_L24_complete (kd : ℕ) : IndexMleComplete kd 24 (imSpecNames.getD 5 "") :=
  im_complete (coreProgram_find?_at (j := idx% «index_mle__L24») rfl) rfl (by decide +kernel)
    index_mle_L24_sound

/-- **Every `index_mle__L{w}` completes**, `19 ≤ w ≤ 24`. -/
theorem index_mle_complete (kd : ℕ) : ∀ w, 19 ≤ w → w ≤ 24 →
    IndexMleComplete kd w (imSpecNames.getD (w - 19) "") := by
  intro w h1 h2
  interval_cases w
  exacts [index_mle_L19_complete kd, index_mle_L20_complete kd, index_mle_L21_complete kd,
    index_mle_L22_complete kd, index_mle_L23_complete kd, index_mle_L24_complete kd]

end
end LeanVM.Guest.B1.VsC
