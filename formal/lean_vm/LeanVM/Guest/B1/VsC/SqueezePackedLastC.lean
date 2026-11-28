/-
  LeanVM.Guest.B1.VsC.SqueezePackedLastC

  `squeeze_packed_last__L{k}` completes, layout-free.
-/

module

public import LeanVM.Guest.B1.VsC.FwdStore
public import LeanVM.Guest.B1.Link.SqueezePacked
import LeanVM.Guest.CoreRef

/-!
# `squeeze_packed_last`, complete

`squeeze_packed_last(rec, end, cells, k)` reads the capacity at `rec`, permutes it `k < 4` times,
storing each permutation's eight rate cells at `cells` and the last capacity at `end`. By
`callCompletes_stores`: on every memory holding the capacity `cap` at `rec`, and at `cells` and
`end` the words its meaning (`MeaningSPL`) gives, on arrays apart, the call returns `0`, popping
nothing, exact.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

/-- The input array of `squeeze_packed_last`: the capacity at `rec`. -/
def splIns (cap : List E) : List (ℕ × List E) := [(0, cap)]

/-- Its output arrays: the cells at `cells`, the last capacity at `end`. -/
def splOuts (k : ℕ) (cap : List E) : List (ℕ × List E) := [(2, (pkSqueeze k cap).1), (1, (pkSqueeze k cap).2)]

/-- What `squeeze_packed_last__L{k}`'s completeness gives. -/
def SqueezePackedLastComplete (kd k : ℕ) (name : String) : Prop :=
  ∀ (rec en cells : E) (cap : List E), cap.length = 5 →
    ArraysApart [rec, en, cells] (shapeOf (splIns cap ++ splOuts k cap)) →
    CallCompletes kd name [rec, en, cells] [0]
      (fun rd ↦ HoldsArrays rd [rec, en, cells] (splIns cap) ∧ HoldsArrays rd [rec, en, cells] (splOuts k cap))
      PostQuiet

theorem spl_complete {kd k : ℕ} {name : String} {f : Fn} (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2]) (hbody : f.body = spLastBody k)
    (hck : storeChecks 3 [(0, 5)] [(2, 8 * k), (1, 5)] f.body = true) :
    SqueezePackedLastComplete kd k name := by
  intro rec en cells cap hcap hap
  have hsh : shapeOf (splIns cap) = [(0, 5)] ∧ shapeOf (splOuts k cap) = [(2, 8 * k), (1, 5)] := by
    simp [shapeOf, splIns, splOuts, hcap, pkSqueeze_length, pkSqueeze_cap_length k cap hcap]
  refine callCompletes_stores (splIns cap) (splOuts k cap) hfind (by rw [hparams]; rfl)
    (by rw [hsh.1, hsh.2]; exact hck)
    (by simp [splIns, splOuts]) (by simp [splIns, splOuts]) hap ?_
  intro rd' hin rets' hR
  obtain ⟨rfl, cap', hl, hr, hc, he⟩ := spl_sound hfind hparams hbody _ _ hR
  have hcap' : cap' = cap := readsAt_eq hr (hin (0, cap) (by simp [splIns])) (by rw [hl, hcap])
  subst hcap'
  refine ⟨fun q hq => ?_, rfl⟩
  simp only [splOuts, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact hc
  · exact he

set_option maxRecDepth 100000 in
theorem squeeze_packed_last_L0_complete (kd : ℕ) : SqueezePackedLastComplete kd 0 "squeeze_packed_last__L0" :=
  spl_complete (coreProgram_find?_at (j := idx% «squeeze_packed_last__L0») rfl) rfl spl0_body (by decide +kernel)

set_option maxRecDepth 100000 in
theorem squeeze_packed_last_L1_complete (kd : ℕ) : SqueezePackedLastComplete kd 1 "squeeze_packed_last__L1" :=
  spl_complete (coreProgram_find?_at (j := idx% «squeeze_packed_last__L1») rfl) rfl spl1_body (by decide +kernel)

set_option maxRecDepth 100000 in
theorem squeeze_packed_last_L2_complete (kd : ℕ) : SqueezePackedLastComplete kd 2 "squeeze_packed_last__L2" :=
  spl_complete (coreProgram_find?_at (j := idx% «squeeze_packed_last__L2») rfl) rfl spl2_body (by decide +kernel)

set_option maxRecDepth 100000 in
theorem squeeze_packed_last_L3_complete (kd : ℕ) : SqueezePackedLastComplete kd 3 "squeeze_packed_last__L3" :=
  spl_complete (coreProgram_find?_at (j := idx% «squeeze_packed_last__L3») rfl) rfl spl3_body (by decide +kernel)

end
end LeanVM.Guest.B1.VsC
