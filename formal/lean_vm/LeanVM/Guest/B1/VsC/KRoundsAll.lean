/-
  LeanVM.Guest.B1.VsC.KRoundsAll

  `layer_rounds__L{n}` completes placed, every specialization `n ≤ 16`.
-/

module

public import LeanVM.Guest.B1.VsC.KRoundsA
import LeanVM.Guest.CoreRef

/-!
# `layer_rounds`, every specialization

Per specialization: its body is the template `lrBody n` and the template's shape facts hold
(`lrOkA n`), one kernel decision each; `layer_rounds_placed` gathers them.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

set_option maxRecDepth 100000 in
theorem lrOkA_0 : lrOkA 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lr_body_0 : Fn.body fn% «layer_rounds__L0» = lrBody 0 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrOkA_1 : lrOkA 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lr_body_1 : Fn.body fn% «layer_rounds__L1» = lrBody 1 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrOkA_2 : lrOkA 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lr_body_2 : Fn.body fn% «layer_rounds__L2» = lrBody 2 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrOkA_3 : lrOkA 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lr_body_3 : Fn.body fn% «layer_rounds__L3» = lrBody 3 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrOkA_4 : lrOkA 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lr_body_4 : Fn.body fn% «layer_rounds__L4» = lrBody 4 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrOkA_5 : lrOkA 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lr_body_5 : Fn.body fn% «layer_rounds__L5» = lrBody 5 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrOkA_6 : lrOkA 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lr_body_6 : Fn.body fn% «layer_rounds__L6» = lrBody 6 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrOkA_7 : lrOkA 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lr_body_7 : Fn.body fn% «layer_rounds__L7» = lrBody 7 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrOkA_8 : lrOkA 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lr_body_8 : Fn.body fn% «layer_rounds__L8» = lrBody 8 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrOkA_9 : lrOkA 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lr_body_9 : Fn.body fn% «layer_rounds__L9» = lrBody 9 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrOkA_10 : lrOkA 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lr_body_10 : Fn.body fn% «layer_rounds__L10» = lrBody 10 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrOkA_11 : lrOkA 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lr_body_11 : Fn.body fn% «layer_rounds__L11» = lrBody 11 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrOkA_12 : lrOkA 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lr_body_12 : Fn.body fn% «layer_rounds__L12» = lrBody 12 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrOkA_13 : lrOkA 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lr_body_13 : Fn.body fn% «layer_rounds__L13» = lrBody 13 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrOkA_14 : lrOkA 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lr_body_14 : Fn.body fn% «layer_rounds__L14» = lrBody 14 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrOkA_15 : lrOkA 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lr_body_15 : Fn.body fn% «layer_rounds__L15» = lrBody 15 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrOkA_16 : lrOkA 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lr_body_16 : Fn.body fn% «layer_rounds__L16» = lrBody 16 := stmtsEqb_sound (by decide +kernel)

/-- **`layer_rounds__L{n}` completes placed**, every `n ≤ 16`: on the coordinates `rs` at
`prev_point`, the messages `ms` at the cursor and the honest challenges at `point`, it returns
`packRunF`'s capacity, the cursor past the `2n` words and the claim, with no words of its own. -/
theorem layer_rounds_placed {k : ℕ} (n : ℕ) (hn : n ≤ 16) {f0 f1 f2 f3 f4 cur v pp pt tabs : E}
    {rs : List E} {ms : List (E × E)} (hrs : rs.length = n) (hms : ms.length = n) {R : ℕ → Prop}
    (hR : KrRegion pp cur pt n R) (fp c0 : ℕ) :
    CallAtA fs al cert k (lrNames.getD n "") [f0, f1, f2, f3, f4, cur, v, pp, pt, tabs]
      (lrRetsW rs ms v cur [f0, f1, f2, f3, f4] n) R (fun _ => False) (fun _ => True)
      (KrPre pp cur pt v [f0, f1, f2, f3, f4] rs ms) PostQuiet (fs (lrNames.getD n "")) fp c0 c0 := by
  interval_cases n
  · exact lr_placed (by decide) (coreProgram_find?_at (j := idx% «layer_rounds__L0») rfl) rfl lr_body_0
      lrOkA_0 hrs hms hR fp c0
  · exact lr_placed (by decide) (coreProgram_find?_at (j := idx% «layer_rounds__L1») rfl) rfl lr_body_1
      lrOkA_1 hrs hms hR fp c0
  · exact lr_placed (by decide) (coreProgram_find?_at (j := idx% «layer_rounds__L2») rfl) rfl lr_body_2
      lrOkA_2 hrs hms hR fp c0
  · exact lr_placed (by decide) (coreProgram_find?_at (j := idx% «layer_rounds__L3») rfl) rfl lr_body_3
      lrOkA_3 hrs hms hR fp c0
  · exact lr_placed (by decide) (coreProgram_find?_at (j := idx% «layer_rounds__L4») rfl) rfl lr_body_4
      lrOkA_4 hrs hms hR fp c0
  · exact lr_placed (by decide) (coreProgram_find?_at (j := idx% «layer_rounds__L5») rfl) rfl lr_body_5
      lrOkA_5 hrs hms hR fp c0
  · exact lr_placed (by decide) (coreProgram_find?_at (j := idx% «layer_rounds__L6») rfl) rfl lr_body_6
      lrOkA_6 hrs hms hR fp c0
  · exact lr_placed (by decide) (coreProgram_find?_at (j := idx% «layer_rounds__L7») rfl) rfl lr_body_7
      lrOkA_7 hrs hms hR fp c0
  · exact lr_placed (by decide) (coreProgram_find?_at (j := idx% «layer_rounds__L8») rfl) rfl lr_body_8
      lrOkA_8 hrs hms hR fp c0
  · exact lr_placed (by decide) (coreProgram_find?_at (j := idx% «layer_rounds__L9») rfl) rfl lr_body_9
      lrOkA_9 hrs hms hR fp c0
  · exact lr_placed (by decide) (coreProgram_find?_at (j := idx% «layer_rounds__L10») rfl) rfl lr_body_10
      lrOkA_10 hrs hms hR fp c0
  · exact lr_placed (by decide) (coreProgram_find?_at (j := idx% «layer_rounds__L11») rfl) rfl lr_body_11
      lrOkA_11 hrs hms hR fp c0
  · exact lr_placed (by decide) (coreProgram_find?_at (j := idx% «layer_rounds__L12») rfl) rfl lr_body_12
      lrOkA_12 hrs hms hR fp c0
  · exact lr_placed (by decide) (coreProgram_find?_at (j := idx% «layer_rounds__L13») rfl) rfl lr_body_13
      lrOkA_13 hrs hms hR fp c0
  · exact lr_placed (by decide) (coreProgram_find?_at (j := idx% «layer_rounds__L14») rfl) rfl lr_body_14
      lrOkA_14 hrs hms hR fp c0
  · exact lr_placed (by decide) (coreProgram_find?_at (j := idx% «layer_rounds__L15») rfl) rfl lr_body_15
      lrOkA_15 hrs hms hR fp c0
  · exact lr_placed (by decide) (coreProgram_find?_at (j := idx% «layer_rounds__L16») rfl) rfl lr_body_16
      lrOkA_16 hrs hms hR fp c0

end
end LeanVM.Guest.B1.VsC
