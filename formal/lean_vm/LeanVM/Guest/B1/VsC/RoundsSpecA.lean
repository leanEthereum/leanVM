/-
  LeanVM.Guest.B1.VsC.RoundsSpecA

  `link_rounds__L{1,6,7}_L0` complete placed.
-/

module

public import LeanVM.Guest.B1.VsC.RoundsMainA
public import LeanVM.Guest.B1.VsC.TerminalA
import LeanVM.Guest.CoreRef

/-!
# `link_rounds` with no grind, placed

The loop's and last arms' hypotheses of `lr_main_placed` with no grind: `lrLoopA0` (from
`lrL_callAtA0`), `lrLastA_placed0` (`k ≥ 1`, from `lrl_placed0`, its cursors located by `CurChain`,
vacuous without it), `lrLastA_copy0` (`k = 0`, the record copied, by `callAtA_leaf0`). Then the three
specializations with no grind: `link_rounds_L1_L0_completeA`, `link_rounds_L6_L0_completeA`,
`link_rounds_L7_L0_completeA`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Guest.Value

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

theorem lrLoopA0 {k nt : ℕ} (hnt : 1 ≤ nt) (hnt' : nt ≤ 32) {name : String} {fn : Fn}
    (hfind : coreProgram.find? name = some fn) (hlp : coreProgram.loop name = true)
    (hparams : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4]) (hbody : fn.body = lrLoopBody nt 0 name)
    (hck : lrLChecks0 nt name = true) : LrLoopA fs al cert k nt 0 name := by
  intro st0 l q cm point tabs R h5 hq hq16 hq0 hRp hRc hRo _ fp c hfc
  have := lrL_callAtA0 (fs := fs) (al := al) (cert := cert) (tabs := tabs) k hnt hnt' hfind hlp hparams hbody hck
    h5 hq hq16 hRp hRc hRo 0 hq0 fp c (by simpa using hfc)
  rw [Nat.sub_zero] at this
  exact this.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun rd h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩)
    (fun _ _ _ h => h)

theorem lrLastA_placed0 {kd nt k : ℕ} (hnt : 1 ≤ nt) (hnt' : nt ≤ 32) (hk0 : k ≠ 0) {name : String} {f : Fn}
    (hfind : coreProgram.find? name = some f) (hlp : coreProgram.loop name = false)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3]) (hbody : f.body = lrLastBody nt 0 k)
    (hck : lrlChecks (lrLastBody nt 0 k) = true) (hleaf : leafB (lrLastBody nt 0 k) = true) :
    LrLastA fs al cert kd nt 0 name k := by
  intro R rp out pts tabs st l h5 hl hrp hout hpts hcur _ fp c
  by_cases hcc : CurChain nt 0 st l
  · refine lrl_placed0 hnt hnt' hk0 hfind hlp hparams hbody hck hleaf rp out pts tabs st l h5 hl
      ⟨hrp, hout, hpts, fun r hr off hoff => ?_⟩ fp c
    have e := curChain_cur st l hcc r (by omega)
    have hR0 : rlen nt 0 = nt + 1 := by simp [rlen]
    obtain ⟨i, hi, hRi⟩ := hcur (r * rlen nt 0 + off) (by
      rw [hR0] at *
      have : (r + 1) * (nt + 1) ≤ k * (nt + 1) := Nat.mul_le_mul_right _ (by omega)
      nlinarith)
    refine ⟨i, ?_, hRi⟩
    rw [e, ← hi, gen_pow_eq_ofK, limb0_mul_ofK, mul_assoc, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add]
  · exact ⟨[], ⟨by simp, List.Pairwise.nil⟩, le_rfl, fun _ _ => trivial,
      fun rd _ _ hP => absurd (roundChain_curChain hP.2.2.1) hcc⟩

theorem lrLastA_copy0 {kd nt bits : ℕ} {name : String} {f : Fn} (hpure : coreProgram.PureIn [name])
    (hfind : coreProgram.find? name = some f) (hlp : coreProgram.loop name = false)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3]) (hL : (atomsOf f.body).all (loadInB [(0, 7), (1, 7)]) = true)
    (hret : (retOf f.body).isSome = true) (h0 : LinkRoundsLastComplete0 kd nt bits 0 name) :
    LrLastA fs al cert kd nt bits name 0 := by
  intro R rp out pts tabs st l h5 hl hrp hout _ _ _ fp c
  refine callAtA_leaf0 hpure List.mem_cons_self hlp hfind (by rw [hparams]; rfl) hL hret (by simp)
    (fun q hq off hoff => ?_) (h0 rp out pts tabs st l h5 hl) fp c
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact hrp off hoff
  · exact hout off hoff

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem lrLChecks0_L1 : lrLChecks0 1 "__loop0_link_rounds__L1_L0" = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lrl_L1_L0_L1_checks :
    lrlChecks (lrLastBody 1 0 1) = true ∧ leafB (lrLastBody 1 0 1) = true := ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem lrl_L1_L0_L2_checks :
    lrlChecks (lrLastBody 1 0 2) = true ∧ leafB (lrLastBody 1 0 2) = true := ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem lrl_L1_L0_L3_checks :
    lrlChecks (lrLastBody 1 0 3) = true ∧ leafB (lrLastBody 1 0 3) = true := ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem lrl_L1_L0_L0_pure : coreProgram.PureIn ["link_rounds_last__L1_L0_L0"] := by
  intro g hg fn hf
  simp only [List.mem_singleton] at hg
  subst hg
  rw [coreProgram_find?_at (j := idx% «link_rounds_last__L1_L0_L0») rfl] at hf
  obtain rfl := Option.some.inj hf
  decide +kernel

set_option maxRecDepth 100000 in
/-- **`link_rounds__L1_L0` completes placed.** -/
theorem link_rounds_L1_L0_completeA (k : ℕ) :
    LinkRoundsCompleteAE fs al cert k 1 0 "link_rounds__L1_L0" (fun c e => FsSmall fs → e ≤ c + 2 ^ 21) := by
  refine lr_main_placed (by norm_num) (coreProgram_find?_at (j := idx% «link_rounds__L1_L0») rfl) (by decide +kernel)
    rfl lrMain_L1_L0_body rfl (coreProgram_find?_at (j := idx% «link_rounds__L1_L0_loop0») rfl) rfl
    (lrLoopA0 (by norm_num) (by norm_num) (coreProgram_find?_at (j := idx% «link_rounds__L1_L0_loop0») rfl)
      (by decide +kernel) rfl lrLoop_L1_L0_body lrLChecks0_L1) fun r hr => ?_
  interval_cases r
  · exact lrLastA_copy0 lrl_L1_L0_L0_pure (coreProgram_find?_at (j := idx% «link_rounds_last__L1_L0_L0») rfl)
      (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (lrl_L1_L0_L0_complete k)
  · exact lrLastA_placed0 (by norm_num) (by norm_num) (by norm_num)
      (coreProgram_find?_at (j := idx% «link_rounds_last__L1_L0_L1») rfl) (by decide +kernel) rfl lrl_L1_L0_L1_body
      lrl_L1_L0_L1_checks.1 lrl_L1_L0_L1_checks.2
  · exact lrLastA_placed0 (by norm_num) (by norm_num) (by norm_num)
      (coreProgram_find?_at (j := idx% «link_rounds_last__L1_L0_L2») rfl) (by decide +kernel) rfl lrl_L1_L0_L2_body
      lrl_L1_L0_L2_checks.1 lrl_L1_L0_L2_checks.2
  · exact lrLastA_placed0 (by norm_num) (by norm_num) (by norm_num)
      (coreProgram_find?_at (j := idx% «link_rounds_last__L1_L0_L3») rfl) (by decide +kernel) rfl lrl_L1_L0_L3_body
      lrl_L1_L0_L3_checks.1 lrl_L1_L0_L3_checks.2

set_option maxRecDepth 100000 in
theorem lrLChecks0_L6 : lrLChecks0 6 "__loop0_link_rounds__L6_L0" = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lrl_L6_L0_L1_checks :
    lrlChecks (lrLastBody 6 0 1) = true ∧ leafB (lrLastBody 6 0 1) = true := ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem lrl_L6_L0_L2_checks :
    lrlChecks (lrLastBody 6 0 2) = true ∧ leafB (lrLastBody 6 0 2) = true := ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem lrl_L6_L0_L3_checks :
    lrlChecks (lrLastBody 6 0 3) = true ∧ leafB (lrLastBody 6 0 3) = true := ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem lrl_L6_L0_L0_pure : coreProgram.PureIn ["link_rounds_last__L6_L0_L0"] := by
  intro g hg fn hf
  simp only [List.mem_singleton] at hg
  subst hg
  rw [coreProgram_find?_at (j := idx% «link_rounds_last__L6_L0_L0») rfl] at hf
  obtain rfl := Option.some.inj hf
  decide +kernel

set_option maxRecDepth 100000 in
/-- **`link_rounds__L6_L0` completes placed.** -/
theorem link_rounds_L6_L0_completeA (k : ℕ) :
    LinkRoundsCompleteAE fs al cert k 6 0 "link_rounds__L6_L0" (fun c e => FsSmall fs → e ≤ c + 2 ^ 21) := by
  refine lr_main_placed (by norm_num) (coreProgram_find?_at (j := idx% «link_rounds__L6_L0») rfl) (by decide +kernel)
    rfl lrMain_L6_L0_body rfl (coreProgram_find?_at (j := idx% «link_rounds__L6_L0_loop0») rfl) rfl
    (lrLoopA0 (by norm_num) (by norm_num) (coreProgram_find?_at (j := idx% «link_rounds__L6_L0_loop0») rfl)
      (by decide +kernel) rfl lrLoop_L6_L0_body lrLChecks0_L6) fun r hr => ?_
  interval_cases r
  · exact lrLastA_copy0 lrl_L6_L0_L0_pure (coreProgram_find?_at (j := idx% «link_rounds_last__L6_L0_L0») rfl)
      (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (lrl_L6_L0_L0_complete k)
  · exact lrLastA_placed0 (by norm_num) (by norm_num) (by norm_num)
      (coreProgram_find?_at (j := idx% «link_rounds_last__L6_L0_L1») rfl) (by decide +kernel) rfl lrl_L6_L0_L1_body
      lrl_L6_L0_L1_checks.1 lrl_L6_L0_L1_checks.2
  · exact lrLastA_placed0 (by norm_num) (by norm_num) (by norm_num)
      (coreProgram_find?_at (j := idx% «link_rounds_last__L6_L0_L2») rfl) (by decide +kernel) rfl lrl_L6_L0_L2_body
      lrl_L6_L0_L2_checks.1 lrl_L6_L0_L2_checks.2
  · exact lrLastA_placed0 (by norm_num) (by norm_num) (by norm_num)
      (coreProgram_find?_at (j := idx% «link_rounds_last__L6_L0_L3») rfl) (by decide +kernel) rfl lrl_L6_L0_L3_body
      lrl_L6_L0_L3_checks.1 lrl_L6_L0_L3_checks.2

set_option maxRecDepth 100000 in
theorem lrLChecks0_L7 : lrLChecks0 7 "__loop0_link_rounds__L7_L0" = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem lrl_L7_L0_L1_checks :
    lrlChecks (lrLastBody 7 0 1) = true ∧ leafB (lrLastBody 7 0 1) = true := ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem lrl_L7_L0_L2_checks :
    lrlChecks (lrLastBody 7 0 2) = true ∧ leafB (lrLastBody 7 0 2) = true := ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem lrl_L7_L0_L3_checks :
    lrlChecks (lrLastBody 7 0 3) = true ∧ leafB (lrLastBody 7 0 3) = true := ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem lrl_L7_L0_L0_pure : coreProgram.PureIn ["link_rounds_last__L7_L0_L0"] := by
  intro g hg fn hf
  simp only [List.mem_singleton] at hg
  subst hg
  rw [coreProgram_find?_at (j := idx% «link_rounds_last__L7_L0_L0») rfl] at hf
  obtain rfl := Option.some.inj hf
  decide +kernel

set_option maxRecDepth 100000 in
/-- **`link_rounds__L7_L0` completes placed.** -/
theorem link_rounds_L7_L0_completeA (k : ℕ) :
    LinkRoundsCompleteAE fs al cert k 7 0 "link_rounds__L7_L0" (fun c e => FsSmall fs → e ≤ c + 2 ^ 21) := by
  refine lr_main_placed (by norm_num) (coreProgram_find?_at (j := idx% «link_rounds__L7_L0») rfl) (by decide +kernel)
    rfl lrMain_L7_L0_body rfl (coreProgram_find?_at (j := idx% «link_rounds__L7_L0_loop0») rfl) rfl
    (lrLoopA0 (by norm_num) (by norm_num) (coreProgram_find?_at (j := idx% «link_rounds__L7_L0_loop0») rfl)
      (by decide +kernel) rfl lrLoop_L7_L0_body lrLChecks0_L7) fun r hr => ?_
  interval_cases r
  · exact lrLastA_copy0 lrl_L7_L0_L0_pure (coreProgram_find?_at (j := idx% «link_rounds_last__L7_L0_L0») rfl)
      (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (lrl_L7_L0_L0_complete k)
  · exact lrLastA_placed0 (by norm_num) (by norm_num) (by norm_num)
      (coreProgram_find?_at (j := idx% «link_rounds_last__L7_L0_L1») rfl) (by decide +kernel) rfl lrl_L7_L0_L1_body
      lrl_L7_L0_L1_checks.1 lrl_L7_L0_L1_checks.2
  · exact lrLastA_placed0 (by norm_num) (by norm_num) (by norm_num)
      (coreProgram_find?_at (j := idx% «link_rounds_last__L7_L0_L2») rfl) (by decide +kernel) rfl lrl_L7_L0_L2_body
      lrl_L7_L0_L2_checks.1 lrl_L7_L0_L2_checks.2
  · exact lrLastA_placed0 (by norm_num) (by norm_num) (by norm_num)
      (coreProgram_find?_at (j := idx% «link_rounds_last__L7_L0_L3») rfl) (by decide +kernel) rfl lrl_L7_L0_L3_body
      lrl_L7_L0_L3_checks.1 lrl_L7_L0_L3_checks.2

set_option maxRecDepth 100000 in
theorem lrl_L8_L1_L0_pure : coreProgram.PureIn ["link_rounds_last__L8_L1_L0"] := by
  intro g hg fn hf
  simp only [List.mem_singleton] at hg
  subst hg
  rw [coreProgram_find?_at (j := idx% «link_rounds_last__L8_L1_L0») rfl] at hf
  obtain rfl := Option.some.inj hf
  decide +kernel

set_option maxRecDepth 100000 in
/-- **`link_rounds__L8_L1` completes placed** from its loop's and its last arms' with rounds (the
record copy is proved). -/
theorem link_rounds_L8_L1_completeA_of (k : ℕ)
    (hloop : LrLoopA fs al cert k 8 1 "__loop0_link_rounds__L8_L1")
    (h1 : LrLastA fs al cert k 8 1 "link_rounds_last__L8_L1_L1" 1)
    (h2 : LrLastA fs al cert k 8 1 "link_rounds_last__L8_L1_L2" 2)
    (h3 : LrLastA fs al cert k 8 1 "link_rounds_last__L8_L1_L3" 3) :
    LinkRoundsCompleteAE fs al cert k 8 1 "link_rounds__L8_L1" (fun c e => FsSmall fs → e ≤ c + 2 ^ 21) := by
  refine lr_main_placed (by norm_num) (coreProgram_find?_at (j := idx% «link_rounds__L8_L1») rfl) (by decide +kernel)
    rfl lrMain_L8_L1_body rfl (coreProgram_find?_at (j := idx% «link_rounds__L8_L1_loop0») rfl) rfl hloop
    fun r hr => ?_
  interval_cases r
  · exact lrLastA_copy0 lrl_L8_L1_L0_pure (coreProgram_find?_at (j := idx% «link_rounds_last__L8_L1_L0») rfl)
      (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (lrl_L8_L1_L0_complete k)
  · exact h1
  · exact h2
  · exact h3

set_option maxRecDepth 100000 in
theorem lrl_L9_L1_L0_pure : coreProgram.PureIn ["link_rounds_last__L9_L1_L0"] := by
  intro g hg fn hf
  simp only [List.mem_singleton] at hg
  subst hg
  rw [coreProgram_find?_at (j := idx% «link_rounds_last__L9_L1_L0») rfl] at hf
  obtain rfl := Option.some.inj hf
  decide +kernel

set_option maxRecDepth 100000 in
/-- **`link_rounds__L9_L1` completes placed** from its loop's and its last arms' with rounds (the
record copy is proved). -/
theorem link_rounds_L9_L1_completeA_of (k : ℕ)
    (hloop : LrLoopA fs al cert k 9 1 "__loop0_link_rounds__L9_L1")
    (h1 : LrLastA fs al cert k 9 1 "link_rounds_last__L9_L1_L1" 1)
    (h2 : LrLastA fs al cert k 9 1 "link_rounds_last__L9_L1_L2" 2)
    (h3 : LrLastA fs al cert k 9 1 "link_rounds_last__L9_L1_L3" 3) :
    LinkRoundsCompleteAE fs al cert k 9 1 "link_rounds__L9_L1" (fun c e => FsSmall fs → e ≤ c + 2 ^ 21) := by
  refine lr_main_placed (by norm_num) (coreProgram_find?_at (j := idx% «link_rounds__L9_L1») rfl) (by decide +kernel)
    rfl lrMain_L9_L1_body rfl (coreProgram_find?_at (j := idx% «link_rounds__L9_L1_loop0») rfl) rfl hloop
    fun r hr => ?_
  interval_cases r
  · exact lrLastA_copy0 lrl_L9_L1_L0_pure (coreProgram_find?_at (j := idx% «link_rounds_last__L9_L1_L0») rfl)
      (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (lrl_L9_L1_L0_complete k)
  · exact h1
  · exact h2
  · exact h3

set_option maxRecDepth 100000 in
theorem lrl_L10_L1_L0_pure : coreProgram.PureIn ["link_rounds_last__L10_L1_L0"] := by
  intro g hg fn hf
  simp only [List.mem_singleton] at hg
  subst hg
  rw [coreProgram_find?_at (j := idx% «link_rounds_last__L10_L1_L0») rfl] at hf
  obtain rfl := Option.some.inj hf
  decide +kernel

set_option maxRecDepth 100000 in
/-- **`link_rounds__L10_L1` completes placed** from its loop's and its last arms' with rounds (the
record copy is proved). -/
theorem link_rounds_L10_L1_completeA_of (k : ℕ)
    (hloop : LrLoopA fs al cert k 10 1 "__loop0_link_rounds__L10_L1")
    (h1 : LrLastA fs al cert k 10 1 "link_rounds_last__L10_L1_L1" 1)
    (h2 : LrLastA fs al cert k 10 1 "link_rounds_last__L10_L1_L2" 2)
    (h3 : LrLastA fs al cert k 10 1 "link_rounds_last__L10_L1_L3" 3) :
    LinkRoundsCompleteAE fs al cert k 10 1 "link_rounds__L10_L1" (fun c e => FsSmall fs → e ≤ c + 2 ^ 21) := by
  refine lr_main_placed (by norm_num) (coreProgram_find?_at (j := idx% «link_rounds__L10_L1») rfl) (by decide +kernel)
    rfl lrMain_L10_L1_body rfl (coreProgram_find?_at (j := idx% «link_rounds__L10_L1_loop0») rfl) rfl hloop
    fun r hr => ?_
  interval_cases r
  · exact lrLastA_copy0 lrl_L10_L1_L0_pure (coreProgram_find?_at (j := idx% «link_rounds_last__L10_L1_L0») rfl)
      (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (lrl_L10_L1_L0_complete k)
  · exact h1
  · exact h2
  · exact h3

/-! ## The link callees -/

/-- **What is left of the link callees**: `link_rounds`' loop helpers and its last arms with rounds
at one bit of grind (`nt = 8, 9, 10`). -/
structure LinkGrindLeft (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) : Prop where
  loop_L8 : LrLoopA fs al cert k 8 1 "__loop0_link_rounds__L8_L1"
  last_L8_L1 : LrLastA fs al cert k 8 1 "link_rounds_last__L8_L1_L1" 1
  last_L8_L2 : LrLastA fs al cert k 8 1 "link_rounds_last__L8_L1_L2" 2
  last_L8_L3 : LrLastA fs al cert k 8 1 "link_rounds_last__L8_L1_L3" 3
  loop_L9 : LrLoopA fs al cert k 9 1 "__loop0_link_rounds__L9_L1"
  last_L9_L1 : LrLastA fs al cert k 9 1 "link_rounds_last__L9_L1_L1" 1
  last_L9_L2 : LrLastA fs al cert k 9 1 "link_rounds_last__L9_L1_L2" 2
  last_L9_L3 : LrLastA fs al cert k 9 1 "link_rounds_last__L9_L1_L3" 3
  loop_L10 : LrLoopA fs al cert k 10 1 "__loop0_link_rounds__L10_L1"
  last_L10_L1 : LrLastA fs al cert k 10 1 "link_rounds_last__L10_L1_L1" 1
  last_L10_L2 : LrLastA fs al cert k 10 1 "link_rounds_last__L10_L1_L2" 2
  last_L10_L3 : LrLastA fs al cert k 10 1 "link_rounds_last__L10_L1_L3" 3

/-- **The link callees `verify_sub` enters complete placed**, from what is left at one bit of grind. -/
theorem vsLinkCalleesA_of (k : ℕ) (h : LinkGrindLeft fs al cert k) : VsLinkCalleesA fs al cert k :=
  ⟨(link_rounds_L1_L0_completeA k).toA, (link_rounds_L6_L0_completeA k).toA, (link_rounds_L7_L0_completeA k).toA,
    (link_rounds_L8_L1_completeA_of k h.loop_L8 h.last_L8_L1 h.last_L8_L2 h.last_L8_L3).toA,
    (link_rounds_L9_L1_completeA_of k h.loop_L9 h.last_L9_L1 h.last_L9_L2 h.last_L9_L3).toA,
    (link_rounds_L10_L1_completeA_of k h.loop_L10 h.last_L10_L1 h.last_L10_L2 h.last_L10_L3).toA,
    (squeeze_packed_completeA k).toA, fun w h1 h2 => (link_terminal_completeA k w h1 h2).toA⟩

/-- **The link callees `verify_sub` enters complete placed, their ends within `2^22` of their
cursors**, from what is left at one bit of grind, every frame below `2^16`. -/
theorem vsLinkCalleesAB_of (k : ℕ) (h : LinkGrindLeft fs al cert k) (hfs : FsSmall fs) :
    VsLinkCalleesAB fs al cert k :=
  have m : ∀ c e : ℕ, (FsSmall fs → e ≤ c + 2 ^ 21) → EndLe c 22 e := fun c e h' _ => by
    have := h' hfs; omega
  ⟨(link_rounds_L1_L0_completeA k).mono m, (link_rounds_L6_L0_completeA k).mono m,
    (link_rounds_L7_L0_completeA k).mono m,
    (link_rounds_L8_L1_completeA_of k h.loop_L8 h.last_L8_L1 h.last_L8_L2 h.last_L8_L3).mono m,
    (link_rounds_L9_L1_completeA_of k h.loop_L9 h.last_L9_L1 h.last_L9_L2 h.last_L9_L3).mono m,
    (link_rounds_L10_L1_completeA_of k h.loop_L10 h.last_L10_L1 h.last_L10_L2 h.last_L10_L3).mono m,
    (squeeze_packed_completeA k).mono m, fun w h1 h2 => (link_terminal_completeA k w h1 h2).mono m⟩

end
end LeanVM.Guest.B1.VsC
