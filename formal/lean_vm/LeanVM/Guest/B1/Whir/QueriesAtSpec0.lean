/-
  LeanVM.Guest.B1.Whir.QueriesAtSpec0

  `opening_queries` placed at its compiled shapes (part 0 of 2).
-/

module

public import LeanVM.Guest.B1.Whir.QueriesAt

/-!
# The specializations of `opening_queries`, placed

Each shape's `OqCompleteAtB` (and `OqCompleteAt`) from `opening_queries_completeAt`: its body and its loop helper's
equal to their templates, the loop helper's statements checked (`OqPlace`), all by kernel
evaluation; the frame run's fit in the loop helper's frame a hypothesis on the certificate.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L0_L16_L6_L14_L5 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop435" (.n (oqP 0 16 6)) + 4 * 9 ≤ fs "__loop435") :
    OqCompleteAtB fs cert k 0 16 14 5 "opening_queries__L0_L16_L6_L14_L5" fun n => fs "opening_queries__L0_L16_L6_L14_L5" + (n + 1) + (n + 1) * fs "__loop435" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L14_L5") (f := Data.core590) (j := 590) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop435") (f := Data.core981) (j := 981) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 9) (cd := 5)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L0_L16_L6_L14_L5 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop435" (.n (oqP 0 16 6)) + 4 * 9 ≤ fs "__loop435") :
    OqCompleteAt fs cert k 0 16 14 5 "opening_queries__L0_L16_L6_L14_L5" :=
  (oq_completeAtB_L0_L16_L6_L14_L5 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L0_L16_L6_L16_L4 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop460" (.n (oqP 0 16 6)) + 4 * 12 ≤ fs "__loop460") :
    OqCompleteAtB fs cert k 0 16 16 4 "opening_queries__L0_L16_L6_L16_L4" fun n => fs "opening_queries__L0_L16_L6_L16_L4" + (n + 1) + (n + 1) * fs "__loop460" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L16_L4") (f := Data.core707) (j := 707) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop460") (f := Data.core1012) (j := 1012) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 12) (cd := 4)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L0_L16_L6_L16_L4 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop460" (.n (oqP 0 16 6)) + 4 * 12 ≤ fs "__loop460") :
    OqCompleteAt fs cert k 0 16 16 4 "opening_queries__L0_L16_L6_L16_L4" :=
  (oq_completeAtB_L0_L16_L6_L16_L4 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L0_L16_L6_L16_L6 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop432" (.n (oqP 0 16 6)) + 4 * 10 ≤ fs "__loop432") :
    OqCompleteAtB fs cert k 0 16 16 6 "opening_queries__L0_L16_L6_L16_L6" fun n => fs "opening_queries__L0_L16_L6_L16_L6" + (n + 1) + (n + 1) * fs "__loop432" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L16_L6") (f := Data.core584) (j := 584) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop432") (f := Data.core976) (j := 976) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 10) (cd := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L0_L16_L6_L16_L6 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop432" (.n (oqP 0 16 6)) + 4 * 10 ≤ fs "__loop432") :
    OqCompleteAt fs cert k 0 16 16 6 "opening_queries__L0_L16_L6_L16_L6" :=
  (oq_completeAtB_L0_L16_L6_L16_L6 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L0_L16_L6_L17_L5 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop441" (.n (oqP 0 16 6)) + 4 * 12 ≤ fs "__loop441") :
    OqCompleteAtB fs cert k 0 16 17 5 "opening_queries__L0_L16_L6_L17_L5" fun n => fs "opening_queries__L0_L16_L6_L17_L5" + (n + 1) + (n + 1) * fs "__loop441" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L17_L5") (f := Data.core614) (j := 614) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop441") (f := Data.core989) (j := 989) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 12) (cd := 5)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L0_L16_L6_L17_L5 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop441" (.n (oqP 0 16 6)) + 4 * 12 ≤ fs "__loop441") :
    OqCompleteAt fs cert k 0 16 17 5 "opening_queries__L0_L16_L6_L17_L5" :=
  (oq_completeAtB_L0_L16_L6_L17_L5 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L0_L16_L6_L18_L4 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop455" (.n (oqP 0 16 6)) + 4 * 14 ≤ fs "__loop455") :
    OqCompleteAtB fs cert k 0 16 18 4 "opening_queries__L0_L16_L6_L18_L4" fun n => fs "opening_queries__L0_L16_L6_L18_L4" + (n + 1) + (n + 1) * fs "__loop455" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L18_L4") (f := Data.core675) (j := 675) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop455") (f := Data.core1007) (j := 1007) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 14) (cd := 4)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L0_L16_L6_L18_L4 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop455" (.n (oqP 0 16 6)) + 4 * 14 ≤ fs "__loop455") :
    OqCompleteAt fs cert k 0 16 18 4 "opening_queries__L0_L16_L6_L18_L4" :=
  (oq_completeAtB_L0_L16_L6_L18_L4 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L0_L16_L6_L18_L6 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop440" (.n (oqP 0 16 6)) + 4 * 12 ≤ fs "__loop440") :
    OqCompleteAtB fs cert k 0 16 18 6 "opening_queries__L0_L16_L6_L18_L6" fun n => fs "opening_queries__L0_L16_L6_L18_L6" + (n + 1) + (n + 1) * fs "__loop440" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L18_L6") (f := Data.core612) (j := 612) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop440") (f := Data.core988) (j := 988) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 12) (cd := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L0_L16_L6_L18_L6 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop440" (.n (oqP 0 16 6)) + 4 * 12 ≤ fs "__loop440") :
    OqCompleteAt fs cert k 0 16 18 6 "opening_queries__L0_L16_L6_L18_L6" :=
  (oq_completeAtB_L0_L16_L6_L18_L6 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L0_L16_L6_L19_L5 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop447" (.n (oqP 0 16 6)) + 4 * 14 ≤ fs "__loop447") :
    OqCompleteAtB fs cert k 0 16 19 5 "opening_queries__L0_L16_L6_L19_L5" fun n => fs "opening_queries__L0_L16_L6_L19_L5" + (n + 1) + (n + 1) * fs "__loop447" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L19_L5") (f := Data.core644) (j := 644) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop447") (f := Data.core997) (j := 997) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 14) (cd := 5)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L0_L16_L6_L19_L5 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop447" (.n (oqP 0 16 6)) + 4 * 14 ≤ fs "__loop447") :
    OqCompleteAt fs cert k 0 16 19 5 "opening_queries__L0_L16_L6_L19_L5" :=
  (oq_completeAtB_L0_L16_L6_L19_L5 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L0_L16_L6_L20_L4 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop469" (.n (oqP 0 16 6)) + 4 * 16 ≤ fs "__loop469") :
    OqCompleteAtB fs cert k 0 16 20 4 "opening_queries__L0_L16_L6_L20_L4" fun n => fs "opening_queries__L0_L16_L6_L20_L4" + (n + 1) + (n + 1) * fs "__loop469" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L20_L4") (f := Data.core756) (j := 756) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop469") (f := Data.core1022) (j := 1022) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 16) (cd := 4)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L0_L16_L6_L20_L4 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop469" (.n (oqP 0 16 6)) + 4 * 16 ≤ fs "__loop469") :
    OqCompleteAt fs cert k 0 16 20 4 "opening_queries__L0_L16_L6_L20_L4" :=
  (oq_completeAtB_L0_L16_L6_L20_L4 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L0_L16_L6_L20_L6 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop446" (.n (oqP 0 16 6)) + 4 * 14 ≤ fs "__loop446") :
    OqCompleteAtB fs cert k 0 16 20 6 "opening_queries__L0_L16_L6_L20_L6" fun n => fs "opening_queries__L0_L16_L6_L20_L6" + (n + 1) + (n + 1) * fs "__loop446" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L20_L6") (f := Data.core642) (j := 642) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop446") (f := Data.core996) (j := 996) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 14) (cd := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L0_L16_L6_L20_L6 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop446" (.n (oqP 0 16 6)) + 4 * 14 ≤ fs "__loop446") :
    OqCompleteAt fs cert k 0 16 20 6 "opening_queries__L0_L16_L6_L20_L6" :=
  (oq_completeAtB_L0_L16_L6_L20_L6 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L0_L16_L6_L21_L5 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop453" (.n (oqP 0 16 6)) + 4 * 16 ≤ fs "__loop453") :
    OqCompleteAtB fs cert k 0 16 21 5 "opening_queries__L0_L16_L6_L21_L5" fun n => fs "opening_queries__L0_L16_L6_L21_L5" + (n + 1) + (n + 1) * fs "__loop453" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L21_L5") (f := Data.core670) (j := 670) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop453") (f := Data.core1005) (j := 1005) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 16) (cd := 5)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L0_L16_L6_L21_L5 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop453" (.n (oqP 0 16 6)) + 4 * 16 ≤ fs "__loop453") :
    OqCompleteAt fs cert k 0 16 21 5 "opening_queries__L0_L16_L6_L21_L5" :=
  (oq_completeAtB_L0_L16_L6_L21_L5 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L0_L16_L6_L22_L4 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop483" (.n (oqP 0 16 6)) + 4 * 18 ≤ fs "__loop483") :
    OqCompleteAtB fs cert k 0 16 22 4 "opening_queries__L0_L16_L6_L22_L4" fun n => fs "opening_queries__L0_L16_L6_L22_L4" + (n + 1) + (n + 1) * fs "__loop483" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L22_L4") (f := Data.core906) (j := 906) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop483") (f := Data.core1038) (j := 1038) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 18) (cd := 4)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L0_L16_L6_L22_L4 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop483" (.n (oqP 0 16 6)) + 4 * 18 ≤ fs "__loop483") :
    OqCompleteAt fs cert k 0 16 22 4 "opening_queries__L0_L16_L6_L22_L4" :=
  (oq_completeAtB_L0_L16_L6_L22_L4 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L0_L16_L6_L22_L6 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop452" (.n (oqP 0 16 6)) + 4 * 16 ≤ fs "__loop452") :
    OqCompleteAtB fs cert k 0 16 22 6 "opening_queries__L0_L16_L6_L22_L6" fun n => fs "opening_queries__L0_L16_L6_L22_L6" + (n + 1) + (n + 1) * fs "__loop452" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L22_L6") (f := Data.core668) (j := 668) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop452") (f := Data.core1004) (j := 1004) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 16) (cd := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L0_L16_L6_L22_L6 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop452" (.n (oqP 0 16 6)) + 4 * 16 ≤ fs "__loop452") :
    OqCompleteAt fs cert k 0 16 22 6 "opening_queries__L0_L16_L6_L22_L6" :=
  (oq_completeAtB_L0_L16_L6_L22_L6 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L0_L16_L6_L23_L6 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop467" (.n (oqP 0 16 6)) + 4 * 17 ≤ fs "__loop467") :
    OqCompleteAtB fs cert k 0 16 23 6 "opening_queries__L0_L16_L6_L23_L6" fun n => fs "opening_queries__L0_L16_L6_L23_L6" + (n + 1) + (n + 1) * fs "__loop467" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L23_L6") (f := Data.core751) (j := 751) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop467") (f := Data.core1020) (j := 1020) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 17) (cd := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L0_L16_L6_L23_L6 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop467" (.n (oqP 0 16 6)) + 4 * 17 ≤ fs "__loop467") :
    OqCompleteAt fs cert k 0 16 23 6 "opening_queries__L0_L16_L6_L23_L6" :=
  (oq_completeAtB_L0_L16_L6_L23_L6 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L0_L16_L6_L24_L6 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop471" (.n (oqP 0 16 6)) + 4 * 18 ≤ fs "__loop471") :
    OqCompleteAtB fs cert k 0 16 24 6 "opening_queries__L0_L16_L6_L24_L6" fun n => fs "opening_queries__L0_L16_L6_L24_L6" + (n + 1) + (n + 1) * fs "__loop471" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L24_L6") (f := Data.core823) (j := 823) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop471") (f := Data.core1025) (j := 1025) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 18) (cd := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L0_L16_L6_L24_L6 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop471" (.n (oqP 0 16 6)) + 4 * 18 ≤ fs "__loop471") :
    OqCompleteAt fs cert k 0 16 24 6 "opening_queries__L0_L16_L6_L24_L6" :=
  (oq_completeAtB_L0_L16_L6_L24_L6 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L1_L64_L8_L17_L8 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop430" (.n (oqP 1 64 8)) + 4 * 9 ≤ fs "__loop430") :
    OqCompleteAtB fs cert k 1 64 17 8 "opening_queries__L1_L64_L8_L17_L8" fun n => fs "opening_queries__L1_L64_L8_L17_L8" + (n + 1) + (n + 1) * fs "__loop430" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L17_L8") (f := Data.core580) (j := 580) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop430") (f := Data.core973) (j := 973) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 9) (cd := 8)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L1_L64_L8_L17_L8 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop430" (.n (oqP 1 64 8)) + 4 * 9 ≤ fs "__loop430") :
    OqCompleteAt fs cert k 1 64 17 8 "opening_queries__L1_L64_L8_L17_L8" :=
  (oq_completeAtB_L1_L64_L8_L17_L8 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L1_L64_L8_L18_L8 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop436" (.n (oqP 1 64 8)) + 4 * 10 ≤ fs "__loop436") :
    OqCompleteAtB fs cert k 1 64 18 8 "opening_queries__L1_L64_L8_L18_L8" fun n => fs "opening_queries__L1_L64_L8_L18_L8" + (n + 1) + (n + 1) * fs "__loop436" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L18_L8") (f := Data.core597) (j := 597) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop436") (f := Data.core983) (j := 983) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 10) (cd := 8)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L1_L64_L8_L18_L8 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop436" (.n (oqP 1 64 8)) + 4 * 10 ≤ fs "__loop436") :
    OqCompleteAt fs cert k 1 64 18 8 "opening_queries__L1_L64_L8_L18_L8" :=
  (oq_completeAtB_L1_L64_L8_L18_L8 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L1_L64_L8_L19_L8 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop439" (.n (oqP 1 64 8)) + 4 * 11 ≤ fs "__loop439") :
    OqCompleteAtB fs cert k 1 64 19 8 "opening_queries__L1_L64_L8_L19_L8" fun n => fs "opening_queries__L1_L64_L8_L19_L8" + (n + 1) + (n + 1) * fs "__loop439" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L19_L8") (f := Data.core610) (j := 610) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop439") (f := Data.core987) (j := 987) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 11) (cd := 8)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L1_L64_L8_L19_L8 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop439" (.n (oqP 1 64 8)) + 4 * 11 ≤ fs "__loop439") :
    OqCompleteAt fs cert k 1 64 19 8 "opening_queries__L1_L64_L8_L19_L8" :=
  (oq_completeAtB_L1_L64_L8_L19_L8 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L1_L64_L8_L20_L7 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop459" (.n (oqP 1 64 8)) + 4 * 13 ≤ fs "__loop459") :
    OqCompleteAtB fs cert k 1 64 20 7 "opening_queries__L1_L64_L8_L20_L7" fun n => fs "opening_queries__L1_L64_L8_L20_L7" + (n + 1) + (n + 1) * fs "__loop459" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L20_L7") (f := Data.core702) (j := 702) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop459") (f := Data.core1011) (j := 1011) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 13) (cd := 7)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L1_L64_L8_L20_L7 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop459" (.n (oqP 1 64 8)) + 4 * 13 ≤ fs "__loop459") :
    OqCompleteAt fs cert k 1 64 20 7 "opening_queries__L1_L64_L8_L20_L7" :=
  (oq_completeAtB_L1_L64_L8_L20_L7 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L1_L64_L8_L21_L6 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop475" (.n (oqP 1 64 8)) + 4 * 15 ≤ fs "__loop475") :
    OqCompleteAtB fs cert k 1 64 21 6 "opening_queries__L1_L64_L8_L21_L6" fun n => fs "opening_queries__L1_L64_L8_L21_L6" + (n + 1) + (n + 1) * fs "__loop475" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L21_L6") (f := Data.core846) (j := 846) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop475") (f := Data.core1029) (j := 1029) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 15) (cd := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L1_L64_L8_L21_L6 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop475" (.n (oqP 1 64 8)) + 4 * 15 ≤ fs "__loop475") :
    OqCompleteAt fs cert k 1 64 21 6 "opening_queries__L1_L64_L8_L21_L6" :=
  (oq_completeAtB_L1_L64_L8_L21_L6 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L1_L64_L8_L21_L8 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop445" (.n (oqP 1 64 8)) + 4 * 13 ≤ fs "__loop445") :
    OqCompleteAtB fs cert k 1 64 21 8 "opening_queries__L1_L64_L8_L21_L8" fun n => fs "opening_queries__L1_L64_L8_L21_L8" + (n + 1) + (n + 1) * fs "__loop445" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L21_L8") (f := Data.core640) (j := 640) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop445") (f := Data.core995) (j := 995) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 13) (cd := 8)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L1_L64_L8_L21_L8 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop445" (.n (oqP 1 64 8)) + 4 * 13 ≤ fs "__loop445") :
    OqCompleteAt fs cert k 1 64 21 8 "opening_queries__L1_L64_L8_L21_L8" :=
  (oq_completeAtB_L1_L64_L8_L21_L8 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L1_L64_L8_L22_L7 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop463" (.n (oqP 1 64 8)) + 4 * 15 ≤ fs "__loop463") :
    OqCompleteAtB fs cert k 1 64 22 7 "opening_queries__L1_L64_L8_L22_L7" fun n => fs "opening_queries__L1_L64_L8_L22_L7" + (n + 1) + (n + 1) * fs "__loop463" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L22_L7") (f := Data.core726) (j := 726) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop463") (f := Data.core1015) (j := 1015) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 15) (cd := 7)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L1_L64_L8_L22_L7 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop463" (.n (oqP 1 64 8)) + 4 * 15 ≤ fs "__loop463") :
    OqCompleteAt fs cert k 1 64 22 7 "opening_queries__L1_L64_L8_L22_L7" :=
  (oq_completeAtB_L1_L64_L8_L22_L7 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L1_L64_L8_L23_L6 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop477" (.n (oqP 1 64 8)) + 4 * 17 ≤ fs "__loop477") :
    OqCompleteAtB fs cert k 1 64 23 6 "opening_queries__L1_L64_L8_L23_L6" fun n => fs "opening_queries__L1_L64_L8_L23_L6" + (n + 1) + (n + 1) * fs "__loop477" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L23_L6") (f := Data.core866) (j := 866) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop477") (f := Data.core1031) (j := 1031) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 17) (cd := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L1_L64_L8_L23_L6 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop477" (.n (oqP 1 64 8)) + 4 * 17 ≤ fs "__loop477") :
    OqCompleteAt fs cert k 1 64 23 6 "opening_queries__L1_L64_L8_L23_L6" :=
  (oq_completeAtB_L1_L64_L8_L23_L6 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L1_L64_L8_L23_L8 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop451" (.n (oqP 1 64 8)) + 4 * 15 ≤ fs "__loop451") :
    OqCompleteAtB fs cert k 1 64 23 8 "opening_queries__L1_L64_L8_L23_L8" fun n => fs "opening_queries__L1_L64_L8_L23_L8" + (n + 1) + (n + 1) * fs "__loop451" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L23_L8") (f := Data.core666) (j := 666) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop451") (f := Data.core1003) (j := 1003) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 15) (cd := 8)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L1_L64_L8_L23_L8 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop451" (.n (oqP 1 64 8)) + 4 * 15 ≤ fs "__loop451") :
    OqCompleteAt fs cert k 1 64 23 8 "opening_queries__L1_L64_L8_L23_L8" :=
  (oq_completeAtB_L1_L64_L8_L23_L8 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L1_L64_L8_L24_L7 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop466" (.n (oqP 1 64 8)) + 4 * 17 ≤ fs "__loop466") :
    OqCompleteAtB fs cert k 1 64 24 7 "opening_queries__L1_L64_L8_L24_L7" fun n => fs "opening_queries__L1_L64_L8_L24_L7" + (n + 1) + (n + 1) * fs "__loop466" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L24_L7") (f := Data.core749) (j := 749) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop466") (f := Data.core1019) (j := 1019) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 17) (cd := 7)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L1_L64_L8_L24_L7 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop466" (.n (oqP 1 64 8)) + 4 * 17 ≤ fs "__loop466") :
    OqCompleteAt fs cert k 1 64 24 7 "opening_queries__L1_L64_L8_L24_L7" :=
  (oq_completeAtB_L1_L64_L8_L24_L7 fs cert k hfit).toD

set_option maxRecDepth 100000 in
theorem oq_completeAtB_L1_L64_L8_L25_L7 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop470" (.n (oqP 1 64 8)) + 4 * 18 ≤ fs "__loop470") :
    OqCompleteAtB fs cert k 1 64 25 7 "opening_queries__L1_L64_L8_L25_L7" fun n => fs "opening_queries__L1_L64_L8_L25_L7" + (n + 1) + (n + 1) * fs "__loop470" := by
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L25_L7") (f := Data.core821) (j := 821) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop470") (f := Data.core1024) (j := 1024) (by decide +kernel) rfl
  exact opening_queries_completeAt fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 18) (cd := 7)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel) hfit hn hleaf hq hsl hlin hreg

theorem oq_completeAt_L1_L64_L8_L25_L7 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop470" (.n (oqP 1 64 8)) + 4 * 18 ≤ fs "__loop470") :
    OqCompleteAt fs cert k 1 64 25 7 "opening_queries__L1_L64_L8_L25_L7" :=
  (oq_completeAtB_L1_L64_L8_L25_L7 fs cert k hfit).toD

end
end LeanVM.Guest.B1
