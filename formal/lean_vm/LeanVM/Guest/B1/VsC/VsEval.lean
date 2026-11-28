/-
  LeanVM.Guest.B1.VsC.VsEval

  `verify_sub`'s body evaluated forward through its two branches, each on its taken arm.
-/

module

public import LeanVM.Guest.B1.VsC.WinSeg
public import LeanVM.Guest.B1.VsC.Fwd
import LeanVM.Guest.CoreRef

/-!
# `verify_sub`'s forward valuation

`Fwd.chk` rejects a branch, and `verify_sub`'s body has two: the least-height check
(`.ite (.n 234) [] vsI1n`, on the `KECCAK` table's log) and the pointer width's flag
(`.ite (.n 471) vsI2z vsI2n`). The body splits around them (`vsBody_eq`, by the kernel):
`vsA`, the first branch, `vsB`, the second, `vsC`, then `ret []`. Each straight part passes the
checker (`chk_vsA`, …), the arms numbered one after the other (the first arm's values, then the
second's).

`vsEv rd w args`: the words `Fwd.ev` gives part by part, each branch on its taken arm, the other
arm's values `0` (`padZ`). `vsVal_spec`: on `vsVal = Val.ofArgs (vsEv …)`, the parameters are the
arguments and every statement of each part, and of each taken arm, satisfies its defining equations
(`GoodS`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The body's parts -/

/-- `verify_sub`'s body. -/
noncomputable def vsBody : List Stmt := Fn.body fn% «verify_sub»

/-- Statements `0 ..< 180`: up to the least-height branch. -/
noncomputable def vsA : List Stmt := vsBody.take 180

/-- The least-height branch's arm when the `KECCAK` table's log is not `9`. -/
def vsI1n : List Stmt :=
  [.atom (.const (.n 235) (word 1 0)), .atom (.assertEq (.n 225) (.n 235)),
    .atom (.const (.n 236) (word 0 0)), .atom (.add (.n 237) (.n 226) (.n 236)),
    .atom (.hint (.inverse (.n 237) (.n 238))), .atom (.assertNe (.n 237) (.n 238) (.n 239))]

/-- Statements `181 ..< 427`: up to the pointer width's branch. -/
noncomputable def vsB : List Stmt := (vsBody.drop 181).take 246

/-- The pointer width's branch, its flag set. -/
def vsI2z : List Stmt :=
  [.atom (.const (.n 472) (word 9223372036854775821 0)), .atom (.mul (.n 473) (.n 409) (.n 472)),
    .atom (.mul (.n 474) (.n 4) (.n 473)), .atom (.load (.n 475) (.n 474) 0),
    .atom (.mul (.n 240) (.n 476) (.n 475)), .call "assert_small_g_power" [.n 476, .n 4] []]

/-- The pointer width's branch, its flag clear. -/
def vsI2n : List Stmt :=
  [.atom (.add (.n 477) (.n 409) (.n 101)), .atom (.const (.n 478) (word 524288 0)),
    .atom (.add (.n 479) (.n 409) (.n 478)), .atom (.mul (.n 480) (.n 477) (.n 479)),
    .atom (.const (.n 481) (word 0 0)), .atom (.assertEq (.n 480) (.n 481))]

/-- Statements `428 ..< 4222`: the rest before the `ret []`. -/
noncomputable def vsC : List Stmt := (vsBody.drop 428).take 3794

set_option maxRecDepth 200000 in
theorem vsBody_eq : vsBody = vsA ++ [.ite (.n 234) [] vsI1n] ++ vsB ++ [.ite (.n 471) vsI2z vsI2n] ++ vsC ++
    [.ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem vs_params : (fn% «verify_sub»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] := rfl

theorem vs_find : coreProgram.find? "verify_sub" = some fn% «verify_sub» :=
  coreProgram_find?_at (j := idx% «verify_sub») rfl

set_option maxRecDepth 200000 in
theorem vs_loop : coreProgram.loop "verify_sub" = false := by
  rw [Program.loop_of_find? vs_find]; decide +kernel

/-- A branch's `assertNe` after its `inverse` hint, as the checker reads it: the product `p = x · i`
(the inverse `i` already defined). -/
def fixA : Atom → Atom
  | .assertNe x i p => .mul p x i
  | a => a

/-- `fixA` on an atom statement. -/
def fixS : Stmt → Stmt
  | .atom a => .atom (fixA a)
  | s => s

/-- `vsA` as the checker reads it. -/
noncomputable def vsAf : List Stmt := vsA.map fixS

/-- `vsI1n` as the checker reads it. -/
def vsI1f : List Stmt := vsI1n.map fixS

set_option maxRecDepth 200000 in
theorem chk_vsA : chk 6 vsAf = some 235 := by decide +kernel

theorem chk_vsI1n : chk 235 vsI1f = some 240 := by decide +kernel

set_option maxRecDepth 200000 in
theorem chk_vsB : chk 240 vsB = some 472 := by decide +kernel

theorem chk_vsI2z : chk 472 vsI2z = some 477 := by decide +kernel

theorem chk_vsI2n : chk 477 vsI2n = some 482 := by decide +kernel

/-- The values `verify_sub`'s body defines: `.n 0 ..< vsN`. -/
def vsN : ℕ := 4070

set_option maxRecDepth 200000 in
theorem chk_vsC : chk 482 vsC = some vsN := by decide +kernel

/-! ## The checker's counters -/

theorem chk_le {c c' : ℕ} {ss : List Stmt} (h : chk c ss = some c') : c ≤ c' := by
  have h' : chk (List.replicate c (0 : E)).length ss = some c' := by simpa using h
  obtain ⟨hl, ⟨m, hm⟩, -⟩ := ev_spec (fun _ => none) (fun _ => 0) ss _ h'
  rw [← hl, hm]; simp

/-- Every value of a checked block is below the counter after it. -/
theorem chk_vals : ∀ {c c' : ℕ} {ss : List Stmt}, chk c ss = some c' → ∀ s ∈ ss, ∀ v ∈ s.vals, v.idx < c'
  | _, _, [], _, _, hs, _, _ => absurd hs List.not_mem_nil
  | c, c', t :: ss, h, s, hs, v, hv => by
    simp only [chk] at h
    split at h
    · rename_i c1 hc1
      have hc1' : chkS (List.replicate c (0 : E)).length t = some c1 := by simpa using hc1
      obtain ⟨-, hv1, -⟩ := stepS (fun _ => none) (fun _ => 0) (List.replicate c 0) hc1'
      rcases List.mem_cons.mp hs with rfl | hs
      · exact lt_of_lt_of_le (hv1 v hv) (chk_le h)
      · exact chk_vals h s hs v hv
    · exact absurd h (by simp)

/-- **A checked block's equations on any extension of its words.** -/
theorem seg_good {rd : Reader} {w : ℕ → E} {l : List E} {ss : List Stmt} {c' : ℕ} (h : chk l.length ss = some c')
    {L : List E} (hL : ∃ m, L = ev rd w l ss ++ m) :
    ∀ s ∈ ss, GoodS rd (storesOf l.length ss) w (B1.Val.ofArgs L) s := by
  obtain ⟨hlen, -, hg⟩ := ev_spec rd w ss l h
  obtain ⟨m, rfl⟩ := hL
  intro s hs
  refine goodS_congr (fun v hv => ?_) (hg s hs)
  exact (ofArgs_old (by rw [hlen]; exact chk_vals h s hs v hv)).symm

/-! ## The evaluation -/

/-- Words padded with `0` to length `n`. -/
def padZ (l : List E) (n : ℕ) : List E := l ++ List.replicate (n - l.length) 0

theorem padZ_length {l : List E} {n : ℕ} (h : l.length ≤ n) : (padZ l n).length = n := by
  simp [padZ]; omega

section
variable (rd : Reader) (w : ℕ → E) (args : List E)

/-- The words after `vsA`. -/
noncomputable def vsL1 : List E := ev rd w args vsAf

/-- The words after the least-height branch. -/
noncomputable def vsL2 : List E :=
  if B1.Val.ofArgs (vsL1 rd w args) (.n 234) = 0 then padZ (vsL1 rd w args) 240 else ev rd w (vsL1 rd w args) vsI1f

/-- The words after `vsB`. -/
noncomputable def vsL3 : List E := ev rd w (vsL2 rd w args) vsB

/-- The words after the pointer width's branch. -/
noncomputable def vsL4 : List E :=
  if B1.Val.ofArgs (vsL3 rd w args) (.n 471) = 0 then padZ (ev rd w (vsL3 rd w args) vsI2z) 482
  else ev rd w (padZ (vsL3 rd w args) 477) vsI2n

/-- **`verify_sub`'s words, evaluated forward**, each branch on its taken arm. -/
noncomputable def vsEv : List E := ev rd w (vsL4 rd w args) vsC

/-- **`verify_sub`'s forward valuation.** -/
noncomputable def vsVal : Val := B1.Val.ofArgs (vsEv rd w args)

end

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vsL1_spec (ha : args.length = 6) : (vsL1 rd w args).length = 235 ∧ ∃ m, vsL1 rd w args = args ++ m := by
  obtain ⟨h1, h2, -⟩ := ev_spec rd w vsAf args (c' := 235) (by rw [ha]; exact chk_vsA)
  exact ⟨h1, h2⟩

theorem vsL2_spec (ha : args.length = 6) : (vsL2 rd w args).length = 240 ∧ ∃ m, vsL2 rd w args = vsL1 rd w args ++ m := by
  obtain ⟨h1, -⟩ := vsL1_spec (rd := rd) (w := w) ha
  unfold vsL2
  split_ifs
  · exact ⟨padZ_length (by omega), _, rfl⟩
  · obtain ⟨h1', h2', -⟩ := ev_spec rd w vsI1f (vsL1 rd w args) (c' := 240) (by rw [h1]; exact chk_vsI1n)
    exact ⟨h1', h2'⟩

theorem vsL3_spec (ha : args.length = 6) : (vsL3 rd w args).length = 472 ∧ ∃ m, vsL3 rd w args = vsL2 rd w args ++ m := by
  obtain ⟨h1, -⟩ := vsL2_spec (rd := rd) (w := w) ha
  obtain ⟨h1', h2', -⟩ := ev_spec rd w vsB (vsL2 rd w args) (c' := 472) (by rw [h1]; exact chk_vsB)
  exact ⟨h1', h2'⟩

theorem vsL4_spec (ha : args.length = 6) : (vsL4 rd w args).length = 482 ∧ ∃ m, vsL4 rd w args = vsL3 rd w args ++ m := by
  obtain ⟨h1, -⟩ := vsL3_spec (rd := rd) (w := w) ha
  unfold vsL4
  split_ifs
  · obtain ⟨h1', ⟨m, hm⟩, -⟩ := ev_spec rd w vsI2z (vsL3 rd w args) (c' := 477) (by rw [h1]; exact chk_vsI2z)
    exact ⟨padZ_length (by omega), m ++ _, by rw [padZ, hm, List.append_assoc]⟩
  · have hp : (padZ (vsL3 rd w args) 477).length = 477 := padZ_length (by omega)
    obtain ⟨h1', ⟨m, hm⟩, -⟩ := ev_spec rd w vsI2n (padZ (vsL3 rd w args) 477) (c' := 482)
      (by rw [hp]; exact chk_vsI2n)
    exact ⟨h1', List.replicate (477 - (vsL3 rd w args).length) 0 ++ m, by rw [hm, padZ, List.append_assoc]⟩

theorem vsEv_spec (ha : args.length = 6) : (vsEv rd w args).length = vsN ∧ ∃ m, vsEv rd w args = vsL4 rd w args ++ m := by
  obtain ⟨h1, -⟩ := vsL4_spec (rd := rd) (w := w) ha
  obtain ⟨h1', h2', -⟩ := ev_spec rd w vsC (vsL4 rd w args) (c' := vsN) (by rw [h1]; exact chk_vsC)
  exact ⟨h1', h2'⟩

theorem ext_trans {a b c : List E} (h1 : ∃ m, b = a ++ m) (h2 : ∃ m, c = b ++ m) : ∃ m, c = a ++ m := by
  obtain ⟨m1, rfl⟩ := h1
  obtain ⟨m2, rfl⟩ := h2
  exact ⟨m1 ++ m2, by simp⟩

theorem vsEv_ext4 (ha : args.length = 6) : ∃ m, vsEv rd w args = vsL4 rd w args ++ m := (vsEv_spec ha).2

theorem vsEv_ext3 (ha : args.length = 6) : ∃ m, vsEv rd w args = vsL3 rd w args ++ m :=
  ext_trans (vsL4_spec ha).2 (vsEv_ext4 ha)

theorem vsEv_ext2 (ha : args.length = 6) : ∃ m, vsEv rd w args = vsL2 rd w args ++ m :=
  ext_trans (vsL3_spec ha).2 (vsEv_ext3 ha)

theorem vsEv_ext1 (ha : args.length = 6) : ∃ m, vsEv rd w args = vsL1 rd w args ++ m :=
  ext_trans (vsL2_spec ha).2 (vsEv_ext2 ha)

theorem vsEv_ext0 (ha : args.length = 6) : ∃ m, vsEv rd w args = args ++ m :=
  ext_trans (vsL1_spec ha).2 (vsEv_ext1 ha)

/-- The parameters keep the arguments. -/
theorem vsVal_param (ha : args.length = 6) {i : ℕ} (hi : i < 6) : vsVal rd w args (.n i) = args.getD i 0 := by
  obtain ⟨m, hm⟩ := vsEv_ext0 (rd := rd) (w := w) ha
  rw [vsVal, hm, ofArgs_old (by rw [ha]; exact hi)]
  rfl

theorem vsVal_params (ha : args.length = 6) : (fn% «verify_sub»).params.map (vsVal rd w args) = args := by
  rw [vs_params]
  match args, ha with
  | [a0, a1, a2, a3, a4, a5], _ =>
    simp only [List.map_cons, List.map_nil]
    rw [vsVal_param rfl (by norm_num : 0 < 6), vsVal_param rfl (by norm_num : 1 < 6),
      vsVal_param rfl (by norm_num : 2 < 6), vsVal_param rfl (by norm_num : 3 < 6),
      vsVal_param rfl (by norm_num : 4 < 6), vsVal_param rfl (by norm_num : 5 < 6)]
    rfl

/-- The least-height branch's selector, read after `vsA`. -/
theorem vsVal_234 (ha : args.length = 6) : vsVal rd w args (.n 234) = B1.Val.ofArgs (vsL1 rd w args) (.n 234) := by
  obtain ⟨m, hm⟩ := vsEv_ext1 (rd := rd) (w := w) ha
  rw [vsVal, hm, ofArgs_old (by rw [(vsL1_spec ha).1]; norm_num)]

/-- The pointer width's selector, read after `vsB`. -/
theorem vsVal_471 (ha : args.length = 6) : vsVal rd w args (.n 471) = B1.Val.ofArgs (vsL3 rd w args) (.n 471) := by
  obtain ⟨m, hm⟩ := vsEv_ext3 (rd := rd) (w := w) ha
  rw [vsVal, hm, ofArgs_old (by rw [(vsL3_spec ha).1]; norm_num)]

/-! ## The equations -/

theorem vsVal_goodA (ha : args.length = 6) : ∀ s ∈ vsAf, GoodS rd (storesOf 6 vsAf) w (vsVal rd w args) s := by
  have := seg_good (rd := rd) (w := w) (l := args) (by rw [ha]; exact chk_vsA) (L := vsEv rd w args)
    (vsEv_ext1 ha)
  rwa [ha] at this

theorem vsVal_goodI1 (ha : args.length = 6) (h : vsVal rd w args (.n 234) ≠ 0) :
    ∀ s ∈ vsI1f, GoodS rd (storesOf 235 vsI1f) w (vsVal rd w args) s := by
  have hl := (vsL1_spec (rd := rd) (w := w) ha).1
  have e2 : vsL2 rd w args = ev rd w (vsL1 rd w args) vsI1f := by
    rw [vsVal_234 ha] at h
    unfold vsL2; split_ifs with hh
    · exact absurd hh h
    · rfl
  have := seg_good (rd := rd) (w := w) (l := vsL1 rd w args) (by rw [hl]; exact chk_vsI1n) (L := vsEv rd w args)
    (by rw [← e2]; exact vsEv_ext2 ha)
  rwa [hl] at this

theorem vsVal_goodB (ha : args.length = 6) : ∀ s ∈ vsB, GoodS rd (storesOf 240 vsB) w (vsVal rd w args) s := by
  have hl := (vsL2_spec (rd := rd) (w := w) ha).1
  have := seg_good (rd := rd) (w := w) (l := vsL2 rd w args) (by rw [hl]; exact chk_vsB) (L := vsEv rd w args)
    (vsEv_ext3 ha)
  rwa [hl] at this

theorem vsVal_goodI2z (ha : args.length = 6) (h : vsVal rd w args (.n 471) = 0) :
    ∀ s ∈ vsI2z, GoodS rd (storesOf 472 vsI2z) w (vsVal rd w args) s := by
  have hl := (vsL3_spec (rd := rd) (w := w) ha).1
  have e4 : vsL4 rd w args = padZ (ev rd w (vsL3 rd w args) vsI2z) 482 := by
    rw [vsVal_471 ha] at h
    unfold vsL4; split_ifs; rfl
  have := seg_good (rd := rd) (w := w) (l := vsL3 rd w args) (by rw [hl]; exact chk_vsI2z) (L := vsEv rd w args)
    (by
      obtain ⟨m, hm⟩ := vsEv_ext4 (rd := rd) (w := w) ha
      exact ⟨List.replicate (482 - (ev rd w (vsL3 rd w args) vsI2z).length) 0 ++ m,
        by rw [hm, e4, padZ, List.append_assoc]⟩)
  rwa [hl] at this

theorem vsVal_goodI2n (ha : args.length = 6) (h : vsVal rd w args (.n 471) ≠ 0) :
    ∀ s ∈ vsI2n, GoodS rd (storesOf 477 vsI2n) w (vsVal rd w args) s := by
  have hl := (vsL3_spec (rd := rd) (w := w) ha).1
  have hp : (padZ (vsL3 rd w args) 477).length = 477 := padZ_length (by omega)
  have e4 : vsL4 rd w args = ev rd w (padZ (vsL3 rd w args) 477) vsI2n := by
    rw [vsVal_471 ha] at h
    unfold vsL4; split_ifs with hh
    · exact absurd hh h
    · rfl
  have := seg_good (rd := rd) (w := w) (l := padZ (vsL3 rd w args) 477) (by rw [hp]; exact chk_vsI2n)
    (L := vsEv rd w args) (by rw [← e4]; exact vsEv_ext4 ha)
  rwa [hp] at this

theorem vsVal_goodC (ha : args.length = 6) : ∀ s ∈ vsC, GoodS rd (storesOf 482 vsC) w (vsVal rd w args) s := by
  have hl := (vsL4_spec (rd := rd) (w := w) ha).1
  have := seg_good (rd := rd) (w := w) (l := vsL4 rd w args) (by rw [hl]; exact chk_vsC) (L := vsEv rd w args)
    ⟨[], by simp [vsEv]⟩
  rwa [hl] at this

end

end
end LeanVM.Guest.B1.VsC
