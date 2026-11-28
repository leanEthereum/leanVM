/-
  LeanVM.Guest.B1.VsC.RelC

  `fold_final_msg`, `opening_tail_round` and `squeeze_point_from` complete, layout-free, from
  their relations' completeness.
-/

module

public import LeanVM.Guest.B1.VsC.Fwd
public import LeanVM.Guest.B1.Eq.FoldFinal
public import LeanVM.Guest.B1.Fs.TailRound
public import LeanVM.Guest.B1.Fs.SqueezePoint
import LeanVM.Guest.CoreRef

/-!
# Straight callees, complete from their relations

Each body is straight with no hint (`straightChecks`, by the kernel) and the guest stream proves
its relation equivalent to its meaning, so `callCompletes_of_rel_straight` gives its completeness
on every memory holding the words its meaning reads (or, for `squeeze_point_from`, the words it
stores: the caller's).

* `fold_final_msg_complete`: `fold_final_msg__L{n}`, `2 ≤ n ≤ 5`, on `m` (`2^n` words) at `msg` and
  `ps` (`n` words) at `point`, returns `multilinearEval m ps`.
* `opening_tail_round_complete`: on `[c0, c2]` at `cur`, its meaning's words.
* `squeeze_point_from_complete`: `squeeze_point_from__L{n}`, `6 ≤ n ≤ 30`, on a memory holding the
  challenges at `point`, returns the capacity after them.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `fold_final_msg` -/

/-- What `fold_final_msg__L{n}`'s completeness gives. -/
def FoldFinalComplete (kd n : ℕ) (name : String) : Prop :=
  ∀ (msg point : E) (m ps : List E), m.length = 2 ^ n → ps.length = n →
    CallCompletes kd name [msg, point] [multilinearEval m ps]
      (fun rd ↦ ReadsAt rd msg m ∧ ReadsAt rd point ps) PostQuiet

theorem ff_complete {kd n : ℕ} {name : String} {f : Fn} (hfind : coreProgram.find? name = some f)
    (hck : straightChecks f.body = true)
    (hiff : ∀ rd args rets, coreProgram.Rel rd name args rets ↔ MeaningFoldFinalMsg n rd args rets) :
    FoldFinalComplete kd n name :=
  fun _ _ m ps hm hps ↦ callCompletes_of_rel_straight hfind hck fun rd _ ⟨h1, h2⟩ ↦
    (hiff rd _ _).mpr ⟨m, ps, hm, hps, h1, h2, rfl⟩

set_option maxRecDepth 100000 in
theorem fold_final_msg_L2_complete (kd : ℕ) : FoldFinalComplete kd 2 "fold_final_msg__L2" :=
  ff_complete (coreProgram_find?_at (j := idx% «fold_final_msg__L2») rfl) (by decide +kernel)
    fold_final_msg_L2_iff

set_option maxRecDepth 100000 in
theorem fold_final_msg_L3_complete (kd : ℕ) : FoldFinalComplete kd 3 "fold_final_msg__L3" :=
  ff_complete (coreProgram_find?_at (j := idx% «fold_final_msg__L3») rfl) (by decide +kernel)
    fold_final_msg_L3_iff

set_option maxRecDepth 100000 in
theorem fold_final_msg_L4_complete (kd : ℕ) : FoldFinalComplete kd 4 "fold_final_msg__L4" :=
  ff_complete (coreProgram_find?_at (j := idx% «fold_final_msg__L4») rfl) (by decide +kernel)
    fold_final_msg_L4_iff

set_option maxRecDepth 100000 in
theorem fold_final_msg_L5_complete (kd : ℕ) : FoldFinalComplete kd 5 "fold_final_msg__L5" :=
  ff_complete (coreProgram_find?_at (j := idx% «fold_final_msg__L5») rfl) (by decide +kernel)
    fold_final_msg_L5_iff

/-- **Every `fold_final_msg__L{n}` completes**, `2 ≤ n ≤ 5`. -/
theorem fold_final_msg_complete (kd : ℕ) : ∀ p ∈ foldFinalMsgNames, FoldFinalComplete kd p.2 p.1 := by
  intro p hp
  simp only [foldFinalMsgNames, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  exacts [fold_final_msg_L2_complete kd, fold_final_msg_L3_complete kd,
    fold_final_msg_L4_complete kd, fold_final_msg_L5_complete kd]

/-! ## `opening_tail_round` -/

/-- `opening_tail_round`'s returns on the round's two words. -/
def otrRets (f0 f1 f2 f3 f4 cur claim c0 c2 : E) : List E :=
  let s := (⟨[f0, f1, f2, f3, f4], []⟩ : Fs).absorbAll [c0, c2] dsObserve
  s.squeeze.2.cap ++ [cur * gen ^ 2, c0 + s.squeeze.1 * (claim + (1 + s.squeeze.1) * c2), s.squeeze.1]

/-- **`opening_tail_round` completes** on a memory holding the round's words `[c0, c2]` at `cur`. -/
theorem opening_tail_round_complete (kd : ℕ) (f0 f1 f2 f3 f4 cur claim tabs c0 c2 : E) :
    CallCompletes kd "opening_tail_round" [f0, f1, f2, f3, f4, cur, claim, tabs]
      (otrRets f0 f1 f2 f3 f4 cur claim c0 c2) (fun rd ↦ ReadsAt rd cur [c0, c2]) PostQuiet :=
  callCompletes_of_rel_straight find_opening_tail_round (by decide +kernel) fun rd _ h ↦
    (opening_tail_round_holds rd _ _).mpr ⟨c0, c2, h, rfl⟩

/-! ## `squeeze_point_from` -/

theorem spf_checks : ∀ n ∈ spfDeployed, ∃ fn : Fn, coreProgram.find? (spfName n) = some fn ∧
    straightChecks fn.body = true := by
  intro n hn
  simp only [spfDeployed, List.mem_map, List.mem_range] at hn
  obtain ⟨i, hi, rfl⟩ := hn
  interval_cases i
  · exact ⟨_, spf_found_6.1, by rw [spf_found_6.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_7.1, by rw [spf_found_7.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_8.1, by rw [spf_found_8.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_9.1, by rw [spf_found_9.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_10.1, by rw [spf_found_10.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_11.1, by rw [spf_found_11.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_12.1, by rw [spf_found_12.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_13.1, by rw [spf_found_13.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_14.1, by rw [spf_found_14.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_15.1, by rw [spf_found_15.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_16.1, by rw [spf_found_16.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_17.1, by rw [spf_found_17.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_18.1, by rw [spf_found_18.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_19.1, by rw [spf_found_19.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_20.1, by rw [spf_found_20.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_21.1, by rw [spf_found_21.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_22.1, by rw [spf_found_22.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_23.1, by rw [spf_found_23.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_24.1, by rw [spf_found_24.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_25.1, by rw [spf_found_25.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_26.1, by rw [spf_found_26.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_27.1, by rw [spf_found_27.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_28.1, by rw [spf_found_28.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_29.1, by rw [spf_found_29.2.2]; decide +kernel⟩
  · exact ⟨_, spf_found_30.1, by rw [spf_found_30.2.2]; decide +kernel⟩

/-- **`squeeze_point_from__L{n}` completes**, `6 ≤ n ≤ 30`, on a memory holding `first` and the
`n - 1` challenges after it at `point`, returning the capacity after them. -/
theorem squeeze_point_from_complete (kd : ℕ) : ∀ n ∈ spfDeployed, ∀ f0 f1 f2 f3 f4 first point : E,
    CallCompletes0 kd (spfName n) [f0, f1, f2, f3, f4, first, point]
      ((⟨[f0, f1, f2, f3, f4], []⟩ : Fs).squeezeN (n - 1)).2.cap
      (fun rd ↦ ReadsAt rd point (first :: ((⟨[f0, f1, f2, f3, f4], []⟩ : Fs).squeezeN (n - 1)).1))
      PostQuiet := by
  intro n hn f0 f1 f2 f3 f4 first point
  obtain ⟨fn, hf, hck⟩ := spf_checks n hn
  exact callCompletes0_of_rel_straight hf hck fun rd _ h ↦
    (squeeze_point_from_holds n hn rd _ _).mpr ⟨h, rfl⟩

end
end LeanVM.Guest.B1.VsC
