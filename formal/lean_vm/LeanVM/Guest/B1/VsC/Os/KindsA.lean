/-
  LeanVM.Guest.B1.VsC.Os.KindsA

  `open_stacked`'s straight named callees placed: `opening_message__L{n}_L1` at every deployed
  `n`, `fold_final_msg__L{n}`, `opening_tail_round`.
-/

module

public import LeanVM.Guest.B1.VsC.LeavesA
import LeanVM.Guest.CoreRef

/-!
# `open_stacked`'s straight named callees, placed

Each is a straight leaf loading only through its arrays (`leafPlaceOk`, one `decide +kernel` a
specialization), so `leafAtA_leafIn` places its `CallCompletes0` (`LeafAtA`: block its frame,
ending at its cursor, no words of its own) in any region holding its arrays' cells:
`opening_message_leafA` (every `(n, 1) ∈ omDeployed`: the cursor's `n + 1` words and the output's
`n`), `fold_final_msg_leafA` (every `foldFinalMsgNames` entry: the message's `2^n` words and the
point's `n`; its `CallCompletes0` by `ff_complete0`), `opening_tail_round_leafA` (the cursor's two
words).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fs LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## `opening_message` -/

set_option maxRecDepth 100000 in
theorem om_place : ∀ n, (n, 1) ∈ omDeployed → ∃ fn, coreProgram.find? (omName (n, 1)) = some fn ∧
    leafPlaceOk (omName (n, 1)) fn 7 [(5, n + 1), (6, n)] = true := by
  intro n hn
  simp only [omDeployed, List.mem_cons, Prod.mk.injEq, and_true, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, coreProgram_find?_at (j := idx% «opening_message__L1_L1») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «opening_message__L6_L1») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «opening_message__L8_L1») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «opening_message__L12_L1») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «opening_message__L20_L1») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «opening_message__L36_L1») rfl, by decide +kernel⟩

section
variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ)

/-- **`opening_message__L{n}_L1` completes placed**, every deployed `n`, its cursor's and output's
arrays in `R`. -/
theorem opening_message_leafA (kd : ℕ) {n : ℕ} (hn : (n, 1) ∈ omDeployed) (f0 f1 f2 f3 f4 cur out nn : E)
    (xs : List E) (hxs : xs.length = n) {R : ℕ → Prop} (hc : ArrIn R cur (n + 1)) (ho : ArrIn R out n) :
    LeafAtA fs al cert kd (omName (n, 1)) [f0, f1, f2, f3, f4, cur, out] (omRets f0 f1 f2 f3 f4 cur xs nn) R
      (fun _ => True) (fun rd ↦ ReadsAt rd cur (xs ++ [nn]) ∧ ReadsAt rd out xs) PostQuiet := by
  obtain ⟨fn, hf, hck⟩ := om_place n hn
  refine leafAtA_leafIn hf hck (fun q hq => ?_)
    (opening_message_complete kd n hn f0 f1 f2 f3 f4 cur out nn xs hxs)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact hc
  · exact ho

end

/-! ## `fold_final_msg` -/

/-- What `fold_final_msg__L{n}`'s completeness with no words of its own gives. -/
def FoldFinalComplete0 (kd n : ℕ) (name : String) : Prop :=
  ∀ (msg point : E) (m ps : List E), m.length = 2 ^ n → ps.length = n →
    CallCompletes0 kd name [msg, point] [multilinearEval m ps]
      (fun rd ↦ ReadsAt rd msg m ∧ ReadsAt rd point ps) PostQuiet

theorem ff_complete0 {kd n : ℕ} {name : String} {f : Fn} (hfind : coreProgram.find? name = some f)
    (hck : straightChecks f.body = true)
    (hiff : ∀ rd args rets, coreProgram.Rel rd name args rets ↔ MeaningFoldFinalMsg n rd args rets) :
    FoldFinalComplete0 kd n name :=
  fun _ _ m ps hm hps ↦ callCompletes0_of_rel_straight hfind hck fun rd _ ⟨h1, h2⟩ ↦
    (hiff rd _ _).mpr ⟨m, ps, hm, hps, h1, h2, rfl⟩

/-- A `fold_final_msg` specialization's kernel facts: found, straight, placeable. -/
def FfmFacts (name : String) (n : ℕ) : Prop :=
  ∃ fn, coreProgram.find? name = some fn ∧ straightChecks fn.body = true ∧
    leafPlaceOk name fn 2 [(0, 2 ^ n), (1, n)] = true ∧
    ∀ rd args rets, coreProgram.Rel rd name args rets ↔ MeaningFoldFinalMsg n rd args rets

set_option maxRecDepth 100000 in
theorem ffm_facts : ∀ p ∈ foldFinalMsgNames, FfmFacts p.1 p.2 := by
  intro p hp
  simp only [foldFinalMsgNames, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨_, coreProgram_find?_at (j := idx% «fold_final_msg__L2») rfl, by decide +kernel, by decide +kernel,
      fold_final_msg_L2_iff⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «fold_final_msg__L3») rfl, by decide +kernel, by decide +kernel,
      fold_final_msg_L3_iff⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «fold_final_msg__L4») rfl, by decide +kernel, by decide +kernel,
      fold_final_msg_L4_iff⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «fold_final_msg__L5») rfl, by decide +kernel, by decide +kernel,
      fold_final_msg_L5_iff⟩

section
variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ)

/-- **`fold_final_msg__L{n}` completes placed**, its message's and point's arrays in `R`. -/
theorem fold_final_msg_leafA (kd : ℕ) {p : String × ℕ} (hp : p ∈ foldFinalMsgNames) (msg point : E)
    (m ps : List E) (hm : m.length = 2 ^ p.2) (hps : ps.length = p.2) {R : ℕ → Prop}
    (hmr : ArrIn R msg (2 ^ p.2)) (hpr : ArrIn R point p.2) :
    LeafAtA fs al cert kd p.1 [msg, point] [multilinearEval m ps] R (fun _ => True)
      (fun rd ↦ ReadsAt rd msg m ∧ ReadsAt rd point ps) PostQuiet := by
  obtain ⟨fn, hf, hck, hpl, hiff⟩ := ffm_facts p hp
  refine leafAtA_leafIn hf hpl (fun q hq => ?_) (ff_complete0 (kd := kd) hf hck hiff msg point m ps hm hps)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact hmr
  · exact hpr

/-! ## `opening_tail_round` -/

set_option maxRecDepth 100000 in
theorem otr_place : ∃ fn, coreProgram.find? "opening_tail_round" = some fn ∧ straightChecks fn.body = true ∧
    leafPlaceOk "opening_tail_round" fn 8 [(5, 2)] = true :=
  ⟨_, find_opening_tail_round, by decide +kernel, by decide +kernel⟩

/-- **`opening_tail_round` completes placed**, its cursor's two cells in `R`. -/
theorem opening_tail_round_leafA (kd : ℕ) (f0 f1 f2 f3 f4 cur claim tabs c0 c2 : E) {R : ℕ → Prop}
    (hc : ArrIn R cur 2) :
    LeafAtA fs al cert kd "opening_tail_round" [f0, f1, f2, f3, f4, cur, claim, tabs]
      (otrRets f0 f1 f2 f3 f4 cur claim c0 c2) R (fun _ => True) (fun rd ↦ ReadsAt rd cur [c0, c2])
      PostQuiet := by
  obtain ⟨fn, hf, hck, hpl⟩ := otr_place
  refine leafAtA_leafIn hf hpl (fun q hq => ?_)
    (callCompletes0_of_rel_straight hf hck fun rd _ h ↦
      (opening_tail_round_holds rd _ _).mpr ⟨c0, c2, h, rfl⟩)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  subst hq
  exact hc

end

end
end LeanVM.Guest.B1.VsC
