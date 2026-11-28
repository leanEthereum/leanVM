/-
  LeanVM.Guest.VsKaps

  B2's obligations on `verify_sub`'s prefix up to its call of `check_stack_terminal`: the kappas
  and the stack's log it hands it.
-/

module

public import LeanVM.Guest.Sound
public import LeanVM.Guest.B1.VerifySub.Sizes
public import LeanVM.Protocol.Relation.Placement
public import LeanVM.Guest.B1.KeccakGkr.Lib

/-!
# `verify_sub`'s kappas and stack log, known

`vsGmvKnown_proved`: `size_sel = gmv·g^-16` range checked below `g^15` puts `gmv` at
`g^(16 + e)`, `e < 15`. `vsKapsKnown_proved`: on the exponent tables, `certify_stack` places
the layout the announced sizes give (`sizesOk`, at any program of `2^23` words: the kappas do not
depend on it), and each block's `kaps` entry is `g^variableCount`, a placement inside a stack of at
most `2^30` words (`placement_aligned`), so `variableCount ≤ 30`.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Value
open LeanVM.Protocol.Verifier LeanVM.Guest.B1.VerifySub

@[expose] public section

theorem vs_core_body : (coreOf (fn_idx% «verify_sub»)).body = Fn.body fn% «verify_sub» := rfl

/-- A slice of `verify_sub`'s statements before `n` holds when the first `n` do. -/
theorem slice_of_prefix {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} {n a m : ℕ}
    {T : List Stmt} (hn : n ≤ 4222) (ham : a + m ≤ n) (hT : (vsPre.drop a).take m = T)
    (h : Stmt.HoldsList C rd σ ((coreOf (fn_idx% «verify_sub»)).body.take n) True kret) :
    Stmt.HoldsList C rd σ T True kret := by
  have hpre : (coreOf (fn_idx% «verify_sub»)).body.take n = vsPre.take n := by
    rw [vs_core_body, vs_body_eq, List.take_append_of_le_length (by
      have : vsPre.length = 4222 := by decide +kernel
      omega)]
  rw [hpre] at h
  have hnr : Stmt.noRetList (vsPre.take n) = true := by
    have := vsPre_noRet
    rw [← List.take_append_drop n vsPre] at this
    rw [VerifySub.noRetList_append, Bool.and_eq_true] at this
    exact this.1
  refine holdsList_of_forall _ fun s hs ↦ ?_
  subst hT
  have hs' : s ∈ vsPre.take n := by
    have e : (vsPre.drop a).take m = ((vsPre.take n).drop a).take m := by
      rw [List.drop_take, List.take_take]
      congr 1
      omega
    rw [e] at hs
    exact List.mem_of_mem_drop (List.mem_of_mem_take hs)
  exact ⟨noRet_of_mem hnr s hs', holds_of_noRetList _ hnr h s hs'⟩

/-- **`verify_sub`'s stack log at its terminal call**, from `size_sel`'s range check. -/
theorem vsGmvKnown_proved : VsGmvKnown := by
  intro κ L hκ1 hκ σ h
  have hs := slice_of_prefix (by decide) (by decide) vsStackT_eq h
  simp only [vsStackT, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hs
  obtain ⟨-, a432, a433, a434, a435, -⟩ := hs
  obtain ⟨e, he, h4⟩ := Digest.rc_const (memOk_of hκ1 (by simp [maxLogMem] at hκ ⊢; omega) L)
    (c := 14) (by norm_num) (by rw [a434, show (16384 : ℕ) = 2 ^ 14 from rfl, word_two_pow (by decide)]) a435
  refine ⟨e, by simp [vsGmvN]; omega, ?_⟩
  have : σ (.n vsGmv) = σ (.n 489) * gen ^ 16 := by
    rw [a433, a432, mul_assoc, word_ginv16_mul, mul_one]
  rw [this, h4, ← pow_add, gen_pow_eq_ofK, add_comm]

/-- **`verify_sub`'s kappas at its terminal call**: each below `g^31`. -/
theorem vsKapsKnown_proved : VsKapsKnown := by
  intro κ L hκ1 hκ σ hexp hwin h
  have hκ30 : κ ≤ 32 := by simp [maxLogMem] at hκ; omega
  have h11 : 11 ≤ κ := winTabBits_le_of_winTabs hκ30 L (winTabs_of_expWinTab hwin)
  have hbl : (List.replicate (2 ^ (Main.bytecodeLog + bytecodeSlotBits)) (0 : K)).length =
      2 ^ (Main.bytecodeLog + bytecodeSlotBits) := List.length_replicate
  have S := sizesOk h11 hκ30 L (C := coreProgram.Rel L.read) (fun _ _ _ h ↦ h) hbl hexp
    (slice_of_prefix (by decide) (by decide) vsReadsT_eq h)
    (slice_of_prefix (by decide) (by decide) vsHeightsT_eq h)
    (slice_of_prefix (by decide) (by decide) vsStackT_eq h)
  intro b hb
  obtain ⟨p, hp, -, hk⟩ := S.placed.2 b (by rw [Stack.nStkBlocks, Stack.stackBlocks_length]; exact hb)
  have hal := (placement_aligned S.build hp).2
  have h30 : 2 ^ p.variableCount ≤ 2 ^ 30 :=
    le_trans (by omega) (Nat.pow_le_pow_right (by norm_num) S.st2)
  have hv : p.variableCount ≤ 30 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h30
  exact ⟨p.variableCount, by simp [vsKapsBound]; omega, by rw [← gen_pow_eq_ofK]; exact hk⟩

end
end LeanVM.Guest.End
