/-
  LeanVM.Guest.Complete.WithinCount

  Why a placed `main`'s end needs a bound before any memory, and its bound within `2^30` below `2^63`
  at the deployed choices.
-/

module

public import LeanVM.Guest.Complete.Open
public import LeanVM.Guest.Complete.BridgeB1
public import LeanVM.Guest.Budget.FramesG

/-!
# `main`'s end from the count

`CallAtA … "main" … e` gives a tree only on memories holding its words `W` (`HoldsWords`), and words
`2^64 - 1` apart alias (`g^(2^64-1) = 1`): with two runs `2^64 - 1` apart holding `0` and `1`, no memory
holds them, every tree is vacuous and `e` is arbitrary (`callAtA_main_vacuous`). So no bound on `e`
follows from `CallAtA` alone: the callees' fields bound their ends (`AtEveryB`, `VsCompleteHypA`), so
that `main`'s window ends below `2^57` (`MainWindowAt`), and below `2^63` the words have a memory
(`rootImage`), the tree on it is `MainHonest`, and its aligned words, which are `e`, are within the count
(`end_le_of_count`, `endWithin_of_count`, `Open.lean`). `within_deployed`: at `alW`, `k = 17` and the
deployed coefficients, from `MainHand alW true`.
-/
namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Guest.Budget

@[expose] public section

/-- **A placed `main` at any end, vacuously**: two runs `2^64 - 1` apart, holding `0` and `1`, share an
address, so no memory holds them and every end past `2^30` is one of `CallAtA`'s. So the former field
`MainCalleesOpenA.within` (every such end within `2^30`) failed on any node its hypotheses admit. -/
theorem callAtA_main_vacuous (al : String → Bool) (k : ℕ) (Pre : Reader → Prop) (Post : Reader → Tree → Prop) :
    ∃ (D : ℕ → Prop) (Out : Reader → Prop) (e : ℕ), 2 ^ 30 < e ∧
      CallAtA B2C.fs al B2C.cert k "main" [] [] (· < 2) D Out Pre Post (B2C.fs "main") 0 (B2C.fs "main") e := by
  set B := B2C.fs "main"
  refine ⟨fun _ => False, fun _ => True, B + 2 ^ 64, by omega,
    [(B, [0]), (B + (2 ^ 64 - 1), [1])], ⟨?_, ?_⟩, by omega, fun _ _ => trivial, ?_⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> right <;> simp
  · simp
  · intro rd _ hw _
    exfalso
    have h1 := (hw _ List.mem_cons_self 0 (by simp)).2
    have h2 := (hw _ (List.mem_cons_of_mem _ List.mem_cons_self) 0 (by simp)).2
    dsimp only at h1 h2
    rw [Main.addr_ofK] at h1 h2
    have ha : addressOfIndex (B + (2 ^ 64 - 1) + 0) = addressOfIndex (B + 0) := by
      simp only [addressOfIndex, Nat.add_zero, pow_add, g_pow_card_sub_one, mul_one]
    rw [ha, h1] at h2
    simp at h2

/-- The frames within the certificates' at the deployed flags. -/
theorem framesWithin_alW : FramesWithin alW := ⟨fs_within_fsW, fun _ hg => hg, B2C.fs_tailKey_le⟩

/-- **`main`'s end within `2^30` below `2^63`**, at the deployed choices, from `main`'s hand facts. -/
theorem within_deployed (hH : MainHand alW true) : MainEndWithin alW 17 :=
  endWithin_of_count (by norm_num) hH framesWithin_alW deployed_above_checker fun s w _ hl => fits_deployed s w hl

end

end LeanVM.Guest.Complete
