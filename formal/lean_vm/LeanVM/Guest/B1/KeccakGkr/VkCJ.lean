/-
  LeanVM.Guest.B1.KeccakGkr.VkCJ

  What the kernel checks of `verify_keccak`'s body as a flat function: its statements, buffers,
  calls.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCCK.Steps
public import LeanVM.Guest.B1.KeccakGkr.VkHolds
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»

/-!
# The body, flat

`vkT = vkPre ++ [.ret vkVs]` (`vkT_pre`). `vkPre_kernel`: its statements are flat, it takes no
frame addresses, its seven buffers (`vkAllocs`); it dispatches nothing, so its calls are `vkCalls`
(`vkPre_callSF`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The inputs' check and the return but the return. -/
def vkFinPre : List Stmt := vkFinT.dropLast

/-- The returned values. -/
def vkVs : List V := [.n (val% «verify_keccak» "s82#0"), .n (val% «verify_keccak» "s82#0[1]"), .n (val% «verify_keccak» "s82#0[2]"), .n (val% «verify_keccak» "s82#0[3]"), .n (val% «verify_keccak» "s82#0[4]"), .n (val% «verify_keccak» "s82#0[5]"), .n (val% «verify_keccak» "s82#0[6]")]

/-- The body but its return. -/
def vkPre : List Stmt := vkHeadT ++ vkFirstT ++ vkStepsT ++ vkOutT ++ vkInT ++ vkFinPre

theorem vkFinT_pre : vkFinT = vkFinPre ++ [.ret vkVs] := stmtsEqb_sound (by decide +kernel)

theorem vkT_pre : vkT = vkPre ++ [.ret vkVs] := by
  rw [vkT, vkPre, vkFinT_pre]; simp only [List.append_assoc]

/-- The buffers. -/
def vkAllocs : List (V × (ℕ ⊕ V)) :=
  [(.n (val% «verify_keccak» "point"), .inr (.n (val% «verify_keccak» "point~1"))), (.n (val% «verify_keccak» "r_lane"), .inl 5), (.n (val% «verify_keccak» "claims"), .inl 286), (.n (val% «verify_keccak» "mu_tree"), .inl 30), (.n (val% «verify_keccak» "lane_tree"), .inl 62),
    (.n (val% «verify_keccak» "segment_tree"), .inl 2), (.n (val% «verify_keccak» "low_tree"), .inl 30)]

/-- Not a dispatch. -/
def vkNoDispB : Stmt → Bool
  | .dispatch .. => false
  | _ => true

/-- Step `s`'s call's arguments and returns. -/
def stepCall (s : ℕ) : Option V × String × List V × List V :=
  let T := stepT0 s (stepB s)
  if s = 0 then
    (none, layerName 1, (stepCap s).map .n ++ [.n (val% «verify_keccak» "value_rate[0]"), .n (val% «verify_keccak» "value_rate[1]"), .n (T + 1), .n (T + 3), .n (val% «verify_keccak» "step_g@2"),
      .n (val% «verify_keccak» "rem_g@3"), .n (val% «verify_keccak» "claims"), .n (T + 5), .n (T - 1), .n (val% «verify_keccak» "tabs"), .n (val% «verify_keccak» "stream")], (List.range 6).map fun j ↦ .n (T + 6 + j))
  else
    (none, layerName 0, (stepCap s).map .n ++ [.n T, .n (T + 1), .n (stepCur s), .n (T + 3),
      .n (val% «verify_keccak» "step_g@2"), .n (val% «verify_keccak» "rem_g@3"), .n (T + 5), .n (T + 7), .n (T - 1), .n (val% «verify_keccak» "tabs"), .n (val% «verify_keccak» "stream")], (List.range 6).map fun j ↦ .n (T + 8 + j))

/-- **The calls.** -/
def vkCalls : List (Option V × String × List V × List V) :=
  [(some (.n (val% «verify_keccak» "s17#1")), name% «verify_keccak_loop0», [.n (val% «verify_keccak» "s17#2"), .n (val% «verify_keccak» "pack_g"), .n (val% «verify_keccak» "point"), .n (val% «verify_keccak» "s17#4")], [])] ++
    (List.range 12).map stepCall ++
    [(none, "keccak_plain_rounds__L6_L0", [.n (val% «verify_keccak» "fs0@13"), .n (val% «verify_keccak» "fs1@13"), .n (val% «verify_keccak» "fs2@13"), .n (val% «verify_keccak» "fs3@13"), .n (val% «verify_keccak» "fs4@13"), .n (val% «verify_keccak» "fs0@14~7"),
        .n (val% «verify_keccak» "fs0@14~8"), .n (val% «verify_keccak» "cursor@13"), .n (val% «verify_keccak» "x@1"), .n (val% «verify_keccak» "out_slot"), .n (val% «verify_keccak» "tabs")], (List.range 7).map fun j ↦ .n ((val% «verify_keccak» "fs0@14") + j)),
      (some (.n (val% «verify_keccak» "s57#1")), name% «verify_keccak_loop1», [.n (val% «verify_keccak» "s57#2"), .n (val% «verify_keccak» "pack_g"), .n (val% «verify_keccak» "s57#4"), .n (val% «verify_keccak» "point")], []),
      (none, "keccak_plain_rounds__L4_L1", [.n (val% «verify_keccak» "fs0@14"), .n (val% «verify_keccak» "fs1@14"), .n (val% «verify_keccak» "fs2@14"), .n (val% «verify_keccak» "fs3@14"), .n (val% «verify_keccak» "fs4@14"), .n (val% «verify_keccak» "word_rate[0]"),
        .n (val% «verify_keccak» "word_rate[1]"), .n (val% «verify_keccak» "fs0@15~8"), .n (val% «verify_keccak» "fs0@15~9"), .n (val% «verify_keccak» "fs0@15~11"), .n (val% «verify_keccak» "tabs")], (List.range 7).map fun j ↦ .n ((val% «verify_keccak» "fs0@15") + j)),
      (none, "keccak_plain_rounds__L6_L0", [.n (val% «verify_keccak» "fs0@15"), .n (val% «verify_keccak» "fs1@15"), .n (val% «verify_keccak» "fs2@15"), .n (val% «verify_keccak» "fs3@15"), .n (val% «verify_keccak» "fs4@15"), .n (val% «verify_keccak» "fs0@16~7"),
        .n (val% «verify_keccak» "fs0@16~8"), .n (val% «verify_keccak» "cursor@15"), .n (val% «verify_keccak» "low_value"), .n (val% «verify_keccak» "in_slot"), .n (val% «verify_keccak» "tabs")], (List.range 7).map fun j ↦ .n ((val% «verify_keccak» "fs0@16") + j)),
      (some (.n (val% «verify_keccak» "s81#1")), name% «verify_keccak_loop2», [.n (val% «verify_keccak» "s81#2"), .n (val% «verify_keccak» "pack_g"), .n (val% «verify_keccak» "s81#4"), .n (val% «verify_keccak» "last_point")], [])]

theorem vkPre_kernel :
    vkPre.all Stmt.flat = true ∧ vkPre.filterMap Main.Stmt.addrS = [] ∧
    vkPre.filterMap Main.Stmt.allocSz = vkAllocs ∧ vkPre.all vkNoDispB = true ∧
    vkPre.filterMap Main.Stmt.callS = vkCalls := by
  decide +kernel

theorem vk_callSF_of_noDisp (σ : Val) {s : Stmt} (h : vkNoDispB s = true) :
    s.callSF σ = Main.Stmt.callS s := by
  cases s with
  | dispatch x fs args rets => simp [vkNoDispB] at h
  | _ => rfl

theorem vkPre_callSF (σ : Val) : vkPre.filterMap (Stmt.callSF σ) = vkCalls := by
  rw [← vkPre_kernel.2.2.2.2]
  exact List.filterMap_congr fun _ hs ↦
    vk_callSF_of_noDisp σ (List.all_eq_true.mp vkPre_kernel.2.2.2.1 _ hs)

theorem vkPre_disp (σ : Val) : ∀ s ∈ vkPre, DispOk σ s := by
  intro s hs
  have h := List.all_eq_true.mp vkPre_kernel.2.2.2.1 s hs
  cases s with
  | dispatch x fs args rets => simp [vkNoDispB] at h
  | _ => trivial

end
end LeanVM.Guest.B1.VerifySub
