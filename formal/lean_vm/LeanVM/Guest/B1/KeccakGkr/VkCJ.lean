/-
  LeanVM.Guest.B1.KeccakGkr.VkCJ

  What the kernel checks of `verify_keccak`'s body as a flat function: its statements, buffers,
  calls.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCI
public import LeanVM.Guest.B1.KeccakGkr.VkHolds
public import LeanVM.Guest.B1.Tables.FlatAt

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
def vkVs : List V := [.n 3868, .n 3869, .n 3870, .n 3871, .n 3872, .n 3875, .n 3876, .n 3877]

/-- The body but its return. -/
def vkPre : List Stmt := vkHeadT ++ vkFirstT ++ vkStepsT ++ vkOutT ++ vkInT ++ vkFinPre

theorem vkFinT_pre : vkFinT = vkFinPre ++ [.ret vkVs] := stmtsEqb_sound (by decide +kernel)

theorem vkT_pre : vkT = vkPre ++ [.ret vkVs] := by
  rw [vkT, vkPre, vkFinT_pre]; simp only [List.append_assoc]

/-- The buffers. -/
def vkAllocs : List (V × (ℕ ⊕ V)) :=
  [(.n 60, .inr (.n 59)), (.n 92, .inl 5), (.n 203, .inl 286), (.n 205, .inl 30), (.n 276, .inl 62),
    (.n 384, .inl 2), (.n 1259, .inl 30)]

/-- Not a dispatch. -/
def vkNoDispB : Stmt → Bool
  | .dispatch .. => false
  | _ => true

/-- Step `s`'s call's arguments and returns. -/
def stepCall (s : ℕ) : Option V × String × List V × List V :=
  let T := stepT0 s (stepB s)
  if s = 0 then
    (none, layerName 1, (stepCap s).map .n ++ [.n 200, .n 202, .n (T + 1), .n (T + 3), .n 33,
      .n 47, .n 203, .n (T + 5), .n (T - 1)], (List.range 6).map fun j ↦ .n (T + 6 + j))
  else
    (none, layerName 0, (stepCap s).map .n ++ [.n T, .n (T + 1), .n (stepCur s), .n (T + 3),
      .n 33, .n 47, .n (T + 5), .n (T + 7), .n (T - 1)], (List.range 6).map fun j ↦ .n (T + 8 + j))

/-- **The calls.** -/
def vkCalls : List (Option V × String × List V × List V) :=
  [(some (.n 62), "__loop10", [.n 63, .n 17, .n 60, .n 65], [])] ++
    (List.range 12).map stepCall ++
    [(none, "keccak_plain_rounds__L6_L0", [.n 957, .n 958, .n 959, .n 960, .n 961, .n 964,
        .n 965, .n 962, .n 193, .n 963], (List.range 7).map fun j ↦ .n (966 + j)),
      (some (.n 1243), "__loop11", [.n 1244, .n 17, .n 1246, .n 60], []),
      (none, "keccak_plain_rounds__L4_L1", [.n 966, .n 967, .n 968, .n 969, .n 970, .n 980,
        .n 982, .n 1248, .n 1249, .n 1251], (List.range 7).map fun j ↦ .n (1252 + j)),
      (none, "keccak_plain_rounds__L6_L0", [.n 1252, .n 1253, .n 1254, .n 1255, .n 1256, .n 1380,
        .n 1381, .n 1257, .n 1258, .n 1379], (List.range 7).map fun j ↦ .n (1382 + j)),
      (some (.n 3864), "__loop12", [.n 3865, .n 17, .n 3867, .n 2249], [])]

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
