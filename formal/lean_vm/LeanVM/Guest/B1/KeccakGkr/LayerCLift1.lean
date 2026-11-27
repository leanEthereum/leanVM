/-
  LeanVM.Guest.B1.KeccakGkr.LayerCLift1

  `keccak_layer`'s placement facts, by kernel evaluation: its body a flat list then its return,
  its buffers, its calls, and the pointers its loads go through.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCG
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.Memory.UniformF
public import LeanVM.Guest.Exact.Free
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L»
import LeanVM.Guest.StmtsAppend

/-!
# A layer's placement facts

`layerPre first odd`: the body but its return (`layerT_pre`). By the kernel (`layerPre_kernel`), it
is flat, places no run, allocates the pack challenges (`y` words), the round records (`77`), the
local point (`11`), the next claim's lanes (`25`) and flips (`7`), dispatches nothing
(`layerPre_disp`), calls the two pack loops (`layerCalls`, `layerPre_callSF`), and loads only
through the pointers `layerGroups` below their bounds and the inlined `grind_check`'s table
pointers `grindPtrs`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory

@[expose] public section

/-- The body but its return. -/
def layerPre (first : ℕ) : List Stmt :=
  secA1 first ⧺ (secA2 first ++ (rmfeBlockT (layOff first) ++ (hornerS first ++
    (packSetupT (layOff first) first ++ (lastT (layOff first) ++ (localS (layOff first) ++
      (tReadsT (layOff first) ++ (eqfS (layOff first) ++ (weightT first (layOff first) ++
        tailPre (layOff first) (tW first) (tV first))))))))))

/-- The returned values. -/
def layerVs (first : ℕ) : List V :=
  [.n (topV (tW first) + 305), .n (topV (tW first) + 306),
    .n (topV (tW first) + 307), .n (topV (tW first) + 308),
    .n (topV (tW first) + 309), .n (topV (tW first) + 312)]

/-- The inlined `grind_check`'s statements are the body's. -/
theorem gcInline_mem_layerT {first : ℕ} (hf : first < 2) :
    ∀ s ∈ gcInlineT 3 (layOff first + 544) (.n (layOff first + 532)) (.n (valf% «keccak_layer» "tabs")),
      s ∈ layerT first := by
  intro s hs
  have h' : s ∈ sqT first := by
    interval_cases first
    · simp only [sqT, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]; exact List.mem_append_right _ hs
    · simp only [sqT, ↓reduceIte]; exact List.mem_append_right _ hs
  unfold layerT
  simp only [List.mem_append, h', true_or, or_true]

theorem layerT_pre (first : ℕ) : layerT first = layerPre first ⧺ [.ret (layerVs first)] := by
  rw [layerT_sections, tailT_split]
  simp only [layerPre, layerVs, List.append_assoc]

theorem layer_fn {first : ℕ} (hf : first < 2) :
    ∃ fn, coreProgram.find? (layerName first) = some fn ∧ fn.body = layerT first ∧
      fn.params = [.n (valf% «keccak_layer» "fs0"), .n (valf% «keccak_layer» "fs1"), .n (valf% «keccak_layer» "fs2"), .n (valf% «keccak_layer» "fs3"), .n (valf% «keccak_layer» "fs4"), .n (valf% «keccak_layer» "p0"), .n (valf% «keccak_layer» "p1"), .n (valf% «keccak_layer» "cursor@1"), .n (valf% «keccak_layer» "y_g"), .n (valf% «keccak_layer» "step_g"), .n (valf% «keccak_layer» "rem_g"), .n (valf% «keccak_layer» "claim"), .n (valf% «keccak_layer» "out"),
        .n (valf% «keccak_layer» "iota"), .n (valf% «keccak_layer» "tabs"), .n (valf% «keccak_layer» "stream")] := by
  interval_cases first
  · exact ⟨_, find_layer265, layer_body265, rfl⟩
  · exact ⟨_, find_layer264, layer_body264, rfl⟩

theorem layer_loop {first : ℕ} (hf : first < 2) :
    coreProgram.loop (layerName first) = false := by
  interval_cases first <;> decide +kernel

/-- A dispatch. -/
def dispB : Stmt → Bool
  | .dispatch .. => true
  | _ => false

/-- The pointers the body loads through, each with a bound on the offsets. -/
def layerGroups (first : ℕ) : List (V × ℕ) :=
  [(.n (valf% «keccak_layer» "cursor@1"), 48), (.n (valf% «keccak_layer» "claim"), 22), (.n (valf% «keccak_layer» "out"), 22), (.n (layOff first + 783), 77),
    (.n (layOff first + 801), 67), (.n (layOff first + 807), 36),
    (.n (layOff first + 1240), 25), (.n (layOff first + 809), 11), (.n (tW first + 25), 25),
    (.n (topV (tW first) + 3), 7)] ++
    if first = 1 then [] else [(.n (layOff first + 1241), 11)]

/-- The pointers of the inlined `grind_check`'s table reads (`gcInline_ptrs_of_good`). -/
def grindPtrs (first : ℕ) : List V :=
  .n (layOff first + 544 + gcW 3 + 5) ::
    (List.range (gcW 3)).map fun i ↦ .n (layOff first + 544 + gcW 3 + 9 * (i + 1) + 4)

/-- The calls of the body: the eight-round loop and the remainder loop. -/
def layerCalls (first : ℕ) : List (Option V × String × List V × List V) :=
  [ (some (.n (layOff first + 787)), packLoopName first,
      [.n (layOff first + 788), .n (valf% «keccak_layer» "step_g"), .n (layOff first + 783), .n (layOff first + 781),
        .n (layOff first + 782), .n (valf% «keccak_layer» "tabs")], []),
    (some (.n (layOff first + 799)), remLoopName first,
      [.n (layOff first + 800), .n (valf% «keccak_layer» "rem_g"), .n (layOff first + 789), .n (layOff first + 793), .n (valf% «keccak_layer» "tabs"),
        .n (layOff first + 797)], [])]

/-- The inlined `grind_check`'s computed hints, its windows: the body's only computed hints not
pinned by their next atom. -/
def layerSites (first : ℕ) : List Atom :=
  (gcInlineT 3 (layOff first + 544) (.n (layOff first + 532)) (.n (valf% «keccak_layer» "tabs"))).filterMap
    fun s ↦ match s with
      | .atom a => if isComputed a then some a else none
      | _ => none

theorem layer_pinnedSites {first : ℕ} (hf : first < 2) :
    Stmt.blockNextOk (fun a ↦ isComputed a && !decide (a ∈ layerSites first)) pinsInverse
      (layerT first) = true := by
  interval_cases first <;> decide +kernel

theorem layerPre_kernel {first : ℕ} (hf : first < 2) :
    (layerPre first).all Stmt.flat = true ∧
    (layerPre first).filterMap Main.Stmt.addrS = [] ∧
    (layerPre first).filterMap Main.Stmt.allocSz =
      [(.n (layOff first + 782), .inr (.n (valf% «keccak_layer» "y_g"))), (.n (layOff first + 783), .inl 77),
        (.n (layOff first + 809), .inl 11), (.n (tW first + 25), .inl 25),
        (.n (topV (tW first) + 3), .inl 7)] ∧
    (layerPre first).all (fun s ↦ !dispB s) = true ∧
    (layerPre first).filterMap Main.Stmt.callS = layerCalls first ∧
    ((layerPre first).filterMap Stmt.loadS).all
      (fun q ↦ (layerGroups first).any (fun g ↦ g.1 == q.1 && decide (q.2 < g.2)) ||
        decide (q.1 ∈ grindPtrs first ∧ q.2 = 0)) = true := by
  interval_cases first
  all_goals exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- Without a dispatch, a statement's frame does not depend on the valuation. -/
theorem callSF_of_not_disp (σ : Val) {s : Stmt} (h : dispB s = false) :
    s.callSF σ = Main.Stmt.callS s := by
  cases s <;> simp_all [dispB, Stmt.callSF]

theorem layerPre_callSF {first : ℕ} (hf : first < 2) (σ : Val) :
    (layerPre first).filterMap (Stmt.callSF σ) = layerCalls first := by
  obtain ⟨-, -, -, hd, hc, -⟩ := layerPre_kernel hf
  rw [← hc]
  refine List.filterMap_congr fun s hs ↦ callSF_of_not_disp σ ?_
  have := List.all_eq_true.mp hd s hs
  simpa using this

theorem layerPre_disp {first : ℕ} (hf : first < 2) (σ : Val) :
    ∀ s ∈ layerPre first, DispOk σ s := by
  obtain ⟨-, -, -, hd, -, -⟩ := layerPre_kernel hf
  intro s hs
  have := List.all_eq_true.mp hd s hs
  cases s <;> simp_all [dispB, DispOk]

end
end LeanVM.Guest.B1.VerifySub
