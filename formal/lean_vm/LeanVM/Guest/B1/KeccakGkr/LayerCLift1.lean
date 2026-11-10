/-
  LeanVM.Guest.B1.KeccakGkr.LayerCLift1

  `keccak_layer`'s placement facts, by kernel evaluation: its body a flat list then its return,
  its buffers, its calls, and the pointers its loads go through.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCG
public import LeanVM.Guest.B1.KeccakGkr.FlatF

/-!
# A layer's placement facts

`layerPre first odd`: the body but its return (`layerT_pre`); it is flat (`layerPre_flat`), places
no run (`layerPre_addrs`), allocates the pack challenges (`y` words), the round records (`128`),
the local point (`11`), the next claim's lanes (`25`) and flips (`7`) (`layerPre_alloc`), calls
the grind's `grind_check` and the two pack loops (`layerPre_calls`), and loads only through the
pointers `layerGroups` below their bounds (`layerPre_loads`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory

@[expose] public section

/-- The body but its return. -/
def layerPre (first : ℕ) : List Stmt :=
  secA1 first ++ (secA2 first ++ (rmfeBlockT (layOff first) ++ (hornerS first ++
    (packSetupT (layOff first) first ++ (lastT (layOff first) ++ (localS (layOff first) ++
      (tReadsT (layOff first) ++ (eqfS (layOff first) ++ (weightT first (layOff first) ++
        tailPre (layOff first) (tW first) (tV first))))))))))

/-- The returned values. -/
def layerVs (first : ℕ) : List V :=
  [.n (topV (tW first) + 305), .n (topV (tW first) + 306),
    .n (topV (tW first) + 307), .n (topV (tW first) + 308),
    .n (topV (tW first) + 309), .n (topV (tW first) + 312)]

theorem layerT_pre (first : ℕ) : layerT first = layerPre first ++ [.ret (layerVs first)] := by
  rw [layerT_sections, tailT_split]
  simp only [layerPre, layerVs, List.append_assoc]

theorem layer_fn {first : ℕ} (hf : first < 2) :
    ∃ fn, coreProgram.find? (layerName first) = some fn ∧ fn.body = layerT first ∧
      fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 12,
        .n 13, .n 14] := by
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
  [(.n 7, 48), (.n 11, 22), (.n 12, 22), (.n (layOff first + 720), 128),
    (.n (layOff first + 739), 113), (.n (layOff first + 745), 36),
    (.n (layOff first + 1190), 25), (.n (layOff first + 748), 11), (.n (tW first + 27), 25),
    (.n (topV (tW first) + 3), 7)] ++
    if first = 1 then [] else [(.n (layOff first + 1191), 11)]

/-- The calls of the body: the grind's `grind_check`, the eight-round loop and the remainder
loop. -/
def layerCalls (first : ℕ) : List (Option V × String × List V × List V) :=
  [(none, grindCheckName 3, [.n (layOff first + 532), .n 14], []),
    (some (.n (layOff first + 725)), packLoopName first,
      [.n (layOff first + 726), .n 9, .n (layOff first + 720), .n (layOff first + 718),
        .n (layOff first + 719), .n 14], []),
    (some (.n (layOff first + 737)), remLoopName first,
      [.n (layOff first + 738), .n 10, .n (layOff first + 727), .n (layOff first + 731), .n 14,
        .n (layOff first + 735)], [])]

theorem layerPre_kernel {first : ℕ} (hf : first < 2) :
    (layerPre first).all Stmt.flat = true ∧
    (layerPre first).filterMap Main.Stmt.addrS = [] ∧
    (layerPre first).filterMap Main.Stmt.allocSz =
      [(.n (layOff first + 719), .inr (.n 8)), (.n (layOff first + 720), .inl 128),
        (.n (layOff first + 748), .inl 11), (.n (tW first + 27), .inl 25),
        (.n (topV (tW first) + 3), .inl 7)] ∧
    (layerPre first).all (fun s ↦ !dispB s) = true ∧
    (layerPre first).filterMap Main.Stmt.callS = layerCalls first ∧
    ((layerPre first).filterMap Stmt.loadS).all
      (fun q ↦ (layerGroups first).any fun g ↦ g.1 == q.1 && decide (q.2 < g.2)) = true := by
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
