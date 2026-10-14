module

public import LeanVMCircuits.Xmss.Paths
public import LeanVMCircuits.Sphincs.Words

@[expose] public section

/-!
# leanSPHINCS chains on the dynamic bus

Layer `lay` of signature `j` runs `Xmss.Circuit.chains` over the base `tweak0(1, lay, 0)` and the tag `3 j + lay`
with 103 steps, so its chain steps are `Words.chainStep` (`walk_stepHash`), and every layer adds 103 `STEP` and 42
`LINK` rows (`count_layer`); the circuit of `n` signatures has `309 n` and `126 n` (`count_circuit`).
-/

namespace LeanVMCircuits.Sphincs

open LeanVMCircuits.Rec (tweakWord)
open LeanVMCircuits.Rec.Model
open LeanVMCircuits.Xmss (Frame Count walk stepHash)
open Xmss.Words (W Dig)

theorem tweak0_chain (lay p : ℕ) : Circuit.tweak0 1 lay p = tweakWord (Circuit.tweak0 1 lay 0) p := by
  unfold Circuit.tweak0 tweakWord; ring

/-- leanSPHINCS's chain steps are `stepHash` over the base `tweak0(1, lay, 0)` and the layer's key word. -/
theorem walk_stepHash (lay tau e : ℕ) (P0 P1 : W) (i d : ℕ) (v : Dig) :
    walk (stepHash (Circuit.tweak0 1 lay 0) (BitVec.ofNat 64 (tau % 2 ^ 32 + e % 2 ^ 32 * 2 ^ 32)) P0 P1) i d v 7 =
      Words.chainFrom lay tau e i (P0, P1) d v := by
  have h : stepHash (Circuit.tweak0 1 lay 0) (BitVec.ofNat 64 (tau % 2 ^ 32 + e % 2 ^ 32 * 2 ^ 32)) P0 P1 =
      fun c s v => Words.chainStep lay tau e c s (P0, P1) v := by
    funext c s v
    simp only [stepHash, Words.chainStep, Words.th, Words.tweak, ← tweak0_chain, List.cons_append, List.nil_append]
  rw [h]
  rfl

/-! The rows the circuit adds. -/

theorem sp_frame_indexWord (tau j : List ℕ) : Frame (Circuit.indexWord tau j) := by
  unfold Circuit.indexWord; frame
theorem sp_frame_th (tw0 tw1 : ℕ) (pp payload : List ℕ) : Frame (Circuit.th tw0 tw1 pp payload) := by
  unfold Circuit.th; frame

macro_rules | `(tactic| frame_atom) => `(tactic| exact sp_frame_indexWord _ _)
macro_rules | `(tactic| frame_atom) => `(tactic| exact sp_frame_th _ _ _ _)

theorem sp_frame_level (tw0 tw1 bit node : ℕ) (pp : List ℕ) : Frame (Circuit.level tw0 tw1 bit node pp) := by
  unfold Circuit.level; frame

macro_rules | `(tactic| frame_atom) => `(tactic| exact sp_frame_level _ _ _ _ _)

theorem sp_frame_fold (ty lay : ℕ) (tauBits jBits : List ℕ) (top : ℕ) (pp : List ℕ) (leaf : ℕ) :
    Frame (Circuit.fold ty lay tauBits jBits top pp leaf) := by
  unfold Circuit.fold; frame

macro_rules | `(tactic| frame_atom) => `(tactic| exact sp_frame_fold _ _ _ _ _ _ _)

theorem sp_frame_fts (idxBits : List ℕ) (us : List (List ℕ)) (top : ℕ) (pp : List ℕ) :
    Frame (Circuit.fts idxBits us top pp) := by
  unfold Circuit.fts; frame

macro_rules | `(tactic| frame_atom) => `(tactic| exact sp_frame_fts _ _ _ _)

/-- A layer adds its chains' 103 `STEP` and 42 `LINK` rows. -/
theorem count_layer (j lay : ℕ) (idxBits pp : List ℕ) (msg : ℕ) :
    Count (Circuit.layer j lay idxBits pp msg) 103 42 := by
  unfold Circuit.layer
  repeat (first
    | with_reducible exact Count.bind_frame (Xmss.count_chains _ _ _ _ _ _) fun _ => by frame
    | with_reducible refine Count.frame_bind (by frame) fun _ => ?_
    | dsimp only)

/-- A signature adds its three layers' rows. The prefix's frames are checked to close, so that the loop over the
layers is met at its own bind. -/
theorem count_signature (j : ℕ) : Count (Circuit.signature j) 309 126 := by
  unfold Circuit.signature
  repeat (first
    | (with_reducible refine Count.frame_bind ?_ fun _ => ?_
       · frame
         done)
    | dsimp only)
  refine Count.bind_frame ((Count.forIn _ _ _ (a := 103) (c := 42) (fun _ _ => ?_) fun _ _ => ?_).congr ?_ ?_)
    fun _ => ?_
  · exact Count.bind_frame (count_layer _ _ _ _ _) fun _ => Frame.pure' _
  · yields
  · simp
  · simp
  · frame

/-- The circuit of `n` signatures has `309 n` `STEP` rows and `126 n` `LINK` rows. -/
theorem count_circuit (n : ℕ) : Count (Circuit.circuit n) (309 * n) (126 * n) := by
  unfold Circuit.circuit
  refine (Count.bind_frame (Count.forIn _ _ _ (a := 309) (c := 126) (fun j _ => ?_) fun _ _ => by yields)
    fun _ => Frame.pure' _).congr (by simp) (by simp)
  exact Count.bind_frame (count_signature j) fun _ => Frame.pure' _

end LeanVMCircuits.Sphincs
