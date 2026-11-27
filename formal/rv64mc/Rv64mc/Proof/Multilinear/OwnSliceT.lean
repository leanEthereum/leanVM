/-
  Rv64mc.Proof.Multilinear.OwnSliceT

  A slice of `E`s a caller may pass to the multilinear leaves (`eq_eval`, `poly_eval`, `index_mle`,
  `padding_weight`, `ring_psi`): none, or owned by the caller (`Env.Owned`: allocated before, below `NEXT`, or in a
  caller's frame, at or above the callee's stack pointer), in a window and 8-byte aligned (`OwnSlice`). The leaves'
  first total contracts keep their partial `Pre`'s `Env.Live`, which says nothing usable of an empty vector's
  dangling pointer or of a slice in a caller's frame; `OwnSlice` admits both, and follows from what those contracts
  ask (`OwnSlice.of_live`), from a vector's buffer (`OwnSlice.of_bufT`) and from a slice in the caller's frame
  (`OwnSlice.of_frame`).

  ## Main definitions

  * `OwnSlice`

  ## Main results

  * `OwnSlice.of_live`, `OwnSlice.of_bufT`, `OwnSlice.of_frame`, `OwnSlice.frame`, `OwnSlice.drop`,
    `OwnSlice.take`, `OwnSlice.load`, `OwnSlice.keep`, `OwnSlice.end_lt`, `mono_pre`, `EListAt.drop`
-/

import Rv64mc.Proof.Multilinear.DotOwnT
import Rv64mc.Proof.Runtime.VecReprT

namespace Rv64mc.Proof.Multilinear.OwnSliceT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT)

/-- **A slice of `n` `E`s at `a` a caller may pass**, the callee's stack pointer `top`: none, or owned by the caller,
    in a window and 8-byte aligned. -/
def OwnSlice (env : Env) (m : MachineState) (top a : Word) (n : Nat) : Prop :=
  n = 0 ∨ (env.Owned m top a (16 * n) ∧ InWin env a (16 * n) ∧ a.toNat % 8 = 0)

namespace OwnSlice

variable {env : Env} {m m' : MachineState} {top a : Word} {n : Nat}

/-- What the leaves' first total contracts ask (`Live`, and a nonempty slice in a window, aligned) gives it. -/
theorem of_live (hl : env.Live m a (Layouts.E.byteSize * n))
    (hw : n = 0 ∨ (InWin env a (16 * n) ∧ a.toNat % 8 = 0)) : OwnSlice env m top a n :=
  hw.imp_right fun h => ⟨DotOwnT.owned_of_live hl, h⟩

/-- The first `n` elements of a vector's buffer of capacity `cap`. -/
theorem of_bufT {cap : Word} (h : BufT env m cap a 16) (hn : n ≤ cap.toNat)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) : OwnSlice env m top a n := by
  rcases h with h | ⟨h1, h2, h3⟩
  · exact .inl (by omega)
  · unfold Env.Live at h2
    have := (env.next m).isLt
    exact .inr ⟨⟨.inl (by omega), by omega⟩, .inl ⟨h1, by omega⟩, h3⟩

/-- A slice in the caller's frame: at or above the callee's stack pointer, in the stack window, 8-byte aligned. -/
theorem of_frame (ht : top.toNat ≤ a.toNat) (hlim : env.stackLimit.toNat ≤ a.toNat)
    (hhi : a.toNat + 16 * n ≤ 0xc0000000) (hal : a.toNat % 8 = 0) : OwnSlice env m top a n :=
  .inr ⟨⟨.inr ht, by omega⟩, .inr ⟨hlim, hhi⟩, hal⟩

/-- Kept by a call's frame, for a callee from a stack pointer no higher. -/
theorem frame {top' t : Word} {out : Word → Prop} (h : OwnSlice env m top a n) (hf : env.Frame t out m m')
    (ht : top'.toNat ≤ top.toNat) : OwnSlice env m' top' a n :=
  h.imp_right fun ⟨ho, hw⟩ => ⟨ho.frame hf ht, hw⟩

/-- The slice's last `n - k` elements. -/
theorem drop {k : Nat} (h : OwnSlice env m top a n) (hk : k ≤ n) :
    OwnSlice env m top (a + BitVec.ofNat 64 (16 * k)) (n - k) := by
  by_cases hkn : n - k = 0
  · exact .inl hkn
  rcases h with h | ⟨⟨ho, hlt⟩, hw, hal⟩
  · omega
  have hlt' : a.toNat + 16 * k < 2 ^ 64 := by omega
  have ha : (a + BitVec.ofNat 64 (16 * k)).toNat = a.toNat + 16 * k := toNat_add_ofNat hlt'
  have e : 16 * (n - k) = 16 * n - 16 * k := by omega
  refine .inr ⟨⟨?_, by rw [ha]; omega⟩, ?_, by rw [ha]; omega⟩
  · rcases ho with ho | ho
    · exact .inl (by rw [ha]; omega)
    · exact .inr (by rw [ha]; omega)
  · unfold InWin at hw ⊢; rw [ha]; omega

/-- The slice's first `k` elements. -/
theorem take {k : Nat} (h : OwnSlice env m top a n) (hk : k ≤ n) : OwnSlice env m top a k := by
  by_cases hk0 : k = 0
  · exact .inl hk0
  rcases h with h | ⟨⟨ho, hlt⟩, hw, hal⟩
  · omega
  refine .inr ⟨⟨?_, by omega⟩, by unfold InWin at hw ⊢; omega, hal⟩
  rcases ho with ho | ho
  · exact .inl (by omega)
  · exact .inr ho

/-- A nonempty slice ends below `2 ^ 64` with room for an end pointer past it. -/
theorem end_lt (h : OwnSlice env m top a n) (hn : n ≠ 0) : a.toNat + 16 * n + 8 < 2 ^ 64 := by
  rcases h with h | ⟨-, hw, -⟩
  · omega
  · have := env.layout; have := env.stackLimit.isLt; unfold InWin at hw; omega

/-- **An element of the slice, read through a frame that writes nothing outside its stack.** -/
theorem load {M : MachineState} {es : List (Word × Word)} {j : Nat} (h : OwnSlice env m top a es.length)
    (hf : env.Frame top Tactic.F m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (he : EListAt m a es) (hj : j < es.length) :
    M.getMem (a + BitVec.ofNat 64 (16 * j)) = es[j].1 ∧ M.getMem (a + BitVec.ofNat 64 (16 * j) + 8#64) = es[j].2 := by
  rcases h with h | ⟨ho, -⟩
  · omega
  · exact DotOwnT.EListAt.load_owned hf hnx hlim he ho hj

/-- **The slice's elements, kept by a frame that writes nothing outside its stack.** -/
theorem keep {M : MachineState} {es : List (Word × Word)} (h : OwnSlice env m top a es.length)
    (hf : env.Frame top Tactic.F m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (he : EListAt m a es) : EListAt M a es := by
  rcases h with h | ⟨ho, -⟩
  · exact ⟨he.1, fun k hk => by omega⟩
  · rcases ho.1 with hl | ha
    · exact he.keep (Env.Frame.keeps_live hf hnx hl fun _ _ h => h)
    · exact he.keep (Env.Frame.keeps_above hf hlim ha fun _ _ h => h)

end OwnSlice

/-- **A contract holds from a stronger precondition**, as the leaves' second contracts give their first. -/
theorem mono_pre {env : Env} {p : Lprog (Op Reg) Reg} {f need : Nat} {Pre Pre' : (Reg → Word) → MachineState → Prop}
    {Post : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}
    {Out : (Reg → Word) → MachineState → Word → Prop}
    {Stop : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}
    (h : HoldsT env p f need Pre Post Out Stop) (hp : ∀ regs m, Pre' regs m → Pre regs m) :
    HoldsT env p f need Pre' Post Out Stop :=
  Isa.TContract.mono h (fun _ _ _ _ ⟨⟨he, hs, hst, hn, hP, hal⟩, hw⟩ => ⟨⟨he, hs, hst, hn, hp _ _ hP, hal⟩, hw⟩)
    (fun _ _ _ _ _ _ _ h => h) fun _ _ _ _ _ _ _ h => h

/-- The last elements of a slice, from the `k`th. -/
theorem EListAt.drop {m : MachineState} {a : Word} {es : List (Word × Word)} (h : EListAt m a es) (k : Nat) :
    EListAt m (a + BitVec.ofNat 64 (16 * k)) (es.drop k) := by
  by_cases hk : es.length ≤ k
  · rw [List.drop_eq_nil_of_le hk]
    exact ⟨by have := h.1; simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]; exact BitVec.isLt _, nofun⟩
  have h1 := h.1
  simp only [Layouts.E.byteSize] at h1
  have ha : (a + BitVec.ofNat 64 (16 * k)).toNat = a.toNat + 16 * k := toNat_add_ofNat (by omega)
  refine ⟨by simp only [Layouts.E.byteSize, List.length_drop]; rw [ha]; omega, fun j hj => ?_⟩
  simp only [List.length_drop] at hj
  have e := h.2 (k + j) (by omega)
  rw [List.getElem_drop]
  have : a + BitVec.ofNat 64 (16 * k) + BitVec.ofNat 64 (Layouts.E.byteSize * j) =
      a + BitVec.ofNat 64 (Layouts.E.byteSize * (k + j)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; simp only [Layouts.E.byteSize]; omega
  rw [this]; exact e

end Rv64mc.Proof.Multilinear.OwnSliceT
