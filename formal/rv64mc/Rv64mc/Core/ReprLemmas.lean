/-
  Rv64mc.Core.ReprLemmas

  Reading values through what a proof knows of memory, in the forms `rv_sym` computes addresses in:

  * an `E` slice in the heap through a frame without `out` (`EListAt.load`): element `j`'s limbs at `p + 16 j` and
    `p + 16 j + 8`;
  * a constant table of the static data (`DataRef.Words`): the words at a template's data reference, in every memory
    where `env.Static` holds, so a proof that reads a table takes its content as a hypothesis, as it takes a callee's
    contract, and depends on the content alone. The link step proves it from `env.data` (`DataRef.Words.of_data`).
-/

import Rv64mc.Core.Repr
import Rv64mc.Link.Basic
import Rv64mc.Tactic.Frame

namespace Rv64mc

open RiscvZkvm.Rv64

theorem EListAt.load {env : Env} {top : Word} {m M : MachineState} {p : Word} {es : List (Word × Word)} {j : Nat}
    (hf : env.Frame top Tactic.F m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (h : EListAt m p es)
    (hl : env.Live m p (Layouts.E.byteSize * es.length)) (hj : j < es.length) :
    M.getMem (p + BitVec.ofNat 64 (16 * j)) = es[j].1 ∧ M.getMem (p + BitVec.ofNat 64 (16 * j) + 8#64) = es[j].2 := by
  have h' := (h.keep (Env.Frame.keeps_live hf hnx hl fun _ _ h => h)).2 j hj
  simpa [EAt, Layouts.E.c0, Layouts.E.c1, Layouts.E.byteSize] using h'

/-- **The data reference `d` holds the words `ws`** wherever the static data hold: word `k` at `d.hi + d.lo + 8 k`,
    the address the template's code computes. -/
def DataRef.Words (env : Env) (d : DataRef) (ws : List Word) : Prop :=
  ∀ m, env.Static m → ∀ k (h : k < ws.length), m.getMem (d.hi + d.lo + BitVec.ofNat 64 (8 * k)) = ws[k]

/-- The link step's proof of `DataRef.Words`: each word is one of `env.data`'s. -/
theorem DataRef.Words.of_data {env : Env} {d : DataRef} {ws : List Word}
    (h : ∀ k (hk : k < ws.length), (d.hi + d.lo + BitVec.ofNat 64 (8 * k), ws[k]) ∈ env.data) :
    DataRef.Words env d ws :=
  fun m hs k hk => env.static_data m hs _ (h k hk)

/-- Word `k` of a table, at the address `rv_sym` computes. -/
theorem DataRef.Words.get {env : Env} {d : DataRef} {ws : List Word} {m : MachineState} (hw : DataRef.Words env d ws)
    (hs : env.Static m) (k : Nat) (hk : k < ws.length) :
    m.getMem (d.hi + d.lo + BitVec.ofNat 64 (8 * k)) = ws[k] := hw m hs k hk

/-- Word `0` of a table, at the address `rv_sym` computes. -/
theorem DataRef.Words.get0 {env : Env} {d : DataRef} {ws : List Word} {m : MachineState} (hw : DataRef.Words env d ws)
    (hs : env.Static m) (hk : 0 < ws.length) : m.getMem (d.hi + d.lo) = ws[0] := by
  simpa using hw m hs 0 hk

/-- The frame's three saved3 words, below `top`. -/
def saved3 (m : MachineState) (top ra s0 s1 : Word) : MachineState :=
  ((m.setMem (top + 0xfffffffffffffff8#64) ra).setMem (top + 0xfffffffffffffff0#64) s0).setMem
    (top + 0xffffffffffffffe8#64) s1

section Saved3

variable {env : Env} {m : MachineState} {top ra s0 s1 : Word} (hlim : env.stackLimit.toNat + 24 ≤ top.toNat)
include hlim

theorem saved3_off {k : Nat} (hk : 0 < k) (hk' : k ≤ 24) :
    (top + BitVec.ofNat 64 (2 ^ 64 - k)).toNat = top.toNat - k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := top.isLt; have := env.layout; omega

/-- A word not in the frame's three slots reads as before. -/
theorem saved3_getMem {b : Word} (hb : b.toNat < top.toNat - 24 ∨ top.toNat ≤ b.toNat) :
    (saved3 m top ra s0 s1).getMem b = m.getMem b := by
  have h8 : (top + 0xfffffffffffffff8#64).toNat = top.toNat - 8 := saved3_off hlim (k := 8) (by decide) (by decide)
  have h16 : (top + 0xfffffffffffffff0#64).toNat = top.toNat - 16 := saved3_off hlim (k := 16) (by decide) (by decide)
  have h24 : (top + 0xffffffffffffffe8#64).toNat = top.toNat - 24 := saved3_off hlim (k := 24) (by decide) (by decide)
  have n8 : b ≠ top + 0xfffffffffffffff8#64 := fun h => by rw [h, h8] at hb; omega
  have n16 : b ≠ top + 0xfffffffffffffff0#64 := fun h => by rw [h, h16] at hb; omega
  have n24 : b ≠ top + 0xffffffffffffffe8#64 := fun h => by rw [h, h24] at hb; omega
  simp only [saved3, MachineState.getMem_setMem_ne n8, MachineState.getMem_setMem_ne n16,
    MachineState.getMem_setMem_ne n24]

theorem next_saved3 : env.next (saved3 m top ra s0 s1) = env.next m := by
  have := env.layout
  unfold Env.next
  exact saved3_getMem hlim (by omega)

theorem frame_saved3 {out : Word → Prop} (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) :
    env.Frame top out m (saved3 m top ra s0 s1) := by
  refine ⟨by rw [next_saved3 hlim]; exact Nat.le_refl _, by rw [next_saved3 hlim]; exact hnx, fun b hb => ?_⟩
  refine saved3_getMem hlim ?_
  rcases Nat.lt_or_ge b.toNat (top.toNat - 24) with h | h
  · exact Or.inl h
  · rcases Nat.lt_or_ge b.toNat top.toNat with h' | h'
    · exact absurd (Or.inl ⟨by omega, h'⟩) hb
    · exact Or.inr h'

theorem static_saved3 (hs : env.Static m) : env.Static (saved3 m top ra s0 s1) :=
  env.static_frame m _ (fun b _ hb => saved3_getMem hlim (by have := env.layout; omega)) hs

theorem saved3_ra : (saved3 m top ra s0 s1).getMem (top + 0xfffffffffffffff8#64) = ra := by
  have h8 : (top + 0xfffffffffffffff8#64).toNat = top.toNat - 8 := saved3_off hlim (k := 8) (by decide) (by decide)
  have h16 : (top + 0xfffffffffffffff0#64).toNat = top.toNat - 16 := saved3_off hlim (k := 16) (by decide) (by decide)
  have h24 : (top + 0xffffffffffffffe8#64).toNat = top.toNat - 24 := saved3_off hlim (k := 24) (by decide) (by decide)
  have n16 : top + 0xfffffffffffffff8#64 ≠ top + 0xfffffffffffffff0#64 := fun h => by
    have := congrArg BitVec.toNat h; rw [h8, h16] at this; omega
  have n24 : top + 0xfffffffffffffff8#64 ≠ top + 0xffffffffffffffe8#64 := fun h => by
    have := congrArg BitVec.toNat h; rw [h8, h24] at this; omega
  simp only [saved3, MachineState.getMem_setMem_ne n24, MachineState.getMem_setMem_ne n16,
    MachineState.getMem_setMem_eq]

theorem saved3_s0 : (saved3 m top ra s0 s1).getMem (top + 0xfffffffffffffff0#64) = s0 := by
  have h16 : (top + 0xfffffffffffffff0#64).toNat = top.toNat - 16 := saved3_off hlim (k := 16) (by decide) (by decide)
  have h24 : (top + 0xffffffffffffffe8#64).toNat = top.toNat - 24 := saved3_off hlim (k := 24) (by decide) (by decide)
  have n24 : top + 0xfffffffffffffff0#64 ≠ top + 0xffffffffffffffe8#64 := fun h => by
    have := congrArg BitVec.toNat h; rw [h16, h24] at this; omega
  simp only [saved3, MachineState.getMem_setMem_ne n24, MachineState.getMem_setMem_eq]

omit hlim in
theorem saved3_s1 : (saved3 m top ra s0 s1).getMem (top + 0xffffffffffffffe8#64) = s1 := by
  simp only [saved3, MachineState.getMem_setMem_eq]

end Saved3

end Rv64mc
