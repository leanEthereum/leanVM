/-
  Rv64mc.Proof.Layout.FlushesMoveT

  A `Flushes` of `Form`s (`PairFormT.FlushesFormT`) moved. A `flushes_*` builder returns its `Flushes` by copying
  its 48 bytes from a frame slot into `sret`, and `tables` copies each into a frame slot and then into a `Table`:
  the copy at `d` of the `Flushes` at `a`, its footprint kept, is a `Flushes` of `Form`s with the same buffers and
  the same footprint (`move`).

  The footprint of a `Flushes` (`FFoot`) is both buffers, to their capacity, and every element's
  (`ExtendTrustedT.InFoot`: its `Form`s' headers and their terms' blocks). It lies below `NEXT` (`FFoot.lt`), so a
  memory agreeing below `NEXT` keeps it (`move_below`).

  ## Main definitions

  * `FFoot`

  ## Main results

  * `FFoot.lt`, `elems_move`, `move`, `move_below`
-/

import Rv64mc.Proof.Layout.StateDerivedT

namespace Rv64mc.Proof.Layout.FlushesMoveT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Proof.Layout.FromElemVecFormT (VecFormT)
open Rv64mc.Proof.Layout.ExtendTrustedT (InFoot VecFormT.foot_lt VecFormT.keep')
open Rv64mc.Proof.Layout.PairT (BufsApart)
open Rv64mc.Proof.Layout.PairFormT (lo hi HeldT ElemsHeldT FlushesFormT vecT_bufCap)

variable {env : Env}

/-- **`x` is in the footprint of the `Flushes` at `a`**: in one of its two buffers (to their capacity), or in an
    element's footprint. -/
def FFoot (m : MachineState) (a x : Word) : Prop :=
  (lo m a ≤ x.toNat ∧ x.toNat < hi m a) ∨ (lo m (a + 24#64) ≤ x.toNat ∧ x.toNat < hi m (a + 24#64)) ∨
    (∃ i, i < (vecLen m a).toNat ∧ InFoot m (vecPtr m a + BitVec.ofNat 64 (24 * i)) x) ∨
    ∃ i, i < (vecLen m (a + 24#64)).toNat ∧ InFoot m (vecPtr m (a + 24#64) + BitVec.ofNat 64 (24 * i)) x

/-- A buffer's words lie below `NEXT`. -/
theorem buf_lt {m : MachineState} {v : Word} {x : Nat} (hV : VecT env m v 24) (h1 : lo m v ≤ x) (h2 : x < hi m v) :
    x < (env.next m).toNat := by
  unfold lo at h1
  unfold hi at h2
  rcases vecT_bufCap hV with h0 | ⟨-, h5, -⟩
  · rw [h0] at h2; omega
  · unfold Env.Live at h5; rw [Nat.mul_comm] at h5; omega

/-- **A `Flushes`' footprint lies below `NEXT`.** -/
theorem FFoot.lt {m : MachineState} {a x : Word} (h : FlushesFormT env m a) (hx : FFoot m a x) :
    x.toNat < (env.next m).toNat := by
  obtain ⟨hV1, hV2, -, hE1, hE2⟩ := h
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨i, hi, hx⟩ | ⟨i, hi, hx⟩
  · exact buf_lt hV1 h1 h2
  · exact buf_lt hV2 h1 h2
  · exact VecFormT.foot_lt (hE1 i hi).1 hx
  · exact VecFormT.foot_lt (hE2 i hi).1 hx

/-- **One vector's elements moved**: the vector at `v'` in `M` has the buffer of the one at `v` in `m`, whose words
    and elements' footprints `M` keeps; the `Flushes` at `d` in `M` has the buffers of the one at `a` in `m`. Each
    element is held, with no more footprint. -/
theorem elems_move {m M : MachineState} {a d v v' : Word} (hV : VecT env m v 24) (h : ElemsHeldT env m a v)
    (hn : (env.next m).toNat ≤ (env.next M).toNat) (ep : vecPtr M v' = vecPtr m v) (el : vecLen M v' = vecLen m v)
    (hb : ∀ x : Word, lo m v ≤ x.toNat → x.toNat < hi m v → M.getMem x = m.getMem x)
    (hf : ∀ i, i < (vecLen m v).toNat → ∀ x : Word, InFoot m (vecPtr m v + BitVec.ofNat 64 (24 * i)) x →
      M.getMem x = m.getMem x)
    (hlo : lo M d = lo m a ∧ hi M d = hi m a ∧ lo M (d + 24#64) = lo m (a + 24#64) ∧
      hi M (d + 24#64) = hi m (a + 24#64)) :
    ElemsHeldT env M d v' ∧ ∀ i, i < (vecLen m v).toNat → ∀ x : Word,
      InFoot M (vecPtr m v + BitVec.ofNat 64 (24 * i)) x → InFoot m (vecPtr m v + BitVec.ofNat 64 (24 * i)) x := by
  have hlc := (FormReprT.vecT_buf hV).2.1
  have hone : ∀ i, i < (vecLen m v).toNat → HeldT env M d (vecPtr m v + BitVec.ofNat 64 (24 * i)) ∧
      ∀ x : Word, InFoot M (vecPtr m v + BitVec.ofNat 64 (24 * i)) x →
        InFoot m (vecPtr m v + BitVec.ofNat 64 (24 * i)) x := fun i hi' => by
    have hs := h i hi'
    obtain ⟨e, -⟩ := FromElemVecFormT.buf_word hV hi'
    obtain ⟨hv, hsub⟩ := VecFormT.keep' hs.1 hn (fun b h1 h2 => hb b (by unfold lo; omega) (by
      unfold hi; rw [e] at h2; have : 24 * i + 24 ≤ 24 * (vecCap m v).toNat := by omega
      omega)) (hf i hi')
    obtain ⟨l1, h1, l2, h2⟩ := hlo
    refine ⟨⟨hv, fun x hx => ?_, fun x hx => ?_⟩, hsub⟩
    · rw [l1, h1]; exact hs.2.1 x (hsub x hx)
    · rw [l2, h2]; exact hs.2.2 x (hsub x hx)
  refine ⟨fun i hi' => ?_, fun i hi' => (hone i hi').2⟩
  rw [el] at hi'
  rw [ep]
  exact (hone i hi').1

/-- **A `Flushes` of `Form`s moved**: its six words copied from `a` to `d`, in a window and 8-byte aligned, its
    footprint kept, `NEXT` no lower. The copy has the same buffers and no more footprint. -/
theorem move {m M : MachineState} {a d : Word} (h : FlushesFormT env m a)
    (hn : (env.next m).toNat ≤ (env.next M).toNat) (hw : InWin env d 48) (hal : d.toNat % 8 = 0)
    (h0 : M.getMem d = m.getMem a) (h8 : M.getMem (d + 8#64) = m.getMem (a + 8#64))
    (h16 : M.getMem (d + 16#64) = m.getMem (a + 16#64)) (h24 : M.getMem (d + 24#64) = m.getMem (a + 24#64))
    (h32 : M.getMem (d + 32#64) = m.getMem (a + 32#64)) (h40 : M.getMem (d + 40#64) = m.getMem (a + 40#64))
    (hf : ∀ x : Word, FFoot m a x → M.getMem x = m.getMem x) :
    FlushesFormT env M d ∧ (∀ x : Word, FFoot M d x → FFoot m a x) ∧
      (lo M d = lo m a ∧ hi M d = hi m a ∧ lo M (d + 24#64) = lo m (a + 24#64) ∧
        hi M (d + 24#64) = hi m (a + 24#64)) := by
  obtain ⟨hV1, hV2, hBA, hE1, hE2⟩ := h
  have hwlt : d.toNat + 48 < 2 ^ 64 := by
    have := env.heapEnd.isLt; unfold InWin at hw; omega
  have ed : (d + 24#64).toNat = d.toNat + 24 := toNat_add_ofNat (by omega)
  have d8 : d + 24#64 + 8#64 = d + 32#64 := by rw [BitVec.add_assoc]; rfl
  have d16 : d + 24#64 + 16#64 = d + 40#64 := by rw [BitVec.add_assoc]; rfl
  have a8 : a + 24#64 + 8#64 = a + 32#64 := by rw [BitVec.add_assoc]; rfl
  have a16 : a + 24#64 + 16#64 = a + 40#64 := by rw [BitVec.add_assoc]; rfl
  have W1 : VecT env M d 24 := CloneFormsT.vecT_copy hV1 (InWin.sub hw (Nat.le_refl _) (by omega)) hal hn h0 h8 h16
  have W2 : VecT env M (d + 24#64) 24 := CloneFormsT.vecT_copy hV2 (InWin.sub hw (by omega) (by omega))
    (by omega) hn h24 (by rw [d8, a8]; exact h32) (by rw [d16, a16]; exact h40)
  have p1 : vecPtr M d = vecPtr m a := by rw [vecPtr_eq, vecPtr_eq, h8]
  have n1 : vecLen M d = vecLen m a := by rw [vecLen_eq, vecLen_eq, h16]
  have p2 : vecPtr M (d + 24#64) = vecPtr m (a + 24#64) := by rw [vecPtr_eq, vecPtr_eq, d8, a8, h32]
  have n2 : vecLen M (d + 24#64) = vecLen m (a + 24#64) := by rw [vecLen_eq, vecLen_eq, d16, a16, h40]
  have hlo : lo M d = lo m a ∧ hi M d = hi m a ∧ lo M (d + 24#64) = lo m (a + 24#64) ∧
      hi M (d + 24#64) = hi m (a + 24#64) := by
    unfold lo hi
    simp only [vecPtr_eq, vecCap_eq, d8, a8, h0, h8, h24, h32]
    exact ⟨trivial, trivial, trivial, trivial⟩
  obtain ⟨G1, s1⟩ := elems_move hV1 hE1 hn p1 n1 (fun x h1 h2 => hf x (.inl ⟨h1, h2⟩))
    (fun i hi x hx => hf x (.inr (.inr (.inl ⟨i, hi, hx⟩)))) hlo
  obtain ⟨G2, s2⟩ := elems_move hV2 hE2 hn p2 n2 (fun x h1 h2 => hf x (.inr (.inl ⟨h1, h2⟩)))
    (fun i hi x hx => hf x (.inr (.inr (.inr ⟨i, hi, hx⟩)))) hlo
  refine ⟨⟨W1, W2, ?_, G1, G2⟩, fun x hx => ?_, hlo⟩
  · unfold BufsApart
    rw [h0, h8, h24, h32]
    exact hBA
  · obtain ⟨l1, i1, l2, i2⟩ := hlo
    rcases hx with hx | hx | ⟨i, hi, hx⟩ | ⟨i, hi, hx⟩
    · rw [l1, i1] at hx; exact .inl hx
    · rw [l2, i2] at hx; exact .inr (.inl hx)
    · rw [n1] at hi; rw [p1] at hx; exact .inr (.inr (.inl ⟨i, hi, s1 i hi x hx⟩))
    · rw [n2] at hi; rw [p2] at hx; exact .inr (.inr (.inr ⟨i, hi, s2 i hi x hx⟩))

/-- **A `Flushes` of `Form`s moved**, in a memory agreeing below `NEXT`. -/
theorem move_below {m M : MachineState} {a d : Word} (h : FlushesFormT env m a)
    (hn : (env.next m).toNat ≤ (env.next M).toNat) (hw : InWin env d 48) (hal : d.toNat % 8 = 0)
    (h0 : M.getMem d = m.getMem a) (h8 : M.getMem (d + 8#64) = m.getMem (a + 8#64))
    (h16 : M.getMem (d + 16#64) = m.getMem (a + 16#64)) (h24 : M.getMem (d + 24#64) = m.getMem (a + 24#64))
    (h32 : M.getMem (d + 32#64) = m.getMem (a + 32#64)) (h40 : M.getMem (d + 40#64) = m.getMem (a + 40#64))
    (hk : ∀ x : Word, x.toNat < (env.next m).toNat → M.getMem x = m.getMem x) :
    FlushesFormT env M d ∧ (∀ x : Word, FFoot M d x → FFoot m a x) ∧
      (lo M d = lo m a ∧ hi M d = hi m a ∧ lo M (d + 24#64) = lo m (a + 24#64) ∧
        hi M (d + 24#64) = hi m (a + 24#64)) :=
  move h hn hw hal h0 h8 h16 h24 h32 h40 fun x hx => hk x (FFoot.lt h hx)

end Rv64mc.Proof.Layout.FlushesMoveT

/-- info: 'Rv64mc.Proof.Layout.FlushesMoveT.move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.FlushesMoveT.move
