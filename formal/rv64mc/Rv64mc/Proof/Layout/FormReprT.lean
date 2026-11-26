/-
  Rv64mc.Proof.Layout.FormReprT

  What a `Form` (`Vec<(Vec<usize>, E)>`) in memory promises its users' total proofs, over `VecReprT`'s predicates: a
  `Form` is a vector of 40-byte terms (`VecT`), each term's monomial (its first 24 bytes) a vector of words
  (`VecT`), its coefficient the next 16 bytes (`TermsT`, `FormT`); `FormsT` is `n` of them, 24 bytes apart, as a
  `Vec<Form>`'s buffer holds them. They read memory only at the `Form`'s header and in its terms' block, so a
  memory agreeing there keeps them (`FormT.keep`); a `Form` whose header and block lie below `NEXT` is kept by every
  call's frame that keeps the heap allocated before it (`FormsT.keep_below`).

  ## Main definitions

  * `TermsT`, `FormT`, `FormsT`

  ## Main results

  * `vecT_keep`, `vecT_buf`, `FormT.keep`, `FormsT.keep_below`, `FormT.foot`
-/

import Rv64mc.Proof.Runtime.VecReprT
import Rv64mc.Proof.Runtime.DropSliceT

namespace Rv64mc.Proof.Layout.FormReprT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)

variable {env : Env}

/-- **`n` terms from `q`**, 40 bytes each: each term's monomial (its first 24 bytes) a vector of words. -/
def TermsT (env : Env) (m : MachineState) (q : Word) (n : Nat) : Prop :=
  ∀ t, t < n → VecT env m (q + BitVec.ofNat 64 (40 * t)) 8

/-- **The `Form` at `a`**: a vector of 40-byte terms, each term's monomial a vector of words. -/
def FormT (env : Env) (m : MachineState) (a : Word) : Prop :=
  VecT env m a 40 ∧ TermsT env m (vecPtr m a) (vecLen m a).toNat

/-- **`n` `Form`s from `q`**, 24 bytes each, as a `Vec<Form>`'s buffer holds them. -/
def FormsT (env : Env) (m : MachineState) (q : Word) (n : Nat) : Prop :=
  ∀ i, i < n → FormT env m (q + BitVec.ofNat 64 (24 * i))

theorem vecCap_eq (m : MachineState) (a : Word) : vecCap m a = m.getMem a := by
  simp only [vecCap, Layouts.Vec.cap]; exact congrArg _ (BitVec.add_zero a)

theorem rvCapAt_eq (a : Word) : rvCapAt a = a := by
  simp only [rvCapAt, Layouts.RawVecInner.cap]; exact BitVec.add_zero a

theorem rvPtrAt_eq (a : Word) : rvPtrAt a = a + 8#64 := rfl

theorem vecPtr_eq (m : MachineState) (a : Word) : vecPtr m a = m.getMem (a + 8#64) := rfl

theorem vecLen_eq (m : MachineState) (a : Word) : vecLen m a = m.getMem (a + 16#64) := rfl

/-- A vector's header words, as numbers: `a + 8` and `a + 16` do not wrap. -/
theorem vecT_lt {m : MachineState} {a : Word} {s : Nat} (h : VecT env m a s) : a.toNat + 24 < 2 ^ 64 := by
  have := env.layout
  have := env.heapEnd.isLt
  rcases h.1 with ⟨-, h2⟩ | ⟨-, h2⟩ <;> simp only [Layouts.Vec.byteSize] at h2 <;> omega

/-- **A vector is kept** by a memory agreeing on its header, `NEXT` no lower. -/
theorem vecT_keep {m m' : MachineState} {a : Word} {s : Nat} (h : VecT env m a s)
    (hn : (env.next m).toNat ≤ (env.next m').toNat)
    (hk : ∀ b : Word, a.toNat ≤ b.toNat → b.toNat < a.toNat + 24 → m'.getMem b = m.getMem b) : VecT env m' a s := by
  have hlt := vecT_lt h
  have e8 : (a + 8#64).toNat = a.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (a + 16#64).toNat = a.toNat + 16 := toNat_add_ofNat (by omega)
  have k0 : m'.getMem a = m.getMem a := hk a (Nat.le_refl _) (by omega)
  have k8 : m'.getMem (a + 8#64) = m.getMem (a + 8#64) := hk _ (by omega) (by omega)
  have k16 : m'.getMem (a + 16#64) = m.getMem (a + 16#64) := hk _ (by omega) (by omega)
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2.keep (by rw [rvCapAt_eq, k0]) (by rw [rvPtrAt_eq, k8]) hn, ?_⟩
  rw [vecLen_eq, vecCap_eq, k16, k0]
  rwa [vecLen_eq, vecCap_eq] at h3

/-- The header's words as the vector's capacity, pointer and length. -/
theorem vecT_buf {m : MachineState} {a : Word} {s : Nat} (h : VecT env m a s) :
    BufT env m (vecLen m a) (vecPtr m a) s ∧ (vecLen m a).toNat ≤ (vecCap m a).toNat ∧
      (vecCap m a).toNat * s < 2 ^ 63 := by
  obtain ⟨-, ⟨-, -, h3, h4⟩, h5⟩ := h
  rw [rvCapAt_eq] at h3 h4
  rw [← vecCap_eq] at h3 h4
  exact ⟨Runtime.DropSliceT.BufT.of_le h3 h5, h5, h4⟩

/-- **A `Form`'s terms' block**: none, or from `0x10000000`, below `NEXT`, 8-byte aligned. -/
theorem FormT.foot {m : MachineState} {a : Word} (h : FormT env m a) :
    (vecLen m a).toNat = 0 ∨ (0x10000000 ≤ (vecPtr m a).toNat ∧
      (vecPtr m a).toNat + 40 * (vecLen m a).toNat ≤ (env.next m).toNat ∧ (vecPtr m a).toNat % 8 = 0) := by
  rcases (vecT_buf h.1).1 with h0 | ⟨h1, h2, h3⟩
  · exact .inl h0
  · unfold Env.Live at h2
    exact .inr ⟨h1, by rw [Nat.mul_comm]; exact h2, h3⟩

/-- **A `Form` is kept** by a memory agreeing on its header and on its terms' block, `NEXT` no lower. -/
theorem FormT.keep {m m' : MachineState} {a : Word} (h : FormT env m a)
    (hn : (env.next m).toNat ≤ (env.next m').toNat)
    (hk : ∀ b : Word, a.toNat ≤ b.toNat → b.toNat < a.toNat + 24 → m'.getMem b = m.getMem b)
    (hb : ∀ b : Word, (vecPtr m a).toNat ≤ b.toNat → b.toNat < (vecPtr m a).toNat + 40 * (vecLen m a).toNat →
      m'.getMem b = m.getMem b) : FormT env m' a := by
  have hlt := vecT_lt h.1
  have ep : vecPtr m' a = vecPtr m a := by
    rw [vecPtr_eq, vecPtr_eq]; exact hk _ (by rw [toNat_add_ofNat (by omega)]; omega)
      (by rw [toNat_add_ofNat (by omega)]; omega)
  have el : vecLen m' a = vecLen m a := by
    rw [vecLen_eq, vecLen_eq]; exact hk _ (by rw [toNat_add_ofNat (by omega)]; omega)
      (by rw [toNat_add_ofNat (by omega)]; omega)
  have hf := h.foot
  have hl := env.layout
  have := env.heapEnd.isLt
  refine ⟨vecT_keep h.1 hn hk, fun t ht => ?_⟩
  rw [ep, el] at *
  have hT := h.2 t ht
  rcases hf with h0 | ⟨-, h2, -⟩
  · omega
  have hnx := vecT_lt hT
  have et : (vecPtr m a + BitVec.ofNat 64 (40 * t)).toNat = (vecPtr m a).toNat + 40 * t :=
    toNat_add_ofNat (by omega)
  refine vecT_keep hT hn fun b h1 h2 => hb b (by omega) ?_
  rw [et] at h2
  have : 40 * t + 40 ≤ 40 * (vecLen m a).toNat := by omega
  omega

/-- **`Form`s below `NEXT` are kept** by a memory agreeing below `NEXT`, `NEXT` no lower. -/
theorem FormsT.keep_below {m m' : MachineState} {q : Word} {n : Nat} (h : FormsT env m q n)
    (hq : n = 0 ∨ q.toNat + 24 * n ≤ (env.next m).toNat) (hn : (env.next m).toNat ≤ (env.next m').toNat)
    (hk : ∀ b : Word, b.toNat < (env.next m).toNat → m'.getMem b = m.getMem b) : FormsT env m' q n := by
  intro i hi
  have hF := h i hi
  have hlt := vecT_lt hF.1
  have e : (q + BitVec.ofNat 64 (24 * i)).toNat = q.toNat + 24 * i := by
    rcases hq with h0 | h0
    · omega
    · exact toNat_add_ofNat (by have := env.heapEnd.isLt; have := env.layout; have := vecT_lt hF.1; omega)
  refine hF.keep hn (fun b _ h2 => hk b ?_) (fun b _ h2 => hk b ?_)
  · rcases hq with h0 | h0
    · omega
    · rw [e] at h2; omega
  · rcases hF.foot with h0 | ⟨-, h3, -⟩
    · omega
    · omega

end Rv64mc.Proof.Layout.FormReprT
