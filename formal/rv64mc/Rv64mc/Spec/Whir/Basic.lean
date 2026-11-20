/-
  Rv64mc.Spec.Whir.Basic

  What the WHIR family's contracts share:

  * words of the image's constant tables (`DataWords`, read from `Env.data`, so in place wherever `env.Static`
    holds, at every call's entry and return);
  * a `Result<E, VerifierError>` returned through the caller's slot (`sret`, in `a0`): `ResultEAt` (the transcript
    family's), `Ok` with the value's limbs where the mirror returns, `Err` where it fails, and the slot as what the
    call writes (`SretOut`).
-/

import Rv64mc.Spec.Transcript.Repr

namespace Rv64mc.Spec.Whir

open RiscvZkvm.Rv64 LeanVM.Parameters

/-- **The words `ws` from `a` are constants of the image**: word `k` at `a + 8k`, each in `env.data`. -/
def DataWords (env : Env) (a : Word) (ws : List Word) : Prop :=
  ∀ k (h : k < ws.length), (a + BitVec.ofNat 64 (8 * k), ws[k]) ∈ env.data

/-- A constant word is in place in every state where `env.Static` holds. -/
theorem DataWords.getMem {env : Env} {a : Word} {ws : List Word} (h : DataWords env a ws) {m : MachineState}
    (hs : env.Static m) {k : Nat} (hk : k < ws.length) : m.getMem (a + BitVec.ofNat 64 (8 * k)) = ws[k] :=
  env.static_data m hs _ (h k hk)

-- `Result<E, VerifierError>` through `sret` is the transcript family's `ResultEAt`.
export Rv64mc.Spec.Transcript (ResultEAt)

/-- A function returning through `sret` (in `a0`) writes the `n` bytes of its slot. -/
def SretOut (n : Nat) (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop := InRange (regs .x10) n b

/-- **A fresh `Vec<u64>` (or `Vec<K>`, `Vec<usize>`) of `ws` at `a`**, allocated between `m` and `m'` (or empty,
    its pointer the alignment). -/
def FreshVecW (env : Env) (m m' : MachineState) (a : Word) (ws : List Word) : Prop :=
  ∃ ptr cap, VecAt WordsAt m' a ptr cap ws ∧ (cap = 0 ∨ env.Fresh m m' ptr (Layouts.K.byteSize * cap))

/-- **A `Vec<u64>` (or `Vec<K>`, `Vec<usize>`) of `ws` at `a`**, its elements live. -/
def WVecAt (env : Env) (m : MachineState) (a : Word) (ws : List Word) : Prop :=
  ∃ ptr cap, VecAt WordsAt m a ptr cap ws ∧ env.Live m ptr (Layouts.K.byteSize * ws.length)

/-- The words of `K`s. -/
def kWords (ks : List K) : List Word := ks.map BF64.toBitVec

end Rv64mc.Spec.Whir
