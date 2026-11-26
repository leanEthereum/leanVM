/-
  Rv64mc.Proof.Transcript.TranscriptReprT

  The representation the total contracts of `Transcript`'s methods share, for safety: `TranscriptT env m a`, the
  transcript at `a` (`Layouts.Transcript`, `360` bytes) in a window with its sponge `SpongeT`, and the `Proof` it
  points to (`proofAddr`) apart from it, in a window, 8-byte aligned, with its stream's buffer in a window unless
  empty (`NextT.StreamWin`); `OwnedT env m top a`, both owned by the caller whose stack top is `top` (`Env.Owned`:
  below `NEXT`, or in a caller's frame). Every access the methods make is inside these, and every index they compute
  is checked by the code, so nothing else is needed. No functional ghost: the sponge's lanes after a permutation are
  `keccak_f`'s, whose functional contract is not total (`KeccakFSafeT`).

  `TranscriptT` reads five words (`of_get`): the ground tag and the count of the sponge, the proof's address, the
  stream's pointer and length. A call whose `out` misses them keeps it, the transcript and its proof owned
  (`frame`, `frameF`).

  ## Main definitions

  * `ProofT`, `TranscriptT`, `OwnedT`

  ## Main results

  * `TranscriptT.of_get`, `OwnedT.of_next`, `OwnedT.mono`, `OwnedT.sponge`, `getMem_owned_out`,
    `TranscriptT.frame`, `TranscriptT.frameF`
-/

import Rv64mc.Proof.Transcript.SpongeReprT
import Rv64mc.Proof.Transcript.NextT

namespace Rv64mc.Proof.Transcript.TranscriptReprT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Transcript.SpongeReprT

variable {env : Env}

/-- The `Proof` at `q`, for safety: 8-byte aligned, its `48` bytes in a window, its stream's buffer in a window
    unless empty. -/
def ProofT (env : Env) (m : MachineState) (q : Word) : Prop :=
  q.toNat % 8 = 0 ∧ InWin env q Layouts.Proof.byteSize ∧ NextT.StreamWin env m q

/-- **The transcript at `a`, for safety**: its sponge `SpongeT`, its `360` bytes in a window, and the proof it
    points to apart from it and `ProofT`. -/
def TranscriptT (env : Env) (m : MachineState) (a : Word) : Prop :=
  SpongeT env m a ∧ InWin env a Layouts.Transcript.byteSize ∧
    Apart (proofAddr m a) Layouts.Proof.byteSize a Layouts.Transcript.byteSize ∧ ProofT env m (proofAddr m a)

/-- The transcript at `a` and its proof owned by a caller whose stack top is `top`. -/
def OwnedT (env : Env) (m : MachineState) (top a : Word) : Prop :=
  env.Owned m top a Layouts.Transcript.byteSize ∧ env.Owned m top (proofAddr m a) Layouts.Proof.byteSize

/-- A memory agreeing with `m` on the five words `TranscriptT` reads keeps it. -/
theorem TranscriptT.of_get {m m' : MachineState} {a : Word} (h : TranscriptT env m a)
    (h0 : m'.getMem a = m.getMem a) (h320 : m'.getMem (a + 320#64) = m.getMem (a + 320#64))
    (h328 : m'.getMem (a + 328#64) = m.getMem (a + 328#64))
    (h8 : m'.getMem (m.getMem (a + 328#64) + 8#64) = m.getMem (m.getMem (a + 328#64) + 8#64))
    (h16 : m'.getMem (m.getMem (a + 328#64) + 16#64) = m.getMem (m.getMem (a + 328#64) + 16#64)) :
    TranscriptT env m' a := by
  obtain ⟨⟨ha, hw, hn, hg⟩, hwa, hap, hq, hqw, hs⟩ := h
  simp only [proofAddr, Layouts.Transcript.proof] at hap hq hqw hs
  refine ⟨⟨ha, hw, h320 ▸ hn, h0 ▸ hg⟩, hwa, ?_, ?_⟩ <;>
    simp only [proofAddr, Layouts.Transcript.proof, h328]
  · exact hap
  · refine ⟨hq, hqw, ?_⟩
    unfold NextT.StreamWin at hs ⊢
    rw [h8, h16]
    exact hs

/-- Ownership is kept by a memory whose `NEXT` is not lower and whose proof's address is the same. -/
theorem OwnedT.of_next {m m' : MachineState} {top a : Word} (h : OwnedT env m top a)
    (hn : (env.next m).toNat ≤ (env.next m').toNat) (hq : proofAddr m' a = proofAddr m a) :
    OwnedT env m' top a := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h
  rw [OwnedT, hq]
  exact ⟨⟨by omega, h2⟩, ⟨by omega, h4⟩⟩

/-- Ownership from a caller's stack top is ownership from a lower one. -/
theorem OwnedT.mono {m : MachineState} {top top' a : Word} (h : OwnedT env m top a) (ht : top'.toNat ≤ top.toNat) :
    OwnedT env m top' a := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h
  exact ⟨⟨by omega, h2⟩, ⟨by omega, h4⟩⟩

/-- The sponge of an owned transcript is owned. -/
theorem OwnedT.sponge {m : MachineState} {top a : Word} (h : OwnedT env m top a) :
    env.Owned m top a Layouts.Sponge.byteSize := by
  obtain ⟨⟨h1, h2⟩, _⟩ := h
  simp only [Layouts.Transcript.byteSize, Layouts.Sponge.byteSize] at h1 h2 ⊢
  exact ⟨by omega, by omega⟩

/-- A word of an owned object is kept by a frame whose `out` misses it. -/
theorem getMem_owned_out {top b : Word} {k n : Nat} {out : Word → Prop} {m m' : MachineState}
    (hf : env.Frame top out m m') (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (ho : env.Owned m top b n) (hk : k + 8 ≤ n)
    (hout : ¬ out (b + BitVec.ofNat 64 k)) : m'.getMem (b + BitVec.ofNat 64 k) = m.getMem (b + BitVec.ofNat 64 k) := by
  have h2 := ho.2
  have e : (b + BitVec.ofNat 64 k).toNat = b.toNat + k := toNat_add_ofNat (by omega)
  rcases ho.1 with h | h
  · exact hf.getMem_below_next hnx (by omega) hout
  · exact hf.getMem_above hlim (by omega) hout

/-- **A call whose `out` misses the five words keeps an owned transcript.** -/
theorem TranscriptT.frame {m m' : MachineState} {top a : Word} {out : Word → Prop} (h : TranscriptT env m a)
    (ho : OwnedT env m top a) (hf : env.Frame top out m m') (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hlim : env.stackLimit.toNat ≤ top.toNat)
    (hout : ∀ k, (k = 0 ∨ k = 320 ∨ k = 328) → ¬ out (a + BitVec.ofNat 64 k))
    (hq : ∀ k, (k = 8 ∨ k = 16) → ¬ out (m.getMem (a + 328#64) + BitVec.ofNat 64 k)) :
    TranscriptT env m' a ∧ OwnedT env m' top a ∧ proofAddr m' a = proofAddr m a := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := ho
  simp only [proofAddr, Layouts.Transcript.proof, Layouts.Transcript.byteSize, Layouts.Proof.byteSize] at h1 h2 h3 h4
  have e0 : m'.getMem a = m.getMem a := by
    simpa using getMem_owned_out (k := 0) hf hnx hlim ⟨h1, h2⟩ (by omega) (hout 0 (by omega))
  have e328 : m'.getMem (a + 328#64) = m.getMem (a + 328#64) :=
    getMem_owned_out hf hnx hlim ⟨h1, h2⟩ (by omega) (hout 328 (by omega))
  refine ⟨h.of_get e0 (getMem_owned_out hf hnx hlim ⟨h1, h2⟩ (by omega) (hout 320 (by omega))) e328
    (getMem_owned_out hf hnx hlim ⟨h3, h4⟩ (by omega) (hq 8 (by omega)))
    (getMem_owned_out hf hnx hlim ⟨h3, h4⟩ (by omega) (hq 16 (by omega))), ?_, ?_⟩
  · refine OwnedT.of_next ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ hf.1 ?_
    simp only [proofAddr, Layouts.Transcript.proof]
    exact e328
  · simp only [proofAddr, Layouts.Transcript.proof]
    exact e328

/-- **A call that writes nothing outside its stack and its allocations keeps an owned transcript.** -/
theorem TranscriptT.frameF {m m' : MachineState} {top a : Word} (h : TranscriptT env m a) (ho : OwnedT env m top a)
    (hf : env.Frame top Tactic.F m m') (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hlim : env.stackLimit.toNat ≤ top.toNat) :
    TranscriptT env m' a ∧ OwnedT env m' top a ∧ proofAddr m' a = proofAddr m a :=
  h.frame ho hf hnx hlim (fun _ _ h => h) fun _ _ h => h

end Rv64mc.Proof.Transcript.TranscriptReprT
