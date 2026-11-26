/-
  Rv64mc.Proof.Transcript.TranscriptReprT

  The representation the total contracts of `Transcript`'s methods share, for safety: `TranscriptT env m a`, the
  transcript at `a` (`Layouts.Transcript`, `360` bytes) in a window with its sponge `SpongeT`, and the `Proof` it
  points to (its address at offset `328`, `proofAddr`'s) apart from it, in a window, 8-byte aligned, with its
  stream's buffer in a window unless empty (`NextT.StreamWin`); `OwnedT env m top a`, both owned by the caller
  whose stack top is `top` (`Env.Owned`: below `NEXT`, or in a caller's frame). Every access the methods make
  is inside these, and every index they compute is checked by the code, so nothing else is needed. No functional
  ghost: the sponge's lanes after a permutation are `keccak_f`'s, whose functional contract is not total
  (`KeccakFSafeT`).

  `TranscriptT` reads five words (`of_get`): the ground tag and the count of the sponge, the proof's address, the
  stream's pointer and length. A call whose `out` misses them keeps it, the transcript and its proof owned
  (`frame`, `frameF`), and one that leaves the sponge `SpongeT` (`frameS`).

  ## Main definitions

  * `ProofT`, `TranscriptT`, `OwnedT`

  ## Main results

  * `spongeT_of_get`, `TranscriptT.of_get`, `TranscriptT.of_sponge`, `OwnedT.of_next`, `OwnedT.mono`, `OwnedT.sponge`,
    `getMem_owned_out`, `TranscriptT.frame`, `TranscriptT.frameS`, `TranscriptT.frameF`
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
    Apart (m.getMem (a + 328#64)) Layouts.Proof.byteSize a Layouts.Transcript.byteSize ∧
    ProofT env m (m.getMem (a + 328#64))

/-- The transcript at `a` and its proof owned by a caller whose stack top is `top`. -/
def OwnedT (env : Env) (m : MachineState) (top a : Word) : Prop :=
  env.Owned m top a Layouts.Transcript.byteSize ∧ env.Owned m top (m.getMem (a + 328#64)) Layouts.Proof.byteSize

/-- A memory agreeing with `m` on the two words `SpongeT` reads keeps it. -/
theorem spongeT_of_get {m m' : MachineState} {a : Word} (h : SpongeT env m a) (h0 : m'.getMem a = m.getMem a)
    (h320 : m'.getMem (a + 320#64) = m.getMem (a + 320#64)) : SpongeT env m' a :=
  ⟨h.1, h.2.1, h320 ▸ h.2.2.1, h0 ▸ h.2.2.2⟩

/-- A memory with a sponge `SpongeT` agreeing with `m` on the proof's address and the stream's words keeps it. -/
theorem TranscriptT.of_sponge {m m' : MachineState} {a : Word} (h : TranscriptT env m a) (hs : SpongeT env m' a)
    (h328 : m'.getMem (a + 328#64) = m.getMem (a + 328#64))
    (h8 : m'.getMem (m.getMem (a + 328#64) + 8#64) = m.getMem (m.getMem (a + 328#64) + 8#64))
    (h16 : m'.getMem (m.getMem (a + 328#64) + 16#64) = m.getMem (m.getMem (a + 328#64) + 16#64)) :
    TranscriptT env m' a := by
  obtain ⟨_, hwa, hap, hq, hqw, hst⟩ := h
  unfold NextT.StreamWin at hst
  rw [TranscriptT, h328]
  exact ⟨hs, hwa, hap, hq, hqw, by unfold NextT.StreamWin; rwa [h8, h16]⟩

/-- A memory agreeing with `m` on the five words `TranscriptT` reads keeps it. -/
theorem TranscriptT.of_get {m m' : MachineState} {a : Word} (h : TranscriptT env m a)
    (h0 : m'.getMem a = m.getMem a) (h320 : m'.getMem (a + 320#64) = m.getMem (a + 320#64))
    (h328 : m'.getMem (a + 328#64) = m.getMem (a + 328#64))
    (h8 : m'.getMem (m.getMem (a + 328#64) + 8#64) = m.getMem (m.getMem (a + 328#64) + 8#64))
    (h16 : m'.getMem (m.getMem (a + 328#64) + 16#64) = m.getMem (m.getMem (a + 328#64) + 16#64)) :
    TranscriptT env m' a :=
  h.of_sponge (spongeT_of_get h.1 h0 h320) h328 h8 h16

/-- Ownership is kept by a memory whose `NEXT` is not lower and whose proof's address is the same. -/
theorem OwnedT.of_next {m m' : MachineState} {top a : Word} (h : OwnedT env m top a)
    (hn : (env.next m).toNat ≤ (env.next m').toNat) (hq : m'.getMem (a + 328#64) = m.getMem (a + 328#64)) :
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

/-- **A call whose `out` misses the proof's address and the stream's words keeps an owned transcript whose sponge
    it leaves `SpongeT`.** -/
theorem TranscriptT.frameS {m m' : MachineState} {top a : Word} {out : Word → Prop} (h : TranscriptT env m a)
    (hs : SpongeT env m' a) (ho : OwnedT env m top a) (hf : env.Frame top out m m')
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hlim : env.stackLimit.toNat ≤ top.toNat)
    (hout : ¬ out (a + BitVec.ofNat 64 328))
    (hq : ∀ k, (k = 8 ∨ k = 16) → ¬ out (m.getMem (a + 328#64) + BitVec.ofNat 64 k)) :
    TranscriptT env m' a ∧ OwnedT env m' top a ∧ m'.getMem (a + 328#64) = m.getMem (a + 328#64) := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := ho
  simp only [Layouts.Transcript.byteSize, Layouts.Proof.byteSize] at h1 h2 h3 h4
  have e328 : m'.getMem (a + 328#64) = m.getMem (a + 328#64) :=
    getMem_owned_out hf hnx hlim ⟨h1, h2⟩ (by omega) hout
  exact ⟨h.of_sponge hs e328 (getMem_owned_out hf hnx hlim ⟨h3, h4⟩ (by omega) (hq 8 (by omega)))
    (getMem_owned_out hf hnx hlim ⟨h3, h4⟩ (by omega) (hq 16 (by omega))),
    OwnedT.of_next ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ hf.1 e328, e328⟩

/-- **A call whose `out` misses the five words keeps an owned transcript.** -/
theorem TranscriptT.frame {m m' : MachineState} {top a : Word} {out : Word → Prop} (h : TranscriptT env m a)
    (ho : OwnedT env m top a) (hf : env.Frame top out m m') (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hlim : env.stackLimit.toNat ≤ top.toNat)
    (hout : ∀ k, (k = 0 ∨ k = 320 ∨ k = 328) → ¬ out (a + BitVec.ofNat 64 k))
    (hq : ∀ k, (k = 8 ∨ k = 16) → ¬ out (m.getMem (a + 328#64) + BitVec.ofNat 64 k)) :
    TranscriptT env m' a ∧ OwnedT env m' top a ∧ m'.getMem (a + 328#64) = m.getMem (a + 328#64) := by
  have ho1 := ho.1
  simp only [Layouts.Transcript.byteSize] at ho1
  have e0 : m'.getMem a = m.getMem a := by
    simpa using getMem_owned_out (k := 0) hf hnx hlim ho1 (by omega) (hout 0 (by omega))
  exact h.frameS (spongeT_of_get h.1 e0 (getMem_owned_out hf hnx hlim ho1 (by omega) (hout 320 (by omega)))) ho hf
    hnx hlim (hout 328 (by omega)) hq

/-- **A call that writes nothing outside its stack and its allocations keeps an owned transcript.** -/
theorem TranscriptT.frameF {m m' : MachineState} {top a : Word} (h : TranscriptT env m a) (ho : OwnedT env m top a)
    (hf : env.Frame top Tactic.F m m') (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hlim : env.stackLimit.toNat ≤ top.toNat) :
    TranscriptT env m' a ∧ OwnedT env m' top a ∧ m'.getMem (a + 328#64) = m.getMem (a + 328#64) :=
  h.frame ho hf hnx hlim (fun _ _ h => h) fun _ _ h => h

end Rv64mc.Proof.Transcript.TranscriptReprT
