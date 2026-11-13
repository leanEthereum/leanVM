/-
  LeanVM.Guest.B1.VerifySub.H.KFacts

  An honest child's Keccak reduction's end sponge and its deferred claim: the reduction ends with
  a full queue, so the ring map's grind permutes it first; the fresh claim is `verify_tables`'
  bytecode point and value.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Keccak
public import LeanVM.Guest.B1.KeccakGkr.VkCH
public import LeanVM.Guest.B1.KeccakGkr.VkCHon

/-!
# The Keccak reduction's end, the deferred claim

`ChildSegs.s6_pend`: the sponge after `verify_keccak` holds a full queue (its sixty-four slices
absorbed on an empty one). `ChildSegs.ringSt_eq`: the ring map's grind permutes it first, so its
permutation is the nonce's on the capacity `verify_keccak` returns. `ChildSegs.fresh_eq`: the
child's deferred claim is the bus point's first `19` coordinates and the slot point, with
`verify_tables`' bytecode value.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

theorem vs_pend_absorbAll : ∀ (xs : List E) (s : Fs) (t : ℕ), 1 ≤ s.pend.length →
    s.pend.length ≤ 4 → (s.absorbAll xs t).pend.length = (s.pend.length - 1 + xs.length) % 4 + 1
  | [], s, t, h1, h4 => by
    show s.pend.length = _
    simp only [List.length_nil]
    omega
  | x :: xs, s, t, h1, h4 => by
    show ((s.absorb x t).absorbAll xs t).pend.length = _
    by_cases hf : s.pend.length = 4
    · have e : s.absorb x t = ⟨capOf s.perm, [(x, t)]⟩ := by simp [Fs.absorb, hf, rateScalars]
      rw [e, vs_pend_absorbAll xs _ t (by simp) (by simp)]
      simp only [List.length_cons, List.length_nil]
      omega
    · have e : s.absorb x t = ⟨s.cap, s.pend ++ [(x, t)]⟩ := by
        simp [Fs.absorb, hf, rateScalars]
      rw [e, vs_pend_absorbAll xs _ t (by simp) (by simp; omega)]
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_cons]
      omega

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- **The sponge after the Keccak reduction holds a full queue.** -/
theorem s6_pend (hbl : bytecode.length = 2 ^ 23) : S.s6.pend.length = 4 := by
  obtain ⟨-, -, hrun⟩ := S.keccak_run hbl
  obtain ⟨hτ9, hτ22, hn, ho, hf, -, -, hsl⟩ := S.keccak_facts hbl
  obtain ⟨-, -, h5⟩ := S.H_spec hbl
  have hc : ∃ sp, (⟨S.H.s3.squeeze.2.cap, []⟩ : Fs).Carries sp := by rw [← h5]; exact S.c5
  obtain ⟨D, -, -, -, -, -, hDs, hD, -, -, -, hsF⟩ := vkData_of_run hτ9 (by omega) hn ho hf hc hrun
  rw [← hsF, VkData.sF, (VkData.S_ok hD).1, hDs]
  obtain ⟨x, xs, hx⟩ : ∃ x xs, S.kc.2.2 = x :: xs := by
    cases h : S.kc.2.2 with
    | nil => rw [h] at hsl; simp at hsl
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hxl : xs.length = 63 := by rw [hx] at hsl; simpa using hsl
  rw [hx]
  show ((Fs.absorb ⟨_, []⟩ x dsObserve).absorbAll xs dsObserve).pend.length = 4
  rw [show Fs.absorb ⟨D.S.2.2.cap, []⟩ x dsObserve = ⟨D.S.2.2.cap, [(x, dsObserve)]⟩ by
    simp [Fs.absorb, rateScalars], vs_pend_absorbAll xs _ _ (by simp) (by simp), hxl]
  simp

/-- **The ring map's grind permutes the full queue first**: its permutation is the nonce's on the
capacity `verify_keccak` returns. -/
theorem ringSt_eq (hbl : bytecode.length = 2 ^ 23) :
    S.ringSt = (⟨capOf S.s6.perm, []⟩ : Fs).nonceState S.ringN := by
  have hp := S.s6_pend hbl
  show (S.s6.absorb S.ringN dsPowNonce).perm = _
  simp [Fs.nonceState, Fs.absorb, hp, rateScalars]

/-- **The deferred claim**: the bus point's first `19` coordinates, then the slot point, and
`verify_tables`' bytecode value. -/
theorem fresh_eq (hbl : bytecode.length = 2 ^ 23) :
    c.freshClaim = ⟨S.rG.2.1.take 19 ++ S.H.slots, S.H.bv⟩ := by
  obtain ⟨hok, -, -, -⟩ := S.H_run hbl
  have h := hok.hbv ⟨⟨default, [], none⟩, [], [], []⟩
  have hlb : S.H.L.logBytecode = 19 := logBytecode_eq hbl _ _
  rw [hlb] at h
  simp only [ChildSegs.H, claimedBytecodeValue, VerifierProgram.require] at h
  split at h
  · rename_i hc
    obtain ⟨h1, h2⟩ := hc
    have e1 : c.freshClaim.bytecodePoint = S.rG.2.1.take 19 ++ S.H.slots := h1.symm
    have e2 : c.freshClaim.bytecodeValue = S.H.bv := h2.symm
    rw [← e1, ← e2]
  · simp [Tables.tbRun, Compile.runWithHash] at h

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
