/-
  LeanVM.Guest.B1.VsC.StreamChunks

  The honest stream's chunk count passes `verify_sub`'s checks on it.
-/

module

public import Statement.LeanVmGuestProver
public import LeanVM.Guest.GuestConst
public import LeanVM.Guest.Data.Consts

/-!
# The stream's chunks

The honest prover pushes `g^c` for `c = max(⌈len / STREAM_CHUNK⌉, 1)` chunks (`childHints`), the
stream zero-padded to `c · STREAM_CHUNK` words. `verify_sub` checks `c < STREAM_CAP / STREAM_CHUNK + 1`
and, after the opening, that the words it read, all of the accepted proof's stream, are fewer than
`c · STREAM_CHUNK + 1`. `streamChunks_ok`: both hold for a stream of at most `STREAM_CAP` words
(`stream_le_of_verifyDeferred`).
-/

namespace LeanVM.Guest.B1.VsC

@[expose] public section

/-- The honest chunk count of a stream of `len` words. -/
def chunksOf (len : ℕ) : ℕ := max ((len + Prover.streamChunk - 1) / Prover.streamChunk) 1

/-- **The honest chunk count passes `verify_sub`'s checks.** -/
theorem streamChunks_ok {len : ℕ} (h : len ≤ guest_const% STREAM_CAP) :
    chunksOf len < guest_const% STREAM_CAP / guest_const% STREAM_CHUNK + 1 ∧
      len < chunksOf len * guest_const% STREAM_CHUNK + 1 ∧ 1 ≤ chunksOf len ∧
      Prover.streamChunk = guest_const% STREAM_CHUNK := by
  have hc : guest_const% STREAM_CAP = 8192 := rfl
  have hk : guest_const% STREAM_CHUNK = 256 := rfl
  have hs : Prover.streamChunk = 256 := rfl
  rw [hc] at h
  unfold chunksOf
  rw [hc, hk, hs]
  omega

end
end LeanVM.Guest.B1.VsC
