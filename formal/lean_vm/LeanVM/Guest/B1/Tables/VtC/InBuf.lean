/-
  LeanVM.Guest.B1.Tables.VtC.InBuf

  Where `verify_tables`' loads read: inside a buffer the memory holds.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.Hon
public import LeanVM.Guest.B1.Fwd.FlatIte

/-!
# Loads inside buffers

`InBuf σ bufs p off`: a load through `p` at offset `off` lands in one of the buffers `bufs`
(pointer, length): `σ p` is the buffer's pointer times `g^j`, `j + off` below its length. The
placed lift needs it of every load (the loads read the caller's or the function's own words).
`LoadsInBuf σ bufs blk`: every load atom of the block does. `vt_inBuf_direct`: a load through a
buffer's own pointer variable at an offset below its length.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

theorem vt_inBuf_direct {σ : Val} {bufs : List (E × ℕ)} {p : V} {off len : ℕ}
    (hq : (σ p, len) ∈ bufs) (hoff : off < len) : InBuf σ bufs p off :=
  ⟨_, hq, 0, by simp, by simpa using hoff⟩

end
end LeanVM.Guest.B1.Tables
