module

public import Native.Keccak.Hash

/-!
# `Keccak.hash` computes Keccak-256

`hash_spec`: from `len` bytes held in words at `rsi` (`HoldsBytes`), `Keccak.hash` leaves
`keccak256` of those bytes in the scratch area's first four words, writes no word outside its
scratch area, and writes no register but `rax`, `rbx`, `rcx`, `rdx`, `rsi`, `r8`. The words and
bytes it speaks of are `Native.Keccak.Words`'; the proof is `Native.Keccak.Proof.hash_correct`
(`Native/Keccak/Hash.lean`): a phase of scratch writes per step of the round (`Round`), the 24
rounds (`Permute`), the blocks as words (`Lanes`), the whole blocks (`Absorb`), the last block and
the padding (`Tail`).
-/

@[expose] public section

namespace Native.Keccak

open LeanVM.Protocol.KeccakHash

/-- **`Keccak.hash` is Keccak-256.** -/
theorem hash_spec {s : QState} {ws : List UInt64} {len : Nat} {E : QState → Prop}
    (hb : HoldsBytes ws len) (hlen : s.reg .rbx = len.toUInt64) (hlen32 : len < 2 ^ 32)
    (hin : WordsAt s.mem (s.reg .rsi) ws)
    (hscr : ∀ k < scratchWords, (s.mem (scratchAddr (s.reg .rdi) k)).isSome)
    (hdisj : ∀ i < ws.length, ∀ k < scratchWords,
      s.reg .rsi + (8 * i).toUInt64 ≠ scratchAddr (s.reg .rdi) k) :
    WP hash s (fun s' ↦
      (∀ k (hk : k < 4), s'.mem (scratchAddr (s.reg .rdi) k) =
        some (keccak256 ((wordsBytes ws).take len))[k]) ∧
      (∀ k < scratchWords, (s'.mem (scratchAddr (s.reg .rdi) k)).isSome) ∧
      (∀ a, (∀ k < scratchWords, a ≠ scratchAddr (s.reg .rdi) k) → s'.mem a = s.mem a) ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8] s s') E :=
  Proof.hash_correct hb hlen hlen32 hin hscr hdisj

end Native.Keccak
