/-
  Rv64mc.Core.ReprBytes

  Bytes and the doublewords that hold them. Memory is a map of doublewords (`MachineState.getMem`), a byte the
  one at its offset in the doubleword at its aligned address (`getByte`, `setByte`), so at an address that is a
  multiple of 8 eight bytes are one doubleword:

  * `getByte_aligned`: byte `k` of the doubleword at an aligned `b`, as a byte at `b + k`;
  * `getMem_of_bytes`: the doubleword at an aligned `a + 8 j` read from bytes `8 j` to `8 j + 7` of a `BytesAt`, the
    bytes a byte copy or fill wrote (`packBytes`, little-endian);
  * `getMem_setByte_ne`, `next_setByte`, `frame_byte`, `static_byte`: a byte store as the doubleword store it is,
    for `rv_sym`, which keeps it as `setByte`;
  * `DataRef.Words.load`: a load of a byte, a halfword or a word from a constant table whose base is a multiple of 8
    (`DataRef.Aligned`), as part of the table's doubleword (`dwLoad`).
-/

import Rv64mc.Core.ReprLemmas
import Rv64mc.Tactic.Heap
import Rv64mc.Tactic.Steps
import RiscvZkvm.Rv64.Logic.MemRegionWrite

namespace Rv64mc

open RiscvZkvm.Rv64

variable {m : MachineState}

theorem toNat_add_lt {a : Word} {k : Nat} (h : a.toNat + k < 2 ^ 64) : (a + BitVec.ofNat 64 k).toNat = a.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : k < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]; omega

/-- **Byte `k` of the doubleword at an aligned `b`.** -/
theorem getByte_aligned {b : Word} (hb : b.toNat % 8 = 0) {k : Nat} (hk : k < 8) :
    m.getByte (b + BitVec.ofNat 64 k) = extractByte (m.getMem b) k := by
  have hn : (b + BitVec.ofNat 64 k).toNat = b.toNat + k := toNat_add_lt (by have := b.isLt; omega)
  have ha : alignToDword (b + BitVec.ofNat 64 k) = b := by
    apply BitVec.eq_of_toNat_eq; rw [toNat_alignToDword, hn]; omega
  rw [MachineState.getByte, ha, byteOffset_eq_toNat_mod, hn]
  congr 1; omega

/-- **Eight bytes at an aligned address are its doubleword**: the one at `a + 8 j` from bytes `8 j` to `8 j + 7`. -/
theorem getMem_of_bytes {a : Word} {bs : List (BitVec 8)} (h : BytesAt m a bs) (ha : a.toNat % 8 = 0) {j : Nat}
    (hj : 8 * j + 8 ≤ bs.length) :
    m.getMem (a + BitVec.ofNat 64 (8 * j)) = packBytes ((bs.drop (8 * j)).take 8) := by
  have h1 := h.1
  have hb : (a + BitVec.ofNat 64 (8 * j)).toNat = a.toNat + 8 * j := toNat_add_lt (by omega)
  apply eq_of_forall_extractByte
  intro k hk
  have hlen : k < ((bs.drop (8 * j)).take 8).length := by simp; omega
  rw [extractByte_packBytes _ _ hk hlen, ← getByte_aligned (by rw [hb]; omega) hk]
  have e : a + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (8 * j + k) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_add_lt (by rw [hb]; omega), hb, toNat_add_lt (by omega)]; omega
  rw [e, h.2 (8 * j + k) (by omega)]
  simp [List.getElem_take, List.getElem_drop]

theorem setByte_def {a : Word} {c : BitVec 8} :
    m.setByte a c = m.setMem (alignToDword a) (replaceByte (m.getMem (alignToDword a)) (byteOffset a) c) := rfl

/-- A byte store keeps a doubleword elsewhere. -/
theorem getMem_setByte_ne {a x : Word} {c : BitVec 8} (h : x ≠ alignToDword a) :
    (m.setByte a c).getMem x = m.getMem x := by
  rw [setByte_def]; exact MachineState.getMem_setMem_ne h

/-- A byte store into its own doubleword `x`. -/
theorem getMem_setByte_eq {a x : Word} {c : BitVec 8} (h : alignToDword a = x) :
    (m.setByte a c).getMem x = replaceByte (m.getMem x) (byteOffset a) c := by
  subst h; rw [setByte_def]; exact MachineState.getMem_setMem_eq

theorem toNat_alignToDword' (a : Word) : (alignToDword a).toNat = a.toNat - a.toNat % 8 := toNat_alignToDword a

variable {env : Env}

theorem next_setByte {N : MachineState} {a : Word} {c : BitVec 8} (h : alignToDword a ≠ env.nextAddr) :
    env.next (N.setByte a c) = env.next N := by
  rw [setByte_def]; exact Tactic.next_setMem h

/-- A byte store into a doubleword of the stack. -/
theorem frame_byte {top a : Word} {c : BitVec 8} {out : Word → Prop} {N : MachineState} (h1 : env.Frame top out m N)
    (hlo : env.stackLimit.toNat ≤ (alignToDword a).toNat) (hhi : (alignToDword a).toNat < top.toNat) :
    env.Frame top out m (N.setByte a c) := by
  rw [setByte_def]; exact Tactic.frame_slot h1 hlo hhi

/-- A byte store into a doubleword of `out`. -/
theorem frame_byte_out {top a : Word} {c : BitVec 8} {out : Word → Prop} {N : MachineState}
    (h1 : env.Frame top out m N) (hb : out (alignToDword a)) (hn : alignToDword a ≠ env.nextAddr) :
    env.Frame top out m (N.setByte a c) := by
  rw [setByte_def]; exact Tactic.frame_out h1 hb hn

/-- A byte store into a doubleword the function allocated. -/
theorem frame_byte_fresh {top a : Word} {c : BitVec 8} {out : Word → Prop} {N B : MachineState}
    (h1 : env.Frame top out m N) (hn : env.next N = env.next B) (hlo : (env.next m).toNat ≤ (alignToDword a).toNat)
    (hhi : (alignToDword a).toNat < (env.next B).toNat) : env.Frame top out m (N.setByte a c) := by
  rw [setByte_def]; exact Tactic.frame_fresh h1 hn hlo hhi

theorem static_byte {N : MachineState} {a : Word} {c : BitVec 8} (hs : env.Static N)
    (h : (alignToDword a).toNat < env.staticLo.toNat ∨ env.staticHi.toNat ≤ (alignToDword a).toNat) :
    env.Static (N.setByte a c) := by
  rw [setByte_def]; exact Tactic.static_store hs h

/-- What a load of width `w` at byte `o` of a doubleword holding `v` reads, before any sign extension. -/
def dwLoad (w : Lprog.Width) (v : Word) (o : Nat) : Word :=
  match w with
  | .b1 => (extractByte v o).zeroExtend 64
  | .b2 => (extractHalfword v (o / 2)).zeroExtend 64
  | .b4 => (extractWord32 v (o / 4)).zeroExtend 64
  | .b8 => v

/-- A load narrower than a doubleword, at byte `o` of the doubleword at an aligned `b + 8 k`. -/
theorem loadVal_aligned {w : Lprog.Width} {M : MachineState} {b : Word} {k o c : Nat} (hb : b.toNat % 8 = 0)
    (hc : c = 8 * k + o) (ho : o < 8) (hn : b.toNat + 8 * k + 8 ≤ 2 ^ 64) (hw : w ≠ .b8) :
    Tactic.loadVal w M (b + BitVec.ofNat 64 c) = dwLoad w (M.getMem (b + BitVec.ofNat 64 (8 * k))) o := by
  have hx : (b + BitVec.ofNat 64 c).toNat = b.toNat + c := toNat_add_lt (by omega)
  have hk : (b + BitVec.ofNat 64 (8 * k)).toNat = b.toNat + 8 * k := toNat_add_lt (by omega)
  have ha : alignToDword (b + BitVec.ofNat 64 c) = b + BitVec.ofNat 64 (8 * k) := by
    apply BitVec.eq_of_toNat_eq; rw [toNat_alignToDword, hx, hk]; omega
  have hoff : byteOffset (b + BitVec.ofNat 64 c) = o := by rw [byteOffset_eq_toNat_mod, hx]; omega
  cases w with
  | b1 => simp only [Tactic.loadVal, dwLoad, MachineState.getByte, ha, hoff]
  | b2 => simp only [Tactic.loadVal, dwLoad, MachineState.getHalfword, ha, hoff]
  | b4 => simp only [Tactic.loadVal, dwLoad, MachineState.getWord32, ha, hoff]
  | b8 => exact absurd rfl hw

/-- **A table's base is a multiple of 8**, and its `n` doublewords do not wrap. -/
def DataRef.Aligned (d : DataRef) (n : Nat) : Prop := (d.hi + d.lo).toNat % 8 = 0 ∧ (d.hi + d.lo).toNat + 8 * n ≤ 2 ^ 64

/-- **A narrow load from a constant table**: byte `o` of its doubleword `k`, `v`. -/
theorem DataRef.Words.load {env : Env} {d : DataRef} {ws : List Word} {M : MachineState} {w : Lprog.Width}
    (hw : DataRef.Words env d ws) (hs : env.Static M) (hal : DataRef.Aligned d ws.length) {k o c : Nat} {v : Word}
    (hv : ws[k]? = some v) (hc : c = 8 * k + o) (ho : o < 8) (hW : w ≠ .b8) :
    Tactic.loadVal w M (d.hi + d.lo + BitVec.ofNat 64 c) = dwLoad w v o := by
  have hk : k < ws.length := by
    rcases Nat.lt_or_ge k ws.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hv; cases hv
  have e : ws[k] = v := by rw [List.getElem?_eq_getElem hk] at hv; exact Option.some.inj hv
  rw [loadVal_aligned hal.1 hc ho (by have := hal.2; omega) hW, hw M hs k hk, e]

end Rv64mc
