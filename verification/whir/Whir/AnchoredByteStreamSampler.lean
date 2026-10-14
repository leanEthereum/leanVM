import Whir.AnchoredFiatShamirSecurityCodec

/-! Bridge from the hand-ported deployed squeeze loop to the finite byte-vector
codec. Mandatory nonempty commitment absorption resets the cursor; there is no
injectable cached-output assumption. -/
namespace Whir.AnchoredByteStreamSampler
open Concrete FiatShamirGame DuplexRefinement AnchoredFiatShamirSecurityCodec
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

@[simp] theorem stream_length (c : Compression) (cv : Digest32) (offset n : Nat) :
    (stream c cv offset n).length = n := by
  induction n generalizing offset with
  | zero => rfl
  | succ n ih => simp [stream, ih]

theorem stream_getElem (c : Compression) (cv : Digest32) (offset n j : Nat)
    (bound : j < n) :
    (stream c cv offset n)[j]'(by simpa using bound) =
      outputBlock c cv ((offset+j)/32) ⟨(offset+j)%32, Nat.mod_lt _ (by decide)⟩ := by
  induction n generalizing offset j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simp [stream]
    | succ j =>
      simp only [stream, List.getElem_cons_succ]
      simpa only [Nat.add_assoc, Nat.add_comm 1 j] using ih (offset+1) j (by omega)

theorem squeezeLoop_getElem (c : Compression) (s : State) (n j : Nat)
    (cache : CacheValid c s) (bound : j < n) :
    (squeezeLoop c n s).2[j]'(by simpa using bound) =
      outputBlock c s.cv ((s.consumed+j)/32)
        ⟨(s.consumed+j)%32, Nat.mod_lt _ (by decide)⟩ := by
  have h := congrArg (fun bs : List Byte => bs[j]?) (squeezeLoop_stream c s n cache)
  have left : j < (squeezeLoop c n s).2.length := by simpa using bound
  have right : j < (stream c s.cv s.consumed n).length := by simpa using bound
  rw [List.getElem?_eq_getElem left, List.getElem?_eq_getElem right] at h
  exact (Option.some.inj h).trans (stream_getElem c s.cv s.consumed n j bound)

def actualBlocks (c : Compression) (s : State) (dimension : Nat) : Blocks dimension :=
  fun i => outputBlock c (finish c s).cv i.val

/-- Direct equality to the actual deployed 24-byte decoder, including every
block straddling and the exact final cursor. The initial cache is irrelevant
because the mandatory absorb has reset that cursor to zero. -/
theorem sampleVec_actual (c : Compression) (s : State) (dimension : Nat)
    (cursor : s.consumed = 0) (positive : 0 < dimension)
    (limit : 24*dimension ≤ maxCursor) :
    sampleVec c s dimension =
      .ok ((squeezeLoop c (24*dimension) (finish c s)).1,
        List.ofFn (point dimension (actualBlocks c s dimension))) := by
  have cache : CacheValid c (finish c s) := by
    intro nonzero
    simp [cursor] at nonzero
  have squeezed : squeeze c s (24*dimension) =
      .ok (squeezeLoop c (24*dimension) (finish c s)) := by
    simp [squeeze, cursor, limit, Nat.ne_of_gt (by omega : 0 < 24*dimension)]
  unfold sampleVec
  split
  next e he => rw [he] at squeezed; cases squeezed
  next t bs hs =>
    have eq := Except.ok.inj (hs.symm.trans squeezed)
    have ht := congrArg Prod.fst eq
    have hb := congrArg Prod.snd eq
    dsimp only at ht hb
    subst t
    subst bs
    apply congrArg Except.ok
    apply Prod.ext
    · rfl
    · apply congrArg List.ofFn
      funext j
      rw [point_bytes]
      apply congrArg ByteCodec.decodeE
      funext i
      have h := squeezeLoop_getElem c (finish c s) (24*dimension) (24*j.val+i.val)
        cache (by have := j.isLt; have := i.isLt; omega)
      simpa only [finish_consumed, cursor, Nat.zero_add, actualBlocks] using h

theorem mandatory_absorb_cursor (c : Compression) (s : State) (header : List Byte)
    (nonempty : header ≠ []) : (absorb c s header).consumed = 0 :=
  absorb_nonempty_cursor c s header nonempty

theorem sampleVec_cursor (c : Compression) (s : State) (dimension : Nat)
    (cursor : s.consumed = 0) :
    (squeezeLoop c (24*dimension) (finish c s)).1.consumed = 24*dimension := by
  simp [cursor]

theorem anchor_dimension_limit (dimension : Nat) (small : dimension ≤ 28) :
    24*dimension ≤ maxCursor := by
  norm_num [maxCursor]
  omega

end Whir.AnchoredByteStreamSampler

#print axioms Whir.AnchoredByteStreamSampler.sampleVec_actual
#print axioms Whir.AnchoredByteStreamSampler.mandatory_absorb_cursor
