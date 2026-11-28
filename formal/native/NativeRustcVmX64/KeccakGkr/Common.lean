module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Spec.KeccakGkr

/-!
# `keccak_gkr.rs`'s functions on x86-64: common facts

A frame whose body keeps RSP at an offset `o` above the slot its calls push their return address
in (`o = 8` in `Transcript.Frame`'s functions; some frames retain padding below their call slot):
a call keeps it, RSP back at `o + 8` (`Frame.call_at`); RSP at offset `o` is the stack
below `F - o` bytes (`off_stackBelow`). The contracts' footprints (`Areas`): the regions mapped,
not wrapping, apart from the stack and each other (`Areas.ok`, `Areas.apart_stack`,
`Areas.apart_read`).
-/

namespace NativeRustcVmX64.KeccakGkr

open NativeRustcX64 NativeRustcVmX64.Transcript NativeVm.Model
open NativeRustcVm (Region Disjoint InAny)
open NativeRustcVm.Transcript (off bytesAt_congr)

public section

variable {m0 d d' : MachineData} {F o : Nat} {slots : Slots}

/-- Offset `o` of the frame below `F` bytes is the stack below `F - o` bytes. -/
theorem off_stackBelow (h : o ≤ F) : off (stackBelow m0 F) o = stackBelow m0 (F - o) := by
  unfold stackBelow off
  conv => lhs; rw [show F = (F - o) + o by omega, BitVec.ofNat_add, ← BitVec.sub_sub,
    BitVec.sub_add_cancel]

/-- Offset `j` of the frame below `F` bytes is offset `j - o` of the one below `F - o`. -/
theorem off_frame_sub {j : Nat} (hoF : o ≤ F) (hoj : o ≤ j) :
    off (stackBelow m0 F) j = off (stackBelow m0 (F - o)) (j - o) := by
  rw [← off_stackBelow hoF, NativeRustcVm.Transcript.off_off, Nat.add_sub_cancel' hoj]

/-- **A frame kept** across a step that keeps the callee-saved registers and every byte of data
memory, moves RSP to the frame's offset `o'` and changes none of the slots' or the return
address's bytes. -/
theorem Frame.move {o' : Nat} (hf : Frame m0 F slots o d) (hs : Saved d d')
    (hrsp : rspOf d' = off (stackBelow m0 F) o') {R : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ p ∈ slots, ∀ i < 8, ¬ R (off (stackBelow m0 F) (p.1 + i)))
    (hRr : ∀ j < 8, ¬ R (off (stackBelow m0 F) (F + j))) : Frame m0 F slots o' d' := by
  refine ⟨hrsp, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans hf.kept hs.2, fun r hr hsl ↦ ?_⟩
  · refine bytesAt_congr (hf.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    rw [NativeRustcVm.Transcript.off_add]
    exact hso _ (hR p hp i hi')
  · rw [hso _ (hRr j hj)]
    exact hf.ret j hj
  · exact (hs.1 r hr).trans (hf.regs r hr hsl)

/-- **A call** keeps the frame, RSP at offset `o` before (the callee's return address below it)
and `o + 8` after, where the callee changes none of its slots' or the return address's bytes. -/
theorem Frame.call_at (hf : Frame m0 F slots o d) (hs : Saved d d')
    (hrsp : rspOf d' = rspOf d + 8#64) {R : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ p ∈ slots, ∀ i < 8, ¬ R (off (stackBelow m0 F) (p.1 + i)))
    (hRr : ∀ j < 8, ¬ R (off (stackBelow m0 F) (F + j))) : Frame m0 F slots (o + 8) d' :=
  Frame.move hf hs (by rw [hrsp, hf.sp]; exact NativeRustcVm.Transcript.off_add _ _ _) hso hR hRr

/-- **A frame kept by a step in place**: RSP, the callee-saved registers and the bytes kept, but
outside `R`, which misses the slots and the return address. -/
theorem Frame.stay (hf : Frame m0 F slots o d) (hs : Saved d d') (hrsp : rspOf d' = rspOf d)
    {R : BitVec 64 → Prop} (hso : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ q, R q → ¬ NativeRustcVm.InRange (stackBelow m0 F) (F + 8) q)
    (hnw : NativeRustcVm.NoWrap (stackBelow m0 F) (F + 8)) (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) :
    Frame m0 F slots o d' :=
  Frame.move hf hs (hrsp.trans hf.sp) hso
    (fun p hp i hi h ↦ hR _ h (NativeRustcVm.Transcript.inRange_off_self
      (by have := hle p hp; omega) (by unfold NativeRustcVm.NoWrap at hnw; omega)))
    (fun j hj h ↦ hR _ h (NativeRustcVm.Transcript.inRange_off_self (by omega)
      (by unfold NativeRustcVm.NoWrap at hnw; omega)))

/-- Two byte ranges at offsets of one non-wrapping area, one before the other, share no byte. -/
theorem off_disj {b q : BitVec 64} {N o n o' n' : Nat} (hN : NativeRustcVm.NoWrap b N)
    (hn : 0 < n) (hn' : 0 < n') (h1 : o + n ≤ N) (h2 : o' + n' ≤ N) (hd : o + n ≤ o' ∨ o' + n' ≤ o)
    (h : NativeRustcVm.InRange (off b o) n q) : ¬ NativeRustcVm.InRange (off b o') n' q := by
  unfold NativeRustcVm.NoWrap at hN
  have hb := b.isLt
  have e1 : (off b o).toNat = b.toNat + o := NativeRustcVm.Transcript.toNat_off (by omega)
  have e2 : (off b o').toNat = b.toNat + o' := NativeRustcVm.Transcript.toNat_off (by omega)
  rw [NativeRustcVm.Transcript.inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), e1] at h
  rw [NativeRustcVm.Transcript.inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), e2]
  omega

/-- A byte range at an offset of an area is in it. -/
theorem off_in {b q : BitVec 64} {N o n : Nat} (hN : NativeRustcVm.NoWrap b N) (h1 : o + n ≤ N)
    (h : NativeRustcVm.InRange (off b o) n q) : NativeRustcVm.InRange b N q :=
  inRange_of_off hN h1 h

/-- **A block's label** is its address, from its place in a placed function (no evaluation of the
function's code). -/
theorem label_of_infix [Host] {F b : List Directive} {k j : Nat} {l : Label} (hp : Placed F k)
    (hb : b.IsInfixAt F j) (h0 : b[0]? = some (.label l)) : Labels.label l = Host.addrOf (k + j) := by
  apply hp.label
  cases b with
  | nil => simp at h0
  | cons x xs =>
    have h := (List.IsInfixAt.cons hb).1
    rw [h]
    exact h0

/-- The regions of `Areas` are data memory and do not wrap. -/
theorem Areas.ok {n : Nat} {ws rs : List Region} (h : Areas m0 n ws rs) {r : Region}
    (hr : r ∈ ws ++ rs) : r.Ok m0.dmem := h.1 r hr

/-- A written region is apart from the stack and the return address. -/
theorem Areas.apart_stack {n : Nat} {ws rs : List Region} (h : Areas m0 n ws rs) {w : Region}
    (hw : w ∈ ws) : NativeRustcVm.Apart w.addr w.size (stackBelow m0 n) (n + 8) := by
  have := List.rel_of_pairwise_cons h.2.1 hw
  unfold NativeRustcVm.Apart at this ⊢
  dsimp only [stackRegion] at this
  omega

/-- A written region is apart from a read one. -/
theorem Areas.apart_read {n : Nat} {ws rs : List Region} (h : Areas m0 n ws rs) {w r : Region}
    (hw : w ∈ ws) (hr : r ∈ rs) : NativeRustcVm.Apart w.addr w.size r.addr r.size :=
  h.2.2 w (List.mem_cons_of_mem _ hw) r hr

/-- The stack is apart from a read region. -/
theorem Areas.stack_read {n : Nat} {ws rs : List Region} (h : Areas m0 n ws rs) {r : Region}
    (hr : r ∈ rs) : NativeRustcVm.Apart (stackBelow m0 n) (n + 8) r.addr r.size :=
  h.2.2 _ List.mem_cons_self r hr

/-! ## Elements -/

/-- `n` elements `f i` from `a`, sixteen bytes each. -/
@[expose] def ElemsAt (d : DataMem) (a : BitVec 64) (f : Nat → EW) (n : Nat) : Prop :=
  ∀ i < n, NativeRustcVm.EWAt d (off a (16 * i)) (f i)

/-- **Elements kept** where memory changed only apart from them. -/
theorem ElemsAt.keep {d d' : DataMem} {a : BitVec 64} {f : Nat → EW} {n : Nat}
    {R : BitVec 64 → Prop} (h : ElemsAt d a f n) (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, NativeRustcVm.InRange a (16 * n) q → ¬R q) (hnw : NativeRustcVm.NoWrap a (16 * n)) :
    ElemsAt d' a f n :=
  fun i hi ↦ NativeRustcVm.BytesAt.of_sameOutside (h i hi) hs fun j hj ↦ by
    rw [NativeRustcVm.length_ewBytes] at hj
    rw [NativeRustcVm.Transcript.off_add]
    exact hR _ (NativeRustcVm.Transcript.inRange_off_self (by omega)
      (by unfold NativeRustcVm.NoWrap at hnw; omega))

/-- **One element changed**: elements but the `n`th kept, the `n`th the new one. -/
theorem ElemsAt.update {d d' : DataMem} {a : BitVec 64} {f : Nat → EW} {N n : Nat} {v : EW}
    (h : ElemsAt d a f N) (hnw : NativeRustcVm.NoWrap a (16 * N)) (hn : n < N)
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (off a (16 * n)) 16))
    (hv : NativeRustcVm.EWAt d' (off a (16 * n)) v) :
    ElemsAt d' a (fun i ↦ if i = n then v else f i) N := by
  intro i hi
  by_cases hin : i = n
  · subst hin; simpa using hv
  · simp only [hin, ite_false]
    refine NativeRustcVm.BytesAt.of_sameOutside (h i hi) hs fun j hj ↦ ?_
    rw [NativeRustcVm.length_ewBytes] at hj
    have := hnw
    unfold NativeRustcVm.NoWrap at this
    rw [NativeRustcVm.Transcript.off_add,
      NativeRustcVm.Transcript.inRange_off_iff (by omega) (by omega)]
    omega

/-- Element `i` of an array whose elements are at `a`. -/
theorem ewsAt_getD {d : DataMem} {a : BitVec 64} {xs : Array EW}
    (h : NativeRustcVm.EWsAt d a xs.toList) {i : Nat} (hi : i < xs.size) :
    NativeRustcVm.EWAt d (off a (16 * i)) (xs.getD i 0) := by
  have hi' : i < xs.toList.length := by simpa using hi
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, List.getElem?_eq_getElem hi',
    Option.getD_some]
  exact NativeRustcVm.EWsAt.getElem h hi'

/-- **Elements grown** by `k` new ones after `n`, nothing else of the range changed. -/
theorem ElemsAt.grow {D D' : DataMem} {a : BitVec 64} {f : Nat → EW} {n k : Nat}
    (h : ElemsAt D a f n) (hnw : (a.toNat + 16 * (n + k)) ≤ 2 ^ 64)
    (hs : NativeRustcVm.SameOutside D D' (NativeRustcVm.InRange (off a (16 * n)) (16 * k)))
    (hnew : ∀ j < k, NativeRustcVm.EWAt D' (off a (16 * (n + j))) (f (n + j))) :
    ElemsAt D' a f (n + k) := by
  intro i hi
  by_cases hin : i < n
  · refine bytesAt_congr (h i hin) fun j hj ↦ hs _ fun hq ↦ ?_
    rw [NativeRustcVm.length_ewBytes] at hj
    rw [NativeRustcVm.Transcript.off_add,
      NativeRustcVm.Transcript.inRange_off_iff (by omega) (by omega)] at hq
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
    exact hnew j (by omega)

/-- The elements as a list. -/
theorem ElemsAt.ewsAt {d : DataMem} {a : BitVec 64} {xs : List EW}
    (h : ElemsAt d a (fun i ↦ xs.getD i 0) xs.length) : NativeRustcVm.EWsAt d a xs := by
  rw [NativeRustcVm.ewsAt_iff]
  intro i hi
  have := h i hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
  exact this

/-- **An element a block wrote**: `v0` at `o`, `v1` at `o + 8`. -/
theorem Match.ewAt_write [Labels] {env : NativeRustcX64.Sym.Env} {S : NativeRustcX64.Sym.SState}
    {m : MachineData} (hm : NativeRustcX64.Sym.Match env S m) {r o : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + 16 ≤ sz) {v0 v1 : NativeRustcX64.Sym}
    (hw0 : ∀ i < 8, NativeRustcX64.Sym.findWrite r (o + i) S.mem = some (v0, i))
    (hw1 : ∀ i < 8, NativeRustcX64.Sym.findWrite r (o + 8 + i) S.mem = some (v1, i)) :
    NativeRustcVm.EWAt m.dmem (off b o)
      ⟨UInt64.ofBitVec (v0.eval env), UInt64.ofBitVec (v1.eval env)⟩ := by
  rw [NativeRustcVm.ewAt_iff, NativeRustcVm.Transcript.off_add]
  exact ⟨wordAt_write hm hb (by omega) hw0, wordAt_write hm hb (by omega) hw1⟩

/-! ## Words -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem beq_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_eq, toNat_ofNat_lt ha,
    toNat_ofNat_lt hb]

theorem add_ofNat' (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofNat_add]

end

end NativeRustcVmX64.KeccakGkr
