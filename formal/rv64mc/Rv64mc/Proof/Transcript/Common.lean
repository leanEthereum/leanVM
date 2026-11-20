/-
  Rv64mc.Proof.Transcript.Common

  What the transcript's proofs share: the frame of stores into a caller's frame (an `sret` slot, the transcript's
  fields), what they keep of a transcript, and the transcript's own fields updated one at a time
  (`TranscriptAt.setStream`), each in the address forms `rv_sym` computes.
-/

import Rv64mc.Spec.Transcript.Repr

namespace Rv64mc.Proof.Transcript

open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64mc.Spec.Transcript

variable {env : Env}

/-! ## Stores into a caller's frame -/

theorem ne_next {b top : Word} (hlim : env.stackLimit.toNat ≤ top.toNat) (hb : top.toNat ≤ b.toNat) :
    b ≠ env.nextAddr := fun h => by have := env.layout; rw [h] at hb; omega

/-- A store into the call's `out` at or above its stack top is in its frame. -/
theorem frame_store_out {top b v : Word} {out : Word → Prop} {m M : MachineState} (h : env.Frame top out m M)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hb : top.toNat ≤ b.toNat) (ho : out b) :
    env.Frame top out m (M.setMem b v) :=
  h.trans (Env.Frame.setMem_out h.2.1 ho (ne_next hlim hb)) (Nat.le_refl _)
    fun _ ha => Or.inr (Or.inr (Or.inr ha))

theorem static_store {top b v : Word} {M : MachineState} (hs : env.Static M)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hb : top.toNat ≤ b.toNat) : env.Static (M.setMem b v) :=
  Env.static_setMem_stack hs (by omega)

theorem heapKept_store {top b v : Word} {m M : MachineState} (h : HeapKept env m M)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hb : top.toNat ≤ b.toNat)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) : HeapKept env m (M.setMem b v) := by
  have hn : env.next (M.setMem b v) = env.next M := by
    simp [Env.next, MachineState.getMem, MachineState.setMem, Ne.symm (ne_next hlim hb)]
  refine ⟨by rw [hn]; exact h.1, fun c hc => ?_⟩
  have : c ≠ b := fun he => by have := env.layout; rw [he] at hc; omega
  rw [MachineState.getMem_setMem_ne this]; exact h.2 c hc

theorem heapKept_refl {m : MachineState} : HeapKept env m m := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem keeps_store {m M : MachineState} {a c v : Word} {n : Nat} (h : Keeps m M a n) (hc : ¬ InRange a n c) :
    Keeps m (M.setMem c v) a n :=
  h.trans (Keeps.setMem hc)

theorem keeps_refl {m : MachineState} {a : Word} {n : Nat} : Keeps m m a n := fun _ _ => rfl

/-- `a + k`, `k` below `n`, is in `[a, a + n)`. -/
theorem inRange_add {a : Word} {n k : Nat} (ha : a.toNat + n < 2 ^ 64) (hk : k < n) :
    InRange a n (a + BitVec.ofNat 64 k) := by
  constructor <;> rw [toNat_add_ofNat (by omega)] <;> omega

theorem inRange_self {a : Word} {n : Nat} (hn : 0 < n) : InRange a n a := ⟨Nat.le_refl _, by omega⟩

/-- A word of `[b, b + k)` is outside a footprint `[a, a + n)` apart from it. -/
theorem not_inRange_apart {a b : Word} {n k j : Nat} (h : Apart a n b k) (hb : b.toNat + k < 2 ^ 64) (hj : j < k) :
    ¬ InRange a n (b + BitVec.ofNat 64 j) := by
  rw [InRange, toNat_add_ofNat (by omega)]; unfold Apart at h; omega

theorem not_inRange_apart' {a b : Word} {n k j : Nat} (h : Apart b k a n) (hb : b.toNat + k < 2 ^ 64) (hj : j < k) :
    ¬ InRange a n (b + BitVec.ofNat 64 j) := by
  rw [InRange, toNat_add_ofNat (by omega)]; unfold Apart at h; omega

theorem toNat_le_add {a : Word} {k n : Nat} (ha : a.toNat + n < 2 ^ 64) (hk : k ≤ n) :
    a.toNat ≤ (a + BitVec.ofNat 64 k).toNat := by
  rw [toNat_add_ofNat (by omega)]; omega

/-- A `usize` the code shifts by four, as the address of element `o`. -/
theorem shl4 (o : Nat) : BitVec.ofNat 64 o <<< 4 = BitVec.ofNat 64 (16 * o) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mul_mod]

theorem ofNat_lt_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a < BitVec.ofNat 64 b ↔ a < b := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem ofNat_le_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a ≤ BitVec.ofNat 64 b ↔ a ≤ b := by
  rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem ofNat_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem ofNat_succ (o : Nat) : BitVec.ofNat 64 o + 1#64 = BitVec.ofNat 64 (o + 1) := by
  apply BitVec.eq_of_toNat_eq; simp

/-! ## Reads through stores at other bases -/

/-- A slot of the function's own stack lies below an object of a caller's frame (`a + k`, at or above `t`). -/
theorem slot_below {S need k K : Nat} {t c a : Word} (hS : S + need ≤ t.toNat) (hc : Tactic.slotOk need c = true)
    (hta : t.toNat ≤ a.toNat) (hak : a.toNat + K < 2 ^ 64) (hk : Nat.ble k K = true) :
    (t + c).toNat < (a + BitVec.ofNat 64 k).toNat := by
  have := Tactic.slot_lt hS hc; have := Nat.le_of_ble_eq_true hk; rw [toNat_add_ofNat (by omega)]; omega

theorem slot_below0 {S need : Nat} {t c a : Word} (hS : S + need ≤ t.toNat) (hc : Tactic.slotOk need c = true)
    (hta : t.toNat ≤ a.toNat) : (t + c).toNat < a.toNat := by
  have := Tactic.slot_lt hS hc; omega


theorem getMem_setMem_lt {M : MachineState} {b x v : Word} (h : b.toNat < x.toNat) :
    (M.setMem b v).getMem x = M.getMem x :=
  MachineState.getMem_setMem_ne fun he => by rw [he] at h; omega

theorem getMem_setMem_gt {M : MachineState} {b x v : Word} (h : x.toNat < b.toNat) :
    (M.setMem b v).getMem x = M.getMem x :=
  MachineState.getMem_setMem_ne fun he => by rw [he] at h; omega

/-- A store at another offset of the same base. -/
theorem getMem_setMem_off {M : MachineState} {t c d v : Word} (h : c ≠ d) :
    (M.setMem (t + d) v).getMem (t + c) = M.getMem (t + c) :=
  MachineState.getMem_setMem_ne fun he => h ((BitVec.add_right_inj t).1 he)

/-- Slot `n` of an array of `24`-byte objects, as the code scales the index: `(n << 4) + (n << 3)`. -/
theorem slot24 {n : Nat} (hn : n < 2 ^ 59) :
    BitVec.ofNat 64 n <<< 4 + BitVec.ofNat 64 n <<< 3 = BitVec.ofNat 64 (24 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := n) (by omega), Nat.mod_eq_of_lt (a := n * 2 ^ 4) (by omega),
    Nat.mod_eq_of_lt (a := n * 2 ^ 3) (by omega)]
  omega

theorem add_ofNat_lit {a : Word} {k c : Nat} : a + BitVec.ofNat 64 k + BitVec.ofNat 64 c = a + BitVec.ofNat 64 (k + c) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- A store into an object of a caller's frame that the call may write. -/
theorem frame_store_obj {top a v : Word} {k n : Nat} {out : Word → Prop} {m M : MachineState}
    (h : env.Frame top out m M) (hlim : env.stackLimit.toNat ≤ top.toNat) (hta : top.toNat ≤ a.toNat)
    (ha : a.toNat + n < 2 ^ 64) (hk : k < n) (hout : out (a + BitVec.ofNat 64 k)) :
    env.Frame top out m (M.setMem (a + BitVec.ofNat 64 k) v) :=
  frame_store_out h hlim (Nat.le_trans hta (toNat_le_add ha (Nat.le_of_lt hk))) hout

theorem static_store_obj {top a v : Word} {k n : Nat} {M : MachineState} (hs : env.Static M)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hta : top.toNat ≤ a.toNat) (ha : a.toNat + n < 2 ^ 64)
    (hk : k < n) : env.Static (M.setMem (a + BitVec.ofNat 64 k) v) :=
  static_store hs hlim (Nat.le_trans hta (toNat_le_add ha (Nat.le_of_lt hk)))

/-- Two slots of the function's own stack, in their order. -/
theorem slot_mono {S need : Nat} {t c d : Word} (h : S + need ≤ t.toNat) (hc : Tactic.slotOk need c = true)
    (hd : Tactic.slotOk need d = true) (hcd : decide (c.toInt ≤ d.toInt) = true) :
    (t + c).toNat ≤ (t + d).toNat := by
  simp only [Tactic.slotOk, decide_eq_true_eq] at hc hd hcd
  have h1 := Tactic.toNat_add_neg (t := t) (c := c) (by omega) (by omega)
  have h2 := Tactic.toNat_add_neg (t := t) (c := d) (by omega) (by omega)
  omega

/-! ## A transcript's fields -/

/-- Two offsets of a footprint that does not wrap name different words. -/
theorem add_ne_add {a : Word} {j k n : Nat} (ha : a.toNat + n < 2 ^ 64) (hj : j < n) (hk : k < n) (h : j ≠ k) :
    a + BitVec.ofNat 64 j ≠ a + BitVec.ofNat 64 k := fun he => by
  rw [← BitVec.toNat_inj, toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)] at he; exact h (by omega)

theorem ne_add_self {a : Word} {k n : Nat} (ha : a.toNat + n < 2 ^ 64) (hk : 0 < k) (hkn : k < n) :
    a ≠ a + BitVec.ofNat 64 k := fun he => by
  have := congrArg BitVec.toNat he; rw [toNat_add_ofNat (by omega)] at this; omega

/-- The base of a footprint `[b, b + k)` is outside a footprint `[a, a + n)` apart from it. -/
theorem not_inRange_apart0 {a b : Word} {n k : Nat} (h : Apart b k a n) (hk : 0 < k) : ¬ InRange a n b := by
  unfold InRange; unfold Apart at h; omega

/-- A store into a footprint in the stack keeps the heap below `NEXT`. -/
theorem heapKept_stack {m : MachineState} {b v : Word} (hlim : env.stackLimit.toNat ≤ b.toNat)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) : HeapKept env m (m.setMem b v) := by
  have hb : b ≠ env.nextAddr := fun h => by have := env.layout; rw [h] at hlim; omega
  have hn : env.next (m.setMem b v) = env.next m := by
    simp [Env.next, MachineState.getMem, MachineState.setMem, Ne.symm hb]
  refine ⟨by rw [hn], fun c hc => ?_⟩
  have : c ≠ b := fun he => by have := env.layout; rw [he] at hc; omega
  rw [MachineState.getMem_setMem_ne this]

/-- **The stream offset written**: the transcript at `a`, in the stack, with `streamOffset` replaced. -/
theorem _root_.Rv64mc.Spec.Transcript.TranscriptAt.setStream {m : MachineState} {a : Word} {t : Model.TState} (ht : TranscriptAt env m a t)
    (ha : a.toNat + Layouts.Transcript.byteSize < 2 ^ 64) (hlim : env.stackLimit.toNat ≤ a.toNat)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) {o : Nat} (ho : o ≤ t.proof.stream.length) :
    TranscriptAt env (m.setMem (a + BitVec.ofNat 64 Layouts.Transcript.stream_offset) (BitVec.ofNat 64 o)) a
      { t with streamOffset := o } := by
  simp only [Layouts.Transcript.byteSize] at ha
  obtain ⟨-, hb2, hs, hp, hap, h1, h2, h3⟩ := ht
  have h336 : (a + BitVec.ofNat 64 336).toNat = a.toNat + 336 := toNat_add_ofNat (by omega)
  have hk : Keeps m (m.setMem (a + BitVec.ofNat 64 336) (BitVec.ofNat 64 o)) (a + BitVec.ofNat 64 0) 328 :=
    Keeps.setMem fun h => by unfold InRange at h; rw [h336] at h; simp at h
  have hne := add_ne_add (n := 360) (j := 328) (k := 336) ha (by decide) (by decide) (by decide)
  refine ⟨ho, hb2, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Layouts.Transcript.sponge, Layouts.Transcript.proof, Layouts.Transcript.stream_offset,
      Layouts.Transcript.opening_offset, Layouts.Transcript.checked, Layouts.Proof.byteSize,
      Layouts.Transcript.byteSize] at hs hp hap h1 h2 h3 ⊢
  · exact hs.keep (by rw [show a + BitVec.ofNat 64 0 = a by simp]; simp only [Layouts.Sponge.byteSize]; omega) hk
  · rw [MachineState.getMem_setMem_ne hne]
    exact hp.keep (heapKept_stack (by omega) hnx) (Keeps.setMem fun h => by
      unfold InRange at h; unfold Apart at hap; rw [h336] at h; simp only [Layouts.Proof.byteSize] at h; omega)
  · rw [MachineState.getMem_setMem_ne hne]; exact hap
  · simp
  · rw [MachineState.getMem_setMem_ne (add_ne_add (n := 360) ha (by decide) (by decide) (by decide))]; exact h2
  · rw [getByte_setMem_ne]; exact h3
    intro h
    have := congrArg BitVec.toNat h
    rw [h336, toNat_alignToDword, toNat_add_ofNat (by omega)] at this
    omega

/-! ## A waiting scalar pushed -/

/-- The memory after `absorb`'s four stores: the slot's limbs and tag, then the count. -/
abbrev pushMem (B : MachineState) (a : Word) (n : Nat) (c0 c1 tag : Word) : MachineState :=
  (((B.setMem (a + BitVec.ofNat 64 (24 * n + 224)) c0).setMem (a + BitVec.ofNat 64 (24 * n + 232)) c1).setMem
    (a + BitVec.ofNat 64 (24 * n + 240)) tag).setMem (a + 320#64) (BitVec.ofNat 64 n + 1#64)

theorem pushMem_get {B : MachineState} {a : Word} {n k : Nat} {c0 c1 tag : Word} (ha : a.toNat + 328 < 2 ^ 64)
    (hn : n < 4) (hk : k < 328) (h0 : k ≠ 24 * n + 224) (h1 : k ≠ 24 * n + 232) (h2 : k ≠ 24 * n + 240)
    (h3 : k ≠ 320) : (pushMem B a n c0 c1 tag).getMem (a + BitVec.ofNat 64 k) = B.getMem (a + BitVec.ofNat 64 k) := by
  simp only [pushMem]
  rw [show (320#64 : Word) = BitVec.ofNat 64 320 from rfl]
  rw [MachineState.getMem_setMem_ne (add_ne_add (n := 328) ha hk (by omega) h3),
    MachineState.getMem_setMem_ne (add_ne_add (n := 328) ha hk (by omega) h2),
    MachineState.getMem_setMem_ne (add_ne_add (n := 328) ha hk (by omega) h1),
    MachineState.getMem_setMem_ne (add_ne_add (n := 328) ha hk (by omega) h0)]

/-- **A waiting scalar pushed**: `absorb`'s stores make the sponge `r.push (e, tag)`. -/
theorem _root_.Rv64mc.Spec.Transcript.SpongeAt.push {B : MachineState} {a : Word} {r : Model.SpongeRust}
    (h : SpongeAt B a r) (ha : a.toNat + 328 < 2 ^ 64) (hn : r.nPending < 4) (e : LeanVM.Parameters.E)
    (tag : Word) :
    SpongeAt (pushMem B a r.nPending (Model.limbs e).1 (Model.limbs e).2 tag) a (r.push (e, tag)) := by
  obtain ⟨hal, hi, hst, hp, -, hg⟩ := h
  have add : ∀ j k, a + BitVec.ofNat 64 j + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (j + k) :=
    fun _ _ => add_ofNat_lit
  have get := fun {k : Nat} (hk : k < 328) (h0 : k ≠ 24 * r.nPending + 224) (h1 : k ≠ 24 * r.nPending + 232)
    (h2 : k ≠ 24 * r.nPending + 240) (h3 : k ≠ 320) =>
    pushMem_get (B := B) (c0 := (Model.limbs e).1) (c1 := (Model.limbs e).2) (tag := tag) ha hn hk h0 h1 h2 h3
  simp only [PendingAt, EAt, pendingSlot, pendingTag, Layouts.Sponge.state, Layouts.Sponge.pending,
    Layouts.Sponge.n_pending, Layouts.Sponge.ground, Layouts.E.c0, Layouts.E.c1, Layouts.E.byteSize] at hst hp hg
  refine ⟨hal, ⟨hi.1, by simp [hi.2.1], by simp; omega⟩, ⟨hst.1, fun k hk' => ?_⟩, fun k hk' => ?_, ?_, ?_⟩
  · have := hi.1; simp only [Model.push_state] at hk' ⊢
    simp only [Layouts.Sponge.state]; rw [add, get (by omega) (by omega) (by omega) (by omega) (by omega), ← add]
    exact hst.2 k hk'
  · have h4 := hi.2.1
    simp only [Model.push_pending, Model.push_nPending, List.length_take, List.length_set] at hk'
    simp only [EAt, pendingSlot, pendingTag, Layouts.Sponge.pending, Layouts.Sponge.n_pending, Layouts.E.c0,
      Layouts.E.c1, Layouts.E.byteSize, Model.push_pending, Model.push_nPending, List.getElem_take]
    by_cases hkn : k < r.nPending
    · obtain ⟨⟨h0, h1⟩, h2⟩ := hp k (by simp; omega)
      simp only [List.getElem_take] at h0 h1 h2
      rw [List.getElem_set_ne (by omega)]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [add, add, get (by omega) (by omega) (by omega) (by omega) (by omega), ← add, ← add]; exact h0
      · rw [add, add, get (by omega) (by omega) (by omega) (by omega) (by omega), ← add, ← add]; exact h1
      · rw [add, get (by omega) (by omega) (by omega) (by omega) (by omega), ← add]; exact h2
    · have hk : k = r.nPending := by omega
      subst hk
      rw [List.getElem_set_self]
      have hne := fun {i j : Nat} (hi : i < 328) (hj : j < 328) (hij : i ≠ j) => add_ne_add (n := 328) ha hi hj hij
      simp only [pushMem, add, add_zero]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [show (320#64 : Word) = BitVec.ofNat 64 320 from rfl, MachineState.getMem_setMem_ne (hne (by omega) (by omega) (by omega)),
          MachineState.getMem_setMem_ne (hne (by omega) (by omega) (by omega)),
          MachineState.getMem_setMem_ne (hne (by omega) (by omega) (by omega)), show 224 + 24 * r.nPending = 24 * r.nPending + 224 by omega,
          MachineState.getMem_setMem_eq]
      · rw [show (320#64 : Word) = BitVec.ofNat 64 320 from rfl, MachineState.getMem_setMem_ne (hne (by omega) (by omega) (by omega)),
          MachineState.getMem_setMem_ne (hne (by omega) (by omega) (by omega)),
          show 224 + 24 * r.nPending + 8 = 24 * r.nPending + 232 by omega, MachineState.getMem_setMem_eq]
      · rw [show (320#64 : Word) = BitVec.ofNat 64 320 from rfl, MachineState.getMem_setMem_ne (hne (by omega) (by omega) (by omega)),
          show 224 + (24 * r.nPending + 16) = 24 * r.nPending + 240 by omega, MachineState.getMem_setMem_eq]
  · simp only [pushMem, Layouts.Sponge.n_pending, Model.push_nPending, ofNat_succ]
    exact MachineState.getMem_setMem_eq
  · simp only [Layouts.Sponge.ground, Model.push_ground]
    cases hr : r.ground with
    | none =>
      rw [hr] at hg
      simp only [OptionEAt, Layouts.OptionE.tagOffset, Layouts.OptionE.None.tag] at hg ⊢
      rw [add, get (by omega) (by omega) (by omega) (by omega) (by omega), ← add]; exact hg
    | some e' =>
      rw [hr] at hg
      simp only [OptionEAt, EAt, Layouts.OptionE.tagOffset, Layouts.OptionE.Some.f0, Layouts.OptionE.Some.tag,
        Layouts.E.c0, Layouts.E.c1] at hg ⊢
      refine ⟨?_, ?_, ?_⟩
      · rw [add, get (by omega) (by omega) (by omega) (by omega) (by omega), ← add]; exact hg.1
      · rw [add, add, get (by omega) (by omega) (by omega) (by omega) (by omega), ← add, ← add]; exact hg.2.1
      · rw [add, add, get (by omega) (by omega) (by omega) (by omega) (by omega), ← add, ← add]; exact hg.2.2

/-- **A sponge whose ground challenge changed**: every word past the ground kept, the new ground in place. -/
theorem _root_.Rv64mc.Spec.Transcript.SpongeAt.setGround {B M : MachineState} {a : Word} {r : Model.SpongeRust}
    (h : SpongeAt B a r)
    (hk : ∀ k, 24 ≤ k → k < 328 → M.getMem (a + BitVec.ofNat 64 k) = B.getMem (a + BitVec.ofNat 64 k))
    {g : Option LeanVM.Parameters.E} (hg : OptionEAt M (a + BitVec.ofNat 64 Layouts.Sponge.ground) g) :
    SpongeAt M a { r with ground := g } := by
  obtain ⟨hal, hi, hst, hp, hn, -⟩ := h
  have add : ∀ j k, a + BitVec.ofNat 64 j + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (j + k) :=
    fun _ _ => add_ofNat_lit
  simp only [PendingAt, EAt, pendingSlot, pendingTag, Layouts.Sponge.state, Layouts.Sponge.pending,
    Layouts.Sponge.n_pending, Layouts.E.c0, Layouts.E.c1, Layouts.E.byteSize] at hst hp hn
  refine ⟨hal, hi, ⟨hst.1, fun k hk' => ?_⟩, fun k hk' => ?_, ?_, hg⟩
  · have := hi.1; simp only [Layouts.Sponge.state] at hk' ⊢; rw [add, hk _ (by omega) (by omega), ← add]
    exact hst.2 k hk'
  · have hk4 : k < 4 := by have := hi.2.2; simp at hk'; omega
    obtain ⟨⟨h0, h1⟩, h2⟩ := hp k hk'
    simp only [EAt, pendingSlot, pendingTag, Layouts.Sponge.pending, Layouts.Sponge.n_pending, Layouts.E.c0,
      Layouts.E.c1, Layouts.E.byteSize]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [add, add, hk _ (by omega) (by omega), ← add, ← add]; exact h0
    · rw [add, add, hk _ (by omega) (by omega), ← add, ← add]; exact h1
    · rw [add, hk _ (by omega) (by omega), ← add]; exact h2
  · simp only [Layouts.Sponge.n_pending]; rw [hk _ (by decide) (by decide)]; exact hn

/-- **The ground challenge taken**: its tag cleared. -/
theorem _root_.Rv64mc.Spec.Transcript.SpongeAt.clearGround {B : MachineState} {a : Word} {r : Model.SpongeRust}
    (h : SpongeAt B a r) (ha : a.toNat + 328 < 2 ^ 64) :
    SpongeAt (B.setMem a 0#64) a { r with ground := none } :=
  h.setGround (fun k hk hk' => MachineState.getMem_setMem_ne (ne_add_self (n := 328) ha (by omega) hk').symm)
    (by simp [OptionEAt])

/-! ## The proof's stream -/

/-- The stream's length, at the address the code reads it. -/
theorem _root_.Rv64mc.Spec.Transcript.ProofAt.stream_len {m : MachineState} {q : Word} {pf : Proof} (h : ProofAt env m q pf) :
    m.getMem (q + 16#64) = BitVec.ofNat 64 pf.stream.length ∧ pf.stream.length < 2 ^ 63 := by
  obtain ⟨ptr, cap, hv, -⟩ := h.stream
  have hl := hv.len_eq; have := hv.len_le; have := hv.cap_lt
  simp only [vecLen, Layouts.Proof.stream, Layouts.Vec.len, List.length_map] at *
  refine ⟨by simpa using hl, by omega⟩

/-- The number of phases of openings, at the address the code reads it. -/
theorem _root_.Rv64mc.Spec.Transcript.ProofAt.openings_len {m : MachineState} {q : Word} {pf : Proof}
    (h : ProofAt env m q pf) :
    m.getMem (q + 40#64) = BitVec.ofNat 64 pf.openings.length ∧ pf.openings.length < 2 ^ 63 := by
  obtain ⟨ptr, cap, hv, -⟩ := h.openings
  have hl := hv.len_eq; have := hv.len_le; have := hv.cap_lt
  simp only [vecLen, Layouts.Proof.merkle_openings, Layouts.Vec.len] at *
  refine ⟨by rw [← hl, BitVec.add_assoc]; rfl, by omega⟩

/-- Element `o` of the stream, at the addresses the code reads it: the buffer's pointer at `q + 8`, the element at
    `o <<< 4` past it. -/
theorem _root_.Rv64mc.Spec.Transcript.ProofAt.stream_elem {m : MachineState} {q : Word} {pf : Proof} (h : ProofAt env m q pf) {o : Nat}
    (ho : o < pf.stream.length) :
    m.getMem (m.getMem (q + 8#64) + BitVec.ofNat 64 o <<< 4) = (Model.limbs pf.stream[o]).1 ∧
      m.getMem (m.getMem (q + 8#64) + BitVec.ofNat 64 o <<< 4 + 8#64) = (Model.limbs pf.stream[o]).2 := by
  obtain ⟨ptr, cap, hv, -⟩ := h.stream
  have hp := hv.ptr_eq
  have he := hv.elems.2 o (by simpa using ho)
  simp only [vecPtr, Layouts.Proof.stream, Layouts.Vec.ptr, EAt, Layouts.E.c0, Layouts.E.c1, Layouts.E.byteSize,
    List.getElem_map] at hp he
  rw [show q + BitVec.ofNat 64 0 + BitVec.ofNat 64 8 = q + 8#64 by simp] at hp
  rw [hp, shl4]
  simpa using he

end Rv64mc.Proof.Transcript
