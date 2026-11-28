module

public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Sumcheck.Common
public import NativeRustcVmArm.Basic
public import NativeRustcVmArm.Spec.KeccakGkr

/-!
# Phase 6's proofs: what they share

- A function's body (`Frame`): `F` bytes of frame below the entry's SP, the prologue's slots there
  (`Arrays.SlotsAt`), the other callee-saved registers the entry's, memory as at the entry but in
  the regions it writes and its stack (`Writes`), every mapped byte kept. A body is kept by a block
  that writes nothing (`Frame.of_block`), by a block that writes into the written regions
  (`Frame.write`), by a call (`Frame.call`); the prologue makes one (`Frame.of_entry`), the epilogue
  restores the entry's registers (`Frame.saved`).
- Elements: an element of `E` at a region's offset as the environment loads it (`load_ew`), an
  element a block wrote (`Match.ewAt_write`).
-/

namespace NativeRustcVmArm.KeccakGkr

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVm (Region InAny)
open NativeRustcArm.Sym (findWrite_cons)

public section

/-! ## Footprints -/

theorem Areas.ok {m : MachineData} {n : Nat} {ws rs : List Region} (h : Areas m n ws rs) {r : Region}
    (hr : r ∈ ws ∨ r ∈ rs) : r.Ok m.dmem :=
  h.1 r (List.mem_append.mpr hr)

theorem Areas.apart_ws {m : MachineData} {n : Nat} {ws rs : List Region} (h : Areas m n ws rs)
    {i j : Nat} (hi : i < ws.length) (hj : j < ws.length) (hij : i ≠ j) :
    Apart ws[i].addr ws[i].size ws[j].addr ws[j].size := by
  have h2 := NativeRustcVm.Disjoint.apart h.2.1 (i := i + 1) (j := j + 1) (by simp; omega)
    (by simp; omega) (by omega)
  simp only [List.getElem_cons_succ] at h2
  exact h2

theorem Areas.apart_stack {m : MachineData} {n : Nat} {ws rs : List Region} (h : Areas m n ws rs)
    {w : Region} (hw : w ∈ ws) : Apart w.addr w.size (stackBelow m n) n := by
  have h1 := h.2.1
  rw [stackRegion, NativeRustcVm.disjoint_cons_iff] at h1
  exact (h1.1 w hw).symm

theorem Areas.apart_rs {m : MachineData} {n : Nat} {ws rs : List Region} (h : Areas m n ws rs)
    {w r : Region} (hw : w ∈ ws) (hr : r ∈ rs) : Apart w.addr w.size r.addr r.size :=
  h.2.2 w (List.mem_cons_of_mem _ hw) r hr

theorem Areas.stack_rs {m : MachineData} {n : Nat} {ws rs : List Region} (h : Areas m n ws rs)
    {r : Region} (hr : r ∈ rs) : Apart (stackBelow m n) n r.addr r.size :=
  h.2.2 _ List.mem_cons_self r hr

/-! ## The body of a function -/

/-- **A function's body**: `F` bytes of frame below the entry's SP `m0`, the prologue's slots
there, the other callee-saved registers the entry's, memory as at the entry but in the regions
`ws` and the `N` bytes of stack, every mapped byte still there. -/
structure Frame (m0 : MachineData) (F N : Nat) (slots : List (Nat × XReg)) (ws : List Region)
    (st : MachineData) : Prop where
  sp : st.regs.SP.toBitVec = m0.regs.SP.toBitVec - BitVec.ofNat 64 F
  frame : SlotsAt st.dmem (m0.regs.SP.toBitVec - BitVec.ofNat 64 F) m0 slots
  regs : ∀ r, calleeSaved r = true → r ∉ slots.map (·.2) → st.regs.getXReg r = m0.regs.getXReg r
  same : Writes m0 st N ws
  kept : Kept m0.dmem st.dmem

variable {m0 st st' : MachineData} {F N n : Nat} {slots : List (Nat × XReg)} {ws : List Region}

/-- The written regions are apart from the stack: no byte of one is a byte of the stack. -/
def WsOff (m0 : MachineData) (N : Nat) (ws : List Region) : Prop :=
  ∀ p, InAny ws p → ¬InRange (stackBelow m0 N) N p

theorem wsOff_of_areas {rs : List Region} (h : Areas m0 N ws rs) (hS : StackOk m0 N) :
    WsOff m0 N ws := by
  rintro p ⟨w, hw, hp⟩ hs
  exact NativeRustcVm.Apart.not_inRange (Areas.apart_stack h hw) (Areas.ok h (Or.inl hw)).2 (noWrap_stackBelow hS) hp hs

/-- The SP of a body, as a number. -/
theorem Frame.sp_toNat (hb : Frame m0 F N slots ws st) (hS : StackOk m0 N) (hF : F ≤ N) :
    st.regs.SP.toNat = m0.regs.SP.toNat - F := by
  rw [← UInt64.toNat_toBitVec, hb.sp, BitVec.toNat_sub, BitVec.toNat_ofNat, UInt64.toNat_toBitVec]
  have := m0.regs.SP.toNat_lt
  have := hS.2.1
  omega

/-- **A callee's stack** `n` bytes below a body's SP is in the function's. -/
theorem Frame.stack_in (hb : Frame m0 F N slots ws st) (hS : StackOk m0 N) (hle : F + n ≤ N)
    {p : BitVec 64} (h : InRange (stackBelow st n) n p) : InRange (stackBelow m0 N) N p := by
  unfold stackBelow at h
  rw [hb.sp] at h
  exact inRange_stack hle hS.2.1 h

/-- A callee's `StackOk` in a body. -/
theorem Frame.stackOk (hb : Frame m0 F N slots ws st) (hS : StackOk m0 N) (hF : F % 16 = 0)
    (hle : F + n ≤ N) : StackOk st n :=
  StackOk.sub hS hb.sp hF hle hb.kept

/-- A region apart from the function's stack is apart from a callee's. -/
theorem Frame.apart_callee (hb : Frame m0 F N slots ws st) (hS : StackOk m0 N) (hle : F + n ≤ N)
    {a : BitVec 64} {k : Nat} (h : Apart a k (stackBelow m0 N) N) :
    Apart a k (stackBelow st n) n :=
  Apart.stack_sub h hb.sp hle hS.2.1

/-- The frame's bytes are not in a callee's stack nor in a written region. -/
theorem slot_not (hS : StackOk m0 N) (hF : F ≤ N)
    (hws : WsOff m0 N ws) {o i : Nat} (hoi : o + i < F) :
    ¬InAny ws (m0.regs.SP.toBitVec - BitVec.ofNat 64 F + BitVec.ofNat 64 (o + i)) := by
  intro h
  apply hws _ h
  unfold InRange stackBelow
  have hN : N ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  have e : m0.regs.SP.toBitVec - BitVec.ofNat 64 F + BitVec.ofNat 64 (o + i) -
      (m0.regs.SP.toBitVec - BitVec.ofNat 64 N) = BitVec.ofNat 64 (N - F + (o + i)) := by
    bv_omega
  rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- **A call** keeps a body: the callee changes memory only in its stack, `n` bytes below the
body's SP, and in written regions (`R`), and keeps the callee-saved registers and SP. -/
theorem Frame.call (hb : Frame m0 F N slots ws st) (hS : StackOk m0 N) (hle : F + n ≤ N)
    (hslots : ∀ p ∈ slots, p.1 + 8 ≤ F) (hws : WsOff m0 N ws) {R : BitVec 64 → Prop}
    (hsame : SameOutside st.dmem st'.dmem R)
    (hR : ∀ p, R p → InRange (stackBelow st n) n p ∨ InAny ws p) (hsaved : Saved st st') :
    Frame m0 F N slots ws st' := by
  refine ⟨hsaved.2.1 ▸ hb.sp, fun p hp i hi ↦ ?_, fun r hr hn ↦ (hsaved.1 r hr).trans
    (hb.regs r hr hn), fun p hp ↦ ?_, fun p hp ↦ hsaved.2.2 p (hb.kept p hp)⟩
  · simp only [List.length_map, List.length_range] at hi
    have hpo := hslots p hp
    rw [hsame _ ?_]
    · exact hb.frame p hp i (by simpa using hi)
    · intro hRp
      rcases hR _ hRp with h | h
      · unfold stackBelow at h
        rw [hb.sp, addr_add] at h
        have := m0.regs.SP.toNat_lt
        exact not_inRange_below (by have := hS.2.1; omega) h
      · rw [addr_add] at h
        exact slot_not hS (by omega) hws (by omega) h
  · rw [hsame p fun h ↦ ?_]
    · exact hb.same p hp
    · rcases hR p h with h | h
      · exact hp ⟨stackRegion m0 N, List.mem_cons_self, hb.stack_in hS hle h⟩
      · obtain ⟨w, hw, hpw⟩ := h
        exact hp ⟨w, List.mem_cons_of_mem _ hw, hpw⟩

/-- **A block that writes nothing and keeps the callee-saved registers and SP** keeps a body. -/
theorem Frame.of_block [Labels] {env : Env} {S₀ S₁ : SState} {rs : List XReg}
    (hb : Frame m0 F N slots ws st)
    (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF) (hd : st.dmem = env.mem0)
    (hrs : ∀ r, calleeSaved r = true → r ∉ slots.map (·.2) → r ∈ rs)
    (hk : keepsAll S₀ S₁ rs = true) : Frame m0 F N slots ws st' := by
  simp only [keepsAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.isEmpty_iff] at hk
  obtain ⟨⟨hr, hsp⟩, hmem⟩ := hk
  have hdm : st'.dmem = st.dmem := (hm.dmem_eq hwf hmem).trans hd.symm
  refine ⟨?_, ?_, fun r hr' hn ↦ ?_, ?_, ?_⟩
  · rw [Match.sp_eq hm₀ hm hsp]; exact hb.sp
  · rw [hdm]; exact hb.frame
  · obtain ⟨hs, he⟩ := hr r (hrs r hr' hn)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    rw [Match.reg_eq hm₀ hm hv (he.trans hv)]
    exact hb.regs r hr' hn
  · intro p hp; rw [hdm]; exact hb.same p hp
  · rw [hdm]; exact hb.kept

/-- `S` keeps `S₀`'s SP and every register of `rs`. -/
@[expose] def keepsRegs (S₀ S : SState) (rs : List XReg) : Bool :=
  rs.all (fun r ↦ (S₀.reg r).isSome && S.reg r == S₀.reg r) && S.sp == S₀.sp

/-- **A block that writes only into written regions** (each write in an environment region inside
one of them) and keeps the callee-saved registers and SP keeps a body. -/
theorem Frame.write [Labels] {env : Env} {S₀ S₁ : SState} {rs : List XReg}
    (hb : Frame m0 F N slots ws st)
    (hS : StackOk m0 N) (hF : F ≤ N) (hslots : ∀ p ∈ slots, p.1 + 8 ≤ F) (hws : WsOff m0 N ws)
    (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF) (hd : st.dmem = env.mem0)
    (hrs : ∀ r, calleeSaved r = true → r ∉ slots.map (·.2) → r ∈ rs)
    (hk : keepsRegs S₀ S₁ rs = true)
    (hin : ∀ p, Written env S₁ p → InAny ws p) : Frame m0 F N slots ws st' := by
  simp only [keepsRegs, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hk
  obtain ⟨hr, hsp⟩ := hk
  have hso : NativeRustcArm.SameOutside st.dmem st'.dmem (Written env S₁) := by
    rw [hd]; exact hm.sameOutside hwf
  refine ⟨?_, fun p hp i hi ↦ ?_, fun r hr' hn ↦ ?_, fun p hp ↦ ?_, ?_⟩
  · rw [Match.sp_eq hm₀ hm hsp]; exact hb.sp
  · simp only [List.length_map, List.length_range] at hi
    have hpo := hslots p hp
    rw [hso _ fun hw ↦ ?_]
    · exact hb.frame p hp i (by simpa using hi)
    · have := hin _ hw
      rw [addr_add] at this
      exact slot_not hS hF hws (by omega) this
  · obtain ⟨hs, he⟩ := hr r (hrs r hr' hn)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    rw [Match.reg_eq hm₀ hm hv (he.trans hv)]
    exact hb.regs r hr' hn
  · rw [hso p fun hw ↦ hp ?_]
    · exact hb.same p hp
    · obtain ⟨w, hw', hpw⟩ := hin p hw
      exact ⟨w, List.mem_cons_of_mem _ hw', hpw⟩
  · exact fun p h ↦ hm.kept hwf p (by rw [← hd]; exact hb.kept p h)

/-! ## The frame's locals

The bytes of the frame below the prologue's slots (`lo` bytes from its base) are the function's
locals: blocks and callees may change them. -/

/-- The frame's locals are in the function's stack. -/
theorem local_inStack (hS : StackOk m0 N) (hF : F ≤ N) {lo : Nat} (hlo : lo ≤ F) {p : BitVec 64}
    (h : InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 F) lo p) :
    InRange (stackBelow m0 N) N p := by
  have hN : N ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  unfold stackBelow
  refine inRange_stack (F := F - lo) (n := lo) (by omega) hN ?_
  rwa [show m0.regs.SP.toBitVec - BitVec.ofNat 64 (F - lo) - BitVec.ofNat 64 lo =
    m0.regs.SP.toBitVec - BitVec.ofNat 64 F by
    apply BitVec.eq_of_toNat_eq
    have := m0.regs.SP.toBitVec.isLt
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show F - lo < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show lo < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show F < 2 ^ 64 by omega)]
    omega]

/-- A slot's byte is not a local. -/
theorem slot_not_local {fb : BitVec 64} {lo o : Nat} (hlo : lo ≤ o) (ho : o < 2 ^ 64) :
    ¬InRange fb lo (fb + BitVec.ofNat 64 o) := by
  unfold InRange
  rw [show fb + BitVec.ofNat 64 o - fb = BitVec.ofNat 64 o by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ho]
  omega

/-- The bytes a block wrote, all in the first `L` bytes of region `r`. -/
theorem Written.inRange_le {env : Env} {S : SState} {r : Nat} {b : BitVec 64} {sz L : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hnw : b.toNat + sz ≤ 2 ^ 64) (hL : L ≤ sz)
    (hS : ∀ w ∈ S.mem, w.r = r ∧ w.off + w.n ≤ L) {p : BitVec 64} (h : Written env S p) :
    InRange b L p := by
  obtain ⟨w, hw, b', sz', hb', h1, h2⟩ := h
  obtain ⟨hr, hle⟩ := hS w hw
  rw [hr, hb] at hb'
  cases hb'
  exact (NativeRustcVm.inRange_iff (show b.toNat + L ≤ 2 ^ 64 by omega)).mpr ⟨by omega, by omega⟩

/-- The bytes a block wrote, all from byte `lo` to byte `hi` of region `r`. -/
theorem Written.inRange_sub {env : Env} {S : SState} {r : Nat} {b : BitVec 64} {sz lo hi : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hnw : b.toNat + sz ≤ 2 ^ 64) (hhi : hi ≤ sz)
    (hS : ∀ w ∈ S.mem, w.r = r ∧ lo ≤ w.off ∧ w.off + w.n ≤ hi) {p : BitVec 64}
    (h : Written env S p) : InRange (b + BitVec.ofNat 64 lo) (hi - lo) p := by
  obtain ⟨w, hw, b', sz', hb', h1, h2⟩ := h
  obtain ⟨hr, hlo, hle⟩ := hS w hw
  rw [hr, hb] at hb'
  cases hb'
  have e : (b + BitVec.ofNat 64 lo).toNat = b.toNat + lo := toNat_add_ofNat' (by omega)
  exact (NativeRustcVm.inRange_iff (show (b + BitVec.ofNat 64 lo).toNat + (hi - lo) ≤ 2 ^ 64 by
    omega)).mpr ⟨by omega, by omega⟩

/-- **Bytes copied**: what `memcpy` wrote at `dst` holds the bytes the source held. -/
theorem bytes_copy {d d' : DataMem} {src dst : BitVec 64} {n o : Nat} {bs : List UInt8}
    (h : NativeRustcVm.BytesAt d (src + BitVec.ofNat 64 o) bs)
    (hc : NativeRustcVm.BytesAt d' dst (NativeRustcArm.bytesOf d src n)) (hle : o + bs.length ≤ n) :
    NativeRustcVm.BytesAt d' (dst + BitVec.ofNat 64 o) bs := by
  intro i hi
  have := hc (o + i) (by simp [NativeRustcArm.bytesOf]; omega)
  rw [NativeRustcVm.addr_add_add, this]
  simp only [NativeRustcArm.bytesOf, List.getElem_map, List.getElem_range]
  rw [← NativeRustcVm.addr_add_add, h i hi, Option.getD_some]

/-- **A `Buf<EW, N>` copied.** -/
theorem BufEWAt.copy {d d' : DataMem} {src dst : BitVec 64} {N : Nat} {xs : List EW}
    (h : NativeRustcVm.BufEWAt d src N xs)
    (hc : NativeRustcVm.BytesAt d' dst (NativeRustcArm.bytesOf d src (8 + 16 * N))) :
    NativeRustcVm.BufEWAt d' dst N xs := by
  obtain ⟨hl, hw, he⟩ := h
  refine ⟨hl, ?_, ?_⟩
  · have := bytes_copy (o := 0) (by rw [NativeRustcVm.addr_add_zero]; exact hw) hc
      (by rw [NativeRustcVm.length_wordBytes]; omega)
    rwa [NativeRustcVm.addr_add_zero] at this
  · exact bytes_copy (o := 8) he hc (by rw [NativeRustcVm.length_ewsBytes]; omega)

/-- A `Buf<EW, N>`'s elements as `bufEWOf` reads them. -/
theorem bufEWOf_eq {d : DataMem} {p : BitVec 64} {N : Nat} {xs : List EW}
    (h : NativeRustcVm.BufEWAt d p N xs) (hN : N < 2 ^ 64) : NativeRustcVm.bufEWOf d p = xs := by
  obtain ⟨hl, hw, he⟩ := h
  unfold NativeRustcVm.bufEWOf
  rw [NativeRustcVm.wordOf_of_wordAt hw, Nat.toUInt64,
    UInt64.toNat_ofNat_of_lt' (show xs.length < UInt64.size by simp [UInt64.size]; omega)]
  exact NativeRustcVm.ewsOf_of_ewsAt he

/-- A byte at offset `x` of `a` is not in the range from offset `o` when `x` is outside it. -/
theorem not_inRange_off {a : BitVec 64} {x o n : Nat} (hx : x < 2 ^ 63) (ho : o + n ≤ 2 ^ 63)
    (h : x < o ∨ o + n ≤ x) : ¬InRange (a + BitVec.ofNat 64 o) n (a + BitVec.ofNat 64 x) := by
  unfold InRange
  rw [show a + BitVec.ofNat 64 x - (a + BitVec.ofNat 64 o) =
    BitVec.ofNat 64 x - BitVec.ofNat 64 o by bv_omega, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  omega

/-- **A block writing into written regions and the frame's locals** keeps a body. -/
theorem Frame.write_local [Labels] {env : Env} {S₀ S₁ : SState} {rs : List XReg} {lo : Nat}
    (hb : Frame m0 F N slots ws st)
    (hS : StackOk m0 N) (hF : F ≤ N) (hslots : ∀ p ∈ slots, lo ≤ p.1 ∧ p.1 + 8 ≤ F)
    (hlo : lo ≤ F) (hws : WsOff m0 N ws)
    (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF) (hd : st.dmem = env.mem0)
    (hrs : ∀ r, calleeSaved r = true → r ∉ slots.map (·.2) → r ∈ rs)
    (hk : keepsRegs S₀ S₁ rs = true)
    (hin : ∀ p, Written env S₁ p →
      InAny ws p ∨ InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 F) lo p) :
    Frame m0 F N slots ws st' := by
  simp only [keepsRegs, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hk
  obtain ⟨hr, hsp⟩ := hk
  have hso : NativeRustcArm.SameOutside st.dmem st'.dmem (Written env S₁) := by
    rw [hd]; exact hm.sameOutside hwf
  have hN : N ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  have := m0.regs.SP.toBitVec.isLt
  refine ⟨?_, fun p hp i hi ↦ ?_, fun r hr' hn ↦ ?_, fun p hp ↦ ?_, ?_⟩
  · rw [Match.sp_eq hm₀ hm hsp]; exact hb.sp
  · simp only [List.length_map, List.length_range] at hi
    have hpo := hslots p hp
    rw [hso _ fun hw ↦ ?_]
    · exact hb.frame p hp i (by simpa using hi)
    · rcases hin _ hw with h | h
      · rw [addr_add] at h
        exact slot_not hS hF hws (by omega) h
      · rw [addr_add] at h
        exact slot_not_local (lo := lo) (o := p.1 + i) (by omega) (by omega) h
  · obtain ⟨hs, he⟩ := hr r (hrs r hr' hn)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    rw [Match.reg_eq hm₀ hm hv (he.trans hv)]
    exact hb.regs r hr' hn
  · rw [hso p fun hw ↦ hp ?_]
    · exact hb.same p hp
    · rcases hin p hw with ⟨w, hw', hpw⟩ | h
      · exact ⟨w, List.mem_cons_of_mem _ hw', hpw⟩
      · exact ⟨stackRegion m0 N, List.mem_cons_self, local_inStack hS hF hlo h⟩
  · exact fun p h ↦ hm.kept hwf p (by rw [← hd]; exact hb.kept p h)

/-- **A call that may change the frame's locals** keeps a body: the callee changes memory only in
its stack, `n` bytes below the body's SP, in written regions and in the locals (`R`), and keeps the
callee-saved registers and SP. -/
theorem Frame.call_local {lo : Nat} (hb : Frame m0 F N slots ws st) (hS : StackOk m0 N)
    (hle : F + n ≤ N) (hslots : ∀ p ∈ slots, lo ≤ p.1 ∧ p.1 + 8 ≤ F) (hlo : lo ≤ F)
    (hws : WsOff m0 N ws) {R : BitVec 64 → Prop}
    (hsame : SameOutside st.dmem st'.dmem R)
    (hR : ∀ p, R p → InRange (stackBelow st n) n p ∨ InAny ws p ∨
      InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 F) lo p) (hsaved : Saved st st') :
    Frame m0 F N slots ws st' := by
  have hN : N ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  have := m0.regs.SP.toBitVec.isLt
  refine ⟨hsaved.2.1 ▸ hb.sp, fun p hp i hi ↦ ?_, fun r hr hn ↦ (hsaved.1 r hr).trans
    (hb.regs r hr hn), fun p hp ↦ ?_, fun p hp ↦ hsaved.2.2 p (hb.kept p hp)⟩
  · simp only [List.length_map, List.length_range] at hi
    have hpo := hslots p hp
    rw [hsame _ ?_]
    · exact hb.frame p hp i (by simpa using hi)
    · intro hRp
      rcases hR _ hRp with h | h | h
      · unfold stackBelow at h
        rw [hb.sp, addr_add] at h
        exact not_inRange_below (by omega) h
      · rw [addr_add] at h
        exact slot_not hS (by omega) hws (by omega) h
      · rw [addr_add] at h
        exact slot_not_local (lo := lo) (o := p.1 + i) (by omega) (by omega) h
  · rw [hsame p fun h ↦ ?_]
    · exact hb.same p hp
    · rcases hR p h with h | h | h
      · exact hp ⟨stackRegion m0 N, List.mem_cons_self, hb.stack_in hS hle h⟩
      · obtain ⟨w, hw, hpw⟩ := h
        exact hp ⟨w, List.mem_cons_of_mem _ hw, hpw⟩
      · exact hp ⟨stackRegion m0 N, List.mem_cons_self, local_inStack hS (by omega) hlo h⟩

/-! ## Prologue and epilogue -/

/-- **The entry block**: from the entry, the prologue's writes in the frame (region 0) and the
other callee-saved registers untouched make a body. -/
theorem Frame.of_entry [Labels] {S' : SState} (hS : StackOk m0 N) (hF : F ≤ N)
    (hm : Match (Env.ofMachine m0 [(m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F)]) S' st)
    (hsp : S'.sp = .ptr 0 0)
    (hw : ∀ p ∈ slots, p.1 + 8 ≤ F ∧ ∀ i < 8, findWrite 0 (p.1 + i) S'.mem = some (.reg p.2, i))
    (hregs : ∀ r ∈ calleeRegs, r ∉ slots.map (·.2) → S'.reg r = some (.reg r))
    (hmem : ∀ w ∈ S'.mem, w.r = 0 ∧ w.off + w.n ≤ F) : Frame m0 F N slots ws st := by
  obtain ⟨hmap, hnw, he⟩ := frame_ok hS hF
  have hwf := wf_one hmap hnw
  have hSle : N ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  refine ⟨?_, slotsAt_of_writes hm hw, fun r hr hn ↦ ?_, fun p hp ↦ ?_, hm.kept hwf⟩
  · rw [hm.sp, hsp]; simp [Sym.eval]
  · apply UInt64.toBitVec_inj.mp
    rw [hm.regs r _ (hregs r (mem_calleeRegs hr) hn)]
    rfl
  · refine hm.get?_mem0 hwf fun ⟨w, hw', b, sz, hb, h1, h2⟩ ↦ hp ⟨stackRegion m0 N, List.mem_cons_self, ?_⟩
    obtain ⟨hr, hoff⟩ := hmem w hw'
    rw [hr] at hb
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    show NativeRustcVm.InRange (stackBelow m0 N) N p
    rw [NativeRustcVm.inRange_iff (stack_noWrap hS), show (stackBelow m0 N).toNat = m0.regs.SP.toBitVec.toNat - N
      from toNat_sub_ofNat hSle]
    have := m0.regs.SP.toBitVec.isLt
    rw [he] at h1 h2
    omega

/-- **The epilogue**: run from a body with the frame as region 0, it restores the entry's
callee-saved registers, X30 and SP. -/
theorem Frame.saved [Labels] {S₁ : SState} (hb : Frame m0 F N slots ws st)
    (hm : Match (Env.ofMachine st [(m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F)]) S₁ st')
    (hwf : (Env.ofMachine st [(m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F)]).WF)
    (hx30 : (XReg.X30) ∈ slots.map (·.2))
    (hr : restores slots F S₁ = true) (hmem : S₁.mem = []) :
    Saved m0 st' ∧ st'.regs.X30 = m0.regs.X30 ∧ st'.dmem = st.dmem := by
  simp only [restores, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hr
  obtain ⟨hr, hsp⟩ := hr
  have hbase : (Env.ofMachine st [(m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F)]).base 0 =
      m0.regs.SP.toBitVec - BitVec.ofNat 64 F := rfl
  have hreg : ∀ r ∈ savedRegs, st'.regs.getXReg r = m0.regs.getXReg r := by
    intro r hrs
    have h := hm.regs r _ (hr r hrs)
    cases hf : slots.find? (·.2 == r) with
    | some p =>
      obtain ⟨hp, rfl⟩ := find?_mem hf
      rw [hf] at h
      apply UInt64.toBitVec_inj.mp
      rw [h]
      exact slot_load (r := 0) (by rw [hbase]; exact hb.frame) hp
    | none =>
      rw [hf] at h
      apply UInt64.toBitVec_inj.mp
      rw [h]
      show (st.regs.getXReg r).toBitVec = _
      by_cases hc : calleeSaved r = true
      · rw [hb.regs r hc (find?_none hf)]
      · have : r = .X30 := by
          cases r <;> simp_all [calleeSaved, savedRegs]
        subst this
        exact absurd hx30 (find?_none hf)
  have hdm : st'.dmem = st.dmem := hm.dmem_eq hwf hmem
  refine ⟨⟨fun r hc ↦ hreg r (mem_savedRegs hc), ?_, ?_⟩, hreg .X30 (by simp [savedRegs]), hdm⟩
  · apply UInt64.toBitVec_inj.mp
    rw [hm.sp, hsp]
    simp only [Sym.eval, hbase]
    rw [show BitVec.ofInt 64 (F : Int) = BitVec.ofNat 64 F from rfl, BitVec.sub_add_cancel]
  · rw [hdm]; exact hb.kept

/-! ## Regions -/

/-- A sub-range of a region that is data memory and does not wrap. -/
theorem sub_ok {d : DataMem} {a : BitVec 64} {N o n : Nat} (h : Region.Ok d ⟨a, N⟩)
    (hle : o + n ≤ N) : Mapped d (a + BitVec.ofNat 64 o) n ∧ NoWrap (a + BitVec.ofNat 64 o) n :=
  ⟨NativeRustcVm.Mapped.sub h.1 hle, NativeRustcVm.NoWrap.sub h.2 hle⟩

/-- Sub-ranges of apart ranges are apart. -/
theorem Apart.sub {a b : BitVec 64} {N M o n o' n' : Nat} (h : Apart a N b M) (ha : NoWrap a N)
    (hb : NoWrap b M) (h1 : o + n ≤ N) (h2 : o' + n' ≤ M) (hn : 0 < n) (hn' : 0 < n') :
    Apart (a + BitVec.ofNat 64 o) n (b + BitVec.ofNat 64 o') n' := by
  unfold NoWrap at ha hb
  unfold Apart at h ⊢
  rw [NativeRustcVm.toNat_add_ofNat (by omega), NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

/-- Two sub-ranges of one range, the first before the second. -/
theorem apart_in {a : BitVec 64} {N o n o' n' : Nat} (hN : NoWrap a N) (h : o + n ≤ o')
    (h' : o' + n' ≤ N) : Apart (a + BitVec.ofNat 64 o) n (a + BitVec.ofNat 64 o') n' :=
  NativeRustcVm.apart_of_le hN (by omega) h' (Or.inl h)

/-- **Bytes of a read region** a body did not change. -/
theorem Frame.bytesAt {rs : List Region} (hb : Frame m0 F N slots ws st) (hA : Areas m0 N ws rs)
    (hS : StackOk m0 N) {r : Region} (hr : r ∈ rs) {o : Nat} {bs : List UInt8}
    (hin : o + bs.length ≤ r.size) (h : NativeRustcVm.BytesAt m0.dmem (r.addr + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt st.dmem (r.addr + BitVec.ofNat 64 o) bs := by
  have hrok := Areas.ok hA (Or.inr hr)
  refine NativeRustcVm.BytesAt.of_sameOutside h hb.same fun i hi hany ↦ ?_
  rw [NativeRustcVm.addr_add_add] at hany
  refine NativeRustcVm.not_inAny_of_apart (rs := stackRegion m0 N :: ws) (a := r.addr) (n := r.size)
    (fun w hw ↦ ⟨(hA.2.2 w hw r hr).symm, ?_⟩) hrok.2
    (NativeRustcVm.inRange_add (by omega) (by have := hrok.2; unfold NativeRustcVm.NoWrap at this; omega)) hany
  rcases List.mem_cons.mp hw with rfl | hw
  · exact noWrap_stackBelow hS
  · exact (Areas.ok hA (Or.inl hw)).2

/-! ## Elements -/

/-- **An element at a region's offset** is what the environment loads there, word by word. -/
theorem load_ew {env : Env} {r o : Nat} {x : EW}
    (h : NativeRustcVm.EWAt env.mem0 (env.base r + BitVec.ofNat 64 o) x) :
    env.load r o 8 = x.c0.toBitVec ∧ env.load r (o + 8) 8 = x.c1.toBitVec := by
  rw [NativeRustcVm.ewAt_iff, NativeRustcVm.addr_add_add] at h
  exact ⟨load_word h.1, load_word h.2⟩

/-- **An element a block wrote**: `v0` at `o`, `v1` at `o + 8`. -/
theorem Match.ewAt_write [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz))
    (hle : o + 16 ≤ sz) {v0 v1 : Sym}
    (hw0 : ∀ i < 8, findWrite r (o + i) S.mem = some (v0, i))
    (hw1 : ∀ i < 8, findWrite r (o + 8 + i) S.mem = some (v1, i)) :
    NativeRustcVm.EWAt m.dmem (b + BitVec.ofNat 64 o)
      ⟨UInt64.ofBitVec (v0.eval env), UInt64.ofBitVec (v1.eval env)⟩ := by
  rw [NativeRustcVm.ewAt_iff, NativeRustcVm.addr_add_add]
  exact ⟨Sumcheck.Match.wordAt_write hm hb (by omega) hw0,
    Sumcheck.Match.wordAt_write hm hb (by omega) hw1⟩

theorem findWrite_skip {r i : Nat} {w : Write} {ws : List Write}
    (h : ¬(w.r = r ∧ w.off ≤ i ∧ i < w.off + w.n)) : findWrite r i (w :: ws) = findWrite r i ws := by
  rw [findWrite_cons, ite_neg h]


/-- **An element a block wrote**, its two words newest-first after writes `pre` elsewhere. -/
theorem Match.ewAt_write2 [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {pre ws : List Write} {r o o' : Nat} {v0 v1 : Sym}
    (hS : S.mem = pre ++ ⟨r, o', 8, v1⟩ :: ⟨r, o, 8, v0⟩ :: ws) (ho : o' = o + 8)
    (hpre : ∀ w ∈ pre, w.r ≠ r ∨ w.off + w.n ≤ o ∨ o + 16 ≤ w.off)
    {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz)) (hle : o + 16 ≤ sz) :
    NativeRustcVm.EWAt m.dmem (b + BitVec.ofNat 64 o)
      ⟨UInt64.ofBitVec (v0.eval env), UInt64.ofBitVec (v1.eval env)⟩ := by
  subst ho
  have hskip : ∀ i < 16, findWrite r (o + i) S.mem =
      findWrite r (o + i) (⟨r, o + 8, 8, v1⟩ :: ⟨r, o, 8, v0⟩ :: ws) := by
    intro i hi
    rw [hS]
    clear hS
    induction pre with
    | nil => rfl
    | cons w pre ih =>
      rw [List.cons_append, findWrite_skip ?_, ih fun w hw ↦ hpre w (List.mem_cons_of_mem _ hw)]
      rcases hpre w List.mem_cons_self with h | h | h <;> omega
  refine KeccakGkr.Match.ewAt_write hm hb hle (fun i hi ↦ ?_) (fun i hi ↦ ?_)
  · rw [hskip i (by omega), findWrite_skip (by simp; omega)]
    exact findWrite_head hi
  · rw [show o + 8 + i = o + (8 + i) by omega, hskip _ (by omega), show o + (8 + i) = o + 8 + i by omega]
    exact findWrite_head hi

/-- **Registers a block kept**: those whose symbolic value is unchanged. -/
theorem Match.regs_keep [Labels] {env : Env} {S S' : SState} {m m' : MachineData}
    (hm : Match env S m) (hm' : Match env S' m') (rs : List XReg)
    (h : rs.all (fun r ↦ (S.reg r).isSome && S'.reg r == S.reg r) = true) :
    ∀ r ∈ rs, m'.regs.getXReg r = m.regs.getXReg r := by
  intro r hr
  have := List.all_eq_true.mp h r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp this.1
  exact Match.reg_eq hm hm' hv (this.2.trans hv)

/-- Mapped bytes kept. -/
theorem Mapped.kept' {d d' : DataMem} {a : BitVec 64} {n : Nat} (h : Mapped d a n) (hk : Kept d d') :
    Mapped d' a n := fun i hi ↦ hk _ (h i hi)

/-- `n` elements `f i` from `a`, sixteen bytes each. -/
@[expose] def ElemsAt (d : DataMem) (a : BitVec 64) (f : Nat → EW) (n : Nat) : Prop :=
  ∀ i < n, NativeRustcVm.EWAt d (a + BitVec.ofNat 64 (16 * i)) (f i)

/-- **Elements grown**: `k` more written after `n`, nothing else of the range changed. -/
theorem ElemsAt.grow {d d' : DataMem} {a : BitVec 64} {f : Nat → EW} {n k : Nat}
    (h : ElemsAt d a f n) (hnw : NoWrap a (16 * (n + k)))
    (hs : SameOutside d d' (InRange (a + BitVec.ofNat 64 (16 * n)) (16 * k)))
    (hnew : ∀ j < k, NativeRustcVm.EWAt d' (a + BitVec.ofNat 64 (16 * (n + j))) (f (n + j))) :
    ElemsAt d' a f (n + k) := by
  intro i hi
  by_cases hin : i < n
  · refine NativeRustcVm.BytesAt.of_sameOutside_apart (h i hin) hs ?_ ?_ ?_
    · rw [NativeRustcVm.length_ewBytes]
      exact apart_in hnw (by omega) (by omega)
    · rw [NativeRustcVm.length_ewBytes]; exact NativeRustcVm.NoWrap.sub hnw (by omega)
    · exact NativeRustcVm.NoWrap.sub hnw (by omega)
  · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
    exact hnew j (by omega)

/-- **Elements kept** where memory changed only apart from them. -/
theorem ElemsAt.keep {d d' : DataMem} {a : BitVec 64} {f : Nat → EW} {n : Nat} {R : BitVec 64 → Prop}
    (h : ElemsAt d a f n) (hs : SameOutside d d' R)
    (hR : ∀ p, InRange a (16 * n) p → ¬R p) (hnw : NoWrap a (16 * n)) : ElemsAt d' a f n :=
  fun i hi ↦ NativeRustcVm.BytesAt.of_sameOutside (h i hi) hs fun j hj ↦ by
    rw [NativeRustcVm.length_ewBytes] at hj
    rw [NativeRustcVm.addr_add_add]
    exact hR _ (NativeRustcVm.inRange_add (by omega) (by unfold NoWrap at hnw; omega))

/-- Element `i` of an array whose elements are at `a`. -/
theorem ewsAt_getD {d : DataMem} {a : BitVec 64} {xs : Array EW}
    (h : NativeRustcVm.EWsAt d a xs.toList) {i : Nat} (hi : i < xs.size) :
    NativeRustcVm.EWAt d (a + BitVec.ofNat 64 (16 * i)) (xs.getD i 0) := by
  have hi' : i < xs.toList.length := by simpa using hi
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, List.getElem?_eq_getElem hi',
    Option.getD_some]
  exact NativeRustcVm.EWsAt.getElem h hi'

/-- The elements as a list. -/
theorem ElemsAt.ewsAt {d : DataMem} {a : BitVec 64} {xs : List EW}
    (h : ElemsAt d a (fun i ↦ xs.getD i 0) xs.length) : NativeRustcVm.EWsAt d a xs := by
  rw [NativeRustcVm.ewsAt_iff]
  intro i hi
  have := h i hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
  exact this

end

end NativeRustcVmArm.KeccakGkr
