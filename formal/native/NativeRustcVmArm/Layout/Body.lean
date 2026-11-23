module

public import NativeRustcVmArm.Layout.Common
public import NativeRustcVmArm.Arrays.Common

/-!
# Function bodies with a frame: what the layout's proofs add to `Arrays.Body`

- A body for no outputs is one for any (`Body.widen`).
- The epilogue run with the frame (region 0) and other regions, writing into those: it restores
  the entry's callee-saved registers, X30 and SP (`Body.saved_of`).
- A prefix of a readable area is mapped in a state that kept it (`readable_prefix`); an area off
  the stack is apart from the frame (`apart_frame`).
-/

namespace NativeRustcVmArm.Layout

open NativeRustcArm NativeRustcArm.Sym
open NativeRustcVmArm.Arrays (Body savedRegs restores slot_load find?_mem find?_none
  mem_savedRegs frame_ok inRange_stack stack_noWrap toNat_sub_ofNat keepsAll calleeRegs inSlots
  mem_calleeRegs inSlots_false not_inRange_of_apart load8_eq)

public section

/-- **A body for no outputs** is one for any. -/
theorem Body.widen {m0 st : MachineData} {F S : Nat} {slots : List (Nat × XReg)} {oa : BitVec 64}
    {on : Nat} (hb : Body m0 F S slots 0 0 st) : Body m0 F S slots oa on st :=
  ⟨hb.sp, hb.frame, hb.regs, fun p hp ↦ hb.same p fun h ↦ hp (h.elim
    (fun h ↦ absurd h (by unfold InRange; omega)) Or.inr), hb.kept⟩

/-- **The epilogue** with the frame as region 0 and other regions (which it may write): it
restores the entry's callee-saved registers, X30 and SP. -/
theorem Body.saved_of [Labels] {m0 st st' : MachineData} {F S : Nat} {slots : List (Nat × XReg)}
    {oa : BitVec 64} {on : Nat} {rs : List (BitVec 64 × Nat)} {S₁ : SState}
    (hb : Body m0 F S slots oa on st)
    (hm : Match (Env.ofMachine st ((m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F) :: rs)) S₁ st')
    (hwf : (Env.ofMachine st ((m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F) :: rs)).WF)
    (hx30 : XReg.X30 ∈ slots.map (·.2)) (hr : restores slots F S₁ = true) :
    Saved m0 st' ∧ st'.regs.X30 = m0.regs.X30 := by
  simp only [restores, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hr
  obtain ⟨hr, hsp⟩ := hr
  have hbase : (Env.ofMachine st ((m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F) :: rs)).base 0 =
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
  refine ⟨⟨fun r hc ↦ hreg r (mem_savedRegs hc), ?_, fun p hp ↦ hm.kept hwf p (hb.kept p hp)⟩,
    hreg .X30 (by simp [savedRegs])⟩
  apply UInt64.toBitVec_inj.mp
  rw [hm.sp, hsp]
  simp only [Sym.eval, hbase]
  rw [show BitVec.ofInt 64 (F : Int) = BitVec.ofNat 64 F from rfl, BitVec.sub_add_cancel]

/-- **An area off the stack is kept by a callee** whose stack (`n'` bytes below SP) lies below a
body's frame. -/
theorem Body.keep_call {m0 st st' : MachineData} {F S : Nat} {slots : List (Nat × XReg)}
    {oa : BitVec 64} {on : Nat} (hb : Body m0 F S slots oa on st) (hS : StackOk m0 S) {n' : Nat}
    (hle : F + n' ≤ S) {a : BitVec 64} {n : Nat} (hoff : OffStack m0 a n S) (hnw : NoWrap a n)
    (hpost : SameOutside st.dmem st'.dmem (InRange (stackBelow st n') n')) :
    ∀ p, InRange a n p → st'.dmem.get? p = st.dmem.get? p := fun p hp' ↦ hpost p fun h ↦ by
  unfold stackBelow at h
  rw [hb.sp] at h
  have h' := inRange_stack (n := n') (F := F) (S := S) hle hS.2.1 h
  have hsnw : NoWrap (m0.regs.SP.toBitVec - BitVec.ofNat 64 S) S := stack_noWrap hS
  have hSle : S ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  rw [inRange_iff hnw] at hp'
  rw [inRange_iff hsnw, toNat_sub_ofNat hSle] at h'
  unfold OffStack Apart stackBelow at hoff
  rw [toNat_sub_ofNat hSle] at hoff
  omega

/-- **Memory after a block writing only into region `r`** is the start's outside it. -/
theorem same_of_region [Labels] {st m : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine st rs) S m) (hwf : (Env.ofMachine st rs).WF) {r : Nat}
    {b : BitVec 64} {sz : Nat} (hb : rs[r]? = some (b, sz))
    (hw : ∀ w ∈ S.mem, w.r = r ∧ w.off + w.n ≤ sz) :
    ∀ p, ¬InRange b sz p → m.dmem.get? p = st.dmem.get? p := fun p hp ↦
  hm.get?_mem0 hwf fun ⟨w, hw', b', sz', hb', h1, h2⟩ ↦ hp (by
    obtain ⟨hr0, hoff⟩ := hw w hw'
    rw [hr0] at hb'
    simp only [Env.ofMachine_regions] at hb'
    rw [hb] at hb'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb')
    rw [inRange_iff (hwf.noWrap r b sz (by simpa using hb))]
    omega)

/-- A register a block set to region `0`'s base. -/
theorem ptr0_of [Labels] {st m : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    {b : BitVec 64} {n : Nat} (hm : Match (Env.ofMachine st ((b, n) :: rs)) S m) {r : XReg}
    (h : S.reg r = some (.ptr 0 0)) : (m.regs.getXReg r).toBitVec = b := by
  rw [hm.regs r _ h]
  show b + BitVec.ofInt 64 0 = b
  rw [ofInt_zero, BitVec.add_zero]

/-- **A block writing only into region 0** (of several), inside the outputs, keeps a body. -/
theorem Body.of_write' [Labels] {m0 st st' : MachineData} {F S : Nat} {slots : List (Nat × XReg)}
    {oa : BitVec 64} {on : Nat} {a : BitVec 64} {n : Nat} {rs : List (BitVec 64 × Nat)}
    {S₀ S₁ : SState} (hb : Body m0 F S slots oa on st) (hS : StackOk m0 S)
    (hm₀ : Match (Env.ofMachine st ((a, n) :: rs)) S₀ st)
    (hm : Match (Env.ofMachine st ((a, n) :: rs)) S₁ st')
    (hwf : (Env.ofMachine st ((a, n) :: rs)).WF) (hin : ∀ p, InRange a n p → InRange oa on p)
    (hk : keepsAll S₀ { S₁ with mem := [] } (calleeRegs.filter fun r ↦ !inSlots slots r) = true)
    (hw : ∀ w ∈ S₁.mem, w.r = 0 ∧ w.off + w.n ≤ n) (hfr : Apart a n (stackBelow m0 S) S)
    (hslots : ∀ p ∈ slots, p.1 + 8 ≤ F) (hF : F ≤ S) :
    Body m0 F S slots oa on st' := by
  simp only [keepsAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.isEmpty_iff] at hk
  obtain ⟨⟨hr, hsp⟩, -⟩ := hk
  have hnw : NoWrap a n := hwf.noWrap 0 a n rfl
  have hsame : ∀ p, ¬InRange a n p → st'.dmem.get? p = st.dmem.get? p :=
    same_of_region hm hwf (r := 0) rfl hw
  refine ⟨?_, fun p hp i hi ↦ ?_, fun r hr' hn ↦ ?_, fun p hp ↦ ?_,
    fun p hp ↦ hm.kept hwf _ (hb.kept p hp)⟩
  · rw [Match.sp_eq hm₀ hm hsp]; exact hb.sp
  · rw [hsame _ ?_]
    · exact hb.frame p hp i hi
    · simp only [List.length_map, List.length_range] at hi
      have hSle : S ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
      have := hslots p hp
      have e : m0.regs.SP.toBitVec - BitVec.ofNat 64 F + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i =
          stackBelow m0 S + BitVec.ofNat 64 (S - F + p.1 + i) := by
        unfold stackBelow
        bv_omega
      rw [e]
      exact not_inRange_of_apart (Or.symm hfr) (stack_noWrap hS) hnw (by omega)
  · obtain ⟨hs, he⟩ := hr r (List.mem_filter.mpr ⟨mem_calleeRegs hr', by
      rw [inSlots_false hn]; rfl⟩)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    rw [Match.reg_eq hm₀ hm hv (he.trans hv)]
    exact hb.regs r hr' hn
  · rw [hsame p fun h ↦ hp (Or.inl (hin p h))]
    exact hb.same p hp

/-- **A call that changes only bytes of the outputs off the frame** (`R`) and keeps the
callee-saved registers, SP and mapped bytes keeps a body. -/
theorem Body.of_call {m0 st st' : MachineData} {F S : Nat} {slots : List (Nat × XReg)}
    {oa : BitVec 64} {on : Nat} (hb : Body m0 F S slots oa on st) {R : BitVec 64 → Prop}
    (hsame : SameOutside st.dmem st'.dmem R)
    (hR : ∀ p, R p → InRange oa on p ∧ ¬InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 F) F p)
    (hsaved : Saved st st') (hslots : ∀ p ∈ slots, p.1 + 8 ≤ F) (hF : F ≤ m0.regs.SP.toNat) :
    Body m0 F S slots oa on st' := by
  refine ⟨hsaved.2.1 ▸ hb.sp, fun p hp i hi ↦ ?_, fun r hr hn ↦ (hsaved.1 r hr).trans
    (hb.regs r hr hn), fun p hp ↦ ?_, fun p hp ↦ hsaved.2.2 p (hb.kept p hp)⟩
  · rw [hsame _ fun h ↦ (hR _ h).2 ?_]
    · exact hb.frame p hp i hi
    · simp only [List.length_map, List.length_range] at hi
      have := hslots p hp
      have hsp := m0.regs.SP.toNat_lt
      have hF' : F ≤ m0.regs.SP.toBitVec.toNat := hF
      unfold InRange
      rw [show m0.regs.SP.toBitVec - BitVec.ofNat 64 F + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i -
          (m0.regs.SP.toBitVec - BitVec.ofNat 64 F) = BitVec.ofNat 64 (p.1 + i) by
        rw [BitVec.add_assoc, BitVec.ofNat_add]; bv_omega, BitVec.toNat_ofNat]
      omega
  · rw [hsame p fun h ↦ hp (Or.inl (hR p h).1)]
    exact hb.same p hp

/-- **An element copied** by a block: the two words it loaded from region 1 at `os`, stored in
region 0 at `od`. -/
theorem copy_ew [Labels] {st m : MachineData} {dst src : BitVec 64} {nd ns : Nat}
    {rs : List (BitVec 64 × Nat)} {S : SState} {od os : Nat}
    (hm : Match (Env.ofMachine st ((dst, nd) :: (src, ns) :: rs)) S m) (hle : od + 16 ≤ nd)
    (h0 : ∀ i < 8, findWrite 0 (od + i) S.mem = some (.load 1 os 8, i))
    (h1 : ∀ i < 8, findWrite 0 (od + 8 + i) S.mem = some (.load 1 (os + 8) 8, i)) :
    NativeRustcVm.EWAt m.dmem (dst + BitVec.ofNat 64 od)
      (NativeRustcVm.ewOf st.dmem (src + BitVec.ofNat 64 os)) := by
  rw [NativeRustcVm.ewAt_iff]
  have w0 := Match.wordAt_write hm (r := 0) (b := dst) (sz := nd) rfl (by omega) h0
  have w1 := Match.wordAt_write hm (r := 0) (b := dst) (sz := nd) rfl (by omega) h1
  simp only [Sym.eval, load8_eq, UInt64.ofBitVec_toBitVec, Env.ofMachine_mem0] at w0 w1
  refine ⟨w0, ?_⟩
  show NativeRustcVm.WordAt m.dmem (dst + BitVec.ofNat 64 od + BitVec.ofNat 64 8)
    (NativeRustcVm.wordOf st.dmem (src + BitVec.ofNat 64 os + BitVec.ofNat 64 8))
  rw [NativeRustcVm.addr_add, NativeRustcVm.addr_add]
  exact w1

theorem ult_iff {x : BitVec 64} {n : Nat} (hn : n < 2 ^ 64) :
    x.ult (BitVec.ofNat 64 n) = true ↔ x.toNat < n := by
  simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem beq_iff {x : BitVec 64} {n : Nat} (hn : n < 2 ^ 64) :
    (x == BitVec.ofNat 64 n) = true ↔ x.toNat = n := by
  rw [beq_iff_eq]
  constructor
  · intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  · intro h; apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem not_beq_iff {x : BitVec 64} {n : Nat} (hn : n < 2 ^ 64) :
    (!(x == BitVec.ofNat 64 n)) = true ↔ x.toNat ≠ n := by
  constructor
  · intro h he
    rw [(beq_iff hn).mpr he] at h
    exact absurd h (by decide)
  · intro h
    cases hb : (x == BitVec.ofNat 64 n) with
    | false => rfl
    | true => exact absurd ((beq_iff hn).mp hb) h

/-- Part of an area off the stack is off it. -/
theorem offStack_sub {m0 : MachineData} {a : BitVec 64} {n o j S : Nat} (h : OffStack m0 a n S)
    (hnw : NoWrap a n) (hj : o + j ≤ n) (h0 : 0 < j) : OffStack m0 (a + BitVec.ofNat 64 o) j S := by
  unfold NoWrap at hnw
  unfold OffStack Apart at *
  rw [Arrays.toNat_add_ofNat' (by omega)]
  omega

/-- The `t`th number read. -/
theorem natsOf_getD (m : MachineData) (a : UInt64) {n t : Nat} (ht : t < n) :
    (natsOf m a n).getD t 0 =
      (NativeRustcVm.wordOf m.dmem (a.toBitVec + BitVec.ofNat 64 (8 * t))).toNat := by
  simp [natsOf, NativeRustcVm.wordsOf, Array.getD, ht]

/-- A branch on `x < y` (unsigned). -/
theorem pc_ult {pc a b : Int64} {x y : BitVec 64} {inst : Decidable (x.ult y = true)}
    (h : pc = @ite _ (x.ult y = true) inst a b) :
    (x.toNat < y.toNat → pc = a) ∧ (¬x.toNat < y.toNat → pc = b) := by
  obtain ⟨h1, h2⟩ := Arrays.pc_cond h
  exact ⟨fun hl ↦ h1 (by simp [BitVec.ult, hl]), fun hl ↦ h2 (by simp [BitVec.ult, hl])⟩

/-- A branch on `x ≥ y` (unsigned). -/
theorem pc_nult {pc a b : Int64} {x y : BitVec 64} {inst : Decidable ((!x.ult y) = true)}
    (h : pc = @ite _ ((!x.ult y) = true) inst a b) :
    (¬x.toNat < y.toNat → pc = a) ∧ (x.toNat < y.toNat → pc = b) := by
  obtain ⟨h1, h2⟩ := Arrays.pc_cond h
  exact ⟨fun hl ↦ h1 (by simp [BitVec.ult, hl]), fun hl ↦ h2 (by simp [BitVec.ult, hl])⟩

/-- A branch on `x = y`. -/
theorem pc_eq {pc a b : Int64} {x y : BitVec 64} {inst : Decidable ((x == y) = true)}
    (h : pc = @ite _ ((x == y) = true) inst a b) :
    (x.toNat = y.toNat → pc = a) ∧ (x.toNat ≠ y.toNat → pc = b) := by
  obtain ⟨h1, h2⟩ := Arrays.pc_cond h
  refine ⟨fun hl ↦ h1 (by rw [BitVec.eq_of_toNat_eq hl]; simp), fun hl ↦ h2 fun he ↦ hl ?_⟩
  rw [beq_iff_eq.mp he]

/-- A branch on `x ≠ y`. -/
theorem pc_ne' {pc a b : Int64} {x y : BitVec 64} {inst : Decidable ((!(x == y)) = true)}
    (h : pc = @ite _ ((!(x == y)) = true) inst a b) :
    (x.toNat ≠ y.toNat → pc = a) ∧ (x.toNat = y.toNat → pc = b) := by
  obtain ⟨h1, h2⟩ := Arrays.pc_cond h
  refine ⟨fun hl ↦ h1 ?_, fun hl ↦ h2 (by rw [BitVec.eq_of_toNat_eq hl]; simp)⟩
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne]
  exact fun he ↦ hl (by rw [he])

/-- **A prefix of a readable area** is mapped in a state that kept it. -/
theorem readable_prefix {m0 st : MachineData} {a : BitVec 64} {n j : Nat} (h : Readable m0 a n)
    (hk : Kept m0.dmem st.dmem) (hj : j ≤ n) : Mapped st.dmem a j ∧ NoWrap a j := by
  refine ⟨fun i hi ↦ hk _ (h.1 i (by omega)), ?_⟩
  have := h.2
  unfold NoWrap at this ⊢
  omega

/-- **Part of a readable area** is readable in a state that kept it. -/
theorem readable_sub {m0 st : MachineData} {a : BitVec 64} {n o j : Nat} (h : Readable m0 a n)
    (hk : Kept m0.dmem st.dmem) (hle : o + j ≤ n) : Readable st (a + BitVec.ofNat 64 o) j := by
  have hnw := h.2
  unfold NoWrap at hnw
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · rw [NativeRustcVm.addr_add]; exact hk _ (h.1 _ (by omega))
  · unfold NoWrap
    by_cases hj : j = 0
    · have := (a + BitVec.ofNat 64 o).isLt; omega
    · rw [Arrays.toNat_add_ofNat' (by omega)]; omega

/-- Parts of two areas apart are apart. -/
theorem apart_sub {a b : BitVec 64} {n n' o o' j j' : Nat} (h : Apart a n b n') (ha : NoWrap a n)
    (hb : NoWrap b n') (hj : o + j ≤ n) (hj' : o' + j' ≤ n') (h0 : 0 < j) (h0' : 0 < j') :
    Apart (a + BitVec.ofNat 64 o) j (b + BitVec.ofNat 64 o') j' := by
  unfold NoWrap at ha hb
  unfold Apart at *
  rw [Arrays.toNat_add_ofNat' (by omega), Arrays.toNat_add_ofNat' (by omega)]
  omega

/-- **The elements copied so far, and `c` more**: the first `i` elements at `o`, kept where a block
wrote elsewhere, and the next `c` written. -/
theorem copied_step {d d' : Mem 64} {o : BitVec 64} {xs : List NativeVm.Model.EW} {i c : Nat}
    (hnw : NoWrap o (16 * xs.length)) (hc : NativeRustcVm.EWsAt d o (xs.take i))
    (hsame : ∀ p, ¬InRange (o + BitVec.ofNat 64 (16 * i)) (16 * c) p → d'.get? p = d.get? p)
    (hnew : NativeRustcVm.EWsAt d' (o + BitVec.ofNat 64 (16 * i)) ((xs.drop i).take c))
    (hic : i + c ≤ xs.length) (hc0 : 0 < c) : NativeRustcVm.EWsAt d' o (xs.take (i + c)) := by
  rw [List.take_add, NativeRustcVm.ewsAt_append, List.length_take, Nat.min_eq_left (by omega)]
  refine ⟨Arrays.bytesAt_congr hc fun j hj ↦ hsame _ fun h ↦ ?_, hnew⟩
  rw [Arrays.length_flatMap_ewBytes, List.length_take, Nat.min_eq_left (by omega)] at hj
  unfold NoWrap at hnw
  rw [inRange_iff (by rw [Arrays.toNat_add_ofNat' (by omega)]; omega),
    Arrays.toNat_add_ofNat' (by omega), Arrays.toNat_add_ofNat' (by omega)] at h
  omega

theorem drop_take_one {α : Type} {xs : List α} {i : Nat} (h : i < xs.length) :
    (xs.drop i).take 1 = [xs[i]] := by
  rw [List.drop_eq_getElem_cons h]; rfl

theorem drop_take_two {α : Type} {xs : List α} {i : Nat} (h : i + 1 < xs.length) :
    (xs.drop i).take 2 = [xs[i], xs[i + 1]] := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons h]; rfl

/-- **An area off the stack** is apart from the frame. -/
theorem apart_frame {m0 : MachineData} {S F n : Nat} {a : BitVec 64} (hS : StackOk m0 S)
    (hF : F ≤ S) (h : OffStack m0 a n S) :
    Apart (m0.regs.SP.toBitVec - BitVec.ofNat 64 F) F a n := by
  have e := (frame_ok hS hF).2.2
  have e' := (frame_ok hS (Nat.le_refl S)).2.2
  have hSle : S ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  unfold OffStack Apart stackBelow at h
  unfold Apart
  rw [e]
  rw [e'] at h
  omega

end

end NativeRustcVmArm.Layout
