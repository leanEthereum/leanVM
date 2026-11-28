module

public import NativeRustcVmX64.Arrays.EqKernel.Exec
public import NativeRustcVm.Arrays.EqKernel
public import NativeRustcVmX64.Code.Vm.EqKernel.Names

/-!
# `eq_kernel` on x86-64: the state

`out`'s kernel `K i` of the first `i` coordinates, the frame's locals (`Loc`: the coordinate's
address, the size, `point`'s end, `|out|`), the body kept by stores into `out` (`B.of_out`), the
loops' invariants (`OInv` at a round's head, `IInv` at a pair's, `RInv` at a round's end), the
blocks' places.
-/

namespace NativeRustcVmX64.Arrays.EqKernel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.EqKernel NativeVm.Model
  NativeRustcVmX64.Field
open NativeRustcVm (ewsOf ewOf EWsAt EWAt WordAt half1)

public section

/-- `point`. -/
abbrev pt (m : MachineData) : BitVec 64 := reg m .rdi
/-- `|point|`. -/
abbrev np (m : MachineData) : Nat := (reg m .rsi).toNat
/-- `out`. -/
abbrev out (m : MachineData) : BitVec 64 := reg m .rdx
/-- `|out|`. -/
abbrev len (m : MachineData) : Nat := (reg m .rcx).toNat
/-- `point`'s coordinates. -/
abbrev pts (m : MachineData) : List EW := ewsOf m.dmem (pt m) (np m)
/-- The frame's base. -/
abbrev fb (m : MachineData) : BitVec 64 := stackBelow m 112
/-- The kernel of the first `i` coordinates. -/
abbrev K (m : MachineData) (i : Nat) : List EW := (eqKernel ((pts m).take i).toArray).toList
/-- The body's state. -/
abbrev B (m0 : MachineData) : MachineData → Prop :=
  Body m0 112 eqKernelStack slots (out m0) (16 * len m0)

theorem length_K (m : MachineData) {i : Nat} (h : i ≤ np m) : (K m i).length = 2 ^ i := by
  simp only [K, Array.length_toList, NativeRustcVm.size_eqKernel, List.size_toArray,
    List.length_take, NativeRustcVm.length_ewsOf, Nat.min_eq_left h]

theorem K_zero (m : MachineData) : K m 0 = [1] := rfl

/-- Coordinate `i`. -/
abbrev rr (m : MachineData) (i : Nat) : EW := (pts m).getD i 0

theorem rr_eq (m : MachineData) {i : Nat} (h : i < np m) :
    rr m i = (pts m)[i]'(by simp; exact h) := by
  simp only [rr, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < (pts m).length by simp; exact h), Option.getD_some]

theorem K_succ (m : MachineData) {i : Nat} (h : i < np m) :
    K m (i + 1) = (K m i).map (· * (1 + rr m i)) ++ (K m i).map (· * rr m i) := by
  rw [rr_eq m h]
  exact NativeRustcVm.eqKernel_take_succ _ _

theorem K_np (m : MachineData) :
    K m (np m) = (eqKernel (slice m (reg m .rdi) (reg m .rsi))).toList := by
  simp only [K, slice]
  rw [List.take_of_length_le (by simp)]

theorem eqKernelStack_eq : eqKernelStack = 256 := rfl

theorem all_slotted (r : Reg64) (h : calleeSaved r = true) : r ∈ slots.map (·.2) := by
  cases r <;> simp_all [calleeSaved, slots]

theorem keepsRegs_head {S₀ S₁ : SState} {r : Reg64} {rs : List Reg64}
    (h : keepsRegs S₀ S₁ (r :: rs) = true) : keepsRegs S₀ S₁ (.rsp :: freeRegs slots) = true ∨
      r ≠ .rsp := by
  by_cases hr : r = .rsp
  · left
    subst hr
    rw [freeRegs_slots]
    unfold keepsRegs at h ⊢
    simp only [List.all_cons, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, rfl⟩
  · exact Or.inr hr

/-- RSP and nothing else: what a frame block must keep. -/
theorem keepsRegs_rsp {S₀ S₁ : SState} {rs : List Reg64}
    (h : keepsRegs S₀ S₁ (.rsp :: rs) = true) : keepsRegs S₀ S₁ (.rsp :: freeRegs slots) = true :=
  (keepsRegs_head h).resolve_right (by simp)

theorem keepsRegs_free (S₀ S₁ : SState) : keepsRegs S₀ S₁ (freeRegs slots) = true := by
  rw [freeRegs_slots]; rfl

/-! ## Addresses -/

section addr
variable {m0 : MachineData}

theorem fb_toNat (hS : StackOk m0 eqKernelStack) : (fb m0).toNat = (rspOf m0).toNat - 112 := by
  have := hS.1
  rw [eqKernelStack_eq] at this
  exact stackBelow_toNat (by omega)

/-- A byte of the frame is not one of `out`'s. -/
theorem frame_not_out (hpre : EqKernelPre m0) {j : Nat} (hj : j < 120) :
    ¬InRange (out m0) (16 * len m0) (fb m0 + BitVec.ofNat 64 j) := by
  obtain ⟨hS, -, -, ⟨⟨-, hnO⟩, hoO⟩, -⟩ := hpre
  have hS1 := hS.1
  have hS2 := hS.2.1
  rw [eqKernelStack_eq] at hS1
  have hfb := fb_toNat hS
  unfold OffStack Apart at hoO
  rw [stackBelow_toNat (by rw [eqKernelStack_eq]; omega), eqKernelStack_eq] at hoO
  unfold NoWrap at hnO
  rw [Sym.inRange_iff hnO, toNat_add_ofNat _ _ (by omega), hfb]
  omega

/-- Bytes of an element of `out` are `out`'s. -/
theorem in_out {O : BitVec 64} {L y : Nat} {q : BitVec 64} (hO : NoWrap O (16 * L))
    (hy : y < L) (h : InRange (O + BitVec.ofNat 64 (16 * y)) 16 q) : InRange O (16 * L) q :=
  inRange_sub hO (by omega) h

/-- A byte of `out` outside element `y`. -/
theorem not_in_elem {O : BitVec 64} {L x y : Nat} (hO : O.toNat + 16 * L ≤ 2 ^ 64)
    (hx : x < 16 * L) (hy : y < L) (h : x < 16 * y ∨ 16 * y + 16 ≤ x) :
    ¬InRange (O + BitVec.ofNat 64 (16 * y)) 16 (O + BitVec.ofNat 64 x) := by
  rw [Sym.inRange_iff (show (O + BitVec.ofNat 64 (16 * y)).toNat + 16 ≤ 2 ^ 64 by
    rw [toNat_add_ofNat _ _ (by omega)]; omega), toNat_add_ofNat _ _ (by omega),
    toNat_add_ofNat _ _ (by omega)]
  omega

end addr

/-! ## The frame's locals -/

/-- The coordinate's address, the size, `point`'s end, `|out|`, at the frame's offsets 8, 16, 32,
40. -/
structure Loc (m0 : MachineData) (d : DataMem) (i : Nat) : Prop where
  ptw : WordAt d (fb m0 + BitVec.ofNat 64 8) (UInt64.ofBitVec (pt m0 + BitVec.ofNat 64 (16 * i)))
  size : WordAt d (fb m0 + BitVec.ofNat 64 16) (UInt64.ofBitVec (BitVec.ofNat 64 (2 ^ np m0)))
  pend : WordAt d (fb m0 + BitVec.ofNat 64 32) (UInt64.ofBitVec (pt m0 + BitVec.ofNat 64 (16 * np m0)))
  lenw : WordAt d (fb m0 + BitVec.ofNat 64 40) (UInt64.ofBitVec (reg m0 .rcx))

/-- A frame word where the frame's bytes are unchanged. -/
theorem fw_congr {m0 : MachineData} {d d' : DataMem} {o : Nat} {w : UInt64}
    (hw : WordAt d (fb m0 + BitVec.ofNat 64 o) w)
    (h : ∀ j, o ≤ j → j < o + 8 → d'.get? (fb m0 + BitVec.ofNat 64 j) = d.get? (fb m0 + BitVec.ofNat 64 j)) :
    WordAt d' (fb m0 + BitVec.ofNat 64 o) w :=
  wordAt_congr hw fun j hj ↦ by rw [addr_add]; exact h _ (by omega) (by omega)

theorem Loc.congr {m0 : MachineData} {d d' : DataMem} {i : Nat} (hl : Loc m0 d i)
    (h : ∀ j, 8 ≤ j → j < 64 → d'.get? (fb m0 + BitVec.ofNat 64 j) = d.get? (fb m0 + BitVec.ofNat 64 j)) :
    Loc m0 d' i :=
  ⟨fw_congr hl.ptw fun j h1 h2 ↦ h j (by omega) (by omega),
    fw_congr hl.size fun j h1 h2 ↦ h j (by omega) (by omega),
    fw_congr hl.pend fun j h1 h2 ↦ h j (by omega) (by omega),
    fw_congr hl.lenw fun j h1 h2 ↦ h j (by omega) (by omega)⟩

/-- A frame word loaded from region 0 of an environment whose region 0 is the frame. -/
theorem load_fw [Labels] {m0 st : MachineData} {rs : List (BitVec 64 × Nat)} {o : Nat} {w : UInt64}
    {vars : Nat → BitVec 64} {ret : BitVec 64}
    (h : WordAt st.dmem (fb m0 + BitVec.ofNat 64 o) w) :
    (Env.ofMachine st ((fb m0, 120) :: rs) vars ret).load 0 o 8 = w.toBitVec :=
  load_word h

/-- A frame word written by a block. -/
theorem fw_write [Labels] {m0 st m : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hm : Match (Env.ofMachine st ((fb m0, 120) :: rs) vars ret) S m) {o : Nat} (ho : o + 8 ≤ 120)
    {v : Sym} (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (v, i)) :
    WordAt m.dmem (fb m0 + BitVec.ofNat 64 o)
      (UInt64.ofBitVec (v.eval (Env.ofMachine st ((fb m0, 120) :: rs) vars ret))) :=
  wordAt_of_write hm rfl ho hw

/-- A frame word a block's writes miss. -/
theorem fw_keep [Labels] {m0 st m : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hm : Match (Env.ofMachine st ((fb m0, 120) :: rs) vars ret) S m) {o : Nat} (ho : o + 8 ≤ 120)
    (h : firstOverlap 0 o 8 S.mem = none) {w : UInt64}
    (h0 : WordAt st.dmem (fb m0 + BitVec.ofNat 64 o) w) : WordAt m.dmem (fb m0 + BitVec.ofNat 64 o) w :=
  wordAt_keep hm rfl ho h h0

/-- Frame bytes at or above `L` where a block writes region 0 below `L` only. -/
theorem frame_above [Labels] {m0 st m : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hm : Match (Env.ofMachine st ((fb m0, 120) :: rs) vars ret) S m)
    (hwf : (Env.ofMachine st ((fb m0, 120) :: rs) vars ret).WF) {L : Nat}
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ L) :
    ∀ j, L ≤ j → j < 120 → m.dmem.get? (fb m0 + BitVec.ofNat 64 j) = st.dmem.get? (fb m0 + BitVec.ofNat 64 j) := by
  intro j hL hj
  refine hm.get?_mem0 hwf fun h ↦ ?_
  have hn := hwf.noWrap 0 _ _ rfl
  have h1 := written_region0 rfl hwf (show L ≤ 120 by omega) hw h
  rw [Sym.inRange_iff (by omega), toNat_add_ofNat _ _ (by omega)] at h1
  omega

/-! ## The body -/

/-- **Memory changed in `out` only** keeps the body. -/
theorem B.of_out {m0 st st' : MachineData} (hpre : EqKernelPre m0) (hb : B m0 st)
    (hrsp : rspOf st' = rspOf st)
    (hsame : ∀ p, ¬InRange (out m0) (16 * len m0) p → st'.dmem.get? p = st.dmem.get? p)
    (hk : Kept st.dmem st'.dmem) : B m0 st' :=
  ⟨by rw [hrsp]; exact hb.rsp, fun p hp i hi ↦ by
      simp only [List.length_map, List.length_range] at hi
      have := slots_ok p hp
      rw [addr_add, hsame _ (frame_not_out hpre (by omega)), ← addr_add]
      exact hb.frame p hp i (by simpa using hi),
    fun r hr hn ↦ absurd (all_slotted r hr) hn,
    fun p hp ↦ by rw [hsame p fun h ↦ hp (Or.inl h)]; exact hb.same p hp,
    fun p h ↦ hk p (hb.kept p h)⟩

/-- A block of registers only keeps the body. -/
theorem B.of_regs [Labels] {m0 st st' : MachineData} {S : SState} {rs : List Reg64}
    (hpre : EqKernelPre m0) (hb : B m0 st) (hm : Match (Env.ofMachine st []) S st')
    (hk : keepsAll regsS S rs = true) : B m0 st' ∧ st'.dmem = st.dmem ∧ ∀ r ∈ rs, reg st' r = reg st r := by
  unfold keepsAll at hk
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hk
  have he := regs_eq_of (match_nil _) hm hk.1
  have hdm : st'.dmem = st.dmem := hm.dmem_eq (Env.wf_nil _) hk.2
  exact ⟨B.of_out hpre hb (he .rsp (List.mem_cons_self ..)) (fun p _ ↦ by rw [hdm])
    (by rw [hdm]; exact fun _ h ↦ h), hdm, fun r h ↦ he r (List.mem_cons_of_mem _ h)⟩

/-- The bytes no write of a block covers, with writes in regions 1 and 2 only. -/
theorem same12 [Labels] {st m : MachineData} {a0 a1 a2 : BitVec 64} {n0 n1 n2 : Nat} {S : SState}
    {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hm : Match (Env.ofMachine st [(a0, n0), (a1, n1), (a2, n2)] vars ret) S m)
    (hwf : (Env.ofMachine st [(a0, n0), (a1, n1), (a2, n2)] vars ret).WF)
    (hw : ∀ w ∈ S.mem, (w.r = 1 ∧ w.off + w.n ≤ n1) ∨ (w.r = 2 ∧ w.off + w.n ≤ n2)) :
    ∀ p, ¬InRange a1 n1 p → ¬InRange a2 n2 p → m.dmem.get? p = st.dmem.get? p :=
  fun p hp1 hp2 ↦ hm.get?_mem0 hwf fun ⟨w, hw', b, sz, hb', h1, h2⟩ ↦ by
    have hn1 := hwf.noWrap 1 _ _ rfl
    have hn2 := hwf.noWrap 2 _ _ rfl
    rcases hw w hw' with ⟨hr, hoff⟩ | ⟨hr, hoff⟩
    · rw [hr] at hb'
      change some (a1, n1) = some (b, sz) at hb'
      cases hb'
      exact hp1 (by rw [Sym.inRange_iff (by omega)]; omega)
    · rw [hr] at hb'
      change some (a2, n2) = some (b, sz) at hb'
      cases hb'
      exact hp2 (by rw [Sym.inRange_iff (by omega)]; omega)

/-! ## The invariants -/

/-- **The outer loop's head** `NativeRustcVmX64.Vm.EqKernel.label_4`, `i` coordinates done. -/
structure OInv (m0 : MachineData) (i : Nat) (s : MachineData) : Prop where
  body : B m0 s
  loc : Loc m0 s.dmem i
  lt : i < np m0
  rdx : reg s .rdx = BitVec.ofNat 64 (2 ^ i)
  r8 : reg s .r8 = reg m0 .rcx
  r15 : reg s .r15 = out m0 + BitVec.ofNat 64 8
  ker : EWsAt s.dmem (out m0) (K m0 i)

/-- **The inner loop's head** `NativeRustcVmX64.Vm.EqKernel.label_8`, `j` pairs of round `i` done. -/
structure IInv (m0 : MachineData) (i j : Nat) (s : MachineData) : Prop where
  body : B m0 s
  loc : Loc m0 s.dmem i
  lt : i < np m0
  jlt : j < 2 ^ i
  half : WordAt s.dmem (fb m0 + BitVec.ofNat 64 24) (UInt64.ofBitVec (BitVec.ofNat 64 (2 ^ i)))
  rlo : WordAt s.dmem (fb m0 + BitVec.ofNat 64 56) (rr m0 i).c0
  rhi : WordAt s.dmem (fb m0 + BitVec.ofNat 64 48) (rr m0 i).c1
  rbx : reg s .rbx = BitVec.ofNat 64 (16 * j)
  rbp : reg s .rbp = BitVec.ofNat 64 (16 * 2 ^ i)
  r12 : reg s .r12 = out m0 + BitVec.ofNat 64 (16 * 2 ^ i + 8)
  r15 : reg s .r15 = out m0 + BitVec.ofNat 64 8
  lo : EWsAt s.dmem (out m0) (half1 (K m0 i) (rr m0 i) j)
  hi : EWsAt s.dmem (out m0 + BitVec.ofNat 64 (16 * 2 ^ i)) (((K m0 i).take j).map (· * rr m0 i))

/-- **Round `i` done**, at `jmp .LEqKernel_9`. -/
structure RInv (m0 : MachineData) (i : Nat) (s : MachineData) : Prop where
  body : B m0 s
  loc : Loc m0 s.dmem i
  lt : i < np m0
  half : WordAt s.dmem (fb m0 + BitVec.ofNat 64 24) (UInt64.ofBitVec (BitVec.ofNat 64 (2 ^ i)))
  r15 : reg s .r15 = out m0 + BitVec.ofNat 64 8
  ker : EWsAt s.dmem (out m0) (K m0 (i + 1))

/-- The postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ EqKernelPost m0 s.data

theorem pow_facts {m0 : MachineData} (hle : 2 ^ np m0 ≤ len m0) {i : Nat} (h : i < np m0) :
    0 < 2 ^ i ∧ 2 * 2 ^ i ≤ len m0 := by
  have := Nat.pow_le_pow_right (by decide : 0 < 2) (show i + 1 ≤ np m0 from h)
  rw [Nat.pow_succ] at this
  exact ⟨Nat.two_pow_pos i, by omega⟩

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqKernel.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqKernel.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqKernel.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqKernel.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqKernel.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqKernel.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqKernel.b7Offset) :=
  b7_in_code.trans hp.1 (by simp [b7])
theorem hb8 (hp : Placed code k) : b8.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqKernel.b8Offset) :=
  b8_in_code.trans hp.1 (by simp [b8])
theorem hb9 (hp : Placed code k) : b9.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqKernel.b9Offset) :=
  b9_in_code.trans hp.1 (by simp [b9])
theorem hb10 (hp : Placed code k) : b10.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqKernel.b10Offset) :=
  b10_in_code.trans hp.1 (by simp [b10])
theorem hb11 (hp : Placed code k) : b11.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqKernel.b11Offset) :=
  b11_in_code.trans hp.1 (by simp [b11])
theorem hb13 (hp : Placed code k) : b13.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqKernel.b13Offset) :=
  b13_in_code.trans hp.1 (by simp [b13])
theorem hb14 (hp : Placed code k) : b14.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqKernel.b14Offset) :=
  b14_in_code.trans hp.1 (by simp [b14])
theorem hb1314 (hp : Placed code k) : (b13 ++ b14).IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqKernel.b13Offset) :=
  isInfixAt_concat (hb13 hp) (hb14 hp)

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.EqKernel.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b0Offset) :=
  hp.label NativeRustcVmX64.Vm.EqKernel.entry_at
theorem lbl_2 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.EqKernel.label_2 = Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b2Offset) :=
  hp.label NativeRustcVmX64.Vm.EqKernel.label_2_at
theorem lbl_4 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.EqKernel.label_4 = Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b6Offset) :=
  hp.label NativeRustcVmX64.Vm.EqKernel.label_4_at
theorem lbl_8 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.EqKernel.label_8 = Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b9Offset) :=
  hp.label NativeRustcVmX64.Vm.EqKernel.label_8_at
theorem lbl_9 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.EqKernel.label_9 = Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b5Offset) :=
  hp.label NativeRustcVmX64.Vm.EqKernel.label_9_at
theorem lbl_10 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.EqKernel.label_10 = Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b13Offset) :=
  hp.label NativeRustcVmX64.Vm.EqKernel.label_10_at
theorem lbl_11 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.EqKernel.label_11 = Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b14Offset) :=
  hp.label NativeRustcVmX64.Vm.EqKernel.label_11_at

end

end NativeRustcVmX64.Arrays.EqKernel
