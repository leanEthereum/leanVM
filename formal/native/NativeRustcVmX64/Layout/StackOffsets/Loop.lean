module

public import NativeRustcVmX64.Layout.StackOffsets.Front
public import NativeRustcVmX64.Code.Vm.InsertionSortOfStackOffsets.Names

/-!
# `stack_offsets` on x86-64: the sort and the main loop (`b13` to `b21`)

`b13` calls `insertion_sort` on the order array (`sorted`): the order array then holds the
model's `ord`, and `b14` starts the main loop. At its head `NativeRustcVmX64.Vm.StackOffsets.label_14` (`b18`, `Loop m0 j`)
the first `j` blocks of the order are placed (`OutAt`), RDX their total (`P m0 j`), RSI `8 j`.
A turn (`step`): `b19` loads `i = order[j]`, `b20` stores the total at `offsets[i]`, `b21` loads
`sizes[i]` and fails past `63` (`Fail`), `b17` adds `2 ^ size`, failing on a carry. With
`j = n`, `b18` leaves for `NativeRustcVmX64.Vm.StackOffsets.label_22` (`End`).
-/

namespace NativeRustcVmX64.Layout.StackOffsets

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.StackOffsets NativeRustcVmX64.Layout.BuildFrame
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVm.Layout (OffsetsFit)

@[expose] public section

/-- **The main loop's head**: `j` blocks placed. -/
structure Loop (m0 : MachineData) (j : Nat) (d : MachineData) : Prop where
  b : B m0 8 d
  regs : Regs m0 d
  le : j ≤ n m0
  rsi : (reg d .rsi).toNat = 8 * j
  rbp : reg d .rbp = BitVec.ofNat 64 (8 * n m0)
  rdx : (reg d .rdx).toNat = (P m0 j).2
  rax : reg d .rax = 0#64
  ordw : WordsAt d.dmem (ob m0) (natWords (ord m0))
  out : OutAt m0 j d.dmem

/-- **A failure**: at `b22`, the blocks not fitting. -/
abbrev Fail [Host] (k : Nat) (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b22Offset) ∧ B m0 8 s.data ∧ reg s.data .rax = 0#64 ∧ ¬OffsetsFit (sizes m0)

/-- **The loop's end**: at `b23`, every block placed. -/
abbrev End [Host] (k : Nat) (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b23Offset) ∧ Loop m0 (n m0) s.data

end

public section

/-- `1 << x` for `x < 64`. -/
theorem shl1 (x : BitVec 64) (hx : x.toNat < 64) :
    (BinOp.apply .shl .W64 (BitVec.ofNat 64 1) x).toNat = 2 ^ x.toNat := by
  simp only [BinOp.apply, low_W64, ext_W64, shiftCount, shiftMask]
  have hs : (low .W8 x).toNat &&& 63 = x.toNat := by
    rw [toNat_low, Nat.mod_eq_of_lt (by simp [Width.bits]; omega)]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 6) (by omega)
  rw [hs, BitVec.toNat_shiftLeft, show (BitVec.ofNat 64 1).toNat = 1 from rfl, Nat.shiftLeft_eq,
    Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hx)

variable {m0 : MachineData}

/-- The frame's bytes from `8` are not its first `8`. -/
theorem fb_not_low {j : Nat} (h1 : 8 ≤ j) (h2 : j < 2 ^ 64) :
    ¬ NativeRustcVm.InRange (stackBelow m0 1328) 8 (off (stackBelow m0 1328) j) := by
  have := inRange_off_iff (b := stackBelow m0 1328) (o := 0) (n := 8) (j := j) h2 (by omega)
  rw [off_zero] at this
  rw [this]
  omega

/-- The sizes' bytes are not the output's nor the stack's. -/
theorem sizes_out [Labels] (hpre : StackOffsetsPre m0) {q : BitVec 64}
    (h : NativeRustcVm.InRange (reg m0 .rdi) (8 * n m0) q) :
    ¬ (R m0 q ∨ NativeRustcVm.InRange (stackBelow m0 1344) 1344 q) := by
  rintro (h' | h')
  · exact not_inRange_of_apart hpre.2.2.2.2.2.2.1 hpre.2.2.1.2 hpre.2.2.2.2.1.2 h h'
  · exact not_inRange_of_apart hpre.2.2.2.1 hpre.2.2.1.2 (noWrap_stackBelow hpre.1) h
      (inRange_mono h' (show 1344 ≤ stackOffsetsStack + 8 by decide))

/-- **The sizes in a body**: as at the entry. -/
theorem sizes_same [Labels] (hpre : StackOffsetsPre m0) {o : Nat} {d : MachineData} (hb : B m0 o d) :
    natsOf d (reg m0 .rdi) (n m0) = sizes m0 := by
  simp only [natsOf, sizes]
  rw [NativeRustcVm.wordsOf_congr fun t ht ↦ hb.same _ (sizes_out hpre
    (inRange_off_self ht (by have hn : n m0 ≤ 158 := hpre.2.1; omega)))]

/-- The order array's bytes are not the output's. -/
theorem ob_not_R [Labels] (hpre : StackOffsetsPre m0) {o : Nat} (ho : o < 1264) :
    ¬ R m0 (ob m0 + BitVec.ofNat 64 o) := fun h ↦ by
  have hst : StackOk m0 1344 := hpre.1
  refine R_not_frame hst hpre.2.2.2.2.2.1 hpre.2.2.2.2.1.2 h ?_
  rw [ob_add]
  exact fb_in hst (by decide) (by omega)

variable [Host] {k : Nat}

/-- `b13`, `b14`: the order sorted, the main loop's head. -/
theorem sorted (hp : Placed code k)
    (hsort : Spec (label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.entryLabel) InsertionSortPre InsertionSortPost)
    (hpre : StackOffsetsPre m0) {st : MachineState} (h : At13 k m0 st) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b18Offset) ∧ Loop m0 0 s.data) st := by
  obtain ⟨hpc, hR⟩ := h
  have hst : StackOk m0 1344 := hpre.1
  have hn : n m0 ≤ 158 := hpre.2.1
  have hs1 := hst.1
  have hs2 := hst.2.1
  have hfb := fb_toNat hst
  have hob := ob_toNat hst
  obtain ⟨hok, hw13, hK⟩ := ok_b13
  refine run0 (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b13Offset + b13.length)).toBitVec) hst
    (b13_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b13 (fun _ _ ↦ rfl) hpc hR.init.b
    (match0 hR.init.b) hok fun st1 hm1 hpc1 hb1 ↦ ?_
  have hwf1 := fr_wf0 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b13Offset + b13.length)).toBitVec)
    hR.init.b hst (by decide)
  have hK1 := kp hm1 hK (rs' := [Reg64.rdi, .rsi, .rdx, .rcx]) (by simp)
  have x7 : reg st1.data .rdi = ob m0 := (hK1 .rdi (by simp)).trans hR.rdi
  have x6 : (reg st1.data .rsi).toNat = n m0 := by rw [hK1 .rsi (by simp)]; exact hR.rsi
  have x2 : reg st1.data .rdx = reg m0 .rdi := (hK1 .rdx (by simp)).trans hR.rdx
  have x1 : (reg st1.data .rcx).toNat = n m0 := by rw [hK1 .rcx (by simp)]; exact hR.rcx
  have hR1 : Regs m0 st1.data := hR.init.regs.of (kp hm1 hK (by simp [cs]))
  have hbp1 : reg st1.data .rbp = BitVec.ofNat 64 (8 * n m0) :=
    (kp hm1 hK (rs' := [Reg64.rbp]) (by simp [cs]) .rbp (by simp)).trans hR.init.rbp
  -- the order array, kept by `b13` (it writes the return address only)
  have hs13 := sameOutside_low hwf1 hm1 (r := 0) rfl (by decide) hw13
  have hords1 : Ords m0 (n m0) st1.data.dmem := fun t ht ↦
    NativeRustcVm.Transcript.bytesAt_congr (hR.init.ords t ht) fun i hi ↦ hs13 _ (by
      have hi8 : i < 8 := by simpa [NativeRustcVm.length_wordBytes] using hi
      rw [NativeRustcVm.addr_add, ob_add]
      exact fb_not_low (by omega) (by omega))
  have hrsp1 := hb1.rsp0
  have hpre1 : InsertionSortPre st1.data := by
    unfold InsertionSortPre
    rw [x7, x2, x6, x1]
    have hok := ord_ok (o := 0) (l := 8 * n m0) hst hb1 (by omega)
    rw [show 16 + 0 = 16 from rfl, ← ob_eq] at hok
    have hcal : (stackBelow st1.data 16).toNat = (rspOf m0).toNat - 1344 := by
      rw [stackBelow_callee hrsp1 (by omega), stackBelow_toNat (by omega)]
    refine ⟨hb1.stackOk hst (by decide), hok, ?_, ⟨Mapped.keeps hpre.2.2.1.1 hb1.fr.kept,
      hpre.2.2.1.2⟩, apart_callee hpre.2.2.2.1 hrsp1 hs1 (by decide), ?_⟩
    · show (ob m0).toNat + 8 * n m0 ≤ (stackBelow st1.data 16).toNat ∨
        (stackBelow st1.data 16).toNat + (16 + 8) ≤ (ob m0).toNat
      rw [hcal, hob]; omega
    · have := hpre.2.2.2.1
      unfold OffStack NativeRustcX64.Apart at this
      rw [SS_eq] at this
      show (ob m0).toNat + 8 * n m0 ≤ (reg m0 .rdi).toNat ∨
        (reg m0 .rdi).toNat + 8 * n m0 ≤ (ob m0).toNat
      rw [stackBelow_toNat hs1] at this
      have x1' : (reg st1.data .rcx).toNat = (reg m0 .rsi).toNat := x1
      rw [hob]; omega
  refine call_then hpc1 hsort hpre1 fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hw2, hso2, hsv2⟩ := hpost
  unfold Changes at hso2
  rw [x7, x2, x6, x1, sizes_same hpre hb1, natsOf_ords rfl (by omega) hords1] at hw2
  rw [x7, x6] at hso2
  have hb2 : B m0 8 st2.data := hb1.call hsv2 hrsp2 hso2 (fun q h ↦ by
      rcases h with h | h
      · exact Or.inr (off_in_stack hst (o := 16) (l := 8 * n m0) (by omega) h)
      · exact Or.inr (hb1.callee hst (by decide) h).1)
    (fun p hp i hi h ↦ by
      have := slots_ge p hp
      have := slots_le p hp
      rcases h with h | h
      · have h' : NativeRustcVm.InRange _ _ _ := h
        rw [ob_eq, inRange_off_iff (by omega) (by omega)] at h'; omega
      · exact (hb1.callee hst (by decide) h).2 (fb_in hst (by decide) (by omega)))
    (fun j hj h ↦ by
      rcases h with h | h
      · have h' : NativeRustcVm.InRange _ _ _ := h
        rw [ob_eq, inRange_off_iff (by omega) (by omega)] at h'; omega
      · exact (hb1.callee hst (by decide) h).2 (fb_in hst (by decide) (by omega)))
  have hR2 : Regs m0 st2.data := hR1.saved hsv2
  -- `b14`
  obtain ⟨hok14, hmem14, hax, hsx, hdx, hK14⟩ := ok_b14
  refine step0 hst (b14_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b14 nofun
    (hpc2.trans rfl) hb2 hok14 hmem14 fun st3 hm3 hpc3 hb3 hd3 ↦ .done _
      ⟨hpc3.trans (hp.label NativeRustcVmX64.Vm.StackOffsets.label_14_at), hb3, hR2.of (kp hm3 hK14 (by simp [cs])),
        Nat.zero_le _, ?_, ?_, ?_, hm3.regs .rax _ hax, hd3 ▸ hw2, outAt_zero _ _⟩
  · show (st3.data.regs.get64 .rsi).toNat = _
    rw [hm3.regs .rsi _ hsx]; rfl
  · rw [kp hm3 hK14 (rs' := [Reg64.rbp]) (by simp [cs]) .rbp (by simp)]
    exact (hsv2.1 .rbp rfl).trans hbp1
  · show (st3.data.regs.get64 .rdx).toNat = _
    rw [hm3.regs .rdx _ hdx, P_zero]; rfl

end

end NativeRustcVmX64.Layout.StackOffsets
