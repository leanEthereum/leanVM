module

public import NativeRustcVmX64.Layout.PlacementsOf.Exec
public import NativeRustcVmX64.Layout.PlacementsOf.Model
public import NativeRustcVmX64.Spec.Layout
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# `placements_of` on x86-64: the state, the frame's areas, reads, blocks in a body

The frame (`fb`, 5120 bytes below the entry's RSP): the stack's log-size at `8`, `offsets` at
`16`, `block_cols` at `1280`, `block_sizes` at `2544`, `block_offsets` at `3808`, the pushed
registers from `5072`. A body (`B m0 o`) changes only the placements and the stack.

- Reads: a log-size `kappas[c]` (`kap_same`, `κ_eq`), a byte of the read-only data (`rod_get`).
- Blocks: of the frame alone (`run0`, `step0`), of regions named by aliases (`runA`).
-/

namespace NativeRustcVmX64.Layout.PlacementsOf

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.PlacementsOf NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeRustcVmX64.Layout.BuildFrame
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf)

@[expose] public section

/-- The log-sizes. -/
abbrev kk (m0 : MachineData) : BitVec 64 := reg m0 .rdi
/-- The placements. -/
abbrev pp (m0 : MachineData) : BitVec 64 := reg m0 .rsi
/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 5120
/-- The output: the placements. -/
abbrev R (m0 : MachineData) : BitVec 64 → Prop := NativeRustcVm.InRange (pp m0) placementsBytes
/-- **A body**, RSP at the frame's offset `o`. -/
abbrev B (m0 : MachineData) (o : Nat) (d : MachineData) : Prop := Bd m0 5120 6464 slots (R m0) o d
/-- Column `c`'s log-size. -/
abbrev κ (m0 : MachineData) (c : Nat) : Nat := (natsOf m0 (reg m0 .rdi) columnCountW).getD c 0

section
variable [Labels]

/-- The facts of the precondition the blocks use. -/
structure Facts (m0 : MachineData) : Prop where
  stack : StackOk m0 6464
  rod : RodataAt m0 6464
  kr : Readable m0 (kk m0) kappasBytes
  ko : OffStack m0 (kk m0) kappasBytes 6464
  pr : Readable m0 (pp m0) placementsBytes
  po : OffStack m0 (pp m0) placementsBytes 6464
  prod : RodataApart (pp m0) placementsBytes
  ap : Apart (kk m0) kappasBytes (pp m0) placementsBytes
  kle : ∀ x ∈ natsOf m0 (reg m0 .rdi) columnCountW, x ≤ 36
  got : GotAt m0 placementsOfStack [(kk m0, kappasBytes), (pp m0, placementsBytes)] ["memset"]

end

end

public section

theorem SS_eq : placementsOfStack = 6464 := rfl
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 5120 := by decide
theorem slots_ge : ∀ p ∈ slots, 5072 ≤ p.1 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide
theorem sub5 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14], r ∈ cs := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [cs]
theorem sub5d : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14], r ∈ Reg64.rdx :: cs :=
  fun r hr ↦ List.mem_cons_of_mem _ (sub5 r hr)
theorem cs_callee : ∀ r ∈ cs, calleeSaved r = true := by
  intro r hr
  simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem kappasBytes_eq : kappasBytes = 1264 := rfl
theorem placementsBytes_eq : placementsBytes = 3792 := rfl

section
variable [Labels] {m0 : MachineData}

theorem Facts.of_pre (h : PlacementsOfPre m0) : Facts m0 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

theorem Facts.κ_le (hF : Facts m0) {c : Nat} (hc : c < 158) : κ m0 c ≤ 36 := by
  have hs : (natsOf m0 (reg m0 .rdi) columnCountW).size = 158 := by
    simp [natsOf, columnCountW, NativeRustcVm.wordsOf]
  have := hF.kle _ (Array.getElem_mem (xs := natsOf m0 (reg m0 .rdi) columnCountW) (i := c)
    (by rw [hs]; exact hc))
  simpa [Array.getD, hs, hc] using this

theorem Facts.sumF_le' (hF : Facts m0) (kr : Nat) : sumF (κ m0) kr ≤ 158 * 2 ^ 36 :=
  sumF_le _ kr fun _ hc ↦ hF.κ_le hc

/-! ## The frame's geometry -/

theorem Facts.rsp (hF : Facts m0) : 6464 ≤ (rspOf m0).toNat ∧ (rspOf m0).toNat + 8 ≤ 2 ^ 64 :=
  ⟨hF.stack.1, hF.stack.2.1⟩

theorem Facts.fb_toNat (hF : Facts m0) : (fb m0).toNat = (rspOf m0).toNat - 5120 :=
  stackBelow_toNat (by have := hF.rsp; omega)

theorem Facts.off_toNat (hF : Facts m0) {o : Nat} (ho : o < 5128) :
    (off (fb m0) o).toNat = (rspOf m0).toNat - 5120 + o := by
  have := hF.rsp
  rw [toNat_off (by rw [hF.fb_toNat]; omega), hF.fb_toNat]

theorem Facts.fnw (hF : Facts m0) : NativeRustcVm.NoWrap (fb m0) (5120 + 8) :=
  frame_noWrap hF.stack (by decide)

theorem Facts.sb_toNat (hF : Facts m0) : (stackBelow m0 6464).toNat = (rspOf m0).toNat - 6464 :=
  stackBelow_toNat hF.rsp.1

/-- Part of the frame, mapped and not wrapping in a body. -/
theorem Facts.part (hF : Facts m0) {o l oo : Nat} {d : MachineData} (hb : B m0 oo d)
    (hl : o + l ≤ 5120) :
    NativeRustcVm.Mapped d.dmem (off (fb m0) o) l ∧ NativeRustcVm.NoWrap (off (fb m0) o) l := by
  have := hF.rsp
  refine ⟨Mapped.keeps (mapped_off (frame_mapped hF.stack (by decide)) (by omega)) hb.fr.kept, ?_⟩
  unfold NativeRustcVm.NoWrap
  rw [hF.off_toNat (by omega)]
  omega

/-- A part of the frame below the slots is in the stack, off the slots and return address. -/
theorem Facts.part_low (hF : Facts m0) {o l : Nat} (hl : o + l ≤ 5072) {q : BitVec 64}
    (h : NativeRustcVm.InRange (off (fb m0) o) l q) :
    NativeRustcVm.InRange (fb m0) 5072 q := by
  have := hF.rsp
  have hnw : NativeRustcVm.NoWrap (off (fb m0) o) l := by
    unfold NativeRustcVm.NoWrap; rw [hF.off_toNat (by omega)]; omega
  rw [inRange_iff' hnw, hF.off_toNat (by omega)] at h
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hF.fb_toNat]; omega), hF.fb_toNat]
  omega

/-- Two parts of the frame apart. -/
theorem Facts.part_apart (hF : Facts m0) {o l o' l' : Nat} (h : o + l ≤ 5120)
    (h' : o' + l' ≤ 5120) (hd : o + l ≤ o' ∨ o' + l' ≤ o) :
    NativeRustcVm.Apart (off (fb m0) o) l (off (fb m0) o') l' := by
  unfold NativeRustcVm.Apart
  rw [hF.off_toNat (by omega), hF.off_toNat (by omega)]
  omega

/-- What is off the stack is apart from a part of the frame. -/
theorem Facts.part_apart_off (hF : Facts m0) {o l : Nat} (h : o + l ≤ 5120) {a : BitVec 64}
    {n : Nat} (ho : OffStack m0 a n 6464) : NativeRustcVm.Apart (off (fb m0) o) l a n := by
  have := hF.rsp
  have h1 : NativeRustcVm.Apart a n (stackBelow m0 6464) (6464 + 8) := ho
  unfold NativeRustcVm.Apart at h1 ⊢
  rw [hF.sb_toNat] at h1
  rw [hF.off_toNat (by omega)]
  omega

/-- The frame apart from the output. -/
theorem Facts.R_frame (hF : Facts m0) {q : BitVec 64} (h : R m0 q) :
    ¬ NativeRustcVm.InRange (fb m0) (5120 + 8) q :=
  not_inRange_of_apart (apart_frame hF.po hF.rsp.1 (by decide)) hF.pr.2 hF.fnw h

/-! ## Reads -/

/-- The log-sizes' bytes are neither the output's nor the stack's. -/
theorem Facts.kk_out (hF : Facts m0) {q : BitVec 64} (h : NativeRustcVm.InRange (kk m0) 1264 q) :
    ¬ (R m0 q ∨ NativeRustcVm.InRange (stackBelow m0 6464) 6464 q) := by
  rintro (h' | h')
  · exact not_inRange_of_apart hF.ap hF.kr.2 hF.pr.2 h h'
  · exact not_inRange_of_apart hF.ko hF.kr.2 (noWrap_stackBelow hF.stack) h
      (inRange_mono h' (by omega))

/-- **A log-size in a body**: as at the entry. -/
theorem kap_same (hF : Facts m0) {oo : Nat} {d : MachineData} (hb : B m0 oo d) {c : Nat}
    (hc : c < 158) :
    wordOf d.dmem (kk m0 + BitVec.ofNat 64 (8 * c)) = wordOf m0.dmem (kk m0 + BitVec.ofNat 64 (8 * c)) :=
  NativeRustcVm.wordOf_congr fun i hi ↦ by
    rw [NativeRustcVm.addr_add]
    have : (kk m0).toNat + kappasBytes ≤ 2 ^ 64 := hF.kr.2
    exact hb.same _ (hF.kk_out (inRange_off_self (by omega) (by rw [kappasBytes_eq] at this; omega)))

omit [Labels] in
theorem κ_eq (m0 : MachineData) {c : Nat} (hc : c < 158) :
    κ m0 c = (wordOf m0.dmem (kk m0 + BitVec.ofNat 64 (8 * c))).toNat := by
  simp [natsOf, NativeRustcVm.wordsOf, columnCountW, hc]

/-- **A byte of the read-only data in a body**. -/
theorem rod_get (hF : Facts m0) {oo : Nat} {d : MachineData} (hb : B m0 oo d)
    (t : NativeRustcVm.Data.Item) {i : Nat} (hi : i < t.bytes.length) :
    d.dmem.get? (rodataAddr t + BitVec.ofNat 64 i) = some t.bytes[i] := by
  have hnw := hF.rod.noWrap t
  unfold NativeRustcVm.NoWrap at hnw
  have hin : NativeRustcVm.InRange (rodataAddr t) t.bytes.length (rodataAddr t + BitVec.ofNat 64 i) :=
    inRange_off_self hi (by omega)
  rw [hb.same _ fun h ↦ h.elim
    (fun h' ↦ not_inRange_of_apart (Apart.symm' (hF.prod t)) hnw hF.pr.2 hin h')
    (fun h' ↦ not_inRange_of_apart (hF.rod.apart t) hnw (noWrap_stackBelow hF.stack) hin
      (inRange_mono h' (by omega)))]
  exact hF.rod.bytesAt t i hi

end

/-! ## Values -/

theorem length_slot : (NativeRustcVm.Data.Item.bytes .keccakSlot).length = 158 := by
  simp [NativeRustcVm.Data.Item.bytes, NativeRustcVm.Data.keccakSlot, columnCount_158]

theorem length_out : (NativeRustcVm.Data.Item.bytes .keccakOutput).length = 158 := by
  simp [NativeRustcVm.Data.Item.bytes, NativeRustcVm.Data.keccakOutput, columnCount_158]

theorem slot_get {c : Nat} (hc : c < 158) :
    (NativeRustcVm.Data.Item.bytes .keccakSlot)[c]'(by rw [length_slot]; exact hc) =
      NativeRustcVm.Data.slotByte (slotF c) := slot_byte hc

theorem out_get {c : Nat} (hc : c < 158) :
    (NativeRustcVm.Data.Item.bytes .keccakOutput)[c]'(by rw [length_out]; exact hc) =
      if outF c then 1 else 0 := out_byte hc

theorem slotByte_255 {c : Nat} :
    (NativeRustcVm.Data.slotByte (slotF c)).toNat = 255 ↔ slotF c = none := by
  rw [← slotByte_none]
  constructor
  · intro h; apply UInt8.toNat.inj; rw [h]; rfl
  · intro h; rw [h]; rfl

/-- A byte loaded from the environment's memory. -/
theorem load_byte {env : Env} {r off : Nat} {b : UInt8}
    (h : env.mem0.get? (env.base r + BitVec.ofNat 64 off) = some b) :
    (env.load r off 1).toNat = b.toNat := by
  have hl := Env.load_of_bytesAt (env := env) (r := r) (off := off) (bs := [b]) (n := 1) rfl
    (fun i hi ↦ by
      simp only [List.length_singleton, Nat.lt_one_iff] at hi
      subst hi
      simpa using h)
  rw [hl, ofBytes_natCast, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  show (0 * 256 + b.toNat) % 2 ^ 64 = b.toNat
  have := b.toNat_lt
  omega

/-- A byte compared (`cmpb`). -/
theorem eq8 {x : BitVec 64} {b v : Nat} (hx : x.toNat = b) (hb : b < 256) :
    CmpOp.apply .eq .W8 x (BitVec.ofNat 64 v) = decide (b = v % 256) := by
  simp only [CmpOp.apply]
  by_cases h : b = v % 256
  · rw [decide_eq_true h]
    apply beq_iff_eq.mpr
    apply BitVec.eq_of_toNat_eq
    rw [toNat_low, toNat_low, hx, BitVec.toNat_ofNat]
    simp only [Width.bits]
    omega
  · rw [decide_eq_false h]
    apply beq_eq_false_iff_ne.mpr
    intro he
    have := congrArg BitVec.toNat he
    rw [toNat_low, toNat_low, hx, BitVec.toNat_ofNat] at this
    simp only [Width.bits] at this
    omega

theorem ult_eval [Labels] (env : Env) (a b : Sym) :
    (SBool.cmp .ult .W64 a b).eval env = decide ((a.eval env).toNat < (b.eval env).toNat) := by
  simp only [SBool.eval, CmpOp.apply, low_W64, BitVec.ult]

theorem eq_eval [Labels] (env : Env) (a b : Sym) :
    (SBool.cmp .eq .W64 a b).eval env = decide ((a.eval env).toNat = (b.eval env).toNat) := by
  simp only [SBool.eval, CmpOp.apply, low_W64]
  by_cases h : a.eval env = b.eval env
  · simp [h]
  · simp only [beq_eq_false_iff_ne.mpr h]
    exact (decide_eq_false fun h' ↦ h (BitVec.eq_of_toNat_eq h')).symm

theorem test_eval' [Labels] (env : Env) (a : Sym) :
    (SBool.cmp .eq .W64 (.bin .and .W64 a a) (.lit 0)).eval env = decide ((a.eval env).toNat = 0) := by
  rw [eq_eval]
  simp [Sym.eval, BinOp.apply]

theorem toNat_toUInt64 {x : Nat} (h : x < 2 ^ 64) : x.toUInt64.toNat = x := by
  rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- A byte at offset `j` of an area, outside its sub-range `[o, o + n)`. -/
theorem notin_off {b : BitVec 64} {o n j : Nat} (hj : j < 2 ^ 64) (h : o + n ≤ 2 ^ 64)
    (hc : j < o ∨ o + n ≤ j) : ¬ NativeRustcVm.InRange (off b o) n (off b j) := by
  rw [inRange_off_iff hj h]; omega

/-- A byte at offset `j ≥ n` of an area, outside its first `n` bytes. -/
theorem notin_base {b : BitVec 64} {n j : Nat} (hj : j < 2 ^ 64) (hn : n ≤ j) :
    ¬ NativeRustcVm.InRange b n (off b j) := by
  have := notin_off (b := b) (o := 0) (n := n) (j := j) hj (by omega) (by omega)
  rwa [off_zero] at this

/-- A branch on a condition the executor evaluates to `decide P`. -/
theorem pc_of {pc a b : Int64} {c : Bool} {P : Prop} [Decidable P]
    (h : pc = if c = true then a else b) (hc : c = decide P) : (P → pc = a) ∧ (¬P → pc = b) := by
  subst hc
  exact ⟨fun hp ↦ by simpa [hp] using h, fun hp ↦ by simpa [hp] using h⟩

theorem lit_toNat {c : Nat} (h : c < 2 ^ 64) : (BitVec.ofNat 64 c).toNat = c :=
  NativeRustcVm.toNat_ofNat_of_lt h

theorem u64_of {v : BitVec 64} {t : Nat} (h : v.toNat = t) : UInt64.ofBitVec v = t.toUInt64 := by
  have := v.isLt
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofBitVec, UInt64.toNat_ofNat', h, Nat.mod_eq_of_lt (by omega)]

/-- `p + 8 i`. -/
theorem idx_eval [Labels] (env : Env) (p i : Reg64) :
    (idx p i).eval env = env.regs p + BitVec.ofNat 64 (8 * (env.regs i).toNat) := by
  simp only [idx, Sym.eval, BinOp.apply, low_W64, ext_W64]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Width.bits]
  omega

/-- Negative offsets. -/
theorem add_m1272 (x : BitVec 64) : x + BitVec.ofInt 64 (-1272) = x - BitVec.ofNat 64 1272 := by
  rw [show BitVec.ofInt 64 (-1272) = 0#64 - BitVec.ofNat 64 1272 by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofInt, BitVec.toNat_sub]; simp,
    BitVec.zero_sub, ← BitVec.sub_eq_add_neg]

theorem add_m3800 (x : BitVec 64) : x + BitVec.ofInt 64 (-3800) = x - BitVec.ofNat 64 3800 := by
  rw [show BitVec.ofInt 64 (-3800) = 0#64 - BitVec.ofNat 64 3800 by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofInt, BitVec.toNat_sub]; simp,
    BitVec.zero_sub, ← BitVec.sub_eq_add_neg]

theorem add_m8 (x : BitVec 64) : x + BitVec.ofInt 64 (-8) = x - BitVec.ofNat 64 8 := by
  rw [show BitVec.ofInt 64 (-8) = 0#64 - BitVec.ofNat 64 8 by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofInt, BitVec.toNat_sub]; simp,
    BitVec.zero_sub, ← BitVec.sub_eq_add_neg]

theorem off_sub (b : BitVec 64) {o c : Nat} (hc : c ≤ o) (h : b.toNat + o < 2 ^ 64) :
    off b o - BitVec.ofNat 64 c = off b (o - c) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_off h, toNat_off (by omega), BitVec.toNat_ofNat]
  omega

/-- A register a block keeps (`Keeps`). -/
theorem kreg [Labels] {d d' : MachineData} {rs0 : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64}
    {ret : BitVec 64} {Sy : SState} (hm : Match (Env.ofMachine d rs0 vs ret) Sy d')
    {rs : List Reg64} (h : Keeps Sy rs = true) {r : Reg64} (hr : r ∈ rs) : reg d' r = reg d r :=
  keeps_reg hm h hr

/-! ## Blocks in a body -/

variable [Host] {m0 : MachineData}

/-- A body in the frame's environment, RSP at offset `8`. -/
theorem match0 {d : MachineData} {ret : BitVec 64} (hb : B m0 8 d) :
    Match (frameEnv m0 d 5120 [] (fun _ ↦ 0) ret) bodyS d :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨hb.fr.rsp_eval, trivial⟩ trivial trivial trivial

/-- The GOT bytes survive the body's stack and output writes. -/
theorem Facts.got_bytes (hF : Facts m0) {d : MachineData} {o : Nat} (hb : B m0 o d) :
    ∀ l ∈ ["memset"], ∀ i < 8,
      d.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
        m0.dmem.get? (gotAddr l + BitVec.ofNat 64 i) :=
  got_keep hF.got hF.stack (writes := [(pp m0, placementsBytes)])
    (by simp) (by simpa using (noWrap_iff.mp hF.pr.2))
    (hb.same.mono (by intro q h; simpa [R, SS_eq] using h))

/-- The frame plus the preserved loader slot is a well-formed environment. -/
theorem Facts.got_wf (hF : Facts m0) {d : MachineData} {o : Nat} (hb : B m0 o d)
    {ret : BitVec 64} :
    (frameEnv m0 d 5120 [(gotAddr "memset", 8)] (fun _ ↦ 0) ret).WF :=
  frame_wf ⟨Mapped.keeps (frame_mapped hF.stack (by decide)) hb.fr.kept, hF.fnw⟩
    (by intro x hx; simp only [List.mem_singleton] at hx; subst x
        exact ⟨Mapped.keeps (hF.got.mapped (by simp)) hb.fr.kept,
          (hF.got.1 "memset" (by simp)).2.1⟩)
    (List.pairwise_pair.mpr (apart_frame
      (hF.got.1 "memset" (by simp)).2.2.1 hF.stack.1 (by decide)).symm)

/-- Execute a GOT-reading block whose writes stay inside the frame. -/
theorem runGot (hF : Facts m0) {ds : List Directive} {kk : Nat} {Sy1 : SState} {x : Exit}
    {st : MachineState} {o' : Nat} {ret : BitVec 64} {Q : MachineState → Prop}
    (hk : ds.IsInfixAt Host.prog kk) (hx : exec ds gotS = some (Sy1, x))
    (hret : ∀ l, x = .call l → ret = (Host.addrOf (kk + ds.length)).toBitVec)
    (hpc : st.pc = Host.addrOf kk) (hb : B m0 8 st.data) (hok : MidOk 5120 o' slots Sy1 = true)
    (hw : ∀ w ∈ Sy1.mem, w.r = 0 ∧ w.off + w.n ≤ 5120)
    (cont : ∀ st', Match (frameEnv m0 st.data 5120 [(gotAddr "memset", 8)] (fun _ ↦ 0) ret)
        Sy1 st'.data →
      PcOk (frameEnv m0 st.data 5120 [(gotAddr "memset", 8)] (fun _ ↦ 0) ret)
        x (Host.addrOf (kk + ds.length)) st' →
      B m0 o' st'.data → Eventually (step1 Host.exe) Q st') :
    Eventually (step1 Host.exe) Q st := by
  have hwf := hF.got_wf (ret := ret) hb
  have hm : Match (frameEnv m0 st.data 5120 [(gotAddr "memset", 8)] (fun _ ↦ 0) ret)
      gotS st.data := by
    apply Match.withKnownBytes
    · exact match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb.fr.rsp_eval, trivial⟩ trivial trivial
        ⟨by simp [Sym.eval, Env.base, gotAddr], trivial⟩
    · intro i hi
      simpa [Sym.eval, Env.base, frameEnv] using
        (hF.got_bytes hb "memset" (by simp) i hi).trans (hF.got.byte (by simp) hi)
  exact exec_at hk hx hwf hret hpc hm fun st' hm' hpc' ↦
    cont st' hm' hpc' (hb.of_block_frame hF.stack (by decide) hwf hm' hok slots_le hw)

/-- **A block of the frame alone** keeps the body. -/
theorem run0 (hF : Facts m0) {ds : List Directive} {kk : Nat} {Sy1 : SState} {x : Exit}
    {st : MachineState} {o' : Nat} {ret : BitVec 64} {Q : MachineState → Prop}
    (hk : ds.IsInfixAt Host.prog kk) (hx : exec ds bodyS = some (Sy1, x))
    (hret : ∀ l, x = .call l → ret = (Host.addrOf (kk + ds.length)).toBitVec)
    (hpc : st.pc = Host.addrOf kk) (hb : B m0 8 st.data) (hok : MidOk 5120 o' slots Sy1 = true)
    (cont : ∀ st', Match (frameEnv m0 st.data 5120 [] (fun _ ↦ 0) ret) Sy1 st'.data →
      PcOk (frameEnv m0 st.data 5120 [] (fun _ ↦ 0) ret) x (Host.addrOf (kk + ds.length)) st' →
      B m0 o' st'.data → Eventually (step1 Host.exe) Q st') :
    Eventually (step1 Host.exe) Q st := by
  have hwf := fr_wf0 (vars := fun _ ↦ 0) (ret := ret) hb hF.stack (by decide)
  exact exec_at hk hx hwf hret hpc (match0 hb) fun st' hm' hpc' ↦
    cont st' hm' hpc' (hb.of_block0 hF.stack (by decide) hm' hok slots_le)

/-- **A block of registers only**: the body, memory kept. -/
theorem step0 (hF : Facts m0) {ds : List Directive} {kk : Nat} {Sy1 : SState} {x : Exit}
    {st : MachineState} {Q : MachineState → Prop} (hk : ds.IsInfixAt Host.prog kk)
    (hx : exec ds bodyS = some (Sy1, x))
    (hret : ∀ l, x = .call l → (0 : BitVec 64) = (Host.addrOf (kk + ds.length)).toBitVec)
    (hpc : st.pc = Host.addrOf kk) (hb : B m0 8 st.data)
    (hok : MidOk 5120 8 slots Sy1 = true) (hmem : Sy1.mem = [])
    (cont : ∀ st', Match (frameEnv m0 st.data 5120 [] (fun _ ↦ 0) 0) Sy1 st'.data →
      PcOk (frameEnv m0 st.data 5120 [] (fun _ ↦ 0) 0) x (Host.addrOf (kk + ds.length)) st' →
      B m0 8 st'.data → st'.data.dmem = st.data.dmem → Eventually (step1 Host.exe) Q st') :
    Eventually (step1 Host.exe) Q st :=
  run0 hF hk hx hret hpc hb hok fun st' hm' hpc' hb' ↦
    cont st' hm' hpc' hb' (hm'.dmem_eq (fr_wf0 hb hF.stack (by decide)) hmem)

/-- **A block reading regions named by aliases**: the body, memory kept. -/
theorem stepR {ds : List Directive} {kk : Nat} {Sy0 Sy1 : SState} {x : Exit}
    {st : MachineState} {rs : List (BitVec 64 × Nat)} {Q : MachineState → Prop}
    (hk : ds.IsInfixAt Host.prog kk) (hx : exec ds Sy0 = some (Sy1, x))
    (hret : ∀ l, x = .call l → (0 : BitVec 64) = (Host.addrOf (kk + ds.length)).toBitVec)
    (hpc : st.pc = Host.addrOf kk) (hb : B m0 8 st.data)
    (hwf : (Env.ofMachine st.data rs (fun _ ↦ 0) 0).WF)
    (hm : Match (Env.ofMachine st.data rs (fun _ ↦ 0) 0) Sy0 st.data)
    (hok : AOk slots Sy1 = true) (hmem : Sy1.mem = [])
    (cont : ∀ st', Match (Env.ofMachine st.data rs (fun _ ↦ 0) 0) Sy1 st'.data →
      PcOk (Env.ofMachine st.data rs (fun _ ↦ 0) 0) x (Host.addrOf (kk + ds.length)) st' →
      B m0 8 st'.data → st'.data.dmem = st.data.dmem → Eventually (step1 Host.exe) Q st') :
    Eventually (step1 Host.exe) Q st :=
  exec_at hk hx hwf hret hpc hm fun st' hm' hpc' ↦
    cont st' hm' hpc' (hb.of_read' hwf hm' hok hmem) (hm'.dmem_eq hwf hmem)

end

end NativeRustcVmX64.Layout.PlacementsOf
