module

public import NativeRustcVmX64.Whir.Common
public import NativeRustcVmX64.Spec.Whir
public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Transcript.Glue
public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Got

/-!
# `each_row`'s frame (x86-64)

Both `each_row`s push the six callee-saved registers, keep an `F`-byte frame below the entry's RSP
`m0` (the call slot, the locals, the pushes: `stackBelow m0 F`, `fb`), read `A` bytes of stack
arguments above the return address and change no memory but their stack (`N` bytes) and their
outputs `outs`. A block runs in `envE m0 m F A' rest`: region 0 the frame, the return address and
`A' ≤ A` bytes of arguments (`A' = 0` where the block reads an input, which need not be apart from
the arguments), then the inputs `rest`.

`Fr m0 F N slots outs o m`: RSP at the frame's offset `o` (`8` in the body, `0` at a call), the
pushed registers in their slots, memory as at the entry but in the stack and the outputs, every
mapped byte kept. The bodies keep locals in the frame below offset `lo` and from `hi` on, and let
the callees and the loop write the frame's bytes in `[lo, hi)` and the call slot and the stack
below the frame: `Hit`. A step changing memory in `Hit` only keeps `Fr` (`Fr.step`) and the locals
(`keep_frame`); a block's writes there (`hit_of_block`), a callee's (`hit_of_call`) are such
steps. The prologue makes `Fr` (`Fr.ofPrologue`), the epilogue returns with the entry's registers
(`Fr.exit`).
-/

namespace NativeRustcVmX64.Whir.EachRow

open NativeRustcX64 NativeRustcX64.Sym
open NativeRustcVmX64.Arrays (SlotsAt slot_load)

@[expose] public section

/-- A block's environment: region 0 the frame, the return address and `A` bytes of stack
arguments, then `rest`. -/
abbrev envE (m0 m : MachineData) (F A : Nat) (rest : List (BitVec 64 × Nat))
    (vars : Nat → BitVec 64 := fun _ ↦ 0) (ret : BitVec 64 := 0) : Env :=
  Env.ofMachine m ((stackBelow m0 F, F + 8 + A) :: rest) vars ret

/-- The layout: the stack, the frame within it, the `A` bytes of arguments mapped and not
wrapping. -/
structure Lay (m0 : MachineData) (F A N : Nat) : Prop where
  ok : StackOk m0 N
  le : F ≤ N
  f8 : 8 ≤ F
  args : Mapped m0.dmem (rspOf m0 + 8#64) A
  top : (rspOf m0).toNat + 8 + A ≤ 2 ^ 64

/-- The bytes a body's steps may change: the frame's `[lo, hi)`, the call slot and the stack below
the frame. -/
def Hit (m0 : MachineData) (F N lo hi : Nat) (q : BitVec 64) : Prop :=
  InRange (stackBelow m0 F + BitVec.ofNat 64 lo) (hi - lo) q ∨
    InRange (stackBelow m0 N) (N - F + 8) q

/-- **Between the prologue and the epilogue**: RSP at the frame's offset `o`, the pushed registers
in their slots, memory as at the entry but in the stack and the outputs, every mapped byte. -/
structure Fr (m0 : MachineData) (F N : Nat) (slots : List (Nat × Reg64))
    (outs : BitVec 64 → Prop) (o : Nat) (m : MachineData) : Prop where
  rsp : rspOf m = stackBelow m0 F + BitVec.ofNat 64 o
  slots : SlotsAt m.dmem (stackBelow m0 F) m0 slots
  same : SameOutside m0.dmem m.dmem (fun q ↦ InRange (stackBelow m0 N) N q ∨ outs q)
  kept : Kept m0.dmem m.dmem

/-- The ordinary frame plus a read-only loader slot. -/
def gotFrameS (F A : Nat) (l : Label) : SState :=
  (init [F + 8 + A, 8] [(.rsp, .ptr 0 8)] [] [] [(.gotSlot l, 1, 0)]).withKnownBytes
    1 0 8 (.label l)

end

public section

variable {m0 : MachineData} {F A N lo hi : Nat}

/-! ## Addresses -/

theorem Lay.sp (h : Lay m0 F A N) : N ≤ (rspOf m0).toNat := h.ok.1

theorem Lay.base (h : Lay m0 F A N) : (stackBelow m0 F).toNat = (rspOf m0).toNat - F :=
  NativeRustcVmX64.Field.stackBelow_toNat' (by have := h.sp; have := h.le; omega)

theorem Lay.baseN (h : Lay m0 F A N) : (stackBelow m0 N).toNat = (rspOf m0).toNat - N :=
  NativeRustcVmX64.Field.stackBelow_toNat' h.sp

/-- Region 0's byte `o` as a number. -/
theorem Lay.addr (h : Lay m0 F A N) {o : Nat} (ho : o < F + 8 + A) :
    (stackBelow m0 F + BitVec.ofNat 64 o).toNat = (rspOf m0).toNat - F + o := by
  have := h.top; have := h.sp; have := h.le
  rw [toNat_add_ofNat _ _ (by rw [h.base]; omega), h.base]

theorem Lay.noWrap0 (h : Lay m0 F A N) {A' : Nat} (hA : A' ≤ A) :
    NoWrap (stackBelow m0 F) (F + 8 + A') := by
  have := h.top; have := h.sp; have := h.le
  unfold NoWrap
  rw [h.base]
  omega

/-- Region 0's bytes are mapped at the entry. -/
theorem Lay.mapped0 (h : Lay m0 F A N) : Mapped m0.dmem (stackBelow m0 F) (F + 8 + A) := by
  have := h.top; have := h.sp; have := h.le
  have hs := (rspOf m0).isLt
  intro i hi
  by_cases hi' : i < F + 8
  · have := h.ok.2.2 (N - F + i) (by omega)
    rwa [show rspOf m0 - BitVec.ofNat 64 N + BitVec.ofNat 64 (N - F + i) =
      stackBelow m0 F + BitVec.ofNat 64 i by
        apply BitVec.eq_of_toNat_eq
        have hN : (rspOf m0 - BitVec.ofNat 64 N).toNat = (rspOf m0).toNat - N := h.baseN
        rw [toNat_add_ofNat _ _ (by rw [hN]; omega), hN, toNat_add_ofNat _ _ (by rw [h.base]; omega),
          h.base]
        omega] at this
  · obtain ⟨j, rfl⟩ : ∃ j, i = F + 8 + j := ⟨i - (F + 8), by omega⟩
    have := h.args j (by omega)
    rwa [show rspOf m0 + 8#64 + BitVec.ofNat 64 j = stackBelow m0 F + BitVec.ofNat 64 (F + 8 + j)
      by rw [Nat.add_assoc, NativeRustcVmX64.Field.frame_add, BitVec.ofNat_add, BitVec.add_assoc]]
      at this

/-- **A block's environment is well formed**: region 0 kept mapped, the inputs mapped, not
wrapping, all apart. -/
theorem envE_wf (h : Lay m0 F A N) {A' : Nat} (hA : A' ≤ A) {m : MachineData}
    (hk : Kept m0.dmem m.dmem) {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64}
    (hrest : ∀ x ∈ rest, Mapped m.dmem x.1 x.2 ∧ NoWrap x.1 x.2)
    (hap : ((stackBelow m0 F, F + 8 + A') :: rest).Pairwise fun x y ↦ Apart x.1 x.2 y.1 y.2) :
    (envE m0 m F A' rest vars ret).WF where
  noWrap r b k hb := by
    cases r with
    | zero => cases hb; exact h.noWrap0 hA
    | succ r => exact (hrest _ (List.mem_of_getElem? hb)).2
  mapped r b k hb := by
    cases r with
    | zero =>
      cases hb
      exact fun i hi ↦ hk _ (h.mapped0 i (by omega))
    | succ r => exact (hrest _ (List.mem_of_getElem? hb)).1
  disjoint r r' b b' k k' hne hb hb' := by
    have := List.pairwise_iff_getElem.mp hap
    simp only [Env.ofMachine_regions] at hb hb'
    obtain ⟨hr, hbr⟩ := List.getElem?_eq_some_iff.mp hb
    obtain ⟨hr', hbr'⟩ := List.getElem?_eq_some_iff.mp hb'
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := this r r' hr hr' h
      rw [hbr, hbr'] at this
      unfold Apart at this
      exact this
    · have := this r' r hr' hr h
      rw [hbr, hbr'] at this
      unfold Apart at this
      dsimp only at this
      omega

/-- An input apart from the stack and the return address is apart from region 0 without the
arguments. -/
theorem Lay.apart0 (h : Lay m0 F A N) {a : BitVec 64} {n : Nat} (hin : OffStack m0 a n N) :
    Apart (stackBelow m0 F) (F + 8) a n := by
  have := h.sp; have := h.le
  have hb := h.base; have hbN := h.baseN
  unfold OffStack Apart at *
  rw [hbN] at hin
  rw [hb]
  omega

theorem eval_ptr0 [Labels] {m : MachineData} {A' : Nat} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} (o : Nat) :
    (Sym.ptr 0 (o : Int)).eval (envE m0 m F A' rest vars ret) =
      stackBelow m0 F + BitVec.ofNat 64 o := by
  show (envE m0 m F A' rest vars ret).base 0 + BitVec.ofInt 64 (o : Int) = _
  rw [BitVec.ofInt_natCast]
  rfl

/-! ## `Hit` -/

/-- `Hit` as numbers. -/
theorem Lay.hit_iff (h : Lay m0 F A N) (hlh : lo ≤ hi) (hhi : hi ≤ F) {q : BitVec 64} :
    Hit m0 F N lo hi q ↔
      ((rspOf m0).toNat - F + lo ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - F + hi) ∨
        ((rspOf m0).toNat - N ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - F + 8) := by
  have := h.top; have := h.sp; have := h.le
  have hb := h.base; have hbN := h.baseN
  have e1 : (stackBelow m0 F + BitVec.ofNat 64 lo).toNat = (rspOf m0).toNat - F + lo := by
    rw [toNat_add_ofNat _ _ (by rw [hb]; omega), hb]
  unfold Hit
  rw [Sym.inRange_iff (x := stackBelow m0 F + BitVec.ofNat 64 lo) (by rw [e1]; omega),
    Sym.inRange_iff (x := stackBelow m0 N) (by rw [hbN]; omega), e1, hbN]
  constructor <;> intro h' <;> omega

/-- The stack as numbers. -/
theorem Lay.stack_iff (h : Lay m0 F A N) {q : BitVec 64} :
    InRange (stackBelow m0 N) N q ↔ (rspOf m0).toNat - N ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat :=
  by
  have := h.sp
  have hbN := h.baseN
  have := (rspOf m0).isLt
  rw [Sym.inRange_iff (x := stackBelow m0 N) (by rw [hbN]; omega), hbN]
  constructor <;> intro h' <;> omega

/-- `Hit` is in the stack, for `hi ≤ F`. -/
theorem Lay.hit_stack (h : Lay m0 F A N) (hlh : lo ≤ hi) (hhi : hi ≤ F) {q : BitVec 64}
    (hq : Hit m0 F N lo hi q) : InRange (stackBelow m0 N) N q := by
  rw [h.hit_iff hlh hhi] at hq
  rw [h.stack_iff]
  have := h.sp; have := h.le; have := h.f8
  omega

/-- A byte of region 0 from offset `8` outside `[lo, hi)` is not hit. -/
theorem Lay.not_hit (h : Lay m0 F A N) (hlh : lo ≤ hi) (hhi : hi ≤ F) {o : Nat}
    (h8 : 8 ≤ o) (ho : o < lo ∨ (hi ≤ o ∧ o < F + 8 + A)) :
    ¬Hit m0 F N lo hi (stackBelow m0 F + BitVec.ofNat 64 o) := by
  rw [h.hit_iff hlh hhi, h.addr (by omega)]
  have := h.sp; have := h.le
  omega

/-- **A step keeping memory**, RSP at the frame's offset `o'`. -/
theorem Fr.ofMem {slots : List (Nat × Reg64)} {outs : BitVec 64 → Prop} {o o' : Nat}
    {m m' : MachineData} (h : Fr m0 F N slots outs o m) (hd : m'.dmem = m.dmem)
    (hsp : rspOf m' = stackBelow m0 F + BitVec.ofNat 64 o') : Fr m0 F N slots outs o' m' where
  rsp := hsp
  slots := by rw [hd]; exact h.slots
  same q hq := by rw [hd]; exact h.same q hq
  kept p hp := by rw [hd]; exact h.kept p hp

/-- RSP in a body, as region 0's offset `o`. -/
theorem Fr.match_rsp [Labels] {slots : List (Nat × Reg64)} {outs : BitVec 64 → Prop} {o : Nat}
    {m : MachineData} (h : Fr m0 F N slots outs o m) {A' : Nat} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} :
    m.regs.get64 .rsp = (Sym.ptr 0 (o : Int)).eval (envE m0 m F A' rest vars ret) := by
  rw [eval_ptr0]
  exact h.rsp

/-- Loader bytes preserved by the row body's declared writable footprint. -/
theorem Fr.got_bytes [Labels] {slots : List (Nat × Reg64)} {outs : BitVec 64 → Prop}
    {o : Nat} {m : MachineData} {areas : List (BitVec 64 × Nat)} {symbols : List Label}
    (h : Fr m0 F N slots outs o m) (hl : Lay m0 F A N)
    (hg : GotAt m0 N areas symbols) (hnw : ∀ a ∈ areas, NoWrap a.1 a.2)
    (hout : ∀ q, outs q → ∃ a ∈ areas, InRange a.1 a.2 q) :
    ∀ l ∈ symbols, ∀ i < 8, m.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
      m0.dmem.get? (gotAddr l + BitVec.ofNat 64 i) :=
  hg.unchanged hl.ok hnw (fun p hp => h.same p (fun h => hp (h.elim Or.inl
    (fun h => Or.inr (hout p h)))))

/-- An indirect call reads its actual loader slot, disjoint also from stack arguments. -/
theorem Fr.got_env [Labels] {slots : List (Nat × Reg64)} {outs : BitVec 64 → Prop}
    {m : MachineData} {areas : List (BitVec 64 × Nat)} {symbols : List Label} {l : Label}
    (h : Fr m0 F N slots outs 8 m) (hl : Lay m0 F A N)
    (hg : GotAt m0 N areas symbols) (hnw : ∀ a ∈ areas, NoWrap a.1 a.2)
    (hout : ∀ q, outs q → ∃ a ∈ areas, InRange a.1 a.2 q)
    (hargs : (rspOf m0 + 8#64, A) ∈ areas) (hlmem : l ∈ symbols) (ret : BitVec 64) :
    (envE m0 m F A [(gotAddr l, 8)] (fun _ => 0) ret).WF ∧
    Match (envE m0 m F A [(gotAddr l, 8)] (fun _ => 0) ret) (gotFrameS F A l) m := by
  have hg0 := hg.1 l hlmem
  have ha := hg0.2.2.2 _ hargs
  have hs : Apart (gotAddr l) 8 (stackBelow m0 N) (N + 8) := hg0.2.2.1
  have hap : Apart (stackBelow m0 F) (F + 8 + A) (gotAddr l) 8 := by
    by_cases hA : A = 0
    · subst A
      unfold Apart at hs ⊢
      rw [hl.baseN] at hs
      rw [hl.base]
      have := hl.sp
      have := hl.le
      omega
    · have harg : (rspOf m0 + 8#64).toNat = (rspOf m0).toNat + 8 :=
        toNat_add_ofNat _ _ (by have := hl.top; omega)
      unfold Apart at ha hs ⊢
      change (gotAddr l).toNat + 8 ≤ (rspOf m0 + 8#64).toNat ∨
        (rspOf m0 + 8#64).toNat + A ≤ (gotAddr l).toNat at ha
      rw [hl.baseN] at hs
      rw [harg] at ha
      rw [hl.base]
      have := hl.sp
      have := hl.le
      omega
  refine ⟨envE_wf hl le_rfl h.kept (fun a ha => by
      simp only [List.mem_singleton] at ha
      subst a
      exact ⟨fun i hi => h.kept _ (hg.mapped hlmem i hi), hg0.2.1⟩)
      (List.pairwise_pair.mpr hap), ?_⟩
  have hm : Match (envE m0 m F A [(gotAddr l, 8)] (fun _ => 0) ret)
      (init [F + 8 + A, 8] [(.rsp, .ptr 0 8)] [] [] [(.gotSlot l, 1, 0)]) m :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨h.match_rsp, trivial⟩ trivial trivial
      ⟨(BitVec.add_zero _).symm, trivial⟩
  apply hm.withKnownBytes
  intro i hi
  simpa [Env.base, Sym.eval] using
    (h.got_bytes hl hg hnw hout l hlmem i hi).trans (hg.byte hlmem hi)

/-- The callee's protected areas are subranges of the row body's stack or input areas. -/
theorem Fr.got_callee [Labels] {slots : List (Nat × Reg64)} {outs : BitVec 64 → Prop}
    {m : MachineData} {areas areas' : List (BitVec 64 × Nat)} {symbols : List Label} {N' : Nat}
    (h : Fr m0 F N slots outs 0 m) (hl : Lay m0 F A N)
    (hg : GotAt m0 N areas symbols) (hnw : ∀ a ∈ areas, NoWrap a.1 a.2)
    (hout : ∀ q, outs q → ∃ a ∈ areas, InRange a.1 a.2 q) (hle : F + N' ≤ N)
    (hcover : ∀ a ∈ areas', ∃ b ∈ (stackBelow m0 N, N + 8) :: areas,
      b.1.toNat ≤ a.1.toNat ∧ a.1.toNat + a.2 ≤ b.1.toNat + b.2) :
    GotAt m N' areas' symbols := by
  have hsp : rspOf m = stackBelow m0 F := by simpa using h.rsp
  have hd : (stackBelow m N').toNat = (rspOf m0).toNat - F - N' := by
    rw [NativeRustcVmX64.Field.stackBelow_toNat' (by rw [hsp, hl.base]; have := hl.sp; omega),
      hsp, hl.base]
  apply NativeRustcVmX64.GotAt.callee hg (h.got_bytes hl hg hnw hout) _ _ hcover <;>
    rw [hd, hl.baseN] <;> have := hl.sp <;> omega

/-- **A block without writes**, RSP at offset `o'` after it. -/
theorem Fr.ofBlock [Labels] {slots : List (Nat × Reg64)} {outs : BitVec 64 → Prop} {o o' : Nat}
    {m m' : MachineData} (h : Fr m0 F N slots outs o m) {A' : Nat}
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (envE m0 m F A' rest vars ret).WF) (hm : Match (envE m0 m F A' rest vars ret) S m')
    (hmem : S.mem = []) (hsp : S.reg .rsp = some (.ptr 0 (o' : Int))) :
    Fr m0 F N slots outs o' m' :=
  h.ofMem (hm.dmem_eq hwf hmem) (by
    show m'.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp, eval_ptr0])

/-- **A step changing memory in `Hit`** keeps the frame, its slots from `8` and outside
`[lo, hi)`. -/
theorem Fr.step {slots : List (Nat × Reg64)} {outs : BitVec 64 → Prop} {o o' : Nat}
    {m m' : MachineData} (hl : Lay m0 F A N) (hlh : lo ≤ hi) (hhi : hi ≤ F)
    (h : Fr m0 F N slots outs o m) (hsp : rspOf m' = stackBelow m0 F + BitVec.ofNat 64 o')
    (hk : Kept m.dmem m'.dmem) (hs : SameOutside m.dmem m'.dmem (Hit m0 F N lo hi))
    (hsl : ∀ p ∈ slots, 8 ≤ p.1 ∧ (p.1 + 8 ≤ lo ∨ (hi ≤ p.1 ∧ p.1 + 8 ≤ F))) :
    Fr m0 F N slots outs o' m' where
  rsp := hsp
  slots p hp i hi' := by
    rw [List.length_map, List.length_range] at hi'
    rw [hs _ ?_]
    · exact h.slots p hp i (by simpa using hi')
    · rw [addr_add]
      have := hsl p hp
      exact hl.not_hit hlh hhi (by omega) (by omega)
  same q hq := by
    rw [hs q fun h' ↦ hq (.inl (hl.hit_stack hlh hhi h'))]
    exact h.same q hq
  kept p hp := hk p (h.kept p hp)

/-- **A step changing memory in `R`**, the stack and the outputs, none of the slots. -/
theorem Fr.stepR {slots : List (Nat × Reg64)} {outs : BitVec 64 → Prop} {o o' : Nat}
    {m m' : MachineData} {R : BitVec 64 → Prop} (h : Fr m0 F N slots outs o m)
    (hsp : rspOf m' = stackBelow m0 F + BitVec.ofNat 64 o')
    (hk : Kept m.dmem m'.dmem) (hs : SameOutside m.dmem m'.dmem R)
    (hR : ∀ q, R q → InRange (stackBelow m0 N) N q ∨ outs q)
    (hsl : ∀ p ∈ slots, ∀ i < 8, ¬R (stackBelow m0 F + BitVec.ofNat 64 (p.1 + i))) :
    Fr m0 F N slots outs o' m' where
  rsp := hsp
  slots p hp i hi' := by
    rw [List.length_map, List.length_range] at hi'
    rw [hs _ ?_]
    · exact h.slots p hp i (by simpa using hi')
    · rw [addr_add]
      exact hsl p hp i (by simpa using hi')
  same q hq := by
    rw [hs q fun h' ↦ hq (hR q h')]
    exact h.same q hq
  kept p hp := hk p (h.kept p hp)

/-- **Bytes of region 0 no change touches.** -/
theorem keep_frameR {d d' : DataMem} {R : BitVec 64 → Prop} (hs : SameOutside d d' R) {o : Nat}
    {bs : List UInt8} (hR : ∀ i < bs.length, ¬R (stackBelow m0 F + BitVec.ofNat 64 (o + i)))
    (hb : NativeRustcVm.BytesAt d (stackBelow m0 F + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt d' (stackBelow m0 F + BitVec.ofNat 64 o) bs :=
  fun i hi' ↦ by
    rw [hs _ ?_]
    · exact hb i hi'
    · rw [addr_add]
      exact hR i hi'

/-- **Bytes of region 0 from `8`, outside `[lo, hi)`**, are kept by a step changing memory in
`Hit`. -/
theorem keep_frame (hl : Lay m0 F A N) (hlh : lo ≤ hi) (hhi : hi ≤ F) {d d' : DataMem}
    (hs : SameOutside d d' (Hit m0 F N lo hi)) {o : Nat} {bs : List UInt8} (h8 : 8 ≤ o)
    (hle : o + bs.length ≤ lo ∨ (hi ≤ o ∧ o + bs.length ≤ F + 8 + A))
    (hb : NativeRustcVm.BytesAt d (stackBelow m0 F + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt d' (stackBelow m0 F + BitVec.ofNat 64 o) bs :=
  fun i hi' ↦ by
    rw [hs _ ?_]
    · exact hb i hi'
    · rw [addr_add]
      exact hl.not_hit hlh hhi (by omega) (by omega)

/-- **A block's writes** in region 0, in the call slot or within `[lo, hi)`. -/
theorem hit_of_block [Labels] (hl : Lay m0 F A N) (hlh : lo ≤ hi) (hhi : hi ≤ F)
    {A' : Nat} {m m' : MachineData} {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hm : Match (envE m0 m F A' rest vars ret) S m')
    (hwf : (envE m0 m F A' rest vars ret).WF)
    (hS : S.mem.all (fun w ↦ w.r == 0 &&
      (decide (w.off + w.n ≤ 8) || (decide (lo ≤ w.off) && decide (w.off + w.n ≤ hi)))) = true) :
    SameOutside m.dmem m'.dmem (Hit m0 F N lo hi) := by
  intro q hq
  refine hm.get?_mem0 hwf fun ⟨w, hw, b, sz, hb, h1, h2⟩ ↦ hq ?_
  have := List.all_eq_true.mp hS w hw
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  obtain ⟨hr, hoff⟩ := this
  rw [hr] at hb
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  rw [hl.base] at h1 h2
  rw [hl.hit_iff hlh hhi]
  have := hl.sp; have := hl.le
  omega

/-- **A callee's change** of `n` bytes at offset `o ∈ [lo, hi)` of the frame and of its stack,
`N'` bytes below the frame, called with RSP at the frame's base. -/
theorem hit_of_call (hl : Lay m0 F A N) (hlh : lo ≤ hi) (hhi : hi ≤ F) {mc m' : MachineData}
    {N' o n : Nat} (hsp : rspOf mc = stackBelow m0 F) (hN' : F + N' ≤ N) (ho : lo ≤ o)
    (hon : o + n ≤ hi)
    (hs : SameOutside mc.dmem m'.dmem (fun q ↦
      NativeRustcVm.InAny [⟨stackBelow m0 F + BitVec.ofNat 64 o, n⟩] q ∨
        InRange (stackBelow mc N') N' q)) :
    SameOutside mc.dmem m'.dmem (Hit m0 F N lo hi) := by
  intro q hq
  refine hs q fun h' ↦ hq ?_
  have := hl.sp; have := hl.le; have := hl.top
  have hb := hl.base
  rw [hl.hit_iff hlh hhi]
  rcases h' with ⟨r, hr, hq'⟩ | hq'
  · simp only [List.mem_singleton] at hr
    subst hr
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : InRange (stackBelow m0 F + BitVec.ofNat 64 o) 0 q := hq'
      unfold InRange at h0
      omega
    have e := hl.addr (o := o) (by omega)
    have hq'' : InRange (stackBelow m0 F + BitVec.ofNat 64 o) n q := hq'
    rw [Sym.inRange_iff (x := stackBelow m0 F + BitVec.ofNat 64 o) (by rw [e]; omega), e] at hq''
    omega
  · have h1 : (BitVec.ofNat 64 N').toNat = N' := NativeRustcVm.toNat_ofNat_of_lt (by omega)
    have hsb : (stackBelow mc N').toNat = (rspOf m0).toNat - F - N' := by
      show (rspOf mc - BitVec.ofNat 64 N').toNat = _
      rw [hsp, toNat_sub_of_le _ _ (by rw [h1, hb]; omega), h1, hb]
    rw [Sym.inRange_iff (x := stackBelow mc N') (by rw [hsb]; omega), hsb] at hq'
    omega

/-- A callee's change of its stack only. -/
theorem hit_of_stack (hl : Lay m0 F A N) (hlh : lo ≤ hi) (hhi : hi ≤ F) {mc m' : MachineData}
    {N' : Nat} (hsp : rspOf mc = stackBelow m0 F) (hN' : F + N' ≤ N)
    (hs : SameOutside mc.dmem m'.dmem (InRange (stackBelow mc N') N')) :
    SameOutside mc.dmem m'.dmem (Hit m0 F N lo hi) :=
  hit_of_call hl hlh hhi (o := lo) (n := 0) hsp hN' le_rfl (by omega)
    fun q hq ↦ hs q fun h' ↦ hq (.inr h')

/-- **A callee returned**: called with RSP at the frame's base, back with RSP 8 above, its
changes in `Hit`. -/
theorem Fr.call {slots : List (Nat × Reg64)} {outs : BitVec 64 → Prop} {mc m' : MachineData}
    (hl : Lay m0 F A N) (hlh : lo ≤ hi) (hhi : hi ≤ F) (h : Fr m0 F N slots outs 0 mc)
    (hr : rspOf m' = rspOf mc + 8#64) (hsv : Saved mc m')
    (hs : SameOutside mc.dmem m'.dmem (Hit m0 F N lo hi))
    (hsl : ∀ p ∈ slots, 8 ≤ p.1 ∧ (p.1 + 8 ≤ lo ∨ (hi ≤ p.1 ∧ p.1 + 8 ≤ F))) :
    Fr m0 F N slots outs 8 m' :=
  h.step hl hlh hhi (by rw [hr, h.rsp, BitVec.add_assoc]; rfl) hsv.2 hs hsl

/-- Bytes `memcpy` copied: a prefix of the source's. -/
theorem bytesAt_copy {d d' : DataMem} {a a' : BitVec 64} {n : Nat} {bs : List UInt8}
    (hc : NativeRustcVm.BytesAt d a (NativeRustcX64.bytesOf d' a' n)) (hb : NativeRustcVm.BytesAt d' a' bs)
    (hle : bs.length ≤ n) : NativeRustcVm.BytesAt d a bs := by
  intro i hi
  rw [hc i (by simp [NativeRustcX64.bytesOf]; omega)]
  have := hb i hi
  simp only [NativeRustcX64.bytesOf, List.getElem_map, List.getElem_range]
  rw [show d'.get? (a' + BitVec.ofNat 64 i) = some bs[i] from this]
  rfl

/-! ## Callees -/

/-- A callee's stack, below the frame, RSP at its base. -/
theorem Fr.stackOk {slots : List (Nat × Reg64)} {outs : BitVec 64 → Prop} {m : MachineData}
    (hl : Lay m0 F A N) (h : Fr m0 F N slots outs 0 m) {N' : Nat} (hle : F + N' ≤ N) :
    StackOk m N' :=
  Transcript.stackOk_callee hl.ok h.kept (by rw [h.rsp]; simp) hle

theorem Fr.rsp0 {slots : List (Nat × Reg64)} {outs : BitVec 64 → Prop} {m : MachineData}
    (h : Fr m0 F N slots outs 0 m) : rspOf m = stackBelow m0 F := by
  rw [h.rsp]; simp

/-- A callee's stack, as numbers. -/
theorem Fr.stackBelow_toNat {slots : List (Nat × Reg64)} {outs : BitVec 64 → Prop}
    {m : MachineData} (hl : Lay m0 F A N) (h : Fr m0 F N slots outs 0 m) {N' : Nat}
    (hle : F + N' ≤ N) : (stackBelow m N').toNat = (rspOf m0).toNat - F - N' := by
  have := hl.sp; have := hl.le
  have hb := hl.base
  have h1 : (BitVec.ofNat 64 N').toNat = N' := NativeRustcVm.toNat_ofNat_of_lt (by omega)
  show (rspOf m - BitVec.ofNat 64 N').toNat = _
  rw [h.rsp0, toNat_sub_of_le _ _ (by rw [h1, hb]; omega), h1, hb]

/-- **An output in the frame** for a callee using `N'` bytes of stack. -/
theorem Fr.whirIn_frame {slots : List (Nat × Reg64)} {outs : BitVec 64 → Prop} {m : MachineData}
    (hl : Lay m0 F A N) (h : Fr m0 F N slots outs 0 m) {o c N' : Nat} (h8 : 8 ≤ o)
    (hoc : o + c ≤ F) (hle : F + N' ≤ N) :
    WhirIn m (stackBelow m0 F + BitVec.ofNat 64 o) c N' := by
  have := hl.sp; have := hl.le; have := hl.top
  have hb := hl.base
  have e := hl.addr (o := o) (by omega)
  refine ⟨⟨fun i hi ↦ ?_, show _ + c ≤ _ by rw [e]; omega⟩, ?_⟩
  · rw [addr_add]
    exact h.kept _ (hl.mapped0 _ (by omega))
  · have h1 : (BitVec.ofNat 64 N').toNat = N' := NativeRustcVm.toNat_ofNat_of_lt (by omega)
    have hsb : (stackBelow m N').toNat = (rspOf m0).toNat - F - N' := by
      show (rspOf m - BitVec.ofNat 64 N').toNat = _
      rw [h.rsp0, toNat_sub_of_le _ _ (by rw [h1, hb]; omega), h1, hb]
    show _ ∨ _
    rw [hsb, e]
    omega

/-- **An input** of the entry, for a callee using `N'` bytes of stack. -/
theorem Fr.whirIn_input {slots : List (Nat × Reg64)} {outs : BitVec 64 → Prop} {m : MachineData}
    (hl : Lay m0 F A N) (h : Fr m0 F N slots outs 0 m) {a : BitVec 64} {n N' : Nat}
    (hin : WhirIn m0 a n N) (hle : F + N' ≤ N) : WhirIn m a n N' :=
  ⟨⟨fun i hi ↦ h.kept _ (hin.1.1 i hi), hin.1.2⟩,
    Transcript.apart_callee hin.2 h.rsp0 hl.sp hle⟩

/-- **An input's bytes** in a body: those of the entry, apart from the stack and the outputs. -/
theorem Fr.input_same {slots : List (Nat × Reg64)} {outs : BitVec 64 → Prop} {o : Nat}
    {m : MachineData} (hl : Lay m0 F A N) (h : Fr m0 F N slots outs o m) {a : BitVec 64} {n : Nat}
    (hin : WhirIn m0 a n N) (hout : ∀ i < n, ¬outs (a + BitVec.ofNat 64 i)) :
    ∀ i < n, m.dmem.get? (a + BitVec.ofNat 64 i) = m0.dmem.get? (a + BitVec.ofNat 64 i) :=
  fun i hi ↦ h.same _ fun h' ↦ h'.elim
    (NativeRustcVmX64.Arrays.not_inRange_of_apart
      (by have := hin.2; unfold OffStack at this; unfold Apart at this ⊢; omega) hin.1.2
      (by have := hl.sp; have := (rspOf m0).isLt; unfold NoWrap; rw [hl.baseN]; omega) hi)
    (hout i hi)

/-- **The arguments' bytes** in a body: those of the entry, apart from the outputs. -/
theorem Fr.args_same {slots : List (Nat × Reg64)} {outs : BitVec 64 → Prop} {o : Nat}
    {m : MachineData} (hl : Lay m0 F A N) (h : Fr m0 F N slots outs o m)
    (hout : ∀ i < A, ¬outs (rspOf m0 + 8#64 + BitVec.ofNat 64 i)) :
    ∀ i < A, m.dmem.get? (rspOf m0 + 8#64 + BitVec.ofNat 64 i) =
      m0.dmem.get? (rspOf m0 + 8#64 + BitVec.ofNat 64 i) := by
  intro i hi
  refine h.same _ fun h' ↦ h'.elim (fun hs ↦ ?_) (hout i hi)
  have := hl.sp; have := hl.top
  have e : rspOf m0 + 8#64 + BitVec.ofNat 64 i = rspOf m0 + BitVec.ofNat 64 (8 + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e, hl.stack_iff, toNat_add_ofNat _ _ (by omega)] at hs
  omega

/-- **A stack argument loaded** through region 0, where the arguments are kept. -/
theorem load_arg {m : MachineData} {A' : Nat} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} (i : Nat)
    (hs : ∀ j < 8, m.dmem.get? (rspOf m0 + 8#64 + BitVec.ofNat 64 (8 * i + j)) =
      m0.dmem.get? (rspOf m0 + 8#64 + BitVec.ofNat 64 (8 * i + j))) :
    (envE m0 m F A' rest vars ret).load 0 (F + 8 + 8 * i) 8 = stackArg m0 i := by
  rw [NativeRustcVmX64.Arrays.load8_eq]
  unfold stackArg
  show (NativeRustcVm.wordOf m.dmem (stackBelow m0 F + BitVec.ofNat 64 (F + 8 + 8 * i))).toBitVec = _
  rw [Nat.add_assoc, NativeRustcVmX64.Field.frame_add]
  refine congrArg UInt64.toBitVec (NativeRustcVm.wordOf_congr fun j hj ↦ ?_)
  have e : rspOf m0 + BitVec.ofNat 64 (8 + 8 * i) + BitVec.ofNat 64 j =
      rspOf m0 + 8#64 + BitVec.ofNat 64 (8 * i + j) := by
    rw [addr_add, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
  rw [e]
  exact hs j hj

/-! ## Prologue and epilogue -/

/-- **After the prologue**, at its call: a block from the entry, region 0's writes below `F`, the
slots written with the entry's registers, RSP at the frame's base. -/
theorem Fr.ofPrologue [Labels] {slots : List (Nat × Reg64)} {outs : BitVec 64 → Prop}
    {A' : Nat} {m : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hl : Lay m0 F A N) (hA : A' ≤ A) (hm : Match (envE m0 m0 F A' [] vars ret) S m)
    (hsp : S.reg .rsp = some (.ptr 0 0))
    (hw : ∀ p ∈ slots, p.1 + 8 ≤ F ∧ ∀ i < 8, findWrite 0 (p.1 + i) S.mem = some (.reg p.2, i))
    (hmem : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ F) : Fr m0 F N slots outs 0 m := by
  have hwf := envE_wf (m := m0) (vars := vars) (ret := ret) hl hA (fun _ h ↦ h)
    (fun _ h ↦ by cases h) (List.pairwise_singleton _ _)
  refine ⟨?_, fun p hp ↦ ?_, fun q hq ↦ ?_, hm.kept hwf⟩
  · show m.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp]
    show stackBelow m0 F + BitVec.ofInt 64 0 = _
    simp
  · exact hm.bytesAt_write (r := 0) rfl (by have := (hw p hp).1; omega) (hw p hp).2
  · refine hm.get?_mem0 hwf fun ⟨w, hwm, b, sz, hb, h1, h2⟩ ↦ hq (.inl ?_)
    obtain ⟨hr, hn⟩ := hmem w hwm
    rw [hr] at hb
    cases hb
    rw [hl.stack_iff]
    rw [hl.base] at h1 h2
    have := hl.sp; have := hl.le
    omega

/-- **The return address**, region 0's offset `F`, while its bytes are the entry's. -/
theorem load_ret {m : MachineData} {A' : Nat} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} (hl : Lay m0 F A N)
    (hsame : ∀ j < 8, m.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) =
      m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j)) :
    Int64.ofBitVec ((envE m0 m F A' rest vars ret).load 0 F 8) = retOf m0 := by
  have hget : ∀ j < 8, m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) =
      some ((m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j)).getD 0) := fun j hj ↦ by
    have := hl.mapped0 (F + j) (by omega)
    rw [NativeRustcVmX64.Field.frame_add] at this
    revert this
    cases m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) <;> simp
  have base0 : (envE m0 m F A' rest vars ret).base 0 = stackBelow m0 F := rfl
  rw [retOf, loadInt_of_get? _ _ 8 _ hget, Option.getD_some]
  unfold Env.load
  congr 3
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [base0, Env.ofMachine_mem0, NativeRustcVmX64.Field.frame_add, hsame j hj]

/-- **After the epilogue**: from a body, a block whose writes are in region 0 below `F`, restoring
each slot's register from the frame, every callee-saved register among the slots, RSP `8` above
the return address, ending in `ret`: back at the entry's return address, RSP 8 above the entry's,
the callee-saved registers the entry's, memory changed only in the stack and the outputs. -/
theorem Fr.exit [Labels] {slots : List (Nat × Reg64)} {outs : BitVec 64 → Prop} {A' : Nat}
    {m : MachineData} {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {S : SState} {st : MachineState} {next : Int64} (hl : Lay m0 F A N) (h : Fr m0 F N slots outs 8 m)
    (hwf : (envE m0 m F A' rest vars ret).WF)
    (hm : Match (envE m0 m F A' rest vars ret) S st.data)
    (hpc : PcOk (envE m0 m F A' rest vars ret) (.ret (.load 0 F 8)) next st)
    (hmem : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ F)
    (hrs : ∀ p ∈ slots, S.reg p.2 = some (.load 0 p.1 8))
    (hcs : ∀ r, calleeSaved r = true → ∃ p ∈ slots, p.2 = r)
    (hsp : S.reg .rsp = some (.ptr 0 ((F + 8 : Nat) : Int)))
    (hret : ∀ j < 8, ¬outs (rspOf m0 + BitVec.ofNat 64 j)) :
    st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ Saved m0 st.data ∧
      SameOutside m0.dmem st.data.dmem (fun q ↦ InRange (stackBelow m0 N) N q ∨ outs q) := by
  have hso : SameOutside m.dmem st.data.dmem (InRange (stackBelow m0 N) N) := fun q hq ↦
    hm.get?_mem0 hwf fun ⟨w, hwm, b, sz, hb, h1, h2⟩ ↦ hq (by
      obtain ⟨hr, hn⟩ := hmem w hwm
      rw [hr] at hb
      cases hb
      rw [hl.stack_iff]
      rw [hl.base] at h1 h2
      have := hl.sp; have := hl.le
      omega)
  refine ⟨?_, ?_, ⟨fun r hr ↦ ?_, fun p hp ↦ hm.kept hwf p (h.kept p hp)⟩, fun q hq ↦ ?_⟩
  · simp only [PcOk] at hpc
    rw [hpc]
    refine load_ret hl fun j hj ↦ h.same _ fun h' ↦ h'.elim (fun hs ↦ ?_) (hret j hj)
    rw [hl.stack_iff, toNat_add_ofNat _ _ (by have := hl.ok.2.1; omega)] at hs
    omega
  · show st.data.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp]
    exact NativeRustcVmX64.Field.frame_rsp F 8
  · obtain ⟨p, hp, rfl⟩ := hcs r hr
    show st.data.regs.get64 p.2 = _
    rw [hm.regs _ _ (hrs p hp)]
    exact slot_load (r := 0) h.slots (show (p.1, p.2) ∈ slots from hp)
  · rw [hso q fun h' ↦ hq (.inl h')]
    exact h.same q hq

end

end NativeRustcVmX64.Whir.EachRow
