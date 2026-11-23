module

public import NativeRustcVmArm.Ring.Frame
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVmArm.Layout.Common
public import NativeRustcVmArm.Spec.Bus

/-!
# The bus's proofs: what they share

Frames are `NativeRustcVmArm.Ring.Fr` (the entry's SP less `F`, the saved registers' slots, memory
as the entry's but in the stack and the outputs). Here:

- `env0`, `wf_env0`, `match_entry`: the entry's environment, region 0 the `F`-byte frame below SP.
- `Fr.readable`, `Fr.offStack`, `Fr.sliceOk`: an argument of the entry passed on to a callee.
- `Fr.bytes_eq`, `Fr.slice_eq`, `Fr.wordSlice_eq`: an argument's bytes unchanged in the frame.
- `changes_of_fr`: what the frame's `same` gives a contract's `Changes`.
-/

namespace NativeRustcVmArm.Bus

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring

public section

/-! ## The entry -/

/-- The entry's environment: region 0 the `F` bytes below SP. -/
@[expose] def env0 (m0 : MachineData) (F : Nat) (rs : List (BitVec 64 × Nat) := []) : Env :=
  Env.ofMachine m0 ((base m0 F, F) :: rs)

theorem base_aligned {m0 : MachineData} {F N : Nat} (hS : StackOk m0 N) (hF : F ≤ N)
    (h16 : F % 16 = 0) : (base m0 F).toNat % 16 = 0 := by
  rw [base_toNat (by have := hS.2.1; omega)]
  have := hS.1
  omega

theorem frame_mapped {m0 : MachineData} {F N : Nat} (hS : StackOk m0 N) (hF : F ≤ N) :
    NativeRustcVm.Mapped m0.dmem (base m0 F) F ∧ NativeRustcVm.NoWrap (base m0 F) F := by
  have hN := hS.2.1
  refine ⟨fun i hi ↦ ?_, base_noWrap (by omega)⟩
  rw [← base_add hF hN, NativeRustcVm.addr_add_add]
  exact hS.2.2 _ (by omega)

/-- The `N` bytes of stack do not wrap. -/
theorem stack_noWrap {m : MachineData} {N : Nat} (hS : StackOk m N) : NoWrap (stackBelow m N) N :=
  base_noWrap hS.2.1

/-- A byte of a region apart from another is not one of the other's. -/
theorem not_inRange_of_apart {a b : BitVec 64} {n n' j : Nat} (hA : Apart a n b n')
    (hna : NoWrap a n) (hnb : NoWrap b n') (hj : j < n) : ¬InRange b n' (a + BitVec.ofNat 64 j) := by
  unfold Apart NoWrap at *
  rw [Sym.inRange_iff hnb, NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

/-- The state `exec ds S` ends in (`S` where it fails). -/
@[expose] def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

/-- The frame alone: a well-formed environment. -/
theorem wf_env0 {m0 : MachineData} {F N : Nat} (hS : StackOk m0 N) (hF : F ≤ N) :
    (env0 m0 F).WF :=
  Env.wf_of ⟨frame_mapped hS hF, trivial⟩ (List.pairwise_singleton _ _)

theorem env0_sp [Labels] {m0 : MachineData} {F : Nat} (rs : List (BitVec 64 × Nat)) :
    m0.regs.SP.toBitVec = (Sym.ptr 0 (F : Int)).eval (env0 m0 F rs) := by
  simp only [Sym.eval, env0, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
    Option.getD_some]
  rw [BitVec.ofInt_natCast]
  exact base_add_eq.symm

/-- **The entry's match**: region 0 the `F`-byte frame below SP, SP its end. -/
theorem match_entry [Labels] {m0 : MachineData} {F N : Nat} (hS : StackOk m0 N) (hF : F ≤ N)
    (h16 : F % 16 = 0) : Match (env0 m0 F) (init [(F, true)] (.ptr 0 (F : Int))) m0 :=
  match_ofMachine (sregions := [(F, true)]) (regions := [(base m0 F, F)])
    ⟨rfl, fun _ ↦ base_aligned hS hF h16, trivial⟩ (env0_sp []) trivial trivial trivial trivial

/-- **A state in the frame**: region 0 the frame, SP its base. -/
theorem match_frame [Labels] {m0 m : MachineData} {F N : Nat} (hS : StackOk m0 N) (hF : F ≤ N)
    (h16 : F % 16 = 0) (hsp : m.regs.SP.toBitVec = base m0 F) :
    Match (Env.ofMachine m [(base m0 F, F)]) (init [(F, true)] (.ptr 0 0)) m :=
  match_ofMachine (sregions := [(F, true)]) (regions := [(base m0 F, F)])
    ⟨rfl, fun _ ↦ base_aligned hS hF h16, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]; rw [hsp]; simp)
    trivial trivial trivial trivial

/-- The frame alone, in a state that kept the entry's bytes. -/
theorem wf_frame {m0 m : MachineData} {F N : Nat} (hS : StackOk m0 N) (hF : F ≤ N)
    (hk : Kept m0.dmem m.dmem) : (Env.ofMachine m [(base m0 F, F)]).WF :=
  Env.wf_of ⟨⟨fun i hi ↦ hk _ ((frame_mapped hS hF).1 i hi), (frame_mapped hS hF).2⟩, trivial⟩
    (List.pairwise_singleton _ _)

/-! ## Arguments -/

namespace Fr

variable {m0 : MachineData} {F N : Nat} {slots : List (Nat × XReg)} {keep : List XReg}
  {outs : BitVec 64 → Prop} {m : MachineData}

/-- An argument readable at the entry is readable in the frame. -/
theorem readable (h : Fr m0 F N slots keep outs m) {a : BitVec 64} {n : Nat}
    (ha : Readable m0 a n) : Readable m a n :=
  ⟨fun i hi ↦ h.kept _ (ha.1 i hi), ha.2⟩

/-- An argument apart from the entry's stack is apart from a callee's. -/
theorem offStack (h : Fr m0 F N slots keep outs m) (hS : StackOk m0 N) {a : BitVec 64}
    {n N' : Nat} (ha : OffStack m0 a n N) (hle : F + N' ≤ N) : OffStack m a n N' :=
  h.apart hS.2.1 ha hle

/-- An argument's bytes, apart from the stack and the outputs, are the entry's. -/
theorem bytes_eq (h : Fr m0 F N slots keep outs m) (hS : StackOk m0 N) {a : BitVec 64}
    {n : Nat} (hna : NoWrap a n) (ha : OffStack m0 a n N)
    (ho : ∀ j < n, ¬outs (a + BitVec.ofNat 64 j)) :
    ∀ j < n, m.dmem.get? (a + BitVec.ofNat 64 j) = m0.dmem.get? (a + BitVec.ofNat 64 j) :=
  fun j hj ↦ h.same _ fun hq ↦ hq.elim
    (not_inRange_of_apart ha hna (stack_noWrap hS) hj) (ho j hj)

/-- A slice apart from the stack and the outputs reads as at the entry. -/
theorem slice_eq (h : Fr m0 F N slots keep outs m) (hS : StackOk m0 N) {a n : UInt64}
    (hok : SliceOk m0 a n N) (ho : ∀ j < 16 * n.toNat, ¬outs (a.toBitVec + BitVec.ofNat 64 j)) :
    slice m a n = slice m0 a n := by
  unfold slice
  rw [NativeRustcVm.ewsOf_congr (Fr.bytes_eq h hS hok.1.2 hok.2 ho)]

/-- `n` elements apart from the stack and the outputs read as at the entry. -/
theorem ewsOf_eq (h : Fr m0 F N slots keep outs m) (hS : StackOk m0 N) {a : BitVec 64} {n : Nat}
    (hna : NoWrap a (16 * n)) (ha : OffStack m0 a (16 * n) N)
    (ho : ∀ j < 16 * n, ¬outs (a + BitVec.ofNat 64 j)) :
    NativeRustcVm.ewsOf m.dmem a n = NativeRustcVm.ewsOf m0.dmem a n :=
  NativeRustcVm.ewsOf_congr (Fr.bytes_eq h hS hna ha ho)

/-- `n` words apart from the stack and the outputs read as at the entry. -/
theorem wordsOf_eq (h : Fr m0 F N slots keep outs m) (hS : StackOk m0 N) {a : BitVec 64} {n : Nat}
    (hna : NoWrap a (8 * n)) (ha : OffStack m0 a (8 * n) N)
    (ho : ∀ j < 8 * n, ¬outs (a + BitVec.ofNat 64 j)) :
    NativeRustcVm.wordsOf m.dmem a n = NativeRustcVm.wordsOf m0.dmem a n :=
  NativeRustcVm.wordsOf_congr (Fr.bytes_eq h hS hna ha ho)

/-- The frame's `same` is a contract's `Changes`, the outputs one region. -/
theorem changes (h : Fr m0 F N slots keep outs m) {oa : BitVec 64} {on : Nat}
    (ho : ∀ q, outs q → InRange oa on q) : Changes m0 m N oa on :=
  NativeRustcVm.SameOutside.mono h.same fun q hq ↦ hq.elim (fun hs ↦ .inr hs) (fun ho' ↦ .inl (ho q ho'))

end Fr

/-! ## Prologues over a larger region -/

/-- **After the prologue**, region 0 the frame and `A` bytes above it (the stack arguments): as
`Fr.ofPrologue`. -/
theorem Fr.ofPrologue' [Labels] {m0 m : MachineData} {F A N : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} {rs : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {S : SState}
    (hN : N ≤ m0.regs.SP.toNat) (hFN : F ≤ N)
    (hm : Match (Env.ofMachine m0 ((base m0 F, F + A) :: rs) vars) S m)
    (hwf : (Env.ofMachine m0 ((base m0 F, F + A) :: rs) vars).WF)
    (hsp : S.sp = .ptr 0 0) (hok : slotsOk S slots = true) (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F)
    (hmem : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ F)
    (hkeep : ∀ r ∈ keep, S.reg r = some (.reg r)) :
    Fr m0 F N slots keep outs m where
  sp := by rw [hm.sp, hsp]; simp [Sym.eval]
  keep r hr := UInt64.toBitVec_inj.mp (hm.regs r _ (hkeep r hr))
  slots p hp := by
    have hw := hm.bytesAt_write (r := 0) (o := p.1) (n := 8) (b := base m0 F) (sz := F + A) rfl
      (by have := hsl p hp; omega) (v := .reg p.2) fun i hi ↦ slotsOk_iff hok p hp i hi
    rw [wordBytes_reg] at hw
    exact hw
  same q hq := by
    refine hm.get?_mem0 hwf fun ⟨w, hw, b, sz, hb, h1, h2⟩ ↦ hq (.inl ?_)
    obtain ⟨hr, hn⟩ := hmem w hw
    rw [hr] at hb
    cases hb
    rw [Sym.inRange_iff (base_noWrap hN), base_toNat hN]
    rw [base_toNat (by omega)] at h1 h2
    omega
  kept := hm.kept hwf

/-- A state in the frame with a second region at the address register `r` holds. -/
theorem match_frame2 [Labels] {m0 m : MachineData} {F N : Nat} (hS : StackOk m0 N) (hF : F ≤ N)
    (h16 : F % 16 = 0) (hsp : m.regs.SP.toBitVec = base m0 F) {r : XReg} {n : Nat} :
    Match (Env.ofMachine m [(base m0 F, F), ((m.regs.getXReg r).toBitVec, n)])
      (init [(F, true), (n, false)] (.ptr 0 0) [(r, .ptr 1 0)]) m :=
  match_ofMachine (sregions := [(F, true), (n, false)])
    (regions := [(base m0 F, F), ((m.regs.getXReg r).toBitVec, n)])
    ⟨rfl, fun _ ↦ base_aligned hS hF h16, rfl, nofun, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]; rw [hsp]; simp)
    ⟨by simp [Sym.eval], trivial⟩ trivial trivial trivial

/-- The frame and a region apart from the entry's stack, in a state that kept them. -/
theorem wf_frame2 {m0 m : MachineData} {F N : Nat} (hS : StackOk m0 N) (hF : F ≤ N)
    (hk : Kept m0.dmem m.dmem) {a : BitVec 64} {n : Nat} (ha : Readable m0 a n)
    (hap : OffStack m0 a n N) : (Env.ofMachine m [(base m0 F, F), (a, n)]).WF := by
  have hN := hS.2.1
  refine Env.wf_of ⟨⟨fun i hi ↦ hk _ ((frame_mapped hS hF).1 i hi), (frame_mapped hS hF).2⟩,
    ⟨fun i hi ↦ hk _ (ha.1 i hi), ha.2⟩, trivial⟩ ?_
  refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
  simp only [List.mem_singleton, forall_eq]
  unfold OffStack Apart at hap
  unfold Apart
  have h1 := base_toNat (m0 := m0) (F := F) (by omega)
  have h2 : (stackBelow m0 N).toNat = m0.regs.SP.toNat - N := base_toNat hN
  omega

/-- **A block in the frame** whose writes are in the frame (region 0) but not its slots, keeping
SP and the kept registers. -/
theorem Fr.block [Labels] {m0 m m' : MachineData} {F N : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} {rs : List (BitVec 64 × Nat)} {S : SState}
    (h : Fr m0 F N slots keep outs m) (hN : N ≤ m0.regs.SP.toNat) (hFN : F ≤ N)
    (hm : Match (Env.ofMachine m ((base m0 F, F) :: rs)) S m')
    (hwf : (Env.ofMachine m ((base m0 F, F) :: rs)).WF) (hsp : S.sp = .ptr 0 0)
    (hmem : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ F ∧
      ∀ p ∈ slots, w.off + w.n ≤ p.1 ∨ p.1 + 8 ≤ w.off)
    (hkeep : ∀ r ∈ keep, S.reg r = some (.reg r)) (hsl8 : ∀ p ∈ slots, p.1 + 8 ≤ F) :
    Fr m0 F N slots keep outs m' := by
  have hFnw := base_noWrap (m0 := m0) (F := F) (by omega)
  have hNnw := base_noWrap (m0 := m0) (F := N) hN
  refine h.step (W := Written (Env.ofMachine m ((base m0 F, F) :: rs)) S) ?_ (fun r hr ↦ ?_)
    (hm.kept hwf) (hm.sameOutside hwf) (fun q hq ↦ ?_) ?_
  · apply UInt64.toBitVec_inj.mp
    rw [hm.sp, hsp, h.sp]
    simp [Sym.eval]
  · exact UInt64.toBitVec_inj.mp (hm.regs r _ (hkeep r hr))
  · obtain ⟨w, hw, b, sz, hbr, h1, h2⟩ := hq
    obtain ⟨hr, hn, -⟩ := hmem w hw
    rw [hr] at hbr
    cases hbr
    left
    rw [Sym.inRange_iff hNnw, base_toNat hN]
    rw [base_toNat (by omega)] at h1 h2
    omega
  · intro p hp i hi hq
    obtain ⟨w, hw, b, sz, hbr, h1, h2⟩ := hq
    obtain ⟨hr, hn, hsl⟩ := hmem w hw
    rw [hr] at hbr
    cases hbr
    have hp8 := hsl p hp
    have hF8 := hsl8 p hp
    rw [NativeRustcVm.addr_add_add] at h1 h2
    rw [NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hFnw; omega)] at h1 h2
    rcases hp8 with h | h <;> omega

/-! ## The frame's words -/

/-- Words at offsets of the frame from `b`. -/
@[expose] def FrameWords (d : DataMem) (b : BitVec 64) (ws : List (Nat × UInt64)) : Prop :=
  ∀ p ∈ ws, NativeRustcVm.WordAt d (b + BitVec.ofNat 64 p.1) p.2

/-- **A word a block wrote**: `v`'s eight bytes at offset `o` of region `r`. -/
theorem wordAt_write [Labels] {env : Env} {S : SState} {m : MachineData}
    (hm : Match env S m) {r o : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + 8 ≤ sz) {v : Sym}
    (hw : ∀ i < 8, findWrite r (o + i) S.mem = some (v, i)) :
    NativeRustcVm.WordAt m.dmem (b + BitVec.ofNat 64 o) (UInt64.ofBitVec (v.eval env)) := by
  have := hm.bytesAt_write hb hle hw
  rw [wordBytes_reg] at this
  exact this

/-- **A word a block did not write** is the environment's. -/
theorem wordAt_keep [Labels] {env : Env} {S : SState} {m : MachineData}
    (hm : Match env S m) {r o : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + 8 ≤ sz)
    (hw : ∀ i < 8, findWrite r (o + i) S.mem = none) {w : UInt64}
    (h : NativeRustcVm.WordAt env.mem0 (b + BitVec.ofNat 64 o) w) :
    NativeRustcVm.WordAt m.dmem (b + BitVec.ofNat 64 o) w := by
  intro i hi
  rw [NativeRustcVm.length_wordBytes] at hi
  rw [NativeRustcVm.addr_add_add, hm.mem r b sz hb (o + i) (by omega)]
  unfold memByte
  rw [hw i hi, ← NativeRustcVm.addr_add_add]
  exact h i (by rw [NativeRustcVm.length_wordBytes]; exact hi)

/-- **The frame's words across a call** that writes its stack below the frame and outputs apart
from it. -/
theorem FrameWords.call {m0 m m' : MachineData} {F N' : Nat} {outs : BitVec 64 → Prop}
    {ws : List (Nat × UInt64)} (h : FrameWords m.dmem (base m0 F) ws)
    (hsp : m.regs.SP.toBitVec = base m0 F) (hN : F + N' ≤ m0.regs.SP.toNat)
    (hws : ∀ p ∈ ws, p.1 + 8 ≤ F) (hfr : ∀ q, outs q → ¬InRange (base m0 F) F q)
    (hs : SameOutside m.dmem m'.dmem fun q ↦ InRange (stackBelow m N') N' q ∨ outs q) :
    FrameWords m'.dmem (base m0 F) ws := by
  intro p hp
  refine NativeRustcVm.BytesAt.of_sameOutside (h p hp) hs fun i hi hq ↦ ?_
  rw [NativeRustcVm.length_wordBytes] at hi
  have hp8 := hws p hp
  have hsb := stackBelow_eq hsp (N' := N') hN
  have hnw : NoWrap (base m0 (F + N')) N' := by
    unfold NoWrap; rw [base_toNat (by omega)]; have := m0.regs.SP.toNat_lt; omega
  have hF := base_noWrap (m0 := m0) (F := F) (by omega)
  rw [NativeRustcVm.addr_add_add] at hq
  have hin : InRange (base m0 F) F (base m0 F + BitVec.ofNat 64 (p.1 + i)) :=
    NativeRustcVm.inRange_add (by omega) (by unfold NoWrap at hF; omega)
  rcases hq with hq | hq
  · rw [hsb, Sym.inRange_iff hnw] at hq
    rw [Sym.inRange_iff hF] at hin
    rw [base_toNat (by omega)] at hq
    rw [base_toNat (by omega)] at hin
    omega
  · exact hfr _ hq hin

/-- **The frame's words across a block** that did not write them. -/
theorem FrameWords.block [Labels] {m m' : MachineData} {b : BitVec 64} {sz : Nat}
    {rs : List (BitVec 64 × Nat)} {S : SState} {ws : List (Nat × UInt64)}
    (h : FrameWords m.dmem b ws) (hm : Match (Env.ofMachine m ((b, sz) :: rs)) S m')
    (hws : ∀ p ∈ ws, p.1 + 8 ≤ sz ∧ ∀ i < 8, findWrite 0 (p.1 + i) S.mem = none) :
    FrameWords m'.dmem b ws := fun p hp ↦
  wordAt_keep hm rfl (hws p hp).1 (hws p hp).2 (h p hp)

/-- The words of the elements from `a`, two each. -/
theorem ewsAt_of_words {d : DataMem} {a : BitVec 64} :
    ∀ (xs : List NativeVm.Model.EW), (∀ i (h : i < xs.length),
      NativeRustcVm.WordAt d (a + BitVec.ofNat 64 (16 * i)) xs[i].c0 ∧
      NativeRustcVm.WordAt d (a + BitVec.ofNat 64 (16 * i + 8)) xs[i].c1) →
      NativeRustcVm.EWsAt d a xs
  | [], _ => NativeRustcVm.ewsAt_nil d a
  | x :: xs, h => by
    rw [show x :: xs = [x] ++ xs from rfl, NativeRustcVm.ewsAt_append]
    refine ⟨?_, ?_⟩
    · rw [NativeRustcVm.ewsAt_singleton, NativeRustcVm.ewAt_iff]
      have := h 0 (by simp)
      simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero] at this
      refine ⟨by simpa using this.1, ?_⟩
      have h8 := this.2
      rwa [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl]
    · simp only [List.length_singleton]
      refine ewsAt_of_words xs fun i hi ↦ ?_
      have := h (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add,
        show 16 * 1 + 16 * i = 16 * (i + 1) by omega,
        show 16 * 1 + (16 * i + 8) = 16 * (i + 1) + 8 by omega]
      exact this

/-- **A local array** of the frame, `n` bytes at offset `o`: readable, apart from a callee's
stack. -/
theorem local_ok {m0 m : MachineData} {F N N' : Nat} {o n : Nat} (hS : StackOk m0 N)
    (hFN : F + N' ≤ N) (hon : o + n ≤ F) (hk : Kept m0.dmem m.dmem)
    (hsp : m.regs.SP.toBitVec = base m0 F) :
    Readable m (base m0 F + BitVec.ofNat 64 o) n ∧
      OffStack m (base m0 F + BitVec.ofNat 64 o) n N' := by
  have hN := hS.2.1
  have hfm := frame_mapped hS (show F ≤ N by omega)
  have hb := base_toNat (m0 := m0) (F := F) (by omega)
  have hlt := m0.regs.SP.toNat_lt
  refine ⟨⟨fun i hi ↦ ?_, ?_⟩, ?_⟩
  · rw [NativeRustcVm.addr_add_add]; exact hk _ (hfm.1 _ (by omega))
  · unfold NoWrap; rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega
  · unfold OffStack Apart
    rw [stackBelow_eq hsp (by omega), base_toNat (by omega),
      NativeRustcVm.toNat_add_ofNat (by omega), hb]
    omega

/-- **`cmp`, `ccmp`, `cset eq` of two elements**: X0 = `1` iff they are equal. -/
theorem cset_ew (x y : NativeVm.Model.EW) :
    (if (!if CmpOp.eq.apply .W64 x.c0.toBitVec y.c0.toBitVec = true then
          CmpOp.eq.apply .W64 x.c1.toBitVec y.c1.toBitVec else false) = true then 0#64
      else 1#64) = (okWord (x == y)).toBitVec := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  have e : ∀ u v : UInt64, (u.toBitVec == v.toBitVec) = (u == v) := fun u v ↦ by
    by_cases h : u = v
    · simp [h]
    · simp [h, UInt64.toBitVec_inj]
  simp only [CmpOp.apply, Sym.low_W64, e, okWord]
  by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [h1, h2]

/-- A callee's frame of no outputs as `Fr.leaf` takes it. -/
theorem changes_zero {m m' : MachineData} {N' : Nat} {outs : BitVec 64 → Prop}
    (h : Changes m m' N' 0 0) :
    SameOutside m.dmem m'.dmem (fun q ↦ InRange (stackBelow m N') N' q ∨ outs q) :=
  NativeRustcVm.SameOutside.mono h fun q hq ↦ hq.elim
    (fun h ↦ by unfold InRange at h; omega) .inl

/-- A register a block left alone. -/
theorem keep_reg [Labels] {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    {r : XReg} (hm : Match (Env.ofMachine m rs) S m') (h : S.reg r = some (.reg r)) :
    m'.regs.getXReg r = m.regs.getXReg r :=
  UInt64.toBitVec_inj.mp (hm.regs r _ h)

/-- The registers `L` of `m` still in `m'`. -/
@[expose] def KeepRegs (L : List XReg) (m m' : MachineData) : Prop :=
  ∀ r ∈ L, m'.regs.getXReg r = m.regs.getXReg r

theorem KeepRegs.trans {L : List XReg} {m m' m'' : MachineData} (h : KeepRegs L m m')
    (h' : KeepRegs L m' m'') : KeepRegs L m m'' := fun r hr ↦ (h' r hr).trans (h r hr)

theorem KeepRegs.of_call {L : List XReg} {m m' : MachineData}
    (h : ∀ r, calleeSaved r = true → m'.regs.getXReg r = m.regs.getXReg r)
    (hL : L.all calleeSaved = true) : KeepRegs L m m' := fun r hr ↦
  h r (List.all_eq_true.mp hL r hr)

theorem KeepRegs.of_block [Labels] {L : List XReg} {m m' : MachineData}
    {rs : List (BitVec 64 × Nat)} {S : SState} (hm : Match (Env.ofMachine m rs) S m')
    (h : L.all (fun r ↦ S.reg r == some (.reg r)) = true) : KeepRegs L m m' := fun r hr ↦
  keep_reg hm (beq_iff_eq.mp (List.all_eq_true.mp h r hr))

theorem KeepRegs.get {L : List XReg} {m m' : MachineData} (h : KeepRegs L m m') {r : XReg}
    (hr : r ∈ L := by decide) : m'.regs.getXReg r = m.regs.getXReg r := h r hr

/-- Nothing is in an empty range. -/
theorem not_inRange_zero (a p : BitVec 64) : ¬InRange a 0 p := fun h ↦ by
  unfold InRange at h; omega

/-- **Where a block wrote**: in region `r`, when every write of the block is there. -/
theorem Written.inRange {env : Env} {S : SState} {r : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hnw : b.toNat + sz ≤ 2 ^ 64)
    (hS : ∀ w ∈ S.mem, w.r = r ∧ w.off + w.n ≤ sz) {p : BitVec 64} (h : Written env S p) :
    InRange b sz p := by
  obtain ⟨w, hw, b', sz', hb', h1, h2⟩ := h
  obtain ⟨hr, hle⟩ := hS w hw
  rw [hr, hb] at hb'
  cases hb'
  exact (NativeRustcVm.inRange_iff hnw).mpr ⟨by omega, by omega⟩

/-- A load from region 1 of a two-region environment: the word there. -/
theorem load_r1 [Labels] (m : MachineData) (b0 b1 : BitVec 64) (F n o : Nat) :
    (Sym.load 1 o 8).eval (Env.ofMachine m [(b0, F), (b1, n)]) =
      (NativeRustcVm.wordOf m.dmem (b1 + BitVec.ofNat 64 o)).toBitVec := by
  show Env.load _ 1 o 8 = _
  rw [load_eq_wordOf]
  rfl

/-- `eor` of a register and a value. -/
theorem eval_eor [Labels] (env : Env) (r : XReg) (s : Sym) (x : UInt64)
    (hs : s.eval env = x.toBitVec) :
    UInt64.ofBitVec ((Sym.bin .eor .W64 (.reg r) s).eval env) =
      UInt64.ofBitVec (env.regs r) ^^^ x := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, hs]
  rfl

/-- Two elements read. -/
theorem ewsOf_two (d : DataMem) (a : BitVec 64) :
    NativeRustcVm.ewsOf d a 2 =
      [⟨NativeRustcVm.wordOf d (a + BitVec.ofNat 64 0),
          NativeRustcVm.wordOf d (a + BitVec.ofNat 64 8)⟩,
        ⟨NativeRustcVm.wordOf d (a + BitVec.ofNat 64 16),
          NativeRustcVm.wordOf d (a + BitVec.ofNat 64 24)⟩] := by
  simp [NativeRustcVm.ewsOf, NativeRustcVm.ewOf, List.range_succ, BitVec.add_assoc]

/-- **A frame with more outputs.** -/
theorem Fr.mono {m0 : MachineData} {F N : Nat} {slots : List (Nat × XReg)} {keep : List XReg}
    {outs outs' : BitVec 64 → Prop} {m : MachineData} (h : Fr m0 F N slots keep outs m)
    (ho : ∀ q, outs q → outs' q) : Fr m0 F N slots keep outs' m :=
  { h with
    same := NativeRustcVm.SameOutside.mono h.same fun q hq ↦ hq.elim .inl fun h ↦ .inr (ho q h) }

/-- The frame's bytes are the stack's. -/
theorem frame_inRange {m0 : MachineData} {F N : Nat} (hN : N ≤ m0.regs.SP.toNat) (hF : F ≤ N)
    {q : BitVec 64} (h : InRange (base m0 F) F q) : InRange (base m0 N) N q := by
  rw [Sym.inRange_iff (base_noWrap (by omega))] at h
  rw [Sym.inRange_iff (base_noWrap hN)]
  rw [base_toNat (by omega)] at h
  rw [base_toNat hN]
  omega

/-- **A contract carrying a fact of the entry** to the exit. -/
theorem Spec.withFact [Host] {l : Int64} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} (h : Spec l P Q) (R : MachineData → Prop) :
    Spec l (fun m ↦ P m ∧ R m) (fun m m' ↦ Q m m' ∧ R m) :=
  fun m hm ↦ (h m hm.1).mono fun _ h' ↦ ⟨h'.1, h'.2, hm.2⟩

end

end NativeRustcVmArm.Bus
