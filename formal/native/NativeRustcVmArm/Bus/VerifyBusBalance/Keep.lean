module

public import NativeRustcVmArm.Bus.VerifyBusBalance.Locs

/-!
# Locals of `verify_bus_balance`'s frame kept, by intervals

`KeepIv ivs m0 d d'`: the frame's bytes in the intervals `ivs` the same from `d` to `d'`.

- `keepIv_block`: a block whose writes in the frame miss the intervals (decided on its writes).
- `keepIv_call`: a call writing below the frame and `X`, apart from the intervals.
- `KeepIv.sameIn`: `n` bytes at `o` within one interval kept.
- `KeepIv.locs`: the locals of `Locs` kept.
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalance
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVm.Layout NativeRustcVmArm.Bus.Gkr

public section

/-- The byte `j` is in one of the intervals `[lo, hi)`. -/
@[expose] def InIv (ivs : List (Nat × Nat)) (j : Nat) : Prop := ∃ p ∈ ivs, p.1 ≤ j ∧ j < p.2

/-- The frame's bytes in the intervals the same. -/
@[expose] def KeepIv (ivs : List (Nat × Nat)) (m0 : MachineData) (d d' : Mem 64) : Prop :=
  ∀ j, InIv ivs j → Same d d' (loc m0 j) 1

theorem KeepIv.trans {ivs : List (Nat × Nat)} {m0 : MachineData} {d d' d'' : Mem 64}
    (h : KeepIv ivs m0 d d') (h' : KeepIv ivs m0 d' d'') : KeepIv ivs m0 d d'' :=
  fun j hj ↦ (h j hj).trans (h' j hj)

theorem KeepIv.rfl' {ivs : List (Nat × Nat)} {m0 : MachineData} {d d' : Mem 64} (h : d' = d) :
    KeepIv ivs m0 d d' := fun _ _ _ _ ↦ by rw [h]

/-- Fewer intervals. -/
theorem KeepIv.mono {ivs ivs' : List (Nat × Nat)} {m0 : MachineData} {d d' : Mem 64}
    (h : KeepIv ivs m0 d d') (hs : ∀ j, InIv ivs' j → InIv ivs j) : KeepIv ivs' m0 d d' :=
  fun j hj ↦ h j (hs j hj)

/-- **`n` bytes at `o` kept**, within the interval `[lo, hi)`. -/
theorem KeepIv.sameIn {ivs : List (Nat × Nat)} {m0 : MachineData} {d d' : Mem 64}
    (h : KeepIv ivs m0 d d') {lo hi : Nat} (hm : (lo, hi) ∈ ivs) {o n : Nat} (h1 : lo ≤ o)
    (h2 : o + n ≤ hi) : Same d d' (loc m0 o) n := fun j hj ↦ by
  have := h (o + j) ⟨(lo, hi), hm, by simp only; omega, by simp only; omega⟩ 0 (by omega)
  rw [Bus.add_zero'] at this
  rw [NativeRustcVm.addr_add_add]
  exact this

/-- Intervals within others. -/
theorem ivSub {ivs ivs' : List (Nat × Nat)}
    (h : ivs'.all (fun p ↦ ivs.any fun q ↦ decide (q.1 ≤ p.1) && decide (p.2 ≤ q.2)) = true) :
    ∀ j, InIv ivs' j → InIv ivs j := by
  rintro j ⟨p, hp, h1, h2⟩
  have := List.all_eq_true.mp h p hp
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨q, hq, h3, h4⟩ := this
  exact ⟨q, hq, by omega, by omega⟩

/-- The intervals' bytes, below `B`. -/
theorem inIv_lt {ivs : List (Nat × Nat)} {B : Nat} (h : ivs.all (fun p ↦ decide (p.2 ≤ B)) = true)
    {j : Nat} (hj : InIv ivs j) : j < B := by
  obtain ⟨p, hp, h1, h2⟩ := hj
  have := List.all_eq_true.mp h p hp
  simp only [decide_eq_true_eq] at this
  omega

/-- The intervals apart from `[o, o + n)`. -/
theorem inIv_apart {ivs : List (Nat × Nat)} {o n : Nat}
    (h : ivs.all (fun p ↦ decide (p.2 ≤ o) || decide (o + n ≤ p.1)) = true)
    {j : Nat} (hj : InIv ivs j) : j < o ∨ o + n ≤ j := by
  obtain ⟨p, hp, h1, h2⟩ := hj
  have := List.all_eq_true.mp h p hp
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  omega

/-- **A block's changes keep the intervals**: its writes in the frame (region `0`) apart from
them, its other writes within their regions. -/
theorem keepIv_block [Labels] {m0 m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m ((base m0 5488, 5488) :: rs)) S m')
    (hwf : (Env.ofMachine m ((base m0 5488, 5488) :: rs)).WF) {sizes : List Nat}
    (hsz : (Env.ofMachine m ((base m0 5488, 5488) :: rs)).regions.map Prod.snd = sizes)
    {ivs : List (Nat × Nat)} (hlt : ivs.all (fun p ↦ decide (p.2 ≤ 5488)) = true)
    (hw : (S.mem.all fun w ↦ (w.r == 0 &&
        ivs.all (fun p ↦ decide (w.off + w.n ≤ p.1) || decide (p.2 ≤ w.off))) ||
      (w.r != 0 && decide (w.off + w.n ≤ (sizes[w.r]?).getD 0))) = true) :
    KeepIv ivs m0 m.dmem m'.dmem := by
  intro j hj
  have hj5 := inIv_lt hlt hj
  obtain ⟨p, hp, h1, h2⟩ := hj
  refine same_block hm hwf hsz (o := j) (n := 1) (by omega) (List.all_eq_true.mpr fun w hw' ↦ ?_)
  have := List.all_eq_true.mp hw w hw'
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq, List.all_eq_true] at this ⊢
  rcases this with ⟨hr, h'⟩ | h'
  · have := h' p hp
    exact .inl ⟨hr, by omega⟩
  · exact .inr h'

/-- **A call's changes keep the intervals**: below the frame and `X`, apart from them. -/
theorem keepIv_call {m0 m d : MachineData} (hS : StackOk m0 verifyBusBalanceStack)
    (hsp : m.regs.SP.toBitVec = base m0 5488) {N' : Nat} (hle : 5488 + N' ≤ verifyBusBalanceStack)
    {X : BitVec 64 → Prop}
    (hs : SameOutside m.dmem d.dmem (fun q ↦ InRange (stackBelow m N') N' q ∨ X q))
    {ivs : List (Nat × Nat)} (hlt : ivs.all (fun p ↦ decide (p.2 ≤ 5488)) = true)
    (hX : ∀ j, InIv ivs j → ¬X (loc m0 j)) : KeepIv ivs m0 m.dmem d.dmem := fun j hj ↦
  same_call hS hsp hle hs (o := j) (n := 1) (by have := inIv_lt hlt hj; omega) fun i hi ↦ by
    rw [show i = 0 by omega, Bus.add_zero']; exact hX j hj

/-- A local of `n` bytes at `o` misses the intervals. -/
theorem not_iv {m0 : MachineData} (hS : StackOk m0 verifyBusBalanceStack) {o n : Nat}
    (hon : o + n ≤ 5488) {ivs : List (Nat × Nat)}
    (hlt : ivs.all (fun p ↦ decide (p.2 ≤ 5488)) = true)
    (hd : ivs.all (fun p ↦ decide (p.2 ≤ o) || decide (o + n ≤ p.1)) = true) :
    ∀ j, InIv ivs j → ¬InRange (loc m0 o) n (loc m0 j) := fun _ hj ↦
  loc_not_loc hS (inIv_lt hlt hj) hon (inIv_apart hd hj)

/-- `Locs`'s intervals. -/
abbrev locsIv : List (Nat × Nat) := [(80, 136), (160, 4176), (5248, 5320)]

/-- **The locals of `Locs` kept.** -/
theorem KeepIv.locs {m0 : MachineData} {d d' : Mem 64} (h : KeepIv locsIv m0 d d') :
    KeepLoc m0 d d' := fun j hj ↦ h j (by
  unfold InLocs at hj
  rcases hj with hj | hj | hj
  · exact ⟨(80, 136), by simp, hj.1, hj.2⟩
  · exact ⟨(160, 4176), by simp, hj.1, hj.2⟩
  · exact ⟨(5248, 5320), by simp, hj.1, hj.2⟩)

end

public section
variable [Labels] {m0 : MachineData}

/-- A register a block loaded from the frame's byte `o` (the frame region `0`). -/
theorem reg_ld' {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState} {x : XReg}
    {o : Nat} (hm : Match (Env.ofMachine m ((base m0 5488, 5488) :: rs)) S m')
    (hx : S.reg x = some (.load 0 o 8)) {w : UInt64}
    (hw : NativeRustcVm.WordAt m.dmem (loc m0 o) w) : m'.regs.getXReg x = w :=
  UInt64.toBitVec_inj.mp ((hm.regs x _ hx).trans
    (Transcript.load_ofMachine (b := base m0 5488) (n := 5488) rfl hw))

end

public section

/-- The registers `L` the same in `m` and `m'`. -/
@[expose] def RegsEq (L : List XReg) (m m' : MachineData) : Prop :=
  ∀ r ∈ L, m'.regs.getXReg r = m.regs.getXReg r

theorem RegsEq.trans {L : List XReg} {m m' m'' : MachineData} (h : RegsEq L m m')
    (h' : RegsEq L m' m'') : RegsEq L m m'' := fun r hr ↦ (h' r hr).trans (h r hr)

/-- **A block keeps the registers** it maps to themselves. -/
theorem regsEq_block [Labels] {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m rs) S m') {L : List XReg}
    (h : L.all (fun r ↦ S.reg r == some (.reg r)) = true) : RegsEq L m m' := fun r hr ↦
  reg_of hm (beq_iff_eq.mp (List.all_eq_true.mp h r hr))

/-- **A call keeps the callee-saved registers.** -/
theorem regsEq_call {m m' : MachineData}
    (hcs : ∀ r, calleeSaved r = true → m'.regs.getXReg r = m.regs.getXReg r) {L : List XReg}
    (h : L.all calleeSaved = true) : RegsEq L m m' := fun r hr ↦
  hcs r (List.all_eq_true.mp h r hr)

/-- The callee-saved registers the function keeps values in. -/
abbrev csL : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29]

end

end NativeRustcVmArm.Bus.VerifyBusBalance
