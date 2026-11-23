module

public import NativeRustcVmArm.Bus.AccumulateSide.Pre

/-!
# `accumulate_side`: the entry

`b0` saves X19 to X30, keeps the arguments (in the frame and in registers: `DA`), and takes the
framework blocks' count (X22), their placements' address (X21) and the fingerprints the known
part reads (X20, `min` of the counts), then branches on X20 being `0`.

- `rs0`, `rsA`: the frame; the frame and the stack arguments.
- `matchA`, `wfA`, `Fr.blockA`: blocks of the frame that read the stack arguments.
- `holds_args`: the stack arguments are the entry's in a state of the frame.
- `A0`, `entry_spec`.
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVm.Transcript (off)

public section

/-- The frame. -/
abbrev rs0 (m0 : MachineData) : List (BitVec 64 × Nat) := [(base m0 F, F)]

/-- The frame and the stack arguments. -/
abbrev rsA (m0 : MachineData) : List (BitVec 64 × Nat) := [(base m0 F, F + 72)]

/-- The stack arguments' words. -/
def DArgs : List (Sym × Nat) :=
  [(.load 0 12096 8, 16), (.load 0 12104 8, 8), (.load 0 12112 8, 9), (.load 0 12120 8, 10),
    (.load 0 12128 8, 11), (.load 0 12136 8, 12), (.load 0 12144 8, 13), (.load 0 12152 8, 14),
    (.load 0 12160 8, 15)]

/-- The entry: the argument registers, the stack arguments, the side layout's base. -/
def DE : List (Sym × Nat) :=
  [(.reg .X0, 0), (.reg .X1, 1), (.reg .X2, 2), (.reg .X3, 3), (.reg .X4, 4), (.reg .X5, 5),
    (.reg .X6, 6), (.reg .X7, 7), (.ptr 1 0, 6)] ++ DArgs

/-- After `b0`. -/
def DA : List (Sym × Nat) :=
  [(.reg .X19, 6), (.reg .X23, 10), (.reg .X24, 11), (.reg .X25, 13), (.reg .X27, 4),
    (.reg .X28, 12), (.reg .X29, 15), (.reg .X7, 7),
    (.load 0 16 8, 0), (.load 0 48 8, 1), (.load 0 56 8, 2), (.load 0 128 8, 3),
    (.load 0 120 8, 5), (.load 0 104 8, 12), (.load 0 112 8, 13), (.load 0 32 8, 14)]

/-- `b0`'s three computed registers. -/
def DA' : List (Sym × Nat) := [(.reg .X20, 19), (.reg .X21, 18), (.reg .X22, 17)]

theorem base_args (m0 : MachineData) (k : Nat) :
    base m0 F + BitVec.ofNat 64 (12096 + k) = m0.regs.SP.toBitVec + BitVec.ofNat 64 k := by
  rw [← NativeRustcVm.addr_add_add, base_add_eq]

section
variable [Labels] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData}

theorem F_le (h : Pre L rows bl Fm SL m0) : F ≤ m0.regs.SP.toNat := by
  have := h.stack.2.1; rw [N_eq] at this; show 12096 ≤ _; omega

theorem N_le (h : Pre L rows bl Fm SL m0) : N ≤ m0.regs.SP.toNat := h.stack.2.1

theorem argsNW (h : Pre L rows bl Fm SL m0) : m0.regs.SP.toBitVec.toNat + 72 ≤ 2 ^ 64 :=
  h.args.2

omit [Labels] in
theorem sp_toNat (m : MachineData) : m.regs.SP.toNat = m.regs.SP.toBitVec.toNat := rfl

omit [Labels] in
/-- A stack argument's word read in a state whose bytes there are the entry's. -/
theorem argLoad {st : MachineData} (rest : List (BitVec 64 × Nat)) (k : Nat)
    (hs : ∀ i < 8, st.dmem.get? (m0.regs.SP.toBitVec + BitVec.ofNat 64 (k + i)) =
      m0.dmem.get? (m0.regs.SP.toBitVec + BitVec.ofNat 64 (k + i))) (vars : Nat → BitVec 64) :
    (Env.ofMachine st ((base m0 F, F + 72) :: rest) vars).load 0 (12096 + k) 8 =
      (stackArg m0 k).toBitVec := by
  rw [load_eq_wordOf]
  simp only [Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some, Option.getD_some,
    Env.ofMachine_mem0]
  rw [base_args]
  unfold stackArg
  rw [NativeRustcVm.wordOf_congr (d := m0.dmem) fun i hi ↦ by
    rw [NativeRustcVm.addr_add_add]; exact hs i hi]

/-- The stack arguments' words where the bytes there are the entry's. -/
theorem holds_args_of {st : MachineData} (rest : List (BitVec 64 × Nat))
    (hsame : ∀ k, k + 8 ≤ 72 → ∀ i < 8,
      st.dmem.get? (m0.regs.SP.toBitVec + BitVec.ofNat 64 (k + i)) =
        m0.dmem.get? (m0.regs.SP.toBitVec + BitVec.ofNat 64 (k + i))) :
    Holds ((base m0 F, F + 72) :: rest) (sv m0) DArgs st := by
  have e : ∀ k, k + 8 ≤ 72 → tval ((base m0 F, F + 72) :: rest) st (.load 0 (12096 + k) 8) =
      stackArg m0 k := fun k hk ↦ by
    unfold tval
    show UInt64.ofBitVec ((Env.ofMachine st _).load 0 (12096 + k) 8) = _
    rw [argLoad rest k (hsame k hk)]
  intro p hp
  simp only [DArgs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e 0 (by omega)
  · exact e 8 (by omega)
  · exact e 16 (by omega)
  · exact e 24 (by omega)
  · exact e 32 (by omega)
  · exact e 40 (by omega)
  · exact e 48 (by omega)
  · exact e 56 (by omega)
  · exact e 64 (by omega)

/-- **The stack arguments** in a state of the frame. -/
theorem holds_args (h : Pre L rows bl Fm SL m0) {st : MachineData}
    (hfr : Fr m0 F N slots keep (outs m0) st) : Holds (rsA m0) (sv m0) DArgs st := by
  refine holds_args_of [] fun k hk i hi ↦ ?_
  refine hfr.same _ fun hq ↦ hq.elim (fun hs ↦ ?_) (fun ho ↦ ?_)
  · have hN := N_le h
    have hsb : (base m0 N).toNat = m0.regs.SP.toNat - N := base_toNat hN
    have := argsNW h
    rw [Sym.inRange_iff (base_noWrap hN), hsb, NativeRustcVm.toNat_add_ofNat (by omega)] at hs
    rw [N_eq] at hs hN
    have := sp_toNat m0
    omega
  · exact NativeRustcVm.Apart.not_inRange_add (NativeRustcVm.Apart.symm h.fArgs) h.args.2
      h.formsOk.1.2 (by omega) ho

/-- The frame and the stack arguments: mapped, not wrapping. -/
theorem mappedA (h : Pre L rows bl Fm SL m0) {d : DataMem} (hk : Kept m0.dmem d) :
    NativeRustcVm.Mapped d (base m0 F) (F + 72) ∧ NoWrap (base m0 F) (F + 72) := by
  have hFl := F_le h
  have hb := base_toNat (m0 := m0) (F := F) hFl
  have hsp := sp_toNat m0
  have hNW := argsNW h
  have hF : F = 12096 := rfl
  refine ⟨fun i hi ↦ hk _ ?_, by unfold NoWrap; rw [hb]; omega⟩
  by_cases hi' : i < F
  · exact (Bus.frame_mapped h.stack (by decide)).1 i hi'
  · have := h.args.1 (i - F) (by omega)
    rwa [← base_add_eq (m0 := m0) (F := F), NativeRustcVm.addr_add_add,
      show F + (i - F) = i by omega] at this

theorem wfA (h : Pre L rows bl Fm SL m0) {st : MachineData} (hk : Kept m0.dmem st.dmem) :
    (Env.ofMachine st (rsA m0)).WF :=
  Env.wf_of ⟨mappedA h hk, trivial⟩ (List.pairwise_singleton _ _)

theorem matchA (h : Pre L rows bl Fm SL m0) {st : MachineData}
    (hsp : st.regs.SP.toBitVec = base m0 F) :
    Match (Env.ofMachine st (rsA m0)) sA st :=
  match_ofMachine (sregions := [(F + 72, true)]) (regions := rsA m0)
    ⟨rfl, fun _ ↦ Bus.base_aligned h.stack (by decide) rfl, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]; rw [hsp]; simp)
    trivial trivial trivial trivial

end

/-- **A block of the frame reading the stack arguments**: its writes in the frame, not the
slots. -/
theorem Fr.blockA [Labels] {m0 m m' : MachineData} {Nn A : Nat} {outs' : BitVec 64 → Prop}
    {rs : List (BitVec 64 × Nat)} {S : SState}
    (h : Fr m0 F Nn slots keep outs' m) (hN : Nn ≤ m0.regs.SP.toNat) (hFN : F ≤ Nn)
    (hm : Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S m')
    (hwf : (Env.ofMachine m ((base m0 F, F + A) :: rs)).WF) (hsp : S.sp = .ptr 0 0)
    (hmem : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ F ∧
      ∀ p ∈ slots, w.off + w.n ≤ p.1 ∨ p.1 + 8 ≤ w.off) :
    Fr m0 F Nn slots keep outs' m' := by
  have hFnw := base_noWrap (m0 := m0) (F := F) (by omega)
  have hNnw := base_noWrap (m0 := m0) (F := Nn) hN
  refine h.step (W := Written (Env.ofMachine m ((base m0 F, F + A) :: rs)) S) ?_ (fun r hr ↦ ?_)
    (hm.kept hwf) (hm.sameOutside hwf) (fun q hq ↦ ?_) ?_
  · apply UInt64.toBitVec_inj.mp
    rw [hm.sp, hsp, h.sp]
    simp [Sym.eval]
  · cases hr
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
    have hF8 := slots_le p hp
    rw [NativeRustcVm.addr_add_add] at h1 h2
    rw [NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hFnw; omega)] at h1 h2
    rcases hp8 with h | h <;> omega

/-! ## The entry -/

/-- The entry's regions: the frame and the stack arguments, the side layout. -/
abbrev rsE (m0 : MachineData) : List (BitVec 64 × Nat) :=
  [(base m0 F, F + 72), (m0.regs.X6.toBitVec, busLayoutBytes)]

section
variable [Labels] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData}

theorem holds_entry : Holds (rsE m0) (sv m0) DE m0 := by
  refine Holds.append (fun p hp ↦ ?_) (holds_args_of _ fun _ _ _ _ ↦ rfl)
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  unfold tval
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | (simp only [Sym.eval, Env.base_ofMachine_eq]; simp [sv])

end

end

end NativeRustcVmArm.Bus.AccumulateSide
