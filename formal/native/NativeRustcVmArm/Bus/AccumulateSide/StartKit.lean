module

public import NativeRustcVmArm.Bus.AccumulateSide.Loop1

/-!
# `accumulate_side` up to the table loop: the descriptions, the regions

From the entry to the table loop's head (`b0` to `b26`) the body keeps turn `0`'s table
(`TT … 0`). The descriptions at the blocks' starts: the known part (`Q2` to `Q15`), the ones over
the framework (`QO` to `QZ`), the zeroing loop and `memcpy` (`QZ`, `Q25`, `Q26`).

- `Holds.dup`: a location described twice, with an equal value.
- `matchRR`, `wf2`: the frame and two more regions (the side layout's framework placements, the
  fingerprints).
- `rok_sl`, `rok_fp`, `ap_sl_fp`: the side layout's and the fingerprints' bytes as regions.
- `mul_eq`: `EW::mul`'s operands as the known part's term.
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

@[expose] public section

/-- The entry's locations: the argument registers, the side layout, the stack arguments. -/
def QE : List (Sym × Nat) :=
  [(.reg .X0, 0), (.reg .X1, 1), (.reg .X2, 2), (.reg .X3, 3), (.reg .X4, 4), (.reg .X5, 5),
    (.reg .X6, 6), (.reg .X7, 7), (.ptr 1 0, 6), (.load 0 12096 8, 16), (.load 0 12120 8, 10),
    (.load 0 12128 8, 11), (.load 0 12136 8, 12), (.load 0 12144 8, 13), (.load 0 12152 8, 14),
    (.load 0 12160 8, 15)]

/-- The frame words `b0` stores but the tree's low limb. -/
def Fw0 : List (Sym × Nat) :=
  [(.load 0 16 8, 0), (.load 0 48 8, 1), (.load 0 56 8, 2), (.load 0 128 8, 3),
    (.load 0 120 8, 5), (.load 0 104 8, 12), (.load 0 112 8, 13)]

/-- The frame words of the known part: the tree's low limb, the blocks' count and the side
layout `b1` saves. -/
def FwK : List (Sym × Nat) :=
  Fw0 ++ [(.load 0 32 8, 14), (.load 0 136 8, 4), (.load 0 144 8, 6)]

/-- After `b0`: the locations it keeps. -/
def QAr : List (Sym × Nat) :=
  [(.reg .X19, 6), (.reg .X23, 10), (.reg .X24, 11), (.reg .X25, 13), (.reg .X27, 4),
    (.reg .X28, 12), (.reg .X29, 15), (.reg .X7, 7)] ++ Fw0 ++ [(.load 0 32 8, 14)]

/-- After `b0`: the framework's count, its placements' address, the known part's count. -/
def QAe : List (Sym × Nat) := [(.reg .X20, 19), (.reg .X21, 18), (.reg .X22, 17)]

/-- At `b1`, `b5`. -/
def QA : List (Sym × Nat) := QAr ++ QAe

/-- The stack arguments `b5` and `b15` copy: the weights. -/
def QArgs : List (Sym × Nat) := [(.load 0 12104 8, 8), (.load 0 12112 8, 9)]

/-- `b1`'s registers kept. -/
def Q1r : List (Sym × Nat) :=
  [(.reg .X20, 19), (.reg .X21, 18), (.reg .X22, 17), (.reg .X23, 10), (.reg .X24, 11),
    (.reg .X25, 13), (.reg .X26, 7), (.reg .X28, 12), (.reg .X29, 15)] ++ FwK

/-- After `b1`: fingerprint `0` in X19, X27. -/
def Q1e : List (Sym × Nat) := [(.reg .X19, 30), (.reg .X27, 31)]

/-- At `b2`: selector `0` in X0, X1. -/
def Q2 : List (Sym × Nat) := (.reg .X0, 40) :: (.reg .X1, 41) :: (Q1r ++ Q1e)

/-- At `b3`: term `0` in X0, X1. -/
def Q3 : List (Sym × Nat) := (.reg .X0, 50) :: (.reg .X1, 51) :: Q1r

/-- `b3`'s registers kept. -/
def Q3r : List (Sym × Nat) :=
  [(.reg .X27, 11), (.reg .X24, 12), (.reg .X20, 19), (.reg .X21, 18), (.reg .X22, 17),
    (.reg .X23, 10), (.reg .X25, 13), (.reg .X26, 7), (.reg .X29, 15)] ++ FwK

/-- At `b4`, `b7`: the known part over one block in X19, X28. -/
def Q4 : List (Sym × Nat) := Q3r ++ [(.reg .X19, 60), (.reg .X28, 61)]

/-- `b7`'s locations kept. -/
def Q7r : List (Sym × Nat) :=
  [(.reg .X19, 60), (.reg .X28, 61), (.reg .X27, 11), (.reg .X24, 12), (.reg .X20, 19),
    (.reg .X21, 18), (.reg .X22, 17), (.reg .X23, 10), (.reg .X25, 13), (.reg .X26, 7)] ++
    FwK ++ [(.load 0 24 8, 15)]

/-- `b7`'s computed locations: fingerprint `1`. -/
def Q7e : List (Sym × Nat) := [(.reg .X29, 33), (.load 0 96 8, 32)]

/-- At `b8`: selector `1`. -/
def Q8 : List (Sym × Nat) := (.reg .X0, 42) :: (.reg .X1, 43) :: (Q7r ++ Q7e)

/-- At `b9`: term `1`. -/
def Q9 : List (Sym × Nat) := (.reg .X0, 52) :: (.reg .X1, 53) :: Q7r

/-- `b9`'s locations kept. -/
def Q9r : List (Sym × Nat) :=
  [(.reg .X27, 11), (.reg .X24, 12), (.reg .X20, 19), (.reg .X21, 18), (.reg .X22, 17),
    (.reg .X23, 10), (.reg .X25, 13), (.reg .X26, 7)] ++ FwK ++ [(.load 0 24 8, 15)]

/-- At `b10`, `b11`: the known part over two blocks. -/
def Q10 : List (Sym × Nat) := Q9r ++ [(.reg .X19, 62), (.reg .X28, 63)]

/-- `b11`'s locations kept. -/
def Q11r : List (Sym × Nat) :=
  [(.reg .X19, 62), (.reg .X28, 63), (.reg .X27, 11), (.reg .X24, 12), (.reg .X21, 18),
    (.reg .X22, 17), (.reg .X23, 10), (.reg .X25, 13)] ++ FwK ++ [(.load 0 24 8, 15)]

/-- `b11`'s computed locations: fingerprint `2`. -/
def Q11e : List (Sym × Nat) := [(.reg .X20, 34), (.reg .X26, 35)]

/-- At `b12`: selector `2`. -/
def Q12 : List (Sym × Nat) := (.reg .X0, 44) :: (.reg .X1, 45) :: (Q11r ++ Q11e)

/-- `b12`'s locations kept. -/
def Q12r : List (Sym × Nat) :=
  [(.reg .X19, 62), (.reg .X28, 63), (.reg .X27, 11), (.reg .X25, 10), (.reg .X21, 18),
    (.reg .X22, 17)] ++ FwK ++ [(.load 0 24 8, 15)]

/-- At `b13`: term `2`. -/
def Q13 : List (Sym × Nat) := (.reg .X0, 54) :: (.reg .X1, 55) :: Q12r

/-- `b13`'s locations kept. -/
def Q13r : List (Sym × Nat) :=
  [(.reg .X27, 11), (.reg .X25, 10), (.reg .X21, 18), (.reg .X22, 17)] ++ FwK ++
    [(.load 0 24 8, 15)]

/-- At `b14`: the known part in X19, X28. -/
def Q14 : List (Sym × Nat) :=
  [(.reg .X19, 66), (.reg .X28, 67), (.reg .X27, 11), (.reg .X25, 10), (.reg .X22, 17),
    (.reg .X21, 18)] ++ FwK ++ [(.load 0 24 8, 15)]

/-- At `b15`. -/
def Q15 : List (Sym × Nat) :=
  [(.reg .X19, 66), (.reg .X28, 67), (.reg .X27, 11), (.reg .X25, 10), (.reg .X29, 15),
    (.reg .X22, 17), (.reg .X21, 18)] ++ FwK

/-- The locations kept from `b15` on. -/
def QOr : List (Sym × Nat) :=
  [(.reg .X19, 6), (.reg .X23, 10), (.reg .X24, 11), (.reg .X26, 13), (.reg .X27, 4),
    (.reg .X28, 12), (.reg .X22, 17), (.reg .X21, 18)] ++ Fw0 ++
    [(.load 0 88 8, 8), (.load 0 96 8, 9)]

/-- At `b6`, `b16`: the tree's value plus the known part in X29 and the frame word at `32`. -/
def QO : List (Sym × Nat) := QOr ++ [(.reg .X29, 81), (.load 0 32 8, 80)]

/-- At `b17`: selector `0`. -/
def Q17 : List (Sym × Nat) := (.reg .X0, 40) :: (.reg .X1, 41) :: QO

/-- At `b18`: the ones over one block in X25, X20. -/
def Q18 : List (Sym × Nat) := [(.reg .X25, 72), (.reg .X20, 73)] ++ QO

/-- At `b19`: selector `1`. -/
def Q19 : List (Sym × Nat) := (.reg .X0, 42) :: (.reg .X1, 43) :: Q18

/-- At `b20`: the ones over two blocks. -/
def Q20 : List (Sym × Nat) := [(.reg .X25, 74), (.reg .X20, 75)] ++ QO

/-- At `b21`: selector `2`. -/
def Q21 : List (Sym × Nat) := (.reg .X0, 44) :: (.reg .X1, 45) :: Q20

/-- At `b22` and through the zeroing loop: the ones over the framework in X25, X20. -/
def QZ : List (Sym × Nat) := [(.reg .X25, 78), (.reg .X20, 79)] ++ QO

/-- `b24`'s locations kept. -/
def Q24r : List (Sym × Nat) :=
  [(.reg .X19, 6), (.reg .X23, 10), (.reg .X24, 11), (.reg .X26, 13), (.reg .X27, 4),
    (.reg .X28, 12)] ++ Fw0 ++
    [(.load 0 88 8, 8), (.load 0 96 8, 9), (.load 0 32 8, 80), (.load 0 136 8, 90),
      (.load 0 144 8, 91), (.load 0 24 8, 81)]

/-- At `b25`: the frame's `FormBuf`'s terms' address at `80`. -/
def Q25 : List (Sym × Nat) := Q24r ++ [(.load 0 80 8, 23)]

/-- At `b26`: the blocks' count in X29. -/
def Q26 : List (Sym × Nat) := Q25 ++ [(.reg .X29, 100)]

/-- `b26`'s locations kept. -/
def Q26r : List (Sym × Nat) :=
  [(.reg .X20, 12), (.reg .X26, 13), (.reg .X29, 100), (.load 0 16 8, 0), (.load 0 24 8, 81),
    (.load 0 32 8, 80), (.load 0 80 8, 23), (.load 0 88 8, 8), (.load 0 96 8, 9),
    (.load 0 104 8, 12), (.load 0 112 8, 13), (.load 0 136 8, 90), (.load 0 144 8, 91),
    (.load 0 64 8, 10), (.load 0 72 8, 11)]

/-- `b26`'s computed locations. -/
def Q26e : List (Sym × Nat) :=
  [(.reg .X12, 97), (.reg .X21, 93), (.reg .X22, 92), (.reg .X27, 98), (.reg .X28, 99),
    (.load 0 40 8, 21), (.load 0 48 8, 20), (.load 0 56 8, 22)]

end

public section

section
variable [Labels] {rs : List (BitVec 64 × Nat)} {V : Nat → UInt64} {D : List (Sym × Nat)}
  {m : MachineData}

/-- **A location described twice**, its value equal. -/
theorem Holds.dup (h : Holds rs V D m) {s : Sym} {i j : Nat} (hp : D.contains (s, i) = true)
    (hv : V i = V j) : Holds rs V ((s, j) :: D) m :=
  Holds.cons h ((h _ (List.contains_iff_mem.mp hp)).trans hv)

/-- A region's base plus an offset. -/
theorem ptr_eval {r : Nat} {b : BitVec 64} {n : Nat} (hb : rs[r]? = some (b, n)) {oi : Int}
    {o : Nat} (ho : oi = o) (vars : Nat → BitVec 64) :
    (Sym.ptr r oi).eval (Env.ofMachine m rs vars) = b + BitVec.ofNat 64 o := by
  subst ho
  simp only [Sym.eval]
  rw [Env.base_ofMachine m rs vars hb, BitVec.ofInt_natCast]

end

theorem ofBitVec_add (a : UInt64) (c : Nat) :
    UInt64.ofBitVec (a.toBitVec + BitVec.ofNat 64 c) = a + UInt64.ofNat c := rfl

theorem toBitVec_add (a : UInt64) (c : Nat) :
    (a + UInt64.ofNat c).toBitVec = a.toBitVec + BitVec.ofNat 64 c := rfl

/-- `EW::mul`'s operands: a selector and a fingerprint plus `side_beta`, limb by limb. -/
theorem mul_eq {s b f : EW} {x0 x1 x2 x3 : UInt64} (h0 : x0 = s.c0) (h1 : x1 = s.c1)
    (h2 : x2 = f.c0 ^^^ b.c0) (h3 : x3 = f.c1 ^^^ b.c1) :
    EW.mul ⟨x0, x1⟩ ⟨x2, x3⟩ = s * (b + f) := by
  subst h0 h1 h2 h3
  show EW.mul ⟨s.c0, s.c1⟩ ⟨f.c0 ^^^ b.c0, f.c1 ^^^ b.c1⟩ = EW.mul s (b + f)
  congr 1
  exact ew_ext (UInt64.xor_comm _ _) (UInt64.xor_comm _ _)

theorem apart_sub {a b : BitVec 64} {n m n' m' : Nat} (h : Apart a n b m) (hn : n' ≤ n)
    (hm : m' ≤ m) : Apart a n' b m' := by
  unfold Apart at *
  omega

section
variable [Labels] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW}

/-- **The frame and two more regions**, register `r1` the first's byte `o1`, `r2` the second's
base. -/
theorem matchRR (h : Pre L rows bl Fm SL m0) {m : MachineData}
    (hsp : m.regs.SP.toBitVec = base m0 F) {a1 a2 : BitVec 64} {n1 n2 : Nat} {r1 r2 : XReg}
    {o1 : Nat} (h1 : (m.regs.getXReg r1).toBitVec = a1 + BitVec.ofNat 64 o1)
    (h2 : (m.regs.getXReg r2).toBitVec = a2) :
    Match (Env.ofMachine m [(base m0 F, F + 0), (a1, n1), (a2, n2)])
      (init [(F + 0, true), (n1, false), (n2, false)] (.ptr 0 0)
        [(r1, .ptr 1 o1), (r2, .ptr 2 0)]) m :=
  match_ofMachine (sregions := [(F + 0, true), (n1, false), (n2, false)])
    (regions := [(base m0 F, F + 0), (a1, n1), (a2, n2)])
    ⟨rfl, fun _ ↦ Bus.base_aligned h.stack (by decide) rfl, rfl, nofun, rfl, nofun, trivial⟩
    (sp_eval hsp _ _)
    ⟨by dsimp only; rw [ptr_eval (rs := [(base m0 F, F + 0), (a1, n1), (a2, n2)]) rfl rfl, h1],
      by dsimp only; rw [ptr_eval (rs := [(base m0 F, F + 0), (a1, n1), (a2, n2)]) (oi := 0) (o := 0) rfl rfl, h2,
        add_zero'], trivial⟩
    trivial trivial trivial

/-- An environment of the frame and two more regions apart. -/
theorem wf2 (h : Pre L rows bl Fm SL m0) {m : MachineData} (hk : Kept m0.dmem m.dmem)
    {e1 e2 : BitVec 64 × Nat} (h1 : ROk m0 0 e1) (h2 : ROk m0 0 e2)
    (hap : Apart e1.1 e1.2 e2.1 e2.2) :
    (Env.ofMachine m [(base m0 F, F + 0), e1, e2]).WF :=
  wfB h hk (.inl rfl) (fun e he ↦ by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl
      · exact h1
      · exact h2)
    (List.Pairwise.cons (fun e he ↦ by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
      subst he; exact hap) (List.pairwise_singleton _ _))

omit [Labels] in
theorem busLayoutBytes_eq : busLayoutBytes = 888 := by decide

/-- The side layout's first `n` bytes, a block's region. -/
theorem rok_sl (h : Pre L rows bl Fm SL m0) {n : Nat} (hn : n ≤ 888) (hpos : 0 < n) :
    ROk m0 0 (m0.regs.X6.toBitVec, n) := by
  have := ROk.sub (o := 0) (n' := n) h.slOk (by rw [busLayoutBytes_eq]; omega) hpos
  rwa [add_zero'] at this

/-- The first `c` fingerprints, a block's region. -/
theorem rok_fp (h : Pre L rows bl Fm SL m0) {c : Nat} (hc : c ≤ nA m0) (hpos : 0 < c) :
    ROk m0 0 (m0.regs.X7.toBitVec, 16 * c) := by
  have := ROk.sub (o := 0) (n' := 16 * c) (h.fp (by omega)) (by omega) (by omega)
  rwa [add_zero'] at this

/-- The side layout's first `n` bytes and the first `c` fingerprints are apart. -/
theorem ap_sl_fp (h : Pre L rows bl Fm SL m0) {n c : Nat} (hn : n ≤ 888) (hc : c ≤ nA m0)
    (hpos : 0 < c) : Apart m0.regs.X6.toBitVec n m0.regs.X7.toBitVec (16 * c) :=
  apart_sub (h.slFp (by omega)) (by rw [busLayoutBytes_eq]; exact hn) (by omega)

/-- A word of the side layout in a state of the body. -/
theorem sl_word (h : Pre L rows bl Fm SL m0) {st : MachineData}
    (hfr : Fr m0 F N slots keep (outs m0) st) {o : Nat} (ho : o + 8 ≤ 888) :
    NativeRustcVm.wordOf st.dmem (m0.regs.X6.toBitVec + BitVec.ofNat 64 o) =
      NativeRustcVm.wordOf m0.dmem (m0.regs.X6.toBitVec + BitVec.ofNat 64 o) :=
  word_in h hfr h.slOk (NativeRustcVm.Apart.symm h.fSL) (by rw [busLayoutBytes_eq]; exact ho)

/-- A word of the fingerprints in a state of the body. -/
theorem fp_word (h : Pre L rows bl Fm SL m0) {st : MachineData}
    (hfr : Fr m0 F N slots keep (outs m0) st) (hn : 0 < nA m0) {o : Nat}
    (ho : o + 8 ≤ 16 * nA m0) :
    NativeRustcVm.wordOf st.dmem (m0.regs.X7.toBitVec + BitVec.ofNat 64 o) =
      NativeRustcVm.wordOf m0.dmem (m0.regs.X7.toBitVec + BitVec.ofNat 64 o) :=
  word_in h hfr (h.fp hn) (NativeRustcVm.Apart.symm (h.fFp hn)) ho

/-- The stack arguments' bytes in a state of the frame are the entry's. -/
theorem args_same (h : Pre L rows bl Fm SL m0) {st : MachineData}
    (hfr : Fr m0 F N slots keep (outs m0) st) : ∀ k, k + 8 ≤ 72 → ∀ i < 8,
      st.dmem.get? (m0.regs.SP.toBitVec + BitVec.ofNat 64 (k + i)) =
        m0.dmem.get? (m0.regs.SP.toBitVec + BitVec.ofNat 64 (k + i)) := by
  intro k hk i hi
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

/-- A stack argument's word where the bytes there are the entry's. -/
theorem argT {st : MachineData} (rest : List (BitVec 64 × Nat)) (k : Nat)
    (hs : ∀ i < 8, st.dmem.get? (m0.regs.SP.toBitVec + BitVec.ofNat 64 (k + i)) =
      m0.dmem.get? (m0.regs.SP.toBitVec + BitVec.ofNat 64 (k + i))) :
    tval ((base m0 F, F + 72) :: rest) st (.load 0 (12096 + k) 8) = stackArg m0 k := by
  unfold tval
  show UInt64.ofBitVec ((Env.ofMachine st _).load 0 (12096 + k) 8) = _
  rw [argLoad rest k hs]

/-- **The weights' stack arguments** in a state of the frame. -/
theorem holds_QArgs (h : Pre L rows bl Fm SL m0) {st : MachineData}
    (hfr : Fr m0 F N slots keep (outs m0) st) :
    Holds (rsA m0) (TT SL m0 L rows bl Fm 0) QArgs st := by
  intro p hp
  simp only [QArgs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact argT [] 8 (args_same h hfr 8 (by omega))
  · exact argT [] 16 (args_same h hfr 16 (by omega))

/-- **The entry's locations.** -/
theorem holds_QE : Holds (rsE m0) (sv m0) QE m0 := by
  intro p hp
  simp only [QE, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · unfold tval
    rw [ptr_eval (rs := rsE m0) (oi := 0) (o := 0) rfl rfl, add_zero']
    rfl
  · exact argT _ 0 fun _ _ ↦ rfl
  · exact argT _ 24 fun _ _ ↦ rfl
  · exact argT _ 32 fun _ _ ↦ rfl
  · exact argT _ 40 fun _ _ ↦ rfl
  · exact argT _ 48 fun _ _ ↦ rfl
  · exact argT _ 56 fun _ _ ↦ rfl
  · exact argT _ 64 fun _ _ ↦ rfl

end

end

end NativeRustcVmArm.Bus.AccumulateSide
