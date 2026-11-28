module

public import NativeRustcVmArm.Arrays.BufEW

/-!
# `Buf<u64, N>::extend` on AArch64

The same shape as `Buf<EW, N>::extend` (`NativeRustcVmArm.Arrays.BufEW`, whose states `entryS`,
`regsS`, returns `ret_block` and memory lemmas it reuses): `b0` returns `Some` for an empty `xs`
(`b4`); `b1` loads the count `c`, X9 = `c + 1`, X10 = `-N`, X8 = `8·|xs|`; the loop head `b2`
returns `None` (`b5`) when the buffer is full, else `b3` loads word `j` (X1 post-indexed), stores
it at `[x0, x9, lsl #3]` (entry `c + j`, placed by an alias of the address), stores the count and
loops while words remain, then returns `Some` (`b4`).

**`spec_of`**: from an instance's runs (`Runs`), `BufU64ExtendPre N`/`BufU64ExtendPost N`.
-/

namespace NativeRustcVmArm.Arrays.BufU64

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVm (wordsOf wordOf bufWordsOf BufWordsAt WordsAt WordAt)
open NativeRustcVmArm.Arrays.BufEW (entryS regsS keptRegs x11Sym buf src len cnt
  not_inRange_zero lt_of_noWrap same_of_regions01 wordAt_of_writeSym ret_block mem_keptRegs
  mem_keptRegs1)

@[expose] public section

/-- `b3`'s store address: `x0 + x9·8`. -/
def addrSym : Sym := .bin .add .W64 (.reg .X0) (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg .X9))

/-- A turn of the loop (`b3`): region 0 the entry written (at `addrSym`), 1 the count word (at
X0), 2 the word read (X1). -/
def bodyS : SState :=
  init [(8, false), (8, false), (8, false)] .sp [(.X1, .ptr 2 0)] [] []
    [(.reg .X0, 1, 0), (addrSym, 0, 0)]

/-- `b2`'s branch: the buffer full. -/
def c2 : SBool := .cmp .eq .W64 (.bin .add .W64 (.reg .X10) (.reg .X9)) (.lit 1)
/-- `b3`'s branch: words remain. -/
def c3 : SBool := .not (.cmp .eq .W64 (.reg .X8) (.lit 8))

/-- The loop head's registers `b2` keeps. -/
def loopRegs : List XReg := [.X8, .X9, .X10] ++ keptRegs

/-- The registers `b3` keeps. -/
def bodyRegs : List XReg := [.X0, .X2, .X10] ++ keptRegs.drop 3

/-- What the executor's runs of an instance's blocks give. -/
structure Runs [Host] (N : Nat) (b0 b1 b2 b3 b4 b5 : List Directive) (k k2 k3 k4 k5 : Nat)
    (l2 l4 l5 : Label) (S0 S1 S2 S3 S4 S5 : SState) : Prop where
  hb0 : b0.IsInfixAt Host.prog k
  hb1 : b1.IsInfixAt Host.prog (k + b0.length)
  hb2 : b2.IsInfixAt Host.prog k2
  hb3 : b3.IsInfixAt Host.prog k3
  hb4 : b4.IsInfixAt Host.prog k4
  hb5 : b5.IsInfixAt Host.prog k5
  e2 : k + b0.length + b1.length = k2
  e3 : k2 + b2.length = k3
  e4 : k3 + b3.length = k4
  hl2 : Labels.label l2 = Host.addrOf k2
  hl4 : Labels.label l4 = Host.addrOf k4
  hl5 : Labels.label l5 = Host.addrOf k5
  x0 : exec b0 entryS = some (S0, .cond BufEW.c0 l4)
  x1 : exec b1 S0 = some (S1, .fall)
  x2 : exec b2 regsS = some (S2, .cond c2 l5)
  x3 : exec b3 bodyS = some (S3, .cond c3 l2)
  x4 : exec b4 regsS = some (S4, .ret)
  x5 : exec b5 regsS = some (S5, .ret)
  f0 : keepsAll entryS S0 keptRegs = true
  f1 : S1.reg .X8 = some (.un (.ubfm 61 60) .W64 (.reg .X2)) ∧
    S1.reg .X9 = some (.bin .add .W64 (.load 0 0 8) (.lit 1)) ∧
    S1.reg .X10 = some (x11Sym N) ∧ keepsAll entryS S1 keptRegs = true
  f2 : keepsAll regsS S2 loopRegs = true
  f3 : S3.reg .X1 = some (.ptr 2 8) ∧ S3.reg .X8 = some (.bin .sub .W64 (.reg .X8) (.lit 8)) ∧
    S3.reg .X9 = some (.bin .add .W64 (.reg .X9) (.lit 1)) ∧
    keepsAll bodyS { S3 with mem := [] } bodyRegs = true ∧
    (∀ w ∈ S3.mem, (w.r = 0 ∧ w.off + w.n ≤ 8) ∨ (w.r = 1 ∧ w.off + w.n ≤ 8)) ∧
    (∀ i < 8, findWrite 0 (0 + i) S3.mem = some (.load 2 0 8, i)) ∧
    (∀ i < 8, findWrite 1 (0 + i) S3.mem = some (.reg .X9, i))
  f4 : S4.reg .X0 = some (.lit 1) ∧ keepsAll regsS S4 (keptRegs.drop 1) = true
  f5 : S5.reg .X0 = some (.lit 0) ∧ keepsAll regsS S5 (keptRegs.drop 1) = true

end

public section

/-- `xs`'s words. -/
abbrev ws (m : MachineData) : List UInt64 := wordsOf m.dmem (src m) (len m)

/-- **The loop head**, `j` words copied. -/
structure WInv (N : Nat) (m0 : MachineData) (j : Nat) (s : MachineData) : Prop where
  lt : j < len m0
  le : cnt m0 + j ≤ N
  x0 : s.regs.X0 = m0.regs.X0
  x1 : s.regs.X1.toBitVec = src m0 + BitVec.ofNat 64 (8 * j)
  x8 : s.regs.X8.toBitVec = BitVec.ofNat 64 (8 * (len m0 - j))
  x9 : s.regs.X9.toNat = cnt m0 + j + 1
  x10 : s.regs.X10.toBitVec = BitVec.ofNat 64 (2 ^ 64 - N)
  x30 : s.regs.X30 = m0.regs.X30
  saved : Saved m0 s
  same : Changes m0 s bufExtendStack (buf m0) (8 + 8 * N)
  count : WordAt s.dmem (buf m0) (cnt m0 + j).toUInt64
  ents : WordsAt s.dmem (buf m0 + 8#64) (bufWordsOf m0.dmem (buf m0) ++ (ws m0).take j)

/-- The postcondition, reached. -/
abbrev Post (N : Nat) (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ BufU64ExtendPost N m0 s.data

theorem lsl3 (x : BitVec 64) : UnOp.apply (.ubfm 61 60) .W64 x = BitVec.ofNat 64 (8 * x.toNat) := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  apply BitVec.eq_of_toNat_eq
  simp [evalUBFM, toNat_take', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem memExt3 (v : BitVec 64) :
    (UnOp.apply (.memExtend ⟨.UXTX, .E3⟩) .W64 v).toNat = v.toNat * 8 % 2 ^ 64 := by
  simp only [UnOp.apply, BitVec.apply_mem_extend, BitVec.unsigned, BitVec.toNat_ofInt,
    Int.shiftLeft_eq]
  omega

theorem mem_bodyRegs {r : XReg} (h : calleeSaved r = true) : r ∈ bodyRegs := by
  cases r <;> first | exact absurd h (by decide) | simp [bodyRegs, keptRegs]

theorem mem_loopRegs {r : XReg} (h : calleeSaved r = true) : r ∈ loopRegs :=
  List.mem_append_right _ (mem_keptRegs h)

/-- The buffer at the entry. -/
theorem bufWordsAt_entry {N : Nat} {m0 : MachineData} (hc : cnt m0 ≤ N)
    (hm : Mapped m0.dmem (buf m0) (8 + 8 * N)) :
    BufWordsAt m0.dmem (buf m0) N (bufWordsOf m0.dmem (buf m0)) := by
  have hc' : (wordOf m0.dmem (buf m0)).toNat ≤ N := hc
  refine ⟨by simp [bufWordsOf]; exact hc, ?_, ?_⟩
  · simp only [bufWordsOf, NativeRustcVm.length_wordsOf, Nat.toUInt64_eq, UInt64.ofNat_toNat]
    exact NativeRustcVm.wordAt_of_mapped fun i hi ↦ hm i (by omega)
  · refine NativeRustcVm.wordsAt_of_mapped fun i hi ↦ ?_
    rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add]
    exact hm _ (by omega)

theorem post_of {N : Nat} {m0 s s' : MachineData}
    (hsame : Changes m0 s bufExtendStack (buf m0) (8 + 8 * N))
    (hsaved : Saved m0 s) (hdm : s'.dmem = s.dmem) (hs' : Saved s s') :
    Changes m0 s' bufExtendStack (buf m0) (8 + 8 * N) ∧ Saved m0 s' :=
  ⟨fun p hp ↦ by rw [hdm]; exact hsame p hp, hsaved.trans hs'⟩

variable [Host] {N : Nat} {b0 b1 b2 b3 b4 b5 : List Directive} {k k2 k3 k4 k5 : Nat}
  {l2 l4 l5 : Label} {S0 S1 S2 S3 S4 S5 : SState}

/-- **A turn of the loop**: the buffer full and `None` returned, or word `j` copied, then back at
the head or `Some` returned. -/
theorem step (R : Runs N b0 b1 b2 b3 b4 b5 k k2 k3 k4 k5 l2 l4 l5 S0 S1 S2 S3 S4 S5)
    {m0 : MachineData} (hpre : BufU64ExtendPre N m0) {j : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf k2) (hI : WInv N m0 j s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ Post N m0 s' ∨
      (s'.pc = Host.addrOf k2 ∧ WInv N m0 (j + 1) s'.data)) s := by
  obtain ⟨hc, ⟨hmB, hnB⟩, ⟨hmS, hnS⟩, hap⟩ := hpre
  have aC : (wordOf m0.dmem m0.regs.X0.toBitVec).toNat = cnt m0 := rfl
  have aC' : (wordOf m0.dmem (buf m0)).toNat = cnt m0 := rfl
  have aB : m0.regs.X0.toBitVec.toNat = (buf m0).toNat := rfl
  have aS : m0.regs.X1.toBitVec.toNat = (src m0).toNat := rfl
  have aL : m0.regs.X2.toNat = len m0 := rfl
  have hnB' : (buf m0).toNat + (8 + 8 * N) ≤ 2 ^ 64 := hnB
  have hnS' : (src m0).toNat + 8 * len m0 ≤ 2 ^ 64 := hnS
  have hN := lt_of_noWrap hnB
  have hlt := hI.lt
  have hle := hI.le
  have hlS := lt_of_noWrap hnS
  refine exec_at R.hb2 R.x2 (Env.wf_nil _) hpc (match_nil _) fun s2 hm2 hpc2 ↦ ?_
  have hk2 := R.f2
  simp only [keepsAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.isEmpty_iff] at hk2
  obtain ⟨⟨hr2, hsp2⟩, hmem2⟩ := hk2
  have e2 : ∀ r ∈ loopRegs, s2.data.regs.getXReg r = s.data.regs.getXReg r := fun r hr' ↦ by
    obtain ⟨hs, he⟩ := hr2 r hr'
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    exact Match.reg_eq (match_nil _) hm2 hv (he.trans hv)
  have hdm2 : s2.data.dmem = s.data.dmem := hm2.dmem_eq (Env.wf_nil _) hmem2
  have hsv2 : Saved s.data s2.data :=
    ⟨fun r hr ↦ e2 r (mem_loopRegs hr),
      Match.sp_eq (match_nil _) hm2 hsp2, by rw [hdm2]; exact fun _ h ↦ h⟩
  simp only [PcOk, c2] at hpc2
  sym_simp at hpc2
  have hpc2' := pc_cond hpc2
  have hfull : ((s.data.regs.getXReg .X10).toBitVec + (s.data.regs.getXReg .X9).toBitVec ==
      BitVec.ofNat 64 1) = true ↔ cnt m0 + j = N := by
    rw [beq_iff_eq]
    show s.data.regs.X10.toBitVec + s.data.regs.X9.toBitVec = _ ↔ _
    rw [hI.x10]
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      have h9 := hI.x9
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, UInt64.toNat_toBitVec] at h'
      omega
    · intro h
      apply BitVec.eq_of_toNat_eq
      have h9 := hI.x9
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, UInt64.toNat_toBitVec]
      omega
  by_cases hF : cnt m0 + j = N
  · -- the buffer full: `None`.
    have hpc2 := (hpc2'.1 (hfull.mpr hF)).trans R.hl5
    refine Eventually.mono (ret_block R.hb5 R.x5 R.f5 hpc2) fun s' ⟨h1, h2, h3, h4⟩ ↦ Or.inl ?_
    obtain ⟨hc', hs'⟩ := post_of hI.same hI.saved (h3.trans hdm2) (hsv2.trans h4)
    refine ⟨by rw [h1]; simp only [retOf]; rw [show s2.data.regs.X30 = s.data.regs.X30 from
      e2 .X30 (by simp [loopRegs, keptRegs]), hI.x30], ?_, hc', hs'⟩
    split
    · rename_i hn; exfalso; omega
    · rw [h2]; rfl
  have hpc3 := hpc2'.2 (fun h ↦ hF (hfull.mp h))
  rw [R.e3] at hpc3
  -- the turn: three regions
  have hcj : cnt m0 + j < N := by omega
  let dst : BitVec 64 := buf m0 + BitVec.ofNat 64 (8 + 8 * (cnt m0 + j))
  let sj : BitVec 64 := src m0 + BitVec.ofNat 64 (8 * j)
  have hkept : Kept m0.dmem s2.data.dmem := by rw [hdm2]; exact hI.saved.2.2
  have hnD : NoWrap dst 8 := by
    unfold NoWrap; rw [toNat_add_ofNat' (by omega)]; omega
  have hnC : NoWrap (buf m0) 8 := by unfold NoWrap; omega
  have hnJ : NoWrap sj 8 := by
    unfold NoWrap; rw [toNat_add_ofNat' (by omega)]; omega
  have hmD : Mapped s2.data.dmem dst 8 := fun i hi ↦ by
    rw [NativeRustcVm.addr_add]; exact hkept _ (hmB _ (by omega))
  have hmC : Mapped s2.data.dmem (buf m0) 8 := fun i hi ↦ hkept _ (hmB _ (by omega))
  have hmJ : Mapped s2.data.dmem sj 8 := fun i hi ↦ by
    rw [NativeRustcVm.addr_add]; exact hkept _ (hmS _ (by omega))
  have hdD : (dst).toNat = (buf m0).toNat + 8 + 8 * (cnt m0 + j) := by
    rw [toNat_add_ofNat' (by omega)]; omega
  have hdJ : (sj).toNat = (src m0).toNat + 8 * j := by
    rw [toNat_add_ofNat' (by omega)]
  have hap' : (buf m0).toNat + (8 + 8 * N) ≤ (src m0).toNat ∨
      (src m0).toNat + 8 * len m0 ≤ (buf m0).toNat := hap
  have hwf : (Env.ofMachine s2.data [(dst, 8), (buf m0, 8), (sj, 8)]).WF := by
    refine Env.wf_of ⟨⟨hmD, hnD⟩, ⟨hmC, hnC⟩, ⟨hmJ, hnJ⟩, trivial⟩ ?_
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons nofun .nil))
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · show Apart dst 8 (buf m0) 8
        unfold Apart; omega
      · show Apart dst 8 sj 8
        unfold Apart; omega
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      subst he
      show Apart (buf m0) 8 sj 8
      unfold Apart; omega
  have h9 : (s2.data.regs.getXReg .X9).toNat = cnt m0 + j + 1 := by
    rw [e2 .X9 (by simp [loopRegs])]; exact hI.x9
  have hm3 : Match (Env.ofMachine s2.data [(dst, 8), (buf m0, 8), (sj, 8)]) bodyS s2.data := by
    refine match_ofMachine ⟨rfl, nofun, rfl, nofun, rfl, nofun, trivial⟩ rfl ⟨?_, trivial⟩
      trivial trivial ⟨?_, ?_, trivial⟩
    · show (s2.data.regs.getXReg .X1).toBitVec = sj + BitVec.ofInt 64 0
      rw [e2 .X1 (by simp [loopRegs, keptRegs])]
      show s.data.regs.X1.toBitVec = _
      rw [hI.x1]; exact (BitVec.add_zero _).symm
    · show (s2.data.regs.getXReg .X0).toBitVec = buf m0 + BitVec.ofInt 64 0
      rw [e2 .X0 (by simp [loopRegs, keptRegs])]
      show s.data.regs.X0.toBitVec = _
      rw [hI.x0]; exact (BitVec.add_zero _).symm
    · show addrSym.eval (Env.ofMachine s2.data [(dst, 8), (buf m0, 8), (sj, 8)]) =
        (Env.ofMachine s2.data [(dst, 8), (buf m0, 8), (sj, 8)]).base 0 + BitVec.ofInt 64 0
      simp only [addrSym, Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs,
        base0]
      rw [e2 .X0 (by simp [loopRegs, keptRegs]), show BitVec.ofInt 64 0 = 0#64 from rfl,
        BitVec.add_zero]
      show s.data.regs.X0.toBitVec + _ = _
      rw [hI.x0]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, memExt3]
      simp only [UInt64.toNat_toBitVec]
      rw [h9, hdD]
      have aB2 : m0.regs.X0.toNat = (buf m0).toNat := rfl
      omega
  refine exec_at R.hb3 R.x3 hwf hpc3 hm3 fun s3 hm3' hpc3' ↦ ?_
  obtain ⟨g1, g8, g9, gk, gw, gw0, gw2⟩ := R.f3
  have gk' := gk
  simp only [keepsAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.isEmpty_iff] at gk'
  obtain ⟨⟨gr, gsp⟩, -⟩ := gk'
  have e3 : ∀ r ∈ bodyRegs, s3.data.regs.getXReg r = s2.data.regs.getXReg r :=
    fun r hr' ↦ by
      obtain ⟨hs, he⟩ := gr r hr'
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
      exact Match.reg_eq hm3 hm3' hv (he.trans hv)
  have hsv3 : Saved s2.data s3.data :=
    ⟨fun r hr ↦ e3 r (mem_bodyRegs hr), Match.sp_eq hm3 hm3' gsp, hm3'.kept hwf⟩
  have hsame3 := same_of_regions01 hm3' hwf gw
  -- the word read, unchanged since the entry
  have hJ : wordOf s2.data.dmem sj = (ws m0)[j]'(by simp; exact hlt) := by
    rw [NativeRustcVm.getElem_wordsOf]
    refine NativeRustcVm.wordOf_congr fun i hi ↦ ?_
    rw [NativeRustcVm.addr_add, hdm2]
    refine hI.same _ fun h ↦ h.elim (fun h ↦ ?_) (not_inRange_zero _ _)
    have hp : (src m0 + BitVec.ofNat 64 (8 * j + i)).toNat = (src m0).toNat + (8 * j + i) :=
      toNat_add_ofNat' (by omega)
    rw [inRange_iff hnB] at h
    omega
  -- the entry written
  have hD : WordAt s3.data.dmem dst ((ws m0)[j]'(by simp; exact hlt)) := by
    rw [← hJ]
    have a0 := wordAt_of_writeSym hm3' (r := 0) rfl (by decide) gw0
    have l0 : (Sym.load 2 0 8).eval (Env.ofMachine s2.data [(dst, 8), (buf m0, 8), (sj, 8)]) =
        (wordOf s2.data.dmem sj).toBitVec := by
      show Env.load _ 2 0 8 = _
      rw [load8_eq, add_ofNat_zero]; rfl
    rw [l0, UInt64.ofBitVec_toBitVec, add_ofNat_zero] at a0
    exact a0
  -- the count written
  have hC : WordAt s3.data.dmem (buf m0) (cnt m0 + j + 1).toUInt64 := by
    have a := wordAt_of_writeSym hm3' (r := 1) rfl (by decide) gw2
    simp only [Sym.eval, Env.ofMachine_regs, add_ofNat_zero, UInt64.ofBitVec_toBitVec] at a
    rw [show s2.data.regs.getXReg .X9 = (cnt m0 + j + 1).toUInt64 by
      apply UInt64.toNat_inj.mp
      rw [h9, Nat.toUInt64_eq, UInt64.toNat_ofNat']
      exact (Nat.mod_eq_of_lt (by omega)).symm] at a
    exact a
  have hlen0 : (bufWordsOf m0.dmem (buf m0) ++ (ws m0).take j).length = cnt m0 + j := by
    simp [bufWordsOf]; omega
  have hE : WordsAt s3.data.dmem (buf m0 + 8#64)
      (bufWordsOf m0.dmem (buf m0) ++ (ws m0).take (j + 1)) := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp; exact hlt), Option.toList_some,
      ← List.append_assoc, NativeRustcVm.wordsAt_append, NativeRustcVm.wordsAt_singleton, hlen0]
    constructor
    · refine bytesAt_congr hI.ents fun i hi ↦ ?_
      have hl : ((bufWordsOf m0.dmem (buf m0) ++ (ws m0).take j).flatMap
          NativeRustcVm.wordBytes).length = 8 * (cnt m0 + j) := by
        rw [List.length_flatMap]; simp [NativeRustcVm.length_wordBytes, bufWordsOf]; omega
      rw [hl] at hi
      have hp : (buf m0 + BitVec.ofNat 64 (8 + i)).toNat = (buf m0).toNat + (8 + i) :=
        toNat_add_ofNat' (by omega)
      rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add]
      rw [hsame3 _ ?_ ?_, hdm2]
      · rw [inRange_iff hnD]; omega
      · rw [inRange_iff hnC]; omega
    · rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add]
      exact hD
  have hsameT : Changes m0 s3.data bufExtendStack (buf m0) (8 + 8 * N) := fun p hp ↦ by
    have hp' : ¬InRange (buf m0) (8 + 8 * N) p := fun h ↦ hp (Or.inl h)
    rw [hsame3 p (fun h ↦ hp' ?_) (fun h ↦ hp' ?_), hdm2]
    · exact hI.same p hp
    · rw [inRange_iff hnD] at h; rw [inRange_iff hnB]; omega
    · rw [inRange_iff hnC] at h; rw [inRange_iff hnB]; omega
  have hsv : Saved m0 s3.data := hI.saved.trans (hsv2.trans hsv3)
  have hx30 : s3.data.regs.X30 = m0.regs.X30 := by
    rw [show s3.data.regs.X30 = s2.data.regs.getXReg .X30 from e3 .X30 (by simp [bodyRegs, keptRegs]),
      e2 .X30 (by simp [loopRegs, keptRegs])]
    exact hI.x30
  -- the loop test
  have q8 : (s3.data.regs.getXReg .X8).toBitVec = BitVec.ofNat 64 (8 * (len m0 - (j + 1))) := by
    rw [hm3'.regs .X8 _ g8]
    sym_simp
    rw [Env.ofMachine_regs, e2 .X8 (by simp [loopRegs])]
    show s.data.regs.X8.toBitVec - _ = _
    rw [hI.x8]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  simp only [PcOk, c3] at hpc3'
  sym_simp at hpc3'
  have hpc3'' := pc_cond hpc3'
  have hmore : ((!((s2.data.regs.getXReg .X8).toBitVec == BitVec.ofNat 64 8)) = true) ↔
      j + 1 < len m0 := by
    rw [Bool.not_eq_true', beq_eq_false_iff_ne, e2 .X8 (by simp [loopRegs])]
    show s.data.regs.X8.toBitVec ≠ _ ↔ _
    rw [hI.x8]
    constructor
    · intro h
      by_contra h'
      exact h (by rw [show 8 * (len m0 - j) = 8 by omega])
    · intro h h'
      have := congrArg BitVec.toNat h'
      simp only [BitVec.toNat_ofNat] at this
      omega
  by_cases hM : j + 1 < len m0
  · have hpc4 := (hpc3''.1 (hmore.mpr hM)).trans R.hl2
    refine .done _ (Or.inr ⟨hpc4, hM, by omega, ?_, ?_, q8, ?_, ?_, hx30, hsv, hsameT, ?_, hE⟩)
    · show s3.data.regs.getXReg .X0 = _
      rw [e3 .X0 (by simp [bodyRegs]), e2 .X0 (by simp [loopRegs, keptRegs])]
      exact hI.x0
    · rw [show s3.data.regs.X1.toBitVec = (s3.data.regs.getXReg .X1).toBitVec from rfl,
        hm3'.regs .X1 _ g1]
      show src m0 + BitVec.ofNat 64 (8 * j) + BitVec.ofInt 64 8 = _
      rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add,
        show 8 * j + 8 = 8 * (j + 1) by omega]
    · show (s3.data.regs.getXReg .X9).toNat = _
      rw [← UInt64.toNat_toBitVec, hm3'.regs .X9 _ g9]
      sym_simp
      rw [Env.ofMachine_regs, BitVec.toNat_add, UInt64.toNat_toBitVec, h9, BitVec.toNat_ofNat]
      omega
    · show (s3.data.regs.getXReg .X10).toBitVec = _
      rw [e3 .X10 (by simp [bodyRegs]), e2 .X10 (by simp [loopRegs])]
      exact hI.x10
    · rw [show cnt m0 + (j + 1) = cnt m0 + j + 1 by omega]; exact hC
  · have hpc4 := hpc3''.2 (fun h ↦ hM (hmore.mp h))
    rw [R.e4] at hpc4
    refine Eventually.mono (ret_block R.hb4 R.x4 R.f4 hpc4) fun s' ⟨h1, h2, h3, h4⟩ ↦ Or.inl ?_
    have hj : j + 1 = len m0 := by omega
    obtain ⟨hc', hs'⟩ := post_of hsameT hsv h3 h4
    refine ⟨by rw [h1]; simp only [retOf]; rw [hx30], ?_, hc', hs'⟩
    split
    rotate_left
    · rename_i hn; exfalso; omega
    refine ⟨by rw [h2]; rfl, ?_, ?_, ?_⟩
    · simp [bufWordsOf]; omega
    · rw [h3]
      have : (bufWordsOf m0.dmem (buf m0) ++ ws m0).length = cnt m0 + j + 1 := by
        simp [bufWordsOf]; omega
      rw [this]; exact hC
    · show WordsAt _ _ (bufWordsOf m0.dmem (buf m0) ++ ws m0)
      rw [h3, ← List.take_of_length_le (l := ws m0) (i := j + 1) (by simp; omega)]
      exact hE

/-- **`Buf<u64, N>::extend` meets its contract**, from an instance's runs. -/
theorem spec_of (R : Runs N b0 b1 b2 b3 b4 b5 k k2 k3 k4 k5 l2 l4 l5 S0 S1 S2 S3 S4 S5)
    {l0 : Label} (hl0 : Labels.label l0 = Host.addrOf k) :
    Spec (Labels.label l0) (BufU64ExtendPre N) (BufU64ExtendPost N) := by
  intro m0 hpre
  rw [hl0]
  have hpre' := hpre
  obtain ⟨hc, ⟨hmB, hnB⟩, ⟨hmS, hnS⟩, hap⟩ := hpre
  have aC : (wordOf m0.dmem m0.regs.X0.toBitVec).toNat = cnt m0 := rfl
  have aC' : (wordOf m0.dmem (buf m0)).toNat = cnt m0 := rfl
  have aB : m0.regs.X0.toBitVec.toNat = (buf m0).toNat := rfl
  have aS : m0.regs.X1.toBitVec.toNat = (src m0).toNat := rfl
  have aL : m0.regs.X2.toNat = len m0 := rfl
  have hnB' : (buf m0).toNat + (8 + 8 * N) ≤ 2 ^ 64 := hnB
  have hnS' : (src m0).toNat + 8 * len m0 ≤ 2 ^ 64 := hnS
  have hN := lt_of_noWrap hnB
  have hwf : (Env.ofMachine m0 [(buf m0, 8)]).WF :=
    wf_one (fun i hi ↦ hmB i (by omega)) (by unfold NoWrap; omega)
  have hm : Match (Env.ofMachine m0 [(buf m0, 8)]) entryS m0 :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl ⟨(BitVec.add_zero _).symm, trivial⟩ trivial trivial
      trivial
  refine exec_then R.hb0 R.x0 hwf hm fun s1 hm1 hpc1 ↦ ?_
  simp only [PcOk, BufEW.c0] at hpc1
  sym_simp at hpc1
  have hpc1' := pc_cond hpc1
  have hk0 := R.f0
  simp only [keepsAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.isEmpty_iff] at hk0
  obtain ⟨⟨hr0, hsp0⟩, hmem0⟩ := hk0
  have e1 : ∀ r ∈ keptRegs, s1.data.regs.getXReg r = m0.regs.getXReg r := fun r hr' ↦ by
    obtain ⟨hs, he⟩ := hr0 r hr'
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    exact Match.reg_eq hm hm1 hv (he.trans hv)
  have hdm1 : s1.data.dmem = m0.dmem := hm1.dmem_eq hwf hmem0
  have hsv1 : Saved m0 s1.data :=
    ⟨fun r hr ↦ e1 r (mem_keptRegs hr),
      Match.sp_eq hm hm1 hsp0, by rw [hdm1]; exact fun _ h ↦ h⟩
  by_cases hz : len m0 = 0
  · -- `xs` empty: `Some`.
    have hpc1 := (hpc1'.1 (by
      show ((m0.regs.getXReg .X2).toBitVec == 0#64) = true
      rw [beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      exact hz)).trans R.hl4
    refine Eventually.mono (ret_block R.hb4 R.x4 R.f4 hpc1) fun s' ⟨h1, h2, h3, h4⟩ ↦ ?_
    refine ⟨by rw [h1]; simp only [retOf]; rw [show s1.data.regs.X30 = m0.regs.X30 from
      e1 .X30 (by simp [keptRegs])], ?_, fun p _ ↦ by rw [h3, hdm1], hsv1.trans h4⟩
    split
    rotate_left
    · rename_i hn; exfalso; omega
    refine ⟨by rw [h2]; rfl, ?_⟩
    rw [h3, hdm1, show wordsOf m0.dmem m0.regs.X1.toBitVec m0.regs.X2.toNat = [] from
      List.eq_nil_of_length_eq_zero (by simp; exact hz), List.append_nil]
    exact bufWordsAt_entry hc hmB
  · have hpc1 := hpc1'.2 (by
      show ¬((m0.regs.getXReg .X2).toBitVec == 0#64) = true
      rw [beq_iff_eq]
      intro h
      exact hz (congrArg BitVec.toNat h))
    refine exec_at R.hb1 R.x1 hwf hpc1 hm1 fun s2 hm2 hpc2 ↦ ?_
    simp only [PcOk, R.e2] at hpc2
    obtain ⟨g8, g9, g10, gk⟩ := R.f1
    have gk' := gk
    simp only [keepsAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.isEmpty_iff] at gk'
    obtain ⟨⟨gr, gsp⟩, gmem⟩ := gk'
    have e2 : ∀ r ∈ keptRegs, s2.data.regs.getXReg r = m0.regs.getXReg r := fun r hr' ↦ by
      obtain ⟨hs, he⟩ := gr r hr'
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
      exact Match.reg_eq hm hm2 hv (he.trans hv)
    have hdm2 : s2.data.dmem = m0.dmem := hm2.dmem_eq hwf gmem
    have hc' : (wordOf m0.dmem (buf m0)).toNat ≤ N := hc
    have hc8 : (wordOf m0.dmem (buf m0)).toNat < 2 ^ 61 := by omega
    have hload : (Env.ofMachine m0 [(buf m0, 8)]).load 0 0 8 = (wordOf m0.dmem (buf m0)).toBitVec := by
      rw [load8_eq]; simp
    refine Sym.loop (fun n s ↦ s.pc = Host.addrOf k2 ∧ ∃ j, len m0 - j = n ∧ WInv N m0 j s.data)
      (fun n s ⟨hpc, j, hn, hI⟩ ↦ ?_) ⟨hpc2, 0, rfl, ?inv⟩
    case inv =>
      refine ⟨Nat.pos_of_ne_zero hz, by simpa using hc, ?_, ?_, ?_, ?_, ?_, ?_, hsv1.trans ?_,
        ?_, ?_, ?_⟩
      · exact e2 .X0 (by simp [keptRegs])
      · show (s2.data.regs.getXReg .X1).toBitVec = _
        rw [e2 .X1 (by simp [keptRegs])]
        exact (BitVec.add_zero _).symm
      · rw [show s2.data.regs.X8.toBitVec = (s2.data.regs.getXReg .X8).toBitVec from rfl,
          hm2.regs .X8 _ g8]
        simp only [Sym.eval, Env.ofMachine_regs, lsl3]
        rfl
      · show (s2.data.regs.getXReg .X9).toNat = _
        rw [← UInt64.toNat_toBitVec, hm2.regs .X9 _ g9]
        sym_simp
        rw [hload, BitVec.toNat_add, BitVec.toNat_ofNat, UInt64.toNat_toBitVec]
        omega
      · show (s2.data.regs.getXReg .X10).toBitVec = _
        rw [hm2.regs .X10 _ g10]
        simp only [x11Sym]
        sym_simp
        rw [hload]
        have hb : (!(wordOf m0.dmem (buf m0)).toBitVec.ult (BitVec.ofNat 64 N) &&
            !((wordOf m0.dmem (buf m0)).toBitVec == BitVec.ofNat 64 N)) = false := by
          rw [Bool.and_eq_false_iff]
          by_cases h : cnt m0 < N
          · left
            rw [Bool.not_eq_false', BitVec.ult_iff_lt, BitVec.lt_def, BitVec.toNat_ofNat,
              UInt64.toNat_toBitVec]
            omega
          · right
            rw [Bool.not_eq_false', beq_iff_eq]
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_ofNat, UInt64.toNat_toBitVec]
            omega
        rw [ite_bool, hb, Bool.cond_false]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, MemWidth.bits]
        omega
      · exact e2 .X30 (by simp [keptRegs])
      · exact ⟨fun r hr ↦ (e2 r (mem_keptRegs hr)).trans (e1 r (mem_keptRegs hr)).symm,
          (Match.sp_eq hm hm2 gsp).trans (Match.sp_eq hm hm1 hsp0).symm,
          by rw [hdm2, hdm1]; exact fun _ h ↦ h⟩
      · intro p _; rw [hdm2]
      · rw [hdm2, Nat.add_zero, Nat.toUInt64_eq, UInt64.ofNat_toNat]
        exact NativeRustcVm.wordAt_of_mapped fun i hi ↦ hmB i (by omega)
      · rw [hdm2, List.take_zero, List.append_nil]
        exact (bufWordsAt_entry hc hmB).2.2
    refine Eventually.mono (step R hpre' hpc hI) fun s' h ↦ ?_
    rcases h with h | ⟨hpc', hI'⟩
    · exact Or.inl h
    · exact Or.inr ⟨len m0 - (j + 1), by have := hI'.lt; omega, hpc', j + 1, rfl, hI'⟩

end

end NativeRustcVmArm.Arrays.BufU64
