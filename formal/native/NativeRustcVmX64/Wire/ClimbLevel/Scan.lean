module

public import NativeRustcVmX64.Wire.ClimbLevel.Head

/-!
# `climb_level`'s scan for a sibling (x86-64)

The regions of a block beside the frame (`Geo.wf_rest`, `Geo.nd_area`, `Geo.sb_area`,
`Geo.pa_area`); node `i`'s state during its step (`Cur`); a node's key word (`key_word`). From the
scan's head at node `j` (`b5`): past the last node, the sibling read (`Rd`); else `b6` compares
node `j`'s key with node `i`'s: the sibling found (`Fnd`) or the next node: `scan_step`.
-/

namespace NativeRustcVmX64.Wire.ClimbLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.ClimbLevel
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap
  Frame.of_block after after_eq MidOk)
open NativeRustcVm.Transcript (Mapped.keeps off off_zero off_add off_off toNat_off)
open NativeRustcVm (WordAt WordsAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open NativeRustcVmX64.Wire (pc_cond ite_t ite_f eq64 ult64 toNat_add64)

@[expose] public section

variable [Host] (k : Nat) (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c : Nat)
  (ns : List (Nat × Digest))

/-- Node `i`'s state during its step: the frame, the memory after `i` nodes, node `i + 1` at
`72`/`80`, the registers. -/
structure Cur (i : Nat) (sl : List (Nat × Digest × Bool)) (ci : Nat) (m : MachineData) : Prop where
  fr : Frame m0 208 slots 8 m
  hs : sibsM B ns (ns.take i) c = some (sl, ci)
  mm : MemS m0 bp B ns (sn sl) (parentsOf (ns.take i) sl) ci m.dmem
  nx : Nx m0 (i + 1) m.dmem
  lt : i < cnt m0
  rbp : reg m .rbp = nd m0 i
  r12 : reg m .r12 = BitVec.ofNat 64 i
  rbx : reg m .rbx = BitVec.ofNat 64 (parentsOf (ns.take i) sl).length
  r14 : reg m .r14 = nxt m0
  r15 : reg m .r15 = sibs m0

/-- **The sibling found** (`b7`): node `j`, the first of node `i`'s key `^^^ 1`, at RAX. -/
structure Fnd (i : Nat) (sl : List (Nat × Digest × Bool)) (ci j : Nat) (st : MachineState) :
    Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ClimbLevel.b7Offset)
  cur : Cur m0 bp B c ns i sl ci st.data
  hi : i < ns.length
  hj : j < ns.length
  kj : (ns[j]'hj).1 = (ns[i]'hi).1 ^^^ 1
  miss : Miss ns i j
  rax : reg st.data .rax = nd m0 j
  r13 : reg st.data .r13 = BitVec.ofNat 64 (ns[i]'hi).1

/-- **No node is node `i`'s sibling** (`b10`): the sibling read. -/
structure Rd (i : Nat) (sl : List (Nat × Digest × Bool)) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ClimbLevel.b10Offset)
  cur : Cur m0 bp B c ns i sl ci st.data
  miss : Miss ns i ns.length

end

public section

theorem ofInt_neg40 : (BitVec.ofInt 64 (-40)).toNat = 2 ^ 64 - 40 := by
  rw [BitVec.toNat_ofInt]; rfl

/-- `x + 40 = a`: `x` is `a` less 40. -/
theorem sub40 {x a : BitVec 64} (h : x + BitVec.ofNat 64 40 = a) :
    x = a + BitVec.ofInt 64 (-40) := by
  subst h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, ofInt_neg40, BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem xor_ne_self (x : Nat) : x ≠ x ^^^ 1 := by
  intro h
  have : x ^^^ x = x ^^^ (x ^^^ 1) := by rw [← h]
  rw [Nat.xor_self, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this
  exact absurd this (by decide)

theorem toNat_xor64 (a b : BitVec 64) :
    (BinOp.apply .xor .W64 a b).toNat = a.toNat ^^^ b.toNat := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_xor]

/-- `test %r, %r; je` of a small number. -/
theorem and_self_zero {x : Nat} (hx : x < 2 ^ 64) :
    CmpOp.apply .eq .W64 (BinOp.apply .and .W64 (BitVec.ofNat 64 x) (BitVec.ofNat 64 x))
      (BitVec.ofNat 64 0) = decide (x = 0) := by
  have e : BinOp.apply .and .W64 (BitVec.ofNat 64 x) (BitVec.ofNat 64 x) = BitVec.ofNat 64 x := by
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.and_self]
  rw [e, eq64, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} {ns : List (Nat × Digest)}

/-- **The sibling found**: node `j`, the first of key `k ^^^ 1`. -/
theorem sibStep_found {i j ci : Nat} (hi : i < ns.length) (hj : j < ns.length)
    (hk : ns[j].1 = ns[i].1 ^^^ 1) (hmiss : Miss ns i j) :
    sibStep B ns ns[i] ci = some ((ns[i].1, ns[j].2, true), ci) := by
  unfold sibStep
  rw [lookup_first ns _ j hj (fun j' hj' ↦ hmiss j' hj' (by omega) hi) hk]

/-- **The sibling read**: no node of key `k ^^^ 1`. -/
theorem sibStep_read {i ci : Nat} (hi : i < ns.length) (hmiss : Miss ns i ns.length) :
    sibStep B ns ns[i] ci = (rdDigest B ci).map fun p ↦ ((ns[i].1, p.1, false), p.2) := by
  unfold sibStep
  rw [lookup_none ns _ fun j' hj' ↦ hmiss j' hj' hj' hi]

theorem take_succ_eq {i : Nat} (hi : i < ns.length) : ns.take (i + 1) = ns.take i ++ [ns[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  rfl

/-- **One node more** of `sibsM`. -/
theorem sibsM_step {i : Nat} {sl : List (Nat × Digest × Bool)} {ci ci' : Nat}
    {q : Nat × Digest × Bool} (hs : sibsM B ns (ns.take i) c = some (sl, ci)) (hi : i < ns.length)
    (hq : sibStep B ns ns[i] ci = some (q, ci')) :
    sibsM B ns (ns.take (i + 1)) c = some (sl ++ [q], ci') := by
  rw [take_succ_eq hi, sibsM_snoc, hs]
  simp only [Option.bind_some, hq, Option.map_some]

/-- **No sibling** for node `i`: `None`. -/
theorem sibsM_none {i : Nat} {sl : List (Nat × Digest × Bool)} {ci : Nat}
    (hs : sibsM B ns (ns.take i) c = some (sl, ci)) (hi : i < ns.length)
    (hq : sibStep B ns ns[i] ci = none) : sibsM B ns ns c = none := by
  have h1 : sibsM B ns (ns.take (i + 1)) c = none := by
    rw [take_succ_eq hi, sibsM_snoc, hs]
    simp only [Option.bind_some, hq, Option.map_none]
  have e : sibsM B ns ns c = sibsM B ns (ns.take (i + 1) ++ ns.drop (i + 1)) c := by
    rw [List.take_append_drop]
  rw [e, sibsM_append, h1]
  rfl

variable [Labels]

/-- **The frame and the regions `rest`**: a well formed environment. -/
theorem Geo.wf_rest (g : Geo m0 bp B.length) {m : MachineData} {o : Nat}
    (hf : Frame m0 208 slots o m) {rest : List (BitVec 64 × Nat)}
    (hr : ∀ x ∈ rest, NativeRustcVm.Mapped m.dmem x.1 x.2 ∧ x.1.toNat + x.2 ≤ 2 ^ 64 ∧
      (x.1.toNat + x.2 ≤ sp m0 - 208 ∨ sp m0 + 8 ≤ x.1.toNat))
    (hp : rest.Pairwise fun x y ↦ x.1.toNat + x.2 ≤ y.1.toNat ∨ y.1.toNat + y.2 ≤ x.1.toNat)
    {vars : Nat → BitVec 64} {ret : BitVec 64} : (frameEnv m0 m 208 rest vars ret).WF := by
  have hfb := g.fb_toNat
  have := g.s0
  refine frame_wf ⟨Mapped.keeps (frame_mapped g.g.st (by decide)) hf.kept,
    frame_noWrap g.g.st (by decide)⟩ (fun x hx ↦ ⟨(hr x hx).1, (hr x hx).2.1⟩)
    (List.pairwise_cons.mpr ⟨fun y hy ↦ ?_, hp⟩)
  unfold NativeRustcVm.Apart
  dsimp only
  rw [hfb]
  have := (hr y hy).2.2
  omega

/-- Bytes of the nodes, as a region beside the frame. -/
theorem Geo.nd_area (g : Geo m0 bp B.length) {m : MachineData} {o' : Nat}
    (hf : Frame m0 208 slots o' m) {o n : Nat} (h : o + n ≤ 40 * cnt m0) (h0 : 0 < n) :
    NativeRustcVm.Mapped m.dmem (off (nodes m0) o) n ∧ (off (nodes m0) o).toNat + n ≤ 2 ^ 64 ∧
      ((off (nodes m0) o).toNat + n ≤ sp m0 - 208 ∨ sp m0 + 8 ≤ (off (nodes m0) o).toNat) := by
  have := g.nS
  have := g.s0
  have ht := g.nd_toNat (o := o) (by omega)
  refine ⟨Mapped.keeps (NativeRustcVm.Mapped.sub g.nm h) hf.kept, by rw [ht]; have := g.nN; omega,
    by rw [ht]; omega⟩

/-- Bytes of the siblings, as a region beside the frame. -/
theorem Geo.sb_area (g : Geo m0 bp B.length) {m : MachineData} {o' : Nat}
    (hf : Frame m0 208 slots o' m) {o n : Nat} (h : o + n ≤ 10240) (h0 : 0 < n) :
    NativeRustcVm.Mapped m.dmem (off (sibs m0) o) n ∧ (off (sibs m0) o).toNat + n ≤ 2 ^ 64 ∧
      ((off (sibs m0) o).toNat + n ≤ sp m0 - 208 ∨ sp m0 + 8 ≤ (off (sibs m0) o).toNat) := by
  have := g.sS
  have := g.s0
  have ht := g.sb_toNat (o := o) (by omega)
  refine ⟨Mapped.keeps (NativeRustcVm.Mapped.sub g.sm h) hf.kept, by rw [ht]; have := g.sN; omega,
    by rw [ht]; omega⟩

/-- Bytes of the parents, as a region beside the frame. -/
theorem Geo.pa_area (g : Geo m0 bp B.length) {m : MachineData} {o' : Nat}
    (hf : Frame m0 208 slots o' m) {o n : Nat} (h : o + n ≤ 10240) (h0 : 0 < n) :
    NativeRustcVm.Mapped m.dmem (off (nxt m0) o) n ∧ (off (nxt m0) o).toNat + n ≤ 2 ^ 64 ∧
      ((off (nxt m0) o).toNat + n ≤ sp m0 - 208 ∨ sp m0 + 8 ≤ (off (nxt m0) o).toNat) := by
  have := g.xS
  have := g.s0
  have ht := g.pa_toNat (o := o) (by omega)
  refine ⟨Mapped.keeps (NativeRustcVm.Mapped.sub g.xm h) hf.kept, by rw [ht]; have := g.xN; omega,
    by rw [ht]; omega⟩

omit [Labels] in
theorem Cur.keep {i : Nat} {sl : List (Nat × Digest × Bool)} {ci : Nat} {m m' : MachineData}
    (h : Cur m0 bp B c ns i sl ci m) (hf : Frame m0 208 slots 8 m')
    (hd : m'.dmem = m.dmem) (hk : ∀ x ∈ loopRegs, reg m' x = reg m x) :
    Cur m0 bp B c ns i sl ci m' :=
  ⟨hf, h.hs, by rw [hd]; exact h.mm, by rw [hd]; exact h.nx, h.lt,
    (hk .rbp (by simp [loopRegs])).trans h.rbp, (hk .r12 (by simp [loopRegs])).trans h.r12,
    (hk .rbx (by simp [loopRegs])).trans h.rbx, (hk .r14 (by simp [loopRegs])).trans h.r14,
    (hk .r15 (by simp [loopRegs])).trans h.r15⟩

end

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} {ns : List (Nat × Digest)}
variable [Host] {k : Nat}

theorem Scan.cur {i : Nat} {sl : List (Nat × Digest × Bool)} {ci j : Nat} {st : MachineState}
    (h : Scan k m0 bp B c ns i sl ci j st) : Cur m0 bp B c ns i sl ci st.data :=
  ⟨h.fr, h.hs, h.mm, h.nx, h.lt, h.rbp, h.r12, h.rbx, h.r14, h.r15⟩

section
variable (hp : Placed code k) (g : Geo m0 bp B.length) (hl : ns.length = cnt m0)
include hp g hl

/-- **A step of the scan** at node `j`: the sibling read (past the last node), found, or the
next node. -/
theorem scan_step {i : Nat} {sl : List (Nat × Digest × Bool)} {ci j : Nat} {st : MachineState}
    (hI : Scan k m0 bp B c ns i sl ci j st) :
    Eventually (step1 Host.exe) (fun st' ↦ Rd k m0 bp B c ns i sl ci st' ∨
      (∃ j', Fnd k m0 bp B c ns i sl ci j' st') ∨ Scan k m0 bp B c ns i sl ci (j + 1) st') st := by
  have hle := hI.le
  have hli := hI.lt
  have hn := g.n256
  obtain ⟨hok5, hK5⟩ := ok_b5
  refine fr_step hp g (j := NativeRustcVmX64.Vm.ClimbLevel.b5Offset) b5_in_code (by simp [b5]) exit_b5 nofun hok5 hI.pc hI.fr
    fun s1 hf1 hd1 hr1 hpc1 ↦ ?_
  have hk1 := regs_kept hK5 hr1
  have hcur : Cur m0 bp B c ns i sl ci s1.data :=
    hI.cur.keep hf1 hd1 fun x hx ↦ hk1 x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
  have hrcx : reg s1.data .rcx = BitVec.ofNat 64 (40 * (cnt m0 - j)) :=
    (hk1 .rcx (by simp)).trans hI.rcx
  have hrax : reg s1.data .rax + BitVec.ofNat 64 40 = nd m0 j := by
    rw [hk1 .rax (by simp)]; exact hI.rax
  have hpc2 := pc_cond hpc1 (P := j = cnt m0) (by
    show CmpOp.apply .eq .W64 (BinOp.apply .and .W64 (reg st.data .rcx) (reg st.data .rcx))
      (BitVec.ofNat 64 0) = _
    rw [hI.rcx, and_self_zero (by omega)]
    exact decide_eq_decide.mpr (by omega))
  by_cases hjn : j = cnt m0
  · rw [ite_t hjn, hp.label NativeRustcVmX64.Vm.ClimbLevel.label_9_at] at hpc2
    subst hjn
    exact .done _ (.inl ⟨hpc2, hcur, by rw [hl]; exact hI.miss⟩)
  rw [ite_f hjn] at hpc2
  have hjl : j < ns.length := by omega
  have hil : i < ns.length := by omega
  -- `b6`: the keys.
  have hrax' : reg s1.data .rax = nd m0 j + BitVec.ofInt 64 (-40) := sub40 hrax
  have hi8 := g.nd_area hcur.fr (o := 40 * i) (n := 8) (by omega) (by omega)
  have hj8 := g.nd_area hcur.fr (o := 40 * j) (n := 8) (by omega) (by omega)
  have hti := g.nd_toNat (o := 40 * i) (by omega)
  have htj := g.nd_toNat (o := 40 * j) (by omega)
  have hkey : ∀ t (ht : t < ns.length), (ns[t]'ht).1 < 2 ^ 64 ∧
      WordAt s1.data.dmem (nd m0 t + BitVec.ofNat 64 0) (ns[t]'ht).1.toUInt64 := fun t ht ↦ by
    have := hcur.mm.nd t ht
    rw [NativeRustcVm.addr_add_zero]
    exact ⟨this.1, this.2.1⟩
  -- After `b6`, the next node.
  have hnext : ∀ st2 : MachineState, Cur m0 bp B c ns i sl ci st2.data →
      reg st2.data .rax = BinOp.apply .add .W64 (BitVec.ofNat 64 40) (reg s1.data .rax) →
      reg st2.data .rcx = BinOp.apply .add .W64 (BitVec.ofNat 64 18446744073709551576)
        (reg s1.data .rcx) →
      Miss ns i (j + 1) → st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ClimbLevel.b5Offset) →
      Scan k m0 bp B c ns i sl ci (j + 1) st2 := by
    intro st2 hc hra hrc hmiss hpc
    refine ⟨hpc, hc.fr, hc.hs, hc.mm, hc.nx, hc.lt, hc.rbp, hc.r12, hc.rbx, hc.r14, hc.r15, ?_, ?_,
      by omega, hmiss⟩
    · rw [hrc, hrcx]
      apply BitVec.eq_of_toNat_eq
      rw [toNat_add64, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    · rw [hra]
      show BitVec.ofNat 64 40 + reg s1.data .rax + BitVec.ofNat 64 40 = _
      rw [BitVec.add_comm (BitVec.ofNat 64 40) (reg s1.data .rax), hrax]
      exact off_add _ _ _
  by_cases hji : j = i
  · -- The node itself: never its own sibling.
    subst hji
    obtain ⟨hmid, hmem, hra6, hrc6, hK6⟩ := ok_b6s
    have hwf : (frameEnv m0 s1.data 208 [(nd m0 j, 8)]).WF :=
      g.wf_rest hf1 (fun x hx ↦ by simp only [List.mem_singleton] at hx; subst hx; exact hi8)
        (List.pairwise_singleton _ _)
    have hm : Match (frameEnv m0 s1.data 208 [(nd m0 j, 8)]) selfS s1.data :=
      match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf1.rsp_eval, trivial⟩ trivial trivial
        ⟨by
          show reg s1.data .rbp = nd m0 j + BitVec.ofInt 64 0
          rw [NativeRustcVmX64.Transcript.ofInt_zero64, BitVec.add_zero]; exact hcur.rbp,
        hrax', trivial⟩
    refine exec_at (Wire.infix_of b6_in_code (by simp [b6]) hp) exit_b6s hwf nofun
      (hpc2.trans (congrArg Host.addrOf rfl)) hm fun st2 hm2 hpc3 ↦ ?_
    simp only [PcOk, SBool.eval, ↓reduceIte, hp.label NativeRustcVmX64.Vm.ClimbLevel.label_4_at] at hpc3
    have hk2 := regs_kept hK6 fun r v h ↦ hm2.regs r v h
    refine .done _ (.inr (.inr (hnext st2
      (hcur.keep (Frame.of_block hf1 hwf hm2 hmid slots_le) (hm2.dmem_eq hwf hmem) hk2)
      (hm2.regs .rax _ hra6) (hm2.regs .rcx _ hrc6) (fun j' hj' hj hi ↦ ?_) hpc3)))
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj') with h | rfl
    · exact hI.miss j' h hj hi
    · exact (xor_ne_self _) ∘ fun h ↦ h
  · obtain ⟨hmid, hmem, hra6, hrc6, hr13, hK6⟩ := ok_b6
    have hwf : (frameEnv m0 s1.data 208 [(nd m0 i, 8), (nd m0 j, 8)]).WF :=
      g.wf_rest hf1 (fun x hx ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact hi8
          · exact hj8)
        (List.pairwise_pair.mpr (by dsimp only; rw [hti, htj]; omega))
    have hm : Match (frameEnv m0 s1.data 208 [(nd m0 i, 8), (nd m0 j, 8)]) cmpS s1.data :=
      match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hf1.rsp_eval, trivial⟩ trivial trivial
        ⟨by
          show reg s1.data .rbp = nd m0 i + BitVec.ofInt 64 0
          rw [NativeRustcVmX64.Transcript.ofInt_zero64, BitVec.add_zero]; exact hcur.rbp,
        hrax', trivial⟩
    have hld : ∀ (r t : Nat) (ht : t < ns.length),
        (frameEnv m0 s1.data 208 [(nd m0 i, 8), (nd m0 j, 8)]).base r = nd m0 t →
        (frameEnv m0 s1.data 208 [(nd m0 i, 8), (nd m0 j, 8)]).load r 0 8 =
          BitVec.ofNat 64 (ns[t]'ht).1 := fun r t ht hb ↦ by
      rw [Wire.load_word (v := (ns[t]'ht).1.toUInt64) (by rw [hb]; exact (hkey t ht).2)]
      apply BitVec.eq_of_toNat_eq
      rw [UInt64.toNat_toBitVec, BitVec.toNat_ofNat, toNat_toUInt64_of_lt (hkey t ht).1,
        Nat.mod_eq_of_lt (hkey t ht).1]
    have hl1 := hld 1 i hil rfl
    have hl2 := hld 2 j hjl rfl
    refine exec_at (Wire.infix_of b6_in_code (by simp [b6]) hp) exit_b6 hwf nofun
      (hpc2.trans (congrArg Host.addrOf rfl)) hm fun st2 hm2 hpc3 ↦ ?_
    have hk2 := regs_kept hK6 fun r v h ↦ hm2.regs r v h
    have hc2 : Cur m0 bp B c ns i sl ci st2.data :=
      hcur.keep (Frame.of_block hf1 hwf hm2 hmid slots_le) (hm2.dmem_eq hwf hmem) hk2
    have hpc4 := pc_cond hpc3 (P := (ns[j]'hjl).1 ≠ (ns[i]'hil).1 ^^^ 1) (by
      show (!(CmpOp.apply .eq .W64 (BinOp.apply .xor .W64
        ((frameEnv m0 s1.data 208 [(nd m0 i, 8), (nd m0 j, 8)]).load 2 0 8)
        ((frameEnv m0 s1.data 208 [(nd m0 i, 8), (nd m0 j, 8)]).load 1 0 8)) (BitVec.ofNat 64 1)))
        = _
      rw [hl1, hl2, eq64, toNat_xor64, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hkey j hjl).1, Nat.mod_eq_of_lt (hkey i hil).1, Nat.xor_comm]
      have e : ((ns[i]'hil).1 ^^^ (ns[j]'hjl).1 = 1 % 2 ^ 64) ↔ (ns[j]'hjl).1 = (ns[i]'hil).1 ^^^ 1 :=
        xor_eq_one_iff _ _
      by_cases h : (ns[j]'hjl).1 = (ns[i]'hil).1 ^^^ 1
      · rw [decide_eq_true (e.mpr h)]; simp [h]
      · rw [decide_eq_false (fun h' ↦ h (e.mp h'))]; simp [h])
    by_cases hf : (ns[j]'hjl).1 ≠ (ns[i]'hil).1 ^^^ 1
    · rw [ite_t hf, hp.label NativeRustcVmX64.Vm.ClimbLevel.label_4_at] at hpc4
      refine .done _ (.inr (.inr (hnext st2 hc2 (hm2.regs .rax _ hra6) (hm2.regs .rcx _ hrc6)
        (fun j' hj' hj hi ↦ ?_) hpc4)))
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj') with h | rfl
      · exact hI.miss j' h hj hi
      · exact hf
    · rw [ite_f hf] at hpc4
      refine .done _ (.inr (.inl ⟨j, hpc4.trans (congrArg Host.addrOf rfl), hc2, hil, hjl,
        by simpa using hf, hI.miss, ?_, ?_⟩))
      · refine (hm2.regs .rax _ hra6).trans ?_
        show BitVec.ofNat 64 40 + reg s1.data .rax = _
        rw [BitVec.add_comm]
        exact hrax
      · exact (hm2.regs .r13 _ hr13).trans hl1

end

end

end NativeRustcVmX64.Wire.ClimbLevel
