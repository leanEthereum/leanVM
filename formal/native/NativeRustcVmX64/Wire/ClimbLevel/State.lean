module

public import NativeRustcVmX64.Wire.ClimbLevel.Basic

/-!
# `climb_level`'s states (x86-64)

The places from the precondition (`geo_of`). The loop's head (`Head`, `b4`) after `i` nodes, the
scan for node `i`'s sibling at node `j` (`Scan`, `b5`), node `i`'s sibling written (`Mid`), the
next node's check (`Nxt`, `b3`); the result at the return (`Res`, `post_of`, `fin`); a block
without memory accesses outside the frame (`fr_step`).
-/

namespace NativeRustcVmX64.Wire.ClimbLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.ClimbLevel
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap
  Frame.of_block Frame.epilogue Frame.load_ret after after_eq MidOk)
open NativeRustcVm.Transcript (Mapped.keeps off off_zero off_add off_off toNat_off)
open NativeRustcVm (WordAt WordsAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- The siblings as nodes. -/
abbrev sn (sl : List (Nat × Digest × Bool)) : List (Nat × Digest) := sl.map fun s ↦ (s.1, s.2.1)

/-- The result at the return, RAX `v` and RDX `w`, in the model's terms. -/
def Res (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c : Nat) (ns : List (Nat × Digest))
    (v w : BitVec 64) (d : Mem 64) : Prop :=
  match sibsM B ns ns c with
  | some (sl, c') => v = 1 ∧ w.toNat = (parentsOf ns sl).length ∧ NodesAt d (sibs m0) (sn sl) ∧
      NodesAt d (nxt m0) (parentsOf ns sl) ∧ ReaderAt d (rdr m0) bp B c'
  | none => v = 0

variable [Host] (k : Nat) (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c : Nat)
  (ns : List (Nat × Digest))

/-- **The loop's head** (`b4`) after `i` nodes. -/
structure Head (i : Nat) (sl : List (Nat × Digest × Bool)) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ClimbLevel.b4Offset)
  fr : Frame m0 208 slots 8 st.data
  hs : sibsM B ns (ns.take i) c = some (sl, ci)
  mm : MemS m0 bp B ns (sn sl) (parentsOf (ns.take i) sl) ci st.data.dmem
  lt : i < cnt m0
  rbp : reg st.data .rbp = nd m0 i
  r12 : reg st.data .r12 = BitVec.ofNat 64 i
  rbx : reg st.data .rbx = BitVec.ofNat 64 (parentsOf (ns.take i) sl).length
  r14 : reg st.data .r14 = nxt m0
  r15 : reg st.data .r15 = sibs m0

/-- **The scan** (`b5`) for node `i`'s sibling, at node `j`. -/
structure Scan (i : Nat) (sl : List (Nat × Digest × Bool)) (ci j : Nat) (st : MachineState) :
    Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ClimbLevel.b5Offset)
  fr : Frame m0 208 slots 8 st.data
  hs : sibsM B ns (ns.take i) c = some (sl, ci)
  mm : MemS m0 bp B ns (sn sl) (parentsOf (ns.take i) sl) ci st.data.dmem
  nx : Nx m0 (i + 1) st.data.dmem
  lt : i < cnt m0
  rbp : reg st.data .rbp = nd m0 i
  r12 : reg st.data .r12 = BitVec.ofNat 64 i
  rbx : reg st.data .rbx = BitVec.ofNat 64 (parentsOf (ns.take i) sl).length
  r14 : reg st.data .r14 = nxt m0
  r15 : reg st.data .r15 = sibs m0
  rcx : reg st.data .rcx = BitVec.ofNat 64 (40 * (cnt m0 - j))
  rax : reg st.data .rax + BitVec.ofNat 64 40 = nd m0 j
  le : j ≤ cnt m0
  miss : Miss ns i j

/-- **Node `i`'s sibling `q` written** (and its digest at `8`), its parent not yet. -/
structure Mid (i : Nat) (sl : List (Nat × Digest × Bool)) (ci : Nat) (q : Nat × Digest × Bool)
    (m : MachineData) : Prop where
  fr : Frame m0 208 slots 8 m
  hs : sibsM B ns (ns.take (i + 1)) c = some (sl ++ [q], ci)
  mm : MemS m0 bp B ns (sn (sl ++ [q])) (parentsOf (ns.take i) sl) ci m.dmem
  nx : Nx m0 (i + 1) m.dmem
  dg : WordsAt m.dmem (off (fb m0) 8) q.2.1.toList
  lt : i < cnt m0
  hl : sl.length = i
  key : ∀ h : i < ns.length, q.1 = ns[i].1
  rbp : reg m .rbp = nd m0 i
  r13 : reg m .r13 = BitVec.ofNat 64 q.1
  r12 : reg m .r12 = BitVec.ofNat 64 i
  rbx : reg m .rbx = BitVec.ofNat 64 (parentsOf (ns.take i) sl).length
  r14 : reg m .r14 = nxt m0
  r15 : reg m .r15 = sibs m0

/-- **The next node's check** (`b3`) after `j` nodes. -/
structure Nxt (j : Nat) (sl : List (Nat × Digest × Bool)) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ClimbLevel.b3Offset)
  fr : Frame m0 208 slots 8 st.data
  hs : sibsM B ns (ns.take j) c = some (sl, ci)
  mm : MemS m0 bp B ns (sn sl) (parentsOf (ns.take j) sl) ci st.data.dmem
  nx : Nx m0 j st.data.dmem
  le : j ≤ cnt m0
  pos : 0 < j
  rbx : reg st.data .rbx = BitVec.ofNat 64 (parentsOf (ns.take j) sl).length
  r14 : reg st.data .r14 = nxt m0
  r15 : reg st.data .r15 = sibs m0

end

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} {ns : List (Nat × Digest)}

theorem sn_length (sl : List (Nat × Digest × Bool)) : (sn sl).length = sl.length := by simp [sn]

theorem take_length_of_le {i : Nat} (h : i ≤ ns.length) : (ns.take i).length = i := by simp; omega

/-- The parents after `i` nodes: at most `i`. -/
theorem par_le (i : Nat) (sl : List (Nat × Digest × Bool)) :
    (parentsOf (ns.take i) sl).length ≤ i :=
  (parentsOf_length_le _ _).trans (by simp)

theorem inRange_num {a q : BitVec 64} {n : Nat} (hn : a.toNat + n ≤ 2 ^ 64) :
    NativeRustcVm.InRange a n q ↔ a.toNat ≤ q.toNat ∧ q.toNat < a.toNat + n :=
  NativeRustcVm.inRange_iff hn

/-- The stack's bytes, as numbers. -/
theorem stack_num {m0 : MachineData} (h : StackOk m0 climbLevelStack) (q : BitVec 64)
    (hq : NativeRustcVm.InRange (stackBelow m0 climbLevelStack) (climbLevelStack + 8) q) :
    sp m0 - 1056 ≤ q.toNat ∧ q.toNat < sp m0 + 8 := by
  rw [stack_eq] at h hq
  have h1 : (stackBelow m0 1056).toNat = sp m0 - 1056 := NativeRustcVmX64.stackBelow_toNat h.1
  have h0 := h.1
  have h2 := h.2.1
  have h3 := sp_eq m0
  unfold NativeRustcVm.InRange at hq
  rw [BitVec.toNat_sub] at hq
  have := q.isLt
  omega

/-- What is apart from the stack, as numbers. -/
theorem stack_apart_num {m0 : MachineData} (h : StackOk m0 climbLevelStack) {a : BitVec 64}
    {n : Nat} (ha : NativeRustcVm.Apart (stackBelow m0 climbLevelStack) (climbLevelStack + 8) a n) :
    a.toNat + n ≤ sp m0 - 1056 ∨ sp m0 + 8 ≤ a.toNat := by
  rw [stack_eq] at h ha
  have h1 : (stackBelow m0 1056).toNat = sp m0 - 1056 := NativeRustcVmX64.stackBelow_toNat h.1
  have h0 := h.1
  have h3 := sp_eq m0
  unfold NativeRustcVm.Apart at ha
  rw [h1] at ha
  omega

section
variable [Labels]

/-- **The places** from the precondition. -/
theorem geo_of (h : ClimbLevelPre m0) (hR : ReaderAt m0.dmem (rdr m0) bp B c) :
    Geo m0 bp B.length := by
  obtain ⟨hst, hrc, hn, ⟨hnm, hnnw⟩, ⟨hsm, hsnw⟩, ⟨hxm, hxnw⟩, bp', B', c', hR', hd, hgot⟩ := h
  obtain ⟨h1, h2, h3⟩ := hR'.unique hR
  subst h1 h2 h3
  have hS0 := hst
  rw [stack_eq] at hS0
  have hsb : (stackBelow m0 climbLevelStack).toNat = sp m0 - 1056 := by
    rw [stack_eq]; exact NativeRustcVmX64.stackBelow_toNat hS0.1
  have hrNw : (rdr m0).toNat + 24 ≤ 2 ^ 64 := hR.ok.2
  have hbNw : bp.toNat + B.length ≤ 2 ^ 64 := hR.noWrap
  have hnnw' : (nodes m0).toNat + 40 * cnt m0 ≤ 2 ^ 64 := hnnw
  have hsnw' : (sibs m0).toNat + 10240 ≤ 2 ^ 64 := hsnw
  have hxnw' : (nxt m0).toNat + 10240 ≤ 2 ^ 64 := hxnw
  simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, stackR, rcR,
    nodesBytes] at hd
  obtain ⟨⟨-, a02, a03, a04, a05, a06⟩, ⟨a12, -, -, a15, a16⟩, ⟨a23, a24, a25, a26⟩,
    ⟨a34, a35, a36⟩, ⟨a45, a46⟩, a56, -⟩ := hd
  have hW : ∀ q, W m0 q → ((sibs m0).toNat ≤ q.toNat ∧ q.toNat < (sibs m0).toNat + 10240) ∨
      ((nxt m0).toNat ≤ q.toNat ∧ q.toNat < (nxt m0).toNat + 10240) := fun q hq ↦ by
    rcases hq with hq | hq
    · left; unfold nodesBytes at hq; rw [inRange_num hsnw'] at hq; exact hq
    · right; unfold nodesBytes at hq; rw [inRange_num hxnw'] at hq; exact hq
  have b5 := stack_apart_num hst a05
  have b6 := stack_apart_num hst a06
  have b2 := stack_apart_num hst a02
  have b3 := stack_apart_num hst a03
  have hsS := stack_num hst
  have e3 : (sibs m0).toNat = (reg m0 .rcx).toNat := rfl
  have e4 : (nxt m0).toNat = (reg m0 .r8).toNat := rfl
  have e5 : (rdr m0).toNat = (reg m0 .rdi).toNat := rfl
  refine ⟨⟨hst, hrNw, hbNw, NativeRustcVmX64.Transcript.Apart.symm' a02,
    NativeRustcVmX64.Transcript.Apart.symm' a03, a23, fun q hq hq' ↦ ?_, fun q hq hq' ↦ ?_,
    fun q hq hq' ↦ ?_⟩, hrc, hn, hnm, hsm, hxm, hnnw', hsnw', hxnw', stack_apart_num hst a04,
    b5, b6, b2, Or.symm a24, Or.symm a25, Or.symm a26, Or.symm a34, a45, a46, a56, a12, a15, a16, hgot⟩
  · have := hsS q hq'; have := hW q hq; omega
  · rw [inRange_num hrNw] at hq'; have := hW q hq; unfold NativeRustcVm.Apart at a25 a26; omega
  · rw [inRange_num hbNw] at hq'; have := hW q hq; unfold NativeRustcVm.Apart at a35 a36; omega

/-- The postcondition, from the result. -/
theorem post_of (g : Geo m0 bp B.length) (hR : ReaderAt m0.dmem (rdr m0) bp B c)
    (hns : NodesAt m0.dmem (nodes m0) ns) (hl : ns.length = cnt m0) {m : MachineData}
    (hres : Res m0 bp B c ns (reg m .rax) (reg m .rdx) m.dmem) (hchg : Chg m0 m.dmem)
    (hsv : Saved m0 m) : ClimbLevelPost m0 m := by
  refine ⟨fun bp' B' c' hR' ns' hl' hns' ↦ ?_, fun q hq ↦ hchg q ?_, hsv⟩
  · obtain ⟨h1, h2, h3⟩ := hR.unique hR'
    subst h1 h2 h3
    obtain rfl : ns = ns' := hns.unique hns' (by rw [hl, hl'])
    exact hres
  · have := g.s0
    have hsp := sp_eq m0
    have hsb : (stackBelow m0 climbLevelStack).toNat = sp m0 - 1056 := by
      rw [stack_eq]; exact NativeRustcVmX64.stackBelow_toNat this.1
    have hrN := g.rNw
    have hsN := g.sN
    have hxN := g.xN
    rintro (h | h | h | h)
    · refine hq ⟨frameR m0 climbLevelStack, by simp, ?_⟩
      show NativeRustcVm.InRange (stackBelow m0 climbLevelStack) climbLevelStack q
      rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [hsb, stack_eq]; omega),
        hsb, stack_eq]
      omega
    · refine hq ⟨curRegion (rdr m0), by simp, ?_⟩
      show NativeRustcVm.InRange (off (rdr m0) 16) 8 q
      have ht : (off (rdr m0) 16).toNat = (rdr m0).toNat + 16 := toNat_off (by omega)
      rw [inRange_num (by rw [ht]; omega), ht]
      omega
    · refine hq ⟨⟨sibs m0, nodesBytes⟩, by simp, ?_⟩
      show NativeRustcVm.InRange (sibs m0) nodesBytes q
      rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap nodesBytes; omega)]
      unfold nodesBytes; omega
    · refine hq ⟨⟨nxt m0, nodesBytes⟩, by simp, ?_⟩
      show NativeRustcVm.InRange (nxt m0) nodesBytes q
      rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap nodesBytes; omega)]
      unfold nodesBytes; omega

/-! ## Blocks -/

theorem fr_wf (g : Geo m0 bp B.length) {m : MachineData} {o : Nat} (hf : Frame m0 208 slots o m)
    {vars : Nat → BitVec 64} {ret : BitVec 64} : (frameEnv m0 m 208 [] vars ret).WF :=
  frame_wf ⟨Mapped.keeps (frame_mapped g.g.st (by decide)) hf.kept,
    frame_noWrap g.g.st (by decide)⟩ (by simp) (List.pairwise_singleton _ _)

theorem fr_match {m : MachineData} (hf : Frame m0 208 slots 8 m) {vars : Nat → BitVec 64}
    {ret : BitVec 64} : Match (frameEnv m0 m 208 [] vars ret) frS m :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial

end

variable [Host] {k : Nat}

/-- **A block from `frS`** (at `j`) without writes: memory and the frame kept. -/
theorem fr_step (hp : Placed code k) (g : Geo m0 bp B.length) {bj : List Directive}
    {j : Nat} (hb : bj.IsInfixAt code j) (hne : bj ≠ []) {x : Exit}
    (hrun : exec bj frS = some (after bj frS, x)) (hx : ∀ l, x = .call l → False)
    (hok : FrOk (after bj frS) = true)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) (hf : Frame m0 208 slots 8 st.data)
    {R : MachineState → Prop}
    (cont : ∀ st', Frame m0 208 slots 8 st'.data → st'.data.dmem = st.data.dmem →
      (∀ r v, (after bj frS).reg r = some v →
        reg st'.data r = v.eval (frameEnv m0 st.data 208 [])) →
      PcOk (frameEnv m0 st.data 208 []) x (Host.addrOf (k + j + bj.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  simp only [FrOk, Bool.and_eq_true, List.isEmpty_iff] at hok
  have hwf := fr_wf g hf (vars := fun _ ↦ 0) (ret := 0)
  have hm := fr_match hf (vars := fun _ ↦ 0) (ret := 0)
  exact exec_at (Wire.infix_of hb hne hp) hrun hwf (fun l h ↦ (hx l h).elim) hpc hm
    fun st' hm' hpc' ↦ cont st' (Frame.of_block hf hwf hm' hok.1 slots_le)
      (hm'.dmem_eq hwf hok.2) (fun r v h ↦ hm'.regs r v h) hpc'

/-- **The return** (`b24`, at `NativeRustcVmX64.Vm.ClimbLevel.label_11`): RAX, the parents' count from RBX. -/
theorem fin (hp : Placed code k) (g : Geo m0 bp B.length) (hR : ReaderAt m0.dmem (rdr m0) bp B c)
    (hns : NodesAt m0.dmem (nodes m0) ns) (hl : ns.length = cnt m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ClimbLevel.b24Offset)) (hf : Frame m0 208 slots 8 st.data)
    (hres : Res m0 bp B c ns (reg st.data .rax) (reg st.data .rbx) st.data.dmem)
    (hchg : Chg m0 st.data.dmem) : Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hepi, hmem, hrdx, hK⟩ := ok_b24
  have hwf := fr_wf g hf (vars := fun _ ↦ 0) (ret := 0)
  have hm := fr_match hf (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (Wire.infix_of b24_in_code (by simp [b24]) hp) exit_b24 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf hwf hm' hepi
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hmem
  simp only [PcOk] at hpc'
  refine .done _ ⟨by rw [hpc']; exact hf.load_ret g.g.st (by decide), hrsp,
    post_of g hR hns hl ?_ (by rw [hd]; exact hchg) hsv⟩
  rw [regs_kept hK (fun r v h ↦ hm'.regs r v h) .rax (by simp),
    show reg st'.data .rdx = reg st.data .rbx from hm'.regs .rdx _ hrdx, hd]
  exact hres

end

end NativeRustcVmX64.Wire.ClimbLevel
