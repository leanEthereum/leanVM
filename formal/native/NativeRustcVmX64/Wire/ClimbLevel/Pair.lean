module

public import NativeRustcVmX64.Wire.ClimbLevel.Hash
public import NativeRustcVmX64.Code.Vm.HashPair.Names

/-!
# `climb_level`'s parents (x86-64)

The model's parent of node `i` (`parent_even`, `parent_odd`, `parent_none`). After node `i`'s
sibling (`Mid`): `hash_pair` of node `i`'s digest and its sibling's, in order (`b13`) or the
sibling's first (`b17`); the count checked (`b14`, `b18`, never `256` or more); the parent stored
at the parents' end (`b19`): the next node's check (`pair_spec`).
-/

namespace NativeRustcVmX64.Wire.ClimbLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.ClimbLevel
open NativeRustcVmX64.Transcript (Frame frameEnv Frame.of_block after after_eq MidOk)
open NativeRustcVm.Transcript (Mapped.keeps off off_zero off_add off_off toNat_off)
open NativeRustcVm (WordAt WordsAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open NativeRustcVmX64.Wire (pc_cond ite_t ite_f eq64 ult64 toNat_add64)
open NativeRustcVmX64.Sumcheck (WordW WordsW wordAt_written wordsAt_written)

public section

/-- A parent of an even key: node `i`'s digest first. -/
theorem parent_even {x : Nat × Digest} {s : Nat × Digest × Bool} (h : x.1 % 2 = 0) :
    parentOf x s = [(x.1 >>> 1, NativeVm.Model.hashPair x.2 s.2.1)] := by
  unfold parentOf
  simp only [h, true_or, ↓reduceIte, keccak_pair]

/-- A parent of an odd key, its sibling read: the sibling's digest first. -/
theorem parent_odd {x : Nat × Digest} {s : Nat × Digest × Bool} (h : x.1 % 2 = 1)
    (hs : s.2.2 = false) : parentOf x s = [(x.1 >>> 1, NativeVm.Model.hashPair s.2.1 x.2)] := by
  unfold parentOf
  simp only [h, hs, or_true, ↓reduceIte, keccak_pair, show (1 : Nat) ≠ 0 by decide]

/-- No parent of an odd key whose sibling is a node. -/
theorem parent_none {x : Nat × Digest} {s : Nat × Digest × Bool} (h : x.1 % 2 = 1)
    (hs : s.2.2 = true) : parentOf x s = [] := by
  unfold parentOf
  simp only [h, hs, show (1 : Nat) ≠ 0 by decide, Bool.true_eq_false, or_self, ↓reduceIte]

/-- Slot `p` of 40-byte nodes at `b`, as `leaq (%r,%r,4); (%b,%rax,8)` computes it. -/
theorem slot_eval (b : BitVec 64) (p : Nat) :
    BinOp.apply .add .W64 b (BinOp.apply .mul .W64 (BinOp.apply .add .W64 (BitVec.ofNat 64 p)
      (BinOp.apply .mul .W64 (BitVec.ofNat 64 p) (BitVec.ofNat 64 4))) (BitVec.ofNat 64 8)) =
      off b (40 * p) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    off]
  omega

theorem shr1_toNat (x : BitVec 64) :
    (BinOp.apply .shr .W64 x (BitVec.ofNat 64 1)).toNat = x.toNat / 2 := by
  have hs : shiftCount .W64 (BitVec.ofNat 64 1) = 1 := by decide
  simp only [BinOp.apply, low_W64, ext_W64, hs, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, pow_one]

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} {ns : List (Nat × Digest)}

variable [Host] {k : Nat}

section
variable (hp : Placed code k) (g : Geo m0 bp B.length) (hl : ns.length = cnt m0)
include hp g hl

/-- **The parent stored** (`b19`, at `NativeRustcVmX64.Vm.ClimbLevel.label_17`): the key halved and the hash `H` at
parent `p`; the next node's check. -/
theorem store_spec {i : Nat} {sl : List (Nat × Digest × Bool)} {ci : Nat}
    {q : Nat × Digest × Bool} {H : Digest} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ClimbLevel.b19Offset)) (hf : Frame m0 208 slots 8 st.data)
    (hs : sibsM B ns (ns.take (i + 1)) c = some (sl ++ [q], ci))
    (hmm : MemS m0 bp B ns (sn (sl ++ [q])) (parentsOf (ns.take i) sl) ci st.data.dmem)
    (hnx : Nx m0 (i + 1) st.data.dmem) (hlt : i < cnt m0) (hsl : sl.length = i)
    (hi : i < ns.length) (hpar : parentOf ns[i] q = [((ns[i]).1 >>> 1, H)])
    (hH : WordsAt st.data.dmem (off (fb m0) 88) H.toList)
    (hr13 : reg st.data .r13 = BitVec.ofNat 64 ns[i].1)
    (hrbx : reg st.data .rbx = BitVec.ofNat 64 (parentsOf (ns.take i) sl).length)
    (hr14 : reg st.data .r14 = nxt m0) (hr15 : reg st.data .r15 = sibs m0) :
    Eventually (step1 Host.exe) (Nxt k m0 bp B c ns (i + 1) (sl ++ [q]) ci) st := by
  have h0 := g.s0
  have hn := g.n256
  set p := (parentsOf (ns.take i) sl).length with hpdef
  have hpl : p ≤ i := par_le i sl
  have hkey := (hmm.nd i hi).1
  obtain ⟨hmid, hin, hall, hwk, hwd, hrbx', hK⟩ := ok_b19
  have harea := g.pa_area hf (o := 40 * p) (n := 40) (by omega) (by omega)
  have hpt := g.pa_toNat (o := 40 * p) (by omega)
  have hwf : (frameEnv m0 st.data 208 [(off (nxt m0) (40 * p), 40)]).WF :=
    g.wf_rest hf (fun x hx ↦ by simp only [List.mem_singleton] at hx; subst hx; exact harea)
      (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 208 [(off (nxt m0) (40 * p), 40)]) stS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial
      ⟨by
        show BinOp.apply .add .W64 (reg st.data .r14) (BinOp.apply .mul .W64
          (BinOp.apply .add .W64 (reg st.data .rbx) (BinOp.apply .mul .W64 (reg st.data .rbx)
          (BitVec.ofNat 64 4))) (BitVec.ofNat 64 8)) = off (nxt m0) (40 * p) + BitVec.ofInt 64 0
        rw [hr14, hrbx, slot_eval, NativeRustcVmX64.Transcript.ofInt_zero64,
          BitVec.add_zero], trivial⟩
  refine exec_at (Wire.infix_of b19_in_code (by simp [b19]) hp) exit_b19 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  have hf' : Frame m0 208 slots 8 st'.data := Frame.of_block hf hwf hm' hmid slots_le
  have hs' : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
      (NativeRustcVm.InRange (off (nxt m0) (40 * p)) 40) :=
    NativeRustcVmX64.Transcript.sameOutside_region hwf hm' (r := 1) rfl (fun w hw ↦ by
      have h1 := hall w hw
      have h2 := List.all_eq_true.mp hin w hw
      rw [h1] at h2
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
      refine ⟨h1, Nat.zero_le _, ?_⟩
      rcases h2 with h2 | h2
      · exact absurd h2 (by decide)
      · exact h2.2)
  have hsn : ∀ q', NativeRustcVm.InRange (off (nxt m0) (40 * p)) 40 q' →
      (nxt m0).toNat + 40 * p ≤ q'.toNat ∧ q'.toNat < (nxt m0).toNat + 40 * p + 40 := by
    intro q' hq'
    rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; omega), hpt] at hq'
    exact hq'
  -- The new parent.
  have hnode : NodeAt st'.data.dmem (off (nxt m0) (40 * p)) ((ns[i]).1 >>> 1, H) := by
    refine ⟨by rw [Nat.shiftRight_eq_div_pow]; omega, ?_, ?_⟩
    · have := wordAt_written hm' (r := 1) (o := 0) (b := off (nxt m0) (40 * p)) rfl (by decide)
        hwk (w := ((ns[i]).1 >>> 1).toUInt64) (by
          apply BitVec.eq_of_toNat_eq
          show (BinOp.apply .shr .W64 (reg st.data .r13) (BitVec.ofNat 64 1)).toNat = _
          rw [shr1_toNat, hr13, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
            toNat_toUInt64_of_lt (by rw [Nat.shiftRight_eq_div_pow]; omega),
            Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hkey])
      rwa [off_zero] at this
    · refine wordsAt_written hm' (r := 1) (o := 8) rfl (by decide) hwd fun t ht ↦ ?_
      show (frameEnv m0 st.data 208 [(off (nxt m0) (40 * p), 40)]).load 0 (88 + 8 * t) 8 = _
      have hw := (NativeRustcVm.wordsAt_iff.mp hH) t (by simpa using ht)
      rw [NativeRustcVm.addr_add_add] at hw
      exact Wire.load_word hw
  -- The memory.
  have htk : (ns.take (i + 1)).length = i + 1 := take_length_of_le (by omega)
  have hpar' : parentsOf (ns.take (i + 1)) (sl ++ [q]) =
      parentsOf (ns.take i) sl ++ [((ns[i]).1 >>> 1, H)] := by
    rw [take_succ_eq hi, parentsOf_snoc (by rw [take_length_of_le (by omega), hsl]), hpar]
  have hls := hmm.ls
  have hlp := hmm.lp
  have hpS := g.xS
  have hsX := g.sX
  have hnY := g.nY
  have hxR := g.xR
  have hmm' : MemS m0 bp B ns (sn (sl ++ [q])) (parentsOf (ns.take (i + 1)) (sl ++ [q])) ci
      st'.data.dmem := by
    have hk := hmm.keep g hl hs' fun q' hq' ↦ by have := hsn q' hq'; unfold Mov; omega
    rw [hpar']
    refine ⟨hk.rd, hk.sb, nodesAt_snoc' hmm.nx (by omega) hnode hs' fun q' hq' ↦ by
      have := hsn q' hq'; omega, hk.nd, hk.loc, hk.chg, hk.ls, ?_⟩
    simp only [List.length_append, List.length_singleton]
    omega
  simp only [PcOk, hp.label NativeRustcVmX64.Vm.ClimbLevel.label_7_at] at hpc'
  refine .done _ ⟨hpc', hf', hs, hmm', hnx.keep g hs' fun q' hq' ↦ by have := hsn q' hq'; omega,
    by omega, by omega, ?_, (regs_kept hK (fun r v h ↦ hm'.regs r v h) .r14 (by simp)).trans hr14,
    (regs_kept hK (fun r v h ↦ hm'.regs r v h) .r15 (by simp)).trans hr15⟩
  refine (hm'.regs .rbx _ hrbx').trans ?_
  rw [hpar']
  show BinOp.apply .add .W64 (reg st.data .rbx) (BitVec.ofNat 64 1) = _
  rw [hrbx]
  simp only [List.length_append, List.length_singleton, BinOp.apply, low_W64, ext_W64]
  exact (BitVec.ofNat_add _ _).symm


/-- **After the hash** (at `b14` or `b18`): the count, below 256, checked; the parent stored. -/
theorem hashed_spec {i : Nat} {sl : List (Nat × Digest × Bool)} {ci : Nat}
    {q : Nat × Digest × Bool} {H : Digest} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ClimbLevel.b14Offset) ∨ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ClimbLevel.b18Offset))
    (hf : Frame m0 208 slots 8 st.data)
    (hs : sibsM B ns (ns.take (i + 1)) c = some (sl ++ [q], ci))
    (hmm : MemS m0 bp B ns (sn (sl ++ [q])) (parentsOf (ns.take i) sl) ci st.data.dmem)
    (hnx : Nx m0 (i + 1) st.data.dmem) (hlt : i < cnt m0) (hsl : sl.length = i)
    (hi : i < ns.length) (hpar : parentOf ns[i] q = [((ns[i]).1 >>> 1, H)])
    (hH : WordsAt st.data.dmem (off (fb m0) 88) H.toList)
    (hr13 : reg st.data .r13 = BitVec.ofNat 64 ns[i].1)
    (hrbx : reg st.data .rbx = BitVec.ofNat 64 (parentsOf (ns.take i) sl).length)
    (hr14 : reg st.data .r14 = nxt m0) (hr15 : reg st.data .r15 = sibs m0) :
    Eventually (step1 Host.exe) (Nxt k m0 bp B c ns (i + 1) (sl ++ [q]) ci) st := by
  have hn := g.n256
  have hpl : (parentsOf (ns.take i) sl).length ≤ i := par_le i sl
  have hlt' : (parentsOf (ns.take i) sl).length < 256 := by omega
  have hcmp : CmpOp.apply .ult .W64 (reg st.data .rbx) (BitVec.ofNat 64 256) = true := by
    rw [hrbx, ult64, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true (by omega)
  have go : ∀ s1 : MachineState, Frame m0 208 slots 8 s1.data → s1.data.dmem = st.data.dmem →
      (∀ x ∈ Reg64.r13 :: loopRegs, reg s1.data x = reg st.data x) →
      s1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ClimbLevel.b19Offset) →
      Eventually (step1 Host.exe) (Nxt k m0 bp B c ns (i + 1) (sl ++ [q]) ci) s1 :=
    fun s1 hf1 hd1 hk hpc1 ↦ store_spec hp g hl hpc1 hf1 hs (hd1 ▸ hmm) (hd1 ▸ hnx) hlt hsl hi
      hpar (hd1 ▸ hH) ((hk .r13 (by simp)).trans hr13)
      ((hk .rbx (by simp [loopRegs])).trans hrbx) ((hk .r14 (by simp [loopRegs])).trans hr14)
      ((hk .r15 (by simp [loopRegs])).trans hr15)
  rcases hpc with hpc | hpc
  · refine fr_step hp g (j := NativeRustcVmX64.Vm.ClimbLevel.b14Offset) b14_in_code (by simp [b14]) exit_b14 nofun ok_b14.1 hpc hf
      fun s1 hf1 hd1 hr1 hpc1 ↦ go s1 hf1 hd1 (regs_kept ok_b14.2 hr1) ?_
    have := pc_cond hpc1 (P := True) (by
      show CmpOp.apply .ult .W64 (reg st.data .rbx) (BitVec.ofNat 64 256) = _
      rw [hcmp]; rfl)
    rw [ite_t trivial, hp.label NativeRustcVmX64.Vm.ClimbLevel.label_17_at] at this
    exact this
  · refine fr_step hp g (j := NativeRustcVmX64.Vm.ClimbLevel.b18Offset) b18_in_code (by simp [b18]) exit_b18 nofun ok_b18.1 hpc hf
      fun s1 hf1 hd1 hr1 hpc1 ↦ go s1 hf1 hd1 (regs_kept ok_b18.2 hr1) ?_
    have := pc_cond hpc1 (P := False) (by
      show (!CmpOp.apply .ult .W64 (reg st.data .rbx) (BitVec.ofNat 64 256)) = _
      rw [hcmp]; rfl)
    rw [ite_f not_false] at this
    exact this.trans (congrArg Host.addrOf rfl)

/-- **The parent** after node `i`'s sibling: `hash_pair` of node `i`'s digest and the sibling's
(at `b13`, an even key) or the sibling's first (at `b17`, an odd key, the sibling read); the
parent stored; the next node's check. -/
theorem pair_spec {i : Nat} {sl : List (Nat × Digest × Bool)} {ci : Nat}
    (hh : Spec (Labels.label NativeRustcVmX64.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    {q : Nat × Digest × Bool} {st : MachineState} (hM : Mid m0 bp B c ns i sl ci q st.data)
    (hi : i < ns.length)
    (hpc : (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ClimbLevel.b13Offset) ∧ ns[i].1 % 2 = 0) ∨
      (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ClimbLevel.b17Offset) ∧ ns[i].1 % 2 = 1 ∧ q.2.2 = false)) :
    Eventually (step1 Host.exe) (Nxt k m0 bp B c ns (i + 1) (sl ++ [q]) ci) st := by
  have hnd := hM.mm.nd i hi
  have hL : WordsAt st.data.dmem (off (nodes m0) (40 * i + 8)) ns[i].2.toList := by
    rw [← off_off]; exact hnd.2.2
  have hnA : Arg m0 (off (nodes m0) (40 * i + 8)) := .inr ⟨_, by omega, rfl⟩
  have hfA : Arg m0 (off (fb m0) 8) := .inl rfl
  have hk13 : (ns[i]).1 = q.1 := (hM.key hi).symm
  have hrbp : BitVec.ofNat 64 8 + reg st.data .rbp = off (nodes m0) (40 * i + 8) := by
    rw [hM.rbp, BitVec.add_comm, off_add]
  -- After the call.
  have post : ∀ (bj : List Directive) (j : Nat), (st.pc = Host.addrOf (k + j)) →
      (after bj frS).reg .rbx = some (.reg .rbx) → (after bj frS).reg .r13 = some (.reg .r13) →
      (after bj frS).reg .r14 = some (.reg .r14) → (after bj frS).reg .r15 = some (.reg .r15) →
      (Host.addrOf (k + j + bj.length) = Host.addrOf (k + NativeRustcVmX64.Vm.ClimbLevel.b14Offset) ∨
        Host.addrOf (k + j + bj.length) = Host.addrOf (k + NativeRustcVmX64.Vm.ClimbLevel.b18Offset)) →
      ∀ H : Digest, parentOf ns[i] q = [((ns[i]).1 >>> 1, H)] →
      ∀ m2, Frame m0 208 slots 8 m2 →
      (∀ r v, (after bj frS).reg r = some v → calleeSaved r = true →
        reg m2 r = v.eval (frameEnv m0 st.data 208 [] (fun _ ↦ 0)
          (Host.addrOf (k + j + bj.length)).toBitVec)) →
      NativeRustcVm.SameOutside st.data.dmem m2.dmem (fun q ↦
        (sp m0 - 1056 ≤ q.toNat ∧ q.toNat < sp m0 - 200) ∨
        (sp m0 - 120 ≤ q.toNat ∧ q.toNat < sp m0 - 88)) →
      WordsAt m2.dmem (off (fb m0) 88) H.toList →
      Eventually (step1 Host.exe) (Nxt k m0 bp B c ns (i + 1) (sl ++ [q]) ci)
        ⟨m2, Host.addrOf (k + j + bj.length)⟩ := by
    intro bj j _ hbx h13 h14 h15 hpc2 H hpar m2 hf2 hr2 hs2 hH2
    have h0 := g.s0
    have hls := hM.mm.ls
    have hlp := hM.mm.lp
    exact hashed_spec hp g hl hpc2 hf2 hM.hs
      (hM.mm.keep g hl hs2 fun q hq ↦ by unfold Mov; omega)
      (hM.nx.keep g hs2 fun q hq ↦ by omega) hM.lt hM.hl hi hpar hH2
      ((hr2 .r13 _ h13 rfl).trans (hM.r13.trans (by rw [hk13])))
      ((hr2 .rbx _ hbx rfl).trans hM.rbx) ((hr2 .r14 _ h14 rfl).trans hM.r14)
      ((hr2 .r15 _ h15 rfl).trans hM.r15)
  rcases hpc with ⟨hpc, hev⟩ | ⟨hpc, hod, hq⟩
  · obtain ⟨hok, hlow, hdi, hsi, hdx, -, hK⟩ := ok_b13
    have hK' := keeps_of hK
    exact hash_call hp hh g (j := NativeRustcVmX64.Vm.ClimbLevel.b13Offset) b13_in_code (by simp [b13]) exit_b13 hok hlow hdi hsi hdx hpc
      hM.fr hM.mm.chg hnA hfA hrbp rfl hL hM.dg
      (post b13 99 hpc (hK' .rbx (by simp)) (hK' .r13 (by simp)) (hK' .r14 (by simp))
        (hK' .r15 (by simp)) (.inl rfl) _ (parent_even hev))
  · obtain ⟨hok, hlow, hdi, hsi, hdx, -, hK⟩ := ok_b17
    have hK' := keeps_of hK
    exact hash_call hp hh g (j := NativeRustcVmX64.Vm.ClimbLevel.b17Offset) b17_in_code (by simp [b17]) exit_b17 hok hlow hdi hsi hdx hpc
      hM.fr hM.mm.chg hfA hnA rfl hrbp hM.dg hL
      (post b17 109 hpc (hK' .rbx (by simp)) (hK' .r13 (by simp)) (hK' .r14 (by simp))
        (hK' .r15 (by simp)) (.inr rfl) _ (parent_odd hod hq))

end

end

end NativeRustcVmX64.Wire.ClimbLevel
