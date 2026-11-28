module

public import NativeRustcVmX64.Wire.ClimbLevel.Pair
public import NativeRustcVmX64.Code.Vm.HashPair.Names

/-!
# `climb_level`'s sibling found (x86-64)

A block writing node `i`'s sibling (`b7`, `b12`): what it changed (`sib_same`), the sibling's
state after it (`sib_mid`). The sibling found among the nodes (`b7`): no parent for an odd key,
back at the next node's check; else (`b8`) the parent (`found_spec`).
-/

namespace NativeRustcVmX64.Wire.ClimbLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.ClimbLevel
open NativeRustcVmX64.Transcript (Frame frameEnv Frame.of_block after after_eq MidOk)
open NativeRustcVm.Transcript (Mapped.keeps off off_zero off_add off_off toNat_off)
open NativeRustcVm (WordAt WordsAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open NativeRustcVmX64.Wire (pc_cond ite_t ite_f eq64)
open NativeRustcVmX64.Sumcheck (WordW WordsW wordAt_written wordsAt_written writesIn_of_mid)

public section

/-- `testb $1, %r13b; jne`: the key's parity. -/
theorem and1_eq (x : BitVec 64) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 x (BitVec.ofNat 64 1)) (BitVec.ofNat 64 0) =
      decide (x.toNat % 2 = 0) := by
  simp only [CmpOp.apply, BinOp.apply, low_ext]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
  have e8 : (2 : Nat) ^ Width.W8.bits = 256 := rfl
  have e1 : (1 : Nat) % 256 = 1 := rfl
  simp only [low, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, e8, e1,
    Nat.and_one_is_mod]
  omega

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} {ns : List (Nat × Digest)}

/-- **A sibling's block**: writes of the frame's `8` to `40` and of region 2 (40 bytes at `a`)
only. -/
theorem sib_same [Labels] (g : Geo m0 bp B.length) {x1 : BitVec 64 × Nat} {a : BitVec 64}
    {S : SState} {d d' : MachineData}
    (hwf : (frameEnv m0 d 208 [x1, (a, 40)]).WF) (hm : Match (frameEnv m0 d 208 [x1, (a, 40)]) S d')
    (hfr : FrW 8 40 S = true) (hin : InR 2 40 S = true) :
    NativeRustcVm.SameOutside d.dmem d'.dmem fun q ↦
      (sp m0 - 200 ≤ q.toNat ∧ q.toNat < sp m0 - 168) ∨
      (a.toNat ≤ q.toNat ∧ q.toNat < a.toNat + 40) := by
  have hfb := g.fb_toNat
  have h0 := g.s0
  refine fun q hq ↦ hm.get?_mem0 hwf fun ⟨w, hw, b, sz, hb, h1, h2⟩ ↦ hq ?_
  have hf := List.all_eq_true.mp hfr w hw
  have hi := List.all_eq_true.mp hin w hw
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hf hi
  match hr : w.r, hb with
  | 0, hb =>
    cases hb
    left
    rcases hf with hf | hf
    · exact absurd hr hf
    · rw [hfb] at h1 h2; omega
  | 1, _ =>
    rcases hi with hi | hi
    · omega
    · omega
  | 2, hb =>
    cases hb
    right
    rcases hi with hi | hi
    · omega
    · omega
  | r + 3, hb => cases hb


theorem toBitVec_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toBitVec = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [UInt64.toNat_toBitVec, BitVec.toNat_ofNat, toNat_toUInt64_of_lt h, Nat.mod_eq_of_lt h]

/-- **Node `i`'s sibling written** (a block writing the frame's `8` to `40` and the 40 bytes of
sibling `i`): the frame kept, the siblings one more, the parents and node `i`'s next check kept,
the sibling's digest at the frame's `8`. -/
theorem sib_mem [Labels] (g : Geo m0 bp B.length) (hl : ns.length = cnt m0) {i : Nat}
    {sl : List (Nat × Digest × Bool)} {ci : Nat} {d d' : MachineData} {x1 : BitVec 64 × Nat}
    {S : SState} (hf : Frame m0 208 slots 8 d)
    (hmm : MemS m0 bp B ns (sn sl) (parentsOf (ns.take i) sl) ci d.dmem)
    (hnx : Nx m0 (i + 1) d.dmem) (hlt : i < cnt m0) (hsl : sl.length = i) (hi : i < ns.length)
    (hwf : (frameEnv m0 d 208 [x1, (off (sibs m0) (40 * i), 40)]).WF)
    (hm : Match (frameEnv m0 d 208 [x1, (off (sibs m0) (40 * i), 40)]) S d')
    (hok : MidOk 208 8 slots S = true) (hfr : FrW 8 40 S = true) (hin : InR 2 40 S = true)
    {src : Nat → Sym} {ks : Sym} (hd : WordsW 0 8 src S) (hk : WordW 2 0 ks S)
    (hw : WordsW 2 8 src S) {D : Digest}
    (hsrc : ∀ t (ht : t < 4), (src t).eval (frameEnv m0 d 208 [x1, (off (sibs m0) (40 * i), 40)]) =
      (D.toList[t]'(by simpa using ht)).toBitVec)
    (hks : ks.eval (frameEnv m0 d 208 [x1, (off (sibs m0) (40 * i), 40)]) =
      BitVec.ofNat 64 (ns[i]).1) (b : Bool) :
    Frame m0 208 slots 8 d' ∧
      MemS m0 bp B ns (sn (sl ++ [((ns[i]).1, D, b)])) (parentsOf (ns.take i) sl) ci d'.dmem ∧
      Nx m0 (i + 1) d'.dmem ∧ WordsAt d'.dmem (off (fb m0) 8) D.toList := by
  have h0 := g.s0
  have hn := g.n256
  have hs := sib_same g hwf hm hfr hin
  have hti := g.sb_toNat (o := 40 * i) (by omega)
  rw [hti] at hs
  have hkey := (hmm.nd i hi).1
  have hsS := g.sS
  have hsN := g.sN
  have hlen : (sn sl).length = i := by simp [hsl]
  have hnode : NodeAt d'.dmem (off (sibs m0) (40 * (sn sl).length)) ((ns[i]).1, D) := by
    rw [hlen]
    refine ⟨hkey, ?_, wordsAt_written hm (r := 2) (o := 8) rfl (by decide) hw hsrc⟩
    have := wordAt_written hm (r := 2) (o := 0) rfl (by decide) hk
      (hks.trans (toBitVec_toUInt64 hkey).symm)
    rwa [off_zero] at this
  have hk' := hmm.keep g hl hs fun q hq ↦ by unfold Mov; rw [hlen]; omega
  refine ⟨Frame.of_block hf hwf hm hok slots_le, ⟨hk'.rd, ?_, hk'.nx, hk'.nd, hk'.loc, hk'.chg,
    by simp; omega, hk'.lp⟩, hnx.keep g hs fun q hq ↦ by omega,
    wordsAt_written hm (r := 0) (o := 8) rfl (by decide) hd hsrc⟩
  rw [sn, List.map_append]
  exact nodesAt_snoc' hmm.sb (by rw [hlen]; omega) hnode hs fun q hq ↦ by rw [hlen]; omega


/-- Sibling `i`'s address, as `slotA .r15 .r12` computes it. -/
theorem sib_alias [Labels] {i : Nat} {d : MachineData} {rest : List (BitVec 64 × Nat)}
    (h15 : reg d .r15 = sibs m0) (h12 : reg d .r12 = BitVec.ofNat 64 i) :
    (slotA .r15 .r12).eval (frameEnv m0 d 208 rest) = off (sibs m0) (40 * i) + BitVec.ofInt 64 0 := by
  show BinOp.apply .add .W64 (reg d .r15) (BinOp.apply .mul .W64 (BinOp.apply .add .W64
    (reg d .r12) (BinOp.apply .mul .W64 (reg d .r12) (BitVec.ofNat 64 4))) (BitVec.ofNat 64 8)) = _
  rw [h15, h12, slot_eval, NativeRustcVmX64.Transcript.ofInt_zero64, BitVec.add_zero]

/-- The key's parity test: `jne` taken for an odd key. -/
theorem odd_cond {n : Nat} (h : n < 2 ^ 64) {x : BitVec 64} (hx : x = BitVec.ofNat 64 n) :
    (!CmpOp.apply .eq .W8 (BinOp.apply .and .W8 x (BitVec.ofNat 64 1)) (BitVec.ofNat 64 0)) =
      decide (n % 2 = 1) := by
  rw [and1_eq, hx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  by_cases h1 : n % 2 = 1
  · rw [decide_eq_true h1, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h1, decide_eq_true (by omega)]; rfl

variable [Host] {k : Nat}

section
variable (hp : Placed code k) (g : Geo m0 bp B.length) (hl : ns.length = cnt m0)
include hp g hl

/-- **The sibling found** (`b7`, node `j`): written; an odd key's parent none, the next node's
check; an even key's (`b8`) the parent. -/
theorem found_spec (hh : Spec (Labels.label NativeRustcVmX64.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    {i : Nat} {sl : List (Nat × Digest × Bool)} {ci j : Nat} {st : MachineState}
    (hF : Fnd k m0 bp B c ns i sl ci j st) :
    Eventually (step1 Host.exe) (fun st' ↦ ∃ sl' ci', Nxt k m0 bp B c ns (i + 1) sl' ci' st') st := by
  have hi := hF.hi
  have hj := hF.hj
  have hcur := hF.cur
  have h0 := g.s0
  have hn := g.n256
  have hlt := hcur.lt
  have hsl : sl.length = i := by
    rw [sibsM_length B ns _ c hcur.hs, List.length_take]; omega
  have hs' := sibsM_step hcur.hs hi (sibStep_found hi hj hF.kj hF.miss)
  have hkey := (hcur.mm.nd i hi).1
  obtain ⟨hmid, hfr, hin, hd, hk, hw, hK⟩ := ok_b7
  have hjA := g.nd_area hcur.fr (o := 40 * j) (n := 40) (by omega) (by omega)
  have hiA := g.sb_area hcur.fr (o := 40 * i) (n := 40) (by omega) (by omega)
  have htj := g.nd_toNat (o := 40 * j) (by omega)
  have hti := g.sb_toNat (o := 40 * i) (by omega)
  have hnX := g.nX
  have hwf : (frameEnv m0 st.data 208 [(nd m0 j, 40), (off (sibs m0) (40 * i), 40)]).WF :=
    g.wf_rest hcur.fr (fun x hx ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact hjA
        · exact hiA)
      (List.pairwise_pair.mpr (by dsimp only; rw [htj, hti]; omega))
  have hm : Match (frameEnv m0 st.data 208 [(nd m0 j, 40), (off (sibs m0) (40 * i), 40)]) fndS
      st.data :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hcur.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨by
        show reg st.data .rax = nd m0 j + BitVec.ofInt 64 0
        rw [NativeRustcVmX64.Transcript.ofInt_zero64, BitVec.add_zero]; exact hF.rax,
       sib_alias hcur.r15 hcur.r12, trivial⟩
  refine exec_at (Wire.infix_of b7_in_code (by simp [b7]) hp) exit_b7 hwf nofun hF.pc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hf1, hmm1, hnx1, hdg1⟩ := sib_mem g hl hcur.fr hcur.mm hcur.nx hlt hsl hi hwf hm1 hmid
    hfr hin hd hk hw (D := (ns[j]).2) (fun t ht ↦ by
      have hw' := (NativeRustcVm.wordsAt_iff.mp (hcur.mm.nd j hj).2.2) t (by simpa using ht)
      rw [NativeRustcVm.addr_add_add] at hw'
      exact Wire.load_word hw') hF.r13 true
  have hk1 := regs_kept hK fun r v h ↦ hm1.regs r v h
  have hpc2 := pc_cond hpc1 (P := (ns[i]).1 % 2 = 1) (by
    show (!CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg st.data .r13) (BitVec.ofNat 64 1))
      (BitVec.ofNat 64 0)) = _
    exact odd_cond hkey hF.r13)
  have hrbx := (hk1 .rbx (by simp [loopRegs])).trans hcur.rbx
  have hr14 := (hk1 .r14 (by simp [loopRegs])).trans hcur.r14
  have hr15 := (hk1 .r15 (by simp [loopRegs])).trans hcur.r15
  by_cases hod : (ns[i]).1 % 2 = 1
  · -- An odd key, its sibling a node: no parent.
    rw [ite_t hod, hp.label NativeRustcVmX64.Vm.ClimbLevel.label_7_at] at hpc2
    have hpar : parentsOf (ns.take (i + 1)) (sl ++ [((ns[i]).1, (ns[j]).2, true)]) =
        parentsOf (ns.take i) sl := by
      rw [take_succ_eq hi, parentsOf_snoc (by rw [take_length_of_le (by omega), hsl]),
        parent_none hod rfl, List.append_nil]
    refine .done _ ⟨_, _, hpc2, hf1, hs', by rw [hpar]; exact hmm1, hnx1, by omega, by omega,
      by rw [hpar]; exact hrbx, hr14, hr15⟩
  · rw [ite_f hod] at hpc2
    refine fr_step hp g (j := NativeRustcVmX64.Vm.ClimbLevel.b8Offset) b8_in_code (by simp [b8]) exit_b8 nofun ok_b8.1
      (hpc2.trans (congrArg Host.addrOf rfl)) hf1 fun st2 hf2 hd2 hr2 hpc3 ↦ ?_
    simp only [PcOk, hp.label NativeRustcVmX64.Vm.ClimbLevel.label_13_at] at hpc3
    have hk2 := regs_kept ok_b8.2 hr2
    have hM : Mid m0 bp B c ns i sl ci ((ns[i]).1, (ns[j]).2, true) st2.data :=
      ⟨hf2, hs', hd2 ▸ hmm1, hd2 ▸ hnx1, hd2 ▸ hdg1, hlt, hsl, fun _ ↦ rfl,
        (hk2 .rbp (by simp [loopRegs])).trans ((hk1 .rbp (by simp [loopRegs])).trans hcur.rbp),
        (hk2 .r13 (by simp)).trans ((hk1 .r13 (by simp)).trans hF.r13),
        (hk2 .r12 (by simp [loopRegs])).trans ((hk1 .r12 (by simp [loopRegs])).trans hcur.r12),
        (hk2 .rbx (by simp [loopRegs])).trans hrbx, (hk2 .r14 (by simp [loopRegs])).trans hr14,
        (hk2 .r15 (by simp [loopRegs])).trans hr15⟩
    exact Eventually.mono (pair_spec hp g hl hh hM hi (.inl ⟨hpc3, by omega⟩))
      fun _ h ↦ ⟨_, _, h⟩

end

end

end NativeRustcVmX64.Wire.ClimbLevel
