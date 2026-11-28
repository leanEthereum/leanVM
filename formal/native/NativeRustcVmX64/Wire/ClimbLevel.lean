module

public import NativeRustcVmX64.Wire.ClimbLevel.Loop
public import NativeRustcVmX64.Code.Vm.ClimbLevel.Names
public import NativeRustcVmX64.Code.Vm.HashPair.Names
public import NativeRustcVmX64.Code.Vm.ReaderDigest.Names

/-!
# `climb_level` meets its contract (x86-64)

`climbLevel_spec`: the prologue (`b0`, the reader saved at offset `40` of the frame); no node
(`b20`, then `Some 0`), or the set-up (`b1`, the locals) and the loop over the nodes
(`loop_spec`). The nodes are the words in memory (`exists_nodesAt`), the only ones there
(`NodesAt.unique`, in `post_of`).
-/

namespace NativeRustcVmX64.Wire.ClimbLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.ClimbLevel
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap match_rsp
  Frame.of_prologue after after_eq MidOk sameOutside_low)
open NativeRustcVm.Transcript (off off_zero)
open NativeRustcVm (WordAt WordsAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open NativeRustcVmX64.Wire (pc_cond ite_t ite_f eq64)
open NativeRustcVmX64.Sumcheck (wordAt_written)

public section

/-! ## Nodes in memory -/

/-- One node more, after them. -/
theorem nodesAt_append_one {d : Mem 64} {a : BitVec 64} {l : List (Nat × Digest)}
    {x : Nat × Digest} (h : NodesAt d a l) (hx : NodeAt d (a + BitVec.ofNat 64 (40 * l.length)) x) :
    NodesAt d a (l ++ [x]) := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
  · rw [List.getElem_append_left hj]; exact h j hj
  · rw [List.getElem_append_right (le_refl _)]; simpa using hx

/-- **A digest's words**, one by one. -/
theorem wordsAt_digest_iff {d : Mem 64} {a : BitVec 64} {dg : Digest} :
    WordsAt d a dg.toList ↔ WordAt d a dg[0] ∧ WordAt d (a + BitVec.ofNat 64 8) dg[1] ∧
      WordAt d (a + BitVec.ofNat 64 16) dg[2] ∧ WordAt d (a + BitVec.ofNat 64 24) dg[3] := by
  obtain ⟨⟨l⟩, hl⟩ := dg
  match l, hl with
  | [w0, w1, w2, w3], _ =>
    show WordsAt d a [w0, w1, w2, w3] ↔ _
    simp only [NativeRustcVm.wordsAt_cons_iff, NativeRustcVm.addr_add_add]
    rw [show WordsAt d (a + BitVec.ofNat 64 (8 + 8 + 8 + 8)) [] ↔ True from
      iff_true_intro (NativeRustcVm.wordsAt_nil _ _), and_true]
    rfl

/-- **A node's words**: its key, its digest's. -/
theorem nodeAt_iff {d : Mem 64} {a : BitVec 64} {x : Nat × Digest} :
    NodeAt d a x ↔ x.1 < 2 ^ 64 ∧ WordAt d a x.1.toUInt64 ∧ WordAt d (a + BitVec.ofNat 64 8) x.2[0] ∧
      WordAt d (a + BitVec.ofNat 64 16) x.2[1] ∧ WordAt d (a + BitVec.ofNat 64 24) x.2[2] ∧
      WordAt d (a + BitVec.ofNat 64 32) x.2[3] := by
  unfold NodeAt
  rw [show off a 8 = a + BitVec.ofNat 64 8 from rfl, wordsAt_digest_iff]
  simp only [NativeRustcVm.addr_add_add]

/-- **Mapped memory holds nodes.** -/
theorem exists_nodesAt {d : Mem 64} {a : BitVec 64} :
    ∀ n : Nat, NativeRustcVm.Mapped d a (40 * n) → ∃ ns : List (Nat × Digest),
      ns.length = n ∧ NodesAt d a ns
  | 0, _ => ⟨[], rfl, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩
  | n + 1, h => by
    obtain ⟨h1, h2⟩ := (NativeRustcVm.mapped_append_iff (n := 40 * n) (m := 40)).mp
      (by rwa [Nat.mul_succ] at h)
    obtain ⟨ns, hl, hns⟩ := exists_nodesAt n h1
    obtain ⟨L, hL, hw⟩ := exists_wordsAt (d := d) 5 _ h2
    match L, hL, hw with
    | [w0, w1, w2, w3, w4], _, hw =>
      refine ⟨ns ++ [(w0.toNat, #v[w1, w2, w3, w4])], by simp [hl], nodesAt_append_one hns ?_⟩
      rw [hl]
      have g := fun (i : Nat) (hi : i < 5) ↦ hw.getElem (i := i) (by simpa using hi)
      refine nodeAt_iff.mpr ⟨UInt64.toNat_lt _, ?_, g 1 (by omega), g 2 (by omega),
        g 3 (by omega), g 4 (by omega)⟩
      have := g 0 (by omega)
      rw [Nat.mul_zero, NativeRustcVm.addr_add_zero] at this
      simpa using this

/-! ## `40 n` -/

theorem add64 (a b : BitVec 64) : BinOp.apply .add .W64 a b = a + b := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem shl3 (x : BitVec 64) :
    BinOp.apply .shl .W64 x (BitVec.ofNat 64 3) = BitVec.ofNat 64 (8 * x.toNat) := by
  have hs : shiftCount .W64 (BitVec.ofNat 64 3) = 3 := by decide
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, low_W64, ext_W64, hs, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  omega

/-- `40 n`, as `b1` computes it (`n40`). -/
theorem n40_eval [Labels] {env : Env} :
    n40.eval env = BitVec.ofNat 64 (40 * ((Sym.reg .rdx).eval env).toNat) := by
  show BinOp.apply .add .W64 (BinOp.apply .shl .W64 ((Sym.reg .rdx).eval env) (BitVec.ofNat 64 3))
    (BinOp.apply .mul .W64 (BinOp.apply .shl .W64 ((Sym.reg .rdx).eval env) (BitVec.ofNat 64 3))
      (BitVec.ofNat 64 4)) = _
  rw [shl3]
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_mul,
    BitVec.toNat_ofNat]
  omega

variable [Host] {k : Nat} {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
  {ns : List (Nat × Digest)}

/-- **From the entry.** -/
theorem entry_spec (hp : Placed code k) (g : Geo m0 bp B.length)
    (hh : Spec (Labels.label NativeRustcVmX64.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    (hd : Spec (Labels.label NativeRustcVmX64.Vm.ReaderDigest.entryLabel) ReaderDigestPre ReaderDigestPost)
    (hR : ReaderAt m0.dmem (rdr m0) bp B c)
    (hns : NodesAt m0.dmem (nodes m0) ns) (hl : ns.length = cnt m0) :
    Eventually (step1 Host.exe) (Post m0) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.ClimbLevel.b0Offset)⟩ := by
  have hst := g.g.st
  have h0 := g.s0
  have hsp := sp_eq m0
  have hfb : (stackBelow m0 208).toNat = sp m0 - 208 := g.fb_toNat
  have hn := g.n256
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 208) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨frame_mapped hst (by decide), frame_noWrap hst (by decide)⟩ (by simp)
    (List.pairwise_singleton _ _)
  have hm0 : Match (frameEnv m0 m0 208 []) entryS m0 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial
  refine exec_then (Wire.infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 nofun hm0
    fun s1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hws1, hw40, hrax1, hK1⟩ := ok_b0
  have hf1 : Frame m0 208 slots 8 s1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le (by decide)
  have hs1 : NativeRustcVm.SameOutside m0.dmem s1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 208) 208) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hws1
  have hR208 : ∀ q, NativeRustcVm.InRange (stackBelow m0 208) 208 q →
      sp m0 - 208 ≤ q.toNat ∧ q.toNat < sp m0 := fun q hq ↦ by
    rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [hfb]; omega), hfb] at hq
    omega
  have hR1 : ReaderAt s1.data.dmem (rdr m0) bp B c :=
    g.reader hR hs1 fun q hq ↦ .inl (by have := hR208 q hq; omega)
  have chg1 : Chg m0 s1.data.dmem := fun q hq ↦ hs1 q fun h ↦ hq (.inl (by
    have := hR208 q h; omega))
  have hk1 := regs_kept hK1 fun r v h ↦ hm1.regs r v h
  have hpc2 := pc_cond hpc1 (P := cnt m0 = 0) (by
    show CmpOp.apply .eq .W64 (BinOp.apply .and .W64 (reg m0 .rdx) (reg m0 .rdx))
      (BitVec.ofNat 64 0) = _
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.and_self]
    rw [eq64, BitVec.toNat_ofNat])
  by_cases h0n : cnt m0 = 0
  · -- `b20`: no node, `Some 0`.
    rw [ite_t h0n, hp.label NativeRustcVmX64.Vm.ClimbLevel.label_1_at] at hpc2
    obtain rfl : ns = [] := List.eq_nil_of_length_eq_zero (hl.trans h0n)
    obtain ⟨hok20, hrbx20, hK20⟩ := ok_b20
    refine fr_step hp g (j := NativeRustcVmX64.Vm.ClimbLevel.b20Offset) b20_in_code (by simp [b20]) exit_b20 nofun hok20 hpc2 hf1
      fun s2 hf2 hd2 hr2 hpc3 ↦ ?_
    simp only [PcOk] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.ClimbLevel.label_11_at] at hpc3
    refine fin hp g hR hns hl hpc3 hf2 ?_ (by rw [hd2]; exact chg1)
    unfold Res
    rw [show sibsM B [] [] c = some ([], c) from rfl]
    dsimp only
    refine ⟨?_, ?_, fun _ h ↦ absurd h (by simp), fun _ h ↦ absurd h (by simp [parentsOf]),
      by rw [hd2]; exact hR1⟩
    · exact (regs_kept hK20 hr2 .rax (by simp)).trans (hm1.regs .rax _ hrax1)
    · exact (congrArg BitVec.toNat (hr2 .rbx _ hrbx20)).trans rfl
  · -- `b1`: the locals, then the loop's head after no node.
    rw [ite_f h0n] at hpc2
    obtain ⟨hmid1, hfw1, hw48, hw56, hw64, hrbx1, hr12_1, hrbp1, hr14_1, hr15_1⟩ := ok_b1
    refine fw_step hp g (j := NativeRustcVmX64.Vm.ClimbLevel.b1Offset) b1_in_code (by simp [b1]) exit_b1 nofun hmid1 hfw1
      (hpc2.trans (congrArg Host.addrOf rfl)) hf1 fun s2 hf2 hs2 hm2 hpc3 ↦ ?_
    simp only [PcOk] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.ClimbLevel.label_3_at] at hpc3
    have ersi : (Sym.reg .rsi).eval (frameEnv m0 s1.data 208 []) = reg m0 .rsi :=
      hk1 .rsi (by simp)
    have erdx : (Sym.reg .rdx).eval (frameEnv m0 s1.data 208 []) = reg m0 .rdx :=
      hk1 .rdx (by simp)
    have hn40 : n40.eval (frameEnv m0 s1.data 208 []) = BitVec.ofNat 64 (40 * cnt m0) := by
      rw [n40_eval, erdx]
    have hfo := fun (o : Nat) (ho : o < 216) ↦ g.fo (o := o) ho
    have hnw : (nodes m0).toNat + 40 * ns.length ≤ 2 ^ 64 := by rw [hl]; exact g.nN
    have hnS := g.nS
    have hloc : Loc m0 s2.data.dmem := by
      refine ⟨wordAt_keep (wordAt_written hm1 (r := 0) (o := 40) rfl (by decide) hw40
            (w := UInt64.ofBitVec (rdr m0)) rfl)
          (by rw [hfo 40 (by omega)]; omega) hs2 fun q hq ↦ by rw [hfo 40 (by omega)]; omega,
        wordAt_written hm2 (r := 0) (o := 48) rfl (by decide) hw48 ?_,
        wordAt_written hm2 (r := 0) (o := 56) rfl (by decide) hw56 ?_,
        wordAt_written hm2 (r := 0) (o := 64) rfl (by decide) hw64 ?_⟩
      · show BinOp.apply .add .W64 ((Sym.reg .rsi).eval (frameEnv m0 s1.data 208 []))
          (n40.eval (frameEnv m0 s1.data 208 [])) = _
        rw [ersi, hn40, add64]
      · show BinOp.apply .add .W64 ((Sym.reg .rsi).eval (frameEnv m0 s1.data 208 []))
          (BitVec.ofNat 64 18446744073709551576) = _
        rw [ersi, add64]
      · rw [hn40]
    have hmm : MemS m0 bp B ns (sn []) (parentsOf (ns.take 0) []) c s2.data.dmem :=
      ⟨g.reader hR1 hs2 fun q hq ↦ .inl (by omega), fun _ h ↦ absurd h (by simp [sn]),
        fun _ h ↦ absurd h (by simp [parentsOf]),
        nodesAt_keep (nodesAt_keep hns hnw hs1 fun q hq ↦ by have := hR208 q hq; omega) hnw hs2
          fun q hq ↦ by omega,
        hloc, chg_trans chg1 hs2 fun q hq ↦ .inl (by omega), by simp [sn],
        by simp [parentsOf]⟩
    refine loop_spec hp g hl hh hd hR hns (i := 0) (sl := []) (ci := c)
      ⟨hpc3, hf2, by simp [sibsM], hmm, by omega, ?_, hm2.regs .r12 _ hr12_1, ?_, ?_, ?_⟩
    · refine (hm2.regs .rbp _ hrbp1).trans ?_
      show (Sym.reg .rsi).eval (frameEnv m0 s1.data 208 []) = off (nodes m0) (40 * 0)
      rw [ersi, Nat.mul_zero, off_zero]
    · exact (hm2.regs .rbx _ hrbx1).trans (show BitVec.ofNat 64 0 = _ by simp [parentsOf])
    · exact (hm2.regs .r14 _ hr14_1).trans (hk1 .r8 (by simp))
    · exact (hm2.regs .r15 _ hr15_1).trans (hk1 .rcx (by simp))

/-- **`climb_level` meets its contract.** -/
theorem climbLevel_spec (hp : Placed code k)
    (hh : Spec (Labels.label NativeRustcVmX64.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    (hd : Spec (Labels.label NativeRustcVmX64.Vm.ReaderDigest.entryLabel) ReaderDigestPre ReaderDigestPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.ClimbLevel.entryLabel) ClimbLevelPre ClimbLevelPost := by
  intro m0 hpre
  obtain ⟨-, -, -, ⟨hnm, -⟩, -, -, bp, B, c, hR, -⟩ := id hpre
  obtain ⟨ns, hlen, hns⟩ := exists_nodesAt (d := m0.dmem) (a := nodes m0) (cnt m0) hnm
  rw [hp.label NativeRustcVmX64.Vm.ClimbLevel.entry_at]
  exact entry_spec hp (geo_of hpre hR) hh hd hR hns hlen

end

end NativeRustcVmX64.Wire.ClimbLevel
