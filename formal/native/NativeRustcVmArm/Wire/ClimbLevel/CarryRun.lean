module

public import NativeRustcVmArm.Code.Vm.HashPair.Names
public import NativeRustcVmArm.Code.Vm.ReaderDigest.Names
public import NativeRustcVmArm.Wire.ClimbLevel.Carry
public import NativeRustcVmArm.Wire.ClimbLevel.Ret

/-!
# `climb_level`'s sibling read, run

`carry_spec`: `Reader::digest` (`b11`), its tag (`b12`), the sibling written (`b13`), the parent
hashed.
-/

namespace NativeRustcVmArm.Wire.ClimbLevel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.ClimbLevel
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable [Host] {k : Nat} {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
  {ns : List (Nat × Digest)}

omit [Host] in
theorem saved10 : ∀ r ∈ [XReg.X19, .X20, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
    calleeSaved r = true := by decide

/-- **The sibling written** (`b13`) from the digest at SP+32, then the parent hashed. -/
theorem b13_spec (hp : Placed code k) (G : Geo m0 bp B)
    (hh : Spec (Labels.label NativeRustcVmArm.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    (hns : NodesAt m0.dmem (nodes m0) ns) (hlen : ns.length = cnt m0) {i : Nat}
    {sl : List (Nat × Digest × Bool)} {ci : Nat} {dg : Digest} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b13Offset)) (hfr : Frm m0 st.data) (hfx : Fix m0 st.data)
    (hlt : i < cnt m0) (hi : i < ns.length)
    (hs : sibsM B ns (ns.take (i + 1)) c = some (sl ++ [(ns[i].1, dg, false)], ci))
    (hrd : ReaderAt st.data.dmem (rdr m0) bp B ci)
    (hsb : NodesAt st.data.dmem (sibs m0) (sl.map fun s ↦ (s.1, s.2.1)))
    (hnx : NodesAt st.data.dmem (nxt m0) (parentsOf (ns.take i) sl)) (hl : sl.length = i)
    (hw : WordsAt st.data.dmem (base m0 224 + BitVec.ofNat 64 32) dg.toList)
    (h19 : (st.data.regs.getXReg .X19).toNat = (parentsOf (ns.take i) sl).length)
    (h20 : (st.data.regs.getXReg .X20).toNat = i + 1)
    (h23 : (st.data.regs.getXReg .X23).toBitVec = nd m0 (i + 1))
    (h24 : (st.data.regs.getXReg .X24).toBitVec = nd m0 i)
    (h26 : (st.data.regs.getXReg .X26).toNat = i) :
    Eventually (step1 Host.exe)
      (Head m0 bp B c ns k (i + 1) (sl ++ [(ns[i].1, dg, false)]) ci) st := by
  have hn := G.n256
  have hsp := G.sp
  have h224 := stack224
  have hi256 : i < 256 := by omega
  have := G.ndNw; have := G.sbNw; have := G.nS; have := G.sS; have := G.nSb
  have hnd0 := G.nd0 hlt
  have hsb0 := G.sb0 hi256
  have hwf : (Env.ofMachine st.data [(base m0 224, 224), (nd m0 i, 8), (sb m0 i, 40)]).WF :=
    G.env3_wf hfr (G.ndMap' hlt (by omega)) (by rw [hnd0]; omega) (by rw [hnd0]; omega)
      (G.sbMap' hi256) (by rw [hsb0]; omega) (by rw [hsb0]; omega) (by rw [hnd0, hsb0]; omega)
  have hm : Match (Env.ofMachine st.data [(base m0 224, 224), (nd m0 i, 8), (sb m0 i, 40)])
      carS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ G.aligned, rfl, nofun, rfl, nofun, trivial⟩
      (by rw [hfr.sp]; simp [Sym.eval])
      ⟨by
        show (st.data.regs.getXReg .X27).toBitVec = base m0 224 + BitVec.ofInt 64 24
        rw [hfx.x27]; rfl, trivial⟩ trivial trivial
      ⟨by
        show (st.data.regs.getXReg .X24).toBitVec = nd m0 i + BitVec.ofInt 64 0
        rw [h24, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero],
      by
        show sibAddr.eval _ = sb m0 i + BitVec.ofInt 64 0
        rw [sibAddr_eval hi256 h26 hfx.x22 G.sbNw, show BitVec.ofInt 64 0 = 0#64 from rfl,
          BitVec.add_zero], trivial⟩
  refine exec_at (infix_of b13_in_code (by simp [b13]) hp) run_b13 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : Frm m0 st1.data := G.frm_block hfr hm hm1 hwf rfl rfl rfl (r1 := 2) (by decide)
    rfl (fun t ht ↦ G.sb_outs hi256 ht) (by decide)
  have hS := G.block_same (ls := i) (lp := 256) hm1 hwf rfl (r1 := 2) rfl
    (fun t ht ↦ ⟨G.sb_keep hi256 ht 256, G.sb_cur hi256 ht⟩) (by decide)
  have hk1 := NativeRustcVm.SameOutside.mono hS fun _ h ↦ h.1
  have hr : ∀ r ∈ [XReg.X19, .X20, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
      st1.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Match.reg_eq hm hm1 rfl rfl
  have hnk := nodeAt_iff.mp (G.nodes_frm hlen hns hfr i hi)
  have k0 : WordAt st.data.dmem (nd m0 i + BitVec.ofNat 64 0) ns[i].1.toUInt64 := by
    rw [NativeRustcVm.addr_add_zero]; exact hnk.2.1
  have hkey := hnk.1
  have hdw := wordsAt_digest_iff.mp hw
  simp only [NativeRustcVm.addr_add_add] at hdw
  obtain ⟨w1, w2, w3, w4⟩ := hdw
  have hl1 : (Env.ofMachine st.data [(base m0 224, 224), (nd m0 i, 8), (sb m0 i, 40)]).load 1 0 8
      = ns[i].1.toUInt64.toBitVec := load_of rfl k0
  let q : Nat × Digest × Bool := (ns[i].1, dg, false)
  have hnode : NodeAt st1.data.dmem (sb m0 i) (q.1, q.2.1) :=
    node_write hm1 (r := 2) (v0 := .load 1 0 8) (v1 := .load 0 32 8) (v2 := .load 0 40 8)
      (v3 := .load 0 48 8) (v4 := .load 0 56 8) rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) hkey (by simp only [Sym.eval]; rw [hl1])
      (by simp only [Sym.eval]; rw [load_of rfl w1])
      (by simp only [Sym.eval]; rw [load_of rfl w2])
      (by simp only [Sym.eval]; rw [load_of rfl w3])
      (by simp only [Sym.eval]; rw [load_of rfl w4])
  have hdg : WordsAt st1.data.dmem (base m0 224 + BitVec.ofNat 64 64) q.2.1.toList :=
    digest_write hm1 (r := 0) (o := 64) (sz := 224) (v1 := .load 0 32 8) (v2 := .load 0 40 8)
      (v3 := .load 0 48 8) (v4 := .load 0 56 8) rfl (by omega) (by decide) (by decide)
      (by decide) (by decide)
      (by simp only [Sym.eval]; rw [load_of rfl w1])
      (by simp only [Sym.eval]; rw [load_of rfl w2])
      (by simp only [Sym.eval]; rw [load_of rfl w3])
      (by simp only [Sym.eval]; rw [load_of rfl w4])
  have h21 : (st1.data.regs.getXReg .X21).toNat = ns[i].1 := by
    show (st1.data.regs.getXReg .X21).toBitVec.toNat = _
    rw [hm1.regs .X21 _ rfl]
    simp only [Sym.eval]
    rw [hl1, UInt64.toNat_toBitVec, toNat_toUInt64_of_lt hkey]
  have hM : Mid m0 bp B c ns i sl ci q st1.data := by
    refine ⟨hfr1, hfx.keep fun r h ↦ hr r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with rfl | rfl | rfl | rfl | rfl <;> simp), hlt, hs,
      G.keep_reader (by omega) (by omega) hS (fun _ h ↦ h) hrd, ?_,
      G.keep_nxt (by omega) (by omega) hk1
        (by have := parentsOf_length_le (ns.take i) sl; have := List.length_take_le i ns; omega)
        hnx,
      hl, fun _ ↦ rfl, hdg, by rw [hr .X19 (by simp)]; exact h19,
      by rw [hr .X20 (by simp)]; exact h20, h21,
      by rw [hr .X23 (by simp)]; exact h23, by rw [hr .X24 (by simp)]; exact h24⟩
    rw [List.map_append, List.map_singleton]
    refine NodesAt.append_one (G.keep_sibs (by omega) (by omega) hk1 (by simp [hl]) hsb) ?_
    rw [List.length_map, hl]
    exact hnode
  have hc : (SBool.bit .W32 (.load 1 0 8) 0).eval
      (Env.ofMachine st.data [(base m0 224, 224), (nd m0 i, 8), (sb m0 i, 40)]) =
      decide (ns[i].1 % 2 = 1) := by
    simp only [SBool.eval, Sym.eval]
    rw [bit0_low, hl1, UInt64.toNat_toBitVec, toNat_toUInt64_of_lt hkey]
  simp only [PcOk, hc] at hpc1
  by_cases hodd : ns[i].1 % 2 = 1
  · simp only [hodd, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.ClimbLevel.b2Offset) NativeRustcVmArm.Vm.ClimbLevel.label_2_at] at hpc1
    exact hash2_spec hp G hh hns hlen hpc1 hM hi (parent_odd hodd rfl)
  · simp only [hodd, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    exact hash14_spec hp G hh hns hlen (hpc1.trans (congrArg Host.addrOf rfl)) hM hi
      (parent_even (by omega))

/-- **No node of key `k ^^^ 1`** (`b11`): the sibling read by `Reader::digest`; `None`, or the
loop's head after node `i`. -/
theorem carry_spec (hp : Placed code k) (G : Geo m0 bp B)
    (hh : Spec (Labels.label NativeRustcVmArm.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    (hd : Spec (Labels.label NativeRustcVmArm.Vm.ReaderDigest.entryLabel) ReaderDigestPre ReaderDigestPost)
    (hR : ReaderAt m0.dmem (rdr m0) bp B c)
    (hns : NodesAt m0.dmem (nodes m0) ns) (hlen : ns.length = cnt m0) {i : Nat}
    {sl : List (Nat × Digest × Bool)} {ci : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b11Offset)) (hC : Cur m0 bp B c ns i sl ci st.data)
    (hi : i < ns.length) (hmiss : Miss ns i ns.length) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      ∃ sl' ci', Head m0 bp B c ns k (i + 1) sl' ci' st') st := by
  have hN := G.g.st.2.1
  have hwf := G.frEnv_wf hC.fr
  have hm := G.frEnv_match hC.fr
  refine exec_at (infix_of b11_in_code (by simp [b11]) hp) run_b11 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hfr1 : Frm m0 st1.data := Fr.ofBlock hC.fr hm hm1 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have hx0 : st1.data.regs.X0.toBitVec = base m0 224 + BitVec.ofNat 64 24 := by
    rw [show st1.data.regs.X0 = st1.data.regs.getXReg .X0 from rfl, hm1.regs .X0 _ rfl]; rfl
  have hx1 : st1.data.regs.X1.toBitVec = rdr m0 := by
    rw [show st1.data.regs.X1 = st1.data.regs.getXReg .X1 from rfl, hm1.regs .X1 _ rfl]
    exact load_rdr hC.fr
  have hR1 : ReaderAt st1.data.dmem (rdr m0) bp B ci := by rw [hd1]; exact hC.dn.rd
  have hr1 : ∀ r ∈ [XReg.X19, .X20, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
      st1.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Match.reg_eq hm hm1 rfl rfl
  refine Fr.leafIn (lo := 24) (n := 40) (N' := readerDigestStack) hfr1 hN (by decide)
    (by decide) (by simp) (by decide) (fun q hq ↦ G.g.not_frame (by decide) hq)
    (Spec.carry hd fun m ↦ m.regs.X0.toBitVec = base m0 224 + BitVec.ofNat 64 24 ∧
      m.regs.X1.toBitVec = rdr m0)
    hpc1 ⟨G.digest_pre hfr1 hx0 hx1 hR1, hx0, hx1⟩ (fun m' ⟨⟨_, hs, hsv⟩, h0, h1⟩ ↦ ⟨?_, hsv⟩) ?_
  · refine NativeRustcVm.SameOutside.mono hs fun q ⟨r, hr, h⟩ ↦ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inl (by have h' : InRange st1.data.regs.X0.toBitVec 40 q := h; rwa [h0] at h'))
    · exact .inr (.inr (.inl (by
        have h' : InRange (st1.data.regs.X1.toBitVec + 16#64) 8 q := h; rwa [h1] at h')))
    · exact .inl h
  intro m2 hfr2 ⟨⟨hpost, hs2, _⟩, h0, h1⟩ hcs
  have hres := hpost bp B ci (by rw [h1]; exact hR1)
  have hs2' : SameOutside st1.data.dmem m2.dmem (InAny [⟨base m0 224 + BitVec.ofNat 64 24, 40⟩,
      curRegion (rdr m0), stackR st1.data readerDigestStack]) := by
    have := hs2
    simp only [h0, h1] at this
    exact this
  have hk2 := G.digest_same hfr1 hs2'
  have hr2 : ∀ r ∈ [XReg.X19, .X20, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
      m2.regs.getXReg r = st.data.regs.getXReg r := fun r hr ↦
    (hcs r (saved10 r hr)).trans (hr1 r hr)
  -- `b12`: the tag
  have hwf2 := G.frEnv_wf hfr2
  have hm2 := G.frEnv_match hfr2
  refine exec_at (infix_of b12_in_code (by simp [b12]) hp) run_b12 hwf2
    (congrArg Host.addrOf rfl) hm2 fun st2 hm2' hpc2 ↦ ?_
  have hd2 : st2.data.dmem = m2.dmem := hm2'.dmem_eq hwf2 rfl
  have hfr3 : Frm m0 st2.data := Fr.ofBlock hfr2 hm2 hm2' hwf2 rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have hr3 : ∀ r ∈ [XReg.X19, .X20, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
      st2.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    rw [← hr2 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Match.reg_eq hm2 hm2' rfl rfl
  have hsl : sl.length = i := by
    rw [sibsM_length B ns _ c hC.dn.hs, List.length_take]; omega
  rw [h0] at hres
  cases hrd : rdDigest B ci with
  | none =>
    rw [hrd] at hres
    have hl : (frEnv m0 m2).load 0 24 4 = BitVec.ofNat 64 0 :=
      Transcript.load4_of_tag (w := 0) (.inl rfl) hres
    have hc : (SBool.bit .W32 (.load 0 24 4) 0).not.eval (frEnv m0 m2) = true := by
      show (!(Sym.low .W32 ((frEnv m0 m2).load 0 24 4)).getLsbD 0) = true
      rw [hl]; rfl
    simp only [PcOk, hc, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.ClimbLevel.b16Offset) NativeRustcVmArm.Vm.ClimbLevel.label_12_at] at hpc2
    exact Eventually.mono (none_spec hp G hR hns hlen hpc2 hfr3
      (sibsM_none hC.dn.hs hi (by rw [sibStep_read hi hmiss, hrd]; rfl))) fun _ h ↦ .inl h
  | some p =>
    obtain ⟨dg, c'⟩ := p
    rw [hrd] at hres
    obtain ⟨ht, hw, hrd'⟩ := hres
    have hl : (frEnv m0 m2).load 0 24 4 = BitVec.ofNat 64 1 :=
      Transcript.load4_of_tag (w := 1) (.inr rfl) ht
    have hc : (SBool.bit .W32 (.load 0 24 4) 0).not.eval (frEnv m0 m2) = false := by
      show (!(Sym.low .W32 ((frEnv m0 m2).load 0 24 4)).getLsbD 0) = false
      rw [hl]; rfl
    simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc2
    have hw' : WordsAt st2.data.dmem (base m0 224 + BitVec.ofNat 64 32) dg.toList := by
      rw [hd2]
      have h' : WordsAt m2.dmem (base m0 224 + BitVec.ofNat 64 24 + BitVec.ofNat 64 8)
        dg.toList := hw
      rwa [NativeRustcVm.addr_add_add] at h'
    have hpl := parentsOf_length_le (ns.take i) sl
    have htl := List.length_take_le i ns
    have hn := G.n256
    refine Eventually.mono (b13_spec hp G hh hns hlen (hpc2.trans (congrArg Host.addrOf rfl))
      hfr3 (hC.fx.keep fun r h ↦ by
        rw [hr3 r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
          rcases h with rfl | rfl | rfl | rfl | rfl <;> simp)])
      hC.lt hi (sibsM_step hC.dn.hs hi (by rw [sibStep_read hi hmiss, hrd]; rfl))
      (by rw [hd2]; rw [h1] at hrd'; exact hrd') ?_ ?_ hsl hw'
      (by rw [hr3 .X19 (by simp)]; exact hC.x19)
      (by rw [hr3 .X20 (by simp)]; exact hC.x20) (by rw [hr3 .X23 (by simp)]; exact hC.x23)
      (by rw [hr3 .X24 (by simp)]; exact hC.x24) (by rw [hr3 .X26 (by simp)]; exact hC.x26))
      fun _ h ↦ .inr ⟨_, _, h⟩
    · rw [hd2]
      exact G.keep_sibs (le_refl _) (le_refl _) hk2 (by simp [hsl]; omega)
        (by rw [hd1]; exact hC.dn.sb)
    · rw [hd2]
      exact G.keep_nxt (le_refl _) (le_refl _) hk2 (by omega) (by rw [hd1]; exact hC.dn.nx)

end

end NativeRustcVmArm.Wire.ClimbLevel
