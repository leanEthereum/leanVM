module

public import NativeRustcVmArm.Wire.ClimbLevel.Step

/-!
# `climb_level`'s parent stored

`b4`: node `i`'s parent, its key halved and the hash at SP+96, at the parents' end; the loop's
head after node `i` (`store_spec`).
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
/-- The parents of the first `i < n ≤ 256` nodes: fewer than 256. -/
theorem parents_lt {i : Nat} {sl : List (Nat × Digest × Bool)} (hi : i < 256) :
    (parentsOf (ns.take i) sl).length < 256 := by
  have := parentsOf_length_le (ns.take i) sl
  have := List.length_take_le i ns
  omega

omit [Host] in
/-- The first `i + 1` nodes. -/
theorem take_succ_eq {i : Nat} (hi : i < ns.length) : ns.take (i + 1) = ns.take i ++ [ns[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some]

/-- **The parent stored** (`b4`): the loop's head after node `i`. -/
theorem store_spec (hp : Placed code k) (G : Geo m0 bp B) {i : Nat} {sl : List (Nat × Digest × Bool)}
    {ci : Nat} {q : Nat × Digest × Bool} {H : Digest} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b4Offset)) (hfr : Frm m0 st.data) (hfx : Fix m0 st.data)
    (hlt : i < cnt m0) (hi : i < ns.length)
    (hs : sibsM B ns (ns.take (i + 1)) c = some (sl ++ [q], ci))
    (hrd : ReaderAt st.data.dmem (rdr m0) bp B ci)
    (hsb : NodesAt st.data.dmem (sibs m0) ((sl ++ [q]).map fun s ↦ (s.1, s.2.1)))
    (hnx : NodesAt st.data.dmem (nxt m0) (parentsOf (ns.take i) sl)) (hl : sl.length = i)
    (hH : WordsAt st.data.dmem (base m0 224 + BitVec.ofNat 64 96) H.toList)
    (hpar : parentOf ns[i] q = [(ns[i].1 >>> 1, H)])
    (h19 : (st.data.regs.getXReg .X19).toNat = (parentsOf (ns.take i) sl).length)
    (h20 : (st.data.regs.getXReg .X20).toNat = i + 1)
    (h21 : (st.data.regs.getXReg .X21).toNat = ns[i].1)
    (h23 : (st.data.regs.getXReg .X23).toBitVec = nd m0 (i + 1)) :
    Eventually (step1 Host.exe) (Head m0 bp B c ns k (i + 1) (sl ++ [q]) ci) st := by
  have hn := G.n256
  obtain ⟨p, hpd⟩ : ∃ p, p = (parentsOf (ns.take i) sl).length := ⟨_, rfl⟩
  have hp256 : p < 256 := by rw [hpd]; exact parents_lt (by omega)
  rw [← hpd] at h19
  have hnx' : NodesAt st.data.dmem (nxt m0) (parentsOf (ns.take i) sl) := hnx
  have hxnw := G.nxNw
  have hsp := G.sp
  have hxs := G.xS
  have hwf : (Env.ofMachine st.data [(base m0 224, 224), (pa m0 p, 40)]).WF :=
    G.env2_wf hfr (fun t ht ↦ by
        rw [NativeRustcVm.addr_add_add]; exact G.nxMap _ (by unfold nodesBytes; omega))
      (by rw [toNat_off (by omega)]; omega)
      (by rw [toNat_off (by omega)]; unfold climbLevelStack at hxs hsp; omega)
  have hm : Match (Env.ofMachine st.data [(base m0 224, 224), (pa m0 p, 40)]) storeS st.data := by
    refine match_ofMachine ⟨rfl, fun _ ↦ G.aligned, rfl, nofun, trivial⟩
      (by rw [hfr.sp]; simp [Sym.eval]) trivial trivial trivial ⟨?_, trivial⟩
    show Sym.eval _ parAddr = pa m0 p + BitVec.ofInt 64 0
    simp only [parAddr, Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [load_nxt hfr, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_off (by omega)]
    have e64 : (2 : Nat) ^ MemWidth.W64.bits = 2 ^ 64 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, UInt64.toNat_toBitVec, h19,
      e64, show (40 : Nat) % 2 ^ 64 = 40 from rfl]
    have hx4 : m0.regs.X4.toNat + 10240 ≤ 2 ^ 64 := hxnw
    omega
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : Frm m0 st1.data := G.frm_block hfr hm hm1 hwf rfl rfl rfl (r1 := 1) (by decide) rfl
    (fun t ht ↦ G.pa_outs hp256 ht) (by decide)
  have hw : ∀ a, Written (Env.ofMachine st.data [(base m0 224, 224), (pa m0 p, 40)])
      (after b4 storeS) a → Keep m0 256 p a ∧ ¬InRange (rdr m0 + BitVec.ofNat 64 16) 8 a := by
    rw [after_eq run_b4]
    exact G.written_keep hwf rfl (r1 := 1) rfl
      (fun t ht ↦ ⟨G.pa_keep hp256 ht 256, G.pa_cur hp256 ht⟩) (by decide)
  rw [← after_eq run_b4] at hm1
  have hs1 := hm1.sameOutside hwf
  have hk1 : SameOutside st.data.dmem st1.data.dmem (Keep m0 256 p) :=
    NativeRustcVm.SameOutside.mono hs1 fun a ha ↦ (hw a ha).1
  -- the parent's words
  have hHw := wordsAt_digest_iff.mp hH
  simp only [NativeRustcVm.addr_add_add] at hHw
  have hkey : ns[i].1 < 2 ^ 64 := by rw [← h21]; exact UInt64.toNat_lt _
  have hsh : ns[i].1 >>> 1 < 2 ^ 64 := by
    have := Nat.shiftRight_le ns[i].1 1; omega
  have hnode : NodeAt st1.data.dmem (pa m0 p) (ns[i].1 >>> 1, H) := by
    rw [after_eq run_b4] at hm1
    refine node_write hm1 (r := 1) (v0 := .un (.ubfm 1 63) .W64 (.reg .X21))
      (v1 := .load 0 96 8) (v2 := .load 0 104 8) (v3 := .load 0 112 8) (v4 := .load 0 120 8)
      rfl (by decide) (by decide) (by decide) (by decide) (by decide)
      hsh ?_ (by simp only [Sym.eval]; rw [load_of rfl hHw.1])
      (by simp only [Sym.eval]; rw [load_of rfl hHw.2.1])
      (by simp only [Sym.eval]; rw [load_of rfl hHw.2.2.1])
      (by simp only [Sym.eval]; rw [load_of rfl hHw.2.2.2])
    apply UInt64.toNat_inj.mp
    simp only [Sym.eval, UInt64.toNat_ofBitVec, Env.ofMachine_regs]
    rw [lsr1, UInt64.toNat_toBitVec, h21, toNat_toUInt64_of_lt hsh, Nat.shiftRight_eq_div_pow,
      Nat.pow_one]
  rw [after_eq run_b4] at hm1
  have hr : ∀ r ∈ [XReg.X20, .X22, .X23, .X25, .X27, .X28, .X29],
      st1.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm hm1 rfl rfl
  have htl : (ns.take i).length = sl.length := by rw [List.length_take, hl]; omega
  simp only [PcOk] at hpc1
  refine .done _ ⟨hpc1.trans (congrArg Host.addrOf rfl), hfr1,
    hfx.keep fun r h ↦ hr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with rfl | rfl | rfl | rfl | rfl <;> simp), ⟨hs, ?_, ?_, ?_⟩, hlt, ?_,
    by rw [hr .X20 (by simp)]; exact h20, by rw [hr .X23 (by simp)]; exact h23⟩
  · exact G.keep_reader (ls := 256) (lp := p) (by omega) (by omega) hs1 hw hrd
  · exact G.keep_sibs (by omega) (by omega) hk1 (by simp [hl]; omega) hsb
  · rw [take_succ_eq hi, parentsOf_snoc htl, hpar]
    refine NodesAt.append_one (G.keep_nxt (by omega) (by omega) hk1 (by rw [hpd]) hnx) ?_
    rw [← hpd]
    exact hnode
  · rw [take_succ_eq hi, parentsOf_snoc htl, hpar, List.length_append, List.length_singleton,
      ← hpd]
    show (st1.data.regs.getXReg .X19).toBitVec.toNat = p + 1
    rw [hm1.regs .X19 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [toNat_add_one (by rw [UInt64.toNat_toBitVec, h19]; exact hp256), UInt64.toNat_toBitVec,
      h19]

end

end NativeRustcVmArm.Wire.ClimbLevel
