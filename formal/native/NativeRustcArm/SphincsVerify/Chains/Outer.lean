module

public import NativeRustcArm.SphincsVerify.Chains.OuterBase
public import NativeRustcArm.SphincsVerify.Epilogue

/-!
# A chain: its head, its steps, its end

`b105` reads chain `i`'s digit and value (`seg_b105`); a digit above 2 goes straight to `b104`,
otherwise `b106` (`seg_b106`) and the steps to `b133` (`seg_b133`); `b104` stores the chain's end
at `20464 + 16 i` and goes on with chain `i + 1` or, after chain 63, to `b134` (`seg_b104`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

@[expose] public section

/-- Chain `i`'s end on layer `l` for the codeword `x`, as `wots_leaf` computes it. -/
def chainEnd (r : Run) (l : Nat) (x : List UInt8) (i : Nat) : List UInt8 :=
  chain r.seed (r.key l) i (x.getD i 0).toNat (3 - (x.getD i 0).toNat)
    ((r.layerSig l).wots.getD i [])

theorem chainEnds_eq (r : Run) (l : Nat) (x : List UInt8) :
    r.chainEnds l x = (List.range 64).map (chainEnd r l x) := rfl

/-- The 32-bit `i << 24`. -/
theorem ubfm_chain {i : Nat} (hi : i < 64) :
    UnOp.apply (.ubfm 8 7) .W32 (BitVec.ofNat 64 i) = BitVec.ofNat 64 (i * 16777216) := by
  interval_cases i <;> rfl

theorem memExt0 (y : BitVec 64) : UnOp.apply (.memExtend ⟨.UXTX, .E0⟩) .W64 y = y := by
  simp [UnOp.apply, BitVec.apply_mem_extend, BitVec.unsigned]

theorem beq_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  by_cases h : a = b
  · subst h
    simp
  · have : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun he ↦ h (by
      have := congrArg BitVec.toNat he
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
        at this)
    simp [h, this]

theorem ult_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem bytesAt_add_zero {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs) :
    BytesAt d (a + BitVec.ofNat 64 0) bs := by
  simpa using h

/-- The ends so far, appended to. -/
theorem Keep.extend {r : Run} [Labels] {l : Nat} {x E e : List UInt8} {m : MachineData}
    (hK : Keep r l x E m) (h : BytesAt m.dmem (r.off 20464) (E ++ e)) : Keep r l x (E ++ e) m :=
  ⟨hK.1, hK.2.1, hK.2.2.1, hK.2.2.2.1, hK.2.2.2.2.1, hK.2.2.2.2.2.1, hK.2.2.2.2.2.2.1,
    hK.2.2.2.2.2.2.2.1, h⟩

variable [ElfHost] {r : Run}

/-- **`b133`**: back to `b104`. -/
theorem seg_b133 (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre) {l : Nat}
    {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i : Nat} {e : List UInt8}
    (he : e.length = 16) {R : MachineState → Prop} {m : MachineData} (hK : Keep r l x E m)
    (hw416 : r.WordAt m 416 i.toUInt64) (hcell : BytesAt m.dmem (r.off 8224) e)
    (cont : ∀ m', Keep r l x E m' → r.WordAt m' 416 i.toUInt64 →
      BytesAt m'.dmem (r.off 8224) e → Eventually (elfStep1 ElfHost.exe) R ⟨m', r.pc NativeRustcArm.Sphincs.SphincsVerify.b104Offset⟩) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b133Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1 (fun _ ↦ 0)
  have hm := match_frameS hpre hK (k := []) trivial
  refine blk r hp b133_in_code (List.cons_ne_nil _ _) run_b133 hwf hm fun st hm1 hpc ↦ ?_
  exact pc_at (hpc.trans (labelAt r hp b104_in_code rfl))
    (cont _ (Keep.of_block hpre hx hE hK hm1 hwf (by decide +kernel))
      (r.bytesAt_kept hpre hm1 hwf (by rw [NativeRustc.length_wordBytes]; decide) hw416
        (by rw [NativeRustc.length_wordBytes]; decide +kernel))
      (r.bytesAt_kept hpre hm1 hwf (by omega) hcell (by rw [he]; decide +kernel)))

/-- **`b106` and the steps**: the chain's word `i << 24`, then `3 - d` steps from the digit `d`;
then `b104`. -/
theorem seg_b106 (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i d : Nat}
    (hi : i < 64) (hd : d ≤ 2) {v : List UInt8} (hv : v.length = 16) {R : MachineState → Prop}
    {m : MachineData} (hK : Keep r l x E m) (h20 : Run.RegIs m .X20 (BitVec.ofNat 64 d))
    (hw416 : r.WordAt m 416 i.toUInt64) (hcell : BytesAt m.dmem (r.off 8224) v)
    (cont : ∀ m', Keep r l x E m' → r.WordAt m' 416 i.toUInt64 →
      BytesAt m'.dmem (r.off 8224) (chain r.seed (r.key l) i d (3 - d) v) →
      Eventually (elfStep1 ElfHost.exe) R ⟨m', r.pc NativeRustcArm.Sphincs.SphincsVerify.b104Offset⟩) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b106Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1 (fun _ ↦ 0)
  have hm := match_frameS hpre hK (k := []) trivial
  refine blk r hp b106_in_code (List.cons_ne_nil _ _) run_b106 hwf hm fun st hm1 hpc ↦ ?_
  have hd' : st.data.dmem = m.dmem := hm1.dmem_eq hwf rfl
  have hK1 := Keep.of_block hpre hx hE hK hm1 hwf (by decide +kernel)
  have h26 : Run.RegIs st.data .X26 (BitVec.ofNat 64 (i * 16777216)) := by
    unfold Run.RegIs
    rw [hm1.regs .X26 _ rfl]
    show UnOp.apply (.ubfm 8 7) .W32 ((r.env m).load 0 416 8) = _
    have hld : (r.env m).load 0 416 8 = BitVec.ofNat 64 i := by
      have hbytes : BytesAt m.dmem (r.base + BitVec.ofNat 64 416) _ := hw416
      rw [Env.load_of_bytesAt (NativeRustc.length_wordBytes _) hbytes, ofInt_ofBytes_wordBytes]
      rfl
    rw [hld, ubfm_chain hi]
  have hw416' : r.WordAt st.data 416 i.toUInt64 := by unfold Run.WordAt; rw [hd']; exact hw416
  refine pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b107Offset) (hpc.trans rfl) ?_
  have hk : 3 - d = 2 - d + 1 := by omega
  exact steps hp hc hpre hx hE hi (2 - d) d (by omega) hv hK1
    ⟨regIs_reg hm1 rfl h20, h26, hw416'⟩ (by rw [hd']; exact hcell)
    fun m' g1 g2 g3 ↦ seg_b133 hp hpre hx hE (length_chain _ _ _ _ _ hv) g1 g2.2.2 g3
      fun m'' f1 f2 f3 ↦ cont m'' f1 f2 (by rw [hk]; exact f3)

end

end NativeRustcArm.SphincsVerifyProof.Chains
