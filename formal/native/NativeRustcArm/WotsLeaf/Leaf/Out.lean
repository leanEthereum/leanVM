module

public import NativeRustcArm.WotsLeaf.Leaf.Hash
public import NativeRustcArm.WotsLeaf.Finish

/-!
# The result written, the return

`b49` (directive 631) writes `out`: the tag `1`, the codeword's 58 bytes from 380, the leaf's 16
from 2128 (`out_bytes`, from `outOK`), its other writes in the frame (`sameOutside_frameOut`);
then the epilogue `b12` returns (`leaf_out`).
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcArm.Sym NativeRustcArm.Xmss.WotsLeaf
open NativeRustcArm.SphincsVerifyProof.InlineTh Leaf Chain LeanVM.Protocol.KeccakHash

public section

section
variable {r : Run} [Labels]

omit [Labels] in
theorem CK.slot0 {x E : List UInt8} {m : MachineData} (h : r.CK x E m) :
    BytesAt m.dmem (r.off 0) (wordBytes r.m0.regs.X0) := h.1.2.1.2.2

/-- **`out`'s 75 bytes** after `b49`: the tag `1`, the codeword, the leaf. -/
theorem out_bytes {env : Env} {S : SState} {m' : MachineData} (hm : Match env S m')
    {out base : BitVec 64} (hreg : env.regions[1]? = some (out, 75)) (hb0 : env.base 0 = base)
    (hbytes : ∀ i < 75, ∃ v t, findWrite 1 i S.mem = some (v, t) ∧
      symByte 64 v t = some (outByte i))
    {x D : List UInt8} (hxl : x.length = 58) (hx : BytesAt env.mem0 (base + BitVec.ofNat 64 380) x)
    (hDl : 16 ≤ D.length) (hD : BytesAt env.mem0 (base + BitVec.ofNat 64 2128) D) :
    bytesOf m'.dmem out 75 = 1 :: (x ++ D.take 16) := by
  have hl : (1 :: (x ++ D.take 16)).length = 75 := by simp [hxl]; omega
  apply List.ext_getElem (by rw [length_bytesOf, hl])
  intro p h1 h2
  rw [length_bytesOf] at h1
  simp only [bytesOf, List.getElem_map, List.getElem_range]
  rw [hm.mem 1 out 75 hreg p h1]
  obtain ⟨v, t, hf, hs⟩ := hbytes p h1
  simp only [memByte, hf, Option.getD_some]
  rw [byteOf_eval_of_symByte 64 v t _ hs]
  have hmem : ∀ o, memAt env 0 o = (env.mem0.get? (base + BitVec.ofNat 64 o)).getD 0 := fun o ↦ by
    rw [memAt, hb0]
  rcases Nat.lt_or_ge p 1 with hp | hp
  · obtain rfl : p = 0 := by omega
    simp [outByte, XB.eval, xorAll]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [List.getElem_cons_succ]
  rcases Nat.lt_or_ge q 58 with hq | hq
  · have hx' := hx q (by omega)
    rw [addr_add_add] at hx'
    simp only [outByte, Nat.add_one_ne_zero, show q + 1 < 59 by omega, Nat.add_sub_cancel,
      ite_false, ite_true, XB.eval, xorAll, hmem, hx', Option.getD_some, UInt8.zero_xor,
      UInt8.xor_zero]
    rw [List.getElem_append_left (by omega)]
  · have hD' := hD (q - 58) (by omega)
    rw [addr_add_add] at hD'
    simp only [outByte, Nat.add_one_ne_zero, show ¬q + 1 < 59 by omega, ite_false, XB.eval,
      xorAll, show 2128 + (q + 1 - 59) = 2128 + (q - 58) by omega, hmem, hD', Option.getD_some,
      UInt8.zero_xor, UInt8.xor_zero]
    rw [List.getElem_append_right (by omega), List.getElem_take]
    congr 1
    omega

/-- The writes of a block in the frame below the saved registers or in `out` change only `out`
and the stack area. -/
theorem sameOutside_frameOut (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m) {S : SState}
    (hm : Match (r.envR m [(r.out, 75)]) S m') (hwf : (r.envR m [(r.out, 75)]).WF)
    (hfo : frameOrOut S = true) :
    SameOutside r.m0.dmem m'.dmem (fun p ↦ InRange r.out 75 p ∨ r.StackArea p) := by
  have hnw := (r.pre_out hpre).2.1
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  intro p hp
  rw [← hF.2.2.2.1 p fun h ↦ hp (.inr h)]
  apply hm.get?_mem0 hwf
  rintro ⟨w, hw, b, sz, hbr, h1, h2⟩
  have hw' := List.all_eq_true.mp hfo w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw'
  rcases hw' with ⟨hr, hn⟩ | ⟨hr, hn⟩
  · rw [hr] at hbr
    simp only [Run.envR, Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hbr
    obtain ⟨rfl, rfl⟩ := hbr
    exact hp (.inr (r.inRange_off hpre (a := 0) (n := 2656) (p := p) (by decide) (by
      rw [Run.off_zero, Sym.inRange_iff (by omega)]
      omega)).1)
  · rw [hr] at hbr
    simp only [Run.envR, Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq, Prod.mk.injEq] at hbr
    obtain ⟨rfl, rfl⟩ := hbr
    apply hp
    left
    unfold NoWrap at hnw
    rw [inRange_iff (by omega)]
    omega

end

variable [NativeRustcArm.Host] {r : Run}

/-- **`b49` and the return**: `out` holds the tag, the codeword `x` and the leaf, the first 16
bytes of the digest `D` at 2128; the function returns with its postcondition. -/
theorem leaf_out (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre) {x E D : List UInt8}
    (hDl : D.length = 32) {m : MachineData} (hK : r.CK x E m)
    (hD : BytesAt m.dmem (r.off 2128) D) (hres : r.result = some (x, D.take 16)) :
    Eventually (step1 NativeRustcArm.Host.exe) r.Done ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b49Offset⟩ := by
  obtain ⟨S, hx49, hbytes, hfo, hin, hn, hsp⟩ := outOK_spec
  have hF := hK.1.1
  have hwf := outEnv_wf hpre hF (fun _ ↦ 0)
  have hm := r.match_frameR hpre hF (vars := fun _ ↦ 0) (rest := [(r.out, 75)])
    (srest := [(75, false)]) (known := []) (labels := []) (bounds := [])
    (aliases := [(.load 0 0 8, 1, 0)]) ⟨rfl, ⟨fun h ↦ absurd h (by decide), trivial⟩⟩ trivial
    trivial trivial ⟨by
      show (r.envR m [(r.out, 75)]).load 0 0 8 = r.out + BitVec.ofInt 64 0
      rw [Env.load_of_bytesAt (length_wordBytes _) (CK.slot0 hK), ofInt_ofBytes_wordBytes]
      simp [Run.out], trivial⟩
  refine blk r hp b49_in_code (List.cons_ne_nil _ _) hx49 hwf hm fun st hm1 hpc ↦ ?_
  refine pc_at (hpc.trans (Run.label_of_block r hp b12_in_code rfl)) ?_
  refine finish r hp hpre st.data ?_ ?_ (fun p h ↦ hm1.kept hwf p (hF.2.2.2.2 p h))
    (sameOutside_frameOut hpre hF hm1 hwf hfo) ?_
  · rw [hm1.sp, hsp]
    show r.base + BitVec.ofInt 64 0 = r.base
    simp
  · refine r.bytesAt_keptR hpre hm1 hwf hin (by rw [length_savedBytes']) hF.2.2.1 ?_
    rw [length_savedBytes']
    exact hn
  · rw [hres, out_bytes hm1 rfl rfl hbytes (CK.length_x hK) (CK.slot380 hK) (by omega) hD]
    refine ⟨1, by decide, ?_⟩
    rw [List.take_of_length_le]
    simp [CK.length_x hK]
    omega

end

end NativeRustcArm.WotsLeafProof
