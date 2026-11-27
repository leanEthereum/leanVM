module

public import NativeRustcX64.Code.Common.Memcpy.Names

public import NativeRustcX64.Hasher.UpdateInv

/-!
# `Hasher::update`'s loop: copying into the buffer (x86-64)

From the loop head (`Inv`), `b3`–`b5` take `t = min (136 - buf_len) remaining` bytes (the slice
bounds checks, branches to `slice_index_fail`, fail since `buf_len < 136`) and call
`memcpy(buf + buf_len, data, t)`; on its return the hasher is the one before with those bytes
written after the buffered ones (`Copied`, `copy_spec`).
-/

namespace NativeRustcX64.Hasher.Update

open NativeRustc NativeRustc.Keccak NativeRustcX64.Sym NativeRustcX64.Common.Update
open NativeRustcX64.KeccakF NativeRustcX64.Hasher

@[expose] public section

/-- After `memcpy`: the hasher `Hc` of the loop head with `t` input bytes copied into its buffer;
RBX, R15 as at the loop head and R12 `t`. -/
structure Copied [Labels] (m0 : MachineData) (c : Nat) (Hc : List UInt8) (m : MachineData) : Prop where
  frame : Frame m0 m
  le : c ≤ nOf m0
  rbx : reg m .rbx = BitVec.ofNat 64 (nOf m0 - c)
  r15 : reg m .r15 = dAt m0 + BitVec.ofNat 64 c
  r12 : reg m .r12 = BitVec.ofNat 64 (min (136 - bufLen Hc) (nOf m0 - c))
  holds : Holds m0 Hc c
  lt : bufLen Hc < 136
  len : Hc.length = 344
  bytes : hasher m0 m = writeAt Hc (200 + bufLen Hc)
    (((input m0).drop c).take (min (136 - bufLen Hc) (nOf m0 - c)))

end

public section

/-- The count `cmovb` picks: the remaining bytes, or the room in the buffer if less. -/
theorem toNat_take {x0 x19 : BitVec 64} (h : x0.toNat < 136) :
    (if x19.ult (BitVec.ofNat 64 136 - x0) = true then x19 else BitVec.ofNat 64 136 - x0).toNat =
      min (136 - x0.toNat) x19.toNat := by
  have h1 : (BitVec.ofNat 64 136 - x0).toNat = 136 - x0.toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  by_cases hc : x19.toNat < 136 - x0.toNat
  · rw [ite_pos' (by simp [BitVec.ult, h1, hc])]
    omega
  · rw [ite_neg' (by simp [BitVec.ult, h1, hc]), h1]
    omega

theorem inRange_zero {a p : BitVec 64} : ¬InRange a 0 p := Nat.not_lt_zero _

variable [ElfHost] {sec k : Nat}

set_option linter.unusedSimpArgs false in
/-- **Copying into the buffer.** -/
theorem copy_spec (hp : PlacedIn code sec k)
    (hmemcpy : ElfSpec (Labels.label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {m0 m : MachineData} (hpre : UpdatePreElf m0) {c : Nat} (hinv : Inv m0 c m) :
    Eventually (elfStep1 ElfHost.exe)
      (fun st => st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b6Offset) ∧ Copied m0 c (hasher m0 m) st.data)
      ⟨m, ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b3Offset)⟩ := by
  have g := geo_of hpre
  obtain ⟨a0, ha0⟩ := hpre.2.2.1
  have hHc := hinv.holds a0 ha0
  have hlen : (hasher m0 m).length = 344 := length_bytesOf ..
  have hL : bufLen (hasher m0 m) < 136 := by
    rw [bufLen_of_holds hHc]
    exact Nat.mod_lt _ (by omega)
  have hn : nOf m0 < 2 ^ 64 := BitVec.isLt _
  have hle := hinv.le
  generalize hLdef : bufLen (hasher m0 m) = L at hL
  have hx0 : (reg m .rdi).toNat = L := hLdef ▸ hinv.rdi
  have hmap : Mapped m.dmem (hAt m0) 344 := fun i hi => hinv.frame.kept _ (hpre.2.2.2.1 i hi)
  let env := Env.ofMachine m [(hAt m0, 344), (frm m0, 120), (gotAddr "memcpy", 8)] (fun _ => 0)
    (ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b6Offset)).toBitVec
  have hwf : env.WF := wf_head hpre hinv.frame
  have hm : Match env headS m := match_headS hpre hinv.frame
  have henv : ∀ r, env.regs r = reg m r := fun _ => rfl
  have h64 : Width.W64.bits = 64 := rfl
  -- The take `cmovb` computes.
  have hx19n : (reg m .rbx).toNat = nOf m0 - c := by
    rw [hinv.rbx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨TV, hTV, htv⟩ : ∃ TV, (if (reg m .rbx).ult (BitVec.ofNat 64 136 - reg m .rdi) = true
      then reg m .rbx else BitVec.ofNat 64 136 - reg m .rdi) = TV ∧
      TV.toNat = min (136 - L) (nOf m0 - c) :=
    ⟨_, rfl, by rw [toNat_take (by rw [hx0]; exact hL), hx0, hx19n]⟩
  -- `b3`: the take, and `jb` to the panic not taken.
  refine exec_then_elf (hb3 hp) run_b3 hwf nofun hm fun st3 hm3 hpc3 => ?_
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
    henv, hTV] at hpc3
  rw [ite_neg' (by
    simp only [BitVec.ult, BitVec.toNat_add, htv, hx0, decide_eq_true_eq, h64]
    omega)] at hpc3
  -- `b4`: `jae` to the panic not taken.
  refine exec_at_elf (hb4 hp) (exec_after run_b3 run_b4) hwf nofun hpc3 hm3 fun st4 hm4 hpc4 => ?_
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
    henv, hTV] at hpc4
  rw [ite_neg' (by
    simp only [BitVec.ult, BitVec.toNat_add, htv, hx0, BitVec.toNat_ofNat, Bool.not_eq_true',
      decide_eq_false_iff_not, Nat.not_lt, h64]
    omega)] at hpc4
  -- `b5`: `memcpy`'s arguments.
  have hr5 := run_b5
  rw [after_eq run_b3, after_eq (exec_after run_b3 run_b4)] at hr5
  have hl5 := b5_mem
  rw [after_eq run_b3, after_eq (exec_after run_b3 run_b4), after_eq hr5] at hl5
  refine exec_at_elf (hb5 hp) hr5 hwf (fun _ _ => rfl) hpc4 hm4 fun st5 hm5 hpc5 => ?_
  have hfrN := frm_toNat g
  have hmem5 : ∀ p, ¬((frm m0).toNat ≤ p.toNat ∧ p.toNat < (frm m0).toNat + 8) →
      st5.data.dmem.get? p = m.dmem.get? p := fun p hp =>
    hm5.get?_mem0 hwf fun hw => hp (written_lim (r := 1) rfl hl5 hw)
  have hrdiv : reg m .rdi = BitVec.ofNat 64 L := by
    apply BitVec.eq_of_toNat_eq
    rw [hx0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hRDI : reg st5.data .rdi = hAt m0 + BitVec.ofNat 64 (200 + L) := by
    rw [show reg st5.data .rdi = _ from hm5.regs .rdi _ rfl]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, henv, hrdiv]
    rw [show env.base 0 = hAt m0 from rfl, show BitVec.ofInt 64 200 = BitVec.ofNat 64 200 from rfl,
      BitVec.add_assoc, BitVec.ofNat_add]
  have hRSI : reg st5.data .rsi = dAt m0 + BitVec.ofNat 64 c := by
    rw [show reg st5.data .rsi = _ from hm5.regs .rsi _ rfl]
    exact hinv.r15
  have hRDX : (reg st5.data .rdx).toNat = min (136 - L) (nOf m0 - c) := by
    rw [show reg st5.data .rdx = _ from hm5.regs .rdx _ rfl]
    simp only [Sym.eval, SBool.eval, BinOp.apply, CmpOp.apply, low_W64, ext_W64, henv, hTV, htv]
  have hRSP : rspOf st5.data = frm m0 := by
    show reg st5.data .rsp = _
    rw [show reg st5.data .rsp = _ from hm5.regs .rsp _ rfl]
    show frm m0 + BitVec.ofInt 64 0 = _
    exact BitVec.add_zero _
  generalize htdef : min (136 - L) (nOf m0 - c) = t at hRDX
  have ht : t ≤ 136 - L ∧ t ≤ nOf m0 - c := by omega
  have hsrc_ok : ∀ i < t, st5.data.dmem.get? (dAt m0 + BitVec.ofNat 64 c + BitVec.ofNat 64 i) =
      m.dmem.get? (dAt m0 + BitVec.ofNat 64 (c + i)) := fun i hi => by
    rw [add_ofNat_add]
    refine hmem5 _ fun h => ?_
    rw [toNat_add_ofNat' (by have := g.d; omega), hfrN] at h
    have := g.ds
    have := g.s
    omega
  have hdst_ok : ∀ i < t, st5.data.dmem.get? (hAt m0 + BitVec.ofNat 64 (200 + L) +
      BitVec.ofNat 64 i) = m.dmem.get? (hAt m0 + BitVec.ofNat 64 (200 + L + i)) := fun i hi => by
    rw [add_ofNat_add]
    refine hmem5 _ fun h => ?_
    rw [toNat_add_ofNat' (by have := g.h; omega), hfrN] at h
    have := g.hs
    have := g.s
    omega
  refine call_then_elf hpc5 hmemcpy ?pre fun st' hpc' hrsp' hpost => ?_
  case pre =>
    refine ⟨⟨Nat.zero_le _, ?_, fun i hi => ?_⟩, fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_, ?_⟩
    · rw [hRSP, hfrN]
      have := g.s8
      have := g.s
      omega
    · rw [hRSP, show frm m0 - BitVec.ofNat 64 0 = frm m0 from BitVec.sub_zero _]
      exact hm5.kept hwf _ (hinv.frame.kept _ (frm_mapped hpre i (by omega)))
    · show (st5.data.dmem.get? (reg st5.data .rdi + _)).isSome
      have hi' : i < t := by rw [← hRDX]; exact hi
      rw [hRDI, hdst_ok i hi']
      exact hmap _ (by omega)
    · show (st5.data.dmem.get? (reg st5.data .rsi + _)).isSome
      have hi' : i < t := by rw [← hRDX]; exact hi
      rw [hRSI, hsrc_ok i hi']
      exact hinv.frame.kept _ (hpre.2.2.2.2.2.1 _ (by unfold nOf at hle ht; omega))
    · show (reg st5.data .rdi).toNat + (reg st5.data .rdx).toNat ≤ _
      rw [hRDI, hRDX, toNat_add_ofNat' (by have := g.h; omega)]
      have := g.h
      omega
    · show (reg st5.data .rsi).toNat + (reg st5.data .rdx).toNat ≤ _
      rw [hRSI, hRDX]
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0]
        exact Nat.le_of_lt (BitVec.isLt _)
      · rw [toNat_add_ofNat' (by have := g.d; omega)]
        have := g.d
        omega
    · show (reg st5.data .rdi).toNat + (reg st5.data .rdx).toNat ≤ (reg st5.data .rsi).toNat ∨
        (reg st5.data .rsi).toNat + (reg st5.data .rdx).toNat ≤ (reg st5.data .rdi).toNat
      rw [hRDI, hRSI, hRDX]
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0, Nat.add_zero, Nat.add_zero]
        exact Nat.le_total _ _
      · rw [toNat_add_ofNat' (by have := g.h; omega), toNat_add_ofNat' (by have := g.d; omega)]
        have := g.hd
        omega
    · show (reg st5.data .rdi).toNat + (reg st5.data .rdx).toNat ≤ (rspOf st5.data).toNat ∨
        (rspOf st5.data).toNat + 8 ≤ (reg st5.data .rdi).toNat
      rw [hRDI, hRDX, hRSP, hfrN, toNat_add_ofNat' (by have := g.h; omega)]
      have := g.hs
      have := g.s
      omega
  obtain ⟨-, hbytes, hsame, hsaved⟩ := hpost
  have h0' : reg st5.data .rdi = _ := hRDI
  have h1' : reg st5.data .rsi = _ := hRSI
  have h2' : (reg st5.data .rdx).toNat = _ := hRDX
  simp only [reg] at h0' h1' h2'
  simp only [h0', h1', h2'] at hbytes hsame
  have hreg : ∀ r, calleeSaved r = true → st'.data.regs.get64 r = st5.data.regs.get64 r :=
    hsaved.1
  have hfr : Frame m0 st'.data := by
    refine hinv.frame.update g ((hreg .r13 rfl).trans (Match.reg_eq hm hm5 rfl rfl))
      ((hreg .r14 rfl).trans (Match.reg_eq hm hm5 rfl rfl))
      (hrsp'.trans (by rw [hRSP, hinv.frame.rsp])) (fun p hp => ?_)
      (fun p hp => hsaved.2 p (hm5.kept hwf p hp))
      ((hreg .rbp rfl).trans (hm5.regs .rbp (.label "memcpy") rfl))
    rw [chgL_iff g] at hp
    rw [hsame p fun hr => hp (Or.inl ?_), hmem5 p (by rw [hfrN]; have := g.s; omega)]
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0
      exact absurd hr inRange_zero
    · rw [inRange_iff (by rw [toNat_add_ofNat' (by have := g.h; omega)]; have := g.h; omega),
        toNat_add_ofNat' (by have := g.h; omega)] at hr
      omega
  refine Eventually.done _ ⟨by rw [hpc']; rfl, hfr, hle, ?_, ?_, ?_, hinv.holds, hLdef ▸ hL,
    hlen, ?_⟩
  · exact (hreg .rbx rfl).trans ((Match.reg_atom hm5 rfl).trans hinv.rbx)
  · exact (hreg .r15 rfl).trans ((Match.reg_eq hm hm5 rfl rfl).trans hinv.r15)
  · refine (hreg .r12 rfl).trans ?_
    rw [hLdef, htdef]
    show reg st5.data .r12 = _
    rw [show reg st5.data .r12 = _ from hm5.regs .r12 _ rfl]
    simp only [Sym.eval, SBool.eval, BinOp.apply, CmpOp.apply, low_W64, ext_W64, henv, hTV]
    apply BitVec.eq_of_toNat_eq
    rw [htv, htdef, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · -- The hasher: the copied bytes in the buffer, the rest as at the loop head.
    rw [hLdef, htdef]
    have hsrc : ((input m0).drop c).take t =
        bytesOf st5.data.dmem (dAt m0 + BitVec.ofNat 64 c) t := by
      rw [input, ← bytesOf_add _ _ (by omega)]
      refine (bytesOf_congr fun i hi => ?_).symm
      rw [hsrc_ok i hi, input_same g hinv.frame (by omega), add_ofNat_add]
    have hsl : (((input m0).drop c).take t).length = t := by
      rw [hsrc, length_bytesOf]
    refine ext_getD (by rw [hasher, length_bytesOf, length_writeAt (by rw [hsl, hlen]; omega),
      hlen]) fun i hi => ?_
    rw [hasher, length_bytesOf] at hi
    rw [hasher, getD_bytesOf _ _ hi, getD_writeAt _ _ _ _ (by rw [hsl, hlen]; omega), hsl]
    by_cases hin : 200 + L ≤ i ∧ i < 200 + L + t
    · rw [ite_pos' hin, show hAt m0 + BitVec.ofNat 64 i =
          hAt m0 + BitVec.ofNat 64 (200 + L) + BitVec.ofNat 64 (i - (200 + L)) by
          rw [add_ofNat_add]; congr 2; omega,
        hbytes (i - (200 + L)) (by rw [length_bytesOf]; omega), hsrc]
      simp only [Option.getD_some, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by rw [length_bytesOf]; omega)]
      rfl
    · rw [ite_neg' hin, hsame _ fun hr => hin ?_, hmem5 _ ?_, ← getD_bytesOf _ _ hi]
      · rfl
      · rw [toNat_add_ofNat' (by have := g.h; omega), hfrN]
        have := g.hs
        have := g.s
        omega
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        exact absurd hr inRange_zero
      · rw [inRange_add_iff (by have := g.h; omega) (by have := g.h; omega) h0] at hr
        exact hr

end

end NativeRustcX64.Hasher.Update
