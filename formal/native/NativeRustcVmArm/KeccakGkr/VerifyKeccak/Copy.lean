module

public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Front

/-!
# `verify_keccak`'s copies within its frame

`cpStep`: a block writing the frame's ranges `L`, then `memcpy` from frame offset `src` to `dst`,
`n` bytes: what was at `src` is at `dst` (`copy_sub`), the frame below the slots the only change.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak

public section

/-- **Bytes copied**: a part of the source is at the same offset of the destination. -/
theorem copy_sub {d d' : DataMem} {dst src : BitVec 64} {n o : Nat} {bs : List UInt8}
    (hcp : NativeRustcVm.BytesAt d' dst (NativeRustcArm.bytesOf d src n))
    (h : NativeRustcVm.BytesAt d (src + BitVec.ofNat 64 o) bs) (hle : o + bs.length ≤ n) :
    NativeRustcVm.BytesAt d' (dst + BitVec.ofNat 64 o) bs := by
  intro i hi
  have := hcp (o + i) (by simp [NativeRustcArm.bytesOf]; omega)
  rw [NativeRustcVm.addr_add_add, this]
  simp only [NativeRustcArm.bytesOf, List.getElem_map, List.getElem_range]
  rw [← NativeRustcVm.addr_add_add, h i hi]
  rfl

theorem loc_add (m0 : MachineData) (o i : Nat) : loc m0 o + BitVec.ofNat 64 i = loc m0 (o + i) :=
  NativeRustcVm.addr_add_add _ _ _

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

/-- **A block, then `memcpy` within the frame.** -/
theorem cpStep (hn : Nums a inst m0)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {ds : List Directive} {i : Nat} {S' : SState} {m : MachineData} {L : List (Nat × Nat)}
    {dst src n : Nat} {R : MachineState → Prop}
    (hk : ds.IsInfixAt Host.prog i) (hrun : exec ds midS = some (S', .call NativeRustcVmArm.Vm.Memcpy.entryLabel))
    (hmid : Mid m0 m) (hsp : S'.sp = .ptr 0 0)
    (hw : S'.mem.all (fun w ↦ w.r == 0 &&
      L.any (fun p ↦ decide (p.1 ≤ w.off) && decide (w.off + w.n ≤ p.2))) = true)
    (hL : L.all (fun p ↦ decide (p.2 ≤ 3264) && (decide (p.2 ≤ 88) || decide (96 ≤ p.1)) &&
      (decide (p.2 ≤ src) || decide (src + n ≤ p.1))) = true)
    (hrk : regsL.all (fun r ↦ (midS.reg r).isSome && S'.reg r == midS.reg r) = true)
    (hx0 : ∀ st, Match (envM m0 m) S' st → st.regs.X0.toBitVec = loc m0 dst)
    (hx1 : ∀ st, Match (envM m0 m) S' st → st.regs.X1.toBitVec = loc m0 src)
    (hx2 : S'.reg .X2 = some (.lit n))
    (hdst : dst + n ≤ 3264) (hsrc : src + n ≤ 3264) (h88 : dst + n ≤ 88 ∨ 96 ≤ dst)
    (hap : dst + n ≤ src ∨ src + n ≤ dst)
    (cont : ∀ st m2 : MachineData, Match (envM m0 m) S' st → Mid m0 m2 →
      (∀ o bs, NativeRustcVm.BytesAt m.dmem (loc m0 (src + o)) bs → o + bs.length ≤ n →
        NativeRustcVm.BytesAt m2.dmem (loc m0 (dst + o)) bs) →
      SameOutside st.dmem m2.dmem (fun q ↦ m0.regs.SP.toNat - 3360 + dst ≤ q.toNat ∧
        q.toNat < m0.regs.SP.toNat - 3360 + dst + n) →
      SameOutside m.dmem st.dmem (fun q ↦ ∃ p ∈ L,
        m0.regs.SP.toNat - 3360 + p.1 ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - 3360 + p.2) →
      SameOutside m.dmem m2.dmem (fun q ↦ m0.regs.SP.toNat - 3360 ≤ q.toNat ∧
        q.toNat < m0.regs.SP.toNat - 3360 + 3264) →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hwf := envM_wf hn hmid.fr
  have hN := hn.hN
  have hSP := m0.regs.SP.toNat_lt
  have hL' := hL
  simp only [List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hL'
  refine callStep hn hk hrun hmid.fr (matchM hn hmid.fr) hwf hsp
    (writeOk_ranges (by
      simp only [List.all_eq_true, decide_eq_true_eq]; exact fun p hp ↦ (hL' p hp).1.1) hw)
    (N' := 0) (lo := dst) (n := n) (by decide) hdst hmemcpy
    (fun st hm1 hfr1 ↦ ?_) (fun st m' hm1 hfr1 hq ↦ ?_) fun st m2 hm1 hfr1 hq hfr2 hcs ↦ ?_
  all_goals
    have e0 := hx0 st hm1
    have e1 := hx1 st hm1
    have e2 : st.regs.X2.toNat = n := by
      rw [← UInt64.toNat_toBitVec, show st.regs.X2 = st.regs.getXReg .X2 from rfl,
        hm1.regs .X2 _ hx2]
      simp only [Sym.eval, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [e2] <;> (try rw [e0]) <;> (try rw [e1])
    · exact frame_mapped' hn hfr1 (by omega)
    · exact frame_mapped' hn hfr1 (by omega)
    · exact loc_noWrap hn (by omega)
    · exact loc_noWrap hn (by omega)
    · unfold Apart; rw [loc_toNat hn.hN (by omega), loc_toNat hn.hN (by omega)]; omega
  · obtain ⟨-, -, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ .inr (.inl ?_), hsv⟩
    rw [e0, e2] at hq; exact hq
  · obtain ⟨-, hcp, hs, hsv⟩ := hq
    rw [e0, e1, e2] at hcp
    rw [e0, e2] at hs
    have hb := written_in hn hm1 hwf hw
    have hs' : SameOutside st.dmem m2.dmem (fun q ↦ m0.regs.SP.toNat - 3360 + dst ≤ q.toNat ∧
        q.toNat < m0.regs.SP.toNat - 3360 + dst + n) :=
      NativeRustcVm.SameOutside.mono hs fun q hq ↦ loc_nat hn (by omega) hq
    have hsrc_st : ∀ o bs, NativeRustcVm.BytesAt m.dmem (loc m0 (src + o)) bs →
        o + bs.length ≤ n → NativeRustcVm.BytesAt st.dmem (loc m0 (src + o)) bs := by
      intro o bs h hle
      refine NativeRustcVm.Layout.BytesAt.of_same h (same_num hb (by
        rw [loc_toNat hn.hN (by omega)]; omega) fun q ⟨p, hp, hq⟩ ↦ ?_) le_rfl
      rw [loc_toNat hn.hN (by omega)]
      have := hL' p hp
      omega
    have hmid1 : Mid m0 st :=
      ⟨hfr1, hmid.regs.block (matchM hn hmid.fr) hm1 hrk, word_keep hmid.pk hb
        (by rw [loc_toNat hn.hN (by omega)]; omega)
        (by rw [loc_toNat hn.hN (by omega)]; intro q ⟨p, hp, hq⟩; have := hL' p hp; omega)⟩
    refine cont st m2 hm1 (Mid.call hn hmid1 hfr2 hcs hs' fun q hq ↦ by omega) ?_ hs' hb ?_ hcs
    · intro o bs h hle
      rw [← loc_add]
      exact copy_sub hcp (by rw [loc_add]; exact hsrc_st o bs h hle) hle
    · intro q hq
      rw [hs' q fun h ↦ hq ⟨by omega, by omega⟩, hb q fun ⟨p, hp, h⟩ ↦ hq ?_]
      have := hL' p hp
      exact ⟨by omega, by omega⟩

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
