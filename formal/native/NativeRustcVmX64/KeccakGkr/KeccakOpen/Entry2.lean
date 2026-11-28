module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.Entry1

/-! # `keccak_open`: entering the six-round fold -/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open NativeRustcVm.Transcript (off off_zero off_add toNat_off inRange_iff' bytesAt_congr DecArea)

@[expose] public section

def varsOf (sl : Array EW) (t i : Nat) : Nat → BitVec 64 :=
  fun n ↦ if n = 0 then (sl.getD t 0).c0.toBitVec
    else if n = 1 then (sl.getD t 0).c1.toBitVec
    else if n = 2 then BitVec.ofNat 64 i else BitVec.ofNat 64 (1024 * i)

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

omit [Host] in
theorem varsOf_ok (cx : Cx) {t i : Nat} (ht : t < 6) : VarsOk cx t (varsOf cx.sl t i) := by
  exact ⟨ht, by simp [varsOf], by simp [varsOf]⟩

theorem fold_start (hp : Placed code k) (h : PreOk a s c m0) {s1 : TState}
    {sl : Array EW} {v : EW} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b4Offset)) (hs : Sw a c m0 s1 sl v st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b5Offset) ∧
      Mid ⟨a, s1, sl, v⟩ m0 8 st'.data ∧ KAt m0 (varsOf sl 0 0) kR0 st'.data ∧
      ElemsAt st'.data.dmem (rwA m0) (Fr sl (swOf c m0) 0) 4096) st := by
  have hn := nums h
  have := hn.r1; have := hn.r2; have := hn.s; have := hn.t; have := hn.w; have := hn.a
  have := hn.ss; have := hn.st; have := hn.sw; have := hn.sa
  have hfb := fbA_toNat h
  have hwf := wf_fold h hs.body.fr.kept (vars := varsOf sl 0 0) (ret := 0)
  have hmatch : Match (E m0 st.data (varsOf sl 0 0) 0) (pS [(.r15, P)]) st.data := by
    apply Match.withKnownBytes
    · refine match_ofMachine ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ ⟨hs.body.fr.rsp_eval, ?_, trivial⟩
        trivial trivial ⟨arg_alias 0, arg_alias 1, arg_alias 2, arg_alias 3, arg_alias 4, arg_alias 5,
          ?_, by simp [Sym.eval, RF, Env.base, gotAddr], trivial⟩
      · change reg st.data .r15 = rwA m0 + BitVec.ofInt 64 0
        rw [hs.r15, ofInt0, BitVec.add_zero]
      · show (E m0 st.data (varsOf sl 0 0) 0).load 3 32 8 = slA m0 + BitVec.ofInt 64 0
        rw [show (32 : Nat) = 8 * 4 from rfl, load_arg h hs.body.same (i := 4) (by decide), ofInt0,
          BitVec.add_zero]
        rfl
    · intro i hi
      simp only [Nat.zero_add]
      change st.data.dmem.get? (gotAddr "memcpy" + BitVec.ofNat 64 i) =
        some (byteOf (Labels.label "memcpy").toBitVec i)
      exact got_byte h hs.body.same hi
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) x4 hwf nofun hpc hmatch
    fun st1 hm1 hpc1 ↦ ?_
  have hb1 := body_block h hs.body hm1 f4.2.1 (by
    intro w hw
    rw [f4.2.2.1] at hw
    simp only [List.mem_singleton] at hw
    subst hw
    exact ⟨rfl, by decide⟩)
  have hso := sameOutside_touch hwf hm1 (r := 0) (b := fbA m0) (N := 2216)
    (lo := 64) (hi := 72) rfl (by decide) (by
      intro w hw
      rw [f4.2.2.1] at hw
      simp only [List.mem_singleton] at hw
      subst hw
      exact ⟨rfl, by dsimp only; omega⟩)
  have keepWord : ∀ {j : Nat} {w : UInt64}, 72 ≤ j → j + 8 ≤ 112 →
      NativeRustcVm.WordAt st.data.dmem (off (fbA m0) j) w →
      NativeRustcVm.WordAt st1.data.dmem (off (fbA m0) j) w := by
    intro j w hj hj' hw
    refine bytesAt_congr hw fun i hi ↦ hso _ fun ⟨l, hl, hl', he⟩ ↦ ?_
    rw [NativeRustcVm.length_wordBytes] at hi
    rw [off_add] at he
    have he' := congrArg BitVec.toNat he
    rw [fb_off h (by omega), fb_off h (by omega)] at he'
    omega
  have hout : NativeRustcVm.WordAt st1.data.dmem (off (fbA m0) 64) (UInt64.ofBitVec (oA m0)) := by
    have hh := wordAt_write hm1 (r := 0) (o := 64) (v := .reg .rbx) rfl (by decide)
      (by rw [f4.2.2.1]; decide +kernel)
    change NativeRustcVm.WordAt _ _ (UInt64.ofBitVec (reg st.data .rbx)) at hh
    rw [hs.bx] at hh
    exact hh
  have hstack : ∀ q, NativeRustcVm.Transcript.Touch (fbA m0) 2216
      (fun j ↦ 64 ≤ j ∧ j < 72) q →
      NativeRustcVm.InRange (stackBelow m0 keccakOpenStack) keccakOpenStack q := by
    intro q hq
    obtain ⟨j, hj, hlow, he⟩ := hq
    rw [he]
    exact (context h).inRange_frame (NativeRustcVm.Transcript.inRange_off_self (by omega)
      (by have := (context h).noWrap_frame; unfold NativeRustcVm.NoWrap at this; omega))
  have hslot : NativeRustcVm.EWsAt st1.data.dmem (slA m0) sl.toList := by
    refine bytesAt_congr hs.slot fun i hi ↦ hso _ fun hq ↦ ?_
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hs.sl_size] at hi
    exact (context h).out_not_stack (slot_out h)
      (NativeRustcVm.Transcript.inRange_off_self hi (by omega)) (hstack _ hq)
  have hts := hs.ts.frame (hm1.kept hwf) (fun q hq ↦ (context h).stack_not_t (hstack q hq)) hso
  have hmid : Mid ⟨a, s1, sl, v⟩ m0 8 st1.data :=
    ⟨hb1.fr, hb1.same, keepWord (by decide) (by decide) hs.v0,
      keepWord (by decide) (by decide) hs.v1, hout, hs.sl_size, hslot, hts⟩
  have hkl : ∀ p ∈ klOf 0 [], p.1.eval (E m0 st.data (varsOf sl 0 0) 0) =
      p.2.eval (E m0 st.data (varsOf sl 0 0) 0) := by
    intro p hp'
    simp only [klOf, List.map_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl
    · change (E m0 st.data (varsOf sl 0 0) 0).load 3 40 8 = rwA m0 + BitVec.ofInt 64 0
      rw [show (40 : Nat) = 8 * 5 from rfl, load_arg h hs.body.same (i := 5) (by decide), ofInt0, BitVec.add_zero]
      rfl
    · change (E m0 st.data (varsOf sl 0 0) 0).load 3 32 8 = slA m0 + BitVec.ofInt 64 0
      rw [show (32 : Nat) = 8 * 4 from rfl, load_arg h hs.body.same (i := 4) (by decide), ofInt0, BitVec.add_zero]
      rfl
    · have hh := NativeRustcVm.ewAt_iff.mp (ewsAt_getD hs.slot (i := 0) (by rw [hs.sl_size]; decide))
      exact load_of_wordAt hh.1
    · have hh := NativeRustcVm.ewAt_iff.mp (ewsAt_getD hs.slot (i := 0) (by rw [hs.sl_size]; decide))
      change (E m0 st.data (varsOf sl 0 0) 0).load 1 8 8 = (sl.getD 0 0).c1.toBitVec
      exact load_of_wordAt (by
        change NativeRustcVm.WordAt st.data.dmem (off (slA m0) 8) (sl.getD 0 0).c1
        simpa only [off_add] using hh.2)
  have hk := KAt.after (m0 := m0) (vars := varsOf sl 0 0) hm1 hkl rfl rfl f4.2.2.2
  have hk' : KAt m0 (varsOf sl 0 0) kR0 st1.data := by
    obtain ⟨h12, h13, hbx, h14, _⟩ := hk
    refine ⟨h12, h13, ?_, ?_, trivial⟩
    · exact hbx
    · change reg st1.data .r14 = (rwA m0 + 0#64) + 0#64
      rw [BitVec.add_zero]
      exact h14
  have hrows : NativeRustcVm.EWsAt st1.data.dmem (rwA m0)
      (NativeRustcVm.KeccakGkr.rowsFlat (swOf c m0)) := by
    refine bytesAt_congr hs.rows fun i hi ↦ hso _ fun hq ↦ ?_
    have hrowN := NativeVm.Math.Keccak.slotWeights_size (reg m0 .rdx).toNat c
      (openFirst m0).toNat (openCount m0).toNat
    rw [NativeRustcVm.length_ewsBytes] at hi
    have hlen : (NativeRustcVm.KeccakGkr.rowsFlat (swOf c m0)).length = 4096 := by
      simp only [NativeRustcVm.KeccakGkr.rowsFlat, swOf]
      rw [NativeRustcVm.KeccakGkr.rowsFlat_length _ (fun r hr ↦ hrowN.2 r (by
        rw [hrowN.1] at hr; exact hr)), hrowN.1]
    rw [hlen] at hi
    have hq' := hstack _ hq
    rw [stack_eq, inRange_iff' (by
      have hh := stack_noWrap h.st; rwa [stack_eq] at hh), stackBelow_toNat (by omega)] at hq'
    rw [show rwA m0 + BitVec.ofNat 64 i = off (rwA m0) i from rfl, toNat_off (by omega)] at hq'
    omega
  refine .done _ ⟨?_, hmid, hk', ?_⟩
  · simp only [PcOk] at hpc1
    exact hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b4_next)
  · intro i hi
    have hrowN := NativeVm.Math.Keccak.slotWeights_size (reg m0 .rdx).toNat c
      (openFirst m0).toNat (openCount m0).toNat
    have hlen : (NativeRustcVm.KeccakGkr.rowsFlat (swOf c m0)).length = 4096 := by
      simp only [NativeRustcVm.KeccakGkr.rowsFlat, swOf]
      rw [NativeRustcVm.KeccakGkr.rowsFlat_length _ (fun r hr ↦ hrowN.2 r (by
        rw [hrowN.1] at hr; exact hr)), hrowN.1]
    have hi' : i < (NativeRustcVm.KeccakGkr.rowsFlat (swOf c m0)).length := by
      rw [hlen]; exact hi
    simpa only [Fr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
      using NativeRustcVm.EWsAt.getElem hrows hi'

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
