module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldLoop
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open NativeRustcVm.Transcript (off off_off off_add inRange_iff' bytesAt_congr DecArea Touch)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem frame_elems_keep (h : PreOk a s c m0) {d d' : MachineData} {start n : Nat}
    (hend : start + 16 * n ≤ 2160) {f : Nat → EW} (hb : ElemsAt d.dmem (off (fbA m0) start) f n)
    {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ q, R q → q.toNat < (rspOf m0).toNat - 2208 + start ∨
      (rspOf m0).toNat - 2208 + start + 16 * n ≤ q.toNat) :
    ElemsAt d'.dmem (off (fbA m0) start) f n := by
  intro j hj
  refine bytesAt_congr (hb j hj) fun i hi ↦ hs _ fun hq ↦ ?_
  rw [NativeRustcVm.length_ewBytes] at hi
  have hx := hR _ hq
  rw [off_off, off_add, fb_off h (by omega)] at hx
  omega

theorem low64_buffer (h : PreOk a s c m0) {d d' : MachineData} {start : Nat}
    (hstart : 112 ≤ start) (hend : start + 1024 ≤ 2160) {f : Nat → EW}
    (hb : ElemsAt d.dmem (off (fbA m0) start) f 64)
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem
      (Touch (fbA m0) 2216 (fun j ↦ 0 ≤ j ∧ j < 64))) :
    ElemsAt d'.dmem (off (fbA m0) start) f 64 := by
  refine frame_elems_keep h hend hb hs fun q ⟨j, hj, hj', he⟩ ↦ ?_
  rw [he, fb_off h (by omega)]
  exact .inl (by omega)

theorem low64_rows (h : PreOk a s c m0) {d d' : MachineData} {f : Nat → EW}
    (hr : ElemsAt d.dmem (rwA m0) f 4096)
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem
      (Touch (fbA m0) 2216 (fun j ↦ 0 ≤ j ∧ j < 64))) :
    ElemsAt d'.dmem (rwA m0) f 4096 := by
  have := (nums h).r1; have := (nums h).sw; have := (nums h).w
  intro z hz
  refine bytesAt_congr (hr z hz) fun b hb ↦ hs _ fun ⟨j, hj, hj', he⟩ ↦ ?_
  rw [NativeRustcVm.length_ewBytes] at hb
  have he' := congrArg BitVec.toNat he
  rw [off_add, NativeRustcVm.Transcript.toNat_off (by omega), fb_off h (by omega)] at he'
  omega

theorem row_start (hp : Placed code k) (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (h : PreOk a s c m0) {cx : Cx} (hA : cx.a = a) {rows : Array (Array EW)}
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {t i : Nat} (ht : t < 6) (hi : i < half t)
    {vars : Nat → BitVec 64} (hv : VarsOk cx t vars)
    {ks0 ks1 ks2 ks : List (Reg64 × Sym)} {ws0 ws1 ws2 ws : List (Nat × Sym)}
    (hk0 : wfK ks0 = true) (hk1 : wfK ks1 = true) (hk2 : wfK ks2 = true)
    (hw0 : wfW ws0 = true) (hw1 : wfW ws1 = true) (hw2 : wfW ws2 = true)
    {ba bb bi : List Directive} {ka kb ki : Nat} {Sa Sb Si : SState}
    (hina : ba.IsInfixAt code ka) (hinb : bb.IsInfixAt code kb) (hini : bi.IsInfixAt code ki)
    (hna : ba ≠ []) (hnb : bb ≠ []) (hni : bi ≠ [])
    (hab : ka + ba.length = kb) (hbi : kb + bb.length = ki)
    (hxa : exec ba (pS ks0) = some (Sa, .call NativeRustcVmX64.Vm.Memcpy.entryLabel))
    (hxb : exec bb (pS ks1) = some (Sb, .call NativeRustcVmX64.Vm.Memcpy.entryLabel))
    (hxi : exec bi (pS ks2) = some (Si, .fall))
    {srcA srcB : Sym} {ib : Reg64} {s0 : Nat}
    (hoa : mOk 112 srcA t ws0 Sa ks1 ws1 = true)
    (hob : mOk 1136 srcB t ws1 Sb ks2 ws2 = true)
    (hoi : blkOk 8 t ws2 Si (ks ++ [(ib, .lit s0)]) ws = true)
    (ha : srcA.eval (envK m0 vars) = off (rwA m0) (1024 * (2 * i)))
    (hb : srcB.eval (envK m0 vars) = off (rwA m0) (1024 * (2 * i + 1)))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + ka))
    (hm : Mid cx m0 8 st.data) (hk : KAt m0 vars ks0 st.data) (hw : Words m0 vars ws0 st.data)
    (hr : ElemsAt st.data.dmem (rwA m0) (F cx.sl rows t i 0) 4096) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + ki + bi.length) ∧
      Inner cx m0 rows t i 0 ib s0 vars ks ws st'.data) st := by
  have hi32 : i < 32 := by have := Nat.div_le_self 32 (2 ^ t); unfold half at hi; omega
  refine (copy_run hp hcpy h hA hv hk0 hw0 hina hna hxa hoa ⟨by decide, by decide⟩ (by omega)
    ha hpc hm hk hw hr).bind fun st1 ⟨hpc1, hm1, hr1, hw1', hrows1, hbufA, _⟩ ↦ ?_
  have hpc1' : st1.pc = Host.addrOf (k + kb) := by rw [← hab, ← Nat.add_assoc]; exact hpc1
  refine (copy_run hp hcpy h hA hv hk1 hw1 hinb hnb hxb hob ⟨by decide, by decide⟩ (by omega)
    hb hpc1' hm1 hr1 hw1' hrows1).bind fun st2 ⟨hpc2, hm2, hr2, hw2', hrows2, hbufB, hso2⟩ ↦ ?_
  have hbufA2 := frame_elems_keep h (by decide) hbufA hso2 (fun q hq ↦ by
    rcases hq with ⟨j, hj, hj', he⟩ | hq
    · rw [he, fb_off h (by omega)]
      exact .inl (by omega)
    · have hfb := fb_off h (j := 1136) (by decide)
      have := (nums h).r1; have := (nums h).r2
      rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hfb] at hq
      exact .inr (by omega))
  have hpc2' : st2.pc = Host.addrOf (k + ki) := by rw [← hbi, ← Nat.add_assoc]; exact hpc2
  refine blk_run hp h hA hv hk2 hw2 hini hni hxi hoi (ret := 0) nofun hpc2' hm2 hr2 hw2'
    fun st3 hpc3 _ hm3 hr3 hw3 hso3 ↦ ?_
  have hknown : KAt m0 vars ks st3.data := allOf_of fun p hp' ↦ hr3.get (List.mem_append_left _ hp')
  have hcnt : reg st3.data ib = BitVec.ofNat 64 (s0 + 16 * 0) := by
    have hh := hr3.get (List.mem_append_right ks (List.mem_singleton_self (ib, Sym.lit s0)))
    simpa only [Sym.eval, Nat.mul_zero, Nat.add_zero] using hh
  have hba := low64_buffer h (by decide) (by decide) hbufA2 hso3
  have hbb := low64_buffer h (by decide) (by decide) hbufB hso3
  refine .done _ ⟨hpc3, hm3, hknown, hw3, hcnt, ?_, ?_, low64_rows h hrows2 hso3⟩
  · intro z hz
    have hh := hba z hz
    dsimp only at hh
    have he := F_pair hrsz hrow (by rw [hm.sl_size]; exact ht) hi (b := 0) (by decide) hz
    simp only [Nat.add_zero] at he
    rw [he] at hh
    exact hh
  · intro z hz
    have hh := hbb z hz
    dsimp only at hh
    rw [F_pair hrsz hrow (by rw [hm.sl_size]; exact ht) hi (b := 1) (by decide) hz] at hh
    exact hh

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
