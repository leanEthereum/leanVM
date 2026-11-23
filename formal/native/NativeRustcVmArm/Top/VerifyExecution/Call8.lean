module

public import NativeRustcVmArm.Code.Vm.KeccakPhase.Names
public import NativeRustcVmArm.Code.Vm.RingSwitch.Names
public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmArm.Top.VerifyExecution.Call9
public import NativeRustcVmArm.Top.VerifyExecution.Areas

/-!
# `verify_execution`: `KECCAK`'s validity

`b14` reads `KECCAK`'s log-height from the layout and calls `keccak_phase` on the tables'
evaluations, the scratch, the column claims and the Keccak output; on `None` `b15` fails, else ring
switching (`call8`).
-/

namespace NativeRustcVmArm.Top.VerifyExecution

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyExecution
open NativeRustcVm.Transcript NativeVm.Model
open NativeVm.Math (keccakPhase_roots)
open NativeRustcVm.Top (workAreaBytes walkKeccak walkRing run_bind_eq)
open NativeRustcVm.Layout (LayoutWAt ClaimsWAt OodAt claimCap)
open NativeRustcVm.Tables (TableEvalsAt)
open LeanVM.Protocol.Verifier (opKeccak keccakOut)

public section

/-- `KECCAK`'s log-height in the layout's word at byte `64`. -/
theorem heightWord {d : DataMem} {x : BitVec 64} {L : LayoutW} (hL : LayoutWAt d x L) :
    NativeRustcVm.WordAt d (x + BitVec.ofNat 64 64) (L.tableLogHeights.getD 5 0).toUInt64 := by
  have h6 := hL.heights_size
  have hw := NativeRustcVm.WordsAt.getElem hL.heights (i := 5) (by simp [h6, nTables])
  rw [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add] at hw
  simp only [List.getElem_map, Array.getElem_toList] at hw
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [h6]; decide),
    Option.getD_some]
  exact hw

variable [Host] {k : Nat}

/-- **`KECCAK`'s validity**, from `b14`: the function returns the walk's rest. -/
theorem call8 (hp : Placed code k)
    (hkp : ∀ a s cs layout evals, Spec (Labels.label NativeRustcVmArm.Vm.KeccakPhase.entryLabel)
      (KeccakPhasePre a s cs layout evals) (KeccakPhasePost a s cs layout evals))
    (hrs : ∀ a s point, Spec (Labels.label NativeRustcVmArm.Vm.RingSwitch.entryLabel) (RingSwitchPre a s)
      (RingSwitchPost a s point))
    (hvso : ∀ a s layout target coefficients point slices cs z value,
      Spec (Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.entryLabel)
        (VerifyStackedOpeningPre a s layout target coefficients point slices cs z value)
        (VerifyStackedOpeningPost a s layout target coefficients point cs z value))
    {a : DecArea} {m0 : MachineData} (g : Geo a m0) {st : MachineState} (h : At m0 st.data)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyExecution.b14Offset)) {rate : Nat} (h21 : st.data.regs.X21.toNat = rate)
    (h23 : st.data.regs.X23 = 112184) (h25 : st.data.regs.X25 = 123992) {s : TState}
    (hts : TStateAt st.data.dmem m0.regs.X0.toBitVec a s) (hroots : s.roots.size ≤ 2)
    {L : LayoutW} (hL : LayoutWAt st.data.dmem m0.regs.X4.toBitVec L)
    {ev : Array (Array EW × Array EW)}
    (hev : TableEvalsAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 112184) ev)
    (hk1 : (ev.getD opKeccak (#[], #[])).1.size = L.tableLogHeights.getD opKeccak 0)
    (hk2 : keccakOut ≤ (ev.getD opKeccak (#[], #[])).2.size) {cs : Array ColumnClaimW}
    (hcl : ClaimsWAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 123992) cs)
    (hcs : cs.size < claimCap)
    {ood : StackClaimW}
    (hood : OodAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 3912) ood) :
    Eventually (step1 Host.exe) (Done a m0 ((walkKeccak L rate ood cs ev).run s)) st := by
  have hs := g.s
  have hwN := g.wN
  have hN : keccakPhaseStack ≤ 18288 := by decide
  obtain ⟨hwf, hm⟩ := h.env g
  refine exec_at (hb14 hp) run_b14 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hk := call_keeps b14 (by simp)
  rw [after_eq run_b14] at hk
  obtain ⟨h1, hd1⟩ := h.block g hm1 hk.1 hk.2
  have r0 : st1.data.regs.X0.toBitVec = m0.regs.X0.toBitVec := by
    have := hm1.regs .X0 _ rfl
    rw [← h.x20]; exact this
  have r1 : st1.data.regs.X1 = (L.tableLogHeights.getD 5 0).toUInt64 := by
    apply UInt64.toBitVec_inj.mp
    have := hm1.regs .X1 _ rfl
    refine this.trans (load_wordAt (r := 1) ?_)
    exact heightWord hL
  have r2 : st1.data.regs.X2.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 112184 := by
    have := hm1.regs .X2 _ rfl
    rw [eval_addW] at this; refine this.trans ?_; show _ + st.data.regs.X23.toBitVec = _
    rw [h23]; rfl
  have r3 : st1.data.regs.X3.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 289728 := by
    have := hm1.regs .X3 _ rfl
    rw [eval_ptrW] at this; exact this
  have r4 : st1.data.regs.X4.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 123992 := by
    have := hm1.regs .X4 _ rfl
    rw [eval_addW] at this; refine this.trans ?_; show _ + st.data.regs.X25.toBitVec = _
    rw [h25]; rfl
  have r5 : st1.data.regs.X5.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 221280 := by
    have := hm1.regs .X5 _ rfl
    rw [eval_ptrW] at this; exact this
  have k21 : st1.data.regs.X21 = st.data.regs.X21 := UInt64.toBitVec_inj.mp (hm1.regs .X21 _ rfl)
  have k22 : st1.data.regs.X22 = 221280 := UInt64.toBitVec_inj.mp (hm1.regs .X22 _ rfl)
  have k25 : st1.data.regs.X25 = st.data.regs.X25 := UInt64.toBitVec_inj.mp (hm1.regs .X25 _ rfl)
  rw [← hd1] at hts hL hev hcl hood
  have hhl : L.tableLogHeights.getD 5 0 ≤ 30 := by
    have h6 := hL.heights_size
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [h6]; decide),
      Option.getD_some]
    exact hL.heights_le _ (Array.getElem_mem _)
  have hx1 : st1.data.regs.X1.toNat = L.tableLogHeights.getD opKeccak 0 := by
    rw [r1]; show (L.tableLogHeights.getD 5 0).toUInt64.toNat = L.tableLogHeights.getD 5 0
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hR := h1.rodataAt g hN
  have hpre : KeccakPhasePre a s cs L ev st1.data := by
    unfold KeccakPhasePre
    simp only [r0, r2, r3, r4, r5]
    exact ⟨h1.stackOk g hN, hR.rcAt, projectAt_of hR, rhoAt_of hR, hts, hcl, hcs, hev, hx1,
      hk1.trans hx1.symm, hk2, h1.keccakAreas g hts hN⟩
  refine call_then hpc1 (hkp a s cs L ev) hpre fun st2 hpc2 hpost ↦ ?_
  obtain ⟨hx0, hres, hch, hsv⟩ := hpost
  simp only [r0, r3, r4, r5] at hres hch
  have hsb := h1.sb g hN
  have h2 : At m0 st2.data := h1.call g hch hsv fun q hq ↦ by
    obtain ⟨r, hr, hq⟩ := hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact wr_stk h1 g hN hq
    · exact wr_t g hq
    · exact wr_w g (o := 289728) (n := 205824) (by omega) (by omega) hq
    · exact wr_w g (o := 123992) (n := 97288) (by omega) (by omega) hq
    · exact wr_w g (o := 221280) (n := 1608) (by omega) (by omega) hq
  have hsW : ∀ {o n : Nat}, o + n ≤ 112184 →
      NativeRustcVm.Layout.Same st1.data.dmem st2.data.dmem
        (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n := fun hn ↦
    g.sameW hch (by omega) (by omega) fun q hq ↦ by
      obtain ⟨r, hr, hq⟩ := hq
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · have := h1.inStk g hN hq; have := g.wS; omega
      · have := g.inT hq; have := g.tw; omega
      · have := g.inW (o := 289728) (n := 205824) (by omega) (by omega) hq; omega
      · have := g.inW (o := 123992) (n := 97288) (by omega) (by omega) hq; omega
      · have := g.inW (o := 221280) (n := 1608) (by omega) (by omega) hq; omega
  rw [show k + NativeRustcVmArm.Vm.VerifyExecution.b14Offset + b14.length = k + NativeRustcVmArm.Vm.VerifyExecution.b15Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyExecution.b14_next]] at hpc2
  rw [walkKeccak, run_bind_eq]
  generalize hr : (keccakPhase L ev).run s = r at hx0 hres
  have bk := branch_keeps b15 (by simp)
  have ck := call_keeps b15 (by simp)
  rw [after_eq run_b15] at bk ck
  refine branch hp g (hb15 hp) run_b15 bk ck.1 h2 hpc2 (cbz_eval hx0) (fun hb ↦ ?_)
    fun hb st3 h3 hreg3 hd3 hpc3 ↦ ?_
  · cases r with
    | none => rfl
    | some _ => cases hb
  obtain ⟨⟨⟨outs, kp, ks⟩, s'⟩, rfl⟩ := Option.isSome_iff_exists.mp hb
  obtain ⟨hts', hcl', hko⟩ := hres _ _ _ _ rfl
  have hroots' : s'.roots = s.roots := (keccakPhase_roots L ev).keeps _ _ _ hr
  rw [show k + NativeRustcVmArm.Vm.VerifyExecution.b15Offset + b15.length = k + NativeRustcVmArm.Vm.VerifyExecution.b16Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyExecution.b15_next]] at hpc3
  have reg : ∀ x : XReg, calleeSaved x = true →
      st3.data.regs.getXReg x = st1.data.regs.getXReg x := fun x hx ↦
    (hreg3 x).trans (hsv.1 x hx)
  have e21 : st3.data.regs.X21 = st1.data.regs.X21 := reg .X21 rfl
  have e22 : st3.data.regs.X22 = st1.data.regs.X22 := reg .X22 rfl
  have e25 : st3.data.regs.X25 = st1.data.regs.X25 := reg .X25 rfl
  have hL2 := NativeRustcVm.Tables.LayoutWAt.of_same (by rw [NativeRustcVm.addr_add_zero]; exact hL)
    (hsW (o := 0) (n := 3912) (by omega))
  rw [NativeRustcVm.addr_add_zero] at hL2
  exact call9 hp hrs hvso g h3 hpc3 (rate := rate) (by rw [e21, k21, h21]) (by rw [e22, k22])
    (by rw [e25, k25, h25]) (hd3 ▸ hts') (by rw [hroots']; exact hroots) (hd3 ▸ hL2)
    (hd3 ▸ hko) (hd3 ▸ hcl')
    (hd3 ▸ NativeRustcVm.Top.OodAt.of_same hood (hsW (o := 3912) (n := 504) (by omega)))

end

end NativeRustcVmArm.Top.VerifyExecution
