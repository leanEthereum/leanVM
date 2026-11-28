module

public import NativeRustcVmX64.Bus.VerifyBusBalance.Acc
public import NativeRustcVmX64.Code.Vm.BufEW63Extend.Names

/-!
# `verify_bus_balance`'s tail (x86-64)

From `b53` (`k + NativeRustcVmX64.Vm.VerifyBusBalance.b53Offset`), after the count side: `b53` empties the bus's point and calls
`Buf<EW, 63>::extend` with the GKR point; `b54` checks it; `b55` writes the three totals and jumps
to the epilogue with AL = `1` (`tail_spec`).
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout

public section

/-- Three elements by their words. -/
theorem ews3 {d : Mem 64} {p : BitVec 64} {x y z : EW}
    (h0 : NativeRustcVm.WordAt d (off p 0) x.c0) (h1 : NativeRustcVm.WordAt d (off p 8) x.c1)
    (h2 : NativeRustcVm.WordAt d (off p 16) y.c0) (h3 : NativeRustcVm.WordAt d (off p 24) y.c1)
    (h4 : NativeRustcVm.WordAt d (off p 32) z.c0) (h5 : NativeRustcVm.WordAt d (off p 40) z.c1) :
    NativeRustcVm.EWsAt d p [x, y, z] := by
  rw [off_zero] at h0
  refine ewsAt_cons.mpr ⟨ewAt_iff.mpr ⟨h0, h1⟩, ewsAt_cons.mpr ⟨ewAt_iff.mpr ⟨?_, ?_⟩,
    ewsAt_cons.mpr ⟨ewAt_iff.mpr ⟨?_, ?_⟩, ewsAt_nil _ _⟩⟩⟩
  · exact h2
  · rw [off_off]; exact h3
  · rw [off_off]; exact h4
  · rw [off_off, off_off]; exact h5

end

public section
variable [Labels] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

/-- A state of the body, region 1 the bus at the word at `112`. -/
theorem match_bS {d : MachineData} (fr : St m0 104 d)
    (h112 : NativeRustcVm.WordAt d.dmem (loc m0 112) (UInt64.ofBitVec (reg m0 .r8)))
    {ret : BitVec 64} :
    Match (frameEnv m0 d 5520 [(reg m0 .r8, busBytes)] (fun _ ↦ 0) ret) bS d :=
  match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨fr.frame.rsp_eval, trivial⟩ trivial trivial
    ⟨by
      show (frameEnv m0 d 5520 [(reg m0 .r8, busBytes)] (fun _ ↦ 0) ret).load 0 112 8 =
        reg m0 .r8 + BitVec.ofInt 64 0
      rw [load_ofMachine (r := 0) rfl h112, ofInt_zero64, BitVec.add_zero], trivial⟩

omit [Labels] in
/-- A word a block loaded from the frame's byte `o`. -/
theorem load_loc {d : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {o : Nat}
    {w : UInt64} (hw : NativeRustcVm.WordAt d.dmem (loc m0 o) w) :
    (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret).load 0 o 8 = w.toBitVec :=
  load_ofMachine (r := 0) rfl hw

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- **The tail** (`b53`, `k + NativeRustcVmX64.Vm.VerifyBusBalance.b53Offset`): the count side's total at `632`, the GKR point at `1800`,
the forms at the bus. -/
theorem tail_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW63Extend.entryLabel) (BufEWExtendPre 63) (BufEWExtendPost 63))
    {d : MachineData} {res : BusResultW} {s' : TState} {t0 t1 t2 : EW} (fr : St m0 104 d)
    (hr : (verifyBusBalance L).run s0 = some (res, s')) (htot : res.totals = #[t0, t1, t2])
    (h112 : NativeRustcVm.WordAt d.dmem (loc m0 112) (UInt64.ofBitVec (reg m0 .r8)))
    (h104 : NativeRustcVm.WordAt d.dmem (loc m0 104) (UInt64.ofBitVec (loc m0 1800)))
    (h120 : NativeRustcVm.WordAt d.dmem (loc m0 120) res.point.size.toUInt64)
    (hsz : res.point.size ≤ 63) (hpt : NativeRustcVm.EWsAt d.dmem (loc m0 1800) res.point.toList)
    (x13 : reg d .r13 = t0.c0.toBitVec) (xbp : reg d .rbp = t0.c1.toBitVec)
    (xbx : reg d .rbx = t1.c0.toBitVec) (x15 : reg d .r15 = t1.c1.toBitVec)
    (h632 : NativeRustcVm.WordAt d.dmem (loc m0 632) t2.c0)
    (h640 : NativeRustcVm.WordAt d.dmem (loc m0 640) t2.c1)
    (hF : FormsAt d.dmem (reg m0 .r8) res.forms)
    (hts : TStateAt d.dmem (reg m0 .rdi) a s')
    (hcl : ClaimsWAt d.dmem (reg m0 .r9) res.claims) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b53Offset)⟩ := by
  have hS := pre_stack h
  have hbus := pre_bus h
  have hbnw : (reg m0 .r8).toNat + 107768 ≤ 2 ^ 64 := hbus.2.1
  have hbo : ∀ o, o < 107768 → (off (reg m0 .r8) o).toNat = (reg m0 .r8).toNat + o :=
    fun o ho ↦ toNat_off (by omega)
  have hbIn : ∀ o n, o + n ≤ 107768 → ∀ q, NativeRustcVm.InRange (off (reg m0 .r8) o) n q →
      NativeRustcVm.InRange (reg m0 .r8) busBytes q := fun o n hon q hq ↦
    inRange_of_off hbus.2.1 (by rw [busBytes_eq]; omega) hq
  have hbusO : ∀ q, NativeRustcVm.InRange (reg m0 .r8) busBytes q → outs m0 q :=
    fun q hq ↦ .inr (.inl hq)
  -- `b53`: the bus's point emptied, `extend` called.
  have hwf1 := wfBus h fr.frame.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b53Offset + b53.length)).toBitVec)
  refine exec_then (infix_of b53_in_code (by simp [b53]) hp) exit_b53 hwf1 (fun _ _ ↦ rfl)
    (match_bS fr h112) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hw1, wr1', hrdi, hrsi, hrdx, hr14, hr12, hk1⟩ := ok_b53
  have fr1 : St m0 96 st1.data := St.blk fr hS hwf1 hm1 hmid1
    (fun q hq ↦ wr1 hS hw1 (by omega) (by rw [busBytes_eq]; omega) hbus.2.1 hbusO hq)
  have hin1 := writesIn_of_mid hmid1
  have hs1 : NativeRustcVm.SameOutside d.dmem st1.data.dmem (fun q ↦
      NativeRustcVm.InRange (loc m0 96) 8 q ∨ NativeRustcVm.InRange (off (reg m0 .r8) 106704) 8 q) :=
    fun q hq ↦ hm1.get?_mem0 hwf1 fun hW ↦ hq (by
      obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hW
      rcases hw1 w hw with ⟨hr, hlo, hhi⟩ | ⟨hr, hlo, hhi⟩
      · rw [hr] at hb; cases hb
        left
        have := loc_toNat hS (j := 96) (by omega)
        have hfb := fb_off_toNat hS N_ge (m0 := m0) (j := 0) (by omega)
        rw [off_zero] at hfb
        rw [inRange_toNat (by rw [this]; have := rsp_top hS; omega), this]
        omega
      · rw [hr] at hb; cases hb
        right
        rw [inRange_toNat (by rw [hbo _ (by omega)]; omega), hbo _ (by omega)]
        omega)
  have e112 : (frameEnv m0 d 5520 [(reg m0 .r8, busBytes)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b53Offset + b53.length)).toBitVec).load 0 112 8 = reg m0 .r8 := load_loc h112
  have x1di : reg st1.data .rdi = off (reg m0 .r8) 106704 := by
    rw [show reg st1.data .rdi = _ from hm1.regs .rdi _ hrdi]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, e112]
  have x1si : reg st1.data .rsi = loc m0 1800 := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hrsi, Sym.eval, load_loc h104]
  have x1dx : reg st1.data .rdx = res.point.size.toUInt64.toBitVec := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hrdx, Sym.eval, load_loc h120]
  have x1_14 : reg st1.data .r14 = t2.c0.toBitVec := by
    rw [show reg st1.data .r14 = _ from hm1.regs .r14 _ hr14, Sym.eval, load_loc h632]
  have x1_12 : reg st1.data .r12 = t2.c1.toBitVec := by
    rw [show reg st1.data .r12 = _ from hm1.regs .r12 _ hr12, Sym.eval, load_loc h640]
  have k1 : ∀ r ∈ [Reg64.rbx, .rbp, .r13, .r15], reg st1.data r = reg d r := fun r hr ↦
    hk1.reg hm1 hr
  have hnsz : res.point.size.toUInt64.toBitVec.toNat = res.point.size := by
    rw [UInt64.toNat_toBitVec]
    exact UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have w0' := wordAt_write hm1 (r := 1) (o := 106704) (b := reg m0 .r8) (sz := busBytes) rfl
    (by rw [busBytes_eq]; omega) (v := .lit 0) (wr1'.find (o := 106704) (List.mem_singleton.mpr rfl))
  have w0 : NativeRustcVm.WordAt st1.data.dmem (off (reg m0 .r8) 106704) 0 := w0'
  have hpt1 : NativeRustcVm.EWsAt st1.data.dmem (loc m0 1800) res.point.toList :=
    NativeRustcVm.Tables.EWsAt.of_same hpt (keepB hwf1 hm1 hin1 (j := 1800)
      (n := 16 * res.point.size) (by omega) (miss01 hw1 (by omega))) (by simp)
  simp only [PcOk] at hpc1
  have hle : 5520 - 96 + bufEWExtendStack ≤ NN := by decide
  have hA1016 : NativeRustcVm.Apart (off (reg m0 .r8) 106704) 1016 (stackBelow m0 NN) (NN + 8) :=
    NativeRustcVm.Apart.mono hbus.2.2.2.2.1 (by rw [hbo _ (by omega)]; omega)
      (by rw [hbo _ (by omega), busBytes_eq]; omega) (Nat.le_refl _) (Nat.le_refl _)
  have hN1016 : NativeRustcVm.NoWrap (off (reg m0 .r8) 106704) 1016 := by
    unfold NativeRustcVm.NoWrap; rw [hbo _ (by omega)]; omega
  refine callF h (c := 96) (Nc := bufEWExtendStack) (lo := 0) (len := 0)
    (X := NativeRustcVm.InRange (off (reg m0 .r8) 106704) (8 + 16 * 63)) (by omega) hle (by omega)
    (fun q hq ↦ .inl (hbusO q (hbIn 106704 1016 (by omega) q hq))) hext fr1 hpc1 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ ?_, hq.2.2⟩)
    fun m2 fr2 hq2 hs2 hcs2 ↦ ?_
  · unfold BufEWExtendPre
    rw [x1di, x1si, x1dx, NativeRustcVm.wordOf_of_wordAt w0, hnsz, UInt64.toNat_zero]
    have hb := cal_out h fr1 (by omega) hle hbus
    have hp := cal_localIn h fr1 (by omega) hle (j := 1800) (n := 16 * res.point.size) (by omega)
      (by omega)
    refine ⟨cal_stack h fr1 (by omega) hle, by decide,
      ⟨fun i hi ↦ by rw [off_add]; exact hb.1 _ (by rw [busBytes_eq]; omega),
        by unfold NativeRustcX64.NoWrap; rw [hbo _ (by omega)]; omega⟩, hp.1,
      NativeRustcVm.Apart.mono (bus_loc h (n := busBytes) (le_refl _) (j := 1800)
        (l := 16 * res.point.size) (by omega)) (by rw [hbo _ (by omega)]; omega)
        (by rw [hbo _ (by omega), busBytes_eq]; omega) (Nat.le_refl _) (Nat.le_refl _),
      NativeRustcVm.Apart.mono hb.2.2.2.2.1 (by rw [hbo _ (by omega)]; omega)
        (by rw [hbo _ (by omega), busBytes_eq]; omega) (Nat.le_refl _) (Nat.le_refl _), hp.2⟩
  · rw [x1di] at hq'
    rcases hq' with hq' | hq'
    · exact .inr hq'
    · exact .inl hq'
  · obtain ⟨h2a, h2c, h2s⟩ := hq2
    rw [x1di, x1si, x1dx, NativeRustcVm.wordOf_of_wordAt w0, hnsz, UInt64.toNat_zero] at h2a
    simp only [show 0 + res.point.size ≤ 63 from by omega, ↓reduceIte] at h2a
    obtain ⟨h2al, h2buf⟩ := h2a
    have hbe : NativeRustcVm.bufEWOf st1.data.dmem (off (reg m0 .r8) 106704) = [] := by
      unfold NativeRustcVm.bufEWOf; rw [NativeRustcVm.wordOf_of_wordAt w0]; rfl
    have hsl : (slice st1.data (loc m0 1800) res.point.size.toUInt64.toBitVec).toList =
        res.point.toList := by
      have := NativeRustcVm.ewsOf_of_ewsAt hpt1
      rw [Array.length_toList] at this
      unfold slice
      rw [show res.point.size.toUInt64.toBitVec.toNat = res.point.size from hnsz, this]
    rw [hbe, hsl, List.nil_append] at h2buf
    rw [x1di] at h2c
    have hs2' : NativeRustcVm.SameOutside st1.data.dmem m2.dmem (fun q ↦
        NativeRustcVm.InRange (stackBelow st1.data bufEWExtendStack) bufEWExtendStack q ∨
          NativeRustcVm.InRange (off (reg m0 .r8) 106704) 1016 q) :=
      NativeRustcVm.SameOutside.mono h2c fun q hq ↦ hq.elim .inr .inl
    -- `b54`: `extend`'s result.
    have hal : boolRet m2 = 1 := h2al
    refine test_spec hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b54Offset) (n := b54.length) (infix_of b54_in_code (by simp [b54]) hp) rfl
      exit_b54 ok_b54 fr2 (fun hc ↦ ?_) fun d4 fr4 hd4 hk4 _ ↦ ?_
    · exfalso
      revert hc
      show CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg m2 .rax) (reg m2 .rax))
        (BitVec.ofNat 64 0) = true → False
      rw [testAl_eq]
      unfold boolRet at hal
      simp [hal]
    -- `b55`: the totals.
    have hsub : ∀ r ∈ [Reg64.rbx, .rbp, .r13, .r15, .r14, .r12], r ∈ nsp ∧ calleeSaved r = true := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp [nsp], rfl⟩
    have hcs : ∀ r ∈ [Reg64.rbx, .rbp, .r13, .r15, .r14, .r12], reg d4 r = reg st1.data r :=
      fun r hr ↦ (hk4 r (hsub r hr).1).trans (hcs2 r (hsub r hr).2)
    have hd4' : d4.dmem = m2.dmem := hd4
    have h112' : NativeRustcVm.WordAt d4.dmem (loc m0 112) (UInt64.ofBitVec (reg m0 .r8)) := by
      rw [hd4']
      refine NativeRustcVm.Layout.WordAt.of_same h112 ((keepB hwf1 hm1 hin1 (j := 112) (n := 8)
        (by omega) (miss01 hw1 (by omega))).trans (keepC hS fr1.frame.sp (by omega) hle hs2
        (j := 112) (n := 8) (by omega) (by omega) fun i hi hq ↦ ?_)) le_rfl
      exact not_loc hS hA1016 hN1016 (j := 112 + i) (l := 1) (by omega) hq
        (loc_inR hS (by omega) (by omega) (by omega))
    show Eventually (step1 Host.exe) (Goal a s0 L m0) { data := d4, pc := Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b55Offset) }
    have hwf5 := wfBus h fr4.frame.kept (vars := fun _ ↦ 0) (ret := 0)
    refine exec_then (infix_of b55_in_code (by simp [b55]) hp) exit_b55 hwf5 nofun
      (match_bS fr4 h112') fun st5 hm5 hpc5 ↦ ?_
    obtain ⟨hmid5, hw5, wr5, hrax5, -⟩ := ok_b55
    have fr5 : St m0 104 st5.data := St.blk fr4 hS hwf5 hm5 hmid5
      (fun q hq ↦ wr1 hS hw5 (by omega) (Nat.le_of_eq busBytes_eq.symm) hbus.2.1 hbusO hq)
    have hs5 : NativeRustcVm.SameOutside d4.dmem st5.data.dmem
        (NativeRustcVm.InRange (off (reg m0 .r8) 107720) 48) :=
      fun q hq ↦ hm5.get?_mem0 hwf5 fun hW ↦ hq (by
        obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hW
        rcases hw5 w hw with ⟨hr, hlo, hhi⟩ | ⟨hr, hlo, hhi⟩
        · omega
        · rw [hr] at hb; cases hb
          rw [inRange_toNat (by rw [hbo _ (by omega)]; omega), hbo _ (by omega)]
          omega)
    have v : ∀ {o : Nat} {r : Reg64} {w : UInt64}, o + 8 ≤ 107768 →
        (∀ i < 8, findWrite 1 (o + i) (after b55 bS).mem = some (Sym.reg r, i)) →
        r ∈ [Reg64.rbx, .rbp, .r13, .r15, .r14, .r12] →
        reg st1.data r = w.toBitVec → NativeRustcVm.WordAt st5.data.dmem (off (reg m0 .r8) o) w :=
      fun {o r w} ho hwr hr hw ↦ by
        have := wordAt_write hm5 (r := 1) (o := _) (b := reg m0 .r8) (sz := busBytes) rfl
          (by rw [busBytes_eq]; exact ho) hwr
        rwa [show (Sym.reg r).eval (frameEnv m0 d4 5520 [(reg m0 .r8, busBytes)] (fun _ ↦ 0) 0) =
          w.toBitVec from (hcs r hr).trans hw, UInt64.ofBitVec_toBitVec] at this
    have htot5 : NativeRustcVm.EWsAt st5.data.dmem (off (reg m0 .r8) busTotalsOff)
        res.totals.toList := by
      rw [htot]
      refine ews3 ?_ ?_ ?_ ?_ ?_ ?_ <;> rw [off_off, busTotalsOff_eq]
      · exact v (by omega) (wr5.find (o := 107720) (v := .reg .r13) (List.Mem.head _)) (by simp)
          ((k1 .r13 (by simp)).trans x13)
      · exact v (by omega) (wr5.find (o := 107728) (v := .reg .rbp) (List.Mem.tail _ (List.Mem.head _))) (by simp)
          ((k1 .rbp (by simp)).trans xbp)
      · exact v (by omega) (wr5.find (o := 107736) (v := .reg .rbx) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by simp)
          ((k1 .rbx (by simp)).trans xbx)
      · exact v (by omega) (wr5.find (o := 107744) (v := .reg .r15) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) (by simp)
          ((k1 .r15 (by simp)).trans x15)
      · exact v (by omega) (wr5.find (o := 107752) (v := .reg .r14) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) (by simp) x1_14
      · exact v (by omega) (wr5.find (o := 107760) (v := .reg .r12) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) (by simp) x1_12
    have hall : NativeRustcVm.SameOutside d.dmem st5.data.dmem (fun q ↦
        (NativeRustcVm.InRange (loc m0 96) 8 q ∨
          NativeRustcVm.InRange (stackBelow st1.data bufEWExtendStack) bufEWExtendStack q) ∨
          NativeRustcVm.InRange (off (reg m0 .r8) 106704) 1064 q) := fun q hq ↦ by
      simp only [not_or] at hq
      have h48 : ¬ NativeRustcVm.InRange (off (reg m0 .r8) 107720) 48 q := fun h' ↦ hq.2 (by
        rw [inRange_toNat (by rw [hbo _ (by omega)]; omega), hbo _ (by omega)] at h' ⊢
        omega)
      have h1016 : ¬ NativeRustcVm.InRange (off (reg m0 .r8) 106704) 1016 q := fun h' ↦ hq.2 (by
        rw [inRange_toNat (by rw [hbo _ (by omega)]; omega), hbo _ (by omega)] at h' ⊢
        omega)
      have h8 : ¬ NativeRustcVm.InRange (off (reg m0 .r8) 106704) 8 q := fun h' ↦ hq.2 (by
        rw [inRange_toNat (by rw [hbo _ (by omega)]; omega), hbo _ (by omega)] at h' ⊢
        omega)
      rw [hs5 q h48, hd4', hs2' q (by rintro (h' | h'); exacts [hq.1.2 h', h1016 h'])]
      exact hs1 q (by rintro (h' | h'); exacts [hq.1.1 h', h8 h'])
    have hkeep : Kept d.dmem st5.data.dmem :=
      kept_trans (hm1.kept hwf1) (kept_trans h2s.2 (by rw [← hd4']; exact hm5.kept hwf5))
    have hstk : ∀ q, (NativeRustcVm.InRange (loc m0 96) 8 q ∨
          NativeRustcVm.InRange (stackBelow st1.data bufEWExtendStack) bufEWExtendStack q) →
        NativeRustcVm.InRange (stackBelow m0 NN) NN q := by
      rintro q (hq | hq)
      · exact inRange_frame_stack (rsp_top hS) (rsp_ge hS) N_ge
          (inRange_of_off (NativeRustcVm.NoWrap.mono (frame_noWrap hS N_ge) (by omega)) (by omega) hq)
      · have := callee_iv hS fr1.frame.sp (by omega) hle hq
        have := rsp_ge hS
        rw [inRange_stack hS]
        have := N_ge
        omega
    have hnot : ∀ q, ((NativeRustcVm.InRange (loc m0 96) 8 q ∨
          NativeRustcVm.InRange (stackBelow st1.data bufEWExtendStack) bufEWExtendStack q) ∨
          NativeRustcVm.InRange (off (reg m0 .r8) 106704) 1064 q) →
        NativeRustcVm.InRange (stackBelow m0 NN) NN q ∨
          NativeRustcVm.InRange (reg m0 .r8) busBytes q ∨
          NativeRustcVm.InRange (reg m0 .r9) claimsBytes q := fun q hq ↦
      hq.elim (fun h' ↦ .inl (hstk q h')) fun h' ↦ .inr (.inl (hbIn 106704 1064 (by omega) q h'))
    simp only [PcOk] at hpc5
    refine at_pc (hpc5.trans (l28_eq hp)) (exit_spec hp h fr5 ?_ fun res' s'' he ↦ ?_)
    · rw [hr]
      unfold OkAl boolRet
      rw [show reg st5.data .rax = _ from hm5.regs .rax _ hrax5]
      simp only [Sym.eval]
      rw [merge8_toNat]
      rfl
    · rw [hr] at he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
      refine ⟨ts_keep h hkeep hall hnot hts, BusWAt.of_formsAt ?_ ?_ (by rw [htot]; rfl) htot5,
        NativeRustcVm.Tables.ClaimsWAt.of_same hcl (Same.of_sameOutside hall fun j hj hq ↦ ?_)⟩
      · refine FormsAt.of_same hF (Same.of_sameOutside hall fun j hj hq ↦ ?_)
        have hfj : j < 106704 := hj
        rcases hq with hq | hq
        · exact NativeRustcVm.Apart.not_inRange_add hbus.2.2.2.2.1 hbus.2.1
            (noWrap_stackBelow hS) (by rw [busBytes_eq]; omega) (inRange_mono (hstk _ hq) (by omega))
        · rw [inRange_toNat (by rw [hbo _ (by omega)]; omega), hbo _ (by omega),
            NativeRustcVm.toNat_add_ofNat (by omega)] at hq
          omega
      · rw [busPointOff_eq]
        refine NativeRustcVm.Layout.BufEWAt.of_same (n := 1016) h2buf ?_ (by decide)
        rw [← hd4']
        exact Same.of_sameOutside hs5 fun j hj hq ↦ by
          rw [off_add] at hq
          rw [inRange_toNat (by rw [hbo _ (by omega)]; omega), hbo _ (by omega),
            hbo _ (by omega)] at hq
          omega
      · rcases hq with hq | hq
        · exact NativeRustcVm.Apart.not_inRange_add (pre_cl h).2.2.2.2.1 (pre_cl h).2.1
            (noWrap_stackBelow hS) hj (inRange_mono (hstk _ hq) (by omega))
        · exact NativeRustcVm.Apart.not_inRange_add (pre_busCl h).symm (pre_cl h).2.1 hbus.2.1 hj
            (hbIn 106704 1064 (by omega) _ hq)

end

end NativeRustcVmX64.Bus.VerifyBusBalance
