module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldPrep
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open NativeRustcVm.Transcript (off DecArea)

@[expose] public section

structure Row [Labels] (cx : Cx) (m0 : MachineData) (rows : Array (Array EW)) (t i : Nat)
    (vars : Nat → BitVec 64) (ks : List (Reg64 × Sym)) (ws : List (Nat × Sym)) (d : MachineData) : Prop where
  mid : Mid cx m0 8 d
  known : KAt m0 vars ks d
  words : Words m0 vars ws d
  rows : ElemsAt d.dmem (rwA m0) (F cx.sl rows t i 0) 4096

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem row_run (hp : Placed code k) (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (h : PreOk a s c m0) {cx : Cx} (hA : cx.a = a) {rows : Array (Array EW)}
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {t i : Nat} (ht : t < 6) (hi : i < half t)
    {vars : Nat → BitVec 64} (hv : VarsOk cx t vars)
    {ks0 ks1 ks2 ks : List (Reg64 × Sym)} {ws0 ws1 ws2 ws : List (Nat × Sym)}
    (hk0 : wfK ks0 = true) (hk1 : wfK ks1 = true) (hk2 : wfK ks2 = true) (hwk : wfK ks = true)
    (hw0 : wfW ws0 = true) (hw1 : wfW ws1 = true) (hw2 : wfW ws2 = true)
    (hws : ws.all (fun p ↦ decide (16 ≤ p.1) && decide (p.1 + 8 ≤ 64)) = true)
    {ba bb bi bl bs : List Directive} {ka kb ki kl kbStore : Nat} {Sa Sb Si Sl Ss : SState}
    (hina : ba.IsInfixAt code ka) (hinb : bb.IsInfixAt code kb) (hini : bi.IsInfixAt code ki)
    (hinl : bl.IsInfixAt code kl) (hins : bs.IsInfixAt code kbStore)
    (hna : ba ≠ []) (hnb : bb ≠ []) (hni : bi ≠ []) (hnl : bl ≠ []) (hns : bs ≠ [])
    (hab : ka + ba.length = kb) (hbi : kb + bb.length = ki)
    (hil : ki + bi.length = kl) (hls : kl + bl.length = kbStore)
    {label : Label} (hlabel : Labels.label label = Host.addrOf (k + kl))
    (hxa : exec ba (pS ks0) = some (Sa, .call NativeRustcVmX64.Vm.Memcpy.entryLabel))
    (hxb : exec bb (pS ks1) = some (Sb, .call NativeRustcVmX64.Vm.Memcpy.entryLabel))
    (hxi : exec bi (pS ks2) = some (Si, .fall))
    {ib cx0 cx1 lo0 lo1 dr : Reg64} {s0 so dst : Nat}
    (hxl : exec bl (loS ib s0) = some (Sl, .call NativeRustcVmX64.Vm.EWMul.entryLabel))
    (hxs : exec bs (stS dr ib so) = some (Ss,
      .cond (notEnd (.bin .add .W64 (.lit 16) (.reg ib)) (s0 + 1024)) label))
    {srcA srcB : Sym}
    (hoa : mOk 112 srcA t ws0 Sa ks1 ws1 = true)
    (hob : mOk 1136 srcB t ws1 Sb ks2 ws2 = true)
    (hoi : blkOk 8 t ws2 Si (ks ++ [(ib, .lit s0)]) ws = true)
    (hol : lOk cx0 cx1 lo0 lo1 (ib :: ks.map Prod.fst) Sl = true)
    (hos : sOk lo0 lo1 ib (.bin .add .W64 (.lit 16) (.reg ib)) (ks.map Prod.fst) Ss = true)
    (ha : srcA.eval (envK m0 vars) = off (rwA m0) (1024 * (2 * i)))
    (hb : srcB.eval (envK m0 vars) = off (rwA m0) (1024 * (2 * i + 1)))
    (hib : calleeSaved ib = true) (hs0 : s0 + 1024 < 2 ^ 64)
    (haddr : dst + s0 = 1024 * i + so)
    (hc0 : (cx0, V0) ∈ ks) (hc1 : (cx1, V1) ∈ ks)
    (hdr : ∀ d, KAt m0 vars ks d → reg d dr = off (rwA m0) dst)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + ka))
    (hh : Row cx m0 rows t i vars ks0 ws0 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + kbStore + bs.length) ∧
      Row cx m0 rows t (i + 1) vars ks ws st'.data) st := by
  refine (row_start hp hcpy h hA hrsz hrow ht hi hv hk0 hk1 hk2 hw0 hw1 hw2 hina hinb hini
    hna hnb hni hab hbi hxa hxb hxi hoa hob hoi ha hb hpc hh.mid hh.known hh.words hh.rows).bind
    fun st1 ⟨hpc1, hh1⟩ ↦ ?_
  have hpc1' : st1.pc = Host.addrOf (k + kl) := by rw [← hil, ← Nat.add_assoc]; exact hpc1
  refine (inner_loop (I := fun j d ↦ Inner cx m0 rows t i j ib s0 vars ks ws d)
    (fun j hj st' hpc' hh' ↦ inner_step hp h hmul hA hrsz hrow ht hi hj hib hs0 haddr hv hwk hws
      hc0 hc1 hdr hinl hins hnl hns hls hlabel hxl hxs hol hos hpc' hh') (by decide) hpc1' hh1).mono
    fun st2 ⟨hpc2, hh2⟩ ↦ ?_
  refine ⟨hpc2, hh2.mid, hh2.known, hh2.words, ?_⟩
  simpa only [F_row] using hh2.rows

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
