module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldMemory
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldControl
public import NativeRustcVmX64.Code.Vm.EWMul.Names

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open NativeRustcVm.Transcript (off DecArea)

@[expose] public section

structure Inner [Labels] (cx : Cx) (m0 : MachineData) (rows : Array (Array EW))
    (t i j : Nat) (ib : Reg64) (s0 : Nat) (vars : Nat → BitVec 64)
    (ks : List (Reg64 × Sym)) (ws : List (Nat × Sym)) (d : MachineData) : Prop where
  mid : Mid cx m0 8 d
  known : KAt m0 vars ks d
  words : Words m0 vars ws d
  counter : reg d ib = BitVec.ofNat 64 (s0 + 16 * j)
  bufA : ElemsAt d.dmem (off (fbA m0) 112) (W cx.sl rows t (2 * i)) 64
  bufB : ElemsAt d.dmem (off (fbA m0) 1136) (W cx.sl rows t (2 * i + 1)) 64
  rows : ElemsAt d.dmem (rwA m0) (F cx.sl rows t i j) 4096

end

public section

theorem lOk_atoms {a b c d : Reg64} {rs : List Reg64} {S : SState}
    (h : lOk a b c d rs S = true) : atoms S rs = true := by
  simp only [lOk, Bool.and_eq_true] at h
  exact h.2

theorem sOk_atoms {a b c : Reg64} {nib : Sym} {rs : List Reg64} {S : SState}
    (h : sOk a b c nib rs S = true) : atoms S rs = true := by
  simp only [sOk, Bool.and_eq_true] at h
  exact h.2

theorem sOk_counter {a b c : Reg64} {nib : Sym} {rs : List Reg64} {S : SState}
    (h : sOk a b c nib rs S = true) : S.reg c = some nib := by
  simp only [sOk, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem inner_step (hp : Placed code k) (h : PreOk a s c m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {cx : Cx} (hA : cx.a = a) {rows : Array (Array EW)}
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {t i j : Nat} (ht : t < 6) (hi : i < half t) (hj : j < 64)
    {ib cx0 cx1 lo0 lo1 dr : Reg64} {s0 so dst : Nat}
    (hib : calleeSaved ib = true) (hs0 : s0 + 1024 < 2 ^ 64)
    (haddr : dst + s0 = 1024 * i + so)
    {vars : Nat → BitVec 64} {ks : List (Reg64 × Sym)} {ws : List (Nat × Sym)}
    (hvars : VarsOk cx t vars) (hwk : wfK ks = true)
    (hws : ws.all (fun p ↦ decide (16 ≤ p.1) && decide (p.1 + 8 ≤ 64)) = true)
    (hc0 : (cx0, V0) ∈ ks) (hc1 : (cx1, V1) ∈ ks)
    (hdr : ∀ d, KAt m0 vars ks d → reg d dr = off (rwA m0) dst)
    {bl bs : List Directive} {kl kb : Nat} {Sl Ss : SState} {label : Label}
    (hinl : bl.IsInfixAt code kl) (hins : bs.IsInfixAt code kb) (hnl : bl ≠ []) (hns : bs ≠ [])
    (hseq : kl + bl.length = kb)
    (hlabel : Labels.label label = Host.addrOf (k + kl))
    (hxl : exec bl (loS ib s0) = some (Sl, .call NativeRustcVmX64.Vm.EWMul.entryLabel))
    (hxs : exec bs (stS dr ib so) = some (Ss,
      .cond (notEnd (.bin .add .W64 (.lit 16) (.reg ib)) (s0 + 1024)) label))
    (hol : lOk cx0 cx1 lo0 lo1 (ib :: ks.map Prod.fst) Sl = true)
    (hos : sOk lo0 lo1 ib (.bin .add .W64 (.lit 16) (.reg ib)) (ks.map Prod.fst) Ss = true)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + kl))
    (hh : Inner cx m0 rows t i j ib s0 vars ks ws st.data) :
    Eventually (step1 Host.exe) (fun st' ↦
      st'.pc = (if j + 1 < 64 then Host.addrOf (k + kl) else Host.addrOf (k + kb + bs.length)) ∧
      Inner cx m0 rows t i (j + 1) ib s0 vars ks ws st'.data) st := by
  have hi64 : i < 64 := by have := Nat.div_le_self 32 (2 ^ t); unfold half at hi; omega
  have hn : 64 * i + j < 4096 := by omega
  have hct0 : reg st.data cx0 = (cx.sl.getD t 0).c0.toBitVec :=
    (hh.known.get hc0).trans hvars.2.1
  have hct1 : reg st.data cx1 = (cx.sl.getD t 0).c1.toBitVec :=
    (hh.known.get hc1).trans hvars.2.2
  refine (load_mul hp hmul h hA hj hinl hnl hxl hol hpc hh.mid hh.counter hct0 hct1
    hh.bufA hh.bufB).bind fun st1 ⟨hpc1, hm1, hprod0, hprod1, hlo0, hlo1, hreg1, hlow⟩ ↦ ?_
  have hk1 : KAt m0 vars ks st1.data := hh.known.regs_keep fun r hr ↦ by
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
    have hw := List.all_eq_true.mp hwk p hp'
    simp only [Bool.and_eq_true] at hw
    exact hreg1 p.1 (.reg p.1) hw.1 (atoms_reg (lOk_atoms hol) (.tail _ (List.mem_map.mpr ⟨p, hp', rfl⟩)))
  have hc1' : reg st1.data ib = BitVec.ofNat 64 (s0 + 16 * j) :=
    (hreg1 ib (.reg ib) hib (atoms_reg (lOk_atoms hol) (.head _))).trans hh.counter
  have hmatch := store_match hm1 (n := 64 * i + j) (so := so) (dr := dr) (ib := ib) (by
    rw [hdr st1.data hk1, hc1']
    exact counter_addr _ haddr)
  have hpc1' : st1.pc = Host.addrOf (k + kb) := by
    rw [← hseq, ← Nat.add_assoc]
    exact hpc1
  refine store_run hp h hA hn hins hns hxs (by intro l he; cases he) hos hpc1' hm1 hmatch
    hprod0 hprod1 hlo0 hlo1 fun st2 hpc2 hm2 hmid2 hvalue hstore ↦ ?_
  have hcounter := counter_next (env := storeEnv m0 st1.data (64 * i + j)) hc1'
  have hcnt2 : reg st2.data ib = BitVec.ofNat 64 (s0 + 16 * (j + 1)) :=
    (hm2.regs ib _ (sOk_counter hos)).trans hcounter
  have htest := notEnd_eval hj hs0 hcounter
  have hpc2' : st2.pc = (if j + 1 < 64 then Host.addrOf (k + kl) else Host.addrOf (k + kb + bs.length)) := by
    simpa only [PcOk, htest, decide_eq_true_eq, hlabel] using hpc2
  have hk2 : KAt m0 vars ks st2.data := hk1.regs_keep fun r hr ↦
    hm2.regs r (.reg r) (atoms_reg (sOk_atoms hos) hr)
  have hso : NativeRustcVm.SameOutside st.data.dmem st2.data.dmem (FoldTouch m0 (64 * i + j)) := by
    intro q hq
    exact (hstore q fun hx ↦ hq (.inr hx)).trans (hlow q fun hx ↦ hq (.inl hx))
  have hvalue' : NativeRustcVm.EWAt st2.data.dmem (off (rwA m0) (16 * (64 * i + j)))
      (W cx.sl rows (t + 1) i j) := by
    have hc (a b : EW) : a + b = b + a := by
      change EW.mk (a.c0 ^^^ b.c0) (a.c1 ^^^ b.c1) = EW.mk (b.c0 ^^^ a.c0) (b.c1 ^^^ a.c1)
      congr 1 <;> exact UInt64.xor_comm _ _
    rw [W_succ hrsz hrow (by rw [hh.mid.sl_size]; exact ht) hi hj, foldE,
      hc (W cx.sl rows t (2 * i) j)]
    exact hvalue
  refine .done _ ⟨hpc2', hmid2, hk2, keep_words h hn hh.words hws hso, hcnt2,
    keep_buffer h hn (by decide) (by decide) hh.bufA hso,
    keep_buffer h hn (by decide) (by decide) hh.bufB hso,
    rows_step h hi64 hj (rows_low h hh.rows hlow) hvalue' hstore⟩

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
