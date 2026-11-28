module

public import NativeRustcVmArm.Tables.TableSumcheck.Swap

/-!
# `table_sumcheck`: the challenges reversed in place

After the sumcheck the `n` challenges `xs` are the frame's elements from `24`, its claim at `512`
(`Rev 0`). `b3` halves `n`; with no swap to make it goes on to `b6`, else `b4` points X9 at the
first element and X10 at the last and the loop `b5` swaps them pairwise, `j` swaps in at its head
(`Rev j`, `Head j`; `swap_loop`). After `n / 2` swaps the elements are `xs.reverse` (`rev_half`):
`rev`.
-/

namespace NativeRustcVmArm.Tables.TableSumcheck

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TableSumcheck
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Tables
open NativeRustcVmArm.Sumcheck (Ctx)
open NativeRustcVm (ewOf)

@[expose] public section

/-- The frame after `j` swaps of the reverse. -/
structure Rev [Labels] (m0 : MachineData) (a : DecArea) (n : Nat) (xs : List EW) (c : EW)
    (s1 : TState) (j : Nat) (m : MachineData) : Prop where
  fr : Fr m0 720 tableSumcheckStack slots keep (outs m0) m
  regs : Regs m0 m n
  ts : TStateAt m.dmem m0.regs.X0.toBitVec a s1
  el : ∀ i < n, ewOf m.dmem (fb m0 + BitVec.ofNat 64 (24 + 16 * i)) = rv xs j i
  claim : ewOf m.dmem (fb m0 + BitVec.ofNat 64 512) = c

/-- The loop's registers at its head, `j` swaps in. -/
structure Head (m0 : MachineData) (n j : Nat) (m : MachineData) : Prop where
  x8 : (m.regs.getXReg .X8).toNat = n / 2 - j
  x9 : (m.regs.getXReg .X9).toBitVec = fb m0 + BitVec.ofNat 64 (24 + 16 * j)
  x10 : (m.regs.getXReg .X10).toBitVec = fb m0 + BitVec.ofNat 64 (24 + 16 * (n - 1 - j))

end

public section

section
variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat} {bus : BusResultW}
  {m0 : MachineData} {n : Nat} {xs : List EW} {c : EW} {s1 : TState}

/-- A block without writes that keeps `mids`: the same `Rev`. -/
theorem Rev.of_block {j : Nat} {m m' : MachineData} (h : Rev m0 a n xs c s1 j m)
    (hfr : Fr m0 720 tableSumcheckStack slots keep (outs m0) m') (hd : m'.dmem = m.dmem)
    (hk : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25],
      m'.regs.getXReg r = m.regs.getXReg r) : Rev m0 a n xs c s1 j m' where
  fr := hfr
  regs := h.regs.of hk
  ts := by rw [hd]; exact h.ts
  el := by rw [hd]; exact h.el
  claim := by rw [hd]; exact h.claim

omit [Host] in
theorem keeps_mids {S : SState} (h : mids.all (fun r ↦ S.reg r == some (.reg r)) = true) :
    ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25], S.reg r = some (.reg r) := fun r hr ↦
  reg_keep h (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)

/-- **The loop**: from `j` swaps with `r ≥ 1` to make, to `b6` with all `n / 2` made. -/
theorem swap_loop (hp : Placed code k) (hS : StackOk m0 tableSumcheckStack)
    (cx : Ctx m0 m0.regs.X0.toBitVec a tableSumcheckStack 720) (hn30 : n ≤ 30)
    (hxs : xs.length = n)
    (cont : ∀ m', Rev m0 a n xs c s1 (n / 2) m' →
      Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.TableSumcheck.b6Offset)⟩) :
    ∀ r j m, j + r = n / 2 → 0 < r → Rev m0 a n xs c s1 j m → Head m0 n j m →
      Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableSumcheck.b5Offset)⟩ := by
  intro r
  induction r with
  | zero => intro j m _ h; omega
  | succ r ih =>
  intro j m hjr _ hR hH
  have hN := hS.2.1
  have h720 : 720 ≤ tableSumcheckStack := N_ge
  have hSP := m0.regs.SP.toNat_lt
  have hfb := fb_toNat hS N_ge
  have hj2 : 2 * j + 2 ≤ n := by omega
  set p := fb m0 + BitVec.ofNat 64 (24 + 16 * j) with hpdef
  set q := fb m0 + BitVec.ofNat 64 (24 + 16 * (n - 1 - j)) with hqdef
  have loc := fun (o l : Nat) (h : o + l ≤ 720) ↦
    Bus.local_ok (N' := 0) (m := m) hS (by have := N_ge; omega) h hR.fr.kept hR.fr.sp
  have hp16 := (loc (24 + 16 * j) 16 (by omega)).1
  have hq16 := (loc (24 + 16 * (n - 1 - j)) 16 (by omega)).1
  have hpq : Apart p 16 q 16 := by
    unfold Apart
    rw [hpdef, hqdef, fb_add hS N_ge (by omega), fb_add hS N_ge (by omega)]
    omega
  have hwf := wf_swap hp16 hq16 hpq
  have hm := match_swap hH.x9 hH.x10
  refine exec_then (b5_in_code.trans hp.1 (by simp [b5])) run_b5' hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨hsp5, -, hk5, h8, h9, h10⟩ := ok_b5
  have hnl : ∀ {o : Nat}, o + 16 ≤ 720 → (o + 16 ≤ 24 + 16 * j ∨ 24 + 16 * j + 16 ≤ o) →
      (o + 16 ≤ 24 + 16 * (n - 1 - j) ∨ 24 + 16 * (n - 1 - j) + 16 ≤ o) →
      ∀ b < 16, st.data.dmem.get? (fb m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 b) =
        m.dmem.get? (fb m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 b) := by
    intro o ho h1 h2 b hb
    rw [NativeRustcVm.addr_add_add]
    exact swap_other hm' hwf (Bus.Gkr.not_loc (by omega) (by omega) (by omega) (by omega))
      (Bus.Gkr.not_loc (by omega) (by omega) (by omega) (by omega))
  have hW : ∀ x, Written (envS m p q) (Bus.after b5 revS) x →
      InRange (fb m0 + BitVec.ofNat 64 24) (16 * n) x := fun x hx ↦
    (written_swap hwf hx).elim (inRange_fb hS N_ge (by omega) (by omega) (by omega))
      (inRange_fb hS N_ge (by omega) (by omega) (by omega))
  have hfr : Fr m0 720 tableSumcheckStack slots keep (outs m0) st.data := by
    refine hR.fr.step (W := Written (envS m p q) (Bus.after b5 revS))
      (UInt64.toBitVec_inj.mp (by rw [hm'.sp, hsp5]; rfl)) (by simp) (hm'.kept hwf)
      (hm'.sameOutside hwf)
      (fun x hx ↦ .inl (fb_stack hS N_ge (by omega) (hW x hx))) fun sl hsl b hb hx ↦ ?_
    have := slots_hi sl hsl
    have h' := hW _ hx
    rw [NativeRustcVm.addr_add_add] at h'
    exact Bus.Gkr.not_loc (by omega) (by omega) (by omega) (by omega) h'
  have hR' : Rev m0 a n xs c s1 (j + 1) st.data := by
    refine ⟨hfr, hR.regs.of fun r hr ↦ Bus.Gkr.reg_of hm' (keeps_mids hk5 r hr),
      tstate_keep cx (fun x hx ↦ fb_stack hS N_ge (by omega) (hW x hx)) hR.ts (hm'.kept hwf)
        (hm'.sameOutside hwf), fun i hi ↦ ?_, ?_⟩
    · rw [rv_succ xs (by omega)]
      by_cases e1 : i = j
      · subst e1
        simp only [↓reduceIte]
        rw [swap_x9 hm' hwf, ← hR.el _ (by omega)]
        congr 3
        omega
      · simp only [e1, ↓reduceIte]
        by_cases e2 : i = xs.length - 1 - j
        · simp only [e2, ↓reduceIte]
          rw [hxs, swap_x10 hm' hwf, ← hR.el _ (by omega)]
        · simp only [e2, ↓reduceIte]
          rw [← hR.el _ hi]
          exact NativeRustcVm.ewOf_congr (hnl (by omega)
            (by rcases Nat.lt_or_gt_of_ne e1 with h | h <;> omega)
            (by rcases Nat.lt_or_gt_of_ne e2 with h | h <;> omega))
    · rw [← hR.claim]
      exact NativeRustcVm.ewOf_congr (hnl (by omega) (by omega) (by omega))
  have h8n : (m.regs.getXReg .X8).toBitVec.toNat = n / 2 - j := hH.x8
  have hx8 : (st.data.regs.getXReg .X8).toNat = n / 2 - (j + 1) := by
    show (st.data.regs.getXReg .X8).toBitVec.toNat = _
    rw [hm'.regs .X8 _ h8]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [sub_lit _ 1 (by omega)]
    omega
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs] at hpc
  rw [sub1_beq _ (by omega)] at hpc
  by_cases hr0 : r = 0
  · subst hr0
    have hz : (m.regs.getXReg .X8).toBitVec.toNat = 1 := by omega
    simp only [hz, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc
    rw [show k + NativeRustcVmArm.Vm.TableSumcheck.b5Offset + b5.length = k + NativeRustcVmArm.Vm.TableSumcheck.b6Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableSumcheck.b5_next]] at hpc
    exact Bus.Gkr.at_pc hpc (cont _ (by rw [show n / 2 = j + 1 by omega]; exact hR'))
  · have hz : (m.regs.getXReg .X8).toBitVec.toNat ≠ 1 := by omega
    simp only [hz, decide_false, Bool.not_false, ↓reduceIte] at hpc
    refine Bus.Gkr.at_pc (hpc.trans (hp.label (j := NativeRustcVmArm.Vm.TableSumcheck.b5Offset) NativeRustcVmArm.Vm.TableSumcheck.label_4_at))
      (ih (j + 1) st.data (by omega) (by omega) hR' ⟨hx8, ?_, ?_⟩)
    · rw [hm'.regs .X9 _ h9]
      simp only [Sym.eval, envS, Env.base_ofMachine_eq,
        List.getElem?_cons_zero, Option.map_some, Option.getD_some]
      rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, NativeRustcVm.addr_add_add]
      exact congrArg (fun x ↦ fb m0 + BitVec.ofNat 64 x) (by omega)
    · rw [hm'.regs .X10 _ h10]
      simp only [Sym.eval, envS, Env.base_ofMachine_eq,
        List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some, Option.getD_some]
      rw [show (-16 : Int) = -((16 : Nat) : Int) from rfl, add_ofInt_neg _ (by omega)]
      congr 2
      omega

/-- **The reverse** (`b3`, `b4`, the loop): from the sumcheck's challenges to their reverse. -/
theorem rev (hp : Placed code k) (hS : StackOk m0 tableSumcheckStack)
    (cx : Ctx m0 m0.regs.X0.toBitVec a tableSumcheckStack 720) (hn30 : n ≤ 30)
    (hxs : xs.length = n)
    (cont : ∀ m', Rev m0 a n xs c s1 (n / 2) m' →
      Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.TableSumcheck.b6Offset)⟩)
    {m : MachineData} (hR : Rev m0 a n xs c s1 0 m) :
    Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableSumcheck.b3Offset)⟩ := by
  have hN := hS.2.1
  have h720 : 720 ≤ tableSumcheckStack := N_ge
  have hSP := m0.regs.SP.toNat_lt
  have hfb := fb_toNat hS N_ge
  have h25 : (m.regs.getXReg .X25).toBitVec.toNat = n := hR.regs.x25
  refine Bus.Gkr.Fr.runBlock hS N_ge rfl hR.fr (b3_in_code.trans hp.1 (by simp [b3])) run_b3'
    ok_b3.2.1 ok_b3.1 rfl rfl fun st hfr hd hm hpc ↦ ?_
  have hR3 := hR.of_block hfr hd fun r hr ↦ Bus.Gkr.reg_of hm (keeps_mids ok_b3.2.2.1 r hr)
  have e8 : UnOp.apply (.ubfm 1 63) .W64 (m.regs.getXReg .X25).toBitVec =
      BitVec.ofNat 64 (n / 2) :=
    BitVec.eq_of_toNat_eq (by rw [lsr1, h25, BitVec.toNat_ofNat]; omega)
  have h8 : (st.data.regs.getXReg .X8).toBitVec.toNat = n / 2 := by
    rw [hm.regs .X8 _ ok_b3.2.2.2]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [e8, BitVec.toNat_ofNat]; omega
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs, e8] at hpc
  by_cases hz : n / 2 = 0
  · rw [hz] at hpc
    simp only [beq_self_eq_true, ↓reduceIte] at hpc
    exact Bus.Gkr.at_pc (hpc.trans (hp.label (j := NativeRustcVmArm.Vm.TableSumcheck.b6Offset) NativeRustcVmArm.Vm.TableSumcheck.label_5_at)) (cont _ (by rw [hz]; exact hR3))
  · have hne : (BitVec.ofNat 64 (n / 2) == BitVec.ofNat 64 0) = false :=
      beq_eq_false_iff_ne.mpr fun h ↦ by
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        omega
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at hpc
    rw [show k + NativeRustcVmArm.Vm.TableSumcheck.b3Offset + b3.length = k + NativeRustcVmArm.Vm.TableSumcheck.b4Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableSumcheck.b3_next]] at hpc
    refine Bus.Gkr.at_pc hpc (Bus.Gkr.Fr.runBlock hS N_ge rfl hR3.fr
      (b4_in_code.trans hp.1 (by simp [b4])) run_b4 rfl rfl rfl rfl fun st4 hfr4 hd4 hm4 hpc4 ↦ ?_)
    have hm4' : Match (Env.ofMachine st.data [(base m0 720, 720)]) (Bus.after b4 sF) st4.data := by
      rw [Bus.after_eq run_b4]; exact hm4
    obtain ⟨-, -, hk4, g8, g9, g10⟩ := ok_b4
    have hR4 := hR3.of_block hfr4 hd4 fun r hr ↦ Bus.Gkr.reg_of hm4' (keeps_mids hk4 r hr)
    have h25' : (st.data.regs.getXReg .X25).toBitVec.toNat = n := hR3.regs.x25
    have e16 : UnOp.apply (.shift .LSL 4) .W64 (st.data.regs.getXReg .X25).toBitVec =
        BitVec.ofNat 64 (16 * n) :=
      BitVec.eq_of_toNat_eq (by rw [lsl4 _ (by omega), h25', BitVec.toNat_ofNat]; omega)
    have hb24 : (base m0 720 + BitVec.ofInt 64 24).toNat = (fb m0).toNat + 24 :=
      fb_add hS N_ge (o := 24) (by omega)
    simp only [PcOk] at hpc4
    rw [show k + NativeRustcVmArm.Vm.TableSumcheck.b4Offset + b4.length = k + NativeRustcVmArm.Vm.TableSumcheck.b5Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableSumcheck.b4_next]] at hpc4
    refine Bus.Gkr.at_pc hpc4 (swap_loop hp hS cx hn30 hxs cont (n / 2) 0 st4.data (by omega)
      (by omega) hR4 ⟨?_, ?_, ?_⟩)
    · rw [Bus.Gkr.reg_of hm4' g8]; exact h8
    · rw [hm4'.regs .X9 _ g9]
      simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some]
      rfl
    · rw [hm4'.regs .X10 _ g10]
      simp only [Sym.eval, Env.ofMachine_regs, Env.base_ofMachine_eq, List.getElem?_cons_zero,
        Option.map_some, Option.getD_some, e16]
      apply BitVec.eq_of_toNat_eq
      rw [sub_lit _ 16 (by rw [add_lit _ _ (by omega), hb24]; omega), add_lit _ _ (by omega), hb24,
        fb_add hS N_ge (by omega)]
      omega

end

end

end NativeRustcVmArm.Tables.TableSumcheck
