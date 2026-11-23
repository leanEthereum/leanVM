module

public import NativeRustcVmArm.Wire.RdRows.ZeroA

/-!
# `rd_rows`' zeros of a leaf without a row (`rw = 0`)

From the loop's head at leaf `i` (`HeadB`, `b16`): no zeros (`lw = 0`), or four at a time
(`b17`, `b18`, `b19`, `VecB`) then one at a time (`b20`, `b21`, `SclB`), up to the call (`CallB`):
`fillB_spec`.
-/

namespace NativeRustcVmArm.Wire.RdRows

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.RdRows
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- The registers the loop over the leaves keeps (`rw = 0`). -/
def regsB : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28]

/-- **The loop over the leaves at leaf `i`** (`rw = 0`). -/
structure RegB (m0 : MachineData) (i : Nat) (s : MachineData) : Prop where
  fr : Frm m0 s
  x19 : (s.regs.getXReg .X19).toBitVec = leaf m0 i
  x20 : s.regs.getXReg .X20 = m0.regs.X2
  x21 : (s.regs.getXReg .X21).toBitVec = rdr m0
  x22 : (s.regs.getXReg .X22).toNat = 8 * lw m0
  x23 : 0 < lw m0 → (s.regs.getXReg .X23).toNat = 8 * lw m0 - 8
  x24 : (s.regs.getXReg .X24).toBitVec = leaf m0 (nr m0)
  x25 : 0 < lw m0 → (s.regs.getXReg .X25).toNat = lw m0
  x26 : 0 < lw m0 → (s.regs.getXReg .X26).toNat = q4 (lw m0)
  x27 : 0 < lw m0 → (s.regs.getXReg .X27).toNat = 8 * q4 (lw m0)
  x28 : (s.regs.getXReg .X28).toBitVec = leaf m0 i + BitVec.ofNat 64 16
  lt : i < nr m0
  rw0 : rw m0 = 0

/-- **Zeros of leaf `i`**: `t` of them written (`rw = 0`). -/
structure ZB (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c i t : Nat)
    (rows : List (List K)) (ci : Nat) (s : MachineData) : Prop where
  reg : RegB m0 i s
  kept : Kept m0 bp B c i rows ci s.dmem
  zs : WordsAt s.dmem (leaf m0 i) (List.replicate t 0)
  le : t ≤ lw m0

end

public section

theorem RegB.keep {m0 : MachineData} {i : Nat} {s s' : MachineData} (h : RegB m0 i s)
    (hfr : Frm m0 s') (hr : ∀ r ∈ regsB, s'.regs.getXReg r = s.regs.getXReg r) :
    RegB m0 i s' where
  fr := hfr
  x19 := by rw [hr .X19 (by simp [regsB])]; exact h.x19
  x20 := by rw [hr .X20 (by simp [regsB])]; exact h.x20
  x21 := by rw [hr .X21 (by simp [regsB])]; exact h.x21
  x22 := by rw [hr .X22 (by simp [regsB])]; exact h.x22
  x23 := by rw [hr .X23 (by simp [regsB])]; exact h.x23
  x24 := by rw [hr .X24 (by simp [regsB])]; exact h.x24
  x25 := by rw [hr .X25 (by simp [regsB])]; exact h.x25
  x26 := by rw [hr .X26 (by simp [regsB])]; exact h.x26
  x27 := by rw [hr .X27 (by simp [regsB])]; exact h.x27
  x28 := by rw [hr .X28 (by simp [regsB])]; exact h.x28
  lt := h.lt
  rw0 := h.rw0

variable [Host] (k : Nat) (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c : Nat)

/-- The loop's head (`b16`) at leaf `i`. -/
structure HeadB (i : Nat) (rows : List (List K)) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RdRows.b16Offset)
  reg : RegB m0 i st.data
  kept : Kept m0 bp B c i rows ci st.data.dmem

/-- The zeros one at a time (`b21`), `t` written. -/
structure SclB (i t : Nat) (rows : List (List K)) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RdRows.b21Offset)
  z : ZB m0 bp B c i t rows ci st.data
  x8 : (st.data.regs.getXReg .X8).toBitVec = leaf m0 i + BitVec.ofNat 64 (8 * lw m0)
  x9 : (st.data.regs.getXReg .X9).toBitVec = leaf m0 i + BitVec.ofNat 64 (8 * t)
  lt : t < lw m0

/-- The zeros four at a time (`b19`), `t` written. -/
structure VecB (i t : Nat) (rows : List (List K)) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RdRows.b19Offset)
  z : ZB m0 bp B c i t rows ci st.data
  x8 : (st.data.regs.getXReg .X8).toBitVec = leaf m0 i + BitVec.ofNat 64 (8 * lw m0)
  x9 : (st.data.regs.getXReg .X9).toBitVec = leaf m0 i + BitVec.ofNat 64 (8 * q4 (lw m0))
  x10 : (st.data.regs.getXReg .X10).toBitVec = leaf m0 i + BitVec.ofNat 64 (8 * t + 16)
  x11 : (st.data.regs.getXReg .X11).toNat = q4 (lw m0) - t
  t4 : t % 4 = 0
  lt : t + 4 ≤ q4 (lw m0)

/-- The call (`b22`), the leaf's zeros written. -/
structure CallB (i : Nat) (rows : List (List K)) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RdRows.b22Offset)
  z : ZB m0 bp B c i (lw m0) rows ci st.data

variable {k m0 bp B c}

/-- **A zero** (`b21`): on, or all written. -/
theorem sclB_step (hp : Placed code k) (G : Geo m0 bp B) {i t : Nat} {rows : List (List K)}
    {ci : Nat} {st : MachineState} (hI : SclB k m0 bp B c i t rows ci st) :
    Eventually (step1 Host.exe)
      (fun st' ↦ CallB k m0 bp B c i rows ci st' ∨ SclB k m0 bp B c i (t + 1) rows ci st') st := by
  have hi := hI.z.reg.lt
  have hz := hI.lt
  have hlw := G.lw64
  have hwf := G.chunk_wf hi (o := 8 * t) (sz := 8) (by omega) (by omega) hI.z.reg.fr
  have hm : Match (chEnv m0 st.data (leaf m0 i + BitVec.ofNat 64 (8 * t)) 8) sclS' st.data :=
    chunk_match G hI.z.reg.fr rfl (by
      show (st.data.regs.getXReg .X9).toBitVec = _
      rw [hI.x9, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero])
  refine exec_at (infix_of b21_in_code (by simp [b21]) hp) run_b21 hwf hI.pc hm fun s1 hm1 hpc1 ↦ ?_
  have hs : SameOutside st.data.dmem s1.data.dmem
      (InRange (leaf m0 i + BitVec.ofNat 64 (8 * t)) 8) := by
    have := Match.sameOutside_in hm1 hwf (r0 := 1) (o := 0) (n := 8) rfl (by omega) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  have h0 : WordAt s1.data.dmem (leaf m0 i + BitVec.ofNat 64 (8 * t)) 0 := by
    have := zero_word hm1 (r := 1) (o := 0) (sz := 8) rfl (by omega) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hfr1 : Frm m0 s1.data :=
    Frm.chunk G hi (o := 8 * t) (sz := 8) (by omega) (by omega) hI.z.reg.fr hm hm1 hwf rfl rfl hs
  have hr := regs_keep hm hm1 (rs := .X8 :: regsB) (by decide)
  have hz1 : ZB m0 bp B c i (t + 1) rows ci s1.data :=
    ⟨hI.z.reg.keep hfr1 (fun r h ↦ hr r (List.mem_cons_of_mem _ h)),
      Kept.chunk G hI.z.kept hi (o := 8 * t) (sz := 8) (by omega) (by omega) hs,
      zeros_snoc (zeros_chunk G hi (o := 8 * t) (sz := 8) (by omega) (le_refl _) hs hI.z.zs) h0,
      by omega⟩
  have e9 : (st.data.regs.getXReg .X9).toBitVec + BitVec.ofNat 64 8 =
      leaf m0 i + BitVec.ofNat 64 (8 * (t + 1)) := by
    rw [hI.x9, NativeRustcVm.addr_add_add]; congr 2
  have hc : (SBool.cmp .eq .W64 (.bin .add .W64 (.reg .X9) (.lit 8)) (.reg .X8)).not.eval
      (chEnv m0 st.data (leaf m0 i + BitVec.ofNat 64 (8 * t)) 8) = decide (t + 1 ≠ lw m0) := by
    simp only [SBool.eval, eq_apply, Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64,
      Env.ofMachine_regs, e9, hI.x8]
    by_cases h : t + 1 = lw m0
    · rw [h]; simp
    · have hn := G.lvNw
      rw [G.leaf_toNat (by omega), NativeRustcVm.addr_add_add]
      rcases NativeRustcVm.toNat_add_ofNat_le (a := lv m0) (i := 512 * i + 8 * lw m0)
        (by omega) with h2 | ⟨h2, -⟩ <;> rw [h2] <;>
      · rw [decide_eq_false (by omega), decide_eq_true h]; rfl
  simp only [PcOk, hc] at hpc1
  by_cases hend : t + 1 = lw m0
  · simp only [hend, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      at hpc1
    exact .done _ (.inl ⟨hpc1.trans (congrArg Host.addrOf rfl), hend ▸ hz1⟩)
  simp only [ne_eq, hend, not_false_eq_true, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.RdRows.b21Offset) NativeRustcVmArm.Vm.RdRows.label_19_at]
    at hpc1
  refine .done _ (.inr ⟨hpc1, hz1, by rw [hr .X8 List.mem_cons_self]; exact hI.x8, ?_, by omega⟩)
  rw [hm1.regs .X9 _ rfl]
  simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
  exact e9

/-- **The zeros one at a time**, to the call. -/
theorem sclB_loop (hp : Placed code k) (G : Geo m0 bp B) {i t : Nat} {rows : List (List K)}
    {ci : Nat} {st : MachineState} (hI : SclB k m0 bp B c i t rows ci st) :
    Eventually (step1 Host.exe) (CallB k m0 bp B c i rows ci) st := by
  refine Sym.loop (fun n st ↦ ∃ t, n = lw m0 - t ∧ SclB k m0 bp B c i t rows ci st)
    (fun n st ⟨t, hn, hI⟩ ↦ ?_) ⟨t, rfl, hI⟩
  refine Eventually.mono (sclB_step hp G hI) fun st' h ↦ ?_
  rcases h with h | h
  · exact .inl h
  · exact .inr ⟨_, by have := hI.lt; omega, t + 1, rfl, h⟩

/-- **The tail of the fours** (`b20`): the call, or the zeros one at a time from `q4`. -/
theorem twentyB_spec (hp : Placed code k) (G : Geo m0 bp B) {i : Nat} {rows : List (List K)}
    {ci : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RdRows.b20Offset))
    (hz : ZB m0 bp B c i (q4 (lw m0)) rows ci st.data)
    (h8 : (st.data.regs.getXReg .X8).toBitVec = leaf m0 i + BitVec.ofNat 64 (8 * lw m0))
    (h9 : (st.data.regs.getXReg .X9).toBitVec = leaf m0 i + BitVec.ofNat 64 (8 * q4 (lw m0)))
    (h0 : 0 < lw m0) :
    Eventually (step1 Host.exe) (CallB k m0 bp B c i rows ci) st := by
  have hst := G.g.st
  have hwf := frEnv_wf hst hz.reg.fr
  have hm := frEnv_match hst hz.reg.fr
  have hq := q4_le (lw m0)
  refine exec_at (infix_of b20_in_code (by simp [b20]) hp) run_b20 hwf hpc hm fun s1 hm1 hpc1 ↦ ?_
  have hd : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hfr1 : Frm m0 s1.data := Fr.ofBlock hz.reg.fr hm hm1 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have hr := regs_keep hm hm1 (rs := .X8 :: .X9 :: regsB) (by decide)
  have hz1 : ZB m0 bp B c i (q4 (lw m0)) rows ci s1.data :=
    ⟨hz.reg.keep hfr1 (fun r h ↦ hr r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))),
      by rw [hd]; exact hz.kept, by rw [hd]; exact hz.zs, hz.le⟩
  have hc : (SBool.cmp .eq .W64 (.reg .X25) (.reg .X26)).eval (frEnv m0 st.data) =
      decide (lw m0 = q4 (lw m0)) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs]
    rw [UInt64.toNat_toBitVec, UInt64.toNat_toBitVec, hz.reg.x25 h0, hz.reg.x26 h0]
  simp only [PcOk, hc] at hpc1
  by_cases he : lw m0 = q4 (lw m0)
  · simp only [decide_eq_true he, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.RdRows.b22Offset) NativeRustcVmArm.Vm.RdRows.label_20_at] at hpc1
    exact .done _ ⟨hpc1, he ▸ hz1⟩
  simp only [decide_eq_false he, Bool.false_eq_true, ↓reduceIte] at hpc1
  exact sclB_loop hp G ⟨hpc1.trans (congrArg Host.addrOf rfl), hz1,
    by rw [hr .X8 (by simp)]; exact h8, by rw [hr .X9 (by simp)]; exact h9, by omega⟩

/-- **Four zeros** (`b19`): on, or the tail. -/
theorem vecB_step (hp : Placed code k) (G : Geo m0 bp B) {i t : Nat} {rows : List (List K)}
    {ci : Nat} {st : MachineState} (hI : VecB k m0 bp B c i t rows ci st) :
    Eventually (step1 Host.exe)
      (fun st' ↦ CallB k m0 bp B c i rows ci st' ∨ VecB k m0 bp B c i (t + 4) rows ci st') st := by
  have hi := hI.z.reg.lt
  have ht4 := hI.t4
  have hlt := hI.lt
  have hlw := G.lw64
  have hq := q4_le (lw m0)
  have hwf := G.chunk_wf hi (o := 8 * t) (sz := 32) (by omega) (by omega) hI.z.reg.fr
  have hm : Match (chEnv m0 st.data (leaf m0 i + BitVec.ofNat 64 (8 * t)) 32) vecS' st.data :=
    chunk_match G hI.z.reg.fr rfl (by
      show (st.data.regs.getXReg .X10).toBitVec =
        leaf m0 i + BitVec.ofNat 64 (8 * t) + BitVec.ofInt 64 16
      rw [hI.x10, show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl,
        NativeRustcVm.addr_add_add (leaf m0 i)])
  refine exec_at (infix_of b19_in_code (by simp [b19]) hp) run_b19 hwf hI.pc hm fun s1 hm1 hpc1 ↦ ?_
  have hs : SameOutside st.data.dmem s1.data.dmem
      (InRange (leaf m0 i + BitVec.ofNat 64 (8 * t)) 32) := by
    have := Match.sameOutside_in hm1 hwf (r0 := 1) (o := 0) (n := 32) rfl (by omega) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hfr1 : Frm m0 s1.data :=
    Frm.chunk G hi (o := 8 * t) (sz := 32) (by omega) (by omega) hI.z.reg.fr hm hm1 hwf rfl rfl hs
  have hr := regs_keep hm hm1 (rs := .X8 :: .X9 :: regsB) (by decide)
  have hz1 : ZB m0 bp B c i (t + 4) rows ci s1.data :=
    ⟨hI.z.reg.keep hfr1 (fun r h ↦ hr r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))),
      Kept.chunk G hI.z.kept hi (o := 8 * t) (sz := 32) (by omega) (by omega) hs,
      zeros4 (zeros_chunk G hi (o := 8 * t) (sz := 32) (by omega) (le_refl _) hs hI.z.zs)
        fun j hj ↦ by
          rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
            exact zero_word hm1 (r := 1) (sz := 32) rfl (by omega) (by decide),
      by omega⟩
  have h11 : ((Sym.reg .X11).eval (chEnv m0 st.data (leaf m0 i + BitVec.ofNat 64 (8 * t)) 32)).toNat =
      q4 (lw m0) - t := hI.x11
  have hc : (SBool.cmp .eq .W64 (.reg .X11) (.lit 4)).not.eval
      (chEnv m0 st.data (leaf m0 i + BitVec.ofNat 64 (8 * t)) 32) = decide (t + 4 ≠ q4 (lw m0)) := by
    simp only [SBool.eval, eq_apply]
    rw [h11, show ((Sym.lit 4).eval (chEnv m0 st.data (leaf m0 i + BitVec.ofNat 64 (8 * t)) 32)).toNat
      = 4 from rfl]
    by_cases h : t + 4 = q4 (lw m0)
    · rw [decide_eq_true (by omega), decide_eq_false (by omega)]; rfl
    · rw [decide_eq_false (by omega), decide_eq_true h]; rfl
  simp only [PcOk, hc] at hpc1
  by_cases hend : t + 4 = q4 (lw m0)
  · simp only [hend, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      at hpc1
    refine Eventually.mono (twentyB_spec hp G (hpc1.trans (congrArg Host.addrOf rfl)) (hend ▸ hz1)
      (by rw [hr .X8 (by simp)]; exact hI.x8) (by rw [hr .X9 (by simp)]; exact hI.x9) (by omega))
      fun _ h ↦ .inl h
  simp only [ne_eq, hend, not_false_eq_true, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.RdRows.b19Offset) NativeRustcVmArm.Vm.RdRows.label_17_at]
    at hpc1
  refine .done _ (.inr ⟨hpc1, hz1, by rw [hr .X8 (by simp)]; exact hI.x8,
    by rw [hr .X9 (by simp)]; exact hI.x9, ?_, ?_, by omega, by omega⟩)
  · rw [hm1.regs .X10 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [hI.x10, NativeRustcVm.addr_add_add (leaf m0 i),
      show 8 * t + 16 + 32 = 8 * (t + 4) + 16 by omega]
  · show (s1.data.regs.getXReg .X11).toBitVec.toNat = _
    rw [hm1.regs .X11 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [toNat_sub_lit (by rw [UInt64.toNat_toBitVec, hI.x11]; omega) (by omega),
      UInt64.toNat_toBitVec, hI.x11]
    omega

/-- **The zeros four at a time**, to the call. -/
theorem vecB_loop (hp : Placed code k) (G : Geo m0 bp B) {i t : Nat} {rows : List (List K)}
    {ci : Nat} {st : MachineState} (hI : VecB k m0 bp B c i t rows ci st) :
    Eventually (step1 Host.exe) (CallB k m0 bp B c i rows ci) st := by
  refine Sym.loop (fun n st ↦ ∃ t, n = q4 (lw m0) - t ∧ VecB k m0 bp B c i t rows ci st)
    (fun n st ⟨t, hn, hI⟩ ↦ ?_) ⟨t, rfl, hI⟩
  refine Eventually.mono (vecB_step hp G hI) fun st' h ↦ ?_
  rcases h with h | h
  · exact .inl h
  · exact .inr ⟨_, by have := hI.lt; omega, t + 4, rfl, h⟩

/-- **The zeros of leaf `i`**, from the loop's head (`b16`, `b17`, `b18`). -/
theorem fillB_spec (hp : Placed code k) (G : Geo m0 bp B) {i : Nat} {rows : List (List K)}
    {ci : Nat} {st : MachineState} (hI : HeadB k m0 bp B c i rows ci st) :
    Eventually (step1 Host.exe) (CallB k m0 bp B c i rows ci) st := by
  have hst := G.g.st
  have hlw := G.lw64
  have hq := q4_le (lw m0)
  have hwf := frEnv_wf hst hI.reg.fr
  have hm := frEnv_match hst hI.reg.fr
  refine exec_at (infix_of b16_in_code (by simp [b16]) hp) run_b16 hwf hI.pc hm fun s1 hm1 hpc1 ↦ ?_
  have hd : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hfr1 : Frm m0 s1.data := Fr.ofBlock hI.reg.fr hm hm1 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have hr := regs_keep hm hm1 (rs := regsB) (by decide)
  have hreg1 : RegB m0 i s1.data := hI.reg.keep hfr1 hr
  have h8 : (s1.data.regs.getXReg .X8).toBitVec = leaf m0 i + BitVec.ofNat 64 (8 * lw m0) := by
    rw [hm1.regs .X8 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [hI.reg.x19]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [UInt64.toNat_toBitVec, hI.reg.x22, BitVec.toNat_ofNat]
    omega
  have hc : (SBool.cmp .eq .W64 (.reg .X20) (.lit 0)).eval (frEnv m0 st.data) =
      decide (lw m0 = 0) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs, hI.reg.x20]
    rfl
  simp only [PcOk, hc] at hpc1
  by_cases h0 : lw m0 = 0
  · simp only [h0, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.RdRows.b22Offset) NativeRustcVmArm.Vm.RdRows.label_20_at] at hpc1
    exact .done _ ⟨hpc1, hreg1, by rw [hd]; exact hI.kept,
      by rw [h0]; exact NativeRustcVm.wordsAt_nil _ _, by omega⟩
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  have hz1 : ZB m0 bp B c i 0 rows ci s1.data :=
    ⟨hreg1, by rw [hd]; exact hI.kept, NativeRustcVm.wordsAt_nil _ _, by omega⟩
  -- `b17`
  have hwf2 := frEnv_wf hst hfr1
  have hm2 := frEnv_match hst hfr1
  refine exec_at (infix_of b17_in_code (by simp [b17]) hp) run_b17 hwf2
    (hpc1.trans (congrArg Host.addrOf rfl)) hm2 fun s2 hm2' hpc2 ↦ ?_
  have hd2 : s2.data.dmem = s1.data.dmem := hm2'.dmem_eq hwf2 rfl
  have hfr2 : Frm m0 s2.data := Fr.ofBlock hfr1 hm2 hm2' hwf2 rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have hr2 := regs_keep hm2 hm2' (rs := .X8 :: regsB) (by decide)
  have hz2 : ZB m0 bp B c i 0 rows ci s2.data :=
    ⟨hreg1.keep hfr2 (fun r h ↦ hr2 r (List.mem_cons_of_mem _ h)),
      by rw [hd2]; exact hz1.kept, NativeRustcVm.wordsAt_nil _ _, by omega⟩
  have h23 := hreg1.x23 (by omega)
  have hc2 : (SBool.cmp .ult .W64 (.reg .X23) (.lit 24)).eval (frEnv m0 s1.data) =
      decide (lw m0 < 4) := by
    simp only [SBool.eval, ult_apply, Sym.eval, Env.ofMachine_regs]
    rw [UInt64.toNat_toBitVec, h23]
    by_cases h : lw m0 < 4
    · rw [decide_eq_true (by simp; omega), decide_eq_true h]
    · rw [decide_eq_false (by simp; omega), decide_eq_false h]
  simp only [PcOk, hc2] at hpc2
  by_cases h4 : lw m0 < 4
  · simp only [h4, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.RdRows.b21Offset) NativeRustcVmArm.Vm.RdRows.label_19_at] at hpc2
    refine sclB_loop hp G ⟨hpc2, hz2, by rw [hr2 .X8 (by simp)]; exact h8, ?_, by omega⟩
    rw [hm2'.regs .X9 _ rfl]
    show (s1.data.regs.getXReg .X19).toBitVec = _
    rw [hreg1.x19, Nat.mul_zero, NativeRustcVm.addr_add_zero]
  simp only [h4, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc2
  -- `b18`
  have hwf3 := frEnv_wf hst hfr2
  have hm3 := frEnv_match hst hfr2
  refine exec_at (infix_of b18_in_code (by simp [b18]) hp) run_b18 hwf3
    (hpc2.trans (congrArg Host.addrOf rfl)) hm3 fun s3 hm3' hpc3 ↦ ?_
  have hd3 : s3.data.dmem = s2.data.dmem := hm3'.dmem_eq hwf3 rfl
  have hfr3 : Frm m0 s3.data := Fr.ofBlock hfr2 hm3 hm3' hwf3 rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have hr3 := regs_keep hm3 hm3' (rs := .X8 :: regsB) (by decide)
  have hreg2 := hz2.reg
  simp only [PcOk] at hpc3
  refine vecB_loop hp G (t := 0) ⟨hpc3.trans (congrArg Host.addrOf rfl),
    ⟨hreg2.keep hfr3 (fun r h ↦ hr3 r (List.mem_cons_of_mem _ h)),
      by rw [hd3]; exact hz2.kept, NativeRustcVm.wordsAt_nil _ _, by omega⟩,
    by rw [hr3 .X8 (by simp), hr2 .X8 (by simp)]; exact h8, ?_, ?_, ?_, rfl, by omega⟩
  · rw [hm3'.regs .X9 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [hreg2.x19]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [UInt64.toNat_toBitVec, hreg2.x27 (by omega), BitVec.toNat_ofNat]
    omega
  · rw [hm3'.regs .X10 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [hreg2.x28]
  · show (s3.data.regs.getXReg .X11).toBitVec.toNat = _
    rw [hm3'.regs .X11 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    have h25' : (s2.data.regs.getXReg .X25).toNat = lw m0 := hreg2.x25 (by omega)
    rw [and_mask (by rw [UInt64.toNat_toBitVec, h25']; omega), UInt64.toNat_toBitVec, h25',
      Nat.sub_zero]

end

end NativeRustcVmArm.Wire.RdRows
