module

public import NativeRustcVmArm.Wire.RdRows.Fill

/-!
# `rd_rows`' zeros before a row of `rw > 0` words

From the loop's head at leaf `i` (`HeadA`, `b5`): no zeros (`lw = rw`), or four at a time (`b7`,
`b8`, `VecA`) then one at a time (`b9`, `b10`, `SclA`), up to the call (`CallA`): `fill_spec`.
-/

namespace NativeRustcVmArm.Wire.RdRows

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.RdRows
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable [Host] (k : Nat) (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c : Nat)

/-- The loop's head (`b5`) at leaf `i`. -/
structure HeadA (i : Nat) (rows : List (List K)) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RdRows.b5Offset)
  reg : RegA m0 i rows st.data
  kept : Kept m0 bp B c i rows ci st.data.dmem

/-- The zeros one at a time (`b10`), `t` written. -/
structure SclA (i t : Nat) (rows : List (List K)) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RdRows.b10Offset)
  z : ZA m0 bp B c i t rows ci st.data
  x8 : (st.data.regs.getXReg .X8).toBitVec = leaf m0 i + BitVec.ofNat 64 (8 * t)
  lt : t < zc m0

/-- The zeros four at a time (`b8`), `t` written. -/
structure VecA (i t : Nat) (rows : List (List K)) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RdRows.b8Offset)
  z : ZA m0 bp B c i t rows ci st.data
  x8 : (st.data.regs.getXReg .X8).toBitVec = leaf m0 i + BitVec.ofNat 64 (8 * q4 (zc m0))
  x9 : (st.data.regs.getXReg .X9).toBitVec = leaf m0 i + BitVec.ofNat 64 (8 * t + 16)
  x10 : (st.data.regs.getXReg .X10).toNat = q4 (zc m0) - t
  t4 : t % 4 = 0
  lt : t + 4 ≤ q4 (zc m0)

/-- The call reading row `i` (`b11`), its zeros written. -/
structure CallA (i : Nat) (rows : List (List K)) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RdRows.b11Offset)
  z : ZA m0 bp B c i (zc m0) rows ci st.data

variable {k m0 bp B c}

omit [Host] in
/-- The chunk's environment and the alias of its pointer. -/
theorem chunk_match [Labels] (G : Geo m0 bp B) {m : MachineData} (hfr : Frm m0 m) {a : BitVec 64}
    {sz : Nat} {S : SState} {x : Sym} {o : Int}
    (hS : S = init [(112, true), (sz, false)] (.ptr 0 0) [] [] [] [(x, 1, o)])
    (hx : x.eval (chEnv m0 m a sz) = a + BitVec.ofInt 64 o) : Match (chEnv m0 m a sz) S m := by
  subst hS
  exact match_ofMachine ⟨rfl, fun _ ↦ base_aligned G.g.st, rfl, nofun, trivial⟩
    (by rw [hfr.sp]; simp [Sym.eval]) trivial trivial trivial ⟨hx, trivial⟩

/-- **A zero** (`b10`): on, or all written. -/
theorem scl_step (hp : Placed code k) (G : Geo m0 bp B) {i t : Nat} {rows : List (List K)}
    {ci : Nat} {st : MachineState} (hI : SclA k m0 bp B c i t rows ci st) :
    Eventually (step1 Host.exe)
      (fun st' ↦ CallA k m0 bp B c i rows ci st' ∨ SclA k m0 bp B c i (t + 1) rows ci st') st := by
  have hi := hI.z.reg.lt
  have hz := hI.lt
  have hlw := G.lw64
  have hrw := hI.z.reg.rw0
  have hrl := G.rwlw
  have hzc : zc m0 = lw m0 - rw m0 := rfl
  have hwf := G.chunk_wf hi (o := 8 * t) (sz := 8) (by omega) (by omega) hI.z.reg.fr
  have hm : Match (chEnv m0 st.data (leaf m0 i + BitVec.ofNat 64 (8 * t)) 8) sclS st.data :=
    chunk_match G hI.z.reg.fr rfl (by
      show (st.data.regs.getXReg .X8).toBitVec = _
      rw [hI.x8, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero])
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) run_b10 hwf hI.pc hm fun s1 hm1 hpc1 ↦ ?_
  have hs : SameOutside st.data.dmem s1.data.dmem
      (InRange (leaf m0 i + BitVec.ofNat 64 (8 * t)) 8) := by
    have := Match.sameOutside_in hm1 hwf (r0 := 1) (o := 0) (n := 8) rfl (by omega) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  have h0 : WordAt s1.data.dmem (leaf m0 i + BitVec.ofNat 64 (8 * t)) 0 := by
    have := zero_word hm1 (r := 1) (o := 0) (sz := 8) rfl (by omega) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hfr1 : Frm m0 s1.data :=
    Frm.chunk G hi (o := 8 * t) (sz := 8) (by omega) (by omega) hI.z.reg.fr hm hm1 hwf rfl rfl hs
  have hr := regs_keep hm hm1 (rs := .X26 :: regsA) (by decide)
  have hz1 : ZA m0 bp B c i (t + 1) rows ci s1.data :=
    ⟨hI.z.reg.keep hfr1 (fun r h ↦ hr r (List.mem_cons_of_mem _ h))
      (fun h ↦ G.frame_word hi (o := 8 * t) (sz := 8) (by omega) (by omega) hs (by omega)
        (hI.z.reg.q h)),
      Kept.chunk G hI.z.kept hi (o := 8 * t) (sz := 8) (by omega) (by omega) hs,
      by rw [hr .X26 List.mem_cons_self]; exact hI.z.x26,
      zeros_snoc (zeros_chunk G hi (o := 8 * t) (sz := 8) (by omega) (le_refl _) hs hI.z.zs) h0,
      by omega⟩
  have e8 : (st.data.regs.getXReg .X8).toBitVec + BitVec.ofNat 64 8 =
      leaf m0 i + BitVec.ofNat 64 (8 * (t + 1)) := by
    rw [hI.x8, NativeRustcVm.addr_add_add]; congr 2
  have hc : (SBool.cmp .eq .W64 (.bin .add .W64 (.reg .X8) (.lit 8)) (.reg .X26)).not.eval
      (chEnv m0 st.data (leaf m0 i + BitVec.ofNat 64 (8 * t)) 8) = decide (t + 1 ≠ zc m0) := by
    simp only [SBool.eval, eq_apply, Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64,
      Env.ofMachine_regs, e8, hI.z.x26]
    rw [G.leaf_toNat (by omega), G.leaf_toNat (by omega)]
    by_cases h : t + 1 = zc m0
    · rw [decide_eq_true (by omega), decide_eq_false (by omega)]; rfl
    · rw [decide_eq_false (by omega), decide_eq_true h]; rfl
  simp only [PcOk, hc] at hpc1
  by_cases hend : t + 1 = zc m0
  · simp only [hend, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      at hpc1
    exact .done _ (.inl ⟨hpc1.trans (congrArg Host.addrOf rfl), hend ▸ hz1⟩)
  simp only [ne_eq, hend, not_false_eq_true, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.RdRows.b10Offset) NativeRustcVmArm.Vm.RdRows.label_10_at]
    at hpc1
  refine .done _ (.inr ⟨hpc1, hz1, ?_, by omega⟩)
  rw [hm1.regs .X8 _ rfl]
  simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
  exact e8

/-- **The zeros one at a time**, to the call. -/
theorem scl_loop (hp : Placed code k) (G : Geo m0 bp B) {i t : Nat} {rows : List (List K)}
    {ci : Nat} {st : MachineState} (hI : SclA k m0 bp B c i t rows ci st) :
    Eventually (step1 Host.exe) (CallA k m0 bp B c i rows ci) st := by
  refine Sym.loop (fun n st ↦ ∃ t, n = zc m0 - t ∧ SclA k m0 bp B c i t rows ci st)
    (fun n st ⟨t, hn, hI⟩ ↦ ?_) ⟨t, rfl, hI⟩
  refine Eventually.mono (scl_step hp G hI) fun st' h ↦ ?_
  rcases h with h | h
  · exact .inl h
  · exact .inr ⟨_, by have := hI.lt; omega, t + 1, rfl, h⟩

omit [Host] in
/-- Four more zeros. -/
theorem zeros4 {d : Mem 64} {a : BitVec 64} {t : Nat} (h : WordsAt d a (List.replicate t 0))
    (hw : ∀ j, j < 4 → WordAt d (a + BitVec.ofNat 64 (8 * t) + BitVec.ofNat 64 (8 * j)) 0) :
    WordsAt d a (List.replicate (t + 4) 0) := by
  have hw' : ∀ j, j < 4 → WordAt d (a + BitVec.ofNat 64 (8 * (t + j))) 0 := fun j hj ↦ by
    have := hw j hj
    rwa [NativeRustcVm.addr_add_add, show 8 * t + 8 * j = 8 * (t + j) by omega] at this
  exact zeros_snoc (zeros_snoc (zeros_snoc (zeros_snoc h (hw' 0 (by omega))) (hw' 1 (by omega)))
    (hw' 2 (by omega))) (hw' 3 (by omega))

omit [Host] in
theorem q4_le (z : Nat) : q4 z ≤ z ∧ z < q4 z + 4 ∧ q4 z % 4 = 0 := by
  unfold q4; omega

/-- **The tail of the fours** (`b9`): the call, or the zeros one at a time from `q4`. -/
theorem nine_spec (hp : Placed code k) (G : Geo m0 bp B) {i : Nat} {rows : List (List K)}
    {ci : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RdRows.b9Offset))
    (hz : ZA m0 bp B c i (q4 (zc m0)) rows ci st.data)
    (h8 : (st.data.regs.getXReg .X8).toBitVec = leaf m0 i + BitVec.ofNat 64 (8 * q4 (zc m0)))
    (h4 : 4 ≤ q4 (zc m0)) :
    Eventually (step1 Host.exe) (CallA k m0 bp B c i rows ci) st := by
  have hst := G.g.st
  have hwf := frEnv_wf hst hz.reg.fr
  have hm := frEnv_match hst hz.reg.fr
  have hlw := G.lw64
  have hq := q4_le (zc m0)
  have hzc : zc m0 = lw m0 - rw m0 := rfl
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 hwf hpc hm fun s1 hm1 hpc1 ↦ ?_
  have hd : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hfr1 : Frm m0 s1.data := Fr.ofBlock hz.reg.fr hm hm1 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have hr := regs_keep hm hm1 (rs := .X8 :: .X26 :: regsA) (by decide)
  have hz1 : ZA m0 bp B c i (q4 (zc m0)) rows ci s1.data :=
    ⟨hz.reg.keep hfr1 (fun r h ↦ hr r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
      (fun h ↦ by rw [hd]; exact hz.reg.q h), by rw [hd]; exact hz.kept,
      by rw [hr .X26 (by simp)]; exact hz.x26, by rw [hd]; exact hz.zs, hz.le⟩
  have hld : (frEnv m0 st.data).load 0 8 8 = (q4 (zc m0)).toUInt64.toBitVec :=
    load_word (by rw [Env.base_ofMachine _ _ _ rfl]; exact hz.reg.q (by omega))
  have h25 := hz.reg.x25 (by omega)
  have hc : (SBool.cmp .eq .W64 (.bin .add .W64 (.reg .X25) (.lit 1)) (.load 0 8 8)).eval
      (frEnv m0 st.data) = decide (zc m0 = q4 (zc m0)) := by
    simp only [SBool.eval, eq_apply, Sym.eval, hld, Env.ofMachine_regs]
    rw [toNat_add_lit (by rw [UInt64.toNat_toBitVec, h25]; omega) (by omega), UInt64.toNat_toBitVec,
      h25, ReaderLe.toBitVec_toUInt64_toNat (by omega)]
    by_cases h : zc m0 = q4 (zc m0)
    · rw [decide_eq_true (by omega), decide_eq_true h]
    · rw [decide_eq_false (by omega), decide_eq_false h]
  simp only [PcOk, hc] at hpc1
  by_cases he : zc m0 = q4 (zc m0)
  · simp only [decide_eq_true he, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.RdRows.b11Offset) NativeRustcVmArm.Vm.RdRows.label_11_at] at hpc1
    exact .done _ ⟨hpc1, he ▸ hz1⟩
  simp only [decide_eq_false he, Bool.false_eq_true, ↓reduceIte] at hpc1
  exact scl_loop hp G ⟨hpc1.trans (congrArg Host.addrOf rfl), hz1,
    by rw [hr .X8 (by simp)]; exact h8, by omega⟩

/-- **Four zeros** (`b8`): on, or the tail. -/
theorem vec_step (hp : Placed code k) (G : Geo m0 bp B) {i t : Nat} {rows : List (List K)}
    {ci : Nat} {st : MachineState} (hI : VecA k m0 bp B c i t rows ci st) :
    Eventually (step1 Host.exe)
      (fun st' ↦ CallA k m0 bp B c i rows ci st' ∨ VecA k m0 bp B c i (t + 4) rows ci st') st := by
  have hi := hI.z.reg.lt
  have ht4 := hI.t4
  have hlt := hI.lt
  have hlw := G.lw64
  have hrw := hI.z.reg.rw0
  have hzc : zc m0 = lw m0 - rw m0 := rfl
  have hq := q4_le (zc m0)
  have hwf := G.chunk_wf hi (o := 8 * t) (sz := 32) (by omega) (by omega) hI.z.reg.fr
  have hm : Match (chEnv m0 st.data (leaf m0 i + BitVec.ofNat 64 (8 * t)) 32) vecS st.data :=
    chunk_match G hI.z.reg.fr rfl (by
      show (st.data.regs.getXReg .X9).toBitVec =
        leaf m0 i + BitVec.ofNat 64 (8 * t) + BitVec.ofInt 64 16
      rw [hI.x9, show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl,
        NativeRustcVm.addr_add_add (leaf m0 i)])
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 hwf hI.pc hm fun s1 hm1 hpc1 ↦ ?_
  have hs : SameOutside st.data.dmem s1.data.dmem
      (InRange (leaf m0 i + BitVec.ofNat 64 (8 * t)) 32) := by
    have := Match.sameOutside_in hm1 hwf (r0 := 1) (o := 0) (n := 32) rfl (by omega) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hfr1 : Frm m0 s1.data :=
    Frm.chunk G hi (o := 8 * t) (sz := 32) (by omega) (by omega) hI.z.reg.fr hm hm1 hwf rfl rfl hs
  have hr := regs_keep hm hm1 (rs := .X8 :: .X26 :: regsA) (by decide)
  have hz1 : ZA m0 bp B c i (t + 4) rows ci s1.data :=
    ⟨hI.z.reg.keep hfr1 (fun r h ↦ hr r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
      (fun h ↦ G.frame_word hi (o := 8 * t) (sz := 32) (by omega) (by omega) hs (by omega)
        (hI.z.reg.q h)),
      Kept.chunk G hI.z.kept hi (o := 8 * t) (sz := 32) (by omega) (by omega) hs,
      by rw [hr .X26 (by simp)]; exact hI.z.x26,
      zeros4 (zeros_chunk G hi (o := 8 * t) (sz := 32) (by omega) (le_refl _) hs hI.z.zs)
        fun j hj ↦ by
          rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
            exact zero_word hm1 (r := 1) (sz := 32) rfl (by omega) (by decide),
      by omega⟩
  have h10 : ((Sym.reg .X10).eval (chEnv m0 st.data (leaf m0 i + BitVec.ofNat 64 (8 * t)) 32)).toNat =
      q4 (zc m0) - t := hI.x10
  have hc : (SBool.cmp .eq .W64 (.reg .X10) (.lit 4)).not.eval
      (chEnv m0 st.data (leaf m0 i + BitVec.ofNat 64 (8 * t)) 32) = decide (t + 4 ≠ q4 (zc m0)) := by
    simp only [SBool.eval, eq_apply]
    rw [h10, show ((Sym.lit 4).eval (chEnv m0 st.data (leaf m0 i + BitVec.ofNat 64 (8 * t)) 32)).toNat
      = 4 from rfl]
    by_cases h : t + 4 = q4 (zc m0)
    · rw [decide_eq_true (by omega), decide_eq_false (by omega)]; rfl
    · rw [decide_eq_false (by omega), decide_eq_true h]; rfl
  simp only [PcOk, hc] at hpc1
  by_cases hend : t + 4 = q4 (zc m0)
  · simp only [hend, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      at hpc1
    refine Eventually.mono (nine_spec hp G (hpc1.trans (congrArg Host.addrOf rfl)) (hend ▸ hz1)
      (by rw [hr .X8 (by simp)]; exact hI.x8) (by omega)) fun _ h ↦ .inl h
  simp only [ne_eq, hend, not_false_eq_true, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.RdRows.b8Offset) NativeRustcVmArm.Vm.RdRows.label_8_at]
    at hpc1
  refine .done _ (.inr ⟨hpc1, hz1, by rw [hr .X8 (by simp)]; exact hI.x8, ?_, ?_, by omega,
    by have := hI.t4; omega⟩)
  · rw [hm1.regs .X9 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [hI.x9, NativeRustcVm.addr_add_add (leaf m0 i),
      show 8 * t + 16 + 32 = 8 * (t + 4) + 16 by omega]
  · show (s1.data.regs.getXReg .X10).toBitVec.toNat = _
    rw [hm1.regs .X10 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [toNat_sub_lit (by rw [UInt64.toNat_toBitVec, hI.x10]; omega) (by omega),
      UInt64.toNat_toBitVec, hI.x10]
    omega

/-- **The zeros four at a time**, to the call. -/
theorem vec_loop (hp : Placed code k) (G : Geo m0 bp B) {i t : Nat} {rows : List (List K)}
    {ci : Nat} {st : MachineState} (hI : VecA k m0 bp B c i t rows ci st) :
    Eventually (step1 Host.exe) (CallA k m0 bp B c i rows ci) st := by
  refine Sym.loop (fun n st ↦ ∃ t, n = q4 (zc m0) - t ∧ VecA k m0 bp B c i t rows ci st)
    (fun n st ⟨t, hn, hI⟩ ↦ ?_) ⟨t, rfl, hI⟩
  refine Eventually.mono (vec_step hp G hI) fun st' h ↦ ?_
  rcases h with h | h
  · exact .inl h
  · exact .inr ⟨_, by have := hI.lt; omega, t + 4, rfl, h⟩

/-- **The zeros before row `i`**, from the loop's head (`b5`, `b6`, `b7`). -/
theorem fill_spec (hp : Placed code k) (G : Geo m0 bp B) {i : Nat} {rows : List (List K)}
    {ci : Nat} {st : MachineState} (hI : HeadA k m0 bp B c i rows ci st) :
    Eventually (step1 Host.exe) (CallA k m0 bp B c i rows ci) st := by
  have hst := G.g.st
  have hlw := G.lw64
  have hzc : zc m0 = lw m0 - rw m0 := rfl
  have hq := q4_le (zc m0)
  have hwf := frEnv_wf hst hI.reg.fr
  have hm := frEnv_match hst hI.reg.fr
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf hI.pc hm fun s1 hm1 hpc1 ↦ ?_
  have hd : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hfr1 : Frm m0 s1.data := Fr.ofBlock hI.reg.fr hm hm1 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have hr := regs_keep hm hm1 (rs := regsA) (by decide)
  have hreg1 : RegA m0 i rows s1.data := hI.reg.keep hfr1 hr (fun h ↦ by rw [hd]; exact hI.reg.q h)
  have h26 : (s1.data.regs.getXReg .X26).toBitVec = leaf m0 i + BitVec.ofNat 64 (8 * zc m0) := by
    rw [hm1.regs .X26 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [hI.reg.x19]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [UInt64.toNat_toBitVec, hI.reg.x28, BitVec.toNat_ofNat]
    omega
  have hc : (SBool.cmp .eq .W64 (.reg .X20) (.reg .X22)).eval (frEnv m0 st.data) =
      decide (zc m0 = 0) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs, hI.reg.x20, hI.reg.x22]
    have := G.rwlw
    have hrw' : rw m0 = m0.regs.X3.toNat := rfl
    have hlw' : lw m0 = m0.regs.X2.toNat := rfl
    by_cases h : zc m0 = 0
    · rw [decide_eq_true (by simp only [UInt64.toNat_toBitVec]; omega), decide_eq_true h]
    · rw [decide_eq_false (by simp only [UInt64.toNat_toBitVec]; omega), decide_eq_false h]
  simp only [PcOk, hc] at hpc1
  by_cases h0 : zc m0 = 0
  · simp only [h0, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.RdRows.b11Offset) NativeRustcVmArm.Vm.RdRows.label_11_at] at hpc1
    exact .done _ ⟨hpc1, hreg1, by rw [hd]; exact hI.kept, h26,
      by rw [h0]; exact NativeRustcVm.wordsAt_nil _ _, by omega⟩
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  have hz1 : ZA m0 bp B c i 0 rows ci s1.data :=
    ⟨hreg1, by rw [hd]; exact hI.kept, h26, NativeRustcVm.wordsAt_nil _ _, by omega⟩
  -- `b6`
  have hwf2 := frEnv_wf hst hfr1
  have hm2 := frEnv_match hst hfr1
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf2
    (hpc1.trans (congrArg Host.addrOf rfl)) hm2 fun s2 hm2' hpc2 ↦ ?_
  have hd2 : s2.data.dmem = s1.data.dmem := hm2'.dmem_eq hwf2 rfl
  have hfr2 : Frm m0 s2.data := Fr.ofBlock hfr1 hm2 hm2' hwf2 rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have hr2 := regs_keep hm2 hm2' (rs := .X26 :: regsA) (by decide)
  have hz2 : ZA m0 bp B c i 0 rows ci s2.data :=
    ⟨hreg1.keep hfr2 (fun r h ↦ hr2 r (List.mem_cons_of_mem _ h))
      (fun h ↦ by rw [hd2]; exact hreg1.q h),
      by rw [hd2]; exact hz1.kept, by rw [hr2 .X26 (by simp)]; exact h26,
      NativeRustcVm.wordsAt_nil _ _, by omega⟩
  have h25 := hreg1.x25 (by omega)
  have hc2 : (SBool.cmp .ult .W64 (.reg .X25) (.lit 3)).eval (frEnv m0 s1.data) =
      decide (zc m0 < 4) := by
    simp only [SBool.eval, ult_apply, Sym.eval, Env.ofMachine_regs]
    rw [UInt64.toNat_toBitVec, h25]
    by_cases h : zc m0 < 4
    · rw [decide_eq_true (by simp; omega), decide_eq_true h]
    · rw [decide_eq_false (by simp; omega), decide_eq_false h]
  simp only [PcOk, hc2] at hpc2
  by_cases h4 : zc m0 < 4
  · simp only [h4, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.RdRows.b10Offset) NativeRustcVmArm.Vm.RdRows.label_10_at] at hpc2
    refine scl_loop hp G ⟨hpc2, hz2, ?_, by omega⟩
    rw [hm2'.regs .X8 _ rfl]
    show (s1.data.regs.getXReg .X19).toBitVec = _
    rw [hreg1.x19, Nat.mul_zero, NativeRustcVm.addr_add_zero]
  simp only [h4, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc2
  -- `b7`
  have hwf3 := frEnv_wf hst hfr2
  have hm3 := frEnv_match hst hfr2
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 hwf3
    (hpc2.trans (congrArg Host.addrOf rfl)) hm3 fun s3 hm3' hpc3 ↦ ?_
  have hd3 : s3.data.dmem = s2.data.dmem := hm3'.dmem_eq hwf3 rfl
  have hfr3 : Frm m0 s3.data := Fr.ofBlock hfr2 hm3 hm3' hwf3 rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have hr3 := regs_keep hm3 hm3' (rs := .X26 :: regsA) (by decide)
  have hreg2 := hz2.reg
  simp only [PcOk] at hpc3
  refine vec_loop hp G (t := 0) ⟨hpc3.trans (congrArg Host.addrOf rfl),
    ⟨hreg2.keep hfr3 (fun r h ↦ hr3 r (List.mem_cons_of_mem _ h))
      (fun h ↦ by rw [hd3]; exact hreg2.q h),
      by rw [hd3]; exact hz2.kept, by rw [hr3 .X26 (by simp)]; exact hz2.x26,
      NativeRustcVm.wordsAt_nil _ _, by omega⟩, ?_, ?_, ?_, rfl, by omega⟩
  · rw [hm3'.regs .X8 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [hreg2.x19]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [UInt64.toNat_toBitVec, hreg2.x29 (by omega), BitVec.toNat_ofNat]
    omega
  · rw [hm3'.regs .X9 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [hreg2.x27]
  · show (s3.data.regs.getXReg .X10).toBitVec.toNat = _
    rw [hm3'.regs .X10 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    have h25' : (s2.data.regs.getXReg .X25).toNat = zc m0 - 1 := hreg2.x25 (by omega)
    have e1 : (BinOp.apply .add .W64 (s2.data.regs.getXReg .X25).toBitVec
        (BitVec.ofNat 64 1)).toNat = zc m0 := by
      rw [toNat_add_lit (by rw [UInt64.toNat_toBitVec, h25']; omega) (by omega),
        UInt64.toNat_toBitVec, h25']
      omega
    rw [and_mask (by rw [e1]; omega), e1, Nat.sub_zero]

end

end NativeRustcVmArm.Wire.RdRows
