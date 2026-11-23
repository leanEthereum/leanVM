module

public import NativeRustcVmX64.KeccakGkr.LinearTranspose.GLoop
public import NativeRustcVmX64.Code.Vm.LinearTranspose.Names

/-!
# `linear_transpose`: the columns (x86-64)

For each column `x < 5` a zeroing block (`zB x`: `b5`, `b7`, …, RAX = 0) and a loop (`colB x`:
`b6`, `b8`, …) that sums the five lanes `x + 5 y` of `g` into the column, element by element
(`col_step`, `col_loop`); `columns` runs all five.
-/

namespace NativeRustcVmX64.KeccakGkr.LinearTranspose

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.LinearTranspose LeanVM.Parameters
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' inRange_off_iff
  Mapped.keeps bytesAt_congr inRange_off_self)

@[expose] public section

/-- Column `x`'s loop. -/
def colB : Nat → List Directive
  | 0 => b6 | 1 => b8 | 2 => b10 | 3 => b12 | _ => b14

/-- The zeroing block before column `x`'s loop. -/
def zB : Nat → List Directive
  | 0 => b5 | 1 => b7 | 2 => b9 | 3 => b11 | _ => b13

/-- Column `x`'s loop's label. -/
def colL : Nat → Label
  | 0 => NativeRustcVmX64.Vm.LinearTranspose.label_5 | 1 => NativeRustcVmX64.Vm.LinearTranspose.label_7 | 2 => NativeRustcVmX64.Vm.LinearTranspose.label_9
  | 3 => NativeRustcVmX64.Vm.LinearTranspose.label_11 | _ => NativeRustcVmX64.Vm.LinearTranspose.label_13

/-- **Column `x`'s loop head** after `z` elements. -/
structure ColHead (m0 : MachineData) (ws : Array EW) (x z : Nat) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  x_lt : x < 5
  z_lt : z < 64
  r15 : reg st .r15 = gA m0
  rbx : reg st .rbx = oA m0
  rax : reg st .rax = BitVec.ofNat 64 (16 * z)
  g : ElemsAt st.dmem (gA m0) (gF ws) 1600
  c : ElemsAt st.dmem (cA m0) (cF ws) (64 * x + z)

/-- **The columns complete**. -/
structure CDone (m0 : MachineData) (ws : Array EW) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  r15 : reg st .r15 = gA m0
  rbx : reg st .rbx = oA m0
  g : ElemsAt st.dmem (gA m0) (gF ws) 1600
  c : ElemsAt st.dmem (cA m0) (cF ws) 320

end

public section

variable {ws : Array EW} {m0 : MachineData}

theorem colB_in_code {x : Nat} (hx : x < 5) : (colB x).IsInfixAt code (49 + 18 * x) := by
  rcases (show x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  · exact b6_in_code
  · exact b8_in_code
  · exact b10_in_code
  · exact b12_in_code
  · exact b14_in_code

theorem zB_in_code {x : Nat} (hx : x < 5) : (zB x).IsInfixAt code (47 + 18 * x) := by
  rcases (show x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  · exact b5_in_code
  · exact b7_in_code
  · exact b9_in_code
  · exact b11_in_code
  · exact b13_in_code

theorem colB_label {x : Nat} (hx : x < 5) : (colB x)[0]? = some (.label (colL x)) := by
  rcases (show x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
    rfl

theorem colB_ne {x : Nat} (hx : x < 5) : colB x ≠ [] := fun h ↦ by
  have := colB_label hx; rw [h] at this; cases this

theorem zB_ne {x : Nat} (hx : x < 5) : zB x ≠ [] := by
  rcases (show x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
    simp [zB, b5, b7, b9, b11, b13]

theorem colB_length {x : Nat} (hx : x < 5) : (colB x).length = 16 := by
  rcases (show x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  exacts [NativeRustcVmX64.Vm.LinearTranspose.b6_length, NativeRustcVmX64.Vm.LinearTranspose.b8_length, NativeRustcVmX64.Vm.LinearTranspose.b10_length, NativeRustcVmX64.Vm.LinearTranspose.b12_length, NativeRustcVmX64.Vm.LinearTranspose.b14_length]

theorem zB_length {x : Nat} (hx : x < 5) : (zB x).length = 2 := by
  rcases (show x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  exacts [NativeRustcVmX64.Vm.LinearTranspose.b5_length, NativeRustcVmX64.Vm.LinearTranspose.b7_length, NativeRustcVmX64.Vm.LinearTranspose.b9_length, NativeRustcVmX64.Vm.LinearTranspose.b11_length, NativeRustcVmX64.Vm.LinearTranspose.b13_length]

/-- Column `x`'s loop run from its state. -/
theorem col_exec {x : Nat} (hx : x < 5) : ∃ S, exec (colB x) (colS x) = some (S,
    .cond (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 16) (.reg .rax)) (.lit 1024)).not (colL x)) ∧
    colOk x S = true := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := ok_cols
  have key : ∀ {b : List Directive} {e : Exit},
      (exec b (colS x)).map (fun p ↦ (colOk x p.1, p.2)) = some (true, e) →
      ∃ S, exec b (colS x) = some (S, e) ∧ colOk x S = true := by
    intro b e h
    cases he : exec b (colS x) with
    | none => rw [he] at h; cases h
    | some p =>
      rw [he] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨p.1, by rw [← h.2], h.1⟩
  rcases (show x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  exacts [key h0, key h1, key h2, key h3, key h4]

/-- The zeroing block run. -/
theorem z_exec {x : Nat} (hx : x < 5) : ∃ S, exec (zB x) regsS = some (S, .fall) ∧
    (regOk S && atoms S [.r12, .r14, .r15, .rbx] && S.reg .rax == some (.lit 0)) = true := by
  have key : ∀ b ∈ [b5, b7, b9, b11, b13], ∃ S, exec b regsS = some (S, .fall) ∧
      (regOk S && atoms S [.r12, .r14, .r15, .rbx] && S.reg .rax == some (.lit 0)) = true := by
    intro b hb
    have h := ok_zero b hb
    cases he : exec b regsS with
    | none => rw [he] at h; cases h
    | some p =>
      rw [he] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨p.1, by rw [← h.1], h.2⟩
  rcases (show x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  exacts [key b5 (by simp), key b7 (by simp), key b9 (by simp), key b11 (by simp), key b13 (by simp)]

/-- The sum chain's value. -/
theorem treeS_eval [Labels] (env : Env) (x d : Nat) :
    (treeS x d).eval env = (((env.load 0 (1024 * x + 5120 + d) 8 ^^^ env.load 0 (1024 * x + d) 8) ^^^
      env.load 0 (1024 * x + 10240 + d) 8) ^^^ env.load 0 (1024 * x + 15360 + d) 8) ^^^
        env.load 0 (1024 * x + 20480 + d) 8 := by
  simp [treeS, Sym.eval, BinOp.apply]

variable [Host] {k : Nat}

/-- **The zeroing block** before column `x`. -/
theorem col_zero (hp : Placed code k) (h : PreOk m0 ws) {x : Nat} (hx : x < 5) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + (47 + 18 * x))) (hc : Ctx m0 st.data)
    (hr15 : reg st.data .r15 = gA m0) (hrbx : reg st.data .rbx = oA m0)
    (hg : ElemsAt st.data.dmem (gA m0) (gF ws) 1600)
    (hcol : ElemsAt st.data.dmem (cA m0) (cF ws) (64 * x)) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + (49 + 18 * x)) ∧
      ColHead m0 ws x 0 s'.data) st := by
  obtain ⟨S, hS, hok⟩ := z_exec hx
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨hreg, hat⟩, hrax⟩ := hok
  refine exec_at (infix_of (zB_in_code hx) (zB_ne hx) hp) hS (Env.wf_nil _) nofun hpc
    (match_nil _) fun st' hm' hpc' ↦ ?_
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq (Env.wf_nil _) (regOk_mem hreg)
  simp only [PcOk] at hpc'
  exact .done _ ⟨hpc'.trans (by rw [zB_length hx]; congr 1; omega),
    hc.of_regs h hm' hreg (atoms_eq hm' hat (by simp)) (atoms_eq hm' hat (by simp)), hx, by decide,
    (atoms_eq hm' hat (by simp)).trans hr15, (atoms_eq hm' hat (by simp)).trans hrbx,
    hm'.regs .rax _ hrax, hd ▸ hg, by rw [hd]; exact hcol⟩

/-- **A turn of column `x`'s loop**. -/
theorem col_step (hp : Placed code k) (h : PreOk m0 ws) {x z : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + (49 + 18 * x))) (hI : ColHead m0 ws x z st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (z + 1 < 64 ∧ s'.pc = Host.addrOf (k + (49 + 18 * x)) ∧
      ColHead m0 ws x (z + 1) s'.data) ∨ (z + 1 = 64 ∧ s'.pc = Host.addrOf (k + (65 + 18 * x)) ∧
      Ctx m0 s'.data ∧ reg s'.data .r15 = gA m0 ∧ reg s'.data .rbx = oA m0 ∧
      ElemsAt s'.data.dmem (gA m0) (gF ws) 1600 ∧
      ElemsAt s'.data.dmem (cA m0) (cF ws) (64 * x + 64))) st := by
  have hx := hI.x_lt
  have hz := hI.z_lt
  have hgn := h.gn
  have hcn := h.cn
  have hgc := h.gc
  set gb := off (gA m0) (16 * z) with hgb
  set ce := off (cA m0) (1024 * x + 16 * z) with hce
  have hgbn : gb.toNat = (gA m0).toNat + 16 * z := toNat_off (by omega)
  have hcen : ce.toNat = (cA m0).toNat + (1024 * x + 16 * z) := toNat_off (by omega)
  obtain ⟨S, hS, hok⟩ := col_exec hx
  have hwf : (Env.ofMachine st.data [(gb, 20496 + 1024 * x), (ce, 16)] (fun _ ↦ 0) 0).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (mapped_off h.gM (by omega)) hI.ctx.frame.kept,
        by show gb.toNat + _ ≤ 2 ^ 64; omega⟩,
      ⟨Mapped.keeps (mapped_off h.cM (by omega)) hI.ctx.frame.kept,
        by show ce.toNat + 16 ≤ 2 ^ 64; omega⟩, trivial⟩
      (List.pairwise_pair.mpr (by show gb.toNat + _ ≤ ce.toNat ∨ ce.toNat + 16 ≤ gb.toNat; omega))
  have hm : Match (Env.ofMachine st.data [(gb, 20496 + 1024 * x), (ce, 16)] (fun _ ↦ 0) 0) (colS x)
      st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ trivial trivial trivial
      ⟨by
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
        rw [show st.data.regs.get64 .r15 = _ from hI.r15, show st.data.regs.get64 .rax = _ from hI.rax,
          show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
        rfl,
       by
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
        rw [show st.data.regs.get64 .r14 = _ from hI.ctx.r14,
          show st.data.regs.get64 .rax = _ from hI.rax,
          show (Env.ofMachine st.data [(gb, 20496 + 1024 * x), (ce, 16)] (fun _ ↦ 0) 0).base 1 = ce
            from rfl, hce, BitVec.ofInt_neg, BitVec.ofInt_natCast, ← BitVec.sub_eq_add_neg,
          show 1024 * x + 16 * z = 16 * z + 1024 * x by omega, ← NativeRustcVm.Transcript.off_off,
          off, off, BitVec.add_sub_cancel], trivial⟩
  refine exec_at (infix_of (colB_in_code hx) (colB_ne hx) hp) hS hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  unfold colOk at hok
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at hok
  obtain ⟨⟨⟨⟨hrsp, hat⟩, hrax⟩, hws⟩, hw⟩ := hok
  have hso : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem (NativeRustcVm.InRange ce 16) :=
    sameOutside_region hwf hm' (r := 1) rfl fun w hw' ↦ by
      have := hws w hw'
      exact ⟨this.1, Nat.zero_le _, this.2⟩
  have hcec : ∀ q, NativeRustcVm.InRange ce 16 q → NativeRustcVm.InRange (cA m0) 5120 q :=
    fun q hq ↦ off_in (by unfold NativeRustcVm.NoWrap; omega) (by omega) hq
  have hf' : Frame m0 64 slots 8 st'.data :=
    Frame.keep hI.ctx.frame (hm'.kept hwf) (hm'.regs .rsp _ hrsp) hso
      (fun q hq ↦ not_frame h.st h.cn h.cS (le_refl _) (hcec q hq)) (frame_nw h)
  have hreg : ∀ r ∈ [Reg64.r12, .r14, .r15, .rbx], reg st'.data r = reg st.data r :=
    fun r hr ↦ atoms_eq hm' hat hr
  have hctx : Ctx m0 st'.data :=
    ⟨hf', fun q hq ↦ by rw [hso q fun h' ↦ hq (Or.inr (Or.inl (hcec q h')))]; exact hI.ctx.same q hq,
      (hreg .r12 (by simp)).trans hI.ctx.r12, (hreg .r14 (by simp)).trans hI.ctx.r14⟩
  -- the element
  have hld : ∀ y < 5, ∀ d < 2, (Env.ofMachine st.data [(gb, 20496 + 1024 * x), (ce, 16)]
      (fun _ ↦ 0) 0).load 0 (1024 * x + 5120 * y + 8 * d) 8 =
      (if d = 0 then (gF ws (64 * (x + 5 * y) + z)).c0 else (gF ws (64 * (x + 5 * y) + z)).c1).toBitVec := by
    intro y hy d hd
    have he := NativeRustcVm.ewAt_iff.mp (hI.g (64 * (x + 5 * y) + z) (by omega))
    refine load_of_wordAt ?_
    show NativeRustcVm.WordAt st.data.dmem (off gb (1024 * x + 5120 * y + 8 * d)) _
    rw [hgb, off_off]
    rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
    · rw [ite_eq_left_iff.mpr (fun h ↦ absurd rfl h), show 16 * z + (1024 * x + 5120 * y + 8 * 0) = 16 * (64 * (x + 5 * y) + z) by
        omega]; exact he.1
    · rw [ite_eq_right_iff.mpr (fun h ↦ absurd h (by decide)), show 16 * z + (1024 * x + 5120 * y + 8 * 1) =
        16 * (64 * (x + 5 * y) + z) + 8 by omega, ← off_off]; exact he.2
  have hel := Match.ewAt_write hm' (r := 1) (o := 0) (v0 := treeS x 0) (v1 := treeS x 8) rfl
    (by decide) (fun t ht ↦ by have := (hw t ht).1; simpa using this)
    (fun t ht ↦ by have := (hw t ht).2; simpa using this)
  rw [off_zero] at hel
  simp only [treeS_eval] at hel
  rw [show 1024 * x + 5120 + 0 = 1024 * x + 5120 * 1 + 8 * 0 by omega,
    show 1024 * x + 0 = 1024 * x + 5120 * 0 + 8 * 0 by omega,
    show 1024 * x + 10240 + 0 = 1024 * x + 5120 * 2 + 8 * 0 by omega,
    show 1024 * x + 15360 + 0 = 1024 * x + 5120 * 3 + 8 * 0 by omega,
    show 1024 * x + 20480 + 0 = 1024 * x + 5120 * 4 + 8 * 0 by omega,
    show 1024 * x + 5120 + 8 = 1024 * x + 5120 * 1 + 8 * 1 by omega,
    show 1024 * x + 8 = 1024 * x + 5120 * 0 + 8 * 1 by omega,
    show 1024 * x + 10240 + 8 = 1024 * x + 5120 * 2 + 8 * 1 by omega,
    show 1024 * x + 15360 + 8 = 1024 * x + 5120 * 3 + 8 * 1 by omega,
    show 1024 * x + 20480 + 8 = 1024 * x + 5120 * 4 + 8 * 1 by omega,
    hld 0 (by decide) 0 (by decide), hld 1 (by decide) 0 (by decide), hld 2 (by decide) 0 (by decide),
    hld 3 (by decide) 0 (by decide), hld 4 (by decide) 0 (by decide),
    hld 0 (by decide) 1 (by decide), hld 1 (by decide) 1 (by decide), hld 2 (by decide) 1 (by decide),
    hld 3 (by decide) 1 (by decide), hld 4 (by decide) 1 (by decide)] at hel
  simp only [ite_true, show (1 : Nat) = 0 ↔ False by decide, ite_false] at hel
  rw [col_ew, ← cF_eq ws hz] at hel
  have hc' : ElemsAt st'.data.dmem (cA m0) (cF ws) (64 * x + (z + 1)) := by
    rw [show 64 * x + (z + 1) = (64 * x + z) + 1 by omega]
    refine ElemsAt.grow hI.c (by omega) (by
      rw [show 16 * (64 * x + z) = 1024 * x + 16 * z by omega, show 16 * 1 = 16 from rfl]
      exact hso) fun j hj ↦ ?_
    rw [show j = 0 by omega, Nat.add_zero, show 16 * (64 * x + z) = 1024 * x + 16 * z by omega]
    exact hel
  have hg' : ElemsAt st'.data.dmem (gA m0) (gF ws) 1600 :=
    hI.g.keep hso (fun q hq hq' ↦ by
      rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)] at hq
      rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hcen] at hq'
      omega) (by unfold NativeRustcVm.NoWrap; omega)
  simp only [PcOk, SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64,
    Env.ofMachine_regs] at hpc'
  rw [show st.data.regs.get64 .rax = _ from hI.rax, add_ofNat', beq_ofNat (by omega) (by omega)]
    at hpc'
  have hrax' : reg st'.data .rax = BitVec.ofNat 64 (16 * (z + 1)) := by
    rw [show reg st'.data .rax = _ from hm'.regs .rax _ hrax]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st.data.regs.get64 .rax = _ from hI.rax, add_ofNat']
    congr 1; omega
  by_cases hlast : z + 1 = 64
  · rw [decide_eq_true (show 16 + 16 * z = 1024 by omega)] at hpc'
    simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hpc'
    refine .done _ (Or.inr ⟨hlast, hpc'.trans (by rw [colB_length hx]; congr 1; omega),
      hctx, (hreg .r15 (by simp)).trans hI.r15, (hreg .rbx (by simp)).trans hI.rbx, hg', ?_⟩)
    rw [show 64 * x + 64 = 64 * x + (z + 1) by omega]; exact hc'
  · rw [decide_eq_false (show ¬16 + 16 * z = 1024 by omega)] at hpc'
    simp only [Bool.not_false, ite_true] at hpc'
    exact .done _ (Or.inl ⟨by omega, hpc'.trans (label_of_infix hp (colB_in_code hx) (colB_label hx)),
      hctx, hx, by omega, (hreg .r15 (by simp)).trans hI.r15, (hreg .rbx (by simp)).trans hI.rbx,
      hrax', hg', hc'⟩)

/-- **Column `x`'s loop**. -/
theorem col_loop (hp : Placed code k) (h : PreOk m0 ws) {x : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + (49 + 18 * x))) (hI : ColHead m0 ws x 0 st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + (65 + 18 * x)) ∧
      Ctx m0 s'.data ∧ reg s'.data .r15 = gA m0 ∧ reg s'.data .rbx = oA m0 ∧
      ElemsAt s'.data.dmem (gA m0) (gF ws) 1600 ∧
      ElemsAt s'.data.dmem (cA m0) (cF ws) (64 * x + 64)) st :=
  loop (fun n st ↦ ∃ z, n = 64 - z ∧ z < 64 ∧ st.pc = Host.addrOf (k + (49 + 18 * x)) ∧
      ColHead m0 ws x z st.data)
    (fun _ st ⟨z, hn, hz, hpc, hI⟩ ↦ (col_step hp h hpc hI).mono fun s' h' ↦ by
      rcases h' with ⟨hlt, hpc', hI'⟩ | ⟨-, hpc', hE⟩
      · exact Or.inr ⟨64 - (z + 1), by omega, z + 1, rfl, hlt, hpc', hI'⟩
      · exact Or.inl ⟨hpc', hE⟩)
    ⟨0, rfl, by decide, hpc, hI⟩

/-- **The columns**: from `g` complete to the columns complete. -/
theorem columns (hp : Placed code k) (h : PreOk m0 ws) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b5Offset)) (hI : GDone m0 ws st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b15Offset) ∧ CDone m0 ws s'.data) st :=
  loop (Q := fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b15Offset) ∧ CDone m0 ws s'.data)
    (fun n st ↦ ∃ x, n = 5 - x ∧ x < 5 ∧ st.pc = Host.addrOf (k + (47 + 18 * x)) ∧
      Ctx m0 st.data ∧ reg st.data .r15 = gA m0 ∧ reg st.data .rbx = oA m0 ∧
      ElemsAt st.data.dmem (gA m0) (gF ws) 1600 ∧ ElemsAt st.data.dmem (cA m0) (cF ws) (64 * x))
    (fun _ st ⟨x, hn, hx, hpc, hc, h15, h3, hg, hcol⟩ ↦
      (col_zero hp h hx hpc hc h15 h3 hg hcol).bind fun s1 ⟨hpc1, hI1⟩ ↦
        (col_loop hp h hpc1 hI1).mono fun s' ⟨hpc', hc', h15', h3', hg', hcol'⟩ ↦ by
          by_cases hlast : x = 4
          · subst hlast
            exact Or.inl ⟨hpc', hc', h15', h3', hg', hcol'⟩
          · exact Or.inr ⟨5 - (x + 1), by omega, x + 1, rfl, by omega,
              hpc'.trans (by congr 1; omega), hc', h15', h3', hg',
              by rw [show 64 * (x + 1) = 64 * x + 64 by omega]; exact hcol'⟩)
    ⟨0, rfl, by decide, hpc, hI.ctx, hI.r15, hI.rbx, hI.g, fun i hi ↦ absurd hi (by omega)⟩

end

end NativeRustcVmX64.KeccakGkr.LinearTranspose
