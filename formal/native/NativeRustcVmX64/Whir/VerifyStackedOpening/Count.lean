module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.Step
public import NativeRustcVmX64.Whir.VerifyStackedOpening.Arith

/-!
# `verify_stacked_opening`: counting the placed claims, its states (x86-64)

`CB`: from the prologue to the squeeze, the frame (RSP at offset `8`), the `TState` as at the
entry, the arguments in RBP (the layout), R12 (the claims), R13 (their first), R14 (the rate),
R15 (their count), RDI, R8, the ring switch's output at the frame's offset `64`. The loop, unrolled
by two (`Head j`, before claims `2j`, `2j + 1`: their count so far in RBX); `bitAt i`: claim `i`
counted (`bit_eq`: by its column and its placement's `present` word). The environments of the
blocks (`cntEnv`) and the words they load (`col_load`, `place_load`).
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir

@[expose] public section

/-- The layout. -/
abbrev layA (m0 : MachineData) : BitVec 64 := reg m0 .rsi
/-- The column claims. -/
abbrev clA (m0 : MachineData) : BitVec 64 := reg m0 .r9

/-- Claim `i` counted. -/
def bitAt (layout : LayoutW) (cs : Array ColumnClaimW) (i : Nat) : Nat :=
  placedOf layout cs (i + 1) - placedOf layout cs i

/-- The registers `CB` names. -/
def cbRegs : List Reg64 := [.rbp, .r12, .r13, .r14, .r15, .rdi, .r8]

/-- `S` keeps the registers `rs`. -/
def keeps (rs : List Reg64) (S : SState) : Bool := rs.all fun r ↦ S.reg r == some (.reg r)

/-- **From the prologue to the squeeze.** -/
structure CB [Labels] (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (m0 st : MachineData) :
    Prop where
  ok : Ok m0 st 8
  ts : TStateAt st.dmem (tA m0) a s
  rbp : reg st .rbp = layA m0
  r12 : reg st .r12 = clA m0
  r13 : reg st .r13 = off (clA m0) 8
  r14 : reg st .r14 = reg m0 .rdx
  r15 : (reg st .r15).toNat = cs.size
  rdi : reg st .rdi = tA m0
  r8 : reg st .r8 = reg m0 .r8
  ring : NativeRustcVm.WordAt st.dmem (off (stackBelow m0 512) 64) (UInt64.ofBitVec (reg m0 .rcx))

/-- **The counting loop's head**, before claims `2j`, `2j + 1`. -/
structure Head [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (cs : Array ColumnClaimW)
    (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  cb : CB a s cs m0 st
  hj : 2 * j + 2 ≤ cs.size
  rax : reg st .rax = off (layA m0) 120
  rdx : (reg st .rdx).toNat = 2 * (cs.size / 2)
  rcx : (reg st .rcx).toNat = 2 * j
  rsi : reg st .rsi = off (clA m0) (8 + 608 * (2 * j))
  rbx : (reg st .rbx).toNat = placedOf layout cs (2 * j)

/-- The registers `Head` names besides `CB`'s. -/
def headRegs : List Reg64 := [.rax, .rdx, .rcx, .rsi, .rbx]

/-- **The pair's bits**, at `NativeRustcVmX64.Vm.VerifyStackedOpening.label_6`. -/
structure Mid [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (cs : Array ColumnClaimW)
    (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  hd : Head a s layout cs m0 j st
  r11 : (reg st .r11).toNat = bitAt layout cs (2 * j)
  r9 : (reg st .r9).toNat = bitAt layout cs (2 * j + 1)

/-- The counting loop's blocks' environment: the frame, the layout, claims `2j`, `2j + 1`. -/
abbrev cntEnv (m0 st : MachineData) (j : Nat) (ret : BitVec 64) : Env :=
  frameEnv m0 st 512 [(layA m0, 3912), (off (clA m0) (8 + 608 * (2 * j)), 1216)] (fun _ ↦ 0) ret

end

public section

theorem keeps_spec {rs : List Reg64} {S : SState} (h : keeps rs S = true) {r : Reg64} (hr : r ∈ rs) :
    S.reg r = some (.reg r) := by
  unfold keeps at h
  rw [List.all_eq_true] at h
  exact beq_iff_eq.mp (h r hr)

/-- A register a block keeps. -/
theorem kept_reg [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {rs : List Reg64} (h : keeps rs S = true) {r : Reg64} (hr : r ∈ rs) :
    reg m r = env.regs r :=
  hm.regs r _ (keeps_spec h hr)

theorem placedOf_succ' (layout : LayoutW) (cs : Array ColumnClaimW) (i : Nat) :
    placedOf layout cs (i + 1) = placedOf layout cs i + bitAt layout cs i := by
  unfold bitAt
  have : placedOf layout cs i ≤ placedOf layout cs (i + 1) := by
    unfold placedOf
    rw [List.take_add_one, List.filterMap_append, List.length_append]
    omega
  omega

theorem bitAt_eq {layout : LayoutW} {cs : Array ColumnClaimW} {i : Nat} (hi : i < cs.size) :
    bitAt layout cs i = if (cs[i].onStack layout).isSome then 1 else 0 := by
  have := placedOf_succ (layout := layout) hi
  unfold bitAt
  omega

section
variable [Labels] {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- `CB` across a block keeping its registers and writing nothing. -/
theorem CB.keep {st st' : MachineData} (hc : CB a s cs m0 st) (hok : Ok m0 st' 8)
    (hd : st'.dmem = st.dmem) (hk : ∀ r ∈ cbRegs, reg st' r = reg st r) : CB a s cs m0 st' :=
  ⟨hok, hd ▸ hc.ts, (hk .rbp (by simp [cbRegs])).trans hc.rbp,
    (hk .r12 (by simp [cbRegs])).trans hc.r12, (hk .r13 (by simp [cbRegs])).trans hc.r13,
    (hk .r14 (by simp [cbRegs])).trans hc.r14, (hk .r15 (by simp [cbRegs])) ▸ hc.r15,
    (hk .rdi (by simp [cbRegs])).trans hc.rdi, (hk .r8 (by simp [cbRegs])).trans hc.r8,
    hd ▸ hc.ring⟩

/-- `Head` across a block keeping its registers and writing nothing. -/
theorem Head.keep {j : Nat} {st st' : MachineData} (hh : Head a s layout cs m0 j st)
    (hok : Ok m0 st' 8) (hd : st'.dmem = st.dmem)
    (hk : ∀ r ∈ cbRegs ++ headRegs, reg st' r = reg st r) : Head a s layout cs m0 j st' :=
  ⟨hh.cb.keep hok hd fun r hr ↦ hk r (List.mem_append_left _ hr), hh.hj,
    (hk .rax (by simp [headRegs])).trans hh.rax, (hk .rdx (by simp [headRegs])) ▸ hh.rdx,
    (hk .rcx (by simp [headRegs])) ▸ hh.rcx, (hk .rsi (by simp [headRegs])).trans hh.rsi,
    (hk .rbx (by simp [headRegs])) ▸ hh.rbx⟩

variable (h : Parts a s layout target coefficients point slices cs z value m0)
include h

theorem Parts.n_le : cs.size ≤ 160 := h.cl.len_le

/-- The layout and the claims are apart. -/
theorem Parts.lay_cl :
    NativeRustcVm.Apart (layA m0) NativeRustcVm.Layout.layoutBytes (clA m0)
      NativeRustcVm.Layout.claimsBytes := by
  have := h.pw
  simp only [vsoInputs, BasisAddrs.regions, List.tail_cons, List.pairwise_cons, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at this
  exact this.1.2.2.1

/-- The claims in a state of the frame. -/
theorem Ok.cl {st : MachineData} {o : Nat} (hok : Ok m0 st o) :
    NativeRustcVm.Layout.ClaimsWAt st.dmem (clA m0) cs :=
  NativeRustcVm.Tables.ClaimsWAt.of_same h.cl (hok.same_in h mem_cl)

/-- The layout in a state of the frame. -/
theorem Ok.lay {st : MachineData} {o : Nat} (hok : Ok m0 st o) :
    NativeRustcVm.Layout.LayoutWAt st.dmem (layA m0) layout :=
  NativeRustcVm.Tables.LayoutWAt.of_same h.lay (hok.same_in h mem_lay)

/-- Claim `i`'s column word. -/
theorem Ok.col {st : MachineData} {o : Nat} (hok : Ok m0 st o) {i : Nat} (hi : i < cs.size) :
    NativeRustcVm.WordAt st.dmem (off (clA m0) (8 + 608 * i)) cs[i].column.toUInt64 :=
  ((hok.cl h).claims i hi).column

/-- **Claim `i` counted**, by its column and its placement's `present` word. -/
theorem Ok.bit_eq {st : MachineData} {o : Nat} (hok : Ok m0 st o) {i : Nat} (hi : i < cs.size) :
    bitAt layout cs i = if cs[i].column ≤ 157 then
      (if NativeRustcVm.wordOf st.dmem (off (layA m0) (120 + 24 * cs[i].column)) = 0 then 0 else 1)
      else 0 := by
  rw [bitAt_eq hi, onStack_isSome (hok.lay h)]
  by_cases hc : cs[i].column ≤ 157
  · have : cs[i].column < 158 := by omega
    simp only [this, decide_true, Bool.true_and, hc, ↓reduceIte]
    by_cases hw : NativeRustcVm.wordOf st.dmem (off (layA m0) (120 + 24 * cs[i].column)) = 0
    · simp [hw]
    · simp [hw]
  · have : ¬ cs[i].column < 158 := by omega
    simp [this, hc]

/-- The counting loop's environment is well formed (a pair within the claims' buffer). -/
theorem Ok.cnt_wf' {st : MachineData} {o : Nat} (hok : Ok m0 st o) {j : Nat}
    (hj : 2 * j + 2 ≤ 160) {ret : BitVec 64} : (cntEnv m0 st j ret).WF := by
  have hl := (h.ins _ mem_lay).1
  have hc := (h.ins _ mem_cl).1
  have hcb : NativeRustcVm.Layout.claimsBytes = 97288 := rfl
  have hlb : NativeRustcVm.Layout.layoutBytes = 3912 := rfl
  simp only [hcb] at hc
  simp only [hlb] at hl
  have hcn : (clA m0).toNat + 97288 ≤ 2 ^ 64 := hc.1.2
  have ho : (off (clA m0) (8 + 608 * (2 * j))).toNat = (clA m0).toNat + (8 + 608 * (2 * j)) :=
    toNat_off (by omega)
  refine hok.wf2 h hl.1.1 hl.1.2 hl.2 (mapped_off hc.1.1 (by omega))
    (by unfold NativeRustcVm.NoWrap; rw [ho]; omega) ?_ ?_
  · have : NativeRustcVm.Apart (clA m0) 97288 (stackBelow m0 verifyStackedOpeningStack)
        (verifyStackedOpeningStack + 8) := hc.2
    unfold NativeRustcVm.Apart at this ⊢
    rw [ho]
    omega
  · have := h.lay_cl
    rw [hcb, hlb] at this
    unfold NativeRustcVm.Apart at this ⊢
    simp only [layA, clA] at this ho ⊢
    rw [ho]
    omega

/-- The counting loop's environment is well formed. -/
theorem Ok.cnt_wf {st : MachineData} {o : Nat} (hok : Ok m0 st o) {j : Nat}
    (hj : 2 * j + 2 ≤ cs.size) {ret : BitVec 64} : (cntEnv m0 st j ret).WF :=
  hok.cnt_wf' h (by have := h.n_le; omega)

/-- A column of the pair, as a number. -/
theorem Ok.col_eval {st : MachineData} {o : Nat} (hok : Ok m0 st o) {j e i : Nat}
    (hi : i < cs.size) (hie : i = 2 * j + e) (ret : BitVec 64) {off' : Nat} (ho : off' = 608 * e) :
    ((Sym.load 2 off' 8).eval (cntEnv m0 st j ret)).toNat = cs[i].column := by
  subst ho hie
  show ((cntEnv m0 st j ret).load 2 (608 * e) 8).toNat = _
  have hc := ((hok.cl h).claims _ hi).column_lt
  rw [load_ofMachine (r := 2) (w := cs[2 * j + e].column.toUInt64) rfl (by
    rw [off_off, show 8 + 608 * (2 * j) + 608 * e = 8 + 608 * (2 * j + e) by omega]
    exact hok.col h hi)]
  exact u64n hc

/-- A placement's `present` word. -/
theorem Ok.place_load {st : MachineData} {o : Nat} (hok : Ok m0 st o) {j c : Nat} (hc : c ≤ 157)
    (ret : BitVec 64) :
    (cntEnv m0 st j ret).load 1 (120 + 24 * c) 8 =
      (NativeRustcVm.wordOf st.dmem (off (layA m0) (120 + 24 * c))).toBitVec := by
  have hm : NativeRustcVm.Mapped st.dmem (off (layA m0) (120 + 24 * c)) 8 := by
    have hl := (h.ins _ mem_lay).1.1.1
    exact mapped_off (Mapped.keeps hl hok.fr.kept) (by show _ ≤ 3912; omega)
  exact load_ofMachine (r := 1) rfl (NativeRustcVm.wordAt_of_mapped hm)

/-- **The `present` bit** `setne` leaves for claim `i`, its column (at most `157`) in `X`. -/
theorem Ok.bit_val {st : MachineData} {o : Nat} (hok : Ok m0 st o) {j i : Nat} (hi : i < cs.size)
    (hc : cs[i].column ≤ 157) {ret : BitVec 64} (X : Sym)
    (hX : (X.eval (cntEnv m0 st j ret)).toNat = cs[i].column) :
    ((Sym.bin .merge .W8 (.lit 0) (.ite (.not (.cmp .eq .W64
      (.loadx 1 120 (.bin .mul .W64 (t3 X) (.lit 8)) 8) (.lit 0))) (.lit 1) (.lit 0))).eval
        (cntEnv m0 st j ret)).toNat = bitAt layout cs i := by
  rw [eval_bit]
  show (BitVec.ofNat 64 (if (cntEnv m0 st j ret).load 1 (120 +
    ((Sym.bin .mul .W64 (t3 X) (.lit 8)).eval (cntEnv m0 st j ret)).toNat) 8 = 0#64 then 0 else 1)).toNat = _
  rw [toNat_idx X (by rw [hX]; omega), hX, hok.place_load h hc, hok.bit_eq h hi]
  simp only [hc, ↓reduceIte, u64_bv0]
  split <;> rfl

end

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
