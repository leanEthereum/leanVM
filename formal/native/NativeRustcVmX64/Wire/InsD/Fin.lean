module

public import NativeRustcVmX64.Wire.InsD.Arith
public import NativeRustcVmX64.Transcript.Glue

/-!
# `ins_d`'s returns (x86-64)

The places of a run (`G`: the stack's return address, the array apart from it, the words `L` the
array holds); `x` stored at `i` and returned (`store_fin`: `b4` at the end, `b14` in place); `x`
found, nothing changed (`found_fin`, `b6`).
-/

namespace NativeRustcVmX64.Wire.InsD

open NativeRustcX64 NativeRustcX64.Sym NativeRustcX64.Mem NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVm (WordAt WordsAt)
open NativeRustcVmX64.Vm.InsD

@[expose] public section

/-- The places of a run from `m`, the array holding the words `L`. -/
structure G (m : MachineData) (L : List UInt64) : Prop where
  stk : StackOk m 0
  ok : NativeRustcVm.Region.Ok m.dmem ⟨arr m, 2048⟩
  ap : NativeRustcVm.Apart (arr m) 2048 (rspOf m) 8
  len : L.length = (reg m .rsi).toNat
  lt : L.length < 256
  w : WordsAt m.dmem (arr m) L

/-- What `ins_d` reaches: its postcondition at the return address. -/
abbrev Post (m : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m ∧ rspOf st.data = rspOf m + 8#64 ∧ InsDPost m st.data

end

public section

variable {m : MachineData} {L : List UInt64}

/-- The return address is as at entry. -/
theorem G.slot (g : G m L) {s : MachineData} (hk : Kp m s) :
    ∀ i < 8, s.dmem.get? (rspOf m + BitVec.ofNat 64 i) = m.dmem.get? (rspOf m + BitVec.ofNat 64 i) :=
  fun i hi ↦ hk.so _ fun hq ↦ by
    have hs := g.stk.2.1
    have ha := arr_noWrap g.ok
    have hap := g.ap
    unfold NativeRustcVm.Apart at hap
    rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; omega),
      NativeRustcVm.toNat_add_ofNat (by omega)] at hq
    omega

theorem G.rsp_ok (g : G m L) {s : MachineData} (hk : Kp m s) :
    NativeRustcVm.Mapped s.dmem (rspOf m) 8 ∧ NativeRustcVm.NoWrap (rspOf m) 8 := by
  have hm := g.stk.2.2
  rw [show rspOf m - BitVec.ofNat 64 0 = rspOf m from BitVec.sub_zero _] at hm
  exact ⟨fun i hi ↦ hk.sv.2 _ (hm i (by omega)), g.stk.2.1⟩

theorem G.pos_rsp (g : G m L) {p : Nat} (hp : p < 256) :
    NativeRustcVm.Apart (rspOf m) 8 (pos m p) 8 := by
  have hap := g.ap
  unfold NativeRustcVm.Apart at hap ⊢
  rw [pos_toNat g.ok hp]
  omega

/-- The words of the array, with a hole at `q ≤ n`. -/
theorem G.hl_noWrap (g : G m L) {q : Nat} (hq : q ≤ L.length) (x : UInt64) :
    NativeRustcVm.NoWrap (arr m) (8 * (hl L q x).length) :=
  noWrap_words g.ok (by rw [length_hl L hq]; have := g.lt; omega)

variable [Host] {k : Nat}

/-- **`x` stored at `i` and returned** (`b4` with RAX, `b14` with RCX, at `j`): the array the
words `insD`. -/
theorem store_fin (hp : Placed code k) (g : G m L) {bj : List Directive} {j : Nat}
    (hb : bj.IsInfixAt code j) (hne : bj ≠ []) {ri : Reg64} {S' : SState}
    (hx : exec bj (init [8, 8] [(.rsp, .ptr 0 0)] [] [] [(elem (.reg ri), 1, 0)]) =
      some (S', .ret (.load 0 0 8)))
    (hmem : S'.mem = [⟨1, 0, 8, .reg .rdx⟩])
    (hrax : S'.reg .rax = some (.bin .add .W64 (.reg .rax) (.lit 1)))
    (hrsp : S'.reg .rsp = some (.ptr 0 8))
    (hkeep : keeps (init [8, 8] [(.rsp, .ptr 0 0)] [] [] [(elem (.reg ri), 1, 0)]) S' = true)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) (hk : Kp m st.data) {i : Nat}
    (hri : (reg st.data ri).toNat = i) (hn : (reg st.data .rax).toNat = L.length)
    (hi : i ≤ L.length) (hbl : Below m L i) (hab : Above m L i) {gw : UInt64}
    (hw : WordsAt st.data.dmem (arr m) (hl L i gw)) :
    Eventually (step1 Host.exe) (Post m) st := by
  have hlt := g.lt
  have hi' : i < 256 := by omega
  let env := Env.ofMachine st.data [(rspOf m, 8), (pos m i, 8)]
  have hwf : env.WF := Env.wf_of ⟨g.rsp_ok hk, pos_ok g.ok hk hi', trivial⟩
    (List.pairwise_pair.mpr (g.pos_rsp hi'))
  have hm : Match env (init [8, 8] [(.rsp, .ptr 0 0)] [] [] [(elem (.reg ri), 1, 0)]) st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨by
        show reg st.data .rsp = rspOf m + BitVec.ofInt 64 0
        rw [hk.rsp, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
      trivial trivial
      ⟨elem_alias hk (r := 1) rfl (by
        show (reg st.data ri).toNat % 256 = i
        rw [hri, Nat.mod_eq_of_lt hi']), trivial⟩
  refine Eventually.mono (Wire.ret_with (Wire.infix_of hb hne hp) hx hrsp rfl rfl hwf hm hpc
    (g.slot hk)) fun st' ⟨hpc', hrsp', hm'⟩ ↦ ⟨hpc', hrsp', ?_⟩
  have hs : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
      (NativeRustcVm.InRange (pos m i) 8) :=
    NativeRustcVmX64.Transcript.sameOutside_region hwf hm' (r := 1) rfl (by simp [hmem])
  have hwx := NativeRustcVmX64.Transcript.wordAt_write hm' (r := 1) (o := 0) (b := pos m i)
    (sz := 8) rfl (by decide) (v := .reg .rdx)
    (fun t ht ↦ by
      have := findWrite_head (r := 1) (o := 0) (v := .reg .rdx) (ws := []) ht
      rw [hmem]; exact this)
  rw [NativeRustcVm.Transcript.off_zero,
    show (Sym.reg .rdx).eval env = reg m .rdx from hk.rdx] at hwx
  obtain ⟨hins, hmap⟩ := insD_words hi hbl hab
  have hlen : (hl L i gw).length = L.length + 1 := length_hl L hi gw
  refine post_of g.len g.w (saved_trans hk.sv (Match.saved hm hm' hwf rfl hkeep))
    (fun q hq ↦ (hs q fun h ↦ hq (NativeRustcVm.InRange.of_sub (n := 2048) h g.ok.2
      (by omega))).trans (hk.so q hq)) ?_ ?_
  · rw [show reg st'.data .rax = _ from hm'.regs .rax _ hrax]
    show (BinOp.apply .add .W64 (reg st.data .rax) (BitVec.ofNat 64 1)).toNat = _
    rw [toNat_addLit, hn, hins]
    simp only [List.length_append, List.length_take, List.length_cons, List.length_drop,
      List.length_map]
    omega
  · rw [hins, hmap]
    refine wordsAt_update (C := hl L i gw) (by rw [hlen, length_hl L hi]) hw
      (g.hl_noWrap hi gw) (lo := i) (hi := i + 1) (by omega) (by rw [hlen]; omega)
      (by rw [show 8 * (i + 1 - i) = 8 by omega]; exact hs) (fun t h1 h2 ↦ ?_) (fun t _ ht ↦ ?_)
    · obtain rfl : t = i := by omega
      rw [getD_hl hi]
      simpa using hwx
    · rw [getD_hl hi, getD_hl hi]
      have : t ≠ i := by omega
      simp only [this, ↓reduceIte]

/-- **`x` found at `i`** (`b6`): the array kept, the count back. -/
theorem found_fin (hp : Placed code k) (g : G m L) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsD.b6Offset)) (hk : Kp m st.data) (hd : st.data.dmem = m.dmem)
    {i : Nat} (hi : i < L.length) (hbl : Below m L i) (hx : L[i].toNat = xv m)
    (hn : (reg st.data .rax).toNat = L.length) : Eventually (step1 Host.exe) (Post m) st :=
  Eventually.mono (Wire.ret_keep (Wire.infix_of b6_in_code (by simp [b6]) hp) run_b6 rfl rfl
    (by decide) hpc g.stk hk.rsp (fun i _ ↦ by rw [hd])) fun st' ⟨hpc', hrsp', hd', hr', hsv'⟩ ↦
    ⟨hpc', hrsp', by
      have hself : insD (lst L) (xv m) = lst L :=
        insD_self _ _ i (by simpa using hi) (fun j hj ↦ by simpa using hbl j hj (by omega))
          (by simpa using hx)
      refine post_of g.len g.w (saved_trans hk.sv hsv') (fun q _ ↦ by rw [hd', hd]) ?_ ?_
      · rw [hself, show reg st'.data .rax = reg st.data .rax from hr' .rax _ rfl, hn]
        simp
      · rw [hself, hd', hd, map_toUInt64_toNat]
        exact g.w⟩

end

end NativeRustcVmX64.Wire.InsD
