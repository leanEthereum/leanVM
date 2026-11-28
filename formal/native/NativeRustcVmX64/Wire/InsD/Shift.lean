module

public import NativeRustcVmX64.Wire.InsD.Fin

/-!
# `ins_d`'s shift (x86-64)

From `NativeRustcVmX64.Vm.InsD.label_1` (`b7`, `SixInv`), `x` to go in at `i`, the count `n`: `x` stored at once when
`i = n`; else the elements from `i` moved up one: first `(n - i) % 4` of them one by one (`b8`,
`b9`, then `b10`, `RInv`), then four at a time (`b11`, `FInv`; `b13`, `UInv`), then `x` stored at
`i` (`b14`). The array holds `hl L j g` at a shift's position `j` (`hl_step`).
-/

namespace NativeRustcVmX64.Wire.InsD

open NativeRustcX64 NativeRustcX64.Sym NativeRustcX64.Mem NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVm (WordAt WordsAt)
open NativeRustcVmX64.Vm.InsD

public section

/-! ## The array during the shift -/

theorem hl_length (L : List UInt64) (g : UInt64) : hl L L.length g = L ++ [g] := by
  simp [hl]

/-- Outside the moved window, a later position's array is the earlier one's. -/
theorem getD_hl_out {L : List UInt64} {a b : Nat} (hab : a < b) (hb : b ≤ L.length) (g : UInt64)
    {t : Nat} (ht : t ≤ a ∨ b < t) : (hl L a (L.getD a 0)).getD t 0 = (hl L b g).getD t 0 := by
  rw [getD_hl (by omega), getD_hl hb]
  rcases ht with ht | ht
  · rcases Nat.lt_or_eq_of_le ht with h | rfl
    · simp only [h, ↓reduceIte, show t < b by omega]
    · simp only [Nat.lt_irrefl, ↓reduceIte, show t < b by omega]
  · simp only [show ¬t < a by omega, show t ≠ a by omega, show ¬t < b by omega,
      show t ≠ b by omega, ↓reduceIte]

/-- Inside the moved window, each position holds the element below it. -/
theorem getD_hl_in {L : List UInt64} {a : Nat} (ha : a ≤ L.length) {t : Nat} (ht : a < t) :
    (hl L a (L.getD a 0)).getD t 0 = L.getD (t - 1) 0 := by
  rw [getD_hl ha]
  simp only [show ¬t < a by omega, show t ≠ a by omega, ↓reduceIte]

variable {m : MachineData} {L : List UInt64}

/-- The words of `hl L j g` below `j`: `L`'s. -/
theorem hl_word {d : Mem 64} {j : Nat} {g : UInt64} (hj : j ≤ L.length)
    (hw : WordsAt d (arr m) (hl L j g)) {p : Nat} (hp : p < j) : WordAt d (pos m p) (L.getD p 0) := by
  have := (wordsAt_getD.mp hw) p (by rw [length_hl L hj]; omega)
  rwa [getD_hl hj, ite_t hp] at this

/-- A word a block moved from region `r'` (element `p'`) to region `r` (element `p`). -/
theorem moved [Labels] {s s' : MachineData} {rs : List (BitVec 64 × Nat)} {S' : SState}
    (hm' : Match (Env.ofMachine s rs) S' s') {r r' p p' : Nat} (hb : rs[r]? = some (pos m p, 8))
    (hb' : rs[r']? = some (pos m p', 8))
    (hw : ∀ i < 8, findWrite r (0 + i) S'.mem = some (.load r' 0 8, i)) {w : UInt64}
    (hW : WordAt s.dmem (pos m p') w) : WordAt s'.dmem (pos m p) w := by
  have h := NativeRustcVmX64.Transcript.wordAt_write hm' (r := r) (o := 0) hb (by decide) hw
  rw [NativeRustcVm.Transcript.off_zero, eval_load, load_pos hb' hW] at h
  exact h

/-- The regions of elements `ps`, pairwise apart. -/
theorem pos_pairwise (hok : NativeRustcVm.Region.Ok m.dmem ⟨arr m, 2048⟩) {ps : List Nat}
    (hlt : ∀ p ∈ ps, p < 256) (hnd : ps.Nodup) :
    (ps.map fun p ↦ (pos m p, 8)).Pairwise fun e e' ↦ NativeRustcVm.Apart e.1 e.2 e'.1 e'.2 :=
  List.pairwise_map.mpr (hnd.imp_of_mem fun ha hb hne ↦ pos_apart hok (hlt _ ha) (hlt _ hb) hne)

/-- A change of element `p` changes only the array. -/
theorem pos_sub1 (hok : NativeRustcVm.Region.Ok m.dmem ⟨arr m, 2048⟩) {p : Nat} (hp : p < 256)
    {d d' : Mem 64} (h : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (pos m p) 8)) :
    NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (arr m) 2048) :=
  window_sub hok (lo := p) (hi := p + 1) (by omega) (by omega)
    (by rw [show 8 * (p + 1 - p) = 8 by omega]; exact h)

/-! ## The invariants -/

variable [Host] (k : Nat) (m L)

/-- At `NativeRustcVmX64.Vm.InsD.label_1` (`b7`): `x` goes in at `i`, memory as at entry. -/
structure SixInv (i : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsD.b7Offset)
  kp : Kp m st.data
  d : st.data.dmem = m.dmem
  rcx : (reg st.data .rcx).toNat = i
  rax : (reg st.data .rax).toNat = L.length
  le : i ≤ L.length
  below : Below m L i
  above : Above m L i

/-- At `NativeRustcVmX64.Vm.InsD.label_4` (`b10`): the one-by-one moves, at `j`, `c` (R9) of them left. -/
structure RInv (i j : Nat) (g : UInt64) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsD.b10Offset)
  kp : Kp m st.data
  rcx : (reg st.data .rcx).toNat = i
  rax : (reg st.data .rax).toNat = L.length
  r8 : (reg st.data .r8).toNat = L.length
  r10 : (reg st.data .r10).toNat = j
  r9 : (reg st.data .r9).toNat + (L.length - j) = (L.length - i) % 4
  pos : 0 < (reg st.data .r9).toNat
  lt : i < L.length
  jle : j ≤ L.length
  below : Below m L i
  above : Above m L i
  w : WordsAt st.data.dmem (arr m) (hl L j g)

/-- At `NativeRustcVmX64.Vm.InsD.label_5` (`b11`): the one-by-one moves done, at `j`. -/
structure FInv (i j : Nat) (g : UInt64) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsD.b11Offset)
  kp : Kp m st.data
  rcx : (reg st.data .rcx).toNat = i
  rax : (reg st.data .rax).toNat = L.length
  r8 : (reg st.data .r8).toNat = L.length
  rsi : (reg st.data .rsi).toNat = j
  rem : L.length - j = (L.length - i) % 4
  lt : i < L.length
  jle : j ≤ L.length
  below : Below m L i
  above : Above m L i
  w : WordsAt st.data.dmem (arr m) (hl L j g)

/-- At `NativeRustcVmX64.Vm.InsD.label_6` (`b13`): four at a time, at `j`. -/
structure UInv (i j : Nat) (g : UInt64) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsD.b13Offset)
  kp : Kp m st.data
  rcx : (reg st.data .rcx).toNat = i
  rax : (reg st.data .rax).toNat = L.length
  rsi : (reg st.data .rsi).toNat = j
  four : i + 4 ≤ j
  mod : (j - i) % 4 = 0
  jle : j ≤ L.length
  below : Below m L i
  above : Above m L i
  w : WordsAt st.data.dmem (arr m) (hl L j g)

variable {k m L}

/-- **A block without memory accesses** run from `regS`: the entry state kept (`Kp`), memory
kept, the registers the block's values. -/
theorem run_reg (hp : Placed code k) {ds : List Directive} {j : Nat} (hb : ds.IsInfixAt code j)
    (hne : ds ≠ []) {S' : SState} {x : Exit} (hx : exec ds regS = some (S', x))
    (hmem : S'.mem = []) (hkeep : keeps regS S' = true)
    (hregs : ∀ r ∈ [Reg64.rdi, .rdx, .rsp], S'.reg r = some (.reg r))
    (hcall : ∀ l, x ≠ .call l) {st : MachineState} (hpc : st.pc = Host.addrOf (k + j))
    (hk : Kp m st.data) {R : MachineState → Prop}
    (cont : ∀ st', Kp m st'.data → st'.data.dmem = st.data.dmem →
      (∀ r v, S'.reg r = some v → reg st'.data r = v.eval (Env.ofMachine st.data [])) →
      PcOk (Env.ofMachine st.data []) x (Host.addrOf (k + j + ds.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hwf : (Env.ofMachine st.data []).WF := Env.wf_of trivial List.Pairwise.nil
  have hm : Match (Env.ofMachine st.data []) regS st.data :=
    match_ofMachine trivial trivial trivial trivial trivial
  refine exec_at (Wire.infix_of hb hne hp) hx hwf (fun l h ↦ absurd h (hcall l)) hpc hm
    fun st' hm' hpc' ↦ ?_
  have hd := hm'.dmem_eq hwf hmem
  refine cont st' (hk.block hm hm' hwf rfl hkeep (fun r hr ↦ ⟨?_, hregs r hr⟩)
    (by rw [hd]; exact NativeRustcVm.SameOutside.refl _ _)) hd (fun r v h ↦ hm'.regs r v h) hpc'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> rfl

section
variable (hp : Placed code k) (g : G m L)
include hp g

/-- **The store** (`b14`) of `x` at `i`. -/
theorem store_spec {i : Nat} {gw : UInt64} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsD.b14Offset)) (hk : Kp m st.data) (hri : (reg st.data .rcx).toNat = i)
    (hn : (reg st.data .rax).toNat = L.length) (hi : i ≤ L.length) (hbl : Below m L i)
    (hab : Above m L i) (hw : WordsAt st.data.dmem (arr m) (hl L i gw)) :
    Eventually (step1 Host.exe) (Post m) st :=
  store_fin hp g b14_in_code (by simp [b14]) (ri := .rcx) run_b14 rfl rfl rfl (by decide) hpc hk
    hri hn hi hbl hab hw

/-- **Four moves** (`b13`): back at `NativeRustcVmX64.Vm.InsD.label_6` at `j - 4`, or the store at `i`. -/
theorem unr_step {i j : Nat} {gj : UInt64} {st : MachineState} (hI : UInv m L k i j gj st) :
    Eventually (step1 Host.exe)
      (fun st' ↦ Post m st' ∨ UInv m L k i (j - 4) (L.getD (j - 4) 0) st') st := by
  have hlt := g.lt
  have hjn := hI.jle
  have h4 := hI.four
  have hok := g.ok
  let rs : List (BitVec 64 × Nat) :=
    [(pos m (j - 1), 8), (pos m j, 8), (pos m (j - 2), 8), (pos m (j - 3), 8), (pos m (j - 4), 8)]
  let env := Env.ofMachine st.data rs
  have hwf : env.WF := Env.wf_of
    ⟨pos_ok hok hI.kp (by omega), pos_ok hok hI.kp (by omega), pos_ok hok hI.kp (by omega),
      pos_ok hok hI.kp (by omega), pos_ok hok hI.kp (by omega), trivial⟩
    (pos_pairwise hok (ps := [j - 1, j, j - 2, j - 3, j - 4])
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        not_false_eq_true, List.nodup_nil, and_true]; omega))
  have hsi : ((reg st.data .rsi)).toNat = j := hI.rsi
  have hj32 : (reg st.data .rsi).toNat < 2 ^ 32 := by omega
  have hm : Match env unrS st.data := by
    refine match_ofMachine ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ trivial trivial trivial
      ⟨elem_alias hI.kp (r := 0) rfl ?_, elem_alias hI.kp (r := 1) rfl ?_,
        elem_alias hI.kp (r := 2) rfl ?_, elem_alias hI.kp (r := 3) rfl ?_,
        elem_alias hI.kp (r := 4) rfl ?_, trivial⟩
    · show (UnOp.apply .trunc .W32 (BinOp.apply .add .W64 (reg st.data .rsi)
        (BitVec.ofNat 64 (2 ^ 64 - 1)))).toNat % 256 = j - 1
      rw [dec32 (by omega) hj32 (by omega), hsi]; omega
    · show (reg st.data .rsi).toNat % 256 = j
      rw [hsi]; omega
    · show (UnOp.apply .trunc .W32 (BinOp.apply .add .W64 (reg st.data .rsi)
        (BitVec.ofNat 64 (2 ^ 64 - 2)))).toNat % 256 = j - 2
      rw [dec32 (by omega) hj32 (by omega), hsi]; omega
    · show (UnOp.apply .trunc .W32 (BinOp.apply .add .W64 (reg st.data .rsi)
        (BitVec.ofNat 64 (2 ^ 64 - 3)))).toNat % 256 = j - 3
      rw [dec32 (by omega) hj32 (by omega), hsi]; omega
    · show (BinOp.apply .add .W64 (BitVec.ofNat 64 (2 ^ 64 - 4)) (reg st.data .rsi)).toNat % 256 =
        j - 4
      rw [dec64' (by omega) (by omega), hsi]; omega
  have hW := fun p (hpj : p < j) ↦ hl_word (m := m) hjn hI.w hpj
  refine exec_at (Wire.infix_of b13_in_code (by simp [b13]) hp) run_b13 hwf nofun hI.pc hm
    fun st' hm' hpc' ↦ ?_
  have hs : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
      (NativeRustcVm.InRange (pos m (j - 3)) 32) := by
    refine same_window hm' hwf (by rw [pos_toNat hok (by omega)]; have := arr_noWrap hok; omega)
      fun w hw b' sz hb ↦ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;>
      simp only [rs, env, Env.ofMachine, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Prod.mk.injEq] at hb <;>
      obtain ⟨rfl, rfl⟩ := hb <;>
      simp only [pos_toNat hok (show j - 3 < 256 by omega), pos_toNat hok (show j - 2 < 256 by omega),
        pos_toNat hok (show j - 1 < 256 by omega), pos_toNat hok (show j < 256 by omega)] <;>
      omega
  have hkp : Kp m st'.data := hI.kp.block hm hm' hwf rfl (by decide) (by decide)
    (window_sub hok (lo := j - 3) (hi := j + 1) (by omega) (by omega)
      (by rw [show 8 * (j + 1 - (j - 3)) = 32 by omega]; exact hs))
  have hws : WordsAt st'.data.dmem (arr m) (hl L (j - 4) (L.getD (j - 4) 0)) := by
    refine wordsAt_update (C := hl L j gj) (by rw [length_hl L hjn, length_hl L (by omega)]) hI.w
      (g.hl_noWrap hjn gj) (lo := j - 3) (hi := j + 1) (by omega) (by rw [length_hl L hjn]; omega)
      (by rw [show 8 * (j + 1 - (j - 3)) = 32 by omega]; exact hs) (fun t h1 h2 ↦ ?_)
      (fun t _ ht ↦ getD_hl_out (by omega) hjn gj (by omega))
    rw [getD_hl_in (by omega) (by omega)]
    obtain rfl | rfl | rfl | rfl : t = j - 3 ∨ t = j - 2 ∨ t = j - 1 ∨ t = j := by omega
    · rw [show j - 3 - 1 = j - 4 by omega]
      exact moved hm' (r := 3) (r' := 4) rfl rfl (by decide) (hW _ (by omega))
    · rw [show j - 2 - 1 = j - 3 by omega]
      exact moved hm' (r := 2) (r' := 3) rfl rfl (by decide) (hW _ (by omega))
    · rw [show j - 1 - 1 = j - 2 by omega]
      exact moved hm' (r := 0) (r' := 2) rfl rfl (by decide) (hW _ (by omega))
    · exact moved hm' (r := 1) (r' := 0) rfl rfl (by decide) (hW _ (by omega))
  have hrsi : (reg st'.data .rsi).toNat = j - 4 := by
    rw [show reg st'.data .rsi = BinOp.apply .add .W64 (BitVec.ofNat 64 18446744073709551612)
      (reg st.data .rsi) from hm'.regs .rsi _ rfl, toNat_add64, hsi, BitVec.toNat_ofNat]
    omega
  have hrcx : reg st'.data .rcx = reg st.data .rcx := Match.reg_eq hm hm' rfl rfl
  have hrax : reg st'.data .rax = reg st.data .rax := Match.reg_eq hm hm' rfl rfl
  have hpc2 := pc_cond hpc' (P := i < j - 4) (by
    show (!(CmpOp.apply .ult .W64 (BinOp.apply .add .W64 (BitVec.ofNat 64 18446744073709551612)
      (reg st.data .rsi)) (reg st.data .rcx)) && !(CmpOp.apply .eq .W64 (BinOp.apply .add .W64
      (BitVec.ofNat 64 18446744073709551612) (reg st.data .rsi)) (reg st.data .rcx))) = _
    rw [ult64, eq64, toNat_add64, BitVec.toNat_ofNat, hsi, hI.rcx, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    omega)
  by_cases hij : i < j - 4
  · rw [ite_t hij, hp.label NativeRustcVmX64.Vm.InsD.label_6_at] at hpc2
    exact .done _ (.inr ⟨hpc2, hkp, by rw [hrcx]; exact hI.rcx, by rw [hrax]; exact hI.rax, hrsi,
      by have := hI.mod; omega, by have := hI.mod; omega, by omega, hI.below, hI.above, hws⟩)
  · rw [ite_f hij] at hpc2
    have hji : j - 4 = i := by have := hI.mod; omega
    rw [hji] at hws
    exact Eventually.mono (store_spec hp g (hpc2.trans (congrArg Host.addrOf rfl)) hkp
      (by rw [hrcx]; exact hI.rcx) (by rw [hrax]; exact hI.rax) (by omega) hI.below hI.above hws)
      fun _ h ↦ .inl h

end

end

end NativeRustcVmX64.Wire.InsD
