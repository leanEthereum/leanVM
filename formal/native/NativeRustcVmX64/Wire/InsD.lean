module

public import NativeRustcVmX64.Wire.InsD.Rem
public import NativeRustcVmX64.Code.Vm.InsD.Names

/-!
# `ins_d` meets its contract (x86-64)

`insD_spec`: an empty list goes straight to `NativeRustcVmX64.Vm.InsD.label_1` (`b0`); else the scan (`b2`, `b3`,
`ScInv`) finds the first element at least `x`: `x` itself, the count back (`b5`, `b6`); past the
last element, `x` at the end (`b4`); else, from `NativeRustcVmX64.Vm.InsD.label_1`, the shift and the store
(`six_spec`). The elements are those of the words `L` the array holds (`exists_wordsAt`), any list
the caller gives being theirs (`post_of`).
-/

namespace NativeRustcVmX64.Wire.InsD

open NativeRustcX64 NativeRustcX64.Sym NativeRustcX64.Mem NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVm (WordAt WordsAt)
open NativeRustcVmX64.Vm.InsD

public section

variable [Host] (k : Nat) (m : MachineData) (L : List UInt64)

/-- The scan's head (`b2`) at element `i < n`. -/
structure ScInv (i : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsD.b2Offset)
  kp : Kp m st.data
  d : st.data.dmem = m.dmem
  rcx : (reg st.data .rcx).toNat = i
  rax : (reg st.data .rax).toNat = L.length
  lt : i < L.length
  below : Below m L i

variable {k m L}

section
variable (hp : Placed code k) (g : G m L) {gn : UInt64}
  (hgn : WordsAt m.dmem (arr m) (L ++ [gn]))
include hp g hgn

/-- **A step of the scan** (`b2`, then `b3` or `b5`): on past element `i`, or `x` found, or the
end, or `NativeRustcVmX64.Vm.InsD.label_1`. -/
theorem scan_step {i : Nat} {st : MachineState} (hI : ScInv k m L i st) :
    Eventually (step1 Host.exe)
      (fun st' ↦ Post m st' ∨ ScInv k m L (i + 1) st') st := by
  have hlt := g.lt
  have hiL := hI.lt
  have hi : i < 256 := by omega
  have hok := g.ok
  let env := Env.ofMachine st.data [(pos m i, 8)]
  have hwf : env.WF := Env.wf_of ⟨pos_ok hok hI.kp hi, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match env scanS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial
      ⟨elem_alias hI.kp (r := 0) rfl (by
        show (reg st.data .rcx).toNat % 256 = i
        rw [hI.rcx, Nat.mod_eq_of_lt hi]), trivial⟩
  have hLi : WordAt st.data.dmem (pos m i) L[i] := by
    rw [hI.d]
    have := (wordsAt_getD.mp g.w) i hiL
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiL, Option.getD_some] at this
  have hld : env.load 0 0 8 = L[i].toBitVec := load_pos rfl hLi
  have hx : (reg st.data .rdx).toNat = xv m := by rw [hI.kp.rdx]
  refine exec_at (Wire.infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf nofun hI.pc hm
    fun s1 hm1 hpc1 ↦ ?_
  have hd1 : s1.data.dmem = m.dmem := (hm1.dmem_eq hwf rfl).trans hI.d
  have hk1 : Kp m s1.data := hI.kp.block hm hm1 hwf rfl (by decide) (by decide)
    (by rw [hm1.dmem_eq hwf rfl]; exact NativeRustcVm.SameOutside.refl _ _)
  have er : ∀ r ∈ [Reg64.rcx, .rax], reg s1.data r = reg st.data r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Match.reg_eq hm hm1 rfl rfl
  have hpc2 := pc_cond hpc1 (P := xv m ≤ L[i].toNat) (by
    show (!(CmpOp.apply .ult .W64 (env.load 0 0 8) (reg st.data .rdx))) = _
    rw [ult64, hld, UInt64.toNat_toBitVec, hx, Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    omega)
  by_cases hge : xv m ≤ L[i].toNat
  · rw [ite_t hge, hp.label NativeRustcVmX64.Vm.InsD.label_11_at] at hpc2
    -- `b5`: found, or `NativeRustcVmX64.Vm.InsD.label_1`.
    have r5 := run_b5
    rw [after_eq run_b2] at r5
    refine exec_at (Wire.infix_of b5_in_code (by simp [b5]) hp) r5 hwf nofun hpc2 hm1
      fun s2 hm2 hpc3 ↦ ?_
    have hd2 : s2.data.dmem = m.dmem := (hm2.dmem_eq hwf rfl).trans hI.d
    have hk2 : Kp m s2.data := hI.kp.block hm hm2 hwf rfl (by decide) (by decide)
      (by rw [hm2.dmem_eq hwf rfl]; exact NativeRustcVm.SameOutside.refl _ _)
    have er2 : ∀ r ∈ [Reg64.rcx, .rax], reg s2.data r = reg st.data r := fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Match.reg_eq hm hm2 rfl rfl
    have hpc4 := pc_cond hpc3 (P := L[i].toNat ≠ xv m) (by
      show (!(CmpOp.apply .eq .W64 (env.load 0 0 8) (reg st.data .rdx))) = _
      rw [eq64, hld, UInt64.toNat_toBitVec, hx, Bool.eq_iff_iff]
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq])
    by_cases hne : L[i].toNat ≠ xv m
    · rw [ite_t hne, hp.label NativeRustcVmX64.Vm.InsD.label_1_at] at hpc4
      exact Eventually.mono (six_spec hp g hgn ⟨hpc4, hk2, hd2,
        by rw [er2 .rcx (by simp)]; exact hI.rcx, by rw [er2 .rax (by simp)]; exact hI.rax,
        le_of_lt hiL, hI.below, fun _ ↦ by omega⟩) fun _ h ↦ .inl h
    · rw [ite_f hne] at hpc4
      exact Eventually.mono (found_fin hp g (hpc4.trans (congrArg Host.addrOf rfl)) hk2 hd2 hiL
        hI.below (by omega) (by rw [er2 .rax (by simp)]; exact hI.rax)) fun _ h ↦ .inl h
  · rw [ite_f hge] at hpc2
    have hb : Below m L (i + 1) := fun j hj hjn ↦ by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
      · exact hI.below j h hjn
      · omega
    -- `b3`: the count.
    refine run_reg hp b3_in_code (by simp [b3]) run_b3 rfl (by decide) (by decide) nofun
      (hpc2.trans (congrArg Host.addrOf rfl)) hk1 fun s2 hk2 hd2 hr2 hpc3 ↦ ?_
    have hc1 : (reg s2.data .rcx).toNat = i + 1 := by
      rw [hr2 .rcx _ rfl]
      show (BinOp.apply .add .W64 (reg s1.data .rcx) (BitVec.ofNat 64 1)).toNat = _
      rw [toNat_add64, er .rcx (by simp), hI.rcx, BitVec.toNat_ofNat]
      omega
    have hrax : reg s2.data .rax = reg st.data .rax := (hr2 .rax _ rfl).trans (er .rax (by simp))
    have hpc4 := pc_cond hpc3 (P := i + 1 ≠ L.length) (by
      show (!(CmpOp.apply .eq .W64 (reg s1.data .rax)
        (BinOp.apply .add .W64 (reg s1.data .rcx) (BitVec.ofNat 64 1)))) = _
      rw [eq64, toNat_add64, er .rax (by simp), er .rcx (by simp), hI.rax, hI.rcx,
        BitVec.toNat_ofNat, Bool.eq_iff_iff]
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
      omega)
    by_cases hend : i + 1 ≠ L.length
    · rw [ite_t hend, hp.label NativeRustcVmX64.Vm.InsD.label_7_at] at hpc4
      exact .done _ (.inr ⟨hpc4, hk2, hd2.trans hd1, hc1, by rw [hrax]; exact hI.rax,
        by omega, hb⟩)
    · rw [ite_f hend] at hpc4
      -- `b4`: `x` at the end.
      have hn : L.length = i + 1 := by omega
      refine Eventually.mono (store_fin hp g b4_in_code (by simp [b4]) (ri := .rax) run_b4 rfl rfl
        rfl (by decide) (hpc4.trans (congrArg Host.addrOf rfl)) hk2
        (by rw [hrax]; exact hI.rax) (by rw [hrax]; exact hI.rax) le_rfl (by rw [hn]; exact hb)
        (fun h ↦ absurd h (Nat.lt_irrefl _)) (gw := gn) (by
          rw [hl_length, hd2, hd1]; exact hgn)) fun _ h ↦ .inl h

/-- **From the entry** (`b0`): the scan, or `NativeRustcVmX64.Vm.InsD.label_1` when the list is empty. -/
theorem entry_spec : Eventually (step1 Host.exe) (Post m) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.InsD.b0Offset)⟩ := by
  have hlt := g.lt
  refine run_reg hp b0_in_code (by simp [b0]) run_b0 rfl (by decide) (by decide) nofun rfl
    (Kp.refl m) fun s1 hk1 hd1 hr1 hpc1 ↦ ?_
  have hc0 : (reg s1.data .rcx).toNat = 0 := by rw [hr1 .rcx _ rfl]; rfl
  have hax : (reg s1.data .rax).toNat = L.length := by rw [hr1 .rax _ rfl]; exact g.len.symm
  have hpc2 := pc_cond hpc1 (P := L.length = 0) (by
    show CmpOp.apply .eq .W64 (BinOp.apply .and .W64 (reg m .rsi) (reg m .rsi))
      (BitVec.ofNat 64 0) = _
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.and_self]
    rw [eq64, BitVec.toNat_ofNat, ← g.len, Nat.zero_mod])
  have hb0 : Below m L 0 := fun _ h ↦ absurd h (Nat.not_lt_zero _)
  by_cases h0 : L.length = 0
  · rw [ite_t h0, hp.label NativeRustcVmX64.Vm.InsD.label_1_at] at hpc2
    exact six_spec hp g hgn ⟨hpc2, hk1, hd1, hc0, hax, by omega, hb0, fun h ↦ by omega⟩
  rw [ite_f h0] at hpc2
  refine run_reg hp b1_in_code (by simp [b1]) run_b1 rfl (by decide) (by decide) nofun
    (hpc2.trans (congrArg Host.addrOf rfl)) hk1 fun s2 hk2 hd2 hr2 hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  have hI : ScInv k m L 0 s2 := ⟨hpc3.trans (congrArg Host.addrOf rfl), hk2, hd2.trans hd1,
    by rw [hr2 .rcx _ rfl]; exact hc0, by rw [hr2 .rax _ rfl]; exact hax, by omega, hb0⟩
  refine Sym.loop (fun n st ↦ ∃ i, n = L.length - i ∧ ScInv k m L i st)
    (fun n st ⟨i, hn, hI⟩ ↦ ?_) ⟨0, rfl, hI⟩
  subst hn
  refine Eventually.mono (scan_step hp g hgn hI) fun st' h ↦ ?_
  rcases h with h | h
  · exact .inl h
  · exact .inr ⟨L.length - (i + 1), by have := hI.lt; omega, i + 1, rfl, h⟩

end

/-- **`ins_d` meets its contract.** -/
theorem insD_spec (hp : Placed code k) : Spec (Labels.label NativeRustcVmX64.Vm.InsD.entryLabel) InsDPre InsDPost := by
  intro m ⟨hstk, hn, hok, hdis⟩
  have hok' : NativeRustcVm.Region.Ok m.dmem ⟨arr m, 2048⟩ := hok
  obtain ⟨L, hL, hW⟩ := exists_wordsAt (reg m .rsi).toNat (arr m)
    (hok.1.mono (show _ ≤ 2048 by omega))
  obtain ⟨gn, hg⟩ := exists_wordAt (hok.1.sub (o := 8 * (reg m .rsi).toNat) (m := 8)
    (show _ ≤ 2048 by omega))
  have hW' : WordsAt m.dmem (arr m) (L ++ [gn]) :=
    NativeRustcVm.wordsAt_append_iff.mpr ⟨hW, by
      rw [hL, NativeRustcVm.wordsAt_singleton_iff]; exact hg⟩
  have hap : NativeRustcVm.Apart (reg m .rdi) 2048 (rspOf m) 8 := by
    have := (List.pairwise_pair.mp hdis)
    have hsb : stackBelow m insDStack = rspOf m := BitVec.sub_zero _
    simp only [stackR] at this
    rw [hsb] at this
    simp only [insDStack] at this
    unfold NativeRustcVm.Apart at this ⊢
    omega
  rw [show Labels.label NativeRustcVmX64.Vm.InsD.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.InsD.b0Offset) from hp.label NativeRustcVmX64.Vm.InsD.entry_at]
  exact entry_spec hp ⟨hstk, hok', hap, hL, by omega, hW⟩ hW'

end

end NativeRustcVmX64.Wire.InsD
