module

public import NativeVm.Code.Phase4.Step
public import NativeVm.Code.Phase4.Model

/-!
# One table's term

`termsC1_spec`: `termsC1` adds table `tix`'s weighted terms (`tableTermsStep`'s `final`) to the
running sum at `oFIN`: its constraints (`JUMP`'s, `constraintsW`) against the constraints' powers,
and its three forms (`FormW.evaluate`) on its evaluations against the forms' powers.

The blocks, inside out: `colC_spec` (a column's factor), `termLoop_spec` and `termC_spec` (a term's
value `termVal`, added to `oSUM`), `formC_spec` (a form's value, its partial sums `formPart`),
`sideC_spec` (a side's form times its power, added to `oTOT`), `jumpC_spec` (`JUMP`'s constraints
dotted with the constraints' powers, to `oTOT`); `sideC_step`, `jumpC_step` and `jumpIte_spec` run
them from a state the block reached, writing only `cvW`.
-/

@[expose] public section

namespace NativeVm.Code.P4

open Native NativeVm.Model NativeVm.Transcript NativeVm.Field LeanVM.Parameters NativeVm.Equiv

variable {env : Env} {s : QState} {E : QState → Prop}

private theorem setReg_same (s : QState) (r : Reg64) (v v' : UInt64) :
    (s.setReg r v).setReg r v' = s.setReg r v' := by
  simp [QState.setReg, Function.update_idem]

/-- `shli rax 4; add rax r`: an element's address, `rax` its index. -/
private theorem wp_shl4add {P : QState → Prop} {xs : List Stmt} {r : Reg64} {w : UInt64} {b n : Nat}
    (hr : s.reg r = wd w b) (hrr : r ≠ .rax)
    (h : WP (blk xs) (s.setReg .rax (wd w (b + 2 * n))) P E) :
    WP (blk (I (.shli .rax 4) :: I (.add .rax r) :: xs)) (s.setReg .rax n.toUInt64) P E := by
  refine wp_reg rfl (wp_reg rfl ?_)
  simp only [QState.setReg_reg, ite_true, hrr, ite_false, hr, setReg_same]
  rw [shl4_add]; exact h

/-- The factor of a column: the row's entry, a column outside the row `0`. -/
private theorem colC_tail {w : UInt64} {a k : Nat} {x acc : EW} (h13 : s.reg .r13 = wd w a)
    (hbp : s.reg .rbp = k.toUInt64) {n : Nat} (hn : s.mem (wd w a) = some n.toUInt64)
    (hA : regA s = acc) (hB : regB s = x) :
    WP (blk [emul, I (.addi .rbp 1), I (.load .rcx (wa .r13 0))]) s
      (fun s' ↦ regA s' = acc * x ∧ s'.mem = s.mem ∧ s'.reg .rbp = (k + 1).toUInt64 ∧
        s'.reg .rcx = n.toUInt64 ∧ RegsFrame (.rbp :: eRegs) s s') E := by
  refine wp_then (emulW s) fun s1 ⟨e1, e2, e3⟩ ↦ ?_
  have h13' : s1.reg .r13 = wd w a := by rw [e3 .r13 (by decide)]; exact h13
  have hbp' : s1.reg .rbp = k.toUInt64 := by rw [e3 .rbp (by decide)]; exact hbp
  fstep
  refine wp_ldA (k := 0) (by rsimp; exact h13') (by rw [Nat.add_zero, QState.setReg_mem, e2]; exact hn) ?_
  fdone
  refine ⟨?_, e2, by rw [hbp', ← toUInt64_add]; rfl, trivial,
    rf_setReg (rf_setReg (rf_mono e3) (by decide) _) (by decide) _⟩
  rw [← hA, ← hB, ← e1]
  simp only [regA, QState.setReg_reg, reduceCtorEq, ite_false]

/-- **One column** of a term: `A := A · row[col]`. -/
theorem colC_spec {w : UInt64} {a b k : Nat} {t : TermW} {row : Array EW} {acc : EW}
    (h13 : s.reg .r13 = wd w a) (h14 : s.reg .r14 = wd w b)
    (h15 : s.reg .r15 = row.size.toUInt64) (hbp : s.reg .rbp = k.toUInt64) (hk : k < t.cols.size)
    (ht : TermAt s.mem (wd w a) t) (hrow : EWArr s.mem (wd w b) row) (hrs : row.size < 2 ^ 64)
    (hA : regA s = acc) :
    WP colC s (fun s' ↦ regA s' = acc * row.getD t.cols[k] 0 ∧ s'.mem = s.mem ∧
      s'.reg .rbp = (k + 1).toUInt64 ∧ s'.reg .rcx = t.cols.size.toUInt64 ∧
      RegsFrame (.rbp :: .r11 :: .r12 :: eRegs) s s') E := by
  obtain ⟨-, ⟨-, hn⟩, hcols, -⟩ := ht
  obtain ⟨hcb, hc⟩ := hcols k hk
  rw [wd_wd, show a + (1 + k) = a + k + 1 by omega] at hc
  unfold colC
  refine wp_load (eval_idx64 h13 hbp 1) hc ?_
  apply WP.blk_cons
  by_cases hlt : t.cols[k] < row.size
  · refine wp_ite_true ?_ ?_
    · simp only [Cond.eval, Rhs.eval, QState.setReg_reg, ite_true, reduceCtorEq, ite_false, h15]
      exact decide_eq_true ((toUInt64_lt hcb hrs).mpr hlt)
    · obtain ⟨hv0, hv1⟩ := hrow _ hlt
      rw [wd_wd] at hv0 hv1
      rw [wd_wd] at hv1
      refine wp_shl4add h14 (by decide) ?_
      refine wp_ldA (k := 0) (by regw) (by rw [Nat.add_zero]; exact hv0) ?_
      refine wp_ldA (k := 1) (by regw) (by rw [Nat.add_assoc]; exact hv1) ?_
      apply WP.blk_nil
      refine WP.mono (colC_tail (by rsimp; exact h13) (by rsimp; exact hbp) hn
        (by simp only [regA, QState.setReg_reg, reduceCtorEq, ite_false]; exact hA)
        (x := row.getD t.cols[k] 0) (by
          simp only [regB, QState.setReg_reg, reduceCtorEq, ite_false, ite_true,
            Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some]))
        (fun s' ⟨e1, e2, e3, e4, e5⟩ ↦ ⟨e1, e2, e3, e4, rf_trans (l := [.rax, .r11, .r12])
          (rf_setReg (rf_setReg (rf_setReg (rf_refl _ s) (by decide) _) (by decide) _)
            (by decide) _) e5⟩) (fun _ h ↦ h)
  · refine wp_ite_false ?_ ?_
    · simp only [Cond.eval, Rhs.eval, QState.setReg_reg, ite_true, reduceCtorEq, ite_false, h15]
      exact decide_eq_false fun h ↦ hlt ((toUInt64_lt hcb hrs).mp h)
    · refine wp_reg rfl (wp_reg rfl (WP.blk_nil ?_))
      refine WP.mono (colC_tail (by rsimp; exact h13) (by rsimp; exact hbp) hn
        (by simp only [regA, QState.setReg_reg, reduceCtorEq, ite_false]; exact hA)
        (x := row.getD t.cols[k] 0) (by
          simp only [regB, QState.setReg_reg, reduceCtorEq, ite_false, ite_true,
            Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hlt),
            Option.getD_none]; rfl))
        (fun s' ⟨e1, e2, e3, e4, e5⟩ ↦ ⟨e1, e2, e3, e4, rf_trans (l := [.rax, .r11, .r12]) (rf_setReg
          (rf_setReg (rf_setReg (rf_refl _ s) (by decide) _) (by decide) _) (by decide) _) e5⟩)
        (fun _ h ↦ h)

/-- A term's value on a row: its coefficient times its columns, a column outside the row `0`. -/
def termVal (row : Array EW) (t : TermW) : EW := t.cols.foldl (fun acc i ↦ acc * row.getD i 0) t.coeff

private theorem foldl_take_succ (row : Array EW) (t : TermW) {k : Nat} (hk : k < t.cols.size) :
    (t.cols.toList.take (k + 1)).foldl (fun acc i ↦ acc * row.getD i 0) t.coeff =
      (t.cols.toList.take k).foldl (fun acc i ↦ acc * row.getD i 0) t.coeff * row.getD t.cols[k] 0 := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hk), List.foldl_append]
  simp

/-- **A term's columns**: `A := coeff · Π row[col]`. -/
theorem termLoop_spec {w : UInt64} {a b : Nat} {t : TermW} {row : Array EW}
    (h13 : s.reg .r13 = wd w a) (h14 : s.reg .r14 = wd w b)
    (h15 : s.reg .r15 = row.size.toUInt64) (ht : TermAt s.mem (wd w a) t)
    (hrow : EWArr s.mem (wd w b) row) (hrs : row.size < 2 ^ 64)
    (hbp : s.reg .rbp = 0) (hcx : s.reg .rcx = t.cols.size.toUInt64)
    (hA : regA s = t.coeff) :
    WP (.loop (.cmp .ltu .rbp (.reg .rcx)) colC) s (fun s' ↦ regA s' = termVal row t ∧
      s'.mem = s.mem ∧ RegsFrame (.rbp :: .r11 :: .r12 :: eRegs) s s') E := by
  have hn2 : t.cols.size ≤ 2 := ht.1
  refine WP.loop (fun u ↦ ∃ k ≤ t.cols.size, u.reg .rbp = k.toUInt64 ∧
      u.reg .rcx = t.cols.size.toUInt64 ∧
      regA u = (t.cols.toList.take k).foldl (fun acc i ↦ acc * row.getD i 0) t.coeff ∧
      u.mem = s.mem ∧ RegsFrame (.rbp :: .r11 :: .r12 :: eRegs) s u)
    (fun u ↦ t.cols.size - (u.reg .rbp).toNat)
    ⟨0, Nat.zero_le _, by rw [hbp]; rfl, hcx, by simpa using hA, rfl, rf_refl _ s⟩ ?_ ?_
  · rintro u ⟨k, hk, hb, hc, hA', hm, hf⟩ hcond
    have hlt : k < t.cols.size := by
      simp only [Cond.eval, Rhs.eval, hb, hc, decide_eq_true_eq] at hcond
      exact (toUInt64_lt (by omega) (by omega)).mp hcond
    refine WP.mono (colC_spec (k := k) (by rw [hf .r13 (by decide)]; exact h13)
      (by rw [hf .r14 (by decide)]; exact h14) (by rw [hf .r15 (by decide)]; exact h15) hb hlt
      (by rw [hm]; exact ht) (by rw [hm]; exact hrow) hrs hA') ?_ fun _ h ↦ h
    rintro u' ⟨e1, e2, e3, e4, e5⟩
    refine ⟨⟨k + 1, hlt, e3, e4, by rw [e1, foldl_take_succ row t hlt], e2.trans hm,
      rf_trans hf e5⟩, ?_⟩
    rw [e3, hb, Transcript.toNat_toUInt64 (by omega), Transcript.toNat_toUInt64 (by omega)]
    omega
  · rintro u ⟨k, hk, hb, hc, hA', hm, hf⟩ hcond
    have hge : k = t.cols.size := by
      simp only [Cond.eval, Rhs.eval, hb, hc, decide_eq_false_iff_not] at hcond
      exact Nat.le_antisymm hk (Nat.not_lt.mp fun h ↦ hcond ((toUInt64_lt (by omega) (by omega)).mpr h))
    subst hge
    refine ⟨?_, hm, hf⟩
    rw [hA', List.take_of_length_le (by simp), Array.foldl_toList]
    rfl

/-- The registers `termC` writes. -/
abbrev termRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13]

/-- **One term**: its value added to `oSUM`. -/
theorem termC_spec (hrdi : s.reg .rdi = env.ctx)
    (hctx : s.mem (wd env.ctx ctxWork) = some (wd env.work 0)) {a b : Nat} {t : TermW}
    {row : Array EW} {sum : EW} (h13 : s.reg .r13 = wd env.work a)
    (h14 : s.reg .r14 = wd env.work b) (h15 : s.reg .r15 = row.size.toUInt64)
    (ht : TermAt s.mem (wd env.work a) t) (hrow : EWArr s.mem (wd env.work b) row)
    (hrs : row.size < 2 ^ 64) (hsum : EWAt s.mem (wd env.work oSUM) sum) :
    WP termC s (fun s' ↦ EWAt s'.mem (wd env.work oSUM) (sum + termVal row t) ∧
      Wr env.work (fun k ↦ oSUM ≤ k ∧ k < oSUM + 2) s s' ∧
      s'.reg .r13 = wd env.work (a + 5) ∧ s'.reg .rsi = s.reg .rsi - 1 ∧
      RegsFrame termRegs s s') E := by
  have hc0 : s.mem (wd env.work (a + 3)) = some t.coeff.c0 := by
    have := ht.2.2.2.1; rwa [wd_wd] at this
  have hc1 : s.mem (wd env.work (a + 4)) = some t.coeff.c1 := by
    have := ht.2.2.2.2; rwa [wd_wd, wd_wd] at this
  have hn : s.mem (wd env.work (a + 0)) = some t.cols.size.toUInt64 := ht.2.1.2
  obtain ⟨hs0, hs1⟩ := hsum
  rw [wd_wd] at hs1
  unfold termC
  refine wp_ldA h13 hc0 ?_
  refine wp_ldA (by regw) (by rw [QState.setReg_mem]; exact hc1) ?_
  fstep
  refine wp_ldA (by regw) (by rw [QState.setReg_mem]; exact hn) ?_
  apply WP.blk_cons
  refine WP.mono (termLoop_spec (a := a) (b := b) (t := t) (row := row) (by regw) (by regw)
    (by regw) ht hrow hrs (by regw) (by regw)
    (by simp only [regA, QState.setReg_reg, reduceCtorEq, ite_false, ite_true])) ?_ fun _ h ↦ h
  rintro u ⟨e1, e2, e3⟩
  simp only [QState.setReg_mem] at e2
  have hrdi' : u.reg .rdi = env.ctx := by rw [e3 .rdi (by decide)]; regw
  have hctx' : u.mem (wd env.ctx ctxWork) = some (wd env.work 0) := by rw [e2]; exact hctx
  have hs0' : u.mem (wd env.work 52770) = some sum.c0 := by rw [e2]; exact hs0
  have hs1' : u.mem (wd env.work 52771) = some sum.c1 := by rw [e2]; exact hs1
  have h13' : u.reg .r13 = wd env.work a := by rw [e3 .r13 (by decide)]; regw
  have h9 : u.reg .r9 = (termVal row t).c0 := congrArg EW.c0 e1
  have h10 : u.reg .r10 = (termVal row t).c1 := congrArg EW.c1 e1
  have hsi : u.reg .rsi = s.reg .rsi := by rw [e3 .rsi (by decide)]; regw
  have hd : ∀ k, oSUM ≤ k → k < oSUM + 2 → (u.mem (wd env.work k)).isSome := fun k h1 h2 ↦ by
    simp only [oSUM, oS] at h1 h2
    obtain rfl | rfl : k = 52770 ∨ k = 52771 := by omega
    · rw [hs0']; rfl
    · rw [hs1']; rfl
  have hfu : RegsFrame termRegs s u :=
    rf_trans (l := [.r9, .r10, .rbp, .rcx]) (rf_setReg (rf_setReg (rf_setReg (rf_setReg
      (rf_refl _ s) (by decide) _) (by decide) _) (by decide) _) (by decide) _) e3
  have hum : u.mem = s.mem := e2
  clear e1 e2 e3 hs0 hs1 hc0 hc1 hn hctx
  wst; wst; wst; wst; wst; wst; wst; wst; wst
  wdone
  simp only [h9, h10, hsi]
  refine ⟨?_, ?_, rfl, rfl, ?_⟩
  · refine EWAt.of ?_ ?_ <;> memw <;> rfl
  · wr_tac
    exact fun x _ ↦ congrFun hum x
  · repeat (first
      | with_reducible refine rf_setMem ?_ _ _
      | with_reducible refine rf_setReg ?_ (by decide) _)
    exact hfu

/-- The words of a store set `W` kept, the region `[p, p + n)` apart from it. -/
private theorem Wr.same {w : UInt64} {W : Nat → Prop} {s s' : QState} (h : Wr w W s s') {p n : Nat}
    (hp : p + n ≤ 2 ^ 61) (hW : ∀ k, W k → (k < p ∨ p + n ≤ k) ∧ k < 2 ^ 61) :
    Same s.mem s'.mem (wd w p) n := fun k hk ↦ by
  rw [wd_wd]
  refine h _ fun j hj e ↦ ?_
  have := hW j hj
  rw [wd_inj (by omega) this.2] at e
  omega

/-- The context's word kept by stores to the working area below `dataEnd`. -/
private theorem Wr.ctx (h4 : Env4 env) {W : Nat → Prop} {s s' : QState} (h : Wr env.work W s s')
    (hW : ∀ k, W k → k < 85438) : s'.mem (wd env.ctx ctxWork) = s.mem (wd env.ctx ctxWork) :=
  h _ fun k hk e ↦ h4.ctxNe k ctxWork (by rw [dataEnd_val]; exact hW k hk) (by decide) e.symm

/-- A form's partial sum: its first `k` terms' values. -/
def formPart (row : Array EW) (f : FormW) (k : Nat) : EW :=
  (f.toList.take k).foldl (fun acc t ↦ acc + termVal row t) 0

private theorem formPart_succ (row : Array EW) (f : FormW) {k : Nat} (hk : k < f.size) :
    formPart row f (k + 1) = formPart row f k + termVal row f[k] := by
  unfold formPart
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hk), List.foldl_append]
  simp

private theorem formPart_size (row : Array EW) (f : FormW) : formPart row f f.size = f.evaluate row := by
  rw [formPart, List.take_of_length_le (by simp), Array.foldl_toList, FormW.evaluate, sumE,
    Array.foldl_map]
  rfl

/-- **A form's value** on a row: the form at `r13`, the row at `r14`, `r15` wide. -/
theorem formC_spec (h4 : Env4 env) (hrdi : s.reg .rdi = env.ctx)
    (hctx : s.mem (wd env.ctx ctxWork) = some (wd env.work 0)) {a b : Nat} {f : FormW}
    {row : Array EW} (h13 : s.reg .r13 = wd env.work a)
    (h14 : s.reg .r14 = wd env.work b) (h15 : s.reg .r15 = row.size.toUInt64)
    (hf : FormAt s.mem (wd env.work a) f) (hrow : EWArr s.mem (wd env.work b) row)
    (ha : a + 741 ≤ 52770) (hb : b + 2 * row.size ≤ 52770)
    (hd : ∀ k, oSUM ≤ k → k < oSUM + 2 → (s.mem (wd env.work k)).isSome) :
    WP formC s (fun s' ↦ regA s' = f.evaluate row ∧
      Wr env.work (fun k ↦ oSUM ≤ k ∧ k < oSUM + 2) s s' ∧ RegsFrame termRegs s s') E := by
  obtain ⟨hfc, ⟨hnb, hn⟩, hterms⟩ := hf
  have hfc' : f.size ≤ 148 := hfc
  have hn0 : s.mem (wd env.work (a + 0)) = some f.size.toUInt64 := hn
  unfold formC
  refine wp_ldA h13 hn0 ?_
  wst; wst; wst; wst
  apply WP.blk_cons
  have hW : ∀ k, (oSUM ≤ k ∧ k < oSUM + 2) → k < 85438 := fun k hk ↦ by
    simp only [oSUM, oS] at hk; omega
  refine WP.loop (fun u ↦ ∃ k ≤ f.size, u.reg .rsi = (f.size - k).toUInt64 ∧
      u.reg .r13 = wd env.work (a + 1 + 5 * k) ∧ EWAt u.mem (wd env.work oSUM) (formPart row f k) ∧
      Wr env.work (fun k ↦ oSUM ≤ k ∧ k < oSUM + 2) s u ∧ RegsFrame termRegs s u)
    (fun u ↦ (u.reg .rsi).toNat) ⟨0, Nat.zero_le _, by rsimp; rfl, by rsimp,
      EWAt.of (by memw; rfl) (by memw; rfl), by wr_tac, by rfw⟩ ?_ ?_
  · rintro u ⟨k, hk, hsi, h13', hsum, hwr, hfr⟩ hcond
    have hlt : k < f.size := (test_count hsi (by omega)).mp hcond
    have hsame : Same s.mem u.mem (wd env.work (a + 1 + 5 * k)) 5 :=
      hwr.same (by omega) fun j hj ↦ by simp only [oSUM, oS] at hj; omega
    have hsr : Same s.mem u.mem (wd env.work b) (2 * row.size) :=
      hwr.same (by omega) fun j hj ↦ by simp only [oSUM, oS] at hj; omega
    have ht : TermAt s.mem (wd env.work (a + 1 + 5 * k)) f[k] := by
      have := hterms k hlt
      rwa [wd_wd, show a + (1 + termWords * k) = a + 1 + 5 * k by unfold termWords monoCap; omega] at this
    refine WP.mono (termC_spec (by rw [hfr .rdi (by decide)]; exact hrdi)
      (by rw [hwr.ctx h4 hW]; exact hctx) h13' (by rw [hfr .r14 (by decide)]; exact h14)
      (by rw [hfr .r15 (by decide)]; exact h15) (ht.congr hsame) (hrow.congr hsr (by omega))
      (by omega) hsum) ?_ fun _ h ↦ h
    rintro u' ⟨e1, e2, e3, e4, e5⟩
    refine ⟨⟨k + 1, hlt, ?_, ?_, by rw [formPart_succ row f hlt]; exact e1, hwr.trans e2,
      rf_trans hfr e5⟩, ?_⟩
    · rw [e4, hsi]; exact natSub_toUInt64 hlt
    · rw [e3]; congr 1
    · rw [e4, hsi, show (f.size - k).toUInt64 - 1 = (f.size - (k + 1)).toUInt64 from
        natSub_toUInt64 hlt, Transcript.toNat_toUInt64 (by omega),
        Transcript.toNat_toUInt64 (by omega)]
      omega
  · rintro u ⟨k, hk, hsi, -, hsum, hwr, hfr⟩ hcond
    have hge : k = f.size := by
      have := (test_count hsi (by omega)).not.mp (by simpa using hcond)
      omega
    subst hge
    obtain ⟨hs0, hs1⟩ := hsum
    have hrdi' : u.reg .rdi = env.ctx := by rw [hfr .rdi (by decide)]; exact hrdi
    have hctx' : u.mem (wd env.ctx ctxWork) = some (wd env.work 0) := by
      rw [hwr.ctx h4 hW]; exact hctx
    wnorm at hs0 hs1
    wst; wst; wst
    wdone
    refine ⟨?_, by wr_tac; exact hwr, rf_setReg (rf_setReg (rf_setReg hfr (by decide) _)
      (by decide) _) (by decide) _⟩
    rw [← formPart_size]
    simp only [regA, QState.setReg_reg, reduceCtorEq, ite_false, ite_true]

/-- A frame of every register but `rdi` and `rsp`. -/
private theorem rf_arr {s t : QState} (h1 : t.reg .rdi = s.reg .rdi) (h2 : t.reg .rsp = s.reg .rsp) :
    RegsFrame arrRegs s t := fun r hr ↦ by
  cases r <;> first | exact h1 | exact h2 | exact absurd (by decide) hr

/-- **Side `j`'s form** on the table's evaluations, times `p`, added to `oTOT`. -/
theorem sideC_spec (h4 : Env4 env) (hrdi : s.reg .rdi = env.ctx)
    (hctx : s.mem (wd env.ctx ctxWork) = some (wd env.work 0)) (hws : WS env s)
    {tix : Nat} (ht : tix < 6) {j : Nat} (hj : j < 3)
    (hix : s.mem (wd env.work oTIX) = some tix.toUInt64)
    (hfp : s.mem (wd env.work oFPTR) = some (wd env.work (oB + formsStride * tix)))
    (hep : s.mem (wd env.work oEPTR) = some (wd env.work (oE + eS * tix)))
    (hwid : s.mem (wd env.work (oWID + tix)) = some (widths.getD tix 0).toUInt64)
    {f : FormW} (hf : FormAt s.mem (wd env.work (oB + formsStride * tix + fW * j)) f)
    {evals : Array EW} (hes : evals.size = widths.getD tix 0)
    (hea : EWArr s.mem (wd env.work (oE + eS * tix + evOff + 1)) evals)
    {p : EW} (hp0 : s.mem (wd env.work (oXP + 4 + 2 * j)) = some p.c0)
    (hp1 : s.mem (wd env.work (oXP + 5 + 2 * j)) = some p.c1)
    {tot : EW} (htot : EWAt s.mem (wd env.work oTOT) tot) :
    WP (sideC j) s (fun s' ↦ EWAt s'.mem (wd env.work oTOT) (tot + f.evaluate evals * p) ∧
      Wr env.work (fun k ↦ oTOT ≤ k ∧ k < oTOT + 4) s s' ∧ RegsFrame arrRegs s s') E := by
  have hw6 : widths.getD tix 0 ≤ 92 := by
    unfold widths; interval_cases tix <;> decide
  unfold sideC
  wnorm at hix hfp hep
  wst; wst; wst; wst; wst; wst
  refine wp_load (eval_idx64 (j := 0) (by regw) (by regw) oWID)
    (by rw [QState.setReg_mem, QState.setReg_mem, QState.setReg_mem, QState.setReg_mem,
      QState.setReg_mem, QState.setReg_mem, show 0 + tix + oWID = oWID + tix by omega]; exact hwid) ?_
  apply WP.blk_cons
  refine WP.mono (formC_spec h4 (by regw) (by simp only [QState.setReg_mem]; exact hctx)
    (a := oB + formsStride * tix + fW * j) (b := oE + eS * tix + evOff + 1) (f := f) (row := evals)
    (by rsimp; congr 1) (by rsimp; congr 1) (by rsimp; rw [hes]) hf hea
    (by simp only [oB, formsStride, fW]; omega) (by simp only [oE, eS, evOff]; omega)
    fun k h1 h2 ↦ hws k (by simp only [oSUM, oS] at h1; omega) (by simp only [oSUM, oS] at h2; omega))
    ?_ fun _ h ↦ h
  rintro u ⟨e1, e2, e3⟩
  have hW : ∀ k, (oSUM ≤ k ∧ k < oSUM + 2) → k < 85438 := fun k hk ↦ by
    simp only [oSUM, oS] at hk; omega
  have hkeep : ∀ i, i < 52770 → u.mem (wd env.work i) = s.mem (wd env.work i) := fun i hi ↦
    e2.word (by omega) fun k hk ↦ by simp only [oSUM, oS] at hk; omega
  have hrdi' : u.reg .rdi = env.ctx := by rw [e3 .rdi (by decide)]; regw
  have hctx' : u.mem (wd env.ctx ctxWork) = some (wd env.work 0) := by
    rw [e2.ctx h4 hW]; exact hctx
  have hp0' : u.mem (wd env.work (0 + (oXP + 4 + 2 * j))) = some p.c0 := by
    rw [Nat.zero_add, hkeep _ (by simp only [oXP, oS]; omega)]; exact hp0
  have hp1' : u.mem (wd env.work (0 + (oXP + 5 + 2 * j))) = some p.c1 := by
    rw [Nat.zero_add, hkeep _ (by simp only [oXP, oS]; omega)]; exact hp1
  obtain ⟨ht0, ht1⟩ := htot
  rw [wd_wd] at ht1
  wnorm at ht0 ht1
  have ht0' : u.mem (wd env.work 52768) = some tot.c0 := by rw [hkeep _ (by omega)]; exact ht0
  have ht1' : u.mem (wd env.work 52769) = some tot.c1 := by rw [hkeep _ (by omega)]; exact ht1
  wst
  refine wp_ldA (by regw) (by rw [QState.setReg_mem]; exact hp0') ?_
  refine wp_ldA (by regw) (by rw [QState.setReg_mem, QState.setReg_mem]; exact hp1') ?_
  refine wp_then (emulW _) fun v ⟨f1, f2, f3⟩ ↦ ?_
  simp only [QState.setReg_mem] at f2
  have hbp : v.reg .rbp = wd env.work 0 := by rw [f3 .rbp (by decide)]; regw
  have ht0'' : v.mem (wd env.work 52768) = some tot.c0 := by rw [f2]; exact ht0'
  have ht1'' : v.mem (wd env.work 52769) = some tot.c1 := by rw [f2]; exact ht1'
  have hd : ∀ k, oTOT ≤ k → k < oTOT + 2 → (v.mem (wd env.work k)).isSome := fun k h1 h2 ↦ by
    simp only [oTOT, oS] at h1 h2
    obtain rfl | rfl : k = 52768 ∨ k = 52769 := by omega
    · rw [ht0'']; rfl
    · rw [ht1'']; rfl
  have hv : regA v = f.evaluate evals * p := by
    rw [f1, ← e1]
    simp only [regA, regB, QState.setReg_reg, reduceCtorEq, ite_false, ite_true]
  have h9 : v.reg .r9 = (f.evaluate evals * p).c0 := congrArg EW.c0 hv
  have h10 : v.reg .r10 = (f.evaluate evals * p).c1 := congrArg EW.c1 hv
  have hsp : v.reg .rsp = s.reg .rsp := by
    rw [f3 .rsp (by decide)]; rsimp; rw [e3 .rsp (by decide)]; rsimp
  have hdi : v.reg .rdi = s.reg .rdi := by
    rw [f3 .rdi (by decide)]; rsimp; rw [hrdi', hrdi]
  have hvm : ∀ i, i < 52770 → v.mem (wd env.work i) = s.mem (wd env.work i) := fun i hi ↦ by
    rw [f2]; exact hkeep i hi
  have hvw : Wr env.work (fun k ↦ oTOT ≤ k ∧ k < oTOT + 4) s v := fun x hx ↦ by
    rw [f2]
    refine e2 x fun k hk ↦ hx k ⟨?_, ?_⟩ <;> simp only [oSUM, oTOT, oS] at hk ⊢ <;> omega
  clear f1 f2 f3 e1 e2 e3 hkeep hp0' hp1' ht0' ht1' hp0 hp1 ht0 ht1 hctx' hrdi' hwid hf hea hfp hep hix
  wst; wst; wst; wst; wst; wst
  wdone
  simp only [h9, h10]
  refine ⟨?_, ?_, ?_⟩
  · refine EWAt.of ?_ ?_ <;> memw <;> rfl
  · wr_tac; exact hvw
  · refine rf_arr ?_ ?_ <;> rsimp
    · exact hdi
    · exact hsp

open LeanVM.Protocol.Verifier in
/-- `JUMP`'s constraints: `b + v_cond · w`, `v_cond · (b + 1)`. -/
private theorem constraintsW_jump (evals : Array EW) : constraintsW 4 evals =
    #[evals.getD 13 0 + evals.getD 5 0 * evals.getD 12 0, evals.getD 5 0 * (evals.getD 13 0 + 1)] := by
  have h5 : columnIndexByName jumpColumns "v_cond" = 5 := by decide
  have h12 : columnIndexByName jumpColumns "w" = 12 := by decide
  have h13 : columnIndexByName jumpColumns "b" = 13 := by decide
  simp only [constraintsW, opJump, ↓reduceIte, h5, h12, h13]

private theorem ew_add_one (x : EW) : (⟨x.c0 ^^^ 1, x.c1⟩ : EW) = x + 1 := by
  show _ = EW.add x 1
  simp only [EW.add]
  congr 1
  exact (UInt64.xor_zero (a := x.c1)).symm

private theorem ew_mul_comm (x y : EW) : x * y = y * x :=
  EW.toE_injective (by rw [EW.toE_mul, EW.toE_mul, mul_comm])

private theorem getD_eq {xs : Array EW} {i : Nat} (h : i < xs.size) : xs.getD i 0 = xs[i] := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, Option.getD_some]

/-- **`JUMP`'s constraints** dotted with the constraints' powers, to `oTOT`. -/
theorem jumpC_spec (h4 : Env4 env) (hrdi : s.reg .rdi = env.ctx)
    (hctx : s.mem (wd env.ctx ctxWork) = some (wd env.work 0))
    (hep : s.mem (wd env.work oEPTR) = some (wd env.work (oE + eS * 4)))
    {xi : EW} (hxp : EWArr s.mem (wd env.work oXP) (powers xi 5))
    {evals : Array EW} (hes : evals.size = 14)
    (hea : EWArr s.mem (wd env.work (oE + eS * 4 + evOff + 1)) evals)
    (hd : ∀ k, oCV ≤ k → k < oCV + 6 → (s.mem (wd env.work k)).isSome) :
    WP jumpC s (fun s' ↦ EWAt s'.mem (wd env.work oTOT) (dot (cpOf xi) (constraintsW 4 evals)) ∧
      Wr env.work (fun k ↦ oCV ≤ k ∧ k < oCV + 6) s s' ∧ RegsFrame arrRegs s s') E := by
  obtain ⟨c0, c1⟩ := hea 5 (by omega)
  obtain ⟨w0, w1⟩ := hea 12 (by omega)
  obtain ⟨b0, b1⟩ := hea 13 (by omega)
  wnorm at hep c0 c1 w0 w1 b0 b1
  unfold jumpC
  simp only [cCond, cInv, cFlag]
  wst; wst; wst; wst; wst; wst
  refine wp_then (emulW _) fun v ⟨f1, f2, f3⟩ ↦ ?_
  simp only [QState.setReg_mem] at f2
  rw [← f2] at c0 c1 b0 b1 hctx hxp
  have hv1 : regA v = evals[5] * evals[12] := by
    rw [f1]; simp only [regA, regB, QState.setReg_reg, reduceCtorEq, ite_false, ite_true]
  have h9 : v.reg .r9 = (evals[5] * evals[12]).c0 := congrArg EW.c0 hv1
  have h10 : v.reg .r10 = (evals[5] * evals[12]).c1 := congrArg EW.c1 hv1
  have hbp : v.reg .rbp = wd env.work 0 := by rw [f3 .rbp (by decide)]; regw
  have h14 : v.reg .r14 = wd env.work 15077 := by rw [f3 .r14 (by decide)]; regw
  have hdi : v.reg .rdi = s.reg .rdi := by rw [f3 .rdi (by decide)]; rsimp
  have hsp : v.reg .rsp = s.reg .rsp := by rw [f3 .rsp (by decide)]; rsimp
  have hdv : ∀ k, oCV ≤ k → k < oCV + 6 → (v.mem (wd env.work k)).isSome := fun k h1 h2 ↦ by
    rw [f2]; exact hd k h1 h2
  have hwv : Wr env.work (fun k ↦ oCV ≤ k ∧ k < oCV + 6) s v := fun x _ ↦ congrFun f2 x
  clear f1 f2 f3 hd hea w0 w1 hep hv1
  wst; wst; wst; wst; wst; wst
  wst; wst; wst; wst; wst
  refine wp_then (emulW _) fun v2 ⟨f1, f2, f3⟩ ↦ ?_
  have hv2 : regA v2 = evals[5] * (evals[13] + 1) := by
    rw [f1, ew_mul_comm, ← ew_add_one]
    simp only [regA, regB, QState.setReg_reg, reduceCtorEq, ite_false, ite_true]
  have hm2 : ∀ x, v2.mem x = (((v.setMem (wd env.work (0 + oCV)) (v.reg .r9 ^^^ evals[13].c0)).setMem
      (wd env.work (0 + (oCV + 1))) (v.reg .r10 ^^^ evals[13].c1))).mem x := fun x ↦ by
    rw [f2]; rfl
  have hbp2 : v2.reg .rbp = wd env.work 0 := by rw [f3 .rbp (by decide)]; rsimp; exact hbp
  have hdi2 : v2.reg .rdi = s.reg .rdi := by rw [f3 .rdi (by decide)]; rsimp; exact hdi
  have hsp2 : v2.reg .rsp = s.reg .rsp := by rw [f3 .rsp (by decide)]; rsimp; exact hsp
  have h92 : v2.reg .r9 = (evals[5] * (evals[13] + 1)).c0 := congrArg EW.c0 hv2
  have h102 : v2.reg .r10 = (evals[5] * (evals[13] + 1)).c1 := congrArg EW.c1 hv2
  have hd2 : ∀ k, oCV ≤ k → k < oCV + 6 → (v2.mem (wd env.work k)).isSome := fun k h1 h2 ↦ by
    rw [hm2]; exact isSome_setMem _ _ _ (isSome_setMem _ _ _ (hdv k h1 h2))
  have hw2 : Wr env.work (fun k ↦ oCV ≤ k ∧ k < oCV + 6) v v2 := fun x hx ↦ by
    rw [hm2]; exact (show Wr env.work (fun k ↦ oCV ≤ k ∧ k < oCV + 6) v _ by wr_tac) x hx
  wnorm at hm2
  have hctx2 : v2.mem (wd env.ctx ctxWork) = some (wd env.work 0) := by
    rw [hm2]; simp (disch := omega) only [mem_setMem_ctx h4]; exact hctx
  have hcv0 : v2.mem (wd env.work 52764) = some (evals[13] + evals[5] * evals[12]).c0 := by
    rw [hm2]; memw; rw [h9]; exact congrArg some (UInt64.xor_comm _ _)
  have hcv1 : v2.mem (wd env.work 52765) = some (evals[13] + evals[5] * evals[12]).c1 := by
    rw [hm2]; memw; rw [h10]; exact congrArg some (UInt64.xor_comm _ _)
  clear f1 f2 f3 hv2 hm2
  wst; wst; wst; wst; wst
  have hcp : (cpOf xi).size = 2 := by simp [cpOf, powers_size]
  refine wp_then (edotW (xs := cpOf xi) (ys := constraintsW 4 evals) ?_ ?_ ?_ ?_ ?_)
    fun v3 ⟨g1, g2, g3⟩ ↦ ?_
  · rsimp
    have hx := EWArr.extract (mem := v.mem) (xs := powers xi 5) hxp 0 2
    rw [Nat.mul_zero, Nat.add_zero] at hx
    refine hx.congr (n := 4) (fun k hk ↦ ?_) (by rw [hcp])
    memw
    exact hw2.word (by omega) fun j hj ↦ by simp only [oCV, oS] at hj; omega
  · rsimp
    rw [constraintsW_jump, getD_eq (i := 5) (by omega), getD_eq (i := 12) (by omega),
      getD_eq (i := 13) (by omega)]
    intro i hi
    simp only [List.size_toArray, List.length_cons, List.length_nil] at hi
    rw [wd_wd]
    interval_cases i <;> refine EWAt.of ?_ ?_ <;>
      simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] <;> memw
    · exact hcv0
    · exact hcv1
    · rw [h92]
    · rw [h102]
  · rw [constraintsW_jump, hcp]; rfl
  · rsimp; rw [hcp]; rfl
  · rw [hcp]; decide
  have hst : Wr env.work (fun k ↦ oCV ≤ k ∧ k < oCV + 6) s v3 := fun x hx ↦ by
    rw [g2]
    refine (show Wr env.work (fun k ↦ oCV ≤ k ∧ k < oCV + 6) s _ by wr_tac; exact hwv.trans hw2) x hx
  have hrdi3 : v3.reg .rdi = env.ctx := by
    rw [g3 .rdi (by decide)]; rsimp; rw [hdi2, hrdi]
  have hsp3 : v3.reg .rsp = s.reg .rsp := by
    rw [g3 .rsp (by decide)]; rsimp; exact hsp2
  have hctx3 : v3.mem (wd env.ctx ctxWork) = some (wd env.work 0) := by
    rw [g2]; simp only [QState.setReg_mem]
    rw [mem_setMem_ctx h4 (by simp only [oCV, oS]; omega),
      mem_setMem_ctx h4 (by simp only [oCV, oS]; omega)]
    exact hctx2
  have hd3 : ∀ k, oCV ≤ k → k < oCV + 6 → (v3.mem (wd env.work k)).isSome := fun k h1 h2 ↦ by
    rw [g2]; simp only [QState.setReg_mem]
    exact isSome_setMem _ _ _ (isSome_setMem _ _ _ (hd2 k h1 h2))
  have h93 : v3.reg .r9 = (dot (cpOf xi) (constraintsW 4 evals)).c0 := congrArg EW.c0 g1
  have h103 : v3.reg .r10 = (dot (cpOf xi) (constraintsW 4 evals)).c1 := congrArg EW.c1 g1
  clear g1 g2 g3 hd2 hcv0 hcv1 hctx2 h92 h102 hw2 hwv
  wst; wst; wst
  wdone
  refine ⟨?_, ?_, ?_⟩
  · refine EWAt.of ?_ ?_ <;> memw
    · rw [h93]
    · rw [h103]
  · wr_tac; exact hst
  · refine rf_arr ?_ ?_ <;> rsimp
    · rw [hrdi3, hrdi]
    · exact hsp3

/-- The scratch words `termsC1`'s blocks write before `oFIN`: `oCV .. oCV + 7`. -/
abbrev cvW (k : Nat) : Prop := oCV ≤ k ∧ k < oCV + 8

/-- A word outside `cvW` is kept. -/
private theorem Wr.keep {u : QState} (h : Wr env.work cvW s u) {i : Nat}
    (hi : i < 52764 ∨ 52772 ≤ i) (hb : i < 2 ^ 61) :
    u.mem (wd env.work i) = s.mem (wd env.work i) :=
  h.word hb fun k hk ↦ by simp only [cvW, oCV, oS] at hk; omega

/-- **Side `j`** from a state `u` that `termsC1` reached from `s`. -/
theorem sideC_step (h4 : Env4 env) (hrdi : s.reg .rdi = env.ctx)
    (hctx : s.mem (wd env.ctx ctxWork) = some (wd env.work 0)) (hws : WS env s)
    {tix : Nat} (ht : tix < 6)
    (hix : s.mem (wd env.work oTIX) = some tix.toUInt64)
    (hfp : s.mem (wd env.work oFPTR) = some (wd env.work (oB + formsStride * tix)))
    (hep : s.mem (wd env.work oEPTR) = some (wd env.work (oE + eS * tix)))
    (hwid : ∀ i < 6, s.mem (wd env.work (oWID + i)) = some (widths.getD i 0).toUInt64)
    {j : Nat} (hj : j < 3) {f : FormW}
    (hf : FormAt s.mem (wd env.work (oB + formsStride * tix + fW * j)) f)
    {evals : Array EW} (hes : evals.size = widths.getD tix 0)
    (hea : EWArr s.mem (wd env.work (oE + eS * tix + evOff + 1)) evals)
    {p : EW} (hp : EWAt s.mem (wd env.work (oXP + 4 + 2 * j)) p)
    {u : QState} (hwu : Wr env.work cvW s u) (hfu : RegsFrame arrRegs s u) (hdu : DomEq s u)
    {tot : EW} (htot : EWAt u.mem (wd env.work oTOT) tot) :
    WP (sideC j) u (fun u' ↦ EWAt u'.mem (wd env.work oTOT) (tot + f.evaluate evals * p) ∧
      Wr env.work cvW s u' ∧ RegsFrame arrRegs s u' ∧ DomEq s u') E := by
  have hw6 : widths.getD tix 0 ≤ 92 := by
    unfold widths; interval_cases tix <;> decide
  have hfw : formWords = 741 := formWords_val
  obtain ⟨hp0, hp1⟩ := hp
  rw [wd_wd] at hp1
  refine WP.mono (WP.domEq (sideC_spec h4 (by rw [hfu .rdi (by decide)]; exact hrdi)
    (by rw [hwu.ctx h4 fun k hk ↦ by simp only [cvW, oCV, oS] at hk; omega]; exact hctx)
    (fun k h1 h2 ↦ by rw [hdu]; exact hws k h1 h2) ht hj
    (by rw [hwu.keep (by simp only [oTIX, oS]; omega) (by simp only [oTIX, oS]; omega)]; exact hix)
    (by rw [hwu.keep (by simp only [oFPTR, oS]; omega) (by simp only [oFPTR, oS]; omega)]; exact hfp)
    (by rw [hwu.keep (by simp only [oEPTR, oS]; omega) (by simp only [oEPTR, oS]; omega)]; exact hep)
    (by rw [hwu.keep (by simp only [oWID, oS]; omega) (by simp only [oWID, oS]; omega)]
        exact hwid tix ht)
    (hf.congr (hwu.same (by rw [hfw]; simp only [oB, formsStride, fW]; omega) fun k hk ↦ by
      rw [hfw]; simp only [cvW, oCV, oS, oB, formsStride, fW] at hk ⊢; omega))
    hes
    (hea.congr (hwu.same (n := 2 * evals.size) (by simp only [oE, eS, evOff]; omega) fun k hk ↦ by
      simp only [cvW, oCV, oS, oE, eS, evOff] at hk ⊢; omega) (Nat.le_refl _))
    (by rw [hwu.keep (by simp only [oXP, oS]; omega) (by simp only [oXP, oS]; omega)]; exact hp0)
    (by rw [show oXP + 5 + 2 * j = oXP + 4 + 2 * j + 1 by omega,
        hwu.keep (by simp only [oXP, oS]; omega) (by simp only [oXP, oS]; omega)]; exact hp1)
    htot)) ?_ fun _ h ↦ h.1
  rintro u' ⟨⟨e1, e2, e3⟩, e4⟩
  exact ⟨e1, hwu.trans (e2.mono fun k hk ↦ by simp only [cvW, oCV, oTOT, oS] at hk ⊢; omega),
    rf_trans hfu e3, hdu.trans e4⟩

/-- **`JUMP`'s constraints** from a state `u` that `termsC1` reached from `s`. -/
theorem jumpC_step (h4 : Env4 env) (hrdi : s.reg .rdi = env.ctx)
    (hctx : s.mem (wd env.ctx ctxWork) = some (wd env.work 0)) (hws : WS env s)
    (hep : s.mem (wd env.work oEPTR) = some (wd env.work (oE + eS * 4)))
    {xi : EW} (hxp : EWArr s.mem (wd env.work oXP) (powers xi 5))
    {evals : Array EW} (hes : evals.size = 14)
    (hea : EWArr s.mem (wd env.work (oE + eS * 4 + evOff + 1)) evals)
    {u : QState} (hwu : Wr env.work cvW s u) (hfu : RegsFrame arrRegs s u) (hdu : DomEq s u) :
    WP jumpC u (fun u' ↦ EWAt u'.mem (wd env.work oTOT) (dot (cpOf xi) (constraintsW 4 evals)) ∧
      Wr env.work cvW s u' ∧ RegsFrame arrRegs s u' ∧ DomEq s u') E := by
  have hxs : (powers xi 5).size = 5 := powers_size xi 5
  have hdcv : ∀ k, oCV ≤ k → k < oCV + 6 → (u.mem (wd env.work k)).isSome := fun k h1 h2 ↦ by
    rw [hdu]; simp only [oCV, oS] at h1 h2; exact hws k (by omega) (by omega)
  refine WP.mono (WP.domEq (jumpC_spec h4 (by rw [hfu .rdi (by decide)]; exact hrdi)
    (by rw [hwu.ctx h4 fun k hk ↦ by simp only [cvW, oCV, oS] at hk; omega]; exact hctx)
    (by rw [hwu.keep (by simp only [oEPTR, oS]; omega) (by simp only [oEPTR, oS]; omega)]; exact hep)
    (hxp.congr (hwu.same (n := 2 * (powers xi 5).size) (by rw [hxs]; simp only [oXP, oS]; omega)
      fun k hk ↦ by rw [hxs]; simp only [cvW, oCV, oS, oXP] at hk ⊢; omega) (Nat.le_refl _))
    hes
    (hea.congr (hwu.same (n := 2 * evals.size) (by simp only [oE, eS, evOff]; omega) fun k hk ↦ by
      simp only [cvW, oCV, oS, oE, eS, evOff] at hk ⊢; omega) (Nat.le_refl _)) hdcv)) ?_
    fun _ h ↦ h.1
  rintro u' ⟨⟨e1, e2, e3⟩, e4⟩
  exact ⟨e1, hwu.trans (e2.mono fun k hk ↦ by simp only [cvW, oCV, oS] at hk ⊢; omega),
    rf_trans hfu e3, hdu.trans e4⟩

open LeanVM.Protocol.Verifier in
/-- `JUMP`'s constraint count. -/
private theorem nConstraints_jump : (tablesW.getD 4 default).nConstraints = 2 := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, tablesW_toList]
  simp [tables, TableW.ofTable, Table.nConstraints, jumpConstraints]

/-- The other tables have no constraints. -/
private theorem constraintsW_ne {tix : Nat} (h : tix ≠ 4) (evals : Array EW) :
    constraintsW tix evals = #[] := by
  simp only [constraintsW, LeanVM.Protocol.Verifier.opJump, h, ↓reduceIte]

private theorem dot_empty (xs : Array EW) : dot xs #[] = 0 := by
  unfold dot; rw [← Array.foldl_toList, Array.toList_zipWith]; simp

private theorem arr3 {α : Type} (xs : Array α) (h : xs.size = 3) :
    xs = #[xs[0], xs[1], xs[2]] := by
  apply Array.ext (by simp [h])
  intro i h1 h2
  simp only [List.size_toArray, List.length_cons, List.length_nil] at h2
  interval_cases i <;> rfl

private theorem dot3 (a0 a1 a2 b0 b1 b2 : EW) :
    dot #[a0, a1, a2] #[b0, b1, b2] = ((0 + a0 * b0) + a1 * b1) + a2 * b2 := by
  unfold dot; rw [← Array.foldl_toList, Array.toList_zipWith]; simp

private theorem extract_self (xs : Array EW) (h : xs.size = 2) : xs.extract 0 2 = xs := by
  rw [← h]; exact Array.extract_size

/-- **`JUMP`'s constraints when the table is `JUMP`**, to `oTOT` (`0` there otherwise). -/
theorem jumpIte_spec (h4 : Env4 env) (hrdi : s.reg .rdi = env.ctx)
    (hctx : s.mem (wd env.ctx ctxWork) = some (wd env.work 0)) (hws : WS env s)
    {tix : Nat} (ht : tix < 6)
    (hep : s.mem (wd env.work oEPTR) = some (wd env.work (oE + eS * tix)))
    {xi : EW} (hxp : EWArr s.mem (wd env.work oXP) (powers xi 5))
    {evals : Array EW} (hes : evals.size = widths.getD tix 0)
    (hea : EWArr s.mem (wd env.work (oE + eS * tix + evOff + 1)) evals)
    {u : QState} (hwu : Wr env.work cvW s u) (hfu : RegsFrame arrRegs s u) (hdu : DomEq s u)
    (hrax : u.reg .rax = tix.toUInt64) (htot : EWAt u.mem (wd env.work oTOT) 0) :
    WP (.ite (.cmp .eq .rax (.imm (Int64.ofNat tJump))) jumpC .skip) u
      (fun u' ↦ EWAt u'.mem (wd env.work oTOT)
          (if tix = 4 then dot (cpOf xi) (constraintsW 4 evals) else 0) ∧
        Wr env.work cvW s u' ∧ RegsFrame arrRegs s u' ∧ DomEq s u') E := by
  have h4u : (Int64.ofNat tJump).toUInt64 = (4 : Nat).toUInt64 := by decide
  by_cases htj : tix = 4
  · subst htj
    refine wp_ite_true (by simp only [Cond.eval, Rhs.eval, hrax, h4u, beq_self_eq_true]) ?_
    refine WP.mono (jumpC_step h4 hrdi hctx hws hep hxp (by rw [hes]; rfl) hea hwu hfu hdu)
      (fun u' h ↦ ?_) fun _ h ↦ h
    simp only [↓reduceIte]
    exact h
  · refine wp_ite_false ?_ (WP.skip ⟨?_, hwu, hfu, hdu⟩)
    · simp only [Cond.eval, Rhs.eval, hrax, h4u, beq_eq_false_iff_ne, ne_eq]
      rw [Transcript.toUInt64_inj (by omega) (by omega)]
      exact htj
    · simp only [htj, ↓reduceIte]
      exact htot

/-- The term the code sums, in the model's order. -/
private theorem terms_value (fin wt T0 p0 p1 p2 F0 F1 F2 : EW) :
    fin + (((T0 + F0 * p0) + F1 * p1) + F2 * p2) * wt =
      fin + wt * (T0 + (((0 + p0 * F0) + p1 * F1) + p2 * F2)) :=
  EW.toE_injective (by simp only [EW.toE_add, EW.toE_mul, EW.toE_zero]; ring)

/-- **Table `tix`'s term**, added at `oFIN`. -/
theorem termsC1_spec (h4 : Env4 env) (hrdi : s.reg .rdi = env.ctx)
    (hctx : s.mem (wd env.ctx ctxWork) = some (wd env.work 0)) (hws : WS env s)
    {tix : Nat} (ht : tix < 6) (cur : Nat) (hcur : tix = 4 → cur = 0)
    (hix : s.mem (wd env.work oTIX) = some tix.toUInt64)
    (hfp : s.mem (wd env.work oFPTR) = some (wd env.work (oB + formsStride * tix)))
    (hep : s.mem (wd env.work oEPTR) = some (wd env.work (oE + eS * tix)))
    (hwid : ∀ i < 6, s.mem (wd env.work (oWID + i)) = some (widths.getD i 0).toUInt64)
    (xi : EW) (hxp : EWArr s.mem (wd env.work oXP) (powers xi 5))
    (weights : Array EW) (hw : EWArr s.mem (wd env.work oWT) weights) (hwsz : weights.size = 6)
    (forms : Array FormW) (hf : forms.size = 3)
    (hfa : ∀ side < 3, FormAt s.mem (wd env.work (oB + formsStride * tix + fW * side))
      (forms.getD side #[]))
    (evals : Array EW) (hes : evals.size = widths.getD tix 0)
    (hea : EWArr s.mem (wd env.work (oE + eS * tix + evOff + 1)) evals)
    (fin : EW) (hfin : EWAt s.mem (wd env.work oFIN) fin) :
    WP termsC1 s (fun s' ↦ EWAt s'.mem (wd env.work oFIN)
        (fin + weights.getD tix 0 *
          (dot ((cpOf xi).extract cur (cur + (tablesW.getD tix default).nConstraints))
              (constraintsW tix evals) +
            dot (fpOf xi) (forms.map (·.evaluate evals)))) ∧
      Wr env.work (fun k ↦ (oFIN ≤ k ∧ k < oFIN + 2) ∨ (oCV ≤ k ∧ k < oCV + 8)) s s' ∧
      RegsFrame arrRegs s s') E := by
  have hsz : (powers xi 5).size = 5 := powers_size xi 5
  have hfps : (fpOf xi).size = 3 := by simp [fpOf, hsz]
  have hfpA : EWArr s.mem (wd env.work (oXP + 4)) (fpOf xi) := EWArr.extract hxp 2 5
  have hpj : ∀ j (h : j < 3), EWAt s.mem (wd env.work (oXP + 4 + 2 * j)) (fpOf xi)[j] :=
    fun j hj ↦ by have := hfpA j (by omega); rwa [wd_wd] at this
  have hfj : ∀ j (h : j < 3), FormAt s.mem (wd env.work (oB + formsStride * tix + fW * j))
      forms[j] := fun j hj ↦ by
    have := hfa j hj
    rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some]
      at this
  have hix' := hix
  wnorm at hix'
  have hdT : ∀ k, oTOT ≤ k → k < oTOT + 2 → (s.mem (wd env.work k)).isSome := fun k h1 h2 ↦ by
    simp only [oTOT, oS] at h1 h2; exact hws k (by omega) (by omega)
  unfold termsC1
  wst; wst; wst; wst
  apply WP.blk_cons
  refine WP.mono (jumpIte_spec h4 hrdi hctx hws ht hep hxp hes hea (by
      repeat (first
        | with_reducible refine Wr.setReg ?_ _ _
        | with_reducible refine Wr.setMem ?_ (by simp only [cvW, oCV, oTOT, oS]; omega) _)
      exact Wr.refl _ _ _)
    (by rfw) ?_ (by regw) (EWAt.of (by memw; rfl) (by memw; rfl))) (fun u0 ⟨g0, w0, f0, d0⟩ ↦ ?_)
    fun _ h ↦ h
  · refine (((DomEq.setReg s _ _).trans (DomEq.setMem ?_ _)).trans (DomEq.setMem ?_ _)).trans
      (DomEq.setReg _ _ _)
    · exact hdT _ (by omega) (by omega)
    · exact isSome_setMem _ _ _ (hdT _ (by omega) (by omega))
  refine wp_then (sideC_step h4 hrdi hctx hws ht hix hfp hep hwid (j := 0) (by decide)
    (hfj 0 (by decide)) hes hea (hpj 0 (by decide)) w0 f0 d0 g0) fun u1 ⟨g1, w1, f1, d1⟩ ↦ ?_
  refine wp_then (sideC_step h4 hrdi hctx hws ht hix hfp hep hwid (j := 1) (by decide)
    (hfj 1 (by decide)) hes hea (hpj 1 (by decide)) w1 f1 d1 g1) fun u2 ⟨g2, w2, f2, d2⟩ ↦ ?_
  refine wp_then (sideC_step h4 hrdi hctx hws ht hix hfp hep hwid (j := 2) (by decide)
    (hfj 2 (by decide)) hes hea (hpj 2 (by decide)) w2 f2 d2 g2) fun u3 ⟨g3, w3, f3, d3⟩ ↦ ?_
  clear g0 g1 g2 w0 w1 w2 f0 f1 f2 d0 d1 d2
  have hwt := hw tix (by omega)
  obtain ⟨wt0, wt1⟩ := hwt
  rw [wd_wd] at wt0
  rw [wd_wd, wd_wd] at wt1
  obtain ⟨fi0, fi1⟩ := hfin
  rw [wd_wd] at fi1
  obtain ⟨tt0, tt1⟩ := g3
  rw [wd_wd] at tt1
  have hrdi3 : u3.reg .rdi = env.ctx := by rw [f3 .rdi (by decide)]; exact hrdi
  have hsp3 : u3.reg .rsp = s.reg .rsp := f3 .rsp (by decide)
  have hctx3 : u3.mem (wd env.ctx ctxWork) = some (wd env.work 0) := by
    rw [w3.ctx h4 fun k hk ↦ by simp only [cvW, oCV, oS] at hk; omega]; exact hctx
  have hix3 : u3.mem (wd env.work 52773) = some tix.toUInt64 := by
    rw [w3.keep (by omega) (by omega)]; exact hix'
  have wt0' : u3.mem (wd env.work (0 + 2 * tix + oWT)) = some weights[tix].c0 := by
    rw [show 0 + 2 * tix + oWT = oWT + 2 * tix by omega,
      w3.keep (by simp only [oWT, oS]; omega) (by simp only [oWT, oS]; omega)]
    exact wt0
  have wt1' : u3.mem (wd env.work (0 + 2 * tix + (oWT + 1))) = some weights[tix].c1 := by
    rw [show 0 + 2 * tix + (oWT + 1) = oWT + 2 * tix + 1 by omega,
      w3.keep (by simp only [oWT, oS]; omega) (by simp only [oWT, oS]; omega)]
    exact wt1
  wnorm at tt0 tt1 fi0 fi1
  have fi0' : u3.mem (wd env.work 52682) = some fin.c0 := by
    rw [w3.keep (by omega) (by omega)]; exact fi0
  have fi1' : u3.mem (wd env.work 52683) = some fin.c1 := by
    rw [w3.keep (by omega) (by omega)]; exact fi1
  clear wt0 wt1 fi0 fi1 hfa hfj hpj hfpA hxp hw hea hwid hep hfp hix hix' hctx
  wst; wst
  refine wp_shl4add (r := .rbp) (by regw) (by decide) ?_
  refine wp_ldA (by regw) (by simp only [QState.setReg_mem]; exact wt0') ?_
  refine wp_ldA (by regw) (by simp only [QState.setReg_mem]; exact wt1') ?_
  wst; wst
  refine wp_then (emulW _) fun v ⟨e1, e2, e3⟩ ↦ ?_
  simp only [QState.setReg_mem] at e2
  set T0 : EW := if tix = 4 then dot (cpOf xi) (constraintsW 4 evals) else 0 with hT0
  set tot3 : EW := T0 + forms[0].evaluate evals * (fpOf xi)[0] +
    forms[1].evaluate evals * (fpOf xi)[1] + forms[2].evaluate evals * (fpOf xi)[2] with htot3
  have hv : regA v = tot3 * weights[tix] := by
    rw [e1]; simp only [regA, regB, QState.setReg_reg, reduceCtorEq, ite_false, ite_true]; rfl
  have hbp : v.reg .rbp = wd env.work 0 := by rw [e3 .rbp (by decide)]; regw
  have hdi : v.reg .rdi = s.reg .rdi := by rw [e3 .rdi (by decide)]; rsimp; rw [hrdi3, hrdi]
  have hsp : v.reg .rsp = s.reg .rsp := by rw [e3 .rsp (by decide)]; rsimp; exact hsp3
  have h9 : v.reg .r9 = (tot3 * weights[tix]).c0 := congrArg EW.c0 hv
  have h10 : v.reg .r10 = (tot3 * weights[tix]).c1 := congrArg EW.c1 hv
  have fv0 : v.mem (wd env.work 52682) = some fin.c0 := by rw [e2]; exact fi0'
  have fv1 : v.mem (wd env.work 52683) = some fin.c1 := by rw [e2]; exact fi1'
  have hvw : Wr env.work (fun k ↦ (oFIN ≤ k ∧ k < oFIN + 2) ∨ (oCV ≤ k ∧ k < oCV + 8)) s v :=
    fun x hx ↦ by rw [e2]; exact w3 x fun k hk ↦ hx k (Or.inr hk)
  have hdF : ∀ k, oFIN ≤ k → k < oFIN + 2 → (v.mem (wd env.work k)).isSome := fun k h1 h2 ↦ by
    simp only [oFIN, oS] at h1 h2
    obtain rfl | rfl : k = 52682 ∨ k = 52683 := by omega
    · rw [fv0]; rfl
    · rw [fv1]; rfl
  have hS : dot ((cpOf xi).extract cur (cur + (tablesW.getD tix default).nConstraints))
      (constraintsW tix evals) = T0 := by
    by_cases htj : tix = 4
    · subst htj
      have hcp : (cpOf xi).size = 2 := by simp [cpOf, hsz]
      rw [hcur rfl, nConstraints_jump, Nat.zero_add, extract_self _ hcp, hT0]
      simp
    · rw [constraintsW_ne htj, dot_empty, hT0]
      simp [htj]
  have hD : dot (fpOf xi) (forms.map (·.evaluate evals)) = (((0 : EW) + (fpOf xi)[0] *
      forms[0].evaluate evals) + (fpOf xi)[1] * forms[1].evaluate evals) +
        (fpOf xi)[2] * forms[2].evaluate evals := by
    conv_lhs => rw [arr3 (fpOf xi) hfps, arr3 (forms.map (·.evaluate evals)) (by simp [hf]), dot3]
    simp only [Array.getElem_map]
  have hV : fin + weights.getD tix 0 * (dot ((cpOf xi).extract cur
      (cur + (tablesW.getD tix default).nConstraints)) (constraintsW tix evals) +
        dot (fpOf xi) (forms.map (·.evaluate evals))) = fin + tot3 * weights[tix] := by
    rw [hS, hD, getD_eq (by omega), htot3, terms_value]
  rw [hV]
  clear e1 e2 e3 hv hS hD hV fi0' fi1' wt0' wt1' tt0 tt1 hix3 hctx3 hrdi3
  wst; wst; wst; wst; wst; wst
  wdone
  refine ⟨?_, ?_, ?_⟩
  · refine EWAt.of ?_ ?_ <;> memw
    · rw [h9]; rfl
    · rw [h10]; rfl
  · wr_tac; exact hvw
  · refine rf_arr ?_ ?_ <;> rsimp
    · exact hdi
    · exact hsp

end NativeVm.Code.P4
