module

public import NativeVm.Code.Phase7.Induced
public import NativeVm.Code.Phase7.Rounds
public import NativeVm.Code.Phase7.RingMath
public import NativeVm.Field.Mle

/-!
# The final level's weight and last check

`finalWC` checks `weight · multilinearEval (folded.extract 0 (2^μ)) tail == claim`, the last
`require` of the final level (`finalM`), with `weight` the glued claims' fold from the basis's
value `b` (`finalWeightW`), the point at `ptO`:

* the fold over the glued claims (`gluedC`, the loop state in the scratch words `cJ`, `cK` and the
  temporaries `tmpO + 20 ..`): per claim the point from its first fold round, then `eqEval z`
  (`eeqEval`, over the common length) or `inducedWeight μ queries weights` (`subTableC` then
  `inducedC` in `indO`'s words, over the common length of the queries and weights), times the
  claim's scalar, added;
* the multilinear evaluation (`emle`, in `mleO`'s words), the product, and the comparison with
  the claim: `.fail` exactly when they differ.

It writes the working area's words `finalWF` only.
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model NativeVm.Field LeanVM.Parameters NativeVm.Equiv
open NativeVm.Transcript (wd Env Fits Disj wdisp ctxWork ctxEnd wd_inj wd_zero wd_toNat wp_load
  wp_store wp_reg eval_cw eval_wd)

/-- The working area's words `finalWC` writes: temporaries `20 ..< 32`, the induced weight's
scratch and table (`indO`), the multilinear evaluation's work area (`mleO`), the counters. -/
def finalWF (k : Nat) : Prop :=
  (tmpO + 20 ≤ k ∧ k < tmpO + 32) ∨ (indO ≤ k ∧ k < indO + 256) ∨ (mleO ≤ k ∧ k < mleO + 64) ∨
    (sc 5 ≤ k ∧ k < sc 8)

/-- The first glued claim's first word. -/
abbrev gBase : Nat := whirR.off + whirGluedOff + 1

/-- The induced weight's table, from `indO + 80`, and its layer, from `indO + 144`. -/
abbrev fwTab : Nat := indO + 80
abbrev fwLay : Nat := indO + 144

/-- Unfold the offsets, then `omega`. -/
macro "nomega" : tactic => `(tactic| first
  | omega
  | (simp only [finalWF, gBase, sc, cJ, cK, cI, cMu, tmpO,
  indO, ptO, mleO, spO, hiO, scratch_off, whir_off, mineLo_val, dataEnd_val, gluedWords_val,
  gluedQOff_val, gluedWOff_val, whirGluedOff_val, stackCap_val, queryCap_val, vecWords,
  wvecWords, whirWords_val, fwTab, fwLay, inducedScratchWords]; omega))

namespace FW

/-! ## The model -/

/-- A glued claim's term. -/
def gstep (point : Array EW) (w : EW) (g : GluedClaimW) : EW :=
  w + g.scalar * g.weight.eval (point.extract g.foldStart point.size)

/-- The weight after the first `j` glued claims. -/
def accW (point : Array EW) (gs : Array GluedClaimW) (b : EW) (j : Nat) : EW :=
  (gs.toList.take j).foldl (gstep point) b

theorem accW_succ (point : Array EW) {gs : Array GluedClaimW} (b : EW) {j : Nat} (hj : j < gs.size) :
    accW point gs b (j + 1) = gstep point (accW point gs b j) gs[j] := by
  have key : gs.toList[j]? = some gs[j] := by simp [hj]
  rw [accW, accW, List.take_add_one, List.foldl_append, key]
  rfl

theorem accW_full (point : Array EW) (gs : Array GluedClaimW) (b : EW) :
    accW point gs b gs.size = gs.foldl
      (fun w g ↦ w + g.scalar * g.weight.eval (point.extract g.foldStart point.size)) b := by
  rw [accW, List.take_of_length_le (by simp), Array.foldl_toList]
  rfl

theorem zip_extract_min {α β : Type} (a : Array α) (b : Array β) :
    (a.extract 0 (min a.size b.size)).zip (b.extract 0 (min a.size b.size)) = a.zip b := by
  apply Array.toList_inj.mp
  simp only [Array.toList_zip, Array.toList_extract, List.extract_eq_take_drop, List.drop_zero,
    Nat.sub_zero]
  rw [List.zip_eq_zipWith, List.zip_eq_zipWith, ← List.take_zipWith,
    List.take_of_length_le (by simp)]

theorem inducedWeight_min (mu : Nat) (qs : Array UInt64) (ws pt : Array EW) :
    inducedWeight mu (qs.extract 0 (min ws.size qs.size)) (ws.extract 0 (min ws.size qs.size)) pt =
      inducedWeight mu qs ws pt := by
  unfold inducedWeight
  rw [zip_extract_min]

theorem eqEvalL_min (a b : List E) :
    LeanVM.Protocol.Verifier.eqEval (a.take (min a.length b.length))
      (b.take (min a.length b.length)) = LeanVM.Protocol.Verifier.eqEval a b := by
  rw [Ring.eqEval_take_drop (min a.length b.length) a b]
  rcases Nat.le_total a.length b.length with h | h
  · rw [List.drop_eq_nil_of_le (as := a) (by omega), Ring.eqEval_nil_left, mul_one]
  · rw [List.drop_eq_nil_of_le (as := b) (by omega), Ring.eqEval_nil_right, mul_one]

theorem eqEval_min (z x : Array EW) :
    LeanVM.Protocol.Verifier.eqEval ((z.extract 0 (min z.size x.size)).toList.map EW.toE)
      ((x.extract 0 (min z.size x.size)).toList.map EW.toE) = (eqEval z x).toE := by
  rw [toE_eqEval]
  have := eqEvalL_min (z.toList.map EW.toE) (x.toList.map EW.toE)
  simp only [List.length_map, Array.length_toList] at this
  rw [← this]
  simp [Array.toList_extract, List.extract_eq_take_drop, List.map_take]

theorem beq_true_iff (x y : EW) : (x == y) = true ↔ x.c0 = y.c0 ∧ x.c1 = y.c1 := by
  rw [EW.beq_iff_toE, EW.toE_inj]
  cases x; cases y; simp

/-! ## Arrays -/

theorem ewarr_drop {mem : UInt64 → Option UInt64} {q : UInt64} {xs : Array EW}
    (h : EWArr mem q xs) (f : Nat) : EWArr mem (wd q (2 * f)) (xs.extract f xs.size) := by
  intro i hi
  simp only [Array.size_extract, Nat.min_self] at hi
  rw [Array.getElem_extract, wd_wd, show 2 * f + 2 * i = 2 * (f + i) by omega]
  exact h (f + i) (by omega)

theorem ewarr_take {mem : UInt64 → Option UInt64} {q : UInt64} {xs : Array EW}
    (h : EWArr mem q xs) (m : Nat) : EWArr mem q (xs.extract 0 m) := by
  intro i hi
  simp only [Array.size_extract] at hi
  simp only [Array.getElem_extract, Nat.zero_add]
  exact h i (by omega)

theorem wordarr_take {mem : UInt64 → Option UInt64} {q : UInt64} {xs : Array UInt64}
    (h : WordArr mem q xs) (m : Nat) : WordArr mem q (xs.extract 0 m) := by
  intro i hi
  simp only [Array.size_extract] at hi
  simp only [Array.getElem_extract, Nat.zero_add]
  exact h i (by omega)

/-! ## Areas -/

theorem fitsW {W : UInt64} {N a m : Nat} (hf : Fits W N) (ha : a < N) (hm : a + m ≤ N) :
    Fits (wd W a) m := Ind.fits_sub hf ha hm

theorem disjW {W : UInt64} {N a n b m : Nat} (hf : Fits W N) (ha : a < N) (hb : b < N)
    (h : a + n ≤ b ∨ b + m ≤ a) : Disj (wd W a) n (wd W b) m := by
  unfold Disj
  rw [wd_toNat hf ha, wd_toNat hf hb]
  omega

/-! ## What the code keeps -/

/-- The run so far from `s0`: `rdi`, the frame, and the area's words outside `finalWF`. -/
structure St (p : Par) (s0 t : QState) : Prop where
  rdi : t.reg .rdi = p.env.ctx
  fr : FrM p.env s0 t
  on : Only p.env finalWF s0.mem t.mem

variable {p : Par} {s0 t t' : QState}

theorem St.setReg (h : St p s0 t) {r : Reg64} (hr : r ≠ .rdi) (v : UInt64) :
    St p s0 (t.setReg r v) :=
  ⟨by rw [QState.setReg_reg, ite_eq_right (Ne.symm hr)]; exact h.rdi,
    h.fr.trans (frM_setReg hr v), h.on⟩

theorem St.ex (h : St p s0 t) (hin : Inputs p.env p.inp s0.mem) {k : Nat} (hk : k < dataEnd) :
    (t.mem (wd p.env.work k)).isSome := by
  rw [h.fr.dom]
  exact hin.workSome k (lt_of_lt_of_le hk (dataEnd_le _))

theorem St.store (h : St p s0 t) (hin : Inputs p.env p.inp s0.mem) {k : Nat} (hk : finalWF k)
    (h1 : mineLo ≤ k) (h2 : k < dataEnd) (v : UInt64) : St p s0 (t.setMem (wd p.env.work k) v) :=
  ⟨by rw [QState.setMem_reg]; exact h.rdi, h.fr.trans (frM_store h1 h2 (h.ex hin h2) v),
    h.on.store hk (by rw [dataEnd_val] at h2; omega) v⟩

theorem St.rd (h : St p s0 t) {k : Nat} (h1 : mineLo ≤ k) (h2 : k < dataEnd) (hk : ¬ finalWF k) :
    t.mem (wd p.env.work k) = s0.mem (wd p.env.work k) := h.on k h1 h2 hk

theorem St.wp (h : St p s0 t) (hin : Inputs p.env p.inp s0.mem)
    (hwp : s0.mem (wd p.env.ctx ctxWork) = some p.env.work) :
    t.mem (wd p.env.ctx ctxWork) = some p.env.work := by
  rw [h.fr.mem _ ?_]
  · exact hwp
  · rintro ⟨k, -, h2, e⟩
    exact hin.ctx_ne_work (by unfold ctxWork; rw [Transcript.ctxEnd_val]; omega)
      (lt_of_lt_of_le h2 (dataEnd_le _)) e

/-- A run writing the `n` words from area word `o`, inside `finalWF`. -/
theorem St.next (h : St p s0 t) (hr : t'.reg .rdi = t.reg .rdi)
    (hd : ∀ a, (t'.mem a).isSome = (t.mem a).isSome) {o n : Nat}
    (ho : ∀ j < n, finalWF (o + j)) (hlo : mineLo ≤ o) (hn : o + n ≤ dataEnd)
    (hm : ∀ a, (∀ k < n, a ≠ wd (wd p.env.work o) k) → t'.mem a = t.mem a) : St p s0 t' := by
  have hde := dataEnd_val
  refine ⟨hr.trans h.rdi, h.fr.trans ⟨hr, hd, fun a ha ↦ hm a fun k hk e ↦ ha
    ⟨o + k, by omega, by omega, by rw [e, wd_wd]⟩⟩, Only.mono (h.on.trans ?_) fun k hk ↦ hk.elim id id⟩
  intro k h1 h2 hk
  refine hm _ fun j hj e ↦ hk ?_
  rw [wd_wd, wd_inj (by omega) (by omega)] at e
  exact e ▸ ho j hj

theorem St.ewarr (h : St p s0 t) {o : Nat} {xs : Array EW} (hx : EWArr s0.mem (wd p.env.work o) xs)
    (hlo : mineLo ≤ o) (hhi : o + 2 * xs.size ≤ dataEnd) (hw : ∀ j < 2 * xs.size, ¬ finalWF (o + j)) :
    EWArr t.mem (wd p.env.work o) xs :=
  hx.congr (h.on.same hlo hhi hw) le_rfl

theorem St.ewat (h : St p s0 t) {o : Nat} {x : EW} (hx : EWAt s0.mem (wd p.env.work o) x)
    (hlo : mineLo ≤ o) (hhi : o + 2 ≤ dataEnd) (hw : ∀ j < 2, ¬ finalWF (o + j)) :
    EWAt t.mem (wd p.env.work o) x :=
  hx.congr (h.on.same hlo hhi hw)

theorem St.glued (h : St p s0 t) {o : Nat} {g : GluedClaimW} (hg : GluedAt s0.mem (wd p.env.work o) g)
    (hlo : mineLo ≤ o) (hhi : o + gluedWords ≤ dataEnd) (hw : ∀ j < gluedWords, ¬ finalWF (o + j)) :
    GluedAt t.mem (wd p.env.work o) g :=
  hg.congr (h.on.same hlo hhi hw)

/-- The statement does not write `rdi`: which words exist and `rdi` kept. -/
theorem wp_fr {c : Stmt} {s : QState} {P E : QState → Prop} (hc : c.writes .rdi = false)
    (h : WP c s P E) :
    WP c s (fun s' ↦ P s' ∧ (∀ a, (s'.mem a).isSome = (s.mem a).isSome) ∧
      s'.reg .rdi = s.reg .rdi) E :=
  WP.mono (NativeVm.Transcript.WP.frame h) (fun _ h' ↦ ⟨h'.1, h'.2.1, h'.2.2 _ hc⟩)
    fun _ h' ↦ h'.1

/-- `b := min a b`. -/
def minR (a b : Reg64) : Stmt := .ite (.cmp .ltu a (.reg b)) (I (.mov b a)) .skip

theorem minR_spec {s : QState} {E : QState → Prop} {a b : Reg64} {x y : Nat} (hx : x < 2 ^ 64)
    (hy : y < 2 ^ 64) (ha : s.reg a = x.toUInt64) (hb : s.reg b = y.toUInt64) :
    WP (minR a b) s (fun s' ↦ s'.mem = s.mem ∧ s'.reg b = (min x y).toUInt64 ∧
      ∀ r, r ≠ b → s'.reg r = s.reg r) E := by
  unfold minR
  apply WP.ite
  have hc : (Cond.cmp .ltu a (.reg b)).eval s = decide (x < y) := by
    rw [NativeVm.Transcript.cond_ltu, NativeVm.Transcript.rhs_reg, ha, hb]
    exact decide_eq_decide.mpr (NativeVm.Transcript.toUInt64_lt hx hy)
  rw [hc]
  by_cases h : x < y
  · rw [decide_eq_true h]
    exact WP.ins' (by
      simp only [QInstr.step]
      refine ⟨rfl, by rsimp; rw [ha, Nat.min_eq_left h.le], fun r hr ↦ ?_⟩
      rw [QState.setReg_reg, ite_eq_right hr])
  · rw [decide_eq_false h]
    exact WP.skip ⟨rfl, by rw [hb, Nat.min_eq_right (by omega)], fun _ _ ↦ rfl⟩

/-! ## The equality weight -/

/-- `A := eqEval z x`: the claim at `rbx` (`z` from its word `5`), `x` at `rsi`, `|x|` in `rdx`. -/
def eqB : Stmt := blk [
  I (.load .r15 (at_ .rbx (wdisp 5))), minR .rdx .r15,
  I (.lea .r13 (at_ .rbx (wdisp 6))), I (.mov .r14 .rsi), eeqEval]

theorem eqB_spec {u : QState} {F : QState → Prop} {z x : Array EW} {G X : UInt64}
    (hS : St p s0 u) (hbx : u.reg .rbx = G) (hsi : u.reg .rsi = X)
    (hdx : u.reg .rdx = x.size.toUInt64) (hz : EVec u.mem (wd G 5) stackCap z)
    (hx : EWArr u.mem X x) (hxs : x.size ≤ 30) :
    WP eqB u (fun u' ↦ St p s0 u' ∧ u'.reg .r9 = (eqEval z x).c0 ∧
      u'.reg .r10 = (eqEval z x).c1 ∧ u'.mem = u.mem) F := by
  obtain ⟨hzs, ⟨-, hzn⟩, hza⟩ := hz
  have hzs' : z.size ≤ 30 := by rw [stackCap_val] at hzs; exact hzs
  unfold eqB
  refine wp_load (eval_wd (j := 0) (by rw [hbx, wd_zero]) 5) (by rw [Nat.zero_add]; exact hzn) ?_
  refine Field.WP.then (minR_spec (x := x.size) (y := z.size) (by omega) (by omega)
    (by rsimp; exact hdx) (by rsimp)) fun u1 ⟨m1, r1, f1⟩ ↦ ?_
  rsimp at m1 f1
  refine Ind.wp_lea 6 (b := G) (by rw [f1 .rbx (by decide)]; rsimp; exact hbx) rfl ?_
  fstep
  set m := min z.size x.size with hm
  refine Field.WP.then (eeqEval_spec (xs := (z.extract 0 m).toList.map EW.toE)
    (ys := (x.extract 0 m).toList.map EW.toE) ?_ ?_ (by simp; omega) ?_ (by simp; omega))
    fun u2 ⟨e1, e2, e3⟩ ↦ ?_
  · rsimp
    rw [m1, ← EWArr_iff_EArr]
    have := ewarr_take hza m
    rwa [wd_wd] at this
  · rsimp
    rw [m1, f1 .rsi (by decide), ← EWArr_iff_EArr]
    rsimp
    rw [hsi]
    exact ewarr_take hx m
  · rsimp
    rw [r1]
    simp [hm, Nat.min_comm]
  rw [eqEval_min] at e1
  obtain ⟨l0, l1⟩ := lanes_of_eOf e1
  have hmem : u2.mem = u.mem := by rw [e2]; rsimp; exact m1
  have hrdi : u2.reg .rdi = u.reg .rdi := by
    rw [e3 .rdi (by decide)]; rsimp; rw [f1 .rdi (by decide)]; rsimp
  refine WP.blk_nil ⟨⟨hrdi.trans hS.rdi, hS.fr.trans ⟨hrdi, fun a ↦ by rw [hmem],
    fun a _ ↦ by rw [hmem]⟩, by rw [hmem]; exact hS.on⟩, l0, l1, hmem⟩

/-! ## The induced weight -/

theorem eval_atw {s : QState} {r : Reg64} {B : UInt64} (h : s.reg r = B) (k : Nat) :
    (at_ r (wdisp k)).eval s = wd B k := by
  rw [Field.eval_at, h]
  rfl

/-- `A := inducedWeight μ queries weights x`: the claim at `rbx` (also at the work word `cJ`),
`x` at `rsi`, `|x|` in `rdx`, `rbp` at the working area. -/
def indB : Stmt := blk [
  stw (tmpO + 23) .rsi, stw (tmpO + 24) .rdx,
  I (.load .r15 (at_ .rbx (wdisp 4))), leaw .r14 fwTab, leaw .rbx fwLay,
  subTableC,
  ldW, ldw .rbx cJ,
  I (.lea .r13 (at_ .rbx (wdisp (gluedQOff + 1)))), I (.lea .r14 (at_ .rbx (wdisp (gluedWOff + 1)))),
  I (.load .r15 (at_ .rbx (wdisp gluedQOff))), I (.load .rax (at_ .rbx (wdisp gluedWOff))),
  minR .rax .r15,
  ldw .rsi (tmpO + 23), ldw .rdx (tmpO + 24), leaw .rcx fwTab,
  I (.load .rax (at_ .rbx (wdisp 4))), leaw .rbx indO, I (.mov .rbp .rax),
  inducedC]

theorem indB_spec {u : QState} {F : QState → Prop} (hin : Inputs p.env p.inp s0.mem)
    (hwp : s0.mem (wd p.env.ctx ctxWork) = some p.env.work)
    {g : GluedClaimW} {mu : Nat} {qs : Array UInt64} {ws x : Array EW} {gi xo : Nat}
    (hS : St p s0 u) (hW : u.reg .rbp = p.env.work) (hbx : u.reg .rbx = wd p.env.work gi)
    (hcj : u.mem (wd p.env.work cJ) = some (wd p.env.work gi))
    (hsi : u.reg .rsi = wd p.env.work xo) (hdx : u.reg .rdx = x.size.toUInt64)
    (hg : GluedAt s0.mem (wd p.env.work gi) g) (hwt : g.weight = .induced mu qs ws)
    (hgi : gBase ≤ gi ∧ gi + gluedWords ≤ whirR.off + whirWords) (hmu : mu ≤ 30)
    (hx : EWArr s0.mem (wd p.env.work xo) x) (hxo : ptO ≤ xo ∧ xo + 2 * x.size ≤ ptO + 64)
    (hxs : x.size ≤ 30) :
    WP indB u (fun u' ↦ St p s0 u' ∧ u'.reg .r9 = (inducedWeight mu qs ws x).c0 ∧
      u'.reg .r10 = (inducedWeight mu qs ws x).c1 ∧
      ∀ k, k < dataEnd → ¬ (tmpO + 23 ≤ k ∧ k < tmpO + 25) → ¬ (indO ≤ k ∧ k < indO + 256) →
        u'.mem (wd p.env.work k) = u.mem (wd p.env.work k)) F := by
  have hde := dataEnd_val
  have hfw : Fits p.env.work dataEnd := by
    have h1 := hin.fitWork
    have h2 := dataEnd_le p.inp.bytecode.size
    unfold Fits at h1 ⊢
    omega
  have hgw : ∀ j < gluedWords, ¬ finalWF (gi + j) := fun j hj ↦ by
    rw [gluedWords_val] at hj; revert hgi; nomega
  have hgv : ∀ {v : QState}, St p s0 v → GluedAt v.mem (wd p.env.work gi) g := fun hv ↦
    hv.glued hg (by revert hgi; nomega) (by revert hgi; nomega) hgw
  have hxv : ∀ {v : QState}, St p s0 v → EWArr v.mem (wd p.env.work xo) x := fun hv ↦
    hv.ewarr hx (by revert hxo; nomega) (by revert hxo; nomega) (fun j hj ↦ by revert hxo; nomega)
  unfold indB
  -- the point's address and size, saved
  refine stw_wp hW (hS.ex hin (by nomega)) ?_
  have hS1 := hS.store hin (k := tmpO + 23) (by nomega) (by nomega) (by nomega) (u.reg .rsi)
  refine stw_wp (by rsimp; exact hW) (hS1.ex hin (by nomega)) ?_
  have hS2 := hS1.store hin (k := tmpO + 24) (by nomega) (by nomega) (by nomega)
    ((u.setMem (wd p.env.work (tmpO + 23)) (u.reg .rsi)).reg .rdx)
  set v := (u.setMem (wd p.env.work (tmpO + 23)) (u.reg .rsi)).setMem (wd p.env.work (tmpO + 24))
    ((u.setMem (wd p.env.work (tmpO + 23)) (u.reg .rsi)).reg .rdx) with hv
  have v23 : v.mem (wd p.env.work (tmpO + 23)) = some (wd p.env.work xo) := by
    rw [hv, setMem_wd _ (by nomega) (by nomega), ite_no (by nomega),
      setMem_wd _ (by nomega) (by nomega), ite_yes rfl, hsi]
  have v24 : v.mem (wd p.env.work (tmpO + 24)) = some x.size.toUInt64 := by
    rw [hv, setMem_wd _ (by nomega) (by nomega), ite_yes rfl]
    rsimp
    rw [hdx]
  have vk : ∀ k, k < dataEnd → k ≠ tmpO + 23 → k ≠ tmpO + 24 → v.mem (wd p.env.work k) = u.mem (wd p.env.work k) :=
    fun k hk h1 h2 ↦ by
      rw [hv, setMem_wd _ (by nomega) (by omega), ite_no h2, setMem_wd _ (by nomega) (by omega),
        ite_no h1]
  have vreg : ∀ r, v.reg r = u.reg r := fun r ↦ by rw [hv]; rsimp
  -- μ, the table and its layer
  obtain ⟨-, -, hk0⟩ := hgv hS2
  rw [hwt] at hk0
  obtain ⟨-, hmu0, -, -⟩ := hk0
  refine wp_load (eval_atw (by rw [vreg, hbx]) 4) hmu0.2 ?_
  refine Ind.wp_lea fwTab (by rsimp; rw [vreg, hW]) rfl ?_
  refine Ind.wp_lea fwLay (by rsimp; rw [vreg, hW]) rfl ?_
  have hT0 : ∀ k < 2 * (mu + 1), (v.mem (wd (wd p.env.work fwTab) k)).isSome := fun k hk ↦ by
    rw [wd_wd]; exact hS2.ex hin (by nomega)
  refine NativeVm.Transcript.wp_then' (wp_fr (by decide) (subTableC_spec (mu := mu) (T := wd p.env.work fwTab) (L := wd p.env.work fwLay)
    hmu (by rsimp) (by rsimp) (by rsimp) (fun k hk ↦ by rsimp; exact hT0 k hk)
    (fun k hk ↦ by rsimp; rw [wd_wd]; exact hS2.ex hin (by nomega))
    (fitsW hfw (by nomega) (by nomega)) (fitsW hfw (by nomega) (by nomega))
    (disjW hfw (by nomega) (by nomega) (by nomega))))
    fun t1 ⟨⟨tb1, f1⟩, d1, rd1⟩ _ ↦ ?_
  simp only [QState.setReg_mem] at f1 d1
  rsimp at rd1
  have f1' : ∀ a, (∀ k < 94, a ≠ wd (wd p.env.work fwTab) k) → t1.mem a = v.mem a := fun a ha ↦
    f1 a (fun k hk ↦ ha k (by omega)) (fun k hk ↦ by
      have := ha (64 + k) (by omega)
      have e : wd (wd p.env.work fwLay) k = wd (wd p.env.work fwTab) (64 + k) := by
        rw [wd_wd, wd_wd, show fwLay + k = fwTab + (64 + k) by simp only [fwTab, fwLay]; omega]
      rw [e]; exact this)
  have hS3 : St p s0 t1 := hS2.next rd1 d1 (o := fwTab) (n := 94)
    (fun j hj ↦ by nomega) (by nomega) (by nomega) f1'
  have t1k : ∀ k, k < dataEnd → (k < fwTab ∨ fwTab + 94 ≤ k) → t1.mem (wd p.env.work k) = v.mem (wd p.env.work k) :=
    fun k hk hk' ↦ f1' _ fun j hj e ↦ by
      rw [wd_wd, wd_inj (by omega) (by nomega)] at e
      omega
  -- the claim's queries and weights
  refine wp_load (eval_cw hS3.rdi ctxWork) (hS3.wp hin hwp) ?_
  have hW4 : (t1.setReg .rbp p.env.work).reg .rbp = p.env.work := by rsimp
  refine ldw_wp hW4 (v := wd p.env.work gi) (by
    rsimp; rw [t1k _ (by nomega) (by nomega), vk _ (by nomega) (by nomega) (by nomega)]
    exact hcj) ?_
  obtain ⟨-, -, hk1⟩ := hgv hS3
  rw [hwt] at hk1
  obtain ⟨-, hmu1, hq1, hw1⟩ := hk1
  refine Ind.wp_lea (gluedQOff + 1) (b := wd p.env.work gi) (by rsimp) rfl ?_
  refine Ind.wp_lea (gluedWOff + 1) (b := wd p.env.work gi) (by rsimp) rfl ?_
  refine wp_load (eval_atw (B := wd p.env.work gi) (by rsimp) gluedQOff) (by rsimp; exact hq1.2.1.2) ?_
  refine wp_load (eval_atw (B := wd p.env.work gi) (by rsimp) gluedWOff) (by rsimp; exact hw1.2.1.2) ?_
  have hqs := hq1.1
  have hws := hw1.1
  rw [queryCap_val] at hqs hws
  refine Field.WP.then (minR_spec (x := ws.size) (y := qs.size) (by omega) (by omega)
    (by rsimp) (by rsimp)) fun t2 ⟨m2, r2, g2⟩ ↦ ?_
  rsimp at m2
  have hW5 : t2.reg .rbp = p.env.work := by rw [g2 .rbp (by decide)]; rsimp
  have hb5 : t2.reg .rbx = wd p.env.work gi := by rw [g2 .rbx (by decide)]; rsimp
  refine ldw_wp hW5 (v := wd p.env.work xo) (by
    rw [m2, t1k _ (by nomega) (by nomega)]; exact v23) ?_
  refine ldw_wp (by rsimp; exact hW5) (v := x.size.toUInt64) (by
    rsimp; rw [m2, t1k _ (by nomega) (by nomega)]; exact v24) ?_
  refine Ind.wp_lea fwTab (by rsimp; exact hW5) rfl ?_
  refine wp_load (eval_atw (B := wd p.env.work gi) (by rsimp; exact hb5) 4) (by rsimp; rw [m2]; exact hmu1.2) ?_
  refine Ind.wp_lea indO (by rsimp; exact hW5) rfl ?_
  fstep
  obtain ⟨m, hm⟩ : ∃ m, m = min ws.size qs.size := ⟨_, rfl⟩
  have hqa := wordarr_take hq1.2.2 m
  have hwa := ewarr_take hw1.2.2 m
  rw [wd_wd] at hqa hwa
  refine NativeVm.Transcript.wp_then' (wp_fr (by decide) (inducedC_spec (mu := mu) (qs := qs.extract 0 m)
    (ws := ws.extract 0 m) (pt := x) (Q := wd (wd p.env.work gi) (gluedQOff + 1))
    (Wt := wd (wd p.env.work gi) (gluedWOff + 1)) (Pt := wd p.env.work xo) (T := wd p.env.work fwTab) (S := wd p.env.work indO)
    hmu (by rsimp; rw [m2]; exact tb1) (by rsimp; rw [m2]; exact hqa)
    (by rsimp; rw [m2]; exact hwa) (by rsimp; rw [m2]; exact hxv hS3)
    (by simp only [Array.size_extract]; omega) (by simp only [Array.size_extract]; omega) (by omega)
    (by rsimp; rw [g2 .r13 (by decide)]; rsimp) (by rsimp; rw [g2 .r14 (by decide)]; rsimp) (by rsimp)
    (by rsimp) (by rsimp; rw [r2, Array.size_extract, show min m qs.size - 0 = min ws.size qs.size by omega])
    (by rsimp) (by rsimp) (by rsimp)
    (fun k hk ↦ by rsimp; rw [m2, wd_wd]; exact hS3.ex hin (by revert hk; nomega))
    (fitsW hfw (by nomega) (by nomega))
    (by rw [wd_wd]; exact fitsW hfw (by revert hgi; nomega) (by simp only [Array.size_extract]; revert hgi; nomega))
    (by rw [wd_wd]; exact fitsW hfw (by revert hgi; nomega) (by simp only [Array.size_extract]; revert hgi; nomega))
    (fitsW hfw (by revert hxo; nomega) (by revert hxo; nomega))
    (fitsW hfw (by nomega) (by nomega))
    (by rw [wd_wd]; exact disjW hfw (by nomega) (by revert hgi; nomega) (by simp only [Array.size_extract]; revert hgi; nomega))
    (by rw [wd_wd]; exact disjW hfw (by nomega) (by revert hgi; nomega) (by simp only [Array.size_extract]; revert hgi; nomega))
    (disjW hfw (by nomega) (by revert hxo; nomega) (by revert hxo; nomega))
    (disjW hfw (by nomega) (by nomega) (by nomega))))
    fun t3 ⟨⟨r9, r10, f3⟩, d3, rd3⟩ _ ↦ ?_
  rsimp at rd3 d3
  rw [m2] at d3
  rw [hm, inducedWeight_min] at r9 r10
  have f3' : ∀ a, (∀ k < 80, a ≠ wd (wd p.env.work indO) k) → t3.mem a = t1.mem a := fun a ha ↦ by
    rw [f3 a ha]; rsimp; rw [m2]
  have hS4 : St p s0 t3 := hS3.next (rd3.trans (g2 .rdi (by decide))) d3 (o := indO) (n := 80)
    (fun j hj ↦ by nomega) (by nomega) (by nomega) f3'
  refine WP.blk_nil ⟨hS4, r9, r10, fun k hk h23 hind ↦ ?_⟩
  rw [f3' _ fun j hj e ↦ by
      rw [wd_wd, wd_inj (by revert hk; nomega) (by nomega)] at e; revert hind; rw [e]; nomega,
    t1k _ hk (by revert hind; nomega), vk _ hk (by revert h23; nomega) (by revert h23; nomega)]

/-! ## One glued claim -/

/-- Read words through register updates and stores to the working area. -/
macro "fwsimp" : tactic => `(tactic| simp (disch := nomega) only [QState.setReg_mem,
  NativeVm.Transcript.setMem_wd_ne, NativeVm.Transcript.setMem_wd_eq, QState.setReg_reg,
  QState.setMem_reg, reduceCtorEq, ↓reduceIte, ite_true, ite_false])

/-- `St` through register updates and stores to `finalWF`. -/
macro "st_tac" : tactic => `(tactic| (repeat (first
  | with_reducible refine St.setReg ?_ (by decide) _
  | with_reducible refine St.store ?_ ‹_› (by nomega) (by nomega) (by nomega) _)))

theorem St.ofMem (h : St p s0 t) (hm : t'.mem = t.mem) (hr : t'.reg .rdi = t.reg .rdi) :
    St p s0 t' :=
  ⟨hr.trans h.rdi, h.fr.trans ⟨hr, fun a ↦ by rw [hm], fun a _ ↦ by rw [hm]⟩, by rw [hm]; exact h.on⟩

theorem toUInt64_sub' {a b : Nat} (h : b ≤ a) :
    a.toUInt64 - b.toUInt64 = (a - b).toUInt64 := by
  conv_lhs => rw [show a = (a - b) + b by omega]
  rw [← NativeVm.Transcript.toUInt64_add, UInt64.add_sub_cancel]

theorem ewat_of {m m' : UInt64 → Option UInt64} {W : UInt64} {o : Nat} {x : EW}
    (h0 : m' (wd W o) = m (wd W o)) (h1 : m' (wd W (o + 1)) = m (wd W (o + 1)))
    (hx : EWAt m (wd W o) x) : EWAt m' (wd W o) x := by
  refine ⟨by rw [h0]; exact hx.1, ?_⟩
  rw [wd_wd, h1, ← wd_wd]
  exact hx.2

/-- The glued claims' loop state after `j` claims. -/
structure GInv (p : Par) (s0 : QState) (gs : Array GluedClaimW) (point : Array EW) (b : EW)
    (j : Nat) (t : QState) : Prop where
  st : St p s0 t
  le : j ≤ gs.size
  ax : t.reg .rax = (gs.size - j).toUInt64
  cj : t.mem (wd p.env.work cJ) = some (wd p.env.work (gBase + gluedWords * j))
  ck : t.mem (wd p.env.work cK) = some (gs.size - j).toUInt64
  acc : EWAt t.mem (wd p.env.work (tmpO + 20)) (accW point gs b j)
  ps : t.mem (wd p.env.work (tmpO + 22)) = some point.size.toUInt64

/-- One glued claim: its weight at the point from its first fold round, times its scalar, added
to the sum at the temporaries `20`, `21`; the next claim's address and the count left. -/
def gluedC : Stmt := blk [
  ldW, ldw .rbx cJ,
  I (.load .rax (at_ .rbx (wdisp 2))), I (.add .rax .rax),
  I (.lea .rsi { base := .rbp, idx := some (.rax, .W64), disp := wdisp ptO }),
  ldw .rdx (tmpO + 22), I (.load .rcx (at_ .rbx (wdisp 2))), I (.sub .rdx .rcx),
  I (.load .rax (at_ .rbx (wdisp 3))),
  .ite (.cmp .eq .rax (.imm 0)) eqB indB,
  ldW, ldw .rbx cJ,
  I (.load .r11 (at_ .rbx (wdisp 0))), I (.load .r12 (at_ .rbx (wdisp 1))), emul,
  ldw .r11 (tmpO + 20), ldw .r12 (tmpO + 20 + 1), eadd,
  stw (tmpO + 20) .r9, stw (tmpO + 20 + 1) .r10,
  ldw .rbx cJ, I (.addi .rbx (wdisp gluedWords)), stw cJ .rbx,
  ldw .rax cK, I (.subi .rax 1), stw cK .rax]

theorem glued_at {sW : WhirStateW} {mem : UInt64 → Option UInt64} {W : UInt64}
    (hw : WhirAt mem (wd W whirR.off) sW) {j : Nat} (hj : j < sW.glued.size) :
    GluedAt mem (wd W (gBase + gluedWords * j)) sW.glued[j] := by
  have := hw.2.2.2.2 j hj
  rwa [wd_wd, show whirR.off + (whirGluedOff + 1 + gluedWords * j) = gBase + gluedWords * j by
    simp only [gBase]; omega] at this

/-- A glued claim's kind word. -/
def kindW (g : GluedClaimW) : UInt64 :=
  match g.weight with
  | .eq _ => 0
  | .induced _ _ _ => 1

theorem kind_at {mem : UInt64 → Option UInt64} {q : UInt64} {g : GluedClaimW} (h : GluedAt mem q g) :
    mem (wd q 3) = some (kindW g) := by
  obtain ⟨-, -, h3⟩ := h
  cases hw : g.weight <;> rw [hw] at h3 <;> simp only [kindW, hw] <;> exact h3.1

theorem gluedC_spec {F : QState → Prop} (hin : Inputs p.env p.inp s0.mem)
    (hwp : s0.mem (wd p.env.ctx ctxWork) = some p.env.work) {sW : WhirStateW} {point : Array EW}
    {b : EW} (hw : WhirAt s0.mem (wd p.env.work whirR.off) sW)
    (hpt : EWArr s0.mem (wd p.env.work ptO) point) (hpts : point.size ≤ 30)
    (hfs : ∀ g ∈ sW.glued, g.foldStart ≤ point.size)
    (hgm : ∀ g ∈ sW.glued, ∀ mu qs ws, g.weight = .induced mu qs ws → mu ≤ 30)
    {j : Nat} (hI : GInv p s0 sW.glued point b j t) (hj : j < sW.glued.size) :
    WP gluedC t (GInv p s0 sW.glued point b (j + 1)) F := by
  have hde := dataEnd_val
  have hn : sW.glued.size ≤ 10 := by have := hw.2.2.1; rwa [gluedCap_val] at this
  obtain ⟨g, hgdef⟩ : ∃ g, g = sW.glued[j] := ⟨_, rfl⟩
  obtain ⟨gi, hgin⟩ : ∃ gi, gi = 28450 + 758 * j := ⟨_, rfl⟩
  have hgidef : gBase + gluedWords * j = gi := by
    rw [hgin]; simp only [gBase, gluedWords_val, whir_off, whirGluedOff_val]
  have hgi' : 28450 ≤ gi ∧ gi + 758 ≤ 36030 := by omega
  have hgi : gBase ≤ gi ∧ gi + gluedWords ≤ whirR.off + whirWords := by
    simp only [gBase, gluedWords_val, whir_off, whirGluedOff_val, whirWords_val]; omega
  have hg := glued_at hw hj
  rw [← hgdef, hgidef] at hg
  have hcj : t.mem (wd p.env.work cJ) = some (wd p.env.work gi) := by rw [← hgidef]; exact hI.cj
  have hgw : ∀ k < gluedWords, ¬ finalWF (gi + k) := fun k hk ↦ by
    rw [gluedWords_val] at hk; nomega
  have hgv : ∀ {v : QState}, St p s0 v → GluedAt v.mem (wd p.env.work gi) g := fun hv ↦
    hv.glued hg (by nomega) (by nomega) hgw
  clear hgi
  have hgm' : g ∈ sW.glued := by rw [hgdef]; exact Array.getElem_mem hj
  obtain ⟨fs, hfsdef⟩ : ∃ fs, fs = g.foldStart := ⟨_, rfl⟩
  have hfs' : fs ≤ point.size := hfsdef ▸ hfs g hgm'
  obtain ⟨x, hxdef⟩ : ∃ x, x = point.extract fs point.size := ⟨_, rfl⟩
  have hxs : x.size = point.size - fs := by rw [hxdef]; simp
  have hxv : ∀ {v : QState}, St p s0 v → EWArr v.mem (wd p.env.work (ptO + 2 * fs)) x := fun hv ↦ by
    have := ewarr_drop (hv.ewarr hpt (by nomega) (by nomega) fun k hk ↦ by nomega) fs
    rwa [wd_wd, ← hxdef] at this
  have hS := hI.st
  unfold gluedC
  refine wp_load (eval_cw hS.rdi ctxWork) (hS.wp hin hwp) ?_
  have hW1 : (t.setReg .rbp p.env.work).reg .rbp = p.env.work := by rsimp
  refine ldw_wp hW1 (by rsimp; exact hcj) ?_
  obtain ⟨-, ⟨-, hfs0⟩, -⟩ := hgv hS
  rw [← hfsdef] at hfs0
  refine wp_load (eval_atw (B := wd p.env.work gi) (by rsimp) 2) (by rsimp; exact hfs0) ?_
  fstep
  refine wp_reg (s' := _) (by
    simp only [QInstr.step]
    rw [NativeVm.Transcript.eval_idx64 (b := p.env.work) (j := 0) (i := fs + fs)
      (by rsimp; rw [wd_zero]) (by rsimp; exact NativeVm.Transcript.toUInt64_add fs fs) ptO]) ?_
  refine ldw_wp (env := p.env) (by rsimp) (by rsimp; exact hI.ps) ?_
  refine wp_load (eval_atw (B := wd p.env.work gi) (by rsimp) 2) (by rsimp; exact hfs0) ?_
  fstep
  refine wp_load (eval_atw (B := wd p.env.work gi) (by rsimp) 3) (by rsimp; exact kind_at (hgv hS)) ?_
  -- the claim's weight
  have hxw : x.size ≤ 30 := by omega
  have hx0 : EWArr s0.mem (wd p.env.work (ptO + 2 * fs)) x := by
    have := ewarr_drop hpt fs
    rwa [wd_wd, ← hxdef] at this
  refine Field.WP.then (Q := fun u4 ↦ St p s0 u4 ∧ u4.reg .r9 = (g.weight.eval x).c0 ∧
      u4.reg .r10 = (g.weight.eval x).c1 ∧ ∀ k, k < dataEnd → ¬ (tmpO + 23 ≤ k ∧ k < tmpO + 25) →
        ¬ (indO ≤ k ∧ k < indO + 256) → u4.mem (wd p.env.work k) = t.mem (wd p.env.work k))
    ?_ fun u4 ⟨hS4, h49, h410, hk4⟩ ↦ ?_
  · have hSu : ∀ {u : QState}, u.mem = t.mem → u.reg .rdi = t.reg .rdi → St p s0 u :=
      fun hm hr ↦ hS.ofMem hm hr
    cases hwt : g.weight with
    | eq z =>
      refine NativeVm.Transcript.wp_ite_true (by simp [Cond.eval, Rhs.eval, kindW, hwt]; rfl) ?_
      obtain ⟨-, -, hk⟩ := hgv hS
      rw [hwt] at hk
      refine WP.mono (eqB_spec (z := z) (x := x) (G := wd p.env.work gi)
        (X := wd p.env.work (ptO + 2 * fs)) (hSu (by rsimp) (by rsimp)) (by rsimp)
        (by rsimp; rw [show 0 + (fs + fs) + ptO = ptO + 2 * fs by rw [Nat.zero_add, Nat.add_comm, two_mul]]) (by rsimp; rw [toUInt64_sub' hfs', hxs]) (by rsimp; exact hk.2)
        (by rsimp; exact hxv hS) hxw) ?_ fun _ h ↦ h
      rintro u4 ⟨h1, h2, h3, h4⟩
      refine ⟨h1, by rw [h2]; rfl, by rw [h3]; rfl, fun k _ _ _ ↦ by rw [h4]; rsimp⟩
    | induced mu qs ws =>
      refine NativeVm.Transcript.wp_ite_false (by simp [Cond.eval, Rhs.eval, kindW, hwt]; decide) ?_
      refine WP.mono (indB_spec (g := g) (mu := mu) (qs := qs) (ws := ws) (x := x) (gi := gi)
        (xo := ptO + 2 * fs) hin hwp (hSu (by rsimp) (by rsimp)) (by rsimp) (by rsimp)
        (by rsimp; exact hcj) (by rsimp; rw [show 0 + (fs + fs) + ptO = ptO + 2 * fs by rw [Nat.zero_add, Nat.add_comm, two_mul]]) (by rsimp; rw [toUInt64_sub' hfs', hxs])
        hg hwt (by simp only [gBase, gluedWords_val, whir_off, whirGluedOff_val, whirWords_val]; omega)
        (hgm g hgm' mu qs ws hwt) hx0 (by omega) hxw) ?_ fun _ h ↦ h
      rintro u4 ⟨h1, h2, h3, h4⟩
      refine ⟨h1, by rw [h2]; rfl, by rw [h3]; rfl, fun k hk h23 hind ↦ by rw [h4 k hk h23 hind]; rsimp⟩
  · have keep : ∀ k, k < dataEnd → (k = cJ ∨ k = cK ∨ k = tmpO + 20 ∨ k = tmpO + 21 ∨
        k = tmpO + 22) → u4.mem (wd p.env.work k) = t.mem (wd p.env.work k) := fun k hk h ↦
      hk4 k hk (by revert h; nomega) (by revert h; nomega)
    have hacc : accW point sW.glued b (j + 1) = g.weight.eval x * g.scalar +
        accW point sW.glued b j := by
      rw [accW_succ point b hj, ← hgdef, gstep, ← hfsdef, ← hxdef]
      apply EW.toE_injective
      simp only [EW.toE_add, EW.toE_mul]
      ring
    refine wp_load (eval_cw hS4.rdi ctxWork) (hS4.wp hin hwp) ?_
    refine ldw_wp (env := p.env) (by rsimp) (v := wd p.env.work gi)
      (by rsimp; rw [keep _ (by nomega) (.inl rfl)]; exact hcj) ?_
    obtain ⟨⟨sc0, sc1⟩, -, -⟩ := hgv hS4
    refine wp_load (eval_atw (B := wd p.env.work gi) (by rsimp) 0) (by rsimp; rw [wd_zero]; exact sc0) ?_
    refine wp_load (eval_atw (B := wd p.env.work gi) (by rsimp) 1) (by rsimp; exact sc1) ?_
    refine Field.WP.then (emul_spec _) fun t5 ⟨e5, m5, f5⟩ ↦ ?_
    rsimp at e5 m5
    rw [h49, h410, eOf_eq_toE, eOf_eq_toE, ← EW.toE_mul] at e5
    obtain ⟨l0, l1⟩ := lanes_of_eOf e5
    have hW6 : t5.reg .rbp = p.env.work := by rw [f5 .rbp (by decide)]; rsimp
    have hS5 : St p s0 t5 := hS4.ofMem m5 (by rw [f5 .rdi (by decide)]; rsimp)
    refine addM_wp (k := tmpO + 20) hW6 l0 l1
      (ewat_of (by rw [m5, keep _ (by nomega) (by nomega)])
        (by rw [m5, keep _ (by nomega) (by nomega)]) hI.acc) fun t6 m6 h9 h10 f6 ↦ ?_
    have hW7 : t6.reg .rbp = p.env.work := by rw [f6 .rbp (by decide), hW6]
    have hS6 : St p s0 t6 := hS5.ofMem m6 (f6 .rdi (by decide))
    have e6 : ∀ k, k < dataEnd → (k = cJ ∨ k = cK ∨ k = tmpO + 20 ∨ k = tmpO + 21 ∨
        k = tmpO + 22) → t6.mem (wd p.env.work k) = t.mem (wd p.env.work k) := fun k hk h ↦ by
      rw [m6, m5, keep k hk h]
    refine stA_wp hW7 (hS6.ex hin (by nomega)) (hS6.ex hin (by nomega)) ?_
    refine ldw_wp (by rsimp; exact hW7) (v := wd p.env.work gi)
      (by fwsimp; rw [e6 _ (by nomega) (.inl rfl)]; exact hcj) ?_
    fstep
    refine stw_wp (by rsimp; exact hW7) (St.ex (by st_tac; exact hS6) hin (by nomega)) ?_
    refine ldw_wp (by rsimp; exact hW7) (v := (sW.glued.size - j).toUInt64)
      (by fwsimp; rw [e6 _ (by nomega) (by nomega)]; exact hI.ck) ?_
    fstep
    refine stw_wp (by rsimp; exact hW7) (St.ex (by st_tac; exact hS6) hin (by nomega)) ?_
    apply WP.blk_nil
    refine ⟨by st_tac; exact hS6, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · rsimp; exact Sp.cnt_succ hj
    · fwsimp
      rw [NativeVm.Transcript.wdisp_toUInt64, NativeVm.Transcript.wd_add, Nat.mul_succ,
        ← Nat.add_assoc, hgidef]
    · fwsimp
      rw [Sp.cnt_succ hj]
    · rw [EWAt, wd_wd]
      fwsimp
      rw [h9, h10, hacc]
      exact ⟨rfl, rfl⟩
    · fwsimp
      rw [e6 _ (by nomega) (by nomega)]
      exact hI.ps

theorem wp_st {c : Stmt} {u : QState} {P E : QState → Prop} (h : St p s0 u) (hw : WP c u P E) :
    WP c u (fun u' ↦ St p s0 u ∧ P u') E :=
  WP.mono hw (fun _ h' ↦ ⟨h, h'⟩) fun _ h' ↦ h'

theorem shl_pow {mu : Nat} (h : mu ≤ 5) :
    (1 : UInt64) <<< (mu.toUInt64 &&& 63) = (2 ^ mu).toUInt64 := by
  interval_cases mu <;> decide

/-- The final product and check, the loop over the glued claims done. -/
def checkC : Stmt := blk [
  ldW, I (.movi .r15 1), ldw .rcx cMu, I (.shlcl .r15), leaw .r13 hiO, leaw .r14 mleO,
  leaw .rsi spO, emle,
  ldW, stw (tmpO + 26) .r9, stw (tmpO + 26 + 1) .r10,
  ldw .r9 (tmpO + 20), ldw .r10 (tmpO + 20 + 1), ldw .r11 (tmpO + 26), ldw .r12 (tmpO + 26 + 1),
  emul,
  ldw .r11 (tmpO + 14), ldw .r12 (tmpO + 14 + 1),
  failIf (.cmp .ne .r9 (.reg .r11)), failIf (.cmp .ne .r10 (.reg .r12))]

theorem checkC_spec {t : QState} (hin : Inputs p.env p.inp s0.mem)
    (hwp : s0.mem (wd p.env.ctx ctxWork) = some p.env.work) {w : EW} {tail folded : Array EW}
    {mu : Nat} {claim : EW} (hS : St p s0 t) (hacc : EWAt t.mem (wd p.env.work (tmpO + 20)) w)
    (hmu : NatAt s0.mem (wd p.env.work cMu) mu) (hmu5 : mu ≤ 5)
    (htail : EWArr s0.mem (wd p.env.work spO) tail) (hts : tail.size = mu)
    (hf : EWArr s0.mem (wd p.env.work hiO) folded) (hfs' : 2 ^ mu ≤ folded.size)
    (hfs'' : folded.size ≤ 64) (hc : EWAt s0.mem (wd p.env.work (tmpO + 14)) claim) :
    WP checkC t
      (fun s' ↦ (w * multilinearEval (folded.extract 0 (2 ^ mu)) tail == claim) = true ∧
        St p s0 s')
      (fun s' ↦ (w * multilinearEval (folded.extract 0 (2 ^ mu)) tail == claim) = false ∧
        St p s0 s') := by
  have hde := dataEnd_val
  have h32 : 2 ^ mu ≤ 32 := by
    calc 2 ^ mu ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hmu5
      _ = 32 := by norm_num
  have hlen : ((folded.extract 0 (2 ^ mu)).toList.map EW.toE).length = 2 ^ mu := by
    simp; omega
  have hts' : tail.size ≤ 5 := by omega
  unfold checkC
  refine wp_load (eval_cw hS.rdi ctxWork) (hS.wp hin hwp) ?_
  fstep
  refine ldw_wp (env := p.env) (by rsimp) (v := mu.toUInt64)
    (by rsimp; rw [hS.rd (by nomega) (by nomega) (by nomega)]; exact hmu.2) ?_
  fstep
  refine Ind.wp_lea hiO (b := p.env.work) (by rsimp) rfl ?_
  refine Ind.wp_lea mleO (b := p.env.work) (by rsimp) rfl ?_
  refine Ind.wp_lea spO (b := p.env.work) (by rsimp) rfl ?_
  refine NativeVm.Transcript.wp_then' (wp_st (p := p) (s0 := s0) (by st_tac; exact hS) (emle_spec (mle := (folded.extract 0 (2 ^ mu)).toList.map EW.toE)
    (point := tail.toList.map EW.toE) (src := wd p.env.work hiO) (work := wd p.env.work mleO)
    (pt := wd p.env.work spO) (by rsimp) (by rsimp) (by rsimp)
    (by rsimp; exact EWArr_iff_EArr.mp (ewarr_take (hS.ewarr hf (by nomega) (by nomega)
      fun k hk ↦ by nomega) _))
    (by rsimp; exact EWArr_iff_EArr.mp (hS.ewarr htail (by nomega) (by nomega) fun k hk ↦ by nomega))
    (by rsimp; rw [hlen, shl_pow hmu5])
    (by rw [hlen]; simp [hts]) (by simp; omega)
    (fun k hk ↦ by
      rsimp
      show (t.mem (wd (wd p.env.work mleO) k)).isSome
      rw [wd_wd]; exact hS.ex hin (by rw [hlen] at hk; nomega))
    (fun k j l l' hkj hj hl hl' e ↦ by
      change wd (wd p.env.work mleO) (2 * k + l) = wd (wd p.env.work hiO) (2 * j + l') at e
      rw [hlen] at hj
      rw [wd_wd, wd_wd, wd_inj (by nomega) (by nomega)] at e
      revert e; nomega)
    (fun k hk j hj e ↦ by
      change wd (wd p.env.work mleO) k = wd (wd p.env.work spO) j at e
      rw [hlen] at hk; simp only [List.length_map, Array.length_toList] at hj
      rw [wd_wd, wd_wd, wd_inj (by nomega) (by nomega)] at e
      revert e; nomega)))
    fun t2 h2 d2 ↦ ?_
  obtain ⟨hSu, e1, e2, e3⟩ := h2
  rw [← toE_multilinearEval] at e1
  obtain ⟨l0, l1⟩ := lanes_of_eOf e1
  have hS2 : St p s0 t2 := hSu.next (by rw [e3 .rdi (by decide)]) d2 (o := mleO) (n := 64)
    (fun j hj ↦ by nomega) (by nomega) (by nomega) fun a ha ↦ e2 a fun k hk ↦ by
      rw [hlen] at hk
      exact ha k (by omega)
  have t2k : ∀ k, k < dataEnd → (k < mleO ∨ mleO + 64 ≤ k) →
      t2.mem (wd p.env.work k) = t.mem (wd p.env.work k) := fun k hk h ↦ by
    rw [e2 _ fun j hj e ↦ ?_]
    · rsimp
    · change wd p.env.work k = wd (wd p.env.work mleO) j at e
      rw [hlen] at hj
      rw [wd_wd, wd_inj (by nomega) (by nomega)] at e
      revert h e; nomega
  refine wp_load (eval_cw hS2.rdi ctxWork) (hS2.wp hin hwp) ?_
  refine stA_wp (env := p.env) (k := tmpO + 26) (by rsimp) (by rsimp; exact hS2.ex hin (by nomega))
    (by rsimp; exact hS2.ex hin (by nomega)) ?_
  have hS3 : St p s0 (((t2.setReg .rbp p.env.work).setMem (wd p.env.work (tmpO + 26))
      ((t2.setReg .rbp p.env.work).reg .r9)).setMem (wd p.env.work (tmpO + 26 + 1))
      (((t2.setReg .rbp p.env.work).setMem (wd p.env.work (tmpO + 26))
      ((t2.setReg .rbp p.env.work).reg .r9)).reg .r10)) := by
    st_tac; exact hS2
  refine ldA_wp (k := tmpO + 20) (env := p.env) (by rsimp) (x := w) ?_ fun t3 m3 h39 h310 f3 ↦ ?_
  · rw [EWAt, wd_wd]
    fwsimp
    have a0 := t2k (tmpO + 20) (by nomega) (by nomega)
    have a1 := t2k (tmpO + 20 + 1) (by nomega) (by nomega)
    rw [a0, a1, ← wd_wd p.env.work (tmpO + 20) 1]
    exact hacc
  have hW3 : t3.reg .rbp = p.env.work := by rw [f3 .rbp (by decide)]; rsimp
  have hS3' : St p s0 t3 := hS3.ofMem m3 (f3 .rdi (by decide))
  refine mulM_wp (k := tmpO + 26) hW3 h39 h310
    (b := multilinearEval (folded.extract 0 (2 ^ mu)) tail) ?_ fun t4 m4 h49 h410 f4 ↦ ?_
  · rw [m3, EWAt, wd_wd]
    fwsimp
    exact ⟨by rw [l0], by rw [l1]⟩
  have hW4 : t4.reg .rbp = p.env.work := by rw [f4 .rbp (by simp), hW3]
  have hS4 : St p s0 t4 := hS3'.ofMem m4 (f4 .rdi (by simp))
  have c4 : ∀ k, k < dataEnd → (k = tmpO + 14 ∨ k = tmpO + 14 + 1) →
      t4.mem (wd p.env.work k) = s0.mem (wd p.env.work k) := fun k hk h ↦
    hS4.rd (by revert h; nomega) hk (by revert h; nomega)
  refine ldw_wp hW4 (v := claim.c0) (by rw [c4 (tmpO + 14) (by nomega) (.inl rfl)]; exact hc.1) ?_
  refine ldw_wp (by rsimp; exact hW4) (v := claim.c1)
    (by rsimp; rw [c4 (tmpO + 14 + 1) (by nomega) (.inr rfl), ← wd_wd]; exact hc.2) ?_
  have hS5 : St p s0 ((t4.setReg .r11 claim.c0).setReg .r12 claim.c1) := by st_tac; exact hS4
  by_cases h0 : (w * multilinearEval (folded.extract 0 (2 ^ mu)) tail).c0 = claim.c0
  · refine NativeVm.Transcript.wp_failIf (by
      rw [NativeVm.Transcript.cond_ne, NativeVm.Transcript.rhs_reg]; rsimp; rw [h49, h0]; simp) ?_
    by_cases h1 : (w * multilinearEval (folded.extract 0 (2 ^ mu)) tail).c1 = claim.c1
    · refine NativeVm.Transcript.wp_failIf (by
        rw [NativeVm.Transcript.cond_ne, NativeVm.Transcript.rhs_reg]; rsimp; rw [h410, h1]; simp) ?_
      exact WP.blk_nil ⟨(beq_true_iff _ _).mpr ⟨h0, h1⟩, hS5⟩
    · refine NativeVm.Transcript.wp_failIf_fail (by
        rw [NativeVm.Transcript.cond_ne, NativeVm.Transcript.rhs_reg]; rsimp; rw [h410]; simp [h1])
        ⟨Bool.eq_false_iff.mpr fun h ↦ h1 ((beq_true_iff _ _).mp h).2, hS5⟩
  · refine NativeVm.Transcript.wp_failIf_fail (by
      rw [NativeVm.Transcript.cond_ne, NativeVm.Transcript.rhs_reg]; rsimp; rw [h49]; simp [h0])
      ⟨Bool.eq_false_iff.mpr fun h ↦ h0 ((beq_true_iff _ _).mp h).1, hS5⟩

end FW

open FW

/-- **The final level's weight and last check**: `weight · multilinearEval (folded.extract 0 (2^μ))
tail == claim`, `.fail` exactly when it is false; `weight` the glued claims' fold from `b` at the
point at `ptO` (`finalWeightW`). -/
def finalWC : Stmt := blk [
  ldW,
  ldw .r9 (tmpO + 18), ldw .r10 (tmpO + 18 + 1), stw (tmpO + 20) .r9, stw (tmpO + 20 + 1) .r10,
  ldw .rax (whirR.off + 2), ldw .rcx cMu, I (.add .rax .rcx), stw (tmpO + 22) .rax,
  leaw .rax gBase, stw cJ .rax, ldw .rax (whirR.off + whirGluedOff), stw cK .rax,
  .loop (.test false .rax (.reg .rax)) gluedC,
  checkC]

/-- **`finalWC` checks the final level's weight.** -/
theorem finalWC_spec {p : Par} {s : QState} {sW : WhirStateW} {point tail folded : Array EW}
    {mu : Nat} {b claim : EW} (hrdi : s.reg .rdi = p.env.ctx) (hin : Inputs p.env p.inp s.mem)
    (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hw : WhirAt s.mem (whirR.at p.env.work) sW) (hpt : EWArr s.mem (wd p.env.work ptO) point)
    (hpts : point.size ≤ 30) (hpa : point.size = sW.alphas.size + mu)
    (hfs : ∀ g ∈ sW.glued, g.foldStart ≤ point.size)
    (hgm : ∀ g ∈ sW.glued, ∀ mu' qs ws, g.weight = .induced mu' qs ws → mu' ≤ 30)
    (hb : EWAt s.mem (wd p.env.work (tmpO + 18)) b) (hmu : NatAt s.mem (wd p.env.work cMu) mu)
    (hmu5 : mu ≤ 5) (htail : EWArr s.mem (wd p.env.work spO) tail) (hts : tail.size = mu)
    (hf : EWArr s.mem (wd p.env.work hiO) folded) (hfs' : 2 ^ mu ≤ folded.size)
    (hfs'' : folded.size ≤ 64) (hc : EWAt s.mem (wd p.env.work (tmpO + 14)) claim) :
    WP finalWC s
      (fun s' ↦ (sW.glued.foldl (fun w g ↦ w + g.scalar * g.weight.eval
          (point.extract g.foldStart point.size)) b *
          multilinearEval (folded.extract 0 (2 ^ mu)) tail == claim) = true ∧
        FrM p.env s s' ∧ Only p.env finalWF s.mem s'.mem)
      (fun s' ↦ (sW.glued.foldl (fun w g ↦ w + g.scalar * g.weight.eval
          (point.extract g.foldStart point.size)) b *
          multilinearEval (folded.extract 0 (2 ^ mu)) tail == claim) = false ∧
        FrM p.env s s' ∧ Only p.env finalWF s.mem s'.mem) := by
  have hde := dataEnd_val
  have hS0 : St p s s := ⟨hrdi, FrM.refl s, Only.refl _ _⟩
  rw [Region.at] at hw
  have hn : sW.glued.size ≤ 10 := by have := hw.2.2.1; rwa [gluedCap_val] at this
  unfold finalWC
  refine wp_load (eval_cw hrdi ctxWork) hwp ?_
  refine ldA_wp (k := tmpO + 18) (env := p.env) (by rsimp) (x := b) (by rsimp; exact hb)
    fun s2 m2 h9 h10 f2 ↦ ?_
  have hS2 : St p s s2 := (hS0.setReg (by decide) _).ofMem m2 (f2 .rdi (by decide))
  have hW2 : s2.reg .rbp = p.env.work := by rw [f2 .rbp (by decide)]; rsimp
  refine stA_wp hW2 (hS2.ex hin (by nomega)) (hS2.ex hin (by nomega)) ?_
  refine ldw_wp (by rsimp; exact hW2) (v := sW.alphas.size.toUInt64) (by
    fwsimp; rw [m2]; rsimp
    have := hw.2.1.2.1.2
    rwa [wd_wd] at this) ?_
  refine ldw_wp (by rsimp; exact hW2) (v := mu.toUInt64) (by fwsimp; rw [m2]; rsimp; exact hmu.2) ?_
  fstep
  refine stw_wp (by rsimp; exact hW2) (St.ex (by st_tac; exact hS2) hin (by nomega)) ?_
  refine Ind.wp_lea gBase (b := p.env.work) (by rsimp; exact hW2) rfl ?_
  refine stw_wp (by rsimp; exact hW2) (St.ex (by st_tac; exact hS2) hin (by nomega)) ?_
  refine ldw_wp (by rsimp; exact hW2) (v := sW.glued.size.toUInt64) (by
    fwsimp; rw [m2]; rsimp
    have := hw.2.2.2.1.2
    rwa [wd_wd] at this) ?_
  refine stw_wp (by rsimp; exact hW2) (St.ex (by st_tac; exact hS2) hin (by nomega)) ?_
  apply WP.blk_cons
  apply WP.loop (fun t ↦ ∃ j, GInv p s sW.glued point b j t) (fun t ↦ (t.reg .rax).toNat)
  · refine ⟨0, ⟨by st_tac; exact hS2, Nat.zero_le _, by rsimp; rw [Nat.sub_zero], ?_, ?_, ?_, ?_⟩⟩
    · fwsimp; rw [Nat.mul_zero, Nat.add_zero]
    · fwsimp; rw [Nat.sub_zero]
    · rw [EWAt, wd_wd]
      fwsimp
      rw [h9, h10]
      exact ⟨rfl, rfl⟩
    · fwsimp; rw [NativeVm.Transcript.toUInt64_add, hpa]
  · intro t ⟨j, hI⟩ hcd
    have hj : j < sW.glued.size := Sp.cnt_lt (hI.ax ▸ Sp.cond_true hcd)
    refine WP.mono (gluedC_spec hin hwp hw hpt hpts hfs hgm hI hj)
      (fun t' h' ↦ ⟨⟨j + 1, h'⟩, ?_⟩) fun _ h ↦ h
    rw [h'.ax, hI.ax]
    exact Sp.cnt_dec (by omega) hj
  · intro t ⟨j, hI⟩ hcd
    have hj : j = sW.glued.size := Sp.cnt_eq (by omega) hI.le (hI.ax ▸ Sp.cond_false hcd)
    subst hj
    have hacc := hI.acc
    rw [accW_full] at hacc
    exact WP.mono (checkC_spec hin hwp hI.st hacc hmu hmu5 htail hts hf hfs' hfs'' hc)
      (fun _ h ↦ ⟨h.1, h.2.fr, h.2.on⟩) fun _ h ↦ ⟨h.1, h.2.fr, h.2.on⟩

end NativeVm.Code.P7
