module

public import NativeVm.Code.Phase4.Row
public import NativeVm.Code.Phase4.ReadN
public import NativeVm.Code.Phase4.Terms1
public import NativeVm.Code.Phase4.Next
public import NativeVm.Code.Phase4.Rows
public import NativeVm.Code.Phase4.Rounds

/-!
# The tables' loop

`termsC_refines`: `termsC` refines `tableTerms`: the loop's start (`termsInitC`), then a table per
pass (`tableC_refines`): its point and its evaluations' count to its entry of `evalsR`
(`rowPreC`), its evaluations read after them (`readN`), its weighted terms added to `oFIN`
(`termsC1`), the next table (`nextC`). The loop's state after `k` tables is `TInv`: the table's
index (`rcx`, `oTIX`) and addresses, the running sum at `oFIN`, the constraint cursor (`0` up to
`JUMP`), the tables done in `evalsR` (`EntryAt`). Whatever survives the loop's writes (`TStab`) is
kept, on either exit.
-/

@[expose] public section

namespace NativeVm.Code.P4

open Native NativeVm.Model NativeVm.Transcript NativeVm.Field LeanVM.Parameters

variable {env : Env}

/-- The words the tables' loop writes: the evaluations, the running sum, `JUMP`'s constraints and
the terms' sums, the loop's state and the widths. -/
def WT (k : Nat) : Prop :=
  (oE ≤ k ∧ k < oE + 1476) ∨ (oFIN ≤ k ∧ k < oFIN + 2) ∨ (oCV ≤ k ∧ k < oCV + 8) ∨
    (oTIX ≤ k ∧ k < oWID + 6)

/-- What the tables' loop keeps: anything that survives the phase's frame and the loop's writes. -/
def TStab (env : Env) (X : QState → Prop) : Prop :=
  ∀ s s', X s → Fr env [evalsR, scratchR] arrRegs s s' → WF env WT s s' → X s'

/-- Offsets compared, the offsets' names unfolded. -/
macro "tomega" : tactic => `(tactic| (
  (try simp only [WT, oE, oFIN, oCV, oTIX, oFPTR, oEPTR, oWID, oS, oL, oB, oXP, oWT, oPT, eS, evOff,
    formsStride, fW, Region.stop] at *)
  omega))

/-! ## Facts through the loop -/

/-- A range of the working area outside `W` is kept. -/
theorem WF.sameAt {W : Nat → Prop} {s s' : QState} (h : WF env W s s') {a n : Nat} (h1 : 69 ≤ a)
    (h2 : a + n ≤ 85438) (hW : ∀ k, W k → k < a ∨ a + n ≤ k) :
    Same s.mem s'.mem (wd env.work a) n := fun k hk ↦ by
  rw [wd_wd]
  exact h _ (by omega) (by omega) fun hw ↦ by have := hW _ hw; omega

theorem le_foldl_max (l : List Nat) (a : Nat) :
    a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp
  | cons y l ih =>
    simp only [List.foldl_cons, List.mem_cons]
    obtain ⟨h1, h2⟩ := ih (max a y)
    refine ⟨le_trans (Nat.le_max_left _ _) h1, fun x hx ↦ ?_⟩
    rcases hx with rfl | hx
    · exact le_trans (Nat.le_max_right _ _) h1
    · exact h2 x hx

theorem getD_le_foldl_max (heights : Array Nat) {k : Nat} (hk : k < heights.size) :
    heights.getD k 0 ≤ heights.foldl max 0 := by
  rw [← Array.foldl_toList, getD_eq_getElem' _ _ hk]
  exact (le_foldl_max _ 0).2 _ (Array.getElem_mem_toList ..)

theorem getD_push_lt {α : Type} (xs : Array α) (x d : α) {j : Nat} (hj : j < xs.size) :
    (xs.push x).getD j d = xs.getD j d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hj,
    Array.getElem?_eq_getElem hj]

theorem getD_push_eq {α : Type} (xs : Array α) (x d : α) : (xs.push x).getD xs.size d = x := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_size, Option.getD_some]

/-- The working area's address, from the context. -/
theorem ctxW {t : TState} {s : QState} (hc : CodeRel env t s) :
    s.mem (wd env.ctx ctxWork) = some (wd env.work 0) := by
  rw [wd_zero]; exact hc.layout.workPtr

/-- The loop's data. -/
structure TData where
  heights : Array Nat
  forms : Array (Array FormW)
  xi : EW
  weights : Array EW
  point : Array EW

/-- What the loop reads and never writes: the heights, the forms, `ξ`'s powers, the weights, the
point. -/
def TFix (env : Env) (d : TData) (s : QState) : Prop :=
  (∀ i < 6, s.mem (wd env.work (oL + 4 + i)) = some (d.heights.getD i 0).toUInt64) ∧
    (∀ t < 6, ∀ side < 3, FormAt s.mem (wd env.work (oB + formsStride * t + fW * side))
      ((d.forms.getD t #[]).getD side #[])) ∧
    EWArr s.mem (wd env.work oXP) (powers d.xi 5) ∧
    EWArr s.mem (wd env.work oWT) d.weights ∧
    EWArr s.mem (wd env.work oPT) d.point

theorem TFix.keep {d : TData} (hwsz : d.weights.size = 6) (hps : d.point.size ≤ 30)
    {W : Nat → Prop} {s s' : QState} (h : TFix env d s) (hw : WF env W s s')
    (hW : ∀ k, W k → WT k) : TFix env d s' := by
  obtain ⟨h1, h2, h3, h5, h6⟩ := h
  have hfw : formWords = 741 := formWords_val
  have hxs : (powers d.xi 5).size = 5 := powers_size _ _
  refine ⟨fun i hi ↦ hw.word (by tomega) (by tomega) (fun hk ↦ by have := hW _ hk; tomega) (h1 i hi),
    fun t ht side hs ↦ (h2 t ht side hs).congr (hw.sameAt (by tomega) (by rw [hfw]; tomega)
      fun k hk ↦ by have := hW _ hk; rw [hfw]; tomega), ?_, ?_, ?_⟩
  · exact EWArr.wf hw h3 (by tomega) (by rw [hxs]; tomega) fun i hi hk ↦ by
      have := hW _ hk; rw [hxs] at hi; tomega
  · exact EWArr.wf hw h5 (by tomega) (by rw [hwsz]; tomega) fun i hi hk ↦ by
      have := hW _ hk; rw [hwsz] at hi; tomega
  · exact EWArr.wf hw h6 (by tomega) (by tomega) fun i hi hk ↦ by have := hW _ hk; tomega

/-- Table `t`'s entry of `evalsR`: its point, its evaluations, as wide as the table. -/
def EntryAt (mem : UInt64 → Option UInt64) (w : UInt64) (t : Nat) (e : Array EW × Array EW) :
    Prop :=
  EVec mem (wd w (oE + eS * t)) tablePointCap e.1 ∧
    EVec mem (wd w (oE + eS * t + evOff)) widthCap e.2 ∧ e.2.size = widths.getD t 0

/-- The loop's accumulator: the constraint cursor, the running sum, the tables done. -/
abbrev TAcc : Type := Nat × EW × Array (Array EW × Array EW)

/-- What every block of a pass keeps: `X`, `TFix`, the words, the widths, the tables done. -/
def CarryA (env : Env) (X : QState → Prop) (d : TData) (k : Nat) (acc : TAcc) (s : QState) :
    Prop :=
  X s ∧ TFix env d s ∧ WS env s ∧
    (∀ i < 6, s.mem (wd env.work (oWID + i)) = some (widths.getD i 0).toUInt64) ∧
    ∀ j < k, EntryAt s.mem env.work j (acc.2.2.getD j (#[], #[]))

/-- The words a pass writes: its table's entry and the ones after, the running sum, `JUMP`'s
constraints and the terms' sums, the loop's index and addresses. -/
def WP1 (k j : Nat) : Prop :=
  (oE + eS * k ≤ j ∧ j < oE + 1476) ∨ (oFIN ≤ j ∧ j < oFIN + 2) ∨ (oCV ≤ j ∧ j < oCV + 8) ∨
    (oTIX ≤ j ∧ j < oTIX + 3)

theorem CarryA.keep {X : QState → Prop} (hX : TStab env X) {d : TData} (hwsz : d.weights.size = 6)
    (hps : d.point.size ≤ 30) {k : Nat} (hk6 : k ≤ 6) {acc : TAcc} {s s' : QState}
    (h : CarryA env X d k acc s)
    (hfr : Fr env [evalsR, scratchR] arrRegs s s') {W : Nat → Prop} (hw : WF env W s s')
    (hW : ∀ j, W j → WP1 k j) : CarryA env X d k acc s' := by
  obtain ⟨hx, hf, hws, hwid, hent⟩ := h
  have hWT : ∀ j, W j → WT j := fun j hj ↦ by have := hW j hj; unfold WP1 at this; tomega
  refine ⟨hX s s' hx hfr (hw.mono hWT), hf.keep hwsz hps hw hWT, Stab.wsome _ _ s s' hws hfr,
    fun i hi ↦ hw.word (by tomega) (by tomega) (fun hk ↦ by have := hW _ hk; unfold WP1 at this; tomega)
      (hwid i hi), fun j hj ↦ ?_⟩
  obtain ⟨e1, e2, e3⟩ := hent j hj
  have hv1 : vecWords tablePointCap = 61 := by decide
  have hv2 : vecWords widthCap = 185 := by decide
  refine ⟨e1.congr (hw.sameAt (by tomega) (by rw [hv1]; tomega) fun i hi ↦ ?_),
    e2.congr (hw.sameAt (by tomega) (by rw [hv2]; tomega) fun i hi ↦ ?_), e3⟩
  · have := hW _ hi; unfold WP1 at this; rw [hv1]; tomega
  · have := hW _ hi; unfold WP1 at this; rw [hv2]; tomega

/-- **The loop's state** after `k` tables. -/
def TInv (env : Env) (X : QState → Prop) (d : TData) (k : Nat) (acc : TAcc) (t : TState)
    (s : QState) : Prop :=
  CodeRel env t s ∧ CarryA env X d k acc s ∧ k ≤ 6 ∧ s.reg .rcx = k.toUInt64 ∧
    s.mem (wd env.work oTIX) = some k.toUInt64 ∧
    s.mem (wd env.work oFPTR) = some (wd env.work (oB + formsStride * k)) ∧
    s.mem (wd env.work oEPTR) = some (wd env.work (oE + eS * k)) ∧
    EWAt s.mem (wd env.work oFIN) acc.2.1 ∧ (k ≤ 4 → acc.1 = 0) ∧ acc.2.2.size = k

/-- A pass between its row's count and its terms: `CarryA`, the loop's words, the row's point and
count. -/
def RowMid (env : Env) (X : QState → Prop) (d : TData) (k : Nat) (acc : TAcc) (width : Nat)
    (s : QState) : Prop :=
  CarryA env X d k acc s ∧ s.mem (wd env.work oTIX) = some k.toUInt64 ∧
    s.mem (wd env.work oFPTR) = some (wd env.work (oB + formsStride * k)) ∧
    s.mem (wd env.work oEPTR) = some (wd env.work (oE + eS * k)) ∧
    EWAt s.mem (wd env.work oFIN) acc.2.1 ∧
    EVec s.mem (wd env.work (oE + eS * k)) tablePointCap (d.point.extract 0 (d.heights.getD k 0)) ∧
    NatAt s.mem (wd env.work (oE + eS * k + evOff)) width

/-- `RowMid` survives writes after the row's count. -/
theorem RowMid.keep {X : QState → Prop} (hX : TStab env X) {d : TData} (hwsz : d.weights.size = 6)
    (hps : d.point.size ≤ 30) {k width : Nat} (hk : k < 6) {acc : TAcc} {s s' : QState}
    (h : RowMid env X d k acc width s) (hfr : Fr env [evalsR, scratchR] arrRegs s s')
    {W : Nat → Prop} (hw : WF env W s s')
    (hW : ∀ j, W j → oE + eS * k + evOff + 1 ≤ j ∧ j < oE + 1476) :
    RowMid env X d k acc width s' := by
  obtain ⟨hc, h1, h2, h3, h5, h6, h7⟩ := h
  have hv1 : vecWords tablePointCap = 61 := by decide
  refine ⟨hc.keep hX hwsz hps (by omega) hfr hw fun j hj ↦ by have := hW j hj; unfold WP1; tomega,
    hw.word (by tomega) (by tomega) (fun hj ↦ by have := hW _ hj; tomega) h1,
    hw.word (by tomega) (by tomega) (fun hj ↦ by have := hW _ hj; tomega) h2,
    hw.word (by tomega) (by tomega) (fun hj ↦ by have := hW _ hj; tomega) h3,
    EWAt.wf hw h5 (by tomega) (by tomega) ⟨fun hj ↦ by have := hW _ hj; tomega,
      fun hj ↦ by have := hW _ hj; tomega⟩,
    h6.congr (hw.sameAt (by tomega) (by rw [hv1]; tomega) fun j hj ↦ by
      have := hW _ hj; rw [hv1]; tomega),
    NatAt.wf hw h7 (by tomega) (by tomega) fun hj ↦ by have := hW _ hj; tomega⟩

/-- A model step's code result: no model step, then `pure (g x)`. -/
theorem refines_bind_pure {α β : Type} {P : TState → QState → Prop} {c : Stmt} {m : VM α}
    {g : α → β} {Q : α → TState → QState → Prop} {Q' : β → TState → QState → Prop}
    {E : QState → Prop} (h : Refines P c m Q E) (hQ : ∀ x t s, Q x t s → Q' (g x) t s) :
    Refines P c (m >>= fun x ↦ pure (g x)) Q' E := fun t s hts ↦
  WP.mono (h t s hts) (fun _ ⟨x, t', hr, hq⟩ ↦ ⟨g x, t', by rw [Refines.run_bind_some hr]; rfl,
    hQ _ _ _ hq⟩) (fun _ ⟨hr, he⟩ ↦ ⟨Refines.run_bind_none hr, he⟩)

theorem evalsR_size : evalsR.size = 1476 := by decide

/-! ## A pass -/

/-- The scratch words `termsC1` and `nextC` write. -/
def WSc (j : Nat) : Prop :=
  (oFIN ≤ j ∧ j < oFIN + 2) ∨ (oCV ≤ j ∧ j < oCV + 8) ∨ (oTIX ≤ j ∧ j < oTIX + 3)

theorem WSc_in : InRs [evalsR, scratchR] WSc := fun j hj ↦ inS (by unfold WSc at hj; tomega)
  (by unfold WSc at hj; tomega)

/-- **One table.** -/
theorem tableC_refines (h4 : Env4 env) {X : QState → Prop} (hX : TStab env X) {d : TData}
    (hh : d.heights.size = 6) (hhb : ∀ i < 6, d.heights.getD i 0 ≤ 30)
    (hf3 : ∀ t < 6, (d.forms.getD t #[]).size = 3) (hps : d.point.size = d.heights.foldl max 0)
    (hwsz : d.weights.size = 6) {k : Nat} (hk : k < 6) (acc : TAcc) :
    Refines (TInv env X d k acc) tableC
      (tableTermsStep (cpOf d.xi) (fpOf d.xi) d.point acc
        (tablesW.getD k default, d.heights.getD k 0, d.forms.getD k #[], d.weights.getD k 0))
      (fun acc' t s ↦ TInv env X d (k + 1) acc' t s) X := by
  obtain ⟨cur, fin, out⟩ := acc
  have hk6 : k ≤ 6 := by omega
  have hph : d.heights.getD k 0 ≤ d.point.size := by rw [hps]; exact getD_le_foldl_max _ (by omega)
  have hp30 : d.point.size ≤ 30 := by rw [hps]; exact foldl_max_le _ hh hhb
  have hwd : widths.getD k 0 ≤ 92 := by unfold widths; interval_cases k <;> decide
  rw [tableTermsStep_eq, tablesW_width hk, tablesW_opcode hk]
  unfold tableC readRowC
  refine Refines.blk_cons (Q₁ := fun xs t s ↦ CodeRel env t s ∧
    (RowMid env X d k (cur, fin, out) (widths.getD k 0) s ∧ (k ≤ 4 → cur = 0) ∧ out.size = k) ∧
    WS env s ∧ xs.size = widths.getD k 0 ∧ EWArr s.mem (wd env.work (oE + eS * k + evOff + 1)) xs)
    ?_ fun xs ↦ ?_
  · refine Refines.pre_blk (P' := fun t s ↦ CodeRel env t s ∧
      (RowMid env X d k (cur, fin, out) (widths.getD k 0) s ∧ (k ≤ 4 → cur = 0) ∧ out.size = k) ∧
      WS env s ∧ s.reg .r12 = wd env.work (oE + eS * k + evOff + 1) ∧
      s.reg .r13 = (widths.getD k 0).toUInt64) ?_ ?_
    · rintro t s ⟨hc, hca, -, -, hix, hfp, hep, hfin, hcur, hsz⟩
      have hca' := hca
      obtain ⟨-, ⟨hhw, -, -, -, hpt⟩, hws, hwid, -⟩ := hca'
      refine WP.mono (WP.dom (rowPreC_spec (env := env) hc.rdi (ctxW hc) hws hk (hhb k hk) hwd hph
        hp30 hix hep (hhw k hk) (hwid k hk) hpt)) ?_ fun _ h ↦ h
      rintro s1 ⟨⟨hpv, hnat, h12, h13, w1, rf1⟩, d1⟩
      have hW1 : InRs [evalsR, scratchR]
          (fun j ↦ oE + eS * k ≤ j ∧ j < oE + eS * k + evOff + 1) :=
        fun j hj ↦ inE (by tomega) (by tomega)
      have fr1 : Fr env [evalsR, scratchR] arrRegs s s1 := Fr.ofWr w1 hW1 d1 rf1 (by decide)
      have wf1 := WF.ofWr (env := env) w1 fun j hj ↦ by tomega
      refine ⟨CodeRel.only hc h4 (by decide) (Only.ofWr w1 hW1) d1 (rf1 .rdi (by decide)),
        ⟨⟨hca.keep hX hwsz hp30 hk6 fr1 wf1 fun j hj ↦ by unfold WP1; tomega,
          wf1.word (by tomega) (by tomega) (fun hj ↦ by tomega) hix,
          wf1.word (by tomega) (by tomega) (fun hj ↦ by tomega) hfp,
          wf1.word (by tomega) (by tomega) (fun hj ↦ by tomega) hep,
          EWAt.wf wf1 hfin (by tomega) (by tomega) ⟨fun hj ↦ by tomega, fun hj ↦ by tomega⟩,
          hpv, hnat⟩, hcur, hsz⟩, WS.wr hws d1, h12, h13⟩
    · have hMine : Mine [⟨oE + eS * k + evOff + 1, 2 * widths.getD k 0⟩] := fun r hr ↦ by
        simp only [List.mem_singleton] at hr; subst hr
        rw [tWorkWords_val, dataEnd_val]; tomega
      exact Refines.mono (readN_refines h4 (a := oE + eS * k + evOff + 1) (n := widths.getD k 0)
        hMine (X := fun u ↦ RowMid env X d k (cur, fin, out) (widths.getD k 0) u ∧
          (k ≤ 4 → cur = 0) ∧ out.size = k)
        fun u u' ⟨hm, hcu, hsu⟩ hf ↦ ⟨hm.keep hX hwsz hp30 hk
          (hf.sub (fun r hr ↦ ⟨evalsR, by simp, by
            simp only [List.mem_singleton] at hr; subst hr
            unfold Region.Sub; rw [evalsR_off]; simp only [Region.stop, evalsR_off, evalsR_size]
            tomega⟩) (by decide))
          (WF.ofFr h4 hf hMine) (fun j ⟨r, hr, h1, h2⟩ ↦ by
            simp only [List.mem_singleton] at hr; subst hr; tomega), hcu, hsu⟩)
        (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) fun _ h ↦ h.1.1.1
  refine Refines.pure fun t s ⟨hc, ⟨⟨hca, hix, hfp, hep, hfin, hpv, hnat⟩, hcur, hsz⟩, hws, hxs, hea⟩ ↦ ?_
  have hca' := hca
  obtain ⟨-, ⟨-, hfa, hxp, hwt, -⟩, -, hwid, -⟩ := hca'
  refine WP.then (WP.dom (termsC1_spec h4 hc.rdi (ctxW hc) hws hk cur (fun h ↦ hcur (by omega)) hix
    hfp hep hwid d.xi hxp d.weights hwt hwsz (d.forms.getD k #[]) (hf3 k hk) (hfa k hk) xs hxs hea
    fin hfin)) fun s3 ⟨⟨hfin3, w3, rf3⟩, d3⟩ ↦ ?_
  have wf3 := WF.ofWr (env := env) w3 fun j hj ↦ by tomega
  have rdi3 : s3.reg .rdi = env.ctx := by rw [rf3 .rdi (by decide)]; exact hc.rdi
  have ctx3 : s3.mem (wd env.ctx ctxWork) = some (wd env.work 0) := by
    rw [w3.ctx h4 fun j hj ↦ by tomega]; exact ctxW hc
  refine WP.mono (WP.dom (nextC_spec rdi3 ctx3 (WS.wr hws d3)
    (wf3.word (by tomega) (by tomega) (fun hj ↦ by tomega) hix)
    (wf3.word (by tomega) (by tomega) (fun hj ↦ by tomega) hfp)
    (wf3.word (by tomega) (by tomega) (fun hj ↦ by tomega) hep))) ?_ fun _ h ↦ h
  rintro s4 ⟨⟨hix4, hfp4, hep4, hrcx4, w4, rf4⟩, d4⟩
  have w34 : Wr env.work WSc s s4 :=
    (w3.mono fun j hj ↦ by unfold WSc; tomega).trans (w4.mono fun j hj ↦ by unfold WSc; tomega)
  have d34 : DomEq s s4 := d3.trans d4
  have rf34 : RegsFrame arrRegs s s4 := rf_arr rf3 rf4
  have fr34 : Fr env [evalsR, scratchR] arrRegs s s4 := Fr.ofWr w34 WSc_in d34 rf34 (by decide)
  have wf34 := WF.ofWr (env := env) w34 fun j hj ↦ by unfold WSc at hj; tomega
  have hca4 := hca.keep hX hwsz hp30 hk6 fr34 wf34 fun j hj ↦ by unfold WSc at hj; unfold WP1; tomega
  have hv1 : vecWords tablePointCap = 61 := by decide
  refine ⟨CodeRel.only hc h4 (by decide) (Only.ofWr w34 WSc_in) d34 (rf34 .rdi (by decide)),
    ⟨hca4.1, hca4.2.1, hca4.2.2.1, hca4.2.2.2.1, fun j hj ↦ ?_⟩, by omega, hrcx4, hix4, hfp4, hep4,
    ?_, fun hk4 ↦ ?_, by rw [Array.size_push, hsz]⟩
  · rcases Nat.lt_or_ge j k with hjk | hjk
    · rw [getD_push_lt _ _ _ (by omega)]; exact hca4.2.2.2.2 j hjk
    · obtain rfl : j = k := by omega
      have he : (out.push (d.point.extract 0 (d.heights.getD j 0), xs)).getD j (#[], #[]) =
          (d.point.extract 0 (d.heights.getD j 0), xs) := by
        rw [show j = out.size from hsz.symm]; exact getD_push_eq _ _ _
      rw [he]
      have hnat4 : NatAt s4.mem (wd env.work (oE + eS * j + evOff)) xs.size := by
        rw [hxs]
        exact NatAt.wf wf34 hnat (by tomega) (by tomega) fun hi ↦ by unfold WSc at hi; tomega
      have hea4 : EWArr s4.mem (wd env.work (oE + eS * j + evOff + 1)) xs :=
        EWArr.wf wf34 hea (by tomega) (by rw [hxs]; tomega) fun i hi hi' ↦ by
          unfold WSc at hi'; rw [hxs] at hi; tomega
      refine ⟨hpv.congr (wf34.sameAt (by tomega) (by rw [hv1]; tomega) fun i hi ↦ by
          unfold WSc at hi; rw [hv1]; tomega), ⟨by rw [hxs]; unfold widthCap; omega, hnat4,
          by rw [wd_wd]; exact hea4⟩, hxs⟩
  · exact EWAt.wf (WF.ofWr (env := env) w4 fun j hj ↦ by tomega) hfin3 (by tomega) (by tomega)
      ⟨fun hj ↦ by tomega, fun hj ↦ by tomega⟩
  · rw [hcur (by omega), tablesW_nConstraints (by omega)]

/-! ## The loop -/

/-- **The tables.** -/
theorem termsC_refines (h4 : Env4 env) {X : QState → Prop} (hX : TStab env X)
    (heights : Array Nat) (hh : heights.size = 6) (hhb : ∀ i < 6, heights.getD i 0 ≤ 30)
    (forms : Array (Array FormW)) (hfs : forms.size = 6)
    (hf3 : ∀ t < 6, (forms.getD t #[]).size = 3)
    (xi : EW) (point : Array EW) (hps : point.size = heights.foldl max 0)
    (weights : Array EW) (hwsz : weights.size = 6) :
    Refines (fun t s ↦ CodeRel env t s ∧ X s ∧ WS env s ∧
        (∀ i < 6, s.mem (wd env.work (oL + 4 + i)) = some (heights.getD i 0).toUInt64) ∧
        (∀ t < 6, ∀ side < 3, FormAt s.mem (wd env.work (oB + formsStride * t + fW * side))
          ((forms.getD t #[]).getD side #[])) ∧
        EWArr s.mem (wd env.work oXP) (powers xi 5) ∧
        EWArr s.mem (wd env.work oWT) weights ∧
        EWArr s.mem (wd env.work oPT) point)
      termsC (tableTerms (cpOf xi) (fpOf xi) point (tablesW.zip (heights.zip (forms.zip weights))))
      (fun r t s ↦ CodeRel env t s ∧ X s ∧ WS env s ∧ EWAt s.mem (wd env.work oFIN) r.1 ∧
        EvalsAt s.mem (wd env.work oE) r.2 ∧
        ∀ t < 6, (r.2.getD t (#[], #[])).2.size = widths.getD t 0) X := by
  have hp30 : point.size ≤ 30 := by rw [hps]; exact foldl_max_le _ hh hhb
  rw [tableTerms_eq]
  unfold termsC
  refine Refines.pre_blk (P' := TInv env X ⟨heights, forms, xi, weights, point⟩ 0 (0, 0, #[]))
    (fun t s ⟨hc, hx, hws, hhw, hfa, hxp, hwt, hpt⟩ ↦ ?_) ?_
  · refine WP.mono (WP.dom (termsInitC_spec hc.rdi (ctxW hc) hws)) ?_ fun _ h ↦ h
    rintro s1 ⟨⟨hfin, hwid, hix, hfp, hep, hrcx, w1, rf1⟩, d1⟩
    have hW1 : InRs [evalsR, scratchR]
        (fun j ↦ (oFIN ≤ j ∧ j < oFIN + 2) ∨ (oTIX ≤ j ∧ j < oWID + 6)) :=
      fun j hj ↦ inS (by tomega) (by tomega)
    have fr1 := Fr.ofWr w1 hW1 d1 rf1 (by decide)
    have wf1 := WF.ofWr (env := env) w1 fun j hj ↦ by tomega
    exact ⟨CodeRel.only hc h4 (by decide) (Only.ofWr w1 hW1) d1 (rf1 .rdi (by decide)),
      ⟨hX s s1 hx fr1 (wf1.mono fun j hj ↦ by unfold WT; tomega),
        TFix.keep (d := ⟨heights, forms, xi, weights, point⟩) hwsz hp30 ⟨hhw, hfa, hxp, hwt, hpt⟩
          wf1 (fun j hj ↦ by unfold WT; tomega), WS.wr hws d1, hwid,
        fun j hj ↦ absurd hj (Nat.not_lt_zero _)⟩,
      by omega, hrcx, hix, hfp, hep, hfin, fun _ ↦ rfl, rfl⟩
  refine refines_bind_pure (Q := fun acc t s ↦
    TInv env X ⟨heights, forms, xi, weights, point⟩ 6 acc t s) ?_ ?_
  · have H := Refines.foldlM (l := (tablesW.zip (heights.zip (forms.zip weights))).toList)
      (f := tableTermsStep (cpOf xi) (fpOf xi) point) (cond := .cmp .ltu .rcx (.imm 6))
      (body := tableC) (E := X) (init := ((0 : Nat), (0 : EW), (#[] : Array (Array EW × Array EW))))
      (Inv := fun k acc t s ↦ TInv env X ⟨heights, forms, xi, weights, point⟩ k acc t s)
      (fun k acc t s h ↦ by
        rw [rows_length hh hfs hwsz,
          cond_ltu_imm h.2.2.2.1 (k := 6) (n := 6) rfl (by have := h.2.2.1; omega) (by omega)]
        exact decide_eq_true_iff)
      (fun k hk acc ↦ by
        rw [rows_get hh hfs hwsz hk]
        rw [rows_length hh hfs hwsz] at hk
        exact tableC_refines (d := ⟨heights, forms, xi, weights, point⟩) h4 hX hh hhb hf3 hps hwsz
          hk acc)
    rw [rows_length hh hfs hwsz] at H
    exact H
  · rintro ⟨cur, fin, out⟩ t s ⟨hc, ⟨hx, -, hws, -, hent⟩, -, -, -, -, -, hfin, -, hsz⟩
    refine ⟨hc, hx, hws, hfin, ⟨hsz, fun j hj ↦ ?_⟩, fun j hj ↦ (hent j hj).2.2⟩
    obtain ⟨e1, e2, -⟩ := hent j hj
    rw [wd_wd, wd_wd, evalStride_val, evOff_val, ← Nat.add_assoc]
    exact ⟨e1, e2⟩

end NativeVm.Code.P4
