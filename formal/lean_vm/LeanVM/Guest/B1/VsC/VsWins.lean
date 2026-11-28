/-
  LeanVM.Guest.B1.VsC.VsWins

  `verify_sub`'s body as one window from its windows' uniform hypotheses.
-/

module

public import LeanVM.Guest.B1.VsC.VsWinData
public import LeanVM.Guest.B1.VsC.CalleesA

/-!
# `verify_sub`'s windows composed

The generated windows (`VsWinData.lean`: `wA`, `wB`, `wC`, the straight parts' windows) and the branches' arms
(`wI1`, `wI2z`, `wI2n`) compose by `segA_wins`, `seg_ite` and `seg_bind` into `vsSS`, the body before its
`ret []` (`vsBody_ss`): `vs_seg` gives `Seg … vsSS st K` on `vsVal rd0 w args` from `VsHyp`, the windows'
hypotheses in continuation form (each run's `RunHyp`, each call's callee `CallAtA`, each branch's taken arm's).
The atoms' equations come from the forward valuation (`vsVal_goodA`, …), the kernel checks from `wA_ok`, ….

`VsWinHyp al k bytecode seed`: at every placement `VsWindowsA` quantifies, an evaluation memory `rd0`, an
oracle `w` and the node's own words `Wo` (`WordsInA`) with `VsHyp` from the state `vsSt0` (the `HeapBuf`s from
`cur`, the callees from their end, `Wo` held, no data claimed), its final condition `vsPostA` from the
callees' posts. `vsWindowsA_of_hyp : VsWinHyp al k bytecode seed → VsWindowsA al k bytecode seed`, and
`vsWindowsFromCallees_of_hyp : VsWinHypFromCallees al k → VsWindowsFromCallees al k`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-! ## The branches' arms -/

/-- The least-height branch's arm when the `KECCAK` table's log is not `9`, as windows. -/
def wI1 : List W0 := [.run (atomsOf vsI1n)]

/-- The pointer width's branch, its flag set, as windows. -/
def wI2z : List W0 := [.run (atomsOf (vsI2z.take 5)), .call ((vsI2z.drop 5).headD (.ret []))]

/-- The pointer width's branch, its flag clear, as windows. -/
def wI2n : List W0 := [.run (atomsOf vsI2n)]

theorem wI1_flat : flatW wI1 = vsI1n := stmtsEqb_sound (by decide +kernel)

theorem wI2z_flat : flatW wI2z = vsI2z := stmtsEqb_sound (by decide +kernel)

theorem wI2n_flat : flatW wI2n = vsI2n := stmtsEqb_sound (by decide +kernel)

theorem wI_ok : winsOk vsRcL wI1 = true ∧ winsOk vsRcL wI2z = true ∧ winsOk vsRcL wI2n = true := by
  decide +kernel

theorem vs_sel_rc : vsRcL.lookup (.n 234) = none ∧ vsRcL.lookup (.n 471) = none := by decide +kernel

theorem vs_params_rc : ((fn% «verify_sub»).params.all fun v => (vsRcL.lookup v).isNone) = true := by
  decide +kernel

/-! ## The body before its `ret []` -/

/-- `verify_sub`'s body before its `ret []`. -/
noncomputable def vsSS : List Stmt :=
  vsA ++ ([.ite (.n 234) [] vsI1n] ++ (vsB ++ ([.ite (.n 471) vsI2z vsI2n] ++ vsC)))

theorem vsBody_ss : vsBody = vsSS ++ [.ret []] := by
  rw [vsBody_eq, vsSS]; simp only [List.append_assoc]

theorem winsOk_atom {rc : List (V × V)} {ws : List W0} (h : winsOk rc ws = true) {x : Atom} (hx : x ∈ atomsW ws) :
    overOk rc x = true := by
  simp only [atomsW, List.mem_flatMap] at hx
  obtain ⟨wd, hw, hx⟩ := hx
  have := List.all_eq_true.mp h wd hw
  cases wd with
  | run as => exact List.all_eq_true.mp this x hx
  | call s => simp at hx

section
variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
  (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop)

/-- **`verify_sub`'s windows' hypotheses** on `vsVal rd0 w args`, from the state `st`, `K` after them. -/
def VsHyp (st : St) (K : St → Prop) : Prop :=
  WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre wA st fun s1 =>
    IteHyp fs al cert k (vsVal rd0 w args) w Own R Pre (.n 234) [] wI1 s1 fun s2 =>
      WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre wB s2 fun s3 =>
        IteHyp fs al cert k (vsVal rd0 w args) w Own R Pre (.n 471) wI2z wI2n s3 fun s4 =>
          WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre wC s4 K

end

/-- **`verify_sub`'s body before its `ret []` is a window** from its windows' hypotheses. -/
theorem vs_seg {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k fp : ℕ} {rd0 : Reader}
    {w : ℕ → E} {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop} {st : St} {K : St → Prop}
    (ha : args.length = 6) (h : VsHyp fs al cert k rd0 w args Own R Pre st K) :
    Seg fs al cert k "verify_sub" fp (vsVal rd0 w args) Own R Pre vsSS st K := by
  have okA : winsOk vsRcs wA = true := by rw [vsRcs_eq]; exact wA_ok
  have okB : winsOk vsRcs wB = true := by rw [vsRcs_eq]; exact wB_ok
  have okC : winsOk vsRcs wC = true := by rw [vsRcs_eq]; exact wC_ok
  have okI1 : winsOk vsRcs wI1 = true := by rw [vsRcs_eq]; exact wI_ok.1
  have okI2z : winsOk vsRcs wI2z = true := by rw [vsRcs_eq]; exact wI_ok.2.1
  have okI2n : winsOk vsRcs wI2n = true := by rw [vsRcs_eq]; exact wI_ok.2.2
  have r234 : vsRcs.lookup (.n 234) = none := by rw [vsRcs_eq]; exact vs_sel_rc.1
  have r471 : vsRcs.lookup (.n 471) = none := by rw [vsRcs_eq]; exact vs_sel_rc.2
  have gA : ∀ x ∈ atomsW wA, ∃ S, Good rd0 S w (vsVal rd0 w args) (fixA x) := fun x hx => by
    have hm := mem_atomsW hx
    rw [wA_flat] at hm
    exact ⟨_, vsVal_goodA ha (fixS (.atom x)) (List.mem_map_of_mem hm)⟩
  have gB : ∀ x ∈ atomsW wB, ∃ S, Good rd0 S w (vsVal rd0 w args) (fixA x) := fun x hx => by
    have hm := mem_atomsW hx
    rw [wB_flat] at hm
    exact ⟨_, good_fixA (winsOk_atom okB hx) (vsVal_goodB ha (.atom x) hm)⟩
  have gC : ∀ x ∈ atomsW wC, ∃ S, Good rd0 S w (vsVal rd0 w args) (fixA x) := fun x hx => by
    have hm := mem_atomsW hx
    rw [wC_flat] at hm
    exact ⟨_, good_fixA (winsOk_atom okC hx) (vsVal_goodC ha (.atom x) hm)⟩
  have gI1 : vsVal rd0 w args (.n 234) ≠ 0 → ∀ x ∈ atomsW wI1, ∃ S, Good rd0 S w (vsVal rd0 w args) (fixA x) :=
    fun h0 x hx => by
      have hm := mem_atomsW hx
      rw [wI1_flat] at hm
      exact ⟨_, vsVal_goodI1 ha h0 (fixS (.atom x)) (List.mem_map_of_mem hm)⟩
  have gI2z : vsVal rd0 w args (.n 471) = 0 → ∀ x ∈ atomsW wI2z, ∃ S, Good rd0 S w (vsVal rd0 w args) (fixA x) :=
    fun h0 x hx => by
      have hm := mem_atomsW hx
      rw [wI2z_flat] at hm
      exact ⟨_, good_fixA (winsOk_atom okI2z hx) (vsVal_goodI2z ha h0 (.atom x) hm)⟩
  have gI2n : vsVal rd0 w args (.n 471) ≠ 0 → ∀ x ∈ atomsW wI2n, ∃ S, Good rd0 S w (vsVal rd0 w args) (fixA x) :=
    fun h0 x hx => by
      have hm := mem_atomsW hx
      rw [wI2n_flat] at hm
      exact ⟨_, good_fixA (winsOk_atom okI2n hx) (vsVal_goodI2n ha h0 (.atom x) hm)⟩
  rw [VsHyp] at h
  rw [vsSS]
  have sA := segA_wins (f := "verify_sub") (fp := fp) wA st _ okA gA h
  rw [wA_flat] at sA
  refine seg_bind (seg_mono sA fun s1 h1 => ?_)
  have s1' := seg_ite (f := "verify_sub") (fp := fp) r234 (fun _ => ⟨rfl, fun x hx => by simp [atomsW] at hx⟩)
    (fun h0 => ⟨okI1, gI1 h0⟩) h1
  rw [flatW_nil, wI1_flat] at s1'
  refine seg_bind (seg_mono s1' fun s2 h2 => ?_)
  have sB := segA_wins (f := "verify_sub") (fp := fp) wB s2 _ okB gB h2
  rw [wB_flat] at sB
  refine seg_bind (seg_mono sB fun s3 h3 => ?_)
  have s3' := seg_ite (f := "verify_sub") (fp := fp) r471 (fun h0 => ⟨okI2z, gI2z h0⟩) (fun h0 => ⟨okI2n, gI2n h0⟩) h3
  rw [wI2z_flat, wI2n_flat] at s3'
  refine seg_bind (seg_mono s3' fun s4 h4 => ?_)
  have sC := segA_wins (f := "verify_sub") (fp := fp) wC s4 K okC gC h4
  rwa [wC_flat] at sC

/-! ## `VsWindowsA` from the windows' hypotheses -/

/-- The events of a block that falls through. -/
def outEvs : Out → List Ev
  | .fall es => es
  | _ => []

/-- `verify_sub`'s events on `σ0` before its `ret []`. -/
noncomputable def vsEs (σ0 : Val) : List Ev := outEvs (walk σ0 vsSS)

/-- `verify_sub`'s forward valuation at a placement's arguments. -/
noncomputable abbrev vsσ (rd0 : Reader) (w : ℕ → E) (seed : Digest) (c : Child) (qt qo : ℕ) : Val :=
  vsVal rd0 w (vsArgs seed c (ptrAt qt) (ptrAt qo))

/-- The state `verify_sub`'s windows start from: its `HeapBuf`s from `cur`, its callees from their end,
its own words `Wo` held, no data claimed, no callee yet. -/
noncomputable def vsSt0 (σ0 : Val) (cur : ℕ) (Wo : Words) : St :=
  ⟨cur, cur + (allocs σ0 (vsEs σ0)).sum, fun rd => HoldsWords rd Wo, fun _ => False, []⟩

/-- **What is left of `verify_sub`'s windows**: at every placement `VsWindowsA` quantifies, an evaluation
memory `rd0`, an oracle `w` and the node's own words `Wo`, its windows' hypotheses on `vsσ rd0 w seed c qt qo`
from `vsSt0`, ending, its callees' cursor within `2^40` of `cur` below `2^60`, where the callees' posts
give `vsPostA`. -/
def VsWinHyp (al : String → Bool) (k : ℕ) (bytecode : List K) (seed : Digest) : Prop :=
  ∀ (c : Child) (qt qo fp cur : ℕ), VsChildOk bytecode seed c → qt + expTabLen ≤ fp →
    qo + c.freshClaim.cells.length ≤ fp → fp + B2C.fs "verify_sub" ≤ cur →
    (∃ rd, vsPreA seed c qt qo rd) → cur < 2 ^ 60 →
    ∃ (rd0 : Reader) (w : ℕ → E) (Wo : Words),
      WordsInA Wo (fp + 2) (fp + B2C.fs "verify_sub") cur
        (cur + (allocs (vsσ rd0 w seed c qt qo) (vsEs (vsσ rd0 w seed c qt qo))).sum) ∧
      VsHyp B2C.fs al B2C.cert k rd0 w (vsArgs seed c (ptrAt qt) (ptrAt qo))
        (ownData B2C.cert fp cur "verify_sub" (allocs (vsσ rd0 w seed c qt qo) (vsEs (vsσ rd0 w seed c qt qo)))
          (vsEs (vsσ rd0 w seed c qt qo)))
        (vsRegion qt qo c.freshClaim.cells.length) (vsPreA seed c qt qo) (vsSt0 (vsσ rd0 w seed c qt qo) cur Wo)
        fun st => (cur < 2 ^ 60 → st.kc ≤ cur + 2 ^ 40) ∧ ∀ rd, LowDef k rd → vsPreA seed c qt qo rd → st.O rd → ∀ ts,
          Tree.KidsValid coreProgram rd (rdOver (vsσ rd0 w seed c qt qo) rd) (calls (vsEs (vsσ rd0 w seed c qt qo))) ts →
          KidsPost rd st.Qs (calls (vsEs (vsσ rd0 w seed c qt qo))) ts →
          vsPostA bytecode seed c rd (.node "verify_sub" (rdOver (vsσ rd0 w seed c qt qo) rd)
            (allocs (vsσ rd0 w seed c qt qo) (vsEs (vsσ rd0 w seed c qt qo))) ts)

/-- **`verify_sub`'s window from its windows' hypotheses.** -/
theorem vsWindowsA_of_hyp {al : String → Bool} {k : ℕ} {bytecode : List K} {seed : Digest}
    (h : VsWinHyp al k bytecode seed) : VsWindowsA al k bytecode seed := by
  intro c qt qo fp cur hc ht ho hfc hP hcur
  obtain ⟨rd0, w, Wo, hWo, hH⟩ := h c qt qo fp cur hc ht ho hfc hP hcur
  have ha : (vsArgs seed c (ptrAt qt) (ptrAt qo)).length = 6 := rfl
  obtain ⟨es, st', Qs, hw, hq, hseg, hkc, hK⟩ := vs_seg (fp := fp) ha hH
  have hes : vsEs (vsσ rd0 w seed c qt qo) = es := by
    have h1 : vsEs (vsσ rd0 w seed c qt qo) = outEvs (walk (vsσ rd0 w seed c qt qo) vsSS) := rfl
    exact h1.trans (congrArg outEvs hw)
  have hq' : st'.Qs = Qs := by rw [hq]; rfl
  have ha' : st'.a = cur + (allocs (vsσ rd0 w seed c qt qo) es).sum := hseg.1
  have e0 : (vsSt0 (vsσ rd0 w seed c qt qo) cur Wo).kc = cur + (allocs (vsσ rd0 w seed c qt qo) es).sum := by
    show cur + (allocs _ (vsEs _)).sum = _
    rw [hes]
  rw [hes] at hWo hK
  refine ⟨fn% «verify_sub», vsSS, vsσ rd0 w seed c qt qo, rdOver (vsσ rd0 w seed c qt qo), es, Wo, Qs, st'.O, st'.D,
    st'.kc, hkc, vs_loop, vs_find, vsBody_ss, hWo, ?_, fun rd _ _ _ => ?_, fun rd hl hp ho ts hv hk => ?_⟩
  · rw [hes, ha', e0] at hseg
    exact hseg
  · have hr : ∀ v ∈ (fn% «verify_sub»).params, rdOver (vsσ rd0 w seed c qt qo) rd v = vsσ rd0 w seed c qt qo v :=
      fun v hv => rdOver_eq (by
        rw [vsRcs_eq]; exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp vs_params_rc v hv))
    rw [List.map_congr_left hr]
    exact vsVal_params ha
  · rw [← hq'] at hk
    exact hK rd hl hp ho ts hv hk

/-- **What is left of `verify_sub`'s completeness**, as its windows' hypotheses: from its callees' placed
completeness, at every seed, on a memory floor `k ≥ 14`. -/
def VsWinHypFromCallees (al : String → Bool) (k : ℕ) : Prop :=
  14 ≤ k → VsCalleesCompleteA B2C.fs al B2C.cert k → ∀ seed, VsWinHyp al k guestBytecode seed

theorem vsWindowsFromCallees_of_hyp {al : String → Bool} {k : ℕ} (h : VsWinHypFromCallees al k) :
    VsWindowsFromCallees al k :=
  fun hk hc seed => vsWindowsA_of_hyp (h hk hc seed)

end
end LeanVM.Guest.B1.VsC
