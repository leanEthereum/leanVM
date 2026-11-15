/-
  LeanVM.Guest.EndExecRVtB

  `verify_tables`' table sumcheck's reads (`Res.vtB`), sound at the honest frames: the rounds loop's
  reads past its cursors lie in the stream, the copy loop's read of the challenges inside them.
-/

module

public import LeanVM.Guest.EndExecRVtL
public import LeanVM.Guest.EndExecRCld
public import LeanVM.Guest.Res.SubDefs

/-!
# The table sumcheck's reads

`stResB_of`: the read `c` words past a cursor base lies in the stream `st·[0, 8192)` once the base's
word is `st·g^q`, `q + c < 8192`. `vt_l10_top`: at an honest frame of `verify_tables_loop0`, its
record's cursor (cell `17`) and the cursor `sumcheck_round4`'s frame holds (`[19] + 3`, the first
call's frame, `FrameHolds.site`, its argument `FrameHolds.kid`) are `st·g^q` (`VtLQ`). `vt_l11_top`:
at an honest frame of `verify_tables_loop1`, cell `10` holds `g^(n - 1 - i)` (`Tables.vt_chi_index`)
below the bound `g^n` (`VtCQ`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1
open LeanVM.Guest.B2C (idxOf FrameHolds fsN fn_of_idx cellJ namedOf siteOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (vtB stResB vtcRes topAtoms)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

/-- **A read past a cursor base inside the stream**: the base's word is `st·g^q`, `q + c < 8192`. -/
theorem stResB_of {M : ℕ → E} {fp : ℕ} {cur st : Base} {c q : ℕ} {S : E}
    (hst : ∀ v, RBase M fp st v → v = S) (hcur : ∀ v, RBase M fp cur v → v = S * gen ^ q)
    (hq : q + c < 8192) : RRes M fp (stResB cur st c) := by
  refine ⟨0, 1, rfl, rfl, fun vq hvq jj _ hjj ↦ ⟨_, List.mem_singleton_self _, fun vb ylo yhi hvb hlo hhi ↦ ?_⟩⟩
  obtain rfl : jj = 0 := by omega
  change ylo = 0 at hlo
  change yhi = 8192 at hhi
  subst hlo hhi
  refine ⟨q + c, Nat.zero_le _, hq, ?_⟩
  obtain ⟨wq, ⟨u, w, hu, hw, rfl⟩, rfl⟩ := hvq
  obtain ⟨wb, ⟨u', w', hu', hw', rfl⟩, rfl⟩ := hvb
  change w = 1 at hw
  change w' = 1 at hw'
  subst hw hw'
  rw [hst _ hu', hcur _ hu]
  simp only [ofK_gpow]
  ring

theorem l10_idx : idxOf name% «verify_tables_loop0» = some (fn_idx% «verify_tables_loop0») := by
  decide +kernel

theorem l11_idx : idxOf name% «verify_tables_loop1» = some (fn_idx% «verify_tables_loop1») := by
  decide +kernel

/-- The rounds loop's atoms on every path: the record `rounds·x^7` and its cursor's load. -/
theorem l10_atoms_top :
    let as := topAtoms (coreOf (fn_idx% «verify_tables_loop0»)).body
    as.contains (.mul (.n 6) (.n 0) (.n 0)) = true ∧ as.contains (.mul (.n 7) (.n 6) (.n 0)) = true ∧
      as.contains (.mul (.n 8) (.n 7) (.n 7)) = true ∧ as.contains (.mul (.n 9) (.n 8) (.n 0)) = true ∧
      as.contains (.mul (.n 10) (.n 2) (.n 9)) = true ∧ as.contains (.load (.n 11) (.n 10) 5) = true := by
  decide +kernel

/-- The rounds loop's cells: the cursor's, and the first call's frame pointer's. -/
theorem l10_cells : cellJ (fn_idx% «verify_tables_loop0») (.n 11) = 17 ∧
    19 < fsN (fn_idx% «verify_tables_loop0») ∧
    ∃ s, siteOf (fn_idx% «verify_tables_loop0»)
      ⟨"sumcheck_round4", [.n 10, .n 11, .n 12, .n 3], [.n 13, .n 14, .n 15], true⟩ = some s ∧ s.q = 19 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (show (siteOf (fn_idx% «verify_tables_loop0»)
    ⟨"sumcheck_round4", [.n 10, .n 11, .n 12, .n 3], [.n 13, .n 14, .n 15], true⟩).isSome = true by
      decide +kernel)
  refine ⟨s, hs, ?_⟩
  have : (siteOf (fn_idx% «verify_tables_loop0»)
    ⟨"sumcheck_round4", [.n 10, .n 11, .n 12, .n 3], [.n 13, .n 14, .n 15], true⟩).map (fun s ↦ s.q) = some 19 := by
    decide +kernel
  rw [hs] at this
  exact Option.some.inj this

/-- **The rounds loop's first call is `sumcheck_round4`'s.** -/
theorem l10_calls0 {σ : Core.Val} {es : List Ev} {vs : List V}
    (hw : walk σ (fn% «verify_tables_loop0»).body = .ret es vs) :
    (calls es)[0]? = some ⟨"sumcheck_round4", [.n 10, .n 11, .n 12, .n 3], [.n 13, .n 14, .n 15], true⟩ := by
  obtain ⟨fn, hf, -, hb⟩ := Tables.l10Found
  obtain rfl : fn = fn% «verify_tables_loop0» := Option.some.inj (hf.symm.trans find_l10)
  rw [hb, Tables.l10Body] at hw
  simp only [Bridge.walk_atom_cons, walk_call_cons, Bridge.out_pre_pre] at hw
  obtain ⟨es', -, rfl⟩ := Bridge.pre_eq_ret hw
  rfl

/-- The copy loop's cells: the bound, the challenges, the index `g^(n - 1 - i)`. -/
theorem l11_cells : cellJ (fn_idx% «verify_tables_loop1») (.n 1) = 3 ∧
    cellJ (fn_idx% «verify_tables_loop1») (.n 3) = 5 ∧ cellJ (fn_idx% «verify_tables_loop1») (.n 7) = 10 ∧
    10 < fsN (fn_idx% «verify_tables_loop1») ∧ V.n 1 ∈ (coreOf (fn_idx% «verify_tables_loop1»)).params ∧
    V.n 3 ∈ (coreOf (fn_idx% «verify_tables_loop1»)).params ∧ Res.inFr (fn_idx% «verify_tables_loop1») 3 = true ∧
    Res.inFr (fn_idx% «verify_tables_loop1») 5 = true ∧
    (topAtoms (coreOf (fn_idx% «verify_tables_loop1»)).body).contains (.mul (.n 6) (.n 7) (.n 0)) = true := by
  decide +kernel

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

/-- **The rounds loop's reads past its cursors** lie in `verify_tables`' stream. -/
theorem vt_l10_top (t : TopAt A r K i e j) (hr : r.Ok) (hname : (coreOf j).name = name% «verify_tables_loop0»)
    {c : ℕ} (hc : c < 3) :
    RRes (refMem r.img) e.I.fp (stResB (.fr 17) (.hp 1 22) c) ∧
      RRes (refMem r.img) e.I.fp (stResB (.hp 19 3) (.hp 1 22) c) := by
  obtain ⟨f, bufs, kids, hJ, hfj, hfn⟩ := t.found
  rw [hname] at hfn
  subst hfn
  have hcj : coreOf j = fn% «verify_tables_loop0» := Option.some.inj (hfj.symm.trans find_l10)
  obtain rfl : j = fn_idx% «verify_tables_loop0» := by
    have := t.idx
    rw [hJ] at this
    exact Option.some.inj (this.symm.trans l10_idx)
  obtain ⟨a, jj, n, q, hhd, ha22, -, -, hjn, -, hld, hroom⟩ := vtLQ_all hr e.I t.inst e.σ bufs kids hJ
  obtain ⟨vs, hw, hF, hev⟩ := t.events hr
  -- the record and its cursor
  obtain ⟨t6, t7, t8, t9, t10, tl⟩ := l10_atoms_top
  have m6 : e.σ (.n 6) = e.σ (.n 0) * e.σ (.n 0) := hev _ (topAtoms_on_path hw (List.contains_iff_mem.mp t6))
  have m7 : e.σ (.n 7) = e.σ (.n 6) * e.σ (.n 0) := hev _ (topAtoms_on_path hw (List.contains_iff_mem.mp t7))
  have m8 : e.σ (.n 8) = e.σ (.n 7) * e.σ (.n 7) := hev _ (topAtoms_on_path hw (List.contains_iff_mem.mp t8))
  have m9 : e.σ (.n 9) = e.σ (.n 8) * e.σ (.n 0) := hev _ (topAtoms_on_path hw (List.contains_iff_mem.mp t9))
  have m10 : e.σ (.n 10) = e.σ (.n 2) * e.σ (.n 9) :=
    hev _ (topAtoms_on_path hw (List.contains_iff_mem.mp t10))
  have hl := topAtoms_on_path hw (List.contains_iff_mem.mp tl)
  have l11 : LoadHolds r.img.read (e.σ (.n 10)) 5 (e.σ (.n 11)) := hev _ hl
  have e10 : e.σ (.n 10) = e.σ (.n 2) * e.σ (.n 0) ^ 7 := by rw [m10, m9, m8, m7, m6]; ring
  rw [e10] at l11
  have ecur := loadHolds_unique l11 hld
  obtain ⟨h17, h19, s, hs, hsq⟩ := l10_cells
  have hfb := t.fb
  have hcm := t.cell hr hF (x := .n 11) (namedOf_atom hl (by simp [atomUses])) (by rw [h17]; omega)
    (by rw [h17]; omega)
  rw [h17] at hcm
  -- the stream
  have hT : refMem r.img (e.I.fp + 1) = ofK (Parameters.g ^ a) := by
    have := (ref_read hr (by omega) hF.hdr1).2
    rw [this, hhd]
  have hst : ∀ v, RBase (refMem r.img) e.I.fp (.hp 1 22) v → v = refMem r.img (a + 22) := by
    intro v hv
    obtain ⟨x, hxn, hxM⟩ := hv
    have hl0 : (refMem r.img (e.I.fp + 1)).limb 0 = Parameters.g ^ a := by rw [hT]; simp
    obtain rfl : x = a + 22 := names_uniq hxn (names_shift hl0 ha22)
    exact hxM.symm
  have hq : q + c < 8192 := by
    have : 3 ≤ 3 * (n - jj) := by omega
    omega
  refine ⟨stResB_of hst (fun v hv ↦ ?_) hq, stResB_of hst (fun v hv ↦ ?_) hq⟩
  · change refMem r.img (e.I.fp + 17) = v at hv
    rw [← hv, hcm, ecur]
  · -- `sumcheck_round4`'s frame and its cursor argument
    obtain ⟨x, hxn, hxM⟩ := hv
    have hc0 := l10_calls0 (by rw [← hcj]; exact hw)
    obtain ⟨kfp, hkfp⟩ : ∃ kfp, e.I.kidFps[0]? = some kfp := by
      have hl' := hF.len
      have : 0 < (calls (e.pre ++ e.es)).length := by
        rcases h : calls (e.pre ++ e.es) with _ | _
        · rw [h] at hc0; cases hc0
        · simp
      exact ⟨e.I.kidFps[0], List.getElem?_eq_getElem (by omega)⟩
    have hrd19 := (hF.site 0 _ kfp s hc0 hkfp hs).1 (by rw [hsq]; omega) (by rw [hsq]; exact h19)
    rw [hsq] at hrd19
    obtain ⟨-, hm19⟩ := ref_read hr (by omega) hrd19
    obtain ⟨-, -, hargs, -⟩ := hF.kid 0 _ kfp hc0 hkfp
    have h3 := hargs 1 (by simp)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h3
    have hxa : Parameters.addressOfIndex (kfp + (2 + 1)) = Parameters.addressOfIndex x := by
      have hy := hxn.1
      simp only [hm19, Mode.limb_mul_ofK, limb_ofK, Fin.isValue, Fin.val_zero, ↓reduceIte, addressOfIndex] at hy
      rw [← pow_add] at hy
      simpa [addressOfIndex] using hy
    rw [hxa] at h3
    obtain ⟨-, hmx⟩ := ref_read hr (by have := hxn.2; unfold maxCells at this; omega) h3
    rw [← hxM, hmx, ecur]

/-- **The copy loop's read of the challenges** lies inside them. -/
theorem vt_l11_top (t : TopAt A r K i e j) (hr : r.Ok) (hname : (coreOf j).name = name% «verify_tables_loop1») :
    RRes (refMem r.img) e.I.fp vtcRes := by
  obtain ⟨f, bufs, kids, hJ, hfj, hfn⟩ := t.found
  rw [hname] at hfn
  subst hfn
  have hcj : coreOf j = fn% «verify_tables_loop1» := Option.some.inj (hfj.symm.trans find_l11)
  obtain rfl : j = fn_idx% «verify_tables_loop1» := by
    have := t.idx
    rw [hJ] at this
    exact Option.some.inj (this.symm.trans l11_idx)
  obtain ⟨ii, n, h0, h1, h4, hin, hn⟩ := vtCQ_all hr e.I t.inst e.σ bufs kids hJ
  -- the index `g^(n - 1 - i)`
  obtain ⟨args, rets, hv⟩ := inst_valid' hr t.inst hJ
  obtain ⟨-, hb⟩ := Res.holds_of_valid hfs_vt hv find_l11
  obtain ⟨fn, hf, -, hbody⟩ := Tables.l11Found
  obtain rfl : fn = fn% «verify_tables_loop1» := Option.some.inj (hf.symm.trans find_l11)
  rw [hbody] at hb
  simp only [Tables.l11Body, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨c5, m6a, m6b, -⟩ := hb
  simp only [Atom.Holds] at c5 m6a m6b
  have hy : gen ^ n * Tables.vtWInvGen = e.σ (.n 7) * gen ^ ii := by rw [← h4, ← c5, ← m6a, m6b, h0]
  have e7 := Tables.vt_chi_index hin hy
  -- the cells
  obtain ⟨hc1, hc3, hc7, h10, hp1, hp3, hf3, hf5, tm⟩ := l11_cells
  obtain ⟨vs, hw, hF, -⟩ := t.events hr
  have hm := topAtoms_on_path hw (List.contains_iff_mem.mp tm)
  have hfb := t.fb
  have hm10 := t.cell hr hF (x := .n 7) (namedOf_atom hm (by simp [atomUses])) (by rw [hc7]; omega)
    (by rw [hc7]; omega)
  rw [hc7] at hm10
  have hm3 := t.param hr hp1 (by rw [hc1]; exact hf3)
  rw [hc1] at hm3
  have hm5 := t.param hr hp3 (by rw [hc3]; exact hf5)
  rw [hc3] at hm5
  -- the read inside the challenges
  refine ⟨0, 1, rfl, rfl, fun vq hvq jj _ hjj ↦ ⟨_, List.mem_singleton_self _, fun vb ylo yhi hvb hlo hhi ↦ ?_⟩⟩
  obtain rfl : jj = 0 := by omega
  change ylo = 0 at hlo
  subst hlo
  obtain ⟨v3, ee, hv3, hee, he62, hy⟩ := hhi
  change refMem r.img (e.I.fp + 3) = v3 at hv3
  have hen : ee = n := by
    rw [← hv3, hm3, h1, ← ofK_gpow] at hee
    exact (ofK_gpow_inj (by omega) (by omega) hee).symm
  refine ⟨n - 1 - ii, Nat.zero_le _, by omega, ?_⟩
  obtain ⟨wq, ⟨u, w, hu, ⟨u2, w2, hu2, hw2, rfl⟩, rfl⟩, rfl⟩ := hvq
  obtain ⟨wb, ⟨u', w', hu', hw', rfl⟩, rfl⟩ := hvb
  change w2 = 1 at hw2
  change w' = 1 at hw'
  subst hw2 hw'
  change refMem r.img (e.I.fp + 5) = u at hu
  change refMem r.img (e.I.fp + 10) = u2 at hu2
  change refMem r.img (e.I.fp + 5) = u' at hu'
  rw [← hu, ← hu2, ← hu', hm10, e7]
  simp only [ofK_gpow]
  ring

/-- **`verify_tables`' table sumcheck's reads at an honest frame.** -/
theorem vt_top (t : TopAt A r K i e j) (hr : r.Ok) {x : Mode.Res} (hx : vtB j x = true) :
    RRes (refMem r.img) e.I.fp x := by
  match x, hx with
  | .sub a bs, hx =>
    simp only [vtB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
    rcases hx with ⟨⟨hn, hc⟩, hx | hx⟩ | ⟨hn, hx⟩ <;> rw [hx]
    · exact (vt_l10_top t hr hn hc).1
    · exact (vt_l10_top t hr hn hc).2
    · exact vt_l11_top t hr hn
  | .lt _ _, hx => simp [vtB] at hx
  | .nz _, hx => simp [vtB] at hx
  | .name _, hx => simp [vtB] at hx

end

end

end LeanVM.Guest.EndExec
