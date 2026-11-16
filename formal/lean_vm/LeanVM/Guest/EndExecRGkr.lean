/-
  LeanVM.Guest.EndExecRGkr

  `verify_bus_gkr`'s residuals at its honest frames: its pair loop's reads (`Res.gkrStB`), the final
  point row's copy (`Res.vbgRowB`), and its layer loop's certificate (`Res.lyResB`, `ly_resCert`).
-/

module

public import LeanVM.Guest.EndExecRGkrL
public import LeanVM.Guest.EndExecRVkSt
public import LeanVM.Guest.Res.GkrDefs

/-!
# `verify_bus_gkr`'s residuals

* `gkrSt_top`: the pair loop's record holds the cursor `q` words into the layer loop's stream, which
  its header names, with room for its eight words (`PairQ`);
* `vbgRow_top`: the final point row read up to `g_bus_mu = g^d` lies in its `m = (d - 1) / 2` pairs
  and the two cells past them, `d ≤ 2m + 2` (`vbg_root_slot`, the range check `d < 33`);
* `ly_resCert`: the layer loop's residuals (`Res.lyResB` at each offset): the reads past the record
  the pairs end at (`8j` words past the slot's cursor) and past the last record (`4L`), inside the
  room `LyQ` leaves for the layer's `140` words; at the offsets of the calls of `gkr_rounds__L2` and
  `__L1` the frame's position reaches the call (`callInG`), so it is on the path and its callee's
  cursor argument is the pairs' end cursor (`kid_arg`); the next point row's run one index on
  (`lyExt_rres`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B1.Tables
open LeanVM.Guest.B2C (idxOf fsN fn_of_idx cellJ siteOf entryOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (topAtoms callInG gkrStB gkrStRes vbgRowB vbgRowRes lyResB lyExtRes stResB)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

/-! ## A block reaching a call -/

theorem callInG_atoms (f : String) (as bs : List V) (p : List Stmt) :
    ∀ xs : List Atom, callInG f as bs (xs.map Stmt.atom ++ p) = callInG f as bs p
  | [] => rfl
  | _ :: xs => by simp only [List.map_cons, List.cons_append, callInG]; exact callInG_atoms f as bs p xs

theorem callInG_sound {σ : Core.Val} {f : String} {as bs : List V} {ss : List Stmt} :
    ∀ {es vs}, walk σ ss = .ret es vs → callInG f as bs ss = true → Ev.call f as bs ∈ es := by
  induction ss with
  | nil => intro es vs _ hc; simp [callInG] at hc
  | cons s ss ih =>
    intro es vs h hc
    cases s
    case atom a =>
      rw [Bridge.walk_atom_cons] at h
      obtain ⟨es', h', rfl⟩ := Bridge.pre_eq_ret h
      exact List.mem_append_right _ (ih h' hc)
    case call f' a r =>
      rw [Bridge.walk_call_cons] at h
      obtain ⟨es', h', rfl⟩ := Bridge.pre_eq_ret h
      simp only [callInG, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
      rcases hc with ⟨⟨rfl, rfl⟩, rfl⟩ | hc
      · exact List.mem_append_left _ (List.mem_singleton_self _)
      · exact List.mem_append_right _ (ih h' hc)
    all_goals simp [callInG] at hc

/-! ## Words of products and exponents -/

section

variable {M : ℕ → E} {fp : ℕ}

theorem rmono_two {k o1 e1 o2 e2 : ℕ} {v : E} (h : RMono M fp ⟨0, k, [(.fr o1, e1), (.fr o2, e2)]⟩ v) :
    v = gen ^ k * M (fp + o1) ^ e1 * M (fp + o2) ^ e2 := by
  obtain ⟨w, ⟨u1, w1, hu1, ⟨u2, w2, hu2, hw2, rfl⟩, rfl⟩, rfl⟩ := h
  change M (fp + o1) = u1 at hu1
  change M (fp + o2) = u2 at hu2
  change w2 = 1 at hw2
  subst hu1 hu2 hw2
  simp only [ofK_gpow]
  ring

theorem ridx_frg {o a c y : ℕ} (h : M (fp + o) = gen ^ a) (ha : a < 2 ^ 62)
    (hy : RIdx M fp (.ex (.fr o) c) y) : y = a + c := by
  obtain ⟨v, e', hv, hve, he', rfl⟩ := hy
  change M (fp + o) = v at hv
  rw [h, hve, ← ofK_gpow] at hv
  have := ofK_gpow_inj (by omega) (by omega) hv
  omega

theorem ridx_frg_mk {o a c : ℕ} (h : M (fp + o) = gen ^ a) (ha : a < 2 ^ 62) :
    RIdx M fp (.ex (.fr o) c) (a + c) :=
  ⟨_, a, (show M (fp + o) = ofK (Parameters.g ^ a) by rw [h, ofK_gpow]), rfl, ha, rfl⟩

/-- **The final point row up to `g^d` inside its `m` pairs and the two cells past them.** -/
theorem vbgRow_rres {d m : ℕ} (h8 : M (fp + 8) = gen ^ d) (h398 : M (fp + 398) = gen ^ m)
    (hd : d < 2 ^ 62) (hm : m < 2 ^ 62) (hdm : d ≤ 2 * m + 2) : RRes M fp vbgRowRes := by
  unfold vbgRowRes Res.vbgRow
  refine ⟨0, d + 0, rfl, ridx_frg_mk h8 hd, fun vq hvq jj _ hjj ↦ ?_⟩
  by_cases h1 : jj < 2 * m
  · rcases Nat.mod_two_eq_zero_or_one jj with hp | hp
    · refine ⟨_, List.mem_cons_self, fun vb ylo yhi hvb hlo hhi ↦ ⟨jj / 2, ?_, ?_, ?_⟩⟩
      · change ylo = 0 at hlo; omega
      · rw [ridx_frg h398 hm hhi]; omega
      · rw [rmono_uniq hvq hvb, show 1 * jj + 0 = 2 * (jj / 2) + 0 by omega]
    · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun vb ylo yhi hvb hlo hhi ↦ ⟨jj / 2, ?_, ?_, ?_⟩⟩
      · change ylo = 0 at hlo; omega
      · rw [ridx_frg h398 hm hhi]; omega
      · rw [rmono_uniq hvq hvb, show 1 * jj + 0 = 2 * (jj / 2) + 1 by omega]
  · by_cases h2 : jj = 2 * m
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        fun vb ylo yhi hvb hlo hhi ↦ ⟨0, ?_, ?_, ?_⟩⟩
      · change ylo = 0 at hlo; omega
      · change yhi = 1 at hhi; omega
      · rw [rmono_two hvq, rmono_two hvb, h398, h2]
        simp only [ofK_gpow]
        ring
    · obtain rfl : jj = 2 * m + 1 := by omega
      refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
        fun vb ylo yhi hvb hlo hhi ↦ ⟨0, ?_, ?_, ?_⟩⟩
      · change ylo = 0 at hlo; omega
      · change yhi = 1 at hhi; omega
      · rw [rmono_two hvq, rmono_two hvb, h398]
        simp only [ofK_gpow]
        ring

/-- **The next point row by pairs, its first cell then the rest one index on.** -/
theorem lyExt_rres {d0 j : ℕ} (h2 : M (fp + 2) = gen ^ j) (hj : j < 2 ^ 62) : RRes M fp (lyExtRes d0) := by
  unfold lyExtRes Res.lyRow
  refine ⟨0, j + 1, rfl, ridx_frg_mk h2 hj, fun vq hvq jj _ hjj ↦ ?_⟩
  rcases Nat.eq_zero_or_pos jj with rfl | hpos
  · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun vb ylo yhi hvb hlo hhi ↦ ⟨0, ?_, ?_, ?_⟩⟩
    · change ylo = 0 at hlo; omega
    · change yhi = 1 at hhi; omega
    · rw [rmono_uniq hvq hvb]
  · obtain ⟨k, rfl⟩ : ∃ k, jj = k + 1 := ⟨jj - 1, by omega⟩
    refine ⟨_, List.mem_cons_self, fun vb ylo yhi hvb hlo hhi ↦ ⟨k, ?_, ?_, ?_⟩⟩
    · change ylo = 0 at hlo; omega
    · rw [ridx_frg h2 hj hhi]; omega
    · rw [rmono_two hvq, rmono_two hvb]
      simp only [ofK_gpow]
      ring

end

/-! ## Cells of the three functions -/

theorem pair_idx : idxOf name% «verify_bus_gkr_loop0_loop0» = some (fn_idx% «verify_bus_gkr_loop0_loop0») := by
  decide +kernel

theorem vbg_idx : idxOf name% «verify_bus_gkr» = some (fn_idx% «verify_bus_gkr») := by decide +kernel

theorem pair_hdr_cells : 2 ≤ cellJ (fn_idx% «verify_bus_gkr_loop0_loop0») (.n 13) := by decide +kernel

theorem vbg_cells : cellJ (fn_idx% «verify_bus_gkr») (.n 6) = 8 ∧ Res.inFr (fn_idx% «verify_bus_gkr») 8 = true ∧
    cellJ (fn_idx% «verify_bus_gkr») (.n 366) = 398 ∧ 398 < fsN (fn_idx% «verify_bus_gkr») ∧
    (topAtoms (fn% «verify_bus_gkr»).body).contains (.load (.n 366) (.n 365) 0) = true := by
  decide +kernel

theorem ly_cells : cellJ (fn_idx% «verify_bus_gkr_loop0») (.n 0) = 2 ∧
    Res.inFr (fn_idx% «verify_bus_gkr_loop0») 2 = true ∧ Res.inFr (fn_idx% «verify_bus_gkr_loop0») 11 = true ∧
    cellJ (fn_idx% «verify_bus_gkr_loop0») (.n 65) = 81 ∧ cellJ (fn_idx% «verify_bus_gkr_loop0») (.n 80) = 100 ∧
    100 < fsN (fn_idx% «verify_bus_gkr_loop0») ∧
    (topAtoms (fn% «verify_bus_gkr_loop0»).body).contains (.load (.n 65) (.n 64) 4310) = true ∧
    (topAtoms (fn% «verify_bus_gkr_loop0»).body).contains (.load (.n 80) (.n 74) 4310) = true := by
  decide +kernel

/-- The calls of `gkr_rounds__L2` and `__L1`: their callee frames' cells `86` and `91`. -/
theorem ly_rounds_sites :
    (siteOf (fn_idx% «verify_bus_gkr_loop0») ⟨"gkr_rounds__L2", [.n 64, .n 68, .n 65, .n 4, .n 9], [.n 69], true⟩).map
      (·.q) = some 86 ∧
    (siteOf (fn_idx% «verify_bus_gkr_loop0») ⟨"gkr_rounds__L1", [.n 64, .n 70, .n 65, .n 4, .n 9], [.n 71], true⟩).map
      (·.q) = some 91 ∧ 86 < fsN (fn_idx% «verify_bus_gkr_loop0») ∧ 91 < fsN (fn_idx% «verify_bus_gkr_loop0») := by
  decide +kernel

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

/-! ## The pair loop's reads -/

/-- **The pair loop's reads past its record's cursor** lie in the layer loop's stream. -/
theorem gkrSt_top (t : TopAt A r K i e j) (hr : r.Ok) {x : Mode.Res} (hx : gkrStB j x = true) :
    RRes (refMem r.img) e.I.fp x := by
  match x, hx with
  | .sub a bs, hx =>
    simp only [gkrStB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
    obtain ⟨⟨hname, hc⟩, hx⟩ := hx
    rw [hx]
    obtain ⟨f, bufs, kids, hJ, hfj, hfn⟩ := t.found
    rw [hname] at hfn
    subst hfn
    have hcj : coreOf j = fn% «verify_bus_gkr_loop0_loop0» := Option.some.inj (hfj.symm.trans find_pair)
    obtain rfl : j = fn_idx% «verify_bus_gkr_loop0_loop0» := by
      have := t.idx
      rw [hJ] at this
      exact Option.some.inj (this.symm.trans pair_idx)
    obtain ⟨a', k, n, q, hhd, ha11, h0, h1, hkn, hn, hld, hroom⟩ := pairQ_all hr e.I t.inst e.σ bufs kids hJ
    obtain ⟨vs, hw, hF, hev⟩ := t.events hr
    rw [hcj] at hw
    obtain ⟨e13, -⟩ := pair_next hw hev hld
    have hon := topAtoms_on_path hw (List.contains_iff_mem.mp
      (List.all_eq_true.mp pair_atoms (.load (.n 13) (.n 5) 4310) (by simp)))
    obtain ⟨hc17, hlt17⟩ := pair_cell13
    have hm := t.cell hr hF (x := .n 13) (namedOf_atom hon (by simp [atomUses]))
      (by rw [hc17]; omega) (by rw [hc17]; exact hlt17)
    rw [hc17] at hm
    have hfb := t.fb
    have hT : refMem r.img (e.I.fp + 1) = ofK (Parameters.g ^ a') := by
      have := (ref_read hr (by omega) hF.hdr1).2
      rw [this, hhd]
    refine stResB_of (S := refMem r.img (a' + 11)) (q := q) (fun v hv ↦ ?_) (fun v hv ↦ ?_) (by omega)
    · obtain ⟨y, hyn, hyM⟩ := hv
      have hl0 : (refMem r.img (e.I.fp + 1)).limb 0 = Parameters.g ^ a' := by rw [hT]; simp
      obtain rfl : y = a' + 11 := names_uniq hyn (names_shift hl0 ha11)
      exact hyM.symm
    · change refMem r.img (e.I.fp + 17) = v at hv
      rw [← hv, hm, e13]

/-! ## The final point row -/

/-- **The final point row's copy at an honest frame of `verify_bus_gkr`.** -/
theorem vbgRow_top (t : TopAt A r K i e j) (hr : r.Ok) {x : Mode.Res} (hx : vbgRowB j x = true) :
    RRes (refMem r.img) e.I.fp x := by
  simp only [vbgRowB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
  obtain ⟨hname, rfl⟩ := hx
  obtain ⟨f, bufs, kids, hJ, hfj, hfn⟩ := t.found
  rw [hname] at hfn
  subst hfn
  have hcj : coreOf j = fn% «verify_bus_gkr» := Option.some.inj (hfj.symm.trans find_vbg)
  obtain rfl : j = fn_idx% «verify_bus_gkr» := by
    have := t.idx
    rw [hJ] at this
    exact Option.some.inj (this.symm.trans vbg_idx)
  obtain ⟨args, rets, hv⟩ := inst_valid' hr t.inst hJ
  obtain ⟨-, hb⟩ := Res.holds_of_valid gkr_hfs hv hfj
  rw [hcj, vbg_body, holdsList_append, holdsList_noRet _ vbgPre_noRet] at hb
  obtain ⟨d, hd, hg, e366, -⟩ := vbg_root_slot (by have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size; omega) r.img hb.1
  obtain ⟨c6, f8, c366, f398, a366⟩ := vbg_cells
  obtain ⟨vs, hw, hF, -⟩ := t.events hr
  rw [hcj] at hw
  have h8 := t.param hr (p := .n 6) (by rw [hcj, vbg_params]; simp) (by rw [c6]; exact f8)
  rw [c6, hg] at h8
  have h398 := t.cell hr hF (x := .n 366) (namedOf_atom (topAtoms_on_path hw (List.contains_iff_mem.mp a366))
    (by simp [atomUses])) (by rw [c366]; omega) (by rw [c366]; exact f398)
  rw [c366, e366] at h398
  exact vbgRow_rres h8 h398 (by omega) (by omega) (by omega)

/-! ## The layer loop -/

/-- **The layer loop's frame**: its counter `g^j` below `g^m`, its stream, the pairs' end cursor
`8j` words past the slot's (cell `81`, `σ 65`), the last record's `4L` (cell `100`), the room. -/
theorem ly_top (t : TopAt A r K i e j) (hr : r.Ok) (hname : (coreOf j).name = name% «verify_bus_gkr_loop0») :
    j = fn_idx% «verify_bus_gkr_loop0» ∧ ∃ jj m sh q, refMem r.img (e.I.fp + 2) = gen ^ jj ∧ jj < m ∧ m ≤ 16 ∧
      sh < 2 ∧ refMem r.img (e.I.fp + 11) = e.σ (.n 9) ∧
      e.σ (.n 65) = e.σ (.n 9) * gen ^ (q + 8 * jj) ∧
      refMem r.img (e.I.fp + 81) = e.σ (.n 9) * gen ^ (q + 8 * jj) ∧
      refMem r.img (e.I.fp + 100) = e.σ (.n 9) * gen ^ (q + 4 * (2 * jj + 2 - sh)) ∧
      q + 140 * (m - jj) ≤ 8192 := by
  obtain ⟨f, bufs, kids, hJ, hfj, hfn⟩ := t.found
  rw [hname] at hfn
  subst hfn
  have hcj : coreOf j = fn% «verify_bus_gkr_loop0» := Option.some.inj (hfj.symm.trans find_ly)
  obtain rfl : j = fn_idx% «verify_bus_gkr_loop0» := by
    have := t.idx
    rw [hJ] at this
    exact Option.some.inj (this.symm.trans ly_idx)
  refine ⟨rfl, ?_⟩
  obtain ⟨jj, m, sh, q, h0, h1, hjm, hm, hsh, h2, h8, hcur, hroom⟩ := lyQ_all hr e.I t.inst e.σ bufs kids hJ
  obtain ⟨args, rets, hv⟩ := inst_valid' hr t.inst hJ
  obtain ⟨-, hb⟩ := Res.holds_of_valid gkr_hfs hv hfj
  rw [hcj, ly_body, holdsList_append, holdsList_noRet _ lyPre_noRet] at hb
  obtain ⟨-, -, e65, e80, -⟩ := ly_curs (fun _ _ _ h ↦ Res.KidRel.rel h) hb.1 (by omega) hsh h0 h2 h8 hcur
  obtain ⟨c0, f2, f11, c65, c80, f100, a65, a80⟩ := ly_cells
  obtain ⟨-, h9c⟩ := ly_cell9
  obtain ⟨vs, hw, hF, -⟩ := t.events hr
  rw [hcj] at hw
  have m2 := t.param hr (p := .n 0) (by rw [hcj, ly_params]; simp) (by rw [c0]; exact f2)
  have m11 := t.param hr (p := .n 9) (by rw [hcj, ly_params]; simp) (by rw [ly_cell9.1]; exact f11)
  have m81 := t.cell hr hF (x := .n 65) (namedOf_atom (topAtoms_on_path hw (List.contains_iff_mem.mp a65))
    (by simp [atomUses])) (by rw [c65]; omega) (by rw [c65]; omega)
  have m100 := t.cell hr hF (x := .n 80) (namedOf_atom (topAtoms_on_path hw (List.contains_iff_mem.mp a80))
    (by simp [atomUses])) (by rw [c80]; omega) (by rw [c80]; exact f100)
  rw [c0, h0] at m2
  rw [ly_cell9.1] at m11
  rw [c65, e65, mul_assoc, ← pow_add] at m81
  rw [c80, e80, mul_assoc, ← pow_add] at m100
  refine ⟨jj, m, sh, q, m2, hjm, hm, hsh, m11, by rw [e65, mul_assoc, ← pow_add], m81, m100, hroom⟩

/-- **A call on the path's callee's argument**, read through the site's cell. -/
theorem kid_arg (t : TopAt A r K i e j) (hr : r.Ok) {f : String} {as bs : List V}
    (hev : Ev.call f as bs ∈ e.pre ++ e.es) {q : ℕ} (hsq : (siteOf j ⟨f, as, bs, true⟩).map (·.q) = some q)
    (h2q : 2 ≤ q) (hqf : q < fsN j) {k : ℕ} (hk : k < as.length) :
    ∀ v, RBase (refMem r.img) e.I.fp (.hp q (2 + k)) v → v = e.σ as[k] := by
  obtain ⟨vs, hw, hF, -⟩ := t.events hr
  set c : Call := ⟨f, as, bs, true⟩ with hcdef
  have hcm : c ∈ calls (e.pre ++ e.es) := List.mem_filterMap.mpr ⟨_, hev, rfl⟩
  obtain ⟨ii, hii⟩ := List.mem_iff_getElem?.mp hcm
  obtain ⟨kfp, hkfp⟩ : ∃ kfp, e.I.kidFps[ii]? = some kfp := by
    have hl := hF.len
    have : ii < (calls (e.pre ++ e.es)).length := (List.getElem?_eq_some_iff.mp hii).1
    exact ⟨e.I.kidFps[ii], List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨st, hst, hstq⟩ := Option.map_eq_some_iff.mp hsq
  have hrdq := (hF.site ii c kfp st hii hkfp hst).1 (by rw [hstq]; exact h2q) (by rw [hstq]; exact hqf)
  rw [hstq] at hrdq
  obtain ⟨-, hmq⟩ := ref_read hr (by have := t.fb; omega) hrdq
  obtain ⟨-, -, hargs, -⟩ := hF.kid ii c kfp hii hkfp
  have ha := hargs k hk
  intro v hv
  obtain ⟨x, hxn, hxM⟩ := hv
  have hxa : Parameters.addressOfIndex (kfp + (2 + k)) = Parameters.addressOfIndex x := by
    have hy := hxn.1
    simp only [hmq, Mode.limb_mul_ofK, limb_ofK, Fin.isValue, Fin.val_zero, ↓reduceIte, addressOfIndex] at hy
    rw [← pow_add] at hy
    simpa [addressOfIndex] using hy
  rw [hxa] at ha
  obtain ⟨-, hmx⟩ := ref_read hr (by have := hxn.2; unfold maxCells at this; omega) ha
  rw [← hxM, hmx]

end

/-! ## The layer loop's certificate -/

/-- **The layer loop's residuals at its honest frames**, its certificate's residuals in `Res.lyResB`
at their offsets, its entries `jf`'s and `alignA`'s. -/
theorem ly_resCert {Kc : Mode.Cert}
    (hres : ∀ i < Kc.code.length, ∀ x ∈ (Kc.F.res.get i).getD [], lyResB i x = true)
    (hent : (fnOf (fn_idx% «verify_bus_gkr_loop0»)).entryPc = Kc.F.entry ∧
      Bridge.entOf Bridge.alignA name% «verify_bus_gkr_loop0» = Kc.F.entry)
    (h70 : (Bridge.alOf Bridge.alignA name% «verify_bus_gkr_loop0» 70).map
      (callInG "gkr_rounds__L2" [.n 64, .n 68, .n 65, .n 4, .n 9] [.n 69]) = some true)
    (h83 : (Bridge.alOf Bridge.alignA name% «verify_bus_gkr_loop0» 83).map
      (callInG "gkr_rounds__L1" [.n 64, .n 70, .n 65, .n 4, .n 9] [.n 71]) = some true) :
    ResCert Bridge.alignA Kc := by
  intro r hr i hi e j t x hx hin
  have hb := hres i hi x hx
  obtain ⟨hent0, hentA⟩ := hent
  -- the frame's function
  obtain ⟨ia, rfl, hia, hna, hfa, hca, -, -, h1a, hlta⟩ := fn_of_idx t.idx
  obtain ⟨ib, hib, hib', hnb, hfb, hcb, -, -, h1b, hltb⟩ := fn_of_idx ly_idx
  have hjj : ia + 1 = fn_idx% «verify_bus_gkr_loop0» := by
    refine fnOf_entry_inj hlta hltb ?_
    have := t.entry
    simp only [entryOf, t.idx] at this
    rw [this, hent0]
  obtain rfl : ia = ib := by omega
  have hname : e.I.t.name = name% «verify_bus_gkr_loop0» := by rw [← hna, hnb]
  have hcn : (coreOf (ia + 1)).name = name% «verify_bus_gkr_loop0» := by rw [hjj]; exact Da.fn_name_of_find find_ly
  obtain ⟨-, jj, m, sh, q, m2, hjm, hm, hsh, m11, e65, m81, m100, hroom⟩ := ly_top t hr hcn
  have hst : ∀ v, RBase (refMem r.img) e.I.fp (.fr 11) v → v = e.σ (.n 9) := fun v hv ↦ by
    change refMem r.img (e.I.fp + 11) = v at hv
    rw [← hv, m11]
  -- the call at offset `o` is on the path
  have hcall : ∀ o g as bs, (Bridge.alOf Bridge.alignA name% «verify_bus_gkr_loop0» o).map (callInG g as bs) =
      some true → i = o → Ev.call g as bs ∈ e.pre ++ e.es := by
    intro o g as bs hal hio
    subst hio
    obtain ⟨off, hoff, p, hal', as', -, hpos⟩ := t.at'
    rw [hname, hentA] at hoff
    obtain rfl : off = i := by omega
    rw [hname] at hal'
    have hci : callInG g as bs p = true := by rw [hal'] at hal; exact Option.some.inj hal
    obtain ⟨vs', hrest⟩ := t.rest
    rw [hpos] at hrest
    exact List.mem_append_right _ (callInG_sound hrest (by rw [callInG_atoms]; exact hci))
  obtain ⟨s86, s91, f86, f91⟩ := ly_rounds_sites
  match x, hb with
  | .sub a bs, hb =>
    simp only [lyResB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
    rcases hb with ((((⟨hc, hx'⟩ | ⟨hc, hx'⟩) | ⟨⟨hi70, hc⟩, hx'⟩) | ⟨⟨hi83, hc⟩, hx'⟩) | hx') | hx'
    · rw [hx']
      refine stResB_of hst (fun v hv ↦ ?_) (q := q + 8 * jj) (by omega)
      change refMem r.img (e.I.fp + 81) = v at hv
      rw [← hv, m81]
    · rw [hx']
      refine stResB_of hst (fun v hv ↦ ?_) (q := q + 4 * (2 * jj + 2 - sh)) (by omega)
      change refMem r.img (e.I.fp + 100) = v at hv
      rw [← hv, m100]
    · rw [hx']
      have hk := kid_arg t hr (hcall 70 _ _ _ h70 hi70) (by rw [← hjj] at s86; exact s86) (by omega)
        (by rw [hjj]; exact f86) (k := 2) (by simp)
      refine stResB_of hst (fun v hv ↦ ?_) (q := q + 8 * jj) (by omega)
      rw [hk v hv]
      exact e65
    · rw [hx']
      have hk := kid_arg t hr (hcall 83 _ _ _ h83 hi83) (by rw [← hjj] at s91; exact s91) (by omega)
        (by rw [hjj]; exact f91) (k := 2) (by simp)
      refine stResB_of hst (fun v hv ↦ ?_) (q := q + 8 * jj) (by omega)
      rw [hk v hv]
      exact e65
    · rw [hx']; exact lyExt_rres m2 (by omega)
    · rw [hx']; exact lyExt_rres m2 (by omega)
  | .lt _ _, hb => simp [lyResB] at hb
  | .nz _, hb => simp [lyResB] at hb
  | .name _, hb => simp [lyResB] at hb

end

end LeanVM.Guest.EndExec
