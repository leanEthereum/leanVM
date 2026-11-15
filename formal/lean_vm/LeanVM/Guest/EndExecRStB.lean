/-
  LeanVM.Guest.EndExecRStB

  The proof stream's reads (`Res.stB`), sound at the honest frames: `keccak_layer`'s and its two
  loops' reads past their cursors lie inside the stream.
-/

module

public import LeanVM.Guest.EndExecRStP
public import LeanVM.Guest.Res.SubDefs

/-!
# The proof stream's reads

`stRes_of`: the read `c` words past cursor cell `o` lies in the stream `st·[0, 8192)` once the cell
holds `st·g^q`, `q + c < 8192`. `st_top`: each site of `Res.stSites` at an honest frame. A layer's
last record's cursor is `48 + 2y` words past its cursor (`layer_cur`), which `LayQ` puts `p` words into
its stream with room for `84 + 2y` (`layQ_all`); a loop's cursor is its record's, `q` words into the
stream of the frame its header names, with room for its iterations (`loopQ_all`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B2C (idxOf FrameHolds fsN fn_of_idx cellJ namedOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (stB stRes stSites topAtoms)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

@[expose] public section

/-- A layer's last record's cursor cell. -/
def layCell (first : ℕ) : ℕ := if first = 1 then 792 else 765

/-- A loop's cursor value, and its cell. -/
def loopCur (rem : Bool) : V := if rem then .n 14 else .n 20
def loopCell (rem : Bool) : ℕ := if rem then 18 else 21

end

public section

/-- **A read past a cursor inside the stream**: the cursor's cell holds `st·g^q`, `q + c < 8192`. -/
theorem stRes_of {M : ℕ → E} {fp o : ℕ} {st : Base} {c q : ℕ} {S : E}
    (hst : ∀ v, RBase M fp st v → v = S) (hcur : M (fp + o) = S * gen ^ q) (hq : q + c < 8192) :
    RRes M fp (stRes o st c) := by
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
  change M (fp + o) = u at hu
  subst hw hw'
  rw [hst _ hu', ← hu, hcur]
  simp only [ofK_gpow]
  ring

theorem lay_load_top {first : ℕ} (hf : first < 2) :
    (topAtoms (coreOf (layIdx first)).body).contains
      (.load (.n (layOff first + 745)) (.n (layOff first + 739)) 80) = true := by
  interval_cases first <;> decide +kernel

theorem layCell_facts {first : ℕ} (hf : first < 2) :
    cellJ (layIdx first) (.n (layOff first + 745)) = layCell first ∧ 2 ≤ layCell first ∧
      layCell first < fsN (layIdx first) := by
  interval_cases first <;> decide +kernel

theorem loop_atoms_top {first : ℕ} (hf : first < 2) (rem : Bool) {fn : Fn}
    (hfn : coreProgram.find? (stLoop first rem) = some fn) :
    (topAtoms fn.body).contains (.mul (.n 6) (.n 2) (.n 0)) = true ∧
      (topAtoms fn.body).contains (.load (loopCur rem) (.n 6) 80) = true := by
  interval_cases first <;> cases rem
  · rw [Option.some.inj (hfn.symm.trans find_pack8_458)]; decide +kernel
  · rw [Option.some.inj (hfn.symm.trans find_packRem_459)]; decide +kernel
  · rw [Option.some.inj (hfn.symm.trans find_pack8_456)]; decide +kernel
  · rw [Option.some.inj (hfn.symm.trans find_packRem_457)]; decide +kernel

theorem loopCell_facts {first : ℕ} (hf : first < 2) (rem : Bool) {j : ℕ} (hj : idxOf (stLoop first rem) = some j) :
    cellJ j (loopCur rem) = loopCell rem ∧ 2 ≤ loopCell rem ∧ loopCell rem < fsN j := by
  interval_cases first <;> cases rem
  · obtain rfl : j = fn_idx% «keccak_layer__L0_loop0» := Option.some.inj (hj.symm.trans (by decide +kernel))
    decide +kernel
  · obtain rfl : j = fn_idx% «keccak_layer__L0_loop1» := Option.some.inj (hj.symm.trans (by decide +kernel))
    decide +kernel
  · obtain rfl : j = fn_idx% «keccak_layer__L1_loop0» := Option.some.inj (hj.symm.trans (by decide +kernel))
    decide +kernel
  · obtain rfl : j = fn_idx% «keccak_layer__L1_loop1» := Option.some.inj (hj.symm.trans (by decide +kernel))
    decide +kernel

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

theorem hfs_guest : ∀ f', 1 ≤ B2C.fs f' := fun f' ↦ by
  unfold B2C.fs; split <;> simp [B2C.mainFrame, Data.mainCells, Data.jtSlots]

/-- **A layer's reads past its last record's cursor** lie in its stream. -/
theorem st_lay (t : TopAt A r K i e j) (hr : r.Ok) {first : ℕ} (hf : first < 2)
    (hname : (coreOf j).name = layerName first) {c : ℕ} (hc : c < 36) :
    RRes (refMem r.img) e.I.fp (stRes (layCell first) (.fr 17) c) := by
  obtain ⟨f, bufs, kids, hJ, hfj, hfn⟩ := t.found
  rw [hname] at hfn
  subst hfn
  have hj : j = layIdx first := by
    have := t.idx
    rw [hJ] at this
    exact Option.some.inj (this.symm.trans (layIdx_eq hf))
  subst hj
  obtain ⟨fL, hfL, hbL, hpL⟩ := layer_found hf
  have hcf : coreOf (layIdx first) = fL := Option.some.inj (hfj.symm.trans hfL)
  obtain ⟨p, y, e7, hy, h9, h10, hroom⟩ := layQ_all hr e.I t.inst _ e.σ bufs kids hJ first hf rfl
  obtain ⟨args, rets, hv⟩ := inst_valid' hr t.inst hJ
  obtain ⟨-, hb⟩ := Res.holds_of_valid hfs_guest hv hfj
  rw [hcf] at hb
  obtain ⟨hcur, -⟩ := layer_cur hf (fun _ _ _ h ↦ Res.KidRel.rel h) hy h9 h10 hbL hb
  obtain ⟨vs, hw, hF, -⟩ := t.events hr
  have hon := topAtoms_on_path hw (List.contains_iff_mem.mp (lay_load_top hf))
  obtain ⟨hcell, h2, hlt⟩ := layCell_facts hf
  have hm := t.cell hr hF (x := .n (layOff first + 745)) (namedOf_atom hon (by simp [atomUses])) (by rw [hcell]; exact h2)
    (by rw [hcell]; exact hlt)
  rw [hcell] at hm
  obtain ⟨h15, h17, -⟩ := layIdx_facts hf
  have hs := t.param hr (p := .n 15) (by rw [hcf, hpL]; simp)
    (by simp only [Res.inFr, h15, Bool.and_eq_true, decide_eq_true_eq]; omega)
  rw [h15] at hs
  refine stRes_of (S := e.σ (.n 15)) (q := p + (48 + 2 * y)) (fun v hv ↦ ?_) ?_ (by omega)
  · change refMem r.img (e.I.fp + 17) = v at hv
    rw [← hv, hs]
  · rw [hm, hcur, e7, mul_assoc, ← pow_add]

/-- **A loop's reads past its cursor** lie in the layer's stream. -/
theorem st_loop (t : TopAt A r K i e j) (hr : r.Ok) {first : ℕ} (hf : first < 2) (rem : Bool)
    (hname : (coreOf j).name = stLoop first rem) {c : ℕ} (hc : c < stStep rem) :
    RRes (refMem r.img) e.I.fp (stRes (loopCell rem) (.hp 1 17) c) := by
  obtain ⟨f, bufs, kids, hJ, hfj, hfn⟩ := t.found
  rw [hname] at hfn
  subst hfn
  have hj := t.idx
  rw [hJ] at hj
  simp only [Tree.name] at hj
  obtain ⟨a, jj, n, q, hhd, ha17, -, -, hjn, -, hld, hroom⟩ :=
    loopQ_all hr e.I t.inst _ e.σ bufs kids hJ first hf rem rfl
  obtain ⟨vs, hw, hF, hev⟩ := t.events hr
  obtain ⟨tm, tl⟩ := loop_atoms_top hf rem hfj
  have hm := topAtoms_on_path hw (List.contains_iff_mem.mp tm)
  have hl := topAtoms_on_path hw (List.contains_iff_mem.mp tl)
  have e6 : e.σ (.n 6) = e.σ (.n 2) * e.σ (.n 0) := hev _ hm
  have hl' : LoadHolds r.img.read (e.σ (.n 6)) 80 (e.σ (loopCur rem)) := hev _ hl
  rw [e6] at hl'
  have ecur := loadHolds_unique hl' hld
  obtain ⟨hcell, h2, hlt⟩ := loopCell_facts hf rem hj
  have hcm := t.cell hr hF (x := loopCur rem) (namedOf_atom hl (by simp [atomUses])) (by rw [hcell]; exact h2)
    (by rw [hcell]; exact hlt)
  rw [hcell] at hcm
  have hfb := t.fb
  have hT : refMem r.img (e.I.fp + 1) = ofK (Parameters.g ^ a) := by
    have := (ref_read hr (by omega) hF.hdr1).2
    rw [this, hhd]
  have hS : stStep rem ≤ stStep rem * (n - jj) := Nat.le_mul_of_pos_right _ (by omega)
  refine stRes_of (S := refMem r.img (a + 17)) (q := q) (fun v hv ↦ ?_) (by rw [hcm, ecur]) (by omega)
  obtain ⟨x, hxn, hxM⟩ := hv
  have hl0 : (refMem r.img (e.I.fp + 1)).limb 0 = Parameters.g ^ a := by rw [hT]; simp
  obtain rfl : x = a + 17 := names_uniq hxn (names_shift hl0 ha17)
  exact hxM.symm

/-- **The proof stream's reads at an honest frame.** -/
theorem st_top (t : TopAt A r K i e j) (hr : r.Ok) {x : Mode.Res} (hx : stB j x = true) :
    RRes (refMem r.img) e.I.fp x := by
  match x, hx with
  | .sub a bs, hx =>
    simp only [stB, stSites, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq] at hx
    rcases hx with ⟨⟨hn, hc⟩, hx⟩ | ⟨⟨hn, hc⟩, hx⟩ | ⟨⟨hn, hc⟩, hx⟩ | ⟨⟨hn, hc⟩, hx⟩ | ⟨⟨hn, hc⟩, hx⟩ |
      ⟨⟨hn, hc⟩, hx⟩ <;> rw [hx]
    · exact st_lay t hr (first := 0) (by decide) hn hc
    · exact st_lay t hr (first := 1) (by decide) hn hc
    · exact st_loop t hr (first := 0) (by decide) false hn hc
    · exact st_loop t hr (first := 1) (by decide) false hn hc
    · exact st_loop t hr (first := 0) (by decide) true hn hc
    · exact st_loop t hr (first := 1) (by decide) true hn hc
  | .lt _ _, hx => simp [stB] at hx
  | .nz _, hx => simp [stB] at hx
  | .name _, hx => simp [stB] at hx

end

end

end LeanVM.Guest.EndExec
