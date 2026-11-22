/-
  LeanVM.Guest.CoreMode.Fn.verify_bus_gkr.ResGkrQ

  `verify_bus_gkr`'s cursor in the proof stream (`VbgQ`), carried down from `verify_sub`'s front, and
  its radix-four layers' slots' cursors, carried down `gkr_layers__L{o}`, its loop and
  `gkr_last_layers__L{r}_L{o}` to each `gkr_layer__L{p}_L{o}` (`GlQ`).
-/

module

public import LeanVM.Guest.CoreMode.Fn.keccak_layer.ResStP
public import LeanVM.Guest.CoreMode.Fn.verify_bus_gkr.ResGkrS
public import LeanVM.Guest.CoreMode.Fam.RefAll
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»
import LeanVM.Guest.Data.ValNames.«gkr_last_layers__L»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L»
import LeanVM.Guest.Data.ValNames.«gkr_layers__L»
import LeanVM.Guest.Data.ValNames.«gkr_layers__L_loop0»
import LeanVM.Guest.Data.ValNames.«verify_bus_gkr»

/-!
# `verify_bus_gkr`'s cursors

`VbgQ J`: at an instance of `verify_bus_gkr`, its cursor is `stream·g^13`. `vbgQ_all`: its only caller
is `verify_sub` (`Res.termCallers_all`), at `vbgArgsV` (`vs_vbg_sites`), whose front puts the cursor
`13` words past the stream (`VerifySub.vs_front`).

The radix-four layers' slots (the slot of binary layer `L` in `layers`, field `5` its cursor), each
cursor `stream·g^q` with `q ≤ 27 + 140 j` at radix-four layer `j`:

* `GlsQ`: `gkr_layers__L{o}` at `n_four = g^n`, `rem_g = g^r` (`n, r < 4`), `start_g = g^(2 - o)`, the
  root-most slot's cursor `14` or `8` words past `verify_bus_gkr`'s (`vbg_ls`), the dispatch taking
  `o = depth % 2` (`walk_disp_sel`);
* `GlsLQ`: its loop at `x_m = g^m < g^n`, the slot of layer `4m`; an iteration's four layers move it to
  `4m + 4` (`gl_slots`, `ResGkrS`);
* `GlastQ`: `gkr_last_layers__L{r}_L{o}` at `n_four = g^n`, `m4 = g^(4n)`, the slot of layer `4n`,
  past the loop's run (`glsl_run`);
* `GlQ`: `gkr_layer__L{p}_L{o}` at `x_m = g^m`, `x_j = g^(4m + p)`, the slot of `L = 2(4m + p) + 2 - o`
  with room for the `4L + 12` words it reads, past its siblings before it.

The callers come from `Res.glCallers_all`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Tables
open LeanVM.Guest.Value (gen_pow_eq_ofK e_add_eq_zero_iff e_add_self gen_pow_inj)
open LeanVM.Guest.B2C (idxOf fsN fn_of_idx cellJ kidHdr siteOf)
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **`verify_bus_gkr`'s cursor**: `13` words into its stream. -/
def VbgQ (J : Inst) : Prop :=
  ∀ σ bufs kids, J.t = .node name% «verify_bus_gkr» σ bufs kids → σ (.n (val% «verify_bus_gkr» "cursor@1")) = σ (.n (val% «verify_bus_gkr» "stream")) * gen ^ 13

/-- `verify_bus_gkr`'s call arguments in `verify_sub`. -/
def vbgArgsV : List V := [val% «verify_sub» "nxt[8]@19", val% «verify_sub» "nxt[9]@19", val% «verify_sub» "nxt[10]@19", val% «verify_sub» "nxt[11]@19", val% «verify_sub» "nxt[12]@19", val% «verify_sub» "cursor@1", val% «verify_sub» "g_bus_mu", val% «verify_sub» "zeta", val% «verify_sub» "fs0@3~8", val% «verify_sub» "stream"].map .n

/-- **`gkr_layers__L{o}`'s depth and root slot**: `n_four = g^n`, `rem_g = g^r`, `start_g = g^(2 - o)`,
the root-most slot's cursor `q ≤ 27` words into the stream. -/
def GlsQ (r : Ref) (J : Inst) : Prop :=
  ∀ o < 2, ∀ σ bufs kids, J.t = .node (glcLsN o) σ bufs kids →
    ∃ n rr q, σ (.n (valf% «gkr_layers» "n_four")) = gen ^ n ∧ n < 4 ∧ σ (.n (valf% «gkr_layers» "rem_g")) = gen ^ rr ∧ rr < 4 ∧ σ (.n (valf% «gkr_layers» "start_g")) = gen ^ (2 - o) ∧
      LoadHolds r.img.read (σ (.n (valf% «gkr_layers» "layers"))) (10 * (2 - o) + 5) (σ (.n (valf% «gkr_layers» "stream")) * gen ^ q) ∧ q ≤ 27

/-- **`gkr_layers__L{o}`'s loop at `x_m = g^m`**: the slot of radix-four layer `4m`. -/
def GlsLQ (r : Ref) (J : Inst) : Prop :=
  ∀ o < 2, ∀ σ bufs kids, J.t = .node (glcLsLN o) σ bufs kids →
    ∃ m n q, σ (.n (valf% «gkr_layers» «_loop0» "x_m")) = gen ^ m ∧ σ (.n (valf% «gkr_layers» «_loop0» "bound")) = gen ^ n ∧ m < n ∧ n < 4 ∧ σ (.n (valf% «gkr_layers» «_loop0» "start_g")) = gen ^ (2 - o) ∧
      LoadHolds r.img.read (σ (.n (valf% «gkr_layers» «_loop0» "layers"))) (10 * (2 * (4 * m) + 2 - o) + 5) (σ (.n (valf% «gkr_layers» «_loop0» "stream")) * gen ^ q) ∧
      q ≤ 27 + 560 * m

/-- **`gkr_last_layers__L{r}_L{o}`**: the slot of radix-four layer `4n`. -/
def GlastQ (r : Ref) (J : Inst) : Prop :=
  ∀ rr < 4, ∀ o < 2, ∀ σ bufs kids, J.t = .node (glcLastN rr o) σ bufs kids →
    ∃ n q, σ (.n (valf% «gkr_last_layers» "n_four")) = gen ^ n ∧ n < 4 ∧ σ (.n (valf% «gkr_last_layers» "m4")) = gen ^ (4 * n) ∧ σ (.n (valf% «gkr_last_layers» "start_g")) = gen ^ (2 - o) ∧
      LoadHolds r.img.read (σ (.n (valf% «gkr_last_layers» "layers"))) (10 * (2 * (4 * n) + 2 - o) + 5) (σ (.n (valf% «gkr_last_layers» "stream")) * gen ^ q) ∧
      q ≤ 27 + 560 * n

/-- **`gkr_layer__L{p}_L{o}`'s slot**: at `x_m = g^m`, `x_j = g^(4m + p)`, the slot of
`L = 2(4m + p) + 2 - o` holds `stream·g^q` with room for the layer's `4L + 12` words. -/
def GlQ (r : Ref) (J : Inst) : Prop :=
  ∀ p < 4, ∀ o < 2, ∀ σ bufs kids, J.t = .node (glName p o) σ bufs kids →
    ∃ m q, σ (.n (valf% «gkr_layer» "x_m")) = gen ^ m ∧ m < 4 ∧ σ (.n (valf% «gkr_layer» "x_j")) = gen ^ (4 * m + p) ∧ σ (.n (valf% «gkr_layer» "start_g")) = gen ^ (2 - o) ∧
      LoadHolds r.img.read (σ (.n (valf% «gkr_layer» "layers"))) (10 * (2 * (4 * m + p) + 2 - o) + 5) (σ (.n (valf% «gkr_layer» "stream")) * gen ^ q) ∧
      q + 4 * (2 * (4 * m + p) + 2 - o) + 12 ≤ 8192

end

public section

/-- **`verify_sub` calls `verify_bus_gkr` only at `vbgArgsV`.** -/
theorem vs_vbg_sites :
    Res.sitesB (fun f args _ ↦ f != name% «verify_bus_gkr» || args == vbgArgsV) VerifySub.vsT = true := by
  decide +kernel

/-- **A loop helper's tail call**: the last call of its path, its counter one step on. -/
theorem loop_tail {rd : Reader} {fI : String} {fnI : Fn} (hfI : coreProgram.find? fI = some fnI)
    (hl : fnI.loop = true) (hnc : fI ∉ Stmt.blockCallees (loopBody fnI)) {σI : Val} {es : List Ev} {vs : List V}
    (hw : walk σI fnI.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σI) {i : ℕ} {c : Call}
    (hci : (calls es)[i]? = some c) (hcf : c.f = fI) :
    ∃ p0 prest i0, fnI.params = p0 :: prest ∧ c.args = i0 :: prest ∧
      σI i0 = σI p0 * ofK (addressOfIndex 1) ∧ i + 1 = (calls es).length := by
  obtain ⟨-, e0, -, hsh, -⟩ := progOk_guest.loop _ _ hfI hl
  obtain ⟨p0, prest, c0, i0, es1, hps, hw1, hes, hi0, -⟩ := Res.loop_path hsh hw hh
  subst hes
  have hnm : fnI.name = fI := Da.fn_name_of_find hfI
  rw [Res.loop_calls, hnm] at hci ⊢
  have hi : i = (calls es1).length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · rw [List.getElem?_append_left hlt] at hci
      have hc1 := walk_callees (σ := σI) (loopBody fnI) (c := c) (by rw [hw1]; exact List.mem_of_getElem? hci)
      rw [hcf] at hc1
      exact hnc hc1
    · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by simp; omega)] at hci
      cases hci
  subst hi
  rw [List.getElem?_append_right le_rfl, Nat.sub_self] at hci
  simp only [List.getElem?_singleton, ↓reduceIte, Option.some.injEq] at hci
  subst hci
  exact ⟨p0, prest, i0, hps, rfl, hi0, by simp⟩

/-! ## Down from `verify_sub` -/

variable {r : Ref}

/-- A callee's frame, at a call entered. -/
theorem kid_fn {P : Core.Program} {rd : Reader} {c : Call} {σI : Val} {J : Inst} {g : String} {σ : Val}
    {bufs : List ℕ} {kids : List Tree} (hJt : J.t = .node g σ bufs kids)
    (hval : c.taken = true → J.t.Valid P rd (c.args.map σI) (c.rets.map σI))
    (hph : c.taken = false → ∃ g σ', J.t = .phantom g σ') :
    ∃ fn, P.find? g = some fn ∧ fn.params.map σ = c.args.map σI := by
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  obtain ⟨fn, hfn, hpar, -⟩ := hJv
  exact ⟨fn, hfn, hpar⟩

/-- **`verify_bus_gkr`'s cursor passes down from `verify_sub`.** -/
theorem vbgQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) VbgQ := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph _
    σ bufs kids hJt
  obtain ⟨fn, hfn, hpar⟩ := kid_fn hJt hval hph
  have hcf : c.f = name% «verify_bus_gkr» := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  -- the caller is `verify_sub`
  have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI)) hw c hc)
    (name% «verify_bus_gkr», name% «verify_sub») (by decide)
  have hnI := Da.fn_name_of_find hfI
  rw [hcf] at hcal
  simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
  have hvs : fI = name% «verify_sub» := by
    rcases hcal with h | ⟨h, hl⟩
    · rw [← hnI, h]
    · exfalso
      rw [hnI] at h
      subst h
      obtain rfl : fnI = fn% «verify_bus_gkr» := Option.some.inj (hfI.symm.trans find_vbg)
      rw [vbg_not_loop] at hl
      cases hl
  subst hvs
  obtain rfl : fnI = fn% «verify_sub» := Option.some.inj (hfI.symm.trans VerifySub.find_vs)
  obtain rfl : fn = fn% «verify_bus_gkr» := Option.some.inj (hfn.symm.trans find_vbg)
  -- its call of `verify_bus_gkr`
  have hs := Res.calls_sites (show Res.sitesB _ (fn% «verify_sub»).body = true by
    rw [VerifySub.vs_body]; exact vs_vbg_sites) hw c hc
  rw [hcf] at hs
  simp only [bne_self_eq_false, Bool.false_or, beq_iff_eq] at hs
  rw [hs, vbg_params] at hpar
  simp only [vbgArgsV, List.map_cons, List.map_nil, List.cons.injEq] at hpar
  obtain ⟨-, -, -, -, -, e5, -, -, -, e9, -⟩ := hpar
  -- its front
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv hfI
  rw [VerifySub.vs_body] at hb
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨hexp, hwin⟩ := carryQ_all hr I hI _ σI bufsI kidsI hIt _ hfI (name% «verify_sub», 4, .tab)
    (by decide) rfl (.n (val% «verify_sub» "g_squares")) (by rw [VerifySub.vs_params]; rfl)
  obtain ⟨⟨F⟩, -⟩ := VerifySub.vs_front (by omega) r.img (fun _ _ _ h ↦ Res.KidRel.rel h)
    (bytecode := List.replicate (2 ^ 23) 0) List.length_replicate hexp hwin hb
  rw [e5, e9, F.h320, F.h312, mul_assoc, ← pow_add]

/-- **`verify_bus_gkr`'s cursor at every honest instance.** -/
theorem vbgQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, VbgQ J := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  refine Res.insts_down (vbgQ_step hr) r.T _ r.hdr hv (fun J h ↦ h) (fun J rest he ↦ ?_)
  intro σ bufs kids hJt
  exact absurd (root_main hr he hJt) (by decide)

/-! ## Down from `verify_bus_gkr` -/

/-- **`gkr_layers__L{o}`'s depth and root slot pass down from `verify_bus_gkr`.** -/
theorem glsQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) (GlsQ r) := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph _
    o ho σ bufs kids hJt
  obtain ⟨fn, hfn, hpar⟩ := kid_fn hJt hval hph
  have hcf : c.f = glcLsN o := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  obtain ⟨fn', hf', hp', -⟩ := glcFnCheck_sound (glc_layers_check o ho).1
  obtain rfl : fn = fn' := Option.some.inj (hfn.symm.trans hf')
  rcases gl_caller hfI hw hc (gl_callers_mem.1 o ho).1 hcf with h | ⟨h, hl⟩
  · simp only [List.mem_singleton] at h
    subst h
    obtain rfl : fnI = fn% «verify_bus_gkr» := Option.some.inj (hfI.symm.trans find_vbg)
    have hmem : [glcLsN 0, glcLsN 1].contains (glcLsN o) = true := by
      interval_cases o <;> decide
    -- the arguments
    have hs := Res.calls_sites vbg_ls_sites hw c hc
    simp only [hcf, hmem, Bool.not_true, Bool.false_or, beq_iff_eq] at hs
    rw [hs, hp', glcPar9_eq] at hpar
    simp only [vbgLsArgs, List.map_cons, List.map_nil, List.cons.injEq] at hpar
    obtain ⟨p0, -, -, p3, p4, p5, -, -, p8, -⟩ := hpar
    -- the dispatch's arm
    rw [vbg_split] at hw
    obtain ⟨sel, hsel, hx⟩ := walk_disp_sel vbg_split_sites.1 vbg_split_sites.2 hw hc (by rw [hcf]; exact hmem)
    rw [hcf] at hsel
    have hso := glcLs_sel ho hsel
    -- the body
    obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
    obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv hfI
    rw [vbg_body, holdsList_append, holdsList_noRet _ vbgPre_noRet] at hb
    have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
    obtain ⟨d, hd, e167, e400, e402, e169, hroot⟩ := vbg_ls (by omega) r.img hb.1
    rw [e167, ← gen_pow_eq_ofK] at hx
    have hsd : d % 2 = sel := gen_pow_inj (by omega) (by omega) hx
    subst hsd hso
    have e5 := vbgQ_all hr I hI σI bufsI kidsI hIt
    refine ⟨(d - 1) / 8, ((d - 1) / 2) % 4, 13 + (if d % 2 = 0 then 14 else 8), by rw [p3, e400], by omega,
      by rw [p4, e402], Nat.mod_lt _ (by norm_num), by rw [p5, e169], ?_, by split <;> omega⟩
    rw [p0, p8, pow_add, ← mul_assoc, ← e5]
    exact hroot
  · exfalso
    subst h
    rw [not_loop_of (gl_loopsB.1 o ho).1 hfI] at hl
    cases hl

/-- **`gkr_layers__L{o}`'s depth and root slot at every honest instance.** -/
theorem glsQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, GlsQ r J := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  refine Res.insts_down (glsQ_step hr) r.T _ r.hdr hv (fun J h ↦ h) (fun J rest he ↦ ?_)
  intro o ho σ bufs kids hJt
  have := root_main hr he hJt
  interval_cases o <;> exact absurd this (by decide)

theorem gls_q_step {q q1 m : ℕ} (h1 : q1 ≤ q + 140 * 4) (h : q ≤ 27 + 560 * m) : q1 ≤ 27 + 560 * (m + 1) := by
  rw [Nat.mul_add_one, ← Nat.add_assoc]
  exact Nat.le_trans h1 (Nat.add_le_add_right h _)

/-- **The loop's slot passes down from `gkr_layers__L{o}`, and from one iteration to the next.** -/
theorem glsLQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) (GlsLQ r) := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph hQI
    o ho σ bufs kids hJt
  obtain ⟨fn, hfn, hpar⟩ := kid_fn hJt hval hph
  have hcf : c.f = glcLsLN o := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  obtain ⟨fn', hf', hp', hb'⟩ := glcFnCheck_sound (glc_layers_check o ho).2.1
  obtain rfl : fn = fn' := Option.some.inj (hfn.symm.trans hf')
  obtain ⟨hlp, hend, hnc⟩ := loop_of (gl_loopsB.1 o ho).2.1 hf'
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  -- the counter below the bound, at the callee
  suffices H : ∃ m n q, σ (.n (valf% «gkr_layers» «_loop0» "x_m")) = gen ^ m ∧ σ (.n (valf% «gkr_layers» «_loop0» "bound")) = gen ^ n ∧ m ≤ n ∧ n < 4 ∧ σ (.n (valf% «gkr_layers» «_loop0» "start_g")) = gen ^ (2 - o) ∧
      LoadHolds r.img.read (σ (.n (valf% «gkr_layers» «_loop0» "layers"))) (10 * (2 * (4 * m) + 2 - o) + 5) (σ (.n (valf% «gkr_layers» «_loop0» "stream")) * gen ^ q) ∧
      q ≤ 27 + 560 * m by
    obtain ⟨m, n, q, h0, h1, hmn, hn, h5, hsl, hq⟩ := H
    obtain ⟨m', hm', h0'⟩ := loop_ctr_lt hr hJS hJt hfn hlp hend (hp'.trans glcPar9_eq) h1 (by omega)
    obtain rfl : m = m' := gen_pow_inj (by omega) (by omega) (h0.symm.trans h0')
    exact ⟨m, n, q, h0, h1, hm', hn, h5, hsl, hq⟩
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv hfI
  rw [hp', glcPar9_eq] at hpar
  rcases gl_caller hfI hw hc (gl_callers_mem.1 o ho).2.1 hcf with h | ⟨h, hl⟩
  · -- `gkr_layers__L{o}`'s call
    simp only [List.mem_singleton] at h
    subst h
    obtain ⟨fnL, hfL, -, hbL⟩ := glcFnCheck_sound (glc_layers_check o ho).1
    obtain rfl : fnI = fnL := Option.some.inj (hfI.symm.trans hfL)
    have hs := Res.calls_sites (by rw [hbL]; exact (gl_sites o ho).1) hw c hc
    simp only [hcf, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hs
    rw [hs.1] at hpar
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar
    obtain ⟨p0, p1, p2, -, -, p5, -, -, p8, -⟩ := hpar
    rw [hbL] at hb
    obtain ⟨c11, -, -, -⟩ := gls_holds hb
    obtain ⟨n, rr, q, h3, hn, -, -, h5, hsl, hq⟩ := glsQ_all hr I hI o ho σI bufsI kidsI hIt
    refine ⟨0, n, q, by rw [p0, c11, pow_zero], by rw [p1, h3], Nat.zero_le _, hn, by rw [p5, h5], ?_, by omega⟩
    rw [p2, p8]
    simpa using hsl
  · -- the loop's tail call
    subst h
    obtain rfl := Option.some.inj (hfI.symm.trans hf')
    obtain ⟨p0, prest, i0, hps, hargs, hi0, -⟩ := loop_tail hfI hlp hnc hw hh hci hcf
    rw [hp', glcPar9_eq] at hps
    obtain ⟨rfl, rfl⟩ := List.cons.inj hps
    rw [hargs] at hpar
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar
    obtain ⟨p0, p1, p2, -, -, p5, -, -, p8, -⟩ := hpar
    obtain ⟨m, n, q, h0I, h1I, hmn, hn, h5I, hslI, hqI⟩ := hQI o ho σI bufsI kidsI hIt
    rw [hb'] at hb
    obtain ⟨m10, -, hcalls⟩ := glsl_holds hb
    have hR : ∀ p < 4, coreProgram.Rel r.img.read (glName p o) [σI (.n (valf% «gkr_layers» «_loop0» "layers")), σI (.n (valf% «gkr_layers» «_loop0» "rounds")), σI (.n (valf% «gkr_layers» «_loop0» "gkr_pts")), gen ^ m,
        gen ^ (4 * m + p), gen ^ (2 - o), σI (.n (valf% «gkr_layers» «_loop0» "g_bus_mu")), σI (.n (valf% «gkr_layers» «_loop0» "tabs")), σI (.n (valf% «gkr_layers» «_loop0» "stream"))] [] := fun p hp ↦ by
      have := Res.KidRel.rel (hcalls p hp)
      rwa [m10, h0I, h5I, gl_pow4] at this
    obtain ⟨q1, h1, hq1⟩ := gl_slots ho (by omega) 4 le_rfl hR hslI 4 le_rfl
    refine ⟨m + 1, n, q1, ?_, by rw [p1, h1I], by omega, hn, by rw [p5, h5I], ?_, gls_q_step hq1 hqI⟩
    · rw [p0, hi0, h0I, ← gen_pow_eq_ofK, ← pow_add]
    · rw [p2, p8, show 4 * (m + 1) = 4 * m + 4 by ring]
      exact h1

/-- **The loop's slot at every honest instance.** -/
theorem glsLQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, GlsLQ r J := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  refine Res.insts_down (glsLQ_step hr) r.T _ r.hdr hv (fun J h ↦ h) (fun J rest he ↦ ?_)
  intro o ho σ bufs kids hJt
  have := root_main hr he hJt
  interval_cases o <;> exact absurd this (by decide)

/-- **`gkr_last_layers`' slot passes down from `gkr_layers__L{o}`**, past the loop's run. -/
theorem glastQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) (GlastQ r) := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph _
    rr hrr o ho σ bufs kids hJt
  obtain ⟨fn, hfn, hpar⟩ := kid_fn hJt hval hph
  have hcf : c.f = glcLastN rr o := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  obtain ⟨fn', hf', hp', -⟩ := glcFnCheck_sound ((glc_layers_check o ho).2.2 rr hrr)
  obtain rfl : fn = fn' := Option.some.inj (hfn.symm.trans hf')
  rw [hp', glcPar9_eq] at hpar
  rcases gl_caller hfI hw hc ((gl_callers_mem.1 o ho).2.2 rr hrr) hcf with h | ⟨h, hl⟩
  · simp only [List.mem_singleton] at h
    subst h
    obtain ⟨fnL, hfL, -, hbL⟩ := glcFnCheck_sound (glc_layers_check o ho).1
    obtain rfl : fnI = fnL := Option.some.inj (hfI.symm.trans hfL)
    have hs := Res.calls_sites (by rw [hbL]; exact (gl_sites o ho).1) hw c hc
    simp only [hcf, Bool.and_eq_true] at hs
    have hs' := List.all_eq_true.mp hs.2 rr (List.mem_range.mpr hrr)
    simp only [bne_self_eq_false, Bool.false_or, beq_iff_eq] at hs'
    rw [hs'] at hpar
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar
    obtain ⟨p0, -, -, p3, p4, p5, -, -, p8, -⟩ := hpar
    obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
    obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv hfI
    rw [hbL] at hb
    obtain ⟨c11, a10, hloop, m13⟩ := gls_holds hb
    obtain ⟨n, rr0, q, h3, hn, -, -, h5, hsl, hq⟩ := glsQ_all hr I hI o ho σI bufsI kidsI hIt
    -- the slot of layer `4n`, past the loop's run
    have hslot : ∃ q', LoadHolds r.img.read (σI (.n (valf% «gkr_layers» "layers"))) (10 * (2 * (4 * n) + 2 - o) + 5)
        (σI (.n (valf% «gkr_layers» "stream")) * gen ^ q') ∧ q' ≤ 27 + 560 * n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · exact ⟨q, by simpa using hsl, by omega⟩
      · have hne : σI (.n (valf% «gkr_layers» "s0#1")) ≠ 0 := by
          rw [a10, h3]
          intro h0
          have := gen_pow_inj (by omega) (by omega) ((e_add_eq_zero_iff.mp h0).symm.trans (pow_zero gen).symm)
          omega
        obtain ⟨dd, hrel⟩ := Res.KidRel.rel (hloop hne)
        rw [c11, h3, h5, ← pow_zero gen] at hrel
        obtain ⟨q', h', hq'⟩ := glsl_run ho hn dd 0 q hn0 hrel (by simpa using hsl)
        exact ⟨q', h', by omega⟩
    obtain ⟨q', h', hq'⟩ := hslot
    exact ⟨n, q', by rw [p3, h3], hn, by rw [p4, m13, h3, glc_pow4], by rw [p5, h5], by rw [p0, p8]; exact h',
      hq'⟩
  · exfalso
    subst h
    rw [not_loop_of ((gl_loopsB.1 o ho).2.2 rr hrr) hfI] at hl
    cases hl

/-- **`gkr_last_layers`' slot at every honest instance.** -/
theorem glastQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, GlastQ r J := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  refine Res.insts_down (glastQ_step hr) r.T _ r.hdr hv (fun J h ↦ h) (fun J rest he ↦ ?_)
  intro rr hrr o ho σ bufs kids hJt
  have := root_main hr he hJt
  interval_cases rr <;> interval_cases o <;> exact absurd this (by decide)

/-- **A layer's slot passes down from `gkr_layers__L{o}`'s loop or from `gkr_last_layers`**, past its
siblings before it. -/
theorem glQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) (GlQ r) := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph _
    p hp o ho σ bufs kids hJt
  obtain ⟨fn, hfn, hpar⟩ := kid_fn hJt hval hph
  have hcf : c.f = glName p o := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  obtain ⟨fn', hf', hp', -⟩ := glIs_sound (glIs_layers p hp o ho)
  obtain rfl : fn = fn' := Option.some.inj (hfn.symm.trans hf')
  rw [hp', glParams_eq] at hpar
  suffices H : ∃ m q, σ (.n 3) = gen ^ m ∧ m < 4 ∧ σ (.n 4) = gen ^ (4 * m + p) ∧ σ (.n 5) = gen ^ (2 - o) ∧
      LoadHolds r.img.read (σ (.n 0)) (10 * (2 * (4 * m + p) + 2 - o) + 5) (σ (.n 8) * gen ^ q) ∧
      q ≤ 27 + 140 * (4 * m + p) by
    obtain ⟨m, q, h3, hm, h4, h5, hsl, hq⟩ := H
    exact ⟨m, q, h3, hm, h4, h5, hsl, by omega⟩
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv hfI
  have site : ∀ {A : ℕ → List V} {body : List Stmt}, fnI.body = body →
      Res.sitesB (fun f args _ ↦ (List.range 4).all fun p ↦ f != glName p o || args == A p) body = true →
      c.args = A p := fun {A body} hbd hsb ↦ by
    have hs := List.all_eq_true.mp (Res.calls_sites (by rw [hbd]; exact hsb) hw c hc) p (List.mem_range.mpr hp)
    simpa [hcf] using hs
  rcases gl_caller hfI hw hc ((gl_callers_mem.2 p hp o ho).1) hcf with h | ⟨h, hl⟩
  · simp only [List.mem_cons, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at h
    rcases h with h | ⟨rr, ⟨hrr, hprr⟩, h⟩
    · -- `gkr_layers__L{o}`'s loop
      subst h
      obtain ⟨fnL, hfL, -, hbL⟩ := glcFnCheck_sound (glc_layers_check o ho).2.1
      obtain rfl : fnI = fnL := Option.some.inj (hfI.symm.trans hfL)
      rw [site hbL (gl_sites o ho).2.1] at hpar
      simp only [glLsLArgs, List.map_cons, List.map_nil, List.cons.injEq] at hpar
      obtain ⟨p0, -, -, p3, p4, p5, -, -, p8, -⟩ := hpar
      rw [hbL] at hb
      obtain ⟨m10, hxs, hcalls⟩ := glsl_holds hb
      obtain ⟨m, n, q, h0I, -, hmn, hn, h5I, hslI, hqI⟩ := glsLQ_all hr I hI o ho σI bufsI kidsI hIt
      have hR : ∀ p < 4, coreProgram.Rel r.img.read (glName p o) [σI (.n 2), σI (.n 3), σI (.n 4), gen ^ m,
          gen ^ (4 * m + p), gen ^ (2 - o), σI (.n 6), σI (.n 7), σI (.n 8)] [] := fun p hp ↦ by
        have := Res.KidRel.rel (hcalls p hp)
        rwa [m10, h0I, h5I, gl_pow4] at this
      obtain ⟨q', h', hq'⟩ := gl_slots ho (by omega) 4 le_rfl hR hslI p hp.le
      refine ⟨m, q', by rw [p3, h0I], by omega, ?_, by rw [p5, h5I], by rw [p0, p8]; exact h', by omega⟩
      rw [p4, hxs p hp, m10, h0I, gl_pow4]
    · -- `gkr_last_layers__L{r}_L{o}`
      subst h
      obtain ⟨fnL, hfL, -, hbL⟩ := glcFnCheck_sound ((glc_layers_check o ho).2.2 rr hrr)
      obtain rfl : fnI = fnL := Option.some.inj (hfI.symm.trans hfL)
      rw [site hbL ((gl_sites o ho).2.2 rr hrr)] at hpar
      simp only [glLastArgs, List.map_cons, List.map_nil, List.cons.injEq] at hpar
      obtain ⟨p0, -, -, p3, p4, p5, -, -, p8, -⟩ := hpar
      rw [hbL] at hb
      obtain ⟨hxs, hcalls⟩ := glast_holds hb
      obtain ⟨n, q, h3I, hn, h4I, h5I, hslI, hqI⟩ := glastQ_all hr I hI rr hrr o ho σI bufsI kidsI hIt
      have hR : ∀ p < rr, coreProgram.Rel r.img.read (glName p o) [σI (.n 0), σI (.n 1), σI (.n 2), gen ^ n,
          gen ^ (4 * n + p), gen ^ (2 - o), σI (.n 6), σI (.n 7), σI (.n 8)] [] := fun p hp ↦ by
        have := Res.KidRel.rel (hcalls p hp)
        rwa [h3I, h4I, h5I, ← pow_add] at this
      obtain ⟨q', h', hq'⟩ := gl_slots ho hn rr hrr.le hR hslI p hprr.le
      refine ⟨n, q', by rw [p3, h3I], hn, ?_, by rw [p5, h5I], by rw [p0, p8]; exact h', by omega⟩
      rw [p4, hxs p hprr, h4I, ← pow_add]
  · exfalso
    subst h
    rw [not_loop_of (gl_loopsB.2 p hp o ho).1 hfI] at hl
    cases hl

/-- **A layer's slot at every honest instance.** -/
theorem glQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, GlQ r J := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  refine Res.insts_down (glQ_step hr) r.T _ r.hdr hv (fun J h ↦ h) (fun J rest he ↦ ?_)
  intro p hp o ho σ bufs kids hJt
  have := root_main hr he hJt
  interval_cases p <;> interval_cases o <;> exact absurd this (by decide)

end

end LeanVM.Guest.EndExec
