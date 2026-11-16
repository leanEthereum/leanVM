/-
  LeanVM.Guest.EndExecRF

  The `sub` families read off a function's own code, sound at the honest frames: a run over a product
  scaled by a factor (F4, F6) and a read the exponent tables' side section guards (F2).
-/

module

public import LeanVM.Guest.EndExecRS
public import LeanVM.Guest.Res.FamDefs
public import LeanVM.Guest.B1.Placement.Common
public import LeanVM.Guest.EndExecYWitCells
public import LeanVM.Guest.EndExecRA
public import LeanVM.Guest.EndExecW
public import LeanVM.Guest.B1.Tables.Basic

/-!
# The families' shared checks, sound

`topAtoms_on_path`, `topSels_sound`: a top-level atom or selector before any statement that may
return is on every returning path; so are a witness's (`TopAt.wit`, `witOk`). `powOf_sound`:
`powOf w = some e` makes `w = g^e` (`Data.powTree`, checked once). `rcBound_sound`: on a memory of at
most `2^32` words, a range check against `g^(N - 1)` makes its value `g^e`, `e < N`
(`B1.Tables.tb_rc_sound'`). `cellLt_top`: at an honest frame, the cell holds `g^e`, `e < N`, through
the frame's value there (`TopAt.cell`).

`shift_top` (F4, F6): the code's `[p] = [c]·[o]`, `[c] = g^ec`, `[o] = g^eo` the factor's word,
makes `Q·[o]·g^j = Q·g^(eo + j)`, below `[p]`'s exponent `ec + eo` (F4) or a constant above it (F6).
`side_top` (F2): the group `g^gi` read at `[q]·g^r` reads the exponent tables' side section at its
group (`tabVals`, the carried tables, `carryQ_all`) into a constant, which the table makes its side's
word, so the group lies in the side's block.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf entryOf FrameHolds fsN fn_of_idx cellJ namedOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (Wit witOk topAtoms topSels selOf powOf constOf rcBound cellLt holdsBase mulBy inFr eqCells shiftHi shiftB frEx subFamB sideShape sideB sideRead sideIn tabVals numOf frExT mulConst)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

/-! ## The atoms on every path -/

theorem topAtoms_on_path {σ : Core.Val} : ∀ {ss : List Stmt} {es : List Ev} {vs : List V},
    walk σ ss = .ret es vs → ∀ {a : Atom}, a ∈ topAtoms ss → Ev.atom a ∈ es
  | [], _, _, _, _, h => by simp [topAtoms] at h
  | s :: ss, es, vs, hw, a, ha => by
    have hrest : Memory.Stmt.noRet s = true → a ∈ topAtoms ss → Ev.atom a ∈ es := fun hn h ↦ by
      obtain ⟨es1, es2, -, h2, rfl⟩ := Res.walk_cons_noRet hn hw
      exact List.mem_append_right _ (topAtoms_on_path h2 h)
    cases s with
    | atom b =>
      simp only [topAtoms, List.mem_cons] at ha
      obtain ⟨es1, es2, h1, h2, rfl⟩ := Res.walk_cons_noRet (s := .atom b) rfl hw
      simp only [walk1, Out.fall.injEq] at h1
      subst h1
      rcases ha with rfl | ha
      · exact List.mem_cons_self
      · exact List.mem_append_right _ (topAtoms_on_path h2 ha)
    | _ =>
      simp only [topAtoms] at ha
      split_ifs at ha with hn
      · exact hrest (by rw [← Memory.noRetR_eq]; exact hn) ha
      · simp at ha

/-- **A top-level selector on a returning path** picks an arm: `g^e`, `e` below the arms. -/
theorem topSels_sound {σ : Core.Val} : ∀ {ss : List Stmt} {es : List Ev} {vs : List V},
    walk σ ss = .ret es vs → ∀ {x : V} {n : ℕ}, (x, n) ∈ topSels ss → ∃ e < n, σ x = ofK (addressOfIndex e)
  | [], _, _, _, _, _, h => by simp [topSels] at h
  | s :: ss, es, vs, hw, x, n, h => by
    simp only [topSels, List.mem_append] at h
    rcases h with h | h
    · split at h
      · rename_i p hs
        simp only [List.mem_singleton] at h
        subst h
        exact Res.selOf_walk hs (Res.walk1_ne_stuck hw)
      · simp at h
    · split_ifs at h with hn
      · obtain ⟨es1, es2, -, h2, rfl⟩ := Res.walk_cons_noRet (by rw [← Memory.noRetR_eq]; exact hn) hw
        exact topSels_sound h2 h
      · simp at h

/-! ## Constants -/

theorem powOf_sound {w : E} {e : ℕ} (h : powOf w = some e) : w = ofK (addressOfIndex e) := by
  unfold powOf at h
  split_ifs at h with h1
  have hk := Exec.PowTree.find_ok (Exec.PowTree.ok_of_okW Checked.powTree_ok) h
  rw [show K.ofBits (w.limb 0).toBitVec.toNat = w.limb 0 by
    simp [K.ofBits, BF64.ofBitVec, BitVec.ofNat_toNat]] at hk
  rw [eq_ofK_limb h1, hk]

theorem constOf_sound {as : List Atom} {k : V} {w : E} (h : constOf as k = some w) : Atom.const k w ∈ as := by
  unfold constOf at h
  obtain ⟨a, ha, hf⟩ := List.exists_of_findSome?_eq_some h
  cases a with
  | const d w' =>
    simp only at hf
    split_ifs at hf with hd
    obtain rfl := Option.some.inj hf
    rw [← hd]; exact ha
  | _ => simp at hf

/-- **A range check's bound**: its value `g^e`, `e < N`. -/
theorem rcBound_sound {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) {σ : Core.Val} {as : List Atom}
    (hh : ∀ a ∈ as, a.Holds Lm.read σ) {v : V} {N : ℕ} (h : rcBound as v = some N) :
    ∃ e < N, σ v = gen ^ e := by
  unfold rcBound at h
  obtain ⟨a, ha, hf⟩ := List.exists_of_findSome?_eq_some h
  cases a with
  | rangeCheck x y t1 t2 k =>
    simp only at hf
    split_ifs at hf with hx
    subst hx
    cases hc : (constOf as k).bind powOf with
    | none => rw [hc] at hf; simp at hf
    | some e =>
      rw [hc] at hf
      simp only at hf
      split_ifs at hf with he
      obtain rfl := Option.some.inj hf
      obtain ⟨w, hw, hpw⟩ := Option.bind_eq_some_iff.mp hc
      have hk : σ k = w := hh _ (constOf_sound hw)
      obtain ⟨h1, h2, h3⟩ := hh _ ha
      exact B1.Tables.tb_rc_sound' hμ Lm (by omega) he
        (by rw [hk, powOf_sound hpw, Nat.add_sub_cancel]) h1 h2 h3
  | _ => simp at hf

/-! ## Cells -/

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ} {w : Wit}

/-- **An honest frame's path, with a witness's atoms and selectors on it.** -/
theorem TopAt.wit (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) :
    ∃ vs, walk e.σ (coreOf j).body = .ret (e.pre ++ e.es) vs ∧
      FrameHolds r.img j e.I.fp e.σ (e.pre ++ e.es) vs e.I.kidFps e.I.hdr ∧
      (∀ ev ∈ e.pre ++ e.es, ev.Holds r.img.read e.σ) ∧ (∀ a ∈ w.as, Ev.atom a ∈ e.pre ++ e.es) ∧
      ∀ p ∈ w.ss, ∃ x < p.2, e.σ p.1 = ofK (addressOfIndex x) := by
  obtain ⟨vs, hw, hF, hev⟩ := t.events hr
  simp only [witOk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, List.isSublist_iff_sublist] at hW
  exact ⟨vs, hw, hF, hev, fun a ha ↦ topAtoms_on_path hw (hW.1.subset ha),
    fun p hp ↦ topSels_sound hw (hW.2 p hp)⟩

/-- **A bounded cell at an honest frame** holds `g^e`, `e < N`. -/
theorem cellLt_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {o N : ℕ} (h : cellLt j w o N = true) :
    ∃ x < N, refMem r.img (e.I.fp + o) = ofK (Parameters.g ^ x) := by
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨vs, hw, hF, hev, hwa, hws⟩ := t.wit hr hW
  simp only [cellLt, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨h2, hlt⟩, hN⟩, h⟩ := h
  rcases h with ⟨a, ha, hb⟩ | hs
  · cases a with
    | rangeCheck x y t1 t2 k =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      obtain ⟨hc, hb⟩ := hb
      split at hb
      · rename_i n hn
        simp only [decide_eq_true_eq] at hb
        have hall : ∀ a ∈ w.as, a.Holds r.img.read e.σ :=
          fun a ha ↦ hev _ (hwa _ ha)
        obtain ⟨x', hx', hσ⟩ := rcBound_sound (by omega) r.img hall hn
        have hx := t.cell hr hF (x := x) (namedOf_atom (hwa _ ha) (by simp [atomUses]))
          (by rw [hc]; exact h2) (by rw [hc]; exact hlt)
        rw [hc] at hx
        exact ⟨x', by omega, by rw [hx, hσ, Value.gen_pow_eq_ofK]⟩
      · cases hb
    | _ => simp at hb
  · obtain ⟨⟨y, n⟩, hyn, hb⟩ := hs
    obtain ⟨⟨hc, hn⟩, hy⟩ := hb
    simp only [beq_iff_eq] at hc hy hn
    obtain ⟨x', hx', hσ⟩ := hws _ hyn
    have hy' : y ∈ namedOf (coreOf j).params (e.pre ++ e.es) vs := by
      rcases hy with hy | ⟨a, ha, hya⟩
      · exact List.mem_append_left _ (List.mem_append_left _ hy)
      · exact namedOf_atom (hwa _ ha) hya
    have hx := t.cell hr hF hy' (by rw [hc]; exact h2) (by rw [hc]; exact hlt)
    rw [hc] at hx
    exact ⟨x', by omega, by rw [hx, hσ]⟩
end

/-! ## Products -/

theorem frEx_eq {i : Mode.Idx} {c : ℕ} (h : frEx i = some c) : i = .ex (.fr c) 0 := by
  match i, h with
  | .ex (.fr c') 0, h => simp only [frEx, Option.some.injEq] at h; rw [h]

section

variable {M : ℕ → E} {fp : ℕ}

theorem rbs_insert_inv {b : Base} {e : ℕ} :
    ∀ {l : List (Base × ℕ)} {w : E}, RBs M fp (insertBs (b, e) l) w →
      ∃ u wl, RBase M fp b u ∧ RBs M fp l wl ∧ w = u ^ e * wl
  | [], w, ⟨u, w', hu, hw', h⟩ => ⟨u, 1, hu, rfl, by rw [h, show w' = 1 from hw']⟩
  | (b', e') :: l, w, h => by
    unfold insertBs at h
    dsimp only at h
    split_ifs at h with hq hl
    · obtain rfl := Base.beq_eq hq
      obtain ⟨u, w', hu, hw', rfl⟩ := h
      exact ⟨u, u ^ e' * w', hu, ⟨u, w', hu, hw', rfl⟩, by rw [pow_add, mul_assoc]⟩
    · obtain ⟨u, w', hu, hw', rfl⟩ := h
      exact ⟨u, w', hu, hw', rfl⟩
    · obtain ⟨u', w', hu', hw', rfl⟩ := h
      obtain ⟨u, wl, hu, hwl, rfl⟩ := rbs_insert_inv hw'
      exact ⟨u, u' ^ e' * wl, hu, ⟨u', wl, hu', hwl, rfl⟩, by ring⟩

/-- **A product with one more base**: its word is the other's times the base's. -/
theorem rmono_insert {a b : Mono} {B : Base} (hfp : a.fp = b.fp) (hk : a.k = b.k)
    (hbs : a.bs = insertBs (B, 1) b.bs) {u va vb : E} (hu : RBase M fp B u) (ha : RMono M fp a va)
    (hb : RMono M fp b vb) : va = vb * u := by
  obtain ⟨w, hw, rfl⟩ := ha
  obtain ⟨w', hw', rfl⟩ := hb
  rw [hbs] at hw
  obtain ⟨u', wl, hu', hwl, rfl⟩ := rbs_insert_inv hw
  rw [rbase_uniq hu' hu, rbs_uniq hwl hw', hfp, hk]
  ring


/-- **A product with one more base and a larger offset**: its word is the other's times the base's
times `g^c`. -/
theorem rmono_insert' {a b : Mono} {B : Base} (hfp : a.fp = b.fp) (hk : b.k ≤ a.k)
    (hbs : a.bs = insertBs (B, 1) b.bs) {u va vb : E} (hu : RBase M fp B u) (ha : RMono M fp a va)
    (hb : RMono M fp b vb) : va = vb * u * ofK (Parameters.g ^ (a.k - b.k)) := by
  obtain ⟨w, hw, rfl⟩ := ha
  obtain ⟨w', hw', rfl⟩ := hb
  rw [hbs] at hw
  obtain ⟨u', wl, hu', hwl, rfl⟩ := rbs_insert_inv hw
  rw [rbase_uniq hu' hu, rbs_uniq hwl hw', hfp, show a.k = b.k + (a.k - b.k) by omega, pow_add, ofK_mul,
    show b.k + (a.k - b.k) - b.k = a.k - b.k by omega]
  ring
end

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ} {w : Wit}

/-- **A cell holding a base's word** at an honest frame. -/
theorem holdsBase_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {o : ℕ} {B : Base} (h2 : 2 ≤ o)
    (hlt : o < fsN j) (h : holdsBase j w o B = true) : RBase (refMem r.img) e.I.fp B (refMem r.img (e.I.fp + o)) := by
  cases B with
  | fr b =>
    simp only [holdsBase, beq_iff_eq] at h
    subst h; rfl
  | hp q d =>
    have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
    obtain ⟨vs, hw, hF, hev, hwa, hws⟩ := t.wit hr hW
    simp only [holdsBase, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hq2, hqlt⟩, h⟩ := h
    obtain ⟨a, ha, hb⟩ := List.any_eq_true.mp h
    cases a with
    | load y p d' =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      obtain ⟨⟨hy, hp⟩, rfl⟩ := hb
      have hon := hwa _ ha
      have hpc := t.cell hr hF (x := p) (namedOf_atom hon (by simp [atomUses])) (by rw [hp]; exact hq2)
        (by rw [hp]; exact hqlt)
      have hyc := t.cell hr hF (x := y) (namedOf_atom hon (by simp [atomUses])) (by rw [hy]; exact h2)
        (by rw [hy]; exact hlt)
      rw [hp] at hpc
      rw [hy] at hyc
      obtain ⟨-, hld⟩ : LoadHolds r.img.read (e.σ p) d' (e.σ y) := hev _ hon
      obtain ⟨x, hx, hxa⟩ := read_pow hld hκ
      refine ⟨x, ⟨?_, hx⟩, ?_⟩
      · rw [hpc, Mode.limb_mul_ofK]; exact hxa
      · rw [hyc]
        rw [hxa] at hld
        exact ((refRd_img hκ r.img) _ _ (by unfold maxCells at hx; omega) hld).2
    | _ => simp at hb

/-- **The cells holding a cell's word** at an honest frame. -/
theorem eqCells_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {a b : ℕ} (ha : 2 ≤ a ∧ a < fsN j)
    (hb : 2 ≤ b ∧ b < fsN j) (h : b ∈ eqCells j w a) :
    refMem r.img (e.I.fp + a) = refMem r.img (e.I.fp + b) := by
  simp only [eqCells, List.mem_cons, List.mem_filterMap] at h
  rcases h with rfl | ⟨c, hc, hb'⟩
  · rfl
  obtain ⟨vs, hw, hF, hev, hwa, hws⟩ := t.wit hr hW
  cases c with
  | copy d s =>
    have hon := hwa _ hc
    have hm : e.σ d = e.σ s := hev _ hon
    have cell : ∀ v ∈ atomUses (.copy d s), 2 ≤ cellJ j v → cellJ j v < fsN j →
        refMem r.img (e.I.fp + cellJ j v) = e.σ v := fun v hv h2 hlt ↦
      t.cell hr hF (namedOf_atom hon hv) h2 hlt
    simp only at hb'
    split_ifs at hb' with hd hs
    · simp only [beq_iff_eq, Option.some.injEq] at hd hb'
      rw [← hd, ← hb', cell d (by simp [atomUses]) (by rw [hd]; exact ha.1) (by rw [hd]; exact ha.2),
        cell s (by simp [atomUses]) (by rw [hb']; exact hb.1) (by rw [hb']; exact hb.2), hm]
    · simp only [beq_iff_eq, Option.some.injEq] at hs hb'
      rw [← hs, ← hb', cell s (by simp [atomUses]) (by rw [hs]; exact ha.1) (by rw [hs]; exact ha.2),
        cell d (by simp [atomUses]) (by rw [hb']; exact hb.1) (by rw [hb']; exact hb.2), hm]
  | _ => simp at hb'

/-- **A top-level product at an honest frame**: `[p] = [c]·[o]`, `p` and `o` cells `okP` and `okO`
take. -/
theorem mulBy_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {c : ℕ} {okP okO : ℕ → Bool}
    (hc : 2 ≤ c ∧ c < fsN j) (h : mulBy j w (eqCells j w c) okP okO = true) :
    ∃ p o, okP p = true ∧ okO o = true ∧
      refMem r.img (e.I.fp + p) = refMem r.img (e.I.fp + c) * refMem r.img (e.I.fp + o) := by
  obtain ⟨vs, hw, hF, hev, hwa, hws⟩ := t.wit hr hW
  obtain ⟨a, ha, hb⟩ := List.any_eq_true.mp h
  cases a with
  | mul d x y =>
    have hon := hwa _ ha
    have hm : e.σ d = e.σ x * e.σ y := hev _ hon
    simp only [inFr, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hb
    obtain ⟨⟨⟨⟨hb, hd⟩, hx⟩, hy⟩, hokP⟩ := hb
    have cell : ∀ v ∈ atomUses (.mul d x y), 2 ≤ cellJ j v → cellJ j v < fsN j →
        refMem r.img (e.I.fp + cellJ j v) = e.σ v := fun v hv h2 hlt ↦
      t.cell hr hF (namedOf_atom hon hv) h2 hlt
    have ed := cell d (by simp [atomUses]) hd.1 hd.2
    have ex := cell x (by simp [atomUses]) hx.1 hx.2
    have ey := cell y (by simp [atomUses]) hy.1 hy.2
    rcases hb with ⟨hcx, hoy⟩ | ⟨hcy, hox⟩
    · refine ⟨_, _, hokP, hoy, ?_⟩
      rw [ed, hm, eqCells_top t hr hW hc hx hcx, ex, ey]
    · refine ⟨_, _, hokP, hox, ?_⟩
      rw [ed, hm, eqCells_top t hr hW hc hy hcy, ex, ey, mul_comm]
  | _ => simp at hb

theorem cellLt_bounds {o N : ℕ} (h : cellLt j w o N = true) : 2 ≤ o ∧ o < fsN j := by
  simp only [cellLt, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h2, hlt⟩, -⟩, -⟩ := h
  exact ⟨h2, hlt⟩

/-- **F4 at an honest frame**: a run over a product scaled by a factor lies inside the run up to the
product's exponent. -/
theorem shift_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {x : Mode.Res} (hx : shiftB j w x = true) :
    RRes (refMem r.img) e.I.fp x := by
  match x, hx with
  | .sub a [b], hx =>
    simp only [shiftB] at hx
    cases hc : frEx a.hi with
    | none => rw [hc] at hx; cases hx
    | some c =>
      rw [hc] at hx
      have hah := frEx_eq hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hx
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨hal, hbl⟩, haS⟩, hbS⟩, hd⟩, hfp⟩, hk⟩, hcl⟩, hany⟩ := hx
      obtain ⟨⟨B, eB⟩, hBm, hB⟩ := List.any_eq_true.mp hany
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hB
      obtain ⟨⟨heB, hbs⟩, hm⟩ := hB
      subst heB
      obtain ⟨ec, hec, hcw⟩ := cellLt_top t hr hW hcl
      obtain ⟨p, o, hhi, hoo, hpo⟩ := mulBy_top t hr hW (cellLt_bounds hcl) hm
      simp only [Bool.and_eq_true] at hoo
      obtain ⟨hob, hol⟩ := hoo
      obtain ⟨eo, heo, how⟩ := cellLt_top t hr hW hol
      have hu := holdsBase_top t hr hW (cellLt_bounds hol).1 (cellLt_bounds hol).2 hob
      -- the product's exponent, below the run's bound
      have hprod : ∀ ep, ep < 2 ^ 62 → refMem r.img (e.I.fp + p) = ofK (Parameters.g ^ ep) → ep = ec + eo :=
        fun ep hep hvp ↦ by
          rw [hpo, hcw, how, ← ofK_mul, ← pow_add] at hvp
          exact (gpow_inj (by omega) (by omega) (ofK_injective hvp)).symm
      have hbound : ∀ yhi, RIdx (refMem r.img) e.I.fp b.hi yhi → ec + eo ≤ yhi := fun yhi hy ↦ by
        unfold shiftHi at hhi
        split at hhi
        · rename_i p' hb'
          simp only [beq_iff_eq] at hhi
          subst hhi
          rw [hb'] at hy
          obtain ⟨vp, ep, hvp, hvp', hep, hyy⟩ := hy
          change refMem r.img (e.I.fp + p) = vp at hvp
          rw [hvp'] at hvp
          rw [hyy, hprod ep hep hvp]
          omega
        · rename_i H hb'
          rw [hb'] at hy
          change yhi = H at hy
          obtain ⟨ep, hep, hvp⟩ := cellLt_top t hr hW hhi
          rw [hprod ep (by have := (show H + 1 ≤ 2 ^ 62 from by
            simp only [cellLt, Bool.and_eq_true, decide_eq_true_eq] at hhi; exact hhi.1.2); omega) hvp] at hep
          omega
        · cases hhi
      refine ⟨0, ec, by rw [hal]; rfl, by rw [hah]; exact ⟨_, ec, hcw, rfl, by omega, rfl⟩,
        fun vq hvq jj _ hjj ↦ ⟨b, List.mem_singleton_self _, fun vb ylo yhi hvb hlo hy ↦ ?_⟩⟩
      rw [hbl] at hlo
      have hyb := hbound yhi hy
      refine ⟨eo + jj, by simp only [RIdx] at hlo; omega, by omega, ?_⟩
      rw [rmono_insert hfp hk hbs hu hvq hvb, how, haS, hbS, hd]
      simp only [one_mul, ofK_gpow]
      rw [show eo + jj + b.d = eo + (jj + b.d) by omega, pow_add]
      ring
  | .sub _ [], hx => simp [shiftB] at hx
  | .sub _ (_ :: _ :: _), hx => simp [shiftB] at hx
  | .lt _ _, hx => simp [shiftB] at hx
  | .nz _, hx => simp [shiftB] at hx
  | .name _, hx => simp [shiftB] at hx

end

/-! ## F2: a read guarded by the side section -/

theorem sideShape_eq {a b : Rng} {q r lo hi : ℕ} (h : sideShape a b = some (q, r, lo, hi)) :
    ∃ T, a.q.bs = [(.fr T, 1), (.hp q r, 1)] ∧ b.q.bs = [(.fr T, 1)] ∧ b.lo = .num lo ∧ b.hi = .num hi := by
  unfold sideShape at h
  split at h
  · rename_i T q' r' T' lo' hi' hA hB hL hH
    split_ifs at h with hT
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨T, hA, by rw [hB, hT], hL, hH⟩
  · cases h

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ} {w : Wit}

/-- The values `tabVals` lists hold the exponent tables at an honest frame. -/
theorem tabVals_top (t : TopAt A r K i e j) (hr : r.Ok) {G : V} (hG : G ∈ tabVals j) :
    B1.ExpTables r.img.read (e.σ G) := by
  obtain ⟨f, bufs, kids, hn⟩ := t.node
  obtain ⟨i', rfl, hi', hname, hfi, hc, -⟩ := fn_of_idx t.idx
  obtain ⟨c, hcm, hcf⟩ := List.mem_filterMap.mp hG
  split_ifs at hcf with hcc
  simp only [Bool.and_eq_true, beq_iff_eq] at hcc
  obtain ⟨hc1, hc2⟩ := hcc
  rw [hn] at hfi hname
  simp only [Tree.name] at hfi hname
  have hq := carryQ_all hr e.I t.inst f e.σ bufs kids hn _ hfi c hcm (by rw [hc1, hc, hname]) G
    (by rw [← hc]; exact hcf)
  rw [hc2] at hq
  exact hq.1

/-- **F2 at an honest frame**: the side section puts the loaded group inside the block. -/
theorem side_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {x : Mode.Res} (hx : sideB j w x = true) :
    RRes (refMem r.img) e.I.fp x := by
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨vs, hw, hF, hev, hwa, hws⟩ := t.wit hr hW
  have hall : ∀ a ∈ w.as, a.Holds r.img.read e.σ :=
    fun a ha ↦ hev _ (hwa _ ha)
  match x, hx with
  | .sub a [b], hx =>
    simp only [sideB] at hx
    cases hs : sideShape a b with
    | none => rw [hs] at hx; cases hx
    | some s =>
      obtain ⟨q, rr, lo, hi⟩ := s
      rw [hs] at hx
      obtain ⟨T, hA, hB, hL, hH⟩ := sideShape_eq hs
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hafp, hbfp⟩, hbk⟩, hal⟩, hah⟩, haS⟩, had⟩, hbS⟩, hbd⟩, hq2⟩, hqlt⟩, hany⟩ := hx
      obtain ⟨ld, hld, hb'⟩ := List.any_eq_true.mp hany
      cases ld with
      | load y p r' =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hb'
        obtain ⟨⟨hp, rfl⟩, hb'⟩ := hb'
        split at hb'
        · rename_i N hN
          -- the loaded group, `g^gi`, `gi < N`
          obtain ⟨gi, hgi, hy⟩ := rcBound_sound (by omega) r.img hall hN
          have hon := hwa _ hld
          obtain ⟨-, hlr⟩ : LoadHolds r.img.read (e.σ p) r' (e.σ y) := hev _ hon
          have hpc := t.cell hr hF (x := p) (namedOf_atom hon (by simp [atomUses])) (by rw [hp]; exact hq2)
            (by rw [hp]; exact hqlt)
          rw [hp] at hpc
          -- its side, read at the tables
          unfold sideRead at hb'
          obtain ⟨m, hm, hb2⟩ := List.any_eq_true.mp hb'
          cases m with
          | mul P G y' =>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hb2
            obtain ⟨⟨rfl, hG⟩, hb3⟩ := hb2
            obtain ⟨l2, hl2, hb4⟩ := List.any_eq_true.mp hb3
            cases l2 with
            | load S P' off =>
              simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb4
              obtain ⟨⟨hPP, hoff⟩, hb4⟩ := hb4
              subst hoff
              split at hb4
              · rename_i w hwc
                have hS : e.σ S = w := hall _ (constOf_sound hwc)
                have hPm : e.σ P = e.σ G * e.σ y' := hall _ hm
                have hPl : LoadHolds r.img.read (e.σ P) B1.sideTabAt (e.σ S) := by
                  have := hall _ hl2; rw [hPP] at this; exact this
                have htab := tabVals_top t hr hG
                rw [hPm, hy, B1.Tables.tb_loadHolds_mul_gen_pow] at hPl
                simp only [LeanVM.Guest.Res.sideIn, List.all_eq_true, List.mem_range, List.any_eq_true,
                  Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
                  Bool.and_eq_false_iff] at hb4
                obtain ⟨⟨s, hs3, hs1, hs2⟩, hside⟩ := hb4 gi hgi
                have hT := htab.2.2.2 s hs3 gi hs1 hs2
                rw [add_comm] at hT
                have hws : w = LeanVM.Protocol.Verifier.eOfNat s := by
                  rw [← hS]; exact B1.Tables.tb_loadHolds_unique hPl hT
                have hin : lo ≤ gi ∧ gi < hi := by
                  rcases hside s hs3 with ((h1 | h1) | h1) | h1
                  · exact absurd hs1 (by simpa using h1)
                  · exact absurd hs2 (by simpa using h1)
                  · exact absurd hws (by simpa using h1)
                  · exact h1
                -- the run
                refine ⟨0, 1, by rw [hal]; rfl, by rw [hah]; rfl, fun vq hvq jj _ hjj ↦
                  ⟨b, List.mem_singleton_self _, fun vb ylo yhi hvb hlo hhi ↦ ?_⟩⟩
                rw [hL] at hlo
                rw [hH] at hhi
                change ylo = lo at hlo
                change yhi = hi at hhi
                subst hlo hhi
                obtain rfl : jj = 0 := by omega
                refine ⟨gi, hin.1, hin.2, ?_⟩
                obtain ⟨wq, hwq, rfl⟩ := hvq
                obtain ⟨wb, hwb, rfl⟩ := hvb
                rw [hA] at hwq
                rw [hB] at hwb
                obtain ⟨u1, w1, hu1, ⟨u2, w2, hu2, hw2, rfl⟩, rfl⟩ := hwq
                obtain ⟨u1', w1', hu1', hw1', rfl⟩ := hwb
                simp only [RBs] at hw2 hw1'
                subst hw2 hw1'
                simp only [RBase] at hu1 hu1'
                obtain ⟨z, ⟨hz, hzlt⟩, rfl⟩ := hu2
                rw [hpc, Mode.limb_mul_ofK] at hz
                have hrd : r.img.read (Parameters.g ^ z) = some (e.σ y') := by rw [← hz]; exact hlr
                rw [((refRd_img hκ r.img) _ _ (by unfold maxCells at hzlt; omega) hrd).2, hy, ← hu1, ← hu1',
                  hafp, hbfp, hbk, haS, had, hbS, hbd]
                simp only [pow_zero, one_mul, mul_one, Nat.add_zero, ofK_gpow]
                rw [pow_add]
                ring
              · cases hb4
            | _ => simp at hb4
          | _ => simp at hb2
        · cases hb'
      | _ => simp at hb'
  | .sub _ [], hx => simp [sideB] at hx
  | .sub _ (_ :: _ :: _), hx => simp [sideB] at hx
  | .lt _ _, hx => simp [sideB] at hx
  | .nz _, hx => simp [sideB] at hx
  | .name _, hx => simp [sideB] at hx

end

/-! ## F5: a run inside the run up to a factor times a constant -/

theorem numOf_eq {i : Mode.Idx} {n : ℕ} (h : numOf i = some n) : i = .num n := by
  match i, h with
  | .num n', h => simp only [numOf, Option.some.injEq] at h; rw [h]

theorem frExT_eq {i : Mode.Idx} {p t : ℕ} (h : frExT i = some (p, t)) : i = .ex (.fr p) t := by
  match i, h with
  | .ex (.fr p') t', h => simp only [frExT, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1, h.2]

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ} {w : Wit}

/-- **A product by a constant at an honest frame**: `[p] = g^(eo + z)`, `[o] = g^eo` holding the base. -/
theorem mulConst_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {p : ℕ} {B : Base}
    {ok : ℕ → Bool} (h : mulConst j w p B ok = true) :
    ∃ o eo z, eo < 2 ^ 33 ∧ z < 2 ^ 33 ∧ ok z = true ∧ RBase (refMem r.img) e.I.fp B (refMem r.img (e.I.fp + o)) ∧
      refMem r.img (e.I.fp + o) = ofK (Parameters.g ^ eo) ∧
      refMem r.img (e.I.fp + p) = ofK (Parameters.g ^ (eo + z)) := by
  obtain ⟨vs, hw, hF, hev, hwa, hws⟩ := t.wit hr hW
  have hall : ∀ a ∈ w.as, a.Holds r.img.read e.σ := fun a ha ↦ hev _ (hwa _ ha)
  obtain ⟨m, hm, hb⟩ := List.any_eq_true.mp h
  cases m with
  | mul P x y =>
    have hon := hwa _ hm
    have hmul : e.σ P = e.σ x * e.σ y := hall _ hm
    simp only [inFr, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
    obtain ⟨⟨hPf, hPp⟩, hb⟩ := hb
    have cell : ∀ v ∈ atomUses (.mul P x y), 2 ≤ cellJ j v → cellJ j v < fsN j →
        refMem r.img (e.I.fp + cellJ j v) = e.σ v := fun v hv h2 hlt ↦
      t.cell hr hF (namedOf_atom hon hv) h2 hlt
    have eP := cell P (by simp [atomUses]) hPf.1 hPf.2
    rw [hPp] at eP
    -- one factor the base, the other the constant
    have key : ∀ f c : V, (e.σ P = e.σ f * e.σ c) → f ∈ atomUses (.mul P x y) →
        holdsBase j w (cellJ j f) B = true → cellLt j w (cellJ j f) (2 ^ 33) = true →
        (match (constOf w.as c).bind powOf with
          | some z => decide (z < 2 ^ 33) && ok z
          | none => false) = true → ∃ o eo z, eo < 2 ^ 33 ∧ z < 2 ^ 33 ∧ ok z = true ∧
          RBase (refMem r.img) e.I.fp B (refMem r.img (e.I.fp + o)) ∧
          refMem r.img (e.I.fp + o) = ofK (Parameters.g ^ eo) ∧
          refMem r.img (e.I.fp + p) = ofK (Parameters.g ^ (eo + z)) := by
      intro f c hfc hf hhb hcl hc
      split at hc
      · rename_i z hz
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨wc, hwc, hpz⟩ := Option.bind_eq_some_iff.mp hz
        have hcw : e.σ c = wc := hall _ (constOf_sound hwc)
        obtain ⟨eo, heo, how⟩ := cellLt_top t hr hW hcl
        have hfb := cellLt_bounds hcl
        have ef := cell f hf hfb.1 hfb.2
        refine ⟨_, eo, z, heo, hc.1, hc.2, holdsBase_top t hr hW hfb.1 hfb.2 hhb, how, ?_⟩
        rw [eP, hfc, ← ef, how, hcw, powOf_sound hpz, ← ofK_mul, ← pow_add]
      · cases hc
    rcases hb with ⟨⟨hxb, hxl⟩, hxc⟩ | ⟨⟨hyb, hyl⟩, hyc⟩
    · exact key x y hmul (by simp [atomUses]) hxb hxl hxc
    · exact key y x (by rw [hmul, mul_comm]) (by simp [atomUses]) hyb hyl hyc
  | _ => simp at hb

/-- **F5 at an honest frame**: the run past the factor lies inside the run up to the factor times
the constant. -/
theorem run_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {x : Mode.Res}
    (hx : Res.runB j w x = true) : RRes (refMem r.img) e.I.fp x := by
  match x, hx with
  | .sub a [b], hx =>
    simp only [Res.runB] at hx
    cases hlo : numOf a.lo with
    | none => rw [hlo] at hx; cases hx
    | some lo =>
    cases hhi : numOf a.hi with
    | none => rw [hlo, hhi] at hx; cases hx
    | some hi =>
    cases hp : frExT b.hi with
    | none => rw [hlo, hhi, hp] at hx; cases hx
    | some pt =>
      obtain ⟨p, tt⟩ := pt
      rw [hlo, hhi, hp] at hx
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
      obtain ⟨⟨⟨⟨⟨⟨hlh, hbl⟩, hbS⟩, hbd⟩, hfp⟩, hk⟩, hany⟩ := hx
      obtain ⟨⟨B, eB⟩, -, hB⟩ := List.any_eq_true.mp hany
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hB
      obtain ⟨⟨heB, hbs⟩, hm⟩ := hB
      subst heB
      obtain ⟨o, eo, z, heo, hz, hok, hu, how, hpw⟩ := mulConst_top t hr hW hm
      simp only [decide_eq_true_eq] at hok
      refine ⟨lo, hi, by rw [numOf_eq hlo]; rfl, by rw [numOf_eq hhi]; rfl, fun vq hvq jj hjj1 hjj2 ↦
        ⟨b, List.mem_singleton_self _, fun vb ylo yhi hvb hyl hyh ↦ ?_⟩⟩
      rw [hbl] at hyl
      change ylo = 0 at hyl
      rw [frExT_eq hp] at hyh
      obtain ⟨vp, ep, hvp, hvp', hep, hyy⟩ := hyh
      change refMem r.img (e.I.fp + p) = vp at hvp
      rw [hvp', hpw] at hvp
      have hep' : ep = eo + z := (gpow_inj (by omega) (by omega) (ofK_injective hvp)).symm
      have hS : a.S * jj ≤ a.S * (hi - 1) := Nat.mul_le_mul_left _ (by omega)
      refine ⟨eo + (a.q.k - b.q.k) + a.S * jj + a.d, by omega, by omega, ?_⟩
      rw [rmono_insert' hfp hk hbs hu hvq hvb, how, hbS, hbd]
      simp only [one_mul, Nat.add_zero, ofK_gpow]
      rw [show eo + (a.q.k - b.q.k) + a.S * jj + a.d = eo + (a.q.k - b.q.k) + (a.S * jj + a.d) by omega,
        pow_add, pow_add]
      ring
  | .sub _ [], hx => simp [Res.runB] at hx
  | .sub _ (_ :: _ :: _), hx => simp [Res.runB] at hx
  | .lt _ _, hx => simp [Res.runB] at hx
  | .nz _, hx => simp [Res.runB] at hx
  | .name _, hx => simp [Res.runB] at hx

end

/-! ## The families' residuals -/

/-- **The `sub` families read off the code, at an honest frame.** -/
theorem subFam_top {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}
    {w : Wit} (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {x : Mode.Res} (hx : subFamB j w x = true) :
    RRes (refMem r.img) e.I.fp x := by
  simp only [LeanVM.Guest.Res.subFamB, Bool.or_eq_true] at hx
  rcases hx with (hx | hx) | hx
  · exact shift_top t hr hW hx
  · exact side_top t hr hW hx
  · exact run_top t hr hW hx

end

end LeanVM.Guest.EndExec
