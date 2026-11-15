/-
  LeanVM.Guest.EndExecRS

  The residuals at the honest frames by family: the selectors' bounds from the instance's path,
  names free, the other families and the listed certificates as hypotheses.
-/

module

public import LeanVM.Guest.EndExecRT
public import LeanVM.Guest.Res.SelDefs

/-!
# The residuals by family

An honest frame (`TopAt`) is a `node` instance whose path returns and whose events hold on the
reference memory (`TopAt.events`: the tree is valid on any memory covering its writes,
`Covers.valid`). An order residual bounding a table jump's selector (`ltSelB`) holds there
(`ltSel_top`): the path passes the `match` or `dispatch`, so its selector is `g^e` below the count
of arms; a frame cell's selector is named on the path, so the frame holds it (`FrameHolds.val`); a
loaded selector's `load` holds on the reference, its pointer named, so the word the residual
names is the selector.

A nonzero divisor at a parameter (`nzB`) holds there (`nzPar_top`): the frame holds the
parameter, a loop helper's counter is a power of `g` (`TopAt.ctr`, `Res.insts_ctr`), and a listed
parameter is nonzero at every honest instance (`NzVal`, B1's).

`resTop_of_ok`: `ResTop` from `ResOk` of every certificate, the listed certificates' residuals
(`ResCert`), the `sub` family's and the exponent facts' order residuals (`ResOpen`) and the listed
parameters' `NzVal`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf entryOf FrameHolds fsN fn_of_idx cellJ namedOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (ltSelB allV scanFr_sound scanHp_sound allV_get ResOk famB)
open LeanVM.Prover.Exec

@[expose] public section

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

/-- **An honest frame's path, its events holding on the reference memory.** -/
theorem TopAt.events (t : TopAt A r K i e j) (hr : r.Ok) : ∃ vs, walk e.σ (coreOf j).body = .ret (e.pre ++ e.es) vs ∧
    FrameHolds r.img j e.I.fp e.σ (e.pre ++ e.es) vs e.I.kidFps e.I.hdr ∧
    ∀ ev ∈ e.pre ++ e.es, ev.Holds r.img.read e.σ := by
  obtain ⟨vs, hw, hF⟩ := t.path
  rw [← t.fn] at hw
  refine ⟨vs, hw, hF, ?_⟩
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  obtain ⟨f, bufs, kids, hn⟩ := t.node
  rcases insts_good r.T _ r.hdr hv e.I t.inst with ⟨args, rets, hval⟩ | ⟨_, _, hph⟩
  · rw [hn] at hval
    unfold Tree.Valid at hval
    obtain ⟨fn, hf, -, es', vs', hw', -, hes, -⟩ := hval
    obtain ⟨i', rfl, hi', -, hfi, hc, -⟩ := fn_of_idx t.idx
    rw [hn] at hfi
    simp only [Tree.name] at hfi
    obtain rfl : fn = coreProgram[i'] := Option.some.inj (hf.symm.trans hfi)
    rw [← hc, hw] at hw'
    obtain ⟨rfl, -⟩ := Out.ret.inj hw'
    exact hes
  · rw [hn] at hph; cases hph

/-- The frame holds each value the path names, at its cell inside the frame. -/
theorem TopAt.cell (t : TopAt A r K i e j) (hr : r.Ok) {vs : List V}
    (hF : FrameHolds r.img j e.I.fp e.σ (e.pre ++ e.es) vs e.I.kidFps e.I.hdr) {x : V}
    (hx : x ∈ namedOf (coreOf j).params (e.pre ++ e.es) vs) (h2 : 2 ≤ cellJ j x) (hlt : cellJ j x < fsN j) :
    refMem r.img (e.I.fp + cellJ j x) = e.σ x := by
  have hκ := logMemorySize_le_28 (e := r.exec) hr.size
  have hb := t.fb
  exact ((refRd_img hκ r.img) _ _ (by omega) (hF.val x hx h2 hlt)).2

/-- An atom on the path names its uses. -/
theorem namedOf_atom {ps : List V} {es : List Ev} {vs : List V} {a : Atom} {x : V} (ha : Ev.atom a ∈ es)
    (hx : x ∈ atomUses a) : x ∈ namedOf ps es vs :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, ha, hx⟩))

/-- **A selector's bound at an honest frame**: an order residual `ltSelB` accepts at the frame's
function holds of the reference. -/
theorem ltSel_top (t : TopAt A r K i e j) (hr : r.Ok) {x : Mode.Res} (hx : ltSelB j x = true)
    (hin : RIn (refMem r.img) e.I.fp x) : RRes (refMem r.img) e.I.fp x := by
  obtain ⟨vs, hw, hF, hev⟩ := t.events hr
  refine obl_rres hin ?_
  unfold ltSelB at hx
  split at hx
  · rename_i o N
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨⟨⟨hN, h2⟩, hlt⟩, hs⟩ := hx
    obtain ⟨y, ev, rfl, he, hσ, hy⟩ := scanFr_sound hs hw
    have hy' : y ∈ namedOf (coreOf j).params (e.pre ++ e.es) vs := by
      rcases hy with hy | ⟨a, ha, hya⟩
      · exact List.mem_append_left _ (List.mem_append_left _ hy)
      · exact namedOf_atom ha hya
    simp only [Obl]
    exact ⟨hN, ev, he, by rw [t.cell hr hF hy' h2 hlt, hσ]⟩
  · rename_i q k N
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨⟨⟨hN, h2⟩, hlt⟩, hs⟩ := hx
    obtain ⟨y, ev, he, hσ, hy⟩ := scanHp_sound hs hw
    rcases hy with hy | ⟨p, ha, rfl⟩
    · cases hy
    have hp := t.cell hr hF (namedOf_atom ha (by simp [atomUses])) h2 hlt
    obtain ⟨-, hld⟩ : LoadHolds r.img.read (e.σ p) k (e.σ y) := hev _ ha
    simp only [Obl]
    refine ⟨hN, fun z hz ↦ ⟨ev, he, ?_⟩⟩
    obtain ⟨hz1, hz2⟩ := hz
    rw [hp, limb_mul_ofK] at hz1
    have hld' : r.img.read (Parameters.g ^ z) = some (e.σ y) := by rw [← hz1]; exact hld
    have hκ := logMemorySize_le_28 (e := r.exec) hr.size
    rw [((refRd_img hκ r.img) _ _ (by unfold maxCells at hz2; omega) hld').2, hσ]
  · cases hx

/-- **A loop helper's counter at an honest frame is a power of `g`** (`Res.insts_ctr`). -/
theorem TopAt.ctr (t : TopAt A r K i e j) (hr : r.Ok) (hl : (coreOf j).loop = true) :
    ∃ p0 prest e', (coreOf j).params = p0 :: prest ∧ e.σ p0 = ofK (addressOfIndex e') := by
  obtain ⟨rd, hH, -⟩ := hr.honest
  obtain ⟨f, bufs, kids, hn⟩ := t.node
  obtain ⟨i', rfl, hi', -, hfi, hc, -⟩ := fn_of_idx t.idx
  rw [hn] at hfi
  simp only [Tree.name] at hfi
  rw [hc] at hl ⊢
  have hfs : ∀ f', 1 ≤ B2C.fs f' := fun f' ↦ by
    unfold B2C.fs; split <;> simp [B2C.mainFrame, Data.mainCells, Data.jtSlots]
  have hroot : Res.CtrOk coreProgram B2C.fs (r.T.total B2C.fs + 1) r.T := by
    intro f' σ' _ _ fn' hT' hg hl'
    have := (progOk_guest.loop f' fn' hg hl').1
    have hn' := hr.name
    rw [hT'] at hn'
    simp only [Tree.name] at hn'
    subst hn'
    exact absurd this (by decide)
  obtain ⟨p0, prest, e1, hps, hσ0, -⟩ := Res.insts_ctr hfs progOk_guest r.T _ r.hdr hH.valid le_rfl hroot e.I t.inst
    f e.σ bufs kids _ hn hfi hl
  exact ⟨p0, prest, e1, hps, hσ0⟩

end

/-- **A value nonzero at every honest instance of a function** (B1's). -/
def NzVal (f : String) (v : V) : Prop :=
  ∀ r : Ref, r.Ok → ∀ I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, ∀ σ bufs kids,
    I.t = .node f σ bufs kids → σ v ≠ 0

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

/-- **A nonzero divisor at a parameter at an honest frame**: the loop counter, a power of `g`, or a
parameter `NzVal` gives. -/
theorem nzPar_top (t : TopAt A r K i e j) (hr : r.Ok) {nzs : List (String × V)} (hnz : ∀ p ∈ nzs, NzVal p.1 p.2)
    {o : ℕ} (h : Res.nzB nzs j o = true) : RRes (refMem r.img) e.I.fp (.nz o) := by
  simp only [Res.nzB, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h2, hlt⟩, v, hv, rfl, hv'⟩ := h
  obtain ⟨vs, -, hF, -⟩ := t.events hr
  show refMem r.img (e.I.fp + cellJ j v) ≠ 0
  rw [t.cell hr hF (List.mem_append_left _ (List.mem_append_left _ hv)) h2 hlt]
  rcases hv' with hc | hl
  · unfold Res.ctrOf at hc
    by_cases hl : (coreOf j).loop = true
    · rw [ite_eq_left hl] at hc
      obtain ⟨p0, prest, e', hps, hσ⟩ := t.ctr hr hl
      rw [hps, List.head?_cons, Option.some.injEq] at hc
      subst hc
      rw [hσ]
      exact Mode.ofK_gpow_ne_zero _
    · rw [ite_eq_right hl] at hc; cases hc
  · obtain ⟨f, bufs, kids, hn⟩ := t.node
    obtain ⟨i', rfl, hi', hname, -, hc, -⟩ := fn_of_idx t.idx
    rw [hc, hname, hn] at hl
    exact hnz _ hl r hr e.I t.inst e.σ bufs kids hn

end

/-! ## Splits -/

section

variable {M : ℕ → E} {fp : ℕ}

theorem rbs_snoc {b0 : Base} {e0 : ℕ} : ∀ {bs : List (Base × ℕ)} {w : E}, RBs M fp (bs ++ [(b0, e0)]) w →
    ∃ u w1, RBase M fp b0 u ∧ RBs M fp bs w1 ∧ w = w1 * u ^ e0
  | [], w, ⟨u, w', hu, hw', hw⟩ => ⟨u, 1, hu, rfl, by rw [hw, show w' = 1 from hw']; ring⟩
  | (b, e) :: bs, w, ⟨u, w', hu, hw', hw⟩ => by
    obtain ⟨u0, w1, h0, h1, rfl⟩ := rbs_snoc hw'
    exact ⟨u0, u ^ e * w1, h0, ⟨u, w1, hu, h1, rfl⟩, by rw [hw]; ring⟩

/-- **A run inside a split** (`splitShape`): on a frame whose `[n]` is `g^(S·a + b)`, `[s] = g^a`
and `[r] = g^b`. -/
theorem split_rres {s r n S a b : ℕ} (hs : M (fp + s) = ofK (Parameters.g ^ a))
    (hr : M (fp + r) = ofK (Parameters.g ^ b))
    (hn : M (fp + n) = ofK (Parameters.g ^ (S * a + b))) (hlt : S * a + b < 2 ^ 62) {x : Mode.Res}
    (hx : Res.splitShape s r n S x = true) : RRes M fp x := by
  match x, hx with
  | .sub a' [b'], hx =>
    simp only [Res.splitShape, decide_eq_true_eq] at hx
    obtain ⟨hblo, hbhi, hbS, hbd, halo, h⟩ := hx
    have hyhi : ∀ yhi, RIdx M fp b'.hi yhi → yhi = S * a + b := fun yhi hy ↦ by
      rw [hbhi] at hy
      obtain ⟨v, e', hv, hve, he', hx⟩ := hy
      change M (fp + n) = v at hv
      rw [hn, hve] at hv
      have := gpow_inj (by omega) (by omega) (ofK_injective hv)
      omega
    have hylo : ∀ ylo, RIdx M fp b'.lo ylo → ylo = 0 := fun ylo hy ↦ by rw [hblo] at hy; exact hy
    show RSub M fp a' [b']
    rcases h with ⟨hq, hhi, hS, hd⟩ | ⟨hq, hhi, hS, hd⟩
    · have haS : a ≤ S * a := Nat.le_mul_of_pos_left a (by omega)
      refine ⟨0, a, by rw [halo]; rfl, by rw [hhi]; exact ⟨_, a, hs, rfl, by omega, rfl⟩,
        fun vq hvq j _ hj ↦ ⟨b', List.mem_singleton_self _, fun vb ylo yhi hvb hlo hhi' ↦
          ⟨S * j + a'.d, ?_, ?_, ?_⟩⟩⟩
      · rw [hylo ylo hlo]; omega
      · rw [hyhi yhi hhi']
        have : S * j + a'.d < S * a := by
          have : S * (j + 1) ≤ S * a := Nat.mul_le_mul_left _ (by omega)
          rw [Nat.mul_succ] at this; omega
        omega
      · rw [hq] at hvq
        rw [rmono_uniq hvq hvb, hS, hbS, hbd, one_mul, add_zero]
    · refine ⟨0, b, by rw [halo]; rfl, by rw [hhi]; exact ⟨_, b, hr, rfl, by omega, rfl⟩,
        fun vq hvq j _ hj ↦ ⟨b', List.mem_singleton_self _, fun vb ylo yhi hvb hlo hhi' ↦
          ⟨S * a + j, ?_, ?_, ?_⟩⟩⟩
      · rw [hylo ylo hlo]; omega
      · rw [hyhi yhi hhi']; omega
      · have e : ofK (Parameters.g ^ (S * a + j)) = ofK (Parameters.g ^ a) ^ S * ofK (Parameters.g ^ j) := by
          rw [pow_add, pow_mul', ofK_mul, Mode.ofK_pow (Parameters.g ^ a) S]
        rcases hq with hq | hq <;> rw [hq] at hvq <;> obtain ⟨w, hw, rfl⟩ := hvq <;>
          obtain ⟨wb, hwb, rfl⟩ := hvb
        · obtain ⟨u, w1, hu, hw1, rfl⟩ := rbs_snoc hw
          rw [rbs_uniq hw1 hwb, show u = ofK (Parameters.g ^ a) from hu.symm.trans hs, hS, hd, hbS, hbd, one_mul,
            one_mul, add_zero, add_zero, e]
          ring
        · obtain ⟨u, w1, hu, hw1, rfl⟩ := hw
          change M (fp + s) = u at hu
          rw [rbs_uniq hw1 hwb, ← hu, hs, hS, hd, hbS, hbd, one_mul, one_mul, add_zero, add_zero, e]
          ring
  | .sub _ [], hx => simp [Res.splitShape] at hx
  | .sub _ (_ :: _ :: _), hx => simp [Res.splitShape] at hx
  | .lt _ _, hx => simp [Res.splitShape] at hx
  | .nz _, hx => simp [Res.splitShape] at hx
  | .name _, hx => simp [Res.splitShape] at hx

end

/-- **A split of function `j`'s frames**: at each honest frame of `j`, `[n] = g^(S·a + b)` with
`[s] = g^a`, `[r] = g^b`, the cells those of `vs`, `vr`, `vn`. -/
def SplitAt (A : String → FnAl) (j : ℕ) (vs vr vn : V) (S : ℕ) : Prop :=
  ∀ (r : Ref) (K : Mode.Cert) (i : ℕ) (e : Bridge.Ent), r.Ok → TopAt A r K i e j → ∃ a b,
    refMem r.img (e.I.fp + cellJ j vs) = ofK (Parameters.g ^ a) ∧
    refMem r.img (e.I.fp + cellJ j vr) = ofK (Parameters.g ^ b) ∧
    refMem r.img (e.I.fp + cellJ j vn) = ofK (Parameters.g ^ (S * a + b)) ∧ S * a + b < 2 ^ 62

/-- **A run inside a split at an honest frame.** -/
theorem split_top {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}
    (t : TopAt A r K i e j) (hr : r.Ok)
    (hsp : ∀ p ∈ Res.splits, SplitAt A p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) {x : Mode.Res}
    (hx : Res.splitB j x = true) : RRes (refMem r.img) e.I.fp x := by
  obtain ⟨p, hp, hpx⟩ := List.any_eq_true.mp hx
  simp only [Bool.and_eq_true, beq_iff_eq] at hpx
  obtain ⟨rfl, hsh⟩ := hpx
  obtain ⟨a, b, hs, hr', hn, hlt⟩ := hsp p hp r K i e hr t
  exact split_rres hs hr' hn hlt hsh

/-! ## The assembly -/

/-- **One certificate's residuals at the honest frames.** -/
def ResCert (A : String → FnAl) (K : Mode.Cert) : Prop :=
  ∀ r : Ref, r.Ok → ∀ i < K.code.length, ∀ e j, TopAt A r K i e j →
    ∀ x ∈ (K.F.res.get i).getD [], RIn (refMem r.img) e.I.fp x → RRes (refMem r.img) e.I.fp x

/-- **A family's residuals at the honest frames**: each residual `p` accepts at the frame's
function. -/
def ResOpen (Ks : List Mode.Cert) (A : String → FnAl) (p : ℕ → Mode.Res → Prop) : Prop :=
  ∀ r : Ref, r.Ok → ∀ K ∈ Ks, ∀ i < K.code.length, ∀ e j, TopAt A r K i e j →
    ∀ x ∈ (K.F.res.get i).getD [], p j x → RIn (refMem r.img) e.I.fp x → RRes (refMem r.img) e.I.fp x

/-- **`ResTop` by family**: every certificate's residuals in the families, the listed ones', the
splits, the other `sub` residuals', the order residuals the exponent facts bound and the listed
parameters' nonzero values given. -/
theorem resTop_of_ok {Ks exc : List Mode.Cert} {nzs : List (String × V)} {A : String → FnAl}
    (hok : ∀ K ∈ Ks, ResOk exc nzs K) (hexc : ∀ K ∈ exc, ResCert A K)
    (hsp : ∀ p ∈ Res.splits, SplitAt A p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
    (hsub : ResOpen Ks A fun j x ↦ (∃ a bs, x = .sub a bs) ∧ Res.splitB j x = false)
    (hexp : ResOpen Ks A fun j x ↦ Res.ltExpB j x = true)
    (hnz : ∀ p ∈ nzs, NzVal p.1 p.2) : ResTop Ks A := by
  intro r hr K hK i hi e j t x hx hin
  rcases hok K hK with hK' | ⟨j0, hj0, hent, hall⟩
  · exact hexc K hK' r hr i hi e j t x hx hin
  obtain rfl : j = j0 := by
    obtain ⟨_, -, -, -, -, -, -, -, -, hj⟩ := fn_of_idx t.idx
    refine fnOf_entry_inj hj hj0 ?_
    have := t.entry
    simp only [entryOf, t.idx] at this
    rw [this, hent]
  cases hg : K.F.res.get i with
  | none => rw [hg] at hx; cases hx
  | some l =>
    rw [hg, Option.getD_some] at hx
    have hf := List.all_eq_true.mp (allV_get hall hg) x hx
    cases x with
    | name o => exact rres_name
    | lt a b =>
      simp only [famB, Bool.or_eq_true] at hf
      rcases hf with hf | hf
      · exact ltSel_top t hr hf hin
      · exact hexp r hr K hK i hi e j t _ (by rw [hg]; exact hx) hf hin
    | sub a bs =>
      cases hs : Res.splitB j (.sub a bs) with
      | true => exact split_top t hr hsp hs
      | false => exact hsub r hr K hK i hi e j t _ (by rw [hg]; exact hx) ⟨⟨a, bs, rfl⟩, hs⟩ hin
    | nz o => exact nzPar_top t hr hnz hf

end

end LeanVM.Guest.EndExec
