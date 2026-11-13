/-
  LeanVM.Guest.B1.Ring.TargetComplete

  `ring_switch_target` is complete in the uniform placed form (`CompleteAtD`): its chain at the
  bump allocator's position, its loop loading the slices, the challenges and the chain.
-/

module

public import LeanVM.Guest.B1.Ring.Loop14Complete
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.B1.Fwd.PureIn
public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.Data.NameStrings

/-!
# `ring_switch_target`, placed (TRIAGE G #64, #65)

On the caller's words, the 64 slices `s` at `g^bs` and the sixteen challenges `chs` at `g^bm`,
`ring_switch_target` is complete at every frame pointer `fp` (`rst_completeAt`): its chain
(`HeapBuf` of 72 words) at `fp + fs "ring_switch_target"` holds the honest rows
`chainWords s (chs.drop 8)`, its `ring_switch_target_loop0` (pure) is complete by `l13_relIn` lifted by
`Lift.completeAtD_of_relIn`, and it returns `ringTarget s f g`. The body's valuation is its
evaluation (`rstσ`); its value at the `ret` is `ringTarget` by the soundness theorem
`ring_switch_target_holds` (`rst_sigma`), the relation it gives read on the honest words.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## The body -/

/-- `ring_switch_target`'s statements before its `ret`. -/
def rstPre : List Stmt :=
  [.atom (.hint (.alloc (.n 2) 72))] ++
  ((List.range 8).map fun p ↦
    [Stmt.atom (.const (.n (3 + p)) (word 0 0)), .atom (.load (.n (3 + p)) (.n 2) p)]).flatten ++
  [.atom (.const (.n 11) (word 1 0)), .call name% «ring_switch_target_loop0» [.n 11, .n 1, .n 0, .n 2] [],
    .atom (.const (.n 12) (word 27 0)), .atom (.mul (.n 13) (.n 2) (.n 12)),
    .atom (.load (.n 14) (.n 1) 0), .atom (.load (.n 15) (.n 13) 0),
    .atom (.mul (.n 16) (.n 14) (.n 15))] ++
  ((List.range 7).map fun p ↦ tbBlock (p + 1)).flatten ++
  [.atom (.const (.n 269) (word 9223372036854775808 0)), .atom (.mul (.n 270) (.n 268) (.n 269))]

theorem rstT_split : rstT = rstPre ++ [.ret [.n 270]] := by
  simp only [rstT, rstPre, List.append_assoc, List.cons_append, List.nil_append]

theorem rst_body' : (fn% «ring_switch_target»).body = rstPre ++ [.ret [.n 270]] := by
  rw [rst_body, rstT_split]

theorem rst_flat : rstPre.all Stmt.flat = true := by decide +kernel

theorem rst_addrs : rstPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem rst_allocs : rstPre.filterMap Main.Stmt.allocSz = [(.n 2, .inl 72)] := by decide +kernel

theorem rst_not_loop : coreProgram.loop "ring_switch_target" = false := by decide +kernel

theorem l13_pure : coreProgram.PureIn [name% «ring_switch_target_loop0»] := Tables.pureIn_of_pureInB (by decide +kernel)

theorem rst_chk : chk 2 rstT = some 271 := by decide +kernel

/-- The zeros of the chain's row `0`. -/
def rstS : List Atom := (List.range 8).map fun p => Atom.load (.n (3 + p)) (.n 2) p

theorem rst_stores : storesOf 2 rstT = rstS := by decide +kernel

/-- The loads `ring_switch_target` needs a word for: the challenges (`1`), the chain's last row
(`13`). -/
def rstLoadOk : Atom → Bool
  | .load _ (.n 1) off => decide (off < 8)
  | .load _ (.n 13) off => decide (off < 8)
  | _ => false

theorem rst_needs : (rtAtoms rstPre).all (fun a => decide (a ∈ rstS) || !needsSide a ||
    rstLoadOk a) = true := by decide +kernel

/-- An atom or a call. -/
def atomOrCall : Stmt → Bool
  | .atom _ => true
  | .call .. => true
  | _ => false

theorem rst_kinds : rstPre.all atomOrCall = true := by decide +kernel

theorem rst_callS : rstPre.filterMap Main.Stmt.callS =
    [(none, name% «ring_switch_target_loop0», [.n 11, .n 1, .n 0, .n 2], [])] := by decide +kernel

theorem rst_callSF (σ : Val) : rstPre.filterMap (Stmt.callSF σ) =
    [(none, name% «ring_switch_target_loop0», [.n 11, .n 1, .n 0, .n 2], [])] := by
  rw [← rst_callS]
  refine List.filterMap_congr fun s hs => ?_
  have := List.all_eq_true.mp rst_kinds s hs
  cases s <;> simp_all [Stmt.callSF, atomOrCall]

/-- The loads of `ring_switch_target`: the challenges (`1`), the chain's row `0` (`2`, the
stores) and its last row (`13`). -/
def rstLoadIn : Atom → Bool
  | .load _ (.n 1) off => decide (off < 8)
  | .load _ (.n 2) off => decide (off < 8)
  | .load _ (.n 13) off => decide (off < 8)
  | .load .. => false
  | _ => true

theorem rstLoadIn_load {d p : V} {off : ℕ} (h : rstLoadIn (.load d p off) = true) :
    (p = .n 1 ∧ off < 8) ∨ (p = .n 2 ∧ off < 8) ∨ (p = .n 13 ∧ off < 8) := by
  unfold rstLoadIn at h
  split at h <;> simp_all

theorem rst_loadIn : (rtAtoms rstPre).all rstLoadIn = true := by decide +kernel

/-- A statement other than an `ite`. -/
def rtNotIte : Stmt → Bool
  | .ite _ _ _ => false
  | _ => true

theorem rst_noIte : rstPre.all rtNotIte = true := by decide +kernel

/-- Without `ite`, the walk's loads are the statements' loads. -/
theorem rt_filterMap_of_loadsEv {σ : Val} : ∀ {pre : List Stmt}, pre.all rtNotIte = true →
    ∀ {q : V × ℕ}, q ∈ pre.flatMap (loadsEv σ) → q ∈ pre.filterMap Stmt.loadS
  | [], _, _, h => by simp at h
  | s :: pre, hni, q, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hni
    rw [List.flatMap_cons, List.mem_append] at h
    rcases h with h | h
    · cases s with
      | ite c z n => simp [rtNotIte] at hni
      | _ =>
        simp only [loadsEv, Option.mem_toList] at h
        simp [h]
    · have := rt_filterMap_of_loadsEv hni.2 h
      cases hs : Stmt.loadS s <;> simp [hs, this]

/-- The regions of `ring_switch_target_loop0`'s caller's words. -/
def l13Lin (bs bm bc : ℕ) (s chs : List E) : Main.Layout :=
  [(bs, s), (bm, chs), (bc, chainWords s (chs.drop 8))]

theorem l13_relIn_lin {rd : Reader} {bs bm bc : ℕ} {s chs : List E} (hs : s.length = 64)
    (hc : chs.length = 16) (hL : MemL rd (l13Lin bs bm bc s chs)) :
    coreProgram.RelIn rd (RegionL (l13Lin bs bm bc s chs)) name% «ring_switch_target_loop0»
      [1, ofK (Parameters.addressOfIndex bm), ofK (Parameters.addressOfIndex bs),
        ofK (Parameters.addressOfIndex bc)] [] := by
  have := l13_relIn hs hc (hL (bs, s) (by simp [l13Lin])) (hL (bm, chs) (by simp [l13Lin]))
    (hL (bc, chainWords s (chs.drop 8)) (by simp [l13Lin])) (R := RegionL (l13Lin bs bm bc s chs))
    (fun i hi => by
      rcases hi with hi | hi | hi
      · exact ⟨(bs, s), by simp [l13Lin], by simpa [hs] using hi⟩
      · exact ⟨(bm, chs), by simp [l13Lin], by simpa [hc] using hi⟩
      · exact ⟨(bc, chainWords s (chs.drop 8)), by simp [l13Lin],
          by simpa [chainWords_length] using hi⟩)
    7 0 rfl
  rwa [pow_zero] at this

/-! ## The honest valuation -/

/-- The evaluated valuation of `ring_switch_target`'s body, its chain at `g^b`. -/
noncomputable def rstσ (rd : Reader) (sl mc : E) (b : ℕ) : Val :=
  B1.Val.ofArgs (ev rd (fun _ => ofK (Parameters.addressOfIndex b)) [sl, mc] rstT)

theorem rt_mem_rstT {s : Stmt} (h : s ∈ rstPre) : s ∈ rstT := by
  rw [rstT_split]; exact List.mem_append_left _ h

/-- **`ring_switch_target`'s statements hold** on their evaluated valuation, over the honest chain,
and its `ret` is `ringTarget`. -/
theorem rst_sigma {rd : Reader} {bs bm b : ℕ} {s chs : List E} (hs : s.length = 64)
    (hc : chs.length = 16) (hsl : ReadsAt rd (ofK (Parameters.addressOfIndex bs)) s)
    (hmc : ReadsAt rd (ofK (Parameters.addressOfIndex bm)) chs)
    (hch : ReadsAt rd (ofK (Parameters.addressOfIndex b)) (chainWords s (chs.drop 8))) :
    rstσ rd (ofK (Parameters.addressOfIndex bs)) (ofK (Parameters.addressOfIndex bm)) b (.n 0) =
        ofK (Parameters.addressOfIndex bs) ∧
      rstσ rd (ofK (Parameters.addressOfIndex bs)) (ofK (Parameters.addressOfIndex bm)) b (.n 1) =
        ofK (Parameters.addressOfIndex bm) ∧
      rstσ rd (ofK (Parameters.addressOfIndex bs)) (ofK (Parameters.addressOfIndex bm)) b (.n 2) =
        ofK (Parameters.addressOfIndex b) ∧
      rstσ rd (ofK (Parameters.addressOfIndex bs)) (ofK (Parameters.addressOfIndex bm)) b (.n 11) = 1 ∧
      rstσ rd (ofK (Parameters.addressOfIndex bs)) (ofK (Parameters.addressOfIndex bm)) b (.n 13) =
        ofK (Parameters.addressOfIndex b) * gen ^ 64 ∧
      (∀ st ∈ rstPre, SHolds (coreProgram.Rel rd) rd
        (rstσ rd (ofK (Parameters.addressOfIndex bs)) (ofK (Parameters.addressOfIndex bm)) b) st) ∧
      rstσ rd (ofK (Parameters.addressOfIndex bs)) (ofK (Parameters.addressOfIndex bm)) b (.n 270) =
        ringTarget s (chs.take ringMapWidth) (chs.drop ringMapWidth) := by
  set sl := ofK (Parameters.addressOfIndex bs)
  set mc := ofK (Parameters.addressOfIndex bm)
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = rstσ rd sl mc b := ⟨_, rfl⟩
  rw [← hσdef]
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => ofK (Parameters.addressOfIndex b)) rstT [sl, mc] rst_chk
  rw [show [sl, mc].length = 2 from rfl, rst_stores, ← rstσ, ← hσdef] at hgs
  have gA : ∀ a ∈ rtAtoms rstPre, Good rd rstS (fun _ => ofK (Parameters.addressOfIndex b)) σ a :=
    fun a ha => hgs (.atom a) (rt_mem_rstT (rt_mem_atoms ha))
  have hpar : ∀ i (hi : i < 2), σ (.n i) = [sl, mc].getD i 0 := fun i hi => by
    rw [hσdef]; exact ev_params rd _ (l := [sl, mc]) rst_chk (by simpa using hi)
  have e0 := hpar 0 (by omega)
  have e1 := hpar 1 (by omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at e0 e1
  have mA : ∀ a, Stmt.atom a ∈ rstPre → a ∈ rtAtoms rstPre := fun a h ↦ rt_atoms_mem h
  have hmem : ∀ st ∈ [Stmt.atom (.const (.n 11) (word 1 0)),
      .call name% «ring_switch_target_loop0» [.n 11, .n 1, .n 0, .n 2] [], .atom (.const (.n 12) (word 27 0)),
      .atom (.mul (.n 13) (.n 2) (.n 12))], st ∈ rstPre := fun st h ↦ by
    simp only [rstPre, List.mem_append]; exact Or.inl (Or.inl (Or.inr (by simp at h ⊢; tauto)))
  have e2 : σ (.n 2) = ofK (Parameters.addressOfIndex b) :=
    gA _ (mA _ (by simp [rstPre]) : Atom.hint (.alloc (.n 2) 72) ∈ rtAtoms rstPre)
  have e11 : σ (.n 11) = 1 := by
    rw [← word_one]; exact gA (.const (.n 11) (word 1 0)) (mA _ (hmem _ (by simp)))
  have e12 : σ (.n 12) = word 27 0 := gA (.const (.n 12) (word 27 0)) (mA _ (hmem _ (by simp)))
  have e13 : σ (.n 13) = ofK (Parameters.addressOfIndex b) * gen ^ 64 := by
    have := gA _ (mA _ (hmem _ (by simp)) : Atom.mul (.n 13) (.n 2) (.n 12) ∈ rtAtoms rstPre)
    simp only [Good] at this
    rw [ite_pos' ⟨by decide, by decide⟩] at this
    rw [this, e2, e12, word_27]
  have hgl : (chs.drop 8).length = 8 := by simp [hc]
  -- the side conditions
  have hside : ∀ a ∈ rtAtoms rstPre, a ∉ rstS → needsSide a = true →
      a.Holds rd σ ∨ Side rd rstS σ a := by
    intro a ha haS hns
    right
    have hok := List.all_eq_true.mp rst_needs a ha
    simp only [hns, Bool.not_true, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq] at hok
    rcases hok with h | h
    · exact absurd h haS
    · match a, h with
      | .load d (.n 1) off, h =>
        simp only [rstLoadOk, decide_eq_true_eq] at h
        simp only [Side, ite_neg' haS, e1]
        exact rt_side_of_load (hmc off (by omega))
      | .load d (.n 13) off, h =>
        simp only [rstLoadOk, decide_eq_true_eq] at h
        simp only [Side, ite_neg' haS, e13]
        have := chain_load hch (j := 8) le_rfl h
        rw [← loadHolds_mul_gen_pow] at this
        exact rt_side_of_load this
  have hstores : ∀ a ∈ rtAtoms rstPre, a ∈ rstS → a.Holds rd σ := by
    intro a ha haS
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp haS
    have hp8 := List.mem_range.mp hp
    have hm : Stmt.atom (.const (.n (3 + p)) (word 0 0)) ∈ rstPre := by
      simp only [rstPre, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_flatten.mpr
        ⟨_, List.mem_map.mpr ⟨p, hp, rfl⟩, by simp⟩))))
    have hc0 : σ (.n (3 + p)) = 0 := by rw [← word_zero]; exact gA _ (mA _ hm)
    show LoadHolds rd (σ (.n 2)) p (σ (.n (3 + p)))
    rw [e2, hc0]
    have := chain_load hch (j := 0) (by omega) hp8
    simpa [rtHz] using this
  have hat : ∀ a ∈ rtAtoms rstPre, a.Holds rd σ :=
    atoms_holds_stores gA hside fun _ a ha haS => hstores a ha haS
  -- the statements
  have hS : ∀ st ∈ rstPre, SHolds (coreProgram.Rel rd) rd σ st := by
    intro st hst
    have hk := List.all_eq_true.mp rst_kinds st hst
    cases st with
    | atom a => exact hat a (mA a hst)
    | call f args rets =>
      have hm : (Option.none, f, args, rets) ∈ rstPre.filterMap (Stmt.callSF σ) :=
        List.mem_filterMap.mpr ⟨_, hst, rfl⟩
      rw [rst_callSF, List.mem_singleton] at hm
      simp only [Prod.mk.injEq] at hm
      obtain ⟨-, rfl, rfl, rfl⟩ := hm
      show coreProgram.Rel rd name% «ring_switch_target_loop0» [σ (.n 11), σ (.n 1), σ (.n 0), σ (.n 2)] []
      rw [e11, e1, e0, e2]
      exact (l13_relIn_lin hs hc (bc := b) (fun q hq ↦ by
        simp only [l13Lin, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact hsl
        · exact hmc
        · exact hch)).rel
    | _ => simp [atomOrCall] at hk
  refine ⟨e0, e1, e2, e11, e13, hS, ?_⟩
  -- the return, by soundness
  have hrel : coreProgram.Rel rd "ring_switch_target" [sl, mc] [σ (.n 270)] :=
    (rel_iff_sem find_rst _ _).mpr ⟨σ, by
      show [Core.V.n 0, .n 1].map σ = _
      simp only [List.map_cons, List.map_nil, e0, e1], by
      have h := holdsList_straight (C := coreProgram.Rel rd) (rd := rd) (σ := σ) rstPre [.n 270] False
        (fun rs => rs = [σ (.n 270)]) hS rfl
      rw [← rst_body'] at h
      exact h⟩
  obtain ⟨s', ch', hs', hc', hsl', hmc', hr⟩ := ring_switch_target_holds rd _ _ hrel
  have e1' : s' = s := rt_readsAt_unique (by rw [hs', hs]; rfl) hsl' hsl
  have e2' : ch' = chs := rt_readsAt_unique (by rw [hc', hc]; rfl) hmc' hmc
  subst e1' e2'
  simpa using hr

/-! ## Placed -/

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- `rst_completeAt`'s valuation, as `completeAt_flatD` asks it. -/
theorem rst_hσ {bs bm : ℕ} {s chs : List E} (hs : s.length = 64) (hc : chs.length = 16) (fp : ℕ)
    (rd : Reader) (hB : MemL rd (bufL (fp + fs "ring_switch_target") [72]
      [chainWords s (chs.drop 8)])) (hLin : MemL rd [(bs, s), (bm, chs)]) (o : List E × Main.Layout)
    (ho1 : o.1 = []) :
    ∃ σ : Val, (fn% «ring_switch_target»).params.map σ = [ofK (Parameters.addressOfIndex bs),
        ofK (Parameters.addressOfIndex bm)] ∧ (∀ s ∈ rstPre, DispOk σ s) ∧
      Stmt.HoldsList (coreProgram.Rel rd) rd σ (fn% «ring_switch_target»).body False
        (fun r => r = [ringTarget s (chs.take ringMapWidth) (chs.drop ringMapWidth)]) ∧
      (rstPre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = [72] ∧
      ((rstPre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
        (bases (fp + fs "ring_switch_target") [72]).map (fun b => ofK (Parameters.addressOfIndex b)) ∧
      CallsMatch σ ((rstPre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
        [⟨name% «ring_switch_target_loop0», true, [1, ofK (Parameters.addressOfIndex bm), ofK (Parameters.addressOfIndex bs),
          ofK (Parameters.addressOfIndex (fp + fs "ring_switch_target"))],
          l13Lin bs bm (fp + fs "ring_switch_target") s chs, Returns []⟩] [o] ∧
      (∀ q ∈ rstPre.flatMap (loadsEv σ), ∃ i, (σ q.1).limb 0 * Parameters.addressOfIndex q.2 =
          Parameters.addressOfIndex i ∧
        (RegionL [(bs, s), (bm, chs)] i ∨
          RegionL (bufL (fp + fs "ring_switch_target") [72] [chainWords s (chs.drop 8)]) i)) := by
  set b := fp + fs "ring_switch_target"
  have hsl : ReadsAt rd (ofK (Parameters.addressOfIndex bs)) s := hLin (bs, s) (by simp)
  have hmc : ReadsAt rd (ofK (Parameters.addressOfIndex bm)) chs := hLin (bm, chs) (by simp)
  have hch : ReadsAt rd (ofK (Parameters.addressOfIndex b)) (chainWords s (chs.drop 8)) :=
    hB (b, chainWords s (chs.drop 8)) (by simp [bufL, bases])
  obtain ⟨e0, e1, e2, e11, e13, hS, e270⟩ := rst_sigma hs hc hsl hmc hch
  set σ := rstσ rd (ofK (Parameters.addressOfIndex bs)) (ofK (Parameters.addressOfIndex bm)) b
  have hcw : (chainWords s (chs.drop 8)).length = 72 := chainWords_length _ _
  refine ⟨σ, ?_, fun st hst => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show [Core.V.n 0, .n 1].map σ = _
    simp only [List.map_cons, List.map_nil, e0, e1]
  · have := List.all_eq_true.mp rst_kinds st hst
    cases st <;> simp_all [DispOk, atomOrCall]
  · have h := holdsList_straight (C := coreProgram.Rel rd) (rd := rd) (σ := σ) rstPre [.n 270] False
      (fun r => r = [ringTarget s (chs.take ringMapWidth) (chs.drop ringMapWidth)]) hS (by simp [e270])
    rw [← rst_body'] at h
    exact h
  · rw [rst_allocs]; rfl
  · rw [rst_allocs]; simp [bases, e2, b]
  · rw [rst_callSF]
    refine ⟨rfl, rfl, fun _ ↦ ⟨?_, ?_⟩, trivial⟩
    · show [σ (.n 11), σ (.n 1), σ (.n 0), σ (.n 2)] = _
      rw [e11, e1, e0, e2]
    · show [] = o.1
      rw [ho1]
  · intro q hq
    replace hq := rt_filterMap_of_loadsEv rst_noIte hq
    obtain ⟨st, hst, hsq⟩ := List.mem_filterMap.mp hq
    cases st with
    | atom a =>
      cases a with
      | load d p off =>
        simp only [Stmt.loadS, Option.some.injEq] at hsq
        subst hsq
        dsimp only
        have hok := List.all_eq_true.mp rst_loadIn _ (rt_atoms_mem hst)
        rcases rstLoadIn_load hok with ⟨rfl, hok⟩ | ⟨rfl, hok⟩ | ⟨rfl, hok⟩
        · rw [e1, Main.addr_ofK]
          exact ⟨_, rfl, Or.inl ⟨(bm, chs), by simp, by simp [hc]; omega⟩⟩
        · rw [e2, Main.addr_ofK]
          exact ⟨_, rfl, Or.inr ⟨(b, chainWords s (chs.drop 8)), by simp [bufL, bases],
            by simp only [hcw]; omega⟩⟩
        · rw [e13, rt_addr_mul]
          exact ⟨_, rfl, Or.inr ⟨(b, chainWords s (chs.drop 8)), by simp [bufL, bases],
            by simp only [hcw]; omega⟩⟩
      | _ => simp [Stmt.loadS] at hsq
    | _ => simp [Stmt.loadS] at hsq

/-- **`ring_switch_target` is complete, placed**: on the slices and the challenges, at every frame
pointer, its chain at the bump allocator's position, returning `ringTarget`. -/
theorem rst_completeAt (κ : ℕ) {bs bm : ℕ} {s chs : List E} (hs : s.length = 64)
    (hc : chs.length = 16) :
    CompleteAtD fs cert κ "ring_switch_target" [(bs, s), (bm, chs)]
      [ofK (Parameters.addressOfIndex bs), ofK (Parameters.addressOfIndex bm)]
      (Returns [ringTarget s (chs.take ringMapWidth) (chs.drop ringMapWidth)]) := by
  refine completeAt_flatD (fs := fs) (cert := cert) find_rst rst_not_loop κ _ _ _ rst_body' rst_flat
    rst_addrs [72] (fun _ ↦ [chainWords s (chs.drop 8)]) (fun _ ↦ by simp [chainWords_length])
    (fun fp ↦ [⟨name% «ring_switch_target_loop0», true, [1, ofK (Parameters.addressOfIndex bm),
      ofK (Parameters.addressOfIndex bs), ofK (Parameters.addressOfIndex (fp + fs "ring_switch_target"))],
      l13Lin bs bm (fp + fs "ring_switch_target") s chs, Returns []⟩])
    ?_ ?_ ?_ ?_
  · intro fp k hk _
    rw [List.mem_singleton] at hk
    subst hk
    exact Lift.completeAtD_of_relIn l13_pure (List.mem_singleton_self _)
      fun rd _ hL ↦ l13_relIn_lin hs hc hL
  · intro fp k hk _ i hi
    rw [List.mem_singleton] at hk
    subst hk
    obtain ⟨q, hq, hi⟩ := hi
    simp only [l13Lin, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact Or.inl ⟨_, by simp, hi⟩
    · exact Or.inl ⟨_, by simp, hi⟩
    · exact Or.inr ⟨_, by simp [bufL, bases], hi⟩
  · intro fp rd hB hLin k hk
    rw [List.mem_singleton] at hk
    subst hk
    intro q hq
    simp only [l13Lin, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hLin (bs, s) (by simp)
    · exact hLin (bm, chs) (by simp)
    · exact hB (fp + fs "ring_switch_target", chainWords s (chs.drop 8)) (by simp [bufL, bases])
  · intro fp outs ho rd _ hB hLin
    rcases outs with _ | ⟨o, _ | ⟨o', os⟩⟩
    · exact absurd ho (by simp [OutsOk])
    swap
    · exact absurd ho.2 (by simp [OutsOk])
    obtain ⟨ho', -⟩ := ho
    obtain ⟨ho1, -⟩ := ho' rfl
    exact rst_hσ hs hc fp rd hB hLin o ho1

end
end LeanVM.Guest.B1.VerifySub
