/-
  LeanVM.Guest.EndExecAFrSize

  A callee frame's hint reserves the next callee's block: `FrameSize alignA`, from the frame size
  check (`Bridge.frChk`) at the call the hint's site makes, but the hints it skips.
-/

module

public import LeanVM.Guest.EndExecAFrame
public import LeanVM.Guest.EndExecRT
public import LeanVM.Guest.Res.Down
public import LeanVM.Guest.Bridge.AllocFrDefs
public import LeanVM.Guest.Bridge.AllocChk.All

/-!
# The callee frames' sizes

`frameSize_alignA : FrSkip → FrameSize alignA`. At a frame hint the frame's next call is through the
hint's site (`frame_next`); the call comes from a call statement of the body (`walk_callOf`) at that
site, which fits the hint (`Bridge.frFits`), its callee's facts those of a listed compiled function
(`calFind_spec`):

* `alloc`: a `call` of a function no loop helper, entered, its block its frame;
* `allocArm`: a `dispatch`, its selector `g^j` at its cell, arm `j`'s callee entered, its block its
  frame;
* `allocFrames`: a conditional call of a loop helper ending at its second parameter: entered, its
  run makes `m` iterations from `g^e` (`chainB`), its block `m + 1` frames and the end
  `g^(e + m)` at the stop cell; not entered, the guard `g^e + end` zero, its block one frame.

`FrSkip` names the frame hints the check skips (`Bridge.AllocChk.frSkipAt`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Guest.Check (getF)
open LeanVM.Prover.Exec

public section

/-! ## The calls of a path, by statement -/

/-- **Call `c` of a path made by statement `st`.** -/
def CallOf (σ : Val) (c : Call) : Stmt → Prop
  | .call f args rets => c = ⟨f, args, rets, true⟩
  | .callIf b f args => c.f = f ∧ c.args = args ∧ c.rets = [] ∧ (c.taken = true ↔ σ b ≠ 0)
  | .dispatch x fs args rets => c.args = args ∧ c.rets = rets ∧ c.taken = true ∧
      ∃ j, fs[j]? = some c.f ∧ σ x = ofK (addressOfIndex j)
  | _ => False

theorem callOf_args {σ : Val} {c : Call} {st : Stmt} (h : CallOf σ c st) : stArgs st = c.args ∧ stRets st = c.rets := by
  cases st with
  | call f args rets => subst h; exact ⟨rfl, rfl⟩
  | callIf b f args => exact ⟨h.2.1.symm, h.2.2.1.symm⟩
  | dispatch x fs args rets => exact ⟨h.1.symm, h.2.1.symm⟩
  | _ => exact h.elim

section

variable {σ : Val} {p : Stmt → Bool}

theorem pick_callOf {x : V} {args rets : List V} : ∀ (gs : List String) (j : ℕ), ∀ c ∈ calls (pick σ x args rets j gs).evs,
    c.args = args ∧ c.rets = rets ∧ c.taken = true ∧ ∃ i, gs[i]? = some c.f ∧ σ x = ofK (addressOfIndex (j + i))
  | [], _, c, h => by simp [pick, Out.evs, calls] at h
  | g0 :: gs, j, c, h => by
    unfold pick at h
    split_ifs at h with hx
    · simp only [Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil, List.mem_cons,
        List.not_mem_nil, or_false] at h
      subst h
      exact ⟨rfl, rfl, rfl, 0, rfl, by rw [Nat.add_zero]; exact hx⟩
    · obtain ⟨h1, h2, h3, i, hi, hσ⟩ := pick_callOf gs (j + 1) c h
      exact ⟨h1, h2, h3, i + 1, hi, by rw [hσ, Nat.add_assoc, Nat.add_comm 1 i]⟩

mutual
/-- **A statement's path calls only at its call statements.** -/
theorem walk1_callOf : ∀ (s : Stmt), callsS p s = true → ∀ c ∈ calls (walk1 σ s).evs,
    ∃ st, p st = true ∧ CallOf σ c st
  | .atom a, _, c, h => by simp [walk1, Out.evs, calls, Ev.call?] at h
  | .ite b z m, hs, c, h => by
    rw [walk1, Out.calls_pre_inK] at h
    replace hs : (callsAll p z && callsAll p m) = true := hs
    simp only [Bool.and_eq_true] at hs
    split_ifs at h
    · exact walk_callOf z hs.1 c h
    · exact walk_callOf m hs.2 c h
  | .match_ x arms, hs, c, h => by
    rw [walk1] at h
    exact walkArms_callOf x arms 0 (show callsArms p arms = true from hs) c h
  | .call f args rets, hs, c, h => by
    simp only [walk1, Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil,
      List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact ⟨_, hs, rfl⟩
  | .callIf b f args, hs, c, h => by
    refine ⟨_, hs, ?_⟩
    rw [walk1] at h
    by_cases h0 : σ b = 0
    · simp only [h0, ↓reduceIte, Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil,
        List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      exact ⟨rfl, rfl, rfl, by simp [h0]⟩
    · simp only [h0, ↓reduceIte, Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil,
        List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      exact ⟨rfl, rfl, rfl, by simp [h0]⟩
  | .dispatch x gs args rets, hs, c, h => by
    rw [walk1] at h
    obtain ⟨h1, h2, h3, i, hi, hσ⟩ := pick_callOf gs 0 c h
    exact ⟨_, hs, h1, h2, h3, i, hi, by rw [hσ, Nat.zero_add]⟩
  | .ret _, _, c, h => by simp [walk1, Out.evs, calls] at h

/-- **A block's path calls only at its call statements.** -/
theorem walk_callOf : ∀ (ss : List Stmt), callsAll p ss = true → ∀ c ∈ calls (walk σ ss).evs,
    ∃ st, p st = true ∧ CallOf σ c st
  | [], _, c, h => by simp [walk, Out.evs, calls] at h
  | s :: ss, hs, c, h => by
    rw [walk] at h
    replace hs : (callsS p s && callsAll p ss) = true := hs
    simp only [Bool.and_eq_true] at hs
    rcases Out.calls_seq h with h | h
    · exact walk1_callOf s hs.1 c h
    · exact walk_callOf ss hs.2 c h

theorem walkArms_callOf (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ), callsArms p arms = true →
    ∀ c ∈ calls (walkArms σ x j arms).evs, ∃ st, p st = true ∧ CallOf σ c st
  | [], _, _, c, h => by simp [walkArms, Out.evs, calls] at h
  | a :: as, j, hs, c, h => by
    unfold walkArms at h
    replace hs : (callsAll p a && callsArms p as) = true := hs
    simp only [Bool.and_eq_true] at hs
    split_ifs at h
    · exact walk_callOf a hs.1 c h
    · exact walkArms_callOf x as (j + 1) hs.2 c h
end

end

/-! ## The listed callees -/

theorem calFind_spec {cs : List ℕ} {f : String} {m : ℕ} {lp ep : Bool}
    (h : calFind (calTbl cs) f = some (m, lp, ep)) :
    ∃ c ∈ cs, (coreOf c).name = f ∧ m = B2C.fsN c ∧ lp = (coreOf c).loop ∧
      ep = ((coreOf c).loop && (loopTail (coreOf c) none).isSome) := by
  unfold calFind at h
  obtain ⟨x, hx, hxe⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hmem, hp⟩ := List.mem_of_find?_eq_some hx, List.find?_some hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hmem
  simp only [beq_iff_eq] at hp
  simp only [Prod.mk.injEq] at hxe
  obtain ⟨rfl, rfl, rfl⟩ := hxe
  exact ⟨c, hc, hp, rfl, rfl, rfl⟩

/-- A listed callee's frame size and loop flag, by its name. -/
theorem cal_facts {c : ℕ} (h1 : 1 ≤ c) (h2 : c < nFns) :
    B2C.fs (coreOf c).name = B2C.fsN c ∧ coreProgram.find? (coreOf c).name = some (coreOf c) ∧
      coreProgram.loop (coreOf c).name = (coreOf c).loop := by
  obtain ⟨i, rfl, hi, hn, hfind, hcore, hfs, -⟩ := B2C.fn_of_idx (B2C.idxOf_coreOf h1 h2)
  have hf' : coreProgram.find? (coreOf (i + 1)).name = some (coreOf (i + 1)) := by rw [hfind, hcore]
  exact ⟨hfs, hf', Program.loop_of_find? hf'⟩

/-! ## A loop's block -/

section

variable {rd : Reader} {fs : String → ℕ} {P : Core.Program}

theorem blockLast_snoc {lp : String → Bool} : ∀ (ks : List Tree) (k : Tree),
    Tree.blockLast fs lp (ks ++ [k]) = k.block fs lp
  | [], k => by simp only [List.nil_append, Tree.blockLast]
  | [k'], k => by simp only [List.cons_append, List.nil_append, Tree.blockLast]
  | k1 :: k2 :: ks, k => by
    rw [List.cons_append, List.cons_append, Tree.blockLast]
    exact blockLast_snoc (k2 :: ks) k

/-- **A loop's run reaches its end, its block a frame per iteration and one more**: `chain`, with the
block. -/
theorem chainB (hfs : ∀ f, 1 ≤ fs f) : ∀ (n : ℕ) {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    {args rets : List E} {fn : Fn} {e : Option ℕ}, (Memory.Tree.node f σ bufs kids).total fs ≤ n →
    (Memory.Tree.node f σ bufs kids).Valid P rd args rets → P.find? f = some fn →
    loopShape fn e = some (loopBody fn) → P.loop f = true →
    ∃ m p0 prest, fn.params = p0 :: prest ∧ 1 ≤ m ∧ m ≤ (Memory.Tree.node f σ bufs kids).total fs ∧
      σ p0 * ofK (addressOfIndex m) = Res.endVal σ fn e ∧
      (Memory.Tree.node f σ bufs kids).block fs P.loop = (m + 1) * fs f
  | 0, f, σ, bufs, kids, _, _, _, _, htot, _, _, _, _ => by
    have := le_total (fs := fs) (Memory.Tree.node f σ bufs kids)
    have := hfs f
    simp only [Tree.name] at *
    omega
  | n + 1, f, σ, bufs, kids, args, rets, fn, e, htot, hv, hf, hs, hlp => by
    unfold Tree.Valid at hv
    obtain ⟨fn', hf', -, es, vs, hw, -, hh, hk⟩ := hv
    have hfe := Option.some.inj (hf'.symm.trans hf)
    subst fn'
    obtain ⟨p0, prest, c, i', es1, hps, -, hes, hi, hc⟩ := Res.loop_path hs hw hh
    subst hes
    rw [Res.loop_calls] at hk
    have hname : fn.name = f := fn_name_of_find hf
    have htk : fs f + Tree.totalKids fs kids + bufs.sum = (Memory.Tree.node f σ bufs kids).total fs :=
      (total_node f σ bufs kids).symm
    have h1 := hfs f
    have hblk : (Memory.Tree.node f σ bufs kids).block fs P.loop = fs f + Tree.blockLast fs P.loop kids := by
      simp only [Tree.block, hlp, ↓reduceIte]
    obtain ⟨ks', k, rfl, -, hkn, hkv⟩ := Res.kidsValid_snoc hk
    rw [hblk, blockLast_snoc]
    by_cases h0 : σ c = 0
    · simp only [ne_eq, h0, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hkv hkn
      obtain ⟨⟨f', σ', rfl⟩, -⟩ := hkv
      simp only [Tree.name, hname] at hkn
      subst hkn
      refine ⟨1, p0, prest, hps, le_rfl, by omega, ?_, by simp [Tree.block]; ring⟩
      rw [h0] at hc
      exact Res.char2_eq hc.symm
    · simp only [ne_eq, h0, not_false_eq_true, decide_true, ↓reduceIte] at hkv hkn
      rcases k with ⟨f', σ', bufs', kids'⟩ | ⟨f', σ'⟩
      · simp only [Tree.name, hname] at hkn
        subst f'
        have hkt := Res.totalKids_snoc (fs := fs) ks' (Memory.Tree.node f σ' bufs' kids')
        have hkv' := hkv
        unfold Tree.Valid at hkv'
        obtain ⟨fn'', hf'', hpm, -⟩ := hkv'
        have hfe' := Option.some.inj (hf''.symm.trans hf)
        subst fn''
        obtain ⟨m, p0', prest', hps', hm1, hm2, hm, hb⟩ := chainB hfs n (by omega) hkv hf hs hlp
        rw [hps] at hps'
        obtain ⟨rfl, rfl⟩ := List.cons.inj hps'
        rw [hps] at hpm
        simp only [List.map_cons, List.cons.injEq] at hpm
        obtain ⟨h0', hrest⟩ := hpm
        have hend : Res.endVal σ' fn e = Res.endVal σ fn e := by
          cases e with
          | some _ => rfl
          | none =>
            simp only [Res.endVal, hps]
            cases prest with
            | nil => rfl
            | cons p1 _ => simp only [List.map_cons, List.cons.injEq] at hrest; exact hrest.1
        refine ⟨m + 1, p0, prest, hps, by omega, by omega, ?_, by rw [hb]; ring⟩
        rw [← hend, ← hm, h0', hi, mul_assoc, Res.ofK_gpow_add, Nat.add_comm 1 m]
      · exact hkv.elim

end

/-! ## The callee frames' sizes -/

/-- **A parameter or a value an event of the path uses is at its cell**, as `cellRef`. -/
theorem cellRefP {r : Ref} (hr : r.Ok) {pc fp : ℕ} {done : List Pop} {e : Ent} {st : List Ent}
    (hT : RefTrack alignA r pc fp (done, e :: st)) {j : ℕ} (hj : B2C.idxOf e.I.t.name = some j) {v : V}
    (hv : (v ∈ (coreOf j).params ∧ (ctxOf j).extra.lookup v.idx = none) ∨ ∃ ev ∈ e.pre ++ e.es, v ∈ ev.uses)
    (hcell : allocCellOk (ctxOf j) (B2C.fsN j) v = true) :
    e.I.fp + (ctxOf j).locAt v.idx < maxCells ∧ refMem r.img (e.I.fp + (ctxOf j).locAt v.idx) = e.σ v := by
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  obtain ⟨hI, j', bufs, kids, vs, hj', hIt, hfn, hw, hFH⟩ :=
    (hT.frames hr.name hHon hHX.covers) e List.mem_cons_self
  obtain rfl : j = j' := Option.some.inj (hj.symm.trans hj')
  have hE := hT.track.ents e List.mem_cons_self
  have hevs : e.I.t.events coreProgram = e.pre ++ e.es := by rw [hIt]; exact events_node hE.find hw
  have hA2 : alignA e.I.t.name = fnAl j := alignA_of hj
  have hnamed : v ∈ B2C.namedOf (coreOf j).params (e.pre ++ e.es) vs := by
    rcases hv with ⟨hp, -⟩ | ⟨ev, hat, hdu⟩
    · exact List.mem_append_left _ (List.mem_append_left _ hp)
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hat, hdu⟩))
  rcases hx : (ctxOf j).extra.lookup v.idx with _ | c
  · simp only [allocCellOk, hx, Option.isSome_none, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hcell
    obtain ⟨-, hlocC⟩ := pairOk_alignA _ _ j hE.find hj
    have hx' : (alignA e.I.t.name).X.extra.lookup v.idx = none := by rw [hA2]; exact hx
    have hlc : (ctxOf j).locAt v.idx = (certOf j).locs.getD v.idx 0 := by
      have := hlocC v.idx hx' hcell.1.1
      rwa [hA2] at this
    have hcj : B2C.cellJ j v = (ctxOf j).locAt v.idx := hlc.symm
    rw [← hcj] at hcell ⊢
    have hrd := hFH.val v hnamed hcell.1.2 hcell.2
    obtain ⟨i, -, -, -, -, -, hfs, -⟩ := B2C.fn_of_idx hj
    have hwithin : e.I.fp + B2C.fs e.I.t.name ≤ r.T.total B2C.fs :=
      honest_within hI (by have := hHon.cells.two_le e.I hI; omega)
    have h28 : r.T.total B2C.fs ≤ 2 ^ r.κ := le_two_pow_logMem _
    have h2k : 2 ^ r.κ ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) hκ
    exact refRd_img hκ r.img _ _ (by rw [hfs] at hwithin; omega) hrd
  · rcases hv with ⟨-, hn⟩ | ⟨ev, hat, hdu⟩
    · rw [hx] at hn; cases hn
    have hx' : (alignA e.I.t.name).X.extra.lookup v.idx = some c := by rw [hA2]; exact hx
    obtain ⟨hlt, hrd⟩ := hr.extra e.I hI _ _ bufs kids hIt v (by rw [hevs]; exact List.mem_flatMap.mpr ⟨_, hat, hdu⟩) c hx'
    have hlc : (ctxOf j).locAt v.idx = c := by
      unfold Bridge.AlignCtx.locAt; rw [hx]; rfl
    rw [hlc]
    exact refRd_img hκ r.img (e.I.fp + c) _ (by omega) hrd

/-- A call's arguments are its event's uses. -/
theorem uses_of_call {es : List Ev} {c : Call} (hc : c ∈ calls es) {v : V} (hv : v ∈ c.args) :
    ∃ ev ∈ es, v ∈ ev.uses := by
  obtain ⟨ev, hev, he⟩ := List.mem_filterMap.mp hc
  refine ⟨ev, hev, ?_⟩
  cases ev <;> simp only [Ev.call?, reduceCtorEq, Option.some.injEq] at he <;> subst he <;>
    simp [Ev.uses, hv]

/-! ## The check's facts -/

theorem spConst_spec {sp : List Atom} {v : V} {e : ℕ} (h : spConst sp v e = true) :
    ∃ w, Atom.const v w ∈ sp ∧ w = ofK (addressOfIndex e) := by
  unfold spConst at h
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  cases a with
  | const x w =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨rfl, hw⟩ := hp
    exact ⟨w, ha, (constOk_spec hw).1⟩
  | _ => simp at hp

theorem spWord_spec {sp : List Atom} {v : V} {w : E} (h : spWord sp v = some w) : Atom.const v w ∈ sp := by
  unfold spWord at h
  obtain ⟨a, ha, hp⟩ := List.exists_of_findSome?_eq_some h
  cases a with
  | const x w' =>
    simp only at hp
    split_ifs at hp with hx
    · simp only [beq_iff_eq] at hx
      obtain rfl := hx
      obtain rfl := Option.some.inj hp
      exact ha
  | _ => simp at hp

/-- The spine's atoms hold on a frame's path. -/
theorem spine_holds {r : Ref} (hr : r.Ok) {pc fp : ℕ} {done : List Pop} {e : Ent} {st : List Ent}
    (htr : RefTrack alignA r pc fp (done, e :: st)) {j : ℕ} {vs : List V}
    (hw : walk e.σ (coreOf j).body = .ret (e.pre ++ e.es) vs) :
    ∃ rd, ∀ a ∈ spine (coreOf j).body, a.Holds rd e.σ := by
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  have hE := htr.track.ents e List.mem_cons_self
  obtain ⟨f, bufs, kids, ht⟩ := hE.node
  rcases insts_good r.T _ r.hdr hHon.valid e.I hE.mem with ⟨args, rets, hv⟩ | ⟨f', σ', hph⟩
  · rw [ht] at hv
    obtain ⟨fn, hf, -, es, vs', hw', -, hh, -⟩ := hv
    refine ⟨rd, fun a ha ↦ ?_⟩
    have hf' : fn = e.fn := by
      have := hE.find
      rw [ht] at this
      exact Option.some.inj (hf.symm.trans this)
    obtain ⟨vs0, hw0, -⟩ := hE.path
    rw [hf', hw0] at hw'
    obtain ⟨rfl, -⟩ := Out.ret.inj hw'
    have hmem := spine_on_path _ hw a ha
    exact hh _ hmem
  · rw [ht] at hph; cases hph

theorem armsFit_spec {tbl : List (String × ℕ × Bool × Bool)} {sizes : List ℕ} :
    ∀ (fs : List String) (j0 : ℕ), armsFit tbl sizes fs j0 = true → ∀ {i : ℕ} {f : String}, fs[i]? = some f →
      ∃ m ep, calFind tbl f = some (m, false, ep) ∧ sizes[j0 + i]? = some m
  | [], _, _, i, f, hi => by simp at hi
  | f0 :: fs, j0, h, i, f, hi => by
    simp only [armsFit, Bool.and_eq_true] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      split at h
      · rename_i m lp ep hc
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
        obtain ⟨⟨h1, rfl⟩, -⟩ := h
        exact ⟨m, ep, hc, by simpa using h1⟩
      · simp at h
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨m, ep, hc, hs⟩ := armsFit_spec fs (j0 + 1) h.2 hi
      exact ⟨m, ep, hc, by rw [← hs]; congr 1; omega⟩

theorem guardOk_spec {sp : List Atom} {b a1 : V} {e : ℕ} (h : guardOk sp b a1 e = true) :
    ∃ x y, Atom.add b x y ∈ sp ∧ ((spConst sp x e = true ∧ y = a1) ∨ (spConst sp y e = true ∧ x = a1) ∨
      ∃ w1 w2, spWord sp x = some w1 ∧ spWord sp y = some w2 ∧ w1 ≠ w2) := by
  unfold guardOk at h
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  cases a with
  | add d x y =>
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hp
    obtain ⟨rfl, hp⟩ := hp
    refine ⟨x, y, ha, ?_⟩
    rcases hp with (⟨h1, h2⟩ | ⟨h1, h2⟩) | h3
    · exact .inl ⟨h1, h2⟩
    · exact .inr (.inl ⟨h1, h2⟩)
    · refine .inr (.inr ?_)
      split at h3
      · rename_i w1 w2 hw1 hw2
        exact ⟨w1, w2, hw1, hw2, by simpa using h3⟩
      · cases h3
  | _ => simp at hp


/-- **The frame hints the sizes check skips** reserve the next callee's block. -/
def FrSkip : Prop :=
  ∀ r C e s sx i h j, HintAt alignA r C e s sx i h → isFrame (alignA e.I.t.name).X h = true →
    B2C.idxOf e.I.t.name = some j → (s.pc - entOf alignA e.I.t.name) ∈ AllocChk.frSkipAt j →
    SizeOk (refMem r.img) sx.fp h
      ((((e.I.t.kidsC coreProgram.loop)[e.nc]?).map (Tree.block B2C.fs coreProgram.loop)).getD 0)

/-- **A callee frame's hint reserves the next callee's block**, but those the check skips. -/
theorem frameSize_alignA (hS : FrSkip) : FrameSize alignA := by
  intro r C e s sx i h hat hfr
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (isFrame_ptr hfr)
  obtain ⟨off, c, s0, hpcE, hqm, hc, hsite, hkC⟩ := frame_next hat hfr hp
  have hat' := hat
  obtain ⟨hr, hC, ⟨done, st, htr, hch, -⟩, -, hfine, -, hget, hpre, hag⟩ := hat
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  obtain ⟨hI, j, bufs, kids, vs, hj, hIt, hfn, hw, hFH⟩ := (htr.frames hr.name hHon hHX.covers) e List.mem_cons_self
  have hE := htr.track.ents e List.mem_cons_self
  have hoff : s.pc - entOf alignA e.I.t.name = off := by omega
  by_cases hsk : off ∈ AllocChk.frSkipAt j
  · exact hS r C e s sx i h j hat' hfr hj (by rw [hoff]; exact hsk)
  have hfpe : e.I.fp = s.fp := htr.linked.top.1
  have hfol := hints_follows _ s sx ⟨hfine.agree.wf, hfine.dl⟩ hpre
  have hsxfp : sx.fp = e.I.fp := hfol.fp.trans hfpe.symm
  rw [hsxfp]
  obtain ⟨i0, rfl, -, -, hfind, hcore, hfs, -, h1, h2⟩ := B2C.fn_of_idx hj
  have hA : alignA e.I.t.name = fnAl (i0 + 1) := alignA_of hj
  rw [hA] at hqm hsite
  obtain ⟨cs, hchk⟩ := AllocChk.frJ_all _ h1 (by have : nFns = 1602 := rfl; omega)
  have hne : (frames (ctxOf (i0 + 1)) (adviceOf (i0 + 1))).isEmpty = false := by
    cases hf : frames (ctxOf (i0 + 1)) (adviceOf (i0 + 1)) with
    | nil => change (off, h) ∈ frames (ctxOf (i0 + 1)) (adviceOf (i0 + 1)) at hqm; rw [hf] at hqm; cases hqm
    | cons _ _ => rfl
  simp only [frChk, hne, Bool.false_or, Bool.and_eq_true, List.all_eq_true] at hchk
  obtain ⟨hcs, hcalls⟩ := hchk
  have hwc : walk e.σ (coreOf (i0 + 1)).body = .ret (e.pre ++ e.es) vs := by rw [hfn]; exact hw
  obtain ⟨stm, hP, hco⟩ := walk_callOf _ hcalls c (by rw [hwc]; exact List.mem_of_getElem? hc)
  have hq := List.all_eq_true.mp hP (off, h) hqm
  have hsk' : (AllocChk.frSkipAt (i0 + 1)).contains (off, h).1 = false := by simpa using hsk
  simp only [hsk', Bool.false_or, hp] at hq
  obtain ⟨hargs, hrets⟩ := callOf_args hco
  rw [hargs, hrets] at hq
  change (ctxOf (i0 + 1)).siteAt p c.args c.rets = some s0 at hsite
  rw [hsite, Option.isNone_some, Bool.false_or] at hq
  -- the callee
  have hlt : e.nc < e.I.t.kids.length := lt_of_lt_of_le hkC (kidsC_length_le _)
  have hkC' : (e.I.t.kidsC coreProgram.loop)[e.nc]? = some e.I.t.kids[e.nc] := by
    rw [List.getElem?_eq_getElem hkC, kidsC_getElem hkC]
  rw [hkC', Option.map_some, Option.getD_some]
  obtain ⟨rv, hkv⟩ := hE.kids
  obtain ⟨hkn, hkt, hkp⟩ := Res.kidsValid_at hkv hc (List.getElem?_eq_getElem hlt)
  have hcs' := fun c' hc' ↦ hcs c' hc'
  -- the facts of a listed callee
  have cal : ∀ {f m lp ep}, calFind (calTbl cs) f = some (m, lp, ep) → ∃ c', (coreOf c').name = f ∧
      B2C.fs f = m ∧ coreProgram.find? f = some (coreOf c') ∧ coreProgram.loop f = lp ∧
      ep = ((coreOf c').loop && (loopTail (coreOf c') none).isSome) := fun h0 ↦ by
    obtain ⟨c', hc', hn, hm, hl, he⟩ := calFind_spec h0
    have hb := hcs' c' hc'
    simp only [Nat.ble_eq, Nat.blt_eq] at hb
    obtain ⟨hf1, hf2, hf3⟩ := cal_facts hb.1 hb.2
    rw [hn] at hf1 hf2 hf3
    exact ⟨c', hn, by rw [hf1, hm], hf2, by rw [hf3, hl], he⟩
  -- a node's block, no loop helper
  have blk : ∀ {f m}, coreProgram.loop f = false → B2C.fs f = m → e.I.t.kids[e.nc].name = f →
      e.I.t.kids[e.nc].block B2C.fs coreProgram.loop = m := fun hl hm hn ↦ by
    rcases hk : e.I.t.kids[e.nc] with ⟨f', σ', bufs', kids'⟩ | ⟨f', σ'⟩
    · rw [hk] at hn; simp only [Tree.name] at hn; subst hn
      simp [Tree.block, hl, hm]
    · rw [hk] at hn; simp only [Tree.name] at hn; subst hn
      simp [Tree.block, hm]
  cases h <;> cases stm <;> simp only [frFits, Bool.false_eq_true] at hq
  case alloc.call q m f args rets =>
    simp only [CallOf] at hco
    subst hco
    split at hq
    · rename_i k' lp ep hcf
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hq
      obtain ⟨rfl, rfl⟩ := hq
      obtain ⟨c', -, hfsf, -, hlp, -⟩ := cal hcf
      exact (blk hlp hfsf hkn).symm
    · cases hq
  case allocFrames.callIf q size stop si tail b f args =>
    obtain ⟨hcf, hca, hcr, htk⟩ := hco
    rcases args with _ | ⟨a0, _ | ⟨a1, rest⟩⟩
    · simp at hq
    · simp at hq
    dsimp only at hq
    split at hq
    · rename_i k' lp ep hcal
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hq
      obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hcell⟩, hstart⟩ := hq
      obtain ⟨c', -, hfsf, hfindf, hlpf, hepf⟩ := cal hcal
      have hep' : (loopTail (coreOf c') none).isSome = true := by
        have := hepf.symm; simp only [Bool.and_eq_true] at this; exact this.2
      obtain ⟨e0, hsc, hsi, hg⟩ : ∃ e0, spConst (spine (coreOf (i0 + 1)).body) a0 e0 = true ∧
          addressOfIndex e0 * si = 1 ∧ guardOk (spine (coreOf (i0 + 1)).body) b a1 e0 = true := by
        rcases hstart with ⟨⟨h1, rfl⟩, h3⟩ | ⟨⟨h1, rfl⟩, h3⟩
        · refine ⟨0, h1, ?_, h3⟩
          decide +kernel
        · refine ⟨1, h1, ?_, h3⟩
          decide +kernel
      obtain ⟨rd', hsp⟩ := spine_holds hr htr hwc
      obtain ⟨w0, hw0, rfl⟩ := spConst_spec hsc
      have hσa0 : e.σ a0 = ofK (addressOfIndex e0) := hsp _ hw0
      -- the end at the stop cell
      have hcm : c ∈ calls (e.pre ++ e.es) := List.mem_of_getElem? hc
      have ha1 := cellRefP hr htr hj (v := a1) (.inr (uses_of_call hcm (by rw [hca]; simp))) hcell
      simp only [SizeOk]
      rw [ha1.2]
      have hsi' : ∀ m, addressOfIndex (e0 + m) * si = addressOfIndex m := fun m ↦ by
        rw [Parameters.addressOfIndex, Parameters.addressOfIndex, pow_add, mul_comm (Parameters.g ^ e0), mul_assoc,
          ← Parameters.addressOfIndex, hsi, mul_one]
      by_cases ht : c.taken = true
      · -- entered: the run's iterations
        have hb0 := htk.mp ht
        have hkv' := hkt ht
        rcases hk : e.I.t.kids[e.nc] with ⟨f', σk, bk, kk⟩ | ⟨f', σk⟩
        · rw [hk] at hkv' hkn
          simp only [Tree.name] at hkn
          rw [hcf] at hkn
          subst hkn
          obtain ⟨-, e', hend, hshape, -⟩ := progOk_guest.loop _ _ hfindf (by rw [← Program.loop_of_find? hfindf]; exact hlpf)
          have he' : e' = none := by
            unfold Res.endOfFn at hend
            simp only [hep', ↓reduceIte] at hend
            exact (Option.some.inj hend).symm
          subst he'
          obtain ⟨m, p0, prest, hps, hm1, hmt, hend', hblk⟩ :=
            chainB (fs := B2C.fs) (fun f ↦ by have := B2C.two_le_fs f; omega) _ le_rfl hkv' hfindf hshape hlpf
          have hkv2 := hkv'
          unfold Tree.Valid at hkv2
          obtain ⟨fn2, hf2, hpm, -⟩ := hkv2
          obtain rfl : fn2 = coreOf c' := Option.some.inj (hf2.symm.trans hfindf)
          rw [hps, hca] at hpm
          rcases prest with _ | ⟨p1, prest'⟩
          · simp at hpm
          simp only [List.map_cons, List.cons.injEq] at hpm
          obtain ⟨hp0, hp1, -⟩ := hpm
          simp only [Res.endVal, hps] at hend'
          rw [hp0, hp1, hσa0, Res.ofK_gpow_add] at hend'
          -- the bound on the iterations
          have hn : ∃ f σ bufs kids, e.I.t = .node f σ bufs kids := ⟨_, _, _, _, hIt⟩
          have hcu := curAt_le_endCur (fs := B2C.fs) (lp := coreProgram.loop) hn e.I.t.bufs.length (e.nc + 1)
          unfold Inst.curAt at hcu
          rw [ksum_succ hkC, kidsC_getElem hkC, hk] at hcu
          have he2 := endCur_chain (A := alignA) hr st e s.pc s.fp htr.track.ents htr.linked hch
          have hIP := insts_placed r.T (0, r.T.block B2C.fs coreProgram.loop) r.hdr (by omega) e.I hI
          have hbl : B2C.fs e.I.t.name ≤ e.I.t.block B2C.fs coreProgram.loop := by
            generalize e.I.t = t; cases t <;> simp [Tree.block, Tree.name]
          have hfs2 := B2C.two_le_fs e.I.t.name
          have h28 := le_two_pow_logMem (r.T.total B2C.fs)
          have h2k : 2 ^ r.κ ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) hκ
          refine ⟨addressOfIndex (e0 + m), m, by rw [← hend'], hsi' m, ?_, ?_⟩
          · have := hIP.2.2
            unfold maxCells; unfold Ref.κ at h2k; omega
          · rw [hblk, hfsf]; ring
        · rw [hk] at hkv'; exact hkv'.elim
      · -- not entered: the guard zero, the end the start
        have hb0 : e.σ b = 0 := by
          by_contra h0; exact ht (htk.mpr h0)
        obtain ⟨f', σk, hph⟩ := hkp (by simpa using ht)
        have hbk : e.I.t.kids[e.nc].block B2C.fs coreProgram.loop = B2C.fs f := by
          rw [hph] at hkn ⊢; simp only [Tree.name] at hkn; rw [hcf] at hkn; subst hkn; simp [Tree.block]
        rw [hbk]
        obtain ⟨x, y, hxy, hcase⟩ := guardOk_spec hg
        have hadd : e.σ b = e.σ x + e.σ y := hsp _ hxy
        rw [hb0] at hadd
        have hend : e.σ a1 = ofK (addressOfIndex e0) := by
          rcases hcase with ⟨hx, rfl⟩ | ⟨hy, rfl⟩ | ⟨w1, w2, h1, h2, hne⟩
          · obtain ⟨w, hw, rfl⟩ := spConst_spec hx
            rw [← Res.char2_eq hadd.symm]; exact hsp _ hw
          · obtain ⟨w, hw, rfl⟩ := spConst_spec hy
            rw [Res.char2_eq hadd.symm]; exact hsp _ hw
          · exact absurd ((hsp _ (spWord_spec h1)).symm.trans ((Res.char2_eq hadd.symm).trans (hsp _ (spWord_spec h2))))
              hne
        refine ⟨addressOfIndex e0, 0, by rw [hend], by simpa using hsi' 0, by unfold maxCells; norm_num, ?_⟩
        rw [hfsf]; ring
    · cases hq
  case allocArm.dispatch q sel sizes x fs args rets =>
    obtain ⟨hca, hcr, htk, jj, hjj, hσx⟩ := hco
    simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, Bool.or_eq_true, List.contains_iff_mem,
      List.any_eq_true] at hq
    obtain ⟨⟨⟨⟨rfl, hcell⟩, huse⟩, hsz⟩, harms⟩ := hq
    obtain ⟨m, ep, hcf, hsm⟩ := armsFit_spec fs 0 harms hjj
    obtain ⟨c', -, hfsf, -, hlp, -⟩ := cal hcf
    rw [Nat.zero_add] at hsm
    have hjl : jj < sizes.length := (List.getElem?_eq_some_iff.mp hsm).1
    refine ⟨jj, ?_, by unfold maxCells; omega, by rw [hsm, blk hlp hfsf hkn]⟩
    have hx := cellRefP hr htr hj (v := x) (by
      rcases huse with ⟨hpx, hxn⟩ | ⟨a, ha, hu⟩
      · exact .inl ⟨hpx, by simpa using hxn⟩
      · exact .inr ⟨.atom a, spine_on_path _ hwc a ha, hu⟩) hcell
    rw [hx.2, hσx]

end

end LeanVM.Guest.EndExec
