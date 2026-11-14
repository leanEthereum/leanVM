/-
  LeanVM.Guest.EndExecYStep

  The tree track's step rule with the entries it pops: the entries done after a step are those
  before and those of the atoms the offset's hints consume.
-/

module

public import LeanVM.Guest.Bridge.StepRule

/-!
# The step rule with its entries

`stepD_of` is `Bridge.stepRule_of` for one state, saying also which entries the step pops: every
move past the atoms the offset's hints consume (`atPc_step`) is followed only by moves that pop
nothing, so the new state's entries done are the old ones and those atoms'. The hint track's cursor
(`EndExecY`) reads it.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Check (getF)

public section

variable {P : Core.Program} {rd : Reader} {Is : List Inst}
variable {prog : LeanIsaProgram} {κ : ℕ} {img : MemoryImage κ} {A : String → FnAl} {T : Tree}

/-- The track moved inside the top frame, at a new pc of the frame, its entries done kept. -/
theorem withinD {pc fp pc' : ℕ} {done done' : List Pop} {e e' : Ent} {st : List Ent}
    (h : RefOk P rd Is T (memOf img) (entOf A) (alOf A) pc fp (done, e :: st))
    (hm : Relation.ReflTransGen (Move P rd Is) (done, e :: st) (done', e' :: st)) (hI : e'.I = e.I)
    (ha : AtPc (entOf A) (alOf A) e' pc') :
    ∃ pc'' fp'' s', regs pc' fp = regs pc'' fp'' ∧ Relation.ReflTransGen (Move P rd Is) (done, e :: st) s' ∧
      RefOk P rd Is T (memOf img) (entOf A) (alOf A) pc'' fp'' s' ∧ s'.1 = done' :=
  ⟨pc', fp, _, rfl, hm, h.within hm hI ha, rfl⟩

/-- **The step rule with the entries it pops**: from a state of the track at `(pc, fp)`, its top
frame's jumps' cells read, a step to registers short of the final ones lands at registers of a
state of the track, reached by moves, whose entries done are the old ones and those of the atoms
the offset's hints consume, the flow ones compiling the flow hints at `pc` one for one. -/
theorem stepD_of (hP : ProgAl prog P A)
    (hIs : ∀ I ∈ Is, ∀ (i : ℕ) (k : Tree), I.t.kids[i]? = some k → ∃ J ∈ Is, J.t = k ∧ I.kidFps[i]? = some J.fp)
    {pc fp : ℕ} {done : List Pop} {e : Ent} {st : List Ent} {r' : Registers K}
    (h : RefOk P rd Is T (memOf img) (entOf A) (alOf A) pc fp (done, e :: st)) (hc : JumpCells img A e pc)
    (hstep : step prog img (regs pc fp) = some r') (hne' : r' ≠ Registers.final prog) :
    ∃ as : List Atom, List.Forall₂ (Pairs (A e.I.t.name).X) (as.filter flowAtom)
        ((((A e.I.t.name).d.2.2.lookup pc).getD []).filter isaFlowHint) ∧
      ∃ pc' fp' s', r' = regs pc' fp' ∧ Relation.ReflTransGen (Move P rd Is) (done, e :: st) s' ∧
        RefOk P rd Is T (memOf img) (entOf A) (alOf A) pc' fp' s' ∧
        s'.1 = done ++ as.flatMap (fun a ↦ a.pops rd e.σ) := by
  obtain ⟨e0, st0, hst, hE, hfp, hat⟩ := h.top
  obtain ⟨rfl, rfl⟩ := List.cons.inj hst
  subst hfp
  have hok := hP.ok _ _ hE.find
  obtain ⟨off, ins, z, tabs, r, as, hpc, hins, hz, ⟨bs, hbs⟩, hpair, hr, e', hm, hI, hfn, hp, -, hnext, h1, h2, h3⟩ :=
    atPc_step (P := P) (rd := rd) (Is := Is) hok rfl (fun _ ↦ rfl) hat done st
  refine ⟨as, hpair, ?_⟩
  have hfetch := hP.fetch _ _ hE.find off ins hins
  rw [← hpc] at hfetch
  rw [step_of_fetch_eq_some hfetch] at hstep
  have hE' : EntOk P Is e' := (h.track.moves hm).ents e' List.mem_cons_self
  have hσ : e'.σ = e.σ := by simp only [Ent.σ, hI]
  have hpath : ∀ vs, walk e.σ e.fn.body = .ret (e.pre ++ e.es) vs → e'.pre ++ e'.es = e.pre ++ e.es := by
    intro vs hw
    obtain ⟨vs', hw', -⟩ := hE'.path
    rw [hσ, hfn, hw] at hw'
    exact (Out.ret.inj hw').1.symm
  obtain ⟨vs0, hw0, -⟩ := hE.path
  have hfull : e'.pre ++ e'.es = e.pre ++ e.es := hpath vs0 hw0
  have hent : entOf A e'.I.t.name = (A e.I.t.name).X.entry := by rw [hI]; rfl
  have hal : ∀ o, alOf A e'.I.t.name o = alignAt (A e.I.t.name).X (A e.I.t.name).body (A e.I.t.name).code
      (A e.I.t.name).d o := fun o ↦ by rw [hI]; rfl
  by_cases hj : ∃ oc od of, ins = .jump oc od of
  swap
  · have hnj : ∀ oc od of, ins ≠ .jump oc od of := fun oc od of h ↦ hj ⟨oc, od, of, h⟩
    have hjf : ins.isJump = false := by
      cases ins <;> first | rfl | exact absurd rfl (hnj _ _ _)
    have hr' := ((execute_iff_holds hjf).mp hstep).2
    rw [hr']
    exact withinD h hm hI (hnext hnj)
  obtain ⟨oc, od, of, rfl⟩ := hj
  obtain ⟨cv, dv, fv, hcv, hdv, hfv, -, -, -, rfl⟩ := execute_jump_iff.mp hstep
  rw [read_cell] at hcv hdv hfv
  set X := (A e.I.t.name).X with hX
  set D := done ++ as.flatMap (fun a ↦ a.pops rd e.σ) with hD
  have fin : ∀ e'' pc', Move P rd Is (D, e' :: st) (D, e'' :: st) → e''.I = e'.I → AtPc (entOf A) (alOf A) e'' pc' →
      ∃ pc'' fp'' s', regs pc' e.I.fp = regs pc'' fp'' ∧ Relation.ReflTransGen (Move P rd Is) (done, e :: st) s' ∧
        RefOk P rd Is T (memOf img) (entOf A) (alOf A) pc'' fp'' s' ∧ s'.1 = D :=
    fun e'' pc' hm' hI' ha' ↦ withinD h (hm.trans (.single hm')) (hI'.trans hI) ha'
  have hinK : ∀ c, Ev.inK c ∈ e'.es → cellAt img e.I.fp (X.locAt c.idx) = some (e.σ c) := fun c hmem ↦
    hc.cond c _ vs0 hw0 (hfull ▸ List.mem_append_right _ hmem)
  have hnz0 : X.nzAt oc = true → cv ≠ 0 := fun hnz ↦ by
    obtain ⟨w, hw, hw0⟩ := hc.nz oc hnz
    rw [hw] at hcv
    rwa [← Option.some.inj hcv]
  have hif : ∀ (a b : ℕ), cv ≠ 0 → dv = ofK (addressOfIndex a) → fv = ofK (addressOfIndex b) →
      (if cv = 0 then (⟨addressOfIndex (pc + 1), addressOfIndex e.I.fp⟩ : Registers K) else ⟨dv.limb 0, fv.limb 0⟩) =
        regs a b := fun a b h0 hd hf ↦ by
    rw [ite_eq_right h0, hd, hf, regs_ofK]
  have hsome : ∀ {o : ℕ} {w w' : E}, cellAt img e.I.fp o = some w → cellAt img e.I.fp o = some w' → w' = w :=
    fun h h' ↦ Option.some.inj (h'.symm.trans h)
  cases hz0 : X.zeroAt oc
  swap
  · have hr0 : r = (some z, []) := by simpa [insStep, jumpStep, hz0] using hr.symm
    obtain rfl := hsome (hc.zero oc hz0) hcv
    rw [ite_eq_left rfl]
    exact withinD h hm hI ⟨off + 1, by rw [hent]; omega, z.pos, by rw [hal]; exact h1 z (by rw [hr0]; rfl), [],
      by simp, by simp [hp]⟩
  cases hfw : fwdJ X off oc od of
  swap
  · obtain ⟨hnz, hself, t, o, ht, ho, rfl⟩ := fwd_step hr hz0 hfw
    obtain ⟨ho1, ho2⟩ := fwdOff_eq ho
    rw [hif t e.I.fp (hnz0 hnz) (hsome (hc.pcw od t ht) hdv) (hsome (hc.self of hself) hfv)]
    exact withinD h hm hI ⟨o, by rw [hent]; omega, z.pos, by rw [hal]; exact h2 (o, z) List.mem_cons_self, [],
      by simp, by simp [hp]⟩
  rcases hzc : z.cur with _ | ⟨s, ss⟩
  · simp [insStep, jumpStep, hz0, hfw, headStep, hzc] at hr
  obtain ⟨vs, hwp⟩ := hE'.walk_pos
  rw [hp, Zip.pos_head hzc] at hwp
  cases s with
  | atom a => simp [insStep, jumpStep, hz0, hfw, headStep, hzc] at hr
  | ite c zb nb =>
    obtain ⟨hloc, hself, t, cz, cn, o, ht, hcz, hcn, ho, rfl⟩ := ite_step hr hzc hz0 hfw
    obtain ⟨e'', hm'', hI'', -, -, ha''⟩ := atPc_ite (P := P) (rd := rd) (Is := Is) hent hal hp hzc hcz hcn
      (h1 _ rfl) (h2 _ List.mem_cons_self) D st
    rw [walk_ite_cons] at hwp
    obtain ⟨es', -, hes'⟩ := pre_eq_ret hwp
    have hcell := hinK c (by rw [hes']; exact List.mem_cons_self)
    rw [hloc] at hcell
    obtain rfl := hsome hcell hcv
    rw [hσ] at ha''
    by_cases h0 : e.σ c = 0
    · rw [ite_eq_left h0] at ha''
      rw [ite_eq_left h0]
      exact fin e'' _ hm'' hI'' (by rw [hpc]; exact ha'')
    · rw [ite_eq_right h0] at ha''
      obtain ⟨ho1, ho2⟩ := fwdOff_eq ho
      rw [hif t e.I.fp h0 (hsome (hc.pcw od t ht) hdv) (hsome (hc.self of hself) hfv)]
      exact fin e'' _ hm'' hI'' (by rw [show t = X.entry + o by omega]; exact ha'')
  | match_ x arms =>
    obtain ⟨a, ha⟩ : ∃ a, getF X.arms od = some a := by
      cases ha : getF X.arms od
      · simp [insStep, jumpStep, hz0, hfw, headStep, hzc, ha] at hr
      · exact ⟨_, rfl⟩
    obtain ⟨hnz, hself, hax, -⟩ := jump_match hr hzc hz0 hfw ha
    rw [walk_match_cons] at hwp
    obtain ⟨k, hk, hxk, hwa⟩ := walkArms_take arms 0 (seq_ne_stuck hwp)
    obtain ⟨t, ht, hlt, c', hc', hat'⟩ := h3 oc od of x arms ss a rfl hzc hz0 hfw ha k hk
    obtain ⟨e'', hm'', hI'', -, -, ha''⟩ := atPc_arm (P := P) (rd := rd) (Is := Is) hent hal hp hzc hk hwa hc' hat' D st
    have hcell := hc.arm off oc od of hpc hins bs x arms (z.next ss).pos (by rw [hbs, Zip.pos_head hzc]) a ha hax k t
      (by rw [← hσ, hxk, Nat.zero_add]) ht
    rw [hif t e.I.fp (hnz0 hnz) (hsome hcell hdv) (hsome (hc.self of hself) hfv)]
    exact fin e'' _ hm'' hI'' (by rw [show t = X.entry + (t - X.entry) by omega]; exact ha'')
  | call f args rets =>
    obtain ⟨hnz, s, t, c, o, hs, ht, hent', hc', ho, rfl⟩ := call_step hr hzc hz0 hfw
    rw [walk_call_cons] at hwp
    obtain ⟨es', -, hes'⟩ := pre_eq_ret hwp
    have hcalls : calls e'.es = ⟨f, args, rets, true⟩ :: calls es' := by rw [hes']; rfl
    obtain ⟨J, hJ, fn, hk, hkf, hfJ, hname⟩ := hE'.callee_named hIs hcalls rfl
    obtain ⟨kfp, hkfp, hq, hk0, hk1, -⟩ := hc.site _ vs0 hw0 e'.nc _ of s (by rw [← hfull]; exact calls_at hcalls)
      rfl hs
    rw [← hI, hkf] at hkfp
    obtain rfl := Option.some.inj hkfp
    obtain ⟨e'', hm'', hI'', -, -, ha''⟩ := atPc_call (P := P) (rd := rd) (Is := Is) hent hal hp hzc hc'
      (h2 _ List.mem_cons_self) hJ hk hkf hfJ D st
    obtain ⟨ho1, ho2⟩ := fwdOff_eq ho
    have htJ : entOf A J.t.name = t := by rw [hname]; exact hP.ent _ _ t f hE.find hent'
    rw [hif t J.fp (hnz0 hnz) (hsome (hc.pcw od t ht) hdv) (hsome hq hfv)]
    refine ⟨t, J.fp, _, rfl, hm.trans (.single hm''), ⟨h.track.moves (hm.trans (.single hm'')),
      Linked.push h.linked (hI''.trans hI) ha'' rfl (htJ ▸ atPc_enter hP hfJ) ?_ (memOf_of hk1)⟩, rfl⟩
    rw [memOf_of hk0]
    congr 2
    omega
  | callIf c f args =>
    obtain ⟨hloc, t, ca, ht, hent', hca, rfl, hcase⟩ := callIf_step hr hzc hz0 hfw
    rw [walk_callIf_cons] at hwp
    obtain ⟨es', hwes, hes'⟩ := pre_eq_ret hwp
    have hcell := hinK c (by rw [hes']; exact List.mem_cons_self)
    rw [hloc] at hcell
    obtain rfl := hsome hcell hcv
    by_cases h0 : e.σ c = 0
    · obtain ⟨e'', hm'', hI'', -, -, ha''⟩ := atPc_skip (P := P) (rd := rd) (Is := Is) hent hal hp hzc (hσ ▸ h0) hca
        (h1 _ rfl) D st
      rw [ite_eq_left h0]
      exact fin e'' _ hm'' hI'' (by rw [hpc]; exact ha'')
    have h0' : e'.σ c ≠ 0 := hσ ▸ h0
    rw [ite_eq_right h0'] at hes'
    have hcalls : calls e'.es = ⟨f, args, [], true⟩ :: calls es' := by rw [hes']; rfl
    obtain ⟨J, hJ, fn, hk, hkf, hfJ, hname⟩ := hE'.callee_named hIs hcalls rfl
    have htJ : entOf A J.t.name = t := by rw [hname]; exact hP.ent _ _ t f hE.find hent'
    rcases hcase with ⟨hnx, hrn⟩ | ⟨-, s, hs, hsr⟩
    · obtain ⟨as2, has2, hpos2, -⟩ := normZ_pos _ hca
      rw [retNil_eq hrn] at hpos2
      rw [hpos2, walk_atoms_ret] at hwes
      have hnil : calls es' = [] := by
        rw [← (Out.ret.inj hwes).1]
        clear * -
        induction as2 with
        | nil => rfl
        | cons a as ih => exact ih
      obtain ⟨hfp0, kfp, hkfp, hq, hk0, hk1⟩ := hc.tail off oc od of hpc hins hnx _ vs0 hw0 e'.nc _
        (by rw [← hfull]; exact calls_at hcalls) rfl
        (by rw [← hfull, calls_append', hcalls, hnil, Ent.nc, List.length_append]; rfl)
      rw [← hI, hkf] at hkfp
      obtain rfl := Option.some.inj hkfp
      have hmv : Move P rd Is (D, e' :: st) (D, Ent.enter P J fn :: st) :=
        .tail (hp.trans (Zip.pos_head hzc)) h0' ⟨as2, fun a ha ↦ flowAtom_pops (has2 a ha), hpos2⟩ hJ hk hkf hfJ
      rw [hif t J.fp h0 (hsome (hc.pcw od t ht) hdv) (hsome hq hfv)]
      rcases st with _ | ⟨e2, st2⟩
      · exact absurd h.linked.2.1 hfp0
      refine ⟨t, J.fp, _, rfl, hm.trans (.single hmv), ⟨h.track.moves (hm.trans (.single hmv)),
        Linked.tail h.linked rfl (htJ ▸ atPc_enter hP hfJ) ?_ ?_⟩, rfl⟩
      · exact congrArg (·.getD 0) hk0
      · exact congrArg (·.getD 0) hk1
    · obtain ⟨kfp, hkfp, hq, hk0, hk1, -⟩ := hc.site _ vs0 hw0 e'.nc _ of s
        (by rw [← hfull]; exact calls_at hcalls) rfl hs
      rw [← hI, hkf] at hkfp
      obtain rfl := Option.some.inj hkfp
      obtain ⟨e'', hm'', hI'', -, -, ha''⟩ := atPc_callIf (P := P) (rd := rd) (Is := Is) hent hal hp hzc h0' hca
        (h1 _ rfl) hJ hk hkf hfJ D st
      rw [hif t J.fp h0 (hsome (hc.pcw od t ht) hdv) (hsome hq hfv)]
      refine ⟨t, J.fp, _, rfl, hm.trans (.single hm''), ⟨h.track.moves (hm.trans (.single hm'')),
        Linked.push h.linked (hI''.trans hI) ha'' rfl (htJ ▸ atPc_enter hP hfJ) ?_ (memOf_of hk1)⟩, rfl⟩
      rw [memOf_of hk0, hsr]
      rfl
  | dispatch x fs args rets =>
    obtain ⟨hnz, hod, s, c, o, hs, hst, hc', ho, rfl⟩ := dispatch_step hr hzc hz0 hfw
    rw [walk_dispatch_cons] at hwp
    obtain ⟨i, hi, hpk⟩ := pick_take fs 0 (seq_ne_stuck hwp)
    rw [hpk, Out.seq] at hwp
    obtain ⟨es', -, hes'⟩ := pre_eq_ret hwp
    have hcalls : calls e'.es = ⟨fs[i], args, rets, true⟩ :: calls es' := by rw [hes']; rfl
    obtain ⟨J, hJ, fn, hk, hkf, hfJ, hname⟩ := hE'.callee_named hIs hcalls rfl
    obtain ⟨kfp, hkfp, hq, hk0, hk1, htg⟩ := hc.site _ vs0 hw0 e'.nc _ of s
      (by rw [← hfull]; exact calls_at hcalls) rfl hs
    rw [← hI, hkf] at hkfp
    obtain rfl := Option.some.inj hkfp
    obtain ⟨e'', hm'', hI'', ha''⟩ := atPc_dispatch (P := P) (rd := rd) (Is := Is) hent hal hp hzc hc'
      (h2 _ List.mem_cons_self) hi hpk hJ hk hkf hfJ D st
    obtain ⟨ho1, ho2⟩ := fwdOff_eq ho
    have hd := htg (by rw [hst]; exact hod)
    rw [hst] at hd
    rw [hif (entOf A J.t.name) J.fp (hnz0 hnz) (by rw [hname]; exact hsome hd hdv) (hsome hq hfv)]
    refine ⟨_, J.fp, _, rfl, hm.trans (.single hm''), ⟨h.track.moves (hm.trans (.single hm'')),
      Linked.push h.linked (hI''.trans hI) ha'' rfl (atPc_enter hP hfJ) ?_ (memOf_of hk1)⟩, rfl⟩
    rw [memOf_of hk0]
    congr 2
    omega
  | ret vs' =>
    obtain ⟨rfl, hnz, hm0⟩ := ret_step hr hzc hz0 hfw
    cases hmain : X.main
    · rw [hmain] at hm0
      simp only [Bool.false_eq_true, ↓reduceIte] at hm0
      obtain ⟨rfl, rfl⟩ := hm0
      rcases st with _ | ⟨e2, st2⟩
      · exact absurd (hc.bot h.linked.2.1) (by rw [hmain]; decide)
      obtain ⟨r0, hr0, hr1, hl⟩ := h.linked.pop
      have hmv : Move P rd Is (D, e' :: e2 :: st2) (D, e2 :: st2) := move_ret hp hzc D (e2 :: st2)
      rw [hif r0 e2.I.fp (hnz0 hnz) (by rw [← hr0]; exact (memOf_of hdv).symm)
        (by rw [← hr1]; exact (memOf_of hfv).symm)]
      exact ⟨r0, e2.I.fp, _, rfl, hm.trans (.single hmv), ⟨h.track.moves (hm.trans (.single hmv)), hl⟩, rfl⟩
    · rw [hmain] at hm0
      simp only [↓reduceIte] at hm0
      obtain ⟨hself, ht⟩ := hm0
      have hfp0 := hc.main hmain
      exfalso
      apply hne'
      rw [hif X.halt e.I.fp (hnz0 hnz) (hsome (hc.pcw od _ ht) hdv) (hsome (hc.self of hself) hfv), hfp0]
      exact hP.halt _ _ hE.find hmain

end

end LeanVM.Guest.Bridge
