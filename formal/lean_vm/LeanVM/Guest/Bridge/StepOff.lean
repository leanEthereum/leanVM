/-
  LeanVM.Guest.Bridge.StepOff

  The step rule at one state, with the offset the step was at and what its instruction did there.
-/

module

public import LeanVM.Guest.Bridge.StepRule

/-!
# What a step did at its offset

`StepOff P Is img A e off st pc' fp' st'`: the step from the top frame `e` at offset `off` of its
function, over the stack `st`, to the registers `(pc', fp')` and the stack `st'`, by the instruction
at `off` (`X` the function's context):

* `fall`: within the frame, past the same calls, at the next offset; the instruction no jump, a jump
  on a constant `0`, or a jump through the own frame (a branch's zero side);
* `fwd`: within the frame, past the same calls, at a pc past the offset a jump through the own frame
  reads: a constant pc, or the slot of a `match`'s arm in the jump table;
* `skip`: within the frame, past one more call, not taken, at the next offset; through a next frame
  as the frame's last call, or through a call site's frame cell;
* `push`: the callee at the frame's next call entered through a call site's frame cell, its header
  the site's return pc past the offset;
* `tail`: a loop's last call through a next frame, the callee in the frame's place with its header;
* `ret`: a return through the header, the frame's calls all made.

`stepRule_off`: `stepRule_at`'s case analysis, recording this.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Check (getF)

@[expose] public section

/-- **What the step at offset `off` of the top frame `e` did**, over the stack `st`, to the registers
`(pc', fp')` and the stack `st'`. -/
inductive StepOff (P : Core.Program) (Is : List Inst) {κ : ℕ} (img : MemoryImage κ) (A : String → FnAl) (e : Ent)
    (off : ℕ) (st : List Ent) : ℕ → ℕ → List Ent → Prop
  | fall {e' : Ent} {ins : OffsetInstruction} : e'.I = e.I → e'.nc = e.nc → (A e.I.t.name).code[off]? = some ins →
      (∀ oc od of, ins = .jump oc od of →
        (A e.I.t.name).X.zeroAt oc = true ∨ (A e.I.t.name).X.selfAt of = true) →
      StepOff P Is img A e off st (entOf A e.I.t.name + off + 1) e.I.fp (e' :: st)
  | fwd {e' : Ent} {oc od of t : ℕ} : e'.I = e.I → e'.nc = e.nc →
      (A e.I.t.name).code[off]? = some (.jump oc od of) → (A e.I.t.name).X.zeroAt oc = false →
      (A e.I.t.name).X.selfAt of = true →
      ((A e.I.t.name).X.pcAt od = some t ∨ ∃ (z : Zip) (x : V) (arms : List (List Stmt)) (ss : List Stmt) (a : ℕ × ℕ)
        (k : ℕ), ZOk (A e.I.t.name).body z ∧ z.cur = .match_ x arms :: ss ∧ getF (A e.I.t.name).X.arms od = some a ∧
        a.1 = x.idx ∧ k < arms.length ∧ getF (A e.I.t.name).X.jt (a.2 + k) = some t) →
      entOf A e.I.t.name + off < t → StepOff P Is img A e off st t e.I.fp (e' :: st)
  | skip {e' : Ent} {oc od of : ℕ} {c : Call} {f : String} {σ' : Val} : e'.I = e.I → e'.nc = e.nc + 1 →
      (A e.I.t.name).code[off]? = some (.jump oc od of) → (calls (e.pre ++ e.es))[e.nc]? = some c →
      e.I.t.kids[e.nc]? = some (.phantom f σ') →
      ((A e.I.t.name).X.nextAt of = true ∧ (calls (e.pre ++ e.es)).length = e.nc + 1 ∨
        ∃ s, (A e.I.t.name).X.siteAt of c.args c.rets = some s) →
      StepOff P Is img A e off st (entOf A e.I.t.name + off + 1) e.I.fp (e' :: st)
  | push {e' : Ent} {J : Inst} {fn : Fn} {oc od of : ℕ} {c : Call} {s : B2C.Site} : e'.I = e.I → e'.nc = e.nc + 1 →
      (A e.I.t.name).code[off]? = some (.jump oc od of) → (calls (e.pre ++ e.es))[e.nc]? = some c →
      (A e.I.t.name).X.siteAt of c.args c.rets = some s → entOf A e.I.t.name + off < s.r →
      AtPc (entOf A) (alOf A) e' s.r → J ∈ Is →
      e.I.t.kids[e.nc]? = some J.t → e.I.kidFps[e.nc]? = some J.fp → P.find? J.t.name = some fn →
      memOf img (J.fp + 0) = ofK (addressOfIndex s.r) →
      StepOff P Is img A e off st (entOf A J.t.name) J.fp (Ent.enter P J fn :: e' :: st)
  | tail {J : Inst} {fn : Fn} {oc od of : ℕ} : (A e.I.t.name).code[off]? = some (.jump oc od of) →
      (A e.I.t.name).X.zeroAt oc = false → (A e.I.t.name).X.nextAt of = true → (calls (e.pre ++ e.es)).length = e.nc + 1 → J ∈ Is →
      e.I.t.kids[e.nc]? = some J.t → e.I.kidFps[e.nc]? = some J.fp → P.find? J.t.name = some fn →
      memOf img (J.fp + 0) = memOf img (e.I.fp + 0) →
      StepOff P Is img A e off st (entOf A J.t.name) J.fp (Ent.enter P J fn :: st)
  | ret {e2 : Ent} {st2 : List Ent} {oc r0 : ℕ} : (A e.I.t.name).code[off]? = some (.jump oc 0 1) →
      (A e.I.t.name).X.zeroAt oc = false → (A e.I.t.name).X.main = false → st = e2 :: st2 → (calls (e.pre ++ e.es)).length = e.nc →
      memOf img (e.I.fp + 0) = ofK (addressOfIndex r0) → StepOff P Is img A e off st r0 e2.I.fp st

end

public section

variable {P : Core.Program} {rd : Reader} {Is : List Inst}
variable {prog : LeanIsaProgram} {κ : ℕ} {img : MemoryImage κ} {A : String → FnAl} {T : Tree}

theorem calls_atoms_ret : ∀ (as : List Atom) {es : List Ev} {vs : List V} {σ : Val},
    walk σ (as.map Stmt.atom ++ [.ret []]) = .ret es vs → calls es = []
  | as, es, vs, σ, h => by
    rw [walk_atoms_ret] at h
    rw [← (Out.ret.inj h).1]
    clear h
    induction as with
    | nil => rfl
    | cons a as ih => exact ih

/-- **A move keeping the top frame, not at a conditional call, keeps its calls.** -/
theorem Move.nc_same {D D' : List Pop} {e e'' : Ent} {st : List Ent} (hE : EntOk P Is e)
    (h : Move P rd Is (D, e :: st) (D', e'' :: st)) (hn : ∀ c f args ps, e.pos ≠ .callIf c f args :: ps) :
    e''.nc = e.nc := by
  obtain ⟨vs, -, hwp⟩ := hE.path
  have es_of : ∀ {o : Out} {δ : List Ev}, o.pre δ = .ret e.es vs → ∃ rest, e.es = δ ++ rest := fun ho ↦ by
    obtain ⟨es', -, h⟩ := pre_eq_ret ho
    exact ⟨es', h⟩
  have hlen : ∀ {x : Ent} {l : List Ent}, l = x :: l → False := fun h ↦ by
    have := congrArg List.length h; simp at this
  generalize hs : (D', e'' :: st) = s at h
  cases h with
  | atom hp =>
    simp only [Prod.mk.injEq, List.cons.injEq] at hs
    obtain ⟨-, rfl, -⟩ := hs
    rw [hp, walk_atom_cons] at hwp
    obtain ⟨rest, hes⟩ := es_of hwp
    exact (Ent.adv_nc e _ hes).trans rfl
  | ite hp =>
    simp only [Prod.mk.injEq, List.cons.injEq] at hs
    obtain ⟨-, rfl, -⟩ := hs
    rw [hp, walk_ite_cons] at hwp
    obtain ⟨rest, hes⟩ := es_of hwp
    exact (Ent.adv_nc e _ hes).trans rfl
  | arm hk hp hw =>
    simp only [Prod.mk.injEq, List.cons.injEq] at hs
    obtain ⟨-, rfl, -⟩ := hs
    simp [Ent.nc, Ent.adv]
  | skip hp => exact absurd hp (hn _ _ _ _)
  | call => simp only [Prod.mk.injEq, List.cons.injEq] at hs; exact (hlen hs.2.2).elim
  | callIf => simp only [Prod.mk.injEq, List.cons.injEq] at hs; exact (hlen hs.2.2).elim
  | tail hp => exact absurd hp (hn _ _ _ _)
  | dispatch => simp only [Prod.mk.injEq, List.cons.injEq] at hs; exact (hlen hs.2.2).elim
  | ret => simp only [Prod.mk.injEq] at hs; exact (hlen hs.2.symm).elim
  | alloc =>
    simp only [Prod.mk.injEq, List.cons.injEq] at hs
    obtain ⟨-, rfl, -⟩ := hs
    rfl

/-- **The step rule at one state, with its offset and what it did there** (`StepOff`): from a state
of the track at `(pc, fp)`, its top frame's jumps' cells read, a step to registers short of the
final ones lands at registers of a state of the track. -/
theorem stepRule_off (hP : ProgAl prog P A)
    (hIs : ∀ I ∈ Is, ∀ (i : ℕ) (k : Tree), I.t.kids[i]? = some k → ∃ J ∈ Is, J.t = k ∧ I.kidFps[i]? = some J.fp)
    {pc fp : ℕ} {done : List Pop} {e : Ent} {st : List Ent} {r' : Registers K}
    (h : RefOk P rd Is T (memOf img) (entOf A) (alOf A) pc fp (done, e :: st)) (hc : JumpCells img A e pc)
    (hstep : step prog img (regs pc fp) = some r') (hne' : r' ≠ Registers.final prog) :
    ∃ off, pc = entOf A e.I.t.name + off ∧ ∃ pc' fp' s', r' = regs pc' fp' ∧
      RefOk P rd Is T (memOf img) (entOf A) (alOf A) pc' fp' s' ∧ StepOff P Is img A e off st pc' fp' s'.2 := by
  obtain ⟨e0, st0, hst, hE, hfp, hat⟩ := h.top
  obtain ⟨rfl, rfl⟩ := List.cons.inj hst
  subst hfp
  have hok := hP.ok _ _ hE.find
  obtain ⟨off, ins, z, tabs, r, as, hpc, hins, hz, ⟨bs, hbs⟩, -, hr, e', hm, hI, hfn, hp, -, hnext, h1, h2, h3⟩ :=
    atPc_step (P := P) (rd := rd) (Is := Is) hok rfl (fun _ ↦ rfl) hat done st
  refine ⟨off, hpc, ?_⟩
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
  have hnc : e'.nc = e.nc := by
    obtain ⟨vs1, -, hw1⟩ := hE.path
    obtain ⟨vs2, -, hw2⟩ := hE'.path
    rw [hbs, walk_atoms_pre', hσ.symm, ← hp, hw2] at hw1
    exact (EntOk.nc_of_es hE hE' hI hfn (Out.ret.inj hw1).1.symm).trans (by rw [calls_map_atom]; rfl)
  have hent : entOf A e'.I.t.name = (A e.I.t.name).X.entry := by rw [hI]; rfl
  have hal : ∀ o, alOf A e'.I.t.name o = alignAt (A e.I.t.name).X (A e.I.t.name).body (A e.I.t.name).code
      (A e.I.t.name).d o := fun o ↦ by rw [hI]; rfl
  have hpcE : pc = entOf A e.I.t.name + off := hpc
  -- a move within the frame
  have win : ∀ {e'' : Ent} {pc' : ℕ} {done' : List Pop}, Relation.ReflTransGen (Move P rd Is) (done, e :: st) (done', e'' :: st) →
      e''.I = e.I → AtPc (entOf A) (alOf A) e'' pc' → StepOff P Is img A e off st pc' e.I.fp (e'' :: st) →
      ∃ pc'' fp'' s', regs pc' e.I.fp = regs pc'' fp'' ∧ RefOk P rd Is T (memOf img) (entOf A) (alOf A) pc'' fp'' s' ∧
        StepOff P Is img A e off st pc'' fp'' s'.2 :=
    fun hm' hI' ha' hk ↦ ⟨_, _, _, rfl, h.within hm' hI' ha', hk⟩
  have hcalls_e : ∀ {c : Call} {cs : List Call}, calls e'.es = c :: cs → (calls (e.pre ++ e.es))[e.nc]? = some c :=
    fun hc' ↦ by rw [← hfull, ← hnc]; exact calls_at hc'
  by_cases hj : ∃ oc od of, ins = .jump oc od of
  swap
  · have hnj : ∀ oc od of, ins ≠ .jump oc od of := fun oc od of h ↦ hj ⟨oc, od, of, h⟩
    have hjf : ins.isJump = false := by
      cases ins <;> first | rfl | exact absurd rfl (hnj _ _ _)
    have hr' := ((execute_iff_holds hjf).mp hstep).2
    rw [hr']
    refine win hm hI (hnext hnj) ?_
    rw [hpcE]
    exact .fall hI hnc hins fun oc od of h' ↦ absurd h' (hnj oc od of)
  obtain ⟨oc, od, of, rfl⟩ := hj
  obtain ⟨cv, dv, fv, hcv, hdv, hfv, -, -, -, rfl⟩ := execute_jump_iff.mp hstep
  rw [read_cell] at hcv hdv hfv
  set X := (A e.I.t.name).X with hX
  set D := done ++ as.flatMap (fun a ↦ a.pops rd e.σ) with hD
  have hK : ∀ s2 : List Pop × List Ent, Move P rd Is (D, e' :: st) s2 → StepKind P e.I e.nc st s2.2 :=
    fun s2 hmv ↦ hI ▸ hnc ▸ Move.kind hE' hmv
  have fin : ∀ e'' pc', Move P rd Is (D, e' :: st) (D, e'' :: st) → e''.I = e'.I → AtPc (entOf A) (alOf A) e'' pc' →
      StepOff P Is img A e off st pc' e.I.fp (e'' :: st) →
      ∃ pc'' fp'' s', regs pc' e.I.fp = regs pc'' fp'' ∧ RefOk P rd Is T (memOf img) (entOf A) (alOf A) pc'' fp'' s' ∧
        StepOff P Is img A e off st pc'' fp'' s'.2 :=
    fun e'' pc' hm' hI' ha' hk ↦ win (hm.trans (.single hm')) (hI'.trans hI) ha' hk
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
  have hfall : ∀ e'', e''.I = e.I → e''.nc = e.nc → (X.zeroAt oc = true ∨ X.selfAt of = true) →
      StepOff P Is img A e off st (pc + 1) e.I.fp (e'' :: st) := fun e'' h1' h2' h3' ↦ by
    rw [hpcE]
    exact .fall h1' h2' hins fun oc' od' of' h' ↦ by
      cases h'
      exact h3'
  cases hz0 : X.zeroAt oc
  swap
  · have hr0 : r = (some z, []) := by simpa [insStep, jumpStep, hz0] using hr.symm
    obtain rfl := hsome (hc.zero oc hz0) hcv
    rw [ite_eq_left rfl]
    exact win hm hI ⟨off + 1, by rw [hent]; omega, z.pos, by rw [hal]; exact h1 z (by rw [hr0]; rfl), [],
      by simp, by simp [hp]⟩ (hfall e' hI hnc (.inl hz0))
  cases hfw : fwdJ X off oc od of
  swap
  · obtain ⟨hnz, hself, t, o, ht, ho, rfl⟩ := fwd_step hr hz0 hfw
    obtain ⟨ho1, ho2⟩ := fwdOff_eq ho
    rw [hif t e.I.fp (hnz0 hnz) (hsome (hc.pcw od t ht) hdv) (hsome (hc.self of hself) hfv)]
    exact win hm hI ⟨o, by rw [hent]; omega, z.pos, by rw [hal]; exact h2 (o, z) List.mem_cons_self, [],
      by simp, by simp [hp]⟩ (.fwd hI hnc hins hz0 hself (.inl ht) ho2)
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
    have hnc'' : e''.nc = e.nc := (Move.nc_same hE' hm'' (by rw [hp, Zip.pos_head hzc]; intro _ _ _ _ h; cases h)).trans hnc
    by_cases h0 : e.σ c = 0
    · rw [ite_eq_left h0] at ha''
      rw [ite_eq_left h0]
      exact fin e'' _ hm'' hI'' (by rw [hpc]; exact ha'') (hfall e'' (hI''.trans hI) hnc'' (.inr hself))
    · rw [ite_eq_right h0] at ha''
      obtain ⟨ho1, ho2⟩ := fwdOff_eq ho
      rw [hif t e.I.fp h0 (hsome (hc.pcw od t ht) hdv) (hsome (hc.self of hself) hfv)]
      exact fin e'' _ hm'' hI'' (by rw [show t = X.entry + o by omega]; exact ha'')
        (.fwd (hI''.trans hI) hnc'' hins hz0 hself (.inl ht) ho2)
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
    have hnc'' : e''.nc = e.nc :=
      (Move.nc_same hE' hm'' (by rw [hp, Zip.pos_head hzc]; intro _ _ _ _ h; cases h)).trans hnc
    rw [hif t e.I.fp (hnz0 hnz) (hsome hcell hdv) (hsome (hc.self of hself) hfv)]
    exact fin e'' _ hm'' hI'' (by rw [show t = X.entry + (t - X.entry) by omega]; exact ha'')
      (.fwd (hI''.trans hI) hnc'' hins hz0 hself (.inr ⟨z, x, arms, ss, a, k, hz, hzc, ha, hax, hk, ht⟩) hlt)
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
    have hm'' : Move P rd Is (D, e' :: st) (D, Ent.enter P J fn :: e'.adv (z.next ss).pos 1 :: st) :=
      .call (hp.trans (Zip.pos_head hzc)) hJ hk hkf hfJ
    have ha'' := atPc_of_norm (e := e'.adv (z.next ss).pos 1) hent hal hc' rfl (h2 _ List.mem_cons_self)
    have hnc'' : (e'.adv (z.next ss).pos 1).nc = e.nc + 1 := by
      rw [← hnc]; exact Ent.adv_nc e' _ hes'
    obtain ⟨ho1, ho2⟩ := fwdOff_eq ho
    have htJ : entOf A J.t.name = t := by rw [hname]; exact hP.ent _ _ t f hE.find hent'
    rw [hif t J.fp (hnz0 hnz) (hsome (hc.pcw od t ht) hdv) (hsome hq hfv), ← htJ]
    refine ⟨_, J.fp, _, rfl, ⟨h.track.moves (hm.trans (.single hm'')),
      Linked.push h.linked hI ha'' rfl (atPc_enter hP hfJ) ?_ (memOf_of hk1)⟩, ?_⟩
    · rw [memOf_of hk0]
      congr 2
      omega
    · exact .push hI hnc'' hins (hcalls_e hcalls) hs ho2 (by rw [show s.r = X.entry + o by omega]; exact ha'') hJ
        (by rw [← hI, ← hnc]; exact hk) (by rw [← hI, ← hnc]; exact hkf) hfJ (memOf_of hk0)
  | callIf c f args =>
    obtain ⟨hloc, t, ca, ht, hent', hca, rfl, hcase⟩ := callIf_step hr hzc hz0 hfw
    rw [walk_callIf_cons] at hwp
    obtain ⟨es', hwes, hes'⟩ := pre_eq_ret hwp
    have hcell := hinK c (by rw [hes']; exact List.mem_cons_self)
    rw [hloc] at hcell
    obtain rfl := hsome hcell hcv
    have hlast : X.nextAt of = true → retNil ca.pos = true → calls es' = [] := fun _ hrn ↦ by
      obtain ⟨as2, -, hpos2, -⟩ := normZ_pos _ hca
      rw [retNil_eq hrn] at hpos2
      rw [hpos2] at hwes
      exact calls_atoms_ret as2 hwes
    have hlen1 : calls es' = [] → (calls (e.pre ++ e.es)).length = e.nc + 1 := fun hnil ↦ by
      rw [← hfull, ← hnc, calls_append', hes', Ent.nc, List.length_append]
      simp only [calls, List.filterMap_cons, Ev.call?, List.filterMap_append] at hnil ⊢
      split_ifs <;> simp_all
    by_cases h0 : e.σ c = 0
    · have h0' : e'.σ c = 0 := hσ ▸ h0
      rw [ite_eq_left h0'] at hes'
      have hcalls : calls e'.es = ⟨f, args, [], false⟩ :: calls es' := by rw [hes']; rfl
      obtain ⟨k, -, hk, rv, hph⟩ := hE'.head_kid hcalls
      simp only [Bool.false_eq_true, ↓reduceIte] at hph
      obtain ⟨⟨f', σ', rfl⟩, -⟩ := hph
      have hm'' : Move P rd Is (D, e' :: st) (D, e'.adv (z.next ss).pos 2 :: st) :=
        .skip (hp.trans (Zip.pos_head hzc)) h0'
      have ha'' := atPc_of_norm (e := e'.adv (z.next ss).pos 2) hent hal hca rfl (h1 _ rfl)
      have hnc'' : (e'.adv (z.next ss).pos 2).nc = e.nc + 1 := by
        rw [← hnc]; exact Ent.adv_nc e' _ hes'
      rw [ite_eq_left h0]
      refine fin _ _ hm'' rfl (by rw [hpc]; exact ha'') ?_
      rw [hpcE]
      refine .skip hI hnc'' hins (hcalls_e hcalls) (by rw [← hI, ← hnc]; exact hk) ?_
      rcases hcase with ⟨hnx, hrn⟩ | ⟨-, s, hs, -⟩
      · exact .inl ⟨hnx, hlen1 (hlast hnx hrn)⟩
      · exact .inr ⟨s, hs⟩
    have h0' : e'.σ c ≠ 0 := hσ ▸ h0
    rw [ite_eq_right h0'] at hes'
    have hcalls : calls e'.es = ⟨f, args, [], true⟩ :: calls es' := by rw [hes']; rfl
    obtain ⟨J, hJ, fn, hk, hkf, hfJ, hname⟩ := hE'.callee_named hIs hcalls rfl
    have htJ : entOf A J.t.name = t := by rw [hname]; exact hP.ent _ _ t f hE.find hent'
    rcases hcase with ⟨hnx, hrn⟩ | ⟨-, s, hs, hsr⟩
    · obtain ⟨as2, has2, hpos2, -⟩ := normZ_pos _ hca
      rw [retNil_eq hrn] at hpos2
      have hnil := hlast hnx hrn
      obtain ⟨hfp0, kfp, hkfp, hq, hk0, hk1⟩ := hc.tail off oc od of hpc hins hnx _ vs0 hw0 e'.nc _
        (by rw [← hfull]; exact calls_at hcalls) rfl
        (by rw [← hfull, calls_append', hcalls, hnil, Ent.nc, List.length_append]; rfl)
      rw [← hI, hkf] at hkfp
      obtain rfl := Option.some.inj hkfp
      have hmv : Move P rd Is (D, e' :: st) (D, Ent.enter P J fn :: st) :=
        .tail (hp.trans (Zip.pos_head hzc)) h0' ⟨as2, fun a ha ↦ flowAtom_pops (has2 a ha), hpos2⟩ hJ hk hkf hfJ
      rw [hif t J.fp h0 (hsome (hc.pcw od t ht) hdv) (hsome hq hfv), ← htJ]
      rcases st with _ | ⟨e2, st2⟩
      · exact absurd h.linked.2.1 hfp0
      refine ⟨_, J.fp, _, rfl, ⟨h.track.moves (hm.trans (.single hmv)),
        Linked.tail h.linked rfl (atPc_enter hP hfJ) ?_ ?_⟩, ?_⟩
      · exact congrArg (·.getD 0) hk0
      · exact congrArg (·.getD 0) hk1
      · exact .tail hins hz0 hnx (hlen1 hnil) hJ (by rw [← hI, ← hnc]; exact hk) (by rw [← hI, ← hnc]; exact hkf) hfJ
          (congrArg (·.getD 0) hk0)
    · obtain ⟨kfp, hkfp, hq, hk0, hk1, -⟩ := hc.site _ vs0 hw0 e'.nc _ of s
        (by rw [← hfull]; exact calls_at hcalls) rfl hs
      rw [← hI, hkf] at hkfp
      obtain rfl := Option.some.inj hkfp
      have hm'' : Move P rd Is (D, e' :: st) (D, Ent.enter P J fn :: e'.adv (z.next ss).pos 2 :: st) :=
        .callIf (hp.trans (Zip.pos_head hzc)) h0' hJ hk hkf hfJ
      have ha'' := atPc_of_norm (e := e'.adv (z.next ss).pos 2) hent hal hca rfl (h1 _ rfl)
      have hnc'' : (e'.adv (z.next ss).pos 2).nc = e.nc + 1 := by
        rw [← hnc]; exact Ent.adv_nc e' _ hes'
      rw [hif t J.fp h0 (hsome (hc.pcw od t ht) hdv) (hsome hq hfv), ← htJ]
      refine ⟨_, J.fp, _, rfl, ⟨h.track.moves (hm.trans (.single hm'')),
        Linked.push h.linked hI ha'' rfl (atPc_enter hP hfJ) ?_ (memOf_of hk1)⟩, ?_⟩
      · rw [memOf_of hk0, hsr]
        rfl
      · exact .push hI hnc'' hins (hcalls_e hcalls) hs (by rw [hsr]; show _ < X.entry + off + 1; omega)
          (by rw [hsr]; exact ha'') hJ (by rw [← hI, ← hnc]; exact hk) (by rw [← hI, ← hnc]; exact hkf) hfJ
          (memOf_of hk0)
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
    have hm'' : Move P rd Is (D, e' :: st) (D, Ent.enter P J fn :: e'.adv (z.next ss).pos 1 :: st) :=
      .dispatch hi (hp.trans (Zip.pos_head hzc)) hpk hJ hk hkf hfJ
    have ha'' := atPc_of_norm (e := e'.adv (z.next ss).pos 1) hent hal hc' rfl (h2 _ List.mem_cons_self)
    have hnc'' : (e'.adv (z.next ss).pos 1).nc = e.nc + 1 := by
      rw [← hnc]; exact Ent.adv_nc e' _ hes'
    obtain ⟨ho1, ho2⟩ := fwdOff_eq ho
    have hd := htg (by rw [hst]; exact hod)
    rw [hst] at hd
    rw [hif (entOf A J.t.name) J.fp (hnz0 hnz) (by rw [hname]; exact hsome hd hdv) (hsome hq hfv)]
    refine ⟨_, J.fp, _, rfl, ⟨h.track.moves (hm.trans (.single hm'')),
      Linked.push h.linked hI ha'' rfl (atPc_enter hP hfJ) ?_ (memOf_of hk1)⟩, ?_⟩
    · rw [memOf_of hk0]
      congr 2
      omega
    · exact .push hI hnc'' hins (hcalls_e hcalls) hs ho2 (by rw [show s.r = X.entry + o by omega]; exact ha'') hJ
        (by rw [← hI, ← hnc]; exact hk) (by rw [← hI, ← hnc]; exact hkf) hfJ (memOf_of hk0)
  | ret vs' =>
    obtain ⟨rfl, hnz, hm0⟩ := ret_step hr hzc hz0 hfw
    rw [walk_ret_cons] at hwp
    have hes0 : e'.es = [] := (Out.ret.inj hwp).1.symm
    have hcl : (calls (e.pre ++ e.es)).length = e.nc := by
      rw [← hfull, ← hnc, hes0, List.append_nil]; rfl
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
      exact ⟨r0, e2.I.fp, _, rfl, ⟨h.track.moves (hm.trans (.single hmv)), hl⟩,
        .ret hins hz0 hmain rfl hcl hr0⟩
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
