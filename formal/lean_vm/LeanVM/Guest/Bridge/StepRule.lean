/-
  LeanVM.Guest.Bridge.StepRule

  The tree track's step rule at the register level: on a program whose functions pass the alignment check, where each frame's cells hold what its jumps read, a step of the run from a state of the track lands at registers of a state reached by moves.
-/

module

public import LeanVM.Guest.Bridge.AlignJump

/-!
# The step rule at the register level

`FnAl`: what the rule reads of a function, by name: its alignment check's context, body, code and advice; `alOf A` and `entOf A` are the alignment (`alignAt`) and the entries the tree track is at. `memOf img` reads the memory by index. `ProgAl prog P A`: every function of `P` passes its check on its body, its code is `prog`'s at its entry, a callee the check names by entry is entered there, and `main`'s halting pc is the final one.

`JumpCells img A e`: what the frame `e`'s jumps read of the memory, at the cells its function's check names: a constant `0` or nonzero constant, its own frame, a pc; a branch's or conditional call's condition `σ c` (any value its path tests); a `match`'s target word, the arm the selector `g^k` picks (`k`-th slot of the table); a call's callee frame, its header (the site's return pc and the frame), a dispatch's target the callee's entry; a loop's tail call (its last) its next frame, whose header is the frame's own, not at frame `0`; the frame's own header; `main` at frame `0`, and only `main`.

`stepRule_of`: under `ProgAl` and the honest instances closed under callees, if the top frame of each state of the track against the run has `JumpCells`, the track has a step rule (`StepRule`): a non-jump falls through, a jump on a constant `0` falls through, a forward jump in the frame lands at its target, and by the head of the frame's position, a branch takes the side `σ c` picks, a `match` the arm its selector picks, a call, a conditional call taken or a dispatch enters its callee (the caller at the site's return pc), a loop's tail call replaces the frame by its callee, a return pops the frame to the registers its header holds; `main`'s return reaches the final registers, where the rule asks nothing.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Check (getF)

@[expose] public section

/-- What the step rule reads of a function: its alignment check's context, body, code and advice. -/
structure FnAl where
  X : AlignCtx
  body : List Stmt
  code : List OffsetInstruction
  d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)

/-- The alignment, by name and offset. -/
noncomputable def alOf (A : String → FnAl) (f : String) (off : ℕ) : Option (List Stmt) :=
  alignAt (A f).X (A f).body (A f).code (A f).d off

/-- The entries, by name. -/
def entOf (A : String → FnAl) (f : String) : ℕ := (A f).X.entry

/-- The memory by index. -/
noncomputable def memOf {κ : ℕ} (img : MemoryImage κ) (n : ℕ) : E := (img.read (addressOfIndex n)).getD 0

/-- The word at cell `o` of frame `fp`. -/
noncomputable abbrev cellAt {κ : ℕ} (img : MemoryImage κ) (fp o : ℕ) : Option E := img.read (addressOfIndex (fp + o))

/-- **The program's functions align**: each passes its check on its body, its code at its entry, a
callee named by entry entered there, `main`'s halting pc the final one. -/
structure ProgAl (prog : LeanIsaProgram) (P : Core.Program) (A : String → FnAl) : Prop where
  ok : ∀ f fn, P.find? f = some fn → alignOk (A f).X (A f).body (A f).code (A f).d = true
  body : ∀ f fn, P.find? f = some fn → (A f).body = fn.body
  fetch : ∀ f fn, P.find? f = some fn → ∀ off ins, (A f).code[off]? = some ins →
    prog.fetch (addressOfIndex ((A f).X.entry + off)) = some ins.toLeanIsaInstruction
  ent : ∀ f fn t g, P.find? f = some fn → (A f).X.entOk t g = true → (A g).X.entry = t
  halt : ∀ f fn, P.find? f = some fn → (A f).X.main = true → regs (A f).X.halt 0 = Registers.final prog

/-- **What a frame's jumps read**, at the cells its function's check names. -/
structure JumpCells {κ : ℕ} (img : MemoryImage κ) (A : String → FnAl) (e : Ent) : Prop where
  zero : ∀ o, (A e.I.t.name).X.zeroAt o = true → cellAt img e.I.fp o = some 0
  nz : ∀ o, (A e.I.t.name).X.nzAt o = true → ∃ w, cellAt img e.I.fp o = some w ∧ w ≠ 0
  self : ∀ o, (A e.I.t.name).X.selfAt o = true → cellAt img e.I.fp o = some (ofK (addressOfIndex e.I.fp))
  pc : ∀ o t, (A e.I.t.name).X.pcAt o = some t → cellAt img e.I.fp o = some (ofK (addressOfIndex t))
  cond : ∀ c es vs, walk e.σ e.fn.body = .ret es vs → Ev.inK c ∈ es →
    cellAt img e.I.fp ((A e.I.t.name).X.locAt c.idx) = some (e.σ c)
  arm : ∀ (bs : List Atom) x arms ps, e.pos = bs.map Stmt.atom ++ .match_ x arms :: ps → ∀ od a,
    getF (A e.I.t.name).X.arms od = some a → a.1 = x.idx → ∀ k t, e.σ x = ofK (addressOfIndex k) →
      getF (A e.I.t.name).X.jt (a.2 + k) = some t → cellAt img e.I.fp od = some (ofK (addressOfIndex t))
  site : ∀ es vs, walk e.σ e.fn.body = .ret es vs → ∀ (i : ℕ) (c : Call) q (s : B2C.Site), (calls es)[i]? = some c →
    c.taken = true →
    (A e.I.t.name).X.siteAt q c.args c.rets = some s → ∃ kfp, e.I.kidFps[i]? = some kfp ∧
      cellAt img e.I.fp q = some (ofK (addressOfIndex kfp)) ∧
      cellAt img kfp 0 = some (ofK (addressOfIndex s.r)) ∧ cellAt img kfp 1 = some (ofK (addressOfIndex e.I.fp)) ∧
      (s.tgt ≠ 0 → cellAt img e.I.fp s.tgt = some (ofK (addressOfIndex (A c.f).X.entry)))
  tail : ∀ es vs, walk e.σ e.fn.body = .ret es vs → ∀ (i : ℕ) (c : Call) q, (calls es)[i]? = some c → c.taken = true →
    i + 1 = (calls es).length → (A e.I.t.name).X.nextAt q = true → e.I.fp ≠ 0 ∧ ∃ kfp, e.I.kidFps[i]? = some kfp ∧
      cellAt img e.I.fp q = some (ofK (addressOfIndex kfp)) ∧
      cellAt img kfp 0 = cellAt img e.I.fp 0 ∧ cellAt img kfp 1 = cellAt img e.I.fp 1
  hdr : (cellAt img e.I.fp 0).isSome ∧ (cellAt img e.I.fp 1).isSome
  main : (A e.I.t.name).X.main = true → e.I.fp = 0
  bot : e.I.fp = 0 → (A e.I.t.name).X.main = true

end

public section

/-! ## Paths through a jump -/

section Paths

variable {σ : Val}

/-- A `match` not stuck takes an arm, the first its selector `g^(j + k)` picks. -/
theorem walkArms_take {x : V} : ∀ (arms : List (List Stmt)) (j : ℕ), walkArms σ x j arms ≠ .stuck →
    ∃ k, ∃ hk : k < arms.length, σ x = ofK (addressOfIndex (j + k)) ∧ walkArms σ x j arms = walk σ arms[k]
  | [], _, h => absurd (by rw [walkArms]) h
  | a :: as, j, h => by
    rw [walkArms] at h ⊢
    by_cases hx : σ x = ofK (addressOfIndex j)
    · exact ⟨0, by simp, by simpa using hx, by simp only [hx, ↓reduceIte]; rfl⟩
    · simp only [hx, ↓reduceIte] at h ⊢
      obtain ⟨k, hk, h1, h2⟩ := walkArms_take as (j + 1) h
      exact ⟨k + 1, by simpa using hk, by rw [h1]; congr 2; omega, by rw [h2]; rfl⟩

/-- A dispatch not stuck calls a callee. -/
theorem pick_take {x : V} {args rets : List V} : ∀ (fs : List String) (j : ℕ), pick σ x args rets j fs ≠ .stuck →
    ∃ i, ∃ hi : i < fs.length, pick σ x args rets j fs = .fall [.call fs[i] args rets]
  | [], _, h => absurd (by rw [pick]) h
  | f :: fs, j, h => by
    rw [pick] at h ⊢
    by_cases hx : σ x = ofK (addressOfIndex j)
    · exact ⟨0, by simp, by simp only [hx, ↓reduceIte]; rfl⟩
    · simp only [hx, ↓reduceIte] at h ⊢
      obtain ⟨i, hi, h1⟩ := pick_take fs (j + 1) h
      exact ⟨i + 1, by simpa using hi, by rw [h1]; rfl⟩

theorem seq_ne_stuck {o k : Out} {es : List Ev} {vs : List V} (h : o.seq k = .ret es vs) : o ≠ .stuck := by
  rintro rfl; cases h

end Paths

variable {P : Core.Program} {rd : Reader} {Is : List Inst}

theorem EntOk.walk_pos {e : Ent} (h : EntOk P Is e) : ∃ vs, walk e.σ e.pos = .ret e.es vs :=
  let ⟨vs, _, h2⟩ := h.path; ⟨vs, h2⟩

/-- **The callee of a call left, by name**: an instance at the frame's next callee frame, of the
called function. -/
theorem EntOk.callee_named {e : Ent} (h : EntOk P Is e)
    (hIs : ∀ I ∈ Is, ∀ (i : ℕ) (k : Tree), I.t.kids[i]? = some k → ∃ J ∈ Is, J.t = k ∧ I.kidFps[i]? = some J.fp)
    {c : Call} {cs : List Call} (hc : calls e.es = c :: cs) (ht : c.taken = true) :
    ∃ J ∈ Is, ∃ fn, e.I.t.kids[e.nc]? = some J.t ∧ e.I.kidFps[e.nc]? = some J.fp ∧
      P.find? J.t.name = some fn ∧ J.t.name = c.f := by
  obtain ⟨J, hJ, fn, hk, hkf, hf⟩ := h.callee hIs hc ht
  obtain ⟨k, hd, hk', -⟩ := h.head_kid hc
  rw [hk] at hk'
  obtain rfl := Option.some.inj hk'
  obtain ⟨rv, hkv⟩ := h.kv
  rw [hc, hd] at hkv
  exact ⟨J, hJ, fn, hk, hkf, hf, hkv.1⟩

/-- The frame's next call, at its index in the whole path. -/
theorem calls_at {e : Ent} {c : Call} {cs : List Call} (hc : calls e.es = c :: cs) :
    (calls (e.pre ++ e.es))[e.nc]? = some c := by
  rw [calls_append', hc, Ent.nc, List.getElem?_append_right le_rfl, Nat.sub_self]
  rfl

theorem read_cell {κ : ℕ} {img : MemoryImage κ} (fp o : ℕ) :
    img.read (addressOfIndex fp * addressOfIndex o) = cellAt img fp o := by
  simp only [cellAt, addressOfIndex, pow_add]

theorem memOf_of {κ : ℕ} {img : MemoryImage κ} {n : ℕ} {w : E} (h : img.read (addressOfIndex n) = some w) :
    memOf img n = w := by
  simp [memOf, h]

theorem regs_ofK (a b : ℕ) :
    (⟨(ofK (addressOfIndex a)).limb 0, (ofK (addressOfIndex b)).limb 0⟩ : Registers K) = regs a b := by
  simp [regs]

/-! ## The moves at a jump -/

section Moves

variable {X : AlignCtx} {body : List Stmt} {code : List OffsetInstruction}
  {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} {ent : String → ℕ} {al : String → ℕ → Option (List Stmt)}

/-- **A dispatch**: the callee its selector picks entered, the caller at the site's return pc. -/
theorem atPc_dispatch {e : Ent} (hent : ent e.I.t.name = X.entry)
    (hal : ∀ off, al e.I.t.name off = alignAt X body code d off) {z : Zip} {x : V} {fs : List String}
    {args rets : List V} {ss : List Stmt} (hp : e.pos = z.pos) (hz : z.cur = .dispatch x fs args rets :: ss)
    {c : Zip} {o : ℕ} (hc : normZ X.fuel (z.next ss) = some c) (ho : alignAt X body code d o = some c.pos)
    {i : ℕ} (hi : i < fs.length) (hpk : pick e.σ x args rets 0 fs = .fall [.call fs[i] args rets])
    {J : Inst} {fn : Fn} (hJ : J ∈ Is) (hk : e.I.t.kids[e.nc]? = some J.t) (hkf : e.I.kidFps[e.nc]? = some J.fp)
    (hf : P.find? J.t.name = some fn) (done : List Pop) (st : List Ent) :
    ∃ e', Move P rd Is (done, e :: st) (done, Ent.enter P J fn :: e' :: st) ∧ e'.I = e.I ∧
      AtPc ent al e' (X.entry + o) :=
  ⟨_, .dispatch hi (hp.trans (Zip.pos_head hz)) hpk hJ hk hkf hf, rfl,
    atPc_of_norm (e := e.adv (z.next ss).pos 1) hent hal hc rfl ho⟩

/-- A forward jump in the frame: on a nonzero constant, its target a constant pc past the offset. -/
theorem fwd_step {i oc od of : ℕ} {tabs : List (ℕ × Zip × ℕ)} {z : Zip} {r : Option Zip × List (ℕ × Zip)}
    (hr : insStep X i (.jump oc od of) tabs z = some r) (hzero : X.zeroAt oc = false)
    (hfwd : fwdJ X i oc od of = true) :
    X.nzAt oc = true ∧ X.selfAt of = true ∧ ∃ t o, X.pcAt od = some t ∧ X.fwdOff i t = some o ∧
      r = (none, [(o, z)]) := by
  have hf := hfwd
  simp only [fwdJ, Bool.and_eq_true] at hf
  simp only [insStep, jumpStep, hzero, hfwd, Bool.cond_false, Bool.cond_true] at hr
  obtain ⟨t, ht, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hr
  exact ⟨hf.1.1, hf.1.2, t, o, ht, ho, rfl⟩

theorem retNil_eq : ∀ {ss : List Stmt}, retNil ss = true → ss = [.ret []]
  | [.ret []], _ => rfl
  | [], h | [.atom _], h | [.ite ..], h | [.match_ ..], h | [.call ..], h | [.callIf ..], h | [.dispatch ..], h
  | [.ret (_ :: _)], h | _ :: _ :: _, h => by simp [retNil] at h

/-- **A callee entered at its entry**, where its function's check puts its body. -/
theorem atPc_enter {prog : LeanIsaProgram} {A : String → FnAl} (hP : ProgAl prog P A) {J : Inst} {fn : Fn}
    (hf : P.find? J.t.name = some fn) : AtPc (entOf A) (alOf A) (Ent.enter P J fn) (entOf A J.t.name) := by
  refine ⟨0, rfl, fn.body, ?_, [], by simp, rfl⟩
  change alignAt (A J.t.name).X (A J.t.name).body (A J.t.name).code (A J.t.name).d 0 = some fn.body
  rw [alignAt_zero (hP.ok _ _ hf), hP.body _ _ hf]

end Moves

/-! ## The step rule -/

variable {prog : LeanIsaProgram} {κ : ℕ} {img : MemoryImage κ} {A : String → FnAl} {T : Tree}

/-- The track moved inside the top frame, at a new pc of the frame. -/
private theorem within' {pc fp pc' : ℕ} {done done' : List Pop} {e e' : Ent} {st : List Ent}
    (h : RefOk P rd Is T (memOf img) (entOf A) (alOf A) pc fp (done, e :: st))
    (hm : Relation.ReflTransGen (Move P rd Is) (done, e :: st) (done', e' :: st)) (hI : e'.I = e.I)
    (ha : AtPc (entOf A) (alOf A) e' pc') :
    ∃ pc'' fp'' s', regs pc' fp = regs pc'' fp'' ∧ Relation.ReflTransGen (Move P rd Is) (done, e :: st) s' ∧
      RefOk P rd Is T (memOf img) (entOf A) (alOf A) pc'' fp'' s' :=
  ⟨pc', fp, _, rfl, hm, h.within hm hI ha⟩

/-- **The step rule at the register level.** -/
theorem stepRule_of (hP : ProgAl prog P A)
    (hIs : ∀ I ∈ Is, ∀ (i : ℕ) (k : Tree), I.t.kids[i]? = some k → ∃ J ∈ Is, J.t = k ∧ I.kidFps[i]? = some J.fp)
    (hC : ∀ pc fp done e st, RefOk P rd Is T (memOf img) (entOf A) (alOf A) pc fp (done, e :: st) →
      JumpCells img A e) :
    StepRule prog img (Move P rd Is) (RefOk P rd Is T (memOf img) (entOf A) (alOf A)) := by
  rintro pc fp ⟨done, st⟩ r' h - hstep hne'
  obtain ⟨e, st, rfl, hE, hfp, hat⟩ := h.top
  have hc := hC _ _ _ _ _ h
  subst hfp
  have hok := hP.ok _ _ hE.find
  obtain ⟨off, ins, z, tabs, r, as, hpc, hins, hz, ⟨bs, hbs⟩, -, hr, e', hm, hI, hfn, hp, -, hnext, h1, h2, h3⟩ :=
    atPc_step (P := P) (rd := rd) (Is := Is) hok rfl (fun _ ↦ rfl) hat done st
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
    exact within' h hm hI (hnext hnj)
  obtain ⟨oc, od, of, rfl⟩ := hj
  obtain ⟨cv, dv, fv, hcv, hdv, hfv, -, -, -, rfl⟩ := execute_jump_iff.mp hstep
  rw [read_cell] at hcv hdv hfv
  set X := (A e.I.t.name).X with hX
  set D := done ++ as.flatMap (fun a ↦ a.pops rd e.σ) with hD
  have fin : ∀ e'' pc', Move P rd Is (D, e' :: st) (D, e'' :: st) → e''.I = e'.I → AtPc (entOf A) (alOf A) e'' pc' →
      ∃ pc'' fp'' s', regs pc' e.I.fp = regs pc'' fp'' ∧ Relation.ReflTransGen (Move P rd Is) (done, e :: st) s' ∧
        RefOk P rd Is T (memOf img) (entOf A) (alOf A) pc'' fp'' s' :=
    fun e'' pc' hm' hI' ha' ↦ within' h (hm.trans (.single hm')) (hI'.trans hI) ha'
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
    exact within' h hm hI ⟨off + 1, by rw [hent]; omega, z.pos, by rw [hal]; exact h1 z (by rw [hr0]; rfl), [],
      by simp, by simp [hp]⟩
  cases hfw : fwdJ X off oc od of
  swap
  · obtain ⟨hnz, hself, t, o, ht, ho, rfl⟩ := fwd_step hr hz0 hfw
    obtain ⟨ho1, ho2⟩ := fwdOff_eq ho
    rw [hif t e.I.fp (hnz0 hnz) (hsome (hc.pc od t ht) hdv) (hsome (hc.self of hself) hfv)]
    exact within' h hm hI ⟨o, by rw [hent]; omega, z.pos, by rw [hal]; exact h2 (o, z) List.mem_cons_self, [],
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
      rw [hif t e.I.fp h0 (hsome (hc.pc od t ht) hdv) (hsome (hc.self of hself) hfv)]
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
    have hcell := hc.arm bs x arms (z.next ss).pos (by rw [hbs, Zip.pos_head hzc]) od a ha hax k t
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
    rw [hif t J.fp (hnz0 hnz) (hsome (hc.pc od t ht) hdv) (hsome hq hfv)]
    refine ⟨t, J.fp, _, rfl, hm.trans (.single hm''), (h.track.moves (hm.trans (.single hm''))),
      Linked.push h.linked (hI''.trans hI) ha'' rfl (htJ ▸ atPc_enter hP hfJ) ?_ (memOf_of hk1)⟩
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
      obtain ⟨hfp0, kfp, hkfp, hq, hk0, hk1⟩ := hc.tail _ vs0 hw0 e'.nc _ of
        (by rw [← hfull]; exact calls_at hcalls) rfl
        (by rw [← hfull, calls_append', hcalls, hnil, Ent.nc, List.length_append]; rfl) hnx
      rw [← hI, hkf] at hkfp
      obtain rfl := Option.some.inj hkfp
      have hmv : Move P rd Is (D, e' :: st) (D, Ent.enter P J fn :: st) :=
        .tail (hp.trans (Zip.pos_head hzc)) h0' ⟨as2, fun a ha ↦ flowAtom_pops (has2 a ha), hpos2⟩ hJ hk hkf hfJ
      rw [hif t J.fp h0 (hsome (hc.pc od t ht) hdv) (hsome hq hfv)]
      rcases st with _ | ⟨e2, st2⟩
      · exact absurd h.linked.2.1 hfp0
      refine ⟨t, J.fp, _, rfl, hm.trans (.single hmv), h.track.moves (hm.trans (.single hmv)),
        Linked.tail h.linked rfl (htJ ▸ atPc_enter hP hfJ) ?_ ?_⟩
      · exact congrArg (·.getD 0) hk0
      · exact congrArg (·.getD 0) hk1
    · obtain ⟨kfp, hkfp, hq, hk0, hk1, -⟩ := hc.site _ vs0 hw0 e'.nc _ of s
        (by rw [← hfull]; exact calls_at hcalls) rfl hs
      rw [← hI, hkf] at hkfp
      obtain rfl := Option.some.inj hkfp
      obtain ⟨e'', hm'', hI'', -, -, ha''⟩ := atPc_callIf (P := P) (rd := rd) (Is := Is) hent hal hp hzc h0' hca
        (h1 _ rfl) hJ hk hkf hfJ D st
      rw [hif t J.fp h0 (hsome (hc.pc od t ht) hdv) (hsome hq hfv)]
      refine ⟨t, J.fp, _, rfl, hm.trans (.single hm''), (h.track.moves (hm.trans (.single hm''))),
        Linked.push h.linked (hI''.trans hI) ha'' rfl (htJ ▸ atPc_enter hP hfJ) ?_ (memOf_of hk1)⟩
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
    refine ⟨_, J.fp, _, rfl, hm.trans (.single hm''), (h.track.moves (hm.trans (.single hm''))),
      Linked.push h.linked (hI''.trans hI) ha'' rfl (atPc_enter hP hfJ) ?_ (memOf_of hk1)⟩
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
      exact ⟨r0, e2.I.fp, _, rfl, hm.trans (.single hmv), h.track.moves (hm.trans (.single hmv)), hl⟩
    · rw [hmain] at hm0
      simp only [↓reduceIte] at hm0
      obtain ⟨hself, ht⟩ := hm0
      have hfp0 := hc.main hmain
      exfalso
      apply hne'
      rw [hif X.halt e.I.fp (hnz0 hnz) (hsome (hc.pc od _ ht) hdv) (hsome (hc.self of hself) hfv), hfp0]
      exact hP.halt _ _ hE.find hmain

end

end LeanVM.Guest.Bridge
