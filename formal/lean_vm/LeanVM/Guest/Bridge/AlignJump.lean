/-
  LeanVM.Guest.Bridge.AlignJump

  The alignment's jumps read by the tree track: at a branch, a table jump, a call site, a conditional call or a return, the frame's move on the side its path takes lands where the alignment puts that side.
-/

module

public import LeanVM.Guest.Bridge.AlignTrack

/-!
# The alignment's jumps and the tree track

The checks a jump passed (`ite_step`, `call_step`, `callIf_step`, `ret_step`: what `headStep` accepted at each head), and the frame's move there (`atPc_ite`, `atPc_arm`, `atPc_call`, `atPc_skip`, `atPc_callIf`): a frame at the position the jump steps from (as `atPc_step` leaves it) moves by its path's statement to a frame at the pc of the side it takes, its offset's position the side's normalized (`atPc_of_norm`: the atoms the normalization skips pop nothing). Which side the run takes is the jump's semantics, left to the caller: the branch's cell holds `σ c`, the table jump's selector the arm, the call's destination its callee's entry.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Check (getF)

public section

theorem flowAtom_pops {a : Atom} (h : flowAtom a = false) (rd : Reader) (σ : Val) : a.pops rd σ = [] := by
  cases a
  case hint hc => cases hc <;> simp_all [flowAtom, coreFlow, Atom.pops, Core.Hint.pops]
  all_goals rfl

variable {X : AlignCtx} {body : List Stmt} {code : List OffsetInstruction}
  {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} {ent : String → ℕ} {al : String → ℕ → Option (List Stmt)}

/-- **A frame at a position the normalization takes to an aligned one is at its offset.** -/
theorem atPc_of_norm {e : Ent} (hent : ent e.I.t.name = X.entry)
    (hal : ∀ off, al e.I.t.name off = alignAt X body code d off) {w c : Zip} (hn : normZ X.fuel w = some c)
    (hp : e.pos = w.pos) {o : ℕ} (ho : alignAt X body code d o = some c.pos) : AtPc ent al e (X.entry + o) := by
  obtain ⟨as, has, hpos, -⟩ := normZ_pos _ hn
  exact ⟨o, by rw [hent], c.pos, by rw [hal]; exact ho, as, fun a ha ↦ flowAtom_pops (has a ha), by rw [hp, hpos]⟩

theorem Zip.pos_head {z : Zip} {s : Stmt} {ss : List Stmt} (hz : z.cur = s :: ss) :
    z.pos = s :: (z.next ss).pos := by
  rw [Zip.next_eq]
  simp [Zip.pos, hz]

theorem Zip.enter_pos (z : Zip) (s : Stmt) (ss : List Stmt) (c : ℕ) :
    (z.enter s ss c).pos = subBlock s c ++ (z.next ss).pos := by
  rw [Zip.next_eq]
  simp [Zip.pos, Zip.enter]

/-! ## What a jump passed -/

/-- A branch's jump: on the branch's cell, the fall-through the zero side, the target the other. -/
theorem ite_step {i oc od of : ℕ} {tabs : List (ℕ × Zip × ℕ)} {z : Zip} {c : V} {zb nb ss : List Stmt}
    {r : Option Zip × List (ℕ × Zip)} (hr : insStep X i (.jump oc od of) tabs z = some r)
    (hz : z.cur = .ite c zb nb :: ss) (hzero : X.zeroAt oc = false) (hfwd : fwdJ X i oc od of = false) :
    X.locAt c.idx = oc ∧ X.selfAt of = true ∧ ∃ t cz cn o, X.pcAt od = some t ∧
      normZ X.fuel (z.enter (.ite c zb nb) ss 0) = some cz ∧ normZ X.fuel (z.enter (.ite c zb nb) ss 1) = some cn ∧
      X.fwdOff i t = some o ∧ r = (some cz, [(o, cn)]) := by
  simp only [insStep, jumpStep, hzero, hfwd, Bool.cond_false, headStep, hz] at hr
  cases hb : (Nat.beq (X.locAt c.idx) oc && X.selfAt of) <;> simp only [hb, Bool.cond_true, Bool.cond_false] at hr
  · cases hr
  simp only [Bool.and_eq_true, Nat.beq_eq] at hb
  refine ⟨hb.1, hb.2, ?_⟩
  split at hr
  · rename_i t cz cn ht hcz hcn
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hr
    exact ⟨t, cz, cn, o, ht, hcz, hcn, ho, rfl⟩
  · cases hr

/-- A call site: the callee's entry the destination, the rest at the site's return pc. -/
theorem call_step {i oc od of : ℕ} {tabs : List (ℕ × Zip × ℕ)} {z : Zip} {f : String} {args rets : List V}
    {ss : List Stmt} {r : Option Zip × List (ℕ × Zip)} (hr : insStep X i (.jump oc od of) tabs z = some r)
    (hz : z.cur = .call f args rets :: ss) (hzero : X.zeroAt oc = false) (hfwd : fwdJ X i oc od of = false) :
    X.nzAt oc = true ∧ ∃ s t c o, X.siteAt of args rets = some s ∧ X.pcAt od = some t ∧ X.entOk t f = true ∧
      normZ X.fuel (z.next ss) = some c ∧ X.fwdOff i s.r = some o ∧ r = (none, [(o, c)]) := by
  simp only [insStep, jumpStep, hzero, hfwd, Bool.cond_false, headStep, hz] at hr
  split at hr
  · rename_i s t c hs ht hc
    cases he : (X.nzAt oc && X.entOk t f) <;> simp only [he, Bool.cond_true, Bool.cond_false] at hr
    · cases hr
    simp only [Bool.and_eq_true] at he
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hr
    exact ⟨he.1, s, t, c, o, hs, ht, he.2, hc, ho, rfl⟩
  · cases hr

/-- A conditional call: on its condition's cell, the callee's entry the destination, the rest falling
through, either at a site returning to the next offset or a loop's tail call before the closing
`ret []`. -/
theorem callIf_step {i oc od of : ℕ} {tabs : List (ℕ × Zip × ℕ)} {z : Zip} {c : V} {f : String} {args : List V}
    {ss : List Stmt} {r : Option Zip × List (ℕ × Zip)} (hr : insStep X i (.jump oc od of) tabs z = some r)
    (hz : z.cur = .callIf c f args :: ss) (hzero : X.zeroAt oc = false) (hfwd : fwdJ X i oc od of = false) :
    X.locAt c.idx = oc ∧ ∃ t ca, X.pcAt od = some t ∧ X.entOk t f = true ∧ normZ X.fuel (z.next ss) = some ca ∧
      r = (some ca, []) ∧ ((X.nextAt of = true ∧ retNil ca.pos = true) ∨
        (X.nextAt of = false ∧ ∃ s, X.siteAt of args [] = some s ∧ s.r = X.entry + i + 1)) := by
  simp only [insStep, jumpStep, hzero, hfwd, Bool.cond_false, headStep, hz] at hr
  cases hb : Nat.beq (X.locAt c.idx) oc <;> simp only [hb, Bool.cond_true, Bool.cond_false] at hr
  · cases hr
  refine ⟨Nat.beq_eq.mp hb, ?_⟩
  split at hr
  · rename_i t ca ht hca
    cases he : X.entOk t f <;> simp only [he, Bool.cond_true, Bool.cond_false] at hr
    · cases hr
    cases hn : X.nextAt of <;> simp only [hn, Bool.cond_true, Bool.cond_false] at hr
    · split at hr
      · rename_i s hs
        cases hsr : Nat.beq s.r (X.entry + i + 1) <;> simp only [hsr, Bool.cond_true, Bool.cond_false] at hr
        · cases hr
        cases hr
        exact ⟨t, ca, ht, he, hca, rfl, Or.inr ⟨rfl, s, hs, Nat.beq_eq.mp hsr⟩⟩
      · cases hr
    · cases hrn : retNil ca.pos <;> simp only [hrn, Bool.cond_true, Bool.cond_false] at hr
      · cases hr
      cases hr
      exact ⟨t, ca, ht, he, hca, rfl, Or.inl ⟨rfl, hrn⟩⟩
  · cases hr

/-- A return: `main`'s the halting jump, any other's `od = 0`, `of = 1`; nothing falls through. -/
theorem ret_step {i oc od of : ℕ} {tabs : List (ℕ × Zip × ℕ)} {z : Zip} {vs : List V} {ss : List Stmt}
    {r : Option Zip × List (ℕ × Zip)} (hr : insStep X i (.jump oc od of) tabs z = some r)
    (hz : z.cur = .ret vs :: ss) (hzero : X.zeroAt oc = false) (hfwd : fwdJ X i oc od of = false) :
    r = (none, []) ∧ X.nzAt oc = true ∧
      (if X.main then X.selfAt of = true ∧ X.pcAt od = some X.halt else od = 0 ∧ of = 1) := by
  simp only [insStep, jumpStep, hzero, hfwd, Bool.cond_false, headStep, hz] at hr
  cases hm : X.main <;> simp only [hm, Bool.cond_true, Bool.cond_false] at hr
  · cases hb : (X.nzAt oc && Nat.beq od 0 && Nat.beq of 1) <;> simp only [hb, Bool.cond_true, Bool.cond_false] at hr
    · cases hr
    cases hr
    simp only [Bool.and_eq_true, Nat.beq_eq] at hb
    exact ⟨rfl, hb.1.1, by simpa using hb.1.2, hb.2⟩
  · cases hb : (X.nzAt oc && X.selfAt of && X.pcAt od == some X.halt) <;>
      simp only [hb, Bool.cond_true, Bool.cond_false] at hr
    · cases hr
    cases hr
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    exact ⟨rfl, hb.1.1, by simpa using ⟨hb.1.2, hb.2⟩⟩

/-- A dispatch: on a nonzero constant, its site's target cell the destination, the rest at the site's
return pc. -/
theorem dispatch_step {i oc od of : ℕ} {tabs : List (ℕ × Zip × ℕ)} {z : Zip} {x : V} {fs : List String}
    {args rets : List V} {ss : List Stmt} {r : Option Zip × List (ℕ × Zip)}
    (hr : insStep X i (.jump oc od of) tabs z = some r) (hz : z.cur = .dispatch x fs args rets :: ss)
    (hzero : X.zeroAt oc = false) (hfwd : fwdJ X i oc od of = false) :
    X.nzAt oc = true ∧ od ≠ 0 ∧ ∃ s c o, X.siteAt of args rets = some s ∧ s.tgt = od ∧
      normZ X.fuel (z.next ss) = some c ∧ X.fwdOff i s.r = some o ∧ r = (none, [(o, c)]) := by
  simp only [insStep, jumpStep, hzero, hfwd, Bool.cond_false, headStep, hz] at hr
  split at hr
  · rename_i s c hs hc
    cases he : (X.nzAt oc && Nat.beq s.tgt od && !Nat.beq od 0) <;>
      simp only [he, Bool.cond_true, Bool.cond_false] at hr
    · cases hr
    simp only [Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at he
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hr
    exact ⟨he.1.1, fun h0 ↦ by simp [h0] at he, s, c, o, hs, he.1.2, hc, ho, rfl⟩
  · cases hr

/-! ## The frame's move on the side its path takes -/

variable {P : Core.Program} {rd : Reader} {Is : List Inst}

/-- **A branch**: the frame takes the side its valuation picks, at the fall-through pc on zero, at
the target otherwise. -/
theorem atPc_ite {e : Ent} (hent : ent e.I.t.name = X.entry) (hal : ∀ off, al e.I.t.name off = alignAt X body code d off)
    {i : ℕ} {z : Zip} {c : V} {zb nb ss : List Stmt} (hp : e.pos = z.pos) (hz : z.cur = .ite c zb nb :: ss)
    {cz cn : Zip} {o : ℕ} (hcz : normZ X.fuel (z.enter (.ite c zb nb) ss 0) = some cz)
    (hcn : normZ X.fuel (z.enter (.ite c zb nb) ss 1) = some cn)
    (h1 : alignAt X body code d (i + 1) = some cz.pos) (h2 : alignAt X body code d o = some cn.pos)
    (done : List Pop) (st : List Ent) :
    ∃ e', Move P rd Is (done, e :: st) (done, e' :: st) ∧ e'.I = e.I ∧ e'.fn = e.fn ∧ e'.nb = e.nb ∧
      AtPc ent al e' (if e.σ c = 0 then X.entry + (i + 1) else X.entry + o) := by
  have hpos : e.pos = .ite c zb nb :: (z.next ss).pos := hp.trans (Zip.pos_head hz)
  refine ⟨_, .ite hpos, rfl, rfl, rfl, ?_⟩
  by_cases h0 : e.σ c = 0
  · simp only [h0, ↓reduceIte]
    exact atPc_of_norm (e := e.adv (zb ++ (z.next ss).pos) 1) hent hal hcz (by rw [Zip.enter_pos]; rfl) h1
  · simp only [h0, ↓reduceIte]
    exact atPc_of_norm (e := e.adv (nb ++ (z.next ss).pos) 1) hent hal hcn (by rw [Zip.enter_pos]; rfl) h2

/-- **A table jump**: the frame takes the arm its path takes, at that arm's target. -/
theorem atPc_arm {e : Ent} (hent : ent e.I.t.name = X.entry) (hal : ∀ off, al e.I.t.name off = alignAt X body code d off)
    {z : Zip} {x : V} {arms : List (List Stmt)} {ss : List Stmt} (hp : e.pos = z.pos) (hz : z.cur = .match_ x arms :: ss)
    {k : ℕ} (hk : k < arms.length) (hw : walkArms e.σ x 0 arms = walk e.σ arms[k]) {c' : Zip} {t : ℕ}
    (hc : normZ X.fuel (z.enter (.match_ x arms) ss k) = some c')
    (ht : alignAt X body code d (t - X.entry) = some c'.pos) (done : List Pop) (st : List Ent) :
    ∃ e', Move P rd Is (done, e :: st) (done, e' :: st) ∧ e'.I = e.I ∧ e'.fn = e.fn ∧ e'.nb = e.nb ∧
      AtPc ent al e' (X.entry + (t - X.entry)) := by
  have hpos : e.pos = .match_ x arms :: (z.next ss).pos := hp.trans (Zip.pos_head hz)
  refine ⟨_, .arm hk hpos hw, rfl, rfl, rfl,
    atPc_of_norm (e := e.adv (arms[k] ++ (z.next ss).pos) 0) hent hal hc ?_ ht⟩
  rw [Zip.enter_pos]
  simp [Ent.adv, subBlock, List.getD_eq_getElem?_getD, hk]

/-- **A call**: the callee entered, the caller at the site's return pc. -/
theorem atPc_call {e : Ent} (hent : ent e.I.t.name = X.entry) (hal : ∀ off, al e.I.t.name off = alignAt X body code d off)
    {z : Zip} {f : String} {args rets : List V} {ss : List Stmt} (hp : e.pos = z.pos) (hz : z.cur = .call f args rets :: ss)
    {c : Zip} {o : ℕ} (hc : normZ X.fuel (z.next ss) = some c) (ho : alignAt X body code d o = some c.pos)
    {J : Inst} {fn : Fn} (hJ : J ∈ Is) (hk : e.I.t.kids[e.nc]? = some J.t) (hkf : e.I.kidFps[e.nc]? = some J.fp)
    (hf : P.find? J.t.name = some fn) (done : List Pop) (st : List Ent) :
    ∃ e', Move P rd Is (done, e :: st) (done, Ent.enter P J fn :: e' :: st) ∧ e'.I = e.I ∧ e'.fn = e.fn ∧
      e'.nb = e.nb ∧ AtPc ent al e' (X.entry + o) :=
  ⟨_, .call (hp.trans (Zip.pos_head hz)) hJ hk hkf hf, rfl, rfl, rfl,
    atPc_of_norm (e := e.adv (z.next ss).pos 1) hent hal hc rfl ho⟩

/-- **A conditional call not taken**: a phantom, the frame at the next pc. -/
theorem atPc_skip {e : Ent} (hent : ent e.I.t.name = X.entry) (hal : ∀ off, al e.I.t.name off = alignAt X body code d off)
    {i : ℕ} {z : Zip} {c : V} {f : String} {args : List V} {ss : List Stmt} (hp : e.pos = z.pos)
    (hz : z.cur = .callIf c f args :: ss) (h0 : e.σ c = 0) {ca : Zip} (hca : normZ X.fuel (z.next ss) = some ca)
    (h1 : alignAt X body code d (i + 1) = some ca.pos) (done : List Pop) (st : List Ent) :
    ∃ e', Move P rd Is (done, e :: st) (done, e' :: st) ∧ e'.I = e.I ∧ e'.fn = e.fn ∧ e'.nb = e.nb ∧
      AtPc ent al e' (X.entry + (i + 1)) :=
  ⟨_, .skip (hp.trans (Zip.pos_head hz)) h0, rfl, rfl, rfl,
    atPc_of_norm (e := e.adv (z.next ss).pos 2) hent hal hca rfl h1⟩

/-- **A conditional call taken at a site**: the callee entered, the caller at the next pc. -/
theorem atPc_callIf {e : Ent} (hent : ent e.I.t.name = X.entry) (hal : ∀ off, al e.I.t.name off = alignAt X body code d off)
    {i : ℕ} {z : Zip} {c : V} {f : String} {args : List V} {ss : List Stmt} (hp : e.pos = z.pos)
    (hz : z.cur = .callIf c f args :: ss) (h0 : e.σ c ≠ 0) {ca : Zip} (hca : normZ X.fuel (z.next ss) = some ca)
    (h1 : alignAt X body code d (i + 1) = some ca.pos) {J : Inst} {fn : Fn} (hJ : J ∈ Is)
    (hk : e.I.t.kids[e.nc]? = some J.t) (hkf : e.I.kidFps[e.nc]? = some J.fp) (hf : P.find? J.t.name = some fn)
    (done : List Pop) (st : List Ent) :
    ∃ e', Move P rd Is (done, e :: st) (done, Ent.enter P J fn :: e' :: st) ∧ e'.I = e.I ∧ e'.fn = e.fn ∧
      e'.nb = e.nb ∧ AtPc ent al e' (X.entry + (i + 1)) :=
  ⟨_, .callIf (hp.trans (Zip.pos_head hz)) h0 hJ hk hkf hf, rfl, rfl, rfl,
    atPc_of_norm (e := e.adv (z.next ss).pos 2) hent hal hca rfl h1⟩

/-- **A return**: the frame popped. -/
theorem move_ret {e : Ent} {z : Zip} {vs : List V} {ss : List Stmt} (hp : e.pos = z.pos) (hz : z.cur = .ret vs :: ss)
    (done : List Pop) (st : List Ent) : Move P rd Is (done, e :: st) (done, st) :=
  .ret (hp.trans (Zip.pos_head hz))

end

end LeanVM.Guest.Bridge
