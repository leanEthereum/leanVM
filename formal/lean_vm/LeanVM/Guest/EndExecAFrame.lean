/-
  LeanVM.Guest.EndExecAFrame

  A callee frame's hint and the frame's next call: the reference run walked from the hint to its call
  site's jump (the bus era's `EndExecAFrame.frame_next`, on the aligned track).
-/

module

public import LeanVM.Guest.EndExecAReady
public import LeanVM.Guest.EndExecAAddr

/-!
# The callee frames' next call

A frame hint precedes its call site's jump with no jump between (`frameOk`, `CurFactsX.frame`), so
the reference run from the hint's state falls through to that jump within the frame, past the same
calls (`reach_jumpA`: `stepRule_off`'s `fall`, the run not yet halted, `OnRef`). The step at the
jump, no jump on a constant `0`, through the own frame, a next frame or a return, is a call through
the site the frame hint names (`site_nextA`: `skip` or `push`), and in a loop helper not its last
(`CurHyps.notLast`): `frame_nextA`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Guest.Check (getF)
open LeanVM.Prover.Exec

public section

variable {L : Lay} {D : Ref → RefD} {A : String → FnAl}

/-- The registers of a frame of the track are not the final ones. -/
theorem regs_ne_finalA (hH : HintHyps L D A) {r : Ref} {pc fp : ℕ} {done : List Pop} {e : Ent} {st : List Ent}
    (htr : RefTrack L D A r pc fp (done, e :: st)) : regs pc fp ≠ Registers.final guestProgram := by
  have hE := htr.track.ents e List.mem_cons_self
  have hpc := (entry_of_atPc hH.progAl hH.layout hE htr.linked.top.2).1
  exact fun h ↦ gpow_ne_pcFinal hpc (congrArg Registers.pc h)

/-- From a state of the track on the run, the step and the rest of the run. -/
theorem step_restA (hH : HintHyps L D A) {r : Ref} {pc fp : ℕ} {done : List Pop} {e : Ent} {st : List Ent}
    (htr : RefTrack L D A r pc fp (done, e :: st)) {m : ℕ}
    (hrun : run guestProgram r.img m (regs pc fp) = some (Registers.final guestProgram)) :
    ∃ r1 m', step guestProgram r.img (regs pc fp) = some r1 ∧
      run guestProgram r.img m' r1 = some (Registers.final guestProgram) := by
  have hne := regs_ne_finalA hH htr
  cases m with
  | zero => exact absurd (Option.some.inj hrun) hne
  | succ k =>
    rw [run_succ_of_ne_final hne, Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun
    obtain ⟨r1, h1, h2⟩ := hrun
    exact ⟨r1, k, h1, h2⟩

/-- **A step through an instruction no jump** keeps the frame, past the same calls, at the next pc. -/
theorem reach_nextA (hH : HintHyps L D A) {r : Ref} (hR : RefH L (D r) r) (hr : r.Ok) {pc : ℕ}
    {done : List Pop} {e : Ent} {st : List Ent} (htr : RefTrack L D A r pc e.I.fp (done, e :: st)) {m : ℕ}
    (hrun : run guestProgram r.img m (regs pc e.I.fp) = some (Registers.final guestProgram))
    (hnj : ∀ oc od of, (A e.I.t.name).code[pc - entOf A e.I.t.name]? ≠ some (.jump oc od of)) :
    ∃ done' e' m', e'.I = e.I ∧ e'.nc = e.nc ∧ RefTrack L D A r (pc + 1) e.I.fp (done', e' :: st) ∧
      run guestProgram r.img m' (regs (pc + 1) e.I.fp) = some (Registers.final guestProgram) := by
  obtain ⟨r1, m', hstep, hrest⟩ := step_restA hH htr hrun
  obtain ⟨off, hpc, pc', fp', ⟨done', st'⟩, hr1, hts', hk⟩ :=
    stepRule_off hH.progAl honestA_closed htr (hH.jumpCells r hR hr _ _ _ _ _ htr) hstep
      (.inr fun oc od of h ↦ absurd h (hnj oc od of))
  have hoff : pc - entOf A e.I.t.name = off := by omega
  rw [hoff] at hnj
  cases hk with
  | @fall e' ins hI' hnc' hins hjk =>
    refine ⟨done', e', m', hI', hnc', ?_, ?_⟩
    · rw [hpc]; exact hts'
    · rw [hpc, ← hr1]; exact hrest
  | fwd _ _ hins => exact absurd hins (hnj _ _ _)
  | skip _ _ hins => exact absurd hins (hnj _ _ _)
  | push _ _ hins => exact absurd hins (hnj _ _ _)
  | tail hins => exact absurd hins (hnj _ _ _)
  | ret hins => exact absurd hins (hnj _ _ _)

/-- **The run falls through to the next jump**: from a state of the track at offset `off`, no jump in
`[off, off + k)`, the frame at offset `off + k`, past the same calls. -/
theorem reach_jumpA (hH : HintHyps L D A) {r : Ref} (hR : RefH L (D r) r) (hr : r.Ok) {done : List Pop}
    {e : Ent} {st : List Ent} {off : ℕ} :
    ∀ (k : ℕ) {m : ℕ}, RefTrack L D A r (entOf A e.I.t.name + off) e.I.fp (done, e :: st) →
      run guestProgram r.img m (regs (entOf A e.I.t.name + off) e.I.fp) = some (Registers.final guestProgram) →
      (∀ o, off ≤ o → o < off + k → ∀ oc od of, (A e.I.t.name).code[o]? ≠ some (.jump oc od of)) →
      ∃ done' e' m', e'.I = e.I ∧ e'.nc = e.nc ∧
        RefTrack L D A r (entOf A e.I.t.name + (off + k)) e.I.fp (done', e' :: st) ∧
        run guestProgram r.img m' (regs (entOf A e.I.t.name + (off + k)) e.I.fp) =
          some (Registers.final guestProgram)
  | 0, m, htr, hrun, _ => ⟨done, e, m, rfl, rfl, htr, hrun⟩
  | k + 1, m, htr, hrun, hnj => by
    obtain ⟨d1, e1, m1, hI1, hn1, ht1, hr1⟩ := reach_jumpA hH hR hr k htr hrun fun o h1 h2 ↦ hnj o h1 (by omega)
    have ht1' : RefTrack L D A r (entOf A e1.I.t.name + (off + k)) e1.I.fp (d1, e1 :: st) := by
      rw [hI1]; exact ht1
    obtain ⟨d2, e2, m2, hI2, hn2, ht2, hr2⟩ := reach_nextA hH hR hr ht1' (by rw [hI1]; exact hr1) fun oc od of ↦ by
      rw [hI1, show entOf A e.I.t.name + (off + k) - entOf A e.I.t.name = off + k by omega]
      exact hnj (off + k) (by omega) (by omega) oc od of
    refine ⟨d2, e2, m2, hI2.trans hI1, hn2.trans hn1, ?_, ?_⟩
    · rw [show entOf A e.I.t.name + (off + (k + 1)) = entOf A e.I.t.name + (off + k) + 1 by omega, ← hI1]
      exact ht2
    · rw [show entOf A e.I.t.name + (off + (k + 1)) = entOf A e.I.t.name + (off + k) + 1 by omega, ← hI1]
      exact hr2

/-- **A call site's jump makes the frame's next call** through that site: a jump on no constant `0`,
through no own frame, next frame or return. -/
theorem site_nextA (hH : HintHyps L D A) {r : Ref} (hR : RefH L (D r) r) (hr : r.Ok) {pc : ℕ}
    {done : List Pop} {e : Ent} {st : List Ent} (htr : RefTrack L D A r pc e.I.fp (done, e :: st)) {m : ℕ}
    (hrun : run guestProgram r.img m (regs pc e.I.fp) = some (Registers.final guestProgram)) {oc od q : ℕ}
    (hins : (A e.I.t.name).code[pc - entOf A e.I.t.name]? = some (.jump oc od q))
    (hz : (A e.I.t.name).X.zeroAt oc = false) (hs : (A e.I.t.name).X.selfAt q = false)
    (hn : (A e.I.t.name).X.nextAt q = false) (hr0 : ¬(od = 0 ∧ q = 1)) :
    ∃ c s, (calls (e.pre ++ e.es))[e.nc]? = some c ∧ (A e.I.t.name).X.siteAt q c.args c.rets = some s := by
  obtain ⟨r1, m', hstep, -⟩ := step_restA hH htr hrun
  obtain ⟨off, hpc, pc', fp', ⟨done', st'⟩, -, -, hk⟩ :=
    stepRule_off hH.progAl honestA_closed htr (hH.jumpCells r hR hr _ _ _ _ _ htr) hstep
      (.inr fun oc' od' of' h ↦ by rw [hins] at h; cases h; exact hs)
  have hoff : pc - entOf A e.I.t.name = off := by omega
  rw [hoff] at hins
  have same : ∀ {a b c : ℕ}, (A e.I.t.name).code[off]? = some (.jump a b c) → a = oc ∧ b = od ∧ c = q :=
    fun h ↦ by rw [hins] at h; cases h; exact ⟨rfl, rfl, rfl⟩
  cases hk with
  | @fall e' ins hI' hnc' hins' hjk =>
    obtain rfl : ins = .jump oc od q := Option.some.inj (hins'.symm.trans hins)
    rcases hjk oc od q rfl with h | h
    · rw [hz] at h; cases h
    · rw [hs] at h; cases h
  | fwd _ _ hins' _ hself =>
    obtain ⟨rfl, rfl, rfl⟩ := same hins'
    rw [hs] at hself; cases hself
  | @skip e' oc' od' of' c f σ' _ _ hins' hc _ hsk =>
    obtain ⟨rfl, rfl, rfl⟩ := same hins'
    rcases hsk with ⟨hnx, -⟩ | ⟨s, hs'⟩
    · rw [hn] at hnx; cases hnx
    · exact ⟨c, s, hc, hs'⟩
  | @push e' J fn oc' od' of' c s _ _ hins' hc hs' =>
    obtain ⟨rfl, rfl, rfl⟩ := same hins'
    exact ⟨c, s, hc, hs'⟩
  | tail hins' _ hnx =>
    obtain ⟨rfl, rfl, rfl⟩ := same hins'
    rw [hn] at hnx; cases hnx
  | ret hins' =>
    obtain ⟨rfl, rfl, rfl⟩ := same hins'
    exact absurd ⟨rfl, rfl⟩ hr0

/-- **The full path of a frame**: two frames of one instance have one path. -/
theorem path_eqA {Is : List Inst} {e e' : Ent} (hE : EntOk coreProgram Is e) (hE' : EntOk coreProgram Is e')
    (hI : e'.I = e.I) : e'.pre ++ e'.es = e.pre ++ e.es := by
  obtain ⟨vs, hw, -⟩ := hE.path
  obtain ⟨vs', hw', -⟩ := hE'.path
  have hf : e'.fn = e.fn := by
    have h1 := hE.find
    have h2 := hE'.find
    rw [hI] at h2
    exact Option.some.inj (h2.symm.trans h1)
  have hσ : e'.σ = e.σ := by simp only [Ent.σ, hI]
  rw [hf, hσ, hw] at hw'
  exact (Out.ret.inj hw').1.symm

/-- **A frame hint's next call**: at the hint, the frame's next call is through the site its pointer
names, and is no loop's tail call. -/
theorem frame_nextA (hH : HintHyps L D A) (hC : CurHyps L D A) {r : Ref} {C : Ctx} {e : Ent} {s sx : St}
    {i : ℕ} {h : Hint} {p : ℕ} (hat : HintAtA L D A r C e s sx i h) (hfr : isFrame (A e.I.t.name).X h = true)
    (hp : allocPtr h = some p) :
    ∃ c s0, (calls (e.pre ++ e.es))[e.nc]? = some c ∧ (A e.I.t.name).X.siteAt p c.args c.rets = some s0 ∧
      e.nc < (e.I.t.kidsC coreProgram.loop).length := by
  obtain ⟨done, st, htr, -⟩ := hat.track
  have hR := hat.ref
  have hr := hat.ok
  have hE := htr.track.ents e List.mem_cons_self
  have hne : (C.hints[s.pc]?).getD [] ≠ [] := fun h0 ↦ by have := hat.get; rw [h0] at this; simp at this
  have hoffs := hints_off hH.progAl hH.advAl hat.ctx htr hne
  have hget := hat.get
  rw [hoffs] at hget
  have hfpe : e.I.fp = s.fp := htr.linked.top.1
  have hU := hintsUp_of hH.progAl hE.find
  have hF := hC.facts _ _ hE.find
  set off := s.pc - entOf A e.I.t.name with hoffdef
  have hpcE : s.pc = entOf A e.I.t.name + off := by
    obtain ⟨-, hat'⟩ := htr.linked.top
    obtain ⟨off', hpc', -⟩ := hat'
    show s.pc = entOf A e.I.t.name + (s.pc - entOf A e.I.t.name)
    have : s.pc = entOf A e.I.t.name + off' := hpc'
    omega
  set X := (A e.I.t.name).X
  set d := (A e.I.t.name).d
  set code := (A e.I.t.name).code
  -- the hint among the frame hints, and its call site's jump
  have hpos : (d.2.2.lookup (X.entry + off)).isSome = true := by
    unfold hintsAtOff at hget
    cases hlk : d.2.2.lookup (X.entry + off) with
    | none => rw [hlk] at hget; simp at hget
    | some _ => rfl
  obtain ⟨hs', hlk⟩ := Option.isSome_iff_exists.mp hpos
  have hget'' := hget
  unfold hintsAtOff at hget''
  rw [hlk, Option.getD_some] at hget''
  have hqm : (off, h) ∈ frames X d := by
    unfold frames allocHints hintsOff
    refine List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨_, mem_of_lookup' hlk,
      List.mem_map.mpr ⟨h, List.mem_of_getElem? hget'', ?_⟩⟩, isFrame_ptr hfr⟩, hfr⟩
    rw [hU.1]; simp
  obtain ⟨oc, od, q, hjc, hpq, hz, hsf, hnx, hr0⟩ := frameOk_spec (hF.frame _ hqm)
  obtain rfl : q = p := Option.some.inj (hpq.symm.trans hp)
  -- the run to the jump
  obtain ⟨-, hrun⟩ := hat.onref
  have hrun' : run guestProgram r.img (r.n - s.steps) (regs (entOf A e.I.t.name + off) e.I.fp) =
      some (Registers.final guestProgram) := by rw [← hpcE, hfpe]; exact hrun
  have htr0 : RefTrack L D A r (entOf A e.I.t.name + off) e.I.fp (done, e :: st) := by
    rw [← hpcE, hfpe]; exact htr
  have hge := nextJump_ge (code := code) off
  obtain ⟨d1, e1, m1, hI1, hn1, ht1, hr1⟩ := reach_jumpA hH hR hr (nextJump code off - off) htr0 hrun'
    fun o ho1 ho2 oc' od' of' hc ↦ by
      have := nextJump_not (code := code) hc ho1 (by omega)
      simp [OffsetInstruction.isJump] at this
  rw [show off + (nextJump code off - off) = nextJump code off by omega] at ht1 hr1
  have ht1' : RefTrack L D A r (entOf A e1.I.t.name + nextJump code off) e1.I.fp (d1, e1 :: st) := by
    rw [hI1]; exact ht1
  obtain ⟨c, s0, hc, hsite⟩ := site_nextA hH hR hr ht1' (by rw [hI1]; exact hr1)
    (by rw [hI1, Nat.add_sub_cancel_left]; exact hjc) (by rw [hI1]; exact hz) (by rw [hI1]; exact hsf)
    (by rw [hI1]; exact hnx) hr0
  have hE1 := ht1.track.ents e1 List.mem_cons_self
  rw [path_eqA hE hE1 hI1, hn1] at hc
  rw [hI1] at hsite
  have hlt : e.nc < (calls (e.pre ++ e.es)).length := (List.getElem?_eq_some_iff.mp hc).1
  have hkl : (calls (e.pre ++ e.es)).length = e.I.t.kids.length := by
    obtain ⟨rv, hkv⟩ := hE.kids; exact kidsValid_len' hkv
  obtain ⟨vs, hw, -⟩ := hE.path
  refine ⟨c, s0, hc, hsite, ?_⟩
  rw [kidsC_length']
  split
  · rename_i hl
    have := hC.notLast _ _ hE.find hl _ _ _ hw _ _ hc _ _ hsite
    omega
  · omega

end

end LeanVM.Guest.EndExec
