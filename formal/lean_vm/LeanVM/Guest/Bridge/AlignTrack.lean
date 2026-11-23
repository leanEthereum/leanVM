/-
  LeanVM.Guest.Bridge.AlignTrack

  The alignment read by the tree track: at an offset a frame is at, its hints' atoms are the next moves of the frame, and past a straight-line instruction the frame is at the next offset.
-/

module

public import LeanVM.Guest.Bridge.AlignSound
public import LeanVM.Guest.Bridge.RefTrace

/-!
# The alignment and the tree track

`atPc_step`: a frame at an offset of a function passing `alignOk` (its aligned positions `al` the check's `alignAt`, its entry `ent` the context's) moves past the atoms its offset's hints consume and those that pop nothing, the flow ones compiling the offset's flow hints one for one, to the position its instruction steps from; past a straight-line instruction it is at the next pc.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

public section

variable {P : Core.Program} {rd : Reader} {Is : List Inst}

/-- **A frame at an aligned offset**: it moves past its offset's hints' atoms (the flow ones
compiling the offset's flow hints one for one) and those that pop nothing, to the position its
instruction steps from; past a straight-line instruction it is at the next pc. -/
theorem atPc_step {X : AlignCtx} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hok : alignOk X body code d = true)
    {ent : String → ℕ} {al : String → ℕ → Option (List Stmt)} {e : Ent} {pc : ℕ}
    (hent : ent e.I.t.name = X.entry) (hal : ∀ off, al e.I.t.name off = alignAt X body code d off)
    (hat : AtPc ent al e pc) (done : List Pop) (st : List Ent) :
    ∃ off ins z tabs r, ∃ as : List Atom, pc = X.entry + off ∧ code[off]? = some ins ∧ ZOk body z ∧
      (∃ bs : List Atom, e.pos = bs.map Stmt.atom ++ z.pos) ∧
      List.Forall₂ (Pairs X) (as.filter flowAtom) (((d.2.2.lookup pc).getD []).filter isaFlowHint) ∧
      insStep X off ins tabs z = some r ∧ ∃ e', Relation.ReflTransGen (Move P rd Is) (done, e :: st)
        (done ++ as.flatMap (fun a ↦ a.pops rd e.σ), e' :: st) ∧ e'.I = e.I ∧ e'.fn = e.fn ∧ e'.pos = z.pos ∧
        e'.nb = e.nb ∧ ((∀ oc od of, ins ≠ .jump oc od of) → AtPc ent al e' (pc + 1)) ∧
        (∀ z1 ∈ r.1, alignAt X body code d (off + 1) = some z1.pos) ∧
        (∀ p ∈ r.2, alignAt X body code d p.1 = some p.2.pos) ∧
        ∀ oc od of x arms ss a, ins = .jump oc od of → z.cur = .match_ x arms :: ss → X.zeroAt oc = false →
          fwdJ X off oc od of = false → Check.getF X.arms od = some a →
          ∀ j < arms.length, ∃ t, Check.getF X.jt (a.2 + j) = some t ∧ X.entry + off < t ∧ ∃ c',
            normZ X.fuel (z.enter (.match_ x arms) ss j) = some c' ∧
            alignAt X body code d (t - X.entry) = some c'.pos := by
  obtain ⟨off, hpc, p, hal', as0, hpops, hpos0⟩ := hat
  rw [hal] at hal'
  rw [hent] at hpc
  obtain ⟨ins, z, tabs, r, as, hins, hz, hpos, hpair, -, hr, h1, h2, h3⟩ := alignAt_step hok hal'
  obtain ⟨e', hm, hI, hfn, hp, hnb⟩ := moves_atoms (P := P) (rd := rd) (Is := Is) (as0 ++ as) (done := done)
    (st := st) (ps := z.pos) (by rw [hpos0, hpos, List.map_append, List.append_assoc])
  have h0 : as0.flatMap (fun a ↦ a.pops rd e.σ) = [] :=
    List.flatMap_eq_nil_iff.mpr fun a ha ↦ hpops a ha rd e.σ
  rw [List.flatMap_append, h0, List.nil_append] at hm
  refine ⟨off, ins, z, tabs, r, as, hpc, hins, hz, ⟨as0 ++ as, by rw [hpos0, hpos, List.map_append, List.append_assoc]⟩,
    by rw [hpc]; exact hpair, hr, e', hm, hI, hfn, hp, hnb,
    fun hnj ↦ ?_, h1, h2, h3⟩
  have hr1 : r = (some z, []) := by
    cases ins
    case jump oc' od' of' => exact absurd rfl (hnj oc' od' of')
    all_goals (simp only [insStep, Option.some.injEq] at hr; exact hr.symm)
  refine ⟨off + 1, by rw [hI, hent]; omega, z.pos, ?_, [], by simp, by simp [hp]⟩
  rw [hI, hal]
  exact h1 z (by rw [hr1]; rfl)

end

end LeanVM.Guest.Bridge
