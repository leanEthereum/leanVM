/-
  LeanVM.Guest.EndExecChain

  The chained `match`es' arms on the track, when each chain's arms jump through one target cell.
-/

module

public import LeanVM.Guest.EndExecXTrace
public import LeanVM.Guest.Bridge.JumpCellsDeployed
public import LeanVM.Guest.B2C.B2Final
import LeanVM.Guest.B2C.ArmsFresh
import LeanVM.Guest.StmtsAppend

/-!
# The chained `match`es' arms, one target cell per chain

`ChainArmAt`: the chained `match`es' arms (`Bridge.ChainArm`) on every node's reference run, only `main_loop2`'s. `ChainArm` asks, at a state of the track whose top frame is at a jump reading a chained target cell `od`, that the arm the previous selector took jump through `od`. The track does not know which arm a code offset belongs to: every arm's closing jump has one aligned position, the chain's next `match`. So it holds at every state of the track only when each chain's arms jump through one cell (`chainOneB`): then any arm the path takes will do. `chainArm_of_one`: from that check, `ChainArm`, the arm being the one the selector picks (the chained `match` a top-level statement of a body without an early `ret`, `lastBody`, so the path's walk passes it, `walkArms_sel`). The compiler gives each chained `match` one target cell for all its arms, so the check holds (`chainOneB_true`, by the kernel over `Data.plumbs`), and with it `ChainArmAt` (`chainArmAt`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Bridge
open LeanVM.Guest.B2C

public section

/-- **The chained `match`es' arms on every node's reference run.** -/
@[expose] def ChainArmAt : Prop :=
  ∀ r : Ref, r.Ok → ChainArm r.rd0 (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) r.T (memOf r.img) alignA

/-- **Each chain's arms jump through one target cell.** -/
@[expose] noncomputable def chainOneB : Bool :=
  (List.range nFns).all fun j ↦ (plumbOf j).chains.all fun ch ↦ ch.2.2.1.all fun t ↦ t == ch.2.2.1.headD 0

/-- A chain's arms jump through one target cell. -/
private def chainOneOk (_ : ℕ) (ch : ℕ × ℕ × List ℕ × ℕ × ℕ) : Bool := ch.2.2.1.all fun t ↦ t == ch.2.2.1.headD 0

private theorem chainsCheck_one : chainsCheck chainOneOk Data.plumbs 0 = true := by decide +kernel

theorem chainOneB_true : chainOneB = true :=
  List.all_eq_true.mpr fun j _ ↦ List.all_eq_true.mpr fun ch hch ↦ chainsCheck_spec chainsCheck_one j ch hch

/-- A path through a top-level `match` of a body without an early `ret` takes an arm. -/
theorem walk_takes {σ : Val} {body : List Stmt} {es : List Ev} {vs : List V} {p : ℕ} {x : V}
    {arms : List (List Stmt)} (hl : lastOkC body = true) (hw : walk σ body = .ret es vs)
    (hp : body[p]? = some (.match_ x arms)) : ∃ k < arms.length, σ x = ofK (addressOfIndex k) := by
  have hnr := lastOkC_take hl hp (fun vs h ↦ by cases h)
  have htake : body.take (p + 1) = body.take p ⧺ [.match_ x arms] := by
    rw [List.take_add_one, hp]; rfl
  rw [← List.take_append_drop (p + 1) body, walk_appendC] at hw
  rcases walk_noRetC _ hnr with ⟨es1, h1⟩ | h1 <;> rw [h1] at hw
  · have hns : walkArms σ x 0 arms ≠ .stuck := fun h ↦ by
      rw [htake, walk_appendC] at h1
      simp only [walk, walk1, h] at h1
      rcases hq : walk σ (body.take p) <;> rw [hq] at h1 <;> simp [Out.seq, Out.pre] at h1
    simpa using walkArms_sel arms 0 hns
  · simp [Out.seq] at hw

/-- **The chained `match`es' arms**, each chain's arms jumping through one target cell. -/
theorem chainArm_of_one (h1 : chainOneB = true) {rd : Reader} {Is : List Inst} {T : Tree} {M : ℕ → E}
    {A : String → FnAl} : ChainArm rd Is T M A := by
  intro pc fp done e st h j hj off oc od of _ _ ch hch hod
  have hE := h.track.ents e List.mem_cons_self
  obtain ⟨i, rfl, hi, hn, hfind, hcore, hfs, hcert, hj1, hjn⟩ := fn_of_idx hj
  have hfn : e.fn = coreOf (i + 1) := by
    have := hE.find
    rw [hfind] at this
    rw [hcore]; exact (Option.some.inj this).symm
  obtain ⟨vs, hw, -⟩ := hE.path
  rw [hfn] at hw
  have hc := (Chained.chainOk_all _ hj1 hjn).1
  simp only [chainFn, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨-, hm⟩ := hc.2 ch hch
  split at hm
  · rename_i x arms y arms' hp _
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq] at hm
    obtain ⟨⟨⟨hx, -⟩, hlen⟩, -⟩ := hm
    subst hx
    obtain ⟨k, hk, hσ⟩ := walk_takes (lastBody (Cplw.cplOk_all _ hj1 hjn) (End.winOk_of hj1 hjn)) hw hp
    have hkt : k < ch.2.2.1.length := hlen ▸ hk
    refine ⟨k, ?_, hσ⟩
    have hone := List.all_eq_true.mp h1 _ (List.mem_range.mpr hjn)
    have hch' := List.all_eq_true.mp (List.all_eq_true.mp hone ch hch)
    rw [List.getElem?_eq_getElem hkt, beq_iff_eq.mp (hch' _ (List.getElem_mem hkt)),
      beq_iff_eq.mp (hch' od hod)]
  · cases hm

/-- **The chained `match`es' arms on every node's reference run**, each chain's arms jumping
through one target cell. -/
theorem chainArmAt_of_one (h1 : chainOneB = true) : ChainArmAt := fun _ _ ↦ chainArm_of_one h1

/-- **The chained `match`es' arms on every node's reference run.** -/
theorem chainArmAt : ChainArmAt := chainArmAt_of_one chainOneB_true

end

end LeanVM.Guest.EndExec
