/-
  LeanVM.Guest.B1.VerifySub.Flat

  `verify_sub`'s body as a conjunction: every statement before its final `ret []` holds, each found
  by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.VerifySub.Phases
import LeanVM.Guest.CoreLemmas

/-!
# The body, flat

`verify_sub`'s body is `vsPre ++ [.ret []]`, `vsPre` without a `ret` (`vs_body_eq`,
`vsPre_noRet`, by kernel evaluation): a run returns nothing and holds every statement of `vsPre`
(`VsRun.flat`). A statement is found in `vsPre` by `membB` (`stmtEqb`, evaluated by the kernel):
an atom holds (`VsRun.atom`), a call is in the call relation (`VsRun.call`), a dispatch holds
(`VsRun.dispatch`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `verify_sub`'s body before its final `ret []`. -/
noncomputable def vsPre : List Stmt := (Fn.body fn% «verify_sub»).take 4222

theorem vs_body_eq : Fn.body fn% «verify_sub» = vsPre ++ [.ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem vsPre_noRet : Stmt.noRetList vsPre = true := by decide +kernel

/-- A statement found in a list, by `stmtEqb`. -/
def membB (s : Stmt) (l : List Stmt) : Bool := l.any (stmtEqb s)

theorem membB_sound {s : Stmt} {l : List Stmt} (h : membB s l = true) : s ∈ l := by
  obtain ⟨t, ht, he⟩ := List.any_eq_true.mp h
  rwa [stmtEqb_sound he]

theorem holds_of_noRetList {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} :
    ∀ (l : List Stmt), Stmt.noRetList l = true → Stmt.HoldsList C rd σ l True kret →
      ∀ s ∈ l, Stmt.Holds C rd σ s True kret
  | [], _, _, _, hs => absurd hs (by simp)
  | t :: l, hn, h, s, hs => by
    simp only [Stmt.noRetList, Bool.and_eq_true] at hn
    simp only [Stmt.HoldsList] at h
    rw [holds_noRet t hn.1] at h
    rcases List.mem_cons.mp hs with rfl | hs
    · exact h.1
    · exact holds_of_noRetList l hn.2 h.2 s hs

variable {bytecode : List K} {κ : ℕ} {L : MemoryImage κ} {C : CallRel} {Vm : FrameMap} {σ : Val}
  {rets : List E}

/-- **The body, flat**: a run returns nothing and holds every statement before its `ret`. -/
theorem VsRun.flat (R : VsRun bytecode L C Vm σ rets) :
    rets = [] ∧ ∀ s ∈ vsPre, Stmt.Holds C L.read σ s True (fun rs ↦ rs = rets) := by
  have hb := R.hb
  rw [vs_body_eq, holdsList_append, holdsList_noRet _ vsPre_noRet] at hb
  refine ⟨?_, holds_of_noRetList vsPre vsPre_noRet hb.1⟩
  have h2 := hb.2
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_nil] at h2
  exact h2.symm

theorem VsRun.atom (R : VsRun bytecode L C Vm σ rets) {a : Atom}
    (hm : membB (.atom a) vsPre = true) : a.Holds L.read σ := by
  have := R.flat.2 _ (membB_sound hm)
  simp only [Stmt.Holds] at this
  exact this.1

theorem VsRun.call (R : VsRun bytecode L C Vm σ rets) {f : String} {args rs : List V}
    (hm : membB (.call f args rs) vsPre = true) : C f (args.map σ) (rs.map σ) := by
  have := R.flat.2 _ (membB_sound hm)
  simp only [Stmt.Holds] at this
  exact this.1

theorem VsRun.dispatch (R : VsRun bytecode L C Vm σ rets) {x : V} {fs : List String}
    {args rs : List V} (hm : membB (.dispatch x fs args rs) vsPre = true) :
    Stmt.Holds C L.read σ (.dispatch x fs args rs) True (fun rs ↦ rs = rets) :=
  R.flat.2 _ (membB_sound hm)

theorem noRet_of_mem : ∀ {l : List Stmt}, Stmt.noRetList l = true → ∀ s ∈ l, Stmt.noRet s = true
  | [], _, _, hs => absurd hs (by simp)
  | t :: l, hn, s, hs => by
    simp only [Stmt.noRetList, Bool.and_eq_true] at hn
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hn.1
    · exact noRet_of_mem hn.2 s hs

theorem holdsList_of_forall {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} :
    ∀ (l : List Stmt), (∀ s ∈ l, Stmt.noRet s = true ∧ Stmt.Holds C rd σ s True kret) →
      Stmt.HoldsList C rd σ l True kret
  | [], _ => trivial
  | t :: l, h => by
    simp only [Stmt.HoldsList]
    rw [holds_noRet t (h t (by simp)).1]
    exact ⟨(h t (by simp)).2, holdsList_of_forall l fun s hs ↦ h s (by simp [hs])⟩

/-- **A slice of the body holds**: statements `a .. a + n` of `vsPre`, given as a template `T`
(checked against the body by the kernel, `stmtsEqb`). -/
theorem VsRun.slice (R : VsRun bytecode L C Vm σ rets) {a n : ℕ} {T : List Stmt}
    (hT : (vsPre.drop a).take n = T) : Stmt.HoldsList C L.read σ T True (fun rs ↦ rs = rets) := by
  subst hT
  refine holdsList_of_forall _ fun s hs ↦ ?_
  have hs' : s ∈ vsPre := List.mem_of_mem_drop (List.mem_of_mem_take hs)
  exact ⟨noRet_of_mem vsPre_noRet s hs', R.flat.2 s hs'⟩

/-- **A statement of a slice of the body holds.** -/
theorem VsRun.mem_slice (R : VsRun bytecode L C Vm σ rets) {a n : ℕ} {T : List Stmt}
    (hT : (vsPre.drop a).take n = T) {s : Stmt} (hs : s ∈ T) :
    Stmt.Holds C L.read σ s True (fun rs ↦ rs = rets) := by
  subst hT
  exact R.flat.2 s (List.mem_of_mem_drop (List.mem_of_mem_take hs))

theorem VsRun.atom_in (R : VsRun bytecode L C Vm σ rets) {a n : ℕ} {T : List Stmt}
    (hT : (vsPre.drop a).take n = T) {x : Atom} (hs : Stmt.atom x ∈ T) : x.Holds L.read σ := by
  have := R.mem_slice hT hs
  simp only [Stmt.Holds] at this
  exact this.1

theorem VsRun.call_in (R : VsRun bytecode L C Vm σ rets) {a n : ℕ} {T : List Stmt}
    (hT : (vsPre.drop a).take n = T) {f : String} {args rs : List V} (hs : Stmt.call f args rs ∈ T) :
    C f (args.map σ) (rs.map σ) := by
  have := R.mem_slice hT hs
  simp only [Stmt.Holds] at this
  exact this.1

/-- A load found in the body. -/
theorem VsRun.load (R : VsRun bytecode L C Vm σ rets) {d p : ℕ} {off : ℕ}
    (hm : membB (.atom (.load (.n d) (.n p) off)) vsPre = true) :
    LoadHolds L.read (σ (.n p)) off (σ (.n d)) := R.atom hm

end
end LeanVM.Guest.B1.VerifySub
