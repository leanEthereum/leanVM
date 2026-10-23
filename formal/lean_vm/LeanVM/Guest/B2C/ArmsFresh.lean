/-
  LeanVM.Guest.B2C.ArmsFresh

  No table selector is a temporary of its function, so checker K's `keep` holds outright.
-/

module

public import LeanVM.Guest.B2C.KRetemp
public import LeanVM.Guest.B2C.Temps1617

/-!
# The table selectors are not temporaries

Only compiled functions `17` and `18` (core functions `16`, `17`) have table jumps
(`armsCheck`, by the kernel over `Data.plumbs`), and their selectors are not among those
functions' temporaries, whose indices the freshness certificates list (`temps16`, `temps17`, by
`tmps16`, `tmps17`). So `ArmsFresh` holds (`armsFresh`), and with it `keep` (`kfacts_keep_all`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- Every arm `a` of the plumbs `l`, the first of index `k`, passes `q`. -/
def armsCheck (q : ℕ → ℕ × ℕ × ℕ → Bool) : List Plumb → ℕ → Bool
  | [], _ => true
  | p :: ps, k => p.arms.all (q k) && armsCheck q ps (k + 1)

theorem armsCheck_spec {q : ℕ → ℕ × ℕ × ℕ → Bool} : ∀ {l : List Plumb} {k : ℕ},
    armsCheck q l k = true → ∀ j, ∀ a ∈ (nth l j {}).arms, q (j + k) a = true
  | [], _, _, j, a, ha => by cases j <;> simp [nth] at ha
  | p :: ps, k, h, j, a, ha => by
    simp only [armsCheck, Bool.and_eq_true, List.all_eq_true] at h
    cases j with
    | zero => simpa using h.1 a ha
    | succ j =>
      have := armsCheck_spec h.2 j a ha
      rwa [show j + (k + 1) = j + 1 + k by omega] at this

/-- The arms' check: only functions `17`, `18` have arms, none at a temporary. -/
def armOk (k : ℕ) (a : ℕ × ℕ × ℕ) : Bool :=
  (k == 17 && !temps16.contains a.1) || (k == 18 && !temps17.contains a.1)

theorem armsCheck_plumbs : armsCheck armOk Data.plumbs 0 = true := by decide +kernel

private theorem not_tmp {body : List Stmt} {ts : List ℕ} (h : (Stmt.tmpsList body).map V.idx = ts)
    {x : ℕ} (hx : ts.contains x = false) : V.n x ∉ Stmt.tmpsList body := fun hm ↦ by
  have : x ∈ ts := h ▸ List.mem_map_of_mem (f := V.idx) hm
  simp [this] at hx

/-- **No table selector is a temporary of its function.** -/
theorem armsFresh : ArmsFresh := by
  intro j a ha
  have h := armsCheck_spec armsCheck_plumbs j a ha
  simp only [armOk, Nat.add_zero, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at h
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact not_tmp (show (Stmt.tmpsList (coreOf 17).body).map V.idx = temps16 from tmps16) h
  · exact not_tmp (show (Stmt.tmpsList (coreOf 18).body).map V.idx = temps17 from tmps17) h

/-- **Checker K's `keep`**, outright. -/
theorem kfacts_keep_all (hdr : E × E) (T : Tree) :
    ∀ ν, ∀ I ∈ honestInsts coreProgram fs H hdr T,
      ∀ I' ∈ honestInsts coreProgram fs H hdr (T.retemp coreProgram fs ν 0),
        I'.fp = I.fp → I'.t = I.t.retemp coreProgram fs ν I.fp → ∀ q ∈ I'.cells C,
          ¬ TmpOff coreProgram cert I.t q.1 → q ∈ I.cells C :=
  kfacts_keep armsFresh hdr T

end
end LeanVM.Guest.B2C
