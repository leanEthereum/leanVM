/-
  LeanVM.Guest.B2C.ArmsFresh

  No table selector is a temporary of its function, so the checker's `keep` holds outright.
-/

module

public import LeanVM.Guest.B2C.KRetemp
public import LeanVM.Guest.Memory.GuestFresh

/-!
# The table selectors are not temporaries

The compiled functions with table jumps (`armsCheck`, by the kernel over `Data.plumbs`: at leanVM
`1a379148`, `verify_lean_xmss`, `sp_wots`, the `opening_queries` variants and their window loops)
(and the chained `match`es) have their selectors outside their temporaries: a function's temporaries are the memory
check's list for the large functions (`Data.bigTemps`, by `bigTemps_spec`; `bigTemps`), and computed
from its body for the others (`armTemps`). So `ArmsFresh` holds (`armsFresh`), and with it `keep`
(`kfacts_keep_all`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- Every arm `a` of the plumbs `l`, the first of index `k`, passes `q`. -/
def armsCheck (q : ℕ → ℕ × ℕ × ℕ → Bool) : List Plumb → ℕ → Bool
  | [], _ => true
  | p :: ps, k => p.arms.all (q k) && armsCheck q ps (k + 1)

theorem armsCheck_spec {q : ℕ → ℕ × ℕ × ℕ → Bool} : ∀ {l : List Plumb} {k : ℕ},
    armsCheck q l k = true → ∀ j, ∀ a ∈ (listElementOrDefault l j {}).arms, q (j + k) a = true
  | [], _, _, j, a, ha => by cases j <;> simp [listElementOrDefault] at ha
  | p :: ps, k, h, j, a, ha => by
    simp only [armsCheck, Bool.and_eq_true, List.all_eq_true] at h
    cases j with
    | zero => simpa using h.1 a ha
    | succ j =>
      have := armsCheck_spec h.2 j a ha
      rwa [show j + (k + 1) = j + 1 + k by omega] at this

/-- The large functions' temporaries, from the memory check's data (`Memory/GuestMem/Data.lean`), by
compiled function index (core index `+ 1`). -/
def bigTemps : List (ℕ × List ℕ) :=
  Data.bigTemps.map fun p ↦ (p.1 + 1, p.2)

/-- The entry of index `j`, if any. -/
def tempsFind : List (ℕ × List ℕ) → ℕ → Option (List ℕ)
  | [], _ => none
  | (k, t) :: l, j => if j = k then some t else tempsFind l j

theorem tempsFind_ok {P : ℕ → List ℕ → Prop} : ∀ {l : List (ℕ × List ℕ)},
    (∀ p ∈ l, P p.1 p.2) → ∀ {j : ℕ} {t : List ℕ}, tempsFind l j = some t → P j t
  | [], _, _, _, h => by simp [tempsFind] at h
  | (k, s) :: l, hl, j, t, h => by
    unfold tempsFind at h
    split_ifs at h with hj
    · subst hj; cases h; exact hl _ List.mem_cons_self
    · exact tempsFind_ok (fun p hp ↦ hl p (List.mem_cons_of_mem _ hp)) h

private theorem listElementOrDefault_eq : ∀ (l : List Fn) (n : ℕ),
    listElementOrDefault l n default = l.getD n default
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => by simp [listElementOrDefault, listElementOrDefault_eq l n]

theorem bigTemps_ok :
    ∀ p ∈ bigTemps, (Stmt.tmpsList (coreOf p.1).body).map V.idx = p.2 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rw [coreOf, Nat.add_sub_cancel, listElementOrDefault_eq]
  exact bigTemps_spec q hq

/-- Compiled function `j`'s temporaries, by index. -/
noncomputable def armTemps (j : ℕ) : List ℕ :=
  (tempsFind bigTemps j).getD ((Stmt.tmpsList (coreOf j).body).map V.idx)

theorem armTemps_eq (j : ℕ) : (Stmt.tmpsList (coreOf j).body).map V.idx = armTemps j := by
  unfold armTemps
  cases h : tempsFind bigTemps j with
  | none => rfl
  | some t =>
    exact tempsFind_ok (P := fun j t ↦ (Stmt.tmpsList (coreOf j).body).map V.idx = t) bigTemps_ok h

/-- The arms' check: no arm's selector is a temporary of its function. -/
noncomputable def armOk (k : ℕ) (a : ℕ × ℕ × ℕ) : Bool := !(armTemps k).contains a.1

theorem armsCheck_plumbs : armsCheck armOk Data.plumbs 0 = true := by decide +kernel

/-- Every chained `match` of the plumbs `l`, the first of index `k`, passes `q`. -/
def chainsCheck (q : ℕ → ℕ × ℕ × List ℕ × ℕ × ℕ → Bool) : List Plumb → ℕ → Bool
  | [], _ => true
  | p :: ps, k => p.chains.all (q k) && chainsCheck q ps (k + 1)

theorem chainsCheck_spec {q : ℕ → ℕ × ℕ × List ℕ × ℕ × ℕ → Bool} : ∀ {l : List Plumb} {k : ℕ},
    chainsCheck q l k = true → ∀ j, ∀ ch ∈ (listElementOrDefault l j {}).chains, q (j + k) ch = true
  | [], _, _, j, a, ha => by cases j <;> simp [listElementOrDefault] at ha
  | p :: ps, k, h, j, a, ha => by
    simp only [chainsCheck, Bool.and_eq_true, List.all_eq_true] at h
    cases j with
    | zero => simpa using h.1 a ha
    | succ j =>
      have := chainsCheck_spec h.2 j a ha
      rwa [show j + (k + 1) = j + 1 + k by omega] at this

/-- The chains' check: neither selector of a chained `match` is a temporary of its function. -/
noncomputable def chainFreshOk (k : ℕ) (ch : ℕ × ℕ × List ℕ × ℕ × ℕ) : Bool :=
  !(armTemps k).contains ch.2.1 && !(armTemps k).contains ch.2.2.2.1

theorem chainsCheck_plumbs : chainsCheck chainFreshOk Data.plumbs 0 = true := by decide +kernel

private theorem not_tmp {body : List Stmt} {ts : List ℕ} (h : (Stmt.tmpsList body).map V.idx = ts)
    {x : ℕ} (hx : ts.contains x = false) : V.n x ∉ Stmt.tmpsList body := fun hm ↦ by
  have : x ∈ ts := h ▸ List.mem_map_of_mem (f := V.idx) hm
  simp [this] at hx

/-- **No table selector is a temporary of its function.** -/
theorem armsFresh : ArmsFresh := by
  refine ⟨fun j a ha ↦ ?_, fun j ch hc ↦ ?_⟩
  · have h := armsCheck_spec armsCheck_plumbs j a ha
    simp only [armOk, Nat.add_zero, Bool.not_eq_true'] at h
    exact not_tmp (armTemps_eq j) h
  · have h := chainsCheck_spec chainsCheck_plumbs j ch hc
    simp only [chainFreshOk, Nat.add_zero, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨not_tmp (armTemps_eq j) h.1, not_tmp (armTemps_eq j) h.2⟩

/-- **The checker's `keep`**, outright. -/
theorem kfacts_keep_all (hdr : E × E) (T : Tree) :
    ∀ ν, ∀ I ∈ honestInsts coreProgram fs H hdr T,
      ∀ I' ∈ honestInsts coreProgram fs H hdr (T.retemp coreProgram fs ν 0),
        I'.fp = I.fp → I'.t = I.t.retemp coreProgram fs ν I.fp → ∀ q ∈ I'.cells C,
          ¬ TmpOff coreProgram cert I.t q.1 → q ∈ I.cells C :=
  kfacts_keep coreProgram_fresh armsFresh hdr T

end
end LeanVM.Guest.B2C
