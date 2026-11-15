/-
  LeanVM.Guest.Res.SubDefs

  The `sub` residuals' families, checked per certificate: a run inside a split, a read inside
  `child_claim_list_any`'s table, a read of the gap walk, the proof stream's reads.
-/

module

public import LeanVM.Guest.EndExecRS
public import LeanVM.Guest.Res.AnyData
public import LeanVM.Guest.Res.MonoDefs
public import LeanVM.Guest.Res.ResGiven
public import LeanVM.Guest.Res.FamDefs
public import LeanVM.Guest.Res.TermDefs

/-!
# The `sub` residuals' families

`subB j x`: residual `x` of function `j` is no `sub` residual, or one of the families
(`splitB`, `anyResB anyLink`, `monoResB`, those read off the function's code, `subFamB` and
`termFamB`, the proof stream's reads, `stB`, the runs a split cuts into blocks, `blkB`, and
`verify_tables`' table sumcheck's reads, `vtB`).
`SubOk exc K`: certificate `K` is listed in `exc`, or each of its residuals passes `subB` at its
function's index, decided per certificate (`subOk_of`).
`EndExec.resOpen_subOk` (`EndExecRSub`): given `SubOk resExc` of every certificate and the listed
certificates' residuals, no `sub` residual outside the families is left open.
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Guest.B2C (cellJ)

@[expose] public section

/-! ## The proof stream's reads -/

/-- **The proof stream's readers**: function, its cursor's cell, the stream's base (the layer's
parameter, the loops' through their header), the words read past the cursor. -/
def stSites : List (String × ℕ × Mode.Base × ℕ) :=
  [(name% «keccak_layer__L0», 765, .fr 17, 36), (name% «keccak_layer__L1», 792, .fr 17, 36),
    (name% «keccak_layer__L0_loop0», 21, .hp 1 17, 16), (name% «keccak_layer__L1_loop0», 21, .hp 1 17, 16),
    (name% «keccak_layer__L0_loop1», 18, .hp 1 17, 2), (name% «keccak_layer__L1_loop1», 18, .hp 1 17, 2)]

/-- The read `c` words past the cursor in cell `o`, inside the stream `st·[0, 8192)`. -/
def stRes (o : ℕ) (st : Mode.Base) (c : ℕ) : Mode.Res :=
  .sub ⟨⟨0, c, [(.fr o, 1)]⟩, .num 0, .num 1, 1, 0⟩ [⟨⟨0, 0, [(st, 1)]⟩, .num 0, .num 8192, 1, 0⟩]

/-- **A read of the proof stream** at function `j`: a site's, below its words. -/
noncomputable def stB (j : ℕ) : Mode.Res → Bool
  | .sub a bs => stSites.any fun s ↦ (coreOf j).name == s.1 && decide (a.q.k < s.2.2.2) &&
      decide (Mode.Res.sub a bs = stRes s.2.1 s.2.2.1 a.q.k)
  | _ => false

/-! ## `verify_tables`' table sumcheck -/

/-- The read `c` words past the cursor base `cur`, inside the stream `st·[0, 8192)`. -/
def stResB (cur st : Mode.Base) (c : ℕ) : Mode.Res :=
  .sub ⟨⟨0, c, [(cur, 1)]⟩, .num 0, .num 1, 1, 0⟩ [⟨⟨0, 0, [(st, 1)]⟩, .num 0, .num 8192, 1, 0⟩]

/-- The copy loop's read `[5]·[10]` inside the challenges `[5]·[0, e([3]))`. -/
def vtcRes : Mode.Res :=
  .sub ⟨⟨0, 0, [(.fr 5, 1), (.fr 10, 1)]⟩, .num 0, .num 1, 1, 0⟩
    [⟨⟨0, 0, [(.fr 5, 1)]⟩, .num 0, .ex (.fr 3) 0, 1, 0⟩]

/-- **`verify_tables`' table sumcheck's reads** at function `j`: the rounds loop's reads of the stream
`[[1]·g^22]` past its record's cursor (cell `17`) and past `sumcheck_round4`'s (`[[19]·g^3]`), below
three words, and the copy loop's read of the challenges. -/
noncomputable def vtB (j : ℕ) : Mode.Res → Bool
  | .sub a bs => ((coreOf j).name == name% «verify_tables_loop0» && decide (a.q.k < 3) &&
        (decide (Mode.Res.sub a bs = stResB (.fr 17) (.hp 1 22) a.q.k) ||
          decide (Mode.Res.sub a bs = stResB (.hp 19 3) (.hp 1 22) a.q.k))) ||
      ((coreOf j).name == name% «verify_tables_loop1» && decide (Mode.Res.sub a bs = vtcRes))
  | _ => false

/-! ## Runs cut into blocks by a split -/

/-- The run of stride `S` from `d` up to `[n]`'s exponent over `T`, inside `K` runs of stride `K·S` up to
`[s]`'s exponent, the `t`-th from `t·S + d`, and the run of stride `S` from `d` up to `[r]`'s exponent
past `[s]^(K·S)`. -/
def blkRes (T : Mode.Base) (s r n K S d : ℕ) : Mode.Res :=
  .sub ⟨⟨0, 0, [(T, 1)]⟩, .num 0, .ex (.fr n) 0, S, d⟩
    ((List.range K).map (fun t ↦ ⟨⟨0, 0, [(T, 1)]⟩, .num 0, .ex (.fr s) 0, K * S, t * S + d⟩) ++
      [⟨⟨0, 0, [(T, 1), (.fr s, K * S)]⟩, .num 0, .ex (.fr r) 0, S, d⟩])

/-- **A run cut into blocks** at function `j`: `[n] = [s]^K·[r]` a split of `j`'s (`splits`). -/
noncomputable def blkB (j : ℕ) : Mode.Res → Bool
  | .sub a bs => match a.q.bs with
    | [(T, _)] => splits.any fun p ↦ p.1 == j &&
        decide (Mode.Res.sub a bs =
          blkRes T (cellJ j p.2.1) (cellJ j p.2.2.1) (cellJ j p.2.2.2.1) p.2.2.2.2 a.S a.d)
    | _ => false
  | _ => false

/-- **The `sub` residuals' families**, the families read off the code from the witness `w`. -/
noncomputable def subB (j : ℕ) (w : Wit) : Mode.Res → Bool
  | .sub a bs => splitB j (.sub a bs) || anyResB anyLink j (.sub a bs) || monoResB j (.sub a bs) ||
      subFamB j w (.sub a bs) || termFamB j w (.sub a bs) || stB j (.sub a bs) ||
      blkB j (.sub a bs) || vtB j (.sub a bs)
  | _ => true

/-- **A certificate's `sub` residuals in the families**: it is listed in `exc`, or each is at its
function's index `j`, with a witness `w` of its code. -/
def SubOk (exc : List Mode.Cert) (K : Mode.Cert) : Prop :=
  K ∈ exc ∨ ∃ j w, j < nFns ∧ (fnOf j).entryPc = K.F.entry ∧ witOk j w = true ∧
    allV (fun l ↦ l.all (subB j w)) K.F.res = true

theorem subOk_of {exc : List Mode.Cert} {K : Mode.Cert} {j : ℕ} {w : Wit}
    (h : (decide (j < nFns) && (fnOf j).entryPc == K.F.entry && witOk j w &&
      allV (fun l ↦ l.all (subB j w)) K.F.res) = true) :
    SubOk exc K := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact Or.inr ⟨j, w, h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem subOk_exc {exc : List Mode.Cert} {K : Mode.Cert} (h : K ∈ exc) : SubOk exc K := Or.inl h

end

end LeanVM.Guest.Res
