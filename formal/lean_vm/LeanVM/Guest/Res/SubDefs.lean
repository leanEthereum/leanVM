/-
  LeanVM.Guest.Res.SubDefs

  The `sub` residuals' families, checked per certificate: a run inside a split, a read inside
  `child_claim_list_any`'s table, a read of the gap walk, the proof stream's reads, a lift's runs.
-/

module

public import LeanVM.Guest.EndExecRS
public import LeanVM.Guest.Res.AnyData
public import LeanVM.Guest.Res.MonoDefs
public import LeanVM.Guest.Res.ResGiven
public import LeanVM.Guest.Res.FamDefs
public import LeanVM.Guest.Res.TermDefs
public import LeanVM.Guest.Res.RootsDefs
public import LeanVM.Guest.Res.TileDefs
public import LeanVM.Guest.Res.ExpDefs

/-!
# The `sub` residuals' families

`subB j x`: residual `x` of function `j` is no `sub` residual, or one of the families
(`splitB`, `anyResB anyLink`, `monoResB`, those read off the function's code, `subFamB` and
`termFamB`, the proof stream's reads, `stB`, the runs a split cuts into blocks, `blkB`,
`verify_tables`' table sumcheck's reads, `vtB`, the runs of a lift, `liftB`, `verify_keccak`'s
reads past its layers, `vkStB`, the roots' tree's reads, `rootsB`, the tiles, `tileFamB`, a lift
read back, `liftBackB`, the same cells named one index up, `ordShiftB`, `verify_tables`' reads past
its table sumcheck, `vtStB`, the runs a product's factors bound, `expFamB`, and `verify_tables`' groups'
bases, `vtGrpB`).
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

/-- **`verify_tables`' reads past its table sumcheck's last record's cursor** (cell `2910`) inside its
stream (`[22]`), below `153` words. -/
noncomputable def vtStB (j : ℕ) : Mode.Res → Bool
  | .sub a bs => (coreOf j).name == name% «verify_tables» && decide (a.q.k < 153) &&
      decide (Mode.Res.sub a bs = stRes 2910 (.fr 22) a.q.k)
  | _ => false

/-! ## `verify_tables`' groups -/

/-- A side's groups' bases `[58]·g^[G0, G0 + m)`, each read through a rank's group
`[58]·[[59]·g^(G0 + k)]`. -/
def vtGrpRes (G0 m : ℕ) : Mode.Res :=
  .sub ⟨⟨0, 0, [(.fr 58, 1)]⟩, .num G0, .num (G0 + m), 1, 0⟩
    ((List.range m).map fun k ↦ ⟨⟨0, 0, [(.fr 58, 1), (.hp 59 (G0 + k), 1)]⟩, .num 0, .num 1, 1, 0⟩)

/-- **`verify_tables`' groups' bases, read in group order**, at function `j`: the ranks of a side
name each of its groups, the push side's `9` and the count side's `6`. -/
noncomputable def vtGrpB (j : ℕ) (x : Mode.Res) : Bool :=
  (coreOf j).name == name% «verify_tables» && (decide (x = vtGrpRes 0 9) || decide (x = vtGrpRes 18 6))

/-! ## Runs cut into blocks by a split -/

/-- The run of stride `S` from `d` up to `[n]`'s exponent over `T`, inside `K` runs of stride `K·S` up to
`[s]`'s exponent, the `t`-th from `t·S + d`, and the run of stride `S` from `d` up to `[r]`'s exponent
past `[s]^(K·S)`. -/
def blkRes (T : Mode.Base) (s r n K S d : ℕ) : Mode.Res :=
  .sub ⟨⟨0, 0, [(T, 1)]⟩, .num 0, .ex (.fr n) 0, S, d⟩
    ((List.range K).map (fun t ↦ ⟨⟨0, 0, [(T, 1)]⟩, .num 0, .ex (.fr s) 0, K * S, t * S + d⟩) ++
      [⟨⟨0, 0, [(T, 1), (.fr s, K * S)]⟩, .num 0, .ex (.fr r) 0, S, d⟩])

/-- `blkRes` with `[s]^(K·S)` first in the last run's product. -/
def blkResC (T : Mode.Base) (s r n K S d : ℕ) : Mode.Res :=
  .sub ⟨⟨0, 0, [(T, 1)]⟩, .num 0, .ex (.fr n) 0, S, d⟩
    ((List.range K).map (fun t ↦ ⟨⟨0, 0, [(T, 1)]⟩, .num 0, .ex (.fr s) 0, K * S, t * S + d⟩) ++
      [⟨⟨0, 0, [(.fr s, K * S), (T, 1)]⟩, .num 0, .ex (.fr r) 0, S, d⟩])

/-- **A run cut into blocks** at function `j`: `[n] = [s]^K·[r]` a split of `j`'s (`splits`). -/
noncomputable def blkB (j : ℕ) : Mode.Res → Bool
  | .sub a bs => match a.q.bs with
    | [(T, _)] => splits.any fun p ↦ p.1 == j &&
        (decide (Mode.Res.sub a bs =
          blkRes T (cellJ j p.2.1) (cellJ j p.2.2.1) (cellJ j p.2.2.2.1) p.2.2.2.2 a.S a.d) ||
        decide (Mode.Res.sub a bs =
          blkResC T (cellJ j p.2.1) (cellJ j p.2.2.1) (cellJ j p.2.2.2.1) p.2.2.2.2 a.S a.d))
    | _ => false
  | _ => false

/-! ## A run up to an exponent `k` past another's -/

/-- **The frames' lifts**: function `j`, values `u`, `v` and `k` with `v = g^k·u`, `u` a power of `g`:
`verify_keccak`'s `y_g = g·pack_g` and `tau_g = g^4·pack_g`. -/
noncomputable def lifts : List (ℕ × V × V × ℕ) :=
  [(fn_idx% «verify_keccak», .n 19, .n 21, 1), (fn_idx% «verify_keccak», .n 19, .n 6, 4)]

/-- A lift's runs, `[v] = g^k·[u]`, over a product `P`: `g^c·P` up to `[u]`'s exponent (`c ≤ k`), or
the point `[u]·P` (`1 ≤ k`), inside `P` up to `[v]`'s; and for `k = 1`, `P` up to `[v]`'s exponent
inside `P` up to `[u]`'s and the point `[u]·P`. -/
def liftShape (u v k : ℕ) : Mode.Res → Bool
  | .sub a [b] => decide (b.q.fp = 0 ∧ b.q.k = 0 ∧ b.lo = .num 0 ∧ b.hi = .ex (.fr v) 0 ∧ b.S = 1 ∧
      b.d = 0 ∧ a.q.fp = 0 ∧ a.lo = .num 0 ∧ a.S = 1 ∧ a.d = 0 ∧
      ((a.q.k ≤ k ∧ a.q.bs = b.q.bs ∧ a.hi = .ex (.fr u) 0) ∨
        (1 ≤ k ∧ a.q.k = 0 ∧ (a.q.bs = (.fr u, 1) :: b.q.bs ∨ a.q.bs = b.q.bs ++ [(.fr u, 1)]) ∧
          a.hi = .num 1)))
  | .sub a [b, c] => decide (k = 1 ∧ a.q.fp = 0 ∧ a.q.k = 0 ∧ a.lo = .num 0 ∧ a.hi = .ex (.fr v) 0 ∧
      a.S = 1 ∧ a.d = 0 ∧ b.q = a.q ∧ b.lo = .num 0 ∧ b.hi = .ex (.fr u) 0 ∧ b.S = 1 ∧ b.d = 0 ∧
      c.q.fp = 0 ∧ c.q.k = 0 ∧ (c.q.bs = (.fr u, 1) :: a.q.bs ∨ c.q.bs = a.q.bs ++ [(.fr u, 1)]) ∧
      c.lo = .num 0 ∧ c.hi = .num 1 ∧ c.S = 1 ∧ c.d = 0)
  | _ => false

/-- **A run of a lift** of function `j`'s frame (`lifts`). -/
noncomputable def liftB (j : ℕ) (x : Mode.Res) : Bool :=
  lifts.any fun p ↦ p.1 == j && liftShape (cellJ j p.2.1) (cellJ j p.2.2.1) p.2.2.2 x

/-- **A run of a lift read back** (`liftBack`): of function `j`'s frame (`lifts`). -/
noncomputable def liftBackB (j : ℕ) (x : Mode.Res) : Bool :=
  lifts.any fun p ↦ p.1 == j && liftBack (cellJ j p.2.1) (cellJ j p.2.2.1) p.2.2.2 x

/-! ## `verify_keccak`'s reads past its layers -/

/-- **`verify_keccak`'s reads past a layer's returned cursor**: the cell of the layer's frame pointer
(step `s`'s call), the words read there: the next layer's, or after the last, the outputs' and the
inputs'. -/
def vkStSites : List (ℕ × ℕ) :=
  [(406, 48), (435, 48), (463, 48), (494, 48), (525, 48), (556, 48), (583, 48), (614, 48), (644, 48),
    (677, 48), (708, 48), (738, 97)]

/-- **A read past a layer's returned cursor** (`[[q]·g^23]`) inside the stream (`[14]`), at
`verify_keccak`. -/
noncomputable def vkStB (j : ℕ) : Mode.Res → Bool
  | .sub a bs => (coreOf j).name == name% «verify_keccak» && vkStSites.any fun s ↦ decide (a.q.k < s.2) &&
      decide (Mode.Res.sub a bs = stResB (.hp s.1 23) (.fr 14) a.q.k)
  | _ => false

/-- **The `sub` residuals' families**, the families read off the code from the witness `w`. -/
noncomputable def subB (j : ℕ) (w : Wit) : Mode.Res → Bool
  | .sub a bs => splitB j (.sub a bs) || anyResB anyLink j (.sub a bs) || monoResB j (.sub a bs) ||
      subFamB j w (.sub a bs) || termFamB j w (.sub a bs) || stB j (.sub a bs) ||
      blkB j (.sub a bs) || vtB j (.sub a bs) || liftB j (.sub a bs) || vkStB j (.sub a bs) ||
      rootsB j (.sub a bs) || tileFamB j w (.sub a bs) || liftBackB j (.sub a bs) || ordShiftB j w (.sub a bs) ||
      vtStB j (.sub a bs) || expFamB j w (.sub a bs) || vtGrpB j (.sub a bs)
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
