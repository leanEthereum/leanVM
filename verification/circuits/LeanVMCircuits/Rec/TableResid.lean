module

public import LeanVMCircuits.Rec.TableSum

@[expose] public section

/-!
The table sumcheck's residual terms as `constraints::verify` makes them.

After its rounds, `constraints::verify` adds to the last claim each owned table's weight times its summand at its
column claims (`residual = mul_add(weight, summand, residual)`, the terms `SumcheckCert.resid` names). `Bind.ResidCert`
names how each term is made, in `Table::OWNED`'s order. Its weight (`TermCert.weightCalls`): from a `one`, round `j`
(variable `m = n - 1 - j`) a `times_one_plus(w, s_j) = mul_add(w, s_j, w)` with `s_j = add(ζ_m, r_j)` where the table is
active (`τ > m`), and a `mul(w, r_j)` where it sits out. Its summand (`TableResidual::value_at`, `TermCert.summandCalls`):
its push and pull forms at its column claims (`BusForm::at`, `FormCert`: a `mul_add(coeff, col, acc)` per linear term
from the form's constant, then a `mul` and a `mul_add` per product term), `mul_add(ξ, pull, push)`, then per identity
of the table (`AirLink.allIds`, in order) `mul_add(ξ^(2 + j), value, acc)`, the identity's value its
`BusForm::at_constants` (`IdCert`: from an `e_const 0`, a `mul_const_add(col, w, acc)` per linear term, then a `mul`
and a `mul_const_add` per product term, its words the model's) and the power from `TableResidual::batch`'s
`powers(ξ, 2 + 66)` (`ResidCert.powCalls`: a `one`, then a `mul(p, ξ)` each).

`ResidCert.sem`: where the calls hold and `ResidCert.okIn` passes, the residual terms sum to
`Σ_T foldWeight ζ τ_T r · summandAt forms ξ T col_T`, `ζ` the named point, `r` the rounds' challenges, `forms` the
named forms' `Quad`s and `col_T` the named column claims. `ResidCert.final_eq`: at the committed witness's heights,
forms and columns' extensions at `chi r`, that is `AirLink.tableInst`'s final value (`tableInst_final`), so the
sumcheck's test is `sumcheckEvent`'s at the honest instance. `checkbind` names one for every table sumcheck.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model AirLink Finset

/-- The owned tables in `Table::OWNED`'s order, the table sumcheck's airs. -/
def ownedList : List Table := [.emul, .exk, .hash, .split, .cast]

/-- Each owned table's number of columns (`Table::n_cols`). -/
def nCols : Table → ℕ
  | .emul => 9
  | .exk => 7
  | .hash => 19
  | .split => 65
  | .cast => 4
  | _ => 0

/-- Identity `g` of `AirLink.allIds`. -/
def idAt (g : ℕ) : Identity := ((allIds[g]?).map (·.2)).getD ⟨[], []⟩

/-- The places in `AirLink.allIds` of table `T`'s identities, in order. -/
def idsOf (T : Table) : List ℕ := (List.range allIds.length).filter fun j => (allIds[j]?.map (·.1)) == some T

/-! Chains of calls. -/

/-- A chain of `mul_const_add(a, w, acc)` from `acc`, one per term `(a, w, call)`, its constant the word `w`. -/
def mcaCalls (os : Array (List ℕ)) (acc : ℕ) : List (ℕ × ℕ × ℕ) → List (ℕ × Call)
  | (a, w, j) :: ts => (j, .mulConstAdd a w 0 0 acc) :: mcaCalls os (o os j) ts
  | [] => []

/-- The chain's output. -/
def mcaOut (os : Array (List ℕ)) (acc : ℕ) : List (ℕ × ℕ × ℕ) → ℕ
  | (_, _, j) :: ts => mcaOut os (o os j) ts
  | [] => acc

/-- A bus form at columns `cols` (`BusForm::at`): from its constant wire `const`, a `mul_add(coeff, cols[c], acc)` per
linear term `(c, coeff, call)`, then per product term `(a, b, coeff, mul, call)` a `mul(cols[a], cols[b])` and a
`mul_add(coeff, product, acc)`. -/
structure FormCert where
  const : ℕ
  lin : List (ℕ × ℕ × ℕ) := []
  prods : List (ℕ × ℕ × ℕ × ℕ × ℕ) := []
  deriving Inhabited, Repr

namespace FormCert

variable (os : Array (List ℕ)) (cols : List ℕ) (f : FormCert)

def linTerms : List (ℕ × ℕ × ℕ) := f.lin.map fun t => (t.2.1, cols.getD t.1 0, t.2.2)
def prodTerms : List (ℕ × ℕ × ℕ) := f.prods.map fun t => (t.2.2.1, o os t.2.2.2.1, t.2.2.2.2)
def linOut : ℕ := residOut os f.const (f.linTerms cols)
def out : ℕ := residOut os (f.linOut os cols) (f.prodTerms os)

/-- Its calls. -/
def calls : List (ℕ × Call) :=
  residCalls os f.const (f.linTerms cols) ++ residCalls os (f.linOut os cols) (f.prodTerms os) ++
    f.prods.map fun t => (t.2.2.2.1, .mul (cols.getD t.1 0) (cols.getD t.2.1 0))

/-- Every column it reads is among the first `n`. -/
def colsIn (n : ℕ) : Bool := f.lin.all (·.1 < n) && f.prods.all fun t => t.1 < n && t.2.1 < n

/-- The form as a `Quad`, its coefficients its wires' values. -/
noncomputable def quad (val : Val) : Quad where
  const := Model.ev val f.const
  lin := f.lin.map fun t => (t.1, Model.ev val t.2.1)
  prods := f.prods.map fun t => (t.1, t.2.1, Model.ev val t.2.2.1)

end FormCert

/-- An identity at columns `cols` (`BusForm::at_constants`): from an `e_const 0` at `start`, a
`mul_const_add(cols[c], w, acc)` per linear term `(c, w)` of identity `g` of `AirLink.allIds` (`lin` its calls), then
per product term `(a, b, w)` a `mul(cols[a], cols[b])` and a `mul_const_add(product, w, acc)` (`prods` their calls); and
the `mul_add(ξ^(2 + g), value, acc)` adding it to its table's summand at `accAt`. -/
structure IdCert where
  g : ℕ
  start : ℕ
  lin : List ℕ := []
  prods : List (ℕ × ℕ) := []
  accAt : ℕ
  deriving Inhabited, Repr

namespace IdCert

variable (os : Array (List ℕ)) (cols : List ℕ) (ic : IdCert)

def linTerms : List (ℕ × ℕ × ℕ) := ((idAt ic.g).linear.zip ic.lin).map fun t => (cols.getD t.1.1 0, t.1.2, t.2)
def prodTerms : List (ℕ × ℕ × ℕ) := ((idAt ic.g).prods.zip ic.prods).map fun t => (o os t.2.1, t.1.2.2, t.2.2)
def linOut : ℕ := mcaOut os (o os ic.start) (ic.linTerms cols)
def out : ℕ := mcaOut os (ic.linOut os cols) (ic.prodTerms os)

/-- Its calls. -/
def calls : List (ℕ × Call) :=
  (ic.start, .eConst 0 0 0) :: mcaCalls os (o os ic.start) (ic.linTerms cols) ++
    mcaCalls os (ic.linOut os cols) (ic.prodTerms os) ++
    ((idAt ic.g).prods.zip ic.prods).map fun t => (t.2.1, .mul (cols.getD t.1.1 0) (cols.getD t.1.2.1 0))

/-- Its calls, one per term of its identity, each in the replay. -/
def ok (cs : Array Call) (rl : Array Bool) : Bool :=
  ic.lin.length == (idAt ic.g).linear.length && ic.prods.length == (idAt ic.g).prods.length &&
    callsOk cs rl (ic.calls os cols)

end IdCert

/-- One residual term (`constraints::verify`): its table's `τ`, the `one` its weight starts from and its weight's call
per round (`wAt`), its column claims (`cols`), its push and pull forms, the `mul_add(ξ, pull, push)` at `formsAt`, and
its identities. -/
structure TermCert where
  tau : ℕ
  oneAt : ℕ
  wAt : List ℕ := []
  cols : List ℕ := []
  push : FormCert := default
  pull : FormCert := default
  formsAt : ℕ := 0
  ids : List IdCert := []
  deriving Inhabited, Repr

/-- The table sumcheck's residual (`ResidCert`): its sumcheck, `ξ`, the point `ζ` (wire `m` its `ζ_m`), each round's
`add(ζ_m, r_j)` (`sAt`), the powers of `ξ` (`pows`), and its terms. -/
structure ResidCert where
  sc : ℕ
  xi : ℕ
  zeta : List ℕ := []
  sAt : List ℕ := []
  pows : List ℕ := []
  terms : List TermCert := []
  deriving Inhabited, Repr

namespace TermCert

variable (os : Array (List ℕ)) (t : TermCert)

/-- The weight after `k` rounds. -/
def wIn (k : ℕ) : ℕ := if k = 0 then o os t.oneAt else o os (t.wAt.getD (k - 1) 0)

/-- Whether the table is active in round `j` of `n`: `τ > n - 1 - j`. -/
def active (n j : ℕ) : Bool := decide (n - 1 - j < t.tau)

/-- Its weight's calls over `n` rounds of challenges `r`, `s` the rounds' `add(ζ_m, r_j)` calls. -/
def weightCalls (n : ℕ) (r s : List ℕ) : List (ℕ × Call) :=
  (t.oneAt, .one) :: (List.range n).map fun j =>
    (t.wAt.getD j 0, if t.active n j then .mulAdd (t.wIn os j) (o os (s.getD j 0)) (t.wIn os j)
      else .mul (t.wIn os j) (r.getD j 0))

/-- Its identities' chain into the summand, from `mul_add(ξ, pull, push)`. -/
def idTerms (pows : List ℕ) : List (ℕ × ℕ × ℕ) :=
  t.ids.map fun ic => (o os (pows.getD (2 + ic.g) 0), ic.out os t.cols, ic.accAt)

def pushOut : ℕ := t.push.out os t.cols
def pullOut : ℕ := t.pull.out os t.cols

/-- Its summand's calls: its forms, their combination at `ξ`, and its identities'. -/
def summandCalls (xi : ℕ) (pows : List ℕ) : List (ℕ × Call) :=
  t.push.calls os t.cols ++ t.pull.calls os t.cols ++ [(t.formsAt, .mulAdd xi (t.pullOut os) (t.pushOut os))] ++
    residCalls os (o os t.formsAt) (t.idTerms os pows)

/-- Its summand. -/
def summand (pows : List ℕ) : ℕ := residOut os (o os t.formsAt) (t.idTerms os pows)

end TermCert

namespace ResidCert

variable (os : Array (List ℕ)) (rc : ResidCert)

/-- Each round's `add(ζ_m, r_j)`, `m = n - 1 - j`. -/
def sCalls (n : ℕ) (r : List ℕ) : List (ℕ × Call) :=
  (List.range n).map fun j => (rc.sAt.getD j 0, .add (rc.zeta.getD (n - 1 - j) 0) (r.getD j 0))

/-- The powers of `ξ`: a `one`, then a `mul(p, ξ)` each. -/
def powCalls : List (ℕ × Call) :=
  (rc.pows.getD 0 0, .one) :: (List.range (rc.pows.length - 1)).map fun k =>
    (rc.pows.getD (k + 1) 0, .mul (o os (rc.pows.getD k 0)) rc.xi)

/-- Term `k`'s check: table `T`'s columns, forms reading them, its identities in `AirLink.allIds`'s order, and its
weight and summand the residual's term `(w, s)`. -/
def termOk (cs : Array Call) (rl : Array Bool) (n : ℕ) (r : List ℕ) (T : Table) (t : TermCert) (w s : ℕ) : Bool :=
  t.cols.length == nCols T && t.push.colsIn (nCols T) && t.pull.colsIn (nCols T) && t.wAt.length == n &&
    t.ids.map (·.g) == idsOf T && t.ids.all (fun ic => ic.ok os t.cols cs rl) &&
    callsOk cs rl (t.weightCalls os n r rc.sAt) && callsOk cs rl (t.summandCalls os rc.xi rc.pows) &&
    w == t.wIn os n && s == t.summand os rc.pows

/-- The check: its sumcheck's residual has one term per owned table, each as `termOk` says, the rounds' `add`s and the
powers of `ξ` are in the replay, as many powers as `AirLink.allIds` needs. -/
def okIn (scs : Array SumcheckCert) (cs : Array Call) (rl : Array Bool) : Bool :=
  match scs[rc.sc]? with
  | some sc =>
    sc.resid.length == 5 && rc.terms.length == 5 && decide (allIds.length + 2 ≤ rc.pows.length) &&
      callsOk cs rl (rc.sCalls sc.rounds.length (sc.rounds.map (·.chal))) && callsOk cs rl (rc.powCalls os) &&
      (List.range 5).all fun k => rc.termOk os cs rl sc.rounds.length (sc.rounds.map (·.chal))
        (ownedList.getD k .emul) (rc.terms.getD k default) (sc.resid.getD k default).1
        (sc.resid.getD k default).2.1
  | none => false

/-- Table `T`'s term. -/
def termOf (T : Table) : TermCert := rc.terms.getD (ownedList.idxOf T) default

/-- The named forms: each table's push (`0`) and pull (`1`) form as a `Quad`. -/
noncomputable def formsV (val : Val) (i : Fin 2) (T : Table) : Quad :=
  if i = 0 then (rc.termOf T).push.quad val else (rc.termOf T).pull.quad val

/-- Table `T`'s named column claims. -/
noncomputable def colV (val : Val) (T : Table) (c : ℕ) : E := Model.ev val ((rc.termOf T).cols.getD c 0)

end ResidCert

/-! The chains' values where the calls hold. -/

section Sem

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}

theorem mca_sem (hF : Facts cs rl os st val) : ∀ (acc : ℕ) (ts : List (ℕ × ℕ × ℕ)),
    callsOk cs rl (mcaCalls os acc ts) = true →
      Model.ev val (mcaOut os acc ts) =
        Model.ev val acc + (ts.map fun t => Model.ev val t.1 * emb (ofWord t.2.1)).sum
  | acc, [], _ => by simp [mcaOut]
  | acc, (a, w, j) :: ts, h => by
    obtain ⟨h1, h2⟩ := callsOk_cons h
    have hj : Model.ev val (o os j) = Model.ev val a * toE (ofWord w) (ofWord 0) (ofWord 0) + Model.ev val acc :=
      holds_of_mem hF h1 (List.mem_singleton_self _)
    rw [ofWord_zero, toE_emb] at hj
    rw [mcaOut, mca_sem hF (o os j) ts h2, hj, List.map_cons, List.sum_cons]
    ring

theorem callsOk_of_sub {l l' : List (ℕ × Call)} (h : callsOk cs rl l = true) (hs : ∀ x ∈ l', x ∈ l) :
    callsOk cs rl l' = true := by
  simp only [callsOk, List.all_eq_true] at h ⊢
  exact fun x hx => h x (hs x hx)

/-- A form's value at its column claims is its `Quad`'s. -/
theorem FormCert.sem (hF : Facts cs rl os st val) {cols : List ℕ} {f : FormCert}
    (h : callsOk cs rl (f.calls os cols) = true) :
    Model.ev val (f.out os cols) = (f.quad val).eval fun c => Model.ev val (cols.getD c 0) := by
  simp only [FormCert.calls, callsOk_append, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hm : ∀ t ∈ f.prods, Model.ev val (o os t.2.2.2.1) =
      Model.ev val (cols.getD t.1 0) * Model.ev val (cols.getD t.2.1 0) := fun t ht =>
    holds_of_mem hF h3 (List.mem_map.mpr ⟨t, ht, rfl⟩)
  rw [FormCert.out, resid_sem hF _ _ h2, FormCert.linOut, resid_sem hF _ _ h1]
  simp only [FormCert.quad, Quad.eval, FormCert.linTerms, FormCert.prodTerms, List.map_map, Function.comp_def]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  rw [hm t ht]

/-- An identity's value at its column claims is its model identity's (`AirLink.ofId`). -/
theorem IdCert.sem (hF : Facts cs rl os st val) {cols : List ℕ} {ic : IdCert} (h : ic.ok os cols cs rl = true) :
    Model.ev val (ic.out os cols) = (ofId (idAt ic.g)).eval fun c => Model.ev val (cols.getD c 0) := by
  simp only [IdCert.ok, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hl, hp⟩, h⟩ := h
  simp only [IdCert.calls, List.cons_append] at h
  obtain ⟨h0, h⟩ := callsOk_cons h
  simp only [callsOk_append, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hs : Model.ev val (o os ic.start) = 0 := by
    have := holds_of_mem hF h0 (List.mem_singleton_self _)
    simp only [Call.Holds] at this
    rw [show o os ic.start = (os.getD ic.start []).getD 0 0 from rfl, this, ofWord_zero, toE_emb, emb_zero]
  have hm : ∀ t ∈ (idAt ic.g).prods.zip ic.prods, Model.ev val (o os t.2.1) =
      Model.ev val (cols.getD t.1.1 0) * Model.ev val (cols.getD t.1.2.1 0) := fun t ht =>
    holds_of_mem hF h3 (List.mem_map.mpr ⟨t, ht, rfl⟩)
  rw [IdCert.out, mca_sem hF _ _ h2, IdCert.linOut, mca_sem hF _ _ h1, hs]
  simp only [ofId, Quad.eval, IdCert.linTerms, IdCert.prodTerms, List.map_map, Function.comp_def, zero_add]
  congr 1
  · have e : ((idAt ic.g).linear.zip ic.lin).map (fun t => Model.ev val (cols.getD t.1.1 0) * emb (ofWord t.1.2)) =
        (((idAt ic.g).linear.zip ic.lin).map Prod.fst).map fun t => Model.ev val (cols.getD t.1 0) * emb (ofWord t.2) := by
      rw [List.map_map]; rfl
    rw [e, List.map_fst_zip (by omega)]
    exact congrArg List.sum (List.map_congr_left fun t _ => mul_comm _ _)
  · have e : ((idAt ic.g).prods.zip ic.prods).map (fun t => Model.ev val (o os t.2.1) * emb (ofWord t.1.2.2)) =
        (((idAt ic.g).prods.zip ic.prods).map Prod.fst).map fun t =>
          Model.ev val (cols.getD t.1 0) * Model.ev val (cols.getD t.2.1 0) * emb (ofWord t.2.2) := by
      rw [List.map_map]
      exact List.map_congr_left fun t ht => by rw [hm t ht]; rfl
    rw [e, List.map_fst_zip (by omega)]
    exact congrArg List.sum (List.map_congr_left fun t _ => by ring)

/-- The weight after `k ≤ n` rounds is the product of each round's factor: `1 + ζ_m + r_j` where the table is active,
`r_j` where it sits out. -/
theorem TermCert.weight_sem (hF : Facts cs rl os st val) {t : TermCert} {n : ℕ} {r s zeta : List ℕ}
    (hw : callsOk cs rl (t.weightCalls os n r s) = true)
    (hs : callsOk cs rl ((List.range n).map fun j => (s.getD j 0, Call.add (zeta.getD (n - 1 - j) 0) (r.getD j 0))) =
      true) :
    ∀ k ≤ n, Model.ev val (t.wIn os k) = ((List.range k).map fun j =>
      if t.active n j then 1 + Model.ev val (zeta.getD (n - 1 - j) 0) + Model.ev val (r.getD j 0)
      else Model.ev val (r.getD j 0)).prod := by
  obtain ⟨h1, h2⟩ := callsOk_cons hw
  intro k hk
  induction k with
  | zero =>
    have h0 : Model.ev val (o os t.oneAt) = 1 := holds_of_mem hF h1 (List.mem_singleton_self _)
    simpa [TermCert.wIn] using h0
  | succ k ih =>
    have hk' : k < n := hk
    have hc := holds_of_mem hF h2 (List.mem_map.mpr ⟨k, List.mem_range.mpr hk', rfl⟩)
    have hwk : t.wIn os (k + 1) = o os (t.wAt.getD k 0) := by simp [TermCert.wIn]
    rw [hwk, List.range_succ, List.map_append, List.prod_append, ← ih (by omega), List.map_singleton,
      List.prod_singleton]
    by_cases ha : t.active n k
    · rw [if_pos ha] at hc ⊢
      have hsk : Model.ev val (o os (s.getD k 0)) =
          Model.ev val (zeta.getD (n - 1 - k) 0) + Model.ev val (r.getD k 0) :=
        holds_of_mem hF hs (List.mem_map.mpr ⟨k, List.mem_range.mpr hk', rfl⟩)
      simp only [Call.Holds] at hc
      rw [show o os (t.wAt.getD k 0) = (os.getD (t.wAt.getD k 0) []).getD 0 0 from rfl, hc, hsk]
      ring
    · rw [if_neg ha] at hc ⊢
      exact hc

/-- The powers of `ξ`: power `k` is `ξ^k`. -/
theorem ResidCert.pow_sem (hF : Facts cs rl os st val) {rc : ResidCert} (h : callsOk cs rl (rc.powCalls os) = true) :
    ∀ k < rc.pows.length, Model.ev val (o os (rc.pows.getD k 0)) = Model.ev val rc.xi ^ k := by
  obtain ⟨h1, h2⟩ := callsOk_cons h
  intro k hk
  induction k with
  | zero =>
    have h0 : Model.ev val (o os (rc.pows.getD 0 0)) = 1 := holds_of_mem hF h1 (List.mem_singleton_self _)
    simpa using h0
  | succ k ih =>
    have hc : Model.ev val (o os (rc.pows.getD (k + 1) 0)) = Model.ev val (o os (rc.pows.getD k 0)) *
        Model.ev val rc.xi := holds_of_mem hF h2 (List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩)
    rw [hc, ih (by omega), pow_succ]

end Sem

/-! The weight is the verifier's fold, and the identities' sum is `summandAt`'s. -/

theorem prod_range_eq_foldWeight {n : ℕ} (ζ r : Fin n → E) (τ : ℕ) (zv rv : ℕ → E) (hz : ∀ m : Fin n, ζ m = zv m)
    (hr : ∀ j : Fin n, r j = rv j) :
    ((List.range n).map fun j => if n - 1 - j < τ then 1 + zv (n - 1 - j) + rv j else rv j).prod =
      foldWeight ζ τ r := by
  have hf : foldWeight ζ τ r = (List.finRange n).foldl
      (fun acc j => acc * (if (Fin.rev j : ℕ) < τ then 1 + ζ (Fin.rev j) + r j else r j)) 1 := by
    unfold foldWeight
    congr 1
    funext acc j
    split_ifs <;> rfl
  rw [hf, foldl_mul_eq, one_mul, ← List.map_coe_finRange_eq_range, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  have e : n - (j.val + 1) = n - 1 - j.val := by omega
  simp only [Function.comp_apply, Fin.val_rev, hz, hr, e]

theorem sum_filter_list {M : Type} [AddCommMonoid M] (p : ℕ → Bool) (F : ℕ → M) :
    ∀ l : List ℕ, ((l.filter p).map F).sum = (l.map fun j => if p j then F j else 0).sum
  | [] => rfl
  | j :: l => by
    rw [List.filter_cons, List.map_cons, List.sum_cons, ← sum_filter_list p F l]
    split <;> simp_all

/-- A table's identities' terms over `idsOf T` are `summandAt`'s sum over `AirLink.allIds`. -/
theorem sum_idsOf (T : Table) (F : ℕ → E) :
    ((idsOf T).map F).sum = ∑ j : Fin allIds.length with allIds[j].1 = T, F j := by
  rw [idsOf, sum_filter_list, Finset.sum_filter, Fin.sum_univ_def, ← List.map_coe_finRange_eq_range, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
  simp only [Function.comp_apply, List.getElem?_eq_getElem j.isLt, Option.map_some, beq_iff_eq,
    Option.some.injEq, Fin.getElem_fin]

/-! The residual as the instance's final value. -/

theorem Quad.eval_congr (q : Quad) {col col' : ℕ → E} (h : ∀ t ∈ q.lin, col t.1 = col' t.1)
    (h' : ∀ t ∈ q.prods, col t.1 = col' t.1 ∧ col t.2.1 = col' t.2.1) : q.eval col = q.eval col' := by
  simp only [Quad.eval]
  rw [List.map_congr_left (fun t ht => by rw [h t ht] : ∀ t ∈ q.lin, t.2 * col t.1 = t.2 * col' t.1),
    List.map_congr_left (fun t ht => by rw [(h' t ht).1, (h' t ht).2] :
      ∀ t ∈ q.prods, t.2.2 * (col t.1 * col t.2.1) = t.2.2 * (col' t.1 * col' t.2.1))]

/-- Every column an identity reads is among its table's (`Table::n_cols`). -/
def idsColsOk : Bool :=
  allIds.all fun p => p.2.linear.all (·.1 < nCols p.1) && p.2.prods.all fun t => t.1 < nCols p.1 && t.2.1 < nCols p.1

theorem idsColsOk_eq : idsColsOk = true := by decide +kernel

theorem idAt_eq (j : Fin allIds.length) : idAt j = allIds[j].2 := by
  simp [idAt]

/-- `summandAt` reads its columns only where its forms and its table's identities do: below `nCols T` when the forms
read only those. -/
theorem summandAt_congr (forms : Fin 2 → Table → Quad) (ξ : E) (T : Table) {col col' : ℕ → E}
    (hc : ∀ c < nCols T, col c = col' c) (hf : ∀ i, (∀ t ∈ (forms i T).lin, t.1 < nCols T) ∧
      ∀ t ∈ (forms i T).prods, t.1 < nCols T ∧ t.2.1 < nCols T) :
    summandAt forms ξ T col = summandAt forms ξ T col' := by
  have hform : ∀ i, (forms i T).eval col = (forms i T).eval col' := fun i =>
    Quad.eval_congr _ (fun t ht => hc _ ((hf i).1 t ht))
      fun t ht => ⟨hc _ ((hf i).2 t ht).1, hc _ ((hf i).2 t ht).2⟩
  have hall := idsColsOk_eq
  simp only [idsColsOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hall
  simp only [summandAt, hform]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hT : allIds[(j : ℕ)].1 = T := by simpa only [Fin.getElem_fin] using (Finset.mem_filter.mp hj).2
  obtain ⟨hl, hp⟩ := hall _ (List.getElem_mem j.isLt)
  rw [hT] at hl hp
  congr 1
  exact Quad.eval_congr _ (fun t ht => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact hc _ (hl u hu))
    fun t ht => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact ⟨hc _ (hp u hu).1, hc _ (hp u hu).2⟩

section Main

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}

/-- A term's summand is `summandAt` at its forms, `ξ` and its column claims. -/
theorem TermCert.summand_sem (hF : Facts cs rl os st val) {rc : ResidCert} {t : TermCert} {T : Table}
    (hpow : callsOk cs rl (rc.powCalls os) = true) (hlen : allIds.length + 2 ≤ rc.pows.length)
    (hids : t.ids.map (·.g) = idsOf T) (hic : ∀ ic ∈ t.ids, ic.ok os t.cols cs rl = true)
    (h : callsOk cs rl (t.summandCalls os rc.xi rc.pows) = true) :
    Model.ev val (t.summand os rc.pows) = summandAt (fun i _ => if i = 0 then t.push.quad val else t.pull.quad val)
      (Model.ev val rc.xi) T fun c => Model.ev val (t.cols.getD c 0) := by
  simp only [TermCert.summandCalls, callsOk_append, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hpu, hpl⟩, hf⟩, hi⟩ := h
  have hfo : Model.ev val (o os t.formsAt) =
      Model.ev val rc.xi * Model.ev val (t.pullOut os) + Model.ev val (t.pushOut os) :=
    holds_of_mem hF hf (List.mem_singleton_self _)
  have hg : ∀ ic ∈ t.ids, ic.g < allIds.length := fun ic hic' => by
    have : ic.g ∈ idsOf T := hids ▸ List.mem_map.mpr ⟨ic, hic', rfl⟩
    exact List.mem_range.mp (List.mem_filter.mp this).1
  have hterms : ((t.idTerms os rc.pows).map fun u => Model.ev val u.1 * Model.ev val u.2.1) =
      (idsOf T).map fun j => Model.ev val rc.xi ^ (2 + j) *
        (ofId (idAt j)).eval fun c => Model.ev val (t.cols.getD c 0) := by
    rw [← hids, List.map_map, TermCert.idTerms, List.map_map]
    refine List.map_congr_left fun ic hic' => ?_
    simp only [Function.comp_apply]
    rw [ResidCert.pow_sem hF hpow _ (by have := hg ic hic'; omega), IdCert.sem hF (hic ic hic')]
  rw [TermCert.summand, resid_sem hF _ _ hi, hfo, TermCert.pullOut, TermCert.pushOut, FormCert.sem hF hpu,
    FormCert.sem hF hpl, hterms, sum_idsOf, summandAt]
  simp only [Fin.isValue, show ((1 : Fin 2) = 0) = False from by decide, ↓reduceIte]
  have e : ∀ j : Fin allIds.length, idAt j = allIds[j].2 := idAt_eq
  simp only [e]
  ring

/-- A term's weight is the verifier's fold `foldWeight` at the point and the rounds' challenges. -/
theorem TermCert.weight_fold (hF : Facts cs rl os st val) {t : TermCert} {rounds : List RoundCert} {s zeta : List ℕ}
    (hw : callsOk cs rl (t.weightCalls os rounds.length (rounds.map (·.chal)) s) = true)
    (hs : callsOk cs rl ((List.range rounds.length).map fun j => (s.getD j 0,
      Call.add (zeta.getD (rounds.length - 1 - j) 0) ((rounds.map (·.chal)).getD j 0))) = true) :
    Model.ev val (t.wIn os rounds.length) = foldWeight (fun m : Fin rounds.length => Model.ev val (zeta.getD m 0))
      t.tau fun j => Model.ev val (rounds.getD j default).chal := by
  rw [TermCert.weight_sem hF hw hs _ le_rfl]
  rw [← prod_range_eq_foldWeight _ _ t.tau (fun m => Model.ev val (zeta.getD m 0))
    (fun j => Model.ev val ((rounds.map (·.chal)).getD j 0)) (fun _ => rfl) fun j => by
      simp only [List.getD_eq_getElem _ _ (by simp : (j : ℕ) < (rounds.map (·.chal)).length),
        List.getD_eq_getElem _ _ j.isLt, List.getElem_map]]
  simp only [TermCert.active, decide_eq_true_eq]

/-- What a passing `ResidCert` gives where the calls hold: its sumcheck's residual terms sum to each owned table's
`foldWeight` at the named point `ζ`, its `τ` and the rounds' challenges, times its `summandAt` at the named forms, `ξ`
and its column claims. -/
theorem ResidCert.sem (hF : Facts cs rl os st val) {scs : Array SumcheckCert} {rc : ResidCert} {sc : SumcheckCert}
    (h : rc.okIn os scs cs rl = true) (hsc : scs[rc.sc]? = some sc) :
    (sc.resid.map fun t => Model.ev val t.1 * Model.ev val t.2.1).sum =
      ∑ T ∈ owned, foldWeight (fun m : Fin sc.rounds.length => Model.ev val (rc.zeta.getD m 0)) (rc.termOf T).tau
        (fun j => Model.ev val (sc.rounds.getD j default).chal) *
          summandAt (rc.formsV val) (Model.ev val rc.xi) T (rc.colV val T) := by
  unfold ResidCert.okIn at h
  rw [hsc] at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hres, hterms⟩, hpl⟩, hs⟩, hpow⟩, hk⟩ := h
  have one : ∀ k < 5, Model.ev val (sc.resid.getD k default).1 * Model.ev val (sc.resid.getD k default).2.1 =
      foldWeight (fun m : Fin sc.rounds.length => Model.ev val (rc.zeta.getD m 0)) (rc.termOf (ownedList.getD k .emul)).tau
        (fun j => Model.ev val (sc.rounds.getD j default).chal) *
          summandAt (rc.formsV val) (Model.ev val rc.xi) (ownedList.getD k .emul)
            (rc.colV val (ownedList.getD k .emul)) := by
    intro k hk5
    have hto : rc.termOf (ownedList.getD k .emul) = rc.terms.getD k default := by
      simp only [ResidCert.termOf]
      congr 1
      interval_cases k <;> rfl
    have ht := hk k hk5
    simp only [ResidCert.termOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ht
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hids⟩, hic⟩, hw⟩, hsm⟩, hwe⟩, hse⟩ := ht
    rw [hwe, hse, hto, TermCert.weight_fold hF hw (by simpa [ResidCert.sCalls] using hs),
      TermCert.summand_sem hF hpow hpl hids hic hsm]
    congr 1
    have hcv : rc.colV val (ownedList.getD k .emul) =
        fun c => Model.ev val ((rc.terms.getD k default).cols.getD c 0) := by
      funext c
      simp only [ResidCert.colV, hto]
    simp only [summandAt, ResidCert.formsV, hto, hcv]
  obtain ⟨t0, t1, t2, t3, t4, he⟩ : ∃ t0 t1 t2 t3 t4, sc.resid = [t0, t1, t2, t3, t4] := by
    match sc.resid, hres with
    | [t0, t1, t2, t3, t4], _ => exact ⟨t0, t1, t2, t3, t4, rfl⟩
  have e0 := one 0 (by norm_num); have e1 := one 1 (by norm_num); have e2 := one 2 (by norm_num)
  have e3 := one 3 (by norm_num); have e4 := one 4 (by norm_num)
  simp only [he, List.getD_cons_zero, List.getD_cons_succ, ownedList] at e0 e1 e2 e3 e4
  rw [he]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, owned]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, e0, e1, e2, e3, e4]

/-- The residual is the honest instance's final value (`AirLink.tableInst_final`) where the named point is `ζ`, each
table's named `τ` its height's, the named forms `forms`, and each table's named column claims its columns' extensions
at `chi r`, `r` the rounds' challenges: the table sumcheck's residual certified as `tableInst`'s final value at the
column claims. -/
theorem ResidCert.final_eq (hF : Facts cs rl os st val) {scs : Array SumcheckCert} {rc : ResidCert}
    {sc : SumcheckCert} (h : rc.okIn os scs cs rl = true) (hsc : scs[rc.sc]? = some sc) (w : Witness)
    (ζ : Fin sc.rounds.length → E) (forms : Fin 2 → Table → Quad)
    (hζ : ∀ m : Fin sc.rounds.length, Model.ev val (rc.zeta.getD m 0) = ζ m)
    (hτ : ∀ T ∈ owned, (rc.termOf T).tau = tauOf w T)
    (hforms : ∀ T ∈ owned, ∀ i, rc.formsV val i T = forms i T)
    (hcol : ∀ T ∈ owned, ∀ c < nCols T, rc.colV val T c =
      MvPolynomial.eval (chi fun j => Model.ev val (sc.rounds.getD j default).chal) (mle sc.rounds.length w T c)) :
    (sc.resid.map fun t => Model.ev val t.1 * Model.ev val t.2.1).sum =
      (tableInst sc.rounds.length w ζ forms (Model.ev val rc.xi)).final
        fun j => Model.ev val (sc.rounds.getD j default).chal := by
  have hok := h
  unfold ResidCert.okIn at hok
  rw [hsc] at hok
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨-, hk⟩ := hok
  rw [ResidCert.sem hF h hsc, tableInst_final]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hζ' : (fun m : Fin sc.rounds.length => Model.ev val (rc.zeta.getD m 0)) = ζ := funext hζ
  rw [hζ', hτ T hT]
  congr 1
  have hsame : summandAt (rc.formsV val) (Model.ev val rc.xi) T = summandAt forms (Model.ev val rc.xi) T := by
    funext col
    simp only [summandAt, hforms T hT]
  rw [← hsame]
  refine summandAt_congr _ _ T (hcol T hT) fun i => ?_
  -- The named forms read only the table's columns.
  have hidx : ∃ k < 5, ownedList.getD k .emul = T := by
    simp only [owned, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl
    exacts [⟨0, by norm_num, rfl⟩, ⟨1, by norm_num, rfl⟩, ⟨2, by norm_num, rfl⟩, ⟨3, by norm_num, rfl⟩,
      ⟨4, by norm_num, rfl⟩]
  obtain ⟨k, hk5, rfl⟩ := hidx
  have hto : rc.termOf (ownedList.getD k .emul) = rc.terms.getD k default := by
    simp only [ResidCert.termOf]
    congr 1
    interval_cases k <;> rfl
  have ht := hk k hk5
  simp only [ResidCert.termOk, Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hpu⟩, hpl⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := ht
  have hc : ∀ f : FormCert, f.colsIn (nCols (ownedList.getD k .emul)) = true →
      (∀ t ∈ (f.quad val).lin, t.1 < nCols (ownedList.getD k .emul)) ∧
        ∀ t ∈ (f.quad val).prods, t.1 < nCols (ownedList.getD k .emul) ∧ t.2.1 < nCols (ownedList.getD k .emul) := by
    intro f hf
    simp only [FormCert.colsIn, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hf
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact hf.1 u hu
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact hf.2 u hu
  simp only [ResidCert.formsV, hto]
  split
  · exact hc _ hpu
  · exact hc _ hpl

end Main

/-! Mutation tests of `ResidCert.okIn`'s rules, on calls whose call `j` outputs wire `100 + j`. -/

/-- Outputs: call `j` makes wire `100 + j`. -/
def mutOuts (k : ℕ) : Array (List ℕ) := ((List.range k).map fun j => [100 + j]).toArray

/-- A table of `τ = 1` over two rounds of challenges `10`, `11`, point `ζ = [20, 21]`: it sits out round 0
(`mul(one, r_0)`) and is active in round 1 (`mul_add(w, add(ζ_0, r_1), w)`). -/
def mutWeightCalls : Array Call := #[.one, .zero, .add 21 10, .add 20 11, .mul 100 10, .mulAdd 104 103 104]

example : callsOk mutWeightCalls #[] (({ tau := 1, oneAt := 0, wAt := [4, 5] } : TermCert).weightCalls (mutOuts 6) 2
    [10, 11] [2, 3]) = true := by decide

/-- Another `τ` reads another pattern of active rounds, and fails. -/
example : callsOk mutWeightCalls #[] (({ tau := 2, oneAt := 0, wAt := [4, 5] } : TermCert).weightCalls (mutOuts 6) 2
    [10, 11] [2, 3]) = false := by decide

example : callsOk mutWeightCalls #[] (({ tau := 0, oneAt := 0, wAt := [4, 5] } : TermCert).weightCalls (mutOuts 6) 2
    [10, 11] [2, 3]) = false := by decide

/-- `HASH`'s identity (`AirLink.allIds`' first, `c^2 + c` at its mux column 18, here wire 50): an `e_const 0`, a
`mul_const_add(c, 1, 0)`, a `mul(c, c)` and a `mul_const_add(c^2, 1, c)` pass; another word fails, and so do its
calls read as `SPLIT`'s first identity. -/
def mutIdCalls (w : ℕ) : Array Call := #[.eConst 0 0 0, .mulConstAdd 50 w 0 0 100, .mul 50 50, .mulConstAdd 102 1 0 0 101]

def mutCols : List ℕ := (List.range 18).map (fun _ => 0) ++ [50]

example : idsOf .hash = [0] ∧ ({ g := 0, start := 0, lin := [1], prods := [(2, 3)], accAt := 9 } : IdCert).ok
    (mutOuts 4) mutCols (mutIdCalls 1) #[] = true := by decide +kernel

example : ({ g := 0, start := 0, lin := [1], prods := [(2, 3)], accAt := 9 } : IdCert).ok (mutOuts 4) mutCols
    (mutIdCalls 2) #[] = false := by decide +kernel

example : ({ g := 1, start := 0, lin := [1], prods := [(2, 3)], accAt := 9 } : IdCert).ok (mutOuts 4) mutCols
    (mutIdCalls 1) #[] = false := by decide +kernel

/-- A table's identities are named in `AirLink.allIds`' order: `SPLIT`'s are its places 1 to 65, and a term naming
them out of order, or naming `HASH`'s, fails `termOk`'s comparison. -/
example : idsOf .split = (List.range 65).map (· + 1) ∧ idsOf .split ≠ [2, 1] ++ (List.range 63).map (· + 3) ∧
    idsOf .split ≠ [0] := by decide +kernel

/-- A form with one linear and one product term at column 0 (wire 50): its constant `30`, `mul_add(31, c, 30)`,
`mul(c, c)`, `mul_add(32, c^2, acc)` pass; reading column 1 fails. -/
def mutFormCalls : Array Call := #[.zero, .mulAdd 31 50 30, .mul 50 50, .mulAdd 32 102 101]

example : callsOk mutFormCalls #[] (({ const := 30, lin := [(0, 31, 1)], prods := [(0, 0, 32, 2, 3)] } : FormCert).calls
    (mutOuts 4) [50]) = true := by decide

example : callsOk mutFormCalls #[] (({ const := 30, lin := [(1, 31, 1)], prods := [(0, 0, 32, 2, 3)] } : FormCert).calls
    (mutOuts 4) [50]) = false := by decide

/-- The powers of `ξ` (wire 7): `one`, `mul(1, ξ)`, `mul(ξ, ξ)` pass; a power not the previous one's times `ξ` fails. -/
example : callsOk #[.one, .mul 100 7, .mul 101 7] #[]
    (({ sc := 0, xi := 7, pows := [0, 1, 2] } : ResidCert).powCalls (mutOuts 3)) = true := by decide

example : callsOk #[.one, .mul 100 7, .mul 100 7] #[]
    (({ sc := 0, xi := 7, pows := [0, 1, 2] } : ResidCert).powCalls (mutOuts 3)) = false := by decide

end LeanVMCircuits.Rec.Bind
