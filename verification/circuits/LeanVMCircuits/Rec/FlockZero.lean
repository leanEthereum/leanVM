module

public import LeanVMCircuits.Rec.FlockInst
public import LeanVMCircuits.Rec.Bind
public import LeanVMCircuits.Rec.RecParts

@[expose] public section

/-!
The zerocheck of flock's reduction over the `HASH` rows as a check of `RecParts`, from the builder's calls.

`zerocheck::verify` (one circuit) draws the eq point's drawn coordinates and `λ`, makes the seven fixed coordinates
(`e_const`), reads the round-1 message's `64` values on `Λ`, draws the skip challenge `ζ`, and its input claim is
`SkipDomain::first_round_at`: `D_128 V_S(ζ) V_Λ(ζ) Σ_i v_i / (ζ + λ_i)`. Then come `n` eq-weighted rounds of degree two
(`read_round(3, claim, Some(r_i))`, the sumcheck `SumcheckCert` names, round `i`'s weight `r_i`), the triple `a, b, c`,
and the test of the last claim against `mul_add(1, mul_add(a, b, c), 0)`, `λ^0 = 1` the one circuit's weight.

`SkipCert` names the input claim's calls: `ζ`'s six squares, `V_S`'s six `mul_const_add(ζ^(2^j), c_j, acc)` from
`ζ^64`, `e_const(V_S(λ_0))`, `add(V_S, it)`, their `mul`, the `mul_const_add(·, D_128, zero)`, per node of `Λ` its
`e_const`, `add(ζ, λ_i)` and `inv`, the `mul_add(v_i, inv_i, acc)` chain from a `zero`, and the last `mul`.
`SkipCert.sem`: where the calls hold (the `inv` calls' facts included: `(ζ + λ_i) inv_i = 1`, so no `ζ` in `Λ` passes),
the input claim is `Flock.phat v` at `ζ`, `v` the message's values: the polynomial zero on `S` and `v` on `Λ`.

`ZeroCert` names the zerocheck: its sumcheck (degree two, no residual, no hints), the skip's calls, the fixed
coordinates' `e_const` calls (`Flock.fixedWords`, each round `j < 7`'s weight), the drawn coordinates (round `7 + k`'s
weight), and the terminal's calls. `ZeroCert.final_eq`: the test's other side is `a b + c`. `ZeroCert.claim0_eq`: the
input claim is `phat v` at `ζ`. `ZeroCert.point_eq`: the rounds' weights are `fixed ++ ρ`, `ρ` the drawn coordinates.
`Bind.zero_part`: true triple outputs (the quirky extensions `a*`, `b*`, `c*` at `(ζ, χ)`, `χ` the rounds' challenges)
make the input claim the honest instance `Flock.zeroInst`'s sum off `sumcheckFalse`. `Bind.zero_rows`: off it, the
skip's event `skipDraws` and the fixed coordinates' event `fixDraws`, every row of the `HASH` tables holds.

What stays a premise: the triple's three claims (the lincheck's input), the test (`htest`), the rounds' challenges as
the oracle's (`hchal`), and the three events, which `sumcheck_run_sound_at` (with `ZeroCert.weights_eq` for its
weights), `skipDraws_card` (at most `127` of the `ζ`, the message fixed before `ζ`) and `fixDraws_card` (at most an
`n'/|E|` fraction of the drawn coordinates, the tables committed before them) bound.

`zerosOf` names the zerocheck certificates of a replay: for each certified sumcheck, its terminal, skip and fixed
coordinates by their calls (`zeroOf`, `skipOf`), those passing `okIn`.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Finset LeanVMCircuits.Rec.Flock

/-! The skip's interpolation. -/

/-- `SkipDomain::first_round_at`'s calls at the skip challenge `ζ`: its six squares, `V_S`'s six `mul_const_add`s,
the coset's constant and `add`, their `mul`, the scale's `zero` and `mul_const_add`, per node its `e_const`, `add` and
`inv`, the message's values, the Lagrange sum's `zero` and `mul_add`s, and the last `mul`. -/
structure SkipCert where
  zeta : ℕ
  sqAt : List ℕ := []
  vanAt : List ℕ := []
  offAt : ℕ
  onAt : ℕ
  bothAt : ℕ
  scaleZero : ℕ
  scaleAt : ℕ
  nodeAt : List ℕ := []
  diffAt : List ℕ := []
  invAt : List ℕ := []
  values : List ℕ := []
  sumZero : ℕ
  sumAt : List ℕ := []
  claimAt : ℕ
  deriving Inhabited, Repr

namespace SkipCert

variable (os : Array (List ℕ)) (k : SkipCert)

/-- `ζ^(2^j)`: `ζ`, then each square. -/
def pow (j : ℕ) : ℕ := if j = 0 then k.zeta else o os (k.sqAt.getD (j - 1) 0)

/-- `V_S`'s fold after `j` terms, from `ζ^64`. -/
def vacc (j : ℕ) : ℕ := if j = 0 then k.pow os 6 else o os (k.vanAt.getD (j - 1) 0)

/-- `V_S(ζ)`. -/
def van : ℕ := k.vacc os 6

/-- The Lagrange sum after `i` terms. -/
def sacc (i : ℕ) : ℕ := if i = 0 then o os k.sumZero else o os (k.sumAt.getD (i - 1) 0)

/-- The input claim. -/
def claim : ℕ := o os k.claimAt

/-- The squares. -/
def sqCalls : List (ℕ × Call) := (List.range 6).map fun j => (k.sqAt.getD j 0, .mul (k.pow os j) (k.pow os j))

/-- `V_S`'s fold, its coefficients `cw`. -/
def vanCalls (cw : List ℕ) : List (ℕ × Call) :=
  (List.range 6).map fun j => (k.vanAt.getD j 0, .mulConstAdd (k.pow os j) (cw.getD j 0) 0 0 (k.vacc os j))

/-- The coset's constant `off`, the scale `d`, and the last `mul`, over `m` nodes. -/
def midCalls (off d m : ℕ) : List (ℕ × Call) :=
  [(k.offAt, .eConst off 0 0), (k.onAt, .add (k.van os) (o os k.offAt)), (k.bothAt, .mul (k.van os) (o os k.onAt)),
    (k.scaleZero, .zero), (k.scaleAt, .mulConstAdd (o os k.bothAt) d 0 0 (o os k.scaleZero)), (k.sumZero, .zero),
    (k.claimAt, .mul (o os k.scaleAt) (k.sacc os m))]

/-- Node `i`'s calls: its `e_const`, `add(ζ, λ_i)`, `inv`, and the sum's `mul_add(v_i, inv_i, acc)`. -/
def nodeCalls (nodes : List ℕ) (i : ℕ) : List (ℕ × Call) :=
  [(k.nodeAt.getD i 0, .eConst (nodes.getD i 0) 0 0), (k.diffAt.getD i 0, .add k.zeta (o os (k.nodeAt.getD i 0))),
    (k.invAt.getD i 0, .inv (o os (k.diffAt.getD i 0))),
    (k.sumAt.getD i 0, .mulAdd (k.values.getD i 0) (o os (k.invAt.getD i 0)) (k.sacc os i))]

/-- The calls, for the coefficients `cw`, the coset's constant `off`, the scale `d` and the nodes. -/
def callsWith (cw : List ℕ) (off d : ℕ) (nodes : List ℕ) : List (ℕ × Call) :=
  k.sqCalls os ++ k.vanCalls os cw ++ k.midCalls os off d nodes.length ++
    (List.range nodes.length).flatMap (k.nodeCalls os nodes)

/-- The calls are in the replay, for the given constants. -/
def okWith (cs : Array Call) (rl : Array Bool) (cw : List ℕ) (off d : ℕ) (nodes : List ℕ) : Bool :=
  callsOk cs rl (k.callsWith os cw off d nodes)

/-- The calls are in the replay, for `first_round_at`'s constants and `Λ`. -/
def ok (cs : Array Call) (rl : Array Bool) : Bool := k.okWith os cs rl vanWords offWord d128Word lWords

end SkipCert

section Sem

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}

theorem ev_mulConstAdd_K {a c d : ℕ} {j : ℕ} (hF : Facts cs rl os st val)
    (h : callsOk cs rl [(j, .mulConstAdd a c 0 0 d)] = true) :
    Model.ev val (o os j) = Model.ev val a * kw c + Model.ev val d := by
  have hj : Model.ev val (o os j) = Model.ev val a * toE (ofWord c) (ofWord 0) (ofWord 0) + Model.ev val d :=
    holds_of_mem hF h (List.mem_singleton_self _)
  rw [hj, ofWord_zero, toE_emb, kw]

theorem ev_eConst_K {c : ℕ} {j : ℕ} (hF : Facts cs rl os st val) (h : callsOk cs rl [(j, .eConst c 0 0)] = true) :
    Model.ev val (o os j) = kw c := by
  have hj : Model.ev val (o os j) = toE (ofWord c) (ofWord 0) (ofWord 0) :=
    holds_of_mem hF h (List.mem_singleton_self _)
  rw [hj, ofWord_zero, toE_emb, kw]

theorem callsOk_mem {l : List (ℕ × Call)} (h : callsOk cs rl l = true) {x : ℕ × Call} (hx : x ∈ l) :
    callsOk cs rl [x] = true := by
  simp only [callsOk, List.all_eq_true] at h ⊢
  intro y hy
  rw [List.mem_singleton.mp hy]
  exact h x hx

/-- `first_round_at`'s value: where the skip's calls hold, its input claim is the round-1 message's polynomial
`phat v` at `ζ`, `v` the message's values. The `inv` calls' facts give `(ζ + λ_i) inv_i = 1`. -/
theorem SkipCert.sem (hF : Facts cs rl os st val) {k : SkipCert} (h : k.ok os cs rl = true) :
    Model.ev val (k.claim os) = (phat fun i => Model.ev val (k.values.getD i 0)).eval (Model.ev val k.zeta) := by
  obtain ⟨hs, hl, -⟩ := skip_facts
  simp only [SkipCert.ok, SkipCert.okWith, SkipCert.callsWith, callsOk_append, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hsq, hvan⟩, hmid⟩, hnodes⟩ := h
  set ζ := Model.ev val k.zeta with hζ
  -- The squares.
  have hpow : ∀ j ≤ 6, Model.ev val (k.pow os j) = ζ ^ 2 ^ j := by
    intro j hj
    induction j with
    | zero => simp [SkipCert.pow, hζ]
    | succ j ih =>
      have hc := callsOk_mem hsq (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩)
      have hj' : Model.ev val (o os (k.sqAt.getD j 0)) = Model.ev val (k.pow os j) * Model.ev val (k.pow os j) :=
        holds_of_mem hF hc (List.mem_singleton_self _)
      have hp : k.pow os (j + 1) = o os (k.sqAt.getD j 0) := by simp [SkipCert.pow]
      rw [hp, hj', ih (by omega), ← sq, ← pow_mul, ← pow_succ]
  -- `V_S`'s fold.
  have hvacc : ∀ j ≤ 6, Model.ev val (k.vacc os j) = ζ ^ 64 + ∑ i ∈ range j, kw (vc i) * ζ ^ 2 ^ i := by
    intro j hj
    induction j with
    | zero =>
      rw [show k.vacc os 0 = k.pow os 6 from if_pos rfl, hpow 6 le_rfl, sum_range_zero, add_zero]
      norm_num
    | succ j ih =>
      have hc := callsOk_mem hvan (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩)
      have hp : k.vacc os (j + 1) = o os (k.vanAt.getD j 0) := by simp [SkipCert.vacc]
      rw [hp, ev_mulConstAdd_K hF hc, ih (by omega), hpow j (by omega), sum_range_succ]
      simp only [vc]
      ring
  have hV : Model.ev val (k.van os) = vanS.eval ζ := by
    rw [SkipCert.van, hvacc 6 le_rfl, vanS_eval]
  -- The middle calls.
  have hmem : ∀ x ∈ k.midCalls os offWord d128Word lWords.length, callsOk cs rl [x] = true :=
    fun x hx => callsOk_mem hmid hx
  have hoff := ev_eConst_K hF (hmem (k.offAt, .eConst offWord 0 0) (by simp [SkipCert.midCalls]))
  have hon : Model.ev val (o os k.onAt) = Model.ev val (k.van os) + Model.ev val (o os k.offAt) :=
    holds_of_mem hF (hmem (k.onAt, .add (k.van os) (o os k.offAt)) (by simp [SkipCert.midCalls]))
      (List.mem_singleton_self _)
  have hboth : Model.ev val (o os k.bothAt) = Model.ev val (k.van os) * Model.ev val (o os k.onAt) :=
    holds_of_mem hF (hmem (k.bothAt, .mul (k.van os) (o os k.onAt)) (by simp [SkipCert.midCalls]))
      (List.mem_singleton_self _)
  have hz1 : Model.ev val (o os k.scaleZero) = 0 :=
    holds_of_mem hF (hmem (k.scaleZero, .zero) (by simp [SkipCert.midCalls])) (List.mem_singleton_self _)
  have hscale := ev_mulConstAdd_K hF (hmem (k.scaleAt, .mulConstAdd (o os k.bothAt) d128Word 0 0 (o os k.scaleZero))
    (by simp [SkipCert.midCalls]))
  have hz2 : Model.ev val (o os k.sumZero) = 0 :=
    holds_of_mem hF (hmem (k.sumZero, .zero) (by simp [SkipCert.midCalls])) (List.mem_singleton_self _)
  have hclaim : Model.ev val (o os k.claimAt) = Model.ev val (o os k.scaleAt) * Model.ev val (k.sacc os 64) := by
    have := holds_of_mem hF (hmem (k.claimAt, .mul (o os k.scaleAt) (k.sacc os lWords.length))
      (by simp [SkipCert.midCalls])) (List.mem_singleton_self _)
    rwa [hl] at this
  -- The nodes.
  have hnode : ∀ i < 64, ∀ x ∈ k.nodeCalls os lWords i, callsOk cs rl [x] = true := fun i hi x hx =>
    callsOk_mem hnodes (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr (by rw [hl]; exact hi), hx⟩)
  have hinv : ∀ i : Fin 64, (ζ + lNode i) * Model.ev val (o os (k.invAt.getD i 0)) = 1 := by
    intro i
    have hn := ev_eConst_K hF (hnode i i.isLt _ (by simp [SkipCert.nodeCalls]) :
      callsOk cs rl [(k.nodeAt.getD i 0, .eConst (lWords.getD i 0) 0 0)] = true)
    have hd : Model.ev val (o os (k.diffAt.getD i 0)) = ζ + Model.ev val (o os (k.nodeAt.getD i 0)) :=
      holds_of_mem hF (hnode i i.isLt (k.diffAt.getD i 0, .add k.zeta (o os (k.nodeAt.getD i 0)))
        (by simp [SkipCert.nodeCalls])) (List.mem_singleton_self _)
    have hi : Model.ev val (o os (k.diffAt.getD i 0)) * Model.ev val (o os (k.invAt.getD i 0)) = 1 :=
      holds_of_mem hF (hnode i i.isLt (k.invAt.getD i 0, .inv (o os (k.diffAt.getD i 0)))
        (by simp [SkipCert.nodeCalls])) (List.mem_singleton_self _)
    rwa [hd, hn] at hi
  have hsum : ∀ m ≤ 64, Model.ev val (k.sacc os m) =
      ∑ i ∈ range m, Model.ev val (k.values.getD i 0) * Model.ev val (o os (k.invAt.getD i 0)) := by
    intro m hm
    induction m with
    | zero => simp [SkipCert.sacc, hz2]
    | succ m ih =>
      have hs' : Model.ev val (o os (k.sumAt.getD m 0)) = Model.ev val (k.values.getD m 0) *
          Model.ev val (o os (k.invAt.getD m 0)) + Model.ev val (k.sacc os m) :=
        holds_of_mem hF (hnode m (by omega) (k.sumAt.getD m 0, .mulAdd (k.values.getD m 0)
          (o os (k.invAt.getD m 0)) (k.sacc os m)) (by simp [SkipCert.nodeCalls])) (List.mem_singleton_self _)
      have hp : k.sacc os (m + 1) = o os (k.sumAt.getD m 0) := by simp [SkipCert.sacc]
      rw [hp, hs', ih (by omega), sum_range_succ]
      ring
  rw [← phat_eval _ hinv, SkipCert.claim, hclaim, hscale, hz1, add_zero, hboth, hon, hoff, hV, hsum 64 le_rfl,
    ← Fin.sum_univ_eq_sum_range (fun i => Model.ev val (k.values.getD i 0) * Model.ev val (o os (k.invAt.getD i 0)))]

end Sem

/-! The zerocheck. -/

/-- The zerocheck: its sumcheck in the certificate's list, the skip's calls, the fixed coordinates' `e_const` calls,
the drawn coordinates' wires, the triple's wires, and the terminal's calls (`mul_add(a, b, c)`, the `one` of `λ^0`, a
`zero`, and `mul_add(1, value, 0)`). -/
structure ZeroCert where
  sc : ℕ
  skip : SkipCert
  fixedAt : List ℕ := []
  outer : List ℕ := []
  tri : ℕ × ℕ × ℕ
  valueAt : ℕ
  oneAt : ℕ
  termZero : ℕ
  termAt : ℕ
  deriving Inhabited, Repr

namespace ZeroCert

variable (os : Array (List ℕ)) (zc : ZeroCert)

/-- The fixed coordinates' `e_const` calls, `Flock.fixedWords` in order. -/
def fixedCalls : List (ℕ × Call) := (List.range 7).map fun j =>
  (zc.fixedAt.getD j 0, .eConst (fixedWords.getD j (0, 0, 0)).1 (fixedWords.getD j (0, 0, 0)).2.1
    (fixedWords.getD j (0, 0, 0)).2.2)

/-- The terminal's calls. -/
def termCalls : List (ℕ × Call) :=
  [(zc.valueAt, .mulAdd zc.tri.1 zc.tri.2.1 zc.tri.2.2), (zc.oneAt, .one), (zc.termZero, .zero),
    (zc.termAt, .mulAdd (o os zc.oneAt) (o os zc.valueAt) (o os zc.termZero))]

/-- The rounds' weights: `7 + |outer|` rounds, round `j < 7` weighted by the fixed coordinate `j`, round `7 + k` by
the drawn coordinate `k`. -/
def weightsOk (sc : SumcheckCert) : Bool :=
  sc.rounds.length == 7 + zc.outer.length &&
    (List.range 7).all (fun j => (sc.rounds.getD j default).weight == some (o os (zc.fixedAt.getD j 0))) &&
    (List.range zc.outer.length).all fun k => (sc.rounds.getD (7 + k) default).weight == some (zc.outer.getD k 0)

/-- The check: the sumcheck has degree two, no residual and no hints, its input claim is the skip's, its test's
other side the terminal's, its weights as `weightsOk` says, and the calls are in the replay. -/
def okIn (scs : Array SumcheckCert) (cs : Array Call) (rl : Array Bool) : Bool :=
  match scs[zc.sc]? with
  | some sc => sc.deg == 2 && sc.resid.isEmpty && sc.hints.isEmpty && sc.claim0 == zc.skip.claim os &&
      sc.final == o os zc.termAt && zc.weightsOk os sc && callsOk cs rl zc.fixedCalls &&
      callsOk cs rl (zc.termCalls os) && zc.skip.ok os cs rl
  | none => false

/-- The drawn coordinates. -/
noncomputable def outerPt (val : Val) : Fin zc.outer.length → E := fun k => Model.ev val (zc.outer.getD k 0)

/-- The skip challenge. -/
noncomputable def zeta (val : Val) : E := Model.ev val zc.skip.zeta

/-- The round-1 message's values. -/
noncomputable def msg (val : Val) : Fin 64 → E := fun i => Model.ev val (zc.skip.values.getD i 0)

end ZeroCert

/-- A sumcheck's eq point: round `i`'s weight. -/
noncomputable def SumcheckCert.weightPt (sc : SumcheckCert) (val : Val) : Fin sc.rounds.length → E :=
  fun i => Model.ev val ((sc.rounds.getD i default).weight.getD 0)

/-- A sumcheck's challenges, round `j`'s at `j`, low variable first. -/
noncomputable def SumcheckCert.chalPt (sc : SumcheckCert) (val : Val) : Fin sc.rounds.length → E :=
  fun j => Model.ev val (sc.rounds.getD j default).chal

section Zero

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}

theorem ZeroCert.okIn_parts {zc : ZeroCert} {scs : Array SumcheckCert} {sc : SumcheckCert}
    (h : zc.okIn os scs cs rl = true) (hsc : scs[zc.sc]? = some sc) :
    sc.deg = 2 ∧ sc.resid = [] ∧ sc.hints = [] ∧ sc.claim0 = zc.skip.claim os ∧ sc.final = o os zc.termAt ∧
      zc.weightsOk os sc = true ∧ callsOk cs rl zc.fixedCalls = true ∧ callsOk cs rl (zc.termCalls os) = true ∧
      zc.skip.ok os cs rl = true := by
  unfold ZeroCert.okIn at h
  rw [hsc] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- The test's other side is the terminal `a b + c`. -/
theorem ZeroCert.final_eq (hF : Facts cs rl os st val) {zc : ZeroCert} {scs : Array SumcheckCert}
    {sc : SumcheckCert} (h : zc.okIn os scs cs rl = true) (hsc : scs[zc.sc]? = some sc) :
    Model.ev val sc.final = Model.ev val zc.tri.1 * Model.ev val zc.tri.2.1 + Model.ev val zc.tri.2.2 := by
  obtain ⟨-, -, -, -, hf, -, -, ht, -⟩ := ZeroCert.okIn_parts h hsc
  have hm : ∀ x ∈ zc.termCalls os, x.2.Holds st val (os.getD x.1 []) := fun x hx => holds_of_mem hF ht hx
  have hv : Model.ev val (o os zc.valueAt) = Model.ev val zc.tri.1 * Model.ev val zc.tri.2.1 +
      Model.ev val zc.tri.2.2 := hm (zc.valueAt, .mulAdd zc.tri.1 zc.tri.2.1 zc.tri.2.2) (by simp [ZeroCert.termCalls])
  have h1 : Model.ev val (o os zc.oneAt) = 1 := hm (zc.oneAt, .one) (by simp [ZeroCert.termCalls])
  have h0 : Model.ev val (o os zc.termZero) = 0 := hm (zc.termZero, .zero) (by simp [ZeroCert.termCalls])
  have hterm : Model.ev val (o os zc.termAt) = Model.ev val (o os zc.oneAt) * Model.ev val (o os zc.valueAt) +
      Model.ev val (o os zc.termZero) :=
    hm (zc.termAt, .mulAdd (o os zc.oneAt) (o os zc.valueAt) (o os zc.termZero)) (by simp [ZeroCert.termCalls])
  rw [hf, hterm, h1, h0, hv, one_mul, add_zero]

/-- The input claim is the round-1 message's polynomial at `ζ` (`SkipCert.sem`). -/
theorem ZeroCert.claim0_eq (hF : Facts cs rl os st val) {zc : ZeroCert} {scs : Array SumcheckCert}
    {sc : SumcheckCert} (h : zc.okIn os scs cs rl = true) (hsc : scs[zc.sc]? = some sc) :
    Model.ev val sc.claim0 = (phat (zc.msg val)).eval (zc.zeta val) := by
  obtain ⟨-, -, -, hc, -, -, -, -, hk⟩ := ZeroCert.okIn_parts h hsc
  rw [hc]
  exact SkipCert.sem hF hk

theorem ZeroCert.weights_parts {zc : ZeroCert} {sc : SumcheckCert} (h : zc.weightsOk os sc = true) :
    sc.rounds.length = 7 + zc.outer.length ∧
      (∀ j < 7, (sc.rounds.getD j default).weight = some (o os (zc.fixedAt.getD j 0))) ∧
      ∀ k < zc.outer.length, (sc.rounds.getD (7 + k) default).weight = some (zc.outer.getD k 0) := by
  simp only [ZeroCert.weightsOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- Every round is eq-weighted, by the eq point's coordinate: the weights `sumcheck_run_sound_at` takes for the honest
instance (`zeroInst_weight`). -/
theorem ZeroCert.weights_eq {zc : ZeroCert} {scs : Array SumcheckCert} {sc : SumcheckCert}
    (h : zc.okIn os scs cs rl = true) (hsc : scs[zc.sc]? = some sc) (val : Val) (T : Tables) (ζ : E)
    (χ : Fin sc.rounds.length → E) (i : Fin sc.rounds.length) :
    (sc.rounds.getD i default).weight.map (Model.ev val) =
      (zeroInst sc.rounds.length (sc.weightPt val) T ζ).weight χ i := by
  obtain ⟨-, -, -, -, -, hw, -⟩ := ZeroCert.okIn_parts h hsc
  obtain ⟨hn, h7, hk⟩ := ZeroCert.weights_parts hw
  rw [zeroInst_weight, SumcheckCert.weightPt]
  by_cases hi : (i : ℕ) < 7
  · rw [h7 i hi]
    rfl
  · have := hk (i - 7) (by omega)
    rw [show 7 + ((i : ℕ) - 7) = i by omega] at this
    rw [this]
    rfl

/-- The eq point is the fixed coordinates, then the drawn ones. -/
theorem ZeroCert.point_eq (hF : Facts cs rl os st val) {zc : ZeroCert} {scs : Array SumcheckCert}
    {sc : SumcheckCert} (h : zc.okIn os scs cs rl = true) (hsc : scs[zc.sc]? = some sc)
    (hn : sc.rounds.length = 7 + zc.outer.length) (i : Fin sc.rounds.length) :
    sc.weightPt val i = Fin.append fixedPt (zc.outerPt val) (Fin.cast hn i) := by
  obtain ⟨-, -, -, -, -, hw, hfx, -⟩ := ZeroCert.okIn_parts h hsc
  obtain ⟨-, h7, hk⟩ := ZeroCert.weights_parts hw
  obtain ⟨i, hi⟩ := i
  by_cases h7i : i < 7
  · have hc : (Fin.cast hn ⟨i, hi⟩ : Fin (7 + zc.outer.length)) = Fin.castAdd zc.outer.length ⟨i, h7i⟩ := Fin.ext rfl
    rw [hc, Fin.append_left, SumcheckCert.weightPt]
    simp only [h7 i h7i, Option.getD_some]
    have hcall := callsOk_mem hfx (List.mem_map.mpr ⟨i, List.mem_range.mpr h7i, rfl⟩)
    have he : Model.ev val (o os (zc.fixedAt.getD i 0)) = toE (ofWord (fixedWords.getD i (0, 0, 0)).1)
        (ofWord (fixedWords.getD i (0, 0, 0)).2.1) (ofWord (fixedWords.getD i (0, 0, 0)).2.2) :=
      holds_of_mem hF hcall (List.mem_singleton_self _)
    rw [he, fixedPt]
    rfl
  · have hc : (Fin.cast hn ⟨i, hi⟩ : Fin (7 + zc.outer.length)) = Fin.natAdd 7 ⟨i - 7, by omega⟩ :=
      Fin.ext (show i = 7 + (i - 7) by omega)
    rw [hc, Fin.append_right, SumcheckCert.weightPt, ZeroCert.outerPt]
    have := hk (i - 7) (by omega)
    rw [show 7 + (i - 7) = i by omega] at this
    simp only [this, Option.getD_some]

end Zero

/-- The zerocheck as a check of `RecParts`: where its calls hold and `ZeroCert.okIn` passes, its test holds and the
triple's claims are the quirky extensions `a*`, `b*`, `c*` at `(ζ, χ)` (the lincheck's input), its input claim is the
honest instance `zeroInst`'s sum at the eq point off its event `sumcheckFalse`. -/
theorem zero_part {c : Cert} {s : State} {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)}
    {st : ℕ → Fin 4 → K} {val : (ℕ → K) → Val} {zc : ZeroCert} {sc : SumcheckCert} {T' : ℕ → E} (ρ : ℕ → K)
    (hF : Facts cs rl os st (val ρ)) (h : zc.okIn os c.sumchecks cs rl = true) (hsc : c.sumchecks[zc.sc]? = some sc)
    (T : Tables)
    (hchal : ∀ j : Fin sc.rounds.length,
      Model.ev (val ρ) (sc.rounds.getD j default).chal = readR (chalWords c.outs sc.chals) ρ j)
    (htest : ∀ a b, s.unions[sc.test]? = some (a, b) → val ρ a = val ρ b)
    (ha : Model.ev (val ρ) zc.tri.1 =
      MvPolynomial.eval (sc.chalPt (val ρ)) (quirky sc.rounds.length T.a (zc.zeta (val ρ))))
    (hb : Model.ev (val ρ) zc.tri.2.1 =
      MvPolynomial.eval (sc.chalPt (val ρ)) (quirky sc.rounds.length T.b (zc.zeta (val ρ))))
    (hc : Model.ev (val ρ) zc.tri.2.2 =
      MvPolynomial.eval (sc.chalPt (val ρ)) (quirky sc.rounds.length T.c (zc.zeta (val ρ))))
    (hnot : ¬ sumcheckFalse c s sc (zeroInst sc.rounds.length (sc.weightPt (val ρ)) T (zc.zeta (val ρ))) T' val ρ) :
    Model.ev (val ρ) sc.claim0 = (zeroInst sc.rounds.length (sc.weightPt (val ρ)) T (zc.zeta (val ρ))).sum := by
  obtain ⟨-, hres, hhint, -⟩ := ZeroCert.okIn_parts h hsc
  refine sumcheck_part ρ htest ⟨fun w hw => by rw [hhint] at hw; simp at hw, ?_⟩ hnot
  have hχ : readR (chalWords c.outs sc.chals) ρ = sc.chalPt (val ρ) := funext fun j => (hchal j).symm
  rw [hres, List.map_nil, List.sum_nil, add_zero, ZeroCert.final_eq hF h hsc, hχ, zeroInst_final, ← ha, ← hb, ← hc]

/-- The zerocheck's events at the eq point `fixed ++ ρ`, for any length `n = 7 + n'`. -/
theorem no_viol_cast {n n' : ℕ} (hn : n = 7 + n') {r : Fin n → E} {ρ : Fin n' → E}
    (hr : ∀ i : Fin n, r i = Fin.append fixedPt ρ (Fin.cast hn i)) {T : Tables} {v : Fin 64 → E} {ζ : E}
    (heq : (phat v).eval ζ = (zeroInst n r T ζ).sum) (hskip : ζ ∉ skipDraws (phat v) (honestP n r T))
    (hfix : ρ ∉ fixDraws n' T) : ¬ Viol n T := by
  subst hn
  have : r = Fin.append fixedPt ρ := funext fun i => by rw [hr]; rfl
  subst this
  exact no_viol_of_claim heq hskip hfix

/-- The zerocheck's soundness on the `HASH` rows: where its calls hold and `ZeroCert.okIn` passes, its test holds and
the triple's claims are true, every row of the tables holds off its sumcheck's event `sumcheckFalse`, the skip's event
`skipDraws` (the message's polynomial differing from the honest one yet meeting it at `ζ`) and the fixed coordinates'
event `fixDraws` (a broken row whose slices' weighted sums all vanish at the drawn coordinates). -/
theorem zero_rows {c : Cert} {s : State} {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)}
    {st : ℕ → Fin 4 → K} {val : (ℕ → K) → Val} {zc : ZeroCert} {sc : SumcheckCert} {T' : ℕ → E} (ρ : ℕ → K)
    (hF : Facts cs rl os st (val ρ)) (h : zc.okIn os c.sumchecks cs rl = true) (hsc : c.sumchecks[zc.sc]? = some sc)
    (T : Tables)
    (hchal : ∀ j : Fin sc.rounds.length,
      Model.ev (val ρ) (sc.rounds.getD j default).chal = readR (chalWords c.outs sc.chals) ρ j)
    (htest : ∀ a b, s.unions[sc.test]? = some (a, b) → val ρ a = val ρ b)
    (ha : Model.ev (val ρ) zc.tri.1 =
      MvPolynomial.eval (sc.chalPt (val ρ)) (quirky sc.rounds.length T.a (zc.zeta (val ρ))))
    (hb : Model.ev (val ρ) zc.tri.2.1 =
      MvPolynomial.eval (sc.chalPt (val ρ)) (quirky sc.rounds.length T.b (zc.zeta (val ρ))))
    (hc : Model.ev (val ρ) zc.tri.2.2 =
      MvPolynomial.eval (sc.chalPt (val ρ)) (quirky sc.rounds.length T.c (zc.zeta (val ρ))))
    (hnot : ¬ sumcheckFalse c s sc (zeroInst sc.rounds.length (sc.weightPt (val ρ)) T (zc.zeta (val ρ))) T' val ρ)
    (hskip : zc.zeta (val ρ) ∉ skipDraws (phat (zc.msg (val ρ))) (honestP sc.rounds.length (sc.weightPt (val ρ)) T))
    (hfix : zc.outerPt (val ρ) ∉ fixDraws zc.outer.length T) :
    ¬ Viol sc.rounds.length T := by
  have hsum := zero_part ρ hF h hsc T hchal htest ha hb hc hnot
  rw [ZeroCert.claim0_eq hF h hsc] at hsum
  obtain ⟨-, -, -, -, -, hw, -⟩ := ZeroCert.okIn_parts h hsc
  obtain ⟨hn, -, -⟩ := ZeroCert.weights_parts hw
  exact no_viol_cast hn (ZeroCert.point_eq hF h hsc hn) hsum hskip hfix

/-! Non-vacuity of the triple's premises: the honest triple meets the terminal, so the test passes at the honest
instance's final value whatever the tables. -/

example (n : ℕ) (r : Fin n → E) (T : Tables) (ζ : E) (χ : Fin n → E) :
    MvPolynomial.eval χ (quirky n T.a ζ) * MvPolynomial.eval χ (quirky n T.b ζ) + MvPolynomial.eval χ (quirky n T.c ζ) =
      (zeroInst n r T ζ).final χ :=
  (zeroInst_final n r T ζ χ).symm

/-- Non-vacuity of the skip's premise: with every row holding, the honest message's claim is the honest sum at every
`ζ`, so the comparison holds and `ζ` is outside the skip's event. -/
example {n : ℕ} (r : Fin n → E) {T : Tables} (h : ¬ Viol n T) (ζ : E) :
    (phat fun i => (honestP n r T).eval (lNode i)).eval ζ = (zeroInst n r T ζ).sum ∧
      ζ ∉ skipDraws (phat fun i => (honestP n r T).eval (lNode i)) (honestP n r T) := by
  classical
  rw [phat_honest r h, honestP_eval]
  exact ⟨rfl, by simp [skipDraws]⟩

/-! Mutation tests of the checks' rules, on calls whose call `j` outputs wire `100 + j`. -/

/-- The skip's calls on one node `70`, coefficients `1, ..., 6`, constant `50`, scale `60`, at `ζ` = wire 7 and the
value wire 9. -/
def mutSkipCalls : Array Call := #[.mul 7 7, .mul 100 100, .mul 101 101, .mul 102 102, .mul 103 103, .mul 104 104,
  .mulConstAdd 7 1 0 0 105, .mulConstAdd 100 2 0 0 106, .mulConstAdd 101 3 0 0 107, .mulConstAdd 102 4 0 0 108,
  .mulConstAdd 103 5 0 0 109, .mulConstAdd 104 6 0 0 110, .eConst 50 0 0, .add 111 112, .mul 111 113, .zero,
  .mulConstAdd 114 60 0 0 115, .zero, .eConst 70 0 0, .add 7 118, .inv 119, .mulAdd 9 120 117, .mul 116 121]

def mutSkip : SkipCert := {
  zeta := 7, sqAt := [0, 1, 2, 3, 4, 5], vanAt := [6, 7, 8, 9, 10, 11], offAt := 12, onAt := 13, bothAt := 14,
  scaleZero := 15, scaleAt := 16, nodeAt := [18], diffAt := [19], invAt := [20], values := [9], sumZero := 17,
  sumAt := [21], claimAt := 22 }

/-- The skip's check on the calls `cs` for the constants `cw`, `off`, `d` and the nodes. -/
def mutSkipOk (cs : Array Call) (cw : List ℕ) (off d : ℕ) (nodes : List ℕ) : Bool :=
  mutSkip.okWith (mutOuts 23) cs #[] cw off d nodes

example : mutSkipOk mutSkipCalls [1, 2, 3, 4, 5, 6] 50 60 [70] = true := by decide +kernel

/-- Another node constant, coefficient, coset constant or scale fails. -/
example : mutSkipOk mutSkipCalls [1, 2, 3, 4, 5, 6] 50 60 [71] = false := by decide +kernel
example : mutSkipOk mutSkipCalls [1, 2, 3, 4, 5, 7] 50 60 [70] = false := by decide +kernel
example : mutSkipOk mutSkipCalls [1, 2, 3, 4, 5, 6] 51 60 [70] = false := by decide +kernel
example : mutSkipOk mutSkipCalls [1, 2, 3, 4, 5, 6] 50 61 [70] = false := by decide +kernel

/-- The claim reading the sum's `zero` instead of its last term fails, and so does a skipped square. -/
example : mutSkipOk (mutSkipCalls.set! 22 (.mul 116 117)) [1, 2, 3, 4, 5, 6] 50 60 [70] = false := by decide +kernel
example : mutSkipOk (mutSkipCalls.set! 2 (.mul 100 100)) [1, 2, 3, 4, 5, 6] 50 60 [70] = false := by decide +kernel

/-- The value paired with another wire's inverse, or the inverse replaced by a product, fails. -/
example : mutSkipOk (mutSkipCalls.set! 21 (.mulAdd 9 119 117)) [1, 2, 3, 4, 5, 6] 50 60 [70] = false := by
  decide +kernel
example : mutSkipOk (mutSkipCalls.set! 20 (.mul 119 119)) [1, 2, 3, 4, 5, 6] 50 60 [70] = false := by decide +kernel

/-- The terminal `mul_add(1, mul_add(a, b, c), 0)` on the triple `(1, 2, 3)`: it passes; `b` and `c` swapped, or the
weight not `one`, fail. -/
def mutTerm : ZeroCert := {
  sc := 0, skip := mutSkip, tri := (1, 2, 3), valueAt := 0, oneAt := 1, termZero := 2, termAt := 3 }

example : callsOk #[.mulAdd 1 2 3, .one, .zero, .mulAdd 101 100 102] #[] (mutTerm.termCalls (mutOuts 4)) = true := by
  decide +kernel
example : callsOk #[.mulAdd 1 3 2, .one, .zero, .mulAdd 101 100 102] #[] (mutTerm.termCalls (mutOuts 4)) = false := by
  decide +kernel
example : callsOk #[.mulAdd 1 2 3, .zero, .zero, .mulAdd 101 100 102] #[] (mutTerm.termCalls (mutOuts 4)) = false := by
  decide +kernel

/-- The fixed coordinates' `e_const`s in order pass; a changed limb, or two coordinates swapped, fail. -/
def mutFixedCalls : Array Call := ((List.range 7).map fun j => let w := fixedWords.getD j (0, 0, 0)
  Call.eConst w.1 w.2.1 w.2.2).toArray

def mutFixed : ZeroCert := { mutTerm with fixedAt := [0, 1, 2, 3, 4, 5, 6] }

example : callsOk mutFixedCalls #[] mutFixed.fixedCalls = true := by decide +kernel
example : callsOk (mutFixedCalls.set! 4 (.eConst 7200243516802924451 16251485319816311889 0)) #[] mutFixed.fixedCalls =
    false := by decide +kernel
example : callsOk mutFixedCalls #[] { mutFixed with fixedAt := [1, 0, 2, 3, 4, 5, 6] }.fixedCalls = false := by
  decide +kernel

/-- Seven rounds weighted by the fixed coordinates' wires and one by the drawn wire `9` pass; a round weighted by
another wire, no weight, or a missing round fail. -/
def mutRound (w : Option ℕ) : RoundCert := { (default : RoundCert) with weight := w }

def mutRounds : List RoundCert := ((List.range 7).map fun j => mutRound (some (100 + j))) ++ [mutRound (some 9)]

/-- The weights' check on rounds `rs`. -/
def mutWeightsOk (rs : List RoundCert) : Bool :=
  { mutFixed with outer := [9] }.weightsOk (mutOuts 7) { (default : SumcheckCert) with rounds := rs }

example : mutWeightsOk mutRounds = true := by decide +kernel
example : mutWeightsOk (mutRounds.set 3 (mutRound (some 9))) = false := by decide +kernel
example : mutWeightsOk (mutRounds.set 7 (mutRound none)) = false := by decide +kernel
example : mutWeightsOk (mutRounds.take 7) = false := by decide +kernel

/-! Naming the certificate on a replay. -/

/-- `first_round_at`'s calls behind an input claim `claim0`: the last `mul(scale, sum)`, the scale's `mul_const_add`
of `mul(V_S, add(V_S, off))`, `V_S`'s fold back to `ζ^64` and the squares from `ζ`, and the Lagrange sum back to its
`zero`, each term's inverse, difference and node. -/
def skipOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (claim0 : ℕ) : Option SkipCert := Id.run do
  let some (claimAt, scaleW, sumW) := makerBy rp idx claim0 (fun j c => match c with
    | .mul a b => some (j, a, b)
    | _ => none) | return none
  let some (scaleAt, bothW, zW) := makerBy rp idx scaleW (fun j c => match c with
    | .mulConstAdd a _ 0 0 d => some (j, a, d)
    | _ => none) | return none
  let some scaleZero := zeroAt rp idx zW | return none
  let some (bothAt, vanW1, onW) := makerBy rp idx bothW (fun j c => match c with
    | .mul a b => some (j, a, b)
    | _ => none) | return none
  let some (onAt, offW) := makerBy rp idx onW (fun j c => match c with
    | .add a b => if a = vanW1 then some (j, b) else none
    | _ => none) | return none
  let some offAt := makerBy rp idx offW (fun j c => match c with
    | .eConst .. => some j
    | _ => none) | return none
  -- `V_S`'s fold, back from `V_S(ζ)` to `ζ^64`.
  let mut cur := vanW1
  let mut vanAt : List ℕ := []
  let mut pows : List ℕ := []
  for _ in [0:6] do
    let some (j, p, acc) := makerBy rp idx cur (fun j c => match c with
      | .mulConstAdd p _ 0 0 acc => some (j, p, acc)
      | _ => none) | return none
    vanAt := j :: vanAt
    pows := p :: pows
    cur := acc
  -- The squares: `pows` are `ζ^(2^j)` for `j < 6`, then `ζ^64`.
  let all := pows ++ [cur]
  let mut sqAt : List ℕ := []
  for j in [0:6] do
    let x := all.getD j 0
    let some sq := makerBy rp idx (all.getD (j + 1) 0) (fun i c => match c with
      | .mul a b => if a = x ∧ b = x then some i else none
      | _ => none) | return none
    sqAt := sqAt ++ [sq]
  -- The Lagrange sum, back to its `zero`.
  cur := sumW
  let mut sumAt : List ℕ := []
  let mut values : List ℕ := []
  let mut invs : List ℕ := []
  for _ in [0:64] do
    let some (j, v, h, acc) := makerBy rp idx cur (fun j c => match c with
      | .mulAdd v h acc => some (j, v, h, acc)
      | _ => none) | return none
    sumAt := j :: sumAt
    values := v :: values
    invs := h :: invs
    cur := acc
  let some sumZero := zeroAt rp idx cur | return none
  let mut invAt : List ℕ := []
  let mut diffAt : List ℕ := []
  let mut nodeAt : List ℕ := []
  for h in invs do
    let some (i, d) := makerBy rp idx h (fun i c => match c with
      | .inv d => some (i, d)
      | _ => none) | return none
    let some (a, nw) := makerBy rp idx d (fun a c => match c with
      | .add _ nw => some (a, nw)
      | _ => none) | return none
    let some n := makerBy rp idx nw (fun n c => match c with
      | .eConst .. => some n
      | _ => none) | return none
    invAt := invAt ++ [i]
    diffAt := diffAt ++ [a]
    nodeAt := nodeAt ++ [n]
  return some {
    zeta := pows.headD 0, sqAt, vanAt, offAt, onAt, bothAt, scaleZero, scaleAt, nodeAt, diffAt, invAt, values,
    sumZero, sumAt, claimAt }

/-- The zerocheck certificate of sumcheck `k`: its terminal by the calls making its final value (`mul_add(1, value,
0)` and `mul_add(a, b, c)`), the skip behind its input claim, the `e_const`s of its first seven weights, and its later
weights as the drawn coordinates. -/
def zeroOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (scs : Array SumcheckCert) (k : ℕ) :
    Option ZeroCert := Id.run do
  let some sc := scs[k]? | return none
  if sc.deg ≠ 2 ∨ !sc.resid.isEmpty ∨ sc.rounds.length < 7 then return none
  let made := idx.getD sc.final #[]
  let some (termAt, oneW, zW) := made.findSome? (fun (j, p) => if p ≠ 0 then none else
    match rp.calls.getD j .zero with
    | .mulAdd one v z => if v = sc.final then some (j, one, z) else none
    | _ => none) | return none
  let some (valueAt, a, b, c) := made.findSome? (fun (j, p) => if p ≠ 0 then none else
    match rp.calls.getD j .zero with
    | .mulAdd a b c => if b ≠ sc.final then some (j, a, b, c) else none
    | _ => none) | return none
  let some oneAt := makerBy rp idx oneW (fun j c => match c with
    | .one => some j
    | _ => none) | return none
  let some termZero := zeroAt rp idx zW | return none
  let some skip := skipOf rp idx sc.claim0 | return none
  let weightOf := fun (i : ℕ) => (sc.rounds.getD i default).weight.getD 0
  let some fixedAt := (List.range 7).mapM (fun j => makerBy rp idx (weightOf j) fun i c => match c with
    | .eConst .. => some i
    | _ => none) | return none
  let outer := (List.range (sc.rounds.length - 7)).map fun j => weightOf (7 + j)
  return some { sc := k, skip, fixedAt, outer, tri := (a, b, c), valueAt, oneAt, termZero, termAt }

/-- The zerocheck certificates of a replay's certified sumchecks `scs`, read with the outputs `os` and the relaxed
calls `rl` (`Report.scs`, `Report.outs`, `Report.relax`): those `zeroOf` names that pass `okIn`. -/
def zerosOf (rp : Replay) (scs : Array SumcheckCert) (os : Array (List ℕ)) (rl : Array Bool) : Array ZeroCert :=
  let idx := outIndex rp
  ((List.range scs.size).filterMap (zeroOf rp idx scs)).toArray.filter (·.okIn os scs rp.calls rl)

end LeanVMCircuits.Rec.Bind
