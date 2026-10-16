module

public import LeanVMCircuits.Rec.UnionRows
public import LeanVMCircuits.Rec.Sumcheck

@[expose] public section

/-!
A sumcheck's rounds, read off the builder's calls.

Every sumcheck of the recursion verifier reads its round polynomials with `Verifier::read_round` and takes the next
claim with `poly_eval`: the prover sends every coefficient but one, and the verifier computes the fixed one from the
running claim (the linear one, `c_1 = claim + ∑_{i ≥ 2} c_i`, or with the round's eq weight `e` factored out the
constant one, `c_0 = claim + e · ∑_{i ≥ 1} c_i`), so the round's check holds by construction. The reduction's only
test is the last: the last claim against the value the verifier computes for it.

A round certificate (`RoundCert`) names the calls: the fold of the coefficients past the fixed one, the fixed
coefficient's call, the challenge, and Horner's `mul_add` per coefficient from the last. `RoundCert.ok` checks each
named call is in the replay with the wires the code gives it. A sumcheck certificate (`SumcheckCert`) chains rounds,
each round's claim the previous round's Horner output, from the reduction's input claim.

A proof-of-work certificate (`PowCert`) names `Transcript::check_pow`'s calls: the trial's compression, its words, the
split of its first word, and the tests holding the word's top `bits` bits to zero. `pow_sem`: where every replayed
call but the trial's compression holds (`FactsBut`) and the tests hold, the trial compression's first output word is
below `2^(64 - bits)`.

`sumRound_sem`: in an assignment where every replayed call holds, the round polynomial `g` of the coefficients' values
has degree at most the certificate's, passes the round's check against the claim (`Sumcheck.lin`), and the next claim
is `g` at the challenge.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Polynomial

/-- `fold(acc, |acc, &c| v.add(acc, c))`: one `add` per wire. -/
def foldCalls (os : Array (List ℕ)) (acc : ℕ) : List ℕ → List ℕ → List (ℕ × Call)
  | c :: cs, j :: js => (j, .add acc c) :: foldCalls os (outAt os j 0) cs js
  | _, _ => []

/-- The fold's output. -/
def foldOut (os : Array (List ℕ)) (acc : ℕ) : List ℕ → List ℕ → ℕ
  | _ :: cs, j :: js => foldOut os (outAt os j 0) cs js
  | _, _ => acc

/-- Horner at `x` from `acc`: one `mul_add(acc, x, c)` per wire. -/
def hornerCalls (os : Array (List ℕ)) (x acc : ℕ) : List ℕ → List ℕ → List (ℕ × Call)
  | c :: cs, j :: js => (j, .mulAdd acc x c) :: hornerCalls os x (outAt os j 0) cs js
  | _, _ => []

/-- Horner's output. -/
def hornerOut (os : Array (List ℕ)) (acc : ℕ) : List ℕ → List ℕ → ℕ
  | _ :: cs, j :: js => hornerOut os (outAt os j 0) cs js
  | _, _ => acc

/-- One round of a sumcheck: its coefficient wires, constant first, the fixed one included; its eq weight when
factored out; the calls making the fixed coefficient (a `zero`, an `add` per coefficient past the fixed one, then the
fixed one's); its challenge and Horner's calls (a `zero`, then a `mul_add` per coefficient from the last); where the
challenge is drawn (its `k_to_e` call, and for each word the `d_to_k` call, the word's place, and the squeeze); and the
number of its transcript's blocks absorbed before that squeeze. -/
structure RoundCert where
  coeffs : List ℕ
  weight : Option ℕ
  tailZero : ℕ
  tailAt : List ℕ
  fixedAt : ℕ
  chal : ℕ
  hornerZero : ℕ
  hornerAt : List ℕ
  chalAt : ℕ
  words : List (ℕ × ℕ × ℕ)
  time : ℕ
  deriving Inhabited, Repr

namespace RoundCert

variable (os : Array (List ℕ)) (rc : RoundCert)

/-- The fixed coefficient's index: the constant one with an eq weight, else the linear one. -/
def fixed : ℕ := if rc.weight.isSome then 0 else 1

/-- The coefficients past the fixed one, summed. -/
def tail : ℕ := foldOut os (o os rc.tailZero) (rc.coeffs.drop (rc.fixed + 1)) rc.tailAt

/-- The next claim: the round polynomial at the challenge. -/
def next : ℕ := hornerOut os (o os rc.hornerZero) rc.coeffs.reverse rc.hornerAt

/-- The fixed coefficient's call: `claim + e · tail` or `claim + tail`. -/
def fixedCall (claim : ℕ) : Call := match rc.weight with
  | some e => .mulAdd e (rc.tail os) claim
  | none => .add claim (rc.tail os)

/-- The round's calls. -/
def calls (claim : ℕ) : List (ℕ × Call) :=
  [(rc.tailZero, .zero), (rc.hornerZero, .zero), (rc.fixedAt, rc.fixedCall os claim)] ++
    foldCalls os (o os rc.tailZero) (rc.coeffs.drop (rc.fixed + 1)) rc.tailAt ++
    hornerCalls os rc.chal (o os rc.hornerZero) rc.coeffs.reverse rc.hornerAt

/-- The round's calls are in the replay, its polynomial has `d + 1` coefficients, and the fixed coefficient is the
fixed call's output. -/
def ok (cs : Array Call) (rl : Array Bool) (d claim : ℕ) : Bool :=
  rc.coeffs.length == d + 1 && 2 ≤ rc.coeffs.length && rc.tailAt.length + rc.fixed + 1 == rc.coeffs.length &&
    rc.hornerAt.length == rc.coeffs.length && o os rc.fixedAt == rc.coeffs.getD rc.fixed 0 &&
    callsOk cs rl (rc.calls os claim)

/-- The coefficients the prover sends: all but the fixed one. -/
def sent : List ℕ := rc.coeffs.eraseIdx rc.fixed

end RoundCert

/-- A residual's chain from `acc`: one `mul_add(w, s, acc)` per term, each its weight, its summand and its call. -/
def residCalls (os : Array (List ℕ)) (acc : ℕ) : List (ℕ × ℕ × ℕ) → List (ℕ × Call)
  | (w, s, j) :: ts => (j, .mulAdd w s acc) :: residCalls os (o os j) ts
  | [] => []

/-- The residual chain's output. -/
def residOut (os : Array (List ℕ)) (acc : ℕ) : List (ℕ × ℕ × ℕ) → ℕ
  | (_, _, j) :: ts => residOut os (o os j) ts
  | [] => acc

/-- A sumcheck: its input claim, its rounds, their degree, its test (an equality of the circuit, between its last
side and `final`) and its transcript. The last side is the last claim, or with residual terms (the table sumcheck's
`residual = mul_add(weight, summand, residual)` from the last claim, `constraints::verify`) the residual. -/
structure SumcheckCert where
  claim0 : ℕ
  rounds : List RoundCert
  deg : ℕ
  test : ℕ
  final : ℕ
  transcript : ℕ
  resid : List (ℕ × ℕ × ℕ) := []
  /-- The hints the input claim reads that no transcript binds (the table sumcheck's target reads hinted
  fixed-column evaluations, claims deferred to the reduction), and the firings binding the input claim with them as
  seeds. -/
  hints : List ℕ := []
  hintFirings : Array ℕ := #[]
  deriving Inhabited, Repr

namespace SumcheckCert

variable (os : Array (List ℕ)) (sc : SumcheckCert)

/-- Round `i`'s claim: the input claim, then each round's next claim. -/
def claimAt (i : ℕ) : ℕ := if i = 0 then sc.claim0 else (sc.rounds.getD (i - 1) default).next os

/-- The test's side: the residual chain from the last claim. -/
def side : ℕ := residOut os (sc.claimAt os sc.rounds.length) sc.resid

/-- Every round's calls are in the replay, each round reading the claim the previous one leaves, and so are the
residual's. -/
def ok (cs : Array Call) (rl : Array Bool) : Bool :=
  0 < sc.rounds.length &&
    ((List.range sc.rounds.length).all fun i => (sc.rounds.getD i default).ok os cs rl sc.deg (sc.claimAt os i)) &&
    callsOk cs rl (residCalls os (sc.claimAt os sc.rounds.length) sc.resid)

end SumcheckCert

/-- A proof-of-work check: the trial's `compress` call, the `d_to_k` of its digest, the `split` of its first word,
its difficulty, and the `eq_k_const` tests of the word's top bits, from bit `64 - bits` up. -/
structure PowCert where
  compressAt : ℕ
  dkAt : ℕ
  splitAt : ℕ
  bits : ℕ
  testAt : List ℕ
  deriving Inhabited, Repr

namespace PowCert

variable (os : Array (List ℕ)) (pc : PowCert)

/-- The trial's digest, its first word, and the word's bit `k`. -/
def trial : ℕ := o os pc.compressAt
def word : ℕ := outAt os pc.dkAt 0
def bit (k : ℕ) : ℕ := outAt os pc.splitAt k

/-- The calls are in the replay, and each top bit has its test. -/
def ok (cs : Array Call) (rl : Array Bool) : Bool :=
  pc.bits ≤ 64 && pc.testAt.length == pc.bits &&
    (match cs[pc.compressAt]? with
      | some (.compress acc x ds) =>
        callsOk cs rl [(pc.compressAt, .compress acc x ds), (pc.dkAt, .dToK (pc.trial os)),
          (pc.splitAt, .split (pc.word os))]
      | _ => false) &&
    (List.range pc.bits).all fun k => cs[pc.testAt.getD k 0]? == some (.eqConstK (pc.bit os (64 - pc.bits + k)) 0)

end PowCert

/-- A challenge: its wire; its `k_to_e` call and, per word, the `d_to_k` call, the word's place and the squeeze; and
the number of its transcript's blocks absorbed before that squeeze. -/
structure ChalCert where
  chal : ℕ
  chalAt : ℕ
  words : List (ℕ × ℕ × ℕ)
  time : ℕ
  deriving Inhabited, Repr

/-- GKR's odd layer (`gkr::verify_products`' binary layer, which runs no sumcheck): the input claims combined at `λ`
by Horner (`claimAt`), each value's two children and their product (`prodAt`), the products combined at `λ`
(`expAt`), the test of the two, and each value's line through its children at the next challenge (`sumAt`, then
`outAt`: `l + r' · (l + r)`). -/
structure OddCert where
  values : List ℕ
  lam : ChalCert
  claimZero : ℕ
  claimAt : List ℕ
  lefts : List ℕ
  rights : List ℕ
  prodAt : List ℕ
  expZero : ℕ
  expAt : List ℕ
  test : ℕ
  next : ChalCert
  sumAt : List ℕ
  outAt : List ℕ
  transcript : ℕ
  deriving Inhabited, Repr

namespace OddCert

variable (os : Array (List ℕ)) (oc : OddCert)

/-- The number of values, a child's wires, the products, the two combinations and each value's next claim. -/
def m : ℕ := oc.values.length
def left (k : ℕ) : ℕ := oc.lefts.getD k 0
def right (k : ℕ) : ℕ := oc.rights.getD k 0
def prods : List ℕ := (List.range oc.m).map fun k => o os (oc.prodAt.getD k 0)
def claim : ℕ := hornerOut os (o os oc.claimZero) oc.values.reverse oc.claimAt
def expected : ℕ := hornerOut os (o os oc.expZero) (oc.prods os).reverse oc.expAt
def out (k : ℕ) : ℕ := o os (oc.outAt.getD k 0)

/-- The layer's calls. -/
def calls : List (ℕ × Call) :=
  [(oc.claimZero, .zero), (oc.expZero, .zero)] ++
    hornerCalls os oc.lam.chal (o os oc.claimZero) oc.values.reverse oc.claimAt ++
    hornerCalls os oc.lam.chal (o os oc.expZero) (oc.prods os).reverse oc.expAt ++
    (List.range oc.m).flatMap fun k => [(oc.prodAt.getD k 0, .mul (oc.left k) (oc.right k)),
      (oc.sumAt.getD k 0, .add (oc.left k) (oc.right k)),
      (oc.outAt.getD k 0, .mulAdd oc.next.chal (o os (oc.sumAt.getD k 0)) (oc.left k))]

/-- The layer's calls are in the replay. -/
def ok (cs : Array Call) (rl : Array Bool) : Bool :=
  0 < oc.m && oc.claimAt.length == oc.m && oc.expAt.length == oc.m && callsOk cs rl (oc.calls os)

end OddCert

/-- The line through `(0, x)` and `(1, y)` at `t` in characteristic two, `Arith::interp`: `x + t · (x + y)`. -/
noncomputable def lineE (x y t : E) : E := x + t * (x + y)

/-- GKR's radix-four layer with an empty point (`gkr::verify_products`' top layer at an even depth, which runs no
sumcheck): the input claims combined at `λ` by Horner, each value's four children and their product (`prodAt`: the
`one` call, then a `mul` per child), the products combined at `λ`, the test of the two, and each value's next claim at
the next two challenges (`lineAt`: `interp(a, b, low)`, `interp(c, d, low)`, then their `interp` at `high`, each an
`add` and a `mul_add`). -/
structure TopCert where
  values : List ℕ
  lam : ChalCert
  claimZero : ℕ
  claimAt : List ℕ
  kids : List (List ℕ)
  prodAt : List (List ℕ)
  expZero : ℕ
  expAt : List ℕ
  test : ℕ
  low : ChalCert
  high : ChalCert
  lineAt : List (List ℕ)
  transcript : ℕ
  deriving Inhabited, Repr

namespace TopCert

variable (os : Array (List ℕ)) (tc : TopCert)

/-- The number of values, child `i` of value `k`, and the calls of value `k`'s product and next claim. -/
def m : ℕ := tc.values.length
def kid (k i : ℕ) : ℕ := (tc.kids.getD k []).getD i 0
def pAt (k i : ℕ) : ℕ := (tc.prodAt.getD k []).getD i 0
def lAt (k i : ℕ) : ℕ := (tc.lineAt.getD k []).getD i 0
def prods : List ℕ := (List.range tc.m).map fun k => o os (tc.pAt k 4)
def claim : ℕ := hornerOut os (o os tc.claimZero) tc.values.reverse tc.claimAt
def expected : ℕ := hornerOut os (o os tc.expZero) (tc.prods os).reverse tc.expAt
def out (k : ℕ) : ℕ := o os (tc.lAt k 5)

/-- Value `k`'s product of its children, from a `one`. -/
def prodCalls (k : ℕ) : List (ℕ × Call) :=
  [(tc.pAt k 0, .one), (tc.pAt k 1, .mul (o os (tc.pAt k 0)) (tc.kid k 0)),
    (tc.pAt k 2, .mul (o os (tc.pAt k 1)) (tc.kid k 1)), (tc.pAt k 3, .mul (o os (tc.pAt k 2)) (tc.kid k 2)),
    (tc.pAt k 4, .mul (o os (tc.pAt k 3)) (tc.kid k 3))]

/-- Value `k`'s next claim: two lines at `low`, then the line through them at `high`. -/
def lineCalls (k : ℕ) : List (ℕ × Call) :=
  [(tc.lAt k 0, .add (tc.kid k 0) (tc.kid k 1)), (tc.lAt k 1, .mulAdd tc.low.chal (o os (tc.lAt k 0)) (tc.kid k 0)),
    (tc.lAt k 2, .add (tc.kid k 2) (tc.kid k 3)), (tc.lAt k 3, .mulAdd tc.low.chal (o os (tc.lAt k 2)) (tc.kid k 2)),
    (tc.lAt k 4, .add (o os (tc.lAt k 1)) (o os (tc.lAt k 3))),
    (tc.lAt k 5, .mulAdd tc.high.chal (o os (tc.lAt k 4)) (o os (tc.lAt k 1)))]

/-- The layer's calls. -/
def calls : List (ℕ × Call) :=
  [(tc.claimZero, .zero), (tc.expZero, .zero)] ++
    hornerCalls os tc.lam.chal (o os tc.claimZero) tc.values.reverse tc.claimAt ++
    hornerCalls os tc.lam.chal (o os tc.expZero) (tc.prods os).reverse tc.expAt ++
    (List.range tc.m).flatMap fun k => tc.prodCalls os k ++ tc.lineCalls os k

/-- The layer's calls are in the replay. -/
def ok (cs : Array Call) (rl : Array Bool) : Bool :=
  0 < tc.m && tc.claimAt.length == tc.m && tc.expAt.length == tc.m && callsOk cs rl (tc.calls os)

end TopCert

/-- `square` calls from `x`, each squaring the last. -/
def squaresCalls (os : Array (List ℕ)) (x : ℕ) : List ℕ → List (ℕ × Call)
  | j :: js => (j, .square x) :: squaresCalls os (o os j) js
  | [] => []

/-- Their output: `x^(2^n)`. -/
def squaresOut (os : Array (List ℕ)) (x : ℕ) : List ℕ → ℕ
  | j :: js => squaresOut os (o os j) js
  | [] => x

/-- A claim split into point claims (`design::program_claims`): from `acc`, one `mul_add(c, h^(2^e), acc)` per term,
each its coefficient `c`, its hint `h`, the `square` calls raising it and the `mul_add`. -/
def termsCalls (os : Array (List ℕ)) (acc : ℕ) : List (ℕ × ℕ × List ℕ × ℕ) → List (ℕ × Call)
  | (c, h, sq, j) :: ts => squaresCalls os h sq ++ (j, .mulAdd c (squaresOut os h sq) acc) :: termsCalls os (o os j) ts
  | [] => []

/-- The split's total. -/
def termsOut (os : Array (List ℕ)) (acc : ℕ) : List (ℕ × ℕ × List ℕ × ℕ) → ℕ
  | (_, _, _, j) :: ts => termsOut os (o os j) ts
  | [] => acc

/-- A claim's split into point claims: the `zero` its total starts from, its terms, and the test of the total against
the claim's value `value`. -/
structure SplitCert where
  zeroAt : ℕ
  terms : List (ℕ × ℕ × List ℕ × ℕ)
  test : ℕ
  value : ℕ
  deriving Inhabited, Repr

namespace SplitCert

variable (os : Array (List ℕ)) (pc : SplitCert)

def total : ℕ := termsOut os (o os pc.zeroAt) pc.terms

/-- The split's calls are in the replay. -/
def ok (cs : Array Call) (rl : Array Bool) : Bool :=
  callsOk cs rl ((pc.zeroAt, .zero) :: termsCalls os (o os pc.zeroAt) pc.terms)

end SplitCert

/-! What the calls give. -/

section Sem

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}

theorem callsOk_cons {x : ℕ × Call} {l : List (ℕ × Call)} (h : callsOk cs rl (x :: l) = true) :
    callsOk cs rl [x] = true ∧ callsOk cs rl l = true := by
  rw [show x :: l = [x] ++ l from rfl, callsOk_append, Bool.and_eq_true] at h
  exact h

theorem fold_sem (hF : Facts cs rl os st val) : ∀ (acc : ℕ) (ws js : List ℕ), ws.length = js.length →
    callsOk cs rl (foldCalls os acc ws js) = true →
      Model.ev val (foldOut os acc ws js) = Model.ev val acc + (ws.map (Model.ev val)).sum
  | acc, [], [], _, _ => by simp [foldOut]
  | acc, w :: ws, j :: js, hl, h => by
    obtain ⟨h1, h2⟩ := callsOk_cons h
    have hj : Model.ev val (o os j) = Model.ev val acc + Model.ev val w := holds_of_mem hF h1 (List.mem_singleton_self _)
    rw [foldOut, fold_sem hF (o os j) ws js (by simpa using hl) h2, hj, List.map_cons, List.sum_cons]
    ring
  | _, [], _ :: _, hl, _ => by simp at hl
  | _, _ :: _, [], hl, _ => by simp at hl

theorem horner_sem (hF : Facts cs rl os st val) (x : ℕ) : ∀ (acc : ℕ) (ws js : List ℕ), ws.length = js.length →
    callsOk cs rl (hornerCalls os x acc ws js) = true →
      Model.ev val (hornerOut os acc ws js) = (ws.map (Model.ev val)).foldl (fun a c => a * Model.ev val x + c) (Model.ev val acc)
  | acc, [], [], _, _ => by simp [hornerOut]
  | acc, w :: ws, j :: js, hl, h => by
    obtain ⟨h1, h2⟩ := callsOk_cons h
    have hj : Model.ev val (o os j) = Model.ev val acc * Model.ev val x + Model.ev val w := holds_of_mem hF h1 (List.mem_singleton_self _)
    rw [hornerOut, horner_sem hF x (o os j) ws js (by simpa using hl) h2, hj, List.map_cons, List.foldl_cons]
  | _, [], _ :: _, hl, _ => by simp at hl
  | _, _ :: _, [], hl, _ => by simp at hl

open Sumcheck in
/-- A round's polynomial, of the coefficients' values, has degree at most `d`, passes the round's check against the
claim, and is the next claim at the challenge. -/
theorem sumRound_sem (hF : Facts cs rl os st val) {rc : RoundCert} {d claim : ℕ}
    (hok : rc.ok os cs rl d claim = true) :
    (polyOf (rc.coeffs.map (Model.ev val))).natDegree ≤ d ∧
      lin (rc.weight.map (Model.ev val)) (polyOf (rc.coeffs.map (Model.ev val))) = Model.ev val claim ∧
      Model.ev val (rc.next os) = (polyOf (rc.coeffs.map (Model.ev val))).eval (Model.ev val rc.chal) := by
  simp only [RoundCert.ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨hlen, hge⟩, htl⟩, hhl⟩, hfx⟩, hcalls⟩ := hok
  simp only [RoundCert.calls, callsOk_append, Bool.and_eq_true] at hcalls
  obtain ⟨⟨hhead, hfold⟩, hhorner⟩ := hcalls
  obtain ⟨hz1, hrest⟩ := callsOk_cons hhead
  obtain ⟨hz2, hfc⟩ := callsOk_cons hrest
  have hz1' : Model.ev val (o os rc.tailZero) = 0 := holds_of_mem hF hz1 (List.mem_singleton_self _)
  have hz2' : Model.ev val (o os rc.hornerZero) = 0 := holds_of_mem hF hz2 (List.mem_singleton_self _)
  have hfc' : (rc.fixedCall os claim).Holds st val (os.getD rc.fixedAt []) :=
    holds_of_mem hF hfc (List.mem_singleton_self _)
  have htail : Model.ev val (rc.tail os) = ((rc.coeffs.drop (rc.fixed + 1)).map (Model.ev val)).sum := by
    rw [RoundCert.tail, fold_sem hF _ _ _ (by simp; omega) hfold, hz1', zero_add]
  refine ⟨(natDegree_polyOf _).trans (by simp; omega), ?_, ?_⟩
  · -- The fixed coefficient is the claim plus the tail, or the claim plus the weight times the tail.
    have hfv : Model.ev val (rc.coeffs.getD rc.fixed 0) = Model.ev val (o os rc.fixedAt) := by rw [hfx]
    match hc : rc.coeffs, hw : rc.weight with
    | c0 :: c1 :: rest, none =>
      have hfix : rc.fixed = 1 := by simp [RoundCert.fixed, hw]
      simp only [RoundCert.fixedCall, hw, Call.Holds] at hfc'
      rw [getD_o] at hfc'
      rw [hfix, hc] at htail hfv
      simp only [List.drop_succ_cons, List.drop_zero, List.getD_cons_succ, List.getD_cons_zero] at htail hfv
      rw [hfc', htail] at hfv
      simp only [Option.map_none, lin, eval_polyOf_zero, eval_polyOf_one, List.map_cons, List.sum_cons, hfv,
        List.head?_cons, Option.getD_some]
      linear_combination (Model.ev val c0 + (rest.map (Model.ev val)).sum) * two_E
    | c0 :: rest, some e =>
      have hfix : rc.fixed = 0 := by simp [RoundCert.fixed, hw]
      simp only [RoundCert.fixedCall, hw, Call.Holds] at hfc'
      rw [getD_o] at hfc'
      rw [hfix, hc] at htail hfv
      simp only [List.drop_succ_cons, List.drop_zero, List.getD_cons_zero] at htail hfv
      rw [hfc', htail] at hfv
      simp only [Option.map_some, lin, eval_polyOf_zero, eval_polyOf_one, List.map_cons, List.sum_cons, hfv,
        List.head?_cons, Option.getD_some]
      linear_combination (Model.ev val e * (rest.map (Model.ev val)).sum) * two_E
    | [], _ => simp [hc] at hge
    | [_], _ => simp [hc] at hge
  · rw [RoundCert.next, horner_sem hF _ _ _ _ (by simp; omega) hhorner, hz2', eval_polyOf, List.map_reverse,
      List.foldl_reverse]

/-- Where every replayed call but the trial's compression holds and the proof-of-work tests hold, the trial digest's
first word is below `2^(64 - bits)`: its top `bits` bits are zero. The trial's compression need not hold: in the ideal
compression model its digest is the oracle's answer. -/
theorem pow_sem {pc : PowCert} (hF : FactsBut cs rl os pc.compressAt st val) (hok : pc.ok os cs rl = true)
    (htests : ∀ k < pc.bits, val (pc.bit os (64 - pc.bits + k)) 0 = 0) :
    toWord (val (PowCert.trial os pc) 0) < 2 ^ (64 - pc.bits) := by
  simp only [PowCert.ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hb, -⟩, hcalls⟩, -⟩ := hok
  split at hcalls
  next acc x ds hc =>
    obtain ⟨-, hrest⟩ := callsOk_cons hcalls
    obtain ⟨h2, h3⟩ := callsOk_cons hrest
    -- The `d_to_k` and `split` calls are not the trial's compression.
    have hne : ∀ {j : ℕ} {c' : Call}, callsOk cs rl [(j, c')] = true → c' ≠ .compress acc x ds →
        j ≠ pc.compressAt := by
      intro j c' hj hc' he
      subst he
      simp only [callsOk, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq, hc] at hj
      exact hc' (Option.some.inj hj.1.1).symm
    have hdk : ∀ i : Fin 4, val (outAt os pc.dkAt i) 0 = val (PowCert.trial os pc) i :=
      holds_of_mem_but hF h2 (List.mem_singleton_self _) (hne h2 fun h => by cases h)
    have hsp : (∀ i < 64, val (PowCert.bit os pc i) 0 = 0 ∨ val (PowCert.bit os pc i) 0 = 1) ∧
        toWord (val (PowCert.word os pc) 0) = num (fun i => if val (PowCert.bit os pc i) 0 = 1 then 1 else 0) 64 :=
      holds_of_mem_but hF h3 (List.mem_singleton_self _) (hne h3 fun h => by cases h)
    have hw : val (PowCert.word os pc) 0 = val (PowCert.trial os pc) 0 := hdk 0
    rw [← hw, hsp.2]
    refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
    by_cases h64 : i < 64
    · rw [testBit_num _ _ _ h64]
      have := htests (i - (64 - pc.bits)) (by omega)
      rw [show 64 - pc.bits + (i - (64 - pc.bits)) = i by omega] at this
      simp [this]
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (num_lt _ 64) (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · simp at hcalls

open Sumcheck in
/-- GKR's odd layer: the claim is the values' polynomial at `λ`, the expected value the children's products', and
each next claim is its value's line through its children at the next challenge. -/
theorem odd_sem (hF : Facts cs rl os st val) {oc : OddCert} (hok : oc.ok os cs rl = true) :
    Model.ev val (oc.claim os) = (polyOf (oc.values.map (Model.ev val))).eval (Model.ev val oc.lam.chal) ∧
      Model.ev val (oc.expected os) = (polyOf ((List.range oc.m).map fun k =>
        Model.ev val (oc.left k) * Model.ev val (oc.right k))).eval (Model.ev val oc.lam.chal) ∧
      ∀ k < oc.m, Model.ev val (oc.out os k) = Model.ev val (oc.left k) +
        Model.ev val oc.next.chal * (Model.ev val (oc.left k) + Model.ev val (oc.right k)) := by
  simp only [OddCert.ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨-, hcl⟩, hel⟩, hcalls⟩ := hok
  simp only [OddCert.calls, callsOk_append, Bool.and_eq_true] at hcalls
  obtain ⟨⟨⟨hz, hh1⟩, hh2⟩, hks⟩ := hcalls
  obtain ⟨hz1, hz2⟩ := callsOk_cons hz
  have hz1' : Model.ev val (o os oc.claimZero) = 0 := holds_of_mem hF hz1 (List.mem_singleton_self _)
  have hz2' : Model.ev val (o os oc.expZero) = 0 := holds_of_mem hF hz2 (List.mem_cons_self ..)
  have hk : ∀ k < oc.m, ∀ x ∈ [(oc.prodAt.getD k 0, Call.mul (oc.left k) (oc.right k)),
      (oc.sumAt.getD k 0, Call.add (oc.left k) (oc.right k)),
      (oc.outAt.getD k 0, Call.mulAdd oc.next.chal (o os (oc.sumAt.getD k 0)) (oc.left k))],
      x.2.Holds st val (os.getD x.1 []) := fun k hk x hx =>
    holds_of_mem hF hks (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, hx⟩)
  have hprods : (oc.prods os).map (Model.ev val) =
      (List.range oc.m).map fun k => Model.ev val (oc.left k) * Model.ev val (oc.right k) := by
    simp only [OddCert.prods, List.map_map]
    refine List.map_congr_left fun k hkm => ?_
    exact hk k (List.mem_range.mp hkm) _ (List.mem_cons_self ..)
  refine ⟨?_, ?_, fun k hkm => ?_⟩
  · rw [OddCert.claim, horner_sem hF _ _ _ _ (by simp [OddCert.m] at hcl ⊢; omega) hh1, hz1', eval_polyOf,
      List.map_reverse, List.foldl_reverse]
  · rw [OddCert.expected, horner_sem hF _ _ _ _ (by simp [OddCert.prods] at hel ⊢; omega) hh2, hz2', eval_polyOf,
      List.map_reverse, List.foldl_reverse, hprods]
  · have hs : Model.ev val (o os (oc.sumAt.getD k 0)) = Model.ev val (oc.left k) + Model.ev val (oc.right k) :=
      hk k hkm _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have ho : Model.ev val (oc.out os k) =
        Model.ev val oc.next.chal * Model.ev val (o os (oc.sumAt.getD k 0)) + Model.ev val (oc.left k) :=
      hk k hkm _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    rw [ho, hs]
    ring

/-- The residual chain is its start plus each weight times its summand. -/
theorem resid_sem (hF : Facts cs rl os st val) : ∀ (acc : ℕ) (ts : List (ℕ × ℕ × ℕ)),
    callsOk cs rl (residCalls os acc ts) = true →
      Model.ev val (residOut os acc ts) =
        Model.ev val acc + (ts.map fun t => Model.ev val t.1 * Model.ev val t.2.1).sum
  | acc, [], _ => by simp [residOut]
  | acc, (w, s, j) :: ts, h => by
    obtain ⟨h1, h2⟩ := callsOk_cons h
    have hj : Model.ev val (o os j) = Model.ev val w * Model.ev val s + Model.ev val acc :=
      holds_of_mem hF h1 (List.mem_singleton_self _)
    rw [residOut, resid_sem hF (o os j) ts h2, hj, List.map_cons, List.sum_cons]
    ring

theorem squares_sem (hF : Facts cs rl os st val) : ∀ (x : ℕ) (js : List ℕ),
    callsOk cs rl (squaresCalls os x js) = true → Model.ev val (squaresOut os x js) = Model.ev val x ^ 2 ^ js.length
  | x, [], _ => by simp [squaresOut]
  | x, j :: js, h => by
    obtain ⟨h1, h2⟩ := callsOk_cons h
    have hj : Model.ev val (o os j) = Model.ev val x * Model.ev val x := holds_of_mem hF h1 (List.mem_singleton_self _)
    rw [squaresOut, squares_sem hF (o os j) js h2, hj, ← sq, ← pow_mul, List.length_cons, pow_succ']

theorem terms_sem (hF : Facts cs rl os st val) : ∀ (acc : ℕ) (ts : List (ℕ × ℕ × List ℕ × ℕ)),
    callsOk cs rl (termsCalls os acc ts) = true →
      Model.ev val (termsOut os acc ts) = Model.ev val acc +
        (ts.map fun t => Model.ev val t.1 * Model.ev val t.2.1 ^ 2 ^ t.2.2.1.length).sum
  | acc, [], _ => by simp [termsOut]
  | acc, (c, h, sq, j) :: ts, hc => by
    simp only [termsCalls, callsOk_append, Bool.and_eq_true] at hc
    obtain ⟨hsq, hrest⟩ := hc
    obtain ⟨h1, h2⟩ := callsOk_cons hrest
    have hj : Model.ev val (o os j) = Model.ev val c * Model.ev val (squaresOut os h sq) + Model.ev val acc :=
      holds_of_mem hF h1 (List.mem_singleton_self _)
    rw [termsOut, terms_sem hF (o os j) ts h2, hj, squares_sem hF h sq hsq, List.map_cons, List.sum_cons]
    ring

/-- A split's total is the sum of its coefficients times their hints' powers. -/
theorem split_sem (hF : Facts cs rl os st val) {pc : SplitCert} (hok : pc.ok os cs rl = true) :
    Model.ev val (pc.total os) =
      (pc.terms.map fun t => Model.ev val t.1 * Model.ev val t.2.1 ^ 2 ^ t.2.2.1.length).sum := by
  unfold SplitCert.ok at hok
  obtain ⟨h1, h2⟩ := callsOk_cons hok
  have hz : Model.ev val (o os pc.zeroAt) = 0 := holds_of_mem hF h1 (List.mem_singleton_self _)
  rw [SplitCert.total, terms_sem hF _ _ h2, hz, zero_add]

open Sumcheck in
/-- GKR's radix-four top layer: the claim is the values' polynomial at `λ`, the expected value the children's
products', and each next claim is its value's children's bilinear interpolation at `low` and `high`. -/
theorem top_sem (hF : Facts cs rl os st val) {tc : TopCert} (hok : tc.ok os cs rl = true) :
    Model.ev val (tc.claim os) = (polyOf (tc.values.map (Model.ev val))).eval (Model.ev val tc.lam.chal) ∧
      Model.ev val (tc.expected os) = (polyOf ((List.range tc.m).map fun k =>
        Model.ev val (tc.kid k 0) * Model.ev val (tc.kid k 1) * Model.ev val (tc.kid k 2) *
          Model.ev val (tc.kid k 3))).eval (Model.ev val tc.lam.chal) ∧
      ∀ k < tc.m, Model.ev val (tc.out os k) =
        lineE (lineE (Model.ev val (tc.kid k 0)) (Model.ev val (tc.kid k 1)) (Model.ev val tc.low.chal))
          (lineE (Model.ev val (tc.kid k 2)) (Model.ev val (tc.kid k 3)) (Model.ev val tc.low.chal))
          (Model.ev val tc.high.chal) := by
  simp only [TopCert.ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨-, hcl⟩, hel⟩, hcalls⟩ := hok
  simp only [TopCert.calls, callsOk_append, Bool.and_eq_true] at hcalls
  obtain ⟨⟨⟨hz, hh1⟩, hh2⟩, hks⟩ := hcalls
  obtain ⟨hz1, hz2⟩ := callsOk_cons hz
  have hz1' : Model.ev val (o os tc.claimZero) = 0 := holds_of_mem hF hz1 (List.mem_singleton_self _)
  have hz2' : Model.ev val (o os tc.expZero) = 0 := holds_of_mem hF hz2 (List.mem_cons_self ..)
  have hk : ∀ k < tc.m, ∀ x ∈ tc.prodCalls os k ++ tc.lineCalls os k, x.2.Holds st val (os.getD x.1 []) :=
    fun k hk x hx => holds_of_mem hF hks (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, hx⟩)
  have hprods : (tc.prods os).map (Model.ev val) = (List.range tc.m).map fun k =>
      Model.ev val (tc.kid k 0) * Model.ev val (tc.kid k 1) * Model.ev val (tc.kid k 2) * Model.ev val (tc.kid k 3) := by
    simp only [TopCert.prods, List.map_map]
    refine List.map_congr_left fun k hkm => ?_
    have hkm := List.mem_range.mp hkm
    have h0 : Model.ev val (o os (tc.pAt k 0)) = 1 :=
      hk k hkm (tc.pAt k 0, .one) (by simp [TopCert.prodCalls])
    have h1 : Model.ev val (o os (tc.pAt k 1)) = Model.ev val (o os (tc.pAt k 0)) * Model.ev val (tc.kid k 0) :=
      hk k hkm (tc.pAt k 1, .mul (o os (tc.pAt k 0)) (tc.kid k 0)) (by simp [TopCert.prodCalls])
    have h2 : Model.ev val (o os (tc.pAt k 2)) = Model.ev val (o os (tc.pAt k 1)) * Model.ev val (tc.kid k 1) :=
      hk k hkm (tc.pAt k 2, .mul (o os (tc.pAt k 1)) (tc.kid k 1)) (by simp [TopCert.prodCalls])
    have h3 : Model.ev val (o os (tc.pAt k 3)) = Model.ev val (o os (tc.pAt k 2)) * Model.ev val (tc.kid k 2) :=
      hk k hkm (tc.pAt k 3, .mul (o os (tc.pAt k 2)) (tc.kid k 2)) (by simp [TopCert.prodCalls])
    have h4 : Model.ev val (o os (tc.pAt k 4)) = Model.ev val (o os (tc.pAt k 3)) * Model.ev val (tc.kid k 3) :=
      hk k hkm (tc.pAt k 4, .mul (o os (tc.pAt k 3)) (tc.kid k 3)) (by simp [TopCert.prodCalls])
    simp only [Function.comp_apply]
    rw [h4, h3, h2, h1, h0, one_mul]
  refine ⟨?_, ?_, fun k hkm => ?_⟩
  · rw [TopCert.claim, horner_sem hF _ _ _ _ (by simp [TopCert.m] at hcl ⊢; omega) hh1, hz1', eval_polyOf,
      List.map_reverse, List.foldl_reverse]
  · rw [TopCert.expected, horner_sem hF _ _ _ _ (by simp [TopCert.prods] at hel ⊢; omega) hh2, hz2', eval_polyOf,
      List.map_reverse, List.foldl_reverse, hprods]
  · have e0 : Model.ev val (o os (tc.lAt k 0)) = Model.ev val (tc.kid k 0) + Model.ev val (tc.kid k 1) :=
      hk k hkm (tc.lAt k 0, .add (tc.kid k 0) (tc.kid k 1)) (by simp [TopCert.lineCalls])
    have e1 : Model.ev val (o os (tc.lAt k 1)) =
        Model.ev val tc.low.chal * Model.ev val (o os (tc.lAt k 0)) + Model.ev val (tc.kid k 0) :=
      hk k hkm (tc.lAt k 1, .mulAdd tc.low.chal (o os (tc.lAt k 0)) (tc.kid k 0)) (by simp [TopCert.lineCalls])
    have e2 : Model.ev val (o os (tc.lAt k 2)) = Model.ev val (tc.kid k 2) + Model.ev val (tc.kid k 3) :=
      hk k hkm (tc.lAt k 2, .add (tc.kid k 2) (tc.kid k 3)) (by simp [TopCert.lineCalls])
    have e3 : Model.ev val (o os (tc.lAt k 3)) =
        Model.ev val tc.low.chal * Model.ev val (o os (tc.lAt k 2)) + Model.ev val (tc.kid k 2) :=
      hk k hkm (tc.lAt k 3, .mulAdd tc.low.chal (o os (tc.lAt k 2)) (tc.kid k 2)) (by simp [TopCert.lineCalls])
    have e4 : Model.ev val (o os (tc.lAt k 4)) = Model.ev val (o os (tc.lAt k 1)) + Model.ev val (o os (tc.lAt k 3)) :=
      hk k hkm (tc.lAt k 4, .add (o os (tc.lAt k 1)) (o os (tc.lAt k 3))) (by simp [TopCert.lineCalls])
    have e5 : Model.ev val (o os (tc.lAt k 5)) =
        Model.ev val tc.high.chal * Model.ev val (o os (tc.lAt k 4)) + Model.ev val (o os (tc.lAt k 1)) :=
      hk k hkm (tc.lAt k 5, .mulAdd tc.high.chal (o os (tc.lAt k 4)) (o os (tc.lAt k 1)))
        (by simp [TopCert.lineCalls])
    rw [TopCert.out, e5, e4, e1, e3, e0, e2]
    simp only [lineE]
    ring

end Sem

end LeanVMCircuits.Rec.Bind
