module

public import LeanVMCircuits.Rec.Rounds

@[expose] public section

/-!
WHIR's sumcheck, read off the builder's calls.

WHIR's verifier (`pcs::whir::verify`) reads each round as a quadratic (`RoundQuad`): `RoundQuad::read` reads it with
the verifier's `read_round`, the linear coefficient fixed by the running claim, and `RoundQuad::eval` evaluates it by Horner
from its top coefficient. After a level's fold rounds it batches the level's out-of-domain claims and its query batch's
claim at the powers of a challenge `λ`: each claim's quadratic is folded into the running one at its power, and the
running claim takes the claim at that power. Its test is the last claim against the terminal value it computes.

The certificate (`WhirCert`) reads this as a sumcheck with two kinds of round (`WhirRound`). A fold round's polynomial
is the running quadratic (`QuadCert`: received against a claim, or another folded into it at a power), whose check
against its claim holds by construction (`quad_sem`: `b + a` is its claim, in characteristic two), and its next claim
is the quadratic at the round's challenge. A batch round's polynomial is the claim after batching as a polynomial in
`λ` (`PExpr`: an expression over wires bound before `λ`, the previous claim among them, and `λ`, through the calls that
make it), with eq weight zero: its check is its value at zero, which is the previous claim (`PExpr.fixes`), and its
next claim is its value at `λ`.

`whirRound_sem`: in an assignment where every replayed call holds, a round's polynomial has degree at most the round's,
passes the round's check against its claim, and is the next claim at the challenge.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Polynomial

/-- A wire as a polynomial in a variable wire `x`: a wire it treats as a coefficient (`atom`), `x` itself, or a call's
first output with its arguments' expressions. -/
inductive PExpr where
  | atom (w : ℕ)
  | var
  | add (j : ℕ) (a d : PExpr)
  | mul (j : ℕ) (a b : PExpr)
  | mulAdd (j : ℕ) (a b d : PExpr)
  | square (j : ℕ) (a : PExpr)
  | mulConstAdd (j c0 c1 c2 : ℕ) (a d : PExpr)
  deriving Inhabited, Repr

namespace PExpr

variable (os : Array (List ℕ)) (x : ℕ)

/-- The expression's wire. -/
def wire : PExpr → ℕ
  | atom w => w
  | var => x
  | add j .. | mul j .. | mulAdd j .. | square j _ | mulConstAdd j .. => o os j

/-- The calls making it. -/
def calls : PExpr → List (ℕ × Call)
  | atom _ | var => []
  | add j a d => (j, .add (a.wire os x) (d.wire os x)) :: (a.calls ++ d.calls)
  | mul j a b => (j, .mul (a.wire os x) (b.wire os x)) :: (a.calls ++ b.calls)
  | mulAdd j a b d => (j, .mulAdd (a.wire os x) (b.wire os x) (d.wire os x)) :: (a.calls ++ b.calls ++ d.calls)
  | square j a => (j, .square (a.wire os x)) :: a.calls
  | mulConstAdd j c0 c1 c2 a d => (j, .mulConstAdd (a.wire os x) c0 c1 c2 (d.wire os x)) :: (a.calls ++ d.calls)

/-- The wires it treats as coefficients. -/
def atoms : PExpr → List ℕ
  | atom w => [w]
  | var => []
  | add _ a d | mul _ a d | mulConstAdd _ _ _ _ a d => a.atoms ++ d.atoms
  | mulAdd _ a b d => a.atoms ++ b.atoms ++ d.atoms
  | square _ a => a.atoms

/-- A bound on its degree in `x`. -/
def deg : PExpr → ℕ
  | atom _ => 0
  | var => 1
  | add _ a d | mulConstAdd _ _ _ _ a d => max a.deg d.deg
  | mul _ a b => a.deg + b.deg
  | mulAdd _ a b d => max (a.deg + b.deg) d.deg
  | square _ a => 2 * a.deg

/-- It vanishes at `x = 0`. -/
def vanish : PExpr → Bool
  | atom _ => false
  | var => true
  | add _ a d | mulConstAdd _ _ _ _ a d => a.vanish && d.vanish
  | mul _ a b => a.vanish || b.vanish
  | mulAdd _ a b d => (a.vanish || b.vanish) && d.vanish
  | square _ a => a.vanish

/-- At `x = 0` it is the wire `w`. -/
def fixes (w : ℕ) : PExpr → Bool
  | atom w' => w' == w
  | add _ a d => (a.fixes w && d.vanish) || (a.vanish && d.fixes w)
  | mulAdd _ a b d => (a.vanish || b.vanish) && d.fixes w
  | _ => false

/-- Its polynomial, the atoms' values as coefficients. -/
noncomputable def poly (val : Val) : PExpr → E[X]
  | atom w => C (Model.ev val w)
  | var => X
  | add _ a d => a.poly val + d.poly val
  | mul _ a b => a.poly val * b.poly val
  | mulAdd _ a b d => a.poly val * b.poly val + d.poly val
  | square _ a => a.poly val * a.poly val
  | mulConstAdd _ c0 c1 c2 a d => a.poly val * C (toE (ofWord c0) (ofWord c1) (ofWord c2)) + d.poly val

theorem natDegree_poly (val : Val) : ∀ e : PExpr, (e.poly val).natDegree ≤ e.deg
  | atom _ => by simp [poly, deg]
  | var => natDegree_X_le
  | add _ a d => (natDegree_add_le _ _).trans (max_le_max (natDegree_poly val a) (natDegree_poly val d))
  | mul _ a b => natDegree_mul_le.trans (add_le_add (natDegree_poly val a) (natDegree_poly val b))
  | mulAdd _ a b d => (natDegree_add_le _ _).trans
      (max_le_max (natDegree_mul_le.trans (add_le_add (natDegree_poly val a) (natDegree_poly val b)))
        (natDegree_poly val d))
  | square _ a => natDegree_mul_le.trans (by
      have := natDegree_poly val a
      simp only [deg]
      omega)
  | mulConstAdd _ _ _ _ a d => (natDegree_add_le _ _).trans (max_le_max
      (natDegree_mul_le.trans (by simp only [natDegree_C, add_zero]; exact natDegree_poly val a))
      (natDegree_poly val d))

theorem poly_congr {val val' : Val} : ∀ e : PExpr, (∀ w ∈ e.atoms, Model.ev val w = Model.ev val' w) →
    e.poly val = e.poly val'
  | atom w, h => by simp [poly, h w (by simp [atoms])]
  | var, _ => rfl
  | add _ a d, h => by
    simp only [atoms, List.mem_append] at h
    simp only [poly, poly_congr a fun w hw => h w (Or.inl hw), poly_congr d fun w hw => h w (Or.inr hw)]
  | mul _ a d, h => by
    simp only [atoms, List.mem_append] at h
    simp only [poly, poly_congr a fun w hw => h w (Or.inl hw), poly_congr d fun w hw => h w (Or.inr hw)]
  | mulConstAdd _ _ _ _ a d, h => by
    simp only [atoms, List.mem_append] at h
    simp only [poly, poly_congr a fun w hw => h w (Or.inl hw), poly_congr d fun w hw => h w (Or.inr hw)]
  | mulAdd _ a b d, h => by
    simp only [atoms, List.mem_append] at h
    simp only [poly, poly_congr a fun w hw => h w (Or.inl (Or.inl hw)),
      poly_congr b fun w hw => h w (Or.inl (Or.inr hw)), poly_congr d fun w hw => h w (Or.inr hw)]
  | square _ a, h => by
    simp only [atoms] at h
    simp only [poly, poly_congr a h]

theorem vanish_eval (val : Val) : ∀ e : PExpr, e.vanish = true → (e.poly val).eval 0 = 0
  | atom _, h => by simp [vanish] at h
  | var, _ => by simp [poly]
  | add _ a d, h => by
    simp only [vanish, Bool.and_eq_true] at h
    simp [poly, vanish_eval val a h.1, vanish_eval val d h.2]
  | mulConstAdd _ _ _ _ a d, h => by
    simp only [vanish, Bool.and_eq_true] at h
    simp [poly, vanish_eval val a h.1, vanish_eval val d h.2]
  | mul _ a b, h => by
    simp only [vanish, Bool.or_eq_true] at h
    rcases h with h | h <;> simp [poly, vanish_eval val _ h]
  | mulAdd _ a b d, h => by
    simp only [vanish, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨h | h, hd⟩ := h <;> simp [poly, vanish_eval val _ h, vanish_eval val d hd]
  | square _ a, h => by
    simp only [vanish] at h
    simp [poly, vanish_eval val a h]

theorem fixes_eval (val : Val) (w : ℕ) : ∀ e : PExpr, e.fixes w = true → (e.poly val).eval 0 = Model.ev val w
  | atom w', h => by
    simp only [fixes, beq_iff_eq] at h
    simp [poly, h]
  | add _ a d, h => by
    simp only [fixes, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨ha, hd⟩ | ⟨ha, hd⟩
    · simp [poly, fixes_eval val w a ha, vanish_eval val d hd]
    · simp [poly, vanish_eval val a ha, fixes_eval val w d hd]
  | mulAdd _ a b d, h => by
    simp only [fixes, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨h | h, hd⟩ := h <;> simp [poly, vanish_eval val _ h, fixes_eval val w d hd]
  | var, h | mul .., h | square .., h | mulConstAdd .., h => by simp [fixes] at h

end PExpr

/-- A WHIR round's quadratic `c + b X + a X^2`: received against a claim by `Verifier::read_round` (`c` and `a` sent,
`b = claim + (0 + a)` by `tailZero`, `tailAt` and `fixedAt`), or `RoundQuad::fold` of `intro` into `base` at `s`, each
coefficient `mul_add(s, intro's, base's)`, its claim the running claim's `mul_add(s, intro's claim, base's claim)`. -/
inductive QuadCert where
  | recv (claim c a tailZero tailAt fixedAt : ℕ)
  | fold (base intro : QuadCert) (s cAt bAt aAt claimAt : ℕ)
  deriving Inhabited, Repr

namespace QuadCert

variable (os : Array (List ℕ))

/-- Its claim and coefficients. -/
def claim : QuadCert → ℕ
  | recv cl .. => cl
  | fold _ _ _ _ _ _ j => o os j
def c : QuadCert → ℕ
  | recv _ c .. => c
  | fold _ _ _ j .. => o os j
def b : QuadCert → ℕ
  | recv _ _ _ _ _ f => o os f
  | fold _ _ _ _ j .. => o os j
def a : QuadCert → ℕ
  | recv _ _ a .. => a
  | fold _ _ _ _ _ j _ => o os j

/-- The calls making it. -/
def calls : QuadCert → List (ℕ × Call)
  | recv cl _ a z t f => [(z, .zero), (t, .add (o os z) a), (f, .add cl (o os t))]
  | fold q i s cAt bAt aAt clAt =>
    [(cAt, .mulAdd s (i.c os) (q.c os)), (bAt, .mulAdd s (i.b os) (q.b os)), (aAt, .mulAdd s (i.a os) (q.a os)),
      (clAt, .mulAdd s (i.claim os) (q.claim os))] ++ q.calls ++ i.calls

end QuadCert

/-- A WHIR round: a fold round (its quadratic, its challenge, and `RoundQuad::eval`'s two `mul_add` calls) or a batch
round (its challenge `λ`, the claim after batching as an expression in `λ`, the output words of its squeezes that
`λ` reads (`own`), and the firings binding the expression's atoms with the words squeezed with `λ`, its query
positions, as seeds). -/
inductive WhirRound where
  | fold (q : QuadCert) (cc : ChalCert) (uAt tAt : ℕ)
  | batch (cc : ChalCert) (e : PExpr) (own : List ℕ) (firings : Array ℕ)
  deriving Inhabited, Repr

namespace WhirRound

variable (os : Array (List ℕ))

def chal : WhirRound → ChalCert
  | fold _ cc .. | batch cc .. => cc

/-- The round's eq weight: none for a fold round, zero for a batch round, whose check is its value at zero. -/
noncomputable def weight : WhirRound → Option E
  | fold .. => none
  | batch .. => some 0

def deg : WhirRound → ℕ
  | fold .. => 2
  | batch _ e .. => e.deg

/-- The next claim. -/
def next : WhirRound → ℕ
  | fold _ _ _ t => o os t
  | batch cc e .. => e.wire os cc.chal

/-- The wires the round's polynomial reads: the quadratic's coefficients, or the expression's atoms. -/
def atoms : WhirRound → List ℕ
  | fold q .. => [q.c os, q.b os, q.a os]
  | batch _ e .. => e.atoms

/-- The round's polynomial. -/
noncomputable def poly (val : Val) : WhirRound → E[X]
  | fold q .. => Sumcheck.polyOf ([q.c os, q.b os, q.a os].map (Model.ev val))
  | batch _ e .. => e.poly val

/-- The round's calls are in the replay and it reads `claim`: a fold round's quadratic has it as its claim, a batch
round's expression is it at zero. -/
def ok (cs : Array Call) (rl : Array Bool) (claim : ℕ) : WhirRound → Bool
  | fold q cc u t => q.claim os == claim &&
    callsOk cs rl (q.calls os ++ [(u, .mulAdd (q.a os) cc.chal (q.b os)), (t, .mulAdd (o os u) cc.chal (q.c os))])
  | batch cc e .. => e.fixes claim && callsOk cs rl (e.calls os cc.chal)

/-- A round's polynomial reads only its atoms. -/
theorem poly_congr {val val' : Val} : ∀ wr : WhirRound, (∀ w ∈ wr.atoms os, Model.ev val w = Model.ev val' w) →
    wr.poly os val = wr.poly os val'
  | fold .., h => congrArg Sumcheck.polyOf (List.map_congr_left h)
  | batch _ e .., h => e.poly_congr h

end WhirRound

/-- WHIR's sumcheck: its input claim, its rounds, its test (an equality of the circuit, between the last claim and
`final`, the terminal value) and its transcript. -/
structure WhirCert where
  claim0 : ℕ
  rounds : List WhirRound
  test : ℕ
  final : ℕ
  transcript : ℕ
  deriving Inhabited, Repr

namespace WhirCert

variable (os : Array (List ℕ)) (wc : WhirCert)

/-- Round `i`'s claim: the input claim, then each round's next claim. -/
def claimAt (i : ℕ) : ℕ := if i = 0 then wc.claim0 else (wc.rounds.getD (i - 1) default).next os

/-- The rounds' degree: the largest. -/
def deg : ℕ := (wc.rounds.map WhirRound.deg).foldr max 0

/-- Every round's calls are in the replay, each round reading the claim the previous one leaves. -/
def ok (cs : Array Call) (rl : Array Bool) : Bool :=
  0 < wc.rounds.length &&
    (List.range wc.rounds.length).all fun i => (wc.rounds.getD i default).ok os cs rl (wc.claimAt os i)

theorem deg_le {i : ℕ} (hi : i < wc.rounds.length) : (wc.rounds.getD i default).deg ≤ wc.deg := by
  have hm : (wc.rounds.getD i default).deg ∈ wc.rounds.map WhirRound.deg := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.mem_map_of_mem (List.getElem_mem hi)
  unfold deg
  generalize wc.rounds.map WhirRound.deg = l at hm
  induction l with
  | nil => simp at hm
  | cons x l ih =>
    rcases List.mem_cons.mp hm with h | h
    · rw [List.foldr_cons]; exact le_max_of_le_left h.le
    · rw [List.foldr_cons]; exact le_max_of_le_right (ih h)

end WhirCert

section Sem

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}

theorem pexpr_sem (hF : Facts cs rl os st val) (x : ℕ) : ∀ e : PExpr, callsOk cs rl (e.calls os x) = true →
    Model.ev val (e.wire os x) = (e.poly val).eval (Model.ev val x)
  | .atom _, _ => by simp [PExpr.wire, PExpr.poly]
  | .var, _ => by simp [PExpr.wire, PExpr.poly]
  | .add j a d, h => by
    simp only [PExpr.calls] at h
    obtain ⟨h1, h2⟩ := callsOk_cons h
    rw [callsOk_append, Bool.and_eq_true] at h2
    have hj : Model.ev val (o os j) = Model.ev val (a.wire os x) + Model.ev val (d.wire os x) :=
      holds_of_mem hF h1 (List.mem_singleton_self _)
    simp only [PExpr.wire, PExpr.poly, Polynomial.eval_add]
    rw [hj, pexpr_sem hF x a h2.1, pexpr_sem hF x d h2.2]
  | .mul j a b, h => by
    simp only [PExpr.calls] at h
    obtain ⟨h1, h2⟩ := callsOk_cons h
    rw [callsOk_append, Bool.and_eq_true] at h2
    have hj : Model.ev val (o os j) = Model.ev val (a.wire os x) * Model.ev val (b.wire os x) :=
      holds_of_mem hF h1 (List.mem_singleton_self _)
    simp only [PExpr.wire, PExpr.poly, Polynomial.eval_mul]
    rw [hj, pexpr_sem hF x a h2.1, pexpr_sem hF x b h2.2]
  | .mulAdd j a b d, h => by
    simp only [PExpr.calls] at h
    obtain ⟨h1, h2⟩ := callsOk_cons h
    rw [callsOk_append, callsOk_append, Bool.and_eq_true, Bool.and_eq_true] at h2
    have hj : Model.ev val (o os j) =
        Model.ev val (a.wire os x) * Model.ev val (b.wire os x) + Model.ev val (d.wire os x) :=
      holds_of_mem hF h1 (List.mem_singleton_self _)
    simp only [PExpr.wire, PExpr.poly, Polynomial.eval_add, Polynomial.eval_mul]
    rw [hj, pexpr_sem hF x a h2.1.1, pexpr_sem hF x b h2.1.2, pexpr_sem hF x d h2.2]
  | .square j a, h => by
    simp only [PExpr.calls] at h
    obtain ⟨h1, h2⟩ := callsOk_cons h
    have hj : Model.ev val (o os j) = Model.ev val (a.wire os x) * Model.ev val (a.wire os x) :=
      holds_of_mem hF h1 (List.mem_singleton_self _)
    simp only [PExpr.wire, PExpr.poly, Polynomial.eval_mul]
    rw [hj, pexpr_sem hF x a h2]
  | .mulConstAdd j c0 c1 c2 a d, h => by
    simp only [PExpr.calls] at h
    obtain ⟨h1, h2⟩ := callsOk_cons h
    rw [callsOk_append, Bool.and_eq_true] at h2
    have hj : Model.ev val (o os j) =
        Model.ev val (a.wire os x) * toE (ofWord c0) (ofWord c1) (ofWord c2) + Model.ev val (d.wire os x) :=
      holds_of_mem hF h1 (List.mem_singleton_self _)
    simp only [PExpr.wire, PExpr.poly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    rw [hj, pexpr_sem hF x a h2.1, pexpr_sem hF x d h2.2]

/-- A quadratic's linear and quadratic coefficients sum to its claim (characteristic two). -/
theorem quad_sem (hF : Facts cs rl os st val) : ∀ q : QuadCert, callsOk cs rl (q.calls os) = true →
    Model.ev val (q.b os) + Model.ev val (q.a os) = Model.ev val (q.claim os)
  | .recv cl _ a z t f, h => by
    obtain ⟨h1, h2⟩ := callsOk_cons h
    obtain ⟨h2, h3⟩ := callsOk_cons h2
    have hz : Model.ev val (o os z) = 0 := holds_of_mem hF h1 (List.mem_singleton_self _)
    have ht : Model.ev val (o os t) = Model.ev val (o os z) + Model.ev val a :=
      holds_of_mem hF h2 (List.mem_singleton_self _)
    have hf : Model.ev val (o os f) = Model.ev val cl + Model.ev val (o os t) :=
      holds_of_mem hF h3 (List.mem_singleton_self _)
    simp only [QuadCert.b, QuadCert.a, QuadCert.claim]
    rw [hf, ht, hz]
    linear_combination Model.ev val a * two_E
  | .fold q i s cAt bAt aAt clAt, h => by
    simp only [QuadCert.calls, callsOk_append, Bool.and_eq_true] at h
    obtain ⟨⟨hh, hq⟩, hi⟩ := h
    obtain ⟨-, hh⟩ := callsOk_cons hh
    obtain ⟨hb, hh⟩ := callsOk_cons hh
    obtain ⟨ha, hcl⟩ := callsOk_cons hh
    have eb : Model.ev val (o os bAt) = Model.ev val s * Model.ev val (i.b os) + Model.ev val (q.b os) :=
      holds_of_mem hF hb (List.mem_singleton_self _)
    have ea : Model.ev val (o os aAt) = Model.ev val s * Model.ev val (i.a os) + Model.ev val (q.a os) :=
      holds_of_mem hF ha (List.mem_singleton_self _)
    have ecl : Model.ev val (o os clAt) = Model.ev val s * Model.ev val (i.claim os) + Model.ev val (q.claim os) :=
      holds_of_mem hF hcl (List.mem_singleton_self _)
    simp only [QuadCert.b, QuadCert.a, QuadCert.claim]
    rw [eb, ea, ecl, ← quad_sem hF q hq, ← quad_sem hF i hi]
    ring

open Sumcheck in
/-- A WHIR round's polynomial has degree at most the round's, passes the round's check against its claim, and is the
next claim at the challenge. -/
theorem whirRound_sem (hF : Facts cs rl os st val) {wr : WhirRound} {claim : ℕ}
    (hok : wr.ok os cs rl claim = true) :
    (wr.poly os val).natDegree ≤ wr.deg ∧ lin wr.weight (wr.poly os val) = Model.ev val claim ∧
      Model.ev val (wr.next os) = (wr.poly os val).eval (Model.ev val wr.chal.chal) := by
  match wr with
  | .fold q cc u t =>
    simp only [WhirRound.ok, Bool.and_eq_true, beq_iff_eq, callsOk_append] at hok
    obtain ⟨hcl, hq, hev⟩ := hok
    obtain ⟨hu, ht⟩ := callsOk_cons hev
    have eu : Model.ev val (o os u) = Model.ev val (q.a os) * Model.ev val cc.chal + Model.ev val (q.b os) :=
      holds_of_mem hF hu (List.mem_singleton_self _)
    have et : Model.ev val (o os t) = Model.ev val (o os u) * Model.ev val cc.chal + Model.ev val (q.c os) :=
      holds_of_mem hF ht (List.mem_singleton_self _)
    have hl := quad_sem hF q hq
    rw [hcl] at hl
    refine ⟨(natDegree_polyOf _).trans (by simp [WhirRound.deg]), ?_, ?_⟩
    · simp only [WhirRound.poly, WhirRound.weight, lin, eval_polyOf_zero, eval_polyOf_one, List.map_cons,
        List.map_nil, List.head?_cons, Option.getD_some, List.sum_cons, List.sum_nil]
      rw [← hl]
      linear_combination Model.ev val (q.c os) * two_E
    · simp only [WhirRound.next, WhirRound.poly, WhirRound.chal, eval_polyOf, List.map_cons, List.map_nil,
        List.foldr_cons, List.foldr_nil]
      rw [et, eu]
      ring
  | .batch cc e _ _ =>
    simp only [WhirRound.ok, Bool.and_eq_true] at hok
    obtain ⟨hfix, hcalls⟩ := hok
    refine ⟨e.natDegree_poly val, ?_, pexpr_sem hF cc.chal e hcalls⟩
    simp only [WhirRound.poly, WhirRound.weight, lin, sub_zero, one_mul, zero_mul, add_zero]
    exact e.fixes_eval val claim hfix

end Sem

end LeanVMCircuits.Rec.Bind
