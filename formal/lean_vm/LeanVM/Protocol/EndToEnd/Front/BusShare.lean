/-
  LeanVM.Protocol.EndToEnd.Front.BusShare

  The bus phase's bytecode share, specified: the sumcheck that reduces the program's share of a
  bytecode leaf to one value of the stacked bytecode, and the deployed verifier's evaluation of
  that value, return only the true share, but with probability `2/|E|` per round.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.BusGkr
public import LeanVM.Protocol.EndToEnd.Front.EqKernel
public import LeanVM.Protocol.EndToEnd.Front.LayoutArith
public import LeanVM.Protocol.ToArkLib.Sumcheck

/-!
# The bytecode share

The verifier never evaluates the program's share of a bytecode leaf, `Σ_x w_x · P(low, x)` over
the stacked bytecode's sixteen tuple slots `x` (`bytecodeShare`, `crates/verifier/src/bus.rs:168-184`):
the prover sends it, a sumcheck over `x` of `w̃(x) · P(low, x)` (degree two in each slot bit,
its low bit first) reduces it to one value of `P` at `(low, slot)`, and the deployed verifier
evaluates `P` there (`computedBytecodeValue`). This module proves that the pair returns only the
true share (`shareCheckSpec`): a wrong share survives a round's challenge with probability at
most `2/|E|`.

The sumcheck is the oracle protocol's sumcheck of a virtual polynomial (`Sumcheck.Virtual`),
which binds its highest coordinate first: its summand is `w̃ · P̃` at the reversed point
(`shareSummand`), so that its final claim is at the wire's slot point (`Sumcheck.claim_self`), and
its total is the share (`shareTotal_eq`, the cube being closed under reversal,
`sum_boolVec_reverse`). The family's invariant is that the share read is wrong
(`shareFamily`): doom on its relations, over one candidate oracle (`soleCands`, the relation
reads none), is "the share is true or the running claim is wrong" (`shareDoom_iff`), which holds
at the start and, at the end, makes the final checks fail unless the share is true.

`Spec.frame` carries a property of the history before a sub-program, kept by every event, to its
returns.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open CompPoly CMlPolynomialEval OracleComp OracleSpec
open scoped NNReal ENNReal

@[expose] public section

/-! ## A frame rule -/

section Frame

variable {α : Type} {p : VerifierProgram α} {Pre : List Ev → Prop} {Post : α → List Ev → Prop}
  {εmax L T : ENNReal}

open Classical in
/-- **The frame rule**: a property `Q` of the history before `p`, kept by every later event,
holds wherever `p` returns. -/
noncomputable def _root_.LeanVM.Protocol.Compile.Spec.frame (S : Spec p Pre Post εmax L T)
    (Q : List Ev → Prop) (hQ : ∀ h l, Q h → Q (h ++ l)) :
    Spec p (fun h ↦ Q h ∧ Pre h) (fun a h ↦ Q h ∧ Post a h) εmax L T where
  D h₀ l := Q h₀ ∧ S.D h₀ l
  V h₀ l := if Q h₀ then S.V h₀ l else 1
  le_one h₀ l := by split_ifs; exacts [S.le_one h₀ l, le_rfl]
  start_D h₀ h := ⟨h.1, S.start_D h₀ h.2⟩
  start_V h₀ h := by simp only [h.1, ↓reduceIte]; exact S.start_V h₀ h.2
  read x hl ha hD := ⟨hD.1, S.read x hl ha hD.2⟩
  grind hl ha hD := ⟨hD.1, S.grind hl ha hD.2⟩
  commit word hl ha hw hD := ⟨hD.1, S.commit word hl ha hw hD.2⟩
  sample := by
    intro h₀ l k hl ha
    by_cases hq : Q h₀
    · simp only [hq, ↓reduceIte]
      exact S.sample hl ha
    · simp only [hq, ↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rw [ENNReal.inv_mul_cancel (by simp) (by simp)]
  query hl ha hr := by
    split_ifs
    · exact S.query hl ha hr
    · exact le_rfl
  moveEnd := by
    intro h₀ l q hl ha hm hD
    by_cases hq : Q h₀
    · simp only [hq, ↓reduceIte]; exact S.moveEnd hl ha hm fun h ↦ hD ⟨hq, h⟩
    · simp only [hq, ↓reduceIte, le_refl]
  retEnd := by
    intro h₀ l a hl ha hD
    by_cases hq : Q h₀
    · simp only [hq, ↓reduceIte]; exact S.retEnd hl ha fun h ↦ hD ⟨hq, h⟩
    · simp only [hq, ↓reduceIte, le_refl]
  retDoom hl ha hD := by simp only [hD.1, ↓reduceIte]; exact S.retDoom hl ha hD.2
  post hl ha hD := ⟨hQ _ _ hD.1, S.post hl ha hD.2⟩
  bound hl hne hm hD := by simp only [hD.1, ↓reduceIte]; exact S.bound hl hne hm hD.2

end Frame

/-! ## Reversing the cube -/

section Reverse

variable {R : Type*} [CommRing R]

/-- Reversing the point moves coordinate `k`'s degree to coordinate `n - 1 - k`. -/
theorem degreeLEAt_reverse {n k d : ℕ} {g : Vector R n → R} (h : DegreeLEAt g (n - 1 - k) d) :
    DegreeLEAt (fun z ↦ g z.reverse) k d := by
  intro z hk
  obtain ⟨p, hp, he⟩ := h z.reverse (by omega)
  refine ⟨p, hp, fun x ↦ ?_⟩
  have hs : (z.set k x hk).reverse = z.reverse.set (n - 1 - k) x (by omega) := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_reverse, Vector.getElem_set]
    split_ifs <;> first | rfl | omega
  show g (z.set k x hk).reverse = _
  rw [hs, he]

/-- On the cube, the encoder inverts the decoder. -/
theorem boolVec_boolIndex [DecidableEq R] [Nontrivial R] :
    ∀ {m : ℕ} (v : Vector R m), (∀ i (hi : i < m), v[i] = 0 ∨ v[i] = 1) →
      (boolVec (boolIndex v) : Vector R m) = v
  | 0, v, _ => Vector.ext fun i hi ↦ absurd hi (by omega)
  | m + 1, v, hv => by
    have ht := boolVec_boolIndex v.tail fun i hi ↦ by
      rw [Vector.getElem_tail]
      exact hv (i + 1) (by omega)
    apply Vector.ext
    intro i hi
    have hb : (if v[0] = 1 then 1 else 0) < 2 := by split <;> omega
    rcases i with _ | i
    · simp only [boolVec, Vector.getElem_ofFn, boolIndex, Nat.testBit_zero]
      rcases hv 0 (by omega) with h0 | h0
      · simp [h0]
      · simp [h0]
    · have := congrArg (fun w : Vector R m ↦ w[i]'(by omega)) ht
      simp only [boolVec, Vector.getElem_ofFn] at this
      simp only [boolVec, Vector.getElem_ofFn, boolIndex, Nat.testBit_add_one]
      generalize (if v[0] = 1 then 1 else 0) = b at hb ⊢
      rw [show (b + 2 * (boolIndex v.tail).val) / 2 = (boolIndex v.tail).val by omega, this,
        Vector.getElem_tail]

/-- **The cube is closed under reversal**: summing over the reversed cube points is summing over
the cube points. -/
theorem sum_boolVec_reverse [DecidableEq R] [Nontrivial R] {M : Type*} [AddCommMonoid M] {n : ℕ}
    (f : Vector R n → M) :
    ∑ x : Fin (2 ^ n), f (boolVec x : Vector R n).reverse = ∑ x : Fin (2 ^ n), f (boolVec x) := by
  let r : Fin (2 ^ n) → Fin (2 ^ n) := fun x ↦ boolIndex (boolVec x : Vector R n).reverse
  have hr : ∀ x, (boolVec (r x) : Vector R n) = (boolVec x : Vector R n).reverse := fun x ↦
    boolVec_boolIndex _ fun i hi ↦ by
      simp only [boolVec, Vector.getElem_reverse, Vector.getElem_ofFn]
      split <;> simp
  have hinv : Function.Involutive r := fun x ↦ by
    show boolIndex (boolVec (r x) : Vector R n).reverse = x
    rw [hr, Vector.reverse_reverse, boolIndex_boolVec]
  exact Fintype.sum_bijective r hinv.bijective _ _ fun x ↦ by rw [hr]

end Reverse

/-! ## The share's sumcheck -/

/-- The share's public data: the slot weights and the bytecode's values at the sixteen slots,
as tables on four variables, and the share read. -/
abbrev ShareX : Type := (CMlPolynomialEval E 4 × CMlPolynomialEval E 4) × E

/-- The summand at a point of the virtual polynomial's coordinates: `w̃ · P̃` at the reversed
point, so that the coordinate the virtual sumcheck binds first is the wire's slot bit `0`. -/
def shareSummand (W B : CMlPolynomialEval E 4) (z : Vector E 4) : E :=
  evalMle W z.reverse * evalMle B z.reverse

/-- The share's total over the slots: the claim the sumcheck reduces. -/
def shareTotal (W B : CMlPolynomialEval E 4) : E :=
  weightedCubeSum (fun _ ↦ ((1 : E), (1 : E))) (shareSummand W B)

/-- **The total is the share**: `Σ_x W_x · B_x`. -/
theorem shareTotal_eq (W B : CMlPolynomialEval E 4) :
    shareTotal W B = ∑ x : Fin (2 ^ 4), W[x] * B[x] := by
  rw [shareTotal, weightedCubeSum_one]
  unfold shareSummand
  rw [sum_boolVec_reverse (fun v ↦ evalMle W v * evalMle B v)]
  simp only [evalMle_boolVec]

variable (I : M3Instance)

/-- The share's virtual polynomial: no table, the summand from the public data. -/
def shareVirtual : Sumcheck.Virtual E ShareX (TheOracle I) Unit 4 0 where
  tables _ := Fin.elim0
  formula x z _ := shareSummand x.1.1 x.1.2 z

/-- The interpolation nodes of a degree-two round: `0, 1, y`. -/
def shareNodes : Fin 3 → E := ![0, 1, y]

theorem shareNodes_injective : Function.Injective shareNodes := by
  have hy : ∀ a : K, y ≠ ofK a := fun a h ↦ by
    have h1 : CompPoly.Extension.Ext.coeff (CompPoly.Extension.Ext.gen : E) ⟨1, eParams.two_le⟩ =
        CompPoly.Extension.Ext.coeff (ofK a) ⟨1, eParams.two_le⟩ :=
      congrArg (fun z : E ↦ CompPoly.Extension.Ext.coeff z _) h
    rw [CompPoly.Extension.Ext.coeff_gen, CompPoly.Extension.Ext.coeff_ofBase] at h1
    simp at h1
  have y0 : y ≠ 0 := by simpa using hy 0
  have y1 : y ≠ 1 := by simpa using hy 1
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [shareNodes, y0.symm, y1.symm]

/-- The share's invariant: the share read is not the total. -/
def shareWrong (ctx : SumcheckRound.Ctx ShareX (TheOracle I) Unit) : Prop :=
  ctx.1.1.2 ≠ shareTotal ctx.1.1.1.1 ctx.1.1.1.2

/-- **The share's family**: the plain sumcheck of the virtual polynomial, its invariant that the
share is wrong. -/
def shareFamily : SumcheckRound.Family E ShareX (TheOracle I) Unit 2 :=
  Sumcheck.family (shareVirtual I) Sumcheck.unitWeights shareNodes (shareWrong I)

/-- The summand has degree two in each coordinate. -/
theorem shareSummand_degree (ctx : SumcheckRound.Ctx ShareX (TheOracle I) Unit) :
    IndividualDegreeLE ((shareVirtual I).summand ctx) 2 := fun _ ↦
  (degreeLEAt_reverse (DegreeLEAt.evalMle _)).mul (degreeLEAt_reverse (DegreeLEAt.evalMle _))

theorem shareFamily_consistent : (shareFamily I).Consistent 4 :=
  (Sumcheck.family_honest (shareVirtual I) Sumcheck.unitWeights shareNodes (shareWrong I)
    (shareSummand_degree I) shareNodes_injective).toConsistent

theorem shareFamily_sound : (shareFamily I).Sound 4 := by
  intro ctx j c _ hn
  have : IsEmpty {x // (shareFamily I).inv ctx (j + 1) (c.push x)} := ⟨fun x ↦ hn x.2⟩
  rw [Nat.card_of_isEmpty]
  exact Nat.zero_le _

/-- One candidate oracle: the share's relations read none. -/
def soleCands (o₀ : ∀ i, TheOracle I i) : Word → Set (∀ i, TheOracle I i) := fun _ ↦ {o₀}

/-- **Doom on the share's relations**: at stage `j`, the share is true or the running claim is
not the family's. -/
theorem shareDoom_iff (o₀ : ∀ i, TheOracle I i) {j : ℕ} (s : SumcheckRound.Stmt ShareX E j)
    (h : List Ev) :
    HDoom (soleCands I o₀) (SumcheckRound.rel (shareFamily I) j) s h ↔
      (∃ W, firstWord h = some W) ∧
        (¬ shareWrong I ((s.1, o₀), ()) ∨
          s.2.2 ≠ (shareFamily I).claim ((s.1, o₀), ()) j s.2.1) := by
  unfold HDoom RelDoom soleCands
  simp only [Set.mem_singleton_iff, forall_eq, SumcheckRound.rel, Set.mem_ofPred_eq,
    SumcheckRound.ctxOf, not_and_or]
  constructor
  · rintro ⟨W, hW, hR⟩
    exact ⟨⟨W, hW⟩, hR⟩
  · rintro ⟨⟨W, hW⟩, hR⟩
    exact ⟨W, hW, hR⟩

/-- The family's claim before any challenge is the total. -/
theorem shareClaim_zero (ctx : SumcheckRound.Ctx ShareX (TheOracle I) Unit) :
    (shareFamily I).claim ctx 0 #v[] = shareTotal ctx.1.1.1.1 ctx.1.1.1.2 :=
  Sumcheck.claim_zero (shareVirtual I) Sumcheck.unitWeights ctx

/-- The family's claim after every challenge is the summand at the challenges, in the wire's
order. -/
theorem shareClaim_self (ctx : SumcheckRound.Ctx ShareX (TheOracle I) Unit) (c : Vector E 4) :
    (shareFamily I).claim ctx 4 c = evalMle ctx.1.1.1.1 c * evalMle ctx.1.1.1.2 c := by
  show Sumcheck.claim (shareVirtual I) Sumcheck.unitWeights ctx 4 c = _
  rw [Sumcheck.claim_self]
  show shareSummand _ _ c.reverse = _
  rw [shareSummand, Vector.reverse_reverse]

/-- The plain wire rounds have the family's domains. -/
theorem shareWeights (x : ShareX) (k : ℕ) (hk : k < (List.replicate 4 (none : Option E)).length) :
    (shareFamily I).weight x (0 + k) = wireDomain (List.replicate 4 (none : Option E))[k] := by
  have hk' : k < 4 := by simpa using hk
  simp only [shareFamily, Sumcheck.family, Sumcheck.domain, zero_add, hk', ↓reduceDIte,
    Sumcheck.unitWeights, List.getElem_replicate, wireDomain]

/-! ## The wire's values -/

/-- The slot weights' extension at the slot point is the program's `dot(eq_kernel(slot), w)`. -/
theorem dot_eqKernel_eq_evalMle {weights slot : List E} (hw : weights.length = 16)
    (hs : slot.length = 4) :
    dot (eqKernel slot) weights = evalMle (vecOf (2 ^ 4) weights) (vecOf 4 slot) := by
  rw [Whir.Complete.dot_eq_sum _ _ (by rw [Whir.Complete.length_eqKernel, hs, hw]; rfl),
    Whir.Complete.length_eqKernel, hs, evalMle_eq_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_comm]
  congr 1
  · simp [vecOf]
  · rw [show (vecOf 4 slot : Vector E 4) = Vector.ofFn fun j : Fin 4 ↦ slot.getD j 0 from rfl,
      lagrangeBasis_ofFn_getD hs, List.getD_eq_getElem _ _ (by
        rw [Whir.Complete.length_eqKernel, hs]; exact i.isLt)]

/-- The bytecode's values at the sixteen slots of the tuple at `low`. -/
def slotValues (words : List K) (low : List E) : CMlPolynomialEval E 4 :=
  Vector.ofFn fun j : Fin (2 ^ 4) ↦ multilinearEval (words.map ofK) (low ++ boolPoint 4 j)

/-- **The bytecode at `(low, slot)`** is the extension of its values at the slots, at `slot`. -/
theorem multilinearEval_eq_slotValues {words : List K} {low slot : List E}
    (hw : words.length = 2 ^ (low.length + 4)) (hs : slot.length = 4) :
    multilinearEval (words.map ofK) (low ++ slot) =
      evalMle (slotValues words low) (vecOf 4 slot) := by
  let t : CMlPolynomialEval E (low.length + 4) := ⟨(words.map ofK).toArray, by simp [hw]⟩
  have ht : (words.map ofK) = t.toList := by simp [t]
  have hlow : (vecOf low.length low).toList = low := toList_vecOf low rfl
  have hslot : (vecOf 4 slot).toList = slot := toList_vecOf slot hs
  have hv : ∀ v : Vector E 4, multilinearEval (words.map ofK) (low ++ v.toList) =
      evalMle t (vecOf low.length low ++ v) := fun v ↦ by
    rw [ht, ← multilinearEval_eq_evalMle, Vector.toList_append, hlow]
  rw [← hslot, hv, evalMle_split, evalMle_eq_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mul_comm]
  congr 1
  simp only [slotValues, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [boolPoint_eq_toList_boolVec, hv, evalMle_append_boolVec]

/-! ## The share's specification -/

variable {εmax T : ℝ≥0∞}

/-- The share's sub-program, as the deployed verifier runs it: the share and its sumcheck, then
the evaluation of the bytecode at the point. -/
def shareProg (weights low : List E) (words : List K) : VerifierProgram (E × List E × E) :=
  bytecodeShare weights low >>= fun r ↦ computedBytecodeValue words r.2.1 r.2.2 >>= fun _ ↦
    VerifierProgram.ret r

/-- One candidate oracle is at most one. -/
theorem soleCands_ncard (o₀ : ∀ i, TheOracle I i) (W : Word) : (soleCands I o₀ W).ncard ≤ 1 := by
  simp [soleCands]

open Classical in
/-- **The share returns only true**: from a property `P` of the history, kept by every event and
giving a commitment, the share's sub-program returns, with `P` kept, the total of the slot weights
against the bytecode's slot values; each of its four rounds' challenges escapes at `2/|E|`, the
rounds' leads `roundError 1 2` (`he`), and the follower's lead is `T`. -/
noncomputable def shareCheckSpec (o₀ : ∀ i, TheOracle I i) {weights low : List E} {words : List K}
    (hw : weights.length = 16) (hwords : words.length = 2 ^ (low.length + 4))
    (P : List Ev → Prop) (hP : ∀ h l, P h → P (h ++ l))
    (hfw : ∀ h, P h → ∃ W, firstWord h = some W) (hT : T ≤ εmax)
    (he : roundError 1 2 + 0 ≤ εmax) :
    Spec (shareProg weights low words) P
      (fun r h ↦ P h ∧ r.1 = shareTotal (vecOf (2 ^ 4) weights) (slotValues words low)) εmax 0 T :=
  let W := vecOf (2 ^ 4) weights
  let B := slotValues words low
  let x : E → ShareX := fun s ↦ ((W, B), s)
  have hd : ∀ s h, P h → HDoom (soleCands I o₀) (SumcheckRound.rel (shareFamily I) 0)
      (x s, (#v[], s)) h := fun s h hp ↦ by
    rw [shareDoom_iff]
    refine ⟨hfw h hp, ?_⟩
    by_cases hs : s = shareTotal W B
    · exact .inl fun hn ↦ hn hs
    · exact .inr (by rw [shareClaim_zero]; exact hs)
  Spec.congr (show (do
      let share ← VerifierProgram.readScalar
      let r ← sumcheck share 3 (List.replicate busBits none)
      let value ← VerifierProgram.readScalar
      VerifierProgram.require (r.2 = dot (eqKernel r.1) weights * value)
      computedBytecodeValue words (low ++ r.1) value
      VerifierProgram.ret (share, low ++ r.1, value)) = shareProg weights low words by
    simp only [shareProg, bytecodeShare, VerifierProgram.bind_eq, VerifierProgram.bind_assoc]
    rfl) <|
  (Spec.readE (Post := fun s h ↦ P h ∧ HDoom (soleCands I o₀) (SumcheckRound.rel (shareFamily I) 0)
      (x s, (#v[], s)) h)
    (fun h₀ s hp ↦ ⟨hP _ _ hp, hd s _ (hP _ _ hp)⟩) zero_le).bind' fun share ↦
  ((wireSumcheckSpec (T := 0) (shareFamily I) (soleCands I o₀) (shareFamily_consistent I)
      (shareFamily_sound I) (fun _ ↦ Set.finite_singleton o₀) (soleCands_ncard I o₀) (by norm_num) he
      (x share) (List.replicate 4 none) 0 #v[] share rfl (shareWeights I (x share))).frame P
      hP).bind' fun r ↦
  (Spec.readE (Post := fun value h ↦ P h ∧ (share = shareTotal W B ∨
      r.2 ≠ evalMle W (vecOf 4 r.1) * evalMle B (vecOf 4 r.1)) ∧ r.1.length = 4)
    (fun h₀ value hp ↦ by
      obtain ⟨hp, hl, hD⟩ := hp
      refine ⟨hP _ _ hp, ?_, by simpa using hl⟩
      obtain ⟨-, hR⟩ := (shareDoom_iff I o₀ _ _).mp hD
      simp only [Vector.toList_empty, List.nil_append] at hR
      rcases hR with hR | hR
      · exact .inl (by simpa [shareWrong] using hR)
      · right
        rw [shareClaim_self] at hR
        exact hR) hT).bind' fun value ↦
  (Spec.require (Post := fun _ h ↦ P h ∧ (share = shareTotal W B ∨
      value ≠ evalMle B (vecOf 4 r.1)) ∧ r.1.length = 4)
    fun h₀ hp hc ↦ by
      obtain ⟨hp, hR, hl⟩ := hp
      refine ⟨hp, ?_, hl⟩
      rcases hR with hR | hR
      · exact .inl hR
      · right
        intro hv
        rw [hc, dot_eqKernel_eq_evalMle hw hl, hv] at hR
        exact hR rfl).bind' fun _ ↦
  (Spec.require (Post := fun _ h ↦ P h ∧ share = shareTotal W B)
    fun h₀ hp hc ↦ by
      obtain ⟨hp, hR, hl⟩ := hp
      refine ⟨hp, hR.resolve_right fun hn ↦ hn ?_⟩
      rw [← hc, multilinearEval_eq_slotValues hwords hl]).bind' fun _ ↦
  (Spec.ret (Post := fun r h ↦ P h ∧ r.1 = shareTotal W B) (share, low ++ r.1, value)).mono
    (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end
end LeanVM.Protocol.EndToEnd.Front
