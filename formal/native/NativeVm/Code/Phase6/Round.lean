module

public import NativeVm.Code.Phase6.Sumcheck

/-!
# A sumcheck round

`roundP_refines`, `roundE_refines`: one round of `Model.sumcheck` (its message, its challenge, the
next claim), from a scratch `g` holding the round `k` and the claim, to one that differs from `g`
only on the round's temporaries (`Tmp`) and the challenge at `co + k`.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code
open NativeVm.Transcript (wd Env)
open Finset

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW}

/-- The round's temporaries: the claim, the round, the message and the challenge. -/
def Tmp (i : Nat) : Prop := i = eSC ∨ i = eRK ∨ (eMsg ≤ i ∧ i < eMsg + 4) ∨ i = eCh

theorem grindingBits_small {n : Nat} (hn : n ≤ 4) : grindingBits n = 0 := by
  interval_cases n <;> decide

theorem grind_small {n : Nat} (hn : n ≤ 4) : Model.grind (grindingBits n) = pure () := by
  rw [grindingBits_small hn]; rfl

/-- A plain round, its message's steps in order. -/
def roundPM (c : Nat) (claim : EW) (acc1 : Array EW) : VM (Array EW × EW) :=
  Model.readScalar >>= fun constant ↦ readScalars (c - 2) >>= fun tail ↦
    Model.sampleChallenge >>= fun ch ↦
      pure (acc1.push ch, polyEval (#[constant, claim + sumE tail] ++ tail) ch)

/-- An equality-mode round, its message's steps in order. -/
def roundEM (c : Nat) (claim e : EW) (acc1 : Array EW) : VM (Array EW × EW) :=
  readScalars (c - 1) >>= fun tail ↦ Model.sampleChallenge >>= fun ch ↦
    pure (acc1.push ch, polyEval (#[claim + e * sumE tail] ++ tail) ch)

theorem roundPM_eq {c : Nat} (hc : 2 ≤ c ∧ c ≤ 4) (acc : Array EW × EW) :
    (Model.sumcheckRoundPoly c acc.2 none >>= fun message ↦ Model.sampleChallenge >>= fun ch ↦
      pure (acc.1.push ch, polyEval message ch)) = roundPM c acc.2 acc.1 := by
  simp only [Model.sumcheckRoundPoly, roundPM, bind_assoc, grind_small (show c - 1 ≤ 4 by omega),
    pure_bind]

theorem roundEM_eq {c : Nat} (hc : 1 ≤ c ∧ c ≤ 3) (acc : Array EW × EW) (e : EW) :
    (Model.sumcheckRoundPoly c acc.2 (some e) >>= fun message ↦ Model.sampleChallenge >>= fun ch ↦
      pure (acc.1.push ch, polyEval message ch)) = roundEM c acc.2 e acc.1 := by
  simp only [Model.sumcheckRoundPoly, roundEM, bind_assoc,
    grind_small (show c - 1 + 1 ≤ 4 by omega), pure_bind]

/-- An array's values, entry by entry. -/
theorem toList_map_toE (a : Array EW) :
    a.toList.map EW.toE = (List.range a.size).map fun i ↦ (a.getD i 0).toE := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using h1)]
  rfl

theorem vals_eq {g : Nat → EW} {o : Nat} (a : Array EW) (h : ∀ i < a.size, g (o + i) = a.getD i 0) :
    vals g o a.size = a.toList.map EW.toE := by
  rw [toList_map_toE, vals]
  exact List.map_congr_left fun i hi ↦ by rw [h i (List.mem_range.1 hi)]

/-- Read `g` through updates at other indices. -/
macro "upd_simp" : tactic => `(tactic| (
  repeat (first
    | rw [Function.update_self]
    | (rw [Function.update_of_ne]; on_goal 2 => p6_ne)
    | (rw [Function.update_of_ne]; p6_ne))))

variable (env inp s0)

/-- What follows the message: the challenge, stored at `co + k`, the next claim, the round
counted. -/
theorem roundTail (hin : Inputs env inp s0.mem) {c co k n : Nat} (hc : c ≤ 4) (hco : 28 ≤ co)
    (hk : co + k < scrN) (msg : Array EW) (hmsg : msg.size = c) (acc1 : Array EW) (eqm : Bool)
    (g : Nat → EW) (hrk : g eRK = EW.ofK k.toUInt64) (hn : g ePtN = EW.ofK n.toUInt64)
    (hm : ∀ i < c, g (eMsg + i) = msg.getD i 0) :
    Refines (St env s0 g) (blk [smpEl eCh, chSt co, peval c, incRK eqm])
      (Model.sampleChallenge >>= fun ch ↦ pure (acc1.push ch, polyEval msg ch))
      (fun acc t s ↦ ∃ ch, acc = (acc1.push ch, polyEval msg ch) ∧
        St env s0 (Function.update (Function.update (Function.update (Function.update g eCh ch)
          (co + k) ch) eSC (polyEval msg ch)) eRK (EW.ofK (k + 1).toUInt64)) t s ∧
        s.reg .r15 = (k + 1).toUInt64 ∧ (eqm = true → s.reg .r13 = n.toUInt64))
      (Kept env rs6 s0) := by
  refine Refines.blk_cons (smpEl_refines env inp s0 hin (by p6_omega) g) fun ch ↦ Refines.pure
    fun t s h ↦ ?_
  refine WP.blk_cons (WP.mono (chSt_spec env inp s0 hin hk h (by upd_simp; exact hrk))
    (fun s1 h1 ↦ ?_) (fun _ h ↦ h))
  refine WP.blk_cons (WP.mono (peval_spec env inp s0 hin (x := polyEval msg ch) hc h1 ?_)
    (fun s2 h2 ↦ ?_) (fun _ h ↦ h))
  · rw [NativeVm.Equiv.toE_polyEval]
    congr 1
    · rw [← hmsg]
      refine (vals_eq msg fun i hi ↦ ?_).symm
      upd_simp
      exact hm i (by omega)
    · upd_simp
  refine WP.mono (incRK_spec env inp s0 hin (eqm := eqm) (k := k) (n := n) h2 (by upd_simp; exact hrk)
    (by upd_simp; exact hn)) (fun s3 ⟨h3, h4, h5⟩ ↦ ⟨ch, rfl, ?_, h4, h5⟩) (fun _ h ↦ h)
  have e : Function.update (Function.update g eCh ch) (co + k) (Function.update g eCh ch eCh) =
      Function.update (Function.update g eCh ch) (co + k) ch := by rw [Function.update_self]
  rw [e] at h3
  exact h3

/-- After a round: the challenge pushed, the scratch `g` with the challenge at `co + k`, up to the
temporaries, the round `k + 1`, the next claim. -/
def RPost (env : Env) (s0 : QState) (g : Nat → EW) (co k n : Nat) (eqm : Bool) (acc1 : Array EW)
    (acc : Array EW × EW) (t : TState) (s : QState) : Prop :=
  ∃ ch, acc.1 = acc1.push ch ∧ ∃ g', St env s0 g' t s ∧
    (∀ i, ¬ Tmp i → g' i = Function.update g (co + k) ch i) ∧ g' eRK = EW.ofK (k + 1).toUInt64 ∧
    g' eSC = acc.2 ∧ g' ePtN = g ePtN ∧ s.reg .r15 = (k + 1).toUInt64 ∧
    (eqm = true → s.reg .r13 = n.toUInt64)

theorem getD_pair_append (a b : EW) (tail : Array EW) (j : Nat) :
    (#[a, b] ++ tail).getD (j + 2) 0 = tail.getD j 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_append_right]

theorem getD_one_append (a : EW) (tail : Array EW) (j : Nat) :
    (#[a] ++ tail).getD (j + 1) 0 = tail.getD j 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_append_right]

/-- The post of `roundTail` is `RPost` when the scratch before the challenge differs from `g`
only on temporaries. -/
theorem rpost_of {co k n : Nat} {eqm : Bool} {acc1 : Array EW} {g g3 : Nat → EW} {msg : Array EW}
    (hco : 28 ≤ co) (hag : ∀ i, ¬ Tmp i → g3 i = g i) (hn : g3 ePtN = g ePtN)
    {acc : Array EW × EW} {t : TState} {s : QState}
    (h : ∃ ch, acc = (acc1.push ch, polyEval msg ch) ∧
        St env s0 (Function.update (Function.update (Function.update (Function.update g3 eCh ch)
          (co + k) ch) eSC (polyEval msg ch)) eRK (EW.ofK (k + 1).toUInt64)) t s ∧
        s.reg .r15 = (k + 1).toUInt64 ∧ (eqm = true → s.reg .r13 = n.toUInt64)) :
    RPost env s0 g co k n eqm acc1 acc t s := by
  obtain ⟨ch, rfl, hst, h15, h13⟩ := h
  refine ⟨ch, rfl, _, hst, fun i hi ↦ ?_, Function.update_self .., ?_, ?_, h15, h13⟩
  · unfold Tmp at hi
    simp only [not_or, not_and, not_lt] at hi
    rw [Function.update_of_ne hi.2.1, Function.update_of_ne hi.1]
    by_cases hik : i = co + k
    · subst hik; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hik, Function.update_of_ne hik, Function.update_of_ne hi.2.2.2,
        hag i (by unfold Tmp; omega)]
  · rw [Function.update_of_ne (by p6_ne), Function.update_self]
  · rw [Function.update_of_ne (by p6_ne), Function.update_of_ne (by p6_ne),
      Function.update_of_ne (by p6_omega), Function.update_of_ne (by p6_ne), hn]

/-- **A plain round** of `c` coefficients, its challenge to `co + k`. -/
theorem roundP_refines (hin : Inputs env inp s0.mem) {c co k n : Nat} (hc : 2 ≤ c ∧ c ≤ 4)
    (hco : 28 ≤ co) (hk : co + k < scrN) (claim : EW) (acc1 : Array EW) (g : Nat → EW)
    (hrk : g eRK = EW.ofK k.toUInt64) (hn : g ePtN = EW.ofK n.toUInt64) (hsc : g eSC = claim) :
    Refines (St env s0 g) (roundP c co) (roundPM c claim acc1)
      (RPost env s0 g co k n false acc1) (Kept env rs6 s0) := by
  unfold roundP roundPM
  refine Refines.blk_cons (rdEl_refines env inp s0 hin (by p6_omega) g) fun constant ↦ ?_
  refine Refines.blk_cons (rdN_refines env inp s0 hin (o := eMsg + 2) (n := c - 2) (by p6_omega)
    (by omega) _) fun tail ↦ Refines.intro fun htail ↦ ?_
  set g2 := wrA (Function.update g eMsg constant) (eMsg + 2) tail with hg2
  have h2sc : g2 eSC = claim := by
    rw [hg2, wrA_out (by p6_ne), Function.update_of_ne (by p6_ne), hsc]
  refine Refines.pre_blk (P' := St env s0 (Function.update g2 (eMsg + 1) (claim + sumE tail)))
    (fun t s h ↦ mid1_spec env inp s0 hin hc h ?_) ?_
  · rw [NativeVm.Equiv.EW.toE_add, toE_sumE_range, htail, h2sc]
    congr 1
    refine sum_congr rfl fun i hi ↦ ?_
    rw [hg2, wrA_in (by rw [htail]; exact mem_range.1 hi)]
  refine Refines.mono (roundTail env inp s0 hin (by omega) hco hk (#[constant, claim + sumE tail] ++ tail)
    (by simp [htail]; omega) acc1 false _ ?_ ?_ ?_) (fun _ _ h ↦ h)
    (fun acc t s h ↦ rpost_of env s0 (g := g) hco ?_ ?_ h) (fun _ h ↦ h)
  · rw [Function.update_of_ne (by p6_ne), hg2, wrA_out (by p6_ne), Function.update_of_ne (by p6_ne)]
    exact hrk
  · rw [Function.update_of_ne (by p6_ne), hg2, wrA_out (by p6_ne), Function.update_of_ne (by p6_ne)]
    exact hn
  · intro i hi
    rcases i with _ | _ | j
    · rw [Function.update_of_ne (by p6_ne), hg2, wrA_out (by p6_ne), Nat.add_zero,
        Function.update_self]; simp [Array.getD_eq_getD_getElem?]
    · rw [Function.update_self]; simp [Array.getD_eq_getD_getElem?, Array.getElem?_append_left]
    · rw [Function.update_of_ne (by p6_ne), hg2, show eMsg + (j + 2) = eMsg + 2 + j by omega,
        wrA_in (by omega), getD_pair_append]
  · intro i hi
    unfold Tmp at hi
    rw [Function.update_of_ne (by omega), hg2, wrA_out (by rw [htail]; omega),
      Function.update_of_ne (by omega)]
  · rw [Function.update_of_ne (by p6_ne), hg2, wrA_out (by p6_ne), Function.update_of_ne (by p6_ne)]

/-- **An equality-mode round** of `c` coefficients, the equality factor `e` at `ePt + k`, its
challenge to `ePt + k`. -/
theorem roundE_refines (hin : Inputs env inp s0.mem) {c k n : Nat} (hc : 1 ≤ c ∧ c ≤ 3)
    (hk : ePt + k < scrN) (claim e : EW) (acc1 : Array EW) (g : Nat → EW) (hk32 : k < 32)
    (hrk : g eRK = EW.ofK k.toUInt64) (hn : g ePtN = EW.ofK n.toUInt64) (hsc : g eSC = claim)
    (he : g (ePt + k) = e) :
    Refines (St env s0 g) (roundE c ePt) (roundEM c claim e acc1)
      (RPost env s0 g ePt k n true acc1) (Kept env rs6 s0) := by
  unfold roundE roundEM
  refine Refines.blk_cons (rdN_refines env inp s0 hin (o := eMsg + 1) (n := c - 1) (by p6_omega)
    (by omega) _) fun tail ↦ Refines.intro fun htail ↦ ?_
  set g2 := wrA g (eMsg + 1) tail with hg2
  have h2sc : g2 eSC = claim := by rw [hg2, wrA_out (by p6_ne), hsc]
  refine Refines.pre_blk (P' := St env s0 (Function.update g2 eMsg (claim + e * sumE tail)))
    (fun t s h ↦ mid0_spec env inp s0 hin (by omega) hk32 h
      (by rw [hg2, wrA_out (by p6_ne)]; exact hrk) ?_) ?_
  · rw [NativeVm.Equiv.EW.toE_add, NativeVm.Equiv.EW.toE_mul, toE_sumE_range, htail, h2sc, hg2, wrA_out (by p6_ne), he]
    congr 2
    refine sum_congr rfl fun i hi ↦ ?_
    rw [wrA_in (by rw [htail]; exact mem_range.1 hi)]
  refine Refines.mono (roundTail env inp s0 hin (by omega) (by p6_ne) hk
    (#[claim + e * sumE tail] ++ tail) (by simp [htail]; omega) acc1 true _ ?_ ?_ ?_)
    (fun _ _ h ↦ h) (fun acc t s h ↦ rpost_of env s0 (g := g) (by p6_ne) ?_ ?_ h) (fun _ h ↦ h)
  · rw [Function.update_of_ne (by p6_ne), hg2, wrA_out (by p6_ne)]; exact hrk
  · rw [Function.update_of_ne (by p6_ne), hg2, wrA_out (by p6_ne)]; exact hn
  · intro i hi
    rcases i with _ | j
    · rw [Nat.add_zero, Function.update_self]; simp [Array.getD_eq_getD_getElem?]
    · rw [Function.update_of_ne (by p6_ne), hg2, show eMsg + (j + 1) = eMsg + 1 + j by omega,
        wrA_in (by omega), getD_one_append]
  · intro i hi
    unfold Tmp at hi
    rw [Function.update_of_ne (by omega), hg2, wrA_out (by rw [htail]; omega)]
  · rw [Function.update_of_ne (by p6_ne), hg2, wrA_out (by p6_ne)]

end NativeVm.Code.P6
