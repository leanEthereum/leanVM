import Rv64Verifier.Model.Transcript
import Rv64Verifier.Model.Multilinear

/-!
# The Keccak reduction as the Rust computes it

`crates/verifier/src/keccak.rs`: mirrors of `verify_layer` (`verifyLayerRust`), `open`
(`openRust`) and `verify_keccak` (`verifyKeccakRust`) in `TM`, following the Rust's reads,
samples and loops (a `for` loop that reads the transcript is a `List.foldlM`), the checks in
checked mode. Their simulations of the statement's `verifyKeccakLayer`, `keccakOpen` and
`verifyKeccak` at `KECCAK_DEPTH = 12` are `verifyLayerRust_sim`, `openRust_sim` and
`verifyKeccakRust_sim`. The arithmetic the two compute differently is proved equal in pure Lean:
the RMFE tables (`decide +kernel`), the instance weights, the projected value and `iota`, the
final check's split kernel, the next weights, `linear_transpose`, and `open`'s row.

`Claim` is the statement's `KeccakClaim` (the same four fields). `KECCAK_RC`, `KECCAK_RHO`,
`KECCAK_PI` and `along` are the statement's `keccakRC`, `keccakRho`, `keccakPi` and
`keccakAlong`, which transcribe them. `SimR` is `Sim` with a postcondition on the mirror's value,
so that a continuation may use what its predecessor returned (a length).
-/

namespace Rv64Verifier.Model.Gkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Finset

/-! ## Simulation with a postcondition -/

/-- `m` runs `P`, and what it returns satisfies `R`. -/
def SimR {α : Type} (m : TM α) (P : VerifierProgram α) (R : α → Prop) : Prop :=
  ∀ t a t', m.run t = some (a, t') → runK P t.toSpec = some (a, t'.toSpec) ∧ R a

theorem vp_bind_assoc {α β γ : Type} (P : VerifierProgram α) (f : α → VerifierProgram β)
    (g : β → VerifierProgram γ) : (P >>= f) >>= g = P >>= fun a ↦ f a >>= g := by
  show VerifierProgram.bind (VerifierProgram.bind P f) g =
    VerifierProgram.bind P fun a ↦ VerifierProgram.bind (f a) g
  induction P with
  | ret a => rfl
  | fail => rfl
  | read k ih => simp only [VerifierProgram.bind, ih]
  | sample k ih => simp only [VerifierProgram.bind, ih]
  | grind b k ih => simp only [VerifierProgram.bind, ih]
  | commit h w k ih => simp only [VerifierProgram.bind, ih]
  | query i ps k ih => simp only [VerifierProgram.bind, ih]

namespace SimR

variable {α β : Type}

theorem toSim {m : TM α} {P : VerifierProgram α} {R : α → Prop} (h : SimR m P R) : Sim m P :=
  fun t a t' hr ↦ (h t a t' hr).1

theorem ofSim {m : TM α} {P : VerifierProgram α} (h : Sim m P) : SimR m P fun _ ↦ True :=
  fun t a t' hr ↦ ⟨h t a t' hr, trivial⟩

theorem bind {m : TM α} {P : VerifierProgram α} {R : α → Prop} {k : α → TM β}
    {Q : α → VerifierProgram β} {S : β → Prop} (hm : SimR m P R)
    (hk : ∀ a, R a → SimR (k a) (Q a) S) : SimR (m >>= k) (P >>= Q) S := by
  intro t b t' h
  rw [StateT.run_bind] at h
  cases hmt : m.run t with
  | none => rw [hmt] at h; cases h
  | some p =>
    obtain ⟨a, t₁⟩ := p
    rw [hmt] at h
    obtain ⟨h1, h2⟩ := hm t a t₁ hmt
    rw [runK_bind, h1]
    exact hk a h2 t₁ b t' h

theorem pure {a b : α} {S : α → Prop} (hab : a = b) (h : S a) :
    SimR (Pure.pure a : TM α) (VerifierProgram.ret b) S := by
  subst hab
  intro t c t' hr
  simp only [StateT.run_pure] at hr
  cases hr
  exact ⟨rfl, h⟩

theorem nextScalar : SimR TM.nextScalar VerifierProgram.readScalar fun _ ↦ True :=
  ofSim Sim.nextScalar

theorem sample : SimR TM.sample VerifierProgram.sampleChallenge fun _ ↦ True :=
  ofSim Sim.sample

theorem nextScalars : ∀ n, SimR (TM.nextScalars n) (VerifierProgram.readScalars n)
    fun l ↦ l.length = n
  | 0 => pure rfl rfl
  | n + 1 => bind nextScalar fun _ _ ↦ bind (nextScalars n) fun _ h ↦ pure rfl (by simp [h])

theorem samples : ∀ n, SimR (TM.samples n) (VerifierProgram.sampleChallenges n)
    fun l ↦ l.length = n
  | 0 => pure rfl rfl
  | n + 1 => bind sample fun _ _ ↦ bind (samples n) fun _ h ↦ pure rfl (by simp [h])

theorem require {c c' : Prop} [Decidable c] [Decidable c'] (h : c ↔ c') :
    SimR (TM.require c) (VerifierProgram.require c') fun _ ↦ c := by
  intro t a t' hr
  simp only [TM.require, StateT.run] at hr
  split_ifs at hr with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨-, rfl⟩ := hr
  simp only [VerifierProgram.require, h.mp hc, ↓reduceIte]
  exact ⟨rfl, hc⟩

/-- A check the statement does not make. -/
theorem require_left {c : Prop} [Decidable c] {k : TM α} {K : VerifierProgram α} {S : α → Prop}
    (h : c → SimR k K S) : SimR (TM.require c >>= fun _ ↦ k) K S := by
  intro t a t' hr
  rw [StateT.run_bind] at hr
  by_cases hc : c
  · have e : (TM.require c).run t = some ((), t) := by simp [TM.require, StateT.run, hc]
    rw [e] at hr
    exact h hc t a t' hr
  · have e : (TM.require c).run t = none := by simp [TM.require, StateT.run, hc]
    rw [e] at hr
    cases hr

end SimR

/-- An `Err` of a pure step. -/
def TM.fail {α : Type} : TM α := fun _ ↦ none

/-! ## `sumcheck_round_poly` and `sumcheck` (`transcript.rs:188-233`) -/

/-- `Transcript::sumcheck_round_poly(count, claim, eq_factor)`. -/
def sumcheckRoundPolyRust (count : ℕ) (claim : E) : Option E → TM (List E)
  | none => do
    let constant ← TM.nextScalar
    let tail ← TM.nextScalars (count - 2)
    pure (constant :: (claim + sumE tail) :: tail)
  | some eqFactor => do
    let tail ← TM.nextScalars (count - 1)
    pure ((claim + eqFactor * sumE tail) :: tail)

theorem sumcheckRoundPoly_sim (count : ℕ) (claim : E) : ∀ e : Option E,
    SimR (sumcheckRoundPolyRust count claim e) (sumcheckRoundPoly count claim e) fun _ ↦ True
  | none => SimR.bind SimR.nextScalar fun _ _ ↦
      SimR.bind (SimR.nextScalars _) fun _ _ ↦ SimR.pure rfl trivial
  | some _ => SimR.bind (SimR.nextScalars _) fun _ _ ↦ SimR.pure rfl trivial

/-- One iteration of `sumcheck`'s loop: the round polynomial, the challenge, `point.push`, the
claim at the challenge. -/
def sumcheckRound (count : ℕ) (acc : List E × E) (equality : Option E) : TM (List E × E) := do
  let message ← sumcheckRoundPolyRust count acc.2 equality
  let challenge ← TM.sample
  pure (acc.1 ++ [challenge], polyEvalRust message challenge)

/-- `sumcheck(transcript, claim, count, equalities)`. -/
def sumcheckRust (claim : E) (count : ℕ) (equalities : List (Option E)) : TM (List E × E) :=
  equalities.foldlM (sumcheckRound count) ([], claim)

theorem sumcheck_sim {β : Type} (count : ℕ) {S : β → Prop} : ∀ (eqs : List (Option E))
    (pre : List E) (claim : E) (k : List E × E → TM β) (K : List E × E → VerifierProgram β),
    (∀ p v, p.length = eqs.length → SimR (k (pre ++ p, v)) (K (p, v)) S) →
    SimR (eqs.foldlM (sumcheckRound count) (pre, claim) >>= k) (sumcheck claim count eqs >>= K) S
  | [], pre, claim, k, K, h => by
    have h0 := h [] claim rfl
    rw [List.append_nil] at h0
    simp only [List.foldlM_nil, pure_bind]
    exact h0
  | e :: es, pre, claim, k, K, h => by
    simp only [List.foldlM_cons, sumcheckRound, bind_assoc, pure_bind]
    rw [sumcheck]
    simp only [vp_bind_assoc]
    refine SimR.bind (sumcheckRoundPoly_sim count claim e) fun message _ ↦
      SimR.bind SimR.sample fun c _ ↦ ?_
    rw [polyEvalRust_eq]
    refine sumcheck_sim count es (pre ++ [c]) _ k _ fun p v hp ↦ ?_
    have h1 := h (c :: p) v (by simp [hp])
    rw [List.append_assoc, List.singleton_append]
    exact h1

theorem sumcheckRust_sim {β : Type} (claim : E) (count : ℕ) (eqs : List (Option E))
    {k : List E × E → TM β} {K : List E × E → VerifierProgram β} {S : β → Prop}
    (h : ∀ p v, p.length = eqs.length → SimR (k (p, v)) (K (p, v)) S) :
    SimR (sumcheckRust claim count eqs >>= k) (sumcheck claim count eqs >>= K) S :=
  sumcheck_sim count eqs [] claim k K h

/-! ## The pack rounds (`keccak.rs:152-161`) -/

/-- One iteration of the pack and segment loop: `value`, `scale`, `point`. -/
def packRound (acc : E × E × List E) (r : E) : TM (E × E × List E) := do
  let message ← sumcheckRoundPolyRust 3 acc.1 (some r)
  let challenge ← TM.sample
  pure ((1 + r + challenge) * polyEvalRust message challenge, acc.2.1 * (1 + r + challenge),
    acc.2.2 ++ [challenge])

theorem packRounds_sim {β : Type} {S : β → Prop} : ∀ (rs : List E) (value scale : E)
    (pre : List E) (k : E × E × List E → TM β) (K : E × E × List E → VerifierProgram β),
    (∀ v s p, p.length = rs.length → SimR (k (v, s, pre ++ p)) (K (v, s, p)) S) →
    SimR (rs.foldlM packRound (value, scale, pre) >>= k) (keccakPackRounds rs value scale >>= K) S
  | [], value, scale, pre, k, K, h => by
    have h0 := h value scale [] rfl
    rw [List.append_nil] at h0
    simp only [List.foldlM_nil, pure_bind]
    exact h0
  | r :: rs, value, scale, pre, k, K, h => by
    simp only [List.foldlM_cons, packRound, bind_assoc, pure_bind]
    rw [keccakPackRounds]
    simp only [vp_bind_assoc]
    refine SimR.bind (sumcheckRoundPoly_sim 3 value (some r)) fun message _ ↦
      SimR.bind SimR.sample fun c _ ↦ ?_
    rw [polyEvalRust_eq]
    refine packRounds_sim rs _ _ (pre ++ [c]) k _ fun v s p hp ↦ ?_
    have h1 := h v s (c :: p) (by simp [hp])
    rw [List.append_assoc, List.singleton_append]
    exact h1


/-! ## Sums -/

theorem sumE_eq_sum (l : List E) : sumE l = l.sum := by
  unfold sumE
  suffices h : ∀ a : E, l.foldl (· + ·) a = a + l.sum by simpa using h 0
  induction l with
  | nil => simp
  | cons x l ih => intro a; rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

theorem list_sum_range (f : ℕ → E) (n : ℕ) :
    ((List.range n).map f).sum = ∑ y ∈ range n, f y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem list_sum_getD (l : List E) : l.sum = ∑ i ∈ range l.length, l.getD i 0 := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']; simp [add_comm]

theorem sumE_filter_map_range (n : ℕ) (p : ℕ → Bool) (f : ℕ → E) :
    sumE (((List.range n).filter p).map f) = ∑ b ∈ range n, if p b then f b else 0 := by
  rw [sumE_eq_sum]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]

theorem sumE_filterMap_range (n : ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → E) :
    sumE ((List.range n).filterMap fun b ↦ if p b then some (f b) else none) =
      ∑ b ∈ range n, if p b then f b else 0 := by
  rw [sumE_eq_sum]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filterMap_append, List.sum_append, ih, Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]

theorem sumE_zip_filterMap (p : ℕ → Prop) [DecidablePred p] : ∀ (l₁ : List E) (l₂ : List ℕ),
    sumE ((List.zip l₁ l₂).filterMap fun x ↦ if p x.2 then some x.1 else none) =
      ∑ i ∈ range l₂.length, if p (l₂.getD i 0) then l₁.getD i 0 else 0
  | _, [] => by simp [sumE]
  | [], _ :: l₂ => by simp [sumE]
  | x :: l₁, y :: l₂ => by
    rw [List.zip_cons_cons, List.length_cons, Finset.sum_range_succ']
    have ih := sumE_zip_filterMap p l₁ l₂
    rw [sumE_eq_sum] at ih ⊢
    by_cases hp : p y
    · simp only [List.filterMap_cons, hp, ite_true, List.sum_cons, ih, List.getD_cons_succ,
        List.getD_cons_zero]
      ring
    · simp only [List.filterMap_cons, hp, ite_false, ih, List.getD_cons_succ, List.getD_cons_zero,
        add_zero]

theorem sum_range_mul (a b : ℕ) (F : ℕ → E) :
    ∑ p ∈ range (a * b), F p = ∑ i ∈ range a, ∑ k ∈ range b, F (b * i + k) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Nat.mul_comm a b]

theorem sum_range_two_mul (N : ℕ) (F : ℕ → E) :
    ∑ w ∈ range (2 * N), F w = ∑ w ∈ range N, (F (2 * w) + F (2 * w + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

theorem sum_cube_succ (m : ℕ) (F : ℕ → E) :
    ∑ w ∈ range (2 ^ (m + 1)), F w = ∑ w ∈ range (2 ^ m), (F (2 * w) + F (2 * w + 1)) := by
  rw [pow_succ, mul_comm, sum_range_two_mul]

/-! ## Lists -/

theorem list_set_getD (l : List E) (i p : ℕ) (x : E) :
    (l.set i x).getD p 0 = if i = p ∧ i < l.length then x else l.getD p 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h1 : i = p
  · subst h1
    by_cases h2 : i < l.length
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem getD_range_map {α : Type} (f : ℕ → α) (d : α) {n i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

theorem ext_getD {l₁ l₂ : List E} (hl : l₁.length = l₂.length)
    (h : ∀ i < l₁.length, l₁.getD i 0 = l₂.getD i 0) : l₁ = l₂ := by
  apply List.ext_getElem hl
  intro i h1 h2
  have := h i h1
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem zipIdx_eq_map {α : Type} (l : List α) (d : α) :
    l.zipIdx = (List.range l.length).map fun i ↦ (l.getD i d, i) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_zipIdx] at h1
  simp [List.getElem_zipIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

theorem zip_range_map {α : Type} (f : ℕ → α) (l : List E) {n : ℕ} (hn : n ≤ l.length) :
    ((List.range n).map f).zip l = (List.range n).map fun i ↦ (f i, l.getD i 0) := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.length_zip, List.length_map, List.length_range] at h1
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < l.length by omega)]

/-- A fold that adds to the entries of a buffer of `N`. -/
theorem foldl_acc {α : Type} (N : ℕ) (δ : α → ℕ → E) (step : List E → α → List E) :
    ∀ (L : List α) (row : List E), row.length = N →
    (∀ r x, x ∈ L → r.length = N →
      (step r x).length = N ∧ ∀ q, (step r x).getD q 0 = r.getD q 0 + δ x q) →
    (L.foldl step row).length = N ∧
      ∀ q, (L.foldl step row).getD q 0 = row.getD q 0 + (L.map fun x ↦ δ x q).sum
  | [], row, hrow, _ => ⟨hrow, fun q ↦ by simp⟩
  | x :: L, row, hrow, h => by
    obtain ⟨h1, h2⟩ := h row x (by simp) hrow
    obtain ⟨h3, h4⟩ := foldl_acc N δ step L (step row x) h1
      (fun r y hy hr ↦ h r y (by simp [hy]) hr)
    refine ⟨h3, fun q ↦ ?_⟩
    rw [List.foldl_cons, h4, h2, List.map_cons, List.sum_cons, add_assoc]

/-- The step `row[i] += v`. -/
theorem addAt_step (r : List E) (i : ℕ) (v : E) :
    (r.set i (r.getD i 0 + v)).length = r.length ∧ ∀ q, (r.set i (r.getD i 0 + v)).getD q 0 =
      r.getD q 0 + if i = q ∧ i < r.length then v else 0 := by
  refine ⟨by simp, fun q ↦ ?_⟩
  rw [list_set_getD]
  split_ifs with h
  · rw [h.1]
  · rw [add_zero]

/-! ## Equality weights (as `lean_vm`'s `LeanVM.Protocol.Keccak.Multilinear`) -/

/-- The equality weight of index `w` at the point `pt`, the first coordinate on the lowest bit. -/
def eqAt : List E → ℕ → E
  | [], _ => 1
  | r :: rs, w => (if w % 2 = 1 then r else 1 + r) * eqAt rs (w / 2)

theorem eqAt_cons (r : E) (rs : List E) (w : ℕ) :
    eqAt (r :: rs) w = (if w % 2 = 1 then r else 1 + r) * eqAt rs (w / 2) := rfl

theorem eqAt_mod : ∀ (pt : List E) (w : ℕ), eqAt pt w = eqAt pt (w % 2 ^ pt.length)
  | [], _ => rfl
  | r :: rs, w => by
    rw [eqAt_cons, eqAt_cons, List.length_cons, pow_succ, mul_comm (2 ^ rs.length) 2,
      Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self, ← eqAt_mod rs]

theorem eqAt_append : ∀ (a b : List E) (w : ℕ),
    eqAt (a ++ b) w = eqAt a w * eqAt b (w / 2 ^ a.length)
  | [], b, w => by simp [eqAt]
  | r :: a, b, w => by
    rw [List.cons_append, eqAt_cons, eqAt_cons, eqAt_append a b, List.length_cons, pow_succ,
      Nat.div_div_eq_div_mul, mul_comm (2 ^ a.length) 2, mul_assoc]

theorem eqKernel_snoc (pt : List E) (r : E) :
    eqKernel (pt ++ [r]) = (eqKernel pt).map (· * (1 + r)) ++ (eqKernel pt).map (· * r) := by
  unfold eqKernel
  rw [List.foldl_concat]

theorem getD_map_mul (l : List E) (c : E) (w : ℕ) :
    (l.map (· * c)).getD w 0 = l.getD w 0 * c := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[w]? <;> simp

theorem eqKernel_getD : ∀ (pt : List E) (w : ℕ),
    (eqKernel pt).getD w 0 = if w < 2 ^ pt.length then eqAt pt w else 0 := by
  intro pt
  induction pt using List.reverseRecOn with
  | nil =>
    intro w
    rcases w with _ | w
    · rfl
    · simp [eqKernel, List.getD_eq_getElem?_getD]
  | append_singleton pt r ih =>
    intro w
    have hlen := eqKernel_length pt
    rw [eqKernel_snoc, List.length_append, List.length_singleton, eqAt_append]
    by_cases hw : w < 2 ^ pt.length
    · rw [List.getD_append _ _ _ _ (by simpa [hlen] using hw), getD_map_mul, ih,
        ite_eq_left hw, ite_eq_left (by rw [pow_succ]; omega), Nat.div_eq_of_lt hw]
      simp [eqAt]
    · rw [List.getD_append_right _ _ _ _ (by simp [hlen]; omega), List.length_map, hlen,
        getD_map_mul, ih]
      by_cases hw2 : w < 2 ^ (pt.length + 1)
      · have hw2' : w < 2 ^ pt.length + 2 ^ pt.length := by rw [pow_succ] at hw2; omega
        have hq : w / 2 ^ pt.length = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
        rw [ite_eq_left hw2, hq, ite_eq_left (by omega), eqAt_mod pt w,
          eqAt_mod pt (w - 2 ^ pt.length), ← Nat.mod_eq_sub_mod (by omega)]
        simp [eqAt]
      · rw [ite_eq_right hw2, ite_eq_right (by rw [pow_succ] at hw2; omega), zero_mul]

theorem dot_eq : ∀ (a b : List E), a.length = b.length →
    dot a b = ∑ j ∈ range a.length, a.getD j 0 * b.getD j 0 := by
  intro a b h
  unfold dot
  rw [← sumE, sumE_eq_sum]
  induction a generalizing b with
  | nil => simp
  | cons x a ih =>
    rcases b with _ | ⟨y, b⟩
    · simp at h
    · simp only [List.zipWith_cons_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ']
      rw [ih b (by simpa using h)]
      simp [add_comm]

theorem dot_eqKernel (pt w : List E) (hn : w.length ≤ 2 ^ pt.length) :
    dot ((eqKernel pt).take w.length) w = ∑ j ∈ range w.length, eqAt pt j * w.getD j 0 := by
  rw [dot_eq _ _ (by simp [eqKernel_length, hn]), List.length_take, eqKernel_length,
    min_eq_left hn]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' := Finset.mem_range.1 hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hj',
    ← List.getD_eq_getElem?_getD, eqKernel_getD, ite_eq_left (by omega)]

/-- `eq(local, j) = eq_z[z] * eq_lane[lane]`, `j = 64 lane + z`. -/
theorem eqAt_split (pt : List E) (hl : pt.length = 11) (j : ℕ) :
    eqAt pt j = eqAt (pt.take 6) (j % 64) * eqAt (pt.drop 6) (j / 64) := by
  have h6 : (pt.take 6).length = 6 := by simp [hl]
  conv_lhs => rw [← List.take_append_drop 6 pt]
  rw [eqAt_append, h6, eqAt_mod (pt.take 6) j, h6]
  rfl

/-! ## Constants and bits -/

/-- `RMFE_EMBED` (`keccak.rs:25-28`). -/
def rmfeEmbedRust : List (BitVec 32) :=
  [0x40c50b#32, 0x7f79f2#32, 0x4b4e0a#32, 0x72740c#32, 0x5357da#32, 0x1d1c9e#32, 0x04be6e#32,
   0x785246#32, 0x097cdc#32, 0x109e7e#32, 0x1f1454#32, 0x213cfc#32, 0x4cfcc8#32, 0x775770#32,
   0x187386#32, 0x818a16#32]

/-- `RMFE_PROJECT` (`keccak.rs:29-46`). -/
def rmfeProjectRust : List (BitVec 64) :=
  [0x1#64, 0x7fffffffffff#64, 0x274e9d3a74e9#64, 0x1d3a74e9d3a7#64, 0x65cb972e5cb9#64,
   0x5cb972e5cb97#64, 0x6690aec7cd21#64, 0x5d8f9a42bb1f#64, 0x73485763e690#64, 0x3750967c6ea1#64,
   0x12cf8dd4259f#64, 0x1ba84b3e3750#64, 0x0ad0c9f715a1#64, 0x064fb8ad0c9f#64, 0x456864fb8ad0#64,
   0x400000000000#64]

/-- The Rust tables are the ones the statement derives. -/
theorem rmfeEmbedRust_eq : rmfeEmbedRust.map BitVec.toNat = rmfeEmbed := by decide +kernel

theorem rmfeProjectRust_eq : rmfeProjectRust.map BitVec.toNat = rmfeProject := by decide +kernel

/-- `x >> b & 1 == 1` on a `u64`. -/
def bit64 (x : BitVec 64) (b : ℕ) : Bool := (x >>> b) &&& 1#64 == 1#64

/-- `x >> b & 1 == 1` on a `u32`. -/
def bit32 (x : BitVec 32) (b : ℕ) : Bool := (x >>> b) &&& 1#32 == 1#32

theorem bit64_eq (x : BitVec 64) (b : ℕ) : bit64 x b = x.toNat.testBit b := by
  have h : ((x >>> b) &&& 1#64).toNat = (x.toNat >>> b) % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.and_one_is_mod]
  have h2 : (x >>> b &&& 1#64 = 1#64) ↔ (x.toNat >>> b) % 2 = 1 := by
    rw [← BitVec.toNat_inj, h]; simp
  unfold bit64
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
  by_cases hc : (x.toNat >>> b) % 2 = 1
  · simp [hc, h2.mpr hc]
  · simp [hc, mt h2.mp hc]

theorem bit32_eq (x : BitVec 32) (b : ℕ) : bit32 x b = x.toNat.testBit b := by
  have h : ((x >>> b) &&& 1#32).toNat = (x.toNat >>> b) % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.and_one_is_mod]
  have h2 : (x >>> b &&& 1#32 = 1#32) ↔ (x.toNat >>> b) % 2 = 1 := by
    rw [← BitVec.toNat_inj, h]; simp
  unfold bit32
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
  by_cases hc : (x.toNat >>> b) % 2 = 1
  · simp [hc, h2.mpr hc]
  · simp [hc, mt h2.mp hc]

/-- `KeccakShape`: `2^log_steps` permutations, a state committed every `depth` rounds. -/
structure KeccakShape where
  logSteps : ℕ
  depth : ℕ

/-- `KeccakShape::segments`, `ROUNDS / depth`. -/
def KeccakShape.segments (s : KeccakShape) : ℕ := 24 / s.depth

/-- `KeccakShape::pack_bits`, `log_steps - PACK_BITS`. -/
def KeccakShape.packBits (s : KeccakShape) : ℕ := s.logSteps - 4

/-- `KeccakShape::slot_bits`, `log2_ceil((STATE_LANES * segments) as u64)`. -/
def KeccakShape.slotBits (s : KeccakShape) : ℕ := log2CeilRust (BitVec.ofNat 64 (25 * s.segments))

theorem shape_segments (l : ℕ) : (⟨l, 12⟩ : KeccakShape).segments = 2 := by
  simp [KeccakShape.segments]

theorem shape_slotBits (l : ℕ) : (⟨l, 12⟩ : KeccakShape).slotBits = qkeccakSlotBits := by
  rw [KeccakShape.slotBits, shape_segments, log2CeilRust_eq]; decide

/-! ## The projected value and `iota` (`keccak.rs:122-145`) -/

/-- Step 1's projected value: per product coefficient `c`, the instance weights of the masks
holding `c`. -/
def projectedRust (mu product : List E) : E :=
  sumE ((List.range productBits).map fun c ↦
    sumE (((List.range 16).filter fun i ↦ bit64 (rmfeProjectRust.getD i 0#64) c).map fun i ↦
      mu.getD i 0) * product.getD c 0)

/-- The statement's projected value. -/
def projectedSpec (mu product : List E) : E :=
  sumE ((List.range productBits).map fun c ↦
    sumE ((List.zip mu rmfeProject).filterMap fun (m, mask) ↦
      if mask.testBit c then some m else none) * product.getD c 0)

theorem projectedRust_eq (mu product : List E) :
    projectedRust mu product = projectedSpec mu product := by
  unfold projectedRust projectedSpec
  refine congrArg sumE (List.map_congr_left fun c _ ↦ congrArg (· * product.getD c 0) ?_)
  have e : (fun (x : E × ℕ) ↦ match x with | (m, mask) => if mask.testBit c then some m else none) =
      fun x ↦ if x.2.testBit c then some x.1 else none := by
    funext x; rfl
  rw [e, sumE_zip_filterMap (fun mask ↦ mask.testBit c), sumE_filter_map_range, ← rmfeProjectRust_eq,
    List.length_map, show rmfeProjectRust.length = 16 from rfl]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show ((rmfeProjectRust.map BitVec.toNat).getD i 0) = (rmfeProjectRust.getD i 0#64).toNat by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases rmfeProjectRust[i]? <;> rfl, bit64_eq]

/-- Step 1's `iota`: per segment, its weight times the weights of the round constant's bits. -/
def iotaRust (shape : KeccakShape) (step : ℕ) (claim : KeccakClaim) : E :=
  ((eqKernelRust (claim.point.drop shape.packBits)).zipIdx.take shape.segments).foldl
    (fun iota (ws : E × ℕ) ↦
      let constant := (keccakRC.getD (shape.depth * (ws.2 + 1) - step - 1) 0).toBitVec
      iota + ws.1 * sumE (((List.range 64).filter fun z ↦ bit64 constant z).map fun z ↦
        claim.weights.getD z 0)) 0

/-- The statement's `iota`. -/
def iotaSpec (logSteps step : ℕ) (claim : KeccakClaim) : E :=
  sumE ((List.range keccakSegments).map fun segment ↦
    let constant := keccakRC.getD (keccakDepth * (segment + 1) - step - 1) 0
    (eqKernel (claim.point.drop (logSteps - 4))).getD segment 0 *
      sumE ((List.range 64).filterMap fun z ↦
        if constant.toNat.testBit z then some (claim.weights.getD z 0) else none))

/-- The weights of a round constant's bits. -/
def iotaInner (weights : List E) (c : UInt64) : E :=
  ∑ z ∈ range 64, if c.toNat.testBit z then weights.getD z 0 else 0

theorem iotaInner_rust (weights : List E) (c : UInt64) :
    sumE (((List.range 64).filter fun z ↦ bit64 c.toBitVec z).map fun z ↦ weights.getD z 0) =
      iotaInner weights c := by
  rw [sumE_filter_map_range, iotaInner]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [bit64_eq]; rfl

theorem iotaInner_spec (weights : List E) (c : UInt64) :
    sumE ((List.range 64).filterMap fun z ↦
      if c.toNat.testBit z then some (weights.getD z 0) else none) = iotaInner weights c := by
  rw [sumE_filterMap_range, iotaInner]

theorem iota_fold (l : List E) (f : ℕ → E) :
    ((l.zipIdx).take 2).foldl (fun acc (ws : E × ℕ) ↦ acc + ws.1 * f ws.2) 0 =
      sumE ((List.range 2).map fun i ↦ l.getD i 0 * f i) := by
  rw [show List.range 2 = [0, 1] from rfl, sumE_eq_sum]
  rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp only [List.zipIdx_nil, List.take_nil, List.foldl_nil, List.map_cons, List.map_nil,
      List.getD_nil, zero_mul, List.sum_cons, List.sum_nil, add_zero]
  · simp only [List.zipIdx_cons, List.zipIdx_nil, List.take_succ_cons, List.take_nil,
      List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, List.getD_nil, zero_mul, List.sum_cons, List.sum_nil, add_zero, zero_add]
  · simp only [List.zipIdx_cons, List.take_succ_cons, List.take_zero,
      List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, List.sum_cons, List.sum_nil, add_zero, zero_add]

theorem iotaRust_eq (logSteps step : ℕ) (claim : KeccakClaim) :
    iotaRust ⟨logSteps, 12⟩ step claim = iotaSpec logSteps step claim := by
  unfold iotaRust iotaSpec
  simp only [iotaInner_rust, iotaInner_spec]
  rw [eqKernelRust_eq, shape_segments]
  refine Eq.trans (iota_fold (eqKernel (claim.point.drop (logSteps - 4)))
    fun i ↦ iotaInner claim.weights (keccakRC.getD (12 * (i + 1) - step - 1) 0)) ?_
  rfl

/-! ## The instance weights (`keccak.rs:103-113`) -/

/-- `powers`: `[ONE; EMBED_BITS]`, then `powers[b] = powers[b - 1] * s` for `b` in `1..24`. -/
def powersRust (s : E) : List E :=
  (List.range' 1 (embedBits - 1)).foldl (fun p b ↦ p.set b (p.getD (b - 1) 0 * s))
    (List.replicate embedBits 1)

/-- `instance_weights(s)`. -/
def instanceWeightsRust (s : E) : List E :=
  let powers := powersRust s
  rmfeEmbedRust.map fun e ↦
    sumE (((List.range embedBits).filter fun b ↦ bit32 e b).map fun b ↦ powers.getD b 0)

theorem powersRust_loop (s : E) : ∀ n, n ≤ 23 →
    ((List.range' 1 n).foldl (fun p b ↦ p.set b (p.getD (b - 1) 0 * s))
      (List.replicate 24 1)).length = 24 ∧
    ∀ b < 24, ((List.range' 1 n).foldl (fun p b ↦ p.set b (p.getD (b - 1) 0 * s))
      (List.replicate 24 1)).getD b 0 = if b ≤ n then s ^ b else 1
  | 0, _ => ⟨by rw [List.range'_zero, List.foldl_nil, List.length_replicate], fun b hb ↦ by
      rw [List.range'_zero, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_replicate,
        ite_eq_left hb, Option.getD_some]
      rcases b with _ | b
      · simp
      · rw [ite_eq_right (by omega)]⟩
  | n + 1, hn => by
    obtain ⟨h1, h2⟩ := powersRust_loop s n (by omega)
    rw [List.range'_concat, show 1 + 1 * n = n + 1 by ring, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    refine ⟨by rw [List.length_set, h1], fun b hb ↦ ?_⟩
    rw [list_set_getD, h1, Nat.add_sub_cancel, h2 n (by omega), ite_eq_left (le_refl n)]
    by_cases hb1 : b = n + 1
    · subst hb1
      rw [ite_eq_left ⟨rfl, by omega⟩, ite_eq_left (le_refl _), pow_succ]
    · rw [ite_eq_right (fun h ↦ hb1 (by omega)), h2 b hb]
      by_cases hb2 : b ≤ n
      · rw [ite_eq_left hb2, ite_eq_left (by omega)]
      · rw [ite_eq_right hb2, ite_eq_right (by omega)]

theorem powersRust_getD (s : E) {b : ℕ} (hb : b < 24) : (powersRust s).getD b 0 = s ^ b := by
  rw [powersRust, show embedBits = 24 from rfl, show 24 - 1 = 23 from rfl,
    (powersRust_loop s 23 le_rfl).2 b hb, ite_eq_left (by omega)]

theorem powersFrom_getD (acc base : E) : ∀ (n b : ℕ), b < n →
    (powersFrom acc base n).getD b 0 = acc * base ^ b
  | n + 1, 0, _ => by simp [powersFrom]
  | n + 1, b + 1, h => by
    rw [powersFrom, List.getD_cons_succ, powersFrom_getD _ base n b (by omega), pow_succ]
    ring

theorem instanceWeightsRust_eq (s : E) : instanceWeightsRust s = keccakInstanceWeights s := by
  unfold instanceWeightsRust keccakInstanceWeights
  rw [← rmfeEmbedRust_eq, List.map_map]
  refine List.map_congr_left fun e _ ↦ ?_
  simp only [Function.comp_apply]
  rw [sumE_filter_map_range, sumE_filterMap_range]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  have hb' : b < 24 := Finset.mem_range.1 hb
  rw [bit32_eq, powersRust_getD s hb', powers, show embedBits = 24 from rfl,
    powersFrom_getD 1 s 24 b hb', one_mul]

/-! ## The final check's weight and the next weights (`keccak.rs:163-195`) -/

/-- `chunks(n)` of a slice. -/
def chunks (n : ℕ) (l : List E) : List (List E) :=
  (List.range ((l.length + n - 1) / n)).map fun i ↦ (l.drop (n * i)).take n

/-- Step 4's `at_local`: per lane, its weight times the slice weights' product with the lane's
position weights. -/
def atLocalRust (weights eqZ eqLane : List E) : E :=
  sumE (((chunks 64 weights).zip eqLane).map fun (le : List E × E) ↦ le.2 * dotRust eqZ le.1)

/-- Step 5's weights: `lane_weights[j / 64] * eq_z[j % 64]`. -/
def nextWeightsRust (eqZ eqLane : List E) (beta : E) : List E :=
  let laneWeights := (List.range 25).map fun lane ↦
    eqLane.getD lane 0 + beta * (eqLane.getD (keccakAlong (64 * lane) 4 / 64) 0 +
      beta * eqLane.getD (keccakAlong (64 * lane) 3 / 64) 0)
  (List.range keccakBits).map fun j ↦ laneWeights.getD (j / 64) 0 * eqZ.getD (j % 64) 0

/-- The statement's next weights. -/
def batchW (p : List E) (beta : E) : List E :=
  (List.range keccakBits).map fun j ↦ (eqKernel p).getD j 0 +
    beta * ((eqKernel p).getD (keccakAlong j 4) 0 + beta * (eqKernel p).getD (keccakAlong j 3) 0)

theorem chunks_eq (w : List E) (hw : w.length = 1600) :
    chunks 64 w = (List.range 25).map fun lane ↦ (w.drop (64 * lane)).take 64 := by
  rw [chunks, hw]

theorem chunk_length (w : List E) (hw : w.length = 1600) {lane : ℕ} (hl : lane < 25) :
    ((w.drop (64 * lane)).take 64).length = 64 := by
  simp [hw]; omega

theorem chunk_getD (w : List E) {lane z : ℕ} (hz : z < 64) :
    ((w.drop (64 * lane)).take 64).getD z 0 = w.getD (64 * lane + z) 0 := by
  simp [List.getD_eq_getElem?_getD, hz, List.getElem?_drop]

theorem eqKernel_getD_lt (pt : List E) {w : ℕ} (hw : w < 2 ^ pt.length) :
    (eqKernel pt).getD w 0 = eqAt pt w := by
  rw [eqKernel_getD, ite_eq_left hw]

theorem atLocalRust_eq (w localPt : List E) (hw : w.length = 1600) (hl : localPt.length = 11) :
    atLocalRust w (eqKernelRust (localPt.take 6)) (eqKernelRust (localPt.drop 6)) =
      dot ((eqKernel localPt).take keccakBits) w := by
  have h6 : (localPt.take 6).length = 6 := by simp [hl]
  have h5 : (localPt.drop 6).length = 5 := by simp [hl]
  rw [eqKernelRust_eq, eqKernelRust_eq, atLocalRust, chunks_eq w hw,
    zip_range_map _ _ (by rw [eqKernel_length, h5]; norm_num), List.map_map, sumE_eq_sum,
    list_sum_range, show keccakBits = w.length from hw.symm,
    dot_eqKernel localPt w (by rw [hl, hw]; norm_num), hw, show 1600 = 25 * 64 from rfl,
    sum_range_mul]
  refine Finset.sum_congr rfl fun lane hlane ↦ ?_
  have hlane' := Finset.mem_range.1 hlane
  simp only [Function.comp_apply]
  rw [dotRust_eq, dot_eq _ _ (by rw [eqKernel_length, h6, chunk_length w hw hlane']; rfl),
    eqKernel_length, h6, eqKernel_getD_lt _ (by rw [h5]; norm_num; omega), Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hz' := Finset.mem_range.1 hz
  rw [eqKernel_getD_lt _ (by rw [h6]; norm_num; omega), chunk_getD w hz', eqAt_split localPt hl,
    show (64 * lane + z) % 64 = z by omega, show (64 * lane + z) / 64 = lane by omega]
  ring

theorem keccakAlong_def (j k : ℕ) :
    keccakAlong j k = 64 * ((j / 64 % 5 + k) % 5 + 5 * (j / 64 / 5)) + j % 64 := rfl

theorem nextWeightsRust_eq (localPt : List E) (hl : localPt.length = 11) (beta : E) :
    nextWeightsRust (eqKernelRust (localPt.take 6)) (eqKernelRust (localPt.drop 6)) beta =
      batchW localPt beta := by
  have h6 : (localPt.take 6).length = 6 := by simp [hl]
  have h5 : (localPt.drop 6).length = 5 := by simp [hl]
  rw [eqKernelRust_eq, eqKernelRust_eq, nextWeightsRust, batchW]
  refine List.map_congr_left fun j hj ↦ ?_
  have hj' : j < 1600 := List.mem_range.1 hj
  have eZ : (eqKernel (localPt.take 6)).getD (j % 64) 0 = eqAt (localPt.take 6) (j % 64) :=
    eqKernel_getD_lt (localPt.take 6) (by rw [h6]; norm_num; omega)
  have eL : ∀ x < 32, (eqKernel (localPt.drop 6)).getD x 0 = eqAt (localPt.drop 6) x :=
    fun x hx ↦ eqKernel_getD_lt (localPt.drop 6) (by rw [h5]; norm_num; omega)
  have hA : ∀ k, (eqKernel localPt).getD (keccakAlong j k) 0 =
      eqAt (localPt.take 6) (j % 64) * eqAt (localPt.drop 6) (keccakAlong (64 * (j / 64)) k / 64) := by
    intro k
    rw [eqKernel_getD_lt localPt (by rw [hl, keccakAlong_def]; norm_num; omega),
      eqAt_split localPt hl, keccakAlong_def, keccakAlong_def]
    congr 2 <;> omega
  have e1 : (eqKernel localPt).getD j 0 =
      eqAt (localPt.take 6) (j % 64) * eqAt (localPt.drop 6) (j / 64) := by
    rw [eqKernel_getD_lt localPt (by rw [hl]; norm_num; omega), eqAt_split localPt hl]
  rw [getD_range_map _ _ (by omega : j / 64 < 25), hA 4, hA 3, e1, eZ, eL _ (by omega),
    eL _ (by rw [keccakAlong_def]; omega), eL _ (by rw [keccakAlong_def]; omega)]
  ring

/-! ## `linear_transpose` (`keccak.rs:83-101`) -/

/-- The first loop: `g[64 lane + z] = w[64 PI[lane] + (z + RHO[lane]) % 64]`. -/
def transposeG (w : List E) : List E :=
  (List.range 25).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
    g.set (64 * lane + z) (w.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
    (List.replicate keccakBits 0)

/-- The column sums: `columns[64 (j / 64 % 5) + j % 64] += g[j]` over `g.iter().enumerate()`. -/
def transposeColumns (g : List E) : List E :=
  g.zipIdx.foldl (fun columns (wj : E × ℕ) ↦
    columns.set (64 * (wj.2 / 64 % 5) + wj.2 % 64)
      (columns.getD (64 * (wj.2 / 64 % 5) + wj.2 % 64) 0 + wj.1)) (List.replicate (5 * 64) 0)

/-- `linear_transpose(w)`. -/
def linearTransposeRust (w : List E) : List E :=
  let g := transposeG w
  let columns := transposeColumns g
  (List.range keccakBits).map fun j ↦
    g.getD j 0 + columns.getD (64 * ((j / 64 % 5 + 1) % 5) + j % 64) 0 +
      columns.getD (64 * ((j / 64 % 5 + 4) % 5) + (j % 64 + 1) % 64) 0

/-- A θ column sum: `Σ_y v(x + 5y, z)`. -/
def colL (v : ℕ → E) (x z : ℕ) : E := ∑ y ∈ range 5, v (64 * (x + 5 * y) + z)

/-- The transpose of θ. -/
def thetaT (g : ℕ → E) (p : ℕ) : E :=
  g p + colL g ((p / 64 % 5 + 1) % 5) (p % 64) + colL g ((p / 64 % 5 + 4) % 5) ((p % 64 + 1) % 64)

/-- The weight position `p` of θ's output carries: `w` where ρ and π send `p`. -/
def gOf (w : List E) (p : ℕ) : E :=
  w.getD (64 * keccakPi (p / 64) + (p % 64 + keccakRho.getD (p / 64) 0) % 64) 0

theorem transposeG_inner (W : ℕ → E) (lane : ℕ) (g : List E) :
    ∀ Z, ((List.range Z).foldl (fun g z ↦ g.set (64 * lane + z) (W z)) g).length = g.length ∧
      ∀ p, ((List.range Z).foldl (fun g z ↦ g.set (64 * lane + z) (W z)) g).getD p 0 =
        if 64 * lane ≤ p ∧ p < 64 * lane + Z ∧ p < g.length then W (p - 64 * lane)
        else g.getD p 0
  | 0 => ⟨rfl, fun p ↦ by simp; omega⟩
  | Z + 1 => by
    obtain ⟨hs, hg⟩ := transposeG_inner W lane g Z
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [List.length_set, hs], fun p ↦ ?_⟩
    rw [list_set_getD, hg p, hs]
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

theorem transposeG_outer (w : List E) : ∀ L, L ≤ 25 →
    ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
      g.set (64 * lane + z) (w.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
      (List.replicate keccakBits 0)).length = 1600 ∧
    ∀ p, ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
      g.set (64 * lane + z) (w.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
      (List.replicate keccakBits 0)).getD p 0 = if p < 64 * L then gOf w p else 0
  | 0, _ => ⟨by rw [List.range_zero, List.foldl_nil, List.length_replicate]; rfl, fun p ↦ by
      rw [List.range_zero, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split_ifs <;> simp_all⟩
  | L + 1, hL => by
    obtain ⟨hs, hg⟩ := transposeG_outer w L (by omega)
    rw [List.range_succ (n := L), List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs', hg'⟩ := transposeG_inner
      (fun z ↦ w.getD (64 * keccakPi L + (z + keccakRho.getD L 0) % 64) 0) L
      ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.set (64 * lane + z) (w.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (List.replicate keccakBits 0)) 64
    refine ⟨hs'.trans hs, fun p ↦ ?_⟩
    rw [hg' p, hg p, hs]
    by_cases h1 : 64 * L ≤ p ∧ p < 64 * L + 64 ∧ p < 1600
    · rw [ite_eq_left h1, ite_eq_left (by omega), gOf]
      have e1 : p / 64 = L := by omega
      have e2 : p % 64 = p - 64 * L := by omega
      rw [e1, e2]
    · rw [ite_eq_right h1]
      by_cases h2 : p < 64 * L
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem transposeG_length (w : List E) : (transposeG w).length = 1600 :=
  (transposeG_outer w 25 le_rfl).1

theorem transposeG_getD (w : List E) {p : ℕ} (hp : p < 1600) : (transposeG w).getD p 0 = gOf w p := by
  rw [transposeG, (transposeG_outer w 25 le_rfl).2 p, ite_eq_left (by omega)]

theorem transposeColumns_getD (g : List E) (hg : g.length = 1600) {x z : ℕ} (hx : x < 5)
    (hz : z < 64) : (transposeColumns g).getD (64 * x + z) 0 = colL (fun p ↦ g.getD p 0) x z := by
  obtain ⟨-, h⟩ := foldl_acc 320
    (fun (wj : E × ℕ) q ↦ if 64 * (wj.2 / 64 % 5) + wj.2 % 64 = q then wj.1 else 0)
    (fun columns (wj : E × ℕ) ↦ columns.set (64 * (wj.2 / 64 % 5) + wj.2 % 64)
      (columns.getD (64 * (wj.2 / 64 % 5) + wj.2 % 64) 0 + wj.1)) g.zipIdx
    (List.replicate (5 * 64) 0) (by rw [List.length_replicate]) (fun r wj _ hr ↦ by
      obtain ⟨a, b⟩ := addAt_step r (64 * (wj.2 / 64 % 5) + wj.2 % 64) wj.1
      refine ⟨a.trans hr, fun q ↦ ?_⟩
      rw [b q]
      congr 1
      by_cases hq : 64 * (wj.2 / 64 % 5) + wj.2 % 64 = q
      · rw [ite_eq_left ⟨hq, by omega⟩, ite_eq_left hq]
      · rw [ite_eq_right (fun h ↦ hq h.1), ite_eq_right hq])
  rw [transposeColumns, h, zipIdx_eq_map g 0, List.map_map, list_sum_range,
    List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left (by omega), Option.getD_some,
    zero_add, hg]
  simp only [Function.comp_apply]
  rw [show 1600 = 25 * 64 from rfl, sum_range_mul, show 25 = 5 * 5 from rfl, sum_range_mul, colL]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  have hy' := Finset.mem_range.1 hy
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single z]
    · rw [ite_eq_left (by omega), show 64 * (5 * y + x) + z = 64 * (x + 5 * y) + z by ring]
    · intro z' hz' hne
      rw [ite_eq_right (by have := Finset.mem_range.1 hz'; omega)]
    · intro h; exact absurd (Finset.mem_range.2 hz) h
  · intro x' hx' hne
    refine Finset.sum_eq_zero fun z' hz' ↦ ?_
    rw [ite_eq_right (by have := Finset.mem_range.1 hz'; have := Finset.mem_range.1 hx'; omega)]
  · intro h; exact absurd (Finset.mem_range.2 hx) h

theorem colL_congr {v v' : ℕ → E} (h : ∀ p < 1600, v p = v' p) {x z : ℕ} (hx : x < 5)
    (hz : z < 64) : colL v x z = colL v' x z :=
  Finset.sum_congr rfl fun y hy ↦ h _ (by have := Finset.mem_range.1 hy; omega)

theorem linearTransposeRust_length (w : List E) : (linearTransposeRust w).length = 1600 := by
  simp [linearTransposeRust, keccakBits]

theorem linearTransposeRust_getD (w : List E) {p : ℕ} (hp : p < 1600) :
    (linearTransposeRust w).getD p 0 = thetaT (gOf w) p := by
  have hv : ∀ q < 1600, (transposeG w).getD q 0 = gOf w q := fun q hq ↦ transposeG_getD w hq
  rw [linearTransposeRust, getD_range_map _ _ (show p < keccakBits from hp),
    transposeColumns_getD _ (transposeG_length w) (by omega) (Nat.mod_lt _ (by omega)),
    transposeColumns_getD _ (transposeG_length w) (by omega) (Nat.mod_lt _ (by omega)),
    colL_congr hv (by omega) (Nat.mod_lt _ (by omega)),
    colL_congr hv (by omega) (Nat.mod_lt _ (by omega)), hv p hp]
  rfl

/-! ### The statement's `keccakLinearTranspose` in closed form (as `lean_vm`'s `Linear`) -/

theorem array_getD_toArray (l : List E) (i : ℕ) : l.toArray.getD i 0 = l.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem setIfInBounds_getD (a : Array E) (i p : ℕ) (x : E) :
    (a.setIfInBounds i x).getD p 0 = if i = p ∧ i < a.size then x else a.getD p 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  split_ifs <;> simp_all
  omega

theorem flatMap_getD (F : ℕ → ℕ → E) (m : ℕ) :
    ∀ (n x z : ℕ), x < n → z < m →
      ((List.range n).flatMap fun x ↦ (List.range m).map (F x)).getD (m * x + z) 0 = F x z
  | 0, _, _, hx, _ => absurd hx (Nat.not_lt_zero _)
  | n + 1, x, z, hx, hz => by
    have hlen : ((List.range n).flatMap fun x ↦ (List.range m).map (F x)).length = n * m := by
      simp [List.length_flatMap, List.sum_replicate]
    rw [List.range_succ, List.flatMap_append]
    by_cases hxn : x < n
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; nlinarith)]
      exact flatMap_getD F m n x z hxn hz
    · have : x = n := by omega
      subst this
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; nlinarith), hlen]
      simp [Nat.mul_comm, hz, List.getD_eq_getElem?_getD]

theorem flatMap_length (F : ℕ → ℕ → E) (m n : ℕ) :
    ((List.range n).flatMap fun x ↦ (List.range m).map (F x)).length = n * m := by
  simp [List.length_flatMap, List.sum_replicate]

theorem spec_inner_loop (W : ℕ → E) (lane : ℕ) (g : Array E) :
    ∀ Z, ((List.range Z).foldl (fun g z ↦ g.setIfInBounds (64 * lane + z) (W z)) g).size =
        g.size ∧
      ∀ p, ((List.range Z).foldl (fun g z ↦ g.setIfInBounds (64 * lane + z) (W z)) g).getD p 0 =
        if 64 * lane ≤ p ∧ p < 64 * lane + Z ∧ p < g.size then W (p - 64 * lane)
        else g.getD p 0
  | 0 => ⟨rfl, fun p ↦ by simp; omega⟩
  | Z + 1 => by
    obtain ⟨hs, hg⟩ := spec_inner_loop W lane g Z
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by simp [hs], fun p ↦ ?_⟩
    rw [setIfInBounds_getD, hg p, hs]
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

theorem spec_outer_loop (w : List E) :
    ∀ L, L ≤ 25 →
      ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)).size = 1600 ∧
      ∀ p, ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)).getD p 0 = if p < 64 * L then gOf w p else 0
  | 0, _ => ⟨by rw [List.range_zero, List.foldl_nil, Array.size_replicate]; rfl, fun p ↦ by
      rw [List.range_zero, List.foldl_nil, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split_ifs <;> simp_all [keccakBits]⟩
  | L + 1, hL => by
    obtain ⟨hs, hg⟩ := spec_outer_loop w L (by omega)
    rw [List.range_succ (n := L), List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs', hg'⟩ := spec_inner_loop
      (fun z ↦ w.toArray.getD (64 * keccakPi L + (z + keccakRho.getD L 0) % 64) 0) L
      ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)) 64
    refine ⟨hs'.trans hs, fun p ↦ ?_⟩
    rw [hg' p, hg p, hs]
    by_cases h1 : 64 * L ≤ p ∧ p < 64 * L + 64 ∧ p < 1600
    · rw [ite_eq_left h1, ite_eq_left (by omega), array_getD_toArray, gOf]
      have e1 : p / 64 = L := by omega
      have e2 : p % 64 = p - 64 * L := by omega
      rw [e1, e2]
    · rw [ite_eq_right h1]
      by_cases h2 : p < 64 * L
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem spec_columns_getD (A : Array E) {x z : ℕ} (hx : x < 5) (hz : z < 64) :
    ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
        sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
      (64 * x + z) 0 = colL (fun p ↦ A.getD p 0) x z := by
  rw [array_getD_toArray, flatMap_getD (fun x z ↦
    sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)) 64 5 x z hx hz]
  rw [sumE_eq_sum, list_sum_range]
  rfl

theorem spec_transposeList_getD (A : Array E) (g : ℕ → E) (hA : ∀ p < 1600, A.getD p 0 = g p)
    {p : ℕ} (hp : p < 1600) :
    ((List.range 25).flatMap fun lane ↦ (List.range 64).map fun z ↦
      A.getD (64 * lane + z) 0 +
        ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
          sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
          (64 * ((lane % 5 + 1) % 5) + z) 0 +
        ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
          sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
          (64 * ((lane % 5 + 4) % 5) + (z + 1) % 64) 0).getD p 0 = thetaT g p := by
  have hp' : p = 64 * (p / 64) + p % 64 := by omega
  conv_lhs => rw [hp']
  rw [flatMap_getD _ 64 25 (p / 64) (p % 64) (by omega) (Nat.mod_lt _ (by omega))]
  rw [spec_columns_getD _ (by omega) (Nat.mod_lt _ (by omega)),
    spec_columns_getD _ (by omega) (Nat.mod_lt _ (by omega)), ← hp', hA p hp]
  rw [colL_congr hA (by omega) (Nat.mod_lt _ (by omega)),
    colL_congr hA (by omega) (Nat.mod_lt _ (by omega))]
  rfl

theorem keccakLinearTranspose_getD (w : List E) {p : ℕ} (hp : p < 1600) :
    (keccakLinearTranspose w).getD p 0 = thetaT (gOf w) p := by
  obtain ⟨-, hg⟩ := spec_outer_loop w 25 le_rfl
  exact spec_transposeList_getD _ (gOf w) (fun q hq ↦ by rw [hg, ite_eq_left (by omega)]) hp

theorem keccakLinearTranspose_length (w : List E) : (keccakLinearTranspose w).length = 1600 := by
  unfold keccakLinearTranspose
  simp only []
  rw [flatMap_length]

theorem linearTransposeRust_eq (w : List E) : linearTransposeRust w = keccakLinearTranspose w :=
  ext_getD (by rw [linearTransposeRust_length, keccakLinearTranspose_length]) fun p hp ↦ by
    rw [linearTransposeRust_length] at hp
    rw [linearTransposeRust_getD w hp, keccakLinearTranspose_getD w hp]

/-! ## `open`'s row (`keccak.rs:208-221`) -/

/-- `row`: per segment and lane, the lane's 64 weights scaled by `segments[segment] *
slots[25 (first + segment) + lane]`, added to `row` by `row.iter_mut().zip(weights)`. -/
def openRow (segments slots weights : List E) (first count : ℕ) : List E :=
  (List.range count).foldl (fun row segment ↦
    (chunks 64 weights).zipIdx.foldl (fun row (cl : List E × ℕ) ↦
      (List.range (min 64 cl.1.length)).foldl (fun row z ↦
        row.set z (row.getD z 0 +
          segments.getD segment 0 * slots.getD (25 * (first + segment) + cl.2) 0 * cl.1.getD z 0))
        row) row) (List.replicate 64 0)

theorem openRow_getD (segments slots w : List E) (first count : ℕ) (hw : w.length = 1600) :
    (openRow segments slots w first count).length = 64 ∧ ∀ z < 64,
      (openRow segments slots w first count).getD z 0 =
        ∑ seg ∈ range count, ∑ lane ∈ range 25, segments.getD seg 0 *
          slots.getD (25 * (first + seg) + lane) 0 * w.getD (64 * lane + z) 0 := by
  have inner : ∀ (σ : E) (c r : List E), r.length = 64 →
      ((List.range (min 64 c.length)).foldl (fun row z ↦ row.set z (row.getD z 0 + σ * c.getD z 0))
        r).length = 64 ∧ ∀ q, ((List.range (min 64 c.length)).foldl
          (fun row z ↦ row.set z (row.getD z 0 + σ * c.getD z 0)) r).getD q 0 =
        r.getD q 0 + if q < min 64 c.length then σ * c.getD q 0 else 0 := by
    intro σ c r hr
    obtain ⟨h1, h2⟩ := foldl_acc 64 (fun z q ↦ if z = q then σ * c.getD z 0 else 0)
      (fun row z ↦ row.set z (row.getD z 0 + σ * c.getD z 0)) (List.range (min 64 c.length)) r hr
      (fun r' z hz hr' ↦ by
        obtain ⟨a, b⟩ := addAt_step r' z (σ * c.getD z 0)
        refine ⟨a.trans hr', fun q ↦ ?_⟩
        rw [b q]
        have hz' := List.mem_range.1 hz
        by_cases hq : z = q
        · rw [ite_eq_left ⟨hq, by omega⟩, ite_eq_left hq]
        · rw [ite_eq_right (fun h ↦ hq h.1), ite_eq_right hq])
    refine ⟨h1, fun q ↦ ?_⟩
    rw [h2, list_sum_range, Finset.sum_ite_eq']
    simp only [Finset.mem_range]
  have mid : ∀ (seg : ℕ) (r : List E), r.length = 64 →
      ((chunks 64 w).zipIdx.foldl (fun row (cl : List E × ℕ) ↦
        (List.range (min 64 cl.1.length)).foldl (fun row z ↦
          row.set z (row.getD z 0 +
            segments.getD seg 0 * slots.getD (25 * (first + seg) + cl.2) 0 * cl.1.getD z 0))
          row) r).length = 64 ∧ ∀ q < 64,
      ((chunks 64 w).zipIdx.foldl (fun row (cl : List E × ℕ) ↦
        (List.range (min 64 cl.1.length)).foldl (fun row z ↦
          row.set z (row.getD z 0 +
            segments.getD seg 0 * slots.getD (25 * (first + seg) + cl.2) 0 * cl.1.getD z 0))
          row) r).getD q 0 = r.getD q 0 + ∑ lane ∈ range 25, segments.getD seg 0 *
            slots.getD (25 * (first + seg) + lane) 0 * w.getD (64 * lane + q) 0 := by
    intro seg r hr
    obtain ⟨h1, h2⟩ := foldl_acc 64 (fun (cl : List E × ℕ) q ↦ if q < min 64 cl.1.length then
        segments.getD seg 0 * slots.getD (25 * (first + seg) + cl.2) 0 * cl.1.getD q 0 else 0)
      _ (chunks 64 w).zipIdx r hr (fun r' cl _ hr' ↦ inner _ cl.1 r' hr')
    refine ⟨h1, fun q hq ↦ ?_⟩
    rw [h2, zipIdx_eq_map _ [], List.map_map, list_sum_range]
    congr 1
    have hlen : (chunks 64 w).length = 25 := by rw [chunks_eq w hw]; simp
    rw [hlen]
    refine Finset.sum_congr rfl fun lane hlane ↦ ?_
    have hl := Finset.mem_range.1 hlane
    simp only [Function.comp_apply]
    rw [chunks_eq w hw, getD_range_map _ _ hl, chunk_length w hw hl, ite_eq_left (by omega),
      chunk_getD w hq]
  have outer : ∀ n, n ≤ count →
      ((List.range n).foldl (fun row segment ↦
        (chunks 64 w).zipIdx.foldl (fun row (cl : List E × ℕ) ↦
          (List.range (min 64 cl.1.length)).foldl (fun row z ↦
            row.set z (row.getD z 0 + segments.getD segment 0 *
              slots.getD (25 * (first + segment) + cl.2) 0 * cl.1.getD z 0)) row) row)
        (List.replicate 64 0)).length = 64 ∧ ∀ z < 64,
      ((List.range n).foldl (fun row segment ↦
        (chunks 64 w).zipIdx.foldl (fun row (cl : List E × ℕ) ↦
          (List.range (min 64 cl.1.length)).foldl (fun row z ↦
            row.set z (row.getD z 0 + segments.getD segment 0 *
              slots.getD (25 * (first + segment) + cl.2) 0 * cl.1.getD z 0)) row) row)
        (List.replicate 64 0)).getD z 0 =
        ∑ seg ∈ range n, ∑ lane ∈ range 25, segments.getD seg 0 *
          slots.getD (25 * (first + seg) + lane) 0 * w.getD (64 * lane + z) 0 := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨by simp, fun z hz ↦ ?_⟩
      rw [List.range_zero, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_replicate,
        ite_eq_left hz, Option.getD_some, Finset.sum_range_zero]
    | succ n ih =>
      intro hn
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      obtain ⟨h3, h4⟩ := mid n _ h1
      refine ⟨h3, fun z hz ↦ ?_⟩
      rw [h4 z hz, h2 z hz]
      exact (Finset.sum_range_succ _ n).symm
  exact outer count le_rfl

/-! ### The statement's slot weights in closed form (as `lean_vm`'s `SlotWeights`) -/

/-- Entry `(o, z)` of an array of rows, `0` outside. -/
def rowsF (rows : Array (Array E)) (o z : ℕ) : E := (rows.getD o #[]).getD z 0

/-- Sixty-four rows of sixty-four entries. -/
def Sized (rows : Array (Array E)) : Prop := rows.size = 64 ∧ ∀ o < 64, (rows.getD o #[]).size = 64

theorem modify_getD (rows : Array (Array E)) (i o : ℕ) (f : Array E → Array E) :
    (rows.modify i f).getD o #[] = if i = o ∧ o < rows.size then f (rows.getD o #[])
      else rows.getD o #[] := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h1 : i = o
  · subst h1
    by_cases h2 : i < rows.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem modify_step {rows : Array (Array E)} (hs : Sized rows) (i z' : ℕ) (x : E) :
    Sized (rows.modify i fun row ↦ row.setIfInBounds z' x) ∧
      ∀ o z, rowsF (rows.modify i fun row ↦ row.setIfInBounds z' x) o z =
        if i = o ∧ z' = z ∧ o < 64 ∧ z < 64 then x else rowsF rows o z := by
  refine ⟨⟨by simp [hs.1], fun o ho ↦ ?_⟩, fun o z ↦ ?_⟩
  · rw [modify_getD]
    split_ifs
    · rw [Array.size_setIfInBounds]; exact hs.2 o ho
    · exact hs.2 o ho
  · rw [rowsF, modify_getD, rowsF]
    by_cases h1 : i = o ∧ o < rows.size
    · rw [ite_eq_left h1, setIfInBounds_getD]
      have ho : o < 64 := hs.1 ▸ h1.2
      rw [hs.2 o ho]
      by_cases h2 : z' = z ∧ z' < 64
      · rw [ite_eq_left h2, ite_eq_left (show i = o ∧ z' = z ∧ o < 64 ∧ z < 64 from
          ⟨h1.1, h2.1, ho, h2.1 ▸ h2.2⟩)]
      · rw [ite_eq_right h2, ite_eq_right (show ¬ (i = o ∧ z' = z ∧ o < 64 ∧ z < 64) from
          fun h ↦ h2 ⟨h.2.1, h.2.1 ▸ h.2.2.2⟩)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ (i = o ∧ z' = z ∧ o < 64 ∧ z < 64) from
        fun h ↦ h1 ⟨h.1, hs.1 ▸ h.2.2.1⟩)]

theorem inner_rows (rows0 : Array (Array E)) (hs : Sized rows0) (b : ℕ) (V : ℕ → E)
    (hb : b + 25 ≤ 64) : ∀ J, J ≤ 1600 →
      Sized ((List.range J).foldl (fun rows j ↦ rows.modify (b + j / 64)
        fun row ↦ row.setIfInBounds (j % 64) (V j)) rows0) ∧
      ∀ o z, rowsF ((List.range J).foldl (fun rows j ↦ rows.modify (b + j / 64)
        fun row ↦ row.setIfInBounds (j % 64) (V j)) rows0) o z =
        if b ≤ o ∧ o < b + 25 ∧ z < 64 ∧ 64 * (o - b) + z < J then V (64 * (o - b) + z)
        else rowsF rows0 o z
  | 0, _ => ⟨hs, fun o z ↦ by simp⟩
  | J + 1, hJ => by
    obtain ⟨hs', hg⟩ := inner_rows rows0 hs b V hb J (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs'', hg''⟩ := modify_step hs' (b + J / 64) (J % 64) (V J)
    refine ⟨hs'', fun o z ↦ ?_⟩
    rw [hg'', hg]
    by_cases h1 : b + J / 64 = o ∧ J % 64 = z ∧ o < 64 ∧ z < 64
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
      congr 1; omega
    · rw [ite_eq_right h1]
      by_cases h2 : b ≤ o ∧ o < b + 25 ∧ z < 64 ∧ 64 * (o - b) + z < J
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- The weight `keccakSlotWeights` puts at row `o`, column `z`. -/
def slotW (segments w : List E) (first count o z : ℕ) : E :=
  if 25 * first ≤ o ∧ o < 25 * (first + count) ∧ z < 64 then
    segments.getD (o / 25 - first) 0 * w.getD (64 * (o % 25) + z) 0 else 0

theorem outer_rows (segments w : List E) (first count : ℕ) (hfc : first + count ≤ 2) :
    ∀ S, S ≤ count →
      Sized ((List.range S).foldl (fun rows segment ↦ (List.range keccakBits).foldl (fun rows j ↦
        rows.modify (25 * (first + segment) + j / 64) fun row ↦
          row.setIfInBounds (j % 64) (segments.getD segment 0 * w.toArray.getD j 0)) rows)
        (Array.replicate 64 (Array.replicate 64 0))) ∧
      ∀ o z, rowsF ((List.range S).foldl (fun rows segment ↦ (List.range keccakBits).foldl
        (fun rows j ↦ rows.modify (25 * (first + segment) + j / 64) fun row ↦
          row.setIfInBounds (j % 64) (segments.getD segment 0 * w.toArray.getD j 0)) rows)
        (Array.replicate 64 (Array.replicate 64 0))) o z = slotW segments w first S o z
  | 0, _ => by
    refine ⟨⟨by simp, fun o ho ↦ ?_⟩, fun o z ↦ ?_⟩
    · simp [Array.getD_eq_getD_getElem?, ho]
    · simp only [List.range_zero, List.foldl_nil, rowsF, slotW]
      rw [ite_eq_right (by omega)]
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      by_cases h : o < 64
      · by_cases h' : z < 64 <;> simp [h, h']
      · simp [h]
  | S + 1, hS => by
    obtain ⟨hs, hg⟩ := outer_rows segments w first count hfc S (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs', hg'⟩ := inner_rows _ hs (25 * (first + S))
      (fun j ↦ segments.getD S 0 * w.toArray.getD j 0) (by omega) keccakBits le_rfl
    refine ⟨hs', fun o z ↦ ?_⟩
    rw [hg', hg, slotW, slotW]
    by_cases h1 : 25 * (first + S) ≤ o ∧ o < 25 * (first + S) + 25 ∧ z < 64 ∧
        64 * (o - 25 * (first + S)) + z < keccakBits
    · rw [ite_eq_left h1, ite_eq_left (by omega), array_getD_toArray]
      have e1 : o / 25 - first = S := by omega
      have e2 : o % 25 = o - 25 * (first + S) := by omega
      rw [e1, e2]
    · rw [ite_eq_right h1]
      by_cases h2 : 25 * first ≤ o ∧ o < 25 * (first + S) ∧ z < 64
      · rw [ite_eq_left h2, ite_eq_left (by simp only [keccakBits] at h1 ⊢; omega)]
      · rw [ite_eq_right h2, ite_eq_right (by simp only [keccakBits] at h1 ⊢; omega)]

theorem qkeccakSlotBits_eq : qkeccakSlotBits = 6 := by decide

theorem toListRows_getD (A : Array (Array E)) {o : ℕ} (ho : o < A.size) (z : ℕ) :
    ((A.toList.map Array.toList).getD o []).getD z 0 = (A.getD o #[]).getD z 0 := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, ho]

theorem toListRows_row (A : Array (Array E)) {o : ℕ} (ho : o < A.size) :
    (A.toList.map Array.toList).getD o [] = (A.getD o #[]).toList := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, ho]

theorem slotWeights_getD (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ)
    (hfc : first + count ≤ 2) {o z : ℕ} (ho : o < 64) :
    ((keccakSlotWeights logSteps claim first count).getD o []).getD z 0 =
      slotW (eqKernel (claim.point.drop (logSteps - 4))) claim.weights first count o z := by
  obtain ⟨hs, hg⟩ := outer_rows (eqKernel (claim.point.drop (logSteps - 4))) claim.weights
    first count hfc count le_rfl
  rw [← hg o z, rowsF]
  unfold keccakSlotWeights
  simp only [qkeccakSlotBits_eq, show (2 : ℕ) ^ 6 = 64 from rfl]
  exact toListRows_getD _ (by rw [hs.1]; exact ho) z

theorem slotWeights_length (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ)
    (hfc : first + count ≤ 2) : (keccakSlotWeights logSteps claim first count).length = 64 := by
  obtain ⟨hs, -⟩ := outer_rows (eqKernel (claim.point.drop (logSteps - 4))) claim.weights
    first count hfc count le_rfl
  unfold keccakSlotWeights
  simp only [qkeccakSlotBits_eq, show (2 : ℕ) ^ 6 = 64 from rfl, List.length_map,
    Array.length_toList]
  exact hs.1

theorem slotWeights_row_length (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ)
    (hfc : first + count ≤ 2) {o : ℕ} (ho : o < 64) :
    ((keccakSlotWeights logSteps claim first count).getD o []).length = 64 := by
  obtain ⟨hs, -⟩ := outer_rows (eqKernel (claim.point.drop (logSteps - 4))) claim.weights
    first count hfc count le_rfl
  unfold keccakSlotWeights
  simp only [qkeccakSlotBits_eq, show (2 : ℕ) ^ 6 = 64 from rfl]
  rw [toListRows_row _ (by rw [hs.1]; exact ho), Array.length_toList]
  exact hs.2 o ho

/-- `keccakOpen`'s fold of the rows along the slot challenges. -/
def foldAll (slot : List E) (rows : List (List E)) : List (List E) :=
  slot.foldl (fun rows challenge ↦
    (List.range (rows.length / 2)).map fun i ↦
      List.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) [])
        (rows.getD (2 * i + 1) [])) rows

theorem zipWith_getD (f : E → E → E) (l₁ l₂ : List E) {z : ℕ} (h₁ : z < l₁.length)
    (h₂ : z < l₂.length) : (List.zipWith f l₁ l₂).getD z 0 = f (l₁.getD z 0) (l₂.getD z 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem h₁,
    List.getElem?_eq_getElem h₂]

theorem foldAll_eq : ∀ (pt : List E) (rows : List (List E)), rows.length = 2 ^ pt.length →
    (∀ o < rows.length, (rows.getD o []).length = 64) →
    (foldAll pt rows).length = 1 ∧ ((foldAll pt rows).headD []).length = 64 ∧
      ∀ z < 64, ((foldAll pt rows).headD []).getD z 0 =
        ∑ o ∈ range (2 ^ pt.length), eqAt pt o * (rows.getD o []).getD z 0
  | [], rows, hl, hr => by
    rcases rows with _ | ⟨r, _ | ⟨r', rs⟩⟩
    · simp at hl
    · refine ⟨rfl, hr 0 (by simp), fun z _ ↦ ?_⟩
      simp [foldAll, eqAt]
    · simp at hl
  | c :: pt, rows, hl, hr => by
    have step : foldAll (c :: pt) rows = foldAll pt ((List.range (rows.length / 2)).map fun i ↦
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])) := rfl
    have hl' : rows.length / 2 = 2 ^ pt.length := by
      rw [hl, List.length_cons, pow_succ]; omega
    have hrow : ∀ i < rows.length / 2, ((List.range (rows.length / 2)).map fun i ↦
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])).getD i [] =
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) []) := by
      intro i hi
      exact getD_range_map _ _ hi
    obtain ⟨h1, h2, h3⟩ := foldAll_eq pt ((List.range (rows.length / 2)).map fun i ↦
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])) (by rw [List.length_map, List.length_range, hl'])
      (fun i hi ↦ by
        have hi2 : i < rows.length / 2 := by simpa using hi
        rw [hrow i hi2, List.length_zipWith, hr _ (by omega), hr _ (by omega), min_self])
    rw [step]
    refine ⟨h1, h2, fun z hz ↦ ?_⟩
    rw [h3 z hz, List.length_cons, sum_cube_succ]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.1 hi
    rw [← hl'] at hi'
    rw [hrow i (by omega), zipWith_getD _ _ _ (by rw [hr _ (by omega)]; exact hz)
      (by rw [hr _ (by omega)]; exact hz), eqAt_cons, eqAt_cons]
    have e1 : 2 * i % 2 = 0 := by omega
    have e2 : (2 * i + 1) % 2 = 1 := by omega
    have e3 : 2 * i / 2 = i := by omega
    have e4 : (2 * i + 1) / 2 = i := by omega
    simp only [e1, e2, e3, e4, ite_true, zero_ne_one, ite_false]
    ring

/-- The slot rows the claim weighs, reindexed by segment and lane. -/
theorem slot_reindex (F : ℕ → E) (G : ℕ → ℕ → E) (first count : ℕ) (hfc : first + count ≤ 2) :
    ∑ o ∈ range 64, F o * (if 25 * first ≤ o ∧ o < 25 * (first + count) then
      G (o / 25 - first) (o % 25) else 0) =
    ∑ seg ∈ range count, ∑ lane ∈ range 25, F (25 * (first + seg) + lane) * G seg lane := by
  obtain ⟨r, hr⟩ : ∃ r, 64 = 25 * first + (count * 25 + r) := ⟨64 - 25 * first - count * 25, by omega⟩
  rw [hr, Finset.sum_range_add, Finset.sum_range_add]
  have z1 : ∑ o ∈ range (25 * first), F o * (if 25 * first ≤ o ∧ o < 25 * (first + count) then
      G (o / 25 - first) (o % 25) else 0) = 0 :=
    Finset.sum_eq_zero fun o ho ↦ by
      rw [ite_eq_right (by have := Finset.mem_range.1 ho; omega), mul_zero]
  have z2 : ∑ o ∈ range r, F (25 * first + (count * 25 + o)) *
      (if 25 * first ≤ 25 * first + (count * 25 + o) ∧
        25 * first + (count * 25 + o) < 25 * (first + count) then
      G ((25 * first + (count * 25 + o)) / 25 - first) ((25 * first + (count * 25 + o)) % 25)
      else 0) = 0 :=
    Finset.sum_eq_zero fun o _ ↦ by rw [ite_eq_right (by omega), mul_zero]
  rw [z1, z2, zero_add, add_zero, sum_range_mul count 25]
  refine Finset.sum_congr rfl fun seg hseg ↦ Finset.sum_congr rfl fun lane hlane ↦ ?_
  have hs := Finset.mem_range.1 hseg
  have hl := Finset.mem_range.1 hlane
  rw [ite_eq_left (by omega), show 25 * first + (25 * seg + lane) = 25 * (first + seg) + lane by ring,
    show (25 * (first + seg) + lane) / 25 - first = seg by omega,
    show (25 * (first + seg) + lane) % 25 = lane by omega]

theorem openRow_eq (logSteps : ℕ) (claim : KeccakClaim) (slot : List E) (hs : slot.length = 6)
    (hw : claim.weights.length = 1600) (first count : ℕ) (hfc : first + count ≤ 2) :
    openRow (eqKernel (claim.point.drop (logSteps - 4))) (eqKernel slot) claim.weights first
        count = (foldAll slot (keccakSlotWeights logSteps claim first count)).headD [] := by
  obtain ⟨hr1, hr2⟩ := openRow_getD (eqKernel (claim.point.drop (logSteps - 4))) (eqKernel slot)
    claim.weights first count hw
  obtain ⟨-, hf2, hf3⟩ := foldAll_eq slot (keccakSlotWeights logSteps claim first count)
    (by rw [slotWeights_length _ _ _ _ hfc, hs]; rfl)
    (fun o ho ↦ slotWeights_row_length _ _ _ _ hfc (by rwa [slotWeights_length _ _ _ _ hfc] at ho))
  refine ext_getD (by rw [hr1, hf2]) fun z hz ↦ ?_
  rw [hr1] at hz
  rw [hr2 z hz, hf3 z hz, hs, show (2 : ℕ) ^ 6 = 64 from rfl]
  have hslot : ∀ o < 64, eqAt slot o = (eqKernel slot).getD o 0 := fun o ho ↦
    (eqKernel_getD_lt slot (by rw [hs]; norm_num; omega)).symm
  have hR : ∑ o ∈ range 64, eqAt slot o *
      ((keccakSlotWeights logSteps claim first count).getD o []).getD z 0 =
      ∑ o ∈ range 64, (eqKernel slot).getD o 0 * (if 25 * first ≤ o ∧ o < 25 * (first + count) then
        (eqKernel (claim.point.drop (logSteps - 4))).getD (o / 25 - first) 0 *
          claim.weights.getD (64 * (o % 25) + z) 0 else 0) := by
    refine Finset.sum_congr rfl fun o ho ↦ ?_
    have ho' := Finset.mem_range.1 ho
    rw [slotWeights_getD _ _ _ _ hfc ho', slotW, hslot o ho']
    by_cases hc : 25 * first ≤ o ∧ o < 25 * (first + count)
    · rw [ite_eq_left ⟨hc.1, hc.2, hz⟩, ite_eq_left hc]
    · rw [ite_eq_right (fun h ↦ hc ⟨h.1, h.2.1⟩), ite_eq_right hc]
  rw [hR, slot_reindex (fun o ↦ (eqKernel slot).getD o 0)
      (fun seg lane ↦ (eqKernel (claim.point.drop (logSteps - 4))).getD seg 0 *
        claim.weights.getD (64 * lane + z) 0) first count hfc]
  refine Finset.sum_congr rfl fun seg _ ↦ Finset.sum_congr rfl fun lane _ ↦ ?_
  ring

/-! ## The first claim's weights (`keccak.rs:249-251`) -/

theorem eNew_shl (z : ℕ) : eNew (1#64 <<< z) = eOfNat (2 ^ z) := by
  have h : (1#64 <<< z) = BitVec.ofNat 64 (2 ^ z) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    simp
  simp only [eNew, eOfNat, K.ofBits, h]

/-! ## `verify_layer` (`keccak.rs:115-196`) -/

/-- `verify_layer(transcript, shape, step, claim)`. -/
def verifyLayerRust (shape : KeccakShape) (step : ℕ) (claim : KeccakClaim) : TM KeccakClaim := do
  let product ← TM.nextScalars productBits
  TM.require (projectedRust claim.mu product + iotaRust shape step claim * sumE claim.mu =
    claim.value)
  let s ← TM.sample
  let mu := instanceWeightsRust s
  let kappa := sumE mu
  let (value, scale, point) ← claim.point.foldlM packRound (polyEvalRust product s, 1, [])
  let (localPt, value) ← sumcheckRust value 4 (List.replicate keccakLocalBits none)
  let t ← TM.nextScalars 3
  let eqZ := eqKernelRust (localPt.take 6)
  let eqLane := eqKernelRust (localPt.drop 6)
  TM.require (scale * atLocalRust claim.weights eqZ eqLane *
    (kappa * t.getD 0 0 + (kappa + t.getD 1 0) * t.getD 2 0) = value)
  let beta ← TM.sample
  pure ⟨t.getD 0 0 + beta * (t.getD 1 0 + beta * t.getD 2 0), mu, point,
    linearTransposeRust (nextWeightsRust eqZ eqLane beta)⟩

/-- The statement's layer, its tuples as projections. -/
def layerSpec (logSteps step : ℕ) (claim : KeccakClaim) : VerifierProgram KeccakClaim :=
  VerifierProgram.readScalars productBits >>= fun product ↦
  VerifierProgram.require (projectedSpec claim.mu product + iotaSpec logSteps step claim *
    sumE claim.mu = claim.value) >>= fun _ ↦
  VerifierProgram.sampleChallenge >>= fun s ↦
  keccakPackRounds claim.point (polyEval product s) 1 >>= fun res ↦
  sumcheck res.1 4 (List.replicate keccakLocalBits none) >>= fun res2 ↦
  VerifierProgram.readScalars 3 >>= fun t ↦
  VerifierProgram.require (res.2.1 * dot ((eqKernel res2.1).take keccakBits) claim.weights *
    (sumE (keccakInstanceWeights s) * t.getD 0 0 +
      (sumE (keccakInstanceWeights s) + t.getD 1 0) * t.getD 2 0) = res2.2) >>= fun _ ↦
  VerifierProgram.sampleChallenge >>= fun beta ↦
  VerifierProgram.ret ⟨t.getD 0 0 + beta * (t.getD 1 0 + beta * t.getD 2 0),
    keccakInstanceWeights s, res.2.2, keccakLinearTranspose (batchW res2.1 beta)⟩

theorem verifyKeccakLayer_eq (logSteps step : ℕ) (claim : KeccakClaim) :
    verifyKeccakLayer logSteps step claim = layerSpec logSteps step claim := rfl

/-- **`verify_layer` runs `verifyKeccakLayer`**, at `KECCAK_DEPTH = 12`, on a claim of `1600`
position weights, and its claim has `1600` too. -/
theorem verifyLayerRust_sim (logSteps step : ℕ) (claim : KeccakClaim)
    (hw : claim.weights.length = 1600) :
    SimR (verifyLayerRust ⟨logSteps, 12⟩ step claim) (verifyKeccakLayer logSteps step claim)
      fun c ↦ c.weights.length = 1600 := by
  rw [verifyKeccakLayer_eq, layerSpec]
  unfold verifyLayerRust
  refine SimR.bind (SimR.nextScalars _) fun product _ ↦ ?_
  refine SimR.bind (SimR.require ?_) fun _ _ ↦ ?_
  · rw [projectedRust_eq, iotaRust_eq]
  refine SimR.bind SimR.sample fun s _ ↦ ?_
  dsimp only
  rw [polyEvalRust_eq]
  refine packRounds_sim claim.point _ 1 [] _ _ fun v sc p _ ↦ ?_
  dsimp only
  refine sumcheckRust_sim _ 4 _ fun localPt v' hl ↦ ?_
  have hl' : localPt.length = 11 := by simpa [keccakLocalBits] using hl
  dsimp only
  refine SimR.bind (SimR.nextScalars 3) fun t _ ↦ ?_
  refine SimR.bind (SimR.require ?_) fun _ _ ↦ ?_
  · rw [instanceWeightsRust_eq, atLocalRust_eq _ _ hw hl']
  refine SimR.bind SimR.sample fun beta _ ↦ ?_
  refine SimR.pure ?_ ?_
  · rw [instanceWeightsRust_eq, nextWeightsRust_eq _ hl', linearTransposeRust_eq, List.nil_append]
  · dsimp only
    exact linearTransposeRust_length _

/-- The layers `for step in steps`. -/
theorem layers_sim (logSteps : ℕ) {β : Type} {S : β → Prop} : ∀ (steps : List ℕ)
    (claim : KeccakClaim), claim.weights.length = 1600 → ∀ (k : KeccakClaim → TM β)
    (K : KeccakClaim → VerifierProgram β),
    (∀ c, c.weights.length = 1600 → SimR (k c) (K c) S) →
    SimR (steps.foldlM (fun claim step ↦ verifyLayerRust ⟨logSteps, 12⟩ step claim) claim >>= k)
      (keccakLayers logSteps steps claim >>= K) S
  | [], claim, hw, k, K, h => by
    simp only [List.foldlM_nil, pure_bind]
    exact h claim hw
  | step :: steps, claim, hw, k, K, h => by
    simp only [List.foldlM_cons, bind_assoc]
    rw [keccakLayers, vp_bind_assoc]
    exact SimR.bind (verifyLayerRust_sim logSteps step claim hw) fun c hc ↦
      layers_sim logSteps steps c hc k K h

/-! ## `open` (`keccak.rs:198-223`) -/

/-- `open(transcript, shape, claim, first, count, value)`. -/
def openRust (shape : KeccakShape) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    TM (List E × List E × E) := do
  let (slot, value) ← sumcheckRust value 3 (List.replicate shape.slotBits none)
  let segments := eqKernelRust (claim.point.drop shape.packBits)
  let slots := eqKernelRust slot
  pure (slot, openRow segments slots claim.weights first count, value)

theorem keccakOpen_eq (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    keccakOpen logSteps claim first count value =
      sumcheck value 3 (List.replicate qkeccakSlotBits none) >>= fun x ↦
        VerifierProgram.ret (x.1, (foldAll x.1 (keccakSlotWeights logSteps claim first
            count)).headD [], x.2) := rfl

theorem shape_packBits (l : ℕ) : (⟨l, 12⟩ : KeccakShape).packBits = l - 4 := rfl

/-- **`open` runs `keccakOpen`** on a claim of `1600` position weights and the segments it
speaks of. -/
theorem openRust_sim (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E)
    (hw : claim.weights.length = 1600) (hfc : first + count ≤ 2) :
    SimR (openRust ⟨logSteps, 12⟩ claim first count value)
      (keccakOpen logSteps claim first count value) fun _ ↦ True := by
  rw [keccakOpen_eq]
  unfold openRust
  rw [shape_slotBits, shape_packBits]
  refine sumcheckRust_sim _ 3 _ fun slot v hs ↦ ?_
  have hs' : slot.length = 6 := by simpa [qkeccakSlotBits_eq] using hs
  dsimp only
  refine SimR.pure ?_ trivial
  rw [eqKernelRust_eq, eqKernelRust_eq, openRow_eq logSteps claim slot hs' hw first count hfc]

/-! ## `verify_keccak` (`keccak.rs:225-294`) -/

/-- `KeccakOpenings`: the committed outputs at one point of `q_keccak`, if any is committed, and
the column's 64 slices at another. -/
structure KeccakOpenings where
  outputs : Option (List E × E)
  inputs : List E × List E

/-- What the caller makes of the openings (`lib.rs:334-348`): the outputs a claim on column
`QKECCAK`. -/
def KeccakOpenings.toSpec (o : KeccakOpenings) : List ColumnClaim × List E × List E :=
  (o.outputs.toList.map fun pw ↦ ⟨qkeccak, pw.1, pw.2⟩, o.inputs)

/-- The `?` of a pure step that returns a `Result`. -/
def TM.ofOption {α : Type} : Option α → TM α
  | some a => pure a
  | none => TM.fail

/-- `verify_keccak(transcript, shape, instance, output)`. -/
def verifyKeccakRust (shape : KeccakShape) (inst output : List E) : TM KeccakOpenings := do
  TM.require (inst.length = shape.logSteps ∧ output.length = 25 ∧ 4 ≤ shape.logSteps)
  let segment ← TM.samples (log2CeilRust (BitVec.ofNat 64 shape.segments))
  let point := inst.drop 4 ++ segment
  let lanePoint ← TM.samples keccakLaneBits
  let lanes := eqKernelRust lanePoint
  let weights := (List.range keccakBits).map fun j ↦ lanes.getD (j / 64) 0 * eNew (1#64 <<< (j % 64))
  let last := (eqKernelRust segment).getD (shape.segments - 1) 0 * dotRust (lanes.take 25) output
  let committed ← if 1 < shape.segments then TM.nextScalar else pure 0
  let first : KeccakClaim := ⟨committed + last, eqKernelRust (inst.take 4), point, weights⟩
  let claim ← verifyLayerRust shape 0 first
  let claim ← (List.range' 1 (shape.depth - 1)).foldlM
    (fun claim step ↦ verifyLayerRust shape step claim) claim
  let outputs ← if 1 < shape.segments then do
      let (slot, row, value) ← openRust shape first 1 (shape.segments - 1) committed
      let word ← TM.nextScalar
      TM.require (row.getD 0 0 * word = value)
      pure (some (inst ++ slot, word))
    else pure none
  let (low, value) ← sumcheckRust claim.value 3 (List.replicate 4 none)
  let (slot, row, value) ← openRust shape claim 0 shape.segments value
  let slices ← TM.nextScalars kBits
  let atLow ← TM.ofOption (multilinearEvalRust claim.mu low)
  TM.require (atLow * dotRust row slices = value)
  pure ⟨outputs, (low ++ claim.point.take shape.packBits ++ slot, slices)⟩

/-- The statement's reduction, its `do` block's join points inlined. -/
def keccakSpec (logSteps : ℕ) (inst output : List E) :
    VerifierProgram (List ColumnClaim × List E × List E) :=
  VerifierProgram.sampleChallenges keccakSegmentBits >>= fun segment ↦
  VerifierProgram.sampleChallenges keccakLaneBits >>= fun lanePoint ↦
  VerifierProgram.readScalar >>= fun committed ↦
  keccakLayers logSteps (List.range keccakDepth)
    (keccakFirstClaim inst segment lanePoint output committed) >>= fun claim ↦
  keccakOpen logSteps (keccakFirstClaim inst segment lanePoint output committed) 1
    (keccakSegments - 1) committed >>= fun x ↦
  VerifierProgram.readScalar >>= fun word ↦
  VerifierProgram.require (x.2.1.headD 0 * word = x.2.2) >>= fun _ ↦
  sumcheck claim.value 3 (List.replicate 4 none) >>= fun y ↦
  keccakOpen logSteps claim 0 keccakSegments y.2 >>= fun x' ↦
  VerifierProgram.readScalars kBits >>= fun slices ↦
  VerifierProgram.require (multilinearEval claim.mu y.1 * dot x'.2.1 slices = x'.2.2) >>= fun _ ↦
  pure ([(⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ x.1, word⟩ : ColumnClaim)],
    y.1 ++ claim.point.take (logSteps - 4) ++ x'.1, slices)

theorem verifyKeccak_eq (logSteps : ℕ) (inst output : List E) :
    verifyKeccak logSteps inst output = keccakSpec logSteps inst output := rfl

theorem SimR.ofOption_left {α β : Type} {o : Option α} {k : α → TM β} {K : VerifierProgram β}
    {S : β → Prop} (h : ∀ a, o = some a → SimR (k a) K S) : SimR (TM.ofOption o >>= k) K S := by
  cases o with
  | none =>
    intro t b t' hr
    have h' : (none : Option (β × TState)) = some (b, t') := hr
    cases h'
  | some a =>
    simp only [TM.ofOption, pure_bind]
    exact h a rfl

theorem multilinearEvalRust_some {mle point : List E} {a : E}
    (h : multilinearEvalRust mle point = some a) : a = multilinearEval mle point := by
  unfold multilinearEvalRust at h
  split_ifs at h with hc
  have e := multilinearEvalRust_eq mle point hc
  rw [multilinearEvalRust, ite_eq_left hc] at e
  rw [e] at h
  exact (Option.some.inj h).symm

/-- The Rust's first claim is the statement's. -/
theorem firstClaim_eq (inst segment lanePoint output : List E) (committed : E) :
    (⟨committed + (eqKernelRust segment).getD (2 - 1) 0 *
        dotRust ((eqKernelRust lanePoint).take 25) output,
      eqKernelRust (inst.take 4), inst.drop 4 ++ segment,
      (List.range keccakBits).map fun j ↦ (eqKernelRust lanePoint).getD (j / 64) 0 *
        eNew (1#64 <<< (j % 64))⟩ : KeccakClaim) =
      keccakFirstClaim inst segment lanePoint output committed := by
  simp only [keccakFirstClaim, eqKernelRust_eq, dotRust_eq, eNew_shl]
  rfl

theorem firstClaim_weights (inst segment lanePoint output : List E) (committed : E) :
    (keccakFirstClaim inst segment lanePoint output committed).weights.length = 1600 := by
  simp only [keccakFirstClaim, List.length_map, List.length_range]; rfl

theorem keccakSegments_eq : keccakSegments = 2 := by decide

theorem keccakSegmentBits_eq : keccakSegmentBits = 1 := by decide

theorem segmentBitsRust_eq : log2CeilRust (BitVec.ofNat 64 2) = 1 := by
  rw [log2CeilRust_eq]; decide

theorem getD_zero_eq_headD (l : List E) : l.getD 0 0 = l.headD 0 := by cases l <;> rfl

/-- **`verify_keccak` runs `verifyKeccak`** at `KECCAK_DEPTH = 12`, its openings read as the
caller reads them. -/
theorem verifyKeccakRust_sim (logSteps : ℕ) (inst output : List E) :
    Sim (KeccakOpenings.toSpec <$> verifyKeccakRust ⟨logSteps, 12⟩ inst output)
      (verifyKeccak logSteps inst output) := by
  rw [verifyKeccak_eq, map_eq_bind_pure_comp]
  refine SimR.toSim (R := fun _ ↦ True) ?_
  unfold verifyKeccakRust keccakSpec
  simp only [bind_assoc, shape_segments, shape_packBits, Nat.one_lt_two, ite_true, pure_bind,
    Function.comp_apply, segmentBitsRust_eq, firstClaim_eq]
  rw [keccakSegments_eq, keccakSegmentBits_eq,
    show List.range keccakDepth = 0 :: List.range' 1 (12 - 1) by decide]
  refine SimR.require_left fun _ ↦ ?_
  refine SimR.bind (SimR.samples _) fun segment _ ↦ ?_
  refine SimR.bind (SimR.samples _) fun lanePoint _ ↦ ?_
  refine SimR.bind SimR.nextScalar fun committed _ ↦ ?_
  rw [keccakLayers, vp_bind_assoc]
  refine SimR.bind (verifyLayerRust_sim logSteps 0 _ (firstClaim_weights _ _ _ _ _)) fun c hc ↦ ?_
  refine layers_sim logSteps (List.range' 1 (12 - 1)) c hc _ _ fun claim hcw ↦ ?_
  refine SimR.bind (openRust_sim logSteps _ 1 1 committed (firstClaim_weights _ _ _ _ _)
    (by norm_num)) fun x _ ↦ ?_
  refine SimR.bind SimR.nextScalar fun word _ ↦ ?_
  refine SimR.bind (SimR.require ?_) fun _ _ ↦ ?_
  · rw [getD_zero_eq_headD]
  refine sumcheckRust_sim _ 3 _ fun low v _ ↦ ?_
  refine SimR.bind (openRust_sim logSteps claim 0 2 v hcw (by norm_num)) fun x' _ ↦ ?_
  refine SimR.bind (SimR.nextScalars _) fun slices _ ↦ ?_
  refine SimR.ofOption_left fun atLow hat ↦ ?_
  refine SimR.bind (SimR.require ?_) fun _ _ ↦ ?_
  · rw [multilinearEvalRust_some hat, dotRust_eq]
  refine SimR.pure ?_ trivial
  simp only [KeccakOpenings.toSpec, Option.toList_some, List.map_cons, List.map_nil,
    List.take_append_drop]

theorem verifyLayerRust_sim' (logSteps step : ℕ) (claim : KeccakClaim)
    (hw : claim.weights.length = 1600) :
    Sim (verifyLayerRust ⟨logSteps, 12⟩ step claim) (verifyKeccakLayer logSteps step claim) :=
  (verifyLayerRust_sim logSteps step claim hw).toSim

theorem openRust_sim' (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E)
    (hw : claim.weights.length = 1600) (hfc : first + count ≤ 2) :
    Sim (openRust ⟨logSteps, 12⟩ claim first count value)
      (keccakOpen logSteps claim first count value) :=
  (openRust_sim logSteps claim first count value hw hfc).toSim

end Rv64Verifier.Model.Gkr
