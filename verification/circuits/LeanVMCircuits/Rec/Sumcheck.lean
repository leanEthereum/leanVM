module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel

@[expose] public section

/-!
Round-by-round soundness of sumcheck, the protocol behind most of the recursion verifier's tests bound only after
their latest challenge.

An instance's truths (`Inst`): with rounds left, the round's eq weight when factored out, the honest round
polynomial and the instance after each challenge; with none, the final value the verifier computes itself.
`Inst.ok d`: the honest polynomials have degree at most `d` and each challenge's instance sums to the honest
polynomial at it. A prover (`Prover`) answers each round with a polynomial of degree at most `d` that may depend on
the challenges so far. The verifier (`accepts`) checks each round's polynomial against the running claim (`lin`:
`g(0) + g(1)`, or `(1 - e) · g(0) + e · g(1)` with the eq weight `e` factored out), takes the polynomial at the
challenge as the next claim, and checks the last claim against the final value.

`sumcheck_sound`: if the claim is not the instance's sum, the challenge vectors of `S^n` at which the verifier
accepts are at most `n · d · |S|^(n-1)`, so at most an `n · d / |S|` fraction (`sumcheck_sound_frac`).
`sumcheck_sound_fun` is the same for a prover given by its round polynomials at each challenge vector, round `i`'s
reading only the challenges before it (`PrefixDep`), along claims that pass each round and end at the final value
(`accepts_ofFun`). `polyOf`: the polynomial of a round's coefficients, which Horner's rule evaluates (`eval_polyOf`).
`Bind.sumcheck_test_sound` applies it to the circuit's certified sumchecks.
-/

namespace LeanVMCircuits.Rec.Sumcheck

open Polynomial Finset Classical

variable {F : Type} [Field F]

/-- A round's check of its polynomial: `g(0) + g(1)`, or with the round's eq weight `e` factored out
`(1 - e) · g(0) + e · g(1)`. -/
noncomputable def lin (w : Option F) (g : F[X]) : F := match w with
  | none => g.eval 0 + g.eval 1
  | some e => (1 - e) * g.eval 0 + e * g.eval 1

/-- An instance's truths for `n` rounds; each round's eq weight, when factored out. -/
inductive Inst (F : Type) [Field F] : ℕ → Type
  | leaf (v : F) : Inst F 0
  | node {n : ℕ} (w : Option F) (H : F[X]) (next : F → Inst F n) : Inst F (n + 1)

/-- The instance's sum: the final value, or the round's check of the honest polynomial. -/
noncomputable def Inst.sum : {n : ℕ} → Inst F n → F
  | _, .leaf v => v
  | _, .node w H _ => lin w H

/-- The honest polynomials have degree at most `d`, and each challenge's instance sums to the polynomial at it. -/
def Inst.ok (d : ℕ) : {n : ℕ} → Inst F n → Prop
  | _, .leaf _ => True
  | _, .node _ H next => H.natDegree ≤ d ∧ ∀ r, (next r).sum = H.eval r ∧ (next r).ok d

/-- A prover for `n` rounds: a polynomial, then a prover after each challenge. -/
inductive Prover (F : Type) [Field F] : ℕ → Type
  | leaf : Prover F 0
  | node {n : ℕ} (g : F[X]) (next : F → Prover F n) : Prover F (n + 1)

/-- The prover's polynomials have degree at most `d`. -/
def Prover.ok (d : ℕ) : {n : ℕ} → Prover F n → Prop
  | _, .leaf => True
  | _, .node g next => g.natDegree ≤ d ∧ ∀ r, (next r).ok d

/-- The verifier accepts the claim `c` at the challenges `r`, the first challenge first. -/
def accepts : {n : ℕ} → Inst F n → Prover F n → F → (Fin n → F) → Prop
  | _, .leaf v, .leaf, c, _ => c = v
  | _, .node w _ nI, .node g nP, c, r => lin w g = c ∧ accepts (nI (r 0)) (nP (r 0)) (g.eval (r 0)) (Fin.tail r)

/-- A nonzero polynomial of degree at most `d` vanishes at at most `d` points of `S`. -/
theorem card_roots_le (S : Finset F) {p : F[X]} (hp : p ≠ 0) {d : ℕ} (hd : p.natDegree ≤ d) :
    #{a ∈ S | p.eval a = 0} ≤ d := by
  classical
  calc #{a ∈ S | p.eval a = 0} ≤ #p.roots.toFinset := by
        refine card_le_card fun a ha => ?_
        rw [mem_filter] at ha
        rw [Multiset.mem_toFinset, mem_roots hp]
        exact ha.2
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := card_roots' p
    _ ≤ d := hd

omit [Field F] in
/-- Counting over `S^(n+1)` by the first coordinate. -/
theorem card_cons (S : Finset F) (n : ℕ) (P : F → (Fin n → F) → Prop) [DecidablePred fun r : Fin (n + 1) → F =>
    P (r 0) (Fin.tail r)] [∀ a, DecidablePred (P a)] :
    #{r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) | P (r 0) (Fin.tail r)} =
      ∑ a ∈ S, #{t ∈ Fintype.piFinset (fun _ : Fin n => S) | P a t} := by
  classical
  rw [← card_sigma]
  refine card_bij' (fun r _ => ⟨r 0, Fin.tail r⟩) (fun p _ => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_
  · intro r hr
    simp only [mem_filter, Fintype.mem_piFinset] at hr
    simp only [mem_sigma, mem_filter, Fintype.mem_piFinset]
    exact ⟨hr.1 0, fun i => hr.1 i.succ, hr.2⟩
  · intro p hp
    simp only [mem_sigma, mem_filter, Fintype.mem_piFinset] at hp
    simp only [mem_filter, Fintype.mem_piFinset, Fin.cons_zero, Fin.tail_cons]
    refine ⟨fun i => ?_, hp.2.2⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hp.1
    · simpa using hp.2.1 j
  · intro r _
    simp
  · intro p _
    simp

/-- Sumcheck's round-by-round soundness: if the claim is not the instance's sum, the verifier accepts at at most
`n · d · |S|^(n-1)` challenge vectors of `S^n`. -/
theorem sumcheck_sound (S : Finset F) (d : ℕ) :
    ∀ {n : ℕ} (I : Inst F n) (P : Prover F n), I.ok d → P.ok d → ∀ c, c ≠ I.sum →
      #{r ∈ Fintype.piFinset (fun _ : Fin n => S) | accepts I P c r} ≤ n * d * #S ^ (n - 1)
  | _, .leaf v, .leaf, _, _, c, hc => by
    simp only [accepts, Inst.sum] at hc ⊢
    simp [hc]
  | n + 1, .node w H nI, .node g nP, hI, hP, c, hc => by
    classical
    obtain ⟨hH, hnext⟩ := hI
    obtain ⟨hg, hPn⟩ := hP
    simp only [Inst.sum] at hc
    -- Accepting: the first polynomial is not the honest one, and it agrees with it at the challenge or the next
    -- claim is false and the rest accepts it.
    have hsub : {r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) | accepts (.node w H nI) (.node g nP) c r} ⊆
        {r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) | (g - H).eval (r 0) = 0 ∧ True} ∪
        {r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) |
          g.eval (r 0) ≠ (nI (r 0)).sum ∧ accepts (nI (r 0)) (nP (r 0)) (g.eval (r 0)) (Fin.tail r)} := by
      intro r hr
      simp only [mem_filter, accepts] at hr
      simp only [mem_union, mem_filter, and_true, eval_sub, sub_eq_zero]
      by_cases he : g.eval (r 0) = H.eval (r 0)
      · exact Or.inl ⟨hr.1, he⟩
      · exact Or.inr ⟨hr.1, by rw [(hnext (r 0)).1]; exact he, hr.2.2⟩
    by_cases hgH : g = H
    · subst hgH
      have hemp : {r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) | accepts (.node w g nI) (.node g nP) c r} = ∅ := by
        ext r
        simp only [mem_filter, accepts, Finset.notMem_empty, iff_false, not_and]
        intro _ h
        exact fun _ => hc h.symm
      rw [hemp, card_empty]
      exact Nat.zero_le _
    have hne : g - H ≠ 0 := sub_ne_zero.mpr hgH
    have hd' : (g - H).natDegree ≤ d := (natDegree_sub_le g H).trans (max_le hg hH)
    have hT : #(Fintype.piFinset fun _ : Fin n => S) = #S ^ n := by simp [Fintype.card_piFinset]
    -- The first polynomial agrees with the honest one at the challenge: at most `d` first challenges.
    have h1 : #{r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) | (g - H).eval (r 0) = 0 ∧ True} ≤ d * #S ^ n := by
      have e := card_cons S n (fun a (_ : Fin n → F) => (g - H).eval a = 0 ∧ True)
      rw [e]
      have hs : ∀ a ∈ S, #{t ∈ Fintype.piFinset (fun _ : Fin n => S) | (g - H).eval a = 0 ∧ True} =
          if (g - H).eval a = 0 then #S ^ n else 0 := by
        intro a _
        by_cases ha : (g - H).eval a = 0
        · rw [if_pos ha, Finset.filter_true_of_mem fun _ _ => ⟨ha, trivial⟩, hT]
        · rw [if_neg ha, Finset.filter_false_of_mem fun _ _ h => ha h.1, card_empty]
      rw [sum_congr rfl hs, ← sum_filter, sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (card_roots_le S hne hd')
    -- Otherwise the next claim is false, and the rest accepts it.
    have h2 : #{r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) |
        g.eval (r 0) ≠ (nI (r 0)).sum ∧ accepts (nI (r 0)) (nP (r 0)) (g.eval (r 0)) (Fin.tail r)} ≤
        #S * (n * d * #S ^ (n - 1)) := by
      have e := card_cons S n (fun a t => g.eval a ≠ (nI a).sum ∧ accepts (nI a) (nP a) (g.eval a) t)
      rw [e]
      calc ∑ a ∈ S, #{t ∈ Fintype.piFinset (fun _ : Fin n => S) | g.eval a ≠ (nI a).sum ∧
              accepts (nI a) (nP a) (g.eval a) t}
          ≤ ∑ _a ∈ S, n * d * #S ^ (n - 1) := by
            refine sum_le_sum fun a _ => ?_
            by_cases ha : g.eval a = (nI a).sum
            · simp [ha]
            · refine (card_le_card fun t ht => ?_).trans
                (sumcheck_sound S d (nI a) (nP a) (hnext a).2 (hPn a) (g.eval a) ha)
              simp only [mem_filter] at ht ⊢
              exact ⟨ht.1, ht.2.2⟩
        _ = #S * (n * d * #S ^ (n - 1)) := by rw [sum_const, smul_eq_mul]
    have h3 : #S * (n * d * #S ^ (n - 1)) ≤ n * d * #S ^ n := by
      rcases n with _ | n
      · simp
      · rw [show n + 1 - 1 = n by omega, pow_succ]
        nlinarith [Nat.zero_le (#S), Nat.zero_le ((n + 1) * d * #S ^ n)]
    calc #{r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) | accepts (.node w H nI) (.node g nP) c r}
        ≤ #({r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) | (g - H).eval (r 0) = 0 ∧ True} ∪
          {r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) |
            g.eval (r 0) ≠ (nI (r 0)).sum ∧ accepts (nI (r 0)) (nP (r 0)) (g.eval (r 0)) (Fin.tail r)}) :=
          card_le_card hsub
      _ ≤ d * #S ^ n + #S * (n * d * #S ^ (n - 1)) := (card_union_le _ _).trans (add_le_add h1 h2)
      _ ≤ (n + 1) * d * #S ^ (n + 1 - 1) := by
        rw [show n + 1 - 1 = n by omega]
        nlinarith [h3]

/-- Sumcheck's soundness as a fraction: if the claim is not the instance's sum, the verifier accepts at at most an
`n · d / |S|` fraction of the challenge vectors of `S^n`. -/
theorem sumcheck_sound_frac (S : Finset F) (hS : S.Nonempty) (d : ℕ) {n : ℕ} (I : Inst F n) (P : Prover F n)
    (hI : I.ok d) (hP : P.ok d) (c : F) (hc : c ≠ I.sum) :
    (#{r ∈ Fintype.piFinset (fun _ : Fin n => S) | accepts I P c r} : ℚ≥0) / #S ^ n ≤ n * d / #S := by
  have h := sumcheck_sound S d I P hI hP c hc
  have hS0 : (0 : ℚ≥0) < #S := by exact_mod_cast hS.card_pos
  rw [div_le_div_iff₀ (pow_pos hS0 n) hS0]
  rcases n with _ | n
  · have : (#{r ∈ Fintype.piFinset (fun _ : Fin 0 => S) | accepts I P c r} : ℚ≥0) = 0 := by
      exact_mod_cast Nat.le_zero.mp (by simpa using h)
    rw [this]
    simp
  · have h' : (#{r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) | accepts I P c r} : ℚ≥0) ≤
        (n + 1) * d * #S ^ n := by
      have := h
      rw [show n + 1 - 1 = n by omega] at this
      exact_mod_cast this
    calc (#{r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) | accepts I P c r} : ℚ≥0) * #S
        ≤ (n + 1) * d * #S ^ n * #S := by gcongr
      _ = ((n + 1 : ℕ) : ℚ≥0) * d * #S ^ (n + 1) := by push_cast; ring

/-! A prover given by its round polynomials at each challenge vector. -/

/-- The final value along the challenges `r`. -/
def Inst.final : {n : ℕ} → Inst F n → (Fin n → F) → F
  | _, .leaf v, _ => v
  | _, .node _ _ next, r => (next (r 0)).final (Fin.tail r)

/-- Round `i`'s eq weight along the challenges `r`. -/
def Inst.weight : {n : ℕ} → Inst F n → (Fin n → F) → Fin n → Option F
  | _, .leaf _, _, i => i.elim0
  | _, .node w _ next, r, i => Fin.cases w (fun j => (next (r 0)).weight (Fin.tail r) j) i

/-- Round polynomials as a function of the challenge vector, round `i`'s reading only the challenges before it. -/
def PrefixDep {n : ℕ} (g : (Fin n → F) → Fin n → F[X]) : Prop :=
  ∀ r r' (i : Fin n), (∀ j < i, r j = r' j) → g r i = g r' i

/-- The prover answering with those polynomials. -/
noncomputable def Prover.ofFun : {n : ℕ} → ((Fin n → F) → Fin n → F[X]) → Prover F n
  | 0, _ => .leaf
  | _ + 1, g => .node (g (fun _ => 0) 0) fun a => Prover.ofFun fun t i => g (Fin.cons a t) i.succ

theorem Prover.ofFun_ok (d : ℕ) : ∀ {n : ℕ} (g : (Fin n → F) → Fin n → F[X]), (∀ r i, (g r i).natDegree ≤ d) →
    (Prover.ofFun g).ok d
  | 0, _, _ => trivial
  | _ + 1, _, h => ⟨h _ 0, fun _ => Prover.ofFun_ok d _ fun _ _ => h _ _⟩

/-- Along `r`, claims `cl` that each round's polynomial passes against, each the previous polynomial at its
challenge, ending at the final value, are an accepting run of the prover. -/
theorem accepts_ofFun : ∀ {n : ℕ} (I : Inst F n) (g : (Fin n → F) → Fin n → F[X]), PrefixDep g →
    ∀ (r : Fin n → F) (cl : Fin (n + 1) → F), (∀ i : Fin n, lin (I.weight r i) (g r i) = cl i.castSucc) →
      (∀ i : Fin n, cl i.succ = (g r i).eval (r i)) → cl (Fin.last n) = I.final r →
        accepts I (Prover.ofFun g) (cl 0) r
  | _, .leaf v, _, _, _, _, _, _, hfin => hfin
  | n + 1, .node w H nI, g, hg, r, cl, hround, hnext, hfin => by
    have hg0 : g (fun _ => 0) 0 = g r 0 := hg _ _ 0 fun j hj => absurd hj (Fin.not_lt_zero j)
    have key := accepts_ofFun (nI (r 0)) (fun t i => g (Fin.cons (r 0) t) i.succ)
      (fun t t' i h => hg _ _ i.succ fun j hj => by
        cases j using Fin.cases with
        | zero => rfl
        | succ j => simpa only [Fin.cons_succ] using h j (Fin.succ_lt_succ_iff.mp hj))
      (Fin.tail r) (fun k => cl k.succ)
      (fun i => by
        rw [Fin.cons_self_tail]
        simpa only [Inst.weight, Fin.cases_succ, Fin.succ_castSucc] using hround i.succ)
      (fun i => by rw [Fin.cons_self_tail]; exact hnext i.succ)
      (by simpa only [Fin.succ_last, Inst.final] using hfin)
    refine ⟨?_, ?_⟩
    · rw [hg0]
      simpa only [Inst.weight, Fin.cases_zero, Fin.castSucc_zero] using hround 0
    · rw [hg0, ← hnext 0]
      exact key

/-- `sumcheck_sound` for a prover given by its round polynomials at each challenge vector: if the claim is not the
instance's sum, the challenge vectors of `S^n` along which claims starting at it pass each round, are each the
previous polynomial at its challenge, and end at the final value are at most `n · d · |S|^(n-1)`. -/
theorem sumcheck_sound_fun (S : Finset F) (d : ℕ) {n : ℕ} (I : Inst F n) (hI : I.ok d)
    (g : (Fin n → F) → Fin n → F[X]) (hg : PrefixDep g) (hd : ∀ r i, (g r i).natDegree ≤ d)
    (cl : (Fin n → F) → Fin (n + 1) → F) (c : F) (hc : c ≠ I.sum) :
    #{r ∈ Fintype.piFinset (fun _ : Fin n => S) | cl r 0 = c ∧ (∀ i, lin (I.weight r i) (g r i) = cl r i.castSucc) ∧
      (∀ i, cl r i.succ = (g r i).eval (r i)) ∧ cl r (Fin.last n) = I.final r} ≤ n * d * #S ^ (n - 1) := by
  refine le_trans (card_le_card fun r hr => ?_) (sumcheck_sound S d I (Prover.ofFun g) hI (Prover.ofFun_ok d g hd) c hc)
  simp only [mem_filter] at hr ⊢
  obtain ⟨hS, h0, h1, h2, h3⟩ := hr
  exact ⟨hS, h0 ▸ accepts_ofFun I g hg r (cl r) h1 h2 h3⟩

/-- Round polynomials reading only the challenges before them among the challenge vectors of `A`. -/
def PrefixDepOn {n : ℕ} (A : Set (Fin n → F)) (g : (Fin n → F) → Fin n → F[X]) : Prop :=
  ∀ r ∈ A, ∀ r' ∈ A, ∀ i : Fin n, (∀ j < i, r j = r' j) → g r i = g r' i

open Classical in
/-- `sumcheck_sound_fun` counting only the challenge vectors of `A`, the round polynomials reading only the challenges
before them among those: on a prefix some vector of `A` has, the prover answers with that vector's polynomial. -/
theorem sumcheck_sound_on (S : Finset F) (d : ℕ) {n : ℕ} (I : Inst F n) (hI : I.ok d) (A : Set (Fin n → F))
    (g : (Fin n → F) → Fin n → F[X]) (hg : PrefixDepOn A g) (hd : ∀ r i, (g r i).natDegree ≤ d)
    (cl : (Fin n → F) → Fin (n + 1) → F) (c : F) (hc : c ≠ I.sum) :
    #{r ∈ Fintype.piFinset (fun _ : Fin n => S) | r ∈ A ∧ cl r 0 = c ∧
      (∀ i, lin (I.weight r i) (g r i) = cl r i.castSucc) ∧ (∀ i, cl r i.succ = (g r i).eval (r i)) ∧
        cl r (Fin.last n) = I.final r} ≤ n * d * #S ^ (n - 1) := by
  let pre : (Fin n → F) → Fin n → (Fin n → F) → Prop := fun r i x => x ∈ A ∧ ∀ j < i, x j = r j
  let G : Fin n → ((Fin n → F) → Prop) → F[X] := fun i P => if h : ∃ x, P x then g (Classical.choose h) i else 0
  let g' : (Fin n → F) → Fin n → F[X] := fun r i => G i (pre r i)
  have hpre : PrefixDep g' := fun r r' i h => by
    have e : pre r i = pre r' i := by
      funext x
      apply propext
      constructor
      · rintro ⟨hx, hj⟩
        exact ⟨hx, fun j hji => (hj j hji).trans (h j hji)⟩
      · rintro ⟨hx, hj⟩
        exact ⟨hx, fun j hji => (hj j hji).trans (h j hji).symm⟩
    show G i (pre r i) = G i (pre r' i)
    rw [e]
  have hagree : ∀ r ∈ A, ∀ i, g' r i = g r i := fun r hr i => by
    have hex : ∃ x, pre r i x := ⟨r, hr, fun _ _ => rfl⟩
    show G i (pre r i) = g r i
    simp only [G, dif_pos hex]
    exact hg _ (Classical.choose_spec hex).1 r hr i (Classical.choose_spec hex).2
  have hd' : ∀ r i, (g' r i).natDegree ≤ d := fun r i => by
    show (G i (pre r i)).natDegree ≤ d
    simp only [G]
    split
    · exact hd _ _
    · simp
  refine le_trans (card_le_card fun r hr => ?_) (sumcheck_sound_fun S d I hI g' hpre hd' cl c hc)
  simp only [mem_filter] at hr ⊢
  obtain ⟨hS, hA, h0, h1, h2, h3⟩ := hr
  exact ⟨hS, h0, fun i => (hagree r hA i).symm ▸ h1 i, fun i => (hagree r hA i).symm ▸ h2 i, h3⟩

/-! A round polynomial of its coefficients. -/

/-- The polynomial of coefficients, constant first. -/
noncomputable def polyOf (cs : List F) : F[X] := cs.foldr (fun c p => p * X + C c) 0

/-- At `x` it is Horner's rule over the coefficients, the last first. -/
theorem eval_polyOf (cs : List F) (x : F) : (polyOf cs).eval x = cs.foldr (fun c a => a * x + c) 0 := by
  induction cs with
  | nil => simp [polyOf]
  | cons c cs ih =>
    simp only [polyOf, List.foldr_cons] at ih ⊢
    rw [eval_add, eval_mul, eval_X, eval_C, ih]

theorem eval_polyOf_zero (cs : List F) : (polyOf cs).eval 0 = cs.head?.getD 0 := by
  cases cs with
  | nil => simp [polyOf]
  | cons c cs => simp [polyOf]

theorem eval_polyOf_one (cs : List F) : (polyOf cs).eval 1 = cs.sum := by
  induction cs with
  | nil => simp [polyOf]
  | cons c cs ih =>
    simp only [polyOf, List.foldr_cons] at ih ⊢
    rw [eval_add, eval_mul, eval_X, eval_C, ih, mul_one, List.sum_cons, add_comm]

theorem natDegree_polyOf : ∀ cs : List F, (polyOf cs).natDegree ≤ cs.length - 1
  | [] => by simp [polyOf]
  | [c] => by simp [polyOf]
  | c :: c' :: cs => by
    have ih := natDegree_polyOf (c' :: cs)
    have he : polyOf (c :: c' :: cs) = polyOf (c' :: cs) * X + C c := rfl
    rw [he]
    refine (natDegree_add_le _ _).trans (max_le (natDegree_mul_le.trans ?_) (by simp))
    have hX := natDegree_X_le (R := F)
    simp only [List.length_cons] at ih ⊢
    omega

theorem coeff_polyOf : ∀ (cs : List F) (k : ℕ), (polyOf cs).coeff k = cs.getD k 0
  | [], k => by simp [polyOf]
  | c :: cs, 0 => by
    have he : polyOf (c :: cs) = polyOf cs * X + C c := rfl
    rw [he, coeff_add, coeff_mul_X_zero, coeff_C_zero, zero_add]
    rfl
  | c :: cs, k + 1 => by
    have he : polyOf (c :: cs) = polyOf cs * X + C c := rfl
    rw [he, coeff_add, coeff_mul_X, coeff_C_succ, add_zero, coeff_polyOf cs k]
    rfl

theorem polyOf_map_sub {α : Type} (f g : α → F) : ∀ l : List α,
    polyOf (l.map fun x => f x - g x) = polyOf (l.map f) - polyOf (l.map g)
  | [] => by simp [polyOf]
  | x :: l => by
    have e1 : polyOf ((x :: l).map fun x => f x - g x) = polyOf (l.map fun x => f x - g x) * X + C (f x - g x) := rfl
    have e2 : polyOf ((x :: l).map f) = polyOf (l.map f) * X + C (f x) := rfl
    have e3 : polyOf ((x :: l).map g) = polyOf (l.map g) * X + C (g x) := rfl
    rw [e1, e2, e3, polyOf_map_sub f g l, C_sub]
    ring

end LeanVMCircuits.Rec.Sumcheck
