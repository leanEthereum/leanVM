/-
  LeanVM.Guest.B1.Basic

  The shared vocabulary of the B1 lemmas: a function's relation unfolded to its body, the
  compile-time words of the guest's data, memory runs, runs of the specification's programs on
  the Fiat-Shamir chain, valuations built block by block, and `mul_range` loops.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.CoreLemmas
public import LeanVM.Guest.Value.All

/-!
# B1: shared vocabulary

* `rel_iff_sem`, `relN_succ_iff`: a function's relation is its body's (`Program.Rel` is a fixed
  point, `rel_iff`), and at a finite depth its calls are one level shallower.
* `word_*`: the constants the data writes as `word c0 c1 c2`, as the Spec's words (`y`, `y²`,
  `y⁻¹`, `E(n)`, `g^a`, the IV cells, the metadata cell of one final block).
* `ReadsAt rd p xs`: the words `xs` lie in memory from the pointer `p`, word `k` at `p·g^k`;
  `loadHolds_mul_gen_pow`: a load through `p·g^j` at offset `k` is the load at offset `j + k`.
* `RunsTo p cv xs a cv'`: the specification's program `p` (`Compile.Prog`) runs from the chain
  state `cv`, reading exactly the stream words `xs`, to the value `a` and the state `cv'`
  (`Compile.run` on the deployed hash, on any stream continuing `xs`, any openings and roots).
  `RunsTo.bind`, `runsTo_readE`, `runsTo_sampleE`, `runsTo_readN`, `runsTo_sampleN` compose runs;
  `RunsTo.unique` makes them functions of the state and the words read.
* `setv σ b n f`: `σ` with the values `.n (b + k)`, `k < n`, set to `f k`: how an honest
  valuation is built, block after block (`set_n_in`, `set_n_lt`, `set_n_ge` evaluate it).
* `loop_iff`: a `mul_range` loop helper, from `g^k` to its end `N`, holds exactly when `N = g^m`
  for the first `m > k` the loop reaches and its body holds at every `g^j`, `k ≤ j < m`;
  `loop_iff_ord` restates it below the order of `g`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Unfolding a function -/

/-- A function's relation is its body's, once it is found by name. -/
theorem rel_iff_sem {P : Core.Program} {rd : Reader} {f : String} {fn : Fn}
    (h : P.find? f = some fn) (args rets : List E) :
    P.Rel rd f args rets ↔
      ∃ σ : Val, fn.params.map σ = args ∧
        Stmt.HoldsList (P.Rel rd) rd σ fn.body False (fun rs => rs = rets) := by
  rw [rel_iff]
  simp only [h, Option.some.injEq, exists_eq_left', Fn.Sem]

/-- The same at a finite depth: the body's calls one level shallower. -/
theorem relN_succ_iff {P : Core.Program} {rd : Reader} {f : String} {fn : Fn}
    (h : P.find? f = some fn) (n : ℕ) (args rets : List E) :
    P.relN rd (n + 1) f args rets ↔
      ∃ σ : Val, fn.params.map σ = args ∧
        Stmt.HoldsList (P.relN rd n) rd σ fn.body False (fun rs => rs = rets) := by
  simp only [Program.relN, h, Option.some.injEq, exists_eq_left', Fn.Sem]

/-! ## Compile-time words -/

theorem word_eOfNat (n : ℕ) : word n 0 0 = eOfNat n := by
  rw [word, eOfNat_eq_ofLimbs]
  rfl

theorem word_zero : word 0 0 0 = 0 := by rw [word_eOfNat, eOfNat_zero]

theorem word_one : word 1 0 0 = 1 := by rw [word_eOfNat, eOfNat_one]

theorem word_gen : word 2 0 0 = gen := by rw [word_eOfNat]; rfl

/-- `E(2^a)` is `g^a` below the first reduction. -/
theorem word_two_pow {a : ℕ} (h : a < 64) : word (2 ^ a) 0 0 = gen ^ a := by
  rw [word_eOfNat, gen_pow_eq_eOfNat h]

theorem word_y : word 0 1 0 = y := by rw [y_eq]; rfl

theorem word_yy : word 0 0 1 = y * y := by
  rw [y_eq, mul_limbs]
  simp only [word, ofLimbs_inj]
  refine ⟨?_, ?_, ?_⟩ <;> ring_nf <;> rfl

theorem word_y_inv : word 1 0 1 = y⁻¹ := by rw [y_inv]; rfl

/-- `y · E(t)`, the data's `word 0 t 0`. -/
theorem word_y_mul (t : ℕ) : word 0 t 0 = y * eOfNat t := by
  rw [eOfNat_eq_ofLimbs, y_eq, mul_limbs]
  simp only [word, ofLimbs_inj]
  refine ⟨?_, ?_, ?_⟩ <;> ring_nf <;> rfl

theorem word_iv0 : word 13503953895743350343 11912009169889063794 0 = Value.ivCells.1 := by
  rw [ivCells_eq]; rfl

theorem word_iv1 : word 11170449402626986623 6620516960021240235 0 = Value.ivCells.2 := by
  rw [ivCells_eq]; rfl

/-- The metadata of one final 64-byte block. -/
theorem word_md64 : word 64 4294967295 0 = metadataCell 64 true := rfl

/-! ## Words in `K` -/

theorem isInK_add {a b : E} (ha : IsInK a) (hb : IsInK b) : IsInK (a + b) := by
  obtain ⟨a, rfl⟩ := (isInK_iff _).mp ha
  obtain ⟨b, rfl⟩ := (isInK_iff _).mp hb
  rw [← ofK_add]; exact ofK_isInK _

theorem isInK_mul {a b : E} (ha : IsInK a) (hb : IsInK b) : IsInK (a * b) := by
  obtain ⟨a, rfl⟩ := (isInK_iff _).mp ha
  obtain ⟨b, rfl⟩ := (isInK_iff _).mp hb
  rw [← ofK_mul]; exact ofK_isInK _

theorem gen_pow_isInK (j : ℕ) : IsInK (gen ^ j) := by
  rw [gen_pow_eq_ofK]; exact ofK_isInK _

theorem isInK_mul_ofK {p : E} {c : K} (hc : c ≠ 0) : IsInK (p * ofK c) ↔ IsInK p := by
  rw [eq_ofLimbs p, ofLimbs_mul_ofK, isInK_ofLimbs_iff, isInK_ofLimbs_iff]
  simp [hc]

theorem limb0_mul_ofK {p : E} (hp : IsInK p) (c : K) : (p * ofK c).limb 0 = p.limb 0 * c := by
  rw [eq_ofLimbs p, ofLimbs_mul_ofK, hp.1, hp.2]
  rfl

/-! ## Memory runs -/

/-- The words `xs` lie in memory from `p`: word `k` at `p·g^k`. -/
def ReadsAt (rd : Reader) (p : E) (xs : List E) : Prop :=
  ∀ k (hk : k < xs.length), LoadHolds rd p k xs[k]

theorem readsAt_nil (rd : Reader) (p : E) : ReadsAt rd p [] := fun _ hk => absurd hk (by simp)

/-- A load through `p·g^j` at offset `k` is the load at offset `j + k`. -/
theorem loadHolds_mul_gen_pow (rd : Reader) (p : E) (j k : ℕ) (w : E) :
    LoadHolds rd (p * gen ^ j) k w ↔ LoadHolds rd p (j + k) w := by
  have hg : Parameters.gpow j ≠ 0 := pow_ne_zero _ g_ne_zero
  rw [gen_pow_eq_ofK]
  unfold LoadHolds
  rw [isInK_mul_ofK hg]
  constructor
  · rintro ⟨hp, h⟩
    rw [limb0_mul_ofK hp, mul_assoc, Parameters.gpow, Parameters.gpow, ← pow_add] at h
    exact ⟨hp, h⟩
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    rw [limb0_mul_ofK hp, mul_assoc, Parameters.gpow, Parameters.gpow, ← pow_add]
    exact h

/-! ## Runs of the specification's programs -/

/-- `Compile.run` over the deployed hash. -/
abbrev runId {α : Type} (p : Prog α) (s : St) : Option (α × St) :=
  Compile.run (m := Id) blake2sBytes p s

theorem prog_bind_eq {α β : Type} (p : Prog α) (f : α → Prog β) : p >>= f = p.bind f := rfl

theorem prog_pure_eq {α : Type} (a : α) : (pure a : Prog α) = Prog.ret a := rfl

theorem run_bind {α β : Type} (p : Prog α) (f : α → Prog β) (s : St) :
    runId (p.bind f) s = (runId p s).bind (fun r => runId (f r.1) r.2) := by
  induction p generalizing s with
  | ret a => rfl
  | fail => rfl
  | read k ih =>
    simp only [runId, Prog.bind, Compile.run]
    split
    · rfl
    · exact ih _ _
  | sample k ih => exact ih _ _
  | grind b k ih =>
    simp only [runId, Prog.bind, Compile.run]
    split
    · rfl
    · simp only [bind, pure]
      split
      · exact ih _
      · rfl
  | commit h w k ih =>
    simp only [runId, Prog.bind, Compile.run]
    split
    · simp only [bind]
      split
      · exact ih _
      · rfl
    · rfl
  | query i ps k ih =>
    simp only [runId, Prog.bind, Compile.run]
    split
    · rfl
    · simp only [bind]
      split
      · exact ih _ _
      · rfl

/-- The chain after absorbing a stream word (`.read`, `Node.observe`). -/
def obsCv (cv : Digest) (x : E) : Digest := blake2sBytes (digestBytes cv ++ blockOf x 1)

/-- The chain after a squeeze (`.sample`, `Node.squeeze`). -/
def sqCv (cv : Digest) : Digest := blake2sBytes (digestBytes cv ++ blockOf 0 2)

/-- The program `p` runs from the chain state `cv`, reading exactly `xs`, to `a` and `cv'`, on
any stream continuing `xs`, any openings and any roots. -/
def RunsTo {α : Type} (p : Prog α) (cv : Digest) (xs : List E) (a : α) (cv' : Digest) : Prop :=
  ∀ (rest : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)),
    runId p ⟨cv, xs ++ rest, os, roots⟩ = some (a, ⟨cv', rest, os, roots⟩)

theorem RunsTo.of_eq {α : Type} {p : Prog α} {cv : Digest} {xs xs' : List E} {a a' : α}
    {c c' : Digest} (h : RunsTo p cv xs a c) (hx : xs = xs') (ha : a = a') (hc : c = c') :
    RunsTo p cv xs' a' c' := by
  subst hx ha hc; exact h

theorem RunsTo.unique {α : Type} {p : Prog α} {cv : Digest} {xs : List E} {a b : α}
    {c1 c2 : Digest} (h1 : RunsTo p cv xs a c1) (h2 : RunsTo p cv xs b c2) : a = b ∧ c1 = c2 := by
  have := (h1 [] [] []).symm.trans (h2 [] [] [])
  simp only [Option.some.injEq, Prod.mk.injEq, St.mk.injEq] at this
  exact ⟨this.1, this.2.1⟩

/-- A run determines its value and final state. -/
theorem RunsTo.iff {α : Type} {p : Prog α} {cv : Digest} {xs : List E} {a b : α}
    {c1 c2 : Digest} (h1 : RunsTo p cv xs a c1) : RunsTo p cv xs b c2 ↔ b = a ∧ c2 = c1 := by
  constructor
  · intro h2
    obtain ⟨h, h'⟩ := h1.unique h2
    exact ⟨h.symm, h'.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact h1

theorem runsTo_ret {α : Type} (a : α) (cv : Digest) : RunsTo (pure a : Prog α) cv [] a cv :=
  fun _ _ _ => rfl

theorem RunsTo.bind {α β : Type} {p : Prog α} {f : α → Prog β} {cv cv1 cv2 : Digest}
    {xs ys : List E} {a : α} {b : β} (h1 : RunsTo p cv xs a cv1) (h2 : RunsTo (f a) cv1 ys b cv2) :
    RunsTo (p >>= f) cv (xs ++ ys) b cv2 := by
  intro rest os roots
  rw [prog_bind_eq, run_bind, List.append_assoc, h1]
  exact h2 rest os roots

theorem runsTo_readE (cv : Digest) (x : E) : RunsTo Prog.readE cv [x] x (obsCv cv x) :=
  fun _ _ _ => rfl

theorem runsTo_sampleE (cv : Digest) :
    RunsTo Prog.sampleE cv [] (challengeOf (sqCv cv)) (sqCv cv) := fun _ _ _ => rfl

/-- The chain after absorbing the words `xs` in order. -/
def obsAll (cv : Digest) (xs : List E) : Digest := xs.foldl obsCv cv

theorem runsTo_readN (cv : Digest) (xs : List E) :
    RunsTo (Prog.readN xs.length) cv xs xs (obsAll cv xs) := by
  induction xs generalizing cv with
  | nil => exact runsTo_ret _ _
  | cons x xs ih =>
    have h := (runsTo_readE cv x).bind (f := fun x => do let xs ← Prog.readN xs.length; return x :: xs)
      ((ih (obsCv cv x)).bind (f := fun xs => (pure (x :: xs) : Prog (List E)))
        (runsTo_ret (x :: xs) _))
    simpa [Prog.readN, obsAll, List.foldl] using h

/-- `n` squeezes from `cv`: the challenges and the final state. -/
def sqAll : ℕ → Digest → List E × Digest
  | 0, cv => ([], cv)
  | n + 1, cv => (challengeOf (sqCv cv) :: (sqAll n (sqCv cv)).1, (sqAll n (sqCv cv)).2)

theorem runsTo_sampleN (n : ℕ) (cv : Digest) :
    RunsTo (Prog.sampleN n) cv [] (sqAll n cv).1 (sqAll n cv).2 := by
  induction n generalizing cv with
  | zero => exact runsTo_ret _ _
  | succ n ih =>
    have h := (runsTo_sampleE cv).bind (f := fun x => do let xs ← Prog.sampleN n; return x :: xs)
      ((ih (sqCv cv)).bind (f := fun xs => (pure (challengeOf (sqCv cv) :: xs) : Prog (List E)))
        (runsTo_ret _ _))
    simpa [Prog.sampleN, sqAll] using h

/-! ## Building valuations -/

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_neg' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

/-- `σ` with the values `.n (b + k)`, `k < n`, set to `f k`. -/
def setv (σ : Val) (b n : ℕ) (f : ℕ → E) : Val := fun v =>
  if v.path = [] ∧ v.tag = 0 ∧ b ≤ v.idx ∧ v.idx < b + n then f (v.idx - b) else σ v

theorem set_n_in {σ : Val} {b n k : ℕ} {f : ℕ → E} (h1 : b ≤ k) (h2 : k < b + n) :
    setv σ b n f (.n k) = f (k - b) := by
  unfold setv
  split
  · rfl
  · rename_i h
    exact absurd ⟨rfl, rfl, h1, h2⟩ h

theorem set_n_lt {σ : Val} {b n k : ℕ} {f : ℕ → E} (h : k < b) : setv σ b n f (.n k) = σ (.n k) := by
  unfold setv
  split
  · rename_i h'
    exact absurd h'.2.2.1 (by simp only; omega)
  · rfl

theorem set_n_ge {σ : Val} {b n k : ℕ} {f : ℕ → E} (h : b + n ≤ k) :
    setv σ b n f (.n k) = σ (.n k) := by
  unfold setv
  split
  · rename_i h'
    exact absurd h'.2.2.2 (by simp only; omega)
  · rfl

/-- The valuation of a function's arguments, `.n k ↦ args[k]`. -/
def Val.ofArgs (args : List E) : Val := fun v => args.getD v.idx 0

/-- `σ` with the values from `.n b` on set to the words `l`. -/
abbrev setl (σ : Val) (b : ℕ) (l : List E) : Val := setv σ b l.length (fun k => l.getD k 0)

theorem ofArgs_n (args : List E) (k : ℕ) : Val.ofArgs args (.n k) = args.getD k 0 := rfl

/-- Evaluate a lookup in a valuation built by `setv`/`setl` on `Val.ofArgs`, the side conditions
by `omega` from the context. -/
macro "b1_look" : tactic =>
  `(tactic| simp (disch := omega) only [setl, set_n_lt, set_n_ge, set_n_in, Nat.add_sub_cancel_left,
    ofArgs_n, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, Nat.add_zero, Nat.sub_self, Nat.zero_add])

/-! ## `mul_range` loops -/

/-- The order of `g`. -/
abbrev ordG : ℕ := 2 ^ 64 - 1

theorem gen_pow_mul_gen (j : ℕ) : gen ^ j * gen = gen ^ (j + 1) := (pow_succ gen j).symm

theorem gen_pow_add_eq_zero_iff {N : E} (j : ℕ) : gen ^ j * gen + N = 0 ↔ N = gen ^ (j + 1) := by
  rw [gen_pow_mul_gen, e_add_eq_zero_iff, eq_comm]

/-- **A `mul_range` loop** (`for x in mul_range(g^k, N)`, lowered to a helper `f` that runs its
body at `x`, then calls itself at `x·g` while `x·g ≠ N`): if `f`'s relation at depth `d + 1` is
its body's meaning `B x` and the conditional call, then `f` holds at `g^k` exactly when the loop
ends: `N = g^m` for the first `m > k` it reaches, and `B` holds at every `g^j`, `k ≤ j < m`. -/
theorem loop_iff {P : Core.Program} {rd : Reader} {f : String} {ps : List E} {N : E}
    {B : E → Prop}
    (hstep : ∀ d x, P.relN rd (d + 1) f (x :: ps) [] ↔
      B x ∧ IsInK (x * gen + N) ∧ (x * gen + N ≠ 0 → P.relN rd d f (x * gen :: ps) []))
    (k : ℕ) :
    P.Rel rd f (gen ^ k :: ps) [] ↔
      ∃ m, k < m ∧ N = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ N) ∧
        ∀ j, k ≤ j → j < m → B (gen ^ j) := by
  constructor
  · rintro ⟨d, hd⟩
    induction d generalizing k with
    | zero => exact hd.elim
    | succ d ih =>
      obtain ⟨hB, -, hnext⟩ := (hstep d _).mp hd
      by_cases h0 : gen ^ k * gen + N = 0
      · refine ⟨k + 1, by omega, (gen_pow_add_eq_zero_iff k).mp h0, fun j h1 h2 => by omega,
          fun j h1 h2 => ?_⟩
        rwa [show j = k by omega]
      · have := hnext h0
        rw [gen_pow_mul_gen] at this
        obtain ⟨m, hm, hN, hfirst, hall⟩ := ih (k + 1) this
        refine ⟨m, by omega, hN, fun j h1 h2 => ?_, fun j h1 h2 => ?_⟩
        · rcases Nat.lt_or_ge (k + 1) j with h | h
          · exact hfirst j h h2
          · rw [show j = k + 1 by omega]
            intro he
            exact h0 ((gen_pow_add_eq_zero_iff k).mpr he.symm)
        · rcases Nat.lt_or_ge k j with h | h
          · exact hall j (by omega) h2
          · rwa [show j = k by omega]
  · rintro ⟨m, hkm, hN, hfirst, hall⟩
    obtain ⟨t, rfl⟩ : ∃ t, m = k + 1 + t := ⟨m - k - 1, by omega⟩
    have hK : ∀ j, IsInK (gen ^ j * gen + N) := fun j => by
      rw [hN]; exact isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _)
    refine ⟨t + 1, ?_⟩
    induction t generalizing k with
    | zero =>
      exact (hstep 0 _).mpr ⟨hall k le_rfl (by omega), hK k,
        fun h => absurd ((gen_pow_add_eq_zero_iff k).mpr hN) h⟩
    | succ t ih =>
      refine (hstep (t + 1) _).mpr ⟨hall k le_rfl (by omega), hK k, fun _ => ?_⟩
      rw [gen_pow_mul_gen]
      exact ih (k + 1) (by omega) (by rw [hN]; congr 1; omega)
        (fun j h1 h2 => hfirst j (by omega) (by omega)) (fun j h1 h2 => hall j (by omega) (by omega))

/-- Below the order of `g`, the first `m > k` the loop reaches is the `m` with `N = g^m`. -/
theorem first_hit_of_lt {N : E} {k m : ℕ} (hm : m < ordG) (hN : N = gen ^ m) :
    ∀ j, k < j → j < m → gen ^ j ≠ N := fun j _ hj h => by
  have hm' : m < 2 ^ 64 - 1 := hm
  rw [hN] at h
  have := gen_pow_inj (by omega) hm h
  omega

/-! ## Comparing statement lists by kernel evaluation

`stmtsEqb` is a structural Boolean equality on statements, comparing words limb by limb (the
kernel reduces `E.limb` on literal words, not `DecidableEq E`). `stmtsEqb_sound`: a template
equal to a function's body by `decide +kernel` on `stmtsEqb`, where `rfl` would unfold both
sides in the elaborator. -/

/-- Words compared limb by limb. -/
def eEqb (a b : E) : Bool :=
  decide (a.limb 0 = b.limb 0) && decide (a.limb 1 = b.limb 1) && decide (a.limb 2 = b.limb 2)

theorem eEqb_sound {a b : E} (h : eEqb a b = true) : a = b := by
  simp only [eEqb, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [← ofLimbs_limb a, ← ofLimbs_limb b, h.1.1, h.1.2, h.2]

/-- Atoms compared, words limb by limb. -/
def atomEqb : Atom → Atom → Bool
  | .const d c, .const d' c' => decide (d = d') && eEqb c c'
  | .const .., _ => false
  | a, b => decide (a = b)

theorem atomEqb_sound {a b : Atom} (h : atomEqb a b = true) : a = b := by
  cases a <;> cases b <;> simp only [atomEqb, Bool.and_eq_true, decide_eq_true_eq,
    Bool.false_eq_true] at h <;> first | exact h | (rw [h.1, eEqb_sound h.2])

mutual
/-- Statements compared structurally. -/
def stmtEqb : Stmt → Stmt → Bool
  | .atom a, .atom b => atomEqb a b
  | .ite c z n, .ite c' z' n' => decide (c = c') && stmtsEqb z z' && stmtsEqb n n'
  | .match_ x as, .match_ x' as' => decide (x = x') && armsEqb as as'
  | .call f a r, .call f' a' r' => decide (f = f') && decide (a = a') && decide (r = r')
  | .callIf c f a, .callIf c' f' a' => decide (c = c') && decide (f = f') && decide (a = a')
  | .dispatch x fs a r, .dispatch x' fs' a' r' =>
      decide (x = x') && decide (fs = fs') && decide (a = a') && decide (r = r')
  | .ret vs, .ret vs' => decide (vs = vs')
  | _, _ => false

/-- Statement lists compared structurally. -/
def stmtsEqb : List Stmt → List Stmt → Bool
  | [], [] => true
  | s :: ss, s' :: ss' => stmtEqb s s' && stmtsEqb ss ss'
  | _, _ => false

/-- Arms compared structurally. -/
def armsEqb : List (List Stmt) → List (List Stmt) → Bool
  | [], [] => true
  | a :: as, a' :: as' => stmtsEqb a a' && armsEqb as as'
  | _, _ => false
end

mutual
theorem stmtEqb_sound : ∀ {s t : Stmt}, stmtEqb s t = true → s = t
  | .atom a, .atom b, h => by rw [atomEqb_sound h]
  | .ite c z n, .ite c' z' n', h => by
    simp only [stmtEqb, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1, stmtsEqb_sound h.1.2, stmtsEqb_sound h.2]
  | .match_ x as, .match_ x' as', h => by
    simp only [stmtEqb, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1, armsEqb_sound h.2]
  | .call .., .call .., h => by
    simp only [stmtEqb, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1, h.1.2, h.2]
  | .callIf .., .callIf .., h => by
    simp only [stmtEqb, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1, h.1.2, h.2]
  | .dispatch .., .dispatch .., h => by
    simp only [stmtEqb, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1.1, h.1.1.2, h.1.2, h.2]
  | .ret _, .ret _, h => by
    simp only [stmtEqb, decide_eq_true_eq] at h
    rw [h]
  | .atom _, .ite .., h | .atom _, .match_ .., h | .atom _, .call .., h | .atom _, .callIf .., h
  | .atom _, .dispatch .., h | .atom _, .ret _, h | .ite .., .atom _, h | .ite .., .match_ .., h
  | .ite .., .call .., h | .ite .., .callIf .., h | .ite .., .dispatch .., h | .ite .., .ret _, h
  | .match_ .., .atom _, h | .match_ .., .ite .., h | .match_ .., .call .., h
  | .match_ .., .callIf .., h | .match_ .., .dispatch .., h | .match_ .., .ret _, h
  | .call .., .atom _, h | .call .., .ite .., h | .call .., .match_ .., h | .call .., .callIf .., h
  | .call .., .dispatch .., h | .call .., .ret _, h | .callIf .., .atom _, h
  | .callIf .., .ite .., h | .callIf .., .match_ .., h | .callIf .., .call .., h
  | .callIf .., .dispatch .., h | .callIf .., .ret _, h | .dispatch .., .atom _, h
  | .dispatch .., .ite .., h | .dispatch .., .match_ .., h | .dispatch .., .call .., h
  | .dispatch .., .callIf .., h | .dispatch .., .ret _, h | .ret _, .atom _, h
  | .ret _, .ite .., h | .ret _, .match_ .., h | .ret _, .call .., h | .ret _, .callIf .., h
  | .ret _, .dispatch .., h => by simp [stmtEqb] at h

theorem stmtsEqb_sound : ∀ {s t : List Stmt}, stmtsEqb s t = true → s = t
  | [], [], _ => rfl
  | s :: ss, t :: tt, h => by
    simp only [stmtsEqb, Bool.and_eq_true] at h
    rw [stmtEqb_sound h.1, stmtsEqb_sound h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [stmtsEqb] at h

theorem armsEqb_sound : ∀ {s t : List (List Stmt)}, armsEqb s t = true → s = t
  | [], [], _ => rfl
  | s :: ss, t :: tt, h => by
    simp only [armsEqb, Bool.and_eq_true] at h
    rw [stmtsEqb_sound h.1, armsEqb_sound h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [armsEqb] at h
end

theorem gen_pow_ordG : gen ^ ordG = 1 := by
  rw [gen_pow_eq_ofK, Parameters.gpow, show ordG = orderOf g from orderOf_g.symm,
    pow_orderOf_eq_one, ofK_one]

theorem ordG_pos : 0 < ordG := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by decide))

/-- **A loop behind its guard** (`for x in mul_range(1, N)`: `callIf (1 + N) f [1, …]`): the guard
is in `K` and, when nonzero, the loop runs, exactly when `N = g^m` for some `m` below the order of
`g` and the body holds at every `g^j`, `j < m`. -/
theorem guarded_loop_iff {P : Core.Program} {rd : Reader} {f : String} {ps : List E} {N : E}
    {B : E → Prop}
    (hstep : ∀ d x, P.relN rd (d + 1) f (x :: ps) [] ↔
      B x ∧ IsInK (x * gen + N) ∧ (x * gen + N ≠ 0 → P.relN rd d f (x * gen :: ps) [])) :
    (IsInK (1 + N) ∧ (1 + N ≠ 0 → P.Rel rd f (1 :: ps) [])) ↔
      ∃ m < ordG, N = gen ^ m ∧ ∀ j < m, B (gen ^ j) := by
  have hl := loop_iff hstep 0
  rw [pow_zero] at hl
  constructor
  · rintro ⟨hK, hrun⟩
    by_cases h1 : 1 + N = 0
    · refine ⟨0, by decide, ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      rw [pow_zero]; exact (e_add_eq_zero_iff.mp h1).symm
    · obtain ⟨m, hm, hN, hfirst, hall⟩ := hl.mp (hrun h1)
      refine ⟨m, ?_, hN, fun j hj => hall j (Nat.zero_le j) hj⟩
      by_contra hge
      rcases Nat.lt_or_ge ordG m with hgt | hle
      · have : gen ^ (m - ordG) = N := by
          obtain ⟨t, rfl⟩ : ∃ t, m = ordG + t := ⟨m - ordG, by omega⟩
          rw [hN, pow_add, gen_pow_ordG, one_mul, Nat.add_sub_cancel_left]
        exact hfirst (m - ordG) (Nat.sub_pos_of_lt hgt) (Nat.sub_lt (by omega) ordG_pos) this
      · have hm' : m = ordG := by omega
        rw [hm', gen_pow_ordG] at hN
        exact h1 (by rw [hN]; exact e_add_self 1)
  · rintro ⟨m, hm, hN, hall⟩
    refine ⟨?_, fun h1 => ?_⟩
    · rw [hN]
      exact isInK_add (by rw [← pow_zero gen]; exact gen_pow_isInK 0) (gen_pow_isInK m)
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (show 1 + N = 0 by rw [hN, h, pow_zero]; exact e_add_self 1) h1
      · exact h
    exact hl.mpr ⟨m, hm0, hN, first_hit_of_lt hm hN, fun j _ hj => hall j hj⟩

/-- A forward branch whose blocks have no `ret` holds, then its continuation. -/
theorem holds_ite_noRet {C : CallRel} {rd : Reader} {σ : Val} (c : V) (z n : List Stmt)
    (hz : Stmt.noRetList z = true) (hn : Stmt.noRetList n = true) (next : Prop)
    (kret : List E → Prop) :
    Stmt.Holds C rd σ (.ite c z n) next kret ↔
      (IsInK (σ c) ∧ (σ c = 0 → Stmt.HoldsList C rd σ z True kret) ∧
        (σ c ≠ 0 → Stmt.HoldsList C rd σ n True kret)) ∧ next := by
  rw [holds_noRet (.ite c z n) (by simp [Stmt.noRet, hz, hn]) next kret]
  rfl

set_option maxRecDepth 8000 in
theorem e_mul_inv_cancel {z : E} (h : z ≠ 0) : z * z⁻¹ = 1 := mul_inv_cancel₀ h

theorem eToNat_ofK (a : K) : eToNat (ofK a) = kToNat a := by
  simp [eToNat, limb_ofK, kToNat]

end
end LeanVM.Guest.B1
