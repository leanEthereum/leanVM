/-
  LeanVM.Guest.B1.Common.Basic

  The shared vocabulary of the B1 lemmas: a function's relation unfolded to its body, the
  compile-time words of the guest's data, memory runs, valuations built block by block,
  `mul_range` loops, and comparing statement lists by kernel evaluation.
-/

module

public import LeanVM.Guest.CoreFind
public import LeanVM.Guest.Renumber
public import LeanVM.Guest.Word
public import LeanVM.Guest.CoreLemmas
public import LeanVM.Guest.Value.Keccak
public import LeanVM.Guest.Value.Bits
public import LeanVM.Guest.ExpTables

/-!
# B1: shared vocabulary

Ported from the BLAKE2s-era `B1/Basic.lean` (its hash-chain runs dropped; the duplex sponge is
`B1/Common/Sponge.lean`).

* `rel_iff_sem`, `relN_succ_iff`: a function's relation is its body's (`Program.Rel` is a fixed
  point, `rel_iff`), and at a finite depth its calls are one level shallower.
* `word_*`: the constants the data writes as `word c0 c1`, as the Spec's words (`y`, `y⁻¹`,
  `y·E(t)`, `E(n)`, `g^a`).
* `ReadsAt rd p xs`: the words `xs` lie in memory from the pointer `p`, word `k` at `p·g^k`;
  `loadHolds_mul_gen_pow`: a load through `p·g^j` at offset `k` is the load at offset `j + k`;
  `loadHolds_unique`.
* `setv σ b n f`: `σ` with the values `.n (b + k)`, `k < n`, set to `f k`: how an honest
  valuation is built, block after block (`set_n_in`, `set_n_lt`, `set_n_ge` evaluate it).
* `loop_iff`, `guarded_loop_iff`: a `mul_range` loop helper, from `g^k` to its end `N`, holds
  exactly when `N = g^m` for the first `m > k` the loop reaches and its body holds at every `g^j`,
  `k ≤ j < m`.
* `stmtsEqb_sound`: a template equal to a function's body by `decide +kernel`.
* `RangeChecked rd x k`: what a range-check atom asks of memory (`rangeCheck_iff` gives its
  meaning on a memory image).
* `WinTabs rd tabs` (`ExpTables.lean`): the bit-window table `exponent_tables` writes
  (`[g^n] = E(n)`, `n < 2^11`), what `grind_check` and `query_window` read;
  `winTabs_of_expWinTab` reads it through `tabs = q·g^236`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier


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

theorem word_eOfNat (n : ℕ) : word n 0 = eOfNat n := by
  rw [word, eOfNat_eq_ofLimbs]
  rfl

theorem word_zero : word 0 0 = 0 := by rw [word_eOfNat, eOfNat_zero]

theorem word_one : word 1 0 = 1 := by rw [word_eOfNat, eOfNat_one]

theorem word_gen : word 2 0 = gen := by rw [word_eOfNat]; rfl

/-- `E(2^a)` is `g^a` below the first reduction. -/
theorem word_two_pow {a : ℕ} (h : a < 64) : word (2 ^ a) 0 = gen ^ a := by
  rw [word_eOfNat, gen_pow_eq_eOfNat h]

theorem word_y : word 0 1 = y := by rw [y_eq]; rfl

/-- `Y_INV = x + y`, the data's `word 2 1`. -/
theorem word_y_inv : word 2 1 = y⁻¹ := by rw [y_inv]; rfl

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

theorem limb0_mul_ofK (p : E) (c : K) : (p * ofK c).limb 0 = p.limb 0 * c := by
  rw [eq_ofLimbs p, ofLimbs_mul_ofK]
  simp

/-! ## Memory runs -/

/-- The words `xs` lie in memory from `p`: word `k` at `p·g^k`. -/
def ReadsAt (rd : Reader) (p : E) (xs : List E) : Prop :=
  ∀ k (hk : k < xs.length), LoadHolds rd p k xs[k]

theorem readsAt_nil (rd : Reader) (p : E) : ReadsAt rd p [] := fun _ hk => absurd hk (by simp)

/-- A load through `p·g^j` at offset `k` is the load at offset `j + k`. -/
theorem loadHolds_mul_gen_pow (rd : Reader) (p : E) (j k : ℕ) (w : E) :
    LoadHolds rd (p * gen ^ j) k w ↔ LoadHolds rd p (j + k) w := by
  have hg : Parameters.addressOfIndex j ≠ 0 := pow_ne_zero _ g_ne_zero
  rw [gen_pow_eq_ofK]
  unfold LoadHolds
  rw [isInK_mul_ofK hg]
  constructor
  · rintro ⟨hp, h⟩
    rw [limb0_mul_ofK, mul_assoc, Parameters.addressOfIndex, Parameters.addressOfIndex, ←
        pow_add] at h
    exact ⟨hp, h⟩
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    rw [limb0_mul_ofK, mul_assoc, Parameters.addressOfIndex, Parameters.addressOfIndex, ←
        pow_add]
    exact h


theorem loadHolds_unique {rd : Reader} {p : E} {k : ℕ} {w w' : E} (h : LoadHolds rd p k w)
    (h' : LoadHolds rd p k w') : w = w' :=
  Option.some.inj (h.2.symm.trans h'.2)

/-- Blocks without a return, one per index below `n`, hold exactly when each does. -/
theorem holdsList_range_flatten {C : CallRel} {rd : Reader} {σ : Val} (n : ℕ)
    (blk : ℕ → List Stmt) (h : ∀ i, Stmt.noRetList (blk i) = true) (next : Prop)
    (kret : List E → Prop) :
    Stmt.HoldsList C rd σ ((List.range n).map blk).flatten next kret ↔
      (∀ i < n, Stmt.HoldsList C rd σ (blk i) True kret) ∧ next := by
  rw [holdsList_flatten _ (fun b hb => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
    exact h i)]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

/-- What a range check `rangeCheck x y t1 t2 k` asks of memory, for some complement and touched
words: `x` and `k / x` are readable addresses (`rangeCheck_iff` makes it `x = g^e`, `e < K`, on a
memory image of at most `2^32` words). -/
def RangeChecked (rd : Reader) (x k : E) : Prop :=
  ∃ y t1 t2 : E, LoadHolds rd x 0 t1 ∧ k = x * y ∧ LoadHolds rd y 0 t2

/-- The specialization of `grind_check` to `bits`, `grind_check__L{bits}`, for the deployed
grinds (a table, not `toString`, whose body a `module`'s kernel cannot unfold). -/
def grindCheckName : ℕ → String
  | 2 => "grind_check__L2"
  | 3 => "grind_check__L3"
  | 7 => "grind_check__L7"
  | 13 => "grind_check__L13"
  | 15 => "grind_check__L15"
  | 17 => "grind_check__L17"
  | 18 => "grind_check__L18"
  | 19 => "grind_check__L19"
  | 20 => "grind_check__L20"
  | 21 => "grind_check__L21"
  | 22 => "grind_check__L22"
  | 23 => "grind_check__L23"
  | 24 => "grind_check__L24"
  | 25 => "grind_check__L25"
  | 26 => "grind_check__L26"
  | 27 => "grind_check__L27"
  | 28 => "grind_check__L28"
  | 29 => "grind_check__L29"
  | 30 => "grind_check__L30"
  | _ => "grind_check"

theorem WinTabs.lt {rd : Reader} {tabs : E} (h : WinTabs rd tabs) {n : ℕ} (hn : n < 2 ^ 11) :
    LoadHolds rd tabs n (eOfNat n) := h n hn

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
def eEqb (a b : E) : Bool := decide (a.limb 0 = b.limb 0) && decide (a.limb 1 = b.limb 1)

theorem eEqb_sound {a b : E} (h : eEqb a b = true) : a = b := by
  simp only [eEqb, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [← ofLimbs_limb a, ← ofLimbs_limb b, h.1, h.2]

/-- Values compared, their indices first (`Nat.beq`, which the kernel evaluates on literals). -/
def vEqb (a b : V) : Bool := a.idx == b.idx && a.tag == b.tag && decide (a.path = b.path)

theorem vEqb_iff {a b : V} : vEqb a b = true ↔ a = b := by
  cases a; cases b
  simp only [vEqb, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, V.mk.injEq]
  tauto

/-- Value lists compared value by value. -/
def vsEqb : List V → List V → Bool
  | [], [] => true
  | a :: as, b :: bs => vEqb a b && vsEqb as bs
  | _, _ => false

theorem vsEqb_iff : ∀ {as bs : List V}, vsEqb as bs = true ↔ as = bs
  | [], [] => by simp [vsEqb]
  | [], _ :: _ => by simp [vsEqb]
  | _ :: _, [] => by simp [vsEqb]
  | a :: as, b :: bs => by simp only [vsEqb, Bool.and_eq_true, vEqb_iff, vsEqb_iff, List.cons.injEq]

/-- Atoms compared, words limb by limb and values by `vEqb`; the rarer atoms by `decide`. -/
def atomEqb : Atom → Atom → Bool
  | .const d c, .const d' c' => vEqb d d' && eEqb c c'
  | .const .., _ => false
  | .add d a b, .add d' a' b' => vEqb d d' && vEqb a a' && vEqb b b'
  | .mul d a b, .mul d' a' b' => vEqb d d' && vEqb a a' && vEqb b b'
  | .copy d a, .copy d' a' => vEqb d d' && vEqb a a'
  | .load d p o, .load d' p' o' => vEqb d d' && vEqb p p' && o == o'
  | .keccak i o x y, .keccak i' o' x' y' => vsEqb i i' && vsEqb o o' && x == x' && y == y'
  | a, b => decide (a = b)

theorem atomEqb_sound {a b : Atom} (h : atomEqb a b = true) : a = b := by
  cases a <;> cases b <;> simp only [atomEqb, Bool.and_eq_true, decide_eq_true_eq, vEqb_iff,
    vsEqb_iff, beq_iff_eq, Bool.false_eq_true] at h <;>
    first | exact h | (rw [h.1, eEqb_sound h.2]) | (obtain ⟨⟨h1, h2⟩, h3⟩ := h; subst h1 h2 h3; rfl) |
      (obtain ⟨h1, h2⟩ := h; subst h1 h2; rfl) | (obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h; subst h1 h2 h3 h4; rfl)

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

/-- The table's window section, read through `tabs = q·g^236`, is `WinTabs`. -/
theorem winTabs_of_expWinTab {rd : Reader} {q : E} (h : ExpWinTab rd q) :
    WinTabs rd (q * gen ^ winTabAt) := fun n hn =>
  (loadHolds_mul_gen_pow rd q winTabAt n _).mpr (h n hn)

theorem gen_pow_ordG : gen ^ ordG = 1 := by
  rw [gen_pow_eq_ofK, Parameters.addressOfIndex, show ordG = orderOf g from orderOf_g.symm,
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

end
end LeanVM.Guest.B1

