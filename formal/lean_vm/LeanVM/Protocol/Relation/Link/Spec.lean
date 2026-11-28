/-
  LeanVM.Protocol.Relation.Link.Spec

  `verify_link` round by round, from the link's arithmetization: the relation failing becomes the
  link's end failing on the stack, or the Keccak defect surviving at the `KECCAK` row point, every
  group of challenges within `εmsg` after its grind.
-/

module

public import LeanVM.Protocol.Relation.Iface
public import LeanVM.Protocol.Relation.Link.Rounds
public import LeanVM.Protocol.Relation.Link.Tail
public import LeanVM.Protocol.Compile.SpecRules.Packed
public import LeanVM.Protocol.Link.Sound
import LeanVM.Protocol.Field

/-!
# The link, round by round

H4's `verifyLink_sound` (`Protocol/Link/Sound.lean`) bounds the best prover's chance against
`verifyLink` as a whole; here the same argument is a specification in the doom calculus
(`Compile/Spec.lean`), group by group, at a fixed stack `q` and the link's chunks, from the link's
arithmetization (`LinkArith`): the index summand `idx` (a table of partial sums over the pointer
width, of degree `2` a round, when the pointers are one-hot, `Good`), the fresh coefficients'
weights `B` (`B_0` the batched mirror certificate, `B_1..4` `JUMP`'s constraint sums, each of degree
at most `2` in each index variable), the row summand `row` (its partial sums over the row and
pointer-column variables, of the row side's round degrees, totalling `idx + Σ_i fresh_i·B_i`), and
the facts tying the end of `linkTail` to the stack (`tail`, `keccak_point`). The doom, group by
group (`linkSpecOf`):

* **after the grind and `θ_0` with the packed challenges** (`GroupDoom`, no prover move between
  them, so one group, `Spec.ofNoMove`): the index side's claim is not the index summand's sum
  (when `Good`), or some `B_i` is a nonzero polynomial in the index point, or the Keccak defect's
  multilinear extension is not zero. Its error is `LinkArith.group`'s count,
  `max(m + 3 + BYTECODE_SLOT_BITS, W + 1)/|E|`, the numerator `verify_link` grinds for
  (`linkGroupError`);
* **the index rounds** (`roundsSpec`, degree `2`, no grind): the claim false, or a `B_i` still
  nonzero in the challenges not yet drawn, or the defect, `2/|E|` a round;
* **the memory term `m1`** keeps it; **the five fresh coefficients** (a packed draw): the row side's
  claim is not the row summand's sum but for `|E|^4` of the `|E|^5` (`card_affine_le`), or the
  defect, `1/|E|`;
* **the program's split** (`computedSplit`) keeps it;
* **the row rounds and the pointer-column rounds** (`roundsSpec`, their grinds): the claim false, or
  the defect's restriction to the row challenges drawn so far nonzero (multilinear, `1/|E|` a
  round, within the round's `(rc − 1)/|E|`);
* **the packed message and the terminal check**: a false final claim fails the check unless the
  link's end fails on the stack (`tail`), and a surviving defect is `KeccakDefectAt`.

`linkSpec_of_arith` lifts it to a subsingleton set of candidates.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.Link Finset
open scoped ENNReal

@[expose] public section

open Classical

/-! ## The arithmetization the link's specification takes -/

/-- The numerator the link's challenges grind for, `max(m + 3 + BYTECODE_SLOT_BITS, W + 1)`. -/
def linkGroupError (layout : Layout) (chunks : Chunks) : ℕ :=
  max (linkRows layout + 3 + bytecodeSlotBits) (chunks.width + 1)

/-- The row side's variables, `m + m_Q`. -/
def linkRowVars (layout : Layout) : ℕ := linkRows layout + linkQVars layout

/-- Lane `l`'s Keccak defect, its multilinear extension at the first `KECCAK` log-height row
variables of a point of the row side. -/
def keccakDefectRow (layout : Layout) {μ : ℕ} (q : Column μ) (l : ℕ) (p : List E) : E :=
  rowMle (p.take (keccakHeight layout)) (keccakDefect layout q l)

/-- **The Keccak defect survives** the row challenges `pre` drawn so far. -/
def KeccakCarry (layout : Layout) {μ : ℕ} (q : Column μ) (pre : List E) : Prop :=
  (∃ l : Fin keccakStateLanes, NonzeroAfter (keccakDefectRow layout q l) (linkRowVars layout) pre) ∨
    False

/-- The carried part of the index rounds' doom: some `B_i` nonzero in the index challenges not yet
drawn, or the Keccak defect. -/
def IndexCarry (layout : Layout) {μ : ℕ} (q : Column μ) (chunks : Chunks)
    (B : E → List E → List E → Fin 5 → E) (theta0 : E) (drawn pre : List E) : Prop :=
  (∃ i, NonzeroAfter (fun r ↦ B theta0 drawn r i) chunks.width pre) ∨ KeccakCarry layout q []

/-- **The link's arithmetization proper** at a stack `q` and chunks: the summands, their rounds and
totals, the drawn group's count and the terminal check (`notes/hotwire-port.md`, M2-A, what is
left). -/
structure LinkCore (layout : Layout) {μ : ℕ} (q : Column μ) (chunks : Chunks) where
  /-- The pointers are one-hot: the index summand is a table of partial sums. -/
  Good : Prop
  /-- The index summand, from `θ_0` and the drawn challenges, over the index point. -/
  idx : E → List E → List E → E
  /-- The fresh coefficients' weights in the row side's sum, at the index point. -/
  B : E → List E → List E → Fin 5 → E
  /-- The row summand, from `θ_0`, the drawn challenges, the index point and the fresh
  coefficients, over the row and pointer-column variables. -/
  row : E → List E → List E → List E → List E → E
  idx_rounds : Good → ∀ theta0 drawn, RoundPolys (idx theta0 drawn) chunks.width (fun _ ↦ 2)
  B_deg : ∀ theta0 drawn i, PerVarDeg (fun r ↦ B theta0 drawn r i) chunks.width 2
  row_rounds : ∀ theta0 drawn r fresh, RoundPolys (row theta0 drawn r fresh) (linkRowVars layout)
    (rowDegrees (linkRows layout) (roundCoefficients chunks.d).1 (roundCoefficients chunks.d).2)
  row_total : ∀ theta0 drawn r fresh, r.length = chunks.width →
    row theta0 drawn r fresh [] = idx theta0 drawn r + ∑ i : Fin 5, fresh.getD i 0 * B theta0 drawn r i
  /-- **The drawn group's count**: the relation failing, the group's doom fails at no more than
  `linkGroupError` `|E|`-ths of `(θ_0, drawn)`. -/
  group : (¬ LinkRel layout q ∨ ¬ KeccakRel layout q) →
    (univ.filter fun v : Fin (linkDrawn layout chunks + 1) → E ↦
      ¬ RoundDoom Good (idx ((List.ofFn v).headD 0) (List.ofFn v).tail)
        (IndexCarry layout q chunks B ((List.ofFn v).headD 0) (List.ofFn v).tail)
        (indexClaim layout chunks (List.ofFn v).tail) []).card ≤
      linkGroupError layout chunks * Fintype.card E ^ linkDrawn layout chunks
  /-- **The terminal check**: a final claim other than the row summand at the final point is not
  `last` unless the link's end fails on the stack. -/
  tail : ∀ theta0 drawn r m1 fresh chi qPoint message, message.length = tailLen layout →
    chi.length = linkRows layout → qPoint.length = linkQVars layout →
    (tailValues layout chunks theta0 drawn r m1 fresh
        (splitAt layout.bytecode (r.take layout.logBytecode) (pcSlots layout.tables)) chi qPoint
        message).1 ≠ row theta0 drawn r fresh (chi ++ qPoint) →
    ¬ LinkEndHolds layout q (tailValues layout chunks theta0 drawn r m1 fresh
        (splitAt layout.bytecode (r.take layout.logBytecode) (pcSlots layout.tables)) chi qPoint
        message).2

/-- **The link's arithmetization** at a stack `q` and chunks: what `linkSpecOf` takes, the core
with the layout's facts (`linkArith_of_core`, `Link/Facts.lean`). -/
structure LinkArith (layout : Layout) {μ : ℕ} (q : Column μ) (chunks : Chunks)
    extends LinkCore layout q chunks where
  /-- The Keccak defect's extension is multilinear. -/
  keccak_deg : ∀ l, PerVarDeg (keccakDefectRow layout q l) (linkRowVars layout) 1
  /-- The `KECCAK` table's row point in the link's end is the first log-height row challenges. -/
  keccak_point : ∀ theta0 drawn r m1 fresh split chi qPoint message,
    ((tailValues layout chunks theta0 drawn r m1 fresh split chi qPoint message).2.columns.getD
      opKeccak ([], [])).1 = chi.take (keccakHeight layout)
  /-- The group's numerator is below `|E|` (the row variables and the width are small). -/
  group_small : linkGroupError layout chunks < 2 ^ 128

theorem getD_le_foldl_max : ∀ (l : List ℕ) (a t : ℕ), l.getD t 0 ≤ l.foldl max a
  | [], a, t => by simp
  | b :: l, a, 0 => by
    simp only [List.getD_cons_zero, List.foldl_cons]
    exact (le_max_right a b).trans (foldl_max_ge l _)
  | b :: l, a, t + 1 => by
    simp only [List.getD_cons_succ, List.foldl_cons]
    exact getD_le_foldl_max l _ t
where
  foldl_max_ge : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a
    | [], _ => le_rfl
    | b :: l, a => (le_max_left a b).trans (foldl_max_ge l _)

/-- The `KECCAK` table's row variables are among the row side's. -/
theorem keccakHeight_le_linkRows (layout : Layout) : keccakHeight layout ≤ linkRows layout :=
  getD_le_foldl_max _ _ _

/-! ## Moves without a prover move -/

/-- A program of challenges and packed draws only. -/
def DrawsOnly {α : Type} : VerifierProgram α → Prop
  | .ret _ => True
  | .sample k => ∀ x, DrawsOnly (k x)
  | .samplePacked _ k => ∀ cs, DrawsOnly (k cs)
  | _ => False

theorem DrawsOnly.after {α : Type} {p : VerifierProgram α} (hp : DrawsOnly p) :
    ∀ {l : List Ev} {q : VerifierProgram α}, p.after l = some q → DrawsOnly q := by
  intro l
  induction l generalizing p with
  | nil => intro q h; simp only [VerifierProgram.after, Option.some.injEq] at h; exact h ▸ hp
  | cons e es ih =>
    intro q h
    cases p <;> cases e <;> simp only [VerifierProgram.after, reduceCtorEq, DrawsOnly] at h hp
    · exact ih (hp _) h
    · split at h
      · exact ih (hp _) h
      · cases h

theorem DrawsOnly.not_isMove {α : Type} {p : VerifierProgram α} (hp : DrawsOnly p) :
    ¬ p.IsMove := by
  cases p <;> simp_all [DrawsOnly, VerifierProgram.IsMove]

/-- The link's group of challenges: `θ_0`, then the packed draw. -/
def linkGroup (n : ℕ) : VerifierProgram (E × List E) :=
  VerifierProgram.sampleChallenge >>= fun theta0 ↦
    VerifierProgram.sampleChallengesPacked n >>= fun drawn ↦ pure (theta0, drawn)

theorem drawsOnly_linkGroup (n : ℕ) : DrawsOnly (linkGroup n) := fun _ _ ↦ trivial

theorem linkGroup_bind {α : Type} (n : ℕ) (k : E → List E → VerifierProgram α) :
    (VerifierProgram.sampleChallenge >>= fun theta0 ↦
      VerifierProgram.sampleChallengesPacked n >>= fun drawn ↦ k theta0 drawn) =
      (linkGroup n >>= fun x ↦ k x.1 x.2) := rfl

/-- **The group's escape** is the fraction of `(θ_0, drawn)` breaking the doom. -/
theorem escRet_linkGroup (n : ℕ) (P : E × List E → Prop) (h₀ : List Ev) :
    VerifierProgram.escRet (fun x _ ↦ P x) h₀ [] (linkGroup n) =
      avgPk (n + 1) fun l ↦ if ¬ P (l.headD 0, l.tail) then 1 else 0 := by
  rw [avgPk_succ]
  simp only [VerifierProgram.escRet, linkGroup, VerifierProgram.sampleChallenge, VerifierProgram.sampleChallengesPacked,
    VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind, VerifierProgram.retExp]
  congr 1
  refine Finset.sum_congr rfl fun c _ ↦ avgPk_congr fun cs _ ↦ ?_
  by_cases h : P (c, cs) <;> simp [h]

/-! ## The specification -/

theorem linkGroupError_div_lt_one (layout : Layout) (chunks : Chunks)
    (hm : linkRows layout ≤ 2 ^ 32) (hw : chunks.width ≤ 2 ^ 32) :
    ((linkGroupError layout chunks : ℕ) : ℝ≥0∞) / Fintype.card E < 1 := by
  rw [Protocol.card_E, ENNReal.div_lt_iff (by simp) (by simp), one_mul]
  exact_mod_cast (show linkGroupError layout chunks < 2 ^ 128 by
    unfold linkGroupError bytecodeSlotBits; omega)

/-- `1/|E|`, a packed draw of one bad `|E|`-th, is within `εmsg`. -/
theorem one_div_card_le_εmsg : ((1 : ℕ) : ℝ≥0∞) / Fintype.card E ≤ εmsg := by
  have := grindingBits_discount 1
  rwa [show grindingBits 1 = 0 from rfl, pow_zero, one_mul] at this


/-! ## Constant doom -/

/-- **Constant doom**: any program keeps a doom that ignores the history (`RomSpec`'s
`constSpec`). -/
noncomputable def constDoom {α : Type} (p : VerifierProgram α) (φ : Prop) {T : ℝ≥0∞}
    (hT : T ≤ εmsg) : Spec p (fun _ ↦ φ) (fun _ _ ↦ φ) εmsg T T where
  D _ _ := φ
  V _ _ := if φ then min 1 T else 1
  le_one _ _ := by split_ifs <;> simp
  start_D _ h := h
  start_V _ h := by simp [h]
  read := fun _ _ _ h ↦ h
  readPacked := fun _ _ _ _ h ↦ h
  grind := fun _ _ h ↦ h
  commit := fun _ _ _ _ h ↦ h
  sample := fun _ _ ↦ (inv_card_mul_sum_const _).le
  samplePacked := fun _ _ ↦ (avgPk_const _ _).le
  query := fun _ _ _ ↦ le_rfl
  moveEnd := fun _ _ _ hD ↦ by simp [hD]
  retEnd := fun _ _ hD ↦ by simp [hD]
  retDoom := fun _ _ hD ↦ by simp [hD]
  post := fun _ _ hD ↦ hD
  bound := fun _ _ _ hD ↦ by
    simp only [hD, ite_true]
    calc _ ≤ 1 * min 1 T := by
          gcongr; exact pow_le_one₀ (zero_le) (ENNReal.inv_le_one.2 one_le_two)
      _ ≤ εmsg := by rw [one_mul]; exact (min_le_right _ _).trans hT

/-! ## The tail -/

section Phases

variable {layout : Layout} {μ : ℕ} {q : Column μ} {chunks : Chunks} (A : LinkArith layout q chunks)

/-- What the link leaves fails on the stack, or the Keccak defect survives at the `KECCAK` row
point. -/
def LinkPost (layout : Layout) {μ : ℕ} (q : Column μ) (e : LinkEnd) : Prop :=
  ¬ LinkEndHolds layout q e ∨ KeccakDefectAt layout q e

/-- **The packed message and the terminal check.** -/
noncomputable def tailSpec {T : ℝ≥0∞} (hT : T ≤ εmsg) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh chi qPoint : List E) (claim : E) (hchi : chi.length = linkRows layout)
    (hq : qPoint.length = linkQVars layout) :
    Spec (linkTail layout chunks theta0 drawn r m1 fresh
        (splitAt layout.bytecode (r.take layout.logBytecode) (pcSlots layout.tables)) chi qPoint claim)
      (fun _ ↦ RoundDoom True (A.row theta0 drawn r fresh) (KeccakCarry layout q) claim (chi ++ qPoint))
      (fun e _ ↦ LinkPost layout q e) εmsg 0 T := by
  rw [linkTail_eq]
  set split := splitAt layout.bytecode (r.take layout.logBytecode) (pcSlots layout.tables)
  set D := RoundDoom True (A.row theta0 drawn r fresh) (KeccakCarry layout q) claim (chi ++ qPoint)
  refine (Spec.readPackedE (Pre := fun _ ↦ D) (Post := fun xs _ ↦ xs.length = tailLen layout ∧ D)
    (tailLen layout) (fun _ _ hp hl ↦ ⟨hl, hp⟩) hT).bind' fun message ↦ ?_
  refine (Spec.require (Post := fun _ _ ↦ LinkPost layout q
      (tailValues layout chunks theta0 drawn r m1 fresh split chi qPoint message).2)
    fun _ ⟨hl, hD⟩ hc ↦ ?_).bind' fun _ ↦
    (Spec.ret (Post := fun e _ ↦ LinkPost layout q e) _).congr (VerifierProgram.pure_eq _).symm
  rcases hD with ⟨-, hne⟩ | hK
  · exact .inl (A.tail theta0 drawn r m1 fresh chi qPoint message hl hchi hq (hc ▸ hne))
  · rcases hK with ⟨l, hl'⟩ | hF
    · refine .inr ⟨l, l.isLt, ?_⟩
      have hlen : (chi ++ qPoint).length = linkRowVars layout := by
        simp [linkRowVars, hchi, hq]
      have h := nonzeroAfter_full hlen hl'
      rw [A.keccak_point]
      simpa [keccakDefectRow, List.take_append_of_le_length (hchi ▸ keccakHeight_le_linkRows layout)] using h
    · exact hF.elim

/-! ## The row side -/

/-- `rowDegrees` on the row rounds. -/
theorem rowDegrees_row {m rc cc i : ℕ} (hi : i < m) : rowDegrees m rc cc i = rc - 1 := by
  simp [rowDegrees, hi]

/-- `rowDegrees` on the pointer-column rounds. -/
theorem rowDegrees_col {m rc cc i : ℕ} (hi : m ≤ i) : rowDegrees m rc cc i = cc - 1 := by
  simp [rowDegrees, show ¬ i < m by omega]

/-- The Keccak carry breaks at most `count − 1 ≥ 1` challenges a round. -/
theorem keccakCarry_escape (hk : ∀ l, PerVarDeg (keccakDefectRow layout q l) (linkRowVars layout) 1)
    {count : ℕ} (hc : 2 ≤ count) (pre : List E)
    (hpre : pre.length < linkRowVars layout) (hC : KeccakCarry layout q pre) :
    (univ.filter fun c ↦ ¬ KeccakCarry layout q (pre ++ [c])).card ≤ count - 1 :=
  by
    have h := card_carry_escape (f := fun l : Fin keccakStateLanes ↦ keccakDefectRow layout q l)
      (d := 1) (count := count) (fun l ↦ hk l) (by omega) False pre hpre hC
    unfold KeccakCarry
    convert h

/-- **The pointer-column rounds, then the tail.** -/
noncomputable def colSpec {T : ℝ≥0∞} (hT : T ≤ εmsg) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh chi : List E) (claim : E) (hchi : chi.length = linkRows layout) :
    Spec (sumcheck claim (roundCoefficients chunks.d).2 (List.replicate (linkQVars layout) none) >>=
        fun x ↦ linkTail layout chunks theta0 drawn r m1 fresh
          (splitAt layout.bytecode (r.take layout.logBytecode) (pcSlots layout.tables)) chi x.1 x.2)
      (fun _ ↦ RoundDoom True (A.row theta0 drawn r fresh) (KeccakCarry layout q) claim chi)
      (fun e _ ↦ LinkPost layout q e) εmsg 0 T := by
  have hcc := (two_le_roundCoefficients chunks.d).2
  refine (roundsSpec (roundCoefficients chunks.d).2 hcc (n0 := linkRows layout)
    (n := linkRowVars layout) (Good := True)
    (fun _ ↦ RoundPolys.between (A.row_rounds theta0 drawn r fresh) le_rfl fun i hi _ ↦ (rowDegrees_col hi).le)
    (fun pre _ hp hC ↦ keccakCarry_escape A.keccak_deg hcc pre hp hC) (linkQVars layout) claim chi
    (by omega) (by simp [linkRowVars, hchi])).bind' fun x ↦ ?_
  by_cases hx : x.1.length = linkQVars layout
  · exact (tailSpec A hT theta0 drawn r m1 fresh chi x.1 x.2 hchi hx).mono
      (fun _ h ↦ h.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  · exact Spec.dead.mono (fun _ h ↦ hx h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **The row rounds, then the pointer-column rounds and the tail.** -/
noncomputable def rowRoundsSpec {T : ℝ≥0∞} (hT : T ≤ εmsg) (theta0 : E) (drawn r : List E)
    (m1 : E) (fresh : List E) (claim : E) :
    Spec (sumcheck claim (roundCoefficients chunks.d).1 (List.replicate (linkRows layout) none) >>=
        fun y ↦ sumcheck y.2 (roundCoefficients chunks.d).2 (List.replicate (linkQVars layout) none) >>=
          fun x ↦ linkTail layout chunks theta0 drawn r m1 fresh
            (splitAt layout.bytecode (r.take layout.logBytecode) (pcSlots layout.tables)) y.1 x.1 x.2)
      (fun _ ↦ RoundDoom True (A.row theta0 drawn r fresh) (KeccakCarry layout q) claim [])
      (fun e _ ↦ LinkPost layout q e) εmsg 0 T := by
  have hrc := (two_le_roundCoefficients chunks.d).1
  refine (roundsSpec (roundCoefficients chunks.d).1 hrc (n0 := 0) (n := linkRows layout)
    (Good := True)
    (fun _ ↦ RoundPolys.between (A.row_rounds theta0 drawn r fresh) (by simp [linkRowVars])
      fun i _ hi ↦ (rowDegrees_row hi).le)
    (fun pre _ hp hC ↦ keccakCarry_escape A.keccak_deg hrc pre (by simp only [linkRowVars]; omega) hC)
    (linkRows layout) claim [] le_rfl (by simp)).bind' fun y ↦ ?_
  by_cases hy : y.1.length = linkRows layout
  · exact (colSpec A hT theta0 drawn r m1 fresh y.1 y.2 hy).mono
      (fun _ h ↦ by simpa using h.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  · exact Spec.dead.mono (fun _ h ↦ hy h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- The deployed program's split, at the link's point. -/
theorem computedSplit_eq (bytecode : List K) (point : List E) (pc : List (ℕ × ℕ)) :
    computedSplit bytecode point pc =
      (VerifierProgram.require (point.length < 64 ∧ bytecode.length >>> bytecodeSlotBits =
        2 ^ point.length) >>= fun _ ↦ VerifierProgram.ret (splitAt bytecode point pc)) := rfl

/-- **The program's split keeps a doom**, and returns `splitAt`. -/
noncomputable def splitSpec (φ : Prop) (bytecode : List K) (point : List E) (pc : List (ℕ × ℕ)) :
    Spec (computedSplit bytecode point pc) (fun _ ↦ φ)
      (fun s _ ↦ s = splitAt bytecode point pc ∧ φ) εmsg 0 0 := by
  rw [computedSplit_eq]
  exact (Spec.require (Post := fun _ _ ↦ φ) fun _ h _ ↦ h).bind' fun _ ↦
    (Spec.ret (Post := fun s _ ↦ s = splitAt bytecode point pc ∧ φ) _).mono
      (fun _ h ↦ ⟨rfl, h⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **The fresh coefficients** leave the row side's claim false but for one `|E|`-th of them. -/
theorem card_fresh_doom (theta0 : E) (drawn r : List E) (claim : E)
    (hr : r.length = chunks.width)
    (hD : RoundDoom A.Good (A.idx theta0 drawn) (IndexCarry layout q chunks A.B theta0 drawn) claim r) :
    (univ.filter fun v : Fin 5 → E ↦ ¬ RoundDoom True (A.row theta0 drawn r (List.ofFn v))
      (KeccakCarry layout q) claim []).card ≤ 1 * Fintype.card E ^ (5 - 1) := by
  by_cases hK : KeccakCarry layout q []
  · simp [RoundDoom, hK]
  have hne : A.idx theta0 drawn r - claim ≠ 0 ∨ ∃ i, A.B theta0 drawn r i ≠ 0 := by
    rcases hD with ⟨-, h⟩ | (⟨i, hi⟩ | h)
    · exact .inl (sub_ne_zero.mpr (Ne.symm h))
    · exact .inr ⟨i, nonzeroAfter_full hr hi⟩
    · exact absurd h hK
  rw [one_mul]
  refine le_trans (card_le_card fun v hv ↦ ?_) (card_affine_le _ _ hne)
  simp only [mem_filter, mem_univ, true_and, RoundDoom, not_or, not_not] at hv ⊢
  have h := hv.1
  rw [A.row_total _ _ _ _ hr] at h
  simp only [getD_ofFn] at h
  linear_combination -h

/-- **The row phase**: the memory term, the fresh coefficients, the split, the row side's rounds
and the tail. -/
noncomputable def rowPhaseSpec {T : ℝ≥0∞} (hT : T ≤ εmsg) (theta0 : E) (drawn r : List E)
    (claim : E) (hr : r.length = chunks.width) :
    Spec (linkRowPhase computedSplit layout chunks theta0 drawn r claim)
      (fun _ ↦ RoundDoom A.Good (A.idx theta0 drawn) (IndexCarry layout q chunks A.B theta0 drawn)
        claim r)
      (fun e _ ↦ LinkPost layout q e) εmsg 0 T := by
  set D := RoundDoom A.Good (A.idx theta0 drawn) (IndexCarry layout q chunks A.B theta0 drawn) claim r
  have hfresh : ((1 : ℕ) : ℝ≥0∞) / Fintype.card E + 0 ≤ εmsg := by
    rw [add_zero]; exact one_div_card_le_εmsg
  refine (Spec.readE (Pre := fun _ ↦ D) (Post := fun _ _ ↦ D) (fun _ _ h ↦ h) hfresh).bind'
    fun m1 ↦ ?_
  refine (Spec.samplePackedCount (Pre := fun _ ↦ D)
    (Post := fun fresh _ ↦ RoundDoom True (A.row theta0 drawn r fresh) (KeccakCarry layout q) claim [])
    (T := 0) 5 1 (by norm_num) fun _ hD ↦ card_fresh_doom A theta0 drawn r claim hr hD).bind'
    fun fresh ↦ ?_
  refine (splitSpec (RoundDoom True (A.row theta0 drawn r fresh) (KeccakCarry layout q) claim [])
    layout.bytecode (r.take layout.logBytecode) (pcSlots layout.tables)).bind' fun s ↦ ?_
  by_cases hs : s = splitAt layout.bytecode (r.take layout.logBytecode) (pcSlots layout.tables)
  · subst hs
    exact (rowRoundsSpec A hT theta0 drawn r m1 fresh claim).mono (fun _ h ↦ h.2) (fun _ _ h ↦ h)
      le_rfl le_rfl le_rfl
  · exact Spec.dead.mono (fun _ h ↦ hs h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Phases


/-! ## The link -/

/-- `verifyLink` at the link's chunks: the grind, the group, the index rounds, the row phase. -/
theorem verifyLink_eq_of_chunks {layout : Layout} {chunks : Chunks}
    (hch : Chunks.new (linkWidth layout) = some chunks) :
    verifyLink computedSplit layout =
      (VerifierProgram.grindProofOfWork (grindingBits (linkGroupError layout chunks)) >>= fun _ ↦
        linkGroup (linkDrawn layout chunks) >>= fun x ↦
          sumcheck (indexClaim layout chunks x.2) 3 (List.replicate chunks.width none) >>= fun y ↦
            linkRowPhase computedSplit layout chunks x.1 x.2 y.1 y.2) := by
  rw [verifyLink_eq_linkSkeleton]
  unfold linkSkeleton
  rw [hch]
  rfl

/-- **The link, round by round, at one stack**: from its arithmetization, the relation failing on
`q` becomes the link's end failing on `q` or the Keccak defect surviving; the drawn group within
`linkGroupError/|E|` through its grind, every later group within `εmsg`. -/
noncomputable def linkSpecOf {layout : Layout} {μ : ℕ} {q : Column μ} {chunks : Chunks}
    (A : LinkArith layout q chunks) (hch : Chunks.new (linkWidth layout) = some chunks)
    {T : ℝ≥0∞} (hT : T ≤ εmsg) :
    Spec (verifyLink computedSplit layout) (fun _ ↦ ¬ LinkRel layout q ∨ ¬ KeccakRel layout q)
      (fun e _ ↦ LinkPost layout q e) εmsg εmsg T := by
  rw [verifyLink_eq_of_chunks hch]
  set D0 := ¬ LinkRel layout q ∨ ¬ KeccakRel layout q
  set e : ℝ≥0∞ := ((linkGroupError layout chunks : ℕ) : ℝ≥0∞) / Fintype.card E with he_def
  have hgrind : (2 : ℝ≥0∞)⁻¹ ^ grindingBits (linkGroupError layout chunks) * (e + 0) ≤ εmsg := by
    rw [add_zero]; exact grindingBits_discount _
  have he : e < 1 := by
    rw [he_def, Protocol.card_E, ENNReal.div_lt_iff (by simp) (by simp), one_mul]
    exact_mod_cast A.group_small
  refine ((Spec.grindP (Pre := fun _ ↦ D0) (Post := fun _ _ ↦ D0) (T := e + 0) _ (fun _ h ↦ h)
    hgrind).bind' fun _ ↦ ?_).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl ?_ le_rfl
  · refine (Spec.ofNoMove (p := linkGroup (linkDrawn layout chunks)) (Pre := fun _ ↦ D0)
      (Post := fun x _ ↦ RoundDoom A.Good (A.idx x.1 x.2) (IndexCarry layout q chunks A.B x.1 x.2)
        (indexClaim layout chunks x.2) []) (T := 0) (εmax := εmsg)
      (fun _ ha ↦ ((drawsOnly_linkGroup _).after ha).not_isMove) he fun _ hD ↦ ?_).bind' fun x ↦ ?_
    · rw [escRet_linkGroup]
      have h := avgPk_le_card (n := linkDrawn layout chunks + 1) (N := linkGroupError layout chunks)
        (by omega) (fun l ↦ ¬ RoundDoom A.Good (A.idx (l.headD 0) l.tail)
          (IndexCarry layout q chunks A.B (l.headD 0) l.tail) (indexClaim layout chunks l.tail) [])
        (by rw [Nat.add_sub_cancel]; convert A.group hD)
      refine le_trans (le_of_eq (avgPk_congr fun l _ ↦ ?_)) h
      split_ifs <;> simp_all
    · refine (roundsSpec 3 (by norm_num) (n0 := 0) (n := chunks.width) (Good := A.Good)
        (g := A.idx x.1 x.2) (Carry := IndexCarry layout q chunks A.B x.1 x.2)
        (fun hG ↦ RoundPolys.between (A.idx_rounds hG x.1 x.2) le_rfl fun _ _ _ ↦ le_rfl)
        (fun pre _ hp hC ↦ by
          have h := card_carry_escape (f := fun i r ↦ A.B x.1 x.2 r i) (d := 2) (count := 3)
            (fun i ↦ A.B_deg x.1 x.2 i) (by norm_num) (KeccakCarry layout q []) pre hp hC
          unfold IndexCarry
          convert h)
        chunks.width (indexClaim layout chunks x.2) [] le_rfl (by simp)).bind' fun y ↦ ?_
      by_cases hy : y.1.length = chunks.width
      · exact (rowPhaseSpec A hT x.1 x.2 y.1 y.2 hy).mono (fun _ h ↦ by simpa using h.2)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      · exact Spec.dead.mono (fun _ h ↦ hy h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  · split_ifs with hb
    · simpa [hb] using hgrind
    · exact zero_le

/-- **The link, round by round, on a subsingleton set of candidates**, from the arithmetization at
each candidate. -/
noncomputable def linkSpecSet (layout : Layout)
    (harith : ∀ (q : Column layout.stackLog) chunks, Chunks.new (linkWidth layout) = some chunks →
      LinkArith layout q chunks)
    (S : Set (Column layout.stackLog)) (hS : S.Subsingleton) {T : ℝ≥0∞} (hT : T ≤ εmsg) :
    Spec (verifyLink computedSplit layout)
      (fun _ ↦ ∀ q ∈ S, ¬ LinkRel layout q ∨ ¬ KeccakRel layout q)
      (fun e _ ↦ ∀ q ∈ S, ¬ LinkEndHolds layout q e ∨ KeccakDefectAt layout q e) εmsg εmsg T := by
  cases hch : Chunks.new (linkWidth layout) with
  | some chunks =>
    by_cases hq : ∃ q, q ∈ S
    · exact (linkSpecOf (harith hq.choose chunks hch) hch hT).mono (fun _ h ↦ h _ hq.choose_spec)
        (fun _ _ h q' hq' ↦ hS hq' hq.choose_spec ▸ h) le_rfl le_rfl le_rfl
    · exact (constDoom _ True hT).mono (fun _ _ ↦ trivial)
        (fun _ _ _ q' hq' ↦ absurd ⟨q', hq'⟩ hq) le_rfl hT le_rfl
  | none =>
    have hfail : verifyLink computedSplit layout = VerifierProgram.fail := by
      rw [verifyLink_eq_linkSkeleton]
      unfold linkSkeleton
      rw [hch]
      rfl
    rw [hfail]
    exact Spec.fail.mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

end

end LeanVM.Protocol.Relation
