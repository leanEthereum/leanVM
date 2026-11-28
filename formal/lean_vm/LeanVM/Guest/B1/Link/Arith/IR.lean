/-
  LeanVM.Guest.B1.Link.Arith.IR

  `verify_sub`'s link section computes the guest's functions: on a valuation satisfying the
  section's atoms, each value the link's arithmetic produces is the guest's function of the values
  it reads.
-/

module

public import LeanVM.Guest.B1.Link.Arith.Exec
public import LeanVM.Guest.B1.Link.Arith.Std
public import LeanVM.Guest.Pack.P33.Core

/-!
# The link section's core IR

`linkSec`: statements `487` to `2905` of `verify_sub`'s body (`Pack/P33/Core.lean`), from the
out-of-domain value's `opening_message__L1_L1` call to the `link_terminal__L{w}` dispatch. Its
buffers and returns: `chal` at value `10`, `slot` at `11` (the weights from offset `14`), the split
values at `14`, `eq_q` at `17` (`eq(q_point, ·)` from `62`), `shifts` at `19`, the sent values at
`1076` (`link_row_side`'s cursor), `below` at `13` (`below[g^log_mem]` through value `801 = 13·101`),
the corners through `cornerVn` (`corners·g^(h_t)`), `table_point`'s returns from `omegaVn`,
`state_ends`' at `752`, `753`, `index_side`'s at `797` to `799`, the fresh permutation's cells at
`782` (`cert`) and `783` to `786` (`jump`), the memory term `m1` at `772`'s word.

`IRReads rd σ v`: those values are the guest's inputs `v`. `linkSecProgram`: then the section's
values `764` (the index side's claim), `967`, `1044` (`program`, `frame_program`), `1049`
(`y_mem`), `1057` (`x_bc`), `1058` (`p_fp`) are the guest's functions at `v` (`gClaim`, …).
`linkSecRow`: if moreover `v`'s `y_mem`, `x_bc`, `p_fp` are those values (`IRAgree`), then `2846`
(`coef`), `2655` (`base`), `2733` (`cert_w`), `2890` (`rest`), `2891` (`cert_w·cert`) and the
twelve words stored at `shifts` are too.

The proof runs the section symbolically (`execStmts`, `exec_eval`), renames its inputs to the
standard variables (`ren`), and the kernel compares the normal forms (`secP_norm`, `secR_*`).
-/

namespace LeanVM.Guest.B1.Link.Arith

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Protocol.Verifier

@[expose] public section

/-- `verify_sub`'s link section. -/
noncomputable def linkSec : List Stmt := (Fn.«verify_sub».core.body.drop 487).take 2419

/-- Each table's `table_point` returns `omega` (then `act`, `eq_tau`). -/
def omegaVn : List ℕ := [1296, 1408, 1529, 1612, 1739, 1885]

/-- Each table's corner pointer, `corners·g^(h_t)`. -/
def cornerVn : List ℕ := [1299, 1411, 1532, 1615, 1742, 1888]

/-- The values the section reads, as the guest's inputs. -/
structure IRReads (rd : Reader) (σ : Val) (v : LinkIn E) : Prop where
  chal : ∀ k < 89, rdw rd (σ (.n 10)) k = v.chal k
  slot : ∀ k < 16, rdw rd (σ (.n 11)) (14 + k) = v.slot k
  sent : ∀ k < 80, rdw rd (σ (.n 1076)) k = v.sent k
  splitv : ∀ k < 36, rdw rd (σ (.n 14)) k = v.splitv k
  eqQ : ∀ q < 64, rdw rd (σ (.n 17)) (62 + q) = v.eqQ q
  omega : ∀ t < 6, σ (.n (omegaVn.getD t 0)) = v.omega t
  act : ∀ t < 6, σ (.n (omegaVn.getD t 0 + 1)) = v.act t
  eqTau : ∀ t < 6, σ (.n (omegaVn.getD t 0 + 2)) = v.eqTau t
  corner : ∀ t < 6, rdw rd (σ (.n (cornerVn.getD t 0))) 0 = v.corner t
  jump : ∀ k < 4, σ (.n (783 + k)) = v.jump k
  e0 : σ (.n 752) = v.e0
  ec : σ (.n 753) = v.ec
  idx : σ (.n 797) = v.idx
  eqzr : σ (.n 798) = v.eqzr
  shz : σ (.n 799) = v.shz
  belowMem : rdw rd (σ (.n 801)) 0 = v.belowMem
  belowBc : rdw rd (σ (.n 13)) 19 = v.belowBc
  eq0R : rdw rd (σ (.n 13)) 0 = v.eq0R
  m1 : rdw rd (σ (.n 772)) 0 = v.m1
  cert : σ (.n 782) = v.cert

/-- The values the section reads, and the `y_mem`, `x_bc`, `p_fp` it computes, as the guest's
inputs (the row side reads the three). -/
structure IRAgree (rd : Reader) (σ : Val) (v : LinkIn E) : Prop extends IRReads rd σ v where
  xBc : σ (.n 1057) = v.xBc
  pFp : σ (.n 1058) = v.pFp
  yMem : σ (.n 1049) = v.yMem

/-- The section's inputs: their codes in the run, and in `stdIn`. -/
def irInputs : List (ℕ × ℕ) :=
  (List.range 89).map (fun k ↦ (memCode 10 k, k)) ++
  (List.range 16).map (fun k ↦ (memCode 11 (14 + k), 1000 + k)) ++
  (List.range 80).map (fun k ↦ (memCode 1076 k, 2000 + k)) ++
  (List.range 36).map (fun k ↦ (memCode 14 k, 3000 + k)) ++
  (List.range 64).map (fun q ↦ (memCode 17 (62 + q), 4000 + q)) ++
  (List.range 6).map (fun t ↦ (2 * omegaVn.getD t 0, 5000 + t)) ++
  (List.range 6).map (fun t ↦ (2 * (omegaVn.getD t 0 + 1), 6000 + t)) ++
  (List.range 6).map (fun t ↦ (2 * (omegaVn.getD t 0 + 2), 7000 + t)) ++
  (List.range 6).map (fun t ↦ (memCode (cornerVn.getD t 0) 0, 8000 + t)) ++
  (List.range 4).map (fun k ↦ (2 * (783 + k), 9000 + k)) ++
  [(2 * 752, 10000), (2 * 753, 10001), (2 * 797, 10002), (2 * 798, 10003), (2 * 799, 10004),
    (memCode 801 0, 10005), (memCode 13 19, 10006), (memCode 13 0, 10007), (memCode 772 0, 10008),
    (2 * 782, 10009), (2 * 1057, 10010), (2 * 1058, 10011), (2 * 1049, 10012)]

/-- The run's code of an input to its `stdIn` code; any other variable past them. -/
def ren (i : ℕ) : ℕ := ((irInputs.find? (·.1 = i)).map (·.2)).getD (100000 + i)

/-- The run with every value defined, and with `y_mem`, `x_bc`, `p_fp` kept variables. -/
noncomputable def runP : Trie := execStmts (fun _ ↦ false) linkSec .nil

noncomputable def runR : Trie := execStmts (fun n ↦ n = 1049 || n = 1057 || n = 1058) linkSec .nil

/-- An output's check: its inputs are among the section's (those of `stdIn` code below `bound`),
its normal form the guest's. -/
noncomputable def outOk (bound : ℕ) (t : Trie) (n : ℕ) (g : Ex) : Prop :=
  (symOf t n).allVars (fun i ↦ ren i < bound) = true ∧ ((symOf t n).rename ren).norm = g.norm

theorem secP_norm : outOk 10010 runP 764 (gClaim stdIn) ∧ outOk 10010 runP 967 (gProgram stdIn).1 ∧
    outOk 10010 runP 1044 (gProgram stdIn).2 ∧ outOk 10010 runP 1049 (gYMem stdIn) ∧
    outOk 10010 runP 1057 (gXBc stdIn) ∧ outOk 10010 runP 1058 (gPFp stdIn) := by
  unfold outOk; decide +kernel

theorem secR_coef : outOk 20000 runR 2846 (gCoef stdIn) := by unfold outOk; decide +kernel

theorem secR_base : outOk 20000 runR 2655 (gBase stdIn) ∧ outOk 20000 runR 2890 (gRest stdIn) := by
  unfold outOk; decide +kernel

theorem secR_cert : outOk 20000 runR 2733 (gCertW stdIn) ∧ outOk 20000 runR 2891 (gCertW stdIn * stdIn.cert) := by
  unfold outOk; decide +kernel

/-- The words stored at `shifts`: statement, value. -/
def shiftStores : List (ℕ × ℕ) :=
  [(2367, 2854), (2376, 2862), (2385, 2870), (2388, 2872), (2391, 2874), (2394, 2876), (2397, 2878),
    (2400, 2880), (2403, 2882), (2406, 2884), (2409, 2886), (2412, 2888)]

/-- Whether statement `i` is the atom `a`. -/
def atomAt (ss : List Stmt) (i : ℕ) (a : Atom) : Bool :=
  match ss[i]? with
  | some (.atom a') => decide (a' = a)
  | _ => false

theorem mem_of_atomAt {ss : List Stmt} {i : ℕ} {a : Atom} (h : atomAt ss i a = true) :
    Stmt.atom a ∈ ss := by
  unfold atomAt at h
  split at h
  · rename_i a' he
    obtain rfl : a' = a := of_decide_eq_true h
    exact List.mem_of_getElem? he
  · simp at h

theorem secR_shifts : ∀ s < 12,
    atomAt linkSec (shiftStores.getD s (0, 0)).1
      (.load (.n (shiftStores.getD s (0, 0)).2) (.n 19) s) = true ∧
    outOk 20000 runR (shiftStores.getD s (0, 0)).2 (gShift stdIn s) := by
  unfold outOk; decide +kernel

theorem Ex.eval_mul' (a b : Ex) (ρ : ℕ → E) : (a * b).eval ρ = a.eval ρ * b.eval ρ := rfl

theorem gRest_eval (v : LinkIn E) : gRest v = (gRest stdIn).eval (envOf v) := by kernel_eq

section

variable {rd : Reader} {σ : Val} {v : LinkIn E}

theorem forall_mem_append' {l1 l2 : List (ℕ × ℕ)} {P : ℕ × ℕ → Prop} (h1 : ∀ p ∈ l1, P p)
    (h2 : ∀ p ∈ l2, P p) : ∀ p ∈ l1 ++ l2, P p :=
  fun p hp ↦ (List.mem_append.mp hp).elim (h1 p) (h2 p)

theorem forall_mem_rangeMap {n : ℕ} {f : ℕ → ℕ × ℕ} {P : ℕ × ℕ → Prop} (h : ∀ k < n, P (f k)) :
    ∀ p ∈ (List.range n).map f, P p := by
  intro p hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
  exact h k (List.mem_range.mp hk)

theorem envOf_chal (v : LinkIn E) {k : ℕ} (hk : k < 1000) : envOf v k = v.chal k := by
  unfold envOf; rw [ite_eq_left (by omega)]

theorem envOf_slot (v : LinkIn E) {k : ℕ} (hk : k < 1000) : envOf v (1000 + k) = v.slot k := by
  unfold envOf; rw [ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

theorem envOf_sent (v : LinkIn E) {k : ℕ} (hk : k < 1000) : envOf v (2000 + k) = v.sent k := by
  unfold envOf; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

theorem envOf_splitv (v : LinkIn E) {k : ℕ} (hk : k < 1000) : envOf v (3000 + k) = v.splitv k := by
  unfold envOf; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

theorem envOf_eqQ (v : LinkIn E) {k : ℕ} (hk : k < 1000) : envOf v (4000 + k) = v.eqQ k := by
  unfold envOf; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

theorem envOf_omega (v : LinkIn E) {k : ℕ} (hk : k < 1000) : envOf v (5000 + k) = v.omega k := by
  unfold envOf; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

theorem envOf_act (v : LinkIn E) {k : ℕ} (hk : k < 1000) : envOf v (6000 + k) = v.act k := by
  unfold envOf; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

theorem envOf_eqTau (v : LinkIn E) {k : ℕ} (hk : k < 1000) : envOf v (7000 + k) = v.eqTau k := by
  unfold envOf; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

theorem envOf_corner (v : LinkIn E) {k : ℕ} (hk : k < 1000) : envOf v (8000 + k) = v.corner k := by
  unfold envOf; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

theorem envOf_jump (v : LinkIn E) {k : ℕ} (hk : k < 1000) : envOf v (9000 + k) = v.jump k := by
  unfold envOf; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

theorem agree_reads (h : IRReads rd σ v) :
    ∀ p ∈ irInputs, p.2 < 10010 → irEnv rd σ p.1 = envOf v p.2 := by
  unfold irInputs
  refine forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append'
    (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append'
    (forall_mem_append' (forall_mem_append' (forall_mem_rangeMap fun k hk _ ↦ ?_)
    (forall_mem_rangeMap fun k hk _ ↦ ?_)) (forall_mem_rangeMap fun k hk _ ↦ ?_))
    (forall_mem_rangeMap fun k hk _ ↦ ?_)) (forall_mem_rangeMap fun k hk _ ↦ ?_))
    (forall_mem_rangeMap fun k hk _ ↦ ?_)) (forall_mem_rangeMap fun k hk _ ↦ ?_))
    (forall_mem_rangeMap fun k hk _ ↦ ?_)) (forall_mem_rangeMap fun k hk _ ↦ ?_))
    (forall_mem_rangeMap fun k hk _ ↦ ?_)) fun p hp hb ↦ ?_
  · dsimp only
    rw [irEnv_mem _ _ _ _ (by omega), h.chal k hk, envOf_chal v (by omega)]
  · dsimp only
    rw [irEnv_mem _ _ _ _ (by omega), h.slot k hk, envOf_slot v (by omega)]
  · dsimp only
    rw [irEnv_mem _ _ _ _ (by omega), h.sent k hk, envOf_sent v (by omega)]
  · dsimp only
    rw [irEnv_mem _ _ _ _ (by omega), h.splitv k hk, envOf_splitv v (by omega)]
  · dsimp only
    rw [irEnv_mem _ _ _ _ (by omega), h.eqQ k hk, envOf_eqQ v (by omega)]
  · dsimp only
    rw [irEnv_vn, h.omega k hk, envOf_omega v (by omega)]
  · dsimp only
    rw [irEnv_vn, h.act k hk, envOf_act v (by omega)]
  · dsimp only
    rw [irEnv_vn, h.eqTau k hk, envOf_eqTau v (by omega)]
  · dsimp only
    rw [irEnv_mem _ _ _ _ (by omega), h.corner k hk, envOf_corner v (by omega)]
  · dsimp only
    rw [irEnv_vn, h.jump k hk, envOf_jump v (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [irEnv_vn, h.e0]; rfl
    · rw [irEnv_vn, h.ec]; rfl
    · rw [irEnv_vn, h.idx]; rfl
    · rw [irEnv_vn, h.eqzr]; rfl
    · rw [irEnv_vn, h.shz]; rfl
    · rw [irEnv_mem _ _ _ _ (by omega), h.belowMem]; rfl
    · rw [irEnv_mem _ _ _ _ (by omega), h.belowBc]; rfl
    · rw [irEnv_mem _ _ _ _ (by omega), h.eq0R]; rfl
    · rw [irEnv_mem _ _ _ _ (by omega), h.m1]; rfl
    · rw [irEnv_vn, h.cert]; rfl
    · exact absurd hb (by decide)
    · exact absurd hb (by decide)
    · exact absurd hb (by decide)

theorem agree_all (h : IRAgree rd σ v) : ∀ p ∈ irInputs, irEnv rd σ p.1 = envOf v p.2 := by
  unfold irInputs
  refine forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append'
    (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append'
    (forall_mem_append' (forall_mem_append' (forall_mem_rangeMap fun k hk ↦ ?_)
    (forall_mem_rangeMap fun k hk ↦ ?_)) (forall_mem_rangeMap fun k hk ↦ ?_))
    (forall_mem_rangeMap fun k hk ↦ ?_)) (forall_mem_rangeMap fun k hk ↦ ?_))
    (forall_mem_rangeMap fun k hk ↦ ?_)) (forall_mem_rangeMap fun k hk ↦ ?_))
    (forall_mem_rangeMap fun k hk ↦ ?_)) (forall_mem_rangeMap fun k hk ↦ ?_))
    (forall_mem_rangeMap fun k hk ↦ ?_)) fun p hp ↦ ?_
  · dsimp only
    rw [irEnv_mem _ _ _ _ (by omega), h.chal k hk, envOf_chal v (by omega)]
  · dsimp only
    rw [irEnv_mem _ _ _ _ (by omega), h.slot k hk, envOf_slot v (by omega)]
  · dsimp only
    rw [irEnv_mem _ _ _ _ (by omega), h.sent k hk, envOf_sent v (by omega)]
  · dsimp only
    rw [irEnv_mem _ _ _ _ (by omega), h.splitv k hk, envOf_splitv v (by omega)]
  · dsimp only
    rw [irEnv_mem _ _ _ _ (by omega), h.eqQ k hk, envOf_eqQ v (by omega)]
  · dsimp only
    rw [irEnv_vn, h.omega k hk, envOf_omega v (by omega)]
  · dsimp only
    rw [irEnv_vn, h.act k hk, envOf_act v (by omega)]
  · dsimp only
    rw [irEnv_vn, h.eqTau k hk, envOf_eqTau v (by omega)]
  · dsimp only
    rw [irEnv_mem _ _ _ _ (by omega), h.corner k hk, envOf_corner v (by omega)]
  · dsimp only
    rw [irEnv_vn, h.jump k hk, envOf_jump v (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [irEnv_vn, h.e0]; rfl
    · rw [irEnv_vn, h.ec]; rfl
    · rw [irEnv_vn, h.idx]; rfl
    · rw [irEnv_vn, h.eqzr]; rfl
    · rw [irEnv_vn, h.shz]; rfl
    · rw [irEnv_mem _ _ _ _ (by omega), h.belowMem]; rfl
    · rw [irEnv_mem _ _ _ _ (by omega), h.belowBc]; rfl
    · rw [irEnv_mem _ _ _ _ (by omega), h.eq0R]; rfl
    · rw [irEnv_mem _ _ _ _ (by omega), h.m1]; rfl
    · rw [irEnv_vn, h.cert]; rfl
    · rw [irEnv_vn, h.xBc]; rfl
    · rw [irEnv_vn, h.pFp]; rfl
    · rw [irEnv_vn, h.yMem]; rfl

theorem ren_mem {i : ℕ} (hi : ren i < 100000) : ∃ p ∈ irInputs, p.1 = i ∧ p.2 = ren i := by
  unfold ren at hi ⊢
  cases hf : irInputs.find? (·.1 = i) with
  | none => rw [hf] at hi; simp at hi
  | some p =>
    refine ⟨p, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, ?_⟩
    simp

theorem ren_reads (h : IRReads rd σ v) (i : ℕ) (hi : ren i < 10010) :
    irEnv rd σ i = envOf v (ren i) := by
  obtain ⟨p, hp, h1, h2⟩ := ren_mem (i := i) (by omega)
  rw [← h2, ← h1]
  exact agree_reads h p hp (h2 ▸ hi)

theorem ren_all (h : IRAgree rd σ v) (i : ℕ) (hi : ren i < 20000) :
    irEnv rd σ i = envOf v (ren i) := by
  obtain ⟨p, hp, h1, h2⟩ := ren_mem (i := i) (by omega)
  rw [← h2, ← h1]
  exact agree_all h p hp

/-- An output's value, from its check: at the section's reads, below `10010`. -/
theorem out_evalP (cut : ℕ → Bool) (hA : ∀ a, Stmt.atom a ∈ linkSec → a.Holds rd σ)
    (h : IRReads rd σ v) {n : ℕ} {g : Ex} (hok : outOk 10010 (execStmts cut linkSec .nil) n g) :
    σ (.n n) = g.eval (envOf v) := by
  rw [exec_eval cut hA n, eval_congr (ρ' := envOf v ∘ ren) (fun i hi ↦ ren_reads h i (by simpa using hi))
    _ hok.1, ← eval_rename, eval_eq_of_norm hok.2]

/-- An output's value, from its check: at every input. -/
theorem out_evalR (cut : ℕ → Bool) (hA : ∀ a, Stmt.atom a ∈ linkSec → a.Holds rd σ)
    (h : IRAgree rd σ v) {n : ℕ} {g : Ex} (hok : outOk 20000 (execStmts cut linkSec .nil) n g) :
    σ (.n n) = g.eval (envOf v) := by
  rw [exec_eval cut hA n, eval_congr (ρ' := envOf v ∘ ren) (fun i hi ↦ ren_all h i (by simpa using hi))
    _ hok.1, ← eval_rename, eval_eq_of_norm hok.2]

end

/-- **The link section's program side**: on a valuation satisfying `linkSec`'s atoms, at inputs
`v` that the section's reads hold (`IRReads`), the index side's claim, the program side, `y_mem`,
`x_bc` and `p_fp` are the guest's functions at `v`. -/
def LinkSecProgram : Prop :=
  ∀ (rd : Reader) (σ : Val) (v : LinkIn E), (∀ a, Stmt.atom a ∈ linkSec → a.Holds rd σ) →
    IRReads rd σ v →
    σ (.n 764) = gClaim v ∧ σ (.n 967) = (gProgram v).1 ∧ σ (.n 1044) = (gProgram v).2 ∧
    σ (.n 1049) = gYMem v ∧ σ (.n 1057) = gXBc v ∧ σ (.n 1058) = gPFp v

theorem linkSecProgram : LinkSecProgram := by
  intro rd σ v hA h
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := secP_norm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [out_evalP (fun _ ↦ false) hA h p1, ← gClaim_eval]
  · rw [out_evalP (fun _ ↦ false) hA h p2, ← gProgram_eval1]
  · rw [out_evalP (fun _ ↦ false) hA h p3, ← gProgram_eval2]
  · rw [out_evalP (fun _ ↦ false) hA h p4, ← gYMem_eval]
  · rw [out_evalP (fun _ ↦ false) hA h p5, ← gXBc_eval]
  · rw [out_evalP (fun _ ↦ false) hA h p6, ← gPFp_eval]

/-- **The link section computes the guest's functions**: on a valuation satisfying `linkSec`'s
atoms, at inputs `v` that the section's reads and its `y_mem`, `x_bc`, `p_fp` hold (`IRAgree`),
`coef`, `base`, `rest`, `cert_w`, `cert_w·cert` and the shift coefficients stored at `shifts` are
the guest's functions at `v`. -/
def LinkSecRow : Prop :=
  ∀ (rd : Reader) (σ : Val) (v : LinkIn E), (∀ a, Stmt.atom a ∈ linkSec → a.Holds rd σ) →
    IRAgree rd σ v →
    σ (.n 2846) = gCoef v ∧ σ (.n 2655) = gBase v ∧ σ (.n 2890) = gRest v ∧
    σ (.n 2733) = gCertW v ∧ σ (.n 2891) = gCertW v * v.cert ∧
    ∀ s < 12, rdw rd (σ (.n 19)) s = gShift v s

theorem linkSecRow : LinkSecRow := by
  intro rd σ v hA h
  obtain ⟨b1, b2⟩ := secR_base
  obtain ⟨c1, c2⟩ := secR_cert
  refine ⟨?_, ?_, ?_, ?_, ?_, fun s hs ↦ ?_⟩
  · rw [out_evalR (fun n ↦ n = 1049 || n = 1057 || n = 1058) hA h secR_coef, ← gCoef_eval]
  · rw [out_evalR (fun n ↦ n = 1049 || n = 1057 || n = 1058) hA h b1, ← gBase_eval]
  · rw [out_evalR (fun n ↦ n = 1049 || n = 1057 || n = 1058) hA h b2, ← gRest_eval]
  · rw [out_evalR (fun n ↦ n = 1049 || n = 1057 || n = 1058) hA h c1, ← gCertW_eval]
  · rw [out_evalR (fun n ↦ n = 1049 || n = 1057 || n = 1058) hA h c2, Ex.eval_mul', ← gCertW_eval]
    rfl
  · obtain ⟨hat, hok⟩ := secR_shifts s hs
    have hl : LoadHolds rd (σ (.n 19)) s (σ (.n (shiftStores.getD s (0, 0)).2)) :=
      hA _ (mem_of_atomAt hat)
    rw [rdw, hl.2, Option.getD_some,
      out_evalR (fun n ↦ n = 1049 || n = 1057 || n = 1058) hA h hok, ← gShift_eval v s hs]

end

end LeanVM.Guest.B1.Link.Arith
