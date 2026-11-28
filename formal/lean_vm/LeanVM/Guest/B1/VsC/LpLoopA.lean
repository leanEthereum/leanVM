/-
  LeanVM.Guest.B1.VsC.LpLoopA

  `level_positions`' loop completes placed, each iteration's decode by `QwA`.
-/

module

public import LeanVM.Guest.B1.VsC.LpA
public import LeanVM.Guest.B1.VsC.LrA
public import LeanVM.Guest.B1.Whir.SqLoop
public import LeanVM.Guest.Complete.ComposeL
public import LeanVM.Guest.B1.VsC.FreeBlock

/-!
# `level_positions`' loop, placed

Iteration `j` (`x = g^j`, `1 ≤ j < S`) of `level_positions__L{d}_L{cd}`'s loop reads row `j` of the
squeeze run `sqz` (the capacity after `j - 1` squeezes, `lpRow`), squeezes once (its `KECCAK`),
stores the next capacity in row `j + 1`, and decodes the squeezed word with `decode_query_windows`
at the iteration's cursor; then calls itself at `g^(j + 1)` unless `j + 1 = S`.

Its valuation is the forward evaluation (`fwdVal`) on the reader `rdOf` holding row `j` alone,
so it is fixed before the memory; every atom but the loads reads no memory, and the loads read
rows `j` and `j + 1`, which every memory the iteration runs on holds (`LpLPre`).

* `lpLChecks`: the kernel's facts about the template at `d, cd` (`LpTable.lean`).
* `lpL_vals`: the values the template's atoms define, from the guest stream's lemmas.
* `lpL_step`, `lpL_complete`: iteration `j` completes placed (`CallAtA`), its decodes' frames
  `lpF` from its cursor, by `callAtA_nodeL`, its decode by `QwA`, its tail by induction.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.Value LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## A reader holding a run -/

/-- The reader holding the words `L` from index `b`, and nothing else. -/
noncomputable def rdOf (b : ℕ) (L : List E) : Reader := fun A =>
  if h : ∃ n, n < L.length ∧ A = addressOfIndex (b + n) then some (L.getD (Classical.choose h) 0) else none

theorem rdOf_at {b : ℕ} {L : List E} (hL : L.length < 2 ^ 64 - 1) {n : ℕ} (hn : n < L.length) :
    rdOf b L (addressOfIndex (b + n)) = some (L.getD n 0) := by
  have h : ∃ m, m < L.length ∧ addressOfIndex (b + n) = addressOfIndex (b + m) := ⟨n, hn, rfl⟩
  unfold rdOf
  split_ifs
  obtain ⟨hm, e⟩ := Classical.choose_spec h
  rw [← addressOfIndex_add_inj (lt_trans hn hL) (lt_trans hm hL) e]

theorem rdAt_rdOf {b : ℕ} {L : List E} (hL : L.length < 2 ^ 64 - 1) {n : ℕ} (hn : n < L.length) :
    rdAt (rdOf b L) (ptrAt b) n = L.getD n 0 := by
  unfold rdAt
  simp only [ptrAt, Main.addr_ofK]
  rw [rdOf_at hL hn]
  rfl

/-! ## The squeeze run -/

/-- Row `k` of `level_positions`' squeeze run: the capacity after `k - 1` squeezes (row `0`, which
nothing reads, the first). -/
def lpRow (fsv : List E) (k : ℕ) : List E := ((⟨fsv, []⟩ : Fs).squeezeN (k - 1)).2.cap

/-- The squeeze run's `5(S + 1)` words. -/
def lpSqz (fsv : List E) (S : ℕ) : List E :=
  (List.range (5 * (S + 1))).map fun n => (lpRow fsv (n / 5)).getD (n % 5) 0

theorem lpRow_length {fsv : List E} (h : fsv.length = 5) (k : ℕ) : (lpRow fsv k).length = 5 := by
  unfold lpRow
  rcases hk : k - 1 with _ | n
  · simpa [Fs.squeezeN] using h
  · rw [squeezeN_snoc]; simp [Fs.squeeze, capOf]

theorem lpSqz_length (fsv : List E) (S : ℕ) : (lpSqz fsv S).length = 5 * (S + 1) := by simp [lpSqz]

theorem lpSqz_load {rd : Reader} {fsv : List E} {S c k i : ℕ} (h : ReadsAt rd (ptrAt c) (lpSqz fsv S))
    (hk : k ≤ S) (hi : i < 5) : LoadHolds rd (ptrAt (c + 5 * k)) i ((lpRow fsv k).getD i 0) := by
  have hlt : 5 * k + i < (lpSqz fsv S).length := by rw [lpSqz_length]; omega
  have := h (5 * k + i) hlt
  rw [loadHolds_ptrAt_add]
  simp only [lpSqz, List.getElem_map, List.getElem_range] at this
  have e1 : (5 * k + i) / 5 = k := by omega
  have e2 : (5 * k + i) % 5 = i := by omega
  rwa [e1, e2] at this

/-- Row `j` is the sponge after `j - 1` squeezes. -/
theorem lpRow_fs (fsv : List E) (j : ℕ) :
    (⟨lpRow fsv j, []⟩ : Fs) = ((⟨fsv, []⟩ : Fs).squeezeN (j - 1)).2 :=
  (fs_mk_eq rfl (squeezeN_pend rfl _)).symm

/-- Row `j + 1` is row `j`'s squeeze, for `1 ≤ j`. -/
theorem lpRow_succ (fsv : List E) {j : ℕ} (hj : 1 ≤ j) :
    lpRow fsv (j + 1) = (⟨lpRow fsv j, []⟩ : Fs).squeeze.2.cap := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [lpRow_fs]
  simp only [lpRow, Nat.add_sub_cancel, squeezeN_snoc]

/-- Sample `j ≥ 1` is row `j`'s squeeze. -/
theorem sqSample_row (w0 : E) (fsv : List E) {j : ℕ} (hj : 1 ≤ j) :
    sqSample w0 fsv j = (⟨lpRow fsv j, []⟩ : Fs).squeeze.1 := by
  rw [lpRow_fs]
  simp [sqSample, show j ≠ 0 by omega]

/-! ## The loop's template -/

/-- The atoms that read no memory. -/
def lpPure : Atom → Bool
  | .const .. | .add .. | .mul .. | .copy .. | .keccak .. => true
  | _ => false

/-- A load. -/
def lpIsLoad : Atom → Bool
  | .load .. => true
  | _ => false

theorem lpPure_holds {rd rd' : Reader} {σ : Val} {a : Atom} (h : lpPure a = true) :
    a.Holds rd σ → a.Holds rd' σ := by
  cases a <;> simp [lpPure] at h <;> exact id

/-- A statement's load. -/
def loadS : Stmt → Option (V × V × ℕ)
  | .atom (.load d p o) => some (d, p, o)
  | _ => none

theorem mem_of_loadS {L : List Stmt} {d p : V} {o : ℕ} (h : (d, p, o) ∈ L.filterMap loadS) :
    Stmt.atom (.load d p o) ∈ L := by
  obtain ⟨s, hs, e⟩ := List.mem_filterMap.mp h
  cases s with
  | atom a =>
    cases a with
    | load d' p' o' =>
      simp only [loadS, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      exact hs
    | _ => simp [loadS] at e
  | _ => simp [loadS] at e

/-- The first value after the decode's pointers' powers: the positions' pointer `positions·x^P`. -/
def lpK (d : ℕ) : ℕ := 33 + osPowLen (128 / d)

/-- The loop's body before its return. -/
def lpLPre (d cd : ℕ) (loop : String) : List Stmt :=
  sqLoopA (lpLv d cd) ++ osLoopTailA (sqLoopE (lpLv d cd)) ++
    [.callIf (.n (sqLoopE (lpLv d cd) + 2)) loop
      (.n (sqLoopE (lpLv d cd) + 4) :: (List.range (6 - 1)).map fun i ↦ .n (i + 1))]

theorem lpLoopBody_eq (d cd : ℕ) (loop : String) : lpLoopBody d cd loop = lpLPre d cd loop ++ [.ret []] := by
  rw [lpLoopBody, sqLoopBody_split]
  simp only [lpLPre, List.append_assoc, List.cons_append, List.nil_append]

theorem lpLv_posOff (d cd : ℕ) : (lpLv d cd).posOff = 0 := rfl

theorem lpLv_depth (d cd : ℕ) : (lpLv d cd).depth = d := rfl

theorem lpE_eq (d cd : ℕ) : sqLoopE (lpLv d cd) = lpK d + 2 := by
  simp only [sqLoopE, osMat, lpLv_posOff, lpLv_depth, ↓reduceIte, lpK]

/-- The loads of the loop's body: row `j`'s five words, then the five stores of row `j + 1`. -/
def lpLoads : List (V × V × ℕ) :=
  ((List.range 5).map fun i => (V.n (10 + i), V.n 9, i)) ++ (List.range 5).map fun i => (V.n (28 + i), V.n 9, 5 + i)

/-- The loop body's stores: row `j + 1`. -/
def lpStores : List Atom := (List.range 5).map fun i => Atom.load (.n (28 + i)) (.n 9) (5 + i)

/-- **The kernel's facts about the loop's template** at `d, cd`. -/
def lpLChecks (d cd : ℕ) (loop : String) : Bool :=
  (chk 6 (lpLoopBody d cd loop)).isSome && (lpLPre d cd loop).all Stmt.straight &&
    (lpLPre d cd loop).all (fun s => match s with
      | .atom a => lpIsLoad a || (lpPure a && !needsSide a)
      | _ => true) &&
    decide ((lpLPre d cd loop).filterMap loadS = lpLoads) &&
    decide (storesOf 6 (lpLoopBody d cd loop) = lpStores) &&
    decide ((lpLPre d cd loop).filterMap Stmt.allocSz = []) &&
    decide ((lpLPre d cd loop).filterMap Stmt.addrS = []) &&
    decide ((lpLPre d cd loop).filterMap Stmt.callS =
      [(none, dqwName d cd, [.n 20, .n (lpK d), .n (lpK d + 1), .n 5], []),
        (some (.n (lpK d + 4)), loop, [.n (lpK d + 6), .n 1, .n 2, .n 3, .n 4, .n 5], [])]) &&
    decide (digitsVal (osPowDigits (128 / d)) 1 = 128 / d)

/-! ## The template's values -/

theorem osPowSteps_pure (x : ℕ) : ∀ (ds : List Bool) (acc k : ℕ),
    ∀ s ∈ (osPowSteps x ds acc k).1, ∃ a, s = .atom a ∧ lpPure a = true
  | [], _, _ => by simp [osPowSteps]
  | b :: ds, acc, k => by
    intro s hs
    cases b with
    | true =>
      simp only [osPowSteps, ↓reduceIte, List.mem_cons] at hs
      rcases hs with rfl | rfl | hs
      · exact ⟨_, rfl, rfl⟩
      · exact ⟨_, rfl, rfl⟩
      · exact osPowSteps_pure x ds _ _ s hs
    | false =>
      simp only [osPowSteps, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact ⟨_, rfl, rfl⟩
      · exact osPowSteps_pure x ds _ _ s hs

theorem allOk_of_pure {C : CallRel} {rd : Reader} {σ : Val} {L M : List Stmt}
    (hsub : ∀ s ∈ L, s ∈ M) (hp : ∀ s ∈ L, ∃ a, s = .atom a ∧ lpPure a = true)
    (hA : ∀ a, Stmt.atom a ∈ M → lpPure a = true → a.Holds rd σ) : AllOk C rd σ L := by
  intro s hs
  obtain ⟨a, rfl, ha⟩ := hp s hs
  exact hA a (hsub _ hs) ha

theorem lpL_mem_pw {d cd : ℕ} {loop : String} {s : Stmt}
    (h : s ∈ (osPowSteps 0 (osPowDigits (128 / d)) 0 33).1) : s ∈ lpLPre d cd loop := by
  simp only [lpLPre, sqLoopA, lpLv_depth, List.mem_append]
  tauto

/-- `x^5` reaches the row: `row = sqz·x^5`. -/
theorem lpL_row {d cd : ℕ} {loop : String} {rd : Reader} {σ : Val}
    (hA : ∀ a, Stmt.atom a ∈ lpLPre d cd loop → lpPure a = true → a.Holds rd σ) :
    σ (.n 9) = σ (.n 2) * σ (.n 0) ^ 5 := by
  have m6 := hA (.mul (.n 6) (.n 0) (.n 0)) (by simp [lpLPre, sqLoopA, osMul]) rfl
  have m7 := hA (.mul (.n 7) (.n 6) (.n 6)) (by simp [lpLPre, sqLoopA, osMul]) rfl
  have m8 := hA (.mul (.n 8) (.n 7) (.n 0)) (by simp [lpLPre, sqLoopA, osMul]) rfl
  have m9 := hA (.mul (.n 9) (.n 2) (.n 8)) (by simp [lpLPre, sqLoopA, osMul]) rfl
  simp only [holds_mul] at m6 m7 m8 m9
  rw [m9, m8, m7, m6]; ring

/-- **The values the loop's atoms define**, from row `j` at `10 ..= 14`: the squeezed word, the next
capacity, the decode's pointers and the tail's words. -/
theorem lpL_vals {d cd : ℕ} {loop : String} {rd : Reader} {σ : Val}
    (hpw : digitsVal (osPowDigits (128 / d)) 1 = 128 / d)
    (hA : ∀ a, Stmt.atom a ∈ lpLPre d cd loop → lpPure a = true → a.Holds rd σ)
    {row : List E} (hrow : row.length = 5) (hld : ∀ i < 5, σ (.n (10 + i)) = row.getD i 0) :
    σ (.n 20) = (⟨row, []⟩ : Fs).squeeze.1 ∧
    (∀ i < 5, σ (.n (28 + i)) = (⟨row, []⟩ : Fs).squeeze.2.cap.getD i 0) ∧
    σ (.n (lpK d)) = σ (.n 3) * σ (.n 0) ^ (128 / d) ∧
    σ (.n (lpK d + 1)) = σ (.n 4) * σ (.n 0) ^ (128 / d) ∧
    σ (.n (lpK d + 4)) = σ (.n 0) * gen + σ (.n 1) ∧ σ (.n (lpK d + 6)) = σ (.n 0) * gen := by
  obtain ⟨r0, r1, r2, r3, r4, rfl⟩ : ∃ r0 r1 r2 r3 r4, row = [r0, r1, r2, r3, r4] := by
    match row, hrow with
    | [a, b, c, e, f], _ => exact ⟨a, b, c, e, f, rfl⟩
  have l0 : σ (.n 10) = r0 := by simpa using hld 0 (by decide)
  have l1 : σ (.n 11) = r1 := by simpa using hld 1 (by decide)
  have l2 : σ (.n 12) = r2 := by simpa using hld 2 (by decide)
  have l3 : σ (.n 13) = r3 := by simpa using hld 3 (by decide)
  have l4 : σ (.n 14) = r4 := by simpa using hld 4 (by decide)
  have c16 := hA (.const (.n 16) (word 0 0)) (by simp [lpLPre, sqLoopA, osCst]) rfl
  have c17 := hA (.const (.n 17) (word 0 0)) (by simp [lpLPre, sqLoopA, osCst]) rfl
  have c18 := hA (.const (.n 18) (word 0 0)) (by simp [lpLPre, sqLoopA, osCst]) rfl
  have c19 := hA (.const (.n 19) (word 0 0)) (by simp [lpLPre, sqLoopA, osCst]) rfl
  simp only [holds_const] at c16 c17 c18 c19
  have hK := hA (.keccak ([16, 16, 16, 16, 16, 17, 18, 19, 10, 11, 12, 13, 14].map V.n) (osRun 20 13) false false)
    (by simp [lpLPre, sqLoopA, osKeccak]) rfl
  have hout := keccakA_fs (s := (⟨[r0, r1, r2, r3, r4], []⟩ : Fs)) hK (by simp) (by
    simp [pendCells, c16, c17, c18, c19, l0, l1, l2, l3, l4, word_zero])
  have e : ∀ c (hc : c < 13), σ (.n (20 + c)) = cellsOfState (⟨[r0, r1, r2, r3, r4], []⟩ : Fs).perm false ⟨c, hc⟩ :=
    fun c hc ↦ by simpa [osRun] using outs_eq hout ⟨c, hc⟩ (by simp [osRun, hc])
  have hpwv := osPowSteps_val (C := fun _ _ _ => True) (rd := rd) (σ := σ) 0 (osPowDigits (128 / d)) 0 33 1
    (by rw [pow_one]) (allOk_of_pure (fun s hs => lpL_mem_pw hs) (osPowSteps_pure 0 _ _ _) hA)
  rw [hpw] at hpwv
  have hm1 := hA (.mul (.n (lpK d)) (.n 3) (.n (osPowSteps 0 (osPowDigits (128 / d)) 0 33).2))
    (by simp [lpLPre, sqLoopA, osMat, osMul, lpLv_posOff, lpLv_depth, lpK]) rfl
  have hm2 := hA (.mul (.n (lpK d + 1)) (.n 4) (.n (osPowSteps 0 (osPowDigits (128 / d)) 0 33).2))
    (by simp [lpLPre, sqLoopA, osMat, osMul, lpLv_posOff, lpLv_depth, lpK]) rfl
  simp only [holds_mul] at hm1 hm2
  have ht := osLoopTailA_val (C := fun _ _ _ => True) (rd := rd) (σ := σ) (k := lpK d + 2)
    (allOk_of_pure (M := lpLPre d cd loop) (fun s hs => by
        simp only [lpLPre, lpE_eq, List.mem_append]; tauto)
      (fun s hs => by
        simp only [osLoopTailA, osCst, osMul, osAdd, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩) hA)
  refine ⟨?_, fun i hi => ?_, by rw [hm1, hpwv], by rw [hm2, hpwv], ht.1, ht.2⟩
  · rw [Fs.squeeze, Keccak.challengeOf_cells]; exact e 0 (by decide)
  · have := e (8 + i) (by omega)
    rw [show 20 + (8 + i) = 28 + i by omega] at this
    rw [this]
    interval_cases i <;> rfl

/-! ## The iterations -/

/-- Decode `k`'s frame, from iteration `j`'s cursor `c`. -/
def lpF (fs : String → ℕ) (al : String → Bool) (dq : String) (c j k : ℕ) : ℕ :=
  allocBase (al dq) ((lpDqStep fs al dq)^[k - j] c)

theorem lpF_self (fs : String → ℕ) (al : String → Bool) (dq : String) (c j : ℕ) :
    lpF fs al dq c j j = allocBase (al dq) c := by simp [lpF]

theorem lpF_succ (fs : String → ℕ) (al : String → Bool) (dq : String) {c j k : ℕ} (h : j < k) :
    lpF fs al dq (lpDqStep fs al dq c) (j + 1) k = lpF fs al dq c j k := by
  unfold lpF
  rw [show k - j = (k - (j + 1)) + 1 by omega, Function.iterate_succ_apply]

theorem lpB_succ (fs : String → ℕ) (loop : String) {S j : ℕ} (h : j < S) :
    lpB fs loop S j = fs loop + lpB fs loop S (j + 1) := by
  unfold lpB
  rw [show S - j = (S - (j + 1)) + 1 by omega, Nat.add_mul, one_mul]
  omega

theorem le_lpDqStep (fs : String → ℕ) (al : String → Bool) (dq : String) (c : ℕ) : c ≤ lpDqStep fs al dq c :=
  le_trans (le_allocBase _ c) (Nat.le_add_right _ _)

/-- Iteration `j`'s arguments. -/
def lpLArgs (j S isqz ipos iptr it : ℕ) : List E :=
  [gen ^ j, gen ^ S, ptrAt isqz, ptrAt ipos, ptrAt iptr, ptrAt it]

/-- The cells the loop reads: the squeeze run, the positions and pointers, the window tables. -/
def LpLReg (S P isqz ipos iptr it : ℕ) (R : ℕ → Prop) : Prop :=
  (∀ n < 5 * (S + 1), R (isqz + n)) ∧ (∀ k < S * P, R (ipos + k)) ∧ (∀ k < S * P, R (iptr + k)) ∧
    ∀ n < 128, R (it + n)

variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ)

/-- What iteration `j` at cursor `c` reads: the window tables, the squeeze run, and for each
iteration from `j` on, its honest positions and its decode's window pointers. -/
def LpLPre (d cd S isqz ipos iptr it : ℕ) (w0 : E) (fsv : List E) (c j : ℕ) (rd : Reader) : Prop :=
  WinTabs rd (ptrAt it) ∧ ReadsAt rd (ptrAt isqz) (lpSqz fsv S) ∧
    ∀ k, j ≤ k → k < S →
      ReadsAt rd (ptrAt (ipos + k * (128 / d)))
          ((List.range (128 / d)).map fun i => eOfNat (qwPosOf d (sqSample w0 fsv k) i)) ∧
        ReadsAt rd (ptrAt (iptr + k * (128 / d)))
          ((List.range (128 / d)).map fun i => ptrAt (lpF fs al (dqwName d cd) c j k + cert (dqwName d cd) (.n 5) + i * qwN d cd))

/-- The windows iteration `j` at cursor `c` and the later ones claim. -/
def LpLD (d cd S c j : ℕ) (i : ℕ) : Prop :=
  ∃ k, j ≤ k ∧ k < S ∧ lpF fs al (dqwName d cd) c j k + cert (dqwName d cd) (.n 5) ≤ i ∧
    i < lpF fs al (dqwName d cd) c j k + cert (dqwName d cd) (.n 5) + 128 / d * qwN d cd

/-- The windows iteration `j` at cursor `c` and the later ones hold. -/
def LpLOut (d cd S : ℕ) (w0 : E) (fsv : List E) (c j : ℕ) (rd : Reader) : Prop :=
  ∀ k, j ≤ k → k < S → ReadsAt rd (ptrAt (lpF fs al (dqwName d cd) c j k + cert (dqwName d cd) (.n 5)))
    (qwRunList d cd (sqSample w0 fsv k))

/-- What iteration `j` of the loop gives. -/
def LpLA (kd : ℕ) (loop : String) (d cd S isqz ipos iptr it : ℕ) (w0 : E) (fsv : List E) (R : ℕ → Prop) (j : ℕ) :
    Prop :=
  ∀ fp c, fp + lpB fs loop S j ≤ c →
    CallAtA fs al cert kd loop (lpLArgs j S isqz ipos iptr it) [] R (LpLD fs al cert d cd S c j)
      (LpLOut fs al cert d cd S w0 fsv c j) (LpLPre fs al cert d cd S isqz ipos iptr it w0 fsv c j) PostQuiet
      (lpB fs loop S j) fp c ((lpDqStep fs al (dqwName d cd))^[S - j] c)

variable {fs al cert}

theorem ns_of_check {a : Atom} (h : (lpIsLoad a || (lpPure a && !needsSide a)) = true) (hp : lpPure a = true) :
    needsSide a = false := by
  cases a <;> simp_all [lpIsLoad, lpPure]

theorem hintAddrs_of_check {σ : Val} {a : Atom} (h : (lpIsLoad a || (lpPure a && !needsSide a)) = true) :
    Ev.hintAddrs σ (.atom a) = [] := by
  cases a <;> simp_all [lpIsLoad, lpPure, Ev.hintAddrs]

theorem quiet_of_check {a : Atom} (h : (lpIsLoad a || (lpPure a && !needsSide a)) = true) : atomQuiet a = true := by
  cases a <;> simp_all [lpIsLoad, lpPure, atomQuiet]

theorem triv_of_check {a : Atom} (h : (lpIsLoad a || (lpPure a && !needsSide a)) = true) : trivExact a = true := by
  cases a <;> simp_all [lpIsLoad, lpPure, trivExact]

/-- **Iteration `j` of `level_positions`' loop completes placed**, given the next one. -/
theorem lpL_step {kd d cd S : ℕ} {loop : String} {fn : Fn} (hfind : coreProgram.find? loop = some fn)
    (hpar : fn.params = osParams 6) (hbody : fn.body = lpLoopBody d cd loop) (hck : lpLChecks d cd loop = true)
    (hqw : QwA fs al cert kd (dqwName d cd) d cd) (hkd : 7 ≤ kd) (hS : S < 2 ^ 20)
    {fsv : List E} (hfsv : fsv.length = 5) (w0 : E) {isqz ipos iptr it : ℕ} {R : ℕ → Prop}
    (hR : LpLReg S (128 / d) isqz ipos iptr it R) {j : ℕ} (hj1 : 1 ≤ j) (hjS : j < S)
    (hnext : j + 1 < S → LpLA fs al cert kd loop d cd S isqz ipos iptr it w0 fsv R (j + 1)) :
    LpLA fs al cert kd loop d cd S isqz ipos iptr it w0 fsv R j := by
  intro fp c hfc
  simp only [lpLChecks, Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hchk, hstr⟩, hat⟩, hlds⟩, hst⟩, hal⟩, had⟩, hcs⟩, hpw⟩ := hck
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hchk
  set args := lpLArgs j S isqz ipos iptr it with hargs
  set row := lpRow fsv j with hrowd
  have hrow : row.length = 5 := lpRow_length hfsv j
  set rdH : Reader := rdOf (isqz + 5 * j) row with hrdH
  have hchk' : chk args.length fn.body = some c' := by rw [hbody]; exact hc'
  set σ := fwdVal rdH (fun _ => 0) args fn.body with hσ
  have hpre : fn.body = lpLPre d cd loop ++ [.ret []] := by rw [hbody, lpLoopBody_eq]
  have hmem : ∀ s ∈ lpLPre d cd loop, s ∈ fn.body := fun s hs => by rw [hpre]; exact List.mem_append_left _ hs
  have hatc : ∀ a, Stmt.atom a ∈ lpLPre d cd loop → (lpIsLoad a || (lpPure a && !needsSide a)) = true :=
    fun a ha => List.all_eq_true.mp hat _ ha
  -- the parameters
  have hp : ∀ i < 6, σ (.n i) = args.getD i 0 := fun i hi => fwd_param hchk' (by simpa [hargs, lpLArgs] using hi)
  have p0 : σ (.n 0) = gen ^ j := hp 0 (by decide)
  have p1 : σ (.n 1) = gen ^ S := hp 1 (by decide)
  have p2 : σ (.n 2) = ptrAt isqz := hp 2 (by decide)
  have p3 : σ (.n 3) = ptrAt ipos := hp 3 (by decide)
  have p4 : σ (.n 4) = ptrAt iptr := hp 4 (by decide)
  have p5 : σ (.n 5) = ptrAt it := hp 5 (by decide)
  -- the atoms that read no memory hold on every memory
  have hpure : ∀ a, Stmt.atom a ∈ lpLPre d cd loop → lpPure a = true → ∀ rd, a.Holds rd σ :=
    fun a ha hpa rd => lpPure_holds hpa
      (fwd_holds_noSide (rd := rdH) (w := fun _ => 0) hchk' (hmem _ ha) (ns_of_check (hatc a ha) hpa))
  have h9 : σ (.n 9) = ptrAt (isqz + 5 * j) := by
    rw [lpL_row (fun a ha hpa => hpure a ha hpa rdH), p2, p0, ← pow_mul, ptrAt_mul_gen, mul_comm j 5]
  -- row `j`
  have hS' : storesOf args.length fn.body = lpStores := by rw [hbody]; exact hst
  have hl : ∀ i < 5, σ (.n (10 + i)) = row.getD i 0 := by
    intro i hi
    have hm : Stmt.atom (.load (.n (10 + i)) (.n 9) i) ∈ fn.body :=
      hmem _ (mem_of_loadS (by
        rw [hlds]; exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))
    have hg := fwd_good (rd := rdH) (w := fun _ => 0) hchk' _ hm
    simp only [Good] at hg
    rcases hg with hg | hg
    · exfalso
      rw [hS'] at hg
      obtain ⟨a, -, h⟩ := List.mem_map.mp hg
      have := congrArg (fun x : Atom => match x with | .load _ _ o => o | _ => 0) h
      simp only at this
      omega
    · rw [← hσ] at hg
      rw [hg, h9]
      exact rdAt_rdOf (by rw [hrow]; norm_num) (by rw [hrow]; exact hi)
  obtain ⟨e20, e28, ek, ek1, ek4, ek6⟩ :=
    lpL_vals hpw (fun a ha hpa => hpure a ha hpa rdH) hrow hl
  have hsamp : σ (.n 20) = sqSample w0 fsv j := by rw [e20, sqSample_row w0 fsv hj1]
  have hnextRow : ∀ i < 5, σ (.n (28 + i)) = (lpRow fsv (j + 1)).getD i 0 := by
    intro i hi; rw [e28 i hi, lpRow_succ fsv hj1]
  have hk : σ (.n (lpK d)) = ptrAt (ipos + j * (128 / d)) := by rw [ek, p3, p0, ← pow_mul, ptrAt_mul_gen]
  have hk1 : σ (.n (lpK d + 1)) = ptrAt (iptr + j * (128 / d)) := by rw [ek1, p4, p0, ← pow_mul, ptrAt_mul_gen]
  have hk4 : σ (.n (lpK d + 4)) = gen ^ (j + 1) + gen ^ S := by rw [ek4, p0, p1, pow_succ]
  have hk6 : σ (.n (lpK d + 6)) = gen ^ (j + 1) := by rw [ek6, p0, pow_succ]
  -- the path
  obtain ⟨es, hes⟩ : ∃ es, es = (lpLPre d cd loop).flatMap (slEvs σ) := ⟨_, rfl⟩
  have hw : walk σ fn.body = .ret es [] := by rw [hpre, hes]; exact walk_straight σ _ _ hstr
  have hparts := straight_parts σ _ hstr
  have hal0 : allocs σ es = [] := by rw [hes, hparts.2.1, hal]; rfl
  have hcalls : calls es = [⟨(dqwName d cd), [.n 20, .n (lpK d), .n (lpK d + 1), .n 5], [], true⟩,
      ⟨loop, [.n (lpK d + 6), .n 1, .n 2, .n 3, .n 4, .n 5], [], decide (σ (.n (lpK d + 4)) ≠ 0)⟩] := by
    rw [hes, hparts.2.2.2, hcs]; rfl
  have hlflag : coreProgram.loop loop = true := by
    have hn : fn.name = loop := by simpa using List.find?_some hfind
    rw [Program.loop_of_find? hfind, Fn.loop, hpre]
    simp [lpLPre, List.reverse_append, hn]
  -- the region and the decodes
  have hRpos : ∀ i < 128 / d, R (ipos + j * (128 / d) + i) := fun i hi => by
    rw [Nat.add_assoc]; exact hR.2.1 _ (by nlinarith)
  have hRptr : ∀ i < 128 / d, R (iptr + j * (128 / d) + i) := fun i hi => by
    rw [Nat.add_assoc]; exact hR.2.2.1 _ (by nlinarith)
  have hdq : CallAtA fs al cert kd (dqwName d cd) ([V.n 20, .n (lpK d), .n (lpK d + 1), .n 5].map σ) (([] : List V).map σ) R
      (fun i => allocBase (al (dqwName d cd)) c + cert (dqwName d cd) (.n 5) ≤ i ∧ i < allocBase (al (dqwName d cd)) c + cert (dqwName d cd) (.n 5) + 128 / d * qwN d cd)
      (fun rd => ReadsAt rd (ptrAt (allocBase (al (dqwName d cd)) c + cert (dqwName d cd) (.n 5))) (qwRunList d cd (sqSample w0 fsv j)))
      (fun rd => LpLPre fs al cert d cd S isqz ipos iptr it w0 fsv c j rd ∧ HoldsWords rd [])
      PostQuiet (fs (dqwName d cd)) (allocBase (al (dqwName d cd)) c) (allocBase (al (dqwName d cd)) c + fs (dqwName d cd))
      (lpDqStep fs al (dqwName d cd) c) := by
    have e : [V.n 20, .n (lpK d), .n (lpK d + 1), .n 5].map σ =
        [sqSample w0 fsv j, ptrAt (ipos + j * (128 / d)), ptrAt (iptr + j * (128 / d)), ptrAt it] := by
      simp [hsamp, hk, hk1, p5]
    rw [e]
    refine (hqw (sqSample w0 fsv j) (ipos + j * (128 / d)) (iptr + j * (128 / d)) it R hkd hRpos hRptr hR.2.2.2
      (allocBase (al (dqwName d cd)) c) (allocBase (al (dqwName d cd)) c + fs (dqwName d cd))).mono
      (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun rd h => ?_) (fun _ _ _ h => h)
    obtain ⟨hwt, -, hblk⟩ := h.1
    obtain ⟨hps, hpt⟩ := hblk j le_rfl hjS
    rw [lpF_self] at hpt
    exact ⟨hwt, hps, hpt⟩
  -- the events
  have hev : ∀ rd, LpLPre fs al cert d cd S isqz ipos iptr it w0 fsv c j rd → ∀ ev ∈ es, ev.Holds rd σ := by
    intro rd hP
    rw [hes]
    refine holds_slEvs _ (fun a ha => ?_) (fun c0 f0 a0 h => ?_)
    · by_cases hld : lpIsLoad a = true
      · cases a with
        | load d0 p0' o0 =>
          have hq : (d0, p0', o0) ∈ lpLoads := by
            rw [← hlds]; exact List.mem_filterMap.mpr ⟨_, ha, rfl⟩
          simp only [lpLoads, List.mem_append, List.mem_map, List.mem_range, Prod.mk.injEq] at hq
          rw [holds_load]
          rcases hq with ⟨i, hi, rfl, rfl, rfl⟩ | ⟨i, hi, rfl, rfl, rfl⟩
          · rw [h9, hl i hi]; exact lpSqz_load hP.2.1 (by omega) hi
          · rw [h9, hnextRow i hi]
            have := lpSqz_load (k := j + 1) hP.2.1 (by omega) hi
            rwa [show isqz + 5 * (j + 1) = isqz + 5 * j + 5 by ring, loadHolds_ptrAt_add] at this
        | _ => simp [lpIsLoad] at hld
      · have hld' : lpIsLoad a = false := by simpa using hld
        have hc := hatc a ha
        simp only [hld', Bool.false_or, Bool.and_eq_true] at hc
        exact hpure a ha hc.1 rd
    · have hq : (some c0, f0, a0, ([] : List V)) ∈ (lpLPre d cd loop).filterMap Stmt.callS :=
        List.mem_filterMap.mpr ⟨_, h, rfl⟩
      rw [hcs] at hq
      have hc0 : c0 = .n (lpK d + 4) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with hq | hq
        · simp at hq
        · simp only [Prod.mk.injEq, Option.some.injEq] at hq; exact hq.1
      rw [hc0, hk4]
      exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
  -- the loads and the post
  have hlo : ∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧
      (ownData cert fp c loop (allocs σ es) es i ∨ R i ∨ LpLD fs al cert d cd S c j i) := by
    intro A hA
    rw [loadAddrs, hes, filterMap_slEvs (Ev.loadAddr? σ) σ (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)] at hA
    obtain ⟨s, hs, hsA⟩ := List.mem_filterMap.mp hA
    cases s with
    | atom a =>
      cases a with
      | load d0 p0' o0 =>
        have hq : (d0, p0', o0) ∈ lpLoads := by
          rw [← hlds]; exact List.mem_filterMap.mpr ⟨_, hs, rfl⟩
        simp only [lpLoads, List.mem_append, List.mem_map, List.mem_range, Prod.mk.injEq] at hq
        simp only [Ev.loadAddr?, Option.some.injEq] at hsA
        subst hsA
        rcases hq with ⟨i, hi, rfl, rfl, rfl⟩ | ⟨i, hi, rfl, rfl, rfl⟩
        · refine ⟨isqz + 5 * j + i, by rw [h9]; exact Main.addr_ofK _ _, Or.inr (Or.inl ?_)⟩
          rw [Nat.add_assoc]; exact hR.1 _ (by omega)
        · refine ⟨isqz + 5 * j + (5 + i), by rw [h9]; exact Main.addr_ofK _ _, Or.inr (Or.inl ?_)⟩
          rw [Nat.add_assoc]; exact hR.1 _ (by omega)
      | _ => simp [Ev.loadAddr?] at hsA
    | _ => simp at hsA
  have hhi : ∀ A ∈ heapHintAddrs σ es, ∃ i, A = addressOfIndex i ∧
      (ownData cert fp c loop (allocs σ es) es i ∨ R i ∨ LpLD fs al cert d cd S c j i) := by
    intro A hA
    rw [heapHintAddrs, hes, flatMap_slEvs (Ev.hintAddrs σ) σ (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)] at hA
    obtain ⟨s, hs, hsA⟩ := List.mem_flatMap.mp hA
    cases s with
    | atom a => simp only [hintAddrs_of_check (hatc a hs), List.not_mem_nil] at hsA
    | _ => simp at hsA
  have hq0 : ∀ a, Ev.atom a ∈ es → atomQuiet a = true := fun a ha =>
    quiet_of_check (hatc a (mem_atom_slEvs (hes ▸ ha)))
  have hx0 : ∀ rd, ∀ ev ∈ es, ev.Exact rd σ := by
    intro rd ev hev'
    cases ev with
    | atom a => exact exact_of_trivExact (triv_of_check (hatc a (mem_atom_slEvs (hes ▸ hev'))))
    | _ => trivial
  have hnode : NodeAt cert (fp, c) loop σ (allocs σ es) es := by
    rw [hal0]
    refine ⟨?_, fun q hq => ?_⟩
    · rw [hes, hparts.1, hal]; rfl
    · rw [hes, hparts.2.2.1, had] at hq; exact absurd hq List.not_mem_nil
  have hc0 : c + (allocs σ es).sum = c := by rw [hal0]; rfl
  -- the tail
  by_cases hlast : j + 1 = S
  · -- the last iteration: the tail is a phantom
    have hd4 : decide (σ (.n (lpK d + 4)) ≠ 0) = false := by
      simp only [decide_eq_false_iff_not, not_not, hk4, hlast]
      exact CharTwo.add_self_eq_zero _
    have hend : (lpDqStep fs al (dqwName d cd))^[S - j] c = lpDqStep fs al (dqwName d cd) c := by
      rw [show S - j = 1 by omega]; rfl
    have hB : lpB fs loop S j = fs loop + fs (tailKey loop) := by
      unfold lpB; rw [show S - j = 1 by omega, one_mul]
    rw [hB, hend]
    refine callAtA_nodeL (Bt := fs (tailKey loop)) hlflag (by rw [← hB]; exact hfc)
      ⟨σ, fn, es, [], [], (calls es).map fun _ => PostQuiet, LpLOut fs al cert d cd S w0 fsv c j,
        LpLD fs al cert d cd S c j, hfind, by rw [hpar]; exact fwd_params hchk', hw, rfl, hnode,
        by rw [hal0]; exact ⟨by simp, List.Pairwise.nil⟩, hlo, hhi, fun i h => Or.inr h, ?_, fun _ h => h,
        fun rd _ hP _ => hev rd hP, fun rd ts _ _ _ hv hq' => postQuiet_node hfind hw hq0 (hx0 rd) hv hq' _⟩
    rw [hc0, hcalls]
    simp only [List.map_cons, List.map_nil]
    rw [KidsAtL]
    simp only [↓reduceIte]
    refine ⟨fs (dqwName d cd), lpDqStep fs al (dqwName d cd) c, R, _, _, fun i hi => Or.inl (Or.inl hi), hdq, ?_⟩
    rw [KidsAtL]
    simp only [hd4, Bool.false_eq_true, ↓reduceIte]
    refine ⟨⟨fun v => ([V.n (lpK d + 6), .n 1, .n 2, .n 3, .n 4, .n 5].map σ).getD v.idx 0, fn, hfind, ?_⟩,
      trivial, trivial, fun rd h k hk1 hk2 => ?_, fun i hi => ?_⟩
    · rw [hpar]; exact params_range_map _
    · obtain rfl : k = j := by omega
      have := h.2; rwa [lpF_self]
    · obtain ⟨k, hk1, hk2, hi1, hi2⟩ := hi
      obtain rfl : k = j := by omega
      rw [lpF_self] at hi1 hi2
      exact Or.inr ⟨hi1, hi2⟩
  · -- the next iteration
    have hlt : j + 1 < S := by omega
    have hd4 : decide (σ (.n (lpK d + 4)) ≠ 0) = true := by
      simp only [decide_eq_true_eq, hk4]
      intro h0
      have := gen_pow_inj (by omega) (by omega) (CharTwo.add_eq_zero.mp h0)
      omega
    have hend : (lpDqStep fs al (dqwName d cd))^[S - j] c = (lpDqStep fs al (dqwName d cd))^[S - (j + 1)] (lpDqStep fs al (dqwName d cd) c) := by
      rw [show S - j = (S - (j + 1)) + 1 by omega, Function.iterate_succ_apply]
    have hB := lpB_succ fs loop hjS
    rw [hB, hend]
    have hnx := hnext hlt (fp + fs loop) (lpDqStep fs al (dqwName d cd) c) (by
      have := le_lpDqStep fs al (dqwName d cd) c; rw [hB] at hfc; omega)
    have hta : [V.n (lpK d + 6), .n 1, .n 2, .n 3, .n 4, .n 5].map σ = lpLArgs (j + 1) S isqz ipos iptr it := by
      simp [lpLArgs, hk6, p1, p2, p3, p4, p5]
    refine callAtA_nodeL (Bt := lpB fs loop S (j + 1)) hlflag (by rw [← hB]; exact hfc)
      ⟨σ, fn, es, [], [], (calls es).map fun _ => PostQuiet, LpLOut fs al cert d cd S w0 fsv c j,
        LpLD fs al cert d cd S c j, hfind, by rw [hpar]; exact fwd_params hchk', hw, rfl, hnode,
        by rw [hal0]; exact ⟨by simp, List.Pairwise.nil⟩, hlo, hhi, fun i h => Or.inr h, ?_, fun _ h => h,
        fun rd _ hP _ => hev rd hP, fun rd ts _ _ _ hv hq' => postQuiet_node hfind hw hq0 (hx0 rd) hv hq' _⟩
    rw [hc0, hcalls]
    simp only [List.map_cons, List.map_nil]
    rw [KidsAtL]
    simp only [↓reduceIte]
    refine ⟨fs (dqwName d cd), lpDqStep fs al (dqwName d cd) c, R, _, _, fun i hi => Or.inl (Or.inl hi), hdq, ?_⟩
    rw [KidsAtL]
    simp only [hd4, ↓reduceIte]
    refine ⟨R, LpLD fs al cert d cd S (lpDqStep fs al (dqwName d cd) c) (j + 1),
      LpLOut fs al cert d cd S w0 fsv (lpDqStep fs al (dqwName d cd) c) (j + 1), fun i hi => Or.inl (Or.inl hi), ?_,
      fun rd h1 h2 k hk1 hk2 => ?_, fun i hi => ?_⟩
    · rw [hta]
      refine hnx.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun rd h => ?_) (fun _ _ _ h => h)
      obtain ⟨⟨hwt, hsq, hblk⟩, -⟩ := h
      refine ⟨hwt, hsq, fun k hk1 hk2 => ?_⟩
      rw [lpF_succ fs al (dqwName d cd) (by omega)]
      exact hblk k (by omega) hk2
    · rcases Nat.eq_or_lt_of_le hk1 with rfl | hk1'
      · have := h1.2; rwa [lpF_self]
      · have := h2 k hk1' hk2; rwa [lpF_succ fs al (dqwName d cd) hk1'] at this
    · obtain ⟨k, hk1, hk2, hi1, hi2⟩ := hi
      rcases Nat.eq_or_lt_of_le hk1 with rfl | hk1'
      · rw [lpF_self] at hi1 hi2
        exact Or.inl (Or.inr ⟨hi1, hi2⟩)
      · rw [← lpF_succ fs al (dqwName d cd) hk1'] at hi1 hi2
        exact Or.inr ⟨k, hk1', hk2, hi1, hi2⟩

/-- **Every iteration of `level_positions`' loop completes placed.** -/
theorem lpL_complete {kd d cd S : ℕ} {loop : String} {fn : Fn} (hfind : coreProgram.find? loop = some fn)
    (hpar : fn.params = osParams 6) (hbody : fn.body = lpLoopBody d cd loop) (hck : lpLChecks d cd loop = true)
    (hqw : QwA fs al cert kd (dqwName d cd) d cd) (hkd : 7 ≤ kd) (hS : S < 2 ^ 20)
    {fsv : List E} (hfsv : fsv.length = 5) (w0 : E) {isqz ipos iptr it : ℕ} {R : ℕ → Prop}
    (hR : LpLReg S (128 / d) isqz ipos iptr it R) :
    ∀ n j, j + n + 1 = S → 1 ≤ j → LpLA fs al cert kd loop d cd S isqz ipos iptr it w0 fsv R j := by
  intro n
  induction n with
  | zero =>
    intro j hj h1
    exact lpL_step hfind hpar hbody hck hqw hkd hS hfsv w0 hR h1 (by omega) fun h => absurd h (by omega)
  | succ n ih =>
    intro j hj h1
    exact lpL_step hfind hpar hbody hck hqw hkd hS hfsv w0 hR h1 (by omega) fun _ => ih (j + 1) (by omega) (by omega)

end
end LeanVM.Guest.B1.VsC
