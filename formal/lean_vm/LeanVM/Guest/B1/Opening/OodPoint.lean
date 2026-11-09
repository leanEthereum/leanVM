/-
  LeanVM.Guest.B1.Opening.OodPoint

  B1 for `opening_ood_point`: one generic argument over the point's dimension.
-/

module

public import LeanVM.Guest.B1.Opening.Meaning
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Run

/-!
# `opening_ood_point` (G:1232-1243, TRIAGE #36)

Its body at dimension `n` (`oodBody n`): the capacity copied into `14 .. 18`, the permutation of
the rate cells `5 .. 12` and the capacity into `19 .. 31`, its challenge (`challengeT` from `32`,
at `38`) stored at `point[0]`, the pad run `39 .. 43`; then `n - 1` rounds (`oodRound x`): a
permutation with nothing waiting (the zero run) into `oodO (x + 1) .. + 12`, its challenge stored
at `point[x + 1]`; the final capacity copied and returned.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- Where round `x`'s permutation writes its thirteen cells (`0`: the first permutation). -/
def oodO : ℕ → ℕ
  | 0 => 19
  | x + 1 => 44 + 20 * x

/-- Thirteen consecutive values. -/
def run13 (b : ℕ) : List V := (List.range 13).map fun i ↦ .n (b + i)

/-- Round `x` (`1 ≤ x + 1 < n`): the permutation of the previous capacity with nothing waiting,
its challenge stored at `point[x + 1]`. -/
def oodRound (x : ℕ) : List Stmt :=
  keccakA ([.n 40, .n 40, .n 40, .n 40, .n 40, .n 41, .n 42, .n 43] ++
      [.n (oodO x + 8), .n (oodO x + 9), .n (oodO x + 10), .n (oodO x + 11), .n (oodO x + 12)])
      (run13 (oodO (x + 1))) ::
    challengeT (.n (oodO (x + 1))) (.n (oodO (x + 1) + 1)) (oodO (x + 1) + 13) ++
    [.atom (.load (.n (oodO (x + 1) + 19)) (.n 13) (x + 1))]

/-- The expansion of `opening_ood_point` at dimension `n ≥ 1`. -/
def oodBody (n : ℕ) : List Stmt :=
  [.atom (.copy (.n 14) (.n 0)), .atom (.copy (.n 15) (.n 1)), .atom (.copy (.n 16) (.n 2)),
    .atom (.copy (.n 17) (.n 3)), .atom (.copy (.n 18) (.n 4)),
    keccakA [.n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 12, .n 14, .n 15, .n 16, .n 17, .n 18]
      (run13 19)] ++
  challengeT (.n 19) (.n 20) 32 ++
  [.atom (.load (.n 38) (.n 13) 0), .atom (.const (.n 39) (word 1 0 0)),
    .atom (.const (.n 40) (word 0 0 0)), .atom (.const (.n 41) (word 0 0 0)),
    .atom (.const (.n 42) (word 0 0 0)), .atom (.const (.n 43) (word 0 0 0))] ++
  ((List.range (n - 1)).map oodRound).flatten ++
  [.atom (.copy (.n (oodO n)) (.n (oodO (n - 1) + 8))),
    .atom (.copy (.n (oodO n + 1)) (.n (oodO (n - 1) + 9))),
    .atom (.copy (.n (oodO n + 2)) (.n (oodO (n - 1) + 10))),
    .atom (.copy (.n (oodO n + 3)) (.n (oodO (n - 1) + 11))),
    .atom (.copy (.n (oodO n + 4)) (.n (oodO (n - 1) + 12))),
    .ret [.n (oodO n), .n (oodO n + 1), .n (oodO n + 2), .n (oodO n + 3), .n (oodO n + 4)]]

/-- The states of the rounds: the first permutation's, then one with nothing waiting each. -/
def oodS (S0 : KeccakState) : ℕ → KeccakState
  | 0 => S0
  | x + 1 => (⟨capOf (oodS S0 x), []⟩ : Fs).perm

/-- `squeezeN` from a state's capacity, nothing waiting: the next states' challenges. -/
theorem squeezeN_oodS (S0 : KeccakState) :
    ∀ k x, (⟨capOf (oodS S0 x), []⟩ : Fs).squeezeN k =
      ((List.range k).map fun i ↦ challengeOf (oodS S0 (x + 1 + i)), ⟨capOf (oodS S0 (x + k)), []⟩)
  | 0, x => by simp [Fs.squeezeN]
  | k + 1, x => by
    simp only [Fs.squeezeN]
    have h := squeezeN_oodS S0 k (x + 1)
    simp only [Fs.squeeze] at h ⊢
    rw [show (⟨capOf (⟨capOf (oodS S0 x), []⟩ : Fs).perm, []⟩ : Fs) = ⟨capOf (oodS S0 (x + 1)), []⟩
      from rfl, h, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Function.comp_def, Prod.mk.injEq]
    refine ⟨?_, by rw [show x + 1 + k = x + (k + 1) by omega]⟩
    refine congrArg₂ List.cons (by rw [Nat.add_zero, oodS]) ?_
    refine congrArg (List.map · (List.range k)) (funext fun i ↦ ?_)
    rw [show x + 1 + 1 + i = x + 1 + i.succ by omega]

/-- A `KECCAK` atom writing a run of thirteen values. -/
theorem keccak_run13 {ins : List V} {b : ℕ}
    (h : (Atom.keccak ins (run13 b) false false).Holds rd σ) :
    AllCanonical (ins.map σ) ∧ ∀ c : Fin 13, σ (.n (b + c.val)) = cellsOfState (permOf (ins.map σ)) false c := by
  obtain ⟨-, -, hcan, hout⟩ := keccakA_perm h
  refine ⟨hcan, fun c => ?_⟩
  have := outs_eq hout c (by simp [run13])
  simpa [run13] using this

/-- What round `x` asks. -/
theorem holds_oodRound (x : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (oodRound x) True kret ↔
      (Atom.keccak ([.n 40, .n 40, .n 40, .n 40, .n 40, .n 41, .n 42, .n 43] ++
        [.n (oodO x + 8), .n (oodO x + 9), .n (oodO x + 10), .n (oodO x + 11), .n (oodO x + 12)])
        (run13 (oodO (x + 1))) false false).Holds
          rd σ ∧
        ChallengeOk σ (.n (oodO (x + 1))) (.n (oodO (x + 1) + 1)) (oodO (x + 1) + 13) ∧
        LoadHolds rd (σ (.n 13)) (x + 1) (σ (.n (oodO (x + 1) + 19))) := by
  simp only [oodRound, keccakA, Stmt.HoldsList, List.cons_append, holdsList_append,
    holds_challengeT, Stmt.Holds, and_true]
  rfl

/-- The thirteen parameters. -/
abbrev oodParams : List V :=
  [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 12, .n 13]

/-- **`opening_ood_point` at every dimension `n ≥ 1`**, for a function whose body is
`oodBody n`: sound. -/
theorem ood_sound {name : String} {f : Fn} (n : ℕ) (hn : 1 ≤ n)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = oodParams)
    (hbody : f.body = oodBody n) (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd name args rets) : MeaningOpeningOodPoint n rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, oodBody] at h
  simp only [holdsList_append, holdsList_range_flatten (n - 1) oodRound (fun _ => rfl),
    holds_oodRound, holds_challengeT, keccakA, Stmt.HoldsList, Stmt.Holds, List.map_cons,
    List.map_nil] at h
  obtain ⟨σ, hp, h14, h15, h16, h17, h18, hK0, hch0, l38, -, h40, h41, h42, h43, hrounds,
    c0, c1, c2, c3, c4, hret⟩ := h
  subst hp
  have h14 : σ (.n 14) = σ (.n 0) := h14
  have h15 : σ (.n 15) = σ (.n 1) := h15
  have h16 : σ (.n 16) = σ (.n 2) := h16
  have h17 : σ (.n 17) = σ (.n 3) := h17
  have h18 : σ (.n 18) = σ (.n 4) := h18
  have h40 : σ (.n 40) = 0 := by rw [← word_zero]; exact h40
  have h41 : σ (.n 41) = 0 := by rw [← word_zero]; exact h41
  have h42 : σ (.n 42) = 0 := by rw [← word_zero]; exact h42
  have h43 : σ (.n 43) = 0 := by rw [← word_zero]; exact h43
  obtain ⟨hcan0, hout0⟩ := keccak_run13 hK0
  set S0 := permOf ([.n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 12, .n 14, .n 15, .n 16, .n 17,
    .n 18].map σ) with hS0
  have hst : ∀ x, x < n → ∀ c : Fin 13, σ (.n (oodO x + c.val)) = cellsOfState (oodS S0 x) false c := by
    intro x
    induction x with
    | zero => intro _ c; exact hout0 c
    | succ x ih =>
      intro hx c
      obtain ⟨hK, -, -⟩ := hrounds x (by omega)
      obtain ⟨-, hout⟩ := keccak_run13 hK
      rw [hout c]
      suffices hp : permOf (([.n 40, .n 40, .n 40, .n 40, .n 40, .n 41, .n 42, .n 43] ++
          [.n (oodO x + 8), .n (oodO x + 9), .n (oodO x + 10), .n (oodO x + 11),
            .n (oodO x + 12)] : List V).map σ) = oodS S0 (x + 1) by rw [hp]
      rw [oodS, perm_eq_cells _ (by simp)]
      have i8 : σ (.n (oodO x + 8)) = cellsOfState (oodS S0 x) false 8 := ih (by omega) 8
      have i9 : σ (.n (oodO x + 9)) = cellsOfState (oodS S0 x) false 9 := ih (by omega) 9
      have i10 : σ (.n (oodO x + 10)) = cellsOfState (oodS S0 x) false 10 := ih (by omega) 10
      have i11 : σ (.n (oodO x + 11)) = cellsOfState (oodS S0 x) false 11 := ih (by omega) 11
      have i12 : σ (.n (oodO x + 12)) = cellsOfState (oodS S0 x) false 12 := ih (by omega) 12
      simp [h40, h41, h42, h43, i8, i9, i10, i11, i12, capOf, pendCells]
  have hS0' : S0 = permOf [σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8), σ (.n 9), σ (.n 10), σ (.n 11),
      σ (.n 12), σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] := by
    rw [hS0]; simp [h14, h15, h16, h17, h18]
  refine ⟨?_, ?_⟩
  · intro c hc
    exact hcan0 c (by simpa [h14, h15, h16, h17, h18] using hc)
  · rw [← hS0']
    show ReadsAt rd (σ (.n 13)) (challengeOf S0 ::
        (Fs.squeezeN (n - 1) ⟨capOf (oodS S0 0), []⟩).1) ∧
      rets = (Fs.squeezeN (n - 1) ⟨capOf (oodS S0 0), []⟩).2.cap
    rw [squeezeN_oodS S0 (n - 1) 0]
    simp only [Nat.zero_add]
    refine ⟨fun k hk => ?_, ?_⟩
    · cases k with
      | zero =>
        have e : σ (.n 38) = challengeOf S0 := challengeT_value hch0 (hst 0 hn 0) (hst 0 hn 1)
        have l38 : LoadHolds rd (σ (.n 13)) 0 (σ (.n 38)) := l38
        rw [e] at l38
        exact l38
      | succ i =>
        simp only [List.length_cons, List.length_map, List.length_range] at hk
        obtain ⟨-, hch, l⟩ := hrounds i (by omega)
        have e := challengeT_value hch (hst (i + 1) (by omega) 0) (hst (i + 1) (by omega) 1)
        rw [show oodO (i + 1) + 13 + 6 = oodO (i + 1) + 19 by omega] at e
        simpa [e, Nat.add_comm 1 i] using l
    · have c0 : σ (.n (oodO n)) = σ (.n (oodO (n - 1) + 8)) := c0
      have c1 : σ (.n (oodO n + 1)) = σ (.n (oodO (n - 1) + 9)) := c1
      have c2 : σ (.n (oodO n + 2)) = σ (.n (oodO (n - 1) + 10)) := c2
      have c3 : σ (.n (oodO n + 3)) = σ (.n (oodO (n - 1) + 11)) := c3
      have c4 : σ (.n (oodO n + 4)) = σ (.n (oodO (n - 1) + 12)) := c4
      have i8 : σ (.n (oodO (n - 1) + 8)) = cellsOfState (oodS S0 (n - 1)) false 8 :=
        hst (n - 1) (by omega) 8
      have i9 : σ (.n (oodO (n - 1) + 9)) = cellsOfState (oodS S0 (n - 1)) false 9 :=
        hst (n - 1) (by omega) 9
      have i10 : σ (.n (oodO (n - 1) + 10)) = cellsOfState (oodS S0 (n - 1)) false 10 :=
        hst (n - 1) (by omega) 10
      have i11 : σ (.n (oodO (n - 1) + 11)) = cellsOfState (oodS S0 (n - 1)) false 11 :=
        hst (n - 1) (by omega) 11
      have i12 : σ (.n (oodO (n - 1) + 12)) = cellsOfState (oodS S0 (n - 1)) false 12 :=
        hst (n - 1) (by omega) 12
      rw [← hret, c0, c1, c2, c3, c4, i8, i9, i10, i11, i12]
      rfl

/-- The honest values of `opening_ood_point` at dimension `n`, by index. -/
def oodVals (as : List E) (S0 : KeccakState) (n k : ℕ) : E :=
  if k < 14 then as.getD k 0
  else if k < 19 then as.getD (k - 14) 0
  else if k < 32 then cellsOfState S0 false ⟨(k - 19) % 13, Nat.mod_lt _ (by omega)⟩
  else if k < 39 then challengeVals (cellsOfState S0 false 0) (cellsOfState S0 false 1) (k - 32)
  else if k = 39 then 1
  else if k < 44 then 0
  else if (k - 44) / 20 + 1 < n then
    (if (k - 44) % 20 < 13 then
      cellsOfState (oodS S0 ((k - 44) / 20 + 1)) false ⟨(k - 44) % 20 % 13, Nat.mod_lt _ (by omega)⟩
    else challengeVals (cellsOfState (oodS S0 ((k - 44) / 20 + 1)) false 0)
      (cellsOfState (oodS S0 ((k - 44) / 20 + 1)) false 1) ((k - 44) % 20 - 13))
  else cellsOfState (oodS S0 (n - 1)) false ⟨(8 + (k - 44) % 20) % 13, Nat.mod_lt _ (by omega)⟩

theorem oodVals_cells (as : List E) (S0 : KeccakState) {n x : ℕ} (hx : x < n) (c : Fin 13) :
    oodVals as S0 n (oodO x + c.val) = cellsOfState (oodS S0 x) false c := by
  have hc := c.isLt
  cases x with
  | zero =>
    unfold oodVals
    split_ifs <;> simp only [oodO] at * <;> try omega
    congr 1; ext; simp
  | succ x =>
    unfold oodVals
    have e1 : (oodO (x + 1) + c.val - 44) / 20 = x := by simp only [oodO]; omega
    have e2 : (oodO (x + 1) + c.val - 44) % 20 = c.val := by simp only [oodO]; omega
    simp only [e1, e2]
    split_ifs <;> simp only [oodO] at * <;> try omega
    congr 1; ext; simp

theorem oodVals_chal (as : List E) (S0 : KeccakState) {n x : ℕ} (hx : x + 1 < n) {i : ℕ}
    (hi : i < 7) :
    oodVals as S0 n (oodO (x + 1) + 13 + i) =
      challengeVals (cellsOfState (oodS S0 (x + 1)) false 0)
        (cellsOfState (oodS S0 (x + 1)) false 1) i := by
  unfold oodVals
  have e1 : (oodO (x + 1) + 13 + i - 44) / 20 = x := by simp only [oodO]; omega
  have e2 : (oodO (x + 1) + 13 + i - 44) % 20 = 13 + i := by simp only [oodO]; omega
  simp only [e1, e2, show 13 + i - 13 = i by omega]
  split_ifs <;> simp only [oodO] at * <;> omega

theorem oodVals_copy (as : List E) (S0 : KeccakState) {n : ℕ} (hn : 1 ≤ n) {i : ℕ} (hi : i < 5) :
    oodVals as S0 n (oodO n + i) = cellsOfState (oodS S0 (n - 1)) false ⟨8 + i, by omega⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold oodVals
  have e1 : (oodO (m + 1) + i - 44) / 20 = m := by simp only [oodO]; omega
  have e2 : (oodO (m + 1) + i - 44) % 20 = i := by simp only [oodO]; omega
  simp only [e1, e2]
  split_ifs <;> simp only [oodO] at * <;> try omega
  congr 1; ext; simp; try omega

theorem cells13_run13 (σ : Val) (b : ℕ) (c : Fin 13) :
    cells13 ((run13 b).map σ) c = σ (.n (b + c.val)) := by
  simp [cells13, run13, List.getD_eq_getElem?_getD]

/-- **`opening_ood_point` at every dimension `n ≥ 1`**: complete. -/
theorem ood_complete {name : String} {f : Fn} (n : ℕ) (hn : 1 ≤ n)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = oodParams)
    (hbody : f.body = oodBody n) (rd : Reader) (args rets : List E)
    (h : MeaningOpeningOodPoint n rd args rets) : coreProgram.Rel rd name args rets := by
  obtain ⟨f0, f1, f2, f3, f4, r0, r1, r2, r3, r4, r5, r6, r7, point, rfl⟩ :
      ∃ f0 f1 f2 f3 f4 r0 r1 r2 r3 r4 r5 r6 r7 point,
        args = [f0, f1, f2, f3, f4, r0, r1, r2, r3, r4, r5, r6, r7, point] := by
    match args, h with
    | [f0, f1, f2, f3, f4, r0, r1, r2, r3, r4, r5, r6, r7, point], _ =>
      exact ⟨f0, f1, f2, f3, f4, r0, r1, r2, r3, r4, r5, r6, r7, point, rfl⟩
  obtain ⟨hcan, hrd, hret⟩ := h
  obtain ⟨S0, hS0⟩ : ∃ S0, S0 = permOf [r0, r1, r2, r3, r4, r5, r6, r7, f0, f1, f2, f3, f4] :=
    ⟨_, rfl⟩
  rw [← hS0] at hrd hret
  have hsq := squeezeN_oodS S0 (n - 1) 0
  simp only [Nat.zero_add] at hsq
  change ReadsAt rd point (challengeOf S0 :: (Fs.squeezeN (n - 1) ⟨capOf (oodS S0 0), []⟩).1) at hrd
  change rets = (Fs.squeezeN (n - 1) ⟨capOf (oodS S0 0), []⟩).2.cap at hret
  rw [hsq] at hrd hret
  let as := [f0, f1, f2, f3, f4, r0, r1, r2, r3, r4, r5, r6, r7, point]
  let σ : Val := fun v ↦ oodVals as S0 n v.idx
  have ev : ∀ k, σ (.n k) = oodVals as S0 n k := fun _ ↦ rfl
  have evc : ∀ x, x < n → ∀ c : Fin 13, σ (.n (oodO x + c.val)) = cellsOfState (oodS S0 x) false c :=
    fun x hx c ↦ oodVals_cells as S0 hx c
  have z : IsCanonical128 (0 : E) := by
    rw [zero_eq_ofLimbs]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
  have cp : ∀ i (hi : i < 5), σ (.n (oodO n + i)) = cellsOfState (oodS S0 (n - 1)) false ⟨8 + i, by omega⟩ :=
    fun i hi ↦ oodVals_copy as S0 hn hi
  rw [rel_iff_sem hfind, hbody, hparams, oodBody]
  simp only [holdsList_append, holdsList_range_flatten (n - 1) oodRound (fun _ => rfl),
    holds_oodRound, holds_challengeT, keccakA, Stmt.HoldsList, Stmt.Holds, List.map_cons,
    List.map_nil]
  have hin0 : [σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8), σ (.n 9), σ (.n 10), σ (.n 11), σ (.n 12),
      σ (.n 14), σ (.n 15), σ (.n 16), σ (.n 17), σ (.n 18)] =
      [r0, r1, r2, r3, r4, r5, r6, r7, f0, f1, f2, f3, f4] := by simp [ev, oodVals, as]
  refine ⟨σ, by simp [ev, oodVals, as], ?_, ?_, ?_, ?_, ?_, keccak13_mk (rd := rd) rfl rfl ?_ ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (show σ _ = _; simp [ev, oodVals, as, word_zero, word_one]; done)
  · intro c
    simp only [List.map_cons, List.map_nil, hin0]
    fin_cases c <;> simp [cells13] <;> exact hcan _ (by simp)
  · intro c
    simp only [List.map_cons, List.map_nil, hin0, cells13_run13]
    exact (evc 0 hn c).trans (by rw [hS0]; rfl)
  · have e19 : σ (.n 19) = cellsOfState S0 false 0 := evc 0 hn 0
    have e20 : σ (.n 20) = cellsOfState S0 false 1 := evc 0 hn 1
    have hc20 : IsCanonical128 (σ (.n 20)) := by rw [e20]; exact cellsOfState_canonical _ _ _
    refine challengeOk_of_vals hc20 fun i hi ↦ ?_
    rw [e19, e20]
    interval_cases i <;> simp [ev, oodVals]
  · have e : σ (.n 38) = challengeOf S0 := by
      rw [ev]; simp only [oodVals]; norm_num; exact challengeVals_six S0
    show LoadHolds rd (σ (.n 13)) 0 (σ (.n 38))
    rw [e]; simpa [ev, oodVals, as] using hrd 0 (by simp)
  · intro i hi
    have i8 : σ (.n (oodO i + 8)) = cellsOfState (oodS S0 i) false 8 := evc i (by omega) 8
    have i9 : σ (.n (oodO i + 9)) = cellsOfState (oodS S0 i) false 9 := evc i (by omega) 9
    have i10 : σ (.n (oodO i + 10)) = cellsOfState (oodS S0 i) false 10 := evc i (by omega) 10
    have i11 : σ (.n (oodO i + 11)) = cellsOfState (oodS S0 i) false 11 := evc i (by omega) 11
    have i12 : σ (.n (oodO i + 12)) = cellsOfState (oodS S0 i) false 12 := evc i (by omega) 12
    have e40 : σ (.n 40) = 0 := by simp [ev, oodVals]
    have e41 : σ (.n 41) = 0 := by simp [ev, oodVals]
    have e42 : σ (.n 42) = 0 := by simp [ev, oodVals]
    have e43 : σ (.n 43) = 0 := by simp [ev, oodVals]
    have hin : ([.n 40, .n 40, .n 40, .n 40, .n 40, .n 41, .n 42, .n 43] ++ [.n (oodO i + 8),
        .n (oodO i + 9), .n (oodO i + 10), .n (oodO i + 11), .n (oodO i + 12)] : List V).map σ =
        pendCells [] ++ List.replicate (8 - 2 * ([] : List (E × ℕ)).length) 0 ++
          capOf (oodS S0 i) := by
      simp [e40, e41, e42, e43, capOf, pendCells, i8, i9, i10, i11, i12]
    refine ⟨keccak13_mk (rd := rd) rfl rfl ?_ ?_, ?_, ?_⟩
    · intro c
      rw [hin]
      fin_cases c <;> simp [cells13, capOf, pendCells, z, cellsOfState_canonical]
    · intro c
      rw [cells13_run13, evc (i + 1) (by omega) c, hin]
      simp only [oodS]
      rw [perm_eq_cells _ (by simp)]
      rfl
    · have e0 : σ (.n (oodO (i + 1))) = cellsOfState (oodS S0 (i + 1)) false 0 :=
        evc (i + 1) (by omega) 0
      have e1 : σ (.n (oodO (i + 1) + 1)) = cellsOfState (oodS S0 (i + 1)) false 1 :=
        evc (i + 1) (by omega) 1
      have hc1 : IsCanonical128 (σ (.n (oodO (i + 1) + 1))) := by
        rw [e1]; exact cellsOfState_canonical _ _ _
      refine challengeOk_of_vals hc1 fun j hj ↦ ?_
      rw [e0, e1]
      exact oodVals_chal as S0 (by omega) hj
    · have e : σ (.n (oodO (i + 1) + 19)) = challengeOf (oodS S0 (i + 1)) := by
        rw [← challengeVals_six]
        exact oodVals_chal as S0 (x := i) (by omega) (i := 6) (by omega)
      rw [e]
      have := hrd (i + 1) (by simp; omega)
      have e13 : σ (.n 13) = point := by simp [ev, oodVals, as]
      rw [e13]
      simpa [Nat.add_comm 1 i] using this
  · show σ (.n (oodO n)) = σ (.n (oodO (n - 1) + 8))
    exact (cp 0 (by omega)).trans (evc (n - 1) (by omega) 8).symm
  · show σ (.n (oodO n + 1)) = σ (.n (oodO (n - 1) + 9))
    exact (cp 1 (by omega)).trans (evc (n - 1) (by omega) 9).symm
  · show σ (.n (oodO n + 2)) = σ (.n (oodO (n - 1) + 10))
    exact (cp 2 (by omega)).trans (evc (n - 1) (by omega) 10).symm
  · show σ (.n (oodO n + 3)) = σ (.n (oodO (n - 1) + 11))
    exact (cp 3 (by omega)).trans (evc (n - 1) (by omega) 11).symm
  · show σ (.n (oodO n + 4)) = σ (.n (oodO (n - 1) + 12))
    exact (cp 4 (by omega)).trans (evc (n - 1) (by omega) 12).symm
  · rw [hret]
    show [σ (.n (oodO n)), σ (.n (oodO n + 1)), σ (.n (oodO n + 2)), σ (.n (oodO n + 3)),
      σ (.n (oodO n + 4))] = capOf (oodS S0 (n - 1))
    rw [show σ (.n (oodO n)) = _ from cp 0 (by omega), cp 1 (by omega), cp 2 (by omega),
      cp 3 (by omega), cp 4 (by omega)]
    rfl

/-! ## The deployed specializations -/

theorem ood_iff {name : String} {f : Fn} (n : ℕ) (hn : 1 ≤ n)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = oodParams)
    (hbody : f.body = oodBody n) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd name args rets ↔ MeaningOpeningOodPoint n rd args rets :=
  ⟨ood_sound n hn hfind hparams hbody rd args rets, ood_complete n hn hfind hparams hbody rd args rets⟩

set_option maxRecDepth 100000 in
theorem ood_L6_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L6" args rets ↔
      MeaningOpeningOodPoint 6 rd args rets :=
  ood_iff 6 (by decide) (Program.find?_of_indexOf? (j := 477) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem ood_L7_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L7" args rets ↔
      MeaningOpeningOodPoint 7 rd args rets :=
  ood_iff 7 (by decide) (Program.find?_of_indexOf? (j := 496) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem ood_L8_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L8" args rets ↔
      MeaningOpeningOodPoint 8 rd args rets :=
  ood_iff 8 (by decide) (Program.find?_of_indexOf? (j := 440) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem ood_L9_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L9" args rets ↔
      MeaningOpeningOodPoint 9 rd args rets :=
  ood_iff 9 (by decide) (Program.find?_of_indexOf? (j := 458) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem ood_L10_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L10" args rets ↔
      MeaningOpeningOodPoint 10 rd args rets :=
  ood_iff 10 (by decide) (Program.find?_of_indexOf? (j := 474) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem ood_L11_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L11" args rets ↔
      MeaningOpeningOodPoint 11 rd args rets :=
  ood_iff 11 (by decide) (Program.find?_of_indexOf? (j := 493) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem ood_L12_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L12" args rets ↔
      MeaningOpeningOodPoint 12 rd args rets :=
  ood_iff 12 (by decide) (Program.find?_of_indexOf? (j := 435) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem ood_L13_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L13" args rets ↔
      MeaningOpeningOodPoint 13 rd args rets :=
  ood_iff 13 (by decide) (Program.find?_of_indexOf? (j := 455) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem ood_L14_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L14" args rets ↔
      MeaningOpeningOodPoint 14 rd args rets :=
  ood_iff 14 (by decide) (Program.find?_of_indexOf? (j := 471) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem ood_L15_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L15" args rets ↔
      MeaningOpeningOodPoint 15 rd args rets :=
  ood_iff 15 (by decide) (Program.find?_of_indexOf? (j := 490) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem ood_L16_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L16" args rets ↔
      MeaningOpeningOodPoint 16 rd args rets :=
  ood_iff 16 (by decide) (Program.find?_of_indexOf? (j := 429) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem ood_L17_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L17" args rets ↔
      MeaningOpeningOodPoint 17 rd args rets :=
  ood_iff 17 (by decide) (Program.find?_of_indexOf? (j := 452) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem ood_L18_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L18" args rets ↔
      MeaningOpeningOodPoint 18 rd args rets :=
  ood_iff 18 (by decide) (Program.find?_of_indexOf? (j := 468) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem ood_L19_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L19" args rets ↔
      MeaningOpeningOodPoint 19 rd args rets :=
  ood_iff 19 (by decide) (Program.find?_of_indexOf? (j := 487) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem ood_L20_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L20" args rets ↔
      MeaningOpeningOodPoint 20 rd args rets :=
  ood_iff 20 (by decide) (Program.find?_of_indexOf? (j := 506) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem ood_L21_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L21" args rets ↔
      MeaningOpeningOodPoint 21 rd args rets :=
  ood_iff 21 (by decide) (Program.find?_of_indexOf? (j := 520) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem ood_L22_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L22" args rets ↔
      MeaningOpeningOodPoint 22 rd args rets :=
  ood_iff 22 (by decide) (Program.find?_of_indexOf? (j := 534) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

/-- **`opening_ood_point`'s core IR is its meaning**, at every deployed dimension. -/
theorem opening_ood_point_holds : opening_ood_point_Spec := by
  intro p hp
  simp only [oodPointNames, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  exacts [ood_L6_iff, ood_L7_iff, ood_L8_iff, ood_L9_iff, ood_L10_iff, ood_L11_iff, ood_L12_iff, ood_L13_iff, ood_L14_iff, ood_L15_iff, ood_L16_iff, ood_L17_iff, ood_L18_iff, ood_L19_iff, ood_L20_iff, ood_L21_iff, ood_L22_iff]

end
end LeanVM.Guest.B1
