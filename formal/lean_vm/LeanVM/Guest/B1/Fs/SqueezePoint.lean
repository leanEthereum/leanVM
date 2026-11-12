/-
  LeanVM.Guest.B1.Fs.SqueezePoint

  B1 for `squeeze_point_from`: a run of challenges after a given first, nothing waiting.
-/

module

public import LeanVM.Guest.B1.Fs.Message

/-!
# `squeeze_point_from`

A run of `m` plain squeezes from a carried capacity (`sqBlk`: the permutation of the zero rate and
the previous capacity, its challenge copied out and stored at the point), after the capacity
copied in and the pad run, and before the last capacity copied out twice:
`squeeze_point_from__L{n}` (`spfBody n`): `point[0] = first`, the capacity into `7 .. 11`, the
pad run `12 .. 16`, `n - 1` squeezes from `17` (block `x` writes from `17 + 14 x`, its challenge
at `17 + 14 x + 13`), stored at `point[x + 1]`.

`sq_sound`, `sq_complete`: the run is `Fs.squeezeN` (`sqSt`, the sponge after `x` squeezes).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## A run of squeezes -/

/-- The sponge after `x` squeezes from `s`. -/
def sqSt (s : Fs) : ℕ → Fs
  | 0 => s
  | x + 1 => (sqSt s x).squeeze.2

theorem sqSt_shift (s : Fs) : ∀ x, sqSt s (x + 1) = sqSt s.squeeze.2 x
  | 0 => rfl
  | x + 1 => by rw [sqSt, sqSt_shift s x]; rfl

theorem squeezeN_eq : ∀ (m : ℕ) (s : Fs),
    s.squeezeN m = ((List.range m).map fun x ↦ (sqSt s x).squeeze.1, sqSt s m)
  | 0, _ => rfl
  | m + 1, s => by
    rw [Fs.squeezeN, squeezeN_eq m, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine Prod.ext ?_ ?_
    · exact congrArg (List.cons _) (List.map_congr_left fun x _ ↦ by
        simp only [Function.comp, sqSt_shift])
    · exact (sqSt_shift s m).symm

theorem sqSt_pend {s : Fs} (hs : s.pend = []) : ∀ x, (sqSt s x).pend = []
  | 0 => hs
  | _ + 1 => rfl

theorem sqSt_cap_succ (s : Fs) (x : ℕ) : (sqSt s (x + 1)).cap = capOf (sqSt s x).perm := rfl

theorem sqSt_squeeze1 (s : Fs) (x : ℕ) : (sqSt s x).squeeze.1 = challengeOf (sqSt s x).perm := rfl

theorem sqSt_perm {s : Fs} (hs : s.pend = []) (x : ℕ) :
    (sqSt s x).perm = permOf ([0, 0, 0, 0, 0, 0, 0, 0] ++ (sqSt s x).cap) := by
  rw [perm_eq_cells _ (by rw [sqSt_pend hs]; simp), sqSt_pend hs]
  rfl

/-! ## The template -/

/-- Five consecutive values. -/
def run5 (c : ℕ) : List V := [.n c, .n (c + 1), .n (c + 2), .n (c + 3), .n (c + 4)]

/-- Thirteen consecutive values. -/
def run13 (b : ℕ) : List V := (List.range 13).map fun i ↦ .n (b + i)

/-- Where squeeze `x` reads its capacity: the copied one first, then the previous outputs'. -/
def sqCap (cap0 b x : ℕ) : ℕ := if x = 0 then cap0 else b + 14 * (x - 1) + 8

/-- Squeeze `x`: the permutation of the zero rate (the pad run's zeros from `z`) and the previous
capacity, its challenge copied and stored at `pt[off + x]`. -/
def sqBlk (z b cap0 : ℕ) (pt : V) (off x : ℕ) : List Stmt :=
  [keccakA ([.n z, .n z, .n z, .n z, .n z, .n (z + 1), .n (z + 2), .n (z + 3)] ++
      run5 (sqCap cap0 b x)) (run13 (b + 14 * x)),
    .atom (.copy (.n (b + 14 * x + 13)) (.n (b + 14 * x))),
    .atom (.load (.n (b + 14 * x + 13)) pt (off + x))]

/-- What squeeze `x` asks of a valuation. -/
def SqOk (rd : Reader) (σ : Val) (z b cap0 : ℕ) (pt : V) (off x : ℕ) : Prop :=
  (Atom.keccak ([.n z, .n z, .n z, .n z, .n z, .n (z + 1), .n (z + 2), .n (z + 3)] ++
      run5 (sqCap cap0 b x)) (run13 (b + 14 * x)) false false).Holds rd σ ∧
    σ (.n (b + 14 * x + 13)) = σ (.n (b + 14 * x)) ∧
    LoadHolds rd (σ pt) (off + x) (σ (.n (b + 14 * x + 13)))

theorem holds_sqBlk (z b cap0 : ℕ) (pt : V) (off x : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (sqBlk z b cap0 pt off x) True kret ↔ SqOk rd σ z b cap0 pt off x := by
  simp only [sqBlk, SqOk, keccakA, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

theorem cells13_run13 (σ : Val) (b : ℕ) (c : Fin 13) :
    cells13 ((run13 b).map σ) c = σ (.n (b + c.val)) := by
  simp [cells13, run13, List.getD_eq_getElem?_getD]

theorem keccak_run13 {ins : List V} {b : ℕ}
    (h : (Atom.keccak ins (run13 b) false false).Holds rd σ) :
    ∀ c : Fin 13, σ (.n (b + c.val)) = cellsOfState (permOf (ins.map σ)) false c := by
  obtain ⟨-, -, hout⟩ := keccakA_perm h
  intro c
  have := outs_eq hout c (by simp [run13])
  simpa [run13] using this

/-- The zero run a chain reads, from the pad run's first zero. -/
def ZeroRun (σ : Val) (z : ℕ) : Prop :=
  σ (.n z) = 0 ∧ σ (.n (z + 1)) = 0 ∧ σ (.n (z + 2)) = 0 ∧ σ (.n (z + 3)) = 0

/-- The cells a squeeze reads, given its capacity's. -/
theorem sq_ins {z c : ℕ} (hz : ZeroRun σ z) :
    (([.n z, .n z, .n z, .n z, .n z, .n (z + 1), .n (z + 2), .n (z + 3)] : List V) ++ run5 c).map σ =
      [0, 0, 0, 0, 0, 0, 0, 0] ++ (run5 c).map σ := by
  obtain ⟨h0, h1, h2, h3⟩ := hz
  simp [run5, h0, h1, h2, h3]

/-- The capacity a squeeze after the first reads: the previous outputs' cells `8 .. 12`. -/
theorem run5_cells {b x : ℕ} {S : KeccakState}
    (h : ∀ c : Fin 13, σ (.n (b + 14 * x + c.val)) = cellsOfState S false c) :
    (run5 (b + 14 * x + 8)).map σ = capOf S := by
  have e : ∀ i (hi : i < 5), σ (.n (b + 14 * x + 8 + i)) = cellsOfState S false ⟨8 + i, by omega⟩ :=
    fun i hi ↦ by rw [show b + 14 * x + 8 + i = b + 14 * x + (⟨8 + i, by omega⟩ : Fin 13).val by
      simp; ring]; exact h _
  simp only [run5, List.map_cons, List.map_nil, capOf]
  rw [show σ (.n (b + 14 * x + 8)) = _ from e 0 (by omega), e 1 (by omega), e 2 (by omega),
    e 3 (by omega), e 4 (by omega)]
  rfl

/-- **A chain of squeezes is sound**: on the zero run and the capacity of `s` (nothing waiting),
squeeze `x` writes the cells of `(sqSt s x).perm` and stores its challenge. -/
theorem sq_sound {z b cap0 : ℕ} {pt : V} {off m : ℕ} {s : Fs} (hs : s.pend = [])
    (hz : ZeroRun σ z) (hcap : (run5 cap0).map σ = s.cap) (h : ∀ x < m, SqOk rd σ z b cap0 pt off x) :
    ∀ x < m, (∀ c : Fin 13, σ (.n (b + 14 * x + c.val)) = cellsOfState (sqSt s x).perm false c) ∧
      LoadHolds rd (σ pt) (off + x) (challengeOf (sqSt s x).perm) := by
  have step : ∀ x < m, (run5 (sqCap cap0 b x)).map σ = (sqSt s x).cap →
      (∀ c : Fin 13, σ (.n (b + 14 * x + c.val)) = cellsOfState (sqSt s x).perm false c) ∧
        LoadHolds rd (σ pt) (off + x) (challengeOf (sqSt s x).perm) := by
    intro x hx hc
    obtain ⟨hk, hcp, hl⟩ := h x hx
    have hout := keccak_run13 hk
    rw [sq_ins hz, hc, ← sqSt_perm hs] at hout
    refine ⟨hout, ?_⟩
    rw [hcp, show b + 14 * x = b + 14 * x + (0 : Fin 13).val by simp, hout 0,
      ← Keccak.challengeOf_cells] at hl
    exact hl
  intro x
  induction x with
  | zero => intro hx; exact step 0 hx (by simpa [sqCap, sqSt] using hcap)
  | succ x ih =>
    intro hx
    obtain ⟨hB, -⟩ := ih (by omega)
    refine step (x + 1) hx ?_
    rw [sqSt_cap_succ, ← run5_cells hB]
    simp only [sqCap, Nat.add_sub_cancel, show x + 1 ≠ 0 by omega, ↓reduceIte]

/-- **A chain of squeezes is complete**: values at the cells of `(sqSt s x).perm` and their
challenges stored make every squeeze hold. -/
theorem sq_complete {z b cap0 : ℕ} {pt : V} {off m : ℕ} {s : Fs} (hs : s.pend = [])
    (hz : ZeroRun σ z) (hcap : (run5 cap0).map σ = s.cap)
    (hv : ∀ x < m, ∀ c : Fin 13, σ (.n (b + 14 * x + c.val)) = cellsOfState (sqSt s x).perm false c)
    (hch : ∀ x < m, σ (.n (b + 14 * x + 13)) = challengeOf (sqSt s x).perm)
    (hpt : ∀ x < m, LoadHolds rd (σ pt) (off + x) (challengeOf (sqSt s x).perm)) :
    ∀ x < m, SqOk rd σ z b cap0 pt off x := by
  intro x hx
  have hc : (run5 (sqCap cap0 b x)).map σ = (sqSt s x).cap := by
    cases x with
    | zero => simpa [sqCap, sqSt] using hcap
    | succ x =>
      rw [sqSt_cap_succ, ← run5_cells (hv x (by omega))]
      simp only [sqCap, Nat.add_sub_cancel, show x + 1 ≠ 0 by omega, ↓reduceIte]
  refine ⟨keccak13_mk (by simp [run5]) (by simp [run13]) fun c ↦ ?_, ?_, ?_⟩
  · rw [cells13_run13, hv x hx c]
    show _ = cellsOfState (permOf _) false c
    rw [sq_ins hz, hc, ← sqSt_perm hs]
  · rw [hch x hx, show b + 14 * x = b + 14 * x + (0 : Fin 13).val by simp, hv x hx 0,
      Keccak.challengeOf_cells]
  · rw [hch x hx]; exact hpt x hx

theorem holds_sqChain (z b cap0 : ℕ) (pt : V) (off m : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ ((List.range m).map (sqBlk z b cap0 pt off)).flatten next kret ↔
      (∀ x < m, SqOk rd σ z b cap0 pt off x) ∧ next := by
  rw [holdsList_range_flatten m _ (fun _ => rfl)]
  simp only [holds_sqBlk]

/-! ## Cells -/

/-- A cell index, reduced. -/
def fin13 (x : ℕ) : Fin 13 := ⟨x % 13, Nat.mod_lt _ (by decide)⟩

/-- Decide the next `if` of an unfolded index function by `omega`. -/
macro "sp_if" : tactic => `(tactic| first
  | (rw [ite_eq_right_of_eq_false]; rotate_left; exact eq_false (by omega))
  | (rw [ite_eq_left_of_eq_true]; rotate_left; exact eq_true (by omega)))

theorem fin13_eq {x : ℕ} {c : Fin 13} (h : x % 13 = c.val) : fin13 x = c := Fin.ext h

/-- The last capacity copied out twice: cells `8 .. 12` of the last squeeze's state, read from the
chain's last block or either copy. -/
theorem sp_copies {b m : ℕ} {S : KeccakState}
    (hB : ∀ c : Fin 13, σ (.n (b + 14 * m + c.val)) = cellsOfState S false c)
    (c1 : ∀ i < 5, σ (.n (b + 14 * (m + 1) + i)) = σ (.n (b + 14 * m + 8 + i)))
    (c2 : ∀ i < 5, σ (.n (b + 5 + 14 * (m + 1) + i)) = σ (.n (b + 14 * (m + 1) + i))) :
    [σ (.n (b + 5 + 14 * (m + 1))), σ (.n (b + 5 + 14 * (m + 1) + 1)),
      σ (.n (b + 5 + 14 * (m + 1) + 2)), σ (.n (b + 5 + 14 * (m + 1) + 3)),
      σ (.n (b + 5 + 14 * (m + 1) + 4))] = capOf S := by
  have e : ∀ i (hi : i < 5), σ (.n (b + 5 + 14 * (m + 1) + i)) =
      cellsOfState S false ⟨8 + i, by omega⟩ := fun i hi ↦ by
    rw [c2 i hi, c1 i hi, show b + 14 * m + 8 + i = b + 14 * m + (⟨8 + i, by omega⟩ : Fin 13).val by
      simp; ring]
    exact hB _
  rw [show σ (.n (b + 5 + 14 * (m + 1))) = _ from (by simpa using e 0 (by omega)), e 1 (by omega),
    e 2 (by omega), e 3 (by omega), e 4 (by omega)]
  rfl

/-! ## `squeeze_point_from` -/

/-- The expansion of `squeeze_point_from__L{n + 1}`, `n ≥ 1` squeezes after the given first. -/
def spfBody (n : ℕ) : List Stmt :=
  [.atom (.load (.n 5) (.n 6) 0), .atom (.copy (.n 7) (.n 0)), .atom (.copy (.n 8) (.n 1)),
    .atom (.copy (.n 9) (.n 2)), .atom (.copy (.n 10) (.n 3)), .atom (.copy (.n 11) (.n 4))] ++
  padRunT 12 ++ ((List.range n).map (sqBlk 13 17 7 (.n 6) 1)).flatten ++
  [.atom (.copy (.n (17 + 14 * n)) (.n (17 + 14 * (n - 1) + 8))),
    .atom (.copy (.n (18 + 14 * n)) (.n (17 + 14 * (n - 1) + 9))),
    .atom (.copy (.n (19 + 14 * n)) (.n (17 + 14 * (n - 1) + 10))),
    .atom (.copy (.n (20 + 14 * n)) (.n (17 + 14 * (n - 1) + 11))),
    .atom (.copy (.n (21 + 14 * n)) (.n (17 + 14 * (n - 1) + 12))),
    .atom (.copy (.n (22 + 14 * n)) (.n (17 + 14 * n))),
    .atom (.copy (.n (23 + 14 * n)) (.n (18 + 14 * n))),
    .atom (.copy (.n (24 + 14 * n)) (.n (19 + 14 * n))),
    .atom (.copy (.n (25 + 14 * n)) (.n (20 + 14 * n))),
    .atom (.copy (.n (26 + 14 * n)) (.n (21 + 14 * n))),
    .ret [.n (22 + 14 * n), .n (23 + 14 * n), .n (24 + 14 * n), .n (25 + 14 * n),
      .n (26 + 14 * n)]]

/-- The honest values of `squeeze_point_from__L{n + 1}` on its arguments `as`, `s` its sponge. -/
def spfVals (as : List E) (s : Fs) (n k : ℕ) : E :=
  if k < 7 then as.getD k 0
  else if k < 12 then as.getD (k - 7) 0
  else if k = 12 then word 1 0
  else if k < 17 then 0
  else if (k - 17) / 14 < n then
    (if (k - 17) % 14 < 13 then cellsOfState (sqSt s ((k - 17) / 14)).perm false (fin13 ((k - 17) % 14))
    else challengeOf (sqSt s ((k - 17) / 14)).perm)
  else if k < 22 + 14 * n then cellsOfState (sqSt s (n - 1)).perm false (fin13 (8 + (k - (17 + 14 * n))))
  else cellsOfState (sqSt s (n - 1)).perm false (fin13 (8 + (k - (22 + 14 * n))))

theorem spf_sound {name : String} {f : Fn} (n : ℕ) (hn : 1 ≤ n)
    (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbody : f.body = spfBody n) (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd name args rets) : MeaningSqueezePointFrom (n + 1) rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, spfBody] at h
  simp only [holdsList_append, holds_padRunT, holds_sqChain, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, hfirst, h7, h8, h9, h10, h11, ⟨-, z13, z14, z15, z16⟩, hchain, c0, c1, c2, c3,
    c4, d0, d1, d2, d3, d4, hret⟩ := h
  subst hp
  set s : Fs := ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ with hsd
  have hz : ZeroRun σ 13 := ⟨z13, z14, z15, z16⟩
  have hcap : (run5 7).map σ = s.cap := by
    simp only [run5, List.map_cons, List.map_nil]
    rw [show σ (.n 7) = σ (.n 0) from h7, show σ (.n (7 + 1)) = σ (.n 1) from h8,
      show σ (.n (7 + 2)) = σ (.n 2) from h9, show σ (.n (7 + 3)) = σ (.n 3) from h10,
      show σ (.n (7 + 4)) = σ (.n 4) from h11]
  have hs := sq_sound (s := s) rfl hz hcap hchain
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hB, -⟩ := hs m (by omega)
  simp only [MeaningSqueezePointFrom, Nat.add_sub_cancel]
  rw [squeezeN_eq]
  refine ⟨fun k hk ↦ ?_, ?_⟩
  · cases k with
    | zero => exact hfirst
    | succ k =>
      simp only [List.length_cons, List.length_map, List.length_range] at hk
      simp only [List.getElem_cons_succ, List.getElem_map, List.getElem_range, sqSt_squeeze1]
      have := (hs k (by omega)).2
      rwa [show 1 + k = k + 1 by omega] at this
  · rw [← hret, sqSt_cap_succ, ← sp_copies (b := 17) hB (fun i hi ↦ ?_) (fun i hi ↦ ?_)]
    · simp only [List.cons.injEq, and_true]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | exact congrArg σ (congrArg V.n (by ring))
    · simp only [show m + 1 - 1 = m by omega] at c0 c1 c2 c3 c4
      interval_cases i
      · exact c0
      · exact (show σ (.n (17 + 14 * (m + 1) + 1)) = σ (.n (18 + 14 * (m + 1))) by
          rw [show 17 + 14 * (m + 1) + 1 = 18 + 14 * (m + 1) by ring]).trans c1
      · exact (show σ (.n (17 + 14 * (m + 1) + 2)) = σ (.n (19 + 14 * (m + 1))) by
          rw [show 17 + 14 * (m + 1) + 2 = 19 + 14 * (m + 1) by ring]).trans
            (c2.trans (by rw [show 17 + 14 * m + 10 = 17 + 14 * m + 8 + 2 by ring]))
      · exact (show σ (.n (17 + 14 * (m + 1) + 3)) = σ (.n (20 + 14 * (m + 1))) by
          rw [show 17 + 14 * (m + 1) + 3 = 20 + 14 * (m + 1) by ring]).trans
            (c3.trans (by rw [show 17 + 14 * m + 11 = 17 + 14 * m + 8 + 3 by ring]))
      · exact (show σ (.n (17 + 14 * (m + 1) + 4)) = σ (.n (21 + 14 * (m + 1))) by
          rw [show 17 + 14 * (m + 1) + 4 = 21 + 14 * (m + 1) by ring]).trans
            (c4.trans (by rw [show 17 + 14 * m + 12 = 17 + 14 * m + 8 + 4 by ring]))
    · interval_cases i
      · exact d0.trans (by rw [show 17 + 14 * (m + 1) + 0 = 17 + 14 * (m + 1) by ring])
      · exact (show σ (.n (17 + 5 + 14 * (m + 1) + 1)) = σ (.n (23 + 14 * (m + 1))) by
          rw [show 17 + 5 + 14 * (m + 1) + 1 = 23 + 14 * (m + 1) by ring]).trans
            (d1.trans (by rw [show 18 + 14 * (m + 1) = 17 + 14 * (m + 1) + 1 by ring]))
      · exact (show σ (.n (17 + 5 + 14 * (m + 1) + 2)) = σ (.n (24 + 14 * (m + 1))) by
          rw [show 17 + 5 + 14 * (m + 1) + 2 = 24 + 14 * (m + 1) by ring]).trans
            (d2.trans (by rw [show 19 + 14 * (m + 1) = 17 + 14 * (m + 1) + 2 by ring]))
      · exact (show σ (.n (17 + 5 + 14 * (m + 1) + 3)) = σ (.n (25 + 14 * (m + 1))) by
          rw [show 17 + 5 + 14 * (m + 1) + 3 = 25 + 14 * (m + 1) by ring]).trans
            (d3.trans (by rw [show 20 + 14 * (m + 1) = 17 + 14 * (m + 1) + 3 by ring]))
      · exact (show σ (.n (17 + 5 + 14 * (m + 1) + 4)) = σ (.n (26 + 14 * (m + 1))) by
          rw [show 17 + 5 + 14 * (m + 1) + 4 = 26 + 14 * (m + 1) by ring]).trans
            (d4.trans (by rw [show 21 + 14 * (m + 1) = 17 + 14 * (m + 1) + 4 by ring]))


theorem spf_complete {name : String} {f : Fn} (n : ℕ) (hn : 1 ≤ n)
    (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbody : f.body = spfBody n) (rd : Reader) (args rets : List E)
    (h : MeaningSqueezePointFrom (n + 1) rd args rets) : coreProgram.Rel rd name args rets := by
  obtain ⟨f0, f1, f2, f3, f4, first, point, rfl⟩ : ∃ f0 f1 f2 f3 f4 first point,
      args = [f0, f1, f2, f3, f4, first, point] := by
    match args, h with
    | [a, b, c, d, e, g, k], _ => exact ⟨a, b, c, d, e, g, k, rfl⟩
  obtain ⟨hpt, hret⟩ := h
  simp only [Nat.add_sub_cancel] at hpt hret
  set s : Fs := ⟨[f0, f1, f2, f3, f4], []⟩ with hsd
  rw [squeezeN_eq] at hpt hret
  let as := [f0, f1, f2, f3, f4, first, point]
  let σ : Val := fun v ↦ spfVals as s n v.idx
  have ev : ∀ k, σ (.n k) = spfVals as s n k := fun _ ↦ rfl
  have hz : ZeroRun σ 13 := by refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [ev, spfVals]
  have hcap : (run5 7).map σ = s.cap := by simp [run5, ev, spfVals, as, hsd]
  have hv : ∀ x < n, ∀ c : Fin 13,
      σ (.n (17 + 14 * x + c.val)) = cellsOfState (sqSt s x).perm false c := by
    intro x hx c
    have := c.isLt
    rw [ev, spfVals, show (17 + 14 * x + c.val - 17) / 14 = x by omega,
      show (17 + 14 * x + c.val - 17) % 14 = c.val by omega]
    repeat sp_if
    congr 1; apply fin13_eq; omega
  have hch : ∀ x < n, σ (.n (17 + 14 * x + 13)) = challengeOf (sqSt s x).perm := by
    intro x hx
    rw [ev, spfVals, show (17 + 14 * x + 13 - 17) / 14 = x by omega,
      show (17 + 14 * x + 13 - 17) % 14 = 13 by omega]
    repeat sp_if
  have hp : ∀ x < n, LoadHolds rd point (1 + x) (challengeOf (sqSt s x).perm) := by
    intro x hx
    have := hpt (x + 1) (by simp; omega)
    rw [show 1 + x = x + 1 by omega]
    simpa [sqSt_squeeze1] using this
  have e6 : σ (.n 6) = point := by simp [ev, spfVals, as]
  have hfirst : LoadHolds rd point 0 first := hpt 0 (by simp)
  rw [rel_iff_sem hfind, hbody, hparams, spfBody]
  simp only [holdsList_append, holds_padRunT, holds_sqChain, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds, List.map_cons, List.map_nil]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have cA : ∀ i < 5, σ (.n (17 + 14 * (m + 1) + i)) =
      cellsOfState (sqSt s m).perm false (fin13 (8 + i)) := by
    intro i hi
    rw [ev, spfVals]
    repeat sp_if
    rw [show m + 1 - 1 = m by omega, show 17 + 14 * (m + 1) + i - (17 + 14 * (m + 1)) = i by omega]
  have cB : ∀ i < 5, σ (.n (22 + 14 * (m + 1) + i)) =
      cellsOfState (sqSt s m).perm false (fin13 (8 + i)) := by
    intro i hi
    rw [ev, spfVals]
    repeat sp_if
    rw [show m + 1 - 1 = m by omega, show 22 + 14 * (m + 1) + i - (22 + 14 * (m + 1)) = i by omega]
  have cC : ∀ i < 5, σ (.n (17 + 14 * m + 8 + i)) =
      cellsOfState (sqSt s m).perm false (fin13 (8 + i)) := by
    intro i hi
    rw [show 17 + 14 * m + 8 + i = 17 + 14 * m + (fin13 (8 + i)).val by simp [fin13]; omega]
    exact hv m (by omega) _
  refine ⟨σ, by simp [ev, spfVals, as], ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, hz⟩,
    ⟨sq_complete (s := s) rfl hz hcap hv hch (fun x hx ↦ by rw [e6]; exact hp x hx), ?_⟩⟩
  · show LoadHolds rd (σ (.n 6)) 0 (σ (.n 5))
    rw [e6, show σ (.n 5) = first by simp [ev, spfVals, as]]; exact hfirst
  all_goals try (simp [ev, spfVals, as]; done)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show m + 1 - 1 = m by omega, show 17 + 14 * (m + 1) = 17 + 14 * (m + 1) + 0 by ring,
      cA 0 (by omega), show 17 + 14 * m + 8 = 17 + 14 * m + 8 + 0 by ring, cC 0 (by omega)]
  · rw [show m + 1 - 1 = m by omega, show 18 + 14 * (m + 1) = 17 + 14 * (m + 1) + 1 by ring,
      cA 1 (by omega), show 17 + 14 * m + 9 = 17 + 14 * m + 8 + 1 by ring, cC 1 (by omega)]
  · rw [show m + 1 - 1 = m by omega, show 19 + 14 * (m + 1) = 17 + 14 * (m + 1) + 2 by ring,
      cA 2 (by omega), show 17 + 14 * m + 10 = 17 + 14 * m + 8 + 2 by ring, cC 2 (by omega)]
  · rw [show m + 1 - 1 = m by omega, show 20 + 14 * (m + 1) = 17 + 14 * (m + 1) + 3 by ring,
      cA 3 (by omega), show 17 + 14 * m + 11 = 17 + 14 * m + 8 + 3 by ring, cC 3 (by omega)]
  · rw [show m + 1 - 1 = m by omega, show 21 + 14 * (m + 1) = 17 + 14 * (m + 1) + 4 by ring,
      cA 4 (by omega), show 17 + 14 * m + 12 = 17 + 14 * m + 8 + 4 by ring, cC 4 (by omega)]
  · rw [show 22 + 14 * (m + 1) = 22 + 14 * (m + 1) + 0 by ring, cB 0 (by omega),
      show 17 + 14 * (m + 1) = 17 + 14 * (m + 1) + 0 by ring, cA 0 (by omega)]
  · rw [show 23 + 14 * (m + 1) = 22 + 14 * (m + 1) + 1 by ring, cB 1 (by omega),
      show 18 + 14 * (m + 1) = 17 + 14 * (m + 1) + 1 by ring, cA 1 (by omega)]
  · rw [show 24 + 14 * (m + 1) = 22 + 14 * (m + 1) + 2 by ring, cB 2 (by omega),
      show 19 + 14 * (m + 1) = 17 + 14 * (m + 1) + 2 by ring, cA 2 (by omega)]
  · rw [show 25 + 14 * (m + 1) = 22 + 14 * (m + 1) + 3 by ring, cB 3 (by omega),
      show 20 + 14 * (m + 1) = 17 + 14 * (m + 1) + 3 by ring, cA 3 (by omega)]
  · rw [show 26 + 14 * (m + 1) = 22 + 14 * (m + 1) + 4 by ring, cB 4 (by omega),
      show 21 + 14 * (m + 1) = 17 + 14 * (m + 1) + 4 by ring, cA 4 (by omega)]
  · rw [hret, sqSt_cap_succ, show 22 + 14 * (m + 1) = 22 + 14 * (m + 1) + 0 by ring,
      show 23 + 14 * (m + 1) = 22 + 14 * (m + 1) + 1 by ring,
      show 24 + 14 * (m + 1) = 22 + 14 * (m + 1) + 2 by ring,
      show 25 + 14 * (m + 1) = 22 + 14 * (m + 1) + 3 by ring,
      show 26 + 14 * (m + 1) = 22 + 14 * (m + 1) + 4 by ring, cB 0 (by omega), cB 1 (by omega),
      cB 2 (by omega), cB 3 (by omega), cB 4 (by omega)]
    rfl

set_option maxRecDepth 100000 in
theorem spf_found_6 : coreProgram.find? (spfName 6) = some Data.core481 ∧
    Data.core481.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core481.body = spfBody 5 :=
  ⟨Program.find?_of_indexOf? (j := 481) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_7 : coreProgram.find? (spfName 7) = some Data.core529 ∧
    Data.core529.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core529.body = spfBody 6 :=
  ⟨Program.find?_of_indexOf? (j := 529) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_8 : coreProgram.find? (spfName 8) = some Data.core572 ∧
    Data.core572.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core572.body = spfBody 7 :=
  ⟨Program.find?_of_indexOf? (j := 572) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_9 : coreProgram.find? (spfName 9) = some Data.core615 ∧
    Data.core615.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core615.body = spfBody 8 :=
  ⟨Program.find?_of_indexOf? (j := 615) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_10 : coreProgram.find? (spfName 10) = some Data.core472 ∧
    Data.core472.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core472.body = spfBody 9 :=
  ⟨Program.find?_of_indexOf? (j := 472) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_11 : coreProgram.find? (spfName 11) = some Data.core520 ∧
    Data.core520.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core520.body = spfBody 10 :=
  ⟨Program.find?_of_indexOf? (j := 520) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_12 : coreProgram.find? (spfName 12) = some Data.core563 ∧
    Data.core563.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core563.body = spfBody 11 :=
  ⟨Program.find?_of_indexOf? (j := 563) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_13 : coreProgram.find? (spfName 13) = some Data.core606 ∧
    Data.core606.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core606.body = spfBody 12 :=
  ⟨Program.find?_of_indexOf? (j := 606) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_14 : coreProgram.find? (spfName 14) = some Data.core462 ∧
    Data.core462.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core462.body = spfBody 13 :=
  ⟨Program.find?_of_indexOf? (j := 462) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_15 : coreProgram.find? (spfName 15) = some Data.core511 ∧
    Data.core511.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core511.body = spfBody 14 :=
  ⟨Program.find?_of_indexOf? (j := 511) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_16 : coreProgram.find? (spfName 16) = some Data.core554 ∧
    Data.core554.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core554.body = spfBody 15 :=
  ⟨Program.find?_of_indexOf? (j := 554) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_17 : coreProgram.find? (spfName 17) = some Data.core597 ∧
    Data.core597.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core597.body = spfBody 16 :=
  ⟨Program.find?_of_indexOf? (j := 597) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_18 : coreProgram.find? (spfName 18) = some Data.core640 ∧
    Data.core640.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core640.body = spfBody 17 :=
  ⟨Program.find?_of_indexOf? (j := 640) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_19 : coreProgram.find? (spfName 19) = some Data.core682 ∧
    Data.core682.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core682.body = spfBody 18 :=
  ⟨Program.find?_of_indexOf? (j := 682) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_20 : coreProgram.find? (spfName 20) = some Data.core308 ∧
    Data.core308.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core308.body = spfBody 19 :=
  ⟨Program.find?_of_indexOf? (j := 308) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_21 : coreProgram.find? (spfName 21) = some Data.core309 ∧
    Data.core309.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core309.body = spfBody 20 :=
  ⟨Program.find?_of_indexOf? (j := 309) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_22 : coreProgram.find? (spfName 22) = some Data.core310 ∧
    Data.core310.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core310.body = spfBody 21 :=
  ⟨Program.find?_of_indexOf? (j := 310) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_23 : coreProgram.find? (spfName 23) = some Data.core311 ∧
    Data.core311.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core311.body = spfBody 22 :=
  ⟨Program.find?_of_indexOf? (j := 311) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_24 : coreProgram.find? (spfName 24) = some Data.core312 ∧
    Data.core312.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core312.body = spfBody 23 :=
  ⟨Program.find?_of_indexOf? (j := 312) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_25 : coreProgram.find? (spfName 25) = some Data.core313 ∧
    Data.core313.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core313.body = spfBody 24 :=
  ⟨Program.find?_of_indexOf? (j := 313) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_26 : coreProgram.find? (spfName 26) = some Data.core314 ∧
    Data.core314.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core314.body = spfBody 25 :=
  ⟨Program.find?_of_indexOf? (j := 314) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_27 : coreProgram.find? (spfName 27) = some Data.core315 ∧
    Data.core315.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core315.body = spfBody 26 :=
  ⟨Program.find?_of_indexOf? (j := 315) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_28 : coreProgram.find? (spfName 28) = some Data.core316 ∧
    Data.core316.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core316.body = spfBody 27 :=
  ⟨Program.find?_of_indexOf? (j := 316) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_29 : coreProgram.find? (spfName 29) = some Data.core317 ∧
    Data.core317.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core317.body = spfBody 28 :=
  ⟨Program.find?_of_indexOf? (j := 317) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem spf_found_30 : coreProgram.find? (spfName 30) = some Data.core318 ∧
    Data.core318.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core318.body = spfBody 29 :=
  ⟨Program.find?_of_indexOf? (j := 318) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

/-- **`squeeze_point_from`'s core IR is its meaning**, at every deployed `n`. -/
theorem squeeze_point_from_holds : squeeze_point_from_Spec := by
  intro n hn rd args rets
  simp only [spfDeployed, List.mem_map, List.mem_range] at hn
  obtain ⟨i, hi, rfl⟩ := hn
  have go : ∀ {m c : ℕ} {fn : Fn}, 1 ≤ m → coreProgram.find? (spfName c) = some fn ∧
      fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧ fn.body = spfBody m → c = m + 1 →
      (coreProgram.Rel rd (spfName c) args rets ↔ MeaningSqueezePointFrom c rd args rets) := by
    rintro m c fn hm ⟨h1, h2, h3⟩ rfl
    exact ⟨spf_sound m hm h1 h2 h3 rd args rets, spf_complete m hm h1 h2 h3 rd args rets⟩
  interval_cases i
  · exact go (by decide) spf_found_6 rfl
  · exact go (by decide) spf_found_7 rfl
  · exact go (by decide) spf_found_8 rfl
  · exact go (by decide) spf_found_9 rfl
  · exact go (by decide) spf_found_10 rfl
  · exact go (by decide) spf_found_11 rfl
  · exact go (by decide) spf_found_12 rfl
  · exact go (by decide) spf_found_13 rfl
  · exact go (by decide) spf_found_14 rfl
  · exact go (by decide) spf_found_15 rfl
  · exact go (by decide) spf_found_16 rfl
  · exact go (by decide) spf_found_17 rfl
  · exact go (by decide) spf_found_18 rfl
  · exact go (by decide) spf_found_19 rfl
  · exact go (by decide) spf_found_20 rfl
  · exact go (by decide) spf_found_21 rfl
  · exact go (by decide) spf_found_22 rfl
  · exact go (by decide) spf_found_23 rfl
  · exact go (by decide) spf_found_24 rfl
  · exact go (by decide) spf_found_25 rfl
  · exact go (by decide) spf_found_26 rfl
  · exact go (by decide) spf_found_27 rfl
  · exact go (by decide) spf_found_28 rfl
  · exact go (by decide) spf_found_29 rfl
  · exact go (by decide) spf_found_30 rfl

end
end LeanVM.Guest.B1
