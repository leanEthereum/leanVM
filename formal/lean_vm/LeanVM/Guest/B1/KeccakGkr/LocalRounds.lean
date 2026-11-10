/-
  LeanVM.Guest.B1.KeccakGkr.LocalRounds

  The eleven rounds over the bit position in `keccak_layer` (G:2819-2830): a uniform template, and
  that it computes `localRunF` on the carried sponge.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.PackLoop
public import LeanVM.Guest.B1.KeccakGkr.LayerSpec

/-!
# The rounds over the bit position

Round `i` from the value `a`: `c₀`, `c₂`, `c₃` read at `cur + 3i ..` (`fs_next` into `a`, `a + 3`,
`a + 6`), two zero cells, one `KECCAK` atom on the three rate pairs and the capacity, the
challenge `a + 24` stored at `local[i]`, and the claim
`c₀ + c·(v + (1 + c)(c₂ + (1 + c)c₃))` at `a + 32`, which is `polyEval [c₀, v + c₂ + c₃, c₂, c₃] c`
in characteristic two (`localRoundT`, `localRoundsT`: round `i` at `a₀ + 33i`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- Round `i` of the bit-position sumcheck, from the value `a`. -/
def localRoundT (cur loc vIn : V) (capV : List V) (i a : ℕ) : List Stmt :=
  fsNextT cur (3 * i) a ++ fsNextT cur (3 * i + 1) (a + 3) ++ fsNextT cur (3 * i + 2) (a + 6) ++
    [.atom (.const (.n (a + 9)) (word 0 0)), .atom (.const (.n (a + 10)) (word 0 0)),
      keccakA ([.n (a + 1), .n (a + 2), .n (a + 4), .n (a + 5), .n (a + 7), .n (a + 8),
        .n (a + 9), .n (a + 10)] ++ capV) ((List.range 13).map fun k ↦ .n (a + 11 + k))] ++
    challengeT (.n (a + 11)) (a + 24) ++
    [.atom (.load (.n (a + 24)) loc i), .atom (.const (.n (a + 25)) (word 1 0)),
      .atom (.add (.n (a + 26)) (.n (a + 25)) (.n (a + 24))),
      .atom (.mul (.n (a + 27)) (.n (a + 26)) (.n (a + 6))),
      .atom (.add (.n (a + 28)) (.n (a + 3)) (.n (a + 27))),
      .atom (.mul (.n (a + 29)) (.n (a + 26)) (.n (a + 28))),
      .atom (.add (.n (a + 30)) vIn (.n (a + 29))),
      .atom (.mul (.n (a + 31)) (.n (a + 24)) (.n (a + 30))),
      .atom (.add (.n (a + 32)) (.n a) (.n (a + 31)))]

/-- The `n` rounds from `a₀`: round `0` on the record's claim `vIn` and capacity `capV`, round
`i + 1` on round `i`'s. -/
def localRoundsT (cur loc vIn : V) (capV : List V) (a0 : ℕ) (n : ℕ) : List Stmt :=
  ((List.range n).map fun i ↦
    localRoundT cur loc (if i = 0 then vIn else .n (a0 + 33 * (i - 1) + 32))
      (if i = 0 then capV else capV' (a0 + 33 * (i - 1) + 19)) i (a0 + 33 * i)).flatten
where
  /-- The capacity cells from `b`. -/
  capV' (b : ℕ) : List V := [.n b, .n (b + 1), .n (b + 2), .n (b + 3), .n (b + 4)]

/-- What a round's statements ask of a valuation. -/
structure LocalRoundOk (rd : Reader) (σ : Val) (cur loc vIn : V) (capV : List V) (i a : ℕ) :
    Prop where
  ld0 : LoadHolds rd (σ cur) (3 * i) (σ (.n a))
  pk0 : FsPackOk σ (.n a) (a + 1) dsObserve
  ld2 : LoadHolds rd (σ cur) (3 * i + 1) (σ (.n (a + 3)))
  pk2 : FsPackOk σ (.n (a + 3)) (a + 3 + 1) dsObserve
  ld3 : LoadHolds rd (σ cur) (3 * i + 2) (σ (.n (a + 6)))
  pk3 : FsPackOk σ (.n (a + 6)) (a + 6 + 1) dsObserve
  z0 : σ (.n (a + 9)) = 0
  z1 : σ (.n (a + 10)) = 0
  kc : (Atom.keccak ([.n (a + 1), .n (a + 2), .n (a + 4), .n (a + 5), .n (a + 7), .n (a + 8),
    .n (a + 9), .n (a + 10)] ++ capV) ((List.range 13).map fun k ↦ .n (a + 11 + k)) false
      false).Holds rd σ
  ch : ChallengeOk σ (.n (a + 11)) (a + 24)
  st : LoadHolds rd (σ loc) i (σ (.n (a + 24)))
  v : σ (.n (a + 32)) = σ (.n a) + σ (.n (a + 24)) * (σ vIn + (1 + σ (.n (a + 24))) *
    (σ (.n (a + 3)) + (1 + σ (.n (a + 24))) * σ (.n (a + 6))))

theorem holds_localRoundT {cur loc vIn : V} {capV : List V} {i a : ℕ} {next : Prop}
    {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (localRoundT cur loc vIn capV i a) next kret) :
    LocalRoundOk rd σ cur loc vIn capV i a ∧ next := by
  simp only [localRoundT, holdsList_append, holds_fsNextT] at h
  obtain ⟨⟨l0, p0⟩, ⟨l2, p2⟩, ⟨l3, p3⟩, h⟩ := h
  simp only [holds_challengeT, keccakA, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨z0, z1, kc, ch, st, e25, e26, e27, e28, e29, e30, e31, e32, hn⟩ := h
  refine ⟨⟨l0, p0, l2, p2, l3, p3, by rw [z0, word_zero], by rw [z1, word_zero], kc, ch, st, ?_⟩, hn⟩
  rw [e32, e31, e30, e29, e28, e27, e26, e25, word_one]

/-- The guest's claim update is the round polynomial's value (characteristic two). -/
theorem local_value (c0 c2 c3 v c : E) :
    c0 + c * (v + (1 + c) * (c2 + (1 + c) * c3)) = polyEval [c0, v + sumE [c2, c3], c2, c3] c := by
  have h2 : (2 : E) = 0 := by rw [show (2 : E) = 1 + 1 by norm_num]; exact e_add_self 1
  simp only [polyEval, sumE, List.foldl, List.foldr]
  linear_combination (c * c * c3) * h2

/-- **A squeeze of three read words**, two zero cells and the capacity. -/
theorem sq3_atoms {a o : ℕ} {z0 z1 : V} {capV : List V} {cap : List E}
    (p1 : FsPackOk σ (.n a) (a + 1) dsObserve) (p2 : FsPackOk σ (.n (a + 3)) (a + 3 + 1) dsObserve)
    (p3 : FsPackOk σ (.n (a + 6)) (a + 6 + 1) dsObserve)
    (hk : (Atom.keccak ([V.n (a + 1), .n (a + 2), .n (a + 4), .n (a + 5), .n (a + 7), .n (a + 8),
      z0, z1] ++ capV) ((List.range 13).map fun k ↦ .n (o + k)) false false).Holds rd σ)
    (hch : ChallengeOk σ (.n o) (o + 13)) (hz0 : σ z0 = 0) (hz1 : σ z1 = 0)
    (hc : capV.map σ = cap) :
    σ (.n (o + 13)) = ((⟨cap, []⟩ : Fs).absorbAll [σ (.n a), σ (.n (a + 3)), σ (.n (a + 6))]
        dsObserve).squeeze.1 ∧
      [σ (.n (o + 8)), σ (.n (o + 9)), σ (.n (o + 10)), σ (.n (o + 11)), σ (.n (o + 12))] =
        ((⟨cap, []⟩ : Fs).absorbAll [σ (.n a), σ (.n (a + 3)), σ (.n (a + 6))]
          dsObserve).squeeze.2.cap := by
  have s0 := fsNext_scalar p1
  have s2 := fsNext_scalar p2
  have s3 := fsNext_scalar p3
  have habs : (⟨cap, []⟩ : Fs).absorbAll [σ (.n a), σ (.n (a + 3)), σ (.n (a + 6))] dsObserve =
      ⟨cap, [(σ (.n a), dsObserve), (σ (.n (a + 3)), dsObserve), (σ (.n (a + 6)), dsObserve)]⟩ :=
    rfl
  have hin : ([V.n (a + 1), .n (a + 2), .n (a + 4), .n (a + 5), .n (a + 7), .n (a + 8), z0, z1] ++
      capV).map σ = rateOf [(σ (.n a), dsObserve), (σ (.n (a + 3)), dsObserve),
        (σ (.n (a + 6)), dsObserve)] ++ cap := by
    rw [rateOf_three, ← s0, ← s2, ← s3, List.map_append, hc]
    simp only [List.map_cons, List.map_nil, hz0, hz1, List.cons_append, List.nil_append]
  have := squeeze_atom (s := ⟨cap, [(σ (.n a), dsObserve), (σ (.n (a + 3)), dsObserve),
    (σ (.n (a + 6)), dsObserve)]⟩) hk hin (by simpa [range13_map] using hch)
  simp only [range13_map, List.drop, List.map_cons, List.map_nil] at this
  rw [habs]
  exact ⟨this.1, this.2⟩

/-- `localRunF`'s first round. -/
theorem localRunF_cons (c0 c2 c3 v : E) (ms : List (E × E × E)) (s : Fs) :
    localRunF ((c0, c2, c3) :: ms) v s =
      (((s.absorbAll [c0, c2, c3] dsObserve).squeeze.1 :: (localRunF ms (polyEval
          [c0, v + sumE [c2, c3], c2, c3] (s.absorbAll [c0, c2, c3] dsObserve).squeeze.1)
          (s.absorbAll [c0, c2, c3] dsObserve).squeeze.2).1.1,
        (localRunF ms (polyEval [c0, v + sumE [c2, c3], c2, c3]
          (s.absorbAll [c0, c2, c3] dsObserve).squeeze.1)
          (s.absorbAll [c0, c2, c3] dsObserve).squeeze.2).1.2),
        (localRunF ms (polyEval [c0, v + sumE [c2, c3], c2, c3]
          (s.absorbAll [c0, c2, c3] dsObserve).squeeze.1)
          (s.absorbAll [c0, c2, c3] dsObserve).squeeze.2).2) := rfl

/-- `localRunF` of a prefix, then one more round. -/
theorem localRunF_snoc : ∀ (ms : List (E × E × E)) (m : E × E × E) (v : E) (s : Fs),
    localRunF (ms ++ [m]) v s =
      (((localRunF ms v s).1.1 ++ [((localRunF ms v s).2.absorbAll [m.1, m.2.1, m.2.2]
          dsObserve).squeeze.1],
        polyEval [m.1, (localRunF ms v s).1.2 + sumE [m.2.1, m.2.2], m.2.1, m.2.2]
          ((localRunF ms v s).2.absorbAll [m.1, m.2.1, m.2.2] dsObserve).squeeze.1),
        ((localRunF ms v s).2.absorbAll [m.1, m.2.1, m.2.2] dsObserve).squeeze.2)
  | [], (c0, c2, c3), v, s => rfl
  | (d0, d2, d3) :: ms, m, v, s => by
    rw [List.cons_append, localRunF_cons, localRunF_cons, localRunF_snoc ms m]
    simp only [List.cons_append]

theorem localRoundsT_succ (cur loc vIn : V) (capV : List V) (a0 n : ℕ) :
    localRoundsT cur loc vIn capV a0 (n + 1) = localRoundsT cur loc vIn capV a0 n ++
      localRoundT cur loc (if n = 0 then vIn else .n (a0 + 33 * (n - 1) + 32))
        (if n = 0 then capV else localRoundsT.capV' (a0 + 33 * (n - 1) + 19)) n (a0 + 33 * n) := by
  simp [localRoundsT, List.range_succ, List.map_append, List.flatten_append]

theorem localRunF_length : ∀ (ms : List (E × E × E)) (v : E) (s : Fs),
    (localRunF ms v s).1.1.length = ms.length
  | [], _, _ => rfl
  | (c0, c2, c3) :: ms, v, s => by
    simp only [localRunF, List.length_cons, localRunF_length ms]

theorem flatMap_triples_length (ms : List (E × E × E)) :
    (ms.flatMap fun m ↦ [m.1, m.2.1, m.2.2]).length = 3 * ms.length := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp [List.flatMap_cons, ih]; ring

/-- **The rounds compute `localRunF`**: the messages read from the cursor, the challenges stored at
`local`, the last claim (`a₀ + 33(n-1) + 32`) and capacity (`a₀ + 33(n-1) + 19 ..`). -/
theorem localRounds_run {cur loc vIn : V} {capV : List V} {a0 : ℕ} {cap : List E}
    (hc : capV.map σ = cap) : ∀ (n : ℕ) {next : Prop} {kret : List E → Prop}, 1 ≤ n →
    Stmt.HoldsList C rd σ (localRoundsT cur loc vIn capV a0 n) next kret →
    (∃ msgs : List (E × E × E), msgs.length = n ∧
      ReadsAt rd (σ cur) (msgs.flatMap fun m ↦ [m.1, m.2.1, m.2.2]) ∧
      ReadsAt rd (σ loc) (localRunF msgs (σ vIn) ⟨cap, []⟩).1.1 ∧
      (localRunF msgs (σ vIn) ⟨cap, []⟩).1.2 = σ (.n (a0 + 33 * (n - 1) + 32)) ∧
      (localRunF msgs (σ vIn) ⟨cap, []⟩).2 =
        ⟨(localRoundsT.capV' (a0 + 33 * (n - 1) + 19)).map σ, []⟩) ∧ next
  | 0, _, _, h, _ => absurd h (by omega)
  | n + 1, next, kret, _, h => by
    rw [localRoundsT_succ, holdsList_append] at h
    -- the earlier rounds, then round `n`
    have step : ∀ (msgs : List (E × E × E)) (vI : V) (cV : List V),
        msgs.length = n → ReadsAt rd (σ cur) (msgs.flatMap fun m ↦ [m.1, m.2.1, m.2.2]) →
        ReadsAt rd (σ loc) (localRunF msgs (σ vIn) ⟨cap, []⟩).1.1 →
        (localRunF msgs (σ vIn) ⟨cap, []⟩).1.2 = σ vI →
        (localRunF msgs (σ vIn) ⟨cap, []⟩).2 = ⟨cV.map σ, []⟩ →
        LocalRoundOk rd σ cur loc vI cV n (a0 + 33 * n) →
        ∃ msgs' : List (E × E × E), msgs'.length = n + 1 ∧
          ReadsAt rd (σ cur) (msgs'.flatMap fun m ↦ [m.1, m.2.1, m.2.2]) ∧
          ReadsAt rd (σ loc) (localRunF msgs' (σ vIn) ⟨cap, []⟩).1.1 ∧
          (localRunF msgs' (σ vIn) ⟨cap, []⟩).1.2 = σ (.n (a0 + 33 * (n + 1 - 1) + 32)) ∧
          (localRunF msgs' (σ vIn) ⟨cap, []⟩).2 =
            ⟨(localRoundsT.capV' (a0 + 33 * (n + 1 - 1) + 19)).map σ, []⟩ := by
      intro msgs vI cV hl hr hs hv hcs ok
      set a := a0 + 33 * n with ha
      have q := sq3_atoms (rd := rd) (a := a) (o := a + 11) (z0 := .n (a + 9)) (z1 := .n (a + 10))
        (capV := cV) (cap := cV.map σ) ok.pk0 ok.pk2 ok.pk3 ok.kc ok.ch ok.z0 ok.z1 rfl
      have e24 : a + 11 + 13 = a + 24 := by omega
      rw [e24] at q
      refine ⟨msgs ++ [(σ (.n a), σ (.n (a + 3)), σ (.n (a + 6)))], by simp [hl], ?_, ?_, ?_, ?_⟩
      · rw [List.flatMap_append, readsAt_append, flatMap_triples_length, hl]
        refine ⟨hr, fun k hk => ?_⟩
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons,
          List.length_nil] at hk
        rw [loadHolds_mul_gen_pow]
        interval_cases k
        · simpa using ok.ld0
        · simpa using ok.ld2
        · simpa using ok.ld3
      · rw [localRunF_snoc, hcs, readsAt_append, localRunF_length, hl]
        refine ⟨hs, fun k hk => ?_⟩
        simp only [List.length_cons, List.length_nil] at hk
        interval_cases k
        rw [loadHolds_mul_gen_pow, Nat.add_zero, ← q.1]
        exact ok.st
      · rw [localRunF_snoc, hcs, hv, ← q.1, ← local_value, ← ok.v]
        congr 3
      · rw [localRunF_snoc, hcs]
        rw [show ((⟨cV.map σ, []⟩ : Fs).absorbAll [σ (.n a), σ (.n (a + 3)), σ (.n (a + 6))]
          dsObserve).squeeze.2 = ⟨((⟨cV.map σ, []⟩ : Fs).absorbAll [σ (.n a), σ (.n (a + 3)),
            σ (.n (a + 6))] dsObserve).squeeze.2.cap, []⟩ from rfl, ← q.2]
        simp only [localRoundsT.capV', List.map_cons, List.map_nil]
        congr 1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [localRoundsT, List.range_zero, List.map_nil, List.flatten_nil, Stmt.HoldsList,
        ↓reduceIte] at h
      obtain ⟨ok, hnext⟩ := holds_localRoundT h
      exact ⟨step [] vIn capV rfl (readsAt_nil _ _) (readsAt_nil _ _) rfl (by rw [hc]; rfl)
        (by simpa using ok), hnext⟩
    · obtain ⟨⟨msgs, hl, hr, hs, hv, hcs⟩, hround⟩ := localRounds_run hc n hn h
      have hn0 : n ≠ 0 := by omega
      simp only [hn0, ↓reduceIte] at hround
      obtain ⟨ok, hnext⟩ := holds_localRoundT hround
      exact ⟨step msgs _ _ hl hr hs hv hcs ok, hnext⟩

end
end LeanVM.Guest.B1.VerifySub
