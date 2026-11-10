/-
  LeanVM.Guest.B1.KeccakGkr.Plain

  B1 of `keccak_plain_rounds`: its two specializations compute plain sumcheck rounds of degree
  two on the carried sponge.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Lib

/-!
# `keccak_plain_rounds` (TRIAGE G #61)

`keccak_plain_rounds(fs0..fs4, p0, p1, cursor, value, point, n, k0)` (G:2878-2903): its
specializations `__L6_L0` (`Data.core269`) and `__L4_L1` (`Data.core271`) copy the capacity, run
`n` rounds, each a template `plainRoundT` (`c₀`, `c₂` read and packed by `fs_next`, one `KECCAK`
atom on the waiting scalars' rate cells and the capacity, `challenge_from_state`, the challenge
stored at `point[i]`, the claim `c₀ + c·((claim + c₂) + c·c₂)`), and return the last capacity,
the cursor `·g^(2n)` and the claim. The bodies are the templates by kernel evaluation
(`stmtsEqb_sound`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## A round -/

/-- One plain round at index `i`: `c₀` read into `a`, `c₂` into `a + 10` (`fs_next`), the
statements `mid` (constants), the `KECCAK` atom on `ins` writing `o .. o + 12`,
`challenge_from_state` from `o + 13` (the challenge `o + 19`), then the claim from `vIn`: `o + 20`
`= vIn + c₂`, the challenge stored at `pt[i]`, `o + 24 = c₀ + c·(o + 20 + c·c₂)`. -/
def plainRoundT (cur pt vIn : V) (ins : List V) (mid : List Stmt) (i a o : ℕ) : List Stmt :=
  fsNextT cur (2 * i) a ++ fsNextT cur (2 * i + 1) (a + 10) ++ mid ++
    [keccakA ins ((List.range 13).map fun k ↦ .n (o + k))] ++
    challengeT (.n o) (.n (o + 1)) (o + 13) ++
    [.atom (.add (.n (o + 20)) vIn (.n (a + 10))), .atom (.load (.n (o + 19)) pt i),
      .atom (.mul (.n (o + 21)) (.n (o + 19)) (.n (a + 10))),
      .atom (.add (.n (o + 22)) (.n (o + 20)) (.n (o + 21))),
      .atom (.mul (.n (o + 23)) (.n (o + 19)) (.n (o + 22))),
      .atom (.add (.n (o + 24)) (.n a) (.n (o + 23)))]

/-- What a round's statements ask of a valuation. -/
structure PlainRoundOk (rd : Reader) (σ : Val) (cur pt vIn : V) (ins : List V) (i a o : ℕ) :
    Prop where
  ld0 : LoadHolds rd (σ cur) (2 * i) (σ (.n a))
  pk0 : FsPackOk σ (.n a) (a + 1) dsObserve
  ld2 : LoadHolds rd (σ cur) (2 * i + 1) (σ (.n (a + 10)))
  pk2 : FsPackOk σ (.n (a + 10)) (a + 10 + 1) dsObserve
  kc : (Atom.keccak ins ((List.range 13).map fun k ↦ .n (o + k)) false false).Holds rd σ
  ch : ChallengeOk σ (.n o) (.n (o + 1)) (o + 13)
  st : LoadHolds rd (σ pt) i (σ (.n (o + 19)))
  v : σ (.n (o + 24)) =
    σ (.n a) + σ (.n (o + 19)) * ((σ vIn + σ (.n (a + 10))) + σ (.n (o + 19)) * σ (.n (a + 10)))

theorem holds_plainRoundT {cur pt vIn : V} {ins : List V} {mid : List Stmt} {i a o : ℕ}
    {kret : List E → Prop} (hmid : Stmt.noRetList mid = true) {next : Prop}
    (h : Stmt.HoldsList C rd σ (plainRoundT cur pt vIn ins mid i a o) next kret) :
    (PlainRoundOk rd σ cur pt vIn ins i a o ∧ Stmt.HoldsList C rd σ mid True kret) ∧ next := by
  simp only [plainRoundT, holdsList_append, holds_fsNextT] at h
  obtain ⟨⟨l0, p0⟩, ⟨l2, p2⟩, h⟩ := h
  obtain ⟨hm, h⟩ := (holdsList_noRet mid hmid _ _).mp h
  simp only [holds_challengeT, keccakA, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨kc, ch, e20, st, e21, e22, e23, e24, hn⟩ := h
  refine ⟨⟨⟨l0, p0, l2, p2, kc, ch, st, ?_⟩, hm⟩, hn⟩
  rw [e24, e23, e22, e21, e20]

/-! ## A round on the carried sponge -/

theorem range13_map (f : ℕ → V) :
    (List.range 13).map f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12] :=
  rfl

/-- The sponge of a plain round: `c₀`, `c₂` absorbed after the waiting scalars, squeezed. -/
def plainSq (s : Fs) (c0 c2 : E) : E × Fs := ((s.absorb c0 dsObserve).absorb c2 dsObserve).squeeze

/-- **A round with nothing waiting**: the atom reads `c₀`'s and `c₂`'s rate cells, four zero
cells and the capacity; the challenge `o + 19` and the outputs `o + 8 .. o + 12` are the
squeeze's. -/
theorem plain_round_sq0 {cur pt vIn : V} {zs capV : List V} {i a o : ℕ} {cap : List E}
    (h : PlainRoundOk rd σ cur pt vIn ([.n (a + 7), .n (a + 9), .n (a + 17), .n (a + 19)] ++ zs ++ capV)
      i a o)
    (hz : zs.map σ = [0, 0, 0, 0]) (hc : capV.map σ = cap) :
    σ (.n (o + 19)) = (plainSq ⟨cap, []⟩ (σ (.n a)) (σ (.n (a + 10)))).1 ∧
      [σ (.n (o + 8)), σ (.n (o + 9)), σ (.n (o + 10)), σ (.n (o + 11)), σ (.n (o + 12))] =
        (plainSq ⟨cap, []⟩ (σ (.n a)) (σ (.n (a + 10)))).2.cap := by
  obtain ⟨-, -, hcan, -⟩ := keccak_outs h.kc
  have c0 : IsCanonical128 (σ (.n (a + 7))) := hcan _ (by simp)
  have c2 : IsCanonical128 (σ (.n (a + 10 + 7))) := hcan _ (by simp)
  have s0 := fsNext_scalar h.pk0 c0
  have s2 := fsNext_scalar h.pk2 c2
  have habs : ((⟨cap, []⟩ : Fs).absorb (σ (.n a)) dsObserve).absorb (σ (.n (a + 10))) dsObserve =
      ⟨cap, [(σ (.n a), dsObserve), (σ (.n (a + 10)), dsObserve)]⟩ := rfl
  have hin : ([V.n (a + 7), .n (a + 9), .n (a + 17), .n (a + 19)] ++ zs ++ capV).map σ =
      rateOf [(σ (.n a), dsObserve), (σ (.n (a + 10)), dsObserve)] ++ cap := by
    rw [rateOf_two, ← s0, ← s2, List.map_append, List.map_append, hz, hc]
    rfl
  have := squeeze_atom (s := ⟨cap, [(σ (.n a), dsObserve), (σ (.n (a + 10)), dsObserve)]⟩) h.kc hin
    (by simpa [range13_map] using h.ch)
  simp only [range13_map, List.drop, List.map_cons, List.map_nil] at this
  rw [plainSq, habs]
  exact ⟨this.1, this.2⟩

/-- **A round with one scalar `w` waiting**, its rate cells `p0`, `p1`: the atom reads them,
`c₀`'s and `c₂`'s rate cells, two zero cells and the capacity. -/
theorem plain_round_sq1 {cur pt vIn p0 p1 : V} {zs capV : List V} {i a o : ℕ} {cap : List E} {w : E}
    (h : PlainRoundOk rd σ cur pt vIn
      ([p0, p1, .n (a + 7), .n (a + 9), .n (a + 17), .n (a + 19)] ++ zs ++ capV) i a o)
    (hp : IsCanonical128 (σ p0) → (σ p0, σ p1) = Keccak.scalarCells w dsObserve)
    (hz : zs.map σ = [0, 0]) (hc : capV.map σ = cap) :
    σ (.n (o + 19)) = (plainSq ⟨cap, [(w, dsObserve)]⟩ (σ (.n a)) (σ (.n (a + 10)))).1 ∧
      [σ (.n (o + 8)), σ (.n (o + 9)), σ (.n (o + 10)), σ (.n (o + 11)), σ (.n (o + 12))] =
        (plainSq ⟨cap, [(w, dsObserve)]⟩ (σ (.n a)) (σ (.n (a + 10)))).2.cap := by
  obtain ⟨-, -, hcan, -⟩ := keccak_outs h.kc
  have c0 : IsCanonical128 (σ (.n (a + 7))) := hcan _ (by simp)
  have c2 : IsCanonical128 (σ (.n (a + 10 + 7))) := hcan _ (by simp)
  have s0 := fsNext_scalar h.pk0 c0
  have s2 := fsNext_scalar h.pk2 c2
  have hp := hp (hcan _ (by simp))
  have habs : ((⟨cap, [(w, dsObserve)]⟩ : Fs).absorb (σ (.n a)) dsObserve).absorb
      (σ (.n (a + 10))) dsObserve =
      ⟨cap, [(w, dsObserve), (σ (.n a), dsObserve), (σ (.n (a + 10)), dsObserve)]⟩ := rfl
  have hin : ([p0, p1, .n (a + 7), .n (a + 9), .n (a + 17), .n (a + 19)] ++ zs ++ capV).map σ =
      rateOf [(w, dsObserve), (σ (.n a), dsObserve), (σ (.n (a + 10)), dsObserve)] ++ cap := by
    rw [rateOf_three, ← hp, ← s0, ← s2, List.map_append, List.map_append, hz, hc]
    rfl
  have := squeeze_atom (s := ⟨cap, [(w, dsObserve), (σ (.n a), dsObserve),
    (σ (.n (a + 10)), dsObserve)]⟩) h.kc hin (by simpa [range13_map] using h.ch)
  simp only [range13_map, List.drop, List.map_cons, List.map_nil] at this
  rw [plainSq, habs]
  exact ⟨this.1, this.2⟩

/-- `plainRun`'s first round, from the facts of its squeeze. -/
theorem plainRun_step {c0 c2 v v' ch : E} {s : Fs} {cap' : List E} {rest : List (E × E)}
    (hch : (plainSq s c0 c2).1 = ch) (hcap : (plainSq s c0 c2).2.cap = cap')
    (hv : c0 + ch * ((v + c2) + ch * c2) = v') :
    plainRun ((c0, c2) :: rest) v s =
      (ch :: (plainRun rest v' ⟨cap', []⟩).1, (plainRun rest v' ⟨cap', []⟩).2) := by
  have e : (plainSq s c0 c2).2 = ⟨cap', []⟩ := by rw [← hcap]; rfl
  simp only [plainRun]
  rw [← plainSq, e, hch, hv]

/-! ## The two specializations -/

theorem word_4096 : word 4096 0 0 = gen ^ (2 * 6) := by
  rw [show (4096 : ℕ) = 2 ^ (2 * 6) from rfl]; exact word_two_pow (by decide)

theorem word_256 : word 256 0 0 = gen ^ (2 * 4) := by
  rw [show (256 : ℕ) = 2 ^ (2 * 4) from rfl]; exact word_two_pow (by decide)

/-- The capacity cells from `b`. -/
def capV (b : ℕ) : List V := [.n b, .n (b + 1), .n (b + 2), .n (b + 3), .n (b + 4)]

/-- The cells a round's atom reads with nothing waiting: `c₀`'s, `c₂`'s, the zeros, the
capacity from `cb`. -/
def plainIns0 (a : ℕ) (zs : List V) (cb : ℕ) : List V :=
  [.n (a + 7), .n (a + 9), .n (a + 17), .n (a + 19)] ++ zs ++ capV cb

/-- The four zero cells of `__L6_L0` (and the constant `1` before them). -/
def plainMid60 : List Stmt :=
  [.atom (.const (.n 35) (word 1 0 0)), .atom (.const (.n 36) (word 0 0 0)),
    .atom (.const (.n 37) (word 0 0 0)), .atom (.const (.n 38) (word 0 0 0)),
    .atom (.const (.n 39) (word 0 0 0))]

/-- `keccak_plain_rounds__L6_L0`'s body. -/
def plain60T : List Stmt :=
  [.atom (.copy (.n 10) (.n 0)),
    .atom (.copy (.n 11) (.n 1)),
    .atom (.copy (.n 12) (.n 2)),
    .atom (.copy (.n 13) (.n 3)),
    .atom (.copy (.n 14) (.n 4))] ++
  plainRoundT (.n 7) (.n 9) (.n 8) (plainIns0 15 [.n 36, .n 37, .n 38, .n 39] 10) plainMid60 0 15 40 ++
  plainRoundT (.n 7) (.n 9) (.n 64) (plainIns0 65 [.n 36, .n 37, .n 38, .n 39] 48) [] 1 65 85 ++
  plainRoundT (.n 7) (.n 9) (.n 109) (plainIns0 110 [.n 36, .n 37, .n 38, .n 39] 93) [] 2 110 130 ++
  plainRoundT (.n 7) (.n 9) (.n 154) (plainIns0 155 [.n 36, .n 37, .n 38, .n 39] 138) [] 3 155 175 ++
  plainRoundT (.n 7) (.n 9) (.n 199) (plainIns0 200 [.n 36, .n 37, .n 38, .n 39] 183) [] 4 200 220 ++
  plainRoundT (.n 7) (.n 9) (.n 244) (plainIns0 245 [.n 36, .n 37, .n 38, .n 39] 228) [] 5 245 265 ++
  [.atom (.copy (.n 290) (.n 273)),
    .atom (.copy (.n 291) (.n 274)),
    .atom (.copy (.n 292) (.n 275)),
    .atom (.copy (.n 293) (.n 276)),
    .atom (.copy (.n 294) (.n 277)),
    .atom (.const (.n 295) (word 4096 0 0)), .atom (.mul (.n 296) (.n 7) (.n 295)),
    .atom (.copy (.n 297) (.n 296)), .atom (.copy (.n 298) (.n 289)),
    .ret [.n 290, .n 291, .n 292, .n 293, .n 294, .n 297, .n 298]]

theorem body60 : Data.core269.body = plain60T := stmtsEqb_sound (by decide +kernel)

/-- The two zero cells of `__L4_L1`'s first round. -/
def plainMid41a : List Stmt :=
  [.atom (.const (.n 37) (word 0 0 0)), .atom (.const (.n 38) (word 0 0 0))]

/-- The four zero cells of `__L4_L1`'s later rounds (and the constant `1` before them). -/
def plainMid41b : List Stmt :=
  [.atom (.const (.n 84) (word 1 0 0)), .atom (.const (.n 85) (word 0 0 0)),
    .atom (.const (.n 86) (word 0 0 0)), .atom (.const (.n 87) (word 0 0 0)),
    .atom (.const (.n 88) (word 0 0 0))]

/-- `keccak_plain_rounds__L4_L1`'s body. -/
def plain41T : List Stmt :=
  [.atom (.copy (.n 10) (.n 0)),
    .atom (.copy (.n 11) (.n 1)),
    .atom (.copy (.n 12) (.n 2)),
    .atom (.copy (.n 13) (.n 3)),
    .atom (.copy (.n 14) (.n 4)),
    .atom (.copy (.n 15) (.n 5)),
    .atom (.copy (.n 16) (.n 6))] ++
  plainRoundT (.n 7) (.n 9) (.n 8)
    ([.n 15, .n 16, .n 24, .n 26, .n 34, .n 36] ++ [.n 37, .n 38] ++ capV 10) plainMid41a 0 17 39 ++
  plainRoundT (.n 7) (.n 9) (.n 63) (plainIns0 64 [.n 85, .n 86, .n 87, .n 88] 47) plainMid41b 1 64 89 ++
  plainRoundT (.n 7) (.n 9) (.n 113) (plainIns0 114 [.n 85, .n 86, .n 87, .n 88] 97) [] 2 114 134 ++
  plainRoundT (.n 7) (.n 9) (.n 158) (plainIns0 159 [.n 85, .n 86, .n 87, .n 88] 142) [] 3 159 179 ++
  [.atom (.copy (.n 204) (.n 187)),
    .atom (.copy (.n 205) (.n 188)),
    .atom (.copy (.n 206) (.n 189)),
    .atom (.copy (.n 207) (.n 190)),
    .atom (.copy (.n 208) (.n 191)),
    .atom (.const (.n 209) (word 256 0 0)), .atom (.mul (.n 210) (.n 7) (.n 209)),
    .atom (.copy (.n 211) (.n 210)), .atom (.copy (.n 212) (.n 203)),
    .ret [.n 204, .n 205, .n 206, .n 207, .n 208, .n 211, .n 212]]

theorem body41 : Data.core271.body = plain41T := stmtsEqb_sound (by decide +kernel)

theorem find_plain60 : coreProgram.find? "keccak_plain_rounds__L6_L0" = some Data.core269 :=
  Program.find?_of_indexOf? (j := 269) (by decide +kernel) rfl

theorem plain60_sound (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd "keccak_plain_rounds__L6_L0" args rets) :
    MeaningPlainRounds 6 0 rd args rets := by
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_plain60 args rets).mp h
  simp only [Data.core269, List.map_cons, List.map_nil] at hpar hb
  subst hpar
  rw [body60] at hb
  simp only [plain60T, holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hb
  obtain ⟨e10, e11, e12, e13, e14, hb⟩ := hb
  obtain ⟨⟨r0, m0⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨⟨r1, m1⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨⟨r2, m2⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨⟨r3, m3⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨⟨r4, m4⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨⟨r5, m5⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨e290, e291, e292, e293, e294, e295, e296, e297, e298, hret⟩ := hb
  simp only [plainMid60, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at m0
  obtain ⟨-, m36, m37, m38, m39⟩ := m0
  have hz : [V.n 36, .n 37, .n 38, .n 39].map σ = [0, 0, 0, 0] := by
    simp only [List.map_cons, List.map_nil, m36, m37, m38, m39, word_zero]
  have q0 := plain_round_sq0 (cap := [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)]) r0 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd, e10, e11, e12, e13, e14])
  have v0 := r0.v
  simp only [Nat.reduceAdd] at q0 v0
  have q1 := plain_round_sq0 (cap := [σ (.n 48), σ (.n 49), σ (.n 50), σ (.n 51), σ (.n 52)]) r1 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have v1 := r1.v
  simp only [Nat.reduceAdd] at q1 v1
  have q2 := plain_round_sq0 (cap := [σ (.n 93), σ (.n 94), σ (.n 95), σ (.n 96), σ (.n 97)]) r2 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have v2 := r2.v
  simp only [Nat.reduceAdd] at q2 v2
  have q3 := plain_round_sq0 (cap := [σ (.n 138), σ (.n 139), σ (.n 140), σ (.n 141), σ (.n 142)]) r3 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have v3 := r3.v
  simp only [Nat.reduceAdd] at q3 v3
  have q4 := plain_round_sq0 (cap := [σ (.n 183), σ (.n 184), σ (.n 185), σ (.n 186), σ (.n 187)]) r4 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have v4 := r4.v
  simp only [Nat.reduceAdd] at q4 v4
  have q5 := plain_round_sq0 (cap := [σ (.n 228), σ (.n 229), σ (.n 230), σ (.n 231), σ (.n 232)]) r5 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have v5 := r5.v
  simp only [Nat.reduceAdd] at q5 v5
  have hrun : plainRun [(σ (.n 15), σ (.n 25)), (σ (.n 65), σ (.n 75)), (σ (.n 110), σ (.n 120)),
      (σ (.n 155), σ (.n 165)), (σ (.n 200), σ (.n 210)), (σ (.n 245), σ (.n 255))] (σ (.n 8))
      ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ =
      ([σ (.n 59), σ (.n 104), σ (.n 149), σ (.n 194), σ (.n 239), σ (.n 284)], σ (.n 289),
        ⟨[σ (.n 273), σ (.n 274), σ (.n 275), σ (.n 276), σ (.n 277)], []⟩) := by
    rw [plainRun_step q0.1.symm q0.2.symm v0.symm, plainRun_step q1.1.symm q1.2.symm v1.symm,
      plainRun_step q2.1.symm q2.2.symm v2.symm, plainRun_step q3.1.symm q3.2.symm v3.symm,
      plainRun_step q4.1.symm q4.2.symm v4.symm, plainRun_step q5.1.symm q5.2.symm v5.symm]
    rfl
  obtain ⟨-, -, hcan, -⟩ := keccak_outs (rd := rd) r0.kc
  refine ⟨fun c hc => hcan c ?_, [(σ (.n 15), σ (.n 25)), (σ (.n 65), σ (.n 75)),
    (σ (.n 110), σ (.n 120)), (σ (.n 155), σ (.n 165)), (σ (.n 200), σ (.n 210)),
    (σ (.n 245), σ (.n 255))], rfl, ?_, fun w _ => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    simp only [plainIns0, capV, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, Nat.reduceAdd, e10, e11, e12, e13, e14]
    clear * - hc
    tauto
  · intro k hk
    simp only [List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
      List.append_nil, List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact r0.ld0
    · exact r0.ld2
    · exact r1.ld0
    · exact r1.ld2
    · exact r2.ld0
    · exact r2.ld2
    · exact r3.ld0
    · exact r3.ld2
    · exact r4.ld0
    · exact r4.ld2
    · exact r5.ld0
    · exact r5.ld2
  · simp only [plainStart, show ¬ (0 : ℕ) = 1 by decide, ↓reduceIte, hrun]
    refine ⟨?_, ?_⟩
    · intro k hk
      simp only [List.length_cons, List.length_nil] at hk
      interval_cases k
      · exact r0.st
      · exact r1.st
      · exact r2.st
      · exact r3.st
      · exact r4.st
      · exact r5.st
    · rw [← hret]
      simp only [List.map_cons, List.map_nil, e290, e291, e292, e293, e294, e297, e296, e295, e298,
        List.cons_append, List.nil_append, word_4096]

theorem find_plain41 : coreProgram.find? "keccak_plain_rounds__L4_L1" = some Data.core271 :=
  Program.find?_of_indexOf? (j := 271) (by decide +kernel) rfl

theorem plain41_sound (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd "keccak_plain_rounds__L4_L1" args rets) :
    MeaningPlainRounds 4 1 rd args rets := by
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_plain41 args rets).mp h
  simp only [Data.core271, List.map_cons, List.map_nil] at hpar hb
  subst hpar
  rw [body41] at hb
  simp only [plain41T, holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hb
  obtain ⟨e10, e11, e12, e13, e14, e15, e16, hb⟩ := hb
  obtain ⟨⟨r0, m0⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨⟨r1, m1⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨⟨r2, -⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨⟨r3, -⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨e204, e205, e206, e207, e208, e209, e210, e211, e212, hret⟩ := hb
  simp only [plainMid41a, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at m0
  simp only [plainMid41b, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at m1
  obtain ⟨m37, m38⟩ := m0
  obtain ⟨-, m85, m86, m87, m88⟩ := m1
  have hz0 : [V.n 37, .n 38].map σ = [0, 0] := by
    simp only [List.map_cons, List.map_nil, m37, m38, word_zero]
  have hz : [V.n 85, .n 86, .n 87, .n 88].map σ = [0, 0, 0, 0] := by
    simp only [List.map_cons, List.map_nil, m85, m86, m87, m88, word_zero]
  have v0 := r0.v
  have v1 := r1.v
  have v2 := r2.v
  have v3 := r3.v
  simp only [Nat.reduceAdd] at v0 v1 v2 v3
  obtain ⟨-, -, hcan, -⟩ := keccak_outs (rd := rd) r0.kc
  refine ⟨fun c hc => hcan c ?_, [(σ (.n 17), σ (.n 27)), (σ (.n 64), σ (.n 74)),
    (σ (.n 114), σ (.n 124)), (σ (.n 159), σ (.n 169))], rfl, ?_, fun w hw => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    simp only [capV, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, Nat.reduceAdd, e10, e11, e12, e13, e14]
    clear * - hc
    tauto
  · intro k hk
    simp only [List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
      List.append_nil, List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact r0.ld0
    · exact r0.ld2
    · exact r1.ld0
    · exact r1.ld2
    · exact r2.ld0
    · exact r2.ld2
    · exact r3.ld0
    · exact r3.ld2
  have hp : IsCanonical128 (σ (.n 15)) → (σ (.n 15), σ (.n 16)) = Keccak.scalarCells w dsObserve := by
    intro hc; rw [e15, e16]; rw [e15] at hc; exact hw rfl hc
  have q0 := plain_round_sq1 (cap := [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)]) r0 hp hz0
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd, e10, e11, e12, e13, e14])
  have q1 := plain_round_sq0 (cap := [σ (.n 47), σ (.n 48), σ (.n 49), σ (.n 50), σ (.n 51)]) r1 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q2 := plain_round_sq0 (cap := [σ (.n 97), σ (.n 98), σ (.n 99), σ (.n 100), σ (.n 101)]) r2 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q3 := plain_round_sq0 (cap := [σ (.n 142), σ (.n 143), σ (.n 144), σ (.n 145), σ (.n 146)]) r3
    hz (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  simp only [Nat.reduceAdd] at q0 q1 q2 q3
  have hrun : plainRun [(σ (.n 17), σ (.n 27)), (σ (.n 64), σ (.n 74)), (σ (.n 114), σ (.n 124)),
      (σ (.n 159), σ (.n 169))] (σ (.n 8))
      ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], [(w, dsObserve)]⟩ =
      ([σ (.n 58), σ (.n 108), σ (.n 153), σ (.n 198)], σ (.n 203),
        ⟨[σ (.n 187), σ (.n 188), σ (.n 189), σ (.n 190), σ (.n 191)], []⟩) := by
    rw [plainRun_step q0.1.symm q0.2.symm v0.symm, plainRun_step q1.1.symm q1.2.symm v1.symm,
      plainRun_step q2.1.symm q2.2.symm v2.symm, plainRun_step q3.1.symm q3.2.symm v3.symm]
    rfl
  simp only [plainStart, ↓reduceIte, hrun]
  refine ⟨?_, ?_⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact r0.st
    · exact r1.st
    · exact r2.st
    · exact r3.st
  · rw [← hret]
    simp only [List.map_cons, List.map_nil, e204, e205, e206, e207, e208, e211, e210, e209, e212,
      List.cons_append, List.nil_append, word_256]

/-- **`keccak_plain_rounds`' two specializations compute their meanings.** -/
theorem keccak_plain_rounds_holds : keccak_plain_rounds_Spec := by
  intro k0 hk rd args rets h
  interval_cases k0
  · exact plain60_sound rd args rets h
  · exact plain41_sound rd args rets h

end
end LeanVM.Guest.B1.VerifySub
