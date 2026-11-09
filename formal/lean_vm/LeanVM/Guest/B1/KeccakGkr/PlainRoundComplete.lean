/-
  LeanVM.Guest.B1.KeccakGkr.PlainRoundComplete

  A plain sumcheck round of `keccak_plain_rounds`, completely: on an evaluated valuation, its two
  words read from memory and its `KECCAK` inputs canonical, the round's template holds once its
  challenge is stored where the memory holds it.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Plain
public import LeanVM.Guest.B1.KeccakGkr.FsComplete

/-!
# A plain round, completely

`plainRound_complete`: from the template's equations (`Fwd.GoodS`), the words `c₀`, `c₂` at the
cursor and the canonical inputs but the packed cells, the round's values are `c₀`, `c₂`, its
sponge facts (`PlainCore`) hold, its claim is `c₀ + c·((v + c₂) + c·c₂)`, and its statements hold
once the challenge's slot holds the challenge. `plain_core_sq0`, `plain_core_sq1`: the challenge
and the capacity cells after it are the squeeze's (as `plain_round_sq0`/`sq1`, from the sponge
facts only).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- A round's sponge facts. -/
structure PlainCore (rd : Reader) (σ : Val) (ins : List V) (a o : ℕ) : Prop where
  pk0 : FsPackOk σ (.n a) (a + 1) dsObserve
  pk2 : FsPackOk σ (.n (a + 10)) (a + 10 + 1) dsObserve
  kc : (Atom.keccak ins ((List.range 13).map fun k ↦ .n (o + k)) false false).Holds rd σ
  ch : ChallengeOk σ (.n o) (.n (o + 1)) (o + 13)

/-- A round with nothing waiting: the challenge and the capacity cells after it. -/
theorem plain_core_sq0 {zs capV : List V} {a o : ℕ} {cap : List E}
    (h : PlainCore rd σ ([.n (a + 7), .n (a + 9), .n (a + 17), .n (a + 19)] ++ zs ++ capV) a o)
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

/-- A round with one scalar `w` waiting, its rate cells `p0`, `p1`. -/
theorem plain_core_sq1 {p0 p1 : V} {zs capV : List V} {a o : ℕ} {cap : List E} {w : E}
    (h : PlainCore rd σ ([p0, p1, .n (a + 7), .n (a + 9), .n (a + 17), .n (a + 19)] ++ zs ++ capV)
      a o)
    (hp : (σ p0, σ p1) = Keccak.scalarCells w dsObserve)
    (hz : zs.map σ = [0, 0]) (hc : capV.map σ = cap) :
    σ (.n (o + 19)) = (plainSq ⟨cap, [(w, dsObserve)]⟩ (σ (.n a)) (σ (.n (a + 10)))).1 ∧
      [σ (.n (o + 8)), σ (.n (o + 9)), σ (.n (o + 10)), σ (.n (o + 11)), σ (.n (o + 12))] =
        (plainSq ⟨cap, [(w, dsObserve)]⟩ (σ (.n a)) (σ (.n (a + 10)))).2.cap := by
  obtain ⟨-, -, hcan, -⟩ := keccak_outs h.kc
  have c0 : IsCanonical128 (σ (.n (a + 7))) := hcan _ (by simp)
  have c2 : IsCanonical128 (σ (.n (a + 10 + 7))) := hcan _ (by simp)
  have s0 := fsNext_scalar h.pk0 c0
  have s2 := fsNext_scalar h.pk2 c2
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

/-- A block of constants holds on an evaluated valuation. -/
theorem consts_complete : ∀ (ss : List Stmt), (∀ s ∈ ss, ∃ d c, s = .atom (.const d c)) →
    (∀ s ∈ ss, GoodS rd S w σ s) → ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ ss next kret
  | [], _, _, _, _, hn => hn
  | s :: ss, hc, hg, _, _, hn => by
    obtain ⟨d, c, rfl⟩ := hc s (List.mem_cons_self ..)
    exact ⟨hg _ (List.mem_cons_self ..), consts_complete ss
      (fun t ht ↦ hc t (List.mem_cons_of_mem _ ht)) (fun t ht ↦ hg t (List.mem_cons_of_mem _ ht)) hn⟩

theorem mul_good {d x y : ℕ} (hx : x < d) (hy : y < d)
    (h : GoodS rd S w σ (.atom (.mul (.n d) (.n x) (.n y)))) : σ (.n d) = σ (.n x) * σ (.n y) := by
  simp only [GoodS, Good] at h
  rwa [ite_pos' ⟨hx, hy⟩] at h

/-- **A plain round, completely.** -/
theorem plainRound_complete {cur pt vIn : V} {ins : List V} {mid : List Stmt} {i a o : ℕ}
    (hg : ∀ s ∈ plainRoundT cur pt vIn ins mid i a o, GoodS rd S w σ s)
    (hn0 : Atom.load (.n a) cur (2 * i) ∉ S) (hn2 : Atom.load (.n (a + 10)) cur (2 * i + 1) ∉ S)
    (hmid : ∀ s ∈ mid, ∃ d c, s = .atom (.const d c)) (hord : a + 10 < o + 21)
    {c0 c2 : E} (h0 : LoadHolds rd (σ cur) (2 * i) c0) (h2 : LoadHolds rd (σ cur) (2 * i + 1) c2)
    (hcan : ∀ v ∈ ins, v ∉ [V.n (a + 7), .n (a + 9), .n (a + 17), .n (a + 19)] →
      IsCanonical128 (σ v)) :
    σ (.n a) = c0 ∧ σ (.n (a + 10)) = c2 ∧ PlainCore rd σ ins a o ∧
      σ (.n (o + 24)) = σ (.n a) + σ (.n (o + 19)) *
        ((σ vIn + σ (.n (a + 10))) + σ (.n (o + 19)) * σ (.n (a + 10))) ∧
      ∀ {next : Prop} {kret : List E → Prop}, LoadHolds rd (σ pt) i (σ (.n (o + 19))) → next →
        Stmt.HoldsList C rd σ (plainRoundT cur pt vIn ins mid i a o) next kret := by
  have mem : ∀ s, s ∈ plainRoundT cur pt vIn ins mid i a o → GoodS rd S w σ s := hg
  unfold plainRoundT at mem
  have g0 : ∀ s ∈ fsNextT cur (2 * i) a, GoodS rd S w σ s := fun s hs ↦ mem s
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ hs)))))
  have g2 : ∀ s ∈ fsNextT cur (2 * i + 1) (a + 10), GoodS rd S w σ s := fun s hs ↦ mem s
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ hs)))))
  have gm : ∀ s ∈ mid, GoodS rd S w σ s := fun s hs ↦ mem s
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hs))))
  have gk : GoodS rd S w σ (keccakA ins ((List.range 13).map fun k ↦ .n (o + k))) := mem _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_singleton_self _))))
  have gc : ∀ s ∈ challengeT (.n o) (.n (o + 1)) (o + 13), GoodS rd S w σ s := fun s hs ↦ mem s
    (List.mem_append_left _ (List.mem_append_right _ hs))
  have gt : ∀ s ∈ [Stmt.atom (.add (.n (o + 20)) vIn (.n (a + 10))),
      .atom (.load (.n (o + 19)) pt i), .atom (.mul (.n (o + 21)) (.n (o + 19)) (.n (a + 10))),
      .atom (.add (.n (o + 22)) (.n (o + 20)) (.n (o + 21))),
      .atom (.mul (.n (o + 23)) (.n (o + 19)) (.n (o + 22))),
      .atom (.add (.n (o + 24)) (.n a) (.n (o + 23)))], GoodS rd S w σ s := fun s hs ↦ mem s
    (List.mem_append_right _ hs)
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true] at gt
  obtain ⟨g20, -, g21, g22, g23, g24⟩ := gt
  obtain ⟨e0, k7, k9, -, f0⟩ := fsNext_complete (C := C) g0 hn0 h0
  obtain ⟨e2, k17, k19, -, f2⟩ := fsNext_complete (C := C) g2 hn2 h2
  have pk0 := fsPackOk_of_vals (fsPack_vals_of_good
    (fun s hs ↦ g0 s (List.mem_cons_of_mem _ hs)))
  have pk2 := fsPackOk_of_vals (fsPack_vals_of_good
    (fun s hs ↦ g2 s (List.mem_cons_of_mem _ hs)))
  have hcanI : AllCanonical (ins.map σ) := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hc
    by_cases hp : v ∈ [V.n (a + 7), .n (a + 9), .n (a + 17), .n (a + 19)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact k7
      · exact k9
      · exact k17
      · exact k19
    · exact hcan v hv hp
  have kc := keccakA_complete (show Good rd S w σ (.keccak ins ((List.range 13).map fun k ↦
    .n (o + k)) false false) from gk) hcanI
  obtain ⟨-, -, -, hout⟩ := keccak_outs kc
  have c1 : IsCanonical128 (σ (.n (o + 1))) := by
    have := hout 1 (by norm_num)
    simp only [range13_map, List.getD_cons_succ, List.getD_cons_zero] at this
    rw [this]; exact cellsOfState_canonical _ _ _
  obtain ⟨ch, fc⟩ := challenge_complete (C := C) gc c1
  simp only [GoodS, Good] at g20 g22 g24
  have e21 := mul_good (by omega) hord g21
  have e23 := mul_good (by omega) (by omega) g23
  refine ⟨e0, e2, ⟨pk0, pk2, kc, ch⟩, by rw [g24, e23, g22, e21, g20], ?_⟩
  intro next kret hst hn
  simp only [plainRoundT, holdsList_append]
  refine f0 (f2 (consts_complete mid hmid gm ?_))
  simp only [keccakA, Stmt.HoldsList, Stmt.Holds]
  refine ⟨kc, fc ?_⟩
  simp only [Atom.Holds]
  exact ⟨g20, hst, e21, g22, e23, g24, hn⟩

end
end LeanVM.Guest.B1.VerifySub
