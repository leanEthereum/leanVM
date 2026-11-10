/-
  LeanVM.Guest.B1.KeccakGkr.LayerCD

  `keccak_layer`'s eleven rounds over the bit position, completely.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LocalRounds
public import LeanVM.Guest.B1.KeccakGkr.PlainRoundComplete

/-!
# The position rounds, completely

`localRound_complete`: on an evaluated valuation, a round's three words read from memory, the
round's values are the words, its challenge and capacity the squeeze's,
its claim the round polynomial's value, and its statements hold once the challenge's slot of the
local point holds it. `localRounds_complete`: the `n` rounds compute `localRunF` of the messages
the memory holds, and hold once the local point holds `localRunF`'s challenges.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- The squeeze after a round's three words. -/
def sq3 (cap : List E) (c0 c2 c3 : E) : E × Fs :=
  ((⟨cap, []⟩ : Fs).absorbAll [c0, c2, c3] dsObserve).squeeze

/-- **A position round, completely.** -/
theorem localRound_complete {cur loc vIn : V} {capV : List V} {i a : ℕ}
    (hg : ∀ s ∈ localRoundT cur loc vIn capV i a, GoodS rd S w σ s)
    (hS : ∀ d off, Atom.load d cur off ∉ S) {c0 c2 c3 : E}
    (h0 : LoadHolds rd (σ cur) (3 * i) c0) (h2 : LoadHolds rd (σ cur) (3 * i + 1) c2)
    (h3 : LoadHolds rd (σ cur) (3 * i + 2) c3) :
    σ (.n a) = c0 ∧ σ (.n (a + 3)) = c2 ∧ σ (.n (a + 6)) = c3 ∧
      σ (.n (a + 24)) = (sq3 (capV.map σ) c0 c2 c3).1 ∧
      [σ (.n (a + 19)), σ (.n (a + 20)), σ (.n (a + 21)), σ (.n (a + 22)), σ (.n (a + 23))] =
        (sq3 (capV.map σ) c0 c2 c3).2.cap ∧
      σ (.n (a + 32)) = polyEval [c0, σ vIn + sumE [c2, c3], c2, c3] (σ (.n (a + 24))) ∧
      ∀ {next : Prop} {kret : List E → Prop}, LoadHolds rd (σ loc) i (σ (.n (a + 24))) → next →
        Stmt.HoldsList C rd σ (localRoundT cur loc vIn capV i a) next kret := by
  have mem : ∀ s, s ∈ localRoundT cur loc vIn capV i a → GoodS rd S w σ s := hg
  unfold localRoundT at mem
  have g0 : ∀ s ∈ fsNextT cur (3 * i) a, GoodS rd S w σ s := fun s hs ↦ mem s
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ hs)))))
  have g2 : ∀ s ∈ fsNextT cur (3 * i + 1) (a + 3), GoodS rd S w σ s := fun s hs ↦ mem s
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ hs)))))
  have g3 : ∀ s ∈ fsNextT cur (3 * i + 2) (a + 6), GoodS rd S w σ s := fun s hs ↦ mem s
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hs))))
  have gm : ∀ s ∈ [Stmt.atom (.const (.n (a + 9)) (word 0 0)),
      .atom (.const (.n (a + 10)) (word 0 0)),
      keccakA ([.n (a + 1), .n (a + 2), .n (a + 4), .n (a + 5), .n (a + 7), .n (a + 8),
        .n (a + 9), .n (a + 10)] ++ capV) ((List.range 13).map fun k ↦ .n (a + 11 + k))],
      GoodS rd S w σ s := fun s hs ↦ mem s
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs)))
  have gc : ∀ s ∈ challengeT (.n (a + 11)) (a + 24), GoodS rd S w σ s :=
    fun s hs ↦ mem s (List.mem_append_left _ (List.mem_append_right _ hs))
  have gt := fun s hs ↦ mem s (List.mem_append_right _ hs)
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true] at gt gm
  obtain ⟨-, g25, g26, g27, g28, g29, g30, g31, g32⟩ := gt
  obtain ⟨z0, z1, gk⟩ := gm
  simp only [GoodS, Good] at z0 z1
  obtain ⟨e0, -, f0⟩ := fsNext_complete (C := C) g0 (hS _ _) h0
  obtain ⟨e2, -, f2⟩ := fsNext_complete (C := C) g2 (hS _ _) h2
  obtain ⟨e3, -, f3⟩ := fsNext_complete (C := C) g3 (hS _ _) h3
  have pk0 := fsPack_vals_of_good (fun s hs ↦ g0 s (List.mem_cons_of_mem _ hs))
  have pk2 := fsPack_vals_of_good (fun s hs ↦ g2 s (List.mem_cons_of_mem _ hs))
  have pk3 := fsPack_vals_of_good (fun s hs ↦ g3 s (List.mem_cons_of_mem _ hs))
  have kc := keccakA_complete (show Good rd S w σ (.keccak _ ((List.range 13).map fun k ↦
    .n (a + 11 + k)) false false) from gk)
  obtain ⟨ch, fc⟩ := challenge_complete (C := C) gc
  have q := sq3_atoms (rd := rd) (a := a) (o := a + 11) (z0 := .n (a + 9)) (z1 := .n (a + 10))
    (capV := capV) (cap := capV.map σ) pk0 pk2 pk3 kc ch (by rw [z0, word_zero])
    (by rw [z1, word_zero]) rfl
  simp only [GoodS, Good] at g25 g26 g28 g30 g32
  have e27 := mul_good (by omega) (by omega) g27
  have e29 := mul_good (by omega) (by omega) g29
  have e31 := mul_good (by omega) (by omega) g31
  have ev : σ (.n (a + 32)) = σ (.n a) + σ (.n (a + 24)) * (σ vIn + (1 + σ (.n (a + 24))) *
      (σ (.n (a + 3)) + (1 + σ (.n (a + 24))) * σ (.n (a + 6)))) := by
    rw [g32, e31, g30, e29, g28, e27, g26, g25, word_one]
  rw [e0, e2, e3] at q
  refine ⟨e0, e2, e3, by rw [show a + 24 = a + 11 + 13 by omega]; exact q.1, ?_, ?_, ?_⟩
  · have := q.2
    simp only [show a + 11 + 8 = a + 19 by omega, show a + 11 + 9 = a + 20 by omega,
      show a + 11 + 10 = a + 21 by omega, show a + 11 + 11 = a + 22 by omega,
      show a + 11 + 12 = a + 23 by omega] at this
    exact this
  · rw [ev, e0, e2, e3, local_value]
  · intro next kret hst hn
    simp only [localRoundT, holdsList_append]
    refine f0 (f2 (f3 ?_))
    simp only [keccakA, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    refine ⟨z0, z1, kc, fc ?_⟩
    exact ⟨hst, g25, g26, e27, g28, e29, g30, e31, g32, hn⟩

theorem readsAt_triple_flat {p : E} {ms : List (E × E × E)} {m : E × E × E}
    (h : ReadsAt rd p ((ms ++ [m]).flatMap fun m ↦ [m.1, m.2.1, m.2.2])) :
    ReadsAt rd p (ms.flatMap fun m ↦ [m.1, m.2.1, m.2.2]) ∧
      LoadHolds rd p (3 * ms.length) m.1 ∧ LoadHolds rd p (3 * ms.length + 1) m.2.1 ∧
      LoadHolds rd p (3 * ms.length + 2) m.2.2 := by
  rw [List.flatMap_append, readsAt_append, flatMap_triples_length] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_, ?_, ?_⟩
  · have := h2 0 (by simp)
    rwa [loadHolds_mul_gen_pow, Nat.add_zero] at this
  · have := h2 1 (by simp)
    rwa [loadHolds_mul_gen_pow] at this
  · have := h2 2 (by simp)
    rwa [loadHolds_mul_gen_pow] at this

/-- **The position rounds, completely.** -/
theorem localRounds_complete {cur loc vIn : V} {capV : List V} {a0 : ℕ}
    (hS : ∀ d off, Atom.load d cur off ∉ S) :
    ∀ (n : ℕ) (msgs : List (E × E × E)), msgs.length = n → 1 ≤ n →
      (∀ s ∈ localRoundsT cur loc vIn capV a0 n, GoodS rd S w σ s) →
      ReadsAt rd (σ cur) (msgs.flatMap fun m ↦ [m.1, m.2.1, m.2.2]) →
      (localRunF msgs (σ vIn) ⟨capV.map σ, []⟩).1.2 = σ (.n (a0 + 33 * (n - 1) + 32)) ∧
      (localRunF msgs (σ vIn) ⟨capV.map σ, []⟩).2 =
        ⟨(localRoundsT.capV' (a0 + 33 * (n - 1) + 19)).map σ, []⟩ ∧
      ∀ {next : Prop} {kret : List E → Prop},
        ReadsAt rd (σ loc) (localRunF msgs (σ vIn) ⟨capV.map σ, []⟩).1.1 → next →
        Stmt.HoldsList C rd σ (localRoundsT cur loc vIn capV a0 n) next kret
  | 0, _, _, h, _, _ => absurd h (by omega)
  | n + 1, msgs, hl, _, hg, hr => by
    obtain ⟨ms, m, rfl⟩ : ∃ ms m, msgs = ms ++ [m] := by
      refine ⟨msgs.dropLast, msgs.getLast (by rintro rfl; simp at hl), ?_⟩
      exact (List.dropLast_append_getLast _).symm
    have hl' : ms.length = n := by simpa using hl
    obtain ⟨hr0, l0, l2, l3⟩ := readsAt_triple_flat hr
    rw [hl'] at l0 l2 l3
    rw [localRoundsT_succ] at hg
    have hgP := fun s hs ↦ hg s (List.mem_append_left _ hs)
    have hgR := fun s hs ↦ hg s (List.mem_append_right _ hs)
    -- the earlier rounds' run, as the round's input
    have pre : ∃ (vI : V) (cV : List V),
        (localRunF ms (σ vIn) ⟨capV.map σ, []⟩).1.2 = σ vI ∧
        (localRunF ms (σ vIn) ⟨capV.map σ, []⟩).2 = ⟨cV.map σ, []⟩ ∧
        (if n = 0 then vIn else .n (a0 + 33 * (n - 1) + 32)) = vI ∧
        (if n = 0 then capV else localRoundsT.capV' (a0 + 33 * (n - 1) + 19)) = cV ∧
        ∀ {next : Prop} {kret : List E → Prop},
          ReadsAt rd (σ loc) (localRunF ms (σ vIn) ⟨capV.map σ, []⟩).1.1 → next →
          Stmt.HoldsList C rd σ (localRoundsT cur loc vIn capV a0 n) next kret := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · obtain rfl : ms = [] := List.eq_nil_of_length_eq_zero hl'
        refine ⟨vIn, capV, rfl, rfl, rfl, rfl, fun _ hn ↦ ?_⟩
        simp only [localRoundsT, List.range_zero, List.map_nil, List.flatten_nil, Stmt.HoldsList]
        exact hn
      · obtain ⟨hv, hc, hh⟩ := localRounds_complete hS n ms hl' hn hgP hr0
        have hn0 : n ≠ 0 := by omega
        exact ⟨_, _, hv, hc, by simp [hn0], by simp [hn0], hh⟩
    obtain ⟨vI, cV, hv, hc, evI, ecV, hh⟩ := pre
    rw [evI, ecV] at hgR
    obtain ⟨e0, e2, e3, e51, ecap, e59, hround⟩ :=
      localRound_complete (C := C) (cur := cur) (loc := loc) hgR hS l0 l2 l3
    refine ⟨?_, ?_, fun {next kret} hloc hn ↦ ?_⟩
    · rw [localRunF_snoc, hv, hc, show a0 + 33 * (n + 1 - 1) + 32 = a0 + 33 * n + 32 by omega, e59,
        e51]
      rfl
    · rw [localRunF_snoc, hc]
      simp only [show n + 1 - 1 = n by omega, localRoundsT.capV', List.map_cons, List.map_nil]
      rw [Fs.mk.injEq]
      refine ⟨?_, ?_⟩
      · show (sq3 (cV.map σ) m.1 m.2.1 m.2.2).2.cap = _
        rw [← ecap]
      · rfl
    · rw [localRunF_snoc, hc, readsAt_append, localRunF_length, hl'] at hloc
      obtain ⟨hloc0, hloc1⟩ := hloc
      rw [localRoundsT_succ, evI, ecV, holdsList_append]
      refine hh hloc0 (hround ?_ hn)
      have := hloc1 0 (by simp)
      rw [loadHolds_mul_gen_pow, Nat.add_zero] at this
      simp only [List.getElem_cons_zero] at this
      rw [e51]
      exact this

end
end LeanVM.Guest.B1.VerifySub
