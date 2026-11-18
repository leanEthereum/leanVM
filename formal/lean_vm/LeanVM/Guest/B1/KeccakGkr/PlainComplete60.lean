/-
  LeanVM.Guest.B1.KeccakGkr.PlainComplete60

  `keccak_plain_rounds__L6_L0`, completely: honest capacity, stream words and stored challenges give
  its relation.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.PlainRoundComplete

/-!
# `keccak_plain_rounds__L6_L0`, completely

`plain60_complete`: the honest valuation evaluates the body (`Fwd.ev`); its six rounds hold by
`plainRound_complete` (each round's capacity the previous round's outputs, its zero cells the
constants), their challenges and claims are `plainRun`'s (`plain_core_sq0`, `plainRun_step`), so
the meaning's stored challenges are the rounds' stores, and the returns the meaning's.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

theorem plain60_chk : Fwd.chk 11 (fn% «keccak_plain_rounds__L6_L0»).body = some 174 :=
  by decide +kernel

theorem plain60_stores : storesOf 11 (fn% «keccak_plain_rounds__L6_L0»).body =
    [.load (.n 27) (.n 9) 0, .load (.n 51) (.n 9) 1, .load (.n 75) (.n 9) 2,
      .load (.n 99) (.n 9) 3, .load (.n 123) (.n 9) 4, .load (.n 147) (.n 9) 5] := by
  decide +kernel

theorem kk_six_of_length {α : Type} {l : List α} (h : l.length = 6) :
    ∃ a b c d e f, l = [a, b, c, d, e, f] := by
  match l, h with
  | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩

/-- **`keccak_plain_rounds__L6_L0` is complete.** -/
theorem plain60_complete (rd : Reader) (args rets : List E)
    (hm : MeaningPlainRounds 6 0 rd args rets) :
    coreProgram.Rel rd "keccak_plain_rounds__L6_L0" args rets := by
  match args, hm with
  | [f0, f1, f2, f3, f4, p0, p1, cur, value, point, tabs], hm =>
  obtain ⟨rounds, hlen, hreads, hrun⟩ := hm
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩, rfl⟩ := kk_six_of_length hlen
  obtain ⟨hpt, hret⟩ := hrun 0 (fun h ↦ absurd h (by decide))
  simp only [plainStart, show ¬ (0 : ℕ) = 1 by decide, ↓reduceIte] at hpt hret
  have rd' : ∀ k (hk : k < 12), LoadHolds rd cur k ([a0, b0, a1, b1, a2, b2, a3, b3, a4, b4, a5,
      b5][k]'(by simpa using hk)) := fun k hk ↦ hreads k (by simpa using hk)
  -- the honest valuation
  set l : List E := [f0, f1, f2, f3, f4, p0, p1, cur, value, point, tabs] with hl
  have g := (ev_spec rd (fun _ ↦ 0) (fn% «keccak_plain_rounds__L6_L0»).body l plain60_chk).2.2
  have pp : ∀ i (hi : i < 11), Val.ofArgs (ev rd (fun _ ↦ 0) l
      (fn% «keccak_plain_rounds__L6_L0»).body) (.n i) =
      l.getD i 0 := fun i hi ↦
    ev_params rd (fun _ ↦ 0) (l := l) plain60_chk (by simpa [hl] using hi)
  rw [show l.length = 11 from rfl, plain60_stores] at g
  generalize Val.ofArgs (ev rd (fun _ ↦ 0) l (fn% «keccak_plain_rounds__L6_L0»).body) = σ at g pp
  rw [body60] at g
  have p7 : σ (.n 7) = cur := pp 7 (by norm_num)
  have p9 : σ (.n 9) = point := pp 9 (by norm_num)
  have inT : ∀ s, (s ∈ [Stmt.atom (.copy (.n 11) (.n 0)), .atom (.copy (.n 12) (.n 1)),
      .atom (.copy (.n 13) (.n 2)), .atom (.copy (.n 14) (.n 3)), .atom (.copy (.n 15) (.n 4))] ∨
      s ∈ plainRoundT (.n 7) (.n 9) (.n 8) (plainIns0 16 [.n 23, .n 24, .n 25, .n 26] 11)
        plainMid60 0 16 27 ∨
      s ∈ plainRoundT (.n 7) (.n 9) (.n 44) (plainIns0 45 [.n 23, .n 24, .n 25, .n 26] 35) [] 1 45 51 ∨
      s ∈ plainRoundT (.n 7) (.n 9) (.n 68) (plainIns0 69 [.n 23, .n 24, .n 25, .n 26] 59) [] 2
        69 75 ∨
      s ∈ plainRoundT (.n 7) (.n 9) (.n 92) (plainIns0 93 [.n 23, .n 24, .n 25, .n 26] 83) [] 3
        93 99 ∨
      s ∈ plainRoundT (.n 7) (.n 9) (.n 116) (plainIns0 117 [.n 23, .n 24, .n 25, .n 26] 107) [] 4
        117 123 ∨
      s ∈ plainRoundT (.n 7) (.n 9) (.n 140) (plainIns0 141 [.n 23, .n 24, .n 25, .n 26] 131) [] 5
        141 147 ∨
      s ∈ [Stmt.atom (.copy (.n 165) (.n 155)), .atom (.copy (.n 166) (.n 156)),
        .atom (.copy (.n 167) (.n 157)), .atom (.copy (.n 168) (.n 158)),
        .atom (.copy (.n 169) (.n 159)), .atom (.const (.n 170) (word 4096 0)),
        .atom (.mul (.n 171) (.n 7) (.n 170)), .atom (.copy (.n 172) (.n 171)),
        .atom (.copy (.n 173) (.n 164)),
        .ret [.n 165, .n 166, .n 167, .n 168, .n 169, .n 172, .n 173]]) → s ∈ plain60T := by
    intro s hs
    simp only [plain60T, List.mem_append]
    tauto
  have gp := fun s hs ↦ g s (inT s (Or.inl hs))
  have g0 := fun s hs ↦ g s (inT s (Or.inr (Or.inl hs)))
  have g1 := fun s hs ↦ g s (inT s (Or.inr (Or.inr (Or.inl hs))))
  have g2 := fun s hs ↦ g s (inT s (Or.inr (Or.inr (Or.inr (Or.inl hs)))))
  have g3 := fun s hs ↦ g s (inT s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs))))))
  have g4 := fun s hs ↦ g s (inT s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs)))))))
  have g5 := fun s hs ↦ g s (inT s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl hs))))))))
  have gt := fun s hs ↦ g s (inT s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr hs))))))))
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true, GoodS, Good] at gp gt
  obtain ⟨c11, c12, c13, c14, c15⟩ := gp
  obtain ⟨c165, c166, c167, c168, c169, c170, m171, c172, c173⟩ := gt
  simp only [Nat.reduceLT, and_self, ↓reduceIte] at m171
  -- the zero cells
  have inMid : ∀ s ∈ plainMid60, s ∈ plainRoundT (.n 7) (.n 9) (.n 8)
      (plainIns0 16 [.n 23, .n 24, .n 25, .n 26] 11) plainMid60 0 16 27 := fun s hs ↦ by
    unfold plainRoundT
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs))
  have z23 : σ (.n 23) = word 0 0 :=
    g0 (.atom (.const (.n 23) (word 0 0))) (inMid _ (by simp [plainMid60]))
  have z24 : σ (.n 24) = word 0 0 :=
    g0 (.atom (.const (.n 24) (word 0 0))) (inMid _ (by simp [plainMid60]))
  have z25 : σ (.n 25) = word 0 0 :=
    g0 (.atom (.const (.n 25) (word 0 0))) (inMid _ (by simp [plainMid60]))
  have z26 : σ (.n 26) = word 0 0 :=
    g0 (.atom (.const (.n 26) (word 0 0))) (inMid _ (by simp [plainMid60]))
  have hz : [V.n 23, .n 24, .n 25, .n 26].map σ = [0, 0, 0, 0] := by
    simp only [List.map_cons, List.map_nil, z23, z24, z25, z26, word_zero]
  have hmid0 : ∀ s ∈ plainMid60, ∃ d c, s = .atom (.const d c) := by
    intro s hs
    simp only [plainMid60, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
  have hnil : ∀ s ∈ ([] : List Stmt), ∃ d c, s = .atom (.const d c) :=
    fun s hs ↦ absurd hs (by simp)
  have pF : ∀ j < 5, σ (.n (11 + j)) = [f0, f1, f2, f3, f4].getD j 0 := by
    intro j hj
    interval_cases j
    · rw [c11]; exact pp 0 (by norm_num)
    · rw [c12]; exact pp 1 (by norm_num)
    · rw [c13]; exact pp 2 (by norm_num)
    · rw [c14]; exact pp 3 (by norm_num)
    · rw [c15]; exact pp 4 (by norm_num)
  -- the rounds
  have p8 : σ (.n 8) = value := pp 8 (by norm_num)
  have l00 : LoadHolds rd (σ (.n 7)) (2 * 0) a0 := by rw [p7]; exact rd' 0 (by norm_num)
  have l01 : LoadHolds rd (σ (.n 7)) (2 * 0 + 1) b0 := by rw [p7]; exact rd' 1 (by norm_num)
  have l10 : LoadHolds rd (σ (.n 7)) (2 * 1) a1 := by rw [p7]; exact rd' 2 (by norm_num)
  have l11 : LoadHolds rd (σ (.n 7)) (2 * 1 + 1) b1 := by rw [p7]; exact rd' 3 (by norm_num)
  have l20 : LoadHolds rd (σ (.n 7)) (2 * 2) a2 := by rw [p7]; exact rd' 4 (by norm_num)
  have l21 : LoadHolds rd (σ (.n 7)) (2 * 2 + 1) b2 := by rw [p7]; exact rd' 5 (by norm_num)
  have l30 : LoadHolds rd (σ (.n 7)) (2 * 3) a3 := by rw [p7]; exact rd' 6 (by norm_num)
  have l31 : LoadHolds rd (σ (.n 7)) (2 * 3 + 1) b3 := by rw [p7]; exact rd' 7 (by norm_num)
  have l40 : LoadHolds rd (σ (.n 7)) (2 * 4) a4 := by rw [p7]; exact rd' 8 (by norm_num)
  have l41 : LoadHolds rd (σ (.n 7)) (2 * 4 + 1) b4 := by rw [p7]; exact rd' 9 (by norm_num)
  have l50 : LoadHolds rd (σ (.n 7)) (2 * 5) a5 := by rw [p7]; exact rd' 10 (by norm_num)
  have l51 : LoadHolds rd (σ (.n 7)) (2 * 5 + 1) b5 := by rw [p7]; exact rd' 11 (by norm_num)
  obtain ⟨e16, e19, r0, v0, f0r⟩ := plainRound_complete (C := coreProgram.Rel rd) g0 (by decide)
    (by decide) hmid0 (by omega) l00 l01
  obtain ⟨e45, e48, r1, v1, f1r⟩ := plainRound_complete (C := coreProgram.Rel rd) g1 (by decide)
    (by decide) hnil (by omega) l10 l11
  obtain ⟨e69, e72, r2, v2, f2r⟩ := plainRound_complete (C := coreProgram.Rel rd) g2 (by decide)
    (by decide) hnil (by omega) l20 l21
  obtain ⟨e93, e96, r3, v3, f3r⟩ := plainRound_complete (C := coreProgram.Rel rd) g3 (by decide)
    (by decide) hnil (by omega) l30 l31
  obtain ⟨e117, e120, r4, v4, f4r⟩ := plainRound_complete (C := coreProgram.Rel rd) g4 (by decide)
    (by decide) hnil (by omega) l40 l41
  obtain ⟨e141, e144, r5, v5, f5r⟩ := plainRound_complete (C := coreProgram.Rel rd) g5 (by decide)
    (by decide) hnil (by omega) l50 l51
  -- the challenges and claims are `plainRun`'s
  have q0 := plain_core_sq0 (cap := [f0, f1, f2, f3, f4]) r0 hz (by
    simp only [capV, List.map_cons, List.map_nil]
    rw [show (11 : ℕ) = 11 + 0 from rfl, pF 0 (by norm_num), pF 1 (by norm_num),
      pF 2 (by norm_num), pF 3 (by norm_num), pF 4 (by norm_num)]; rfl)
  have q1 := plain_core_sq0 (cap := [σ (.n 35), σ (.n 36), σ (.n 37), σ (.n 38), σ (.n 39)]) r1 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q2 := plain_core_sq0 (cap := [σ (.n 59), σ (.n 60), σ (.n 61), σ (.n 62), σ (.n 63)]) r2 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q3 := plain_core_sq0 (cap := [σ (.n 83), σ (.n 84), σ (.n 85), σ (.n 86), σ (.n 87)])
    r3 hz (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q4 := plain_core_sq0 (cap := [σ (.n 107), σ (.n 108), σ (.n 109), σ (.n 110), σ (.n 111)])
    r4 hz (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q5 := plain_core_sq0 (cap := [σ (.n 131), σ (.n 132), σ (.n 133), σ (.n 134), σ (.n 135)])
    r5 hz (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  simp only [Nat.reduceAdd] at q0 q1 q2 q3 q4 q5 v0 v1 v2 v3 v4 v5
  rw [p8] at v0
  have hrunEq : plainRun [(a0, b0), (a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5)] value
      ⟨[f0, f1, f2, f3, f4], []⟩ =
      ([σ (.n 27), σ (.n 51), σ (.n 75), σ (.n 99), σ (.n 123), σ (.n 147)], σ (.n 164),
        ⟨[σ (.n 155), σ (.n 156), σ (.n 157), σ (.n 158), σ (.n 159)], []⟩) := by
    rw [← e16, ← e19, ← e45, ← e48, ← e69, ← e72, ← e93, ← e96, ← e117, ← e120, ← e141,
      ← e144, plainRun_step q0.1.symm q0.2.symm v0.symm, plainRun_step q1.1.symm q1.2.symm v1.symm,
      plainRun_step q2.1.symm q2.2.symm v2.symm, plainRun_step q3.1.symm q3.2.symm v3.symm,
      plainRun_step q4.1.symm q4.2.symm v4.symm, plainRun_step q5.1.symm q5.2.symm v5.symm]
    rfl
  rw [hrunEq] at hpt hret
  have st : ∀ k (hk : k < 6), LoadHolds rd (σ (.n 9)) k ([σ (.n 27), σ (.n 51), σ (.n 75),
      σ (.n 99), σ (.n 123), σ (.n 147)][k]'(by simpa using hk)) := fun k hk ↦ by
    rw [p9]; exact hpt k (by simpa using hk)
  -- the relation
  refine (rel_iff_sem find_plain60 _ _).mpr ⟨σ, ?_, ?_⟩
  · show [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7),
      σ (.n 8), σ (.n 9), σ (.n 10)] = l
    rw [pp 0 (by norm_num), pp 1 (by norm_num), pp 2 (by norm_num), pp 3 (by norm_num),
      pp 4 (by norm_num), pp 5 (by norm_num), pp 6 (by norm_num), pp 7 (by norm_num),
      pp 8 (by norm_num), pp 9 (by norm_num), pp 10 (by norm_num)]
    rfl
  show Stmt.HoldsList _ rd σ (fn% «keccak_plain_rounds__L6_L0»).body False (fun rs ↦ rs = rets)
  rw [body60]
  simp only [plain60T, holdsList_append, Stmt.HoldsList, Stmt.Holds]
  refine ⟨c11, c12, c13, c14, c15, f0r (st 0 (by norm_num)) (f1r (st 1 (by norm_num))
    (f2r (st 2 (by norm_num)) (f3r (st 3 (by norm_num)) (f4r (st 4 (by norm_num))
    (f5r (st 5 (by norm_num)) ⟨c165, c166, c167, c168, c169, c170, m171, c172, c173, ?_⟩)))))⟩
  rw [hret]
  simp only [List.map_cons, List.map_nil, c165, c166, c167, c168, c169, c172, m171, c170, c173,
    p7, word_4096, List.cons_append, List.nil_append]

end
end LeanVM.Guest.B1.VerifySub
