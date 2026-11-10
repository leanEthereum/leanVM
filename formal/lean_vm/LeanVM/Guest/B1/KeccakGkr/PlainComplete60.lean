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
`plainRound_complete` (each round's capacity the previous round's outputs, canonical, its zero
cells the constants), their challenges and claims are `plainRun`'s (`plain_core_sq0`,
`plainRun_step`), so the meaning's stored challenges are the rounds' stores, and the returns the
meaning's.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

theorem plain60_chk : Fwd.chk 10 Data.core269.body = some 299 := by decide +kernel

theorem plain60_stores : storesOf 10 Data.core269.body =
    [.load (.n 59) (.n 9) 0, .load (.n 104) (.n 9) 1, .load (.n 149) (.n 9) 2,
      .load (.n 194) (.n 9) 3, .load (.n 239) (.n 9) 4, .load (.n 284) (.n 9) 5] := by
  decide +kernel

theorem kk_six_of_length {α : Type} {l : List α} (h : l.length = 6) :
    ∃ a b c d e f, l = [a, b, c, d, e, f] := by
  match l, h with
  | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩

/-- The zero cells of `__L6_L0`. -/
abbrev zs60 : List V := [.n 36, .n 37, .n 38, .n 39]

theorem cellsOf_canonical {rd : Reader} {σ : Val} {ins : List V} {o : ℕ}
    (hk : (Atom.keccak ins ((List.range 13).map fun k ↦ .n (o + k)) false false).Holds rd σ) :
    ∀ j < 13, IsCanonical128 (σ (.n (o + j))) := by
  obtain ⟨-, -, -, hout⟩ := keccak_outs hk
  intro j hj
  have := hout j hj
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range] at this
  rw [this]; exact cellsOfState_canonical _ _ _

/-- **`keccak_plain_rounds__L6_L0` is complete.** -/
theorem plain60_complete (rd : Reader) (args rets : List E)
    (hm : MeaningPlainRounds 6 0 rd args rets) :
    coreProgram.Rel rd "keccak_plain_rounds__L6_L0" args rets := by
  match args, hm with
  | [f0, f1, f2, f3, f4, p0, p1, cur, value, point], hm =>
  obtain ⟨hcanF, rounds, hlen, hreads, hrun⟩ := hm
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩, rfl⟩ := kk_six_of_length hlen
  obtain ⟨hpt, hret⟩ := hrun 0 (fun h ↦ absurd h (by decide))
  simp only [plainStart, show ¬ (0 : ℕ) = 1 by decide, ↓reduceIte] at hpt hret
  have rd' : ∀ k (hk : k < 12), LoadHolds rd cur k ([a0, b0, a1, b1, a2, b2, a3, b3, a4, b4, a5,
      b5][k]'(by simpa using hk)) := fun k hk ↦ hreads k (by simpa using hk)
  -- the honest valuation
  set l : List E := [f0, f1, f2, f3, f4, p0, p1, cur, value, point] with hl
  have g := (ev_spec rd (fun _ ↦ 0) Data.core269.body l plain60_chk).2.2
  have pp : ∀ i (hi : i < 10), Val.ofArgs (ev rd (fun _ ↦ 0) l Data.core269.body) (.n i) =
      l.getD i 0 := fun i hi ↦
    ev_params rd (fun _ ↦ 0) (l := l) plain60_chk (by simpa [hl] using hi)
  rw [show l.length = 10 from rfl, plain60_stores] at g
  generalize Val.ofArgs (ev rd (fun _ ↦ 0) l Data.core269.body) = σ at g pp
  rw [body60] at g
  have p7 : σ (.n 7) = cur := pp 7 (by norm_num)
  have p9 : σ (.n 9) = point := pp 9 (by norm_num)
  have inT : ∀ s, (s ∈ [Stmt.atom (.copy (.n 10) (.n 0)), .atom (.copy (.n 11) (.n 1)),
      .atom (.copy (.n 12) (.n 2)), .atom (.copy (.n 13) (.n 3)), .atom (.copy (.n 14) (.n 4))] ∨
      s ∈ plainRoundT (.n 7) (.n 9) (.n 8) (plainIns0 15 [.n 36, .n 37, .n 38, .n 39] 10)
        plainMid60 0 15 40 ∨
      s ∈ plainRoundT (.n 7) (.n 9) (.n 64) (plainIns0 65 [.n 36, .n 37, .n 38, .n 39] 48) [] 1 65 85 ∨
      s ∈ plainRoundT (.n 7) (.n 9) (.n 109) (plainIns0 110 [.n 36, .n 37, .n 38, .n 39] 93) [] 2
        110 130 ∨
      s ∈ plainRoundT (.n 7) (.n 9) (.n 154) (plainIns0 155 [.n 36, .n 37, .n 38, .n 39] 138) [] 3
        155 175 ∨
      s ∈ plainRoundT (.n 7) (.n 9) (.n 199) (plainIns0 200 [.n 36, .n 37, .n 38, .n 39] 183) [] 4
        200 220 ∨
      s ∈ plainRoundT (.n 7) (.n 9) (.n 244) (plainIns0 245 [.n 36, .n 37, .n 38, .n 39] 228) [] 5
        245 265 ∨
      s ∈ [Stmt.atom (.copy (.n 290) (.n 273)), .atom (.copy (.n 291) (.n 274)),
        .atom (.copy (.n 292) (.n 275)), .atom (.copy (.n 293) (.n 276)),
        .atom (.copy (.n 294) (.n 277)), .atom (.const (.n 295) (word 4096 0 0)),
        .atom (.mul (.n 296) (.n 7) (.n 295)), .atom (.copy (.n 297) (.n 296)),
        .atom (.copy (.n 298) (.n 289)),
        .ret [.n 290, .n 291, .n 292, .n 293, .n 294, .n 297, .n 298]]) → s ∈ plain60T := by
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
  obtain ⟨c10, c11, c12, c13, c14⟩ := gp
  obtain ⟨c290, c291, c292, c293, c294, c295, m296, c297, c298⟩ := gt
  simp only [Nat.reduceLT, and_self, ↓reduceIte] at m296
  -- the zero cells
  have inMid : ∀ s ∈ plainMid60, s ∈ plainRoundT (.n 7) (.n 9) (.n 8)
      (plainIns0 15 [.n 36, .n 37, .n 38, .n 39] 10) plainMid60 0 15 40 := fun s hs ↦ by
    unfold plainRoundT
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hs)))
  have z36 : σ (.n 36) = word 0 0 0 :=
    g0 (.atom (.const (.n 36) (word 0 0 0))) (inMid _ (by simp [plainMid60]))
  have z37 : σ (.n 37) = word 0 0 0 :=
    g0 (.atom (.const (.n 37) (word 0 0 0))) (inMid _ (by simp [plainMid60]))
  have z38 : σ (.n 38) = word 0 0 0 :=
    g0 (.atom (.const (.n 38) (word 0 0 0))) (inMid _ (by simp [plainMid60]))
  have z39 : σ (.n 39) = word 0 0 0 :=
    g0 (.atom (.const (.n 39) (word 0 0 0))) (inMid _ (by simp [plainMid60]))
  have cz : IsCanonical128 (word 0 0 0) := by
    rw [word_zero]; unfold IsCanonical128; exact limb_zero 2
  have hz : [V.n 36, .n 37, .n 38, .n 39].map σ = [0, 0, 0, 0] := by
    simp only [List.map_cons, List.map_nil, z36, z37, z38, z39, word_zero]
  have hmid0 : ∀ s ∈ plainMid60, ∃ d c, s = .atom (.const d c) := by
    intro s hs
    simp only [plainMid60, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
  have hnil : ∀ s ∈ ([] : List Stmt), ∃ d c, s = .atom (.const d c) :=
    fun s hs ↦ absurd hs (by simp)
  -- the canonical inputs of a round
  have hcanR : ∀ (a cb : ℕ), (∀ j < 5, IsCanonical128 (σ (.n (cb + j)))) →
      ∀ v ∈ plainIns0 a [.n 36, .n 37, .n 38, .n 39] cb,
        v ∉ [V.n (a + 7), .n (a + 9), .n (a + 17), .n (a + 19)] → IsCanonical128 (σ v) := by
    intro a cb hcb v hv hnp
    simp only [plainIns0, capV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with ((h | h | h | h) | h | h | h | h) | h | h | h | h | h
    · exact absurd (by simp [h]) hnp
    · exact absurd (by simp [h]) hnp
    · exact absurd (by simp [h]) hnp
    · exact absurd (by simp [h]) hnp
    · rw [h, z36]; exact cz
    · rw [h, z37]; exact cz
    · rw [h, z38]; exact cz
    · rw [h, z39]; exact cz
    · rw [h]; simpa using hcb 0 (by norm_num)
    · rw [h]; exact hcb 1 (by norm_num)
    · rw [h]; exact hcb 2 (by norm_num)
    · rw [h]; exact hcb 3 (by norm_num)
    · rw [h]; exact hcb 4 (by norm_num)
  have pF : ∀ j < 5, σ (.n (10 + j)) = [f0, f1, f2, f3, f4].getD j 0 := by
    intro j hj
    interval_cases j
    · rw [c10]; exact pp 0 (by norm_num)
    · rw [c11]; exact pp 1 (by norm_num)
    · rw [c12]; exact pp 2 (by norm_num)
    · rw [c13]; exact pp 3 (by norm_num)
    · rw [c14]; exact pp 4 (by norm_num)
  have hcb0 : ∀ j < 5, IsCanonical128 (σ (.n (10 + j))) := by
    intro j hj
    rw [pF j hj]
    interval_cases j <;> exact hcanF _ (by simp)
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
  have nextCan : ∀ {ins : List V} {o cb : ℕ}, cb = o + 8 →
      (Atom.keccak ins ((List.range 13).map fun k ↦ .n (o + k)) false false).Holds rd σ →
      ∀ j < 5, IsCanonical128 (σ (.n (cb + j))) := by
    intro ins o cb hcb hk j hj
    have := cellsOf_canonical hk (8 + j) (by omega)
    rwa [show o + (8 + j) = cb + j by omega] at this
  obtain ⟨e15, e25, r0, v0, f0r⟩ := plainRound_complete (C := coreProgram.Rel rd) g0 (by decide)
    (by decide) hmid0 (by omega) l00 l01 (hcanR 15 10 hcb0)
  obtain ⟨e65, e75, r1, v1, f1r⟩ := plainRound_complete (C := coreProgram.Rel rd) g1 (by decide)
    (by decide) hnil (by omega) l10 l11 (hcanR 65 48 (nextCan rfl r0.kc))
  obtain ⟨e110, e120, r2, v2, f2r⟩ := plainRound_complete (C := coreProgram.Rel rd) g2 (by decide)
    (by decide) hnil (by omega) l20 l21 (hcanR 110 93 (nextCan rfl r1.kc))
  obtain ⟨e155, e165, r3, v3, f3r⟩ := plainRound_complete (C := coreProgram.Rel rd) g3 (by decide)
    (by decide) hnil (by omega) l30 l31 (hcanR 155 138 (nextCan rfl r2.kc))
  obtain ⟨e200, e210, r4, v4, f4r⟩ := plainRound_complete (C := coreProgram.Rel rd) g4 (by decide)
    (by decide) hnil (by omega) l40 l41 (hcanR 200 183 (nextCan rfl r3.kc))
  obtain ⟨e245, e255, r5, v5, f5r⟩ := plainRound_complete (C := coreProgram.Rel rd) g5 (by decide)
    (by decide) hnil (by omega) l50 l51 (hcanR 245 228 (nextCan rfl r4.kc))
  -- the challenges and claims are `plainRun`'s
  have q0 := plain_core_sq0 (cap := [f0, f1, f2, f3, f4]) r0 hz (by
    simp only [capV, List.map_cons, List.map_nil]
    rw [show (10 : ℕ) = 10 + 0 from rfl, pF 0 (by norm_num), pF 1 (by norm_num),
      pF 2 (by norm_num), pF 3 (by norm_num), pF 4 (by norm_num)]; rfl)
  have q1 := plain_core_sq0 (cap := [σ (.n 48), σ (.n 49), σ (.n 50), σ (.n 51), σ (.n 52)]) r1 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q2 := plain_core_sq0 (cap := [σ (.n 93), σ (.n 94), σ (.n 95), σ (.n 96), σ (.n 97)]) r2 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q3 := plain_core_sq0 (cap := [σ (.n 138), σ (.n 139), σ (.n 140), σ (.n 141), σ (.n 142)])
    r3 hz (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q4 := plain_core_sq0 (cap := [σ (.n 183), σ (.n 184), σ (.n 185), σ (.n 186), σ (.n 187)])
    r4 hz (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q5 := plain_core_sq0 (cap := [σ (.n 228), σ (.n 229), σ (.n 230), σ (.n 231), σ (.n 232)])
    r5 hz (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  simp only [Nat.reduceAdd] at q0 q1 q2 q3 q4 q5 v0 v1 v2 v3 v4 v5
  rw [p8] at v0
  have hrunEq : plainRun [(a0, b0), (a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5)] value
      ⟨[f0, f1, f2, f3, f4], []⟩ =
      ([σ (.n 59), σ (.n 104), σ (.n 149), σ (.n 194), σ (.n 239), σ (.n 284)], σ (.n 289),
        ⟨[σ (.n 273), σ (.n 274), σ (.n 275), σ (.n 276), σ (.n 277)], []⟩) := by
    rw [← e15, ← e25, ← e65, ← e75, ← e110, ← e120, ← e155, ← e165, ← e200, ← e210, ← e245,
      ← e255, plainRun_step q0.1.symm q0.2.symm v0.symm, plainRun_step q1.1.symm q1.2.symm v1.symm,
      plainRun_step q2.1.symm q2.2.symm v2.symm, plainRun_step q3.1.symm q3.2.symm v3.symm,
      plainRun_step q4.1.symm q4.2.symm v4.symm, plainRun_step q5.1.symm q5.2.symm v5.symm]
    rfl
  rw [hrunEq] at hpt hret
  have st : ∀ k (hk : k < 6), LoadHolds rd (σ (.n 9)) k ([σ (.n 59), σ (.n 104), σ (.n 149),
      σ (.n 194), σ (.n 239), σ (.n 284)][k]'(by simpa using hk)) := fun k hk ↦ by
    rw [p9]; exact hpt k (by simpa using hk)
  -- the relation
  refine (rel_iff_sem find_plain60 _ _).mpr ⟨σ, ?_, ?_⟩
  · show [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7),
      σ (.n 8), σ (.n 9)] = l
    rw [pp 0 (by norm_num), pp 1 (by norm_num), pp 2 (by norm_num), pp 3 (by norm_num),
      pp 4 (by norm_num), pp 5 (by norm_num), pp 6 (by norm_num), pp 7 (by norm_num),
      pp 8 (by norm_num), pp 9 (by norm_num)]
    rfl
  show Stmt.HoldsList _ rd σ Data.core269.body False (fun rs ↦ rs = rets)
  rw [body60]
  simp only [plain60T, holdsList_append, Stmt.HoldsList, Stmt.Holds]
  refine ⟨c10, c11, c12, c13, c14, f0r (st 0 (by norm_num)) (f1r (st 1 (by norm_num))
    (f2r (st 2 (by norm_num)) (f3r (st 3 (by norm_num)) (f4r (st 4 (by norm_num))
    (f5r (st 5 (by norm_num)) ⟨c290, c291, c292, c293, c294, c295, m296, c297, c298, ?_⟩)))))⟩
  rw [hret]
  simp only [List.map_cons, List.map_nil, c290, c291, c292, c293, c294, c297, m296, c295, c298,
    p7, word_4096, List.cons_append, List.nil_append]

end
end LeanVM.Guest.B1.VerifySub
