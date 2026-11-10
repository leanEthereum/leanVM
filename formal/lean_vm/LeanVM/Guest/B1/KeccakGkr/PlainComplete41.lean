/-
  LeanVM.Guest.B1.KeccakGkr.PlainComplete41

  `keccak_plain_rounds__L4_L1`, completely, and both specializations: `keccak_plain_rounds`'
  completeness.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.PlainComplete60

/-!
# `keccak_plain_rounds__L4_L1`, completely

As `plain60_complete`, with one scalar `w` waiting, its rate cells the arguments `5`, `6`
(`PlainCellsOk`): the first round's `KECCAK` reads them (`plain_core_sq1`).
`keccak_plain_rounds_complete : keccak_plain_rounds_complete_Spec`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

theorem plain41_chk : Fwd.chk 10 Data.core271.body = some 213 := by decide +kernel

theorem plain41_stores : storesOf 10 Data.core271.body =
    [.load (.n 58) (.n 9) 0, .load (.n 108) (.n 9) 1, .load (.n 153) (.n 9) 2,
      .load (.n 198) (.n 9) 3] := by
  decide +kernel

theorem four_of_length {α : Type} {l : List α} (h : l.length = 4) :
    ∃ a b c d, l = [a, b, c, d] := by
  match l, h with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

/-- **`keccak_plain_rounds__L4_L1` is complete**, the waiting cells a scalar's. -/
theorem plain41_complete (rd : Reader) (args rets : List E) (hpc : PlainCellsOk 1 args)
    (hm : MeaningPlainRounds 4 1 rd args rets) :
    coreProgram.Rel rd "keccak_plain_rounds__L4_L1" args rets := by
  match args, hm with
  | [f0, f1, f2, f3, f4, p0, p1, cur, value, point], hm =>
  obtain ⟨wv, hwv⟩ := hpc rfl
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hwv
  obtain ⟨hcanF, rounds, hlen, hreads, hrun⟩ := hm
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, rfl⟩ := four_of_length hlen
  obtain ⟨hpt, hret⟩ := hrun wv (fun _ _ ↦ hwv)
  simp only [plainStart, ↓reduceIte] at hpt hret
  have rd' : ∀ k (hk : k < 8), LoadHolds rd cur k ([a0, b0, a1, b1, a2, b2, a3, b3][k]'(by
      simpa using hk)) := fun k hk ↦ hreads k (by simpa using hk)
  -- the honest valuation
  set l : List E := [f0, f1, f2, f3, f4, p0, p1, cur, value, point] with hl
  have g := (ev_spec rd (fun _ ↦ 0) Data.core271.body l plain41_chk).2.2
  have pp : ∀ i (hi : i < 10), Val.ofArgs (ev rd (fun _ ↦ 0) l Data.core271.body) (.n i) =
      l.getD i 0 := fun i hi ↦
    ev_params rd (fun _ ↦ 0) (l := l) plain41_chk (by simpa [hl] using hi)
  rw [show l.length = 10 from rfl, plain41_stores] at g
  generalize Val.ofArgs (ev rd (fun _ ↦ 0) l Data.core271.body) = σ at g pp
  rw [body41] at g
  have p7 : σ (.n 7) = cur := pp 7 (by norm_num)
  have p8 : σ (.n 8) = value := pp 8 (by norm_num)
  have p9 : σ (.n 9) = point := pp 9 (by norm_num)
  have inT : ∀ s, (s ∈ [Stmt.atom (.copy (.n 10) (.n 0)), .atom (.copy (.n 11) (.n 1)),
      .atom (.copy (.n 12) (.n 2)), .atom (.copy (.n 13) (.n 3)), .atom (.copy (.n 14) (.n 4)),
      .atom (.copy (.n 15) (.n 5)), .atom (.copy (.n 16) (.n 6))] ∨
      s ∈ plainRoundT (.n 7) (.n 9) (.n 8)
        ([.n 15, .n 16, .n 24, .n 26, .n 34, .n 36] ++ [.n 37, .n 38] ++ capV 10) plainMid41a 0 17 39 ∨
      s ∈ plainRoundT (.n 7) (.n 9) (.n 63) (plainIns0 64 [.n 85, .n 86, .n 87, .n 88] 47)
        plainMid41b 1 64 89 ∨
      s ∈ plainRoundT (.n 7) (.n 9) (.n 113) (plainIns0 114 [.n 85, .n 86, .n 87, .n 88] 97) [] 2
        114 134 ∨
      s ∈ plainRoundT (.n 7) (.n 9) (.n 158) (plainIns0 159 [.n 85, .n 86, .n 87, .n 88] 142) [] 3
        159 179 ∨
      s ∈ [Stmt.atom (.copy (.n 204) (.n 187)), .atom (.copy (.n 205) (.n 188)),
        .atom (.copy (.n 206) (.n 189)), .atom (.copy (.n 207) (.n 190)),
        .atom (.copy (.n 208) (.n 191)), .atom (.const (.n 209) (word 256 0 0)),
        .atom (.mul (.n 210) (.n 7) (.n 209)), .atom (.copy (.n 211) (.n 210)),
        .atom (.copy (.n 212) (.n 203)),
        .ret [.n 204, .n 205, .n 206, .n 207, .n 208, .n 211, .n 212]]) → s ∈ plain41T := by
    intro s hs
    simp only [plain41T, List.mem_append]
    tauto
  have gp := fun s hs ↦ g s (inT s (Or.inl hs))
  have g0 := fun s hs ↦ g s (inT s (Or.inr (Or.inl hs)))
  have g1 := fun s hs ↦ g s (inT s (Or.inr (Or.inr (Or.inl hs))))
  have g2 := fun s hs ↦ g s (inT s (Or.inr (Or.inr (Or.inr (Or.inl hs)))))
  have g3 := fun s hs ↦ g s (inT s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs))))))
  have gt := fun s hs ↦ g s (inT s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hs))))))
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true, GoodS, Good] at gp gt
  obtain ⟨c10, c11, c12, c13, c14, c15, c16⟩ := gp
  obtain ⟨c204, c205, c206, c207, c208, c209, m210, c211, c212⟩ := gt
  simp only [Nat.reduceLT, and_self, ↓reduceIte] at m210
  -- the zero cells
  have inMid0 : ∀ s ∈ plainMid41a, s ∈ plainRoundT (.n 7) (.n 9) (.n 8)
      ([.n 15, .n 16, .n 24, .n 26, .n 34, .n 36] ++ [.n 37, .n 38] ++ capV 10) plainMid41a 0 17
      39 := fun s hs ↦ by
    unfold plainRoundT
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hs)))
  have inMid1 : ∀ s ∈ plainMid41b, s ∈ plainRoundT (.n 7) (.n 9) (.n 63)
      (plainIns0 64 [.n 85, .n 86, .n 87, .n 88] 47) plainMid41b 1 64 89 := fun s hs ↦ by
    unfold plainRoundT
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hs)))
  have z37 : σ (.n 37) = word 0 0 0 :=
    g0 (.atom (.const (.n 37) (word 0 0 0))) (inMid0 _ (by simp [plainMid41a]))
  have z38 : σ (.n 38) = word 0 0 0 :=
    g0 (.atom (.const (.n 38) (word 0 0 0))) (inMid0 _ (by simp [plainMid41a]))
  have z85 : σ (.n 85) = word 0 0 0 :=
    g1 (.atom (.const (.n 85) (word 0 0 0))) (inMid1 _ (by simp [plainMid41b]))
  have z86 : σ (.n 86) = word 0 0 0 :=
    g1 (.atom (.const (.n 86) (word 0 0 0))) (inMid1 _ (by simp [plainMid41b]))
  have z87 : σ (.n 87) = word 0 0 0 :=
    g1 (.atom (.const (.n 87) (word 0 0 0))) (inMid1 _ (by simp [plainMid41b]))
  have z88 : σ (.n 88) = word 0 0 0 :=
    g1 (.atom (.const (.n 88) (word 0 0 0))) (inMid1 _ (by simp [plainMid41b]))
  have cz : IsCanonical128 (word 0 0 0) := by
    rw [word_zero]; unfold IsCanonical128; exact limb_zero 2
  have hz0 : [V.n 37, .n 38].map σ = [0, 0] := by
    simp only [List.map_cons, List.map_nil, z37, z38, word_zero]
  have hz : [V.n 85, .n 86, .n 87, .n 88].map σ = [0, 0, 0, 0] := by
    simp only [List.map_cons, List.map_nil, z85, z86, z87, z88, word_zero]
  have hmidA : ∀ s ∈ plainMid41a, ∃ d c, s = .atom (.const d c) := by
    intro s hs
    simp only [plainMid41a, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> exact ⟨_, _, rfl⟩
  have hmidB : ∀ s ∈ plainMid41b, ∃ d c, s = .atom (.const d c) := by
    intro s hs
    simp only [plainMid41b, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
  have hnil : ∀ s ∈ ([] : List Stmt), ∃ d c, s = .atom (.const d c) :=
    fun s hs ↦ absurd hs (by simp)
  -- the canonical inputs
  have hcanR : ∀ (a cb : ℕ), (∀ j < 5, IsCanonical128 (σ (.n (cb + j)))) →
      ∀ v ∈ plainIns0 a [.n 85, .n 86, .n 87, .n 88] cb,
        v ∉ [V.n (a + 7), .n (a + 9), .n (a + 17), .n (a + 19)] → IsCanonical128 (σ v) := by
    intro a cb hcb v hv hnp
    simp only [plainIns0, capV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with ((h | h | h | h) | h | h | h | h) | h | h | h | h | h
    · exact absurd (by simp [h]) hnp
    · exact absurd (by simp [h]) hnp
    · exact absurd (by simp [h]) hnp
    · exact absurd (by simp [h]) hnp
    · rw [h, z85]; exact cz
    · rw [h, z86]; exact cz
    · rw [h, z87]; exact cz
    · rw [h, z88]; exact cz
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
  have e15 : σ (.n 15) = p0 := by rw [c15]; exact pp 5 (by norm_num)
  have e16 : σ (.n 16) = p1 := by rw [c16]; exact pp 6 (by norm_num)
  have hpw : (σ (.n 15), σ (.n 16)) = Keccak.scalarCells wv dsObserve := by rw [e15, e16]; exact hwv
  have hcan0 : ∀ v ∈ ([.n 15, .n 16, .n 24, .n 26, .n 34, .n 36] ++ [.n 37, .n 38] ++ capV 10 :
      List V), v ∉ [V.n (17 + 7), .n (17 + 9), .n (17 + 17), .n (17 + 19)] →
      IsCanonical128 (σ v) := by
    intro v hv hnp
    have h15 : IsCanonical128 (σ (.n 15)) := by
      have := congrArg Prod.fst hpw; simp only at this
      rw [this]; exact (scalarCells_canonical wv dsObserve).1
    have h16 : IsCanonical128 (σ (.n 16)) := by
      have := congrArg Prod.snd hpw; simp only at this
      rw [this]; exact (scalarCells_canonical wv dsObserve).2
    simp only [capV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with ((h | h | h | h | h | h) | h | h) | h | h | h | h | h
    · rw [h]; exact h15
    · rw [h]; exact h16
    · exact absurd (by simp [h]) hnp
    · exact absurd (by simp [h]) hnp
    · exact absurd (by simp [h]) hnp
    · exact absurd (by simp [h]) hnp
    · rw [h, z37]; exact cz
    · rw [h, z38]; exact cz
    · rw [h]; simpa using hcb0 0 (by norm_num)
    · rw [h]; exact hcb0 1 (by norm_num)
    · rw [h]; exact hcb0 2 (by norm_num)
    · rw [h]; exact hcb0 3 (by norm_num)
    · rw [h]; exact hcb0 4 (by norm_num)
  -- the rounds
  have l00 : LoadHolds rd (σ (.n 7)) (2 * 0) a0 := by rw [p7]; exact rd' 0 (by norm_num)
  have l01 : LoadHolds rd (σ (.n 7)) (2 * 0 + 1) b0 := by rw [p7]; exact rd' 1 (by norm_num)
  have l10 : LoadHolds rd (σ (.n 7)) (2 * 1) a1 := by rw [p7]; exact rd' 2 (by norm_num)
  have l11 : LoadHolds rd (σ (.n 7)) (2 * 1 + 1) b1 := by rw [p7]; exact rd' 3 (by norm_num)
  have l20 : LoadHolds rd (σ (.n 7)) (2 * 2) a2 := by rw [p7]; exact rd' 4 (by norm_num)
  have l21 : LoadHolds rd (σ (.n 7)) (2 * 2 + 1) b2 := by rw [p7]; exact rd' 5 (by norm_num)
  have l30 : LoadHolds rd (σ (.n 7)) (2 * 3) a3 := by rw [p7]; exact rd' 6 (by norm_num)
  have l31 : LoadHolds rd (σ (.n 7)) (2 * 3 + 1) b3 := by rw [p7]; exact rd' 7 (by norm_num)
  have nextCan : ∀ {ins : List V} {o cb : ℕ}, cb = o + 8 →
      (Atom.keccak ins ((List.range 13).map fun k ↦ .n (o + k)) false false).Holds rd σ →
      ∀ j < 5, IsCanonical128 (σ (.n (cb + j))) := by
    intro ins o cb hcb hk j hj
    have := cellsOf_canonical hk (8 + j) (by omega)
    rwa [show o + (8 + j) = cb + j by omega] at this
  obtain ⟨e17, e27, r0, v0, f0r⟩ := plainRound_complete (C := coreProgram.Rel rd) g0 (by decide)
    (by decide) hmidA (by omega) l00 l01 hcan0
  obtain ⟨e64, e74, r1, v1, f1r⟩ := plainRound_complete (C := coreProgram.Rel rd) g1 (by decide)
    (by decide) hmidB (by omega) l10 l11 (hcanR 64 47 (nextCan rfl r0.kc))
  obtain ⟨e114, e124, r2, v2, f2r⟩ := plainRound_complete (C := coreProgram.Rel rd) g2 (by decide)
    (by decide) hnil (by omega) l20 l21 (hcanR 114 97 (nextCan rfl r1.kc))
  obtain ⟨e159, e169, r3, v3, f3r⟩ := plainRound_complete (C := coreProgram.Rel rd) g3 (by decide)
    (by decide) hnil (by omega) l30 l31 (hcanR 159 142 (nextCan rfl r2.kc))
  -- the challenges and claims are `plainRun`'s
  have q0 := plain_core_sq1 (cap := [f0, f1, f2, f3, f4]) (w := wv) r0 hpw hz0 (by
    simp only [capV, List.map_cons, List.map_nil]
    rw [show (10 : ℕ) = 10 + 0 from rfl, pF 0 (by norm_num), pF 1 (by norm_num),
      pF 2 (by norm_num), pF 3 (by norm_num), pF 4 (by norm_num)]; rfl)
  have q1 := plain_core_sq0 (cap := [σ (.n 47), σ (.n 48), σ (.n 49), σ (.n 50), σ (.n 51)]) r1 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q2 := plain_core_sq0 (cap := [σ (.n 97), σ (.n 98), σ (.n 99), σ (.n 100), σ (.n 101)]) r2 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q3 := plain_core_sq0 (cap := [σ (.n 142), σ (.n 143), σ (.n 144), σ (.n 145), σ (.n 146)])
    r3 hz (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  simp only [Nat.reduceAdd] at q0 q1 q2 q3 v0 v1 v2 v3
  rw [p8] at v0
  have hrunEq : plainRun [(a0, b0), (a1, b1), (a2, b2), (a3, b3)] value
      ⟨[f0, f1, f2, f3, f4], [(wv, dsObserve)]⟩ =
      ([σ (.n 58), σ (.n 108), σ (.n 153), σ (.n 198)], σ (.n 203),
        ⟨[σ (.n 187), σ (.n 188), σ (.n 189), σ (.n 190), σ (.n 191)], []⟩) := by
    rw [← e17, ← e27, ← e64, ← e74, ← e114, ← e124, ← e159, ← e169,
      plainRun_step q0.1.symm q0.2.symm v0.symm, plainRun_step q1.1.symm q1.2.symm v1.symm,
      plainRun_step q2.1.symm q2.2.symm v2.symm, plainRun_step q3.1.symm q3.2.symm v3.symm]
    rfl
  rw [hrunEq] at hpt hret
  have st : ∀ k (hk : k < 4), LoadHolds rd (σ (.n 9)) k ([σ (.n 58), σ (.n 108), σ (.n 153),
      σ (.n 198)][k]'(by simpa using hk)) := fun k hk ↦ by
    rw [p9]; exact hpt k (by simpa using hk)
  -- the relation
  refine (rel_iff_sem find_plain41 _ _).mpr ⟨σ, ?_, ?_⟩
  · show [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7),
      σ (.n 8), σ (.n 9)] = l
    rw [pp 0 (by norm_num), pp 1 (by norm_num), pp 2 (by norm_num), pp 3 (by norm_num),
      pp 4 (by norm_num), pp 5 (by norm_num), pp 6 (by norm_num), pp 7 (by norm_num),
      pp 8 (by norm_num), pp 9 (by norm_num)]
    rfl
  show Stmt.HoldsList _ rd σ Data.core271.body False (fun rs ↦ rs = rets)
  rw [body41]
  simp only [plain41T, holdsList_append, Stmt.HoldsList, Stmt.Holds]
  refine ⟨c10, c11, c12, c13, c14, c15, c16, f0r (st 0 (by norm_num)) (f1r (st 1 (by norm_num))
    (f2r (st 2 (by norm_num)) (f3r (st 3 (by norm_num))
    ⟨c204, c205, c206, c207, c208, c209, m210, c211, c212, ?_⟩)))⟩
  rw [hret]
  simp only [List.map_cons, List.map_nil, c204, c205, c206, c207, c208, c211, m210, c209, c212,
    p7, word_256, List.cons_append, List.nil_append]

end
end LeanVM.Guest.B1.VerifySub
