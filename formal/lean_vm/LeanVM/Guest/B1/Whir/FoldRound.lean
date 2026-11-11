/-
  LeanVM.Guest.B1.Whir.FoldRound

  `opening_fold_round` at `0` bits and at `b > 0` bits is a fold round with its proof of work.
-/

module

public import LeanVM.Guest.B1.Whir.Squeezes
public import LeanVM.Guest.B1.Opening.Fold

/-!
# `opening_fold_round`

A level some rate grinds the folds of calls, at each round, `opening_fold_round` specialized on
the rate's bits (`osFoldNames`): at `0` bits `opening_fold` itself (`ofrZero_sound`); at `b > 0`
bits (`ofr_sound`) the nonce at the cursor is absorbed with the two waiting scalars
(`DS_POW_NONCE`), the permutation's first cell passes `grind_check__L{b}`, and the challenge is
squeezed from its capacity: the Spec's `foldProofOfWork b` then the round (`MeaningFoldRound b`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

theorem ofrZeroBody_split : ofrZeroBody =
    ([.call "opening_fold" ((List.range 11).map V.n) (osRun 11 10)] ++
      ((List.range 10).map fun i ↦ .atom (.copy (.n (21 + i)) (.n (11 + i))))) ++
    [.ret (osRun 21 10)] := by
  simp only [ofrZeroBody, List.append_assoc]

/-- **`opening_fold_round__L0` is `opening_fold`.** -/
theorem ofrZero_sound (hfn : FnIs "opening_fold_round__L0" (osParams 11) ofrZeroBody)
    (args rets : List E) (h : coreProgram.Rel rd "opening_fold_round__L0" args rets) :
    MeaningFoldRound 0 rd args rets := by
  obtain ⟨fn, hf, hps, hb⟩ := hfn
  rw [rel_iff_sem hf] at h
  obtain ⟨σ, hp, hh⟩ := h
  rw [hb, ofrZeroBody_split, holdsList_flat_ret _ (by simp [Stmt.flat])] at hh
  obtain ⟨hok, hret⟩ := hh
  rw [hps] at hp
  subst hp hret
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons,
    List.map_nil, List.range_succ, List.range_zero, List.nil_append, List.cons_append, osRun,
    Nat.add_zero, Nat.reduceAdd] at hok
  obtain ⟨hcall, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30⟩ := hok
  have hm := meaningFoldRound_zero ((opening_fold_holds rd _ _).mp hcall)
  simp only [osParams, osRun, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, Nat.add_zero, Nat.reduceAdd] at hm ⊢
  rw [e21, e22, e23, e24, e25, e26, e27, e28, e29, e30]
  exact hm

/-- `opening_fold_round` at `b > 0` bits before its `ret`. -/
def ofrA (b : ℕ) : List Stmt :=
  ((List.range 5).map fun i ↦ .atom (.copy (.n (11 + i)) (.n i))) ++
    fsPackT (.n 5) 16 1 ++ fsPackT (.n 6) 25 1 ++
    [.atom (.load (.n 34) (.n 7) 0)] ++ fsPackT (.n 34) 35 4 ++
    [.atom (.const (.n 44) (word 0 0 0)), .atom (.const (.n 45) (word 0 0 0)),
      keccakA ([22, 24, 31, 33, 41, 43, 44, 45, 11, 12, 13, 14, 15].map V.n) (osRun 46 13),
      .call ("grind_check__L" ++ natStr b) [.n 46] []] ++
    (osPad none 59).1 ++ osSqueeze0 59 [54, 55, 56, 57, 58] 64 ++
    [.atom (.mul (.n 84) (.n 10) (.n 83)), .atom (.add (.n 85) (.n 84) (.n 9)),
      .atom (.mul (.n 86) (.n 85) (.n 83)), .atom (.add (.n 87) (.n 86) (.n 8)),
      .atom (.load (.n 88) (.n 7) 1), .atom (.load (.n 89) (.n 7) 2)] ++
    ((List.range 5).map fun i ↦ .atom (.copy (.n (90 + i)) (.n (72 + i)))) ++
    [.atom (.const (.n 95) (gw 3)), .atom (.mul (.n 96) (.n 7) (.n 95)),
      .atom (.copy (.n 97) (.n 96)), .atom (.copy (.n 98) (.n 87)), .atom (.copy (.n 99) (.n 88)),
      .atom (.copy (.n 100) (.n 89)), .atom (.copy (.n 101) (.n 83))]

theorem ofrBody_split (b : ℕ) : ofrBody b = ofrA b ++
    [.ret [.n 90, .n 91, .n 92, .n 93, .n 94, .n 97, .n 98, .n 99, .n 100, .n 101]] := by
  simp only [ofrBody, ofrA, List.append_assoc, List.cons_append, List.nil_append]

theorem ofrA_flat (b : ℕ) : (ofrA b).all Stmt.flat = true := by
  simp [ofrA, fsPackT, osPad, osSqueeze0, keccakA, challengeT, Stmt.flat]

/-- **`opening_fold_round` at `b > 0` bits is a fold round with its proof of work.** -/
theorem ofr_sound {b : ℕ} (hb : b ≠ 0)
    (hfn : FnIs (osFoldRoundName b) (osParams 11) (ofrBody b))
    (hgr : ∀ args rets, coreProgram.Rel rd ("grind_check__L" ++ natStr b) args rets →
      MeaningGrindCheck b args rets)
    (args rets : List E) (h : coreProgram.Rel rd (osFoldRoundName b) args rets) :
    MeaningFoldRound b rd args rets := by
  obtain ⟨fn, hf, hps, hbd⟩ := hfn
  rw [rel_iff_sem hf] at h
  obtain ⟨σ, hp, hh⟩ := h
  rw [hbd, ofrBody_split, holdsList_flat_ret _ (ofrA_flat b)] at hh
  obtain ⟨hok, hret⟩ := hh
  rw [hps] at hp
  subst hp hret
  simp only [ofrA, osPad, allOk_append, allOk_cons, allOk_nil, and_true, allOk_fsPackT, StmtOk,
    Atom.Holds, List.map_cons, List.map_nil, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, osRun, Nat.add_zero, Nat.reduceAdd, and_assoc] at hok
  obtain ⟨e11, e12, e13, e14, e15, P16, P25, L34, P35, z44, z45, hK, hgc, c59, c60, c61, c62, c63,
    hQ, m84, a85, m86, a87, L88, L89, e90, e91, e92, e93, e94, c95, m96, e97, e98, e99, e100,
    e101⟩ := hok
  -- the nonce's permutation
  obtain ⟨-, -, hcanK, hout⟩ := keccakA_perm (rd := rd) hK
  have cn0 := packed_cells P16 (hcanK _ (by simp))
  have cn1 := packed_cells P25 (hcanK _ (by simp))
  have cn2 := packed_cells P35 (hcanK _ (by simp))
  simp only [Nat.reduceAdd] at cn0 cn1 cn2
  set F : Fs := ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)],
    [(σ (.n 5), dsObserve), (σ (.n 6), dsObserve)]⟩ with hF
  have hFa : F.absorb (σ (.n 34)) dsPowNonce = ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)],
      [(σ (.n 5), dsObserve), (σ (.n 6), dsObserve), (σ (.n 34), dsPowNonce)]⟩ := by
    simp [hF, Fs.absorb, rateScalars]
  set S := (F.absorb (σ (.n 34)) dsPowNonce).perm with hSdef
  have hS : permOf ([V.n 22, V.n 24, V.n 31, V.n 33, V.n 41, V.n 43, V.n 44, V.n 45, V.n 11,
      V.n 12, V.n 13, V.n 14, V.n 15].map σ) = S := by
    rw [hSdef, hFa, perm_eq_cells _ (by simp)]
    simp only [List.map_cons, List.map_nil, e11, e12, e13, e14, e15, z44, z45]
    simp [pendCells, cn0.1, cn0.2, cn1.1, cn1.2, cn2.1, cn2.2, dsObserve, dsPowNonce, word_zero]
  rw [hS] at hout
  have o0 : σ (.n 46) = cellsOfState S false 0 := outs_eq hout 0 (by simp)
  have o8 : σ (.n 54) = cellsOfState S false 8 := outs_eq hout 8 (by simp)
  have o9 : σ (.n 55) = cellsOfState S false 9 := outs_eq hout 9 (by simp)
  have o10 : σ (.n 56) = cellsOfState S false 10 := outs_eq hout 10 (by simp)
  have o11 : σ (.n 57) = cellsOfState S false 11 := outs_eq hout 11 (by simp)
  have o12 : σ (.n 58) = cellsOfState S false 12 := outs_eq hout 12 (by simp)
  -- the proof of work
  obtain ⟨-, -, hlow⟩ := hgr _ _ hgc
  have hpow : PowOk b F (σ (.n 34)) := by
    intro _
    have hl : ((F.absorb (σ (.n 34)) dsPowNonce).squeeze.1.limb 0).lane.toNat % 2 ^ b = 0 := by
      simp only [Fs.squeeze]
      rw [Keccak.challengeOf_limb0, ← hSdef, ← o0]; exact hlow
    simp only [powOk, hb, ↓reduceIte]
    exact decide_eq_true hl
  -- the challenge
  have hpad : PadOk σ (some 59) := by
    simp only [PadOk]; rw [c60, c61, c62, c63, word_zero]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hsq := osSqueeze0_val (cap := [54, 55, 56, 57, 58]) rfl hpad hQ
  have hG : powSponge b F (σ (.n 34)) =
      ⟨[σ (.n 54), σ (.n 55), σ (.n 56), σ (.n 57), σ (.n 58)], []⟩ := by
    simp only [powSponge, hb, ↓reduceIte, Fs.squeeze, capOf, ← hSdef, o8, o9, o10, o11, o12]
  simp only [List.map_cons, List.map_nil] at hsq
  rw [← hG] at hsq
  obtain ⟨hcells, hlam⟩ := hsq
  have hr1 : (powSponge b F (σ (.n 34))).squeeze.1 = σ (.n 83) := by
    rw [show (83 : ℕ) = 64 + 19 from rfl, hlam]; rfl
  have h72 : σ (.n 72) = _ := hcells 8
  have h73 : σ (.n 73) = _ := hcells 9
  have h74 : σ (.n 74) = _ := hcells 10
  have h75 : σ (.n 75) = _ := hcells 11
  have h76 : σ (.n 76) = _ := hcells 12
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  refine ⟨σ (.n 34), σ (.n 88), σ (.n 89), ?_, hpow, ?_⟩
  · intro i hi
    simp only [powWords, hb, ↓reduceIte, List.singleton_append, List.length_cons,
      List.length_nil] at hi ⊢
    rcases i with _ | _ | _ | i
    · exact L34
    · exact L88
    · exact L89
    · omega
  · simp only [Fs.squeeze, capOf] at hr1 ⊢
    rw [e90, e91, e92, e93, e94, e97, m96, c95, gw_eq (by unfold u128Bound; norm_num), e98, a87,
      m86, a85, m84, e99, e100, e101, ← hr1, h72, h73, h74, h75, h76]
    simp [roundLen, hb, hF]


/-! ## A level's fold calls -/

/-- **`opening_fold` calls are rounds at `0` bits.** -/
theorem foldCallOk_none {C : CallRel} {σ : Val} (hle : CallRel.Le C (coreProgram.Rel rd)) :
    FoldCallOk C rd σ none 0 := fun _ _ h ↦
  meaningFoldRound_zero ((opening_fold_holds rd _ _).mp (hle _ _ _ h))

/-- **A level's fold calls**, at the rate's bits: `opening_fold` where no rate grinds the level's
folds, else the dispatch into `opening_fold_round` at the rate's bits. -/
theorem foldCallOk_level {C : CallRel} {σ : Val} (hle : CallRel.Le C (coreProgram.Rel rd))
    {c : OsCfg} {lvl : ℕ} {lv : OsLv} (hrate : LvRate σ c lvl lv)
    (hany : lv.grindAny = 0 → lv.foldGrind = 0)
    (h0 : FnIs "opening_fold_round__L0" (osParams 11) ofrZeroBody)
    (hb : lv.foldGrind ≠ 0 → FnIs (osFoldRoundName lv.foldGrind) (osParams 11) (ofrBody lv.foldGrind) ∧
      ∀ args rets, coreProgram.Rel rd ("grind_check__L" ++ natStr lv.foldGrind) args rets →
        MeaningGrindCheck lv.foldGrind args rets) :
    FoldCallOk C rd σ (osFoldNames c lvl lv) lv.foldGrind := by
  unfold osFoldNames
  by_cases ha : lv.grindAny = 0
  · simp only [ha, ↓reduceIte]
    rw [hany ha]
    exact foldCallOk_none hle
  · simp only [ha, ↓reduceIte]
    intro args rets h
    have hc := hle _ _ _ (dispatch_rate hrate (fun l ↦ osFoldRoundName l.foldGrind) h)
    by_cases hb0 : lv.foldGrind = 0
    · rw [hb0] at hc ⊢
      exact ofrZero_sound h0 _ _ hc
    · exact ofr_sound hb0 (hb hb0).1 (hb hb0).2 _ _ hc

end
end LeanVM.Guest.B1.Whir
