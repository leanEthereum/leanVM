/-
  LeanVM.Guest.B1.Whir.Commit

  A non-final level's next commitment, high part, out-of-domain points and values and query
  nonce (`osCommit`), and the final level's lane and query nonce (`osFinalMsg`), soundly.
-/

module

public import LeanVM.Guest.B1.Whir.Folds
public import LeanVM.Guest.B1.Fs.Message
public import LeanVM.Guest.B1.Whir.SqLoop

/-!
# The level's message (G:1584-1612)

`osCommit_sound`: `opening_message` reads the next root's two cells and the high part at the
cursor, stores them in `sent` (the root also in `level_roots`), absorbs them and permutes; the
permutation's first cell is the first out-of-domain point's first coordinate
(`squeeze_point_from`), the second point follows (`squeeze_point`); the two values and the query
nonce are read at the cursor past the message and absorbed, the nonce's permutation `S` leaving
the first query word and the proof of work in its cells `0`, `1` and the sponge's capacity.
`osFinalMsg_sound`: the final lane and the nonce, by `opening_message` with a nonce.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- An output cell of a permutation. -/
theorem outCellK {k : ℕ} {S : KeccakState} (h : cells13 ((osRun k 13).map σ) = cellsOfState S false)
    (i : Fin 13) : σ (.n (k + i.val)) = cellsOfState S false i := by
  simpa [osRun] using outs_eq h i (by simp [osRun])

/-- `osMatS_val`, the statements first, so that they name the state. -/
theorem osMatS_val' {P : List (ℕ × ℕ × ℕ)} {base off : ℕ} {s : OsSt}
    (hok : AllOk C rd σ (osMatS P base off s).1) (hm : MatsOk σ s.mats) (h : off < u128Bound) :
    σ (.n (osMatS P base off s).2.1) = σ (.n base) * gen ^ off ∧
      MatsOk σ (osMatS P base off s).2.2.mats := osMatS_val hm h hok

/-- `n` squeezes from a sponge with nothing waiting are the first, then `n - 1` more. -/
theorem squeezeN_succ' (s : Fs) (n : ℕ) :
    s.squeezeN (n + 1) = (s.squeeze.1 :: (s.squeeze.2.squeezeN n).1, (s.squeeze.2.squeezeN n).2) :=
  rfl

/-- The sponge after squeezes is its capacity with nothing waiting. -/
theorem squeezeN_eq_cap (s : Fs) (n : ℕ) (h : 0 < n) :
    (s.squeezeN n).2 = ⟨(s.squeezeN n).2.cap, []⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := squeezeN_pend (s := s.squeeze.2) rfl m
  rw [squeezeN_succ']
  cases e : (s.squeeze.2.squeezeN m).2
  rw [e] at this
  simp only at this
  rw [this]

/-- A sponge is its capacity and what waits. -/
theorem fs_mk_eq {s : Fs} {c : List E} {p : List (E × ℕ)} (h1 : s.cap = c) (h2 : s.pend = p) :
    s = ⟨c, p⟩ := by
  cases s; simp_all

/-- What a non-final level's message leaves (G:1586-1612): the root's two cells `x0, x1` and the
high part read at the cursor, stored at `sent` and the root in `level_roots`; the out-of-domain
points `P1`, `P2` squeezed after them and stored in `ood_z`; the values `y0, y1` and the nonce
`nn` read past them; the nonce's permutation `S`. -/
structure CommitOut (rd : Reader) (σ : Val) (lvl : ℕ) (lv : OsLv) (st st' : OsSt)
    (x0 x1 : E) (high : List E) (y0 y1 nn : E) : Prop where
  high_len : high.length = lv.folds
  reads : ReadsAt rd (st.cur σ) (x0 :: x1 :: high ++ [y0, y1, nn])
  sent : ReadsAt rd (σ (.n st'.sent)) (x0 :: x1 :: high)
  root0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 2) x0
  root1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 3) x1
  ood0 : ReadsAt rd (σ (.n osOodz) * gen ^ (oodSamples * (lvl + 1) * ligColsCap))
    (((st.F σ).absorbAll (x0 :: x1 :: high) dsObserve).squeezeN lv.logCols).1
  ood1 : ReadsAt rd (σ (.n osOodz) * gen ^ ((oodSamples * (lvl + 1) + 1) * ligColsCap))
    (((((st.F σ).absorbAll (x0 :: x1 :: high) dsObserve).squeezeN lv.logCols).2.squeezeN
      lv.logCols).1)
  ys : st'.ys = [st'.ys.getD 0 0, st'.ys.getD 1 0] ∧ σ (.n (st'.ys.getD 0 0)) = y0 ∧
    σ (.n (st'.ys.getD 1 0)) = y1
  word0 : σ (.n st'.word0) = cellsOfState ((((((st.F σ).absorbAll (x0 :: x1 :: high)
    dsObserve).squeezeN lv.logCols).2.squeezeN lv.logCols).2.absorbAll [y0, y1] dsObserve).nonceState
      nn) false 0
  pow0 : σ (.n st'.pow0) = cellsOfState ((((((st.F σ).absorbAll (x0 :: x1 :: high)
    dsObserve).squeezeN lv.logCols).2.squeezeN lv.logCols).2.absorbAll [y0, y1] dsObserve).nonceState
      nn) false 1
  F : st'.F σ = ⟨capOf ((((((st.F σ).absorbAll (x0 :: x1 :: high) dsObserve).squeezeN
    lv.logCols).2.squeezeN lv.logCols).2.absorbAll [y0, y1] dsObserve).nonceState nn), []⟩
  cur : st'.cur σ = st.cur σ * gen ^ (lv.folds + 5)
  fs : st'.fs.length = 5
  mats : MatsOk σ st'.mats
  co : st'.co = 3
  pad : st'.pad = st.pad

/-- **A non-final level's message, soundly** (G:1586-1612). -/
theorem osCommit_sound {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt}
    (hom : ∀ a r, C ("opening_message__L" ++ natStr (2 + lv.folds) ++ "_L0") a r →
      MeaningOpeningMessage (2 + lv.folds) 0 rd a r)
    (hspf : ∀ a r, C ("squeeze_point_from__L" ++ natStr lv.logCols) a r →
      MeaningSqueezePointFrom lv.logCols rd a r)
    (hsp : ∀ a r, C ("squeeze_point__L" ++ natStr lv.logCols) a r →
      MeaningSqueezePoint lv.logCols rd a r)
    (hmu : 1 ≤ lv.logCols) (hfs : st.fs.length = 5) (hm : MatsOk σ st.mats)
    (hco : st.co < u128Bound) (hoff : (oodSamples * (lvl + 1) + 1) * ligColsCap < u128Bound)
    (hok : AllOk C rd σ (osCommit c lvl lv st).1) :
    ∃ x0 x1 high y0 y1 nn, CommitOut rd σ lvl lv st (osCommit c lvl lv st).2 x0 x1 high y0 y1 nn := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fs_five st hfs
  unfold osCommit at hok ⊢
  simp only [allOk_append, and_assoc] at hok
  obtain ⟨-, hcu, hmsg, ho0, hspf', ho1, hsp', hcp, hn0, hn1, hlast⟩ := hok
  set s0 : OsSt := { st with k := st.k + 2 } with hs0
  set r := (osCurS s0).2.2.k with hr
  set s1 : OsSt := { (osCurS s0).2.2 with k := r + 10 } with hs1
  set q := (osMatS c.plan osOodz (oodSamples * (lvl + 1) * ligColsCap) s1).2.2.k with hq
  set s2 : OsSt := { (osMatS c.plan osOodz (oodSamples * (lvl + 1) * ligColsCap) s1).2.2 with
    k := q + 5 } with hs2
  set t := (osMatS c.plan osOodz ((oodSamples * (lvl + 1) + 1) * ligColsCap) s2).2.2.k with ht
  have ecu := osCurS_val (s := s0) hco hcu
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_call, stmtOk_atom, holds_load, osLd] at hmsg
  obtain ⟨hcall, ls0, lr0, ls1, lr1⟩ := hmsg
  have hM := hom _ _ hcall
  have hfm : List.map V.n st.fs = [.n f0, .n f1, .n f2, .n f3, .n f4] := by rw [hf]; rfl
  simp only [List.map_append, hfm, List.cons_append, List.nil_append, List.map_cons, List.map_nil, osRun,
    List.range_succ, List.range_zero, Nat.add_zero, MeaningOpeningMessage] at hM
  obtain ⟨xs, hxl, hrd, hsent, nn0, -, hret⟩ := hM
  obtain ⟨x0, x1, high, rfl⟩ : ∃ x0 x1 high, xs = x0 :: x1 :: high := by
    rcases xs with _ | ⟨x0, _ | ⟨x1, high⟩⟩
    · simp only [List.length_nil] at hxl; omega
    · simp only [List.length_cons, List.length_nil] at hxl; omega
    · exact ⟨x0, x1, high, rfl⟩
  simp only [show ¬ (0 : ℕ) = 1 from by decide, ↓reduceIte, omState, capOf, List.cons_append,
    List.nil_append, List.cons.injEq] at hret
  obtain ⟨e0, e1, c0, c1, c2, c3, c4, ecur, -⟩ := hret
  rw [ecu] at hrd ecur
  -- the first out-of-domain point
  have hrow0 : oodSamples * (lvl + 1) * ligColsCap < u128Bound :=
    lt_of_le_of_lt (by unfold ligColsCap; omega) hoff
  obtain ⟨ev0, hm0⟩ := osMatS_val' ho0 hm hrow0
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_call, List.map_cons, List.map_nil, osRun,
    List.range_succ, List.range_zero] at hspf'
  have hP1 := hspf _ _ hspf'
  simp only [MeaningSqueezePointFrom] at hP1
  obtain ⟨rP1, eP1⟩ := hP1
  rw [ev0] at rP1
  -- the second
  obtain ⟨ev1, hm1⟩ := osMatS_val' ho1 hm0 hoff
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_call, List.map_cons, List.map_nil, osRun,
    List.range_succ, List.range_zero] at hsp'
  have hP2 := hsp _ _ hsp'
  simp only [MeaningSqueezePoint] at hP2
  obtain ⟨rP2, eP2⟩ := hP2
  rw [ev1] at rP2
  -- the values, the nonce and its permutation
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_copy, holds_load, holds_const,
    osCp, osLd, osCst, osOodNext, List.map_cons, List.map_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, Nat.add_zero] at hcp hn0 hn1 hlast
  simp only [List.nil_append, List.cons_append, List.map_cons, List.map_nil, Nat.add_zero] at eP1 eP2
  obtain ⟨c5, c6, c7, c8, c9⟩ := hcp
  obtain ⟨ly0, p1, p2, p3⟩ := hn0
  obtain ⟨ly1, q1, q2, q3⟩ := hn1
  obtain ⟨lnn, z1, z2, z3, z4, hK⟩ := hlast
  simp only [Nat.add_assoc, Nat.reduceAdd] at p1 p2 p3 ly1 q1 q2 q3 lnn z1 z2 z3 z4 hK c6 c7 c8 c9
  obtain ⟨m, hmm⟩ : ∃ m, lv.logCols = m + 1 := ⟨lv.logCols - 1, by omega⟩
  rw [hmm] at rP1 eP1 rP2 eP2
  simp only [Nat.add_sub_cancel] at rP1 eP1
  have hF : st.F σ = ⟨[σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)], []⟩ := by
    simp [OsSt.F, hf]
  set F1 : Fs := (⟨[σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)], []⟩ : Fs).absorbAll
    (x0 :: x1 :: high) dsObserve with hF1
  have hS1 : F1.squeeze =
      (σ (.n r), ⟨[σ (.n (r + 2)), σ (.n (r + 3)), σ (.n (r + 4)), σ (.n (r + 5)), σ (.n (r + 6))], []⟩) := by
    simp only [Fs.squeeze, capOf, e0, c0, c1, c2, c3, c4, Keccak.challengeOf_cells]
  set G1 := (⟨[σ (.n (r + 2)), σ (.n (r + 3)), σ (.n (r + 4)), σ (.n (r + 5)), σ (.n (r + 6))], []⟩ :
    Fs).squeezeN m with hG1d
  have hP1 : F1.squeezeN (m + 1) = (σ (.n r) :: G1.1, G1.2) := by rw [squeezeN_succ', hS1]
  have hG1 : G1.2 = ⟨[σ (.n q), σ (.n (q + 1)), σ (.n (q + 2)), σ (.n (q + 3)), σ (.n (q + 4))], []⟩ :=
    fs_mk_eq eP1.symm (squeezeN_pend rfl m)
  set G2 := (⟨[σ (.n q), σ (.n (q + 1)), σ (.n (q + 2)), σ (.n (q + 3)), σ (.n (q + 4))], []⟩ :
    Fs).squeezeN (m + 1) with hG2d
  have hG2 : G2.2 = ⟨[σ (.n (t + 5)), σ (.n (t + 6)), σ (.n (t + 7)), σ (.n (t + 8)), σ (.n (t + 9))],
      []⟩ := by
    refine fs_mk_eq ?_ (squeezeN_pend rfl (m + 1))
    rw [← eP2, c5, c6, c7, c8, c9]
  set y0 := σ (.n (t + 10))
  set y1 := σ (.n (t + 14))
  set nn := σ (.n (t + 18))
  have hS : (G2.2.absorbAll [y0, y1] dsObserve).nonceState nn =
      (⟨[σ (.n (t + 5)), σ (.n (t + 6)), σ (.n (t + 7)), σ (.n (t + 8)), σ (.n (t + 9))],
        [(y0, dsObserve), (y1, dsObserve), (nn, dsPowNonce)]⟩ : Fs).perm := by
    rw [hG2, absorbAll_short _ _ _ (by simp)]
    simp [Fs.nonceState, Fs.absorb, rateScalars]
  simp only [osKeccak, stmtOk_atom] at hK
  have hout := keccakA_fs (s := (⟨[σ (.n (t + 5)), σ (.n (t + 6)), σ (.n (t + 7)), σ (.n (t + 8)),
      σ (.n (t + 9))], [(y0, dsObserve), (y1, dsObserve), (nn, dsPowNonce)]⟩ : Fs)) hK (by simp) (by
    simp [pendCells, Keccak.scalarCells, p1, p2, q1, q2, z1, z2, z3, z4, dsObserve,
      dsPowNonce, word, y0, y1, nn]
    exact ⟨rfl, rfl, word_zero⟩)
  rw [← hS] at hout
  have o : ∀ i : Fin 13, σ (.n (t + 23 + i.val)) =
      cellsOfState ((G2.2.absorbAll [y0, y1] dsObserve).nonceState nn) false i := outCellK hout
  have hxl' : high.length = lv.folds := by simp only [List.length_cons] at hxl; omega
  have hx0 : σ (.n (r + 8)) = x0 := loadHolds_unique ls0 (hsent 0 (by simp))
  have hx1 : σ (.n (r + 9)) = x1 := loadHolds_unique ls1 (hsent 1 (by simp))
  have hF1eq : (st.F σ).absorbAll (x0 :: x1 :: high) dsObserve = F1 := by rw [hF]
  have h2 : ReadsAt rd (OsSt.cur σ s0 * gen ^ (x0 :: x1 :: high).length) [y0, y1, nn] := by
    rw [hxl, ← ecur]
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    exacts [ly0, ly1, lnn]
  refine ⟨x0, x1, high, y0, y1, nn, ?_⟩
  dsimp only
  refine ⟨hxl', readsAt_append hrd h2, hsent, hx0 ▸ lr0, hx1 ▸ lr1, ?_, ?_, ⟨rfl, ?_, ?_⟩, ?_, ?_,
    ?_, ?_, rfl, hm1, rfl, rfl⟩
  · rw [hF1eq, hmm, hP1]; exact rP1
  · rw [hF1eq, hmm, hP1, hG1]; exact rP2
  · simpa [Nat.add_assoc] using p3
  · simpa [Nat.add_assoc] using q3
  · rw [hF1eq, hmm, hP1, hG1]; simpa [Nat.add_assoc] using o 0
  · rw [hF1eq, hmm, hP1, hG1]; simpa [Nat.add_assoc] using o 1
  · rw [hF1eq, hmm, hP1, hG1]
    have e8 : σ (.n (t + 31)) = _ := o 8
    have e9 : σ (.n (t + 32)) = _ := o 9
    have e10 : σ (.n (t + 33)) = _ := o 10
    have e11 : σ (.n (t + 34)) = _ := o 11
    have e12 : σ (.n (t + 35)) = _ := o 12
    show (⟨[σ (.n (t + 31)), σ (.n (t + 32)), σ (.n (t + 33)), σ (.n (t + 34)), σ (.n (t + 35))], []⟩ :
      Fs) = _
    rw [e8, e9, e10, e11, e12]
    rfl
  · simp only [OsSt.cur]
    rw [ecur]
    simp only [OsSt.cur, hs0]
    rw [mul_assoc, ← pow_add]
    ring_nf

end
end LeanVM.Guest.B1.Whir
