/-
  LeanVM.Guest.B1.Whir.Commit

  A non-final level's next commitment, high part, OOD nonce, point and value and query nonce
  (`osCommit`), and the final level's lane and query nonce (`osFinalMsg`), soundly.
-/

module

public import LeanVM.Guest.B1.Whir.Folds
public import LeanVM.Guest.B1.Fs.Message
public import LeanVM.Guest.B1.Whir.SqLoop

/-!
# The level's message (G:1568-1592)

`osCommit_sound`: `opening_message` reads the next root's two cells, the high part and the OOD
nonce at the cursor, stores the words in `sent` (the root also in `level_roots`), absorbs them and
permutes with the nonce; the grind passes on the permutation's cell `1` (`levelOodGrind` bits),
its cell `0` is the OOD point's first coordinate (`squeeze_point_from`); the value and the query
nonce are read at the cursor past the message and absorbed, the nonce's permutation leaving the
first query word and the proof of work in its cells `0`, `1` and the sponge's capacity. The
padding's zero run is allocated here at its first use (`PadOk`). `osFinalMsg_sound`: the final
lane and the nonce, by `opening_message` with a nonce.
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

/-- The zero run's cells past its first are zero, once it is allocated. -/
def PadOk (σ : Val) (pad : Option ℕ) : Prop :=
  ∀ p, pad = some p → σ (.n (p + 1)) = 0 ∧ σ (.n (p + 2)) = 0 ∧ σ (.n (p + 3)) = 0 ∧
    σ (.n (p + 4)) = 0

/-- The zero run, allocated if it was not: its cells are zero. -/
theorem osPad_ok {pad : Option ℕ} {k : ℕ} (hp : PadOk σ pad) (hok : AllOk C rd σ (osPad pad k).1) :
    PadOk σ (some (osPad pad k).2.1) := by
  intro p hpe
  simp only [Option.some.injEq] at hpe
  subst hpe
  cases pad with
  | some q => exact hp q rfl
  | none =>
    simp only [osPad, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_const, osCst] at hok ⊢
    obtain ⟨-, h1, h2, h3, h4⟩ := hok
    exact ⟨h1.trans word_zero, h2.trans word_zero, h3.trans word_zero, h4.trans word_zero⟩

/-- The sponge after a non-final level's message `xs` and its OOD nonce `n1`: the message absorbed
and the OOD grind's challenge drawn (`Fs.grindSqueeze`). -/
def oodG (F : Fs) (xs : List E) (n1 : E) : E × Fs :=
  (F.absorbAll xs dsObserve).grindSqueeze levelOodGrind n1

/-- The OOD point of a level of `mu` message coordinates: the grind's challenge, then `mu - 1`
squeezes; and the sponge after it. -/
def oodPt (F : Fs) (xs : List E) (n1 : E) (mu : ℕ) : List E × Fs :=
  ((oodG F xs n1).1 :: ((oodG F xs n1).2.squeezeN (mu - 1)).1, ((oodG F xs n1).2.squeezeN (mu - 1)).2)

/-- The query nonce's permutation after the OOD value `y0`. -/
def oodQ (F : Fs) (xs : List E) (n1 : E) (mu : ℕ) (y0 nn : E) : KeccakState :=
  ((oodPt F xs n1 mu).2.absorbAll [y0] dsObserve).nonceState nn

/-- What a non-final level's message leaves (G:1570-1588): the root's two cells `x0, x1` and the
high part read at the cursor, stored at `sent` and the root in `level_roots`; the OOD nonce `n1`
read past them, its grind passing; the OOD point squeezed from its permutation and stored in
`ood_z`; the value `y0` and the query nonce `nn` read past it; the query nonce's permutation. -/
structure CommitOut (rd : Reader) (σ : Val) (lvl : ℕ) (lv : OsLv) (st st' : OsSt)
    (x0 x1 : E) (high : List E) (n1 y0 nn : E) : Prop where
  high_len : high.length = lv.folds
  reads : ReadsAt rd (st.cur σ) (x0 :: x1 :: high ++ [n1, y0, nn])
  sent : ReadsAt rd (σ (.n st'.sent)) (x0 :: x1 :: high)
  root0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 2) x0
  root1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 3) x1
  oodOk : ((st.F σ).absorbAll (x0 :: x1 :: high) dsObserve).GrindOk levelOodGrind n1
  ood : ReadsAt rd (σ (.n osOodz) * gen ^ ((lvl + 1) * ligColsCap))
    (oodPt (st.F σ) (x0 :: x1 :: high) n1 lv.logCols).1
  ys : st'.ys = [st'.ys.getD 0 0] ∧ σ (.n (st'.ys.getD 0 0)) = y0
  word0 : σ (.n st'.word0) = cellsOfState (oodQ (st.F σ) (x0 :: x1 :: high) n1 lv.logCols y0 nn)
    false 0
  pow0 : σ (.n st'.pow0) = cellsOfState (oodQ (st.F σ) (x0 :: x1 :: high) n1 lv.logCols y0 nn)
    false 1
  F : st'.F σ = ⟨capOf (oodQ (st.F σ) (x0 :: x1 :: high) n1 lv.logCols y0 nn), []⟩
  cur : st'.cur σ = st.cur σ * gen ^ (lv.folds + 5)
  fs : st'.fs.length = 5
  mats : MatsOk σ st'.mats
  co : st'.co = 2
  pad : PadOk σ st'.pad

/-- **A non-final level's message, soundly** (G:1570-1592). -/
theorem osCommit_sound {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt}
    (hom : ∀ a r, C ("opening_message__L" ++ natStr (2 + lv.folds) ++ "_L1") a r →
      MeaningOpeningMessage (2 + lv.folds) 1 rd a r)
    (hgr : ∀ w, C ("grind_check__L" ++ natStr levelOodGrind) [w, σ (.n osTabs)] [] →
      (w.limb 0).lane.toNat % 2 ^ levelOodGrind = 0)
    (hspf : ∀ a r, C ("squeeze_point_from__L" ++ natStr lv.logCols) a r →
      MeaningSqueezePointFrom lv.logCols rd a r)
    (hfs : st.fs.length = 5) (hm : MatsOk σ st.mats)
    (hpad : PadOk σ st.pad) (hco : st.co < u128Bound)
    (hoff : (lvl + 1) * ligColsCap < u128Bound)
    (hok : AllOk C rd σ (osCommit c lvl lv st).1) :
    ∃ x0 x1 high n1 y0 nn,
      CommitOut rd σ lvl lv st (osCommit c lvl lv st).2 x0 x1 high n1 y0 nn := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fs_five st hfs
  unfold osCommit at hok ⊢
  simp only [allOk_append, and_assoc] at hok
  obtain ⟨-, hcu, hmsg, ho0, hspf', hcp, hn, hpd, hlast⟩ := hok
  set s0 : OsSt := { st with k := st.k + 2 } with hs0
  set r := (osCurS s0).2.2.k with hr
  set s1 : OsSt := { (osCurS s0).2.2 with k := r + 10 } with hs1
  set q := (osMatS c.plan osOodz ((lvl + 1) * ligColsCap) s1).2.2.k with hq
  set b := q + 10 with hb
  have hP := osPad_ok hpad hpd
  set p := (osPad (osMatS c.plan osOodz ((lvl + 1) * ligColsCap) s1).2.2.pad (b + 6)).2.1 with hp
  set j := (osPad (osMatS c.plan osOodz ((lvl + 1) * ligColsCap) s1).2.2.pad (b + 6)).2.2 with hj
  obtain ⟨z1, z2, z3, z4⟩ := hP p rfl
  have ecu := osCurS_val (s := s0) hco hcu
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_call, stmtOk_atom, holds_load, osLd,
    List.map_cons, List.map_nil] at hmsg
  obtain ⟨hcall, hg, ls0, lr0, ls1, lr1⟩ := hmsg
  have hM := hom _ _ hcall
  have hfm : List.map V.n st.fs = [.n f0, .n f1, .n f2, .n f3, .n f4] := by rw [hf]; rfl
  simp only [List.map_append, hfm, List.cons_append, List.nil_append, List.map_cons, List.map_nil, osRun,
    List.range_succ, List.range_zero, Nat.add_zero, MeaningOpeningMessage] at hM
  obtain ⟨xs, hxl, hrd, hsent, n1, hn1, hret⟩ := hM
  obtain ⟨x0, x1, high, rfl⟩ : ∃ x0 x1 high, xs = x0 :: x1 :: high := by
    rcases xs with _ | ⟨x0, _ | ⟨x1, high⟩⟩
    · simp only [List.length_nil] at hxl; omega
    · simp only [List.length_cons, List.length_nil] at hxl; omega
    · exact ⟨x0, x1, high, rfl⟩
  simp only [↓reduceIte, omState, capOf, List.cons_append, List.nil_append, List.cons.injEq] at hret
  obtain ⟨e0, e1, c0, c1, c2, c3, c4, ecur, -⟩ := hret
  rw [ecu] at hrd ecur hn1
  have hF : st.F σ = ⟨[σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)], []⟩ := by
    simp [OsSt.F, hf]
  set F1 := (st.F σ).absorbAll (x0 :: x1 :: high) dsObserve with hF1
  -- the OOD grind
  have e0' : σ (.n r) = cellsOfState (F1.nonceState n1) false 0 := by rw [hF1, hF]; exact e0
  have e1' : σ (.n (r + 1)) = cellsOfState (F1.nonceState n1) false 1 := by rw [hF1, hF]; exact e1
  have hlb : levelOodGrind ≠ 0 := by decide
  obtain ⟨gok, hgα, hgs⟩ := grindSqueeze_cells hlb n1 _ _ e0' e1' (hgr _ hg)
  have hG : oodG (st.F σ) (x0 :: x1 :: high) n1 =
      (σ (.n r), ⟨[σ (.n (r + 2)), σ (.n (r + 3)), σ (.n (r + 4)), σ (.n (r + 5)), σ (.n (r + 6))],
        []⟩) := by
    rw [oodG, ← hF1, Prod.ext_iff]
    refine ⟨hgα, ?_⟩
    rw [hgs]
    simp only [capOf, hF1, hF, c0, c1, c2, c3, c4]
  -- the OOD point
  obtain ⟨ev0, hm0⟩ := osMatS_val' ho0 hm hoff
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_call, List.map_cons, List.map_nil, osRun,
    List.range_succ, List.range_zero] at hspf'
  have hP1 := hspf _ _ hspf'
  simp only [MeaningSqueezePointFrom] at hP1
  obtain ⟨rP1, eP1⟩ := hP1
  rw [ev0] at rP1
  simp only [List.nil_append, List.cons_append, List.map_cons, List.map_nil, Nat.add_zero] at eP1
  set G1 := (⟨[σ (.n (r + 2)), σ (.n (r + 3)), σ (.n (r + 4)), σ (.n (r + 5)), σ (.n (r + 6))], []⟩ :
    Fs).squeezeN (lv.logCols - 1) with hG1d
  have hG1 : G1.2 = ⟨[σ (.n q), σ (.n (q + 1)), σ (.n (q + 2)), σ (.n (q + 3)), σ (.n (q + 4))], []⟩ :=
    fs_mk_eq eP1.symm (squeezeN_pend rfl _)
  have hPt : oodPt (st.F σ) (x0 :: x1 :: high) n1 lv.logCols = (σ (.n r) :: G1.1, G1.2) := by
    rw [oodPt, hG]
  -- the value, the query nonce and its permutation
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_copy, holds_load, holds_const,
    osCp, osLd, osCst, osKeccak, List.map_cons, List.map_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, Nat.add_zero] at hcp hn hlast
  obtain ⟨c5, c6, c7, c8, c9⟩ := hcp
  obtain ⟨ly0, p1, p2, lnn, q1, q2⟩ := hn
  simp only [Nat.add_assoc, Nat.reduceAdd] at c5 c6 c7 c8 c9 p1 p2 lnn q1 q2
  set y0 := σ (.n b)
  set nn := σ (.n (b + 3))
  have hQ : oodQ (st.F σ) (x0 :: x1 :: high) n1 lv.logCols y0 nn =
      (⟨[σ (.n (q + 5)), σ (.n (q + 6)), σ (.n (q + 7)), σ (.n (q + 8)), σ (.n (q + 9))],
        [(y0, dsObserve), (nn, dsPowNonce)]⟩ : Fs).perm := by
    rw [oodQ, hPt, hG1, c5, c6, c7, c8, c9]
    simp [Fs.absorbAll, Fs.nonceState, Fs.absorb, rateScalars]
  have hout := keccakA_fs (s := (⟨[σ (.n (q + 5)), σ (.n (q + 6)), σ (.n (q + 7)), σ (.n (q + 8)),
      σ (.n (q + 9))], [(y0, dsObserve), (nn, dsPowNonce)]⟩ : Fs)) hlast (by simp) (by
    simp [pendCells, Keccak.scalarCells, p1, p2, q1, q2, z1, z2, z3, z4, dsObserve,
      dsPowNonce, word, y0, nn]
    exact ⟨rfl, rfl⟩)
  rw [← hQ] at hout
  have o : ∀ i : Fin 13, σ (.n (j + i.val)) =
      cellsOfState (oodQ (st.F σ) (x0 :: x1 :: high) n1 lv.logCols y0 nn) false i := outCellK hout
  have hxl' : high.length = lv.folds := by simp only [List.length_cons] at hxl; omega
  have hx0 : σ (.n (r + 8)) = x0 := loadHolds_unique ls0 (hsent 0 (by simp))
  have hx1 : σ (.n (r + 9)) = x1 := loadHolds_unique ls1 (hsent 1 (by simp))
  have h2 : ReadsAt rd (OsSt.cur σ s0 * gen ^ (x0 :: x1 :: high).length) [n1, y0, nn] := by
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · show LoadHolds rd _ 0 n1
      rw [hxl]; exact (loadHolds_mul_gen_pow _ _ _ _ _).mpr (by simpa using hn1 trivial)
    · have := ly0; rw [ecur, loadHolds_mul_gen_pow] at this
      show LoadHolds rd _ 1 y0
      rw [loadHolds_mul_gen_pow, hxl]; simpa [Nat.add_assoc] using this
    · have := lnn; rw [ecur, loadHolds_mul_gen_pow] at this
      show LoadHolds rd _ 2 nn
      rw [loadHolds_mul_gen_pow, hxl]; simpa [Nat.add_assoc] using this
  refine ⟨x0, x1, high, n1, y0, nn, ?_⟩
  dsimp only
  refine ⟨hxl', readsAt_append hrd h2, hsent, hx0 ▸ lr0, hx1 ▸ lr1, gok, ?_, ⟨rfl, rfl⟩, ?_, ?_, ?_,
    ?_, rfl, hm0, rfl, ?_⟩
  · rw [hPt]; exact rP1
  · simpa using o 0
  · simpa using o 1
  · have e8 : σ (.n (j + 8)) = _ := o 8
    have e9 : σ (.n (j + 9)) = _ := o 9
    have e10 : σ (.n (j + 10)) = _ := o 10
    have e11 : σ (.n (j + 11)) = _ := o 11
    have e12 : σ (.n (j + 12)) = _ := o 12
    show (⟨[σ (.n (j + 8)), σ (.n (j + 9)), σ (.n (j + 10)), σ (.n (j + 11)), σ (.n (j + 12))], []⟩ :
      Fs) = _
    rw [e8, e9, e10, e11, e12]
    rfl
  · simp only [OsSt.cur]
    rw [ecur]
    simp only [OsSt.cur, hs0]
    rw [mul_assoc, ← pow_add]
    ring_nf
  · intro q' hq'
    simp only [Option.some.injEq] at hq'
    subst hq'
    exact ⟨z1, z2, z3, z4⟩

/-- What the final level's message leaves (G:1573-1574): the lane `xs` read at the cursor and
stored in `final_msg`, the nonce `nn` after it, the nonce's permutation `S` leaving the first
query word and the proof of work in its cells `0`, `1` and the sponge's capacity. -/
structure FinalOut (rd : Reader) (σ : Val) (n : ℕ) (st st' : OsSt) (xs : List E) (nn : E) : Prop where
  len : xs.length = n
  reads : ReadsAt rd (st.cur σ) (xs ++ [nn])
  fmsg : ReadsAt rd (σ (.n osFmsg)) xs
  word0 : σ (.n st'.word0) = cellsOfState (((st.F σ).absorbAll xs dsObserve).nonceState nn) false 0
  pow0 : σ (.n st'.pow0) = cellsOfState (((st.F σ).absorbAll xs dsObserve).nonceState nn) false 1
  F : st'.F σ = ⟨capOf (((st.F σ).absorbAll xs dsObserve).nonceState nn), []⟩
  cur : st'.cur σ = st.cur σ * gen ^ (n + 1)
  fs : st'.fs.length = 5
  mats : MatsOk σ st'.mats
  co : st'.co = 0
  pad : st'.pad = st.pad

/-- **The final level's message, soundly** (G:1573-1574). -/
theorem osFinalMsg_sound {c : OsCfg} {lv : OsLv} {st : OsSt}
    (hom : ∀ a r, C ("opening_message__L" ++ natStr (c.yrLen + lv.folds) ++ "_L1") a r →
      MeaningOpeningMessage (c.yrLen + lv.folds) 1 rd a r)
    (hfs : st.fs.length = 5) (hm : MatsOk σ st.mats) (hco : st.co < u128Bound)
    (hok : AllOk C rd σ (osFinalMsg c lv st).1) :
    ∃ xs nn, FinalOut rd σ (c.yrLen + lv.folds) st (osFinalMsg c lv st).2 xs nn := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fs_five st hfs
  unfold osFinalMsg at hok ⊢
  simp only [allOk_append] at hok
  obtain ⟨hcu, hcall⟩ := hok
  have ecu := osCurS_val hco hcu
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_call] at hcall
  have hM := hom _ _ hcall
  have hfm : List.map V.n st.fs = [.n f0, .n f1, .n f2, .n f3, .n f4] := by rw [hf]; rfl
  simp only [List.map_append, hfm, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
    osRun, List.range_succ, List.range_zero, MeaningOpeningMessage] at hM
  obtain ⟨xs, hxl, hrd, hfmsg, nn, hnn, hret⟩ := hM
  simp only [↓reduceIte, omState, capOf, List.cons_append, List.nil_append, List.cons.injEq] at hret
  obtain ⟨e0, e1, c0, c1, c2, c3, c4, ecur, -⟩ := hret
  rw [ecu] at hrd ecur hnn
  have hF : st.F σ = ⟨[σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)], []⟩ := by
    simp [OsSt.F, hf]
  refine ⟨xs, nn, hxl, readsAt_append hrd ?_, hfmsg, ?_, ?_, ?_, ?_, rfl, hm, rfl, rfl⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    rw [hxl]
    exact (loadHolds_mul_gen_pow _ _ _ _ _).mpr (by simpa using hnn trivial)
  · rw [hF]; exact e0
  · rw [hF]; exact e1
  · rw [hF]
    simp only [OsSt.F, capOf, List.map_cons, List.map_nil, c0, c1, c2, c3, c4]
  · simp only [OsSt.cur, pow_zero, mul_one]
    rw [ecur]
    rfl

end
end LeanVM.Guest.B1.Whir
