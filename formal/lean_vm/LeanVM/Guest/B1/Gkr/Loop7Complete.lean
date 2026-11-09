/-
  LeanVM.Guest.B1.Gkr.Loop7Complete

  `__loop6` is complete: an iteration holds on its honest valuation when the memory holds its
  slot, its step's words, its round records and the next slot; iterations at every `g^j`,
  `j < m`, give the loop.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop7C

/-!
# `__loop6`, completely (G:1852-1934)

`ly_iter`: from the slot of `L = 2j + sh` (`GkSlotC`), one step of two levels (`GkStepD.Ok`), its
words at the cursor, its round records (`RecsAt`) and the slot of `L + 2` the step leads to, the
iteration at `g^j` holds (its body evaluated forward, region by region), given the next
iteration below the bound. `LyIter`: those words for the iteration at `g^j`; `ly_complete`: with
them at every `j < m`, `__loop6` holds from `1` below `g^m`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The children's words read, by tree. -/
theorem lyCh_of {σ : Val} {ch0 ch1 ch2 : List E} (h0 : ch0.length = 4) (h1 : ch1.length = 4)
    (h2 : ch2.length = 4) (hv : ∀ i < 12, σ (.n (lyEv i)) = (ch0 ++ (ch1 ++ ch2)).getD i 0) :
    lyCh σ 0 = ch0 ∧ lyCh σ 1 = ch1 ∧ lyCh σ 2 = ch2 := by
  rw [list4_eq h0, list4_eq h1, list4_eq h2] at hv ⊢
  rw [lyCh_eq, lyCh_eq, lyCh_eq, hv (4 * 0) (by omega), hv (4 * 0 + 1) (by omega),
    hv (4 * 0 + 2) (by omega), hv (4 * 0 + 3) (by omega), hv (4 * 1) (by omega),
    hv (4 * 1 + 1) (by omega), hv (4 * 1 + 2) (by omega), hv (4 * 1 + 3) (by omega),
    hv (4 * 2) (by omega), hv (4 * 2 + 1) (by omega), hv (4 * 2 + 2) (by omega),
    hv (4 * 2 + 3) (by omega)]
  simp

theorem tb_squeezeN_two (s : Fs) : s.squeezeN 2 =
    ([challengeOf s.perm, challengeOf (permOf (rateOf [] ++ capOf s.perm))],
      ⟨capOf (permOf (rateOf [] ++ capOf s.perm)), []⟩) := rfl

/-- **An iteration of `__loop6`, completely.** -/
theorem ly_iter {rd : Reader} {N dsb gmu layers rounds kmn : E} {j sh : ℕ} (hj : j < 2 ^ 30)
    (hsh2 : sh < 2) (hN : IsInK N) (hsh : LoadHolds rd (dsb * gmu) 0 (gen ^ sh))
    (hkmn : KModNext rd kmn)
    {s : Fs} {cur : E} {st : GkrState} {row pos : E} {D : GkStepD}
    (hS : GkSlotC rd layers (2 * j + sh) s cur st row pos (gen ^ (j / 4)) (gen ^ (j % 4)))
    (hD : D.Ok s st 2) (hx : TbReadsAt rd cur D.xs)
    (hR : RecsAt rd (rounds * pos) cur D.cs st.point (polyEval st.values s.squeeze.1)
      s.squeeze.2)
    (hS' : GkSlotC rd layers (2 * j + sh + 2) (D.s' s st 2) (cur * gen ^ D.xs.length)
      (D.st' s st 2) (row * gen ^ 40) (pos * gen ^ (2 * j + sh + 1)) (gen ^ ((j + 1) / 4))
      (gen ^ ((j + 1) % 4)))
    (hnext : gen ^ j * gen + N ≠ 0 →
      coreProgram.Rel rd "__loop6" [gen ^ j * gen, N, dsb, gmu, layers, rounds, kmn] []) :
    coreProgram.Rel rd "__loop6" [gen ^ j, N, dsb, gmu, layers, rounds, kmn] [] := by
  obtain ⟨fn, hf, hp, hb⟩ := lyFound
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp ly_chk
  set args : List E := [gen ^ j, N, dsb, gmu, layers, rounds, kmn] with hargs
  have hc6 : chk args.length lyEvL = some c' := hc'
  set σ : Val := B1.Val.ofArgs (ev rd (fun _ => 0) args lyEvL) with hσ
  have hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s :=
    (ev_spec rd (fun _ => 0) lyEvL args hc6).2.2
  have par : ∀ i < 7, σ (.n i) = args.getD i 0 := fun i hi =>
    ev_params rd _ hc6 (by simpa [hargs] using hi)
  have e0 : σ (.n 0) = gen ^ j := par 0 (by omega)
  have e1 : σ (.n 1) = N := par 1 (by omega)
  have e2 : σ (.n 2) = dsb := par 2 (by omega)
  have e3 : σ (.n 3) = gmu := par 3 (by omega)
  have e4 : σ (.n 4) = layers := par 4 (by omega)
  have e5 : σ (.n 5) = rounds := par 5 (by omega)
  have e6 : σ (.n 6) = kmn := par 6 (by omega)
  have hS0 := hS
  obtain ⟨hcl, hcan, hpe, hcap, hrate, hcur, hvl, hval, hrow, hpl, hpt, hpos, hhalf, hpar⟩ := hS
  obtain ⟨-, -, -, hcap', hrate', hcur', -, hval', hrow', -, hpt', hpos', hhalf', hpar'⟩ := hS'
  obtain ⟨hl, h4, hl0, hl1, hl2, hchk⟩ := hD
  set L := 2 * j + sh with hL
  set run := D.run s st with hrun
  have hcsl : D.cs.length = L := hl.trans hpl
  -- the head
  obtain ⟨hc0, hu0, hm0⟩ := hR 0 (by omega)
  simp only [List.take_zero, gkrRun, pow_zero, mul_one, Nat.mul_zero] at hc0 hu0 hm0
  obtain ⟨R1, e7, e10, e16, e50, e51, e52, m53, e62, e63, e65, e66, c27, c28, c29, c30⟩ :=
    lyc_head (C := coreProgram.Rel rd) (kret := fun rs => rs = []) hG e0
      (by rw [e2, e3]; exact hsh) (by rw [e4]; exact hS0) (by rw [e5]; exact hc0)
      (by rw [e5]; exact hu0) (by rw [e5]; exact hm0)
  rw [e5] at m53
  -- the rounds
  have hflat : TbReadsAt rd cur D.cs.flatten := (tbReadsAt_append.mp hx).1
  have hysl : (D.ys s st 2).length = 2 := rfl
  have hpt2 := tbReadsAt_append.mp hpt'
  have hch42 : TbReadsAt rd (row * gen ^ 42) run.1 := by
    have := hpt2.2
    rwa [hysl, mul_assoc, ← pow_add] at this
  have hT : ∀ a k, a + k ≤ L →
      TbGkrRoundsOut k rd (σ (.n 53) * gen ^ a) (σ (.n 51) * gen ^ a) := by
    intro a k hak
    rw [m53, e51]
    exact recs_rounds hR rfl (tb_capOf_canonical _) hl h4 hflat hpt hch42 (by omega)
  have R2 := lyc_rounds (kret := fun rs => rs = []) hG hj hsh2 e7 e10 e62 e63 e65 e66 hT
  -- the last record
  obtain ⟨hcL, huL, hlL⟩ := hR L (by omega)
  have htk : D.cs.take L = D.cs := List.take_of_length_le (by omega)
  have htp : st.point.take L = st.point := List.take_of_length_le (by omega)
  rw [htk, htp] at hcL hlL
  obtain ⟨R3, e78, e83, e84⟩ := lyc_last (C := coreProgram.Rel rd) (kret := fun rs => rs = [])
    hG e10 (by rw [m53]; exact hcL) (by rw [m53]; exact huL) (by rw [m53]; exact hlL)
  -- the children
  have hchl : (D.ch0 ++ (D.ch1 ++ D.ch2)).length = 12 := by simp [hl0, hl1, hl2]
  have hrc : TbReadsAt rd (σ (.n 83)) (D.ch0 ++ (D.ch1 ++ D.ch2)) := by
    have := (tbReadsAt_append.mp hx).2
    rwa [flatten_length_four h4, hcsl, ← e83] at this
  have hcanR : AllCanonical run.2.2.cap := tb_gkrRun_canonical _ _ _ _ (tb_capOf_canonical _)
  obtain ⟨R4, EV, B1⟩ := lyc_children (C := coreProgram.Rel rd) (kret := fun rs => rs = []) hG
    hcL.1 hcanR e78 hchl hrc
  obtain ⟨hch0, hch1, hch2⟩ := lyCh_of hl0 hl1 hl2 fun i hi => (EV i hi).1
  rw [hch0, hch1] at B1
  -- the check and the new coordinates
  have hcheck : σ (.n 84) =
      polyEval [prodE (lyCh σ 0), prodE (lyCh σ 1), prodE (lyCh σ 2)] (σ (.n 50)) := by
    rw [e84, hch0, hch1, hch2, e50]; exact hchk
  obtain ⟨R5, e278, e298, e287⟩ := lyc_check (C := coreProgram.Rel rd)
    (kret := fun rs => rs = []) hG (fun i hi => (EV i hi).2.1) (fun i hi => (EV i hi).2.2.1)
    (fun i hi => (EV i hi).2.2.2) B1 hcheck c27 c28 c29 c30
  rw [hch2] at e278 e298 e287
  have hpend : run.2.2.pend = [] :=
    tb_gkrRun_pend D.cs st.point (polyEval st.values s.squeeze.1) s.squeeze.2 rfl
  have hp0 : run.2.2 = ⟨run.2.2.cap, []⟩ := by rw [← hpend]
  have hsb : D.sb s st = ⟨capOf (Fs.perm ⟨capOf (Fs.perm ⟨run.2.2.cap,
      D.ch0.map (·, dsObserve)⟩), D.ch1.map (·, dsObserve)⟩), D.ch2.map (·, dsObserve)⟩ := by
    show (((run.2.2.absorbAll D.ch0 dsObserve).absorbAll D.ch1 dsObserve).absorbAll D.ch2
      dsObserve) = _
    rw [hp0, absorbAll_short ⟨run.2.2.cap, []⟩ D.ch0 dsObserve (by simp [hl0]), List.nil_append,
      tb_absorbAll_full ⟨run.2.2.cap, D.ch0.map (·, dsObserve)⟩ (by simp [hl0]) D.ch1 hl1,
      tb_absorbAll_full _ (by simp [hl1]) D.ch2 hl2]
  have hys : D.ys s st 2 = [σ (.n 278), σ (.n 298)] := by
    rw [e278, e298]; show ((D.sb s st).squeezeN 2).1 = _; rw [hsb, tb_squeezeN_two]; rfl
  have hs' : D.s' s st 2 = ⟨(List.range 5).map fun k ↦ σ (.n (287 + k)), []⟩ := by
    rw [e287]; show ((D.sb s st).squeezeN 2).2 = _; rw [hsb, tb_squeezeN_two]; rfl
  -- the next slot
  have ld : ∀ k w, LoadHolds rd layers (17 * (L + 2) + k) w →
      LoadHolds rd (σ (.n 16)) (34 + k) w := fun k w h => by
    rw [e16, e4, tb_loadHolds_mul_gen_pow, show 17 * L + (34 + k) = 17 * (L + 2) + k by ring]
    exact h
  have s34 : ∀ k < 5, LoadHolds rd (σ (.n 16)) (34 + k) (σ (.n (287 + k))) := by
    intro k hk
    have := hcap' k hk
    rw [hs'] at this
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
      Option.map_some, Option.getD_some] at this
    exact ld k _ this
  have s47 : ∀ k < 4, LoadHolds rd (σ (.n 16)) (47 + k) 0 := by
    intro k hk
    have := hrate' k hk
    rw [hs', tb_rateOf_nil_getD, show 17 * (L + 2) + 13 + k = 17 * (L + 2) + (13 + k) by ring]
      at this
    have h := ld (13 + k) _ this
    rwa [show 34 + (13 + k) = 47 + k by ring] at h
  have hxl : D.xs.length = 4 * L + 12 := by
    simp [GkStepD.xs, flatten_length_four h4, hcsl, hl0, hl1, hl2]
  have s39 : LoadHolds rd (σ (.n 16)) 39 (σ (.n 83) * gen ^ 12) := by
    have h := ld 5 _ hcur'
    rw [hxl] at h
    rw [e83, mul_assoc, ← pow_add]
    exact h
  have sv : ∀ t < 3, LoadHolds rd (σ (.n 16)) (40 + t)
      (multilinearEval (lyCh σ t) [σ (.n 278), σ (.n 298)]) := by
    intro t ht
    have h := ld (6 + t) _ (by rw [← Nat.add_assoc]; exact hval' t ht)
    rw [show 34 + (6 + t) = 40 + t by ring] at h
    have hv : (D.st' s st 2).values.getD t 0 =
        multilinearEval (lyCh σ t) [σ (.n 278), σ (.n 298)] := by
      show ([D.ch0, D.ch1, D.ch2].map (multilinearEval · (D.ys s st 2))).getD t 0 = _
      rw [hys]
      interval_cases t
      · rw [hch0]; rfl
      · rw [hch1]; rfl
      · rw [hch2]; rfl
    rwa [hv] at h
  have s43 : LoadHolds rd (σ (.n 16)) 43 (σ (.n 51) * gen ^ 40) := by
    have h := ld 9 _ hrow'
    rw [e51] at ⊢; exact h
  have s44 : LoadHolds rd (σ (.n 16)) 44 (σ (.n 52) * σ (.n 10) * gen) := by
    have h := ld 10 _ hpos'
    rwa [e52, e10, mul_assoc, ← pow_succ]
  obtain ⟨k4, k0⟩ := hkmn (j % 4) (Nat.mod_lt _ (by omega))
  have k4' : LoadHolds rd (σ (.n 6) * σ (.n 63)) 4 (gen ^ ((j % 4 + 1) / 4)) := by
    rw [e6, e63, tb_loadHolds_mul_gen_pow, show j % 4 + 4 = 4 + j % 4 by omega]; exact k4
  have k0' : LoadHolds rd (σ (.n 6) * σ (.n 63)) 0 (gen ^ ((j % 4 + 1) % 4)) := by
    rw [e6, e63, tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact k0
  have s45 : LoadHolds rd (σ (.n 16)) 45 (σ (.n 62) * gen ^ ((j % 4 + 1) / 4)) := by
    have h := ld 11 _ hhalf'
    rwa [e62, ly_half_next j]
  have s46 : LoadHolds rd (σ (.n 16)) 46 (gen ^ ((j % 4 + 1) % 4)) := by
    have h := ld 12 _ hpar'
    rwa [ly_parity_next j]
  have s40 : LoadHolds rd (σ (.n 51)) 40 (σ (.n 278)) := by
    have h := hpt2.1 0 (by rw [hysl]; omega)
    simp only [hys, List.getElem_cons_zero] at h
    rw [tb_loadHolds_mul_gen_pow] at h
    rw [e51]; exact h
  have s41 : LoadHolds rd (σ (.n 51)) 41 (σ (.n 298)) := by
    have h := hpt2.1 1 (by rw [hysl]; omega)
    simp only [hys, List.getElem_cons_succ, List.getElem_cons_zero] at h
    rw [tb_loadHolds_mul_gen_pow] at h
    rw [e51]; exact h
  have hK : IsInK (σ (.n 0) * gen + σ (.n 1)) := by
    rw [e0, e1]
    exact tb_isInK_add (tb_isInK_mul (tb_gen_pow_isInK _) (by simpa using tb_gen_pow_isInK 1)) hN
  have R6 := lyc_stores (C := coreProgram.Rel rd) (kret := fun rs => rs = []) hG
    (fun i hi => (EV i hi).2.1) s40 s41 s34 s47 s39 sv s43 s44 k4' k0' s45 s46 hK (fun hne => by
      rw [e0, e1] at hne; rw [e0, e1, e2, e3, e4, e5, e6]; exact hnext hne)
  refine (tb_rel_pre hf (hb.trans lyBody_eq) lyPre_noRet args []).mpr ⟨σ, ?_, ?_, rfl⟩
  · rw [hp]
    simp only [List.map_cons, List.map_nil]
    rw [e0, e1, e2, e3, e4, e5, e6]
  · rw [lyPre_eq]
    repeat rw [tb_holdsList_append_noRet (by decide +kernel)]
    exact ⟨⟨⟨⟨⟨R1, R2⟩, R3⟩, R4⟩, R5⟩, R6⟩

/-- **An iteration's words**: the slot of `L = 2j + sh`, one step of two levels, its words at the
cursor, its round records, and the slot of `L + 2`. -/
def LyIter (rd : Reader) (layers rounds : E) (sh j : ℕ) : Prop :=
  ∃ (s : Fs) (cur : E) (st : GkrState) (row pos : E) (D : GkStepD),
    GkSlotC rd layers (2 * j + sh) s cur st row pos (gen ^ (j / 4)) (gen ^ (j % 4)) ∧
    D.Ok s st 2 ∧ TbReadsAt rd cur D.xs ∧
    RecsAt rd (rounds * pos) cur D.cs st.point (polyEval st.values s.squeeze.1) s.squeeze.2 ∧
    GkSlotC rd layers (2 * j + sh + 2) (D.s' s st 2) (cur * gen ^ D.xs.length) (D.st' s st 2)
      (row * gen ^ 40) (pos * gen ^ (2 * j + sh + 1)) (gen ^ ((j + 1) / 4))
      (gen ^ ((j + 1) % 4))

/-- **`__loop6`, completely**: an iteration's words at every `j < m` give the loop from `1` below
`g^m`. -/
theorem ly_complete {rd : Reader} {dsb gmu layers rounds kmn : E} {sh m : ℕ} (hm : 0 < m)
    (hmb : m < 2 ^ 30) (hsh2 : sh < 2) (hsh : LoadHolds rd (dsb * gmu) 0 (gen ^ sh))
    (hkmn : KModNext rd kmn) (hit : ∀ j < m, LyIter rd layers rounds sh j) :
    coreProgram.Rel rd "__loop6" [1, gen ^ m, dsb, gmu, layers, rounds, kmn] [] := by
  have key : ∀ t, t < m → coreProgram.Rel rd "__loop6"
      [gen ^ (m - 1 - t), gen ^ m, dsb, gmu, layers, rounds, kmn] [] := by
    intro t
    induction t with
    | zero =>
      intro _
      obtain ⟨s, cur, st, row, pos, D, h1, h2, h3, h4, h5⟩ := hit (m - 1 - 0) (by omega)
      refine ly_iter (by omega) hsh2 (tb_gen_pow_isInK _) hsh hkmn h1 h2 h3 h4 h5 fun hne => ?_
      rw [← pow_succ, show m - 1 - 0 + 1 = m by omega, e_add_self] at hne
      exact absurd rfl hne
    | succ t ih =>
      intro ht
      obtain ⟨s, cur, st, row, pos, D, h1, h2, h3, h4, h5⟩ := hit (m - 1 - (t + 1)) (by omega)
      refine ly_iter (by omega) hsh2 (tb_gen_pow_isInK _) hsh hkmn h1 h2 h3 h4 h5 fun _ => ?_
      rw [← pow_succ, show m - 1 - (t + 1) + 1 = m - 1 - t by omega]
      exact ih (by omega)
  have := key (m - 1) (by omega)
  rwa [show m - 1 - (m - 1) = 0 by omega, pow_zero] at this

end
end LeanVM.Guest.B1.Tables
