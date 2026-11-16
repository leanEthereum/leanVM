/-
  LeanVM.Guest.B1.Gkr.Loop7Complete

  `verify_bus_gkr_loop0` is complete: an iteration holds on its honest valuation when the memory
  holds its slot, its step's words, its round records and the next slot; iterations at every `g^j`,
  `j < m`, give the loop.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop7C
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_bus_gkr_loop0`, completely

`ly_iter`: from the slot of `L = 2j + 2 - sh` (`GkSlot`), one step of two levels
(`GkStepD.Ok`), its words at the cursor, its round records (`LyRecs`), at an odd depth the row's
zero cell after the challenges, and the slot of `L + 2` the step leads to, the iteration at `g^j`
holds (its body evaluated forward, region by region), given
the next iteration below the bound. `LyIter`: those words for the iteration at `g^j`;
`ly_complete`: with them at every `j < m`, `verify_bus_gkr_loop0` holds from `1` below `g^m`.
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

/-- `verify_bus_gkr_loop0`'s arguments at `x = g^j`. -/
def lyArgs (x N : E) (sh : ℕ) (layers tabs pts rounds u stream gmu : E) : List E :=
  [x, N, gen ^ (2 - sh), layers, tabs, pts, rounds, u, gen ^ sh, stream, gmu]

/-- **An iteration of `verify_bus_gkr_loop0`, completely.** -/
theorem ly_iter {rd : Reader} {N layers tabs pts rounds u stream gmu : E} {j sh : ℕ}
    (hj : j < 2 ^ 30) (hsh2 : sh < 2) (hN : IsInK N)
    {s : Fs} {cur : E} {st : GkrState} {pos : E} {D : GkStepD}
    (hS : GkSlot rd layers (2 * j + 2 - sh) s cur st (pts * gen ^ (40 * (j + 1))) pos)
    (hD : D.Ok s st 2) (hx : TbReadsAt rd cur D.xs)
    (hR : LyRecs rd (rounds * pos) cur D.cs st.point (polyEval st.values s.squeeze.1)
      s.squeeze.2 j)
    (hpad : sh = 1 → LoadHolds rd (pts * gen ^ (40 * (j + 1))) (2 * j + 43) 0)
    (hS' : GkSlot rd layers (2 * j + 2 - sh + 2) (D.s' s st 2) (cur * gen ^ D.xs.length)
      (D.st' s st 2) (pts * gen ^ (40 * (j + 2))) (pos * gen ^ (j + 2)))
    (hnext : gen ^ j * gen + N ≠ 0 →
      coreProgram.Rel rd name% «verify_bus_gkr_loop0» (lyArgs (gen ^ j * gen) N sh layers tabs
          pts rounds u stream gmu) []) :
    coreProgram.Rel rd name% «verify_bus_gkr_loop0» (lyArgs (gen ^ j) N sh layers tabs pts rounds
        u stream gmu) [] := by
  obtain ⟨fn, hf, hp, hb⟩ := lyFound
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp ly_chk
  set args : List E := lyArgs (gen ^ j) N sh layers tabs pts rounds u stream gmu with hargs
  have hc6 : chk args.length lyEvL = some c' := hc'
  set σ : Val := B1.Val.ofArgs (ev rd (fun _ => 0) args lyEvL) with hσ
  have hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s :=
    (ev_spec rd (fun _ => 0) lyEvL args hc6).2.2
  have par : ∀ i < 11, σ (.n i) = args.getD i 0 := fun i hi =>
    ev_params rd _ hc6 (by simpa [hargs, lyArgs] using hi)
  have e0 : σ (.n 0) = gen ^ j := par 0 (by omega)
  have e1 : σ (.n 1) = N := par 1 (by omega)
  have e2 : σ (.n 2) = gen ^ (2 - sh) := par 2 (by omega)
  have e3 : σ (.n 3) = layers := par 3 (by omega)
  have e4 : σ (.n 4) = tabs := par 4 (by omega)
  have e5 : σ (.n 5) = pts := par 5 (by omega)
  have e6 : σ (.n 6) = rounds := par 6 (by omega)
  have e7 : σ (.n 7) = u := par 7 (by omega)
  have e8 : σ (.n 8) = gen ^ sh := par 8 (by omega)
  have e9 : σ (.n 9) = stream := par 9 (by omega)
  have e10 : σ (.n 10) = gmu := par 10 (by omega)
  set L := 2 * j + 2 - sh with hL
  have hS0 := hS
  obtain ⟨hcl, hcap, hpe, hcur, hvl, hval, hpl, hpt, hpos⟩ := hS
  obtain ⟨-, hcap', -, hcur', -, hval', -, hpt', hpos'⟩ := hS'
  obtain ⟨hl, h4, hl0, hl1, hl2, hchk⟩ := hD
  set run := D.run s st with hrun
  have hcsl : D.cs.length = L := hl.trans hpl
  obtain ⟨hRy, hRl⟩ := hR
  -- the head
  obtain ⟨hc0, hu0, hm0⟩ := hRy 0 (by omega)
  simp only [List.take_zero, gkrRun, pow_zero, mul_one, Nat.mul_zero] at hc0 hu0 hm0
  obtain ⟨R1, e11, e12, e17, e42, e46, e55, e56, c25, c26, c27, c28⟩ :=
    lyc_head (C := coreProgram.Rel rd) (kret := fun rs => rs = []) hG e0 e2 hsh2
      (by rw [e3]; exact hS0) (by rw [e6]; exact hc0) (by rw [e6]; exact hu0)
      (by rw [e6]; exact hm0)
  rw [e6] at e56
  rw [e5] at e55
  -- the rounds
  have hflat : TbReadsAt rd cur D.cs.flatten := (tbReadsAt_append.mp hx).1
  have hysl : (D.ys s st 2).length = 2 := rfl
  have hpt2 := tbReadsAt_append.mp hpt'
  have hch42 : TbReadsAt rd (pts * gen ^ (40 * (j + 1)) * gen ^ 42) run.1 := by
    have := hpt2.2
    rwa [hysl, mul_assoc, ← pow_add, show 40 * (j + 2) + 2 = 40 * (j + 1) + 42 by ring, pow_add,
      ← mul_assoc] at this
  have hp0 : s.squeeze.2.pend = [] := rfl
  have hT : ∀ y < j, TbGkrRoundsOut 2 1 rd (σ (.n 56) * gen ^ y) (σ (.n 55) * gen ^ (2 * y)) := by
    intro y hy
    rw [e56, e55]
    refine recs_rounds hp0 hl h4 hflat hpt hch42 (by omega) (hRy y (by omega)) ?_
    rw [mul_assoc, ← pow_add, show 2 * y + 2 = 2 * (y + 1) by ring]
    exact hRy (y + 1) (by omega)
  have hTl : TbGkrRoundsOut (2 - sh) 1 rd (σ (.n 56) * gen ^ j) (σ (.n 55) * gen ^ (2 * j)) := by
    rw [e56, e55]
    refine recs_rounds hp0 hl h4 hflat hpt hch42 (by omega) (hRy j le_rfl) ?_
    rw [mul_assoc, ← pow_add, show 2 * j + (2 - sh) = D.cs.length by omega]
    exact hRl
  have hpad' : sh = 1 → LoadHolds rd (σ (.n 55) * gen ^ (2 * j)) 43 0 := fun h1 => by
    rw [e55, tb_loadHolds_mul_gen_pow, show 2 * j + 43 = 2 * j + 43 from rfl]
    exact hpad h1
  have R2 := lyc_rounds (kret := fun rs => rs = []) hG hj hsh2 e0 e11 e8 hT hTl hpad'
  -- the last record
  obtain ⟨hcL, huL, hlL⟩ := hRl
  have htk : D.cs.take D.cs.length = D.cs := List.take_length
  have htp : st.point.take D.cs.length = st.point := List.take_of_length_le (by omega)
  rw [htk, htp] at hcL hlL
  obtain ⟨R3, e74, e75, e80⟩ := lyc_last (C := coreProgram.Rel rd) (kret := fun rs => rs = [])
    hG e0 (by rw [e56]; exact hcL) (by rw [e56]; exact huL)
  -- the children
  have hchl : (D.ch0 ++ (D.ch1 ++ D.ch2)).length = 12 := by simp [hl0, hl1, hl2]
  have hrc : TbReadsAt rd (σ (.n 80)) (D.ch0 ++ (D.ch1 ++ D.ch2)) := by
    have := (tbReadsAt_append.mp hx).2
    rwa [flatten_length_four h4, ← e80] at this
  obtain ⟨R4, EV, B1⟩ := lyc_children (C := coreProgram.Rel rd) (kret := fun rs => rs = []) hG
    hcL.1 e75 hchl hrc
  obtain ⟨hch0, hch1, hch2⟩ := lyCh_of hl0 hl1 hl2 fun i hi => (EV i hi).1
  rw [hch0, hch1] at B1
  -- the check and the new coordinates
  have hcheck : run.2.1 =
      polyEval [prodE (lyCh σ 0), prodE (lyCh σ 1), prodE (lyCh σ 2)] (σ (.n 42)) := by
    rw [hch0, hch1, hch2, e42]; exact hchk
  obtain ⟨R5, e185, e199, e194⟩ := lyc_check (C := coreProgram.Rel rd)
    (kret := fun rs => rs = []) hG (fun i hi => (EV i hi).2.1) (fun i hi => (EV i hi).2.2) B1
    (by rw [e74, e56]; exact hlL) hcheck c25 c26 c27 c28
  rw [hch2] at e185 e199 e194
  have hpend : run.2.2.pend = [] :=
    tb_gkrRun_pend D.cs st.point (polyEval st.values s.squeeze.1) s.squeeze.2 rfl
  have hp0' : run.2.2 = ⟨run.2.2.cap, []⟩ := by rw [← hpend]
  have hsb : D.sb s st = ⟨capOf (Fs.perm ⟨capOf (Fs.perm ⟨run.2.2.cap,
      D.ch0.map (·, dsObserve)⟩), D.ch1.map (·, dsObserve)⟩), D.ch2.map (·, dsObserve)⟩ := by
    show (((run.2.2.absorbAll D.ch0 dsObserve).absorbAll D.ch1 dsObserve).absorbAll D.ch2
      dsObserve) = _
    rw [hp0', absorbAll_short ⟨run.2.2.cap, []⟩ D.ch0 dsObserve (by simp [hl0]), List.nil_append,
      tb_absorbAll_full ⟨run.2.2.cap, D.ch0.map (·, dsObserve)⟩ (by simp [hl0]) D.ch1 hl1,
      tb_absorbAll_full _ (by simp [hl1]) D.ch2 hl2]
  have hys : D.ys s st 2 = [σ (.n 185), σ (.n 199)] := by
    rw [e185, e199]; show ((D.sb s st).squeezeN 2).1 = _; rw [hsb, tb_squeezeN_two]; rfl
  have hs' : D.s' s st 2 = ⟨(List.range 5).map fun k ↦ σ (.n (194 + k)), []⟩ := by
    rw [e194]; show ((D.sb s st).squeezeN 2).2 = _; rw [hsb, tb_squeezeN_two]; rfl
  -- the next slot
  have ld : ∀ k w, LoadHolds rd layers (10 * (L + 2) + k) w →
      LoadHolds rd (σ (.n 17)) (20 + k) w := fun k w h => by
    rw [e17, e3, tb_loadHolds_mul_gen_pow, show 10 * L + (20 + k) = 10 * (L + 2) + k by ring]
    exact h
  have s20 : ∀ k < 5, LoadHolds rd (σ (.n 17)) (20 + k) (σ (.n (194 + k))) := by
    intro k hk
    have := hcap' k hk
    rw [hs'] at this
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
      Option.map_some, Option.getD_some] at this
    exact ld k _ this
  have hxl : D.xs.length = 4 * L + 12 := by
    simp [GkStepD.xs, flatten_length_four h4, hcsl, hl0, hl1, hl2]
  have s25 : LoadHolds rd (σ (.n 17)) 25 (σ (.n 80) * gen ^ 12) := by
    have h := ld 5 _ hcur'
    rw [hxl] at h
    rw [e80, hcsl, mul_assoc, ← pow_add]
    exact h
  have sv : ∀ t < 3, LoadHolds rd (σ (.n 17)) (26 + t)
      (multilinearEval (lyCh σ t) [σ (.n 185), σ (.n 199)]) := by
    intro t ht
    have h := ld (6 + t) _ (by rw [← Nat.add_assoc]; exact hval' t ht)
    rw [show 20 + (6 + t) = 26 + t by ring] at h
    have hv : (D.st' s st 2).values.getD t 0 =
        multilinearEval (lyCh σ t) [σ (.n 185), σ (.n 199)] := by
      show ([D.ch0, D.ch1, D.ch2].map (multilinearEval · (D.ys s st 2))).getD t 0 = _
      rw [hys]
      interval_cases t
      · rw [hch0]; rfl
      · rw [hch1]; rfl
      · rw [hch2]; rfl
    rwa [hv] at h
  have s29 : LoadHolds rd (σ (.n 17)) 29 (σ (.n 46) * σ (.n 0) * gen ^ 2) := by
    have h := ld 9 _ hpos'
    rwa [e46, e0, mul_assoc, ← pow_add]
  have hrow' : σ (.n 55) * gen ^ 40 = pts * gen ^ (40 * (j + 2)) := by
    rw [e55, mul_assoc, ← pow_add]; ring_nf
  have s40 : LoadHolds rd (σ (.n 55)) 40 (σ (.n 185)) := by
    have h := hpt2.1 0 (by rw [hysl]; omega)
    simp only [hys, List.getElem_cons_zero] at h
    rw [← hrow', tb_loadHolds_mul_gen_pow] at h
    exact h
  have s41 : LoadHolds rd (σ (.n 55)) 41 (σ (.n 199)) := by
    have h := hpt2.1 1 (by rw [hysl]; omega)
    simp only [hys, List.getElem_cons_succ, List.getElem_cons_zero] at h
    rw [← hrow', tb_loadHolds_mul_gen_pow] at h
    exact h
  have hK : IsInK (σ (.n 0) * gen + σ (.n 1)) := by
    rw [e0, e1]
    exact tb_isInK_add (tb_isInK_mul (tb_gen_pow_isInK _) (by simpa using tb_gen_pow_isInK 1)) hN
  have R6 := lyc_stores (C := coreProgram.Rel rd) (kret := fun rs => rs = []) hG
    (fun i hi => (EV i hi).2.1) s40 s41 s20 s25 sv s29 hK (fun hne => by
      rw [e0, e1] at hne
      rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      exact hnext hne)
  refine (tb_rel_pre hf (hb.trans lyBody_eq) lyPre_noRet args []).mpr ⟨σ, ?_, ?_, rfl⟩
  · rw [hp]
    show [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7),
      σ (.n 8), σ (.n 9), σ (.n 10)] = args
    rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
    rfl
  · rw [lyPre_eq]
    refine (tb_holdsList_append_noRet (A := lyR1 ++ lyR2 ++ lyR3 ++ lyR4 ++ lyR5)
      (by decide +kernel)).mpr ⟨?_, R6⟩
    refine (tb_holdsList_append_noRet (A := lyR1 ++ lyR2 ++ lyR3 ++ lyR4)
      (by decide +kernel)).mpr ⟨?_, R5⟩
    refine (tb_holdsList_append_noRet (A := lyR1 ++ lyR2 ++ lyR3)
      (by decide +kernel)).mpr ⟨?_, R4⟩
    refine (tb_holdsList_append_noRet (A := lyR1 ++ lyR2) (by decide +kernel)).mpr ⟨?_, R3⟩
    exact (tb_holdsList_append_noRet (A := lyR1) (by decide +kernel)).mpr ⟨R1, R2⟩

/-- **An iteration's words**: the slot of `L = 2j + 2 - sh`, its point in row `j + 1`, one step of
two levels, its words at the cursor, its round records, at an odd depth the row's zero cell after
the challenges, and the slot of `L + 2`. -/
def LyIter (rd : Reader) (layers pts rounds : E) (sh j : ℕ) : Prop :=
  ∃ (s : Fs) (cur : E) (st : GkrState) (pos : E) (D : GkStepD),
    GkSlot rd layers (2 * j + 2 - sh) s cur st (pts * gen ^ (40 * (j + 1))) pos ∧
    D.Ok s st 2 ∧ TbReadsAt rd cur D.xs ∧
    LyRecs rd (rounds * pos) cur D.cs st.point (polyEval st.values s.squeeze.1) s.squeeze.2 j ∧
    (sh = 1 → LoadHolds rd (pts * gen ^ (40 * (j + 1))) (2 * j + 43) 0) ∧
    GkSlot rd layers (2 * j + 2 - sh + 2) (D.s' s st 2) (cur * gen ^ D.xs.length) (D.st' s st 2)
      (pts * gen ^ (40 * (j + 2))) (pos * gen ^ (j + 2))

/-- **`verify_bus_gkr_loop0`, completely**: an iteration's words at every `j < m` give the loop from
`1` below `g^m`. -/
theorem ly_complete {rd : Reader} {layers tabs pts rounds u stream gmu : E} {sh m : ℕ}
    (hm : 0 < m) (hmb : m < 2 ^ 30) (hsh2 : sh < 2)
    (hit : ∀ j < m, LyIter rd layers pts rounds sh j) :
    coreProgram.Rel rd name% «verify_bus_gkr_loop0» (lyArgs 1 (gen ^ m) sh layers tabs pts rounds
        u stream gmu) [] := by
  have key : ∀ t, t < m → coreProgram.Rel rd name% «verify_bus_gkr_loop0»
      (lyArgs (gen ^ (m - 1 - t)) (gen ^ m) sh layers tabs pts rounds u stream gmu) [] := by
    intro t
    induction t with
    | zero =>
      intro _
      obtain ⟨s, cur, st, pos, D, h1, h2, h3, h4, h5, h6⟩ := hit (m - 1 - 0) (by omega)
      refine ly_iter (by omega) hsh2 (tb_gen_pow_isInK _) h1 h2 h3 h4 h5 h6 fun hne => ?_
      rw [← pow_succ, show m - 1 - 0 + 1 = m by omega, e_add_self] at hne
      exact absurd rfl hne
    | succ t ih =>
      intro ht
      obtain ⟨s, cur, st, pos, D, h1, h2, h3, h4, h5, h6⟩ := hit (m - 1 - (t + 1)) (by omega)
      refine ly_iter (by omega) hsh2 (tb_gen_pow_isInK _) h1 h2 h3 h4 h5 h6 fun _ => ?_
      rw [← pow_succ, show m - 1 - (t + 1) + 1 = m - 1 - t by omega]
      exact ih (by omega)
  have := key (m - 1) (by omega)
  rwa [show m - 1 - (m - 1) = 0 by omega, pow_zero] at this

end
end LeanVM.Guest.B1.Tables
