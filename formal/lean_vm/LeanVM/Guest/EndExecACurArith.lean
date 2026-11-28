/-
  LeanVM.Guest.EndExecACurArith

  The cursor follows each step of the tree track, aligned: `CurArith` from the guest's facts
  `CurHyps`.
-/

module

public import LeanVM.Guest.EndExecACur

/-!
# `CurArith`, aligned

`curArith_of : ProgAl … → JumpCellsAt L D A → AlLayout A → CurHyps L D A → CurArith L D A`, by
`StepOff`'s kinds (`EndExecACur.lean`'s overview): the cursor past the offset's hints
(`cursor_stepA`) is the next state's cursor.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Guest.Check (getF)
open LeanVM.Prover.Exec

public section

variable {L : Lay} {D : Ref → RefD} {A : String → FnAl}

theorem getLast_of_len {kids : List Tree} {nc : ℕ} {k : Tree} (hk : kids[nc]? = some k) (hl : kids.length = nc + 1)
    (hne : kids ≠ []) : kids.getLast hne = k := by
  rw [List.getLast_eq_getElem]
  rw [List.getElem?_eq_some_iff] at hk
  obtain ⟨_, hk⟩ := hk
  simp only [hl, Nat.add_sub_cancel]; exact hk

theorem bif_one {p : Bool} {c : ℕ} (h : (bif p then 1 else 0) + c = 1) : (p || decide (0 < c)) = true := by
  cases p <;> simp at h ⊢
  omega

theorem curForm_succ {e e' : Ent} (hI : e'.I = e.I) (hnc : e'.nc = e.nc + 1) (nb : ℕ) :
    curForm L e' nb false = e.I.curA L.fs coreProgram.loop L.al nb (e.nc + 1) := by
  unfold curForm; rw [hI, hnc]; rfl

/-- **The cursor follows each step of the tree track**, aligned, from the guest's facts. -/
theorem curArith_of (hP : ProgAl guestProgram coreProgram A) (hJ : JumpCellsAt L D A) (hL : AlLayout A)
    (hC : CurHyps L D A) : CurArith L D A := by
  intro r hR hr pc fp done e st r' htr hch hncT hstep hne'
  have hE := htr.track.ents e List.mem_cons_self
  obtain ⟨f0, bufs0, kids0, hIt⟩ := hE.node
  have hnode : ∃ f σ bufs kids, e.I.t = .node f σ bufs kids := ⟨_, _, _, _, hIt⟩
  have hF := hC.facts _ _ hE.find
  have hU := hintsUp_of hP hE.find
  have hbl := hC.bufsLe r hR hr e.I hE.mem
  obtain ⟨vs, hw, -⟩ := hE.path
  have hkl : (calls (e.pre ++ e.es)).length = e.I.t.kids.length := by
    obtain ⟨rv, hkv⟩ := hE.kids; exact kidsValid_len' hkv
  obtain ⟨off, hpc, pc', fp', ⟨done', st'⟩, hr', hts', hk⟩ :=
    stepRule_off hP honestA_closed htr (hJ r hR hr _ _ _ _ _ htr) hstep (.inl hne')
  have hoff : pc - entOf A e.I.t.name = off := by omega
  have hncT' : NcTop A e off := hoff ▸ hncT
  rw [hoff, cursor_stepA hU hF hncT', any_eq_decide]
  have hfrAt : (hintsAtOff (A e.I.t.name) off).countP (isFrame (A e.I.t.name).X) =
      (frames (A e.I.t.name).X (A e.I.t.name).d).countP (fun q ↦ decide (q.1 = off)) :=
    (countP_at hU (fun _ ↦ isFrame_ptr (X := (A e.I.t.name).X)) off).symm
  have hpd : ∀ o, pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d o =
      pendIn (A e.I.t.name).code (frames (A e.I.t.name).X (A e.I.t.name).d) o := fun _ ↦ rfl
  have hnbS : nbAt (A e.I.t.name).X (A e.I.t.name).d (off + 1) = nbAt (A e.I.t.name).X (A e.I.t.name).d off +
      (hintsAtOff (A e.I.t.name) off).countP (isBuf (A e.I.t.name).X) := nb_succ hU off
  -- all the buffer hints at or before a jump that is no forward jump in the frame
  have hnone : ∀ oc od of, (A e.I.t.name).code[off]? = some (.jump oc od of) →
      bufJumpOk (A e.I.t.name).X (bufsOf (A e.I.t.name).X (A e.I.t.name).d) off oc od of = false →
      nbAt (A e.I.t.name).X (A e.I.t.name).d off +
          (hintsAtOff (A e.I.t.name) off).countP (isBuf (A e.I.t.name).X) =
        (bufsOf (A e.I.t.name).X (A e.I.t.name).d).length ∧
      ∀ t, off < t → nbAt (A e.I.t.name).X (A e.I.t.name).d t =
        (bufsOf (A e.I.t.name).X (A e.I.t.name).d).length := fun oc od of hi hb ↦ by
    rcases hF.bufs off oc od of hi with h | h
    · exact nb_none hU h
    · rw [h] at hb; cases hb
  have hkC := kidsC_length' e.I.t
  have hwf : walk e.σ e.fn.body = .ret (e.pre ++ e.es) vs := hw
  cases hk with
  | @fall e' ins hI' hnc' hins hjk =>
    refine ⟨_, _, done', _, st, hr', hts', ?_, chainA_top hI' (tailA_congr hI' hnc' (chainA_tail hch)) hch,
      ncTop_same hI' hnc' hncT' (by rw [hI']; omega)⟩
    have hpe : pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d (off + 1) =
        (pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d off ||
          decide (0 < (hintsAtOff (A e.I.t.name) off).countP (isFrame (A e.I.t.name).X))) := by
      rw [hpd, hpd, hfrAt]
      cases ins with
      | jump oc od of =>
        have hn := noFrame_of hF hins (by rcases hjk oc od of rfl with h | h <;> simp [h])
        obtain ⟨h1, h2, h3⟩ := pend_nf hins rfl hn
        rw [h2, h1, h3]
        rfl
      | _ => exact bif_add (pend_succ (frJump_of hF) hF.uniq hins rfl)
    rw [cursorAt_congr hI' hnc', hI', show entOf A e.I.t.name + off + 1 - entOf A e.I.t.name = off + 1 by omega,
      cursorAt_eq, hnbS, hpe]
  | @fwd e' oc od of _ hI' hnc' hins hz0 hself htgt hlt =>
    refine ⟨_, _, done', _, st, hr', hts', ?_, chainA_top hI' (tailA_congr hI' hnc' (chainA_tail hch)) hch,
      ncTop_same hI' hnc' hncT' (by rw [hI']; omega)⟩
    rw [cursorAt_congr hI' hnc', hI', cursorAt_eq]
    have hlt' : off < pc' - entOf A e.I.t.name := by omega
    obtain ⟨h1, h2, -⟩ := pend_nf hins rfl (noFrame_of hF hins (Or.inr (Or.inl hself)))
    have hnb : nbAt (A e.I.t.name).X (A e.I.t.name).d (pc' - entOf A e.I.t.name) =
        nbAt (A e.I.t.name).X (A e.I.t.name).d off +
          (hintsAtOff (A e.I.t.name) off).countP (isBuf (A e.I.t.name).X) := by
      rcases hF.bufs off oc od of hins with h | h
      · obtain ⟨ha, hb⟩ := nb_none hU h
        rw [hb _ hlt']; exact ha.symm
      · unfold bufJumpOk at h
        simp only [hz0, Bool.false_and, Bool.false_or, Bool.and_eq_true] at h
        obtain ⟨⟨⟨⟨-, -⟩, -⟩, harm⟩, hpc'⟩ := h
        rcases htgt with ht | ⟨z, x, arms, ss, a, k, hz, hzc, ha, hax, hk, hjt⟩
        · rw [ht] at hpc'
          simp only [List.all_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
            not_lt] at hpc'
          refine nb_skip hU hlt' fun q hq ⟨hq1, hq2⟩ ↦ ?_
          rcases hpc' q hq with h | h
          · omega
          · exact absurd hq2 (by show ¬ q.1 < pc' - (A e.I.t.name).X.entry; omega)
        · rw [ha] at harm; cases harm
    have hpt : pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d (pc' - entOf A e.I.t.name) = false := by
      rcases htgt with ht | ⟨z, x, arms, ss, a, k, hz, hzc, ha, hax, hk, hjt⟩
      · exact hF.tgt off oc od of hins pc' ht
      · have hmem : Stmt.match_ x arms ∈ stmtsOf (A e.I.t.name).body :=
          zok_stmts hz (by rw [Zip.pos, hzc]; simp)
        exact hF.arm _ hmem x arms rfl od a k pc' ha hax hk hjt
    rw [hnb, hpt, hpd, h1, hfrAt, h2]
    rfl
  | @skip e' oc od of c f σ' hI' hnc' hins hc hph hcase =>
    have hlt0 : e.nc < e.I.t.kids.length := (List.getElem?_eq_some_iff.mp hph).1
    have hle := bufs_le_of_call (hF.bufs off oc od of hins) (by
      rcases hcase with ⟨hnx, -⟩ | ⟨s, hs⟩
      · exact Or.inl hnx
      · exact Or.inr (siteAt_some hs))
    refine ⟨_, _, done', _, st, hr', hts', ?_, chainA_top hI' ?_ hch, ncTop_past fun q hq ↦ ?_⟩
    · rw [cursorAt_eq, hI', show entOf A e.I.t.name + off + 1 - entOf A e.I.t.name = off + 1 by omega, hnbS]
      rcases hcase with ⟨hnx, hlen⟩ | ⟨s, hs⟩
      · obtain ⟨h1, h2, h3⟩ := pend_nf hins rfl (noFrame_of hF hins (Or.inr (Or.inr (Or.inl hnx))))
        have hl := hC.loopNext _ _ hE.find off oc od of hins hnx
        rw [hl] at hkC
        simp only [↓reduceIte] at hkC
        have h3' : pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d (off + 1) = false := h3
        have h1' : pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d off = false := h1
        rw [h3', h1', hfrAt, h2, curForm_succ hI' hnc']
        show e.I.curA L.fs coreProgram.loop L.al _ (e.nc + 1) = e.I.curA L.fs coreProgram.loop L.al _ e.nc
        rw [curA_take_le (by omega), curA_take_le (I := e.I) (nc := e.nc) (by omega)]
      · obtain ⟨rr, hrr, -, hrj⟩ := hF.site off oc od of hins (siteAt_some hs)
        obtain ⟨hsum, h3⟩ := pend_site hF.uniq hins rfl ⟨rr, hrr, hrj⟩
        have hnc : e.nc < (e.I.t.kidsC coreProgram.loop).length := by
          rw [hkC]
          split
          · have := hkl ▸ hC.notLast _ _ hE.find (by assumption) _ _ _ hwf _ _ hc _ _ hs; omega
          · exact hlt0
        have hkc : (e.I.t.kidsC coreProgram.loop)[e.nc]? = some (.phantom f σ') := by
          rw [kidsC_getElem?_of hnc]; exact hph
        have h3' : pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d (off + 1) = false := h3
        have hP1 : (pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d off ||
            decide (0 < (hintsAtOff (A e.I.t.name) off).countP (isFrame (A e.I.t.name).X))) = true := by
          rw [hfrAt]; exact bif_one hsum
        rw [h3', hP1, curForm_succ hI' hnc', curForm_true hkc, curA_succ hkc, kidEnd, endA_phantom]
    · unfold TailA
      rw [hI', hnc']
      intro hl hle' hne
      rcases hcase with ⟨-, hlen⟩ | ⟨s, hs⟩
      · exact ⟨f, σ', getLast_of_len hph (by omega) hne⟩
      · have := hkl ▸ hC.notLast _ _ hE.find hl _ _ _ hwf _ _ hc _ _ hs
        omega
    · rw [hI'] at hq ⊢
      have := hle q hq
      omega
  | @push e' J fn oc od of c s hI' hnc' hins hc hsite hsr hat hJ hk hkf hfind hhdr =>
    obtain ⟨rr, hrr, -, hrj⟩ := hF.site off oc od of hins (siteAt_some hsite)
    obtain ⟨hsum, -⟩ := pend_site hF.uniq hins rfl ⟨rr, hrr, hrj⟩
    have hz0 : (A e.I.t.name).X.zeroAt oc = false := by
      obtain ⟨oc', od', q', hc', -, h1, -⟩ := frameOk_spec (hF.frame rr hrr)
      rw [hrj, hins] at hc'
      cases hc'
      exact h1
    obtain ⟨hnbo, hnbt⟩ := hnone oc od of hins (by
      unfold bufJumpOk
      obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp (siteAt_some hsite)
      simp [hz0, hs'])
    have hlt0 : e.nc < e.I.t.kids.length := (List.getElem?_eq_some_iff.mp hk).1
    have hnl : coreProgram.loop e.I.t.name = true → e.nc + 1 < e.I.t.kids.length := fun hl ↦
      hkl ▸ hC.notLast _ _ hE.find hl _ _ _ hwf _ _ hc _ _ hsite
    have hnc : e.nc < (e.I.t.kidsC coreProgram.loop).length := by
      rw [hkC]
      split
      · have := hnl (by assumption); omega
      · exact hlt0
    have hkc : (e.I.t.kidsC coreProgram.loop)[e.nc]? = some J.t := by
      rw [kidsC_getElem?_of hnc]; exact hk
    have hpos := kid_placeA hR hE.mem hJ hk hkf
    rw [kid_posA hkc] at hpos
    obtain ⟨hJfp, hJcur⟩ := Prod.mk.inj (Option.some.inj hpos)
    have hE' : EntOk coreProgram (instsOf L (D r) r) e' :=
      hts'.track.ents e' (List.mem_cons_of_mem _ List.mem_cons_self)
    have hsr63 : s.r < 2 ^ 63 := by
      have := (entry_of_atPc hP hL hE' hat).1
      rw [guest_logSize] at this
      omega
    have hle := bufs_le_of_call (hF.bufs off oc od of hins) (Or.inr (siteAt_some hsite))
    have hP1 : (pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d off ||
        decide (0 < (hintsAtOff (A e.I.t.name) off).countP (isFrame (A e.I.t.name).X))) = true := by
      rw [hfrAt]; exact bif_one hsum
    have hbl' : e.I.t.bufs.length ≤ nbAt (A e.I.t.name).X (A e.I.t.name).d off +
        (hintsAtOff (A e.I.t.name) off).countP (isBuf (A e.I.t.name).X) := by rw [hnbo]; exact hbl
    refine ⟨_, _, done', _, e' :: st, hr', hts', ?_, ⟨tailA_enter J fn, ⟨s.r, hhdr, hsr63, ?_,
      ncTop_past fun q hq ↦ ?_⟩, chainA_top hI' ?_ hch⟩, ncTop_enter J fn _⟩
    · change cursorAt L A (Ent.enter coreProgram J fn) (entOf A J.t.name - entOf A J.t.name) = _
      rw [Nat.sub_self, cursorAt_enter, hP1, curForm_true hkc, curA_bufs_le hbl', hJcur]
    · change J.endCurA L.fs coreProgram.loop L.al = cursorAt L A e' (s.r - entOf A e'.I.t.name)
      have hret : pendIn (A e.I.t.name).code (frames (A e.I.t.name).X (A e.I.t.name).d)
          (s.r - entOf A e.I.t.name) = false := hF.ret _ _ _ s hsite
      have hret' : pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d (s.r - entOf A e.I.t.name) = false :=
        hret
      rw [cursorAt_eq, hI', hnbt _ (by omega), hret', curForm_succ hI' hnc', curA_bufs_le hbl,
        endCurA_kid hkc hJcur.symm]
    · rw [hI'] at hq ⊢
      have := hle q hq
      omega
    · unfold TailA
      rw [hI', hnc']
      intro hl hle'
      have := hnl hl
      omega
  | @tail J fn oc od of hins hz0 hnx hlen hJ hk hkf hfind hhdr =>
    obtain ⟨h1, h2, -⟩ := pend_nf hins rfl (noFrame_of hF hins (Or.inr (Or.inr (Or.inl hnx))))
    obtain ⟨hnbo, -⟩ := hnone oc od of hins (by unfold bufJumpOk; simp [hz0, nextAt_selfAt hnx])
    have hl := hC.loopNext _ _ hE.find off oc od of hins hnx
    have hkl' : e.I.t.kids.length = e.nc + 1 := hkl ▸ hlen
    rw [hl] at hkC
    simp only [↓reduceIte] at hkC
    have hne : e.I.t.kids ≠ [] := fun h ↦ by rw [h] at hkl'; simp at hkl'
    have hpos := kid_placeA hR hE.mem hJ hk hkf
    rw [show e.nc = e.I.t.kids.length - 1 by omega, tail_posA hl hne] at hpos
    obtain ⟨-, hJcur⟩ := Prod.mk.inj (Option.some.inj hpos)
    have hJt : J.t = e.I.t.kids.getLast hne := (getLast_of_len hk hkl' hne).symm
    have hbl' : e.I.t.bufs.length ≤ nbAt (A e.I.t.name).X (A e.I.t.name).d off +
        (hintsAtOff (A e.I.t.name) off).countP (isBuf (A e.I.t.name).X) := by rw [hnbo]; exact hbl
    have hend : J.endCurA L.fs coreProgram.loop L.al = e.I.endCurA L.fs coreProgram.loop L.al :=
      endCurA_tail hl hne hJt hJcur.symm hnode
    refine ⟨_, _, done', _, st, hr', hts', ?_, ?_, ncTop_enter J fn _⟩
    · change cursorAt L A (Ent.enter coreProgram J fn) (entOf A J.t.name - entOf A J.t.name) = _
      rw [Nat.sub_self, cursorAt_enter, hpd, h1, hfrAt, h2]
      show J.cur = e.I.curA L.fs coreProgram.loop L.al _ e.nc
      rw [curA_bufs_le hbl', ← hJcur, show (e.I.t.kidsC coreProgram.loop).length = e.nc by omega]
    · rcases st with _ | ⟨e2, st2⟩
      · exact tailA_enter J fn
      · obtain ⟨-, ⟨r0, hr0, hlt, he, hn2⟩, hrest⟩ := hch
        exact ⟨tailA_enter J fn, ⟨r0, by rw [← hr0]; exact hhdr, hlt, by
          change J.endCurA L.fs coreProgram.loop L.al = _; rw [hend]; exact he, hn2⟩, hrest⟩
  | @ret e2 st2 oc _ hins hz0 hmain hst hlen hhdr =>
    subst hst
    obtain ⟨h1, h2, -⟩ := pend_nf hins rfl (noFrame_of hF hins (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
    obtain ⟨hnbo, -⟩ := hnone oc 0 1 hins (by unfold bufJumpOk; simp [hz0])
    obtain ⟨htl, ⟨r1, hr1, hr1lt, hend, hn2⟩, hrest⟩ := hch
    have hE2 : EntOk coreProgram (instsOf L (D r) r) e2 := hts'.track.ents e2 List.mem_cons_self
    have hr0lt : pc' < 2 ^ 63 := by
      have := (entry_of_atPc hP hL hE2 hts'.linked.top.2).1
      rw [guest_logSize] at this
      omega
    have hr10 : r1 = pc' := by
      have h := ofK_injective (hr1.symm.trans hhdr)
      exact gpow_inj (by omega) (by omega) h
    subst hr10
    have hbl' : e.I.t.bufs.length ≤ nbAt (A e.I.t.name).X (A e.I.t.name).d off +
        (hintsAtOff (A e.I.t.name) off).countP (isBuf (A e.I.t.name).X) := by rw [hnbo]; exact hbl
    refine ⟨_, _, done', e2, st2, hr', hts', ?_, hrest, hn2⟩
    rw [← hend, endCurA_ret hnode (fun hl hk ↦ htl hl (by omega) hk), hpd, h1, hfrAt, h2]
    show _ = e.I.curA L.fs coreProgram.loop L.al _ e.nc
    rw [curA_bufs_le hbl']
    exact (curA_take_le (by rw [hkC]; split <;> omega)).symm

/-- **The allocation track's obligations**, `CurArith` from the guest's facts `CurHyps`. -/
theorem allocTrack_ofCur {R : Ref → Prop} {Km : Mode.Cert} {E0 : Mode.Env} (hH : HintHyps L D A)
    (hRH : ∀ r, R r → RefH L (D r) r) (hMain : MainOk Km E0) (hM : MainA L) (hS : SizesAt L D A)
    (hC : CurHyps L D A) (hR : AllocReady L D A) : AllocTrack R (YAlloc L D A) :=
  allocTrack_of hH hRH hMain hM hS (curArith_of hH.progAl hH.jumpCells hH.layout hC) hR

end

end LeanVM.Guest.EndExec
