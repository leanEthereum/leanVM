/-
  LeanVM.Guest.Bridge.JumpCellsOf

  The jump cells of the deployed guest along the reference run, from the program's alignment (`progAl`).
-/

module

public import LeanVM.Guest.Bridge.JumpCells
public import LeanVM.Guest.Bridge.ProgAl

/-!
# The jump cells along the reference run

`jumpCells_of` (`JumpCells.lean` states its parts): apart from them, since it reads the program's alignment
`progAl`, whose checks (`ProgAl/Link*`, a long function's windows in `CoreMode/AlignOk`) a reader of the parts need not import.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B2C
open LeanVM.Guest.Check (getF getF_eq)

@[expose] public section

variable {hdr : E × E} {rd rd0 : Reader} {T : Tree} {κ : ℕ} {L : MemoryImage κ} {M : ℕ → E}

/-- **The jump cells of the deployed guest**: the top frame of every state of the track against the
run holds what its jumps read, on a memory covering the honest writes. -/
theorem jumpCells_of (hT : T.name = "main") (hH : HonestAt coreProgram B2C.fs B2C.H B2C.C hdr T B2C.cert rd [] [])
    (hL : Covers coreProgram B2C.fs B2C.H B2C.C hdr T L)
    (hD : ∀ j, 1 ≤ j → j < nFns → jcData j = true)
    (hCh : ChainArm rd0 (honestInsts coreProgram B2C.fs B2C.H hdr T) T M alignA) {pc fp : ℕ} {done : List Pop}
    {e : Ent} {st : List Ent}
    (h : RefOk coreProgram rd0 (honestInsts coreProgram B2C.fs B2C.H hdr T) T M (entOf alignA) (alOf alignA) pc fp
      (done, e :: st)) : JumpCells L alignA e pc := by
  obtain ⟨hIe, j, bufs, kids, vs, hj, ht, hcore, hw, hF⟩ := h.frames hT hH hL e List.mem_cons_self
  have hE := h.track.ents e List.mem_cons_self
  obtain ⟨i0, rfl, -, -, -, -, -, -, h1, h2⟩ := fn_of_idx hj
  have hA : alignA e.I.t.name = fnAl (i0 + 1) := alignA_of hj
  have hd := hD _ h1 h2
  unfold jcData jcDataD at hd
  simp only [Bool.and_eq_true] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hstat, harms⟩, hsites⟩, huniq⟩, hextra⟩, hblock⟩, hloop⟩, -⟩, -⟩ := hd
  have hcont := Check.cont_of (End.winOk_of h1 h2)
  have hwc : walk e.σ (coreOf (i0 + 1)).body = .ret (e.pre ++ e.es) vs := by rw [hcore]; exact hw
  have hes : ∀ es' vs', walk e.σ e.fn.body = .ret es' vs' → es' = e.pre ++ e.es := fun es' vs' h' ↦ by
    rw [hw] at h'; exact (Out.ret.inj h').1.symm
  have hstatB : ∀ {o : ℕ} {w : PC}, (o, w) ∈ (plumbOf (i0 + 1)).stat →
      cellAt L e.I.fp o = some (w.word e.I.fp) ∧ (∀ a b, w = .k a b → a < 2 ^ 64 ∧ b < 2 ^ 64) := by
    intro o w hm
    have hb := List.all_eq_true.mp hstat _ hm
    simp only [cellIn, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hb
    refine ⟨hF.stat _ hm hb.1.1 hb.1.2, fun a b hw' ↦ ?_⟩
    subst hw'
    simpa only [Bool.and_eq_true, Nat.blt_eq] using hb.2
  have hroot : ∀ I ∈ honestInsts coreProgram B2C.fs B2C.H hdr T, I.t.name = "main" → I.fp = 0 := fun I hI hn ↦ by
    rcases insts_main_or T _ hdr hH.toHonest.valid I hI with ⟨h0, -⟩ | h0
    · exact h0
    · exact absurd hn h0
  have hmain : (i0 + 1 == 1) = true → e.I.fp = 0 := fun h1' ↦
    hroot _ hIe ((idx_one_iff hj).mp (by simpa using h1'))
  have hok := progAl.ok _ _ hE.find
  rw [hA] at hok
  have hlocs : (certOf (i0 + 1)).locs.all (fun c ↦ Nat.blt c (2 ^ cellBits)) = true := by
    rw [alignOk, AlignCtx.seq_eq] at hok
    simp only [Bool.and_eq_true] at hok
    exact hok.1.1.1.1
  have hfe : e.I.fp = 0 → e.I.Frame B2C.fs 0 := fun h0 ↦
    ⟨by omega, by have := two_le_fsz e.I.t; omega⟩
  have hf0 : ∀ {I : Inst}, I.t = T → I.fp = 0 → I.Frame B2C.fs 0 := fun {I} _ h0 ↦
    ⟨by omega, by have := two_le_fsz I.t; omega⟩
  refine ⟨?zero, ?nz, ?self, ?pcw, ?cond, ?arm, ?site, ?tail, ?hdr, ?main, ?bot⟩
  case zero =>
    intro o hz
    rw [hA] at hz
    unfold AlignCtx.zeroAt at hz
    split at hz
    · rename_i k0 k1 hso
      simp only [Bool.and_eq_true, Nat.beq_eq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      rw [(hstatB (statOf_ofData hso)).1]
      simp [PC.word, Mode.imm_zero]
    · cases hz
  case nz =>
    intro o hz
    rw [hA] at hz
    unfold AlignCtx.nzAt at hz
    split at hz
    · rename_i k0 k1 hso
      obtain ⟨hr, hk⟩ := hstatB (statOf_ofData hso)
      obtain ⟨ha, hb⟩ := hk k0 k1 rfl
      refine ⟨_, hr, Mode.imm_ne_zero ha hb fun ⟨h0, h1⟩ ↦ ?_⟩
      subst h0 h1
      simp at hz
    · cases hz
  case self =>
    intro o hz
    rw [hA] at hz
    unfold AlignCtx.selfAt at hz
    split at hz
    · rename_i hso
      rw [(hstatB (statOf_ofData hso)).1]
      simp [PC.word]
    · rename_i hso
      rw [(hstatB (statOf_ofData hso)).1, hmain hz]
      simp only [PC.word, imm_one, addressOfIndex, pow_zero, Exec.ofK_one]
    · cases hz
  case pcw =>
    intro o t hz
    rw [hA] at hz
    unfold AlignCtx.pcAt at hz
    split at hz
    · rename_i k0 hso
      rw [(hstatB (statOf_ofData hso)).1]
      simp only [PC.word]
      rw [Exec.imm_of_ofBits (Mode.PowTree.find_ok' (Exec.PowTree.ok_of_okW Checked.powTree_ok) hz)]
    · cases hz
  case cond =>
    intro c es' vs' hw' hc
    obtain rfl := hes es' vs' hw'
    have hcc : c ∈ condsOf (coreOf (i0 + 1)).body := walk_inK _ (by rw [hwc, evsOf_ret]; exact hc)
    have hco := blockB_conds _ _ hblock c hcc
    unfold condOk at hco
    simp only [Bool.and_eq_true, Nat.blt_eq] at hco
    obtain ⟨hidx, hxc⟩ := hco
    split at hxc
    · rename_i x hxs
      have hloc := cellW_spec hcont hxs
      simp only [cellIn, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hxc
      have hval := hF.val c (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨_, hc, by simp [Ev.uses]⟩))) (by rw [cellJ, hloc]; exact hxc.1)
        (by rw [cellJ, hloc]; exact hxc.2)
      have hxn : (extraOf (i0 + 1)).lookup c.idx = none := by
        cases hl : (extraOf (i0 + 1)).lookup c.idx with
        | none => rfl
        | some c' =>
          have hm := mem_of_lookupN hl
          have := List.all_eq_true.mp hextra _ hm
          split at this
          · rename_i y hy
            rw [cellW_spec hcont hy] at hloc
            simp only [Nat.blt_eq] at this
            omega
          · cases this
      have hla : (fnAl (i0 + 1)).X.locAt c.idx = (certOf (i0 + 1)).locs.getD c.idx 0 :=
        locAt_ofData hlocs hxn hidx
      rw [hA, hla]
      exact hval
    · cases hxc
  case arm =>
    intro off oc od of hpc hcode bs x arms ps hpos a ha hax k t hσk ht'
    rw [hA] at ha ht'
    -- the selector is numbered: the `match` is a statement of the body
    have hnum : x = V.n x.idx := by
      obtain ⟨-, off0, -, p0, hal0, as0, -, hpos0⟩ := h.linked.top
      rw [alOf, hA] at hal0
      simp only [alignAt] at hal0
      obtain ⟨c0, hl0, rfl⟩ := Option.map_eq_some_iff.mp hal0
      obtain ⟨l, hl, hlk⟩ := Option.bind_eq_some_iff.mp hl0
      have hpre : alignPre (fnAl (i0 + 1)).X (fnAl (i0 + 1)).d = true := by
        rw [alignOk, AlignCtx.seq_eq] at hok
        simp only [Bool.and_eq_true] at hok
        simp only [alignPre, Bool.and_eq_true]
        exact ⟨⟨⟨hok.1.1.1.1, hok.1.1.1.2⟩, hok.1.1.2⟩, hok.1.2⟩
      obtain ⟨-, -, -, -, -, -, hz0, -⟩ := alignRun_step hpre hl (mem_of_lookup hlk)
      have hmem : Stmt.match_ x arms ∈ c0.pos := by
        have : Stmt.match_ x arms ∈ e.pos := by rw [hpos]; simp
        rw [hpos0, List.mem_append] at this
        rcases this with h' | h'
        · simp at h'
        · exact h'
      exact numbered_eq (blockB_sels _ _ hblock _ (zok_stmts hz0 hmem) x arms rfl)
    have hσx : e.σ (V.n a.1) = ofK (addressOfIndex k) := by rw [hax, ← hnum]; exact hσk
    have hjt := End.jtHolds_of (jumpTables_cover hH.toHonest hL hT)
    have htab := jumpTables_cover hH.toHonest hL hT
    have hglob : glob.jt.get (a.2 + k) = some t := by
      change Data.jtTrie.get (a.2 + k) = some t
      rw [← getF_eq]; exact ht'
    obtain ⟨hf, hlt⟩ := tbl_slot hjt htab hglob
    have hword := tbl_armWord hσx hf hlt
    have hmem := arms_ofData ha
    have hb := List.all_eq_true.mp harms _ hmem
    simp only [cellIn, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hb
    unfold armsOf at hmem
    rcases List.mem_append.mp hmem with hm | hm
    · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm
      simp only [Prod.mk.injEq] at hqe
      obtain ⟨rfl, rfl⟩ := hqe
      rw [cellAt, hF.arm q hq hb.1 hb.2]
      exact congrArg some hword
    · obtain ⟨ch, hch, hm'⟩ := List.mem_flatMap.mp hm
      obtain ⟨t', ht'', hte⟩ := List.mem_map.mp hm'
      simp only [Prod.mk.injEq] at hte
      obtain ⟨rfl, rfl⟩ := hte
      obtain ⟨k', hk', hσ'⟩ := hCh _ _ _ _ _ h _ hj off oc t' of hpc hcode ch hch ht''
      obtain ⟨-, -, -, -, hread⟩ := hF.chain ch hch k' t' hk' hσ'
      rw [cellAt, hread hb.1 hb.2]
      exact congrArg some hword
  case site =>
    intro es' vs' hw' i c q s hc htk hs
    obtain rfl := hes es' vs' hw'
    rw [hA] at hs
    obtain ⟨hsm, hsq, hsa, hsr⟩ := siteAt_ofData hs
    have hso : siteOf (i0 + 1) c = some s := siteOf_eq huniq hsm hsa hsr
    have hi : i < (calls (e.pre ++ e.es)).length := (List.getElem?_eq_some_iff.mp hc).1
    obtain ⟨kfp, hkfp⟩ : ∃ kfp, e.I.kidFps[i]? = some kfp :=
      ⟨_, List.getElem?_eq_getElem (by rw [hF.len]; exact hi)⟩
    obtain ⟨hq', htg⟩ := hF.site i c kfp s hc hkfp hso
    obtain ⟨hk0, hk1, -, -⟩ := hF.kid i c kfp hc hkfp
    have hnl : ¬((coreOf (i0 + 1)).loop = true ∧ i + 1 = (calls (e.pre ++ e.es)).length) := by
      rintro ⟨hl, hi'⟩
      simp only [hl, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hloop
      exact loop_last hloop.2 hwc hc hi' s hsm ⟨hsa, hsr⟩
    have hkh : kidHdr (i0 + 1) e.I.fp e.I.hdr (e.pre ++ e.es) i =
        (ofK (addressOfIndex s.r), ofK (addressOfIndex e.I.fp)) := by
      unfold kidHdr
      rw [hc]
      dsimp only
      rw [ite_eq_right hnl, hso]
    have hb := List.all_eq_true.mp hsites _ hsm
    simp only [cellIn, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Bool.or_eq_true, beq_iff_eq] at hb
    refine ⟨kfp, hkfp, ?_, ?_, ?_, fun htg0 ↦ ?_⟩
    · rw [← hsq]; exact hq' hb.1.1 hb.1.2
    · rw [cellAt, hk0, hkh]
    · rw [cellAt, hk1, hkh]
    · rcases hb.2 with h0 | hb2
      · exact absurd h0 htg0
      obtain ⟨rv, hkv⟩ := hE.kids
      obtain ⟨kk, -, hkn, hkv'⟩ := kidsValid_get hkv hc
      obtain ⟨args, rets, hv⟩ := hkv' htk
      rcases kk with ⟨f', σ', bufs', kids'⟩ | ⟨f', σ'⟩
      · obtain ⟨fn', hf', -⟩ := hv
        simp only [Tree.name] at hkn
        subst hkn
        obtain ⟨j', hj'⟩ := idxOf_of_find hf'
        rw [cellAt, htg htg0 hb2.1 hb2.2, entryOf_of hj', alignA_of hj']
        rfl
      · exact hv.elim
  case tail =>
    intro off oc od q hpc hcode hnx es' vs' hw' i c hc htk hi
    obtain rfl := hes es' vs' hw'
    rw [hA] at hnx hcode
    obtain ⟨hl, hn1, kfp, hkfp, -, hread⟩ := next_read h1 h2 (hD _ h1 h2) hF hwc hc hi hcode hnx
    obtain ⟨hk0, hk1, -, -⟩ := hF.kid i c kfp hc hkfp
    have hkh : kidHdr (i0 + 1) e.I.fp e.I.hdr (e.pre ++ e.es) i = e.I.hdr := by
      unfold kidHdr
      rw [hc]
      dsimp only
      rw [ite_eq_left ⟨hl, hi⟩]
    refine ⟨fun h0 ↦ ?_, kfp, hkfp, ?_, ?_, ?_⟩
    · obtain ⟨I0, hI0, hI0t, hI0fp, -⟩ := root_inst (P := coreProgram) (fs := B2C.fs) (H := B2C.H) (hdr := hdr) (T := T)
      have := insts_same hIe hI0 (hfe h0) (hf0 hI0t hI0fp)
      have hn : e.I.t.name = "main" := by rw [this, hI0t, hT]
      have := (idx_one_iff hj).mpr hn
      simp [this] at hn1
    · rw [cellAt, hread]
    · rw [cellAt, cellAt, hk0, hkh, hF.hdr0]
    · rw [cellAt, cellAt, hk1, hkh, hF.hdr1]
  case hdr =>
    refine ⟨?_, ?_⟩
    · rw [cellAt, hF.hdr0]; rfl
    · rw [cellAt, hF.hdr1]; rfl
  case main =>
    intro hm
    rw [hA] at hm
    exact hmain hm
  case bot =>
    intro h0
    obtain ⟨I0, hI0, hI0t, hI0fp, -⟩ := root_inst (P := coreProgram) (fs := B2C.fs) (H := B2C.H) (hdr := hdr) (T := T)
    have := insts_same hIe hI0 (hfe h0) (hf0 hI0t hI0fp)
    have hn : e.I.t.name = "main" := by rw [this, hI0t, hT]
    have h01 : i0 + 1 = 1 := (idx_one_iff hj).mpr hn
    rw [hA]
    show (i0 + 1 == 1) = true
    rw [h01]; rfl

end

end LeanVM.Guest.Bridge
