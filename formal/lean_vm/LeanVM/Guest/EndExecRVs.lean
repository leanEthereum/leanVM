/-
  LeanVM.Guest.EndExecRVs

  `verify_sub`'s exponent facts (`Res.vsFacts`) at its honest frames, and its residuals in their
  families (`Res.vsB`).
-/

module

public import LeanVM.Guest.EndExecREf
public import LeanVM.Guest.EndExecRSt
public import LeanVM.Guest.EndExecRVkSt
public import LeanVM.Guest.EndExecRStB
public import LeanVM.Guest.B1.VerifySub.Lanes
public import LeanVM.Guest.B1.KeccakGkr.VkHolds
public import LeanVM.Guest.B1.Bits.Grind

/-!
# `verify_sub`'s exponent facts

`top_ret`: at an honest frame, a call on the path, its callee's frame pointer in the site's cell
`q`: the word at `[q]·g^(2 + |args| + k)` is the caller's value of the call's `k`-th return.
`vs_factsOk`: at an honest frame of `verify_sub`, its front (`B1.VerifySub.vs_front`) gives the
tables' log-heights in `dims` (`hdims`, each below `31`, the keccak table's between `9` and `24`), the
stack's log (`h276`, `h278`), the bus depth (`h253`), the table sumcheck's depth `|chis|` (`TCtx`),
at least the keccak table's (its first output lane's claim, as `verify_sub_sound_of`), and the cursors
past the bus's GKR walk, the tables' segment and `verify_keccak`'s run (`verify_keccak_holds`), their
reads bounded (`runsTo_reads`), the sum below the stream's `8192` words with room for `207` more.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1
open LeanVM.Guest.B2C (idxOf fsN cellJ)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (EFacts vsFacts vsB topAtoms)
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec

public section

/-! ## The body's facts -/

theorem vs_idx : idxOf name% «verify_sub» = some (fn_idx% «verify_sub») := by decide +kernel

/-- The calls whose returns the facts read, before `verify_keccak`'s return. -/
def vsRetCalls : List (String × List V × List V) :=
  [("log2_ceil_in_the_exponent__L0_L34", [.n 252, .n 4], [.n 253]),
   ("log2_ceil_in_the_exponent__L16_L34", [.n 274, .n 4], [.n 276]),
   ("verify_bus_gkr", [554, 555, 556, 557, 558, 320, 253, 254, 561, 25].map .n, (List.range 7).map fun k ↦ .n (562 + k)),
   ("verify_tables", vtArgsV, vtRetsV),
   ("verify_keccak", vkArgsV, (List.range 7).map fun k ↦ .n (590 + k))]

/-- The calls' sites. -/
def vsRetSites : List ℕ := [185, 221, 577, 591, 604]

/-- `verify_sub`'s statements up to `verify_keccak`'s call. -/
noncomputable def vsPre : List Stmt := (fn% «verify_sub»).body.take 342

theorem vsPre_noRet : Memory.Stmt.noRetListS vsPre = true := by decide +kernel

theorem vsRetCalls_any : vsRetCalls.all (fun c ↦ vsPre.any (stmtEqb · (Stmt.call c.1 c.2.1 c.2.2))) = true := by
  decide +kernel

theorem vsRetCalls_mem {s : ℕ} (hs : s < 5) :
    Stmt.call (vsRetCalls.getD s ("", [], [])).1 (vsRetCalls.getD s ("", [], [])).2.1
      (vsRetCalls.getD s ("", [], [])).2.2 ∈ vsPre := by
  have hm : vsRetCalls.getD s ("", [], []) ∈ vsRetCalls := by
    rw [List.getD_eq_getElem _ _ (by simp [vsRetCalls]; omega)]
    exact List.getElem_mem _
  have h := List.all_eq_true.mp vsRetCalls_any _ hm
  obtain ⟨x, hx, he⟩ := List.any_eq_true.mp h
  rw [← stmtEqb_sound he]
  exact hx

theorem vsRetSites_eq : (List.range 5).all (fun s ↦ ((B2C.siteOf (fn_idx% «verify_sub»)
    ⟨(vsRetCalls.getD s ("", [], [])).1, (vsRetCalls.getD s ("", [], [])).2.1,
      (vsRetCalls.getD s ("", [], [])).2.2, true⟩).map (·.q)) == some (vsRetSites.getD s 0) &&
      decide (2 ≤ vsRetSites.getD s 0) && decide (vsRetSites.getD s 0 < fsN (fn_idx% «verify_sub»))) = true := by
  decide +kernel

/-- The cells of the stream, the stack's log less `20` and the dims table, each named by an atom. -/
theorem vs_cells : cellJ (fn_idx% «verify_sub») (.n 25) = 27 ∧ cellJ (fn_idx% «verify_sub») (.n 278) = 224 ∧
    cellJ (fn_idx% «verify_sub») (.n 71) = 92 ∧ 224 < fsN (fn_idx% «verify_sub») := by
  decide +kernel

theorem vs_atoms : (topAtoms (fn% «verify_sub»).body).contains (.load (.n 27) (.n 25) 0) = true ∧
    (topAtoms (fn% «verify_sub»).body).contains (.load (.n 72) (.n 71) 0) = true ∧
    (topAtoms (fn% «verify_sub»).body).contains (.mul (.n 278) (.n 276) (.n 277)) = true := by
  decide +kernel

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

/-- **A callee's return through its site's cell**: the word at `[q]·g^(2 + |args| + k)` is the
caller's value of the call's `k`-th return. -/
theorem top_ret (t : TopAt A r K i e j) (hr : r.Ok) {f : String} {as bs : List V}
    (hev : Ev.call f as bs ∈ e.pre ++ e.es) {q : ℕ}
    (hq : (B2C.siteOf j ⟨f, as, bs, true⟩).map (·.q) = some q) (h2 : 2 ≤ q) (hqf : q < fsN j)
    {k : ℕ} (hk : k < bs.length) {v : E}
    (hv : RBase (refMem r.img) e.I.fp (.hp q (2 + as.length + k)) v) : v = e.σ (bs.getD k (.n 0)) := by
  obtain ⟨fn, bufs, kids, hJ, hfj, -⟩ := t.found
  obtain ⟨vs, hw, hF, -⟩ := t.events hr
  set c : Call := ⟨f, as, bs, true⟩ with hcdef
  have hcm : c ∈ calls (e.pre ++ e.es) := List.mem_filterMap.mpr ⟨_, hev, rfl⟩
  obtain ⟨ii, hii⟩ := List.mem_iff_getElem?.mp hcm
  obtain ⟨kfp, hkfp⟩ : ∃ kfp, e.I.kidFps[ii]? = some kfp := by
    have hl := hF.len
    have : ii < (calls (e.pre ++ e.es)).length := (List.getElem?_eq_some_iff.mp hii).1
    exact ⟨e.I.kidFps[ii], List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨st, hst, hstq⟩ := Option.map_eq_some_iff.mp hq
  have hrdq := (hF.site ii c kfp st hii hkfp hst).1 (by rw [hstq]; exact h2) (by rw [hstq]; exact hqf)
  rw [hstq] at hrdq
  obtain ⟨-, hmq⟩ := ref_read hr (by have := t.fb; omega) hrdq
  have hret := kid_rets hr t.inst hJ hfj hw hii hkfp rfl k hk
  obtain ⟨x, hxn, hxM⟩ := hv
  have hxa : Parameters.addressOfIndex (kfp + (2 + as.length + k)) = Parameters.addressOfIndex x := by
    have hy := hxn.1
    simp only [hmq, Mode.limb_mul_ofK, limb_ofK, Fin.isValue, Fin.val_zero, ↓reduceIte, addressOfIndex] at hy
    rw [← pow_add] at hy
    simpa [addressOfIndex] using hy
  rw [hxa] at hret
  obtain ⟨-, hmx⟩ := ref_read hr (by have := hxn.2; unfold maxCells at this; omega) hret
  rw [← hxM, hmx]

/-- **`verify_sub`'s values at an honest frame**: the tables' log-heights `hs` in `dims`, the stack's
log `sl`, the bus depth `d`, the table sumcheck's depth `n`, the cursors past the bus's GKR walk, the
tables' segment and `verify_keccak`, `gK + 207` words at most into the stream. -/
theorem vs_vals (t : TopAt A r K i e j) (hr : r.Ok) (hname : (coreOf j).name = name% «verify_sub») :
    j = fn_idx% «verify_sub» ∧ ∃ (hs : List ℕ) (lm sl d n gG gT gK : ℕ),
      hs.length = 6 ∧ (∀ h ∈ hs, h < 31) ∧ 9 ≤ hs.getD 5 0 ∧ hs.getD 5 0 ≤ 24 ∧
      ReadsAt r.img.read (e.σ (.n 71)) (gen ^ lm :: hs.map (gen ^ ·)) ∧
      20 ≤ sl ∧ sl ≤ 30 ∧ e.σ (.n 278) = gen ^ (sl - 20) ∧ e.σ (.n 276) = gen ^ sl ∧
      20 ≤ d ∧ d < 34 ∧ e.σ (.n 253) = gen ^ d ∧
      hs.getD 5 0 ≤ n ∧ n ≤ d ∧ e.σ (.n 579) = gen ^ n ∧
      e.σ (.n 567) = e.σ (.n 25) * gen ^ gG ∧ e.σ (.n 578) = e.σ (.n 25) * gen ^ gT ∧
      e.σ (.n 595) = e.σ (.n 25) * gen ^ gK ∧ gG ≤ gT ∧ gT ≤ gK ∧ gK + 207 ≤ 8192 := by
  obtain ⟨f, bufs, kids, hJ, hfj, hfn⟩ := t.found
  rw [hname] at hfn
  subst hfn
  have hj : j = fn_idx% «verify_sub» := by
    have := t.idx
    rw [hJ] at this
    exact Option.some.inj (this.symm.trans vs_idx)
  refine ⟨hj, ?_⟩
  have hcj : coreOf j = fn% «verify_sub» := Option.some.inj (hfj.symm.trans VerifySub.find_vs)
  rw [hcj] at hfj
  obtain ⟨args, rets, hv⟩ := inst_valid' hr t.inst hJ
  obtain ⟨-, hb⟩ := Res.holds_of_valid hfs_guest hv hfj
  rw [VerifySub.vs_body] at hb
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨hexp, hwin⟩ := carryQ_all hr e.I t.inst _ e.σ bufs kids hJ _ hfj (name% «verify_sub», 4, .tab)
    (by decide) rfl (.n 4) (by rw [VerifySub.vs_params]; rfl)
  obtain ⟨⟨F⟩, -⟩ := VerifySub.vs_front (by omega) r.img (fun _ _ _ h ↦ Res.KidRel.rel h)
    (bytecode := List.replicate (2 ^ 23) 0) List.length_replicate hexp hwin hb
  have hκw := VerifySub.winTab_kappa (by omega) r.img hwin
  -- the words read before each cursor
  obtain ⟨sp, hsp⟩ := front_carried F
  obtain ⟨hlG, sp', hsp'⟩ := runsTo_reads (reads_gkrPhase _) F.hG hsp
  have hhl : ∀ h ∈ (Tables.layoutOf (List.replicate (2 ^ 23) 0) F.logMem F.rowsN).tableLogHeights,
      h ≤ 30 := by
    rw [VerifySub.layoutOf_heights]
    intro h hh'
    have := F.hh31 h hh'
    omega
  have hRT := reads_tablesSeg (claimedBytecodeValue ⟨F.bus.bytecodePoint, e.σ (.n 580)⟩)
    (fun w p v ↦ Child.reads_claimedBytecodeValue ⟨F.bus.bytecodePoint, e.σ (.n 580)⟩ w p v) _ hhl F.pi F.weights
    (e.σ (.n 559)) F.r.2.1 F.r.2.2
  obtain ⟨hlT, sp'', hsp''⟩ := runsTo_reads hRT F.hT hsp'
  generalize (List.replicate (2 ^ 23) 0 : List LeanVM.Parameters.K) = bc at F hhl
  -- the tables' context
  obtain ⟨chis, hbpR, hgmu, hchi, hgzc, hchiL, -, hcol, hpts⟩ := F.hctx
  have hpts' : ∀ j (p : List E), (F.claims.map (·.point))[j]? = some p →
      (j < Tables.nPooled → p.length = Tables.claimLowDim F.logMem (Tables.tableHeightsOf F.rowsN) j) ∧
      (Tables.nBusClaims ≤ j → j < Tables.nPooled → p = chis.take p.length) :=
    fun j p hp ↦ ⟨(hpts j p hp).1, (hpts j p hp).2.2.1⟩
  obtain ⟨-, -, -, hl25, hlR⟩ := VerifySub.lanes_facts F.hcl hcol hpts' F.hcew
  have hτc : ((Tables.tableHeightsOf F.rowsN).getD 5 0) ≤ chis.length := by
    have h105 : 105 < (F.claims.map (·.point)).length := by simp [F.hcl]
    obtain ⟨hl, -, ht, -⟩ := hpts 105 _ (List.getElem?_eq_getElem h105)
    have hsrc : Tables.claimKappaSrc.getD 105 0 = 7 := by decide +kernel
    have hcd : Tables.claimLowDim (Tables.layoutOf (bc) F.logMem F.rowsN).logMemory
        (Tables.layoutOf (bc) F.logMem F.rowsN).tableLogHeights 105 =
          ((Tables.tableHeightsOf F.rowsN).getD 5 0) := by
      rw [VerifySub.layoutOf_heights]
      unfold Tables.claimLowDim
      rw [hsrc]
      simp [Tables.claimKappaAdj]
    have e1 := hl (by decide)
    have e2 := congrArg List.length (ht (by decide) (by decide))
    rw [hcd] at e1
    rw [List.length_take] at e2
    omega
  have hτ9 := VerifySub.tau_ge F.hrowsL
  have hτ24 := VerifySub.tau_le_of_kappasBelow (VerifySub.tableHeights_length _ F.hrowsL) F.hKB
  -- `verify_keccak`
  have hK := VerifySub.verify_keccak_holds (by omega) hκw r.img (grind_check_holds 3 (by decide)) _ _
    (Res.KidRel.rel F.hkc)
  obtain ⟨xsK, op, point, slices, word, s', -, hrunK, -, -, -, -, -, -, -, hretK⟩ :=
    hK (by rw [F.h589]; exact VerifySub.winTabs_of hwin) ((Tables.tableHeightsOf F.rowsN).getD 5 0) chis _ hτ9
      (by omega) F.h583 hτc hchi hl25 (by rw [F.h587]; exact hlR)
  obtain ⟨-, hK2⟩ := List.append_inj' (show [e.σ (.n 590), e.σ (.n 591), e.σ (.n 592), e.σ (.n 593),
    e.σ (.n 594)] ++ [e.σ (.n 595), e.σ (.n 596)] = _ from hretK) rfl
  simp only [List.cons.injEq, and_true] at hK2
  obtain ⟨e595, -⟩ := hK2
  obtain ⟨hlK, -⟩ := runsTo_reads (Child.reads_verifyKeccak _ _ _ (by simp only [List.length_take]; omega)) hrunK hsp''
  -- the bus depth
  have hbusL : F.bus.point.length = VerifySub.busDepth (Tables.layoutOf (bc) F.logMem F.rowsN) := by
    have := hgmu.symm.trans F.h253
    exact Value.gen_pow_inj (by have := VerifySub.mem_size_le (by omega) r.img hbpR; omega) (by have := F.hdep34; omega) this
  have hgk := Child.gkrReads_le (VerifySub.busDepth (Tables.layoutOf (bc) F.logMem F.rowsN))
    (by have := F.hdep34; omega)
  have hroom : 13 + (2 + Child.gkrReadsBound) + (busRestReads + Child.tableReads) + Child.keccakReads 27 + 207
      ≤ 8192 := by decide
  refine ⟨Tables.tableHeightsOf F.rowsN, F.logMem, _, _, chis.length, 13 + F.xsG.length,
    13 + F.xsG.length + F.xsT.length, 13 + F.xsG.length + F.xsT.length + xsK.length,
    VerifySub.tableHeights_length _ F.hrowsL, fun h hh ↦ F.hh31 h hh, hτ9, hτ24, F.hdims, F.hst20, F.hst30,
    F.h278, F.h276, F.hdep20, F.hdep34, F.h253, hτc, by omega, hgzc, ?_, ?_, ?_, by omega, by omega, by omega⟩
  · rw [F.h567, F.h320, F.h312]
    simp only [mul_assoc, ← pow_add]
  · rw [F.h578, F.h567, F.h320, F.h312]
    simp only [mul_assoc, ← pow_add]
  · rw [e595, F.h578, F.h567, F.h320, F.h312]
    simp only [mul_assoc, ← pow_add]

/-- A word `gen^x` as a listed power. -/
theorem epow_of {M : ℕ → E} {fp : ℕ} {B : Base} {lo hi x : ℕ} {u : E} (hu : ∀ v, RBase M fp B v → v = u)
    (hx : u = gen ^ x) (hl : lo ≤ x) (hh : x ≤ hi) (h62 : hi < 2 ^ 62) : EPowOk M fp (B, lo, hi) :=
  fun v hv ↦ ⟨x, by rw [hu v hv, hx, efOfKg], hl, hh, by omega⟩

/-- **`verify_sub`'s exponent facts hold at its honest frames.** -/
theorem vs_factsOk (t : TopAt A r K i e j) (hr : r.Ok) (hname : (coreOf j).name = name% «verify_sub») :
    EFactsOk (refMem r.img) e.I.fp vsFacts := by
  obtain ⟨rfl, hs, lm, sl, d, n, gG, gT, gK, hsL, hs31, hτ9, hτ24, hdims, hsl20, hsl30, e278, e276, hd20, hd34,
    e253, hτn, hnd, e579, e567, e578, e595, hGT, hTK, hroom⟩ := vs_vals t hr hname
  have hcj : coreOf (fn_idx% «verify_sub») = fn% «verify_sub» := by
    obtain ⟨f, bufs, kids, hJ, hfj, hfn⟩ := t.found
    rw [hname] at hfn
    subst hfn
    exact Option.some.inj (hfj.symm.trans VerifySub.find_vs)
  obtain ⟨vs, hw, hF, -⟩ := t.events hr
  have hfb := t.fb
  -- the frame's cells
  obtain ⟨c25, c278, c71, c224⟩ := vs_cells
  obtain ⟨a25, a71, a278⟩ := vs_atoms
  rw [← hcj] at a25 a71 a278
  have m25 := t.cell hr hF (x := .n 25)
    (namedOf_atom (topAtoms_on_path hw (List.contains_iff_mem.mp a25)) (by simp [atomUses]))
    (by rw [c25]; omega) (by rw [c25]; omega)
  have m71 := t.cell hr hF (x := .n 71)
    (namedOf_atom (topAtoms_on_path hw (List.contains_iff_mem.mp a71)) (by simp [atomUses]))
    (by rw [c71]; omega) (by rw [c71]; omega)
  have m278 := t.cell hr hF (x := .n 278)
    (namedOf_atom (topAtoms_on_path hw (List.contains_iff_mem.mp a278)) (by simp [atomUses]))
    (by rw [c278]; omega) (by rw [c278]; omega)
  rw [c25] at m25
  rw [c71] at m71
  rw [c278] at m278
  have r27 : ∀ v, RBase (refMem r.img) e.I.fp (.fr 27) v → v = e.σ (.n 25) := fun v hv ↦ by
    change refMem r.img (e.I.fp + 27) = v at hv
    rw [← hv, m25]
  have r224 : ∀ v, RBase (refMem r.img) e.I.fp (.fr 224) v → v = e.σ (.n 278) := fun v hv ↦ by
    change refMem r.img (e.I.fp + 224) = v at hv
    rw [← hv, m278]
  -- the tables' log-heights
  have hD : ∀ t' < 6, ∀ v, RBase (refMem r.img) e.I.fp (.hp 92 (t' + 1)) v → v = gen ^ hs.getD t' 0 := by
    intro t' ht v hv
    have hld := hdims (t' + 1) (by simp [hsL]; omega)
    rw [rbase_uniq hv (rbase_hp_load hr m71 hld)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show t' < hs.length by omega)]
  have hs31' : ∀ t' < 6, hs.getD t' 0 < 31 := fun t' ht ↦
    hs31 _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  -- the calls' returns
  have hw' := hw
  rw [hcj, show (fn% «verify_sub»).body = vsPre ++ (fn% «verify_sub»).body.drop 342 from
    (List.take_append_drop _ _).symm] at hw'
  have hret : ∀ s < 5, ∀ k < (vsRetCalls.getD s ("", [], [])).2.2.length, ∀ v,
      RBase (refMem r.img) e.I.fp (.hp (vsRetSites.getD s 0) (2 + (vsRetCalls.getD s ("", [], [])).2.1.length + k)) v →
        v = e.σ ((vsRetCalls.getD s ("", [], [])).2.2.getD k (.n 0)) := by
    intro s hs k hk v hv
    have hev := call_of_pre hw' vsPre_noRet (vsRetCalls_mem hs)
    have hsite := List.all_eq_true.mp vsRetSites_eq s (List.mem_range.mpr hs)
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsite
    exact top_ret t hr hev hsite.1.1 hsite.1.2 hsite.2 hk hv
  have r185 : ∀ v, RBase (refMem r.img) e.I.fp (.hp 185 4) v → v = e.σ (.n 253) := hret 0 (by decide) 0 (by decide)
  have r221 : ∀ v, RBase (refMem r.img) e.I.fp (.hp 221 4) v → v = e.σ (.n 276) := hret 1 (by decide) 0 (by decide)
  have r577 : ∀ v, RBase (refMem r.img) e.I.fp (.hp 577 17) v → v = e.σ (.n 567) := hret 2 (by decide) 5 (by decide)
  have r591 : ∀ v, RBase (refMem r.img) e.I.fp (.hp 591 28) v → v = e.σ (.n 578) := hret 3 (by decide) 5 (by decide)
  have r591' : ∀ v, RBase (refMem r.img) e.I.fp (.hp 591 29) v → v = e.σ (.n 579) := hret 3 (by decide) 6 (by decide)
  have r604 : ∀ v, RBase (refMem r.img) e.I.fp (.hp 604 20) v → v = e.σ (.n 595) := hret 4 (by decide) 5 (by decide)
  have hcur : ∀ {B : Base} {u : E} {p m : ℕ}, (∀ v, RBase (refMem r.img) e.I.fp B v → v = u) →
      u = e.σ (.n 25) * gen ^ p → p + m ≤ 8192 → ECurOk (refMem r.img) e.I.fp (B, .fr 27, m) :=
    fun hu hp hm v s hv hs' ↦ ⟨_, by rw [hu v hv, hp, r27 s hs', efOfKg], hm⟩
  refine ⟨fun p hp ↦ ?_, fun l hl ↦ ?_, fun c hc ↦ ?_⟩
  · simp only [vsFacts, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with ⟨t', ht', rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl
    · exact epow_of (hD t' (by omega)) rfl (Nat.zero_le _) (by have := hs31' t' (by omega); omega) (by norm_num)
    · exact epow_of (hD 5 (by omega)) rfl hτ9 hτ24 (by norm_num)
    · exact epow_of r224 e278 (Nat.zero_le _) (by omega) (by norm_num)
    · exact epow_of r185 e253 hd20 (by omega) (by norm_num)
    · exact epow_of r591' e579 (by omega) (by omega) (by norm_num)
    · exact epow_of r221 e276 hsl20 hsl30 (by norm_num)
  · simp only [vsFacts, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · intro vx hvx
      refine ⟨hs.getD 5 0, by rw [hD 5 (by omega) vx hvx, efOfKg], by omega, fun vy hvy ↦
        ⟨n, by rw [r591' vy hvy, e579, efOfKg], by omega, by simp only; omega⟩⟩
    · intro vx hvx
      refine ⟨sl, by rw [r221 vx hvx, e276, efOfKg], by omega, fun vy hvy ↦
        ⟨sl - 20, by rw [r224 vy hvy, e278, efOfKg], by omega, by simp only; omega⟩⟩
  · simp only [vsFacts, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcur r577 e567 (by omega)
    · exact hcur r591 e578 (by omega)
    · exact hcur r604 e595 (by omega)

/-- **`verify_sub`'s residuals in its exponent facts' families hold at its honest frames.** -/
theorem vs_top (t : TopAt A r K i e j) (hr : r.Ok) {x : Mode.Res} (hx : vsB j x = true)
    (hin : RIn (refMem r.img) e.I.fp x) : RRes (refMem r.img) e.I.fp x := by
  simp only [vsB, Bool.and_eq_true, beq_iff_eq] at hx
  exact efFam_sound (vs_factsOk t hr hx.1) hx.2 hin

end

end

end LeanVM.Guest.EndExec
