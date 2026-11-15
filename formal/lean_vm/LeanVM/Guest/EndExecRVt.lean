/-
  LeanVM.Guest.EndExecRVt

  `verify_tables`' cursor in the proof stream and its table sumcheck's round count (`VtQ`), carried
  down from `verify_sub`'s front.
-/

module

public import LeanVM.Guest.EndExecRSt
public import LeanVM.Guest.B1.Tables.Vt.Pi
public import LeanVM.Guest.B1.Tables.Vt.BcShare
public import LeanVM.Guest.B1.VerifySub.NodePops

/-!
# `verify_tables`' cursor

`VtQ J`: at an instance of `verify_tables`, its cursor is `stream·g^p` with room for `1009` words
past it, and its table sumcheck runs `n < 34` rounds (`g_zc_n = g^n`).

`vt_holds`: a node's body gives `B1.Tables.VtH` and its returns. `vt_zc_front`: the loops' counters
start at `1` and the first round record's cursor is `14` words past the cursor (`vt_cur13`, the
bytecode share's three tail rounds). `vtQ_all`: at every honest instance, by `Res.insts_down`: its
only caller is `verify_sub` (`Res.termCallers_all`), at `vtArgsV` (`vs_vt_sites`), whose front puts
the cursor at `stream·g^(13 + |xsG|)` with room for `verify_keccak`'s words (`vk_room`), and `g_zc_n`,
returned, is `g^|chis|`, `|chis|` at most the bus point's length (`TCtx`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **`verify_tables`' cursor in its stream**: `cursor = stream·g^p` with room for `1009` words, and
`g_zc_n = g^n`, `n < 34`. -/
def VtQ (J : Inst) : Prop :=
  ∀ σ bufs kids, J.t = .node "verify_tables" σ bufs kids →
    ∃ p n, σ (.n 5) = σ (.n 20) * gen ^ p ∧ σ (.n 2545) = gen ^ n ∧ n < 34 ∧ p + 1009 ≤ 8192

/-- `verify_tables`' call arguments and returns in `verify_sub`. -/
def vtArgsV : List V :=
  [562, 563, 564, 565, 566, 567, 0, 1, 254, 253, 71, 26, 4, 335, 559, 6, 569, 568, 572, 570, 25].map .n
def vtRetsV : List V := (List.range 10).map fun k ↦ .n (573 + k)

end

public section

/-! ## `verify_tables`' body -/

/-- **A node's body**: `VtH` and the returns `vtRets`. -/
theorem vt_holds {rd : Reader} {C : CallRel} (hC : CallRel.Le C (coreProgram.Rel rd)) {σ : Val}
    {rets : List E} {fn : Fn} (hf : coreProgram.find? "verify_tables" = some fn)
    (h : Stmt.HoldsList C rd σ fn.body False (· = rets)) :
    Tables.VtH rd σ ∧ Tables.vtRets.map σ = rets := by
  obtain ⟨fn', hf', -, hb⟩ := Tables.vtFound
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
  rw [hb, holdsList_append] at h
  obtain ⟨h1, h2⟩ := (holdsList_noRet _ Tables.vtPre_noRet _ _).mp h
  simp only [Stmt.HoldsList, Stmt.Holds] at h2
  exact ⟨⟨_, holdsList_mono hC _ id (fun _ h ↦ h) h1⟩, h2⟩

/-- **The bytecode share's cursor**: its three tail rounds leave the cursor `13` words on. -/
theorem vt_cur13 {rd : Reader} {σ : Val} (h : Tables.VtH rd σ) : σ (.n 1898) = σ (.n 5) * gen ^ 13 := by
  have a1938 := h.atomAt 1938 (.const (.n 1875) (word 128 0)) (by decide +kernel)
  have a1939 := h.atomAt 1939 (.mul (.n 1876) (.n 5) (.n 1875)) (by decide +kernel)
  have k1 := h.callAt 1940 "opening_tail_round" [.n 1863, .n 1864, .n 1865, .n 1866, .n 1867,
    .n 1876, .n 1874, .n 18] [.n 1877, .n 1878, .n 1879, .n 1880, .n 1881, .n 1882, .n 1883,
    .n 1884] (by decide +kernel)
  have k2 := h.callAt 1942 "opening_tail_round" [.n 1877, .n 1878, .n 1879, .n 1880, .n 1881,
    .n 1882, .n 1883, .n 18] [.n 1885, .n 1886, .n 1887, .n 1888, .n 1889, .n 1890, .n 1891,
    .n 1892] (by decide +kernel)
  have k3 := h.callAt 1944 "opening_tail_round" [.n 1885, .n 1886, .n 1887, .n 1888, .n 1889,
    .n 1890, .n 1891, .n 18] [.n 1893, .n 1894, .n 1895, .n 1896, .n 1897, .n 1898, .n 1899,
    .n 1900] (by decide +kernel)
  simp only [Atom.Holds] at a1938 a1939
  simp only [List.map_cons, List.map_nil] at k1 k2 k3
  obtain ⟨_, _, -, e1⟩ := Tables.vt_otr k1
  obtain ⟨_, _, -, e2⟩ := Tables.vt_otr k2
  obtain ⟨_, _, -, e3⟩ := Tables.vt_otr k3
  obtain ⟨-, u1, -, -⟩ := Tables.vt_split8 (by rfl) e1
  obtain ⟨-, u2, -, -⟩ := Tables.vt_split8 (by rfl) e2
  obtain ⟨-, u3, -, -⟩ := Tables.vt_split8 (by rfl) e3
  have hw128 : σ (.n 1875) = gen ^ 7 := by
    rw [a1938, show (128 : ℕ) = 2 ^ 7 by norm_num, Tables.tb_word_two_pow (by norm_num)]
  rw [u3, u2, u1, a1939, hw128]
  ring

/-- **The table sumcheck's loops' setup**: both counters start at `1`, and the first round record
holds the cursor `14` words past `verify_tables`' cursor. -/
theorem vt_zc_front {rd : Reader} {σ : Val} (h : Tables.VtH rd σ) :
    σ (.n 2638) = 1 ∧ σ (.n 2641) = 1 ∧ LoadHolds rd (σ (.n 2628)) 5 (σ (.n 5) * gen ^ 14) := by
  have c2638 := h.atomAt 2667 (.const (.n 2638) (word 1 0)) (by decide +kernel)
  have c2641 := h.atomAt 2671 (.const (.n 2641) (word 1 0)) (by decide +kernel)
  have c2632 := h.atomAt 2658 (.const (.n 2632) (word 2 0)) (by decide +kernel)
  have m2633 := h.atomAt 2659 (.mul (.n 2633) (.n 1898) (.n 2632)) (by decide +kernel)
  have l2633 := h.atomAt 2660 (.load (.n 2633) (.n 2628) 5) (by decide +kernel)
  simp only [Atom.Holds] at c2638 c2641 c2632 m2633 l2633
  refine ⟨by rw [c2638, Tables.tb_word_one], by rw [c2641, Tables.tb_word_one], ?_⟩
  rw [m2633, c2632, Tables.tb_word_gen, vt_cur13 h] at l2633
  rw [show σ (.n 5) * gen ^ 14 = σ (.n 5) * gen ^ 13 * gen by ring]
  exact l2633

/-! ## Down from `verify_sub` -/

/-- **`verify_sub` calls `verify_tables` only at `vtArgsV`.** -/
theorem vs_vt_sites :
    Res.sitesB (fun f args rets ↦ f != "verify_tables" || (args == vtArgsV && rets == vtRetsV))
      VerifySub.vsT = true := by
  decide +kernel

theorem vt_params : (fn% «verify_tables»).params = (List.range 21).map V.n := by decide +kernel

theorem vt_not_loop : (fn% «verify_tables»).loop = false := by decide +kernel

variable {r : Ref}

/-- **`verify_tables`' cursor passes down from `verify_sub`.** -/
theorem vtQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) VtQ := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph _
    σ bufs kids hJt
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  have hcf : c.f = "verify_tables" := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  have hfs : ∀ f', 1 ≤ B2C.fs f' := fun f' ↦ by
    unfold B2C.fs; split <;> simp [B2C.mainFrame, Data.mainCells, Data.jtSlots]
  -- the callee's body
  obtain ⟨hpar, hbJ⟩ := Res.holds_of_valid hfs hJv VerifySub.find_vt
  obtain ⟨hJ, hrJ⟩ := vt_holds (fun _ _ _ h ↦ Res.KidRel.rel h) VerifySub.find_vt hbJ
  -- the caller is `verify_sub`
  have hmem : ("verify_tables", name% «verify_sub») ∈ Res.termCallers := by decide
  have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI))
    hw c hc) _ hmem
  have hnI := Da.fn_name_of_find hfI
  rw [hcf] at hcal
  simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
  have hvs : fI = name% «verify_sub» := by
    rcases hcal with h | ⟨h, hl⟩
    · rw [← hnI, h]
    · exfalso
      rw [hnI] at h
      subst h
      obtain rfl : fnI = fn% «verify_tables» := Option.some.inj (hfI.symm.trans VerifySub.find_vt)
      rw [vt_not_loop] at hl; cases hl
  subst hvs
  obtain rfl : fnI = fn% «verify_sub» := Option.some.inj (hfI.symm.trans VerifySub.find_vs)
  -- its call of `verify_tables`
  have hs := Res.calls_sites (show Res.sitesB _ (fn% «verify_sub»).body = true by
    rw [VerifySub.vs_body]; exact vs_vt_sites) hw c hc
  rw [hcf] at hs
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨ha, hrt⟩ := hs
  rw [ha, vt_params] at hpar
  have e5 := params_get hpar (k := 5) (by decide) rfl
  have e20 := params_get hpar (k := 20) (by decide) rfl
  rw [hrt] at hrJ
  have e5991 : σ (.n 5991) = σI (.n 579) := by
    have := congrArg (·[6]?) hrJ
    simpa [Tables.vtRets, vtRetsV] using this
  -- its front
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
  obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv hfI
  rw [VerifySub.vs_body] at hb
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  have hQ := carryQ_all hr I hI _ σI bufsI kidsI hIt _ hfI (name% «verify_sub», 4, .tab) (by decide) rfl
    (.n 4) (by rw [VerifySub.vs_params]; rfl)
  obtain ⟨hexp, hwin⟩ := hQ
  obtain ⟨⟨F⟩, -⟩ := VerifySub.vs_front (by omega) r.img (fun _ _ _ h ↦ Res.KidRel.rel h)
    (bytecode := List.replicate (2 ^ 23) 0) List.length_replicate hexp hwin hb
  -- the words before the cursor
  obtain ⟨sp, hsp⟩ := front_carried F
  obtain ⟨hlG, sp', hsp'⟩ := runsTo_reads (reads_gkrPhase _) F.hG hsp
  have hhl : ∀ h ∈ (Tables.layoutOf (List.replicate (2 ^ 23) 0) F.logMem F.rowsN).tableLogHeights,
      h ≤ 30 := by
    rw [VerifySub.layoutOf_heights]
    intro h hh'
    have := F.hh31 h hh'
    omega
  obtain ⟨hlT, -⟩ := runsTo_reads (reads_tablesSeg _ (fun w p v ↦ Child.reads_claimedBytecodeValue _ w p v)
    _ hhl _ _ _ _ _) F.hT hsp'
  -- the round count
  have hctx := F.hctx
  obtain ⟨chis, hbpR, hgmu, -, hgz, hle, -⟩ := hctx
  have hbusL : F.bus.point.length =
      VerifySub.busDepth (Tables.layoutOf (List.replicate (2 ^ 23) 0) F.logMem F.rowsN) :=
    Value.gen_pow_inj (by have := VerifySub.mem_size_le (by omega) r.img hbpR; omega)
      (by have := F.hdep34; omega) (hgmu.symm.trans F.h253)
  have hroom := vk_room F.hdep34 hlG hlT (τ := 0) (by omega)
  refine ⟨13 + F.xsG.length, chis.length, ?_, ?_, by have := F.hdep34; omega, ?_⟩
  · rw [e5, e20, F.h567, F.h320, F.h312]
    ring
  · rw [← (Tables.vt_pi hJ).2.2.2.1, e5991, hgz]
  · simp only [vkNeed] at hroom
    omega

/-- **`verify_tables`' cursor at every honest instance.** -/
theorem vtQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, VtQ J := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  refine Res.insts_down (vtQ_step hr) r.T _ r.hdr hv (fun J h ↦ h) (fun J rest he ↦ ?_)
  obtain ⟨J', rest', he', ht, -⟩ := head_insts (fs := B2C.fs) (lp := coreProgram.loop) (H := B2C.H) r.T
    (0, r.T.block B2C.fs coreProgram.loop) r.hdr
  rw [he'] at he
  obtain ⟨rfl, -⟩ := List.cons.inj he
  intro σ bufs kids hJt
  have hn := hr.name
  rw [← ht, hJt] at hn
  simp only [Tree.name] at hn
  exact absurd hn (by decide)

end

end LeanVM.Guest.EndExec
