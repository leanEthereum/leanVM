/-
  LeanVM.Guest.CoreMode.Fn.verify_tables.ResVt

  `verify_tables`' cursor in the proof stream and its table sumcheck's round count (`VtQ`), carried
  down from `verify_sub`'s front.
-/

module

public import LeanVM.Guest.CoreMode.Fn.verify_keccak.ResSt
public import LeanVM.Guest.B1.Tables.Vt.Pi
public import LeanVM.Guest.B1.Tables.Vt.BcShare
public import LeanVM.Guest.B1.VerifySub.NodePops
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# `verify_tables`' cursor

`VtQ J`: at an instance of `verify_tables`, its cursor is `stream·g^p` with room for `1009` words
past it, and its table sumcheck runs `n < 34` rounds (`g_zc_n = g^n`).

`vt_holds`: a node's body gives `B1.Tables.VtH` and its returns. `vt_zc_front`: the rounds loop's counter
starts at `1` and the first round record's cursor is `14` words past the cursor (`vt_cur13`, the
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
    ∃ p n, σ (.n (val% «verify_tables» "cursor@1")) = σ (.n (val% «verify_tables» "stream")) * gen ^ p ∧ σ (.n (val% «verify_tables» "g_zc_n")) = gen ^ n ∧ n < 34 ∧ p + 1009 ≤ 8192

/-- `verify_tables`' call arguments and returns in `verify_sub`. -/
def vtArgsV : List V :=
  [val% «verify_sub» "fs0@3", val% «verify_sub» "fs1@3", val% «verify_sub» "fs2@3", val% «verify_sub» "fs3@3", val% «verify_sub» "fs4@3", val% «verify_sub» "cursor@2", val% «verify_sub» "pi_0", val% «verify_sub» "pi_1", val% «verify_sub» "zeta", val% «verify_sub» "g_bus_mu", val% «verify_sub» "dims_g", val% «verify_sub» "table_rows", val% «verify_sub» "g_squares", val% «verify_sub» "fp_w", val% «verify_sub» "nxt[0]@19", val% «verify_sub» "claim_pool", val% «verify_sub» "chi", val% «verify_sub» "gkr_leaves", val% «verify_sub» "fs0@4~11", val% «verify_sub» "bc_point", val% «verify_sub» "stream"].map .n
def vtRetsV : List V := (List.range 10).map fun k ↦ .n (val% «verify_sub» "fs0@4" + k)

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
theorem vt_cur13 {rd : Reader} {σ : Val} (h : Tables.VtH rd σ) : σ (.n (val% «verify_tables» "cursor@4")) = σ (.n (val% «verify_tables» "cursor@1")) * gen ^ 13 := by
  have a1938 := h.atomAt (pos% «verify_tables» "s42.u1.s0#8") (.const (.n (val% «verify_tables» "bfs0@1~8")) (word 128 0)) (by decide +kernel)
  have a1939 := h.atomAt (pos% «verify_tables» "s42.u1.s0#9") (.mul (.n (val% «verify_tables» "bfs0@1~9")) (.n (val% «verify_tables» "cursor@1")) (.n (val% «verify_tables» "bfs0@1~8"))) (by decide +kernel)
  have k1 := h.callAt (pos% «verify_tables» "s42.u1.s0#0") "opening_tail_round" [.n (val% «verify_tables» "nxt[8]@2"), .n (val% «verify_tables» "nxt[9]@2"), .n (val% «verify_tables» "nxt[10]@2"), .n (val% «verify_tables» "nxt[11]@2"), .n (val% «verify_tables» "nxt[12]@2"),
    .n (val% «verify_tables» "bfs0@1~9"), .n (val% «verify_tables» "bc_claim@1"), .n (val% «verify_tables» "tabs")] [.n (val% «verify_tables» "bfs0@1"), .n (val% «verify_tables» "bfs1@1"), .n (val% «verify_tables» "bfs2@1"), .n (val% «verify_tables» "bfs3@1"), .n (val% «verify_tables» "bfs4@1"), .n (val% «verify_tables» "cursor@2"), .n (val% «verify_tables» "bc_claim@2"),
    .n (val% «verify_tables» "bc_r@1")] (by decide +kernel)
  have k2 := h.callAt (pos% «verify_tables» "s42.u2.s0#0") "opening_tail_round" [.n (val% «verify_tables» "bfs0@1"), .n (val% «verify_tables» "bfs1@1"), .n (val% «verify_tables» "bfs2@1"), .n (val% «verify_tables» "bfs3@1"), .n (val% «verify_tables» "bfs4@1"),
    .n (val% «verify_tables» "cursor@2"), .n (val% «verify_tables» "bc_claim@2"), .n (val% «verify_tables» "tabs")] [.n (val% «verify_tables» "bfs0@2"), .n (val% «verify_tables» "bfs1@2"), .n (val% «verify_tables» "bfs2@2"), .n (val% «verify_tables» "bfs3@2"), .n (val% «verify_tables» "bfs4@2"), .n (val% «verify_tables» "cursor@3"), .n (val% «verify_tables» "bc_claim@3"),
    .n (val% «verify_tables» "bc_r@2")] (by decide +kernel)
  have k3 := h.callAt (pos% «verify_tables» "s42.u3.s0#0") "opening_tail_round" [.n (val% «verify_tables» "bfs0@2"), .n (val% «verify_tables» "bfs1@2"), .n (val% «verify_tables» "bfs2@2"), .n (val% «verify_tables» "bfs3@2"), .n (val% «verify_tables» "bfs4@2"),
    .n (val% «verify_tables» "cursor@3"), .n (val% «verify_tables» "bc_claim@3"), .n (val% «verify_tables» "tabs")] [.n (val% «verify_tables» "bfs0@3"), .n (val% «verify_tables» "bfs1@3"), .n (val% «verify_tables» "bfs2@3"), .n (val% «verify_tables» "bfs3@3"), .n (val% «verify_tables» "bfs4@3"), .n (val% «verify_tables» "cursor@4"), .n (val% «verify_tables» "bc_claim@4"),
    .n (val% «verify_tables» "bc_r@3")] (by decide +kernel)
  simp only [Atom.Holds] at a1938 a1939
  simp only [List.map_cons, List.map_nil] at k1 k2 k3
  obtain ⟨_, _, -, e1⟩ := Tables.vt_otr k1
  obtain ⟨_, _, -, e2⟩ := Tables.vt_otr k2
  obtain ⟨_, _, -, e3⟩ := Tables.vt_otr k3
  obtain ⟨-, u1, -, -⟩ := Tables.vt_split8 (by rfl) e1
  obtain ⟨-, u2, -, -⟩ := Tables.vt_split8 (by rfl) e2
  obtain ⟨-, u3, -, -⟩ := Tables.vt_split8 (by rfl) e3
  have hw128 : σ (.n (val% «verify_tables» "bfs0@1~8")) = gen ^ 7 := by
    rw [a1938, show (128 : ℕ) = 2 ^ 7 by norm_num, Tables.tb_word_two_pow (by norm_num)]
  rw [u3, u2, u1, a1939, hw128]
  ring

/-- **The table sumcheck's rounds loop's setup**: its counter starts at `1`, and the first round record holds the
cursor `14` words past `verify_tables`' cursor. -/
theorem vt_zc_front {rd : Reader} {σ : Val} (h : Tables.VtH rd σ) :
    σ (.n (val% «verify_tables» "s73#2")) = 1 ∧ LoadHolds rd (σ (.n (val% «verify_tables» "zc_rounds"))) 5 (σ (.n (val% «verify_tables» "cursor@1")) * gen ^ 14) := by
  have c2638 := h.atomAt (pos% «verify_tables» "s73#2") (.const (.n (val% «verify_tables» "s73#2")) (word 1 0)) (by decide +kernel)
  have c2632 := h.atomAt (pos% «verify_tables» "s69#0") (.const (.n (val% «verify_tables» "s69#0")) (word 2 0)) (by decide +kernel)
  have m2633 := h.atomAt (pos% «verify_tables» "s69#1") (.mul (.n (val% «verify_tables» "s69#1")) (.n (val% «verify_tables» "cursor@4")) (.n (val% «verify_tables» "s69#0"))) (by decide +kernel)
  have l2633 := h.atomAt (pos% «verify_tables» "s69#1" + 1) (.load (.n (val% «verify_tables» "s69#1")) (.n (val% «verify_tables» "zc_rounds")) 5) (by decide +kernel)
  simp only [Atom.Holds] at c2638 c2632 m2633 l2633
  refine ⟨by rw [c2638, Tables.tb_word_one], ?_⟩
  rw [m2633, c2632, Tables.tb_word_gen, vt_cur13 h] at l2633
  rw [show σ (.n (val% «verify_tables» "cursor@1")) * gen ^ 14 = σ (.n (val% «verify_tables» "cursor@1")) * gen ^ 13 * gen by ring]
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
  have hfs : ∀ f', 1 ≤ B2C.fs f' := Res.fs_pos
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
  have e5987 : σ (.n (val% «verify_tables» "s92#0[6]")) = σI (.n (val% «verify_sub» "fs0@4" + 6)) := by
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
  · rw [← (Tables.vt_pi hJ).2.2.2.1, e5987, hgz]
  · simp only [vkNeed] at hroom
    omega

/-- **`verify_tables`' cursor at every honest instance.** -/
theorem vtQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, VtQ J := by
  refine insts_all hr (vtQ_step hr) fun J hm ↦ ?_
  intro σ bufs kids hJt
  have hn := hm _ _ _ _ hJt
  exact absurd hn (by decide)

end

end LeanVM.Guest.EndExec
