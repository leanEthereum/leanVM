/-
  LeanVM.Guest.EndExecRGkrQ

  `verify_bus_gkr`'s cursor in the proof stream (`VbgQ`), carried down from `verify_sub`'s front, and
  its layer loop's slots' cursors (`LyQ`), carried down from it.
-/

module

public import LeanVM.Guest.EndExecRStP
public import LeanVM.Guest.B1.Gkr.Holds
public import LeanVM.Guest.B1.Gkr.RoundsHolds

/-!
# `verify_bus_gkr`'s cursors

`VbgQ J`: at an instance of `verify_bus_gkr`, its cursor is `stream·g^13`. `vbgQ_all`: its only caller
is `verify_sub` (`Res.termCallers_all`), at `vbgArgsV` (`vs_vbg_sites`), whose front puts the cursor
`13` words past the stream (`VerifySub.vs_front`).

`LyQ r J`: at an instance of the layer loop `verify_bus_gkr_loop0` at `x = g^j` below `n_pairs = g^m`
(`m ≤ 16`), the depth's parity `sh`, the slot of `L = 2j + 2 - sh` in `layers` holds the cursor
`stream·g^q`, with room for `140` words a layer to the last. `ly_curs`: an iteration's records and
slots, on its body alone: the first record holds the slot's cursor, the record the pairs end at
`8j` words on (`l29_loop`), the last record `4L` (`ly_rounds`), the next slot `4L + 12`.
`lyQ_all`: the loop's callers are `verify_bus_gkr` (its root slot's cursor `8` or `14` words past
the roots, `vbg_root_slot`) and its own tail.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Tables
open LeanVM.Guest.Value (gen_pow_eq_ofK e_add_eq_zero_iff e_add_self gen_pow_inj)
open LeanVM.Guest.B2C (idxOf fsN fn_of_idx cellJ kidHdr siteOf)
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **`verify_bus_gkr`'s cursor**: `13` words into its stream. -/
def VbgQ (J : Inst) : Prop :=
  ∀ σ bufs kids, J.t = .node name% «verify_bus_gkr» σ bufs kids → σ (.n 5) = σ (.n 9) * gen ^ 13

/-- `verify_bus_gkr`'s call arguments in `verify_sub`. -/
def vbgArgsV : List V := [554, 555, 556, 557, 558, 320, 253, 254, 561, 25].map .n

/-- `verify_bus_gkr_loop0`'s call arguments in `verify_bus_gkr`. -/
def lyArgsV : List V := [369, 366, 135, 16, 8, 18, 17, 63, 133, 9, 6].map .n

/-- **A layer slot's cursor in the stream**: the loop at `x = g^j < g^m`, the slot of
`L = 2j + 2 - sh` holding `stream·g^q`, room for `140` words a layer. -/
def LyQ (r : Ref) (J : Inst) : Prop :=
  ∀ σ bufs kids, J.t = .node name% «verify_bus_gkr_loop0» σ bufs kids →
    ∃ j m sh q, σ (.n 0) = gen ^ j ∧ σ (.n 1) = gen ^ m ∧ j < m ∧ m ≤ 16 ∧ sh < 2 ∧
      σ (.n 2) = gen ^ (2 - sh) ∧ σ (.n 8) = gen ^ sh ∧
      LoadHolds r.img.read (σ (.n 3)) (10 * (2 * j + 2 - sh) + 5) (σ (.n 9) * gen ^ q) ∧
      q + 140 * (m - j) ≤ 8192

end

public section

theorem find_vbg : coreProgram.find? name% «verify_bus_gkr» = some fn% «verify_bus_gkr» :=
  coreProgram_find?_at (j := idx% «verify_bus_gkr») rfl

theorem find_ly : coreProgram.find? name% «verify_bus_gkr_loop0» = some fn% «verify_bus_gkr_loop0» :=
  coreProgram_find?_at (j := idx% «verify_bus_gkr_loop0») rfl

theorem vbg_params : (fn% «verify_bus_gkr»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] :=
  rfl

theorem ly_params : (fn% «verify_bus_gkr_loop0»).params =
    [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10] := rfl

theorem vbg_body : (fn% «verify_bus_gkr»).body = vbgPre ++ [.ret vbgRets] := by
  obtain ⟨fn, hf, -, hb⟩ := vbgFound
  rw [Option.some.inj (find_vbg.symm.trans hf)]; exact hb

theorem ly_body : (fn% «verify_bus_gkr_loop0»).body = lyPre ++ [.ret []] := by
  obtain ⟨fn, hf, -, hb⟩ := lyFound
  rw [Option.some.inj (find_ly.symm.trans hf), hb]; exact lyBody_eq

theorem gkr_hfs : ∀ f', 1 ≤ B2C.fs f' := fun f' ↦ by
  unfold B2C.fs; split <;> simp [B2C.mainFrame, Data.mainCells, Data.jtSlots]

theorem vbg_not_loop : (fn% «verify_bus_gkr»).loop = false := by decide +kernel

theorem ly_loop : (fn% «verify_bus_gkr_loop0»).loop = true ∧ Res.endOfFn (fn% «verify_bus_gkr_loop0») = some none :=
  by decide +kernel

/-- **`verify_sub` calls `verify_bus_gkr` only at `vbgArgsV`.** -/
theorem vs_vbg_sites :
    Res.sitesB (fun f args _ ↦ f != name% «verify_bus_gkr» || args == vbgArgsV) VerifySub.vsT = true := by
  decide +kernel

/-- **`verify_bus_gkr` calls its layer loop only at `lyArgsV`.** -/
theorem vbg_ly_sites :
    Res.sitesB (fun f args _ ↦ f != name% «verify_bus_gkr_loop0» || args == lyArgsV)
      (fn% «verify_bus_gkr»).body = true := by
  decide +kernel

/-! ## An iteration of the layer loop -/

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **An iteration's cursors**: from the slot's cursor `cur`, the first record (`σ 56`) holds it, the
pair loop is called on it, the record the pairs end at holds it `8j` words on (`σ 65`), the last
record `4L` (`σ 80`), and the next slot `4L + 12`. -/
theorem ly_curs (hC : CallRel.Le C (coreProgram.Rel rd)) (h : Stmt.HoldsList C rd σ lyPre True kret)
    {j sh : ℕ} {cur : E} (hj : j < 2 ^ 30) (hsh : sh < 2) (hx : σ (.n 0) = gen ^ j)
    (hsg : σ (.n 2) = gen ^ (2 - sh)) (e8 : σ (.n 8) = gen ^ sh)
    (hcur : LoadHolds rd (σ (.n 3)) (10 * (2 * j + 2 - sh) + 5) cur) :
    LoadHolds rd (σ (.n 56)) 4310 cur ∧
      (1 + σ (.n 0) ≠ 0 → C name% «verify_bus_gkr_loop0_loop0» [1, σ (.n 0), σ (.n 56), σ (.n 55), σ (.n 4)]
        []) ∧
      σ (.n 65) = cur * gen ^ (8 * j) ∧ σ (.n 80) = cur * gen ^ (4 * (2 * j + 2 - sh)) ∧
      LoadHolds rd (σ (.n 3)) (10 * (2 * j + 2 - sh + 2) + 5) (cur * gen ^ (4 * (2 * j + 2 - sh) + 12)) := by
  have hnr := lyPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have m11 := a 0 (.mul (.n 11) (.n 0) (.n 0)) (by decide +kernel)
  have m12 := a 1 (.mul (.n 12) (.n 11) (.n 2)) (by decide +kernel)
  have m13 := a 2 (.mul (.n 13) (.n 12) (.n 12)) (by decide +kernel)
  have m14 := a 3 (.mul (.n 14) (.n 13) (.n 13)) (by decide +kernel)
  have m15 := a 4 (.mul (.n 15) (.n 14) (.n 12)) (by decide +kernel)
  have m16 := a 5 (.mul (.n 16) (.n 15) (.n 15)) (by decide +kernel)
  have m17 := a 6 (.mul (.n 17) (.n 3) (.n 16)) (by decide +kernel)
  have l23 := a 12 (.load (.n 23) (.n 17) 5) (by decide +kernel)
  have l23' := a 39 (.load (.n 23) (.n 56) 4310) (by decide +kernel)
  have l60 := a 44 (.load (.n 60) (.n 56) 5172) (by decide +kernel)
  have c61 := a 45 (.const (.n 61) (word 1 0)) (by decide +kernel)
  have a62 := a 46 (.add (.n 62) (.n 61) (.n 0)) (by decide +kernel)
  have c63 := a 47 (.const (.n 63) (word 1 0)) (by decide +kernel)
  have m64 := a 49 (.mul (.n 64) (.n 56) (.n 0)) (by decide +kernel)
  have l65 := a 50 (.load (.n 65) (.n 64) 4310) (by decide +kernel)
  have m72 := a 54 (.mul (.n 72) (.n 56) (.n 0)) (by decide +kernel)
  have c73 := a 55 (.const (.n 73) (word 2 0)) (by decide +kernel)
  have m74 := a 56 (.mul (.n 74) (.n 72) (.n 73)) (by decide +kernel)
  have l80 := a 62 (.load (.n 80) (.n 74) 4310) (by decide +kernel)
  have hst := tb_holds_slice hnr h 34 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (37 + k)) (.n 56) (862 * k))) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hst
  simp only [Atom.Holds] at m11 m12 m13 m14 m15 m16 m17 l23 l23' l60 c61 a62 c63 m64 l65 m72 c73 m74 l80 hst
  rw [tb_word_one] at c61 c63
  rw [tb_word_gen] at c73
  obtain ⟨-, hc35⟩ := tb_holds_callIf hnr h 48 (.n 62) name% «verify_bus_gkr_loop0_loop0» [.n 63,
      .n 0, .n 56, .n 55, .n 4] (by decide +kernel)
  simp only [List.map_cons, List.map_nil, c63] at hc35
  set L := 2 * j + 2 - sh with hL
  have e11 : σ (.n 11) = gen ^ (2 * j) := by rw [m11, hx, ← pow_add]; ring_nf
  have e12 : σ (.n 12) = gen ^ L := by
    rw [m12, e11, hsg, ← pow_add, show 2 * j + (2 - sh) = L by omega]
  have e17 : σ (.n 17) = σ (.n 3) * gen ^ (10 * L) := by
    rw [m17, m16, m15, m14, m13, e12, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    ring_nf
  rw [e17, tb_loadHolds_mul_gen_pow] at l23
  obtain rfl : σ (.n 23) = cur := tb_loadHolds_unique l23 hcur
  -- the first record
  have hcap : TbCapAt rd (σ (.n 56)) 0 gkCap ((List.range 5).map fun k ↦ σ (.n (37 + k))) := by
    refine ⟨by simp, fun k hk => ?_⟩
    have hk5 : k < 5 := by simpa using hk
    simp only [List.getElem_map, List.getElem_range]
    rw [show 0 + k * gkCap = 862 * k by unfold gkCap; ring]
    exact hst k hk5
  have h0 : TbGkrRoundsOut 0 0 rd (σ (.n 56)) (σ (.n 55)) := gkrRoundsOut_zero hcap l23' l60
  -- the pairs
  have hcall : 1 + σ (.n 0) ≠ 0 → C name% «verify_bus_gkr_loop0_loop0» [1, σ (.n 0), σ (.n 56), σ (.n 55),
      σ (.n 4)] [] := fun hne => hc35 (by rw [a62, c61]; exact hne)
  have R2 := l29_loop (h := j) hx (by omega) (fun hne => hC _ _ _ (hcall hne)) h0
  obtain ⟨-, cur2, -, -, -, -, hcur2, -, -, -, -, -, -, -, -, hend2, -⟩ := R2
  obtain rfl : cur2 = σ (.n 23) := tb_loadHolds_unique hcur2 l23'
  rw [m64, hx, tb_loadHolds_mul_gen_pow] at l65
  have e65 : σ (.n 65) = σ (.n 23) * gen ^ (8 * j) := by
    rw [tb_loadHolds_unique l65 hend2]; ring_nf
  -- the last record
  have R := ly_rounds hC tb_gkr_rounds_holds h hj hsh hx e11 e8 h0
  obtain ⟨-, cur', -, -, -, -, hcur', -, -, -, -, -, -, -, -, hcurT, -⟩ := R
  obtain rfl : cur' = σ (.n 23) := tb_loadHolds_unique hcur' l23'
  have e74 : σ (.n 74) = σ (.n 56) * gen ^ (j + 1) := by rw [m74, m72, c73, hx, pow_succ]; ring
  rw [e74, tb_loadHolds_mul_gen_pow] at l80
  have e80 : σ (.n 80) = σ (.n 23) * gen ^ (4 * L) := tb_loadHolds_unique l80 hcurT
  -- the next slot
  obtain ⟨-, s25, -⟩ := ly_stores h
  rw [e17, tb_loadHolds_mul_gen_pow, e80, mul_assoc, ← pow_add] at s25
  refine ⟨l23', hcall, e65, e80, ?_⟩
  rw [show 10 * (L + 2) + 5 = 10 * L + 25 by ring]
  exact s25

end Sem

/-! ## `verify_bus_gkr`'s root slot -/

/-- **`verify_bus_gkr`'s depth, tables and root slot**: `g_bus_mu = g^d`, `d < 33`, the loop's bound
`g^((d - 1) / 2)`, `start_g = g^(2 - sh)` and `odd_g = g^sh` for `sh = d % 2`, and the root slot, of
`L = 2 - sh`, holding the cursor `8` or `14` words past the frame's. -/
theorem vbg_root_slot {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) {C : CallRel} {σ : Val} {kret : List E → Prop}
    (h : Stmt.HoldsList C Lm.read σ vbgPre True kret) :
    ∃ d < 33, σ (.n 6) = gen ^ d ∧ σ (.n 366) = gen ^ ((d - 1) / 2) ∧ σ (.n 135) = gen ^ (2 - d % 2) ∧
      σ (.n 133) = gen ^ (d % 2) ∧ σ (.n 369) = 1 ∧
      LoadHolds Lm.read (σ (.n 16)) (10 * (2 - d % 2) + 5)
        (σ (.n 5) * gen ^ (if d % 2 = 0 then 14 else 8)) := by
  have hnr := vbgPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := Lm.read) (σ := σ) (kret := kret) hnr h n a heq
  have c19 := a 9 (.const (.n 19) (word 4294967296 0)) (by decide +kernel)
  have rc := a 10 (.rangeCheck (.n 6) (.n 20) (.n 21) (.n 22) (.n 19)) (by decide +kernel)
  simp only [Atom.Holds] at c19 rc
  obtain ⟨d, hd, hg⟩ := tb_rc_sound' hμ Lm (K := 33) (by omega) (by norm_num)
    (by rw [c19, show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num),
      gen_pow_eq_ofK]) rc.1 rc.2.1 rc.2.2
  obtain ⟨e133, e366, e135⟩ := vbg_tables h hg hd
  have m136 := a 178 (.mul (.n 136) (.n 135) (.n 135)) (by decide +kernel)
  have m137 := a 179 (.mul (.n 137) (.n 136) (.n 136)) (by decide +kernel)
  have m138 := a 180 (.mul (.n 138) (.n 137) (.n 135)) (by decide +kernel)
  have m139 := a 181 (.mul (.n 139) (.n 138) (.n 138)) (by decide +kernel)
  have m140 := a 182 (.mul (.n 140) (.n 16) (.n 139)) (by decide +kernel)
  have c141 := a 183 (.const (.n 141) (word 1 0)) (by decide +kernel)
  have a142 := a 184 (.add (.n 142) (.n 133) (.n 141)) (by decide +kernel)
  have c369 := a 190 (.const (.n 369) (word 1 0)) (by decide +kernel)
  simp only [Atom.Holds] at m136 m137 m138 m139 m140 c141 a142 c369
  rw [tb_word_one] at c141 c369
  have e140 : σ (.n 140) = σ (.n 16) * gen ^ (10 * (2 - d % 2)) := by
    rw [m140, m139, m138, m137, m136, e135, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    ring_nf
  have hi := tb_holds_slice hnr h 185 [.ite (.n 142) rtFour rtTwo] (by decide +kernel)
  simp only [Stmt.HoldsList] at hi
  rw [tb_holds_ite_noRet _ _ _ rtFour_noRet rtTwo_noRet] at hi
  obtain ⟨⟨-, hfour, htwo⟩, -⟩ := hi
  refine ⟨d, hd, hg, e366, e135, e133, c369, ?_⟩
  rw [← tb_loadHolds_mul_gen_pow, ← e140]
  rcases Nat.mod_two_eq_zero_or_one d with h2 | h2
  · have h0 : σ (.n 142) = 0 := by rw [a142, c141, e133, h2, pow_zero, e_add_self]
    have hf := hfour h0
    have b := fun n a heq => tb_holds_atom (C := C) (rd := Lm.read) (σ := σ) (kret := kret) rtFour_noRet hf n a heq
    have c261 := b 78 (.const (.n 261) (word 16384 0)) (by decide +kernel)
    have m262 := b 79 (.mul (.n 262) (.n 5) (.n 261)) (by decide +kernel)
    have l262 := b 80 (.load (.n 262) (.n 140) 5) (by decide +kernel)
    simp only [Atom.Holds] at c261 m262 l262
    rw [show (16384 : ℕ) = 2 ^ 14 by norm_num, tb_word_two_pow (by norm_num)] at c261
    rw [m262, c261] at l262
    simpa [h2] using l262
  · have hne : σ (.n 142) ≠ 0 := by
      rw [a142, c141, e133, h2, pow_one]
      intro h0
      have := gen_pow_inj (a := 1) (b := 0) (by omega) (by omega)
        ((pow_one gen).trans ((e_add_eq_zero_iff.mp h0).trans (pow_zero gen).symm))
      omega
    have hf := htwo hne
    have b := fun n a heq => tb_holds_atom (C := C) (rd := Lm.read) (σ := σ) (kret := kret) rtTwo_noRet hf n a heq
    have c353 := b 46 (.const (.n 353) (word 256 0)) (by decide +kernel)
    have m354 := b 47 (.mul (.n 354) (.n 5) (.n 353)) (by decide +kernel)
    have l354 := b 48 (.load (.n 354) (.n 140) 5) (by decide +kernel)
    simp only [Atom.Holds] at c353 m354 l354
    rw [show (256 : ℕ) = 2 ^ 8 by norm_num, tb_word_two_pow (by norm_num)] at c353
    rw [m354, c353] at l354
    simpa [h2] using l354

/-! ## Down from `verify_sub` -/

variable {r : Ref}

/-- **`verify_bus_gkr`'s cursor passes down from `verify_sub`.** -/
theorem vbgQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) VbgQ := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph _
    σ bufs kids hJt
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  obtain ⟨fn, hfn, hpar, -⟩ := hJv
  have hcf : c.f = name% «verify_bus_gkr» := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  -- the caller is `verify_sub`
  have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI)) hw c hc)
    (name% «verify_bus_gkr», name% «verify_sub») (by decide)
  have hnI := Da.fn_name_of_find hfI
  rw [hcf] at hcal
  simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
  have hvs : fI = name% «verify_sub» := by
    rcases hcal with h | ⟨h, hl⟩
    · rw [← hnI, h]
    · exfalso
      rw [hnI] at h
      subst h
      obtain rfl : fnI = fn% «verify_bus_gkr» := Option.some.inj (hfI.symm.trans find_vbg)
      rw [vbg_not_loop] at hl
      cases hl
  subst hvs
  obtain rfl : fnI = fn% «verify_sub» := Option.some.inj (hfI.symm.trans VerifySub.find_vs)
  obtain rfl : fn = fn% «verify_bus_gkr» := Option.some.inj (hfn.symm.trans find_vbg)
  -- its call of `verify_bus_gkr`
  have hs := Res.calls_sites (show Res.sitesB _ (fn% «verify_sub»).body = true by
    rw [VerifySub.vs_body]; exact vs_vbg_sites) hw c hc
  rw [hcf] at hs
  simp only [bne_self_eq_false, Bool.false_or, beq_iff_eq] at hs
  rw [hs, vbg_params] at hpar
  simp only [vbgArgsV, List.map_cons, List.map_nil, List.cons.injEq] at hpar
  obtain ⟨-, -, -, -, -, e5, -, -, -, e9, -⟩ := hpar
  -- its front
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
  obtain ⟨-, hb⟩ := Res.holds_of_valid gkr_hfs hv hfI
  rw [VerifySub.vs_body] at hb
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨hexp, hwin⟩ := carryQ_all hr I hI _ σI bufsI kidsI hIt _ hfI (name% «verify_sub», 4, .tab)
    (by decide) rfl (.n 4) (by rw [VerifySub.vs_params]; rfl)
  obtain ⟨⟨F⟩, -⟩ := VerifySub.vs_front (by omega) r.img (fun _ _ _ h ↦ Res.KidRel.rel h)
    (bytecode := List.replicate (2 ^ 23) 0) List.length_replicate hexp hwin hb
  rw [e5, e9, F.h320, F.h312, mul_assoc, ← pow_add]

/-- **`verify_bus_gkr`'s cursor at every honest instance.** -/
theorem vbgQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, VbgQ J := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  refine Res.insts_down (vbgQ_step hr) r.T _ r.hdr hv (fun J h ↦ h) (fun J rest he ↦ ?_)
  obtain ⟨J', rest', he', ht, -⟩ := head_insts (fs := B2C.fs) (lp := coreProgram.loop) (H := B2C.H) r.T
    (0, r.T.block B2C.fs coreProgram.loop) r.hdr
  rw [he'] at he
  obtain ⟨rfl, -⟩ := List.cons.inj he
  intro σ bufs kids hJt
  have hn := hr.name
  rw [← ht, hJt] at hn
  simp only [Tree.name] at hn
  exact absurd hn (by decide)

/-! ## Down from `verify_bus_gkr` -/

/-- **A layer slot's cursor passes down from `verify_bus_gkr`, and from one iteration to the next.** -/
theorem lyQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) (LyQ r) := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ hhdr hname hval hph hQI
    σ bufs kids hJt
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  obtain ⟨fn, hfn, hpar, -⟩ := hJv
  have hcf : c.f = name% «verify_bus_gkr_loop0» := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  obtain rfl : fn = fn% «verify_bus_gkr_loop0» := Option.some.inj (hfn.symm.trans find_ly)
  rw [ly_params] at hpar
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  -- the counter below the bound, at the callee
  suffices H : ∃ j m sh q, σ (.n 0) = gen ^ j ∧ σ (.n 1) = gen ^ m ∧ j ≤ m ∧ m ≤ 16 ∧ sh < 2 ∧
      σ (.n 2) = gen ^ (2 - sh) ∧ σ (.n 8) = gen ^ sh ∧
      LoadHolds r.img.read (σ (.n 3)) (10 * (2 * j + 2 - sh) + 5) (σ (.n 9) * gen ^ q) ∧
      q + 140 * (m - j) ≤ 8192 by
    obtain ⟨j, m, sh, q, h0, h1, hjm, h3, h4, h5, h6, h7, h8⟩ := H
    obtain ⟨j', hj', h0'⟩ := loop_ctr_lt hr hJS hJt find_ly ly_loop.1 ly_loop.2 ly_params h1 (by omega)
    obtain rfl : j = j' := gen_pow_inj (by omega) (by omega) (h0.symm.trans h0')
    exact ⟨j, m, sh, q, h0, h1, hj', h3, h4, h5, h6, h7, h8⟩
  -- the caller: `verify_bus_gkr`, or the loop's tail
  have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI))
    hw c hc) (name% «verify_bus_gkr_loop0», name% «verify_bus_gkr») (by decide)
  have hnI := Da.fn_name_of_find hfI
  rw [hcf] at hcal
  simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
  obtain ⟨-, hb⟩ := Res.holds_of_valid gkr_hfs hv hfI
  rcases hcal with hV | ⟨hS, hl⟩
  · -- `verify_bus_gkr`'s call
    obtain rfl : fI = name% «verify_bus_gkr» := hnI.symm.trans hV
    obtain rfl : fnI = fn% «verify_bus_gkr» := Option.some.inj (hfI.symm.trans find_vbg)
    have hs := Res.calls_sites vbg_ly_sites hw c hc
    rw [hcf] at hs
    simp only [bne_self_eq_false, Bool.false_or, beq_iff_eq] at hs
    rw [hs] at hpar
    simp only [lyArgsV, List.map_cons, List.map_nil, List.cons.injEq] at hpar
    obtain ⟨p0, p1, p2, p3, -, -, -, -, p8, p9, -⟩ := hpar
    rw [vbg_body, holdsList_append, holdsList_noRet _ vbgPre_noRet] at hb
    obtain ⟨d, hd, hg, e366, e135, e133, e369, hroot⟩ :=
      vbg_root_slot (by omega) r.img hb.1
    have e5 := vbgQ_all hr I hI σI bufsI kidsI hIt
    refine ⟨0, (d - 1) / 2, d % 2, 13 + (if d % 2 = 0 then 14 else 8), ?_, ?_, Nat.zero_le _, by omega,
      Nat.mod_lt _ (by norm_num), ?_, ?_, ?_, ?_⟩
    · rw [p0, e369, pow_zero]
    · rw [p1, e366]
    · rw [p2, e135]
    · rw [p8, e133]
    · rw [p3, p9]
      rw [e5, mul_assoc, ← pow_add] at hroot
      simpa using hroot
    · split <;> omega
  · -- the loop's tail call
    obtain rfl : fI = name% «verify_bus_gkr_loop0» := hnI.symm.trans hS
    obtain rfl : fnI = fn% «verify_bus_gkr_loop0» := Option.some.inj (hfI.symm.trans find_ly)
    obtain ⟨-, e0, -, hsh, -⟩ := progOk_guest.loop _ _ hfI hl
    obtain ⟨p0, prest, c0, i0, es1, hps, hw1, hes, hi0, -⟩ := Res.loop_path hsh hw hh
    subst hes
    have hnm : (fn% «verify_bus_gkr_loop0»).name = name% «verify_bus_gkr_loop0» := Da.fn_name_of_find find_ly
    rw [Res.loop_calls, hnm] at hci
    have hi : i = (calls es1).length := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · rw [List.getElem?_append_left hlt] at hci
        have hc1 := walk_callees (σ := σI) (loopBody (fn% «verify_bus_gkr_loop0»)) (c := c)
          (by rw [hw1]; exact List.mem_of_getElem? hci)
        rw [hcf] at hc1
        exact absurd hc1 (by decide +kernel)
      · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by simp; omega)] at hci
        cases hci
    subst hi
    rw [List.getElem?_append_right le_rfl, Nat.sub_self] at hci
    simp only [List.getElem?_singleton, ↓reduceIte, Option.some.injEq] at hci
    subst hci
    rw [ly_params] at hps
    obtain ⟨rfl, rfl⟩ := List.cons.inj hps
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar
    obtain ⟨p0, p1, p2, p3, -, -, -, -, p8, p9, -⟩ := hpar
    -- the iteration's slot and its next one
    obtain ⟨jI, m, sh, q, h0I, h1I, hjm, hm, hsh, h2I, h8I, hcurI, hroomI⟩ := hQI σI bufsI kidsI hIt
    rw [ly_body, holdsList_append, holdsList_noRet _ lyPre_noRet] at hb
    obtain ⟨-, -, -, -, hnext⟩ := ly_curs (fun _ _ _ h ↦ Res.KidRel.rel h) hb.1 (by omega) hsh h0I h2I h8I hcurI
    refine ⟨jI + 1, m, sh, q + (4 * (2 * jI + 2 - sh) + 12), ?_, by rw [p1, h1I], by omega, hm, hsh,
      by rw [p2, h2I], by rw [p8, h8I], ?_, by omega⟩
    · rw [p0, hi0, h0I, ← gen_pow_eq_ofK, ← pow_add]
    · rw [p3, p9, pow_add, ← mul_assoc, show 2 * (jI + 1) + 2 - sh = 2 * jI + 2 - sh + 2 by omega]
      exact hnext

/-- **A layer slot's cursor at every honest instance.** -/
theorem lyQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, LyQ r J := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  refine Res.insts_down (lyQ_step hr) r.T _ r.hdr hv (fun J h ↦ h) (fun J rest he ↦ ?_)
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
