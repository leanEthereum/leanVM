/-
  LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.ResM

  The gap walk's records at the honest instances: each frame loop and last claims of
  `child_claim_list_mono` linked to its caller's frame and to the records of the walk, carried down
  the honest tree.
-/

module

public import LeanVM.Guest.CoreMode.Fam.ResA
public import LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.MonoReplay
public import LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.MonoDefs
public import LeanVM.Guest.B1.Digest.ChildDigest
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«child_claim_list_digest»
import LeanVM.Guest.Data.ValNames.«child_claim_list_mono»
import LeanVM.Guest.Data.ValNames.«child_claim_list_mono_last__L0»

/-!
# The gap walk's records down the honest tree

`MonoQ M rd J`: an instance `J` of a frame loop of `child_claim_list_mono` has a header naming the
caller's frame `a` (`MonoHdr`: cell `5` holds `limit = g^L`), its counter `g^q` below its end
`g^n`, and every record `chain · g^(15 q')`, `q' ≤ n`, holding the walk's pointers into the
caller's region and entries (cells `3`, `2`) at an offset at most `L` (`RecAt`); an instance of its
last claims has the header, `limit` and `region` its parameters, `region ≠ 0`, and its record so; an
instance of `child_claim_list_mono` has a list of at least one claim (its counts not all `g^0`).

`monoQ_all`: at every honest instance (`MonoOk`, the checks), by `Res.insts_down`: called by
`child_claim_list_mono`, whose body holds at its own valuation (`Res.holds_of_valid`), the records
are `Res.mono_replay`'s, the header the call site's (`H_eq_kidHdr`), the cells the frame's
(`FrameHolds.val`), a loop's count at least one (`Res.loop_pos`); a frame loop's tail call keeps
the header and the records and steps the counter, below the end where the call is taken; called by
`child_claim_list_digest` on a nonempty list (`n_g ≠ 1`, the path past the empty list's branch,
`digest_zero_calls`), `child_claim_list_mono` gets `list_split`'s counts, not all `g^0`.

`nzVal_ml0`: the last claims' region is nonzero at every honest instance (`NzVal`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf FrameHolds fsN fn_of_idx cellJ namedOf kidHdr siteOf)
open LeanVM.Guest.Value (gen_pow_eq_ofK gen_pow_inj)
open LeanVM.Guest.B1.Digest (mlNames ml_idx ml_all mlOk find_of_idx mono136_idx mono17_idx)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

@[expose] public section

/-- **The caller's frame `a`**, named by the header, its cell `5` holding `g^L`. -/
def MonoHdr (M : ℕ → E) (J : Inst) (a L : ℕ) : Prop :=
  J.hdr.2 = ofK (addressOfIndex a) ∧ a + 5 < maxCells ∧ M (a + 5) = gen ^ L ∧ L < 2 ^ 33

/-- **The gap walk at an instance**: a frame loop's caller, counter and records; the last claims'
caller, bound, region and record. -/
def MonoQ (M : ℕ → E) (rd : Reader) (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids →
    ((f = name% «child_claim_list_mono_loop0» ∨ f = name% «child_claim_list_mono_loop1») →
      ∃ a L n q, MonoHdr M J a L ∧ σ (.n 0) = gen ^ q ∧ q < n ∧ n < 2 ^ 32 ∧ σ (.n 1) = gen ^ n ∧
        ∀ q' ≤ n, Res.RecAt rd (σ (.n 2) * gen ^ (15 * q')) (M (a + 3)) (M (a + 2)) L) ∧
    (f ∈ mlNames → ∃ a L, MonoHdr M J a L ∧ σ (.n 3) = gen ^ L ∧ σ (.n 1) = M (a + 3) ∧ σ (.n 1) ≠ 0 ∧
      Res.RecAt rd (σ (.n 0)) (M (a + 3)) (M (a + 2)) L) ∧
    (f = name% «child_claim_list_mono» → σ (.n 4) = 1 → σ (.n 5) = 1 → σ (.n 6) ≠ 1)

/-- `child_claim_list_digest` calls `child_claim_list_mono` at its arguments, and not on its empty
list's branch. -/
noncomputable def monoDigestB : Bool :=
  Res.sitesB (fun f args _ => f != name% «child_claim_list_mono» ||
      args == [.n (val% «child_claim_list_digest» "entries_ptr"), .n (val% «child_claim_list_digest» "region"), .n (val% «child_claim_list_digest» "base"), .n (val% «child_claim_list_digest» "limit_g"), .n (val% «child_claim_list_digest» "bigs"), .n (val% «child_claim_list_digest» "groups"), .n (val% «child_claim_list_digest» "rest")]) (Fn.body fn% «child_claim_list_digest») &&
    !(Stmt.blockCallees B1.Digest.cc25Zero).contains name% «child_claim_list_mono»

/-- **The gap walk's checks.** -/
structure MonoOk : Prop where
  idx : idxOf name% «child_claim_list_mono» = some fn_idx% «child_claim_list_mono»
  origin : Res.monoOriginB = true
  loop0 : Res.monoLoopB name% «child_claim_list_mono_loop0» = true
  loop1 : Res.monoLoopB name% «child_claim_list_mono_loop1» = true
  ml : Res.monoMlB = true
  digest : monoDigestB = true
  callers : ∀ fn ∈ coreProgram, Res.callersG Res.monoCallers fn = true

section

variable {r : Ref}

/-- Every honest instance's subtree within `2^28` words. -/
theorem inst_total (hr : r.Ok) :
    ∀ I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, I.t.total B2C.fs ≤ 2 ^ 28 := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  have hle := le_two_pow_logMem (r.T.total B2C.fs)
  have h28 : 2 ^ logMem (r.T.total B2C.fs) ≤ 2 ^ 28 :=
    Nat.pow_le_pow_right (by norm_num) (logMemorySize_le_28 (e := r.exec) hr.size)
  refine Res.insts_down (Res.insts_total Res.fs_pos _ _) r.T _ r.hdr hv (fun J h ↦ h) (fun J rest he ↦ ?_)
  obtain ⟨J', rest', he', ht, -⟩ := head_insts (fs := B2C.fs) (lp := coreProgram.loop) (H := B2C.H) r.T
    (0, r.T.block B2C.fs coreProgram.loop) r.hdr
  rw [he'] at he
  obtain ⟨rfl, -⟩ := List.cons.inj he
  rw [ht]
  omega

/-- An honest node is valid on the reference. -/
theorem inst_valid (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Core.Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) :
    ∃ args rets, (Memory.Tree.node f σ bufs kids).Valid coreProgram r.img.read args rets := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  rcases insts_good r.T _ r.hdr hv I hI with ⟨args, rets, hval⟩ | ⟨_, _, hph⟩
  · rw [ht] at hval; exact ⟨args, rets, hval⟩
  · rw [ht] at hph; cases hph

/-- A frame loop's facts. -/
theorem monoLoop_facts {f : String} (hf : f = name% «child_claim_list_mono_loop0» ∨
    f = name% «child_claim_list_mono_loop1») : ∃ j, coreProgram.indexOf? f = some j ∧
    (coreProgram.getD j default).loop = true ∧ Res.endOfFn (coreProgram.getD j default) = some none ∧
    (coreProgram.getD j default).params = [.n 0, .n 1, .n 2, .n 3] := by
  rcases hf with rfl | rfl
  · obtain ⟨h1, h2, h3, -⟩ := Res.loop0_facts
    exact ⟨_, mono136_idx, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3, -⟩ := Res.loop1_facts
    exact ⟨_, mono17_idx, h1, h2, h3⟩

/-- **The empty list's branch calls only its own callees**: on a path of
`child_claim_list_digest` with `n_g = 1`. -/
theorem digest_zero_calls {σ : Core.Val} {es : List Ev} {vs : List V}
    (hw : Memory.walk σ (Fn.body fn% «child_claim_list_digest») = .ret es vs) (h6 : σ (.n (val% «child_claim_list_digest» "s1#1")) = 0) {c : Call}
    (hc : c ∈ calls es) : c.f ∈ Stmt.blockCallees B1.Digest.cc25Zero := by
  have hc' : c ∈ calls (Memory.walk σ (Fn.body fn% «child_claim_list_digest»)).evs := by rw [hw]; exact hc
  rw [B1.Digest.child_claim_list_digest_shape] at hc'
  simp only [Memory.walk] at hc'
  rcases Out.calls_seq hc' with h | h
  · simp [walk1, Out.evs, calls, Ev.call?] at h
  rcases Out.calls_seq h with h | h
  · simp [walk1, Out.evs, calls, Ev.call?] at h
  rcases Out.calls_seq h with h | h
  · rw [walk1, Out.calls_pre_inK, ite_eq_left h6] at h
    exact walk_callees _ h
  rcases Out.calls_seq h with h | h
  · simp [walk1, Out.evs, calls, Ev.call?] at h
  rcases Out.calls_seq h with h | h
  · simp [walk1, Out.evs, calls, Ev.call?] at h
  rcases Out.calls_seq h with h | h
  · simp [walk1, Out.evs, calls, Ev.call?] at h
  · simp [Out.evs, calls] at h

/-- A call site of the walk's callees: its arguments, a site of the caller's plumbing. -/
theorem monoSite_of {o : ℕ} {f : String} {args rets : List V} (h : Res.monoSiteB o f args rets = true) :
    (f = name% «child_claim_list_mono_loop0» → args = [.n (val% «child_claim_list_mono» "s4#2"), .n (val% «child_claim_list_mono» "bigs"), .n (val% «child_claim_list_mono» "chain"), .n (val% «child_claim_list_mono» "base")]) ∧
    (f = name% «child_claim_list_mono_loop1» → args = [.n (val% «child_claim_list_mono» "s6#2"), .n (val% «child_claim_list_mono» "groups"), .n (val% «child_claim_list_mono» "mid"), .n (val% «child_claim_list_mono» "base")]) ∧
    (f ∈ mlNames → args = [.n (val% «child_claim_list_mono» "last"), .n (val% «child_claim_list_mono» "region"), .n (val% «child_claim_list_mono» "base"), .n (val% «child_claim_list_mono» "limit_g")]) ∧
    (f ∈ [name% «child_claim_list_mono_loop0», name% «child_claim_list_mono_loop1»] ++ mlNames →
      Res.siteB o args rets = true) := by
  simp only [Res.monoSiteB, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    beq_iff_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have hml : f ∈ mlNames → mlNames.contains f = true := fun hf ↦ List.contains_iff_mem.mpr hf
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_, fun hf ↦ ?_, fun hf ↦ ?_⟩
  · rcases h0 with h0 | h0
    · exact absurd hf h0
    · exact h0.1
  · rcases h1 with h1 | h1
    · exact absurd hf h1
    · exact h1.1
  · rcases h2 with h2 | h2
    · rw [hml hf] at h2; cases h2
    · exact h2.1
  · rcases List.mem_append.mp hf with hf | hf
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with hf | hf
      · rcases h0 with h0 | h0
        · exact absurd hf h0
        · exact h0.2
      · rcases h1 with h1 | h1
        · exact absurd hf h1
        · exact h1.2
    · rcases h2 with h2 | h2
      · rw [hml hf] at h2; cases h2
      · exact h2.2

/-- **The gap walk passes down a call.** -/
theorem monoQ_step (hO : MonoOk) (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
      (MonoQ (refMem r.img) r.img.read) := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ hhdr hname hval hph hQI
    f σ bufs kids hJt
  have hcf : c.f = f := by rw [← hname, hJt]; rfl
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  have hJv' := hJv
  obtain ⟨fn, hfn, hpar, -⟩ := hJv'
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  have hfnI : fnI ∈ coreProgram := List.mem_of_find?_eq_some hfI
  have hnI : fnI.name = fI := fn_name_of_find hfI
  have hJtot : (Memory.Tree.node f σ bufs kids).total B2C.fs ≤ 2 ^ 28 := by
    have := inst_total hr J hJS; rwa [hJt] at this
  have hcall : Res.monoCallers.all (fun p => p.1 != c.f || fnI.name == p.2 || (fnI.name == c.f && fnI.loop)) =
      true := Res.calls_sites (hO.callers fnI hfnI) hw c hc
  -- the callers of the walk's functions
  have hcallp : ∀ p ∈ Res.monoCallers, p.1 = f → fI = p.2 ∨ (fI = f ∧ fnI.loop = true) := fun p hp hpf ↦ by
    have := List.all_eq_true.mp hcall p hp
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.and_eq_true, hnI, hcf] at this
    rcases this with (h | h) | h
    · exact absurd hpf h
    · exact Or.inl h
    · exact Or.inr h
  have hcaller : f ∈ [name% «child_claim_list_mono_loop0», name% «child_claim_list_mono_loop1»] ++ mlNames →
      fI = name% «child_claim_list_mono» ∨ (fI = f ∧ fnI.loop = true) := fun hm ↦
    hcallp (f, name% «child_claim_list_mono») (List.mem_append_left _ (List.mem_map.mpr ⟨f, hm, rfl⟩)) rfl
  -- called by `child_claim_list_mono`: the replay, the header, the cells
  have hP : fI = name% «child_claim_list_mono» →
      f ∈ [name% «child_claim_list_mono_loop0», name% «child_claim_list_mono_loop1»] ++ mlNames →
      ∃ a b L, Res.monoSiteB fn_idx% «child_claim_list_mono» c.f c.args c.rets = true ∧
      MonoHdr (refMem r.img) J I.fp L ∧ refMem r.img (I.fp + 3) = σI (.n 1) ∧
      refMem r.img (I.fp + 2) = σI (.n 0) ∧
      σI (.n 4) = gen ^ a ∧ σI (.n 5) = gen ^ b ∧ a < 2 ^ 32 ∧ b < 2 ^ 32 ∧
      σI (.n 3) = gen ^ L ∧ σI (.n 32) = 1 ∧ σI (.n 42) = 1 ∧ σI (.n 49) = σI (.n 39) * gen ^ (15 * b) ∧
      (∀ q ≤ a, Res.RecAt r.img.read (σI (.n 16) * gen ^ (15 * q)) (σI (.n 1)) (σI (.n 0)) L) ∧
      (∀ q ≤ b, Res.RecAt r.img.read (σI (.n 39) * gen ^ (15 * q)) (σI (.n 1)) (σI (.n 0)) L) ∧
      (σI (.n 4) ≠ 1 ∨ σI (.n 5) ≠ 1 ∨ σI (.n 6) ≠ 1 → σI (.n 1) ≠ 0) := by
    intro hfI' hm
    subst hfI'
    have hj := hO.idx
    obtain ⟨i', hoi, hi', -, hf', hc', -⟩ := fn_of_idx hj
    obtain rfl : fnI = coreOf fn_idx% «child_claim_list_mono» := by
      rw [hc']; exact Option.some.inj (hfI.symm.trans hf')
    have hO' := hO.origin
    simp only [Res.monoOriginB, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq,
      Nat.blt_eq] at hO'
    obtain ⟨⟨⟨⟨⟨⟨⟨-, hloop⟩, hps⟩, hc0⟩, hc1⟩, hc3⟩, h5⟩, hsites⟩ := hO'
    have hs := Res.calls_sites hsites hw c hc
    obtain ⟨args, rets, hvI⟩ := inst_valid hr hI hIt
    obtain ⟨-, hbI⟩ := Res.holds_of_valid Res.fs_pos hvI B1.Digest.find_child_claim_list_mono
    have hT := inst_total hr I hI
    rw [hIt] at hT
    obtain ⟨a, b, L, ha, hb, ha', hb', hL', hL, h32, h42, h49, hra, hrb, hreg⟩ :=
      Res.mono_replay (ref_memOk hr) hT hbI
    -- the header
    obtain ⟨s, hs'⟩ : ∃ s, siteOf fn_idx% «child_claim_list_mono» c = some s :=
      Option.isSome_iff_exists.mp ((monoSite_of hs).2.2.2 (by rw [hcf]; exact hm))
    have hH := B2C.H_eq_kidHdr hIt hj hw i
    unfold kidHdr at hH
    rw [hci] at hH
    dsimp only at hH
    rw [ite_eq_right (by rw [hloop]; simp), hs'] at hH
    -- the cells
    have hfb := inst_fb hr hI (by rw [hIt]; rfl) hj
    have hF0 := inst_frame hr hI hIt hj hw
    have hval' : ∀ u ∈ (coreOf fn_idx% «child_claim_list_mono»).params, 2 ≤ cellJ fn_idx% «child_claim_list_mono» u →
        cellJ fn_idx% «child_claim_list_mono» u < fsN fn_idx% «child_claim_list_mono» →
        I.fp + cellJ fn_idx% «child_claim_list_mono» u < maxCells ∧
          refMem r.img (I.fp + cellJ fn_idx% «child_claim_list_mono» u) = σI u := fun u hu h2 hlt ↦
      ref_read hr (by omega) (hF0.val u (List.mem_append_left _ (List.mem_append_left _ hu)) h2 hlt)
    obtain ⟨-, hm0⟩ := hval' (.n 0) (by rw [hps]; simp) (by omega) (by omega)
    obtain ⟨-, hm1⟩ := hval' (.n 1) (by rw [hps]; simp) (by omega) (by omega)
    obtain ⟨hlt5, hm3⟩ := hval' (.n 3) (by rw [hps]; simp) (by omega) (by omega)
    rw [hc0] at hm0
    rw [hc1] at hm1
    rw [hc3] at hm3
    exact ⟨a, b, L, hs, ⟨by rw [hhdr, hH], hlt5, by rw [hm3, hL], hL'⟩, hm1, hm0, ha, hb, ha', hb', hL,
      h32, h42, h49, hra, hrb, hreg⟩
  refine ⟨fun hfl ↦ ?_, fun hfm ↦ ?_, fun hfo ↦ ?_⟩
  · -- a frame loop
    have hm : f ∈ [name% «child_claim_list_mono_loop0», name% «child_claim_list_mono_loop1»] ++ mlNames := by
      rcases hfl with rfl | rfl <;> simp
    obtain ⟨jf, hidx, hl, hend, hparf⟩ := monoLoop_facts hfl
    obtain rfl : fn = coreProgram.getD jf default := Option.some.inj (hfn.symm.trans (find_of_idx hidx))
    rcases hcaller hm with hfI' | ⟨hfe, hl'⟩
    · -- entered from `child_claim_list_mono`
      obtain ⟨a, b, L, hs, hH, h3, h2, ha, hb, ha', hb', hL, h32, h42, -, hra, hrb, -⟩ := hP hfI' hm
      have hsite := monoSite_of hs
      rw [hcf] at hsite
      rcases hfl with rfl | rfl
      · rw [hsite.1 rfl, hparf] at hpar
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
        obtain ⟨hp0, hp1, hp2, -⟩ := hpar
        have h1a := Res.loop_pos hidx hl hend hparf hJv hJtot (by rw [hp0, h32]) ha' (by rw [hp1, ha])
        refine ⟨I.fp, L, a, 0, hH, by rw [hp0, h32, pow_zero], h1a, ha', by rw [hp1, ha], fun q' hq' ↦ ?_⟩
        rw [hp2, h3, h2]
        exact hra q' hq'
      · rw [hsite.2.1 rfl, hparf] at hpar
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
        obtain ⟨hp0, hp1, hp2, -⟩ := hpar
        have h1b := Res.loop_pos hidx hl hend hparf hJv hJtot (by rw [hp0, h42]) hb' (by rw [hp1, hb])
        refine ⟨I.fp, L, b, 0, hH, by rw [hp0, h42, pow_zero], h1b, hb', by rw [hp1, hb], fun q' hq' ↦ ?_⟩
        rw [hp2, h3, h2]
        exact hrb q' hq'
    · -- a tail call
      subst hfe
      obtain rfl : coreProgram.getD jf default = fnI := Option.some.inj (hfn.symm.trans hfI)
      have hnc : ∀ x ∈ Stmt.blockCallees (loopBody (coreProgram.getD jf default)), ¬fI = x := by
        have h0 : Res.monoLoopB fI = true := by rcases hfl with rfl | rfl; exact hO.loop0; exact hO.loop1
        simp only [Res.monoLoopB, find_of_idx hidx, Bool.not_eq_true'] at h0
        intro x hx hfx
        subst hfx
        rw [List.contains_iff_mem.mpr hx] at h0
        cases h0
      obtain ⟨-, e0, he0, hsh, -⟩ := progOk_guest.loop fI _ hfI hl'
      obtain rfl : e0 = none := Option.some.inj (he0.symm.trans hend)
      obtain ⟨p0, prest, c0, i0, es1, hps, hw1, hes, hi0, hc0⟩ := Res.loop_path hsh hw hh
      subst hes
      have hnm : (coreProgram.getD jf default).name = fI := hnI
      rw [Res.loop_calls, hnm] at hci
      have hi : i = (calls es1).length := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · rw [List.getElem?_append_left hlt] at hci
          have hc1 := walk_callees (σ := σI) (loopBody (coreProgram.getD jf default)) (c := c)
            (by rw [hw1]; exact List.mem_of_getElem? hci)
          exact hnc _ hc1 hcf.symm
        · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by simp; omega)] at hci
          cases hci
      subst hi
      rw [List.getElem?_append_right le_rfl, Nat.sub_self] at hci
      simp only [List.getElem?_singleton, ↓reduceIte, Option.some.injEq] at hci
      subst hci
      obtain ⟨j, hj⟩ := B2C.idxOf_of_find hfI
      obtain ⟨i2, hji2, hi2, -, hf', hc', -⟩ := fn_of_idx hj
      have hcj : coreOf j = coreProgram.getD jf default := by rw [hc']; exact Option.some.inj (hf'.symm.trans hfI)
      have hH := B2C.H_eq_kidHdr hIt hj (by rw [hcj]; exact hw) (calls es1).length
      unfold kidHdr at hH
      rw [Res.loop_calls, hnm, List.getElem?_append_right le_rfl, Nat.sub_self] at hH
      simp only [List.getElem?_singleton, ↓reduceIte] at hH
      rw [ite_eq_left (show (coreOf j).loop = true ∧ _ from ⟨by rw [hcj]; exact hl', by simp⟩)] at hH
      rw [hparf] at hps
      obtain ⟨rfl, rfl⟩ := List.cons.inj hps
      rw [hparf] at hpar
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
      obtain ⟨hp0, hp1, hp2, -⟩ := hpar
      obtain ⟨a, L, n, q, ⟨hh2, ha5, hm5, hL⟩, hq0, hqn, hn, hn1, hrec⟩ := (hQI fI σI bufsI kidsI hIt).1 hfl
      have hne : σI c0 ≠ 0 := by simpa using hct
      rw [hc0, hq0] at hne
      simp only [Res.endVal, hparf, hn1] at hne
      have hq1 : q + 1 ≠ n := by
        rintro rfl
        apply hne
        rw [← gen_pow_eq_ofK, ← pow_add, CharTwo.add_self_eq_zero]
      refine ⟨a, L, n, q + 1, ⟨by rw [hhdr, hH, hh2], ha5, hm5, hL⟩, by rw [hp0, hi0, hq0, ← gen_pow_eq_ofK,
        ← pow_add], by omega, hn, by rw [hp1, hn1], fun q' hq' ↦ ?_⟩
      rw [hp2]
      exact hrec q' hq'
  · -- the last claims
    have hm : f ∈ [name% «child_claim_list_mono_loop0», name% «child_claim_list_mono_loop1»] ++ mlNames :=
      List.mem_append_right _ hfm
    obtain ⟨k, hk17, rfl⟩ : ∃ k, k < 17 ∧ mlNames.getD k "" = f := by
      obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hfm
      exact ⟨k, hk, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact he⟩
    obtain rfl : fn = coreProgram.getD (idx% «child_claim_list_mono_last__L0» + k) default :=
      Option.some.inj (hfn.symm.trans (find_of_idx (ml_idx k hk17)))
    have hmlk := ml_all k hk17
    simp only [mlOk, Bool.and_eq_true, decide_eq_true_eq] at hmlk
    have hparf := hmlk.1
    rcases hcaller hm with hfI' | ⟨hfe, hl'⟩
    · obtain ⟨a, b, L, hs, hH, h3, h2, -, -, -, -, hL, -, -, h49, -, hrb, hreg⟩ := hP hfI' hm
      have hsite := monoSite_of hs
      rw [hcf] at hsite
      rw [hsite.2.2.1 hfm, hparf] at hpar
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
      obtain ⟨hp0, hp1, -, hp3⟩ := hpar
      -- the caller's list is nonempty
      have hne := (hQI fI σI bufsI kidsI hIt).2.2 hfI'
      have hreg' : σI (.n 1) ≠ 0 := hreg (by
        by_cases h4 : σI (.n 4) = 1
        · by_cases h5 : σI (.n 5) = 1
          · exact Or.inr (Or.inr (hne h4 h5))
          · exact Or.inr (Or.inl h5)
        · exact Or.inl h4)
      refine ⟨I.fp, L, hH, by rw [hp3, hL], by rw [hp1, h3], by rw [hp1]; exact hreg', ?_⟩
      rw [hp0, h49, h3, h2]
      exact hrb b le_rfl
    · -- the last claims are no loops
      subst hfe
      have h0 := hO.ml
      simp only [Res.monoMlB, List.all_eq_true] at h0
      have := h0 _ hfm
      rw [hfI] at this
      simp [hl'] at this
  · -- `child_claim_list_mono`, called by `child_claim_list_digest` on a nonempty list
    subst hfo
    intro h4 h5 h6
    have hfnm : fn = fn% «child_claim_list_mono» :=
      Option.some.inj (hfn.symm.trans B1.Digest.find_child_claim_list_mono)
    rcases hcallp (name% «child_claim_list_mono», name% «child_claim_list_digest») (by simp [Res.monoCallers]) rfl
      with hfd | ⟨hfe, hl'⟩
    · subst hfd
      obtain rfl : fnI = fn% «child_claim_list_digest» :=
        Option.some.inj (hfI.symm.trans B1.Digest.find_child_claim_list_digest)
      have hD := hO.digest
      simp only [monoDigestB, Bool.and_eq_true, Bool.not_eq_true'] at hD
      obtain ⟨hDs, hDz⟩ := hD
      have hs := Res.calls_sites hDs hw c hc
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, hcf, not_true_eq_false, false_or] at hs
      rw [hs, hfnm, show (fn% «child_claim_list_mono»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] by
        decide +kernel] at hpar
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
      obtain ⟨-, -, -, -, hp4, hp5, hp6⟩ := hpar
      -- the path is past the empty list's branch
      have h6I : σI (.n 6) ≠ 0 := fun h0 ↦ by
        have := digest_zero_calls hw h0 hc
        rw [hcf] at this
        rw [List.contains_iff_mem.mpr this] at hDz
        cases hDz
      -- `list_split`'s counts
      obtain ⟨args, rets, hvI⟩ := inst_valid hr hI hIt
      obtain ⟨-, hbI⟩ := Res.holds_of_valid Res.fs_pos hvI B1.Digest.find_child_claim_list_digest
      rw [B1.Digest.child_claim_list_digest_shape] at hbI
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hbI
      obtain ⟨c5, a6, -, -, hnz⟩ := hbI
      obtain ⟨hsplit, -⟩ := hnz h6I
      obtain ⟨a, ha, b, hb, c', hc', hn, habc⟩ := B1.Digest.list_split_sound _ (ref_memOk hr) _ _ hsplit.rel
      simp only [List.cons.injEq, and_true] at habc
      obtain ⟨h15, h16, h17⟩ := habc
      simp only [B1.Digest.claimGroup, B1.Digest.bigGroups] at hb hc'
      have ha0 : a = 0 := gen_pow_inj (by omega) (by norm_num) (by rw [← h15, ← hp4, h4, pow_zero])
      have hb0 : b = 0 := gen_pow_inj (by omega) (by norm_num) (by rw [← h16, ← hp5, h5, pow_zero])
      have hc0 : c' = 0 := gen_pow_inj (by omega) (by norm_num) (by rw [← h17, ← hp6, h6, pow_zero])
      apply h6I
      rw [a6, c5, B1.word_one, hn, ha0, hb0, hc0]
      simp only [mul_zero, add_zero, pow_zero]
      exact CharTwo.add_self_eq_zero 1
    · -- `child_claim_list_mono` is no loop
      obtain rfl : fnI = fn% «child_claim_list_mono» := by
        rw [hfe] at hfI; exact Option.some.inj (hfI.symm.trans B1.Digest.find_child_claim_list_mono)
      exact absurd hl' (by decide +kernel)

/-- **The gap walk at every honest instance.** -/
theorem monoQ_all (hO : MonoOk) (hr : r.Ok) :
    ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, MonoQ (refMem r.img) r.img.read J := by
  refine insts_all hr (monoQ_step hO hr) fun J hm ↦ ?_
  intro f σ bufs kids hJt
  have hn := hm _ _ _ _ hJt
  subst hn
  refine ⟨fun h ↦ absurd h (by decide), fun h ↦ absurd h (by decide), fun h ↦ absurd h (by decide)⟩


/-- **The last claims' region at every honest instance of the empty rest** is nonzero. -/
theorem nzVal_ml0 (hO : MonoOk) : NzVal name% «child_claim_list_mono_last__L0» (.n (val% «child_claim_list_mono_last__L0» "region")) := by
  intro r hr I hI σ bufs kids ht
  obtain ⟨-, -, -, -, -, h, -⟩ := (monoQ_all hO hr I hI _ σ bufs kids ht).2.1 (by decide)
  exact h

end

end

end LeanVM.Guest.EndExec
