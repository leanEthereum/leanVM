/-
  LeanVM.Guest.CoreMode.Fn.hint_stream.HsCarry

  `hint_stream`'s chunk count at the honest instances of b2c's aligned tree (`expOkA_hs`), carried from `verify_sub`'s
  range check.
-/

module

public import LeanVM.Guest.EndExecExpCA
public import LeanVM.Guest.CoreMode.Fn.column_selector.CsChain
public import LeanVM.Guest.CoreMode.Fn.hint_stream.Data

/-!
# `hint_stream`'s chunk count, carried down

`hint_stream`'s only caller is `verify_sub` (`Own.hint_stream.stCallers`, the whole program's check
`Res.termCallers_all`), which passes as its `n_g` (parameter `1`) its `stream_chunks` (value `42`), range checked
below `g^32` (`assert log(stream_chunks) < STREAM_CAP // STREAM_CHUNK + 1`, the atom `rangeCheck 42 … 43`, `43` the
constant `g^32`).

`expOkA_hs`: `hint_stream`'s exponent fact (`Own.hint_stream.expFacts`) at every honest instance (`insts_allA`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **`hint_stream`'s chunk count at an instance**: `g^e`, `e < 33`. -/
def HsQ (J : Inst) : Prop :=
  ∀ σ bufs kids, J.t = .node name% «hint_stream» σ bufs kids → ∃ e < 33, σ (.n 1) = gen ^ e

end

public section

/-- `verify_sub` passes its `stream_chunks` as `hint_stream`'s `n_g`. -/
theorem vs_hs_sites : Res.sitesB (fun g args _ ↦ g != name% «hint_stream» || args[1]? == some (.n 42))
    (fn% «verify_sub»).body = true := by
  decide +kernel

theorem hs_facts : (fn% «hint_stream»).params[1]? = some (.n 1) ∧ (fn% «hint_stream»).loop = false := by
  decide +kernel

theorem find_hs : coreProgram.find? name% «hint_stream» = some fn% «hint_stream» :=
  coreProgram_find?_at (j := idx% «hint_stream») rfl

/-- `verify_sub`'s range check of `stream_chunks` and the constant `g^32` it is checked against. -/
theorem vs_hs_atoms : Atom.rangeCheck (.n 42) (.n 44) (.n 45) (.n 46) (.n 43) ∈ Res.topAtoms (fn% «verify_sub»).body ∧
    Atom.const (.n 43) (word (2 ^ 32) 0) ∈ Res.topAtoms (fn% «verify_sub»).body := by
  constructor <;> decide +kernel

end

section

variable {al : String → Bool} {D : Ref → RefD} {r : Ref}

public section

/-- **`HsQ` passes down a call**: from `verify_sub`'s range check of `stream_chunks`. -/
theorem hsQ_stepA (hR : RefH (layB al) (D r) r) (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (instsR al D r) HsQ := by
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
  have hcf : c.f = name% «hint_stream» := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  obtain rfl : fn = fn% «hint_stream» := Option.some.inj (hfn.symm.trans find_hs)
  obtain ⟨hp1, hpl⟩ := hs_facts
  -- the caller is `verify_sub`
  have hmem : (name% «hint_stream», name% «verify_sub») ∈ Res.termCallers :=
    CoreMode.FnReg.stCallers_of_hint_stream _ (by simp [CoreMode.Own.hint_stream.stCallers])
  have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI))
    hw c hc) _ hmem
  have hnI := find_name' hfI
  rw [hcf] at hcal
  simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
  have hvs : fI = name% «verify_sub» := by
    rcases hcal with h | ⟨h, hl⟩
    · rw [← hnI, h]
    · exfalso
      rw [hnI] at h
      subst h
      obtain rfl : fnI = fn% «hint_stream» := Option.some.inj (hfI.symm.trans find_hs)
      rw [hpl] at hl; cases hl
  subst hvs
  obtain rfl : fnI = fn% «verify_sub» := Option.some.inj (hfI.symm.trans find_vs)
  -- the site: `n_g` is `verify_sub`'s `stream_chunks`
  have hs := Res.calls_sites vs_hs_sites hw c hc
  rw [hcf] at hs
  simp only [bne_self_eq_false, Bool.false_or, beq_iff_eq] at hs
  have h1 : σ (.n 1) = σI (.n 42) := param_of hpar hp1 hs
  -- its range check
  have hrc : (Atom.rangeCheck (.n 42) (.n 44) (.n 45) (.n 46) (.n 43)).Holds r.img.read σI :=
    hh _ (topAtoms_on_path hw vs_hs_atoms.1)
  have h43 : (Atom.const (.n 43) (word (2 ^ 32) 0)).Holds r.img.read σI :=
    hh _ (topAtoms_on_path hw vs_hs_atoms.2)
  simp only [Atom.Holds] at hrc h43
  obtain ⟨e, he, hx⟩ := B1.Digest.rc_const (ref_memOkA hR hr) (c := 32) (by norm_num)
    (h43.trans (B1.word_two_pow (a := 32) (by norm_num))) hrc
  exact ⟨e, by omega, h1.trans hx⟩

/-- **`hint_stream`'s chunk count at every honest instance.** -/
theorem hsQ_allA (hR : RefH (layB al) (D r) r) (hr : r.Ok) : ∀ J ∈ instsR al D r, HsQ J := by
  refine insts_allA hR (hsQ_stepA hR hr) fun J hm ↦ ?_
  intro σ bufs kids hJt
  have hn := hm _ _ _ _ hJt
  exact absurd hn (by decide +kernel)

/-- **`hint_stream`'s exponent fact holds**, aligned (`HsQ`). -/
theorem expOkA_hs : ExpOkA al D (name% «hint_stream», 1, none, 33) := by
  intro r hR hr J hJ σ bufs kids hJt fn hf v hv
  obtain ⟨e, he, h⟩ := hsQ_allA hR hr J hJ σ bufs kids hJt
  obtain rfl := Option.some.inj (hf.symm.trans find_hs)
  rw [hs_facts.1] at hv
  obtain rfl : v = .n 1 := by simpa using hv.symm
  exact ⟨e, he, h⟩

end

end

end LeanVM.Guest.EndExec
