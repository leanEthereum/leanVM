/-
  LeanVM.Guest.EndExecCoreResAll

  A heap certificate's residuals of families sound at the honest instances: the generic families
  (`EndExecCoreRes`) and each function's own, by the registries' soundness (`Gen/FnSound.lean`).
-/

module

public import LeanVM.Guest.EndExecCoreRes
public import LeanVM.Guest.EndExecCoreSt
public import LeanVM.Guest.CoreMode.CoreResG
public import LeanVM.Guest.CoreMode.Gen.FnSound

/-!
# The residual families, sound, the functions' own among them

`expQ_all`, `dimQ_all`, `expVQ_all`: the listed exponent, dimension and value facts at every honest instance, each
proved by its function (`FnReg.expFacts_ok`, …). `resQ_inst`: the `expQ` and `dim` families from them. `st_inst`: a
stream-cursor loop's reads past its cursor, from its function's `StLoopOk` (`FnReg.stLoops_ok`). `resOk_inst`,
`resOk_instG`: every residual of a heap certificate whose residuals are of families (`CoreMode.resOk`): the generic
families' (`resFam_inst`, `resQ_inst`, `rcPts_inst`, `rcTab_inst`), the function's own (`FnReg.fams_ok`,
`FnReg.gwFams_ok`), and the ghost families' as given.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun CRes CIdx ResF LtF rep_of capE resFam resOk idxC baseC vw stK stSub setG)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

variable {r : Ref}

/-- **The listed exponent facts at every honest instance** (`FnReg.expFacts_ok`). -/
theorem expQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, ExpQ r J := by
  intro J hJ f σ bufs kids hJt fn hf c hc hcf v hv
  subst hcf
  exact CoreMode.FnReg.expFacts_ok c hc hr J hJ σ bufs kids hJt fn hf v hv

/-- **The listed dimension facts at every honest instance** (`FnReg.dimFacts_ok`). -/
theorem dimQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, DimQ r J := by
  intro J hJ f σ bufs kids hJt fn hf c hc hcf vk vb hvk hvb
  subst hcf
  exact CoreMode.FnReg.dimFacts_ok c hc hr J hJ σ bufs kids hJt fn hf vk vb hvk hvb

/-- **The listed values' facts at every honest instance** (`FnReg.expVals_ok`). -/
theorem expVQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, ExpVQ J := by
  intro J hJ f σ bufs kids hJt c hc hcf
  subst hcf
  exact CoreMode.FnReg.expVals_ok c hc hr J hJ σ bufs kids hJt

/-- **The `expQ` and `dim` families hold at an honest instance**: the listed facts, each its function's own. -/
theorem resQ_inst (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {x : CRes} (h : CoreMode.resQ fn x = true) : x.Holds σ := by
  obtain ⟨args, rets, fn', hf', -, es, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
  have hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds r.img.read σ := fun a ha ↦ hh _ (topAtoms_on_path hw ha)
  exact resQ_sound (expVQ_all hr I hI) (expQ_all hr I hI) (dimQ_all hr I hI) ht hf hall x h

/-- **The stream-cursor family at an honest instance**: its header names its caller's frame `a`, its reads past its
cursor lie in the stream at the caller's cell `D`, its ghost words that stream and the frame's address (`StLoopOk`, its
function's own). -/
theorem st_inst (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {D v S : ℕ} (hk : stK fn = some (D, v, S)) :
    ∃ a, I.hdr.2 = ofK (addressOfIndex a) ∧ a + D < maxCells ∧
      ∀ x, stSub fn x = true → x.Holds (setG σ [refMem r.img (a + D), ofK (Parameters.g ^ a)]) := by
  have hname : fn.name = f := find_name' hf
  obtain ⟨-, hv, hst⟩ := CoreMode.FnReg.stLoops_ok _ (CoreMode.lookup_memL hk)
  rw [hname] at hst
  obtain ⟨a, q, hhd, ha, hcur, hroom⟩ := hst hr I hI σ bufs kids ht fn hf
  exact ⟨a, hhd, ha, stSub_holds hk hv hcur hroom⟩

/-- **A stream-cursor loop's caller's cell is not its header's** (`StLoopOk`). -/
theorem stK_D {fn : Fn} {D v S : ℕ} (hk : stK fn = some (D, v, S)) : D ≠ 0 :=
  (CoreMode.FnReg.stLoops_ok _ (CoreMode.lookup_memL hk)).1

/-- **A function's own family holds** at an honest instance (`FnReg.fams_ok`). -/
theorem ownFam_inst (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {x : CRes} (h : CoreMode.ownFam fn x = true) : x.Holds σ := by
  obtain ⟨p, hp, hpx⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at hpx
  obtain ⟨hn, hx⟩ := hpx
  have hn' : p.1 = f := hn ▸ find_name' hf
  subst hn'
  exact CoreMode.FnReg.fams_ok p hp hr I hI σ bufs kids ht fn hf x hx

/-- **A function's own family over its own parameter words holds** at a valuation agreeing below `GB` with an honest
instance's, its ghosts those words (`FnReg.gwFams_ok`). -/
theorem gwFam_inst (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {σ' : Val} (hag : ∀ v : V, v.idx < CoreMode.GB → σ' v = σ v)
    (hng : CoreMode.ngB fn = true) {G : CoreMode.HSig} (hgw : CoreMode.GwR r.img G σ') {x : CRes}
    (h : CoreMode.gwFam fn G.gw x = true) : x.Holds σ' := by
  simp only [CoreMode.gwFam, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  obtain ⟨p, hp, hpx⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at hpx
  obtain ⟨hn, hx⟩ := hpx
  have hn' : p.1 = f := hn ▸ find_name' hf
  subst hn'
  exact CoreMode.FnReg.gwFams_ok p hp hr I hI σ bufs kids ht fn hf σ' hag hng G hgw x hx

/-- **The residuals of a heap certificate of families hold** at an honest instance of its function, in
a frame holding its parameters whose entry runs' exponent cells are powers of `g`. -/
theorem resOk_inst (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {Cf : CFun}
    (hf : coreProgram.find? f = some Cf.fn) (h : resOk Cf = true) (hml : CoreMode.mlK Cf.fn = none)
    (hst : CoreMode.stK Cf.fn = none) (hcm : CoreMode.cmK Cf.fn = none) (hgw : Cf.H.sig.gw = []) {fp : ℕ}
    (hpar : ∀ k < Cf.fn.params.length, CoreMode.Rd r.img fp (2 + k) = some (σ (V.n k)))
    (hx : CoreMode.ExpW r.img Cf.xc fp) : ResF Cf.H σ := fun x hx' ↦ by
  have := List.all_eq_true.mp h x hx'
  simp only [CoreMode.resFamG, Bool.or_eq_true, Bool.and_eq_true] at this
  rcases this with (((⟨((((hf' | hq) | hrc) | htb) | hown), -⟩ | hm) | hs) | hc) | he
  · exact resFam_inst hr hI ht hf hx hpar x hf'
  · exact resQ_inst hr hI ht hf hq
  · exact rcPts_inst hr hI ht hf hrc
  · exact rcTab_inst hr hI ht hf x htb
  · exact ownFam_inst hr hI ht hf hown
  · cases x <;> simp [CoreMode.mlSub, hml] at hm
  · cases x <;> simp [CoreMode.stSub, hst] at hs
  · rw [CoreMode.cmSub_none hcm] at hc; cases hc
  · rw [hgw, CoreMode.gwFam_nil] at he; cases he

/-- **The residuals of a heap certificate of families hold** at a valuation `σ'` agreeing below `GB` with an honest
instance's, given its ghost families' (`mlSub`, `stSub`, `cmSub`, `gwFam`): the others name no ghost
(`CRes.holds_congr`). -/
theorem resOk_instG (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {Cf : CFun}
    (hf : coreProgram.find? f = some Cf.fn) (h : resOk Cf = true) {fp : ℕ}
    (hpar : ∀ k < Cf.fn.params.length, CoreMode.Rd r.img fp (2 + k) = some (σ (V.n k)))
    (hx : CoreMode.ExpW r.img Cf.xc fp) {σ' : Val}
    (hag : ∀ m < CoreMode.GB, σ' (V.n m) = σ (V.n m)) (hml : ∀ x, CoreMode.mlSub Cf.fn x = true → x.Holds σ')
    (hst : ∀ x, CoreMode.stSub Cf.fn x = true → x.Holds σ')
    (hcm : ∀ x, CoreMode.cmSub Cf.fn x = true → x.Holds σ')
    (hvx : ∀ x, CoreMode.gwFam Cf.fn Cf.H.sig.gw x = true → x.Holds σ') :
    ResF Cf.H σ' := fun x hx' ↦ by
  have := List.all_eq_true.mp h x hx'
  simp only [CoreMode.resFamG, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at this
  rcases this with (((⟨((((hf' | hq) | hrc) | htb) | hown), hv⟩ | hm) | hs) | hc) | he
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (resFam_inst hr hI ht hf hx hpar x hf')
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (resQ_inst hr hI ht hf hq)
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (rcPts_inst hr hI ht hf hrc)
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (rcTab_inst hr hI ht hf x htb)
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (ownFam_inst hr hI ht hf hown)
  · exact hml x hm
  · exact hst x hs
  · exact hcm x hc
  · exact hvx x he

end

end LeanVM.Guest.EndExec
