/-
  LeanVM.Guest.CoreMode.Fn.keccak_layer.Sound

  `keccak_layer`'s own routing facts and families, sound (`CoreMode/FnReg.lean`): its loops' cursors, its family.
-/

module

public import LeanVM.Guest.EndExecCoreRes
public import LeanVM.Guest.EndExecCoreSt
public import LeanVM.Guest.CoreMode.Fn.keccak_layer.ResStP
public import LeanVM.Guest.CoreMode.Fn.keccak_layer.ResStB
public import LeanVM.Guest.CoreMode.Fn.keccak_layer.ResStL
public import LeanVM.Guest.CoreMode.Fn.keccak_layer.Data
public import LeanVM.Guest.CoreMode.Fn.keccak_layer.Fam
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L»

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun CRes CIdx ResF LtF rep_of capE resFam idxC baseC vw csSub)

public section

/-! ## `keccak_layer`'s cursor -/

/-- **`keccak_layer__L{first}` at an honest instance** (`LayQ`, `layer_cur`): its pack rounds' words, its last record's
cursor `p + 48 + 2y` words into its stream, with room for `84 + 2y` words. -/
theorem layCur_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {v : ℕ} (hv : CoreMode.layCur fn = some v) :
    ∃ p y, σ (.n (valf% «keccak_layer» "step_g")) = Protocol.Verifier.gen ^ (y / B1.VerifySub.krStep) ∧
      σ (.n (valf% «keccak_layer» "rem_g")) = Protocol.Verifier.gen ^ (y % B1.VerifySub.krStep) ∧ y < 32 ∧
      σ (.n v) = σ (.n (valf% «keccak_layer» "stream")) * Protocol.Verifier.gen ^ (p + 48 + 2 * y) ∧ p + 84 + 2 * y ≤ 8192 := by
  have hn : ∃ first < 2, fn.name = B1.VerifySub.layerName first ∧ v = B1.VerifySub.layOff first + 743 := by
    simp only [CoreMode.layCur, Bool.cond_eq_ite, beq_iff_eq] at hv
    split_ifs at hv with h0 h1
    · exact ⟨0, by decide, h0, (Option.some.inj hv).symm⟩
    · exact ⟨1, by decide, h1, (Option.some.inj hv).symm⟩
  obtain ⟨first, hfi, hname, rfl⟩ := hn
  have hf' : f = B1.VerifySub.layerName first := by rw [← find_name' hf, hname]
  subst hf'
  obtain ⟨fL, hfL, hbL, -⟩ := layer_found hfi
  obtain rfl : fn = fL := Option.some.inj (hf.symm.trans hfL)
  obtain ⟨p, y, e7, hy, h9, h10, hroom⟩ := layQ_all hr I hI _ σ bufs kids ht first hfi rfl
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI ht
  have hfs : ∀ f', 1 ≤ B2C.fs f' := fun f' ↦ by
    unfold B2C.fs; split <;> simp [B2C.mainFrame, Data.mainCells, Data.jtSlots]
  obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv hf
  obtain ⟨hcur, -⟩ := layer_cur hfi (fun _ _ _ h ↦ Res.KidRel.rel h) hy h9 h10 hbL hb
  refine ⟨p, y, h9, h10, hy, ?_, by omega⟩
  rw [hcur, e7, mul_assoc, ← pow_add]
  ring_nf

/-- **`keccak_layer`'s family holds** at an honest instance (`layQC`): `LayQ` puts its cursor `p` words into its stream
with room for `84 + 2y` words and its pack rounds' words below `32`, its last record's cursor `48 + 2y` words past it
(`layer_cur`). -/
theorem layQC_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) : ∀ x : CRes, CoreMode.layQC fn x = true → x.Holds σ
  | .under gs r', h => fun _ ↦ layQC_inst hr hI ht hf r' h
  | .sub c q, h => by
    simp only [CoreMode.layQC, Bool.and_eq_true, decide_eq_true_eq, Option.any_eq_true] at h
    obtain ⟨⟨⟨v, hv, hcb⟩, hco⟩, rfl⟩ := h
    obtain ⟨p, y, -, -, -, hcur, hroom⟩ := layCur_inst hr hI ht hf hv
    have hcap : (8192 : ℕ) < CoreMode.capE := by rw [CoreMode.capE_eq]; norm_num
    refine ⟨0, 8192, p + 48 + 2 * y + c.off, CoreMode.rep_const (by rw [CoreMode.capE_eq]; norm_num),
      CoreMode.rep_const hcap, Nat.zero_le _, by omega, ?_⟩
    obtain ⟨cb, co⟩ := c
    simp only at hcb
    subst hcb
    simp only [CoreMode.CCell.addrW, CoreMode.CCell.valW, CoreMode.prodW, vw, pow_one, mul_one, one_mul, hcur,
      ← Value.gen_pow_eq_ofK, addressOfIndex]
    rw [mul_assoc, ← pow_add]
    ring_nf
  | .lt (.val x) (.num n), h => by
    simp only [CoreMode.layQC, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, decide_eq_true_eq,
      Option.isSome_iff_exists] at h
    obtain ⟨⟨⟨⟨v, hv⟩, hx⟩, hn⟩, hnc⟩ := h
    obtain ⟨p, y, h9, h10, hy, -⟩ := layCur_inst hr hI ht hf hv
    have hk : 0 < B1.VerifySub.krStep := by decide
    have h8 : B1.VerifySub.krStep ≤ 32 := by decide
    rcases hx with rfl | rfl
    · exact ltF_of_pow (e := y / B1.VerifySub.krStep) hnc (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
        (by rw [h9, Value.gen_pow_eq_ofK])
    · exact ltF_of_pow (e := y % B1.VerifySub.krStep) hnc (by have := Nat.mod_lt y hk; omega)
        (by rw [h10, Value.gen_pow_eq_ofK])
  | .lt (.val _) (.val _), h | .lt (.val _) (.mono _), h | .lt (.num _) _, h | .lt (.mono _) _, h
  | .nz _, h | .subR _ _, h | .subP _ _, h => by simp [CoreMode.layQC] at h

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun CRes stK stSub GlF setG setG_eq ownG ownG_setG prodW vw capE rep_of
  rep_const idxC baseC valW_baseC)
open LeanVM.Guest.Value (gen_pow_eq_ofK gen_pow_inj)
open LeanVM.Guest.B1 (loadHolds_unique)
open LeanVM.Guest.Res (topAtoms)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

/-- **The keccak layer's loops' cursors** in the stream: `LoopQ` and the iteration's record and load. -/
theorem st_keccak {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {first : ℕ} (hfi : first < 2) (rem : Bool) (hn : f = stLoop first rem) :
    ∃ a q, I.hdr.2 = ofK (addressOfIndex a) ∧ a + (2 + valf% «keccak_layer» "stream") < maxCells ∧
      σ (loopCur rem) = refMem r.img (a + (2 + valf% «keccak_layer» "stream")) * gen ^ q ∧ q + stStep rem ≤ 8192 := by
  obtain ⟨a, j, n, q, hhd, ha17, -, -, hjn, -, hld, hroom⟩ := loopQ_all hr I hI f σ bufs kids ht first hfi rem hn
  obtain ⟨args, rets, fn', hf', -, es0, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
  rw [hn] at hf
  obtain ⟨tm, tl⟩ := loop_atoms_top hfi rem hf
  have e6 : σ (.n (valf% «keccak_layer» "p1")) = σ (.n (valf% «keccak_layer» "fs2")) * σ (.n (valf% «keccak_layer» "fs0")) :=
    hh _ (topAtoms_on_path hw (List.contains_iff_mem.mp tm))
  have hl : LoadHolds r.img.read (σ (.n (valf% «keccak_layer» "p1"))) 80 (σ (loopCur rem)) :=
    hh _ (topAtoms_on_path hw (List.contains_iff_mem.mp tl))
  rw [e6] at hl
  exact ⟨a, q, hhd, ha17, loadHolds_unique hl hld, room_of hjn hroom⟩

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.CoreMode.Own.keccak_layer

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Protocol.Verifier (gen)

public section

/-- **Its loops' cursors** (`st_keccak`). -/
theorem stLoops_ok : ∀ c ∈ stLoops, StLoopOk c := by
  simp only [stLoops, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨⟨by decide, by unfold CoreMode.GB; decide, fun hr I hI σ bufs kids ht fn hf ↦
      st_keccak hr hI ht hf (first := 0) (by decide) false rfl⟩,
    ⟨by decide, by unfold CoreMode.GB; decide, fun hr I hI σ bufs kids ht fn hf ↦
      st_keccak hr hI ht hf (first := 1) (by decide) false rfl⟩,
    ⟨by decide, by unfold CoreMode.GB; decide, fun hr I hI σ bufs kids ht fn hf ↦
      st_keccak hr hI ht hf (first := 0) (by decide) true rfl⟩,
    ⟨by decide, by unfold CoreMode.GB; decide, fun hr I hI σ bufs kids ht fn hf ↦
      st_keccak hr hI ht hf (first := 1) (by decide) true rfl⟩⟩

/-- **Its family.** -/
theorem fams_ok : ∀ c ∈ fams, OwnOk c := by
  simp only [fams, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨fun hr I hI σ bufs kids ht fn hf x h ↦ layQC_inst hr hI ht hf x h,
    fun hr I hI σ bufs kids ht fn hf x h ↦ layQC_inst hr hI ht hf x h⟩

end

end LeanVM.Guest.CoreMode.Own.keccak_layer
