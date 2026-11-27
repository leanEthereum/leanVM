/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.Sound

  `verify_sub`'s own routing facts and families, sound (`CoreMode/FnReg.lean`): its exponent family.
-/

module

public import LeanVM.Guest.EndExecCoreRes
public import LeanVM.Guest.CoreMode.Fn.verify_sub.ResVs
public import LeanVM.Guest.CoreMode.Fn.verify_sub.Fam
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun CRes CIdx ResF LtF rep_of capE resFam idxC baseC vw csSub)

public section

/-- `verify_sub`'s exponents by value, from its values (`vs_valsI`). -/
def vsE (hs : List ℕ) (d n sl : ℕ) (v : ℕ) : ℕ :=
  if v = val% «verify_sub» "kb[2]" then hs.getD 0 0 else if v = val% «verify_sub» "kb[3]" then hs.getD 1 0
  else if v = val% «verify_sub» "kb[4]" then hs.getD 2 0 else if v = val% «verify_sub» "kb[5]" then hs.getD 3 0
  else if v = val% «verify_sub» "kb[6]" then hs.getD 4 0 else if v = val% «verify_sub» "kb[7]" then hs.getD 5 0
  else if v = val% «verify_sub» "tau_keccak_g" then hs.getD 5 0 else if v = val% «verify_sub» "g_bus_mu" then d
  else if v = val% «verify_sub» "g_zc_n" then n else if v = val% «verify_sub» "gmv" then sl else sl - 20

/-- **`verify_sub`'s exponents** (`vsPows`, `vsLes`): each listed value `g^(E v)` within its bounds, the orders, the
cursors. -/
theorem vs_exps {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node name% «verify_sub» σ bufs kids)
    (hall : ∀ a ∈ Res.topAtoms (fn% «verify_sub»).body, a.Holds r.img.read σ) :
    ∃ E : ℕ → ℕ, (∀ v lo hi, (v, lo, hi) ∈ CoreMode.vsPows → lo ≤ E v ∧ E v ≤ hi ∧
        σ (V.n v) = Protocol.Verifier.gen ^ E v) ∧
      (∀ x y c, (x, y, c) ∈ CoreMode.vsLes → E x ≤ E y + c) ∧
      ∃ gK, (∀ x ∈ CoreMode.vsCurs, ∃ gX ≤ gK, σ (V.n x) = σ (.n (val% «verify_sub» "stream")) * Protocol.Verifier.gen ^ gX) ∧
        gK + 207 ≤ 8192 := by
  obtain ⟨hs, lm, sl, d, n, gG, gT, gK, hsL, hs31, hτ9, hτ24, hrd, hsl20, hsl30, e278, e276, hd20, hd34, e253,
    hτn, hnd, e579, e567, e578, e595, hGT, hTK, hroom⟩ := vs_valsI hr hI ht
  -- the dims' words, read at `dims_g`'s cells by the top-level loads
  have hld : ∀ v t, Atom.load (.n v) (.n (val% «verify_sub» "dims_g")) (t + 1) ∈ Res.topAtoms (fn% «verify_sub»).body → t < 6 →
      σ (.n v) = Protocol.Verifier.gen ^ hs.getD t 0 := by
    intro v t hm ht6
    have hx : (Atom.load (.n v) (.n (val% «verify_sub» "dims_g")) (t + 1)).Holds r.img.read σ := hall _ hm
    have hy := hrd (t + 1) (by simp [hsL]; omega)
    have := loadHolds_det hx hy
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show t < hs.length by omega)]
  have hm : ([(val% «verify_sub» "kb[2]", 0), (val% «verify_sub» "kb[3]", 1), (val% «verify_sub» "kb[4]", 2), (val% «verify_sub» "kb[5]", 3), (val% «verify_sub» "kb[6]", 4),
      (val% «verify_sub» "kb[7]", 5), (val% «verify_sub» "tau_keccak_g", 5)] : List (ℕ × ℕ)).all
      (fun p ↦ (Res.topAtoms (fn% «verify_sub»).body).contains (Atom.load (.n p.1) (.n (val% «verify_sub» "dims_g")) (p.2 + 1))) = true := by
    decide +kernel
  have hm' : ∀ v t, (v, t) ∈ ([(val% «verify_sub» "kb[2]", 0), (val% «verify_sub» "kb[3]", 1), (val% «verify_sub» "kb[4]", 2), (val% «verify_sub» "kb[5]", 3), (val% «verify_sub» "kb[6]", 4),
      (val% «verify_sub» "kb[7]", 5), (val% «verify_sub» "tau_keccak_g", 5)] : List (ℕ × ℕ)) →
      t < 6 → σ (.n v) = Protocol.Verifier.gen ^ hs.getD t 0 := fun v t hvt ht6 ↦
    hld v t (List.contains_iff_mem.mp (List.all_eq_true.mp hm (v, t) hvt)) ht6
  have h31 : ∀ t < 6, hs.getD t 0 < 31 := fun t ht ↦
    hs31 _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  refine ⟨vsE hs d n sl, fun v lo hi hv ↦ ?_, fun x y c hl ↦ ?_, gK, fun x hx ↦ ?_, hroom⟩
  · simp only [CoreMode.vsPows, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hv
    rcases hv with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨Nat.zero_le _, by have := h31 0 (by omega); show hs.getD 0 0 ≤ 30; omega,
        hm' (val% «verify_sub» "kb[2]") 0 (by simp) (by omega)⟩
    · exact ⟨Nat.zero_le _, by have := h31 1 (by omega); show hs.getD 1 0 ≤ 30; omega,
        hm' (val% «verify_sub» "kb[3]") 1 (by simp) (by omega)⟩
    · exact ⟨Nat.zero_le _, by have := h31 2 (by omega); show hs.getD 2 0 ≤ 30; omega,
        hm' (val% «verify_sub» "kb[4]") 2 (by simp) (by omega)⟩
    · exact ⟨Nat.zero_le _, by have := h31 3 (by omega); show hs.getD 3 0 ≤ 30; omega,
        hm' (val% «verify_sub» "kb[5]") 3 (by simp) (by omega)⟩
    · exact ⟨Nat.zero_le _, by have := h31 4 (by omega); show hs.getD 4 0 ≤ 30; omega,
        hm' (val% «verify_sub» "kb[6]") 4 (by simp) (by omega)⟩
    · exact ⟨show 9 ≤ hs.getD 5 0 by omega, show hs.getD 5 0 ≤ 24 by omega, hm' (val% «verify_sub» "kb[7]") 5 (by simp) (by omega)⟩
    · exact ⟨show 9 ≤ hs.getD 5 0 by omega, show hs.getD 5 0 ≤ 24 by omega, hm' (val% «verify_sub» "tau_keccak_g") 5 (by simp) (by omega)⟩
    · exact ⟨show 20 ≤ d by omega, show d ≤ 33 by omega, e253⟩
    · exact ⟨show 9 ≤ n by omega, show n ≤ 33 by omega, e579⟩
    · exact ⟨show 20 ≤ sl by omega, show sl ≤ 30 by omega, e276⟩
    · exact ⟨Nat.zero_le _, show sl - 20 ≤ 10 by omega, e278⟩
  · simp only [CoreMode.vsLes, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hl
    rcases hl with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · show hs.getD 5 0 ≤ n + 0; omega
    · show hs.getD 5 0 ≤ n + 0; omega
    · show sl ≤ sl - 20 + 20; omega
  · simp only [CoreMode.vsCurs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨gG, by omega, e567⟩
    · exact ⟨gT, by omega, e578⟩
    · exact ⟨gK, le_rfl, e595⟩

/-- `verify_sub`'s index as its value times `g^c` (`vsBase`): its word's exponent plus `c`. -/
theorem vsBase_rep {σ : Val} (hM : σ (.n (val% «verify_sub» "size_sel")) = σ (.n (val% «verify_sub» "gmv")) * σ (.n (val% «verify_sub» "size_sel~0"))) {i : CIdx} {x c : ℕ}
    (h : CoreMode.vsBase i = some (x, c)) {e : ℕ} (hσ : σ (V.n x) = Protocol.Verifier.gen ^ e) (hc : e + c < capE) :
    CoreMode.rep ((idxC i).valW (vw σ)) = some (e + c) := by
  cases i with
  | num n => simp [CoreMode.vsBase] at h
  | val v =>
    simp only [CoreMode.vsBase, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact rep_val_gen hσ (by omega)
  | mono m =>
    obtain ⟨cb, o⟩ := m
    simp only [CoreMode.vsBase] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact rep_mono_gen hσ hc
    · rename_i a b
      obtain ⟨x', hx', hxe⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at hxe
      obtain ⟨rfl, rfl⟩ := hxe
      have hm := CoreMode.lookup_memL hx'
      simp only [CoreMode.vsMuls, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hm
      have := rep_mono_gen (c := o) (x := val% «verify_sub» "size_sel") hσ hc
      simpa [idxC, CoreMode.CCell.valW, CoreMode.prodW, vw, hM, mul_assoc] using this
    · cases h

/-- **`verify_sub`'s exponent family holds** at an honest instance (`vsExp`). -/
theorem vsExp_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) : ∀ x : CRes, CoreMode.vsExp fn x = true → x.Holds σ
  | .under gs r', h => fun _ ↦ vsExp_inst hr hI ht hf r' h
  | .lt a b, h => by
    simp only [CoreMode.vsExp, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hn, h⟩ := h
    have hf' : f = name% «verify_sub» := by rw [← find_name' hf, hn]
    subst hf'
    obtain rfl : fn = fn% «verify_sub» := Option.some.inj (hf.symm.trans B1.VerifySub.find_vs)
    obtain ⟨args, rets, fn', hf'', -, es, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
    obtain rfl : fn% «verify_sub» = fn' := Option.some.inj (B1.VerifySub.find_vs.symm.trans hf'')
    have hall : ∀ a ∈ Res.topAtoms (fn% «verify_sub»).body, a.Holds r.img.read σ :=
      fun a ha ↦ hh _ (topAtoms_on_path hw ha)
    obtain ⟨E, hP, hL, -⟩ := vs_exps hr hI ht hall
    have hM : σ (.n (val% «verify_sub» "size_sel")) = σ (.n (val% «verify_sub» "gmv")) * σ (.n (val% «verify_sub» "size_sel~0")) :=
      hall (.mul (.n (val% «verify_sub» "size_sel")) (.n (val% «verify_sub» "gmv")) (.n (val% «verify_sub» "size_sel~0"))) (by decide +kernel)
    -- an index's exponent, within its bounds
    have hiv : ∀ i l h', CoreMode.vsIv i = some (l, h') → h' < capE → ∃ y, l ≤ y ∧ y ≤ h' ∧
        CoreMode.rep ((idxC i).valW (vw σ)) = some y ∧ ∀ x c, CoreMode.vsBase i = some (x, c) → y = E x + c := by
      intro i l h' hi hc
      cases i with
      | num n =>
        simp only [CoreMode.vsIv, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        exact ⟨_, le_rfl, le_rfl, CoreMode.rep_const hc, fun x c hb ↦ by simp [CoreMode.vsBase] at hb⟩
      | _ =>
        simp only [CoreMode.vsIv] at hi
        obtain ⟨⟨x, c⟩, hb, hp⟩ := Option.bind_eq_some_iff.mp hi
        obtain ⟨⟨lo, hi'⟩, hl, he⟩ := Option.map_eq_some_iff.mp hp
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨h1, h2, hσ⟩ := hP x lo hi' (CoreMode.lookup_memL hl)
        exact ⟨E x + c, by omega, by omega, vsBase_rep hM hb hσ (by omega),
          fun x' c' hb' ↦ by rw [hb] at hb'; cases hb'; rfl⟩
    simp only [CoreMode.vsLt] at h
    split at h
    · rename_i la ha lb hb hia hib
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
      obtain ⟨⟨hca, hcb⟩, h⟩ := h
      obtain ⟨ya, -, hya, hra, hea⟩ := hiv a _ _ hia hca
      obtain ⟨yb, hyb, -, hrb, heb⟩ := hiv b _ _ hib hcb
      refine ⟨ya, yb, hra, hrb, ?_⟩
      rcases h with h | h
      · omega
      · split at h
        · rename_i x ca y cb hba hbb
          obtain ⟨⟨lx, ly, lc⟩, hl, hle⟩ := List.any_eq_true.mp h
          simp only [decide_eq_true_eq] at hle
          obtain ⟨rfl, rfl, hlt⟩ := hle
          have := hL _ _ _ hl
          rw [hea _ _ hba, heb _ _ hbb]
          omega
        · cases h
    · cases h
  | .sub c q, h => by
    simp only [CoreMode.vsExp, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hn, rfl⟩, hcx⟩, hco⟩ := h
    have hf' : f = name% «verify_sub» := by rw [← find_name' hf, hn]
    subst hf'
    obtain rfl : fn = fn% «verify_sub» := Option.some.inj (hf.symm.trans B1.VerifySub.find_vs)
    obtain ⟨args, rets, fn', hf'', -, es, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
    obtain rfl : fn% «verify_sub» = fn' := Option.some.inj (B1.VerifySub.find_vs.symm.trans hf'')
    have hall : ∀ a ∈ Res.topAtoms (fn% «verify_sub»).body, a.Holds r.img.read σ :=
      fun a ha ↦ hh _ (topAtoms_on_path hw ha)
    obtain ⟨E, -, -, gK, hC, hroom⟩ := vs_exps hr hI ht hall
    obtain ⟨cb, k⟩ := c
    simp only at hcx hco
    split at hcx
    · rename_i x
      obtain ⟨gX, hgX, hσ⟩ := hC x (List.contains_iff_mem.mp hcx)
      refine (CoreMode.runSet_const (q := ⟨⟨[(val% «verify_sub» "stream", 1)], 0⟩, 1, .num 0, .num 8192⟩) rfl rfl (by norm_num)
        (by norm_num)).mpr ⟨gX + k, Nat.zero_le _, by omega, ?_⟩
      simp only [CoreMode.CCell.addrW, CoreMode.CCell.valW, CoreMode.prodW, vw, pow_one, mul_one, hσ,
        Value.gen_pow_eq_ofK, addressOfIndex, pow_zero, one_mul, pow_add, LeanVM.Parameters.ofK_mul,
        show ofK (1 : Parameters.K) = 1 from map_one (algebraMap Parameters.K Parameters.E), mul_one, mul_assoc]
    · cases hcx
  | .nz _, h | .subR _ _, h | .subP _ _, h => by simp [CoreMode.vsExp] at h

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.CoreMode.Own.verify_sub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Protocol.Verifier (gen)

public section

/-- **Its family.** -/
theorem fams_ok : ∀ c ∈ fams, OwnOk c := by
  simp only [fams, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact fun hr I hI σ bufs kids ht fn hf x h ↦ vsExp_inst hr hI ht hf x h

end

end LeanVM.Guest.CoreMode.Own.verify_sub
