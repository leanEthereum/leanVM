/-
  LeanVM.Guest.EndExecCoreMono

  The core route's ghost family at the honest instances: `child_claim_list_mono_last__L{k}`, its ghost
  word its caller's entries table, its reads in that table (the old route's gap walk on names).
-/

module

public import LeanVM.Guest.EndExecRMR
public import LeanVM.Guest.EndExecCoreLink

/-!
# The ghost family, sound

`ml_inst`: at an honest instance of `child_claim_list_mono_last__L{k}`, `1 ≤ k < 17` (`mlK`), its header names
its caller's frame `a` (`monoQ_all`), whose cell `5` holds its parameter `limit = g^L`; with its ghost word the
caller's cell `2` (`setG σ [M (a + 2)]`), each read of the family (`mlSub`) lies in the caller's table: the record
gives the entries pointer `M (a + 2) · g^(4 O)` (`RecAt`), the gaps add `4 Σ e_i` (`monoWalk_vals`), and the range
check of the walk's end bounds `O + Σ e_i + k` below `L` (as `mlRead`). `mlGlF`: its linked cells hold.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun CRes mlK mlSub GlF setG setG_eq ownG ownG_setG prodW vw capE rep_of
  rep_const idxC baseC valW_baseC)
open LeanVM.Guest.Value (gen_pow_eq_ofK gen_pow_inj)
open LeanVM.Guest.B1 (loadHolds_unique word_two_pow)
open LeanVM.Guest.B1.Digest
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

theorem mlK_spec {fn : Fn} {k : ℕ} (h : mlK fn = some k) : 1 ≤ k ∧ k < 17 ∧ mlNames.getD k "" = fn.name := by
  unfold mlK at h
  obtain ⟨k', hk', hb⟩ := Option.bind_eq_some_iff.mp h
  simp only [Bool.cond_eq_ite, Nat.ble_eq] at hb
  split_ifs at hb with h1
  cases hb
  have := List.find?_some hk'
  simp only [beq_iff_eq] at this
  exact ⟨h1, List.mem_range.mp (List.mem_of_find?_eq_some hk'), this⟩

theorem prodW_gaps (w : ℕ → E) : ∀ n : ℕ,
    prodW w ((List.range n).map fun i ↦ (6 + 10 * i, 4)) = ((List.range n).map fun i ↦ w (6 + 10 * i) ^ 4).prod
  | 0 => by simp [prodW]
  | n + 1 => by
    have happ : ∀ (a b : List (ℕ × ℕ)), prodW w (a ++ b) = prodW w a * prodW w b := by
      intro a b
      induction a with
      | nil => simp [prodW]
      | cons x l ih => simp only [List.cons_append, prodW, ih, mul_assoc]
    rw [List.range_succ, List.map_append, happ, prodW_gaps w n, List.map_append, List.prod_append]
    simp [prodW]

theorem setG_ghost0 (σ : Val) (w : E) : setG σ [w] (V.n CoreMode.GB) = w := by
  have h := ownG_setG (G := ({ ghosts := 1 } : CoreMode.HSig)) (σ := σ) (gw := [w]) rfl
  simpa [CoreMode.ownG, CoreMode.vw] using h

/-- **The ghost family at an honest instance.** -/
theorem ml_inst {r : Ref} (hr : r.Ok) (hO : MonoOk) {I : Inst}
    (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn} (hf : coreProgram.find? f = some fn) {k : ℕ}
    (hk : mlK fn = some k) :
    fn.params = [.n 0, .n 1, .n 2, .n 3] ∧ ∃ a, I.hdr.2 = ofK (addressOfIndex a) ∧ a + 5 < maxCells ∧
      refMem r.img (a + 5) = σ (V.n 3) ∧
      ∀ x, mlSub fn x = true → x.Holds (setG σ [refMem r.img (a + 2)]) := by
  obtain ⟨hk1, hk17, hkn⟩ := mlK_spec hk
  have hfn : f = mlNames.getD k "" := by rw [hkn, find_name' hf]
  have hmem : f ∈ mlNames := by
    rw [hfn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [mlNames] using hk17)]
    exact List.getElem_mem _
  obtain ⟨aP, L, ⟨hh2, ha5, hm5, hL⟩, hσ3, hσ1, -, O, hOL, h13, h14⟩ :=
    (monoQ_all hO hr I hI f σ bufs kids ht).2.1 hmem
  have hfn' : fn = coreProgram.getD (idx% «child_claim_list_mono_last__L0» + k) default := by
    rw [hfn] at hf
    exact Option.some.inj (hf.symm.trans (find_of_idx (ml_idx k hk17)))
  have hok : mlOk k fn = true := by rw [hfn']; exact ml_all k hk17
  clear hfn'
  obtain ⟨hpar, atoms, r0, r1, hbody, hl4, hl5, hrecs, ⟨cm, hac, hcm⟩, tv, htv, hend⟩ := mlOk_parts (by omega) hok
  refine ⟨hpar, aP, hh2, ha5, by rw [hm5, hσ3], ?_⟩
  obtain ⟨args, rets, fn', hf', -, es0, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
  rw [hbody] at hw
  have hpath := atoms_on_path' atoms hw
  have hat : ∀ a ∈ atoms, a.Holds r.img.read σ := fun a ha ↦ hh _ (hpath a ha)
  -- the record's pointers
  have h4 : σ (.n 4) = refMem r.img (aP + 3) * gen ^ O := loadHolds_unique (load_sound hl4 hat) h13
  have h5 : σ (.n 5) = refMem r.img (aP + 2) * gen ^ (4 * O) := loadHolds_unique (load_sound hl5 hat) h14
  -- the walk and its bound
  obtain ⟨es, hes, hvals, hnz⟩ := monoWalk_vals (ref_memOk hr) hrecs hat
  have hreg : refMem r.img (aP + 3) ≠ 0 := fun h0 ↦ hnz (by omega) (by rw [h4, h0, zero_mul])
  have hce : σ (.n (mlEnd k)) = refMem r.img (aP + 3) * gen ^ (O + (gsum es k + k)) := by
    rw [mulOf_sound hac hat, const_sound hcm hat, word_two_pow (by omega), (hvals k le_rfl).1, h4,
      pow_add, pow_add]
    ring
  obtain ⟨y, t1, t2, hy1, hy2, hy3⟩ := rcOf_sound hend hat
  obtain ⟨e0, e0', he0, he0', hx0, hk0'⟩ := rc_sound (ref_memOk hr) ⟨hy1, hy2, hy3⟩
  have hb := endOf_sound htv hat
  rw [hce, hx0, hσ1, mul_comm (gen ^ e0)] at hb
  have hgs := gsum_le (fun i hi ↦ (hes i hi).1) k le_rfl
  have hend' : O + (gsum es k + k) = e0 :=
    gen_pow_inj (by omega) (by omega) (mul_left_cancel₀ hreg hb)
  have hLe : L = e0 + e0' := gen_pow_inj (by omega) (by omega) (hσ3.symm.trans hk0')
  -- the family's read
  intro x hx
  match x, hx with
  | .sub c q, hx =>
    simp only [mlSub, hk, Option.any_some, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq] at hx
    obtain ⟨⟨hjj, rfl⟩, hcb⟩ := hx
    set jj := c.off / 4 with hjjd
    have hgjj := gsum_mono es (show jj + 1 ≤ k by omega)
    have hcap : L < capE := by unfold capE; omega
    have hσ' : ∀ m < CoreMode.GB, setG σ [refMem r.img (aP + 2)] (V.n m) = σ (V.n m) := fun m hm ↦
      setG_eq (show (V.n m).idx < CoreMode.GB from hm)
    show CoreMode.RunSet _ _ _ _ _ _
    refine ⟨0, L, O + gsum es (jj + 1) + jj, rep_const (by unfold capE; omega), ?_, Nat.zero_le _, by omega, ?_⟩
    · simp only [idxC, valW_baseC, vw]
      rw [hσ' 3 (by unfold CoreMode.GB; omega), hσ3, gen_pow_eq_ofK]
      exact rep_of hcap
    · have hoff : c.off = 4 * jj + c.off % 4 := (Nat.div_add_mod c.off 4).symm
      have hgap : ∀ i < jj + 1, σ (.n (6 + 10 * i)) = gen ^ es i := fun i hi ↦ (hes i (by omega)).2.1
      have hpg := prod_gaps hgap (jj + 1) le_rfl
      set w := vw (setG σ [refMem r.img (aP + 2)]) with hw
      have hw5 : w 5 = σ (.n 5) := hσ' 5 (by unfold CoreMode.GB; omega)
      have hwg : w CoreMode.GB = refMem r.img (aP + 2) := setG_ghost0 σ _
      have hgl : ((List.range (jj + 1)).map fun i ↦ w (6 + 10 * i) ^ 4) =
          (List.range (jj + 1)).map fun i ↦ σ (V.n (6 + 10 * i)) ^ 4 := by
        refine List.map_congr_left fun i hi ↦ ?_
        rw [hw, vw, hσ' _ (by have := List.mem_range.mp hi; unfold CoreMode.GB; omega)]
      have e1 : CoreMode.CCell.valW w c =
          w 5 * ((List.range (jj + 1)).map fun i ↦ w (6 + 10 * i) ^ 4).prod * ofK (addressOfIndex c.off) := by
        unfold CoreMode.CCell.valW
        rw [hcb, prodW, prodW_gaps, pow_one]
      have e2 : CoreMode.CCell.valW w ⟨[(CoreMode.GB, 1)], c.off % 4⟩ =
          w CoreMode.GB * ofK (addressOfIndex (c.off % 4)) := by
        unfold CoreMode.CCell.valW
        rw [prodW, prodW, pow_one, mul_one]
      obtain ⟨d, hd⟩ : ∃ d, c.off % 4 = d := ⟨_, rfl⟩
      have hfin : refMem r.img (aP + 2) * gen ^ (4 * O) * gen ^ (4 * gsum es (jj + 1)) * ofK (addressOfIndex c.off) =
          refMem r.img (aP + 2) * ofK (addressOfIndex (c.off % 4)) *
            ofK (addressOfIndex (4 * (O + gsum es (jj + 1) + jj))) := by
        rw [hd, hoff, hd, ← gen_pow_eq_ofK, ← gen_pow_eq_ofK, ← gen_pow_eq_ofK]
        ring
      unfold CoreMode.CCell.addrW
      rw [e1, e2, hgl, hpg, hw5, hwg, h5, hfin]
  | .lt _ _, hx | .nz _, hx | .subR _ _, hx | .under _ _, hx | .subP _ _, hx => simp [mlSub] at hx

/-- **The ghost family's linked cells** at its frame: the caller's cell `2` its ghost word, cell `5` its parameter
`limit`. -/
theorem mlGlF {r : Ref} {Cf : CFun} {fp a : ℕ} {σ : Val} (hgl : Cf.gl = [(2, 4, 0), (5, 3, 0)])
    (hgh : Cf.H.sig.ghosts = 1) (hpar : Cf.fn.params = [.n 0, .n 1, .n 2, .n 3])
    (hRd : CoreMode.Rd r.img fp 1 = some (ofK (Parameters.g ^ a))) (h5 : a + 5 < maxCells)
    (hm5 : refMem r.img (a + 5) = σ (V.n 3)) :
    GlF r.img Cf.gl fp (Cf.fn.params.map (setG σ [refMem r.img (a + 2)]) ++
      ownG Cf.H.sig (setG σ [refMem r.img (a + 2)])) := by
  rw [ownG_setG (by rw [hgh]; rfl), hpar, hgl]
  intro d b k hm
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine ⟨a, hRd, by omega, ?_⟩
    simp [CoreMode.LinkW, CoreMode.slotW]
  · refine ⟨a, hRd, h5, ?_⟩
    simp only [CoreMode.LinkW, show (5 : ℕ) ≠ 0 by omega, ↓reduceIte, CoreMode.slotW, List.map_cons, List.map_nil, List.cons_append, List.nil_append, pow_zero]
    rw [hm5, setG_eq (show (V.n 3).idx < CoreMode.GB by show 3 < CoreMode.GB; unfold CoreMode.GB; omega)]
    simp

end

end LeanVM.Guest.EndExec
