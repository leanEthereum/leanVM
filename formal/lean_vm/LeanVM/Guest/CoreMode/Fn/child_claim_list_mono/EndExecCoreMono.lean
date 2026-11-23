/-
  LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.EndExecCoreMono

  The core route's ghost family at the honest instances: `child_claim_list_mono_last__L{k}`, its ghost
  word its caller's entries table, its reads in that table.
-/

module

public import LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.ResMR
public import LeanVM.Guest.EndExecCoreLink
import LeanVM.Guest.ValRef
public import LeanVM.Guest.GuestConst
import LeanVM.Guest.Data.Consts
import LeanVM.Guest.Data.ValNames.«child_claim_list_mono_last__L»
import LeanVM.Guest.Data.ValNames.child_claim_list_mono_loop0
import LeanVM.Guest.Data.ValNames.child_claim_list_mono_loop1

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
open LeanVM.Guest.B1 (loadHolds_unique loadHolds_mul_gen_pow word_two_pow)
open LeanVM.Guest.B1.Digest
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

theorem mlK_spec {fn : Fn} {p : ℕ × ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ)} (h : mlK fn = some p) :
    ∃ k, p = (k, 5, 6, 10, 3, [(2, 4, 0), (5, 3, 0)]) ∧ 1 ≤ k ∧ k < 17 ∧ mlNames.getD k "" = fn.name := by
  have hm := CoreMode.lookup_memL h
  simp only [CoreMode.FnReg.mlLoops, CoreMode.Own.child_claim_list_mono_last.mlLoops, List.append_nil,
    List.mem_map, List.mem_range, Prod.mk.injEq] at hm
  obtain ⟨j, hj, he, rfl⟩ := hm
  exact ⟨j + 1, rfl, by omega, by omega, he⟩

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
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn} (hf : coreProgram.find? f = some fn)
    {p : ℕ × ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ)} (hk : mlK fn = some p) :
    fn.params = [.n (valf% «child_claim_list_mono_last» "rec"), .n (valf% «child_claim_list_mono_last» "region"), .n (valf% «child_claim_list_mono_last» "mark"), .n (valf% «child_claim_list_mono_last» "limit_g")] ∧ ∃ a, I.hdr.2 = ofK (addressOfIndex a) ∧ a + 5 < maxCells ∧
      refMem r.img (a + 5) = σ (V.n (valf% «child_claim_list_mono_last» "limit_g")) ∧
      ∀ x, mlSub fn x = true → x.Holds (setG σ [refMem r.img (a + 2)]) := by
  obtain ⟨k, rfl, hk1, hk17, hkn⟩ := mlK_spec hk
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

/-! ## The frame loops (`cm`) -/

/-- **A frame loop's entry** in the `cmLoops` registry, `child_claim_list_mono`'s own. -/
theorem cmK_spec {fn : Fn} {p : ℕ × ℕ × ℕ × ℕ × List ℕ} (h : CoreMode.cmK fn = some p) :
    (fn.name, p) ∈ CoreMode.Own.child_claim_list_mono.cmLoops := by
  simpa only [CoreMode.FnReg.cmLoops, List.append_nil] using CoreMode.lookup_memL h

/-- **A frame loop's reads at an honest instance**: the record at offset `O`, the next at `O'`, at most `L`
(`MonoQ`); claim `jj`'s entry `ent · Π_{i ≤ jj} gap_i^4 · g^(4jj)` lies `4o` words into the caller's table, `o < L`. -/
theorem cmRead {r : Ref} (hr : r.Ok) (hO : MonoOk) {I : Inst}
    (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) {jf m p0 st0 cw ew : ℕ}
    (hfl : f = name% «child_claim_list_mono_loop0» ∨ f = name% «child_claim_list_mono_loop1»)
    (hidx : coreProgram.indexOf? f = some jf) (hok : monoOk (coreProgram.getD jf default) f m p0 st0 cw ew = true)
    (hcw : word cw 0 = gen ^ m) (hm136 : m ≤ 136) (hm0 : 0 < m) :
    ∃ aP L, I.hdr.2 = ofK (addressOfIndex aP) ∧ aP + 5 < maxCells ∧ refMem r.img (aP + 5) = gen ^ L ∧
      L < 2 ^ 33 ∧ ∀ jj < m, ∃ o < L, σ (.n 12) *
        ((List.range (jj + 1)).map fun i ↦ σ (.n (13 + 10 * i)) ^ 4).prod * gen ^ (4 * jj) =
          refMem r.img (aP + 2) * gen ^ (4 * o) := by
  obtain ⟨aP, L, n, qc, ⟨hh2, ha5, hm5, hL⟩, hq0', hqn, hn, hn1, hrec⟩ :=
    (monoQ_all hO hr I hI f σ bufs kids ht).1 hfl
  obtain ⟨args, rets, fn', hf', -, es0, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
  obtain rfl : fn' = coreProgram.getD jf default := Option.some.inj (hf'.symm.trans (find_of_idx hidx))
  simp only [monoOk, monoHead, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, -⟩, -⟩, -⟩, -⟩, hm10⟩, hl11⟩, hl12⟩, hoc⟩, -⟩, -⟩, hrecs⟩ := hok
  -- the body's atoms, on the path
  have hpath : ∀ a ∈ loopAtoms (coreProgram.getD jf default), Ev.atom a ∈ es0 := by
    simp only [B1.Digest.loopShape, Bool.and_eq_true, decide_eq_true_eq] at hshape
    obtain ⟨-, hsp⟩ := hshape
    unfold loopAtoms
    split at hsp
    · rename_i atoms c g args hsl
      rw [hsl]
      rw [splitLoop_eq hsl] at hw
      exact atoms_on_path' atoms hw
    · exact absurd hsp (by simp)
  have hat : ∀ a ∈ loopAtoms (coreProgram.getD jf default), a.Holds r.img.read σ := fun a ha ↦ hh _ (hpath a ha)
  -- the record's pointers
  have h10 : σ (.n 10) = σ (.n 2) * gen ^ (15 * qc) := by
    rw [monoIs_sound hm10 hat, hq0', gen_pow_pow]
  obtain ⟨O, hOL, h13, h14⟩ := hrec qc hqn.le
  rw [← h10] at h13 h14
  have h11 : σ (.n 11) = refMem r.img (aP + 3) * gen ^ O := loadHolds_unique (load_sound hl11 hat) h13
  have h12 : σ (.n 12) = refMem r.img (aP + 2) * gen ^ (4 * O) := loadHolds_unique (load_sound hl12 hat) h14
  -- the walk and the next record
  obtain ⟨es, hes, hvals, hnz⟩ := monoWalk_vals (ref_memOk hr) hrecs hat
  have hreg : refMem r.img (aP + 3) ≠ 0 := fun h0 ↦ hnz (by omega) (by rw [h11, h0, zero_mul])
  obtain ⟨hlc, hcc⟩ := outOk_sound hoc hat
  obtain ⟨O', hO'L, h13', -⟩ := hrec (qc + 1) (by omega)
  have h28 : LoadHolds r.img.read (σ (.n 10)) 28 (refMem r.img (aP + 3) * gen ^ O') := by
    rw [h10, loadHolds_mul_gen_pow, show 15 * qc + 28 = 15 * (qc + 1) + 13 by ring, ← loadHolds_mul_gen_pow]
    exact h13'
  have heq := loadHolds_unique h28 hlc
  rw [hcc, (hvals m le_rfl).1, h11, hcw, mul_assoc, mul_assoc, ← pow_add, ← pow_add] at heq
  have hgs := gsum_le (fun i hi ↦ (hes i hi).1) m le_rfl
  have hO' : O' = O + (gsum es m + m) := gen_pow_inj (by omega) (by omega) (mul_left_cancel₀ hreg heq)
  refine ⟨aP, L, hh2, ha5, hm5, hL, fun jj hjj ↦ ⟨O + gsum es (jj + 1) + jj, ?_, ?_⟩⟩
  · have hgjj := gsum_mono es (show jj + 1 ≤ m by omega)
    omega
  · rw [prod_gaps (fun i hi ↦ (hes i hi).2.1) (jj + 1) (by omega), h12, mul_assoc, mul_assoc, ← pow_add, ← pow_add,
      show 4 * O + (4 * gsum es (jj + 1) + 4 * jj) = 4 * (O + gsum es (jj + 1) + jj) by ring]

/-- **A frame loop's family at an honest instance** (`cmSub`), its ghost words its caller's entries, bound and frame. -/
theorem cm_inst {r : Ref} (hr : r.Ok) (hO : MonoOk) {I : Inst}
    (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn} (hf : coreProgram.find? f = some fn)
    {p : ℕ × ℕ × ℕ × ℕ × List ℕ} (hk : CoreMode.cmK fn = some p) :
    ∃ a, I.hdr.2 = ofK (addressOfIndex a) ∧ a + 5 < maxCells ∧
      ∀ x, CoreMode.cmSub fn x = true →
        x.Holds (setG σ [refMem r.img (a + 2), refMem r.img (a + 5), ofK (Parameters.g ^ a)]) := by
  obtain ⟨m, rfl, hcases⟩ : ∃ m, p = (m, val% «child_claim_list_mono_loop0» «child_claim_list_mono_loop1» "s4#1",
      val% «child_claim_list_mono_loop0» «child_claim_list_mono_loop1» "gap@1", 10, [2, 5]) ∧
      ((f = name% «child_claim_list_mono_loop0» ∧ m = guest_const% CLAIM_BIG) ∨
        (f = name% «child_claim_list_mono_loop1» ∧ m = guest_const% CLAIM_GROUP)) := by
    have hm := cmK_spec hk
    rw [find_name' hf] at hm
    simp only [CoreMode.Own.child_claim_list_mono.cmLoops, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hm
    rcases hm with ⟨h0, rfl⟩ | ⟨h1, rfl⟩
    · exact ⟨_, rfl, Or.inl ⟨h0, rfl⟩⟩
    · exact ⟨_, rfl, Or.inr ⟨h1, rfl⟩⟩
  obtain ⟨aP, L, hh2, ha5, hm5, hL, hrd⟩ : ∃ aP L, I.hdr.2 = ofK (addressOfIndex aP) ∧ aP + 5 < maxCells ∧
      refMem r.img (aP + 5) = gen ^ L ∧ L < 2 ^ 33 ∧ ∀ jj < m, ∃ o < L, σ (.n 12) *
        ((List.range (jj + 1)).map fun i ↦ σ (.n (13 + 10 * i)) ^ 4).prod * gen ^ (4 * jj) =
          refMem r.img (aP + 2) * gen ^ (4 * o) := by
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact cmRead hr hO hI ht (Or.inl rfl) mono136_idx mono136_ok word_g136 (by norm_num) (by norm_num)
    · exact cmRead hr hO hI ht (Or.inr rfl) mono17_idx mono17_ok word_g17 (by norm_num) (by norm_num)
  refine ⟨aP, hh2, ha5, fun x hx ↦ ?_⟩
  have hO3 := ownG_setG (G := ({ ghosts := 3 } : CoreMode.HSig)) (σ := σ)
    (gw := [refMem r.img (aP + 2), refMem r.img (aP + 5), ofK (Parameters.g ^ aP)]) rfl
  have hσ' : ∀ k < CoreMode.GB, vw (setG σ [refMem r.img (aP + 2), refMem r.img (aP + 5),
      ofK (Parameters.g ^ aP)]) k = σ (V.n k) := fun k hk ↦ setG_eq (show (V.n k).idx < CoreMode.GB from hk)
  have hg0 : vw (setG σ [refMem r.img (aP + 2), refMem r.img (aP + 5), ofK (Parameters.g ^ aP)]) CoreMode.GB =
      refMem r.img (aP + 2) := by
    have h := congrArg (·[0]?) hO3
    simp only [CoreMode.ownG, List.getElem?_map, List.getElem?_range (show 0 < 3 by decide), Option.map_some,
      List.getElem?_cons_zero, Option.some.injEq, Nat.add_zero] at h
    exact h
  have hg1 : vw (setG σ [refMem r.img (aP + 2), refMem r.img (aP + 5), ofK (Parameters.g ^ aP)])
      (CoreMode.GB + 1) = refMem r.img (aP + 5) := by
    have h := congrArg (·[1]?) hO3
    simp only [CoreMode.ownG, List.getElem?_map, List.getElem?_range (show 1 < 3 by decide), Option.map_some,
      List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
    exact h
  have hcap : L < capE := by unfold capE; omega
  have hlim : CoreMode.rep ((idxC (.val (CoreMode.GB + 1))).valW (vw (setG σ [refMem r.img (aP + 2),
      refMem r.img (aP + 5), ofK (Parameters.g ^ aP)]))) = some L := by
    simp only [idxC, valW_baseC]
    rw [hg1, hm5, gen_pow_eq_ofK]
    exact rep_of hcap
  have hc0 : CoreMode.rep ((idxC (.num 0)).valW (vw (setG σ [refMem r.img (aP + 2),
      refMem r.img (aP + 5), ofK (Parameters.g ^ aP)]))) = some 0 := rep_const (by unfold capE; omega)
  match x, hx with
  | .sub c q, hx =>
    simp only [CoreMode.cmSub, hk, Option.any_some, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq] at hx
    obtain ⟨⟨hjj, rfl⟩, hcb⟩ := hx
    obtain ⟨o, hoL, ho⟩ := hrd (c.off / 4) hjj
    refine ⟨0, L, o, hc0, hlim, Nat.zero_le _, hoL, ?_⟩
    have hgl : ((List.range (c.off / 4 + 1)).map fun i ↦ vw (setG σ [refMem r.img (aP + 2), refMem r.img (aP + 5),
        ofK (Parameters.g ^ aP)]) (13 + 10 * i) ^ 4) =
        (List.range (c.off / 4 + 1)).map fun i ↦ σ (V.n (13 + 10 * i)) ^ 4 := by
      refine List.map_congr_left fun i hi ↦ ?_
      rw [hσ' _ (by have := List.mem_range.mp hi; unfold CoreMode.GB; omega)]
    have h12 := hσ' 12 (by unfold CoreMode.GB; omega)
    have hprodW : ∀ (w : ℕ → E) (n : ℕ), prodW w ((List.range n).map fun i ↦ (13 + 10 * i, 4)) =
        ((List.range n).map fun i ↦ w (13 + 10 * i) ^ 4).prod := by
      intro w n
      induction n with
      | zero => simp [prodW]
      | succ n ih =>
        have happ : ∀ (a b : List (ℕ × ℕ)), prodW w (a ++ b) = prodW w a * prodW w b := by
          intro a b
          induction a with
          | nil => simp [prodW]
          | cons x l ih => simp only [List.cons_append, prodW, ih, mul_assoc]
        rw [List.range_succ, List.map_append, happ, ih, List.map_append, List.prod_append]
        simp [prodW]
    unfold CoreMode.CCell.addrW CoreMode.CCell.valW
    rw [hcb, prodW, hprodW, pow_one, hgl, h12, prodW, prodW, pow_one, mul_one, hg0]
    dsimp only
    have hx : gen ^ c.off = gen ^ (4 * (c.off / 4)) * gen ^ (c.off % 4) := by
      rw [← pow_add, Nat.div_add_mod]
    rw [← gen_pow_eq_ofK, ← gen_pow_eq_ofK, ← gen_pow_eq_ofK]
    refine congrArg (fun x : E ↦ x.limb 0) ?_
    calc σ (V.n 12) * ((List.range (c.off / 4 + 1)).map fun i ↦ σ (V.n (13 + 10 * i)) ^ 4).prod * gen ^ c.off
        = σ (V.n 12) * ((List.range (c.off / 4 + 1)).map fun i ↦ σ (V.n (13 + 10 * i)) ^ 4).prod *
            gen ^ (4 * (c.off / 4)) * gen ^ (c.off % 4) := by rw [hx]; ring
      _ = refMem r.img (aP + 2) * gen ^ (4 * o) * gen ^ (c.off % 4) := by rw [ho]
      _ = _ := by ring
  | .lt a b, hx =>
    simp only [CoreMode.cmSub, hk, Option.isSome_some, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    obtain ⟨o, hoL, -⟩ := hrd 0 (by rcases hcases with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num)
    exact ⟨0, L, hc0, hlim, by omega⟩
  | .nz _, hx | .subR _ _, hx | .under _ _, hx | .subP _ _, hx =>
    simp [CoreMode.cmSub] at hx

/-- **A frame loop's linked cells** at its frame: the caller's cells `2` and `5` its first two ghost words, the
caller's frame its third. -/
theorem cmGlF {r : Ref} {Cf : CFun} {fp a : ℕ} {σ : Val} {p : ℕ × ℕ × ℕ × ℕ × List ℕ}
    (hk : CoreMode.cmK Cf.fn = some p) (hgl : Cf.gl = CoreMode.loopGl Cf.fn.params.length p.2.2.2.2)
    (hgh : Cf.H.sig.ghosts = 3) (hRd : CoreMode.Rd r.img fp 1 = some (ofK (Parameters.g ^ a)))
    (ha5 : a + 5 < maxCells) :
    GlF r.img Cf.gl fp (Cf.fn.params.map (setG σ [refMem r.img (a + 2), refMem r.img (a + 5),
      ofK (Parameters.g ^ a)]) ++ ownG Cf.H.sig (setG σ [refMem r.img (a + 2), refMem r.img (a + 5),
      ofK (Parameters.g ^ a)])) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = (m, val% «child_claim_list_mono_loop0» «child_claim_list_mono_loop1» "s4#1",
      val% «child_claim_list_mono_loop0» «child_claim_list_mono_loop1» "gap@1", 10, [2, 5]) := by
    have hm := cmK_spec hk
    simp only [CoreMode.Own.child_claim_list_mono.cmLoops, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hm
    rcases hm with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨_, rfl⟩
  dsimp only at hgl
  rw [ownG_setG (by rw [hgh]; rfl), hgl]
  intro d b k hm
  simp only [CoreMode.loopGl, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton,
    Prod.mk.injEq] at hm
  set gs := [refMem r.img (a + 2), refMem r.img (a + 5), ofK (Parameters.g ^ a)]
  have hsl : ∀ j, CoreMode.slotW (Cf.fn.params.map (setG σ gs) ++ gs) (Cf.fn.params.length + j) = gs.getD j 0 :=
    fun j ↦ by simp [CoreMode.slotW, List.getD_eq_getElem?_getD, List.getElem?_append_right]
  rcases hm with ⟨j, hj, hjd⟩ | ⟨rfl, rfl, rfl⟩
  · obtain ⟨rfl, rfl, rfl⟩ := hjd
    have hj' : j = 0 ∨ j = 1 := by simp at hj; omega
    rcases hj' with rfl | rfl
    · refine ⟨a, hRd, by simp; omega, ?_⟩
      simp only [CoreMode.LinkW, List.getD_cons_zero, show (2 : ℕ) ≠ 0 by omega, ↓reduceIte]
      rw [hsl 0]
      simp [gs]
    · refine ⟨a, hRd, by simp; omega, ?_⟩
      simp only [CoreMode.LinkW, List.getD_cons_succ, List.getD_cons_zero, show (5 : ℕ) ≠ 0 by omega, ↓reduceIte]
      rw [hsl 1]
      simp [gs]
  · refine ⟨a, hRd, by omega, ?_⟩
    simp only [CoreMode.LinkW, ↓reduceIte, List.length_cons, List.length_nil]
    rw [hsl 2]
    simp [gs]

/-- **The ghost family's linked cells** at its frame: the caller's cell `2` its ghost word, cell `5` its parameter
`limit`. -/
theorem mlGlF {r : Ref} {Cf : CFun} {fp a : ℕ} {σ : Val} {p : ℕ × ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ)}
    (hk : mlK Cf.fn = some p) (hgl : Cf.gl = p.2.2.2.2.2)
    (hgh : Cf.H.sig.ghosts = 1) (hpar : Cf.fn.params = [.n (valf% «child_claim_list_mono_last» "rec"), .n (valf% «child_claim_list_mono_last» "region"), .n (valf% «child_claim_list_mono_last» "mark"), .n (valf% «child_claim_list_mono_last» "limit_g")])
    (hRd : CoreMode.Rd r.img fp 1 = some (ofK (Parameters.g ^ a))) (h5 : a + 5 < maxCells)
    (hm5 : refMem r.img (a + 5) = σ (V.n (valf% «child_claim_list_mono_last» "limit_g"))) :
    GlF r.img Cf.gl fp (Cf.fn.params.map (setG σ [refMem r.img (a + 2)]) ++
      ownG Cf.H.sig (setG σ [refMem r.img (a + 2)])) := by
  obtain ⟨k, rfl, -⟩ := mlK_spec hk
  dsimp only at hgl
  rw [ownG_setG (by rw [hgh]; rfl), hpar, hgl]
  intro d b k hm
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine ⟨a, hRd, by omega, ?_⟩
    simp [CoreMode.LinkW, CoreMode.slotW]
  · refine ⟨a, hRd, h5, ?_⟩
    simp only [CoreMode.LinkW, show (5 : ℕ) ≠ 0 by omega, ↓reduceIte, CoreMode.slotW, List.map_cons, List.map_nil, List.cons_append, List.nil_append, pow_zero]
    rw [hm5, setG_eq (show (V.n (valf% «child_claim_list_mono_last» "limit_g")).idx < CoreMode.GB by show 3 < CoreMode.GB; unfold CoreMode.GB; omega)]
    simp

end

end LeanVM.Guest.EndExec
