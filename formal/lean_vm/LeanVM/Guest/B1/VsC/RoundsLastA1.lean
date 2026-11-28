/-
  LeanVM.Guest.B1.VsC.RoundsLastA1

  `link_rounds_last` grinding one bit completes placed.
-/

module

public import LeanVM.Guest.B1.VsC.RoundsLoads1
public import LeanVM.Guest.B1.VsC.RoundsMainA
import LeanVM.Guest.CoreRef

/-!
# `link_rounds_last`, placed, one bit of grind

`lrl_placed1`: `link_rounds_last__L{nt}_L1_L{k}`, `k ≥ 1`, placed at any frame, ending at its
cursor, by `callAtA_straight` on vsc7's forward valuation per memory (`lrl_complete1`: the windows
from `winOracle` over each round's `roundWord`), its loads located by `lrRounds_loads1`: the record's
(`rp`, `out`), the challenges' (`pts`), the reads at each round's cursor (offsets `≤ nt + 1`, the
nonce last), and `grind_check`'s reads of the window table at `tabs`. `lrLastA_placed1`: the
statement `LrLastA` at one bit, its cursors located by `CurChain`, vacuous without it.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- The region a chain grinding one bit reads: the record at `rp` and `out`, the challenges at
`pts`, each round's cursor run (its scalars and nonce), the window table at `tabs`. -/
def LrlRegion1 (R : ℕ → Prop) (nt k : ℕ) (rp out pts tabs : E) (st : RSt) (l : List (E × RSt)) : Prop :=
  (∀ off < 7, ∃ i, rp.limb 0 * addressOfIndex off = addressOfIndex i ∧ R i) ∧
  (∀ off < 7, ∃ i, out.limb 0 * addressOfIndex off = addressOfIndex i ∧ R i) ∧
  (∀ off < k, ∃ i, pts.limb 0 * addressOfIndex off = addressOfIndex i ∧ R i) ∧
  (∀ r < k, ∀ off ≤ nt + 1, ∃ i, (chainLast st (l.take r)).cur.limb 0 * addressOfIndex off = addressOfIndex i ∧
    R i) ∧
  ∀ t < 2 ^ 11, ∃ i, tabs.limb 0 * addressOfIndex t = addressOfIndex i ∧ R i

/-- What the kernel checks of `link_rounds_last`'s body at one bit, placed: `lrlChecks1`, a leaf,
no allocation, the grinds' windows apart. -/
def lrlChecks1A (nt k : ℕ) (body : List Stmt) : Bool :=
  lrlChecks1 nt k body && leafB body && (atomsOf body).all (fun a => !atomAllocB a) &&
    decide (((List.range k).map fun r => lrOg nt 2 3 r 11 [4, 5, 6, 7, 8] 9 10 none).Pairwise
      (fun a b => a + gcW 1 < b))

set_option maxHeartbeats 2000000 in
/-- **`link_rounds_last__L{nt}_L1_L{k}` completes placed**, `k ≥ 1`, on a memory defined on its
first `2^11` words at least. -/
theorem lrl_placed1 {kd nt k : ℕ} {name : String} {f : Fn} (hkd : 11 ≤ kd) (hnt : 1 ≤ nt) (hnt' : nt ≤ 32)
    (hk3 : nt % 4 ≠ 3) (hk0 : k ≠ 0)
    (hfind : coreProgram.find? name = some f) (hlp : coreProgram.loop name = false)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3]) (hbody : f.body = lrLastBody nt 1 k)
    (hck : lrlChecks1A nt k (lrLastBody nt 1 k) = true)
    {R : ℕ → Prop} (rp out pts tabs : E) (st : RSt) (l : List (E × RSt)) (h5 : st.cap.length = 5) (hl : l.length = k)
    (hR : LrlRegion1 R nt k rp out pts tabs st l) (fp c : ℕ) :
    CallAtA fs al cert kd name [rp, out, pts, tabs] [0] R (fun _ => False) (fun _ => True)
      (fun rd ↦ ReadsAt rd rp st.cells ∧ (1 ≠ 0 → WinTabs rd tabs) ∧ RoundChain rd nt 1 st l ∧
        ReadsAt rd pts (l.map Prod.fst) ∧ ReadsAt rd out (chainLast st l).cells)
      PostQuiet (fs name) fp c c := by
  obtain ⟨c0, c1, c2, c3, c4, cu, cl, hcells, rfl⟩ := cells_eq_seven h5
  rw [← hbody] at hck
  simp only [lrlChecks1A, Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨hck1, hleaf⟩, hnoal⟩, hog⟩ := hck
  simp only [lrlChecks1, Bool.and_eq_true, List.all_eq_true] at hck1
  obtain ⟨⟨⟨hc, hat⟩, hst⟩, hsg⟩ := hck1
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp hc
  replace hc : chk [rp, out, pts, tabs].length f.body = some c' := hc
  set rs := lrRounds nt 1 2 3 k 11 [4, 5, 6, 7, 8] 9 10 none with hrs
  have hb : f.body = lrlPre nt 1 k ++ [.ret [.n rs.2.2.2.2.1]] := by rw [hbody, lrLastBody_eq hk0]
  have hmemB : ∀ s ∈ lrlPre nt 1 k, s ∈ f.body := fun s hs => by rw [hb]; exact List.mem_append_left _ hs
  have hat' : ∀ a, Stmt.atom a ∈ f.body → mulFwdB a = true ∧ atomQuiet a = true := fun a ha => by
    simpa using hat a (mem_atomsOf' ha)
  let ogs : ℕ → ℕ := fun r => lrOg nt 2 3 r 11 [4, 5, 6, 7, 8] 9 10 none
  let ps : Reader → List (ℕ × E) := fun rd => (List.range k).map fun r =>
    (ogs r, roundWord rd nt (chainLast ⟨[c0, c1, c2, c3, c4], cu, cl⟩ (l.take r)))
  have hsum : c + ([] : List ℕ).sum = c := by simp
  rw [← hsum]
  refine callAtA_straight (fun rd => fwdVal rd (winOracle (ps rd)) [rp, out, pts, tabs] f.body) [] []
    hfind hlp hleaf ⟨by simp, List.Pairwise.nil⟩ (fun _ _ => trivial) (fun _ h => h.elim)
    fun rd hlow _ hP => ?_
  obtain ⟨hrp, hwt, hch, hpts, hout⟩ := hP
  set σ := fwdVal rd (winOracle (ps rd)) [rp, out, pts, tabs] f.body with hσ
  have G : ∀ a, Stmt.atom a ∈ f.body → Good rd (storesOf 4 f.body) (winOracle (ps rd)) σ a := fwd_good hc
  have p0 : σ (.n 0) = rp := fwd_param hc (by norm_num)
  have p1 : σ (.n 1) = out := fwd_param hc (by norm_num)
  have p2 : σ (.n 2) = pts := fwd_param hc (by norm_num)
  have p3 : σ (.n 3) = tabs := fwd_param hc (by norm_num)
  have hW : ∀ r < k, ∀ j ≤ gcW 1, winOracle (ps rd) (ogs r + j) =
      gcWin 1 (roundWord rd nt (chainLast ⟨[c0, c1, c2, c3, c4], cu, cl⟩ (l.take r))) j := by
    intro r hr j hj
    refine winOracle_at (p := (ogs r, _)) ?_ (List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩) hj
    simpa [ps, List.map_map, Function.comp_def] using hog
  have hSp : ∀ d p off, Atom.load d p off ∈ storesOf 4 f.body → p = .n 1 ∨ p = .n 2 := by
    intro d p off h
    simpa [storeOutPtsB] using hst _ h
  have hSp' : ∀ d p off, Atom.load d p off ∈ storesOf 4 f.body → p.idx < 3 := fun d p off h => by
    rcases hSp d p off h with rfl | rfl <;> simp
  rw [hcells] at hrp
  -- the record read
  have hrec : ∀ j < 7, σ (.n (4 + j)) = [c0, c1, c2, c3, c4, cu, cl].getD j 0 ∧
      LoadHolds rd (σ (.n 0)) j (σ (.n (4 + j))) := by
    intro j hj
    have hm : Stmt.atom (.load (.n (4 + j)) (.n 0) j) ∈ f.body := by
      apply hmemB; simp only [lrlPre]; interval_cases j <;> simp
    have hns : Atom.load (.n (4 + j)) (.n 0) j ∉ storesOf 4 f.body := fun h => by
      rcases hSp _ _ _ h with h | h <;> simp at h
    have hld : LoadHolds rd (σ (.n 0)) j ([c0, c1, c2, c3, c4, cu, cl].getD j 0) := by
      rw [p0, List.getD_eq_getElem _ _ (by simp; omega)]; exact hrp j (by simp; omega)
    have e := good_load_eq hld (G _ hm) hns
    exact ⟨e, e ▸ hld⟩
  have hst0 : rstOf σ [4, 5, 6, 7, 8] 9 10 = ⟨[c0, c1, c2, c3, c4], cu, cl⟩ := by
    have e0 := (hrec 0 (by norm_num)).1; have e1 := (hrec 1 (by norm_num)).1
    have e2 := (hrec 2 (by norm_num)).1; have e3 := (hrec 3 (by norm_num)).1
    have e4 := (hrec 4 (by norm_num)).1; have e5 := (hrec 5 (by norm_num)).1
    have e6 := (hrec 6 (by norm_num)).1
    simp only [Nat.reduceAdd, List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3 e4 e5 e6
    simp only [rstOf, List.map_cons, List.map_nil, Function.comp_apply, e0, e1, e2, e3, e4, e5, e6]
  -- the rounds
  have hmR : ∀ a, Stmt.atom a ∈ rs.1 → Stmt.atom a ∈ f.body := fun a ha => hmemB _ (by
    simp only [lrlPre]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ha)))
  have hrc := hrc_of_lowDef hlow hkd
  have hwt' : WinTabs rd (σ (.n 3)) := by rw [p3]; exact hwt one_ne_zero
  obtain ⟨hR', hlast, -, -, -, -⟩ := lrRounds_complete1 (m := 3) (S := storesOf 4 f.body)
    (w := winOracle (ps rd)) (σ := σ) (pts := 2) (tabs := 3) hnt hnt' hk3 hSp' hrc hwt' k 11
    [4, 5, 6, 7, 8] 9 10 none _ l (by norm_num) (by norm_num) (by norm_num) (fun a ha => G a (hmR a ha))
    (fun d x y ha => by simpa [mulFwdB] using (hat' _ (hmR _ ha)).1)
    (fun a ha r hr => by simpa using hsg a ha r (List.mem_range.mpr hr)) hW
    (fun z hz => absurd hz (by simp)) hst0 hl hch (by rw [p2]; exact hpts)
  have hLd := lrRounds_loads1 (m := 3) (S := storesOf 4 f.body) (w := winOracle (ps rd)) (σ := σ) (pts := 2)
    (tabs := 3) hnt hnt' hk3 hSp' hrc hwt' k 11 [4, 5, 6, 7, 8] 9 10 none _ l (by norm_num) (by norm_num)
    (by norm_num) (fun a ha => G a (hmR a ha))
    (fun d x y ha => by simpa [mulFwdB] using (hat' _ (hmR _ ha)).1)
    (fun a ha r hr => by simpa using hsg a ha r (List.mem_range.mpr hr)) hW
    (fun z hz => absurd hz (by simp)) hst0 hl hch (by rw [p2]; exact hpts)
  -- the record stored
  have hlen : rs.2.1.length = 5 := lrRounds_cap_length _ _ _ _ _ _ _ _ _ _ rfl
  rw [← hrs] at hR' hlast hLd
  rw [← hlast] at hout
  have hfin : ∀ j (hj : j < 5), LoadHolds rd out j (σ (.n (rs.2.1.getD j 0))) := by
    intro j hj
    have h := hout j (by simp [RSt.cells, rstOf, hlen]; omega)
    have e : (rstOf σ rs.2.1 rs.2.2.1 rs.2.2.2.1).cells[j]'(by simp [RSt.cells, rstOf, hlen]; omega) =
        σ (.n (rs.2.1.getD j 0)) := by
      simp only [RSt.cells, rstOf]
      rw [List.getElem_append_left (by simp [hlen]; omega), List.getElem_map,
        List.getD_eq_getElem _ _ (by omega)]
      rfl
    rwa [e] at h
  have h5' : LoadHolds rd out 5 (σ (.n rs.2.2.1)) := by
    have h := hout 5 (by simp [RSt.cells, rstOf, hlen])
    simpa [RSt.cells, rstOf, List.getElem_append_right, hlen] using h
  have h6' : LoadHolds rd out 6 (σ (.n rs.2.2.2.1)) := by
    have h := hout 6 (by simp [RSt.cells, rstOf, hlen])
    simpa [RSt.cells, rstOf, List.getElem_append_right, hlen] using h
  have hmc : Stmt.atom (.const (.n rs.2.2.2.2.1) (word 0 0)) ∈ f.body := hmemB _ (by simp [lrlPre, ← hrs])
  have hV : σ (.n rs.2.2.2.2.1) = word 0 0 := G _ hmc
  have hatoms : atomsOf f.body = atomsOf (lrlPre nt 1 k) := by rw [hb, atomsOf_append_ret]
  refine ⟨by rw [hparams]; exact fwd_params hc, fun vs hvs => ?_, fun a ha => ?_, ?_, ?_, fun A hA => ?_⟩
  · rw [hb] at hvs
    have := retOf_spec hvs
    obtain ⟨ss, he, -⟩ := this
    have := (List.append_inj' he rfl).2
    simp only [List.cons.injEq, Stmt.ret.injEq, and_true] at this
    subst this
    simp [hV, word_zero]
  · rw [hb] at ha
    rcases List.mem_append.mp ha with ha | ha
    swap
    · simp at ha
    simp only [lrlPre, ← hrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range, Stmt.atom.injEq] at ha
    rcases ha with (((ha | ha) | ⟨j, hj, ha⟩) | ha)
    · rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨(hrec 0 (by norm_num)).2, trivial⟩
      · exact ⟨(hrec 1 (by norm_num)).2, trivial⟩
      · exact ⟨(hrec 2 (by norm_num)).2, trivial⟩
      · exact ⟨(hrec 3 (by norm_num)).2, trivial⟩
      · exact ⟨(hrec 4 (by norm_num)).2, trivial⟩
      · exact ⟨(hrec 5 (by norm_num)).2, trivial⟩
      · exact ⟨(hrec 6 (by norm_num)).2, trivial⟩
    · exact ⟨(hR' a ha).1, (hR' a ha).2 rd⟩
    · subst ha
      refine ⟨?_, trivial⟩
      show LoadHolds rd (σ (.n 1)) j _
      rw [p1]; exact hfin j hj
    · rcases ha with rfl | rfl | rfl
      · refine ⟨?_, trivial⟩
        show LoadHolds rd (σ (.n 1)) 5 _
        rw [p1]; exact h5'
      · refine ⟨?_, trivial⟩
        show LoadHolds rd (σ (.n 1)) 6 _
        rw [p1]; exact h6'
      · exact ⟨hV, trivial⟩
  · exact LeanVM.Guest.Memory.allocs_atoms _ hnoal
  · rw [LeanVM.Guest.Memory.allocDsts_atoms hnoal]; rfl
  · -- the loads
    obtain ⟨d, q, off, hm, rfl⟩ := mem_loadAddrs hA
    rw [hatoms] at hm
    have hm' := mem_of_mem_atomsOf hm
    obtain ⟨hRrp, hRout, hRpts, hRcur, hRtab⟩ := hR
    simp only [lrlPre, ← hrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range, Stmt.atom.injEq] at hm'
    rcases hm' with (((hm' | hm') | ⟨j, hj, hm'⟩) | hm')
    · have key : ∀ off < 7, ∃ i, (σ (.n 0)).limb 0 * addressOfIndex off = addressOfIndex i ∧
          ((c ≤ i ∧ i < c + ([] : List ℕ).sum) ∨ R i) := fun off h => by
        obtain ⟨i, hi, hRi⟩ := hRrp off h
        exact ⟨i, by rw [p0]; exact hi, Or.inr hRi⟩
      rcases hm' with h | h | h | h | h | h | h <;> obtain ⟨rfl, rfl, rfl⟩ := Atom.load.inj h <;>
        exact key _ (by norm_num)
    · rcases hLd d q off hm' with ⟨rfl, hoff⟩ | ⟨r, hr, hoff, hq⟩ | ⟨rfl, e, he, hq⟩
      · obtain ⟨i, hi, hRi⟩ := hRpts off (by omega)
        exact ⟨i, by rw [p2]; exact hi, Or.inr hRi⟩
      · obtain ⟨i, hi, hRi⟩ := hRcur r (by omega) off hoff
        exact ⟨i, by rw [hq]; exact hi, Or.inr hRi⟩
      · obtain ⟨i, hi, hRi⟩ := hRtab e he
        refine ⟨i, ?_, Or.inr hRi⟩
        rw [hq, p3]
        exact addr_mul_gen_pow (by rw [Nat.add_zero]; exact hi)
    · obtain ⟨rfl, rfl, rfl⟩ := Atom.load.inj hm'
      obtain ⟨i, hi, hRi⟩ := hRout j (by omega)
      exact ⟨i, by rw [p1]; exact hi, Or.inr hRi⟩
    · rcases hm' with h | h | h
      · obtain ⟨rfl, rfl, rfl⟩ := Atom.load.inj h
        obtain ⟨i, hi, hRi⟩ := hRout 5 (by norm_num)
        exact ⟨i, by rw [p1]; exact hi, Or.inr hRi⟩
      · obtain ⟨rfl, rfl, rfl⟩ := Atom.load.inj h
        obtain ⟨i, hi, hRi⟩ := hRout 6 (by norm_num)
        exact ⟨i, by rw [p1]; exact hi, Or.inr hRi⟩
      · cases h

/-- **`LrLastA` at one bit**, from the placed leaf: the cursors located by `CurChain`. -/
theorem lrLastA_placed1 {kd nt k : ℕ} (hkd : 11 ≤ kd) (hnt : 1 ≤ nt) (hnt' : nt ≤ 32) (hk3 : nt % 4 ≠ 3)
    (hk0 : k ≠ 0) {name : String} {f : Fn}
    (hfind : coreProgram.find? name = some f) (hlp : coreProgram.loop name = false)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3]) (hbody : f.body = lrLastBody nt 1 k)
    (hck : lrlChecks1A nt k (lrLastBody nt 1 k) = true) :
    LrLastA fs al cert kd nt 1 name k := by
  intro R rp out pts tabs st l h5 hl hrp hout hpts hcur htab fp c
  by_cases hcc : CurChain nt 1 st l
  · refine lrl_placed1 hkd hnt hnt' hk3 hk0 hfind hlp hparams hbody hck rp out pts tabs st l h5 hl
      ⟨hrp, hout, hpts, fun r hr off hoff => ?_, fun t ht => htab one_ne_zero t ht⟩ fp c
    have e := curChain_cur st l hcc r (by omega)
    have hR1 : rlen nt 1 = nt + 2 := by simp [rlen]
    obtain ⟨i, hi, hRi⟩ := hcur (r * rlen nt 1 + off) (by
      rw [hR1] at *
      have : (r + 1) * (nt + 2) ≤ k * (nt + 2) := Nat.mul_le_mul_right _ (by omega)
      nlinarith)
    exact ⟨i, by rw [e]; exact addr_mul_gen_pow hi, hRi⟩
  · exact ⟨[], ⟨by simp, List.Pairwise.nil⟩, le_rfl, fun _ _ => trivial,
      fun rd _ _ hP => absurd (roundChain_curChain hP.2.2.1) hcc⟩

end
end LeanVM.Guest.B1.VsC
