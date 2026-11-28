/-
  LeanVM.Guest.B1.VsC.RoundsLastA

  `link_rounds_last` with no grind completes placed.
-/

module

public import LeanVM.Guest.B1.VsC.RoundsLoadsC
public import LeanVM.Guest.B1.VsC.RoundsLastC
public import LeanVM.Guest.B1.VsC.SqueezeFwd
import LeanVM.Guest.CoreRef

/-!
# `link_rounds_last`, placed, no grind

`lrl_placed0`: `link_rounds_last__L{nt}_L0_L{k}`, `k ≥ 1`, placed at any frame, ending at its cursor
(no words of its own), by `callAtA_straight` on the forward valuation per memory: vsc7's
`lrl_complete0` with its loads located. They are the record's (`rp`, `out`), the challenges'
(`pts`), and the scalars' reads at the cursor before each round, `(chainLast st (l.take r)).cur`
(`lrRounds_loads0`); each run's cells are given in the region `R`. `lrl0_placed`: `k = 0`, the record
copied, by the transfer `callAtA_leaf0`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- The region a chain's reads need: the record at `rp` and `out`, the challenges at `pts`, the
scalars at each round's cursor. -/
def LrlRegion (R : ℕ → Prop) (nt k : ℕ) (rp out pts : E) (st : RSt) (l : List (E × RSt)) : Prop :=
  (∀ off < 7, ∃ i, rp.limb 0 * addressOfIndex off = addressOfIndex i ∧ R i) ∧
  (∀ off < 7, ∃ i, out.limb 0 * addressOfIndex off = addressOfIndex i ∧ R i) ∧
  (∀ off < k, ∃ i, pts.limb 0 * addressOfIndex off = addressOfIndex i ∧ R i) ∧
  ∀ r < k, ∀ off ≤ nt, ∃ i, (chainLast st (l.take r)).cur.limb 0 * addressOfIndex off = addressOfIndex i ∧ R i

/-- What the kernel checks of a placed straight leaf's body, beside `lrlChecks`. -/
def leafB (body : List Stmt) : Bool := (retOf body).isSome && (atomsOf body).all leafAtomOk

set_option maxHeartbeats 1000000 in
/-- **`link_rounds_last__L{nt}_L0_L{k}` completes placed**, `k ≥ 1`. -/
theorem lrl_placed0 {kd nt k : ℕ} {name : String} {f : Fn} (hnt : 1 ≤ nt) (hnt' : nt ≤ 32) (hk0 : k ≠ 0)
    (hfind : coreProgram.find? name = some f) (hlp : coreProgram.loop name = false)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3]) (hbody : f.body = lrLastBody nt 0 k)
    (hck : lrlChecks (lrLastBody nt 0 k) = true) (hleaf : leafB (lrLastBody nt 0 k) = true)
    {R : ℕ → Prop} (rp out pts tabs : E) (st : RSt) (l : List (E × RSt)) (h5 : st.cap.length = 5) (hl : l.length = k)
    (hR : LrlRegion R nt k rp out pts st l) (fp c : ℕ) :
    CallAtA fs al cert kd name [rp, out, pts, tabs] [0] R (fun _ => False) (fun _ => True)
      (fun rd ↦ ReadsAt rd rp st.cells ∧ (0 ≠ 0 → WinTabs rd tabs) ∧ RoundChain rd nt 0 st l ∧
        ReadsAt rd pts (l.map Prod.fst) ∧ ReadsAt rd out (chainLast st l).cells)
      PostQuiet (fs name) fp c c := by
  obtain ⟨c0, c1, c2, c3, c4, cu, cl, hcells, rfl⟩ := cells_eq_seven h5
  rw [← hbody] at hck hleaf
  simp only [lrlChecks, Bool.and_eq_true, List.all_eq_true] at hck
  obtain ⟨⟨hc, hat⟩, hst⟩ := hck
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp hc
  replace hc : chk [rp, out, pts, tabs].length f.body = some c' := hc
  set rs := lrRounds nt 0 2 3 k 11 [4, 5, 6, 7, 8] 9 10 none with hrs
  have hb : f.body = lrlPre nt 0 k ++ [.ret [.n rs.2.2.2.2.1]] := by rw [hbody, lrLastBody_eq hk0]
  have hmemB : ∀ s ∈ lrlPre nt 0 k, s ∈ f.body := fun s hs => by rw [hb]; exact List.mem_append_left _ hs
  have hat' : ∀ a, Stmt.atom a ∈ f.body → mulFwdB a = true ∧ noHint a = true := fun a ha => by
    simpa using hat a (mem_atomsOf' ha)
  have hsum : c + ([] : List ℕ).sum = c := by simp
  rw [← hsum]
  refine callAtA_straight (fun rd => fwdVal rd (fun _ => 0) [rp, out, pts, tabs] f.body) [] [] hfind hlp
    hleaf ⟨by simp, List.Pairwise.nil⟩ (fun _ _ => trivial) (fun _ h => h.elim)
    fun rd _ _ hP => ?_
  obtain ⟨hrp, -, hch, hpts, hout⟩ := hP
  set σ := fwdVal rd (fun _ => 0) [rp, out, pts, tabs] f.body with hσ
  have G : ∀ a, Stmt.atom a ∈ f.body → Good rd (storesOf 4 f.body) (fun _ => 0) σ a := fwd_good hc
  have p0 : σ (.n 0) = rp := fwd_param hc (by norm_num)
  have p1 : σ (.n 1) = out := fwd_param hc (by norm_num)
  have p2 : σ (.n 2) = pts := fwd_param hc (by norm_num)
  have hSp : ∀ d p off, Atom.load d p off ∈ storesOf 4 f.body → p = .n 1 ∨ p = .n 2 := by
    intro d p off h
    simpa [storeOutPtsB] using hst _ h
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
  have hSp' : ∀ d p off, Atom.load d p off ∈ storesOf 4 f.body → p.idx < 3 := fun d p off h => by
    rcases hSp d p off h with rfl | rfl <;> simp
  obtain ⟨hR', hlast, -, -, -⟩ := lrRounds_complete0 (m := 3) (S := storesOf 4 f.body) (w := fun _ => 0)
    (σ := σ) (pts := 2) (tabs := 3) hnt hnt' hSp' k 11 [4, 5, 6, 7, 8] 9 10 none _ l
    (by norm_num) (by norm_num) (fun a ha => G a (hmR a ha))
    (fun d x y ha => by simpa [mulFwdB] using (hat' _ (hmR _ ha)).1)
    (fun z hz => absurd hz (by simp)) hst0 hl hch (by rw [p2]; exact hpts)
  have hLd := lrRounds_loads0 (m := 3) (S := storesOf 4 f.body) (w := fun _ => 0) (σ := σ) (pts := 2) (tabs := 3)
    hnt hnt' hSp' k 11 [4, 5, 6, 7, 8] 9 10 none _ l (by norm_num) (by norm_num) (fun a ha => G a (hmR a ha))
    (fun d x y ha => by simpa [mulFwdB] using (hat' _ (hmR _ ha)).1)
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
  have hatoms : atomsOf f.body = atomsOf (lrlPre nt 0 k) := by rw [hb, atomsOf_append_ret]
  refine ⟨by rw [hparams]; exact fwd_params hc, fun vs hvs => ?_, fun a ha => ⟨?_, ?_⟩, ?_, ?_, fun A hA => ?_⟩
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
      · exact (hrec 0 (by norm_num)).2
      · exact (hrec 1 (by norm_num)).2
      · exact (hrec 2 (by norm_num)).2
      · exact (hrec 3 (by norm_num)).2
      · exact (hrec 4 (by norm_num)).2
      · exact (hrec 5 (by norm_num)).2
      · exact (hrec 6 (by norm_num)).2
    · exact hR' a ha
    · subst ha
      show LoadHolds rd (σ (.n 1)) j _
      rw [p1]; exact hfin j hj
    · rcases ha with rfl | rfl | rfl
      · show LoadHolds rd (σ (.n 1)) 5 _
        rw [p1]; exact h5'
      · show LoadHolds rd (σ (.n 1)) 6 _
        rw [p1]; exact h6'
      · exact hV
  · have := (hat' a ha).2
    cases a with
    | hint _ => simp [noHint] at this
    | _ => trivial
  · rw [hatoms, allocs_atoms]
    refine List.all_eq_true.mpr fun a ha => ?_
    have := (hat' a (hmemB _ (mem_of_mem_atomsOf ha))).2
    cases a with
    | hint h => simp [noHint] at this
    | _ => rfl
  · rw [hatoms, allocDsts_atoms]
    · rfl
    · refine List.all_eq_true.mpr fun a ha => ?_
      have := (hat' a (hmemB _ (mem_of_mem_atomsOf ha))).2
      cases a with
      | hint h => simp [noHint] at this
      | _ => rfl
  · -- the loads
    obtain ⟨d, q, off, hm, rfl⟩ := mem_loadAddrs hA
    rw [hatoms] at hm
    have hm' := mem_of_mem_atomsOf hm
    obtain ⟨hRrp, hRout, hRpts, hRcur⟩ := hR
    simp only [lrlPre, ← hrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range, Stmt.atom.injEq] at hm'
    rcases hm' with (((hm' | hm') | ⟨j, hj, hm'⟩) | hm')
    · have key : ∀ off < 7, ∃ i, (σ (.n 0)).limb 0 * addressOfIndex off = addressOfIndex i ∧
          ((c ≤ i ∧ i < c + ([] : List ℕ).sum) ∨ R i) := fun off h => by
        obtain ⟨i, hi, hRi⟩ := hRrp off h
        exact ⟨i, by rw [p0]; exact hi, Or.inr hRi⟩
      rcases hm' with h | h | h | h | h | h | h <;> obtain ⟨rfl, rfl, rfl⟩ := Atom.load.inj h <;>
        exact key _ (by norm_num)
    · rcases hLd d q off hm' with ⟨rfl, hoff⟩ | ⟨r, hr, hoff, hq⟩
      · obtain ⟨i, hi, hRi⟩ := hRpts off (by omega)
        exact ⟨i, by rw [p2]; exact hi, Or.inr hRi⟩
      · obtain ⟨i, hi, hRi⟩ := hRcur r (by omega) off hoff
        exact ⟨i, by rw [hq]; exact hi, Or.inr hRi⟩
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

end
end LeanVM.Guest.B1.VsC
