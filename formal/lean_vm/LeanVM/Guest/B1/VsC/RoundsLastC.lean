/-
  LeanVM.Guest.B1.VsC.RoundsLastC

  `link_rounds_last` completes layout-free: the record copied, or `k` rounds with no grind.
-/

module

public import LeanVM.Guest.B1.VsC.RoundsC
public import LeanVM.Guest.B1.VsC.RoundsC1
public import LeanVM.Guest.B1.VsC.LinkCallees
public import LeanVM.Guest.B1.Link.RoundsLast
public import LeanVM.Guest.Complete.Call0
import LeanVM.Guest.CoreRef

/-!
# `link_rounds_last`, completely

`LinkRoundsLastComplete0 kd nt bits k name` (`LinkCallees.lean`): on the record `st` at `rp`, a
chain of `k` rounds, its challenges at `pts`, the record after it at `out`, the call returns `0`.

* `lrl0_complete`, `k = 0`: the record copied, on the valuation of the record's words.
* `lrl_complete0`, `k ≥ 1` with no grind: the body's forward evaluation (`fwdVal`), the record's
  loads reading `st`, the rounds holding by `lrRounds_complete0`, the stores writing the chain's
  challenges and last record. What the kernel checks per specialization (`lrlChecks`): the body's
  forward shape, its products forward, no hint, its stores through `out` and `pts` only.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

/-! ## With no words of its own -/

/-- **`link_rounds_last__L{nt}_L{bits}_L{k}` completes with no words of its own** (`CallCompletes0`,
the form the bridge's `callAtA_of_callCompletes0` places): `LinkRoundsLastComplete`'s statement. -/
def LinkRoundsLastComplete0 (kd nt bits k : ℕ) (name : String) : Prop :=
  ∀ (rp out pts tabs : E) (st : RSt) (l : List (E × RSt)), st.cap.length = 5 → l.length = k →
    CallCompletes0 kd name [rp, out, pts, tabs] [0]
      (fun rd ↦ ReadsAt rd rp st.cells ∧ (bits ≠ 0 → WinTabs rd tabs) ∧ RoundChain rd nt bits st l ∧
        ReadsAt rd pts (l.map Prod.fst) ∧ ReadsAt rd out (chainLast st l).cells)
      PostQuiet

theorem LinkRoundsLastComplete0.complete {kd nt bits k : ℕ} {name : String}
    (h : LinkRoundsLastComplete0 kd nt bits k name) : LinkRoundsLastComplete kd nt bits k name :=
  fun rp out pts tabs st l h5 hl => (h rp out pts tabs st l h5 hl).toCallCompletes

/-! ## The record copied -/

/-- **`link_rounds_last__L{nt}_L{bits}_L0` completes**: the record read and stored. -/
theorem lrl0_complete {kd nt bits : ℕ} {name : String} {f : Fn} (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3]) (hbody : f.body = lrLastBody nt bits 0) :
    LinkRoundsLastComplete0 kd nt bits 0 name := by
  intro rp out pts tabs st l h5 hl
  obtain rfl : l = [] := List.eq_nil_of_length_eq_zero hl
  obtain ⟨c0, c1, c2, c3, c4, cu, cl, -, rfl⟩ := cells_eq_seven h5
  let σ : Val := fun v => [rp, out, pts, tabs, c0, c1, c2, c3, c4, cu, cl, 0].getD v.idx 0
  have hb : f.body =
      [.atom (.load (.n 4) (.n 0) 0), .atom (.load (.n 5) (.n 0) 1), .atom (.load (.n 6) (.n 0) 2),
        .atom (.load (.n 7) (.n 0) 3), .atom (.load (.n 8) (.n 0) 4),
        .atom (.load (.n 4) (.n 1) 0), .atom (.load (.n 5) (.n 1) 1), .atom (.load (.n 6) (.n 1) 2),
        .atom (.load (.n 7) (.n 1) 3), .atom (.load (.n 8) (.n 1) 4),
        .atom (.load (.n 9) (.n 0) 5), .atom (.load (.n 9) (.n 1) 5),
        .atom (.load (.n 10) (.n 0) 6), .atom (.load (.n 10) (.n 1) 6),
        .atom (.const (.n 11) (word 0 0))] ++ [.ret [.n 11]] := by
    rw [hbody]; rfl
  refine callCompletes0_straightRd (fun _ => σ) hfind hb (allAtoms_of_isAtomsB (by decide)) rfl
    fun rd _ hP => ?_
  obtain ⟨hrp, -, -, -, hout⟩ := hP
  refine ⟨by rw [hparams]; rfl, by
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact word_zero.symm, ?_⟩
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ⟨hrp _ (by simp [RSt.cells]), trivial⟩
    | exact ⟨hout _ (by simp [RSt.cells, chainLast]), trivial⟩
    | exact ⟨word_zero.symm, trivial⟩

/-! ## Rounds with no grind -/

/-- The body before its `ret`, at `k ≥ 1`. -/
def lrlPre (nt bits k : ℕ) : List Stmt :=
  let rs := lrRounds nt bits 2 3 k 11 [4, 5, 6, 7, 8] 9 10 none
  [.atom (.load (.n 4) (.n 0) 0), .atom (.load (.n 5) (.n 0) 1), .atom (.load (.n 6) (.n 0) 2),
    .atom (.load (.n 7) (.n 0) 3), .atom (.load (.n 8) (.n 0) 4), .atom (.load (.n 9) (.n 0) 5),
    .atom (.load (.n 10) (.n 0) 6)] ++ rs.1 ++
  ((List.range 5).map fun j ↦ .atom (.load (.n (rs.2.1.getD j 0)) (.n 1) j)) ++
  [.atom (.load (.n rs.2.2.1) (.n 1) 5), .atom (.load (.n rs.2.2.2.1) (.n 1) 6),
    .atom (.const (.n rs.2.2.2.2.1) (word 0 0))]

theorem lrLastBody_eq {nt bits k : ℕ} (hk : k ≠ 0) :
    lrLastBody nt bits k = lrlPre nt bits k ++
      [.ret [.n (lrRounds nt bits 2 3 k 11 [4, 5, 6, 7, 8] 9 10 none).2.2.2.2.1]] := by
  simp [lrLastBody, lrlPre, hk]

theorem lrlPre_atoms (nt bits k : ℕ) : AllAtoms (lrlPre nt bits k) := by
  unfold lrlPre
  refine allAtoms_append (allAtoms_append (allAtoms_append ?_ (lrRounds_atoms _ _ _ _ _ _ _ _ _ _))
    (fun s hs ↦ ?_)) ?_
  · intro s hs; simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hs; exact ⟨_, rfl⟩
  · intro s hs; simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- A product whose operands are older than its result. -/
def mulFwdB : Atom → Bool
  | .mul d x y => decide (x.idx < d.idx) && decide (y.idx < d.idx)
  | _ => true

/-- A store through `out` (`.n 1`) or `pts` (`.n 2`). -/
def storeOutPtsB : Atom → Bool
  | .load _ p _ => decide (p = .n 1) || decide (p = .n 2)
  | _ => false

/-- What the kernel checks of `link_rounds_last`'s body. -/
def lrlChecks (body : List Stmt) : Bool :=
  (chk 4 body).isSome && (atomsOf body).all (fun a => mulFwdB a && noHint a) &&
    (storesOf 4 body).all storeOutPtsB

/-- **`link_rounds_last__L{nt}_L0_L{k}` completes**, `k ≥ 1`. -/
theorem lrl_complete0 {kd nt k : ℕ} {name : String} {f : Fn} (hnt : 1 ≤ nt) (hnt' : nt ≤ 32) (hk0 : k ≠ 0)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1, .n 2, .n 3])
    (hbody : f.body = lrLastBody nt 0 k) (hck : lrlChecks (lrLastBody nt 0 k) = true) :
    LinkRoundsLastComplete0 kd nt 0 k name := by
  intro rp out pts tabs st l h5 hl
  obtain ⟨c0, c1, c2, c3, c4, cu, cl, hcells, rfl⟩ := cells_eq_seven h5
  rw [← hbody] at hck
  simp only [lrlChecks, Bool.and_eq_true, List.all_eq_true] at hck
  obtain ⟨⟨hc, hat⟩, hst⟩ := hck
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp hc
  replace hc : chk [rp, out, pts, tabs].length f.body = some c' := hc
  set rs := lrRounds nt 0 2 3 k 11 [4, 5, 6, 7, 8] 9 10 none with hrs
  have hb : f.body = lrlPre nt 0 k ++ [.ret [.n rs.2.2.2.2.1]] := by rw [hbody, lrLastBody_eq hk0]
  have hmemB : ∀ s ∈ lrlPre nt 0 k, s ∈ f.body := fun s hs => by rw [hb]; exact List.mem_append_left _ hs
  have hat' : ∀ a, Stmt.atom a ∈ f.body → mulFwdB a = true ∧ noHint a = true := fun a ha => by
    simpa using hat a (mem_atomsOf' ha)
  have hq : (atomsOf (lrlPre nt 0 k)).all atomQuiet = true := List.all_eq_true.mpr fun a ha => by
    have := (hat' a (hmemB _ (mem_of_mem_atomsOf ha))).2
    cases a with
    | hint _ => simp [noHint] at this
    | _ => rfl
  refine callCompletes0_straightRd (fun rd => fwdVal rd (fun _ => 0) [rp, out, pts, tabs] f.body) hfind hb
    (lrlPre_atoms nt 0 k) hq fun rd _ hP => ?_
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
  obtain ⟨hR, hlast, -, -, -⟩ := lrRounds_complete0 (m := 3) (S := storesOf 4 f.body) (w := fun _ => 0)
    (σ := σ) (pts := 2) (tabs := 3) hnt hnt'
    (fun d p off h => by rcases hSp d p off h with rfl | rfl <;> simp) k 11 [4, 5, 6, 7, 8] 9 10 none _ l
    (by norm_num) (by norm_num) (fun a ha => G a (hmR a ha))
    (fun d x y ha => by simpa [mulFwdB] using (hat' _ (hmR _ ha)).1)
    (fun z hz => absurd hz (by simp)) hst0 hl hch (by rw [p2]; exact hpts)
  -- the record stored
  have hlen : rs.2.1.length = 5 := lrRounds_cap_length _ _ _ _ _ _ _ _ _ _ rfl
  rw [← hrs] at hR hlast
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
  refine ⟨by rw [hparams]; exact fwd_params hc, by simp [hV, word_zero], fun a ha => ⟨?_, ?_⟩⟩
  · have hm := hmemB _ ha
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
    · exact hR a ha
    · subst ha
      show LoadHolds rd (σ (.n 1)) j _
      rw [p1]; exact hfin j hj
    · rcases ha with rfl | rfl | rfl
      · show LoadHolds rd (σ (.n 1)) 5 _
        rw [p1]; exact h5'
      · show LoadHolds rd (σ (.n 1)) 6 _
        rw [p1]; exact h6'
      · exact hV
  · have := (hat' a (hmemB _ ha)).2
    cases a with
    | hint _ => simp [noHint] at this
    | _ => trivial

/-! ## Rounds grinding one bit -/

/-- What the kernel checks of `link_rounds_last`'s body at one bit: its forward shape, its products
forward, no witness hint, its stores through `out` and `pts`, none into a grind's values. -/
def lrlChecks1 (nt k : ℕ) (body : List Stmt) : Bool :=
  (chk 4 body).isSome && (atomsOf body).all (fun a => mulFwdB a && atomQuiet a) &&
    (storesOf 4 body).all storeOutPtsB &&
    (storesOf 4 body).all fun a => (List.range k).all fun r =>
      !loadInto (lrOg nt 2 3 r 11 [4, 5, 6, 7, 8] 9 10 none)
        (lrOg nt 2 3 r 11 [4, 5, 6, 7, 8] 9 10 none + (gcLen 1 - 2)) a

/-- **`link_rounds_last__L{nt}_L1_L{k}` completes**, `k ≥ 1`, on a memory defined on its first
`2^11` words at least (the grinds' range checks). -/
theorem lrl_complete1 {kd nt k : ℕ} {name : String} {f : Fn} (hkd : 11 ≤ kd) (hnt : 1 ≤ nt)
    (hnt' : nt ≤ 32) (hk3 : nt % 4 ≠ 3) (hk0 : k ≠ 0)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1, .n 2, .n 3])
    (hbody : f.body = lrLastBody nt 1 k) (hck : lrlChecks1 nt k (lrLastBody nt 1 k) = true)
    (hog : ((List.range k).map fun r => lrOg nt 2 3 r 11 [4, 5, 6, 7, 8] 9 10 none).Pairwise
      (fun a b => a + gcW 1 < b)) :
    LinkRoundsLastComplete0 kd nt 1 k name := by
  intro rp out pts tabs st l h5 hl
  obtain ⟨c0, c1, c2, c3, c4, cu, cl, hcells, rfl⟩ := cells_eq_seven h5
  rw [← hbody] at hck
  simp only [lrlChecks1, Bool.and_eq_true, List.all_eq_true] at hck
  obtain ⟨⟨⟨hc, hat⟩, hst⟩, hsg⟩ := hck
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp hc
  replace hc : chk [rp, out, pts, tabs].length f.body = some c' := hc
  set rs := lrRounds nt 1 2 3 k 11 [4, 5, 6, 7, 8] 9 10 none with hrs
  have hb : f.body = lrlPre nt 1 k ++ [.ret [.n rs.2.2.2.2.1]] := by rw [hbody, lrLastBody_eq hk0]
  have hmemB : ∀ s ∈ lrlPre nt 1 k, s ∈ f.body := fun s hs => by rw [hb]; exact List.mem_append_left _ hs
  have hat' : ∀ a, Stmt.atom a ∈ f.body → mulFwdB a = true ∧ atomQuiet a = true := fun a ha => by
    simpa using hat a (mem_atomsOf' ha)
  have hq : (atomsOf (lrlPre nt 1 k)).all atomQuiet = true := List.all_eq_true.mpr fun a ha =>
    (hat' a (hmemB _ (mem_of_mem_atomsOf ha))).2
  let ogs : ℕ → ℕ := fun r => lrOg nt 2 3 r 11 [4, 5, 6, 7, 8] 9 10 none
  let ps : Reader → List (ℕ × E) := fun rd => (List.range k).map fun r =>
    (ogs r, roundWord rd nt (chainLast ⟨[c0, c1, c2, c3, c4], cu, cl⟩ (l.take r)))
  refine callCompletes0_straightRd (fun rd => fwdVal rd (winOracle (ps rd)) [rp, out, pts, tabs] f.body) hfind hb
    (lrlPre_atoms nt 1 k) hq fun rd hlow hP => ?_
  obtain ⟨hrp, hwt, hch, hpts, hout⟩ := hP
  set σ := fwdVal rd (winOracle (ps rd)) [rp, out, pts, tabs] f.body with hσ
  have G : ∀ a, Stmt.atom a ∈ f.body → Good rd (storesOf 4 f.body) (winOracle (ps rd)) σ a := fwd_good hc
  have p3 : σ (.n 3) = tabs := fwd_param hc (by norm_num)
  have hW : ∀ r < k, ∀ j ≤ gcW 1, winOracle (ps rd) (ogs r + j) =
      gcWin 1 (roundWord rd nt (chainLast ⟨[c0, c1, c2, c3, c4], cu, cl⟩ (l.take r))) j := by
    intro r hr j hj
    refine winOracle_at (p := (ogs r, _)) ?_ (List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩) hj
    simpa [ps, List.map_map, Function.comp_def] using hog
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
  obtain ⟨hR, hlast, -, -, -, -⟩ := lrRounds_complete1 (m := 3) (S := storesOf 4 f.body)
    (w := winOracle (ps rd)) (σ := σ) (pts := 2) (tabs := 3) hnt hnt' hk3
    (fun d p off h => by rcases hSp d p off h with rfl | rfl <;> simp) (hrc_of_lowDef hlow hkd)
    (by rw [p3]; exact hwt one_ne_zero) k 11 [4, 5, 6, 7, 8] 9 10 none _ l
    (by norm_num) (by norm_num) (by norm_num) (fun a ha => G a (hmR a ha))
    (fun d x y ha => by simpa [mulFwdB] using (hat' _ (hmR _ ha)).1)
    (fun a ha r hr => by simpa using hsg a ha r (List.mem_range.mpr hr)) hW
    (fun z hz => absurd hz (by simp)) hst0 hl hch (by rw [p2]; exact hpts)
  -- the record stored
  have hlen : rs.2.1.length = 5 := lrRounds_cap_length _ _ _ _ _ _ _ _ _ _ rfl
  rw [← hrs] at hR hlast
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
  refine ⟨by rw [hparams]; exact fwd_params hc, by simp [hV, word_zero], fun a ha => ?_⟩
  · simp only [lrlPre, ← hrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
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
    · exact ⟨(hR a ha).1, (hR a ha).2 rd⟩
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


/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem lrl_L1_L0_L0_complete (kd : ℕ) : LinkRoundsLastComplete0 kd 1 0 0 "link_rounds_last__L1_L0_L0" :=
  lrl0_complete (coreProgram_find?_at (j := idx% «link_rounds_last__L1_L0_L0») rfl) rfl lrl_L1_L0_L0_body

set_option maxRecDepth 100000 in
theorem lrl_L6_L0_L0_complete (kd : ℕ) : LinkRoundsLastComplete0 kd 6 0 0 "link_rounds_last__L6_L0_L0" :=
  lrl0_complete (coreProgram_find?_at (j := idx% «link_rounds_last__L6_L0_L0») rfl) rfl lrl_L6_L0_L0_body

set_option maxRecDepth 100000 in
theorem lrl_L7_L0_L0_complete (kd : ℕ) : LinkRoundsLastComplete0 kd 7 0 0 "link_rounds_last__L7_L0_L0" :=
  lrl0_complete (coreProgram_find?_at (j := idx% «link_rounds_last__L7_L0_L0») rfl) rfl lrl_L7_L0_L0_body

set_option maxRecDepth 100000 in
theorem lrl_L8_L1_L0_complete (kd : ℕ) : LinkRoundsLastComplete0 kd 8 1 0 "link_rounds_last__L8_L1_L0" :=
  lrl0_complete (coreProgram_find?_at (j := idx% «link_rounds_last__L8_L1_L0») rfl) rfl lrl_L8_L1_L0_body

set_option maxRecDepth 100000 in
theorem lrl_L9_L1_L0_complete (kd : ℕ) : LinkRoundsLastComplete0 kd 9 1 0 "link_rounds_last__L9_L1_L0" :=
  lrl0_complete (coreProgram_find?_at (j := idx% «link_rounds_last__L9_L1_L0») rfl) rfl lrl_L9_L1_L0_body

set_option maxRecDepth 100000 in
theorem lrl_L10_L1_L0_complete (kd : ℕ) : LinkRoundsLastComplete0 kd 10 1 0 "link_rounds_last__L10_L1_L0" :=
  lrl0_complete (coreProgram_find?_at (j := idx% «link_rounds_last__L10_L1_L0») rfl) rfl lrl_L10_L1_L0_body

set_option maxRecDepth 100000 in
theorem lrl_L1_L0_L1_complete (kd : ℕ) : LinkRoundsLastComplete0 kd 1 0 1 "link_rounds_last__L1_L0_L1" :=
  lrl_complete0 (by decide) (by decide) (by decide)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L1_L0_L1») rfl) rfl lrl_L1_L0_L1_body (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L1_L0_L2_complete (kd : ℕ) : LinkRoundsLastComplete0 kd 1 0 2 "link_rounds_last__L1_L0_L2" :=
  lrl_complete0 (by decide) (by decide) (by decide)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L1_L0_L2») rfl) rfl lrl_L1_L0_L2_body (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L1_L0_L3_complete (kd : ℕ) : LinkRoundsLastComplete0 kd 1 0 3 "link_rounds_last__L1_L0_L3" :=
  lrl_complete0 (by decide) (by decide) (by decide)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L1_L0_L3») rfl) rfl lrl_L1_L0_L3_body (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L6_L0_L1_complete (kd : ℕ) : LinkRoundsLastComplete0 kd 6 0 1 "link_rounds_last__L6_L0_L1" :=
  lrl_complete0 (by decide) (by decide) (by decide)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L6_L0_L1») rfl) rfl lrl_L6_L0_L1_body (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L6_L0_L2_complete (kd : ℕ) : LinkRoundsLastComplete0 kd 6 0 2 "link_rounds_last__L6_L0_L2" :=
  lrl_complete0 (by decide) (by decide) (by decide)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L6_L0_L2») rfl) rfl lrl_L6_L0_L2_body (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L6_L0_L3_complete (kd : ℕ) : LinkRoundsLastComplete0 kd 6 0 3 "link_rounds_last__L6_L0_L3" :=
  lrl_complete0 (by decide) (by decide) (by decide)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L6_L0_L3») rfl) rfl lrl_L6_L0_L3_body (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L7_L0_L1_complete (kd : ℕ) : LinkRoundsLastComplete0 kd 7 0 1 "link_rounds_last__L7_L0_L1" :=
  lrl_complete0 (by decide) (by decide) (by decide)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L7_L0_L1») rfl) rfl lrl_L7_L0_L1_body (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L7_L0_L2_complete (kd : ℕ) : LinkRoundsLastComplete0 kd 7 0 2 "link_rounds_last__L7_L0_L2" :=
  lrl_complete0 (by decide) (by decide) (by decide)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L7_L0_L2») rfl) rfl lrl_L7_L0_L2_body (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L7_L0_L3_complete (kd : ℕ) : LinkRoundsLastComplete0 kd 7 0 3 "link_rounds_last__L7_L0_L3" :=
  lrl_complete0 (by decide) (by decide) (by decide)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L7_L0_L3») rfl) rfl lrl_L7_L0_L3_body (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L8_L1_L1_complete (kd : ℕ) (hkd : 11 ≤ kd) :
    LinkRoundsLastComplete0 kd 8 1 1 "link_rounds_last__L8_L1_L1" :=
  lrl_complete1 hkd (by decide) (by decide) (by decide) (by decide)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L8_L1_L1») rfl) rfl lrl_L8_L1_L1_body (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L8_L1_L2_complete (kd : ℕ) (hkd : 11 ≤ kd) :
    LinkRoundsLastComplete0 kd 8 1 2 "link_rounds_last__L8_L1_L2" :=
  lrl_complete1 hkd (by decide) (by decide) (by decide) (by decide)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L8_L1_L2») rfl) rfl lrl_L8_L1_L2_body (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L8_L1_L3_complete (kd : ℕ) (hkd : 11 ≤ kd) :
    LinkRoundsLastComplete0 kd 8 1 3 "link_rounds_last__L8_L1_L3" :=
  lrl_complete1 hkd (by decide) (by decide) (by decide) (by decide)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L8_L1_L3») rfl) rfl lrl_L8_L1_L3_body (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L9_L1_L1_complete (kd : ℕ) (hkd : 11 ≤ kd) :
    LinkRoundsLastComplete0 kd 9 1 1 "link_rounds_last__L9_L1_L1" :=
  lrl_complete1 hkd (by decide) (by decide) (by decide) (by decide)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L9_L1_L1») rfl) rfl lrl_L9_L1_L1_body (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L9_L1_L2_complete (kd : ℕ) (hkd : 11 ≤ kd) :
    LinkRoundsLastComplete0 kd 9 1 2 "link_rounds_last__L9_L1_L2" :=
  lrl_complete1 hkd (by decide) (by decide) (by decide) (by decide)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L9_L1_L2») rfl) rfl lrl_L9_L1_L2_body (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L9_L1_L3_complete (kd : ℕ) (hkd : 11 ≤ kd) :
    LinkRoundsLastComplete0 kd 9 1 3 "link_rounds_last__L9_L1_L3" :=
  lrl_complete1 hkd (by decide) (by decide) (by decide) (by decide)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L9_L1_L3») rfl) rfl lrl_L9_L1_L3_body (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L10_L1_L1_complete (kd : ℕ) (hkd : 11 ≤ kd) :
    LinkRoundsLastComplete0 kd 10 1 1 "link_rounds_last__L10_L1_L1" :=
  lrl_complete1 hkd (by decide) (by decide) (by decide) (by decide)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L10_L1_L1») rfl) rfl lrl_L10_L1_L1_body (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L10_L1_L2_complete (kd : ℕ) (hkd : 11 ≤ kd) :
    LinkRoundsLastComplete0 kd 10 1 2 "link_rounds_last__L10_L1_L2" :=
  lrl_complete1 hkd (by decide) (by decide) (by decide) (by decide)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L10_L1_L2») rfl) rfl lrl_L10_L1_L2_body (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L10_L1_L3_complete (kd : ℕ) (hkd : 11 ≤ kd) :
    LinkRoundsLastComplete0 kd 10 1 3 "link_rounds_last__L10_L1_L3" :=
  lrl_complete1 hkd (by decide) (by decide) (by decide) (by decide)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L10_L1_L3») rfl) rfl lrl_L10_L1_L3_body (by decide +kernel) (by decide +kernel)

end
end LeanVM.Guest.B1.VsC
