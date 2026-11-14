/-
  LeanVM.Guest.B1.Place.SqAtE

  `open_stacked`'s squeeze loop placed by trees popping nothing whose every node is exact on the memory.
-/

module

public import LeanVM.Guest.B1.Place.SqAt
public import LeanVM.Guest.B1.Main.RelAtInE
public import LeanVM.Guest.Exact.Free
public import LeanVM.Guest.Memory.PopsNil

/-!
# The squeeze loop, placed and exact

The loop helper's body has no hint (`sqLoopPre_hints`), so its paths pop nothing and are exact (`evs_noHint`); its
decoders are exact by `QwDecodeAtDE`. `sqLoop_iterE`, `sqLoop_relAtInE`: `sqLoop_iter`, `sqLoop_relAtIn` by such trees.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- A statement's hint. -/
def hintS : Stmt → Option Hint
  | .atom (.hint h) => some h
  | _ => none

/-- **A straight run with no hint** pops nothing and is exact, on every reader. -/
theorem evs_noHint {σ : Val} {pre : List Stmt} (h : pre.filterMap hintS = []) :
    ∀ e ∈ pre.flatMap (Main.slEvs σ), e.noWit ∧ ∀ rd, e.Exact rd σ := by
  intro e he
  obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp he
  have hn : hintS s = none := List.filterMap_eq_nil_iff.mp h s hs
  cases s with
  | atom a =>
    simp only [Main.slEvs, List.mem_singleton] at he
    subst he
    cases a with
    | hint => simp [hintS] at hn
    | _ => exact ⟨rfl, fun _ => trivial⟩
  | call f args rets =>
    simp only [Main.slEvs, List.mem_singleton] at he
    subst he
    exact ⟨trivial, fun _ => trivial⟩
  | callIf c f args =>
    simp only [Main.slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact ⟨trivial, fun _ => trivial⟩
    · split <;> exact ⟨trivial, fun _ => trivial⟩
  | _ => simp [Main.slEvs] at he

/-- **A straight run whose hints are none computed** is exact, on every reader. -/
theorem evs_exact_of_hints {σ : Val} {pre : List Stmt}
    (h : ∀ x ∈ pre.filterMap hintS, isComputed (.hint x) = false) :
    ∀ e ∈ pre.flatMap (Main.slEvs σ), ∀ rd, e.Exact rd σ := by
  intro e he rd
  obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp he
  cases s with
  | atom a =>
    simp only [Main.slEvs, List.mem_singleton] at he
    subst he
    cases a with
    | hint x => exact exact_of_not_computed (h x (List.mem_filterMap.mpr ⟨_, hs, rfl⟩))
    | _ => trivial
  | call f args rets =>
    simp only [Main.slEvs, List.mem_singleton] at he
    subst he
    trivial
  | callIf c f args =>
    simp only [Main.slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · trivial
    · split <;> trivial
  | _ => simp [Main.slEvs] at he

theorem sqLoopPre_hints (lv : OsLv) (name : String) : (sqLoopPre lv name).filterMap hintS = [] := by
  simp only [sqLoopPre, sqLoopA, List.filterMap_append,
    fm_pow_nil hintS (fun _ _ _ => rfl),
    fm_mat_nil hintS (fun _ _ _ => rfl) (fun _ _ => rfl),
    List.append_nil]
  rfl

theorem RelAtInCT.dmono' {P : Core.Program} {fs : String → ℕ} {cert : String → V → ℕ} {rd : Reader}
    {R D D' : ℕ → Prop} {fp c B n : ℕ} {f : String} {args rets : List E} {T : Tree → Prop}
    (h : RelAtInCT P fs cert rd R D fp c B n f args rets T) (hD : ∀ i, D' i → D i) :
    RelAtInCT P fs cert rd R D' fp c B n f args rets T :=
  let ⟨t, ⟨hn, hv, hb, hp, hB, ht, hl, hd⟩, hT⟩ := h
  ⟨t, ⟨hn, hv, hb, hp, hB, ht, hl, fun i hi => hd i (hD i hi)⟩, hT⟩

/-- **One iteration of a squeeze loop, placed at `(fp, c)` and exact**: its decoder at `c`, its tail's frames
at `fp + fs L` and the rest after the decoder (or skipped at the last), its loads through the row
in `R`. -/
theorem sqLoop_iterE (fs : String → ℕ) (cert : String → V → ℕ) {lv : OsLv} {name : String}
    {fn : Fn} (hfind : coreProgram.find? name = some fn) (hp : fn.params = osParams 6)
    (hb : fn.body = sqLoopBody lv name) (hlp : coreProgram.loop name = true) (hit : SqIterC lv)
    {rd : Reader} {R Rd Dd Dt : ℕ → Prop} {X N sqz qpos qbp tabs : E}
    {cap : List E} (hcl : cap.length = 5) (fp c : ℕ) {Bt m : ℕ}
    (hrow : ∀ i < 5, LoadHolds rd (sqz * X ^ 5) i (cap.getD i 0))
    (hnext : ∀ i < 5, LoadHolds rd (sqz * X ^ 5) (5 + i) ((⟨cap, []⟩ : Fs).squeeze.2.cap.getD i 0))
    (hdec : RelAtInPE coreProgram fs cert rd (ExactAt coreProgram rd) Rd Dd c (fs (sqDecName lv))
      (sqDecName lv) [(⟨cap, []⟩ : Fs).squeeze.1, qpos * gen ^ lv.posOff * X ^ (128 / lv.depth),
        qbp * gen ^ lv.posOff * X ^ (128 / lv.depth), tabs] [] [])
    (hRd : ∀ i, Rd i → R i) (hK : IsInK (X * gen + N))
    (htail : if X * gen + N ≠ 0 then
      RelAtInCPE coreProgram fs cert rd (ExactAt coreProgram rd) R Dt (fp + fs name) (c + fs (sqDecName lv)) Bt m
        name [X * gen, N, sqz, qpos, qbp, tabs] [] []
      else Bt = fs name ∧ m = 0)
    (hreg : ∀ t < 10, ∃ i, (sqz * X ^ 5).limb 0 * Parameters.addressOfIndex t =
        Parameters.addressOfIndex i ∧ R i) :
    RelAtInCPE coreProgram fs cert rd (ExactAt coreProgram rd) R (fun i => Dd i ∨ (X * gen + N ≠ 0 ∧ Dt i)) fp c
      (fs name + Bt) (fs (sqDecName lv) + m) name [X, N, sqz, qpos, qbp, tabs] [] [] := by
  obtain ⟨σ, hpar, hA, h8, hdargs, hg, hta⟩ := hit rd X N sqz qpos qbp tabs cap hcl hrow hnext
  have hpre : fn.body = sqLoopPre lv name ++ [.ret []] := hb.trans (sqLoopBody_pre lv name)
  have hst := sqLoopPre_straight lv name
  set es := (sqLoopPre lv name).flatMap (Main.slEvs σ) with hes_def
  have hw : walk σ fn.body = .ret es [] := by rw [hpre]; exact Main.walk_straight σ [] _ hst
  have hholds : Stmt.HoldsList (fun _ _ _ => True) rd σ fn.body False (fun rs => rs = []) := by
    rw [hpre, holdsList_flat_ret _ (sqLoopPre_flat lv name)]
    refine ⟨?_, rfl⟩
    rw [sqLoopPre, allOk_append]
    refine ⟨hA, allOk_cons.mpr ⟨⟨by rw [hg]; exact hK, fun _ => trivial⟩, allOk_nil⟩⟩
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    have := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hfind))
      hholds
    rw [hw] at this
    exact fun e he => (this.1 e he).1
  obtain ⟨had, hal, hadr, hcl'⟩ := Main.straight_parts σ _ hst
  have hal0 : allocs σ es = [] := by rw [hal, sqLoopPre_allocs]; rfl
  have hcalls : calls es = [⟨sqDecName lv, sqDecArgs lv, [], true⟩] ++
      [⟨name, sqTailArgs lv, [], decide (σ (.n (sqLoopE lv + 2)) ≠ 0)⟩] := by
    rw [hcl', sqLoopPre_calls]; rfl
  have hno := evs_noHint (σ := σ) (sqLoopPre_hints lv name)
  have h := relAtInPE_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (Q := ExactAt coreProgram rd) (pss := [[]]) (pt := []) (ps := [])
    coreProgram_wf (R := R) (D := fun i => Dd i ∨ (X * gen + N ≠ 0 ∧ Dt i))
    (Dk := fun i => False ∨ (true = true ∧ Dd i)) (Rt := R) (Dt := Dt) (fp := fp) (c := c)
    (Bt := Bt) (m := m)
    (N := fs (sqDecName lv)) (args := [X, N, sqz, qpos, qbp, tabs]) (rets := [])
    hfind hlp (by rw [hp]; exact hpar) hw rfl hev hcalls ?_
    (by rw [had, sqLoopPre_allocs, hal0]; rfl)
    (fun q hq' => by rw [hadr, sqLoopPre_addrs] at hq'; simp at hq')
    ?_ (fun i hi => Or.inl hi) (fun A hA => ?_) ?_
    (splice_nil_of _ _ (fun e he => (hno e he).1) (by simp))
    (exactAt_of_walk hfind hw fun e he => (hno e he).2 rd)
  · rwa [hal0, List.sum_nil, Nat.zero_add] at h
  · rw [hal0, List.sum_nil, Nat.add_zero]
    simp only [hg]
    split
    · next hc =>
      have hne : X * gen + N ≠ 0 := by simpa using hc
      rw [List.map_nil, hta]
      simpa [hne] using htail
    · next hc =>
      have h0 : X * gen + N = 0 := by simpa using hc
      simp only [h0, ne_eq, not_true_eq_false, ↓reduceIte] at htail
      exact ⟨htail.1, htail.2, by trivial⟩
  · rw [hal0, List.sum_nil, Nat.add_zero]
    refine ⟨fs (sqDecName lv), 0, Rd, Dd, rfl, fun i hi => Or.inl (Or.inl (hRd i hi)), ?_, rfl,
      fun i hi => hi⟩
    simp only [↓reduceIte, List.map_nil]
    rw [hdargs]; exact hdec
  · rw [loadAddrs_straight σ _ hst] at hA
    obtain ⟨⟨p, off⟩, hq', rfl⟩ := List.mem_map.mp hA
    have hql := sqLoopPre_loads lv name _ hq'
    obtain ⟨i, hi, hR⟩ := hreg off hql.2
    refine ⟨i, ?_, Or.inr (Or.inl hR)⟩
    have hp8 : p = .n 9 := hql.1
    rw [hp8, h8]; exact hi
  · intro i hi
    rcases hi with hi | ⟨ht, hi⟩
    · exact Or.inr (Or.inl (Or.inr ⟨rfl, hi⟩))
    · refine Or.inr (Or.inr ⟨?_, hi⟩)
      simp only [hg]
      exact decide_eq_true ht

/-- **A level's squeeze loop, placed and exact** from its first iteration `x = g^e` at `fp`, `m = n - e`
iterations: on every memory holding the capacities `cap j` in the rows `sqz·(g^j)^5` (each the
previous one's squeeze), the window table at `tabs` and, at `qpos` and `qbp`, what each decoder
stores (the positions and the pointers into its `wins` run at `sqDecAt`), the loop holds, its
decoders' runs its data (`sqRuns`, decoder `t` decoding `w t`, the word of squeeze `e + t`). -/
theorem sqLoop_relAtInE (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {lv : OsLv}
    {name : String} {fn : Fn} (hfind : coreProgram.find? name = some fn)
    (hp : fn.params = osParams 6) (hb : fn.body = sqLoopBody lv name)
    (hlp : coreProgram.loop name = true) (hit : SqIterC lv)
    (hdec : QwDecodeAtDE fs cert k lv.depth lv.capDepth (sqDecName lv))
    {e n : ℕ} (hen : e < n) (hn' : n < ordG) {sqz qpos qbp tabs : E} {cap : ℕ → List E}
    (hcl : ∀ j, (cap j).length = 5) {Lin : Layout} (fp : ℕ)
    (hmem : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j, e ≤ j → j < n →
      (∀ i < 5, LoadHolds rd (sqz * (gen ^ j) ^ 5) i ((cap j).getD i 0)) ∧
        ∀ i < 5, LoadHolds rd (sqz * (gen ^ j) ^ 5) (5 + i)
          (((⟨cap j, []⟩ : Fs).squeeze.2.cap).getD i 0))
    (hdmem : ∀ rd, LowDef k rd → MemL rd Lin → WinTabs rd tabs ∧ ∀ t < n - e, ∀ i < 128 / lv.depth,
      LoadHolds rd (qpos * gen ^ lv.posOff * (gen ^ (e + t)) ^ (128 / lv.depth)) i
          (eOfNat (qwPosOf lv.depth ((⟨cap (e + t), []⟩ : Fs).squeeze.1) i)) ∧
        LoadHolds rd (qbp * gen ^ lv.posOff * (gen ^ (e + t)) ^ (128 / lv.depth)) i
          (qwPtrAt cert (sqDecName lv) (sqDecAt fs lv name (n - e) fp t) lv.depth lv.capDepth i))
    (hreg : ∀ j, e ≤ j → j < n → ∀ t < 10, ∃ i,
      (sqz * (gen ^ j) ^ 5).limb 0 * Parameters.addressOfIndex t =
        Parameters.addressOfIndex i ∧ RegionL Lin i)
    (hregd : ∀ t < n - e, QwRegs lv.depth [(⟨cap (e + t), []⟩ : Fs).squeeze.1,
        qpos * gen ^ lv.posOff * (gen ^ (e + t)) ^ (128 / lv.depth),
        qbp * gen ^ lv.posOff * (gen ^ (e + t)) ^ (128 / lv.depth), tabs] (RegionL Lin)) :
    ∃ Lown : Layout,
      Within (sqRuns fs cert lv name (n - e) fp (fun t ↦ (⟨cap (e + t), []⟩ : Fs).squeeze.1) 0 ++ Lown)
        fp (sqTot fs lv name (n - e) 0) ∧
      DisjL (sqRuns fs cert lv name (n - e) fp (fun t ↦ (⟨cap (e + t), []⟩ : Fs).squeeze.1) 0 ++ Lown) ∧
      ∀ rd, LowDef k rd →
        MemL rd (sqRuns fs cert lv name (n - e) fp (fun t ↦ (⟨cap (e + t), []⟩ : Fs).squeeze.1) 0 ++
          Lown ++ Lin) →
        RelAtInPE coreProgram fs cert rd (ExactAt coreProgram rd) (RegionL Lin)
          (RegionL (sqRuns fs cert lv name (n - e) fp (fun t ↦ (⟨cap (e + t), []⟩ : Fs).squeeze.1) 0))
          fp (sqTot fs lv name (n - e) 0) name [gen ^ e, gen ^ n, sqz, qpos, qbp, tabs] [] [] := by
  have hn2 : n < 2 ^ 64 - 1 := hn'
  set m := n - e with hm
  set w : ℕ → E := fun t ↦ (⟨cap (e + t), []⟩ : Fs).squeeze.1 with hwdef
  have hdecj : ∀ t < m, ∃ Lj : Layout,
      Within (qwRunL cert (sqDecName lv) (sqDecAt fs lv name m fp t) lv.depth lv.capDepth (w t) ++ Lj)
        (sqDecAt fs lv name m fp t) (fs (sqDecName lv)) ∧
      DisjL (qwRunL cert (sqDecName lv) (sqDecAt fs lv name m fp t) lv.depth lv.capDepth (w t) ++ Lj) ∧
      ∀ rd, LowDef k rd →
        MemL rd (qwRunL cert (sqDecName lv) (sqDecAt fs lv name m fp t) lv.depth lv.capDepth (w t) ++
          Lj ++ Lin) →
        RelAtInPE coreProgram fs cert rd (ExactAt coreProgram rd) (RegionL Lin)
          (RegionL (qwRunL cert (sqDecName lv) (sqDecAt fs lv name m fp t) lv.depth lv.capDepth (w t)))
          (sqDecAt fs lv name m fp t) (fs (sqDecName lv)) (sqDecName lv)
          [w t, qpos * gen ^ lv.posOff * (gen ^ (e + t)) ^ (128 / lv.depth),
            qbp * gen ^ lv.posOff * (gen ^ (e + t)) ^ (128 / lv.depth), tabs] [] [] := fun t ht =>
    hdec _ _ _ _ Lin _ (hregd t ht) fun rd hl hmm =>
      ⟨(hdmem rd hl hmm).1, fun i hi => (hdmem rd hl hmm).2 t ht i hi⟩
  classical
  let Lj : ℕ → Layout := fun t => if h : t < m then Classical.choose (hdecj t h) else []
  have hLj : ∀ t (h : t < m), Lj t = Classical.choose (hdecj t h) := fun t h => by simp [Lj, h]
  let Lown : Layout := ((List.range m).map Lj).flatten
  refine ⟨Lown, ?_, ?_, fun rd hlow hL => ?_⟩
  · rw [within_append]
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · simp only [sqRuns, List.mem_flatten, List.mem_map, List.mem_range] at hq
      obtain ⟨_, ⟨t, ht, rfl⟩, hq⟩ := hq
      simp only [Nat.zero_add] at hq
      have hw := (Classical.choose_spec (hdecj t (by omega))).1 q (List.mem_append_left _ hq)
      have := sqDecAt_le fs lv name fp (m := m) (t := t) (by omega)
      have : fp ≤ sqDecAt fs lv name m fp t := by unfold sqDecAt; omega
      omega
    · simp only [Lown, List.mem_flatten, List.mem_map, List.mem_range] at hq
      obtain ⟨_, ⟨t, ht, rfl⟩, hq⟩ := hq
      rw [hLj t ht] at hq
      have hw := (Classical.choose_spec (hdecj t ht)).1 q (List.mem_append_right _ hq)
      have := sqDecAt_le fs lv name fp (m := m) (t := t) ht
      have : fp ≤ sqDecAt fs lv name m fp t := by unfold sqDecAt; omega
      omega
  · have e1 : sqRuns fs cert lv name m fp w 0 =
        ((List.range m).map fun t =>
          qwRunL cert (sqDecName lv) (sqDecAt fs lv name m fp t) lv.depth lv.capDepth (w t)).flatten := by
      simp [sqRuns]
    rw [e1]
    refine os_disj_windows _ Lj (fun t => sqDecAt fs lv name m fp t) (fun _ => fs (sqDecName lv))
      (fun t ht => ?_) (fun t ht => ?_) (fun i hi j hj hij => ?_)
    · rw [hLj t ht]; exact (Classical.choose_spec (hdecj t ht)).2.1
    · rw [hLj t ht]; exact (Classical.choose_spec (hdecj t ht)).1
    · unfold sqDecAt
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · left
        have : (i + 1) * fs (sqDecName lv) ≤ j * fs (sqDecName lv) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.succ_mul] at this
        omega
      · right
        have : (j + 1) * fs (sqDecName lv) ≤ i * fs (sqDecName lv) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.succ_mul] at this
        omega
  obtain ⟨h12, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hR, hO⟩ := Main.memL_append.mp h12
  have hd := hmem rd hlow hLin
  have hrel : ∀ t (ht : t < m), RelAtInPE coreProgram fs cert rd (ExactAt coreProgram rd) (RegionL Lin)
      (RegionL (qwRunL cert (sqDecName lv) (sqDecAt fs lv name m fp t) lv.depth lv.capDepth (w t)))
      (sqDecAt fs lv name m fp t) (fs (sqDecName lv)) (sqDecName lv)
      [w t, qpos * gen ^ lv.posOff * (gen ^ (e + t)) ^ (128 / lv.depth),
        qbp * gen ^ lv.posOff * (gen ^ (e + t)) ^ (128 / lv.depth), tabs] [] [] := fun t ht => by
    refine (Classical.choose_spec (hdecj t ht)).2.2 rd hlow
      (Main.memL_append.mpr ⟨Main.memL_append.mpr ⟨?_, ?_⟩, hLin⟩)
    · intro q hq
      exact hR q (by
        simp only [sqRuns, List.mem_flatten, List.mem_map, List.mem_range]
        exact ⟨_, ⟨t, ht, by simp⟩, hq⟩)
    · intro q hq
      rw [← hLj t ht] at hq
      exact hO q (by
        simp only [Lown, List.mem_flatten, List.mem_map, List.mem_range]
        exact ⟨_, ⟨t, ht, rfl⟩, hq⟩)
  have hKj : ∀ j, IsInK (gen ^ j * gen + gen ^ n) := fun j =>
    isInK_add (by rw [gen_pow_mul_gen]; exact gen_pow_isInK _) (gen_pow_isInK _)
  have hstep : ∀ s t, t + s + 1 = m →
      RelAtInCPE coreProgram fs cert rd (ExactAt coreProgram rd) (RegionL Lin)
        (fun i => RegionL (sqRuns fs cert lv name m fp w t) i)
        (fp + t * fs name) (sqDecAt fs lv name m fp t) ((m - t + 1) * fs name)
        ((m - t) * fs (sqDecName lv)) name [gen ^ (e + t), gen ^ n, sqz, qpos, qbp, tabs] [] [] := by
    intro s
    induction s with
    | zero =>
      intro t ht
      obtain ⟨hr0, hn0⟩ := hd (e + t) (by omega) (by omega)
      have h0 : gen ^ (e + t) * gen + gen ^ n = 0 := by
        rw [gen_pow_add_eq_zero_iff]; congr 1; omega
      have := sqLoop_iterE fs cert hfind hp hb hlp hit (rd := rd) (R := RegionL Lin)
        (Dt := fun _ => False) (N := gen ^ n) (sqz := sqz) (qpos := qpos) (qbp := qbp) (tabs := tabs)
        (hcl (e + t)) (fp + t * fs name) (sqDecAt fs lv name m fp t) (Bt := fs name) (m := 0) hr0 hn0
        (hrel t (by omega)) (fun i h => h) (hKj (e + t)) (by simp [h0])
        (fun t' ht' => hreg (e + t) (by omega) (by omega) t' ht')
      rw [show (m - t + 1) * fs name = fs name + fs name by rw [show m - t = 1 by omega]; ring,
        show (m - t) * fs (sqDecName lv) = fs (sqDecName lv) + 0 by rw [show m - t = 1 by omega]; ring]
      refine RelAtInCT.dmono' this fun i hi => ?_
      obtain ⟨t', h1, h2, hi'⟩ := regionL_sqRuns.mp hi
      obtain rfl : t' = t := by omega
      exact Or.inl hi'
    | succ s ih =>
      intro t ht
      obtain ⟨hr0, hn0⟩ := hd (e + t) (by omega) (by omega)
      have hne : gen ^ (e + t) * gen + gen ^ n ≠ 0 := by
        rw [ne_eq, gen_pow_add_eq_zero_iff]
        intro he
        have := gen_pow_inj (by omega) (by omega) he
        omega
      have ht' := ih (t + 1) (by omega)
      rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, ← Nat.add_assoc, sqDecAt_succ] at ht'
      have := sqLoop_iterE fs cert hfind hp hb hlp hit (rd := rd) (R := RegionL Lin)
        (Dt := fun i => RegionL (sqRuns fs cert lv name m fp w (t + 1)) i)
        (N := gen ^ n) (sqz := sqz) (qpos := qpos) (qbp := qbp) (tabs := tabs)
        (hcl (e + t)) (fp + t * fs name) (sqDecAt fs lv name m fp t)
        (Bt := (m - (t + 1) + 1) * fs name) (m := (m - (t + 1)) * fs (sqDecName lv)) hr0 hn0
        (hrel t (by omega)) (fun i h => h) (hKj (e + t))
        (by
          split
          · rw [gen_pow_mul_gen]; exact ht'
          · next h => exact absurd hne h)
        (fun t' ht'' => hreg (e + t) (by omega) (by omega) t' ht'')
      rw [show (m - t + 1) * fs name = fs name + (m - (t + 1) + 1) * fs name by
          rw [show m - t = m - (t + 1) + 1 by omega]; ring,
        show (m - t) * fs (sqDecName lv) = fs (sqDecName lv) + (m - (t + 1)) * fs (sqDecName lv) by
          rw [show m - t = m - (t + 1) + 1 by omega]; ring]
      refine RelAtInCT.dmono' this fun i hi => ?_
      obtain ⟨t', h1, h2, hi'⟩ := regionL_sqRuns.mp hi
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · exact Or.inl hi'
      · exact Or.inr ⟨hne, regionL_sqRuns.mpr ⟨t', by omega, h2, hi'⟩⟩
  have := hstep (m - 1) 0 (by omega)
  simp only [Nat.zero_mul, Nat.add_zero, Nat.sub_zero] at this
  have h := (show sqDecAt fs lv name m fp 0 = fp + (m + 1) * fs name by unfold sqDecAt; ring) ▸ this
  rw [show sqTot fs lv name m 0 = (m + 1) * fs name + m * fs (sqDecName lv) by unfold sqTot; simp]
  exact RelAtInCPE.relAtInPE h

end
end LeanVM.Guest.B1
