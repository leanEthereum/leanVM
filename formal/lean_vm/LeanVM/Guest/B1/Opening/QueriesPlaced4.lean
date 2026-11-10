/-
  LeanVM.Guest.B1.Opening.QueriesPlaced4

  A level-0 iteration of `opening_queries`' loop, placed (`RelAtIn`).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced3

/-!
# `walk_path` and a level-0 iteration, placed

`wp_relAtIn`: an honest `walk_path` frame (`WD`), placed at `fp`, is `RelAtIn` the caller's region
`R` by its frame alone: its body is flat (`walk_flatM`: its path's `match`es take the arms their
windows name), no `HeapBuf`, no `frameAddr`, no call, every load reading `R` (`OqWReg`: the windows,
the flag, the cap leaf).

`oqIter1_relAtIn`: the iteration at `x = g^j`, placed at `fp`, at its honest values (`oqIter1F`),
its tail at `fp + fs loop`, its two walks after the tail's tree, is `RelAtIn` the caller's region
`R`: no `HeapBuf`, no `frameAddr`, every load reading `R` (`OqQReg`: the challenges and the final
coefficients; the points, the window pointers and the chain), its walks' loads too.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- What a query of an iteration and its walk read from the caller's region: its challenges, its
final coefficients (final level), its windows (the path's and the cap's two), its flag and its cap
leaf. -/
structure OqQReg (R : ℕ → Prop) (s : Oq) (cap flags coefs hs bp : E) (q : ℕ) : Prop where
  co : ∀ off < 3 * s.folds, OqIn R (coefs.limb 0 * Parameters.addressOfIndex off)
  h : s.final = 1 → ∀ off < s.nHs, OqIn R (hs.limb 0 * Parameters.addressOfIndex off)
  b : ∀ off < oqNpw s + 2, OqIn R (bp.limb 0 * Parameters.addressOfIndex off)
  f : OqIn R ((flags * gen ^ (q / 2 ^ (s.pd + 1))).limb 0 * Parameters.addressOfIndex (2 ^
      (s.cd - 1)))
  c : ∀ e < 2, OqIn R ((cap * gen ^ (4 * (q / 2 ^ (s.pd + 1)) +
    (if q.testBit s.pd then 2 else 0))).limb 0 * Parameters.addressOfIndex (2 ^ (s.cd + 1) + e))

/-- What a walk reads from the caller's region: its windows (the path's and the cap's two), its
flag and its cap leaf. -/
structure OqWReg (R : ℕ → Prop) (pd cd : ℕ) (cap flags bp : E) (q : ℕ) : Prop where
  b : ∀ off < oqNpw ⟨0, 0, pd, cd, 0, [], 0, 0⟩ + 2, OqIn R (bp.limb 0 * Parameters.addressOfIndex off)
  f : OqIn R ((flags * gen ^ (q / 2 ^ (pd + 1))).limb 0 * Parameters.addressOfIndex (2 ^ (cd - 1)))
  c : ∀ e < 2, OqIn R ((cap * gen ^ (4 * (q / 2 ^ (pd + 1)) +
    (if q.testBit pd then 2 else 0))).limb 0 * Parameters.addressOfIndex (2 ^ (cd + 1) + e))

/-- A query's region holds its walk's. -/
theorem OqQReg.toW {R : ℕ → Prop} {s : Oq} {cap flags coefs hs bp : E} {q : ℕ}
    (h : OqQReg R s cap flags coefs hs bp q) : OqWReg R s.pd s.cd cap flags bp q :=
  ⟨h.b, h.f, h.c⟩

/-- A query's load of its challenges or final coefficients reads the caller's region. -/
theorem oqQLoad_in {R : ℕ → Prop} {s : Oq} {σ : Val} {coefs hs : V} {cap flags bp : E} {q : ℕ}
    (hreg : OqQReg R s cap flags (σ coefs) (σ hs) bp q) {p : V} {off : ℕ}
    (hl : OqQLoad s coefs hs p off) : OqIn R ((σ p).limb 0 * Parameters.addressOfIndex off) := by
  rcases hl with ⟨rfl, ho⟩ | ⟨hf, rfl, ho⟩
  · exact hreg.co off ho
  · exact hreg.h hf off ho

/-- **A walk's load reads the caller's region.** -/
theorem oqWLoad_in {R : ℕ → Prop} {w : WD} {σ : Val} (hv : w.Hv σ)
    (hreg : OqWReg R w.pd w.cd w.capv w.flagsv w.bpv w.q) {p : V} {off : ℕ}
    (hl : OqWLoad w.s (.n 2) wpCh p off) : OqIn R ((σ p).limb 0 * Parameters.addressOfIndex off) := by
  rcases hl with ⟨rfl, ho⟩ | ⟨rfl, rfl⟩ | ⟨rfl, ho⟩
  · rw [hv 2]; exact hreg.b off ho
  · rw [show (V.n (oqCq w.s wpCh + 2)) = .n (w.Cq + 2) from rfl, w.ptr_flag hv]
    exact hreg.f
  · rw [show (V.n (oqCq w.s wpCh + 8)) = .n (w.Cq + 8) from rfl, w.ptr_cap hv]
    rcases ho with rfl | rfl
    · exact hreg.c 0 (by omega)
    · exact hreg.c 1 (by omega)

/-- **An honest `walk_path` frame, placed**, by its frame alone. -/
theorem wp_relAtIn (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ) {w : WD}
    (hpd : 1 ≤ w.pd) (hcd : 1 ≤ w.cd) (hsl : w.sibs.length = w.pd) (hq : w.q < 2 ^ (w.pd + w.cd))
    {rd : Reader} (hm : w.MemOk rd) {wlk : String} (hW : WalkFn wlk w.pd w.cd) {R : ℕ → Prop}
    (hreg : OqWReg R w.pd w.cd w.capv w.flagsv w.bpv w.q) (fp : ℕ) :
    RelAtIn coreProgram fs cert rd R (fun _ => False) fp (fs wlk) wlk
      [(digestHalves w.leaf).1, (digestHalves w.leaf).2, w.bpv, w.capv, w.flagsv] [] := by
  obtain ⟨fn, hf, hp, hb⟩ := hW
  set σ : Val := fun v ↦ w.val v.idx with hσ
  have hv : w.Hv σ := fun _ ↦ rfl
  set pre := oqPathT w.s (.n 2) (wpPr w.s) 0 wpCh ++ oqCapT w.s (.n 2) (.n 3) (.n 4) 0 wpCh with hpre
  have hok := wp_atoms_ok w.s
  have hA : BlockOkC anyCall rd σ pre :=
    blockOkC_of_blockOk (w.walk_block hpd hcd hsl hq hv hm)
  have hfm : pre.all Stmt.flatM = true := hok.flatM
  have hbody : fn.body = pre ++ [.ret []] := by rw [hb, hpre]; exact wpBodyT_eq w.s
  set es := pre.flatMap (fmEvs σ) with hes
  have hw : walk σ fn.body = .ret es [] := by rw [hbody]; exact walk_flatM σ [] pre hfm (hok.matchOk hA)
  obtain ⟨i1, i2, i3, i4⟩ := flatM_parts σ pre hfm
  have hal : pre.filterMap Stmt.allocSz = [] := hok.allocSz
  have hallocs : allocs σ es = [] := by rw [i2, hal]; rfl
  have hcalls : calls es = [] := by
    rw [i4, callS_flat (flat_append (oqPathT_flat _ _ _ _ _) (flat_of_atoms (oqCapT_atoms _ _ _ _ _ _)))]
    rfl
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd) hP
    (R := R) (D := fun _ => False) (Dk := fun _ => False) (fp := fp) (N := 0)
    (args := [(digestHalves w.leaf).1, (digestHalves w.leaf).2, w.bpv, w.capv, w.flagsv]) (rets := [])
    hf (Or.inr hcalls) (by rw [hp]; rfl) hw rfl (hok.evs_holds hA)
    (by rw [i1, hal, hallocs]; rfl) (fun q hq ↦ ?_)
    (by rw [hcalls]; exact ⟨rfl, fun _ h ↦ h⟩) (fun A hAl ↦ ?_) (fun _ h ↦ h.elim)
  · rw [hallocs, List.sum_nil, Nat.add_zero, Nat.add_zero] at h; exact h
  · rw [i3, hok.addrS] at hq
    simp at hq
  · rw [loadAddrs_flatM σ pre hfm] at hAl
    obtain ⟨⟨p, off⟩, hq, rfl⟩ := List.mem_map.mp hAl
    obtain ⟨i, hi, hr⟩ := oqWLoad_in hv hreg (hok.load hq)
    exact ⟨i, hi, Or.inr (Or.inl hr)⟩

/-- A walk call's kid: the walk placed at the kids' base, then the others. -/
theorem kidsFromIn_walk {fs : String → ℕ} {cert : String → V → ℕ} {rd : Reader} {σ : Val}
    {R R0 Dacc : ℕ → Prop} {b n : ℕ} {wlk : String} {args : List V} {cs : List Call}
    {Dend : ℕ → Prop}
    (hR : RelAtIn coreProgram fs cert rd R0 (fun _ => False) b (fs wlk) wlk (args.map σ) [])
    (hR0 : ∀ i, R0 i → R i ∨ Dacc i)
    (hrest : KidsFromIn coreProgram fs cert rd σ R (fun i => Dacc i ∨ (true = true ∧ False)) cs
      (b + fs wlk) n Dend) :
    KidsFromIn coreProgram fs cert rd σ R Dacc (⟨wlk, args, [], true⟩ :: cs) b (fs wlk + n) Dend :=
  ⟨fs wlk, n, R0, fun _ => False, rfl, hR0, hR, hrest⟩

/-- `KidsFromIn` grows with the data earlier kids claimed. -/
theorem kidsFromIn_dacc {fs : String → ℕ} {cert : String → V → ℕ} {rd : Reader} {σ : Val}
    {R : ℕ → Prop} : ∀ (cs : List Call) {Dacc Dacc' : ℕ → Prop} {b n : ℕ} {Dend : ℕ → Prop},
    (∀ i, Dacc i → Dacc' i) → KidsFromIn coreProgram fs cert rd σ R Dacc cs b n Dend →
      KidsFromIn coreProgram fs cert rd σ R Dacc' cs b n Dend
  | [], _, _, _, _, _, h, ⟨hn, hd⟩ => ⟨hn, fun i hi ↦ h i (hd i hi)⟩
  | _ :: cs, _, _, _, _, _, h, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩ =>
    ⟨m, n', Rk, Dk, hn, fun i hi ↦ (hR i hi).imp_right (h i), hc,
      kidsFromIn_dacc cs (fun i hi ↦ hi.imp (h i) id) hk⟩

/-- A level-0 iteration's calls: its two queries' walks. -/
theorem oqLoop1A_callS (s : Oq) (odd : ℕ) (wlk : String) :
    (oqLoop1A s odd wlk).filterMap Stmt.callS =
      [(none, wlk, [.n (oqOut s (oqKL s 16 true) (s.B - 1) 0), .n (oqOut s (oqKL s 16 true) (s.B - 1) 1),
          .n 15, .n 4, .n 5], []),
        (none, wlk, [.n (oqOut s (oqKL s (oqE1 s + 2) false) (s.B - 1) 0),
          .n (oqOut s (oqKL s (oqE1 s + 2) false) (s.B - 1) 1), .n (oqE1 s + 1), .n 4, .n 5], [])] := by
  unfold oqLoop1A
  simp only [List.filterMap_append, oqQueryT_callS]
  split <;> rfl

/-- **A level-0 iteration, placed**, its tail's tree `m` words, its walks after it. -/
theorem oqIter1_relAtIn (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd) {odd : ℕ}
    {wlk loop : String} (hW : WalkFn wlk s.pd s.cd) {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd wlk loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp m j : ℕ} {N positions qptrs cap flags coefs hsp ch mu : E}
    {rounds : List FoldRound} {hsv : List E} {w1 w2 : QW} {bp1 bp2 v : E}
    (hok1 : (oqQD s 16 true 0 cap flags rounds hsv w1).Ok rd coefs hsp bp1)
    (hok2 : (oqQD s (oqE1 s + 2) false (oqK1 s 16) cap flags rounds hsv w2).Ok rd coefs hsp bp2)
    (hx1 : LoadHolds rd positions (2 * j + odd) (eOfNat w1.1))
    (hx2 : LoadHolds rd positions (2 * j + odd + 1) (eOfNat w2.1))
    (hb1 : LoadHolds rd qptrs (2 * j + odd) bp1) (hb2 : LoadHolds rd qptrs (2 * j + odd + 1) bp2)
    (hv : s.final ≠ 1 → LoadHolds rd ch j v ∧
      LoadHolds rd ch (j + 1) (((v + oqResV s rounds w1) * mu + oqResV s rounds w2) * mu))
    (hK : IsInK (gen ^ j * gen + N))
    (htail : if gen ^ j * gen + N ≠ 0 then
      RelAtIn coreProgram fs cert rd R (fun _ => False) (fp + fs loop) m loop
        [gen ^ j * gen, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] []
      else m = fs loop)
    (hRp : ∀ e < 2, OqIn R ((positions * gen ^ j * gen ^ j).limb 0 * Parameters.addressOfIndex
        (odd + e)))
    (hRq : ∀ e < 2, OqIn R ((qptrs * gen ^ j * gen ^ j).limb 0 * Parameters.addressOfIndex
        (odd + e)))
    (hR1 : OqQReg R s cap flags coefs hsp bp1 w1.1) (hR2 : OqQReg R s cap flags coefs hsp bp2 w2.1)
    (hRc : s.final ≠ 1 → ∀ e < 2, OqIn R ((ch * gen ^ j).limb 0 * Parameters.addressOfIndex e)) :
    RelAtIn coreProgram fs cert rd R (fun _ => False) fp (fs loop + m + 2 * fs wlk) loop
      [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] [] := by
  set D1 := oqQD s 16 true 0 cap flags rounds hsv w1 with hD1
  set D2 := oqQD s (oqE1 s + 2) false (oqK1 s 16) cap flags rounds hsv w2 with hD2
  set args : List E := [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] with hargs
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, ∀ w : V, σ w = oqIter1F s args D1 D2 bp1 bp2 v w.idx :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨hpar, hA, -, -, e11, e13, e15, eB2, eCh, eG2, eG4, hl1, hl2⟩ :=
    oqIter1_at (σ := σ) (walk := wlk) hs hfin hok1 hok2 hx1 hx2 hb1 hb2 hv (fun _ ↦ hσ _)
  have eP : ∀ i < 10, σ (.n i) = args.getD i 0 := by
    intro i hi
    have := congrArg (·.getD i 0) hpar
    simp only [oqLoopParams] at this
    interval_cases i <;> simpa [hargs] using this
  -- the body
  set ca : Stmt := .callIf (.n (oqG1 s + 2)) loop
    [.n (oqG1 s + 4), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] with hca
  set pre := oqLoop1A s odd wlk ++ [ca] with hpre
  have hok := oqLoop1A_ok s odd wlk
  have hfm : pre.all Stmt.flatM = true := by
    rw [hpre, List.all_append, hok.flatM]; rfl
  have hmo : ∀ x ∈ pre, MatchOk σ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hok.matchOk hA x hx
    · simp only [List.mem_singleton] at hx
      subst hx; trivial
  have hbody : fl.body = pre ++ [.ret []] := by
    rw [hbl, hpre, oqLoop1T, oqNextT, List.append_assoc]; rfl
  set es := pre.flatMap (fmEvs σ) with hes
  have hw : walk σ fl.body = .ret es [] := by rw [hbody]; exact walk_flatM σ [] pre hfm hmo
  obtain ⟨i1, i2, i3, i4⟩ := flatM_parts σ pre hfm
  have hal : pre.filterMap Stmt.allocSz = [] := by
    rw [hpre, List.filterMap_append, hok.allocSz]; rfl
  have hallocs : allocs σ es = [] := by rw [i2, hal]; rfl
  set a1 : List V := [.n (oqOut s (oqKL s 16 true) (s.B - 1) 0), .n (oqOut s (oqKL s 16 true) (s.B - 1) 1),
    .n 15, .n 4, .n 5] with ha1
  set a2 : List V := [.n (oqOut s (oqKL s (oqE1 s + 2) false) (s.B - 1) 0),
    .n (oqOut s (oqKL s (oqE1 s + 2) false) (s.B - 1) 1), .n (oqE1 s + 1), .n 4, .n 5] with ha2
  have hcalls : calls es = [⟨wlk, a1, [], true⟩, ⟨wlk, a2, [], true⟩] ++
      [⟨loop, [.n (oqG1 s + 4), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9],
      [], decide (σ (.n (oqG1 s + 2)) ≠ 0)⟩] := by
    rw [i4, hpre, List.filterMap_append, oqLoop1A_callS]; rfl
  -- the events hold
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    intro e he
    rw [hes, hpre, List.flatMap_append] at he
    rcases List.mem_append.mp he with he | he
    · exact hok.evs_holds hA e he
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at he
      change e ∈ slEvs σ ca at he
      simp only [hca, slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | he
      · show IsInK (σ (.n (oqG1 s + 2)))
        rw [eG2]; exact hK
      · rw [he]; split <;> trivial
  -- the walks
  have hW1 := wp_relAtIn (w := D1.wd bp1) hP fs cert hpd1 (show 1 ≤ s.cd by omega) hok1.hsibs
    hok1.hq hok1.hmem hW hR1.toW
  have hW2 := wp_relAtIn (w := D2.wd bp2) hP fs cert hpd1 (show 1 ≤ s.cd by omega) hok2.hsibs
    hok2.hq hok2.hmem hW hR2.toW
  have hm1 : a1.map σ = [(digestHalves D1.leaf).1, (digestHalves D1.leaf).2, bp1, cap, flags] := by
    have e0 := congrArg Prod.fst hl1
    have e1 := congrArg Prod.snd hl1
    simp only at e0 e1
    simp only [ha1, List.map_cons, List.map_nil, e0, e1, e15, eP 4 (by omega), eP 5 (by omega)]
    rfl
  have hm2 : a2.map σ = [(digestHalves D2.leaf).1, (digestHalves D2.leaf).2, bp2, cap, flags] := by
    have e0 := congrArg Prod.fst hl2
    have e1 := congrArg Prod.snd hl2
    simp only at e0 e1
    simp only [ha2, List.map_cons, List.map_nil, e0, e1, eB2, eP 4 (by omega), eP 5 (by omega)]
    rfl
  have inR : ∀ A, OqIn R A → ∃ i, A = Parameters.addressOfIndex i ∧
      (ownData cert fp (fp + fs loop + m) loop (allocs σ es) es i ∨ R i ∨ False ∨
        ((⟨loop, [.n (oqG1 s + 4), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9], [],
          decide (σ (.n (oqG1 s + 2)) ≠ 0)⟩ : Call).taken = true ∧ False)) :=
    fun A ⟨i, hi, hr⟩ ↦ ⟨i, hi, Or.inr (Or.inl hr)⟩
  have h := relAtIn_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    hP (R := R) (D := fun _ => False) (Dk := fun _ => False) (Rt := R) (Dt := fun _ => False)
    (fp := fp) (m := m) (N := fs wlk + (fs wlk + 0)) (args := args) (rets := [])
    hfl hlp (hpl ▸ hpar) hw rfl hev hcalls ?_
    (by rw [i1, hal, hallocs]; rfl)
    (fun q hq ↦ ?_) ?_ (fun i hi ↦ Or.inl hi)
    (fun A hAl ↦ ?_) (fun _ h ↦ h.elim)
  · rw [hallocs, List.sum_nil, Nat.add_zero, Nat.add_zero,
      show fs loop + m + (fs wlk + fs wlk) = fs loop + m + 2 * fs wlk by ring] at h
    exact h
  · -- the tail
    have hargs' : ([.n (oqG1 s + 4), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] :
        List V).map σ = [gen ^ j * gen, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] := by
      simp only [List.map_cons, List.map_nil, eG4, eP 1 (by omega), eP 2 (by omega),
        eP 3 (by omega), eP 4 (by omega), eP 5 (by omega), eP 6 (by omega), eP 7 (by omega),
        eP 8 (by omega), eP 9 (by omega)]
      rfl
    by_cases ht : gen ^ j * gen + N ≠ 0
    · simp only [ht, ne_eq, not_false_eq_true, ↓reduceIte] at htail
      have htk : decide (σ (.n (oqG1 s + 2)) ≠ 0) = true := by rw [eG2]; exact decide_eq_true ht
      simp only [htk, ↓reduceIte, List.map_nil]
      rw [hargs']; exact htail
    · simp only [ht, ↓reduceIte] at htail
      have htk : decide (σ (.n (oqG1 s + 2)) ≠ 0) = false := by rw [eG2]; exact decide_eq_false ht
      simp only [htk, Bool.false_eq_true, ↓reduceIte]
      exact htail
  · -- no frame address
    rw [i3, hpre, List.filterMap_append, hok.addrS] at hq
    simp [hca, Stmt.addrS] at hq
  · -- the walks
    rw [hallocs, List.sum_nil, Nat.add_zero]
    refine kidsFromIn_walk (R0 := R) ?_ (fun i hi ↦ Or.inl (Or.inl hi))
      (kidsFromIn_walk (R0 := R) ?_ (fun i hi ↦ Or.inl (Or.inl hi)) ⟨rfl, fun _ h ↦ h.elim⟩)
    · rw [hm1]; exact hW1 _
    · rw [hm2]; exact hW2 _
  · -- the loads
    rw [loadAddrs_flatM σ pre hfm] at hAl
    obtain ⟨⟨p, off⟩, hq, rfl⟩ := List.mem_map.mp hAl
    rw [hpre, List.filterMap_append] at hq
    rcases List.mem_append.mp hq with hq | hq
    · rcases hok.load hq with hl | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨hf, rfl, rfl⟩ | ⟨hf, rfl, rfl⟩
      · exact inR _ (oqQLoad_in (σ := σ) (coefs := .n 6) (hs := .n 7)
          (by rw [eP 6 (by omega), eP 7 (by omega)]; exact hR1) hl)
      · rw [e11]
        rcases ho with rfl | rfl
        · exact inR _ (by simpa using hRp 0 (by omega))
        · exact inR _ (hRp 1 (by omega))
      · rw [e13]
        rcases ho with rfl | rfl
        · exact inR _ (by simpa using hRq 0 (by omega))
        · exact inR _ (hRq 1 (by omega))
      · rw [(eCh hf).1]; exact inR _ (hRc hf 0 (by omega))
      · rw [(eCh hf).2]; exact inR _ (hRc hf 1 (by omega))
    · simp [hca, stmtLoad?] at hq

end
end LeanVM.Guest.B1
