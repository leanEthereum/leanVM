/-
  LeanVM.Guest.WalkKnown

  The windowed Merkle walk's cut obligations (`CutsKnown`) of `opening_queries`' specializations
  and their loops, from B1's facts on the templates (whir's `QueriesWalk`), read through the
  certificates' cells.
-/

module

public import LeanVM.Guest.Sound
public import LeanVM.Guest.WalkKnownDefs
public import LeanVM.Guest.B1.Opening.QueriesWalk

/-!
# The walks' obligations, from the templates

Checker K hands on, at the cuts of `opening_queries__*` and its loops, the window bounds a `match`
reads (`knownIf`: the word at `fp[o]·g^i`, if read, is `g^e`, `e < n`, or read twice through
`fp[o]`, `memTwice`) and the walk's tuples (`sems`). The certificates' generator writes them on
fixed cells; here a decided check per function (`loopOk`, `mainOk`) says each is one of the forms
B1 proves on the template (`B1.Opening.QueriesWalk`). The tags are keyed by the path depth `pd`
(`oqTag`), on which alone the windows a query dispatches on depend (`walk_path` is inline):

* a loop's precondition is the walk (`WinWalkP` or `WinWalk2P`) on its values `[qptrs, x, N]`
  and `x ≠ N` (`tagNe`); each window bound is on the cell of a window pointer the prefix loads
  (`oqLoop0T_wins`, `oqLoop1T_wins1`, `oqLoop1T_wins2`: `winTripOk`), the tail call's tuple the
  walk from `x·g` (`oqLoop0T_tail`, `oqLoop1T_tail`);
* a deeper specialization's precondition is the walk from `1` on `[qptrs, N]`, which its loop
  call's tuple is, conditional on the argument's cell holding `1` (`impTag … 1 1`, a constant
  `SET` in the call's setup);
* a level-0 specialization's is `OqStartP` for both `odd`'s on `[qptrs, N, odd_g]` and
  `odd_g ∈ {1, g}` (`tagOdd`): the first pointer names path windows, which the odd first query
  reads under its branch on `odd_g` (bounds read twice through `qptrs`, `twiceOk`), and the loop
  call's tuple is the walk of the `odd` that `odd_g` is, from `1` over `qptrs·odd_g`
  (`oqMainT_loop1`).

`loop0_cutsKnown`, `loop1_cutsKnown`, `main_cutsKnown`: `CutsKnown j` from the body's template and
the decided check. The instances are `WalkOq*.lean`.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.B1

@[expose] public section

/-! ## The tags -/

theorem walkTag_ge (kind odd d cd : ℕ) : 2 ≤ walkTag kind odd d cd := by
  unfold walkTag; omega

theorem semRel_lt {t : ℕ} (ht : t < 2 ^ 31) (rd : Reader) (ws : List E) :
    SemRel glob t rd ws ↔ SemRel0 glob t rd ws := by
  unfold SemRel
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- A tag `2 ≤ t < 2^21` is a walk tag. -/
theorem semRel0_walk {t : ℕ} (ht : 2 ≤ t) (hl : t < 2 ^ 21)
    (rd : Reader) (ws : List E) : SemRel0 glob t rd ws ↔ walkSem t rd ws := by
  have hT : t ≠ tagTabs := by rw [show tagTabs = 2 ^ 21 from rfl]; omega
  unfold SemRel0
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by unfold tagNe; omega))]
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 2 := ⟨t - 2, by omega⟩
  change (if n + 2 = tagTabs then B1.WinTabs rd (ws.getD 0 0)
    else if 2 ^ 21 ≤ n + 2 then lqSem (n + 2) rd ws else walkSem (n + 2) rd ws) ↔ _
  rw [ite_eq_right_of_eq_false _ _ (eq_false hT),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem semRel_ne (rd : Reader) (ws : List E) : SemRel glob tagNe rd ws ↔ ws.getD 0 0 ≠ ws.getD 1 0 := by
  rw [semRel_lt (by unfold tagNe; norm_num)]
  unfold SemRel0
  rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]

theorem oqTag_lt {kind odd pd : ℕ} (hk : kind < 4) (ho : odd < 2) (hpd : pd < 64) :
    oqTag kind odd pd < 2 ^ 21 := by
  have := walkTag_lt (cd := 0) hk ho (by decide) hpd
  unfold oqTag
  omega

theorem semRel0_oq {kind odd pd : ℕ} (hk : kind < 4) (ho : odd < 2) (hpd : pd < 64) (rd : Reader)
    (ws : List E) : SemRel0 glob (oqTag kind odd pd) rd ws ↔ walkSem (oqTag kind odd pd) rd ws :=
  semRel0_walk (walkTag_ge _ _ _ _) (oqTag_lt hk ho hpd) rd ws

theorem semRel_oq {kind odd pd : ℕ} (hk : kind < 4) (ho : odd < 2) (hpd : pd < 64) (rd : Reader)
    (ws : List E) : SemRel glob (oqTag kind odd pd) rd ws ↔ walkSem (oqTag kind odd pd) rd ws := by
  rw [semRel_lt (by have := oqTag_lt hk ho hpd; omega), semRel0_oq hk ho hpd]

/-- A deeper loop's tag: its walk. -/
theorem walkSem_oq0 (pd : ℕ) (rd : Reader) (ws : List E) :
    walkSem (oqTag 0 0 pd) rd ws ↔ WinWalkP rd pd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) := by
  obtain ⟨h1, h2, h3, -⟩ := walkTag_decode (kind := 0) (odd := 0) (d := pd) (cd := 0) (by decide)
    (by decide) (by decide)
  simp [walkSem, oqTag, h1, h2, h3]

/-- A level-0 loop's tag: its walk. -/
theorem walkSem_oq1 (pd : ℕ) (rd : Reader) (ws : List E) :
    walkSem (oqTag 1 0 pd) rd ws ↔ WinWalk2P rd pd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) := by
  obtain ⟨h1, -, h3, -⟩ := walkTag_decode (kind := 1) (odd := 0) (d := pd) (cd := 0) (by decide)
    (by decide) (by decide)
  simp [walkSem, oqTag, h1, h3]

/-- A deeper specialization's tag: the walk from `1`. -/
theorem walkSem_oq2 (pd : ℕ) (rd : Reader) (ws : List E) :
    walkSem (oqTag 2 0 pd) rd ws ↔ WinWalkP rd pd (ws.getD 0 0) 1 (ws.getD 1 0) := by
  obtain ⟨h1, -, h3, -⟩ := walkTag_decode (kind := 2) (odd := 0) (d := pd) (cd := 0) (by decide)
    (by decide) (by decide)
  simp [walkSem, oqTag, h1, h3]

/-- A level-0 specialization's tag for `odd`: `OqStartP`. -/
theorem walkSem_oq3 {odd : ℕ} (ho : odd < 2) (pd : ℕ) (rd : Reader) (ws : List E) :
    walkSem (oqTag 3 odd pd) rd ws ↔ OqStartP rd pd odd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) := by
  obtain ⟨h1, h2, h3, -⟩ := walkTag_decode (kind := 3) (odd := odd) (d := pd) (cd := 0) (by decide) ho
    (by decide)
  simp [walkSem, oqTag, h1, h2, h3]

/-- **`odd_g`'s tag**: `1` or `g`. -/
theorem semRel0_odd (rd : Reader) (ws : List E) :
    SemRel0 glob tagOdd rd ws ↔ ws.getD 0 0 = 1 ∨ ws.getD 0 0 = Protocol.Verifier.gen := by
  exact semRel0_walk (t := tagOdd) (by decide) (by decide) rd ws

theorem semRel_odd (rd : Reader) (ws : List E) :
    SemRel glob tagOdd rd ws ↔ ws.getD 0 0 = 1 ∨ ws.getD 0 0 = Protocol.Verifier.gen := by
  rw [semRel_lt (by decide), semRel0_odd]

/-- **`level_queries`' tag**: `OqMainWins` of its walk on the tuple's one word, at `g^n`. -/
theorem semRel_lq {n odd base d cd : ℕ} (ho : odd < 2) (hb : base < 2) (hc : cd < 64) (hd : d < 64)
    (hn : n < 992) (rd : Reader) (ws : List E) :
    SemRel glob (lqTag n odd base d cd) rd ws ↔
      OqMainWins rd d cd odd base (ws.getD 0 0) (Protocol.Verifier.gen ^ n) := by
  have hw := walkTag_lt (kind := 2 + base) (by omega) ho hc hd
  have hw2 := walkTag_ge (2 + base) odd d cd
  have hlt : lqTag n odd base d cd < 2 ^ 26 := by unfold lqTag; omega
  have hge : 2 ^ 21 < lqTag n odd base d cd := by unfold lqTag; omega
  unfold SemRel SemRel0
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by unfold tagNe; omega))]
  obtain ⟨m, hm⟩ : ∃ m, lqTag n odd base d cd = m + 2 := ⟨lqTag n odd base d cd - 2, by omega⟩
  change globSem (lqTag n odd base d cd) rd ws ↔ _
  rw [hm]
  change (if m + 2 = tagTabs then B1.WinTabs rd (ws.getD 0 0)
    else if 2 ^ 21 ≤ m + 2 then lqSem (m + 2) rd ws else walkSem (m + 2) rd ws) ↔ _
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by unfold tagTabs; omega)),
    ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ← hm]
  obtain ⟨e1, e2⟩ := lqTag_decode (n := n) hb ho hc hd
  obtain ⟨h1, h2, h3, h4⟩ := walkTag_decode (d := d) (by omega : 2 + base < 4) ho hc
  simp only [lqSem, e1, e2, h1, h2, h3, h4, Nat.add_sub_cancel_left]

/-! ## The certificates' cells -/

theorem valG_n {κ : ℕ} (L : MemoryImage κ) (fp : K) (C : Cert) (v : ℕ) :
    valG L fp C (.n v) = wd L fp (C.locs.getD v 0) := rfl

theorem getD_map_lt {f : ℕ → E} {l : List ℕ} {i : ℕ} (h : i < l.length) :
    (l.map f).getD i 0 = f (l.getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]

theorem cutAt_mem {C : Cert} {i : ℕ} (hi : i ≤ C.cuts.length) (h0 : 0 < i) : C.cutAt i ∈ C.cuts := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hc : C.cutAt (i + 1) = C.cuts[i]'(by omega) := by
    simp only [Cert.cutAt]
    exact nth_eq _
  rw [hc]
  exact List.getElem_mem _


/-- A conditional tag on the immediate `l` at position `k < 8`: the relation holds if the `k`-th
word is `l`'s. -/
theorem semRel_impK {t : ℕ} (ht : t < 2 ^ 32) {k : ℕ} (hk : k < 8) (l : ℕ) (rd : Reader) (ws : List E) :
    SemRel glob (impTag t k l) rd ws ↔
      (ws.getD k 0 = OffsetInstruction.immediateWord l 0 → SemRel0 glob t rd ws) := by
  have e0 : impTag t k l / 2 ^ 32 = 1 + k + 8 * l := by
    unfold impTag
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ht, Nat.zero_add]
  have e1 : impPos (impTag t k l) = k := by unfold impPos; rw [e0]; omega
  have e2 : impImm (impTag t k l) = l := by unfold impImm; rw [e0]; omega
  have e3 : impBase (impTag t k l) = t := by
    unfold impBase impTag
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
  unfold SemRel
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by unfold impTag; omega)), e1, e2, e3]

/-! ## The bounds -/

/-- Bounds read once, each of which holds. -/
theorem memIf_once {κ : ℕ} {L : MemoryImage κ} {fp : K} {knownIf : List (ℕ × ℕ × ℕ)}
    (h : ∀ m ∈ knownIf, m.2.1 < 2 ^ 32 ∧ ∀ v, LoadHolds L.read (wd L fp m.1) m.2.1 v →
      ∃ e < m.2.2, v = ofK (addressOfIndex e)) : MemIf L fp knownIf := by
  intro m hm q v hq hv
  obtain ⟨hs, hw⟩ := h m hm
  rw [ite_eq_left_of_eq_true _ _ (eq_true hs)] at hq hv
  subst hq
  exact hw v hv

theorem memIf_of_wins {κ : ℕ} {L : MemoryImage κ} {fp : K} {C : Cert} {pd start : ℕ} (hpd : pd < 64)
    {src : List (ℕ × ℕ)} {knownIf : List (ℕ × ℕ × ℕ)}
    (hok : knownIf.all (winTripOk C pd src start) = true)
    (hw : ∀ v ∈ src, v.2 ≤ start → WinsP L.read pd (valG L fp C (.n v.1))) :
    MemIf L fp knownIf := by
  refine memIf_once fun m hm ↦ ?_
  have h := List.all_eq_true.mp hok m hm
  simp only [winTripOk, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq,
    Nat.blt_eq] at h
  obtain ⟨v, hv', ⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hn : pwN pd < 2 ^ 32 := by unfold pwN; omega
  refine ⟨by omega, fun val hval ↦ ?_⟩
  have hW := hw v hv' h2
  rw [valG_n, ← h1] at hW
  obtain ⟨e, he, rfl⟩ := hW m.2.1 h3 val hval
  exact ⟨e, lt_of_lt_of_le he h4, rfl⟩

/-! ## The loops -/

/-- **A loop's cut obligations**, from its certificate's check (`loopOk`) and the walk's facts on
the prefixes of its body: the window pointers `src` name path windows, the tail passes the walk
on. -/
theorem loop_cutsKnown {j tag pd xv tl : ℕ} {src : List (ℕ × ℕ)} (hpd : pd < 64)
    (hok : loopOk (certOf j) tag pd src xv tl = true) (W : Reader → E → E → E → Prop)
    (hsem : ∀ rd ws, SemRel glob tag rd ws ↔ W rd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0))
    (hwins : ∀ {κ : ℕ} (L : MemoryImage κ) (σ : Val) (n : ℕ),
      Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((coreOf j).body.take n) True (fun _ ↦ True) →
      W L.read (σ (.n oqQp)) (σ (.n oqX)) (σ (.n oqN)) → σ (.n oqX) ≠ σ (.n oqN) →
      ∀ v ∈ src, v.2 ≤ n → WinsP L.read pd (σ (.n v.1)))
    (htail : ∀ {κ : ℕ} (L : MemoryImage κ) (σ : Val) (n : ℕ), tl ≤ n →
      Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((coreOf j).body.take n) True (fun _ ↦ True) →
      W L.read (σ (.n oqQp)) (σ (.n oqX)) (σ (.n oqN)) → σ (.n oqX) ≠ σ (.n oqN) →
      W L.read (σ (.n oqQp)) (σ (.n xv)) (σ (.n oqN))) :
    CutsKnown j := by
  intro κ L _ _ fp _ hsem' i hi h0 hl
  simp only [loopOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨hs, hcuts⟩ := hok
  rw [hs] at hsem'
  have hW : W L.read (valG L fp (certOf j) (.n oqQp)) (valG L fp (certOf j) (.n oqX))
      (valG L fp (certOf j) (.n oqN)) :=
    (hsem _ _).mp (hsem' _ (List.mem_cons_self ..))
  have hne : valG L fp (certOf j) (.n oqX) ≠ valG L fp (certOf j) (.n oqN) :=
    (semRel_ne _ _).mp (hsem' _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have hcut := hcuts _ (cutAt_mem hi h0)
  simp only [loopCutOk, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at hcut
  obtain ⟨⟨hkn, hki⟩, hsm⟩ := hcut
  have hwv := fun v hv hle ↦ hwins L _ _ hl hW hne v hv hle
  refine ⟨by rw [hkn]; intro _ h; simp at h, memIf_of_wins hpd (by simpa using hki) hwv,
    fun t ht ↦ ?_⟩
  have h := hsm t ht
  simp only [beq_iff_eq, Nat.ble_eq] at h
  obtain ⟨rfl, hle⟩ := h
  exact (hsem _ _).mpr (htail L _ _ hle hl hW hne)

/-- **A deeper loop's cut obligations** (`oqLoop0T`, the walk `WinWalkP`). -/
theorem loop0_cutsKnown {j : ℕ} {s : Oq} {name : String} (hb : (coreOf j).body = oqLoop0T s name)
    (hpd : s.pd < 64) (hok : loop0Ok j s = true) : CutsKnown j := by
  refine loop_cutsKnown hpd hok (fun rd t x N ↦ WinWalkP rd s.pd t x N)
    (fun rd ws ↦ (semRel_oq (by decide) (by decide) hpd rd ws).trans (walkSem_oq0 _ _ _))
    (fun L σ n hl hw hne v hv hle ↦ ?_) (fun L σ n hle hl hw hne ↦ ?_)
  · simp only [List.mem_singleton] at hv
    subst hv
    rw [hb] at hl
    exact oqLoop0T_wins hle hl hw hne
  · rw [hb] at hl
    exact oqLoop0T_tail hle hl hw hne

/-- **A level-0 loop's cut obligations** (`oqLoop1T`, the walk `WinWalk2P`). -/
theorem loop1_cutsKnown {j : ℕ} {s : Oq} {name : String} (hb : (coreOf j).body = oqLoop1T s name)
    (hpd : s.pd < 64) (hok : loop1Ok j s = true) : CutsKnown j := by
  refine loop_cutsKnown hpd hok (fun rd t x N ↦ WinWalk2P rd s.pd t x N)
    (fun rd ws ↦ (semRel_oq (by decide) (by decide) hpd rd ws).trans (walkSem_oq1 _ _ _))
    (fun L σ n hl hw hne v hv hle ↦ ?_) (fun L σ n hle hl hw hne ↦ ?_)
  · rw [hb] at hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact oqLoop1T_wins1 hle hl hw hne
    · exact oqLoop1T_wins2 hle hl hw hne
  · rw [hb] at hl
    exact oqLoop1T_tail hle hl hw hne

/-! ## The specializations -/

/-- **A specialization's cut obligations** (`oqMainT`): deeper, the loop call's walk from `1` is
its precondition; at level 0, `OqStartP` of both `odd`'s and `odd_g ∈ {1, g}` give the odd
query's bounds read twice (the first pointer's path windows) and the loop call's walk. -/
theorem main_cutsKnown {j : ℕ} {s : Oq} {loop : String} (hb : (coreOf j).body = oqMainT s loop)
    (hpd : s.pd < 64) (hok : mainOkS j s = true) : CutsKnown j := by
  intro κ L _ _ fp _ hsem' i hi h0 hl
  simp only [mainOkS, mainOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨hs, hcuts⟩ := hok
  rw [hs] at hsem'
  rw [hb] at hl
  have hcut := hcuts _ (cutAt_mem hi h0)
  unfold mainCutOk at hcut
  by_cases h1 : s.base = 1
  · simp only [h1, ↓reduceIte, beq_self_eq_true, Bool.true_or, Bool.and_eq_true, and_true,
      List.isEmpty_iff, List.all_eq_true, beq_iff_eq, Nat.ble_eq] at hcut
    obtain ⟨⟨hkn, hki⟩, hsm⟩ := hcut
    simp only [mainSem, h1, ↓reduceIte] at hsem'
    have hS : ∀ o < 2, OqStartP L.read s.pd o (valG L fp (certOf j) (.n oqMQp))
        (valG L fp (certOf j) (.n oqMN)) (valG L fp (certOf j) (.n oqMOdd)) := by
      intro o ho
      have hm : (oqTag 3 o s.pd, [(certOf j).locs.getD oqMQp 0, (certOf j).locs.getD oqMN 0,
          (certOf j).locs.getD oqMOdd 0]) ∈ [(oqTag 3 0 s.pd, [(certOf j).locs.getD oqMQp 0,
          (certOf j).locs.getD oqMN 0, (certOf j).locs.getD oqMOdd 0]), (oqTag 3 1 s.pd,
          [(certOf j).locs.getD oqMQp 0, (certOf j).locs.getD oqMN 0, (certOf j).locs.getD oqMOdd 0]),
          (tagOdd, [(certOf j).locs.getD oqMOdd 0])] := by
        obtain rfl | rfl : o = 0 ∨ o = 1 := by omega
        · simp
        · simp
      exact ((semRel_oq (by decide) ho hpd _ _).trans (walkSem_oq3 ho _ _ _)).mp (hsem' _ hm)
    have hU : valG L fp (certOf j) (.n oqMOdd) = 1 ∨ valG L fp (certOf j) (.n oqMOdd) = Protocol.Verifier.gen :=
      (semRel_odd _ _).mp (hsem' (tagOdd, [(certOf j).locs.getD oqMOdd 0]) (by simp))
    refine ⟨by rw [hkn]; intro _ h; simp at h, fun m hm q v hq hv ↦ ?_, fun t ht ↦ ?_⟩
    · have h := hki m hm
      simp only [twiceOk, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq, Nat.blt_eq] at h
      obtain ⟨⟨⟨⟨hc, hbig⟩, hmod⟩, hwi⟩, hle⟩ := h
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at hq hv
      rw [hmod, hc, ← valG_n] at hq
      obtain ⟨e, he, rfl⟩ := (hS 0 (by decide)).1 q hq _ hwi v hv
      exact ⟨e, lt_of_lt_of_le he hle, rfl⟩
    · obtain ⟨⟨⟨ht1, hlen⟩, ht2⟩, ht0, hst⟩ := hsm t ht
      rw [ht1, semRel_impK (by have := oqTag_lt (kind := 1) (odd := 0) (by decide) (by decide) hpd; omega)
        (by decide), (Exec.imm_of_ofBits rfl).trans Exec.ofK_one, semRel0_oq (by decide) (by decide) hpd,
        walkSem_oq1]
      intro hx
      rw [getD_map_lt (by omega)] at hx
      rw [getD_map_lt (by omega), getD_map_lt (by omega), getD_map_lt (by omega), hx, ht0, ht2,
        ← valG_n, ← valG_n]
      rcases hU with hu | hu
      · exact oqMainT_loop1 h1 hst hl (odd := 0) (by rw [pow_zero]; exact hu) (hS 0 (by decide))
      · exact oqMainT_loop1 h1 hst hl (odd := 1) (by rw [pow_one]; exact hu) (hS 1 (by decide))
  · simp only [h1, ↓reduceIte, beq_iff_eq, Bool.or_eq_true, false_or, Bool.and_eq_true, List.isEmpty_iff,
      List.all_eq_true] at hcut
    obtain ⟨⟨⟨hkn, hkiE⟩, -⟩, hsm⟩ := hcut
    simp only [mainSem, h1, ↓reduceIte] at hsem'
    have hW : WinWalkP L.read s.pd (valG L fp (certOf j) (.n oqMQp)) 1 (valG L fp (certOf j) (.n oqMN)) :=
      ((semRel_oq (by decide) (by decide) hpd _ _).trans (walkSem_oq2 _ _ _)).mp
        (hsem' _ (List.mem_singleton_self _))
    refine ⟨by rw [hkn]; intro _ h; simp at h, by rw [hkiE]; intro _ h; simp at h, fun t ht ↦ ?_⟩
    obtain ⟨⟨⟨ht1, hlen⟩, ht2⟩, ht0⟩ := hsm t ht
    rw [ht1, semRel_impK (by have := oqTag_lt (kind := 0) (odd := 0) (by decide) (by decide) hpd; omega)
      (by decide), (Exec.imm_of_ofBits rfl).trans Exec.ofK_one, semRel0_oq (by decide) (by decide) hpd,
      walkSem_oq0]
    intro hx
    rw [getD_map_lt (by omega)] at hx
    rw [getD_map_lt (by omega), getD_map_lt (by omega), getD_map_lt (by omega), hx, ht0, ht2,
      ← valG_n, ← valG_n]
    exact hW

end
end LeanVM.Guest.End
