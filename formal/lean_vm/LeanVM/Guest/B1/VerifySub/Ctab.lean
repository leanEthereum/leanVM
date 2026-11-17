/-
  LeanVM.Guest.B1.VerifySub.Ctab

  `verify_sub`'s ring map: its grind and sixteen challenges, and their Frobenius coefficients
  `c_table`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Front
public import LeanVM.Guest.B1.Bits.Grind
public import LeanVM.Guest.B1.Common.Run

/-!
# The ring map's challenges and `c_table`

* `vsMapsT_holds`: the ring grind's nonce absorbed over the full queue `verify_keccak` leaves,
  `grind_check__L13` on the permutation's cell `1`, the ground challenge and fifteen squeezes,
  stored in `map_challenges`: from the sponge `s`, `ringSwitch` reads the nonce and returns the
  target and weight of these sixteen challenges.
* `vsCtabT_holds`: `c_table[8p + b] = f_p · g_b^(2^(8p))`, by eight squarings per block, is
  `ringCoefficients f g`; then the call of `ring_switch_target`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}

theorem vsRun5_map (b : ℕ) :
    (vsRun b 5).map σ = [σ (.n b), σ (.n (b + 1)), σ (.n (b + 2)), σ (.n (b + 3)), σ (.n (b + 4))] :=
  rfl

/-! ## The ring map's challenges -/

/-- `vsSqzT_holds` with the capacity left as a run. -/
theorem vsSqzT_holds' {capb o : ℕ} (h8 : σ (.n 8) = 0) (h9 : σ (.n 9) = 0)
    (h10 : σ (.n 10) = 0) (h11 : σ (.n 11) = 0)
    (h : Stmt.HoldsList C rd σ (vsSqzT capb o) next kret) :
    (⟨(vsRun capb 5).map σ, []⟩ : Fs).squeeze = (σ (.n (o + 13)), ⟨(vsRun (o + 8) 5).map σ, []⟩) ∧
      next := by
  obtain ⟨e, hn⟩ := vsSqzT_holds h8 h9 h10 h11 h
  exact ⟨e, hn⟩

/-- The block of the ring map's squeeze `i`. -/
def vsMapSqz (i : ℕ) : List Stmt :=
  vsSqzT (vsChCap i) (622 + 15 * i) ++ [vsCopy (vsCh (i + 1)) (635 + 15 * i)]

/-- **The fifteen squeezes** from the capacity at `vsChCap j`. -/
theorem maps_chain (h8 : σ (.n 8) = 0) (h9 : σ (.n 9) = 0) (h10 : σ (.n 10) = 0)
    (h11 : σ (.n 11) = 0) : ∀ (k j : ℕ) {nx : Prop},
      Stmt.HoldsList C rd σ ((List.range' j k).flatMap vsMapSqz) nx kret →
      (⟨(vsRun (vsChCap j) 5).map σ, []⟩ : Fs).squeezeN k =
          ((List.range' j k).map fun i ↦ σ (.n (vsCh (i + 1))),
            ⟨(vsRun (vsChCap (j + k)) 5).map σ, []⟩) ∧ nx
  | 0, j, _, h => ⟨by simp [Fs.squeezeN], h⟩
  | k + 1, j, _, h => by
    rw [List.range'_succ, List.flatMap_cons, holdsList_append, vsMapSqz, holdsList_append] at h
    obtain ⟨e, h⟩ := vsSqzT_holds' h8 h9 h10 h11 h
    obtain ⟨c, h⟩ := h
    simp only [Atom.Holds] at c
    obtain ⟨ih, hn⟩ := maps_chain h8 h9 h10 h11 k (j + 1) h
    refine ⟨?_, hn⟩
    have e1 : vsChCap (j + 1) = 622 + 15 * j + 8 := by simp only [vsChCap]; split <;> omega
    rw [Fs.squeezeN, e]
    dsimp only
    rw [← e1, ih, List.range'_succ, List.map_cons, show j + 1 + k = j + (k + 1) by omega, c,
      show 622 + 15 * j + 13 = 635 + 15 * j by omega]

theorem loads_map {p : ℕ} (f : ℕ → ℕ) : ∀ (l : List ℕ) {nx : Prop},
    Stmt.HoldsList C rd σ (l.map fun i ↦ vsLd (f i) p i) nx kret →
      (∀ i ∈ l, LoadHolds rd (σ (.n p)) i (σ (.n (f i)))) ∧ nx
  | [], _, h => ⟨fun _ h ↦ absurd h (by simp), h⟩
  | i :: l, _, h => by
    obtain ⟨li, h⟩ := h
    obtain ⟨hl, hn⟩ := loads_map f l h
    exact ⟨fun x hx ↦ by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact li
      · exact hl x hx, hn⟩

theorem maps_winTabs_of {q tabs : E} (hwin : ExpWinTab rd q) (h : tabs = q * gen ^ winTabAt) :
    WinTabs rd tabs := fun n hn ↦ by rw [h, loadHolds_mul_gen_pow]; exact hwin n hn

/-- The sixteen challenges, from the sponge's ground challenge. -/
theorem runsFromG_sample16 (cap : List E) (c : E) :
    RunsFromG (VerifierProgram.sampleChallenges 16) cap c [] (c :: ((⟨cap, []⟩ : Fs).squeezeN 15).1)
      ((⟨cap, []⟩ : Fs).squeezeN 15).2 :=
  (runsFromG_sample cap c).bind (f := fun x ↦ do
      let xs ← VerifierProgram.sampleChallenges 15
      return x :: xs)
    ((runsTo_sampleN 15 _).bind (f := fun xs ↦ (pure (c :: xs) : VerifierProgram (List E)))
      (runsTo_ret _ _))

/-- **The ring map's challenges**: from the sponge `s` with a full queue, the
nonce at the cursor `σ 595`, `ringSwitch` returns the target and weight of the sixteen challenges
stored at `map_challenges`. -/
theorem vsMapsT_holds {κ : ℕ} (hκ : κ ≤ 32) (hκw : winTabBits ≤ κ) (L : MemoryImage κ)
    (hC : CallRel.Le C (coreProgram.Rel L.read)) (hwin : ExpWinTab L.read (σ (.n 4)))
    (h8 : σ (.n 8) = 0) (h9 : σ (.n 9) = 0) (h10 : σ (.n 10) = 0) (h11 : σ (.n 11) = 0)
    {s : Fs} (hs : s.pend.length = 4)
    (hcap : [σ (.n 590), σ (.n 591), σ (.n 592), σ (.n 593), σ (.n 594)] = capOf s.perm)
    (h : Stmt.HoldsList C L.read σ vsMapsT next kret) :
    ∃ chs : List E, chs.length = 16 ∧ (∀ i < 16, σ (.n (vsCh i)) = chs.getD i 0) ∧
      ReadsAt L.read (σ (.n 847)) chs ∧ LoadHolds L.read (σ (.n 595)) 0 (σ (.n 602)) ∧
      (∀ point sl : List E, RunsTo (ringSwitch point sl) s [σ (.n 602)]
        (ringTarget sl (chs.take ringMapWidth) (chs.drop ringMapWidth),
          fun r ↦ ringWeight point r
            (ringCoefficients (chs.take ringMapWidth) (chs.drop ringMapWidth)))
        ⟨[σ (.n 840), σ (.n 841), σ (.n 842), σ (.n 843), σ (.n 844)], []⟩) ∧ next := by
  simp only [vsMapsT, holdsList_append] at h
  rw [show List.range 5 = [0, 1, 2, 3, 4] from rfl] at h
  simp only [List.map_cons, List.map_nil] at h
  obtain ⟨c0, c1, c2, c3, c4, h⟩ := h
  simp only [Atom.Holds] at c0 c1 c2 c3 c4
  obtain ⟨⟨ln, pk⟩, h⟩ := (holds_fsNonceT _ _ _ _ _).1 h
  obtain ⟨hk, h⟩ := holds_atom1.1 h
  obtain ⟨h619, h⟩ := vsTabsT_holds h
  obtain ⟨hg, c620, c621, h⟩ := h
  simp only [Atom.Holds] at c620 c621
  rw [List.range_eq_range'] at h
  obtain ⟨hsq, h⟩ := maps_chain h8 h9 h10 h11 15 0 h
  obtain ⟨-, h⟩ := h
  obtain ⟨hl, hn⟩ := loads_map vsCh (List.range 16) h
  -- the nonce's permutation
  set S := s.nonceState (σ (.n 602)) with hS
  have habs : s.absorb (σ (.n 602)) dsPowNonce = ⟨capOf s.perm, [(σ (.n 602), dsPowNonce)]⟩ := by
    simp [Fs.absorb, hs, rateScalars]
  have hcells : cells13 ((vsRun 605 13).map σ) = cellsOfState S false := by
    rw [hS, Fs.nonceState, habs]
    refine keccakA_fs hk (by simp) ?_
    have hp := fsPackT_cells pk
    simp only [List.map_cons, List.map_nil, h8, h9, h10, h11, c0, c1, c2, c3, c4]
    rw [show [σ (.n 590), σ (.n 591), σ (.n 592), σ (.n 593), σ (.n 594)] = capOf s.perm from hcap]
    simp only [pendCells, List.flatMap_cons, List.flatMap_nil, List.append_nil, ← hp,
      List.length_cons, List.length_nil]
    rfl
  have hc : ∀ c : Fin 13, σ (.n (605 + c.val)) = cellsOfState S false c := fun c ↦ by
    have := congrFun hcells c
    simpa [cells13, vsRun, c.isLt] using this
  have hc0 : σ (.n 605) = cellsOfState S false 0 := hc 0
  have hc1 : σ (.n 606) = cellsOfState S false 1 := hc 1
  -- the grind
  simp only [List.map_cons, List.map_nil] at hg
  have hW : WinTabs L.read (σ (.n 619)) := maps_winTabs_of hwin h619
  have hgm := (grind_check_holds 13 (by decide) hκ hκw L _ _ hW []).1 (hC _ _ _ hg)
  simp only [MeaningGrindCheck] at hgm
  have hb : _root_.LeanVM.Parameters.Whir.batchGrindingBits ≠ 0 := by decide
  have hok : s.GrindOk _root_.LeanVM.Parameters.Whir.batchGrindingBits (σ (.n 602)) := by
    refine (grindOk_iff hb _).2 ?_
    rw [← hS, ← hc1]
    exact hgm.2
  have g := runsToG_grind hb s (σ (.n 602)) (hok.resolve_left hb)
  -- the challenges
  have hcap0 : capOf S = (vsRun (vsChCap 0) 5).map σ := by
    simp only [capOf, vsChCap, ↓reduceIte, vsRun5_map]
    rw [← hc 8, ← hc 9, ← hc 10, ← hc 11, ← hc 12]
    rfl
  have hch0 : challengeOf S = σ (.n (vsCh 0)) := by
    rw [Keccak.challengeOf_cells, ← hc0]
    simp only [vsCh]
    rw [c621, c620]
  set chs := (List.range 16).map fun i ↦ σ (.n (vsCh i)) with hchs
  have hchs' : challengeOf S :: ((⟨capOf S, []⟩ : Fs).squeezeN 15).1 = chs := by
    rw [hcap0, hsq, hch0, hchs, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.range_eq_range']
    rfl
  have hend : ((⟨capOf S, []⟩ : Fs).squeezeN 15).2 =
      ⟨[σ (.n 840), σ (.n 841), σ (.n 842), σ (.n 843), σ (.n 844)], []⟩ := by
    rw [hcap0, hsq]
    rfl
  refine ⟨chs, by simp [chs], fun i hi ↦ by simp [chs, List.getD_eq_getElem?_getD, hi], fun k hk ↦ ?_,
    ln, fun point sl ↦ ?_, hn⟩
  · simp only [chs, List.length_map, List.length_range] at hk
    simpa [chs] using hl k (List.mem_range.2 hk)
  · have r := g.bindFrom (f := fun _ ↦ do
        let challenges ← VerifierProgram.sampleChallenges (2 * ringMapWidth)
        let f := challenges.take ringMapWidth
        let g := challenges.drop ringMapWidth
        let coefficients := ringCoefficients f g
        let target := ringTarget sl f g
        return (target, fun rPrime ↦ ringWeight point rPrime coefficients))
      ((runsFromG_sample16 (capOf S) (challengeOf S)).bind (runsTo_ret _ _))
    refine RunsTo.of_eq r rfl rfl ?_ hend
    rw [hchs']

/-! ## `c_table` -/

/-- **Eight squarings** from the previous power `a`. -/
theorem vsSqT_holds {b s q : ℕ} {a : E} {nx : Prop}
    (ha : σ (.n (if q = 0 then vsCh (8 + b) else s + 1 + 9 * q - 2)) = a)
    (h : Stmt.HoldsList C rd σ (vsSqT b s q) nx kret) :
    σ (.n (s + 1 + 9 * q + 7)) = a ^ 2 ^ 8 ∧ nx := by
  rw [vsSqT, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl] at h
  simp only [List.map_cons, List.map_nil, vsMul] at h
  obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7, hn⟩ := h
  have e2 : ∀ t : ℕ, t + 2 - 1 = t + 1 := fun t ↦ by omega
  simp only [Atom.Holds, ↓reduceIte, Nat.add_zero, Nat.add_sub_cancel, e2,
    OfNat.ofNat_ne_zero, one_ne_zero] at m0 m1 m2 m3 m4 m5 m6 m7
  rw [ha] at m0
  refine ⟨?_, hn⟩
  rw [m7, m6, m5, m4, m3, m2, m1, m0]
  ring

/-- The steps of block `b` from term `j`: `k` squaring runs, products and stores. -/
theorem ctab_chain {b s : ℕ} : ∀ (k j : ℕ) {nx : Prop},
    σ (.n (if j = 0 then vsCh (8 + b) else s + 1 + 9 * j - 2)) =
      σ (.n (vsCh (8 + b))) ^ 2 ^ (8 * j) →
    Stmt.HoldsList C rd σ ((List.range' j k).flatMap fun q ↦
      vsSqT b s q ++ [vsMul (s + 1 + 9 * q + 8) (vsCh (q + 1)) (s + 1 + 9 * q + 7),
        vsLd (s + 1 + 9 * q + 8) 848 (8 * (q + 1) + b)]) nx kret →
    (∀ q, j ≤ q → q < j + k → LoadHolds rd (σ (.n 848)) (8 * (q + 1) + b)
      (σ (.n (vsCh (q + 1))) * σ (.n (vsCh (8 + b))) ^ 2 ^ (8 * (q + 1)))) ∧ nx
  | 0, j, _, _, h => ⟨fun q h1 h2 ↦ absurd h2 (by omega), h⟩
  | k + 1, j, _, ha, h => by
    rw [List.range'_succ, List.flatMap_cons, holdsList_append, holdsList_append] at h
    obtain ⟨e7, h⟩ := vsSqT_holds ha h
    obtain ⟨m8, l8, h⟩ := h
    simp only [Atom.Holds] at m8 l8
    have ha' : σ (.n (if j + 1 = 0 then vsCh (8 + b) else s + 1 + 9 * (j + 1) - 2)) =
        σ (.n (vsCh (8 + b))) ^ 2 ^ (8 * (j + 1)) := by
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      rw [show s + 1 + 9 * (j + 1) - 2 = s + 1 + 9 * j + 7 by omega, e7, ← pow_mul, ← pow_add,
        show 8 * (j + 1) = 8 * j + 8 by ring]
    obtain ⟨ih, hn⟩ := ctab_chain k (j + 1) ha' h
    refine ⟨fun q h1 h2 ↦ ?_, hn⟩
    rcases Nat.eq_or_lt_of_le h1 with e | h1
    · rw [← e]
      rw [m8, e7, ← pow_mul, ← pow_add] at l8
      rw [show 8 * (j + 1) = 8 * j + 8 by ring]
      exact l8
    · exact ih q h1 (by omega)

/-- **Block `b` of `c_table`**: `c[8p + b] = f_p · g_b^(2^(8p))`. -/
theorem ctab_block {b : ℕ} {nx : Prop} (h : Stmt.HoldsList C rd σ (vsCtabBlock b) nx kret) :
    (∀ p < 8, LoadHolds rd (σ (.n 848)) (8 * p + b)
      (σ (.n (vsCh p)) * σ (.n (vsCh (8 + b))) ^ 2 ^ (8 * p))) ∧ nx := by
  simp only [vsCtabBlock, holdsList_append] at h
  obtain ⟨m0, l0, h⟩ := h
  simp only [Atom.Holds] at m0 l0
  rw [List.range_eq_range'] at h
  obtain ⟨hc, hn⟩ := ctab_chain (b := b) (s := 849 + 64 * b) 7 0 (by simp) h
  refine ⟨fun p hp ↦ ?_, hn⟩
  rcases p with _ | q
  · rw [m0] at l0
    simpa using l0
  · exact hc q (by omega) (by omega)

theorem ctab_blocks : ∀ (l : List ℕ) {nx : Prop},
    Stmt.HoldsList C rd σ (l.flatMap vsCtabBlock) nx kret →
      (∀ b ∈ l, ∀ p < 8, LoadHolds rd (σ (.n 848)) (8 * p + b)
        (σ (.n (vsCh p)) * σ (.n (vsCh (8 + b))) ^ 2 ^ (8 * p))) ∧ nx
  | [], _, h => ⟨fun _ h ↦ absurd h (by simp), h⟩
  | b :: l, _, h => by
    rw [List.flatMap_cons, holdsList_append] at h
    obtain ⟨hb, h⟩ := ctab_block h
    obtain ⟨hl, hn⟩ := ctab_blocks l h
    exact ⟨fun x hx ↦ by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hb
      · exact hl x hx, hn⟩

/-- `ringCoefficients`' fold from block `j`: block `p` is `f_p` times the row raised to
`2^(8 (j + p))`. -/
theorem ringCoefficients_foldl (g : List E) : ∀ (f acc : List E) (j : ℕ),
    (f.foldl (fun (acc : List E × List E) fP ↦ (acc.1 ++ acc.2.map (fP * ·),
        acc.2.map (frobenius8 · 1))) (acc, g.map (· ^ 2 ^ (8 * j)))).1 =
      acc ++ (List.range f.length).flatMap fun p ↦ g.map fun x ↦ f.getD p 0 * x ^ 2 ^ (8 * (j + p))
  | [], acc, j => by simp
  | fP :: f, acc, j => by
    have hg : (g.map (· ^ 2 ^ (8 * j))).map (frobenius8 · 1) = g.map (· ^ 2 ^ (8 * (j + 1))) := by
      rw [List.map_map]
      refine List.map_congr_left fun x _ ↦ ?_
      simp only [Function.comp, frobenius8, ringMapWidth, ← pow_mul, ← pow_add,
        show 8 * j + 8 * 1 = 8 * (j + 1) by ring]
    have ih := ringCoefficients_foldl g f (acc ++ (g.map (· ^ 2 ^ (8 * j))).map (fP * ·)) (j + 1)
    rw [← hg] at ih
    rw [List.foldl_cons]
    refine ih.trans ?_
    rw [List.append_assoc, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    refine congrArg (acc ++ ·) (congrArg₂ (· ++ ·) ?_ ?_)
    · rw [List.map_map]
      refine List.map_congr_left fun x _ ↦ ?_
      simp
    · refine List.flatMap_congr fun p _ ↦ List.map_congr_left fun x _ ↦ ?_
      simp only [List.getD_cons_succ, show j + 1 + p = j + (p + 1) by omega]

/-- **`ringCoefficients` of eight `f`s**, block by block. -/
theorem ringCoefficients_eq {f g : List E} (hf : f.length = 8) :
    ringCoefficients f g =
      (List.range 8).flatMap fun p ↦ g.map fun x ↦ f.getD p 0 * x ^ 2 ^ (8 * (0 + p)) := by
  have hg0 : g.map (· ^ 2 ^ (8 * 0)) = g := by simp
  have e := ringCoefficients_foldl g f [] 0
  rw [hg0, hf, List.nil_append] at e
  exact e

theorem readsAt_flatMap8 {p : E} {F : ℕ → List E} (hF : ∀ q, (F q).length = 8) :
    ∀ n, (∀ q < n, ∀ b < 8, LoadHolds rd p (8 * q + b) ((F q).getD b 0)) →
      ReadsAt rd p ((List.range n).flatMap F)
  | 0, _ => by simp [ReadsAt]
  | n + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine readsAt_append.2 ⟨readsAt_flatMap8 hF n fun q hq ↦ h q (by omega), ?_⟩
    have hl : ((List.range n).flatMap F).length = 8 * n := by
      simp [List.length_flatMap, hF, mul_comm]
    rw [hl]
    intro b hb
    rw [loadHolds_mul_gen_pow]
    have := h n (by omega) b (by rw [hF] at hb; exact hb)
    rwa [List.getD_eq_getElem _ _ hb] at this

/-- **`c_table`**: the Frobenius coefficients of the sixteen challenges, then the
call of `ring_switch_target`. -/
theorem vsCtabT_holds {chs : List E} (hl : chs.length = 16)
    (hch : ∀ i < 16, σ (.n (vsCh i)) = chs.getD i 0)
    (h : Stmt.HoldsList C rd σ vsCtabT next kret) :
    ReadsAt rd (σ (.n 848)) (ringCoefficients (chs.take ringMapWidth) (chs.drop ringMapWidth)) ∧
      C "ring_switch_target" [σ (.n 585), σ (.n 847)] [σ (.n 1361)] ∧ next := by
  simp only [vsCtabT, holdsList_append] at h
  obtain ⟨-, h⟩ := h
  obtain ⟨hb, h⟩ := ctab_blocks (List.range 8) h
  obtain ⟨hc, hn⟩ := h
  refine ⟨?_, hc, hn⟩
  have hft : (chs.take ringMapWidth).length = 8 := by simp [ringMapWidth, hl]
  rw [ringCoefficients_eq hft]
  refine readsAt_flatMap8 (fun q ↦ by simp [ringMapWidth, hl]) 8 fun p hp b hb' ↦ ?_
  have e := hb b (List.mem_range.2 hb') p hp
  rw [hch p (by omega), hch (8 + b) (by omega)] at e
  have h1 : (chs.take ringMapWidth).getD p 0 = chs.getD p 0 := by
    simp [List.getD_eq_getElem?_getD, ringMapWidth, hp]
  have h3 : (chs.drop ringMapWidth).getD b 0 = chs.getD (8 + b) 0 := by
    simp [List.getD_eq_getElem?_getD, ringMapWidth, List.getElem?_drop]
  have hb8 : b < (chs.drop ringMapWidth).length := by simp [ringMapWidth, hl]; omega
  have h4 : (chs.drop ringMapWidth)[b]'hb8 = chs.getD (8 + b) 0 := by
    rw [← List.getD_eq_getElem _ 0 hb8, h3]
  rw [List.getD_eq_getElem _ _ (by simpa using hb8), List.getElem_map]
  simp only [h1, h4, zero_add]
  exact e

end
end LeanVM.Guest.B1.VerifySub
