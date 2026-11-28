/-
  LeanVM.Guest.Complete.HandLoopW

  The children's loop's words hand facts (`LoopHand`), so `main`'s (`MainHand`): each iteration's counts
  are its child's (`loopMeta_all`), and every node below it has its words hand fact, `verify_sub`'s subtree's
  from what `verify_sub` certifies (`vsVals`, `VsDown`) and `open_stacked__Lk`'s from its own path.
-/

module

public import LeanVM.Guest.Complete.HandVs

/-!
# The loop's words

* `verify_sub_wh`, `verify_keccak_wh`, `check_stack_terminal_wh`: the words hand facts of `verify_sub`'s
  certified callees, from `VsNodeVals` and `VsDown` (`verify_keccak`'s twelve values `v18 · g` on its path).
* `os_hand`: `open_stacked__Lk`'s, from its path: its rate selector `v0 = g^r`, `r < 4` (its dispatch on
  `v0` over four arms), and `v35` the `r`-th of four stored totals `g^t`, `c_k + 2·t ≤ C_k` (by the kernel).
* `wh_node`: every node but `main` and the loop; `loopHand_all`: `loopRun_countR` at the words' loop hand.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.Budget LeanVM.Guest.Value

@[expose] public section

variable {rd : Reader} {H : List Pop}

/-! ## Paths: statements that fall through -/

section Paths

variable {σ : Val}

/-- A statement of a block that falls through falls through. -/
theorem stmt_fall {s : Stmt} : ∀ {ss : List Stmt} {es : List Ev}, walk σ ss = .fall es → s ∈ ss →
    ∃ es1, walk1 σ s = .fall es1
  | [], _, _, hm => absurd hm List.not_mem_nil
  | t :: ss, es, hw, hm => by
      rw [walk] at hw
      cases h1 : walk1 σ t with
      | fall es1 =>
        rw [h1] at hw
        cases h2 : walk σ ss with
        | fall es2 =>
          rcases List.mem_cons.mp hm with rfl | hm
          · exact ⟨es1, h1⟩
          · exact stmt_fall h2 hm
        | ret _ _ => rw [h2] at hw; simp [Out.seq, Out.pre] at hw
        | stuck => rw [h2] at hw; simp [Out.seq, Out.pre] at hw
      | ret _ _ => rw [h1] at hw; simp [Out.seq] at hw
      | stuck => rw [h1] at hw; simp [Out.seq] at hw

/-- A return-free prefix of a returning path falls through. -/
theorem pre_fall {pre rest : List Stmt} {es : List Ev} {vs : List V} (hn : Stmt.noRetListS pre = true)
    (hw : walk σ (pre ++ rest) = .ret es vs) : ∃ es0, walk σ pre = .fall es0 := by
  rw [walk_append] at hw
  rcases walk_noRet pre hn with h0 | h0
  · exact h0
  · rw [h0] at hw; simp [Out.seq] at hw

/-- A dispatch that falls through is at `x = g^(j + i)`, `i` below its arms. -/
theorem pick_fall {x : V} {args rets : List V} : ∀ (gs : List String) (j : ℕ) {es : List Ev},
    pick σ x args rets j gs = .fall es → ∃ i < gs.length, σ x = ofK (addressOfIndex (j + i))
  | [], _, _, h => by simp [pick] at h
  | g :: gs, j, es, h => by
      unfold pick at h
      split_ifs at h with hx
      · exact ⟨0, by simp, by simpa using hx⟩
      · obtain ⟨i, hi, he⟩ := pick_fall gs (j + 1) h
        exact ⟨i + 1, by simp; omega, by rw [he]; congr 2; omega⟩

end Paths

/-! ## `verify_sub` -/

/-- **`verify_sub`'s words hand fact**, from its values. -/
theorem verify_sub_wh {C₁ C₂ : ℕ} {σ : Val} (h : VsNodeVals "verify_sub" σ) :
    HandFact coreProgram (whCertAt C₁ C₂) (whHandAt C₁ C₂) whOut "verify_sub" σ := by
  obtain ⟨⟨c, gc, hc⟩, h645, h409, h408, h120⟩ := h.1 rfl
  refine handFact_of (j := 15) (n := 11) (bS := ⟨395519, [(6, 276), (7, 29), (8, 38), (9, 850), (10, 58)]⟩)
    (bOS := ⟨427606, []⟩) (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide)
    (by decide) (by decide) rfl rfl (by decide +kernel) (by decide +kernel) SameOnPath.refl ?_
  intro fn hfn _
  have e := Option.some.inj (hfn.symm.trans (coreProgram_find?_at (j := idx% «verify_sub») rfl))
  subst e
  have hp : (fn% «verify_sub»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] := rfl
  rw [hp]
  set ps : List E := [V.n 0, .n 1, .n 2, .n 3, .n 4, .n 5].map σ with hps
  set vs : List E := ps ++ [V.n 42, .n 645, .n 409, .n 408, .n 120].map σ with hvs
  have a6 : argExp vs 6 = c := argExp_gpow rfl gc
  have a7 : argExp vs 7 = logG (σ (.n 645)) := rfl
  have a8 : argExp vs 8 = logG (σ (.n 409)) := rfl
  have a9 : argExp vs 9 = logG (σ (.n 408)) := rfl
  have a10 : argExp vs 10 = logG (σ (.n 120)) := rfl
  refine ⟨argsPre_gT (vs := vs) (k := 6) (e := c) gc.1 gc.2, ?_⟩
  simp only [Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, a6, a7, a8, a9, a10]
  omega

/-! ## `verify_keccak` -/

/-- The values `verify_keccak`'s words hand reads besides `v18`: each `v18 · g`. -/
def vkVs : List ℕ := [475, 508, 542, 585, 626, 669, 702, 743, 781, 824, 865, 905]

set_option maxRecDepth 100000 in
theorem vk_atoms : (Atom.const (.n 17) (word 8070450532247928836 0) ∈ VsC.atomsOf ((fn% «verify_keccak»).body.take 894) ∧
    Atom.mul (.n 18) (.n 6) (.n 17) ∈ VsC.atomsOf ((fn% «verify_keccak»).body.take 894)) ∧
    ∀ k ∈ vkVs, Atom.const (.n (k - 1)) (word 2 0) ∈ VsC.atomsOf ((fn% «verify_keccak»).body.take 894) ∧
      Atom.mul (.n k) (.n 18) (.n (k - 1)) ∈ VsC.atomsOf ((fn% «verify_keccak»).body.take 894) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem vk_noRet894 : Stmt.noRetListS ((fn% «verify_keccak»).body.take 894) = true := by decide +kernel

theorem word2_eq : word 2 0 = gen := by
  rw [show (2 : ℕ) = 2 ^ 1 by norm_num, word_two_pow (by decide), pow_one]

set_option maxHeartbeats 1000000 in
/-- **`verify_keccak`'s words hand fact**, from its table log. -/
theorem verify_keccak_wh {C₁ C₂ : ℕ} {σ : Val} (hp : PathIn coreProgram rd H "verify_keccak" σ)
    (hpre : PreAt coreProgram (VsDown rd) "verify_keccak" σ) :
    HandFact coreProgram (whCertAt C₁ C₂) (whHandAt C₁ C₂) whOut "verify_keccak" σ := by
  obtain ⟨fn0, hf0, -, es, vs, hw, hes, -⟩ := hp
  rw [coreProgram_find?_at (j := idx% «verify_keccak») rfl] at hf0
  obtain rfl := Option.some.inj hf0
  obtain ⟨τ, h4, h24, e6⟩ := (hpre _ (coreProgram_find?_at (j := idx% «verify_keccak») rfl)).1 rfl
  rw [vk_params] at e6
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at e6
  rw [← List.take_append_drop 894 (fn% «verify_keccak»).body] at hw
  have hA : ∀ a, a ∈ VsC.atomsOf ((fn% «verify_keccak»).body.take 894) → a.Holds rd σ :=
    fun a ha => hes _ (atom_mem_walk vk_noRet894 hw (atom_mem_of_atomsOf ha))
  obtain ⟨⟨m17, m18⟩, mk⟩ := vk_atoms
  have a17 : σ (.n 17) = word 8070450532247928836 0 := hA _ m17
  have a18 : σ (.n 18) = σ (.n 6) * σ (.n 17) := hA _ m18
  have e18 : σ (.n 18) = gen ^ (τ - 4) := by rw [a18, a17, e6, pow_mul_winv4 h4]
  have g18 : GPow (σ (.n 18)) (τ - 4) := ⟨e18, by omega⟩
  have gk : ∀ k ∈ vkVs, GPow (σ (.n k)) (τ - 3) := by
    intro k hk
    have c1 : σ (.n (k - 1)) = word 2 0 := hA _ (mk k hk).1
    have c2 : σ (.n k) = σ (.n 18) * σ (.n (k - 1)) := hA _ (mk k hk).2
    refine ⟨?_, by omega⟩
    rw [c2, c1, e18, word2_eq, ← pow_succ, show τ - 4 + 1 = τ - 3 by omega]
  refine handFact_of (j := 8) (n := 25) (bS := ⟨37909, [(12, 46), (13, 1), (14, 1), (15, 1), (16, 1), (17, 1),
      (18, 1), (19, 1), (20, 1), (21, 1), (22, 1), (23, 1), (24, 1)]⟩) (bOS := ⟨37909, [(6, 58)]⟩)
    (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide)
    rfl rfl (by decide +kernel) (by decide +kernel) SameOnPath.refl ?_
  intro fn hfn _
  have e := Option.some.inj (hfn.symm.trans (coreProgram_find?_at (j := idx% «verify_keccak») rfl))
  subst e
  rw [vk_params]
  refine ⟨argsPre_gT (k := 12) (e := τ - 4) (by simpa using e18) (by omega), ?_⟩
  simp only [Aff.eval, argExp, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.sum_cons,
    List.sum_nil, List.getD_cons_succ, List.getD_cons_zero, g18.logG,
      (gk 475 (by decide)).logG,
      (gk 508 (by decide)).logG,
      (gk 542 (by decide)).logG,
      (gk 585 (by decide)).logG,
      (gk 626 (by decide)).logG,
      (gk 669 (by decide)).logG,
      (gk 702 (by decide)).logG,
      (gk 743 (by decide)).logG,
      (gk 781 (by decide)).logG,
      (gk 824 (by decide)).logG,
      (gk 865 (by decide)).logG,
      (gk 905 (by decide)).logG,
    e6, logG_gen_pow (e := τ) (by omega)]
  omega

/-! ## `check_stack_terminal` -/

set_option maxHeartbeats 1000000 in
/-- **`check_stack_terminal`'s words hand fact**, from its window and `verify_sub`'s `v408`. -/
theorem check_stack_terminal_wh {C₁ C₂ : ℕ} {σ : Val} (hV : VsNodeVals "check_stack_terminal" σ)
    (hpre : PreAt coreProgram (VsDown rd) "check_stack_terminal" σ) :
    HandFact coreProgram (whCertAt C₁ C₂) (whHandAt C₁ C₂) whOut "check_stack_terminal" σ := by
  have h58 := hV.2.2 rfl
  obtain ⟨-, n, hn, e6⟩ := (hpre _ (coreProgram_find?_at (j := idx% «check_stack_terminal») rfl)).2 rfl
  refine handFact_of (j := 13) (n := 24) (bS := ⟨17697, [(6, 270), (23, 214)]⟩) (bOS := ⟨24117, [(6, 270)]⟩)
    (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide)
    rfl rfl (by decide +kernel) (by decide +kernel) SameOnPath.refl ?_
  intro fn hfn _
  have e := Option.some.inj (hfn.symm.trans (coreProgram_find?_at (j := idx% «check_stack_terminal») rfl))
  subst e
  set ps : List E := (fn% «check_stack_terminal»).params.map σ with hps
  set vs : List E := ps ++ [V.n 58].map σ with hvs
  have hlen : ps.length = 23 := by rw [hps, List.length_map]; rfl
  have a23 : argExp vs 23 = logG (σ (.n 58)) := by
    unfold argExp
    rw [hvs, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen]
    rfl
  have g6 : vs.getD 6 0 = ps.getD 6 0 := by
    rw [hvs, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
  have a6 : argExp vs 6 = argExp ps 6 := by unfold argExp; rw [g6]
  refine ⟨argsPre_gT (k := 6) (e := n) (by rw [g6]; exact e6) (by omega), ?_⟩
  simp only [Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, a23, a6]
  omega

/-! ## `open_stacked__Lk` -/

/-- `open_stacked__Lk`'s stored totals and its selection by the rate (statements `21 ..< 31`). -/
def osAtoms (cs : List ℕ) : List Atom :=
  [.const (.n 30) (word (cs.getD 0 0) 0), .load (.n 30) (.n 29) 0, .const (.n 31) (word (cs.getD 1 0) 0),
    .load (.n 31) (.n 29) 1, .const (.n 32) (word (cs.getD 2 0) 0), .load (.n 32) (.n 29) 2,
    .const (.n 33) (word (cs.getD 3 0) 0), .load (.n 33) (.n 29) 3, .mul (.n 34) (.n 29) (.n 0),
    .load (.n 35) (.n 34) 0]

/-- A dispatch on `v0` over four arms. -/
def isDisp4 : Option Stmt → Bool
  | some (.dispatch x fs _ _) => x == .n 0 && fs.length == 4
  | _ => false

/-- `open_stacked__Lk`'s shape: its totals' atoms, its dispatch on `v0` at statement `660`, no return before it,
eleven parameters. -/
noncomputable def osShapeOk (j : ℕ) (cs : List ℕ) : Bool :=
  match coreProgram[j]? with
  | some fn => (VsC.atomsOf ((fn.body.take 31).drop 21) == osAtoms cs) && isDisp4 (fn.body[660]?) &&
      Stmt.noRetListS (fn.body.take 661) && fn.params.length == 11
  | none => false

/-- The four totals are `g^t`. -/
def osPowsOk (cs ts : List ℕ) : Bool :=
  cs.length == 4 && ts.length == 4 && (List.range 4).all fun i => K.ofBits (cs.getD i 0) == g ^ ts.getD i 0

theorem isDisp4_spec {o : Option Stmt} (h : isDisp4 o = true) :
    ∃ fs args rets, o = some (.dispatch (.n 0) fs args rets) ∧ fs.length = 4 := by
  rcases o with _ | st
  · simp [isDisp4] at h
  · cases st with
    | dispatch x fs args rets =>
      simp only [isDisp4, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      exact ⟨fs, args, rets, rfl, h⟩
    | _ => simp [isDisp4] at h

set_option maxHeartbeats 1000000 in
/-- **`open_stacked__Lk`'s words hand fact**, from its path. -/
theorem os_hand {f : String} {j c C : ℕ} {cs ts : List ℕ} {C₁ C₂ : ℕ} {σ : Val}
    (hn : (coreProgram[j]?).map Fn.name = some f) (hd : j ≠ Data.whidxDa) (hl : j ≠ Data.whidxLoop)
    (hm : j ≠ Data.whidxMain) {bO b : Aff} (hc : certStat (Data.whcertJ j) = some ([], bO))
    (hh : (Data.whhandJ j).map handTriple = some ([.n 35], [], b)) (hbq : affEqB 12 b ⟨c, [(11, 2)]⟩ = true)
    (hbOq : affEqB 12 bO ⟨C, []⟩ = true) (hs : osShapeOk j cs = true)
    (hpw : osPowsOk cs ts = true) (hb : (ts.all fun t => decide (c + 2 * t ≤ C)) = true) (hC : C < 2 ^ 63)
    (hp : PathIn coreProgram rd H f σ) :
    HandFact coreProgram (whCertAt C₁ C₂) (whHandAt C₁ C₂) whOut f σ := by
  obtain ⟨fnj, hj, hname⟩ := Option.map_eq_some_iff.mp hn
  have hfj : coreProgram.find? f = some fnj := coreProgram_find?_at hj hname
  unfold osShapeOk at hs
  rw [hj] at hs
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨⟨hat, hdisp⟩, hnr⟩, hlen⟩ := hs
  simp only [osPowsOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hpw
  obtain ⟨⟨hcl, htl⟩, hpows⟩ := hpw
  obtain ⟨fn0, hf0, -, es, vs, hw, hes, -⟩ := hp
  rw [hfj] at hf0
  obtain rfl := Option.some.inj hf0
  rw [← List.take_append_drop 661 fnj.body] at hw
  have hA : ∀ a ∈ osAtoms cs, a.Holds rd σ := by
    intro a ha
    rw [← hat] at ha
    have hm1 := List.mem_of_mem_drop (atom_mem_of_atomsOf ha)
    have hm2 : Stmt.atom a ∈ fnj.body.take 661 := by
      have e : (fnj.body.take 661).take 31 = fnj.body.take 31 := by rw [List.take_take]; rfl
      rw [← e] at hm1
      exact List.mem_of_mem_take hm1
    exact hes _ (atom_mem_walk hnr hw hm2)
  -- the rate selector
  obtain ⟨fs, args, rets, hd660, hfs⟩ := isDisp4_spec hdisp
  have hmd : Stmt.dispatch (.n 0) fs args rets ∈ fnj.body.take 661 := by
    have : (fnj.body.take 661)[660]? = some (Stmt.dispatch (.n 0) fs args rets) := by
      rw [List.getElem?_take_of_lt (by norm_num)]; exact hd660
    exact List.mem_of_getElem? this
  obtain ⟨es0, h0⟩ := pre_fall hnr hw
  obtain ⟨es1, h1⟩ := stmt_fall h0 hmd
  rw [walk1] at h1
  obtain ⟨r, hr, e0⟩ := pick_fall fs 0 h1
  rw [hfs] at hr
  rw [Nat.zero_add, ← gen_pow_eq_ofK] at e0
  -- the total it selects
  have l35 : LoadHolds rd (σ (.n 34)) 0 (σ (.n 35)) := hA (.load (.n 35) (.n 34) 0) (by simp [osAtoms])
  have m34 : σ (.n 34) = σ (.n 29) * σ (.n 0) := hA (.mul (.n 34) (.n 29) (.n 0)) (by simp [osAtoms])
  rw [m34, e0, loadHolds_mul_gen_pow, Nat.add_zero] at l35
  have hsel : σ (.n 35) = word (cs.getD r 0) 0 := by
    have L0 : LoadHolds rd (σ (.n 29)) 0 (σ (.n 30)) := hA (.load (.n 30) (.n 29) 0) (by simp [osAtoms])
    have L1 : LoadHolds rd (σ (.n 29)) 1 (σ (.n 31)) := hA (.load (.n 31) (.n 29) 1) (by simp [osAtoms])
    have L2 : LoadHolds rd (σ (.n 29)) 2 (σ (.n 32)) := hA (.load (.n 32) (.n 29) 2) (by simp [osAtoms])
    have L3 : LoadHolds rd (σ (.n 29)) 3 (σ (.n 33)) := hA (.load (.n 33) (.n 29) 3) (by simp [osAtoms])
    have K0 : σ (.n 30) = word (cs.getD 0 0) 0 := hA (.const (.n 30) (word (cs.getD 0 0) 0)) (by simp [osAtoms])
    have K1 : σ (.n 31) = word (cs.getD 1 0) 0 := hA (.const (.n 31) (word (cs.getD 1 0) 0)) (by simp [osAtoms])
    have K2 : σ (.n 32) = word (cs.getD 2 0) 0 := hA (.const (.n 32) (word (cs.getD 2 0) 0)) (by simp [osAtoms])
    have K3 : σ (.n 33) = word (cs.getD 3 0) 0 := hA (.const (.n 33) (word (cs.getD 3 0) 0)) (by simp [osAtoms])
    interval_cases r
    · rw [loadHolds_func l35 L0, K0]
    · rw [loadHolds_func l35 L1, K1]
    · rw [loadHolds_func l35 L2, K2]
    · rw [loadHolds_func l35 L3, K3]
  have ht : ts.getD r 0 ∈ ts := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]; exact List.getElem_mem _
  have hbr : c + 2 * ts.getD r 0 ≤ C := by
    have := List.all_eq_true.mp hb _ ht
    simpa using this
  have g35 : GPow (σ (.n 35)) (ts.getD r 0) := by
    refine ⟨?_, by omega⟩
    calc σ (.n 35) = word (cs.getD r 0) 0 := hsel
      _ = ofK (K.ofBits (cs.getD r 0)) := word_eOfNat _
      _ = ofK (g ^ ts.getD r 0) := by rw [hpows r hr]
      _ = gen ^ ts.getD r 0 := (gen_pow_eq_ofK _).symm
  refine handFact_of (j := j) (n := 12) (bS := ⟨c, [(11, 2)]⟩) (bOS := ⟨C, []⟩) hn hd hl hm hc hh
    hbq hbOq SameOnPath.refl ?_
  intro fn hfn _
  have hfe : fn = fnj := Option.some.inj (hfn.symm.trans hfj)
  rw [hfe]
  refine ⟨fun q hq => by simp at hq, ?_⟩
  set ps : List E := fnj.params.map σ with hps
  set args : List E := ps ++ [V.n 35].map σ with hargsd
  have a11 : argExp args 11 = logG (σ (.n 35)) := by
    unfold argExp
    rw [hargsd, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hps, hlen])]
    simp [hps, hlen]
  simp only [Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, a11, g35.logG]
  omega

/-! ## Every node below the loop -/

theorem name_coreIdx {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) :
    (coreProgram[coreIdx f]?).map Fn.name = some f := by
  have hmem : f ∈ coreProgram.map (·.name) :=
    List.mem_map.mpr ⟨fn, List.mem_of_find?_eq_some hf, fn_name_of_find (P := coreProgram) hf⟩
  have hlt' : coreIdx f < coreProgram.length := coreIdx_lt hf
  have hget := List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)
  rw [List.getElem?_eq_getElem hlt', Option.map_some]
  rw [List.getElem_map] at hget
  exact congrArg some hget

variable {s : NodeStatement} {w : NodeWitness}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **A node other than `main` and the loop has its words hand fact**, its path within the honest pushes, its
values those `verify_sub` certifies and its arguments those `verify_sub` passes down. -/
theorem wh_node (hrel : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w) {C₂ : ℕ}
    {f : String} {σ : Val} (hm : f ≠ "main") (hl : f ≠ "__loop4_main")
    (hp' : PathIn coreProgram rd (Prover.honestPushes guestBytecode guestSeed s w) f σ) (hV : VsNodeVals f σ)
    (hpre : PreAt coreProgram (VsDown rd) f σ) :
    HandFact coreProgram (whCertAt (daWordsC (itemsOf s w).rows) C₂) (whHandAt (daWordsC (itemsOf s w).rows) C₂)
      whOut f σ := by
  by_cases hv : f ∈ vsNames
  swap
  · exact hand_of_pathIn hrel hlim claimThenHand ⟨hv, hl, hm⟩ hp'
  have hp := hp'
  obtain ⟨fn, hf, -⟩ := id hp
  have hloop : coreIdx f ≠ Data.whidxLoop := fun h => hl (name_at hf h wh_nodeIdx.nl)
  have hj0 : coreIdx f ≠ Data.whidxMain := fun h => hm (name_at hf h wh_nodeIdx.nm)
  cases hh : whHandAt (daWordsC (itemsOf s w).rows) C₂ f with
  | none => exact handFact_of_none hloop hh
  | some h =>
  have e : whHandAt (daWordsC (itemsOf s w).rows) C₂ f = Data.whhandJ (coreIdx f) := by
    simp only [whHandAt, handAt, hj0, ↓reduceIte]
  rw [e] at hh
  have N : ∀ {j : ℕ} {nm : String}, coreIdx f = j → (coreProgram[j]?).map Fn.name = some nm → f = nm :=
    fun hj hn => name_at hf hj hn
  rcases handIdx_ok (coreIdx f) (coreIdx_lt hf) (by rw [hh]; rfl) with hi | hi
  · have hpn := pathIdx_names _ hi
    have hn := name_coreIdx hf
    rw [hn] at hpn
    simp at hpn
    exact absurd hv hpn
  simp only [vsIdx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[8]?).map Fn.name = some "verify_keccak")
    exact verify_keccak_wh hp hpre
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[13]?).map Fn.name = some "check_stack_terminal")
    exact check_stack_terminal_wh hV hpre
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[15]?).map Fn.name = some "verify_sub")
    exact verify_sub_wh hV
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[23]?).map Fn.name = some "child_claim_list_digest")
    exact child_hand hrel hlim hp
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[259]?).map Fn.name = some "open_stacked__L0")
    exact os_hand (j := 259) (c := 189058) (C := 189724) (cs := [14331240448, 3988258816, 21810380800, 650]) (ts := [333, 211, 154, 129]) (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide) rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by norm_num) hp
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[260]?).map Fn.name = some "open_stacked__L1")
    exact os_hand (j := 260) (c := 190412) (C := 191100) (cs := [29350380437504, 1947392, 87241523200, 972777519512027136]) (ts := [344, 200, 156, 119]) (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide) rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by norm_num) hp
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[261]?).map Fn.name = some "open_stacked__L2")
    exact os_hand (j := 261) (c := 194613) (C := 195271) (cs := [895702528, 7789568, 5452595200, 60798594969501696]) (ts := [329, 202, 152, 115]) (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide) rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by norm_num) hp
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[262]?).map Fn.name = some "open_stacked__L3")
    exact os_hand (j := 262) (c := 201365) (C := 202021) (cs := [447851264, 15214, 170393600, 7599824371187712]) (ts := [328, 193, 147, 112]) (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide) rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by norm_num) hp
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[263]?).map Fn.name = some "open_stacked__L4")
    exact os_hand (j := 263) (c := 222449) (C := 223155) (cs := [15027394784002048, 16335908110336, 91479367430963200, 665600]) (ts := [353, 223, 176, 139]) (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide) rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by norm_num) hp
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[264]?).map Fn.name = some "open_stacked__L5")
    exact os_hand (j := 264) (c := 226159) (C := 226845) (cs := [14675190218752, 1020994256896, 45739683715481600, 170393600]) (ts := [343, 219, 175, 147]) (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide) rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by norm_num) hp
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[265]?).map Fn.name = some "open_stacked__L6")
    exact os_hand (j := 265) (c := 231449) (C := 232127) (cs := [917199388672, 255248564224, 5717460464435200, 42598400]) (ts := [339, 217, 172, 145]) (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide) rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by norm_num) hp
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[266]?).map Fn.name = some "open_stacked__L7")
    exact os_hand (j := 266) (c := 238190) (C := 238862) (cs := [114649923584, 63812141056, 714682558054400, 2662400]) (ts := [336, 215, 169, 141]) (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide) rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by norm_num) hp
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[267]?).map Fn.name = some "open_stacked__L8")
    exact os_hand (j := 267) (c := 253712) (C := 254434) (cs := [3847013064704524288, 66911879619936256, 7607, 21810380800]) (ts := [361, 235, 192, 154]) (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide) rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by norm_num) hp
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[268]?).map Fn.name = some "open_stacked__L9")
    exact os_hand (j := 268) (c := 262819) (C := 263557) (cs := [7157908657751982759, 33455939809968128, 7607, 1363148800]) (ts := [369, 234, 192, 150]) (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide) rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by norm_num) hp
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[269]?).map Fn.name = some "open_stacked__L10")
    exact os_hand (j := 269) (c := 274586) (C := 275320) (cs := [6401163182865383599, 16727969904984064, 2882303761517117678, 2726297600]) (ts := [367, 233, 187, 151]) (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide) rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by norm_num) hp
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[270]?).map Fn.name = some "open_stacked__L11")
    exact os_hand (j := 270) (c := 284243) (C := 284965) (cs := [3847013064704524288, 261374529765376, 5854679515581644800, 10905190400]) (ts := [361, 227, 182, 153]) (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide) rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by norm_num) hp
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[271]?).map Fn.name = some "open_stacked__L12")
    exact os_hand (j := 271) (c := 297053) (C := 297801) (cs := [7692148163548828756, 13177532509686071341, 121712, 714682558054400]) (ts := [374, 245, 196, 169]) (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide) rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by norm_num) hp
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[272]?).map Fn.name = some "open_stacked__L13")
    exact os_hand (j := 272) (c := 304174) (C := 304914) (cs := [14315817315503965518, 7908320945662591041, 973696, 357341279027200]) (ts := [370, 246, 199, 168]) (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide) rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by norm_num) hp
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[273]?).map Fn.name = some "open_stacked__L14")
    exact os_hand (j := 273) (c := 311006) (C := 311748) (cs := [10184890557298379399, 15852670688344147018, 121712, 178670639513600]) (ts := [371, 250, 196, 167]) (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide) rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by norm_num) hp

/-! ## The loop -/

theorem whloop_eq : (coreProgram[Data.whidxLoop]'wh_nodeIdx.hl) = coreProgram[Data.chidxLoop]'ch_nodeIdx.hl := rfl

theorem whloopHand_pre : Data.whloopHand.pre = [] := rfl

theorem whloopHand_eval (vs : List E) :
    Data.whloopHand.b.eval vs = iterSum + 45 * (argExp vs 16 + argExp vs 17) := by
  simp only [Data.whloopHand, Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, iterSum]
  ring

theorem sum_childClaimsW (it : NodeItems) :
    (∑ m ∈ Finset.Ico 0 it.children.length, (iterSum + 45 * childClaims it m)) + 62 = loopWordsC iterSum it := by
  unfold loopWordsC childClaims
  rw [← Finset.range_eq_Ico, sum_range_getD]

variable {al : String → Bool}

/-- **The children's loop's words hand facts.** -/
theorem loopHand_all (al : String → Bool) : LoopHand al := by
  intro s w hrel hlim hch rd σ bufs kids h k hk hkn a r hkv
  have hH : ∀ p ∈ (Memory.Tree.node "main" σ bufs kids).pops coreProgram rd,
      p ∈ Prover.honestPushes guestBytecode guestSeed s w := fun p hp => mem_of_sameStreams h.pops hp
  have hroot : VsDown rd (Memory.Tree.node "main" σ bufs kids).name [] := by
    show VsDown rd "main" []
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  have hAll := ((every_pathIn_preAt (vsPreIn hch) h.valid hH hroot).and
    (vsVals al s w hrel hlim hch rd _ h)).and (loopMeta_all al s w hrel hlim hch rd _ h)
  rw [Memory.Tree.every_node] at hAll
  have hkR := Memory.Tree.every_of_mem hAll.2 hk
  obtain ⟨hargs, h0⟩ := mainLoopCall al s w hrel hlim hch rd σ bufs kids h k hk hkn a r hkv
  have hn : (itemsOf s w).children.length < 2 ^ 64 - 1 := by
    have hb := hlim.withinMemoryBudget
    simp only [NodeWitness.memoryBudget, NodeWitness.childClaimCount] at hb
    simp only [itemsOf, NodeItems.ofWitness, List.length_map]
    omega
  have hOff : coreProgram.EveryIn rd (fun f _ => OffNode f) OffNode :=
    offNode_everyIn fun f hf _ _ _ _ _ _ _ => hf
  rw [whloop_eq]
  obtain ⟨S, hrun, hS'⟩ := loopRun_countR loop_find loopShape_loop
    (fun σ' es ks hw hes hks hR k' hk' => by
      have hO := kids_every_of_offNode hOff loopPre_callees σ' es ks hw hes hks k' hk'
      exact (hO.and (hR k' hk')).mono fun f σ'' ⟨ho, ⟨⟨hp, hpre⟩, hv⟩, _⟩ =>
        wh_node (C₂ := loopWordsC iterSum (itemsOf s w)) hrel hlim ho.1 ho.2.2 hp hv hpre)
    Data.whloopHand 62 (itemsOf s w).children.length hn (fun j => iterSum + 45 * childClaims (itemsOf s w) j)
    (fun σ' hRσ j hj ht => by
      refine ⟨fun q hq => by simp [whloopHand_pre] at hq, ?_⟩
      rw [whloopHand_eval]
      have hv := hRσ.2 rfl j hj ht
      have e16 : argExp (((coreProgram[Data.chidxLoop]'ch_nodeIdx.hl).params ++ Data.whloopHand.vps).map σ') 16 =
          logG (σ' (.n 18)) := by
        unfold argExp
        rw [List.getD_eq_getElem?_getD, List.map_append, List.getElem?_append_right (by simp [loop_params_length])]
        simp [loop_params_length, Data.whloopHand]
      have e17 : argExp (((coreProgram[Data.chidxLoop]'ch_nodeIdx.hl).params ++ Data.whloopHand.vps).map σ') 17 =
          logG (σ' (.n 19)) := by
        unfold argExp
        rw [List.getD_eq_getElem?_getD, List.map_append, List.getElem?_append_right (by simp [loop_params_length])]
        simp [loop_params_length, Data.whloopHand]
      rw [e16, e17]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hv) _)
    k hkv hkn hkR h0 hargs
  refine ⟨S, hrun, ?_⟩
  rw [← sum_childClaimsW]
  exact hS'

/-- **`main`'s words hand facts** (`GuestLeft.hand` for every allocator). -/
theorem mainHand_all (al : String → Bool) : MainHand al true := mainHand_of_loop (loopHand_all al)

/-- **`GuestLeft.hand`.** -/
theorem mainHand_alW : MainHand Memory.alW true := mainHand_all _

/-- **`GuestLeft.cycles`.** -/
theorem mainCycles_alW : MainCycles Memory.alW true := mainCycles_all _

end
end LeanVM.Guest.Complete
