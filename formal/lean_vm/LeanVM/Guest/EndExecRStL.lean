/-
  LeanVM.Guest.EndExecRStL

  `keccak_layer`'s cursor in the proof stream (`LayQ`), carried down from `verify_keccak`.
-/

module

public import LeanVM.Guest.EndExecRSt
public import LeanVM.Guest.B1.KeccakGkr.LayerHolds
public import LeanVM.Guest.B1.KeccakGkr.VkChain

/-!
# `keccak_layer`'s cursor

`LayQ J`: at an instance of `keccak_layer__L{first}`, its cursor is `stream·g^p`, its pack rounds
`y < 32` (`step_g = g^(y/8)`, `rem_g = g^(y % 8)`), and `p + 84 + 2y ≤ 8192`: room for its words.

* `pack_cur`, `rem_cur`: the two loops' records, by their iterations (`B1.VerifySub.pack8_step`,
  `packRem_step`), hold the cursor sixteen, then two words on per iteration;
* `layer_cur`: on `y`'s facts alone, a layer's body puts its last record's cursor (value
  `layOff first + 745`) `48 + 2y` words past its cursor and returns the cursor `84 + 2y` words past it;
* `vk_curs`: `verify_keccak`'s step `s` hands its layer the cursor `1 + s·(84 + 2(τ - 3))` words past
  its own, each layer's returned cursor the next one's;
* `layQ_all`: at every honest instance of a layer, by `Res.insts_down`: its only caller is
  `verify_keccak` (`Res.termCallers_all`), whose calls of it are its steps' (`vk_lay_sites`), with
  `VkQ` there (`vkQ_all`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.VerifySub
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **A layer's cursor in its stream**: `cursor = stream·g^p`, `y < 32` pack rounds, room for its
`84 + 2y` words. -/
def LayQ (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids → ∀ first < 2, f = layerName first →
    ∃ p y, σ (.n 7) = σ (.n 15) * gen ^ p ∧ y < 32 ∧ σ (.n 9) = gen ^ (y / krStep) ∧
      σ (.n 10) = gen ^ (y % krStep) ∧ p + 84 + 2 * y ≤ 8192

/-- A layer's statements before its pack rounds' setup. -/
def layA (first : ℕ) : List Stmt :=
  headT first ++ prodT (.n 7) (muB first) (prodTab first) ++ checkT (accL first) ++
    sqT first ++ rmfeBlockT (layOff first) ++
    hornerT (fun k ↦ ((prodTab first).getD k default).a) (layOff first + 544) (layOff first + 626)

/-- A layer's statements between its last record and its tail. -/
def layB (first : ℕ) : List Stmt :=
  localRoundsT (.n (layOff first + 745)) (.n (layOff first + 748)) (.n (layOff first + 746))
      (cap5 (layOff first + 740)) (layOff first + 749) 11 ++
    tReadsT (layOff first) ++ eqfT (.n (layOff first + 748)) 6 5 25 (layOff first + 1121) ++
    weightT first (layOff first)

/-- A layer's tail. -/
def layTail (first : ℕ) : List Stmt :=
  tailT (layOff first) (weightEnd first (layOff first)) (weightVal first (layOff first))

/-- The last statements of a layer's tail: the returned cursor, `g^36` past the last record's. -/
def layEnd (first : ℕ) : List Stmt :=
  let W := weightEnd first (layOff first)
  [.atom (.const (.n (topV W + 310)) (word 68719476736 0)),
    .atom (.mul (.n (topV W + 311)) (.n (layOff first + 745)) (.n (topV W + 310))),
    .atom (.copy (.n (topV W + 312)) (.n (topV W + 311))),
    .ret [.n (topV W + 305), .n (topV W + 306), .n (topV W + 307), .n (topV W + 308),
      .n (topV W + 309), .n (topV W + 312)]]

/-- A layer's tail before `layEnd`. -/
def layTailPre (first : ℕ) : List Stmt := (layTail first).take ((layTail first).length - 4)

end

public section

variable {rd : Reader}

/-! ## Blocks without a return -/

/-- **The atoms and calls of a block without a return hold.** -/
theorem holdsList_mem {C : CallRel} {σ : Val} : ∀ {ss : List Stmt}, Stmt.noRetList ss = true →
    ∀ {next : Prop} {kret : List E → Prop}, Stmt.HoldsList C rd σ ss next kret →
      (∀ a, Stmt.atom a ∈ ss → a.Holds rd σ) ∧
        (∀ f args rets, Stmt.call f args rets ∈ ss → C f (args.map σ) (rets.map σ))
  | [], _, _, _, _ => ⟨fun _ h ↦ absurd h List.not_mem_nil, fun _ _ _ h ↦ absurd h List.not_mem_nil⟩
  | s :: ss, hn, next, kret, h => by
    simp only [Stmt.noRetList, Bool.and_eq_true] at hn
    simp only [Stmt.HoldsList] at h
    rw [holds_noRet s hn.1] at h
    obtain ⟨hs, hr⟩ := h
    obtain ⟨ia, ic⟩ := holdsList_mem hn.2 hr
    refine ⟨fun a ha ↦ ?_, fun f args rets hc ↦ ?_⟩
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact hs.1
      · exact ia a ha
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact hs.1
      · exact ic f args rets hc

/-! ## The loops' records -/

theorem word_g36 : word 68719476736 0 = gen ^ 36 := by
  rw [show (68719476736 : ℕ) = 2 ^ 36 from rfl]; exact word_two_pow (by decide)

/-- **The eight-round loop's records**: record `j` holds the cursor `16 j` words on, `j ≤ n`. -/
theorem pack_cur {first : ℕ} (hf : first < 2) {sg rec pp pt tb cur : E} {n : ℕ} (hn : n < 32)
    (hsg : sg = gen ^ n) (hloop : 1 + sg ≠ 0 → coreProgram.Rel rd (packLoopName first) [1, sg, rec, pp, pt, tb] [])
    (h0 : LoadHolds rd rec (5 * krCap) cur) :
    ∀ j ≤ n, LoadHolds rd (rec * gen ^ j) (5 * krCap) (cur * gen ^ (16 * j)) := by
  have hlt : n < ordG := by unfold ordG; omega
  intro j hj
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    have hne := gen_pow_ne_one (h := n) (by omega) hlt
    obtain ⟨fn, hfn, hb, hp⟩ := find_pack8 hf
    have hs := loop_sound (P := coreProgram) (f := packLoopName first) (ps := [sg, rec, pp, pt, tb])
      (N := sg) (m := n) (B := Pack8Step rd rec pp pt)
      (fun d x h' => pack8_step hfn hb hp d x sg rec pp pt tb h') hsg hlt
      0 (by rw [pow_zero]; exact hloop (by rw [hsg]; exact hne)) j (Nat.zero_le _) (by omega)
    obtain ⟨cap, cur', cl, sc, rs, ms, chs, cl', sc', cap', h0', -, -, -, -, -, h1'⟩ := hs
    have e : cur' = cur * gen ^ (16 * j) := loadHolds_unique h0'.2.1 (by simpa using ih (by omega))
    have h1 := h1'.2.1
    rw [loadHolds_rec_succ, e] at h1
    have e2 : cur * gen ^ (16 * (j + 1)) = cur * gen ^ (16 * j) * gen ^ 16 := by
      rw [mul_assoc, ← pow_add]; ring_nf
    rw [e2]
    exact h1

/-- **The remainder loop's records**: record `j` holds the cursor `2 j` words on, `j ≤ m`. -/
theorem rem_cur {first : ℕ} (hf : first < 2) {rg rec pp pt tb cur : E} {m : ℕ} (hm : m < 32)
    (hrg : rg = gen ^ m) (hrem : 1 + rg ≠ 0 → coreProgram.Rel rd (remLoopName first) [1, rg, rec, pp, tb, pt] [])
    (h0 : LoadHolds rd rec (5 * krCap) cur) :
    ∀ j ≤ m, LoadHolds rd (rec * gen ^ j) (5 * krCap) (cur * gen ^ (2 * j)) := by
  have hlt : m < ordG := by unfold ordG; omega
  intro j hj
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    have hne := gen_pow_ne_one (h := m) (by omega) hlt
    obtain ⟨fn, hfn, hb, hp⟩ := find_packRem hf
    have hs := loop_sound (P := coreProgram) (f := remLoopName first) (ps := [rg, rec, pp, tb, pt])
      (N := rg) (m := m) (B := PackRemStep rd rec pp pt)
      (fun d x h' => packRem_step hfn hb hp d x rg rec pp tb pt h') hrg hlt
      0 (by rw [pow_zero]; exact hrem (by rw [hrg]; exact hne)) j (Nat.zero_le _) (by omega)
    obtain ⟨cap, cur', cl, sc, r, g1, g2, h0', -, -, -, h1'⟩ := hs
    have e : cur' = cur * gen ^ (2 * j) := loadHolds_unique h0'.2.1 (by simpa using ih (by omega))
    have h1 := h1'.2.1
    rw [loadHolds_rec_succ, e] at h1
    have e2 : cur * gen ^ (2 * (j + 1)) = cur * gen ^ (2 * j) * gen ^ 2 := by
      rw [mul_assoc, ← pow_add]; ring_nf
    rw [e2]
    exact h1

/-! ## A layer's cursors -/

theorem layerT_split {first : ℕ} : layerT first = layA first ++ (packSetupT (layOff first) first ++
    (lastT (layOff first) ++ (layB first ++ layTail first))) := by
  simp only [layerT, layA, layB, layTail, List.append_assoc]

theorem layA_noRet {first : ℕ} (hf : first < 2) : Stmt.noRetList (layA first) = true := by
  interval_cases first <;> decide +kernel

theorem layB_noRet {first : ℕ} (hf : first < 2) : Stmt.noRetList (layB first) = true := by
  interval_cases first <;> decide +kernel

theorem layTailPre_noRet {first : ℕ} (hf : first < 2) : Stmt.noRetList (layTailPre first) = true := by
  interval_cases first <;> decide +kernel

theorem layTail_split {first : ℕ} (hf : first < 2) : layTail first = layTailPre first ++ layEnd first := by
  interval_cases first <;> exact (stmtsEqb_sound (by decide +kernel)).symm

/-- **A layer's cursors**, on `y`'s facts alone: the last record's cursor `48 + 2y` words on, the
returned cursor `84 + 2y`. -/
theorem layer_cur {first : ℕ} (hf : first < 2) {C : CallRel} (hC : CallRel.Le C (coreProgram.Rel rd))
    {σ : Val} {kret : List E → Prop} {y : ℕ} (hy : y < 32) (h9 : σ (.n 9) = gen ^ (y / krStep))
    (h10 : σ (.n 10) = gen ^ (y % krStep)) {body : List Stmt} (hbd : body = layerT first)
    (h : Stmt.HoldsList C rd σ body False kret) :
    σ (.n (layOff first + 745)) = σ (.n 7) * gen ^ (48 + 2 * y) ∧
      ∃ ws, kret (ws ++ [σ (.n 7) * gen ^ (84 + 2 * y)]) := by
  subst hbd
  rw [layerT_split, holdsList_append, holdsList_noRet _ (layA_noRet hf)] at h
  replace h := h.2
  rw [holdsList_append] at h
  obtain ⟨-, hrec0, -, hloopC, e727, -, hremC, h⟩ := packSetupT_holds h
  rw [holdsList_append] at h
  obtain ⟨e739, hlast, h⟩ := lastT_holds h
  rw [holdsList_append, holdsList_noRet _ (layB_noRet hf)] at h
  replace h := h.2
  rw [layTail_split hf, holdsList_append, holdsList_noRet _ (layTailPre_noRet hf)] at h
  replace h := h.2
  simp only [layEnd, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨c310, m311, c312, hk⟩ := h
  have hn : y / krStep < 32 := by simp only [krStep]; omega
  have hm : y % krStep < 32 := by simp only [krStep]; omega
  have hP := pack_cur hf hn h9 (fun hne ↦ hC _ _ _ (hloopC hne)) hrec0.2.1 _ le_rfl
  rw [← h9] at hP
  have hR := rem_cur hf hm h10 (fun hne ↦ hC _ _ _ (hremC hne)) hP _ le_rfl
  rw [← h10, ← e727, ← e739] at hR
  have e745 := loadHolds_unique hlast.2.1 hR
  have hy' : 16 * (y / krStep) + 2 * (y % krStep) = 2 * y := by simp only [krStep]; omega
  have hcur : σ (.n (layOff first + 745)) = σ (.n 7) * gen ^ (48 + 2 * y) := by
    rw [e745, mul_assoc, mul_assoc, ← pow_add, ← pow_add, hy']
  rw [c312, m311, c310, word_g36, hcur, mul_assoc, ← pow_add,
    show 48 + 2 * y + 36 = 84 + 2 * y by ring] at hk
  exact ⟨hcur, [σ (.n (topV (weightEnd first (layOff first)) + 305)),
    σ (.n (topV (weightEnd first (layOff first)) + 306)), σ (.n (topV (weightEnd first (layOff first)) + 307)),
    σ (.n (topV (weightEnd first (layOff first)) + 308)), σ (.n (topV (weightEnd first (layOff first)) + 309))], hk⟩

/-- `keccak_layer__L{first}`, found, its body the template and its parameters the first sixteen. -/
theorem layer_found {first : ℕ} (hf : first < 2) :
    ∃ fn, coreProgram.find? (layerName first) = some fn ∧ fn.body = layerT first ∧
      fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 12,
        .n 13, .n 14, .n 15] := by
  interval_cases first
  · exact ⟨fn% «keccak_layer__L0», find_layer265, layer_body265, rfl⟩
  · exact ⟨fn% «keccak_layer__L1», find_layer264, layer_body264, rfl⟩

/-- **A layer's returned cursor**, from its relation: `84 + 2y` words past its cursor. -/
theorem layer_ret {first : ℕ} (hf : first < 2) {args rets : List E} {y : ℕ} (hy : y < 32)
    (h : coreProgram.Rel rd (layerName first) args rets) (h9 : args.getD 9 0 = gen ^ (y / krStep))
    (h10 : args.getD 10 0 = gen ^ (y % krStep)) :
    ∃ ws, rets = ws ++ [args.getD 7 0 * gen ^ (84 + 2 * y)] := by
  obtain ⟨fn, hfn, hb, hp⟩ := layer_found hf
  obtain ⟨σ, hpar, hbody⟩ := (rel_iff_sem hfn args rets).mp h
  rw [hp] at hpar
  have hg : ∀ k < 16, args.getD k 0 = σ (.n k) := fun k hk ↦ by
    rw [← hpar]; interval_cases k <;> rfl
  rw [hg 9 (by decide)] at h9
  rw [hg 10 (by decide)] at h10
  obtain ⟨-, ws, hk⟩ := layer_cur hf (fun _ _ _ h ↦ h) hy h9 h10 hb hbody
  exact ⟨ws, by rw [hg 7 (by decide)]; exact hk.symm⟩

/-! ## `verify_keccak`'s steps -/

theorem getD_map_V {σ : Val} {l : List V} {k : ℕ} (hk : k < l.length) :
    (l.map σ).getD k 0 = σ (l.getD k (.n 0)) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]

theorem getD_snoc {ws : List E} {x : E} : (ws ++ [x]).getD ws.length 0 = x := by
  simp [List.getD_eq_getElem?_getD]

/-- The value after which step `s` from `b` makes its call. -/
def stepT0 (s b : ℕ) : ℕ := iotaSegEnd s (b + 6 + flipSz s * (iotaUsed s).length)

/-- Step `s`'s call: callee, arguments, returns (`stepTailT`'s). -/
def stepCall (s b : ℕ) (cap : List ℕ) (cur _cb _pn : ℕ) : String × List V × List V :=
  let T := stepT0 s b
  if s = 0 then
    ("keccak_layer__L1", cap.map .n ++ [.n 160, .n 161, .n (T + 1), .n (T + 3), .n 35, .n 49, .n 162,
      .n (T + 5), .n (T - 1), .n 11, .n 12], (List.range 6).map fun j ↦ .n (T + 6 + j))
  else
    ("keccak_layer__L0", cap.map .n ++ [.n T, .n (T + 1), .n cur, .n (T + 3), .n 35, .n 49, .n (T + 5),
      .n (T + 7), .n (T - 1), .n 11, .n 12], (List.range 6).map fun j ↦ .n (T + 8 + j))

theorem stepCall_mem (s b : ℕ) (cap : List ℕ) (cur cb pn : ℕ) :
    Stmt.call (stepCall s b cap cur cb pn).1 (stepCall s b cap cur cb pn).2.1
      (stepCall s b cap cur cb pn).2.2 ∈ stepT s b cap cur cb pn := by
  unfold stepT stepCall stepTailT stepT0
  split_ifs <;> simp

theorem step0_atoms (b : ℕ) (cap : List ℕ) (cur cb pn : ℕ) :
    Stmt.atom (.const (.n (stepT0 0 b)) (word 2 0)) ∈ stepT 0 b cap cur cb pn ∧
      Stmt.atom (.mul (.n (stepT0 0 b + 1)) (.n 5) (.n (stepT0 0 b))) ∈ stepT 0 b cap cur cb pn := by
  unfold stepT stepTailT stepT0
  simp

/-- The steps' first values, capacities, cursors, claims and next claims (`vkStepsT`'s). -/
def vkB (s : ℕ) : ℕ := [449, 490, 525, 559, 602, 643, 686, 719, 760, 798, 841, 882].getD s 0
def vkCap (s : ℕ) : List ℕ :=
  let b := [153, 484, 519, 553, 596, 637, 680, 713, 754, 792, 835, 876].getD s 0
  [b, b + 1, b + 2, b + 3, b + 4]
def vkCurA (s : ℕ) : ℕ := [0, 489, 524, 558, 601, 642, 685, 718, 759, 797, 840, 881].getD s 0
def vkCb (s : ℕ) : ℕ := [162, 162, 483, 518, 552, 595, 636, 679, 712, 753, 791, 834].getD s 0
def vkPn (s : ℕ) : ℕ := [0, 483, 518, 552, 595, 636, 679, 712, 753, 791, 834, 875].getD s 0

/-- Step `s`. -/
def vkStep (s : ℕ) : List Stmt := stepT s (vkB s) (vkCap s) (vkCurA s) (vkCb s) (vkPn s)

/-- Step `s`'s call. -/
def vkCall (s : ℕ) : String × List V × List V := stepCall s (vkB s) (vkCap s) (vkCurA s) (vkCb s) (vkPn s)

/-- The value of the cursor step `s` hands its layer. -/
def vkCurV (s : ℕ) : ℕ := if s = 0 then stepT0 0 (vkB 0) + 1 else vkCurA s

theorem vkStepsT_eq : vkStepsT = ((List.range 12).map vkStep).flatten :=
  stmtsEqb_sound (by decide +kernel)

/-- The calls' cursors, rates and streams at their places, each step's returned cursor the next
one's cursor. -/
theorem vkCall_facts : (List.range 12).all (fun s ↦ (vkCall s).2.1.length == 16 &&
    (vkCall s).2.1.getD 7 (.n 0) == .n (vkCurV s) && (vkCall s).2.1.getD 9 (.n 0) == .n 35 &&
    (vkCall s).2.1.getD 10 (.n 0) == .n 49 && (vkCall s).2.1.getD 15 (.n 0) == .n 12 &&
    (vkCall s).2.2.length == 6 &&
    (s == 11 || (vkCall s).2.2.getD 5 (.n 0) == .n (vkCurV (s + 1))) &&
    ((vkCall s).1 == layerName (if s = 0 then 1 else 0))) = true := by
  decide +kernel

theorem vkFirstT_noRet : Stmt.noRetList vkFirstT = true := by decide +kernel

theorem vkStepsT_noRet : Stmt.noRetList vkStepsT = true := by decide +kernel

/-- **`verify_keccak`'s cursors**: step `s` hands its layer the cursor `1 + s·(84 + 2(τ - 3))` words
past its own; and the pack rounds' step and remainder are `τ - 3`'s. -/
theorem vk_curs {C : CallRel} (hC : CallRel.Le C (coreProgram.Rel rd)) {σ : Val}
    {kret : List E → Prop} {τ : ℕ} (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28) (htg : σ (.n 6) = gen ^ τ)
    {body : List Stmt} (hbd : body = vkT) (hb : Stmt.HoldsList C rd σ body False kret) :
    σ (.n 35) = gen ^ ((τ - 3) / krStep) ∧ σ (.n 49) = gen ^ ((τ - 3) % krStep) ∧
      ∀ s < 12, σ (.n (vkCurV s)) = σ (.n 5) * gen ^ (1 + s * (84 + 2 * (τ - 3))) := by
  subst hbd
  rw [vkT, holdsList_append, holdsList_append, holdsList_append, holdsList_append, holdsList_append] at hb
  obtain ⟨-, -, h33, h47, -, -, -, -, -, -, -, -, hb⟩ := vkHeadT_holds hτ1 hτ2 htg hb
  rw [holdsList_noRet _ vkFirstT_noRet] at hb
  replace hb := hb.2
  rw [holdsList_noRet _ vkStepsT_noRet] at hb
  obtain ⟨ha, hc⟩ := holdsList_mem vkStepsT_noRet hb.1
  have hmem : ∀ s < 12, ∀ x ∈ vkStep s, x ∈ vkStepsT := fun s hs x hx ↦ by
    rw [vkStepsT_eq]
    exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩, hx⟩
  have hF := fun s (hs : s < 12) ↦ List.all_eq_true.mp vkCall_facts s (List.mem_range.mpr hs)
  refine ⟨h33, h47, fun s hs ↦ ?_⟩
  induction s with
  | zero =>
    obtain ⟨a1, a2⟩ := step0_atoms (vkB 0) (vkCap 0) (vkCurA 0) (vkCb 0) (vkPn 0)
    have e1 := ha _ (hmem 0 (by decide) _ a1)
    have e2 := ha _ (hmem 0 (by decide) _ a2)
    simp only [Atom.Holds] at e1 e2
    show σ (.n (stepT0 0 (vkB 0) + 1)) = _
    rw [e2, e1, word_gen]
    simp
  | succ s ih =>
    have ih := ih (by omega)
    have hcl := hc _ _ _ (hmem s (by omega) _ (stepCall_mem s (vkB s) (vkCap s) (vkCurA s) (vkCb s) (vkPn s)))
    have hf := hF s (by omega)
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hf
    obtain ⟨⟨⟨⟨⟨⟨⟨hl16, h7⟩, h9⟩, h10⟩, -⟩, hl6⟩, h5⟩, hname⟩ := hf
    rcases h5 with h5 | h5
    · omega
    change C (vkCall s).1 ((vkCall s).2.1.map σ) ((vkCall s).2.2.map σ) at hcl
    rw [hname] at hcl
    have hfirst : (if s = 0 then 1 else 0) < 2 := by split <;> omega
    obtain ⟨ws, hws⟩ := layer_ret hfirst (y := τ - 3) (by omega) (hC _ _ _ hcl)
      (by rw [getD_map_V (by omega), h9]; exact h33) (by rw [getD_map_V (by omega), h10]; exact h47)
    have hlw : ws.length = 5 := by
      have := congrArg List.length hws
      simp only [List.length_map, List.length_append, List.length_singleton] at this
      omega
    have e := congrArg (·.getD 5 0) hws
    rw [getD_map_V (by omega), h5, ← hlw, getD_snoc, getD_map_V (by omega), h7, ih, mul_assoc,
      ← pow_add] at e
    rw [e]
    congr 2
    ring

/-! ## Down from `verify_keccak` -/

/-- **`verify_keccak` calls a layer only at its steps' calls.** -/
theorem vk_lay_sites : Res.sitesB (fun f args _ ↦ (f != "keccak_layer__L0" && f != "keccak_layer__L1") ||
    (List.range 12).any fun s ↦ args == (vkCall s).2.1) vkT = true := by
  decide +kernel

theorem layer_not_loop : (fn% «keccak_layer__L0»).loop = false ∧ (fn% «keccak_layer__L1»).loop = false := by
  decide +kernel

/-- A callee's sixteen parameters, matched to a call's arguments. -/
theorem params16 {σ σ' : Val} {l : List V} (hl : l.length = 16)
    (h : ([.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 12, .n 13, .n 14,
      .n 15] : List V).map σ = l.map σ') : ∀ k < 16, σ (.n k) = σ' (l.getD k (.n 0)) := by
  intro k hk
  have e := congrArg (·.getD k 0) h
  rw [getD_map_V (by simp; omega), getD_map_V (by omega)] at e
  rw [← e]
  congr 1
  interval_cases k <;> rfl

variable {r : Ref}

/-- **A layer's cursor passes down from `verify_keccak`.** -/
theorem layQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) LayQ := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph _
    f σ bufs kids hJt first hf hfL
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  obtain ⟨fn, hfn, hpar, -⟩ := hJv
  have hcf : c.f = f := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  obtain ⟨fn', hfn', -, hp'⟩ := layer_found hf
  rw [hfL] at hfn
  obtain rfl : fn = fn' := Option.some.inj (hfn.symm.trans hfn')
  -- the caller is `verify_keccak`
  have hmem : (layerName first, "verify_keccak") ∈ Res.termCallers := by
    refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
    interval_cases first
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI))
    hw c hc) _ hmem
  have hnI := Da.fn_name_of_find hfI
  rw [hcf, hfL] at hcal
  simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
  have hvk : fI = "verify_keccak" := by
    rcases hcal with h | ⟨h, hl⟩
    · rw [← hnI, h]
    · exfalso
      rw [hnI] at h
      subst h
      obtain ⟨fl, hfl, -, -⟩ := layer_found hf
      obtain rfl : fnI = fl := Option.some.inj (hfI.symm.trans hfl)
      interval_cases first
      · rw [Option.some.inj (hfl.symm.trans find_layer265), layer_not_loop.1] at hl; cases hl
      · rw [Option.some.inj (hfl.symm.trans find_layer264), layer_not_loop.2] at hl; cases hl
  subst hvk
  obtain rfl : fnI = fn% «verify_keccak» := Option.some.inj (hfI.symm.trans find_vk)
  -- the step
  have hs := Res.calls_sites (show Res.sitesB _ (fn% «verify_keccak»).body = true by
    rw [vk_body]; exact vk_lay_sites) hw c hc
  rw [hcf, hfL] at hs
  have hs' : ∃ s < 12, c.args = (vkCall s).2.1 := by
    interval_cases first <;>
    · simp only [layerName, bne_self_eq_false, Bool.false_and, Bool.and_false, Bool.false_or,
        List.any_eq_true, List.mem_range, beq_iff_eq] at hs
      exact hs
  obtain ⟨s, hs12, hargs⟩ := hs'
  have hF := List.all_eq_true.mp vkCall_facts s (List.mem_range.mpr hs12)
  simp only [Bool.and_eq_true, beq_iff_eq] at hF
  obtain ⟨⟨⟨⟨⟨⟨⟨hl16, h7⟩, h9⟩, h10⟩, h15⟩, -⟩, -⟩, -⟩ := hF
  rw [hargs, hp'] at hpar
  have hk := params16 hl16 hpar
  -- `verify_keccak`'s cursors
  obtain ⟨p, τ, e5, e6, hτ9, hτ28, hroom⟩ := vkQ_all hr I hI σI bufsI kidsI hIt
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
  have hfs : ∀ f', 1 ≤ B2C.fs f' := fun f' ↦ by
    unfold B2C.fs; split <;> simp [B2C.mainFrame, Data.mainCells, Data.jtSlots]
  obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv hfI
  obtain ⟨h35, h49, hcur⟩ := vk_curs (fun _ _ _ h ↦ Res.KidRel.rel h) hτ9 hτ28 e6 vk_body hb
  have hL : (s + 1) * (84 + 2 * (τ - 3)) ≤ 12 * (84 + 2 * (τ - 3)) := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at hL
  refine ⟨p + (1 + s * (84 + 2 * (τ - 3))), τ - 3, ?_, by omega, ?_, ?_, ?_⟩
  · rw [hk 7 (by decide), hk 15 (by decide), h7, h15, hcur s hs12, e5, mul_assoc, ← pow_add]
  · rw [hk 9 (by decide), h9, h35]
  · rw [hk 10 (by decide), h10, h49]
  · unfold vkNeed at hroom
    omega

/-- **A layer's cursor at every honest instance.** -/
theorem layQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, LayQ J := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  refine Res.insts_down (layQ_step hr) r.T _ r.hdr hv (fun J h ↦ h) (fun J rest he ↦ ?_)
  obtain ⟨J', rest', he', ht, -⟩ := head_insts (fs := B2C.fs) (lp := coreProgram.loop) (H := B2C.H) r.T
    (0, r.T.block B2C.fs coreProgram.loop) r.hdr
  rw [he'] at he
  obtain ⟨rfl, -⟩ := List.cons.inj he
  intro f σ bufs kids hJt first hf hfL
  have hn := hr.name
  rw [← ht, hJt] at hn
  simp only [Tree.name] at hn
  subst hn
  interval_cases first <;> exact absurd hfL (by decide)

end

end LeanVM.Guest.EndExec
