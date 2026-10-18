/-
  LeanVM.Guest.B1.Sig.XmssComplete

  One layer of `verify_lean_xmss` is complete: from a layer signature whose root is the one the
  layer computes, a valuation under which the layer holds.
-/

module

public import LeanVM.Guest.B1.Sig.XmssLayer
public import LeanVM.Guest.B1.Sig.Congr

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanXmss LeanXmss.Concrete

@[expose] public section

variable {C : CallRel} {rd : Reader} {inst : HasQuery LeanXmss.HashSpec Id}

/-! ## Bounds -/

theorem cCodeword_tips_lt (w : Wots) (power : Nat → V) (G : Nat) (target : E) (d0 : V) (b : Nat) :
    ∀ i < 3 * G + 1, NB (cCodeword w power G target d0 b).2.1
      ((cCodeword w power G target d0 b).2.2.getD i (.n 0, .n 0)).1 := by
  intro i hi
  simp only [cCodeword]
  have hg := cGroup_snd_ge w power (cGroups w power G 0 (.n 0) (.n 0) b).2.2.2.1
    (cGroups w power G 0 (.n 0) (.n 0) b).2.2.2.2 (3 * G) 1 false (cGroups w power G 0 (.n 0) (.n 0) b).2.1
  have h5 := groupStart_ge false (cGroups w power G 0 (.n 0) (.n 0) b).2.1
  have hst := ws_lt_stride w.lx
  have hlen := cGroups_tips_length w power G 0 (.n 0) (.n 0) b
  by_cases h : i < 3 * G
  · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact h)]
    exact ((cGroups_tips_lt w power G 0 (.n 0) (.n 0) b i h).1).mono (by omega)
  · rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen, show i - 3 * G = 0 by omega]
    simp only [List.getD_cons_zero, groupTips]
    exact ⟨_, by simp only [chainStride] at hg ⊢; omega, rfl⟩

theorem hashValues_snd_lt (pp a : V) (val : Nat → V) (n b : Nat) :
    NB (b + hashValuesSize n) (hashValues pp a val n b).2 := by
  rw [hashValues_eq]
  simp only [hashValuesSize]
  split <;> (rename_i h; refine ⟨_, ?_, rfl⟩; omega)

theorem merkle_snd_lt (pp : V) (bit node : Nat → V) (addr : Nat → Nat) (isEnd : Nat → Bool) :
    ∀ (m l : Nat) (cur : V) (b : Nat), NB b cur →
      NB (merkle pp bit node addr isEnd m l cur b).2.2 (merkle pp bit node addr isEnd m l cur b).2.1
  | 0, _, _, _, h => h
  | m + 1, l, cur, b, _ => by
      rw [merkle_eq]
      exact merkle_snd_lt pp bit node addr isEnd m (l + 1) _ _ ⟨_, by omega, rfl⟩

theorem canonical_chainFrom (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i : Nat) :
    ∀ m s v, IsCanonical128 (chainFrom lx pp adr idx i m s v).1 ∧ IsCanonical128 (chainFrom lx pp adr idx i m s v).2
  | 0, _, _ => isCanonical128_hb _
  | m + 1, s, _ => canonical_chainFrom lx pp adr idx i m (s + 1) _

theorem canonical_tipPair (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i d : Nat) {x : E}
    (hx : IsCanonical128 x) : IsCanonical128 (tipPair lx pp adr idx i d x).1 := by
  unfold tipPair
  split
  · exact hx
  · exact (canonical_chainFrom lx pp adr idx i _ _ _).1

/-! ## The step addresses -/

theorem xStepAddrs_complete {σ : Val} {idx : V} {a : Nat} (hidx : NB a idx) :
    Completes C rd a (a + 6) (xStepAddrs idx a) σ (fun σ' =>
      (∀ s < 3, σ' (.n (a + 2 * s)) = word (tw 1 + s * stepMul) 0 0 ∧
        σ' (.n (a + 2 * s + 1)) = σ idx + word (tw 1 + s * stepMul) 0 0) ∧ AgreeBelow a σ σ') := by
  set w := fun s : Nat => word (tw 1 + s * stepMul) 0 0
  set σ' := upds σ [(a, w 0), (a + 1, σ idx + w 0), (a + 2, w 1), (a + 3, σ idx + w 1), (a + 4, w 2),
    (a + 5, σ idx + w 2)]
  have he : Ext a (a + 6) σ σ' := upds_ext σ _ (by simp)
  have hv : ∀ s < 3, σ' (.n (a + 2 * s)) = w s ∧ σ' (.n (a + 2 * s + 1)) = σ idx + w s := by
    intro s hs
    interval_cases s <;> simp [σ', upds, Function.update_apply] <;> intro h <;> omega
  refine ⟨σ', he, ⟨hv, he.agree⟩, fun next kret hn => (xStepAddrs_iff idx a).mpr ⟨fun s hs => ?_, hn⟩⟩
  rw [he.below hidx]
  exact hv s hs

theorem cCodeword_snd_gt (w : Wots) (power : Nat → V) (G : Nat) (target : E) (d0 : V) (b : Nat) :
    b < (cCodeword w power G target d0 b).2.1 := by
  simp only [cCodeword]
  have hgsb := cGroups_snd_ge w power G 0 (.n 0) (.n 0) b
  have hLb := cGroup_snd_ge w power (cGroups w power G 0 (.n 0) (.n 0) b).2.2.2.1
    (cGroups w power G 0 (.n 0) (.n 0) b).2.2.2.2 (3 * G) 1 false (cGroups w power G 0 (.n 0) (.n 0) b).2.1
  have h5 := groupStart_ge false (cGroups w power G 0 (.n 0) (.n 0) b).2.1
  omega

theorem xStepAddrs_below {idx : V} {a : Nat} (hidx : NB a idx) : NumBelow (a + 6) (Stmt.valsList (xStepAddrs idx a)) := by
  simp only [xStepAddrs, List.range_succ, List.range_zero, List.nil_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.cons_append, List.nil_append, cst, addS, valsList_cons, valsList_nil, Stmt.vals,
    Atom.vals]
  have hi := hidx.mono (show a ≤ a + 6 by omega)
  exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons hi (.cons ⟨_, by omega, rfl⟩
    (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons hi (.cons ⟨_, by omega, rfl⟩
    (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons hi (.cons ⟨_, by omega, rfl⟩ (.nil _))))))))))))

/-- A layer's node addresses as the tree's tweaks. -/
theorem node_cells {σ : Val} {L layer : Nat} (hl : layer < 2) (hpre : XPre σ L) {key : KeyIndex}
    (hkey : key.val = L / 2 ^ (16 * layer)) :
    ∀ l < layerHeight, cellBytes (mAddr σ (fun l => .n (128 - 3 * (16 * layer + l)))
      (fun l => tw 3 + (l + 1) * hiMul + layer * lxTop) (fun l => 16 * layer + l + 1 == 32) l) =
      tweakBytes (.node ⟨layer, hl⟩ (l + 1) (key.val / 2 ^ (l + 1))) := fun l hl16 => by
  have hL := hpre.lt
  simp only [layerHeight] at hl16
  rw [tweakBytes_node, hkey]
  simp only [mAddr]
  by_cases he : 16 * layer + l + 1 = 32
  · have h1 : layer = 1 := by omega
    subst h1
    simp only [he, beq_self_eq_true, ↓reduceIte]
    rw [node_addr_end hL (by omega)]
  · have he' : (16 * layer + l + 1 == 32) = false := by simpa using he
    simp only [he', Bool.false_eq_true, ↓reduceIte]
    rw [show 16 * layer + (l + 1) = 16 * layer + l + 1 by omega, hpre.nodes _ (by omega),
      show L / 2 ^ (16 * layer + l + 1) = L / 2 ^ (16 * layer) / 2 ^ (l + 1) by
        rw [Nat.div_div_eq_div_mul, ← pow_add]; ring_nf,
      node_addr hL hl hl16]

theorem mAddr_congr {σ σ' : Val} {hi : Nat} (h : ∀ k < hi, σ' (.n k) = σ (.n k)) {layer : Nat} (hle : 128 < hi) :
    mAddr σ' (fun l => .n (128 - 3 * (16 * layer + l))) (fun l => tw 3 + (l + 1) * hiMul + layer * lxTop)
      (fun l => 16 * layer + l + 1 == 32) =
    mAddr σ (fun l => .n (128 - 3 * (16 * layer + l))) (fun l => tw 3 + (l + 1) * hiMul + layer * lxTop)
      (fun l => 16 * layer + l + 1 == 32) := by
  funext l
  simp only [mAddr]
  rw [h _ (by omega)]

theorem canonical_mAddr {σ : Val} {L layer : Nat} (hpre : XPre σ L) {l : Nat} (hl : layer < 2) (hl16 : l < 16) :
    IsCanonical128 (mAddr σ (fun l => .n (128 - 3 * (16 * layer + l))) (fun l => tw 3 + (l + 1) * hiMul + layer * lxTop)
      (fun l => 16 * layer + l + 1 == 32) l) := by
  simp only [mAddr]
  split
  · exact isCanonical128_word _ _
  · rename_i he
    refine isCanonical128_add (isCanonical128_word _ _) ?_
    by_cases hlt : 16 * layer + (l + 1) < 32
    · rw [hpre.nodes _ hlt]; exact isCanonical128_eOfNat _
    · have : 16 * layer + l + 1 ≠ 32 := by simpa using he
      omega

/-- The chains as the completeness proof walks them: the step addresses read at the three steps. -/
def xW' (a : Nat) (idx : V) : Wots := { xW a idx with adr := fun s => .n (a + 2 * min s 2 + 1) }

theorem xW_congr (a : Nat) (idx : V) : ∀ s < 3, (xW a idx).adr s = (fun s => V.n (a + 2 * min s 2 + 1)) s :=
  fun s hs => by simp only [xW, Nat.min_eq_left (show s ≤ 2 by omega)]

/-- **The tail of a layer is complete**: over a digest that decodes, from any chain values and
siblings, the root is the fold of the path over the leaf of the recovered chains. -/
theorem xTail_complete (hq : XQ inst) {σ : Val} {L layer a : Nat} {idx d0 : V} (hl : layer < 2)
    (hrd : MemOK rd 64) (hpre : XPre σ L) {key : KeyIndex} (hkey : key.val = L / 2 ^ (16 * layer))
    (hidx : σ idx = eOfNat (xIdx layer L)) (ha : 139 ≤ a) (hidxB : NB a idx) (hd0B : NB a d0)
    (hpp : IsCanonical128 (σ (.n 1))) {enc : Encoding} (hdec : Codeword.decode (xv (σ d0)) = some enc)
    (hd0c : IsCanonical128 (σ d0)) {vals sibs : Nat → E} (hvals : ∀ i, IsCanonical128 (vals i))
    (hsibs : ∀ l, IsCanonical128 (sibs l)) :
    Completes C rd a (xTail layer a idx d0).2.1 (xTail layer a idx d0).1 σ (fun σ' =>
      @treeFold Id _ inst (xpp (σ (.n 1))) ⟨layer, hl⟩ key (fun l => xv (sibs l.val)) layerHeight
        (@leafHash Id _ inst (xpp (σ (.n 1))) ⟨layer, hl⟩ key fun i =>
          @recoverChain Id _ inst (xpp (σ (.n 1))) ⟨layer, hl⟩ key i (enc i) (xv (vals i.val))) =
        xv (σ' (xTail layer a idx d0).2.2) ∧ IsCanonical128 (σ' (xTail layer a idx d0).2.2) ∧
        AgreeBelow a σ σ') := by
  set lay : Layer := ⟨layer, hl⟩
  obtain ⟨henc, hsum, hval⟩ := decode_some hdec
  set dig : Nat → Nat := fun i => (xv (σ d0)).toNat / 4 ^ i % 4 with hdig_def
  have hdig : ∀ i, dig i < 4 := fun i => Nat.mod_lt _ (by norm_num)
  have hL := hpre.lt
  have hcw : cCodeword (xW a idx) (fun s => .n (129 + s)) 19 xTarget d0 (a + 6) =
      cCodeword (xW' a idx) (fun s => .n (129 + s)) 19 xTarget d0 (a + 6) := cCodeword_congr (xW_congr a idx)
  simp only [xTail]
  rw [hcw]
  simp only [List.append_assoc]
  set cw := cCodeword (xW' a idx) (fun s => .n (129 + s)) 19 xTarget d0 (a + 6) with hcw_def
  set c := cw.2.1
  set tip : Nat → V := fun i => (cw.2.2.getD i (.n 0, .n 0)).1
  set leaf := hashValues (.n 1) (.n (c + 1)) tip 58 (c + 2)
  have hc6 : a + 6 < c := cCodeword_snd_gt _ _ _ _ _ _
  have htipB : ∀ i < 58, NB c (tip i) := cCodeword_tips_lt _ _ 19 _ _ _
  have hleafB : NB (c + 2 + hashValuesSize 58) leaf.2 := hashValues_snd_lt _ _ _ _ _
  have hmkge := merkle_snd_ge (.n 1) (fun l => .n (3 + 16 * layer + l)) (fun l => .n (128 - 3 * (16 * layer + l)))
    (fun l => tw 3 + (l + 1) * hiMul + layer * lxTop) (fun l => 16 * layer + l + 1 == 32) 16 0 leaf.2
    (c + 2 + hashValuesSize 58)
  have hw'B : (xW' a idx).Below (a + 6) :=
    ⟨⟨1, by omega, rfl⟩, ⟨2, by omega, rfl⟩, fun s => ⟨_, by have := Nat.min_le_right s 2; omega, rfl⟩,
      hidxB.mono (by omega)⟩
  have hpwB : ∀ s < 10, NB (a + 6) (V.n (129 + s)) := fun s hs => ⟨_, by omega, rfl⟩
  refine Completes.append (m := a + 6) (by omega) (by omega) (xStepAddrs_below hidxB)
    (xStepAddrs_complete hidxB) fun σ1 he1 ⟨hS1, hag1⟩ => ?_
  have h1 : ∀ k < a, σ1 (.n k) = σ (.n k) := fun k hk => (hag1 k hk).symm
  have hidx1 : σ1 idx = σ idx := he1.below hidxB
  have hcan1 : (xW' a idx).Canon σ1 := ⟨by rw [Wots.pp', xW', xW]; rw [h1 1 (by omega)]; exact hpp,
    fun _ s => by
      simp only [Wots.adr', xW']
      rw [(hS1 (min s 2) (by omega)).2, hidx]
      exact isCanonical128_add (isCanonical128_eOfNat _) (isCanonical128_word _ _),
    fun h => absurd h (by simp [xW', xW])⟩
  have hcomp := cCodeword_complete (C := C) (w := xW' a idx) (power := fun s => .n (129 + s)) hrd (G := 19)
    (by norm_num) (target := xTarget) (d0 := d0) (b := a + 6) (σ := σ1) (by omega) hw'B hpwB (hd0B.mono (by omega))
    (by show σ1 (.n 2) = mdw 64 true; rw [h1 2 (by omega)]; exact hpre.md) hcan1
    (fun s hs => by show σ1 (.n (129 + s)) = _; rw [h1 _ (by omega)]; exact hpre.pow s hs)
    (dig := dig) hdig (xs := vals) hvals
    (by rw [xTarget_eq]; exact congrArg (gen ^ ·) hsum.symm)
    (by rw [he1.below hd0B, ← cellOf_cellVal hd0c, show cellVal (σ d0) = xv (σ d0) from rfl, ← lit_toNat]
        exact congrArg lit hval)
  refine Completes.append (m := c) (by omega) (by omega) (cCodeword_below (by norm_num) (by omega) hw'B hpwB
    (hd0B.mono (by omega))) hcomp.withExt fun σ2 he2 ⟨hT2, he2'⟩ => ?_
  have h2 : ∀ k < a + 6, σ2 (.n k) = σ1 (.n k) := fun k hk => (he2'.agree k hk).symm
  have hidx2 : σ2 idx = σ idx := by rw [he2'.below (hidxB.mono (by omega)), hidx1]
  have hp2 : σ2 (.n 1) = σ (.n 1) := by rw [h2 1 (by omega), h1 1 (by omega)]
  -- the leaf address
  set A0 := word (tw 2) 0 0
  have ne : ∀ i j : Nat, i ≠ j → (V.n i) ≠ V.n j := fun i j h e => h (by cases e; rfl)
  obtain ⟨kI, hkI, hkIe⟩ := hidxB
  rw [hkIe] at hidx1 hidx2 hidx hS1 ⊢
  refine Completes.append (m := c + 2) (by omega) (by omega)
    (show NumBelow (c + 2) (Stmt.valsList [cst c A0, addS (.n (c + 1)) (.n kI) (.n c)]) from
      .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
        (.nil _)))))
    (P := fun σ' => σ' (.n (c + 1)) = σ2 (.n kI) + A0 ∧ AgreeBelow c σ2 σ')
    (Completes.atom_cons A0 (by omega) (.cons ⟨_, by omega, rfl⟩ (.nil _)) (Function.update_self _ _ _)
      (Completes.atom_cons (σ2 (.n kI) + A0) (by omega)
        (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))))
        (by
          show Function.update (Function.update σ2 (.n c) A0) (.n (c + 1)) (σ2 (.n kI) + A0) (.n (c + 1)) =
            Function.update (Function.update σ2 (.n c) A0) (.n (c + 1)) (σ2 (.n kI) + A0) (.n kI) +
            Function.update (Function.update σ2 (.n c) A0) (.n (c + 1)) (σ2 (.n kI) + A0) (.n c)
          have h1 : kI ≠ c := by omega
          have h2 : kI ≠ c + 1 := by omega
          simp [h1, h2])
        (Completes.nil _ _ _ ⟨Function.update_self _ _ _, fun k hk => by
          rw [Function.update_of_ne (ne _ _ (by omega)), Function.update_of_ne (ne _ _ (by omega))]⟩)))
    fun σ3 he3 ⟨hA3, hag3⟩ => ?_
  have h3 : ∀ k < c, σ3 (.n k) = σ2 (.n k) := fun k hk => (hag3 k hk).symm
  have hp3 : σ3 (.n 1) = σ (.n 1) := by rw [h3 1 (by omega), hp2]
  have hI : IsCanonical128 (σ2 (.n kI)) := by rw [hidx2, hidx]; exact isCanonical128_eOfNat _
  have htip3 : ∀ i < 58, σ3 (tip i) = (tipPair true (σ (.n 1)) (fun s => σ2 (.n (a + 2 * min s 2 + 1)))
      (σ2 idx) i (dig i) (vals i)).1 := fun i hi => by
    obtain ⟨k, hk, e⟩ := htipB i hi
    have := (hT2 i hi).1
    simp only [tip] at e ⊢
    rw [e, h3 k hk, ← e]
    refine this.trans ?_
    show (tipPair true (σ2 (.n 1)) (fun s => σ2 (.n (a + 2 * min s 2 + 1))) (σ2 idx) i (dig i) (vals i)).1 = _
    rw [hp2]
  have hcanT : ∀ i < 58, IsCanonical128 (σ3 (tip i)) := fun i hi => by
    rw [htip3 i hi]; exact canonical_tipPair _ _ _ _ _ _ (hvals i)
  have hv := hashValues_complete (C := C) (rd := rd) (σ := σ3) (pp := .n 1) (a := .n (c + 1)) (val := tip)
    (n := 58) (b := c + 2) (Or.inr (by norm_num)) (by norm_num)
    ⟨⟨1, by omega, rfl⟩, ⟨c + 1, by omega, rfl⟩, fun i hi => (htipB i hi).mono (by omega)⟩
    ⟨by rw [hp3]; exact hpp, by rw [hA3]; exact isCanonical128_add hI (isCanonical128_word _ _), hcanT⟩
  refine Completes.append (m := c + 2 + hashValuesSize 58) (by omega) (by omega)
    (hashValues_below (by norm_num) ⟨⟨1, by omega, rfl⟩, ⟨c + 1, by omega, rfl⟩,
      fun i hi => (htipB i hi).mono (by omega)⟩) hv.withExt fun σ4 he4 ⟨hleaf4, he4'⟩ => ?_
  have hσ4 : ∀ k < a, σ4 (.n k) = σ (.n k) := fun k hk => by
    rw [← he4'.agree k (by omega), h3 k (by omega), h2 k (by omega), h1 k hk]
  have hpre4 : XPre σ4 L := hpre.congr fun k hk => (hσ4 k (by omega)).symm
  have hleafc : IsCanonical128 (σ4 leaf.2) := by rw [hleaf4]; exact (isCanonical128_hb _).1
  have hmk := merkle_complete (C := C) (rd := rd) (pp := .n 1) (bit := fun l => .n (3 + 16 * layer + l))
    (node := fun l => .n (128 - 3 * (16 * layer + l))) (addr := fun l => tw 3 + (l + 1) * hiMul + layer * lxTop)
    (isEnd := fun l => 16 * layer + l + 1 == 32) (β := fun l => key.val.testBit l) (sibs := sibs) 16 0 leaf.2
    (c + 2 + hashValuesSize 58) σ4 ⟨1, by omega, rfl⟩ hleafB
    (fun l' _ hl' => ⟨⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩)
    (fun l' _ hl' => ⟨by
        show σ4 (.n (3 + 16 * layer + l')) = _
        rw [show 3 + 16 * layer + l' = 3 + (16 * layer + l') by omega, hpre4.bits _ (by omega), hkey,
          Nat.testBit_div_two_pow, Nat.add_comm l'],
      hsibs l', canonical_mAddr hpre4 hl (by omega)⟩)
    (by rw [hσ4 1 (by omega)]; exact hpp) hleafc
  refine hmk.withExt.mono le_rfl le_rfl fun σ5 ⟨hroot5, he5⟩ => ⟨?_, ?_, fun k hk => ?_⟩
  · have hadr2 : ∀ s : ChainStep, cellBytes (σ2 (.n (a + 2 * min s.val 2 + 1))) = tweakBytes (.chain lay key s) :=
      fun s => by
        have hs : s.val < 3 := s.isLt
        rw [Nat.min_eq_left (by omega), h2 _ (by omega), (hS1 s.val hs).2, hidx, chain_addr hL hl hs,
          tweakBytes_chain, hkey]
    have hchains : (fun i : ChainIndex => @recoverChain Id _ inst (xpp (σ (.n 1))) lay key i (enc i)
        (xv (vals i.val))) = fun i => xv (σ3 (tip i.val)) := by
      funext i
      rw [show enc i = ⟨dig i.val, hdig _⟩ from Fin.ext (henc i),
        recoverChain_cells (adr := fun s => σ2 (.n (a + 2 * min s 2 + 1))) hq hadr2, htip3 i.val i.isLt,
        tipPair_lx _ _ (σ2 idx)]
    have hleafAdr : cellBytes (σ3 (.n (c + 1))) = tweakBytes (.leaf lay key) := by
      rw [hA3, hidx2, hidx, tag_addr hL hl (by norm_num), tweakBytes_leaf, hkey]
    rw [hchains, leafHash_cells hq (fun i => σ3 (tip i)) hleafAdr, show numChains = 58 from rfl]
    rw [hroot5, mAddr_congr hσ4 (by omega), hσ4 1 (by omega), hleaf4, hp3,
      treeFold_cells hq (node_cells hl hpre hkey) sibs layerHeight le_rfl]
    rfl
  · rw [hroot5]; exact mFold_canonical _ _ _ _ _ _ _ (Or.inl (by norm_num))
  · rw [← he5.agree k (by omega), ← hσ4 k hk]


/-! ## The digests -/

theorem xDigest0_complete {σ : Val} {b : Nat} (hb9 : 129 ≤ b) {m0 m1 rho : E}
    (hl2 : LoadHolds rd (σ (.n 0)) 2 m0) (hl3 : LoadHolds rd (σ (.n 0)) 3 m1)
    (hpp : IsCanonical128 (σ (.n 1))) (hm0 : IsCanonical128 m0) (hm1 : IsCanonical128 m1)
    (hrho : IsCanonical128 rho) (hA : IsCanonical128 (σ (.n 128))) :
    Completes C rd b (b + 16) (xDigest0 b) σ (fun σ' =>
      σ' (.n (b + 2)) = σ (.n 128) + word (tw 12) 0 0 ∧
      σ' (.n (b + 14)) = (hcell [σ (.n 1), σ (.n 128) + word (tw 12) 0 0, m0, m1, rho]).1 ∧
      AgreeBelow b σ σ') := by
  set A := σ (.n 128) + word (tw 12) 0 0
  set x := hmid ![σ (.n 1), A, m0, m1]
  set o := hb (blockBytes ![σ (.n 1), A, m0, m1] ++ [rho].flatMap cellBytes)
  set σ' := upds σ [(b, rho), (b + 1, word (tw 12) 0 0), (b + 2, A), (b + 3, m0), (b + 4, m1), (b + 5, iv0),
    (b + 6, iv1), (b + 7, mdw 64 false), (b + 8, x.1), (b + 9, x.2), (b + 10, word 0 0 0), (b + 11, word 0 0 0),
    (b + 12, word 0 0 0), (b + 13, mdw 80 true), (b + 14, o.1), (b + 15, o.2)]
  have he : Ext b (b + 16) σ σ' := upds_ext σ _ (by simp)
  have hk : ∀ k < b, σ' (.n k) = σ (.n k) := fun k hk => (he.agree k hk).symm
  have v : ∀ j < 16, σ' (.n (b + j)) = [rho, word (tw 12) 0 0, A, m0, m1, iv0, iv1, mdw 64 false, x.1, x.2,
      word 0 0 0, word 0 0 0, word 0 0 0, mdw 80 true, o.1, o.2].getD j 0 := fun j hj => by
    interval_cases j <;> simp [σ', upds]
  have hr : ([rho].flatMap cellBytes).length = 16 := by rw [length_flatMap_cellBytes']; rfl
  have hcmp := (compress_two_iff (b0 := ![σ (.n 1), A, m0, m1]) (x0 := x.1) (x1 := x.2) (o0 := o.1) (o1 := o.2)
    (blockBytes_one rho) (by rw [hr]; omega) (by rw [hr]; omega)).mpr
    ⟨fin4_canonical.mpr ⟨hpp, isCanonical128_add hA (isCanonical128_word _ _), hm0, hm1⟩,
      fin4_canonical.mpr ⟨hrho, isCanonical128_zero, isCanonical128_zero, isCanonical128_zero⟩, rfl, rfl⟩
  rw [hr] at hcmp
  refine ⟨σ', he, ⟨?_, ?_, he.agree⟩, fun next kret hn => ?_⟩
  · rw [v 2 (by omega)]; rfl
  · rw [v 14 (by omega)]
    show o.1 = _
    simp only [o, blockBytes_four, hcell, ← List.flatMap_append]
    rfl
  · simp only [xDigest0, ivs, cst, b2s, addS, hintW, List.cons_append, List.nil_append, holdsList_cons_atom,
      holdsList_nil, Atom.Holds, true_and]
    have v0 := v 0 (by omega)
    rw [Nat.add_zero] at v0
    rw [v0, v 1 (by omega), v 2 (by omega), v 3 (by omega), v 4 (by omega), v 5 (by omega),
      show b + 5 + 1 = b + 6 by omega, v 6 (by omega), v 7 (by omega), v 8 (by omega), v 9 (by omega),
      v 10 (by omega), v 11 (by omega), v 12 (by omega), v 13 (by omega), v 14 (by omega), v 15 (by omega),
      hk 1 (by omega), hk 128 (by omega), hk 0 (by omega)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, word_zero]
    obtain ⟨hc1, hc2⟩ := hcmp
    refine ⟨?_, ?_, hl2, hl3, ?_, ?_, ?_, hc1, ?_, ?_, ?_, ?_, hc2, hn⟩ <;> trivial

theorem xDigest1_complete {σ : Val} {b : Nat} {root : V} (hb9 : 129 ≤ b) (hroot : NB b root) {rho : E}
    (hpp : IsCanonical128 (σ (.n 1))) (hrc : IsCanonical128 (σ root)) (hrho : IsCanonical128 rho)
    (hA : IsCanonical128 (σ (.n 80))) :
    Completes C rd b (b + 10) (xDigest1 b root) σ (fun σ' =>
      σ' (.n (b + 1)) = σ (.n 80) + word lxTop 0 0 ∧
      σ' (.n (b + 4)) = σ (.n 80) + word lxTop 0 0 + word (tw 12) 0 0 ∧
      σ' (.n (b + 8)) = (hcell [σ (.n 1), σ (.n 80) + word lxTop 0 0 + word (tw 12) 0 0, σ root, rho]).1 ∧
      AgreeBelow b σ σ') := by
  set I := σ (.n 80) + word lxTop 0 0
  set A := I + word (tw 12) 0 0
  set o := hcell [σ (.n 1), A, σ root, rho]
  set σ' := upds σ [(b, word lxTop 0 0), (b + 1, I), (b + 2, rho), (b + 3, word (tw 12) 0 0), (b + 4, A),
    (b + 5, iv0), (b + 6, iv1), (b + 7, mdw 64 true), (b + 8, o.1), (b + 9, o.2)]
  have he : Ext b (b + 10) σ σ' := upds_ext σ _ (by simp)
  have hk : ∀ k < b, σ' (.n k) = σ (.n k) := fun k hk => (he.agree k hk).symm
  have v : ∀ j < 10, σ' (.n (b + j)) = [word lxTop 0 0, I, rho, word (tw 12) 0 0, A, iv0, iv1, mdw 64 true,
      o.1, o.2].getD j 0 := fun j hj => by
    interval_cases j <;> simp [σ', upds]
  have hcmp := compress4_iff (o0 := o.1) (o1 := o.2) |>.mpr
    ⟨⟨hpp, isCanonical128_add (isCanonical128_add hA (isCanonical128_word _ _)) (isCanonical128_word _ _), hrc,
      hrho⟩, rfl⟩
  obtain ⟨kr, hkr, rfl⟩ := hroot
  refine ⟨σ', he, ⟨?_, ?_, ?_, he.agree⟩, fun next kret hn => ?_⟩
  · rw [v 1 (by omega)]; rfl
  · rw [v 4 (by omega)]; rfl
  · rw [v 8 (by omega)]; rfl
  · simp only [xDigest1, ivs, cst, b2s, addS, hintW, List.cons_append, List.nil_append, holdsList_cons_atom,
      holdsList_nil, Atom.Holds, true_and]
    have v0 := v 0 (by omega)
    rw [Nat.add_zero] at v0
    rw [v0, v 1 (by omega), v 2 (by omega), v 3 (by omega), v 4 (by omega), v 5 (by omega),
      show b + 5 + 1 = b + 6 by omega, v 6 (by omega), v 7 (by omega), v 8 (by omega), v 9 (by omega),
      hk 1 (by omega), hk 80 (by omega), hk kr hkr]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hcmp, hn⟩ <;> trivial

/-! ## Bounds of a layer -/

theorem xTail_below {layer a : Nat} {idx d0 : V} (hl : layer < 2) (ha : 139 ≤ a) (hidxB : NB a idx)
    (hd0B : NB a d0) : NumBelow (xTail layer a idx d0).2.1 (Stmt.valsList (xTail layer a idx d0).1) := by
  obtain ⟨kI, hkI, rfl⟩ := hidxB
  have hcw : cCodeword (xW a (.n kI)) (fun s => .n (129 + s)) 19 xTarget d0 (a + 6) =
      cCodeword (xW' a (.n kI)) (fun s => .n (129 + s)) 19 xTarget d0 (a + 6) := cCodeword_congr (xW_congr a (.n kI))
  simp only [xTail]
  rw [hcw]
  set cw := cCodeword (xW' a (.n kI)) (fun s => .n (129 + s)) 19 xTarget d0 (a + 6)
  set c := cw.2.1
  set tip : Nat → V := fun i => (cw.2.2.getD i (.n 0, .n 0)).1
  set leaf := hashValues (.n 1) (.n (c + 1)) tip 58 (c + 2)
  have hc6 : a + 6 < c := cCodeword_snd_gt _ _ _ _ _ _
  have htipB : ∀ i < 58, NB c (tip i) := cCodeword_tips_lt _ _ 19 _ _ _
  have hleafB : NB (c + 2 + hashValuesSize 58) leaf.2 := hashValues_snd_lt _ _ _ _ _
  have hmkge := merkle_snd_ge (.n 1) (fun l => .n (3 + 16 * layer + l)) (fun l => .n (128 - 3 * (16 * layer + l)))
    (fun l => tw 3 + (l + 1) * hiMul + layer * lxTop) (fun l => 16 * layer + l + 1 == 32) 16 0 leaf.2
    (c + 2 + hashValuesSize 58)
  have hw'B : (xW' a (.n kI)).Below (a + 6) :=
    ⟨⟨1, by omega, rfl⟩, ⟨2, by omega, rfl⟩, fun s => ⟨_, by have := Nat.min_le_right s 2; omega, rfl⟩,
      ⟨kI, by omega, rfl⟩⟩
  have hpwB : ∀ s < 10, NB (a + 6) (V.n (129 + s)) := fun s hs => ⟨_, by omega, rfl⟩
  have hcc : (cCodeword (xW' a (.n kI)) (fun s => .n (129 + s)) 19 xTarget d0 (a + 6)).2.1 = c := rfl
  simp only [valsList_append]
  refine (((((xStepAddrs_below ⟨kI, hkI, rfl⟩).mono (by omega)).append
    ((cCodeword_below (by norm_num) (by omega) hw'B hpwB (hd0B.mono (by omega))).mono (by omega))).append ?_).append
    ((hashValues_below (by norm_num) ⟨⟨1, by omega, rfl⟩, ⟨c + 1, by omega, rfl⟩,
      fun i hi => (htipB i hi).mono (by omega)⟩).mono hmkge)).append
    (merkle_below 16 0 leaf.2 _ ⟨1, by omega, rfl⟩ hleafB fun l' _ hl' => ⟨⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩)
  simp only [cst, addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.cons_append, List.nil_append,
    List.append_nil]
  exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
    (.nil _))))

theorem xDigest0_below (b : Nat) (hb : 129 ≤ b) : NumBelow (b + 16) (Stmt.valsList (xDigest0 b)) := by
  simp only [xDigest0, ivs, cst, b2s, addS, hintW, List.cons_append, List.nil_append, valsList_cons, valsList_nil,
    Stmt.vals, Atom.vals, Hint.vals, Dest.vals, List.append_nil]
  repeat (first | exact .nil _ | refine .cons ⟨_, by omega, rfl⟩ ?_)

theorem xDigest1_below (b : Nat) (hb : 129 ≤ b) {root : V} (hroot : NB b root) :
    NumBelow (b + 10) (Stmt.valsList (xDigest1 b root)) := by
  obtain ⟨kr, hkr, rfl⟩ := hroot
  simp only [xDigest1, ivs, cst, b2s, addS, hintW, List.cons_append, List.nil_append, valsList_cons, valsList_nil,
    Stmt.vals, Atom.vals, Hint.vals, Dest.vals, List.append_nil]
  repeat (first | exact .nil _ | refine .cons ⟨_, by omega, rfl⟩ ?_)

theorem xLayer_snd_gt (layer b : Nat) (root : V) (hl : layer < 2) : b + 16 < (xLayer layer b root).2.1 := by
  interval_cases layer
  · rw [xLayer_zero]
    simp only [xTail]
    have := merkle_snd_ge (.n 1) (fun l => .n (3 + 16 * 0 + l)) (fun l => .n (128 - 3 * (16 * 0 + l)))
      (fun l => tw 3 + (l + 1) * hiMul + 0 * lxTop) (fun l => 16 * 0 + l + 1 == 32) 16 0
      (hashValues (.n 1) (.n ((cCodeword (xW (b + 16) (.n 128)) (fun s => .n (129 + s)) 19 xTarget (.n (b + 14))
        (b + 16 + 6)).2.1 + 1)) (fun i => ((cCodeword (xW (b + 16) (.n 128)) (fun s => .n (129 + s)) 19 xTarget
        (.n (b + 14)) (b + 16 + 6)).2.2.getD i (.n 0, .n 0)).1) 58
        ((cCodeword (xW (b + 16) (.n 128)) (fun s => .n (129 + s)) 19 xTarget (.n (b + 14)) (b + 16 + 6)).2.1 + 2)).2
      ((cCodeword (xW (b + 16) (.n 128)) (fun s => .n (129 + s)) 19 xTarget (.n (b + 14)) (b + 16 + 6)).2.1 + 2 +
        hashValuesSize 58)
    have := cCodeword_snd_gt (xW (b + 16) (.n 128)) (fun s => .n (129 + s)) 19 xTarget (.n (b + 14)) (b + 16 + 6)
    omega
  · rw [xLayer_one]
    simp only [xTail]
    have := merkle_snd_ge (.n 1) (fun l => .n (3 + 16 * 1 + l)) (fun l => .n (128 - 3 * (16 * 1 + l)))
      (fun l => tw 3 + (l + 1) * hiMul + 1 * lxTop) (fun l => 16 * 1 + l + 1 == 32) 16 0
      (hashValues (.n 1) (.n ((cCodeword (xW (b + 10) (.n (b + 1))) (fun s => .n (129 + s)) 19 xTarget (.n (b + 8))
        (b + 10 + 6)).2.1 + 1)) (fun i => ((cCodeword (xW (b + 10) (.n (b + 1))) (fun s => .n (129 + s)) 19 xTarget
        (.n (b + 8)) (b + 10 + 6)).2.2.getD i (.n 0, .n 0)).1) 58
        ((cCodeword (xW (b + 10) (.n (b + 1))) (fun s => .n (129 + s)) 19 xTarget (.n (b + 8)) (b + 10 + 6)).2.1 + 2)).2
      ((cCodeword (xW (b + 10) (.n (b + 1))) (fun s => .n (129 + s)) 19 xTarget (.n (b + 8)) (b + 10 + 6)).2.1 + 2 +
        hashValuesSize 58)
    have := cCodeword_snd_gt (xW (b + 10) (.n (b + 1))) (fun s => .n (129 + s)) 19 xTarget (.n (b + 8)) (b + 10 + 6)
    omega

/-! ## A layer -/

/-- The cells of a layer signature's values. -/
def valsOf (part : LayerSignature) : Nat → E := fun i => if h : i < numChains then cellOf (part.chainValues ⟨i, h⟩) else 0
def sibsOf (part : LayerSignature) : Nat → E := fun l => if h : l < layerHeight then cellOf (part.path ⟨l, h⟩) else 0

theorem xv_valsOf (part : LayerSignature) (i : ChainIndex) : xv (valsOf part i.val) = part.chainValues i := by
  simp only [valsOf, i.isLt, ↓reduceDIte]; exact cellVal_cellOf _

theorem xv_sibsOf (part : LayerSignature) (l : Fin layerHeight) : xv (sibsOf part l.val) = part.path l := by
  simp only [sibsOf, l.isLt, ↓reduceDIte]; exact cellVal_cellOf _

theorem canonical_valsOf (part : LayerSignature) (i : Nat) : IsCanonical128 (valsOf part i) := by
  unfold valsOf; split
  · exact isCanonical128_cellOf _
  · exact isCanonical128_zero

theorem canonical_sibsOf (part : LayerSignature) (l : Nat) : IsCanonical128 (sibsOf part l) := by
  unfold sibsOf; split
  · exact isCanonical128_cellOf _
  · exact isCanonical128_zero

/-- A layer root, unfolded. -/
theorem layerRoot_some {P : PublicParameter} {lay : Layer} {key : KeyIndex} {M : HashInput} {part : LayerSignature}
    {r : LeanXmss.Digest} (h : @layerRoot Id _ inst P lay key M part = some r) :
    ∃ enc, Codeword.decode (@messageDigest Id _ inst P lay key M part.randomness) = some enc ∧
      @treeFold Id _ inst P lay key part.path layerHeight
        (@leafHash Id _ inst P lay key fun i => @recoverChain Id _ inst P lay key i (enc i) (part.chainValues i)) = r := by
  rw [layerRoot_id, otsLeaf_id] at h
  cases hD : Codeword.decode (@messageDigest Id _ inst P lay key M part.randomness) with
  | none => rw [hD] at h; simp only [Option.map_none, reduceCtorEq] at h
  | some enc =>
      rw [hD] at h
      simp only [Option.map_some] at h
      exact ⟨enc, rfl, Option.some.inj h⟩

/-- **The bottom layer is complete.** -/
theorem xLayer0_complete (hq : XQ inst) (hrd : MemOK rd 64) {σ : Val} {L b : Nat} {root : V} (hpre : XPre σ L)
    {key : KeyIndex} (hkey : key.val = L) (hb : 139 ≤ b) {m0 m1 : E} (hl2 : LoadHolds rd (σ (.n 0)) 2 m0)
    (hl3 : LoadHolds rd (σ (.n 0)) 3 m1) (hpp : IsCanonical128 (σ (.n 1))) (hm0 : IsCanonical128 m0)
    (hm1 : IsCanonical128 m1) {part : LayerSignature} {r : LeanXmss.Digest}
    (hr : @layerRoot Id _ inst (xpp (σ (.n 1))) bottomLayer key (cellBytes m0 ++ cellBytes m1) part = some r) :
    Completes C rd b (xLayer 0 b root).2.1 (xLayer 0 b root).1 σ (fun σ' =>
      σ' (xLayer 0 b root).2.2 = cellOf r ∧ AgreeBelow b σ σ') := by
  obtain ⟨enc, hdec, htree⟩ := layerRoot_some hr
  have hkey' : key.val = L / 2 ^ (16 * 0) := by rw [hkey]; simp
  have hidx : σ (.n 128) = eOfNat (xIdx 0 L) := by
    have := hpre.nodes 0 (by omega)
    simpa [xIdx] using this
  have hgt := xLayer_snd_gt 0 b root (by omega)
  rw [xLayer_zero] at hgt ⊢
  dsimp only at hgt ⊢
  refine Completes.append (m := b + 16) (by omega) (by omega) (xDigest0_below b (by omega))
    (xDigest0_complete (rho := cellOf part.randomness) (by omega) hl2 hl3 hpp hm0 hm1 (isCanonical128_cellOf _)
      (by rw [hidx]; exact isCanonical128_eOfNat _))
    fun σ1 he1 ⟨hA1, hd1, hag1⟩ => ?_
  have h1 : ∀ k < b, σ1 (.n k) = σ (.n k) := fun k hk => (hag1 k hk).symm
  have hpre1 : XPre σ1 L := hpre.congr fun k hk => (h1 k (by omega)).symm
  have hmd : @messageDigest Id _ inst (xpp (σ (.n 1))) bottomLayer key (cellBytes m0 ++ cellBytes m1)
      part.randomness = xv (σ1 (.n (b + 14))) := by
    rw [← show xv (cellOf part.randomness) = part.randomness from cellVal_cellOf _,
      messageDigest_cells hq (a := σ (.n 128) + word (tw 12) 0 0) (cs := [m0, m1]) ?_ (by simp), hd1]
    · simp only [List.cons_append, List.nil_append]
    · rw [hidx, tag_addr hpre.lt (by omega) (by omega), tweakBytes_message, hkey',
        show (bottomLayer : Layer).val = 0 from rfl]
  have hdec1 : Codeword.decode (xv (σ1 (.n (b + 14)))) = some enc := by rw [← hmd]; exact hdec
  have hd1c : IsCanonical128 (σ1 (.n (b + 14))) := by rw [hd1]; exact (isCanonical128_hb _).1
  refine (xTail_complete (inst := inst) hq (layer := 0) (a := b + 16) (by omega) hrd hpre1 hkey'
    (by rw [h1 128 (by omega)]; exact hidx) (by omega) ⟨128, by omega, rfl⟩ ⟨b + 14, by omega, rfl⟩
    (by rw [h1 1 (by omega)]; exact hpp) hdec1 hd1c (canonical_valsOf part) (canonical_sibsOf part)).mono le_rfl le_rfl
    fun σ2 ⟨heq, hcan, hag2⟩ => ⟨?_, fun k hk => (hag1 k hk).trans (hag2 k (by omega))⟩
  rw [h1 1 (by omega)] at heq
  simp only [xv_valsOf, xv_sibsOf] at heq
  rw [← cellOf_cellVal hcan, show cellVal _ = xv _ from rfl, ← heq]
  exact congrArg cellOf htree

theorem idx_top {σ : Val} {L : Nat} (hpre : XPre σ L) : σ (.n 80) + word lxTop 0 0 = eOfNat (xIdx 1 L) := by
  have := hpre.nodes 16 (by omega)
  rw [show 128 - 3 * 16 = 80 by omega] at this
  rw [this, xIdx, show lxTop = 2 ^ 55 * 1 by rfl, eOfNat_add_word (lt_of_le_of_lt (Nat.div_le_self _ _)
    (lt_trans hpre.lt (by norm_num)))]
  congr 1
  ring

/-- **The top layer is complete.** -/
theorem xLayer1_complete (hq : XQ inst) (hrd : MemOK rd 64) {σ : Val} {L b : Nat} {root : V} (hpre : XPre σ L)
    {key : KeyIndex} (hkey : key.val = L / 2 ^ 16) (hb : 139 ≤ b) (hroot : NB b root)
    (hpp : IsCanonical128 (σ (.n 1))) (hrc : IsCanonical128 (σ root)) {part : LayerSignature} {r : LeanXmss.Digest}
    (hr : @layerRoot Id _ inst (xpp (σ (.n 1))) topLayer key (cellBytes (σ root)) part = some r) :
    Completes C rd b (xLayer 1 b root).2.1 (xLayer 1 b root).1 σ (fun σ' =>
      σ' (xLayer 1 b root).2.2 = cellOf r ∧ AgreeBelow b σ σ') := by
  obtain ⟨enc, hdec, htree⟩ := layerRoot_some hr
  have hkey' : key.val = L / 2 ^ (16 * 1) := by rw [hkey]
  have hI := idx_top hpre
  have hgt := xLayer_snd_gt 1 b root (by omega)
  rw [xLayer_one] at hgt ⊢
  dsimp only at hgt ⊢
  refine Completes.append (m := b + 10) (by omega) (by omega) (xDigest1_below b (by omega) hroot)
    (xDigest1_complete (rho := cellOf part.randomness) (by omega) hroot hpp hrc (isCanonical128_cellOf _)
      (by have := hpre.nodes 16 (by omega); rw [show 128 - 3 * 16 = 80 by omega] at this
          rw [this]; exact isCanonical128_eOfNat _))
    fun σ1 he1 ⟨hI1, hA1, hd1, hag1⟩ => ?_
  have h1 : ∀ k < b, σ1 (.n k) = σ (.n k) := fun k hk => (hag1 k hk).symm
  have hpre1 : XPre σ1 L := hpre.congr fun k hk => (h1 k (by omega)).symm
  have hmd : @messageDigest Id _ inst (xpp (σ (.n 1))) topLayer key (cellBytes (σ root))
      part.randomness = xv (σ1 (.n (b + 8))) := by
    rw [← show xv (cellOf part.randomness) = part.randomness from cellVal_cellOf _,
      messageDigest_cells hq (a := σ (.n 80) + word lxTop 0 0 + word (tw 12) 0 0) (cs := [σ root]) ?_ (by simp), hd1]
    · simp only [List.cons_append, List.nil_append]
    · rw [hI, tag_addr hpre.lt (by omega) (by omega), tweakBytes_message, hkey',
        show (topLayer : Layer).val = 1 from rfl]
  have hdec1 : Codeword.decode (xv (σ1 (.n (b + 8)))) = some enc := by rw [← hmd]; exact hdec
  have hd1c : IsCanonical128 (σ1 (.n (b + 8))) := by rw [hd1]; exact (isCanonical128_hb _).1
  refine (xTail_complete (inst := inst) hq (layer := 1) (a := b + 10) (by omega) hrd hpre1 hkey'
    (by rw [hI1, hI]) (by omega) ⟨b + 1, by omega, rfl⟩ ⟨b + 8, by omega, rfl⟩
    (by rw [h1 1 (by omega)]; exact hpp) hdec1 hd1c (canonical_valsOf part) (canonical_sibsOf part)).mono le_rfl le_rfl
    fun σ2 ⟨heq, hcan, hag2⟩ => ⟨?_, fun k hk => (hag1 k hk).trans (hag2 k (by omega))⟩
  rw [h1 1 (by omega)] at heq
  simp only [xv_valsOf, xv_sibsOf] at heq
  rw [← cellOf_cellVal hcan, show cellVal _ = xv _ from rfl, ← heq]
  exact congrArg cellOf htree

end
end LeanVM.Guest.B1.Sig
