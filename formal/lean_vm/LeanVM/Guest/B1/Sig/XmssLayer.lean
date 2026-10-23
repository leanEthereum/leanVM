/-
  LeanVM.Guest.B1.Sig.XmssLayer

  One layer of `verify_lean_xmss` (G:2400-2440): the message digest, the step addresses, the
  codeword's chains, the leaf and the Merkle path, sound and complete for `layerRoot`.
-/

module

public import LeanVM.Guest.B1.Sig.XmssPrologue
public import LeanVM.Guest.B1.Sig.XmssScheme
public import LeanVM.Guest.B1.Sig.Codeword
public import LeanVM.Guest.Word

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanXmss LeanXmss.Concrete

@[expose] public section

variable {C : CallRel} {rd : Reader} {inst : HasQuery LeanXmss.HashSpec Id}

/-! ## Constants -/

theorem gen_pow_gpowK {e : Nat} (h : e < u128Bound) : gen ^ e = ofK (gpowK e) := by
  rw [gpowK_eq h, gen, eOfNat, ← ofK_pow]
  rfl

theorem xTarget_eq : xTarget = gen ^ 106 := by
  rw [gen_pow_gpowK (by decide), xTarget, word_eq_eOfNat, eOfNat]
  exact congrArg ofK (by decide +kernel)

theorem word_add_eOfNat {k q B : Nat} (hB : B < 2 ^ k) : word (2 ^ k * q) 0 0 + eOfNat B = eOfNat (2 ^ k * q + B) := by
  rw [word_eq_eOfNat, eOfNat_add_of_lt hB]

theorem eOfNat_add_word {k q B : Nat} (hB : B < 2 ^ k) : eOfNat B + word (2 ^ k * q) 0 0 = eOfNat (2 ^ k * q + B) := by
  rw [add_comm, word_add_eOfNat hB]

/-! ## The tail of a layer -/

/-- A layer's index word: its key, the top layer's bit 55. -/
def xIdx (layer L : Nat) : Nat := L / 2 ^ (16 * layer) + 2 ^ 55 * layer

/-- A layer's chains: the parameter, the step metadata, the step addresses from `a`. -/
def xW (a : Nat) (idx : V) : Wots := ⟨.n 1, .n 2, true, fun s => .n (a + 2 * s + 1), idx⟩

/-- A layer after its digest, from the address base `a`, over its index `idx` and digest `d0`:
its statements, the next base and its root. -/
def xTail (layer a : Nat) (idx d0 : V) : List Stmt × Nat × V :=
  let cw := cCodeword (xW a idx) (fun s => .n (129 + s)) 19 xTarget d0 (a + 6)
  let c := cw.2.1
  let leaf := hashValues (.n 1) (.n (c + 1)) (fun i => (cw.2.2.getD i (.n 0, .n 0)).1) 58 (c + 2)
  let mk := merkle (.n 1) (fun l => .n (3 + 16 * layer + l))
    (fun l => .n (128 - 3 * (16 * layer + l)))
    (fun l => tw 3 + (l + 1) * hiMul + layer * lxTop) (fun l => 16 * layer + l + 1 == 32)
    16 0 leaf.2 (c + 2 + hashValuesSize 58)
  (xStepAddrs idx a ++ cw.1 ++ [cst c (word (tw 2) 0 0), addS (.n (c + 1)) idx (.n c)] ++ leaf.1 ++ mk.1,
    mk.2.2, mk.2.1)

theorem xLayer_zero (b : Nat) (root : V) :
    xLayer 0 b root = (xDigest0 b ++ (xTail 0 (b + 16) (.n 128) (.n (b + 14))).1,
      (xTail 0 (b + 16) (.n 128) (.n (b + 14))).2.1, (xTail 0 (b + 16) (.n 128) (.n (b + 14))).2.2) := by
  simp only [xLayer, xTail, xW, ↓reduceIte, List.append_assoc]

theorem xLayer_one (b : Nat) (root : V) :
    xLayer 1 b root = (xDigest1 b root ++ (xTail 1 (b + 10) (.n (b + 1)) (.n (b + 8))).1,
      (xTail 1 (b + 10) (.n (b + 1)) (.n (b + 8))).2.1, (xTail 1 (b + 10) (.n (b + 1)) (.n (b + 8))).2.2) := by
  simp only [xLayer, xTail, xW, one_ne_zero, ↓reduceIte, List.append_assoc]

theorem xStepAddrs_iff {σ : Val} (idx : V) (a : Nat) {next : Prop} {kret : List E → Prop} :
    Stmt.HoldsList C rd σ (xStepAddrs idx a) next kret ↔
      (∀ s < 3, σ (.n (a + 2 * s)) = word (tw 1 + s * stepMul) 0 0 ∧
        σ (.n (a + 2 * s + 1)) = σ idx + word (tw 1 + s * stepMul) 0 0) ∧ next := by
  simp only [xStepAddrs, List.range_succ, List.range_zero, List.nil_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append, cst, addS,
    holdsList_cons_atom, holdsList_nil, Atom.Holds]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, hn⟩
    refine ⟨fun s hs => ?_, hn⟩
    interval_cases s
    · exact ⟨h0, h1.trans (by rw [h0])⟩
    · exact ⟨h2, h3.trans (by rw [h2])⟩
    · exact ⟨h4, h5.trans (by rw [h4])⟩
  · rintro ⟨h, hn⟩
    have e0 := h 0 (by omega); have e1 := h 1 (by omega); have e2 := h 2 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, zero_mul] at e0 e1 e2 ⊢
    refine ⟨e0.1, by rw [e0.2, e0.1], e1.1, by rw [e1.2, e1.1], e2.1, by rw [e2.2, e2.1], hn⟩

/-! ## Addresses as tweaks -/

theorem layerHi_val (lay : Layer) (f : Nat) : layerHi lay f = f + 2 ^ 23 * lay.val := rfl

theorem key_lt {L layer : Nat} (hL : L < 2 ^ 32) : L / 2 ^ (16 * layer) < 2 ^ 32 :=
  lt_of_le_of_lt (Nat.div_le_self _ _) hL

/-- A step address. -/
theorem chain_addr {L layer s : Nat} (hL : L < 2 ^ 32) (hl : layer < 2) (hs : s < 3) :
    eOfNat (xIdx layer L) + word (tw 1 + s * stepMul) 0 0 =
      eOfNat (addrNat 1 s (0 + 2 ^ 23 * layer) (L / 2 ^ (16 * layer))) := by
  have hk := key_lt (layer := layer) hL
  rw [show tw 1 + s * stepMul = 2 ^ 56 * (1 + 32 * s) by simp only [tw, stepMul]; ring,
    eOfNat_add_word (by simp only [xIdx]; interval_cases layer <;> omega)]
  congr 1
  simp only [addrNat, xIdx]
  rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by interval_cases layer <;> omega),
    Nat.mod_eq_of_lt (show 1 < 32 by omega), Nat.mod_eq_of_lt (show s < 8 by omega)]
  ring

/-- The leaf and message addresses. -/
theorem tag_addr {L layer t : Nat} (hL : L < 2 ^ 32) (hl : layer < 2) (ht : t < 32) :
    eOfNat (xIdx layer L) + word (tw t) 0 0 = eOfNat (addrNat t 0 (0 + 2 ^ 23 * layer) (L / 2 ^ (16 * layer))) := by
  have hk := key_lt (layer := layer) hL
  rw [show tw t = 2 ^ 56 * t by simp only [tw]; ring,
    eOfNat_add_word (by simp only [xIdx]; interval_cases layer <;> omega)]
  congr 1
  simp only [addrNat, xIdx]
  rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by interval_cases layer <;> omega), Nat.mod_eq_of_lt ht]
  ring

/-- A node address below the top. -/
theorem node_addr {L layer l : Nat} (hL : L < 2 ^ 32) (hl : layer < 2) (hl16 : l < 16) :
    word (tw 3 + (l + 1) * hiMul + layer * lxTop) 0 0 + eOfNat (L / 2 ^ (16 * layer) / 2 ^ (l + 1)) =
      eOfNat (addrNat 3 0 ((l + 1) + 2 ^ 23 * layer) (L / 2 ^ (16 * layer) / 2 ^ (l + 1))) := by
  have hk : L / 2 ^ (16 * layer) / 2 ^ (l + 1) < 2 ^ 32 :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (key_lt hL)
  rw [show tw 3 + (l + 1) * hiMul + layer * lxTop = 2 ^ 32 * (3 * 2 ^ 24 + (l + 1) + 2 ^ 23 * layer) by
    simp only [tw, hiMul, lxTop]; ring, word_add_eOfNat hk]
  congr 1
  simp only [addrNat]
  rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by interval_cases layer <;> omega),
    Nat.mod_eq_of_lt (show 3 < 32 by omega), Nat.zero_mod]
  ring

/-- The top address of the top layer. -/
theorem node_addr_end {L l : Nat} (hL : L < 2 ^ 32) (hl : 16 + l + 1 = 32) :
    word (tw 3 + (l + 1) * hiMul + 1 * lxTop) 0 0 =
      eOfNat (addrNat 3 0 ((l + 1) + 2 ^ 23 * 1) (L / 2 ^ (16 * 1) / 2 ^ (l + 1))) := by
  have : L / 2 ^ (16 * 1) / 2 ^ (l + 1) = 0 := by
    rw [Nat.div_div_eq_div_mul, ← pow_add, show 16 * 1 + (l + 1) = 32 by omega]
    exact Nat.div_eq_of_lt hL
  rw [this, word_eq_eOfNat]
  have : l = 15 := by omega
  subst this
  congr 1

/-- Tweak bytes as a cell's. -/
theorem tweakBytes_chain (lay : Layer) (key : KeyIndex) (s : ChainStep) :
    tweakBytes (.chain lay key s) = cellBytes (eOfNat (addrNat 1 s.val (0 + 2 ^ 23 * lay.val) key.val)) := by
  rw [← fieldBytes_tweakFields]; rfl

theorem tweakBytes_leaf (lay : Layer) (key : KeyIndex) :
    tweakBytes (.leaf lay key) = cellBytes (eOfNat (addrNat 2 0 (0 + 2 ^ 23 * lay.val) key.val)) := by
  rw [← fieldBytes_tweakFields]; rfl

theorem tweakBytes_message (lay : Layer) (key : KeyIndex) :
    tweakBytes (.message lay key) = cellBytes (eOfNat (addrNat 12 0 (0 + 2 ^ 23 * lay.val) key.val)) := by
  rw [← fieldBytes_tweakFields]; rfl

theorem tweakBytes_node (lay : Layer) (level idx : Nat) :
    tweakBytes (.node lay level idx) = cellBytes (eOfNat (addrNat 3 0 (level + 2 ^ 23 * lay.val) idx)) := by
  rw [← fieldBytes_tweakFields]; rfl

/-! ## Chains: the index does not enter a leanXMSS step -/

theorem chainFrom_lx (pp : E) (adr : Nat → E) (idx : E) (i : Nat) :
    ∀ m s v, chainFrom true pp adr idx i m s v = chainFrom true pp adr 0 i m s v
  | 0, _, _ => rfl
  | m + 1, s, v => by simp only [chainFrom, stepCells, ↓reduceIte]; exact chainFrom_lx pp adr idx i m _ _

theorem tipPair_lx (pp : E) (adr : Nat → E) (idx : E) (i d : Nat) (x : E) :
    tipPair true pp adr idx i d x = tipPair true pp adr 0 i d x := by
  simp only [tipPair]; split <;> simp only [chainFrom_lx]

theorem exists_fun_of_lt {P : Nat → E → Prop} {n : Nat} (h : ∀ i < n, ∃ x, P i x) :
    ∃ f : Nat → E, ∀ i < n, P i (f i) := by
  classical
  exact ⟨fun i => if hi : i < n then (h i hi).choose else 0, fun i hi => by
    simp only [hi, ↓reduceDIte]; exact (h i hi).choose_spec⟩

theorem digit_sum_le {dig : Nat → Nat} (hd : ∀ i, dig i < 4) (n : Nat) : ∑ i ∈ Finset.range n, dig i ≤ 3 * n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ]; have := hd n; omega

theorem mFold_canonical (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) :
    ∀ (m l : Nat) (x : E), (0 < m ∨ IsCanonical128 x) → IsCanonical128 (mFold pp A bits sibs m l x)
  | 0, _, _, h => h.resolve_left (by omega)
  | m + 1, l, x, _ => mFold_canonical pp A bits sibs m (l + 1) _ (Or.inr (isCanonical128_hb _).1)

/-- The tips of a layer's codeword. -/
def xTip (a : Nat) (idx d0 : V) (i : Nat) : V :=
  ((cCodeword (xW a idx) (fun s => .n (129 + s)) 19 xTarget d0
    (a + 6)).2.2.getD i (.n 0, .n 0)).1

/-- **The tail of a layer is sound**: the digest decodes, and the root is the fold of the path over
the leaf of the chains recovered from some values. -/
theorem xTail_sound (hq : XQ inst) {σ : Val} {L layer a : Nat} {idx d0 : V} (hl : layer < 2)
    (hpre : XPre σ L) {key : KeyIndex} (hkey : key.val = L / 2 ^ (16 * layer))
    (hidx : σ idx = eOfNat (xIdx layer L)) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (xTail layer a idx d0).1 next kret) :
    (∃ (enc : Encoding) (vals sibs : Nat → E), Codeword.decode (xv (σ d0)) = some enc ∧
      @treeFold Id _ inst (xpp (σ (.n 1))) ⟨layer, hl⟩ key (fun l => xv (sibs l.val)) layerHeight
        (@leafHash Id _ inst (xpp (σ (.n 1))) ⟨layer, hl⟩ key fun i =>
          @recoverChain Id _ inst (xpp (σ (.n 1))) ⟨layer, hl⟩ key i (enc i) (xv (vals i.val))) =
        xv (σ (xTail layer a idx d0).2.2)) ∧ IsCanonical128 (σ (xTail layer a idx d0).2.2) ∧ next := by
  set lay : Layer := ⟨layer, hl⟩
  simp only [xTail, holdsList_append] at h ⊢
  obtain ⟨hS, h⟩ := (xStepAddrs_iff idx a).mp h
  obtain ⟨⟨dig, hdig, htips, htarget, hd0⟩, h⟩ := cCodeword_sound (w := xW a idx) hpre.md hpre.pow (G := 19)
    (by norm_num) h
  obtain ⟨hc, hc1, h⟩ := h
  have hc : σ (.n _) = word (tw 2) 0 0 := hc
  have hc1 : σ (.n _) = σ idx + σ (.n _) := hc1
  obtain ⟨hleaf, h⟩ := hashValues_sound (Or.inr (by norm_num)) (by norm_num) h
  obtain ⟨⟨sibs, hroot⟩, hn⟩ := merkle_sound (β := fun l => key.val.testBit l) 16 0 _ _ (fun l' _ hl' => by
    rw [show 3 + 16 * layer + l' = 3 + (16 * layer + l') by omega, hpre.bits _ (by omega), hkey, Nat.testBit_div_two_pow, Nat.add_comm l']) h
  have hsum : ∑ i ∈ Finset.range numChains, dig i = targetSum := by
    rw [xTarget_eq] at htarget
    have := digit_sum_le hdig (3 * 19 + 1)
    exact (gen_pow_inj (by norm_num) (by omega) htarget).symm
  obtain ⟨vals, hvals⟩ := exists_fun_of_lt htips
  refine ⟨⟨fun i => ⟨dig i.val, hdig _⟩, vals, sibs, ?_, ?_⟩,
    by rw [hroot]; exact mFold_canonical _ _ _ _ _ _ _ (Or.inl (by norm_num)), hn⟩
  · rw [hd0]
    exact decode_lit hdig hsum
  have hL := hpre.lt
  have hadr : ∀ s : ChainStep, cellBytes (σ (.n (a + 2 * s.val + 1))) = tweakBytes (.chain lay key s) := fun s => by
    have hs : s.val < 3 := s.isLt
    rw [(hS s.val hs).2, hidx, chain_addr hL hl hs, tweakBytes_chain, hkey]
  have hchains : (fun i : ChainIndex => @recoverChain Id _ inst (xpp (σ (.n 1))) lay key i ⟨dig i.val, hdig _⟩
      (xv (vals i.val))) = fun i => xv (σ (xTip a idx d0 i.val)) := by
    funext i
    rw [recoverChain_cells (adr := fun s => σ (.n (a + 2 * s + 1))) hq hadr]
    have := (hvals i.val i.isLt).1
    simp only [xTip]
    rw [this]
    exact congrArg (fun t => xv t.1) (tipPair_lx _ _ _ _ _ _).symm
  have hleafAdr : cellBytes (σ (.n ((cCodeword (xW a idx) (fun s => .n (129 + s)) 19 xTarget d0 (a + 6)).2.1 + 1))) =
      tweakBytes (.leaf lay key) := by
    rw [hc1, hc, hidx, tag_addr hL hl (by norm_num), tweakBytes_leaf, hkey]
  have hA : ∀ l < layerHeight, cellBytes (mAddr σ (fun l => .n (128 - 3 * (16 * layer + l)))
      (fun l => tw 3 + (l + 1) * hiMul + layer * lxTop) (fun l => 16 * layer + l + 1 == 32) l) =
      tweakBytes (.node lay (l + 1) (key.val / 2 ^ (l + 1))) := fun l hl16 => by
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
  rw [hchains, leafHash_cells hq (fun i => σ (xTip a idx d0 i)) hleafAdr]
  simp only [xTip] at hleaf ⊢
  rw [show numChains = 58 from rfl, ← hleaf, treeFold_cells hq hA sibs layerHeight le_rfl, hroot]
  rfl

/-! ## The digests -/

theorem xDigest0_sound {σ : Val} {b : Nat} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (xDigest0 b) next kret) :
    LoadHolds rd (σ (.n 0)) 2 (σ (.n (b + 3))) ∧ LoadHolds rd (σ (.n 0)) 3 (σ (.n (b + 4))) ∧
      IsCanonical128 (σ (.n 1)) ∧ IsCanonical128 (σ (.n (b + 3))) ∧ IsCanonical128 (σ (.n (b + 4))) ∧
      σ (.n (b + 2)) = σ (.n 128) + word (tw 12) 0 0 ∧
      σ (.n (b + 14)) = (hcell [σ (.n 1), σ (.n (b + 2)), σ (.n (b + 3)), σ (.n (b + 4)), σ (.n b)]).1 ∧
      next := by
  simp only [xDigest0, ivs, cst, b2s, addS, hintW, List.cons_append, List.nil_append, holdsList_cons_atom,
    holdsList_nil, Atom.Holds, true_and] at h
  obtain ⟨h1, h2, hl3, hl4, h5, h6, h7, hc1, h10, h11, h12, h13, hc2, hn⟩ := h
  rw [h5, h6, h7] at hc1
  rw [h10, h11, h12, h13, word_zero] at hc2
  have hr : ([σ (.n b)].flatMap cellBytes).length = 16 := by rw [length_flatMap_cellBytes']; rfl
  have hc2' : CompressCells ![σ (.n b), 0, 0, 0] (σ (.n (b + 8))) (σ (.n (b + 9))) (σ (.n (b + 14)))
      (σ (.n (b + 15))) (mdw (64 + ([σ (.n b)].flatMap cellBytes).length) true) := by rw [hr]; exact hc2
  obtain ⟨hb0, -, -, ho⟩ := (compress_two_iff (blockBytes_one (σ (.n b))) (by rw [hr]; omega)
    (by rw [hr]; omega)).mp ⟨hc1, hc2'⟩
  rw [fin4_canonical] at hb0
  refine ⟨hl3, hl4, hb0.1, hb0.2.2.1, hb0.2.2.2, by rw [h2, h1], ?_, hn⟩
  refine (congrArg Prod.fst ho).trans ?_
  rw [blockBytes_four, hcell, ← List.flatMap_append]
  rfl

theorem xDigest1_sound {σ : Val} {b : Nat} {root : V} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (xDigest1 b root) next kret) :
    IsCanonical128 (σ root) ∧ σ (.n (b + 1)) = σ (.n 80) + word lxTop 0 0 ∧
      σ (.n (b + 4)) = σ (.n (b + 1)) + word (tw 12) 0 0 ∧
      σ (.n (b + 8)) = (hcell [σ (.n 1), σ (.n (b + 4)), σ root, σ (.n (b + 2))]).1 ∧ next := by
  simp only [xDigest1, ivs, cst, b2s, addS, hintW, List.cons_append, List.nil_append, holdsList_cons_atom,
    holdsList_nil, Atom.Holds, true_and] at h
  obtain ⟨h0, h1, h3, h4, h5, h6, h7, hc, hn⟩ := h
  rw [h5, h6, h7] at hc
  obtain ⟨hcan, ho⟩ := compress4_iff.mp hc
  exact ⟨hcan.2.2.1, by rw [h1, h0], by rw [h4, h3], congrArg Prod.fst ho, hn⟩

/-! ## A layer's root -/

theorem layerRoot_of_tail {pp : E} {lay : Layer} {key : KeyIndex} {M : HashInput} {rho d : E}
    {enc : Encoding} {vals sibs : Nat → E} {root : E}
    (hd : @messageDigest Id _ inst (xpp pp) lay key M (xv rho) = xv d) (hdec : Codeword.decode (xv d) = some enc)
    (hroot : @treeFold Id _ inst (xpp pp) lay key (fun l => xv (sibs l.val)) layerHeight
        (@leafHash Id _ inst (xpp pp) lay key fun i =>
          @recoverChain Id _ inst (xpp pp) lay key i (enc i) (xv (vals i.val))) = xv root) :
    @layerRoot Id _ inst (xpp pp) lay key M ⟨xv rho, fun i => xv (vals i.val), fun l => xv (sibs l.val)⟩ =
      some (xv root) := by
  rw [layerRoot_id, otsLeaf_id]
  simp only
  rw [hd, hdec]
  simp only [Option.map_some]
  exact congrArg some hroot

/-- **The bottom layer is sound.** -/
theorem xLayer0_sound (hq : XQ inst) {σ : Val} {L b : Nat} {root : V} (hpre : XPre σ L) {key : KeyIndex}
    (hkey : key.val = L) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (xLayer 0 b root).1 next kret) :
    LoadHolds rd (σ (.n 0)) 2 (σ (.n (b + 3))) ∧ LoadHolds rd (σ (.n 0)) 3 (σ (.n (b + 4))) ∧
      IsCanonical128 (σ (.n 1)) ∧ IsCanonical128 (σ (.n (b + 3))) ∧ IsCanonical128 (σ (.n (b + 4))) ∧
      (∃ part, @layerRoot Id _ inst (xpp (σ (.n 1))) bottomLayer key
        (cellBytes (σ (.n (b + 3))) ++ cellBytes (σ (.n (b + 4)))) part = some (xv (σ (xLayer 0 b root).2.2))) ∧
      next := by
  rw [xLayer_zero] at h ⊢
  dsimp only at h ⊢
  rw [holdsList_append] at h
  obtain ⟨hl3, hl4, hpp, hm0, hm1, hadr, hd, h⟩ := xDigest0_sound h
  have hkey' : key.val = L / 2 ^ (16 * 0) := by rw [hkey]; simp
  have hidx : σ (.n 128) = eOfNat (xIdx 0 L) := by
    have := hpre.nodes 0 (by omega)
    simpa [xIdx] using this
  obtain ⟨⟨enc, vals, sibs, hdec, hroot⟩, -, hn⟩ := xTail_sound hq (by omega) hpre hkey' hidx h
  refine ⟨hl3, hl4, hpp, hm0, hm1, ⟨_, layerRoot_of_tail (rho := σ (.n b)) ?_ hdec hroot⟩, hn⟩
  rw [messageDigest_cells hq (a := σ (.n (b + 2))) (cs := [σ (.n (b + 3)), σ (.n (b + 4))]) ?_ (by simp), hd]
  · simp only [List.cons_append, List.nil_append]
  · rw [hadr, hidx, tag_addr hpre.lt (by omega) (by omega), tweakBytes_message, hkey',
      show (bottomLayer : Layer).val = 0 from rfl]

/-- **The top layer is sound.** -/
theorem xLayer1_sound (hq : XQ inst) {σ : Val} {L b : Nat} {root : V} (hpre : XPre σ L) {key : KeyIndex}
    (hkey : key.val = L / 2 ^ 16) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (xLayer 1 b root).1 next kret) :
    IsCanonical128 (σ root) ∧ IsCanonical128 (σ (xLayer 1 b root).2.2) ∧
      (∃ part, @layerRoot Id _ inst (xpp (σ (.n 1))) topLayer key (cellBytes (σ root)) part =
        some (xv (σ (xLayer 1 b root).2.2))) ∧ next := by
  rw [xLayer_one] at h ⊢
  dsimp only at h ⊢
  rw [holdsList_append] at h
  obtain ⟨hcan, hidx, hadr, hd, h⟩ := xDigest1_sound h
  have hkey' : key.val = L / 2 ^ (16 * 1) := by rw [hkey]
  have hidx' : σ (.n (b + 1)) = eOfNat (xIdx 1 L) := by
    have := hpre.nodes 16 (by omega)
    rw [hidx, show 128 - 3 * 16 = 80 by omega] at *
    rw [this, xIdx, show lxTop = 2 ^ 55 * 1 by rfl, eOfNat_add_word (lt_of_le_of_lt (Nat.div_le_self _ _)
      (lt_trans hpre.lt (by norm_num)))]
    congr 1
    ring
  obtain ⟨⟨enc, vals, sibs, hdec, hroot⟩, hrc, hn⟩ := xTail_sound hq (by omega) hpre hkey' hidx' h
  refine ⟨hcan, hrc, ⟨_, layerRoot_of_tail (rho := σ (.n (b + 2))) ?_ hdec hroot⟩, hn⟩
  rw [messageDigest_cells hq (a := σ (.n (b + 4))) (cs := [σ root]) ?_ (by simp), hd]
  · simp only [List.cons_append, List.nil_append]
  · rw [hadr, hidx', tag_addr hpre.lt (by omega) (by omega), tweakBytes_message, hkey',
      show (topLayer : Layer).val = 1 from rfl]

end
end LeanVM.Guest.B1.Sig
