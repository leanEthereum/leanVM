/-
  LeanVM.Guest.B1.Sig.XmssLayer

  A layer of `verify_lean_xmss` is the layer's root of leanXMSS: from its message digest, its
  codeword, its one-time leaf and its path.
-/

module

public import LeanVM.Guest.B1.Sig.Codeword
public import LeanVM.Guest.B1.Sig.Shifts
public import LeanVM.Guest.B1.Sig.Digest80
public import LeanVM.Guest.B1.Sig.XmssT
public import Common.WithHash
public import LeanVM.Guest.WithHash

/-!
# A layer of `verify_lean_xmss`

`xLayer layer b root` is the layer's message digest, its three step addresses, the
codeword (`xCw`), the one-time leaf (`xLeafK`) and the path (`xMk`). `xLayerCore_sound`: when its
statements after the digest hold, the prologue's facts given (`XPre`), the digest's first cell
`hcell` of `P`, the message's address and cells and the randomizer, `layerRoot` of the signature
part the frame holds (`xPart`) is the cell the path reaches.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The signature a layer's frame holds -/

/-- **The layer signature `verify_lean_xmss` checks**: the randomizer, the chain values (each
chain's hinted start, in the arm its group's dispatch takes), the path (each level's sibling). -/
noncomputable def xPart (layer b : Nat) (σ : Val) : LeanXmss.LayerSignature :=
  ⟨xv (σ (xRho layer b)), fun i => xv (σ (cwStart (xW layer b) 19 (xA layer b + 6) σ i.val)),
    fun l => xv (mSib σ (xBitOf layer) l.val (mBase (xNodeOf layer) 0 l.val (xLeafK layer b).2.1))⟩

/-! ## The prologue -/

/-- The leaf index the frame's bits spell. -/
noncomputable def xLeaf (σ : Val) : Nat := bitsOf σ 2 32

/-- What the prologue establishes. -/
structure XPre (σ : Val) : Prop where
  bits : ∀ j < 32, IsBit (σ (xBit j))
  nodes : ∀ l < 32, σ (xNode l) = eOfNat (xLeaf σ >>> l)
  powers : ∀ s < 10, σ (xPower s) = gen ^ s
  tags : ∀ i < 58, σ (xTag i) = eOfNat i

theorem xLeaf_lt (σ : Val) : xLeaf σ < 2 ^ 32 := bitsVal_lt _ _

/-! ## Addresses -/

theorem two_pow_mul_xor_mul (s a b : Nat) : 2 ^ s * a ^^^ 2 ^ s * b = 2 ^ s * (a ^^^ b) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_xor, Nat.testBit_two_pow_mul]
  cases decide (s ≤ j) <;> simp

/-- An address cell: the index's word plus a constant above bit 32. -/
theorem idx_add_word {q1 q2 key : Nat} (hkey : key < 2 ^ 32) :
    eOfNat (2 ^ 32 * q1 + key) + word (2 ^ 32 * q2) 0 = eOfNat (2 ^ 32 * (q1 ^^^ q2) + key) := by
  rw [word_eq_eOfNat, ← Value.eOfNat_add_of_lt hkey, ← Value.eOfNat_add_of_lt hkey, add_right_comm,
    ← Value.eOfNat_xor, two_pow_mul_xor_mul]

theorem word_add_eOfNat {q lo : Nat} (hlo : lo < 2 ^ 32) :
    word (2 ^ 32 * q) 0 + eOfNat lo = eOfNat (2 ^ 32 * q + lo) := by
  rw [word_eq_eOfNat, Value.eOfNat_add_of_lt hlo]

/-- The index of layer `layer`: the leaf index's key, the top layer's bit `55` set. -/
def xIdxNat (layer L : Nat) : Nat := 2 ^ 32 * (2 ^ 23 * layer) + L >>> (16 * layer)

theorem key_lt (L layer : Nat) (hL : L < 2 ^ 32) : L >>> (16 * layer) < 2 ^ 32 :=
  lt_of_le_of_lt (Nat.shiftRight_le _ _) hL

theorem xIdxNat_zero (L : Nat) : xIdxNat 0 L = L := by simp [xIdxNat]

theorem xIdxNat_one {L : Nat} (hL : L < 2 ^ 32) :
    eOfNat (L >>> 16) + word lxTop 0 = eOfNat (xIdxNat 1 L) := by
  rw [add_comm, show lxTop = 2 ^ 32 * 2 ^ 23 by simp [lxTop], word_add_eOfNat (key_lt L 1 hL)]
  simp [xIdxNat]

/-- A message's bytes are its two cells', the first low. -/
theorem bytesLE_cellPairVal (c d : E) : HashSig.littleEndianBytes 32 (cellPairVal c d) = cellBytes c ++ cellBytes d := by
  have h0 := cellNat_lt c
  have h1 := cellNat_lt d
  have ht : (cellPairVal c d).toNat = cellNat c + 2 ^ 128 * cellNat d := by
    rw [cellPairVal, BitVec.toNat_append, toNat_cellVal, toNat_cellVal, Nat.shiftLeft_eq, mul_comm,
      two_pow_mul_or h0]
    ring
  rw [bytesLE_eq, ht, cellBytes_eq_leBytes, cellBytes_eq_leBytes,
    show (2 : Nat) ^ 128 = 256 ^ 16 by norm_num, show 32 = 16 + 16 from rfl,
    leBytes_add_mul _ _ _ _ (by norm_num; omega)]

/-! ## Chains and folds -/

theorem xFold_congr {pp : E} {A A' : Nat → E} {bits bits' : Nat → Bool} {sibs sibs' : Nat → E} :
    ∀ (m : Nat), (∀ l < m, A l = A' l ∧ bits l = bits' l ∧ sibs l = sibs' l) →
      ∀ x, xFold pp A bits sibs m x = xFold pp A' bits' sibs' m x
  | 0, _, _ => rfl
  | m + 1, h, x => by
      simp only [xFold]
      obtain ⟨h1, h2, h3⟩ := h m (by omega)
      rw [xFold_congr m (fun l hl => h l (by omega)) x, h1, h2, h3]

/-! ## The target sum -/

theorem xTarget_eq : xTarget = gen ^ 106 := by
  rw [Value.gen_pow_eq_ofK, xTarget, word, Value.ofBits_zero]
  rw [← ofK_eq_ofLimbs]
  exact congrArg ofK (by decide +kernel)

/-! ## A layer, sound -/

theorem cellsBytes_getD_past {cs : List E} {j : Nat} (h : 16 * cs.length ≤ j) :
    (cellsBytes cs).getD j 0 = 0 := by
  rw [List.getD_eq_default _ _ (by rw [length_cellsBytes]; exact h)]

attribute [local irreducible] kMsg codewordT merkleT

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

theorem xStep_sound (hpad : PadOK σ xPad) (layer b : Nat) :
    StepSound rd σ (xW layer b)
      (fun i s y => (hcell [σ (.n 1), σ (.n (xA layer b + 2 * s + 1)), y, σ (xTag i)]).1) := by
  intro i s v c o h
  exact k64_sound hpad h

theorem xW_atoms (layer b : Nat) : StepAtoms (xW layer b) := fun _ _ _ _ _ => rfl

theorem xStepAddrs_sound {idx : V} {a : Nat} (h : AtomsHold rd σ (xStepAddrs idx a)) :
    ∀ s < 3, σ (.n (a + 2 * s + 1)) = σ idx + word (tw 1 + s * stepMul) 0 := by
  intro s hs
  have e1 := h.atom (a := .const (.n (a + 2 * s)) (word (tw 1 + s * stepMul) 0)) (by
    simp only [xStepAddrs, List.mem_flatMap, List.mem_range]
    exact ⟨s, hs, List.mem_cons_self ..⟩)
  have e2 := h.atom (a := .add (.n (a + 2 * s + 1)) idx (.n (a + 2 * s))) (by
    simp only [xStepAddrs, List.mem_flatMap, List.mem_range]
    exact ⟨s, hs, List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩)
  simp only [Atom.Holds] at e1 e2
  rw [e2, e1]

theorem xStepAddrs_atoms (idx : V) (a : Nat) : atomsOnly (xStepAddrs idx a) = true := rfl

/-- The codeword of a layer, sound. -/
theorem xCw_sound (hpre : XPre σ) (hpad : PadOK σ xPad) {layer b : Nat} {rest : List Stmt} {next : Prop}
    (h : Stmt.HoldsList C rd σ ((xCw layer b).1 ++ rest) next kret) :
    Stmt.HoldsList C rd σ rest next kret ∧
      (∀ i < 3 * 19 + 1, cwDigit (xW layer b) 19 (xA layer b + 6) σ i < 4 ∧
        σ (cwTip (xW layer b) (xA layer b + 6) i) =
          chainT (fun i s y => (hcell [σ (.n 1), σ (.n (xA layer b + 2 * s + 1)), y, σ (xTag i)]).1) i
            (3 - cwDigit (xW layer b) 19 (xA layer b + 6) σ i) (cwDigit (xW layer b) 19 (xA layer b + 6) σ i)
            (σ (cwStart (xW layer b) 19 (xA layer b + 6) σ i))) ∧
      gen ^ (∑ i ∈ Finset.range (3 * 19 + 1), cwDigit (xW layer b) 19 (xA layer b + 6) σ i) = xTarget ∧
      σ (xD0 layer b) = lit (∑ i ∈ Finset.range (3 * 19 + 1),
        cwDigit (xW layer b) 19 (xA layer b + 6) σ i * 4 ^ i) :=
  codewordT_sound (xW_atoms layer b) (xStep_sound hpad layer b) (fun s hs => hpre.powers s hs)
    (by norm_num) (by norm_num) h

theorem xLeafK_atoms (layer b : Nat) : atomsOnly (xLeafK layer b).1 = true := kMsg_atoms ..

theorem xMk_atoms (layer b : Nat) : atomsOnly (xMk layer b).1 = true := merkleT_atoms ..

theorem atomsOnly_cst_addS (c : Nat) (w : E) (d x y : V) : atomsOnly [cst c w, addS d x y] = true := rfl

/-- The key of layer `layer` a leaf index signs with. -/
theorem keyAt_val (L : Nat) (hL : L < 2 ^ 32) (layer : Nat) (hl : layer < 2) :
    (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer, hl⟩).val = L >>> (16 * layer) := by
  simp [LeanXmss.keyIndexOnLayer, LeanXmss.layerHeight, Nat.shiftRight_eq_div_pow]

theorem chainT_eq_xChain' {f : Nat → Nat → E → E} {pp : E} {adr : Nat → E} {i : Nat}
    (hf : ∀ s y, f i s y = (hcell [pp, adr s, y, eOfNat i]).1) :
    ∀ (m s : Nat) (x : E), chainT f i m s x = xChain pp adr i m s x
  | 0, _, _ => rfl
  | m + 1, s, x => by
      rw [chainT, xChain, hf]
      exact chainT_eq_xChain' hf m (s + 1) _

/-- **The chain step addresses.** -/
theorem xStepAdr_bytes {L layer s : Nat} (hL : L < 2 ^ 32) (hl : layer < 2) (hs : s < 3) :
    cellBytes (eOfNat (xIdxNat layer L) + word (tw 1 + s * stepMul) 0) =
      LeanXmss.tweakBytes (.chain ⟨layer, hl⟩ (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer, hl⟩) ⟨s, by
        simp [HashSig.chainLength, HashSig.winternitzBits]; omega⟩) := by
  have hk := key_lt L layer hL
  rw [show LeanXmss.tweakBytes (.chain ⟨layer, hl⟩ (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer, hl⟩)
      ⟨s, _⟩) =
      LeanXmss.addressBytes (LeanXmss.tweakFields 1 s (0 + 2 ^ 23 * layer) (L >>> (16 * layer))) by
      rw [← keyAt_val L hL layer hl]; rfl, fieldBytes_tweakFields, xIdxNat,
    show tw 1 + s * stepMul = 2 ^ 32 * (2 ^ 24 + 2 ^ 29 * s) by simp [tw, stepMul]; ring,
    idx_add_word hk]
  congr 2
  unfold addrNat
  rw [Nat.mod_eq_of_lt hk]
  interval_cases layer <;> interval_cases s <;> norm_num <;> omega

/-- **The leaf address.** -/
theorem xLeafAdr_bytes {L layer : Nat} (hL : L < 2 ^ 32) (hl : layer < 2) :
    cellBytes (eOfNat (xIdxNat layer L) + word (tw 2) 0) =
      LeanXmss.tweakBytes (.leaf ⟨layer, hl⟩ (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer, hl⟩)) := by
  have hk := key_lt L layer hL
  rw [show LeanXmss.tweakBytes (.leaf ⟨layer, hl⟩ (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer, hl⟩)) =
      LeanXmss.addressBytes (LeanXmss.tweakFields 2 0 (0 + 2 ^ 23 * layer) (L >>> (16 * layer))) by
      rw [← keyAt_val L hL layer hl]; rfl, fieldBytes_tweakFields, xIdxNat,
    show tw 2 = 2 ^ 32 * 2 ^ 25 by simp [tw], idx_add_word hk]
  congr 2
  unfold addrNat
  rw [Nat.mod_eq_of_lt hk]
  interval_cases layer <;> norm_num <;> omega

/-- **The message address.** -/
theorem xMsgAdr_bytes {L layer : Nat} (hL : L < 2 ^ 32) (hl : layer < 2) :
    cellBytes (eOfNat (xIdxNat layer L) + word (tw 12) 0) =
      LeanXmss.tweakBytes (.message ⟨layer, hl⟩ (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer,
          hl⟩)) := by
  have hk := key_lt L layer hL
  rw [show LeanXmss.tweakBytes (.message ⟨layer, hl⟩ (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer,
      hl⟩)) =
      LeanXmss.addressBytes (LeanXmss.tweakFields 12 0 (0 + 2 ^ 23 * layer) (L >>> (16 * layer))) by
      rw [← keyAt_val L hL layer hl]; rfl, fieldBytes_tweakFields, xIdxNat,
    show tw 12 = 2 ^ 32 * (12 * 2 ^ 24) by simp [tw], idx_add_word hk]
  congr 2
  unfold addrNat
  rw [Nat.mod_eq_of_lt hk]
  interval_cases layer <;> norm_num <;> omega

/-- **The node addresses**: level `l`'s, the parent's index added unless it is the root. -/
theorem xNodeAdr_bytes {L layer l : Nat} (hL : L < 2 ^ 32) (hl : layer < 2) (hl16 : l < 16) :
    cellBytes (word (xAddrOf layer l) 0 + (if 16 * layer + l + 1 = 32 then 0 else
        eOfNat (L >>> (16 * layer + l + 1)))) =
      LeanXmss.tweakBytes (.node ⟨layer, hl⟩ (l + 1)
        ((LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer, hl⟩).val / 2 ^ (l + 1))) := by
  have hk := key_lt L layer hL
  rw [show LeanXmss.tweakBytes (.node ⟨layer, hl⟩ (l + 1)
        ((LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer, hl⟩).val / 2 ^ (l + 1))) =
      LeanXmss.addressBytes (LeanXmss.tweakFields 3 0 (l + 1 + 2 ^ 23 * layer)
        ((L >>> (16 * layer)) / 2 ^ (l + 1))) by rw [← keyAt_val L hL layer hl]; rfl,
    fieldBytes_tweakFields,
    show xAddrOf layer l = 2 ^ 32 * (3 * 2 ^ 24 + (l + 1) + 2 ^ 23 * layer) by
      simp [xAddrOf, tw, hiMul, lxTop]; ring]
  have hdiv : L >>> (16 * layer) / 2 ^ (l + 1) = L >>> (16 * layer + l + 1) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]
    ring_nf
  rw [hdiv]
  have hlt : L >>> (16 * layer + l + 1) < 2 ^ 32 := lt_of_le_of_lt (Nat.shiftRight_le _ _) hL
  split
  · rename_i h32
    have h0 : L >>> (16 * layer + l + 1) = 0 := by
      rw [h32, Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hL
    rw [h0, add_zero, word_eq_eOfNat]
    congr 2
    unfold addrNat
    interval_cases layer <;> omega
  · rw [word_add_eOfNat hlt]
    congr 2
    unfold addrNat
    rw [Nat.mod_eq_of_lt hlt]
    interval_cases layer <;> omega


/-- **A layer after its digest, sound**: the layer's statements after the message digest holding,
`layerRoot` of the part the frame holds reaches the cell the path reaches. -/
theorem xLayerCore_sound (hpre : XPre σ) (hpad : PadOK σ xPad) {layer b : Nat} (hl : layer < 2)
    (hidx : σ (xIdx layer b) = eOfNat (xIdxNat layer (xLeaf σ)))
    {msgCells : List E} {M : HashSig.HashInput} (hM : M = msgCells.flatMap cellBytes) {aMsg : E}
    (haMsg : cellBytes aMsg = LeanXmss.tweakBytes
      (.message ⟨layer, hl⟩ (LeanXmss.keyIndexOnLayer ⟨xLeaf σ, xLeaf_lt σ⟩ ⟨layer, hl⟩)))
    (hd0 : σ (xD0 layer b) = (hcell (σ (.n 1) :: aMsg :: msgCells ++ [σ (xRho layer b)])).1)
    {rest : List Stmt} {next : Prop}
    (h : Stmt.HoldsList C rd σ (xStepAddrs (xIdx layer b) (xA layer b) ++ ((xCw layer b).1 ++
      ([cst (xCw layer b).2.1 (word (tw 2) 0), addS (.n ((xCw layer b).2.1 + 1)) (xIdx layer b)
        (.n (xCw layer b).2.1)] ++ ((xLeafK layer b).1 ++ ((xMk layer b).1 ++ rest))))) next kret) :
    Stmt.HoldsList C rd σ rest next kret ∧
      @LeanXmss.Verification.layerRootWithHash Id _ ⟨Node.keccakBits⟩ (xpp (σ (.n 1))) ⟨layer, hl⟩
        (LeanXmss.keyIndexOnLayer ⟨xLeaf σ, xLeaf_lt σ⟩ ⟨layer, hl⟩) M (xPart layer b σ) =
        some (xv (σ (xMk layer b).2.2)) := by
  have s1 := holdsList_split_atoms (xs := xStepAddrs (xIdx layer b) (xA layer b))
    (xStepAddrs_atoms _ _) h
  have hsteps := xStepAddrs_sound (atomsHold_of_holdsList (xStepAddrs_atoms _ _) s1.1)
  have s2 := xCw_sound (rest := [cst (xCw layer b).2.1 (word (tw 2) 0),
      addS (.n ((xCw layer b).2.1 + 1)) (xIdx layer b) (.n (xCw layer b).2.1)] ++
      ((xLeafK layer b).1 ++ ((xMk layer b).1 ++ rest))) hpre hpad s1.2
  have hcw := s2.2.1
  have hsum := s2.2.2.1
  have hd := s2.2.2.2
  have s3 := holdsList_split_atoms (xs := [cst (xCw layer b).2.1 (word (tw 2) 0),
      addS (.n ((xCw layer b).2.1 + 1)) (xIdx layer b) (.n (xCw layer b).2.1)])
    (atomsOnly_cst_addS _ _ _ _ _) s2.1
  have hla := atomsHold_of_holdsList (atomsOnly_cst_addS _ _ _ _ _) s3.1
  have e1 : σ (.n (xCw layer b).2.1) = word (tw 2) 0 := hla.atom (List.mem_cons_self ..)
  have e2 : σ (.n ((xCw layer b).2.1 + 1)) = σ (xIdx layer b) + σ (.n (xCw layer b).2.1) :=
    hla.atom (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have s4 := holdsList_split_atoms (xs := (xLeafK layer b).1) (xLeafK_atoms layer b) s3.2
  have hlk := atomsHold_of_holdsList (xLeafK_atoms layer b) s4.1
  have s5 := holdsList_split_atoms (xs := (xMk layer b).1) (xMk_atoms layer b) s4.2
  have hmk := atomsHold_of_holdsList (xMk_atoms layer b) s5.1
  refine ⟨s5.2, ?_⟩
  -- the values
  have hL := xLeaf_lt σ
  set key := LeanXmss.keyIndexOnLayer ⟨xLeaf σ, hL⟩ ⟨layer, hl⟩ with hkey
  set W := xW layer b with hW
  set K := xA layer b + 6 with hKb
  set dig := cwDigit W 19 K σ with hdig
  have hdig4 : ∀ j, dig j < 4 := fun j => Nat.mod_lt _ (by norm_num)
  have hsum' : ∑ i ∈ Finset.range 58, dig i = 106 := by
    have h106 : gen ^ (∑ i ∈ Finset.range (3 * 19 + 1), dig i) = gen ^ 106 := by rw [hsum, xTarget_eq]
    have hle : ∑ i ∈ Finset.range (3 * 19 + 1), dig i ≤ ∑ _i ∈ Finset.range (3 * 19 + 1), 3 :=
      Finset.sum_le_sum fun j _ => by have := hdig4 j; omega
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hle
    simp only [show 3 * 19 + 1 = 58 from rfl] at h106 hle
    exact Value.gen_pow_inj (by omega) (by norm_num) h106
  -- the addresses
  have hidx' : σ (xIdx layer b) = eOfNat (xIdxNat layer (xLeaf σ)) := hidx
  have hadr : ∀ st : HashSig.ChainStep, cellBytes (σ (.n (xA layer b + 2 * st.val + 1))) =
      LeanXmss.tweakBytes (.chain ⟨layer, hl⟩ key st) := by
    intro st
    have := hsteps st.val st.isLt
    rw [this, hidx']
    exact xStepAdr_bytes hL hl st.isLt
  have haLeaf : cellBytes (σ (.n ((xCw layer b).2.1 + 1))) = LeanXmss.tweakBytes (.leaf ⟨layer, hl⟩ key) := by
    rw [e2, e1, hidx']
    exact xLeafAdr_bytes hL hl
  -- the leaf
  have hlk' : AtomsHold rd σ (kMsg xPad ((xLeafCells layer b).map KC.cell) 960 false none
      ((xCw layer b).2.1 + 2)).1 := hlk
  have htips := codewordT_tips W (G := 19) (by norm_num) xTarget (xD0 layer b) K
  have hcells : ((xLeafCells layer b).map KC.cell).map (KC.val σ) =
      σ (.n 1) :: σ (.n ((xCw layer b).2.1 + 1)) :: (List.range 58).map (fun i => σ (cwTip W K i)) := by
    simp only [xLeafCells, List.map_cons, List.map_map]
    rw [show (xCw layer b).2.2 = (codewordT W 19 xTarget (xD0 layer b) K).2.2 from rfl, htips]
    simp [KC.val]
  have hleaf := kMsg_sound (out := none) hpad (by simp) hlk' (by rw [List.length_map, xLeafCells,
    List.length_cons, List.length_cons, show (xCw layer b).2.2 = (codewordT W 19 xTarget (xD0 layer b) K).2.2
    from rfl, codewordT_tips_length W (by norm_num)]) (fun j hj => by
      rw [hcells]
      exact cellsBytes_getD_past (by simp; omega))
  rw [hcells, List.take_of_length_le (by rw [length_cellsBytes]; simp)] at hleaf
  have hlo := hleaf
  -- the path
  have hmk' : AtomsHold rd σ (merkleT xPad (.n 1) (xBitOf layer) (xNodeOf layer) (xAddrOf layer) 16 0
      (.n (xLeafK layer b).2.2) (xLeafK layer b).2.1).1 := hmk
  have hroot := merkleT_sound (bound := 16) hpad (fun l hl16 => hpre.bits _ (by omega)) 16 0 _ _
    (by norm_num) hmk'
  rw [mFold_eq_xFold] at hroot
  have hroot' : σ (xMk layer b).2.2 = xFold (σ (.n 1))
      (fun l' => σ (mAdr (xNodeOf layer) l' (mBase (xNodeOf layer) 0 (l' - 0) (xLeafK layer b).2.1)))
      (fun l' => decide (σ (xBitOf layer l') = 1))
      (fun l' => mSib σ (xBitOf layer) l' (mBase (xNodeOf layer) 0 (l' - 0) (xLeafK layer b).2.1)) 16
      (σ (.n (xLeafK layer b).2.2)) := hroot
  have hA : ∀ l < LeanXmss.layerHeight, cellBytes (σ (mAdr (xNodeOf layer) l
      (mBase (xNodeOf layer) 0 l (xLeafK layer b).2.1))) =
      LeanXmss.tweakBytes (.node ⟨layer, hl⟩ (l + 1) (key.val / 2 ^ (l + 1))) := by
    intro l hl16
    have e := merkleT_adr 16 0 _ _ hmk' l hl16
    rw [Nat.zero_add] at e
    rw [e]
    have hl16' : l < 16 := by simpa [LeanXmss.layerHeight] using hl16
    have hb := xNodeAdr_bytes hL hl hl16'
    by_cases h32 : 16 * layer + l + 1 = 32
    · simp only [xNodeOf, h32, ↓reduceIte] at hb ⊢
      exact hb
    · simp only [xNodeOf, h32, ↓reduceIte] at hb ⊢
      rw [hpre.nodes _ (by omega)]
      exact hb
  -- the Spec
  rw [layerRoot_id, otsLeaf_id]
  have hmd : @LeanXmss.Verification.messageDigestWithHash Id _ ⟨Node.keccakBits⟩ (xpp (σ (.n 1))) ⟨layer, hl⟩ key M
      (xPart layer b σ).randomizer = xv (lit (∑ j ∈ Finset.range 58, dig j * 4 ^ j)) := by
    rw [show (xPart layer b σ).randomizer = xv (σ (xRho layer b)) from rfl,
      messageDigest_cells xq_keccak haMsg hM, ← hd0, hd]
  rw [hmd, show (58 : Nat) = LeanXmss.chainCount from rfl, decode_lit hdig4 hsum', Option.map_some]
  refine congrArg some ?_
  have hrc : ∀ i : LeanXmss.ChainIndex, @LeanXmss.Verification.recoverChainWithHash Id _ ⟨Node.keccakBits⟩
      (xpp (σ (.n 1))) ⟨layer, hl⟩ key i ⟨dig i.val, hdig4 _⟩ ((xPart layer b σ).chainValues i) =
      xv (σ (cwTip W K i.val)) := by
    intro i
    rw [show (xPart layer b σ).chainValues i = xv (σ (cwStart W 19 K σ i.val)) from rfl,
      recoverChain_cells xq_keccak (pp := σ (.n 1)) (adr := fun s => σ (.n (xA layer b + 2 * s + 1))) hadr]
    have hi : i.val < 3 * 19 + 1 := i.isLt
    rw [(hcw i.val hi).2, chainT_eq_xChain' (fun s y => by rw [hpre.tags i.val i.isLt])]
  rw [show (fun i : LeanXmss.ChainIndex => @LeanXmss.Verification.recoverChainWithHash Id _ ⟨Node.keccakBits⟩
      (xpp (σ (.n 1))) ⟨layer, hl⟩ key i ⟨dig i.val, hdig4 _⟩ ((xPart layer b σ).chainValues i)) =
      fun i => xv (σ (cwTip W K i.val)) from funext hrc]
  have hlo' : σ (.n (xLeafK layer b).2.2) = (hcell (σ (.n 1) :: σ (.n ((xCw layer b).2.1 + 1)) ::
      List.map (fun i => σ (cwTip W K i)) (List.range LeanXmss.chainCount))).1 := hlo
  rw [leafHash_cells xq_keccak (fun i => σ (cwTip W K i)) haLeaf, ← hlo']
  beta_reduce
  rw [
    show (xPart layer b σ).authenticationPath = fun l => xv (mSib σ (xBitOf layer) l.val
      (mBase (xNodeOf layer) 0 l.val (xLeafK layer b).2.1)) from rfl,
    treeFold_cells xq_keccak hA (fun l => mSib σ (xBitOf layer) l
      (mBase (xNodeOf layer) 0 l (xLeafK layer b).2.1)) LeanXmss.layerHeight le_rfl, hroot']
  refine congrArg xv ?_
  apply xFold_congr
  intro l hl16
  have hl16' : l < 16 := by simpa [LeanXmss.layerHeight] using hl16
  refine ⟨by simp, ?_, rfl⟩
  rw [hkey, keyAt_val _ hL layer hl, Nat.testBit_shiftRight, xLeaf, bitsOf, testBit_bitsVal]
  simp [xBitOf, xBit, show 16 * layer + l < 32 by omega, show 2 + (16 * layer + l) = 2 + 16 * layer + l by omega]

end
end LeanVM.Guest.B1.Sig
