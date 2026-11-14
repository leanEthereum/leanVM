/-
  LeanVM.Guest.B1.Sig.XmssSegSound

  The leanXMSS check inline in `main_loop2` (`verify_lean_xmss`, `lean_ethereum.py`) is
  sound: whenever its statements hold, the rest holds, and with the carried chain indices held the
  signature its valuation holds verifies the claim at its pointer (`verify_lean_xmss_sound_holds`).
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegArms
public import LeanVM.Guest.B1.Sig.XmssSegPath
public import LeanVM.Guest.B1.Sig.XmssLayer
public import LeanVM.Guest.B1.Sig.InterfaceP

/-!
# The leanXMSS check of `main_loop2`, sound

`xmssSigOf σ`: the leaf index of the four windows the path's dispatches take (`sKw`, `lxIndex`),
and per layer (`sPart`) the randomizer, the chain starts in the codeword's arms taken (`sStart`)
and the hinted siblings in the windows' arms taken (`sSibAt`).

`verify_lean_xmss_sound_holds : verify_lean_xmss_sound_Spec xmssSigOf`: the prologue gives `P` and
the powers; each layer (`sLayerCore_sound`) its step addresses, its codeword, its leaf and its two
windows, each window an arm `k < 256` and its pin; the four pins make the hinted shifts the
windows' index (`lx_his`); then each layer's root is `layerRoot` of its part, the bottom over the
message, the top over the bottom root, asserted to be the claim's first cell.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The signature the valuation holds -/

theorem logG_lt (x : E) {bound : Nat} (hb : 0 < bound) : logG x bound < bound := by
  unfold logG
  generalize hf : List.find? _ (List.range bound) = o
  cases o with
  | none => simpa using hb
  | some k => simpa using List.mem_range.mp (List.mem_of_find?_eq_some hf)

/-- The arm window `w`'s dispatch takes: its selector's exponent. -/
noncomputable def sKw (σ : Val) (w : Nat) : Nat := logG (σ (sWin w)) 256

theorem sKw_lt (σ : Val) (w : Nat) : sKw σ w < 256 := logG_lt _ (by norm_num)

/-- The hinted sibling of level `l` of a layer: in the arm its window's dispatch takes. -/
noncomputable def sSibAt (σ : Val) (layer b l : Nat) : E :=
  if l < 8 then
    lxSibF σ (2 * layer) (lxArmB (2 * layer) 0 (sKw σ (2 * layer)) ((sLeafK layer b).2.1 + 5)) l
  else lxSibF σ (2 * layer + 1) (lxArmB (2 * layer + 1) 0 (sKw σ (2 * layer + 1))
    ((sWin0 layer b).2.1 + 5)) (l - 8)

/-- **The layer signature a layer of the check holds**: the randomizer, the chain values (each
chain's hinted start, in the arm its group's dispatch takes), the path (each level's hinted
sibling, in the arm its window's dispatch takes). -/
noncomputable def sPart (layer b : Nat) (σ : Val) : LeanXmss.LayerSignature :=
  ⟨xv (σ (sRho layer b)),
    fun i => xv (σ (sStart (sW layer b) σ (sA layer b + 6) (sA layer b + 6 + 70) i.val)),
    fun l => xv (sSibAt σ layer b l.val)⟩

/-- **The leanXMSS signature the check of `main_loop2` verifies**, read off the loop's valuation. -/
noncomputable def xmssSigOf (σ : Val) : LeanXmss.Signature :=
  ⟨⟨lxIndex (sKw σ), lxIndex_lt fun w _ => sKw_lt σ w⟩, fun lay =>
    if lay = LeanXmss.bottomLayer then sPart 0 88 σ else sPart 1 (sLayer 0 88 (.n 0)).2.1 σ⟩

/-! ## Folds -/

theorem mFold_add (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) :
    ∀ (m n l : Nat) (x : E), mFold pp A bits sibs (m + n) l x =
      mFold pp A bits sibs n (l + m) (mFold pp A bits sibs m l x)
  | 0, n, l, x => by rw [Nat.zero_add, Nat.add_zero]; rfl
  | m + 1, n, l, x => by
      rw [show m + 1 + n = (m + n) + 1 by omega, mFold, mFold_add pp A bits sibs m n (l + 1),
        show l + 1 + m = l + (m + 1) by omega]
      rfl

theorem mFold_shift (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) (j : Nat) :
    ∀ (m l : Nat) (x : E), mFold pp A bits sibs m (l + j) x =
      mFold pp (fun i => A (i + j)) (fun i => bits (i + j)) (fun i => sibs (i + j)) m l x
  | 0, l, x => rfl
  | m + 1, l, x => by
      simp only [mFold]
      rw [show l + j + 1 = l + 1 + j by omega, mFold_shift pp A bits sibs j m (l + 1)]

theorem mFold_congrB {pp : E} {A A' : Nat → E} {bits bits' : Nat → Bool} {sibs sibs' : Nat → E} :
    ∀ (m l : Nat), (∀ l', l ≤ l' → l' < l + m → A l' = A' l' ∧ bits l' = bits' l' ∧ sibs l' = sibs' l') →
      ∀ x, mFold pp A bits sibs m l x = mFold pp A' bits' sibs' m l x
  | 0, _, _, _ => rfl
  | m + 1, l, h, x => by
      simp only [mFold]
      obtain ⟨h1, h2, h3⟩ := h l le_rfl (by omega)
      rw [h1, h2, h3]
      exact mFold_congrB m (l + 1) (fun l' hl' hl'' => h l' (by omega) (by omega)) _

/-- **Sixteen levels are two windows of eight.** -/
theorem xFold_two {pp : E} {A A0 A1 : Nat → E} {bits b0 b1 : Nat → Bool} {sibs s0 s1 : Nat → E}
    (h0 : ∀ l < 8, A l = A0 l ∧ bits l = b0 l ∧ sibs l = s0 l)
    (h1 : ∀ l < 8, A (l + 8) = A1 l ∧ bits (l + 8) = b1 l ∧ sibs (l + 8) = s1 l) (x : E) :
    xFold pp A bits sibs 16 x = mFold pp A1 b1 s1 8 0 (mFold pp A0 b0 s0 8 0 x) := by
  rw [← mFold_eq_xFold, show (16 : Nat) = 8 + 8 from rfl, mFold_add,
    mFold_congrB 8 0 (fun l' _ hl => h0 l' (by omega)), show (0 + 8 : Nat) = 0 + 8 from rfl,
    mFold_shift]
  exact mFold_congrB 8 0 (fun l' _ hl => h1 l' (by omega)) _

/-! ## Addresses and windows -/

theorem lxNodeAddr_eq {L layer l : Nat} (hl16 : l < 16) :
    lxNodeAddr L (2 * layer + l / 8) (l % 8) = word (xAddrOf layer l) 0 +
      (if 16 * layer + l + 1 = 32 then 0 else eOfNat (L >>> (16 * layer + l + 1))) := by
  have e : 8 * (2 * layer + l / 8) + l % 8 = 16 * layer + l := by omega
  unfold lxNodeAddr lxNodeConst xAddrOf
  rw [e, show (16 * layer + l) % 16 = l by omega, show (16 * layer + l) / 16 = layer by omega]

theorem lxWin_lxIndex {K : Nat → Nat} (hk : ∀ w < 4, K w < 256) {w : Nat} (hw : w < 4) :
    lxWin (lxIndex K) w = K w := by
  have := hk 0 (by omega); have := hk 1 (by omega); have := hk 2 (by omega); have := hk 3 (by omega)
  simp only [lxWin, lxIndex, Nat.shiftRight_eq_div_pow]
  interval_cases w <;> norm_num <;> omega

/-! ## The prologue and the digests -/

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

attribute [local irreducible] kMsg sCodewordT lxWindowT

theorem sPrologue_atoms : atomsOnly sPrologue = true := by decide

theorem sPrologue_sound (h : AtomsHold rd σ sPrologue) :
    LoadHolds rd (σ sSigner) 1 (σ sLxPP) ∧ ∀ s < 13, σ (sPower s) = gen ^ s := by
  refine ⟨h.atom (a := .load sLxPP sSigner 1) (by simp [sPrologue, loadS]), fun s hs => ?_⟩
  have e := h.atom (a := .const (.n (75 + s)) (word (2 ^ s) 0)) (by
    simp only [sPrologue, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inr ⟨s, hs, rfl⟩)
  simp only [Atom.Holds] at e
  rw [sPower, e, word_eq_eOfNat, Value.gen_pow_eq_eOfNat (by omega)]

theorem sDigest0_atoms (b : Nat) : atomsOnly (sDigest0 b) = true := rfl

theorem sDigest0_pad (b k : Nat) (hk : k < 5) :
    cst (b + 10 + k) (word (if k = 0 then 1 else 0) 0) ∈ sDigest0 b := by
  simp only [sDigest0, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr ⟨k, hk, rfl⟩)

/-- **The bottom layer's digest**: the message's cells loaded, the padding run set, the digest of
`P`, the message's address, the two cells and the randomizer. -/
theorem sDigest0_sound (h : AtomsHold rd σ (sDigest0 88)) :
    LoadHolds rd (σ sSigner) 2 (σ (.n 91)) ∧ LoadHolds rd (σ sSigner) 3 (σ (.n 92)) ∧
      PadOK σ sLxPad ∧ σ (.n 90) = σ (sHis 0) + word (tw 12) 0 ∧
      σ (.n 103) = (hcell [σ sLxPP, σ (.n 90), σ (.n 91), σ (.n 92), σ (.n 88)]).1 := by
  have ld2 := h.atom (a := .load (.n 91) sSigner 2) (by simp [sDigest0, loadS])
  have ld3 := h.atom (a := .load (.n 92) sSigner 3) (by simp [sDigest0, loadS])
  have ad := h.atom (a := .add (.n 90) (sHis 0) (.n 89)) (by simp [sDigest0, addS])
  have c89 := h.atom (a := .const (.n 89) (word (tw 12) 0)) (by simp [sDigest0, cst])
  have cp := h.atom (a := .copy (.n 93) (.n 88)) (by simp [sDigest0, copyS])
  have c94 := h.atom (a := .const (.n 94) (word 1 0)) (by simp [sDigest0, cst])
  have c95 := h.atom (a := .const (.n 95) (word 0 0)) (by simp [sDigest0, cst])
  have c96 := h.atom (a := .const (.n 96) (word 0 0)) (by simp [sDigest0, cst])
  have c97 := h.atom (a := .const (.n 97) (word (2 ^ 63) 0)) (by simp [sDigest0, cst])
  have p0 : σ (.n 98) = word (if 0 = 0 then 1 else 0) 0 := h.atom (sDigest0_pad 88 0 (by norm_num))
  have p1 : σ (.n 99) = word (if 1 = 0 then 1 else 0) 0 := h.atom (sDigest0_pad 88 1 (by norm_num))
  have p2 : σ (.n 100) = word (if 2 = 0 then 1 else 0) 0 := h.atom (sDigest0_pad 88 2 (by norm_num))
  have p3 : σ (.n 101) = word (if 3 = 0 then 1 else 0) 0 := h.atom (sDigest0_pad 88 3 (by norm_num))
  have p4 : σ (.n 102) = word (if 4 = 0 then 1 else 0) 0 := h.atom (sDigest0_pad 88 4 (by norm_num))
  simp only [Atom.Holds, word_zero] at ad c89 cp c94 c95 c96 c97
  simp only [↓reduceIte, word_zero, one_ne_zero, OfNat.ofNat_ne_zero] at p0 p1 p2 p3 p4
  refine ⟨ld2, ld3, ⟨p0, p1, p2, p3, p4⟩, by rw [ad, c89], ?_⟩
  have hk : AtomsHold rd σ [kecS [sLxPP, .n 90, .n 91, .n 92, .n 93, .n 94, .n 95, .n 96, .n 97,
      .n 99, .n 100, .n 101, .n 102] (runV 103 1) false false] :=
    h.sub fun x hx => by
      simp only [List.mem_singleton] at hx
      subst hx
      simp [sDigest0]
  have := kec80_sound hk c94 c95 c96 c97 p1 p2 p3 p4
  rw [← cp]
  exact this

theorem sDigest1_atoms (b : Nat) (root : V) : atomsOnly (sDigest1 b root) = true := rfl

/-- **The top layer's index and digest**: the digest of `P`, the message's address, the bottom root
and the randomizer. -/
theorem sDigest1_sound {b : Nat} {root : V} (hpad : PadOK σ sLxPad) (h : AtomsHold rd σ (sDigest1 b root)) :
    σ (.n (b + 1)) = σ (sHis 2) + word lxTop 0 ∧
      σ (.n (b + 4)) = σ (.n (b + 1)) + word (tw 12) 0 ∧
      σ (.n (b + 6)) = (hcell [σ sLxPP, σ (.n (b + 4)), σ root, σ (.n (b + 2))]).1 := by
  have c0 : σ (.n b) = word lxTop 0 := h.atom (a := .const (.n b) (word lxTop 0)) (by simp [sDigest1, cst])
  have a1 : σ (.n (b + 1)) = σ (sHis 2) + σ (.n b) :=
    h.atom (a := .add (.n (b + 1)) (sHis 2) (.n b)) (by simp [sDigest1, addS])
  have c3 : σ (.n (b + 3)) = word (tw 12) 0 :=
    h.atom (a := .const (.n (b + 3)) (word (tw 12) 0)) (by simp [sDigest1, cst])
  have a4 : σ (.n (b + 4)) = σ (.n (b + 1)) + σ (.n (b + 3)) :=
    h.atom (a := .add (.n (b + 4)) (.n (b + 1)) (.n (b + 3))) (by simp [sDigest1, addS])
  have hk : AtomsHold rd σ (k64 sLxPad sLxPP (.n (b + 4)) root (.n (b + 2)) (b + 5) (b + 6)) :=
    h.sub fun x hx => by simp only [sDigest1, List.mem_append]; exact Or.inr hx
  exact ⟨by rw [a1, c0], by rw [a4, c3], k64_sound hpad hk⟩

/-! ## A layer -/

theorem sStep_sound (hpad : PadOK σ sLxPad) (layer b : Nat) :
    StepSound rd σ (sW layer b)
      (fun i s y => (hcell [σ sLxPP, σ (.n (sA layer b + 2 * s + 1)), y, σ (sTag i)]).1) := by
  intro i s v c o h
  exact k64_sound hpad h

theorem sCodewordT_tips (W : WotsT) (target : E) (d0 : V) (dg : Nat) :
    (sCodewordT W target d0 dg).2.2 = (List.range 58).map (sTip W (dg + 70)) := by
  have hgs := sGroupsT_eq W dg (dg + 70) 15 0
  simp only [Nat.zero_add] at hgs
  have hgs' : (sGroupsT W dg 15 0 (.n 0) (.n 0) (dg + 70)).2 = _ := hgs
  unfold sCodewordT
  simp only
  rw [hgs']
  rfl

theorem sLeafK_atoms (layer b : Nat) : atomsOnly (sLeafK layer b).1 = true := kMsg_atoms ..

theorem sLayer_split (layer b : Nat) (root : V) : (sLayer layer b root).1 =
    (if layer = 0 then sDigest0 b else sDigest1 b root) ++ (xStepAddrs (sLxIdx layer b) (sA layer b) ++
      ((sCw layer b).1 ++ ([cst (sCw layer b).2.1 (word (tw 2) 0),
        addS (.n ((sCw layer b).2.1 + 1)) (sLxIdx layer b) (.n (sCw layer b).2.1)] ++
        ((sLeafK layer b).1 ++ ((sWin0 layer b).1 ++ (sWin1 layer b).1))))) := by
  simp only [sLayer, List.append_assoc]

theorem sLayer_snd (layer b : Nat) (root : V) :
    (sLayer layer b root).2 = ((sWin1 layer b).2.1, .n (sWin1 layer b).2.2) := by
  simp only [sLayer]

/-- What a window establishes: its arm below `256` and its pin. -/
def WinOK (σ : Val) (w : Nat) : Prop := sKw σ w < 256 ∧ LxPin σ w (sKw σ w)

/-- **A layer after its digest, sound**: the rest holds, each window took an arm and pinned its
shift, and, once the leaf index `L` is known from the four pins (the shifts its words, the windows
its windows) and the chain indices held, `layerRoot` of the part the frame holds over the message
reaches the root the second window reaches. -/
theorem sLayerCore_sound (hpad : PadOK σ sLxPad) (hpow : ∀ s < 13, σ (sPower s) = gen ^ s)
    {layer b : Nat} (hl : layer < 2) {rest : List Stmt} {next : Prop}
    (h : Stmt.HoldsList C rd σ (xStepAddrs (sLxIdx layer b) (sA layer b) ++ ((sCw layer b).1 ++
      ([cst (sCw layer b).2.1 (word (tw 2) 0), addS (.n ((sCw layer b).2.1 + 1)) (sLxIdx layer b)
        (.n (sCw layer b).2.1)] ++ ((sLeafK layer b).1 ++ ((sWin0 layer b).1 ++
          ((sWin1 layer b).1 ++ rest)))))) next kret) :
    Stmt.HoldsList C rd σ rest next kret ∧ WinOK σ (2 * layer) ∧ WinOK σ (2 * layer + 1) ∧
      ∀ (L : Nat) (hL : L < 2 ^ 32), σ (sLxIdx layer b) = eOfNat (xIdxNat layer L) →
        (∀ v < 4, σ (sHis v) = eOfNat (L >>> (8 * v))) → (∀ w < 4, sKw σ w = lxWin L w) →
        (∀ i < 58, σ (sTag i) = eOfNat i) →
        ∀ {msgCells : List E} {M : HashSig.HashInput}, M = msgCells.flatMap cellBytes → ∀ {aMsg : E},
        cellBytes aMsg = LeanXmss.tweakBytes
          (.message ⟨layer, hl⟩ (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer, hl⟩)) →
        σ (sD0 layer b) = (hcell (σ sLxPP :: aMsg :: msgCells ++ [σ (sRho layer b)])).1 →
        @LeanXmss.Verification.layerRootWithHash Id _ ⟨Node.keccakBits⟩ (xpp (σ sLxPP)) ⟨layer, hl⟩
          (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer, hl⟩) M (sPart layer b σ) =
          some (xv (σ (.n (sWin1 layer b).2.2))) := by
  have s1 := holdsList_split_atoms (xs := xStepAddrs (sLxIdx layer b) (sA layer b))
    (xStepAddrs_atoms _ _) h
  have hsteps := xStepAddrs_sound (atomsHold_of_holdsList (xStepAddrs_atoms _ _) s1.1)
  obtain ⟨s2, htips, hsum, hd⟩ := sCodewordT_sound (W := sW layer b) (fun _ _ _ _ _ => rfl)
    (sStep_sound hpad layer b) hpow (target := xTarget) (d0 := sD0 layer b) (dg := sA layer b + 6) s1.2
  have s3 := holdsList_split_atoms (xs := [cst (sCw layer b).2.1 (word (tw 2) 0),
      addS (.n ((sCw layer b).2.1 + 1)) (sLxIdx layer b) (.n (sCw layer b).2.1)])
    (atomsOnly_cst_addS _ _ _ _ _) s2
  have hla := atomsHold_of_holdsList (atomsOnly_cst_addS _ _ _ _ _) s3.1
  have e1 : σ (.n (sCw layer b).2.1) = word (tw 2) 0 := hla.atom (List.mem_cons_self ..)
  have e2 : σ (.n ((sCw layer b).2.1 + 1)) = σ (sLxIdx layer b) + σ (.n (sCw layer b).2.1) :=
    hla.atom (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have s4 := holdsList_split_atoms (xs := (sLeafK layer b).1) (sLeafK_atoms layer b) s3.2
  have hlk := atomsHold_of_holdsList (sLeafK_atoms layer b) s4.1
  obtain ⟨s5, k0, hk0, hx0, hpin0, hout0⟩ := lxWindowT_sound (w := 2 * layer)
    (cur := .n (sLeafK layer b).2.2) (b := (sLeafK layer b).2.1) hpad s4.2
  obtain ⟨s6, k1, hk1, hx1, hpin1, hout1⟩ := lxWindowT_sound (w := 2 * layer + 1)
    (cur := .n (sWin0 layer b).2.2) (b := (sWin0 layer b).2.1) hpad s5
  have ek0 : sKw σ (2 * layer) = k0 := logG_eq hk0 (by norm_num) hx0
  have ek1 : sKw σ (2 * layer + 1) = k1 := logG_eq hk1 (by norm_num) hx1
  subst ek0 ek1
  refine ⟨s6, ⟨hk0, hpin0⟩, ⟨hk1, hpin1⟩, ?_⟩
  intro L hL hidx hhis hwk htag msgCells M hM aMsg haMsg hd0
  -- the values
  set key := LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer, hl⟩ with hkey
  set W := sW layer b with hW
  set dg := sA layer b + 6 with hdg
  set dig := lxDigit (sK σ dg) with hdig
  have hdig4 : ∀ j, dig j < 4 := fun j => lxDigit_lt _ j
  have hsum' : ∑ i ∈ Finset.range 58, dig i = 106 := by
    have h106 : gen ^ (∑ i ∈ Finset.range 58, dig i) = gen ^ 106 := by rw [hsum, xTarget_eq]
    have hle : ∑ i ∈ Finset.range 58, dig i ≤ ∑ _i ∈ Finset.range 58, 3 :=
      Finset.sum_le_sum fun j _ => by have := hdig4 j; omega
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hle
    exact Value.gen_pow_inj (by omega) (by norm_num) h106
  -- the addresses
  have hadr : ∀ st : HashSig.ChainStep, cellBytes (σ (.n (sA layer b + 2 * st.val + 1))) =
      LeanXmss.tweakBytes (.chain ⟨layer, hl⟩ key st) := by
    intro st
    rw [hsteps st.val st.isLt, hidx]
    exact xStepAdr_bytes hL hl st.isLt
  have haLeaf : cellBytes (σ (.n ((sCw layer b).2.1 + 1))) =
      LeanXmss.tweakBytes (.leaf ⟨layer, hl⟩ key) := by
    rw [e2, e1, hidx]
    exact xLeafAdr_bytes hL hl
  -- the leaf
  have htipsL : (sCw layer b).2.2 = (List.range 58).map (sTip W (dg + 70)) := sCodewordT_tips ..
  have hcells : ((sLeafCells layer b).map KC.cell).map (KC.val σ) =
      σ sLxPP :: σ (.n ((sCw layer b).2.1 + 1)) :: (List.range 58).map (fun i => σ (sTip W (dg + 70) i)) := by
    simp only [sLeafCells, List.map_cons, List.map_map]
    rw [htipsL]
    simp [KC.val]
  have hleaf := kMsg_sound (out := none) hpad (by simp) hlk (by
    rw [List.length_map, sLeafCells, List.length_cons, List.length_cons, htipsL, List.length_map,
      List.length_range]) (fun j hj => by
      rw [hcells]
      exact cellsBytes_getD_past (by simp; omega))
  rw [hcells, List.take_of_length_le (by rw [length_cellsBytes]; simp)] at hleaf
  have hlo := hleaf
  -- the Spec
  rw [layerRoot_id, otsLeaf_id]
  have hmd : @LeanXmss.Verification.messageDigestWithHash Id _ ⟨Node.keccakBits⟩ (xpp (σ sLxPP))
      ⟨layer, hl⟩ key M (sPart layer b σ).randomizer = xv (lit (∑ j ∈ Finset.range 58, dig j * 4 ^ j)) := by
    rw [show (sPart layer b σ).randomizer = xv (σ (sRho layer b)) from rfl,
      messageDigest_cells xq_keccak haMsg hM, ← hd0, hd]
  rw [hmd, show (58 : Nat) = LeanXmss.chainCount from rfl, decode_lit hdig4 hsum', Option.map_some]
  refine congrArg some ?_
  have hrc : ∀ i : LeanXmss.ChainIndex, @LeanXmss.Verification.recoverChainWithHash Id _ ⟨Node.keccakBits⟩
      (xpp (σ sLxPP)) ⟨layer, hl⟩ key i ⟨dig i.val, hdig4 _⟩ ((sPart layer b σ).chainValues i) =
      xv (σ (sTip W (dg + 70) i.val)) := by
    intro i
    rw [show (sPart layer b σ).chainValues i = xv (σ (sStart W σ dg (dg + 70) i.val)) from rfl,
      recoverChain_cells xq_keccak (pp := σ sLxPP) (adr := fun s => σ (.n (sA layer b + 2 * s + 1))) hadr]
    rw [htips i.val i.isLt, chainT_eq_xChain' (fun s y => by rw [htag i.val i.isLt])]
  rw [show (fun i : LeanXmss.ChainIndex => @LeanXmss.Verification.recoverChainWithHash Id _
      ⟨Node.keccakBits⟩ (xpp (σ sLxPP)) ⟨layer, hl⟩ key i ⟨dig i.val, hdig4 _⟩
        ((sPart layer b σ).chainValues i)) = fun i => xv (σ (sTip W (dg + 70) i.val)) from funext hrc]
  have hlo' : σ (.n (sLeafK layer b).2.2) = (hcell (σ sLxPP :: σ (.n ((sCw layer b).2.1 + 1)) ::
      List.map (fun i => σ (sTip W (dg + 70) i)) (List.range LeanXmss.chainCount))).1 := hlo
  rw [leafHash_cells xq_keccak (fun i => σ (sTip W (dg + 70) i)) haLeaf, ← hlo']
  beta_reduce
  -- the path
  have hA : ∀ l < LeanXmss.layerHeight, cellBytes (lxNodeAddr L (2 * layer + l / 8) (l % 8)) =
      LeanXmss.tweakBytes (.node ⟨layer, hl⟩ (l + 1) (key.val / 2 ^ (l + 1))) := by
    intro l hl16
    have hl16' : l < 16 := by simpa [LeanXmss.layerHeight] using hl16
    rw [lxNodeAddr_eq hl16']
    exact xNodeAdr_bytes hL hl hl16'
  rw [show (sPart layer b σ).authenticationPath = fun l => xv (sSibAt σ layer b l.val) from rfl,
    treeFold_cells xq_keccak hA (sSibAt σ layer b) LeanXmss.layerHeight le_rfl]
  refine congrArg xv ?_
  have hout0' : σ (.n (sWin0 layer b).2.2) = mFold (σ sLxPP) (lxAtF σ (2 * layer) (sKw σ (2 * layer)))
      (lxBitF (sKw σ (2 * layer))) (lxSibF σ (2 * layer) (lxArmB (2 * layer) 0 (sKw σ (2 * layer))
        ((sLeafK layer b).2.1 + 5))) 8 0 (σ (.n (sLeafK layer b).2.2)) := hout0
  have hout1' : σ (.n (sWin1 layer b).2.2) = mFold (σ sLxPP)
      (lxAtF σ (2 * layer + 1) (sKw σ (2 * layer + 1))) (lxBitF (sKw σ (2 * layer + 1)))
      (lxSibF σ (2 * layer + 1) (lxArmB (2 * layer + 1) 0 (sKw σ (2 * layer + 1))
        ((sWin0 layer b).2.1 + 5))) 8 0 (σ (.n (sWin0 layer b).2.2)) := hout1
  rw [hout1', hout0']
  have hpw : ∀ r < 8, σ (sPower (7 - r)) = eOfNat (2 ^ (7 - r)) := fun r _ => by
    rw [hpow _ (by omega), Value.gen_pow_eq_eOfNat (by omega)]
  have hkey' : key.val = L >>> (16 * layer) := keyAt_val L hL layer hl
  have win : ∀ (j : Nat), j < 2 → ∀ l < 8,
      lxNodeAddr L (2 * layer + (l + 8 * j) / 8) ((l + 8 * j) % 8) = lxAtF σ (2 * layer + j) (sKw σ (2 * layer + j)) l ∧
      key.val.testBit (l + 8 * j) = lxBitF (sKw σ (2 * layer + j)) l := by
    intro j hj l hl8
    have ew : (l + 8 * j) / 8 = j := by omega
    have er : (l + 8 * j) % 8 = l := by omega
    rw [ew, er, hwk _ (by omega)]
    refine ⟨?_, ?_⟩
    · unfold lxAtF
      rw [hpw l hl8]
      exact (lx_at hL hhis (by omega) hl8).symm
    · rw [hkey', Nat.testBit_shiftRight, lxBitF]
      have hb := lx_bit L (2 * layer + j) l hl8
      rw [show 8 * (2 * layer + j) + l = 16 * layer + (l + 8 * j) by ring] at hb
      by_cases ht : L.testBit (16 * layer + (l + 8 * j)) = true
      · rw [ht]; exact (decide_eq_true (hb.mpr ht)).symm
      · rw [Bool.not_eq_true] at ht
        rw [ht]
        exact (decide_eq_false fun h => by rw [hb.mp h] at ht; exact Bool.noConfusion ht).symm
  rw [show LeanXmss.layerHeight = 16 from rfl]
  refine xFold_two (fun l hl8 => ?_) (fun l hl8 => ?_) _
  · obtain ⟨a, bt⟩ := win 0 (by omega) l hl8
    simp only [Nat.mul_zero, Nat.add_zero] at a bt
    exact ⟨a, bt, by simp [sSibAt, hl8]⟩
  · obtain ⟨a, bt⟩ := win 1 (by omega) l hl8
    simp only [Nat.mul_one] at a bt
    exact ⟨a, bt, by simp [sSibAt, show ¬ (l + 8 < 8) by omega]⟩

/-! ## The check -/

theorem sTag_eq (σ : Val) (i : Nat) :
    σ (sTag i) = lxTagOf (σ (.n (sLxPad + 1))) (fun s => σ (sPower s)) (fun j => σ (sTagParam j)) i := by
  unfold sTag lxTagOf
  split_ifs <;> rfl

/-- **The leanXMSS check of `main_loop2` is sound**, for the signature its valuation holds. -/
theorem verify_lean_xmss_sound_holds : verify_lean_xmss_sound_Spec xmssSigOf := by
  intro C rd σ rest next kret h
  simp only [xSeg, List.append_assoc] at h
  -- the prologue
  have s0 := holdsList_split_atoms sPrologue_atoms h
  obtain ⟨hld1, hpow⟩ := sPrologue_sound (atomsHold_of_holdsList sPrologue_atoms s0.1)
  -- the bottom layer
  have s1 := s0.2
  rw [sLayer_split 0 88 (.n 0)] at s1
  simp only [↓reduceIte, List.append_assoc] at s1
  have s2 := holdsList_split_atoms (sDigest0_atoms 88) s1
  obtain ⟨hld2, hld3, hpad, h90, h103⟩ := sDigest0_sound (atomsHold_of_holdsList (sDigest0_atoms 88) s2.1)
  have c0 := sLayerCore_sound (layer := 0) (b := 88) hpad hpow (by norm_num) s2.2
  -- the top layer
  have s3 := c0.1
  rw [sLayer_split 1 (sLayer 0 88 (.n 0)).2.1 (sLayer 0 88 (.n 0)).2.2] at s3
  simp only [one_ne_zero, ↓reduceIte, List.append_assoc] at s3
  have s4 := holdsList_split_atoms (sDigest1_atoms _ _) s3
  obtain ⟨h1, h4, h6⟩ := sDigest1_sound hpad (atomsHold_of_holdsList (sDigest1_atoms _ _) s4.1)
  have c1 := sLayerCore_sound (layer := 1) hpad hpow (by norm_num) s4.2
  -- the root
  have s5 := holdsList_split_atoms (xs := [loadS (.n (sLayer 1 (sLayer 0 88 (.n 0)).2.1
      (sLayer 0 88 (.n 0)).2.2).2.1) sSigner 0, .atom (.assertEq (sLayer 1 (sLayer 0 88 (.n 0)).2.1
      (sLayer 0 88 (.n 0)).2.2).2.2 (.n (sLayer 1 (sLayer 0 88 (.n 0)).2.1 (sLayer 0 88 (.n 0)).2.2).2.1))])
    rfl c1.1
  refine ⟨s5.2, fun htags => ?_⟩
  have hend := atomsHold_of_holdsList (ss := [loadS _ sSigner 0, .atom (.assertEq _ _)]) rfl s5.1
  have hld0 := hend.atom (List.mem_cons_self ..)
  have hroot := hend.atom (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  simp only [Atom.Holds] at hroot
  rw [sLayer_snd] at hld0 hroot
  rw [e_add_eq_zero_iff] at hroot
  -- the index
  set K := sKw σ with hK
  have hk : ∀ w < 4, K w < 256 := fun w _ => sKw_lt σ w
  set L := lxIndex K with hLdef
  have hL : L < 2 ^ 32 := lxIndex_lt hk
  have p0 : LxPin σ 0 (K 0) := c0.2.1.2
  have p1 : LxPin σ 1 (K 1) := c0.2.2.1.2
  have p2 : LxPin σ 2 (K 2) := c1.2.1.2
  have p3 : LxPin σ 3 (K 3) := c1.2.2.1.2
  have hp8 : σ (sPower 8) = eOfNat (2 ^ 8) := by
    rw [hpow 8 (by norm_num), Value.gen_pow_eq_eOfNat (by norm_num)]
  have hhis : ∀ w < 4, σ (sHis w) = eOfNat (L >>> (8 * w)) := lx_his (h := fun w => σ (sHis w)) hk
    (by rw [p3]; rfl) (fun w hw => by
      have hp : LxPin σ w (K w) := by interval_cases w; exacts [p0, p1, p2]
      rw [hp]; simp only [show ¬ (w + 1 = 4) by omega, ↓reduceIte, hp8])
  have hwk : ∀ w < 4, sKw σ w = lxWin L w := fun w hw => (lxWin_lxIndex hk hw).symm
  have htag : ∀ i < 58, σ (sTag i) = eOfNat i := fun i hi => by
    rw [sTag_eq σ i]
    exact lx_tag hpad.2.1 (fun s hs => hpow s (by omega)) htags i hi
  -- the bottom layer's root
  have hidx0 : σ (sLxIdx 0 88) = eOfNat (xIdxNat 0 L) := by
    rw [xIdxNat_zero, show sLxIdx 0 88 = sHis 0 from rfl, hhis 0 (by norm_num)]
    rfl
  have hM0 : HashSig.littleEndianBytes 32 (cellPairVal (σ (.n 91)) (σ (.n 92))) =
      [σ (.n 91), σ (.n 92)].flatMap cellBytes := by
    rw [bytesLE_cellPairVal]; simp
  have haMsg0 : cellBytes (σ (.n 90)) = LeanXmss.tweakBytes
      (.message ⟨0, by decide⟩ (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨0, by decide⟩)) := by
    rw [h90, show σ (sHis 0) = eOfNat (xIdxNat 0 L) from hidx0]
    exact xMsgAdr_bytes hL (by norm_num)
  have r0 := c0.2.2.2 L hL hidx0 hhis hwk htag hM0 haMsg0 h103
  -- the top layer's root
  have hidx1 : σ (sLxIdx 1 (sLayer 0 88 (.n 0)).2.1) = eOfNat (xIdxNat 1 L) := by
    rw [show sLxIdx 1 (sLayer 0 88 (.n 0)).2.1 = .n ((sLayer 0 88 (.n 0)).2.1 + 1) from rfl, h1,
      hhis 2 (by norm_num), xIdxNat_one hL]
  have hM1 : HashSig.littleEndianBytes 16 (xv (σ (sLayer 0 88 (.n 0)).2.2)) =
      [σ (sLayer 0 88 (.n 0)).2.2].flatMap cellBytes := by
    rw [bytesLE_xv]; simp
  have haMsg1 : cellBytes (σ (.n ((sLayer 0 88 (.n 0)).2.1 + 4))) = LeanXmss.tweakBytes
      (.message ⟨1, by decide⟩ (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨1, by decide⟩)) := by
    rw [h4, show σ (.n ((sLayer 0 88 (.n 0)).2.1 + 1)) = eOfNat (xIdxNat 1 L) from hidx1]
    exact xMsgAdr_bytes hL (by norm_num)
  have r1 := c1.2.2.2 L hL hidx1 hhis hwk htag hM1 haMsg1 h6
  -- the claim
  refine ⟨σ (.n (sWin1 1 (sLayer 0 88 (.n 0)).2.1).2.1), σ sLxPP, σ (.n 91), σ (.n 92),
    ⟨hld0, hld1, hld2, hld3⟩, ?_⟩
  have lb : (xmssSigOf σ).layers LeanXmss.bottomLayer = sPart 0 88 σ := by simp [xmssSigOf]
  have lt : (xmssSigOf σ).layers LeanXmss.topLayer = sPart 1 (sLayer 0 88 (.n 0)).2.1 σ := by
    simp [xmssSigOf, LeanXmss.topLayer, LeanXmss.bottomLayer]
  rw [xmssVerify_iff]
  refine ⟨xv (σ (sLayer 0 88 (.n 0)).2.2), ?_, ?_⟩
  · rw [lb, sLayer_snd]
    exact r0
  · rw [lt, ← hroot]
    exact r1

end
end LeanVM.Guest.B1.Sig
