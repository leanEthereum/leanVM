/-
  LeanVM.Guest.B1.Sig.XmssSigPops

  The witness-stream entries leanXMSS's check inline in `main_loop2` pops are the honest hint generator's pushes for the signature (`Hints.xmssHints`), stream by stream.
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegPops
public import LeanVM.Guest.B1.Sig.XmssPathPops

/-!
# A leanXMSS signature's pops are its hints

* `xmssLayer_fst`, `xmssLayer_snd`: a layer's pushes are its siblings', then its randomizer's, its digit words' (`lxK` of its digest) and its starts'; the root it passes up is `xRootOf`;
* `xLayerPops_sameStreams`: a layer's pops are its pushes, the siblings moved after the rest;
* `xSegPops_sameStreams`: the check's pops are `xmssHints`';
* `verify_lean_xmss_complete_pops`: `verify_lean_xmss` completes popping, on every valuation agreeing below its end, entries that are `xmssHints pk m sig`, stream by stream.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Memory LeanVM.Protocol.Verifier
open EthLib.Cryptography

@[expose] public section

/-! ## Lists -/

theorem map_finRange_val {α : Type} (n : Nat) (f : Nat → α) :
    (List.finRange n).map (fun i => f i.val) = (List.range n).map f :=
  List.ext_getElem (by simp) (fun _ _ _ => by simp)

theorem flatten_map_singleton {α β : Type} (l : List α) (f : α → β) : (l.map fun i => [f i]).flatten = l.map f := by
  induction l <;> simp_all

theorem take_drop_map_range (d : Nat → Nat) (a j n : Nat) :
    (((List.range n).map d).drop a).take j = (List.range' a (min j (n - a))).map d := by
  have ht : ∀ m, List.take j (List.range' a m) = List.range' a (min j m) := fun m =>
    List.ext_getElem (by simp) (fun _ _ _ => by simp [List.getElem_range'])
  rw [← List.map_drop, List.range_eq_range', List.drop_range', Nat.zero_add, Nat.mul_one, ← List.map_take, ht]

theorem foldr_digits (N : Nat) : ∀ j a, ((List.range' a j).map fun i => N / 4 ^ i % 4).foldr (· + 4 * ·) 0 =
    N / 4 ^ a % 4 ^ j
  | 0, a => by simp [Nat.mod_one]
  | j + 1, a => by
      rw [List.range'_succ, List.map_cons, List.foldr_cons, foldr_digits N j (a + 1),
        show N / 4 ^ (a + 1) = N / 4 ^ a / 4 by rw [pow_succ, Nat.div_div_eq_div_mul],
        show (4 : Nat) ^ (j + 1) = 4 * 4 ^ j from pow_succ' 4 j, Nat.mod_mul]

theorem count_eq {n : Nat} (_h : n < 2 ^ 64) : Hints.count n = ofK (addressOfIndex n) := by
  rw [Hints.count, LeanVM.Protocol.Verifier.gpow, gen_pow_eq_ofK]

/-- **A digest's digit words**: its base-4 digits four at a time, in the exponent, are the groups
`lxK` of its number. -/
theorem digitHints_lx (D : EthLib.Cryptography.Hash.Keccak.Lanes2) :
    (Hints.digitHints Hints.lxDigitGroup ((List.range Xmss.Constants.V).map fun i =>
      if h : i < Xmss.Constants.DIGITS then (Xmss.Internal.digit D ⟨i, h⟩).val else 0)).flatten =
      (List.range 15).map fun q => ofK (addressOfIndex (lxK D.toNat q)) := by
  have hd : ((List.range Xmss.Constants.V).map fun i =>
      if h : i < Xmss.Constants.DIGITS then (Xmss.Internal.digit D ⟨i, h⟩).val else 0) =
      (List.range 58).map fun i => D.toNat / 4 ^ i % 4 := by
    refine List.map_congr_left fun i hi => ?_
    have hi' : i < Xmss.Constants.DIGITS := by
      have := List.mem_range.mp hi
      rw [Xmss.Constants.digits_eq]
      simp only [Xmss.Constants.V] at this
      omega
    simp only [hi', ↓reduceDIte]
    exact Xmss.digit_val D ⟨i, hi'⟩
  rw [hd, Hints.digitHints, flatten_map_singleton]
  simp only [List.length_map, List.length_range, Hints.lxDigitGroup]
  refine List.map_congr_left fun q hq => ?_
  have hq' : q < 15 := List.mem_range.mp hq
  have hn : min 4 (58 - 4 * q) = lxN q := by unfold lxN; split <;> omega
  rw [take_drop_map_range, foldr_digits, hn]
  exact count_eq (lt_of_lt_of_le (lxK_lt _ q) (by unfold lxN; split <;> norm_num))

/-! ## A layer -/

theorem cellOfLanes_eq (w : EthLib.Cryptography.Hash.Keccak.Lanes2) : Hints.cellOfLanes w = xc w
    := by
  conv_lhs => rw [← xl_xc w]
  rw [Hints.cellOfLanes, bytes_xl, cellOfBytes_cellBytes]

/-- **A layer's pushes**: its siblings, then its randomizer, its digit words and its starts. -/
theorem xmssLayer_fst (P : EthLib.Cryptography.Hash.Keccak.Lanes2) (lay : Xmss.Layer) (key : Nat)
    (M : Array UInt64) (part : Xmss.LayerSignature) :
    (Hints.xmssLayer P lay key M part).1 = lxPathPops 16 (xSibs part) ++
      (("randomizer", [xc part.randomizer]) ::
        ("lx_digits", (List.range 15).map fun q =>
          ofK (addressOfIndex (lxK (xDigestN P lay key M part) q))) ::
          (List.range 58).map fun i => startPop (xVals part i)) := by
  have hs : part.path.toList.map (fun sibling => (("lx_path" : String),
      [Hints.cellOfLanes sibling])) = lxPathPops 16 (xSibs part) := by
    refine List.ext_getElem (by simp [lxPathPops]; rfl) fun i h1 h2 => ?_
    have hi : i < 16 := by simpa [lxPathPops] using h2
    simp only [List.getElem_map, Vector.getElem_toList, lxPathPops, List.getElem_range, xSibs, hi,
      dite_true]
    exact congrArg (fun c => (("lx_path" : String), [c])) (cellOfLanes_eq _)
  have hst : part.chainValues.toList.map (fun value => (("chain_starts" : String),
      [Hints.cellOfLanes value])) = (List.range 58).map fun i => startPop (xVals part i) := by
    refine List.ext_getElem (by simp; rfl) fun i h1 h2 => ?_
    have hi : i < 58 := by simpa using h2
    simp only [List.getElem_map, Vector.getElem_toList, List.getElem_range, xVals, hi, dite_true]
    exact congrArg (fun c => (("chain_starts" : String), [c])) (cellOfLanes_eq _)
  simp only [Hints.xmssLayer]
  rw [hs, hst, digitHints_lx, cellOfLanes_eq, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  rfl

/-- The root a layer passes up is `xRootOf`. -/
theorem xmssLayer_snd (P : EthLib.Cryptography.Hash.Keccak.Lanes2) (lay : Xmss.Layer) (key : Nat)
    (M : Array UInt64) (part : Xmss.LayerSignature) :
    (Hints.xmssLayer P lay key M part).2 = xRootOf P lay key M part := rfl

/-- **A layer pops its pushes**, stream by stream. -/
theorem xLayerPops_sameStreams (P : EthLib.Cryptography.Hash.Keccak.Lanes2) (lay : Xmss.Layer)
    (key : Nat) (M : Array UInt64) (part : Xmss.LayerSignature) :
    SameStreams (xLayerPops part (xDigestN P lay key M part)) (Hints.xmssLayer P lay key M part).1 := by
  have e : xLayerPops part (xDigestN P lay key M part) = (("randomizer", [xc part.randomizer]) ::
      ("lx_digits", (List.range 15).map fun q =>
        ofK (addressOfIndex (lxK (xDigestN P lay key M part) q))) ::
        (List.range 58).map fun i => startPop (xVals part i)) ++ lxPathPops 16 (xSibs part) := rfl
  rw [xmssLayer_fst, e]
  refine sameStreams_append_comm fun p hp q hq => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_cons, List.mem_map] at hp
  rcases hp with rfl | rfl | ⟨i, -, rfl⟩
  · exact (by decide : ("randomizer" : String) ≠ "lx_path")
  · exact (by decide : ("lx_digits" : String) ≠ "lx_path")
  · exact (by decide : ("chain_starts" : String) ≠ "lx_path")

/-! ## The signature -/

theorem xN1_eq (pk : Xmss.PublicKey) (m : HashSig.Message) (sig : Xmss.Signature) :
    xN1 pk m sig = xDigestN pk.publicParam .top (Xmss.bottomTree sig.leafIndex)
      (xRootOf pk.publicParam .bottom sig.leafIndex.toNat (LeanXmss.lanesOfBits m).toArray
        sig.bottom).toArray sig.top := by
  unfold xN1
  rw [shift_eq_bottomTree]

theorem xmssHints_eq (pk : Xmss.PublicKey) (m : HashSig.Message) (sig : Xmss.Signature) :
    Hints.xmssHints pk m sig =
      ("lx_index", ((List.range 4).map fun v => sig.leafIndex.toNat / 2 ^ (8 * v)).map
          fun x => word x 0) ::
        ("lx_windows", ((List.range 4).map fun v => sig.leafIndex.toNat / 2 ^ (8 * v)).map
          fun x => Hints.count (x % 2 ^ 8)) ::
        ((Hints.xmssLayer pk.publicParam .bottom sig.leafIndex.toNat
            (LeanXmss.lanesOfBits m).toArray sig.bottom).1 ++
          (Hints.xmssLayer pk.publicParam .top (Xmss.bottomTree sig.leafIndex)
            (Hints.xmssLayer pk.publicParam .bottom sig.leafIndex.toNat
              (LeanXmss.lanesOfBits m).toArray sig.bottom).2.toArray sig.top).1) :=
  rfl

/-- **The check's pops are `xmssHints`'**, stream by stream. -/
theorem xSegPops_sameStreams (pk : Xmss.PublicKey) (m : HashSig.Message) (sig : Xmss.Signature) :
    SameStreams (xSegPops pk m sig) (Hints.xmssHints pk m sig) := by
  have hi : ((List.range 4).map fun v => sig.leafIndex.toNat / 2 ^ (8 * v)).map (fun x => word x 0)
      =
      (List.range 4).map fun v => eOfNat (sig.leafIndex.toNat >>> (8 * v)) := by
    rw [List.map_map]
    exact List.map_congr_left fun v _ => by
      simp only [Function.comp_apply, word_eq_eOfNat, Nat.shiftRight_eq_div_pow]
  have hw : ((List.range 4).map fun v => sig.leafIndex.toNat / 2 ^ (8 * v)).map
      (fun x => Hints.count (x % 2 ^ 8)) =
      (List.range 4).map fun w => ofK (addressOfIndex (lxWin sig.leafIndex.toNat w)) := by
    rw [List.map_map]
    exact List.map_congr_left fun w _ => by
      simp only [Function.comp_apply, lxWin, Nat.shiftRight_eq_div_pow]
      exact count_eq (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))
  rw [xmssHints_eq, xmssLayer_snd, hi, hw]
  unfold xSegPops
  rw [xN1_eq]
  exact SameStreams.append (a := [_, _]) (b := [_, _]) (fun _ => rfl)
    ((xLayerPops_sameStreams _ _ _ _ _).append (xLayerPops_sameStreams _ _ _ _ _))

/-- **`verify_lean_xmss` completes popping its hints**: on every valuation agreeing below its end with the completing one, the check pops `xSegPops`, which are `xmssHints pk m sig`, stream by stream. -/
theorem verify_lean_xmss_complete_pops (C : CallRel) (rd : Reader) (σ : Val) (pk : Xmss.PublicKey)
    (m : HashSig.Message) (sig : Xmss.Signature) (hm : MemOK rd 256)
    (htags : LxTagsHold (fun j => σ (sTagParam j)))
    (hat : ClaimAt rd (σ sSigner) (xc pk.root) (xc pk.publicParam)
      (cellOf128 (m.extractLsb' 0 128)) (cellOf128 (m.extractLsb' 128 128)))
    (hv : LeanXmss.verifyWithKeccak pk (LeanXmss.lanesOfBits m) sig = true) :
    Completes C rd 66 (xEnd + 1) xSeg σ (fun σ' => ∀ σ'', AgreeBelow (xEnd + 1) σ' σ'' →
      FallPops rd σ'' xSeg (xSegPops pk m sig) ∧ SameStreams (xSegPops pk m sig) (Hints.xmssHints pk m sig)) :=
  (verify_lean_xmss_complete_pops_of lxWindowsC C rd σ pk m sig hm htags hat hv).mono le_rfl le_rfl
    fun _ h σ'' hag => ⟨h σ'' hag, xSegPops_sameStreams pk m sig⟩

end
end LeanVM.Guest.B1.Sig
