/-
  LeanVM.Guest.B1.Sig.SphincsTailComplete

  The one-time leaf and the tree of `verify_sig_lean_sphincs` are complete: over an encoding
  digest that decodes, from any chain values and siblings, the root is the tree's fold over the
  leaf of the recovered chains.
-/

module

public import LeanVM.Guest.B1.Sig.Sphincs
public import LeanVM.Guest.B1.Sig.SphincsBody
public import LeanVM.Guest.B1.Sig.XmssComplete

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader} {inst : HasQuery Sphincs.HashSpec Id}

/-- The leanSPHINCS one-time key's chains. -/
def spW : Wots := ⟨.n 1, .n 2, false, fun _ => .n 0, .n 142⟩

/-- The codeword from base `e`, over the powers at `e + 7` and the digest at `e + 5`. -/
def sCw (e : Nat) : List Stmt × Nat × List (V × V) :=
  cCodeword spW (fun s => .n (e + 7 + s)) 21 sTarget (.n (e + 5)) (e + 17)

/-- The one-time leaf from base `e`. -/
def sLeaf (e : Nat) : List Stmt × V :=
  hashValues (.n 1) (.n ((sCw e).2.1 + 1)) (fun i => ((sCw e).2.2.getD i (.n 0, .n 0)).1) 64 ((sCw e).2.1 + 2)

/-- The tree from base `e`. -/
def sMk (e : Nat) : List Stmt × V × Nat :=
  merkle (.n 1) (fun l => .n (19 + l)) (fun l => .n (142 - 3 * l)) (fun l => tw 3 + (l + 1) * hiMul)
    (fun l => l + 1 == 26) 26 0 (sLeaf e).2 ((sCw e).2.1 + 2 + hashValuesSize 64)

/-- The powers, the codeword, the leaf and the tree. -/
def sTail (e : Nat) : List Stmt :=
  powers (e + 7) ++ ((sCw e).1 ++ ([cst (sCw e).2.1 (word (tw 2) 0 0), addS (.n ((sCw e).2.1 + 1)) (.n 142)
    (.n (sCw e).2.1)] ++ ((sLeaf e).1 ++ (sMk e).1)))

theorem sBody_split : sBody =
    sPrologue ++ ((sCoords 8 0 (.n 209) 210).1 ++ (sLanes (fun k => (((sCoords 8 0 (.n 209) 210).2.2.1.getD (k / 2)
      (.n 0, .n 0)) |> fun p => if k % 2 = 0 then p.1 else p.2)) (sCoords 8 0 (.n 209) 210).2.2.2.2
      (sCoords 8 0 (.n 209) 210).2.1 ++
    ([cst ((sCoords 8 0 (.n 209) 210).2.1 + 45) (word (tw 20) 0 0),
      addS (.n ((sCoords 8 0 (.n 209) 210).2.1 + 45 + 1)) (.n 142) (.n ((sCoords 8 0 (.n 209) 210).2.1 + 45))] ++
    ((hashValues (.n 1) (.n ((sCoords 8 0 (.n 209) 210).2.1 + 45 + 1))
      (fun k => (((sCoords 8 0 (.n 209) 210).2.2.2.1.getD (k / 2) (.n 0, .n 0)) |>
        fun p => if k % 2 = 0 then p.1 else p.2)) 16 ((sCoords 8 0 (.n 209) 210).2.1 + 45 + 2)).1 ++
    (sCounter (hashValues (.n 1) (.n ((sCoords 8 0 (.n 209) 210).2.1 + 45 + 1))
      (fun k => (((sCoords 8 0 (.n 209) 210).2.2.2.1.getD (k / 2) (.n 0, .n 0)) |>
        fun p => if k % 2 = 0 then p.1 else p.2)) 16 ((sCoords 8 0 (.n 209) 210).2.1 + 45 + 2)).2
      ((sCoords 8 0 (.n 209) 210).2.1 + 45 + 2 + hashValuesSize 16) ++
    (sTail ((sCoords 8 0 (.n 209) 210).2.1 + 45 + 2 + hashValuesSize 16 + 126) ++
    [.atom (.load (.n (sMk ((sCoords 8 0 (.n 209) 210).2.1 + 45 + 2 + hashValuesSize 16 + 126)).2.2) (.n 0) 0),
      .atom (.assertEq (sMk ((sCoords 8 0 (.n 209) 210).2.1 + 45 + 2 + hashValuesSize 16 + 126)).2.1
        (.n (sMk ((sCoords 8 0 (.n 209) 210).2.1 + 45 + 2 + hashValuesSize 16 + 126)).2.2))])))))) ++
    [.ret []] := by
  simp only [sBody, sTail, sMk, sLeaf, sCw, spW, List.append_assoc, List.cons_append, List.nil_append]

theorem sMk_ge (e : Nat) : e + 7 ≤ (sMk e).2.2 := by
  have hc := cCodeword_snd_gt spW (fun s => .n (e + 7 + s)) 21 sTarget (.n (e + 5)) (e + 17)
  have hmkge := merkle_snd_ge (.n 1) (fun l => .n (19 + l)) (fun l => .n (142 - 3 * l))
    (fun l => tw 3 + (l + 1) * hiMul) (fun l => l + 1 == 26) 26 0 (sLeaf e).2 ((sCw e).2.1 + 2 + hashValuesSize 64)
  show e + 7 ≤ (merkle _ _ _ _ _ 26 0 (sLeaf e).2 ((sCw e).2.1 + 2 + hashValuesSize 64)).2.2
  simp only [sCw] at hmkge ⊢
  omega

theorem sMk_root_lt (e : Nat) : NB (sMk e).2.2 (sMk e).2.1 :=
  merkle_snd_lt _ _ _ _ _ 26 0 _ _ (hashValues_snd_lt _ _ _ _ _)

theorem sPowers_below (b : Nat) : NumBelow (b + 10) (Stmt.valsList (powers b)) := by
  simp only [powers, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.cons_append,
    List.nil_append, List.append_nil]
  repeat (first | exact .nil _ | refine .cons ⟨_, by omega, rfl⟩ ?_)

theorem sTail_below {e : Nat} (he : 143 ≤ e) : NumBelow (sMk e).2.2 (Stmt.valsList (sTail e)) := by
  have hc := cCodeword_snd_gt spW (fun s => .n (e + 7 + s)) 21 sTarget (.n (e + 5)) (e + 17)
  have htipB := cCodeword_tips_lt spW (fun s => .n (e + 7 + s)) 21 sTarget (.n (e + 5)) (e + 17)
  have hmkge := merkle_snd_ge (.n 1) (fun l => .n (19 + l)) (fun l => .n (142 - 3 * l))
    (fun l => tw 3 + (l + 1) * hiMul) (fun l => l + 1 == 26) 26 0 (sLeaf e).2 ((sCw e).2.1 + 2 + hashValuesSize 64)
  rw [show cCodeword spW (fun s => .n (e + 7 + s)) 21 sTarget (.n (e + 5)) (e + 17) = sCw e from rfl] at hc htipB
  rw [show merkle (.n 1) (fun l => .n (19 + l)) (fun l => .n (142 - 3 * l)) (fun l => tw 3 + (l + 1) * hiMul)
    (fun l => l + 1 == 26) 26 0 (sLeaf e).2 ((sCw e).2.1 + 2 + hashValuesSize 64) = sMk e from rfl] at hmkge
  have hcwge : e + 17 ≤ (sCw e).2.1 := by omega
  have hwB : spW.Below (e + 17) := ⟨⟨1, by omega, rfl⟩, ⟨2, by omega, rfl⟩, fun _ => ⟨0, by omega, rfl⟩,
    ⟨142, by omega, rfl⟩⟩
  have hpwB : ∀ s < 10, NB (e + 17) (V.n (e + 7 + s)) := fun s hs => ⟨_, by omega, rfl⟩
  simp only [sTail, valsList_append]
  refine ((sPowers_below (e + 7)).mono (by omega)).append
    (((show NumBelow (sCw e).2.1 (Stmt.valsList (sCw e).1) from
      cCodeword_below (by norm_num) (by omega) hwB hpwB ⟨e + 5, by omega, rfl⟩).mono
      (by omega)).append ?_)
  refine NumBelow.append ?_ (NumBelow.append ?_ ?_)
  · simp only [cst, addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.cons_append, List.nil_append,
      List.append_nil]
    repeat (first | exact .nil _ | (refine .cons ⟨_, ?_, rfl⟩ ?_; omega))
  · exact (hashValues_below (by norm_num) ⟨⟨1, by omega, rfl⟩, ⟨_, by omega, rfl⟩,
      fun i hi => (htipB i hi).mono (by omega)⟩).mono hmkge
  · exact merkle_below 26 0 _ _ ⟨1, by omega, rfl⟩ (hashValues_snd_lt _ _ _ _ _)
      fun l' _ hl' => ⟨⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩

/-- A decoded encoding digest's digits. -/
theorem sDecode_some {d : Sphincs.Digest} {enc : Sphincs.Encoding} (h : Sphincs.TargetSum.decodeDigest d = some enc) :
    (∀ i : Sphincs.ChainIndex, (enc i).val = d.toNat / 4 ^ i.val % 4) ∧
      ∑ i ∈ Finset.range Sphincs.numChains, d.toNat / 4 ^ i % 4 = Sphincs.targetSum ∧
      d.toNat = ∑ j ∈ Finset.range Sphincs.numChains, d.toNat / 4 ^ j % 4 * 4 ^ j := by
  simp only [Sphincs.TargetSum.decodeDigest] at h
  split at h
  next hv =>
    cases h
    have hdig : ∀ i : Sphincs.ChainIndex, (Sphincs.TargetSum.digestEncoding d i).val = d.toNat / 4 ^ i.val % 4 :=
      fun i => by
        show (BitVec.extractLsb' (2 * i.val) 2 d).toNat = _
        rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_mul]
        norm_num
    refine ⟨hdig, ?_, ?_⟩
    · rw [← hv, Sphincs.TargetSum.sum, ← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun i _ => (hdig i).symm
    · have hlt : d.toNat < 4 ^ Sphincs.numChains := by
        have := d.isLt
        norm_num [Sphincs.numChains, Sphincs.digestBits] at this ⊢
        omega
      exact (base4_expand _ _ hlt).symm
  next => cases h

/-- **The tail is complete**: over an encoding digest at `e + 5` that decodes, from any chain
values and siblings, the root is the tree's fold over the leaf of the recovered chains. -/
theorem sTail_complete (hq : SQ inst) (hrd : MemOK rd 64) {σ : Val} {N U e : Nat} (he : 210 ≤ e)
    (hpre : SPre σ N U) (hidx : σ (.n 142) = eOfNat N) (hpp : IsCanonical128 (σ (.n 1)))
    {leaf : Sphincs.LeafIndex} (hleaf : leaf.val = N) {enc : Sphincs.Encoding}
    (hdec : Sphincs.TargetSum.decodeDigest (sv (σ (.n (e + 5)))) = some enc) (hd0c : IsCanonical128 (σ (.n (e + 5))))
    {vals sibs : Nat → E} (hvals : ∀ i, IsCanonical128 (vals i)) (hsibs : ∀ l, IsCanonical128 (sibs l)) :
    Completes C rd (e + 7) (sMk e).2.2 (sTail e) σ (fun σ' =>
      @Sphincs.Concrete.treeFold Id _ inst (spp (σ (.n 1))) Sphincs.topLayer 0 leaf (fun l => sv (sibs l))
        Sphincs.maxLayerHeight
        (@Sphincs.Concrete.leafHash Id _ inst (spp (σ (.n 1))) Sphincs.topLayer 0 leaf fun i =>
          @Sphincs.Concrete.recoverChain Id _ inst (spp (σ (.n 1))) Sphincs.topLayer 0 leaf i (enc i)
            (sv (vals i.val))) =
        sv (σ' (sMk e).2.1) ∧ IsCanonical128 (σ' (sMk e).2.1) ∧ AgreeBelow (e + 7) σ σ') := by
  have hN := hpre.ltN
  obtain ⟨henc, hsum, hval⟩ := sDecode_some hdec
  set dig : Nat → Nat := fun i => (sv (σ (.n (e + 5)))).toNat / 4 ^ i % 4 with hdig_def
  have hdig : ∀ i, dig i < 4 := fun i => Nat.mod_lt _ (by norm_num)
  have hc := cCodeword_snd_gt spW (fun s => .n (e + 7 + s)) 21 sTarget (.n (e + 5)) (e + 17)
  have htipB := cCodeword_tips_lt spW (fun s => .n (e + 7 + s)) 21 sTarget (.n (e + 5)) (e + 17)
  rw [show cCodeword spW (fun s => .n (e + 7 + s)) 21 sTarget (.n (e + 5)) (e + 17) = sCw e from rfl] at hc htipB
  have hmkge := merkle_snd_ge (.n 1) (fun l => .n (19 + l)) (fun l => .n (142 - 3 * l))
    (fun l => tw 3 + (l + 1) * hiMul) (fun l => l + 1 == 26) 26 0 (sLeaf e).2 ((sCw e).2.1 + 2 + hashValuesSize 64)
  rw [show merkle (.n 1) (fun l => .n (19 + l)) (fun l => .n (142 - 3 * l)) (fun l => tw 3 + (l + 1) * hiMul)
    (fun l => l + 1 == 26) 26 0 (sLeaf e).2 ((sCw e).2.1 + 2 + hashValuesSize 64) = sMk e from rfl] at hmkge
  have hleafB : NB ((sCw e).2.1 + 2 + hashValuesSize 64) (sLeaf e).2 := hashValues_snd_lt _ _ _ _ _
  have hwB : spW.Below (e + 17) := ⟨⟨1, by omega, rfl⟩, ⟨2, by omega, rfl⟩, fun _ => ⟨0, by omega, rfl⟩,
    ⟨142, by omega, rfl⟩⟩
  have hpwB : ∀ s < 10, NB (e + 17) (V.n (e + 7 + s)) := fun s hs => ⟨_, by omega, rfl⟩
  simp only [sTail]
  set c := (sCw e).2.1
  set tip : Nat → V := fun i => ((sCw e).2.2.getD i (.n 0, .n 0)).1
  -- the powers
  refine Completes.append (m := e + 17) (by omega) (by omega) (sPowers_below (e + 7)) (powers_complete (e + 7))
    fun σ1 _ ⟨hp1, hag1⟩ => ?_
  have h1 : ∀ k < e + 7, σ1 (.n k) = σ (.n k) := fun k hk => (hag1 k hk).symm
  -- the codeword
  have hcan1 : spW.Canon σ1 := ⟨by show IsCanonical128 (σ1 (.n 1)); rw [h1 1 (by omega)]; exact hpp,
    fun h => absurd h Bool.false_ne_true,
    fun _ => by show IsCanonical128 (σ1 (.n 142)); rw [h1 142 (by omega), hidx]; exact isCanonical128_eOfNat _⟩
  have hcomp := cCodeword_complete (C := C) (w := spW) (power := fun s => .n (e + 7 + s)) hrd (G := 21)
    (by norm_num) (target := sTarget) (d0 := .n (e + 5)) (b := e + 17) (σ := σ1) (by omega) hwB hpwB
    ⟨e + 5, by omega, rfl⟩ (by show σ1 (.n 2) = mdw 48 true; rw [h1 2 (by omega)]; exact hpre.md48) hcan1
    hp1 (dig := dig) hdig (xs := vals) hvals
    (by rw [sTarget_eq]; exact congrArg (gen ^ ·) hsum.symm)
    (by rw [h1 _ (by omega), ← cellOf_cellVal hd0c, ← lit_toNat (cellVal (σ (.n (e + 5))))]; exact congrArg lit hval)
  refine Completes.append (m := c) (by omega) (by omega)
    (show NumBelow (sCw e).2.1 (Stmt.valsList (sCw e).1) from
      cCodeword_below (by norm_num) (by omega) hwB hpwB ⟨e + 5, by omega, rfl⟩) hcomp.withExt
    fun σ2 _ ⟨hT2, he2'⟩ => ?_
  have h2 : ∀ k < e + 17, σ2 (.n k) = σ1 (.n k) := fun k hk => (he2'.agree k hk).symm
  have hp2 : σ2 (.n 1) = σ (.n 1) := by rw [h2 1 (by omega), h1 1 (by omega)]
  have hidx2 : σ2 (.n 142) = eOfNat N := by rw [h2 142 (by omega), h1 142 (by omega), hidx]
  -- the leaf address
  set A0 := word (tw 2) 0 0
  have ne : ∀ i j : Nat, i ≠ j → (V.n i) ≠ V.n j := fun i j h e => h (by cases e; rfl)
  refine Completes.append (m := c + 2) (by omega) (by omega)
    (show NumBelow (c + 2) (Stmt.valsList [cst c A0, addS (.n (c + 1)) (.n 142) (.n c)]) from
      .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
        (.nil _)))))
    (P := fun σ' => σ' (.n (c + 1)) = σ2 (.n 142) + A0 ∧ AgreeBelow c σ2 σ')
    (Completes.atom_cons A0 (by omega) (.cons ⟨_, by omega, rfl⟩ (.nil _)) (Function.update_self _ _ _)
      (Completes.atom_cons (σ2 (.n 142) + A0) (by omega)
        (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))))
        (by
          show Function.update (Function.update σ2 (.n c) A0) (.n (c + 1)) (σ2 (.n 142) + A0) (.n (c + 1)) =
            Function.update (Function.update σ2 (.n c) A0) (.n (c + 1)) (σ2 (.n 142) + A0) (.n 142) +
            Function.update (Function.update σ2 (.n c) A0) (.n (c + 1)) (σ2 (.n 142) + A0) (.n c)
          have h1 : 142 ≠ c := by omega
          have h2 : 142 ≠ c + 1 := by omega
          simp [h1, h2])
        (Completes.nil _ _ _ ⟨Function.update_self _ _ _, fun k hk => by
          rw [Function.update_of_ne (ne _ _ (by omega)), Function.update_of_ne (ne _ _ (by omega))]⟩)))
    fun σ3 _ ⟨hA3, hag3⟩ => ?_
  have h3 : ∀ k < c, σ3 (.n k) = σ2 (.n k) := fun k hk => (hag3 k hk).symm
  have hp3 : σ3 (.n 1) = σ (.n 1) := by rw [h3 1 (by omega), hp2]
  have htip3 : ∀ i < 64, σ3 (tip i) = (tipPair false (σ (.n 1)) (fun _ => σ2 (.n 0)) (eOfNat N) i (dig i)
      (vals i)).1 := fun i hi => by
    obtain ⟨k, hk, e⟩ := htipB i hi
    have := (hT2 i hi).1
    simp only [tip] at e ⊢
    rw [e, h3 k hk, ← e]
    refine this.trans ?_
    show (tipPair false (σ2 (.n 1)) (fun _ => σ2 (.n 0)) (σ2 (.n 142)) i (dig i) (vals i)).1 = _
    rw [hp2, hidx2]
  have hcanT : ∀ i < 64, IsCanonical128 (σ3 (tip i)) := fun i hi => by
    rw [htip3 i hi]; exact canonical_tipPair _ _ _ _ _ _ (hvals i)
  -- the leaf
  have hv : Completes C rd (c + 2) (c + 2 + hashValuesSize 64) (sLeaf e).1 σ3
      (fun σ' => σ' (sLeaf e).2 = (hcell (σ3 (.n 1) :: σ3 (.n (c + 1)) :: (List.range 64).map fun i => σ3 (tip i))).1) :=
    hashValues_complete (Or.inl (by norm_num)) (by norm_num)
      ⟨⟨1, by omega, rfl⟩, ⟨c + 1, by omega, rfl⟩, fun i hi => (htipB i hi).mono (by omega)⟩
      ⟨by rw [hp3]; exact hpp,
        by rw [hA3, hidx2]; exact isCanonical128_add (isCanonical128_eOfNat _) (isCanonical128_word _ _), hcanT⟩
  refine Completes.append (m := c + 2 + hashValuesSize 64) (by omega) (by omega)
    (hashValues_below (by norm_num) ⟨⟨1, by omega, rfl⟩, ⟨c + 1, by omega, rfl⟩,
      fun i hi => (htipB i hi).mono (by omega)⟩) hv.withExt fun σ4 _ ⟨hleaf4, he4'⟩ => ?_
  have hσ4 : ∀ k < e + 7, σ4 (.n k) = σ (.n k) := fun k hk => by
    rw [← he4'.agree k (by omega), h3 k (by omega), h2 k (by omega), h1 k hk]
  have hleafc : IsCanonical128 (σ4 (sLeaf e).2) := by rw [hleaf4]; exact (isCanonical128_hb _).1
  have hnode4 : ∀ l, l + 1 < 26 → σ4 (.n (142 - 3 * (l + 1))) = eOfNat (N / 2 ^ (l + 1)) := fun l hl => by
    rw [hσ4 _ (by omega)]; exact hpre.nodes (l + 1) hl
  -- the tree
  have hmk := merkle_complete (C := C) (rd := rd) (pp := .n 1) (bit := fun l => .n (19 + l))
    (node := fun l => .n (142 - 3 * l)) (addr := fun l => tw 3 + (l + 1) * hiMul) (isEnd := fun l => l + 1 == 26)
    (β := fun l => N.testBit l) (sibs := sibs)
    26 0 _ _ σ4 ⟨1, by omega, rfl⟩ hleafB
      (fun l' _ hl' => ⟨⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩)
      (fun l' _ hl' => ⟨by
          show σ4 (.n (19 + l')) = _
          rw [hσ4 _ (by omega)]; exact hpre.bits l' (by omega),
        hsibs l', by
          unfold mAddr
          split
          · exact isCanonical128_word _ _
          · rename_i hne
            rw [hnode4 l' (by simp only [beq_iff_eq] at hne; omega)]
            exact isCanonical128_add (isCanonical128_word _ _) (isCanonical128_eOfNat _)⟩)
      (by rw [hσ4 1 (by omega)]; exact hpp) hleafc
  rw [show merkle (.n 1) (fun l => .n (19 + l)) (fun l => .n (142 - 3 * l)) (fun l => tw 3 + (l + 1) * hiMul)
    (fun l => l + 1 == 26) 26 0 (sLeaf e).2 (c + 2 + hashValuesSize 64) = sMk e from rfl] at hmk
  refine hmk.withExt.mono le_rfl le_rfl fun σ5 ⟨hroot5, he5⟩ => ⟨?_, ?_, fun k hk => ?_⟩
  · have hchains : (fun i : Sphincs.ChainIndex => @Sphincs.Concrete.recoverChain Id _ inst (spp (σ (.n 1)))
        Sphincs.topLayer 0 leaf i (enc i) (sv (vals i.val))) = fun i => sv (σ3 (tip i.val)) := by
      funext i
      rw [show enc i = ⟨dig i.val, hdig _⟩ from Fin.ext (henc i),
        sRecoverChain_cells (idx := eOfNat N) hq (fun s => sp_chain_addr hN i s leaf hleaf), htip3 i.val i.isLt]
      exact congrArg (fun p => sv p.1) (tipPair_sp _ _ _ _ _ _ _)
    have hleafAdr : cellBytes (σ3 (.n (c + 1))) = Sphincs.tweakBytes (.leaf Sphincs.topLayer 0 leaf) := by
      rw [hA3, hidx2, sp_tag_addr hN (by norm_num), ← hleaf, ← sTweak]
      rfl
    have hA : ∀ l < Sphincs.maxLayerHeight, cellBytes (mAddr σ4 (fun l => .n (142 - 3 * l))
        (fun l => tw 3 + (l + 1) * hiMul) (fun l => l + 1 == 26) l) =
        Sphincs.tweakBytes (.node Sphincs.topLayer 0 (l + 1) (leaf.val / 2 ^ (l + 1))) := fun l hl => by
      rw [hleaf]
      exact sp_node_addr hN hl (hnode4 l)
    rw [hchains, sLeafHash_cells hq (fun i => σ3 (tip i)) hleafAdr, sTreeFold_cells hq hA sibs _ le_rfl, hroot5,
      hleaf4, hσ4 1 (by omega), hp3, hleaf]
    rfl
  · rw [hroot5]; exact mFold_canonical _ _ _ _ _ _ _ (Or.inl (by norm_num))
  · rw [← he5.agree k (by omega), hσ4 k hk]

end
end LeanVM.Guest.B1.Sig
