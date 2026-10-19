/-
  LeanVM.Guest.B1.Sig.Sphincs

  `verify_sig_lean_sphincs` (G:2525-2656) is sound: when it holds of a claim, some signature
  verifies the claim's message under its key.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsBody
public import LeanVM.Guest.B1.Sig.Xmss

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1.Sig

@[expose] public section

/-- **`verify_sig_lean_sphincs(claim)`**: the claim at the pointer is a leanSPHINCS key and a
message that some signature verifies under BLAKE2s. -/
def Meaning_verify_sig_lean_sphincs (rd : Reader) (args rets : List E) : Prop :=
  ∃ p, args = [p] ∧ rets = [] ∧ ∃ (pk : Sphincs.PublicKey) (m : Sphincs.Message),
    ClaimAt rd p (claimCells pk.root pk.parameter m) ∧ ∃ σ, Node.sphincsVerify pk m σ = true

namespace Sig

variable {C : CallRel} {rd : Reader}

theorem sTarget_eq : sTarget = gen ^ 120 := by
  rw [gen_pow_gpowK (by decide), sTarget, word_eq_eOfNat, eOfNat]
  exact congrArg ofK (by decide +kernel)

/-- A leanSPHINCS step does not read the step addresses. -/
theorem chainFrom_sp (pp : E) (adr adr' : Nat → E) (idx : E) (i : Nat) :
    ∀ m s v, chainFrom false pp adr idx i m s v = chainFrom false pp adr' idx i m s v
  | 0, _, _ => rfl
  | m + 1, s, v => by simp only [chainFrom, stepCells]; exact chainFrom_sp pp adr adr' idx i m _ _

theorem tipPair_sp (pp : E) (adr adr' : Nat → E) (idx : E) (i d : Nat) (x : E) :
    tipPair false pp adr idx i d x = tipPair false pp adr' idx i d x := by
  simp only [tipPair]; split <;> simp only [chainFrom_sp pp adr adr']

theorem digestMarks_super_val (D : Sphincs.MessageDigest) (c : Sphincs.Coord) :
    ((Sphincs.Concrete.digestMarks D c).super).val =
      (D.extractLsb' (Sphincs.Concrete.superOffset c) Sphincs.topHeight).toNat := rfl

theorem digestMarks_child_val (D : Sphincs.MessageDigest) (c : Sphincs.Coord) (j : Sphincs.SubIdx) :
    ((Sphincs.Concrete.digestMarks D c).child j).val =
      (D.extractLsb' (Sphincs.Concrete.childOffset c j) Sphincs.subHeight).toNat := rfl

theorem digestMarks_word_val (D : Sphincs.MessageDigest) (c : Sphincs.Coord) (j : Sphincs.SubIdx) :
    ((Sphincs.Concrete.digestMarks D c).word j).val = (D.extractLsb' (Sphincs.Concrete.wordOffset c j) 8).toNat := rfl

theorem sv_zero : sv 0 = (0 : Sphincs.Digest) := by
  show cellVal 0 = (0 : BitVec 128)
  apply BitVec.eq_of_toNat_eq
  rw [toNat_cellVal, cellNat, zero_eq_ofLimbs, ofLimbs_limb0, ofLimbs_limb1, kToNat_zero]
  rfl

theorem bytesLE_counter {Cn : Nat} (h : Cn < 2 ^ 32) :
    Sphincs.bytesLE 4 (BitVec.ofNat Sphincs.counterBits Cn) = leBytes Cn 4 := by
  show Sphincs.bytesLE 4 (BitVec.ofNat (8 * 4) Cn) = _
  rw [sphincs_bytesLE_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- A one-time chain step's address. -/
theorem sp_chain_addr {N : Nat} (hN : N < 2 ^ 26) (i : Sphincs.ChainIndex) (s : Sphincs.ChainStep)
    (leaf : Sphincs.LeafIndex) (hl : leaf.val = N) :
    cellBytes (eOfNat N + eOfNat (tw 1 + i.val * hiMul + s.val * stepMul)) =
      Sphincs.tweakBytes (.chain Sphincs.topLayer 0 leaf i s) := by
  have hi : i.val < 64 := i.isLt
  have hs : s.val < 3 := s.isLt
  rw [show tw 1 + i.val * hiMul + s.val * stepMul = 2 ^ 32 * (i.val + 2 ^ 24 * (1 + 32 * s.val)) by
      simp only [tw, hiMul, stepMul]; ring, sp_add_eOfNat (by omega),
    show Sphincs.tweakBytes (.chain Sphincs.topLayer 0 leaf i s) =
      cellBytes (eOfNat (addrNat 1 s.val i.val leaf.val)) by rw [← sTweak]; rfl]
  congr 2
  rw [sp_addrNat (by omega) (by omega) (by omega) (by omega), hl]
  ring

/-- An address with only a type and the instance. -/
theorem sp_tag_addr {N : Nat} (hN : N < 2 ^ 26) {tag : Nat} (ht : tag < 32) :
    cellBytes (eOfNat N + word (tw tag) 0 0) = cellBytes (eOfNat (addrNat tag 0 0 N)) := by
  rw [show tw tag = 2 ^ 56 * tag by simp only [tw]; ring, sp_add_word (by omega)]
  congr 2
  rw [sp_addrNat (by omega) (by omega) ht (by omega)]
  ring

/-- A node address of the tree. -/
theorem sp_node_addr {σ : Val} {N l : Nat} (hN : N < 2 ^ 26) (hl : l < Sphincs.maxLayerHeight)
    (hnode : l + 1 < 26 → σ (.n (142 - 3 * (l + 1))) = eOfNat (N / 2 ^ (l + 1))) :
    cellBytes (mAddr σ (fun l => .n (142 - 3 * l)) (fun l => tw 3 + (l + 1) * hiMul) (fun l => l + 1 == 26) l) =
      Sphincs.tweakBytes (.node Sphincs.topLayer 0 (l + 1) (N / 2 ^ (l + 1))) := by
  simp only [Sphincs.maxLayerHeight] at hl
  rw [show Sphincs.tweakBytes (.node Sphincs.topLayer 0 (l + 1) (N / 2 ^ (l + 1))) =
    cellBytes (eOfNat (addrNat 3 0 (l + 1) (N / 2 ^ (l + 1)))) by rw [← sTweak]; rfl]
  have hq32 : N / 2 ^ (l + 1) < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  by_cases he : l + 1 = 26
  · have he' : (l + 1 == 26) = true := by simpa using he
    have h0 : N / 2 ^ (l + 1) = 0 := by rw [he]; exact Nat.div_eq_of_lt hN
    simp only [mAddr, he', ↓reduceIte]
    rw [h0, word_eq_eOfNat, sp_addrNat (by omega) (by omega) (by omega) (by omega)]
    exact congrArg (fun n => cellBytes (eOfNat n)) (by simp only [tw, hiMul]; ring)
  · have he' : (l + 1 == 26) = false := by simpa using he
    simp only [mAddr, he', Bool.false_eq_true, ↓reduceIte]
    rw [hnode (by omega), show tw 3 + (l + 1) * hiMul = 2 ^ 32 * (3 * 2 ^ 24 + (l + 1)) by
        simp only [tw, hiMul]; ring, word_add_eOfNat hq32, sp_addrNat hq32 (by omega) (by omega) (by omega)]
    exact congrArg (fun n => cellBytes (eOfNat n)) (by ring)

/-- **`verify_sig_lean_sphincs` is sound.** -/
theorem verify_sig_lean_sphincs_sound (hfk : FkSound C rd) {σ : Val} {rets : List E}
    (h : Stmt.HoldsList C rd σ sBody False (fun rs => rs = rets)) :
    rets = [] ∧ ∃ (pk : Sphincs.PublicKey) (m : Sphincs.Message),
      ClaimAt rd (σ (.n 0)) (claimCells pk.root pk.parameter m) ∧ ∃ sig, Node.sphincsVerify pk m sig = true := by
  suffices H : ∀ inst : HasQuery Sphincs.HashSpec Id, SQ inst → rets = [] ∧ ∃ (pk : Sphincs.PublicKey)
      (m : Sphincs.Message), ClaimAt rd (σ (.n 0)) (claimCells pk.root pk.parameter m) ∧
        ∃ sig, @Sphincs.Concrete.verify Id _ inst pk m sig = true by
    obtain ⟨h1, pk, m, hc, sig, hv⟩ := H ⟨Node.blake2sBits⟩ sq_blake2s
    exact ⟨h1, pk, m, hc, sig, by rw [Node.sphincsVerify.eq_def, idRun]; exact hv⟩
  intro inst hq
  simp only [sBody, holdsList_append] at h
  obtain ⟨hl1, hl5, hl6, hpp, hm0, hm1, hdgst, ⟨N, U, hpre⟩, h⟩ := sPrologue_sound h
  set index : Sphincs.Index := ⟨N, hpre.ltN⟩
  have hidx : σ (.n 142) = eOfNat index.val := by
    have := hpre.nodes 0 (by omega)
    simpa using this
  obtain ⟨⟨marks, openings, hcs, hbound⟩, h⟩ :=
    sCoords_sound (inst := inst) hq hfk hpre.md64 index hidx 8 0 (.n 209) 210 (by omega) h
  generalize sCoords 8 0 (.n 209) 210 = cs at *
  obtain ⟨h17, hb18, h⟩ := sLanes_sound (t := fun k => ((marks (k / 2)).word ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val)
    (fun k _ => ((marks (k / 2)).word _).isLt) (fun k hk => by
      have := hcs (k / 2) (by omega)
      simp only [Nat.zero_add] at this
      rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2
      · simp only [hk2, ↓reduceIte]
        rw [this.2.1, word_eq_eOfNat]
        rfl
      · simp only [hk2, Nat.one_ne_zero, ↓reduceIte]
        rw [this.2.2, word_eq_eOfNat]
        rfl) h
  simp only [Nat.zero_add] at hcs hbound
  simp only [cst, addS, holdsList_cons_atom, holdsList_nil, Atom.Holds] at h
  obtain ⟨hf, hf1, h⟩ := h
  obtain ⟨hfkey, h⟩ := hashValues_sound (Or.inl rfl) (by norm_num) h
  obtain ⟨Cn, hCn, hctr, he1, he5, h⟩ := sCounter_sound h
  rw [powers_iff] at h
  obtain ⟨hpow, h⟩ := h
  obtain ⟨⟨dig, hdig, htips, htarget, hd0⟩, h⟩ :=
    cCodeword_sound (w := ⟨.n 1, .n 2, false, fun _ => .n 0, .n 142⟩) hpre.md48 hpow (G := 21) (by norm_num) h
  obtain ⟨hc, hc1, h⟩ := h
  obtain ⟨hleaf, h⟩ := hashValues_sound (Or.inl rfl) (by norm_num) h
  obtain ⟨⟨sibs, hroot⟩, h⟩ := merkle_sound (β := fun l => N.testBit l) 26 0 _ _
    (fun l' _ hl' => hpre.bits l' (by omega)) h
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_nil] at h
  obtain ⟨hload, heq, hret⟩ := h
  generalize cCodeword ⟨.n 1, .n 2, false, fun _ => .n 0, .n 142⟩ _ 21 sTarget _ _ = cw at *
  generalize hashValues (.n 1) _ _ 64 _ = lf at *
  generalize merkle (.n 1) _ _ _ _ 26 0 lf.2 _ = mk at *
  have hN := hpre.ltN
  -- the digest's cells
  have hs : ∀ c < 8, (marks c).super.val < 2 ^ 4 := fun c _ => (marks c).super.isLt
  have ha : ∀ k < 16, ((marks (k / 2)).child ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val < 2 ^ 3 := fun k _ =>
    ((marks (k / 2)).child _).isLt
  have hV : σ (.n 18) = lit (digestHi N U (fun c => (marks c).super.val)
      (fun k => ((marks (k / 2)).child ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val)) := by
    rw [← hb18, hbound, hpre.bound, ← lit_digestHi hN hs ha]
    refine congrArg (fun x => eOfNat N + lit (U * 2 ^ 106) + x) (Finset.sum_congr rfl fun c _ => ?_)
    simp only [coordWeight, show 2 * c / 2 = c by omega, show (2 * c + 1) / 2 = c by omega,
      show 2 * c % 2 = 0 by omega, show (2 * c + 1) % 2 = 1 by omega]
    rfl
  have hc18 : cellNat (σ (.n 18)) = digestHi N U (fun c => (marks c).super.val)
      (fun k => ((marks (k / 2)).child ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val) := by
    rw [hV, cellNat_lit, Nat.mod_eq_of_lt (digestHi_lt hN hpre.ltU hs ha)]
  have hw : ∀ k < 16, ((marks (k / 2)).word ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val < 2 ^ 8 := fun k _ =>
    ((marks (k / 2)).word _).isLt
  have hc17 : cellNat (σ (.n 17)) = ∑ k ∈ Finset.range 16,
      ((marks (k / 2)).word ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val * 2 ^ (8 * k) := by
    rw [h17, cellNat_lit, Nat.mod_eq_of_lt (baseW_lt 8 16 hw)]
  -- the message digest, its index and its marks
  set m : Sphincs.Message := BitVec.ofNat 256 (cellNat (σ (.n 5)) + 2 ^ 128 * cellNat (σ (.n 6)))
  have hmsg : Sphincs.bytesLE 32 m = cellBytes (σ (.n 5)) ++ cellBytes (σ (.n 6)) := by
    have := bytesLE_message (m := m) (lo_ofNat _ _) (hi_ofNat _ _)
    rw [bytesLE_eq] at this
    rw [sphincs_bytesLE_eq]
    exact this
  have htw12 : cellBytes (word (tw 12) 0 0) = Sphincs.tweakBytes .message := by
    rw [Sphincs.tweakBytes, Sphincs.hashDomainFields, sTweak, word_eq_eOfNat]
    rfl
  have hD : ∀ root : Sphincs.Digest, @Sphincs.Concrete.messageDigest Id _ inst (spp (σ (.n 1))) root m
      (sv (σ (.n 12))) = BitVec.ofNat Sphincs.messageDigestBits (cellNat (σ (.n 17)) + 2 ^ 128 * cellNat (σ (.n 18))) :=
    fun root => by
      rw [sMessageDigest_cells hq htw12 hmsg, ← hdgst]
  have hI : ∀ root : Sphincs.Digest, Sphincs.Concrete.digestIndex
      (@Sphincs.Concrete.messageDigest Id _ inst (spp (σ (.n 1))) root m (sv (σ (.n 12)))) = index :=
    fun root => Fin.ext (by rw [hD, digestIndex_ofNat (cellNat_lt _), hc18, digestHi_index hN])
  have hmk : ∀ x y : Sphincs.CoordMark, x.super = y.super → x.child = y.child → x.word = y.word → x = y := by
    rintro ⟨⟩ ⟨⟩ h1 h2 h3
    simp only at h1 h2 h3
    rw [h1, h2, h3]
  have hM : ∀ root : Sphincs.Digest, Sphincs.Concrete.digestMarks
      (@Sphincs.Concrete.messageDigest Id _ inst (spp (σ (.n 1))) root m (sv (σ (.n 12)))) =
      fun c => marks c.val := fun root => by
    funext c
    have hc8 : c.val < 8 := c.isLt
    refine hmk _ _ (Fin.ext ?_) (funext fun j => Fin.ext ?_) (funext fun j => Fin.ext ?_)
    · rw [digestMarks_super_val, hD, show Sphincs.Concrete.superOffset c = 128 + (26 + 4 * c.val) by
          simp [Sphincs.Concrete.superOffset]; ring,
        digestField_ofNat (cellNat_lt _) (by simp only [Sphincs.topHeight]; omega), hc18]
      exact digestHi_super hN hs hc8
    · have hj : j.val < 2 := j.isLt
      rw [digestMarks_child_val, hD, show Sphincs.Concrete.childOffset c j = 128 + (58 + 3 * (2 * c.val + j.val)) by
          simp [Sphincs.Concrete.childOffset]; ring,
        digestField_ofNat (cellNat_lt _) (by simp only [Sphincs.subHeight]; omega), hc18]
      refine (digestHi_child (k := 2 * c.val + j.val) hN hs ha (by omega)).trans ?_
      simp only [show (2 * c.val + j.val) / 2 = c.val by omega, show (2 * c.val + j.val) % 2 = j.val by omega]
    · have hj : j.val < 2 := j.isLt
      rw [digestMarks_word_val, hD, show Sphincs.Concrete.wordOffset c j = 8 * (2 * c.val + j.val) by
          simp [Sphincs.Concrete.wordOffset],
        digestByte_ofNat (by omega), hc17, baseW_digit 8 16 hw _ (by omega)]
      simp only [show (2 * c.val + j.val) / 2 = c.val by omega, show (2 * c.val + j.val) % 2 = j.val by omega]
  -- the forest key
  have hR : cellBytes (σ (.n (cs.2.1 + 45 + 1))) = Sphincs.tweakBytes (.roots index) := by
    rw [hf1, hf, hidx, show tw 20 = 2 ^ 56 * 20 by simp only [tw]; ring, sp_add_word (by simp [index]; omega),
      Sphincs.tweakBytes, Sphincs.hashDomainFields, sTweak]
    congr 2
    rw [sp_addrNat (by simp [index]; omega) (by omega) (by omega) (by omega)]
    simp [index]
    ring
  have hFK := sForestRecover_cells (inst := inst) hq (marks := fun c => marks c.val)
    (opening := fun c => openings c.val)
    (fun k => σ (if k % 2 = 0 then (cs.2.2.2.1.getD (k / 2) (V.n 0, V.n 0)).1
      else (cs.2.2.2.1.getD (k / 2) (V.n 0, V.n 0)).2)) (fun c => by
        have := (hcs c.val c.isLt).1
        simp only [show 2 * c.val % 2 = 0 by omega, show (2 * c.val + 1) % 2 = 1 by omega,
          show 2 * c.val / 2 = c.val by omega, show (2 * c.val + 1) / 2 = c.val by omega, ↓reduceIte,
          Nat.one_ne_zero]
        exact this) hR
  rw [← hfkey] at hFK
  generalize (hashValues (V.n 1) (V.n (cs.2.1 + 45 + 1)) _ 16 (cs.2.1 + 45 + 2)).2 = fkc at *
  -- the one-time leaf
  obtain ⟨vals, hvals⟩ := exists_fun_of_lt htips
  have hsum : ∑ i ∈ Finset.range Sphincs.numChains, dig i = Sphincs.targetSum := by
    rw [sTarget_eq] at htarget
    have := digit_sum_le hdig (3 * 21 + 1)
    exact (gen_pow_inj (by norm_num) (by omega) htarget).symm
  have hleafIdx : (Sphincs.Concrete.leafIndexAt index Sphincs.topLayer).val = N := leafIndexAt_top index
  have hadr : ∀ (i : Sphincs.ChainIndex) (s : Sphincs.ChainStep),
      cellBytes (σ (.n 142) + eOfNat (tw 1 + i.val * hiMul + s.val * stepMul)) =
        Sphincs.tweakBytes (.chain Sphincs.topLayer 0 (Sphincs.Concrete.leafIndexAt index Sphincs.topLayer) i s) :=
    fun i s => by rw [hidx]; exact sp_chain_addr hN i s _ hleafIdx
  have hrec : ∀ i : Sphincs.ChainIndex, @Sphincs.Concrete.recoverChain Id _ inst (spp (σ (.n 1)))
      Sphincs.topLayer 0 (Sphincs.Concrete.leafIndexAt index Sphincs.topLayer) i ⟨dig i.val, hdig _⟩ (sv (vals i.val)) =
      sv (σ (cw.2.2.getD i.val (V.n 0, V.n 0)).1) := fun i => by
    rw [sRecoverChain_cells hq (hadr i), (hvals i.val i.isLt).1]
    exact congrArg (fun p => sv p.1) (tipPair_sp _ _ _ _ _ _ _)
  have hleafA : cellBytes (σ (.n (cw.2.1 + 1))) =
      Sphincs.tweakBytes (.leaf Sphincs.topLayer 0 (Sphincs.Concrete.leafIndexAt index Sphincs.topLayer)) := by
    rw [hc1, hc, hidx, sp_tag_addr hN (by norm_num), ← hleafIdx]
    rw [← sTweak]; rfl
  have htw4 : Sphincs.tweakBytes (.encoding Sphincs.topLayer 0 (Sphincs.Concrete.leafIndexAt index Sphincs.topLayer)) =
      cellBytes (σ (.n (cs.2.1 + 45 + 2 + hashValuesSize 16 + 126 + 1))) := by
    rw [he1, hidx, sp_tag_addr hN (by norm_num), ← hleafIdx]
    rw [← sTweak]; rfl
  have hots : @Sphincs.Concrete.otsLeaf Id _ inst (spp (σ (.n 1))) Sphincs.topLayer 0
      (Sphincs.Concrete.leafIndexAt index Sphincs.topLayer) (sv (σ fkc)) (BitVec.ofNat Sphincs.counterBits Cn)
      (fun i => sv (vals i.val)) = some (sv (σ lf.2)) := by
    rw [sOtsLeaf_id]
    have henc : @Sphincs.Concrete.tweakableHash Id _ inst (spp (σ (.n 1)))
        (.encoding Sphincs.topLayer 0 (Sphincs.Concrete.leafIndexAt index Sphincs.topLayer))
        (Sphincs.bytesLE 16 (sv (σ fkc)) ++ Sphincs.bytesLE 4 (BitVec.ofNat Sphincs.counterBits Cn)) =
        sv (σ (.n (cs.2.1 + 45 + 2 + hashValuesSize 16 + 126 + 5))) := by
      rw [he5]
      apply sHash_bytes hq
      show Sphincs.bytesLE 16 (spp (σ (.n 1))) ++ Sphincs.tweakBytes _ ++ _ = _
      rw [bytesLE_spp, htw4, bytesLE_sv, bytesLE_counter hCn]
      simp
    rw [henc, hd0, show 3 * 21 + 1 = Sphincs.numChains from rfl, sDecode_lit hdig hsum, Option.map_some]
    refine congrArg some ?_
    rw [show (fun i : Sphincs.ChainIndex => @Sphincs.Concrete.recoverChain Id _ inst (spp (σ (.n 1)))
        Sphincs.topLayer 0 (Sphincs.Concrete.leafIndexAt index Sphincs.topLayer) i ⟨dig i.val, hdig _⟩
        (sv (vals i.val))) = fun i => sv (σ (cw.2.2.getD i.val (V.n 0, V.n 0)).1) from funext hrec,
      sLeafHash_cells hq (fun i => σ (cw.2.2.getD i (V.n 0, V.n 0)).1) hleafA, hleaf]
    rfl
  -- the tree
  have heq' : σ mk.2.1 = σ (.n mk.2.2) := e_add_eq_zero_iff.mp heq
  have hA : ∀ l < Sphincs.maxLayerHeight, cellBytes (mAddr σ (fun l => .n (142 - 3 * l))
      (fun l => tw 3 + (l + 1) * hiMul) (fun l => l + 1 == 26) l) =
      Sphincs.tweakBytes (.node Sphincs.topLayer 0 (l + 1)
        ((Sphincs.Concrete.leafIndexAt index Sphincs.topLayer).val / 2 ^ (l + 1))) := fun l hl => by
    rw [hleafIdx]
    exact sp_node_addr hN hl (fun h => hpre.nodes (l + 1) (by omega))
  let sib' : Nat → E := fun l => if l < 26 then sibs l else 0
  have htree : @Sphincs.Concrete.treeFold Id _ inst (spp (σ (.n 1))) Sphincs.topLayer 0
      (Sphincs.Concrete.leafIndexAt index Sphincs.topLayer) (fun l => sv (sib' l)) Sphincs.maxLayerHeight
      (sv (σ lf.2)) = sv (σ (.n mk.2.2)) := by
    rw [sTreeFold_cells hq hA sib' _ le_rfl, ← heq', hroot]
    refine congrArg sv ?_
    simp only [hleafIdx]
    exact mFold_congr _ _ _ 26 0 (fun l _ hl => by simp [sib', show l < 26 by omega]) _
  -- the claim and the signature
  have hrc : IsCanonical128 (σ (.n mk.2.2)) := by
    rw [← heq', hroot]; exact mFold_canonical _ _ _ _ _ _ _ (Or.inl (by norm_num))
  refine ⟨hret.symm, ⟨sv (σ (.n mk.2.2)), spp (σ (.n 1))⟩, m, ?_, ⟨sv (σ (.n 12)), fun c => openings c.val,
    fun _ => ⟨BitVec.ofNat Sphincs.counterBits Cn, fun i => sv (vals i.val), fun l => sv (sibs l.val)⟩⟩, ?_⟩
  · show ClaimAt rd (σ (.n 0)) (claimCells (xv (σ (.n mk.2.2))) (xpp (σ (.n 1)))
      (BitVec.ofNat 256 (cellNat (σ (.n 5)) + 2 ^ 128 * cellNat (σ (.n 6)))))
    rw [claimCells_of hrc hpp hm0 hm1]
    intro k
    fin_cases k
    · exact hload
    · exact hl1
    · exact hl5
    · exact hl6
  · rw [sVerify_iff]
    refine ⟨sv (σ lf.2), ?_, ?_⟩
    · dsimp only
      rw [hI, hM, hFK]
      exact hots
    · dsimp only
      rw [hI]
      have hsp : Sphincs.Concrete.signaturePath ⟨sv (σ (.n 12)), fun c => openings c.val,
          fun _ => ⟨BitVec.ofNat Sphincs.counterBits Cn, fun i => sv (vals i.val), fun l => sv (sibs l.val)⟩⟩
          Sphincs.topLayer = fun l => sv (sib' l) := funext fun l => by
        simp only [Sphincs.Concrete.signaturePath, Sphincs.layerHeight, Sphincs.maxLayerHeight, sib']
        by_cases hl : l < 26
        · simp only [hl, ↓reduceDIte, ↓reduceIte]
        · simp only [hl, ↓reduceDIte, ↓reduceIte]
          exact sv_zero.symm
      rw [hsp]
      exact htree

end Sig

end
end LeanVM.Guest.B1
