/-
  LeanVM.Guest.B1.Sig.SphincsIff

  `verify_sig_lean_sphincs` is complete: every claim some signature verifies holds; with its
  soundness, its relation is its meaning.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsTailComplete
public import LeanVM.Guest.B1.Sig.SphincsBodyComplete
public import LeanVM.Guest.B1.Sig.SphincsGlue
public import LeanVM.Guest.B1.Sig.XmssIff

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1.Sig

@[expose] public section

namespace Sig

variable {C : CallRel} {rd : Reader}

theorem SPre.congr {σ σ' : Val} {N U : Nat} (h : SPre σ N U) (hag : ∀ k < 210, σ' (.n k) = σ (.n k)) :
    SPre σ' N U :=
  ⟨by rw [hag 2 (by omega)]; exact h.md48, by rw [hag 3 (by omega)]; exact h.md64, h.ltN, h.ltU,
    fun j hj => by rw [hag _ (by omega)]; exact h.bits j hj, fun l hl => by rw [hag _ (by omega)]; exact h.nodes l hl,
    by rw [hag 209 (by omega)]; exact h.bound⟩

theorem holds_of_completes {p : E} {X : List Stmt} {hi : Nat}
    (h : Completes C rd 1 hi X (fun _ => p) (fun _ => True)) :
    ∃ σ : Val, σ (.n 0) = p ∧ Stmt.HoldsList C rd σ (X ++ [.ret []]) False (fun rs => rs = []) := by
  obtain ⟨σ', he, -, hh⟩ := h
  refine ⟨σ', he.apply (Or.inl (by norm_num)), ?_⟩
  have hret : Stmt.HoldsList C rd σ' [.ret []] False (fun rs => rs = []) := by
    simp only [Stmt.HoldsList, Stmt.Holds, List.map_nil]
  rw [holdsList_append]
  exact hh _ _ hret

/-- **`verify_sig_lean_sphincs` is complete**: for a claim at `p` that some signature verifies,
on a memory holding at least 256 words, with the forest keys complete, the body holds from a
valuation with `p` as its argument. -/
theorem verify_sig_lean_sphincs_complete (hfk : FkComplete C) (hrd : MemOK rd 256) {p : E}
    {pk : Sphincs.PublicKey} {m : Sphincs.Message} {sig : Sphincs.Signature}
    (hc : ClaimAt rd p (claimCells pk.root pk.parameter m)) (hv : Node.sphincsVerify pk m sig = true) :
    ∃ σ : Val, σ (.n 0) = p ∧ Stmt.HoldsList C rd σ sBody False (fun rs => rs = []) := by
  have hv' : @Sphincs.Concrete.verify Id _ ⟨Node.blake2sBits⟩ pk m sig = true := by
    rw [Node.sphincsVerify.eq_def, idRun] at hv; exact hv
  generalize hI : (⟨Node.blake2sBits⟩ : HasQuery Sphincs.HashSpec Id) = inst at hv'
  have hq : SQ inst := hI ▸ sq_blake2s
  obtain ⟨lv, hots, htree⟩ := (sVerify_iff pk m sig).mp hv'
  -- the message digest
  set pp := cellOf pk.parameter
  set m0 := cellOf (m.extractLsb' 0 128)
  set m1 := cellOf (m.extractLsb' 128 128)
  set rho := cellOf sig.randomness
  set H := hcell [pp, word (tw 12) 0 0, m0, m1, rho]
  set x0 := cellNat H.1
  set x1 := cellNat H.2
  have hx0 : x0 < 2 ^ 128 := cellNat_lt _
  have hspp : spp pp = pk.parameter := cellVal_cellOf _
  have hsrho : sv rho = sig.randomness := cellVal_cellOf _
  have hmsg : Sphincs.bytesLE 32 m = cellBytes m0 ++ cellBytes m1 := by
    exact (sphincs_bytesLE_eq 32 m).trans ((bytesLE_eq 32 m).symm.trans (message_bytes m))
  have htw12 : cellBytes (word (tw 12) 0 0) = Sphincs.tweakBytes .message := by
    rw [Sphincs.tweakBytes, Sphincs.hashDomainFields, sTweak, word_eq_eOfNat]
    rfl
  have hD : @Sphincs.Concrete.messageDigest Id _ inst pk.parameter pk.root m sig.randomness =
      BitVec.ofNat Sphincs.messageDigestBits (x0 + 2 ^ 128 * x1) := by
    have := sMessageDigest_cells (inst := inst) (pp := pp) (rho := rho) (root := pk.root) hq htw12 hmsg
    rw [hspp, hsrho] at this
    exact this
  rw [hD] at hots htree
  rw [← dMarks_eq x0 x1] at hots
  rw [← hspp] at hots htree
  set N := x1 % 2 ^ 26
  set U := x1 / 2 ^ 106
  set index := Sphincs.Concrete.digestIndex (BitVec.ofNat Sphincs.messageDigestBits (x0 + 2 ^ 128 * x1))
  have hindex : index.val = N := digestIndex_ofNat hx0
  have hN : N < 2 ^ 26 := Nat.mod_lt _ (by positivity)
  have hU : U < 2 ^ 22 := by
    have := cellNat_lt H.2
    exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by norm_num at this ⊢; omega)
  set marks := dMarks x0 x1
  set openings : Nat → Sphincs.CoordOpening := fun r => sig.forest ⟨r % 8, Nat.mod_lt _ (by norm_num)⟩
  have hopen : (fun c : Sphincs.Coord => openings c.val) = sig.forest :=
    funext fun c => congrArg _ (Fin.ext (Nat.mod_eq_of_lt c.isLt))
  rw [← hopen] at hots
  set leaf := Sphincs.Concrete.leafIndexAt index Sphincs.topLayer
  have hleaf : leaf.val = N := (leafIndexAt_top index).trans hindex
  rw [sOtsLeaf_id] at hots
  obtain ⟨enc, hdecE, hlv⟩ := Option.map_eq_some_iff.mp hots
  -- the layout
  rw [sBody_split]
  have hbge := sCoords_snd_ge 8 0 (.n 209) 210
  obtain ⟨hbB, houts⟩ := sCoords_outs_lt 8 0 (.n 209) 210 ⟨209, by omega, rfl⟩
  set cs := sCoords 8 0 (.n 209) 210
  set b := cs.2.1
  have hmkge := sMk_ge (b + 45 + 2 + hashValuesSize 16 + 126)
  have hhv16 : 0 < hashValuesSize 16 := by decide
  -- the prologue
  refine holds_of_completes (hi := (sMk (b + 45 + 2 + hashValuesSize 16 + 126)).2.2 + 1) ?_
  refine Completes.append (m := 210) (by omega) (by omega) sPrologue_below
    (sPrologue_complete (pp := pp) (m0 := m0) (m1 := m1) (rho := rho) (hc 1) (hc 2) (hc 3)
      (isCanonical128_cellOf _) (isCanonical128_cellOf _) (isCanonical128_cellOf _) (isCanonical128_cellOf _)
      hN hU) fun σ1 _ ⟨hpre1, hp1, _, _, _, hH1, hag1⟩ => ?_
  have h01 : σ1 (.n 0) = p := (hag1 0 (by omega)).symm
  have hidx1 : σ1 (.n 142) = eOfNat index.val := by
    rw [hindex]; have := hpre1.nodes 0 (by omega); simpa using this
  have h17 : σ1 (.n 17) = H.1 := congrArg Prod.fst hH1
  have h18 : σ1 (.n 18) = H.2 := congrArg Prod.snd hH1
  -- the coordinates
  refine Completes.append (m := b) (by omega) (by omega) (sCoords_below 8 0 (.n 209) 210 (by omega) ⟨209, by omega, rfl⟩)
    (sCoords_complete (C := C) (rd := rd) (inst := inst) hq hfk hrd index marks openings 8 0 (.n 209) 210 σ1
      (by omega) (by omega) ⟨209, by omega, rfl⟩ hpre1.md64 (by rw [hp1]; exact isCanonical128_cellOf _) hidx1)
    fun σ2 _ ⟨hrec2, hbd2, hag2⟩ => ?_
  simp only [Nat.zero_add] at hrec2 hbd2
  have hag21 : ∀ k < 210, σ2 (.n k) = σ1 (.n k) := fun k hk => (hag2 k hk).symm
  -- the lanes
  have hwd : ∀ k < 16, NB b (if k % 2 = 0 then (cs.2.2.1.getD (k / 2) (.n 0, .n 0)).1
      else (cs.2.2.1.getD (k / 2) (.n 0, .n 0)).2) := fun k hk => by
    obtain ⟨h1, h2, -, -⟩ := houts (k / 2) (by omega)
    split
    · exact h1
    · exact h2
  have hwv : ∀ k < 16, σ2 (if k % 2 = 0 then (cs.2.2.1.getD (k / 2) (.n 0, .n 0)).1
      else (cs.2.2.1.getD (k / 2) (.n 0, .n 0)).2) =
      eOfNat ((marks (k / 2)).word ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val := fun k hk => by
    obtain ⟨-, -, -, hw0, hw1⟩ := hrec2 (k / 2) (by omega)
    rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2
    · simp only [hk2, ↓reduceIte]
      rw [hw0, word_eq_eOfNat]
      rfl
    · simp only [hk2, Nat.one_ne_zero, ↓reduceIte]
      rw [hw1, word_eq_eOfNat]
      rfl
  have h17' : σ2 (.n 17) = lit (∑ k ∈ Finset.range 16,
      ((marks (k / 2)).word ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val * 2 ^ (8 * k)) :=
    (hag21 17 (by omega)).trans (h17.trans ((lit_cellNat_of (isCanonical128_hb _).1).symm.trans
      (dMarks_lanes x1 hx0).symm))
  have h18' : σ2 cs.2.2.2.2 = σ2 (.n 18) := by
    rw [hbd2, hpre1.bound, hag21 18 (by omega), h18]
    exact (dMarks_bound x1 hx0).trans (lit_cellNat_of (isCanonical128_hb _).2)
  refine Completes.append (m := b + 45) (by omega) (by omega) (sLanes_below hwd hbB (by omega))
    (sLanes_complete (by omega) hwd hbB (t := fun k => ((marks (k / 2)).word ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val)
      (fun k _ => ((marks (k / 2)).word _).isLt) hwv h17' h18') fun σ3 _ hag3 => ?_
  have hag31 : ∀ k < 210, σ3 (.n k) = σ1 (.n k) := fun k hk => (hag3 k (by omega)).symm.trans (hag21 k hk)
  have hkeep3 : ∀ v : V, NB b v → σ3 v = σ2 v := fun v ⟨k, hk, e⟩ => by rw [e]; exact (hag3 k hk).symm
  -- the forest key
  refine Completes.append (m := b + 45 + 2) (by omega) (by omega) (addr142_below (by omega) _)
    (addr142_complete (C := C) (rd := rd) (σ := σ3) (k := b + 45) (by omega) (word (tw 20) 0 0))
    fun σ4 _ ⟨h41, hag4⟩ => ?_
  have hag41 : ∀ k < 210, σ4 (.n k) = σ1 (.n k) := fun k hk => (hag4 k (by omega)).symm.trans (hag31 k hk)
  have htopB : ∀ k < 16, NB b (if k % 2 = 0 then (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).1
      else (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).2) := fun k hk => by
    obtain ⟨-, -, h1, h2⟩ := houts (k / 2) (by omega)
    split
    · exact h1
    · exact h2
  have htop4 : ∀ k < 16, σ4 (if k % 2 = 0 then (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).1
      else (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).2) = σ2 (if k % 2 = 0 then (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).1
      else (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).2) := fun k hk => by
    obtain ⟨j, hj, e⟩ := htopB k hk
    rw [e, ← hag4 j (by omega), hkeep3 _ ⟨j, hj, rfl⟩]
  have htopc : ∀ k < 16, IsCanonical128 (σ4 (if k % 2 = 0 then (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).1
      else (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).2)) := fun k hk => by
    rw [htop4 k hk]
    obtain ⟨-, hc1, hc2, -, -⟩ := hrec2 (k / 2) (by omega)
    split
    · exact hc1
    · exact hc2
  have hp4 : σ4 (.n 1) = pp := by rw [hag41 1 (by omega), hp1]
  have h142_4 : σ4 (.n 142) = eOfNat N := by rw [hag41 142 (by omega), hidx1, hindex]
  have hA4 : σ4 (.n (b + 45 + 1)) = eOfNat N + word (tw 20) 0 0 := by
    rw [h41, hag31 142 (by omega), hidx1, hindex]
  have hv := hashValues_complete (C := C) (rd := rd) (σ := σ4) (pp := .n 1) (a := .n (b + 45 + 1))
    (val := fun k => if k % 2 = 0 then (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).1
      else (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).2) (n := 16) (b := b + 45 + 2) (Or.inl (by norm_num)) (by norm_num)
    ⟨⟨1, by omega, rfl⟩, ⟨_, by omega, rfl⟩, fun i hi => (htopB i hi).mono (by omega)⟩
    ⟨by rw [hp4]; exact isCanonical128_cellOf _,
      by rw [hA4]; exact isCanonical128_add (isCanonical128_eOfNat _) (isCanonical128_word _ _), htopc⟩
  refine Completes.append (m := b + 45 + 2 + hashValuesSize 16) (by omega) (by omega)
    (hashValues_below (by norm_num) ⟨⟨1, by omega, rfl⟩, ⟨_, by omega, rfl⟩, fun i hi => (htopB i hi).mono (by omega)⟩)
    hv.withExt fun σ5 _ ⟨hfk5, he5⟩ => ?_
  have hag51 : ∀ k < 210, σ5 (.n k) = σ1 (.n k) := fun k hk => (he5.agree k (by omega)).symm.trans (hag41 k hk)
  have hp5 : σ5 (.n 1) = pp := by rw [hag51 1 (by omega), hp1]
  have h142_5 : σ5 (.n 142) = eOfNat N := by rw [hag51 142 (by omega), hidx1, hindex]
  -- the counter
  have hfkB := hashValues_snd_lt (.n 1) (.n (b + 45 + 1)) (fun k => if k % 2 = 0 then
    (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).1 else (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).2) 16 (b + 45 + 2)
  have hCn : (sig.layers Sphincs.topLayer).counter.toNat < 2 ^ 32 := (sig.layers Sphincs.topLayer).counter.isLt
  refine Completes.append (m := b + 45 + 2 + hashValuesSize 16 + 133) (by omega) (by omega)
    (sCounter_below hfkB (by omega))
    (sCounter_complete (C := C) (rd := rd) (σ := σ5) (by omega) hfkB hCn (by rw [hp5]; exact isCanonical128_cellOf _)
      (by rw [h142_5]; exact isCanonical128_add (isCanonical128_eOfNat _) (isCanonical128_word _ _))
      (by rw [hfk5]; exact (isCanonical128_hb _).1)) fun σ6 _ ⟨_, he61, he65, hag6⟩ => ?_
  -- the forest key's digest
  have hR : cellBytes (σ4 (.n (b + 45 + 1))) = Sphincs.tweakBytes (.roots index) := by
    rw [hA4, show tw 20 = 2 ^ 56 * 20 by simp only [tw]; ring, sp_add_word (by omega),
      Sphincs.tweakBytes, Sphincs.hashDomainFields, sTweak]
    refine congrArg (fun n => cellBytes (eOfNat n)) ?_
    rw [sp_addrNat (by omega) (by omega) (by omega) (by omega), hindex]
    ring
  have hcT : ∀ c : Sphincs.Coord, @Sphincs.Concrete.coordRecover Id _ inst (spp pp) index c (marks c.val)
      (openings c.val) = (sv ((fun k => σ4 (if k % 2 = 0 then (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).1
        else (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).2)) (2 * c.val)),
        sv ((fun k => σ4 (if k % 2 = 0 then (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).1
        else (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).2)) (2 * c.val + 1))) := fun c => by
    have hc8 := c.isLt
    simp only [Sphincs.forestCoords] at hc8
    have h := (hrec2 c.val c.isLt).1
    rw [hp1] at h
    dsimp only
    rw [htop4 _ (by omega), htop4 _ (by omega)]
    simp only [show 2 * c.val % 2 = 0 by omega, show (2 * c.val + 1) % 2 = 1 by omega,
      show 2 * c.val / 2 = c.val by omega, show (2 * c.val + 1) / 2 = c.val by omega, ↓reduceIte, Nat.one_ne_zero]
    exact h
  have hFK : @Sphincs.Concrete.forestRecover Id _ inst (spp pp) index (fun c => marks c.val) (fun c => openings c.val) =
      sv (σ5 (hashValues (.n 1) (.n (b + 45 + 1)) (fun k => if k % 2 = 0 then
        (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).1 else (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).2) 16 (b + 45 + 2)).2) := by
    rw [sForestRecover_cells hq (fun k => σ4 (if k % 2 = 0 then (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).1
        else (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).2)) hcT hR, hfk5, hp4]
  -- the encoding digest
  have htw4 : cellBytes (σ5 (.n 142) + word (tw 4) 0 0) = Sphincs.tweakBytes (.encoding Sphincs.topLayer 0 leaf) := by
    rw [h142_5, sp_tag_addr hN (by norm_num), ← hleaf, ← sTweak]
    rfl
  have hctrB : Sphincs.bytesLE 4 (sig.layers Sphincs.topLayer).counter =
      leBytes (sig.layers Sphincs.topLayer).counter.toNat 4 := sphincs_bytesLE_eq 4 _
  rw [hp5, List.append_assoc] at he65
  rw [hFK, sHash_bytes hq (by
      show Sphincs.bytesLE 16 (spp pp) ++ Sphincs.tweakBytes _ ++ _ = _
      rw [bytesLE_spp, ← htw4, bytesLE_sv, hctrB]), ← he65] at hdecE
  -- the tail
  set e := b + 45 + 2 + hashValuesSize 16 + 126 with he_def
  have hag61 : ∀ k < 210, σ6 (.n k) = σ1 (.n k) := fun k hk => (hag6 k (by omega)).symm.trans (hag51 k hk)
  have hp6 : σ6 (.n 1) = pp := by rw [hag61 1 (by omega), hp1]
  have h142_6 : σ6 (.n 142) = eOfNat N := by rw [hag61 142 (by omega), hidx1, hindex]
  refine Completes.append (m := (sMk e).2.2) (by omega) (by omega) (sTail_below (by omega))
    ((sTail_complete (C := C) (rd := rd) hq (hrd.mono (by norm_num)) (σ := σ6) (e := e) (by omega)
      (hpre1.congr hag61) h142_6 (by rw [hp6]; exact isCanonical128_cellOf _) hleaf hdecE
      (by rw [he65]; exact (isCanonical128_hb _).1) (canonical_finCells (sig.layers Sphincs.topLayer).chainValues)
      (canonical_finCells (sig.layers Sphincs.topLayer).path)).mono (by omega) le_rfl fun σ' h => h)
    fun σ7 _ ⟨hroot7, hcan7, hag7⟩ => ?_
  -- the root
  have hpath : Sphincs.Concrete.signaturePath sig Sphincs.topLayer =
      fun l => sv (finCells (sig.layers Sphincs.topLayer).path l) := funext fun l => by
    unfold Sphincs.Concrete.signaturePath finCells
    by_cases hl : l < Sphincs.layerHeight Sphincs.topLayer
    · simp only [hl, ↓reduceDIte]
      exact (cellVal_cellOf _).symm
    · simp only [hl, ↓reduceDIte]
      exact sv_zero.symm
  rw [hp6] at hroot7
  rw [sv_finCells (sig.layers Sphincs.topLayer).chainValues] at hlv
  rw [hpath, ← hlv] at htree
  have hroot : pk.root = sv (σ7 (sMk e).2.1) := htree.symm.trans hroot7
  have hrootc : σ7 (sMk e).2.1 = cellOf pk.root := by rw [hroot]; exact (cellOf_cellVal hcan7).symm
  have h70 : σ7 (.n 0) = p := by rw [← hag7 0 (by omega), hag61 0 (by omega), h01]
  -- the claim's root
  obtain ⟨kr, hkr, hkre⟩ := sMk_root_lt e
  have hne0 : (V.n 0) ≠ V.n (sMk e).2.2 := fun h => by simp only [V.mk.injEq] at h; omega
  have hner : (sMk e).2.1 ≠ V.n (sMk e).2.2 := fun h => by rw [hkre] at h; simp only [V.mk.injEq] at h; omega
  refine Completes.atom_cons (cellOf pk.root) le_rfl
    (.cons ⟨_, by omega, rfl⟩ (.cons ⟨0, by omega, rfl⟩ (.nil _))) ?_ ?_
  · show LoadHolds rd (Function.update σ7 (.n (sMk e).2.2) (cellOf pk.root) (.n 0)) 0
      (Function.update σ7 (.n (sMk e).2.2) (cellOf pk.root) (.n (sMk e).2.2))
    rw [Function.update_self, Function.update_of_ne hne0, h70]
    exact hc 0
  refine Completes.atom_cons0 (.cons ⟨kr, by omega, hkre⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))) ?_
    (Completes.nil _ _ _ trivial)
  show Function.update σ7 (.n (sMk e).2.2) (cellOf pk.root) (sMk e).2.1 +
    Function.update σ7 (.n (sMk e).2.2) (cellOf pk.root) (.n (sMk e).2.2) = 0
  rw [Function.update_self, Function.update_of_ne hner, hrootc]
  exact e_add_eq_zero_iff.mpr rfl

end Sig

variable {rd : Reader}

/-- **`verify_sig_lean_sphincs` is its meaning**, on a memory holding at least 256 words. -/
theorem verify_sig_lean_sphincs_iff (hrd : MemOK rd 256) {args rets : List E} :
    coreProgram.Rel rd "verify_sig_lean_sphincs" args rets ↔ Meaning_verify_sig_lean_sphincs rd args rets := by
  refine ⟨verify_sig_lean_sphincs_meaning, fun ⟨p, ha, hr, pk, m, hc, sig, hv⟩ => ?_⟩
  obtain ⟨σ, hσ, hb⟩ := Sig.verify_sig_lean_sphincs_complete (C := coreProgram.Rel rd) Sig.fkComplete_rel hrd hc hv
  refine (rel_iff_sem Sig.find_verify_sig_lean_sphincs args rets).mpr ⟨σ, by rw [ha]; simp [hσ], ?_⟩
  rw [hr]
  exact hb

end
end LeanVM.Guest.B1
