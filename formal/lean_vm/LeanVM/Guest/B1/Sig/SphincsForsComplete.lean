/-
  LeanVM.Guest.B1.Sig.SphincsForsComplete

  The FORS block of `verify_sig_lean_sphincs` (`sp_fors_tree`, `lean_ethereum.py:4034-4055`, and
  `T_k`, `lean_ethereum.py:4226-4228`) is complete: each tree's secret and the
  ordered children of its levels hinted, the FORS key is `T_k` of the roots.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsPathComplete
public import LeanVM.Guest.B1.Sig.SphincsSoundFors

/-!
# FORS, complete

* `sForsAt_seq`: `sp_fors_at` is a sequential block;
* `sForsLevels_complete`: a tree's levels, the siblings read back (`sForsSib`);
* `sForsTree_complete`: a tree, its secret and siblings read back, its root `fRootE`;
* `sForsTrees_complete`, `sForsBlock_complete`: the 24 trees, and the FORS key.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

open LeanVM.Guest.Memory (FallPops)

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem pFold_congr {node node' : Nat → E → E} : ∀ (m : Nat) (v : E),
    (∀ j < m, node j = node' j) → pFold node m v = pFold node' m v
  | 0, _, _ => rfl
  | m + 1, v, h => by
      rw [pFold, pFold, pFold_congr m v fun j hj => h j (by omega), h m (by omega)]

theorem fRootE_congr {pp a0 A1 : E} {c s : Nat} {secret : E} {sib sib' : Nat → E}
    (h : ∀ j < 10, sib j = sib' j) : fRootE pp a0 A1 c s secret sib = fRootE pp a0 A1 c s secret sib' := by
  unfold fRootE
  refine pFold_congr 10 _ fun j hj => ?_
  funext v
  unfold fNodeE
  rw [h j hj]

/-! ## Shapes -/

/-- `a + const(w)` is a sequential block whose value is below its next base. -/
theorem sAddK_seq {a : V} {k : Nat} {w : E} {x : Nat} (ha : NBv x a) :
    SeqOK x (sAddK a k w x).1 (sAddK a k w x).2.1 ∧ NBv (sAddK a k w x).2.1 (sAddK a k w x).2.2 ∧
      x ≤ (sAddK a k w x).2.1 := by
  unfold sAddK
  split
  · exact ⟨rfl, ha, le_rfl⟩
  · exact ⟨⟨rfl, ⟨rfl, ha.mono' (by omega), ⟨x, by omega, rfl⟩⟩, rfl⟩,
      ⟨x + 1, show x + 1 < x + 2 by omega, rfl⟩, show x ≤ x + 2 by omega⟩

theorem sAddK_atoms (a : V) (k : Nat) (w : E) (x : Nat) : atomsOnly (sAddK a k w x).1 = true := by
  unfold sAddK; split <;> rfl

/-- `sp_be16` then the sum with `s`, from base `y`: a sequential block. -/
theorem sBe16Add_seq {val : Nat → V} {pos n y : Nat} {s : V} (hs : NBv y s)
    (h0 : NBv y (val pos)) (h8 : (n + 7) / 8 = 2 → NBv y (val (pos + 8))) :
    SeqOK y ((sBe16 val pos n y).1 ++ [addS (.n (sBe16 val pos n y).2.1) s (sBe16 val pos n y).2.2])
      ((sBe16 val pos n y).2.1 + 1) ∧
      NBv ((sBe16 val pos n y).2.1 + 1) (.n (sBe16 val pos n y).2.1) := by
  have hb := sBe16_seq (val := val) (pos := pos) (n := n) (x := y) h0 h8
  have hle := hb.le
  have ho := sBe16_out val pos n y
  have hx : y < (sBe16 val pos n y).2.1 := by rw [sBe16_next]; split <;> omega
  refine ⟨SeqOK.append hb ⟨⟨rfl, hs.mono' (by omega), ?_⟩, rfl⟩, ⟨_, by omega, rfl⟩⟩
  rw [ho]; exact ⟨_, by omega, rfl⟩

theorem sForsAt_seq {a1 : V} {val : Nat → V} {c z x : Nat} (ha : NBv x a1)
    (h0 : z ≠ 10 → NBv x (val (10 * c + z))) (h8 : z ≤ 1 → NBv x (val (10 * c + z + 8))) :
    SeqOK x (sForsAt a1 val c z x).1 (sForsAt a1 val c z x).2.1 ∧
      NBv (sForsAt a1 val c z x).2.1 (sForsAt a1 val c z x).2.2 := by
  obtain ⟨k1, k2, k3⟩ := sAddK_seq (k := z) (w := lit (2 ^ 88 * z)) ha
  by_cases hz : z = 10
  · subst hz
    simp only [sForsAt, ↓reduceIte]
    obtain ⟨m1, m2, -⟩ := sAddK_seq (k := c) (w := lit (2 ^ 120 * c)) k2
    exact ⟨SeqOK.append k1 m1, m2⟩
  · by_cases hz2 : z / 2 = 0
    · simp only [sForsAt, hz, hz2, ↓reduceIte]
      obtain ⟨b1, b2⟩ := sBe16Add_seq (n := 16) k2 ((h0 hz).mono' k3)
        (fun _ => (h8 (by omega)).mono' k3)
      exact ⟨by rw [List.append_assoc]; exact SeqOK.append k1 b1, b2⟩
    · simp only [sForsAt, hz, hz2, ↓reduceIte]
      obtain ⟨m1, m2, m3⟩ := sAddK_seq (k := c / 2 ^ (z - 2)) (w := forsHiW (c / 2 ^ (z - 2))) k2
      obtain ⟨b1, b2⟩ := sBe16Add_seq (n := 8) m2 ((h0 hz).mono' (by omega))
        (fun h => by omega)
      exact ⟨by rw [List.append_assoc, List.append_assoc]
                exact SeqOK.append k1 (SeqOK.append m1 b1), b2⟩

theorem sForsAt_atoms (a1 : V) (val : Nat → V) (c z x : Nat) :
    atomsOnly (sForsAt a1 val c z x).1 = true := by
  unfold sForsAt
  split_ifs <;> simp [atomsOnly_append, sAddK_atoms, sBe16_atoms, addS, atomsOnly]

theorem sForsLevels_atoms (pad : Nat) (pp a0 a1 : V) (bit val : Nat → V) (c : Nat) :
    ∀ (m z : Nat) (cur : V) (x : Nat), atomsOnly (sForsLevels pad pp a0 a1 bit val c m z cur x).1 = true
  | 0, _, _, _ => rfl
  | m + 1, z, cur, x => by
      rw [sForsLevels_succ, sForsLevel_eq]
      simp only [atomsOnly_append, sForsAt_atoms, kNode,
        sForsLevels_atoms pad pp a0 a1 bit val c m (z + 1)]
      rfl

theorem sForsLevels_le (pad : Nat) (pp a0 a1 : V) (bit val : Nat → V) (c : Nat) :
    ∀ (m z : Nat) (cur : V) (x : Nat), z + m ≤ 10 →
      x ≤ (sForsLevels pad pp a0 a1 bit val c m z cur x).2.1 := by
  intro m z cur x h
  rw [forsLevels_shape pad pp a0 a1 bit val c m z cur x h]
  omega

/-! ## The levels -/

/-- **A FORS tree's levels complete** from level `z` (base `x`), `m` levels up to `10`: each level's
children hinted in the order of the leaf `s`'s bit, the siblings `sib` read back. -/
theorem sForsLevels_complete {pad : Nat} {pp a0 a1 : V} {bit val : Nat → V} {c s : Nat}
    (hc : c < 24) (hs : s < 2 ^ 10) {sib : Nat → E} :
    ∀ (m z : Nat) (cur : V) (x : Nat) (σ : Val), z + m ≤ 10 → pad + 5 ≤ x → NBv x pp →
      NBv x a0 → NBv x a1 → (∀ j < 10, NBv x (bit (10 * c + j))) →
      (∀ j < 10, NBv x (val (10 * c + j))) → NBv x cur → PadOK σ pad →
      (∀ j < 10, σ (bit (10 * c + j)) = if s.testBit j then 1 else 0) →
      (∀ j < 10, σ (val (10 * c + j)) = eOfNat (fIdx c j s)) →
      Completes C rd x (sForsLevels pad pp a0 a1 bit val c m z cur x).2.1
        (sForsLevels pad pp a0 a1 bit val c m z cur x).1 σ
        (fun σ' => AgreeBelow x σ σ' ∧ ∀ j, z ≤ j → j < z + m → sForsSib σ' bit c m z x j = sib j)
  | 0, _, _, _, σ, _, _, _, _, _, _, _, _, _, _, _ =>
      ⟨σ, Ext.refl _ _ _, ⟨fun _ _ => rfl, fun j h1 h2 => by omega⟩, fun _ _ hn => hn⟩
  | m + 1, z, cur, x, σ, hm, hpx, hpp, ha0, ha1, hbn, hvn, hcur, hp, hbit, hval => by
      rw [sForsLevels_succ, sForsLevel_eq]
      set A := sForsAt a1 val c (z + 1) (x + 4) with hA
      obtain ⟨hseqA, hadrA⟩ := sForsAt_seq (a1 := a1) (val := val) (c := c) (z := z + 1) (x := x + 4)
        (ha1.mono' (by omega)) (fun _ => (hvn (z + 1) (by omega)).mono' (by omega))
        (fun h1 => (hvn (z + 1 + 8) (by omega)).mono' (by omega))
      have hnext := sForsAt_next a1 val c z x (by omega)
      rw [← hA] at hseqA hadrA hnext
      have hlev := pairNode_complete (C := C) (rd := rd) "sp_fors_nodes" σ hpx hpp ha0
        (hbn z (by omega)) hcur hseqA hadrA (bt := s.testBit z) (sib := sib z) (hbit z (by omega))
      have hle := hseqA.le
      have hx18 : x + forsLevelWidth c z = A.2.1 + 5 := by
        have : 9 ≤ forsLevelWidth c z := by unfold forsLevelWidth forsLevelW; omega
        omega
      have hnb : NumBelow (A.2.1 + 5) (Stmt.valsList ([hintW "sp_fors_nodes" [.n x, .n (x + 1)]] ++
          isChildS cur (.n x) (.n (x + 1)) (bit (10 * c + z)) (x + 2) ++ A.1 ++
          (kNode pad pp a0 A.2.2 (.n x) (.n (x + 1)) A.2.1).1)) := by
        simp only [valsList_append]
        refine NumBelow.append (NumBelow.append (NumBelow.append ?_ ?_) ?_) ?_
        · rw [valsList_hint]
          exact .cons ⟨x, by omega, rfl⟩ (.cons ⟨x + 1, by omega, rfl⟩ (.nil _))
        · intro v hv
          simp only [isChildS, addS, mulS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals,
            List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals first | exact ⟨_, by omega, rfl⟩ | exact hcur.mono' (by omega) |
            exact (hbn z (by omega)).mono' (by omega)
        · exact hseqA.numBelow.mono (by omega)
        · refine kNode_numBelow (by omega) ?_
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro v (rfl | rfl | rfl | rfl | rfl)
          · exact hpp.mono' (by omega)
          · exact ha0.mono' (by omega)
          · exact hadrA
          · exact ⟨x, by omega, rfl⟩
          · exact ⟨x + 1, by omega, rfl⟩
      refine Completes.append (m := A.2.1 + 5) (by omega)
        (sForsLevels_le pad pp a0 a1 bit val c m (z + 1) _ _ (by omega)) hnb
        (hlev.withAtoms (by simp only [atomsOnly_append, hseqA.atoms, kNode]; rfl))
        (fun σ1 he1 h1 => ?_)
      obtain ⟨⟨hag1, hk0, hk1⟩, hA1⟩ := h1
      have t1 : ∀ v, NBv x v → σ1 v = σ v := fun v hv => hag1.apply hv
      obtain ⟨hib, hd⟩ := bit_facts (hbit z (by omega))
      have hib1 : IsBit (σ1 (bit (10 * c + z))) := by rw [t1 _ (hbn z (by omega))]; exact hib
      have hp1 : PadOK σ1 pad := hp.congr hpx hag1
      have hlv := level_sound hp1 hib1
        (hA1.left.left.sub fun t ht => List.mem_append_right _ ht) hA1.right
      have ih := sForsLevels_complete (sib := sib) hc hs m (z + 1) (.n (A.2.1 + 4)) (A.2.1 + 5) σ1
        (by omega) (by omega) (hpp.mono' (by omega)) (ha0.mono' (by omega)) (ha1.mono' (by omega))
        (fun j hj => (hbn j hj).mono' (by omega)) (fun j hj => (hvn j hj).mono' (by omega))
        ⟨A.2.1 + 4, by omega, rfl⟩ hp1 (fun j hj => by rw [t1 _ (hbn j hj)]; exact hbit j hj)
        (fun j hj => by rw [t1 _ (hvn j hj)]; exact hval j hj)
      refine ih.mono le_rfl le_rfl (fun σ' ⟨hag', hs'⟩ => ⟨?_, ?_⟩)
      · exact fun j hj => (hag1 j hj).trans (hag' j (by omega))
      · intro j hj1 hj2
        by_cases hjz : j = z
        · subst hjz
          simp only [sForsSib, ite_true]
          have hb' : σ' (bit (10 * c + j)) = if s.testBit j then 1 else 0 := by
            rw [(hag'.apply ((hbn j (by omega)).mono' (by omega))), t1 _ (hbn j (by omega))]
            exact hbit j (by omega)
          exact siblingOf_mPair (node := σ cur) hb' (by rw [← hag' x (by omega), hk0])
            (by rw [← hag' (x + 1) (by omega), hk1])
        · simp only [sForsSib, hjz, ite_false, hx18]
          exact hs' j (by omega) (by omega)

/-! ## A tree -/

theorem k64_numBelow {pad : Nat} {m0 m1 m2 m3 : V} {c : Nat} (hpc : pad + 5 ≤ c)
    (hm : ∀ v ∈ [m0, m1, m2, m3], NBv c v) :
    NumBelow (c + 2) (Stmt.valsList (k64 pad m0 m1 m2 m3 c (c + 1))) := by
  rw [k64_vals_eq]
  intro v hv
  simp only [cst, kecS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals,
    List.append_nil, List.cons_append, List.nil_append, List.mem_cons] at hv
  have hr : ∀ w ∈ runV (c + 1) 1, NBv (c + 2) w := runV_nb (by omega)
  have h0 := hm m0 (by simp)
  have h1 := hm m1 (by simp)
  have h2 := hm m2 (by simp)
  have h3 := hm m3 (by simp)
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    hv
  all_goals first
    | exact ⟨_, by omega, rfl⟩
    | exact h0.mono' (by omega)
    | exact h1.mono' (by omega)
    | exact h2.mono' (by omega)
    | exact h3.mono' (by omega)
    | exact hr _ hv

theorem sForsTree_atoms (pad : Nat) (pp a0 a1 : V) (bit val : Nat → V) (c b : Nat) :
    atomsOnly (sForsTree pad pp a0 a1 bit val c b).1 = true := by
  simp only [sForsTree, atomsOnly_append, sForsAt_atoms, sForsLevels_atoms, k64]
  rfl

/-- **FORS tree `c` completes** from base `b`: its secret hinted at `b`, its levels' children in the
order of the leaf `s`'s bits; the secret and the siblings `sib` read back. -/
theorem sForsTree_complete {pad : Nat} {pp a0 a1 : V} {bit val : Nat → V} {c s b : Nat}
    (hc : c < 24) (hs : s < 2 ^ 10) {secret : E} {sib : Nat → E} (σ : Val) (hpb : pad + 5 ≤ b)
    (hpp : NBv b pp) (ha0 : NBv b a0) (ha1 : NBv b a1) (hbn : ∀ j < 10, NBv b (bit (10 * c + j)))
    (hvn : ∀ j < 10, NBv b (val (10 * c + j))) (hp : PadOK σ pad)
    (hbit : ∀ j < 10, σ (bit (10 * c + j)) = if s.testBit j then 1 else 0)
    (hval : ∀ j < 10, σ (val (10 * c + j)) = eOfNat (fIdx c j s)) :
    Completes C rd b (sForsTree pad pp a0 a1 bit val c b).2.1 (sForsTree pad pp a0 a1 bit val c b).1 σ
      (fun σ' => AgreeBelow b σ σ' ∧ σ' (.n b) = secret ∧
        ∀ j < 10, sForsSib σ' bit c 10 0 (b + forsLeafWidth c) j = sib j) := by
  set σr := updRun σ b 1 (fun _ => secret) with hσr
  have tk : ∀ v, NBv b v → σr v = σ v := fun v hv => updRun_below σ b 1 (fun _ => secret) hv
  have hsr : σr (.n b) = secret := by
    have := updRun_at σ b 1 (fun _ => secret) (j := 0) (by norm_num); rwa [Nat.add_zero] at this
  refine Completes.reload ((updRun_ext σ b 1 (fun _ => secret)).mono le_rfl
    (by rw [(sForsTree_shape pad pp a0 a1 bit val c b).1]; have := forsTreeW_ge c; omega)) ?_
  have hy := sForsAt_leaf_next a1 val c b
  have hlw : forsLeafWidth c = 9 := rfl
  simp only [sForsTree, List.append_assoc]
  set A := sForsAt a1 val c 0 (b + 1) with hA
  obtain ⟨hseqA, hadrA⟩ := sForsAt_seq (a1 := a1) (val := val) (c := c) (z := 0) (x := b + 1)
    (ha1.mono' (by omega)) (fun _ => (hvn 0 (by omega)).mono' (by omega))
    (fun _ => (hvn 8 (by omega)).mono' (by omega))
  rw [← hA] at hseqA hadrA
  have hle := hseqA.le
  have hw : A.2.1 + 2 = b + forsLeafWidth c := by omega
  have hlv_le := sForsLevels_le pad pp a0 a1 bit val c 10 0 (.n (A.2.1 + 1)) (A.2.1 + 2) (by norm_num)
  refine Completes.append (m := b + 1) (by omega) (by omega)
    (by rw [valsList_hint]; exact .cons ⟨b, by omega, rfl⟩ (.nil _))
    (hintKeep_complete σr _ _ _ _) (fun σ1 he1 hp1 => ?_)
  subst hp1
  refine Completes.seqThen hseqA (by omega) (fun σ2 he2 hA2 => ?_)
  have hag2 : AgreeBelow (b + 1) σr σ2 := he2.agree
  have t2 : ∀ v, NBv b v → σ2 v = σ v := fun v hv =>
    (hag2.apply (hv.mono' (by omega))).trans (tk v hv)
  have hs2 : σ2 (.n b) = secret := (hag2.apply ⟨b, by omega, rfl⟩).trans hsr
  have hk := k64_complete (C := C) (rd := rd) (pad := pad) (m0 := pp) (m1 := a0) (m2 := A.2.2)
    (m3 := .n b) (c := A.2.1) σ2 (hp.congr hpb fun j hj => (t2 (.n j) ⟨j, hj, rfl⟩).symm)
    (by omega) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl | rfl | rfl)
      · exact hpp.mono' (by omega)
      · exact ha0.mono' (by omega)
      · exact hadrA
      · exact ⟨b, by omega, rfl⟩)
  have hnbk := k64_numBelow (pad := pad) (m0 := pp) (m1 := a0) (m2 := A.2.2) (m3 := .n b)
    (c := A.2.1) (by omega) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl | rfl | rfl)
      · exact hpp.mono' (by omega)
      · exact ha0.mono' (by omega)
      · exact hadrA
      · exact ⟨b, by omega, rfl⟩)
  refine Completes.append (m := A.2.1 + 2) (by omega) hlv_le hnbk hk.withExt
    (fun σ3 he3 h3 => ?_)
  obtain ⟨-, he3'⟩ := h3
  have hag3 : AgreeBelow A.2.1 σ2 σ3 := he3'.agree
  have t3 : ∀ v, NBv b v → σ3 v = σ v := fun v hv =>
    (hag3.apply (hv.mono' (by omega))).trans (t2 v hv)
  have hlvc := sForsLevels_complete (C := C) (rd := rd) (pad := pad) (pp := pp) (a0 := a0) (a1 := a1)
    (bit := bit) (val := val) (sib := sib) hc hs 10 0 (.n (A.2.1 + 1)) (A.2.1 + 2) σ3 (by norm_num)
    (by omega) (hpp.mono' (by omega)) (ha0.mono' (by omega)) (ha1.mono' (by omega))
    (fun j hj => (hbn j hj).mono' (by omega)) (fun j hj => (hvn j hj).mono' (by omega))
    ⟨A.2.1 + 1, by omega, rfl⟩ (hp.congr hpb fun j hj => (t3 (.n j) ⟨j, hj, rfl⟩).symm)
    (fun j hj => by rw [t3 _ (hbn j hj)]; exact hbit j hj)
    (fun j hj => by rw [t3 _ (hvn j hj)]; exact hval j hj)
  refine hlvc.mono le_rfl le_rfl (fun σ' ⟨hag', hs'⟩ => ⟨?_, ?_, ?_⟩)
  · intro j hj
    rw [← t3 (.n j) ⟨j, hj, rfl⟩]
    exact hag' j (by omega)
  · rw [← hag' b (by omega), ← hag3 b (by omega), hs2]
  · intro j hj
    rw [← hw]
    exact hs' j (by omega) (by omega)

/-- **FORS tree `c`'s root**, completed: `fRootE` of the secret and siblings. -/
theorem sForsTree_complete_val {pad : Nat} {pp a0 a1 : V} {bit val : Nat → V} {c s b : Nat}
    (hc : c < 24) (hs : s < 2 ^ 10) {secret : E} {sib : Nat → E} (σ : Val) (hpb : pad + 5 ≤ b)
    (hpp : NBv b pp) (ha0 : NBv b a0) (ha1 : NBv b a1) (hbn : ∀ j < 10, NBv b (bit (10 * c + j)))
    (hvn : ∀ j < 10, NBv b (val (10 * c + j))) (hp : PadOK σ pad)
    (hbit : ∀ j < 10, σ (bit (10 * c + j)) = if s.testBit j then 1 else 0)
    (hval : ∀ j < 10, σ (val (10 * c + j)) = eOfNat (fIdx c j s)) :
    Completes C rd b (sForsTree pad pp a0 a1 bit val c b).2.1 (sForsTree pad pp a0 a1 bit val c b).1 σ
      (fun σ' => AgreeBelow b σ σ' ∧
        σ' (sForsTree pad pp a0 a1 bit val c b).2.2 = fRootE (σ pp) (σ a0) (σ a1) c s secret sib) := by
  refine ((sForsTree_complete (secret := secret) (sib := sib) hc hs σ hpb hpp ha0 ha1 hbn hvn hp hbit
    hval).withAtoms (sForsTree_atoms ..)).mono le_rfl le_rfl
    (fun σ' ⟨⟨hag, hsec', hsib'⟩, hA⟩ => ⟨hag, ?_⟩)
  have t : ∀ v, NBv b v → σ' v = σ v := fun v hv => hag.apply hv
  rw [sForsTree_sound (hp.congr hpb hag) hc hs
    (fun j hj => by rw [t _ (hbn j hj)]; exact hbit j hj)
    (fun j hj => by rw [t _ (hvn j hj)]; exact hval j hj) hA, t _ hpp, t _ ha0, t _ ha1, hsec']
  exact fRootE_congr hsib'

theorem forsTreePops_congr (pp a0 A1 : E) (c s : Nat) (secret : E) {sib sib' : Nat → E}
    (h : ∀ j < 10, sib j = sib' j) :
    forsTreePops pp a0 A1 c s secret sib = forsTreePops pp a0 A1 c s secret sib' := by
  unfold forsTreePops
  rw [climbPops_congr _ _ 10 0 _ fun j _ hj =>
    ⟨funext fun v => by unfold fNodeE; rw [h j (by omega)], h j (by omega)⟩]
  rfl

/-- **FORS tree `c` completes popping its secret and its levels' children** (`forsTreePops`), its root `fRootE`. -/
theorem sForsTree_complete_pops {pad : Nat} {pp a0 a1 : V} {bit val : Nat → V} {c s b : Nat}
    (hc : c < 24) (hs : s < 2 ^ 10) {secret : E} {sib : Nat → E} (σ : Val) (hpb : pad + 5 ≤ b)
    (hpp : NBv b pp) (ha0 : NBv b a0) (ha1 : NBv b a1) (hbn : ∀ j < 10, NBv b (bit (10 * c + j)))
    (hvn : ∀ j < 10, NBv b (val (10 * c + j))) (hp : PadOK σ pad)
    (hbit : ∀ j < 10, σ (bit (10 * c + j)) = if s.testBit j then 1 else 0)
    (hval : ∀ j < 10, σ (val (10 * c + j)) = eOfNat (fIdx c j s)) :
    Completes C rd b (sForsTree pad pp a0 a1 bit val c b).2.1 (sForsTree pad pp a0 a1 bit val c b).1 σ
      (fun σ' => AgreeBelow b σ σ' ∧
        σ' (sForsTree pad pp a0 a1 bit val c b).2.2 = fRootE (σ pp) (σ a0) (σ a1) c s secret sib ∧
        FallPops rd σ' (sForsTree pad pp a0 a1 bit val c b).1
          (forsTreePops (σ pp) (σ a0) (σ a1) c s secret sib)) := by
  refine ((sForsTree_complete (secret := secret) (sib := sib) hc hs σ hpb hpp ha0 ha1 hbn hvn hp hbit
    hval).withAtoms (sForsTree_atoms ..)).mono le_rfl le_rfl
    (fun σ' ⟨⟨hag, hsec', hsib'⟩, hA⟩ => ?_)
  have t : ∀ v, NBv b v → σ' v = σ v := fun v hv => hag.apply hv
  have hp' := hp.congr hpb hag
  have hb' : ∀ j < 10, σ' (bit (10 * c + j)) = if s.testBit j then 1 else 0 :=
    fun j hj => by rw [t _ (hbn j hj)]; exact hbit j hj
  have hv' : ∀ j < 10, σ' (val (10 * c + j)) = eOfNat (fIdx c j s) :=
    fun j hj => by rw [t _ (hvn j hj)]; exact hval j hj
  refine ⟨hag, ?_, ?_⟩
  · rw [sForsTree_sound hp' hc hs hb' hv' hA, t _ hpp, t _ ha0, t _ ha1, hsec']
    exact fRootE_congr hsib'
  · have hP := sForsTree_pops (rd := rd) hp' hc hs hb' hv' hA
    rw [t _ hpp, t _ ha0, t _ ha1, hsec'] at hP
    exact FallPops.congr_pops hP (forsTreePops_congr _ _ _ _ _ _ hsib')

/-! ## The trees -/

theorem sForsLevels_nb {pad : Nat} {pp a0 a1 : V} {bit val : Nat → V} {c : Nat} :
    ∀ (m z : Nat) (cur : V) (x : Nat), z + m ≤ 10 → pad + 5 ≤ x → NBv x pp → NBv x a0 →
      NBv x a1 → (∀ j < 10, NBv x (bit (10 * c + j))) → (∀ j < 10, NBv x (val (10 * c + j))) →
      NBv x cur → NumBelow (sForsLevels pad pp a0 a1 bit val c m z cur x).2.1
        (Stmt.valsList (sForsLevels pad pp a0 a1 bit val c m z cur x).1)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => NumBelow.nil _
  | m + 1, z, cur, x, hm, hpx, hpp, ha0, ha1, hbn, hvn, hcur => by
      rw [sForsLevels_succ, sForsLevel_eq]
      set A := sForsAt a1 val c (z + 1) (x + 4) with hA
      obtain ⟨hseqA, hadrA⟩ := sForsAt_seq (a1 := a1) (val := val) (c := c) (z := z + 1) (x := x + 4)
        (ha1.mono' (by omega)) (fun _ => (hvn (z + 1) (by omega)).mono' (by omega))
        (fun h1 => (hvn (z + 1 + 8) (by omega)).mono' (by omega))
      rw [← hA] at hseqA hadrA
      have hle := hseqA.le
      have hrest := sForsLevels_nb (pad := pad) (pp := pp) (a0 := a0) (a1 := a1) (bit := bit)
        (val := val) (c := c) m (z + 1) (.n (A.2.1 + 4)) (A.2.1 + 5) (by omega) (by omega)
        (hpp.mono' (by omega)) (ha0.mono' (by omega)) (ha1.mono' (by omega))
        (fun j hj => (hbn j hj).mono' (by omega)) (fun j hj => (hvn j hj).mono' (by omega))
        ⟨A.2.1 + 4, by omega, rfl⟩
      have hge := sForsLevels_le pad pp a0 a1 bit val c m (z + 1) (.n (A.2.1 + 4)) (A.2.1 + 5)
        (by omega)
      simp only [valsList_append]
      refine NumBelow.append (NumBelow.append (NumBelow.append (NumBelow.append ?_ ?_) ?_) ?_) hrest
      · rw [valsList_hint]
        exact .cons ⟨x, by omega, rfl⟩ (.cons ⟨x + 1, by omega, rfl⟩ (.nil _))
      · intro v hv
        simp only [isChildS, addS, mulS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals,
          List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | exact ⟨_, by omega, rfl⟩ | exact hcur.mono' (by omega) |
          exact (hbn z (by omega)).mono' (by omega)
      · exact hseqA.numBelow.mono (by omega)
      · refine (kNode_numBelow (by omega) ?_).mono (by omega)
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro v (rfl | rfl | rfl | rfl | rfl)
        · exact hpp.mono' (by omega)
        · exact ha0.mono' (by omega)
        · exact hadrA
        · exact ⟨x, by omega, rfl⟩
        · exact ⟨x + 1, by omega, rfl⟩

theorem sForsTree_nb {pad : Nat} {pp a0 a1 : V} {bit val : Nat → V} {c b : Nat} (hpb : pad + 5 ≤ b)
    (hpp : NBv b pp) (ha0 : NBv b a0) (ha1 : NBv b a1) (hbn : ∀ j < 10, NBv b (bit (10 * c + j)))
    (hvn : ∀ j < 10, NBv b (val (10 * c + j))) :
    NumBelow (sForsTree pad pp a0 a1 bit val c b).2.1
      (Stmt.valsList (sForsTree pad pp a0 a1 bit val c b).1) := by
  have hy := sForsAt_leaf_next a1 val c b
  have hlw : forsLeafWidth c = 9 := rfl
  simp only [sForsTree]
  set A := sForsAt a1 val c 0 (b + 1) with hA
  obtain ⟨hseqA, hadrA⟩ := sForsAt_seq (a1 := a1) (val := val) (c := c) (z := 0) (x := b + 1)
    (ha1.mono' (by omega)) (fun _ => (hvn 0 (by omega)).mono' (by omega))
    (fun _ => (hvn 8 (by omega)).mono' (by omega))
  rw [← hA] at hseqA hadrA
  have hle := hseqA.le
  have hge := sForsLevels_le pad pp a0 a1 bit val c 10 0 (.n (A.2.1 + 1)) (A.2.1 + 2) (by norm_num)
  simp only [valsList_append]
  refine NumBelow.append (NumBelow.append (NumBelow.append ?_ ?_) ?_)
    (sForsLevels_nb 10 0 _ _ (by norm_num) (by omega) (hpp.mono' (by omega)) (ha0.mono' (by omega))
      (ha1.mono' (by omega)) (fun j hj => (hbn j hj).mono' (by omega))
      (fun j hj => (hvn j hj).mono' (by omega)) ⟨A.2.1 + 1, by omega, rfl⟩)
  · rw [valsList_hint]; exact .cons ⟨b, by omega, rfl⟩ (.nil _)
  · exact hseqA.numBelow.mono (by omega)
  · refine (k64_numBelow (by omega) ?_).mono (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl)
    · exact hpp.mono' (by omega)
    · exact ha0.mono' (by omega)
    · exact hadrA
    · exact ⟨b, by omega, rfl⟩

theorem forsTreeBase_mono (b0 : Nat) {c c' : Nat} (h : c ≤ c') :
    forsTreeBase b0 c ≤ forsTreeBase b0 c' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [forsTreeBase_succ]; omega

theorem forsTreeBase_24 (b0 : Nat) : forsTreeBase b0 (0 + 24) = b0 + 3802 := by
  have : ((List.range 24).map forsTreeW).sum = 3800 := by decide +kernel
  simp only [forsTreeBase, Nat.zero_add, this]

theorem forsTreeBase_ge (b0 c : Nat) : b0 + 2 ≤ forsTreeBase b0 c := by
  unfold forsTreeBase; omega

theorem forsRootPos_lt (b0 c : Nat) : forsRootPos b0 c < forsTreeBase b0 (c + 1) ∧
    forsTreeBase b0 c ≤ forsRootPos b0 c := by
  have := forsTreeW_ge c
  rw [forsTreeBase_succ]; unfold forsRootPos; omega

/-- The trees' values, below their next base. -/
theorem sForsTrees_nb {pad : Nat} {pp a0 a1 : V} {bit val : Nat → V} {b0 : Nat}
    (hpb : pad + 5 ≤ b0 + 2) (hpp : NBv (b0 + 2) pp) (ha0 : NBv (b0 + 2) a0) (ha1 : NBv (b0 + 2) a1)
    (hbn : ∀ k < 240, NBv (b0 + 2) (bit k)) (hvn : ∀ k < 240, NBv (b0 + 2) (val k)) :
    ∀ (m c : Nat), c + m ≤ 24 →
      NumBelow (forsTreeBase b0 (c + m))
        (Stmt.valsList (sForsTrees pad pp a0 a1 bit val m c (forsTreeBase b0 c)).1)
  | 0, _, _ => NumBelow.nil _
  | m + 1, c, hcm => by
      have h2 : b0 + 2 ≤ forsTreeBase b0 c := forsTreeBase_ge b0 c
      rw [sForsTrees_succ, valsList_append]
      have ht := sForsTree_nb (pad := pad) (pp := pp) (a0 := a0) (a1 := a1) (bit := bit) (val := val)
        (c := c) (b := forsTreeBase b0 c) (by omega) (hpp.mono' h2) (ha0.mono' h2) (ha1.mono' h2)
        (fun j hj => (hbn _ (by omega)).mono' h2) (fun j hj => (hvn _ (by omega)).mono' h2)
      rw [(sForsTree_shape pad pp a0 a1 bit val c _).1, ← forsTreeBase_succ] at ht ⊢
      have hr := sForsTrees_nb hpb hpp ha0 ha1 hbn hvn m (c + 1) (by omega)
      rw [show c + 1 + m = c + (m + 1) by omega] at hr
      exact (ht.mono (forsTreeBase_mono b0 (by omega))).append hr

/-- **The FORS trees complete** from tree `c`, `m` of them: tree `c + k`'s root is `fRootE` of its
secret and siblings. -/
theorem sForsTrees_complete {pad : Nat} {pp a0 a1 : V} {bit val : Nat → V} {b0 : Nat}
    {s : Nat → Nat} (hs : ∀ c < 24, s c < 2 ^ 10) {secret : Nat → E} {sib : Nat → Nat → E}
    (hpb : pad + 5 ≤ b0 + 2) (hpp : NBv (b0 + 2) pp) (ha0 : NBv (b0 + 2) a0) (ha1 : NBv (b0 + 2) a1)
    (hbn : ∀ k < 240, NBv (b0 + 2) (bit k)) (hvn : ∀ k < 240, NBv (b0 + 2) (val k)) :
    ∀ (m c : Nat) (σ : Val), c + m ≤ 24 → PadOK σ pad →
      (∀ c < 24, ∀ j < 10, σ (bit (10 * c + j)) = if (s c).testBit j then 1 else 0) →
      (∀ c < 24, ∀ j < 10, σ (val (10 * c + j)) = eOfNat (fIdx c j (s c))) →
      Completes C rd (forsTreeBase b0 c) (forsTreeBase b0 (c + m))
        (sForsTrees pad pp a0 a1 bit val m c (forsTreeBase b0 c)).1 σ
        (fun σ' => AgreeBelow (forsTreeBase b0 c) σ σ' ∧ (∀ k < m,
          σ' (.n (forsRootPos b0 (c + k))) =
            fRootE (σ pp) (σ a0) (σ a1) (c + k) (s (c + k)) (secret (c + k)) (sib (c + k))) ∧
          FallPops rd σ' (sForsTrees pad pp a0 a1 bit val m c (forsTreeBase b0 c)).1
            ((List.range m).flatMap fun k =>
              forsTreePops (σ pp) (σ a0) (σ a1) (c + k) (s (c + k)) (secret (c + k)) (sib (c + k))))
  | 0, c, σ, _, _, _, _ =>
      ⟨σ, Ext.refl _ _ _, ⟨fun _ _ => rfl, fun k hk => absurd hk (by omega), FallPops.nil⟩, fun _ _ hn => hn⟩
  | m + 1, c, σ, hcm, hp, hbit, hval => by
      have h2 : b0 + 2 ≤ forsTreeBase b0 c := forsTreeBase_ge b0 c
      rw [sForsTrees_succ]
      have ht := sForsTree_complete_pops (C := C) (rd := rd) (pad := pad) (pp := pp) (a0 := a0)
        (a1 := a1) (bit := bit) (val := val) (c := c) (s := s c) (b := forsTreeBase b0 c)
        (secret := secret c) (sib := sib c) (by omega) (hs c (by omega)) σ (by omega) (hpp.mono' h2)
        (ha0.mono' h2) (ha1.mono' h2) (fun j hj => (hbn _ (by omega)).mono' h2)
        (fun j hj => (hvn _ (by omega)).mono' h2) hp (hbit c (by omega))
        (hval c (by omega))
      have hnb := sForsTree_nb (pad := pad) (pp := pp) (a0 := a0) (a1 := a1) (bit := bit) (val := val)
        (c := c) (b := forsTreeBase b0 c) (by omega) (hpp.mono' h2) (ha0.mono' h2) (ha1.mono' h2)
        (fun j hj => (hbn _ (by omega)).mono' h2) (fun j hj => (hvn _ (by omega)).mono' h2)
      obtain ⟨e1, e2⟩ := sForsTree_shape pad pp a0 a1 bit val c (forsTreeBase b0 c)
      rw [e1, ← forsTreeBase_succ] at ht hnb ⊢
      rw [e2] at ht
      have hlt := forsRootPos_lt b0 c
      refine Completes.append (m := forsTreeBase b0 (c + 1))
        (forsTreeBase_mono b0 (by omega)) (forsTreeBase_mono b0 (by omega)) hnb ht
        (fun σ1 he1 ⟨hag1, hr1, hP1⟩ => ?_)
      have t1 : ∀ v, NBv (b0 + 2) v → σ1 v = σ v := fun v hv => hag1.apply (hv.mono' h2)
      have ih := sForsTrees_complete (secret := secret) (sib := sib) hs hpb hpp ha0 ha1 hbn hvn m (c + 1)
        σ1 (by omega) (hp.congr hpb fun j hj => (t1 (.n j) ⟨j, hj, rfl⟩).symm)
        (fun c hc j hj => by rw [t1 _ (hbn _ (by omega))]; exact hbit c hc j hj)
        (fun c hc j hj => by rw [t1 _ (hvn _ (by omega))]; exact hval c hc j hj)
      rw [show c + 1 + m = c + (m + 1) by omega] at ih
      refine ih.mono le_rfl le_rfl (fun σ' ⟨hag', hr', hP'⟩ => ⟨?_, ?_, ?_⟩)
      · have hmono := forsTreeBase_mono b0 (Nat.le_succ c)
        exact fun j hj => (hag1 j hj).trans (hag' j (by omega))
      · intro k hk
        rcases k with _ | k
        · rw [Nat.add_zero, ← hag' _ hlt.1, ← hr1]
          simp [forsRootPos]
        · rw [show c + (k + 1) = c + 1 + k by omega, hr' k (by omega), t1 _ hpp, t1 _ ha0,
            t1 _ ha1]
      · rw [t1 _ hpp, t1 _ ha0, t1 _ ha1] at hP'
        refine FallPops.congr_pops ((hP1.agree hnb hag').append hP') ?_
        rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
        simp only [Nat.add_zero, show ∀ k, c + 1 + k = c + (k + 1) from fun k => by omega]

/-! ## The FORS key -/

/-- The FORS block after its trees, over any trees' statements `tr` ending at `b0 + 3802` with
their roots at `forsRootPos`: `roots_at`, then `T_k`. -/
theorem forsKey_complete_gen {pad : Nat} {pp a0 key : V} {b0 : Nat} (tr : List Stmt × Nat × List V)
    (ht1 : tr.2.1 = b0 + 3802) (ht2 : tr.2.2 = (List.range 24).map fun k => V.n (forsRootPos b0 (0 + k)))
    (hnb : NumBelow (b0 + 3802) (Stmt.valsList tr.1)) (σ : Val) (hp : PadOK σ pad)
    (hpb : pad + 5 ≤ b0) (hpp : NBv b0 pp) (ha0 : NBv b0 a0) (hkey : NBv b0 key) {roots : Nat → E}
    {Q : Val → Prop} (hQ : ∀ σ σ', AgreeBelow (b0 + 3802) σ σ' → Q σ → Q σ')
    (htr : ∀ σ1, AgreeBelow b0 σ σ1 → σ1 (.n (b0 + 1)) = σ key + lit (3 * 2 ^ 24) →
      Completes C rd (b0 + 2) (b0 + 3802) tr.1 σ1
        (fun σ' => AgreeBelow (b0 + 2) σ1 σ' ∧ (∀ k < 24, σ' (.n (forsRootPos b0 (0 + k))) = roots k) ∧
          Q σ')) :
    Completes C rd b0
      (kMsg pad (([pp, a0, .n (tr.2.1 + 1)] ++ tr.2.2).map KC.cell) 432 true none (tr.2.1 + 2)).2.1
      ([cst b0 (lit (3 * 2 ^ 24)), addS (.n (b0 + 1)) key (.n b0)] ++ tr.1 ++
        [cst tr.2.1 (lit (4 * 2 ^ 24)), addS (.n (tr.2.1 + 1)) key (.n tr.2.1)] ++
        (kMsg pad (([pp, a0, .n (tr.2.1 + 1)] ++ tr.2.2).map KC.cell) 432 true none (tr.2.1 + 2)).1) σ
      (fun σ' => AgreeBelow b0 σ σ' ∧
        σ' (.n (kMsg pad (([pp, a0, .n (tr.2.1 + 1)] ++ tr.2.2).map KC.cell) 432 true none
          (tr.2.1 + 2)).2.2) =
        (hcell ([σ pp, σ a0, σ key + lit (4 * 2 ^ 24)] ++ (List.range 24).map roots)).1 ∧ Q σ') := by
  rw [ht1, ht2]
  simp only [List.append_assoc]
  set vs : List V := [pp, a0, .n (b0 + 3802 + 1)] ++
    (List.range 24).map fun k => V.n (forsRootPos b0 (0 + k)) with hvs
  have hroot_lt : ∀ k < 24, forsRootPos b0 (0 + k) < b0 + 3802 ∧ b0 + 2 ≤ forsRootPos b0 (0 + k) := by
    intro k hk
    have h1 := forsRootPos_lt b0 (0 + k)
    have h2 := forsTreeBase_mono b0 (show 0 + k + 1 ≤ 0 + 24 by omega)
    have h3 := forsTreeBase_ge b0 (0 + k)
    rw [forsTreeBase_24] at h2
    omega
  have hvsb : ∀ c ∈ vs.map KC.cell, KCb (b0 + 3802 + 2) c := by
    intro c hc
    simp only [hvs, List.map_cons, List.cons_append, List.nil_append,
      List.mem_cons, List.mem_map, List.mem_range] at hc
    rcases hc with rfl | rfl | rfl | ⟨w, ⟨k, hk, rfl⟩, rfl⟩
    · exact hpp.mono' (by omega)
    · exact ha0.mono' (by omega)
    · exact ⟨b0 + 3802 + 1, by omega, rfl⟩
    · exact ⟨_, by have := hroot_lt k hk; omega, rfl⟩
  have hs1 : SeqOK b0 [cst b0 (lit (3 * 2 ^ 24)), addS (.n (b0 + 1)) key (.n b0)] (b0 + 2) :=
    ⟨rfl, ⟨rfl, hkey.mono' (by omega), ⟨b0, by omega, rfl⟩⟩, rfl⟩
  refine Completes.seqThen hs1 (by
      have := (kMsg_nb (pad := pad) (cells := vs.map KC.cell) (len := 432) (tailRun := true)
        (b := b0 + 3802 + 2) (by omega) hvsb).2
      omega) (fun σ1 he1 hA1 => ?_)
  have hag1 : AgreeBelow b0 σ σ1 := he1.agree
  have e1 : σ1 (.n (b0 + 1)) = σ key + lit (3 * 2 ^ 24) := by
    have a1 : σ1 (.n (b0 + 1)) = σ1 key + σ1 (.n b0) :=
      hA1.atom (a := .add (.n (b0 + 1)) _ _) (by simp [addS])
    have c0 : σ1 (.n b0) = lit (3 * 2 ^ 24) := hA1.atom (a := .const (.n b0) _) (by simp [cst])
    rw [a1, c0, hag1.apply hkey]
  refine Completes.append (m := b0 + 3802) (by omega) (by
      have := (kMsg_nb (pad := pad) (cells := vs.map KC.cell) (len := 432) (tailRun := true)
        (b := b0 + 3802 + 2) (by omega) hvsb).2
      omega) hnb ((htr σ1 hag1 e1).withExt) (fun σ2 he2 h2 => ?_)
  obtain ⟨⟨hag2, hr2, hq2⟩, -⟩ := h2
  have hs3 : SeqOK (b0 + 3802) [cst (b0 + 3802) (lit (4 * 2 ^ 24)),
      addS (.n (b0 + 3802 + 1)) key (.n (b0 + 3802))] (b0 + 3802 + 2) :=
    ⟨rfl, ⟨rfl, hkey.mono' (by omega), ⟨b0 + 3802, by omega, rfl⟩⟩, rfl⟩
  have t2 : ∀ v, NBv b0 v → σ2 v = σ v := fun v hv =>
    (hag2.apply (hv.mono' (by omega))).trans (hag1.apply hv)
  refine Completes.seqThen hs3 (by
      have := (kMsg_nb (pad := pad) (cells := vs.map KC.cell) (len := 432) (tailRun := true)
        (b := b0 + 3802 + 2) (by omega) hvsb).2
      omega) (fun σ3 he3 hA3 => ?_)
  have hag3 : AgreeBelow (b0 + 3802) σ2 σ3 := he3.agree
  have e3 : σ3 (.n (b0 + 3802 + 1)) = σ key + lit (4 * 2 ^ 24) := by
    have a1 : σ3 (.n (b0 + 3802 + 1)) = σ3 key + σ3 (.n (b0 + 3802)) :=
      hA3.atom (a := .add (.n (b0 + 3802 + 1)) _ _) (by simp [addS])
    have c0 : σ3 (.n (b0 + 3802)) = lit (4 * 2 ^ 24) :=
      hA3.atom (a := .const (.n (b0 + 3802)) _) (by simp [cst])
    rw [a1, c0, hag3.apply (hkey.mono' (by omega)), t2 _ hkey]
  have hval3 : vs.map σ3 = [σ pp, σ a0, σ key + lit (4 * 2 ^ 24)] ++ (List.range 24).map roots := by
    simp only [hvs, List.map_cons, List.map_map, Function.comp_def,
      List.cons_append, List.nil_append, e3, List.cons.injEq, true_and]
    refine ⟨by rw [hag3.apply (hpp.mono' (by omega)), t2 _ hpp],
      by rw [hag3.apply (ha0.mono' (by omega)), t2 _ ha0], ?_⟩
    refine List.map_congr_left fun k hk => ?_
    have hk24 := List.mem_range.mp hk
    rw [hag3.apply ⟨_, (hroot_lt k hk24).1, rfl⟩, hr2 k hk24]
  have hp3 : PadOK σ3 pad := hp.congr hpb fun j hj => by
    rw [← hag3 j (by omega), t2 (.n j) ⟨j, hj, rfl⟩]
  obtain ⟨hk, -, -⟩ := kMsg_complete (C := C) (rd := rd) σ3 hp3 (b := b0 + 3802 + 2)
    (cells := vs.map KC.cell) (len := 432) (tailRun := true) (by omega)
    hvsb
    (fun _ => tailCells_of_cells (by simp [hvs]) (by norm_num))
  refine (hk.withAtoms (kMsg_atoms ..)).withExt.mono le_rfl le_rfl
    (fun σ4 ⟨⟨_, hA4⟩, he4⟩ => ⟨?_, ?_, ?_⟩)
  · have hag4 : AgreeBelow (b0 + 3802 + 2) σ3 σ4 := he4.agree
    exact fun j hj => (hag1 j hj).trans ((hag2 j (by omega)).trans ((hag3 j (by omega)).trans
      (hag4 j (by omega))))
  · have hag4 : AgreeBelow (b0 + 3802 + 2) σ3 σ4 := he4.agree
    have hp4 : PadOK σ4 pad := hp3.congr (by omega) hag4
    have hK := kMsg_cells_sound (vs := vs) (len := 432) hp4 (by simp [hvs]) (fun _ => by simp [hvs])
      hA4
    rw [hK, ← hval3]
    congr 2
    exact List.map_congr_left fun v hv => hag4.apply (hvsb _ (List.mem_map_of_mem hv))
  · have hag4 : AgreeBelow (b0 + 3802 + 2) σ3 σ4 := he4.agree
    exact hQ σ2 σ4 (fun j hj => (hag3 j hj).trans (hag4 j (by omega))) hq2

/-- **The FORS block completes** (its statements as `sForsBlock_eq` gives them) from `b0` (`fors_at`, the 24 trees at the leaves `s c` with their
secrets and siblings hinted, `T_k`): the FORS key is `T_k` of the roots `fRootE`. -/
theorem sForsBlock_complete {pad : Nat} {pp a0 key : V} {bit val : Nat → V} {b0 : Nat}
    {s : Nat → Nat} (hs : ∀ c < 24, s c < 2 ^ 10) {secret : Nat → E} {sib : Nat → Nat → E}
    (σ : Val) (hp : PadOK σ pad) (hpb : pad + 5 ≤ b0)
    (hpp : NBv b0 pp) (ha0 : NBv b0 a0) (hkey : NBv b0 key) (hbn : ∀ k < 240, NBv b0 (bit k))
    (hvn : ∀ k < 240, NBv b0 (val k))
    (hbit : ∀ c < 24, ∀ j < 10, σ (bit (10 * c + j)) = if (s c).testBit j then 1 else 0)
    (hval : ∀ c < 24, ∀ j < 10, σ (val (10 * c + j)) = eOfNat (fIdx c j (s c))) :
    Completes C rd b0 (kMsg pad (([pp, a0, .n ((sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.1 + 1)] ++
        (sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.2).map KC.cell) 432 true none ((sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.1 + 2)).2.1
      ([cst b0 (lit (3 * 2 ^ 24)), addS (.n (b0 + 1)) key (.n b0)] ++ (sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).1 ++
        [cst (sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.1 (lit (4 * 2 ^ 24)),
          addS (.n ((sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.1 + 1)) key (.n (sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.1)] ++
        (kMsg pad (([pp, a0, .n ((sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.1 + 1)] ++
        (sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.2).map KC.cell) 432 true none ((sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.1 + 2)).1) σ
      (fun σ' => AgreeBelow b0 σ σ' ∧ σ' (.n (kMsg pad (([pp, a0, .n ((sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.1 + 1)] ++
        (sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.2).map KC.cell) 432 true none ((sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).2.1 + 2)).2.2) =
          (hcell ([σ pp, σ a0, σ key + lit (4 * 2 ^ 24)] ++ (List.range 24).map fun c =>
            fRootE (σ pp) (σ a0) (σ key + lit (3 * 2 ^ 24)) c (s c) (secret c) (sib c))).1 ∧
        FallPops rd σ' (sForsBlock pad pp a0 key bit val b0).1 ((List.range 24).flatMap fun c =>
          forsTreePops (σ pp) (σ a0) (σ key + lit (3 * 2 ^ 24)) c (s c) (secret c) (sib c))) := by
  obtain ⟨t1, t2⟩ := sForsTrees_shape pad pp a0 (.n (b0 + 1)) bit val b0 24 0
  have e0 : forsTreeBase b0 0 = b0 + 2 := by simp [forsTreeBase]
  have e24 : forsTreeBase b0 (0 + 24) = b0 + 3802 := forsTreeBase_24 b0
  rw [e0, e24] at t1
  rw [e0] at t2
  have hnb := sForsTrees_nb (pad := pad) (pp := pp) (a0 := a0) (a1 := .n (b0 + 1)) (bit := bit)
    (val := val) (b0 := b0) (by omega) (hpp.mono' (by omega)) (ha0.mono' (by omega))
    ⟨b0 + 1, by omega, rfl⟩ (fun k hk => (hbn k hk).mono' (by omega))
    (fun k hk => (hvn k hk).mono' (by omega)) 24 0 (by norm_num)
  rw [e0, e24] at hnb
  have htrees : ∀ σ1, AgreeBelow b0 σ σ1 → σ1 (.n (b0 + 1)) = σ key + lit (3 * 2 ^ 24) →
      Completes C rd (b0 + 2) (b0 + 3802)
        (sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).1 σ1
        (fun σ' => AgreeBelow (b0 + 2) σ1 σ' ∧ (∀ k < 24, σ' (.n (forsRootPos b0 (0 + k))) =
          fRootE (σ pp) (σ a0) (σ key + lit (3 * 2 ^ 24)) k (s k) (secret k) (sib k)) ∧
          FallPops rd σ' (sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)).1
            ((List.range 24).flatMap fun c =>
              forsTreePops (σ pp) (σ a0) (σ key + lit (3 * 2 ^ 24)) c (s c) (secret c) (sib c))) := by
    intro σ1 hag1 e1
    have t1' : ∀ v, NBv b0 v → σ1 v = σ v := fun v hv => hag1.apply hv
    have htr := sForsTrees_complete (C := C) (rd := rd) (pad := pad) (pp := pp) (a0 := a0)
      (a1 := .n (b0 + 1)) (bit := bit) (val := val) (b0 := b0) (secret := secret) (sib := sib) hs (by omega)
      (hpp.mono' (by omega)) (ha0.mono' (by omega)) ⟨b0 + 1, by omega, rfl⟩
      (fun k hk => (hbn k hk).mono' (by omega)) (fun k hk => (hvn k hk).mono' (by omega)) 24 0 σ1
      (by norm_num) (hp.congr hpb hag1)
      (fun c hc j hj => by rw [t1' _ (hbn _ (by omega))]; exact hbit c hc j hj)
      (fun c hc j hj => by rw [t1' _ (hvn _ (by omega))]; exact hval c hc j hj)
    rw [e0, e24] at htr
    refine htr.mono le_rfl le_rfl (fun σ' ⟨hag', hr', hP'⟩ => ⟨hag', fun k hk => ?_, ?_⟩)
    · rw [hr' k hk, t1' _ hpp, t1' _ ha0, e1]
      simp only [Nat.zero_add]
    · rw [t1' _ hpp, t1' _ ha0, show σ1 (.n (b0 + 1)) = _ from e1] at hP'
      simpa only [Nat.zero_add] using hP'
  refine (forsKey_complete_gen (roots := fun c =>
      fRootE (σ pp) (σ a0) (σ key + lit (3 * 2 ^ 24)) c (s c) (secret c) (sib c))
    _ t1 t2 hnb σ hp hpb hpp ha0 hkey (fun _ _ hab hq => hq.agree hnb hab) htrees).mono le_rfl le_rfl
    (fun σ' ⟨hag, hk, hP⟩ => ⟨hag, hk, ?_⟩)
  have sh : ∀ {α : Type} (F : List α), [] ++ F ++ [] ++ [] = F := by intros; simp
  rw [sForsBlock_eq]
  exact FallPops.congr_pops ((((fallPops_quiet σ' rfl).append hP).append (fallPops_quiet σ' rfl)).append
    (fallPops_quiet σ' (kMsg_quiet _ _ _ _ _ _ _))) (sh _)

end
end LeanVM.Guest.B1.Sig
