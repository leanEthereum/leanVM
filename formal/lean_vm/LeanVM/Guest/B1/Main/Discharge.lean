/-
  LeanVM.Guest.B1.Main.Discharge

  `main`'s callees (`Callees`) from the other groups' B1 lemmas: the digests, the claim lists, the
  DA root list and cover, `verify_lean_xmss`, and `verify_sub` from its own pieces.
-/

module

public import LeanVM.Guest.B1.Main.Sound
public import LeanVM.Guest.B1.Digest.Statement
public import LeanVM.Guest.B1.Digest.ClaimList
public import LeanVM.Guest.B1.Digest.ChildList
public import LeanVM.Guest.B1.Da.ListDigest
public import LeanVM.Guest.B1.Sig.Xmss
public import LeanVM.Guest.B1.Sig.XmssData
public import LeanVM.Guest.B1.VerifySub.Sound
public import LeanVM.Guest.B1.Tables.All
public import LeanVM.Guest.B1.Tables.TCtx
public import LeanVM.Guest.B1.Sig.Sphincs
public import LeanVM.Guest.B1.Sig.SphincsData
public import LeanVM.Guest.B1.Da.Verify
public import LeanVM.Guest.B1.Tables.VerifyTablesSound
public import LeanVM.Guest.B1.Whir.Stacked

/-!
# `main`'s callees, discharged

Each field of `Callees` is the owning group's lemma, restated: group 3's `Meaning_*` with their
scratch tables and canonicity dropped and `da_verify_sound`, group 2's `verify_lean_xmss_sound` and
`verify_sig_lean_sphincs_sound` read through the claim's cells, group 6's `verify_sub_sound` with
group 5's placement (`PCtx`, `hypKappa`, `soundPlace`), `verify_bus_gkr_sound`,
`verify_flock_sound` and `check_opening_terminal_sound`. `CalleesPending` holds the last two,
`verify_tables` (`SoundTables` with the terminal's `TCtx`) and `open_stacked` (`SoundOpen`);
`callees_all` gives `Callees` on every memory `MemOk` admits from them, the form
`End.B1Sound.callees` takes, and `callees_proved` discharges them (group 5's
`verify_tables_sound`, group 4's `soundOpen`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

variable {rd : Reader}

theorem memOk_digest (hm : MemOk rd) : Digest.MemOk rd := hm

theorem squaresAt_of_table {q : E} (h : SquaresTable rd q) : Digest.SquaresAt rd q :=
  fun j hj => h j (by unfold sizeBits; omega)

theorem statement_digest_sound : ∀ seed0 seed1 sigp da0 da1 dp d0 d1,
    coreProgram.Rel rd "statement_digest" [seed0, seed1, sigp, da0, da1, dp] [d0, d1] →
      ∃ (seed sig da : Digest) (cells : List E), cells.length = 53 ∧
        (seed0, seed1) = digestScalars seed ∧ LoadHolds rd sigp 0 (digestScalars sig).1 ∧
        LoadHolds rd sigp 1 (digestScalars sig).2 ∧ (da0, da1) = digestScalars da ∧
        ReadsAt rd dp cells ∧ (d0, d1) = digestScalars (stmtDigestOf seed sig da cells) := by
  intro seed0 seed1 sigp da0 da1 dp d0 d1 h
  obtain ⟨_, _, _, _, _, _, _, _, ha, hr, seed, sig, da, cells, h1, h2, h3, h4, h5, h6, h7⟩ :=
    (statement_digest_iff rd _ _).mp h
  simp only [List.cons.injEq, and_true] at ha hr
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := ha
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨seed, sig, da, cells, h1, h2, h3, h4, h5, h6, h7⟩

theorem claim_list_digest_sound (hm : MemOk rd) : ∀ p n_g gsq d0 d1, SquaresTable rd gsq →
    coreProgram.Rel rd "claim_list_digest" [p, n_g, gsq] [d0, d1] →
      ∃ n < 2 ^ 16, n_g = gen ^ n ∧ ∃ cs : List E, cs.length = 4 * n ∧ ReadsAt rd p cs ∧
        (d0, d1) = digestScalars (blake2sBytes (cs.flatMap cellBytes)) := by
  intro p n_g gsq d0 d1 hT h
  obtain ⟨_, _, _, _, _, ha, hr, n, hn, hng, cs, hl, hc, -, hd, -⟩ :=
    (claim_list_digest_iff (memOk_digest hm) (squaresAt_of_table hT) _ _ _).mp h
  simp only [List.cons.injEq, and_true] at ha hr
  obtain ⟨rfl, rfl, rfl⟩ := ha
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨n, hn, hng, cs, hl, hc, hd⟩

theorem child_claim_list_digest_sound (hm : MemOk rd) :
    ∀ entries cover base origin limit n_g gsq d0 d1, SquaresTable rd gsq →
      coreProgram.Rel rd "child_claim_list_digest" [entries, cover, base, origin, limit, n_g, gsq]
        [d0, d1] →
      ∃ n < 2 ^ 16, n_g = gen ^ n ∧ ∃ (off : ℕ → ℕ) (cs : List E), cs.length = 4 * n ∧
        ChildReads rd entries cover base origin limit off cs n ∧
        (d0, d1) = digestScalars (blake2sBytes (cs.flatMap cellBytes)) := by
  intro entries cover base origin limit n_g gsq d0 d1 hT h
  obtain ⟨_, _, _, _, _, _, _, _, _, ha, hr, n, hn, hng, off, cs, hl, hc, -, hd, -⟩ :=
    child_claim_list_digest_fwd (memOk_digest hm) (squaresAt_of_table hT) h
  simp only [List.cons.injEq, and_true] at ha hr
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ha
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨n, hn, hng, off, cs, hl, hc, hd⟩

theorem da_list_digest_sound : ∀ roots n_g d0 d1,
    coreProgram.Rel rd "da_list_digest" [roots, n_g] [d0, d1] →
      ∃ claims : List DaClaim, claims.length ≤ 16 ∧ n_g = gen ^ claims.length ∧
        DaClaimsAt rd roots claims ∧ (d0, d1) = digestScalars (daListDigest claims) := by
  intro roots n_g d0 d1 h
  obtain ⟨_, _, _, _, ha, hr, claims, h1, h2, h3, h4⟩ := (da_list_digest_iff rd _ _).mp h
  simp only [List.cons.injEq, and_true] at ha hr
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨claims, h1, h2, h3, h4⟩

theorem cover_da_root_sound' (hm : MemOk rd) : ∀ roots cover nslots mark r0 r1 r2 r3,
    coreProgram.Rel rd "cover_da_root" [roots, cover, nslots, mark] [r0, r1, r2, r3] →
      ∃ i M, M < 2 ^ 33 ∧ i < M ∧ nslots = gen ^ M ∧ LoadHolds rd (cover * gen ^ i) 0 mark ∧
        ReadsAt rd (roots * gen ^ (4 * i)) [r0, r1, r2, r3] := by
  intro roots cover nslots mark r0 r1 r2 r3 h
  obtain ⟨_, _, _, _, _, _, _, _, ha, hr, i, M, h1, h2, h3, h4, h5⟩ :=
    cover_da_root_sound (memOk_digest hm) h
  simp only [List.cons.injEq, and_true] at ha hr
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ha
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
  exact ⟨i, M, h1, h2, h3, h4, h5⟩

theorem cellPairVal_cellOf (m : BitVec 256) :
    cellPairVal (Sig.cellOf (m.extractLsb' 0 128)) (Sig.cellOf (m.extractLsb' 128 128)) = m := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_cellPairVal, show cellNat = Sig.cellNat from rfl, Sig.cellNat_cellOf, Sig.cellNat_cellOf,
    BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow]
  have := m.isLt
  rw [Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by norm_num at this ⊢; omega))]
  have := Nat.mod_add_div m.toNat (2 ^ 128)
  omega

theorem verify_lean_xmss_signed : ∀ p, coreProgram.Rel rd "verify_lean_xmss" [p] [] →
    XmssSigned rd p := by
  intro p h
  rw [rel_iff_sem Sig.find_verify_lean_xmss] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨-, pk, m, hc, sig, hv⟩ := Sig.verify_lean_xmss_sound h
  rw [hp] at hc
  refine ⟨_, _, _, _, readsAt_four.mpr ⟨hc 0, hc 1, hc 2, hc 3⟩, sig, ?_⟩
  have e : xmssOf (claimCells pk.root pk.parameter m 0) (claimCells pk.root pk.parameter m 1)
      (claimCells pk.root pk.parameter m 2) (claimCells pk.root pk.parameter m 3) = (pk, m) := by
    simp only [xmssOf, claimCells, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    exact Prod.ext (congrArg₂ LeanXmss.PublicKey.mk (Sig.cellVal_cellOf _) (Sig.cellVal_cellOf _))
      (cellPairVal_cellOf m)
  rw [e]
  exact hv

theorem verify_sig_lean_sphincs_signed : ∀ p,
    coreProgram.Rel rd "verify_sig_lean_sphincs" [p] [] → SphincsSigned rd p := by
  intro p h
  rw [rel_iff_sem Sig.find_verify_sig_lean_sphincs] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨-, pk, m, hc, sig, hv⟩ := Sig.verify_sig_lean_sphincs_sound Sig.fkSound_rel h
  rw [hp] at hc
  refine ⟨_, _, _, _, readsAt_four.mpr ⟨hc 0, hc 1, hc 2, hc 3⟩, sig, ?_⟩
  have e : sphincsOf (claimCells pk.root pk.parameter m 0) (claimCells pk.root pk.parameter m 1)
      (claimCells pk.root pk.parameter m 2) (claimCells pk.root pk.parameter m 3) = (pk, m) := by
    simp only [sphincsOf, claimCells, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    exact Prod.ext (congrArg₂ Sphincs.PublicKey.mk (Sig.cellVal_cellOf _) (Sig.cellVal_cellOf _))
      (cellPairVal_cellOf m)
  rw [e]
  exact hv

theorem da_verify_opens (hm : MemOk rd) : ∀ gsq r0 r1 v0 v1, SquaresTable rd gsq →
    coreProgram.Rel rd "da_verify" [gsq] [r0, r1, v0, v1] →
      ∃ (root vd : Digest) (w : Da.Witness), (r0, r1) = digestScalars root ∧
        (v0, v1) = digestScalars vd ∧ w.Opens root vd :=
  fun _ _ _ _ _ hT h => da_verify_sound (memOk_digest hm) (squaresAt_of_table hT) h

/-- **`main`'s callees**, from the other groups' lemmas, given those not proved yet. -/
theorem callees_of {bytecode : List K} (hm : MemOk rd)
    (hsph : ∀ p, coreProgram.Rel rd "verify_sig_lean_sphincs" [p] [] → SphincsSigned rd p)
    (hda : ∀ gsq r0 r1 v0 v1, SquaresTable rd gsq →
      coreProgram.Rel rd "da_verify" [gsq] [r0, r1, v0, v1] →
        ∃ (root vd : Digest) (w : Da.Witness), (r0, r1) = digestScalars root ∧
          (v0, v1) = digestScalars vd ∧ w.Opens root vd)
    (hvs : ∀ pi0 pi1 s0 s1 glp gsq out, ExpTables rd glp gsq →
      coreProgram.Rel rd "verify_sub" [pi0, pi1, s0, s1, glp, gsq, out] [] →
        ∃ (pi iv : Digest) (fresh : FixedClaims) (π : Proof), (pi0, pi1) = digestScalars pi ∧
          (s0, s1) = digestScalars iv ∧ FreshShaped fresh ∧ ReadsAt rd out (fixedCells fresh) ∧
          verifyDeferred bytecode iv pi fresh π = true) :
    Callees bytecode rd where
  verify_lean_xmss := verify_lean_xmss_signed
  verify_sig_lean_sphincs := hsph
  statement_digest := statement_digest_sound
  claim_list_digest := claim_list_digest_sound hm
  child_claim_list_digest := child_claim_list_digest_sound hm
  da_list_digest := da_list_digest_sound
  cover_da_root := cover_da_root_sound' hm
  da_verify := hda
  verify_sub := hvs

/-- `verify_sub`, soundly, in `Callees`' shape, on a memory of `2^κ` words, from its callees'. -/
theorem verify_sub_callee {bytecode : List K} (hb : bytecode.length = 2 ^ 22)
    {TCtx : Reader → Verifier.Layout → BusResult → List ColumnClaim → List E → Prop} (hm : MemOk rd)
    (hgkr : VerifySub.SoundGkr rd) (htab : VerifySub.SoundTables bytecode TCtx rd)
    (hfl : VerifySub.SoundFlock rd) (hop : VerifySub.SoundOpen rd)
    (hterm : VerifySub.SoundTerm TCtx PCtx rd) :
    ∀ pi0 pi1 s0 s1 glp gsq out, ExpTables rd glp gsq →
      coreProgram.Rel rd "verify_sub" [pi0, pi1, s0, s1, glp, gsq, out] [] →
        ∃ (pi iv : Digest) (fresh : FixedClaims) (π : Proof), (pi0, pi1) = digestScalars pi ∧
          (s0, s1) = digestScalars iv ∧ FreshShaped fresh ∧ ReadsAt rd out (fixedCells fresh) ∧
          verifyDeferred bytecode iv pi fresh π = true := by
  intro pi0 pi1 s0 s1 glp gsq out ht h
  obtain ⟨κ, h16, h32, L, rfl⟩ := hm
  obtain ⟨iv, pi, c, π, hs, hpi, hv, hsh, hr⟩ :=
    VerifySub.verify_sub_sound (args := [pi0, pi1, s0, s1, glp, gsq, out]) h32 (by omega) L hb hgkr
      htab hfl (soundPlace h32 L) (hypKappa _) hop hterm ht h
  exact ⟨pi, iv, c, π, hpi, hs, hsh, hr, hv⟩

/-- **What `main`'s callees rest on last**: `verify_sub`'s callees `verify_tables` (with the
terminal's context `TCtx`, group 5a) and `open_stacked` (group 4), on every memory `MemOk`
admits. -/
structure CalleesPending (bytecode : List K) : Prop where
  tables : ∀ rd, MemOk rd → VerifySub.SoundTables bytecode VerifySub.TCtx rd
  opening : ∀ rd, MemOk rd → VerifySub.SoundOpen rd

/-- **`main`'s callees on every memory** (`End.B1Sound.callees`), given what they still rest on. -/
theorem callees_all {bytecode : List K} (hb : bytecode.length = 2 ^ 22)
    (P : CalleesPending bytecode) : ∀ rd, MemOk rd → Callees bytecode rd := fun rd hm =>
  callees_of hm verify_sig_lean_sphincs_signed (da_verify_opens hm)
    (verify_sub_callee hb hm
      (by obtain ⟨κ, -, h32, L, rfl⟩ := hm; exact VerifySub.verify_bus_gkr_sound h32 L)
      (P.tables rd hm) (verify_flock_sound rd) (P.opening rd hm) (check_opening_terminal_sound rd))

/-- **`main`'s callees on every memory**, nothing assumed (`End.B1Sound.callees`). -/
theorem callees_proved {bytecode : List K} (hb : bytecode.length = 2 ^ 22) :
    ∀ rd, MemOk rd → Callees bytecode rd :=
  callees_all hb
    { tables := fun rd hm => by
        obtain ⟨κ, -, h32, L, rfl⟩ := hm
        exact VerifySub.verify_tables_sound h32 L hb
      opening := fun rd _ => soundOpen rd }

end
end LeanVM.Guest.B1.Main
