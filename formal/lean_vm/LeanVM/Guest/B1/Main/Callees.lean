/-
  LeanVM.Guest.B1.Main.Callees

  `main`'s callee contracts from the callees' statements: witness functions exist for which
  `CalleesW` holds, so a run of `main` establishes `NodeRelation` of some witness.
-/

module

public import LeanVM.Guest.B1.Main.Final

/-!
# The callees' contracts, from their statements

`callees_exist`: from the signature verifiers' soundness statements (B1-e's
`verify_lean_xmss_sound_Spec`, `verify_sig_lean_sphincs_sound_Spec`), `verify_sub`'s (in the shape
of B1-d's `MeaningVerifySub`, `SubSound`), and this family's `da_verify_sound_Spec` and
`aggregate_claims_sound_Spec`, witness functions exist (into the signature and proof types,
inhabited) with `CalleesW` (chosen: the decoder that
reads them off memory is the end theorem's). `main_sound_exists`: a run of `main` then decodes to
a statement of the public input's digest and some witness holding it.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-- `verify_sub`'s soundness in the shape `main` reads it (B1-d's `verify_sub_Spec` gives it):
every call with the exponent tables has a proof that `VerifySubOut` describes. -/
def SubSound (bytecode : List K) : Prop :=
  ∀ (rd : Reader), MemOk rd → ∀ pi0 pi1 s0 s1 gsq out,
    coreProgram.Rel rd "verify_sub" [pi0, pi1, s0, s1, gsq, out] [] → ExpTables rd gsq →
      ∃ π, VerifySubOut bytecode rd [pi0, pi1, s0, s1, gsq, out] π

/-- **Witness functions for `main`'s callees exist.** -/
theorem callees_exist [Nonempty LeanXmss.Signature] [Nonempty Sphincs.Signature] [Nonempty Proof]
    {bytecode : List K} {sx : Val → LeanXmss.Signature}
    {ss : Val → FrameMap → Sphincs.Signature} (hx : Sig.verify_lean_xmss_sound_Spec sx)
    (hs : Sig.verify_sig_lean_sphincs_sound_Spec ss) (hv : SubSound bytecode)
    (hd : Da.da_verify_sound_Spec) (ha : aggregate_claims_sound_Spec) {rd : Reader}
    (hm : MemOk rd) :
    ∃ (wX : List E → LeanXmss.Signature) (wS : E → Sphincs.Signature)
      (wD : List E → List E → LeanVM.Da.MatrixWitness) (wV : List E → Proof)
      (wA : List E → BatchingHints), CalleesW bytecode rd wX wS wD wV wA := by
  classical
  obtain ⟨κ, h16, hκ, L, rfl⟩ := hm
  have hm' : MemOk L.read := ⟨κ, h16, hκ, L, rfl⟩
  -- the signatures
  have ex : ∀ args, ∃ sig, coreProgram.Rel L.read "__loop2" args [] →
      Loop2Out (coreProgram.Rel L.read) L.read args sig := by
    intro args
    by_cases h : coreProgram.Rel L.read "__loop2" args []
    · obtain ⟨σ, hp, hb⟩ := (Sig.rel_iff_body find_loop2 args []).mp h
      exact ⟨sx σ, fun _ => loop2Out_of_body hx hp hb⟩
    · exact ⟨Classical.ofNonempty, fun h' => absurd h' h⟩
  have es : ∀ p, ∃ sig, ∀ bb, coreProgram.Rel L.read "verify_sig_lean_sphincs" [p, bb] [] →
      Sig.ByteBits L.read bb → Sig.SphincsOut L.read p sig := by
    intro p
    by_cases h : ∃ bb, coreProgram.Rel L.read "verify_sig_lean_sphincs" [p, bb] [] ∧
        Sig.ByteBits L.read bb
    · obtain ⟨bb, hr, hbb⟩ := h
      obtain ⟨p', bb', hp, -, hsig⟩ := Sig.verify_sig_lean_sphincs_signed hs hκ hr
      simp only [List.cons.injEq, and_true] at hp
      obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨sig, hsig⟩ := hsig hbb
      exact ⟨sig, fun _ _ _ => hsig⟩
    · exact ⟨Classical.ofNonempty, fun bb hr hbb => absurd ⟨bb, hr, hbb⟩ h⟩
  -- the matrix
  have edd : ∀ args rets : List E, ∃ w : LeanVM.Da.MatrixWitness, ∀ gsq, args = [gsq] →
      coreProgram.Rel L.read "da_verify" [gsq] rets → Da.SquaresAt L.read gsq →
      ∃ (root : Digest) (z : E), w.Opens root z ∧ rets = digestCells root ++ [z] := by
    intro args rets
    by_cases h : ∃ gsq, args = [gsq] ∧ coreProgram.Rel L.read "da_verify" [gsq] rets ∧
        Da.SquaresAt L.read gsq
    · obtain ⟨gsq, rfl, hr, hsq⟩ := h
      obtain ⟨w, root, z, hop, hrets⟩ := hd L.read hm' [gsq] rets hr hsq
      exact ⟨w, fun g hg _ _ => by
        simp only [List.cons.injEq, and_true] at hg
        subst hg
        exact ⟨root, z, hop, hrets⟩⟩
    · exact ⟨⟨[]⟩, fun g hg hr hsq => absurd ⟨g, hg, hr, hsq⟩ h⟩
  -- the proofs
  have ev : ∀ args : List E, ∃ π : Proof, ∀ pi0 pi1 s0 s1 gsq out,
      args = [pi0, pi1, s0, s1, gsq, out] →
      coreProgram.Rel L.read "verify_sub" args [] → ExpTables L.read gsq →
      VerifySubOut bytecode L.read args π := by
    intro args
    by_cases h : ∃ pi0 pi1 s0 s1 gsq out, args = [pi0, pi1, s0, s1, gsq, out] ∧
        coreProgram.Rel L.read "verify_sub" args [] ∧ ExpTables L.read gsq
    · obtain ⟨pi0, pi1, s0, s1, gsq, out, rfl, hr, he⟩ := h
      obtain ⟨π, hπ⟩ := hv L.read hm' _ _ _ _ _ _ hr he
      exact ⟨π, fun _ _ _ _ _ _ _ _ _ => hπ⟩
    · exact ⟨Classical.ofNonempty, fun a b c d e f hargs hr he =>
        absurd ⟨a, b, c, d, e, f, hargs, hr, he⟩ h⟩
  -- the batching's hints
  have ea : ∀ args : List E, ∃ hints : BatchingHints, ∀ ncg cpi cfresh ccarried dst tabs,
      args = [ncg, cpi, cfresh, ccarried, dst, tabs] →
      coreProgram.Rel L.read "aggregate_claims" args [] → WinTabs L.read tabs →
      ∀ m, 1 ≤ m → m ≤ 16 → ncg = gen ^ m →
      ∃ out : DeferredClaim, out.bytecodePoint.length = bytecodeVars ∧
        ReadsAt L.read dst out.cells ∧ ∀ cs : List ChildClaims, cs.length = m →
          (∀ c (hc : c < cs.length), ChildWordsAt L.read cpi cfresh ccarried c cs[c]) →
          batch cs hints = some out := by
    intro args
    by_cases h : ∃ ncg cpi cfresh ccarried dst tabs m,
        args = [ncg, cpi, cfresh, ccarried, dst, tabs] ∧
        coreProgram.Rel L.read "aggregate_claims" args [] ∧ WinTabs L.read tabs ∧ 1 ≤ m ∧ m ≤ 16 ∧
        ncg = gen ^ m
    · obtain ⟨ncg, cpi, cfresh, ccarried, dst, tabs, m, rfl, hr, hw, h1, h16, hn⟩ := h
      obtain ⟨-, hints, out, hl, hrd, hb⟩ := ha L.read _ _ hr hw m h1 h16 hn
      refine ⟨hints, fun _ _ _ _ _ _ hargs _ _ m' h1' h16' hn' => ?_⟩
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
      have : m' = m := gen_pow_inj34 (by omega) (by omega) (hn'.symm.trans hn)
      subst this
      exact ⟨out, hl, hrd, hb⟩
    · exact ⟨⟨0, [], 0⟩, fun a b c d e t hargs hr hw m h1 h16 hn =>
        absurd ⟨a, b, c, d, e, t, m, hargs, hr, hw, h1, h16, hn⟩ h⟩
  choose wX hwX using ex
  choose wS hwS using es
  choose wD hwD using edd
  choose wV hwV using ev
  choose wA hwA using ea
  exact ⟨wX, wS, wD, wV, wA, fun args hr => hwX args hr, fun p bb hr hbb => hwS p bb hr hbb,
    fun gsq rets hr hsq => hwD [gsq] rets gsq rfl hr hsq,
    fun pi0 pi1 s0 s1 gsq out hr he => hwV _ _ _ _ _ _ _ rfl hr he,
    fun ncg cpi cfresh ccarried dst tabs hr hw m h1 h16 hn =>
      hwA _ _ _ _ _ _ _ rfl hr hw m h1 h16 hn⟩

/-- **A run of `main` decodes to a statement of the public input's digest, held by a witness.** -/
theorem main_sound_exists [Nonempty LeanXmss.Signature] [Nonempty Sphincs.Signature]
    [Nonempty Proof] {bytecode : List K} {sx : Val → LeanXmss.Signature}
    {ss : Val → FrameMap → Sphincs.Signature} (hx : Sig.verify_lean_xmss_sound_Spec sx)
    (hs : Sig.verify_sig_lean_sphincs_sound_Spec ss) (hv : SubSound bytecode)
    (hd : Da.da_verify_sound_Spec) (ha : aggregate_claims_sound_Spec)
    (hexp : exponent_tables_Spec) (hbl : bytecode.length = 2 ^ bytecodeVars) {rd : Reader} (hm : MemOk rd) {D : Digest}
    {σ : Val} (hp0 : LoadHolds rd 1 0 (digestHalves D).1) (hp1 : LoadHolds rd 1 1 (digestHalves D).2)
    (hb : Stmt.HoldsList (coreProgram.Rel rd) rd σ Data.core0.body False (fun rs => rs = [])) :
    statementDigest (decSeed σ) (decStmt σ rd) = D ∧
      ∃ w, NodeRelation bytecode (decSeed σ) (decStmt σ rd) w := by
  obtain ⟨wX, wS, wD, wV, wA, cw⟩ := callees_exist hx hs hv hd ha hm
  obtain ⟨h1, h2⟩ := main_sound_w hexp bytecode hbl rd hm wX wS wD wV wA cw D σ hp0 hp1 hb
  exact ⟨h1, _, h2⟩

end
end LeanVM.Guest.B1.Main
