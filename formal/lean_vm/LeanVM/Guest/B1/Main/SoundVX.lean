/-
  LeanVM.Guest.B1.Main.SoundVX

  `main`, soundly, its witness decoded from the frame map, for any reader of the leanXMSS
  signature off `__loop2`'s frames whose segment statement holds.
-/

module

public import LeanVM.Guest.B1.Main.Callees
public import LeanVM.Guest.B1.Main.Aggregate
public import LeanVM.Guest.B1.VerifySub.Interface
public import LeanVM.Guest.B1.Da.Verify
public import LeanVM.Guest.B1.Sig.SphincsSound

/-!
# `main`, its witness decoded from the frame map, the leanXMSS reader a parameter

`decWitVX sigOf σ rd V piOf` is `SoundV`'s `decWitV` with the leanXMSS signature of raw iteration
`j` read by `sigOf` off `__loop2`'s frame at its arguments (`V "__loop2" args []`: the leanXMSS
check is inline in `__loop2` at 40f877dc). `main_sound_VX`: given the segment's statement for
`sigOf` (`Sig.verify_lean_xmss_sound_Spec sigOf`) and `verify_sub`'s (`SubSoundW`), a run of
`main`'s body gives the statement of the public input's digest, held by `decWitVX sigOf σ rd V
piOf`. `SoundV` instantiates it with the xmss family's reader and proof.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-- **`main`'s witness, decoded from the frame map `V`**, the leanXMSS reader `sigOf`. -/
noncomputable def decWitVX (sigOf : Val → LeanXmss.Signature) (σ : Val) (rd : Reader)
    (V : FrameMap) (piOf : Reader → Val → FrameMap → Proof) : NodeWitness :=
  decWit σ rd (fun args => sigOf (V "__loop2" args []))
    (fun p => Sig.sphincsSigOf (V "verify_sig_lean_sphincs" [p, σ (.n 47)] []) V)
    (fun args rets => Da.dvWit (V "da_verify" args rets) V)
    (fun args => piOf rd (V "verify_sub" args []) V)
    (fun args => aggHints rd (V "aggregate_claims" args []))

theorem find_verify_sub : coreProgram.find? "verify_sub" = some Data.core18 :=
  Program.find?_of_indexOf? (j := 18) (by decide +kernel) rfl

/-- **`verify_sub`'s statement, its proof named by `piOf`**: on a memory image of at most `2^32`
words, under a call relation that unfolds at `V` and lies below `coreProgram.Rel`, a run of its
body whose arguments hold the exponent tables returns nothing, and its proof `piOf L.read σ V` is
accepted for the public input and the seed of its arguments. -/
def SubSoundW (bytecode : List K) (piOf : Reader → Val → FrameMap → Proof) : Prop :=
  bytecode.length = 2 ^ bytecodeVars → ∀ {κ : ℕ} (L : MemoryImage κ), κ ≤ 32 →
    ∀ (C : CallRel) (V : FrameMap), UnfoldsV L.read C V → CallRel.Le C (coreProgram.Rel L.read) →
      ∀ (σ : Val) (rets : List E),
        Stmt.HoldsList C L.read σ (Fn.body Data.core18) False (fun rs ↦ rs = rets) →
        VerifySub.VerifySubPre L.read (Data.core18.params.map σ) →
          rets = [] ∧ VerifySubOut bytecode L.read (Data.core18.params.map σ) (piOf L.read σ V)

/-- **`main` is sound, its witness decoded from the frame map**, the leanXMSS reader `sigOf`,
given the segment's statement and `verify_sub`'s with its proof named. -/
theorem main_sound_VX {bytecode : List K} {piOf : Reader → Val → FrameMap → Proof}
    {sigOf : Val → LeanXmss.Signature} (hx : Sig.verify_lean_xmss_sound_Spec sigOf)
    (hv : SubSoundW bytecode piOf) :
    bytecode.length = 2 ^ bytecodeVars → ∀ (rd : Reader), MemOk rd → ∀ (C : CallRel) (V : FrameMap),
      UnfoldsV rd C V → CallRel.Le C (coreProgram.Rel rd) → ∀ (D : Digest) (σ : Val),
        LoadHolds rd 1 0 (digestHalves D).1 → LoadHolds rd 1 1 (digestHalves D).2 →
        Stmt.HoldsList C rd σ Data.core0.body False (fun rs ↦ rs = []) →
          statementDigest (decSeed σ) (decStmt σ rd) = D ∧
            NodeRelation bytecode (decSeed σ) (decStmt σ rd) (decWitVX sigOf σ rd V piOf) := by
  intro hbl rd hm C V hV hle D σ hp0 hp1 hb
  obtain ⟨κ, -, hκ, L, rfl⟩ := id hm
  refine main_sound_C hbl hm (unfolds_of_V hV) hle ⟨?_, ?_, ?_, ?_, ?_⟩ hp0 hp1 hb
  · intro args h
    obtain ⟨hp, hbx⟩ := body_ofV hV find_loop2 h
    exact loop2Out_of_body hx hp hbx
  · intro p h hbb
    obtain ⟨hp, hbs⟩ := body_ofV hV Sig.find_verify_sig_lean_sphincs h
    obtain ⟨-, ho⟩ := Sig.verify_sig_lean_sphincs_sound_holds C V L hκ hV _ _ hbs
    rw [Sig.core20_params] at hp
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
    obtain ⟨e0, e1⟩ := hp
    rw [e0, e1] at ho
    exact ho hbb
  · intro gsq rets h hsq
    obtain ⟨hp, hbd⟩ := body_ofV hV Da.find_da_verify h
    exact Da.da_verify_sound_w hV hle hm hp hbd hsq
  · intro pi0 pi1 s0 s1 gsq out h hexp
    obtain ⟨hp, hbv⟩ := body_ofV hV find_verify_sub h
    obtain ⟨-, ho⟩ := hv hbl L hκ C V hV hle _ _ hbv (by rw [hp]; exact hexp)
    rw [hp] at ho
    exact ho
  · intro ncg cpi cfresh ccarried dst h m hm1 hm16 hN
    obtain ⟨hp, hba⟩ := body_ofV hV find_aggregate_claims h
    exact (aggregate_claims_val hle hp hba m hm1 hm16 hN).2

end
end LeanVM.Guest.B1.Main
