/-
  LeanVM.Guest.B1.VerifySub.Accept

  The deferring verifier accepts a proof whose phases run as `verify_sub`'s callees establish.
-/

module

public import LeanVM.Guest.B1.VerifySub.Split
public import LeanVM.Guest.B1.Whir.Run
public import LeanVM.Protocol.WithHash
public import LeanVM.Protocol.WithHashBridge

/-!
# Acceptance from the phases' runs

`deferred_accepts`: from the seed's sponge, if the announced sizes, the commitment, the
out-of-domain sample, the bus's challenges, `gkrPhase`, `tablesSeg`, `keccakPhaseClaims`, the ring
switch and the stacked opening run one after the other on the stream words
`xs₀, [x₀, x₁], xs_O, xs_B, xs_G, xs_T, xs_K, xs_R, xs_W` and the openings `os`, the stack's root
committed being `digestFromHalves (x₀, x₁)`, then `verifyDeferred` accepts the proof of those words
and openings.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Whir

@[expose] public section

theorem require_true {c : Prop} [Decidable c] (h : c) : VerifierProgram.require c =
    VerifierProgram.ret () := by
  simp [VerifierProgram.require, h]

/-- **The deferring verifier accepts**, given its phases' runs. -/
theorem deferred_accepts {bytecode : List K} {seed pi : Digest} {c : BytecodeClaim} {s0 : Fs}
    (hs0 : s0.Carries ⟨keccakF1600 (seedInput seed pi), [], none⟩)
    {L : Layout} {lir : ℕ} {xs0 : List E} {s1 : Fs}
    (h1 : RunsTo (readAnnouncedSizes bytecode) s0 xs0 (L, lir) s1)
    {level : Whir.Level} {rest : List Whir.Level}
    (hcfg : Whir.ladder L.stackLog lir = some (level :: rest)) (x0 x1 : E)
    {xsO : List E} {ood : StackClaim} {s2 : Fs}
    (h2 : RunsTo (readOod L.stackLog) ((s1.absorb x0 dsObserve).absorb x1 dsObserve) xsO ood s2)
    (hd : busDepth L < 64)
    {xsB : List E} {wb : List E × E} {s3 : Fs}
    (h3 : RunsTo (busChallenges (busDepth L)) s2 xsB wb s3)
    {xsG : List E} {r : E × List E × List E} {s4 : Fs}
    (h4 : RunsTo (Tables.gkrPhase (busDepth L)) s3 xsG r s4)
    {xsT : List E} {bc : BusResult × List ColumnClaim} {s5 : Fs}
    (h5 : RunsTo (Tables.tablesSeg (claimedBytecodeValue c) L pi wb.1 wb.2 r.2.1 r.2.2) s4 xsT bc s5)
    {xsK : List E} {kc : List ColumnClaim × List E × List E} {s6 : Fs}
    (h6 : RunsTo (keccakPhaseClaims L bc.2) s5 xsK kc s6)
    {xsR : List E} {rs : E × (List E → E)} {s7 : Fs}
    (h7 : RunsTo (ringSwitch kc.2.1 kc.2.2) s6 xsR rs s7)
    {xsW : List E} {os : List (List Opening)} {s8 : Fs} {roots' : List (Digest × ℕ × ℕ)}
    (h8 : RunsWith (verifyStackedOpening L.stackLog lir (stackClaims L kc.1 rs.1 rs.2 ood)) s7 xsW os
      [(digestFromHalves (x0, x1), stackShape L.stackLog lir)] () s8 roots') :
    verifyDeferred bytecode seed pi c
      ⟨xs0 ++ [x0, x1] ++ xsO ++ xsB ++ xsG ++ xsT ++ xsK ++ xsR ++ xsW, os⟩ = true := by
  have hrun0 : RunsWith (deferredFlat c bytecode pi) s0
      (xs0 ++ ([x0, x1] ++ (xsO ++ ([] ++ (xsB ++ (xsG ++ (xsT ++ (xsK ++ (xsR ++
        (xsW ++ []))))))))))
      ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ (os ++ []))))))))))
      [] true s8 roots' := by
    have hc : RunsWith (commitStack L.stackLog lir) s1 [x0, x1] [] []
        () ((s1.absorb x0 dsObserve).absorb x1 dsObserve)
        [(digestFromHalves (x0, x1), stackShape L.stackLog lir)] := by
      rw [commitStack_eq hcfg]
      exact runsWith_commitP s1 x0 x1 _ _ []
    refine RunsWith.bind' (RunsTo.withRoots h1 []) ?_
    refine RunsWith.bind' hc ?_
    refine RunsWith.bind' (RunsTo.withRoots h2 _) ?_
    refine RunsWith.bind' (a := ()) (s1 := s2) (xs := []) (os1 := [])
      (r1 := [(digestFromHalves (x0, x1), stackShape L.stackLog lir)]) ?_ ?_
    · rw [require_true hd]
      exact RunsTo.withRoots (runsTo_ret () s2) _
    refine RunsWith.bind' (RunsTo.withRoots h3 _) ?_
    refine RunsWith.bind' (RunsTo.withRoots h4 _) ?_
    refine RunsWith.bind' (RunsTo.withRoots h5 _) ?_
    refine RunsWith.bind' (RunsTo.withRoots h6 _) ?_
    refine RunsWith.bind' (RunsTo.withRoots h7 _) ?_
    refine RunsWith.bind' h8 ?_
    exact runsWith_ret true s8 roots'
  have hrun : RunsWith (deferredFlat c bytecode pi) s0
      (xs0 ++ [x0, x1] ++ xsO ++ xsB ++ xsG ++ xsT ++ xsK ++ xsR ++ xsW) os [] true s8 roots' :=
    RunsWith.of_eq hrun0 rfl (by simp) (by simp) rfl rfl rfl rfl
  obtain ⟨sp, -, hsp⟩ := hrun ⟨keccakF1600 (seedInput seed pi), [], none⟩ hs0 [] []
  simp only [List.append_nil] at hsp
  rw [← deferred_eq] at hsp
  rw [verifyDeferred_eq_withHash]
  simp only [verifyDeferredWithHash, Compile.runProofWithHash]
  simp only [runId] at hsp
  exact congrArg (fun o : Option (Bool × VerifierProgramState) ↦ match o with
    | some (true, s) => (s.stream.isEmpty && s.openings.isEmpty : Bool)
    | _ => false) hsp

end
end LeanVM.Guest.B1.VerifySub
