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

`deferred_accepts`: from the seed's sponge, if the announced sizes, the commitment, the bus's
challenges, `gkrPhase`, `tablesSeg`, the output lanes' check, `keccakSeg`, the ring map's other
challenges, the batching challenge, `whirOpen` and its terminal check run one after the other on
the stream words `xs₀, [x₀, x₁], xs_G, xs_T, xs_K, xs_W` and the openings `os`, then
`verifyDeferred` accepts the proof `⟨xs₀ ++ [x₀, x₁] ++ xs_G ++ xs_T ++ xs_K ++ xs_W, os⟩`.
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
    (hs0 : s0.Carries ⟨keccakF1600 (seedInput seed pi), []⟩)
    {L : Layout} {lir : ℕ} {xs0 : List E} {s1 : Fs}
    (h1 : RunsTo (readAnnouncedSizes bytecode) s0 xs0 (L, lir) s1)
    {level : Whir.Level} {rest : List Whir.Level}
    (hcfg : Whir.ladder L.stackLog lir = some (level :: rest))
    {x0 x1 : E} {root : Digest} (hroot : digestFromHalves (x0, x1) = some root)
    {alphas : List E} {s3 : Fs}
    (h3 : ((s1.absorb x0 dsObserve).absorb x1 dsObserve).squeezeN busBits = (alphas, s3))
    {beta : E} {s4 : Fs} (h4 : s3.squeeze = (beta, s4))
    {xsG : List E} {r : E × List E × List E} {s5 : Fs}
    (h5 : RunsTo (Tables.gkrPhase (busLayout [0, L.logMemory, L.logBytecode] L.push).depth) s4 xsG
      r s5)
    {xsT : List E} {bc : BusResult × List ColumnClaim} {s6 : Fs}
    (h6 : RunsTo (Tables.tablesSeg (claimedBytecodeValue c) L pi alphas beta r.2.1 r.2.2) s5
        xsT bc s6)
    (h7 : (lanesOf bc.2).map (·.column) = keccakOutputColumns ∧
      ∀ c ∈ lanesOf bc.2, c.point = ((lanesOf bc.2).headD default).point)
    {xsK : List E} {km : (List ColumnClaim × List E × List E) × E} {s7 : Fs}
    (h8 : RunsTo (keccakSeg (L.tableLogHeights.getD opKeccak 0) ((lanesOf bc.2).headD default).point
      ((lanesOf bc.2).map (·.value))) s6 xsK km s7)
    {chs : List E} {s8 : Fs} (h9 : s7.squeezeN 5 = (chs, s8))
    {lam : E} {s9 : Fs} (h10 : s8.squeeze = (lam, s9))
    {xsW : List E} {os : List (List Opening)} {w : B1.Whir.WhirEnd} {s10 : Fs}
    {roots' : List (Digest × ℕ × ℕ)}
    (h11 : RunsWith (B1.Whir.whirOpen L.stackLog lir
      (dot (powers lam (stackClaims L bc.2 km.1.1 km.1.2.1 km.1.2.2 (km.2 :: chs)).length)
        ((stackClaims L bc.2 km.1.1 km.1.2.1 km.1.2.2 (km.2 :: chs)).map (·.2))))
      s9 xsW os [(root, B1.Whir.stackShape L.stackLog lir)] w s10 roots')
    (h12 : w.Accepts fun point ↦
      dot (powers lam (stackClaims L bc.2 km.1.1 km.1.2.1 km.1.2.2 (km.2 :: chs)).length)
        ((stackClaims L bc.2 km.1.1 km.1.2.1 km.1.2.2 (km.2 :: chs)).map fun c ↦ c.1 point)) :
    verifyDeferred bytecode seed pi c ⟨xs0 ++ [x0, x1] ++ xsG ++ xsT ++ xsK ++ xsW, os⟩ = true := by
  have hrun0 : RunsWith (deferredFlat c bytecode pi) s0
      (xs0 ++ ([x0, x1] ++ ([] ++ ([] ++ (xsG ++ (xsT ++ ([] ++ (xsK ++ ([] ++ ([] ++ (xsW ++ ([] ++ ([])))))))))))))
      ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ (os ++ ([] ++ ([]))))))))))))) [] true s10 roots' := by
      have hc : RunsWith (commitStack L.stackLog lir) s1 [x0, x1] [] []
          () ((s1.absorb x0 dsObserve).absorb x1 dsObserve) [(root, stackShape L.stackLog lir)] := by
        rw [commitStack_eq hcfg]
        exact runsWith_commitP s1 x0 x1 hroot _ _ []
      refine RunsWith.bind' (RunsTo.withRoots h1 []) ?_
      refine RunsWith.bind' hc ?_
      have e3 := runsTo_sampleN busBits ((s1.absorb x0 dsObserve).absorb x1 dsObserve)
      rw [h3] at e3
      refine RunsWith.bind' (RunsTo.withRoots e3 _) ?_
      have e4 := runsTo_sampleE s3
      rw [h4] at e4
      refine RunsWith.bind' (RunsTo.withRoots e4 _) ?_
      refine RunsWith.bind' (RunsTo.withRoots h5 _) ?_
      refine RunsWith.bind' (RunsTo.withRoots h6 _) ?_
      refine RunsWith.bind' (a := ()) (s1 := s6) (xs := []) (os1 := [])
        (r1 := [(root, stackShape L.stackLog lir)]) ?_ ?_
      · rw [require_true h7]
        exact RunsTo.withRoots (runsTo_ret () s6) _
      refine RunsWith.bind' (RunsTo.withRoots h8 _) ?_
      have e9 := runsTo_sampleN 5 s7
      rw [h9] at e9
      refine RunsWith.bind' (RunsTo.withRoots e9 _) ?_
      have e10 := runsTo_sampleE s8
      rw [h10] at e10
      refine RunsWith.bind' (RunsTo.withRoots e10 _) ?_
      refine RunsWith.bind' h11 ?_
      refine RunsWith.bind' (a := ()) (s1 := s10) (xs := []) (os1 := []) (r1 := roots') ?_ ?_
      · rw [require_true h12]
        exact runsWith_ret () s10 roots'
      exact runsWith_ret true s10 roots'
  have hrun : RunsWith (deferredFlat c bytecode pi) s0
      (xs0 ++ [x0, x1] ++ xsG ++ xsT ++ xsK ++ xsW) os [] true s10 roots' :=
    RunsWith.of_eq hrun0 rfl (by simp) (by simp) rfl rfl rfl rfl
  obtain ⟨sp, -, hsp⟩ := hrun ⟨keccakF1600 (seedInput seed pi), []⟩ hs0 [] []
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
