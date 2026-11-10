/-
  LeanVM.Prover.Assemble

  The statement's honest prover is the specification at the execution's own witness: its script
  makes the moves of the specification's honest script, phase by phase, so its proof is the
  specification's, and the completeness theorems apply to it.
-/

import Statement.Prover.Prove
import LeanVM.Prover.Complete
import LeanVM.Prover.Refine
import LeanVM.Prover.Witness
import LeanVM.Prover.Bus
import LeanVM.Prover.Table
import LeanVM.Prover.Keccak
import LeanVM.Prover.Ring
import LeanVM.Prover.Whir
import LeanVM.Prover.Ntt
import LeanVM.Protocol.WithHash

/-!
# The honest prover is the specification at the execution's witness

* `corr_honestScript`: at a valid execution within the cap and a valid rate, the honest script
  (`LeanVM.Prover.honestScript`) of the execution's witness (`witness?`) makes the moves of the
  specification's honest script `honestProver prog s ρ q (leanVmPhases prog s q)` at the
  witness `skelWitness prog input t.image t.runSkels`, its sizes and its stack: the announcement,
  the stack's commitment (`stackWordFast_eq`), the bus (`corr_busFast`), the table sumcheck
  (`corr_tableFast`, which needs the bus's result true: `BusGood`), the public input, the Keccak
  phase (`corr_keccakPhase`, which needs the output lanes' point of the table's height), ring
  switching (`corr_ringFast`) and the opening (`corr_openingFast`). Each of the first four runs
  beside the verifier's phase (`Script.alongside`), whose result the specification's phase
  returns too, by its simulation (`corr_alongside`: the `Phases.Honest` facts, the bus's and the
  table's through the claim-list form, `follows_of_bind_ret`).
* `prove_eq_honestComp`: so the prover with the oracle calls is `Rom.honestComp?` of the
  specification's strategy there (`runScript_corr`, `runScript_eq_proveM`).
* `specOnValid_prove`, `childSpec_prove`: the hypotheses of `completeness_of_spec` and
  `guestChildComplete_of_spec`.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.Whir.Complete LeanVM.Guest.Child
open Air.Flat (EnsembleWitness)
open OracleComp

/-! ## Scripts: associativity, results -/

namespace Script

variable {α β γ : Type}

theorem bind_assoc' (p : Script α) (f : α → Script β) (g : β → Script γ) :
    (p.bind f).bind g = p.bind fun a ↦ (f a).bind g := by
  induction p with
  | ret a => rfl
  | send x k ih => simp only [bind, ih]
  | sample k ih => simp only [bind, ih]
  | grind k ih => simp only [bind, ih]
  | commit w k ih => simp only [bind, ih]
  | query k ih => simp only [bind, ih]

theorem AllRet.mono {P Q : α → Prop} (hPQ : ∀ a, P a → Q a) :
    ∀ H : Script α, Script.AllRet P H → Script.AllRet Q H
  | .ret a, h => hPQ a h
  | .send _ k, h => AllRet.mono hPQ k h
  | .sample k, h => fun c ↦ AllRet.mono hPQ (k c) (h c)
  | .grind k, h => AllRet.mono hPQ k h
  | .commit _ k, h => AllRet.mono hPQ k h
  | .query k, h => fun rows ↦ AllRet.mono hPQ (k rows) (h rows)

end Script

/-- A script with no opening. -/
def Script.NoQuery {α : Type} : Script α → Prop
  | .ret _ => True
  | .send _ k => Script.NoQuery k
  | .sample k => ∀ c, Script.NoQuery (k c)
  | .grind k => Script.NoQuery k
  | .commit _ k => Script.NoQuery k
  | .query _ => False

theorem Script.NoQuery.bind {α β : Type} {f : α → Script β} (hk : ∀ a, Script.NoQuery (f a)) :
    ∀ H : Script α, Script.NoQuery H → Script.NoQuery (H.bind f)
  | .ret a, _ => hk a
  | .send _ k, h => Script.NoQuery.bind hk k h
  | .sample k, h => fun c ↦ Script.NoQuery.bind hk (k c) (h c)
  | .grind k, h => Script.NoQuery.bind hk k h
  | .commit _ k, h => Script.NoQuery.bind hk k h
  | .query _, h => h.elim

theorem noQuery_sendList : ∀ xs : List E, Script.NoQuery (Script.sendList xs)
  | [] => trivial
  | _ :: xs => noQuery_sendList xs

theorem noQuery_sampleE_bind {β : Type} {f : E → Script β} (h : ∀ c, Script.NoQuery (f c)) :
    Script.NoQuery (Script.sampleE.bind f) := h

theorem noQuery_sendE_bind {β : Type} (x : E) {f : Unit → Script β}
    (h : Script.NoQuery (f ())) : Script.NoQuery ((Script.sendE x).bind f) := h

theorem noQuery_sampleN : ∀ n : ℕ, Script.NoQuery (Script.sampleN n)
  | 0 => trivial
  | n + 1 => by
    show Script.NoQuery (Script.sampleE.bind fun x ↦
      (Script.sampleN n).bind fun xs ↦ Script.ret (x :: xs))
    exact noQuery_sampleE_bind fun _ ↦ Script.NoQuery.bind (fun _ ↦ trivial) _ (noQuery_sampleN n)

theorem noQuery_hSumcheck (count : ℕ) (claimOf : List E → E) :
    ∀ (modes : List (Option E)) (pre : List E), Script.NoQuery (hSumcheck count claimOf modes pre)
  | [], _ => trivial
  | _ :: modes, pre => by
    simp only [hSumcheck]
    exact Script.NoQuery.bind (fun _ ↦ noQuery_sampleE_bind fun c ↦
      Script.NoQuery.bind (fun _ ↦ trivial) _ (noQuery_hSumcheck count claimOf modes (pre ++ [c])))
      _ (noQuery_sendList _)

theorem noQuery_hStep (L₀ L₁ L₂ : List E) (k step : ℕ) (s : GkrState) :
    Script.NoQuery (hStep L₀ L₁ L₂ k step s) := by
  unfold hStep
  refine noQuery_sampleE_bind fun c ↦ Script.NoQuery.bind (fun r ↦ ?_) _ (noQuery_hSumcheck _ _ _ _)
  refine Script.NoQuery.bind (fun _ ↦ ?_) _ (noQuery_sendList _)
  refine Script.NoQuery.bind (fun _ ↦ ?_) _ (noQuery_sendList _)
  refine Script.NoQuery.bind (fun _ ↦ ?_) _ (noQuery_sendList _)
  exact Script.NoQuery.bind (fun _ ↦ trivial) _ (noQuery_sampleN _)

theorem noQuery_hLayers (L₀ L₁ L₂ : List E) :
    ∀ (n : ℕ) (s : GkrState), Script.NoQuery (hLayers L₀ L₁ L₂ n s)
  | 0, _ => trivial
  | 1, s => by
    simp only [hLayers]
    exact Script.NoQuery.bind (fun _ ↦ noQuery_hLayers L₀ L₁ L₂ 0 _) _ (noQuery_hStep _ _ _ _ _ _)
  | n + 2, s => by
    simp only [hLayers]
    split
    · exact Script.NoQuery.bind (fun _ ↦ noQuery_hLayers L₀ L₁ L₂ (n + 1) _) _
        (noQuery_hStep _ _ _ _ _ _)
    · exact Script.NoQuery.bind (fun _ ↦ noQuery_hLayers L₀ L₁ L₂ n _) _
        (noQuery_hStep _ _ _ _ _ _)

theorem noQuery_hGkr (D : ℕ) (L₀ L₁ L₂ : List E) : Script.NoQuery (hGkr D L₀ L₁ L₂) := by
  unfold hGkr
  refine noQuery_sendE_bind L₀.prod (noQuery_sendE_bind L₂.prod ?_)
  exact Script.NoQuery.bind (fun _ ↦ trivial) _ (noQuery_hLayers _ _ _ _ _)

theorem noQuery_hBusK3 (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s))
    (alphas : List E) (beta : E) (g : E × List E × List E) :
    Script.NoQuery (hBusK3 prog s q alphas beta g) := by
  unfold hBusK3
  refine Script.NoQuery.bind (fun _ ↦ ?_) _ (noQuery_sendList _)
  exact noQuery_sendE_bind (mfVal prog s q g.2.1) (noQuery_sendE_bind (bfVal prog s q g.2.1) trivial)

attribute [local irreducible] Script.NoQuery Script.bind hBusK1 hBusK2 hBusK3 hGkr in
theorem noQuery_hBus (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s)) :
    Script.NoQuery (hBus prog s q) := by
  unfold hBus
  refine Script.NoQuery.bind (fun alphas ↦ ?_) _ (noQuery_sampleN _)
  unfold hBusK1
  refine noQuery_sampleE_bind fun beta ↦ ?_
  unfold hBusK2
  exact Script.NoQuery.bind (fun g ↦ noQuery_hBusK3 prog s q alphas beta g) _ (noQuery_hGkr _ _ _ _)

theorem noQuery_hTable (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s))
    (bus : BusResult) : Script.NoQuery (hTable prog s q bus) := by
  unfold hTable
  refine noQuery_sampleE_bind fun xi ↦ ?_
  generalize List.replicate (nRounds s) none = modes
  exact Script.NoQuery.bind (fun _ ↦ Script.NoQuery.bind (fun _ ↦ trivial) _ (noQuery_sendList _))
    _ (noQuery_hSumcheck _ _ _ _)

theorem noQuery_hPub (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s)) :
    Script.NoQuery (hPub prog s q) := by
  unfold hPub
  exact noQuery_sampleE_bind fun _ ↦ trivial

/-! ## The Keccak phase's honest script opens nothing -/

section KeccakNoQuery

open LeanVM.Protocol.KeccakGkr

theorem noQuery_hPack (F : List E → E) :
    ∀ (rs acc : List E) (scale : E), Script.NoQuery (hPack F rs acc scale)
  | [], _, _ => trivial
  | _ :: rs, acc, _ => by
    simp only [hPack]
    exact Script.NoQuery.bind (fun _ ↦ noQuery_sampleE_bind fun c ↦
      Script.NoQuery.bind (fun _ ↦ trivial) _ (noQuery_hPack F rs (acc ++ [c]) _)) _
      (noQuery_sendList _)

theorem noQuery_hLayer (T : States) (P : ℕ) (claim : KeccakClaim) :
    Script.NoQuery (hLayer T P claim) := by
  unfold hLayer
  simp only [Script.bind_eq, Script.ret_bind]
  refine Script.NoQuery.bind (fun _ ↦ noQuery_sampleE_bind fun _ ↦ ?_) _ (noQuery_sendList _)
  refine Script.NoQuery.bind (fun _ ↦ ?_) _ (noQuery_hPack _ _ _ _)
  refine Script.NoQuery.bind (fun _ ↦ ?_) _ (noQuery_hSumcheck _ _ _ _)
  exact Script.NoQuery.bind (fun _ ↦ noQuery_sampleE_bind fun _ ↦ trivial) _ (noQuery_sendList _)

theorem noQuery_keccakLayers (P : ℕ) (col : ℕ → K) :
    ∀ (ds : List ℕ) (claim : KeccakClaim), Script.NoQuery (hLayers P col ds claim)
  | [], _ => trivial
  | _ :: ds, _ => Script.NoQuery.bind (fun c ↦ noQuery_keccakLayers P col ds c) _
      (noQuery_hLayer _ _ _)

theorem noQuery_hOpen (F : List E → E) : Script.NoQuery (hOpen F) :=
  Script.NoQuery.bind (fun _ ↦ trivial) _ (noQuery_hSumcheck _ _ _ _)

theorem noQuery_hInput (P : ℕ) (col : ℕ → K) (claim : KeccakClaim) (outs : List ColumnClaim) :
    Script.NoQuery (hInput P col claim outs) := by
  unfold hInput
  simp only [Script.bind_eq, Script.ret_bind]
  refine Script.NoQuery.bind (fun _ ↦ ?_) _ (noQuery_hSumcheck _ _ _ _)
  exact Script.NoQuery.bind (fun _ ↦ Script.NoQuery.bind (fun _ ↦ trivial) _ (noQuery_sendList _))
    _ (noQuery_hOpen _)

theorem noQuery_hKeccak (P : ℕ) (col : ℕ → K) (inst output : List E) :
    Script.NoQuery (hKeccak P col inst output) := by
  unfold hKeccak
  simp only [Script.bind_eq, Script.ret_bind]
  refine Script.NoQuery.bind (fun _ ↦ ?_) _ (noQuery_sampleN _)
  refine Script.NoQuery.bind (fun _ ↦ noQuery_sendE_bind _ ?_) _ (noQuery_sampleN _)
  refine Script.NoQuery.bind (fun _ ↦ ?_) _ (noQuery_keccakLayers _ _ _ _)
  exact Script.NoQuery.bind (fun _ ↦ noQuery_sendE_bind _ (noQuery_hInput _ _ _ _)) _
    (noQuery_hOpen _)

theorem noQuery_hKeccakPhase (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s))
    (claims : List ColumnClaim) : Script.NoQuery (hKeccakPhase prog s q claims) :=
  Script.NoQuery.bind (fun _ ↦ Script.NoQuery.bind (fun _ ↦ trivial) _ (noQuery_hKeccak _ _ _ _))
    _ trivial

end KeccakNoQuery

/-! ## A phase's script beside the verifier's phase -/

/-- **A script beside the program another script follows** makes that script's moves where it
does, and ends in the program's result, related to the other's result as the simulation relates
them. -/
theorem corr_alongside {α β γ : Type} [Inhabited β] {R : Commits → α → β → Prop} :
    ∀ (S : Script γ) (H : Script α) (P : VerifierProgram β) (cs : Commits), Script.NoQuery H →
      Corr (fun _ _ ↦ True) S H → Follows R H P cs →
      Corr (fun b a ↦ ∃ cs', R cs' a b) (Script.alongside P S) H := by
  intro S
  induction S with
  | ret c =>
    intro H P cs _ hc hf
    cases H <;> cases P <;> simp only [Corr, Follows, Script.alongside] at hc hf ⊢
    exact ⟨cs, hf⟩
  | send x k ih =>
    intro H P cs hn hc hf
    cases H <;> cases P <;> simp only [Corr, Follows, Script.alongside] at hc hf ⊢
    obtain ⟨rfl, hc⟩ := hc
    exact ⟨rfl, ih _ _ _ hn hc hf⟩
  | sample k ih =>
    intro H P cs hn hc hf
    cases H <;> cases P <;> simp only [Corr, Follows, Script.alongside] at hc hf ⊢
    exact fun c ↦ ih c _ _ _ (hn c) (hc c) (hf c)
  | grind k ih =>
    intro H P cs hn hc hf
    cases H <;> cases P <;> simp only [Corr, Follows, Script.alongside] at hc hf ⊢
    exact ih _ _ _ hn hc hf
  | commit w k ih =>
    intro H P cs hn hc hf
    cases H <;> cases P <;> simp only [Corr, Follows, Script.alongside] at hc hf ⊢
    exact ⟨hc.1, ih _ _ _ hn hc.2 hf.2⟩
  | query k _ =>
    intro H P cs hn hc hf
    cases H <;> simp only [Corr] at hc
    exact hn.elim

/-- A simulation of a program whose result is then mapped is a simulation of the program, the
relation read at the mapped result. -/
theorem follows_of_bind_ret {α β γ : Type} {R : Commits → α → γ → Prop} {f : β → γ} :
    ∀ (H : Script α) (P : VerifierProgram β) (cs : Commits),
      Follows R H (P.bind fun b ↦ .ret (f b)) cs → Follows (fun cs a b ↦ R cs a (f b)) H P cs := by
  intro H
  induction H with
  | ret a => intro P cs h; cases P <;> simp only [Follows, VerifierProgram.bind] at h ⊢; exact h
  | send x k ih =>
    intro P cs h; cases P <;> simp only [Follows, VerifierProgram.bind] at h ⊢; exact ih _ _ h
  | sample k ih =>
    intro P cs h; cases P <;> simp only [Follows, VerifierProgram.bind] at h ⊢
    exact fun c ↦ ih c _ _ (h c)
  | grind k ih =>
    intro P cs h; cases P <;> simp only [Follows, VerifierProgram.bind] at h ⊢; exact ih _ _ h
  | commit W k ih =>
    intro P cs h; cases P <;> simp only [Follows, VerifierProgram.bind] at h ⊢
    exact ⟨h.1, ih _ _ h.2⟩
  | query k ih =>
    intro P cs h; cases P <;> simp only [Follows, VerifierProgram.bind] at h ⊢
    obtain ⟨rows, h1, h2⟩ := h
    exact ⟨rows, h1, ih _ _ _ h2⟩

/-- A simulation's results satisfy what every result of the program does. -/
theorem follows_and_allRet {α β : Type} {R : Commits → α → β → Prop} {Q : β → Prop} :
    ∀ (H : Script α) (P : VerifierProgram β) (cs : Commits), Follows R H P cs →
      Claims.AllRet P Q → Follows (fun cs a b ↦ R cs a b ∧ Q b) H P cs := by
  intro H
  induction H with
  | ret a =>
    intro P cs h hq; cases P <;> simp only [Follows] at h ⊢
    cases hq with | ret hb => exact ⟨h, hb⟩
  | send x k ih =>
    intro P cs h hq; cases P <;> simp only [Follows] at h ⊢
    cases hq with | read hk => exact ih _ _ h (hk x)
  | sample k ih =>
    intro P cs h hq; cases P <;> simp only [Follows] at h ⊢
    cases hq with | sample hk => exact fun c ↦ ih c _ _ (h c) (hk c)
  | grind k ih =>
    intro P cs h hq; cases P <;> simp only [Follows] at h ⊢
    cases hq with | grind hk => exact ih _ _ h hk
  | commit W k ih =>
    intro P cs h hq; cases P <;> simp only [Follows] at h ⊢
    cases hq with | commit hk => exact ⟨h.1, ih _ _ h.2 hk⟩
  | query k ih =>
    intro P cs h hq; cases P <;> simp only [Follows] at h ⊢
    obtain ⟨rows, h1, h2⟩ := h
    cases hq with | query hk => exact ⟨rows, h1, ih _ _ _ h2 (hk rows)⟩

/-- The public-input phase's executable script receives the challenge `hPub` receives. -/
theorem corr_sampleE_hPub (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s)) :
    Corr (fun _ _ ↦ True) Script.sampleE (hPub prog s q) := fun _ ↦ trivial

/-- The verifier's layout satisfies what the claim-list form of the verifier uses. -/
theorem layoutOk_verifierLayout {prog : LeanIsaProgram} {s : Sizes} (h : LayoutOk s) :
    Claims.LayoutOk (verifierLayout prog s) := by
  have e := buildLayout_eq prog s
  simp only [h, ↓reduceIte] at e
  exact Claims.buildLayout_ok e

/-! ## The honest script makes the specification's moves -/

section Honest

variable {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}

/-- The output lanes' point of an honest claim list has the `KECCAK` table's height. -/
theorem lanes_point_length {s : Sizes} {q : Column (leanIsaμ prog s)}
    {bc tc pc : List ColumnClaim} (hb : ∀ c ∈ bc, c.column < 6) (hp : ∀ c ∈ pc, c.column < 6)
    (z : Vector E (s.τ 5))
    (ht : tc.filter (fun c ↦ c.column ∈ keccakOutputColumns) = honestLanes prog s q z) :
    ((lanesOf (bc ++ tc ++ pc)).headD default).point.length = s.τ 5 := by
  rw [lanesOf_honest prog s q hb hp z ht]
  simp [honestLanes, List.finRange_succ]

/-- The tables' log-heights of the verifier's layout, the `KECCAK` table's among them. -/
theorem tableLogHeights_verifierLayout (s : Sizes) :
    (verifierLayout prog s).tableLogHeights = tableLogs s := rfl

theorem getD_tableLogs_keccak (s : Sizes) : (tableLogs s).getD opKeccak 0 = s.τ 5 := by
  simp [tableLogs, opKeccak]

attribute [local irreducible] Corr Script.bind Script.NoQuery Script.alongside hBus hTable hPub
  hKeccakPhase hRing honestOpening busFast tableFast KeccakGkr.keccakPhaseProve ringFast
  openingFast in
/-- **The honest script makes the specification's moves** at the execution's witness, its
sizes and its stack. -/
theorem corr_honestScript (hv : ValidExecution prog input t) (hcap : t.committedSize ≤ 2 ^ 32)
    {ρ : ℕ} (hρ : validRate ρ) {W : Witness} (hW : WitnessSpec prog input t W) :
    Corr (fun _ _ ↦ True) (honestScript W ρ (publicInputDigest input))
      (LeanVM.Protocol.EndToEnd.Complete.honestProver prog (traceSizes prog input t) ρ
        (stackOf prog (traceSizes prog input t) (traceWitness prog input t))
        (leanVmPhases prog (traceSizes prog input t)
          (stackOf prog (traceSizes prog input t) (traceWitness prog input t)))) := by
  obtain ⟨⟨-, hw, hs, hadm, -⟩, -⟩ := childFor_trace hv hcap hρ
  obtain ⟨-, hWL, hWcols, hWstack, hWann⟩ := hW
  unfold honestScript
  rw [hWL]
  generalize traceSizes prog input t = s at hWcols hWstack hWann hw hs hadm ⊢
  generalize traceWitness prog input t = w at hWcols hWstack hw hs ⊢
  have hq := m3Honest_stackOf hw hs
  generalize stackOf prog s w = q at hWcols hWstack hq ⊢
  have hP := leanVmPhases_honest hadm hq
  have hμ : leanIsaμ prog s ≤ 64 := by have := hadm.2.2.2; unfold maxMu at this; omega
  have hcols : ColsOk prog s q W.cols := hWcols
  have hl : Claims.LayoutOk (verifierLayout prog s) :=
    layoutOk_verifierLayout ⟨hadm.1, hadm.2.1, hadm.2.2.1⟩
  unfold LeanVM.Protocol.EndToEnd.Complete.honestProver honestRun
  simp only [Script.bind_eq, Script.bind_assoc', hWann, stackLog_verifierLayout, hWstack,
    Enc.stackWordFast_eq hμ]
  refine Corr.bind_same _ fun _ ↦ Corr.bind_same _ fun _ ↦ ?_
  -- the bus, beside `verifyBusBalance`
  refine Corr.bind (fun _ bus hb ↦ ?_) _ _ (corr_alongside _ _ _ [] (noQuery_hBus prog s q)
    (corr_busFast hcols) (follows_and_allRet _ _ _
      (follows_retOK _ _ _ (hP.bus []) (retOK_busColumns _)) (Claims.allRet_verifyBusBalance _ _)))
  obtain ⟨_, ⟨⟨-, rfl, hbg⟩, hbcol⟩, hbok⟩ := hb
  -- the table sumcheck, beside `tablePhase`
  have htab := hP.table bus hbg []
  rw [Claims.tablePhaseClaims_eq] at htab
  refine Corr.bind (fun rows cl hc ↦ ?_) _ _ (corr_alongside _ _ _ [] (noQuery_hTable prog s q bus)
    (corr_tableFast W.cols hcols _ (tableLogHeights_verifierLayout s) bus hbg)
    (follows_and_allRet _ _ _ (follows_of_bind_ret _ _ _ htab) (Claims.allRet_tablePhase hl hbok)))
  obtain ⟨_, ⟨-, rfl, htrue, tc, htc, z, hz⟩, hrows⟩ := hc
  obtain rfl := List.append_cancel_left htc
  -- the public input, beside `publicInputPhase`
  refine Corr.bind (fun _ pub hp ↦ ?_) _ _ (corr_alongside _ _ _ [] (noQuery_hPub prog s q)
    (corr_sampleE_hPub prog s q) (follows_and_allRet _ _ _ (follows_retOK _ _ _
      (follows_publicInputPhase hq.1 []) (retOK_publicColumns _ _))
      (Claims.allRet_publicInputPhase _ _)))
  obtain ⟨_, ⟨⟨-, rfl, hpub⟩, hpcol⟩, hpmem⟩ := hp
  -- the Keccak phase, beside `keccakPhase`
  have hlanes : lanesOf (bus.claims ++ tableColumnClaims rows ++ pub) =
      Claims.laneClaims (rows.getD opKeccak ([], [])) := Claims.lanes_eq hbok.2 hpmem hrows
  have hlen : (rows.getD opKeccak ([], [])).1.length = s.τ 5 := by
    have h := lanes_point_length hbcol hpcol z hz
    rw [hlanes] at h
    exact h
  have hk := hP.keccak _ (trueClaims_append htrue hpub) z
    (lanesOf_honest prog s q hbcol hpcol z hz) []
  rw [Claims.keccakPhaseClaims_eq hbok.2 hpmem hrows] at hk
  rw [tableLogHeights_verifierLayout, getD_tableLogs_keccak]
  refine Corr.bind (fun kr kr' hk' ↦ ?_) _ _ (corr_alongside _ _ _ []
    (noQuery_hKeccakPhase prog s q _)
    (KeccakGkr.corr_keccakPhase prog s q W.cols hcols _ rows hlanes hlen)
    (follows_of_bind_ret _ _ _ hk))
  obtain ⟨_, -, rfl, -⟩ := hk'
  -- ring switching, then the opening
  refine Corr.bind (fun r rs hr ↦ ?_) _ _ (corr_ringFast kr.2.1 kr.2.2)
  obtain ⟨rfl, -, -⟩ := hr
  have hcl : ∀ L : List ColumnClaim, (RingOut.claim r (verifierLayout prog s) ::
      L.map (ClaimDesc.column (verifierLayout prog s))).map ClaimDesc.denote =
      openingClaims prog s (r.target, fun rPrime ↦ ringWeight r.point rPrime
        (ringCoefficients r.challenges)) L := by
    intro L
    simp only [openingClaims, RingOut.claim, ClaimDesc.denote, List.map_cons, List.map_map,
      Function.comp_def]
    rfl
  rw [← hcl, ← Script.bind_ret (openingFast _ _ _ _)]
  exact Corr.bind (fun _ _ _ ↦ by unfold Corr; trivial) _ _ (corr_openingFast hμ ρ q _)

end Honest

/-! ## The prover is the specification at the execution's witness -/

section Prove

variable {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}

/-- **The prover with the oracle calls is the specification** at the execution's witness: on a
valid execution within the cap at a valid rate, `proveWithHash callKeccak256 callKeccakF1600` is
`Rom.honestComp?` of the specification's honest strategy at `skelWitness`, its sizes and its
stack. -/
theorem prove_eq_honestComp (hv : ValidExecution prog input t) (hcap : t.committedSize ≤ 2 ^ 32)
    {ρ : ℕ} (hρ : 1 ≤ ρ ∧ ρ ≤ 4) (fuel : ℕ) :
    proveWithHash callKeccak256 callKeccakF1600 prog input t ρ fuel =
      Rom.honestComp? (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
        (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
        (leanVmProver prog (traceSizes prog input t) ρ
          (stackOf prog (traceSizes prog input t) (traceWitness prog input t))) fuel := by
  obtain ⟨W, hW, hspec⟩ := witness?_spec hv hcap
  simp only [proveWithHash, hW, hρ, and_self, ↓reduceIte, Rom.honestComp?,
    seedRun_leanVmSeed]
  refine congrArg (fun k : KeccakState → OracleComp KeccakCalls (Option Proof) ↦
    seedWithHash callKeccak256 callKeccakF1600 (bytecodeWords prog) (publicInputDigest input) >>= k)
    (funext fun seed ↦ ?_)
  rw [runScript_corr callKeccak256 callKeccakF1600 fuel _ (corr_honestScript hv hcap hρ hspec) seed,
    runScript_eq_proveM]
  rfl

/-- The statement's honest prover is `prove` with the oracle calls. -/
abbrev oracleProver : HonestProverWithHash := LeanVM.proverWithHash

/-- **The hypothesis of the completeness theorems**: on valid executions within the cap at a
valid rate, the prover is the specification at a child's witness. -/
theorem specOnValid_prove : SpecOnValid oracleProver ChildFor :=
  fun _ _ _ _ fuel hv hcap hρ ↦ ⟨_, _, childFor_trace hv hcap hρ, prove_eq_honestComp hv hcap hρ fuel⟩

/-- The same, at an honest witness. -/
theorem specOnValid_prove_honest : SpecOnValid oracleProver HonestFor :=
  fun prog input t ρ fuel hv hcap hρ ↦
    let ⟨w, s, h, e⟩ := specOnValid_prove prog input t ρ fuel hv hcap hρ
    ⟨w, s, h.1, e⟩

/-- **Everywhere, the prover is the specification at a child's witness or makes no proof.** -/
theorem childSpec_prove (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ
    fuel : ℕ) :
    ChildSpec oracleProver prog input t ρ fuel := by
  by_cases h : ValidExecution prog input t ∧ t.committedSize ≤ 2 ^ 32 ∧ 1 ≤ ρ ∧ ρ ≤ 4
  · exact .inr (specOnValid_prove prog input t ρ fuel h.1 h.2.1 h.2.2)
  · left
    show proveWithHash callKeccak256 callKeccakF1600 prog input t ρ fuel = pure none
    unfold proveWithHash
    cases hW : witness? prog input t with
    | none => rfl
    | some W =>
      have hs := (isSome_witness?_iff prog input t).mp (by rw [hW]; rfl)
      have hρ : ¬ (1 ≤ ρ ∧ ρ ≤ 4) := fun hρ ↦ h ⟨hs.1, hs.2, hρ⟩
      simp only [hρ, ↓reduceIte]

end Prove

/-! ## Completeness of the named prover -/


end LeanVM.Prover
