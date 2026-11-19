module

public import NativeVm.Code.Data
public import NativeVm.Code.Rel
public import NativeVm.Wire.Mem
public import NativeVm.Transcript.Seed

/-!
# What each part of the verifier's code promises

`body` (`NativeVm.Code.Main`) runs the decoder, the seed, the seven phases of
`Model.verifyExecution` and the end check, each a `Stmt` of its own; this module states what each
must do, as a proposition about its code (`Phase1Ok phase1`, ..., `DecodeOk Wire.decode`), and
`body_spec` assumes them; the end check's (`FinishOk`) is proved from the transcript's.

A phase's contract (`Runs`) relates its code to its model step from a state that holds the model's
(`CodeRel`): it ends normally where the step returns, in a state holding the step's next state and
its result in the step's regions (`NativeVm.Code.Data`), or fails exactly where the step rejects.
Either way it keeps `rdi` and every word outside the transcript's (`Transcript.Foot`) and its
regions (`Kept`): the inputs, the save area, the decoded proof and the earlier phases' results
survive it (`Inputs.kept`, `Kept.same`). The phases are the statement's, in order:

| phase | model step | reads | writes |
|---|---|---|---|
| 1 | `readAnnouncedSizes bytecode` | | `LayoutAt` |
| 2 | `phase2M layout rate` (`commitStack`, `readOod`) | layout | `EqClaimAt` |
| 3 | `verifyBusBalance layout` | layout | `BusAt`, `ClaimsAt` (the bus's claims) |
| 4 | `tablePhase layout bus` | layout, bus | `EvalsAt`, `ClaimsAt` (appended) |
| 5 | `publicInputPhase layout publicInput` | layout | `ClaimsAt` (appended) |
| 6 | `keccakPhase layout evaluations` | layout, evaluations | `KeccakOutAt`, `ClaimsAt` (appended) |
| 7 | `phase7M layout rate ood claims point slices` (`ringSwitch`, `verifyStackedOpening`) | all | phase 7's regions |

The column claims grow in place, phase by phase, within `claimCap`: each phase's contract bounds
what it appends.
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Model LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile
open NativeVm.Transcript (wd Fits Disj Env Foot SeedPre ctxEnd scratchW ctxBytecode
  ctxBytecodeLen ctxPublic wd_inj wd_ne_of_disj wd_toNat)

/-! ## The inputs -/

/-- The verifier's inputs besides the proof: the bytecode's words and their address, the public
input. -/
structure Input where
  bcA : UInt64
  bytecode : Array UInt64
  pub : Vector UInt64 4

/-- **The inputs and the working area**: the context's words `2 .. 7` point to the bytecode and
hold the public input; the working area holds `workWords n` words, every area inside the address
space and apart from the others. -/
structure Inputs (env : Env) (inp : Input) (mem : UInt64 → Option UInt64) : Prop where
  bcPtr : mem (wd env.ctx ctxBytecode) = some inp.bcA
  bcLen : NatAt mem (wd env.ctx ctxBytecodeLen) inp.bytecode.size
  bcWords : WordArr mem inp.bcA inp.bytecode
  pubWords : ∀ i (h : i < 4), mem (wd env.ctx (ctxPublic + i)) = some inp.pub[i]
  fitCtx : Fits env.ctx ctxEnd
  fitBc : Fits inp.bcA inp.bytecode.size
  fitWork : Fits env.work (workWords inp.bytecode.size)
  disjCtx : Disj env.ctx ctxEnd env.work (workWords inp.bytecode.size)
  disjDec : Disj env.dec (decodedWords env.L) env.work (workWords inp.bytecode.size)
  disjBcCtx : Disj inp.bcA inp.bytecode.size env.ctx ctxEnd
  disjBcWork : Disj inp.bcA inp.bytecode.size env.work (workWords inp.bytecode.size)
  workSome : ∀ k < workWords inp.bytecode.size, (mem (wd env.work k)).isSome

/-! ## What a run keeps -/

/-- **What a part of the code keeps**: `rdi` at the context, and every word outside the
transcript's (`Transcript.Foot`) and the regions `rs` of the working area. -/
def Kept (env : Env) (rs : List Region) (s s' : QState) : Prop :=
  s'.reg .rdi = env.ctx ∧
    ∀ a, ¬ Foot env a → (∀ r ∈ rs, ¬ r.In env.work a) → s'.mem a = s.mem a

theorem Kept.trans {env : Env} {rs : List Region} {s₁ s₂ s₃ : QState} (h₁ : Kept env rs s₁ s₂)
    (h₂ : Kept env rs s₂ s₃) : Kept env rs s₁ s₃ :=
  ⟨h₂.1, fun a hf hr ↦ (h₂.2 a hf hr).trans (h₁.2 a hf hr)⟩

theorem Kept.mono {env : Env} {rs rs' : List Region} {s s' : QState} (h : Kept env rs s s')
    (hrs : ∀ r ∈ rs, r ∈ rs') : Kept env rs' s s' :=
  ⟨h.1, fun a hf hr ↦ h.2 a hf fun r hm ↦ hr r (hrs r hm)⟩

theorem workWords_lt {env : Env} {inp : Input} {mem : UInt64 → Option UInt64}
    (h : Inputs env inp mem) : workWords inp.bytecode.size ≤ 2 ^ 61 := by
  have := h.fitWork
  unfold Fits at this
  omega

theorem transcriptWords_le (n : Nat) : Transcript.workWords ≤ workWords n := by
  have := dataEnd_le n
  rw [dataEnd_val] at this
  rw [Transcript.workWords_val]
  omega

theorem stop_le_of_mem {r : Region} (hr : r ∈ regions) (n : Nat) : r.stop ≤ workWords n :=
  le_trans (regions_bounds r hr).2 (dataEnd_le n)

/-- A context word is no word of the working area. -/
theorem Inputs.ctx_ne_work {env : Env} {inp : Input} {mem : UInt64 → Option UInt64}
    (h : Inputs env inp mem) {j k : Nat} (hj : j < ctxEnd) (hk : k < workWords inp.bytecode.size) :
    wd env.ctx j ≠ wd env.work k :=
  wd_ne_of_disj h.fitCtx h.fitWork h.disjCtx hj hk

/-- A word of the working area at or after the transcript's is not the transcript's. -/
theorem Inputs.not_foot_work {env : Env} {inp : Input} {mem : UInt64 → Option UInt64}
    (h : Inputs env inp mem) {k : Nat} (hk1 : Transcript.workWords ≤ k)
    (hk2 : k < workWords inp.bytecode.size) : ¬ Foot env (wd env.work k) := by
  have hl := workWords_lt h
  rintro (⟨j, -, hj, e⟩ | ⟨j, hj, e⟩)
  · exact h.ctx_ne_work hj hk2 e.symm
  · rw [Transcript.workWords_val] at hj hk1
    have := (wd_inj (by omega) (by omega)).mp e
    omega

/-- A context word below the transcript's scratch is not the transcript's. -/
theorem Inputs.not_foot_ctx {env : Env} {inp : Input} {mem : UInt64 → Option UInt64}
    (h : Inputs env inp mem) {j : Nat} (hj : j < scratchW) : ¬ Foot env (wd env.ctx j) := by
  rw [Transcript.scratchW_val] at hj
  have hj' : j < ctxEnd := by rw [Transcript.ctxEnd_val]; omega
  rintro (⟨k, hk, hk', e⟩ | ⟨k, hk, e⟩)
  · rw [Transcript.scratchW_val] at hk
    rw [Transcript.ctxEnd_val] at hk'
    have := (wd_inj (by omega) (by omega)).mp e
    omega
  · exact h.ctx_ne_work hj' (by have := transcriptWords_le inp.bytecode.size; omega) e

/-- A context word below the transcript's scratch survives a run that keeps the regions `rs`. -/
theorem Kept.ctx {env : Env} {inp : Input} {rs : List Region} {s s' : QState}
    (hk : Kept env rs s s') (h : Inputs env inp s.mem)
    (hrs : ∀ r ∈ rs, r.stop ≤ workWords inp.bytecode.size) {j : Nat} (hj : j < scratchW) :
    s'.mem (wd env.ctx j) = s.mem (wd env.ctx j) := by
  refine hk.2 _ (h.not_foot_ctx hj) fun r hr ⟨k, hk', e⟩ ↦ ?_
  have := hrs r hr
  rw [Transcript.scratchW_val] at hj
  exact h.ctx_ne_work (by rw [Transcript.ctxEnd_val]; omega) (by unfold Region.stop at this; omega) e

/-- **The inputs survive** a run that keeps the regions `rs` and which words exist. -/
theorem Inputs.kept {env : Env} {inp : Input} {rs : List Region} {s s' : QState}
    (h : Inputs env inp s.mem) (hk : Kept env rs s s')
    (hrs : ∀ r ∈ rs, r.stop ≤ workWords inp.bytecode.size)
    (hdom : ∀ a, (s'.mem a).isSome = (s.mem a).isSome) : Inputs env inp s'.mem := by
  have hlt := workWords_lt h
  have hbc : ∀ i < inp.bytecode.size, s'.mem (wd inp.bcA i) = s.mem (wd inp.bcA i) := by
    intro i hi
    refine hk.2 _ ?_ fun r hr ⟨k, hk', e⟩ ↦ ?_
    · rintro (⟨j, -, hj, e⟩ | ⟨j, hj, e⟩)
      · exact wd_ne_of_disj h.fitBc h.fitCtx h.disjBcCtx hi hj e
      · exact wd_ne_of_disj h.fitBc h.fitWork h.disjBcWork hi
          (by have := transcriptWords_le inp.bytecode.size; omega) e
    · have := hrs r hr
      exact wd_ne_of_disj h.fitBc h.fitWork h.disjBcWork hi (by unfold Region.stop at this; omega) e
  exact { h with
    bcPtr := by rw [hk.ctx h hrs (by rw [Transcript.scratchW_val]; unfold ctxBytecode; omega)]
                exact h.bcPtr
    bcLen := h.bcLen.congr
      (hk.ctx h hrs (by rw [Transcript.scratchW_val]; unfold ctxBytecodeLen; omega))
    bcWords := fun i hi ↦ by rw [hbc i hi]; exact h.bcWords i hi
    pubWords := fun i hi ↦ by
      rw [hk.ctx h hrs (by rw [Transcript.scratchW_val]; unfold ctxPublic; omega)]
      exact h.pubWords i hi
    workSome := fun k hk' ↦ by rw [hdom]; exact h.workSome k hk' }

/-- **A region apart from the regions `rs` survives** a run that keeps them. -/
theorem Kept.same {env : Env} {inp : Input} {rs : List Region} {s s' : QState}
    (hk : Kept env rs s s') (h : Inputs env inp s.mem)
    (hrs : ∀ r ∈ rs, r.stop ≤ workWords inp.bytecode.size) {q : Region} (hq : q ∈ regions)
    (hap : ∀ r ∈ rs, q.Apart r) : Same s.mem s'.mem (q.at env.work) q.size := by
  intro k hk'
  have hlt := workWords_lt h
  have hb := regions_bounds q hq
  have hq' := stop_le_of_mem hq inp.bytecode.size
  unfold Region.stop at hb hq'
  rw [Region.at, wd_wd]
  refine hk.2 _ (h.not_foot_work (by omega) (by omega)) fun r hr ⟨j, hj, e⟩ ↦ ?_
  have := hrs r hr
  have hap' := hap r hr
  unfold Region.stop at this
  have := (wd_inj (by omega) (by omega)).mp e
  unfold Region.Apart Region.stop at hap'
  omega

/-! ## The phases' model steps -/

/-- Phase 2's step: the stack's commitment, then its out-of-domain claim. -/
def phase2M (layout : LayoutW) (rate : Nat) : VM StackClaimW := do
  commitStack layout.stackLog rate
  readOod layout.stackLog

/-- Phase 7's step: ring switching, then the stacked opening of every stack claim. -/
def phase7M (layout : LayoutW) (rate : Nat) (ood : StackClaimW) (claims : Array ColumnClaimW)
    (point slices : Array EW) : VM Unit := do
  let (target, ringPoint, coefficients) ← ringSwitch point slices
  verifyStackedOpening layout.stackLog rate
    (#[ringSwitchClaim layout target ringPoint coefficients] ++
      claims.filterMap (·.onStack layout) ++ #[ood])

/-! ## The contracts -/

/-- **`c` runs the model step `m`** from `s`, which holds `t`: it ends normally when `m` returns,
holding its next state, with `Out` of its result, or fails when `m` rejects; either way keeping
`rs`'s complement (`Kept`). -/
def Runs {α : Type} (env : Env) (c : Stmt) (m : VM α) (t : TState) (s : QState) (rs : List Region)
    (Out : α → QState → Prop) : Prop :=
  WP c s (fun s' ↦ ∃ a t', m.run t = some (a, t') ∧ CodeRel env t' s' ∧ Out a s' ∧ Kept env rs s s')
    (fun s' ↦ m.run t = none ∧ Kept env rs s s')

/-- **Phase 1**: the sizes read, the layout and the rate exponent at `layoutR`. -/
def Phase1Ok (c : Stmt) : Prop :=
  ∀ env inp t s, CodeRel env t s → Inputs env inp s.mem →
    Runs env c (readAnnouncedSizes inp.bytecode) t s [layoutR, scratchR] fun r s' ↦
      LayoutAt s'.mem (layoutR.at env.work) inp.bytecode r.1 r.2

/-- **Phase 2**: the stack's root read, its out-of-domain claim at `oodR`. -/
def Phase2Ok (c : Stmt) : Prop :=
  ∀ env inp t s layout rate, CodeRel env t s → t.roots.size < Transcript.maxRoots →
    Inputs env inp s.mem →
    LayoutAt s.mem (layoutR.at env.work) inp.bytecode layout rate →
    Runs env c (phase2M layout rate) t s [oodR, scratchR] fun ood s' ↦
      EqClaimAt s'.mem (oodR.at env.work) ood

/-- **Phase 3**: the bus; its forms, point and totals at `busR`, its column claims the first at
`claimsR`. -/
def Phase3Ok (c : Stmt) : Prop :=
  ∀ env inp t s layout rate, CodeRel env t s → Inputs env inp s.mem →
    LayoutAt s.mem (layoutR.at env.work) inp.bytecode layout rate →
    Runs env c (verifyBusBalance layout) t s [busR, claimsR, scratchR] fun bus s' ↦
      BusAt s'.mem (busR.at env.work) bus ∧ ClaimsAt s'.mem (claimsR.at env.work) bus.claims ∧
        bus.claims.size ≤ busClaimCount

/-- **Phase 4**: the table sumcheck; the tables' points and evaluations at `evalsR`, their column
claims appended at `claimsR`. -/
def Phase4Ok (c : Stmt) : Prop :=
  ∀ env inp t s layout rate bus acc, CodeRel env t s → Inputs env inp s.mem →
    LayoutAt s.mem (layoutR.at env.work) inp.bytecode layout rate →
    BusAt s.mem (busR.at env.work) bus → ClaimsAt s.mem (claimsR.at env.work) acc →
    acc.size ≤ busClaimCount →
    Runs env c (tablePhase layout bus) t s [evalsR, claimsR, scratchR] fun ev s' ↦
      EvalsAt s'.mem (evalsR.at env.work) ev ∧
        ClaimsAt s'.mem (claimsR.at env.work) (acc ++ tableColumnClaims ev) ∧
        (tableColumnClaims ev).size ≤ tableClaimCount

/-- **Phase 5**: the public input's column claims appended at `claimsR`. -/
def Phase5Ok (c : Stmt) : Prop :=
  ∀ env inp t s layout rate acc, CodeRel env t s → Inputs env inp s.mem →
    LayoutAt s.mem (layoutR.at env.work) inp.bytecode layout rate →
    ClaimsAt s.mem (claimsR.at env.work) acc → acc.size ≤ busClaimCount + tableClaimCount →
    Runs env c (publicInputPhase layout inp.pub) t s [claimsR, scratchR] fun pc s' ↦
      ClaimsAt s'.mem (claimsR.at env.work) (acc ++ pc) ∧ pc.size ≤ publicClaimCount

/-- **Phase 6**: `KECCAK` by GKR; `q_keccak`'s point and slices at `keccakR`, the committed
outputs' claim appended at `claimsR`. -/
def Phase6Ok (c : Stmt) : Prop :=
  ∀ env inp t s layout rate ev acc, CodeRel env t s → Inputs env inp s.mem →
    LayoutAt s.mem (layoutR.at env.work) inp.bytecode layout rate →
    EvalsAt s.mem (evalsR.at env.work) ev → ClaimsAt s.mem (claimsR.at env.work) acc →
    acc.size ≤ busClaimCount + tableClaimCount + publicClaimCount →
    Runs env c (keccakPhase layout ev) t s [keccakR, claimsR, scratchR] fun r s' ↦
      KeccakOutAt s'.mem (keccakR.at env.work) r.2.1 r.2.2 ∧
        ClaimsAt s'.mem (claimsR.at env.work) (acc ++ r.1) ∧ r.1.size ≤ keccakClaimCount

/-- Phase 7's regions: every region from `ringR` on. -/
def phase7Regions : List Region := [ringR, basisR, whirR, roundsR, queriesR, rowsR, scratchR]

/-- **Phase 7**: ring switching and the stacked opening. -/
def Phase7Ok (c : Stmt) : Prop :=
  ∀ env inp t s layout rate ood claims point slices, CodeRel env t s → t.roots.size ≤ 1 →
    Inputs env inp s.mem →
    LayoutAt s.mem (layoutR.at env.work) inp.bytecode layout rate →
    EqClaimAt s.mem (oodR.at env.work) ood → ClaimsAt s.mem (claimsR.at env.work) claims →
    KeccakOutAt s.mem (keccakR.at env.work) point slices →
    Runs env c (phase7M layout rate ood claims point slices) t s phase7Regions fun _ _ ↦ True

/-- **The end check** (`Model.verify`'s): the stream and the openings consumed. -/
def FinishOk (c : Stmt) : Prop :=
  ∀ env t s, CodeRel env t s →
    WP c s (fun s' ↦ (t.cursor == t.stream.size && t.phase == t.openings.size) = true ∧ Kept env [] s s')
      (fun s' ↦ (t.cursor == t.stream.size && t.phase == t.openings.size) = false ∧ Kept env [] s s')

/-- The model's state after the seed (`Model.verify`'s `start`). -/
def start (inp : Input) (stream : Array EW) (openings : Array (Array OpeningW)) : TState :=
  ⟨⟨Model.seed inp.bytecode inp.pub, #[], none⟩, stream, 0, openings, 0, #[]⟩

/-- The seed's hash input, the working area's first `n + 2` words. -/
def seedR (n : Nat) : Region := ⟨0, n + 2⟩

/-- **The decoder**: `Proof.fromBytes` of the wire bytes, decoded at the decoded area, or a failure
where it refuses them; either way `rdi` and every word outside its scratch and areas kept. -/
def DecodeOk (c : Stmt) : Prop :=
  ∀ (e : Wire.Env) (s : QState), Wire.Pre e → s.reg .rdi = e.x → s.mem = e.m0 →
    WP c s
      (fun s' ↦ ∃ π, Id.run (Proof.fromBytes (m := Id) keccakF1600 e.B) = some π ∧
        Decoded s'.mem e.da e.L π ∧ Wire.Kept e s')
      (fun s' ↦ Id.run (Proof.fromBytes (m := Id) keccakF1600 e.B) = none ∧ Wire.Kept e s')

end NativeVm.Code
