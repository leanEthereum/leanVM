module

public import NativeVm.Code.Roots
public import NativeVm.Code.Seed
public import NativeVm.Code.Gadgets
public import NativeVm.Code.Phase1
public import NativeVm.Code.Phase2
public import NativeVm.Code.Phase3
public import NativeVm.Code.Phase4
public import NativeVm.Code.Phase5
public import NativeVm.Code.Phase6
public import NativeVm.Code.Phase7
public import NativeVm.Equiv.Execution
public import NativeVm.Transcript.SeedState
public import Native.Context

/-!
# The leanVM verifier's code

`body` saves the callee-saved registers in the context's words `16 .. 21` (`NativeVm.Input`),
decodes the proof (`Wire.decode`), seeds the transcript (`Transcript.seed`), runs the seven phases
(`phase1` ... `phase7`, each in its module), checks the stream and the openings consumed
(`Transcript.finish`), restores the registers and sets `rax := 1`.

**Rejection is a failure.** Every check that rejects ends at `.fail`, inside the decoder, a
transcript gadget or a phase, so the code carries no verdict flag: `body` ends normally only when
the proof is accepted, and the failure handler `onFail` (`Compile.program body onFail`) restores
the registers and sets `rax := 0`. It finds the save area through `rdi`, so every part keeps `rdi`
at the context and the save area's words, on both exits (`Kept`, `Wire.Kept`): a failure leaves
the state `Exit` describes.

`body_spec`: from a context holding the wire bytes, the bytecode, the public input and the areas
(`BodyPre`), `body` ends normally with `rax = 1` and the registers restored, or fails in a state
from which `onFail` ends with `rax = 0` and the registers restored, `rax` being `1` exactly when
`verifyWith` accepts the decoded proof (`verdict`). It assumes the decoder's contract and the
phases' (`NativeVm.Code.Contracts`); the seed's and the end check's are proved from the
transcript's (`seed_run`, `finishOk`). `verifier_spec` adds the failure handler.
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Model LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
open NativeVm.Transcript (wd Fits Disj Env Foot SeedPre Layout ctxEnd scratchW ctxBytecode
  ctxBytecodeLen ctxPublic ctxWireLen ctxDecoded ctxWork cw eval_cw wp_store wp_load wd_inj
  wd_ne_of_disj BufIn)

/-! ## The code -/

/-- The save area: each callee-saved register's word of the context. -/
def saveSlots : List (Nat × Reg64) :=
  [(16, .rbx), (17, .rbp), (18, .r12), (19, .r13), (20, .r14), (21, .r15)]

/-- Save the callee-saved registers. -/
def save : Stmt := blk [
  I (.store (cw 16) .rbx), I (.store (cw 17) .rbp), I (.store (cw 18) .r12),
  I (.store (cw 19) .r13), I (.store (cw 20) .r14), I (.store (cw 21) .r15)]

/-- Restore the callee-saved registers. -/
def restore : Stmt := blk [
  I (.load .rbx (cw 16)), I (.load .rbp (cw 17)), I (.load .r12 (cw 18)),
  I (.load .r13 (cw 19)), I (.load .r14 (cw 20)), I (.load .r15 (cw 21))]

/-- **The leanVM verifier**: `rax := 1` if it accepts; a rejection fails, to `onFail`. -/
def body : Stmt := blk [
  save, Wire.decode, Transcript.seed,
  phase1, phase2, phase3, phase4, phase5, phase6, phase7,
  Transcript.finish, restore, I (.movi .rax 1)]

/-- **The failure handler**: the registers restored, `rax := 0`. -/
def onFail : Stmt := blk [restore, I (.movi .rax 0)]

/-! ## The verdict and the exits -/

/-- **The verdict**: the wire bytes decoded (`Proof.fromBytes`) and the proof verified
(`verifyWith`) against the bytecode and the public input; `false` if they do not decode. -/
def verdict (bytes : List UInt8) (inp : Input) : Bool :=
  (Id.run (Proof.fromBytes (m := Id) keccakF1600 bytes)).elim false fun π ↦
    Id.run (LeanVM.Protocol.Verifier.verifyWith (m := Id) keccakF1600
      (inp.bytecode.toList.map K.ofLane) inp.pub π)

/-- The save area holds the registers `sv`. -/
def Saved (mem : UInt64 → Option UInt64) (ctx : UInt64) (sv : Reg64 → UInt64) : Prop :=
  ∀ p ∈ saveSlots, mem (wd ctx p.1) = some (sv p.2)

/-- A failure's state: `rdi` at the context, the save area holding `sv`. -/
def Exit (ctx : UInt64) (sv : Reg64 → UInt64) (s : QState) : Prop :=
  s.reg .rdi = ctx ∧ Saved s.mem ctx sv

/-- The end: `rax` is `1` for `b`, `0` otherwise, and the callee-saved registers are `sv`. -/
def Ret (sv : Reg64 → UInt64) (b : Bool) (s : QState) : Prop :=
  s.reg .rax = (if b then 1 else 0) ∧ ∀ r ∈ Context.calleeSaved, s.reg r = sv r

theorem saveSlots_lt {p : Nat × Reg64} (hp : p ∈ saveSlots) : p.1 < scratchW := by
  simp only [saveSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rw [Transcript.scratchW_val]
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem save_spec {s : QState} {ctx : UInt64} {E : QState → Prop} (hrdi : s.reg .rdi = ctx)
    (hsome : ∀ p ∈ saveSlots, (s.mem (wd ctx p.1)).isSome) :
    WP save s (fun s' ↦ s'.reg = s.reg ∧ Saved s'.mem ctx s.reg ∧
      ∀ a, (∀ p ∈ saveSlots, a ≠ wd ctx p.1) → s'.mem a = s.mem a) E := by
  simp only [saveSlots, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hsome
  obtain ⟨h16, h17, h18, h19, h20, h21⟩ := hsome
  unfold save
  refine wp_store (eval_cw hrdi 16) h16 ?_
  refine wp_store (eval_cw (by simpa using hrdi) 17) (by simp; split <;> simp_all) ?_
  refine wp_store (eval_cw (by simpa using hrdi) 18) (by simp; split_ifs <;> simp_all) ?_
  refine wp_store (eval_cw (by simpa using hrdi) 19) (by simp; split_ifs <;> simp_all) ?_
  refine wp_store (eval_cw (by simpa using hrdi) 20) (by simp; split_ifs <;> simp_all) ?_
  refine wp_store (eval_cw (by simpa using hrdi) 21) (by simp; split_ifs <;> simp_all) ?_
  refine WP.blk_nil ⟨rfl, ?_, ?_⟩
  · intro p hp
    simp only [saveSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := omega) [QState.setMem_mem, wd_inj]
  · intro a ha
    simp only [saveSlots, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at ha
    simp [QState.setMem_mem, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2.1, ha.2.2.2.2.2]

theorem restore_spec {s : QState} {ctx : UInt64} {sv : Reg64 → UInt64} {E : QState → Prop}
    (hrdi : s.reg .rdi = ctx) (hsv : Saved s.mem ctx sv) :
    WP restore s (fun s' ↦ s'.reg .rax = s.reg .rax ∧ ∀ r ∈ Context.calleeSaved, s'.reg r = sv r)
      E := by
  have h : ∀ k r, (k, r) ∈ saveSlots → s.mem (wd ctx k) = some (sv r) := fun k r h ↦ hsv _ h
  unfold restore
  refine wp_load (eval_cw hrdi 16) (h 16 .rbx (by simp [saveSlots])) ?_
  refine wp_load (eval_cw (by simpa using hrdi) 17) (h 17 .rbp (by simp [saveSlots])) ?_
  refine wp_load (eval_cw (by simpa using hrdi) 18) (h 18 .r12 (by simp [saveSlots])) ?_
  refine wp_load (eval_cw (by simpa using hrdi) 19) (h 19 .r13 (by simp [saveSlots])) ?_
  refine wp_load (eval_cw (by simpa using hrdi) 20) (h 20 .r14 (by simp [saveSlots])) ?_
  refine wp_load (eval_cw (by simpa using hrdi) 21) (h 21 .r15 (by simp [saveSlots])) ?_
  refine WP.blk_nil ⟨by simp, ?_⟩
  simp [Context.calleeSaved]

theorem calleeSaved_ne_rax {r : Reg64} (hr : r ∈ Context.calleeSaved) : r ≠ .rax := by
  simp only [Context.calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `rax := v` ends the run with the callee-saved registers kept. -/
theorem movi_ret {s : QState} {sv : Reg64 → UInt64} {b : Bool} {E : QState → Prop} {v : Int64}
    (hcs : ∀ r ∈ Context.calleeSaved, s.reg r = sv r) (hv : v.toUInt64 = if b then 1 else 0) :
    WP (blk [I (.movi .rax v)]) s (Ret sv b) E :=
  Transcript.wp_reg rfl (WP.blk_nil ⟨by simp [hv], fun r hr ↦ by
    simp [calleeSaved_ne_rax hr, hcs r hr]⟩)

/-- **The failure handler**: from a failure's state, `rax = 0` and the registers restored. -/
theorem onFail_spec {s : QState} {ctx : UInt64} {sv : Reg64 → UInt64} (h : Exit ctx sv s) :
    WP onFail s (Ret sv false) (fun _ ↦ False) := by
  unfold onFail
  refine WP.blk_cons (WP.mono (restore_spec h.1 h.2) (fun s₁ h₁ ↦ ?_) fun _ h ↦ h)
  exact movi_ret h₁.2 rfl

/-! ## The seed and the end check -/

/-- **The end check** keeps every word and `rdi`. -/
theorem finishOk : FinishOk Transcript.finish := fun _ _ _ hr ↦
  WP.mono (finishM_spec hr)
    (fun _ ⟨hc, hm, hf⟩ ↦ ⟨hc, (hf .rdi (by decide)).trans hr.rdi, fun a _ _ ↦ by rw [hm]⟩)
    fun _ ⟨hc, hm, hf⟩ ↦ ⟨hc, (hf .rdi (by decide)).trans hr.rdi, fun a _ _ ↦ by rw [hm]⟩

/-- An opening as the decoded proof holds it. -/
def ofOpening (o : Opening) : OpeningW := ⟨o.leafIndex.toUInt64, (o.leaf.map K.lane).toArray, o.path.toArray⟩

theorem toOpening_ofOpening {o : Opening} (h : o.leafIndex < 2 ^ 64) : (ofOpening o).toOpening = o := by
  obtain ⟨i, leaf, path⟩ := o
  simp only [ofOpening, OpeningW.toOpening, List.map_map, List.toList_toArray]
  congr
  · exact Transcript.toNat_toUInt64 h
  · exact (List.map_congr_left fun x _ ↦ Field.ofLane_lane x).trans (List.map_id _)

/-- **The decoded proof as the model's arrays.** -/
theorem exists_model {mem : UInt64 → Option UInt64} {a : UInt64} {L : Nat} {π : Proof}
    (h : Decoded mem a L π) : ∃ (stream : Array EW) (openings : Array (Array OpeningW)),
      stream.toList.map EW.toE = π.stream ∧ openings.toList.map Equiv.phaseOpenings = π.openings := by
  refine ⟨(π.stream.map EW.ofE).toArray, (π.openings.map fun ph ↦ (ph.map ofOpening).toArray).toArray,
    ?_, ?_⟩
  · simp only [List.map_map]
    exact (List.map_congr_left fun x _ ↦ Equiv.EW.toE_ofE x).trans (List.map_id _)
  · simp only [List.map_map]
    refine (List.map_congr_left fun ph hph ↦ ?_).trans (List.map_id _)
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hph
    obtain ⟨hh, width, -, -, -, -, -, -, hd⟩ := h.2.2.2.2.2 k hk
    simp only [Function.comp, Equiv.phaseOpenings, List.map_map, id]
    refine (List.map_congr_left fun o ho ↦ ?_).trans (List.map_id _)
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ho
    exact toOpening_ofOpening (by have := (hd j hj).2.2.1; omega)

/-- **The seed** from its statement-level spec (`Transcript.seed_spec`). -/
theorem seed_run {env : Env} {inp : Input} {s : QState}
    (h : SeedPre env inp.bcA (inp.bytecode.toList.map K.ofLane) inp.pub s) {stream : Array EW}
    {openings : Array (Array OpeningW)} (hs : stream.toList.map EW.toE = env.proof.stream)
    (ho : openings.toList.map Equiv.phaseOpenings = env.proof.openings) :
    WP Transcript.seed s (fun s' ↦ CodeRel env (start inp stream openings) s' ∧
      Kept env [seedR inp.bytecode.size] s s') (fun _ ↦ False) := by
  refine WP.mono (seedM_spec (bytecode := inp.bytecode) (publicInput := inp.pub)
    (Transcript.seed_spec h) hs ho) (fun s' ⟨hr, hf, hm⟩ ↦ ⟨hr, ?_, ?_⟩) fun _ h ↦ h
  · exact (hf .rdi (by decide)).trans h.rdi
  · intro a hfoot hin
    refine hm a hfoot fun ⟨k, hk, e⟩ ↦ hin _ (List.mem_singleton_self _) ⟨k, ?_, ?_⟩
    · simpa [seedR] using hk
    · simpa [seedR] using e

/-! ## Steps -/

theorem step {s : QState} {x : Stmt} {xs : List Stmt} {Q R P E : QState → Prop} (h : WP x s Q R)
    (hq : ∀ s₁, Q s₁ → (∀ a, (s₁.mem a).isSome = (s.mem a).isSome) → WP (blk xs) s₁ P E)
    (hr : ∀ s₁, R s₁ → E s₁) : WP (blk (x :: xs)) s P E :=
  WP.blk_cons (WP.mono (Transcript.WP.frame h) (fun s₁ h₁ ↦ hq s₁ h₁.1 h₁.2.1) fun s₁ h₁ ↦ hr s₁ h₁.1)

theorem stops {rs : List Region} (h : ∀ r ∈ rs, r ∈ regions) (n : Nat) :
    ∀ r ∈ rs, r.stop ≤ workWords n := fun r hr ↦ stop_le_of_mem (h r hr) n

theorem Saved.kept {env : Env} {inp : Input} {rs : List Region} {s s' : QState}
    {sv : Reg64 → UInt64} (hsv : Saved s.mem env.ctx sv) (hk : Kept env rs s s')
    (hin : Inputs env inp s.mem) (hrs : ∀ r ∈ rs, r.stop ≤ workWords inp.bytecode.size) :
    Saved s'.mem env.ctx sv := fun p hp ↦ by
  rw [hk.ctx hin hrs (saveSlots_lt hp)]; exact hsv p hp

theorem exit_of {env : Env} {inp : Input} {rs : List Region} {s s' : QState}
    {sv : Reg64 → UInt64} (hk : Kept env rs s s') (hin : Inputs env inp s.mem)
    (hsv : Saved s.mem env.ctx sv) (hrs : ∀ r ∈ rs, r.stop ≤ workWords inp.bytecode.size) :
    Exit env.ctx sv s' := ⟨hk.1, hsv.kept hk hin hrs⟩

/-! ## The phases -/

/-- **The phases and the end check** compute `Model.verify` from the seed's state. -/
theorem phases_spec (h1 : Phase1Ok phase1) (h2 : Phase2Ok phase2) (h3 : Phase3Ok phase3)
    (h4 : Phase4Ok phase4) (h5 : Phase5Ok phase5) (h6 : Phase6Ok phase6) (h7 : Phase7Ok phase7)
    {env : Env} {inp : Input} {stream : Array EW} {openings : Array (Array OpeningW)} {s : QState}
    {sv : Reg64 → UInt64} (hr : CodeRel env (start inp stream openings) s)
    (hin : Inputs env inp s.mem) (hsv : Saved s.mem env.ctx sv) :
    WP (blk [phase1, phase2, phase3, phase4, phase5, phase6, phase7, Transcript.finish, restore,
        I (.movi .rax 1)]) s
      (Ret sv (Model.verify inp.bytecode inp.pub stream openings))
      (fun s' ↦ Model.verify inp.bytecode inp.pub stream openings = false ∧ Exit env.ctx sv s') := by
  have hV := verify_chain inp stream openings
  have hroots : (start inp stream openings).roots = #[] := rfl
  generalize Model.verify inp.bytecode inp.pub stream openings = V at hV ⊢
  generalize start inp stream openings = t0 at hr hV hroots
  have hrs1 := stops (rs := [layoutR, scratchR]) (by decide +kernel) inp.bytecode.size
  have hrs2 := stops (rs := [oodR, scratchR]) (by decide +kernel) inp.bytecode.size
  have hrs3 := stops (rs := [busR, claimsR, scratchR]) (by decide +kernel) inp.bytecode.size
  have hrs4 := stops (rs := [evalsR, claimsR, scratchR]) (by decide +kernel) inp.bytecode.size
  have hrs5 := stops (rs := [claimsR, scratchR]) (by decide +kernel) inp.bytecode.size
  have hrs6 := stops (rs := [keccakR, claimsR, scratchR]) (by decide +kernel) inp.bytecode.size
  have hrs7 := stops (rs := phase7Regions) (by decide +kernel) inp.bytecode.size
  have hrs0 := stops (rs := []) (by decide +kernel) inp.bytecode.size
  -- phase 1
  refine step (h1 env inp t0 s hr hin) (fun s₁ h hd ↦ ?_)
    (fun s₁ h ↦ ⟨by rw [hV, h.1], exit_of h.2 hin hsv hrs1⟩)
  obtain ⟨⟨layout, rate⟩, t1, hrun₁, hr₁, hlay, hk₁⟩ := h
  rw [hrun₁] at hV; simp only at hV
  have hin₁ := hin.kept hk₁ hrs1 hd
  have hsv₁ := hsv.kept hk₁ hin hrs1
  -- phase 2
  have hroots₁ : t1.roots.size < Transcript.maxRoots := by
    rw [(readAnnouncedSizes_roots _).keeps _ _ _ hrun₁, hroots]; decide
  refine step (h2 env inp t1 s₁ layout rate hr₁ hroots₁ hin₁ hlay) (fun s₂ h hd ↦ ?_)
    (fun s₂ h ↦ ⟨by rw [hV, h.1], exit_of h.2 hin₁ hsv₁ hrs2⟩)
  obtain ⟨ood, t2, hrun, hr₂, hood, hk₂⟩ := h
  have hR₂ : t2.roots.size ≤ 1 := by
    have := (phase2M_roots layout rate).grows _ _ _ hrun
    rw [(readAnnouncedSizes_roots _).keeps _ _ _ hrun₁, hroots] at this
    simpa using this
  rw [hrun] at hV; simp only at hV
  have hin₂ := hin₁.kept hk₂ hrs2 hd
  have hsv₂ := hsv₁.kept hk₂ hin₁ hrs2
  have hlay₂ := hlay.congr (hk₂.same hin₁ hrs2 (q := layoutR) (by decide +kernel) (by decide +kernel))
  -- phase 3
  refine step (h3 env inp t2 s₂ layout rate hr₂ hin₂ hlay₂) (fun s₃ h hd ↦ ?_)
    (fun s₃ h ↦ ⟨by rw [hV, h.1], exit_of h.2 hin₂ hsv₂ hrs3⟩)
  obtain ⟨bus, t3, hrun, hr₃, ⟨hbus, hcl₃, hsz₃⟩, hk₃⟩ := h
  have hR₃ : t3.roots.size ≤ 1 := by rw [(verifyBusBalance_roots _).keeps _ _ _ hrun]; exact hR₂
  rw [hrun] at hV; simp only at hV
  have hin₃ := hin₂.kept hk₃ hrs3 hd
  have hsv₃ := hsv₂.kept hk₃ hin₂ hrs3
  have hlay₃ := hlay₂.congr (hk₃.same hin₂ hrs3 (q := layoutR) (by decide +kernel) (by decide +kernel))
  have hood₃ := hood.congr (hk₃.same hin₂ hrs3 (q := oodR) (by decide +kernel) (by decide +kernel))
  -- phase 4
  refine step (h4 env inp t3 s₃ layout rate bus bus.claims hr₃ hin₃ hlay₃ hbus hcl₃ hsz₃)
    (fun s₄ h hd ↦ ?_) (fun s₄ h ↦ ⟨by rw [hV, h.1], exit_of h.2 hin₃ hsv₃ hrs4⟩)
  obtain ⟨ev, t4, hrun, hr₄, ⟨hev, hcl₄, hsz₄⟩, hk₄⟩ := h
  have hR₄ : t4.roots.size ≤ 1 := by rw [(tablePhase_roots _ _).keeps _ _ _ hrun]; exact hR₃
  rw [hrun] at hV; simp only at hV
  have hin₄ := hin₃.kept hk₄ hrs4 hd
  have hsv₄ := hsv₃.kept hk₄ hin₃ hrs4
  have hlay₄ := hlay₃.congr (hk₄.same hin₃ hrs4 (q := layoutR) (by decide +kernel) (by decide +kernel))
  have hood₄ := hood₃.congr (hk₄.same hin₃ hrs4 (q := oodR) (by decide +kernel) (by decide +kernel))
  -- phase 5
  refine step (h5 env inp t4 s₄ layout rate _ hr₄ hin₄ hlay₄ hcl₄
    (by rw [Array.size_append]; omega)) (fun s₅ h hd ↦ ?_)
    (fun s₅ h ↦ ⟨by rw [hV, h.1], exit_of h.2 hin₄ hsv₄ hrs5⟩)
  obtain ⟨pc, t5, hrun, hr₅, ⟨hcl₅, hsz₅⟩, hk₅⟩ := h
  have hR₅ : t5.roots.size ≤ 1 := by rw [(publicInputPhase_roots _ _).keeps _ _ _ hrun]; exact hR₄
  rw [hrun] at hV; simp only at hV
  have hin₅ := hin₄.kept hk₅ hrs5 hd
  have hsv₅ := hsv₄.kept hk₅ hin₄ hrs5
  have hlay₅ := hlay₄.congr (hk₅.same hin₄ hrs5 (q := layoutR) (by decide +kernel) (by decide +kernel))
  have hood₅ := hood₄.congr (hk₅.same hin₄ hrs5 (q := oodR) (by decide +kernel) (by decide +kernel))
  have hev₅ := hev.congr (hk₅.same hin₄ hrs5 (q := evalsR) (by decide +kernel) (by decide +kernel))
  -- phase 6
  refine step (h6 env inp t5 s₅ layout rate ev _ hr₅ hin₅ hlay₅ hev₅ hcl₅
    (by simp only [Array.size_append]; omega)) (fun s₆ h hd ↦ ?_)
    (fun s₆ h ↦ ⟨by rw [hV, h.1], exit_of h.2 hin₅ hsv₅ hrs6⟩)
  obtain ⟨r6, t6, hrun, hr₆, ⟨hkec, hcl₆, -⟩, hk₆⟩ := h
  have hR₆ : t6.roots.size ≤ 1 := by rw [(keccakPhase_roots _ _).keeps _ _ _ hrun]; exact hR₅
  rw [hrun] at hV; simp only at hV
  have hin₆ := hin₅.kept hk₆ hrs6 hd
  have hsv₆ := hsv₅.kept hk₆ hin₅ hrs6
  have hlay₆ := hlay₅.congr (hk₆.same hin₅ hrs6 (q := layoutR) (by decide +kernel) (by decide +kernel))
  have hood₆ := hood₅.congr (hk₆.same hin₅ hrs6 (q := oodR) (by decide +kernel) (by decide +kernel))
  -- phase 7
  refine step (h7 env inp t6 s₆ layout rate ood _ r6.2.1 r6.2.2 hr₆ hR₆ hin₆ hlay₆ hood₆ hcl₆ hkec)
    (fun s₇ h hd ↦ ?_) (fun s₇ h ↦ ⟨by rw [hV, h.1], exit_of h.2 hin₆ hsv₆ hrs7⟩)
  obtain ⟨⟨⟩, t7, hrun, hr₇, -, hk₇⟩ := h
  rw [hrun] at hV; simp only at hV
  have hin₇ := hin₆.kept hk₇ hrs7 hd
  have hsv₇ := hsv₆.kept hk₇ hin₆ hrs7
  -- the end check
  refine step (finishOk env t7 s₇ hr₇) (fun s₈ h _ ↦ ?_)
    (fun s₈ h ↦ ⟨by rw [hV]; exact h.1, exit_of h.2 hin₇ hsv₇ hrs0⟩)
  have hV' : V = true := by rw [hV]; exact h.1
  refine WP.blk_cons (WP.mono (restore_spec h.2.1 (hsv₇.kept h.2 hin₇ hrs0)) (fun s₉ h₉ ↦ ?_)
    fun _ h ↦ h)
  exact movi_ret h₉.2 (by rw [hV']; rfl)

/-! ## The body -/

/-- **What the caller provides**: `rdi` at the context; the decoder's preconditions (`Wire.Pre`:
the wire bytes, the decoded and working areas recorded in the context); the context's words up to
`ctxEnd`; the bytecode's address and length at words `2`, `3` and its words; the public input at
words `4 .. 7`; the working area of `workWords n` words, `n` the bytecode's length; every area
inside the address space and apart from the others. -/
structure BodyPre (s : QState) (we : Wire.Env) (inp : Input) : Prop where
  rdi : s.reg .rdi = we.x
  mem : s.mem = we.m0
  wire : Wire.Pre we
  fitCtx : Fits we.x ctxEnd
  ctxSome : ∀ k < ctxEnd, (s.mem (wd we.x k)).isSome
  disjCtxDec : Disj we.x ctxEnd we.da (decodedWords we.L)
  bcPtr : s.mem (wd we.x ctxBytecode) = some inp.bcA
  bcLen : NatAt s.mem (wd we.x ctxBytecodeLen) inp.bytecode.size
  bcWords : WordArr s.mem inp.bcA inp.bytecode
  pubWords : ∀ i (h : i < 4), s.mem (wd we.x (ctxPublic + i)) = some inp.pub[i]
  bcSmall : 8 * inp.bytecode.size + 9 < 2 ^ 32
  fitBc : Fits inp.bcA inp.bytecode.size
  fitWork : Fits we.wk (workWords inp.bytecode.size)
  disjCtxWork : Disj we.x ctxEnd we.wk (workWords inp.bytecode.size)
  disjDecWork : Disj we.da (decodedWords we.L) we.wk (workWords inp.bytecode.size)
  disjBcCtx : Disj inp.bcA inp.bytecode.size we.x ctxEnd
  disjBcDec : Disj inp.bcA inp.bytecode.size we.da (decodedWords we.L)
  disjBcWork : Disj inp.bcA inp.bytecode.size we.wk (workWords inp.bytecode.size)
  workSome : ∀ k < workWords inp.bytecode.size, (s.mem (wd we.wk k)).isSome

theorem fits_mono {b : UInt64} {n m : Nat} (h : Fits b n) (hm : m ≤ n) : Fits b m := by
  unfold Fits at *; omega

theorem disj_mono {a b : UInt64} {n m n' m' : Nat} (h : Disj a n b m) (hn : n' ≤ n) (hm : m' ≤ m) :
    Disj a n' b m' := by
  unfold Disj at *; omega

theorem saveSlots_ge {p : Nat × Reg64} (hp : p ∈ saveSlots) : 16 ≤ p.1 := by
  simp only [saveSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem save_ne {ctx : UInt64} {j : Nat} (hj : j < 16) : ∀ p ∈ saveSlots, wd ctx j ≠ wd ctx p.1 :=
  fun p hp e ↦ by
    have h1 := saveSlots_lt hp
    have h2 := saveSlots_ge hp
    rw [Transcript.scratchW_val] at h1
    have := (wd_inj (by omega) (by omega)).mp e
    omega

theorem saveSlots_lt' {p : Nat × Reg64} (hp : p ∈ saveSlots) : p.1 < 32 := by
  have := saveSlots_lt hp
  rwa [Transcript.scratchW_val] at this

/-- **`body` verifies**: from `BodyPre`, it ends normally with `rax = 1`, or fails, in a state
from which `onFail` restores, exactly when the verdict is `false`; it keeps the callee-saved
registers. It assumes the decoder's and the phases' contracts. -/
theorem body_spec (hD : DecodeOk Wire.decode) (h1 : Phase1Ok phase1) (h2 : Phase2Ok phase2)
    (h3 : Phase3Ok phase3) (h4 : Phase4Ok phase4) (h5 : Phase5Ok phase5) (h6 : Phase6Ok phase6)
    (h7 : Phase7Ok phase7) {s : QState} {we : Wire.Env} {inp : Input} (hp : BodyPre s we inp) :
    WP body s (Ret s.reg (verdict we.B inp))
      (fun s' ↦ verdict we.B inp = false ∧ Exit we.x s.reg s') := by
  have hw := hp.wire
  have hn := seedBuf_le inp.bytecode.size
  have hwk := wireWork_le inp.bytecode.size
  have hce : ctxEnd = 175 := Transcript.ctxEnd_val
  have hsw : Keccak.scratchWords = 84 := Transcript.scratchWords_val
  unfold body
  refine step (save_spec (E := fun _ ↦ False) hp.rdi fun p hp' ↦
      hp.ctxSome _ (by have := saveSlots_lt' hp'; omega))
    (fun s₁ h hd₁ ↦ ?_) fun _ h ↦ h.elim
  obtain ⟨hreg₁, hsv₁, hfr₁⟩ := h
  have hlow₁ : ∀ j < 16, s₁.mem (wd we.x j) = s.mem (wd we.x j) := fun j hj ↦ hfr₁ _ (save_ne hj)
  have hbc₁ : ∀ i < inp.bytecode.size, s₁.mem (wd inp.bcA i) = s.mem (wd inp.bcA i) :=
    fun i hi ↦ hfr₁ _ fun p hp' e ↦
      wd_ne_of_disj hp.fitBc hp.fitCtx hp.disjBcCtx hi (by have := saveSlots_lt' hp'; omega) e
  -- the decoder
  let e : Wire.Env := { we with m0 := s₁.mem }
  have hm : ∀ a, s.mem a = we.m0 a := fun a ↦ by rw [hp.mem]
  have hpre : Wire.Pre e :=
    { fx := hw.fx, fw := hw.fw, fd := hw.fd, fk := hw.fk, xw := hw.xw, xd := hw.xd, xk := hw.xk,
      wd := hw.wd, wk' := hw.wk', dk := hw.dk, hold := hw.hold, L32 := hw.L32
      c0 := (hlow₁ 0 (by decide)).trans ((hm _).trans hw.c0)
      c1 := (hlow₁ 1 (by decide)).trans ((hm _).trans hw.c1)
      c8 := (hlow₁ 8 (by decide)).trans ((hm _).trans hw.c8)
      c9 := by
        obtain ⟨v, hv, hle⟩ := hw.c9
        exact ⟨v, (hlow₁ 9 (by decide)).trans ((hm _).trans hv), hle⟩
      c10 := (hlow₁ 10 (by decide)).trans ((hm _).trans hw.c10)
      c11 := by
        obtain ⟨v, hv, hle⟩ := hw.c11
        exact ⟨v, (hlow₁ 11 (by decide)).trans ((hm _).trans hv), hle⟩
      scr := fun k hk ↦ by
        show (s₁.mem _).isSome = true
        rw [hd₁, hm]; exact hw.scr k hk
      wire := fun k hk ↦ by
        show s₁.mem _ = _
        rw [hfr₁ _ fun p hp' e' ↦ Wire.adr_ne hw.fx hw.fw hw.xw (k := p.1)
          (by have := saveSlots_lt' hp'; unfold Wire.ctxN Wire.cScr; omega) hk e'.symm, hm]
        exact hw.wire k hk
      dec := fun k hk ↦ by
        show (s₁.mem _).isSome = true
        rw [hd₁, hm]; exact hw.dec k hk
      work := fun k hk ↦ by
        show (s₁.mem _).isSome = true
        rw [hd₁, hm]; exact hw.work k hk }
  have hout : ∀ j < 32, Wire.Out e (wd we.x j) := fun j hj ↦ hpre.out_ctx (k := j) hj
  refine step (hD e s₁ hpre (by rw [hreg₁]; exact hp.rdi) rfl) (fun s₂ h hd₂ ↦ ?_)
    (fun s₂ h ↦ ⟨?_, h.2.1, fun p hp' ↦ ?_⟩)
  rotate_left
  · have hnone : Id.run (Proof.fromBytes (m := Id) keccakF1600 we.B) = none := h.1
    unfold verdict
    rw [hnone]
    rfl
  · exact (h.2.2 _ (hout _ (saveSlots_lt' hp'))).trans (hsv₁ p hp')
  obtain ⟨π, hπ, hdec, hk₂⟩ := h
  have hlow₂ : ∀ j < 16, s₂.mem (wd we.x j) = s.mem (wd we.x j) :=
    fun j hj ↦ (hk₂.2 _ (hout j (by omega))).trans (hlow₁ j hj)
  have hbc₂ : ∀ i < inp.bytecode.size, s₂.mem (wd inp.bcA i) = s.mem (wd inp.bcA i) := by
    intro i hi
    refine (hk₂.2 _ ⟨fun k hk e' ↦ ?_, fun k hk e' ↦ ?_, fun k hk e' ↦ ?_⟩).trans (hbc₁ i hi)
    · exact wd_ne_of_disj hp.fitBc hp.fitCtx hp.disjBcCtx hi
        (by unfold Wire.cScr; omega) e'
    · exact wd_ne_of_disj hp.fitBc hw.fd hp.disjBcDec hi hk e'
    · exact wd_ne_of_disj hp.fitBc hp.fitWork hp.disjBcWork hi (by omega) e'
  have hdom₂ : ∀ a, (s₂.mem a).isSome = (s.mem a).isSome := fun a ↦ (hd₂ a).trans (hd₁ a)
  have hsv₂ : Saved s₂.mem we.x s.reg :=
    fun p hp' ↦ (hk₂.2 _ (hout _ (saveSlots_lt' hp'))).trans (hsv₁ p hp')
  let env : Env := ⟨we.x, we.da, we.wk, we.L, π⟩
  have hin₂ : Inputs env inp s₂.mem :=
    { bcPtr := (hlow₂ 2 (by decide)).trans hp.bcPtr
      bcLen := hp.bcLen.congr (hlow₂ 3 (by decide))
      bcWords := fun i hi ↦ (hbc₂ i hi).trans (hp.bcWords i hi)
      pubWords := fun i hi ↦ (hlow₂ (4 + i) (by omega)).trans (hp.pubWords i hi)
      fitCtx := hp.fitCtx, fitBc := hp.fitBc, fitWork := hp.fitWork, disjCtx := hp.disjCtxWork
      disjDec := hp.disjDecWork, disjBcCtx := hp.disjBcCtx, disjBcWork := hp.disjBcWork
      workSome := fun k hk ↦ by rw [hdom₂]; exact hp.workSome k hk }
  have htw := transcriptWords_le inp.bytecode.size
  have hseed : SeedPre env inp.bcA (inp.bytecode.toList.map K.ofLane) inp.pub s₂ :=
    { rdi := hk₂.1
      layout :=
        { fitCtx := hp.fitCtx, fitDec := hw.fd, fitWork := fits_mono hp.fitWork htw
          disjCD := hp.disjCtxDec, disjCW := disj_mono hp.disjCtxWork le_rfl htw
          disjDW := disj_mono hp.disjDecWork le_rfl htw
          ctxSome := fun k hk ↦ by rw [hdom₂]; exact hp.ctxSome k hk
          workSome := fun k hk ↦ by rw [hdom₂]; exact hp.workSome k (by omega)
          decPtr := (hlow₂ 8 (by decide)).trans ((hm _).trans hw.c8)
          workPtr := (hlow₂ 10 (by decide)).trans ((hm _).trans hw.c10) }
      decoded := hdec
      wireLen := (hlow₂ 1 (by decide)).trans ((hm _).trans hw.c1)
      L64 := by have := hw.L32; show we.L < 2 ^ 64; omega
      bcPtr := (hlow₂ 2 (by decide)).trans hp.bcPtr
      bcLen := by
        rw [List.length_map, Array.length_toList]
        exact (hlow₂ 3 (by decide)).trans hp.bcLen.2
      bcWords := fun i hi ↦ by
        rw [List.length_map, Array.length_toList] at hi
        rw [hbc₂ i hi, hp.bcWords i hi]
        simp only [List.getElem_map, Array.getElem_toList]
        rfl
      pubWords := fun i hi ↦ (hlow₂ (4 + i) (by omega)).trans (hp.pubWords i hi)
      bcSmall := by simpa using hp.bcSmall
      fitBc := by simpa using hp.fitBc
      fitBuf := fits_mono hp.fitWork (by simpa using hn)
      bufSome := fun k hk ↦ by
        rw [hdom₂]; exact hp.workSome k (by simp only [List.length_map, Array.length_toList] at hk; omega)
      disjBufCtx := disj_mono (Disj.symm hp.disjCtxWork) (by simpa using hn) le_rfl
      disjBufDec := disj_mono (Disj.symm hp.disjDecWork) (by simpa using hn) le_rfl
      disjBufBc := disj_mono (Disj.symm hp.disjBcWork) (by simpa using hn) (by simp) }
  -- the seed
  obtain ⟨stream, openings, hs, ho⟩ := exists_model hdec
  have hπ' : Id.run (Proof.fromBytes (m := Id) keccakF1600 we.B) = some π := hπ
  have hverd : verdict we.B inp = Model.verify inp.bytecode inp.pub stream openings := by
    rw [Equiv.verify_eq, hs, ho]
    unfold verdict
    rw [hπ']
    rfl
  rw [hverd]
  refine step (seed_run hseed (stream := stream) (openings := openings) hs ho)
    (fun s₃ h hd₃ ↦ ?_) fun _ h ↦ h.elim
  obtain ⟨hr₃, hk₃⟩ := h
  have hrsS : ∀ r ∈ [seedR inp.bytecode.size], r.stop ≤ workWords inp.bytecode.size := by
    simpa [seedR, Region.stop] using hn
  have hin₃ := hin₂.kept hk₃ hrsS hd₃
  have hsv₃ : Saved s₃.mem env.ctx s.reg := Saved.kept hsv₂ hk₃ hin₂ hrsS
  exact phases_spec h1 h2 h3 h4 h5 h6 h7 hr₃ hin₃ hsv₃

/-- **The verifier with its failure handler**: `body` ends normally with `rax` the verdict, or
fails and `onFail` ends normally with `rax` the verdict (then `0`); the callee-saved registers kept
either way. -/
theorem verifier_spec (hD : DecodeOk Wire.decode) (h1 : Phase1Ok phase1) (h2 : Phase2Ok phase2)
    (h3 : Phase3Ok phase3) (h4 : Phase4Ok phase4) (h5 : Phase5Ok phase5) (h6 : Phase6Ok phase6)
    (h7 : Phase7Ok phase7) {s : QState} {we : Wire.Env} {inp : Input} (hp : BodyPre s we inp) :
    WP body s (Ret s.reg (verdict we.B inp))
      (fun s' ↦ WP onFail s' (Ret s.reg (verdict we.B inp)) (fun _ ↦ False)) :=
  WP.mono (body_spec hD h1 h2 h3 h4 h5 h6 h7 hp) (fun _ h ↦ h) fun _ ⟨hv, hx⟩ ↦ hv ▸ onFail_spec hx

end NativeVm.Code
