import Rv64Verifier.Sym.Api

/-!
# Following constant control flow

`symRunCode cfg code pc fuel` is `symRun` fetching from `code` by pc, so that it can follow
control flow: after a `JAL`, a `JALR` or a branch whose target folds to a constant `E.c`, it
continues there. A call made inside the run sets `ra` to a constant, so the callee's return is
followed too, and a loop-free call tree runs as one symbolic execution. It stops at a branch whose
condition is not constant, a jump to a target that is not constant, an `ECALL`, a word that does
not decode (`Stop.endOfCode`: the machine traps there), or when `fuel` runs out.
`symRunCode_sound` is `symRun_sound` for it, and `BlockSpec.of_expectCode` the `Expect` route.

The kernel finds an instruction by walking the code's word list, so a run over a large image
fetches from a window of it (`codeWindow`) whose instructions are the image's (`CodeSub`).
-/

namespace Rv64Verifier.Sym
open RiscvZkvm.Rv64

/-- Every instruction of `w` is the instruction of `code` at the same address. -/
def CodeSub (w code : Code) : Prop := ∀ pc i, w.fetch pc = some i → code.fetch pc = some i

theorem codeSub_refl (code : Code) : CodeSub code code := fun _ _ h => h

/-- The `n` words of `code` from index `i`, at their addresses. -/
def codeWindow (code : Code) (i n : Nat) : Code :=
  ⟨code.base + BitVec.ofNat 64 (4 * i), (code.words.drop i).take n⟩

theorem codeWindow_sub (code : Code) (i n : Nat) (h : code.base.toNat + 4 * (i + n) < 2 ^ 64) :
    CodeSub (codeWindow code i n) code := by
  intro pc x hx
  have hb : (code.base + BitVec.ofNat 64 (4 * i)).toNat = code.base.toNat + 4 * i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := code.base.isLt
    rw [Nat.mod_eq_of_lt (by omega : 4 * i < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  unfold Code.fetch at hx ⊢
  simp only [codeWindow, hb] at hx
  split at hx
  · rename_i hc
    rw [ite_eq_left ⟨by omega, hc.2⟩]
    obtain ⟨y, hy, hd⟩ := Option.bind_eq_some_iff.mp hx
    simp only [List.getElem?_take, List.getElem?_drop] at hy
    split at hy
    · rw [show (pc.toNat - code.base.toNat) / 4 = i + (pc.toNat - (code.base.toNat + 4 * i)) / 4
        by omega, hy]
      exact hd
    · cases hy
  · cases hx

def symRunCodeAux (cfg : Config) (code : Code) : Word → Nat → SymState → Option Result
  | pc, 0, σ => some ⟨σ, .c pc, .fuel, 0⟩
  | pc, f + 1, σ =>
    match code.fetch pc with
    | none => some ⟨σ, .c pc, .endOfCode, 0⟩
    | some i =>
      if isEcall i then some ⟨σ, .c pc, .ecall, 0⟩ else
      match classify i with
      | none => none
      | some m =>
        match symMicro cfg pc σ m with
        | none => none
        | some (σ', none) =>
          match symRunCodeAux cfg code (pc + 4) f σ' with
          | none => none
          | some r => some { r with steps := r.steps + 1 }
        | some (σ', some (.c t)) =>
          match symRunCodeAux cfg code t f σ' with
          | none => none
          | some r => some { r with steps := r.steps + 1 }
        | some (σ', some t) => some ⟨σ', t, m.stopKind, 1⟩

/-- Symbolically execute `code` from `pc` for at most `fuel` steps, following every jump and
branch whose target is a constant, from the identity symbolic state. -/
def symRunCode (cfg : Config) (code : Code) (pc : Word) (fuel : Nat) : Option Result :=
  symRunCodeAux cfg code pc fuel SymState.init

theorem symRunCodeAux_sound (cfg : Config) {w code : Code} (hsub : CodeSub w code)
    (s : MachineState) :
    ∀ (fuel : Nat) (pc : Word) (σ : SymState) (r : Result) (c : Word → Option Instr),
      symRunCodeAux cfg w pc fuel σ = some r → (∀ o ∈ r.st.obl, o.holds s) →
      (∃ c', Steps code r.steps (σ.toState s c pc) (r.toState s c')) ∧ σ.obl ⊆ r.st.obl ∧
        (r.stop = .ecall → code.fetch (r.pc.eval s) = some (.base .ECALL)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro pc σ r c h _
    simp only [symRunCodeAux, Option.some.injEq] at h; subst h
    exact ⟨⟨c, rfl⟩, List.Subset.refl _, by simp⟩
  | succ f ih =>
    intro pc σ r c h hobl
    simp only [symRunCodeAux] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      exact ⟨⟨c, rfl⟩, List.Subset.refl _, by simp⟩
    · rename_i i hf
      have hf' : code.fetch (σ.toState s c pc).pc = some i := hsub _ _ hf
      split at h
      · rename_i he
        simp only [Option.some.injEq] at h; subst h
        refine ⟨⟨c, rfl⟩, List.Subset.refl _, fun _ => ?_⟩
        rw [← isEcall_eq he]
        exact hf'
      · split at h
        · cases h
        · rename_i m hcl
          split at h
          · cases h
          · rename_i σ' hm
            split at h
            · cases h
            · rename_i r' hr'
              simp only [Option.some.injEq] at h; subst h
              obtain ⟨⟨c', hsteps⟩, hsub, hec⟩ :=
                ih (pc + 4) σ' r' (codeAfter code (σ.toState s c pc) i) hr' hobl
              obtain ⟨hsub', hexec⟩ :=
                symMicro_sound (c := c) hm s (fun o ho => hobl o (hsub ho))
              refine ⟨⟨c', Steps.cons ?_ hsteps⟩, List.Subset.trans hsub' hsub, hec⟩
              rw [classify_sound hf' hcl, hexec]
              rfl
          · rename_i σ' t hm
            split at h
            · cases h
            · rename_i r' hr'
              simp only [Option.some.injEq] at h; subst h
              obtain ⟨⟨c', hsteps⟩, hsub, hec⟩ :=
                ih t σ' r' (codeAfter code (σ.toState s c pc) i) hr' hobl
              obtain ⟨hsub', hexec⟩ :=
                symMicro_sound (c := c) hm s (fun o ho => hobl o (hsub ho))
              refine ⟨⟨c', Steps.cons ?_ hsteps⟩, List.Subset.trans hsub' hsub, hec⟩
              rw [classify_sound hf' hcl, hexec]
              rfl
          · rename_i σ' t _ hm
            simp only [Option.some.injEq] at h; subst h
            obtain ⟨hsub', hexec⟩ := symMicro_sound (c := c) hm s hobl
            refine ⟨⟨codeAfter code (σ.toState s c pc) i, Steps.cons ?_ (Steps.refl _ _)⟩,
              hsub', ?_⟩
            · rw [classify_sound hf' hcl, hexec]
              rfl
            · intro hst; cases m <;> cases hst

/-- **Soundness of the executor that follows constant control flow.** -/
theorem symRunCode_sound {cfg : Config} {w code : Code} {pc : Word} {fuel : Nat} {r : Result}
    (hrun : symRunCode cfg w pc fuel = some r) (hsub : CodeSub w code) (s : MachineState)
    (hpc : s.pc = pc) (hobl : r.obligs s) : ∃ c, Steps code r.steps s (r.toState s c) := by
  have := (symRunCodeAux_sound cfg hsub s fuel pc _ r s.code hrun
    ((Oblig.all_iff s _).mp hobl)).1
  rwa [← hpc, SymState.init_toState] at this

/-- When the run stopped at an `ECALL`, its final pc fetches that `ECALL`. -/
theorem symRunCode_ecall {cfg : Config} {w code : Code} {pc : Word} {fuel : Nat} {r : Result}
    (hrun : symRunCode cfg w pc fuel = some r) (hsub : CodeSub w code) (s : MachineState)
    (hobl : r.obligs s) (hstop : r.stop = .ecall) :
    code.fetch (r.pc.eval s) = some (.base .ECALL) :=
  (symRunCodeAux_sound cfg hsub s fuel pc _ r s.code hrun ((Oblig.all_iff s _).mp hobl)).2.2 hstop

theorem BlockSpec.of_symRunCode {cfg : Config} {w code : Code} {pc : Word} {fuel : Nat}
    {r : Result} (hrun : symRunCode cfg w pc fuel = some r) (hsub : CodeSub w code)
    {P : MachineState → Prop}
    {Q : MachineState → MachineState → Prop}
    (hobl : ∀ s, P s → r.obligs s) (hQ : ∀ s c, P s → Q s (r.toState s c)) :
    BlockSpec code pc r.steps P Q := by
  intro s hpc hP
  obtain ⟨c, h⟩ := symRunCode_sound hrun hsub s hpc (hobl s hP)
  exact ⟨_, h, hQ s c hP⟩

/-- A specification from one kernel check: `hrun` is
`(symRunCode cfg code pc fuel).any (·.meets cfg x) = true`, proved by `decide +kernel`. -/
theorem BlockSpec.of_expectCode {cfg : Config} {w code : Code} {pc : Word} {fuel : Nat}
    {x : Expect} (hrun : (symRunCode cfg w pc fuel).any (·.meets cfg x) = true)
    (hsub : CodeSub w code) {P : MachineState → Prop}
    {Q : MachineState → MachineState → Prop}
    (hobl : ∀ s, P s → Oblig.all s x.obl) (hQ : ∀ s t, P s → x.Holds s t → Q s t) :
    BlockSpec code pc x.steps P Q := by
  cases hr : symRunCode cfg w pc fuel with
  | none => rw [hr] at hrun; cases hrun
  | some r =>
    rw [hr] at hrun
    have hm : r.meets cfg x = true := hrun
    intro s hpc hP
    obtain ⟨hsteps, hobls, -⟩ := Result.meets_holds hm s (hobl s hP) s.code
    obtain ⟨c, h⟩ := symRunCode_sound hr hsub s hpc hobls
    obtain ⟨-, -, hx⟩ := Result.meets_holds hm s (hobl s hP) c
    exact ⟨_, hsteps ▸ h, hQ s _ hP hx⟩

end Rv64Verifier.Sym
