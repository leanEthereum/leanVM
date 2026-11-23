module

public import NativeRustcVmArm.Whir.NextLevel.Exec
public import NativeRustcVmArm.Whir.TFrame
public import NativeRustcVmArm.Whir.Block
public import NativeRustcVmArm.Whir.FoldRounds.Basic
public import NativeRustcVmArm.Whir.State
public import NativeRustcVm.Whir.Model
public import NativeRustcVm.Whir.Sample

/-!
# `next_level`: its frame, its context, the model

From the entry `m0` (the `TState` X0, the index X1, the level X2, the next level's fold X3 and rate
exponent X4, `μ` X5, the `WhirW` X6): the 8192-byte frame (`NFr`, X19 to X30 saved at `8096` to
`8192`), the outputs until `glue_level` (`outs`: the `TState` and the query buffer), the context
`ctx` for the calls, the addresses as numbers (`Geo`). `run_eq`: `nextLevelM` as a chain of its
steps.
-/

namespace NativeRustcVmArm.Whir.NextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters

@[expose] public section

/-- The `TState`. -/
abbrev tA (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- The level. -/
abbrev lA (m0 : MachineData) : BitVec 64 := m0.regs.X2.toBitVec
/-- The `WhirW`. -/
abbrev pA (m0 : MachineData) : BitVec 64 := m0.regs.X6.toBitVec
/-- The `WhirW`'s query buffer. -/
abbrev qA (m0 : MachineData) : BitVec 64 := off (pA m0) queriesOff

/-- The outputs before `glue_level`: the `TState`, the query buffer. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (tA m0) tstateBytes q ∨ InRange (qA m0) queryBufBytes q

/-- The frame. -/
abbrev NFr (m0 st : MachineData) : Prop := Fr m0 8192 nextLevelStack slots [] (outs m0) st

/-- The frame's byte `o`. -/
abbrev loc (m0 : MachineData) (o : Nat) : BitVec 64 := base m0 8192 + BitVec.ofNat 64 o

/-- The addresses as numbers: SP, the `TState`, the `WhirW`, the level, the decoded area. -/
structure Geo (sp t p l aw al : Nat) : Prop where
  hN : 11424 ≤ sp
  hsp : sp < 2 ^ 64
  tW : t + 760 ≤ 2 ^ 64
  pW : p + 63200 ≤ 2 ^ 64
  lW : l + 24 ≤ 2 ^ 64
  aW : aw + al ≤ 2 ^ 64
  tS : t + 760 ≤ sp - 11424 ∨ sp ≤ t
  aS : aw + al ≤ sp - 11424 ∨ sp ≤ aw
  pS : p + 63200 ≤ sp - 11424 ∨ sp ≤ p
  lS : l + 24 ≤ sp - 11424 ∨ sp ≤ l
  pT : p + 63200 ≤ t ∨ t + 760 ≤ p
  pA : p + 63200 ≤ aw ∨ aw + al ≤ p
  tA : t + 760 ≤ aw ∨ aw + al ≤ t
  lP : l + 24 ≤ p ∨ p + 63200 ≤ l
  lT : l + 24 ≤ t ∨ t + 760 ≤ l

end

public section

theorem stack_eq : nextLevelStack = 11424 := rfl

theorem slots_le : ∀ p ∈ slots, 8096 ≤ p.1 ∧ p.1 + 8 ≤ 8192 := by decide

theorem slots_le' : ∀ p ∈ slots, p.1 + 8 ≤ 8192 := fun p hp ↦ (slots_le p hp).2

theorem apart_nat {a b : BitVec 64} {n m : Nat} (h : Apart a n b m) :
    a.toNat + n ≤ b.toNat ∨ b.toNat + m ≤ a.toNat := h

/-- Not in a range, by numbers. -/
theorem nin {b q : BitVec 64} {n : Nat} (hb : b.toNat + n ≤ 2 ^ 64)
    (h : q.toNat < b.toNat ∨ b.toNat + n ≤ q.toNat) : ¬InRange b n q := by
  rw [Sym.inRange_iff hb]; omega

/-- In a range, by numbers. -/
theorem inr {b q : BitVec 64} {n : Nat} (hb : b.toNat + n ≤ 2 ^ 64) (h : InRange b n q) :
    b.toNat ≤ q.toNat ∧ q.toNat < b.toNat + n := (Sym.inRange_iff hb).mp h

theorem toNat_off' {b : BitVec 64} {j : Nat} (h : b.toNat + j < 2 ^ 64) :
    (b + BitVec.ofNat 64 j).toNat = b.toNat + j := NativeRustcVm.toNat_add_ofNat h

theorem qA_toNat {m0 : MachineData} (h : (pA m0).toNat + 63200 ≤ 2 ^ 64) :
    (qA m0).toNat = (pA m0).toNat + 61352 :=
  toNat_off (by unfold queriesOff; omega)

theorem base_nat {m0 : MachineData} {F : Nat} (h : F ≤ m0.regs.SP.toNat) :
    (base m0 F).toNat = m0.regs.SP.toNat - F := base_toNat h

theorem loc_toNat {m0 : MachineData} {o : Nat} (h : 8192 ≤ m0.regs.SP.toNat) (ho : o ≤ 8192) :
    (loc m0 o).toNat = m0.regs.SP.toNat - 8192 + o := by
  have := m0.regs.SP.toNat_lt
  rw [toNat_off' (by rw [base_nat h]; omega), base_nat h]

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData}

/-- **The addresses as numbers.** -/
theorem geo (h : NextLevelPre a s level w rounds m0) :
    Geo m0.regs.SP.toNat (tA m0).toNat (pA m0).toNat (lA m0).toNat a.words.toNat (8 * a.len) := by
  obtain ⟨⟨hS, -, -, htok, -⟩, hts, -, -, -, -, -, -, -, -, -, -, ⟨hpo, -⟩, ⟨⟨-, hlw⟩, hls⟩, hlp,
    hlt⟩ := h
  have hN : nextLevelStack ≤ m0.regs.SP.toNat := hS.2.1
  have hsb : (stackBelow m0 nextLevelStack).toNat = m0.regs.SP.toNat - 11424 := base_nat hN
  have hfp := hts.footprint
  have h1 := apart_nat htok.1
  have h2 := apart_nat htok.2.1
  have h3 := apart_nat hpo.2.2.2.2.1
  have h4 := apart_nat hls
  have h5 := apart_nat hpo.2.2.1
  have h6 := apart_nat hpo.2.2.2.1
  have h7 := apart_nat hfp.2.2
  have h8 := apart_nat hlp
  have h9 := apart_nat hlt
  have w1 : m0.regs.X0.toBitVec.toNat + 760 ≤ 2 ^ 64 := hfp.1.2
  have w2 : m0.regs.X6.toBitVec.toNat + 63200 ≤ 2 ^ 64 := hpo.2.1
  have w3 : m0.regs.X2.toBitVec.toNat + 24 ≤ 2 ^ 64 := hlw
  have w4 : a.words.toNat + 8 * a.len ≤ 2 ^ 64 := hfp.2.1.2
  rw [hsb] at h1 h2 h3 h4
  rw [stack_eq] at hN h1 h2 h3 h4
  simp only [tstateBytes, whirBytes, levelBytes] at h1 h3 h4 h5 h6 h7 h8 h9 w1
  show Geo m0.regs.SP.toNat m0.regs.X0.toBitVec.toNat m0.regs.X6.toBitVec.toNat
    m0.regs.X2.toBitVec.toNat _ _
  exact ⟨hN, m0.regs.SP.toNat_lt, w1, w2, w3, w4, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega⟩

/-- **The context of `next_level`'s calls.** -/
theorem ctx (h : NextLevelPre a s level w rounds m0) :
    TCtx m0 8192 nextLevelStack (tA m0) a (outs m0) := by
  have g := geo h
  obtain ⟨⟨hS, hrc, -, htok, -⟩, hts, -, -, -, -, -, -, -, -, -, -, ⟨hpo, -⟩, -⟩ := h
  have hfp := hts.footprint
  have hq := qA_toNat (m0 := m0) g.pW
  have hrw : rcAddr.toNat + 192 ≤ 2 ^ 64 := hrc.2.1
  have hr1 : (tA m0).toNat + tstateBytes ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (tA m0).toNat :=
    htok.2.2
  have hr2 : (pA m0).toNat + whirBytes ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (pA m0).toNat :=
    hpo.2.2.2.2.2
  have hrs := apart_nat hrc.2.2
  have hN : nextLevelStack ≤ m0.regs.SP.toNat := hS.2.1
  have hsb : (stackBelow m0 nextLevelStack).toNat = m0.regs.SP.toNat - 11424 := base_nat hN
  have hb := base_nat (F := 8192) (m0 := m0) (by rw [stack_eq] at hN; omega)
  rw [hsb] at hrs
  simp only [tstateBytes, whirBytes] at hr1 hr2
  have hqw : (qA m0).toNat + queryBufBytes ≤ 2 ^ 64 := by
    rw [hq]; have := g.pW; simp only [queryBufBytes, queryCap]; omega
  have hqb : queryBufBytes = 1848 := rfl
  have tS := g.tS
  have pS := g.pS
  have tA' := g.tA
  have pA' := g.pA
  have hsp := g.hsp
  have hN' := g.hN
  rw [hqb] at hqw
  refine ⟨hS, hrc, htok, hfp, by rw [stack_eq]; decide, rfl, fun q hq' hr ↦ ?_, fun q hq' hd ↦ ?_,
    fun q hq' ↦ Or.inl hq', fun q hq' hf ↦ ?_⟩
  · have r1 := inr hrw hr
    rcases hq' with hq' | hq'
    · have r2 := inr g.tW hq'; omega
    · rw [hqb] at hq'; have r2 := inr hqw hq'; omega
  · have r1 := inr g.aW hd
    rcases hq' with hq' | hq'
    · have r2 := inr g.tW hq'; omega
    · rw [hqb] at hq'; have r2 := inr hqw hq'; omega
  · have r1 := inr (by rw [hb]; omega) hf
    rw [hb] at r1
    rcases hq' with hq' | hq'
    · have r2 := inr g.tW hq'; omega
    · rw [hqb] at hq'; have r2 := inr hqw hq'; omega

end


/-! ## The model -/

end

/-! The model's run from each step on: `tail8` after the squeeze for `λ`, `tail6` after the second
grind, `tail4` after the out-of-domain sample, `tail3` after the first grind. -/

@[expose] public section

/-- From `query_openings` on. -/
def tail8 (index mu : Nat) (w : WhirStateW) (rounds : Array FoldRoundW) (xs ood : Array EW)
    (v : EW) (qs : Array UInt64) (lam : EW) (s8 : TState) : Option (WhirStateW × TState) :=
  ((queryOpenings index qs).run s8).bind fun p9 ↦
    some (glueLevel w lam mu ood v qs (powers lam qs.size)
      (batchedOf index mu rounds xs qs p9.1 (powers lam qs.size)), p9.2)

/-- From `sample_queries` on. -/
def tail6 (index mu : Nat) (level : Whir.Level) (w : WhirStateW) (rounds : Array FoldRoundW)
    (xs ood : Array EW) (v : EW) (s6 : TState) : Option (WhirStateW × TState) :=
  ((sampleQueries (mu + level.logInvRate) level.queries).run s6).bind fun p7 ↦
    tail8 index mu w rounds xs ood v p7.1 (sq p7.2).1 (sq p7.2).2

/-- From `read_scalar` on. -/
def tail4 (index mu : Nat) (level : Whir.Level) (w : WhirStateW) (rounds : Array FoldRoundW)
    (xs ood : Array EW) (s4 : TState) : Option (WhirStateW × TState) :=
  (readScalar.run s4).bind fun p5 ↦ ((grind Whir.queryGrindingBits).run p5.2).bind fun p6 ↦
    tail6 index mu level w rounds xs ood p5.1 p6.2

/-- From `sample_challenges` on. -/
def tail3 (index mu : Nat) (level : Whir.Level) (w : WhirStateW) (rounds : Array FoldRoundW)
    (xs : Array EW) (s3 : TState) : Option (WhirStateW × TState) :=
  ((sampleChallenges mu).run s3).bind fun p4 ↦ tail4 index mu level w rounds xs p4.1 p4.2

end

public section

/-- **`nextLevelM` as a chain of its steps.** -/
theorem run_eq (index : Nat) (level next : Whir.Level) (mu : Nat) (w : WhirStateW)
    (rounds : Array FoldRoundW) (s : TState) :
    (nextLevelM index level next mu w rounds).run s =
      ((readCommitment (mu - next.fold + next.logInvRate) (2 * 2 ^ next.fold)).run s).bind
        fun p1 ↦ ((readScalars level.fold).run p1.2).bind
        fun p2 ↦ ((grind Whir.oodGrindingBits).run p2.2).bind
        fun p3 ↦ tail3 index mu level w rounds p2.1 p3.2 := by
  rfl

end

end NativeRustcVmArm.Whir.NextLevel
