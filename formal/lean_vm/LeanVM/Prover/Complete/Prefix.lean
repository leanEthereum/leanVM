/-
  LeanVM.Prover.Complete.Prefix

  The first phases of the honest script win: the announced sizes and the stack's out-of-domain
  sample; and what the honest witness is.
-/

module

public import LeanVM.Prover.Complete.Truth
public import LeanVM.Prover.Complete.Wins
public import Statement.Prover.Prove
import LeanVM.Parameters.Field

/-!
# The first phases

* Moves: `Wins` of the program's helpers against the script's (`wins_readScalars`,
  `wins_sampleChallenges`, `wins_require`, `wins_liftOption`), and the scripts' monad laws.
* `witness?_spec`: what `witness?` returns, field by field.
* `wins_sizes`: the honest script announces the sizes the witness was built at, and the verifier
  reads back its layout and the rate.
* `wins_ood`: the stack's out-of-domain sample; the value sent is the stack's extension at the
  point.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Extraction LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash

variable {α β γ : Type} {B : ℕ}

/-! ## The scripts' monad laws -/

namespace Script

theorem bind_assoc (p : Script α) (f : α → Script β) (g : β → Script γ) :
    (p.bind f).bind g = p.bind fun a ↦ (f a).bind g := by
  induction p with
  | ret a => rfl
  | send x k ih => simp only [bind, ih]
  | sample k ih => simp only [bind, ih]
  | sendPacked xs k ih => simp only [bind, ih]
  | samplePacked n k ih => simp only [bind, ih]
  | grind o k ih => simp only [bind, ih]
  | commit w k ih => simp only [bind, ih]
  | query k ih => simp only [bind, ih]

theorem bind_ret (p : Script α) : p.bind ret = p := by
  induction p with
  | ret a => rfl
  | send x k ih => simp only [bind, ih]
  | sample k ih => simp only [bind, ih]
  | sendPacked xs k ih => simp only [bind, ih]
  | samplePacked n k ih => simp only [bind, ih]
  | grind o k ih => simp only [bind, ih]
  | commit w k ih => simp only [bind, ih]
  | query k ih => simp only [bind, ih]

@[simp] theorem bind_eq (p : Script α) (f : α → Script β) : p >>= f = p.bind f := rfl

@[simp] theorem pure_eq (a : α) : (pure a : Script α) = ret a := rfl

end Script

/-! ## Moves -/

theorem readScalars_succ_bind (n : ℕ) (k : List E → VerifierProgram α) :
    (VerifierProgram.readScalars (n + 1)).bind k =
      .read fun x ↦ (VerifierProgram.readScalars n).bind fun xs ↦ k (x :: xs) := by
  simp only [VerifierProgram.readScalars, VerifierProgram.readScalar, VerifierProgram.bind_eq,
    VerifierProgram.pure_eq, VerifierProgram.bind_assoc]
  rfl

theorem sampleChallenges_succ_bind (n : ℕ) (k : List E → VerifierProgram α) :
    (VerifierProgram.sampleChallenges (n + 1)).bind k =
      .sample fun x ↦ (VerifierProgram.sampleChallenges n).bind fun xs ↦ k (x :: xs) := by
  simp only [VerifierProgram.sampleChallenges, VerifierProgram.sampleChallenge,
    VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc]
  rfl

theorem sampleN_succ_bind (n : ℕ) (t : List E → Script β) :
    (Script.sampleN (n + 1)).bind t =
      .sample fun x ↦ (Script.sampleN n).bind fun xs ↦ t (x :: xs) := by
  simp only [Script.sampleN, Script.sampleE, Script.bind_eq, Script.pure_eq, Script.bind_assoc]
  rfl

/-- **Reading scalars the script sends.** -/
theorem wins_readScalars {Q : α → β → Bool → List Committed → Prop} {cs : List Committed} :
    ∀ (xs : List E) {k : List E → VerifierProgram α} {t : Unit → Script β},
      Wins B Q (k xs) (t ()) false cs →
      Wins B Q ((VerifierProgram.readScalars xs.length).bind k) ((Script.sendList xs).bind t)
        false cs
  | [], _, _, h => h
  | x :: xs, k, t, h => by
    rw [List.length_cons, readScalars_succ_bind]
    exact Wins.read (wins_readScalars xs (k := fun ys ↦ k (x :: ys)) h)

/-- **Sampling challenges the script receives.** -/
theorem wins_sampleChallenges {Q : α → β → Bool → List Committed → Prop} {cs : List Committed} :
    ∀ (n : ℕ) {g : Bool} {k : List E → VerifierProgram α} {t : List E → Script β},
      (∀ zs : List E, zs.length = n → Wins B Q (k zs) (t zs) (if n = 0 then g else false) cs) →
      Wins B Q ((VerifierProgram.sampleChallenges n).bind k) ((Script.sampleN n).bind t) g cs
  | 0, g, k, t, h => h [] rfl
  | n + 1, g, k, t, h => by
    rw [sampleChallenges_succ_bind, sampleN_succ_bind]
    refine Wins.sample fun c ↦ wins_sampleChallenges n (k := fun zs ↦ k (c :: zs))
      (t := fun zs ↦ t (c :: zs)) fun zs hzs ↦ ?_
    have := h (c :: zs) (by simp [hzs])
    simp only [Nat.add_one_ne_zero, ↓reduceIte] at this
    split <;> exact this

/-- **A check that holds.** -/
theorem wins_require {Q : α → β → Bool → List Committed → Prop} {c : Prop} [Decidable c]
    (hc : c) {k : Unit → VerifierProgram α} {s : Script β} {g : Bool} {cs : List Committed}
    (h : Wins B Q (k ()) s g cs) : Wins B Q ((VerifierProgram.require c).bind k) s g cs := by
  simpa [VerifierProgram.require, hc] using h

/-- **An option that is some.** -/
theorem wins_liftOption {Q : β → γ → Bool → List Committed → Prop} {o : Option α} {a : α}
    (ho : o = some a) {k : α → VerifierProgram β} {s : Script γ} {g : Bool}
    {cs : List Committed} (h : Wins B Q (k a) s g cs) :
    Wins B Q ((liftOption o).bind k) s g cs := by
  subst ho
  exact h

/-! ## The witness -/

/-- **What the witness is**: the trace's boundary holds, its run gives the steps whose rows the
witness counts, the layout is `buildLayout`'s at those rows within the stack cap, the chunks are the
pointer width's, and the columns and the stack are built from the rows. -/
theorem witness?_spec {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    {W : Witness} (hW : witness? prog input t = some W) :
    boundaryOK input t = true ∧
      ∃ steps, runSteps (powIndex t.logMemorySize) (powIndex prog.logSize) prog t = some steps ∧
        W.rows = rowCounts steps ∧
        buildLayout (bytecodeWords prog) t.logMemorySize W.rows = some W.layout ∧
        W.layout.stackLog ≤ Whir.maxLogStack ∧
        Chunks.new (pointerWidth t.logMemorySize prog.logSize W.rows.sum) = some W.chunks ∧
        W.cols = colsOf t.memory (rowsOf ⟨powIndex t.logMemorySize, t.memory, W.chunks⟩ steps)
          W.layout.tableLogHeights ∧
        W.stack = stackArray W.layout W.cols := by
  unfold witness? at hW
  by_cases hb : boundaryOK input t = true
  · simp only [hb, ↓reduceIte] at hW
    refine ⟨hb, ?_⟩
    rcases hs : runSteps (powIndex t.logMemorySize) (powIndex prog.logSize) prog t with _ | steps
    · simp [hs] at hW
    · simp only [hs] at hW
      rcases hl : buildLayout (bytecodeWords prog) t.logMemorySize (rowCounts steps) with _ | layout
      · simp [hl] at hW
      · simp only [hl] at hW
        by_cases hlog : layout.stackLog ≤ Whir.maxLogStack
        · simp only [hlog, ↓reduceIte] at hW
          rcases hc : Chunks.new (pointerWidth t.logMemorySize prog.logSize (rowCounts steps).sum)
            with _ | chunks
          · simp [hc] at hW
          · simp only [hc, Option.some.injEq] at hW
            have hr := congrArg Witness.rows hW
            have hla := congrArg Witness.layout hW
            have hch := congrArg Witness.chunks hW
            have hco := congrArg Witness.cols hW
            have hst := congrArg Witness.stack hW
            dsimp only at hr hla hch hco hst
            rw [← hr, ← hla, ← hch, ← hco, ← hst]
            exact ⟨steps, rfl, rfl, hl, hlog, hc, rfl, rfl⟩
        · simp [hlog] at hW
  · simp [hb] at hW

/-! ## The announced sizes -/

theorem kToNat_ofBits (n : ℕ) : kToNat (K.ofBits n) = n % 2 ^ 64 := by
  simp [kToNat, K.ofBits, BF64.toBitVec_ofBitVec]

theorem limb_eOfNat (n : ℕ) (i : Fin 2) :
    (eOfNat n).limb i = if i = 0 then K.ofBits n else 0 := by
  simp [eOfNat]

/-- `buildLayout` keeps the memory's log-size and the row counts, and bounds them. -/
theorem buildLayout_spec {bytecode : List K} {logMemory : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode logMemory rows = some layout) :
    layout.logMemory = logMemory ∧ layout.tableRows = rows ∧ rows.length = nTables ∧
      (∀ r ∈ rows, r ≤ 2 ^ maxTableLog) ∧ logMemory ≤ maxLogMemory ∧
      Whir.minLogStack ≤ layout.stackLog := by
  unfold buildLayout at h
  split at h
  · cases h
  · split at h
    · rename_i hc
      cases h
      refine ⟨rfl, rfl, hc.2.2.2.2.2, fun r hr ↦ ?_, hc.2.1, ?_⟩
      · have := hc.2.2.1
        simp only [List.all_eq_true, decide_eq_true_eq] at this
        exact this r hr
      · exact le_max_left _ _
    · cases h

/-- **The announced sizes.** The honest script announces the witness's sizes and the rate; the
verifier reads back its layout and the rate, and nothing waits in the sponge. -/
theorem wins_sizes {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    {W : Witness} (hW : witness? prog input t = some W) {ρ : ℕ} (hρ : 1 ≤ ρ ∧ ρ ≤ 4)
    (cs : List Committed) :
    Wins B (fun a _ g cs' ↦ a = (W.layout, ρ) ∧ g = false ∧ cs' = cs)
      (readAnnouncedSizes (bytecodeWords prog)) (Script.sendList (W.announce ρ)) false cs := by
  obtain ⟨-, steps, -, -, hl, hlog, -⟩ := witness?_spec hW
  obtain ⟨hlm, -, hlen, hrows, hmem, hmin⟩ := buildLayout_spec hl
  have hann : W.announce ρ = eOfNat t.logMemorySize :: (W.rows.map eOfNat ++ [eOfNat ρ]) := by
    simp [Witness.announce, hlm]
  have hlen' : (W.announce ρ).length = 2 + nTables := by
    rw [hann]
    simp only [List.length_cons, List.length_append, List.length_map, List.length_nil, hlen]
    omega
  have hmem64 : t.logMemorySize < 18446744073709551616 := by
    have : maxLogMemory < 18446744073709551616 := by decide
    omega
  have hrow64 : ∀ r ∈ W.rows, r < 18446744073709551616 := fun r hr ↦ by
    have h1 := hrows r hr
    have : 2 ^ maxTableLog < 18446744073709551616 := by decide
    omega
  have hρ64 : ρ < 18446744073709551616 := by omega
  rw [← Script.bind_ret (Script.sendList _)]
  unfold readAnnouncedSizes
  rw [← hlen']
  simp only [VerifierProgram.bind_eq]
  refine wins_readScalars (W.announce ρ) ?_
  have hall : ((W.announce ρ).all fun value ↦ decide (value.limb 1 = 0)) = true := by
    simp [hann, limb_eOfNat]
  have hhead : kToNat (((W.announce ρ).headD 0).limb 0) = t.logMemorySize := by
    simp [hann, limb_eOfNat, kToNat_ofBits, Nat.mod_eq_of_lt hmem64]
  have hmid : (((W.announce ρ).drop 1).take nTables).map (fun value ↦ kToNat (value.limb 0)) =
      W.rows := by
    rw [hann, List.drop_one, List.tail_cons, List.take_append_of_le_length (by simp [hlen]),
      List.take_of_length_le (by simp [hlen]), List.map_map]
    conv_rhs => rw [← List.map_id W.rows]
    refine List.map_congr_left fun r hr ↦ ?_
    simp [limb_eOfNat, kToNat_ofBits, Nat.mod_eq_of_lt (hrow64 r hr)]
  have hlast : kToNat (((W.announce ρ).getLastD 0).limb 0) = ρ := by
    rw [hann, ← List.cons_append, List.getLastD_concat]
    simp [limb_eOfNat, kToNat_ofBits, Nat.mod_eq_of_lt hρ64]
  refine wins_require hall ?_
  simp only [hhead, hmid, hlast]
  refine wins_require hρ ?_
  refine wins_liftOption hl ?_
  exact wins_require ⟨hmin, hlog⟩ ⟨rfl, rfl, rfl⟩

/-! ## The out-of-domain sample -/

/-- **The stack's out-of-domain sample.** After a grind, the point, then the stack's extension
there; the verifier's claim is `eq(z, ·)` and that value. -/
theorem wins_ood {μ : ℕ} (hμ : 1 ≤ μ) (hB : Whir.oodGrindingBits ≤ B) (stack : Array K)
    (cs : List Committed) :
    Wins B (fun a b g cs' ↦ a = ((fun x ↦ eqEval b.1 x), b.2) ∧ b.2 = mleK stack b.1 ∧
        b.1.length = μ ∧ g = false ∧ cs' = cs)
      (readOod μ) (oodFast μ stack) false cs := by
  obtain ⟨m, rfl⟩ : ∃ m, μ = m + 1 := ⟨μ - 1, by omega⟩
  have hg : Whir.oodGrindingBits ≠ 0 := by decide
  simp only [readOod, oodFast, VerifierProgram.grindProofOfWork, Script.grindBits, hg,
    ↓reduceIte, VerifierProgram.bind_eq, Script.grindS]
  refine Wins.grind hB ?_
  refine wins_sampleChallenges (m + 1) fun zs hzs ↦ ?_
  simp only [Nat.add_one_ne_zero, ↓reduceIte]
  exact Wins.read ⟨rfl, rfl, hzs, rfl, rfl⟩

end LeanVM.Prover

end
