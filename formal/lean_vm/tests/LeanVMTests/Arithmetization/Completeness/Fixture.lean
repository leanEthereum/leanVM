import LeanVM.Arithmetization.Completeness.Skeletons

/-!
# Test fixture: a jump to the sentinel on a sum-free image

A program of `2^11` slots whose first instruction is `JUMP [g^2, g^2, g^3]` to the sentinel, and
every other slot a `SET_CONSTANT` (`jumpProg`), and a valid execution of it, one step on an image
whose five words are linearly independent over `GF(2)`, so that no `XOR` executes on it at any
registers or operands (`badImage_no_xor`). The image holds the public words `y` and `x·y`, the
`JUMP` operand cells `(d, d)` and `1`, and `y²` everywhere else. Its witness has an empty `XOR`
table: a table holds the run's rows, any number of them, and nothing more.

Also the generic arms of `executeWith` and run lemmas the long-run test uses.
-/

namespace LeanVMTests.Arithmetization.Completeness.Fixture

open LeanVM.Parameters LeanVM.Semantics

/-- The sentinel counter of a `2^11`-slot program, as a literal term. The elaborator unifies two
`K` terms by evaluating powers of `g`, so it is never a definition. -/
local notation "d₀" => (gpow 2047 : K)

/-! ## Arms and runs -/

/-- `XOR` executes to the fall-through when its result cell holds the sum of its operands. -/
theorem executeWith_xor_of_reads {read : K → Option E} {r : Regs K} {oA oB oC : K} {a b c : E}
    (hA : read (r.fp * oA) = some a) (hB : read (r.fp * oB) = some b)
    (hC : read (r.fp * oC) = some c) (h : c = a + b) :
    executeWith read r (.xor oA oB oC) = some r.next := by
  simp [executeWith, hA, hB, hC, h]

/-- `SET_CONSTANT` executes to the fall-through when its cell holds its immediate. -/
theorem executeWith_set_of_read {read : K → Option E} {r : Regs K} {o : K} {k : E}
    (h : read (r.fp * o) = some k) : executeWith read r (.setConstant o k) = some r.next := by
  simp [executeWith, h]

/-- A `JUMP` whose three cells hold words of `K`, the condition nonzero, goes to the destination
in the frame the third cell holds. -/
theorem executeWith_jump_taken {read : K → Option E} {r : Regs K} {oc od of : K} {c d f : K}
    (hc : read (r.fp * oc) = some (ofK c)) (hd : read (r.fp * od) = some (ofK d))
    (hf : read (r.fp * of) = some (ofK f)) (hc0 : c ≠ 0) :
    executeWith read r (.jump oc od of) = some ⟨d, f⟩ := by
  have hin : ∀ a : K, IsInK (ofK a) := fun a ↦ (isInK_iff _).mpr ⟨a, rfl⟩
  have hne : ofK c ≠ 0 := by
    intro h
    have := congrArg (fun z : E ↦ z.limb 0) h
    simp only [limb_ofK, limb_zero] at this
    exact hc0 this
  simp [executeWith, hc, hd, hf, hin, hne, limb_ofK]

/-- One step from a state away from the sentinel is a run of one step. -/
theorem run_one {κ : ℕ} {prog : Program} {L : MemImage κ} {r r' : Regs K}
    (hpc : r.pc ≠ prog.finalPc) (h : step prog L r = some r') : run prog L 1 r = some r' := by
  rw [run_succ_of_ne hpc, h]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rfl

/-- Runs compose. -/
theorem run_trans {κ : ℕ} {prog : Program} {L : MemImage κ} {m n : ℕ} {r r₁ r₂ : Regs K}
    (h1 : run prog L m r = some r₁) (h2 : run prog L n r₁ = some r₂) :
    run prog L (m + n) r = some r₂ := by
  rw [run_add, h1]
  simpa only [Option.bind_eq_bind, Option.bind_some] using h2

/-- A slot below the sentinel is not the sentinel's counter. -/
theorem gpow_ne_finalPc (prog : Program) {n : ℕ} (hn : n + 1 < 2 ^ prog.logSize) :
    gpow n ≠ prog.finalPc := by
  unfold Program.finalPc
  intro heq
  have hL : prog.logSize ≤ 32 := prog.logSize_le
  have h32 : 2 ^ prog.logSize ≤ 4294967296 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hL
    simpa using this
  have hc : (2 : ℕ) ^ 64 - 1 = 18446744073709551615 := by norm_num
  have hm1 : n ∈ Set.Iio (2 ^ 64 - 1) := by
    simp only [Set.mem_Iio, hc]; omega
  have hm2 : 2 ^ prog.logSize - 1 ∈ Set.Iio (2 ^ 64 - 1) := by
    simp only [Set.mem_Iio, hc]; omega
  have := gpow_injOn hm1 hm2 heq
  omega

/-- Reading the address of a literal index gives the cell at that index. -/
theorem read_lit {κ : ℕ} (L : MemImage κ) (j : ℕ) (hκ : κ < 64 := by decide)
    (hj : j < 2 ^ κ := by decide) : L.read (gpow j) = some (L ⟨j, hj⟩) :=
  MemImage.read_gpow hκ L ⟨j, hj⟩

/-! ## The image -/

/-- `y`, the first public word. -/
def wA : E := E.ofLimbs 0 1 0

/-- `x·y`, the second public word (`K.ofBits 2` is `x`). -/
def wB : E := E.ofLimbs 0 (K.ofBits 2) 0

/-- `y²`, the word of every other cell. -/
def vS : E := E.ofLimbs 0 0 1

/-- The five words the image holds, for the sentinel counter `d`. -/
def S (d : K) : List E := [wA, wB, ofK d, ofK 1, vS]

/-- No word of `S` is the sum of two words of `S`: the five words are linearly independent over
`GF(2)`. Checked in the kernel on the `5^3` triples. -/
theorem S_sumfree_bool :
    (S d₀).all (fun x ↦ (S d₀).all (fun y ↦ (S d₀).all (fun z ↦ decide (z ≠ x + y)))) = true := by
  decide +kernel

/-- No word of the five is the sum of two of them. -/
theorem S_sumfree : ∀ x ∈ S d₀, ∀ y ∈ S d₀, ∀ z ∈ S d₀, z ≠ x + y := by
  intro x hx y hy z hz
  have := S_sumfree_bool
  simp only [List.all_eq_true, decide_eq_true_eq] at this
  exact this x hx y hy z hz

/-- The sentinel counter of a `2^11`-slot program is not `1`. -/
theorem d₀_ne_one : d₀ ≠ 1 := by decide +kernel

/-- The sentinel counter of a `2^11`-slot program is not `0`. -/
theorem d₀_ne_zero : d₀ ≠ 0 := by decide +kernel

/-- The image: the two public words, the `JUMP` operand cells `(d, d)` and `1`, and `y²`
everywhere else. -/
def badImage (d : K) : MemImage minLogMem := fun i ↦
  match (i : ℕ) with
  | 0 => wA
  | 1 => wB
  | 2 => ofK d
  | 3 => ofK 1
  | _ => vS

/-- Every cell of the image is one of the five words. -/
theorem badImage_mem (d : K) (i : Fin (2 ^ minLogMem)) : badImage d i ∈ S d := by
  obtain ⟨i, hi⟩ := i
  unfold badImage
  match i, hi with
  | 0, _ => simp [S]
  | 1, _ => simp [S]
  | 2, _ => simp [S]
  | 3, _ => simp [S]
  | n + 4, _ => simp [S]

/-- The public input whose words are the first two cells. -/
def badInput : PublicInput := ⟨![0, 1, 0, K.ofBits 2]⟩

/-! ## No `XOR` instruction steps on this image -/

/-- On an image where no word is the sum of two words, no `XOR` executes, whatever the operands and
registers. -/
theorem no_xor_execute {κ : ℕ} (hκ : κ < 64) (L : MemImage κ)
    (hL : ∀ i j k, L k ≠ L i + L j) (r : Regs K) (oA oB oC : K) :
    execute L r (.xor oA oB oC) = none := by
  unfold execute executeWith
  rcases hA : L.read (r.fp * oA) with _ | vA
  · simp [hA]
  rcases hB : L.read (r.fp * oB) with _ | vB
  · simp [hA, hB]
  rcases hC : L.read (r.fp * oC) with _ | vC
  · simp [hA, hB, hC]
  obtain ⟨i, -, rfl⟩ := (MemImage.read_eq_some_iff hκ L).mp hA
  obtain ⟨j, -, rfl⟩ := (MemImage.read_eq_some_iff hκ L).mp hB
  obtain ⟨k, -, rfl⟩ := (MemImage.read_eq_some_iff hκ L).mp hC
  simp [hA, hB, hC, hL i j k]

/-- No `XOR` executes on the image, at any registers and operands. -/
theorem badImage_no_xor (r : Regs K) (oA oB oC : K) :
    execute (badImage d₀) r (.xor oA oB oC) = none :=
  no_xor_execute (by decide) (badImage d₀)
    (fun i j k ↦ S_sumfree _ (badImage_mem d₀ i) _ (badImage_mem d₀ j) _ (badImage_mem d₀ k))
    r oA oB oC

/-- The all-zero image. -/
def zeroImage : MemImage minLogMem := fun _ ↦ 0

/-- Control: the sum-free hypothesis is what blocks the step. On the all-zero image, where
`0 = 0 + 0`, an `XOR` of three cells executes. -/
theorem zeroImage_xor :
    execute zeroImage ⟨gpow 5, 1⟩ (.xor (gpow 0) (gpow 0) (gpow 0)) =
      some (Regs.next ⟨gpow 5, 1⟩) := by
  have h : zeroImage.read (((⟨gpow 5, 1⟩ : Regs K).fp) * gpow 0) = some 0 := by
    show zeroImage.read (1 * gpow 0) = some 0
    rw [one_mul]
    exact read_lit zeroImage 0
  exact executeWith_xor_of_reads h h h (add_zero 0).symm

/-! ## The trace is valid -/

theorem bad_run (prog : Program) (d : K) (hd : prog.finalPc = d) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (h0 : prog.fetch 1 = some (.jump (gpow 2) (gpow 2) (gpow 3))) :
    run prog (badImage d) 1 Regs.initial = some (Regs.final prog) := by
  have hne : (Regs.initial : Regs K).pc ≠ prog.finalPc := by
    rw [hd]; exact fun h ↦ hd1 h.symm
  have e2 : (badImage d).read (gpow 2) = some (ofK d) := by
    rw [read_lit (badImage d) 2]; rfl
  have e3 : (badImage d).read (gpow 3) = some (ofK 1) := by
    rw [read_lit (badImage d) 3]; rfl
  have hin : IsInK (ofK d) := (isInK_iff _).mpr ⟨d, rfl⟩
  have hin1 : IsInK (ofK (1 : K)) := (isInK_iff _).mpr ⟨1, rfl⟩
  have hne0 : ofK d ≠ 0 := by
    intro h
    have := congrArg (fun z : E ↦ z.limb 0) h
    simp only [limb_ofK, limb_zero] at this
    exact hd0 this
  rw [run_succ_of_ne hne, step_of_fetch_eq_some (r := Regs.initial) h0]
  show (execute (badImage d) ⟨1, 1⟩ (.jump (gpow 2) (gpow 2) (gpow 3))) >>= _ = _
  simp only [execute, executeWith, one_mul, e2, e3]
  have hin1' : IsInK (1 : E) := by simpa using hin1
  have hl1 : (1 : E).limb 0 = 1 := by simpa using limb_ofK (1 : K) 0
  simp [hin, hin1', hne0, limb_ofK, hl1, run_zero, Regs.final, hd]

/-- The image holds the public words at `g^0` and `g^1`. -/
theorem bad_boundary {prog : Program} (d : K) (steps : ℕ) :
    HasPublicBoundary badInput (⟨minLogMem, badImage d, steps⟩ : Trace prog) := by
  refine ⟨le_rfl, (by decide : minLogMem ≤ maxLogMem), ?_, ?_⟩
  · rw [read_lit (badImage d) 0]; rfl
  · rw [read_lit (badImage d) 1]; rfl

/-- For every `2^11`-slot program whose first instruction is `JUMP [g^2, g^2, g^3]`, one step to
the sentinel is a valid execution on `badImage d₀`. -/
theorem bad_valid (prog : Program) (hL : prog.logSize = 11)
    (h0 : prog.fetch 1 = some (.jump (gpow 2) (gpow 2) (gpow 3))) :
    ValidExecution prog badInput (⟨minLogMem, badImage d₀, 1⟩ : Trace prog) := by
  have hfin : prog.finalPc = d₀ := by
    have h : 2 ^ prog.logSize - 1 = 2047 := by rw [hL]; norm_num
    unfold Program.finalPc
    rw [h]
  exact ⟨bad_boundary d₀ 1, bad_run prog d₀ hfin d₀_ne_zero d₀_ne_one h0⟩

/-! ## The program -/

/-- `JUMP [g^2, g^2, g^3]` in slot `0`, `SET_CONSTANT [g^0] 0` in every other slot, the sentinel
included. -/
def jumpProg : Program :=
  ⟨11, by decide, fun i ↦
    if (i : ℕ) = 0 then .jump (gpow 2) (gpow 2) (gpow 3) else .setConstant (gpow 0) 0⟩

/-- The sentinel slot is not a `JUMP`. -/
theorem jumpProg_sentinelSafe : SentinelSafe jumpProg := by decide

/-- Its first slot is the `JUMP`. -/
theorem jumpProg_fetch_one : jumpProg.fetch 1 = some (.jump (gpow 2) (gpow 2) (gpow 3)) := by
  have h : jumpProg.fetch (gpow 0) = some (jumpProg.code ⟨0, by decide⟩) :=
    jumpProg.fetch_gpow ⟨0, by decide⟩
  rw [show gpow 0 = (1 : K) from pow_zero g] at h
  rw [h]
  simp [jumpProg]

/-- The trace: one step, `JUMP` to the sentinel. -/
def badTrace : Trace jumpProg := ⟨minLogMem, badImage d₀, 1⟩

/-- It is a valid execution. -/
theorem badTrace_valid : ValidExecution jumpProg badInput badTrace :=
  bad_valid jumpProg rfl jumpProg_fetch_one

end LeanVMTests.Arithmetization.Completeness.Fixture
