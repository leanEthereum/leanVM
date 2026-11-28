/-
  LeanVM.Prover.Complete.Link.BalanceRows

  An honest row's share of the index balance is zero: `XOR`, `MUL`, `SET`, `DEREF`, `JUMP`.
-/

module

public import LeanVM.Prover.Complete.Link.BalanceArrays
public import LeanVM.Prover.Complete.Link.ScatterHonest
import LeanVM.Semantics.Lemmas

/-!
# The honest rows balance

A row `rowOf ctx k st` of a step whose instruction executes (`executeWith`) reads, at each access,
the memory word at the cell its pointer names, at the address its frame gives; and its program
link reads its instruction's slots. So `rowBal_eq_zero`'s hypotheses hold (`TargetsOK` gives the
index side's targets at the row's cells and instruction), table by table.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.Verifier LeanVM.Prover
open LeanVM.Extraction LeanVM.Protocol.Relation

/-! ## A row's columns and pointers -/

/-- A row's columns in `E`. -/
def rowCol (row : Array K) : ℕ → E := fun c ↦ ofK (row.getD c 0)

/-- The index a row's pointer column `p` names. -/
def rowPtr (chunks : Chunks) (row : Array K) (p : ℕ) : ℕ :=
  (chunks.indices (kToNat (row.getD p 0))).headD 0

/-- An instruction's slot `s`, in `E`. -/
def slotE (ins : LeanIsaInstruction) (s : ℕ) : E := ofK ((instructionSlots ins).toList.getD s 0)

/-- **The index side's targets** at a row of table `t` whose instruction is `σ`: `Y` and the
words at the memory's cells, `X_ω` and `P_fp` at `σ` under table `t`'s weights. -/
def TargetsOK (ch : LinkChallenges) {κ : ℕ} (img : MemoryImage κ) (t σ : ℕ) (B : ℕ → E)
    (Y X words P : ℕ → E) : Prop :=
  (∀ j (hj : j < 2 ^ κ), Y j = ch.gammaMem.getD 0 0 * gpow j + ch.gammaMem.getD 1 0 * img ⟨j, hj⟩ +
      ch.gammaMem.getD 3 0) ∧
    (∀ j (hj : j < 2 ^ κ), words j = img ⟨j, hj⟩) ∧
    X σ = ch.etaBc * ch.slot.getD 1 0 * gpow σ + ch.etaBc * ch.slot.getD 2 0 +
      (slotSum (tableSlotWeights (tables.getD t default) ch.slot
          (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0) (ch.mu.getD t []) ch.etaMem ch.etaBc).1 3 13 B +
        slotSum (tableSlotWeights (tables.getD t default) ch.slot
          (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0) (ch.mu.getD t []) ch.etaMem ch.etaBc).2.1 3 13
          (fun s ↦ gpow σ * B s)) ∧
    P σ = slotSum (tableSlotWeights (tables.getD t default) ch.slot
      (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0) (ch.mu.getD t []) ch.etaMem ch.etaBc).2.2 4 12 B

/-! ## An access that reads its cell -/

/-- **An ungated access that reads its cell balances**: its address is `g^c` and its word is the
memory's word at `c`. -/
theorem acc_of_cell (ch : LinkChallenges) {κ : ℕ} (img : MemoryImage κ) (col : ℕ → E) (B : ℕ → E)
    (fp G : E) (Z Y : ℕ → E) (a : Access) (c : ℕ) (hc : c < 2 ^ κ)
    (hY : Y c = ch.gammaMem.getD 0 0 * gpow c + ch.gammaMem.getD 1 0 * img ⟨c, hc⟩ + ch.gammaMem.getD 3 0)
    (hg : a.gate = none)
    (haddr : a.address.evaluate col + frameVal B fp a = gpow c)
    (hval : a.value.evaluate col + ((a.reads.map (readWordVal Z col)).sum +
      (a.reads.map (readProgVal B fp G)).sum) = img ⟨c, hc⟩) :
    gateOf col a * Y c = gateOf col a * committedOf ch col a + ch.gammaMem.getD 0 0 * frameVal B fp a +
      ch.gammaMem.getD 1 0 * ((a.reads.map (readWordVal Z col)).sum +
        (a.reads.map (readProgVal B fp G)).sum) := by
  have h1 : gateOf col a = 1 := by simp [gateOf, hg]
  rw [h1, hY, ← haddr, ← hval, committedOf]
  ring

/-- The pointer of a cell names the cell's index. -/
theorem rowPtr_cell {κ : ℕ} (hκ : κ < 64) (img : MemoryImage κ) {chunks : Chunks} (hc : ChunksOK chunks)
    (hκw : κ ≤ chunks.width) {row : Array K} {p : ℕ} {a : K} {i : Fin (2 ^ κ)}
    (hrow : row.getD p 0 = (⟨powIndex κ, img, chunks⟩ : FillCtx κ).cell a)
    (ha : addressIndex? κ a = some i) : rowPtr chunks row p = i := by
  rw [rowPtr, hrow, FillCtx.cell, gLogIn_powIndex hκ, ha]
  exact headD_indices_encode hc (lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hκw))

theorem ofK_gpow (n : ℕ) : ofK (addressOfIndex n) = gpow n := (gpow_eq_ofK n).symm

theorem gpow_zero' : gpow 0 = 1 := pow_zero gen

/-- A framed address `g^e·fp·o` at a cell `fp·o = g^i`. -/
theorem frame_gpow {fp o : K} {i : ℕ} (h : fp * o = addressOfIndex i) (e : ℕ) :
    ofK fp * (gpow e * ofK o) = gpow e * gpow i := by
  rw [← ofK_gpow i, ← h, ofK_mul]
  ring

/-- **A row's share from its links' facts** (`rowBal_eq_zero` at the row). -/
theorem share_of (ch : LinkChallenges) {κ : ℕ} (img : MemoryImage κ) (chunks : Chunks) (t : ℕ)
    (row : Array K) (ω : E) (σ : ℕ) (B : ℕ → E) (Y X words P : ℕ → E)
    (hσ : rowPtr chunks row (tables.getD t default).links.bytecodeLink.pointer = σ)
    (hT : TargetsOK ch img t σ B Y X words P)
    (hpc : rowCol row (tables.getD t default).links.bytecodeLink.pc = gpow σ)
    (hop : B 3 = gpow (tables.getD t default).links.bytecodeLink.opcode)
    (hopnd : ∀ op ∈ (tables.getD t default).links.bytecodeLink.operands,
      (op.1.map B).sum = op.2.evaluate (rowCol row))
    (hops : operandsOK (tables.getD t default).links.bytecodeLink.operands = true)
    (hslots : (tables.getD t default).links.memory.all accessSlotsOK = true)
    (hacc : ∀ a ∈ (tables.getD t default).links.memory,
      gateOf (rowCol row) a * Y (rowPtr chunks row a.pointer + a.shift) =
        gateOf (rowCol row) a * committedOf ch (rowCol row) a +
          ch.gammaMem.getD 0 0 * frameVal B (rowCol row (tables.getD t default).links.stateLink.fp) a +
          ch.gammaMem.getD 1 0 * ((a.reads.map (readWordVal (fun p ↦ words (rowPtr chunks row p))
            (rowCol row))).sum + (a.reads.map (readProgVal B
              (rowCol row (tables.getD t default).links.stateLink.fp) (gpow σ))).sum)) :
    rowBal ch (tables.getD t default) (ch.mu.getD t []) (rowCol row) ω
      (fun a ↦ rowPtr chunks row a.pointer + a.shift) (rowPtr chunks row)
      (rowPtr chunks row (tables.getD t default).links.bytecodeLink.pointer) Y X words P = 0 := by
  rw [hσ]
  exact rowBal_eq_zero ch _ _ _ ω _ _ σ Y X words P B (gpow σ) hT.2.2.1 hT.2.2.2 hpc hop hopnd hops
    hslots hacc

/-! ## `XOR` -/

theorem share_xor (ch : LinkChallenges) {κ : ℕ} (hκ : κ < 64) (img : MemoryImage κ) {chunks : Chunks}
    (hc : ChunksOK chunks) (hκw : κ ≤ chunks.width) (ω : E) (k σ : ℕ) (hσ : σ < 2 ^ chunks.width)
    (r r' : Registers K) (oA oB oC : K) (hpc : r.pc = addressOfIndex σ)
    (hex : executeWith img.read r (.xor oA oB oC) = some r') (Y X words P : ℕ → E)
    (hT : TargetsOK ch img 0 σ (slotE (.xor oA oB oC)) Y X words P) :
    rowBal ch (tables.getD 0 default) (ch.mu.getD 0 [])
      (rowCol (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .xor oA oB oC⟩)) ω
      (fun a ↦ rowPtr chunks (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .xor oA oB oC⟩) a.pointer +
        a.shift)
      (rowPtr chunks (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .xor oA oB oC⟩))
      (rowPtr chunks (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .xor oA oB oC⟩)
        (tables.getD 0 default).links.bytecodeLink.pointer) Y X words P = 0 := by
  generalize hrow : rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .xor oA oB oC⟩ = row
  -- the reads
  rcases hA : img.read (r.fp * oA) with _ | vA
  · simp [executeWith, hA] at hex
  rcases hB : img.read (r.fp * oB) with _ | vB
  · simp [executeWith, hA, hB] at hex
  rcases hC : img.read (r.fp * oC) with _ | vC
  · simp [executeWith, hA, hB, hC] at hex
  have hsum : vC = vA + vB := by
    by_contra hne
    simp [executeWith, hA, hB, hC, hne] at hex
  obtain ⟨iA, hiA, hvA, hxA⟩ := read_cell hκ img hA
  obtain ⟨iB, hiB, hvB, hxB⟩ := read_cell hκ img hB
  obtain ⟨iC, hiC, hvC, hxC⟩ := read_cell hκ img hC
  have p2 : rowPtr chunks row 2 = iA := rowPtr_cell hκ img hc hκw (by rw [← hrow]; rfl) hxA
  have p3 : rowPtr chunks row 3 = iB := rowPtr_cell hκ img hc hκw (by rw [← hrow]; rfl) hxB
  have p4 : rowPtr chunks row 4 = iC := rowPtr_cell hκ img hc hκw (by rw [← hrow]; rfl) hxC
  have c1 : rowCol row 1 = ofK r.fp := by rw [← hrow]; rfl
  have hmem := (LeanVM.Protocol.Relation.xor_links).2
  refine share_of ch img chunks 0 row ω σ _ Y X words P ?_ hT ?_ ?_ (fun op hop ↦ by
    rw [show (tables.getD 0 default).links.bytecodeLink.operands = [] from rfl] at hop; cases hop)
    (by decide +kernel) (by decide +kernel) ?_
  · rw [← hrow]
    exact headD_indices_encode hc hσ
  · rw [← hrow]; exact ofK_gpow σ ▸ congrArg ofK hpc
  · rfl
  · intro a ha
    rw [hmem] at ha
    have hfp : (tables.getD 0 default).links.stateLink.fp = 1 := rfl
    rw [hfp, c1]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · dsimp only
      rw [add_zero, p2]
      refine acc_of_cell ch img _ _ _ _ _ _ _ iA iA.isLt (hT.1 _ _) rfl ?_ ?_
      · simp only [frameVal, Form.evaluate_empty, zero_add, slotE]
        rw [show (instructionSlots (.xor oA oB oC)).toList.getD 4 0 = oA from rfl, frame_gpow hiA,
          gpow_zero', one_mul]
      · simp only [readWordVal, readProgVal, Form.evaluate_empty, Form.evaluate_const, zero_add,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, mul_one, p2]
        exact hT.2.1 _ _
    · dsimp only
      rw [add_zero, p3]
      refine acc_of_cell ch img _ _ _ _ _ _ _ iB iB.isLt (hT.1 _ _) rfl ?_ ?_
      · simp only [frameVal, Form.evaluate_empty, zero_add, slotE]
        rw [show (instructionSlots (.xor oA oB oC)).toList.getD 5 0 = oB from rfl, frame_gpow hiB,
          gpow_zero', one_mul]
      · simp only [readWordVal, readProgVal, Form.evaluate_empty, Form.evaluate_const, zero_add,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, mul_one, p3]
        exact hT.2.1 _ _
    · dsimp only
      rw [add_zero, p4]
      refine acc_of_cell ch img _ _ _ _ _ _ _ iC iC.isLt (hT.1 _ _) rfl ?_ ?_
      · simp only [frameVal, Form.evaluate_empty, zero_add, slotE]
        rw [show (instructionSlots (.xor oA oB oC)).toList.getD 6 0 = oC from rfl, frame_gpow hiC,
          gpow_zero', one_mul]
      · simp only [readWordVal, readProgVal, Form.evaluate_empty, Form.evaluate_const, zero_add,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, mul_one, p2, p3]
        rw [hT.2.1 _ iA.isLt, hT.2.1 _ iB.isLt, hvA, hvB, hvC, hsum]

/-! ## Words read whole -/

theorem limbs_read {κ : ℕ} (hκ : κ < 64) (img : MemoryImage κ) (chunks : Chunks) {a : K}
    {i : Fin (2 ^ κ)} (ha : addressIndex? κ a = some i) :
    (⟨powIndex κ, img, chunks⟩ : FillCtx κ).limbs a = #v[(img i).limb 0, (img i).limb 1] := by
  simp [FillCtx.limbs, limbsIn, readIn, gLogIn_powIndex hκ, ha]

theorem ofK_limb_zero {v : E} (h : IsInK v) : ofK (v.limb 0) = v := by
  rw [ofK_eq_ofLimbs]; exact ofLimbs_of_isInK h

theorem word_limbs (v : E) : ofK (v.limb 0) + eY * ofK (v.limb 1) = v := by
  rw [word_of_limbs, ofLimbs_limb]

theorem col_eval (i : ℕ) (col : ℕ → E) : (Form.col i 0).evaluate col = col i := by
  rw [Form.col_evaluate, gpow_zero', one_mul]

theorem mulA_eval (col : ℕ → E) : mulA.evaluate col = col 2 + eY * col 3 := by
  rw [mulA, Form.add, Form.evaluate_addScaled, col_eval]
  simp [Form.evaluate, sumE]

/-! ## `MUL` -/

theorem share_mul (ch : LinkChallenges) {κ : ℕ} (hκ : κ < 64) (img : MemoryImage κ) {chunks : Chunks}
    (hc : ChunksOK chunks) (hκw : κ ≤ chunks.width) (ω : E) (k σ : ℕ) (hσ : σ < 2 ^ chunks.width)
    (r r' : Registers K) (oA oB oC : K) (hpc : r.pc = addressOfIndex σ)
    (hex : executeWith img.read r (.mulNative oA oB oC) = some r') (Y X words P : ℕ → E)
    (hT : TargetsOK ch img 1 σ (slotE (.mulNative oA oB oC)) Y X words P) :
    rowBal ch (tables.getD 1 default) (ch.mu.getD 1 [])
      (rowCol (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .mulNative oA oB oC⟩)) ω
      (fun a ↦ rowPtr chunks (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .mulNative oA oB oC⟩)
        a.pointer + a.shift)
      (rowPtr chunks (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .mulNative oA oB oC⟩))
      (rowPtr chunks (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .mulNative oA oB oC⟩)
        (tables.getD 1 default).links.bytecodeLink.pointer) Y X words P = 0 := by
  rcases hA : img.read (r.fp * oA) with _ | vA
  · simp [executeWith, hA] at hex
  rcases hB : img.read (r.fp * oB) with _ | vB
  · simp [executeWith, hA, hB] at hex
  rcases hC : img.read (r.fp * oC) with _ | vC
  · simp [executeWith, hA, hB, hC] at hex
  have hprod : vC = vA * vB := by
    by_contra hne
    simp [executeWith, hA, hB, hC, hne] at hex
  obtain ⟨iA, hiA, hvA, hxA⟩ := read_cell hκ img hA
  obtain ⟨iB, hiB, hvB, hxB⟩ := read_cell hκ img hB
  obtain ⟨iC, hiC, hvC, hxC⟩ := read_cell hκ img hC
  have hl := limbs_read hκ img chunks hxA
  generalize hrow : rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .mulNative oA oB oC⟩ = row
  have p4 : rowPtr chunks row 4 = iA := rowPtr_cell hκ img hc hκw (by rw [← hrow]; rfl) hxA
  have p5 : rowPtr chunks row 5 = iB := rowPtr_cell hκ img hc hκw (by rw [← hrow]; rfl) hxB
  have p6 : rowPtr chunks row 6 = iC := rowPtr_cell hκ img hc hκw (by rw [← hrow]; rfl) hxC
  have c1 : rowCol row 1 = ofK r.fp := by rw [← hrow]; rfl
  have ha : mulA.evaluate (rowCol row) = vA := by
    rw [mulA_eval, ← hvA, ← word_limbs (img iA)]
    rw [← hrow]
    simp only [rowCol, rowOf, hl]
    rfl
  have hmem := (LeanVM.Protocol.Relation.mul_links).2
  refine share_of ch img chunks 1 row ω σ _ Y X words P ?_ hT ?_
    (show ofK (addressOfIndex 1) = gpow 1 from ofK_gpow 1) (fun op hop ↦ by
    rw [show (tables.getD 1 default).links.bytecodeLink.operands = [] from rfl] at hop; cases hop)
    (by decide +kernel) (by decide +kernel) ?_
  · rw [← hrow]
    exact headD_indices_encode hc hσ
  · rw [← hrow]; exact ofK_gpow σ ▸ congrArg ofK hpc
  · intro a ha'
    rw [hmem] at ha'
    have hfp : (tables.getD 1 default).links.stateLink.fp = 1 := rfl
    rw [hfp, c1]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
    rcases ha' with rfl | rfl | rfl
    · dsimp only
      rw [add_zero, p4]
      refine acc_of_cell ch img _ _ _ _ _ _ _ iA iA.isLt (hT.1 _ _) rfl ?_ ?_
      · simp only [frameVal, Form.evaluate_empty, zero_add, slotE]
        rw [show (instructionSlots (.mulNative oA oB oC)).toList.getD 4 0 = oA from rfl, frame_gpow hiA,
          gpow_zero', one_mul]
      · simp only [List.map_nil, List.sum_nil, add_zero, ha, hvA]
    · dsimp only
      rw [add_zero, p5]
      refine acc_of_cell ch img _ _ _ _ _ _ _ iB iB.isLt (hT.1 _ _) rfl ?_ ?_
      · simp only [frameVal, Form.evaluate_empty, zero_add, slotE]
        rw [show (instructionSlots (.mulNative oA oB oC)).toList.getD 5 0 = oB from rfl, frame_gpow hiB,
          gpow_zero', one_mul]
      · simp only [readWordVal, readProgVal, Form.evaluate_empty, Form.evaluate_const, zero_add,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, mul_one, p5]
        exact hT.2.1 _ _
    · dsimp only
      rw [add_zero, p6]
      refine acc_of_cell ch img _ _ _ _ _ _ _ iC iC.isLt (hT.1 _ _) rfl ?_ ?_
      · simp only [frameVal, Form.evaluate_empty, zero_add, slotE]
        rw [show (instructionSlots (.mulNative oA oB oC)).toList.getD 6 0 = oC from rfl, frame_gpow hiC,
          gpow_zero', one_mul]
      · simp only [readWordVal, readProgVal, Form.evaluate_empty, zero_add,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, p5, ha]
        rw [hT.2.1 _ iB.isLt, hvB, hvC, hprod, mul_comm]

/-! ## `SET` -/

theorem share_set (ch : LinkChallenges) {κ : ℕ} (hκ : κ < 64) (img : MemoryImage κ) {chunks : Chunks}
    (hc : ChunksOK chunks) (hκw : κ ≤ chunks.width) (ω : E) (k σ : ℕ) (hσ : σ < 2 ^ chunks.width)
    (r r' : Registers K) (o : K) (kk : E) (hpc : r.pc = addressOfIndex σ)
    (hex : executeWith img.read r (.setConstant o kk) = some r') (Y X words P : ℕ → E)
    (hT : TargetsOK ch img 2 σ (slotE (.setConstant o kk)) Y X words P) :
    rowBal ch (tables.getD 2 default) (ch.mu.getD 2 [])
      (rowCol (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .setConstant o kk⟩)) ω
      (fun a ↦ rowPtr chunks (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .setConstant o kk⟩)
        a.pointer + a.shift)
      (rowPtr chunks (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .setConstant o kk⟩))
      (rowPtr chunks (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .setConstant o kk⟩)
        (tables.getD 2 default).links.bytecodeLink.pointer) Y X words P = 0 := by
  rcases hA : img.read (r.fp * o) with _ | v
  · simp [executeWith, hA] at hex
  have hv : v = kk := by
    by_contra hne
    simp [executeWith, hA, hne] at hex
  obtain ⟨i, hi, hvi, hx⟩ := read_cell hκ img hA
  generalize hrow : rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .setConstant o kk⟩ = row
  have p2 : rowPtr chunks row 2 = i := rowPtr_cell hκ img hc hκw (by rw [← hrow]; rfl) hx
  have c1 : rowCol row 1 = ofK r.fp := by rw [← hrow]; rfl
  have hmem := (LeanVM.Protocol.Relation.set_links).2
  refine share_of ch img chunks 2 row ω σ _ Y X words P ?_ hT ?_
    (show ofK (addressOfIndex 2) = gpow 2 from ofK_gpow 2) (fun op hop ↦ by
    rw [show (tables.getD 2 default).links.bytecodeLink.operands = [] from rfl] at hop; cases hop)
    (by decide +kernel) (by decide +kernel) ?_
  · rw [← hrow]
    exact headD_indices_encode hc hσ
  · rw [← hrow]; exact ofK_gpow σ ▸ congrArg ofK hpc
  · intro a ha'
    rw [hmem] at ha'
    have hfp : (tables.getD 2 default).links.stateLink.fp = 1 := rfl
    rw [hfp, c1]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
    subst ha'
    dsimp only
    rw [add_zero, p2]
    refine acc_of_cell ch img _ _ _ _ _ _ _ i i.isLt (hT.1 _ _) rfl ?_ ?_
    · simp only [frameVal, Form.evaluate_empty, zero_add, slotE]
      rw [show (instructionSlots (.setConstant o kk)).toList.getD 4 0 = o from rfl, frame_gpow hi,
        gpow_zero', one_mul]
    · simp only [readWordVal, readProgVal, Form.evaluate_empty, zero_add,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, slotE, one_mul]
      rw [show (instructionSlots (.setConstant o kk)).toList.getD 5 0 = kk.limb 0 from rfl,
        show (instructionSlots (.setConstant o kk)).toList.getD 6 0 = kk.limb 1 from rfl,
        word_limbs, ← hv, ← hvi]

/-! ## `JUMP` -/

theorem share_jump (ch : LinkChallenges) {κ : ℕ} (hκ : κ < 64) (img : MemoryImage κ) {chunks : Chunks}
    (hc : ChunksOK chunks) (hκw : κ ≤ chunks.width) (ω : E) (k σ : ℕ) (hσ : σ < 2 ^ chunks.width)
    (r r' : Registers K) (oc od ofr : K) (hpc : r.pc = addressOfIndex σ)
    (hex : executeWith img.read r (.jump oc od ofr) = some r') (Y X words P : ℕ → E)
    (hT : TargetsOK ch img 4 σ (slotE (.jump oc od ofr)) Y X words P) :
    rowBal ch (tables.getD 4 default) (ch.mu.getD 4 [])
      (rowCol (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .jump oc od ofr⟩)) ω
      (fun a ↦ rowPtr chunks (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .jump oc od ofr⟩)
        a.pointer + a.shift)
      (rowPtr chunks (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .jump oc od ofr⟩))
      (rowPtr chunks (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .jump oc od ofr⟩)
        (tables.getD 4 default).links.bytecodeLink.pointer) Y X words P = 0 := by
  rcases hA : img.read (r.fp * oc) with _ | vc
  · simp [executeWith, hA] at hex
  rcases hB : img.read (r.fp * od) with _ | vd
  · simp [executeWith, hA, hB] at hex
  rcases hC : img.read (r.fp * ofr) with _ | vf
  · simp [executeWith, hA, hB, hC] at hex
  have hin : IsInK vc ∧ IsInK vd ∧ IsInK vf := by
    by_contra hne
    simp [executeWith, hA, hB, hC, hne] at hex
  obtain ⟨iA, hiA, hvA, hxA⟩ := read_cell hκ img hA
  obtain ⟨iB, hiB, hvB, hxB⟩ := read_cell hκ img hB
  obtain ⟨iC, hiC, hvC, hxC⟩ := read_cell hκ img hC
  have lA := limbs_read hκ img chunks hxA
  have lB := limbs_read hκ img chunks hxB
  have lC := limbs_read hκ img chunks hxC
  generalize hrow : rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .jump oc od ofr⟩ = row
  have p9 : rowPtr chunks row 9 = iA := rowPtr_cell hκ img hc hκw (by rw [← hrow]; rfl) hxA
  have p10 : rowPtr chunks row 10 = iB := rowPtr_cell hκ img hc hκw (by rw [← hrow]; rfl) hxB
  have p11 : rowPtr chunks row 11 = iC := rowPtr_cell hκ img hc hκw (by rw [← hrow]; rfl) hxC
  have c1 : rowCol row 1 = ofK r.fp := by rw [← hrow]; rfl
  have c2 : rowCol row 2 = vc := by
    rw [← hrow, ← ofK_limb_zero hin.1, ← hvA]
    show ofK ((FillCtx.limbs ⟨powIndex κ, img, chunks⟩ (r.fp * oc))[0]) = _
    rw [lA]; rfl
  have c3 : rowCol row 3 = vd := by
    rw [← hrow, ← ofK_limb_zero hin.2.1, ← hvB]
    show ofK ((FillCtx.limbs ⟨powIndex κ, img, chunks⟩ (r.fp * od))[0]) = _
    rw [lB]; rfl
  have c4 : rowCol row 4 = vf := by
    rw [← hrow, ← ofK_limb_zero hin.2.2, ← hvC]
    show ofK ((FillCtx.limbs ⟨powIndex κ, img, chunks⟩ (r.fp * ofr))[0]) = _
    rw [lC]; rfl
  have hmem := (LeanVM.Protocol.Relation.jump_links).2.1
  refine share_of ch img chunks 4 row ω σ _ Y X words P ?_ hT ?_
    (show ofK (addressOfIndex 4) = gpow 4 from ofK_gpow 4) (fun op hop ↦ by
    rw [show (tables.getD 4 default).links.bytecodeLink.operands = [] from rfl] at hop; cases hop)
    (by decide +kernel) (by decide +kernel) ?_
  · rw [← hrow]
    exact headD_indices_encode hc hσ
  · rw [← hrow]; exact ofK_gpow σ ▸ congrArg ofK hpc
  · intro a ha'
    rw [hmem] at ha'
    have hfp : (tables.getD 4 default).links.stateLink.fp = 1 := rfl
    rw [hfp, c1]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
    rcases ha' with rfl | rfl | rfl
    · dsimp only
      rw [add_zero, p9]
      refine acc_of_cell ch img _ _ _ _ _ _ _ iA iA.isLt (hT.1 _ _) rfl ?_ ?_
      · simp only [frameVal, Form.evaluate_empty, zero_add, slotE]
        rw [show (instructionSlots (.jump oc od ofr)).toList.getD 4 0 = oc from rfl, frame_gpow hiA,
          gpow_zero', one_mul]
      · simp only [List.map_nil, List.sum_nil, add_zero, col_eval, c2, hvA]
    · dsimp only
      rw [add_zero, p10]
      refine acc_of_cell ch img _ _ _ _ _ _ _ iB iB.isLt (hT.1 _ _) rfl ?_ ?_
      · simp only [frameVal, Form.evaluate_empty, zero_add, slotE]
        rw [show (instructionSlots (.jump oc od ofr)).toList.getD 5 0 = od from rfl, frame_gpow hiB,
          gpow_zero', one_mul]
      · simp only [List.map_nil, List.sum_nil, add_zero, col_eval, c3, hvB]
    · dsimp only
      rw [add_zero, p11]
      refine acc_of_cell ch img _ _ _ _ _ _ _ iC iC.isLt (hT.1 _ _) rfl ?_ ?_
      · simp only [frameVal, Form.evaluate_empty, zero_add, slotE]
        rw [show (instructionSlots (.jump oc od ofr)).toList.getD 6 0 = ofr from rfl, frame_gpow hiC,
          gpow_zero', one_mul]
      · simp only [List.map_nil, List.sum_nil, add_zero, col_eval, c4, hvC]

/-! ## `DEREF` -/

/-- `DEREF`'s committed `s = f_pc + f_fp`. -/
def derefS : DerefMode → K
  | .cell => 0
  | _ => 1

theorem share_deref (ch : LinkChallenges) {κ : ℕ} (hκ : κ < 64) (img : MemoryImage κ) {chunks : Chunks}
    (hc : ChunksOK chunks) (hκw : κ ≤ chunks.width) (ω : E) (k σ : ℕ) (hσ : σ < 2 ^ chunks.width)
    (r r' : Registers K) (o1 o2 o3 : K) (mode : DerefMode) (hpc : r.pc = addressOfIndex σ)
    (hex : executeWith img.read r (.deref o1 o2 o3 mode) = some r') (Y X words P : ℕ → E)
    (hT : TargetsOK ch img 3 σ (slotE (.deref o1 o2 o3 mode)) Y X words P) :
    rowBal ch (tables.getD 3 default) (ch.mu.getD 3 [])
      (rowCol (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .deref o1 o2 o3 mode⟩)) ω
      (fun a ↦ rowPtr chunks (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .deref o1 o2 o3 mode⟩)
        a.pointer + a.shift)
      (rowPtr chunks (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .deref o1 o2 o3 mode⟩))
      (rowPtr chunks (rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .deref o1 o2 o3 mode⟩)
        (tables.getD 3 default).links.bytecodeLink.pointer) Y X words P = 0 := by
  rcases hA : img.read (r.fp * o1) with _ | vp
  · simp [executeWith, hA] at hex
  have hin : IsInK vp := by
    by_contra hne
    simp [executeWith, hA, hne] at hex
  rcases hB : img.read (r.fp * o3) with _ | v3
  · simp [executeWith, hA, hB] at hex
  rcases hC : img.read (vp.limb 0 * o2) with _ | v2
  · simp [executeWith, hA, hin, hB, hC] at hex
  have hsrc : v2 = derefSource mode r v3 := by
    by_contra hne
    simp [executeWith, hA, hin, hB, hC, hne] at hex
  obtain ⟨iA, hiA, hvA, hxA⟩ := read_cell hκ img hA
  obtain ⟨iB, hiB, hvB, hxB⟩ := read_cell hκ img hB
  obtain ⟨iC, hiC, hvC, hxC⟩ := read_cell hκ img hC
  have lA := limbs_read hκ img chunks hxA
  generalize hrow : rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, σ, .deref o1 o2 o3 mode⟩ = row
  have hptr : row.getD 2 0 = vp.limb 0 := by
    rw [← hrow, ← hvA]
    show (FillCtx.limbs ⟨powIndex κ, img, chunks⟩ (r.fp * o1))[0] = _
    rw [lA]; rfl
  have p5 : rowPtr chunks row 5 = iA := rowPtr_cell hκ img hc hκw (by rw [← hrow]; rfl) hxA
  have p6 : rowPtr chunks row 6 = iC := rowPtr_cell hκ img hc hκw (by
    rw [← hrow, ← hptr, ← hrow]; rfl) hxC
  have p7 : rowPtr chunks row 7 = iB := rowPtr_cell hκ img hc hκw (by rw [← hrow]; rfl) hxB
  have c1 : rowCol row 1 = ofK r.fp := by rw [← hrow]; rfl
  have c2 : rowCol row 2 = vp := by rw [rowCol, hptr, ofK_limb_zero hin]
  have c3 : rowCol row 3 = ofK o2 := by rw [← hrow]; rfl
  have c4 : rowCol row 4 = ofK (derefS mode) := by rw [← hrow]; cases mode <;> rfl
  have hmem := (LeanVM.Protocol.Relation.deref_links).2.1
  have hops := (LeanVM.Protocol.Relation.deref_links).2.2
  have hB7 : slotE (.deref o1 o2 o3 mode) 7 = ofK (derefFlags mode).1 := rfl
  have hB8 : slotE (.deref o1 o2 o3 mode) 8 = ofK (derefFlags mode).2 := rfl
  have hfl : ofK (derefFlags mode).1 + ofK (derefFlags mode).2 = ofK (derefS mode) := by
    cases mode <;> simp [derefFlags, derefS]
  refine share_of ch img chunks 3 row ω σ _ Y X words P ?_ hT ?_
    (show ofK (addressOfIndex 3) = gpow 3 from ofK_gpow 3) ?_ (by decide +kernel) (by decide +kernel) ?_
  · rw [← hrow]
    exact headD_indices_encode hc hσ
  · rw [← hrow]; exact ofK_gpow σ ▸ congrArg ofK hpc
  · intro op hop
    rw [hops] at hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl
    · show [slotE (.deref o1 o2 o3 mode) 5].sum = (Form.col 3 0).evaluate (rowCol row)
      rw [List.sum_singleton, col_eval, c3]
      rfl
    · show [slotE (.deref o1 o2 o3 mode) 7, slotE (.deref o1 o2 o3 mode) 8].sum =
        (Form.col 4 0).evaluate (rowCol row)
      rw [List.sum_cons, List.sum_singleton, col_eval, c4, hB7, hB8, hfl]
  · intro a ha'
    rw [hmem] at ha'
    have hfp : (tables.getD 3 default).links.stateLink.fp = 1 := rfl
    rw [hfp, c1]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
    rcases ha' with rfl | rfl | rfl
    · dsimp only
      rw [add_zero, p5]
      refine acc_of_cell ch img _ _ _ _ _ _ _ iA iA.isLt (hT.1 _ _) rfl ?_ ?_
      · simp only [frameVal, Form.evaluate_empty, zero_add, slotE]
        rw [show (instructionSlots (.deref o1 o2 o3 mode)).toList.getD 4 0 = o1 from rfl,
          frame_gpow hiA, gpow_zero', one_mul]
      · simp only [List.map_nil, List.sum_nil, add_zero, col_eval, c2, hvA]
    · dsimp only
      rw [add_zero, p6]
      refine acc_of_cell ch img _ _ _ _ _ _ _ iC iC.isLt (hT.1 _ _) rfl ?_ ?_
      · simp only [frameVal, add_zero]
        rw [LeanVM.Protocol.Relation.prod_evaluate 2 3 _ (by norm_num), gpow_zero', one_mul, c2, c3,
          ← ofK_limb_zero hin, ← ofK_mul, hiC, ofK_gpow]
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        simp only [readWordVal, readProgVal]
        rw [Form.evaluate_empty, LeanVM.Protocol.Relation.one_add_col_evaluate, gpow_zero', one_mul, c4,
          hB7, hB8, p7, hT.2.1 _ iB.isLt, hvB, hvC, hsrc]
        have h2 : (2 : E) = 0 := LeanVM.Protocol.Tables.two_eq_zero_E
        cases mode
        · simp [derefFlags, derefSource, derefS]
        · simp only [derefFlags, derefSource, derefS, ofK_zero, ofK_one, mul_zero, add_zero, mul_one, hpc]
          rw [ofK_mul, ← gpow_eq_ofK, ofK_gpow]
          linear_combination v3 * h2
        · simp only [derefFlags, derefSource, derefS, ofK_zero, ofK_one, mul_zero, add_zero, mul_one,
            zero_add]
          linear_combination v3 * h2
    · dsimp only
      rw [add_zero, p7]
      refine acc_of_cell ch img _ _ _ _ _ _ _ iB iB.isLt (hT.1 _ _) rfl ?_ ?_
      · simp only [frameVal, Form.evaluate_empty, zero_add, slotE]
        rw [show (instructionSlots (.deref o1 o2 o3 mode)).toList.getD 6 0 = o3 from rfl,
          frame_gpow hiB, gpow_zero', one_mul]
      · simp only [readWordVal, readProgVal, Form.evaluate_empty, Form.evaluate_const, zero_add,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, mul_one, p7]
        exact hT.2.1 _ _

end LeanVM.Prover.Complete

end
