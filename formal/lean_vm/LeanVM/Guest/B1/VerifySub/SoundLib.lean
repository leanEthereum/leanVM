/-
  LeanVM.Guest.B1.VerifySub.SoundLib

  The facts `verify_sub`'s assembly combines: the body's split, the output lanes among the
  pooled claims, the heights, the stack's configuration, the bus depth, the claimed bytecode.
-/

module

public import LeanVM.Guest.B1.VerifySub.FrontAll
public import LeanVM.Guest.B1.VerifySub.Lanes
public import LeanVM.Guest.B1.VerifySub.Accept
public import LeanVM.Guest.B1.Whir.Interface
public import LeanVM.Protocol.WithHash

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The body -/

/-- The front: the statements up to the three calls. -/
abbrev vsFrontT : List Stmt :=
  vsHeadT ++ vsReadsT ++ vsSizesT ++ vsPushT ++ vsRootsT ++ vsAlphasT ++ vsFpwT ++
    vsCallsT

theorem vsFrontT_noRet : Stmt.noRetList vsFrontT = true := by decide +kernel

theorem vsT_split : vsT = vsFrontT ++ (vsMapsT ++ (vsCtabT ++ (vsLamT ++ vsTailT))) := by
  simp only [vsT, vsFrontT, List.append_assoc]

/-! ## The output lanes among the pooled claims -/

theorem claimColumns_length : Tables.claimColumns.length = 167 := by decide +kernel

theorem claimColumns_front : ∀ x ∈ Tables.claimColumns.take 112, x ∉ keccakOutputColumns := by
  decide +kernel

theorem claimColumns_lanes : ∀ x ∈ (Tables.claimColumns.drop 112).take 25,
    x ∈ keccakOutputColumns := by decide +kernel

theorem claimColumns_back : ∀ x ∈ Tables.claimColumns.drop 137, x ∉ keccakOutputColumns := by
  decide +kernel

theorem claimColumns_lanes_eq : (Tables.claimColumns.drop 112).take 25 = keccakOutputColumns := by
  decide +kernel

theorem claims_split (claims : List ColumnClaim) :
    claims = claims.take 112 ++ (claims.drop 112).take 25 ++ claims.drop 137 := by
  have e : (claims.drop 112).take 25 ++ claims.drop 137 = claims.drop 112 := by
    rw [show claims.drop 137 = (claims.drop 112).drop 25 by simp [List.drop_drop]]
    exact List.take_append_drop 25 _
  rw [List.append_assoc, e, List.take_append_drop]

theorem lanes_eq {claims : List ColumnClaim} (hcol : claims.map (·.column) = Tables.claimColumns) :
    lanesOf claims = (claims.drop 112).take 25 ∧
      claims.filter (fun c ↦ c.column ∉ keccakOutputColumns) =
        claims.take 112 ++ claims.drop 137 := by
  have hA : ∀ c ∈ claims.take 112, c.column ∉ keccakOutputColumns := fun c hc ↦
    claimColumns_front _ (by rw [← hcol, ← List.map_take]; exact List.mem_map_of_mem hc)
  have hB : ∀ c ∈ (claims.drop 112).take 25, c.column ∈ keccakOutputColumns := by
    intro c hc
    apply claimColumns_lanes
    rw [← hcol, ← List.map_drop, ← List.map_take]
    exact List.mem_map_of_mem hc
  have hD : ∀ c ∈ claims.drop 137, c.column ∉ keccakOutputColumns := fun c hc ↦
    claimColumns_back _ (by rw [← hcol, ← List.map_drop]; exact List.mem_map_of_mem hc)
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [claims_split claims]
    simp only [lanesOf, List.filter_append]
    rw [List.filter_eq_nil_iff.2 (fun c hc ↦ by simpa using hA c hc),
      List.filter_eq_self.2 (fun c hc ↦ by simpa using hB c hc),
      List.filter_eq_nil_iff.2 (fun c hc ↦ by simpa using hD c hc)]
    simp only [List.nil_append, List.append_nil]
  · conv_lhs => rw [claims_split claims]
    simp only [List.filter_append]
    rw [List.filter_eq_self.2 (fun c hc ↦ by simpa using hA c hc),
      List.filter_eq_nil_iff.2 (fun c hc ↦ by simpa using hB c hc),
      List.filter_eq_self.2 (fun c hc ↦ by simpa using hD c hc)]
    simp only [List.append_nil]

theorem getD_mem' {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

/-! ## The heights -/

theorem tau_ge {rowsN : List ℕ} (h : rowsN.length = 6) :
    9 ≤ (Tables.tableHeightsOf rowsN).getD 5 0 := by
  match rowsN, h with
  | [_, _, _, _, _, _], _ =>
    simp [Tables.tableHeightsOf, tableLogFloors, keccakMinStepsLog]

theorem tau_lt {rowsN : List ℕ} (h : rowsN.length = 6)
    (hh : ∀ x ∈ Tables.tableHeightsOf rowsN, x < 33) : (Tables.tableHeightsOf rowsN).getD 5 0 < 33 :=
  hh _ (getD_mem' (by rw [tableHeights_length rowsN h]; omega))

/-! ## The bus depth -/

theorem pushTotal_ge2 {logMem : ℕ} {hs : List ℕ} (hl : hs.length = 6) :
    2 ^ logMem + 2 ^ 19 ≤ pushTotal logMem hs := by
  match hs, hl with
  | [h0, h1, h2, h3, h4, h5], _ =>
    unfold pushTotal
    rw [show (List.range 54).map (fun b ↦ 2 ^ pushKappa logMem [h0, h1, h2, h3, h4, h5] b) =
      ((List.range 54).map (pushKappa logMem [h0, h1, h2, h3, h4, h5])).map (2 ^ ·) from
      (List.map_map ..).symm, pushKappas_eq]
    simp only [List.cons_append, List.map_cons, List.sum_cons]
    omega

theorem depth_ge {logMem : ℕ} {hs : List ℕ} (hl : hs.length = 6) :
    20 ≤ log2Ceil (pushTotal logMem hs) := by
  have h := pushTotal_ge2 (logMem := logMem) hl
  have : 2 ^ 19 < pushTotal logMem hs := by
    have := Nat.one_le_two_pow (n := logMem)
    omega
  exact lt_log2Ceil_iff.2 this

/-! ## The claimed bytecode -/

theorem bytecodeAt_claimed (bytecode : List K) (pt : List E) (v : E) :
    Tables.BytecodeAt (claimedBytecodeValue ⟨pt, v⟩) bytecode pt v := by
  intro s
  simp [claimedBytecodeValue, Tables.tbRun, VerifierProgram.require, Compile.runWithHash]
  rfl

/-! ## The stack's log -/

theorem sl_word_ginv20_mul : word 14347465658197868555 0 0 * gen ^ 20 = 1 := by
  rw [show gen ^ 20 = ofK (K.ofBits 1048576) by
      rw [← word_two_pow (a := 20) (by decide)]; exact word_eOfNat _,
    show word 14347465658197868555 0 0 = ofK (K.ofBits 14347465658197868555) from word_eOfNat _,
    ← ofK_mul, show K.ofBits 14347465658197868555 * K.ofBits 1048576 = 1 by decide +kernel, ofK_one]

theorem size_sel_eq {m e : ℕ} (hm : m < 34) (he : e < 13)
    (h : gen ^ m * word 14347465658197868555 0 0 = gen ^ e) : m = e + 20 := by
  have h2 : gen ^ m = gen ^ (e + 20) := by
    calc gen ^ m = gen ^ m * (word 14347465658197868555 0 0 * gen ^ 20) := by
          rw [sl_word_ginv20_mul, mul_one]
      _ = gen ^ (e + 20) := by rw [← mul_assoc, h, pow_add]
  exact gen_pow_inj (by omega) (by omega) h2

/-! ## The committed columns' total -/

theorem committedCols_length : (Tables.committedCols 165).length = Tables.nCommittedCols := by
  decide +kernel

theorem sum_pow_le (l : List ℕ) (h : ∀ x ∈ l, x ≤ 38) :
    (l.map (2 ^ ·)).sum ≤ l.length * 2 ^ 38 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h x (by simp)
    have h2 := ih (fun y hy ↦ h y (by simp [hy]))
    have : 2 ^ x ≤ 2 ^ 38 := Nat.pow_le_pow_right (by decide) h1
    nlinarith

theorem sl_columnKappas_le {logMem : ℕ} {hs : List ℕ} (hm : logMem ≤ 32) (hl : hs.length = 6)
    (hh : ∀ x ∈ hs, x < 33) : ∀ x ∈ columnKappas logMem 19 hs, x ≤ 38 := by
  have hg : ∀ i, hs.getD i 0 < 33 := fun i ↦ by
    by_cases hi : i < hs.length
    · exact hh _ (getD_mem' hi)
    · rw [List.getD_eq_default _ _ (by omega)]; omega
  intro x hx
  have q6 : qkeccakSlotBits = 6 := by decide
  simp only [columnKappas, List.cons_append, List.mem_cons, List.mem_flatMap,
    List.nil_append] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | ⟨t, -, hx⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [q6]; have := hg opKeccak; omega
  · rw [List.mem_replicate] at hx
    rw [hx.2]
    have := hg t.opcode
    omega

theorem sl_stackTotal_lt {logMem : ℕ} {hs : List ℕ} (hm : logMem ≤ 32) (hl : hs.length = 6)
    (hh : ∀ x ∈ hs, x < 33) : Tables.stackTotal (columnKappas logMem 19 hs) < 2 ^ 45 := by
  have hk := sl_columnKappas_le hm hl hh
  have hlen : (columnKappas logMem 19 hs).length = 165 := by
    simp [columnKappas]; decide +kernel
  have hle := sum_pow_le (Tables.committedKappas (columnKappas logMem 19 hs)) (fun x hx ↦ by
    simp only [Tables.committedKappas, List.mem_map] at hx
    obtain ⟨c, -, rfl⟩ := hx
    by_cases hc : c < (columnKappas logMem 19 hs).length
    · exact hk _ (getD_mem' hc)
    · rw [List.getD_eq_default _ _ (by omega)]; omega)
  have : (Tables.committedKappas (columnKappas logMem 19 hs)).length = Tables.nCommittedCols := by
    simp [Tables.committedKappas, hlen, committedCols_length]
  have hn : Tables.nCommittedCols ≤ 113 := by decide
  unfold Tables.stackTotal
  rw [this] at hle
  omega

end
end LeanVM.Guest.B1.VerifySub
