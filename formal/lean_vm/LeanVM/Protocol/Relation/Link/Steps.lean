/-
  LeanVM.Protocol.Relation.Link.Steps

  Each executed row of the tables takes one leanISA step under the link's relation.
-/

module

public import LeanVM.Protocol.Relation.Link.Valid
public import LeanVM.Protocol.Relation.Link.Shape
import LeanVM.Semantics.Lemmas
import LeanVM.Parameters.Generator
import LeanVM.Parameters.Field
import LeanVM.Protocol.Tables

/-!
# The rows' steps

`RowStep` per table, under the link's relation at an announced layout of the program's bytecode:
the program lookup names the instruction at the row's `pc` (`fetch_of_row`), whose slots are the
program's words (`bcWord_eq`) and whose opcode is the table's (`opcodeOf_slot3`); the memory lookup
reads each accessed cell (`read_of_access`); the table's links then are the instruction's
`executeWith`.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Link
open LeanVM.Arithmetization

@[expose] public section

/-! ## The program's words -/

theorem getD_flatMap_uniform {α β : Type} (f : α → List β) (n : ℕ) (d : β) :
    ∀ (L : List α), (∀ a ∈ L, (f a).length = n) → ∀ s k (hs : s < L.length), k < n →
      (L.flatMap f).getD (s * n + k) d = (f L[s]).getD k d
  | [], _, s, _, hs, _ => absurd hs (by simp)
  | a :: L, hf, 0, k, _, hk => by
    rw [List.flatMap_cons, List.getD_append _ _ _ _ (by rw [hf a (by simp)]; omega)]
    simp
  | a :: L, hf, s + 1, k, hs, hk => by
    rw [List.flatMap_cons, List.getD_append_right _ _ _ _ (by rw [hf a (by simp)]; nlinarith),
      hf a (by simp), show (s + 1) * n + k - n = s * n + k by rw [Nat.succ_mul]; omega]
    exact getD_flatMap_uniform f n d L (fun b hb ↦ hf b (by simp [hb])) s k
      (by simpa using hs) hk

/-- **Word `s·2^logSize + k` of the bytecode** is slot `s` of instruction `k`. -/
theorem bytecodeWords_getD (program : LeanIsaProgram) {s k : ℕ} (hs : s < 16)
    (hk : k < 2 ^ program.logSize) :
    (bytecodeWords program).getD (s * 2 ^ program.logSize + k) 0 =
      (instructionSlots (program.instructions ⟨k, hk⟩))[s] := by
  unfold bytecodeWords
  rw [getD_flatMap_uniform _ (2 ^ program.logSize) 0 _ (fun _ _ ↦ by simp) s k (by simpa using hs) hk]
  simp [List.getD_eq_getElem?_getD, hk]

/-- An opcode's number, its table's. -/
def opIndex : Opcode → ℕ
  | .xor => 0
  | .mulNative => 1
  | .setConstant => 2
  | .deref => 3
  | .jump => 4
  | .keccak => 5

theorem opcodeOf_code : ∀ op : Opcode, opcodeOf op.code = opIndex op := by
  intro op; cases op <;> decide +kernel

/-- An instruction's slot `3` names its opcode. -/
theorem opcodeOf_slot3 (ins : LeanIsaInstruction) :
    opcodeOf (instructionSlots ins)[3] = opIndex ins.opcode := by
  rw [← opcodeOf_code]
  cases ins <;> rfl

/-! ## A row's instruction -/

/-- Every table reads the program at its state's `pc`. -/
theorem bc_pc_eq : ∀ t < nTables,
    (tables.getD t default).links.bytecodeLink.pc = (tables.getD t default).links.stateLink.pc := by
  decide +kernel

variable {program : LeanIsaProgram} {layout : Layout} {ρ : ℕ} {μ : ℕ} {q : Column μ}
  {chunks : Chunks}

/-- **The program lookup names the row's instruction**: at `pc = g^k`, of the table's opcode, its
slots the program's words. -/
theorem fetch_of_row (hA : Announced (bytecodeWords program) layout ρ)
    (hP : ProgramHolds layout q chunks) {t u : ℕ} (ht : t < nTables) (hu : u < tableRowCount layout t) :
    ∃ hk : rowBc layout q chunks t u < 2 ^ program.logSize,
      tableWord layout q t (tableAt layout t).links.stateLink.pc u =
        g ^ rowBc layout q chunks t u ∧
      program.fetch (tableWord layout q t (tableAt layout t).links.stateLink.pc u) =
        some (program.instructions ⟨_, hk⟩) ∧
      opIndex (program.instructions ⟨_, hk⟩).opcode = t ∧
      (∀ s (hs : s < 16), bcWord layout s (rowBc layout q chunks t u) =
        ofK ((instructionSlots (program.instructions ⟨_, hk⟩))[s]'hs)) ∧
      ∀ op ∈ (tableAt layout t).links.bytecodeLink.operands,
        (op.1.map fun s ↦ bcWord layout s (rowBc layout q chunks t u)).sum =
          op.2.evaluate fun c ↦ tableValue layout q t c u := by
  obtain ⟨hB, hT, -, -, -, -⟩ := announced_facts hA
  have hlb := logBytecode_eq hA
  obtain ⟨hk, hpc, hop, -, hops⟩ := hP t ht u hu
  rw [hlb] at hk
  have hbc : ∀ s (hs : s < 16), bcWord layout s (rowBc layout q chunks t u) =
      ofK ((instructionSlots (program.instructions ⟨_, hk⟩))[s]'hs) := fun s hs ↦ by
    rw [bcWord, hB, hlb, bytecodeWords_getD program hs hk]
  have hpcl : (tableAt layout t).links.bytecodeLink.pc = (tableAt layout t).links.stateLink.pc := by
    simp only [tableAt, hT]
    exact bc_pc_eq t ht
  have hpcW : tableWord layout q t (tableAt layout t).links.stateLink.pc u =
      g ^ rowBc layout q chunks t u := by
    rw [hpcl] at hpc
    rw [(tableValue_state hT q ht u).1, gpow_eq_ofK] at hpc
    exact ofK_injective hpc
  refine ⟨hk, hpcW, by rw [hpcW]; exact program.fetch_gpow ⟨_, hk⟩, ?_, hbc, hops⟩
  rw [hB, hlb, bytecodeWords_getD program (by norm_num) hk, opcodeOf_slot3] at hop
  exact hop

/-! ## A row's reads -/

/-- **The memory lookup reads an access's cell**: an access with a nonzero gate, at an address
`A` in `K`, finds its word there. -/
theorem read_of_access (hA : Announced (bytecodeWords program) layout ρ)
    (hM : MemoryHolds layout q chunks) {t u : ℕ} (ht : t < nTables) (hu : u < tableRowCount layout t)
    {a : Access} (ha : a ∈ (tableAt layout t).links.memory) (hg : accessGate layout q t u a ≠ 0)
    {A : K} (hAd : accessAddress layout q t u (rowBc layout q chunks t u) a = ofK A) :
    (memoryImage layout q).read A = some (accessWord layout q chunks t u (rowBc layout q chunks t u) a) := by
  obtain ⟨-, -, -, -, hmax, -⟩ := announced_facts hA
  obtain ⟨j, -, hj, haddr, hword⟩ := hM t ht u hu a ha hg
  rw [hAd, gpow_eq_ofK] at haddr
  rw [← ofK_injective haddr, ← hword]
  have hκ : layout.logMemory < 64 := by simp only [maxLogMemory] at hmax; omega
  exact MemoryImage.read_gpow hκ (memoryImage layout q) ⟨j, hj⟩


/-! ## Forms and words -/

theorem eY_eq_y : eY = y := by rw [eY, ofLimbs_eq]; simp

theorem word_of_limbs (a b : K) : ofK a + eY * ofK b = E.ofLimbs a b := by
  rw [ofLimbs_eq, eY_eq_y, mul_comm]

theorem Form.col_evaluate (i e : ℕ) (col : ℕ → E) : (Form.col i e).evaluate col = gpow e * col i := by
  simp [Form.evaluate, Form.col, sumE]

theorem Form.empty_evaluate (col : ℕ → E) : ({} : Form).evaluate col = 0 := by
  simp [Form.evaluate, sumE]

theorem tableAt_eq {layout : Layout} (hT : layout.tables = tables) (t : ℕ) :
    tableAt layout t = tables.getD t default := by rw [tableAt, hT]

/-- The state link of a table whose successor is the next instruction in the same frame. -/
theorem rowNext_step {layout : Layout} (hT : layout.tables = tables) {μ : ℕ} (q : Column μ)
    (x : LinkRow layout)
    (hnext : (tableAt layout x.1).links.stateLink.next =
      (Form.col (tableAt layout x.1).links.stateLink.pc 1,
        Form.col (tableAt layout x.1).links.stateLink.fp 0)) :
    rowNext layout q x =
      regE ⟨g * tableWord layout q x.1 (tableAt layout x.1).links.stateLink.pc x.2,
        tableWord layout q x.1 (tableAt layout x.1).links.stateLink.fp x.2⟩ := by
  obtain ⟨hpc, hfp⟩ := tableValue_state hT q x.1.isLt x.2
  have h1 : rowNext layout q x 0 = (tableAt layout x.1).links.stateLink.next.1.evaluate
      (fun c ↦ tableValue layout q x.1 c x.2) := rfl
  have h2 : rowNext layout q x 1 = (tableAt layout x.1).links.stateLink.next.2.evaluate
      (fun c ↦ tableValue layout q x.1 c x.2) := rfl
  funext i
  fin_cases i
  · show rowNext layout q x 0 = ofK _
    rw [h1, hnext, Form.col_evaluate, hpc, gpow_eq_ofK, pow_one, ← ofK_mul]
  · show rowNext layout q x 1 = ofK _
    rw [h2, hnext, Form.col_evaluate, hfp, gpow_eq_ofK, pow_zero, ← ofK_mul, one_mul]

/-- A row's state is its words' registers. -/
theorem rowState_regs {layout : Layout} (hT : layout.tables = tables) {μ : ℕ} (q : Column μ)
    (x : LinkRow layout) :
    rowState layout q x =
      regE ⟨tableWord layout q x.1 (tableAt layout x.1).links.stateLink.pc x.2,
        tableWord layout q x.1 (tableAt layout x.1).links.stateLink.fp x.2⟩ := by
  obtain ⟨hpc, hfp⟩ := tableValue_state hT q x.1.isLt x.2
  funext i
  fin_cases i <;> simp [rowState, regE, hpc, hfp]

/-! ## `SET` -/

theorem set_links : (tables.getD 2 default).links.stateLink =
      { cycle := 4, pc := 0, fp := 1, next := (Form.col 0 1, Form.col 1 0) } ∧
    (tables.getD 2 default).links.memory =
      [{ pointer := 2, shift := 0, gate := none, address := {}, frame := some (4, 0), value := {},
         reads := [.slot 5 1, .slot 6 eY] }] := ⟨rfl, rfl⟩

theorem rowStep_set (hA : Announced (bytecodeWords program) layout ρ)
    (hM : MemoryHolds layout q chunks) (hP : ProgramHolds layout q chunks) (u : ℕ)
    (hu : u < tableRowCount layout 2) : RowStep program layout q ⟨⟨2, by decide⟩, ⟨u, hu⟩⟩ := by
  obtain ⟨-, hT, -⟩ := announced_facts hA
  obtain ⟨hk, -, hfetch, hop, hbc, -⟩ := fetch_of_row hA hP (t := 2) (by decide) hu
  obtain ⟨hst, hmem⟩ := set_links
  refine ⟨_, _, rowState_regs hT q _, rowNext_step hT q _ (by rw [tableAt_eq hT]; simp only [hst]), ?_⟩
  rw [step_of_fetch_eq_some hfetch]
  generalize hI : program.instructions ⟨_, hk⟩ = ins at hop hbc
  cases ins with
  | setConstant o kk =>
    let a : Access := Access.mk 2 0 none {} (some (4, 0)) {} [.slot 5 1, .slot 6 eY]
    have ha : a ∈ (tableAt layout 2).links.memory := by
      rw [tableAt_eq hT, hmem]; exact List.mem_singleton_self _
    have hfp := (tableValue_state hT q (t := 2) (by decide) u).2
    have hread := read_of_access hA hM (by decide) hu ha (by simp [accessGate, a])
      (A := tableWord layout q 2 (tableAt layout 2).links.stateLink.fp u * o) (by
        rw [accessAddress]
        simp only [a, Form.empty_evaluate, zero_add, gpow, pow_zero, one_mul]
        rw [hbc 4 (by norm_num), hfp, ofK_mul]
        rfl)
    have hw : accessWord layout q chunks 2 u (rowBc layout q chunks 2 u) a = kk := by
      simp only [accessWord, a, Form.empty_evaluate, zero_add, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, readValue, one_mul]
      rw [hbc 5 (by norm_num), hbc 6 (by norm_num), word_of_limbs]
      exact ofLimbs_limb kk
    rw [hw] at hread
    show executeWith (memoryImage layout q).read
      ⟨tableWord layout q 2 (tableAt layout 2).links.stateLink.pc u,
        tableWord layout q 2 (tableAt layout 2).links.stateLink.fp u⟩ (.setConstant o kk) = _
    simp only [executeWith, hread]
    simp [Registers.next]
  | _ => simp [opIndex, LeanIsaInstruction.opcode] at hop


/-! ## Framed accesses -/

theorem Form.const_evaluate (v : E) (col : ℕ → E) : (Form.const v).evaluate col = v := by
  simp [Form.evaluate, Form.const, sumE]

/-- **A framed access reads its cell**: an ungated access at `fp·BC_s`, `s` a slot holding `o`,
reads its word at `fp·o`. -/
theorem read_framed (hA : Announced (bytecodeWords program) layout ρ)
    (hM : MemoryHolds layout q chunks) {t u : ℕ} (ht : t < nTables) (hu : u < tableRowCount layout t)
    {p s : ℕ} {v : Form} {rs : List Read}
    (ha : Access.mk p 0 none {} (some (s, 0)) v rs ∈ (tableAt layout t).links.memory) {o : K}
    (ho : bcWord layout s (rowBc layout q chunks t u) = ofK o) :
    (memoryImage layout q).read (tableWord layout q t (tableAt layout t).links.stateLink.fp u * o) =
      some (accessWord layout q chunks t u (rowBc layout q chunks t u)
        (Access.mk p 0 none {} (some (s, 0)) v rs)) := by
  obtain ⟨-, hT, -⟩ := announced_facts hA
  refine read_of_access hA hM ht hu ha (by simp [accessGate]) ?_
  rw [accessAddress]
  simp only [Form.empty_evaluate, zero_add, gpow, pow_zero, one_mul]
  rw [ho, (tableValue_state hT q ht u).2, ofK_mul]

/-- The word of a framed access. -/
theorem accessWord_mk (t u k p s : ℕ) (v : Form) (rs : List Read) :
    accessWord layout q chunks t u k (Access.mk p 0 none {} (some (s, 0)) v rs) =
      v.evaluate (fun c ↦ tableValue layout q t c u) + (rs.map (readValue layout q chunks t u k)).sum :=
  rfl

theorem readValue_word (t u k p : ℕ) :
    readValue layout q chunks t u k (.word p (Form.const 1)) = memWord layout q (rowPtr layout q chunks t p u) := by
  simp [readValue, Form.const_evaluate]

/-! ## `XOR` and `MUL` -/

theorem xor_links : (tables.getD 0 default).links.stateLink =
      { cycle := 6, pc := 0, fp := 1, next := (Form.col 0 1, Form.col 1 0) } ∧
    (tables.getD 0 default).links.memory =
      [Access.mk 2 0 none {} (some (4, 0)) {} [.word 2 (Form.const 1)],
       Access.mk 3 0 none {} (some (5, 0)) {} [.word 3 (Form.const 1)],
       Access.mk 4 0 none {} (some (6, 0)) {} [.word 2 (Form.const 1), .word 3 (Form.const 1)]] :=
  ⟨rfl, rfl⟩

theorem rowStep_xor (hA : Announced (bytecodeWords program) layout ρ)
    (hM : MemoryHolds layout q chunks) (hP : ProgramHolds layout q chunks) (u : ℕ)
    (hu : u < tableRowCount layout 0) : RowStep program layout q ⟨⟨0, by decide⟩, ⟨u, hu⟩⟩ := by
  obtain ⟨-, hT, -⟩ := announced_facts hA
  obtain ⟨hk, -, hfetch, hop, hbc, -⟩ := fetch_of_row hA hP (t := 0) (by decide) hu
  obtain ⟨hst, hmem⟩ := xor_links
  refine ⟨_, _, rowState_regs hT q _, rowNext_step hT q _ (by rw [tableAt_eq hT]; simp only [hst]), ?_⟩
  rw [step_of_fetch_eq_some hfetch]
  generalize hI : program.instructions ⟨_, hk⟩ = ins at hop hbc
  cases ins with
  | xor oA oB oC =>
    have h1 := read_framed hA hM (t := 0) (by decide) hu (p := 2) (v := {}) (rs := [.word 2 (Form.const 1)]) (o := oA)
      (by rw [tableAt_eq hT, hmem]; simp) (hbc 4 (by norm_num))
    have h2 := read_framed hA hM (t := 0) (by decide) hu (p := 3) (v := {}) (rs := [.word 3 (Form.const 1)]) (o := oB)
      (by rw [tableAt_eq hT, hmem]; simp) (hbc 5 (by norm_num))
    have h3 := read_framed hA hM (t := 0) (by decide) hu (p := 4) (v := {})
      (rs := [.word 2 (Form.const 1), .word 3 (Form.const 1)]) (o := oC)
      (by rw [tableAt_eq hT, hmem]; simp) (hbc 6 (by norm_num))
    simp only [accessWord_mk, Form.empty_evaluate, zero_add, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, readValue_word] at h1 h2 h3
    show executeWith (memoryImage layout q).read
      ⟨tableWord layout q 0 (tableAt layout 0).links.stateLink.pc u,
        tableWord layout q 0 (tableAt layout 0).links.stateLink.fp u⟩ (.xor oA oB oC) = _
    simp only [executeWith, h1, h2, h3]
    simp [Registers.next]
  | _ => simp [opIndex, LeanIsaInstruction.opcode] at hop

/-- `MUL`'s committed `a = a_0 + y·a_1`. -/
def mulA : Form := (Form.col 2 0).add ⟨[([3], eY)]⟩

theorem mul_links : (tables.getD 1 default).links.stateLink =
      { cycle := 8, pc := 0, fp := 1, next := (Form.col 0 1, Form.col 1 0) } ∧
    (tables.getD 1 default).links.memory =
      [Access.mk 4 0 none {} (some (4, 0)) mulA [],
       Access.mk 5 0 none {} (some (5, 0)) {} [.word 5 (Form.const 1)],
       Access.mk 6 0 none {} (some (6, 0)) {} [.word 5 mulA]] :=
  ⟨rfl, rfl⟩

theorem rowStep_mul (hA : Announced (bytecodeWords program) layout ρ)
    (hM : MemoryHolds layout q chunks) (hP : ProgramHolds layout q chunks) (u : ℕ)
    (hu : u < tableRowCount layout 1) : RowStep program layout q ⟨⟨1, by decide⟩, ⟨u, hu⟩⟩ := by
  obtain ⟨-, hT, -⟩ := announced_facts hA
  obtain ⟨hk, -, hfetch, hop, hbc, -⟩ := fetch_of_row hA hP (t := 1) (by decide) hu
  obtain ⟨hst, hmem⟩ := mul_links
  refine ⟨_, _, rowState_regs hT q _, rowNext_step hT q _ (by rw [tableAt_eq hT]; simp only [hst]), ?_⟩
  rw [step_of_fetch_eq_some hfetch]
  generalize hI : program.instructions ⟨_, hk⟩ = ins at hop hbc
  cases ins with
  | mulNative oA oB oC =>
    have h1 := read_framed hA hM (t := 1) (by decide) hu (p := 4) (v := mulA) (rs := []) (o := oA)
      (by rw [tableAt_eq hT, hmem]; simp) (hbc 4 (by norm_num))
    have h2 := read_framed hA hM (t := 1) (by decide) hu (p := 5) (v := {}) (rs := [.word 5 (Form.const 1)]) (o := oB)
      (by rw [tableAt_eq hT, hmem]; simp) (hbc 5 (by norm_num))
    have h3 := read_framed hA hM (t := 1) (by decide) hu (p := 6) (v := {}) (rs := [.word 5 mulA]) (o := oC)
      (by rw [tableAt_eq hT, hmem]; simp) (hbc 6 (by norm_num))
    simp only [accessWord_mk, Form.empty_evaluate, zero_add, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, readValue_word] at h1 h2 h3
    simp only [readValue] at h3
    show executeWith (memoryImage layout q).read
      ⟨tableWord layout q 1 (tableAt layout 1).links.stateLink.pc u,
        tableWord layout q 1 (tableAt layout 1).links.stateLink.fp u⟩ (.mulNative oA oB oC) = _
    simp only [executeWith, h1, h2, h3]
    simp [Registers.next]
  | _ => simp [opIndex, LeanIsaInstruction.opcode] at hop


/-! ## `JUMP` -/

theorem le_two_pow_log2Ceil (n : ℕ) : n ≤ 2 ^ log2Ceil n := by
  unfold log2Ceil bitLength
  split_ifs with h0
  · omega
  · have := Nat.lt_log2_self (n := n - 1); omega

theorem le_two_pow_zipWith : ∀ (rows floors : List ℕ) (t : ℕ), t < rows.length →
    t < floors.length → rows.getD t 0 ≤
      2 ^ (List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) rows floors).getD t 0
  | [], _, _, h, _ => absurd h (by simp)
  | _ :: _, [], _, _, h => absurd h (by simp)
  | r :: _, _ :: _, 0, _, _ => by
    simp only [List.zipWith_cons_cons, List.getD_cons_zero]
    exact (le_two_pow_log2Ceil r).trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
  | _ :: rs, _ :: fs, t + 1, h1, h2 => by
    simp only [List.zipWith_cons_cons, List.getD_cons_succ]
    exact le_two_pow_zipWith rs fs t (by simpa using h1) (by simpa using h2)

/-- A table's rows fit its height. -/
theorem tableRows_le_height {layout : Layout} {ρ : ℕ} {bytecode : List K}
    (hA : Announced bytecode layout ρ) {t : ℕ} (ht : t < nTables) :
    tableRowCount layout t ≤ 2 ^ layout.tableLogHeights.getD t 0 := by
  obtain ⟨lm, rows, hB⟩ := announced_build hA
  have hlen := (announced_facts hA).2.2.2.2.2
  unfold buildLayout at hB
  split at hB
  · cases hB
  · split at hB
    · simp only [Option.some.injEq] at hB
      subst hB
      simp only [tableRowCount] at hlen ⊢
      exact le_two_pow_zipWith _ _ t (by rw [hlen]; exact ht) (by rw [show tableLogFloors.length = nTables from rfl]; exact ht)
    · cases hB

theorem rowValues_getD {layout : Layout} (hT : layout.tables = tables) {μ : ℕ} (q : Column μ)
    {t i : ℕ} (u : ℕ) (hi : i < (tables.getD t default).width) :
    (rowValues layout q t u).getD i 0 = tableValue layout q t i u := by
  rw [rowValues, tableAt_eq hT, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem tableValue_ofK {layout : Layout} {μ : ℕ} (q : Column μ) {t c : ℕ} (u : ℕ)
    (h : keccakOutputLane (globalColumnBases.getD t 0 + c) = none) :
    tableValue layout q t c u = ofK (tableWord layout q t c u) := by
  rw [tableValue, columnValue, h]
  rfl

theorem jump_links : (tables.getD 4 default).links.stateLink =
      { cycle := 13, pc := 0, fp := 1, next := (Form.col 5 0, Form.col 6 0) } ∧
    (tables.getD 4 default).links.memory =
      [Access.mk 9 0 none {} (some (4, 0)) (Form.col 2 0) [],
       Access.mk 10 0 none {} (some (5, 0)) (Form.col 3 0) [],
       Access.mk 11 0 none {} (some (6, 0)) (Form.col 4 0) []] ∧
    (tables.getD 4 default).width = 14 ∧
    (tables.getD 4 default).constraints = jumpConstraints := ⟨rfl, rfl, rfl, rfl⟩

theorem jumpConstraints_eq (v : List E) : jumpConstraints v =
    [v.getD 8 0 + v.getD 2 0 * v.getD 7 0, v.getD 2 0 * (v.getD 8 0 + 1),
      v.getD 5 0 + v.getD 8 0 * v.getD 3 0 + (v.getD 8 0 + 1) * gpow 1 * v.getD 0 0,
      v.getD 6 0 + v.getD 8 0 * v.getD 4 0 + (v.getD 8 0 + 1) * v.getD 1 0] := rfl

theorem jump_cols : ∀ c < 14, keccakOutputLane (globalColumnBases.getD 4 0 + c) = none := by
  decide +kernel

theorem eq_of_add_eq_zero {a b : E} (h : a + b = 0) : a = b := by
  linear_combination h - b * Tables.two_eq_zero_E

theorem rowStep_jump (hA : Announced (bytecodeWords program) layout ρ)
    (hM : MemoryHolds layout q chunks) (hP : ProgramHolds layout q chunks)
    (hC : ConstraintsHold layout q) (u : ℕ)
    (hu : u < tableRowCount layout 4) : RowStep program layout q ⟨⟨4, by decide⟩, ⟨u, hu⟩⟩ := by
  obtain ⟨-, hT, -⟩ := announced_facts hA
  obtain ⟨hk, -, hfetch, hop, hbc, -⟩ := fetch_of_row hA hP (t := 4) (by decide) hu
  obtain ⟨hst, hmem, hwid, hcon⟩ := jump_links
  have hv : ∀ c < 14, (rowValues layout q 4 u).getD c 0 = ofK (tableWord layout q 4 c u) :=
    fun c hc ↦ by rw [rowValues_getD hT q u (by rw [hwid]; exact hc), tableValue_ofK q u (jump_cols c hc)]
  have hcons := hC 4 (by decide) u (lt_of_lt_of_le hu (tableRows_le_height hA (by decide)))
  simp only [tableAt_eq hT, hcon, jumpConstraints_eq, hv 0 (by norm_num), hv 1 (by norm_num),
    hv 2 (by norm_num), hv 3 (by norm_num), hv 4 (by norm_num), hv 5 (by norm_num),
    hv 6 (by norm_num), hv 7 (by norm_num), hv 8 (by norm_num), List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at hcons
  obtain ⟨e1, e2, e3, e4⟩ := hcons
  have hs := rowState_regs hT q (layout := layout) ⟨⟨4, by decide⟩, ⟨u, hu⟩⟩
  have hn : rowNext layout q ⟨⟨4, by decide⟩, ⟨u, hu⟩⟩ =
      regE ⟨tableWord layout q 4 5 u, tableWord layout q 4 6 u⟩ := by
    funext i
    fin_cases i
    · show (tableAt layout 4).links.stateLink.next.1.evaluate _ = ofK _
      rw [tableAt_eq hT, hst, Form.col_evaluate, tableValue_ofK q u (jump_cols 5 (by norm_num)),
        gpow_eq_ofK, pow_zero, ← ofK_mul, one_mul]
    · show (tableAt layout 4).links.stateLink.next.2.evaluate _ = ofK _
      rw [tableAt_eq hT, hst, Form.col_evaluate, tableValue_ofK q u (jump_cols 6 (by norm_num)),
        gpow_eq_ofK, pow_zero, ← ofK_mul, one_mul]
  refine ⟨_, _, hs, hn, ?_⟩
  rw [step_of_fetch_eq_some hfetch]
  generalize hI : program.instructions ⟨_, hk⟩ = ins at hop hbc
  cases ins with
  | jump oc od ofr =>
    have hval : ∀ c < 14, (Form.col c 0).evaluate (fun c ↦ tableValue layout q 4 c u) =
        ofK (tableWord layout q 4 c u) := fun c hc ↦ by
      rw [Form.col_evaluate, tableValue_ofK q u (jump_cols c hc), gpow_eq_ofK, pow_zero, ← ofK_mul,
        one_mul]
    have h1 := read_framed hA hM (t := 4) (by decide) hu (p := 9) (v := Form.col 2 0) (rs := [])
      (o := oc) (by rw [tableAt_eq hT, hmem]; simp) (hbc 4 (by norm_num))
    have h2 := read_framed hA hM (t := 4) (by decide) hu (p := 10) (v := Form.col 3 0) (rs := [])
      (o := od) (by rw [tableAt_eq hT, hmem]; simp) (hbc 5 (by norm_num))
    have h3 := read_framed hA hM (t := 4) (by decide) hu (p := 11) (v := Form.col 4 0) (rs := [])
      (o := ofr) (by rw [tableAt_eq hT, hmem]; simp) (hbc 6 (by norm_num))
    simp only [accessWord_mk, List.map_nil, List.sum_nil, add_zero, hval 2 (by norm_num),
      hval 3 (by norm_num), hval 4 (by norm_num)] at h1 h2 h3
    show executeWith (memoryImage layout q).read
      ⟨tableWord layout q 4 (tableAt layout 4).links.stateLink.pc u,
        tableWord layout q 4 (tableAt layout 4).links.stateLink.fp u⟩ (.jump oc od ofr) = _
    simp only [executeWith, h1, h2, h3]
    simp only [tableAt_eq hT, hst]
    have hin : ∀ a : K, IsInK (ofK a) := fun a ↦ (isInK_iff _).mpr ⟨a, rfl⟩
    have hz : (ofK 0 : E) = 0 := by rw [ofK_eq_ofLimbs]; exact (ofLimbs_eq_zero_iff 0).mpr rfl
    have hin0 : IsInK (0 : E) := hz ▸ hin 0
    by_cases hc0 : tableWord layout q 4 2 u = 0
    · have hb : ofK (tableWord layout q 4 8 u) = 0 := by
        rw [hc0, hz, zero_mul, add_zero] at e1; exact e1
      simp only [hb, zero_mul, add_zero, zero_add, one_mul] at e3 e4
      have h3' := eq_of_add_eq_zero e3
      have h4' := eq_of_add_eq_zero e4
      rw [gpow_eq_ofK, pow_one, ← ofK_mul] at h3'
      simp [hin, hin0, hc0, hz, Registers.next, ofK_injective h3', ofK_injective h4']
    · have hc0' : ofK (tableWord layout q 4 2 u) ≠ 0 := fun h ↦ hc0 (ofK_injective (h.trans hz.symm))
      have hb1 : ofK (tableWord layout q 4 8 u) + 1 = 0 :=
        (mul_eq_zero.mp e2).resolve_left hc0'
      have hb : ofK (tableWord layout q 4 8 u) = 1 := eq_of_add_eq_zero hb1
      rw [hb1, zero_mul, zero_mul, add_zero, hb, one_mul] at e3
      rw [hb1, zero_mul, add_zero, hb, one_mul] at e4
      have h3' := eq_of_add_eq_zero e3
      have h4' := eq_of_add_eq_zero e4
      simp [hin, hc0', ofK_injective h3', ofK_injective h4']
  | _ => simp [opIndex, LeanIsaInstruction.opcode] at hop


/-! ## `DEREF` -/

theorem deref_links : (tables.getD 3 default).links.stateLink =
      { cycle := 9, pc := 0, fp := 1, next := (Form.col 0 1, Form.col 1 0) } ∧
    (tables.getD 3 default).links.memory =
      [Access.mk 5 0 none {} (some (4, 0)) (Form.col 2 0) [],
       Access.mk 6 0 none (Form.prod 2 3 0) none {}
        [.word 7 ((Form.const 1).add (Form.col 4 0)), .pc 7 (gpow 2), .frame 8 1],
       Access.mk 7 0 none {} (some (6, 0)) {} [.word 7 (Form.const 1)]] ∧
    (tables.getD 3 default).links.bytecodeLink.operands =
      [([5], Form.col 3 0), ([7, 8], Form.col 4 0)] := ⟨rfl, rfl, rfl⟩

theorem deref_cols : ∀ c < 10, keccakOutputLane (globalColumnBases.getD 3 0 + c) = none := by
  decide +kernel

theorem ofK_one : ofK (1 : K) = 1 := map_one (algebraMap K E)

theorem ofK_zero : ofK (0 : K) = 0 := map_zero (algebraMap K E)

theorem one_add_col_evaluate (i : ℕ) (col : ℕ → E) :
    ((Form.const 1).add (Form.col i 0)).evaluate col = 1 + gpow 0 * col i := by
  simp [Form.add, Form.addScaled, addTerm, Form.evaluate, Form.const, Form.col, sumE]

theorem prod_evaluate (a b : ℕ) (col : ℕ → E) (h : a < b) :
    (Form.prod a b 0).evaluate col = gpow 0 * col a * col b := by
  simp [Form.prod, Form.evaluate, sumE, min_eq_left h.le, max_eq_right h.le]

theorem rowStep_deref (hA : Announced (bytecodeWords program) layout ρ)
    (hM : MemoryHolds layout q chunks) (hP : ProgramHolds layout q chunks) (u : ℕ)
    (hu : u < tableRowCount layout 3) : RowStep program layout q ⟨⟨3, by decide⟩, ⟨u, hu⟩⟩ := by
  obtain ⟨-, hT, -⟩ := announced_facts hA
  obtain ⟨hk, hpcW, hfetch, hop, hbc, hops⟩ := fetch_of_row hA hP (t := 3) (by decide) hu
  obtain ⟨hst, hmem, hopnd⟩ := deref_links
  refine ⟨_, _, rowState_regs hT q _, rowNext_step hT q _ (by rw [tableAt_eq hT]; simp only [hst]), ?_⟩
  rw [step_of_fetch_eq_some hfetch]
  have hv : ∀ c < 10, tableValue layout q 3 c u = ofK (tableWord layout q 3 c u) :=
    fun c hc ↦ tableValue_ofK q u (deref_cols c hc)
  rw [tableAt_eq hT, hopnd] at hops
  have hop5 := hops ([5], Form.col 3 0) (by simp)
  have hop78 := hops ([7, 8], Form.col 4 0) (by simp)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    Form.col_evaluate, hv 3 (by norm_num), hv 4 (by norm_num), gpow_eq_ofK, pow_zero, ofK_one,
    one_mul] at hop5 hop78
  generalize hI : program.instructions ⟨_, hk⟩ = ins at hop hbc
  cases ins with
  | deref o1 o2 o3 mode =>
    rw [hbc 5 (by norm_num)] at hop5
    rw [hbc 7 (by norm_num), hbc 8 (by norm_num)] at hop78
    have ho2 : tableWord layout q 3 3 u = o2 := (ofK_injective hop5).symm
    have h1 := read_framed hA hM (t := 3) (by decide) hu (p := 5) (v := Form.col 2 0) (rs := [])
      (o := o1) (by rw [tableAt_eq hT, hmem]; simp) (hbc 4 (by norm_num))
    have h3 := read_framed hA hM (t := 3) (by decide) hu (p := 7) (v := {})
      (rs := [.word 7 (Form.const 1)]) (o := o3) (by rw [tableAt_eq hT, hmem]; simp)
      (hbc 6 (by norm_num))
    have ha2 : Access.mk 6 0 none (Form.prod 2 3 0) none {}
        [.word 7 ((Form.const 1).add (Form.col 4 0)), .pc 7 (gpow 2), .frame 8 1] ∈
        (tableAt layout 3).links.memory := by rw [tableAt_eq hT, hmem]; simp
    have h2 := read_of_access hA hM (t := 3) (by decide) hu ha2 (by simp [accessGate])
      (A := tableWord layout q 3 2 u * o2) (by
        rw [accessAddress]
        simp only [prod_evaluate 2 3 _ (by norm_num), hv 2 (by norm_num), hv 3 (by norm_num),
          gpow_eq_ofK, pow_zero, ofK_one, one_mul, add_zero, ho2, ofK_mul])
    simp only [accessWord_mk, Form.empty_evaluate, zero_add, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, readValue_word, Form.col_evaluate,
      hv 2 (by norm_num), gpow_eq_ofK, pow_zero, ofK_one, one_mul] at h1 h3
    simp only [accessWord, Form.empty_evaluate, zero_add, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, readValue, one_add_col_evaluate, hv 4 (by norm_num),
      gpow_eq_ofK, pow_zero, ofK_one, one_mul, tableAt_eq hT, hst] at h2
    show executeWith (memoryImage layout q).read
      ⟨tableWord layout q 3 (tableAt layout 3).links.stateLink.pc u,
        tableWord layout q 3 (tableAt layout 3).links.stateLink.fp u⟩ (.deref o1 o2 o3 mode) = _
    simp only [tableAt_eq hT, hst] at h1 h3 hpcW ⊢
    have hin : IsInK (ofK (tableWord layout q 3 2 u)) := (isInK_iff _).mpr ⟨_, rfl⟩
    rw [hbc 7 (by norm_num), hbc 8 (by norm_num), hv 1 (by norm_num)] at h2
    rw [hpcW]
    simp only [executeWith, h1, h3, limb_ofK, hin, Option.bind_eq_bind, Option.bind_some,
      guard, ite_true, show ((0 : Fin 2) : ℕ) = 0 from rfl, h2]
    have h2' : (2 : E) = 0 := Tables.two_eq_zero_E
    cases mode
    · have h7 : (instructionSlots (.deref o1 o2 o3 .cell))[7] = 0 := rfl
      have h8 : (instructionSlots (.deref o1 o2 o3 .cell))[8] = 0 := rfl
      rw [h7, h8, ofK_zero, add_zero] at hop78
      rw [h7, h8, ofK_zero, ← hop78]
      simp [derefSource, Registers.next]
    · have h7 : (instructionSlots (.deref o1 o2 o3 .pc))[7] = 1 := rfl
      have h8 : (instructionSlots (.deref o1 o2 o3 .pc))[8] = 0 := rfl
      rw [h7, h8, ofK_zero, ofK_one, add_zero] at hop78
      have key : (1 + ofK (tableWord layout q 3 4 u)) * memWord layout q (rowPtr layout q chunks 3 7 u) +
          (ofK (g ^ 2) * ofK (g ^ rowBc layout q chunks 3 u) * ofK 1 +
            ofK (tableWord layout q 3 1 u) * ofK 0) =
          derefSource .pc ⟨g ^ rowBc layout q chunks 3 u, tableWord layout q 3 1 u⟩
            (memWord layout q (rowPtr layout q chunks 3 7 u)) := by
        rw [← hop78, ofK_one, ofK_zero, derefSource, ofK_mul]
        linear_combination (memWord layout q (rowPtr layout q chunks 3 7 u)) * h2'
      rw [h7, h8, key]
      simp [Registers.next]
    · have h7 : (instructionSlots (.deref o1 o2 o3 .fp))[7] = 0 := rfl
      have h8 : (instructionSlots (.deref o1 o2 o3 .fp))[8] = 1 := rfl
      rw [h7, h8, ofK_zero, ofK_one, zero_add] at hop78
      have key : (1 + ofK (tableWord layout q 3 4 u)) * memWord layout q (rowPtr layout q chunks 3 7 u) +
          (ofK (g ^ 2) * ofK (g ^ rowBc layout q chunks 3 u) * ofK 0 +
            ofK (tableWord layout q 3 1 u) * ofK 1) =
          derefSource .fp ⟨g ^ rowBc layout q chunks 3 u, tableWord layout q 3 1 u⟩
            (memWord layout q (rowPtr layout q chunks 3 7 u)) := by
        rw [← hop78, ofK_one, ofK_zero, derefSource]
        linear_combination (memWord layout q (rowPtr layout q chunks 3 7 u)) * h2'
      rw [h7, h8, key]
      simp [Registers.next]
  | _ => simp [opIndex, LeanIsaInstruction.opcode] at hop


/-! ## Every row -/

/-- **`KECCAK`'s rows take their leanISA step** (what is left of the rows' steps). -/
def KeccakRowSteps (program : LeanIsaProgram) (layout : Layout) {μ : ℕ} (q : Column μ) : Prop :=
  ∀ u (hu : u < tableRowCount layout 5), RowStep program layout q ⟨⟨5, by decide⟩, ⟨u, hu⟩⟩

/-- **Every executed row takes its leanISA step** under the link's relation, `KECCAK`'s given. -/
theorem rowStep_of_rel (hA : Announced (bytecodeWords program) layout ρ)
    (hrel : LinkRel layout q) (hk : KeccakRowSteps program layout q) (x : LinkRow layout) :
    RowStep program layout q x := by
  obtain ⟨chunks, -, -, -, hM, hP, hC⟩ := hrel
  obtain ⟨⟨t, ht⟩, ⟨u, hu⟩⟩ := x
  simp only [nTables] at ht
  interval_cases t
  · exact rowStep_xor hA hM hP u hu
  · exact rowStep_mul hA hM hP u hu
  · exact rowStep_set hA hM hP u hu
  · exact rowStep_deref hA hM hP u hu
  · exact rowStep_jump hA hM hP hC u hu
  · exact hk u hu

end

end LeanVM.Protocol.Relation
