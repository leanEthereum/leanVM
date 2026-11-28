/-
  LeanVM.Prover.Complete.Link.TailRowBase

  A bound table's base terms: its payload under `ω·eq(0, r)` and `JUMP`'s identities under
  `eq(τ, ·)`, evaluated at its bound tables.
-/

module

public import LeanVM.Prover.Complete.Link.TailRowVer

/-!
# The base terms at the row point

`baseAt_blocks`: a bound table's base terms are its blocks' values (`blockVal`) at its bound
tables, times its corner. `sum_blockVal_tableBlocks`: the blocks' values are `ω·eq(0, r)` times the
payload forms' value, plus `eq(τ, ·)` times `JUMP`'s identity form. `payloadVal_payloadForms`: the
payload forms' value is the verifier's payload (`payloadAt`: `η_mem·memory + η_bc·R_bc`), the
gated forms each once (`linkGates` has distinct gates, every access's gate among them).
`jump_evaluate`: `JUMP`'s identity form is the identities weighed.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Protocol.Verifier.Defers

/-! ## The blocks at an evaluation -/

/-- A block's value where table `f` reads `ev f`. -/
def blockVal (ev : ℕ → E) (b : Block) : E :=
  ev (if b.onEq then 2 else 0) * (b.gate.map fun g ↦ ev (3 + g)).getD 1 *
    b.form.evaluate fun c ↦ ev (3 + c)

theorem termsVal_rowBaseStep (ev : ℕ → E) (T : Array (E × Array ℕ)) (b : Block) :
    termsVal ev (rowBaseStep T b) = termsVal ev T + blockVal ev b := by
  unfold rowBaseStep
  dsimp only
  rw [termsVal_foldl ev _ (fun m : List ℕ × E ↦ ev (if b.onEq then 2 else 0) *
      (b.gate.map fun g ↦ ev (3 + g)).getD 1 * tailRowMono (fun c ↦ ev (3 + c)) m) (fun T m ↦ ?_)]
  · rw [blockVal, evaluate_eq_sum, List.sum_map_mul_left]
  · obtain ⟨vars, c⟩ := m
    rw [termsVal_push]
    refine congrArg (termsVal ev T + ·) ?_
    unfold termVal tailRowMono
    simp only [Array.toList_append, List.map_append, List.prod_append, prod_gate,
      List.map_map, Function.comp_def, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil]
    ring

theorem termsVal_foldl_blocks (ev : ℕ → E) (bs : List Block) (T : Array (E × Array ℕ)) :
    termsVal ev (bs.foldl rowBaseStep T) = termsVal ev T + (bs.map (blockVal ev)).sum :=
  termsVal_foldl ev rowBaseStep (blockVal ev) (termsVal_rowBaseStep ev) bs T

/-- **A bound table's base terms are its blocks' values.** -/
theorem baseAt_blocks {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (x : LinkProverPre) (chi : List E)
    (hchi : chi.length = linkNRows W) {t : ℕ} (ht : t < nTables) :
    baseAt ((chi.foldl rowFold (linkRowStart W x)).getD t default) =
      ((chi.foldl rowFold (linkRowStart W x)).getD t default).corner *
        ((tableBlocks (linkRowInputs W x).ch t (linkRowInputs W x).eq0
          (some (linkRowInputs W x).jump)).map
          (blockVal ((chi.foldl rowFold (linkRowStart W x)).getD t default).prods.at)).sum := by
  have _hW := hW
  have hh : W.layout.tableLogHeights.getD t 0 ≤ chi.length := hchi ▸ le_foldl_max _ _
  set inp := linkRowInputs W x
  have hrt := rowStart_getD W x chi ht hh
  set rt := (chi.foldl rowFold (linkRowStart W x)).getD t default
  set r := (tables.getD t default).links.pointers.zipIdx.foldl
    (rowPointerStep W inp t (pointerStarts.getD t 0)) (rowInit W inp t) with hr
  have hrp := rowProds_eq W inp t (pointerStarts.getD t 0)
  rw [← hr] at hrp
  obtain ⟨Y, hY⟩ := foldl_push_prefix rowBaseStep rowBaseStep_prefix
    (tableBlocks inp.ch t inp.eq0 (some inp.jump)) r.2.1
  have hterms : rt.prods.terms = (tableBlocks inp.ch t inp.eq0 (some inp.jump)).foldl rowBaseStep r.2.1 := by
    rw [hrt]; simp only; rw [foldl_fold_terms, hrp]
  have hct : rt.columnTerms = r.2.1.size := by rw [hrt]; simp only; rw [hrp]
  rw [baseAt_eq, hct, hterms]
  have hsplit := termsVal_split rt.prods.at _ _ _ hY
  rw [termsVal_foldl_blocks] at hsplit
  congr 1
  linear_combination -hsplit

/-! ## The payload -/

/-- The payload forms' value at `col`: the ungated form, and each gated form times its gate. -/
def payloadVal (col : ℕ → E) (fs : Form × List (ℕ × Form)) : E :=
  fs.1.evaluate col + (fs.2.map fun gf ↦ col gf.1 * gf.2.evaluate col).sum

/-- **The verifier's payload** at a row's values `col`: `η_mem·memory + η_bc·R_bc`. -/
def payloadAt (ch : LinkChallenges) (links : Links) (muT : List E) (col : ℕ → E) : E :=
  ch.etaMem * sumE ((links.memory.zip muT).map fun am ↦ am.2 * (am.1.gate.map col).getD 1 *
      (ch.gammaMem.getD 0 0 * am.1.address.evaluate col + ch.gammaMem.getD 3 0 +
        ch.gammaMem.getD 1 0 * am.1.value.evaluate col)) +
    ch.etaBc * (ch.slot.getD 1 0 * col links.bytecodeLink.pc + ch.slot.getD 2 0 +
      ch.slot.getD 3 0 * gpow links.bytecodeLink.opcode +
      sumE (links.bytecodeLink.operands.map fun so ↦
        ch.slot.getD (so.1.headD 0) 0 * so.2.evaluate col))

theorem sum_blockVal_tableBlocks (ev : ℕ → E) (ch : LinkChallenges) (t : ℕ) (scale : E)
    (jump : List E) :
    ((tableBlocks ch t scale (some jump)).map (blockVal ev)).sum =
      ev 0 * scale * payloadVal (fun c ↦ ev (3 + c))
          (payloadForms ch (tables.getD t default).links (ch.mu.getD t [])) +
        if 0 < (tables.getD t default).nConstraints then
          ev 2 * (jumpConstraintForm jump).evaluate (fun c ↦ ev (3 + c))
        else 0 := by
  unfold tableBlocks payloadVal
  dsimp only
  set u := (payloadForms ch (tables.getD t default).links (ch.mu.getD t [])).1
  set gs := (payloadForms ch (tables.getD t default).links (ch.mu.getD t [])).2
  simp only [List.map_cons, List.map_append, List.map_map, List.sum_cons, List.sum_append]
  have hg : ((gs.map ((blockVal ev) ∘ fun x : ℕ × Form ↦ (⟨false, some x.1,
      ({} : Form).addScaled x.2 scale⟩ : Block)))).sum =
      ev 0 * scale * (gs.map fun gf ↦ ev (3 + gf.1) * gf.2.evaluate fun c ↦ ev (3 + c)).sum := by
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun gf _ ↦ ?_)
    simp [blockVal, evaluate_addScaled, evaluate_empty]
    ring
  rw [hg]
  split_ifs with hc
  · simp [blockVal, evaluate_addScaled, evaluate_empty]
    ring
  · simp [blockVal, evaluate_addScaled, evaluate_empty]
    ring

/-! ## The gates -/

theorem tailRow_linkGates_spec (links : Links) :
    (linkGates links).Nodup ∧ ∀ a ∈ links.memory, ∀ g, a.gate = some g → g ∈ linkGates links := by
  unfold linkGates
  suffices h : ∀ (L : List Access) (gs : List ℕ), gs.Nodup →
      let r := L.foldl (fun gs a ↦ match a.gate with
        | some g => if gs.contains g then gs else gs ++ [g]
        | none => gs) gs
      r.Nodup ∧ (∀ g ∈ gs, g ∈ r) ∧ ∀ a ∈ L, ∀ g, a.gate = some g → g ∈ r by
    obtain ⟨h1, -, h3⟩ := h links.memory [] List.nodup_nil
    exact ⟨h1, h3⟩
  intro L
  induction L with
  | nil => intro gs hgs; exact ⟨hgs, fun g hg ↦ hg, fun a ha ↦ absurd ha List.not_mem_nil⟩
  | cons a L ih =>
    intro gs hgs
    simp only [List.foldl_cons]
    set gs' := (match a.gate with
      | some g => if gs.contains g then gs else gs ++ [g]
      | none => gs) with hgs'
    have hnd : gs'.Nodup ∧ (∀ g ∈ gs, g ∈ gs') ∧ ∀ g, a.gate = some g → g ∈ gs' := by
      rw [hgs']
      rcases hga : a.gate with _ | g
      · exact ⟨hgs, fun g hg ↦ hg, fun g h ↦ by cases h⟩
      · simp only
        split_ifs with hc
        · refine ⟨hgs, fun g hg ↦ hg, fun g' h ↦ ?_⟩
          cases h; simpa using hc
        · refine ⟨List.nodup_append.mpr ⟨hgs, by simp, ?_⟩, fun g hg ↦ by simp [hg], fun g' h ↦ ?_⟩
          · intro x hx y hy
            simp only [List.mem_singleton] at hy
            subst hy
            intro hxy; subst hxy
            exact hc (by simpa using hx)
          · cases h; simp
    obtain ⟨i1, i2, i3⟩ := ih gs' hnd.1
    refine ⟨i1, fun g hg ↦ i2 g (hnd.2.1 g hg), fun a' ha' g hg ↦ ?_⟩
    rcases List.mem_cons.mp ha' with rfl | ha'
    · exact i2 g (hnd.2.2 g hg)
    · exact i3 a' ha' g hg

theorem foldl_inv_add {α β : Type} (f : β → α → β) (P : β → Prop) (V : β → E) (δ : α → E)
    (Q : α → Prop) (hf : ∀ b a, Q a → P b → P (f b a) ∧ V (f b a) = V b + δ a) :
    ∀ (L : List α) (b : β), (∀ a ∈ L, Q a) → P b → V (L.foldl f b) = V b + (L.map δ).sum
  | [], b, _, _ => by simp
  | a :: L, b, hQ, hP => by
    obtain ⟨h1, h2⟩ := hf b a (hQ a List.mem_cons_self) hP
    rw [List.foldl_cons, foldl_inv_add f P V δ Q hf L _ (fun x hx ↦ hQ x (List.mem_cons_of_mem _ hx)) h1,
      h2, List.map_cons, List.sum_cons]
    ring

theorem evaluate_foldl_ops (col : ℕ → E) (w : List ℕ → E) :
    ∀ (ops : List (List ℕ × Form)) (f : Form),
      (ops.foldl (fun f so ↦ f.addScaled so.2 (w so.1)) f).evaluate col =
        f.evaluate col + (ops.map fun so ↦ w so.1 * so.2.evaluate col).sum
  | [], f => by simp
  | so :: ops, f => by
    rw [List.foldl_cons, evaluate_foldl_ops col w ops, evaluate_addScaled, List.map_cons,
      List.sum_cons]
    ring

/-- `payloadForms`' step at one access. -/
def payStep (ch : LinkChallenges) (acc : Form × List (ℕ × Form)) (am : Access × E) :
    Form × List (ℕ × Form) :=
  let w := ch.etaMem * am.2
  let add := fun (f : Form) ↦
    ((f.addScaled am.1.address (w * ch.gammaMem.getD 0 0)).addScaled (Form.const 1)
      (w * ch.gammaMem.getD 3 0)).addScaled am.1.value (w * ch.gammaMem.getD 1 0)
  match am.1.gate with
  | none => (add acc.1, acc.2)
  | some g => (acc.1, acc.2.map fun gf ↦ if gf.1 = g then (gf.1, add gf.2) else (gf.1, gf.2))

/-- The ungated form before the operands. -/
def ungated0 (ch : LinkChallenges) (links : Links) : Form :=
  ⟨[([links.bytecodeLink.pc], ch.etaBc * ch.slot.getD 1 0),
    ([], ch.etaBc * ch.slot.getD 2 0 + ch.etaBc * ch.slot.getD 3 0 * gpow links.bytecodeLink.opcode)]⟩

theorem payloadForms_eq (ch : LinkChallenges) (links : Links) (mu : List E) :
    payloadForms ch links mu = (links.memory.zip mu).foldl (payStep ch)
      (links.bytecodeLink.operands.foldl
        (fun f so ↦ f.addScaled so.2 (ch.etaBc * ch.slot.getD (so.1.headD 0) 0)) (ungated0 ch links),
        (linkGates links).map fun g ↦ (g, ({} : Form))) := by
  unfold payloadForms
  rfl

/-- An access's committed part at `col`. -/
def accV (ch : LinkChallenges) (col : ℕ → E) (a : Access) : E :=
  ch.gammaMem.getD 0 0 * a.address.evaluate col + ch.gammaMem.getD 3 0 +
    ch.gammaMem.getD 1 0 * a.value.evaluate col

theorem evaluate_add3 (ch : LinkChallenges) (col : ℕ → E) (f : Form) (a : Access) (w : E) :
    (((f.addScaled a.address (w * ch.gammaMem.getD 0 0)).addScaled (Form.const 1)
      (w * ch.gammaMem.getD 3 0)).addScaled a.value (w * ch.gammaMem.getD 1 0)).evaluate col =
      f.evaluate col + w * accV ch col a := by
  simp only [evaluate_addScaled, evaluate_const, accV]
  ring

theorem payStep_spec (ch : LinkChallenges) (links : Links) (col : ℕ → E)
    (fs : Form × List (ℕ × Form)) (am : Access × E) (ha : am.1 ∈ links.memory)
    (hP : fs.2.map (·.1) = linkGates links) :
    (payStep ch fs am).2.map (·.1) = linkGates links ∧
      payloadVal col (payStep ch fs am) =
        payloadVal col fs + am.2 * (am.1.gate.map col).getD 1 * (ch.etaMem * accV ch col am.1) := by
  obtain ⟨hnd, hmem⟩ := tailRow_linkGates_spec links
  obtain ⟨a, m⟩ := am
  obtain ⟨u, gs⟩ := fs
  simp only at hP ha
  rcases hga : a.gate with _ | g
  · have e : payStep ch (u, gs) (a, m) = (((u.addScaled a.address (ch.etaMem * m * ch.gammaMem.getD 0 0)).addScaled
        (Form.const 1) (ch.etaMem * m * ch.gammaMem.getD 3 0)).addScaled a.value
        (ch.etaMem * m * ch.gammaMem.getD 1 0), gs) := by
      simp only [payStep, hga]
    rw [e]
    refine ⟨hP, ?_⟩
    simp only [payloadVal, evaluate_add3, Option.map_none, Option.getD_none]
    ring
  · have hg : g ∈ gs.map (·.1) := hP ▸ hmem a ha g hga
    have e : payStep ch (u, gs) (a, m) = (u, gs.map fun gf ↦ if gf.1 = g then
        (gf.1, ((gf.2.addScaled a.address (ch.etaMem * m * ch.gammaMem.getD 0 0)).addScaled
        (Form.const 1) (ch.etaMem * m * ch.gammaMem.getD 3 0)).addScaled a.value
        (ch.etaMem * m * ch.gammaMem.getD 1 0)) else (gf.1, gf.2)) := by
      simp only [payStep, hga]
    rw [e]
    refine ⟨?_, ?_⟩
    · rw [List.map_map, ← hP]
      refine List.map_congr_left fun x _ ↦ ?_
      simp only [Function.comp]
      split_ifs <;> rfl
    · unfold payloadVal
      dsimp only
      rw [List.map_map, List.map_congr_left (g := fun x : ℕ × Form ↦ col x.1 * x.2.evaluate col +
        if x.1 = g then col g * (ch.etaMem * m * accV ch col a) else 0) ?_, List.sum_map_add,
        sum_ite_key_one _ g gs (hP ▸ hnd) (by simpa using hg)]
      · simp only [Option.map_some, Option.getD_some]
        ring
      · intro x _
        simp only [Function.comp]
        split_ifs with h
        · simp only [evaluate_add3, h]; ring
        · simp

theorem ungated0_evaluate (ch : LinkChallenges) (links : Links) (col : ℕ → E) :
    (ungated0 ch links).evaluate col = ch.etaBc * ch.slot.getD 1 0 * col links.bytecodeLink.pc +
      (ch.etaBc * ch.slot.getD 2 0 + ch.etaBc * ch.slot.getD 3 0 * gpow links.bytecodeLink.opcode) := by
  rw [ungated0, evaluate_eq_sum]
  simp only [tailRowMono, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.sum_cons,
    List.sum_nil]
  ring

/-- **The payload forms' value is the verifier's payload.** -/
theorem payloadVal_payloadForms (ch : LinkChallenges) (links : Links) (mu : List E) (col : ℕ → E) :
    payloadVal col (payloadForms ch links mu) = payloadAt ch links mu col := by
  rw [payloadForms_eq, foldl_inv_add (payStep ch) (fun fs ↦ fs.2.map (·.1) = linkGates links)
    (payloadVal col) (fun am ↦ am.2 * (am.1.gate.map col).getD 1 * (ch.etaMem * accV ch col am.1))
    (fun am ↦ am.1 ∈ links.memory) (fun fs am ha hP ↦ payStep_spec ch links col fs am ha hP) _ _
    (fun am ham ↦ (List.of_mem_zip ham).1) (by simp [Function.comp_def])]
  have h0 : ∀ L : List ℕ, (L.map fun g ↦ col g * ({} : Form).evaluate col).sum = 0 := by
    intro L; simp [evaluate_empty]
  simp only [payloadVal, List.map_map, Function.comp_def, h0, add_zero]
  rw [evaluate_foldl_ops col (fun slots ↦ ch.etaBc * ch.slot.getD (slots.headD 0) 0),
    ungated0_evaluate]
  unfold payloadAt
  simp only [sumE_eq_sum]
  have e1 : (links.bytecodeLink.operands.map fun so ↦
      ch.etaBc * ch.slot.getD (so.1.headD 0) 0 * so.2.evaluate col).sum =
      ch.etaBc * (links.bytecodeLink.operands.map fun so ↦
        ch.slot.getD (so.1.headD 0) 0 * so.2.evaluate col).sum := by
    rw [← List.sum_map_mul_left]; simp only [mul_assoc]
  have e2 : ((links.memory.zip mu).map fun am ↦
      am.2 * (am.1.gate.map col).getD 1 * (ch.etaMem * accV ch col am.1)).sum =
      ch.etaMem * ((links.memory.zip mu).map fun am ↦ am.2 * (am.1.gate.map col).getD 1 *
        (ch.gammaMem.getD 0 0 * am.1.address.evaluate col + ch.gammaMem.getD 3 0 +
          ch.gammaMem.getD 1 0 * am.1.value.evaluate col)).sum := by
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun am _ ↦ ?_)
    simp only [accV]; ring
  rw [e1, e2]
  ring

/-! ## `JUMP`'s identities -/

theorem mul_col_min_max (col : ℕ → E) (k : E) (a b : ℕ) :
    k * col (min a b) * col (max a b) = k * col a * col b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h]; ring

/-- **`JUMP`'s identity form is its identities weighed**, the columns it reads agreeing. -/
theorem jump_evaluate (jump values : List E) (col : ℕ → E) (hj : jump.length = 4)
    (hv : ∀ c ∈ jumpCols, values.getD c 0 = col c) :
    (jumpConstraintForm jump).evaluate col = sumE (List.zipWith (· * ·) jump (jumpConstraints values)) := by
  obtain ⟨k0, k1, k2, k3, rfl⟩ : ∃ k0 k1 k2 k3, jump = [k0, k1, k2, k3] := by
    match jump, hj with
    | [k0, k1, k2, k3], _ => exact ⟨k0, k1, k2, k3, rfl⟩
  have h : ∀ name, colIndex jumpColumns name ∈ jumpCols →
      values.getD (colIndex jumpColumns name) 0 = col (colIndex jumpColumns name) := fun _ hn ↦ hv _ hn
  unfold jumpConstraints
  simp only [h "b" (by simp [jumpCols]), h "v_cond" (by simp [jumpCols]), h "w" (by simp [jumpCols]),
    h "pc_next" (by simp [jumpCols]), h "v_pc" (by simp [jumpCols]), h "pc" (by simp [jumpCols]),
    h "fp_next" (by simp [jumpCols]), h "v_fp" (by simp [jumpCols]), h "fp" (by simp [jumpCols])]
  rw [evaluate_eq_sum]
  simp only [jumpConstraintForm, tailRowMono, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.prod_cons, List.prod_nil, List.getD_cons_zero,
    List.getD_cons_succ, List.zipWith_cons_cons, List.zipWith_nil_left, sumE_eq_sum, mul_one]
  simp only [← mul_assoc, mul_col_min_max]
  ring

/-! ## A bound table's base terms -/

/-- **A bound table's base terms**: `ω·eq(0, r)` times its payload, and `eq(τ, ·)` times `JUMP`'s
identity form, at its bound tables, times its corner. -/
theorem baseAt_eq_payload {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (x : LinkProverPre) (chi : List E)
    (hchi : chi.length = linkNRows W) {t : ℕ} (ht : t < nTables) :
    let rt := (chi.foldl rowFold (linkRowStart W x)).getD t default
    let inp := linkRowInputs W x
    baseAt rt = rt.corner * (rt.prods.at 0 * inp.eq0 *
        payloadAt inp.ch (tables.getD t default).links (inp.ch.mu.getD t [])
          (fun c ↦ rt.prods.at (3 + c)) +
      if 0 < (tables.getD t default).nConstraints then
        rt.prods.at 2 * (jumpConstraintForm inp.jump).evaluate (fun c ↦ rt.prods.at (3 + c))
      else 0) := by
  intro rt inp
  rw [baseAt_blocks hW x chi hchi ht, sum_blockVal_tableBlocks, payloadVal_payloadForms]

end LeanVM.Prover.Complete

end
