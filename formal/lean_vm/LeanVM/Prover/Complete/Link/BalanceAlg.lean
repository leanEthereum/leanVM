/-
  LeanVM.Prover.Complete.Link.BalanceAlg

  The algebra of the index side's balance on one row: the payload's forms, the word reads and the
  program side's slot weights as sums over the row's accesses.
-/

module

public import LeanVM.Prover.Complete.Link.IndexSplit
import LeanVM.Protocol.Tables

/-!
# One row's balance, algebraically

A table's row contributes to the index side's balance (`balanceProds`) through its accesses'
weights at their cells (`w_mem` against `Y`), its word reads (`v_word` against `words`), its weight
at its instruction (`w_bc` against `X_ω`, `w_fp` against `P_fp`) and its payload. Each of these is a
fold over the table's `Links`; here each is a sum over the accesses:

* `Form.evaluate_addScaled`: a form's value is linear;
* `payload_sum`: the payload's blocks (`payloadForms`) sum to `η_bc·R_bc` plus each access's
  committed part under `η_mem·μ·gate`;
* `wordReads_sum`: the word reads (`wordReads`) sum to each `Read.word`'s value;
* `slotSum_omega`, `slotSum_pc`, `slotSum_frame`: the program side's weights (`tableSlotWeights`)
  against an instruction's slots.

`rowBal_eq_zero`: when every access reads its cell (`gate·Y = ` its own side) and the program link
holds (the `pc`, the opcode, the operand equations), the row's balance is zero, in characteristic
two.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Prover

/-! ## Forms -/

/-- A monomial's value. -/
def monoVal (c : ℕ → E) (m : List ℕ) : E := m.foldl (fun acc i ↦ acc * c i) 1

theorem foldl_mul_init (c : ℕ → E) :
    ∀ (m : List ℕ) (a : E), m.foldl (fun acc i ↦ acc * c i) a = a * monoVal c m
  | [], a => by simp [monoVal]
  | i :: m, a => by
    simp only [List.foldl_cons, monoVal]
    rw [foldl_mul_init c m, foldl_mul_init c m (1 * c i)]
    ring

/-- The value of a list of terms. -/
def formTermsVal (c : ℕ → E) (L : List (List ℕ × E)) : E := (L.map fun t ↦ t.2 * monoVal c t.1).sum

theorem Form.evaluate_eq (f : Form) (c : ℕ → E) : f.evaluate c = formTermsVal c f.terms := by
  simp only [Form.evaluate, LeanVM.Protocol.Tables.sumE_eq, foldl_mul_init, formTermsVal]

theorem termsVal_addTerm (c : ℕ → E) : ∀ (L : List (List ℕ × E)) (m : List ℕ) (w : E),
    formTermsVal c (addTerm L m w) = formTermsVal c L + w * monoVal c m
  | [], m, w => by simp [addTerm, formTermsVal]
  | (m', c') :: rest, m, w => by
    unfold addTerm
    split_ifs with h
    · subst h; simp only [formTermsVal, List.map_cons, List.sum_cons]; ring
    · have := termsVal_addTerm c rest m w
      simp only [formTermsVal, List.map_cons, List.sum_cons] at this ⊢
      rw [this]; ring

theorem Form.evaluate_addScaled (f g : Form) (w : E) (c : ℕ → E) :
    (f.addScaled g w).evaluate c = f.evaluate c + w * g.evaluate c := by
  simp only [Form.addScaled, Form.evaluate_eq]
  generalize f.terms = L
  induction g.terms generalizing L with
  | nil => simp [formTermsVal]
  | cons t ts ih =>
    rw [List.foldl_cons, ih, termsVal_addTerm]
    simp only [formTermsVal, List.map_cons, List.sum_cons]
    ring

@[simp] theorem Form.evaluate_empty (c : ℕ → E) : ({} : Form).evaluate c = 0 := by
  simp [Form.evaluate, sumE]

theorem Form.evaluate_const (v : E) (c : ℕ → E) : (Form.const v).evaluate c = v := by
  simp [Form.evaluate, Form.const, sumE]

/-! ## The payload -/

/-- An access's gate on a row: its gating column, `1` for none. -/
def gateOf (col : ℕ → E) (a : Access) : E := (a.gate.map col).getD 1

/-- An access's committed part, `γ_addr·address + γ_pres + γ_word·value`. -/
def committedOf (ch : LinkChallenges) (col : ℕ → E) (a : Access) : E :=
  ch.gammaMem.getD 0 0 * a.address.evaluate col + ch.gammaMem.getD 3 0 +
    ch.gammaMem.getD 1 0 * a.value.evaluate col

/-- The program link's form on a row: `α_1·pc + α_2 + α_3·g^opcode + Σ α_{slots[0]}·form`. -/
def bcFormVal (ch : LinkChallenges) (bc : BytecodeLink) (col : ℕ → E) : E :=
  ch.slot.getD 1 0 * col bc.pc + ch.slot.getD 2 0 + ch.slot.getD 3 0 * gpow bc.opcode +
    (bc.operands.map fun op ↦ ch.slot.getD (op.1.headD 0) 0 * op.2.evaluate col).sum

/-- The value of the gated forms. -/
def gatedVal (wt col : ℕ → E) (L : List (ℕ × Form)) : E :=
  (L.map fun p ↦ wt p.1 * p.2.evaluate col).sum

theorem gatedVal_update (wt col : ℕ → E) (g : ℕ) (h : Form → Form) (δ : E)
    (hh : ∀ f, (h f).evaluate col = f.evaluate col + δ) :
    ∀ L : List (ℕ × Form), (L.map Prod.fst).Nodup →
      gatedVal wt col (L.map fun p ↦ if p.1 = g then (p.1, h p.2) else (p.1, p.2)) =
        gatedVal wt col L + (if g ∈ L.map Prod.fst then wt g * δ else 0)
  | [], _ => by simp [gatedVal]
  | (g', f) :: L, hnd => by
    have hnd' : (L.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
    have ih := gatedVal_update wt col g h δ hh L hnd'
    simp only [gatedVal, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    by_cases hg : g' = g
    · subst hg
      have hn : g' ∉ L.map Prod.fst := (List.nodup_cons.mp hnd).1
      simp [hn, hh]; ring
    · have hm : (g ∈ g' :: L.map Prod.fst) ↔ g ∈ L.map Prod.fst := by
        simp only [List.mem_cons, or_iff_right (Ne.symm hg)]
      simp only [hg, ↓reduceIte, hm]; ring

theorem map_fst_update (g : ℕ) (h : Form → Form) (L : List (ℕ × Form)) :
    (L.map fun p ↦ if p.1 = g then (p.1, h p.2) else (p.1, p.2)).map Prod.fst = L.map Prod.fst := by
  induction L with
  | nil => rfl
  | cons p L ih => simp only [List.map_cons, ih]; split <;> rfl

/-- The gates' list collects each access's gate once. -/
theorem linkGates_spec : ∀ (L : List Access) (gs : List ℕ), gs.Nodup →
    (L.foldl (fun gs a ↦ match a.gate with
      | some g => if gs.contains g then gs else gs ++ [g]
      | none => gs) gs).Nodup ∧
    (∀ g ∈ gs, g ∈ L.foldl (fun gs a ↦ match a.gate with
      | some g => if gs.contains g then gs else gs ++ [g]
      | none => gs) gs) ∧
    ∀ a ∈ L, ∀ g, a.gate = some g → g ∈ L.foldl (fun gs a ↦ match a.gate with
      | some g => if gs.contains g then gs else gs ++ [g]
      | none => gs) gs
  | [], gs, h => ⟨h, fun _ hg ↦ hg, fun _ ha ↦ absurd ha (by simp)⟩
  | a :: L, gs, h => by
    simp only [List.foldl_cons]
    set gs' := (match a.gate with
      | some g => if gs.contains g then gs else gs ++ [g]
      | none => gs) with hgs'
    have hnd' : gs'.Nodup ∧ (∀ g ∈ gs, g ∈ gs') ∧ ∀ g, a.gate = some g → g ∈ gs' := by
      rw [hgs']
      rcases hag : a.gate with _ | g
      · simp [h]
      · simp only [Option.some.injEq, forall_eq']
        by_cases hc : gs.contains g
        · simp only [hc, ↓reduceIte]
          exact ⟨h, fun _ x ↦ x, by simpa using hc⟩
        · simp only [hc, Bool.false_eq_true, ↓reduceIte]
          refine ⟨List.Nodup.append h (List.nodup_singleton g) ?_, fun _ x ↦ List.mem_append_left _ x,
            by simp⟩
          simp only [List.disjoint_singleton]
          simpa using hc
    obtain ⟨h1, h2, h3⟩ := linkGates_spec L gs' hnd'.1
    refine ⟨h1, fun g hg ↦ h2 g (hnd'.2.1 g hg), fun b hb g hbg ↦ ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h2 g (hnd'.2.2 g hbg)
    · exact h3 b hb g hbg

theorem evaluate_addCommitted (ch : LinkChallenges) (col : ℕ → E) (a : Access) (w : E) (f : Form) :
    (((f.addScaled a.address (w * ch.gammaMem.getD 0 0)).addScaled (Form.const 1)
        (w * ch.gammaMem.getD 3 0)).addScaled a.value (w * ch.gammaMem.getD 1 0)).evaluate col =
      f.evaluate col + w * committedOf ch col a := by
  simp only [Form.evaluate_addScaled, Form.evaluate_const, committedOf]
  ring

/-- One access's step of `payloadForms`' fold. -/
def payloadStep (ch : LinkChallenges) (acc : Form × List (ℕ × Form)) (am : Access × E) :
    Form × List (ℕ × Form) :=
  let (access, m) := am
  let w := ch.etaMem * m
  let add := fun (f : Form) ↦
    ((f.addScaled access.address (w * ch.gammaMem.getD 0 0)).addScaled (Form.const 1)
      (w * ch.gammaMem.getD 3 0)).addScaled access.value (w * ch.gammaMem.getD 1 0)
  match access.gate with
  | none => (add acc.1, acc.2)
  | some g => (acc.1, acc.2.map fun (g', f) ↦ if g' = g then (g', add f) else (g', f))

/-- `add` of an access, as `payloadStep` applies it. -/
def addCommitted (ch : LinkChallenges) (a : Access) (m : E) (f : Form) : Form :=
  ((f.addScaled a.address (ch.etaMem * m * ch.gammaMem.getD 0 0)).addScaled (Form.const 1)
    (ch.etaMem * m * ch.gammaMem.getD 3 0)).addScaled a.value (ch.etaMem * m * ch.gammaMem.getD 1 0)

theorem payloadStep_none (ch : LinkChallenges) (acc : Form × List (ℕ × Form)) {a : Access} (m : E)
    (h : a.gate = none) : payloadStep ch acc (a, m) = (addCommitted ch a m acc.1, acc.2) := by
  simp only [payloadStep, h, addCommitted]

theorem payloadStep_some (ch : LinkChallenges) (acc : Form × List (ℕ × Form)) {a : Access} (m : E)
    {g : ℕ} (h : a.gate = some g) : payloadStep ch acc (a, m) =
      (acc.1, acc.2.map fun p ↦ if p.1 = g then (p.1, addCommitted ch a m p.2) else (p.1, p.2)) := by
  simp only [payloadStep, h, addCommitted]

theorem payloadFold_sum (ch : LinkChallenges) (col : ℕ → E) :
    ∀ (L : List (Access × E)) (acc : Form × List (ℕ × Form)), (acc.2.map Prod.fst).Nodup →
      (∀ p ∈ L, ∀ g, p.1.gate = some g → g ∈ acc.2.map Prod.fst) →
      (L.foldl (payloadStep ch) acc).1.evaluate col + gatedVal col col (L.foldl (payloadStep ch) acc).2 =
        acc.1.evaluate col + gatedVal col col acc.2 +
          (L.map fun p ↦ ch.etaMem * p.2 * gateOf col p.1 * committedOf ch col p.1).sum
  | [], acc, _, _ => by simp
  | (a, m) :: L, acc, hnd, hg => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rcases hag : a.gate with _ | g
    · rw [payloadStep_none ch acc m hag]
      rw [payloadFold_sum ch col L (addCommitted ch a m acc.1, acc.2) hnd fun p hp ↦ hg p (List.mem_cons_of_mem _ hp),
        addCommitted, evaluate_addCommitted, gateOf, hag]
      simp only [Option.map_none, Option.getD_none, mul_one]
      ring
    · rw [payloadStep_some ch acc m hag]
      have hnd' := hnd
      rw [← map_fst_update g (addCommitted ch a m) acc.2] at hnd'
      rw [payloadFold_sum ch col L (acc.1, _) hnd' fun p hp g' hg' ↦ by
        rw [map_fst_update]; exact hg p (List.mem_cons_of_mem _ hp) g' hg']
      have hgm : g ∈ acc.2.map Prod.fst := hg (a, m) List.mem_cons_self g hag
      have hu := gatedVal_update col col g (addCommitted ch a m) _
        (fun f ↦ evaluate_addCommitted ch col a (ch.etaMem * m) f) acc.2 hnd
      simp only [hgm, ↓reduceIte] at hu
      simp only
      rw [hu, gateOf, hag]
      simp only [Option.map_some, Option.getD_some]
      ring

theorem gatedVal_nil_forms (wt col : ℕ → E) (gs : List ℕ) :
    gatedVal wt col (gs.map fun g ↦ (g, ({} : Form))) = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [gatedVal, List.map_cons, List.sum_cons] at ih ⊢; rw [ih]; simp

theorem operands_eval (ch : LinkChallenges) (col : ℕ → E) :
    ∀ (ops : List (List ℕ × Form)) (f : Form),
      (ops.foldl (fun f (op : List ℕ × Form) ↦
        f.addScaled op.2 (ch.etaBc * ch.slot.getD (op.1.headD 0) 0)) f).evaluate col =
        f.evaluate col + ch.etaBc *
          (ops.map fun op ↦ ch.slot.getD (op.1.headD 0) 0 * op.2.evaluate col).sum
  | [], f => by simp
  | op :: ops, f => by
    rw [List.foldl_cons, operands_eval ch col ops, Form.evaluate_addScaled]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- The access sums the row's balance is made of. -/
def accSum (L : List (Access × E)) (F : Access → E) : E := (L.map fun p ↦ p.2 * F p.1).sum

theorem evaluate_two (a : ℕ) (c1 c2 : E) (col : ℕ → E) :
    (⟨[([a], c1), ([], c2)]⟩ : Form).evaluate col = c1 * col a + c2 := by
  simp [Form.evaluate, sumE]

/-- **The payload's forms** sum to the program link's and each access's committed part. -/
theorem payloadForms_val (ch : LinkChallenges) (links : Links) (mu : List E) (col : ℕ → E) :
    (payloadForms ch links mu).1.evaluate col + gatedVal col col (payloadForms ch links mu).2 =
      ch.etaBc * bcFormVal ch links.bytecodeLink col +
        ch.etaMem * accSum (links.memory.zip mu) fun a ↦ gateOf col a * committedOf ch col a := by
  have hgates := linkGates_spec links.memory [] List.nodup_nil
  have h : payloadForms ch links mu = (links.memory.zip mu).foldl (payloadStep ch)
      (links.bytecodeLink.operands.foldl (fun f (op : List ℕ × Form) ↦
        f.addScaled op.2 (ch.etaBc * ch.slot.getD (op.1.headD 0) 0))
        ⟨[([links.bytecodeLink.pc], ch.etaBc * ch.slot.getD 1 0),
          ([], ch.etaBc * ch.slot.getD 2 0 + ch.etaBc * ch.slot.getD 3 0 *
            gpow links.bytecodeLink.opcode)]⟩,
        (linkGates links).map fun g ↦ (g, ({} : Form))) := rfl
  have hfst : ((linkGates links).map fun g ↦ (g, ({} : Form))).map Prod.fst = linkGates links := by
    simp [Function.comp_def]
  rw [h, payloadFold_sum ch col _ _ (by rw [hfst]; exact hgates.1) (fun p hp g hg ↦ by
      rw [hfst]; exact hgates.2.2 p.1 (List.of_mem_zip hp).1 g hg)]
  simp only [gatedVal_nil_forms, add_zero, operands_eval, accSum, bcFormVal, evaluate_two]
  rw [show (links.memory.zip mu).map (fun p ↦ ch.etaMem * p.2 * gateOf col p.1 * committedOf ch col p.1)
      = (links.memory.zip mu).map (fun p ↦ ch.etaMem * (p.2 * (gateOf col p.1 * committedOf ch col p.1)))
      from List.map_congr_left fun p _ ↦ by ring, List.sum_map_mul_left]
  ring

/-! ## The word reads -/

/-- One read's step of `wordReads`' fold. -/
def wordStep (weight m : E) (out : List (ℕ × Form)) (read : Read) : List (ℕ × Form) :=
  match read with
  | .word p scale =>
    if out.any (·.1 = p) then out.map fun (p', f) ↦ (p', if p' = p then f.addScaled scale (weight * m) else f)
    else out ++ [(p, ({} : Form).addScaled scale (weight * m))]
  | _ => out

/-- A read's word term, at the cells `Z` its pointer names. -/
def readWordVal (Z col : ℕ → E) : Read → E
  | .word p scale => Z p * scale.evaluate col
  | _ => 0

theorem wordStep_val (weight m : E) (Z col : ℕ → E) (r : Read) (out : List (ℕ × Form))
    (hnd : (out.map Prod.fst).Nodup) :
    ((wordStep weight m out r).map Prod.fst).Nodup ∧
      gatedVal Z col (wordStep weight m out r) = gatedVal Z col out + weight * m * readWordVal Z col r := by
  cases r with
  | word p scale =>
    simp only [wordStep, readWordVal]
    by_cases hany : out.any (·.1 = p)
    · simp only [hany, ↓reduceIte]
      have hmap : (out.map fun x ↦ match x with
          | (p', f) => (p', if p' = p then f.addScaled scale (weight * m) else f)) =
          out.map fun x ↦ if x.1 = p then (x.1, x.2.addScaled scale (weight * m)) else (x.1, x.2) :=
        List.map_congr_left fun x _ ↦ by obtain ⟨p', f⟩ := x; dsimp only; split_ifs <;> rfl
      have hp : p ∈ out.map Prod.fst := by
        obtain ⟨x, hx, hxp⟩ := List.any_eq_true.mp hany
        exact List.mem_map.mpr ⟨x, hx, of_decide_eq_true hxp⟩
      rw [hmap, map_fst_update p (fun f ↦ f.addScaled scale (weight * m))]
      refine ⟨hnd, ?_⟩
      rw [gatedVal_update Z col p (fun f ↦ f.addScaled scale (weight * m)) (weight * m * scale.evaluate col)
        (fun f ↦ Form.evaluate_addScaled f scale _ col) out hnd]
      simp only [hp, ↓reduceIte]
      ring
    · simp only [hany, Bool.false_eq_true, ↓reduceIte]
      have hp : p ∉ out.map Prod.fst := fun hp ↦ by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
        exact hany (List.any_eq_true.mpr ⟨x, hx, decide_eq_true rfl⟩)
      refine ⟨?_, ?_⟩
      · rw [List.map_append]
        exact hnd.append (List.nodup_singleton _) (by simpa using hp)
      · simp only [gatedVal, List.map_append, List.sum_append, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Form.evaluate_addScaled, Form.evaluate_empty]
        ring
  | slot => exact ⟨hnd, by simp [wordStep, readWordVal]⟩
  | frame => exact ⟨hnd, by simp [wordStep, readWordVal]⟩
  | pc => exact ⟨hnd, by simp [wordStep, readWordVal]⟩

theorem wordReads_fold (weight m : E) (Z col : ℕ → E) :
    ∀ (rs : List Read) (out : List (ℕ × Form)), (out.map Prod.fst).Nodup →
      ((rs.foldl (wordStep weight m) out).map Prod.fst).Nodup ∧
      gatedVal Z col (rs.foldl (wordStep weight m) out) =
        gatedVal Z col out + weight * m * (rs.map (readWordVal Z col)).sum
  | [], out, hnd => ⟨hnd, by simp⟩
  | r :: rs, out, hnd => by
    obtain ⟨h1, h2⟩ := wordStep_val weight m Z col r out hnd
    obtain ⟨h3, h4⟩ := wordReads_fold weight m Z col rs _ h1
    refine ⟨h3, ?_⟩
    rw [List.foldl_cons, h4, h2]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem wordReads_acc (weight : E) (Z col : ℕ → E) :
    ∀ (L : List (Access × E)) (out : List (ℕ × Form)), (out.map Prod.fst).Nodup →
      ((L.foldl (fun out am ↦ am.1.reads.foldl (wordStep weight am.2) out) out).map Prod.fst).Nodup ∧
      gatedVal Z col (L.foldl (fun out am ↦ am.1.reads.foldl (wordStep weight am.2) out) out) =
        gatedVal Z col out + weight * accSum L fun a ↦ (a.reads.map (readWordVal Z col)).sum
  | [], out, hnd => ⟨hnd, by simp [accSum]⟩
  | (a, m) :: L, out, hnd => by
    obtain ⟨h1, h2⟩ := wordReads_fold weight m Z col a.reads out hnd
    obtain ⟨h3, h4⟩ := wordReads_acc weight Z col L _ h1
    refine ⟨h3, ?_⟩
    rw [List.foldl_cons, h4, h2]
    simp only [accSum, List.map_cons, List.sum_cons]
    ring

/-- **The word reads** sum to each `Read.word`'s value at its cell. -/
theorem wordReads_val (links : Links) (mu : List E) (weight : E) (Z col : ℕ → E) :
    gatedVal Z col (wordReads links mu weight) =
      weight * accSum (links.memory.zip mu) fun a ↦ (a.reads.map (readWordVal Z col)).sum := by
  have h : wordReads links mu weight = (links.memory.zip mu).foldl
      (fun out am ↦ am.1.reads.foldl (wordStep weight am.2) out) [] := rfl
  rw [h, (wordReads_acc weight Z col _ [] List.nodup_nil).2]
  simp [gatedVal]

/-! ## The program side's slot weights -/

/-- An instruction's slots `lo, …, lo + n − 1` under the weights `w`, against `F`. -/
def slotSum (w : List E) (lo n : ℕ) (F : ℕ → E) : E :=
  sumE ((List.range n).map fun i ↦ w.getD (i + lo) 0 * F (i + lo))

theorem iteT {c : Prop} [Decidable c] (h : c) (a b : E) : (if c then a else b) = a := by simp [h]

theorem iteF {c : Prop} [Decidable c] (h : ¬ c) (a b : E) : (if c then a else b) = b := by simp [h]

theorem getD_set_eq (w : List E) {s : ℕ} (hs : s < w.length) (x : E) (i : ℕ) :
    (w.set s x).getD i 0 = if i = s then x else w.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = s
  · subst h; simp [hs]
  · simp [h, Ne.symm h]

theorem slotSum_set (w : List E) (lo : ℕ) (F : ℕ → E) {s : ℕ} (hs : s < w.length) (x : E) :
    ∀ n, slotSum (w.set s x) lo n F =
      slotSum w lo n F + if lo ≤ s ∧ s < lo + n then (x - w.getD s 0) * F s else 0
  | 0 => by
    simp only [slotSum, List.range_zero, List.map_nil]
    rw [iteF (by omega)]; simp
  | n + 1 => by
    have ih := slotSum_set w lo F hs x n
    simp only [slotSum, LeanVM.Protocol.Tables.sumE_eq, List.range_succ, List.map_append,
      List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at ih ⊢
    rw [ih, getD_set_eq w hs]
    by_cases h : n + lo = s
    · subst h
      rw [iteF (show ¬ (lo ≤ n + lo ∧ n + lo < lo + n) by omega),
        iteT (show lo ≤ n + lo ∧ n + lo < lo + (n + 1) by omega), iteT rfl]
      ring
    · rw [iteF h]
      by_cases h2 : lo ≤ s ∧ s < lo + n
      · rw [iteT h2, iteT (show lo ≤ s ∧ s < lo + (n + 1) by omega)]; ring
      · rw [iteF h2, iteF (show ¬ (lo ≤ s ∧ s < lo + (n + 1)) by omega)]; ring

theorem slotSum_addAtSlot (w : List E) (lo n : ℕ) (F : ℕ → E) {s : ℕ} (v : E) (hs : s < w.length) :
    slotSum (addAtSlot w s v) lo n F =
      slotSum w lo n F + if lo ≤ s ∧ s < lo + n then v * F s else 0 := by
  rw [addAtSlot, slotSum_set w lo F hs]
  split_ifs <;> ring

theorem length_addAtSlot (w : List E) (s : ℕ) (v : E) : (addAtSlot w s v).length = w.length := by
  simp [addAtSlot]

/-- A read's slots in range: a slot, `pc` read in slots `3 ..= 15`, a frame read in `4 ..= 15`. -/
def readSlotsOK : Read → Bool
  | .word _ _ => true
  | .slot s _ => 3 ≤ s && s < 16
  | .frame s _ => 4 ≤ s && s < 16
  | .pc s _ => 3 ≤ s && s < 16

/-- An access's frame and reads in range. -/
def accessSlotsOK (a : Access) : Bool :=
  (match a.frame with
    | some (s, _) => 4 ≤ s && s < 16
    | none => true) && a.reads.all readSlotsOK

/-- The program terms of a read (not a word read): `scale·BC_s`, `fp·scale·BC_s`,
`scale·g^σ·BC_s`. -/
def readProgVal (B : ℕ → E) (fp G : E) : Read → E
  | .word _ _ => 0
  | .slot s scale => scale * B s
  | .frame s scale => fp * (scale * B s)
  | .pc s scale => scale * (G * B s)

/-- A framed access's address term `g^e·fp·BC_s`. -/
def frameVal (B : ℕ → E) (fp : E) (a : Access) : E :=
  match a.frame with
  | some (s, e) => fp * (gpow e * B s)
  | none => 0

/-- The weights' value: `X_ω`'s slot sums and `fp·P_fp`. -/
def slotTotal (B : ℕ → E) (fp G : E) (acc : List E × List E × List E) : E :=
  slotSum acc.1 3 13 B + slotSum acc.2.1 3 13 (fun s ↦ G * B s) + fp * slotSum acc.2.2 4 12 B

/-- One read's step of `tableSlotWeights`' fold. -/
def slotReadStep (gamma : E × E) (m : E) (acc : List E × List E × List E) (read : Read) :
    List E × List E × List E :=
  match read with
  | .word _ _ => acc
  | .slot s scale => (addAtSlot acc.1 s (m * gamma.2 * scale), acc.2.1, acc.2.2)
  | .frame s scale => (acc.1, acc.2.1, addAtSlot acc.2.2 s (m * gamma.2 * scale))
  | .pc s scale => (acc.1, addAtSlot acc.2.1 s (m * gamma.2 * scale), acc.2.2)

/-- Three weight lists of `16` entries. -/
def Len16 (acc : List E × List E × List E) : Prop :=
  acc.1.length = 16 ∧ acc.2.1.length = 16 ∧ acc.2.2.length = 16

theorem slotReadStep_val (B : ℕ → E) (fp G : E) (gamma : E × E) (m : E) (r : Read)
    (hr : readSlotsOK r = true) (acc : List E × List E × List E) (hl : Len16 acc) :
    Len16 (slotReadStep gamma m acc r) ∧
      slotTotal B fp G (slotReadStep gamma m acc r) =
        slotTotal B fp G acc + m * gamma.2 * readProgVal B fp G r := by
  obtain ⟨h1, h2, h3⟩ := hl
  cases r with
  | word => exact ⟨⟨h1, h2, h3⟩, by simp [slotReadStep, readProgVal]⟩
  | slot s scale =>
    simp only [readSlotsOK, Bool.and_eq_true, decide_eq_true_eq] at hr
    refine ⟨⟨by simp [slotReadStep, length_addAtSlot, h1], h2, h3⟩, ?_⟩
    simp only [slotReadStep, slotTotal, readProgVal]
    rw [slotSum_addAtSlot _ _ _ _ _ (by omega), iteT (by omega)]
    ring
  | frame s scale =>
    simp only [readSlotsOK, Bool.and_eq_true, decide_eq_true_eq] at hr
    refine ⟨⟨h1, h2, by simp [slotReadStep, length_addAtSlot, h3]⟩, ?_⟩
    simp only [slotReadStep, slotTotal, readProgVal]
    rw [slotSum_addAtSlot _ _ _ _ _ (by omega), iteT (by omega)]
    ring
  | pc s scale =>
    simp only [readSlotsOK, Bool.and_eq_true, decide_eq_true_eq] at hr
    refine ⟨⟨h1, by simp [slotReadStep, length_addAtSlot, h2], h3⟩, ?_⟩
    simp only [slotReadStep, slotTotal, readProgVal]
    rw [slotSum_addAtSlot _ _ _ _ _ (by omega), iteT (by omega)]
    ring

theorem slotReads_val (B : ℕ → E) (fp G : E) (gamma : E × E) (m : E) :
    ∀ (rs : List Read), rs.all readSlotsOK = true → ∀ acc, Len16 acc →
      Len16 (rs.foldl (slotReadStep gamma m) acc) ∧
      slotTotal B fp G (rs.foldl (slotReadStep gamma m) acc) =
        slotTotal B fp G acc + m * gamma.2 * (rs.map (readProgVal B fp G)).sum
  | [], _, acc, hl => ⟨hl, by simp⟩
  | r :: rs, hrs, acc, hl => by
    simp only [List.all_cons, Bool.and_eq_true] at hrs
    obtain ⟨h1, h2⟩ := slotReadStep_val B fp G gamma m r hrs.1 acc hl
    obtain ⟨h3, h4⟩ := slotReads_val B fp G gamma m rs hrs.2 _ h1
    refine ⟨h3, ?_⟩
    rw [List.foldl_cons, h4, h2]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- One access's step of `tableSlotWeights`' fold. -/
def slotAccessStep (gamma : E × E) (etaMem : E) (acc : List E × List E × List E) (am : Access × E) :
    List E × List E × List E :=
  let (access, m) := am
  let m := etaMem * m
  let frame := match access.frame with
    | some (s, e) => addAtSlot acc.2.2 s (m * gamma.1 * gpow e)
    | none => acc.2.2
  access.reads.foldl (slotReadStep gamma m) (acc.1, acc.2.1, frame)

theorem slotAccess_val (B : ℕ → E) (fp G : E) (gamma : E × E) (etaMem : E) :
    ∀ (L : List (Access × E)), (∀ p ∈ L, accessSlotsOK p.1 = true) → ∀ acc, Len16 acc →
      Len16 (L.foldl (slotAccessStep gamma etaMem) acc) ∧
      slotTotal B fp G (L.foldl (slotAccessStep gamma etaMem) acc) =
        slotTotal B fp G acc + etaMem * (gamma.1 * accSum L (frameVal B fp) +
          gamma.2 * accSum L fun a ↦ (a.reads.map (readProgVal B fp G)).sum)
  | [], _, acc, hl => ⟨hl, by simp [accSum]⟩
  | (a, m) :: L, hL, acc, hl => by
    have ha := hL (a, m) List.mem_cons_self
    simp only [accessSlotsOK, Bool.and_eq_true] at ha
    -- the frame
    obtain ⟨frame, hfl, hfe, hfv⟩ : ∃ frame : List E, frame.length = 16 ∧
        (match a.frame with
          | some (s, e) => addAtSlot acc.2.2 s (etaMem * m * gamma.1 * gpow e)
          | none => acc.2.2) = frame ∧
        fp * slotSum frame 4 12 B = fp * slotSum acc.2.2 4 12 B +
          etaMem * m * gamma.1 * frameVal B fp a := by
      rcases hfr : a.frame with _ | ⟨s, e⟩
      · exact ⟨acc.2.2, hl.2.2, rfl, by simp [frameVal, hfr]⟩
      · rw [hfr] at ha
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
        refine ⟨_, by rw [length_addAtSlot]; exact hl.2.2, rfl, ?_⟩
        rw [slotSum_addAtSlot _ _ _ _ _ (by rw [hl.2.2]; omega), iteT (by omega), frameVal, hfr]
        ring
    have hstep : slotAccessStep gamma etaMem acc (a, m) =
        a.reads.foldl (slotReadStep gamma (etaMem * m)) (acc.1, acc.2.1, frame) := by
      simp only [slotAccessStep]; rw [hfe]
    obtain ⟨h3, h4⟩ := slotReads_val B fp G gamma (etaMem * m) a.reads ha.2 (acc.1, acc.2.1, frame)
      ⟨hl.1, hl.2.1, hfl⟩
    obtain ⟨h5, h6⟩ := slotAccess_val B fp G gamma etaMem L
      (fun p hp ↦ hL p (List.mem_cons_of_mem _ hp)) _ h3
    refine ⟨by rw [List.foldl_cons, hstep]; exact h5, ?_⟩
    rw [List.foldl_cons, hstep, h6, h4]
    simp only [slotTotal, accSum, List.map_cons, List.sum_cons] at hfv ⊢
    rw [hfv]
    ring

/-- The operand equations' slots in range. -/
def operandsOK (ops : List (List ℕ × Form)) : Bool := ops.all fun op ↦ op.1.all fun s ↦ 3 ≤ s && s < 16

theorem slotSum_operand (B : ℕ → E) (c : E) :
    ∀ (slots : List ℕ), slots.all (fun s ↦ 3 ≤ s && s < 16) = true → ∀ w : List E, w.length = 16 →
      (slots.foldl (fun w s ↦ addAtSlot w s c) w).length = 16 ∧
      slotSum (slots.foldl (fun w s ↦ addAtSlot w s c) w) 3 13 B = slotSum w 3 13 B + c * (slots.map B).sum
  | [], _, w, hw => ⟨hw, by simp⟩
  | s :: ss, hs, w, hw => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hs
    have h1 : (addAtSlot w s c).length = 16 := by rw [length_addAtSlot, hw]
    obtain ⟨h2, h3⟩ := slotSum_operand B c ss hs.2 _ h1
    refine ⟨h2, ?_⟩
    rw [List.foldl_cons, h3, slotSum_addAtSlot _ _ _ _ _ (by omega), iteT (by omega)]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem slotSum_operands (B : ℕ → E) (slot : List E) (etaBc : E) :
    ∀ (ops : List (List ℕ × Form)), operandsOK ops = true → ∀ w : List E, w.length = 16 →
      (ops.foldl (fun omega (op : List ℕ × Form) ↦
        op.1.foldl (fun omega s ↦ addAtSlot omega s (etaBc * slot.getD (op.1.headD 0) 0)) omega) w).length
        = 16 ∧
      slotSum (ops.foldl (fun omega (op : List ℕ × Form) ↦
        op.1.foldl (fun omega s ↦ addAtSlot omega s (etaBc * slot.getD (op.1.headD 0) 0)) omega) w) 3 13 B =
        slotSum w 3 13 B + etaBc * (ops.map fun op ↦ slot.getD (op.1.headD 0) 0 * (op.1.map B).sum).sum
  | [], _, w, hw => ⟨hw, by simp⟩
  | op :: ops, hs, w, hw => by
    simp only [operandsOK, List.all_cons, Bool.and_eq_true] at hs
    obtain ⟨h1, h2⟩ := slotSum_operand B (etaBc * slot.getD (op.1.headD 0) 0) op.1 hs.1 w hw
    obtain ⟨h3, h4⟩ := slotSum_operands B slot etaBc ops hs.2 _ h1
    refine ⟨h3, ?_⟩
    rw [List.foldl_cons, h4, h2]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem getD_replicate_zero (n k : ℕ) : (List.replicate n (0 : E)).getD k 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> rfl

theorem slotSum_zero (lo n : ℕ) (F : ℕ → E) : slotSum (List.replicate 16 0) lo n F = 0 := by
  simp only [slotSum, LeanVM.Protocol.Tables.sumE_eq]
  refine List.sum_eq_zero fun x hx ↦ ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  rw [getD_replicate_zero, zero_mul]

/-- **The program side's weights** of a table against an instruction's slots: the opcode's, the
operand equations' and each access's frame and program reads. -/
theorem tableSlotWeights_val (B : ℕ → E) (fp G : E) (table : Table) (slot : List E) (gamma : E × E)
    (mu : List E) (etaMem etaBc : E) (hops : operandsOK table.links.bytecodeLink.operands = true)
    (hacc : table.links.memory.all accessSlotsOK = true) :
    slotTotal B fp G (tableSlotWeights table slot gamma mu etaMem etaBc) =
      etaBc * slot.getD 3 0 * B 3 +
        etaBc * (table.links.bytecodeLink.operands.map fun op ↦
          slot.getD (op.1.headD 0) 0 * (op.1.map B).sum).sum +
        etaMem * (gamma.1 * accSum (table.links.memory.zip mu) (frameVal B fp) +
          gamma.2 * accSum (table.links.memory.zip mu) fun a ↦ (a.reads.map (readProgVal B fp G)).sum) := by
  have h : tableSlotWeights table slot gamma mu etaMem etaBc =
      (table.links.memory.zip mu).foldl (slotAccessStep gamma etaMem)
        (table.links.bytecodeLink.operands.foldl (fun omega (op : List ℕ × Form) ↦
          op.1.foldl (fun omega s ↦ addAtSlot omega s (etaBc * slot.getD (op.1.headD 0) 0)) omega)
          ((List.replicate 16 (0 : E)).set 3 (etaBc * slot.getD 3 0)),
          List.replicate 16 0, List.replicate 16 0) := rfl
  have hl0 : ((List.replicate 16 (0 : E)).set 3 (etaBc * slot.getD 3 0)).length = 16 := by simp
  obtain ⟨h1, h2⟩ := slotSum_operands B slot etaBc _ hops _ hl0
  obtain ⟨-, h4⟩ := slotAccess_val B fp G gamma etaMem (table.links.memory.zip mu)
    (fun p hp ↦ List.all_eq_true.mp hacc p.1 (List.of_mem_zip hp).1) (_, List.replicate 16 0,
      List.replicate 16 0) ⟨h1, List.length_replicate, List.length_replicate⟩
  rw [h, h4]
  simp only [slotTotal]
  rw [h2, slotSum_set _ _ _ (by simp) _ 13, iteT (by omega), slotSum_zero, slotSum_zero, slotSum_zero,
    getD_replicate_zero]
  ring

/-! ## A row's balance -/

/-- **One executed row's share of the balance**: its accesses' weights at their cells against `Y`,
its weight at its instruction against `X_ω`, its payload, its word reads' weights against
`words`, and `ω·fp` against `P_fp`. `tgt a` is the cell access `a` reads, `ptr p` the cell
pointer column `p` names, `σ` the instruction. -/
def rowBal (ch : LinkChallenges) (table : Table) (mu : List E) (col : ℕ → E) (ω : E)
    (tgt : Access → ℕ) (ptr : ℕ → ℕ) (σ : ℕ) (Y X words P : ℕ → E) : E :=
  ch.etaMem * ((table.links.memory.zip mu).map fun am ↦
      gateOf col am.1 * (am.2 * ω) * Y (tgt am.1)).sum +
    ω * X σ +
    ω * ((payloadForms ch table.links mu).1.evaluate col +
      gatedVal col col (payloadForms ch table.links mu).2) +
    ch.etaMem * ((wordReads table.links mu (ch.gammaMem.getD 1 0)).map fun pf ↦
      pf.2.evaluate col * ω * words (ptr pf.1)).sum +
    ω * col table.links.stateLink.fp * P σ

theorem accSum_congr {L : List (Access × E)} {F F' : Access → E} (h : ∀ p ∈ L, F p.1 = F' p.1) :
    accSum L F = accSum L F' := by
  unfold accSum
  rw [List.map_congr_left fun p hp ↦ by rw [h p hp]]

theorem accSum_add (L : List (Access × E)) (F F' : Access → E) :
    accSum L (fun a ↦ F a + F' a) = accSum L F + accSum L F' := by
  unfold accSum
  rw [← List.sum_map_add]
  exact congrArg List.sum <| List.map_congr_left fun p _ ↦ by ring

theorem accSum_mul (L : List (Access × E)) (c : E) (F : Access → E) :
    accSum L (fun a ↦ c * F a) = c * accSum L F := by
  unfold accSum
  rw [← List.sum_map_mul_left]
  exact congrArg List.sum <| List.map_congr_left fun p _ ↦ by ring

/-- **A row whose accesses read their cells and whose program link holds balances**, in
characteristic two. -/
theorem rowBal_alg (ηm ηbc ω a1 a2 a3 G gop Sops SGC SF SRW SRP gm0 gm1 S1 S2 S3 fp : E)
    (hW : S1 + S2 + fp * S3 = ηbc * a3 * gop + ηbc * Sops + ηm * (gm0 * SF + gm1 * SRP)) :
    ηm * (ω * (SGC + gm0 * SF + gm1 * (SRW + SRP))) +
        ω * (ηbc * a1 * G + ηbc * a2 + (S1 + S2)) +
        ω * (ηbc * (a1 * G + a2 + a3 * gop + Sops) + ηm * SGC) +
        ηm * (ω * (gm1 * SRW)) + ω * fp * S3 = 0 := by
  linear_combination ω * hW + (ω * ηbc * (a1 * G + a2 + a3 * gop + Sops) +
    ω * ηm * (SGC + gm0 * SF + gm1 * (SRW + SRP))) * LeanVM.Protocol.Tables.two_eq_zero_E

/-- **A row whose accesses read their cells and whose program link holds balances**, in
characteristic two. -/
theorem rowBal_eq_zero (ch : LinkChallenges) (table : Table) (mu : List E) (col : ℕ → E) (ω : E)
    (tgt : Access → ℕ) (ptr : ℕ → ℕ) (σ : ℕ) (Y X words P : ℕ → E) (B : ℕ → E) (G : E)
    (hX : X σ = ch.etaBc * ch.slot.getD 1 0 * G + ch.etaBc * ch.slot.getD 2 0 +
      (slotSum (tableSlotWeights table ch.slot (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0) mu
          ch.etaMem ch.etaBc).1 3 13 B +
        slotSum (tableSlotWeights table ch.slot (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0) mu
          ch.etaMem ch.etaBc).2.1 3 13 (fun s ↦ G * B s)))
    (hP : P σ = slotSum (tableSlotWeights table ch.slot (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0)
      mu ch.etaMem ch.etaBc).2.2 4 12 B)
    (hpc : col table.links.bytecodeLink.pc = G)
    (hop : B 3 = gpow table.links.bytecodeLink.opcode)
    (hopnd : ∀ op ∈ table.links.bytecodeLink.operands, (op.1.map B).sum = op.2.evaluate col)
    (hops : operandsOK table.links.bytecodeLink.operands = true)
    (hslots : table.links.memory.all accessSlotsOK = true)
    (hacc : ∀ a ∈ table.links.memory, gateOf col a * Y (tgt a) =
      gateOf col a * committedOf ch col a +
        ch.gammaMem.getD 0 0 * frameVal B (col table.links.stateLink.fp) a +
        ch.gammaMem.getD 1 0 * ((a.reads.map (readWordVal (fun p ↦ words (ptr p)) col)).sum +
          (a.reads.map (readProgVal B (col table.links.stateLink.fp) G)).sum)) :
    rowBal ch table mu col ω tgt ptr σ Y X words P = 0 := by
  have hW := tableSlotWeights_val B (col table.links.stateLink.fp) G table ch.slot
    (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0) mu ch.etaMem ch.etaBc hops hslots
  simp only [slotTotal] at hW
  have hpay := payloadForms_val ch table.links mu col
  have hwr := wordReads_val table.links mu (ch.gammaMem.getD 1 0) (fun p ↦ words (ptr p)) col
  have hwr' : ((wordReads table.links mu (ch.gammaMem.getD 1 0)).map fun pf ↦
      pf.2.evaluate col * ω * words (ptr pf.1)).sum =
      ω * gatedVal (fun p ↦ words (ptr p)) col (wordReads table.links mu (ch.gammaMem.getD 1 0)) := by
    rw [gatedVal, ← List.sum_map_mul_left]
    exact congrArg List.sum <| List.map_congr_left fun p _ ↦ by ring
  have hmem : ((table.links.memory.zip mu).map fun am ↦ gateOf col am.1 * (am.2 * ω) * Y (tgt am.1)).sum =
      ω * accSum (table.links.memory.zip mu) fun a ↦ gateOf col a * Y (tgt a) := by
    rw [accSum, ← List.sum_map_mul_left]
    exact congrArg List.sum <| List.map_congr_left fun p _ ↦ by ring
  have hsum := accSum_congr (L := table.links.memory.zip mu) (F := fun a ↦ gateOf col a * Y (tgt a))
    (F' := fun a ↦ gateOf col a * committedOf ch col a +
        ch.gammaMem.getD 0 0 * frameVal B (col table.links.stateLink.fp) a +
        ch.gammaMem.getD 1 0 * ((a.reads.map (readWordVal (fun p ↦ words (ptr p)) col)).sum +
          (a.reads.map (readProgVal B (col table.links.stateLink.fp) G)).sum))
    (fun p hp ↦ hacc p.1 (List.of_mem_zip hp).1)
  rw [accSum_add, accSum_add, accSum_mul, accSum_mul, accSum_add] at hsum
  have hopsum : (table.links.bytecodeLink.operands.map fun op ↦
      ch.slot.getD (op.1.headD 0) 0 * (op.1.map B).sum).sum =
      (table.links.bytecodeLink.operands.map fun op ↦
        ch.slot.getD (op.1.headD 0) 0 * op.2.evaluate col).sum := by
    exact congrArg List.sum <| List.map_congr_left fun op hop ↦ by rw [hopnd op hop]
  rw [hop, hopsum] at hW
  unfold rowBal
  rw [hX, hP, hpay, hwr', hwr, hmem, hsum]
  simp only [bcFormVal, hpc]
  exact rowBal_alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hW

end LeanVM.Prover.Complete

end
