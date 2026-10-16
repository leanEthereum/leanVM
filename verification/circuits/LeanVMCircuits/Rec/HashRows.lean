module

public import LeanVMCircuits.Blake2s.Export

@[expose] public section

/-!
`Hash::circuit`'s constraint rows, as flock's `Builder` lays them out (`crates/flock/src/circuit.rs`).

`Hash::circuit` (`crates/leanvm_core/src/rv/semantics/hash.rs`) opens a builder on 14 input ports (`INPUT_BITS`) and
four 64-bit output ports, binds the Clean circuit's ports to the input bits, calls `flock::clean::blake2s` and commits
its 256 output bits. `flock::clean::blake2s` makes the builder calls of the Clean artifact's steps (`Compress.artifact`)
in order: `Blake2s.Emit` writes each operation as the call `Op.steps` names, and `Export.adder32_call` and
`Export.adder31_call` make the calls' products and sums the artifact's. A row sees a wire only through its linear form
over the instance's bits, so a wire is the structural zero (`none`, `Wire::ZERO`) or its form in `α`, an XOR gate the
sum of its operands' forms (`wxor`, `Builder::xor`). The rows (`rowsOf`), each `(slot, A row, B row)`:

- `Gate::Free(s)`, the constant and each input bit: `z[s] * z[c] = z[s]`, `c` the constant's slot (`constSlot`);
- `Gate::And(x, y, s)` (`Builder::and`): `x * y = z[s]` at the next product slot, unless an operand is the structural
  zero, which makes the zero and takes no slot;
- `Gate::Copy(x, s)` (`Builder::output`): `x * z[c] = z[s]` at output bit `s`, none for the structural zero.

Every other slot's row is empty, forcing its bit to zero. `hashA0` and `hashB0` are the base matrices, each row the form
of its slot's row. `run_holds`: where every row holds under a valuation of the forms, the wires' values satisfy every
step of the artifact. `rowsOf_slots`: the slots are distinct and below `2^14`, and an output bit has a row exactly when
its wire is not the structural zero. `rowsOf_map` (`Rec.HashRowsMap`): an additive map of the slots' values maps each
row's forms, so the rows at column weights are `hashA0`'s and `hashB0`'s rows at the weights; `checkhashrows` compares
them with Rust's `Circuit::row_values` at pseudorandom weights, which checks this transcription against `Hash::circuit`.
-/

namespace LeanVMCircuits.Rec.HashRows

open LeanVMCircuits Gates Blake2s Flock

attribute [local irreducible] program Compress.artifact

/-- The constant wire's slot, right after the 14 input and four output port words (`const_pos`). -/
def constSlot : ℕ := 64 * (14 + 4)

/-- `INPUT_BITS`: `t`, `f0`, then the four words of `h` and the eight of `m`. -/
def portBits : List ℕ := [64, 32, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64]

/-- The input bits' slots in the order `Builder::new` makes their free gates: bit `b` of port `p` at `64 p + b`, each
port one word. -/
def freeSlots : List ℕ := (List.range 14).flatMap fun p => (List.range (portBits.getD p 0)).map (64 * p + ·)

/-- The slot `Hash::circuit` binds the Clean port variable `v` to (`Export.ports`: `t` at 0, `f0` at 64, `h` at 96, `m`
at 352): `t` and `f0` are ports 0 and 1, and 32-bit word `i` of `h` (of `m`) is half `i % 2` of port `2 + i / 2`
(`6 + i / 2`). -/
def portSlot (v : ℕ) : ℕ :=
  if v < 64 then v
  else if v < 96 then 64 + (v - 64)
  else if v < 352 then 64 * (2 + (v - 96) / 32 / 2) + 32 * ((v - 96) / 32 % 2) + (v - 96) % 32
  else 64 * (6 + (v - 352) / 32 / 2) + 32 * ((v - 352) / 32 % 2) + (v - 352) % 32

/-- Output bit `k`'s slot: bit `k % 64` of output port `k / 64`, the ports after the 14 input words. -/
def outSlot (k : ℕ) : ℕ := 64 * (14 + k / 64) + k % 64

variable {α : Type} [Add α]

/-- `Builder::xor`: the structural zero leaves the other wire, two gates make their sum. -/
def wxor : Option α → Option α → Option α
  | some a, some b => some (a + b)
  | none, w => w
  | some a, none => some a

/-- The wire the builder calls of an affine form make, the variables' wires `σ`: `.one` is the constant gate
(`Wire::ONE`), `.zero` the structural zero. -/
def emit (δ : ℕ → α) (σ : ℕ → Option α) : Affine → Option α
  | .zero => none
  | .one => some (δ constSlot)
  | .var i => σ i
  | .xor a b => wxor (emit δ σ a) (emit δ σ b)

/-- A builder part way: its rows, the next product slot, and each variable's wire. -/
structure St (α : Type) where
  rows : List (ℕ × α × α)
  next : ℕ
  σ : ℕ → Option α

/-- `Builder::new(&INPUT_BITS, &[64, 64, 64, 64])` with the Clean ports bound: the constant's free row first, then each
input bit's; products from the slot after the constant. -/
def init (δ : ℕ → α) : St α where
  rows := (constSlot, δ constSlot, δ constSlot) :: freeSlots.map fun s => (s, δ s, δ constSlot)
  next := constSlot + 1
  σ v := if v < Compress.inputBits then some (δ (portSlot v)) else none

/-- One artifact step's builder calls: a definition its XORs (no row), a product `Builder::and` on its operands. -/
def step (δ : ℕ → α) (st : St α) : Step → St α
  | .define o v => { st with σ := Function.update st.σ o (emit δ st.σ v) }
  | .product o l r =>
    match emit δ st.σ l, emit δ st.σ r with
    | some a, some b =>
      { rows := st.rows ++ [(st.next, a, b)], next := st.next + 1, σ := Function.update st.σ o (some (δ st.next)) }
    | _, _ => { st with σ := Function.update st.σ o none }

/-- The builder after the artifact's steps. -/
def run (δ : ℕ → α) : St α := Compress.artifact.steps.foldl (step δ) (init δ)

/-- Output bit `k`'s affine form: `h ^ v_low ^ v_high` at bit `k` (`Compress.outputAffine`). -/
def outAff (k : ℕ) : Affine := Compress.artifact.outputs.getD k .zero

/-- The output bits' rows: `c.output(k / 64, k % 64, wire)` copies output bit `k`'s wire to its slot, none for the
structural zero. -/
def outRows (δ : ℕ → α) (σ : ℕ → Option α) : List (ℕ × α × α) :=
  (List.range 256).filterMap fun k => (emit δ σ (outAff k)).map fun a => (outSlot k, a, δ constSlot)

/-- `Hash::circuit`'s rows. -/
def rowsOf (δ : ℕ → α) : List (ℕ × α × α) := (run δ).rows ++ outRows δ (run δ).σ

/-- A slot's linear form: its own bit. -/
def unit (s : ℕ) : ℕ → ZMod 2 := fun col => if col = s then 1 else 0

/-- `HASH`'s base matrix `A_0`: row `s` the `A` form of slot `s`'s row, zero for an empty row. -/
def hashA0 (s col : ℕ) : ZMod 2 := ((rowsOf unit).find? (·.1 = s)).elim 0 fun r => r.2.1 col

/-- `HASH`'s base matrix `B_0`. -/
def hashB0 (s col : ℕ) : ZMod 2 := ((rowsOf unit).find? (·.1 = s)).elim 0 fun r => r.2.2 col

/-! Soundness: rows holding under a valuation give the artifact's steps. -/

section Sound

variable (δ : ℕ → α) (D : α → Bit)

/-- A wire's value: the structural zero's is zero. -/
def val : Option α → Bit
  | none => 0
  | some a => D a

variable {D}

theorem val_wxor (hD : ∀ a b, D (a + b) = D a + D b) (x y : Option α) : val D (wxor x y) = val D x + val D y := by
  cases x <;> cases y <;> simp [wxor, val, hD]

theorem val_emit (hD : ∀ a b, D (a + b) = D a + D b) (h1 : D (δ constSlot) = 1) (σ : ℕ → Option α) (e : Affine) :
    val D (emit δ σ e) = e.eval (val D ∘ σ) := by
  induction e with
  | zero => rfl
  | one => simp [emit, val, h1, Affine.eval]
  | var i => rfl
  | xor a b iha ihb => simp [emit, Affine.eval, val_wxor hD, iha, ihb]

theorem step_rows (st : St α) (s : Step) : st.rows <+: (step δ st s).rows := by
  cases s with
  | define o v => exact List.prefix_refl _
  | product o l r =>
    simp only [step]
    split
    · exact List.prefix_append _ _
    · exact List.prefix_refl _

theorem foldl_rows (steps : List Step) (st : St α) : st.rows <+: (steps.foldl (step δ) st).rows := by
  induction steps generalizing st with
  | nil => exact List.prefix_refl _
  | cons s rest ih => exact (step_rows δ st s).trans (ih _)

/-- Where every row reached holds (`z[s] = a · b` for the row `(s, a, b)`, valued by `D`), the wires' values satisfy
every step of a well-formed list from `n`, and agree with the start's below `n`. -/
theorem run_holds (hD : ∀ a b, D (a + b) = D a + D b) (h1 : D (δ constSlot) = 1) (steps : List Step) (st : St α)
    (n : ℕ) (hw : Gates.wellFormed n steps = true)
    (hrows : ∀ r ∈ (steps.foldl (step δ) st).rows, D (δ r.1) = D r.2.1 * D r.2.2) :
    AgreeBelow n (val D ∘ st.σ) (val D ∘ (steps.foldl (step δ) st).σ) ∧
      steps.Forall (Step.Holds (val D ∘ (steps.foldl (step δ) st).σ)) := by
  induction steps generalizing st n with
  | nil => exact ⟨fun _ _ => rfl, by simp⟩
  | cons s rest ih =>
    simp only [List.foldl_cons] at hrows ⊢
    set F := rest.foldl (step δ) (step δ st s)
    have hwr : Gates.wellFormed (n + 1) rest = true := by
      cases s <;> simp only [Gates.wellFormed, Bool.and_eq_true] at hw <;> exact hw.2
    obtain ⟨hag, hrest⟩ := ih (step δ st s) (n + 1) hwr hrows
    have hout : s.output = n := by
      cases s <;> simp only [Gates.wellFormed, Bool.and_eq_true, beq_iff_eq] at hw <;> simp only [Step.output] <;> tauto
    have hkeep : ∀ i < n, (step δ st s).σ i = st.σ i := by
      intro i hi
      have hne : i ≠ n := by omega
      cases s with
      | define o v =>
        simp only [Step.output] at hout
        subst hout
        simp [step, Function.update_of_ne hne]
      | product o l r =>
        simp only [Step.output] at hout
        subst hout
        simp only [step]
        split <;> simp [Function.update_of_ne hne]
    have hbelow : AgreeBelow n (val D ∘ st.σ) (val D ∘ F.σ) := by
      intro i hi
      rw [hag i (by omega)]
      simp only [Function.comp, hkeep i hi]
    refine ⟨hbelow, ?_⟩
    simp only [List.forall_cons]
    refine ⟨?_, hrest⟩
    have hn : (val D ∘ F.σ) n = val D ((step δ st s).σ n) := hag n (by omega)
    cases s with
    | define o v =>
      simp only [Gates.wellFormed, Bool.and_eq_true, beq_iff_eq] at hw
      obtain ⟨⟨rfl, hb⟩, -⟩ := hw
      simp only [Step.Holds]
      rw [hn, Affine.eval_agree v o _ _ hb hbelow]
      simp [step, val_emit δ hD h1]
    | product o l r =>
      simp only [Gates.wellFormed, Bool.and_eq_true, beq_iff_eq] at hw
      obtain ⟨⟨⟨rfl, hbl⟩, hbr⟩, -⟩ := hw
      simp only [Step.Holds]
      rw [hn, Affine.eval_agree l o _ _ hbl hbelow, Affine.eval_agree r o _ _ hbr hbelow,
        ← val_emit δ hD h1, ← val_emit δ hD h1]
      cases hl : emit δ st.σ l with
      | none => simp [step, hl, val]
      | some a =>
        cases hr : emit δ st.σ r with
        | none => simp [step, hl, hr, val]
        | some b =>
          have hmem : (st.next, a, b) ∈ F.rows :=
            (foldl_rows δ rest (step δ st (.product o l r))).subset (by simp [step, hl, hr])
          simpa [step, hl, hr, val] using hrows _ hmem

end Sound

/-! The rows' slots. -/

/-- The artifact's products. -/
def nProducts (steps : List Step) : ℕ := steps.countP fun | .product .. => true | .define .. => false

theorem foldl_slots (δ : ℕ → α) (steps : List Step) (st : St α) :
    ∃ m ≤ nProducts steps, (steps.foldl (step δ) st).rows.map Prod.fst = st.rows.map Prod.fst ++ List.range' st.next m ∧
      (steps.foldl (step δ) st).next = st.next + m := by
  induction steps generalizing st with
  | nil => exact ⟨0, by simp [nProducts]⟩
  | cons s rest ih =>
    simp only [List.foldl_cons]
    cases s with
    | define o v =>
      obtain ⟨m, hm, h1, h2⟩ := ih (step δ st (.define o v))
      exact ⟨m, by simpa [nProducts] using hm, by simpa [step] using h1, by simpa [step] using h2⟩
    | product o l r =>
      simp only [step]
      split
      · rename_i a b _ _
        obtain ⟨m, hm, h1, h2⟩ := ih ⟨st.rows ++ [(st.next, a, b)], st.next + 1, Function.update st.σ o (some (δ st.next))⟩
        dsimp only at h1 h2
        refine ⟨m + 1, by simp only [nProducts, List.countP_cons] at hm ⊢; simp; omega, ?_, by rw [h2]; omega⟩
        rw [h1, List.range'_succ]
        simp
      · obtain ⟨m, hm, h1, h2⟩ := ih ⟨st.rows, st.next, Function.update st.σ o none⟩
        exact ⟨m, by simp only [nProducts, List.countP_cons] at hm ⊢; simp; omega, h1, h2⟩

/-- An operation's products: 31 per 32-bit addition, 30 for an even literal's, none for an XOR. -/
def Op.products : Op → ℕ
  | .add _ _ | .addOdd _ _ => 31
  | .addEven _ _ => 30
  | .xorRotr _ _ _ => 0

theorem nProducts_model (ops : List Op) (affs : Affs) (n : ℕ) :
    nProducts (modelSteps ops affs n) = (ops.map Op.products).sum := by
  induction ops generalizing affs n with
  | nil => rfl
  | cons op ops ih =>
    simp only [modelSteps, nProducts, List.countP_append, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    congr 1
    cases op <;> simp [Op.steps, adderSteps, defines, List.countP_map, Function.comp_def, Op.products]

theorem program_products : (program.ops.map Op.products).sum = 14878 := by decide +kernel

theorem artifact_products : nProducts Compress.artifact.steps = 14878 := by
  have e : Compress.artifact.steps = modelSteps program.ops Compress.initialAffines Compress.inputBits := by
    unfold Compress.artifact
    rfl
  rw [e, nProducts_model, program_products]

theorem freeSlots_lt : ∀ s ∈ freeSlots, s < 64 * 14 := by decide +kernel

theorem freeSlots_eq : freeSlots = List.range 96 ++ List.range' 128 768 := by decide +kernel

theorem freeSlots_nodup : freeSlots.Nodup := by
  rw [freeSlots_eq]
  refine List.Nodup.append List.nodup_range List.nodup_range' fun a ha hb => ?_
  simp only [List.mem_range, List.mem_range'] at ha hb
  omega

theorem outRows_slots (δ : ℕ → α) (σ : ℕ → Option α) :
    (outRows δ σ).map Prod.fst = ((List.range 256).filter fun k => (emit δ σ (outAff k)).isSome).map outSlot := by
  simp only [outRows]
  induction (List.range 256) with
  | nil => rfl
  | cons k ks ih =>
    cases h : emit δ σ (outAff k) with
    | none =>
      rw [List.filterMap_cons_none (by rw [h, Option.map_none]), List.filter_cons_of_neg (by rw [h]; simp)]
      exact ih
    | some a =>
      rw [List.filterMap_cons_some (by rw [h, Option.map_some]), List.filter_cons_of_pos (by rw [h]; rfl)]
      simp only [List.map_cons, ih]

theorem outSlot_inj {k k' : ℕ} (h : outSlot k = outSlot k') : k = k' := by
  simp only [outSlot] at h
  omega

theorem rowsOf_slots (δ : ℕ → α) :
    ((rowsOf δ).map Prod.fst).Nodup ∧ (∀ r ∈ rowsOf δ, r.1 < 2 ^ 14) ∧
      ∀ k < 256, (outSlot k ∈ (rowsOf δ).map Prod.fst ↔ (emit δ (run δ).σ (outAff k)).isSome) := by
  obtain ⟨m, hm, hs, -⟩ := foldl_slots δ Compress.artifact.steps (init δ)
  rw [artifact_products] at hm
  have hrun : (run δ).rows.map Prod.fst = constSlot :: freeSlots ++ List.range' (constSlot + 1) m := by
    simpa [run, init, Function.comp_def] using hs
  have hout := outRows_slots δ (run δ).σ
  set O := (List.range 256).filter fun k => (emit δ (run δ).σ (outAff k)).isSome
  have hO : ∀ k ∈ O, k < 256 := fun k hk => by simpa [O] using (List.mem_filter.mp hk).1
  have hslots : (rowsOf δ).map Prod.fst = constSlot :: freeSlots ++ List.range' (constSlot + 1) m ++ O.map outSlot := by
    simp only [rowsOf, List.map_append, hrun, hout]
  have hfree := freeSlots_lt
  refine ⟨?_, ?_, ?_⟩
  · rw [hslots]
    have hOn : (O.map outSlot).Nodup :=
      (List.Nodup.filter _ List.nodup_range).map (fun _ _ h => outSlot_inj h)
    refine List.Nodup.append (List.Nodup.append (List.nodup_cons.mpr ⟨fun h => ?_, freeSlots_nodup⟩)
      List.nodup_range' ?_) hOn ?_
    · have := hfree _ h
      simp [constSlot] at this
    · intro a ha hb
      simp only [List.mem_range'] at hb
      rcases List.mem_cons.mp ha with rfl | ha
      · omega
      · have := hfree _ ha
        simp only [constSlot] at hb
        omega
    · intro a ha hb
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
      have hk' := hO k hk
      simp only [List.mem_append, List.mem_cons, List.mem_range'] at ha
      simp only [outSlot, constSlot] at ha
      rcases ha with (h | ha) | ha
      · omega
      · have := hfree _ ha
        omega
      · omega
  · intro r hr
    have hmem : r.1 ∈ (rowsOf δ).map Prod.fst := List.mem_map_of_mem hr
    rw [hslots] at hmem
    simp only [List.mem_append, List.mem_cons, List.mem_range', List.mem_map] at hmem
    simp only [constSlot] at hmem
    rcases hmem with ((h | h) | h) | ⟨k, hk, h⟩
    · omega
    · have := hfree _ h
      omega
    · omega
    · have := hO k hk
      simp only [outSlot] at h
      omega
  · intro k hk
    rw [hslots]
    simp only [List.mem_append, List.mem_cons, List.mem_range', List.mem_map]
    constructor
    · rintro (((h | h) | h) | ⟨k', hk', h⟩)
      · simp [outSlot, constSlot] at h
        omega
      · have := hfree _ h
        simp only [outSlot] at this
        omega
      · simp only [outSlot, constSlot] at h
        omega
      · rw [← outSlot_inj h]
        exact (List.mem_filter.mp hk').2
    · intro h
      exact Or.inr ⟨k, List.mem_filter.mpr ⟨List.mem_range.mpr hk, h⟩, rfl⟩

theorem outAff_eq (k : ℕ) (hk : k < 256) :
    outAff k = Compress.outputAffine (modelAffs program.ops Compress.initialAffines Compress.inputBits) ⟨k, hk⟩ := by
  unfold outAff Compress.artifact
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk, dite_true, Option.getD_some]

theorem find?_of_nodup {β : Type} (l : List (ℕ × β)) (hl : (l.map Prod.fst).Nodup) (r : ℕ × β) (hr : r ∈ l) :
    l.find? (·.1 = r.1) = some r := by
  induction l with
  | nil => simp at hr
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hl
    rcases List.mem_cons.mp hr with rfl | hr
    · simp
    · have hne : x.1 ≠ r.1 := fun h => hl.1 (h ▸ List.mem_map_of_mem hr)
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact ih hl.2 hr

theorem find?_of_not_mem {β : Type} (l : List (ℕ × β)) (s : ℕ) (hs : s ∉ l.map Prod.fst) :
    l.find? (·.1 = s) = none := by
  rw [List.find?_eq_none]
  intro x hx h
  exact hs (List.mem_map.mpr ⟨x, hx, by simpa using h⟩)

open Finset in
/-- Where every row of a `2^k`-bit instance `z` holds (`(A_0 z)_s (B_0 z)_s + z_s = 0`), `k ≥ 14`, and the constant's
bit is one, the wires' values satisfy the artifact, its port variables are their slots' bits, and its outputs are the
output slots' bits. -/
theorem rows_sound (k : ℕ) (hk : 14 ≤ k) (z : ℕ → ZMod 2)
    (hrow : ∀ s < 2 ^ k, (∑ col ∈ range (2 ^ k), hashA0 s col * z col) * (∑ col ∈ range (2 ^ k), hashB0 s col * z col) +
      z s = 0) (hpin : z constSlot = 1) :
    ∃ a, Compress.artifact.Holds a ∧ (∀ v < Compress.inputBits, a v = z (portSlot v)) ∧
      ∀ j < 256, (outAff j).eval a = z (outSlot j) := by
  let D : (ℕ → ZMod 2) → Bit := fun f => ∑ col ∈ range (2 ^ k), f col * z col
  have hD : ∀ a b, D (a + b) = D a + D b := fun a b => by
    simp only [D, Pi.add_apply, add_mul, sum_add_distrib]
  have hk' : 2 ^ 14 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hunit : ∀ s < 2 ^ k, D (unit s) = z s := fun s hs => by
    simp only [D, unit, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range, hs, if_true]
  have hc : constSlot < 2 ^ k := lt_of_lt_of_le (by simp [constSlot]) hk'
  have h1 : D (unit constSlot) = 1 := by rw [hunit _ hc]; exact hpin
  obtain ⟨hnd, hlt, hout⟩ := rowsOf_slots (unit : ℕ → ℕ → ZMod 2)
  have hok : ∀ r ∈ rowsOf unit, D (unit r.1) = D r.2.1 * D r.2.2 := by
    intro r hr
    have hs : r.1 < 2 ^ k := lt_of_lt_of_le (hlt _ hr) hk'
    have hf := find?_of_nodup _ hnd _ hr
    have h := hrow r.1 hs
    simp only [hashA0, hashB0, hf, Option.elim_some] at h
    rw [hunit r.1 hs]
    have h' := neg_eq_of_add_eq_zero_right h
    rwa [ZMod.neg_eq_self_mod_two, eq_comm] at h'
  have hwf : Gates.wellFormed Compress.inputBits Compress.artifact.steps = true :=
    (Gates.lowerAt_correct _ _ _ _ Compress.lowered ⟨fun _ => 0, fun _ _ => #[]⟩).2.2.2.2
  have hrun : Compress.artifact.steps.foldl (step unit) (init unit) = run unit := rfl
  obtain ⟨hag, hholds⟩ := run_holds unit hD h1 _ (init unit) _ hwf fun r hr =>
    hok r (List.mem_append_left _ (by rw [hrun] at hr; exact hr))
  rw [hrun] at hag hholds
  refine ⟨val D ∘ (run unit).σ, hholds, fun v hv => ?_, fun j hj => ?_⟩
  · rw [hag v hv]
    have hps : portSlot v < 2 ^ k := by
      simp only [Compress.inputBits] at hv
      refine lt_of_lt_of_le ?_ hk'
      simp only [portSlot]
      split_ifs <;> omega
    simp only [Function.comp, init, hv, if_true, val, hunit _ hps]
  · have hos : outSlot j < 2 ^ k := lt_of_lt_of_le (by simp only [outSlot]; omega) hk'
    rw [← val_emit unit hD h1]
    cases he : emit unit (run unit).σ (outAff j) with
    | none =>
      have hn : outSlot j ∉ (rowsOf unit).map Prod.fst := fun h => by simpa [he] using (hout j hj).mp h
      have hf := find?_of_not_mem _ _ hn
      have h := hrow _ hos
      simp only [hashA0, hashB0, hf, Option.elim_none, zero_mul, sum_const_zero, mul_zero, zero_add] at h
      simp only [val, h]
    | some f =>
      have hm : (outSlot j, f, unit constSlot) ∈ rowsOf unit :=
        List.mem_append_right _ (List.mem_filterMap.mpr ⟨j, List.mem_range.mpr hj, by simp [he]⟩)
      have h := hok _ hm
      simp only [h1, mul_one, hunit _ hos] at h
      simp only [val, h]

end LeanVMCircuits.Rec.HashRows
