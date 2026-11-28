/-
  LeanVM.Prover.Complete.Link.RowShape

  The row rounds' tables are well shaped: every table of a table's sum has `2^h` entries, every
  term at most `rowCount - 1` factors (`RowOK`).
-/

module

public import LeanVM.Prover.Complete.Link.Core
public import LeanVM.Prover.Complete.Keccak.Witness

/-!
# The rows' shape

`rowProds` (`Statement/Prover/LinkRow.lean`) is restated with its pointer-column step
(`rowPointerStep`) and its base step (`rowBaseStep`) named (`rowProds_eq`, by `rfl`), so their
invariants are lemmas: every table has `2^h` entries (the column tables, the coefficient tables
and the functional tables of the table's columns, each `2^h` rows) and every term has at most
`d + 2` factors (a pointer's `ω·c·D_0·Π D_i`, a shifted read's `ω·gate·T_s·Π D_i`, a certificate's
three) or, for a base term, at most four (its weight, its gate and a monomial of degree at most
two). `rowOK_linkRowStart`: the rows' start is `RowOK` at `rowCount = max (d + 2) 4 + 1`.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Protocol.Verifier.Defers

/-! ## `rowProds`, its steps named -/

/-- The pointer-column step of `rowProds`. -/
def rowPointerStep (W : Witness) (inp : RowInputs) (t q₀ : ℕ)
    (acc : Array (Array E) × Array (E × Array ℕ) × ℕ) (pk : ℕ × ℕ) :
    Array (Array E) × Array (E × Array ℕ) × ℕ :=
  let ch := inp.ch
  let chunks := W.chunks
  let d := chunks.d
  let table := tables.getD t default
  let links := table.links
  let mu := ch.mu.getD t []
  let h := W.layout.tableLogHeights.getD t 0
  let cols := W.tableCols t
  let fTabs := inp.functionals.tables
  let pointer := pk.1
  let k := pk.2
  let (tabs, terms, pos) := acc
  let words := cols.getD pointer #[]
  let coefs := Array.ofFn (n := 2 ^ h) fun u ↦ rowCoefs inp links mu k pointer (rowValue cols u)
  let shifts := shiftsAt links mu pointer
  let ds := (List.range (2 * d)).map fun i ↦ functionalTable chunks words (fTabs.getD i (0, []))
  let ts := shifts.map fun s ↦ functionalTable chunks words (fTabs.getD (2 * d + s - 1) (0, []))
  let tabs := tabs ++ #[coefs.map (·.1), coefs.map (·.2)] ++ ds.toArray ++ ts.toArray
  let (cω, cAct, dAt) := (pos, pos + 1, pos + 2)
  let rest := (List.range (d - 1)).map (dAt + 1 + ·)
  let terms := terms.push (1, (#[0, cω, dAt] ++ rest.toArray))
  let terms := terms.push (1, (#[1, cAct, dAt] ++ rest.toArray))
  let terms := (accessesAt links mu pointer).foldl (fun terms (a, m) ↦
    if a.shift = 0 then terms
    else
      let tAt := dAt + 2 * d + shifts.idxOf a.shift
      let gate := (a.gate.map fun g ↦ #[3 + g]).getD #[]
      terms.push (ch.etaMem * inp.yMem * m, #[0] ++ gate ++ #[tAt] ++ rest.toArray)) terms
  let e := inp.cert * ch.eps.getD (q₀ + k) 0
  let terms := (List.range d).foldl (fun terms i ↦
    let w := e * ch.nu.getD i 0
    (terms.push (w, #[0, dAt + i, dAt + d + i])).push
      (w * inp.functionals.mirrors.getD i 0, #[0])) terms
  (tabs, terms, pos + 2 + 2 * d + shifts.length)

/-- The start of `rowProds`' pointer-column fold. -/
def rowInit (W : Witness) (inp : RowInputs) (t : ℕ) : Array (Array E) × Array (E × Array ℕ) × ℕ :=
  let ch := inp.ch
  let table := tables.getD t default
  let h := W.layout.tableLogHeights.getD t 0
  let n := W.rows.getD t 0
  let cols := W.tableCols t
  let width := table.width
  let omega := omegaTable (ch.theta.getD t 0) ch.tau h n
  let act := Array.ofFn (n := 2 ^ h) fun u ↦ if u.val < n then (1 : E) else 0
  let eqTau := eqTable (ch.tau.take h)
  let colTabs := (List.range width).map (columnE cols)
  (#[omega, act, eqTau] ++ colTabs.toArray, #[], 3 + width)

/-- The base step of `rowProds`: one block's monomials. -/
def rowBaseStep (terms : Array (E × Array ℕ)) (b : Block) : Array (E × Array ℕ) :=
  let weight := if b.onEq then 2 else 0
  let gate := (b.gate.map fun g ↦ #[3 + g]).getD #[]
  b.form.terms.foldl (fun terms (vars, c) ↦
    terms.push (c, #[weight] ++ gate ++ (vars.map (3 + ·)).toArray)) terms

theorem rowProds_eq (W : Witness) (inp : RowInputs) (t q₀ : ℕ) :
    rowProds W inp t q₀ =
      let r := (tables.getD t default).links.pointers.zipIdx.foldl (rowPointerStep W inp t q₀)
        (rowInit W inp t)
      (⟨r.1, (tableBlocks inp.ch t inp.eq0 (some inp.jump)).foldl rowBaseStep r.2.1⟩, r.2.1.size) := by
  unfold rowProds rowPointerStep rowInit rowBaseStep
  rfl

/-! ## The witness's columns -/

theorem tableOf_base : ∀ t < nTables, ∀ c < tableWidths.getD t 0,
    tableOf (globalColumnBases.getD t 0 + c) = t ∧ 3 ≤ globalColumnBases.getD t 0 ∧
      globalColumnBases.getD t 0 + c < nColumns := by
  decide +kernel

/-- A table's column of the witness has the table's `2^h` rows. -/
theorem size_tableCols_getD {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) {t c : ℕ} (ht : t < nTables)
    (hc : c < tableWidths.getD t 0) :
    ((W.tableCols t).getD c #[]).size = 2 ^ W.layout.tableLogHeights.getD t 0 := by
  obtain ⟨-, steps, -, -, -, -, -, hcols, -⟩ := witness?_spec hW
  obtain ⟨h1, h2, h3⟩ := tableOf_base t ht c hc
  have hsize : W.cols.size = nColumns := by rw [hcols]; simp [colsOf]
  have hlt : c < min (globalColumnBases.getD t 0 + tableWidths.getD t 0) W.cols.size -
      globalColumnBases.getD t 0 := by rw [hsize]; omega
  simp only [Witness.tableCols, Array.getD_eq_getD_getElem?, Array.getElem?_extract, hlt,
    ↓reduceIte]
  rw [← Array.getD_eq_getD_getElem?, hcols]
  unfold colsOf
  rw [Keccak.getD_ofFn' _ h3]
  have hm0 : globalColumnBases.getD t 0 + c ≠ memory0 := by unfold memory0; omega
  have hm1 : globalColumnBases.getD t 0 + c ≠ memory1 := by unfold memory1; omega
  have hq : globalColumnBases.getD t 0 + c ≠ qkeccak := by unfold qkeccak; omega
  simp only [hm0, hm1, hq, ↓reduceIte, h1, Nat.add_sub_cancel_left]
  exact Keccak.tableColumn_size _ _ _ _

/-! ## Forms of degree at most two -/

/-- Every monomial of the form has at most two variables. -/
def FormLE (f : Form) : Prop := ∀ m ∈ f.terms, m.1.length ≤ 2

theorem addTerm_vars : ∀ (l : List (List ℕ × E)) (v : List ℕ) (c : E), ∀ x ∈ addTerm l v c,
    x.1 = v ∨ ∃ y ∈ l, x.1 = y.1
  | [], v, c, x, hx => by simp [addTerm] at hx; subst hx; exact Or.inl rfl
  | (m', c') :: rest, v, c, x, hx => by
    simp only [addTerm] at hx
    split at hx
    · rename_i he
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr ⟨(m', c'), List.mem_cons_self, rfl⟩
      · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, rfl⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr ⟨(m', c'), List.mem_cons_self, rfl⟩
      · rcases addTerm_vars rest v c x hx with h | ⟨y, hy, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, h⟩

theorem FormLE.addScaled {f g : Form} (hf : FormLE f) (hg : FormLE g) (w : E) :
    FormLE (f.addScaled g w) := by
  unfold Form.addScaled FormLE
  suffices h : ∀ (L : List (List ℕ × E)) (acc : List (List ℕ × E)),
      (∀ m ∈ L, m.1.length ≤ 2) → (∀ m ∈ acc, m.1.length ≤ 2) →
      ∀ m ∈ L.foldl (fun acc t ↦ addTerm acc t.1 (w * t.2)) acc, m.1.length ≤ 2 from
    h g.terms f.terms hg hf
  intro L
  induction L with
  | nil => intro acc _ h; exact h
  | cons t L ih =>
    intro acc hL hacc
    refine ih _ (fun m hm ↦ hL m (List.mem_cons_of_mem _ hm)) fun m hm ↦ ?_
    rcases addTerm_vars _ _ _ m hm with h | ⟨y, hy, h⟩
    · rw [h]; exact hL t List.mem_cons_self
    · rw [h]; exact hacc y hy

theorem FormLE.empty : FormLE ({} : Form) := fun m hm ↦ by simp at hm

theorem FormLE.const (c : E) : FormLE (Form.const c) := fun m hm ↦ by
  simp [Form.const] at hm; subst hm; simp

/-- The tables' link forms have degree at most two. -/
theorem tables_formLE : ∀ t < nTables,
    (∀ sf ∈ (tables.getD t default).links.bytecodeLink.operands, ∀ m ∈ sf.2.terms,
      m.1.length ≤ 2) ∧
    ∀ a ∈ (tables.getD t default).links.memory,
      (∀ m ∈ a.address.terms, m.1.length ≤ 2) ∧ ∀ m ∈ a.value.terms, m.1.length ≤ 2 := by
  decide +kernel

theorem foldl_inv {α β : Type} (P : β → Prop) (Q : α → Prop) (f : β → α → β)
    (h : ∀ b a, Q a → P b → P (f b a)) : ∀ (L : List α) (b : β), (∀ a ∈ L, Q a) → P b →
      P (L.foldl f b)
  | [], _, _, hb => hb
  | a :: L, b, hL, hb => foldl_inv P Q f h L _ (fun x hx ↦ hL x (List.mem_cons_of_mem _ hx))
      (h b a (hL a List.mem_cons_self) hb)

theorem formLE_payloadForms (ch : LinkChallenges) {t : ℕ} (ht : t < nTables) (mu : List E) :
    FormLE (payloadForms ch (tables.getD t default).links mu).1 ∧
      ∀ g ∈ (payloadForms ch (tables.getD t default).links mu).2, FormLE g.2 := by
  obtain ⟨hop, hmem⟩ := tables_formLE t ht
  unfold payloadForms
  dsimp only
  refine foldl_inv (fun acc : Form × List (ℕ × Form) ↦ FormLE acc.1 ∧ ∀ g ∈ acc.2, FormLE g.2)
    (fun am : Access × E ↦ am.1 ∈ (tables.getD t default).links.memory) _ ?_ _ _
    (fun am ham ↦ (List.of_mem_zip ham).1) ⟨?_, ?_⟩
  · intro acc am ham hacc
    obtain ⟨access, m⟩ := am
    have ha := hmem access ham
    have hadd : ∀ f, FormLE f → ∀ w, FormLE (((f.addScaled access.address
        (w * ch.gammaMem.getD 0 0)).addScaled (Form.const 1)
        (w * ch.gammaMem.getD 3 0)).addScaled access.value (w * ch.gammaMem.getD 1 0)) :=
      fun f hf w ↦ ((hf.addScaled ha.1 _).addScaled (FormLE.const 1) _).addScaled ha.2 _
    dsimp only
    split
    · exact ⟨hadd _ hacc.1 _, hacc.2⟩
    · refine ⟨hacc.1, fun g hg ↦ ?_⟩
      simp only [List.mem_map] at hg
      obtain ⟨⟨g', f⟩, hgf, rfl⟩ := hg
      dsimp only
      split
      · exact hadd _ (hacc.2 _ hgf) _
      · exact hacc.2 _ hgf
  · refine foldl_inv FormLE (fun sf ↦ sf ∈ (tables.getD t default).links.bytecodeLink.operands) _
      (fun f sf hsf hf ↦ hf.addScaled (fun m hm ↦ hop sf hsf m hm) _) _ _ (fun _ h ↦ h) ?_
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · simp
    rcases List.mem_cons.mp hm with rfl | hm
    · simp
    simp at hm
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨_, -, rfl⟩ := hg
    exact FormLE.empty

theorem formLE_jumpConstraintForm (coefs : List E) : FormLE (jumpConstraintForm coefs) := by
  intro m hm
  simp only [jumpConstraintForm, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem formLE_tableBlocks (ch : LinkChallenges) {t : ℕ} (ht : t < nTables) (scale : E)
    (jump : Option (List E)) : ∀ b ∈ tableBlocks ch t scale jump, FormLE b.form := by
  obtain ⟨hu, hg⟩ := formLE_payloadForms ch ht (ch.mu.getD t [])
  intro b hb
  unfold tableBlocks at hb
  dsimp only at hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact FormLE.empty.addScaled hu _
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨⟨g, f⟩, hgf, rfl⟩ := List.mem_map.mp hb
    exact FormLE.empty.addScaled (hg _ hgf) _
  · split at hb
    · split at hb
      · simp only [List.mem_singleton] at hb
        subst hb
        exact formLE_jumpConstraintForm _
      · simp at hb
    · simp at hb

/-! ## The terms' sizes -/

/-- Every term has at most `count - 1` factors. -/
def TermsLE (count : ℕ) (terms : Array (E × Array ℕ)) : Prop :=
  ∀ cf ∈ terms.toList, cf.2.size + 1 ≤ count

theorem TermsLE.push {count : ℕ} {terms : Array (E × Array ℕ)} (h : TermsLE count terms)
    {cf : E × Array ℕ} (hcf : cf.2.size + 1 ≤ count) : TermsLE count (terms.push cf) := by
  intro x hx
  rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact h x hx
  · exact hcf

theorem gate_size (g : Option ℕ) : ((g.map fun g ↦ #[3 + g]).getD #[]).size ≤ 1 := by
  cases g <;> simp

theorem rowBaseStep_termsLE {count : ℕ} (hc : 5 ≤ count) {terms : Array (E × Array ℕ)}
    (h : TermsLE count terms) {b : Block} (hb : FormLE b.form) :
    TermsLE count (rowBaseStep terms b) := by
  unfold rowBaseStep
  refine foldl_inv (TermsLE count) (fun m : List ℕ × E ↦ m.1.length ≤ 2) _ ?_ _ _
    (fun m hm ↦ hb m hm) h
  intro ts m hm hts
  refine hts.push ?_
  have := gate_size b.gate
  simp only [Array.size_append, List.size_toArray, List.length_map, List.length_cons,
    List.length_nil]
  omega

theorem size_functionalTable (chunks : Chunks) (words : Array K) (f : ℕ × List E) :
    (functionalTable chunks words f).size = words.size := by
  simp [functionalTable]

/-- **The pointer-column step keeps the tables' size and the terms' bound.** -/
theorem rowPointerStep_spec (W : Witness) (inp : RowInputs) (t q₀ count : ℕ)
    (hd : 1 ≤ W.chunks.d) (hcount : W.chunks.d + 3 ≤ count)
    (pk : ℕ × ℕ) (hsz : ((W.tableCols t).getD pk.1 #[]).size = 2 ^ W.layout.tableLogHeights.getD t 0)
    (acc : Array (Array E) × Array (E × Array ℕ) × ℕ)
    (h1 : ∀ x ∈ acc.1.toList, x.size = 2 ^ W.layout.tableLogHeights.getD t 0)
    (h2 : TermsLE count acc.2.1) :
    (∀ x ∈ (rowPointerStep W inp t q₀ acc pk).1.toList,
      x.size = 2 ^ W.layout.tableLogHeights.getD t 0) ∧
      TermsLE count (rowPointerStep W inp t q₀ acc pk).2.1 := by
  obtain ⟨tabs, terms, pos⟩ := acc
  obtain ⟨pointer, k⟩ := pk
  unfold rowPointerStep
  dsimp only at h1 h2 hsz ⊢
  refine ⟨fun x hx ↦ ?_, ?_⟩
  · simp only [Array.toList_append, List.mem_append] at hx
    rcases hx with ((hx | hx) | hx) | hx
    · exact h1 x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      rw [size_functionalTable, hsz]
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      rw [size_functionalTable, hsz]
  · have hrest : ∀ a b c : ℕ, (#[a, b, c] ++ ((List.range (W.chunks.d - 1)).map
        (c + 1 + ·)).toArray).size + 1 ≤ count := by
      intro a b c
      simp only [Array.size_append, List.size_toArray, List.length_map, List.length_range,
        List.length_cons, List.length_nil]
      omega
    refine foldl_inv (TermsLE count) (fun _ ↦ True) _ ?_ _ _ (fun _ _ ↦ trivial) ?_
    · intro ts i _ hts
      refine (hts.push ?_).push ?_
      · simp; omega
      · simp; omega
    · refine foldl_inv (TermsLE count) (fun _ ↦ True) _ ?_ _ _ (fun _ _ ↦ trivial) ?_
      · intro ts am _ hts
        split
        · exact hts
        · refine hts.push ?_
          have := gate_size am.1.gate
          simp only [Array.size_append, List.size_toArray, List.length_map, List.length_range,
            List.length_cons, List.length_nil]
          omega
      · exact (h2.push (hrest _ _ _)).push (hrest _ _ _)

/-! ## The rows' start -/

theorem tables_pointers : ∀ t < nTables, (tables.getD t default).width = tableWidths.getD t 0 ∧
    ∀ p ∈ (tables.getD t default).links.pointers, p < tableWidths.getD t 0 := by
  decide +kernel

theorem one_le_d {w : ℕ} {c : Chunks} (h : Chunks.new w = some c) : 1 ≤ c.d := by
  unfold Chunks.new at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp [Chunks.d]
  · cases h

theorem le_foldl_max_self : ∀ (l : List ℕ) (b : ℕ), b ≤ l.foldl max b
  | [], _ => le_rfl
  | y :: l, b => (le_max_left b y).trans (le_foldl_max_self l _)

theorem le_foldl_max : ∀ (l : List ℕ) (a : ℕ) {t : ℕ}, l.getD t 0 ≤ l.foldl max a
  | [], a, t => by simp
  | x :: l, a, 0 => by
    simp only [List.getD_cons_zero, List.foldl_cons]
    exact (le_max_right a x).trans (le_foldl_max_self l _)
  | x :: l, a, t + 1 => by
    simp only [List.getD_cons_succ, List.foldl_cons]
    exact le_foldl_max l _

theorem length_tau (nRows width d : ℕ) (theta0 : E) (drawn : List E)
    (hlen : drawn.length = packedChallenges tables nRows width) :
    (LinkChallenges.ofDraw tables nRows width d theta0 drawn).tau.length = nRows := by
  have h1 : (tables.map (·.links.memory.length)).sum = 39 := by decide
  have h2 : (tables.map (·.links.pointers.length)).sum = 33 := by decide
  unfold packedChallenges at hlen
  rw [h1, h2] at hlen
  unfold LinkChallenges.ofDraw
  simp only [muFold_snd, h1, h2, List.length_take, List.length_drop, hlen, bytecodeSlotBits,
    nTables]
  omega

/-- **The rows' start is well shaped.** -/
theorem rowOK_linkRowStart {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (x : LinkProverPre)
    (hch : ∃ theta0 drawn, drawn.length = packedChallenges tables (linkNRows W) W.chunks.width ∧
      x.ch = LinkChallenges.ofDraw tables (linkNRows W) W.chunks.width W.chunks.d theta0 drawn) :
    RowOK (roundCoefficients W.chunks.d).1 (linkRowStart W x) := by
  obtain ⟨-, hch', -, -⟩ := linkSizes hW
  have hd := one_le_d hch'
  obtain ⟨θ, drawn, hlen, hx⟩ := hch
  have htau : x.ch.tau.length = linkNRows W := by rw [hx]; exact length_tau _ _ _ _ _ hlen
  have hcount : W.chunks.d + 3 ≤ (roundCoefficients W.chunks.d).1 := by
    simp only [roundCoefficients]; omega
  have hc5 : 5 ≤ (roundCoefficients W.chunks.d).1 := by simp only [roundCoefficients]; omega
  intro rt hrt
  simp only [linkRowStart, Array.toList_ofFn, List.mem_ofFn] at hrt
  obtain ⟨⟨t, ht⟩, rfl⟩ := hrt
  obtain ⟨hwid, hptr⟩ := tables_pointers t ht
  have hhle : W.layout.tableLogHeights.getD t 0 ≤ linkNRows W := le_foldl_max _ _
  rw [rowProds_eq]
  dsimp only
  -- the start of the pointer-column fold
  have hinit1 : ∀ y ∈ (rowInit W (linkRowInputs W x) t).1.toList, y.size = 2 ^ W.layout.tableLogHeights.getD t 0 := by
    intro y hy
    simp only [rowInit, Array.toList_append, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hy
    rcases hy with (rfl | rfl | rfl) | hy
    · simp only [omegaTable, Array.size_ofFn]
    · simp
    · rw [Keccak.size_eqTable, List.length_take]
      have : (linkRowInputs W x).ch.tau.length = linkNRows W := htau
      rw [this, min_eq_left hhle]
    · simp only [List.mem_map, List.mem_range] at hy
      obtain ⟨c, hc, rfl⟩ := hy
      simp only [columnE, Array.size_map]
      exact size_tableCols_getD hW ht (by rw [← hwid]; exact hc)
  have hinit2 : 0 < (rowInit W (linkRowInputs W x) t).1.size := by simp [rowInit]
  have hinit3 : TermsLE (roundCoefficients W.chunks.d).1 (rowInit W (linkRowInputs W x) t).2.1 :=
    fun cf hcf ↦ by simp [rowInit] at hcf
  -- the pointer-column fold
  have hfold := foldl_inv (fun acc : Array (Array E) × Array (E × Array ℕ) × ℕ ↦
      (∀ y ∈ acc.1.toList, y.size = 2 ^ W.layout.tableLogHeights.getD t 0) ∧ 0 < acc.1.size ∧
        TermsLE (roundCoefficients W.chunks.d).1 acc.2.1)
    (fun pk : ℕ × ℕ ↦ pk.1 ∈ (tables.getD t default).links.pointers)
    (rowPointerStep W (linkRowInputs W x) t (pointerStarts.getD t 0)) (fun acc pk hpk hacc ↦ by
      obtain ⟨h1, h2, h3⟩ := hacc
      obtain ⟨s1, s2⟩ := rowPointerStep_spec W (linkRowInputs W x) t (pointerStarts.getD t 0) _
        hd hcount pk (size_tableCols_getD hW ht (hptr _ hpk)) acc h1 h3
      refine ⟨s1, ?_, s2⟩
      obtain ⟨tabs, terms, pos⟩ := acc
      dsimp only at h2
      unfold rowPointerStep
      simp only [Array.size_append]
      omega)
    (tables.getD t default).links.pointers.zipIdx (rowInit W (linkRowInputs W x) t)
    (fun _ hpk ↦ List.fst_mem_of_mem_zipIdx hpk) ⟨hinit1, hinit2, hinit3⟩
  obtain ⟨h1, h2, h3⟩ := hfold
  refine ⟨Nat.zero_le _, ⟨fun y hy ↦ ?_, ?_⟩, fun cf hcf ↦ ?_, fun _ ↦ rfl⟩
  · rw [Nat.sub_zero]; exact h1 y (by simpa using hy)
  · rw [Nat.sub_zero]
    exact h1 _ (by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2, Option.getD_some]
      exact Array.getElem_mem_toList h2)
  · refine foldl_inv (TermsLE (roundCoefficients W.chunks.d).1)
      (fun b ↦ FormLE b.form) rowBaseStep (fun ts b hb hts ↦ rowBaseStep_termsLE hc5 hts hb)
      _ _ (formLE_tableBlocks _ ht _ _) h3 cf (by simpa using hcf)

end LeanVM.Prover.Complete

end
