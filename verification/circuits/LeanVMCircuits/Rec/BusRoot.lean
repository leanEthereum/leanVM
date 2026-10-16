module

public import LeanVMCircuits.Rec.Flocked

@[expose] public section

/-!
The bus GKR's root claim as the bus's honest roots, from the sides' certificates.

`checksGiveTable_of_parts` asks, of the GKR's root stage (`hG`): where the named root values are the trees' roots, the
table's root claim is the bus's honest pull and push roots on the committed witness. The trees' leaves are the sides'
stacked layers (`SideCert.stack`), so each root is the product of its side's blocks' leaves. `checkbind` checks the
blocks are `BusBlocks::new`'s (`sidesOk`, `recCoords`), which are one per bus slot (`recCoords_eq`: `busSlots` mapped
by `slotCoords`), at their residual terms' heights, within the layer and disjoint (`SideCert.fits`). A block's leaf at
row `z` is `β + Σ_i w_i c_i(z)`: its key coordinate is, on the pull side, the slot's key column, the slot's key below
`2^32` rows (`idxKey_val`), and on the push side its `Next` column; its limb coordinates are the slot's forms' terms
(`slotLeaf`), or the framework block's public value columns (`pubLeaf`). With the named weights the draw's `eqAt A i`
and `β` its first coordinate, each leaf is the slot's fingerprint leaf `β + fp_A(key, limbs)` (`SideCert.stack_leaf`),
and `level_stack` makes the trees' roots the honest roots.

`ChildCerts.roots`: where `checkbind`'s checks pass (`ChildCerts.Ok`) and the root stage's named values are its true
values (`tvals`), the root claim is the honest pull and push roots at a witness of heights `2^τ_T`, `τ_T ≤ 32`. What
stays: each owned table's residual term at `τ_T` and the framework block at `τ_pub` (the heights the parent reads,
the layout's); the draw's coordinates the named `β` and fingerprint weights (which `DrawCert.sem` gives at the bus draw);
the public value columns the witness's and each push side `Next` column its slot's class-next key (`pushKey`), the
public columns `SideCert.PubTrue` reads.

`checksGiveTable_certs` puts `tableParts_certs` and `checksGiveTable_of_parts` together: at the committed witness at each child's layout with the stack's columns (`certCols`), the honest public columns (`honestPub`) and the bus draw the oracle's challenges at the draw certificate's words (`certDraw`), the dumps' certificates give `ChecksGiveTable` and `RecParts.Ok`, the root premise from `ChildCerts.roots` with the named `β` and weights the draw's (`DrawCert.sem`, the parent's calls holding where its circuit is satisfied). Its premises left: the layout fitting the rows, the parent reading each child at its layout, the draw's transcript's squeezes answering the oracle, `SideCert.PubTrue` at the honest public columns, and the openings.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model AirLink Finset

/-- A bus slot's block on a side, as `recCoords` lists it: the public slot the framework's block, its key and four
value columns; an owned slot its table's block, its key and its forms' terms. -/
def slotCoords (pull : Bool) (p : Table × ℕ) : Option Table × List CoordD :=
  if p.1 = .pub then (none, keyCoord pull (firstSlot .pub) :: (List.range 4).map (CoordD.pub false))
  else (some p.1, keyCoord pull (firstSlot p.1 + p.2) ::
    ((AirLink.forms p.1).getD p.2 []).map fun f => .terms (formTerms f))

theorem pub_not_mem_ownedList : Table.pub ∉ ownedList := by decide

/-- `BusBlocks::new`'s blocks are the bus slots' blocks, in order. -/
theorem recCoords_eq (pull : Bool) : recCoords pull = busSlots.map (slotCoords pull) := by
  rw [recCoords, busSlots, List.map_cons, List.map_flatMap]
  refine congrArg₂ _ (by simp [slotCoords]) (List.flatMap_congr fun T hT => ?_)
  have hne : T ≠ .pub := fun h => pub_not_mem_ownedList (h ▸ hT)
  simp [slotCoords, hne]

/-- Every owned slot has four limbs. -/
theorem forms_slot_length : ∀ T ∈ ownedList, ∀ i < T.nSlots, ((AirLink.forms T).getD i []).length = 4 := by
  decide +kernel

/-- Non-vacuity of `recCoords_eq`: the bus has the public slot and 97 owned ones. -/
example : busSlots.length = 98 := by decide +kernel

/-- The framework block's leaf: `β` plus its key coordinate's value and its four public value columns at the first five
weights, the weights `eq(A, k)` and the columns `col`, is the bus tuple's `β + fp_A`. -/
theorem pubLeaf (pubF : Bool → ℕ → ℕ → E) (wv : ℕ → E) (A : Fin 4 → E)
    (h0 : wv 0 = UnionSound.eqAt A 0) (h1 : wv 1 = UnionSound.eqAt A 1) (h2 : wv 2 = UnionSound.eqAt A 2)
    (h3 : wv 3 = UnionSound.eqAt A 3) (h4 : wv 4 = UnionSound.eqAt A 4) (β : E) (k : CoordD) (kv : ℕ)
    (row : ℕ → E) (z : ℕ) (col : Fin 4 → K) (hcol : ∀ j (hj : j < 4), pubF false j z = emb (col ⟨j, hj⟩))
    (hk : ((k.ts pubF (wv 0)).map fun t => t.1 * t.2.val row z).sum = wv 0 * emb (ofWord kv)) :
    blockLeaf β (coordsTs pubF wv 0 (k :: (List.range 4).map (CoordD.pub false))) row z =
      β + UnionSound.fpAt A (busTuple (kv, col)) := by
  rw [show (List.range 4).map (CoordD.pub false) = [.pub false 0, .pub false 1, .pub false 2, .pub false 3] from rfl]
  simp only [blockLeaf, coordsTs, List.map_append, List.sum_append]
  rw [hk]
  simp only [CoordD.ts, DCoord.val, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, zero_add,
    Nat.reduceAdd, fpAt_busTuple]
  rw [hcol 0 (by norm_num), hcol 1 (by norm_num), hcol 2 (by norm_num), hcol 3 (by norm_num), h0, h1, h2, h3, h4]
  rfl

/-- Where the leaves agree on every block's rows, the stacked layers agree. -/
theorem stackLeaf_congr {m : ℕ} (κ q : Fin m → ℕ) (leaf leaf' : Fin m → ℕ → E)
    (h : ∀ b, ∀ z < 2 ^ κ b, leaf b z = leaf' b z) : stackLeaf κ q leaf = stackLeaf κ q leaf' := by
  funext x
  unfold stackLeaf
  split_ifs with hx
  · have hm := mem_Ico.mp hx.choose_spec
    exact h _ _ (by omega)
  · rfl

/-- `level_stack` over blocks counted by any `m` equal to the bus's slots, each block's leaves `g`'s on its rows. -/
theorem level_stack_of_eq (w : Witness) (taus : Table → ℕ) (hh : ∀ T, w.height T = 2 ^ taus T) (g : Slot → E)
    {n m : ℕ} (hm : m = busSlots.length) (κ q : Fin m → ℕ) (leaf : Fin m → ℕ → E)
    (hκ : ∀ b : Fin m, κ b = taus (busSlots[b.val]'(hm ▸ b.isLt)).1) (hin : ∀ b, 2 ^ κ b * q b + 2 ^ κ b ≤ 2 ^ n)
    (hdisj : ∀ b b', b ≠ b' → Disjoint (Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b))
      (Ico (2 ^ κ b' * q b') (2 ^ κ b' * q b' + 2 ^ κ b')))
    (hleaf : ∀ b : Fin m, ∀ z < 2 ^ κ b,
      leaf b z = g ((busSlots[b.val]'(hm ▸ b.isLt)).1, z, (busSlots[b.val]'(hm ▸ b.isLt)).2)) :
    level (stackLeaf κ q leaf) n 0 = ((slots w).map g).prod := by
  subst hm
  rw [stackLeaf_congr κ q leaf (fun b z => g (busSlots[b].1, z, busSlots[b].2)) hleaf]
  exact level_stack w taus hh g κ q _ hκ hin hdisj fun _ _ => rfl

/-- A side's blocks at a witness of heights `2^τ_T`, `τ_T ≤ 32`, each owned block at its table's `τ` and each
framework block at `τ_pub`, are one per bus slot, and each one's leaves are its slot's fingerprint leaves `g`, the
draw's `β` and weights the named ones: on the pull side each slot's key, on the push side its `Next` column's. Then
the side's stacked layer's root is the product of `g` over the slots. -/
theorem SideCert.stack_root {sc : SideCert} (hs : sc.shapeOk = true) (pull : Bool)
    (hrc : sc.blocks.map (fun b => (b.owner, b.coords)) = recCoords pull) (val : Val) (pubF : Bool → ℕ → ℕ → E)
    (w : Witness) (taus : Table → ℕ) (hh : ∀ T, w.height T = 2 ^ taus T) (h32 : ∀ T, taus T ≤ 32)
    (hκ : ∀ b : Fin sc.blocks.length, sc.blocks[b].kappa = taus (sc.blocks[b].owner.getD .pub))
    (f : Fin 5 → E) (hβ : f 0 = Model.ev val sc.beta)
    (hw : ∀ j (hj : j < 5), sc.wV val j = UnionSound.eqAt (Fin.tail f) ⟨j, by omega⟩)
    (hcol : ∀ j < 4, ∀ z, pubF false j z = emb (w.cols .pub z j)) (kv : Slot → ℕ)
    (hkey : ∀ T i z (row : ℕ → E), i < T.nSlots → z < 2 ^ 32 →
      (((keyCoord pull (firstSlot T + i)).ts pubF (sc.wV val 0)).map fun t => t.1 * t.2.val row z).sum =
        sc.wV val 0 * emb (ofWord (kv (T, z, i)))) :
    level (sc.stack val pubF w) sc.mu 0 =
      ((slots w).map fun e => f 0 + UnionSound.fpAt (Fin.tail f) (busTuple (kv e, carried w e))).prod := by
  have hlen : sc.blocks.length = busSlots.length := by
    rw [← List.length_map (f := fun b : BlockD => (b.owner, b.coords)), hrc, recCoords_eq, List.length_map]
  have hb : ∀ b : Fin sc.blocks.length,
      (sc.blocks[b].owner, sc.blocks[b].coords) = slotCoords pull (busSlots[b.val]'(hlen ▸ b.isLt)) := by
    intro b
    have hb' : b.val < busSlots.length := hlen ▸ b.isLt
    have h := congrArg (fun l => l[b.val]?) hrc
    simp only [List.getElem?_map, List.getElem?_eq_getElem b.isLt, Option.map_some, recCoords_eq,
      List.getElem?_eq_getElem hb'] at h
    exact Option.some.inj h
  obtain ⟨hfit, hdisj⟩ := SideCert.fits hs
  have hw' := hw
  refine level_stack_of_eq w taus hh _ hlen _ _ _ (fun b => ?_) (fun b => (hfit b).2.2) hdisj fun b z hzb => ?_
  · rw [hκ b]
    have := hb b
    unfold slotCoords at this
    split_ifs at this with hp
    · rw [(Prod.mk.inj this).1, Option.getD_none, hp]
    · rw [(Prod.mk.inj this).1, Option.getD_some]
  · set p := busSlots[b.val]'(hlen ▸ b.isLt) with hpdef
    have hpm : p ∈ busSlots := List.getElem_mem _
    have hbp := hb b
    rw [← hpdef] at hbp
    have hz32 : z < 2 ^ 32 := by
      refine lt_of_lt_of_le hzb (Nat.pow_le_pow_right (by norm_num) ?_)
      rw [hκ b]
      exact h32 _
    unfold slotCoords at hbp
    split_ifs at hbp with hp
    · obtain ⟨ho, hc⟩ := Prod.mk.inj hbp
      have hp2 : p.2 = 0 := by
        simp only [busSlots, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_range] at hpm
        rcases hpm with hpm | ⟨T, hT, i, -, hTi⟩
        · rw [hpm]
        · rw [← hTi] at hp
          exact absurd (hp ▸ hT) pub_not_mem_ownedList
      simp only [ho, if_true, SideCert.leafOf, SideCert.tsOf, BlockD.ts, hc]
      rw [hβ]
      have hk := hkey .pub 0 z (fun _ => 0) (by decide) hz32
      rw [show firstSlot .pub + 0 = firstSlot .pub from rfl] at hk
      rw [pubLeaf pubF (sc.wV val) (Fin.tail f) (hw' 0 (by norm_num)) (hw' 1 (by norm_num)) (hw' 2 (by norm_num))
        (hw' 3 (by norm_num)) (hw' 4 (by norm_num)) _ _ (kv (.pub, z, 0)) (fun _ => 0) z (fun j => w.cols .pub z j)
        (fun j hj => hcol j hj z) hk]
      rw [hp, hp2]
      congr 3
      refine Prod.ext rfl (funext fun j => ?_)
      fin_cases j <;> rfl
    · obtain ⟨ho, hc⟩ := Prod.mk.inj hbp
      have hown : p.1 ∈ ownedList ∧ p.2 < p.1.nSlots := by
        simp only [busSlots, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_range] at hpm
        rcases hpm with hpm | ⟨T, hT, i, hi, hTi⟩
        · exact absurd (by rw [hpm]) hp
        · rw [← hTi]
          exact ⟨hT, hi⟩
      simp only [ho, reduceCtorEq, if_false, Option.getD_some, SideCert.tsOf, BlockD.ts, hc]
      rw [hβ]
      exact slotLeaf pubF (sc.wV val) (Fin.tail f) (hw' 0 (by norm_num)) (hw' 1 (by norm_num)) (hw' 2 (by norm_num))
        (hw' 3 (by norm_num)) (hw' 4 (by norm_num)) _ _ (kv (p.1, z, p.2)) _
        (forms_slot_length p.1 hown.1 p.2 hown.2) (w.cols p.1 z) z (hkey p.1 p.2 z _ hown.2 hz32)

end LeanVMCircuits.Rec.Bind

namespace LeanVMCircuits.Rec.Edges

open LeanVMCircuits.Rec Model AirLink Finset LeanVMCircuits.Rec.Bind

/-- `checksGiveTable_of_parts`' root premise on the dumps' certificates: where `checkbind`'s checks pass and the root
stage's named values are its true values, the table's root claim is the bus's honest pull and push roots at a witness
of heights `2^τ_T`, `τ_T ≤ 32`. Left: each owned table's residual term at `τ_T` and the framework block at `τ_pub`;
the draw's first coordinate the named `β` and its fingerprint weights the named ones; the public value columns the
witness's, and each push side `Next` column its slot's class-next key. -/
theorem ChildCerts.roots {cc : ChildCerts} {c : Cert} {s : State} (hcc : cc.Ok c s c.outs) (ρ : ℕ → K) (val : Val)
    (pubF0 pubF1 : Bool → ℕ → ℕ → E) (w : Witness) (t : State) (taus : Table → ℕ)
    (hh : ∀ T, w.height T = 2 ^ taus T) (h32 : ∀ T, taus T ≤ 32)
    (hτ : ∀ T ∈ owned, (cc.rc.termOf T).tau = taus T) (hτp : (cc.s0.blocks.headD default).kappa = taus .pub)
    (f : Fin 5 → E) (hβ : f 0 = Model.ev val cc.s0.beta)
    (hw : ∀ j (hj : j < 5), cc.s0.wV val j = UnionSound.eqAt (Fin.tail f) ⟨j, by omega⟩)
    (hcol0 : ∀ j < 4, ∀ z, pubF0 false j z = emb (w.cols .pub z j))
    (hcol1 : ∀ j < 4, ∀ z, pubF1 false j z = emb (w.cols .pub z j))
    (hnext : ∀ T i z, i < T.nSlots → pubF0 true (firstSlot T + i) z = emb (ofWord (pushKey t w (T, z, i))))
    (hv : cc.vals c val 0 = cc.tvals c ρ val pubF0 pubF1 w 0) :
    Model.ev val cc.tc.root = pullRoot t w f ∧ Model.ev val cc.tc.root = pushRoot t w f := by
  obtain ⟨-, hg, -, -, -, hs, -⟩ := hcc
  simp only [GkrCert.okIn, Bool.and_eq_true, beq_iff_eq] at hg
  have hst := hg.1.2
  simp only [sidesOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hmu⟩, hw1⟩, hb1⟩, -⟩, -⟩, hrc0⟩, hrc1⟩, hall⟩ := hs
  have hs0 : cc.s0.shapeOk = true := by simp only [SideCert.ok, Bool.and_eq_true] at h0; exact h0.1
  have hs1 : cc.s1.shapeOk = true := by simp only [SideCert.ok, Bool.and_eq_true] at h1; exact h1.1
  -- Each block's height: an owned block its residual term's, the framework's the first block's.
  have hκ : ∀ x ∈ cc.s0.blocks ++ cc.s1.blocks, (∀ T, x.owner = some T → T ∈ owned) →
      x.kappa = taus (x.owner.getD .pub) := fun x hx hown => by
    have := hall x hx
    cases ho : x.owner with
    | none => rw [ho] at this; rw [Option.getD_none, ← hτp]; exact beq_iff_eq.mp this
    | some T => rw [ho] at this; rw [Option.getD_some, ← hτ T (hown T ho)]; exact beq_iff_eq.mp this
  have hκ0 : ∀ b : Fin cc.s0.blocks.length, cc.s0.blocks[b].kappa = taus (cc.s0.blocks[b].owner.getD .pub) :=
    fun b => hκ _ (List.mem_append_left _ (List.getElem_mem _)) ((SideCert.fits hs0).1 b).2.1
  have hκ1 : ∀ b : Fin cc.s1.blocks.length, cc.s1.blocks[b].kappa = taus (cc.s1.blocks[b].owner.getD .pub) :=
    fun b => hκ _ (List.mem_append_right _ (List.getElem_mem _)) ((SideCert.fits hs1).1 b).2.1
  have hwv1 : ∀ j, cc.s1.wV val j = cc.s0.wV val j := fun j => by simp only [SideCert.wV, hw1]
  -- The root stage: both named values the root, both true values the trees' roots.
  have hroot : ∀ i : Fin 2, Model.ev val cc.tc.root = level (cc.leaf val pubF0 pubF1 w i) cc.s0.mu 0 := fun i => by
    have h := congrFun hv i
    simp only [ChildCerts.vals, ChildCerts.tvals, GkrCert.outsAt, GkrCert.ptR, mleL_nil, List.length_nil,
      Nat.sub_zero, hst] at h
    rw [← h]
    fin_cases i <;> rfl
  refine ⟨?_, ?_⟩
  · rw [hroot 1, pullRoot_eq_slots]
    simp only [ChildCerts.leaf, one_ne_zero, if_false, Fin.isValue, Fin.val_one]
    rw [← hmu]
    refine SideCert.stack_root hs1 true hrc1 val pubF1 w taus hh h32 hκ1 f (by rw [hβ, hb1]) (fun j hj => by
      rw [hwv1]; exact hw j hj) (fun j hj z => hcol1 j hj z) key fun T i z row _ hz => ?_
    rw [hwv1, keyCoord, if_pos rfl]
    exact idxKey_val pubF1 _ row _ z hz
  · rw [hroot 0, pushRoot_eq_slots]
    simp only [ChildCerts.leaf, if_true, Fin.isValue, Fin.val_zero]
    refine SideCert.stack_root hs0 false hrc0 val pubF0 w taus hh h32 hκ0 f hβ hw (fun j hj z => hcol0 j hj z)
      (pushKey t w) fun T i z row hi _ => ?_
    simp only [keyCoord, Bool.false_eq_true, if_false, CoordD.ts, DCoord.val, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    rw [hnext T i z hi]

/-! The table premise on the dumps' certificates. -/

/-- The committed columns as the stack holds them (`RecLayout::sources`): the hash table's first 18 columns the `HASH`
region's words, column `c` at row `b` word `c` of block `b`, blocks of `2^h` words; every other column the committed
one. -/
def portCols (cols : Table → ℕ → ℕ → K) (h : ℕ) (wd : ℕ → K) : Table → ℕ → ℕ → K :=
  fun T b c => if T = .hash ∧ c < 18 then wd (c + 2 ^ h * b) else cols T b c

/-- The witness at a layout of the stack's columns is the stack's witness. -/
theorem ported_committedAt (s : State) (st : ℕ → Fin 4 → K) (taus : Table → ℕ) (cols : Table → ℕ → ℕ → K) (h : ℕ)
    (wd : ℕ → K) :
    ported (committedAt s st taus (portCols cols h wd)) h wd = committedAt s st taus (portCols cols h wd) := by
  simp only [ported, committedAt, Witness.mk.injEq, true_and]
  funext T b c
  by_cases h1 : T = .hash ∧ c < 18
  · obtain ⟨rfl, hc⟩ := h1
    simp [portCols, hc]
  · simp only [h1, if_false]

/-- The bus slot numbered `j` (`firstSlot T + i`). -/
def slotOf (j : ℕ) : Table × ℕ := (busSlots.find? fun p => firstSlot p.1 + p.2 == j).getD (.pub, 0)

theorem slotOf_firstSlot : ∀ T : Table, ∀ i < T.nSlots, slotOf (firstSlot T + i) = (T, i) := by
  intro T
  cases T <;> decide +kernel

/-- The public columns a side reads at their honest values: each slot's `Next` column its class-next key (`pushKey`), each value column the witness's. Taken at the circuit with its public rows in the Rust order (`stmtFirst`), these are the columns the Rust verifier evaluates. -/
noncomputable def honestPub (s : State) (w : Witness) : Bool → ℕ → ℕ → E := fun nx j z =>
  if nx then emb (ofWord (pushKey s w ((slotOf j).1, z, (slotOf j).2))) else emb (w.cols .pub z j)

/-- Non-vacuity of `slotOf`: slot 97 is the public table's, slot 8 the hash table's first. -/
example : slotOf 97 = (.pub, 0) ∧ slotOf 8 = (.hash, 0) := by decide +kernel

variable {ι Ω : Type}

/-- Each node's valuation at its oracle answers. -/
def certVal (valR : ι → (ℕ → K) → Val) (ρ : ι → Ω → ℕ → K) : ι → Ω → Val := fun p ω => valR p (ρ p ω)

/-- Each child's columns at an outcome, the stack's. -/
def certCols (cc : ι → ChildCerts) (colsC : ι → Ω → Table → ℕ → ℕ → K) (hr : (v : ι) → Ω → HashRegion (cc v)) :
    ι → Ω → Table → ℕ → ℕ → K := fun v ω => portCols (colsC v ω) (cc v).lsc.rounds.length (hr v ω).wd

/-- Each child's bus draw `(β, A)` at an outcome: the oracle's challenges at its draw certificate's words in its parent's (`DrawCert.own`). -/
noncomputable def certDraw (T : TreeSound.Tree ι) (bc : ι → Cert) (cc : ι → ChildCerts) (ρ : ι → Ω → ℕ → K) :
    ι → Ω → Fin 5 → E := fun v ω => readR ((cc v).dr.own (bc (T.parent v)).outs) (ρ (T.parent v) ω)

theorem ChildCerts.drawOk {cc : ChildCerts} {c : Cert} {s : State} {os : Array (List ℕ)} (h : cc.Ok c s os) :
    cc.dr.ok os s c.calls c.relax c.transcripts cc.s0 = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := h
  exact h

/-- The checks from the bus GKR's root to the opening on the dumps' certificates, child `v`'s in its parent's, at the
committed witness `W` with the honest public columns. -/
noncomputable def certParts [Fintype Ω] (T : TreeSound.Tree ι) (t : ι → State) (bc : ι → Cert)
    (valR : ι → (ℕ → K) → Val) (ρ : ι → Ω → ℕ → K) (cc : ι → ChildCerts) (W : ι → Ω → Witness)
    (hr : (v : ι) → Ω → HashRegion (cc v)) (T' : ι → Ω → ℕ → E) (opened : ι → Ω → Prop) (pcsBad crBad : ι → Finset Ω) :
    RecParts ι Ω :=
  tableParts (fun v => (cc v).G) (fun v k ω => (cc v).vals (bc (T.parent v)) (certVal valR ρ (T.parent v) ω) k)
    (fun v k ω => (cc v).tvals (bc (T.parent v)) (ρ (T.parent v) ω) (certVal valR ρ (T.parent v) ω)
      (honestPub (stmtFirst (t v)) (W v ω)) (honestPub (stmtFirst (t v)) (W v ω)) (W v ω) k)
    (fun v ω => (cc v).tin (certVal valR ρ (T.parent v) ω) (W v ω)) (fun v ω => Flocked (stmtFirst (t v)) (W v ω)) opened
    (fun v => (cc v).layerBad (bc (T.parent v)) (t (T.parent v)) (valR (T.parent v)) (ρ (T.parent v))
      (fun ω => honestPub (stmtFirst (t v)) (W v ω)) (fun ω => honestPub (stmtFirst (t v)) (W v ω)) (W v))
    (fun v => (cc v).balBad (fun ω => certVal valR ρ (T.parent v) ω) (W v))
    (fun v => (cc v).tabBad (bc (T.parent v)) (t (T.parent v)) (valR (T.parent v)) (ρ (T.parent v)) (W v) (T' v))
    (fun v => (cc v).flBad (bc (T.parent v)) (t (T.parent v)) (bc (T.parent v)).outs (valR (T.parent v))
      (ρ (T.parent v)) (hr v) (T' v)) pcsBad crBad

/-- `ChecksGiveTable` and `RecParts.Ok` on the dumps' certificates: child `v`'s certificates `cc v` in its parent's
(passing `checkbind`'s checks), at the committed witness at its layout `taus v` with the stack's columns (`witAt`,
`certCols`), the public columns the honest ones (`honestPub`). `checksGiveTable_of_parts`' premises are discharged:
the table's input claim from `tin`, flock's from `Flocked`, the root from `ChildCerts.roots`; `tableParts_certs`'s
residual heights are `hτ`'s, its hash rows within the layout's height. What stays: the layout fitting the rows
(`hlay`, which `layoutFits_converge` gives); the parent reading each child at its layout (`hτ`: each owned table's
residual term at `τ_T`; `hτp`: the framework block at `τ_pub`), the building fact `checksGiveRows_of_converge` states
of the tree; the draw's transcript's squeezes answering the oracle (`hans`, a run's `Run.ans`), whence the draw's `β` and fingerprint weights are the named ones (`DrawCert.sem`); the
honest public columns' values (`hpub`, `SideCert.PubTrue`); and the openings off `pcsBad`. The bus draw is the oracle's challenges at the draw certificate's words (`certDraw`). The child's side is its circuit with its public rows in the Rust order (`stmtFirst (t v)`), the order of the public columns, keys and bus roots the verifier evaluates; as first stated at `t v`, in the model's building order, `hpub` could not hold on an honest run. The certificates are checked on the parents' replayed circuits `t`. -/
theorem checksGiveTable_certs [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (L : Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K) (bc : ι → Cert)
    (valR : ι → (ℕ → K) → Val) (ρ : ι → Ω → ℕ → K) (cc : ι → ChildCerts)
    (hacc : ∀ v, (bc (T.parent v)).accepts (t (T.parent v)) = true)
    (hcc : ∀ v, (cc v).Ok (bc (T.parent v)) (t (T.parent v)) (bc (T.parent v)).outs)
    (st : ι → Ω → ℕ → Fin 4 → K) (taus : ι → Table → ℕ) (colsC : ι → Ω → Table → ℕ → ℕ → K)
    (hr : (v : ι) → Ω → HashRegion (cc v)) (T' : ι → Ω → ℕ → E)
    (pcsBad crBad : ι → Finset Ω) (opened : ι → Ω → Prop)
    (hlay : ∀ v, LayoutFits (t v) (taus v)) (hτ : ∀ v, ∀ T' ∈ owned, ((cc v).rc.termOf T').tau = taus v T')
    (hτp : ∀ v, ((cc v).s0.blocks.headD default).kappa = taus v .pub)
    (hans : ∀ v ω, ∀ p ∈ chalSeeds (t (T.parent v)) ((bc (T.parent v)).transcripts.getD (cc v).dr.tr default),
      nu (certVal valR ρ (T.parent v) ω) p.2 = ρ (T.parent v) ω p.2)
    (hpub : ∀ v ω, RunHeld (bc (T.parent v)) (t (T.parent v)) (bc (T.parent v)).outs (st v ω) (valR (T.parent v))
        (ρ (T.parent v) ω) →
      (cc v).s0.PubTrue (certVal valR ρ (T.parent v) ω)
          (honestPub (stmtFirst (t v)) (witAt T cert (fun v => stmtFirst (t v)) slot stRoot (certVal valR ρ) taus (certCols cc colsC hr) v ω)) ∧
        (cc v).s1.PubTrue (certVal valR ρ (T.parent v) ω)
          (honestPub (stmtFirst (t v)) (witAt T cert (fun v => stmtFirst (t v)) slot stRoot (certVal valR ρ) taus (certCols cc colsC hr) v ω)))
    (hopT : ∀ v ω, opened v ω → (cc v).tabOpened (certVal valR ρ (T.parent v) ω)
      (witAt T cert (fun v => stmtFirst (t v)) slot stRoot (certVal valR ρ) taus (certCols cc colsC hr) v ω) (T' v ω))
    (hopF : ∀ v ω, opened v ω → (cc v).flOpened (bc (T.parent v)).outs (certVal valR ρ (T.parent v) ω) (hr v ω))
    (hhintL : ∀ v ω, opened v ω → ∀ x ∈ (cc v).lsc.hints, Model.ev (certVal valR ρ (T.parent v) ω) x = T' v ω x)
    (hopen : ∀ v ω, ω ∉ pcsBad v → opened v ω) :
    ChecksGiveTable T cert (fun v => stmtFirst (t v)) os L slot stRoot (certVal valR ρ)
        (certParts T t bc valR ρ cc (witAt T cert (fun v => stmtFirst (t v)) slot stRoot (certVal valR ρ) taus (certCols cc colsC hr)) hr T'
          opened pcsBad crBad)
        (fun v => (cc v).tsc.rounds.length)
        (fun v ω => ((cc v).zetaV (certVal valR ρ (T.parent v) ω),
          Model.ev (certVal valR ρ (T.parent v) ω) (cc v).tc.xi))
        (fun v ω _ => (cc v).rc.formsV (certVal valR ρ (T.parent v) ω))
        (fun v ω _ i => Model.ev (certVal valR ρ (T.parent v) ω) (if i = 0 then (cc v).tc.tot0 else (cc v).tc.tot1))
        (fun v ω _ => Model.ev (certVal valR ρ (T.parent v) ω) (cc v).tc.root) (certDraw T bc cc ρ) taus
        (certCols cc colsC hr) ∧
      (certParts T t bc valR ρ cc (witAt T cert (fun v => stmtFirst (t v)) slot stRoot (certVal valR ρ) taus (certCols cc colsC hr)) hr T'
          opened pcsBad crBad).Ok
        (fun v ω => RunHeld (bc (T.parent v)) (t (T.parent v)) (bc (T.parent v)).outs (st v ω) (valR (T.parent v))
          (ρ (T.parent v) ω)) := by
  set W := witAt T cert (fun v => stmtFirst (t v)) slot stRoot (certVal valR ρ) taus (certCols cc colsC hr) with hW
  have hwit : ∀ v ω, (cc v).wit (W v ω) (hr v ω) = W v ω := fun v ω => by
    simp only [hW, witAt, certCols, ChildCerts.wit]
    exact ported_committedAt _ _ _ _ _ _
  have hh : ∀ v ω T', (W v ω).height T' = 2 ^ taus v T' := fun _ _ _ => rfl
  have htau : ∀ v ω, ∀ T' ∈ owned, ((cc v).rc.termOf T').tau = tauOf (W v ω) T' := fun v ω T' hT' => by
    rw [hτ v T' hT', hW, witAt, tauOf_committedAt]
  refine ⟨checksGiveTable_of_parts T cert (fun v => stmtFirst (t v)) os L slot stRoot (certVal valR ρ) (fun v => (cc v).G)
    _ _ _ _ opened _ _ _ _ pcsBad crBad _ _ _ (certDraw T bc cc ρ) taus (certCols cc colsC hr) bc (fun v => (cc v).tc) t
    (fun _ _ _ h => sat_stmtFirst.mp h)
    (fun v _ _ => ⟨hacc v, (hcc v).1⟩) (fun _ _ => rfl) (fun v ω sc hsc hin => ?_) (fun v ω hf hv => ?_)
    (fun v ω hfl => hfl), ?_⟩
  · have h8 := (hcc v).2.2.2.2.2.2.2.1
    rw [h8] at hsc
    cases Option.some.inj hsc
    exact hin
  · have hd := DrawCert.sem hf (ChildCerts.drawOk (hcc v)) (hans v ω)
    refine ChildCerts.roots (hcc v) (ρ (T.parent v) ω) _ _ _ (W v ω) (stmtFirst (t v)) (taus v) (hh v ω)
      (fun T' => (hlay v T').2)
      (hτ v) (hτp v) (certDraw T bc cc ρ v ω) hd.1 hd.2 (fun j _ z => ?_) (fun j _ z => ?_) (fun T' i z hi => ?_)
      hv
    · simp [honestPub]
    · simp [honestPub]
    · simp [honestPub, slotOf_firstSlot T' i hi]
  · have := tableParts_certs (fun v => bc (T.parent v)) (fun v => t (T.parent v)) hacc st (fun v => valR (T.parent v))
      (fun v => ρ (T.parent v)) cc hcc (fun v => stmtFirst (t v)) W hr T' (fun v ω => honestPub (stmtFirst (t v)) (W v ω))
      (fun v ω => honestPub (stmtFirst (t v)) (W v ω)) pcsBad crBad opened hpub htau
      (fun v ω => (hlay v .hash).1) (fun v ω ho => by rw [hwit]; exact hopT v ω ho) hopF hhintL hopen
    simp only [hwit] at this
    exact this

/-- The openings child `v`'s checks take at outcome `ω`: the table sumcheck's column claims and hints the opened values `T'` at the committed witness (`tabOpened`), flock's ring switch target and matrix (`flOpened`), and the lincheck's hints the opened values. -/
def certOpened (T : TreeSound.Tree ι) (bc : ι → Cert) (valR : ι → (ℕ → K) → Val) (ρ : ι → Ω → ℕ → K)
    (cc : ι → ChildCerts) (W : ι → Ω → Witness) (hr : (v : ι) → Ω → HashRegion (cc v)) (T' : ι → Ω → ℕ → E) :
    ι → Ω → Prop := fun v ω =>
  (cc v).tabOpened (certVal valR ρ (T.parent v) ω) (W v ω) (T' v ω) ∧
    (cc v).flOpened (bc (T.parent v)).outs (certVal valR ρ (T.parent v) ω) (hr v ω) ∧
    ∀ x ∈ (cc v).lsc.hints, Model.ev (certVal valR ρ (T.parent v) ω) x = T' v ω x

open Classical in
/-- The outcomes at which an opening child `v`'s checks take fails: the event #551 bounds (`PcsBound` of the parts, through `Pcs551.sub`). -/
noncomputable def openBad [Fintype Ω] (opened : ι → Ω → Prop) : ι → Finset Ω := fun v => {ω | ¬ opened v ω}

/-- `checksGiveTable_certs` with the openings as #551's interface: `opened` the openings the checks take (`certOpened`) and `pcsBad` the outcomes at which one fails (`openBad`), so the opening premises hold by definition and what they asked is the parts' `PcsBound` (#551's theorem bounding `openBad`, `Pcs551`). -/
theorem checksGiveTable_opened [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (L : Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K) (bc : ι → Cert)
    (valR : ι → (ℕ → K) → Val) (ρ : ι → Ω → ℕ → K) (cc : ι → ChildCerts)
    (hacc : ∀ v, (bc (T.parent v)).accepts (t (T.parent v)) = true)
    (hcc : ∀ v, (cc v).Ok (bc (T.parent v)) (t (T.parent v)) (bc (T.parent v)).outs)
    (st : ι → Ω → ℕ → Fin 4 → K) (taus : ι → Table → ℕ) (colsC : ι → Ω → Table → ℕ → ℕ → K)
    (hr : (v : ι) → Ω → HashRegion (cc v)) (T' : ι → Ω → ℕ → E) (crBad : ι → Finset Ω)
    (hlay : ∀ v, LayoutFits (t v) (taus v)) (hτ : ∀ v, ∀ T' ∈ owned, ((cc v).rc.termOf T').tau = taus v T')
    (hτp : ∀ v, ((cc v).s0.blocks.headD default).kappa = taus v .pub)
    (hans : ∀ v ω, ∀ p ∈ chalSeeds (t (T.parent v)) ((bc (T.parent v)).transcripts.getD (cc v).dr.tr default),
      nu (certVal valR ρ (T.parent v) ω) p.2 = ρ (T.parent v) ω p.2)
    (hpub : ∀ v ω, RunHeld (bc (T.parent v)) (t (T.parent v)) (bc (T.parent v)).outs (st v ω) (valR (T.parent v))
        (ρ (T.parent v) ω) →
      (cc v).s0.PubTrue (certVal valR ρ (T.parent v) ω)
          (honestPub (stmtFirst (t v)) (witAt T cert (fun v => stmtFirst (t v)) slot stRoot (certVal valR ρ) taus
            (certCols cc colsC hr) v ω)) ∧
        (cc v).s1.PubTrue (certVal valR ρ (T.parent v) ω)
          (honestPub (stmtFirst (t v)) (witAt T cert (fun v => stmtFirst (t v)) slot stRoot (certVal valR ρ) taus
            (certCols cc colsC hr) v ω))) :
    let W := witAt T cert (fun v => stmtFirst (t v)) slot stRoot (certVal valR ρ) taus (certCols cc colsC hr)
    let opened := certOpened T bc valR ρ cc W hr T'
    ChecksGiveTable T cert (fun v => stmtFirst (t v)) os L slot stRoot (certVal valR ρ)
        (certParts T t bc valR ρ cc W hr T' opened (openBad opened) crBad)
        (fun v => (cc v).tsc.rounds.length)
        (fun v ω => ((cc v).zetaV (certVal valR ρ (T.parent v) ω),
          Model.ev (certVal valR ρ (T.parent v) ω) (cc v).tc.xi))
        (fun v ω _ => (cc v).rc.formsV (certVal valR ρ (T.parent v) ω))
        (fun v ω _ i => Model.ev (certVal valR ρ (T.parent v) ω) (if i = 0 then (cc v).tc.tot0 else (cc v).tc.tot1))
        (fun v ω _ => Model.ev (certVal valR ρ (T.parent v) ω) (cc v).tc.root) (certDraw T bc cc ρ) taus
        (certCols cc colsC hr) ∧
      (certParts T t bc valR ρ cc W hr T' opened (openBad opened) crBad).Ok
        (fun v ω => RunHeld (bc (T.parent v)) (t (T.parent v)) (bc (T.parent v)).outs (st v ω) (valR (T.parent v))
          (ρ (T.parent v) ω)) :=
  checksGiveTable_certs T cert t os L slot stRoot bc valR ρ cc hacc hcc st taus colsC hr T' _ crBad _ hlay hτ hτp
    hans hpub (fun _ _ h => h.1) (fun _ _ h => h.2.1) (fun _ _ h => h.2.2)
    (fun v ω h => by simpa [openBad] using h)

end LeanVMCircuits.Rec.Edges
