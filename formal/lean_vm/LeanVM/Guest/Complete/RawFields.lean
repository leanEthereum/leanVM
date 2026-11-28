/-
  LeanVM.Guest.Complete.RawFields

  `MainCalleesAt`'s fields `rawx` and `raws`: the raw signatures' loops at `main`'s honest
  arguments, placed at every frame past the exponent tables.
-/

module

public import LeanVM.Guest.Complete.RawSA
public import LeanVM.Guest.Complete.MainHypAt
public import LeanVM.Guest.Complete.ClaimCells
public import LeanVM.Guest.Complete.MainDup
public import LeanVM.Guest.Complete.CoverageEq
public import LeanVM.Guest.B1.Main.Plan
public import LeanVM.Guest.B1.Main.Basic
public import LeanVM.Guest.B1.Sig.XmssSegCoreC
public import LeanVM.Guest.B1.Sig.Bytes
public import LeanVM.Facts.ClaimBytes

/-!
# The raw signatures' fields

On a node with `NodeRelation`, `DeployedLimits` and `ChildrenOk`, at `17 ≤ k`, and for every
coverage table `cover` of `sx + ss` marks holding the raw signatures' marks (`RawMarks`: raw
leanXMSS signature `i`'s slot `g^i`, raw leanSPHINCS signature `i`'s, after the leanXMSS region,
`g^(nrx + i)`), the fields `rawx` (`rawx_field`) and `raws` (`raws_field`) of `MainCalleesAt` (and
`MainCalleesOpenAt`) hold.

The raw index's range check reads the words at indices below the slots, defined on every memory
`MainPreA` admits at `17 ≤ k` (`count_def`: below `2^17` by `LowDef`, above `main`'s frame by
`main`'s words). The claims' cells are read off `main`'s tables at their slots (`xslot_claim`,
`tableX_at`, the four cells of a claim `claimCells4`), the coverage marks off `cover`, the byte
table off its run.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.Value.Keccak
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## A claim's four cells -/

theorem cellOfBytes_cellsBytes_cons (x : E) (xs : List E) : Prover.cellOfBytes (cellsBytes (x :: xs)) = x := by
  conv_rhs => rw [eq_ofLimbs x]
  rw [Prover.cellOfBytes, leLane_cellsBytes, leLane_cellsBytes]
  simp

theorem cellsOfBytes_cellsBytesR (l : List E) : Prover.cellsOfBytes (cellsBytes l) = l := by
  rw [Prover.cellsOfBytes, length_cellsBytes, Nat.mul_div_cancel_left _ (by norm_num : 0 < 16)]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [← cellsBytes_drop, List.drop_eq_getElem_cons h2, cellOfBytes_cellsBytes_cons]

/-- **A claim's four cells**: its key's two halves, its message's halves. -/
theorem claimCells4 (a b : BitVec 128) (m : BitVec 256) :
    Prover.cellsOfBytes (claimBytesOf a b m) = [Sig.cellOf128 a, Sig.cellOf128 b,
      Sig.cellOf128 (m.extractLsb' 0 128), Sig.cellOf128 (m.extractLsb' 128 128)] := by
  conv_lhs => rw [← Sig.cellVal_cellOf128 a, ← Sig.cellVal_cellOf128 b, ← Sig.cellPairVal_cellOf128 m,
    B1.Main.claimBytes_cells]
  exact cellsOfBytes_cellsBytesR _

theorem xCells_eq (c : LeanXmssClaim) : xCells c = [Sig.cellOf128 c.1.root, Sig.cellOf128 c.1.parameter,
    Sig.cellOf128 (c.2.extractLsb' 0 128), Sig.cellOf128 (c.2.extractLsb' 128 128)] := by
  simp only [xCells, claimBytes_xmss]; exact claimCells4 _ _ _

theorem sCells_eq (c : LeanSphincsClaim) : sCells c = [Sig.cellOf128 c.1.publicSeed, Sig.cellOf128 c.1.root,
    Sig.cellOf128 (c.2.extractLsb' 0 128), Sig.cellOf128 (c.2.extractLsb' 128 128)] := by
  simp only [sCells, claimBytes_sphincs]; exact claimCells4 _ _ _

theorem claimAt_of_readsAt {rd : Reader} {p a b c d : E} :
    ∀ xs : List E, xs = [a, b, c, d] → ReadsAt rd p xs → Sig.ClaimAt rd p a b c d := by
  rintro _ rfl h
  exact ⟨h 0 (by simp), h 1 (by simp), h 2 (by simp), h 3 (by simp)⟩

/-- **The leanXMSS table's slot `t`**, read. -/
theorem tableX_at {rd : Reader} {T : ℕ} {l : List LeanXmssClaim} (h : ReadsAt rd (ptrAt T) (l.flatMap xCells))
    {t : ℕ} {c : LeanXmssClaim} (ht : l[t]? = some c) :
    Sig.ClaimAt rd (ptrAt T * gen ^ (4 * t)) (Sig.cellOf128 c.1.root) (Sig.cellOf128 c.1.parameter)
      (Sig.cellOf128 (c.2.extractLsb' 0 128)) (Sig.cellOf128 (c.2.extractLsb' 128 128)) := by
  obtain ⟨htl, rfl⟩ := List.getElem?_eq_some_iff.mp ht
  exact claimAt_of_readsAt _ (xCells_eq _)
    (B1.Main.readsAt_flatMap_of (w := 4) l (fun a _ => xCells_length a) h t htl)

/-- **The leanSPHINCS table's slot `t`**, read. -/
theorem tableS_at {rd : Reader} {T : ℕ} {l : List LeanSphincsClaim} (h : ReadsAt rd (ptrAt T) (l.flatMap sCells))
    {t : ℕ} {c : LeanSphincsClaim} (ht : l[t]? = some c) :
    Sig.ClaimAt rd (ptrAt T * gen ^ (4 * t)) (Sig.cellOf128 c.1.publicSeed) (Sig.cellOf128 c.1.root)
      (Sig.cellOf128 (c.2.extractLsb' 0 128)) (Sig.cellOf128 (c.2.extractLsb' 128 128)) := by
  obtain ⟨htl, rfl⟩ := List.getElem?_eq_some_iff.mp ht
  exact claimAt_of_readsAt _ (sCells_eq _)
    (B1.Main.readsAt_flatMap_of (w := 4) l (fun a _ => sCells_length a) h t htl)

/-! ## The raw slots -/

theorem xDirect_length (s : NodeStatement) (w : NodeWitness) :
    (xPlan s w).directSlots.length = w.xmssSignatures.length := by
  have e := coveragePlan_eq s.claims.xmss (w.xmssSignatures.map (·.1)) (w.children.map (·.statement.claims.xmss))
  simp only [xPlan]
  rw [e.2.1, B1.Main.plan_raw_length, List.length_map]

theorem sDirect_length (s : NodeStatement) (w : NodeWitness) :
    (sPlan s w).directSlots.length = w.sphincsSignatures.length := by
  have e := coveragePlan_eq s.claims.sphincs (w.sphincsSignatures.map (·.1))
    (w.children.map (·.statement.claims.sphincs))
  simp only [sPlan]
  rw [e.2.1, B1.Main.plan_raw_length, List.length_map]

/-- A raw leanXMSS signature's slot is in the leanXMSS region. -/
theorem xslot_lt {s : NodeStatement} {w : NodeWitness} {x : ℕ} (hx : x ∈ (xPlan s w).directSlots) :
    x < (mainCounts s w).sx := by
  have e := coveragePlan_eq s.claims.xmss (w.xmssSignatures.map (·.1)) (w.children.map (·.statement.claims.xmss))
  have hmem : x ∈ B1.Main.slotsOf (Coverage.coveragePlan s.claims.xmss (w.xmssSignatures.map (·.1))
      (w.children.map (·.statement.claims.xmss))) := by
    unfold B1.Main.slotsOf
    exact List.mem_append_left _ (e.2.1 ▸ hx)
  have := B1.Main.plan_lt _ _ _ _ hmem
  rw [List.length_append, ← e.1] at this
  exact this

/-- A raw leanSPHINCS signature's slot is in the leanSPHINCS region. -/
theorem sslot_lt {s : NodeStatement} {w : NodeWitness} {x : ℕ} (hx : x ∈ (sPlan s w).directSlots) :
    x < (mainCounts s w).ss := by
  have e := coveragePlan_eq s.claims.sphincs (w.sphincsSignatures.map (·.1))
    (w.children.map (·.statement.claims.sphincs))
  have hmem : x ∈ B1.Main.slotsOf (Coverage.coveragePlan s.claims.sphincs (w.sphincsSignatures.map (·.1))
      (w.children.map (·.statement.claims.sphincs))) := by
    unfold B1.Main.slotsOf
    exact List.mem_append_left _ (e.2.1 ▸ hx)
  have := B1.Main.plan_lt _ _ _ _ hmem
  rw [List.length_append, ← e.1] at this
  exact this

/-- **The leanXMSS table holds raw signature `i`'s claim at its slot.** -/
theorem xslot_claim {s : NodeStatement} {w : NodeWitness} (x0 : LeanXmssClaim × LeanXmss.Signature) {i : ℕ}
    (hi : i < w.xmssSignatures.length) :
    (s.claims.xmss ++ (xPlan s w).duplicates)[(xPlan s w).directSlots.getD i 0]? =
      some (w.xmssSignatures.getD i x0).1 := by
  have e := coveragePlan_eq s.claims.xmss (w.xmssSignatures.map (·.1)) (w.children.map (·.statement.claims.xmss))
  obtain ⟨hk', -, -, h⟩ := B1.Main.plan_raw s.claims.xmss (w.xmssSignatures.map (·.1))
    (w.children.map (·.statement.claims.xmss)) (k := i) (by simpa using hi)
  simp only [xPlan]
  rw [e.1, e.2.1, List.getD_eq_getElem _ _ hk', h, List.getD_eq_getElem _ _ hi]
  simp

/-- **The leanSPHINCS table holds raw signature `i`'s claim at its slot.** -/
theorem sslot_claim {s : NodeStatement} {w : NodeWitness} (x0 : LeanSphincsClaim × Sphincs.Signature) {i : ℕ}
    (hi : i < w.sphincsSignatures.length) :
    (s.claims.sphincs ++ (sPlan s w).duplicates)[(sPlan s w).directSlots.getD i 0]? =
      some (w.sphincsSignatures.getD i x0).1 := by
  have e := coveragePlan_eq s.claims.sphincs (w.sphincsSignatures.map (·.1))
    (w.children.map (·.statement.claims.sphincs))
  obtain ⟨hk', -, -, h⟩ := B1.Main.plan_raw s.claims.sphincs (w.sphincsSignatures.map (·.1))
    (w.children.map (·.statement.claims.sphincs)) (k := i) (by simpa using hi)
  simp only [sPlan]
  rw [e.1, e.2.1, List.getD_eq_getElem _ _ hk', h, List.getD_eq_getElem _ _ hi]
  simp

/-! ## `main`'s layout -/

theorem mBase_twoR (m : MainCounts) : mBase m 2 = B2C.fs "main" + 4 * m.sx + 4 * m.ss := by
  simp [mBase, MainCounts.bufs, bases]

theorem mBase_threeR (m : MainCounts) : mBase m 3 = B2C.fs "main" + 4 * m.sx + 4 * m.ss + (m.sx + m.ss) := by
  simp [mBase, MainCounts.bufs, bases]

theorem mTop_ge' (m : MainCounts) : B2C.fs "main" + 4 * m.sx + 4 * m.ss + (m.sx + m.ss) + 256 ≤ mTop m := by
  simp only [mTop, MainCounts.bufs, List.sum_cons, List.sum_nil]; omega

/-- A callee's postcondition weakened. -/
theorem AtEvery.mono_post {al : String → Bool} {k : ℕ} {f : String} {args rets : List E} {R : ℕ → Prop}
    {Pre : Reader → Prop} {Q Q' : Reader → Tree → Prop} {B lo : ℕ} (h : AtEvery al k f args rets R Pre Q B lo)
    (hq : ∀ rd t, Q rd t → Q' rd t) : AtEvery al k f args rets R Pre Q' B lo :=
  fun fp cur h1 h2 => let ⟨e, he⟩ := h fp cur h1 h2
    ⟨e, he.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h) fun rd t _ hq' => hq rd t hq'⟩

/-! ## The fields -/

/-- **The raw signatures' coverage marks**: raw leanXMSS signature `i`'s slot holds `g^i`, raw
leanSPHINCS signature `i`'s, after the leanXMSS region, `g^(nrx + i)` (the loops' write counts). -/
structure RawMarks (s : NodeStatement) (w : NodeWitness) (cover : List E) : Prop where
  xm : ∀ i < w.xmssSignatures.length, cover[(xPlan s w).directSlots.getD i 0]? = some (gen ^ i)
  sm : ∀ i < w.sphincsSignatures.length,
    cover[(mainCounts s w).sx + (sPlan s w).directSlots.getD i 0]? = some (gen ^ ((mainCounts s w).nrx + i))

/-- **The raw marks of a cover written slot by slot**: a cover whose slot `t` of each region holds
`g` to the mark of the slot's taker (`(slotsOf plan).idxOf t`), the raw signatures' marks their
write counts, has `RawMarks` (the slots are taken once each, `B1.Main.plan_nodup`). -/
theorem rawMarks_of {s : NodeStatement} {w : NodeWitness} {cover : List E} (mx ms : ℕ → ℕ)
    (hx : ∀ t < (mainCounts s w).sx,
      cover[t]? = some (gen ^ mx ((B1.Main.slotsOf (B1.Main.xPlan s w)).idxOf t)))
    (hs : ∀ t < (mainCounts s w).ss,
      cover[(mainCounts s w).sx + t]? = some (gen ^ ms ((B1.Main.slotsOf (B1.Main.sPlan s w)).idxOf t)))
    (hmx : ∀ k < w.xmssSignatures.length, mx k = k)
    (hms : ∀ k < w.sphincsSignatures.length, ms k = (mainCounts s w).nrx + k) : RawMarks s w cover := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have e := coveragePlan_eq s.claims.xmss (w.xmssSignatures.map (·.1)) (w.children.map (·.statement.claims.xmss))
    have ed : (xPlan s w).directSlots = (B1.Main.xPlan s w).directSlots := e.2.1
    have hd : i < (B1.Main.xPlan s w).directSlots.length := by rw [← ed, xDirect_length]; exact hi
    have hsl : i < (B1.Main.slotsOf (B1.Main.xPlan s w)).length := by
      simp only [B1.Main.slotsOf, List.length_append]; omega
    have hget : (xPlan s w).directSlots.getD i 0 = (B1.Main.slotsOf (B1.Main.xPlan s w))[i] := by
      rw [ed, List.getD_eq_getElem _ _ hd]
      simp only [B1.Main.slotsOf]
      rw [List.getElem_append_left hd]
    have hmem : (xPlan s w).directSlots.getD i 0 ∈ (xPlan s w).directSlots := by
      rw [List.getD_eq_getElem _ _ (by rw [xDirect_length]; exact hi)]; exact List.getElem_mem _
    have hn : (B1.Main.slotsOf (B1.Main.xPlan s w)).Nodup := B1.Main.plan_nodup _ _ _
    rw [hx _ (xslot_lt hmem), hget, hn.idxOf_getElem _ hsl, hmx i hi]
  · have e := coveragePlan_eq s.claims.sphincs (w.sphincsSignatures.map (·.1))
      (w.children.map (·.statement.claims.sphincs))
    have ed : (sPlan s w).directSlots = (B1.Main.sPlan s w).directSlots := e.2.1
    have hd : i < (B1.Main.sPlan s w).directSlots.length := by rw [← ed, sDirect_length]; exact hi
    have hsl : i < (B1.Main.slotsOf (B1.Main.sPlan s w)).length := by
      simp only [B1.Main.slotsOf, List.length_append]; omega
    have hget : (sPlan s w).directSlots.getD i 0 = (B1.Main.slotsOf (B1.Main.sPlan s w))[i] := by
      rw [ed, List.getD_eq_getElem _ _ hd]
      simp only [B1.Main.slotsOf]
      rw [List.getElem_append_left hd]
    have hmem : (sPlan s w).directSlots.getD i 0 ∈ (sPlan s w).directSlots := by
      rw [List.getD_eq_getElem _ _ (by rw [sDirect_length]; exact hi)]; exact List.getElem_mem _
    have hn : (B1.Main.slotsOf (B1.Main.sPlan s w)).Nodup := B1.Main.plan_nodup _ _ _
    rw [hs _ (sslot_lt hmem), hget, hn.idxOf_getElem _ hsl, hms i hi]

/-- `main`'s words' runs: the coverage table. -/
theorem mainWords_coverRun {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {cover : List E} {rd : Reader}
    (h : MainPreA al s w cover rd) : ReadsAt rd (ptrAt (mBase (mainCounts s w) 2)) cover :=
  h.1 (mBase (mainCounts s w) 2, cover)
    (by simp only [mainWords]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- `main`'s words' runs: the byte table. -/
theorem mainWords_byteRun {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {cover : List E} {rd : Reader}
    (h : MainPreA al s w cover rd) : Sig.ByteBits rd (ptrAt (mBase (mainCounts s w) 3)) := fun v hv => by
  have hb : ReadsAt rd (ptrAt (mBase (mainCounts s w) 3)) ((List.range 256).map fun v => word v 0) :=
    h.1 (mBase (mainCounts s w) 3, (List.range 256).map fun v => word v 0) (by
      simp only [mainWords]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have := hb v (by simpa using hv)
  simpa using this

/-- **`rawx`**: the raw leanXMSS signatures' loop at `main`'s honest arguments. -/
theorem rawx_field {al : String → Bool} {k : ℕ} (hk : 17 ≤ k) {s : NodeStatement} {w : NodeWitness}
    {cover : List E} (hr : NodeRelation guestBytecode guestSeed s w) (hl : DeployedLimits s w)
    (hok : ChildrenOk guestBytecode guestSeed w)
    (hc : cover.length = (mainCounts s w).sx + (mainCounts s w).ss) (hm : RawMarks s w cover) :
    (mainCounts s w).nrx ≠ 0 → AtEveryB al k "__loop2_main"
      ([1, gen ^ (mainCounts s w).nrx, gen ^ (mainCounts s w).sx, mPtr (mainCounts s w) 2 0,
        mPtr (mainCounts s w) 0 0] ++ Main.lxTagWords) []
      (mainR al (mainCounts s w)) (MainPreA al s w cover)
      (PopsPost ((w.xmssSignatures.zip (xPlan s w).directSlots).flatMap fun cs =>
        ("raw_index", [Prover.count cs.2]) :: Prover.xmssHints cs.1.1.1 cs.1.1.2 cs.1.2))
      (loopBlock "__loop2_main" (mainCounts s w).nrx) (mLo al (mainCounts s w)) (2 ^ 60) (2 ^ 40) := by
  intro hn0
  have hcells := claimCells_of hr hok
  have hlen := mainLists_length hc hcells.fresh hcells.carried hcells.own
  have hslots := slots_lt hr hl
  have hraw := raw_le_slots hr
  have hnrx : (mainCounts s w).nrx = w.xmssSignatures.length := rfl
  obtain ⟨x0, -⟩ : ∃ x0, x0 ∈ w.xmssSignatures :=
    List.exists_mem_of_ne_nil _ fun h => hn0 (by rw [hnrx, h]; rfl)
  have hds := xDirect_length s w
  let D : RawXSigs := ⟨fun i => (xPlan s w).directSlots.getD i 0, fun i => (w.xmssSignatures.getD i x0).1.1,
    fun i => (w.xmssSignatures.getD i x0).1.2, fun i => (w.xmssSignatures.getD i x0).2⟩
  have hsl : ∀ i < (mainCounts s w).nrx, (xPlan s w).directSlots.getD i 0 < (mainCounts s w).sx := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by rw [hds]; exact hi)]
    exact xslot_lt (List.getElem_mem _)
  have hv : ∀ i < (mainCounts s w).nrx, LeanXmss.verifyWithKeccak (D.pk i) (D.msg i) (D.sig i) = true :=
    fun i hi => by
      show LeanXmss.verifyWithKeccak (w.xmssSignatures.getD i x0).1.1 (w.xmssSignatures.getD i x0).1.2
        (w.xmssSignatures.getD i x0).2 = true
      rw [List.getD_eq_getElem _ _ hi]
      exact hr.1.1 _ (List.getElem_mem _)
  have h2 := mTop_ge' (mainCounts s w)
  have hR : ∀ i < (mainCounts s w).nrx, mainR al (mainCounts s w) (mBase (mainCounts s w) 2 + D.slot i) ∧
      ∀ o < 4, mainR al (mainCounts s w) (mBase (mainCounts s w) 0 + 4 * D.slot i + o) := by
    intro i hi
    have h1 : (xPlan s w).directSlots.getD i 0 < (mainCounts s w).sx := hsl i hi
    show mainR al (mainCounts s w) (mBase (mainCounts s w) 2 + (xPlan s w).directSlots.getD i 0) ∧
      ∀ o < 4, mainR al (mainCounts s w) (mBase (mainCounts s w) 0 + 4 * (xPlan s w).directSlots.getD i 0 + o)
    rw [mBase_twoR, mBase_zero]
    exact ⟨Or.inl ⟨by omega, by omega⟩, fun o ho => Or.inl ⟨by omega, by omega⟩⟩
  have hP : ∀ rd, LowDef k rd → MainPreA al s w cover rd →
      RawXPre D (mainCounts s w).nrx (ptrAt (mBase (mainCounts s w) 2)) (ptrAt (mBase (mainCounts s w) 0)) rd ∧
        ∀ j < (mainCounts s w).sx, (rd (addressOfIndex j)).isSome := by
    intro rd hL hpre
    refine ⟨fun i hi => ⟨?_, ?_⟩, fun j hj => count_def hk hlen (by omega) hL hpre.1⟩
    · have hlt : (xPlan s w).directSlots.getD i 0 < cover.length := by rw [hc]; have := hsl i hi; omega
      have hld := loadHolds_ptr (mainWords_coverRun hpre) hlt
      have hx := hm.xm i hi
      rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hx
      rw [hx] at hld
      exact hld
    · exact tableX_at (mainWords_x hpre) (xslot_claim x0 hi)
  have H := l2_atEvery (al := al) (k := k) (by omega) (X := (mainCounts s w).sx) (by omega)
    (Nat.pos_of_ne_zero hn0) D hsl hv (mBase (mainCounts s w) 2) (mBase (mainCounts s w) 0) hR hP
    (mLo al (mainCounts s w))
  have ea : l2Args 0 (mainCounts s w).nrx (mainCounts s w).sx (ptrAt (mBase (mainCounts s w) 2))
      (ptrAt (mBase (mainCounts s w) 0)) = [1, gen ^ (mainCounts s w).nrx, gen ^ (mainCounts s w).sx,
        mPtr (mainCounts s w) 2 0, mPtr (mainCounts s w) 0 0] ++ Main.lxTagWords := by
    simp [l2Args, mPtr]
  rw [ea] at H
  refine H.mono_post fun rd t ⟨hp, hx⟩ => ⟨?_, hx⟩
  rw [hp, flatMap_zip_range _ _ hds x0 0, Nat.sub_zero, ← List.range_eq_range']
  refine sameStreams_flatMap _ fun i _ => ?_
  simp only [l2Pops, count_eq_gen]
  exact sameStreams_consR _ (Sig.xSegPops_sameStreams _ _ _)

/-- **`raws`**: the raw leanSPHINCS signatures' loop at `main`'s honest arguments. -/
theorem raws_field {al : String → Bool} {k : ℕ} (hk : 17 ≤ k) {s : NodeStatement} {w : NodeWitness}
    {cover : List E} (hr : NodeRelation guestBytecode guestSeed s w) (hl : DeployedLimits s w)
    (hok : ChildrenOk guestBytecode guestSeed w)
    (hc : cover.length = (mainCounts s w).sx + (mainCounts s w).ss) (hm : RawMarks s w cover) :
    (mainCounts s w).nrs ≠ 0 → AtEveryB al k "__loop3_main"
      [1, gen ^ (mainCounts s w).nrs, gen ^ (mainCounts s w).ss, mPtr (mainCounts s w) 2 (mainCounts s w).sx,
        gen ^ (mainCounts s w).nrx, mPtr (mainCounts s w) 1 0, mPtr (mainCounts s w) 3 0] []
      (mainR al (mainCounts s w)) (MainPreA al s w cover)
      (PopsPost ((w.sphincsSignatures.zip (sPlan s w).directSlots).flatMap fun cs =>
        ("sp_raw_index", [Prover.count cs.2]) :: Prover.sphincsHints cs.1.1.1 cs.1.1.2 cs.1.2))
      (loopBlock "__loop3_main" (mainCounts s w).nrs) (mLo al (mainCounts s w)) (2 ^ 60) (2 ^ 40) := by
  intro hn0
  have hcells := claimCells_of hr hok
  have hlen := mainLists_length hc hcells.fresh hcells.carried hcells.own
  have hslots := slots_lt hr hl
  have hraw := raw_le_slots hr
  have hnrs : (mainCounts s w).nrs = w.sphincsSignatures.length := rfl
  obtain ⟨x0, -⟩ : ∃ x0, x0 ∈ w.sphincsSignatures :=
    List.exists_mem_of_ne_nil _ fun h => hn0 (by rw [hnrs, h]; rfl)
  have hds := sDirect_length s w
  let D : RawSigs := ⟨fun i => (sPlan s w).directSlots.getD i 0, fun i => (w.sphincsSignatures.getD i x0).1.1,
    fun i => (w.sphincsSignatures.getD i x0).1.2, fun i => (w.sphincsSignatures.getD i x0).2⟩
  have hsl : ∀ i < (mainCounts s w).nrs, (sPlan s w).directSlots.getD i 0 < (mainCounts s w).ss := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by rw [hds]; exact hi)]
    exact sslot_lt (List.getElem_mem _)
  have hv : ∀ i < (mainCounts s w).nrs, Sphincs.verifyWithKeccak (D.pk i) (D.msg i) (D.sig i) = true :=
    fun i hi => by
      show Sphincs.verifyWithKeccak (w.sphincsSignatures.getD i x0).1.1 (w.sphincsSignatures.getD i x0).1.2
        (w.sphincsSignatures.getD i x0).2 = true
      rw [List.getD_eq_getElem _ _ hi]
      exact hr.1.2.1 _ (List.getElem_mem _)
  have h2 := mTop_ge' (mainCounts s w)
  have hR : (∀ i < (mainCounts s w).nrs,
      mainR al (mainCounts s w) (mBase (mainCounts s w) 2 + (mainCounts s w).sx + D.slot i) ∧
        ∀ o < 4, mainR al (mainCounts s w) (mBase (mainCounts s w) 1 + 4 * D.slot i + o)) ∧
      ∀ v < 256, mainR al (mainCounts s w) (mBase (mainCounts s w) 3 + v) := by
    refine ⟨fun i hi => ?_, fun v hv => ?_⟩
    · have h1 : (sPlan s w).directSlots.getD i 0 < (mainCounts s w).ss := hsl i hi
      show mainR al (mainCounts s w) (mBase (mainCounts s w) 2 + (mainCounts s w).sx +
          (sPlan s w).directSlots.getD i 0) ∧
        ∀ o < 4, mainR al (mainCounts s w) (mBase (mainCounts s w) 1 + 4 * (sPlan s w).directSlots.getD i 0 + o)
      rw [mBase_twoR, mBase_one]
      exact ⟨Or.inl ⟨by omega, by omega⟩, fun o ho => Or.inl ⟨by omega, by omega⟩⟩
    · rw [mBase_threeR]
      exact Or.inl ⟨by omega, by omega⟩
  have hP : ∀ rd, LowDef k rd → MainPreA al s w cover rd →
      RawSPre D (mainCounts s w).nrs (mainCounts s w).nrx (ptrAt (mBase (mainCounts s w) 2 + (mainCounts s w).sx))
        (ptrAt (mBase (mainCounts s w) 1)) (ptrAt (mBase (mainCounts s w) 3)) rd ∧
        ∀ j < (mainCounts s w).ss, (rd (addressOfIndex j)).isSome := by
    intro rd hL hpre
    refine ⟨fun i hi => ⟨?_, mainWords_byteRun hpre, ?_⟩, fun j hj => count_def hk hlen (by omega) hL hpre.1⟩
    · have hlt : (mainCounts s w).sx + (sPlan s w).directSlots.getD i 0 < cover.length := by
        rw [hc]; have := hsl i hi; omega
      have hld := loadHolds_ptr (mainWords_coverRun hpre) hlt
      have hx := hm.sm i hi
      rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hx
      rw [hx, ptrAt_mul_gen_pow, ← Nat.add_assoc, ← ptrAt_mul_gen_pow, pow_add] at hld
      exact hld
    · exact tableS_at (mainWords_s hpre) (sslot_claim x0 hi)
  have H := l3_atEvery (al := al) (k := k) (by omega) (Y := (mainCounts s w).ss) (nrx := (mainCounts s w).nrx)
    (by omega) (Nat.pos_of_ne_zero hn0) D hsl hv (mBase (mainCounts s w) 2 + (mainCounts s w).sx)
    (mBase (mainCounts s w) 1) (mBase (mainCounts s w) 3) hR hP (mLo al (mainCounts s w))
  have ea : l3Args 0 (mainCounts s w).nrs (mainCounts s w).ss (mainCounts s w).nrx
      (ptrAt (mBase (mainCounts s w) 2 + (mainCounts s w).sx)) (ptrAt (mBase (mainCounts s w) 1))
      (ptrAt (mBase (mainCounts s w) 3)) = [1, gen ^ (mainCounts s w).nrs, gen ^ (mainCounts s w).ss,
        mPtr (mainCounts s w) 2 (mainCounts s w).sx, gen ^ (mainCounts s w).nrx, mPtr (mainCounts s w) 1 0,
        mPtr (mainCounts s w) 3 0] := by
    simp [l3Args, mPtr]
  rw [ea] at H
  refine H.mono_post fun rd t ⟨hp, hx⟩ => ⟨?_, hx⟩
  rw [hp, flatMap_zip_range _ _ hds x0 0, Nat.sub_zero, ← List.range_eq_range']
  refine sameStreams_flatMap _ fun i hi => ?_
  simp only [l3Pops, count_eq_gen]
  exact sameStreams_consR _ (Sig.spSegPops_sameStreams _ _ _ (hv i (List.mem_range.mp hi)))

end
end LeanVM.Guest.Complete
