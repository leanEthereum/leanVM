/-
  LeanVM.Guest.B1.Da.ColAt

  `da_verify_column` placed (G:4562-4576): column `h` of every blob, its weights expanded from the
  top leaf `h` (`da_expand__L7_L8`, its run in its frame), then every blob's cell checked against
  them and joined to its running sum and its tree (`da_verify_column_loop0`), within its frame and
  its callees' bounds, by a tree of its honest shape (`colNH r`).

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.B1.Da.VecAt
public import LeanVM.Guest.B1.Da.DvLoops
public import LeanVM.Guest.B1.Da.VectorMath
public import LeanVM.Guest.Data.NameStrings

/-!
# The column, placed

The column reads its top leaf `topRun z [128 + h] = topLeaf z h` (`topLeaf_eq`), expands the cell's
weights from it (`exp8_completeAtB`: the cell factors, `zs`, the offsets of the cell `h`), whose
leaves are the dual codeword on the cell (`cellLeaf_eq`), then runs `da_verify_column_loop0` over
the blobs (`l21_rel`). `colLin`: what it reads; `colNH r`: its honest shape (its counter's bound
`g^r` and its loop's start `1`); `colNHT r h Tr`: column `h`'s, its row loop by a tree of `Tr`; `col_completeAtBT`:
complete within `colB` by such a tree, given its row loop's completeness; `col_completeAtB`: complete within `colB`,
when the static bounds hold.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (CompleteAtDTB Kid KidD kidsAt outsL KidsDepBP OutsOk RegionsOk CallsMatch
  Returns completeAt_flatDepRet flatCalls namedP)
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1.Main (Layout MemL RegionL iterK)

@[expose] public section

/-- `da_verify_column`'s block. -/
noncomputable def colPre : List Stmt := (Fn.body fn% «da_verify_column»).dropLast

/-- Its calls. -/
def colCallsS : List (Option V × String × List V × List V) :=
  [(none, "da_expand__L7_L8", [.n 8, .n 5, .n 3, .n 12], [.n 13]),
    (some (.n 16), name% «da_verify_column_loop0», [.n 17, .n 1, .n 13, .n 2, .n 0, .n 14], [])]

/-- **Its shape** (kernel evaluation). -/
noncomputable def colCOk : Bool :=
  colPre.all Core.Stmt.flat && colPre.all noDispatch && colPre.all B1.notIteB &&
  decide (colPre.filterMap Stmt.addrS = []) && decide (colPre.filterMap Stmt.allocSz = []) &&
  decide (colPre.filterMap Main.Stmt.callS = colCallsS) &&
  decide (colPre.filterMap Stmt.loadS = [(.n 7, 0)])

theorem col_cok : colCOk = true := by decide +kernel

/-- **What a column reads**: `zs`, the top tree's run, the cell factors, the offsets, the regions
and their bases. -/
def colLin (r : ℕ) (syms : ℕ → ℕ → List K) (z : E) (bz bt bc bo bb bR : ℕ) : Layout :=
  [(bz, zsCells z), (bt, topRun z), (bc, facCells (zsVal z) 7 8), (bo, offCells (zsVal z)),
    (bb, blobsCells r syms z), (bR, rowbaseCells r bb)]

/-- Column `h`'s shifts: the offsets of the cell `h`. -/
def colShift (z : E) (h : ℕ) : ℕ → E := fun j => zsVal z j * ofK (wK j (256 * h))

/-- Column `h`'s expansion's run. -/
def colRun (z : E) (h : ℕ) : List E := expRunVals (topLeaf z h) (factorAt (zsVal z) 7) (zsVal z) (colShift z h) 7 8

/-- The expansion's run's base, read off its result. -/
noncomputable def colRb (z : E) (h : ℕ) (pv : List (List E × Layout)) : ℕ :=
  outB (fun b rets Lo => rets = [gen ^ (b + 2 ^ 8)] ∧ (b, colRun z h) ∈ Lo) (pv.headD ([], []))

/-- A column's callees. -/
noncomputable def colKids (r : ℕ) (syms : ℕ → ℕ → List K) (z : E) (bz bc bo bb bR h : ℕ) : List KidD :=
  [fun _ => ⟨"da_expand__L7_L8", true, [topLeaf z h, gen ^ bc, gen ^ bz, gen ^ (bo + 8 * h)],
      [(bz, zsCells z), (bc, facCells (zsVal z) 7 8), (bo, offCells (zsVal z))],
      expOut (topLeaf z h) (factorAt (zsVal z) 7) (zsVal z) (colShift z h) 7 8⟩,
    fun pv => ⟨name% «da_verify_column_loop0», true, [1, gen ^ r, gen ^ (colRb z h pv + 256),
        gen ^ bR, gen ^ h, gen ^ h * gen ^ h],
      [(bb, blobsCells r syms z), (bR, rowbaseCells r bb), (colRb z h pv, colRun z h)], Returns []⟩]

/-- A column's valuation. -/
def colVals (r : ℕ) (z : E) (bz bt bc bo bR h : ℕ) (r13 : E) : List E :=
  [gen ^ h, gen ^ r, gen ^ bR, gen ^ bz, gen ^ (bt + 2 ^ 7), gen ^ bc, gen ^ bo,
    gen ^ (bt + 2 ^ 7) * gen ^ h, topLeaf z h, gen ^ h * gen ^ h, gen ^ h * gen ^ h * (gen ^ h * gen ^ h),
    gen ^ h * gen ^ h * (gen ^ h * gen ^ h) * (gen ^ h * gen ^ h * (gen ^ h * gen ^ h)),
    gen ^ bo * (gen ^ h * gen ^ h * (gen ^ h * gen ^ h) * (gen ^ h * gen ^ h * (gen ^ h * gen ^ h))),
    r13, gen ^ h * gen ^ h, 1, 1 + gen ^ r, 1]

theorem col_flatCalls (σ : Val) : flatCalls colPre σ = colCallsS.map (Main.mkCall σ) := rfl

/-- **A column's honest shape**: its counter's bound `g^r`, its loop started at `1`. -/
def colQ (r : ℕ) (σ : Val) : Prop := σ (.n 1) = gen ^ r ∧ σ (.n 17) = 1

/-- **A column's honest tree**. -/
def colNH (r : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "da_verify_column" (colQ r) (flatCalls colPre) (fun _ => [])
    [fun _ => True, fun _ => True]

/-- Column `h`'s honest words: `colQ`, its counter `g^h`, its row loop's guard `1 + g^r`. -/
def colQh (r h : ℕ) (σ : Val) : Prop := colQ r σ ∧ σ (.n 0) = gen ^ h ∧ σ (.n 16) = 1 + gen ^ r

/-- **Column `h`'s honest tree, its row loop by a tree of `Tr`**. -/
def colNHT (r h : ℕ) (Tr : Tree → Prop) : Tree → Prop :=
  NodeHonest coreProgram "da_verify_column" (colQh r h) (flatCalls colPre) (fun _ => []) [fun _ => True, Tr]

theorem kidsT_mono : ∀ (cs : List Call) (Ts Ts' : List (Tree → Prop)) (ks : List Tree),
    List.Forall₂ (fun T T' => ∀ t, T t → T' t) Ts Ts' → KidsT cs Ts ks → KidsT cs Ts' ks
  | _ :: cs, _ :: Ts, _ :: Ts', k :: ks, .cons h hs, ⟨h1, h2⟩ =>
    ⟨fun ht => h k (h1 ht), kidsT_mono cs Ts Ts' ks hs h2⟩
  | [], _, _, _, _, _ => trivial
  | _ :: _, [], [], _, _, _ => trivial
  | _ :: _, _ :: _, _ :: _, [], _, _ => trivial

/-- An honest node under weaker predicates on its callees. -/
theorem nodeHonest_mono {P : Core.Program} {f : String} {Q : Val → Prop} {cs : Val → List Call}
    {bs : Val → List ℕ} {Ts Ts' : List (Tree → Prop)} {t : Tree} (h : NodeHonest P f Q cs bs Ts t)
    (hT : List.Forall₂ (fun T T' => ∀ t, T t → T' t) Ts Ts') : NodeHonest P f Q cs bs Ts' t := by
  obtain ⟨σ, ks, rfl, hQ, hw, hl, hk⟩ := h
  exact ⟨σ, ks, rfl, hQ, hw, by rw [← hT.length_eq]; exact hl, kidsT_mono _ _ _ _ hT hk⟩

theorem colNH_of_T {r h : ℕ} {Tr : Tree → Prop} {t : Tree} (ht : colNHT r h Tr t) : colNH r t :=
  let ⟨σ, ks, e, hQ, hw, hl, hk⟩ := ht
  nodeHonest_mono (Ts := [fun _ => True, Tr]) ⟨σ, ks, e, hQ.1, hw, hl, hk⟩
    (.cons (fun _ h => h) (.cons (fun _ _ => trivial) .nil))

theorem namedP_forall₂ {fs : String → ℕ} : ∀ (names : List String) (Bs : List ℕ) (Ps : List (Tree → Prop)),
    names.length = Ps.length → Bs.length = Ps.length →
    List.Forall₂ (fun T T' => ∀ t, T t → T' t) (namedP fs names Bs Ps) Ps
  | [], [], [], _, _ => .nil
  | _ :: ns, _ :: Bs, _ :: Ps, h1, h2 =>
    .cons (fun _ h => h.2) (namedP_forall₂ ns Bs Ps (by simpa using h1) (by simpa using h2))
  | [], _ :: _, _, h1, h2 => by simp at h1 h2; omega
  | _ :: _, [], _, h1, h2 => by simp at h1 h2; omega
  | [], [], _ :: _, h1, _ => by simp at h1
  | _ :: _, _ :: _, [], h1, _ => by simp at h1

theorem length_expRunVals {root : E} {F Z S : ℕ → E} {top D : ℕ} :
    (expRunVals root F Z S top D).length = 512 := by
  simp [expRunVals]

set_option maxRecDepth 8000 in
theorem length_topRun (z : E) : (topRun z).length = 512 := length_expRunVals

theorem length_colRun (z : E) (h : ℕ) : (colRun z h).length = 512 := length_expRunVals

theorem topRun_leaf (z : E) {h : ℕ} (hh : h < 128) :
    (topRun z).getD (128 + h) 0 = topLeaf z h := by
  have hk : 128 + h < 512 := by omega
  unfold topRun
  rw [List.getD_eq_getElem _ _ (by rw [length_expRunVals]; exact hk), expRunVals_get hk, ite_pos' ⟨by omega, by norm_num; omega⟩,
    show Nat.log 2 (128 + h) = 7 from log_two_pow_add (k := 7) hh, show (2 : ℕ) ^ 7 = 128 by norm_num,
    Nat.add_sub_cancel_left, topLeaf_eq z hh]

set_option maxRecDepth 8000 in
theorem colRun_leaf (z : E) (h : ℕ) {e : ℕ} (he : e < 256) :
    (colRun z h).getD (256 + e) 0 = dualAt z (256 * h + e) := by
  have hk : 256 + e < 512 := by omega
  unfold colRun
  rw [List.getD_eq_getElem _ _ (by rw [length_expRunVals]; exact hk), expRunVals_get hk, ite_pos' ⟨by omega, by norm_num; omega⟩,
    show Nat.log 2 (256 + e) = 8 from log_two_pow_add (k := 8) he, show (2 : ℕ) ^ 8 = 256 by norm_num,
    Nat.add_sub_cancel_left]
  exact cellLeaf_eq z he

/-- **Column `h`'s weights**, the leaves of its expansion's run. -/
theorem colRun_reads {rd : Reader} {L : Layout} (hm : MemL rd L) {c : ℕ} (z : E) (h : ℕ) (hq : (c, colRun z h) ∈ L) :
    ReadsAt rd (gen ^ (c + 256)) (colWs z h) := by
  intro e he
  have he' : e < 256 := by simpa [colWs] using he
  have := reads_of_memL hm hq (256 + e) (by rw [length_colRun]; omega)
  rw [← List.getD_eq_getElem _ 0, colRun_leaf z h he'] at this
  rw [pow_add, loadHolds_mul_gen_pow]
  simpa [colWs, he'] using this

theorem one_add_gen_isInK (r : ℕ) : IsInK (1 + gen ^ r) := by
  rw [← pow_zero gen]; exact gen_pow_add_isInK _ _

set_option maxRecDepth 20000 in
/-- **A column's statements hold** on its valuation, its top leaf read. -/
theorem col_sholds {rd : Reader} (r : ℕ) (z : E) (bz bt bc bo bR h : ℕ) (r13 : E)
    (htop : LoadHolds rd (gen ^ (bt + 2 ^ 7) * gen ^ h) 0 (topLeaf z h)) :
    ∀ s ∈ colPre, SHolds (fun _ _ _ => True) rd (Val.ofArgs (colVals r z bz bt bc bo bR h r13)) s := by
  intro s hs
  simp only [colPre, core_eq% «da_verify_column», core_eq% «da_verify_column» body,
      List.dropLast_cons_cons, List.dropLast_singleton,
    List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [SHolds, Atom.Holds, ofArgs_n, colVals, List.getD_cons_succ,
    List.getD_cons_zero, word_one]
  all_goals first | exact htop | exact ⟨one_add_gen_isInK r, fun _ => True.intro⟩

variable (fs : String → ℕ) (cert : String → V → ℕ)

set_option maxRecDepth 20000 in
/-- **Column `h` is complete, placed, by a tree of its honest shape, within its frame and its
callees' bounds**: the expansion's frame, the row loop's `r` iterations and its run's phantom
frame, its row loop by a tree of `Tr` when it is complete so (`hrow`). -/
theorem col_completeAtBT (hrf : Lift.RunsFit fs cert) {SK : String → ℕ}
    {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ 1024) {syms : ℕ → ℕ → List K}
    {z : E} {bz bt bc bo bb bR h : ℕ} (hh : h < 128) {Tr : Tree → Prop}
    (hrow : ∀ c, CompleteAtDTB fs cert 16 name% «da_verify_column_loop0»
      [(bb, blobsCells r syms z), (bR, rowbaseCells r bb), (c, colRun z h)]
      [1, gen ^ r, gen ^ (c + 256), gen ^ bR, gen ^ h, gen ^ h * gen ^ h] (Returns []) Tr
      (r * iterK fs SK name% «da_verify_column_loop0» + fs name% «da_verify_column_loop0»)) :
    CompleteAtDTB fs cert 16 "da_verify_column" (colLin r syms z bz bt bc bo bb bR)
      [gen ^ h, gen ^ r, gen ^ bR, gen ^ bz, gen ^ (bt + 2 ^ 7), gen ^ bc, gen ^ bo] (Returns [])
      (colNHT r h Tr)
      (fs "da_verify_column" + (fs "da_expand__L7_L8" + (r * iterK fs SK
          name% «da_verify_column_loop0» + fs name% «da_verify_column_loop0»))) := by
  have hcok := col_cok
  unfold colCOk at hcok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcok
  obtain ⟨⟨⟨⟨⟨⟨hflat, hnd⟩, hni⟩, haddr⟩, halloc⟩, hcalls⟩, hloads⟩ := hcok
  have hb : Fn.body fn% «da_verify_column» = colPre ++ [.ret []] := rfl
  have hLz : ∀ {rd : Reader} {L : Layout}, (bz, zsCells z) ∈ L → MemL rd L →
      ∀ j < 15, LoadHolds rd (gen ^ bz) j (zsVal z j) := fun hq hm j hj => by
    have := reads_of_memL hm hq j (by simp [zsCells]; exact hj)
    rwa [zsCells_get hj] at this
  refine ((completeAt_flatDepRet (fs := fs) (cert := cert) find_da_verify_column
    (by rw [Program.loop_of_find? find_da_verify_column]; decide +kernel) 16
    (colLin r syms z bz bt bc bo bb bR)
    [gen ^ h, gen ^ r, gen ^ bR, gen ^ bz, gen ^ (bt + 2 ^ 7), gen ^ bc, gen ^ bo]
    (fun _ _ => []) [] hb hflat haddr hni [] (fun _ => []) (fun _ => .nil)
    (fun _ => colKids r syms z bz bc bo bb bR h) ["da_expand__L7_L8",
        name% «da_verify_column_loop0»]
    [fs "da_expand__L7_L8", r * iterK fs SK name% «da_verify_column_loop0» + fs
        name% «da_verify_column_loop0»] [fun _ => True, Tr]
    (colQh r h)
    (fun _ => .cons (fun _ => rfl) (.cons (fun _ => rfl) .nil))
    (fun fp => ?_) (fun _ _ _ _ => rfl)
    (fun fp outs ho => ?_) (fun fp outs ho rd _ _ hLin hO => ?_) ?_).mono (by simp)
    (fun t ht => nodeHonest_mono ht (namedP_forall₂ _ _ _ rfl rfl)))
  · -- the callees
    refine ⟨fun pv => ⟨fun _ => ?_, fun h => absurd h (by simp)⟩,
      fun pv => ⟨fun _ => ?_, fun h => absurd h (by simp)⟩, trivial⟩
    · refine exp8_completeAtB fs cert hrf (fun rd hm n h1 h2 => ?_)
        (fun rd hm d hd => hLz List.mem_cons_self hm _ (by omega)) (fun rd hm d hd => ?_)
        (fun n h1 h2 => regionL_of_mem (List.mem_cons_of_mem _ List.mem_cons_self)
          (by simp [facCells]; omega))
        (fun d hd => regionL_of_mem List.mem_cons_self (by simp [zsCells]; omega))
        (fun d hd => by
          have := regionL_of_mem (L := [(bz, zsCells z), (bc, facCells (zsVal z) 7 8),
            (bo, offCells (zsVal z))]) (k := 8 * h + (7 - d)) (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ List.mem_cons_self)) (by simp [offCells]; omega)
          rwa [← Nat.add_assoc] at this)
      · have := reads_of_memL hm (List.mem_cons_of_mem _ List.mem_cons_self) n
          (by simp [facCells]; omega)
        rwa [facCells_get h1 h2 (by norm_num)] at this
      · have := reads_of_memL hm (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          List.mem_cons_self)) (8 * h + (7 - d)) (by simp [offCells]; omega)
        rw [offCells_get (by omega), show (8 * h + (7 - d)) % 8 = 7 - d by omega,
          show (8 * h + (7 - d)) / 8 = h by omega] at this
        rw [pow_add, loadHolds_mul_gen_pow]
        exact this
    · exact hrow (colRb z h pv)
  · -- the callees' regions
    match outs, ho with
    | [], _ => trivial
    | o1 :: os, ho =>
      have hf := outB_spec (P := fun b rets Lo => rets = [gen ^ (b + 2 ^ 8)] ∧ (b, colRun z h) ∈ Lo)
        (o := o1) (ho.1 rfl)
      have hL : ∀ {xs : List E} {b : ℕ}, (b, xs) ∈ colLin r syms z bz bt bc bo bb bR → ∀ i,
          RegionL [(b, xs)] i → RegionL (colLin r syms z bz bt bc bo bb bR) i :=
        fun hq i ⟨q, hq', h1, h2⟩ => ⟨q, by rw [List.mem_singleton] at hq'; subst hq'; exact hq, h1, h2⟩
      refine ⟨fun _ i hi => ?_, ?_⟩
      · obtain ⟨q, hq, hq1, hq2⟩ := hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        refine Or.inl (Or.inl (hL ?_ i ⟨_, List.mem_singleton_self _, hq1, hq2⟩))
        rcases hq with rfl | rfl | rfl <;> simp [colLin]
      match os with
      | [] => trivial
      | o2 :: os =>
        refine ⟨fun _ i hi => ?_, by cases os <;> trivial⟩
        obtain ⟨q, hq, hq1, hq2⟩ := hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact Or.inl (Or.inl (hL (by simp [colLin]) i ⟨_, List.mem_singleton_self _, hq1, hq2⟩))
        · exact Or.inl (Or.inl (hL (by simp [colLin]) i ⟨_, List.mem_singleton_self _, hq1, hq2⟩))
        · exact Or.inr (Or.inr ⟨rfl, _, by simpa [colRb] using hf.2, hq1, hq2⟩)
  · -- what the callees read
    intro q hq
    match outs, ho with
    | [], _ => simp [kidsAt, B1.Kid.lins] at hq
    | o1 :: os, ho =>
      have hf := outB_spec (P := fun b rets Lo => rets = [gen ^ (b + 2 ^ 8)] ∧ (b, colRun z h) ∈ Lo)
        (o := o1) (ho.1 rfl)
      have hrq : (colRb z h [o1], colRun z h) ∈ outsL (kidsAt (colKids r syms z bz bc bo bb bR h) [] (o1 :: os))
          (o1 :: os) := by
        simp only [kidsAt, outsL, colKids, ↓reduceIte, List.mem_append]
        exact Or.inl (by simpa [colRb] using hf.2)
      have hq' : q ∈ colLin r syms z bz bt bc bo bb bR ∨ q = (colRb z h [o1], colRun z h) := by
        rcases os with _ | ⟨o2, os⟩ <;> simp [kidsAt, B1.Kid.lins, colKids] at hq <;>
          simp only [colLin, List.mem_cons, List.not_mem_nil, or_false] <;> tauto
      rcases hq' with hq' | rfl
      · exact hLin _ hq'
      · exact hO _ hrq
  · -- the valuation
    intro fp outs hlen ho rd _ _ hLin _
    match outs, hlen, ho with
    | [o1, o2], _, ho =>
      obtain ⟨h1, h2, -⟩ := ho
      have hf := outB_spec (P := fun b rets Lo => rets = [gen ^ (b + 2 ^ 8)] ∧ (b, colRun z h) ∈ Lo)
        (o := o1) (h1 rfl)
      obtain ⟨b1, e1, -⟩ := h1 rfl
      have hrb : gen ^ (colRb z h [o1] + 256) = gen ^ (b1 + 2 ^ 8) := by
        have := hf.1.symm.trans e1
        simpa [colRb] using this
      obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = Val.ofArgs (colVals r z bz bt bc bo bR h (gen ^ (b1 + 2 ^ 8))) :=
        ⟨_, rfl⟩
      have htop : LoadHolds rd (gen ^ (bt + 2 ^ 7) * gen ^ h) 0 (topLeaf z h) := by
        have := loadHolds_of_reads (reads_of_memL hLin (List.mem_cons_of_mem _ List.mem_cons_self))
          (by rw [length_topRun]; omega) (topRun_leaf z hh)
        rw [← pow_add, show bt + 2 ^ 7 + h = bt + (128 + h) by norm_num; ring, pow_add,
          loadHolds_mul_gen_pow, Nat.add_zero]
        exact this
      have hall := col_sholds (rd := rd) r z bz bt bc bo bR h (gen ^ (b1 + 2 ^ 8)) htop
      rw [← hσ] at hall
      have hcs : colPre.filterMap (Stmt.callSF σ) = colCallsS := by
        rw [← hcalls]
        refine List.filterMap_congr fun s hs => ?_
        have := List.all_eq_true.mp hnd s hs
        cases s with
        | dispatch => simp [noDispatch] at this
        | _ => rfl
      have s7 : σ (.n 7) = gen ^ (bt + 2 ^ 7 + h) := by rw [hσ]; exact (pow_add gen (bt + 2 ^ 7) h).symm
      have hne : (1 : E) + gen ^ r ≠ 0 := Digest.one_add_gen_pow_ne_zero (by omega) (by unfold ordG; omega)
      refine ⟨σ, by rw [hσ]; rfl, fun s hs => ?_, ?_, by rw [halloc]; rfl, by rw [halloc]; rfl, ?_, ?_,
        by rw [hσ]; exact ⟨⟨rfl, rfl⟩, rfl, rfl⟩⟩
      · have := List.all_eq_true.mp hnd s hs
        cases s with
        | dispatch => simp [noDispatch] at this
        | _ => trivial
      · rw [hb]
        exact holdsList_straight _ _ _ _ hall rfl
      · simp only [flatCalls, hcs, colCallsS, List.map_cons, List.map_nil, Main.mkCall, kidsAt, colKids]
        refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, ?_, fun _ => ⟨?_, ?_⟩, trivial⟩
        · simp [hσ, ofArgs_n, colVals, ← pow_add]
          ring_nf
        · simp [hσ, ofArgs_n, colVals, e1]
        · simp [hσ, ofArgs_n, colVals, hne]
        · simp [hσ, ofArgs_n, colVals, hrb]
        · simp only [Returns] at h2
          rw [(h2 trivial).1]
          rfl
      · rw [hloads]
        intro q hq
        rw [List.mem_singleton] at hq
        subst hq
        refine ⟨bt + 2 ^ 7 + h, by rw [s7]; exact limb0_gen_pow_mul _ _, Or.inl ?_⟩
        have := regionL_of_mem (L := colLin r syms z bz bt bc bo bb bR) (k := 2 ^ 7 + h)
          (List.mem_cons_of_mem _ List.mem_cons_self) (by rw [length_topRun]; omega)
        rwa [← Nat.add_assoc] at this

/-- **Column `h` is complete, placed, by a tree of its honest shape, within its frame and its callees' bounds**, when
the static bounds hold (`col_completeAtBT`, its row loop by the pure lift). -/
theorem col_completeAtB (hrf : Lift.RunsFit fs cert) {SK : String → ℕ}
    (h21 : TotalLeOn coreProgram fs name% «da_verify_column_loop0» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «da_verify_column_loop0» + fs
          name% «da_verify_column_loop0»))
    {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ 1024) {syms : ℕ → ℕ → List K} (hsl : ∀ i j, (syms i j).length = 256)
    {z : E} {bz bt bc bo bb bR h : ℕ} (hh : h < 128) :
    CompleteAtDTB fs cert 16 "da_verify_column" (colLin r syms z bz bt bc bo bb bR)
      [gen ^ h, gen ^ r, gen ^ bR, gen ^ bz, gen ^ (bt + 2 ^ 7), gen ^ bc, gen ^ bo] (Returns [])
      (colNH r)
      (fs "da_verify_column" + (fs "da_expand__L7_L8" + (r * iterK fs SK
          name% «da_verify_column_loop0» + fs name% «da_verify_column_loop0»))) :=
  (col_completeAtBT fs cert hrf hr1 hr hh (Tr := fun _ => True) fun c =>
    pureB_loop daPure (by simp [daPureSet]) (fun rd hm => l21_rel hr1 hh hsl (reads_of_memL hm List.mem_cons_self)
      (reads_of_memL hm (List.mem_cons_of_mem _ List.mem_cons_self))
      (colRun_reads hm z h (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) h21
      (by omega) (by omega)).mono le_rfl fun _ => colNH_of_T

end
end LeanVM.Guest.B1.Da
