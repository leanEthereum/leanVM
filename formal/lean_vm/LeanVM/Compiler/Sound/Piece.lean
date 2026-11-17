/-
  LeanVM.Compiler.Sound.Piece

  What a function's piece (`Compiler.Piece`) says, and the composition of a program's pieces.
-/

module

public import LeanVM.Compiler.Piece
public import LeanVM.Compiler.Sound.Program
public import LeanVM.Compiler.Sound.Asm

/-!
# Pieces

`pieceOk_spec`: a success of `pieceOk` is a success of `placeFn` from the jump tables `t` to
`t.after o`, whose emitted function has the name, frame size, code size and jump table slots `o`
records, and whose code, resolved at the layout, is the compiled function's.
-/

namespace LeanVM.Compiler

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest

@[expose] public section

/-! ## The slots a function fills are its own instructions -/

/-- A slot filled with an instruction of the function `f`. -/
def FillOf (f : String) (x : Fill) : Prop := ∃ i, x.2 = .at f i

mutual
theorem stmtFills_of (f : String) : ∀ (s : PStmt) (pos : Nat), ∀ x ∈ stmtFills f s pos, FillOf f x
  | .ite _ _ _ _ zero hasElse _ _ nonzero, pos, x, hx => by
      simp only [stmtFills, List.mem_append] at hx
      rcases hx with hx | hx
      · exact blockFills_of f zero _ x hx
      · split at hx
        · exact blockFills_of f nonzero _ x hx
        · nomatch hx
  | .chain _ _ _ _ _ _ firsts stages, pos, x, hx => stagesFills_of f firsts stages _ x hx
  | .op _ _, _, x, hx => by simp [stmtFills] at hx
  | .call _ _, _, x, hx => by simp [stmtFills] at hx
  | .loopNext _ _ _ _ _ _ _, _, x, hx => by simp [stmtFills] at hx
  | .dispatch _ _ _ _ _ _ _ _ _ _, _, x, hx => by simp [stmtFills] at hx
  | .ret _ _, _, x, hx => by simp [stmtFills] at hx
  | .halt _ _ _, _, x, hx => by simp [stmtFills] at hx

theorem blockFills_of (f : String) : ∀ (b : List PStmt) (pos : Nat), ∀ x ∈ blockFills f b pos,
    FillOf f x
  | [], _, x, hx => by simp [blockFills] at hx
  | s :: ss, pos, x, hx => by
      simp only [blockFills, List.mem_append] at hx
      rcases hx with hx | hx
      · exact stmtFills_of f s pos x hx
      · exact blockFills_of f ss _ x hx

theorem armsFills_of (f : String) (first : Nat) : ∀ (as : List (List PStmt)) (j pos : Nat),
    ∀ x ∈ armsFills f first as j pos, FillOf f x
  | [], _, _, x, hx => by simp [armsFills] at hx
  | a :: as, j, pos, x, hx => by
      simp only [armsFills, List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx
      · exact ⟨pos, rfl⟩
      · exact blockFills_of f a pos x hx
      · exact armsFills_of f first as _ _ x hx

theorem stagesFills_of (f : String) : ∀ (firsts : List Nat) (ss : List (List (List PStmt)))
    (pos : Nat), ∀ x ∈ stagesFills f firsts ss pos, FillOf f x
  | _, [], _, x, hx => by simp [stagesFills] at hx
  | firsts, s :: ss, pos, x, hx => by
      simp only [stagesFills, List.mem_append] at hx
      rcases hx with hx | hx
      · exact armsFills_of f _ s 0 pos x hx
      · exact stagesFills_of f firsts.tail ss _ x hx
end

theorem emitFn_fills_of (p : PFn) : ∀ x ∈ (emitFn p).2.toList, FillOf p.name x := by
  rw [emitFn_fills]
  exact blockFills_of p.name p.body 0

theorem allPairs_fillIs {f : String} : ∀ (l : List Fill) (os : List (Nat × Nat)),
    (∀ x ∈ l, FillOf f x) → allPairs fillIs l os = true →
      l = os.map fun x => (x.1, KVal.at f x.2)
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [allPairs] at h
  | _ :: _, [], _, h => by simp [allPairs] at h
  | (s, k) :: l, (s', i') :: os, hf, h => by
      simp only [allPairs, Bool.and_eq_true] at h
      obtain ⟨i, hi⟩ := hf (s, k) List.mem_cons_self
      simp only at hi
      subst hi
      simp only [fillIs, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, rfl⟩, h⟩ := h
      rw [allPairs_fillIs l os (fun x hx => hf x (List.mem_cons_of_mem _ hx)) h]
      rfl

/-! ## A piece -/

theorem tables_after {t t' : Tables} {o : FnOut} (hle : TablesLe t t') (hlen : t'.len = o.len)
    (hsz : t'.shared.length = o.shared.length + t.shared.length)
    (htake : t'.shared.take o.shared.length = o.shared) : t' = t.after o := by
  obtain ⟨l, hl⟩ := hle.shared
  have hll : l.length = o.shared.length := by
    have := congrArg List.length hl
    simp only [List.length_append] at this
    omega
  have : l = o.shared := by
    rw [← htake, ← hl, ← hll, List.take_left]
  obtain ⟨len', sh'⟩ := t'
  simp only at hlen hl
  rw [Tables.after, ← hlen, ← hl, this]

/-- **What a success of `pieceOkWith` says**: `pieceOk`'s, and the test on the placed locations. -/
theorem pieceOkWith_spec {extra : VMap Loc → Bool} {loops : Loops} {sigs : SMap (Nat × Nat)}
    {l : Layout} {t : Tables} {tf : TracedFn} {o : FnOut} {pc0 frame : Nat} {cf : CompiledFunction}
    (h : pieceOkWith extra loops sigs l t tf o pc0 frame cf = true) :
    ∃ pf : Placed, placeFn loops sigs t tf = .ok (pf, t.after o) ∧
      (emitFn pf.fn).2.toList = o.fills.map (fun x => (x.1, KVal.at tf.core.name x.2)) ∧
      (emitFn pf.fn).1.name = tf.core.name ∧ (emitFn pf.fn).1.frameSize = o.frame ∧
      (emitFn pf.fn).1.code.size = o.size ∧ cf.name = tf.core.name ∧ cf.entryPc = pc0 ∧
      cf.instructionCount = o.size ∧
      chunked (resolvedFn l pc0 { (emitFn pf.fn).1 with frameSize := frame }) = cf.chunks ∧
      extra pf.locs = true := by
  unfold pieceOkWith at h
  split at h
  · cases h
  · next pf t' hpf =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlen, hsz⟩, htake⟩, hfills⟩, hframe⟩, hsize⟩, hname⟩, hpc⟩, hcount⟩, hcode⟩,
      hextra⟩ := h
    have hnm : pf.fn.name = tf.core.name := by
      obtain ⟨st', -, rfl, -⟩ := placeFn_ok hpf
      rfl
    refine ⟨pf, ?_, ?_, hnm, hframe, hsize, hname, hpc, hcount, hcode, hextra⟩
    · rw [tables_after (placeFn_tables hpf) hlen hsz htake] at hpf
      exact hpf
    · rw [← hnm]
      exact allPairs_fillIs _ _ (emitFn_fills_of pf.fn) hfills

/-- **What a success of `pieceOk` says.** -/
theorem pieceOk_spec {loops : Loops} {sigs : SMap (Nat × Nat)} {l : Layout} {t : Tables}
    {tf : TracedFn} {o : FnOut} {pc0 frame : Nat} {cf : CompiledFunction}
    (h : pieceOk loops sigs l t tf o pc0 frame cf = true) :
    ∃ pf : Placed, placeFn loops sigs t tf = .ok (pf, t.after o) ∧
      (emitFn pf.fn).2.toList = o.fills.map (fun x => (x.1, KVal.at tf.core.name x.2)) ∧
      (emitFn pf.fn).1.name = tf.core.name ∧ (emitFn pf.fn).1.frameSize = o.frame ∧
      (emitFn pf.fn).1.code.size = o.size ∧ cf.name = tf.core.name ∧ cf.entryPc = pc0 ∧
      cf.instructionCount = o.size ∧
      chunked (resolvedFn l pc0 { (emitFn pf.fn).1 with frameSize := frame }) = cf.chunks := by
  obtain ⟨pf, h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := pieceOkWith_spec h
  exact ⟨pf, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-! ## The pieces of a program -/

/-- **The pieces of a program**, from the jump tables `t` and the pc `pc`: function `tfs[j]`
gives `os[j]` and, resolved with frame size `frs[j]`, is `cfs[j]`, each at the pc past the ones
before it. -/
def Chain (loops : Loops) (sigs : SMap (Nat × Nat)) (l : Layout) : Tables → Nat →
    List TracedFn → List FnOut → List Nat → List CompiledFunction → Prop
  | _, _, [], [], [], [] => True
  | t, pc, tf :: tfs, o :: os, fr :: frs, cf :: cfs =>
      pieceOk loops sigs l t tf o pc fr cf = true ∧ Chain loops sigs l (t.after o) (pc + o.size) tfs os frs cfs
  | _, _, _, _, _, _ => False

/-- What the pieces of a program say of its placed functions. -/
def ChainOut (l : Layout) : Nat → List Placed → List TracedFn → List FnOut → List Nat →
    List CompiledFunction → Prop
  | _, [], [], [], [], [] => True
  | pc, pf :: pfs, tf :: tfs, o :: os, fr :: frs, cf :: cfs =>
      ((emitFn pf.fn).2.toList = o.fills.map (fun x => (x.1, KVal.at tf.core.name x.2)) ∧
        (emitFn pf.fn).1.name = tf.core.name ∧ (emitFn pf.fn).1.frameSize = o.frame ∧
        (emitFn pf.fn).1.code.size = o.size ∧ cf.name = tf.core.name ∧ cf.entryPc = pc ∧
        cf.instructionCount = o.size ∧
        chunked (resolvedFn l pc { (emitFn pf.fn).1 with frameSize := fr }) = cf.chunks) ∧
      ChainOut l (pc + o.size) pfs tfs os frs cfs
  | _, _, _, _, _, _ => False

/-- **The pieces of a program place it**, function by function. -/
theorem placeFns_of_chain {loops : Loops} {sigs : SMap (Nat × Nat)} {l : Layout} :
    ∀ (tfs : List TracedFn) (os : List FnOut) (frs : List Nat) (cfs : List CompiledFunction)
      (t : Tables) (pc : Nat), Chain loops sigs l t pc tfs os frs cfs →
      ∃ placed, placeFns loops sigs tfs t = .ok (placed, os.foldl Tables.after t) ∧
        ChainOut l pc placed tfs os frs cfs
  | [], [], [], [], t, pc, _ => ⟨[], rfl, trivial⟩
  | tf :: tfs, o :: os, fr :: frs, cf :: cfs, t, pc, ⟨hp, hc⟩ => by
      obtain ⟨pf, hpf, h1, h2, h3, h4, h5, h6, h7, h8⟩ := pieceOk_spec hp
      obtain ⟨placed, hrest, hout⟩ := placeFns_of_chain tfs os frs cfs _ _ hc
      refine ⟨pf :: placed, ?_, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, hout⟩
      rw [placeFns, hpf]
      simp only [hrest, List.foldl_cons]
  | [], _ :: _, _, _, _, _, h => nomatch h
  | [], [], _ :: _, _, _, _, h => nomatch h
  | [], [], [], _ :: _, _, _, h => nomatch h
  | _ :: _, [], _, _, _, _, h => nomatch h
  | _ :: _, _ :: _, [], _, _, _, h => nomatch h
  | _ :: _, _ :: _, _ :: _, [], _, _, h => nomatch h

/-! ## The assembled functions -/

/-- The compiled functions of `fns` laid out from `pc`, resolved at the layout `l`. -/
def fnsFrom (l : Layout) : List Lowered → Nat → List CompiledFunction
  | [], _ => []
  | f :: fs, pc => ⟨f.name, pc, f.code.size, chunked (resolvedFn l pc f)⟩ :: fnsFrom l fs (pc + f.code.size)

/-- **The functions of an assembled program**, when the layout gives each its entry. -/
theorem assembleAt_toFunctions (l : Layout) (size : Nat) (fns : List Lowered)
    (hent : ∀ pre f post, fns = pre ++ f :: post → l.entry.getD f.name (totalSize pre) = totalSize pre) :
    (assembleAt l size fns).toFunctions = fnsFrom l fns 0 := by
  generalize ha : assembleAt l size fns = a
  have hfns : a.fns.toList = rangesFrom fns 0 := by rw [← ha, assembleAt_fns]
  have hacode : a.code.toList = resolvedFrom l fns 0 := by rw [← ha, assembleAt_code]
  rw [toFunctions_eq, hfns]
  suffices h : ∀ (fs pre : List Lowered), fns = pre ++ fs →
      (rangesFrom fs (totalSize pre)).map a.fnOf = fnsFrom l fs (totalSize pre) by
    simpa [totalSize] using h fns [] rfl
  intro fs
  induction fs with
  | nil => intro _ _; rfl
  | cons f fs ih =>
      intro pre hsplit
      have hgetD := hent pre f fs hsplit
      have hcode : (a.code.extract (totalSize pre) (totalSize pre + f.code.size)).toList =
          resolvedFn l (totalSize pre) f := by
        rw [Array.toList_extract, hacode, hsplit, resolvedFrom_append, resolvedFrom, Nat.zero_add,
          hgetD, List.extract_eq_take_drop, List.drop_left' (resolvedFrom_length l pre 0),
          Nat.add_sub_cancel_left, List.take_left' (resolvedFn_length l _ f)]
      have hrest := ih (pre ++ [f]) (by rw [hsplit, List.append_assoc]; rfl)
      have hs : totalSize (pre ++ [f]) = totalSize pre + f.code.size := by simp [totalSize]
      rw [hs] at hrest
      simp only [rangesFrom, List.map_cons, fnsFrom, Assembled.fnOf, hcode, hrest]

/-- `layout` reads of a function its name, length and frame size. -/
theorem layout_eq_info (fns : List Lowered) (tb : Nat) :
    (layout fns tb).1 = { layoutInfo (fns.map infoOf) tb with gpow := gpowTable (layout fns tb).2 } := by
  suffices h : ∀ (fs : List Lowered) (e fr : SMap Nat) (pc : Nat),
      fs.foldl (fun (x : SMap Nat × SMap Nat × Nat) f =>
        (x.1.insert f.name x.2.2, x.2.1.insert f.name f.frameSize, x.2.2 + f.code.size)) (e, fr, pc) =
      (fs.map infoOf).foldl (fun (x : SMap Nat × SMap Nat × Nat) (i : String × Nat × Nat) =>
        (x.1.insert i.1 x.2.2, x.2.1.insert i.1 i.2.2, x.2.2 + i.2.1)) (e, fr, pc) by
    simp only [layout, layoutInfo]
    rw [h]
  intro fs
  induction fs with
  | nil => intro _ _ _; rfl
  | cons f fs ih => intro e fr pc; exact ih _ _ _

/-- A layout's powers, its table of `gpowTable` or none. -/
theorem pow_gpowTable (l : Layout) {n : Nat} (hn : n ≤ 2 ^ 128) :
    ({ l with gpow := gpowTable n } : Layout).pow = ({ l with gpow := #[] } : Layout).pow := by
  funext k
  simp only [Layout.pow]
  by_cases hk : k < n
  · rw [gpowTable_getElem? hk, gpowBits_eq, gpowK_eq (lt_of_lt_of_le hk hn)]
    rfl
  · have : (gpowTable n)[k]? = none := by
      rw [Array.getElem?_eq_none_iff, gpowTable_size]
      omega
    rw [this]
    rfl

theorem resolveOp_gpow (l : Layout) {n : Nat} (hn : n ≤ 2 ^ 128) (pc0 fs : Nat) (o : LOp) :
    resolveOp { l with gpow := gpowTable n } pc0 fs o = resolveOp { l with gpow := #[] } pc0 fs o := by
  have hp := pow_gpowTable l hn
  cases o with
  | set c k =>
      cases k <;> simp only [resolveOp, resolveK] <;> rw [hp]
  | _ => rfl

theorem resolvedFn_gpow (l : Layout) {n : Nat} (hn : n ≤ 2 ^ 128) (pc0 : Nat) (f : Lowered) :
    resolvedFn { l with gpow := gpowTable n } pc0 f = resolvedFn { l with gpow := #[] } pc0 f := by
  simp only [resolvedFn, resolveOp_gpow l hn]

theorem fnsFrom_gpow (l : Layout) {n : Nat} (hn : n ≤ 2 ^ 128) :
    ∀ (fs : List Lowered) (pc : Nat),
      fnsFrom { l with gpow := gpowTable n } fs pc = fnsFrom { l with gpow := #[] } fs pc
  | [], _ => rfl
  | f :: fs, pc => by simp only [fnsFrom, resolvedFn_gpow l hn, fnsFrom_gpow l hn fs]

theorem layoutInfo_gpow (info : List (String × Nat × Nat)) (tb : Nat) :
    ({ layoutInfo info tb with gpow := #[] } : Layout) = layoutInfo info tb := rfl

/-- **The functions `assemble` lays out**, at the layout of their names, lengths and frame sizes,
when the padded size is at most `2^128`. -/
theorem assemble_toFunctions (fns : List Lowered) (slots : Array KVal)
    (hnd : ((withTables fns slots).1.map (·.name)).Nodup)
    (hsize : (assemble fns slots).size ≤ 2 ^ 128) :
    (assemble fns slots).toFunctions =
      fnsFrom (layoutInfo ((withTables fns slots).1.map infoOf) (withTables fns slots).2)
        (withTables fns slots).1 0 := by
  rw [assemble_def] at hsize ⊢
  rw [assembleAt_toFunctions]
  · rw [layout_eq_info, fnsFrom_gpow _ (by rw [assembleAt_size] at hsize; exact hsize)]
    rfl
  · intro pre f post hsplit
    rw [KMap.getD_eq_getD_getElem?, layout_entry _ hnd hsplit]
    rfl

/-! ## A program compiled from its pieces -/

theorem fillsOf_of_chainOut {l : Layout} : ∀ (placed : List Placed) (tfs : List TracedFn)
    (os : List FnOut) (frs : List Nat) (cfs : List CompiledFunction) (pc : Nat),
    ChainOut l pc placed tfs os frs cfs →
      fillsOf placed = (tfs.zip os).flatMap fun x => fillsOfOut x.1 x.2
  | [], [], [], [], [], _, _ => rfl
  | pf :: pfs, tf :: tfs, o :: os, fr :: frs, cf :: cfs, pc, ⟨h, hr⟩ => by
      have := fillsOf_of_chainOut pfs tfs os frs cfs _ hr
      simp only [fillsOf, List.flatMap_cons, List.zip_cons_cons] at this ⊢
      rw [h.1, this]
      rfl
  | [], _ :: _, _, _, _, _, h => nomatch h
  | [], [], _ :: _, _, _, _, h => nomatch h
  | [], [], [], _ :: _, _, _, h => nomatch h
  | [], [], [], [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, _, _, _, h => nomatch h
  | _ :: _, _ :: _, [], _, _, _, h => nomatch h
  | _ :: _, _ :: _, _ :: _, [], _, _, h => nomatch h
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, h => nomatch h

theorem fnsFrom_of_chainOut {l : Layout} : ∀ (placed : List Placed) (tfs : List TracedFn)
    (os : List FnOut) (frs : List Nat) (cfs : List CompiledFunction) (pc : Nat),
    ChainOut l pc placed tfs os frs cfs →
      fnsFrom l (List.zipWith (fun pf fr => { (emitFn pf.fn).1 with frameSize := fr }) placed frs) pc =
        cfs
  | [], [], [], [], [], _, _ => rfl
  | pf :: pfs, tf :: tfs, o :: os, fr :: frs, cf :: cfs, pc, ⟨⟨_, h2, _, h4, h5, h6, h7, h8⟩, hr⟩ => by
      have := fnsFrom_of_chainOut pfs tfs os frs cfs _ hr
      simp only [List.zipWith_cons_cons, fnsFrom]
      rw [h4, this, h8]
      obtain ⟨n, e, c, ch⟩ := cf
      simp only at h5 h6 h7
      rw [h2, h5, h6, h7]
  | [], _ :: _, _, _, _, _, h => nomatch h
  | [], [], _ :: _, _, _, _, h => nomatch h
  | [], [], [], _ :: _, _, _, h => nomatch h
  | [], [], [], [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, _, _, _, h => nomatch h
  | _ :: _, _ :: _, [], _, _, _, h => nomatch h
  | _ :: _, _ :: _, _ :: _, [], _, _, h => nomatch h
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, h => nomatch h

theorem chainOut_frames {l : Layout} : ∀ (placed : List Placed) (tfs : List TracedFn)
    (os : List FnOut) (frs : List Nat) (cfs : List CompiledFunction) (pc : Nat),
    ChainOut l pc placed tfs os frs cfs → frs = os.map (·.frame) →
      List.zipWith (fun pf fr => { (emitFn pf.fn).1 with frameSize := fr }) placed frs =
        placed.map fun pf => (emitFn pf.fn).1
  | [], [], [], [], [], _, _, _ => rfl
  | pf :: pfs, tf :: tfs, o :: os, fr :: frs, cf :: cfs, pc, ⟨⟨_, _, h3, _⟩, hr⟩, hf => by
      simp only [List.map_cons, List.cons.injEq] at hf
      simp only [List.zipWith_cons_cons, List.map_cons]
      rw [chainOut_frames pfs tfs os frs cfs _ hr hf.2, hf.1, ← h3]
  | [], _ :: _, _, _, _, _, h, _ => nomatch h
  | [], [], _ :: _, _, _, _, h, _ => nomatch h
  | [], [], [], _ :: _, _, _, h, _ => nomatch h
  | [], [], [], [], _ :: _, _, h, _ => nomatch h
  | _ :: _, [], _, _, _, _, h, _ => nomatch h
  | _ :: _, _ :: _, [], _, _, _, h, _ => nomatch h
  | _ :: _, _ :: _, _ :: _, [], _, _, h, _ => nomatch h
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, h, _ => nomatch h

theorem chainOut_info {l : Layout} : ∀ (placed : List Placed) (tfs : List TracedFn)
    (os : List FnOut) (frs : List Nat) (cfs : List CompiledFunction) (pc : Nat),
    ChainOut l pc placed tfs os frs cfs →
      (placed.map fun pf => infoOf (emitFn pf.fn).1) =
        (tfs.zip os).map fun x => (x.1.core.name, x.2.size, x.2.frame)
  | [], [], [], [], [], _, _ => rfl
  | pf :: pfs, tf :: tfs, o :: os, fr :: frs, cf :: cfs, pc, ⟨⟨_, h2, h3, h4, _⟩, hr⟩ => by
      have := chainOut_info pfs tfs os frs cfs _ hr
      simp only [List.map_cons, List.zip_cons_cons, infoOf] at this ⊢
      rw [h2, h3, h4, this]
  | [], _ :: _, _, _, _, _, h => nomatch h
  | [], [], _ :: _, _, _, _, h => nomatch h
  | [], [], [], _ :: _, _, _, h => nomatch h
  | [], [], [], [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, _, _, _, h => nomatch h
  | _ :: _, _ :: _, [], _, _, _, h => nomatch h
  | _ :: _, _ :: _, _ :: _, [], _, _, h => nomatch h
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, h => nomatch h

theorem tableSlots_size (len : Nat) (fills : Array Fill) (shared : Array (Nat × String)) :
    (tableSlots len fills shared).size = len := by
  simp [tableSlots]

end
end LeanVM.Compiler
