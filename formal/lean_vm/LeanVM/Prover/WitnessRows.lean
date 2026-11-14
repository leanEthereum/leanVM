/-
  LeanVM.Prover.WitnessRows

  The executable rows of a run are the specification's: `rowsOf` over the run's steps holds, table
  by table, the raw rows of `skelRows` of the run's skeletons, and its counters are the finalize
  counts of the memory and bytecode blocks.
-/

module

public import Statement.Prover.Columns
public import LeanVM.Arithmetization.Completeness.Witness
public import LeanVM.Prover.WitnessRun

/-!
# The rows of a run

`rowIn_powIndex`: through the memory index, a step's raw row is `rowOf`, cell for cell (the typed
rows of the tables flattened, `xorRow_toArray` and its siblings). `countReads_spec`: the counts
of a sequence of reads are `g` to the numbers `readExps` gives them, and the counters after them
`g` to `readBump`. `rowsOf_spec`: over the steps of a valid run, `rowsOf` holds in table `op` the
raw rows of the rows of `skelRows` of the skeletons with that opcode, and its counters are `g` to
`skelMemFin` and `skelBcFin`, cell by cell.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Extraction
open LeanVM.Protocol.Halting

@[expose] public section

/-! ## The typed rows, flattened -/

theorem xorRow_toArray {F : Type} (r : XorRow F) : (toElements r).toArray =
    #[r.pc, r.fp, r.oA, r.oB, r.oC, r.vA[0], r.vA[1], r.vB[0], r.vB[1], r.rA, r.rB, r.rC,
      r.rbc] := by
  obtain ⟨pc, fp, oA, oB, oC, vA, vB, rA, rB, rC, rbc⟩ := r
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]
  apply Array.toList_inj.mp
  rw [Vector.toList_toArray]
  repeat rw [Vector.toList_append]
  rw [vec2_toList, vec2_toList]
  simp

theorem mulRow_toArray {F : Type} (r : MulRow F) : (toElements r).toArray =
    #[r.pc, r.fp, r.oA, r.oB, r.oC, r.vA[0], r.vA[1], r.vB[0], r.vB[1], r.rA, r.rB, r.rC,
      r.rbc] := by
  obtain ⟨pc, fp, oA, oB, oC, vA, vB, rA, rB, rC, rbc⟩ := r
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]
  apply Array.toList_inj.mp
  rw [Vector.toList_toArray]
  repeat rw [Vector.toList_append]
  rw [vec2_toList, vec2_toList]
  simp

theorem setRow_toArray {F : Type} (r : SetRow F) : (toElements r).toArray =
    #[r.pc, r.fp, r.o, r.k[0], r.k[1], r.r, r.rbc] := by
  obtain ⟨pc, fp, o, k, rr, rbc⟩ := r
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]
  apply Array.toList_inj.mp
  rw [Vector.toList_toArray]
  repeat rw [Vector.toList_append]
  rw [vec2_toList]
  simp

theorem derefRow_toArray {F : Type} (r : DerefRow F) : (toElements r).toArray =
    #[r.pc, r.fp, r.o1, r.o2, r.o3, r.fpc, r.ffp, r.p, r.v3[0], r.v3[1], r.r1, r.r2, r.r3,
      r.rbc] := by
  obtain ⟨pc, fp, o1, o2, o3, fpc, ffp, p, v3, r1, r2, r3, rbc⟩ := r
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]
  apply Array.toList_inj.mp
  rw [Vector.toList_toArray]
  repeat rw [Vector.toList_append]
  rw [vec2_toList]
  simp

theorem jumpRow_toArray {F : Type} (r : JumpRow F) : (toElements r).toArray =
    #[r.pc, r.fp, r.oc, r.od, r.of, r.vcond, r.vpc, r.vfp, r.rc, r.rd, r.rf, r.rbc] := by
  obtain ⟨pc, fp, oc, od, of, vcond, vpc, vfp, rc, rd, rf, rbc⟩ := r
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]
  apply Array.toList_inj.mp
  rw [Vector.toList_toArray]
  repeat rw [Vector.toList_append]
  simp

/-- A vector of four is the list of its entries. -/
theorem vec4_toList {F : Type} (v : Vector F 4) : v.toList = [v[0], v[1], v[2], v[3]] := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have : i < 4 := by simpa using h1
  interval_cases i <;> simp

theorem keccakRow_toArray {F : Type} (r : KeccakRow F) : (toElements r).toArray =
    #[r.pc, r.fp, r.om[0], r.om[1], r.om[2], r.om[3], r.otail, r.ob8, r.ocap, r.oout, r.oddIn,
      r.oddOut, r.outTwo, r.outAll, r.free] ++ r.lin.toArray ++ r.lout.toArray ++ r.cnt.toArray ++
        #[r.rbc] := by
  obtain ⟨pc, fp, om, otail, ob8, ocap, oout, oddIn, oddOut, outTwo, outAll, free, lin, lout, cnt,
    rbc⟩ := r
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]
  apply Array.toList_inj.mp
  rw [Vector.toList_toArray]
  repeat rw [Vector.toList_append]
  simp [vec4_toList, Vector.toList_push, Vector.toList_toArray]

theorem memRow_toArray {F : Type} (r : MemRow F) : (toElements r).toArray =
    #[r.m[0], r.m[1], r.idx, r.cntFin] := by
  obtain ⟨m, idx, cntFin⟩ := r
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]
  apply Array.toList_inj.mp
  rw [Vector.toList_toArray]
  repeat rw [Vector.toList_append]
  rw [vec2_toList]
  simp

theorem bytecodeRow_toArray {F : Type} (r : BytecodeRow F) : (toElements r).toArray =
    #[r.idx, r.cntFin, r.opcode] ++ r.op.toArray := by
  obtain ⟨idx, cntFin, opcode, op⟩ := r
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]
  apply Array.toList_inj.mp
  rw [Vector.toList_toArray]
  repeat rw [Vector.toList_append]
  simp [Vector.toList_toArray]

/-! ## Through the index -/

variable {κ : ℕ}

/-- The reader through the index is the image's. -/
theorem readIn_powIndex (hκ : κ < 64) (img : MemoryImage κ) :
    readIn (powIndex κ) img = img.read := by
  funext a
  unfold readIn MemoryImage.read
  rw [gLogIn_powIndex hκ]

/-- The limbs through the index are the image's. -/
theorem limbsIn_powIndex (hκ : κ < 64) (img : MemoryImage κ) :
    limbsIn (powIndex κ) img = img.limbsAt := by
  funext a
  unfold limbsIn MemoryImage.limbsAt
  rw [readIn_powIndex hκ]
  cases img.read a <;> rfl

/-- The cells an instruction reads, through the index, are `readAddrs`. -/
theorem addrsIn_powIndex (hκ : κ < 64) (img : MemoryImage κ) (fp : K) (ins : LeanIsaInstruction) :
    addrsIn (powIndex κ) img fp ins = readAddrs img fp ins := by
  cases ins <;> first | (simp only [addrsIn, readAddrs, limbsIn_powIndex hκ]; done) | rfl

/-- The cells a `KECCAK` reads, through the index, are `keccakInputCells`. -/
theorem keccakInputIn_powIndex (hκ : κ < 64) (img : MemoryImage κ) (fp : K) (om : Fin 4 → K)
    (otail ob8 ocap : K) :
    keccakInputIn (powIndex κ) img fp om otail ob8 ocap =
      keccakInputCells img fp om otail ob8 ocap := by
  funext c
  unfold keccakInputIn keccakInputCells
  rw [readIn_powIndex hκ]

/-- **The raw row through the index is `rowOf`.** -/
theorem rowIn_powIndex (hκ : κ < 64) (img : MemoryImage κ) (pc fp : K) (c : ℕ → K) (rbc : K)
    (ins : LeanIsaInstruction) : rowIn (powIndex κ) img pc fp c rbc ins = rowOf img pc fp c rbc
        ins := by
  cases ins with
  | xor oA oB oC =>
    simp only [rowIn, rowOf, rawRow, xorRow_toArray, xorRowOf, limbsIn_powIndex hκ]
  | mulNative oA oB oC =>
    simp only [rowIn, rowOf, rawRow, mulRow_toArray, mulRowOf, limbsIn_powIndex hκ]
  | setConstant o k =>
    simp only [rowIn, rowOf, rawRow, setRow_toArray, setRowOf]
    simp
  | deref o1 o2 o3 mode =>
    simp only [rowIn, rowOf, rawRow, derefRow_toArray, derefRowOf, limbsIn_powIndex hκ]
  | jump oc od of =>
    simp only [rowIn, rowOf, jumpRaw, rawRow, jumpRow_toArray, jumpRowOf, limbsIn_powIndex hκ]
    simp
  | keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    simp only [rowIn, rowOf, rawRow, keccakRow_toArray, keccakRowOf,
      keccakInputIn_powIndex hκ]
    simp [laneK, freeLimb]
    rfl

/-! ## The counters -/

/-- Powers of `g` below `2^κ`, `κ < 64`, are distinct. -/
theorem gpow_inj (hκ : κ < 64) {i j : ℕ} (hi : i < 2 ^ κ) (hj : j < 2 ^ κ) :
    addressOfIndex i = addressOfIndex j ↔ i = j := by
  have hb : 2 ^ κ ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨fun h ↦ gpow_injOn (by simp; omega) (by simp; omega) h, fun h ↦ h ▸ rfl⟩

/-- A counter array: `g` to the counter of each address, `2^κ` of them. -/
def CtrOk (κ : ℕ) (s : K → ℕ) (ctr : Array K) : Prop :=
  ctr.size = 2 ^ κ ∧ ∀ i (h : i < ctr.size), ctr[i] = g ^ s (addressOfIndex i)

/-- One read steps its cell's counter. -/
theorem ctrOk_modify (hκ : κ < 64) {s : K → ℕ} {ctr : Array K} (h : CtrOk κ s ctr) {i : ℕ}
    (hi : i < 2 ^ κ) :
    CtrOk κ (Function.update s (addressOfIndex i) (s (addressOfIndex i) + 1)) (ctr.modify i (g *
        ·)) := by
  refine ⟨by rw [Array.size_modify, h.1], fun j hj ↦ ?_⟩
  have hj' : j < 2 ^ κ := by rw [Array.size_modify, h.1] at hj; exact hj
  rw [Array.getElem_modify]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, h.2 i (by rw [h.1]; exact hi), Function.update_self, pow_succ']
  · rw [ite_eq_right hij, h.2 j (by rw [h.1]; exact hj'), Function.update_of_ne]
    exact fun e ↦ hij ((gpow_inj hκ hj' hi).mp e).symm

/-- **The counts of a sequence of reads**: `g` to the numbers `readExps` gives them, the counters
after them `g` to `readBump`. -/
theorem countReads_spec (hκ : κ < 64) :
    ∀ (as : List K) (s : K → ℕ) (cs ctr : Array K), (∀ a ∈ as, ∃ i, i < 2 ^ κ ∧ a =
        addressOfIndex i) →
      CtrOk κ s ctr →
      (countReads (powIndex κ) κ as cs ctr).1 = cs ++ ((readExps s as).map (g ^ ·)).toArray ∧
      CtrOk κ (readBump s as) (countReads (powIndex κ) κ as cs ctr).2
  | [], s, cs, ctr, _, h => by simp [countReads, readExps, readBump, h]
  | a :: rest, s, cs, ctr, ha, h => by
    obtain ⟨i, hi, rfl⟩ := ha a List.mem_cons_self
    have hg : gLogIn (powIndex κ) κ (addressOfIndex i) = some ⟨i, hi⟩ := by
      rw [gLogIn_powIndex hκ]
      exact (gLog?_spec hκ (i := ⟨i, hi⟩)).mpr rfl
    have hget : ctr.getD i 1 = g ^ s (addressOfIndex i) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [h.1]; exact hi),
        Option.getD_some, h.2]
    obtain ⟨h1, h2⟩ := countReads_spec hκ rest (Function.update s (addressOfIndex i) (s
        (addressOfIndex i) + 1))
      (cs.push (ctr.getD i 1)) (ctr.modify i (g * ·))
      (fun a ha' ↦ ha a (List.mem_cons_of_mem _ ha')) (ctrOk_modify hκ h hi)
    simp only [countReads, hg]
    refine ⟨?_, h2⟩
    rw [h1, hget]
    simp [readExps]

/-! ## The rows of a list of skeletons, one more -/

/-- The rows of a list of skeletons with one more: the rows of the list, then the row of the last,
its reads numbered from the counters the list leaves. -/
theorem mkRows_concat (img : MemoryImage κ) (S : List Skel) (sk : Skel) :
    ∀ sm sb : K → ℕ, mkRows img sm sb (S ++ [sk]) = mkRows img sm sb S ++
      [⟨sk, readExps (readBump sm (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins))
          (readAddrs img sk.fp sk.ins), readBump sb (S.map (·.pc)) sk.pc⟩] := by
  induction S with
  | nil => intro sm sb; rfl
  | cons a S ih =>
    intro sm sb
    simp only [List.cons_append, mkRows, ih, List.flatMap_cons, readBump_append, List.map_cons]
    rfl

/-! ## The invariant of the pass -/

/-- What the pass has built after the steps of the skeletons `S`: each table's rows are the raw
rows of `S`'s rows of its opcode, and the counters are `g` to the reads so far. -/
structure RowsInv (img : MemoryImage κ) (logSize : ℕ) (acc : Rows) (S : List Skel) : Prop where
  tabs_size : acc.tabs.size = 6
  tabs : ∀ op, (acc.tabs.getD (opTableIdx op) #[]).toList =
    ((mkRows img (fun _ ↦ 0) (fun _ ↦ 0) S).filter fun r ↦ r.sk.ins.opcode = op).map
      (PRow.raw img)
  mem : CtrOk κ (readBump (fun _ ↦ 0) (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)) acc.mem
  bc : CtrOk logSize (readBump (fun _ ↦ 0) (S.map (·.pc))) acc.bc

/-- The table index of an opcode is below six. -/
theorem tableOf_lt (op : Opcode) : opTableIdx op < 6 := by cases op <;> decide

/-- Distinct opcodes have distinct tables. -/
theorem tableOf_inj {op op' : Opcode} (h : opTableIdx op = opTableIdx op') : op = op' := by
  cases op <;> cases op' <;> first | rfl | exact absurd h (by decide)

/-- The pass starts from the invariant. -/
theorem rowsInv_init (img : MemoryImage κ) (logSize : ℕ) :
    RowsInv img logSize ⟨Array.replicate 6 #[], Array.replicate (2 ^ κ) 1,
      Array.replicate (2 ^ logSize) 1⟩ [] := by
  refine ⟨by simp, fun op ↦ ?_, ⟨by simp, fun i h ↦ ?_⟩, ⟨by simp, fun i h ↦ ?_⟩⟩
  · have := tableOf_lt op
    simp [mkRows, Array.getD_eq_getD_getElem?, this]
  · simp [readBump]
  · simp [readBump]

/-- One read bumps its cell's counter. -/
theorem readBump_single {ι : Type} [DecidableEq ι] (s : ι → ℕ) (a : ι) :
    readBump s [a] = Function.update s a (s a + 1) := rfl

/-- `g` to a list of numbers, read with the default `1`, is `g` to the list read with `0`. -/
theorem getD_map_pow (l : List ℕ) (j : ℕ) : (l.map (g ^ ·)).toArray.getD j 1 = g ^ l.getD j 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getD_eq_getElem?_getD]
  cases l[j]? <;> simp

/-- One step of the pass, unfolded. -/
theorem stepRows_eq (memIdx : Std.HashMap UInt64 ℕ) (img : MemoryImage κ) (acc : Rows) (st : Step) :
    stepRows memIdx img acc st =
      ⟨acc.tabs.modify (opTableIdx st.ins.opcode) (·.push (rowIn memIdx img st.pc st.fp
          (fun j ↦ (countReads memIdx κ (addrsIn memIdx img st.fp st.ins) #[] acc.mem).1.getD j 1)
          (acc.bc.getD st.slot 1) st.ins)),
        (countReads memIdx κ (addrsIn memIdx img st.fp st.ins) #[] acc.mem).2,
        acc.bc.modify st.slot (g * ·)⟩ := rfl

/-- **One step keeps the invariant.** -/
theorem rowsInv_step (hκ : κ < 64) {prog : LeanIsaProgram} (img : MemoryImage κ) {acc : Rows}
    {S : List Skel} (h : RowsInv img prog.logSize acc S) {st : Step}
    (hst : StepOk prog img st) :
    RowsInv img prog.logSize (stepRows (powIndex κ) img acc st) (S ++ [st.toSkel]) := by
  obtain ⟨hslot, hpc, -, next, hex⟩ := hst
  have hvalid : ∀ a ∈ readAddrs img st.fp st.ins, ∃ i, i < 2 ^ κ ∧ a = addressOfIndex i := by
    intro a ha
    obtain ⟨w, hw⟩ := readAddrs_valid hex a ha
    obtain ⟨i, hi, -⟩ := (MemoryImage.read_eq_some_iff hκ img).mp hw
    exact ⟨i, i.isLt, hi⟩
  obtain ⟨hc1, hc2⟩ := countReads_spec hκ (readAddrs img st.fp st.ins)
    (readBump (fun _ ↦ 0) (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)) #[] acc.mem
    hvalid h.mem
  have hbc : acc.bc.getD st.slot 1 = g ^ readBump (fun _ ↦ 0) (S.map (·.pc)) st.pc := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [h.bc.1]; exact hslot),
      Option.getD_some, h.bc.2, hpc]
  have hrow : rowIn (powIndex κ) img st.pc st.fp
      (fun j ↦ (countReads (powIndex κ) κ (addrsIn (powIndex κ) img st.fp st.ins) #[]
        acc.mem).1.getD j 1) (acc.bc.getD st.slot 1) st.ins =
      PRow.raw img ⟨st.toSkel, readExps (readBump (fun _ ↦ 0)
        (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)) (readAddrs img st.fp st.ins),
        readBump (fun _ ↦ 0) (S.map (·.pc)) st.pc⟩ := by
    have hcnt : (fun j ↦ (countReads (powIndex κ) κ (addrsIn (powIndex κ) img st.fp st.ins) #[]
        acc.mem).1.getD j 1) = PRow.cnt ⟨st.toSkel, readExps (readBump (fun _ ↦ 0)
          (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)) (readAddrs img st.fp st.ins),
          readBump (fun _ ↦ 0) (S.map (·.pc)) st.pc⟩ := by
      funext j
      rw [addrsIn_powIndex hκ, hc1]
      simp only [PRow.cnt, Array.empty_append, getD_map_pow]
    rw [hcnt, rowIn_powIndex hκ, hbc]
    rfl
  rw [stepRows_eq]
  refine ⟨by simp [h.tabs_size], fun op ↦ ?_, ?_, ?_⟩
  · rw [mkRows_concat, List.filter_append, List.map_append]
    have hlt := tableOf_lt op
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem
      (by rw [Array.size_modify, h.tabs_size]; exact hlt), Option.getD_some, Array.getElem_modify]
    have hold := h.tabs op
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [h.tabs_size]; exact hlt),
      Option.getD_some] at hold
    by_cases hop : st.ins.opcode = op
    · rw [ite_eq_left (by rw [hop]), Array.toList_push, hold, hrow]
      simp [Step.toSkel, hop]
    · rw [ite_eq_right (fun e ↦ hop (tableOf_inj e)), hold]
      simp [Step.toSkel, hop]
  · rw [List.flatMap_append, readBump_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, addrsIn_powIndex hκ]
    exact hc2
  · have := ctrOk_modify (LeanVM.Protocol.Halting.logSize_lt prog) h.bc hslot
    rw [← hpc] at this
    rw [List.map_append, readBump_append, List.map_cons, List.map_nil, readBump_single]
    exact this

/-- **The rows of a valid run's steps.** Over steps that each fetch and execute, the pass holds,
table by table, the raw rows of the rows of their skeletons, and its counters are `g` to the
finalize counts. -/
theorem rowsInv_rowsOf (hκ : κ < 64) {prog : LeanIsaProgram} (img : MemoryImage κ) (L : List Step)
    (hL : ∀ st ∈ L, StepOk prog img st) :
    RowsInv img prog.logSize (rowsOf (powIndex κ) img prog.logSize L.toArray)
      (L.map Step.toSkel) := by
  unfold rowsOf
  rw [List.foldl_toArray]
  suffices ∀ (L₁ L₂ : List Step) (acc : Rows), (∀ st ∈ L₂, StepOk prog img st) →
      RowsInv img prog.logSize acc (L₁.map Step.toSkel) →
      RowsInv img prog.logSize (L₂.foldl (stepRows (powIndex κ) img) acc)
        ((L₁ ++ L₂).map Step.toSkel) from
    this [] L _ hL (rowsInv_init img prog.logSize)
  intro L₁ L₂
  induction L₂ generalizing L₁ with
  | nil => intro acc _ h; simpa using h
  | cons st rest ih =>
    intro acc hrest h
    have h' := rowsInv_step hκ img h (hrest st List.mem_cons_self)
    have := ih (L₁ ++ [st]) _ (fun st' hs ↦ hrest st' (List.mem_cons_of_mem _ hs))
      (by simpa using h')
    simpa using this

end

end LeanVM.Prover
