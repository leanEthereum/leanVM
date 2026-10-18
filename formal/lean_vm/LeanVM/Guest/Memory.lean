/-
  LeanVM.Guest.Memory

  The honest memory of an evaluation of the guest's core IR: frames and `HeapBuf`s by the bump
  allocator, every frame cell holding its value, the public input in `main`'s header, and the
  words the paths read; write-once consistent, of at most `2^32` words, and the evaluation
  valid on it.
-/

module

public import LeanVM.Guest.Memory.Alloc
public import LeanVM.Guest.Memory.Tree
public import LeanVM.Guest.Memory.Placed
public import LeanVM.Guest.Data.Bytecode00

/-!
# The honest memory

B2's completeness direction runs the compiled guest on a memory built from an honest
evaluation of its core IR (`Tree.Valid`, `Memory/Eval.lean`): a call tree with one valuation per
call instance, which a derivation of `Program.Rel` is for a well-formed program
(`Program.Rel.tree`, `Memory/Tree.lean`). This file builds that memory and states what the
checker's completeness consumes.

**Inputs.** The evaluation `T` from `main`, valid on some reader `rd`; the frame sizes `fs`
(the certificate's); the header of each callee, `H I i` (`fp[0]`, `fp[1]`: the return pc and
the caller's frame, or the caller's own header for a tail call); and the cells of each frame,
`C I` (offset, word): the certificate's cell of each value with its word (`valueCells`), and
whatever plumbing the compiled code writes (callee frame pointers, jump targets, a loop's next
frame, `main`'s jump table, `tableCells`).

**The memory** (`honest`): the bump allocator places `T` from word `0` (`Tree.insts`, `main`'s
frame at `fp = g^0 = 1`, its header the public input), and the image holds every frame's header
and cells and every memory equation of the paths (`Tree.eqns`: what the loads, range checks and
frame runs read), on `2^logMem n` words for the `n` words allocated.

**Hypotheses** (`Honest`): the evaluation is valid, at most `2^32` words are allocated, the cells
fit their frames past the header and agree at one offset (`CellsOk`; distinct values of one
frame may share a cell when they hold one word, as the compiler's shared cells do), the
equations name addresses of the memory, agree among themselves (`Tree.Valid.eqns_consistent`:
they do on any memory the evaluation is valid on), and agree with the frames where they meet
(`cross`: an equation in a `HeapBuf` meets no frame, `frameWrites_not_buf`; one in a frame,
a `StackBuf` read through `frameAddr` or a range check landing there, reads what the frame
holds; both hold when one memory holds the frames and the equations, `cross_of_read`).

**Conclusions.** The image is consistent (`Honest.consistent`); every frame's header, cells
and certificate values read back at `fp · g^o` (`Honest.read_hdr`, `read_C`, `read_value`), and
every equation (`Honest.read_eqn`); the evaluation and every instance in it are valid on the
image (`Honest.valid_image`, `Honest.inst_good`); a callee is the instance at its caller's
callee frame (`honest_kid`), a loop helper's tail call at `fp + fs f` (`honest_kidFps_getLast?`); the
public input is in words `0`, `1` and `minLogMem ≤ κ ≤ maxLogMem` (`Honest.publicBoundary`).
`Trace.committedSize ≤ 2^28` is the end theorem's: `logMem_le_iff` and `two_pow_logMem_le`
bound `2^κ` by the words allocated.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-! ## Validity of the instances -/

section Valid

variable {P : Core.Program} {rd : Reader} {fs : String → ℕ} {lp : String → Bool}
  {H : Inst → ℕ → E × E}

/-- An instance that runs is a valid tree; the others are phantoms. -/
def Inst.Good (P : Core.Program) (rd : Reader) (I : Inst) : Prop :=
  (∃ args rets, I.t.Valid P rd args rets) ∨ ∃ f σ, I.t = .phantom f σ

mutual
/-- Every instance of a valid tree is valid or a phantom. -/
theorem insts_good : ∀ (t : Tree) (fp : ℕ) (hdr : E × E) {args rets : List E},
    t.Valid P rd args rets → ∀ I ∈ t.insts fs lp H fp hdr, I.Good P rd
  | .node f σ bufs kids, fp, hdr, args, rets, hv, I, hI => by
      rw [insts_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact Or.inl ⟨args, rets, hv⟩
      · obtain ⟨_, _, _, es, _, _, _, _, hk⟩ := hv
        exact instsKids_good kids σ (calls es) _ 0 _ hk I hI
  | .phantom .., _, _, _, _, hv, _, _ => hv.elim

/-- `insts_good` for the callees. -/
theorem instsKids_good : ∀ (ks : List Tree) (σ : Val) (cs : List Call) (I : Inst) (j : ℕ)
    (ps : List ℕ), Tree.KidsValid P rd σ cs ks → ∀ J ∈ Tree.instsKids fs lp H I j ps ks, J.Good P rd
  | [], _, _, _, _, _, _, J, hJ => by rw [instsKids_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, _, _, _, _, [], _, J, hJ => by
      rw [instsKids_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, σ, c :: cs, I, j, p :: ps, ⟨_, hc, hks⟩, J, hJ => by
      rw [instsKids_cons, List.mem_append] at hJ
      rcases hJ with hJ | hJ
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hc
          exact insts_good k _ _ hc J hJ
        · rw [ite_eq_right ht] at hc
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
          rw [insts_phantom, List.mem_singleton] at hJ
          exact Or.inr ⟨f, σ', by rw [hJ]⟩
      · exact instsKids_good ks σ cs I (j + 1) ps hks J hJ
  | _ :: _, _, [], _, _, _ :: _, h, _, _ => h.elim
end

end Valid

/-! ## Equations -/

/-- **The equations are consistent** when the evaluation is valid on a memory holding their
addresses. -/
theorem Tree.Valid.eqns_consistent {P : Core.Program} {κ : ℕ} (hκ : κ < 64) {M : MemImage κ}
    {T : Tree} {args rets : List E} (hv : T.Valid P M.read args rets)
    (ha : ∀ q ∈ T.eqns P, ∃ i : Fin (2 ^ κ), q.1 = gpow i) : Consistent (T.eqns P) :=
  consistent_of_read fun q hq => hv.eqns_read hκ T q hq (ha q hq)

/-! ## The honest memory -/

section Honest

variable (P : Core.Program) (fs : String → ℕ) (H : Inst → ℕ → E × E) (C : Inst → List (ℕ × E))
  (hdr : E × E) (T : Tree)

/-- The placed call instances, `main` at word `0`. -/
def honestInsts : List Inst := T.insts fs P.loop H 0 hdr

/-- **The honest memory**: the frames' writes and the paths' equations, on `2^logMem` words for
the words allocated. -/
noncomputable def honest : MemImage (logMem (T.total fs)) :=
  image (logMem (T.total fs)) (frameWrites C (honestInsts P fs H hdr T) ++ T.eqns P)

/-- What the honest memory needs. -/
structure Honest (rd : Reader) (args rets : List E) : Prop where
  /-- The evaluation, on some reader. -/
  valid : T.Valid P rd args rets
  /-- At most `2^32` words are allocated. -/
  size : T.total fs ≤ 2 ^ 32
  /-- The cells fit their frames and agree. -/
  cells : CellsOk fs C (honestInsts P fs H hdr T)
  /-- The equations name addresses of the memory. -/
  addr : ∀ q ∈ T.eqns P, ∃ i : Fin (2 ^ logMem (T.total fs)), q.1 = gpow i
  /-- The equations agree among themselves. -/
  eqns : Consistent (T.eqns P)
  /-- The equations agree with the frames where they meet. -/
  cross : ∀ a ∈ frameWrites C (honestInsts P fs H hdr T), ∀ b ∈ T.eqns P, a.1 = b.1 → a.2 = b.2

/-- What the honest memory of a placed tree needs: `Honest`, every `HeapBuf` that of its path,
and the tree placed from `main`'s frame at word `0` (`Tree.Placed`, the certificate `cert` placing
the `frameAddr`s), so that every `HeapBuf` pointer is its instance's base and every `frameAddr`
the address of its run (`HonestAt.nodeAt`). -/
structure HonestAt (cert : String → V → ℕ) (rd : Reader) (args rets : List E) : Prop
    extends Honest P fs H C hdr T rd args rets where
  /-- The `HeapBuf`s are those of the paths. -/
  bufsOk : T.BufsOk P
  /-- The tree is placed from word `0`. -/
  placed : T.Placed P fs cert 0

variable {P fs H C hdr T} {rd : Reader} {args rets : List E}

theorem Honest.logMem_le (h : Honest P fs H C hdr T rd args rets) :
    logMem (T.total fs) ≤ maxLogMem :=
  logMem_le_maxLogMem h.size

theorem Honest.lt_64 (h : Honest P fs H C hdr T rd args rets) : logMem (T.total fs) < 64 := by
  have := h.logMem_le; unfold maxLogMem at this; omega

/-- Every instance's frame is in the allocation. -/
theorem honest_within {I : Inst} (hI : I ∈ honestInsts P fs H hdr T) (h0 : 0 < fs I.t.name) :
    I.fp + fs I.t.name ≤ T.total fs := by
  have := insts_within T 0 hdr I hI (I.fp + fs I.t.name - 1) (Or.inl ⟨by omega, by omega⟩)
  omega

/-- **Write-once consistency** of the honest memory's writes. -/
theorem Honest.consistent (h : Honest P fs H C hdr T rd args rets) :
    Consistent (frameWrites C (honestInsts P fs H hdr T) ++ T.eqns P) :=
  (frameWrites_consistent (insts_pairwise T 0 hdr) h.cells fun I hI => by
    have := honest_within hI (by have := h.cells.two_le I hI; omega)
    have := h.size
    omega).append h.eqns h.cross

/-- **Every frame cell reads back**: header and cells, at `fp · g^o`. -/
theorem Honest.read_cell (h : Honest P fs H C hdr T rd args rets) {I : Inst}
    (hI : I ∈ honestInsts P fs H hdr T) {q : ℕ × E} (hq : q ∈ I.cells C) :
    (honest P fs H C hdr T).read (gpow I.fp * gpow q.1) = some q.2 := by
  have hlt := h.cells.cell_lt hI hq
  have hw := honest_within hI (by omega)
  have hle := le_two_pow_logMem (T.total fs)
  rw [← pow_add]
  exact image_read h.lt_64 h.consistent (q := (gpow (I.fp + q.1), q.2))
    (List.mem_append_left _ (List.mem_flatMap.mpr ⟨I, hI, List.mem_map.mpr ⟨q, hq, rfl⟩⟩))
    ⟨⟨I.fp + q.1, by omega⟩, rfl⟩

/-- The header: `fp[0]`, `fp[1]`. -/
theorem Honest.read_hdr (h : Honest P fs H C hdr T rd args rets) {I : Inst}
    (hI : I ∈ honestInsts P fs H hdr T) :
    (honest P fs H C hdr T).read (gpow I.fp * gpow 0) = some I.hdr.1 ∧
      (honest P fs H C hdr T).read (gpow I.fp * gpow 1) = some I.hdr.2 :=
  ⟨h.read_cell hI (q := (0, I.hdr.1)) List.mem_cons_self,
    h.read_cell hI (q := (1, I.hdr.2)) (List.mem_cons_of_mem _ List.mem_cons_self)⟩

/-- A cell of `C`. -/
theorem Honest.read_C (h : Honest P fs H C hdr T rd args rets) {I : Inst}
    (hI : I ∈ honestInsts P fs H hdr T) {o : ℕ} {w : E} (hq : (o, w) ∈ C I) :
    (honest P fs H C hdr T).read (gpow I.fp * gpow o) = some w :=
  h.read_cell hI (q := (o, w)) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))

/-- Every memory equation reads back. -/
theorem Honest.read_eqn (h : Honest P fs H C hdr T rd args rets) {q : Write}
    (hq : q ∈ T.eqns P) : (honest P fs H C hdr T).read q.1 = some q.2 :=
  image_read h.lt_64 h.consistent (List.mem_append_right _ hq) (h.addr q hq)

/-- **The evaluation is valid on the honest memory.** -/
theorem Honest.valid_image (h : Honest P fs H C hdr T rd args rets) :
    T.Valid P (honest P fs H C hdr T).read args rets :=
  h.valid.transfer T fun _ hq => h.read_eqn hq

/-- **Every instance is valid on the honest memory**, or a phantom. -/
theorem Honest.inst_good (h : Honest P fs H C hdr T rd args rets) {I : Inst}
    (hI : I ∈ honestInsts P fs H hdr T) : I.Good P (honest P fs H C hdr T).read :=
  insts_good T 0 hdr h.valid_image I hI

/-- `main`'s instance: the root, at frame `g^0`, with the header `hdr`. -/
theorem root_inst : ∃ I ∈ honestInsts P fs H hdr T, I.t = T ∧ I.fp = 0 ∧ I.hdr = hdr := by
  obtain ⟨I, rest, he, ht, hfp, hh⟩ := head_insts (fs := fs) (H := H) T 0 hdr
  exact ⟨I, by rw [honestInsts, he]; exact List.mem_cons_self, ht, hfp, hh⟩

/-- **The public boundary**: with the public input as `main`'s header, the honest memory holds
it in words `0`, `1`, and has between `2^16` and `2^32` words. -/
theorem Honest.publicBoundary {input : PublicInput} {prog : Semantics.Program}
    (h : Honest P fs H C (input.word0, input.word1) T rd args rets) :
    HasPublicBoundary input
      (⟨logMem (T.total fs), honest P fs H C (input.word0, input.word1) T, 0⟩ : Trace prog) := by
  obtain ⟨I, hI, -, hfp, hh⟩ := root_inst (fs := fs) (H := H) (hdr := (input.word0, input.word1))
    (T := T)
  obtain ⟨h0, h1⟩ := h.read_hdr hI
  rw [hfp, hh, gpow, pow_zero, one_mul] at h0 h1
  exact ⟨minLogMem_le_logMem _, h.logMem_le, h0, h1⟩

/-- A word nothing writes reads `0`, as the Rust runner reads an unwritten cell. -/
theorem Honest.read_unwritten (h : Honest P fs H C hdr T rd args rets)
    (i : Fin (2 ^ logMem (T.total fs)))
    (hn : ∀ q ∈ frameWrites C (honestInsts P fs H hdr T) ++ T.eqns P, q.1 ≠ gpow i) :
    (honest P fs H C hdr T).read (gpow i) = some 0 :=
  image_read_zero h.lt_64 i hn

/-- **The callees of an instance**: its `i`-th callee is an instance at its `i`-th callee frame,
with the header `H I i`. -/
theorem honest_kid {I : Inst} (hI : I ∈ honestInsts P fs H hdr T) {i : ℕ} {k : Tree}
    (hk : I.t.kids[i]? = some k) :
    ∃ J ∈ honestInsts P fs H hdr T, J.t = k ∧ I.kidFps[i]? = some J.fp ∧ J.hdr = H I i :=
  insts_kid T 0 hdr I hI i k hk

/-- **A loop's next iteration**: a loop helper's last callee's frame is at `fp + fs f`, the frame
its code addresses as `fp · g^S`. -/
theorem honest_kidFps_getLast? {I : Inst} (hI : I ∈ honestInsts P fs H hdr T)
    (hl : P.loop I.t.name = true) (hk : I.t.kids ≠ []) :
    I.kidFps.getLast? = some (I.fp + fs I.t.name) :=
  (insts_placed T 0 hdr I hI).kidFps_getLast? hl hk

/-- An instance's callees' frames, in call order. -/
theorem honest_kidFps {I : Inst} (hI : I ∈ honestInsts P fs H hdr T) :
    I.kidFps = kidPos fs P.loop I.fp I.t.name I.t.bufs (I.t.kids.map (Tree.total fs)) :=
  (insts_placed T 0 hdr I hI).1

/-- An instance's `HeapBuf`s: the `j`-th of `bufs[j]` words from `bufBases[j]`, in the
allocation, apart from every frame (`frameWrites_not_buf`). -/
theorem honest_bufBases {I : Inst} (hI : I ∈ honestInsts P fs H hdr T) :
    I.bufBases = bases (bufBase fs P.loop I.fp I.t.name (I.t.kids.map (Tree.total fs))) I.t.bufs :=
  (insts_placed T 0 hdr I hI).2

/-! ## Discharging the hypotheses -/

/-- A frame write is at a word of an instance's frame. -/
theorem frameWrites_addr (hok : CellsOk fs C (honestInsts P fs H hdr T)) {a : Write}
    (ha : a ∈ frameWrites C (honestInsts P fs H hdr T)) :
    ∃ I ∈ honestInsts P fs H hdr T, ∃ o < fs I.t.name, a.1 = gpow (I.fp + o) := by
  obtain ⟨I, hI, q, hq, rfl⟩ := mem_frameWrites ha
  exact ⟨I, hI, q.1, hok.cell_lt hI hq, rfl⟩

/-- **No frame write is in a `HeapBuf`**: an equation there meets no frame. -/
theorem frameWrites_not_buf (hok : CellsOk fs C (honestInsts P fs H hdr T))
    (hsize : T.total fs ≤ 2 ^ 32) {I : Inst} (hI : I ∈ honestInsts P fs H hdr T) {i : ℕ}
    (hi : I.Buf i) : ∀ a ∈ frameWrites C (honestInsts P fs H hdr T), a.1 ≠ gpow i := by
  intro a ha he
  obtain ⟨J, hJ, o, ho, hao⟩ := frameWrites_addr hok ha
  have hiw := insts_within T 0 hdr I hI i (Or.inr hi)
  have hJw := honest_within hJ (by omega)
  have hio : J.fp + o = i :=
    gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
      (hao.symm.trans he)
  have hF : J.Frame fs i := ⟨by omega, by omega⟩
  by_cases hIJ : I = J
  · subst hIJ
    exact (insts_placed T 0 hdr I hI).frame_buf hF hi
  · exact (insts_pairwise T 0 hdr).forall hI hJ hIJ i (Or.inr hi) (Or.inl hF)

/-- The equations agree with the frames when one memory holds both. -/
theorem cross_of_read {rd' : Reader}
    (hf : ∀ a ∈ frameWrites C (honestInsts P fs H hdr T), rd' a.1 = some a.2)
    (he : ∀ b ∈ T.eqns P, rd' b.1 = some b.2) :
    ∀ a ∈ frameWrites C (honestInsts P fs H hdr T), ∀ b ∈ T.eqns P, a.1 = b.1 → a.2 = b.2 :=
  fun a ha b hb hab => Option.some.inj ((hf a ha).symm.trans (hab ▸ he b hb))

/-! ## A placed tree -/

/-- **A placed instance**: its `HeapBuf` pointers are its `bufBases`, its `frameAddr`s the
addresses of their runs in its frame. -/
theorem HonestAt.nodeAt {cert : String → V → ℕ} (h : HonestAt P fs H C hdr T cert rd args rets)
    {I : Inst} (hI : I ∈ honestInsts P fs H hdr T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) :
    (allocDsts (I.t.events P)).map σ = I.bufBases.map (fun b => ofK (gpow b)) ∧
      ∀ q ∈ addrs (I.t.events P), σ q.1 = ofK (gpow (I.fp + cert f q.2)) :=
  Inst.nodeAt (insts_placedAt T 0 hdr h.placed I hI) (insts_placed T 0 hdr I hI) ht

/-- **Every equation is an instance's**: an atom's on the path of a node instance. -/
theorem honest_eqns {q : Write} (hq : q ∈ T.eqns P) :
    ∃ I ∈ honestInsts P fs H hdr T, (∃ f σ bufs kids, I.t = .node f σ bufs kids) ∧
      ∃ a, Ev.atom a ∈ I.t.events P ∧ q ∈ atomEqns I.t.val a :=
  eqns_insts T 0 hdr q hq

/-- **A memory holding the frames**: a placed tree valid on a memory holding every frame write
is `HonestAt`, its equations consistent and agreeing with the frames. -/
theorem honestAt_of_read {cert : String → V → ℕ} {M : MemImage (logMem (T.total fs))}
    (hv : T.Valid P M.read args rets) (hb : T.BufsOk P) (hp : T.Placed P fs cert 0)
    (hsize : T.total fs ≤ 2 ^ 32) (hcells : CellsOk fs C (honestInsts P fs H hdr T))
    (haddr : ∀ q ∈ T.eqns P, ∃ i : Fin (2 ^ logMem (T.total fs)), q.1 = gpow i)
    (hf : ∀ a ∈ frameWrites C (honestInsts P fs H hdr T), M.read a.1 = some a.2) :
    HonestAt P fs H C hdr T cert M.read args rets := by
  have hκ : logMem (T.total fs) < 64 := by
    have := logMem_le_maxLogMem hsize; unfold maxLogMem at this; omega
  exact ⟨⟨hv, hsize, hcells, haddr, hv.eqns_consistent hκ haddr,
    cross_of_read hf fun b hb => hv.eqns_read hκ T b hb (haddr b hb)⟩, hb, hp⟩

/-- **The equations agree with the frames** when each lies in a `HeapBuf`, is itself a frame
write, or agrees with the frames. -/
theorem cross_of_cases (hcells : CellsOk fs C (honestInsts P fs H hdr T))
    (hsize : T.total fs ≤ 2 ^ 32)
    (h : ∀ b ∈ T.eqns P, (∃ I ∈ honestInsts P fs H hdr T, ∃ i, I.Buf i ∧ b.1 = gpow i) ∨
      b ∈ frameWrites C (honestInsts P fs H hdr T) ∨
      ∀ a ∈ frameWrites C (honestInsts P fs H hdr T), a.1 = b.1 → a.2 = b.2) :
    ∀ a ∈ frameWrites C (honestInsts P fs H hdr T), ∀ b ∈ T.eqns P, a.1 = b.1 → a.2 = b.2 := by
  intro a ha b hb hab
  rcases h b hb with ⟨I, hI, i, hi, he⟩ | hb' | hb'
  · exact absurd (hab.trans he) (frameWrites_not_buf hcells hsize hI hi a ha)
  · exact frameWrites_consistent (insts_pairwise T 0 hdr) hcells (fun I hI => by
      have := honest_within hI (by have := hcells.two_le I hI; omega)
      omega) a ha b hb' hab
  · exact hb' a ha hab

/-- **A `frameAddr`'s equations are frame writes** of a placed instance whose cells hold its run
at the certificate's offsets. -/
theorem HonestAt.frameAddr_eqns {cert : String → V → ℕ}
    (h : HonestAt P fs H C hdr T cert rd args rets) {I : Inst} (hI : I ∈ honestInsts P fs H hdr T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids)
    {p r : V} {rs : List V} (he : Ev.atom (.frameAddr p (r :: rs)) ∈ I.t.events P)
    (hrun : ∀ (k : ℕ) (hk : k < (r :: rs).length), (cert f r + k, σ (r :: rs)[k]) ∈ C I) :
    ∀ q ∈ atomEqns σ (.frameAddr p (r :: rs)), q ∈ frameWrites C (honestInsts P fs H hdr T) := by
  intro q hq
  have hp := (h.nodeAt hI ht).2 (p, r) (List.mem_filterMap.mpr ⟨_, he, rfl⟩)
  obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hq
  refine List.mem_flatMap.mpr ⟨I, hI, List.mem_map.mpr ⟨(cert f r + k, σ (r :: rs)[k]),
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hrun k hk)), ?_⟩⟩
  simp only at hp ⊢
  rw [hp]
  rw [show (ofK (gpow (I.fp + cert f r))).limb 0 = gpow (I.fp + cert f r) by simp, gpow, gpow,
    gpow, ← pow_add, Nat.add_assoc]

/-! ## Certificates -/

/-- **The cells of a certificate**: each value of the frame's domain at the certificate's
offset for its function, with its word. -/
def valueCells (cert : String → V → ℕ) (dom : Inst → List V) (I : Inst) : List (ℕ × E) :=
  (dom I).map fun v => (cert I.t.name v, I.t.val v)

theorem mem_valueCells {cert : String → V → ℕ} {dom : Inst → List V} {I : Inst} {v : V}
    (hv : v ∈ dom I) : (cert I.t.name v, I.t.val v) ∈ valueCells cert dom I :=
  List.mem_map.mpr ⟨v, hv, rfl⟩

/-- A certificate's cells are `CellsOk` when its offsets are past the header and in the frame,
and values sharing a cell hold one word: injectivity on the frame's values, or the compiler's
sharing of equal values. -/
theorem cellsOk_valueCells {Is : List Inst} {cert : String → V → ℕ} {dom : Inst → List V}
    (h2 : ∀ I ∈ Is, 2 ≤ fs I.t.name)
    (hoff : ∀ I ∈ Is, ∀ v ∈ dom I, 2 ≤ cert I.t.name v ∧ cert I.t.name v < fs I.t.name)
    (hshare : ∀ I ∈ Is, ∀ v ∈ dom I, ∀ w ∈ dom I, cert I.t.name v = cert I.t.name w →
      I.t.val v = I.t.val w) :
    CellsOk fs (valueCells cert dom) Is where
  two_le := h2
  off I hI q hq := by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hq
    exact hoff I hI v hv
  agree I hI q hq q' hq' he := by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hq
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq'
    exact hshare I hI v hv w hw he

/-- Cells from two sources, agreeing where they meet. -/
theorem CellsOk.append {Is : List Inst} {C₁ C₂ : Inst → List (ℕ × E)} (h₁ : CellsOk fs C₁ Is)
    (h₂ : CellsOk fs C₂ Is)
    (hx : ∀ I ∈ Is, ∀ q ∈ C₁ I, ∀ q' ∈ C₂ I, q.1 = q'.1 → q.2 = q'.2) :
    CellsOk fs (fun I => C₁ I ++ C₂ I) Is where
  two_le := h₁.two_le
  off I hI q hq := (List.mem_append.mp hq).elim (h₁.off I hI q) (h₂.off I hI q)
  agree I hI q hq q' hq' he := by
    rcases List.mem_append.mp hq with hq | hq <;> rcases List.mem_append.mp hq' with hq' | hq'
    · exact h₁.agree I hI q hq q' hq' he
    · exact hx I hI q hq q' hq' he
    · exact (hx I hI q' hq' q hq he.symm).symm
    · exact h₂.agree I hI q hq q' hq' he

/-- **Every value reads back** at its certificate cell. -/
theorem Honest.read_value (h : Honest P fs H C hdr T rd args rets) {cert : String → V → ℕ}
    {dom : Inst → List V} (hC : ∀ I, valueCells cert dom I ⊆ C I) {I : Inst}
    (hI : I ∈ honestInsts P fs H hdr T) {v : V} (hv : v ∈ dom I) :
    (honest P fs H C hdr T).read (gpow I.fp * gpow (cert I.t.name v)) = some (I.t.val v) :=
  h.read_C hI (hC I (mem_valueCells hv))

/-! ## `main`'s jump table -/

/-- **`main`'s jump table**: the slot each `SET` of `__jump_tables` writes in `main`'s frame,
and its word. -/
def tableCells : List (ℕ × E) :=
  Data.f0.code.filterMap fun
    | .set o k0 k1 k2 => some (o, OInstr.imm k0 k1 k2)
    | _ => none

set_option maxRecDepth 100000 in
/-- The slots are `167, 168, …`, one per `SET`. -/
theorem tableCells_offsets : tableCells.map Prod.fst = List.range' 167 4478 := by
  decide +kernel

/-- The slots lie in `main`'s frame past its header, below `167 + 4478`. -/
theorem tableCells_off {q : ℕ × E} (hq : q ∈ tableCells) : 2 ≤ q.1 ∧ q.1 < 167 + 4478 := by
  have := tableCells_offsets ▸ List.mem_map_of_mem (f := Prod.fst) hq
  rw [List.mem_range'_1] at this
  omega

/-- Two slots at one offset are one slot. -/
theorem tableCells_agree {q q' : ℕ × E} (hq : q ∈ tableCells) (hq' : q' ∈ tableCells)
    (he : q.1 = q'.1) : q.2 = q'.2 := by
  have hnd : (tableCells.map Prod.fst).Nodup := tableCells_offsets ▸ List.nodup_range'
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq'
  have : i = j := by
    have hi' : i < (tableCells.map Prod.fst).length := by simpa using hi
    have hj' : j < (tableCells.map Prod.fst).length := by simpa using hj
    exact (List.Nodup.getElem_inj_iff hnd (hi := hi') (hj := hj')).mp (by simpa using he)
  subst this
  rfl

end Honest

end
end LeanVM.Guest.Memory
