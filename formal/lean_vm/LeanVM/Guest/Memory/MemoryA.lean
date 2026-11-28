/-
  LeanVM.Guest.Memory.MemoryA

  The honest memory on the aligned allocator (`Memory/AllocA.lean`): `Memory.lean`'s honest memory
  with every instance where Hotwire's executor puts it.
-/

module

public import LeanVM.Guest.Memory
public import LeanVM.Guest.Memory.PlacedA

/-!
# The honest memory, aligned

`honestA P fs al H C hdr T`: `Memory.lean`'s `honest`, the tree placed by the aligned allocator
(`Tree.instsA`, `al` the frames allocated aligned) from `main`'s frame at word `0`, on
`2^logMem` words for the words it uses (`Tree.wordsA`: to its end, the padding of its aligned
allocations included). `HonestA`, `HonestAtA` and their conclusions are `Honest`'s and
`HonestAt`'s, word for word.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-! ## Validity of the instances -/

section Valid

variable {P : Core.Program} {rd : Reader} {fs : String → ℕ} {lp al : String → Bool}
  {H : Inst → ℕ → E × E}

mutual
/-- Every instance of a valid tree is valid or a phantom. -/
theorem instsA_good : ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E) {args rets : List E},
    t.Valid P rd args rets → ∀ I ∈ t.instsA fs lp al H p hdr, I.Good P rd
  | .node f σ bufs kids, p, hdr, args, rets, hv, I, hI => by
      rw [instsA_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact Or.inl ⟨args, rets, hv⟩
      · obtain ⟨_, _, _, es, _, _, _, _, hk⟩ := hv
        exact instsKidsA_good kids σ (calls es) _ 0 _ hk I hI
  | .phantom .., _, _, _, _, hv, _, _ => hv.elim

/-- `instsA_good` for the callees. -/
theorem instsKidsA_good : ∀ (ks : List Tree) (σ : Val) (cs : List Call) (I : Inst) (j : ℕ)
    (ps : List (ℕ × ℕ)), Tree.KidsValid P rd σ cs ks →
      ∀ J ∈ Tree.instsKidsA fs lp al H I j ps ks, J.Good P rd
  | [], _, _, _, _, _, _, J, hJ => by rw [instsKidsA_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, _, _, _, _, [], _, J, hJ => by
      rw [instsKidsA_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, σ, c :: cs, I, j, p :: ps, ⟨_, hc, hks⟩, J, hJ => by
      rw [instsKidsA_cons, List.mem_append] at hJ
      rcases hJ with hJ | hJ
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hc
          exact instsA_good k _ _ hc J hJ
        · rw [ite_eq_right ht] at hc
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
          rw [instsA_phantom, List.mem_singleton] at hJ
          exact Or.inr ⟨f, σ', by rw [hJ]⟩
      · exact instsKidsA_good ks σ cs I (j + 1) ps hks J hJ
  | _ :: _, _, [], _, _, _ :: _, h, _, _ => h.elim
end

end Valid

/-! ## The honest memory -/

section HonestA

variable (P : Core.Program) (fs : String → ℕ) (al : String → Bool) (H : Inst → ℕ → E × E) (C : Inst → List (ℕ × E))
  (hdr : E × E) (T : Tree)

/-- The placed call instances, `main` at word `0`. -/
def honestInstsA : List Inst := T.instsA fs P.loop al H (0, T.block fs P.loop) hdr

/-- **The honest memory**: the frames' writes and the paths' equations, on `2^logMem` words for
the words allocated. -/
noncomputable def honestA : MemoryImage (logMem (T.wordsA fs P.loop al)) :=
  image (logMem (T.wordsA fs P.loop al)) (frameWrites C (honestInstsA P fs al H hdr T) ++ T.eqns P)

/-- What the honest memory needs. -/
structure HonestA (rd : Reader) (args rets : List E) : Prop where
  /-- The evaluation, on some reader. -/
  valid : T.Valid P rd args rets
  /-- At most `2^30` words are allocated. -/
  size : T.wordsA fs P.loop al ≤ 2 ^ 30
  /-- The cells fit their frames and agree. -/
  cells : CellsOk fs C (honestInstsA P fs al H hdr T)
  /-- The equations name addresses of the memory. -/
  addr : ∀ q ∈ T.eqns P, ∃ i : Fin (2 ^ logMem (T.wordsA fs P.loop al)), q.1 = addressOfIndex i
  /-- The equations agree among themselves. -/
  eqns : Consistent (T.eqns P)
  /-- The equations agree with the frames where they meet. -/
  cross : ∀ a ∈ frameWrites C (honestInstsA P fs al H hdr T), ∀ b ∈ T.eqns P, a.1 = b.1 → a.2 = b.2

/-- What the honest memory of a placed tree needs: `Honest`, every `HeapBuf` that of its path,
and the tree placed from `main`'s frame at word `0` (`Tree.Placed`, the certificate `cert` placing
the `frameAddr`s), so that every `HeapBuf` pointer is its instance's base and every `frameAddr`
the address of its run (`HonestAtA.nodeAt`). -/
structure HonestAtA (cert : String → V → ℕ) (rd : Reader) (args rets : List E) : Prop
    extends HonestA P fs al H C hdr T rd args rets where
  /-- The `HeapBuf`s are those of the paths. -/
  bufsOk : T.BufsOk P
  /-- The tree is placed from word `0`. -/
  placed : T.PlacedA P fs al cert (0, T.block fs P.loop)

variable {P fs al H C hdr T} {rd : Reader} {args rets : List E}

theorem HonestA.logMem_le (h : HonestA P fs al H C hdr T rd args rets) :
    logMem (T.wordsA fs P.loop al) ≤ maxLogMem :=
  logMem_le_maxLogMem h.size

theorem HonestA.lt_64 (h : HonestA P fs al H C hdr T rd args rets) : logMem (T.wordsA fs P.loop al) < 64 := by
  have := h.logMem_le; unfold maxLogMem at this; omega

/-- Every word an instance owns is in the allocation. -/
theorem honestA_owns {I : Inst} (hI : I ∈ honestInstsA P fs al H hdr T) {i : ℕ} (hi : I.Owns fs i) :
    i < T.wordsA fs P.loop al := by
  have h1 := instsA_within T _ hdr (Nat.zero_add _).le I hI i hi
  have := le_endA (fs := fs) (lp := P.loop) (al := al) T (T.block fs P.loop)
  unfold RegA at h1
  unfold Tree.wordsA
  simp only at h1
  omega

/-- Every instance's frame is in the allocation. -/
theorem honestA_within {I : Inst} (hI : I ∈ honestInstsA P fs al H hdr T) (h0 : 0 < I.t.fsz fs) :
    I.fp + I.t.fsz fs ≤ T.wordsA fs P.loop al := by
  have := honestA_owns hI (i := I.fp + I.t.fsz fs - 1) (Or.inl ⟨by omega, by omega⟩)
  omega

theorem fszA_of_node {t : Tree} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : t = .node f σ bufs kids) : t.fsz fs = fs t.name := by
  subst ht; rfl

/-- A running instance's frame is in the allocation. -/
theorem honestA_within_node {I : Inst} (hI : I ∈ honestInstsA P fs al H hdr T) {f : String} {σ : Val}
    {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) (h0 : 0 < I.t.fsz fs) :
    I.fp + fs I.t.name ≤ T.wordsA fs P.loop al := by
  rw [← fszA_of_node (fs := fs) ht]; exact honestA_within hI h0

/-- **Write-once consistency** of the honest memory's writes. -/
theorem HonestA.consistent (h : HonestA P fs al H C hdr T rd args rets) :
    Consistent (frameWrites C (honestInstsA P fs al H hdr T) ++ T.eqns P) :=
  (frameWrites_consistent (instsA_pairwise T _ hdr (Nat.zero_add _).le) h.cells fun I hI => by
    have := honestA_within hI (by have := h.cells.two_le I hI; omega)
    have := h.size
    omega).append h.eqns h.cross

/-- **Every frame cell reads back**: header and cells, at `fp · g^o`. -/
theorem HonestA.read_cell (h : HonestA P fs al H C hdr T rd args rets) {I : Inst}
    (hI : I ∈ honestInstsA P fs al H hdr T) {q : ℕ × E} (hq : q ∈ I.cells C) :
    (honestA P fs al H C hdr T).read (addressOfIndex I.fp * addressOfIndex q.1) = some q.2 := by
  have hlt := h.cells.cell_lt hI hq
  have hw := honestA_within hI (by omega)
  have hle := le_two_pow_logMem (T.wordsA fs P.loop al)
  rw [← pow_add]
  exact image_read h.lt_64 h.consistent (q := (addressOfIndex (I.fp + q.1), q.2))
    (List.mem_append_left _ (List.mem_flatMap.mpr ⟨I, hI, List.mem_map.mpr ⟨q, hq, rfl⟩⟩))
    ⟨⟨I.fp + q.1, by omega⟩, rfl⟩

/-- The header: `fp[0]`, `fp[1]`. -/
theorem HonestA.read_hdr (h : HonestA P fs al H C hdr T rd args rets) {I : Inst}
    (hI : I ∈ honestInstsA P fs al H hdr T) :
    (honestA P fs al H C hdr T).read (addressOfIndex I.fp * addressOfIndex 0) = some I.hdr.1 ∧
      (honestA P fs al H C hdr T).read (addressOfIndex I.fp * addressOfIndex 1) = some I.hdr.2 :=
  ⟨h.read_cell hI (q := (0, I.hdr.1)) List.mem_cons_self,
    h.read_cell hI (q := (1, I.hdr.2)) (List.mem_cons_of_mem _ List.mem_cons_self)⟩

/-- A cell of `C`. -/
theorem HonestA.read_C (h : HonestA P fs al H C hdr T rd args rets) {I : Inst}
    (hI : I ∈ honestInstsA P fs al H hdr T) {o : ℕ} {w : E} (hq : (o, w) ∈ C I) :
    (honestA P fs al H C hdr T).read (addressOfIndex I.fp * addressOfIndex o) = some w :=
  h.read_cell hI (q := (o, w)) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))

/-- Every memory equation reads back. -/
theorem HonestA.read_eqn (h : HonestA P fs al H C hdr T rd args rets) {q : Write}
    (hq : q ∈ T.eqns P) : (honestA P fs al H C hdr T).read q.1 = some q.2 :=
  image_read h.lt_64 h.consistent (List.mem_append_right _ hq) (h.addr q hq)

/-- **The evaluation is valid on the honest memory.** -/
theorem HonestA.valid_image (h : HonestA P fs al H C hdr T rd args rets) :
    T.Valid P (honestA P fs al H C hdr T).read args rets :=
  h.valid.transfer T fun _ hq => h.read_eqn hq

/-- **Every instance is valid on the honest memory**, or a phantom. -/
theorem HonestA.inst_good (h : HonestA P fs al H C hdr T rd args rets) {I : Inst}
    (hI : I ∈ honestInstsA P fs al H hdr T) : I.Good P (honestA P fs al H C hdr T).read :=
  instsA_good T _ hdr h.valid_image I hI

/-- `main`'s instance: the root, at frame `g^0`, with the header `hdr`. -/
theorem rootA_inst : ∃ I ∈ honestInstsA P fs al H hdr T, I.t = T ∧ I.fp = 0 ∧ I.hdr = hdr := by
  obtain ⟨I, rest, he, ht, hfp, -, hh⟩ :=
    head_instsA (fs := fs) (lp := P.loop) (H := H) T (0, T.block fs P.loop) hdr
  exact ⟨I, by rw [honestInstsA, he]; exact List.mem_cons_self, ht, hfp, hh⟩

/-- **The public boundary**: with the public input as `main`'s header, the honest memory holds
it in words `0`, `1`, and has between `2^16` and `2^32` words. -/
theorem HonestA.publicBoundary {input : PublicInput} {prog : Semantics.LeanIsaProgram}
    (h : HonestA P fs al H C (input.word0, input.word1) T rd args rets) :
    HoldsPublicInput input
      (⟨logMem (T.wordsA fs P.loop al), honestA P fs al H C (input.word0, input.word1) T, 0⟩ : Execution prog) := by
  obtain ⟨I, hI, -, hfp, hh⟩ := rootA_inst (fs := fs) (H := H) (hdr := (input.word0, input.word1))
    (T := T)
  obtain ⟨h0, h1⟩ := h.read_hdr hI
  rw [hfp, hh, addressOfIndex, pow_zero, one_mul] at h0 h1
  exact ⟨minLogMem_le_logMem _, h.logMem_le, h0, h1⟩

/-- A word nothing writes reads `0`, as the Rust runner reads an unwritten cell. -/
theorem HonestA.read_unwritten (h : HonestA P fs al H C hdr T rd args rets)
    (i : Fin (2 ^ logMem (T.wordsA fs P.loop al)))
    (hn : ∀ q ∈ frameWrites C (honestInstsA P fs al H hdr T) ++ T.eqns P, q.1 ≠ addressOfIndex i) :
    (honestA P fs al H C hdr T).read (addressOfIndex i) = some 0 :=
  image_read_zero h.lt_64 i hn

/-- **The callees of an instance**: its `i`-th callee is an instance at its `i`-th callee frame,
with the header `H I i`. -/
theorem honestA_kid {I : Inst} (hI : I ∈ honestInstsA P fs al H hdr T) {i : ℕ} {k : Tree}
    (hk : I.t.kids[i]? = some k) :
    ∃ J ∈ honestInstsA P fs al H hdr T, J.t = k ∧ I.kidFps[i]? = some J.fp ∧ J.hdr = H I i :=
  instsA_kid T _ hdr I hI i k hk

/-- **A loop's next iteration**: a loop helper's last callee's frame is at `fp + fs f`, the frame
its code addresses as `fp · g^S`. -/
theorem honestA_kidFps_getLast? {I : Inst} (hI : I ∈ honestInstsA P fs al H hdr T)
    (hl : P.loop I.t.name = true) (hk : I.t.kids ≠ []) :
    I.kidFps.getLast? = some (I.fp + fs I.t.name) :=
  (instsA_placed T _ hdr (Nat.zero_add _).le I hI).kidFps_getLast? hl hk

/-- An instance's callees' frames, in call order. -/
theorem honestA_kidFps {I : Inst} (hI : I ∈ honestInstsA P fs al H hdr T) :
    I.kidFps = (kidPosA fs P.loop al (I.fp, I.cur) I.t.name I.t.bufs I.t.kids).map Prod.fst :=
  (instsA_placed T _ hdr (Nat.zero_add _).le I hI).1

/-! ## Discharging the hypotheses -/

/-- A frame write is at a word of an instance's frame. -/
theorem frameWritesA_addr (hok : CellsOk fs C (honestInstsA P fs al H hdr T)) {a : Write}
    (ha : a ∈ frameWrites C (honestInstsA P fs al H hdr T)) :
    ∃ I ∈ honestInstsA P fs al H hdr T, ∃ o < I.t.fsz fs, a.1 = addressOfIndex (I.fp + o) := by
  obtain ⟨I, hI, q, hq, rfl⟩ := mem_frameWrites ha
  exact ⟨I, hI, q.1, hok.cell_lt hI hq, rfl⟩

/-- **No frame write is in a `HeapBuf`**: an equation there meets no frame. -/
theorem frameWritesA_not_buf (hok : CellsOk fs C (honestInstsA P fs al H hdr T))
    (hsize : T.wordsA fs P.loop al ≤ 2 ^ 30) {I : Inst} (hI : I ∈ honestInstsA P fs al H hdr T) {i : ℕ}
    (hi : I.Buf i) : ∀ a ∈ frameWrites C (honestInstsA P fs al H hdr T), a.1 ≠ addressOfIndex i := by
  intro a ha he
  obtain ⟨J, hJ, o, ho, hao⟩ := frameWritesA_addr hok ha
  have hiw := honestA_owns hI (Or.inr hi)
  have hJw := honestA_within hJ (by omega)
  have hio : J.fp + o = i :=
    gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
      (hao.symm.trans he)
  have hF : J.Frame fs i := ⟨by omega, by omega⟩
  by_cases hIJ : I = J
  · subst hIJ
    exact (instsA_placed T _ hdr (Nat.zero_add _).le I hI).frame_buf hF hi
  · exact (instsA_pairwise T _ hdr (Nat.zero_add _).le).forall hI hJ hIJ i (Or.inr hi) (Or.inl hF)

/-! ## A placed tree -/

/-- **A placed instance**: its `HeapBuf` pointers are its `bufBases`, its `frameAddr`s the
addresses of their runs in its frame. -/
theorem HonestAtA.nodeAt {cert : String → V → ℕ} (h : HonestAtA P fs al H C hdr T cert rd args rets)
    {I : Inst} (hI : I ∈ honestInstsA P fs al H hdr T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) :
    (allocDsts (I.t.events P)).map σ = I.bufBases.map (fun b => ofK (addressOfIndex b)) ∧
      ∀ q ∈ addrs (I.t.events P), σ q.1 = ofK (addressOfIndex (I.fp + cert f q.2)) :=
  Inst.nodeAtA (insts_placedAtA T _ hdr h.placed I hI) (instsA_placed T _ hdr (Nat.zero_add _).le I hI) ht

/-- **A `frameAddr`'s equations are frame writes** of a placed instance whose cells hold its run
at the certificate's offsets. -/
theorem HonestAtA.frameAddr_eqns {cert : String → V → ℕ}
    (h : HonestAtA P fs al H C hdr T cert rd args rets) {I : Inst} (hI : I ∈ honestInstsA P fs al H hdr T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids)
    {p r : V} {rs : List V} (he : Ev.atom (.frameAddr p (r :: rs)) ∈ I.t.events P)
    (hrun : ∀ (k : ℕ) (hk : k < (r :: rs).length), (cert f r + k, σ (r :: rs)[k]) ∈ C I) :
    ∀ q ∈ atomEqns σ (.frameAddr p (r :: rs)), q ∈ frameWrites C (honestInstsA P fs al H hdr T) := by
  intro q hq
  have hp := (h.nodeAt hI ht).2 (p, r) (List.mem_filterMap.mpr ⟨_, he, rfl⟩)
  obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hq
  refine List.mem_flatMap.mpr ⟨I, hI, List.mem_map.mpr ⟨(cert f r + k, σ (r :: rs)[k]),
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hrun k hk)), ?_⟩⟩
  simp only at hp ⊢
  rw [hp]
  rw [show (ofK (addressOfIndex (I.fp + cert f r))).limb 0 = addressOfIndex (I.fp + cert f r)
      by simp, addressOfIndex, addressOfIndex,
    addressOfIndex, ← pow_add, Nat.add_assoc]

end HonestA

end
end LeanVM.Guest.Memory
