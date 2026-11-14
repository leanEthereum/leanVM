/-
  LeanVM.Guest.Memory.DischargeE

  The honest memory extended by the heap hints' words and by the values only hints read, at
  frame cells nothing else uses: with those cells fresh, the re-chosen tree is `HonestX`.
-/

module

public import LeanVM.Guest.Memory.DischargeX

/-!
# The hint-only cells

A value only hints touch has no cell in the certificate; its hints use a cell of their own
(`ex f`: value index and cell). The executor writes it there, so the reference must hold it:
`extraWrites` writes, at each node instance of `f` and each `(i, c)` of `ex f`, the value of index
`i` at frame cell `c`. `ExtraFresh`: each such cell is past the header, in the frame, no cell of
`C` nor a temporary's, and holds one entry. Then the words miss every frame cell, `HeapBuf` word,
equation and temporary's cell of another kind (`extra_not_cell`, `extra_not_buf`,
`extra_not_eqn`, `extra_not_temp`, `extra_not_data`), so they join the heap hints' words in the
re-choice of the temporaries (`honestX_retempE`), and the extension holds each value a path names
at its cell (`extra_read`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable (P : Core.Program) (fs : String → ℕ) (cert : String → V → ℕ) (H : Inst → ℕ → E × E)
  (C : Inst → List (ℕ × E)) (hdr : E × E) (T : Tree) (ex : String → List (ℕ × ℕ))

/-- An instance's words at its function's hint-only cells: for each `(i, c)` of `ex f`, the value
of index `i` at frame cell `c`. -/
def Inst.extraW (I : Inst) : List Write :=
  match I.t with
  | .node f σ _ _ => (ex f).map fun p => (addressOfIndex (I.fp + p.2), σ ⟨[], 0, p.1⟩)
  | .phantom .. => []

/-- **The words at the hint-only cells** of the placed instances. -/
noncomputable def extraWrites : List Write := (honestInsts P fs H hdr T).flatMap (Inst.extraW ex)

/-- **The hint-only cells are fresh**: past the header and in the frame, no cell of `C` nor a
temporary's, one entry per cell. -/
structure ExtraFresh : Prop where
  cell : ∀ I ∈ honestInsts P fs H hdr T, ∀ f σ bufs kids, I.t = .node f σ bufs kids → ∀ p ∈ ex f,
    2 ≤ p.2 ∧ p.2 < fs f ∧ (∀ q ∈ C I, q.1 ≠ p.2) ∧ ∀ t ∈ P.temps f, cert f t ≠ p.2
  inj : ∀ f, ∀ p ∈ ex f, ∀ p' ∈ ex f, p.2 = p'.2 → p = p'

variable {P fs cert H C hdr T ex} {R : ℕ → Prop} {M : MemoryImage (logMem (T.total fs))} {args rets : List E}

theorem mem_extraWrites {q : Write} (hq : q ∈ extraWrites P fs H hdr T ex) :
    ∃ I ∈ honestInsts P fs H hdr T, ∃ f σ bufs kids, I.t = .node f σ bufs kids ∧ ∃ p ∈ ex f,
      q = (addressOfIndex (I.fp + p.2), σ ⟨[], 0, p.1⟩) := by
  obtain ⟨I, hI, hq⟩ := List.mem_flatMap.mp hq
  unfold Inst.extraW at hq
  split at hq
  · rename_i f σ bufs kids hIt
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact ⟨I, hI, f, σ, bufs, kids, hIt, p, hp, rfl⟩
  · cases hq

section Proof

variable (h : DischargeHyps P fs cert H C hdr T R M args rets) (hE : ExtraFresh P fs cert H C hdr T ex)
include h hE

variable {I : Inst} (hI : I ∈ honestInsts P fs H hdr T) {f : String} {σ : Val} {bufs : List ℕ}
  {kids : List Tree} (hIt : I.t = .node f σ bufs kids) {p : ℕ × ℕ} (hp : p ∈ ex f)
include hI hIt hp

/-- A hint-only cell is a word of its instance's frame. -/
theorem extra_at : I.fp + p.2 < T.total fs ∧ I.Frame fs (I.fp + p.2) := by
  obtain ⟨-, hlt, -, -⟩ := hE.cell I hI f σ bufs kids hIt p hp
  have hn : I.t.name = f := by rw [hIt]; rfl
  exact ⟨h.within hI (by rw [hn]; exact hlt), ⟨Nat.le_add_right _ _, by rw [hn]; omega⟩⟩

/-- **A hint-only cell is no other frame cell.** -/
theorem extra_not_cell {J : Inst} (hJ : J ∈ honestInsts P fs H hdr T) {q : ℕ × E} (hq : q ∈ J.cells C) :
    addressOfIndex (J.fp + q.1) ≠ addressOfIndex (I.fp + p.2) := by
  intro hx
  obtain ⟨hlt, hF⟩ := extra_at h hE hI hIt hp
  obtain ⟨h2, -, hC, -⟩ := hE.cell I hI f σ bufs kids hIt p hp
  have hqlt := h.cells.cell_lt hJ hq
  have heq := h.inj (h.within hJ hqlt) hlt hx
  have hIJ := insts_same hI hJ hF ⟨by omega, by omega⟩
  subst hIJ
  simp only [Inst.cells, List.mem_cons] at hq
  rcases hq with rfl | rfl | hq
  · simp only at heq; omega
  · simp only at heq; omega
  · exact hC q hq (by omega)

/-- **A hint-only cell is no `HeapBuf` word.** -/
theorem extra_not_buf {K : Inst} (hK : K ∈ honestInsts P fs H hdr T) {i : ℕ} (hb : K.Buf i) :
    addressOfIndex i ≠ addressOfIndex (I.fp + p.2) := by
  intro hx
  obtain ⟨hlt, hF⟩ := extra_at h hE hI hIt hp
  have hi := honest_owns (P := P) hK (Or.inr hb)
  have heq := h.inj hi hlt hx
  rw [heq] at hb
  by_cases hKI : K = I
  · subst hKI
    exact (insts_placed T _ hdr (Nat.zero_add _).le _ hK).frame_buf hF hb
  · exact (insts_pairwise T _ hdr (Nat.zero_add _).le).forall hK hI hKI _ (Or.inr hb) (Or.inl hF)

/-- **A hint-only cell is no word of an equation** of an atom but a range check. -/
theorem extra_not_eqn {K : Inst} (hK : K ∈ honestInsts P fs H hdr T) {g : String} {σK : Val} {bK : List ℕ}
    {kK : List Tree} (hKt : K.t = .node g σK bK kK) {a : Atom} (he : Ev.atom a ∈ K.t.events P)
    (hta : atomTmps a = []) {q : Write} (hq : q ∈ atomEqns σK a) : q.1 ≠ addressOfIndex (I.fp + p.2) := by
  intro hx
  rcases h.classify hK hKt he hta hq with ⟨K', hK', i, hb, hqi⟩ | ⟨i, hR, hqi⟩ |
      ⟨K', hK', g', σ', b', k', hK't, pK, r, rs, hfa, k, hk, hqi, -⟩
  · exact extra_not_buf h hE hI hIt hp hK' hb (hqi.symm.trans hx)
  · obtain ⟨hlt, hF⟩ := extra_at h hE hI hIt hp
    obtain ⟨h2, hlt', -, -⟩ := hE.cell I hI f σ bufs kids hIt p hp
    rcases h.region i hR with hi2 | hR'
    · have := h.two_le_total
      have heq := h.inj (by omega) hlt (hqi.symm.trans hx)
      omega
    · have hn : I.t.name = f := by rw [hIt]; rfl
      exact hR' I hI p.2 (by rw [hn]; exact hlt') (hqi.symm.trans hx)
  · have hrun := (h.run K' hK' g' σ' b' k' hK't pK r rs hfa k hk).1
    exact extra_not_cell h hE hI hIt hp hK' (q := (cert g' r + k, σ' (r :: rs)[k]))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hrun)) (by rw [← hx, hqi])

/-- **A hint-only cell is no temporary's cell.** -/
theorem extra_not_temp {τ : Inst × V × K} (hτ : TempsOn P fs H hdr T τ) :
    tempCell cert τ ≠ addressOfIndex (I.fp + p.2) := by
  intro hx
  obtain ⟨g, σ', bufs', kids', ht, hmem, hcell, hlt', hF'⟩ := h.temp_cell hτ
  obtain ⟨hlt, hF⟩ := extra_at h hE hI hIt hp
  rw [hcell] at hx
  have heq := h.inj hlt' hlt hx
  have hIJ := insts_same hI hτ.1 hF (by rw [← heq]; exact hF')
  rw [← hIJ, hIt] at ht
  cases ht
  rw [← hIJ] at heq
  exact (hE.cell I hI f σ bufs kids hIt p hp).2.2.2 τ.2.1 hmem (by omega)

/-- **A hint-only cell is no word of the data**, nor a header word. -/
theorem extra_not_data {i : ℕ} (hd : T.Data P fs cert (0, T.block fs P.loop) i ∨ i < 2) :
    addressOfIndex i ≠ addressOfIndex (I.fp + p.2) := by
  rcases hd with hd | hd
  · rcases h.data_cases hd with ⟨K, hK, hb⟩ | ⟨K, hK, g, σK, bK, kK, hKt, pK, r, rs, he, k, hk, rfl, -, -⟩
    · exact extra_not_buf h hE hI hIt hp hK hb
    · have hrun := (h.run K hK g σK bK kK hKt pK r rs he k hk).1
      exact extra_not_cell h hE hI hIt hp hK (q := (cert g r + k, σK (r :: rs)[k]))
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hrun))
  · intro hx
    obtain ⟨hlt, -⟩ := extra_at h hE hI hIt hp
    obtain ⟨h2, -, -, -⟩ := hE.cell I hI f σ bufs kids hIt p hp
    have := h.two_le_total
    have heq := h.inj (by omega) hlt hx
    omega

omit hI hIt hp

/-- **The words at the hint-only cells are consistent.** -/
theorem extra_consistent : Consistent (extraWrites P fs H hdr T ex) := by
  intro a ha b hb hab
  obtain ⟨I, hI, f, σ, bufs, kids, hIt, p, hp, rfl⟩ := mem_extraWrites ha
  obtain ⟨J, hJ, g, σ', bufs', kids', hJt, p', hp', rfl⟩ := mem_extraWrites hb
  obtain ⟨hlt, hF⟩ := extra_at h hE hI hIt hp
  obtain ⟨hlt', hF'⟩ := extra_at h hE hJ hJt hp'
  have heq := h.inj hlt hlt' hab
  have hIJ := insts_same hI hJ hF (by rw [heq]; exact hF')
  subst hIJ
  rw [hIt] at hJt
  cases hJt
  obtain rfl := hE.inj f p hp p' hp' (by omega)
  rfl

/-- **The honest memory extended by the heap hints' words and the hint-only cells' words**: with
every heap hint word in the tree's data or a header word and the hint-only cells fresh, the
temporaries re-chosen, the tree is `HonestAt` and `HonestX` with the hints' words read off `M` and
the hint-only cells' words, each hint word a word of `M`, and its heap hint words the tree's. -/
theorem honestX_retempE (hhint : T.HintsIn P fs cert (fun i => i < 2) (0, T.block fs P.loop)) :
    ∃ ν, HonestAt P fs H C hdr (T.retemp P fs ν (0, T.block fs P.loop)) cert
        (honest P fs H C hdr (T.retemp P fs ν (0, T.block fs P.loop))).read args rets ∧
      HonestX P fs H C hdr (T.retemp P fs ν (0, T.block fs P.loop))
        (honest P fs H C hdr (T.retemp P fs ν (0, T.block fs P.loop))).read args rets
        (readerWrites M.read (hintWords P fs H hdr T) ++ extraWrites P fs H hdr T ex) ∧
      hintWords P fs H hdr (T.retemp P fs ν (0, T.block fs P.loop)) ⊆ hintWords P fs H hdr T ∧
      ∀ a ∈ hintWords P fs H hdr T, ∃ w, M.read a = some w := by
  have hA : ∀ a ∈ hintWords P fs H hdr T, ∃ i, a = addressOfIndex i ∧
      (T.Data P fs cert (0, T.block fs P.loop) i ∨ i < 2) := by
    intro a ha
    obtain ⟨I, hI, haI⟩ := List.mem_flatMap.mp ha
    exact hints_insts T _ _ hdr hhint I hI a haI
  have hlt : ∀ a ∈ hintWords P fs H hdr T, ∃ i, a = addressOfIndex i ∧ i < T.total fs := by
    intro a ha
    obtain ⟨i, rfl, hd | hd⟩ := hA a ha
    · exact ⟨i, rfl, h.data_lt hd⟩
    · have := h.two_le_total; exact ⟨i, rfl, by omega⟩
  -- the reader's words miss the hint-only cells
  have hRE : ∀ a ∈ readerWrites M.read (hintWords P fs H hdr T), ∀ b ∈ extraWrites P fs H hdr T ex,
      a.1 ≠ b.1 := by
    intro a ha b hb hab
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    obtain ⟨I, hI, f, σ, bufs, kids, hIt, p, hp, rfl⟩ := mem_extraWrites hb
    obtain ⟨i, rfl, hd⟩ := hA c hc
    exact extra_not_data h hE hI hIt hp hd hab
  have hcons : Consistent (readerWrites M.read (hintWords P fs H hdr T) ++ extraWrites P fs H hdr T ex) :=
    (readerWrites_consistent _ _).append (extra_consistent h hE) fun a ha b hb hab ↦ absurd hab (hRE a ha b hb)
  obtain ⟨ν, hν, hY⟩ := honestAt_retempW h
    (fun x w => (x, w) ∈ readerWrites M.read (hintWords P fs H hdr T) ++ extraWrites P fs H hdr T ex)
    (fun _ _ _ hw hw' => hcons _ hw _ hw' rfl)
    (fun x w w' hw hw' => by
      rcases List.mem_append.mp hw' with hw' | hw'
      · obtain ⟨a, ha, he⟩ := List.mem_map.mp hw'
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨i, rfl, hd⟩ := hA a ha
        rw [h.fixed_read_at hd hw]; rfl
      · obtain ⟨I, hI, f, σ, bufs, kids, hIt, p, hp, he⟩ := mem_extraWrites hw'
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, -⟩ := he
        rcases hw with ⟨J, hJ, q, hq, hx, -, -⟩ | ⟨J, hJ, ⟨g, σJ, bJ, kJ, hJt⟩, a, hea, hta, hq⟩
        · exact absurd hx.symm (extra_not_cell h hE hI hIt hp hJ hq)
        · rw [hJt] at hq
          exact absurd rfl (extra_not_eqn h hE hI hIt hp hJ hJt hea hta (q := (addressOfIndex (I.fp + p.2), w)) hq))
    (fun τ hτ w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨a, ha, he⟩ := List.mem_map.mp hw
        obtain ⟨i, hi, hd | hd⟩ := hA a ha
        · exact h.temp_not_data hτ hd ((congrArg Prod.fst he).symm.trans hi)
        · exact h.temp_not_hdr hτ hd ((congrArg Prod.fst he).symm.trans hi)
      · obtain ⟨I, hI, f, σ, bufs, kids, hIt, p, hp, he⟩ := mem_extraWrites hw
        exact extra_not_temp h hE hI hIt hp hτ (congrArg Prod.fst he))
  have htot : (T.retemp P fs ν (0, T.block fs P.loop)).total fs = T.total fs := total_retemp T _
  refine ⟨ν, hν, HonestX.mk hν.toHonest ?_ hcons (fun a ha b hb hab => hY a ha b.2 (by rw [hab]; exact hb)), ?_, ?_⟩
  · intro q hq
    have hle := le_two_pow_logMem (T.total fs)
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
      obtain ⟨i, rfl, hd⟩ := hlt a ha
      exact ⟨⟨i, by rw [htot]; omega⟩, rfl⟩
    · obtain ⟨I, hI, f, σ, bufs, kids, hIt, p, hp, rfl⟩ := mem_extraWrites hq
      obtain ⟨hl, -⟩ := extra_at h hE hI hIt hp
      exact ⟨⟨I.fp + p.2, by rw [htot]; omega⟩, rfl⟩
  · intro a ha
    obtain ⟨I', hI', haI⟩ := List.mem_flatMap.mp ha
    obtain ⟨I, hI, -, -, hteq⟩ := insts_retemp (H := H) T _ hdr hdr I' (by rwa [honestInsts_retemp] at hI')
    refine List.mem_flatMap.mpr ⟨I, hI, ?_⟩
    unfold Inst.hintAddrs at haI ⊢
    cases hIt : I.t with
    | phantom f σ =>
      rw [hIt, retemp_phantom] at hteq
      rw [hteq] at haI
      exact (List.not_mem_nil haI).elim
    | node f σ bufs kids =>
      obtain ⟨fn, es, vs, hf, hw, hev⟩ := h.path hI hIt
      have hag := evAgree_retemp (ν := ν) h.fresh hf (fp := I.fp) hw
      rw [hIt, retemp_node] at hteq
      rw [hteq] at haI
      simp only at haI ⊢
      rw [events_retemp h.fresh (bufs' := bufs) (ks' := kids), ← hIt, hev, heapHintAddrs_congr hag] at haI
      rw [← hIt, hev]
      exact haI
  · intro a ha
    obtain ⟨i, rfl, hd⟩ := hlt a ha
    have := le_two_pow_logMem (T.total fs)
    exact ⟨_, MemoryImage.read_gpow h.lt_64 M ⟨i, by omega⟩⟩

/-- **The extension holds each hint-only value at its cell**, at each node instance of the re-chosen
tree, for a value its path names (each such value being the one of its index). -/
theorem extra_read {ν : ℕ → String → Val → V → E} {rd : Reader} {Xr : List Write}
    (hX : HonestX P fs H C hdr (T.retemp P fs ν (0, T.block fs P.loop)) rd args rets
      (Xr ++ extraWrites P fs H hdr T ex))
    (hn : ∀ f σ bufs kids, ∀ v ∈ ((Tree.node f σ bufs kids).events P).flatMap Ev.uses, ∀ c,
      (ex f).lookup v.idx = some c → v = ⟨[], 0, v.idx⟩) :
    ∀ I' ∈ honestInsts P fs H hdr (T.retemp P fs ν (0, T.block fs P.loop)), ∀ f σ' bufs kids,
      I'.t = .node f σ' bufs kids → ∀ v ∈ (I'.t.events P).flatMap Ev.uses, ∀ c,
        (ex f).lookup v.idx = some c → I'.fp + c < 2 ^ 30 ∧
          (honestX P fs H C hdr (T.retemp P fs ν (0, T.block fs P.loop)) (Xr ++ extraWrites P fs H hdr T ex)).read
            (addressOfIndex (I'.fp + c)) = some (σ' v) := by
  intro I' hI' f σ' bufs kids hI't v hv c hc
  obtain ⟨I, hI, hfp, -, hteq⟩ := insts_retemp (H := H) T _ hdr hdr I' (by rwa [honestInsts_retemp] at hI')
  rw [hI't] at hteq
  obtain ⟨σ, kids0, hIt, rfl⟩ := node_of_retemp hteq.symm
  obtain ⟨fn, es, vs, hf, hw, hev⟩ := h.path hI hIt
  have hag := evAgree_retemp (ν := ν) h.fresh hf (fp := I.fp) hw
  have hv' : v ∈ (I.t.events P).flatMap Ev.uses := by
    rw [hI't, events_retemp h.fresh (bufs' := bufs) (ks' := kids0), ← hIt] at hv
    exact hv
  have hvn := hn f σ bufs kids0 v (by rw [← hIt]; exact hv') c hc
  have hpc : (v.idx, c) ∈ ex f := by
    obtain ⟨l₁, l₂, he, -⟩ := List.lookup_eq_some_iff.mp hc
    rw [he]
    exact List.mem_append_right _ List.mem_cons_self
  have hmem : (addressOfIndex (I.fp + c), σ ⟨[], 0, v.idx⟩) ∈ extraWrites P fs H hdr T ex :=
    List.mem_flatMap.mpr ⟨I, hI, by
      unfold Inst.extraW
      rw [hIt]
      exact List.mem_map.mpr ⟨(v.idx, c), hpc, rfl⟩⟩
  have hr := hX.read_X (List.mem_append_right _ hmem)
  rw [hev] at hv'
  obtain ⟨e, he, hve⟩ := List.mem_flatMap.mp hv'
  have hlt := (extra_at h hE hI hIt hpc).1
  have := h.size
  refine ⟨by simp only at hlt; omega, ?_⟩
  rw [← hfp, hr, ← hvn, hag e he v hve]

end Proof

end
end LeanVM.Guest.Memory
