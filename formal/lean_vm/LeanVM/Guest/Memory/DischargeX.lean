/-
  LeanVM.Guest.Memory.DischargeX

  The honest memory of a placed tree extended by the words its hints write to the heap, read off
  the memory it is valid on: with its heap hints in its data, the re-chosen tree is `HonestX`.
-/

module

public import LeanVM.Guest.Memory.Discharge
public import LeanVM.Guest.Memory.HonestX
public import LeanVM.Guest.Memory.HintsIn

/-!
# Discharging `HonestX`

The executor writes every heap word a hint writes; the honest memory (`honest`) holds only those
something loads. `honestX_retemp` extends it by the hints' words read off the memory `M` the
tree is valid on (`readerWrites M.read (hintWords …)`), given that every heap hint word is in the
tree's data (`Tree.HintsIn` at the root, the region empty).

A word of the data is a `HeapBuf` word, in no frame (`frameWrites_not_buf`), or a cell of a
`frameAddr` run, whose equation is the tree's and whose frame cell holds the same word
(`DischargeHyps.data_cases`). So a frame write at a hint word reads back from `M`
(`DischargeHyps.frame_read`), as every equation does, and no hint word is a temporary's cell
(`DischargeHyps.temp_not_data`): the hint words agree with the fixed words and join them in the
re-choice of the temporaries (`honestAt_retempW`), which keeps the heap hint words
(`heapHintAddrs_congr`: a hint's pointer is a use). `honestX_retempH` admits hint words in the
header too, which the memory holds as the root's frame does (`DischargeHyps.fixed_hdr`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {P : Core.Program} {fs : String → ℕ} {cert : String → V → ℕ} {H : Inst → ℕ → E × E}
  {C : Inst → List (ℕ × E)} {hdr : E × E} {T : Tree} {R : ℕ → Prop}
  {M : MemoryImage (logMem (T.total fs))} {args rets : List E}

section Proof

variable (h : DischargeHyps P fs cert H C hdr T R M args rets)
include h

/-- **A word of the tree's data** is a `HeapBuf` word, or a cell of a `frameAddr` run, whose
equation is the tree's and whose frame cell holds it. -/
theorem DischargeHyps.data_cases {i : ℕ} (hd : T.Data P fs cert (0, T.block fs P.loop) i) :
    (∃ K ∈ honestInsts P fs H hdr T, K.Buf i) ∨
      ∃ K ∈ honestInsts P fs H hdr T, ∃ g σK bK kK, K.t = .node g σK bK kK ∧
        ∃ pK r rs, Ev.atom (.frameAddr pK (r :: rs)) ∈ K.t.events P ∧
          ∃ (k : ℕ) (hk : k < (r :: rs).length), i = K.fp + (cert g r + k) ∧
            (addressOfIndex i, σK (r :: rs)[k]) ∈ T.eqns P ∧
            (addressOfIndex i, σK (r :: rs)[k]) ∈ frameWrites C (honestInsts P fs H hdr T) := by
  obtain ⟨K, hK, hb | ⟨g, σK, bufsK, kidsK, hKt, qr, hqr, h1, h2⟩⟩ := data_insts (H := H) T _ hdr i hd
  · exact Or.inl ⟨K, hK, hb⟩
  · obtain ⟨e, he, hre⟩ := List.mem_filterMap.mp hqr
    rcases e with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨pK, _ | ⟨r, rs⟩⟩ | _ | _⟩ | _ | _ | _ <;>
      simp only [Ev.run?, reduceCtorEq, Option.some.injEq] at hre
    subst hre
    simp only at h1 h2
    have hk : i - (K.fp + cert g r) < (r :: rs).length := by simp only [List.length_cons]; omega
    have hi : i = K.fp + (cert g r + (i - (K.fp + cert g r))) := by omega
    have hpl := (Inst.nodeAt (insts_placedAt T _ hdr h.placed K hK)
      (insts_placed T _ hdr (Nat.zero_add _).le K hK) hKt).2 (pK, r) (List.mem_filterMap.mpr ⟨_, he, rfl⟩)
    have hm : ((σK pK).limb 0 * addressOfIndex (i - (K.fp + cert g r)), σK (r :: rs)[i - (K.fp + cert g r)]) ∈
        atomEqns σK (.frameAddr pK (r :: rs)) := List.mem_mapIdx.mpr ⟨_, hk, rfl⟩
    have heq := eqns_of_insts (P := P) T _ hdr K hK ⟨g, σK, bufsK, kidsK, hKt⟩ _ he _ (by rw [hKt]; exact hm)
    rw [hpl, show (ofK (addressOfIndex (K.fp + cert g r))).limb 0 = addressOfIndex (K.fp + cert g r) by simp,
      show addressOfIndex (K.fp + cert g r) * addressOfIndex (i - (K.fp + cert g r)) = addressOfIndex i by
        simp only [addressOfIndex, ← pow_add]
        congr 1
        omega] at heq
    have hrun := (h.run K hK g σK bufsK kidsK hKt pK r rs he _ hk).1
    have hfw := honest_mem_frameWrites hK (q := (cert g r + (i - (K.fp + cert g r)), σK (r :: rs)[i - (K.fp + cert g r)]))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hrun))
    simp only at hfw
    rw [← Nat.add_assoc, show K.fp + cert g r + (i - (K.fp + cert g r)) = i by omega] at hfw
    exact Or.inr ⟨K, hK, g, σK, bufsK, kidsK, hKt, pK, r, rs, he, _, hk, hi, heq, hfw⟩

/-- A word of the tree's data is allocated. -/
theorem DischargeHyps.data_lt {i : ℕ} (hd : T.Data P fs cert (0, T.block fs P.loop) i) : i < T.total fs := by
  rcases h.data_cases hd with ⟨K, hK, hb⟩ | ⟨K, hK, g, σK, bK, kK, hKt, pK, r, rs, he, k, hk, rfl, -, -⟩
  · exact honest_owns hK (Or.inr hb)
  · exact h.within hK (h.cells.off K hK _ (h.run K hK g σK bK kK hKt pK r rs he k hk).1).2

/-- **A frame write at a word of the data reads back** from the memory the tree is valid on. -/
theorem DischargeHyps.frame_read {a : Write} (ha : a ∈ frameWrites C (honestInsts P fs H hdr T)) {i : ℕ}
    (hai : a.1 = addressOfIndex i) (hd : T.Data P fs cert (0, T.block fs P.loop) i) :
    M.read a.1 = some a.2 := by
  rcases h.data_cases hd with ⟨K, hK, hb⟩ | ⟨K, hK, g, σK, bK, kK, hKt, pK, r, rs, he, k, hk, -, heq, hfw⟩
  · exact absurd hai (frameWrites_not_buf h.cells h.size hK hb _ ha)
  · rw [hai, h.valid.eqns_read h.lt_64 T _ heq (h.addr _ heq), h.frames_consistent _ ha _ hfw hai]

/-- **No temporary's cell is a word of the data.** -/
theorem DischargeHyps.temp_not_data {τ : Inst × V × K} (hτ : TempsOn P fs H hdr T τ) {i : ℕ}
    (hd : T.Data P fs cert (0, T.block fs P.loop) i) : tempCell cert τ ≠ addressOfIndex i := by
  intro hx
  obtain ⟨g, σ, bufs, kids, ht, hmem, hcell, hlt, hF⟩ := h.temp_cell hτ
  rw [hcell] at hx
  have heq := h.inj hlt (h.data_lt hd) hx
  rcases h.data_cases hd with ⟨K, hK, hb⟩ | ⟨K, hK, g', σK, bK, kK, hKt, pK, r, rs, he, k, hk, hik, -, -⟩
  · rw [heq] at hF
    by_cases hKJ : K = τ.1
    · subst hKJ
      exact (insts_placed T _ hdr (Nat.zero_add _).le _ hτ.1).frame_buf hF hb
    · exact (insts_pairwise T _ hdr (Nat.zero_add _).le).forall hK hτ.1 hKJ i (Or.inr hb) (Or.inl hF)
  · have hrun := h.run K hK g' σK bK kK hKt pK r rs he k hk
    have hKlt : cert g' r + k < fs K.t.name := (h.cells.off K hK _ hrun.1).2
    obtain rfl := insts_same hτ.1 hK hF ⟨by omega, by omega⟩
    obtain ⟨rfl, -⟩ : g' = g ∧ σK = σ := by rw [ht] at hKt; cases hKt; exact ⟨rfl, rfl⟩
    exact hrun.2 τ.2.1 hmem (by omega)

/-- **Words read off the memory at words of the data agree with the fixed words.** -/
theorem DischargeHyps.fixed_reader {A : List K}
    (hA : ∀ a ∈ A, ∃ i, a = addressOfIndex i ∧ T.Data P fs cert (0, T.block fs P.loop) i) {x : K} {w w' : E}
    (hw : FixedW P fs cert H C hdr T x w) (hw' : (x, w') ∈ readerWrites M.read A) : w = w' := by
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hw'
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  suffices hr : M.read a = some w by rw [hr]; rfl
  rcases hw with ⟨I, hI, q, hq, hx, rfl, -⟩ | ⟨I, hI, ⟨f, σ, bufs, kids, ht⟩, at', he, -, hq⟩
  · obtain ⟨i, hi, hd⟩ := hA _ ha
    rw [hx]
    exact h.frame_read (honest_mem_frameWrites hI hq) (hx.symm.trans hi) hd
  · have hqT := eqns_of_insts T _ hdr I hI ⟨f, σ, bufs, kids, ht⟩ at' he _ hq
    exact h.valid.eqns_read h.lt_64 T _ hqT (h.addr _ hqT)

/-- **A header word read off the memory** agrees with the fixed words. -/
theorem DischargeHyps.fixed_hdr {i : ℕ} (hi : i < 2) {w : E}
    (hw : FixedW P fs cert H C hdr T (addressOfIndex i) w) : M.read (addressOfIndex i) = some w := by
  rcases hw with ⟨I, hI, q, hq, hx, rfl, -⟩ | ⟨I, hI, ⟨f, σ, bufs, kids, ht⟩, at', he, -, hq⟩
  · obtain ⟨I0, hI0, -, hfp0, hh0⟩ := root_inst (P := P) (fs := fs) (H := H) (hdr := hdr) (T := T)
    have hrd : (addressOfIndex (I0.fp + i), if i = 0 then hdr.1 else hdr.2) ∈
        frameWrites C (honestInsts P fs H hdr T) ∧
          M.read (addressOfIndex i) = some (if i = 0 then hdr.1 else hdr.2) := by
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · refine ⟨?_, h.hdr_read.1⟩
        have := honest_mem_frameWrites (C := C) hI0 (q := (0, I0.hdr.1)) List.mem_cons_self
        rwa [hh0] at this
      · refine ⟨?_, h.hdr_read.2⟩
        have := honest_mem_frameWrites (C := C) hI0 (q := (1, I0.hdr.2))
          (List.mem_cons_of_mem _ List.mem_cons_self)
        rwa [hh0] at this
    rw [hrd.2]
    exact congrArg some (h.frames_consistent _ hrd.1 _ (honest_mem_frameWrites hI hq)
      (by simp only; rw [hfp0, Nat.zero_add, hx]))
  · have hqT := eqns_of_insts T _ hdr I hI ⟨f, σ, bufs, kids, ht⟩ at' he _ hq
    exact h.valid.eqns_read h.lt_64 T _ hqT (h.addr _ hqT)

/-- **A word of the data or the header read off the memory** agrees with the fixed words. -/
theorem DischargeHyps.fixed_read_at {i : ℕ} (hd : T.Data P fs cert (0, T.block fs P.loop) i ∨ i < 2)
    {w : E} (hw : FixedW P fs cert H C hdr T (addressOfIndex i) w) : M.read (addressOfIndex i) = some w := by
  rcases hd with hd | hd
  · rcases hw with ⟨I, hI, q, hq, hx, rfl, -⟩ | ⟨I, hI, ⟨f, σ, bufs, kids, ht⟩, at', he, -, hq⟩
    · rw [hx]; exact h.frame_read (honest_mem_frameWrites hI hq) hx.symm hd
    · have hqT := eqns_of_insts T _ hdr I hI ⟨f, σ, bufs, kids, ht⟩ at' he _ hq
      exact h.valid.eqns_read h.lt_64 T _ hqT (h.addr _ hqT)
  · exact h.fixed_hdr hd hw

theorem DischargeHyps.two_le_total : 2 ≤ T.total fs := by
  obtain ⟨I0, hI0, hI0t, -⟩ := root_inst (P := P) (fs := fs) (H := H) (hdr := hdr) (T := T)
  have h2 := h.cells.two_le I0 hI0
  rw [hI0t] at h2
  exact h2.trans (le_total T)

/-- **No temporary's cell is a header word.** -/
theorem DischargeHyps.temp_not_hdr {τ : Inst × V × K} (hτ : TempsOn P fs H hdr T τ) {i : ℕ}
    (hi : i < 2) : tempCell cert τ ≠ addressOfIndex i := by
  intro hx
  obtain ⟨g, σ, bufs, kids, ht, hmem, hcell, hlt, -⟩ := h.temp_cell hτ
  rw [hcell] at hx
  have := h.two_le_total
  have heq := h.inj hlt (by omega) hx
  have := (h.cert_lt g τ.2.1 hmem).1
  omega

/-- **The honest memory extended by the heap hints' words, a hint writing a header word too**:
with every heap hint word in the tree's data or a header word (`Tree.HintsIn` at the root, the
region the header), the temporaries re-chosen, the tree is `HonestAt` and `HonestX` with the
hints' words read off `M`, each a word of `M`, and its heap hint words are the tree's. -/
theorem honestX_retempH (hhint : T.HintsIn P fs cert (fun i => i < 2) (0, T.block fs P.loop)) :
    ∃ ν, HonestAt P fs H C hdr (T.retemp P fs ν (0, T.block fs P.loop)) cert
        (honest P fs H C hdr (T.retemp P fs ν (0, T.block fs P.loop))).read args rets ∧
      HonestX P fs H C hdr (T.retemp P fs ν (0, T.block fs P.loop))
        (honest P fs H C hdr (T.retemp P fs ν (0, T.block fs P.loop))).read args rets
        (readerWrites M.read (hintWords P fs H hdr T)) ∧
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
  obtain ⟨ν, hν, hY⟩ := honestAt_retempW h
    (fun x w => (x, w) ∈ readerWrites M.read (hintWords P fs H hdr T))
    (fun _ _ _ hw hw' => readerWrites_consistent _ _ _ hw _ hw' rfl)
    (fun x w w' hw hw' => by
      obtain ⟨a, ha, he⟩ := List.mem_map.mp hw'
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨i, rfl, hd⟩ := hA a ha
      rw [h.fixed_read_at hd hw]; rfl)
    (fun τ hτ w hw => by
      obtain ⟨a, ha, he⟩ := List.mem_map.mp hw
      obtain ⟨i, hi, hd | hd⟩ := hA a ha
      · exact h.temp_not_data hτ hd ((congrArg Prod.fst he).symm.trans hi)
      · exact h.temp_not_hdr hτ hd ((congrArg Prod.fst he).symm.trans hi))
  have htot : (T.retemp P fs ν (0, T.block fs P.loop)).total fs = T.total fs := total_retemp T _
  refine ⟨ν, hν, HonestX.mk hν.toHonest ?_ (readerWrites_consistent _ _)
    (fun a ha b hb hab => hY a ha b.2 (by rw [hab]; exact hb)), ?_, ?_⟩
  · intro q hq
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
    obtain ⟨i, rfl, hd⟩ := hlt a ha
    have := le_two_pow_logMem (T.total fs)
    exact ⟨⟨i, by rw [htot]; omega⟩, rfl⟩
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

/-- **The honest memory extended by the heap hints' words**: with every heap hint word in the
tree's data (`Tree.HintsIn` at the root, the region empty), the temporaries re-chosen, the tree is
`HonestAt` and `HonestX` with the hints' words read off `M`, each a word of `M`, and its heap hint
words are the tree's. -/
theorem honestX_retemp (hhint : T.HintsIn P fs cert (fun _ => False) (0, T.block fs P.loop)) :
    ∃ ν, HonestAt P fs H C hdr (T.retemp P fs ν (0, T.block fs P.loop)) cert
        (honest P fs H C hdr (T.retemp P fs ν (0, T.block fs P.loop))).read args rets ∧
      HonestX P fs H C hdr (T.retemp P fs ν (0, T.block fs P.loop))
        (honest P fs H C hdr (T.retemp P fs ν (0, T.block fs P.loop))).read args rets
        (readerWrites M.read (hintWords P fs H hdr T)) ∧
      hintWords P fs H hdr (T.retemp P fs ν (0, T.block fs P.loop)) ⊆ hintWords P fs H hdr T ∧
      ∀ a ∈ hintWords P fs H hdr T, ∃ w, M.read a = some w :=
  honestX_retempH h (hintsIn_mono T _ (fun _ h => h.elim) hhint)

end Proof

end
end LeanVM.Guest.Memory
