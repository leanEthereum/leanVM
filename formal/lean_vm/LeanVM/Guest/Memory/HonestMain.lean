/-
  LeanVM.Guest.Memory.HonestMain

  From `main`'s uniform placed relation at `0` to an honest tree (`HonestAt`): the memory image of
  a consistent layout and the header, the certificate's facts the discharge takes (`KFacts`), the
  discharge's address field, and `honestAt_retemp`. Ported from leanVM `3f7dc219`'s
  `B1/Main/HonestImage.lean` and `B1/Main/HonestPiece.lean`.
-/

module

public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.Memory.Discharge

/-!
# The honest tree of `main`

`LConsistent L`: two entries of `L` covering one word give it the same value. `imageOf κ L hdr`
holds `hdr` at words `0`, `1` and each entry's words elsewhere (`memL_imageOf`, `imageOf_hdr`),
when the entries lie in `[2, 2^κ)`.

`KFacts`: the certificate's facts the discharge takes of a tree (the checker's). `dischargeAddr`:
every equation of a tree valid on a memory image and placed at `0` names a word of it, its loads
and range checks by validity, its `frameAddr` runs by their certificate cells in their frames.
`honest_of_relAtIn`: if `main` holds by a tree placed at `0` of `N ≤ 2^30` words on every memory
holding a consistent layout `L` in `[2, N)` and the header, an honest tree of `N` words exists.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **A consistent layout**: two entries covering one word give it the same value. -/
def LConsistent (L : Layout) : Prop :=
  ∀ q ∈ L, ∀ q' ∈ L, ∀ i, q.1 ≤ i → i < q.1 + q.2.length → q'.1 ≤ i → i < q'.1 + q'.2.length →
    q.2.getD (i - q.1) 0 = q'.2.getD (i - q'.1) 0

theorem pairwise_mem_ne {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b
  | [], _, a, ha, _, _, _ => by simp at ha
  | x :: l, h, a, ha, b, hb, hab => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
    · exact absurd (h1.trans h2.symm) hab
    · rw [h1]; exact h.1 b h2
    · rw [h2]; exact hs _ _ (h.1 a h1)
    · exact pairwise_mem_ne hs h.2 a h1 b h2 hab

/-- **Pairwise disjoint entries are consistent.** -/
theorem lConsistent_of_pairwise {L : Layout}
    (h : L.Pairwise fun q q' => q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1) : LConsistent L := by
  intro q hq q' hq' i h1 h2 h3 h4
  by_cases he : q = q'
  · subst he; rfl
  · have := pairwise_mem_ne (fun a b hab => hab.symm) h q hq q' hq' he
    omega

open Classical in
/-- **The image of a layout**: `hdr` at words `0` and `1`, an entry's word where one covers. -/
noncomputable def imageOf (κ : ℕ) (L : Layout) (hdr : E × E) : MemoryImage κ := fun i =>
  if (i : ℕ) = 0 then hdr.1 else if (i : ℕ) = 1 then hdr.2 else
    match L.find? (fun q => decide (q.1 ≤ (i : ℕ) ∧ (i : ℕ) < q.1 + q.2.length)) with
    | some q => q.2.getD ((i : ℕ) - q.1) 0
    | none => 0

theorem imageOf_hdr {κ : ℕ} (hκ : κ < 64) (h1 : 1 ≤ κ) (L : Layout) (hdr : E × E) :
    (imageOf κ L hdr).read (addressOfIndex 0) = some hdr.1 ∧ (imageOf κ L hdr).read (addressOfIndex 1) = some hdr.2 := by
  have h2 : 1 < 2 ^ κ := Nat.one_lt_two_pow (by omega)
  refine ⟨?_, ?_⟩
  · have := MemoryImage.read_gpow hκ (imageOf κ L hdr) ⟨0, by omega⟩
    simpa [imageOf] using this
  · have := MemoryImage.read_gpow hκ (imageOf κ L hdr) ⟨1, h2⟩
    simpa [imageOf] using this

theorem memL_imageOf {κ : ℕ} (hκ : κ < 64) {L : Layout} (hc : LConsistent L)
    (hin : ∀ q ∈ L, 2 ≤ q.1 ∧ q.1 + q.2.length ≤ 2 ^ κ) (hdr : E × E) :
    MemL (imageOf κ L hdr).read L := by
  intro q hq k hk
  obtain ⟨h2, hle⟩ := hin q hq
  refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
  rw [addr_ofK]
  have hi : q.1 + k < 2 ^ κ := by omega
  rw [MemoryImage.read_gpow hκ (imageOf κ L hdr) ⟨q.1 + k, hi⟩]
  congr 1
  simp only [imageOf, show q.1 + k ≠ 0 by omega, show q.1 + k ≠ 1 by omega, ↓reduceIte]
  have hex : (L.find? fun q' => decide (q'.1 ≤ q.1 + k ∧ q.1 + k < q'.1 + q'.2.length)).isSome := by
    rw [List.find?_isSome]
    exact ⟨q, hq, by simp; omega⟩
  obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp hex
  simp only [hq']
  have hm := List.mem_of_find?_eq_some hq'
  have hp := List.find?_some hq'
  simp only [decide_eq_true_eq] at hp
  rw [← hc q hq q' hm (q.1 + k) (by omega) (by omega) hp.1 hp.2, Nat.add_sub_cancel_left,
    List.getD_eq_getElem _ _ hk]

end
end LeanVM.Guest.B1.Main

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1 (LowDef)

@[expose] public section

variable {P : Core.Program} {fs : String → ℕ} {cert : String → V → ℕ} {H : Inst → ℕ → E × E}
  {C : Inst → List (ℕ × E)} {hdr : E × E}

variable (P fs cert H C hdr) in
/-- **The certificate's facts about a tree** (group K): `DischargeHyps`' fields on the cells. -/
structure KFacts (T : Tree) : Prop where
  cells : CellsOk fs C (honestInsts P fs H hdr T)
  cells' : ∀ ν, CellsOk fs C (honestInsts P fs H hdr (T.retemp P fs ν (0, T.block fs P.loop)))
  cert_lt : ∀ f, ∀ t ∈ P.temps f, 2 ≤ cert f t ∧ cert f t < fs f
  cert_inj : ∀ f, ∀ t ∈ P.temps f, ∀ t' ∈ P.temps f, cert f t = cert f t' → t = t'
  run : ∀ I ∈ honestInsts P fs H hdr T, ∀ f σ bufs kids, I.t = .node f σ bufs kids →
    ∀ p r rs, Ev.atom (.frameAddr p (r :: rs)) ∈ I.t.events P →
      ∀ (k : ℕ) (hk : k < (r :: rs).length), (cert f r + k, σ (r :: rs)[k]) ∈ C I ∧
        ∀ t ∈ P.temps f, cert f r + k ≠ cert f t
  tmp : ∀ ν, ∀ I' ∈ honestInsts P fs H hdr (T.retemp P fs ν (0, T.block fs P.loop)), ∀ f σ bufs kids,
    I'.t = .node f σ bufs kids → ∀ t ∈ P.temps f, ∀ q ∈ C I', q.1 = cert f t → q.2 = σ t
  keep : ∀ ν, ∀ I ∈ honestInsts P fs H hdr T, ∀ I' ∈ honestInsts P fs H hdr (T.retemp P fs ν (0, T.block fs P.loop)),
    I'.fp = I.fp → I'.t = I.t.retemp P fs ν (I.fp, I.cur) → ∀ q ∈ I'.cells C,
      ¬ TmpOff P cert I.t q.1 →
      q ∈ I.cells C

theorem read_some_gpow {κ : ℕ} (hκ : κ < 64) {M : MemoryImage κ} {a : K} {v : E} (h : M.read a = some v) :
    ∃ i : Fin (2 ^ κ), a = Parameters.addressOfIndex i :=
  let ⟨i, hi, _⟩ := (MemoryImage.read_eq_some_iff hκ M).mp h; ⟨i, hi⟩

/-- **Every equation names a word of the memory**. -/
theorem dischargeAddr {κ : ℕ} (hκ : κ < 64) {M : MemoryImage κ} {T : Tree} {args rets : List E}
    (hv : T.Valid P M.read args rets) (hp : T.Placed P fs cert (0, T.block fs P.loop))
    (hrun : ∀ I ∈ honestInsts P fs H hdr T, ∀ f σ bufs kids, I.t = .node f σ bufs kids →
      ∀ p r rs, Ev.atom (.frameAddr p (r :: rs)) ∈ I.t.events P →
        ∀ k < (r :: rs).length, I.fp + (cert f r + k) < 2 ^ κ) :
    ∀ q ∈ T.eqns P, ∃ i : Fin (2 ^ κ), q.1 = Parameters.addressOfIndex i := by
  intro q hq
  obtain ⟨I, hI, ⟨f, σ, bufs, kids, ht⟩, a, ha, hqa⟩ := eqns_insts (lp := P.loop) (H := H) T _ hdr q hq
  have hgood := insts_good (H := H) T _ hdr hv I hI
  obtain ⟨fn, es, vs, hf, hw, hes⟩ : ∃ fn es vs, P.find? f = some fn ∧ walk σ fn.body = .ret es vs ∧
      ∀ e ∈ es, e.Holds M.read σ := by
    rcases hgood with ⟨_, _, hv'⟩ | ⟨_, _, hph⟩
    · rw [ht] at hv'
      obtain ⟨fn, hf, _, es, vs, hw, _, hes, _⟩ := hv'
      exact ⟨fn, es, vs, hf, hw, hes⟩
    · rw [ht] at hph; cases hph
  have hev : I.t.events P = es := by rw [ht]; exact events_node hf hw
  have hval : I.t.val = σ := by rw [ht]; rfl
  rw [hval] at hqa
  have hh := hes _ (hev ▸ ha)
  cases a with
  | load d p off =>
    simp only [atomEqns, List.mem_singleton] at hqa
    subst hqa
    exact read_some_gpow hκ hh.2
  | rangeCheck x y t1 t2 k =>
    simp only [atomEqns, List.mem_cons, List.not_mem_nil, or_false] at hqa
    rcases hqa with rfl | rfl
    · exact read_some_gpow hκ hh.1.2
    · exact read_some_gpow hκ hh.2.2.2
  | touch t p =>
    simp only [atomEqns, List.mem_singleton] at hqa
    subst hqa
    exact read_some_gpow hκ hh.2
  | frameAddr p run =>
    match run, hqa, ha with
    | r :: rs, hqa, ha =>
      simp only [atomEqns, List.mem_mapIdx] at hqa
      obtain ⟨k, hk, rfl⟩ := hqa
      have hpl := (Inst.nodeAt (insts_placedAt T _ hdr hp I hI)
        (insts_placed T _ hdr (Nat.zero_add _).le I hI) ht).2 (p, r)
        (List.mem_filterMap.mpr ⟨_, ha, rfl⟩)
      simp only at hpl
      rw [hpl, addr_ofK]
      have := hrun I hI f σ bufs kids ht p r rs ha k hk
      exact ⟨⟨_, by rw [← Nat.add_assoc] at this; exact this⟩, rfl⟩
  | _ => simp [atomEqns] at hqa

end
end LeanVM.Guest.B1.Main
