/-
  LeanVM.Guest.B1.Main.HonestPiece

  From a uniform placed relation of `main` at `0` to an honest tree (`HonestAt`): the memory image
  of the layout, the discharge's memory-side fields, its addresses, and `honestAt_retemp`.
-/

module

public import LeanVM.Guest.B1.Main.HonestImage

/-!
# The honest tree

`KFacts`: the certificate's facts the discharge takes of a tree (group K). `dischargeAddr`: every
equation of a tree valid on a memory image and placed at `0` names a word of it, its loads and
range checks by validity, its `frameAddr` runs by their certificate cells in their frames.
`honest_of_relAtIn`: if `main` holds by a tree placed at `0` of `N ≤ 2^32` words on every memory
holding a consistent layout `L` in `[2, N)` and the header, an honest tree of `N` words exists.
-/

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
  cells' : ∀ ν, CellsOk fs C (honestInsts P fs H hdr (T.retemp P fs ν 0))
  cert_lt : ∀ f, ∀ t ∈ P.temps f, 2 ≤ cert f t ∧ cert f t < fs f
  cert_inj : ∀ f, ∀ t ∈ P.temps f, ∀ t' ∈ P.temps f, cert f t = cert f t' → t = t'
  run : ∀ I ∈ honestInsts P fs H hdr T, ∀ f σ bufs kids, I.t = .node f σ bufs kids →
    ∀ p r rs, Ev.atom (.frameAddr p (r :: rs)) ∈ I.t.events P →
      ∀ (k : ℕ) (hk : k < (r :: rs).length), (cert f r + k, σ (r :: rs)[k]) ∈ C I ∧
        ∀ t ∈ P.temps f, cert f r + k ≠ cert f t
  tmp : ∀ ν, ∀ I' ∈ honestInsts P fs H hdr (T.retemp P fs ν 0), ∀ f σ bufs kids,
    I'.t = .node f σ bufs kids → ∀ t ∈ P.temps f, ∀ q ∈ C I', q.1 = cert f t → q.2 = σ t
  keep : ∀ ν, ∀ I ∈ honestInsts P fs H hdr T, ∀ I' ∈ honestInsts P fs H hdr (T.retemp P fs ν 0),
    I'.fp = I.fp → I'.t = I.t.retemp P fs ν I.fp → ∀ q ∈ I'.cells C, ¬ TmpOff P cert I.t q.1 →
      q ∈ I.cells C

theorem read_some_gpow {κ : ℕ} (hκ : κ < 64) {M : MemImage κ} {a : K} {v : E} (h : M.read a = some v) :
    ∃ i : Fin (2 ^ κ), a = Parameters.gpow i :=
  let ⟨i, hi, _⟩ := (MemImage.read_eq_some_iff hκ M).mp h; ⟨i, hi⟩

/-- **Every equation names a word of the memory**. -/
theorem dischargeAddr {κ : ℕ} (hκ : κ < 64) {M : MemImage κ} {T : Tree} {args rets : List E}
    (hv : T.Valid P M.read args rets) (hp : T.Placed P fs cert 0)
    (hrun : ∀ I ∈ honestInsts P fs H hdr T, ∀ f σ bufs kids, I.t = .node f σ bufs kids →
      ∀ p r rs, Ev.atom (.frameAddr p (r :: rs)) ∈ I.t.events P →
        ∀ k < (r :: rs).length, I.fp + (cert f r + k) < 2 ^ κ) :
    ∀ q ∈ T.eqns P, ∃ i : Fin (2 ^ κ), q.1 = Parameters.gpow i := by
  intro q hq
  obtain ⟨I, hI, ⟨f, σ, bufs, kids, ht⟩, a, ha, hqa⟩ := eqns_insts (lp := P.loop) (H := H) T 0 hdr q hq
  have hgood := insts_good (H := H) T 0 hdr hv I hI
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
  | frameAddr p run =>
    match run, hqa, ha with
    | r :: rs, hqa, ha =>
      simp only [atomEqns, List.mem_mapIdx] at hqa
      obtain ⟨k, hk, rfl⟩ := hqa
      have hpl := (Inst.nodeAt (insts_placedAt T 0 hdr hp I hI) (insts_placed T 0 hdr I hI) ht).2 (p, r)
        (List.mem_filterMap.mpr ⟨_, ha, rfl⟩)
      simp only at hpl
      rw [hpl, addr_ofK]
      have := hrun I hI f σ bufs kids ht p r rs ha k hk
      exact ⟨⟨_, by rw [← Nat.add_assoc] at this; exact this⟩, rfl⟩
  | _ => simp [atomEqns] at hqa

end
end LeanVM.Guest.B1.Main
