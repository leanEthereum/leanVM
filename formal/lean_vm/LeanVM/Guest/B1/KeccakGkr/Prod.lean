/-
  LeanVM.Guest.B1.KeccakGkr.Prod

  The product polynomial in `keccak_layer` (G:2709-2723): its 47 coefficients read, packed and
  absorbed, and the projection onto the claim's instance weights; a template over a table of
  value numbers.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerW
public import LeanVM.Protocol.Keccak.Rmfe

/-!
# The product polynomial

Position `k < 47` (`PPos`): the coefficient read into `a` (`cursor[k]`), with a full queue first
the permutation of the waiting scalars (`kc`: its thirteen inputs and its first output), the
coefficient packed (`fs_pack` from `fb`), the reader `Σ_{i ∈ idx} μ_i` (a chain of additions from
`rb`, `readerT`), the product `r = reader·a` and the running projection `acc = accPrev + r`
(`prodPosT`). `prodPos_holds` reads the facts off a position.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- One position of the product's section: its value numbers. -/
structure PPos where
  a : ℕ
  kc : Option (List ℕ × ℕ)
  fb : ℕ
  idx : List ℕ
  rb : ℕ
  r : ℕ
  accPrev : Option ℕ
  acc : ℕ
  deriving Inhabited

/-- The additions after the first: `nv = prev + μ_j`. -/
def readerChainT (muB : ℕ) : List ℕ → ℕ → ℕ → List Stmt
  | [], _, _ => []
  | j :: rest, prev, nv => .atom (.add (.n nv) (.n prev) (.n (muB + j))) :: readerChainT muB rest nv (nv + 1)

/-- The reader's additions from `rb`. -/
def readerT (muB : ℕ) : List ℕ → ℕ → List Stmt
  | i0 :: i1 :: rest, rb => .atom (.add (.n rb) (.n (muB + i0)) (.n (muB + i1))) ::
      readerChainT muB rest rb (rb + 1)
  | _, _ => []

/-- The reader's value. -/
def readerOut (muB : ℕ) (idx : List ℕ) (rb : ℕ) : ℕ :=
  match idx with
  | [i] => muB + i
  | _ => rb + idx.length - 2

/-- Position `k`. -/
def prodPosT (cur : V) (muB k : ℕ) (p : PPos) : List Stmt :=
  [.atom (.load (.n p.a) cur k)] ++
    (match p.kc with
      | some (ins, o) => [keccakA (ins.map .n) ((List.range 13).map fun j ↦ .n (o + j))]
      | none => []) ++
    fsPackT (.n p.a) p.fb dsObserve ++ readerT muB p.idx p.rb ++
    [.atom (.mul (.n p.r) (.n (readerOut muB p.idx p.rb)) (.n p.a))] ++
    (match p.accPrev with
      | some q => [.atom (.add (.n p.acc) (.n q) (.n p.r))]
      | none => [])

/-- The positions of a table from position `k`. -/
def prodTFrom (cur : V) (muB : ℕ) : ℕ → List PPos → List Stmt
  | _, [] => []
  | k, p :: ps => prodPosT cur muB k p ++ prodTFrom cur muB (k + 1) ps

/-- The section: the positions of a table. -/
def prodT (cur : V) (muB : ℕ) (tab : List PPos) : List Stmt := prodTFrom cur muB 0 tab

/-! ## The reader -/

/-- The reader's chain of additions, from `prev`: the last value is `prev` plus the indices'
weights. -/
theorem readerChain_val {muB : ℕ} : ∀ (rest : List ℕ) (prev nv : ℕ),
    (∀ a, Stmt.atom a ∈ readerChainT muB rest prev nv → a.Holds rd σ) → rest ≠ [] →
    σ (.n (nv + rest.length - 1)) = σ (.n prev) + (rest.map fun j ↦ σ (.n (muB + j))).sum
  | [], _, _, _, h => absurd rfl h
  | [j], prev, nv, H, _ => by
    have h0 := H (.add (.n nv) (.n prev) (.n (muB + j))) (by simp [readerChainT])
    simp only [Atom.Holds] at h0
    simpa using h0
  | j :: j' :: rest, prev, nv, H, _ => by
    have h0 := H (.add (.n nv) (.n prev) (.n (muB + j))) (by simp [readerChainT])
    simp only [Atom.Holds] at h0
    have ih := readerChain_val (j' :: rest) nv (nv + 1)
      (fun a ha ↦ H a (by rw [readerChainT]; exact List.mem_cons_of_mem _ ha)) (by simp)
    simp only [List.length_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [show nv + (rest.length + 1 + 1) - 1 = nv + 1 + (rest.length + 1) - 1 by omega, ih, h0]
    ring

/-- **The reader's value**: the sum of the weights of its indices. -/
theorem reader_val {muB rb : ℕ} {idx : List ℕ}
    (H : ∀ a, Stmt.atom a ∈ readerT muB idx rb → a.Holds rd σ) (hne : idx ≠ []) :
    σ (.n (readerOut muB idx rb)) = (idx.map fun i ↦ σ (.n (muB + i))).sum := by
  match idx, hne with
  | [i], _ => simp [readerOut]
  | i0 :: i1 :: rest, _ =>
    have h0 := H (.add (.n rb) (.n (muB + i0)) (.n (muB + i1))) (by simp [readerT])
    simp only [Atom.Holds] at h0
    have hro : readerOut muB (i0 :: i1 :: rest) rb = rb + rest.length := by
      simp only [readerOut, List.length_cons]; omega
    rw [hro]
    rcases rest with _ | ⟨j, rest⟩
    · simp [h0]
    · have := readerChain_val (muB := muB) (j :: rest) rb (rb + 1)
        (fun a ha ↦ H a (by rw [readerT]; exact List.mem_cons_of_mem _ ha)) (by simp)
      simp only [List.length_cons, List.map_cons, List.sum_cons] at this ⊢
      rw [show rb + (rest.length + 1) = rb + 1 + (rest.length + 1) - 1 by omega, this, h0]
      ring

/-! ## One position -/

theorem allAtoms_fsPackT (x : V) (b t : ℕ) : AllAtoms (fsPackT x b t) := by
  intro s hs
  simp only [fsPackT, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;> exact ⟨_, rfl⟩

/-- The facts of position `k`. -/
theorem prodPos_facts {cur : V} {muB k : ℕ} {p : PPos}
    (H : ∀ a, Stmt.atom a ∈ prodPosT cur muB k p → a.Holds rd σ) :
    LoadHolds rd (σ cur) k (σ (.n p.a)) ∧
    (∀ ins o, p.kc = some (ins, o) →
      (Atom.keccak (ins.map .n) ((List.range 13).map fun j ↦ .n (o + j)) false false).Holds rd σ) ∧
    FsPackOk σ (.n p.a) p.fb dsObserve ∧
    (∀ a, Stmt.atom a ∈ readerT muB p.idx p.rb → a.Holds rd σ) ∧
    σ (.n p.r) = σ (.n (readerOut muB p.idx p.rb)) * σ (.n p.a) ∧
    (∀ q, p.accPrev = some q → σ (.n p.acc) = σ (.n q) + σ (.n p.r)) := by
  have hm : ∀ a, (Stmt.atom a ∈ fsPackT (.n p.a) p.fb dsObserve ∨
      Stmt.atom a ∈ readerT muB p.idx p.rb) → Stmt.atom a ∈ prodPosT cur muB k p := by
    intro a ha
    simp only [prodPosT, List.mem_append]
    rcases ha with ha | ha
    · exact Or.inl (Or.inl (Or.inl (Or.inr ha)))
    · exact Or.inl (Or.inl (Or.inr ha))
  refine ⟨?_, ?_, ?_, fun a ha ↦ H a (hm a (Or.inr ha)), ?_, ?_⟩
  · exact H (.load (.n p.a) cur k) (by simp [prodPosT])
  · intro ins o hk
    exact H _ (by simp [prodPosT, hk, keccakA])
  · have := (holdsList_atoms (C := fun _ _ _ ↦ True) (allAtoms_fsPackT (.n p.a) p.fb dsObserve) True
      (fun _ ↦ False)).2 ⟨fun a ha ↦ H a (hm a (Or.inl ha)), trivial⟩
    exact ((holds_fsPackT (C := fun _ _ _ ↦ True) _ _ _ _ _).1 this).1
  · exact H (.mul (.n p.r) (.n (readerOut muB p.idx p.rb)) (.n p.a)) (by simp [prodPosT])
  · intro q hq
    exact H (.add (.n p.acc) (.n q) (.n p.r)) (by simp [prodPosT, hq])

theorem prodTFrom_cons_mem {cur : V} {muB k : ℕ} {p : PPos} {ps : List PPos}
    (H : ∀ a, Stmt.atom a ∈ prodTFrom cur muB k (p :: ps) → a.Holds rd σ) :
    (∀ a, Stmt.atom a ∈ prodPosT cur muB k p → a.Holds rd σ) ∧
      ∀ a, Stmt.atom a ∈ prodTFrom cur muB (k + 1) ps → a.Holds rd σ :=
  ⟨fun a ha ↦ H a (by rw [prodTFrom]; exact List.mem_append_left _ ha),
    fun a ha ↦ H a (by rw [prodTFrom]; exact List.mem_append_right _ ha)⟩

/-! ## The loads -/

/-- Position `k + j` reads its coefficient at `cur·g^(k + j)`. -/
theorem prodTFrom_loads {cur : V} {muB : ℕ} : ∀ (ps : List PPos) (k : ℕ),
    (∀ a, Stmt.atom a ∈ prodTFrom cur muB k ps → a.Holds rd σ) →
    ∀ j (hj : j < ps.length), LoadHolds rd (σ cur) (k + j) (σ (.n ps[j].a))
  | [], _, _, j, hj => absurd hj (by simp)
  | p :: ps, k, H, j, hj => by
    obtain ⟨H0, H1⟩ := prodTFrom_cons_mem H
    rcases j with _ | j
    · simpa using (prodPos_facts H0).1
    · have := prodTFrom_loads ps (k + 1) H1 j (by simpa using hj)
      rw [show k + 1 + j = k + (j + 1) by omega] at this
      simpa using this

/-! ## The sponge -/

/-- The cell values of waiting scalars, in order. -/
def pendCellsV (pv : List (V × V)) : List V := pv.flatMap fun c ↦ [c.1, c.2]

/-- The cells a position's `fs_pack` writes. -/
def cellsOfPos (p : PPos) : V × V := (.n p.fb, .n (p.fb + 1))

/-- The capacity cells of a permutation's outputs from `o`. -/
def capOuts (o : ℕ) : List V := (List.range 5).map fun j ↦ .n (o + 8 + j)

/-- One position on the guest's sponge (capacity cells, waiting cells): with a full queue, the
permutation of the waiting cells and the capacity first. -/
def spStep (st : List V × List (V × V)) (p : PPos) : Option (List V × List (V × V)) :=
  match p.kc with
  | some (ins, o) =>
      if st.2.length = 4 ∧ ins.map V.n = pendCellsV st.2 ++ st.1 then
        some (capOuts o, [cellsOfPos p])
      else none
  | none => if st.2.length < 4 then some (st.1, st.2 ++ [cellsOfPos p]) else none

/-- The positions on the guest's sponge. -/
def spChain : List V × List (V × V) → List PPos → Option (List V × List (V × V))
  | st, [] => some st
  | st, p :: ps =>
      match spStep st p with
      | some st' => spChain st' ps
      | none => none

/-- The waiting scalars against their cells' values: the scalar's rate cells. -/
def PendOk (σ : Val) : List (E × ℕ) → List (V × V) → Prop
  | [], [] => True
  | q :: qs, c :: cs =>
      (σ c.1, σ c.2) = Keccak.scalarCells q.1 q.2 ∧ PendOk σ qs cs
  | _, _ => False

/-- The sponge `s` against the guest's cells. -/
def SpOk (σ : Val) (s : Fs) (st : List V × List (V × V)) : Prop :=
  s.cap = st.1.map σ ∧ PendOk σ s.pend st.2

theorem pendOk_length : ∀ {qs : List (E × ℕ)} {cs : List (V × V)}, PendOk σ qs cs →
    qs.length = cs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [pendOk_length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem pendOk_append : ∀ {qs : List (E × ℕ)} {cs : List (V × V)} {q : E × ℕ} {c : V × V},
    PendOk σ qs cs → (σ c.1, σ c.2) = Keccak.scalarCells q.1 q.2 →
    PendOk σ (qs ++ [q]) (cs ++ [c])
  | [], [], _, _, _, h => ⟨h, trivial⟩
  | _ :: _, _ :: _, _, _, h, hc => ⟨h.1, pendOk_append h.2 hc⟩
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim

theorem pendOk_cells : ∀ {qs : List (E × ℕ)} {cs : List (V × V)}, PendOk σ qs cs →
    (pendCellsV cs).map σ = pendCells qs
  | [], [], _ => rfl
  | q :: qs, c :: cs, h => by
    have e := h.1
    simp only [Prod.ext_iff] at e
    simp only [pendCellsV, pendCells, List.flatMap_cons, List.map_cons, List.cons_append,
      List.nil_append] at ⊢
    rw [e.1, e.2]
    congr 2
    exact pendOk_cells h.2
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- **A permutation of the guest's cells**: on the waiting cells (zeros past them) and the
capacity, its outputs are the cells of the sponge's next permutation. -/
theorem spOk_perm {s : Fs} {st : List V × List (V × V)} (h : SpOk σ s st) {ins outs : List V}
    (hk : (Atom.keccak ins outs false false).Holds rd σ) {zs : List V}
    (hin : ins = pendCellsV st.2 ++ zs ++ st.1)
    (hz : zs.map σ = List.replicate (8 - 2 * st.2.length) 0) (hl : st.2.length ≤ 4)
    (ho : outs.length = 13 := by first | rfl | simp) :
    s.perm = permOf (ins.map σ) ∧
      ∀ k (hk : k < 13), σ (outs.getD k default) = cellsOfState s.perm false ⟨k, hk⟩ := by
  obtain ⟨-, -, hout⟩ := keccak_outs hk ho
  have hlen := pendOk_length h.2
  have hp : s.perm = permOf (ins.map σ) := by
    rw [perm_eq_cells s (by omega), hin, List.map_append, List.map_append, pendOk_cells h.2,
      hz, hlen, h.1]
  exact ⟨hp, fun k hk ↦ by rw [hp]; exact hout k hk⟩

theorem capOf_outs {S : KeccakState} {o : ℕ}
    (h : ∀ k (hk : k < 13), σ (((List.range 13).map fun j ↦ V.n (o + j)).getD k default) =
      cellsOfState S false ⟨k, hk⟩) :
    capOf S = (capOuts o).map σ := by
  have e : ∀ j (hj : j < 5), σ (.n (o + 8 + j)) = cellsOfState S false ⟨8 + j, by omega⟩ := by
    intro j hj
    have := h (8 + j) (by omega)
    rw [List.getD_eq_getElem _ _ (by simp; omega)] at this
    simpa [Nat.add_assoc] using this
  simp only [capOf, capOuts, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append]
  rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega)]
  rfl

/-- One position on the sponge. -/
theorem spStep_sound {st st' : List V × List (V × V)} {p : PPos} (hs : spStep st p = some st')
    {s : Fs} (h : SpOk σ s st)
    (hk : ∀ ins o, p.kc = some (ins, o) →
      (Atom.keccak (ins.map .n) ((List.range 13).map fun j ↦ .n (o + j)) false false).Holds rd σ)
    (hp : FsPackOk σ (.n p.a) p.fb dsObserve) :
    SpOk σ (s.absorb (σ (.n p.a)) dsObserve) st' := by
  have hcells : (σ (cellsOfPos p).1, σ (cellsOfPos p).2) =
      Keccak.scalarCells (σ (.n p.a)) dsObserve := fsPackT_cells hp
  have hlen := pendOk_length h.2
  unfold spStep at hs
  split at hs
  · rename_i ins o hkc
    split at hs
    · rename_i hc
      cases hs
      obtain ⟨hl4, hin⟩ := hc
      obtain ⟨hperm, hout⟩ := spOk_perm h (hk ins o hkc) (zs := []) (by rw [hin, List.append_nil])
        (by rw [hl4]; rfl) (by omega)
      have hfull : s.pend.length = rateScalars := by rw [hlen, hl4]; rfl
      simp only [Fs.absorb, hfull, ↓reduceIte]
      exact ⟨capOf_outs hout, hcells, trivial⟩
    · cases hs
  · split at hs
    · rename_i hl
      cases hs
      have hne : s.pend.length ≠ rateScalars := by rw [hlen]; unfold rateScalars; omega
      simp only [Fs.absorb, hne, ↓reduceIte]
      exact ⟨h.1, pendOk_append h.2 hcells⟩
    · cases hs

/-- **The positions on the sponge**: from the guest's cells of `s`, the positions absorb their
coefficients, to the cells `spChain` computes. -/
theorem spChain_sound {cur : V} {muB : ℕ} : ∀ (ps : List PPos) (k : ℕ)
    (st stF : List V × List (V × V)) (s : Fs), spChain st ps = some stF → SpOk σ s st →
    (∀ a, Stmt.atom a ∈ prodTFrom cur muB k ps → a.Holds rd σ) →
    SpOk σ (s.absorbAll (ps.map fun p ↦ σ (.n p.a)) dsObserve) stF
  | [], _, st, stF, s, hc, h, _ => by
    simp only [spChain, Option.some.injEq] at hc
    subst hc; exact h
  | p :: ps, k, st, stF, s, hc, h, H => by
    obtain ⟨H0, H1⟩ := prodTFrom_cons_mem H
    obtain ⟨-, hk, hp, -⟩ := prodPos_facts H0
    simp only [spChain] at hc
    split at hc
    · rename_i st' hs
      exact spChain_sound ps (k + 1) st' stF _ hc (spStep_sound hs h hk hp) H1
    · cases hc

/-! ## The projection -/

/-- The value number of a running sum, `0` before the first. -/
def ov (σ : Val) : Option ℕ → E
  | none => 0
  | some q => σ (.n q)

/-- The projection's reader of bit `b`: the indices of the masks with bit `b`. -/
def projIdx (b : ℕ) : List ℕ := (List.range 16).filter fun i ↦ (projectLit.getD i 0).testBit b

/-- The running sum's checks from position `k`: each reader is `R`'s (the indices of its
values above `muB`), the first sum is the first product. -/
def accOk (R : ℕ → List ℕ) : Option ℕ → ℕ → List PPos → Bool
  | _, _, [] => true
  | prev, k, p :: ps => p.accPrev == prev && p.idx == R k && p.idx != [] &&
      (prev.isSome || p.acc == p.r) && accOk R (some p.acc) (k + 1) ps

/-- The last running sum. -/
def accLast : Option ℕ → List PPos → Option ℕ
  | prev, [] => prev
  | _, p :: ps => accLast (some p.acc) ps

/-- **The running sum**: the readers times the coefficients. -/
theorem accOk_sound {cur : V} {muB : ℕ} {R : ℕ → List ℕ} : ∀ (ps : List PPos) (prev : Option ℕ)
    (k : ℕ), accOk R prev k ps = true →
    (∀ a, Stmt.atom a ∈ prodTFrom cur muB k ps → a.Holds rd σ) →
    ov σ (accLast prev ps) = ov σ prev + ((List.range ps.length).map fun j ↦
      ((R (k + j)).map fun i ↦ σ (.n (muB + i))).sum * σ (.n (ps.getD j default).a)).sum
  | [], prev, _, _, _ => by simp [accLast]
  | p :: ps, prev, k, hok, H => by
    obtain ⟨H0, H1⟩ := prodTFrom_cons_mem H
    obtain ⟨-, -, -, hrd, hr, hacc⟩ := prodPos_facts H0
    simp only [accOk, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.or_eq_true,
      Option.isSome_iff_ne_none] at hok
    obtain ⟨⟨⟨⟨hprev, hidx⟩, hne⟩, hfirst⟩, hrest⟩ := hok
    have ih := accOk_sound ps (some p.acc) (k + 1) hrest H1
    have hv : σ (.n p.acc) = ov σ prev +
        ((R k).map fun i ↦ σ (.n (muB + i))).sum * σ (.n p.a) := by
      rw [← hidx, ← reader_val hrd hne, ← hr]
      rcases prev with _ | q
      · have : p.acc = p.r := by simpa using hfirst
        simp [ov, this]
      · simp [ov, hacc q hprev]
    simp only [accLast, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.sum_cons]
    rw [ih]
    simp only [ov] at hv ⊢
    rw [hv]
    simp only [Nat.add_zero, List.getD_cons_zero, Function.comp_def, Nat.succ_eq_add_one,
      List.getD_cons_succ, show ∀ x, k + 1 + x = k + (x + 1) from fun x ↦ by omega]
    ring

/-- A sum over a filtered range. -/
theorem sum_filter_range (P : ℕ → Bool) (f : ℕ → E) : ∀ n,
    (((List.range n).filter P).map f).sum = ∑ i ∈ Finset.range n, if P i then f i else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append,
      sum_filter_range P f n, Finset.sum_range_succ]
    cases h : P n <;> simp [h]

end
end LeanVM.Guest.B1.VerifySub
