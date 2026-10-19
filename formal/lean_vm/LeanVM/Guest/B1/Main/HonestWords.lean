/-
  LeanVM.Guest.B1.Main.HonestWords

  `main`'s words in an honest run, from a witness of `NodeRel`: the regions' slots and their
  marks, the tables, the children's iterations (`honestWords`).
-/

module

public import LeanVM.Guest.B1.Main.MainAt
public import LeanVM.Guest.B1.Main.MainHonest

/-!
# `main`'s honest words

Each region's writers (`writersX`, …) take their slots by `assign` (`planX`, …): every slot
holds its writer's claim, no two writers share one (`region_slots`). The writers are numbered
in `main`'s order: the raw leanXMSS, leanSPHINCS and DA claims, then each child's three lists;
writer `g` marks its slot with `g^g`. A region's marks (`covOf`) put at each slot the mark of the
writer holding it (`covOf_slot`), the writer's number read from its position in the region
(`gX`, `gS`, `gD`). `honestWords` collects the counts, tables and digests.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (direct)

@[expose] public section

/-! ## Holders -/

theorem direct_mem {α W : Type} {P : α → Holder W → Prop} : ∀ {cs : List α} {hs : List (Holder W)},
    List.Forall₂ P cs hs → ∀ {p : α × W}, p ∈ direct cs hs → P p.1 (.direct p.2)
  | [], [], .nil, p, hp => by simp [direct] at hp
  | _ :: _, .direct _ :: _, .cons h1 h2, p, hp => by
    simp only [direct, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h1
    · exact direct_mem h2 hp
  | _ :: _, .child _ :: _, .cons _ h2, p, hp => by
    simp only [direct] at hp
    exact direct_mem h2 hp

/-! ## A region's slots -/

section Region

variable {α : Type} [DecidableEq α]

/-- **A region's slots**: one per writer, distinct, in the region, each holding its writer's
claim. -/
theorem region_slots (D W : List α) :
    (assign D [] [] W).1.length = W.length ∧ (assign D [] [] W).1.Nodup ∧
      ∀ i < W.length, (assign D [] [] W).1.getD i 0 < D.length + (assign D [] [] W).2.length ∧
        (D ++ (assign D [] [] W).2)[(assign D [] [] W).1.getD i 0]? = W[i]? := by
  obtain ⟨i1, -, i3, i4, i5, -, -⟩ := assign_spec D W [] [] (by simp) List.nodup_nil
  refine ⟨i1, by simpa using i4, fun i hi => ⟨?_, i3 i hi⟩⟩
  have hmem : (assign D [] [] W).1.getD i 0 ∈ (assign D [] [] W).1 := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  rcases i5 _ hmem with h | h
  · omega
  · simp only [List.length_nil, Nat.add_zero] at h; omega

/-- **A region's marks**: at each of its `n` slots, `g^(gl r)` for the writer `r` holding it. -/
noncomputable def covOf (sl : List ℕ) (gl : ℕ → ℕ) (n : ℕ) : List E :=
  (List.range n).map fun k => gen ^ gl (sl.idxOf k)

theorem covOf_length (sl : List ℕ) (gl : ℕ → ℕ) (n : ℕ) : (covOf sl gl n).length = n := by
  simp [covOf]

theorem covOf_slot {sl : List ℕ} {gl : ℕ → ℕ} {n : ℕ} (hnd : sl.Nodup) {r : ℕ} (hr : r < sl.length)
    (hn : sl.getD r 0 < n) :
    (covOf sl gl n)[sl.getD r 0]'(by rw [covOf_length]; exact hn) = gen ^ gl r := by
  simp only [covOf, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ hr, hnd.idxOf_getElem]

end Region

/-! ## The writers' numbers -/

section Node

variable (seed : Digest) (s : NodeStatement) (w : NodeWitness)

/-- A child's claim counts. -/
def cnx (c : Child) : ℕ := c.statement.claims.xmss.length
def cns (c : Child) : ℕ := c.statement.claims.sphincs.length
def cnda (c : Child) : ℕ := c.statement.claims.da.length

/-- A child's writers. -/
def cnw (c : Child) : ℕ := cnx c + cns c + cnda c

/-- The raw claims' counts. -/
def hrx : ℕ := (direct s.claims.xmss w.xmss).length
def hrs : ℕ := (direct s.claims.sphincs w.sphincs).length
def hrd : ℕ := (direct s.claims.da w.da).length

/-- **Child `c`'s first writer's number**: after the raw claims and the earlier children's. -/
def hbase (c : ℕ) : ℕ := hrx s w + hrs s w + hrd s w + ((w.children.take c).map cnw).sum

/-- The number of the writer at position `t` of the children's claims of one kind (`sel` of
them per child, after `pre` of the child's earlier kinds), the children's writers from `b`. -/
def locIn (sel pre : Child → ℕ) : List Child → ℕ → ℕ → ℕ
  | [], t, b => b + t
  | c :: cs, t, b => if t < sel c then b + pre c + t else locIn sel pre cs (t - sel c) (b + cnw c)

theorem locIn_at (sel pre : Child → ℕ) : ∀ (cs : List Child) (b c j : ℕ) (hc : c < cs.length),
    j < sel cs[c] →
    locIn sel pre cs (((cs.take c).map sel).sum + j) b = b + ((cs.take c).map cnw).sum + pre cs[c] + j
  | [], _, _, _, hc, _ => absurd hc (by simp)
  | x :: cs, b, 0, j, _, hj => by
    simp only [List.getElem_cons_zero] at hj
    simp [locIn, hj]
  | x :: cs, b, c + 1, j, hc, hj => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ] at hj ⊢
    have hn : ¬ (sel x + ((cs.take c).map sel).sum + j < sel x) := by omega
    rw [locIn]
    simp only [hn, ↓reduceIte]
    rw [show sel x + ((cs.take c).map sel).sum + j - sel x =
      ((cs.take c).map sel).sum + j by omega, locIn_at sel pre cs _ c j (by simpa using hc) hj]
    ring

/-- The number of the leanXMSS region's writer `r`. -/
def gX (r : ℕ) : ℕ :=
  if r < hrx s w then r else locIn cnx (fun _ => 0) w.children (r - hrx s w) (hrx s w + hrs s w + hrd s w)

/-- The number of the leanSPHINCS region's writer `r`. -/
def gS (r : ℕ) : ℕ :=
  if r < hrs s w then hrx s w + r
  else locIn cns cnx w.children (r - hrs s w) (hrx s w + hrs s w + hrd s w)

/-- The number of the DA region's writer `r`. -/
def gD (r : ℕ) : ℕ :=
  if r < hrd s w then hrx s w + hrs s w + r
  else locIn cnda (fun c => cnx c + cns c) w.children (r - hrd s w) (hrx s w + hrs s w + hrd s w)

/-! ## The words -/

/-- A leanXMSS claim's four cells. -/
def xCellsOf (c : XmssClaim) : List E := List.ofFn (LeanVM.Guest.B1.claimCells c.1.root c.1.parameter c.2)

/-- A leanSPHINCS claim's four cells. -/
def sCellsOf (c : SphincsClaim) : List E := List.ofFn (LeanVM.Guest.B1.claimCells c.1.root c.1.parameter c.2)

/-- **A child's iteration in an honest run**, its first writer's number `b`. -/
def childWordsOf (c : Child) (b : ℕ) : ChildWords :=
  ⟨gen ^ b, cnx c, cns c, c.statement.claims.da,
    digestScalars (xmssListDigest c.statement.claims.xmss),
    digestScalars (sphincsListDigest c.statement.claims.sphincs),
    signersDigest c.statement.claims.xmss c.statement.claims.sphincs, c.statement.defer.cells,
    statementDigest seed c.statement⟩

/-- The direct DA claim's cells. -/
def drOf : List (DaClaim × Da.Witness) → E × E × E × E
  | p :: _ => ((digestScalars p.1.1).1, (digestScalars p.1.1).2, (digestScalars p.1.2).1,
      (digestScalars p.1.2).2)
  | [] => (0, 0, 0, 0)

/-- **`main`'s words in an honest run.** -/
noncomputable def honestWords : MainWords where
  dx := s.claims.xmss.length
  ux := (planX s w).2.length
  rx := hrx s w
  ds := s.claims.sphincs.length
  us := (planS s w).2.length
  rs := hrs s w
  nc := w.children.length
  rd := hrd s w
  da := s.claims.da.length
  ud := (planD s w).2.length
  drows := ((direct s.claims.da w.da).map fun p => p.2.rows.length).sum
  seed := seed
  daTab := (s.claims.da ++ (planD s w).2).flatMap daCellsOf
  xTab := (s.claims.xmss ++ (planX s w).2).flatMap xCellsOf
  sTab := (s.claims.sphincs ++ (planS s w).2).flatMap sCellsOf
  cov := covOf (planX s w).1 (gX s w) (s.claims.xmss.length + (planX s w).2.length) ++
    covOf (planS s w).1 (gS s w) (s.claims.sphincs.length + (planS s w).2.length) ++
    covOf (planD s w).1 (gD s w) (s.claims.da.length + (planD s w).2.length)
  cpiTab := w.children.flatMap fun c =>
    [(digestScalars (statementDigest seed c.statement)).1, (digestScalars (statementDigest seed c.statement)).2]
  frTab := w.children.flatMap fun c => fixedCells c.fresh
  carTab := w.children.flatMap fun c => c.statement.defer.cells
  wTab := (List.range (w.children.length + 1)).map fun c => gen ^ hbase s w c
  dTab := s.defer.cells
  daDig := daListDigest s.claims.da
  xDig := xmssListDigest s.claims.xmss
  sDig := sphincsListDigest s.claims.sphincs
  sigDig := signersDigest s.claims.xmss s.claims.sphincs
  stDig := statementDigest seed s
  dr := drOf (direct s.claims.da w.da)
  lbv := s.defer.bytecodeValue
  lmA := s.defer.matrixA
  lmB := s.defer.matrixB
  child := fun c => if h : c < w.children.length then childWordsOf seed w.children[c] (hbase s w c)
    else childWordsOf seed ⟨⟨⟨[], [], []⟩, ⟨[], 0, [], 0, 0⟩⟩, ⟨[], 0, 0, 0, [], [], [], 0⟩, ⟨[], []⟩⟩ 0
  slX := fun c => (planX s w).1.getD c 0
  slS := fun c => (planS s w).1.getD c 0

end Node

end
end LeanVM.Guest.B1.Main
