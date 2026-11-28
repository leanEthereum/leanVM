/-
  LeanVM.Prover.Complete.Link.Skeleton

  The link's honest prover wins `verifyLink`, from the facts about the honest witness the link's
  checks read (`LinkFacts`): the moves aligned, every arithmetic fact a hypothesis.
-/

module

public import LeanVM.Prover.Complete.Link.Split
public import LeanVM.Prover.Complete.Link.Rows
public import LeanVM.Prover.Complete.Assemble
public import LeanVM.Wire.HonestCost

/-!
# The link, from its facts

`verifyLink computedSplit` (`Statement/Verifier/Link.lean`) against the honest prover `linkProve`
(`Statement/Prover/Link.lean`), both split (`Link/Split.lean`): the prefix (the grind, the
challenges, the index side, `M_1`, the fresh coefficients), the program's split, the row rounds,
the pointer-column rounds, the packed message and the terminal check.

`LinkFacts W` lists what the moves need of the witness, each as exact Lean:

* the sizes: the layout's tables, the chunks, the grind's bits, the program's length;
* `index`: the index side's cube sum is the state identity's claim
  `eq(ζ, 0)·ŝ_init + eq(ζ, T)·ŝ_fin` (the state chain telescopes, the memory and the program
  lookups balance), and its tables' shape;
* `rowStart`: the index side's value at `r` is the rows' claim (the row side's sum is the index
  summand at `r`, every fresh identity zero on the honest rows), and the rows' shape;
* `columns`: the bound rows' claim is the pointer-column rounds' cube sum, and their shape;
* `message`: the message's length;
* `tail`: the terminal check passes on the honest message, and what the link returns holds
  (`LinkOut`).

`wins_link_of`: from these, the honest prover beside `verifyLink` wins with `LinkOut`, the form
`LinkWins` asks.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Protocol.Verifier.Defers LeanVM.Prover.Complete.Keccak

/-- The tallest table's row variables. -/
abbrev linkNRows (W : Witness) : ℕ := W.layout.tableLogHeights.foldl max 0

/-- The honest `M_1` at the index point `r`. -/
def honestM1 (W : Witness) (r : List E) : E :=
  let rMem := r.take W.layout.logMemory
  (mleK (W.cols.getD memory0 #[]) rMem + eY * mleK (W.cols.getD memory1 #[]) rMem) *
    prodE ((r.drop (min W.layout.logMemory W.chunks.width)).map (1 + ·))

/-- **What the honest prefix holds**: the verifier's `y` and the prover's `x` after the prefix. -/
structure HonestPre (W : Witness) (y : LinkPre) (x : LinkProverPre) : Prop where
  chunks : y.chunks = W.chunks
  drawn : y.drawn.length = packedChallenges tables (linkNRows W) W.chunks.width
  ch : x.ch = LinkChallenges.ofDraw tables (linkNRows W) W.chunks.width W.chunks.d y.theta0 y.drawn
  r : y.r = x.r
  rlen : x.r.length = W.chunks.width
  index : x.index = x.r.foldl Prods.fold (indexProds W x.ch)
  claim : y.claim = x.index.value
  m1 : y.m1 = x.m1
  m1eq : x.m1 = honestM1 W x.r
  fresh : y.fresh = x.fresh
  freshlen : x.fresh.length = 5

/-- The program side the link reads, from the computed split at its point. -/
def honestProgramSide (W : Witness) (y : LinkPre) : E × E :=
  programSide (linkWeights W.layout y)
    (splitAt W.layout.bytecode (y.r.take W.layout.logBytecode) (pcSlots W.layout.tables))

/-- **The facts the link's checks read of the honest witness.** -/
structure LinkFacts (W : Witness) : Prop where
  layoutTables : W.layout.tables = tables
  chunks : Chunks.new (pointerWidth W.layout.logMemory W.layout.logBytecode
    (W.layout.tableRows.foldl (· + ·) 0)) = some W.chunks
  nRows : linkNRows W ≤ 30
  bytecode : W.layout.logBytecode ≤ W.chunks.width ∧
    W.layout.bytecode.length >>> bytecodeSlotBits = 2 ^ W.layout.logBytecode
  indexTabs : ∀ theta0 drawn, drawn.length = packedChallenges tables (linkNRows W) W.chunks.width →
    Tabs W.chunks.width
      (indexProds W (LinkChallenges.ofDraw tables (linkNRows W) W.chunks.width W.chunks.d theta0 drawn))
  index : ∀ theta0 drawn, drawn.length = packedChallenges tables (linkNRows W) W.chunks.width →
    let ch := LinkChallenges.ofDraw tables (linkNRows W) W.chunks.width W.chunks.d theta0 drawn
    linkEqAt ch.zeta 0 * (1 + ch.gammaState.getD 0 0 * 1 + ch.gammaState.getD 1 0 * 1) +
      linkEqAt ch.zeta (W.layout.tableRows.foldl (· + ·) 0) *
        (1 + ch.gammaState.getD 0 0 * gpow (2 ^ W.layout.logBytecode - 1) +
          ch.gammaState.getD 1 0 * 1) =
      cubeSum (2 ^ W.chunks.width) (indexProds W ch)
  rowStart : ∀ y x, HonestPre W y x →
    RowOK (roundCoefficients W.chunks.d).1 (linkRowStart W x) ∧
      x.index.value = rowClaim (linkRowStart W x)
  columns : ∀ y x, HonestPre W y x → ∀ chi : List E, chi.length = linkNRows W →
    let st := chi.foldl rowFold (linkRowStart W x)
    (linkColumns W x chi st).length = linkNPointers W.layout ∧
      Tabs (log2Ceil (linkColumns W x chi st).length) (linkColumnProds W x chi st) ∧
      (∀ cf ∈ (linkColumnProds W x chi st).terms,
        cf.2.size + 1 ≤ (roundCoefficients W.chunks.d).2) ∧
      rowClaim st = cubeSum (2 ^ log2Ceil (linkColumns W x chi st).length)
        (linkColumnProds W x chi st)
  message : ∀ y x, HonestPre W y x → ∀ chi qPoint : List E,
    (linkMessage W x chi qPoint (chi.foldl rowFold (linkRowStart W x))).length =
      linkNValues W.layout + kBits
  tail : ∀ y x, HonestPre W y x → ∀ chi qPoint : List E, chi.length = linkNRows W →
    qPoint.length = log2Ceil (linkNPointers W.layout) →
    let st := chi.foldl rowFold (linkRowStart W x)
    ∃ e, linkTail W.layout y (honestProgramSide W y) chi qPoint
        (qPoint.foldl Prods.fold (linkColumnProds W x chi st)).value
        (linkMessage W x chi qPoint st) = .ret e ∧ LinkOut W e

/-! ## The moves -/

theorem wins_samplePacked {B : ℕ} (n : ℕ) (cs : List Committed) :
    Wins B (fun a b g' cs' ↦ a = b ∧ a.length = n ∧ g' = false ∧ cs' = cs)
      (VerifierProgram.sampleChallengesPacked n) (Script.samplePackedS n) false cs :=
  fun ys hys ↦ ⟨rfl, hys, by simp, rfl⟩

theorem grindingBits_le_seventeen {n : ℕ} (hn : n ≤ 40) : grindingBits n ≤ 17 := by
  have key : ∀ n < 41, grindingBits n ≤ 17 := by decide
  exact key n (by omega)

/-- **The prefix wins**, the verifier's and the prover's values related (`HonestPre`). -/
theorem wins_linkPre {W : Witness} (hf : LinkFacts W) (cs : List Committed) :
    Wins 17 (fun y x g cs' ↦ HonestPre W y x ∧ g = false ∧ cs' = cs)
      (linkPre W.layout) (linkProvePre W) false cs := by
  have hc := Wire.Chunks.new_le hf.chunks
  have hw := hc.1
  unfold maxPointerWidth at hw
  have hnr := hf.nRows
  unfold linkPre linkProvePre
  rw [hf.layoutTables]
  refine wins_liftOption hf.chunks ?_
  refine LeanVM.Prover.Wins.bind' (Wins.grindBits (grindingBits_le_seventeen (by
    unfold linkNRows at hnr; simp only [bytecodeSlotBits]; omega)) cs) fun _ _ g1 cs1 h1 ↦ ?_
  obtain ⟨-, h1⟩ := h1
  subst cs1
  refine LeanVM.Prover.Wins.bind' (Wins.sampleE g1 cs) fun θ θ' g2 cs2 h2 ↦ ?_
  obtain ⟨rfl, rfl, h2⟩ := h2
  subst cs2
  refine LeanVM.Prover.Wins.bind' (wins_samplePacked _ cs) fun drawn drawn' g3 cs3 h3 ↦ ?_
  obtain ⟨rfl, hlen, rfl, h3⟩ := h3
  subst cs3
  have hidx := hf.index θ drawn hlen
  dsimp only at hidx
  have hterms : ∀ ch, ∀ cf ∈ (indexProds W ch).terms, cf.2.size + 1 ≤ 3 := by
    intro ch cf hcf
    simp only [indexProds, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hcf
    rcases hcf with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hwin := wins_prodsSumcheck (B := 17) 3 W.chunks.width (by norm_num) (by norm_num)
    (by unfold roundBits; exact grindingBits_le_seventeen (by simp))
    (indexProds W (LinkChallenges.ofDraw tables (linkNRows W) W.chunks.width W.chunks.d θ drawn))
    (hf.indexTabs θ drawn hlen) (hterms _) cs
  rw [← hidx] at hwin
  refine LeanVM.Prover.Wins.bind' hwin fun rc ri g4 cs4 h4 ↦ ?_
  obtain ⟨hr, hrl, hri, hv, rfl, h4⟩ := h4
  subst cs4
  obtain ⟨r, index⟩ := ri
  dsimp only at hr hrl hri hv ⊢
  refine LeanVM.Prover.Wins.bind' (Wins.sendE_readScalar _ cs) fun m1 _ g5 cs5 h5 ↦ ?_
  obtain ⟨rfl, rfl, h5⟩ := h5
  subst cs5
  refine LeanVM.Prover.Wins.bind' (wins_samplePacked 5 cs) fun fresh fresh' g6 cs6 h6 ↦ ?_
  obtain ⟨rfl, hfl, rfl, h6⟩ := h6
  subst cs6
  refine ⟨⟨rfl, hlen, rfl, hr, hrl, hri, hv, rfl, rfl, rfl, hfl⟩, rfl, rfl⟩

theorem roundCoefficients_le {d : ℕ} (hd : d ≤ 25) :
    (roundCoefficients d).1 ≤ 28 ∧ (roundCoefficients d).2 ≤ 28 ∧ 2 ≤ (roundCoefficients d).1 ∧
      2 ≤ (roundCoefficients d).2 := by
  simp only [roundCoefficients]
  omega

/-- **The honest link prover wins `verifyLink`**, from the facts, leaving what `LinkOut` lists. -/
theorem wins_linkProve {W : Witness} (hf : LinkFacts W) (cs : List Committed) :
    Wins 17 (fun a _ g cs' ↦ g = false ∧ cs' = cs ∧ LinkOut W a)
      (verifyLink computedSplit W.layout) (linkProve W) false cs := by
  have hd := (Wire.Chunks.new_le hf.chunks).2
  obtain ⟨hrc1, hrc2, hrc1', hrc2'⟩ := roundCoefficients_le hd
  rw [verifyLink_split, linkProve_eq]
  refine LeanVM.Prover.Wins.bind (fun y x g cs1 h ↦ ?_) _ _ _ _ (wins_linkPre hf cs)
  obtain ⟨hp, rfl, h1⟩ := h
  subst cs1
  -- the program's split
  have hreq : (y.r.take W.layout.logBytecode).length < 64 ∧
      W.layout.bytecode.length >>> bytecodeSlotBits = 2 ^ (y.r.take W.layout.logBytecode).length := by
    have hw := (Wire.Chunks.new_le hf.chunks).1
    unfold maxPointerWidth at hw
    have hb := hf.bytecode.1
    rw [List.length_take, hp.r, hp.rlen, min_eq_left hb]
    exact ⟨by omega, hf.bytecode.2⟩
  unfold computedSplit
  simp only [VerifierProgram.bind_eq, VerifierProgram.bind_assoc, VerifierProgram.pure_eq,
    VerifierProgram.ret_bind]
  refine wins_require hreq ?_
  unfold linkSuf
  rw [linkSufOf_eq]
  unfold linkProveSuf
  -- the row rounds
  obtain ⟨hok, hstart⟩ := hf.rowStart y x hp
  rw [hp.claim, hstart, hp.chunks]
  refine LeanVM.Prover.Wins.bind' (wins_rowSumcheck (B := 17) _ (linkNRows W) hrc1' (by omega)
    (by unfold roundBits; exact grindingBits_le_seventeen (by simp; omega)) _ hok cs)
    fun a s g2 cs2 h2 ↦ ?_
  obtain ⟨ha, hsl, hst, hval, rfl, h2⟩ := h2
  subst cs2
  obtain ⟨chi, st⟩ := s
  obtain ⟨chi', c1⟩ := a
  dsimp only at ha hsl hst hval ⊢
  subst chi'
  subst st
  -- the pointer-column rounds
  obtain ⟨hlen, htabs, hterms, hcol⟩ := hf.columns y x hp chi hsl
  rw [hval, hcol, ← hlen]
  refine LeanVM.Prover.Wins.bind' (wins_prodsSumcheck (B := 17) _ _ hrc2' (by omega)
    (by unfold roundBits; exact grindingBits_le_seventeen (by simp; omega)) _ htabs hterms cs)
    fun z q g3 cs3 h3 ↦ ?_
  obtain ⟨hz, hql, hqf, hzv, rfl, h3⟩ := h3
  subst cs3
  obtain ⟨qPoint, P⟩ := q
  obtain ⟨qPoint', c2⟩ := z
  dsimp only at hz hql hqf hzv ⊢
  subst qPoint'
  subst P
  -- the message and the terminal check
  refine ⟨rfl, hf.message y x hp chi qPoint, ?_⟩
  obtain ⟨e, he, hout⟩ := hf.tail y x hp chi qPoint hsl (by rw [hql, hlen])
  rw [hzv]
  show Wins 17 _ (linkTail W.layout y (honestProgramSide W y) chi qPoint _ _) _ false cs
  rw [he]
  exact ⟨rfl, rfl, hout⟩

/-- **The link wins**, from the facts: the form `LinkWins` asks. -/
theorem linkWins_of {W : Witness} (hf : LinkFacts W) (cs : List Committed) :
    Wins 17 (fun a b g cs' ↦ a = b ∧ g = false ∧ cs' = cs ∧ LinkOut W a)
      (verifyLink computedSplit W.layout)
      (Script.alongside (verifyLink computedSplit W.layout) (linkProve W)) false cs :=
  LeanVM.Prover.Wins.mono (fun _ _ _ _ h ↦ ⟨h.1.symm, h.2.choose_spec⟩) _ _ _ _
    (Wins.alongside _ _ _ _ (wins_linkProve hf cs))

/-- **`LinkWins`**, where every admitted execution's witness has the facts. -/
theorem linkWins_of_facts
    (h : ∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ : ℕ)
      (W : Witness), Admitted prog input t ρ W → LinkFacts W) : LinkWins :=
  fun prog input t ρ W hA cs ↦ linkWins_of (h prog input t ρ W hA) cs

end LeanVM.Prover.Complete

end
