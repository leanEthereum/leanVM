/-
  LeanVM.Guest.B1.VsC.LinkCallees

  The link callees' completeness statements left after vsc4, and `link_row_side` from
  `link_rounds`'.
-/

module

public import LeanVM.Guest.B1.VsC.Quiet
public import LeanVM.Guest.B1.VsC.Mono
public import LeanVM.Guest.B1.VsC.ChunkDC
public import LeanVM.Guest.B1.Link.RowSide
public import LeanVM.Guest.B1.Link.SqueezePacked
public import LeanVM.Guest.B1.Link.Terminal
import LeanVM.Guest.CoreRef

/-!
# The link's callees: what is left, and `link_row_side`

Each statement is a `CallCompletes` popping nothing, every node exact (`PostQuiet`), over the
soundness stream's records (`RSt`, `RoundChain`, `chainLast`, `pkSqueeze`, `Functionals`):

* `LinkRoundsComplete kd nt bits name`: `link_rounds__L{nt}_L{bits}` on the state
  `fs0..fs4, cursor, claim`, a chain `l` of `l.length < 64` rounds, the challenges at `point`,
  returns the state after them;
* `LinkRoundsLastComplete kd nt bits k name`: `link_rounds_last__L{nt}_L{bits}_L{k}` on the record
  `st` at `rp`, a chain of `k` rounds, returns `0`, the record after them at `out`;
* `LinkRowSideComplete kd d b1 b2 name`: `link_row_side__L{d}`, two chains, the rows' (`d + 1` tail
  coefficients, grind `b1`) then the pointer columns' (`6` rounds of `d`, grind `b2`);
* `SqueezePackedComplete kd`: `squeeze_packed` on the capacity and `g^p`, `p < 64`, the packed draw's
  cells at `out`, returns the capacity after it;
* `LinkTerminalComplete kd w name`: `link_terminal__L{w}` on the summand's inputs, the claim the
  summand plus `rest`, returns `0`.

`link_row_side_complete`: `link_row_side__L{d}` completes given its two `link_rounds`' completeness,
by `callCompletes_node` on `lrsBody` with the valuation fixed by the two chains. A chain whose first
record's capacity is not five cells long has no `RoundChain`, so that case is vacuous.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The statements -/

/-- **`link_rounds__L{nt}_L{bits}` completes**: a chain of `l.length < 64` rounds from the state
`fs0..fs4, cursor, claim`, its challenges at `point`, returns the state after it. -/
def LinkRoundsComplete (kd nt bits : ℕ) (name : String) : Prop :=
  ∀ (f0 f1 f2 f3 f4 cur cl point tabs : E) (l : List (E × RSt)), l.length < 64 →
    CallCompletes kd name [f0, f1, f2, f3, f4, cur, cl, point, gen ^ l.length, tabs]
      (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l).cells
      (fun rd ↦ (bits ≠ 0 → WinTabs rd tabs) ∧ RoundChain rd nt bits ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l ∧
        ReadsAt rd point (l.map Prod.fst))
      PostQuiet

/-- **`link_rounds_last__L{nt}_L{bits}_L{k}` completes**: on the record `st` at `rp`, a chain of
`k` rounds, its challenges at `pts`, the record after it at `out`, it returns `0`. -/
def LinkRoundsLastComplete (kd nt bits k : ℕ) (name : String) : Prop :=
  ∀ (rp out pts tabs : E) (st : RSt) (l : List (E × RSt)), st.cap.length = 5 → l.length = k →
    CallCompletes kd name [rp, out, pts, tabs] [0]
      (fun rd ↦ ReadsAt rd rp st.cells ∧ (bits ≠ 0 → WinTabs rd tabs) ∧ RoundChain rd nt bits st l ∧
        ReadsAt rd pts (l.map Prod.fst) ∧ ReadsAt rd out (chainLast st l).cells)
      PostQuiet

/-- **`link_row_side__L{d}` completes**: the rows' chain `l1` (`d + 1` tail coefficients, grind
`b1`), then the pointer columns' `l2` (`6` rounds of `d`, grind `b2`), the challenges at `chi` and
`qp`, return the state after both. -/
def LinkRowSideComplete (kd d b1 b2 : ℕ) (name : String) : Prop :=
  ∀ (f0 f1 f2 f3 f4 cur cl chi qp tabs : E) (l1 l2 : List (E × RSt)), l1.length < 64 → l2.length = 6 →
    CallCompletes kd name [f0, f1, f2, f3, f4, cur, cl, chi, qp, gen ^ l1.length, tabs]
      (chainLast (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1) l2).cells
      (fun rd ↦ WinTabs rd tabs ∧ RoundChain rd (d + 1) b1 ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1 ∧
        RoundChain rd d b2 (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1) l2 ∧
        ReadsAt rd chi (l1.map Prod.fst) ∧ ReadsAt rd qp (l2.map Prod.fst))
      PostQuiet

/-- **`squeeze_packed` completes**: `p < 64` permutations of the capacity alone, their cells at
`out`, return the capacity after them. -/
def SqueezePackedComplete (kd : ℕ) : Prop :=
  ∀ (f0 f1 f2 f3 f4 out : E) (p : ℕ), p < 64 →
    CallCompletes kd "squeeze_packed" [f0, f1, f2, f3, f4, out, gen ^ p] (pkSqueeze p [f0, f1, f2, f3, f4]).2
      (fun rd ↦ ReadsAt rd out (pkSqueeze p [f0, f1, f2, f3, f4]).1)
      PostQuiet

/-- **`link_terminal__L{w}` completes** at the chunking `Chunks.new w = some c`: on the index
point's words at `r`, the slices at `sent[80 ..]`, the shift coefficients at `shifts`, the chunks'
`ν` at `nu`, with the claim the summand plus `rest`, it returns `0`. -/
def LinkTerminalComplete (kd w : ℕ) (name : String) : Prop :=
  ∀ c, Chunks.new w = some c →
    ∀ (r sent coef shifts certW nu rest claim : E) (rs sl shs nus : List E), rs.length = c.width →
      sl.length = 64 → shs.length = 12 → nus.length = c.d →
      claim = (Functionals.new c rs 12).summand coef shs ((Functionals.new c rs 12).values c sl)
        (nus.map (certW * ·)) + rest →
      CallCompletes kd name [r, sent, coef, shifts, certW, nu, rest, claim] [0]
        (fun rd ↦ ReadsAt rd r rs ∧ (∀ k < 64, LoadHolds rd sent (80 + k) (sl.getD k 0)) ∧
          ReadsAt rd shifts shs ∧ ReadsAt rd nu nus)
        PostQuiet

/-! ## `link_row_side` -/

/-- `link_row_side`'s events on its one path. -/
def lrsEvs (rows cols : String) : List Ev :=
  [.call rows [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 9, .n 10]
      [.n 11, .n 12, .n 13, .n 14, .n 15, .n 16, .n 17],
    .atom (.const (.n 18) (word 64 0)),
    .call cols [.n 11, .n 12, .n 13, .n 14, .n 15, .n 16, .n 17, .n 8, .n 18, .n 10]
      [.n 19, .n 20, .n 21, .n 22, .n 23, .n 24, .n 25],
    .atom (.copy (.n 26) (.n 19)), .atom (.copy (.n 27) (.n 20)), .atom (.copy (.n 28) (.n 21)),
    .atom (.copy (.n 29) (.n 22)), .atom (.copy (.n 30) (.n 23)), .atom (.copy (.n 31) (.n 24)),
    .atom (.copy (.n 32) (.n 25))]

theorem walk_lrsBody (σ : Val) (rows cols : String) :
    walk σ (lrsBody rows cols) = .ret (lrsEvs rows cols) [.n 26, .n 27, .n 28, .n 29, .n 30, .n 31, .n 32] := by
  simp [lrsBody, lrsEvs, walk, walk1, Out.seq, Out.pre]

theorem calls_lrsEvs (rows cols : String) :
    calls (lrsEvs rows cols) =
      [⟨rows, [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 9, .n 10],
          [.n 11, .n 12, .n 13, .n 14, .n 15, .n 16, .n 17], true⟩,
        ⟨cols, [.n 11, .n 12, .n 13, .n 14, .n 15, .n 16, .n 17, .n 8, .n 18, .n 10],
          [.n 19, .n 20, .n 21, .n 22, .n 23, .n 24, .n 25], true⟩] := rfl

/-- `link_row_side`'s valuation: the arguments, the first chain's state, `g^6`, the second's twice. -/
def lrsVals (args c1 c2 : List E) : List E := args ++ c1 ++ [word 64 0] ++ c2 ++ c2

/-- **`link_row_side` completes from its two `link_rounds`'.** -/
theorem link_row_side_complete {kd d b1 b2 : ℕ} {rows cols name : String} {f : Fn}
    (hrows : LinkRoundsComplete kd (d + 1) b1 rows) (hcols : LinkRoundsComplete kd d b2 cols)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = (List.range 11).map V.n)
    (hbody : f.body = lrsBody rows cols) : LinkRowSideComplete kd d b1 b2 name := by
  intro f0 f1 f2 f3 f4 cur cl chi qp tabs l1 l2 hl1 hl2
  by_cases h5 : (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1).cap.length = 5
  swap
  · intro b
    exact ⟨0, [], wordsIn_nil b, fun rd _ _ hP ↦ absurd (chainLast_cap_length rfl hP.2.1) h5⟩
  by_cases h5' : (chainLast (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1) l2).cap.length = 5
  swap
  · intro b
    exact ⟨0, [], wordsIn_nil b, fun rd _ _ hP ↦ absurd (chainLast_cap_length h5 hP.2.2.1) h5'⟩
  obtain ⟨a1, a2, a3, a4, a5, u, v, hc1, hst1⟩ := cells_eq_seven h5
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, hc2, -⟩ := cells_eq_seven h5'
  rw [hc2]
  rw [hst1] at hc2
  let σ : Val := fun x ↦ (lrsVals [f0, f1, f2, f3, f4, cur, cl, chi, qp, gen ^ l1.length, tabs]
    [a1, a2, a3, a4, a5, u, v] [e1, e2, e3, e4, e5, e6, e7]).getD x.idx 0
  have hw : walk σ f.body = .ret (lrsEvs rows cols) [.n 26, .n 27, .n 28, .n 29, .n 30, .n 31, .n 32] := by
    rw [hbody]; exact walk_lrsBody σ rows cols
  have hq : ∀ a, Ev.atom a ∈ lrsEvs rows cols → atomQuiet a = true := by
    intro a ha
    simp only [lrsEvs, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, Ev.atom.injEq,
      false_or] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hx : ∀ rd, ∀ e ∈ lrsEvs rows cols, e.Exact rd σ := by
    intro rd e he
    simp only [lrsEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  have g6 : gen ^ l2.length = word 64 0 := by
    rw [hl2, show (64 : ℕ) = 2 ^ 6 from rfl, word_two_pow (by norm_num)]
  apply callCompletes_node
  intro b
  refine ⟨0, [], σ, f, lrsEvs rows cols, [.n 26, .n 27, .n 28, .n 29, .n 30, .n 31, .n 32],
    [PostQuiet, PostQuiet], wordsIn_nil b, hfind, by rw [hparams]; rfl, hw, rfl, ?_, ?_, ?_⟩
  · intro rd _ _ _ e he
    simp only [lrsEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · rw [calls_lrsEvs]
    simp only [KidsCompl, ↓reduceIte, List.headD_cons, List.tail_cons, and_true]
    refine ⟨?_, ?_⟩
    · have ea : [V.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 9, .n 10].map σ =
          [f0, f1, f2, f3, f4, cur, cl, chi, gen ^ l1.length, tabs] := rfl
      have er : [V.n 11, .n 12, .n 13, .n 14, .n 15, .n 16, .n 17].map σ =
          (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1).cells := by rw [hst1]; rfl
      rw [ea, er]
      exact (hrows f0 f1 f2 f3 f4 cur cl chi tabs l1 hl1).mono'
        fun rd ⟨_, hw', hc, _, hr, _⟩ ↦ ⟨fun _ ↦ hw', hc, hr⟩
    · have ea : [V.n 11, .n 12, .n 13, .n 14, .n 15, .n 16, .n 17, .n 8, .n 18, .n 10].map σ =
          [a1, a2, a3, a4, a5, u, v, qp, gen ^ l2.length, tabs] := by rw [g6]; rfl
      have er : [V.n 19, .n 20, .n 21, .n 22, .n 23, .n 24, .n 25].map σ =
          (chainLast ⟨[a1, a2, a3, a4, a5], u, v⟩ l2).cells := by rw [hc2]; rfl
      rw [ea, er]
      refine (hcols a1 a2 a3 a4 a5 u v qp tabs l2 (by omega)).mono'
        fun rd ⟨_, hw', _, hc, _, hr⟩ ↦ ⟨fun _ ↦ hw', ?_, hr⟩
      rwa [hst1] at hc
  · intro rd ts _ _ _ hv hp
    exact postQuiet_node hfind hw (hq) (hx rd) hv (by rw [calls_lrsEvs] at hp ⊢; exact hp) _

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem link_row_side_L6_complete (kd : ℕ) (h7 : LinkRoundsComplete kd 7 0 "link_rounds__L7_L0")
    (h6 : LinkRoundsComplete kd 6 0 "link_rounds__L6_L0") :
    LinkRowSideComplete kd 6 0 0 "link_row_side__L6" :=
  link_row_side_complete h7 h6 (coreProgram_find?_at (j := idx% «link_row_side__L6») rfl) rfl
    (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem link_row_side_L7_complete (kd : ℕ) (h8 : LinkRoundsComplete kd 8 1 "link_rounds__L8_L1")
    (h7 : LinkRoundsComplete kd 7 0 "link_rounds__L7_L0") :
    LinkRowSideComplete kd 7 1 0 "link_row_side__L7" :=
  link_row_side_complete h8 h7 (coreProgram_find?_at (j := idx% «link_row_side__L7») rfl) rfl
    (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem link_row_side_L8_complete (kd : ℕ) (h9 : LinkRoundsComplete kd 9 1 "link_rounds__L9_L1")
    (h8 : LinkRoundsComplete kd 8 1 "link_rounds__L8_L1") :
    LinkRowSideComplete kd 8 1 1 "link_row_side__L8" :=
  link_row_side_complete h9 h8 (coreProgram_find?_at (j := idx% «link_row_side__L8») rfl) rfl
    (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem link_row_side_L9_complete (kd : ℕ) (h10 : LinkRoundsComplete kd 10 1 "link_rounds__L10_L1")
    (h9 : LinkRoundsComplete kd 9 1 "link_rounds__L9_L1") :
    LinkRowSideComplete kd 9 1 1 "link_row_side__L9" :=
  link_row_side_complete h10 h9 (coreProgram_find?_at (j := idx% «link_row_side__L9») rfl) rfl
    (stmtsEqb_sound (by decide +kernel))


/-! ## The link's part of `verify_sub`'s callees -/

/-- **The link callees `verify_sub` enters, layout-free**: `link_rounds` at the index side's
`(1, 0)` and at the four row sides' two specializations, `squeeze_packed`, and
`link_terminal__L{w}`; `link_row_side` follows (`VsLinkCallees.row_side`). The route proves the
placed form, `VsLinkCalleesA` (`vsLinkCalleesA_complete`). -/
structure VsLinkCallees (kd : ℕ) : Prop where
  rounds_L1_L0 : LinkRoundsComplete kd 1 0 "link_rounds__L1_L0"
  rounds_L6_L0 : LinkRoundsComplete kd 6 0 "link_rounds__L6_L0"
  rounds_L7_L0 : LinkRoundsComplete kd 7 0 "link_rounds__L7_L0"
  rounds_L8_L1 : LinkRoundsComplete kd 8 1 "link_rounds__L8_L1"
  rounds_L9_L1 : LinkRoundsComplete kd 9 1 "link_rounds__L9_L1"
  rounds_L10_L1 : LinkRoundsComplete kd 10 1 "link_rounds__L10_L1"
  squeeze_packed : SqueezePackedComplete kd
  terminal : ∀ w, 19 ≤ w → w ≤ 24 → LinkTerminalComplete kd w (ltNames.getD (w - 19) "")

/-- The row side's grind bits at chunk count `d`: the rows', then the pointer columns'. -/
def lrsGrind (d : ℕ) : ℕ × ℕ := if d = 6 then (0, 0) else if d = 7 then (1, 0) else (1, 1)

/-- The row sides' names, `link_row_side__L{d}`, `6 ≤ d ≤ 9`. -/
def lrsNames : List String := ["link_row_side__L6", "link_row_side__L7", "link_row_side__L8", "link_row_side__L9"]

/-- **Every `link_row_side__L{d}` completes**, from the link callees' completeness. -/
theorem VsLinkCallees.row_side {kd : ℕ} (h : VsLinkCallees kd) :
    ∀ d, 6 ≤ d → d ≤ 9 → LinkRowSideComplete kd d (lrsGrind d).1 (lrsGrind d).2 (lrsNames.getD (d - 6) "") := by
  intro d h1 h2
  interval_cases d
  exacts [link_row_side_L6_complete kd h.rounds_L7_L0 h.rounds_L6_L0,
    link_row_side_L7_complete kd h.rounds_L8_L1 h.rounds_L7_L0,
    link_row_side_L8_complete kd h.rounds_L9_L1 h.rounds_L8_L1,
    link_row_side_L9_complete kd h.rounds_L10_L1 h.rounds_L9_L1]

end
end LeanVM.Guest.B1.VsC
