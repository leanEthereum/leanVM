/-
  LeanVM.Guest.B1.Tables.TerminalBody

  `check_opening_terminal`'s body as a generator, equal to the compiled core body by kernel
  evaluation, and its loop `__loop83`.
-/

module

public import LeanVM.Guest.B1.Tables.Flock

/-!
# `check_opening_terminal`'s body (TRIAGE #43)

`check_opening_terminal` (G:2020-2075, `Data.core14`, 2253 statements) is straight-line: the
prefix chains and the public input's chain (`tPre`), the 92 column selectors dispatched on their
logs (`selBlk`), the 112 claims (`claimBlk`, by the claim's point buffer: the bus point, the table
point, `q_flock`'s slots, the public input), the ring-switch rows (`tPostA`, `rinitBlk`,
`tPostB`), their sum (`rsBlk`) and the check (`tEnd`). `core14_body` checks the generator
against the data, `core142_body` the loop's.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The irregular segments -/

/-- The three prefix chains, the public input's chain by `__loop83` and its value (G:2023-2032). -/
def tPre : List Stmt :=
  [.atom (.hint (.alloc (.n 17) 35)),
    .atom (.const (.n 18) (word 1 0 0)),
    .call "eq_prefix_chain" [.n 17, .n 18, .n 0, .n 13, .n 3] [],
    .atom (.hint (.alloc (.n 19) 35)),
    .atom (.const (.n 20) (word 1 0 0)),
    .call "eq_prefix_chain" [.n 19, .n 20, .n 1, .n 13, .n 4] [],
    .atom (.hint (.alloc (.n 21) 35)),
    .atom (.const (.n 22) (word 1 0 0)),
    .atom (.const (.n 23) (word 256 0 0)),
    .atom (.mul (.n 24) (.n 13) (.n 23)),
    .call "eq_prefix_chain" [.n 21, .n 22, .n 1, .n 24, .n 6] [],
    .atom (.hint (.alloc (.n 25) 35)),
    .atom (.const (.n 26) (word 1 0 0)),
    .atom (.load (.n 26) (.n 25) 0),
    .atom (.const (.n 27) (word 1 0 0)),
    .atom (.add (.n 28) (.n 27) (.n 2)),
    .atom (.load (.n 29) (.n 13) 0),
    .atom (.add (.n 30) (.n 28) (.n 29)),
    .atom (.load (.n 30) (.n 25) 1),
    .atom (.const (.n 31) (word 2 0 0)),
    .atom (.add (.n 32) (.n 31) (.n 5)),
    .atom (.const (.n 33) (word 2 0 0)),
    .callIf (.n 32) "__loop83" [.n 33, .n 5, .n 25, .n 13],
    .atom (.mul (.n 34) (.n 25) (.n 5)),
    .atom (.load (.n 35) (.n 34) 0)]

/-- `q_flock`'s size checked, the ring-switch rows allocated (G:2057-2060). -/
def tPostA : List Stmt :=
  [.atom (.const (.n 1737) (word 256 0 0)),
    .atom (.mul (.n 1738) (.n 6) (.n 1737)),
    .atom (.load (.n 1739) (.n 10) 5),
    .atom (.assertEq (.n 1738) (.n 1739)),
    .atom (.const (.n 1740) (word 256 0 0)),
    .atom (.mul (.n 1741) (.n 6) (.n 1740)),
    .atom (.const (.n 1742) (word 2 0 0)),
    .atom (.mul (.n 1743) (.n 1741) (.n 1742)),
    .atom (.mul (.n 1744) (.n 1743) (.n 1743)),
    .atom (.mul (.n 1745) (.n 1744) (.n 1744)),
    .atom (.mul (.n 1746) (.n 1745) (.n 1745)),
    .atom (.mul (.n 1747) (.n 1746) (.n 1746)),
    .atom (.mul (.n 1748) (.n 1747) (.n 1747)),
    .atom (.mul (.n 1749) (.n 1748) (.n 1748)),
    .atom (.hint (.allocDyn (.n 1750) (.n 1749)))]

/-- `rs_eq_run` and the last row (G:2061-2062). -/
def tPostB : List Stmt :=
  [.atom (.const (.n 1815) (word 256 0 0)),
    .atom (.mul (.n 1816) (.n 6) (.n 1815)),
    .call "rs_eq_run" [.n 1750, .n 11, .n 13, .n 1816] [],
    .atom (.const (.n 1817) (word 256 0 0)),
    .atom (.mul (.n 1818) (.n 6) (.n 1817)),
    .atom (.mul (.n 1819) (.n 1818) (.n 1818)),
    .atom (.mul (.n 1820) (.n 1819) (.n 1819)),
    .atom (.mul (.n 1821) (.n 1820) (.n 1820)),
    .atom (.mul (.n 1822) (.n 1821) (.n 1821)),
    .atom (.mul (.n 1823) (.n 1822) (.n 1822)),
    .atom (.mul (.n 1824) (.n 1823) (.n 1823)),
    .atom (.mul (.n 1825) (.n 1750) (.n 1824))]

/-- The ring-switch term and the terminal's check (G:2066-2067). -/
def tEnd : List Stmt :=
  [.atom (.mul (.n 2081) (.n 2080) (.n 53)),
    .atom (.add (.n 2082) (.n 1736) (.n 2081)),
    .atom (.mul (.n 2083) (.n 2082) (.n 15)),
    .atom (.assertEq (.n 2083) (.n 16))]

/-! ## The column selectors -/

/-- `column_selector`'s 29 specializations, in dispatch order. -/
def csNames : List String :=
  ["column_selector__L0", "column_selector__L1", "column_selector__L2", "column_selector__L3",
    "column_selector__L4", "column_selector__L5", "column_selector__L6", "column_selector__L7",
    "column_selector__L8", "column_selector__L9", "column_selector__L10", "column_selector__L11",
    "column_selector__L12", "column_selector__L13", "column_selector__L14", "column_selector__L15",
    "column_selector__L16", "column_selector__L17", "column_selector__L18", "column_selector__L19",
    "column_selector__L20", "column_selector__L21", "column_selector__L22", "column_selector__L23",
    "column_selector__L24", "column_selector__L25", "column_selector__L26", "column_selector__L27",
    "column_selector__L28"]

/-- The value of committed column `c`'s selector. -/
def selV (c : ℕ) : ℕ := 38 + 3 * c

/-- Committed column `c`'s selector (G:2034-2037): its offset and log read, the selector
dispatched on the log. -/
def selBlk (c : ℕ) : List Stmt :=
  [.atom (.load (.n (36 + 3 * c)) (.n 9) c), .atom (.load (.n (37 + 3 * c)) (.n 10) c),
    .dispatch (.n (37 + 3 * c)) csNames [.n (36 + 3 * c), .n 13] [.n (selV c)]]

/-! ## The claims -/

/-- Claim `j`'s point buffer (`CLAIM_POINT_BUF`): `0` the bus point, `1` the table point, `2`
`q_flock`'s slots on the table point, `3` the public input. -/
def claimKind (j : ℕ) : ℕ :=
  if j < 5 then 0 else if j < 81 then 1 else if j < 99 then 2 else if j < 109 then 1 else 3

/-- Claim `j`'s committed column (`CLAIM_COMMITTED_COL`). -/
def claimCol (j : ℕ) : ℕ :=
  if j < 5 then j else if j < 81 then j + 1 else if j < 99 then 5 else if j < 109 then j - 17
  else j - 109

/-- The `q_flock` slot of claims `81 .. 98` (`CLAIM_QFLOCK_SLOT_BITS`, as integers). -/
def claimSlot (j : ℕ) : ℕ :=
  [10, 11, 12, 13, 14, 15, 16, 17, 4, 5, 6, 7, 0, 1, 2, 3, 18, 19].getD (j - 81) 0

/-- Claim `j`'s first value. -/
def claimV : List ℕ :=
  [312, 320, 328, 336, 344, 352, 360, 368, 376, 384, 392, 400, 408, 416, 424, 432, 440, 448, 456,
    464, 472, 480, 488, 496, 504, 512, 520, 528, 536, 544, 552, 560, 568, 576, 584, 592, 600, 608,
    616, 624, 632, 640, 648, 656, 664, 672, 680, 688, 696, 704, 712, 720, 728, 736, 744, 752, 760,
    768, 776, 784, 792, 800, 808, 816, 824, 832, 840, 848, 856, 864, 872, 880, 888, 896, 904, 912,
    920, 928, 936, 944, 952, 960, 998, 1034, 1072, 1108, 1144, 1178, 1218, 1256, 1296, 1334,
    1372, 1408, 1450, 1490, 1530, 1568, 1606, 1642, 1650, 1658, 1666, 1674, 1682, 1690, 1698,
    1706, 1714, 1722, 1727, 1732, 1737]

/-- The running sum before claim `j`. -/
def claimAcc (j : ℕ) : ℕ := if j = 0 then 14 else claimV.getD j 0 - 1

/-- One factor `1 + bit + point[t]` of a slot's equality, folded (`bit = 1` cancels the `1`),
times the product so far `prev`, from value `c`: the statements, the product's value, the next
value. -/
def qFac (t : ℕ) (bit : Bool) (prev : Option ℕ) (c : ℕ) : List Stmt × ℕ × ℕ :=
  let (f, val, c') : List Stmt × ℕ × ℕ :=
    if bit then ([.atom (.load (.n c) (.n 13) t)], c, c + 1)
    else ([.atom (.const (.n c) (word 1 0 0)), .atom (.load (.n (c + 1)) (.n 13) t),
      .atom (.add (.n (c + 2)) (.n c) (.n (c + 1)))], c + 2, c + 3)
  match prev with
  | none => (f, val, c')
  | some q => (f ++ [.atom (.mul (.n c') (.n q) (.n val))], c', c' + 1)

/-- The slot's eight factors from factor `t`, from value `c`. -/
def qFacs (slot : ℕ) : ℕ → Option ℕ → ℕ → List Stmt × ℕ × ℕ
  | 0, prev, c => ([], prev.getD 0, c)
  | n + 1, prev, c =>
    let t := 8 - (n + 1)
    let r := qFac t (slot.testBit t) prev c
    let s := qFacs slot n (some r.2.1) r.2.2
    (r.1 ++ s.1, s.2.1, s.2.2)

/-- Claim `j`, from value `v`, on the running sum `acc` (G:2039-2056). -/
def claimBlk (j : ℕ) : List Stmt :=
  let v := claimV.getD j 0
  let acc := claimAcc j
  let col := claimCol j
  if claimKind j = 3 then
    [.atom (.load (.n v) (.n 10) col), .atom (.assertEq (.n 5) (.n v)),
      .atom (.load (.n (v + 1)) (.n 8) j), .atom (.mul (.n (v + 2)) (.n (v + 1)) (.n 35)),
      .atom (.mul (.n (v + 3)) (.n (v + 2)) (.n (selV col))),
      .atom (.add (.n (v + 4)) (.n acc) (.n (v + 3)))]
  else if claimKind j = 2 then
    let q := qFacs (claimSlot j) 8 none (v + 1)
    let u := q.2.2
    .atom (.load (.n v) (.n 7) j) :: q.1 ++
      [.atom (.mul (.n u) (.n 21) (.n v)), .atom (.load (.n (u + 1)) (.n u) 0),
        .atom (.mul (.n (u + 2)) (.n q.2.1) (.n (u + 1))),
        .atom (.const (.n (u + 3)) (word 256 0 0)), .atom (.mul (.n (u + 4)) (.n v) (.n (u + 3))),
        .atom (.load (.n (u + 5)) (.n 10) 5), .atom (.assertEq (.n (u + 4)) (.n (u + 5))),
        .atom (.load (.n (u + 6)) (.n 8) j), .atom (.mul (.n (u + 7)) (.n (u + 6)) (.n (u + 2))),
        .atom (.mul (.n (u + 8)) (.n (u + 7)) (.n (selV 5))),
        .atom (.add (.n (u + 9)) (.n acc) (.n (u + 8)))]
  else
    [.atom (.load (.n v) (.n 7) j),
      .atom (.mul (.n (v + 1)) (.n (if claimKind j = 0 then 17 else 19)) (.n v)),
      .atom (.load (.n (v + 2)) (.n (v + 1)) 0), .atom (.load (.n (v + 3)) (.n 10) col),
      .atom (.assertEq (.n v) (.n (v + 3))), .atom (.load (.n (v + 4)) (.n 8) j),
      .atom (.mul (.n (v + 5)) (.n (v + 4)) (.n (v + 2))),
      .atom (.mul (.n (v + 6)) (.n (v + 5)) (.n (selV col))),
      .atom (.add (.n (v + 7)) (.n acc) (.n (v + 6)))]

/-- Each claim's last value is the next claim's running sum. -/
theorem claimAcc_succ : ∀ j < 112,
    (claimKind j = 3 → claimAcc (j + 1) = claimV.getD j 0 + 4) ∧
    (claimKind j = 0 ∨ claimKind j = 1 → claimAcc (j + 1) = claimV.getD j 0 + 7) ∧
    (claimKind j = 2 →
      claimAcc (j + 1) = (qFacs (claimSlot j) 8 none (claimV.getD j 0 + 1)).2.2 + 9) := by
  decide +kernel

/-! ## The ring switch -/

/-- Row 0 of the ring switch's chains, coordinate `k` (G:2059-2060). -/
def rinitBlk (k : ℕ) : List Stmt :=
  [.atom (.const (.n (1751 + k)) (word 1 0 0)), .atom (.load (.n (1751 + k)) (.n 1750) k)]

/-- Term `k` of `Σ c_k · row_k` (G:2063-2065). -/
def rsBlk (k : ℕ) : List Stmt :=
  if k = 0 then
    [.atom (.load (.n 1826) (.n 12) 0), .atom (.load (.n 1827) (.n 1825) 0),
      .atom (.mul (.n 1828) (.n 1826) (.n 1827))]
  else
    [.atom (.load (.n (1825 + 4 * k)) (.n 12) k), .atom (.load (.n (1826 + 4 * k)) (.n 1825) k),
      .atom (.mul (.n (1827 + 4 * k)) (.n (1825 + 4 * k)) (.n (1826 + 4 * k))),
      .atom (.add (.n (1828 + 4 * k)) (.n (if k = 1 then 1828 else 1824 + 4 * k))
        (.n (1827 + 4 * k)))]

/-! ## The body -/

/-- The segments of `check_opening_terminal`'s body before its `ret`. -/
def tSegs : List (List Stmt) :=
  [tPre, ((List.range 92).map selBlk).flatten, ((List.range 112).map claimBlk).flatten, tPostA,
    ((List.range 64).map rinitBlk).flatten, tPostB, ((List.range 64).map rsBlk).flatten, tEnd]

set_option maxRecDepth 100000 in
theorem core14_body : Fn.body Data.core14 = tSegs.flatten ++ [.ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem tSegs_noRet : ∀ s ∈ tSegs, Stmt.noRetList s = true := by decide +kernel

theorem find_check_opening_terminal :
    coreProgram.find? "check_opening_terminal" = some Data.core14 :=
  Program.find?_of_indexOf? (j := 14) (by decide +kernel) rfl

theorem core14_params : Fn.params Data.core14 =
    [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 12, .n 13,
      .n 14, .n 15, .n 16] := rfl

/-- **`check_opening_terminal`'s relation**: a valuation taking the parameters to the arguments,
every segment holding. -/
theorem check_opening_terminal_holds {rd : Reader} {args : List E}
    (h : coreProgram.Rel rd "check_opening_terminal" args []) :
    ∃ σ : Val, [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7),
        σ (.n 8), σ (.n 9), σ (.n 10), σ (.n 11), σ (.n 12), σ (.n 13), σ (.n 14), σ (.n 15),
        σ (.n 16)] = args ∧
      ∀ s ∈ tSegs, Stmt.HoldsList (coreProgram.Rel rd) rd σ s True fun rs => rs = [] := by
  rw [rel_iff_sem find_check_opening_terminal, core14_body, core14_params] at h
  obtain ⟨σ, hp, hb⟩ := h
  rw [holdsList_append, holdsList_flatten_noRet _ tSegs_noRet] at hb
  exact ⟨σ, hp, hb.1⟩

/-! ## `__loop83` -/

/-- `__loop83`'s body (G:2030-2031): `chain[x·g] = chain[x] · (1 + point[x])`. -/
def l83Body : List Stmt :=
  [.atom (.mul (.n 4) (.n 2) (.n 0)), .atom (.load (.n 5) (.n 4) 0),
    .atom (.const (.n 6) (word 1 0 0)), .atom (.mul (.n 7) (.n 3) (.n 0)),
    .atom (.load (.n 8) (.n 7) 0), .atom (.add (.n 9) (.n 6) (.n 8)),
    .atom (.mul (.n 10) (.n 5) (.n 9)), .atom (.mul (.n 11) (.n 2) (.n 0)),
    .atom (.load (.n 10) (.n 11) 1), .atom (.const (.n 12) (word 2 0 0)),
    .atom (.mul (.n 13) (.n 0) (.n 12)), .atom (.add (.n 14) (.n 13) (.n 1)),
    .atom (.const (.n 15) (word 2 0 0)), .atom (.mul (.n 16) (.n 0) (.n 15)),
    .callIf (.n 14) "__loop83" [.n 16, .n 1, .n 2, .n 3], .ret []]

theorem core142_body : Fn.body Data.core142 = l83Body := stmtsEqb_sound (by decide +kernel)

theorem find_loop83 : coreProgram.find? "__loop83" = some Data.core142 :=
  Program.find?_of_indexOf? (j := 142) (by decide +kernel) rfl

/-- `__loop83` at `x`: `chain[x·g] = chain[x] · (1 + point[x])`. -/
def L83Body (rd : Reader) (chain pt x : E) : Prop :=
  ∃ c p, LoadHolds rd (chain * x) 0 c ∧ LoadHolds rd (pt * x) 0 p ∧
    LoadHolds rd (chain * x) 1 (c * (1 + p))

theorem loop83_step (rd : Reader) (N chain pt : E) (d : ℕ) (x : E) :
    coreProgram.relN rd (d + 1) "__loop83" (x :: [N, chain, pt]) [] ↔
      L83Body rd chain pt x ∧ IsInK (x * gen + N) ∧
        (x * gen + N ≠ 0 → coreProgram.relN rd d "__loop83" (x * gen :: [N, chain, pt]) []) := by
  rw [relN_succ_iff find_loop83, show Fn.params Data.core142 = [.n 0, .n 1, .n 2, .n 3] from rfl,
    core142_body, l83Body]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, and_true,
    word_one, word_gen]
  constructor
  · rintro ⟨σ, hp, h4, l5, h6, h7, l8, h9, h10, h11, l10, h12, h13, h14, h15, h16, hK, hcall⟩
    simp only [List.cons.injEq] at hp
    obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hp
    refine ⟨⟨σ (.n 5), σ (.n 8), by rwa [h4] at l5, by rwa [h7] at l8, ?_⟩,
      by rwa [h14, h13, h12] at hK, fun hne => ?_⟩
    · rw [h11, h10, h9, h6] at l10; exact l10
    · have := hcall (by rwa [h14, h13, h12])
      rwa [h16, h15] at this
  · rintro ⟨⟨c, p, l5, l8, l10⟩, hK, hcall⟩
    refine ⟨setl (Val.ofArgs [x, N, chain, pt]) 4 [chain * x, c, 1, pt * x, p, 1 + p, c * (1 + p),
      chain * x, gen, x * gen, x * gen + N, gen, x * gen], ?_, ?_⟩
    · b1_look
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (try b1_look)
      exacts [l5, l8, l10, hK, hcall]

end
end LeanVM.Guest.B1
