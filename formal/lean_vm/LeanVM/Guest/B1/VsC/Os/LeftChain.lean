/-
  LeanVM.Guest.B1.VsC.Os.LeftChain

  `open_stacked`'s levels' callees placed one after the other, their ends chosen before the
  node's valuation, and `query_win_ptrs`' words from them.
-/

module

public import LeanVM.Guest.B1.VsC.Os.LeftLpAt

/-!
# The levels' chain

`KidsAtF` places each callee at the aligned base of the cursor the previous one ends at. The
leaves end where they start (`osLeafEnd`); `level_positions` and `level_queries` end where their
`CallAtA` says. `query_win_ptrs`' words are frame addresses of the decoders `level_positions`
places (`osWq`), so they depend on the level's cursor, which follows the previous level's
`level_queries`. The node's words are fixed before its valuation (`OsKidsAt`'s `∃ wq`), so the
levels' ends are chosen first: `osChain_choose` picks a cursor per level from a step that exists
at every cursor, and `HonRun.osChain` the levels' cursors `cs` with each level's `level_positions`
and `level_queries` placed (`HonRun.LvStep`, by `HonRun.lpEntry_os` and `HonRun.lqEntry_os`), at
the helpers' honest values, independent of the valuation.

* `osOmName`, `osSpfName`: level `l`'s `opening_message` and `squeeze_point_from`;
* `osLeafEnd al f cur`: where a leaf `f` placed from `cur` ends;
* `osLpFp al c l cur`: level `l`'s `level_positions`' frame, the level entered at `cur`;
* `osLqFp al c l e`: its `level_queries`' frame, `level_positions` ending at `e`;
* `osBufCells c b`: the cells of `open_stacked`'s buffers at `b`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- **A chain of cursors from a step at every cursor.** -/
theorem osChain_choose {P : ℕ → ℕ → ℕ → Prop} (h : ∀ l cur, ∃ e, P l cur e) (start : ℕ) :
    ∃ cs : ℕ → ℕ, cs 0 = start ∧ ∀ l, P l (cs l) (cs (l + 1)) := by
  choose f hf using h
  exact ⟨fun l => Nat.rec start (fun l acc => f l acc) l, rfl, fun l => hf l _⟩

/-- Level `l`'s `opening_message`. -/
def osOmName (c : OsCfg) (l : ℕ) : String :=
  if l = c.yrLevel then "opening_message__L" ++ natStr (c.yrLen + (osLvA c l).folds) ++ "_L1"
  else "opening_message__L" ++ natStr (2 + (osLvA c l).folds) ++ "_L1"

/-- Level `l`'s `squeeze_point_from`. -/
def osSpfName (c : OsCfg) (l : ℕ) : String := "squeeze_point_from__L" ++ natStr (osLvA c l).logCols

/-- Where a leaf `f` placed from the cursor `cur` ends. -/
noncomputable def osLeafEnd (al : String → Bool) (f : String) (cur : ℕ) : ℕ := allocBase (al f) cur + B2C.fs f

/-- Level `l`'s `level_positions`' frame, the level entered at `cur`. -/
noncomputable def osLpFp (al : String → Bool) (c : OsCfg) (l cur : ℕ) : ℕ :=
  allocBase (al (osPositionsName (osLvA c l)))
    (if l = c.yrLevel then osLeafEnd al (osOmName c l) cur
      else osLeafEnd al (osSpfName c l) (osLeafEnd al (osOmName c l) cur))

/-- Level `l`'s `level_positions`' cursor, the level entered at `cur`. -/
noncomputable def osLpC (al : String → Bool) (c : OsCfg) (l cur : ℕ) : ℕ :=
  osLpFp al c l cur + B2C.fs (osPositionsName (osLvA c l))

/-- Level `l`'s `level_queries`' frame, `level_positions` ending at `e`. -/
noncomputable def osLqFp (al : String → Bool) (c : OsCfg) (l e : ℕ) : ℕ :=
  allocBase (al (osQueriesName c l (osLvA c l))) (if l = c.yrLevel then e else osLeafEnd al "is_zero" e)

/-- The cells of `open_stacked`'s buffers placed from `b`. -/
def osBufCells (c : OsCfg) (b i : ℕ) : Prop :=
  ∃ q ∈ (osSizesL c).zip (bases b (osSizesL c)), q.2 ≤ i ∧ i < q.2 + q.1

theorem osLeafEnd_le {al : String → Bool} {F : ℕ} (hF : ∀ f, B2C.fs f ≤ F) (f : String) (cur : ℕ) :
    osLeafEnd al f cur ≤ cur + 15 + F := by
  have := allocBase_le (al f) cur; have := hF f; unfold osLeafEnd; omega

theorem osLpFp_le {al : String → Bool} {F : ℕ} (hF : ∀ f, B2C.fs f ≤ F) (c : OsCfg) (l cur : ℕ) :
    osLpFp al c l cur ≤ cur + 45 + 2 * F := by
  unfold osLpFp
  have h1 := osLeafEnd_le (al := al) hF (osOmName c l) cur
  have h2 := osLeafEnd_le (al := al) hF (osSpfName c l) (osLeafEnd al (osOmName c l) cur)
  split
  · have := allocBase_le (al (osPositionsName (osLvA c l))) (osLeafEnd al (osOmName c l) cur); omega
  · have := allocBase_le (al (osPositionsName (osLvA c l)))
      (osLeafEnd al (osSpfName c l) (osLeafEnd al (osOmName c l) cur)); omega

theorem osLqFp_le {al : String → Bool} {F : ℕ} (hF : ∀ f, B2C.fs f ≤ F) (c : OsCfg) (l e : ℕ) :
    osLqFp al c l e ≤ e + 30 + F := by
  unfold osLqFp
  have h1 := osLeafEnd_le (al := al) hF "is_zero" e
  split
  · have := allocBase_le (al (osQueriesName c l (osLvA c l))) e; omega
  · have := allocBase_le (al (osQueriesName c l (osLvA c l))) (osLeafEnd al "is_zero" e); omega

/-- A level's end, from its pieces. -/
theorem lv_end_le {c0 fp1 e1 fp2 e S q F A B : ℕ} (h1 : fp1 ≤ c0 + 45 + 2 * F) (hA : A ≤ F)
    (h2 : e1 ≤ fp1 + A + (S + 1) * (3 * F + 64)) (h3 : fp2 ≤ e1 + 30 + F) (hB : B ≤ F)
    (h4 : e ≤ fp2 + B + (q + 2) * (3 * F + 2048)) : e ≤ c0 + (S + q + 6) * (3 * F + 2048) := by
  have h5 : (S + 1) * (3 * F + 64) ≤ (S + 1) * (3 * F + 2048) := Nat.mul_le_mul_left _ (by omega)
  have h6 : (S + q + 6) * (3 * F + 2048) =
      (S + 1) * (3 * F + 2048) + (q + 2) * (3 * F + 2048) + 3 * (3 * F + 2048) := by ring
  omega

theorem osBufCells_of {c : OsCfg} {b j i : ℕ} (hj : j < (osSizesL c).length) (hi : i < (osSizesL c).getD j 0) :
    osBufCells c b ((bases b (osSizesL c)).getD j 0 + i) :=
  ⟨_, mem_zip_bases hj, by omega, by omega⟩

/-- Level `l`'s decoders' runs, `level_positions` at the cursor `cc`. -/
def osWinCells (al : String → Bool) (c : OsCfg) (l cc i : ℕ) : Prop :=
  ∃ j < (osLvA c l).squeezes, osLpF al c l cc j ≤ i ∧
    i < osLpF al c l cc j + 128 / (osLvA c l).depth * qwN (osLvA c l).depth (osLvA c l).capDepth

end
end LeanVM.Guest.B1.VsC

namespace LeanVM.Guest.B1.Whir.HonRun

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1 LeanVM.Guest.B1.VsC
open LeanVM.Guest.Memory LeanVM.Guest.Complete LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}

set_option hygiene false in
local notation "CC" => osCfgR (μ - minOpenLog) (r - 1)

set_option hygiene false in
local notation "LV" => osLvA (osCfgR (μ - minOpenLog) (r - 1)) l

set_option hygiene false in
local notation "HH" => hR.osHonest (cur := cur) (tabs := tabs)

/-- `level_positions`' call at level `l` in the node, from the frame `fp` to `e`. -/
def LpAtOs (hR : HonRun μ r target S root xs os w cfg Ls) (cur tabs : E) (al : String → Bool) (kd b it : ℕ)
    (R : ℕ → Prop) (l fp e : ℕ) : Prop :=
  CallAtA B2C.fs al B2C.cert kd (osPositionsName (LV))
      (((HH).D l).w0 :: ((HH).D l).capL ++ [osPtrA CC b osIxQposA * gen ^ (LV).posOff,
        osPtrA CC b osIxQbpA * gen ^ (LV).posOff, ptrAt it, gen ^ (LV).squeezes])
      ((⟨((HH).D l).capL, []⟩ : Fs).squeezeN ((LV).squeezes - 1)).2.cap
      (fun i => R i ∨ osBufCells CC b i)
      (osWinCells al CC l (fp + B2C.fs (osPositionsName (LV))))
      (fun rd => ∀ j < (LV).squeezes, ReadsAt rd (ptrAt (osLpF al CC l (fp + B2C.fs (osPositionsName (LV))) j))
        (qwRunList (LV).depth (LV).capDepth (sqSample ((HH).D l).w0 ((HH).D l).capL j)))
      (fun rd => WinTabs rd (ptrAt it) ∧ OsMemA rd CC b (HH).own ∧
        ∀ k < (LV).squeezes * sqPer (LV), LoadHolds rd (osPtrA CC b osIxQbpA * gen ^ (LV).posOff) k
          (ptrAt (osLpF al CC l (fp + B2C.fs (osPositionsName (LV))) (k / sqPer (LV)) +
            k % sqPer (LV) * qwN (LV).depth (LV).capDepth)))
      PostQuiet (B2C.fs (osPositionsName (LV))) fp (fp + B2C.fs (osPositionsName (LV))) e

/-- `level_queries`' call at level `l` in the node, from the frame `fp` to `e`, its decoders' runs
`level_positions`' at the cursor `cc`. -/
def LqAtOs (hR : HonRun μ r target S root xs os w cfg Ls) (cur tabs : E) (al : String → Bool) (kd b : ℕ)
    (R : ℕ → Prop) (l cc fp e : ℕ) : Prop :=
  CallAtA B2C.fs al B2C.cert kd (osQueriesName CC l (LV))
      [if l = (CC).yrLevel then 0 else ((HH).D l).lam, if l = (CC).yrLevel then 0 else ((HH).D l).lamInv,
        osPtrA CC b osIxCoefsA * gen ^ (2 * (LV).foldsOff), osHsPtrA CC b l,
        osPtrA CC b osIxQposA * gen ^ (LV).posOff, osPtrA CC b osIxQbpA * gen ^ (LV).posOff]
      [(osRootA (HH).own l).1, (osRootA (HH).own l).2, ((HH).D l).batched,
        (if l = (CC).yrLevel then 0 else ((HH).D l).lam) ^ (LV).queries]
      (fun i => R i ∨ osBufCells CC b i ∨ osWinCells al CC l cc i)
      (fun _ => False) (fun _ => True)
      (fun rd => OsMemA rd CC b (HH).own ∧
        (∀ k < (LV).queries, LoadHolds rd (osPtrA CC b osIxQbpA * gen ^ (LV).posOff) k
          (ptrAt (lqWp (LV).depth (LV).capDepth (osLpF al CC l cc) k))) ∧
        ∀ j < (LV).squeezes, ReadsAt rd (ptrAt (osLpF al CC l cc j))
          (qwRunList (LV).depth (LV).capDepth (sqSample ((HH).D l).w0 ((HH).D l).capL j)))
      (fun rd t => SameStreams (t.pops coreProgram rd)
          (Hints.levelHints (l == 0) (LV).depth (os.getD l []).length (os.getD l [])) ∧
        t.Every (ExactAt coreProgram rd))
      (B2C.fs (osQueriesName CC l (LV))) fp (fp + B2C.fs (osQueriesName CC l (LV))) e

/-- **Level `l`'s placed helpers**, the level entered at `c0`, ending at `e`: `level_positions` at its
frame, ending at `e1`, then `level_queries` after `is_zero` (at a non-final level), ending at `e`. -/
def LvStep (hR : HonRun μ r target S root xs os w cfg Ls) (cur tabs : E) (al : String → Bool) (kd b it : ℕ)
    (R : ℕ → Prop) (l c0 e : ℕ) : Prop :=
  l < (CC).levels.length → ∃ e1, LpAtOs hR cur tabs al kd b it R l (osLpFp al CC l c0) e1 ∧
    LqAtOs hR cur tabs al kd b R l (osLpC al CC l c0) (osLqFp al CC l e1) e

variable (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

/-- **The levels' cursors, each level's end bounded**: `osChain` with every level within
`(squeezes + queries + 6)·(3F + 2048)` of its cursor when every frame is at most `F`. -/
theorem osChainB {cur tabs : E} (al : String → Bool) (kd : ℕ) (hkd : 7 ≤ kd) (b it : ℕ) (R : ℕ → Prop)
    (hRt : ∀ n < 2 ^ winTabBits, R (it + n)) (start : ℕ) :
    ∃ cs : ℕ → ℕ, cs 0 = start ∧ (∀ l, LvStep hR cur tabs al kd b it R l (cs l) (cs (l + 1))) ∧
      ∀ F, (∀ f, B2C.fs f ≤ F) → ∀ l, l < (CC).levels.length →
        cs (l + 1) ≤ cs l + ((LV).squeezes + (LV).queries + 6) * (3 * F + 2048) := by
  have hstep : ∀ l c0, ∃ e, LvStep hR cur tabs al kd b it R l c0 e ∧
      ∀ F, (∀ f, B2C.fs f ≤ F) → l < (CC).levels.length →
        e ≤ c0 + ((LV).squeezes + (LV).queries + 6) * (3 * F + 2048) := by
    intro l c0
    by_cases hl : l < (CC).levels.length
    · obtain ⟨e1, hb1, h1⟩ := hR.lpEntry_os (cur := cur) (tabs := tabs) (al := al) kd hkd hl b it
        (fun i => R i ∨ osBufCells CC b i)
        (fun j hj i hi => Or.inr (osBufCells_of hj hi)) (fun n hn => Or.inl (hRt n hn))
        (osLpFp al CC l c0) (osLpC al CC l c0) le_rfl
      obtain ⟨e, hb2, h2⟩ := hR.lqEntry_os (cur := cur) (tabs := tabs) (fs := B2C.fs) (al := al) (cert := B2C.cert) kd hl b
        (osLpF al CC l (osLpC al CC l c0)) (fun i => R i ∨ osBufCells CC b i ∨ osWinCells al CC l (osLpC al CC l c0) i)
        (fun j hj i hi => Or.inr (Or.inl (osBufCells_of hj hi)))
        (fun j hj i hi => Or.inr (Or.inr ⟨j, hj, by omega, by omega⟩))
        (osLqFp al CC l e1) _ le_rfl
      exact ⟨e, fun _ => ⟨e1, h1, h2⟩, fun F hF _ => lv_end_le (osLpFp_le hF CC l c0) (hF _) (hb1 F hF)
        (osLqFp_le hF CC l e1) (hF _) (hb2 F hF)⟩
    · exact ⟨0, fun h => absurd h hl, fun _ _ h => absurd h hl⟩
  obtain ⟨cs, h0, h⟩ := osChain_choose hstep start
  exact ⟨cs, h0, fun l => (h l).1, fun F hF l hl => (h l).2 F hF hl⟩

/-- **The levels' cursors, chosen before the node's valuation**: from `start`, each level's
`level_positions` and `level_queries` placed at the helpers' honest values. -/
theorem osChain {cur tabs : E} (al : String → Bool) (kd : ℕ) (hkd : 7 ≤ kd) (b it : ℕ) (R : ℕ → Prop)
    (hRt : ∀ n < 2 ^ winTabBits, R (it + n)) (start : ℕ) :
    ∃ cs : ℕ → ℕ, cs 0 = start ∧ ∀ l, LvStep hR cur tabs al kd b it R l (cs l) (cs (l + 1)) := by
  obtain ⟨cs, h0, h, -⟩ := hR.osChainB al kd hkd b it R hRt start (cur := cur) (tabs := tabs)
  exact ⟨cs, h0, h⟩

end
end LeanVM.Guest.B1.Whir.HonRun
