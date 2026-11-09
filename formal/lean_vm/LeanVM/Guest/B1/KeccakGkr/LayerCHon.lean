/-
  LeanVM.Guest.B1.KeccakGkr.LayerCHon

  A layer's honest run: the transcript it reads, the pack rounds' records, the next claim's
  record and buffers, and the returns.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerW

/-!
# A layer's honest run

`LayerData`: the carried capacity, the waiting word, the claim, and the transcript (the product,
the pack rounds' and the position rounds' messages, `t`). From them, on the run
`verifyKeccakLayer` makes (`layerSq`, `layerPack`, `layerLocal`, `layerBeta`, `layerClaim`):

* `run k`: the first `k` pack rounds (`packRunF`); `recWords cur`: the round records' buffer,
  field `f` of record `j` at `16 f + j`, record `j` the state after `8j` rounds for
  `j ≤ ⌊y/8⌋` (the eight-round loop), then one round a record (the remainder loop) (`recK`);
* `chs`, `locPt`, `beta`, `next`: the pack challenges, the local point, `β`, the next claim;
* `outW`: the next claim's record (its pointers given); `rets cur`: the returns.

`run_cap`: every state of the run has five canonical capacity cells and nothing waiting.
`run_add`: more rounds continue the run (`cont`); `eqChain_of_packRunF`: rounds from a state with
nothing waiting chain by `eqRound`. `run_chs`: the challenges so far are a prefix of `chs`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **A layer's honest data**: the carried capacity, the waiting word, the claim, the
transcript. -/
structure LayerData where
  cap : List E
  w0 : E
  c : KeccakClaim
  product : List E
  packMsgs : List (E × E)
  localMsgs : List (E × E × E)
  t : E × E × E

namespace LayerData

variable (D : LayerData) (first : ℕ)

/-- The sponge the layer starts from. -/
def s0 : Fs := plainStart first D.cap D.w0

/-- The claim's number of coordinates. -/
def y : ℕ := D.c.point.length

/-- `s`. -/
def sv : E := (layerSq (D.s0 first) D.product).1

/-- The capacity after `s`. -/
def capS : List E := (layerSq (D.s0 first) D.product).2.cap

/-- The first `k` pack rounds. -/
def run (k : ℕ) : (E × E × List E) × Fs :=
  packRunF (D.c.point.take k) (D.packMsgs.take k) (polyEval D.product (D.sv first)) 1
    ⟨D.capS first, []⟩

/-- The rounds record `j` follows: eight a record up to `⌊y/8⌋`, then one. -/
def recK (j : ℕ) : ℕ := if j ≤ D.y / 8 then 8 * j else min (8 * (D.y / 8) + (j - D.y / 8)) D.y

/-- Record `j`'s cursor. -/
def recCur (cur : E) (j : ℕ) : E := cur * gen ^ (47 + 2 * D.recK j)

/-- Field `f` of record `j`: the capacity, the cursor, the claim, the scale. -/
def recField (cur : E) (f j : ℕ) : E :=
  if f < 5 then ((D.run first (D.recK j)).2.cap).getD f 0
  else if f = 5 then D.recCur cur j
  else if f = 6 then (D.run first (D.recK j)).1.1 else (D.run first (D.recK j)).1.2.1

/-- The records' buffer. -/
def recWords (cur : E) : List E := (List.range 128).map fun i ↦
  if i % 16 ≤ D.y / 8 + D.y % 8 then D.recField first cur (i / 16) (i % 16) else 0

/-- The pack rounds. -/
def pack : (E × E × List E) × Fs := layerPack D.c (D.s0 first) D.product D.packMsgs

/-- The position rounds. -/
def loc : (List E × E) × Fs := layerLocal D.c (D.s0 first) D.product D.packMsgs D.localMsgs

/-- `β` and the sponge after it. -/
def beta : E × Fs := layerBeta D.c (D.s0 first) D.product D.packMsgs D.localMsgs D.t

/-- The next claim. -/
def next : KeccakClaim := layerClaim D.c (D.s0 first) D.product D.packMsgs D.localMsgs D.t

/-- The pack challenges. -/
def chs : List E := (D.pack first).1.2.2

/-- The local point. -/
def locPt : List E := (D.loc first).1.1

/-- The words the layer reads. -/
def xs : List E :=
  D.product ++ D.packMsgs.flatMap (fun m ↦ [m.1, m.2]) ++
    D.localMsgs.flatMap (fun m ↦ [m.1, m.2.1, m.2.2]) ++ [D.t.1, D.t.2.1, D.t.2.2]

/-- The next claim's record, its point, lanes, local point and flips at `pt`, `lp`, `lc`, `fl`. -/
def outW (pt lp lc fl : E) : List E :=
  [(D.next first).value, sumE (D.next first).mu, pt, lp, lc, fl] ++ (D.next first).mu

/-- The returns. -/
def rets (cur : E) : List E := (D.beta first).2.cap ++ [cur * gen ^ (47 + 2 * D.y + 36)]

end LayerData

/-! ## The run's states -/

theorem packRunF_cap : ∀ (rs : List E) (ms : List (E × E)) (v sc : E) (s : Fs),
    s.cap.length = 5 → AllCanonical s.cap → s.pend = [] →
    (packRunF rs ms v sc s).2.cap.length = 5 ∧ AllCanonical (packRunF rs ms v sc s).2.cap ∧
      (packRunF rs ms v sc s).2.pend = []
  | r :: rs, (g1, g2) :: ms, v, sc, s, _, _, _ => by
    simp only [packRunF]
    exact packRunF_cap rs ms _ _ _ (by simp [Fs.squeeze, capOf]) (squeeze_cap_canonical _) rfl
  | [], _, _, _, _, h1, h2, h3 => by simp only [packRunF]; exact ⟨h1, h2, h3⟩
  | _ :: _, [], _, _, _, h1, h2, h3 => by simp only [packRunF]; exact ⟨h1, h2, h3⟩

theorem packRunF_chs_length : ∀ (rs : List E) (ms : List (E × E)) (v sc : E) (s : Fs),
    ms.length = rs.length → (packRunF rs ms v sc s).1.2.2.length = rs.length
  | [], [], _, _, _, _ => rfl
  | r :: rs, (g1, g2) :: ms, v, sc, s, h => by
    simp only [packRunF, List.length_cons]
    rw [packRunF_chs_length rs ms _ _ _ (by simpa using h)]
  | [], _ :: _, _, _, _, h | _ :: _, [], _, _, _, h => by simp at h

namespace LayerData

variable {D : LayerData} {first : ℕ}

theorem capS_ok : (D.capS first).length = 5 ∧ AllCanonical (D.capS first) :=
  ⟨by simp [capS, layerSq, Fs.squeeze, capOf], squeeze_cap_canonical _⟩

theorem run_cap (k : ℕ) : ((D.run first k).2.cap.length = 5 ∧
    AllCanonical (D.run first k).2.cap) ∧ (D.run first k).2 = ⟨(D.run first k).2.cap, []⟩ := by
  obtain ⟨h1, h2, h3⟩ := packRunF_cap (D.c.point.take k) (D.packMsgs.take k)
    (polyEval D.product (D.sv first)) 1 ⟨D.capS first, []⟩ capS_ok.1 capS_ok.2 rfl
  refine ⟨⟨h1, h2⟩, ?_⟩
  unfold run
  generalize packRunF _ _ _ _ _ = q at h3 ⊢
  cases q with
  | mk a b => cases b; simp_all

theorem run_zero : D.run first 0 = ((polyEval D.product (D.sv first), 1, []), ⟨D.capS first, []⟩) := by
  simp [run, packRunF]

theorem run_full (hpm : D.packMsgs.length = D.y) : D.run first D.y = D.pack first := by
  simp only [run, pack, layerPack, y]
  rw [List.take_of_length_le le_rfl, List.take_of_length_le (by rw [hpm]; rfl)]
  rfl

/-- More rounds after a state with nothing waiting. -/
def cont (s : (E × E × List E) × Fs) (rs : List E) (ms : List (E × E)) : (E × E × List E) × Fs :=
  ((((packRunF rs ms s.1.1 s.1.2.1 ⟨s.2.cap, []⟩).1.1,
    (packRunF rs ms s.1.1 s.1.2.1 ⟨s.2.cap, []⟩).1.2.1,
    s.1.2.2 ++ (packRunF rs ms s.1.1 s.1.2.1 ⟨s.2.cap, []⟩).1.2.2)),
    (packRunF rs ms s.1.1 s.1.2.1 ⟨s.2.cap, []⟩).2)

theorem run_add (hpm : D.packMsgs.length = D.y) {k n : ℕ} (hk : k + n ≤ D.y) :
    D.run first (k + n) = cont (D.run first k) ((D.c.point.drop k).take n)
      ((D.packMsgs.drop k).take n) := by
  have hy : D.y = D.c.point.length := rfl
  have hA : (D.packMsgs.take k).length = (D.c.point.take k).length := by
    simp only [List.length_take]; omega
  have hs := (run_cap (D := D) (first := first) k).2
  unfold run at hs ⊢
  rw [List.take_add, List.take_add, packRunF_append _ _ _ _ _ _ _ hA]
  unfold cont
  generalize packRunF (D.c.point.take k) (D.packMsgs.take k) _ _ _ = q at hs ⊢
  obtain ⟨a, st⟩ := q
  cases st with
  | mk cap pend =>
    simp only [Fs.mk.injEq, true_and] at hs
    subst hs
    rfl

/-- **Rounds from a state with nothing waiting chain by `eqRound`.** -/
theorem eqChain_of_packRunF : ∀ (rs : List E) (ms : List (E × E)) (cl sc : E) (cap : List E),
    ms.length = rs.length →
    EqChain rs ms cl sc cap (packRunF rs ms cl sc ⟨cap, []⟩).1.2.2
      (packRunF rs ms cl sc ⟨cap, []⟩).1.1 (packRunF rs ms cl sc ⟨cap, []⟩).1.2.1
      (packRunF rs ms cl sc ⟨cap, []⟩).2.cap
  | [], [], _, _, _, _ => ⟨rfl, rfl, rfl, rfl⟩
  | r :: rs, (g1, g2) :: ms, cl, sc, cap, h => by
    rw [packRunF_eqRound]
    have hs : (eqRound ⟨cap, []⟩ g1 g2 r cl sc).2.2.2 =
        ⟨(eqRound ⟨cap, []⟩ g1 g2 r cl sc).2.2.2.cap, []⟩ := rfl
    refine ⟨_, _, _, _, _, by rw [← hs], rfl, ?_⟩
    rw [hs]
    exact eqChain_of_packRunF rs ms _ _ _ (by simpa using h)
  | [], _ :: _, _, _, _, h | _ :: _, [], _, _, _, h => by simp at h

/-- **The challenges so far** are a prefix of the pack challenges. -/
theorem run_chs (hpm : D.packMsgs.length = D.y) {k : ℕ} (hk : k ≤ D.y) {i : ℕ}
    (hi : i < (D.run first k).1.2.2.length) :
    ∃ h : i < (D.chs first).length, (D.chs first)[i] = (D.run first k).1.2.2[i] := by
  have hfull := run_full (D := D) (first := first) hpm
  have hy : D.y = D.c.point.length := rfl
  have hA : (D.packMsgs.take k).length = (D.c.point.take k).length := by
    simp only [List.length_take]; omega
  have e : D.chs first = (D.run first k).1.2.2 ++ (packRunF (D.c.point.drop k) (D.packMsgs.drop k)
      (D.run first k).1.1 (D.run first k).1.2.1 (D.run first k).2).1.2.2 := by
    rw [chs, ← hfull]
    unfold run
    rw [show D.c.point.take D.y = D.c.point.take k ++ D.c.point.drop k by
        rw [List.take_of_length_le (by omega), List.take_append_drop],
      show D.packMsgs.take D.y = D.packMsgs.take k ++ D.packMsgs.drop k by
        rw [List.take_of_length_le (by rw [hpm]), List.take_append_drop],
      packRunF_append _ _ _ _ _ _ _ hA]
  refine ⟨by rw [e, List.length_append]; omega, ?_⟩
  simp only [e]
  rw [List.getElem_append_left hi]

theorem run_chsD (hpm : D.packMsgs.length = D.y) {k : ℕ} (hk : k ≤ D.y) {i : ℕ} (hi : i < k) :
    (D.chs first).getD i 0 = (D.run first k).1.2.2.getD i 0 := by
  have hl : (D.run first k).1.2.2.length = k := by
    have hy : D.y = D.c.point.length := rfl
    exact (packRunF_chs_length _ _ _ _ _ (by simp only [List.length_take]; omega)).trans
      (by simp only [List.length_take]; omega)
  obtain ⟨h1, h2⟩ := run_chs (D := D) (first := first) hpm hk (i := i) (by omega)
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ (by omega), h2]

theorem run_chs_length (hpm : D.packMsgs.length = D.y) {k : ℕ} (hk : k ≤ D.y) :
    (D.run first k).1.2.2.length = k := by
  have hy : D.y = D.c.point.length := rfl
  exact (packRunF_chs_length _ _ _ _ _ (by simp only [List.length_take]; omega)).trans
    (by simp only [List.length_take]; omega)

end LayerData

namespace LayerData
variable {D : LayerData} {first : ℕ}

theorem chs_length (hpm : D.packMsgs.length = D.y) : (D.chs first).length = D.y := by
  rw [chs, ← run_full hpm]; exact run_chs_length hpm le_rfl

end LayerData
end
end LeanVM.Guest.B1.VerifySub
