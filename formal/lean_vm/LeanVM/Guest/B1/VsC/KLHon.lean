/-
  LeanVM.Guest.B1.VsC.KLHon

  A layer's honest run, split at its two pack dispatches (the archive's `LayerCHon`).
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerSpec
public import LeanVM.Guest.B1.KeccakGkr.PackChain
public import LeanVM.Guest.B1.KeccakGkr.InterfaceP

/-!
# A layer's honest run

`LayerData`: the carried capacity, the waiting word, the claim, and the transcript (the product,
the nonce, the pack rounds' and the position rounds' messages, `t`). From them, on the run
`verifyKeccakLayer` makes (`layerSq`, `layerPack`, `layerLocal`, `layerBeta`, `layerClaim`):
`run1`, `run2` the pack rounds of the two dispatches (`16⌊y/16⌋` rounds, then `y mod 16`), `r1`, `r2`
their returns; `pack_split`: the pack rounds are the two in turn.
-/

namespace LeanVM.Guest.B1.VerifySub.KL

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **A layer's honest data.** -/
structure LayerData where
  cap : List E
  w0 : E
  c : KeccakClaim
  product : List E
  nonce : E
  packMsgs : List (E × E)
  localMsgs : List (E × E × E)
  t : E × E × E

namespace LayerData

variable (D : LayerData) (first : ℕ)

/-- The sponge the layer starts from. -/
def s0 : Fs := plainStart first D.cap D.w0

/-- The pack rounds' count. -/
def y : ℕ := D.c.point.length

/-- `s`. -/
def sv : E := (layerSq (D.s0 first) D.product D.nonce).1

/-- The capacity after `s`. -/
def capS : List E := (layerSq (D.s0 first) D.product D.nonce).2.cap

/-- The first dispatch's rounds, `16⌊y/16⌋`. -/
def n1 : ℕ := krStep * (D.y / krStep)

/-- The first dispatch's rounds. -/
def run1 : (E × List E) × Fs :=
  packRunF (D.c.point.take D.n1) (D.packMsgs.take D.n1) (polyEval D.product (D.sv first))
    ⟨D.capS first, []⟩

/-- The second dispatch's rounds. -/
def run2 : (E × List E) × Fs :=
  packRunF (D.c.point.drop D.n1) (D.packMsgs.drop D.n1) (D.run1 first).1.1 (D.run1 first).2

/-- The first dispatch's returns, from the cursor `cur` past the product and the nonce. -/
def r1 (cur : E) : List E :=
  (D.run1 first).2.cap ++ [cur * gen ^ 48 * gen ^ (2 * D.n1), (D.run1 first).1.1]

/-- The second dispatch's returns. -/
def r2 (cur : E) : List E :=
  (D.run2 first).2.cap ++ [cur * gen ^ 48 * gen ^ (2 * D.n1) * gen ^ (2 * (D.y % krStep)),
    (D.run2 first).1.1]

/-- The pack rounds. -/
def pack : (E × List E) × Fs := layerPack D.c (D.s0 first) D.product D.nonce D.packMsgs

/-- The position rounds. -/
def loc : (List E × E) × Fs := layerLocal D.c (D.s0 first) D.product D.nonce D.packMsgs D.localMsgs

/-- `β` and the sponge after it. -/
def beta : E × Fs := layerBeta D.c (D.s0 first) D.product D.nonce D.packMsgs D.localMsgs D.t

/-- The next claim. -/
def next : KeccakClaim := layerClaim D.c (D.s0 first) D.product D.nonce D.packMsgs D.localMsgs D.t

/-- The pack challenges. -/
def chs : List E := (D.pack first).1.2

/-- The local point. -/
def locPt : List E := (D.loc first).1.1

/-- The words the layer reads. -/
def xs : List E :=
  D.product ++ [D.nonce] ++ D.packMsgs.flatMap (fun m ↦ [m.1, m.2]) ++
    D.localMsgs.flatMap (fun m ↦ [m.1, m.2.1, m.2.2]) ++ [D.t.1, D.t.2.1, D.t.2.2]

/-- The next claim's record, its point, lanes, local point and flips at `pt`, `lp`, `lc`, `fl`. -/
def outW (pt lp lc fl : E) : List E :=
  [(D.next first).value, sumE (D.next first).mu, pt, lp, lc, fl] ++ (D.next first).mu

/-- The returns. -/
def rets (cur : E) : List E := (D.beta first).2.cap ++ [cur * gen ^ (48 + 2 * D.y + 36)]

end LayerData

/-! ## The run's states -/

theorem packRunF_cap : ∀ (rs : List E) (ms : List (E × E)) (v : E) (s : Fs),
    s.cap.length = 5 → s.pend = [] →
    (packRunF rs ms v s).2.cap.length = 5 ∧ (packRunF rs ms v s).2.pend = []
  | r :: rs, (g1, g2) :: ms, v, s, _, _ => by
    simp only [packRunF]
    exact packRunF_cap rs ms _ _ (by simp [Fs.squeeze, capOf]) rfl
  | [], _, _, _, h1, h3 => by simp only [packRunF]; exact ⟨h1, h3⟩
  | _ :: _, [], _, _, h1, h3 => by simp only [packRunF]; exact ⟨h1, h3⟩

theorem fs_eta {s : Fs} (h : s.pend = []) : s = ⟨s.cap, []⟩ := by
  cases s; simp_all

namespace LayerData

variable {D : LayerData} {first : ℕ}

theorem capS_ok : (D.capS first).length = 5 := by
  unfold capS layerSq Fs.grindSqueeze
  split <;> simp [Fs.squeeze, capOf]

theorem n1_le : D.n1 ≤ D.y := by unfold n1 krStep; omega

theorem run1_state :
    (D.run1 first).2 = ⟨(D.run1 first).2.cap, []⟩ ∧ (D.run1 first).2.cap.length = 5 := by
  obtain ⟨h1, h2⟩ := packRunF_cap (D.c.point.take D.n1) (D.packMsgs.take D.n1)
    (polyEval D.product (D.sv first)) ⟨D.capS first, []⟩ capS_ok rfl
  exact ⟨fs_eta h2, h1⟩

theorem run2_state :
    (D.run2 first).2 = ⟨(D.run2 first).2.cap, []⟩ ∧ (D.run2 first).2.cap.length = 5 := by
  obtain ⟨h1, h2⟩ := packRunF_cap (D.c.point.drop D.n1) (D.packMsgs.drop D.n1)
    (D.run1 first).1.1 (D.run1 first).2 run1_state.2 (by rw [run1_state.1])
  exact ⟨fs_eta h2, h1⟩

/-- **The pack rounds are the two dispatches' in turn.** -/
theorem pack_split (hpm : D.packMsgs.length = D.y)
    (hsq : layerSq (D.s0 first) D.product D.nonce = (D.sv first, ⟨D.capS first, []⟩)) :
    D.pack first = (((D.run2 first).1.1, (D.run1 first).1.2 ++ (D.run2 first).1.2),
      (D.run2 first).2) := by
  have hl : (D.packMsgs.take D.n1).length = (D.c.point.take D.n1).length := by
    simp only [List.length_take, hpm]; rfl
  unfold pack layerPack
  rw [show (layerSq (D.s0 first) D.product D.nonce).1 = D.sv first by rw [hsq],
    show (layerSq (D.s0 first) D.product D.nonce).2 = ⟨D.capS first, []⟩ by rw [hsq],
    ← List.take_append_drop D.n1 D.c.point, ← List.take_append_drop D.n1 D.packMsgs,
    packRunF_append _ _ _ _ _ _ hl]
  rfl

theorem chs_length (hpm : D.packMsgs.length = D.y) :
    (D.chs first).length = D.y := by
  unfold chs pack layerPack
  rw [packRunF_chs_length _ _ _ _ (by rw [hpm]; rfl)]
  rfl

end LayerData

end
end LeanVM.Guest.B1.VerifySub.KL
