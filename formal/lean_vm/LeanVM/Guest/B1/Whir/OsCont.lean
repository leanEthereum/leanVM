/-
  LeanVM.Guest.B1.Whir.OsCont

  `open_stacked`'s buffers' honest words, from a run's data, and the run's values from them.
-/

module

public import LeanVM.Guest.B1.Whir.OsLayout
public import LeanVM.Guest.B1.Whir.OsAllocs
public import LeanVM.Guest.B1.Whir.SqAt

/-!
# The buffers' words (TRIAGE #36)

From a run's data `OsData` (the words read, the chain state, the claim, the root, the openings,
each level's data, the tail's), each buffer's honest words: the caps and flags the openings fill
(`OsCap`), the final message, the levels' roots, the fold challenges, the levels' scalars and
query weights, the decoded positions, the out-of-domain points and claims, each level's squeeze
run and row weights, the tail's challenges, the point, the basis rows, the inner sums and the
chains. `osRunOf` is the run at the allocator's pointers, its values read back from those words.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public noncomputable section

/-- A run's data: the words read, the chain state, the claim, the root, the openings, each level's
data, the tail's state, challenges and chain state. -/
structure OsData where
  xs : List E
  cv : Digest
  target : E
  root : Digest
  os : List Opening
  Hs : List OsLvH
  w1t : WhirState
  chst : List E
  cv1t : Digest

instance : Inhabited OsLvP := ⟨⟨0, default, 0, ⟨0, [], [], []⟩, [], [], default⟩⟩

namespace OsData

variable (cfg : OsCfg) (d : OsData)

/-- Level `0`'s chain state. -/
def cv0 : Digest := obsCv (obsCv d.cv (d.xs.getD 0 0)) (d.xs.getD 1 0)

/-- Level `0`'s roots. -/
def roots0 : List (Digest × ℕ × ℕ) := [(d.root, (cfg.lv 0).depth, 2 ^ (cfg.lv 0).folds)]

/-- The levels. -/
def lvs : List OsLvP := osLvsList cfg d.xs 0 d.cv0 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) d.Hs

/-- Level `l`. -/
def lv (l : ℕ) : OsLvP := (d.lvs cfg).getD l default

/-- Level `l`'s chain state after its nonce. -/
def cv3 (l : ℕ) : Digest := osHCv3 cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1

/-- Level `l`'s batching challenge. -/
def lam (l : ℕ) : E := osHLam cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1

/-- Level `l`'s positions with their openings. -/
def qs (l : ℕ) : List (ℕ × Opening) := (osHQs cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1).zip (d.lv cfg l).osp

/-- Level `l`'s root. -/
def rt (l : ℕ) : Digest := ((d.lv cfg l).roots.getD l default).1

/-- Level `l`'s out-of-domain point. -/
def oodPt (l : ℕ) : List E := (sqAll (cfg.lv l).logCols (osHCv12 cfg l d.xs (d.lv cfg l).p (d.lv cfg l).H.cv1)).1

/-- Level `l`'s scalar. -/
def beta (l : ℕ) : E := if l = cfg.yrLevel then d.lam cfg l else d.lam cfg l * d.lam cfg l

/-- The tail's closing challenge. -/
def last : E := challengeOf (sqCv d.cv1t)

/-- The tail's challenges. -/
def tf : List E := d.chst ++ [d.last]

/-! ## The fixed buffers -/

def capsC : List E :=
  osSegC (4 * cfg.capLen) ((List.range cfg.levels.length).map fun l =>
    (4 * (cfg.lv l).capOff, osCapCells (cfg.lv l).depth (cfg.lv l).capDepth (d.qs cfg l)))

def flagsC : List E :=
  osSegC cfg.capLen ((List.range cfg.levels.length).map fun l =>
    ((cfg.lv l).capOff, osCapFlags (cfg.lv l).depth (cfg.lv l).capDepth (d.qs cfg l)))

def fmsgC : List E := osHMs cfg cfg.yrLevel d.xs (d.lv cfg cfg.yrLevel).p

def rootsC : List E :=
  osSegC (2 * cfg.levels.length) ((List.range cfg.levels.length).map fun l =>
    (2 * l, [(digestScalars (d.rt cfg l)).1, (digestScalars (d.rt cfg l)).2]))

/-- The fold challenges: the state's after the levels. -/
def fchC : List E := (osLvsEnd cfg d.xs 0 d.cv0 2 (osW0 d.target d.xs) (d.roots0 cfg) d.Hs).2.2.folds

def betasC : List E := (List.range cfg.levels.length).map (d.beta cfg)

def qwC : List E :=
  osSegC (cfg.levels.length * cfg.maxQ) ((List.range cfg.levels.length).map fun l =>
    (l * cfg.maxQ, (List.range (cfg.lv l).queries).map fun i => d.lam cfg l ^ i))

def qposC : List E :=
  osSegC cfg.posLen ((List.range cfg.levels.length).map fun l =>
    ((cfg.lv l).posOff, (List.range ((cfg.lv l).squeezes * (192 / (cfg.lv l).depth))).map fun i =>
      eOfNat (osPosOf (cfg.lv l).depth (d.cv3 cfg l) i)))

def oodzC : List E :=
  osSegC (cfg.levels.length * 22) ((List.range (cfg.levels.length - 1)).map fun l => ((l + 1) * 22, d.oodPt cfg l))

def oodC : List E :=
  osSegC (cfg.levels.length * 4) ((List.range (cfg.levels.length - 1)).map fun l =>
    ((l + 1) * 4, [d.lam cfg l, osHW cfg l d.xs (d.lv cfg l).p 2, osHW cfg l d.xs (d.lv cfg l).p 3,
      osHW cfg l d.xs (d.lv cfg l).p 4]))

/-- The pointers the decoders of level `l`'s loop entered at `p` store. -/
def qbpSeg (fs : String → ℕ) (cert : String → V → ℕ) (l p : ℕ) : List E :=
  (List.range ((cfg.lv l).squeezes * (192 / (cfg.lv l).depth))).map fun i =>
    ofK (Parameters.gpow (sqDecAt fs (cfg.lv l) (cfg.lv l).squeezes p (i / (192 / (cfg.lv l).depth)) +
      cert (cfg.lv l).decode (.n 3))) * gen ^ (i % (192 / (cfg.lv l).depth) * (cfg.lv l).depth)

/-- The decoders' pointers, level `l`'s loop entered at `ps l`. -/
def qbpC (fs : String → ℕ) (cert : String → V → ℕ) (ps : ℕ → ℕ) : List E :=
  osSegC cfg.posLen ((List.range cfg.levels.length).map fun l => ((cfg.lv l).posOff, qbpSeg cfg fs cert l (ps l)))

/-! ## The levels' buffers -/

def sqzC (l : ℕ) : List E :=
  (List.range ((cfg.lv l).squeezes + 1)).flatMap fun j =>
    [(digestScalars (sqAll j (d.cv3 cfg l)).2).1, (digestScalars (sqAll j (d.cv3 cfg l)).2).2]

def rewC (l : ℕ) : List E :=
  (List.range (2 ^ (cfg.lv l).folds)).map fun i =>
    (eqKernel (d.lv cfg l).H.chs).getD (orwSlot (cfg.lv l).folds (if l = 0 then 1 else 0) i) 0

/-! ## The tail's and the finish's buffers -/

def tchC : List E := d.tf ++ List.replicate (5 - cfg.yrLog) 0

/-- A source's word: the fold challenges' or the tail challenges'. -/
def srcVal (q : ℕ × ℕ) : E := if q.1 = osFch then (d.fchC cfg).getD q.2 0 else (d.tchC cfg).getD q.2 0

def ent (i : ℕ) : E :=
  match osPtSrc cfg.nFolds (cfg.levels.headD default).folds cfg.yrLog (OsRun.tch cfg) i with
  | some q => d.srcVal cfg q
  | none => 0

def ptC : List E := (List.range 42).map (d.ent cfg)

def cf (it : ℕ × (ℕ × ℕ) × ℕ) : E := d.srcVal cfg it.2.1

def baC : List E :=
  osSegC (cfg.levels.length * 22) ((List.range cfg.levels.length).map fun l =>
    (l * 22, (osBasisCoords cfg.yrLog (OsRun.tch cfg) l (cfg.lv l)).map fun it => 1 + d.cf cfg it))

def bbC : List E :=
  osSegC (cfg.levels.length * 22) ((List.range cfg.levels.length).map fun l =>
    (l * 22, (osBasisCoords cfg.yrLog (OsRun.tch cfg) l (cfg.lv l)).map fun it => d.cf cfg it * eOfNat it.2.2))

/-- Level `l`'s basis row's words. -/
def rowA (l t : ℕ) : E := (d.baC cfg).getD (l * 22 + t) 0
def rowB (l t : ℕ) : E := (d.bbC cfg).getD (l * 22 + t) 0

/-- Level `l`'s chain after `j` queries. -/
def chain (l j : ℕ) : E :=
  ∑ x ∈ Finset.range j, d.lam cfg l ^ x * resProd (d.rowA cfg l) (d.rowB cfg l) (cfg.lv l).vals
    ((d.qposC cfg).getD ((cfg.lv l).posOff + x) 0) (cfg.lv l).logCols

def chvC (l : ℕ) : List E := (List.range ((cfg.lv l).queries + 1)).map (d.chain cfg l)

/-- The inner sum before level `l`. -/
def inner (l : ℕ) : E := ∑ i ∈ Finset.range l, d.beta cfg i * d.chain cfg i (cfg.lv i).queries

def ichC : List E := (List.range (cfg.levels.length + 1)).map (d.inner cfg)

/-- The finish's values, its buffers' pointers from `b`. -/
def finD (b : ℕ) : OsFinD where
  yat := multilinearEval (d.fmsgC cfg) d.tf
  pt := osPtrAt cfg b (11 + 2 * cfg.levels.length + 1)
  ent := d.ent cfg
  ba := osPtrAt cfg b (11 + 2 * cfg.levels.length + 2)
  bb := osPtrAt cfg b (11 + 2 * cfg.levels.length + 3)
  cf := d.cf cfg
  ich := osPtrAt cfg b (11 + 2 * cfg.levels.length + 4)
  chv := fun l => osPtrAt cfg b (11 + 2 * cfg.levels.length + 5 + l)
  i0 := d.inner cfg
  b := d.beta cfg
  r := fun l => d.chain cfg l (cfg.lv l).queries
  sc := fun i => d.lam cfg (i - 1)
  z := fun i t => (d.oodzC cfg).getD (i * 22 + t) 0
  c := fun i t => d.srcVal cfg (osOodSrc (OsRun.tch cfg)
    (osPrevColsAt cfg.levels.tail (cfg.levels.headD default).logCols (i - 1) - cfg.yrLog)
    (cfg.levels.tail.getD (i - 1) default).foldsOff t)
  t := polyEval d.w1t.quad d.last
  ichN := d.inner cfg cfg.levels.length

/-- **The run at the allocator's pointers from `b`**, the cursor `cur`. -/
def runOf (cur : E) (b : ℕ) : OsRun where
  xs := d.xs
  cv := d.cv
  target := d.target
  root := d.root
  os := d.os
  Hs := d.Hs
  w1t := d.w1t
  chst := d.chst
  cv1t := d.cv1t
  D := d.finD cfg b
  P := osPtrsOf cfg b
  sqz := fun l => osPtrAt cfg b (11 + 2 * l)
  rew := fun l => osPtrAt cfg b (11 + 2 * l + 1)
  tchv := osPtrAt cfg b (11 + 2 * cfg.levels.length)
  cur := cur

theorem runOf_ptrs (cur : E) (b : ℕ) : OsPtrsFrom cfg b (d.runOf cfg cur b) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- **The buffers' honest words**, in allocation order, the decoders' pointers `Q`. -/
def ownQ (Q : List E) : List (List E) :=
  [d.capsC cfg, d.flagsC cfg, d.fmsgC cfg, d.rootsC cfg, d.fchC cfg, d.betasC cfg, d.qwC cfg, d.qposC cfg,
    Q, d.oodzC cfg, d.oodC cfg] ++
    (List.range cfg.levels.length).flatMap (fun l => [d.sqzC cfg l, d.rewC cfg l]) ++
    [d.tchC cfg, d.ptC cfg, d.baC cfg, d.bbC cfg, d.ichC cfg] ++
    (List.range cfg.levels.length).map (d.chvC cfg)

end OsData

end
end LeanVM.Guest.B1
