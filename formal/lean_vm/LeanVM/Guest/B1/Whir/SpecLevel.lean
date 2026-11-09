/-
  LeanVM.Guest.B1.Whir.SpecLevel

  One level of an accepting run of `whirOpenNZ`, read backwards: its honest words, openings and
  sponges, in the form the guest's blocks consume.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.SpecFold
public import LeanVM.Guest.B1.Whir.CCommit
public import LeanVM.Protocol.WithHash

/-!
# A level of the run, backwards

A level of an accepting run of `whirOpenNZ` from the sponge `F` (two scalars waiting), the
running state `ws`, the words and the openings is described by `SpLv`: the level's fold words
`xf`, its next commitment's words `ra rb y c0 c2` (a level that is not the last) or its final
message `ms` (the last), the proof of work's `nonce`, its openings `os` and its intro's words
`ic0 ic2`. Everything else is a function of these (`SpLv.F1` … `SpLv.Fend`):

* `tr = foldsTr folds F quad claim xf`: the sponge `F1` after the rounds, the challenges `chs`,
  the state `ws1`; the message log `ml` after them;
* the commitment (not the last level): `cF1 F1 ra rb` the sponge with the root's two scalars
  waiting, `oodZ` the out-of-domain point (`ml` squeezes), `cRest` its tail, `cF2` the sponge of
  the nonce's permutation; `F2 = ⟨capOf (cF2 …).perm, []⟩`;
* the last level: `F2 = ((F1.absorbAll ms).absorb nonce).squeeze.2`;
* the queries: `nsq` squeezes of `F2` give the positions `qs` (`queriesOf`), the batching
  challenge `lam` the next squeeze; the rows the openings' leaves, the enforced sum, the state
  `wsEnd` glued with `lam`; the next level's sponge `Fend = foldStep … ic0 ic2`;
* `words`: the level's stream words in order.

`SpLv.Ok`: the facts the run gives (every challenge nonzero, the root's digest, the proofs of
work, the openings passing `openOne` under the level's root at `qs`).

`level_nf_inv` (a level that is not the last), `level_fin_inv` (the last, with its tail rounds
and `w`) and `head_inv` (the first quadratic): an accepting run splits so.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The commitment's sponges -/

/-- The sponge with the root's two scalars waiting after the two already waiting. -/
def cF1 (F1 : Fs) (ra rb : E) : Fs := ⟨F1.cap, F1.pend ++ [(ra, dsObserve), (rb, dsObserve)]⟩

/-- The out-of-domain point's squeezes after its first. -/
def cRest (F1 : Fs) (ra rb : E) (m : ℕ) : List E × Fs :=
  (⟨capOf (cF1 F1 ra rb).perm, []⟩ : Fs).squeezeN (m - 1)

/-- The sponge the nonce's permutation reads. -/
def cF2 (F1 : Fs) (ra rb : E) (m : ℕ) (y c0 c2 nonce : E) : Fs :=
  ⟨(cRest F1 ra rb m).2.cap, [(y, dsObserve), (c0, dsObserve), (c2, dsObserve),
    (nonce, dsPowNonce)]⟩

/-- The out-of-domain point. -/
def oodZ (F1 : Fs) (ra rb : E) (m : ℕ) : List E :=
  challengeOf (cF1 F1 ra rb).perm :: (cRest F1 ra rb m).1

theorem commitF1_eq (σ : Val) (st : OsSt) (ra rb : E) :
    commitF1 σ st ra rb = cF1 (st.F σ) ra rb := rfl

theorem commitRest_eq (σ : Val) (st : OsSt) (ra rb : E) (m : ℕ) :
    commitRest σ st ra rb m = cRest (st.F σ) ra rb m := rfl

theorem commitF2_eq (σ : Val) (st : OsSt) (ra rb : E) (m : ℕ) (y c0 c2 nonce : E) :
    commitF2 σ st ra rb m y c0 c2 nonce = cF2 (st.F σ) ra rb m y c0 c2 nonce := rfl

theorem absorb_two {F1 : Fs} (h : F1.pend.length = 2) (ra rb : E) :
    (F1.absorb ra dsObserve).absorb rb dsObserve = cF1 F1 ra rb := by
  obtain ⟨cap, pend⟩ := F1
  simp only at h
  simp [Fs.absorb, cF1, h, rateScalars]

theorem squeezeN_cF1 {F1 : Fs} (ra rb : E) {m : ℕ} (hm : 1 ≤ m) :
    (cF1 F1 ra rb).squeezeN m = (oodZ F1 ra rb m, ⟨(cRest F1 ra rb m).2.cap, []⟩) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hp : (cRest F1 ra rb (k + 1)).2.pend = [] := squeezeN_pend_nil k _ rfl
  refine Prod.ext rfl ?_
  show (cRest F1 ra rb (k + 1)).2 = ⟨(cRest F1 ra rb (k + 1)).2.cap, []⟩
  exact fs_of_pend_nil hp

/-- Three words, then the nonce, after the out-of-domain point. -/
theorem absorb_four (cap : List E) (y c0 c2 nonce : E) :
    (((((⟨cap, []⟩ : Fs).absorb y dsObserve).absorb c0 dsObserve).absorb c2 dsObserve).absorb nonce
      dsPowNonce) =
      ⟨cap, [(y, dsObserve), (c0, dsObserve), (c2, dsObserve), (nonce, dsPowNonce)]⟩ := by
  simp [Fs.absorb, rateScalars]

theorem foldStep_pend (F : Fs) (d0 d2 : E) : (foldStep F d0 d2).pend.length = 2 := rfl

theorem foldsTr_pend : ∀ (n : ℕ) (F : Fs) (q : List E) (t : E) (xs : List E),
    F.pend.length = 2 → (foldsTr n F q t xs).1.pend.length = 2
  | 0, _, _, _, _, h => h
  | n + 1, _, _, _, _, _ => foldsTr_pend n _ _ _ _ (foldStep_pend _ _ _)

/-! ## A level -/

/-- **A level's honest data**: its configuration and start, and its words and openings. -/
structure SpLv where
  logN : ℕ
  index : ℕ
  level : Whir.Level
  fin : Bool
  ws : WhirStateT
  F : Fs
  xf : List E
  ra : E
  rb : E
  y : E
  c0 : E
  c2 : E
  ms : List E
  nonce : E
  os : List Opening
  ic0 : E
  ic2 : E
  /-- The root, height and width of the commitment the level's queries open. -/
  root : Digest
  height : ℕ
  width : ℕ

namespace SpLv

variable (L : SpLv)

/-- The rounds. -/
def tr : Fs × List E × List E × E := foldsTr L.level.fold L.F L.ws.quad L.ws.target L.xf
/-- The fold challenges. -/
def chs : List E := L.tr.2.1
/-- The sponge after the rounds. -/
def F1 : Fs := L.tr.1
/-- The state after the rounds. -/
def ws1 : WhirStateT :=
  { L.ws with target := L.tr.2.2.2, quad := L.tr.2.2.1, folds := L.ws.folds ++ L.chs }
/-- The message log after the rounds. -/
def ml : ℕ := L.logN - L.ws1.folds.length
/-- The sponge the queries start from. -/
def F2 : Fs :=
  if L.fin then ((L.F1.absorbAll L.ms dsObserve).absorb L.nonce dsPowNonce).squeeze.2
  else ⟨capOf (cF2 L.F1 L.ra L.rb L.ml L.y L.c0 L.c2 L.nonce).perm, []⟩
/-- The positions' bits. -/
def D : ℕ := L.ml + L.level.logInvRate
/-- The queries' squeezes. -/
def nsq : ℕ := ceilDiv L.level.queries (192 / L.D)
/-- The query positions. -/
def qs : List ℕ := queriesOf (192 / L.D) L.D (L.F2.squeezeN L.nsq).1 L.level.queries
/-- The batching challenge. -/
def lam : E := (L.F2.squeezeN L.nsq).2.squeeze.1
/-- The rows as the Spec reads them. -/
def rows : List (List E) :=
  if L.index = 0 then (L.os.map (·.leaf)).map fun row ↦ row.reverse.map ofK
  else (L.os.map (·.leaf)).map extRow
/-- The enforced sum. -/
def enforced : E := enforcedSum L.rows L.chs (powers L.lam L.qs.length)
/-- The claims waiting for the glue: the out-of-domain one (not the last level). -/
def pending : List (E × List E × (List E → E)) :=
  if L.fin then [] else [(L.y, [L.c0, L.y + L.c2, L.c2], fun x ↦ eqEval (oodZ L.F1 L.ra L.rb L.ml) x)]
/-- The state after the glue. -/
def wsEnd : WhirStateT :=
  glueT L.lam L.ws1 (L.pending ++ [(L.enforced, [L.ic0, L.enforced + L.ic2, L.ic2],
    fun x ↦ inducedWeight L.ml L.qs (powers L.lam L.qs.length) x)])
/-- The next level's sponge. -/
def Fend : Fs := foldStep (L.F2.squeezeN L.nsq).2 L.ic0 L.ic2
/-- The level's stream words, in order. -/
def words : List E :=
  L.xf ++ (if L.fin then L.ms ++ [L.nonce] else [L.ra, L.rb, L.y, L.c0, L.c2, L.nonce]) ++
    [L.ic0, L.ic2]

/-- **What an accepting run gives of a level**: `R` the commitments read before it, `d` its
next commitment's root (not the last level). -/
structure Ok (R : List (Digest × ℕ × ℕ)) (d : Digest) : Prop where
  xf : L.xf.length = 2 * L.level.fold
  chs : ∀ c ∈ L.chs, c ≠ 0
  digest : L.fin = false → digestFromHalves (L.ra, L.rb) = some d
  powNf : L.fin = false → powOk Whir.queryGrindingBits L.nonce
    (challengeOf (cF2 L.F1 L.ra L.rb L.ml L.y L.c0 L.c2 L.nonce).perm) = true
  ms : L.fin = true → L.ms.length = 2 ^ L.ml
  powFin : L.fin = true → powOk Whir.queryGrindingBits L.nonce
    ((L.F1.absorbAll L.ms dsObserve).absorb L.nonce dsPowNonce).squeeze.1 = true
  lam : L.lam ≠ 0
  root : R[L.index]? = some (L.root, L.height, L.width)
  osLen : L.os.length = L.qs.length
  opens : ∀ k (hk : k < L.qs.length) (ho : k < L.os.length),
    Id.run (Compile.openOneWithHash (m := Id) keccak256 L.root L.height L.width L.qs[k] L.os[k]) = true

theorem chs_length : L.chs.length = L.level.fold := foldsTr_chs_length _ _ _ _ _

theorem Fend_pend : L.Fend.pend.length = 2 := rfl

end SpLv

/-! ## The level's queries, backwards -/

/-- **A level's queries and intro, backwards**, from the sponge `F2` with nothing waiting. -/
theorem rest_inv {β : Type} {ml index : ℕ} {level : Whir.Level} {lf : List E} {ws1 : WhirStateT}
    {pending : List (E × List E × (List E → E))} {F2 : Fs} {xs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {r : β × FSt} (hd : 1 ≤ 192 / (ml + level.logInvRate))
    {K : WhirStateT → VerifierProgram β}
    (h : runF ((sampleQueries (ml + level.logInvRate) level.queries).bind fun queries ↦
      VerifierProgram.sampleChallenge.bind fun lam ↦ (VerifierProgram.require (lam ≠ 0)).bind
          fun _ ↦
        (VerifierProgram.queryOpenings index queries).bind fun words ↦
          (sumcheckRoundPoly 3 (enforcedSum (if index = 0 then words.map fun row ↦ row.reverse.map ofK
            else words.map extRow) lf (powers lam queries.length)) none).bind fun intro ↦
            K (glueT lam ws1 (pending ++ [(enforcedSum (if index = 0 then
              words.map fun row ↦ row.reverse.map ofK else words.map extRow) lf
              (powers lam queries.length), intro,
              fun x ↦ inducedWeight ml queries (powers lam queries.length) x)])))
      ⟨F2, xs, os, R⟩ = some r) :
    let nsq := ceilDiv level.queries (192 / (ml + level.logInvRate))
    let qs := queriesOf (192 / (ml + level.logInvRate)) (ml + level.logInvRate)
      (F2.squeezeN nsq).1 level.queries
    let lam := (F2.squeezeN nsq).2.squeeze.1
    ∃ (osL : List Opening) (osR : List (List Opening)) (ic0 ic2 : E) (xsR : List E) (root : Digest) (height width : ℕ),
      os = osL :: osR ∧ xs = ic0 :: ic2 :: xsR ∧ lam ≠ 0 ∧
      R[index]? = some (root, height, width) ∧ osL.length = qs.length ∧
      (∀ k (hk : k < qs.length) (ho : k < osL.length),
        Id.run (Compile.openOneWithHash (m := Id) keccak256 root height width qs[k] osL[k]) = true) ∧
      osL.map Opening.leafIndex = qs ∧
      runF (K (glueT lam ws1 (pending ++ [(enforcedSum (if index = 0 then
          (osL.map (·.leaf)).map fun row ↦ row.reverse.map ofK else (osL.map (·.leaf)).map extRow)
          lf (powers lam qs.length),
          [ic0, enforcedSum (if index = 0 then
            (osL.map (·.leaf)).map fun row ↦ row.reverse.map ofK else (osL.map (·.leaf)).map extRow)
            lf (powers lam qs.length) + ic2, ic2],
          fun x ↦ inducedWeight ml qs (powers lam qs.length) x)])))
        ⟨foldStep (F2.squeezeN nsq).2 ic0 ic2, xsR, osR, R⟩ = some r := by
  intro nsq qs lam
  rw [runF_sampleQueries_bind hd, runF_sampleE_bind] at h
  obtain ⟨hlam, h⟩ := runF_require_bind h
  obtain ⟨root, height, width, rows, osL, rest, hR, eos, ho, h⟩ := runF_queryP_bind h
  obtain ⟨hol, hok, hrows⟩ := openPhase_inv ho
  have hidx := (openPhase_some keccak256 ho).2.1
  rw [sumcheck3_bind] at h
  obtain ⟨ic0, xs1, hx1, h1⟩ := runF_readE_bind h
  obtain ⟨ic2, xs2, hx2, h2⟩ := runF_readE_bind h1
  subst hx1 hx2 hrows
  rw [squeeze_absorb_two] at h2
  exact ⟨osL, rest, ic0, ic2, xs2, root, height, width, eos, rfl, hlam, hR, hol, hok, hidx, h2⟩

/-! ## The last level's shape -/

/-- A level's queries and glue after its proof of work, refusing a zero `λ`. -/
def levelRestNZ (ml index : ℕ) (level : Whir.Level) (lf : List E) (s : WhirStateT)
    (pending : List (E × List E × (List E → E))) : VerifierProgram WhirStateT := do
  let queries ← sampleQueries (ml + level.logInvRate) level.queries
  let lam ← VerifierProgram.sampleChallenge
  VerifierProgram.require (lam ≠ 0)
  let queryWeights := powers lam queries.length
  let words ← VerifierProgram.queryOpenings index queries
  let rows : List (List E) :=
    if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
  let enforced := enforcedSum rows lf queryWeights
  let intro ← sumcheckRoundPoly 3 enforced none
  return glueT lam s (pending ++
    [(enforced, intro, fun x ↦ inducedWeight ml queries queryWeights x)])

/-- The last level's tail, refusing a zero challenge. -/
def levelTailNZ (lane ml : ℕ) (residual : List E) (s : WhirStateT) : VerifierProgram WhirEnd := do
  let (tailFolds, target) ← tailRoundsNZ ml s.target s.quad
  let point := s.folds ++ tailFolds
  let inner := s.glued.foldl
    (fun weight claim ↦
      weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds)) 0
  return ⟨point.drop lane ++ point.take lane, inner, multilinearEval residual tailFolds, target⟩

/-- **The last level**: its folds, its final message, its proof of work, its queries, its tail. -/
theorem whirLevelsOpenNZ_last (logN lane index : ℕ) (level : Whir.Level) (s : WhirStateT) :
    whirLevelsOpenNZ logN lane index [level] s = (do
      let (s, levelFolds) ← foldRoundsNZ level.fold s []
      let messageLog := logN - s.folds.length
      let residual ← VerifierProgram.readScalars (2 ^ messageLog)
      VerifierProgram.grindProofOfWork Whir.queryGrindingBits
      let s ← levelRestNZ messageLog index level levelFolds s []
      levelTailNZ lane messageLog residual s) := by
  rw [whirLevelsOpenNZ]
  simp only [levelRestNZ, levelTailNZ, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]

/-- `rest_inv` on `levelRestNZ`. -/
theorem rest_inv' {β : Type} {ml index : ℕ} {level : Whir.Level} {lf : List E} {ws1 : WhirStateT}
    {pending : List (E × List E × (List E → E))} {F2 : Fs} {xs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {r : β × FSt} (hd : 1 ≤ 192 / (ml + level.logInvRate))
    {K : WhirStateT → VerifierProgram β}
    (h : runF ((levelRestNZ ml index level lf ws1 pending).bind K) ⟨F2, xs, os, R⟩ = some r) :
    let nsq := ceilDiv level.queries (192 / (ml + level.logInvRate))
    let qs := queriesOf (192 / (ml + level.logInvRate)) (ml + level.logInvRate)
      (F2.squeezeN nsq).1 level.queries
    let lam := (F2.squeezeN nsq).2.squeeze.1
    ∃ (osL : List Opening) (osR : List (List Opening)) (ic0 ic2 : E) (xsR : List E) (root : Digest) (height width : ℕ),
      os = osL :: osR ∧ xs = ic0 :: ic2 :: xsR ∧ lam ≠ 0 ∧
      R[index]? = some (root, height, width) ∧ osL.length = qs.length ∧
      (∀ k (hk : k < qs.length) (ho : k < osL.length),
        Id.run (Compile.openOneWithHash (m := Id) keccak256 root height width qs[k] osL[k]) = true) ∧
      osL.map Opening.leafIndex = qs ∧
      runF (K (glueT lam ws1 (pending ++ [(enforcedSum (if index = 0 then
          (osL.map (·.leaf)).map fun row ↦ row.reverse.map ofK else (osL.map (·.leaf)).map extRow)
          lf (powers lam qs.length),
          [ic0, enforcedSum (if index = 0 then
            (osL.map (·.leaf)).map fun row ↦ row.reverse.map ofK else (osL.map (·.leaf)).map extRow)
            lf (powers lam qs.length) + ic2, ic2],
          fun x ↦ inducedWeight ml qs (powers lam qs.length) x)])))
        ⟨foldStep (F2.squeezeN nsq).2 ic0 ic2, xsR, osR, R⟩ = some r := by
  simp only [levelRestNZ, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind] at h
  exact rest_inv hd h

end
end LeanVM.Guest.B1.Whir
