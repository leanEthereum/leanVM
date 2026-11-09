import LeanVM.Prover.Fast.Copy
import Statement.Prover.Prove

/-!
# The statement's prover, compiled with `E`'s word-level arithmetic

The verifier's definitions (`Statement/LeanVmVerifier.lean`) and the prover's
(`Statement/Prover/`) that multiply in `E`, or call one that does, copied (`Copy.lean`),
callee-first: the verifier's first (its recursive ones, which the prover does not call in its hot
loops, are left as they are), then the prover's in rounds, each round after the hand-written
copies of the recursive definitions its callers wait for. A hand-written copy is the statement's
text with `E`'s product as `mulE` and its own name for the recursive call, proved equal by
induction and marked `@[csimp]`; the last round fails if a recursive definition is left
(`fast_copy_modules_complete`), so a prover that gains one fails the build here.

`leanvm-prove` imports this module: its call of `LeanVM.Prover.prove` compiles as
`LeanVM.Prover.prove.fast`, which is `prove` (`prove.fast_eq`, by `rfl`).
-/

open LeanVM.Parameters LeanVM.Prover.Fast

fast_copy_modules_final Statement.LeanVmVerifier

fast_copy_modules Statement.Prover

namespace LeanVM.Prover

open LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

/-- `addSlice`, copied. -/
def addSlice.fast (off : ℕ) (vals : Array E) (s : E) : ℕ → Array E → Array E
  | 0, acc => acc
  | n + 1, acc => addSlice.fast off vals s n (acc.modify (off + n) (· + mulE s (vals.getD n 0)))

@[csimp] theorem addSlice.fast_eq : @addSlice = @addSlice.fast := by
  funext off vals s n acc
  induction n generalizing acc with
  | zero => rfl
  | succ n ih => exact ih _

/-- `mulLineFrom`, copied. -/
def mulLineFrom.fast (a₀ a₁ : E) : E → List E → List E
  | prev, [] => [mulE a₁ prev]
  | prev, p :: ps => (mulE a₀ p + mulE a₁ prev) :: mulLineFrom.fast a₀ a₁ p ps

@[csimp] theorem mulLineFrom.fast_eq : @mulLineFrom = @mulLineFrom.fast := by
  funext a₀ a₁ prev ps
  induction ps generalizing prev with
  | nil => rfl
  | cons p ps ih => simp only [mulLineFrom, mulLineFrom.fast, ih, mulE]

/-- `treeLayers`, copied. -/
def treeLayers.fast : ℕ → Array E → List (Array E)
  | 0, t => [t]
  | n + 1, t => t :: treeLayers.fast n (mulPairsA t)

@[csimp] theorem treeLayers.fast_eq : @treeLayers = @treeLayers.fast := by
  funext n t
  induction n generalizing t with
  | zero => rfl
  | succ n ih => simp only [treeLayers, treeLayers.fast, ih]

/-- `foldRoundsA`, copied. -/
def foldRoundsA.fast : ℕ → ℕ → Array E → Array E → Script (Array E × Array E)
  | 0, _, f, w => return (f, w)
  | n + 1, s, f, w => do
    let (f, w) ← foldRoundA f w s
    foldRoundsA.fast n (s / 2) f w

@[csimp] theorem foldRoundsA.fast_eq : @foldRoundsA = @foldRoundsA.fast := by
  funext n s f w
  induction n generalizing s f w with
  | zero => rfl
  | succ n ih => simp only [foldRoundsA, foldRoundsA.fast, ih]

/-- `levelsA`, copied. -/
def levelsA.fast : ℕ → List Whir.Level → Array E → Array E → Script Unit
  | _, [], _, _ => return ()
  | mu, level :: rest, f, w => do
    let (p, w) ← foldRoundsA level.fold (2 ^ level.fold) f w
    let mu := mu - level.fold
    let depth := mu + level.logInvRate
    match rest with
    | [] => do
      Script.sendList p.toList
      Script.grindBits Whir.queryGrindingBits
      let _ ← sampleQueriesS depth level.queries level.queries
      let _ ← Script.queryS
      tailA mu w (p.extract 0 (2 ^ mu))
    | next :: _ => do
      let low := p.extract 0 (2 ^ mu)
      Script.commitS (levelWordFast (mu - next.fold) next.fold next.logInvRate low)
      Script.sendList (p.extract (2 ^ mu) p.size).toList
      let z₁ ← Script.sampleN mu
      let z₂ ← Script.sampleN mu
      let e₁ := eqTable z₁
      let e₂ := eqTable z₂
      Script.sendList [dotA low e₁, dotA low e₂]
      Script.grindBits Whir.queryGrindingBits
      let queries ← sampleQueriesS depth level.queries level.queries
      Script.grindBits Whir.batchGrindingBits
      let lam ← Script.sampleE
      let _ ← Script.queryS
      levelsA.fast mu rest low
        (glueTablesA lam w [e₁, e₂, queryTableA mu queries (powers lam queries.length)])

@[csimp] theorem levelsA.fast_eq : @levelsA = @levelsA.fast := by
  funext mu levels f w
  induction levels generalizing mu f w with
  | nil => rfl
  | cons level rest ih =>
    cases rest with
    | nil => rfl
    | cons next rest' =>
      unfold levelsA levelsA.fast
      simp only [ih]

namespace KeccakGkr

/-- `layersProve`, copied. -/
def layersProve.fast (col : ℕ → K) (P : ℕ) : List ℕ → KeccakClaim → Script KeccakClaim
  | [], claim => .ret claim
  | d :: ds, claim => (layerProve col P d claim).bind fun c ↦ layersProve.fast col P ds c

@[csimp] theorem layersProve.fast_eq : @layersProve = @layersProve.fast := by
  funext col P ds claim
  induction ds generalizing claim with
  | nil => rfl
  | cons d ds ih => simp only [layersProve, layersProve.fast, ih]

end KeccakGkr

end LeanVM.Prover

fast_copy_modules Statement.Prover

namespace LeanVM.Prover

open LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

/-- `gkrLayersA`, copied. -/
def gkrLayersA.fast (A₀ A₁ A₂ : List (Array E)) : ℕ → GkrState → Script GkrState
  | 0, s => .ret s
  | 1, s =>
    (gkrStepA (A₀.getD 0 #[]) (A₁.getD 0 #[]) (A₂.getD 0 #[]) 1 true s).bind
      (gkrLayersA.fast A₀ A₁ A₂ 0)
  | n + 2, s =>
    if n % 2 = 1 then
      (gkrStepA (A₀.getD (n + 1) #[]) (A₁.getD (n + 1) #[]) (A₂.getD (n + 1) #[]) 1 false
        s).bind
        (gkrLayersA.fast A₀ A₁ A₂ (n + 1))
    else
      (gkrStepA (A₀.getD n #[]) (A₁.getD n #[]) (A₂.getD n #[]) 2 (n = 0) s).bind
        (gkrLayersA.fast A₀ A₁ A₂ n)

@[csimp] theorem gkrLayersA.fast_eq : @gkrLayersA = @gkrLayersA.fast := by
  funext A₀ A₁ A₂ n s
  induction n using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => simp only [gkrLayersA, gkrLayersA.fast]
    | n + 2 =>
      have h1 : gkrLayersA A₀ A₁ A₂ (n + 1) = gkrLayersA.fast A₀ A₁ A₂ (n + 1) :=
        funext fun s ↦ ih (n + 1) (by omega) s
      have h0 : gkrLayersA A₀ A₁ A₂ n = gkrLayersA.fast A₀ A₁ A₂ n :=
        funext fun s ↦ ih n (by omega) s
      simp only [gkrLayersA, gkrLayersA.fast, h1, h0]

end LeanVM.Prover

fast_copy_modules Statement.Prover

namespace LeanVM.Prover

open LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile

section Run

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- `searchM`, copied. -/
def searchM.fast (bits : ℕ) (sp : Sponge) : ℕ → ℕ → m (Option E)
  | _, 0 => pure none
  | n, count + 1 => do
    let r ← absorbNonce F sp (nonceOf n)
    if powOk bits r.1 then pure (some (nonceOf n)) else searchM.fast bits sp (n + 1) count

@[csimp] theorem searchM.fast_eq : @searchM = @searchM.fast := by
  funext m _ F bits sp n count
  induction count generalizing n with
  | zero => rfl
  | succ count ih => simp only [searchM, searchM.fast, ih]

end Run

end LeanVM.Prover

fast_copy_modules Statement.Prover

namespace LeanVM.Prover

open LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile

section Run

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- `runFrom`, copied. -/
def runFrom.fast (fuel : ℕ) {α β : Type} :
    VerifierProgram α → Option (Script β) → Sponge → List Tree →
      m (Option (List E × List (List Opening)))
  | .ret _, _, _, _ => pure (some ([], []))
  | .fail, _, _, _ => pure (some ([], []))
  | .read k, S, sp, cs => do
    let sp' ← absorb F sp (Script.msgOf S) dsObserve
    let r ← runFrom.fast fuel (k (Script.msgOf S)) (Script.afterSend S) sp' cs
    pure (r.map fun t ↦ (Script.msgOf S :: t.1, t.2))
  | .sample k, S, sp, cs => do
    let r ← squeeze F sp
    runFrom.fast fuel (k r.1) (Script.afterSample r.1 S) r.2 cs
  | .grind bits k, S, sp, cs => do
    match ← findNonceM F bits sp fuel with
    | none => pure none
    | some n => do
      let r ← absorbNonce F sp n
      let t ← runFrom.fast fuel k (Script.afterGrind S) r.2 cs
      pure (t.map fun t ↦ (n :: t.1, t.2))
  | .commit ht _ k, S, sp, cs => do
    let tree ← buildTreeM F ht (Script.wordOf S)
    let sp0 ← absorb F sp (digestHalves tree.root).1 dsObserve
    let sp1 ← absorb F sp0 (digestHalves tree.root).2 dsObserve
    let r ← runFrom.fast fuel k (Script.afterCommit S) sp1 (cs ++ [tree])
    pure (r.map fun t ↦ ((digestHalves tree.root).1 :: (digestHalves tree.root).2 :: t.1, t.2))
  | .query i ps k, S, sp, cs => match cs[i]? with
    | none => pure (some ([], []))
    | some tree => do
      let rows := ps.map fun q ↦ tree.word (q % 2 ^ tree.height)
      let r ← runFrom.fast fuel (k rows) (Script.afterQuery rows S) sp cs
      pure (r.map fun t ↦ (t.1, ps.map tree.opening :: t.2))

@[csimp] theorem runFrom.fast_eq : @runFrom = @runFrom.fast := by
  funext m _ F fuel α β P S sp cs
  induction P generalizing S sp cs with
  | ret => rfl
  | fail => rfl
  | read k ih => simp only [runFrom, runFrom.fast, ih]
  | sample k ih => simp only [runFrom, runFrom.fast, ih]
  | grind bits k ih =>
    simp only [runFrom, runFrom.fast]
    congr 1
    funext o
    cases o <;> simp only [ih]
  | commit ht w k ih => simp only [runFrom, runFrom.fast, ih]
  | query i ps k ih =>
    simp only [runFrom, runFrom.fast]
    cases cs[i]? <;> simp only [ih]

end Run

end LeanVM.Prover

fast_copy_modules_complete Statement.Prover
