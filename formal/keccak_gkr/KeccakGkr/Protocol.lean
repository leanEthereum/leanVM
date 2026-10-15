import KeccakGkr.Start

/-!
# Keccak by GKR: the protocol

`protocol` is Protocol `keccak:protocol` of `doc/leanvm`, run from the main protocol's point
`(r_low, r_pack)`, which the verifier samples, and its output values `v`, which the prover sends:

1. the verifier samples `r_low`, `r_pack`; the prover sends `v`; the verifier samples `r_seg` and
   `r_lane`; the prover sends `c_st`, and the first claim is formed (`start`);
2. `D` layers (`layers`);
3. the opening of `c_st` (`outOpen`);
4. the opening of the last claim (`inOpen`).

The verifier ends holding two claims on the committed column (`Final`): its words at
`(r_low, r_pack, outPt)` are `outVal` (`OutEval`), and its bit slices at
`(inLow, inPack, inSlot)` are `slices` (`InEval`), what the commitment scheme opens.
-/

open Polynomial OracleComp
open scoped ENNReal

namespace KeccakGkr

variable {E : Type} [Field E] [CharP E 2] [Fintype E] [DecidableEq E] [SampleableType E]
variable (P : Perm) (D : ℕ) {n : ℕ} (Q : Column n) (x : E)

/-- The words' weights `x ^ z` are a basis of the lanes over the bits. -/
def WordBasis (x : E) : Prop :=
  ∀ d : Slice → ZMod 2, ∑ z, ι (d z) * x ^ z.val = 0 → ∀ z, d z = 0

/-! ## The phases -/

/-- The start's data before `c_st`. -/
abbrev Pre (E : Type) (n : ℕ) := (((Fin 4 → E) × (Fin n → E)) × (Lane → E)) × (Fin 6 → E)

/-- The public data, once `c_st` is sent. -/
def mkCtx (a : Pre E n) (cst : E) : Ctx E n := ⟨a.1.1.1, a.1.1.2, a.1.2, a.2, cst⟩

/-- Step 1: the main protocol's point and values, the segment and lane challenges, `c_st`, and
the first claim. -/
noncomputable def start : Phase Unit (Option (Ctx E n × Claim E n)) :=
  (Phase.sample (Fin 4 → E) fun _ rl => rl).comp <|
  (Phase.sample (Fin n → E) fun rl rp => (rl, rp)).comp <|
  (Phase.receive (Lane → E) (fun a v => (a, v)) fun a ℓ => outEval P D Q x ℓ a.1 a.2).comp <|
  (Phase.sample (Fin 6 → E) fun a ρ => (a, ρ)).comp <|
  Phase.receive E (fun a cst => some (mkCtx a cst, firstClaim x (mkCtx a cst)))
    fun a => outTotal Q x a.1.1.1 a.1.1.2 a.2

/-- After the opening of `c_st`: the public data, the last claim, the point and the value. -/
abbrev OutStage (E : Type) (n : ℕ) := Ctx E n × Claim E n × (Fin 6 → E) × E

/-- The summand of `keccak:eq:out`. -/
noncomputable def outSum : Summand E (Ctx E n × Claim E n) 6 2 where
  f cc := outSummand Q x cc.1.rl cc.1.rp cc.1.rseg cc.1.rlane
  deg _ := outSummand_deg Q x _ _ _ _

/-- The last check of the opening of `c_st`. -/
noncomputable def checkOut (st : Option ((Ctx E n × Claim E n) × (Fin 6 → E) × E)) (cout : E) :
    Option (OutStage E n) :=
  st.bind fun s => if s.2.2 = mle (outWeights s.1.1.rseg s.1.1.rlane) s.2.1 * cout
    then some (s.1.1, s.1.2, s.2.1, cout) else none

/-- Step 3: the opening of `c_st`. -/
noncomputable def outOpen : Phase (Option (Ctx E n × Claim E n)) (Option (OutStage E n)) :=
  (Phase.compute fun st => st.map fun cc => (cc, cc.1.cst)).comp <|
  (sumcheck 6 (outSum Q x)).comp <|
  Phase.receive E checkOut fun st =>
    match st with
    | some s => colEval Q x s.1.1.rl s.1.1.rp s.2.1
    | none => 0

/-- What the verifier ends with. -/
structure Final (E : Type) (n : ℕ) where
  ctx : Ctx E n
  outPt : Fin 6 → E
  outVal : E
  inLow : Fin 4 → E
  inPack : Fin n → E
  inSlot : Fin 6 → E
  slices : Slice → E

/-- The summand over the instance in `keccak:eq:in`. -/
noncomputable def inSum₁ : Summand E (OutStage E n) 4 2 where
  f s := inSummand₁ Q s.2.1.μ (Fin.init s.2.1.r) (s.2.1.r (Fin.last n)) s.2.1.w
  deg _ := inSummand₁_deg Q _ _ _ _

/-- The summand over the slot in `keccak:eq:in`. -/
noncomputable def inSum₂ : Summand E (OutStage E n × (Fin 4 → E)) 6 2 where
  f s := inSummand₂ Q s.1.2.1.μ (Fin.init s.1.2.1.r) (s.1.2.1.r (Fin.last n)) s.1.2.1.w s.2
  deg _ := inSummand₂_deg Q _ _ _ _ _

/-- The last check of the opening of the last claim. -/
noncomputable def checkIn (st : Option ((OutStage E n × (Fin 4 → E)) × (Fin 6 → E) × E))
    (sl : Slice → E) : Option (Final E n) :=
  st.bind fun s => if s.2.2 = mle s.1.1.2.1.μ s.1.2 * ∑ z,
      mle (inWeights (s.1.1.2.1.r (Fin.last n)) s.1.1.2.1.w z) s.2.1 * sl z
    then some ⟨s.1.1.1, s.1.1.2.2.1, s.1.1.2.2.2, s.1.2, Fin.init s.1.1.2.1.r, s.2.1, sl⟩
    else none

/-- Step 4: the opening of the last claim. -/
noncomputable def inOpen : Phase (Option (OutStage E n)) (Option (Final E n)) :=
  (Phase.compute fun st => st.map fun s => (s, s.2.1.c)).comp <|
  ((sumcheck 4 (inSum₁ (E := E) Q)).map fun st => st.map fun c => ((c.1, c.2.1), c.2.2)).comp <|
  (sumcheck 6 (inSum₂ (E := E) Q)).comp <|
  Phase.receive (Slice → E) checkIn fun st =>
    match st with
    | some s => fun z => sliceEval Q z s.1.2 (Fin.init s.1.1.2.1.r) s.2.1
    | none => 0

/-- Protocol `keccak:protocol`, `D` rounds a segment. -/
noncomputable def protocol : Phase Unit (Option (Final E n)) :=
  (start P D Q x).comp ((layers P D Q D).comp ((outOpen Q x).comp (inOpen Q)))

/-! ## What the verifier ends with -/

/-- The claim on the column's words holds. -/
def OutEval (f : Final E n) : Prop := colEval Q x f.ctx.rl f.ctx.rp f.outPt = f.outVal

/-- The claims on the column's bit slices hold. -/
def InEval (f : Final E n) : Prop := ∀ z, f.slices z = sliceEval Q z f.inLow f.inPack f.inSlot

/-- The verifier accepts with true claims on the column, though the statement is false. -/
def Fooled : Option (Final E n) → Prop
  | none => False
  | some f => OutEval Q x f ∧ InEval Q f ∧ ¬ Statement P D Q x f.ctx.rl f.ctx.rp f.ctx.v

/-- The verifier accepts with true claims on the column, and the statement holds. -/
def Accepted : Option (Final E n) → Prop
  | none => False
  | some f => OutEval Q x f ∧ InEval Q f ∧ Statement P D Q x f.ctx.rl f.ctx.rp f.ctx.v

end KeccakGkr
