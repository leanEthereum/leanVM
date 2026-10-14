import Whir.PCSBCSCallerParserPolynomialBound

/-! Concrete Flock caller work, including malformed layouts and token rejection.
The additive size charges declared Nat literals by value, not their bit length.
The counter is the existing source-operation counter; delayed slice closures are
not evaluated here and retain `assembleFlockGetterWork` as their access price. -/
set_option autoImplicit false
namespace Whir.PCSBCSCallerParserCost
open Concrete WHIRCallerClaims
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private theorem bind_bound {A B : Type} (p : Parser A) (f : A → Parser B)
    (ts : List CallerToken) (m n total : Nat) (sum : m+n ≤ total)
    (hp : (p ts).work ≤ m)
    (hf : ∀ a rest, (p ts).result = some (a,rest) → (f a rest).work ≤ n) :
    ((p >>= f) ts).work ≤ total := (bind_work_le p f ts m n hp hf).trans sum

private theorem tick_bound {A : Type} (n : Nat) (p : Parser A)
    (ts : List CallerToken) (cap total : Nat) (sum : n+cap ≤ total)
    (hp : (p ts).work ≤ cap) :
    ((tick n >>= fun _ => p) ts).work ≤ total := by
  rw [tick_bind_work]
  exact (Nat.add_le_add_left hp n).trans sum

local macro "flock_bind " m:term "," n:term : tactic =>
  `(tactic| (apply bind_bound _ _ _ $m $n; · omega))
local macro "flock_tick " n:term : tactic =>
  `(tactic| (apply tick_bound _ _ _ $n; · first | (unfold lengthCost; omega) | omega))

/-- Placement, declared dimensions, derived round/point numerals, and a cell. -/
def flockLayoutSize (l : FlockLayout) : Nat :=
  1+l.offset+l.kLog+l.instanceLog+l.logN+(l.kLog-6)+(l.logN-6)

/-- Additive literal configuration size, including the list spine. -/
def flockConfigurationSize (ls : List FlockLayout) : Nat :=
  1+ls.length+(ls.map flockLayoutSize).sum

namespace FlockPolynomial

theorem literal_le_sum (ls : List FlockLayout) (l : FlockLayout) (h : l ∈ ls) :
    flockLayoutSize l ≤ (ls.map flockLayoutSize).sum := by
  induction ls with
  | nil => simp at h
  | cons a ls ih =>
    simp only [List.mem_cons] at h
    simp only [List.map_cons,List.sum_cons]
    rcases h with rfl | h
    · omega
    · exact (ih h).trans (Nat.le_add_left _ _)

theorem layout_caps (ls : List FlockLayout) (l : FlockLayout) (h : l ∈ ls) :
    l.logN ≤ flockConfigurationSize ls ∧
    l.kLog-6 ≤ flockConfigurationSize ls ∧
    l.logN-6 ≤ flockConfigurationSize ls := by
  have hs := literal_le_sum ls l h
  have localCap : l.logN ≤ flockLayoutSize l ∧ l.kLog-6 ≤ flockLayoutSize l ∧
      l.logN-6 ≤ flockLayoutSize l := by unfold flockLayoutSize; omega
  unfold flockConfigurationSize
  omega

theorem max_fold_le (xs : List Nat) (cap start : Nat)
    (hs : start ≤ cap) (hx : ∀ x ∈ xs, x ≤ cap) : xs.foldl max start ≤ cap := by
  induction xs generalizing start with
  | nil => exact hs
  | cons x xs ih =>
    apply ih (max start x) (max_le hs (hx x (by simp)))
    intro y hy
    exact hx y (by simp [hy])

theorem dimension_caps (ls : List FlockLayout) :
    ls.length ≤ flockConfigurationSize ls ∧
    (ls.map FlockLayout.logN).foldl max 0 ≤ flockConfigurationSize ls ∧
    (ls.map (fun l => l.kLog-6)).foldl max 0 ≤ flockConfigurationSize ls := by
  refine ⟨by unfold flockConfigurationSize; omega, ?_, ?_⟩
  · apply max_fold_le _ _ _ (Nat.zero_le _)
    intro x hx
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hx
    exact (layout_caps ls l hl).1
  · apply max_fold_le _ _ _ (Nat.zero_le _)
    intro x hx
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hx
    exact (layout_caps ls l hl).2.1

/-- Literal two-coefficient sumcheck round used twice by `flockClaims`. -/
def round (_ : Nat) : Parser E := do
  tick 2
  let _ ← readScalars 2
  drawScalar

theorem round_work_le (i : Nat) (ts : List CallerToken) : (round i ts).work ≤ 26 := by
  unfold round
  rw [tick_bind_work]
  have h := bind_work_le (readScalars 2) (fun _ => drawScalar) ts 20 4
    (readScalars_work_le 2 ts) (by intro values rest parsed; exact drawScalar_work_le rest)
  omega

theorem rounds_work_le (n : Nat) (ts : List CallerToken) :
    ((List.range n).mapM round ts).work ≤ 26*n := by
  simpa using mapM_work_le (List.range n) round 26
    (fun i _ rest => round_work_le i rest) ts

/-- Both growing sampled-coordinate lists have the actual requested length. -/
theorem rounds_success_length (n : Nat) (ts : List CallerToken) (point : List E)
    (rest : List CallerToken)
    (h : ((List.range n).mapM round ts).result = some (point,rest)) :
    point.length = n := by
  simpa using mapM_success_length (List.range n) round ts point rest h

def produce (zc lc : List E) (layout : FlockLayout) : Parser RingPCSGame.FamilyClaim := do
  tick 2
  let slices ← readScalars 64
  let _ ← readScalar
  let assembled := assembleFlock layout zc lc slices
  tick (assembled.work+1)
  match assembled.value with
  | some claim => pure claim
  | none => liftOption 0 none

theorem produce_work_le (zc lc : List E) (l : FlockLayout) (ts : List CallerToken) :
    (produce zc lc l ts).work ≤ 9*lc.length+6*zc.length+679 := by
  unfold produce
  flock_tick (9*lc.length+6*zc.length+677)
  flock_bind 578, (9*lc.length+6*zc.length+99)
  · exact readScalars_work_le 64 ts
  · intro slices rest parsed
    have hs := readScalars_success_length 64 ts slices rest parsed
    flock_bind 4, (9*lc.length+6*zc.length+95)
    · exact readScalar_work_le rest
    · intro unused tail parsed
      rw [tick_bind_work]
      have ha := assembleFlock_work_le l zc lc slices
      cases (assembleFlock l zc lc slices).value <;>
        simp only [pure,liftOption] <;> omega

/-- The assembly success branch supplies its actual point and slices; no honest
metadata hypothesis is required. Accesses to the returned closure remain deferred. -/
theorem assemble_success (l : FlockLayout) (zc lc slices : List E)
    (claim : RingPCSGame.FamilyClaim)
    (h : (assembleFlock l zc lc slices).value = some claim) :
    slices.length = 64 ∧ claim.offset = l.offset ∧ claim.point.size = l.logN-6 ∧
    (∀ i : Fin 64, claim.slices i = slices[i.val]?.getD 0) := by
  simp only [assembleFlock] at h
  split at h
  · simp at h
  · rename_i valid
    have hv : 6 ≤ l.kLog ∧ 13 ≤ l.logN ∧ l.kLog-6 ≤ lc.length ∧
        l.logN-6 ≤ zc.length := by
      simp at valid
      omega
    split at h
    · rename_i hs
      cases h
      refine ⟨hs,rfl,?_,?_⟩
      · simp only [List.size_toArray,List.length_append,List.length_reverse,
          List.length_take,List.length_drop,FlockLayout.logN] at *
        omega
      · intro i
        have hi : i.val < slices.length := by rw [hs]; exact i.isLt
        simp only [List.getElem?_eq_getElem hi,Option.getD_some]
    · simp at h

/-- Success elimination for the actual counted bind, retaining intermediate values. -/
theorem bind_success {A B : Type} (p : Parser A) (f : A → Parser B)
    (ts : List CallerToken) (v : B) (rest : List CallerToken)
    (h : ((p >>= f) ts).result = some (v,rest)) :
    ∃ a middle, (p ts).result = some (a,middle) ∧
      (f a middle).result = some (v,rest) := by
  change (bind p f ts).result = _ at h
  unfold bind at h
  cases hp : (p ts).result with
  | none => simp [hp] at h
  | some pair =>
    rcases pair with ⟨a,middle⟩
    exact ⟨a,middle,rfl,by simpa only [hp] using h⟩

end FlockPolynomial

/-- No token or metadata admissibility premise: failed prefixes are charged too. -/
theorem flockClaims_work_le (ls : List FlockLayout) (ts : List CallerToken) :
    (flockClaims ls ts).work ≤
      20*(flockConfigurationSize ls)^2+800*flockConfigurationSize ls+700 := by
  let s := flockConfigurationSize ls
  let m := (ls.map FlockLayout.logN).foldl max 0
  let r := (ls.map (fun l => l.kLog-6)).foldl max 0
  have caps := FlockPolynomial.dimension_caps ls
  have hn : ls.length ≤ s := caps.1
  have hm : m ≤ s := caps.2.1
  have hr : r ≤ s := caps.2.2
  have header : (3+if ls.isEmpty then 0 else
      allCost (fun l => 6 ≤ l.kLog && 13 ≤ l.logN)
        (fun l => if 6 ≤ l.kLog then 4 else 2) ls) ≤ 5*ls.length+4 := by
    have h := allCost_le (fun l : FlockLayout => 6 ≤ l.kLog && 13 ≤ l.logN)
      (fun l => if 6 ≤ l.kLog then 4 else 2) ls 4
      (by intro l hl; split <;> omega)
    split <;> omega
  unfold flockClaims
  change _ ≤ 20*s^2+800*s+700
  flock_tick (20*s^2+795*s+696)
  flock_bind 3, (20*s^2+795*s+693)
  · exact check_work_le _ ts
  · intro unused rest parsed
    flock_tick (20*s^2+785*s+687)
    flock_bind (9*s+2), (20*s^2+776*s+685)
    · exact (drawScalars_work_le _ rest).trans (by omega)
    · intro values rest parsed
      flock_bind 4, (20*s^2+776*s+681)
      · exact drawScalar_work_le rest
      · intro unused rest parsed
        flock_bind 578, (20*s^2+776*s+103)
        · exact readScalars_work_le 64 rest
        · intro values rest parsed
          flock_bind 4, (20*s^2+776*s+99)
          · exact drawScalar_work_le rest
          · intro unused rest parsed
            flock_tick (20*s^2+774*s+96)
            flock_bind (26*s), (20*s^2+748*s+96)
            · exact (FlockPolynomial.rounds_work_le _ rest).trans
                (Nat.mul_le_mul_left 26 (by omega))
            · intro zc rest parsed
              have hz : zc.length ≤ s := by
                have h := mapM_success_length (List.range (m-6)) FlockPolynomial.round _ zc _ parsed
                simp only [List.length_range] at h
                omega
              flock_tick (20*s^2+747*s+94)
              flock_bind (27*s+2), (20*s^2+720*s+92)
              · exact (readScalars_work_le _ rest).trans (by omega)
              · intro values rest parsed
                flock_bind 4, (20*s^2+720*s+88)
                · exact drawScalar_work_le rest
                · intro unused rest parsed
                  flock_tick (20*s^2+718*s+86)
                  flock_bind (26*s), (20*s^2+692*s+86)
                  · exact (FlockPolynomial.rounds_work_le _ rest).trans
                      (Nat.mul_le_mul_left 26 hr)
                  · intro lc rest parsed
                    have hl : lc.length ≤ s := by
                      have h := mapM_success_length (List.range r) FlockPolynomial.round _ lc _ parsed
                      simp only [List.length_range] at h
                      omega
                    have bound := mapM_work_le ls (FlockPolynomial.produce zc lc) (15*s+679)
                      (by intro l _ tail; have h := FlockPolynomial.produce_work_le zc lc l tail; omega) rest
                    have mul := Nat.mul_le_mul_left (15*s+679) hn
                    change ((ls.mapM (FlockPolynomial.produce zc lc)) rest).work ≤
                      20*s^2+692*s+86
                    simp only [pow_two]
                    nlinarith

namespace FlockPolynomial

theorem produce_success (zc lc : List E) (l : FlockLayout) (ts rest : List CallerToken)
    (claim : RingPCSGame.FamilyClaim) (h : (produce zc lc l ts).result = some (claim,rest)) :
    ∃ slices : List E, slices.length = 64 ∧
      (assembleFlock l zc lc slices).value = some claim := by
  unfold produce at h
  obtain ⟨_,t0,_,h0⟩ := bind_success _ _ _ _ _ h
  obtain ⟨slices,t1,hs,h1⟩ := bind_success _ _ _ _ _ h0
  obtain ⟨_,t2,_,h2⟩ := bind_success _ _ _ _ _ h1
  obtain ⟨_,t3,_,h3⟩ := bind_success _ _ _ _ _ h2
  have length := readScalars_success_length 64 t0 slices t1 hs
  cases ha : (assembleFlock l zc lc slices).value with
  | none => simp only [ha,liftOption,Option.map_none] at h3; cases h3
  | some value =>
    simp only [ha,pure,Option.some.injEq,Prod.mk.injEq] at h3
    rcases h3 with ⟨rfl,_⟩
    exact ⟨slices,length,ha⟩

theorem mapM_success_related {A B : Type} (xs : List A) (f : A → Parser B)
    (R : A → B → Prop)
    (body : ∀ a ∈ xs, ∀ ts v rest, (f a ts).result = some (v,rest) → R a v)
    (ts : List CallerToken) (ys : List B) (rest : List CallerToken)
    (h : (xs.mapM f ts).result = some (ys,rest)) :
    ∀ y ∈ ys, ∃ x ∈ xs, R x y := by
  induction xs generalizing ts ys rest with
  | nil =>
    change some ([],ts) = some (ys,rest) at h
    cases h
    simp
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    obtain ⟨y,middle,hy,ht⟩ := bind_success _ _ _ _ _ h
    obtain ⟨tail,remaining,htail,hfinal⟩ := bind_success _ _ _ _ _ ht
    change some (y::tail,remaining) = some (ys,rest) at hfinal
    cases hfinal
    have head := body x (by simp) ts y middle hy
    have later := ih (fun a ha => body a (by simp [ha])) middle tail rest htail
    intro value member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨x,by simp,head⟩
    · obtain ⟨a,ha,hr⟩ := later value member
      exact ⟨a,by simp [ha],hr⟩

theorem producer_outputs (ls : List FlockLayout) (zc lc : List E)
    (ts : List CallerToken) (claims : List RingPCSGame.FamilyClaim)
    (rest : List CallerToken)
    (h : (ls.mapM (produce zc lc) ts).result = some (claims,rest)) :
    claims.length = ls.length ∧
    ∀ c ∈ claims, ∃ l ∈ ls, c.offset = l.offset ∧ c.point.size = l.logN-6 := by
  refine ⟨mapM_success_length ls _ ts claims rest h, ?_⟩
  apply mapM_success_related ls (produce zc lc)
    (fun l c => c.offset = l.offset ∧ c.point.size = l.logN-6) _ ts claims rest h
  intro l _ tokens c tail accepted
  obtain ⟨slices,_,assembled⟩ := produce_success zc lc l tokens tail c accepted
  have shape := assemble_success l zc lc slices c assembled
  exact ⟨shape.2.1,shape.2.2.1⟩

end FlockPolynomial

/-- Exact producer cardinality and actual returned ring dimensions, even when
the accepted metadata differs from any intended honest configuration. -/
theorem flockClaims_success_layouts (ls : List FlockLayout) (ts : List CallerToken)
    (claims : List RingPCSGame.FamilyClaim) (rest : List CallerToken)
    (accepted : (flockClaims ls ts).result = some (claims,rest)) :
    claims.length = ls.length ∧
    ∀ c ∈ claims, ∃ l ∈ ls, c.offset = l.offset ∧ c.point.size = l.logN-6 := by
  unfold flockClaims at accepted
  repeat' (obtain ⟨value,middle,_,accepted⟩ :=
    FlockPolynomial.bind_success _ _ _ _ _ accepted)
  exact FlockPolynomial.producer_outputs ls _ _ _ _ _ accepted

/-- Parent-composable resource endpoint: additive literal size, quadratic work,
exact producer count, and a size cap for each actually returned point. -/
theorem flockClaims_resource (ls : List FlockLayout) (ts : List CallerToken) :
    (flockClaims ls ts).work ≤
      20*(flockConfigurationSize ls)^2+800*flockConfigurationSize ls+700 ∧
    ∀ claims rest, (flockClaims ls ts).result = some (claims,rest) →
      claims.length = ls.length ∧
      ∀ c ∈ claims, c.point.size ≤ flockConfigurationSize ls := by
  refine ⟨flockClaims_work_le ls ts,?_⟩
  intro claims rest accepted
  have shape := flockClaims_success_layouts ls ts claims rest accepted
  refine ⟨shape.1,?_⟩
  intro c hc
  obtain ⟨l,hl,_,point⟩ := shape.2 c hc
  rw [point]
  exact (FlockPolynomial.layout_caps ls l hl).2.2

/-! Persistent kernel smoke on the changed proof path. Erasure equates the
actual counted accepted/rejected result with the source interpreter. -/
namespace FlockPolynomial.Smoke

theorem accepted_counted_source :
    ∃ claims, (flockClaims [⟨0,6,7⟩] PCSBCSCallerParserCost.Smoke.flockTokens).result =
      some (claims,[]) ∧
      WHIRCallerClaims.flockClaims [⟨0,6,7⟩] PCSBCSCallerParserCost.Smoke.flockTokens =
        some (claims,[]) ∧ claims.length = 1 ∧
      ∀ c ∈ claims, c.point.size = 7 := by
  obtain ⟨claims,h⟩ := PCSBCSCallerParserCost.Smoke.minimal_flock_accepts
  have shape := flockClaims_success_layouts [⟨0,6,7⟩] _ claims [] h
  refine ⟨claims,h,?_,shape.1,?_⟩
  · change erase (flockClaims _) _ = _ at h
    rwa [flockClaims_erasure] at h
  · intro c hc
    obtain ⟨l,hl,_,point⟩ := shape.2 c hc
    simp only [List.mem_singleton] at hl
    subst l
    exact point

theorem rejected_counted_source :
    (flockClaims [⟨0,5,10⟩] []).result = none ∧
    WHIRCallerClaims.flockClaims [⟨0,5,10⟩] [] = none ∧
    (flockClaims [⟨0,5,10⟩] []).work ≤
      20*(flockConfigurationSize [⟨0,5,10⟩])^2+
        800*flockConfigurationSize [⟨0,5,10⟩]+700 := by
  exact ⟨rfl,rfl,flockClaims_work_le _ _⟩

theorem token_rejection_counted_source :
    (flockClaims [⟨0,6,7⟩] [.sent 0]).result = none ∧
    WHIRCallerClaims.flockClaims [⟨0,6,7⟩] [.sent 0] = none ∧
    0 < (flockClaims [⟨0,6,7⟩] [.sent 0]).work := by
  constructor
  · rfl
  constructor
  · rfl
  · decide

def mixedLayouts : List FlockLayout := [⟨0,6,7⟩,⟨64,7,7⟩]

def mixedTokens : List CallerToken :=
  List.replicate 2 (.draw 0) ++ List.replicate 64 (.sent 0) ++ [.draw 0] ++
  (List.replicate 8 [.sent 0,.sent 0,.draw 0]).flatten ++
  List.replicate 6 (.sent 0) ++ [.draw 0] ++ [.sent 0,.sent 0,.draw 0] ++
  List.replicate 130 (.sent 0)

/-- Two unequal dimensions, nonempty lincheck, eight zerocheck coordinates, and
two separately consumed 64-slice blocks exercise the actual producer path. -/
theorem mixed_accepted_counted :
    ((flockClaims mixedLayouts mixedTokens).result.map
      (fun (claims,rest) => (claims.map (fun c => (c.offset,c.point.size)),rest))) =
      some ([(0,7),(64,8)],[]) := by rfl

theorem mixed_accepted_source :
    ((WHIRCallerClaims.flockClaims mixedLayouts mixedTokens).map
      (fun (claims,rest) => (claims.map (fun c => (c.offset,c.point.size)),rest))) =
      some ([(0,7),(64,8)],[]) := by
  rw [← flockClaims_erasure]
  exact mixed_accepted_counted

theorem mixed_accepted_work :
    (flockClaims mixedLayouts mixedTokens).work ≤
      20*(flockConfigurationSize mixedLayouts)^2+
        800*flockConfigurationSize mixedLayouts+700 := flockClaims_work_le _ _

theorem malformed_assembly_rejected :
    (assembleFlock ⟨0,7,7⟩ (List.replicate 8 0) [] (List.replicate 64 0)).value = none ∧
    (assembleFlock ⟨0,6,7⟩ (List.replicate 7 0) [] (List.replicate 63 0)).value = none := by
  constructor <;> rfl

end FlockPolynomial.Smoke

#print axioms flockClaims_resource
#print axioms flockClaims_success_layouts
#print axioms FlockPolynomial.Smoke.accepted_counted_source
#print axioms FlockPolynomial.Smoke.rejected_counted_source
#print axioms flockClaims_work_le
#print axioms FlockPolynomial.assemble_success
#print axioms FlockPolynomial.Smoke.mixed_accepted_counted
#print axioms FlockPolynomial.Smoke.mixed_accepted_source
end Whir.PCSBCSCallerParserCost
