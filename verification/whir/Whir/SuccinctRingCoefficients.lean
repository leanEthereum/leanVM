import Whir.SuccinctRingWeight

namespace Whir.SuccinctRingCoefficients
open Concrete RingPCSGame SuccinctRingWeight
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

/-- The source uses the materialized descending-squaring ladder at every stage. -/
def sourceExtend (f : E) (shift : Nat) (ps : List (Nat × E)) : List (Nat × E) :=
  let ladder := inverseFrobeniusLadder f shift
  ps ++ ps.map (fun t => (t.1+shift,t.2*ladder[t.1+shift]!))

theorem sourceExtend_eq (f : E) (shift : Nat) (ps : List (Nat × E))
    (positive : 1 ≤ shift) (bound : ∀ t ∈ ps, t.1+shift < 64) :
    sourceExtend f shift ps = extendCoefficients f shift ps := by
  dsimp only [sourceExtend,extendCoefficients]
  congr 1
  apply List.map_congr_left
  intro t member
  have hk := bound t member
  have active : max shift 1 ≤ t.1+shift := by omega
  have h := inverseFrobeniusLadder_get f shift ⟨t.1+shift,hk⟩
  have index : t.1+shift < (inverseFrobeniusLadder f shift).length := by
    simpa only [inverseFrobeniusLadder_length] using hk
  rw [getElem!_pos (inverseFrobeniusLadder f shift) (t.1+shift) index]
  simpa only [active,↓reduceIte] using congrArg (fun power => (t.1+shift,t.2*power)) h

def sourceNewCoefficients (f : Fin 6 → E) : List (Nat × E) :=
  (List.finRange 6).foldl (fun ps p => sourceExtend (f p) (2^(5-p.val)) ps) [(0,1)]

theorem sourceNewCoefficients_eq (f : Fin 6 → E) : sourceNewCoefficients f = newCoefficients f := by
  have foldEq (stages : List (E × Nat)) (ps : List (Nat × E)) (b : Nat)
      (bound : ∀ t ∈ ps, t.1 ≤ b)
      (budget : b + (stages.map Prod.snd).sum ≤ 63)
      (positive : ∀ stage ∈ stages, 1 ≤ stage.2) :
      stages.foldl (fun acc fs => sourceExtend fs.1 fs.2 acc) ps =
        stages.foldl (fun acc fs => extendCoefficients fs.1 fs.2 acc) ps := by
    induction stages generalizing ps b with
    | nil => rfl
    | cons fs stages ih =>
      have positiveHead := positive fs (by simp)
      have positiveTail : ∀ stage ∈ stages, 1 ≤ stage.2 :=
        fun stage member => positive stage (by simp [member])
      simp only [List.map_cons,List.sum_cons] at budget
      simp only [List.foldl_cons]
      rw [sourceExtend_eq fs.1 fs.2 ps positiveHead (by intro t member; have := bound t member; omega)]
      exact ih _ (b+fs.2) (extend_bound ps fs.1 fs.2 b bound) (by omega) positiveTail
  let stages := (List.finRange 6).map (fun p => (f p,2^(5-p.val)))
  have budget : 0 + (stages.map Prod.snd).sum ≤ 63 := by
    change 0 + ((List.finRange 6).map (fun p => 2^(5-p.val))).sum ≤ 63
    decide +kernel
  have positive : ∀ stage ∈ stages, 1 ≤ stage.2 := by
    intro stage member
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp member
    have positive : 0 < 2^(5-p.val) := by positivity
    exact positive
  have h := foldEq stages [(0,1)] 0 (by simp) budget positive
  simpa only [stages,List.foldl_map,sourceNewCoefficients,newCoefficients] using h

private theorem fill_size (ps : List (Nat × E)) (out : Array E) :
    (ps.foldl (fun acc t => acc.set! t.1 t.2) out).size = out.size := by
  induction ps generalizing out with
  | nil => rfl
  | cons t ps ih => simp only [List.foldl_cons,ih,Array.size_set!]

private theorem fill_get (ps : List (Nat × E)) (target : Fin 64 → E)
    (sound : ∀ t ∈ ps, ∀ k : Fin 64, t.1=k.val → t.2=target k)
    (out : Array E) (size : out.size=64) (k : Fin 64) :
    (ps.foldl (fun acc t => acc.set! t.1 t.2) out)[k.val]! =
      if k.val ∈ ps.map Prod.fst then target k else out[k.val]! := by
  induction ps generalizing out with
  | nil => simp
  | cons t ps ih =>
    have tailSound : ∀ a ∈ ps, ∀ k : Fin 64, a.1=k.val → a.2=target k :=
      fun a member => sound a (by simp [member])
    rw [List.foldl_cons,ih tailSound _ (by simpa only [Array.size_set!] using size)]
    by_cases later : k.val ∈ ps.map Prod.fst
    · simp [later]
    · by_cases same : t.1=k.val
      · have value := sound t (by simp) k same
        have updated : (out.set! t.1 t.2)[k.val]! = target k := by
          rw [same,Array.getElem!_set!_self _ _ _ (by rw [size]; exact k.isLt),value]
        rw [updated]
        simp [later,same]
      · rw [Array.getElem!_set!_ne _ _ _ _ same]
        simp [later,Ne.symm same]

theorem coefficientArray_get (f : Fin 6 → E) (k : Fin 64) :
    (coefficientArray f)[k.val]! = coefficients f k := by
  have sound : ∀ t ∈ newCoefficients f, ∀ k : Fin 64, t.1=k.val → t.2=coefficients f k := by
    intro t member k same
    rw [newCoefficients_ofFn] at member
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
    exact congrArg (coefficients f) (Fin.ext same)
  have present : k.val ∈ (newCoefficients f).map Prod.fst := by
    rw [newCoefficients_keys,coefficientIndices_eq]
    exact List.mem_ofFn.mpr ⟨reverseIndex.symm k,by simp⟩
  exact (fill_get (newCoefficients f) (coefficients f) sound (Array.replicate 64 1)
    (by simp) k).trans (ite_eq_left present)

theorem coefficientArray_size (f : Fin 6 → E) : (coefficientArray f).size=64 := by
  rw [coefficientArray,fill_size]
  rfl

/-- Rust RingMap::new, including all six actual ladders and indexed writes. -/
def sourceCoefficientArray (f : Fin 6 → E) : Array E :=
  (sourceNewCoefficients f).foldl (fun out term => out.set! term.1 term.2) (Array.replicate 64 1)

theorem sourceCoefficientArray_get (f : Fin 6 → E) (k : Fin 64) :
    (sourceCoefficientArray f)[k.val]! = coefficients f k := by
  rw [sourceCoefficientArray,sourceNewCoefficients_eq]
  exact coefficientArray_get f k

theorem sourceCoefficientArray_size (f : Fin 6 → E) : (sourceCoefficientArray f).size=64 := by
  rw [sourceCoefficientArray,sourceNewCoefficients_eq]
  exact coefficientArray_size f

theorem queryLadder_get (q : E) (k : Fin 64) :
    (inverseFrobeniusLadder q 1)[k.val]! = inverseFrobenius q k.val := by
  rw [getElem!_pos (inverseFrobeniusLadder q 1) k.val
    (by simpa only [inverseFrobeniusLadder_length] using k.isLt)]
  have h := inverseFrobeniusLadder_get q 1 k
  by_cases zero : k.val=0
  · simpa [zero,inverseFrobenius] using h
  · have active : max 1 1 ≤ k.val := by omega
    simpa only [active,↓reduceIte] using h

end Whir.SuccinctRingCoefficients
