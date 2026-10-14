import Whir.TypedOracleCompiler

/-! Exact finite-table coupling for causal, globally memoized oracle programs. -/
namespace Whir.RawOracleCoupling
open TypedOracleCompiler TypedFiatShamirGame
open FiatShamirGame (average)
open scoped BigOperators

universe u v w

 theorem average_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (f : Y → ℚ) : average (fun x => f (e x)) = average f := by
  unfold average
  rw [Fintype.sum_equiv e _ _ (fun _ => rfl), Fintype.card_congr e]

 theorem average_comm {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → ℚ) :
    average (fun x => average (f x)) = average (fun y => average (fun x => f x y)) := by
  unfold average
  simp only [← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

section Memo
variable {Key : Type u} {Answer : Key → Type v} {R : Type w}
variable [DecidableEq Key]

def overlay (cache : Cache Key Answer) (table : (k : Key) → Answer k) :
    (k : Key) → Answer k := fun k => (cache k).getD (table k)

omit [DecidableEq Key] in
@[simp] theorem overlay_empty (table : (k : Key) → Answer k) :
    overlay (fun _ => none) table = table := rfl

 theorem overlay_put (cache : Cache Key Answer) (table : (k : Key) → Answer k)
    (k : Key) (a : Answer k) :
    overlay (put cache k a) table = Function.update (overlay cache table) k a := by
  funext j
  by_cases h : j = k
  · subst j; simp [overlay]
  · simp [overlay, put_other, h]

/-- The cache is private interpreter state. Continuations receive exactly their
requested answer, including every bit of a requested padded block. -/
def memo {n} : Sampling Key Answer R n → Cache Key Answer →
    Sampling Key Answer (R × Cache Key Answer) n
  | .ret r, cache => .ret (r, cache)
  | .draw k next, cache =>
    match cache k with
    | some a => Sampling.pad (Nat.le_succ _) (memo (next a) cache)
    | none => .draw k (fun a => memo (next a) (put cache k a))

theorem overlay_put_miss (cache : Cache Key Answer) (table : (k : Key) → Answer k)
    (k : Key) (miss : cache k = none) :
    overlay (put cache k (table k)) table = overlay cache table := by
  funext j
  by_cases h : j = k
  · subst j; simp [overlay, miss]
  · simp [overlay, put_other, h]

theorem memo_eval_first {n} (p : Sampling Key Answer R n) (cache : Cache Key Answer)
    (table : (k : Key) → Answer k) :
    (Sampling.eval table (memo p cache)).1 = Sampling.eval (overlay cache table) p := by
  induction p generalizing cache with
  | ret r => rfl
  | draw k next ih =>
    cases hit : cache k with
    | some a => simp [memo, hit, ih, Sampling.eval, overlay]
    | none =>
      simp only [memo, hit, Sampling.eval, ih, overlay_put_miss cache table k hit]
      simp [overlay, hit]

theorem memo_eval_consistent {n} (p : Sampling Key Answer R n)
    (cache : Cache Key Answer) (table : (k : Key) → Answer k)
    (consistent : ∀ k a, cache k = some a → table k = a) :
    ∀ k a, (Sampling.eval table (memo p cache)).2 k = some a → table k = a := by
  induction p generalizing cache with
  | ret r => exact consistent
  | draw k next ih =>
    cases hit : cache k with
    | some a =>
      simpa only [memo, hit, Sampling.eval_pad] using ih a cache consistent
    | none =>
      simp only [memo, hit, Sampling.eval]
      apply ih (table k)
      intro j a ha
      by_cases h : j = k
      · subst j; simpa only [put_self, Option.some.injEq] using ha
      · exact consistent j a (by simpa only [put_other _ _ _ _ h] using ha)

variable [Fintype Key] [∀ k, Fintype (Answer k)] [∀ k, Nonempty (Answer k)]

 theorem average_update (k : Key) (f : ((j : Key) → Answer j) → ℚ) :
    average f = average (fun a : Answer k =>
      average (fun table : (j : Key) → Answer j => f (Function.update table k a))) := by
  classical
  let e := Equiv.piSplitAt k Answer
  have split (g : ((j : Key) → Answer j) → ℚ) :
      average g = average (fun rest : (j : {j : Key // j ≠ k}) → Answer j =>
        average (fun a : Answer k => g (e.symm (a, rest)))) := by
    have h := TypedFiatShamirGame.fresh_coordinate k
      (fun rest a => g (e.symm (a, rest)))
    change average (fun table => g (e.symm (e table))) = _ at h
    simpa only [e.symm_apply_apply] using h
  rw [split f]
  rw [average_comm]
  apply congrArg average
  funext a
  rw [split]
  apply congrArg average
  funext rest
  have hu (b : Answer k) : Function.update (e.symm (b, rest)) k a = e.symm (a, rest) := by
    apply e.injective
    apply Prod.ext
    · simp [e]
    · funext j; simp [e, j.property]
  simp only [hu]
  exact (FiatShamirGame.average_const _).symm


 theorem overlay_average (cache : Cache Key Answer) (k : Key) (miss : cache k = none)
    (f : ((j : Key) → Answer j) → ℚ) :
    average (fun table => f (overlay cache table)) =
      average (fun a : Answer k => average (fun table => f (overlay (put cache k a) table))) := by
  rw [average_update k]
  apply congrArg average
  funext a
  apply congrArg average
  funext table
  congr 1
  rw [overlay_put]
  funext j
  by_cases h : j = k
  · subst j; simp [overlay, miss]
  · simp [overlay, Function.update_of_ne h]

/-- Exact equality for EVERY payoff, for arbitrary adaptive requests and repeats.
The total table appears only in the reference integral, never in a continuation. -/
theorem table_eq_memo {n} (program : Sampling Key Answer R n)
    (cache : Cache Key Answer) (payoff : R → ℚ) :
    average (fun table => payoff (Sampling.eval (overlay cache table) program)) =
      Sampling.expectation (fun result => payoff result.1) (memo program cache) := by
  induction program generalizing cache with
  | ret r => simp [memo, Sampling.eval, Sampling.expectation, FiatShamirGame.average_const]
  | draw k next ih =>
    cases hit : cache k with
    | some a =>
      simp only [memo, hit, Sampling.expectation_pad]
      rw [← ih a cache]
      apply congrArg average
      funext table
      simp [Sampling.eval, overlay, hit]
    | none =>
      simp only [memo, hit, Sampling.expectation]
      trans average (fun a : Answer k => average (fun table =>
        payoff (Sampling.eval (overlay (put cache k a) table) (.draw k next))))
      · exact overlay_average cache k hit (fun oracle => payoff (Sampling.eval oracle (.draw k next)))
      apply congrArg average
      funext a
      rw [← ih a (put cache k a)]
      apply congrArg average
      funext table
      simp [Sampling.eval, overlay]

 theorem empty_table_eq_memo {n} (program : Sampling Key Answer R n) (payoff : R → ℚ) :
    average (fun table => payoff (Sampling.eval table program)) =
      Sampling.expectation (fun result => payoff result.1) (memo program (fun _ => none)) :=
  table_eq_memo program (fun _ => none) payoff


/-- The final verifier may inspect the actually completed private cache. This
strengthened coupling retains that cache in the result, without exposing it to
any adversarial continuation. -/
theorem table_eq_memo_full {n} (program : Sampling Key Answer R n)
    (cache : Cache Key Answer) (payoff : R × Cache Key Answer → ℚ) :
    average (fun table =>
      payoff (Sampling.eval (overlay cache table) (memo program cache))) =
      Sampling.expectation payoff (memo program cache) := by
  induction program generalizing cache with
  | ret r => simp [memo, Sampling.eval, Sampling.expectation, FiatShamirGame.average_const]
  | draw k next ih =>
    cases hit : cache k with
    | some a =>
      simpa only [memo, hit, Sampling.eval_pad, Sampling.expectation_pad] using ih a cache
    | none =>
      trans average (fun a : Answer k => average (fun table =>
        payoff (Sampling.eval (overlay (put cache k a) table) (memo (.draw k next) cache))))
      · exact overlay_average cache k hit
          (fun oracle => payoff (Sampling.eval oracle (memo (.draw k next) cache)))
      simp only [memo, hit, Sampling.expectation]
      apply congrArg average
      funext a
      rw [← ih a (put cache k a)]
      apply congrArg average
      funext table
      simp [Sampling.eval, overlay]
end Memo

/-- A completed operational trace determines the executable evaluation when
the evaluator agrees with its actual allocated answers. No unseen answer is
consulted by this reconstruction. -/
theorem execute_eq_of_runs {Key : Type u} {Answer : Key → Type v} {R : Type w}
    (oracle : (key : Key) → Answer key) {n} {p : Sampling Key Answer R n}
    {trace result} (run : Sampling.Runs p trace result)
    (answers : ∀ entry ∈ trace, oracle entry.1 = entry.2) :
    Sampling.execute oracle p = (result,trace) := by
  induction run with
  | ret => rfl
  | draw a run ih =>
    have first := answers _ List.mem_cons_self
    have rest := ih (fun entry member => answers entry (List.mem_cons_of_mem _ member))
    simp only [Sampling.execute, first, rest]

/-- A concrete recognizer partitions all raw keys. Its laws are codec laws,
not distribution assumptions. Off-image keys are retained, not rejected. -/
structure Partition (Raw Packet : Type u) (Block : Packet → Type u) where
  encode : Sigma Block → Raw
  recognize : Raw → Option (Sigma Block)
  recognize_encode : ∀ c, recognize (encode c) = some c
  encode_recognize : ∀ raw c, recognize raw = some c → encode c = raw

namespace Partition
variable {Raw Packet D : Type u} {Block : Packet → Type u}
variable (part : Partition Raw Packet Block)

abbrev Garbage := {raw : Raw // part.recognize raw = none}
abbrev Key := Sum Packet part.Garbage
abbrev Answer : part.Key → Type u
  | .inl p => Block p → D
  | .inr _ => D

def join (table : (k : part.Key) → part.Answer (D := D) k) (raw : Raw) : D :=
  match h : part.recognize raw with
  | some c => table (.inl c.1) c.2
  | none => table (.inr ⟨raw,h⟩)

def split (table : Raw → D) : (k : part.Key) → part.Answer (D := D) k
  | .inl p => fun b => table (part.encode ⟨p,b⟩)
  | .inr g => table g.val

theorem join_split (table : Raw → D) : part.join (part.split table) = table := by
  funext raw
  unfold join
  split
  · rename_i c h
    exact congrArg table (part.encode_recognize raw c h)
  · rfl

theorem split_join (table : (k : part.Key) → part.Answer (D := D) k) :
    part.split (part.join table) = table := by
  funext k
  cases k with
  | inl p =>
    funext b
    simp only [split]
    unfold join
    split
    · rename_i c hc
      have he : c = ⟨p,b⟩ := Option.some.inj (hc.symm.trans (part.recognize_encode _))
      subst c
      rfl
    · rename_i hc
      rw [part.recognize_encode] at hc
      contradiction
  | inr g =>
    simp only [split]
    unfold join
    split
    · rename_i c hc
      rw [g.property] at hc
      contradiction
    · rfl

def tableEquiv : (Raw → D) ≃ ((k : part.Key) → part.Answer (D := D) k) where
  toFun := part.split
  invFun := part.join
  left_inv := part.join_split
  right_inv := part.split_join

/-- Proactive ancestor reads do not release their packets to the adversary.
They are memoized with every other request by the single outer interpreter. -/
def warm : (ancestors : List Packet) →
    Sampling part.Key (part.Answer (D := D)) Unit ancestors.length
  | [] => .ret ()
  | p :: ps => .draw (.inl p) (fun _ => warm ps)

@[simp] theorem eval_warm (table : (k : part.Key) → part.Answer (D := D) k)
    (ancestors : List Packet) : Sampling.eval table (part.warm ancestors) = () := by
  induction ancestors with
  | nil => rfl
  | cons p ps ih => exact ih

/-- Earlier caller-output coordinates are ordinary off-image raw groups. They
are completed privately before any WHIR packet at the corresponding entry. -/
def warmCaller : (calls : List part.Garbage) →
    Sampling part.Key (part.Answer (D := D)) Unit calls.length
  | [] => .ret ()
  | raw :: rest => .draw (.inr raw) (fun _ => warmCaller rest)

@[simp] theorem eval_warmCaller (table : (k : part.Key) → part.Answer (D := D) k)
    (calls : List part.Garbage) : Sampling.eval table (part.warmCaller calls) = () := by
  induction calls with
  | nil => rfl
  | cons raw rest ih => exact ih

/-- An explicit bounded prefix schedule; the concrete recognizer supplies its
strict ancestors, in oldest-first order, and the uniform syntactic depth cap. -/
structure Schedule (Packet : Type u) (B : Nat) where
  positive : 0 < B
  ancestors : Packet → List Packet
  bounded : ∀ p, (ancestors p).length + 1 ≤ B

structure CallerPlan (Packet Garbage : Type u) (C : Nat) where
  calls : Packet → List Garbage
  bounded : ∀ p, (calls p).length ≤ C

/-- Caller outputs, strict WHIR ancestors, then the entire current packet.
All three stages are processed by the same outer memoizing interpreter. -/
def completePacket {B C} (schedule : Schedule Packet B)
    (caller : CallerPlan Packet part.Garbage C) (packet : Packet) :
    Sampling part.Key (part.Answer (D := D)) (Block packet → D) (B+C) :=
  Sampling.pad (by have := schedule.bounded packet; have := caller.bounded packet; omega)
    (Sampling.bind (part.warmCaller (caller.calls packet)) (fun _ =>
      Sampling.bind (part.warm (schedule.ancestors packet)) (fun _ =>
        Sampling.draw (.inl packet) (fun answer => Sampling.ret (n := 0) answer))))

@[simp] theorem eval_completePacket {B C} (schedule : Schedule Packet B)
    (caller : CallerPlan Packet part.Garbage C)
    (table : (k : part.Key) → part.Answer (D := D) k) (packet : Packet) :
    Sampling.eval table (part.completePacket schedule caller packet) = table (.inl packet) := by
  simp [completePacket, Sampling.eval]

def request {B C} (schedule : Schedule Packet B)
    (caller : CallerPlan Packet part.Garbage C) (raw : Raw) :
    Sampling part.Key (part.Answer (D := D)) D (B+C) :=
  match h : part.recognize raw with
  | some c => Sampling.pad (by omega)
      (Sampling.bind (part.completePacket schedule caller c.1)
        (fun packet => Sampling.ret (n := 0) (packet c.2)))
  | none => Sampling.pad (by have := schedule.positive; omega)
      (Sampling.draw (.inr ⟨raw,h⟩) (fun answer => Sampling.ret (n := 0) answer))

theorem eval_request {B C} (schedule : Schedule Packet B)
    (caller : CallerPlan Packet part.Garbage C)
    (table : (k : part.Key) → part.Answer (D := D) k) (raw : Raw) :
    Sampling.eval table (part.request schedule caller raw) = part.join table raw := by
  unfold request join
  split <;> simp [Sampling.eval]

/-- All raw requests, including simulator-generated requests, use this same
syntax and counter. Padding can select subsequent inputs. Caller completion
and final WHIR completion are included even when no raw query precedes them. -/
def program {R : Type u} {B C} (schedule : Schedule Packet B)
    (caller : CallerPlan Packet part.Garbage C) (final : R → Option Packet) :
    {n : Nat} → Sampling Raw (fun _ => D) R n →
      Sampling part.Key (part.Answer (D := D)) R ((B+C)*n+(B+C))
  | _, .ret r =>
    match final r with
    | none => .ret r
    | some packet => Sampling.pad (by omega)
        (Sampling.bind (part.completePacket schedule caller packet)
          (fun _ => Sampling.ret (n := 0) r))
  | n+1, .draw raw next => Sampling.pad (by simp only [Nat.mul_add, Nat.mul_one]; omega)
      (Sampling.bind (part.request schedule caller raw)
        (fun answer => program schedule caller final (next answer)))

theorem eval_program {R : Type u} {B C n} (schedule : Schedule Packet B)
    (caller : CallerPlan Packet part.Garbage C) (final : R → Option Packet)
    (table : (k : part.Key) → part.Answer (D := D) k)
    (p : Sampling Raw (fun _ => D) R n) :
    Sampling.eval table (part.program schedule caller final p) =
      Sampling.eval (part.join table) p := by
  induction p with
  | ret r =>
    simp only [program]
    split <;> simp [Sampling.eval]
  | draw raw next ih => simp [program, eval_request, Sampling.eval, ih]

variable [DecidableEq Packet] [DecidableEq Raw]
variable [Fintype Raw] [Fintype Packet] [∀ p, Fintype (Block p)]
variable [Fintype D] [Nonempty D]

instance : Fintype part.Garbage := inferInstanceAs (Fintype {raw // part.recognize raw = none})
noncomputable instance (k : part.Key) : Fintype (part.Answer (D := D) k) := by
  classical
  cases k <;> simp only [Answer] <;> infer_instance
instance (k : part.Key) : Nonempty (part.Answer (D := D) k) := by
  cases k <;> simp only [Answer] <;> infer_instance

/-- Exact raw finite-table to lazy whole-packet/garbage distribution equality.
Neither arbitrary full-input injection nor an equal-distribution premise occurs. -/
theorem raw_table_eq_packets {R : Type u} {B C n} (schedule : Schedule Packet B)
    (caller : CallerPlan Packet part.Garbage C) (final : R → Option Packet)
    (p : Sampling Raw (fun _ => D) R n) (payoff : R → ℚ) :
    average (fun table : Raw → D => payoff (Sampling.eval table p)) =
      Sampling.expectation (fun result => payoff result.1)
        (memo (part.program schedule caller final p) (fun _ => none)) := by
  rw [← empty_table_eq_memo]
  simp only [eval_program]
  have h := average_equiv part.tableEquiv
    (fun table => payoff (Sampling.eval (part.join table) p))
  simpa only [tableEquiv, Equiv.coe_fn_mk, join_split] using h

omit [Fintype Raw] [Fintype Packet] [∀ p, Fintype (Block p)] [Fintype D] [Nonempty D] in
theorem all_branch_cap {R : Type u} {B C n} (schedule : Schedule Packet B)
    (caller : CallerPlan Packet part.Garbage C) (final : R → Option Packet)
    (p : Sampling Raw (fun _ => D) R n) {trace result}
    (run : Sampling.Runs
      (memo (part.program schedule caller final p) (fun _ => none)) trace result) :
    trace.length ≤ (B+C)*(n+1) := by simpa [Nat.mul_add] using run.length_le

end Partition

section Relabel
variable {Key : Type u} {Answer : Key → Type v}
variable {Target : Type u} {Fiber : Target → Type v}
variable [DecidableEq Key]

/-- A label is computed from already allocated private state. The equivalence
changes only representation of the selected fiber; it does not identify
arbitrary full inputs with raw keys. -/
structure Labeling (Key : Type u) (Answer : Key → Type v)
    (Target : Type u) (Fiber : Target → Type v) where
  key : Cache Key Answer → Key → Target
  answer : ∀ cache k, Fiber (key cache k) ≃ Answer k

def relabelMemo (labels : Labeling Key Answer Target Fiber) {R : Type w} {n} :
    Sampling Key Answer R n → Cache Key Answer →
      Sampling Target Fiber (R × Cache Key Answer) n
  | .ret r, cache => .ret (r,cache)
  | .draw k next, cache =>
    match cache k with
    | some a => Sampling.pad (Nat.le_succ _) (relabelMemo labels (next a) cache)
    | none => .draw (labels.key cache k) (fun fresh =>
        let a := labels.answer cache k fresh
        relabelMemo labels (next a) (put cache k a))

variable [∀ k, Fintype (Answer k)] [∀ k, Nonempty (Answer k)]
variable [∀ k, Fintype (Fiber k)] [∀ k, Nonempty (Fiber k)]

omit [∀ k, Nonempty (Answer k)] [∀ k, Nonempty (Fiber k)] in
/-- Distribution-preserving canonical relabeling is operational and local to
each miss. It requires no full-key injection and no preexisting cache invariant. -/
theorem relabelMemo_expectation (labels : Labeling Key Answer Target Fiber)
    {R : Type w} {n} (p : Sampling Key Answer R n) (cache : Cache Key Answer)
    (payoff : R × Cache Key Answer → ℚ) :
    Sampling.expectation payoff (relabelMemo labels p cache) =
      Sampling.expectation payoff (memo p cache) := by
  induction p generalizing cache with
  | ret r => rfl
  | draw k next ih =>
    cases hit : cache k with
    | some a => simpa only [relabelMemo, memo, hit, Sampling.expectation_pad] using ih a cache
    | none =>
      simp only [relabelMemo, memo, hit, Sampling.expectation, ih]
      exact average_equiv (labels.answer cache k)
        (fun a => Sampling.expectation payoff (memo (next a) (put cache k a)))

variable [Fintype Key]

omit [∀ k, Nonempty (Fiber k)] in
theorem table_eq_relabelMemo (labels : Labeling Key Answer Target Fiber)
    {R : Type w} {n} (p : Sampling Key Answer R n) (payoff : R → ℚ) :
    average (fun table => payoff (Sampling.eval table p)) =
      Sampling.expectation (fun result => payoff result.1)
        (relabelMemo labels p (fun _ => none)) := by
  rw [relabelMemo_expectation]
  exact empty_table_eq_memo p payoff

end Relabel
end Whir.RawOracleCoupling
