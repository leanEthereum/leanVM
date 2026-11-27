import LeanSphincsProofs.Hasher
import Hash.Keccak.Fast

/-!
# `keccak256::keccak_f` is Keccak-f[1600]

The extracted Rust permutation (`keccak256::lanes::permute` at `u64`) against the lane-level
reference of `hash-specs`, `Hash.Keccak.Fast.keccakF`.

The Rust round keeps the column parities `c` across rounds, takes θ's `d` from them, builds each
output row before χ with `pi_row` (θ, ρ and π at once), and writes χ of the row (ι in row 0) back
into the state while rebuilding the parities. The proof follows that shape: the lane operations
and the three inner loops are computed (`theta`, `chi_row`, the loop over the rows), giving one
round as a function on lists (`roundU`); that function is the reference's `round`
(`roundU_round`) and leaves the parities of its output (`roundU_par`); the 24 rounds are an
induction over the outer loop.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open LeanVM.Semantics (KeccakState)
open LeanVM.Semantics.Keccak (lane)
open LeanVM.Protocol.KeccakHash

namespace LeanSphincsProofs

/-- A Rust state's lanes, as hash-specs' fast Keccak takes them. -/
def lanesOf (a : Array Std.U64 25#usize) : _root_.Array UInt64 := (a.val.map lane64).toArray

namespace Permutation
open keccak256

/-- A program that meets a specification returns a value that satisfies it. -/
theorem exists_of_spec {α : Type} {m : RustM α} {P : α → Prop} (h : m ⦃ y => P y ⦄) :
    ∃ y, m = ok y ∧ P y := by
  cases m with
  | ret a => exact ⟨a, rfl, (WP.spec_ok a).1 h⟩
  | vis i k => exact ((WP.spec_vis i k).1 h).elim
  | div => exact (WP.spec_div.1 h).elim

/-- Rotate left, on a Rust lane. -/
def rl (x : Std.U64) (n : ℕ) : Std.U64 := ⟨x.bv <<< n ||| x.bv >>> (64 - n)⟩

/-! ## The lane operations of `u64` -/

theorem chi_eq (a b c : Std.U64) :
    U64.Insts.Keccak256LanesLane.chi a b c = ok (a ^^^ (~~~b &&& c)) := by
  simp [U64.Insts.Keccak256LanesLane.chi, lift]

/-- The two halves of a rotation share no bit: the library's XOR of them is the OR. -/
theorem xor_or (x : BitVec 64) (n : ℕ) (h0 : 0 < n) (h : n < 64) :
    x <<< n ^^^ x >>> (64 - n) = x <<< n ||| x >>> (64 - n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hin : i < n
  · simp [hin]
  · have : 64 ≤ 64 - n + i := by omega
    simp [BitVec.getLsbD_of_ge _ _ this]

/-- `rotl::<N>` for `0 < N < 64`. -/
theorem rotl_spec (N : Std.I32) (x : Std.U64) (h0 : 0 < N.val) (h : N.val < 64) :
    U64.Insts.Keccak256LanesLane.rotl N x ⦃ r => r = rl x N.val.toNat ⦄ := by
  unfold U64.Insts.Keccak256LanesLane.rotl core.num.U64.rotate_left
  have hc := IScalar.hcast_inBounds_spec .U32 N (by scalar_tac)
  step*
  have hm : m.val = N.val.toNat := by scalar_tac
  rw [UScalar.eq_equiv_bv_eq]
  simp only [UScalar.bv_xor, i_post1, i2_post1, rl, i1_post, hm]
  exact xor_or _ _ (by omega) (by omega)

theorem lane64_xor (a b : Std.U64) : lane64 (a ^^^ b) = lane64 a ^^^ lane64 b := rfl
theorem lane64_rl (a : Std.U64) (n : ℕ) (h0 : 0 < n) (h : n < 64) :
    lane64 (rl a n) = Hash.UInt64.rotl (lane64 a) n.toUInt64 := by
  simp only [lane64, rl, Hash.UInt64.rotl]
  apply UInt64.toBitVec_inj.mp
  have h1 : n % 64 = n := by omega
  have h2 : (18446744073709551616 - n % 18446744073709551616) % 64 = 64 - n := by omega
  simp [h1, h2]
theorem rotl_zero (a : UInt64) : Hash.UInt64.rotl a 0 = a := by
  apply UInt64.toBitVec_inj.mp
  simp [Hash.UInt64.rotl]


@[step] theorem xor_spec (a b : Std.U64) :
    U64.Insts.Keccak256LanesLane.xor a b ⦃ r => r = a ^^^ b ⦄ := (WP.spec_ok _).2 rfl
@[step] theorem chi_spec (a b c : Std.U64) :
    U64.Insts.Keccak256LanesLane.chi a b c ⦃ r => r = a ^^^ (~~~b &&& c) ⦄ := by
  rw [chi_eq]; exact (WP.spec_ok _).2 rfl
@[step] theorem splat_spec (a : Std.U64) :
    U64.Insts.Keccak256LanesLane.splat a ⦃ r => r = a ⦄ := (WP.spec_ok _).2 rfl
attribute [step] rotl_spec

/-! ## Ranges and loops -/

theorem range_step (i e s : Std.Usize) (h : i.val < e.val) (hs : s.val = i.val + 1) :
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep { start := i, «end» := e } =
        ok (some i, { start := s, «end» := e }) := by
  obtain ⟨s', hs', h'⟩ := range_next_lt i e h
  have : s' = s := UScalar.eq_of_val_eq (by omega)
  subst this
  exact h'

theorem range_stop (i e : Std.Usize) (h : e.val ≤ i.val) :
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep { start := i, «end» := e } =
        ok (none, { start := i, «end» := e }) := range_next_ge i e h



/-! ## θ -/

@[step] theorem t_spec (a : Array Std.U64 25#usize) (d : Array Std.U64 5#usize) (i : Std.Usize) (h : i.val < 25) :
    lanes.t U64.Insts.Keccak256LanesLane a d i ⦃ r => r = a.val[i.val]! ^^^ d.val[i.val % 5]! ⦄ := by
  unfold lanes.t
  step*
  have hd : i.val % 5 < d.val.length := by scalar_tac
  have ha : i.val < a.val.length := by scalar_tac
  simp_all [getElem!_pos]
theorem theta_body (c d : Array Std.U64 5#usize) (x s : Std.Usize) (hx : x.val < 5) (hs : s.val = x.val + 1) :
    lanes.theta_loop.body U64.Insts.Keccak256LanesLane c { start := x, «end» := 5#usize } d = ok (
      .cont ({ start := s, «end» := 5#usize }, d.set x (c.val[(x.val + 4) % 5]! ^^^ rl c.val[(x.val + 1) % 5]! 1))) := by
  have : lanes.theta_loop.body U64.Insts.Keccak256LanesLane c { start := x, «end» := 5#usize } d ⦃ r => r = 
      .cont ({ start := s, «end» := 5#usize }, d.set x (c.val[(x.val + 4) % 5]! ^^^ rl c.val[(x.val + 1) % 5]! 1)) ⦄ := by
    unfold lanes.theta_loop.body
    rw [range_step x _ s (by scalar_tac) hs]
    simp only [Aeneas.Std.bind_ok]
    have h1 : (x.val + 4) % 5 < c.val.length := by scalar_tac
    have h2 : (x.val + 1) % 5 < c.val.length := by scalar_tac
    step*
    simp_all [getElem!_pos]
  obtain ⟨y, hy, rfl⟩ := exists_of_spec this
  exact hy


theorem list5 {α : Type} : ∀ l : List α, l.length = 5 → ∃ x0 x1 x2 x3 x4, l = [x0, x1, x2, x3, x4]
  | [x0, x1, x2, x3, x4], _ => ⟨x0, x1, x2, x3, x4, rfl⟩

theorem arr5 {α : Type} (a : Array α 5#usize) :
    ∃ x0 x1 x2 x3 x4, a = Array.make 5#usize [x0, x1, x2, x3, x4] := by
  obtain ⟨x0, x1, x2, x3, x4, h⟩ := list5 a.val a.property
  exact ⟨x0, x1, x2, x3, x4, Aeneas.Std.Array.ext _ _ (by simpa using h)⟩

theorem list25 {α : Type} : ∀ l : List α, l.length = 25 →
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
      x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24,
      l = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12,
        x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24]
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12,
      x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24], _ =>
    ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12,
      x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, rfl⟩

theorem loop_cont {α β : Type} (body : α → RustM (ControlFlow α β)) (x x' : α)
    (h : body x = ok (.cont x')) : loop body x = loop body x' := by
  rw [loop.eq_def, h, Aeneas.Std.bind_ok]

theorem loop_done {α β : Type} (body : α → RustM (ControlFlow α β)) (x : α) (y : β)
    (h : body x = ok (.done y)) : loop body x = ok y := by
  rw [loop.eq_def, h, Aeneas.Std.bind_ok]

theorem theta_done (c d : Array Std.U64 5#usize) :
    lanes.theta_loop.body U64.Insts.Keccak256LanesLane c { start := 5#usize, «end» := 5#usize } d =
      ok (.done d) := by
  unfold lanes.theta_loop.body
  rw [range_stop _ _ (by simp)]
  simp

/-- θ's `d`, from the column parities. -/
def thetaD (c : List Std.U64) : List Std.U64 :=
  [c[4]! ^^^ rl c[1]! 1, c[0]! ^^^ rl c[2]! 1, c[1]! ^^^ rl c[3]! 1, c[2]! ^^^ rl c[4]! 1,
    c[3]! ^^^ rl c[0]! 1]

@[step] theorem theta_spec (c : Array Std.U64 5#usize) :
    lanes.theta U64.Insts.Keccak256LanesLane c ⦃ r => r.val = thetaD c.val ⦄ := by
  unfold lanes.theta lanes.theta_loop
  rw [loop_cont _ _ _ (theta_body c _ 0#usize 1#usize (by simp) (by simp)),
    loop_cont _ _ _ (theta_body c _ 1#usize 2#usize (by simp) (by simp)),
    loop_cont _ _ _ (theta_body c _ 2#usize 3#usize (by simp) (by simp)),
    loop_cont _ _ _ (theta_body c _ 3#usize 4#usize (by simp) (by simp)),
    loop_cont _ _ _ (theta_body c _ 4#usize 5#usize (by simp) (by simp)),
    loop_done _ _ _ (theta_done c _)]
  rw [WP.spec_ok]
  obtain ⟨c0, c1, c2, c3, c4, rfl⟩ := arr5 c
  simp [thetaD]


/-! ## ρ and π: a row before χ -/

/-- Row `y` of the state after θ, ρ and π, from the state `a` and θ's `d`. -/
def piRow (a d : List Std.U64) : ℕ → List Std.U64
  | 0 => [a[0]! ^^^ d[0]!, rl (a[6]! ^^^ d[1]!) 44, rl (a[12]! ^^^ d[2]!) 43, rl (a[18]! ^^^ d[3]!) 21, rl (a[24]! ^^^ d[4]!) 14]
  | 1 => [rl (a[3]! ^^^ d[3]!) 28, rl (a[9]! ^^^ d[4]!) 20, rl (a[10]! ^^^ d[0]!) 3, rl (a[16]! ^^^ d[1]!) 45, rl (a[22]! ^^^ d[2]!) 61]
  | 2 => [rl (a[1]! ^^^ d[1]!) 1, rl (a[7]! ^^^ d[2]!) 6, rl (a[13]! ^^^ d[3]!) 25, rl (a[19]! ^^^ d[4]!) 8, rl (a[20]! ^^^ d[0]!) 18]
  | 3 => [rl (a[4]! ^^^ d[4]!) 27, rl (a[5]! ^^^ d[0]!) 36, rl (a[11]! ^^^ d[1]!) 10, rl (a[17]! ^^^ d[2]!) 15, rl (a[23]! ^^^ d[3]!) 56]
  | _ => [rl (a[2]! ^^^ d[2]!) 62, rl (a[8]! ^^^ d[3]!) 55, rl (a[14]! ^^^ d[4]!) 39, rl (a[15]! ^^^ d[0]!) 41, rl (a[21]! ^^^ d[1]!) 2]

@[step] theorem pi_row0 (a : Array Std.U64 25#usize) (d : Array Std.U64 5#usize) :
    lanes.pi_row U64.Insts.Keccak256LanesLane a d 0#usize ⦃ r => r.val = piRow a.val d.val 0 ⦄ := by
  unfold lanes.pi_row
  simp only [show (0#usize).val = 0 from rfl]
  step*
  simp_all [piRow]

@[step] theorem pi_row1 (a : Array Std.U64 25#usize) (d : Array Std.U64 5#usize) :
    lanes.pi_row U64.Insts.Keccak256LanesLane a d 1#usize ⦃ r => r.val = piRow a.val d.val 1 ⦄ := by
  unfold lanes.pi_row
  simp only [show (1#usize).val = 1 from rfl]
  step*
  simp_all [piRow]

@[step] theorem pi_row2 (a : Array Std.U64 25#usize) (d : Array Std.U64 5#usize) :
    lanes.pi_row U64.Insts.Keccak256LanesLane a d 2#usize ⦃ r => r.val = piRow a.val d.val 2 ⦄ := by
  unfold lanes.pi_row
  simp only [show (2#usize).val = 2 from rfl]
  step*
  simp_all [piRow]

@[step] theorem pi_row3 (a : Array Std.U64 25#usize) (d : Array Std.U64 5#usize) :
    lanes.pi_row U64.Insts.Keccak256LanesLane a d 3#usize ⦃ r => r.val = piRow a.val d.val 3 ⦄ := by
  unfold lanes.pi_row
  simp only [show (3#usize).val = 3 from rfl]
  step*
  simp_all [piRow]

@[step] theorem pi_row4 (a : Array Std.U64 25#usize) (d : Array Std.U64 5#usize) :
    lanes.pi_row U64.Insts.Keccak256LanesLane a d 4#usize ⦃ r => r.val = piRow a.val d.val 4 ⦄ := by
  unfold lanes.pi_row
  simp only [show (4#usize).val = 4 from rfl]
  step*
  simp_all [piRow]

/-! ## The column parities -/

/-- The column parities of a state. -/
def par (l : List Std.U64) : List Std.U64 :=
  [l[0]! ^^^ l[5]! ^^^ l[10]! ^^^ l[15]! ^^^ l[20]!, l[1]! ^^^ l[6]! ^^^ l[11]! ^^^ l[16]! ^^^ l[21]!, l[2]! ^^^ l[7]! ^^^ l[12]! ^^^ l[17]! ^^^ l[22]!, l[3]! ^^^ l[8]! ^^^ l[13]! ^^^ l[18]! ^^^ l[23]!, l[4]! ^^^ l[9]! ^^^ l[14]! ^^^ l[19]! ^^^ l[24]!]

theorem xor5_spec (a b c d e : Std.U64) :
    lanes.Lane.xor5.default U64.Insts.Keccak256LanesLane a b c d e ⦃ r => r = a ^^^ b ^^^ c ^^^ d ^^^ e ⦄ := by
  unfold lanes.Lane.xor5.default
  step*

theorem parities_spec (a : Array Std.U64 25#usize) :
    lanes.parities U64.Insts.Keccak256LanesLane a ⦃ r => r.val = par a.val ⦄ := by
  unfold lanes.parities
  step*
  simp_all [par]

/-! ## χ and ι on a row, written into the state -/

/-- χ on a lane. -/
def chi1 (a b c : Std.U64) : Std.U64 := a ^^^ (~~~b &&& c)

theorem lane64_chi1 (a b c : Std.U64) :
    lane64 (chi1 a b c) = lane64 a ^^^ (~~~lane64 b &&& lane64 c) := rfl

/-- χ on a row. -/
def chiRow (b : List Std.U64) : List Std.U64 :=
  [chi1 b[0]! b[1]! b[2]!, chi1 b[1]! b[2]! b[3]!, chi1 b[2]! b[3]! b[4]!, chi1 b[3]! b[4]! b[0]!,
    chi1 b[4]! b[0]! b[1]!]

/-- ι on row `y`: the round constant into lane 0 of row 0. -/
def iotaRow (y : ℕ) (rc : Std.U64) (r : List Std.U64) : List Std.U64 :=
  if y = 0 then r.set 0 (r[0]! ^^^ rc) else r

/-- One lane of row `y` written into the state, and into the parities. -/
def chiStep (y : ℕ) (r : List Std.U64) (s : List Std.U64 × List Std.U64) (x : ℕ) :
    List Std.U64 × List Std.U64 :=
  (s.1.set (5 * y + x) r[x]!, s.2.set x (if y = 0 then r[x]! else s.2[x]! ^^^ r[x]!))

theorem chi_body (y : Std.Usize) (r : Array Std.U64 5#usize) (x s : Std.Usize)
    (out : Array Std.U64 25#usize) (c : Array Std.U64 5#usize) (k : ℕ) (hy : y.val < 5)
    (hk : x.val = k) (hx : k < 5) (hs : s.val = k + 1) :
    ∃ o' c', lanes.chi_row_loop.body U64.Insts.Keccak256LanesLane y r
        { start := x, «end» := 5#usize } out c = ok (.cont ({ start := s, «end» := 5#usize }, o', c')) ∧
      (o'.val, c'.val) = chiStep y.val r.val (out.val, c.val) k := by
  have : lanes.chi_row_loop.body U64.Insts.Keccak256LanesLane y r
        { start := x, «end» := 5#usize } out c ⦃ q => ∃ o' c', 
          q = .cont ({ start := s, «end» := 5#usize }, o', c') ∧
          (o'.val, c'.val) = chiStep y.val r.val (out.val, c.val) k ⦄ := by
    subst hk
    unfold lanes.chi_row_loop.body
    rw [range_step x _ s (by scalar_tac) hs]
    simp only [Aeneas.Std.bind_ok]
    have h1 : x.val < r.val.length := by scalar_tac
    have h2 : x.val < c.val.length := by scalar_tac
    by_cases hy0 : y = 0#usize
    · have hv : y.val = 0 := by simp [hy0]
      simp only [hy0, ↓reduceIte]
      step*
      refine ⟨_, _, rfl, ?_⟩
      simp_all [chiStep, getElem!_pos]
    · have hv : y.val ≠ 0 := by scalar_tac
      simp only [hy0, ↓reduceIte]
      step*
      refine ⟨_, _, rfl, ?_⟩
      simp_all [chiStep, getElem!_pos]
  obtain ⟨q, hq, o', c', rfl, h⟩ := exists_of_spec this
  exact ⟨o', c', hq, h⟩


theorem chi_done (y : Std.Usize) (r : Array Std.U64 5#usize) (out : Array Std.U64 25#usize)
    (c : Array Std.U64 5#usize) :
    lanes.chi_row_loop.body U64.Insts.Keccak256LanesLane y r
      { start := 5#usize, «end» := 5#usize } out c = ok (.done (out, c)) := by
  unfold lanes.chi_row_loop.body
  rw [range_stop _ _ (by simp)]
  simp

@[step] theorem chi_loop (y : Std.Usize) (r : Array Std.U64 5#usize) (o0 : Array Std.U64 25#usize)
    (c0 : Array Std.U64 5#usize) (hy : y.val < 5) :
    lanes.chi_row_loop U64.Insts.Keccak256LanesLane { start := 0#usize, «end» := 5#usize } o0 c0 y r
      ⦃ q => (q.1.val, q.2.val) = [0, 1, 2, 3, 4].foldl (chiStep y.val r.val) (o0.val, c0.val) ⦄ := by
  obtain ⟨o1, c1, e1, h1⟩ := chi_body y r 0#usize 1#usize o0 c0 0 hy (by simp) (by simp) (by simp)
  obtain ⟨o2, c2, e2, h2⟩ := chi_body y r 1#usize 2#usize o1 c1 1 hy (by simp) (by simp) (by simp)
  obtain ⟨o3, c3, e3, h3⟩ := chi_body y r 2#usize 3#usize o2 c2 2 hy (by simp) (by simp) (by simp)
  obtain ⟨o4, c4, e4, h4⟩ := chi_body y r 3#usize 4#usize o3 c3 3 hy (by simp) (by simp) (by simp)
  obtain ⟨o5, c5, e5, h5⟩ := chi_body y r 4#usize 5#usize o4 c4 4 hy (by simp) (by simp) (by simp)
  unfold lanes.chi_row_loop
  rw [loop_cont _ _ _ e1, loop_cont _ _ _ e2, loop_cont _ _ _ e3, loop_cont _ _ _ e4,
    loop_cont _ _ _ e5, loop_done _ _ _ (chi_done y r o5 c5), WP.spec_ok]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [h5, h4, h3, h2, h1]

/-- Row `y` of the round's output written into the state and the parities: χ, and ι in row 0. -/
def rowStep (rc : Std.U64) (s : List Std.U64 × List Std.U64) (y : ℕ) (row : List Std.U64) :
    List Std.U64 × List Std.U64 :=
  [0, 1, 2, 3, 4].foldl (chiStep y (iotaRow y rc (chiRow row))) s

theorem chi_row_spec (out : Array Std.U64 25#usize) (c : Array Std.U64 5#usize) (y : Std.Usize)
    (a : Array Std.U64 5#usize) (rc : Std.U64) (hy : y.val < 5) :
    lanes.chi_row U64.Insts.Keccak256LanesLane out c y a rc
      ⦃ q => (q.1.val, q.2.val) = rowStep rc (out.val, c.val) y.val a.val ⦄ := by
  unfold lanes.chi_row
  by_cases hy0 : y = 0#usize
  · simp only [hy0, ↓reduceIte]
    step*
    have hr : r.val = iotaRow 0 rc (chiRow a.val) := by simp_all [iotaRow, chiRow, chi1]
    rw [q_post, hr]
    simp [rowStep]
  · have hv : y.val ≠ 0 := by scalar_tac
    simp only [hy0, ↓reduceIte]
    step*
    have hr : (Array.make 5#usize [t, t1, t2, t3, t4]).val = iotaRow y.val rc (chiRow a.val) := by
      simp_all [iotaRow, chiRow, chi1]
    rw [q_post, hr]
    rfl

/-! ## The loop over the rows -/

/-- One step of `rows.iter().enumerate()`: the next row and its number. -/
theorem enumerate_next {T : Type} (s : Slice T) (x : T) (xs : List T) (c : Std.Usize)
    (hs : s.val = x :: xs) (hc : c.val + 1 ≤ Usize.max) :
    ∃ it, core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
        (core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)
        { iter := s, count := c } = ok (core.option.Option.Some (c, x), it) ∧
      it.iter.val = xs ∧ it.count.val = c.val + 1 := by
  have hlen : s.val.length = xs.length + 1 := by simp [hs]
  have hne : ¬ (Slice.len s = 0#usize) := by
    intro h
    have : (Slice.len s).val = 0 := by rw [h]; rfl
    scalar_tac
  have t : ⦃ ⌜ True ⌝ ⦄
      core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
        (core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)
        { iter := s, count := c }
      ⦃ ⇓ r => ⌜ r.1 = core.option.Option.Some (c, x) ∧ r.2.iter.val = xs ∧
        r.2.count.val = c.val + 1 ⌝ ⦄ := by
    hax_mvcgen [core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next,
      core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      rust_primitives.sequence.seq_len, rust_primitives.sequence.seq_remove]
    case vc2.hQ =>
      rename_i r hr
      refine ⟨?_, ?_, ?_⟩
      · simp [hs]
      · simp [hs]
      · scalar_tac
    case vc3.h_fail => scalar_tac
    case vc4.hQ => rename_i h; exact absurd (by simp [hlen] : (0#usize).val < s.val.length) h
  obtain ⟨⟨o, it⟩, hr, h0, h1, h2⟩ := ok_of_triple t
  exact ⟨it, by rw [hr]; simp only at h0; rw [h0], h1, h2⟩

/-- The iterator, once every row is taken, gives none. -/
theorem enumerate_next_nil {T : Type} (s : Slice T) (c : Std.Usize) (hs : s.val = []) :
    core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
        (core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)
        { iter := s, count := c } =
      ok (core.option.Option.None, { iter := s, count := c }) := by
  have h0 : Slice.len s = 0#usize := by
    rw [UScalar.eq_equiv]
    simp [hs]
  simp [core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next,
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
    rust_primitives.sequence.seq_len, h0]
  rfl

theorem rows_body (rc : Std.U64)
    (it : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (Array Std.U64 5#usize)))
    (a : Array Std.U64 25#usize) (c : Array Std.U64 5#usize) (row : Array Std.U64 5#usize)
    (rest : List (Array Std.U64 5#usize)) (k : ℕ) (hit : it.iter.val = row :: rest)
    (hk : it.count.val = k) (hk5 : k < 5) :
    ∃ it' a' c', lanes.permute_loop0_loop0.body U64.Insts.Keccak256LanesLane rc it a c =
        ok (.cont (it', a', c')) ∧ it'.iter.val = rest ∧ it'.count.val = k + 1 ∧
      (a'.val, c'.val) = rowStep rc (a.val, c.val) k row.val := by
  obtain ⟨s, n⟩ := it
  obtain ⟨it', e, h1, h2⟩ := enumerate_next s row rest n hit (by scalar_tac)
  obtain ⟨⟨a', c'⟩, e', h⟩ := exists_of_spec (chi_row_spec a c n row rc (by scalar_tac))
  refine ⟨it', a', c', ?_, h1, by simp_all, by simp_all⟩
  unfold lanes.permute_loop0_loop0.body
  rw [e]
  simp [e']

theorem rows_done (rc : Std.U64)
    (it : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (Array Std.U64 5#usize)))
    (a : Array Std.U64 25#usize) (c : Array Std.U64 5#usize) (hit : it.iter.val = []) :
    lanes.permute_loop0_loop0.body U64.Insts.Keccak256LanesLane rc it a c = ok (.done (a, c)) := by
  obtain ⟨s, n⟩ := it
  unfold lanes.permute_loop0_loop0.body
  rw [enumerate_next_nil s n hit]
  simp

theorem rows_loop (rc : Std.U64)
    (it : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (Array Std.U64 5#usize)))
    (a0 : Array Std.U64 25#usize) (c0 : Array Std.U64 5#usize) (r0 r1 r2 r3 r4 : Array Std.U64 5#usize)
    (hit : it.iter.val = [r0, r1, r2, r3, r4]) (hk : it.count.val = 0) :
    ∃ a' c', lanes.permute_loop0_loop0 U64.Insts.Keccak256LanesLane it a0 c0 rc = ok (a', c') ∧
      (a'.val, c'.val) = rowStep rc (rowStep rc (rowStep rc (rowStep rc (rowStep rc (a0.val, c0.val)
        0 r0.val) 1 r1.val) 2 r2.val) 3 r3.val) 4 r4.val := by
  obtain ⟨i1, a1, c1, e1, t1, k1, h1⟩ := rows_body rc it a0 c0 r0 _ 0 hit hk (by simp)
  obtain ⟨i2, a2, c2, e2, t2, k2, h2⟩ := rows_body rc i1 a1 c1 r1 _ 1 t1 k1 (by simp)
  obtain ⟨i3, a3, c3, e3, t3, k3, h3⟩ := rows_body rc i2 a2 c2 r2 _ 2 t2 k2 (by simp)
  obtain ⟨i4, a4, c4, e4, t4, k4, h4⟩ := rows_body rc i3 a3 c3 r3 _ 3 t3 k3 (by simp)
  obtain ⟨i5, a5, c5, e5, t5, k5, h5⟩ := rows_body rc i4 a4 c4 r4 _ 4 t4 k4 (by simp)
  refine ⟨a5, c5, ?_, ?_⟩
  · unfold lanes.permute_loop0_loop0
    rw [loop_cont _ _ _ e1, loop_cont _ _ _ e2, loop_cont _ _ _ e3, loop_cont _ _ _ e4,
      loop_cont _ _ _ e5, loop_done _ _ _ (rows_done rc i5 a5 c5 t5)]
  · rw [h5, h4, h3, h2, h1]

/-- One round, on the state and its column parities. -/
def roundU (a c : List Std.U64) (rc : Std.U64) : List Std.U64 × List Std.U64 :=
  rowStep rc (rowStep rc (rowStep rc (rowStep rc (rowStep rc (a, c)
    0 (piRow a (thetaD c) 0)) 1 (piRow a (thetaD c) 1)) 2 (piRow a (thetaD c) 2))
    3 (piRow a (thetaD c) 3)) 4 (piRow a (thetaD c) 4)

theorem round_body (i e s : Std.Usize) (a : Array Std.U64 25#usize) (c : Array Std.U64 5#usize)
    (h : i.val < e.val) (h24 : i.val < 24) (hs : s.val = i.val + 1) :
    ∃ a' c', lanes.permute_loop0.body U64.Insts.Keccak256LanesLane { start := i, «end» := e } a c =
        ok (.cont ({ start := s, «end» := e }, a', c')) ∧
      (a'.val, c'.val) = roundU a.val c.val RC.val[i.val]! := by
  have : lanes.permute_loop0.body U64.Insts.Keccak256LanesLane { start := i, «end» := e } a c ⦃ q =>
      ∃ a' c', q = .cont ({ start := s, «end» := e }, a', c') ∧
        (a'.val, c'.val) = roundU a.val c.val RC.val[i.val]! ⦄ := by
    unfold lanes.permute_loop0.body
    rw [range_step i e s h hs]
    simp only [Aeneas.Std.bind_ok]
    step*
    simp only [core.array.Array.as_slice, rust_primitives.slice.array_as_slice,
      core.slice.Slice.iter, rust_primitives.sequence.seq_from_slice,
      core.iter.traits.iterator.Iterator.enumerate.default,
      core.iter.adapters.enumerate.Enumerate.new, Aeneas.Std.bind_ok]
    obtain ⟨a', c', el, hl⟩ := rows_loop rc
      { iter := (Array.make 5#usize [a1, a2, a3, a4, a5]).to_slice, count := 0#usize } a c
      a1 a2 a3 a4 a5 (by simp) (by simp)
    erw [Aeneas.Std.bind_ok, Aeneas.Std.bind_ok, el, Aeneas.Std.bind_ok]
    refine (WP.spec_ok _).2 ?_
    have hrc : rc = RC.val[i.val]! := by
      have : i.val < RC.val.length := rc_post
      rw [rc_post1, getElem!_pos RC.val i.val this]
    refine ⟨a', c', rfl, ?_⟩
    rw [hl, a1_post, a2_post, a3_post, a4_post, a5_post, d_post, hrc]
    rfl
  obtain ⟨q, hq, a', c', rfl, h⟩ := exists_of_spec this
  exact ⟨a', c', hq, h⟩


/-! ## The round, against the reference -/

/-- The parities a round leaves are those of the state it leaves, whatever they were before. -/
theorem roundU_par (l c : List Std.U64) (hl : l.length = 25) (hc : c.length = 5) (rc : Std.U64) :
    (roundU l c rc).2 = par (roundU l c rc).1 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
    a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, rfl⟩ := list25 l hl
  generalize thetaD c = d
  obtain ⟨c0, c1, c2, c3, c4, rfl⟩ := list5 c hc
  simp [roundU, rowStep, chiStep, iotaRow, chiRow, piRow, par]

open Hash.Keccak.Fast in
/-- **One round of the Rust is one round of the reference.** -/
theorem roundU_round (l : List Std.U64) (hl : l.length = 25) (rc : Std.U64) (ir : ℕ)
    (hrc : lane64 rc = roundConstantWords.getD ir 0) :
    ((roundU l (par l) rc).1.map lane64).toArray = Hash.Keccak.Fast.round (l.map lane64).toArray ir := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
    a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, rfl⟩ := list25 l hl
  simp [roundU, rowStep, chiStep, iotaRow, chiRow, piRow, par, thetaD, lane64_xor, lane64_chi1,
    lane64_rl, hrc, Hash.Keccak.Fast.round, iota, chi, pi, rho, theta, tabulate, Hash.Keccak.Fast.lane, List.range_succ, rhoRotations,
    Hash.Keccak.rhoOffsets, rotl_zero]

/-! ## The round constants -/

theorem RC_words :
    RC.val.map lane64 = Hash.Keccak.Fast.roundConstantWords.toList := by
  simp [RC, Hash.Keccak.Fast.roundConstantWords, Hash.Keccak.roundConstants, lane64]

theorem rc_word (i : ℕ) (h : i < 24) :
    lane64 RC.val[i]! = Hash.Keccak.Fast.roundConstantWords.getD i 0 := by
  have h1 : i < RC.val.length := by simpa using h
  have h2 : i < Hash.Keccak.Fast.roundConstantWords.size := by
    rw [← Array.length_toList, ← RC_words]; simpa using h
  have := congrArg (fun l => l[i]?) RC_words
  simp only [List.getElem?_map, List.getElem?_eq_getElem h1, Option.map_some,
    Array.getElem?_toList, Array.getElem?_eq_getElem h2] at this
  rw [getElem!_pos RC.val i h1, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2]
  simpa using this

/-! ## The rounds -/

/-- A loop whose body returns, keeps `inv` and decreases `μ` returns, with `Q`. -/
theorem loop_induct {α β : Type} (body : α → RustM (ControlFlow α β)) (inv : α → Prop)
    (Q : β → Prop) (μ : α → Nat)
    (hstep : ∀ x, inv x → ∃ r, body x = ok r ∧
      (match r with
        | .cont x' => inv x' ∧ μ x' < μ x
        | .done y => Q y)) :
    ∀ x, inv x → ∃ y, loop body x = ok y ∧ Q y := by
  intro x
  induction h : μ x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro hx
    obtain ⟨r, hr, hpost⟩ := hstep x hx
    rw [loop.eq_def, hr, Aeneas.Std.bind_ok]
    cases r with
    | cont x' =>
      obtain ⟨hi, hlt⟩ := hpost
      exact ih _ (h ▸ hlt) x' rfl hi
    | done y => exact ⟨y, rfl, hpost⟩

theorem round_done (i e : Std.Usize) (a : Array Std.U64 25#usize) (c : Array Std.U64 5#usize)
    (h : e.val ≤ i.val) :
    lanes.permute_loop0.body U64.Insts.Keccak256LanesLane { start := i, «end» := e } a c =
      ok (.done a) := by
  unfold lanes.permute_loop0.body
  rw [range_stop _ _ h]
  simp

theorem rounds (e : Std.Usize) (he : e.val = 24) (a0 : Array Std.U64 25#usize)
    (c0 : Array Std.U64 5#usize) (hc : c0.val = par a0.val) :
    ∃ a', lanes.permute_loop0 U64.Insts.Keccak256LanesLane { start := 0#usize, «end» := e } a0 c0 =
        ok a' ∧ lanesOf a' = Hash.Keccak.Fast.keccakF (lanesOf a0) := by
  unfold lanes.permute_loop0
  refine loop_induct _
    (fun x : core.ops.range.Range Std.Usize × Array Std.U64 25#usize × Array Std.U64 5#usize =>
      x.1.«end» = e ∧ x.1.start.val ≤ 24 ∧ x.2.2.val = par x.2.1.val ∧
        lanesOf x.2.1 = (List.range x.1.start.val).foldl Hash.Keccak.Fast.round (lanesOf a0))
    (fun a' => lanesOf a' = Hash.Keccak.Fast.keccakF (lanesOf a0))
    (fun x => 24 - x.1.start.val) ?_ _ ⟨rfl, by simp, hc, by simp⟩
  rintro ⟨⟨i, e'⟩, a, c⟩ ⟨he', hi, hpar, hl⟩
  simp only at he' hi hpar hl
  subst he'
  by_cases hlt : i.val < 24
  · obtain ⟨s, hs, -⟩ := range_next_lt i e' (by omega)
    obtain ⟨a', c', hb, hr⟩ := round_body i e' s a c (by omega) hlt hs
    refine ⟨.cont ({ start := s, «end» := e' }, a', c'), hb, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
    · simp only [hs]; omega
    · have := roundU_par a.val c.val (by simp) (by simp) RC.val[i.val]!
      rw [← hr] at this
      exact this
    · have := roundU_round a.val (by simp) RC.val[i.val]! i.val (rc_word i.val hlt)
      rw [← hpar, ← hr] at this
      simp only [hs, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← hl]
      exact this
    · simp only [hs]; omega
  · refine ⟨.done a, round_done i e' a c (by omega), ?_⟩
    have : i.val = 24 := by omega
    simpa [this, Hash.Keccak.Fast.keccakF] using hl

end Permutation

open Permutation in
/-- **The Rust Keccak-f[1600] is the reference's**, on lanes. -/
theorem keccak_f_spec (a : Array Std.U64 25#usize) :
    ∃ a', keccak256.keccak_f a = ok a' ∧ lanesOf a' = Hash.Keccak.Fast.keccakF (lanesOf a) := by
  obtain ⟨c, hc, hpar⟩ := exists_of_spec (parities_spec a)
  unfold keccak256.keccak_f keccak256.lanes.permute
  rw [hc]
  simp only [core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice, core.slice.Slice.len,
    rust_primitives.slice.slice_length, Aeneas.Std.bind_ok]
  exact rounds _ (by simp) a c hpar

end LeanSphincsProofs
