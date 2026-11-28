/-
  LeanVM.Guest.B1.Link.TableSize

  B1 for `table_size__L{h}`: a table's row count against its log height.
-/

module

public import LeanVM.Guest.B1.Link.IndexMle
public import LeanVM.Guest.B1.Link.RoundsLoop
import LeanVM.Guest.CoreRef

/-!
# `table_size`

`table_size(rows, bits, h)` (G) certifies `h` against a table's row count: the hint at `bits` is the
complement of the row count's `h` low bits, then its bit `h`, set only alone. Its meaning
(`MeaningTS`): `rows` is the word of a count `R ≤ 2^h`, the bits at `bits` are `cbitsE R h` then
`bitE R h` (what `table_point` reads), it returns `g^R`, and its least-height terms `lead`, `rest`
pass (`lead = 1`, `rest ≠ 0`) exactly when `h = 0` or `2^(h-1) < R`.

`natOfBits` and `polyE` read a list of bits little-endian as a number and as a polynomial in `g`.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Bits as numbers and as polynomials -/

/-- A list of bits, little-endian, as a number. -/
def natOfBits : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + 2 * natOfBits ds

/-- A list of field elements as the polynomial in `g` they are the coefficients of. -/
def polyE : List E → E
  | [] => 0
  | c :: cs => c + gen * polyE cs

theorem natOfBits_lt : ∀ ds : List ℕ, (∀ d ∈ ds, d ≤ 1) → natOfBits ds < 2 ^ ds.length
  | [], _ => by simp [natOfBits]
  | d :: ds, h => by
    have := natOfBits_lt ds fun x hx ↦ h x (List.mem_cons_of_mem _ hx)
    have := h d List.mem_cons_self
    simp only [natOfBits, List.length_cons, pow_succ]
    omega

theorem natOfBits_append_single : ∀ (l : List ℕ) (d : ℕ), natOfBits (l ++ [d]) = natOfBits l + d * 2 ^ l.length
  | [], d => by simp [natOfBits]
  | x :: l, d => by
    simp only [List.cons_append, natOfBits, natOfBits_append_single l d, List.length_cons, pow_succ]
    ring

theorem polyE_append_single : ∀ (l : List E) (c : E), polyE (l ++ [c]) = polyE l + c * gen ^ l.length
  | [], c => by simp [polyE]
  | x :: l, c => by
    simp only [List.cons_append, polyE, polyE_append_single l c, List.length_cons, pow_succ]
    ring

theorem polyE_eOfNat : ∀ ds : List ℕ, (∀ d ∈ ds, d ≤ 1) → ds.length ≤ 63 →
    polyE (ds.map eOfNat) = eOfNat (natOfBits ds)
  | [], _, _ => by simp [polyE, natOfBits, eOfNat_zero]
  | d :: ds, h, hl => by
    have hd := h d List.mem_cons_self
    have hlt := natOfBits_lt ds fun x hx ↦ h x (List.mem_cons_of_mem _ hx)
    simp only [List.length_cons] at hl
    have h2 : 2 * natOfBits ds < 2 ^ 64 := by
      have : 2 ^ ds.length ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    simp only [List.map_cons, polyE, natOfBits]
    rw [polyE_eOfNat ds (fun x hx ↦ h x (List.mem_cons_of_mem _ hx)) (by omega), gen_mul_eOfNat h2,
      add_comm, ← pow_one 2, eOfNat_add_of_lt (show d < 2 ^ 1 by omega), add_comm]

/-- `1 + c` over a list. -/
theorem polyE_one_add : ∀ l : List E, polyE (l.map (1 + ·)) = polyE l + polyE (List.replicate l.length 1)
  | [] => by simp [polyE]
  | c :: l => by
    simp only [List.map_cons, polyE, List.length_cons, List.replicate_succ, polyE_one_add l]
    ring

theorem natOfBits_replicate_one : ∀ n : ℕ, natOfBits (List.replicate n 1) = 2 ^ n - 1
  | 0 => rfl
  | n + 1 => by
    simp only [List.replicate_succ, natOfBits, natOfBits_replicate_one n, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

theorem polyE_replicate_one {n : ℕ} (hn : n ≤ 63) : polyE (List.replicate n 1) = eOfNat (2 ^ n - 1) := by
  have := polyE_eOfNat (List.replicate n 1) (fun d hd ↦ by rw [(List.mem_replicate.mp hd).2]) (by simpa using hn)
  rw [List.map_replicate, eOfNat_one, natOfBits_replicate_one] at this
  exact this

theorem natOfBits_compl : ∀ l : List ℕ, (∀ d ∈ l, d ≤ 1) →
    natOfBits (l.map (1 - ·)) + natOfBits l = 2 ^ l.length - 1
  | [], _ => rfl
  | d :: l, h => by
    have hd := h d List.mem_cons_self
    have ih := natOfBits_compl l fun x hx ↦ h x (List.mem_cons_of_mem _ hx)
    have hlt := natOfBits_lt l fun x hx ↦ h x (List.mem_cons_of_mem _ hx)
    simp only [List.map_cons, natOfBits, List.length_cons, pow_succ]
    have := Nat.one_le_two_pow (n := l.length)
    omega

theorem natOfBits_eq_zero : ∀ l : List ℕ, natOfBits l = 0 → ∀ d ∈ l, d = 0
  | [], _ => by simp
  | x :: l, h => by
    simp only [natOfBits] at h
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · omega
    · exact natOfBits_eq_zero l (by omega) d hd

/-- Bit `k` of a number read from bits. -/
theorem bitE_natOfBits : ∀ (l : List ℕ), (∀ d ∈ l, d ≤ 1) → ∀ k, bitE (natOfBits l) k = eOfNat (l.getD k 0)
  | [], _, k => by simp [natOfBits, bitE, eOfNat_zero]
  | d :: l, h, 0 => by
    have hd := h d List.mem_cons_self
    rw [bitE_zero]
    simp only [natOfBits, List.getD_cons_zero]
    rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
    · simp [eOfNat_zero]
    · simp [eOfNat_one]
  | d :: l, h, k + 1 => by
    have hd := h d List.mem_cons_self
    rw [bitE_succ, show natOfBits (d :: l) / 2 = natOfBits l by simp only [natOfBits]; omega,
      bitE_natOfBits l (fun x hx ↦ h x (List.mem_cons_of_mem _ hx)) k, List.getD_cons_succ]

/-! ## Hinted bits -/

theorem eOfNat_bv {c : E} (hc : c * c = c) : c = eOfNat (bv c) := by
  have := bitE_of_mul_self hc
  unfold bv
  by_cases h1 : c = 1
  · simp [h1, eOfNat_one]
  · simp only [h1, ↓reduceIte, eOfNat_zero]
    rw [this]; simp [Value.bitE, h1]

theorem one_add_bit {c : E} (hc : c * c = c) : (1 + c) * (1 + c) = 1 + c := by
  linear_combination hc + c * two_eq_zero_E

theorem bv_one_add {c : E} (hc : c * c = c) : bv (1 + c) = 1 - bv c := by
  have h := eOfNat_bv hc
  unfold bv
  by_cases h1 : c = 1
  · subst h1; simp [add_self_E]
  · have h0 : c = 0 := by
      rw [h]; unfold bv; simp [h1, eOfNat_zero]
    subst h0; simp

theorem one_add_eq_eOfNat {c : E} (hc : c * c = c) : 1 + c = eOfNat (1 - bv c) := by
  rw [← bv_one_add hc]
  exact eOfNat_bv (one_add_bit hc)

theorem bv_le_one (c : E) : bv c ≤ 1 := bv_le c

/-! ## The templates -/

/-- The factor block of bit `0`. -/
def tsBlk0 : List Stmt :=
  [.atom (.load (.n 4) (.n 1) 0), .atom (.mul (.n 5) (.n 4) (.n 4)), .atom (.load (.n 5) (.n 1) 0),
    .atom (.const (.n 6) (word 1 0)), .atom (.const (.n 7) (word 1 0)), .atom (.add (.n 8) (.n 7) (.n 4)),
    .atom (.const (.n 9) (word (imFactor 0) 0)), .atom (.mul (.n 10) (.n 8) (.n 9)),
    .atom (.add (.n 11) (.n 6) (.n 10))]

/-- The factor block of bit `k ≥ 1`, from value `3 + 9 k`, times the product so far. -/
def tsBlk (k : ℕ) : List Stmt :=
  [.atom (.load (.n (3 + 9 * k)) (.n 1) k), .atom (.mul (.n (4 + 9 * k)) (.n (3 + 9 * k)) (.n (3 + 9 * k))),
    .atom (.load (.n (4 + 9 * k)) (.n 1) k), .atom (.const (.n (5 + 9 * k)) (word 1 0)),
    .atom (.const (.n (6 + 9 * k)) (word 1 0)), .atom (.add (.n (7 + 9 * k)) (.n (6 + 9 * k)) (.n (3 + 9 * k))),
    .atom (.const (.n (8 + 9 * k)) (word (imFactor k) 0)),
    .atom (.mul (.n (9 + 9 * k)) (.n (7 + 9 * k)) (.n (8 + 9 * k))),
    .atom (.add (.n (10 + 9 * k)) (.n (5 + 9 * k)) (.n (9 + 9 * k))),
    .atom (.mul (.n (11 + 9 * k)) (.n (2 + 9 * k)) (.n (10 + 9 * k)))]

/-- Bit `h`'s block, times the product so far: `g^rows` at `9 + 9 h`. -/
def tsTop (h : ℕ) : List Stmt :=
  [.atom (.load (.n (3 + 9 * h)) (.n 1) h), .atom (.mul (.n (4 + 9 * h)) (.n (3 + 9 * h)) (.n (3 + 9 * h))),
    .atom (.load (.n (4 + 9 * h)) (.n 1) h), .atom (.const (.n (5 + 9 * h)) (word 1 0)),
    .atom (.const (.n (6 + 9 * h)) (word (imFactor h) 0)),
    .atom (.mul (.n (7 + 9 * h)) (.n (3 + 9 * h)) (.n (6 + 9 * h))),
    .atom (.add (.n (8 + 9 * h)) (.n (5 + 9 * h)) (.n (7 + 9 * h))),
    .atom (.mul (.n (9 + 9 * h)) (.n (2 + 9 * h)) (.n (8 + 9 * h)))]

/-- The word, its hint, and `g^rows`, `h ≥ 1`. -/
def tsHead (h : ℕ) : List Stmt :=
  [.atom (.const (.n 2) (word (2 ^ h - 1) 0)), .atom (.add (.n 3) (.n 0) (.n 2)),
    .atom (.hint (.bits (.n 3) 0 (h + 1) (.heap (.n 1) 0 (h + 1))))] ++ tsBlk0 ++
  ((List.range (h - 1)).map fun k ↦ tsBlk (k + 1)).flatten ++ tsTop h

/-- A step of `below`'s Horner walk, `h ≥ 2`. -/
def tsBelowStep (h j : ℕ) : List Stmt :=
  [.atom (.const (.n (11 + 9 * h + 4 * j)) (word 2 0)),
    .atom (.mul (.n (12 + 9 * h + 4 * j)) (.n (10 + 9 * h + 4 * j)) (.n (11 + 9 * h + 4 * j))),
    .atom (.load (.n (13 + 9 * h + 4 * j)) (.n 1) (h - 3 - j)),
    .atom (.add (.n (14 + 9 * h + 4 * j)) (.n (12 + 9 * h + 4 * j)) (.n (13 + 9 * h + 4 * j)))]

/-- `below`, the bits under `h - 1` as a polynomial, at `13 h + 2`. -/
def tsBelow (h : ℕ) : List Stmt :=
  .atom (.load (.n (10 + 9 * h)) (.n 1) (h - 2)) :: ((List.range (h - 2)).map (tsBelowStep h)).flatten

/-- `low`, `lead`, `rest` and the two checks, `h ≥ 2`. -/
def tsTail (h : ℕ) : List Stmt :=
  [.atom (.load (.n (13 * h + 3)) (.n 1) (h - 1)), .atom (.const (.n (13 * h + 4)) (word (2 ^ (h - 1)) 0)),
    .atom (.mul (.n (13 * h + 5)) (.n (13 * h + 3)) (.n (13 * h + 4))),
    .atom (.add (.n (13 * h + 6)) (.n (13 * h + 2)) (.n (13 * h + 5))),
    .atom (.const (.n (13 * h + 7)) (word 1 0)), .atom (.add (.n (13 * h + 8)) (.n (3 + 9 * h)) (.n (13 * h + 7))),
    .atom (.load (.n (13 * h + 9)) (.n 1) (h - 1)),
    .atom (.add (.n (13 * h + 10)) (.n (13 * h + 8)) (.n (13 * h + 9))),
    .atom (.add (.n (13 * h + 11)) (.n (3 + 9 * h)) (.n (13 * h + 2))),
    .atom (.const (.n (13 * h + 12)) (word (2 ^ (h - 1) - 1) 0)),
    .atom (.add (.n (13 * h + 13)) (.n (13 * h + 11)) (.n (13 * h + 12))),
    .atom (.const (.n (13 * h + 14)) (word (2 ^ h) 0)),
    .atom (.mul (.n (13 * h + 15)) (.n (3 + 9 * h)) (.n (13 * h + 14))),
    .atom (.add (.n (13 * h + 16)) (.n (13 * h + 6)) (.n (13 * h + 15))),
    .atom (.assertEq (.n (13 * h + 16)) (.n 3)),
    .atom (.const (.n (13 * h + 17)) (word (2 ^ h - 1) 0)),
    .atom (.add (.n (13 * h + 18)) (.n (13 * h + 6)) (.n (13 * h + 17))),
    .atom (.mul (.n (13 * h + 19)) (.n (3 + 9 * h)) (.n (13 * h + 18))),
    .atom (.const (.n (13 * h + 20)) (word 0 0)),
    .atom (.assertEq (.n (13 * h + 19)) (.n (13 * h + 20))),
    .atom (.copy (.n (13 * h + 21)) (.n (9 + 9 * h))), .atom (.copy (.n (13 * h + 22)) (.n (13 * h + 10))),
    .atom (.copy (.n (13 * h + 23)) (.n (13 * h + 13)))]

/-- `table_size__L{h}`'s body, `h ≥ 2`. -/
def tsBody (h : ℕ) : List Stmt :=
  tsHead h ++ tsBelow h ++ tsTail h ++ [.ret [.n (13 * h + 21), .n (13 * h + 22), .n (13 * h + 23)]]

/-- `table_size__L1`'s tail. -/
def tsTail1 : List Stmt :=
  [.atom (.load (.n 19) (.n 1) 0), .atom (.const (.n 20) (word 1 0)), .atom (.add (.n 21) (.n 12) (.n 20)),
    .atom (.load (.n 22) (.n 1) 0), .atom (.add (.n 23) (.n 21) (.n 22)), .atom (.const (.n 24) (word 2 0)),
    .atom (.mul (.n 25) (.n 12) (.n 24)), .atom (.add (.n 26) (.n 19) (.n 25)), .atom (.assertEq (.n 26) (.n 3)),
    .atom (.const (.n 27) (word 1 0)), .atom (.add (.n 28) (.n 19) (.n 27)), .atom (.mul (.n 29) (.n 12) (.n 28)),
    .atom (.const (.n 30) (word 0 0)), .atom (.assertEq (.n 29) (.n 30)), .atom (.copy (.n 31) (.n 18)),
    .atom (.copy (.n 32) (.n 23)), .atom (.copy (.n 33) (.n 12))]

/-- `table_size__L1`'s body. -/
def tsBody1 : List Stmt := tsHead 1 ++ tsTail1 ++ [.ret [.n 31, .n 32, .n 33]]

/-- `table_size__L0`'s body. -/
def tsBody0 : List Stmt :=
  [.atom (.hint (.bits (.n 0) 0 1 (.heap (.n 1) 0 1))), .atom (.load (.n 2) (.n 1) 0),
    .atom (.mul (.n 3) (.n 2) (.n 2)), .atom (.load (.n 3) (.n 1) 0), .atom (.const (.n 4) (word 1 0)),
    .atom (.const (.n 5) (word 3 0)), .atom (.mul (.n 6) (.n 2) (.n 5)), .atom (.add (.n 7) (.n 4) (.n 6)),
    .atom (.assertEq (.n 2) (.n 0)), .atom (.const (.n 8) (word 0 0)), .atom (.mul (.n 9) (.n 2) (.n 8)),
    .atom (.const (.n 10) (word 0 0)), .atom (.assertEq (.n 9) (.n 10)), .atom (.copy (.n 11) (.n 7)),
    .atom (.const (.n 12) (word 1 0)), .atom (.const (.n 13) (word 1 0)), .ret [.n 11, .n 12, .n 13]]

/-! ## The meaning -/

/-- **`table_size__L{h}(rows, bits)`**: `rows` is the word of a count `R ≤ 2^h`; the bits at `bits`
are `R`'s complement bits below `h`, then its bit `h`; it returns `g^R`, and terms `lead`, `rest`
with `lead = 1 ∧ rest ≠ 0` exactly when `h = 0` or `2^(h-1) < R`. -/
def MeaningTS (h : ℕ) (rd : Reader) : List E → List E → Prop
  | [rows, bits], rets => ∃ R : ℕ, R ≤ 2 ^ h ∧ rows = eOfNat R ∧ ReadsAt rd bits (cbitsE R h) ∧
      LoadHolds rd bits h (bitE R h) ∧ ∃ gr lead rest : E, rets = [gr, lead, rest] ∧ gr = gen ^ R ∧
      (lead = 1 ∧ rest ≠ 0 ↔ (h = 0 ∨ 2 ^ (h - 1) < R))
  | _, _ => False

/-- The bit the factor blocks load at `k`. -/
def tsCv (σ : Val) (k : ℕ) : E := σ (.n (if k = 0 then 4 else 3 + 9 * k))

/-- The complement of a loaded bit, as a number. -/
def tsD (σ : Val) (k : ℕ) : ℕ := 1 - bv (tsCv σ k)

/-- The row count the bits stand for. -/
def tsR (σ : Val) (h : ℕ) : ℕ := natOfBits ((List.range h).map (tsD σ) ++ [bv (σ (.n (3 + 9 * h)))])

theorem bit_of_loads {rd : Reader} {p x y : E} {k : ℕ} (h1 : LoadHolds rd p k x) (hm : y = x * x)
    (h2 : LoadHolds rd p k y) : x * x = x := by
  rw [← hm]; exact (loadHolds_unique h1 h2).symm

theorem factor_eq {c : E} (hc : c * c = c) {k : ℕ} (hk : k < 34) :
    1 + (1 + c) * word (imFactor k) 0 = gen ^ (2 ^ k * (1 - bv c)) := by
  rw [imFactor_eq hk, add_comm (1 : E) (gen ^ 2 ^ k), bit_factor (one_add_bit hc).symm, ← bv_one_add hc]
  rfl

theorem top_factor_eq {c : E} (hc : c * c = c) {k : ℕ} (hk : k < 34) :
    1 + c * word (imFactor k) 0 = gen ^ (2 ^ k * bv c) := by
  rw [imFactor_eq hk, add_comm (1 : E) (gen ^ 2 ^ k), bit_factor hc.symm]
  rfl

theorem natOfBits_range_succ (f : ℕ → ℕ) (k : ℕ) :
    natOfBits ((List.range (k + 1)).map f) = natOfBits ((List.range k).map f) + f k * 2 ^ k := by
  simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
  rw [natOfBits_append_single]
  simp

theorem polyE_range_succ (f : ℕ → E) (k : ℕ) :
    polyE ((List.range (k + 1)).map f) = polyE ((List.range k).map f) + f k * gen ^ k := by
  simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
  rw [polyE_append_single]
  simp

/-- What the word, the hint and the factor blocks establish. -/
theorem tsHead_facts {rd : Reader} {σ : Val} {h : ℕ} (hh : 1 ≤ h) (hh' : h ≤ 24)
    (hA : ∀ a, Stmt.atom a ∈ tsHead h → a.Holds rd σ) :
    σ (.n 3) = σ (.n 0) + eOfNat (2 ^ h - 1) ∧
      (∀ k < h, LoadHolds rd (σ (.n 1)) k (tsCv σ k) ∧ tsCv σ k * tsCv σ k = tsCv σ k) ∧
      LoadHolds rd (σ (.n 1)) h (σ (.n (3 + 9 * h))) ∧
      σ (.n (3 + 9 * h)) * σ (.n (3 + 9 * h)) = σ (.n (3 + 9 * h)) ∧
      σ (.n (9 + 9 * h)) = gen ^ tsR σ h := by
  have mP : ∀ a, Stmt.atom a ∈ [Stmt.atom (.const (.n 2) (word (2 ^ h - 1) 0)), .atom (.add (.n 3) (.n 0) (.n 2)),
      .atom (.hint (.bits (.n 3) 0 (h + 1) (.heap (.n 1) 0 (h + 1))))] → a.Holds rd σ := fun a ha ↦
    hA a (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ha)))
  have m0 : ∀ a, Stmt.atom a ∈ tsBlk0 → a.Holds rd σ := fun a ha ↦
    hA a (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ha)))
  have mL : ∀ k < h - 1, ∀ a, Stmt.atom a ∈ tsBlk (k + 1) → a.Holds rd σ := fun k hk a ha ↦
    hA a (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatten.mpr
      ⟨_, List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, ha⟩)))
  have mT : ∀ a, Stmt.atom a ∈ tsTop h → a.Holds rd σ := fun a ha ↦ hA a (List.mem_append_right _ ha)
  have c2 := mP (.const (.n 2) (word (2 ^ h - 1) 0)) (by simp)
  have a3 := mP (.add (.n 3) (.n 0) (.n 2)) (by simp)
  simp only [Atom.Holds] at c2 a3
  -- the bits
  have hbits : ∀ k < h, LoadHolds rd (σ (.n 1)) k (tsCv σ k) ∧ tsCv σ k * tsCv σ k = tsCv σ k := by
    intro k hk
    rcases k with _ | k
    · have l4 := m0 (.load (.n 4) (.n 1) 0) (by simp [tsBlk0])
      have m5 := m0 (.mul (.n 5) (.n 4) (.n 4)) (by simp [tsBlk0])
      have l5 := m0 (.load (.n 5) (.n 1) 0) (by simp [tsBlk0])
      simp only [Atom.Holds] at l4 m5 l5
      simp only [tsCv, ↓reduceIte]
      exact ⟨l4, bit_of_loads l4 m5 l5⟩
    · have hB := mL k (by omega)
      have l1 := hB (.load (.n (3 + 9 * (k + 1))) (.n 1) (k + 1)) (by simp [tsBlk])
      have m2 := hB (.mul (.n (4 + 9 * (k + 1))) (.n (3 + 9 * (k + 1))) (.n (3 + 9 * (k + 1)))) (by simp [tsBlk])
      have l2 := hB (.load (.n (4 + 9 * (k + 1))) (.n 1) (k + 1)) (by simp [tsBlk])
      simp only [Atom.Holds] at l1 m2 l2
      simp only [tsCv, Nat.add_one_ne_zero, ↓reduceIte]
      exact ⟨l1, bit_of_loads l1 m2 l2⟩
  -- the running product
  have hprod : ∀ k < h, σ (.n (11 + 9 * k)) = gen ^ natOfBits ((List.range (k + 1)).map (tsD σ)) := by
    intro k hk
    induction k with
    | zero =>
      have c6 := m0 (.const (.n 6) (word 1 0)) (by simp [tsBlk0])
      have c7 := m0 (.const (.n 7) (word 1 0)) (by simp [tsBlk0])
      have a8 := m0 (.add (.n 8) (.n 7) (.n 4)) (by simp [tsBlk0])
      have c9 := m0 (.const (.n 9) (word (imFactor 0) 0)) (by simp [tsBlk0])
      have m10 := m0 (.mul (.n 10) (.n 8) (.n 9)) (by simp [tsBlk0])
      have a11 := m0 (.add (.n 11) (.n 6) (.n 10)) (by simp [tsBlk0])
      simp only [Atom.Holds] at c6 c7 a8 c9 m10 a11
      have hb := (hbits 0 hk).2
      simp only [tsCv, ↓reduceIte] at hb
      rw [show 11 + 9 * 0 = 11 from rfl, a11, m10, a8, c9, c6, c7, word_one, factor_eq hb (by norm_num)]
      simp [natOfBits, tsD, tsCv]
    | succ k ih =>
      have hB := mL k (by omega)
      have c5 := hB (.const (.n (5 + 9 * (k + 1))) (word 1 0)) (by simp [tsBlk])
      have c6 := hB (.const (.n (6 + 9 * (k + 1))) (word 1 0)) (by simp [tsBlk])
      have a7 := hB (.add (.n (7 + 9 * (k + 1))) (.n (6 + 9 * (k + 1))) (.n (3 + 9 * (k + 1)))) (by simp [tsBlk])
      have c8 := hB (.const (.n (8 + 9 * (k + 1))) (word (imFactor (k + 1)) 0)) (by simp [tsBlk])
      have m9 := hB (.mul (.n (9 + 9 * (k + 1))) (.n (7 + 9 * (k + 1))) (.n (8 + 9 * (k + 1)))) (by simp [tsBlk])
      have a10 := hB (.add (.n (10 + 9 * (k + 1))) (.n (5 + 9 * (k + 1))) (.n (9 + 9 * (k + 1)))) (by simp [tsBlk])
      have m11 := hB (.mul (.n (11 + 9 * (k + 1))) (.n (2 + 9 * (k + 1))) (.n (10 + 9 * (k + 1)))) (by simp [tsBlk])
      simp only [Atom.Holds] at c5 c6 a7 c8 m9 a10 m11
      have hb := (hbits (k + 1) hk).2
      simp only [tsCv, Nat.add_one_ne_zero, ↓reduceIte] at hb
      rw [m11, a10, m9, a7, c8, c5, c6, word_one, factor_eq hb (by omega),
        show 2 + 9 * (k + 1) = 11 + 9 * k by ring, ih (by omega), ← pow_add]
      congr 1
      rw [natOfBits_range_succ (tsD σ) (k + 1),
        show tsD σ (k + 1) = 1 - bv (σ (.n (3 + 9 * (k + 1)))) by simp [tsD, tsCv]]
      ring
  refine ⟨by rw [a3, c2, word_eOfNat], hbits, ?_⟩
  have l1 := mT (.load (.n (3 + 9 * h)) (.n 1) h) (by simp [tsTop])
  have m2 := mT (.mul (.n (4 + 9 * h)) (.n (3 + 9 * h)) (.n (3 + 9 * h))) (by simp [tsTop])
  have l2 := mT (.load (.n (4 + 9 * h)) (.n 1) h) (by simp [tsTop])
  have c5 := mT (.const (.n (5 + 9 * h)) (word 1 0)) (by simp [tsTop])
  have c6 := mT (.const (.n (6 + 9 * h)) (word (imFactor h) 0)) (by simp [tsTop])
  have m7 := mT (.mul (.n (7 + 9 * h)) (.n (3 + 9 * h)) (.n (6 + 9 * h))) (by simp [tsTop])
  have a8 := mT (.add (.n (8 + 9 * h)) (.n (5 + 9 * h)) (.n (7 + 9 * h))) (by simp [tsTop])
  have m9 := mT (.mul (.n (9 + 9 * h)) (.n (2 + 9 * h)) (.n (8 + 9 * h))) (by simp [tsTop])
  simp only [Atom.Holds] at l1 m2 l2 c5 c6 m7 a8 m9
  have hb := bit_of_loads l1 m2 l2
  refine ⟨l1, hb, ?_⟩
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  rw [m9, a8, m7, c6, c5, word_one, top_factor_eq hb (by omega), show 2 + 9 * (h' + 1) = 11 + 9 * h' by ring,
    hprod h' (by omega), ← pow_add, tsR, natOfBits_append_single, List.length_map, List.length_range]
  congr 1
  ring

theorem tsR_facts {σ : Val} {h : ℕ} (hh' : h ≤ 24) (hbits : ∀ k < h, tsCv σ k * tsCv σ k = tsCv σ k)
    (htop : σ (.n (3 + 9 * h)) * σ (.n (3 + 9 * h)) = σ (.n (3 + 9 * h))) :
    eOfNat (tsR σ h) = polyE ((List.range h).map (tsCv σ)) + eOfNat (2 ^ h - 1) +
        σ (.n (3 + 9 * h)) * gen ^ h ∧
      cbitsE (tsR σ h) h = (List.range h).map (tsCv σ) ∧ bitE (tsR σ h) h = σ (.n (3 + 9 * h)) ∧
      tsR σ h = natOfBits ((List.range h).map (tsD σ)) + bv (σ (.n (3 + 9 * h))) * 2 ^ h ∧
      natOfBits ((List.range h).map (tsD σ)) < 2 ^ h := by
  have hd : ∀ d ∈ (List.range h).map (tsD σ) ++ [bv (σ (.n (3 + 9 * h)))], d ≤ 1 := by
    intro d hd
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hd
    rcases hd with ⟨k, -, rfl⟩ | rfl
    · simp only [tsD]; omega
    · exact bv_le _
  have hmap : ((List.range h).map (tsD σ)).map eOfNat = ((List.range h).map (tsCv σ)).map (1 + ·) := by
    simp only [List.map_map]
    exact List.map_congr_left fun k hk ↦ (one_add_eq_eOfNat (hbits k (List.mem_range.mp hk))).symm
  have hR : tsR σ h = natOfBits ((List.range h).map (tsD σ)) + bv (σ (.n (3 + 9 * h))) * 2 ^ h := by
    rw [tsR, natOfBits_append_single, List.length_map, List.length_range]
  refine ⟨?_, ?_, ?_, hR, ?_⟩
  · rw [tsR, ← polyE_eOfNat _ hd (by simp; omega), List.map_append, List.map_singleton, polyE_append_single, hmap,
      polyE_one_add, List.length_map, List.length_map, List.length_range, polyE_replicate_one (by omega),
      ← eOfNat_bv htop, List.length_map, List.length_range]
  · apply List.ext_getElem (by simp [cbitsE_length])
    intro k h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp only [cbitsE, List.getElem_map, List.getElem_range, cbitE, tsR]
    rw [bitE_natOfBits _ hd, List.getD_append _ _ _ _ (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h2, Option.map_some,
      Option.getD_some]
    rw [show eOfNat (tsD σ k) = 1 + tsCv σ k from (one_add_eq_eOfNat (hbits k h2)).symm]
    linear_combination two_eq_zero_E
  · rw [tsR, bitE_natOfBits _ hd, List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_map, List.length_range, Nat.sub_self, List.getD_cons_zero]
    exact (eOfNat_bv htop).symm
  · have := natOfBits_lt ((List.range h).map (tsD σ)) fun d hd' ↦ hd d (List.mem_append_left _ hd')
    simpa using this

theorem tsHead_atoms (h : ℕ) : AllAtoms (tsHead h) :=
  allAtoms_append (allAtoms_append (allAtoms_of_isAtomsB rfl)
    (allAtoms_map_flatten fun _ _ ↦ allAtoms_of_isAtomsB rfl)) (allAtoms_of_isAtomsB rfl)

theorem eq_of_add_E {a b : E} (h : a + b = 0) : a = b := by linear_combination h - b * two_eq_zero_E

theorem eOfNat_ne_zero {n : ℕ} (hn : n < 2 ^ 64) (h0 : n ≠ 0) : eOfNat n ≠ 0 := fun h ↦
  h0 (eOfNat_inj hn (by norm_num) (h.trans eOfNat_zero.symm))

theorem eOfNat_bit_eq_one {d : ℕ} (hd : d ≤ 1) : eOfNat d = 1 ↔ d = 1 := by
  rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
  · simp [eOfNat_zero]
  · simp [eOfNat_one]

/-- The least-height test: `lead = top + 1 + c_{h-1}`, `rest = top + below + (2^(h-1) - 1)`. -/
theorem ts_lead_rest {σ : Val} {h : ℕ} (hh : 1 ≤ h) (hh' : h ≤ 24)
    (hbits : ∀ k < h, tsCv σ k * tsCv σ k = tsCv σ k)
    (htop : σ (.n (3 + 9 * h)) * σ (.n (3 + 9 * h)) = σ (.n (3 + 9 * h)))
    (hall : σ (.n (3 + 9 * h)) = 1 → natOfBits ((List.range h).map (tsD σ)) = 0) :
    (σ (.n (3 + 9 * h)) + 1 + tsCv σ (h - 1) = 1 ∧
      σ (.n (3 + 9 * h)) + polyE ((List.range (h - 1)).map (tsCv σ)) + eOfNat (2 ^ (h - 1) - 1) ≠ 0 ↔
      2 ^ (h - 1) < tsR σ h) := by
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  obtain ⟨-, -, -, hR, hlt⟩ := tsR_facts hh' hbits htop
  set top := σ (.n (3 + 9 * (h' + 1)))
  have hbelow : polyE ((List.range h').map (tsCv σ)) + eOfNat (2 ^ h' - 1) =
      eOfNat (natOfBits ((List.range h').map (tsD σ))) := by
    have hd : ∀ d ∈ (List.range h').map (tsD σ), d ≤ 1 := by
      intro d hd; obtain ⟨k, -, rfl⟩ := List.mem_map.mp hd; simp only [tsD]; omega
    rw [← polyE_eOfNat _ hd (by simp; omega), ← polyE_replicate_one (by omega), List.map_map]
    rw [show (List.range h').map (eOfNat ∘ tsD σ) = ((List.range h').map (tsCv σ)).map (1 + ·) from by
      simp only [List.map_map]
      exact List.map_congr_left fun k hk ↦ (one_add_eq_eOfNat (hbits k (by
        have := List.mem_range.mp hk; omega))).symm]
    rw [polyE_one_add]; simp
  have hlast : 1 + tsCv σ h' = eOfNat (tsD σ h') := one_add_eq_eOfNat (hbits h' (by omega))
  have hsplit : natOfBits ((List.range (h' + 1)).map (tsD σ)) =
      natOfBits ((List.range h').map (tsD σ)) + tsD σ h' * 2 ^ h' := natOfBits_range_succ _ _
  have hlt' : natOfBits ((List.range h').map (tsD σ)) < 2 ^ h' := by
    have := natOfBits_lt ((List.range h').map (tsD σ)) (fun d hd ↦ by
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hd; simp only [tsD]; omega)
    simpa using this
  have hdl : tsD σ h' ≤ 1 := by simp only [tsD]; omega
  have hp : 2 ^ h' < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [add_assoc top (polyE ((List.range h').map (tsCv σ))) (eOfNat (2 ^ h' - 1)), hbelow,
    add_assoc top 1 (tsCv σ h'), hlast]
  have htb := eOfNat_bv htop
  by_cases ht : top = 1
  · have h0 := hall ht
    rw [hsplit] at h0
    have e1 : natOfBits ((List.range h').map (tsD σ)) = 0 := by omega
    have e2 : tsD σ h' = 0 := by
      rcases Nat.eq_zero_or_pos (tsD σ h') with h | h
      · exact h
      · have := Nat.one_le_two_pow (n := h'); nlinarith
    have hR' : tsR σ (h' + 1) = 2 ^ (h' + 1) := by
      rw [hR, hsplit, e1, e2, show bv top = 1 by simp [bv, ht]]; ring
    rw [ht, e1, e2, eOfNat_zero, add_zero, hR', pow_succ]
    exact ⟨fun _ ↦ by have := Nat.one_le_two_pow (n := h'); omega, fun _ ↦ ⟨rfl, one_ne_zero⟩⟩
  · have hbv : bv top = 0 := by simp [bv, ht]
    have h0 : top = 0 := by rw [htb, hbv, eOfNat_zero]
    rw [h0, zero_add, zero_add, hR, hbv, zero_mul, add_zero, hsplit,
      eOfNat_bit_eq_one hdl]
    constructor
    · rintro ⟨h1, h2⟩
      have : natOfBits ((List.range h').map (tsD σ)) ≠ 0 := fun h ↦ h2 (by rw [h, eOfNat_zero])
      rw [h1]; omega
    · intro hgt
      have hd1 : tsD σ h' = 1 := by
        rcases (show tsD σ h' = 0 ∨ tsD σ h' = 1 by omega) with h | h
        · rw [h] at hgt; omega
        · exact h
      refine ⟨hd1, eOfNat_ne_zero (by omega) ?_⟩
      rw [hd1] at hgt; omega

/-- **`table_size__L{h}`, `2 ≤ h ≤ 24`, implies its meaning.** -/
theorem ts_sound {h : ℕ} (hh : 2 ≤ h) (hh' : h ≤ 24) {rd : Reader} {name : String} {f : Fn}
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1]) (hbody : f.body = tsBody h)
    (args rets : List E) : coreProgram.Rel rd name args rets → MeaningTS h rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams]
  rintro ⟨σ, rfl, hH⟩
  have hat : AllAtoms (tsHead h ++ tsBelow h ++ tsTail h) :=
    allAtoms_append (allAtoms_append (tsHead_atoms h) (allAtoms_cons (allAtoms_map_flatten fun _ _ ↦
      allAtoms_of_isAtomsB rfl))) (allAtoms_of_isAtomsB rfl)
  rw [tsBody, holdsList_append] at hH
  obtain ⟨hA, hret⟩ := (holdsList_atoms hat _ _).mp hH
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hret
  obtain ⟨h3, hbits, htopl, htopb, hg⟩ :=
    tsHead_facts (by omega) hh' fun a ha ↦ hA a (List.mem_append_left _ (List.mem_append_left _ ha))
  have mB0 := hA (.load (.n (10 + 9 * h)) (.n 1) (h - 2))
    (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
  have mB : ∀ j < h - 2, ∀ a, Stmt.atom a ∈ tsBelowStep h j → a.Holds rd σ := fun j hj a ha ↦
    hA a (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_flatten.mpr
      ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, ha⟩))))
  have mT : ∀ a, Stmt.atom a ∈ tsTail h → a.Holds rd σ := fun a ha ↦ hA a (List.mem_append_right _ ha)
  simp only [Atom.Holds] at mB0
  have hb' : ∀ k < h, tsCv σ k * tsCv σ k = tsCv σ k := fun k hk ↦ (hbits k hk).2
  -- below, by its Horner walk from the top
  have hbel : ∀ j ≤ h - 2, σ (.n (10 + 9 * h + 4 * j)) =
      polyE ((List.range (j + 1)).map fun m ↦ tsCv σ (h - 2 - j + m)) := by
    intro j hj
    induction j with
    | zero =>
      rw [show 10 + 9 * h + 4 * 0 = 10 + 9 * h by ring,
        show polyE ((List.range (0 + 1)).map fun m ↦ tsCv σ (h - 2 - 0 + m)) = tsCv σ (h - 2) by simp [polyE]]
      exact loadHolds_unique mB0 (hbits (h - 2) (by omega)).1
    | succ j ih =>
      have hS := mB j (by omega)
      have c1 := hS (.const (.n (11 + 9 * h + 4 * j)) (word 2 0)) (by simp [tsBelowStep])
      have m2 := hS (.mul (.n (12 + 9 * h + 4 * j)) (.n (10 + 9 * h + 4 * j)) (.n (11 + 9 * h + 4 * j)))
        (by simp [tsBelowStep])
      have l3 := hS (.load (.n (13 + 9 * h + 4 * j)) (.n 1) (h - 3 - j)) (by simp [tsBelowStep])
      have a4 := hS (.add (.n (14 + 9 * h + 4 * j)) (.n (12 + 9 * h + 4 * j)) (.n (13 + 9 * h + 4 * j)))
        (by simp [tsBelowStep])
      simp only [Atom.Holds] at c1 m2 l3 a4
      have hm : ((List.range (j + 1)).map ((fun m ↦ tsCv σ (h - 2 - (j + 1) + m)) ∘ Nat.succ)) =
          (List.range (j + 1)).map fun m ↦ tsCv σ (h - 2 - j + m) :=
        List.map_congr_left fun m _ ↦ by simp only [Function.comp]; congr 1; omega
      have e : polyE ((List.range (j + 1 + 1)).map fun m ↦ tsCv σ (h - 2 - (j + 1) + m)) =
          tsCv σ (h - 3 - j) + gen * polyE ((List.range (j + 1)).map fun m ↦ tsCv σ (h - 2 - j + m)) := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map, polyE, hm,
          show h - 2 - (j + 1) + 0 = h - 3 - j by omega]
      rw [show 10 + 9 * h + 4 * (j + 1) = 14 + 9 * h + 4 * j by ring, a4, m2, c1, word_gen, ih (by omega),
        loadHolds_unique l3 (hbits (h - 3 - j) (by omega)).1, e]
      ring
  have hbelow := hbel (h - 2) le_rfl
  rw [show 10 + 9 * h + 4 * (h - 2) = 13 * h + 2 by omega, show h - 2 - (h - 2) = 0 by omega,
    show h - 2 + 1 = h - 1 by omega] at hbelow
  simp only [Nat.zero_add] at hbelow
  -- the tail
  have l3 := mT (.load (.n (13 * h + 3)) (.n 1) (h - 1)) (by simp [tsTail])
  have c4 := mT (.const (.n (13 * h + 4)) (word (2 ^ (h - 1)) 0)) (by simp [tsTail])
  have m5 := mT (.mul (.n (13 * h + 5)) (.n (13 * h + 3)) (.n (13 * h + 4))) (by simp [tsTail])
  have a6 := mT (.add (.n (13 * h + 6)) (.n (13 * h + 2)) (.n (13 * h + 5))) (by simp [tsTail])
  have c7 := mT (.const (.n (13 * h + 7)) (word 1 0)) (by simp [tsTail])
  have a8 := mT (.add (.n (13 * h + 8)) (.n (3 + 9 * h)) (.n (13 * h + 7))) (by simp [tsTail])
  have l9 := mT (.load (.n (13 * h + 9)) (.n 1) (h - 1)) (by simp [tsTail])
  have a10 := mT (.add (.n (13 * h + 10)) (.n (13 * h + 8)) (.n (13 * h + 9))) (by simp [tsTail])
  have a11 := mT (.add (.n (13 * h + 11)) (.n (3 + 9 * h)) (.n (13 * h + 2))) (by simp [tsTail])
  have c12 := mT (.const (.n (13 * h + 12)) (word (2 ^ (h - 1) - 1) 0)) (by simp [tsTail])
  have a13 := mT (.add (.n (13 * h + 13)) (.n (13 * h + 11)) (.n (13 * h + 12))) (by simp [tsTail])
  have c14 := mT (.const (.n (13 * h + 14)) (word (2 ^ h) 0)) (by simp [tsTail])
  have m15 := mT (.mul (.n (13 * h + 15)) (.n (3 + 9 * h)) (.n (13 * h + 14))) (by simp [tsTail])
  have a16 := mT (.add (.n (13 * h + 16)) (.n (13 * h + 6)) (.n (13 * h + 15))) (by simp [tsTail])
  have e16 := mT (.assertEq (.n (13 * h + 16)) (.n 3)) (by simp [tsTail])
  have c17 := mT (.const (.n (13 * h + 17)) (word (2 ^ h - 1) 0)) (by simp [tsTail])
  have a18 := mT (.add (.n (13 * h + 18)) (.n (13 * h + 6)) (.n (13 * h + 17))) (by simp [tsTail])
  have m19 := mT (.mul (.n (13 * h + 19)) (.n (3 + 9 * h)) (.n (13 * h + 18))) (by simp [tsTail])
  have c20 := mT (.const (.n (13 * h + 20)) (word 0 0)) (by simp [tsTail])
  have e19 := mT (.assertEq (.n (13 * h + 19)) (.n (13 * h + 20))) (by simp [tsTail])
  have k21 := mT (.copy (.n (13 * h + 21)) (.n (9 + 9 * h))) (by simp [tsTail])
  have k22 := mT (.copy (.n (13 * h + 22)) (.n (13 * h + 10))) (by simp [tsTail])
  have k23 := mT (.copy (.n (13 * h + 23)) (.n (13 * h + 13))) (by simp [tsTail])
  simp only [Atom.Holds] at l3 c4 m5 a6 c7 a8 l9 a10 a11 c12 a13 c14 m15 a16 e16 c17 a18 m19 c20 e19 k21 k22 k23
  have hl3 := loadHolds_unique l3 (hbits (h - 1) (by omega)).1
  have hl9 := loadHolds_unique l9 (hbits (h - 1) (by omega)).1
  have hlow : σ (.n (13 * h + 6)) = polyE ((List.range h).map (tsCv σ)) := by
    rw [a6, m5, c4, hl3, hbelow, word_two_pow (by omega)]
    obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    rw [polyE_range_succ, Nat.add_sub_cancel]
  set top := σ (.n (3 + 9 * h))
  obtain ⟨hRe, hcb, htb, hR, hlt⟩ := tsR_facts hh' hb' htopb
  have hall : top = 1 → natOfBits ((List.range h).map (tsD σ)) = 0 := by
    intro ht
    rw [m19, c20, word_zero, add_zero, a18, c17, hlow, ht, one_mul, word_eOfNat] at e19
    have hbl : ∀ d ∈ (List.range h).map (bv ∘ tsCv σ), d ≤ 1 := by
      intro d hd; obtain ⟨k, -, rfl⟩ := List.mem_map.mp hd; exact bv_le _
    have hpe : polyE ((List.range h).map (tsCv σ)) = eOfNat (natOfBits ((List.range h).map (bv ∘ tsCv σ))) := by
      rw [← polyE_eOfNat _ hbl (by simp; omega), List.map_map]
      exact congrArg polyE (List.map_congr_left fun k hk ↦ eOfNat_bv (hb' k (List.mem_range.mp hk)))
    have hlt2 := natOfBits_lt _ hbl
    simp only [List.length_map, List.length_range] at hlt2
    have hp : 2 ^ h < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have heq := eOfNat_inj (by omega) (by omega) (hpe ▸ eq_of_add_E e19)
    have hc := natOfBits_compl _ hbl
    rw [List.map_map] at hc
    have : (1 - ·) ∘ bv ∘ tsCv σ = tsD σ := rfl
    rw [this, heq] at hc
    simp only [List.length_map, List.length_range] at hc
    omega
  refine ⟨tsR σ h, ?_, ?_, ?_, ?_, _, _, _, hret.symm, ?_, ?_⟩
  · rw [hR]
    by_cases ht : top = 1
    · rw [hall ht, show bv top = 1 by simp [bv, ht]]; omega
    · rw [show bv top = 0 by simp [bv, ht]]; omega
  · rw [hRe, ← hlow]
    have h3' : σ (.n 3) = σ (.n (13 * h + 16)) := (eq_of_add_E e16).symm
    rw [a16, m15, c14, word_two_pow (by omega)] at h3'
    rw [h3] at h3'
    linear_combination h3' - (eOfNat (2 ^ h - 1)) * two_eq_zero_E
  · rw [hcb]
    intro k hk
    simp only [List.length_map, List.length_range] at hk
    simpa using (hbits k hk).1
  · rw [htb]; exact htopl
  · rw [k21, hg]
  · rw [k22, k23, a10, a8, c7, word_one, hl9, a13, a11, c12, hbelow, word_eOfNat]
    exact (ts_lead_rest (by omega) hh' hb' htopb hall).trans ⟨Or.inr, fun hx ↦ hx.resolve_left (show h ≠ 0 by omega)⟩

/-- **`table_size__L1` implies its meaning.** -/
theorem ts1_sound {rd : Reader} {name : String} {f : Fn}
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1]) (hbody : f.body = tsBody1)
    (args rets : List E) : coreProgram.Rel rd name args rets → MeaningTS 1 rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams]
  rintro ⟨σ, rfl, hH⟩
  have hat : AllAtoms (tsHead 1 ++ tsTail1) := allAtoms_append (tsHead_atoms 1) (allAtoms_of_isAtomsB rfl)
  rw [tsBody1, holdsList_append] at hH
  obtain ⟨hA, hret⟩ := (holdsList_atoms hat _ _).mp hH
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hret
  obtain ⟨h3, hbits, htopl, htopb, hg⟩ :=
    tsHead_facts le_rfl (by norm_num) fun a ha ↦ hA a (List.mem_append_left _ ha)
  have mT : ∀ a, Stmt.atom a ∈ tsTail1 → a.Holds rd σ := fun a ha ↦ hA a (List.mem_append_right _ ha)
  have l19 := mT (.load (.n 19) (.n 1) 0) (by simp [tsTail1])
  have c20 := mT (.const (.n 20) (word 1 0)) (by simp [tsTail1])
  have a21 := mT (.add (.n 21) (.n 12) (.n 20)) (by simp [tsTail1])
  have l22 := mT (.load (.n 22) (.n 1) 0) (by simp [tsTail1])
  have a23 := mT (.add (.n 23) (.n 21) (.n 22)) (by simp [tsTail1])
  have c24 := mT (.const (.n 24) (word 2 0)) (by simp [tsTail1])
  have m25 := mT (.mul (.n 25) (.n 12) (.n 24)) (by simp [tsTail1])
  have a26 := mT (.add (.n 26) (.n 19) (.n 25)) (by simp [tsTail1])
  have e26 := mT (.assertEq (.n 26) (.n 3)) (by simp [tsTail1])
  have c27 := mT (.const (.n 27) (word 1 0)) (by simp [tsTail1])
  have a28 := mT (.add (.n 28) (.n 19) (.n 27)) (by simp [tsTail1])
  have m29 := mT (.mul (.n 29) (.n 12) (.n 28)) (by simp [tsTail1])
  have c30 := mT (.const (.n 30) (word 0 0)) (by simp [tsTail1])
  have e29 := mT (.assertEq (.n 29) (.n 30)) (by simp [tsTail1])
  have k31 := mT (.copy (.n 31) (.n 18)) (by simp [tsTail1])
  have k32 := mT (.copy (.n 32) (.n 23)) (by simp [tsTail1])
  have k33 := mT (.copy (.n 33) (.n 12)) (by simp [tsTail1])
  simp only [Atom.Holds] at l19 c20 a21 l22 a23 c24 m25 a26 e26 c27 a28 m29 c30 e29 k31 k32 k33
  have hb' : ∀ k < 1, tsCv σ k * tsCv σ k = tsCv σ k := fun k hk ↦ (hbits k hk).2
  have hc0 : tsCv σ 0 = σ (.n 4) := by simp [tsCv]
  have hl0 := (hbits 0 (by norm_num)).1
  rw [hc0] at hl0
  have h19 := loadHolds_unique l19 hl0
  have h22 := loadHolds_unique l22 hl0
  obtain ⟨hRe, hcb, htb, hR, hlt⟩ := tsR_facts (h := 1) (by norm_num) hb' htopb
  simp only [show 3 + 9 * 1 = 12 from rfl, show 9 + 9 * 1 = 18 from rfl] at hRe htb hR htopl htopb hg
  have hall : σ (.n 12) = 1 → natOfBits ((List.range 1).map (tsD σ)) = 0 := by
    intro ht
    rw [m29, c30, word_zero, add_zero, a28, c27, word_one, ht, one_mul, h19] at e29
    have : σ (.n 4) = 1 := eq_of_add_E e29
    simp [natOfBits, tsD, tsCv, this, bv]
  refine ⟨tsR σ 1, ?_, ?_, ?_, ?_, _, _, _, hret.symm, ?_, ?_⟩
  · rw [hR]
    by_cases ht : σ (.n 12) = 1
    · rw [hall ht, show bv (σ (.n 12)) = 1 by simp [bv, ht]]; norm_num
    · rw [show bv (σ (.n 12)) = 0 by simp [bv, ht], zero_mul, add_zero]
      have := hlt
      simp only [pow_one] at this ⊢
      omega
  · have e1 : eOfNat (2 ^ 1 - 1) = 1 := eOfNat_one
    rw [hRe, e1]
    have h3' : σ (.n 3) = σ (.n 26) := (eq_of_add_E e26).symm
    rw [a26, m25, c24, word_gen, h19] at h3'
    rw [h3, e1] at h3'
    simp only [List.range_one, List.map_cons, List.map_nil, polyE, hc0, mul_zero, add_zero, pow_one]
    linear_combination h3' - 1 * two_eq_zero_E
  · rw [hcb]
    intro k hk
    simp only [List.length_map, List.length_range] at hk
    obtain rfl : k = 0 := by omega
    simpa using (hbits 0 (by norm_num)).1
  · rw [htb]; exact htopl
  · rw [k31, hg]
  · have hlr := ts_lead_rest (h := 1) le_rfl (by norm_num) hb' (by simpa using htopb) (by simpa using hall)
    simp only [show 3 + 9 * 1 = 12 from rfl, Nat.sub_self, List.range_zero, List.map_nil, polyE, add_zero,
      eOfNat_zero, hc0, pow_zero] at hlr
    rw [k32, k33, a23, a21, c20, word_one, h22]
    exact hlr.trans ⟨Or.inr, fun hx ↦ hx.resolve_left (by norm_num)⟩

/-- **`table_size__L0` implies its meaning.** -/
theorem ts0_sound {rd : Reader} {name : String} {f : Fn}
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1]) (hbody : f.body = tsBody0)
    (args rets : List E) : coreProgram.Rel rd name args rets → MeaningTS 0 rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams]
  simp only [tsBody0, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and]
  rintro ⟨σ, rfl, l2, m3, l3, c4, c5, m6, a7, e2, -, -, -, -, k11, c12, c13, hret⟩
  have hb := bit_of_loads l2 m3 l3
  have w3 : word 3 0 = gen ^ 1 + 1 := word_two_pow_xor_one (a := 1) (by norm_num)
  have h0 : σ (.n 0) = σ (.n 2) := (eq_of_add_E e2).symm
  have hv := eOfNat_bv hb
  refine ⟨bv (σ (.n 2)), by simpa using bv_le _, by rw [h0]; exact hv, fun k hk ↦ absurd hk (by simp [cbitsE]),
    ?_, _, _, _, hret.symm, ?_, ?_⟩
  · have : bitE (bv (σ (.n 2))) 0 = σ (.n 2) := by
      rw [bitE_zero]
      by_cases h1 : σ (.n 2) = 1
      · simp [bv, h1]
      · have : σ (.n 2) = 0 := by rw [hv]; simp [bv, h1, eOfNat_zero]
        simp [bv, this]
    rw [this]; exact l2
  · rw [k11, a7, m6, c5, c4, word_one, w3, bit_factor hb.symm]
    simp [bv]
  · rw [c12, c13, word_one]
    simp

/-- The specializations' names, `table_size__L{h}`, `h ≤ 24` (`N_ROW_LOGS`). -/
def tsNames : List String := ["table_size__L0", "table_size__L1", "table_size__L2", "table_size__L3", "table_size__L4", "table_size__L5", "table_size__L6", "table_size__L7", "table_size__L8", "table_size__L9", "table_size__L10", "table_size__L11", "table_size__L12", "table_size__L13", "table_size__L14", "table_size__L15", "table_size__L16", "table_size__L17", "table_size__L18", "table_size__L19", "table_size__L20", "table_size__L21", "table_size__L22", "table_size__L23", "table_size__L24"]

/-- `table_size__L{h}`'s core IR implies its meaning. -/
def table_size_SoundP (P : Program) : Prop :=
  ∀ h ≤ 24, ∀ (rd : Reader) (args rets : List E),
    P.Rel rd (tsNames.getD h "") args rets → MeaningTS h rd args rets

set_option maxRecDepth 100000 in
theorem table_size_L0_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 0 "") args rets → MeaningTS 0 rd args rets :=
  ts0_sound (f := fn% «table_size__L0») (coreProgram_find?_at (j := idx% «table_size__L0») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L1_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 1 "") args rets → MeaningTS 1 rd args rets :=
  ts1_sound (f := fn% «table_size__L1») (coreProgram_find?_at (j := idx% «table_size__L1») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L2_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 2 "") args rets → MeaningTS 2 rd args rets :=
  ts_sound (h := 2) (by norm_num) (by norm_num) (f := fn% «table_size__L2»)
    (coreProgram_find?_at (j := idx% «table_size__L2») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L3_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 3 "") args rets → MeaningTS 3 rd args rets :=
  ts_sound (h := 3) (by norm_num) (by norm_num) (f := fn% «table_size__L3»)
    (coreProgram_find?_at (j := idx% «table_size__L3») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L4_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 4 "") args rets → MeaningTS 4 rd args rets :=
  ts_sound (h := 4) (by norm_num) (by norm_num) (f := fn% «table_size__L4»)
    (coreProgram_find?_at (j := idx% «table_size__L4») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L5_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 5 "") args rets → MeaningTS 5 rd args rets :=
  ts_sound (h := 5) (by norm_num) (by norm_num) (f := fn% «table_size__L5»)
    (coreProgram_find?_at (j := idx% «table_size__L5») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L6_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 6 "") args rets → MeaningTS 6 rd args rets :=
  ts_sound (h := 6) (by norm_num) (by norm_num) (f := fn% «table_size__L6»)
    (coreProgram_find?_at (j := idx% «table_size__L6») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L7_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 7 "") args rets → MeaningTS 7 rd args rets :=
  ts_sound (h := 7) (by norm_num) (by norm_num) (f := fn% «table_size__L7»)
    (coreProgram_find?_at (j := idx% «table_size__L7») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L8_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 8 "") args rets → MeaningTS 8 rd args rets :=
  ts_sound (h := 8) (by norm_num) (by norm_num) (f := fn% «table_size__L8»)
    (coreProgram_find?_at (j := idx% «table_size__L8») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L9_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 9 "") args rets → MeaningTS 9 rd args rets :=
  ts_sound (h := 9) (by norm_num) (by norm_num) (f := fn% «table_size__L9»)
    (coreProgram_find?_at (j := idx% «table_size__L9») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L10_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 10 "") args rets → MeaningTS 10 rd args rets :=
  ts_sound (h := 10) (by norm_num) (by norm_num) (f := fn% «table_size__L10»)
    (coreProgram_find?_at (j := idx% «table_size__L10») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L11_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 11 "") args rets → MeaningTS 11 rd args rets :=
  ts_sound (h := 11) (by norm_num) (by norm_num) (f := fn% «table_size__L11»)
    (coreProgram_find?_at (j := idx% «table_size__L11») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L12_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 12 "") args rets → MeaningTS 12 rd args rets :=
  ts_sound (h := 12) (by norm_num) (by norm_num) (f := fn% «table_size__L12»)
    (coreProgram_find?_at (j := idx% «table_size__L12») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L13_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 13 "") args rets → MeaningTS 13 rd args rets :=
  ts_sound (h := 13) (by norm_num) (by norm_num) (f := fn% «table_size__L13»)
    (coreProgram_find?_at (j := idx% «table_size__L13») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L14_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 14 "") args rets → MeaningTS 14 rd args rets :=
  ts_sound (h := 14) (by norm_num) (by norm_num) (f := fn% «table_size__L14»)
    (coreProgram_find?_at (j := idx% «table_size__L14») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L15_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 15 "") args rets → MeaningTS 15 rd args rets :=
  ts_sound (h := 15) (by norm_num) (by norm_num) (f := fn% «table_size__L15»)
    (coreProgram_find?_at (j := idx% «table_size__L15») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L16_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 16 "") args rets → MeaningTS 16 rd args rets :=
  ts_sound (h := 16) (by norm_num) (by norm_num) (f := fn% «table_size__L16»)
    (coreProgram_find?_at (j := idx% «table_size__L16») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L17_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 17 "") args rets → MeaningTS 17 rd args rets :=
  ts_sound (h := 17) (by norm_num) (by norm_num) (f := fn% «table_size__L17»)
    (coreProgram_find?_at (j := idx% «table_size__L17») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L18_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 18 "") args rets → MeaningTS 18 rd args rets :=
  ts_sound (h := 18) (by norm_num) (by norm_num) (f := fn% «table_size__L18»)
    (coreProgram_find?_at (j := idx% «table_size__L18») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L19_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 19 "") args rets → MeaningTS 19 rd args rets :=
  ts_sound (h := 19) (by norm_num) (by norm_num) (f := fn% «table_size__L19»)
    (coreProgram_find?_at (j := idx% «table_size__L19») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L20_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 20 "") args rets → MeaningTS 20 rd args rets :=
  ts_sound (h := 20) (by norm_num) (by norm_num) (f := fn% «table_size__L20»)
    (coreProgram_find?_at (j := idx% «table_size__L20») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L21_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 21 "") args rets → MeaningTS 21 rd args rets :=
  ts_sound (h := 21) (by norm_num) (by norm_num) (f := fn% «table_size__L21»)
    (coreProgram_find?_at (j := idx% «table_size__L21») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L22_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 22 "") args rets → MeaningTS 22 rd args rets :=
  ts_sound (h := 22) (by norm_num) (by norm_num) (f := fn% «table_size__L22»)
    (coreProgram_find?_at (j := idx% «table_size__L22») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L23_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 23 "") args rets → MeaningTS 23 rd args rets :=
  ts_sound (h := 23) (by norm_num) (by norm_num) (f := fn% «table_size__L23»)
    (coreProgram_find?_at (j := idx% «table_size__L23») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem table_size_L24_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tsNames.getD 24 "") args rets → MeaningTS 24 rd args rets :=
  ts_sound (h := 24) (by norm_num) (by norm_num) (f := fn% «table_size__L24»)
    (coreProgram_find?_at (j := idx% «table_size__L24») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

/-- **Every `table_size__L{h}` implies its meaning.** -/
theorem table_size_sound : table_size_SoundP coreProgram := by
  intro h hh
  interval_cases h
  exacts [table_size_L0_sound, table_size_L1_sound, table_size_L2_sound, table_size_L3_sound, table_size_L4_sound, table_size_L5_sound, table_size_L6_sound, table_size_L7_sound, table_size_L8_sound, table_size_L9_sound, table_size_L10_sound, table_size_L11_sound, table_size_L12_sound, table_size_L13_sound, table_size_L14_sound, table_size_L15_sound, table_size_L16_sound, table_size_L17_sound, table_size_L18_sound, table_size_L19_sound, table_size_L20_sound, table_size_L21_sound, table_size_L22_sound, table_size_L23_sound, table_size_L24_sound]

end
end LeanVM.Guest.B1.Link
