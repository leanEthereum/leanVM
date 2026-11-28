/-
  LeanVM.Guest.B1.Link.Terminal

  B1 for `link_terminal` (pointer widths `19` to `24`): the link's terminal check.
-/

module

public import LeanVM.Guest.B1.Link.EqTree
public import LeanVM.Guest.B1.Link.Forms
public import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.CoreRef

/-!
# `link_terminal`

`link_terminal(r, sent, coef, shifts, cert_w, nu, rest, claim, w)` (G) checks the summand at the
end point (`Functionals::summand`, `link.rs`) against the claim, at the `w`-bit chunking
(`Chunks.new w`): chunk `i`'s eq table by `eqtree` into a buffer `eqs` at `step·i`
(`step = 2^(width_0 + 1)`), its values `D_i(r)` and `D_i(1 + r)` against the slices at
`sent[80 + word_shift_i ..]`, chunk `0`'s shifted reads `T_s`, `s = 1 .. 12`, the product, the
mirror certificate under `cert_w·nu_i`, and `low + cert + rest == claim`.

Its specialization `link_terminal__L{w}` is `ltBody (Chunks.new w) cw`, `cw` the buffer's size
word (`link_terminal_L{w}_body`, by the kernel): the template is built from the Statement's own
`Chunks.new`, so the guest's chunk tables (`CHUNK_*`) are checked to be the verifier's.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- Chunk `i`'s width, first index bit and first word bit. -/
def cW (c : Chunks) (i : ℕ) : ℕ := c.widths.getD i 0

def cI (c : Chunks) (i : ℕ) : ℕ := c.indexShifts.getD i 0

def cS (c : Chunks) (i : ℕ) : ℕ := c.wordShifts.getD i 0

/-- `Σ_{j < n} f j`. -/
def psum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => psum f n + f n

/-- The values of an `eqtree` over `w ≥ 1` coordinates. -/
def eqtCount (w : ℕ) : ℕ := 3 * w + 3 * 2 ^ w - 6

/-- The eq tables' stride in `eqs`. -/
def ltStep (c : Chunks) : ℕ := 2 ^ (cW c 0 + 1)

/-- The first value of chunk `i`'s `eqtree`. -/
def ltEqS (c : Chunks) (i : ℕ) : ℕ := 10 + psum (fun j ↦ eqtCount (cW c j)) i

/-- The first value of chunk `i`'s sums. -/
def ltDS (c : Chunks) (i : ℕ) : ℕ := ltEqS c c.d + psum (fun j ↦ 7 * 2 ^ cW c j) i

/-- `vals[i]`, `vals[d + i]`: `D_i(r)`, `D_i(1 + r)`. -/
def ltVal (c : Chunks) (i : ℕ) : ℕ := ltDS c i + 7 * 2 ^ cW c i - 2

def ltValR (c : Chunks) (i : ℕ) : ℕ := ltDS c i + 7 * 2 ^ cW c i - 1

/-- The running sums after word `v` of chunk `i`. -/
def ltAcc (c : Chunks) (i v : ℕ) : ℕ := if v = 0 then ltDS c i + 2 else ltDS c i + 7 * v + 1

def ltAccR (c : Chunks) (i v : ℕ) : ℕ := if v = 0 then ltDS c i + 4 else ltDS c i + 7 * v + 4

/-- Word `v` of chunk `i`'s sums. -/
def ltDBlk (c : Chunks) (i v : ℕ) : List Stmt :=
  let s0 := ltDS c i
  let n := 2 ^ cW c i
  let a0 := ltStep c * i + n - 2
  let o := 80 + cS c i
  if v = 0 then
    [.atom (.load (.n s0) (.n 1) o), .atom (.load (.n (s0 + 1)) (.n 9) a0),
      .atom (.mul (.n (s0 + 2)) (.n (s0 + 1)) (.n s0)),
      .atom (.load (.n (s0 + 3)) (.n 9) (a0 + n - 1)),
      .atom (.mul (.n (s0 + 4)) (.n (s0 + 3)) (.n s0))]
  else
    let b := s0 + 7 * v - 2
    [.atom (.load (.n b) (.n 1) (o + v)), .atom (.load (.n (b + 1)) (.n 9) (a0 + v)),
      .atom (.mul (.n (b + 2)) (.n (b + 1)) (.n b)),
      .atom (.add (.n (b + 3)) (.n (ltAcc c i (v - 1))) (.n (b + 2))),
      .atom (.load (.n (b + 4)) (.n 9) (a0 + n - 1 - v)),
      .atom (.mul (.n (b + 5)) (.n (b + 4)) (.n b)),
      .atom (.add (.n (b + 6)) (.n (ltAccR c i (v - 1))) (.n (b + 5)))]

/-- Chunk `i`'s sums and their copies into `vals`. -/
def ltD (c : Chunks) (i : ℕ) : List Stmt :=
  ((List.range (2 ^ cW c i)).map (ltDBlk c i)).flatten ++
    [.atom (.copy (.n (ltVal c i)) (.n (ltAcc c i (2 ^ cW c i - 1)))),
      .atom (.copy (.n (ltValR c i)) (.n (ltAccR c i (2 ^ cW c i - 1))))]

/-- `low = coef·vals[0]`. -/
def ltLow0 (c : Chunks) : ℕ := ltDS c c.d

/-- Chunk `0`'s size, `n0`. -/
def ltN0 (c : Chunks) : ℕ := 2 ^ cW c 0

/-- The first value of shift `s ≥ 1`'s block. -/
def ltShS (c : Chunks) (s : ℕ) : ℕ := ltLow0 c + 1 + psum (fun k ↦ 4 * (ltN0 c - (k + 1)) + 2) (s - 1)

/-- `low` after shift `s`. -/
def ltLowS (c : Chunks) (s : ℕ) : ℕ :=
  if s = 0 then ltLow0 c else ltShS c s + 4 * (ltN0 c - s) + 1

/-- Shift `s`'s block: `T_s` (`n0 - s` terms), times `shifts[s - 1]`, into `low`. -/
def ltShBlk (c : Chunks) (s : ℕ) : List Stmt :=
  let q := ltShS c s
  let n0 := ltN0 c
  let m := n0 - s
  [.atom (.load (.n q) (.n 9) (n0 - 2 + s)), .atom (.load (.n (q + 1)) (.n 1) 80),
    .atom (.mul (.n (q + 2)) (.n q) (.n (q + 1)))] ++
  ((List.range (m - 1)).map fun v' ↦
    let v := v' + 1
    let b := q + 4 * v - 1
    [.atom (.load (.n b) (.n 9) (n0 - 2 + v + s)), .atom (.load (.n (b + 1)) (.n 1) (80 + v)),
      .atom (.mul (.n (b + 2)) (.n b) (.n (b + 1))),
      .atom (.add (.n (b + 3)) (.n (q + 4 * (v - 1) + 2)) (.n (b + 2)))]).flatten ++
  [.atom (.load (.n (q + 4 * m - 1)) (.n 3) (s - 1)),
    .atom (.mul (.n (q + 4 * m)) (.n (q + 4 * m - 1)) (.n (q + 4 * m - 2))),
    .atom (.add (.n (q + 4 * m + 1)) (.n (ltLowS c (s - 1))) (.n (q + 4 * m)))]

/-- `low` after the shifts, then the products. -/
def ltL (c : Chunks) : ℕ := ltLowS c 12

/-- The first value of chunk `i`'s certificate block, and the certificate after it. -/
def ltCS (c : Chunks) (i : ℕ) : ℕ :=
  ltL c + c.d + psum (fun j ↦ 4 * cW c j + 4 + if j = 0 then 0 else 1) i

def ltCert (c : Chunks) (i : ℕ) : ℕ := ltCS c i + 4 * cW c i + 3 + if i = 0 then 0 else 1

/-- Chunk `i`'s certificate block: `cert_w·nu_i`, the mirror, `vals[i]·vals[d + i] + mirror`. -/
def ltCertBlk (c : Chunks) (i : ℕ) : List Stmt :=
  let k := ltCS c i
  let M := k + 4 * cW c i
  [.atom (.load (.n k) (.n 5) i), .atom (.mul (.n (k + 1)) (.n 4) (.n k)),
    .atom (.load (.n (k + 2)) (.n 0) (cI c i)), .atom (.mul (.n (k + 3)) (.n (k + 2)) (.n (k + 2))),
    .atom (.add (.n (k + 4)) (.n (k + 3)) (.n (k + 2)))] ++
  ((List.range (cW c i - 1)).map fun j' ↦
    let j := j' + 1
    let b := k + 4 * j + 1
    [.atom (.load (.n b) (.n 0) (cI c i + j)), .atom (.mul (.n (b + 1)) (.n b) (.n b)),
      .atom (.add (.n (b + 2)) (.n (b + 1)) (.n b)),
      .atom (.mul (.n (b + 3)) (.n (k + 4 * j)) (.n (b + 2)))]).flatten ++
  [.atom (.mul (.n (M + 1)) (.n (ltVal c i)) (.n (ltValR c i))),
    .atom (.add (.n (M + 2)) (.n (M + 1)) (.n M)), .atom (.mul (.n (M + 3)) (.n (k + 1)) (.n (M + 2)))] ++
  (if i = 0 then [] else [.atom (.add (.n (M + 4)) (.n (ltCert c (i - 1))) (.n (M + 3)))])

/-- The final check's first value. -/
def ltF (c : Chunks) : ℕ := ltCert c (c.d - 1) + 1

/-- The atoms of `link_terminal`'s expansion. -/
def ltAtoms (c : Chunks) (cw : ℕ) : List Stmt :=
  [.atom (.const (.n 8) (word cw 0)), .atom (.hint (.allocDyn (.n 9) (.n 8)))] ++
  ((List.range c.d).map fun i ↦ eqtreeAt (.n 0) (.n 9) (cI c i) (ltStep c * i) (ltEqS c i) (cW c i)).flatten ++
  ((List.range c.d).map (ltD c)).flatten ++
  [.atom (.mul (.n (ltLow0 c)) (.n 2) (.n (ltVal c 0)))] ++
  ((List.range 12).map fun s ↦ ltShBlk c (s + 1)).flatten ++
  ((List.range (c.d - 1)).map fun i ↦ .atom (.mul (.n (ltL c + i + 1)) (.n (ltL c + i)) (.n (ltVal c (i + 1))))) ++
  ((List.range c.d).map (ltCertBlk c)).flatten ++
  [.atom (.add (.n (ltF c)) (.n (ltL c + c.d - 1)) (.n (ltCert c (c.d - 1)))),
    .atom (.add (.n (ltF c + 1)) (.n (ltF c)) (.n 6)), .atom (.assertEq (.n (ltF c + 1)) (.n 7)),
    .atom (.const (.n (ltF c + 2)) (word 0 0))]

/-- The expansion of `link_terminal__L{w}` at the chunking `c` and the buffer's size word `cw`. -/
def ltBody (c : Chunks) (cw : ℕ) : List Stmt := ltAtoms c cw ++ [.ret [.n (ltF c + 2)]]

/-- The specializations' names, `link_terminal__L{w}`, `19 ≤ w ≤ 24`. -/
def ltNames : List String := ["link_terminal__L19", "link_terminal__L20", "link_terminal__L21", "link_terminal__L22", "link_terminal__L23", "link_terminal__L24"]

/-! ## The meaning -/

/-- What `link_terminal` checks at the chunking `c`: for the words `rs` of the index point at `r`,
the `64` slices at `sent[80 ..]`, the twelve shift coefficients at `shifts` and the chunks' `ν` at
`nu`, the Statement's summand (`Functionals.summand` at `max_shift = 12`, the certificates
`cert_w·ν_i`) plus `rest` is the claim. -/
def LtHolds (c : Chunks) (rd : Reader) (r sent coef shifts certW nu rest claim : E) : Prop :=
  ∀ rs sl shs nus : List E, rs.length = c.width → sl.length = 64 → shs.length = 12 →
    nus.length = c.d → ReadsAt rd r rs → (∀ k < 64, LoadHolds rd sent (80 + k) (sl.getD k 0)) →
    ReadsAt rd shifts shs → ReadsAt rd nu nus →
    (Functionals.new c rs 12).summand coef shs ((Functionals.new c rs 12).values c sl)
      (nus.map (certW * ·)) + rest = claim

/-- **`link_terminal(r, sent, coef, shifts, cert_w, nu, rest, claim, w)`**: it returns `0`, and the
terminal check holds at `Chunks.new w`. -/
def MeaningLinkTerminal (w : ℕ) (rd : Reader) : List E → List E → Prop
  | [r, sent, coef, shifts, certW, nu, rest, claim], rets =>
      rets = [0] ∧ ∀ c, Chunks.new w = some c → LtHolds c rd r sent coef shifts certW nu rest claim
  | _, _ => False

/-- `link_terminal__L{w}`'s core IR implies its meaning. -/
def link_terminal_SoundP (P : Program) : Prop :=
  ∀ w, 19 ≤ w → w ≤ 24 → ∀ (rd : Reader) (args rets : List E),
    P.Rel rd (ltNames.getD (w - 19) "") args rets → MeaningLinkTerminal w rd args rets

/-- The chunking's facts the template's proof reads, decided at each width. -/
structure ChunkOk (c : Chunks) : Prop where
  d_pos : 1 ≤ c.d
  w0 : cW c 0 = 4
  s0 : cS c 0 = 0
  wpos : ∀ i < c.d, 1 ≤ cW c i
  idx : ∀ i < c.d, cI c i + cW c i ≤ c.width
  word : ∀ i < c.d, cS c i + 2 ^ cW c i ≤ 64

/-! ## Lists -/

theorem sumE_snoc (l : List E) (x : E) : sumE (l ++ [x]) = sumE l + x := by
  rw [sumE_append, sumE_cons, sumE_nil, add_zero]

theorem prodE_snoc (l : List E) (x : E) : prodE (l ++ [x]) = prodE l * x := by
  rw [prodE_append, prodE_cons, prodE_nil, mul_one]

theorem sumE_range_succ (f : ℕ → E) (n : ℕ) :
    sumE ((List.range (n + 1)).map f) = sumE ((List.range n).map f) + f n := by
  rw [List.range_succ, List.map_append, List.map_singleton, sumE_snoc]

theorem prodE_range_succ (f : ℕ → E) (n : ℕ) :
    prodE ((List.range (n + 1)).map f) = prodE ((List.range n).map f) * f n := by
  rw [List.range_succ, List.map_append, List.map_singleton, prodE_snoc]

/-- A running sum, its first term folded in: the sum of its terms. -/
theorem run_sum {acc t : ℕ → E} (h0 : acc 0 = t 0) (hs : ∀ v, acc (v + 1) = acc v + t (v + 1)) :
    ∀ v, acc v = sumE ((List.range (v + 1)).map t)
  | 0 => by rw [h0]; simp [sumE]
  | v + 1 => by rw [hs, run_sum h0 hs v, sumE_range_succ t (v + 1)]

/-- Terms that vanish past `m` add nothing. -/
theorem sumE_range_zero {f : ℕ → E} {m n : ℕ} (hmn : m ≤ n) (hz : ∀ v, m ≤ v → v < n → f v = 0) :
    sumE ((List.range n).map f) = sumE ((List.range m).map f) := by
  induction n with
  | zero => obtain rfl : m = 0 := by omega
            rfl
  | succ n ih =>
    rcases Nat.lt_or_ge n m with h | h
    · obtain rfl : m = n + 1 := by omega
      rfl
    · rw [sumE_range_succ, ih h fun v h1 h2 ↦ hz v h1 (by omega), hz n h (by omega), add_zero]

theorem zipWith_mul_eq_range (a b : List E) (n : ℕ) (ha : a.length = n) (hb : n ≤ b.length) :
    List.zipWith (· * ·) a b = (List.range n).map fun v ↦ a.getD v 0 * b.getD v 0 := by
  apply List.ext_getElem (by simp [ha]; omega)
  intro v h1 h2
  simp only [List.length_map, List.length_range] at h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show v < a.length by omega),
    List.getElem?_eq_getElem (show v < b.length by omega)]

theorem length_eqKernel (pt : List E) : (eqKernel pt).length = 2 ^ pt.length :=
  LeanVM.Protocol.Hotwire.eqKernel_length pt

theorem getD_reverse_eq (l : List E) (v : ℕ) (hv : v < l.length) :
    l.reverse.getD v 0 = l.getD (l.length - 1 - v) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_reverse hv]

/-! ## The proof -/

theorem getD_drop_eq (l : List E) (k v : ℕ) : (l.drop k).getD v 0 = l.getD (k + v) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]


/-- The atoms of the template are atoms. -/
def isAtomsB : List Stmt → Bool
  | [] => true
  | .atom _ :: ss => isAtomsB ss
  | _ :: _ => false

theorem allAtoms_of_isAtomsB : ∀ {ss : List Stmt}, isAtomsB ss = true → AllAtoms ss
  | [], _ => allAtoms_nil
  | .atom _ :: ss, h => allAtoms_cons (allAtoms_of_isAtomsB (ss := ss) h)
  | .ite .. :: _, h => by simp [isAtomsB] at h
  | .match_ .. :: _, h => by simp [isAtomsB] at h
  | .call .. :: _, h => by simp [isAtomsB] at h
  | .callIf .. :: _, h => by simp [isAtomsB] at h
  | .dispatch .. :: _, h => by simp [isAtomsB] at h
  | .ret .. :: _, h => by simp [isAtomsB] at h

/-! ## The Statement's summand -/

/-- Chunk `i`'s mirror term, `Π x·(1 + x)` over its coordinates. -/
def ltMir (rs : List E) (c : Chunks) (i : ℕ) : E := prodE ((c.part rs i).map fun x ↦ x * (1 + x))


/-- `D_i(r)` and `D_i(1 + r)`, the Statement's chunk values. -/
def ltDv (rs sl : List E) (c : Chunks) (i : ℕ) : E :=
  sumE (List.zipWith (· * ·) (eqKernel (c.part rs i)) (sl.drop (cS c i)))

def ltDRv (rs sl : List E) (c : Chunks) (i : ℕ) : E :=
  sumE (List.zipWith (· * ·) (eqKernel (c.part rs i)).reverse (sl.drop (cS c i)))

/-- `T_s`, the Statement's shifted read. -/
def ltTw (rs sl : List E) (c : Chunks) (s : ℕ) : E :=
  sumE (List.zipWith (· * ·) (linkWindowShift (eqKernel (c.part rs 0)) s) (sl.drop (cS c 0)))

theorem zip_range_self_map {α : Type} (g : ℕ → α) (n : ℕ) :
    (List.range n).zip ((List.range n).map g) = (List.range n).map fun i ↦ (i, g i) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, List.zip_append, ih]

theorem headD_range_map {α : Type} (f : ℕ → α) (d : ℕ) (hd : 1 ≤ d) (x : α) :
    ((List.range d).map f).headD x = f 0 := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [List.range_succ_eq_map]
  rfl

theorem values_eq (c : Chunks) (hd : 1 ≤ c.d) (rs sl : List E) :
    (Functionals.new c rs 12).values c sl = (List.range c.d).map (ltDv rs sl c) ++
      (List.range c.d).map (ltDRv rs sl c) ++ (List.range 12).map fun s ↦ ltTw rs sl c (s + 1) := by
  unfold Functionals.values Functionals.new
  simp only [zip_range_self_map, List.map_append, List.map_map, headD_range_map _ _ hd]
  rfl

theorem getD_range_map (f : ℕ → E) {n i : ℕ} (hi : i < n) : ((List.range n).map f).getD i 0 = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- `Functionals::summand` on values `A ++ B ++ C`: `A` at `r`, `B` at `1 + r`, `C` the shifts. -/
theorem summand_split (f : Functionals) (coef : E) (shs certs A B C : List E) (hAl : A.length = f.d)
    (hBl : B.length = f.d) (hd : 1 ≤ f.d) (hshl : shs.length = 12) (hCl : C.length = 12) :
    f.summand coef shs (A ++ B ++ C) certs =
      (coef * (A ++ B ++ C).getD 0 0 + sumE ((List.range 12).map fun s ↦ shs.getD s 0 * C.getD s 0)) *
        prodE ((A.drop 1).take (f.d - 1)) +
      sumE ((List.range f.d).map fun i ↦
        certs.getD i 0 * (A.getD i 0 * B.getD i 0 + f.mirrors.getD i 0)) := by
  have gA : ∀ i < f.d, (A ++ B ++ C).getD i 0 = A.getD i 0 := fun i hi ↦ by
    rw [List.getD_append _ _ _ _ (by simp [hAl, hBl]; omega), List.getD_append _ _ _ _ (by omega)]
  have gB : ∀ i < f.d, (A ++ B ++ C).getD (f.d + i) 0 = B.getD i 0 := fun i hi ↦ by
    rw [List.getD_append _ _ _ _ (by simp [hAl, hBl]; omega),
      List.getD_append_right _ _ _ _ (by omega), hAl, Nat.add_sub_cancel_left]
  have dC : (A ++ B ++ C).drop (2 * f.d) = C := List.drop_left' (by simp [hAl, hBl]; omega)
  have tA : ((A ++ B ++ C).drop 1).take (f.d - 1) = (A.drop 1).take (f.d - 1) := by
    rw [List.append_assoc, List.drop_append_of_le_length (by omega), List.take_append_of_le_length
      (by simp [hAl])]
  unfold Functionals.summand
  dsimp only
  rw [dC, tA, zipWith_mul_eq_range shs C 12 hshl (by omega)]
  refine congrArg₂ (· + ·) rfl (congrArg sumE (List.map_congr_left fun i hi ↦ ?_))
  have hi' := List.mem_range.mp hi
  rw [gA i hi', gB i hi']

/-- **The Statement's summand**, written as the guest sums it. -/
theorem summand_eq (c : Chunks) (hd : 1 ≤ c.d) (rs sl shs certs : List E) (coef : E)
    (hshl : shs.length = 12) :
    (Functionals.new c rs 12).summand coef shs ((Functionals.new c rs 12).values c sl) certs =
      (coef * ltDv rs sl c 0 + sumE ((List.range 12).map fun s ↦ shs.getD s 0 * ltTw rs sl c (s + 1))) *
        prodE ((List.range (c.d - 1)).map fun i ↦ ltDv rs sl c (i + 1)) +
      sumE ((List.range c.d).map fun i ↦
        certs.getD i 0 * (ltDv rs sl c i * ltDRv rs sl c i + ltMir rs c i)) := by
  have hfd : (Functionals.new c rs 12).d = c.d := rfl
  have hmir : ∀ i < c.d, (Functionals.new c rs 12).mirrors.getD i 0 = ltMir rs c i := fun i hi ↦ by
    rw [show (Functionals.new c rs 12).mirrors =
      (List.range c.d).map fun i ↦ prodE ((c.part rs i).map fun x ↦ x * (1 + x)) from rfl,
      getD_range_map _ hi]
    rfl
  rw [values_eq c hd, summand_split _ coef shs certs _ _ _ (by simp [hfd]) (by simp [hfd]) (by rw [hfd]; exact hd) hshl (by simp),
    hfd]
  have g0 : ((List.range c.d).map (ltDv rs sl c) ++ (List.range c.d).map (ltDRv rs sl c) ++
      (List.range 12).map fun s ↦ ltTw rs sl c (s + 1)).getD 0 0 = ltDv rs sl c 0 := by
    rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega),
      getD_range_map _ hd]
  have tA : (((List.range c.d).map (ltDv rs sl c)).drop 1).take (c.d - 1) =
      (List.range (c.d - 1)).map fun i ↦ ltDv rs sl c (i + 1) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp
  rw [g0, tA]
  refine congrArg₂ (· + ·) (congrArg₂ (· * ·) (congrArg₂ (· + ·) rfl (congrArg sumE
    (List.map_congr_left fun s hs ↦ ?_))) rfl) (congrArg sumE (List.map_congr_left fun i hi ↦ ?_))
  · rw [getD_range_map _ (List.mem_range.mp hs)]
  · have hi' := List.mem_range.mp hi
    rw [getD_range_map _ hi', getD_range_map _ hi', hmir i hi']

/-- The shifted read `T_s` as the guest sums it: chunk `0`'s `16 - s` terms. -/
def ltTv (rs sl : List E) (c : Chunks) (s : ℕ) : E :=
  sumE ((List.range (16 - s)).map fun v ↦ (eqKernel (c.part rs 0)).getD (v + s) 0 * sl.getD v 0)

theorem ltTv_eq {c : Chunks} (hc : ChunkOk c) (rs sl : List E) (hrs : rs.length = c.width) (hsll : sl.length = 64)
    {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 12) : ltTv rs sl c s = ltTw rs sl c s := by
  set ek := eqKernel (c.part rs 0) with hek
  have hpl : (c.part rs 0).length = 4 := by
    have := hc.idx 0 hc.d_pos
    simp only [Chunks.part, List.length_take, List.length_drop, cW, cI] at *
    have h4 := hc.w0; simp only [cW] at h4; omega
  have hekl : ek.length = 16 := by rw [hek, length_eqKernel, hpl]; rfl
  have hlw : (linkWindowShift ek s).length = 16 := by simp [linkWindowShift, hekl]
  rw [ltTw, ← hek, hc.s0, List.drop_zero, zipWith_mul_eq_range _ sl 16 hlw (by omega), ltTv, ← hek]
  rw [sumE_range_zero (m := 16 - s) (n := 16) (by omega) fun v h1 h2 ↦ ?_]
  · refine congrArg sumE (List.map_congr_left fun v hv ↦ ?_)
    have hv' := List.mem_range.mp hv
    simp only [linkWindowShift, hekl]
    rw [getD_range_map _ (by omega)]
  · simp only [linkWindowShift, hekl]
    rw [getD_range_map _ h2, List.getD_eq_default _ _ (by omega), zero_mul]

section Proof

variable {rd : Reader} {σ : Val} {c : Chunks} {cw : ℕ}

theorem mem_ltAtoms_eqtree {i : ℕ} (hi : i < c.d) {a : Atom}
    (ha : Stmt.atom a ∈ eqtreeAt (.n 0) (.n 9) (cI c i) (ltStep c * i) (ltEqS c i) (cW c i)) :
    Stmt.atom a ∈ ltAtoms c cw := by
  unfold ltAtoms
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_flatten.mpr
    ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, ha⟩)))))))

theorem mem_ltAtoms_D {i : ℕ} (hi : i < c.d) {a : Atom} (ha : Stmt.atom a ∈ ltD c i) :
    Stmt.atom a ∈ ltAtoms c cw := by
  unfold ltAtoms
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_flatten.mpr
    ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, ha⟩))))))

theorem mem_ltAtoms_low0 : Stmt.atom (.mul (.n (ltLow0 c)) (.n 2) (.n (ltVal c 0))) ∈ ltAtoms c cw := by
  unfold ltAtoms
  simp

theorem mem_ltAtoms_sh {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 12) {a : Atom} (ha : Stmt.atom a ∈ ltShBlk c s) :
    Stmt.atom a ∈ ltAtoms c cw := by
  unfold ltAtoms
  simp only [List.mem_append]
  refine Or.inl (Or.inl (Or.inl (Or.inr (List.mem_flatten.mpr
    ⟨_, List.mem_map.mpr ⟨s - 1, List.mem_range.mpr (by omega), ?_⟩, ha⟩))))
  rw [Nat.sub_add_cancel hs1]

theorem mem_ltAtoms_prod {i : ℕ} (hi : i + 1 < c.d) :
    Stmt.atom (.mul (.n (ltL c + i + 1)) (.n (ltL c + i)) (.n (ltVal c (i + 1)))) ∈ ltAtoms c cw := by
  unfold ltAtoms
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩)))

theorem mem_ltAtoms_cert {i : ℕ} (hi : i < c.d) {a : Atom} (ha : Stmt.atom a ∈ ltCertBlk c i) :
    Stmt.atom a ∈ ltAtoms c cw := by
  unfold ltAtoms
  simp only [List.mem_append]
  exact Or.inl (Or.inr (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, ha⟩))

theorem mem_ltAtoms_fin {a : Atom}
    (ha : a ∈ [Atom.add (.n (ltF c)) (.n (ltL c + c.d - 1)) (.n (ltCert c (c.d - 1))),
      .add (.n (ltF c + 1)) (.n (ltF c)) (.n 6), .assertEq (.n (ltF c + 1)) (.n 7),
      .const (.n (ltF c + 2)) (word 0 0)]) :
    Stmt.atom a ∈ ltAtoms c cw := by
  unfold ltAtoms
  simp only [List.mem_append]
  refine Or.inr ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
  rcases ha with rfl | rfl | rfl | rfl <;> simp

variable (hA : ∀ a, Stmt.atom a ∈ ltAtoms c cw → a.Holds rd σ)
include hA

/-- **The eq tables**: chunk `i`'s `eqtree` holds `eqKernel` of its part of the index point. -/
theorem lt_eqtree (hc : ChunkOk c) {rs : List E} (hrs : rs.length = c.width)
    (hr : ReadsAt rd (σ (.n 0)) rs) {i : ℕ} (hi : i < c.d) :
    ∀ v < 2 ^ cW c i, LoadHolds rd (σ (.n 9)) (ltStep c * i + (2 ^ cW c i - 2 + v))
      ((eqKernel (c.part rs i)).getD v 0) := by
  have hpl : (c.part rs i).length = cW c i := by
    simp only [Chunks.part, List.length_take, List.length_drop, cW] at *
    have := hc.idx i hi; simp only [cW, cI] at this; omega
  have h := eqtreeAt_sound (hc.wpos i hi) (fun a ha ↦ hA a (mem_ltAtoms_eqtree hi ha)) hpl
    (fun t ht ↦ by
      have hk : cI c i + t < rs.length := by have := hc.idx i hi; omega
      have ht' : t < c.widths[i]?.getD 0 := by simpa [cW, List.getD_eq_getElem?_getD] using ht
      have e : (c.part rs i).getD t 0 = rs[cI c i + t] := by
        simp only [Chunks.part, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
          ht', ↓reduceIte]
        have hk' : c.indexShifts[i]?.getD 0 + t < rs.length := by simpa [cI, List.getD_eq_getElem?_getD] using hk
        rw [List.getElem?_eq_getElem hk', Option.getD_some]
        rfl
      rw [e]; exact hr _ hk)
    (cW c i) (hc.wpos i hi) le_rfl
  intro v hv
  have := h v hv
  rwa [← hpl, List.take_length, hpl] at this

/-- **Chunk `i`'s values**: `D_i(r)` and `D_i(1 + r)` against the slices. -/
theorem lt_D (hc : ChunkOk c) {rs sl : List E} (hrs : rs.length = c.width) (hr : ReadsAt rd (σ (.n 0)) rs)
    (hsll : sl.length = 64) (hsl : ∀ k < 64, LoadHolds rd (σ (.n 1)) (80 + k) (sl.getD k 0))
    {i : ℕ} (hi : i < c.d) :
    σ (.n (ltVal c i)) = sumE (List.zipWith (· * ·) (eqKernel (c.part rs i)) (sl.drop (cS c i))) ∧
      σ (.n (ltValR c i)) =
        sumE (List.zipWith (· * ·) (eqKernel (c.part rs i)).reverse (sl.drop (cS c i))) := by
  set n := 2 ^ cW c i with hn
  set ek := eqKernel (c.part rs i) with hek
  have hpl : (c.part rs i).length = cW c i := by
    simp only [Chunks.part, List.length_take, List.length_drop, cW] at *
    have := hc.idx i hi; simp only [cW, cI] at this; omega
  have hekl : ek.length = n := by rw [hek, length_eqKernel, hpl]
  have hn2 : 2 ≤ n := by
    have := hc.wpos i hi
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ cW c i := Nat.pow_le_pow_right (by norm_num) this
  have hword := hc.word i hi
  have hE := lt_eqtree hA hc hrs hr hi
  have blk : ∀ v < n, ∀ a, Stmt.atom a ∈ ltDBlk c i v → a.Holds rd σ := fun v hv a ha ↦
    hA a (mem_ltAtoms_D hi (List.mem_append_left _ (List.mem_flatten.mpr
      ⟨_, List.mem_map.mpr ⟨v, List.mem_range.mpr hv, rfl⟩, ha⟩)))
  have hcp := fun a (ha : a ∈ [Atom.copy (.n (ltVal c i)) (.n (ltAcc c i (n - 1))),
      .copy (.n (ltValR c i)) (.n (ltAccR c i (n - 1)))]) ↦
    hA a (mem_ltAtoms_D hi (List.mem_append_right _ (by simpa using ha)))
  have c1 : σ (.n (ltVal c i)) = σ (.n (ltAcc c i (n - 1))) :=
    hcp (.copy (.n (ltVal c i)) (.n (ltAcc c i (n - 1)))) (by simp)
  have c2 : σ (.n (ltValR c i)) = σ (.n (ltAccR c i (n - 1))) :=
    hcp (.copy (.n (ltValR c i)) (.n (ltAccR c i (n - 1)))) (by simp)
  -- the words of each block
  have hs : ∀ v < n, ∃ x, LoadHolds rd (σ (.n 1)) (80 + cS c i + v) x ∧ x = sl.getD (cS c i + v) 0 :=
    fun v hv ↦ ⟨_, by simpa [Nat.add_assoc] using hsl (cS c i + v) (by omega), rfl⟩
  have he : ∀ v < n, LoadHolds rd (σ (.n 9)) (ltStep c * i + n - 2 + v) (ek.getD v 0) := fun v hv ↦ by
    have := hE v hv
    rwa [show ltStep c * i + (2 ^ cW c i - 2 + v) = ltStep c * i + n - 2 + v by omega] at this
  let t : ℕ → E := fun v ↦ ek.getD v 0 * sl.getD (cS c i + v) 0
  let t' : ℕ → E := fun v ↦ ek.getD (n - 1 - v) 0 * sl.getD (cS c i + v) 0
  have hacc : ∀ v, v < n → σ (.n (ltAcc c i v)) = sumE ((List.range (v + 1)).map t) ∧
      σ (.n (ltAccR c i v)) = sumE ((List.range (v + 1)).map t') := by
    intro v hv
    induction v with
    | zero =>
      have a0 := blk 0 hv _ (by simp [ltDBlk] : Stmt.atom (.load (.n (ltDS c i)) (.n 1) (80 + cS c i)) ∈ _)
      have a1 := blk 0 hv _ (by simp [ltDBlk] : Stmt.atom (.load (.n (ltDS c i + 1)) (.n 9)
        (ltStep c * i + 2 ^ cW c i - 2)) ∈ _)
      have a2 := blk 0 hv _ (by simp [ltDBlk] : Stmt.atom (.mul (.n (ltDS c i + 2)) (.n (ltDS c i + 1))
        (.n (ltDS c i))) ∈ _)
      have a3 := blk 0 hv _ (by simp [ltDBlk] : Stmt.atom (.load (.n (ltDS c i + 3)) (.n 9)
        (ltStep c * i + 2 ^ cW c i - 2 + 2 ^ cW c i - 1)) ∈ _)
      have a4 := blk 0 hv _ (by simp [ltDBlk] : Stmt.atom (.mul (.n (ltDS c i + 4)) (.n (ltDS c i + 3))
        (.n (ltDS c i))) ∈ _)
      simp only [Atom.Holds] at a2 a4
      have e0 : σ (.n (ltDS c i)) = sl.getD (cS c i) 0 := by
        obtain ⟨x, hx, rfl⟩ := hs 0 hv; exact loadHolds_unique a0 (by simpa using hx)
      have e1 : σ (.n (ltDS c i + 1)) = ek.getD 0 0 := loadHolds_unique a1 (by simpa using he 0 hv)
      have e3 : σ (.n (ltDS c i + 3)) = ek.getD (n - 1) 0 := loadHolds_unique a3 (by
        have := he (n - 1) (by omega)
        rwa [show ltStep c * i + n - 2 + (n - 1) = ltStep c * i + 2 ^ cW c i - 2 + 2 ^ cW c i - 1 by
          omega] at this)
      refine ⟨?_, ?_⟩
      · simp only [ltAcc, ↓reduceIte, a2, e1, e0, t]; simp [sumE]
      · simp only [ltAccR, ↓reduceIte, a4, e3, e0, t']; simp [sumE]
    | succ v ih =>
      obtain ⟨i1, i2⟩ := ih (by omega)
      have hv' : v + 1 ≠ 0 := by omega
      set b := ltDS c i + 7 * (v + 1) - 2 with hb
      have a0 := blk (v + 1) hv _ (by simp [ltDBlk, ← hb] : Stmt.atom (.load (.n b) (.n 1)
        (80 + cS c i + (v + 1))) ∈ _)
      have a1 := blk (v + 1) hv _ (by simp [ltDBlk, ← hb] : Stmt.atom (.load (.n (b + 1)) (.n 9)
        (ltStep c * i + 2 ^ cW c i - 2 + (v + 1))) ∈ _)
      have a2 := blk (v + 1) hv _ (by simp [ltDBlk, ← hb] : Stmt.atom (.mul (.n (b + 2)) (.n (b + 1))
        (.n b)) ∈ _)
      have a3 := blk (v + 1) hv _ (by simp [ltDBlk, ← hb] : Stmt.atom (.add (.n (b + 3))
        (.n (ltAcc c i v)) (.n (b + 2))) ∈ _)
      have a4 := blk (v + 1) hv _ (by simp [ltDBlk, ← hb] : Stmt.atom (.load (.n (b + 4)) (.n 9)
        (ltStep c * i + 2 ^ cW c i - 2 + 2 ^ cW c i - 1 - (v + 1))) ∈ _)
      have a5 := blk (v + 1) hv _ (by simp [ltDBlk, ← hb] : Stmt.atom (.mul (.n (b + 5)) (.n (b + 4))
        (.n b)) ∈ _)
      have a6 := blk (v + 1) hv _ (by simp [ltDBlk, ← hb] : Stmt.atom (.add (.n (b + 6))
        (.n (ltAccR c i v)) (.n (b + 5))) ∈ _)
      simp only [Atom.Holds] at a2 a3 a5 a6
      have e0 : σ (.n b) = sl.getD (cS c i + (v + 1)) 0 := by
        obtain ⟨x, hx, rfl⟩ := hs (v + 1) hv; exact loadHolds_unique a0 hx
      have e1 : σ (.n (b + 1)) = ek.getD (v + 1) 0 := loadHolds_unique a1 (he (v + 1) hv)
      have e4 : σ (.n (b + 4)) = ek.getD (n - 1 - (v + 1)) 0 := loadHolds_unique a4 (by
        have := he (n - 1 - (v + 1)) (by omega)
        rwa [show ltStep c * i + n - 2 + (n - 1 - (v + 1)) =
          ltStep c * i + 2 ^ cW c i - 2 + 2 ^ cW c i - 1 - (v + 1) by omega] at this)
      have q1 : ltAcc c i (v + 1) = b + 3 := by simp only [ltAcc, hv', ↓reduceIte, hb]; omega
      have q2 : ltAccR c i (v + 1) = b + 6 := by simp only [ltAccR, hv', ↓reduceIte, hb]; omega
      refine ⟨?_, ?_⟩
      · rw [q1, a3, a2, i1, e1, e0, sumE_range_succ t (v + 1)]
      · rw [q2, a6, a5, i2, e4, e0, sumE_range_succ t' (v + 1)]
  obtain ⟨f1, f2⟩ := hacc (n - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at f1 f2
  have hdl : n ≤ (sl.drop (cS c i)).length := by simp [hsll]; omega
  refine ⟨?_, ?_⟩
  · rw [c1, f1, zipWith_mul_eq_range ek _ n hekl hdl]
    refine congrArg sumE (List.map_congr_left fun v _ ↦ ?_)
    simp only [t, getD_drop_eq]
  · rw [c2, f2, zipWith_mul_eq_range ek.reverse _ n (by simp [hekl]) hdl]
    refine congrArg sumE (List.map_congr_left fun v hv ↦ ?_)
    have hv' : v < n := List.mem_range.mp hv
    simp only [t', getD_drop_eq, getD_reverse_eq ek v (by omega), hekl]

/-- **Shift `s`'s read**: `T_s`, chunk `0`'s table read `s` further, against the slices, and `low`
after it. -/
theorem lt_T (hc : ChunkOk c) {rs sl : List E} (hrs : rs.length = c.width) (hr : ReadsAt rd (σ (.n 0)) rs)
    (hsl : ∀ k < 64, LoadHolds rd (σ (.n 1)) (80 + k) (sl.getD k 0)) {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 12) :
    ∃ x, LoadHolds rd (σ (.n 3)) (s - 1) x ∧ σ (.n (ltLowS c s)) = σ (.n (ltLowS c (s - 1))) + x *
      sumE ((List.range (16 - s)).map fun v ↦ (eqKernel (c.part rs 0)).getD (v + s) 0 * sl.getD v 0) := by
  have hn0 : ltN0 c = 16 := by rw [ltN0, hc.w0]; rfl
  set q := ltShS c s with hq
  set m := 16 - s with hm
  set ek := eqKernel (c.part rs 0) with hek
  have hE := lt_eqtree hA hc hrs hr hc.d_pos
  rw [hc.w0] at hE
  have blk : ∀ a, Stmt.atom a ∈ ltShBlk c s → a.Holds rd σ := fun a ha ↦ hA a (mem_ltAtoms_sh hs1 hs ha)
  have he : ∀ v, v + s < 16 → LoadHolds rd (σ (.n 9)) (16 - 2 + v + s) (ek.getD (v + s) 0) := fun v hv ↦ by
    have := hE (v + s) (by norm_num; omega)
    rwa [Nat.mul_zero, Nat.zero_add, show 2 ^ 4 - 2 + (v + s) = 16 - 2 + v + s by omega] at this
  let t : ℕ → E := fun v ↦ ek.getD (v + s) 0 * sl.getD v 0
  have hacc : ∀ v < m, σ (.n (q + 4 * v + 2)) = sumE ((List.range (v + 1)).map t) := by
    intro v hv
    induction v with
    | zero =>
      have a0 := blk _ (by simp [ltShBlk, ← hq, hn0] : Stmt.atom (.load (.n q) (.n 9) (16 - 2 + s)) ∈ _)
      have a1 := blk _ (by simp [ltShBlk, ← hq] : Stmt.atom (.load (.n (q + 1)) (.n 1) 80) ∈ _)
      have a2 := blk _ (by simp [ltShBlk, ← hq] : Stmt.atom (.mul (.n (q + 2)) (.n q) (.n (q + 1))) ∈ _)
      simp only [Atom.Holds] at a2
      have e0 : σ (.n q) = ek.getD (0 + s) 0 := loadHolds_unique a0 (by simpa using he 0 (by omega))
      have e1 : σ (.n (q + 1)) = sl.getD 0 0 := loadHolds_unique a1 (by simpa using hsl 0 (by omega))
      rw [show q + 4 * 0 + 2 = q + 2 by ring, a2, e0, e1]
      simp [sumE, t]
    | succ v ih =>
      have ihv := ih (by omega)
      have mem : ∀ a ∈ [Atom.load (.n (q + 4 * (v + 1) - 1)) (.n 9) (ltN0 c - 2 + (v + 1) + s),
          .load (.n (q + 4 * (v + 1) - 1 + 1)) (.n 1) (80 + (v + 1)),
          .mul (.n (q + 4 * (v + 1) - 1 + 2)) (.n (q + 4 * (v + 1) - 1)) (.n (q + 4 * (v + 1) - 1 + 1)),
          .add (.n (q + 4 * (v + 1) - 1 + 3)) (.n (q + 4 * (v + 1 - 1) + 2)) (.n (q + 4 * (v + 1) - 1 + 2))],
          a.Holds rd σ := fun a ha ↦ blk a (by
        unfold ltShBlk
        refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatten.mpr
          ⟨_, List.mem_map.mpr ⟨v, List.mem_range.mpr (by rw [hn0]; omega), rfl⟩, ?_⟩))
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
        rcases ha with rfl | rfl | rfl | rfl <;> simp [← hq])
      have a0 := mem (.load (.n (q + 4 * (v + 1) - 1)) (.n 9) (ltN0 c - 2 + (v + 1) + s)) (by simp)
      have a1 := mem (.load (.n (q + 4 * (v + 1) - 1 + 1)) (.n 1) (80 + (v + 1))) (by simp)
      have a2 := mem (.mul (.n (q + 4 * (v + 1) - 1 + 2)) (.n (q + 4 * (v + 1) - 1))
        (.n (q + 4 * (v + 1) - 1 + 1))) (by simp)
      have a3 := mem (.add (.n (q + 4 * (v + 1) - 1 + 3)) (.n (q + 4 * (v + 1 - 1) + 2))
        (.n (q + 4 * (v + 1) - 1 + 2))) (by simp)
      simp only [Atom.Holds] at a2 a3
      rw [hn0] at a0
      have e0 : σ (.n (q + 4 * (v + 1) - 1)) = ek.getD (v + 1 + s) 0 :=
        loadHolds_unique a0 (he (v + 1) (by omega))
      have e1 : σ (.n (q + 4 * (v + 1) - 1 + 1)) = sl.getD (v + 1) 0 :=
        loadHolds_unique a1 (hsl (v + 1) (by omega))
      rw [show q + 4 * (v + 1) + 2 = q + 4 * (v + 1) - 1 + 3 by omega, a3,
        show v + 1 - 1 = v from rfl, ihv, a2, e0, e1, sumE_range_succ t (v + 1)]
  have mem : ∀ a ∈ [Atom.load (.n (q + 4 * m - 1)) (.n 3) (s - 1),
      .mul (.n (q + 4 * m)) (.n (q + 4 * m - 1)) (.n (q + 4 * m - 2)),
      .add (.n (q + 4 * m + 1)) (.n (ltLowS c (s - 1))) (.n (q + 4 * m))], a.Holds rd σ :=
    fun a ha ↦ blk a (by
      unfold ltShBlk
      refine List.mem_append_right _ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
      rcases ha with rfl | rfl | rfl <;> simp [← hq, hn0, ← hm])
  have a0 := mem (.load (.n (q + 4 * m - 1)) (.n 3) (s - 1)) (by simp)
  have a1 := mem (.mul (.n (q + 4 * m)) (.n (q + 4 * m - 1)) (.n (q + 4 * m - 2))) (by simp)
  have a2 := mem (.add (.n (q + 4 * m + 1)) (.n (ltLowS c (s - 1))) (.n (q + 4 * m))) (by simp)
  simp only [Atom.Holds] at a1 a2
  refine ⟨_, a0, ?_⟩
  have hl : ltLowS c s = q + 4 * m + 1 := by
    simp only [ltLowS, show s ≠ 0 by omega, ↓reduceIte, hn0, ← hq, ← hm]
  have hT := hacc (m - 1) (by omega)
  rw [show q + 4 * (m - 1) + 2 = q + 4 * m - 2 by omega, Nat.sub_add_cancel (by omega)] at hT
  rw [hl, a2, a1, hT]

/-- **`low` after the shifts**: `coef·D_0 + Σ_s shifts[s - 1]·T_s`. -/
theorem lt_low (hc : ChunkOk c) {rs sl shs : List E} (hrs : rs.length = c.width)
    (hr : ReadsAt rd (σ (.n 0)) rs) (hsl : ∀ k < 64, LoadHolds rd (σ (.n 1)) (80 + k) (sl.getD k 0))
    (hshl : shs.length = 12) (hsh : ReadsAt rd (σ (.n 3)) shs) :
    ∀ s ≤ 12, σ (.n (ltLowS c s)) = σ (.n 2) * σ (.n (ltVal c 0)) +
      sumE ((List.range s).map fun s' ↦ shs.getD s' 0 * ltTv rs sl c (s' + 1)) := by
  intro s hs
  induction s with
  | zero =>
    have a := hA _ mem_ltAtoms_low0
    simp only [Atom.Holds] at a
    simp only [ltLowS, ↓reduceIte, a, List.range_zero, List.map_nil, sumE_nil, add_zero]
  | succ s ih =>
    obtain ⟨x, hx, e⟩ := lt_T hA hc hrs hr hsl (s := s + 1) (by omega) hs
    have ex : x = shs.getD s 0 := by
      have := hsh s (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact loadHolds_unique hx this
    rw [e, Nat.add_sub_cancel, ih (by omega), sumE_range_succ, ex, add_assoc]
    rfl

/-- **The product** over chunks `1 .. d - 1`. -/
theorem lt_prod : ∀ j, j + 1 ≤ c.d → σ (.n (ltL c + j)) =
    σ (.n (ltL c)) * prodE ((List.range j).map fun i ↦ σ (.n (ltVal c (i + 1))))
  | 0, _ => by simp [prodE]
  | j + 1, hj => by
    have a := hA _ (mem_ltAtoms_prod (c := c) (cw := cw) (i := j) (by omega))
    simp only [Atom.Holds] at a
    rw [show ltL c + (j + 1) = ltL c + j + 1 by ring, a, lt_prod j (by omega), prodE_range_succ,
      mul_assoc]

/-- **The certificate**, through chunk `i`. -/
theorem lt_cert (hc : ChunkOk c) {rs nus : List E} (hrs : rs.length = c.width)
    (hr : ReadsAt rd (σ (.n 0)) rs) (hnul : nus.length = c.d) (hnu : ReadsAt rd (σ (.n 5)) nus) :
    ∀ i < c.d, σ (.n (ltCert c i)) = sumE ((List.range (i + 1)).map fun j ↦
      σ (.n 4) * nus.getD j 0 * (σ (.n (ltVal c j)) * σ (.n (ltValR c j)) + ltMir rs c j)) := by
  -- one chunk's term
  have term : ∀ i < c.d, σ (.n (ltCS c i + 4 * cW c i + 3)) =
      σ (.n 4) * nus.getD i 0 * (σ (.n (ltVal c i)) * σ (.n (ltValR c i)) + ltMir rs c i) := by
    intro i hi
    set k := ltCS c i with hk
    set w := cW c i with hw
    have hw1 := hc.wpos i hi
    have hidx := hc.idx i hi
    have blk : ∀ a, Stmt.atom a ∈ ltCertBlk c i → a.Holds rd σ := fun a ha ↦ hA a (mem_ltAtoms_cert hi ha)
    have hx : ∀ u < w, ∀ y, LoadHolds rd (σ (.n 0)) (cI c i + u) y → y = rs.getD (cI c i + u) 0 :=
      fun u hu y hy ↦ by
        have := hr (cI c i + u) (by omega)
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact loadHolds_unique hy this
    let xx : ℕ → E := fun u ↦ rs.getD (cI c i + u) 0 * (1 + rs.getD (cI c i + u) 0)
    have hmir : ∀ j < w, σ (.n (k + 4 * j + 4)) = prodE ((List.range (j + 1)).map xx) := by
      intro j hj
      induction j with
      | zero =>
        have mem : ∀ a ∈ [Atom.load (.n (k + 2)) (.n 0) (cI c i), .mul (.n (k + 3)) (.n (k + 2)) (.n (k + 2)),
            .add (.n (k + 4)) (.n (k + 3)) (.n (k + 2))], a.Holds rd σ := fun a ha ↦ blk a (by
          unfold ltCertBlk
          refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
          rcases ha with rfl | rfl | rfl <;> simp [← hk])
        have a0 := mem (.load (.n (k + 2)) (.n 0) (cI c i)) (by simp)
        have a1 := mem (.mul (.n (k + 3)) (.n (k + 2)) (.n (k + 2))) (by simp)
        have a2 := mem (.add (.n (k + 4)) (.n (k + 3)) (.n (k + 2))) (by simp)
        simp only [Atom.Holds] at a1 a2
        have e0 := hx 0 (by omega) _ (by rw [Nat.add_zero]; exact a0)
        rw [show k + 4 * 0 + 4 = k + 4 by ring, a2, a1, e0]
        simp [xx, prodE]
        ring
      | succ j ih =>
        set b := k + 4 * (j + 1) + 1 with hb
        have mem : ∀ a ∈ [Atom.load (.n b) (.n 0) (cI c i + (j + 1)), .mul (.n (b + 1)) (.n b) (.n b),
            .add (.n (b + 2)) (.n (b + 1)) (.n b), .mul (.n (b + 3)) (.n (k + 4 * (j + 1))) (.n (b + 2))],
            a.Holds rd σ := fun a ha ↦ blk a (by
          unfold ltCertBlk
          refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
            (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩, ?_⟩)))
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
          rcases ha with rfl | rfl | rfl | rfl <;> simp [← hk, ← hb])
        have a0 := mem (.load (.n b) (.n 0) (cI c i + (j + 1))) (by simp)
        have a1 := mem (.mul (.n (b + 1)) (.n b) (.n b)) (by simp)
        have a2 := mem (.add (.n (b + 2)) (.n (b + 1)) (.n b)) (by simp)
        have a3 := mem (.mul (.n (b + 3)) (.n (k + 4 * (j + 1))) (.n (b + 2))) (by simp)
        simp only [Atom.Holds] at a1 a2 a3
        have e0 := hx (j + 1) hj _ a0
        rw [show k + 4 * (j + 1) + 4 = b + 3 by omega, a3,
          show k + 4 * (j + 1) = k + 4 * j + 4 by ring, ih (by omega), a2, a1, e0,
          prodE_range_succ (n := j + 1)]
        simp only [xx]
        ring
    have mem : ∀ a ∈ [Atom.load (.n k) (.n 5) i, .mul (.n (k + 1)) (.n 4) (.n k),
        .mul (.n (k + 4 * w + 1)) (.n (ltVal c i)) (.n (ltValR c i)),
        .add (.n (k + 4 * w + 2)) (.n (k + 4 * w + 1)) (.n (k + 4 * w)),
        .mul (.n (k + 4 * w + 3)) (.n (k + 1)) (.n (k + 4 * w + 2))], a.Holds rd σ := fun a ha ↦ blk a (by
      unfold ltCertBlk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (by simp [← hk])))
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (by simp [← hk])))
      all_goals exact List.mem_append_left _ (List.mem_append_right _ (by simp [← hk, ← hw])))
    have a0 := mem (.load (.n k) (.n 5) i) (by simp)
    have a1 := mem (.mul (.n (k + 1)) (.n 4) (.n k)) (by simp)
    have a2 := mem (.mul (.n (k + 4 * w + 1)) (.n (ltVal c i)) (.n (ltValR c i))) (by simp)
    have a3 := mem (.add (.n (k + 4 * w + 2)) (.n (k + 4 * w + 1)) (.n (k + 4 * w))) (by simp)
    have a4 := mem (.mul (.n (k + 4 * w + 3)) (.n (k + 1)) (.n (k + 4 * w + 2))) (by simp)
    simp only [Atom.Holds] at a1 a2 a3 a4
    have enu : σ (.n k) = nus.getD i 0 := by
      have := hnu i (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact loadHolds_unique a0 this
    have hm := hmir (w - 1) (by omega)
    rw [show k + 4 * (w - 1) + 4 = k + 4 * w by omega, Nat.sub_add_cancel hw1] at hm
    have hpart : ltMir rs c i = prodE ((List.range w).map xx) := by
      rw [ltMir]
      refine congrArg prodE (List.ext_getElem (by simp [Chunks.part, cW, cI] at *; omega)
        fun u h1 h2 ↦ ?_)
      simp only [List.length_map, List.length_range] at h2
      simp only [List.getElem_map, List.getElem_range, xx, Chunks.part, List.getElem_take,
        List.getElem_drop, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show cI c i + u < rs.length by omega), Option.getD_some]
      rfl
    rw [a4, a1, a3, a2, hm, enu, hpart]
  intro i hi
  induction i with
  | zero =>
    rw [show ltCert c 0 = ltCS c 0 + 4 * cW c 0 + 3 by simp [ltCert], term 0 hi]
    simp [sumE]
  | succ i ih =>
    have hk := term (i + 1) hi
    have blk : ∀ a, Stmt.atom a ∈ ltCertBlk c (i + 1) → a.Holds rd σ := fun a ha ↦
      hA a (mem_ltAtoms_cert hi ha)
    have a := blk (.add (.n (ltCS c (i + 1) + 4 * cW c (i + 1) + 4)) (.n (ltCert c i))
      (.n (ltCS c (i + 1) + 4 * cW c (i + 1) + 3))) (by unfold ltCertBlk; simp)
    simp only [Atom.Holds] at a
    rw [show ltCert c (i + 1) = ltCS c (i + 1) + 4 * cW c (i + 1) + 4 by simp [ltCert], a,
      ih (by omega), hk, sumE_range_succ _ (i + 1)]

/-- **The terminal check**, from the template's atoms. -/
theorem lt_check (hc : ChunkOk c) :
    LtHolds c rd (σ (.n 0)) (σ (.n 1)) (σ (.n 2)) (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) (σ (.n 6))
      (σ (.n 7)) := by
  intro rs sl shs nus hrs hsll hshl hnul hr hsl hsh hnu
  have hd := hc.d_pos
  rw [summand_eq c hd rs sl shs _ (σ (.n 2)) hshl]
  have hD := fun i (hi : i < c.d) ↦ lt_D hA hc hrs hr hsll hsl hi
  have hlow := lt_low hA hc hrs hr hsl hshl hsh 12 le_rfl
  have hprod := lt_prod hA (c.d - 1) (by omega)
  have hcert := lt_cert hA hc hrs hr hnul hnu (c.d - 1) (by omega)
  rw [Nat.sub_add_cancel hd] at hcert
  have f1 := hA _ (mem_ltAtoms_fin (c := c) (cw := cw) (a := .add (.n (ltF c)) (.n (ltL c + c.d - 1))
    (.n (ltCert c (c.d - 1)))) (by simp))
  have f2 := hA _ (mem_ltAtoms_fin (c := c) (cw := cw) (a := .add (.n (ltF c + 1)) (.n (ltF c)) (.n 6))
    (by simp))
  have f3 := hA _ (mem_ltAtoms_fin (c := c) (cw := cw) (a := .assertEq (.n (ltF c + 1)) (.n 7)) (by simp))
  simp only [Atom.Holds] at f1 f2 f3
  have h7 : σ (.n 7) = σ (.n (ltF c + 1)) := by
    linear_combination (-1 : E) * f3 + (σ (.n 7)) * two_eq_zero_E
  rw [h7, f2, f1, show ltL c + c.d - 1 = ltL c + (c.d - 1) by omega, hprod, hcert,
    show ltL c = ltLowS c 12 from rfl, hlow, (hD 0 hd).1]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· * ·) (congrArg₂ (· + ·) rfl
    (congrArg sumE (List.map_congr_left fun s hs ↦ ?_))) (congrArg prodE (List.map_congr_left
      fun i hi ↦ ?_))) (congrArg sumE (List.map_congr_left fun i hi ↦ ?_))) rfl
  · have hs' := List.mem_range.mp hs
    rw [ltTv_eq hc rs sl hrs hsll (by omega) (by omega)]
  · have hi' := List.mem_range.mp hi
    rw [(hD (i + 1) (by omega)).1]
    rfl
  · have hi' := List.mem_range.mp hi
    rw [(hD i hi').1, (hD i hi').2]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (show i < nus.length by omega), Option.map_some, Option.getD_some]
    rfl

end Proof

/-- **The template's relation implies its meaning.** -/
theorem lt_sound (w : ℕ) (cw : ℕ) (hc : ChunkOk ((Chunks.new w).getD default))
    (hat : AllAtoms (ltAtoms ((Chunks.new w).getD default) cw)) {f : Fn}
    (hfind : coreProgram.find? (ltNames.getD (w - 19) "") = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hbody : f.body = ltBody ((Chunks.new w).getD default) cw) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (ltNames.getD (w - 19) "") args rets → MeaningLinkTerminal w rd args rets := by
  set c := (Chunks.new w).getD default with hcdef
  rw [rel_iff_sem hfind, hbody, hparams, ltBody]
  simp only [holdsList_append]
  rintro ⟨σ, rfl, h⟩
  obtain ⟨hA, hret⟩ := (holdsList_atoms hat _ _).mp h
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hret
  have h0 := hA _ (mem_ltAtoms_fin (c := c) (cw := cw) (a := .const (.n (ltF c + 2)) (word 0 0)) (by simp))
  simp only [Atom.Holds, word_zero] at h0
  refine ⟨by rw [← hret, h0], fun c' hc' ↦ ?_⟩
  have e : c' = c := by rw [hcdef, hc']; rfl
  subst e
  exact lt_check hA hc

/-! ## The specializations -/


set_option maxRecDepth 100000 in
theorem link_terminal_L19_body :
    Fn.body (fn% «link_terminal__L19») = ltBody ((Chunks.new 19).getD default) 7607 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem link_terminal_L20_body :
    Fn.body (fn% «link_terminal__L20») = ltBody ((Chunks.new 20).getD default) 7607 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem link_terminal_L21_body :
    Fn.body (fn% «link_terminal__L21») = ltBody ((Chunks.new 21).getD default) 32671816220672 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem link_terminal_L22_body :
    Fn.body (fn% «link_terminal__L22») = ltBody ((Chunks.new 22).getD default) 32671816220672 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem link_terminal_L23_body :
    Fn.body (fn% «link_terminal__L23») = ltBody ((Chunks.new 23).getD default) 69649 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem link_terminal_L24_body :
    Fn.body (fn% «link_terminal__L24») = ltBody ((Chunks.new 24).getD default) 299140177199104 :=
  stmtsEqb_sound (by decide +kernel)

theorem chunkOk_19 : ChunkOk ((Chunks.new 19).getD default) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem link_terminal_L19_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (ltNames.getD 0 "") args rets → MeaningLinkTerminal 19 rd args rets :=
  lt_sound 19 7607 chunkOk_19 (allAtoms_of_isAtomsB (by decide +kernel)) (f := fn% «link_terminal__L19»)
    (coreProgram_find?_at (j := idx% «link_terminal__L19») rfl) rfl link_terminal_L19_body rd args rets

theorem chunkOk_20 : ChunkOk ((Chunks.new 20).getD default) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem link_terminal_L20_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (ltNames.getD 1 "") args rets → MeaningLinkTerminal 20 rd args rets :=
  lt_sound 20 7607 chunkOk_20 (allAtoms_of_isAtomsB (by decide +kernel)) (f := fn% «link_terminal__L20»)
    (coreProgram_find?_at (j := idx% «link_terminal__L20») rfl) rfl link_terminal_L20_body rd args rets

theorem chunkOk_21 : ChunkOk ((Chunks.new 21).getD default) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem link_terminal_L21_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (ltNames.getD 2 "") args rets → MeaningLinkTerminal 21 rd args rets :=
  lt_sound 21 32671816220672 chunkOk_21 (allAtoms_of_isAtomsB (by decide +kernel)) (f := fn% «link_terminal__L21»)
    (coreProgram_find?_at (j := idx% «link_terminal__L21») rfl) rfl link_terminal_L21_body rd args rets

theorem chunkOk_22 : ChunkOk ((Chunks.new 22).getD default) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem link_terminal_L22_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (ltNames.getD 3 "") args rets → MeaningLinkTerminal 22 rd args rets :=
  lt_sound 22 32671816220672 chunkOk_22 (allAtoms_of_isAtomsB (by decide +kernel)) (f := fn% «link_terminal__L22»)
    (coreProgram_find?_at (j := idx% «link_terminal__L22») rfl) rfl link_terminal_L22_body rd args rets

theorem chunkOk_23 : ChunkOk ((Chunks.new 23).getD default) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem link_terminal_L23_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (ltNames.getD 4 "") args rets → MeaningLinkTerminal 23 rd args rets :=
  lt_sound 23 69649 chunkOk_23 (allAtoms_of_isAtomsB (by decide +kernel)) (f := fn% «link_terminal__L23»)
    (coreProgram_find?_at (j := idx% «link_terminal__L23») rfl) rfl link_terminal_L23_body rd args rets

theorem chunkOk_24 : ChunkOk ((Chunks.new 24).getD default) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem link_terminal_L24_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (ltNames.getD 5 "") args rets → MeaningLinkTerminal 24 rd args rets :=
  lt_sound 24 299140177199104 chunkOk_24 (allAtoms_of_isAtomsB (by decide +kernel)) (f := fn% «link_terminal__L24»)
    (coreProgram_find?_at (j := idx% «link_terminal__L24») rfl) rfl link_terminal_L24_body rd args rets

/-- **`link_terminal`'s core IR implies its meaning**, every specialization. -/
theorem link_terminal_sound : link_terminal_SoundP coreProgram := by
  intro w h1 h2
  interval_cases w
  exacts [link_terminal_L19_sound, link_terminal_L20_sound, link_terminal_L21_sound, link_terminal_L22_sound, link_terminal_L23_sound, link_terminal_L24_sound]

end
end LeanVM.Guest.B1.Link
