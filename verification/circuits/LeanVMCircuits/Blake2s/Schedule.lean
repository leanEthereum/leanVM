module

public import LeanVMCircuits.Blake2s.Program
public import LeanVMCircuits.Blake2s.Spec

@[expose] public section

/-!
The BLAKE2s compression as a register program, and the proof that it computes RFC 7693's F.

The registers start as the chaining value's eight words (0 to 7), the message's sixteen (8 to 23), and the working
vector's last eight words (24 to 31): `IV[0..4]`, then `IV[4..8]` with the counter's halves and the finalization word
XORed in. Each half of a G appends five registers, and a lane map says which register holds each word of the
working vector. In round 0 the third lane of a column G is still `IV[c - 8]`, a literal, so that addition is `k + y`.
-/

namespace LeanVMCircuits.Blake2s

open Rfc7693

/-- A program under construction: its operations, the register of each lane, and the next register. -/
structure Gen where
  ops : List Op
  lanes : Vector ℕ 16
  next : ℕ

/-- The literal adder of `k`'s parity. -/
def addLit (k : Word) (y : ℕ) : Op := if k.getLsbD 0 then .addOdd k y else .addEven k y

/-- Half of G's operations: `a += b + x`, `d = (d ^ a) >>> r1`, `c += d`, `b = (b ^ c) >>> r2`. -/
def Gen.halfOps (g : Gen) (a b c d : Fin 16) (x : ℕ) (r1 r2 : Fin 32) (literal : Option Word) : List Op :=
  let n := g.next
  let third := match literal with
    | some k => addLit k (n + 2)
    | none => .add g.lanes[c] (n + 2)
  [.add g.lanes[a] g.lanes[b], .add n x, .xorRotr r1 g.lanes[d] (n + 1), third, .xorRotr r2 g.lanes[b] (n + 3)]

/-- Half of G, the third lane `c` a literal or a register. -/
def Gen.half (g : Gen) (a b c d : Fin 16) (x : ℕ) (r1 r2 : Fin 32) (literal : Option Word) : Gen :=
  { ops := g.ops ++ g.halfOps a b c d x r1 r2 literal
    lanes := ((((g.lanes.set a (g.next + 1)).set d (g.next + 2)).set c (g.next + 3)).set b (g.next + 4))
    next := g.next + 5 }

/-- G, its message words the registers `8 + x` and `8 + y`. -/
def Gen.g (gen : Gen) (a b c d : Fin 16) (x y : Fin 16) (literal : Option Word) : Gen :=
  (gen.half a b c d (8 + x.val) 16 12 literal).half a b c d (8 + y.val) 8 7 none

/-- One round. In the first, the column G's third lanes are the IV's literals. -/
def Gen.round (gen : Gen) (s : Vector (Fin 16) 16) (first : Bool) : Gen :=
  let lit (i : Fin 8) : Option Word := if first then some IV[i] else none
  let gen := gen.g 0 4 8 12 s[0] s[1] (lit 0)
  let gen := gen.g 1 5 9 13 s[2] s[3] (lit 1)
  let gen := gen.g 2 6 10 14 s[4] s[5] (lit 2)
  let gen := gen.g 3 7 11 15 s[6] s[7] (lit 3)
  let gen := gen.g 0 5 10 15 s[8] s[9] none
  let gen := gen.g 1 6 11 12 s[10] s[11] none
  let gen := gen.g 2 7 8 13 s[12] s[13] none
  gen.g 3 4 9 14 s[14] s[15] none

def initial : Gen :=
  { ops := [], lanes := #v[0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31], next := 32 }

/-- Ten rounds, the message schedule `SIGMA`. -/
def program : Gen :=
  (List.finRange 10).foldl (fun gen i => gen.round SIGMA[i] (i.val == 0)) initial

/-! The program computes F. -/

/-- Half of RFC 7693's G. -/
def halfG (v : Vector Word 16) (a b c d : Fin 16) (x : Word) (r1 r2 : ℕ) : Vector Word 16 :=
  let v := v.set a (v[a] + v[b] + x)
  let v := v.set d ((v[d] ^^^ v[a]).rotateRight r1)
  let v := v.set c (v[c] + v[d])
  v.set b ((v[b] ^^^ v[c]).rotateRight r2)

theorem G_halves (v : Vector Word 16) (a b c d : Fin 16) (x y : Word) :
    G v a b c d x y = halfG (halfG v a b c d x 16 12) a b c d y 8 7 := rfl

/-- The registers `values` hold the working vector `v` through the lanes, and the message at `8..24`. -/
def Holds (values : List Word) (gen : Gen) (v m : Vector Word 16) : Prop :=
  values.length = gen.next ∧ 24 ≤ gen.next ∧ (∀ i : Fin 16, gen.lanes[i] < gen.next) ∧
    (∀ i : Fin 16, values.getD gen.lanes[i] 0 = v[i]) ∧ ∀ j : Fin 16, values.getD (8 + j.val) 0 = m[j]

theorem getD_append_left (values more : List Word) (i : ℕ) (h : i < values.length) :
    (values ++ more).getD i 0 = values.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right (values more : List Word) (j : ℕ) :
    (values ++ more).getD (values.length + j) 0 = more.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem addLit_eval (values : List Word) (k : Word) (y : ℕ) :
    (addLit k y).eval values = k + values.getD y 0 := by
  unfold addLit; split <;> rfl

theorem addLit_valid (k : Word) (y : ℕ) : (addLit k y).valid = true := by
  unfold addLit; split <;> simp_all [Op.valid]

theorem evalOps_cons (op : Op) (ops : List Op) (values : List Word) :
    evalOps (op :: ops) values = evalOps ops (values ++ [op.eval values]) := rfl

theorem half_holds (values : List Word) (gen : Gen) (v m : Vector Word 16) (a b c d : Fin 16) (x : ℕ)
    (r1 r2 : Fin 32) (literal : Option Word) (h : Holds values gen v m) (hx : x < gen.next)
    (hlit : ∀ k, literal = some k → v[c] = k)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Holds (evalOps (gen.halfOps a b c d x r1 r2 literal) values) (gen.half a b c d x r1 r2 literal)
      (halfG v a b c d (values.getD x 0) r1.val r2.val) m := by
  obtain ⟨hlen, h24, hlanes, hv, hm⟩ := h
  have hn : ∀ (more : List Word) (j : ℕ), (values ++ more).getD (gen.next + j) 0 = more.getD j 0 := by
    intro more j; rw [← hlen]; exact getD_append_right _ _ _
  have hn0 : ∀ (more : List Word), (values ++ more).getD gen.next 0 = more.getD 0 0 := fun more => hn more 0
  have hl : ∀ (more : List Word) (i : Fin 16), (values ++ more).getD gen.lanes[i] 0 = v[i] := by
    intro more i; rw [getD_append_left _ _ _ (by rw [hlen]; exact hlanes i), hv]
  have hxv : ∀ (more : List Word), (values ++ more).getD x 0 = values.getD x 0 := by
    intro more; rw [getD_append_left _ _ _ (by omega)]
  set X := values.getD x 0
  set w0 := v[a] + v[b]
  set w1 := w0 + X
  set w2 := (v[d] ^^^ w1).rotateRight r1.val
  set w3 := v[c] + w2
  set w4 := (v[b] ^^^ w3).rotateRight r2.val
  have e3 : ∀ (more : List Word), (match literal with
      | some k => addLit k (gen.next + 2)
      | none => Op.add gen.lanes[c] (gen.next + 2)).eval (values ++ [w0, w1] ++ more) =
        v[c] + (values ++ [w0, w1] ++ more).getD (gen.next + 2) 0 := by
    intro more
    cases literal with
    | none => rw [Op.eval, List.append_assoc, hl]
    | some k => rw [addLit_eval, hlit k rfl]
  have key : evalOps (gen.halfOps a b c d x r1 r2 literal) values = values ++ [w0, w1, w2, w3, w4] := by
    simp only [Gen.halfOps]
    rw [evalOps_cons, show Op.eval values (.add gen.lanes[a] gen.lanes[b]) = w0 by
      rw [Op.eval, ← List.append_nil values, hl, hl]]
    rw [evalOps_cons, show Op.eval (values ++ [w0]) (.add gen.next x) = w1 by rw [Op.eval, hn0, hxv]; rfl]
    rw [List.append_assoc, List.singleton_append]
    rw [evalOps_cons, show Op.eval (values ++ [w0, w1]) (.xorRotr r1 gen.lanes[d] (gen.next + 1)) = w2 by
      rw [Op.eval, hl, hn]; rfl]
    rw [List.append_assoc, List.cons_append, List.singleton_append]
    rw [evalOps_cons, show Op.eval (values ++ [w0, w1, w2]) (match literal with
      | some k => addLit k (gen.next + 2)
      | none => Op.add gen.lanes[c] (gen.next + 2)) = w3 by
        have := e3 [w2]
        simp only [List.append_assoc, List.cons_append, List.nil_append] at this
        rw [this, hn]; rfl]
    rw [List.append_assoc, List.cons_append, List.cons_append, List.singleton_append]
    rw [evalOps_cons, show Op.eval (values ++ [w0, w1, w2, w3]) (.xorRotr r2 gen.lanes[b] (gen.next + 3)) = w4 by
      rw [Op.eval, hl, hn]; rfl]
    simp only [evalOps, List.foldl_nil, List.append_assoc, List.cons_append, List.nil_append]
  rw [key]
  refine ⟨by simp [Gen.half, hlen], by simp only [Gen.half]; omega, ?_, ?_, ?_⟩
  · intro i
    simp only [Gen.half, Fin.getElem_fin, Vector.getElem_set]
    have := hlanes i
    simp only [Fin.getElem_fin] at this
    split_ifs <;> omega
  · intro i
    have hab' : (a : ℕ) ≠ b := Fin.val_ne_of_ne hab
    have hac' : (a : ℕ) ≠ c := Fin.val_ne_of_ne hac
    have had' : (a : ℕ) ≠ d := Fin.val_ne_of_ne had
    have hbc' : (b : ℕ) ≠ c := Fin.val_ne_of_ne hbc
    have hbd' : (b : ℕ) ≠ d := Fin.val_ne_of_ne hbd
    have hcd' : (c : ℕ) ≠ d := Fin.val_ne_of_ne hcd
    have hba' := hab'.symm
    have hca' := hac'.symm
    have hda' := had'.symm
    have hcb' := hbc'.symm
    have hdb' := hbd'.symm
    have hdc' := hcd'.symm
    have hn' : ∀ j, (values ++ [w0, w1, w2, w3, w4]).getD (gen.next + j) 0 = [w0, w1, w2, w3, w4].getD j 0 :=
      hn _
    have hvi := hl [w0, w1, w2, w3, w4] i
    simp only [Fin.getElem_fin] at hvi hn' ⊢
    simp only [Gen.half, halfG, Vector.getElem_set]
    split_ifs <;> simp_all [w0, w1, w2, w3, w4]
  · intro j
    rw [getD_append_left _ _ _ (by omega), hm]

theorem half_correct (initial : List Word) (gen : Gen) (v m : Vector Word 16) (a b c d x : Fin 16)
    (r1 r2 : Fin 32) (literal : Option Word) (h : Holds (evalOps gen.ops initial) gen v m)
    (hlit : ∀ k, literal = some k → v[c] = k)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Holds (evalOps (gen.half a b c d (8 + x.val) r1 r2 literal).ops initial) (gen.half a b c d (8 + x.val) r1 r2 literal)
      (halfG v a b c d m[x] r1.val r2.val) m := by
  have hx : (evalOps gen.ops initial).getD (8 + x.val) 0 = m[x] := h.2.2.2.2 x
  have := half_holds _ gen v m a b c d (8 + x.val) r1 r2 literal h (by have := h.2.1; omega) hlit
    hab hac had hbc hbd hcd
  rw [hx] at this
  simpa only [Gen.half, evalOps_append] using this

theorem G_other (v : Vector Word 16) (a b c d i : Fin 16) (x y : Word)
    (ha : i ≠ a) (hb : i ≠ b) (hc : i ≠ c) (hd : i ≠ d) : (G v a b c d x y)[i] = v[i] := by
  have ha' : (a : ℕ) ≠ i := (Fin.val_ne_of_ne ha).symm
  have hb' : (b : ℕ) ≠ i := (Fin.val_ne_of_ne hb).symm
  have hc' : (c : ℕ) ≠ i := (Fin.val_ne_of_ne hc).symm
  have hd' : (d : ℕ) ≠ i := (Fin.val_ne_of_ne hd).symm
  simp only [G, Fin.getElem_fin, Vector.getElem_set, ha', hb', hc', hd', if_false]

theorem g_correct (initial : List Word) (gen : Gen) (v m : Vector Word 16) (a b c d x y : Fin 16)
    (literal : Option Word) (h : Holds (evalOps gen.ops initial) gen v m)
    (hlit : ∀ k, literal = some k → v[c] = k)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Holds (evalOps (gen.g a b c d x y literal).ops initial) (gen.g a b c d x y literal) (G v a b c d m[x] m[y]) m := by
  rw [G_halves]
  exact half_correct _ _ _ m a b c d y 8 7 none
    (half_correct _ _ v m a b c d x 16 12 literal h hlit hab hac had hbc hbd hcd) (by simp) hab hac had hbc hbd hcd

theorem round_correct (initial : List Word) (gen : Gen) (v m : Vector Word 16) (s : Vector (Fin 16) 16)
    (first : Bool) (h : Holds (evalOps gen.ops initial) gen v m)
    (hiv : first = true → v[8] = IV[0] ∧ v[9] = IV[1] ∧ v[10] = IV[2] ∧ v[11] = IV[3]) :
    Holds (evalOps (gen.round s first).ops initial) (gen.round s first) (Rfc7693.round v m s) m := by
  simp only [Gen.round, Rfc7693.round]
  have lit : ∀ (i : Fin 8) (w : Word), (∀ k, first = true → k = IV[i] → w = k) →
      ∀ k, (if first then some IV[i] else none) = some k → w = k := by
    intro i w hw k hk
    cases first <;> simp_all
  refine g_correct _ _ _ m 3 4 9 14 _ _ none ?_ (by simp) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  refine g_correct _ _ _ m 2 7 8 13 _ _ none ?_ (by simp) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  refine g_correct _ _ _ m 1 6 11 12 _ _ none ?_ (by simp) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  refine g_correct _ _ _ m 0 5 10 15 _ _ none ?_ (by simp) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  refine g_correct _ _ _ m 3 7 11 15 _ _ _ ?_ ?_ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  rotate_left
  · apply lit 3
    intro k hf hk
    rw [hk, G_other _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide),
      G_other _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide),
      G_other _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
    exact (hiv hf).2.2.2
  refine g_correct _ _ _ m 2 6 10 14 _ _ _ ?_ ?_ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  rotate_left
  · apply lit 2
    intro k hf hk
    rw [hk, G_other _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide),
      G_other _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
    exact (hiv hf).2.2.1
  refine g_correct _ _ _ m 1 5 9 13 _ _ _ ?_ ?_ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  rotate_left
  · apply lit 1
    intro k hf hk
    rw [hk, G_other _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
    exact (hiv hf).2.1
  refine g_correct _ _ _ m 0 4 8 12 _ _ _ h ?_ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  apply lit 0
  intro k hf hk
  rw [hk]
  exact (hiv hf).1

/-- The working vector after F's ten rounds. -/
def rounds (v m : Vector Word 16) : Vector Word 16 := (List.finRange 10).foldl (fun v i => Rfc7693.round v m SIGMA[i]) v

theorem program_correct (initial : List Word) (v m : Vector Word 16) (h : Holds initial Blake2s.initial v m)
    (hiv : v[8] = IV[0] ∧ v[9] = IV[1] ∧ v[10] = IV[2] ∧ v[11] = IV[3]) :
    Holds (evalOps program.ops initial) program (rounds v m) m := by
  have hrange : List.finRange 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by decide
  simp only [program, rounds, hrange, List.foldl_cons, List.foldl_nil]
  have skip : ∀ (i : Fin 10) (w : Vector Word 16), i.val ≠ 0 → (i.val == 0) = true →
      w[8] = IV[0] ∧ w[9] = IV[1] ∧ w[10] = IV[2] ∧ w[11] = IV[3] := by
    intro i w hi h; simp_all
  iterate 9 refine round_correct _ _ _ m _ _ ?_ (skip _ _ (by decide))
  exact round_correct _ _ _ m _ _ (by simpa [Blake2s.initial, evalOps] using h) (fun _ => hiv)

def Gen.Valid (gen : Gen) : Prop := ∀ op ∈ gen.ops, op.valid = true

theorem half_valid (gen : Gen) (a b c d : Fin 16) (x : ℕ) (r1 r2 : Fin 32) (literal : Option Word)
    (h : gen.Valid) : (gen.half a b c d x r1 r2 literal).Valid := by
  intro op hop
  simp only [Gen.half, Gen.halfOps, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with hop | rfl | rfl | rfl | rfl | rfl
  · exact h op hop
  all_goals try rfl
  cases literal
  · rfl
  · exact addLit_valid _ _

theorem round_valid (gen : Gen) (s : Vector (Fin 16) 16) (first : Bool) (h : gen.Valid) :
    (gen.round s first).Valid := by
  simp only [Gen.round, Gen.g]
  iterate 16 apply half_valid
  exact h

theorem program_valid : program.Valid := by
  have hrange : List.finRange 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by decide
  simp only [program, hrange, List.foldl_cons, List.foldl_nil]
  iterate 10 apply round_valid
  intro op hop
  simp [Blake2s.initial] at hop

end LeanVMCircuits.Blake2s
