module

public import LeanVMCircuits.Rec.Justify
public import LeanVMCircuits.Rec.Relax
public import LeanVMCircuits.Rec.Union
public import LeanVMCircuits.Rec.PoolParse
public import LeanVMCircuits.Rec.UnionSound

@[expose] public section

/-!
A union's rows, read off the builder's calls (`rec::tree::union`).

A union certificate names where a dump's calls make each pool (`pool_rows`) and each product (`product`): the
calls' indices, call for call as the Rust code makes them, and the `pack` calls that hold the hinted bits. `PoolCert.ok`
and `ProdCert.ok` check every named call is in the replay with the wires the code gives it. In an assignment where
every replayed call holds (`Facts`, from `Model.replayR_sound`), the calls give:

- a pool's values satisfy `PoolParse.Sem` (`pool_sem`);
- a product is `prodSpec` of its pool's items' values and the point (`prod_sem`).

`PointCert`: where a dump's calls draw a union's point from its challenges, `X + 1` and the sixteen weights `eq(A, k)`
of `A`'s four challenges (`union::challenge`, `union::eq_weights`); `point_sem`: the weights are `UnionSound.eqAt A k`.

`unionsValid`: two such assignments that agree on a union's digests, begin and selection bits and point, whose
compressions do not collide (`HashCR`), give its products one value. With `PoolParse.parse_unique` the pools' items
agree but for padding, whose factors are one.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model PoolParse

/-! Calls a check names. -/

/-- A squeeze: a `leaf_block` at the duplex's output role. Its output is a challenge, the random oracle's answer. -/
def _root_.LeanVMCircuits.Rec.Model.Call.isSqueeze : Call → Bool
  | .leafBlock _ _ t _ => t / 2 ^ 56 == 6
  | _ => false

/-- Each listed call is in the replay at its index, is not a relaxed equality and is not a squeeze. -/
def callsOk (cs : Array Call) (rl : Array Bool) (l : List (ℕ × Call)) : Bool :=
  l.all fun jc => cs[jc.1]? == some jc.2 && !(rl.getD jc.1 false && jc.2.isEq) && !jc.2.isSqueeze

theorem callsOk_append {cs : Array Call} {rl : Array Bool} {a b : List (ℕ × Call)} :
    callsOk cs rl (a ++ b) = (callsOk cs rl a && callsOk cs rl b) := by
  simp [callsOk, List.all_append]

/-- Output `k` of call `j`. -/
def outAt (os : Array (List ℕ)) (j k : ℕ) : ℕ := (os.getD j []).getD k 0

/-- Every replayed call holds, unless it is a relaxed equality or a squeeze: in the random-oracle view a squeeze's
output is the oracle's answer, not the compression of its inputs. -/
def Facts (cs : Array Call) (rl : Array Bool) (os : Array (List ℕ)) (st : ℕ → Fin 4 → K) (val : Val) : Prop :=
  ∀ j (hj : j < cs.size), (rl.getD j false && cs[j].isEq) = false → cs[j].isSqueeze = false →
    cs[j].Holds st val (os.getD j [])

/-- Every replayed `block` call's `HASH` row is in `s`. -/
def RowsIn (cs : Array Call) (os : Array (List ℕ)) (s : State) : Prop :=
  ∀ j (hj : j < cs.size), cs[j].Rows s (os.getD j [])

theorem holds_of_mem {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}
    {l : List (ℕ × Call)} {j : ℕ} {c : Call} (hF : Facts cs rl os st val) (h : callsOk cs rl l = true)
    (hm : (j, c) ∈ l) : c.Holds st val (os.getD j []) := by
  simp only [callsOk, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨hc, hr⟩, hsq⟩ := h _ hm
  dsimp only at hc hr hsq
  obtain ⟨hj, hcj⟩ := Array.getElem?_eq_some_iff.mp hc
  subst hcj
  exact hF j hj hr hsq

theorem holds_all {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}
    {l : List (ℕ × Call)} (hF : Facts cs rl os st val) (h : callsOk cs rl l = true) :
    ∀ x ∈ l, x.2.Holds st val (os.getD x.1 []) := fun _ hx => holds_of_mem hF h hx

/-- Every replayed call but call `j0` holds, unless it is a relaxed equality or a squeeze: in the ideal compression
model a proof-of-work trial's compression is the oracle's answer, not the compression of its inputs. -/
def FactsBut (cs : Array Call) (rl : Array Bool) (os : Array (List ℕ)) (j0 : ℕ) (st : ℕ → Fin 4 → K) (val : Val) :
    Prop :=
  ∀ j (hj : j < cs.size), j ≠ j0 → (rl.getD j false && cs[j].isEq) = false → cs[j].isSqueeze = false →
    cs[j].Holds st val (os.getD j [])

theorem Facts.but {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}
    (hF : Facts cs rl os st val) (j0 : ℕ) : FactsBut cs rl os j0 st val :=
  fun j hj _ => hF j hj

theorem holds_of_mem_but {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}
    {j0 : ℕ} {l : List (ℕ × Call)} {j : ℕ} {c : Call} (hF : FactsBut cs rl os j0 st val)
    (h : callsOk cs rl l = true) (hm : (j, c) ∈ l) (hj0 : j ≠ j0) : c.Holds st val (os.getD j []) := by
  simp only [callsOk, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨hc, hr⟩, hsq⟩ := h _ hm
  dsimp only at hc hr hsq
  obtain ⟨hj, hcj⟩ := Array.getElem?_eq_some_iff.mp hc
  subst hcj
  exact hF j hj hj0 hr hsq

theorem rows_of_mem {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {s : State}
    {l : List (ℕ × Call)} {j : ℕ} {c : Call} (hR : RowsIn cs os s) (h : callsOk cs rl l = true)
    (hm : (j, c) ∈ l) : c.Rows s (os.getD j []) := by
  simp only [callsOk, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hc, -⟩, -⟩ := h _ hm
  dsimp only at hc
  obtain ⟨hj, hcj⟩ := Array.getElem?_eq_some_iff.mp hc
  subst hcj
  exact hR j hj

/-! Values. -/

theorem emb_inj {a b : K} (h : emb a = emb b) : a = b := by
  rw [← toE_emb, ← toE_emb] at h
  exact (toE_injective _ _ _ _ _ _ h).1

theorem emb_one' : emb 1 = 1 := map_one _

theorem add_self_E (a : E) : a + a = 0 := by linear_combination a * two_E

theorem eq_of_add_eq_zero_E {a b : E} (h : a + b = 0) : a = b := by linear_combination h - b * two_E

theorem ev_of_val {val : Val} {a b : ℕ} (h : val a = val b) : Model.ev val a = Model.ev val b := by simp [Model.ev, h]

theorem ev_of_val' {val val' : Val} {a : ℕ} (h : val a = val' a) : Model.ev val a = Model.ev val' a := by
  simp [Model.ev, h]

theorem ev_eConst {val : Val} {w c0 c1 c2 : ℕ} (h : Model.ev val w = toE (ofWord c0) (ofWord c1) (ofWord c2)) :
    Model.ev val w = toE (ofWord c0) (ofWord c1) (ofWord c2) := h

theorem ev_toE (val : Val) (w : ℕ) : Model.ev val w = toE (val w 0) (val w 1) (val w 2) := rfl

/-- A wire's limb `k`, zero past the fourth. -/
noncomputable def vk (val : Val) (w k : ℕ) : K := if h : k < 4 then val w ⟨k, h⟩ else 0

/-! A pool item's calls. -/

section Item

variable (os : Array (List ℕ))

/-- Output 0 of call `j`. -/
abbrev o (j : ℕ) : ℕ := outAt os j 0

theorem getD_o (j : ℕ) : (os.getD j []).getD 0 0 = o os j := rfl

/-- An item's kind bits and the forms the products read: thirteen calls from `p`. -/
def kindCalls (one zero p : ℕ) : List (ℕ × Call) :=
  [(p, .freeK), (p + 1, .freeK), (p + 2, .freeK),
   (p + 3, .mulKAdd one (o os p) zero), (p + 4, .mulKAdd one (o os (p + 1)) zero),
   (p + 5, .mulKAdd (o os (p + 3)) (o os (p + 1)) zero),
   (p + 6, .add (o os (p + 3)) (o os (p + 5))), (p + 7, .add (o os (p + 4)) (o os (p + 5))),
   (p + 8, .add (o os (p + 3)) (o os (p + 4))), (p + 9, .add (o os (p + 8)) (o os (p + 5))),
   (p + 10, .mulKAdd one (o os (p + 2)) zero), (p + 11, .mulKAdd (o os (p + 6)) (o os (p + 2)) zero),
   (p + 12, .eqE (o os (p + 10)) (o os (p + 11)))]

/-- The calls of an item's start, from `p + 13`, `ended` the previous item's end-or-padding form. -/
def startCalls (one zero p : ℕ) : Start → Option ℕ → List (ℕ × Call)
  | .yes, _ => [(p + 13, .eqE (o os (p + 5)) zero)]
  | .ifBit bit, some ended =>
    [(p + 13, .mulKAdd one bit zero), (p + 14, .mul ended (o os (p + 13))), (p + 15, .eqE (o os (p + 14)) (o os (p + 13))),
     (p + 16, .add ended (o os (p + 13))), (p + 17, .eqE (o os (p + 5)) (o os (p + 16)))]
  | .no, some ended => [(p + 13, .eqE (o os (p + 5)) ended)]
  | _, none => []

/-- How many calls a start makes. -/
def sLen : Start → ℕ
  | .ifBit _ => 5
  | _ => 1

/-- The start's form in the counter word. -/
def startWire (one zero p : ℕ) : Start → ℕ
  | .yes => one
  | .ifBit _ => o os (p + 13)
  | .no => zero

/-- The counter word's calls from `c`. -/
def counterCalls (cM cE cP cF kZero c b0 b1 pair isEnd startE : ℕ) : List (ℕ × Call) :=
  [(c, .mulKAdd cM b0 startE), (c + 1, .mulKAdd cE b1 (o os c)), (c + 2, .mulKAdd cP pair (o os (c + 1))),
   (c + 3, .mulAdd cF isEnd (o os (c + 2))), (c + 4, .eToK (o os (c + 3))),
   (c + 5, .kToD (o os (c + 4)) (outAt os (c + 4) 1) kZero kZero)]

/-- The chaining value's calls from `c`: the parameter IV at the pool's start, at a chunk's start the previous
output's halves or the IV's by the begin bit. -/
def hCalls (ivLo ivHi c : ℕ) : Start → Option (ℕ × ℕ) → List (ℕ × Call)
  | .yes, _ => [(c, .dConst paramIVLimbs)]
  | .ifBit bit, some (lo, hi) =>
    [(c, .add lo ivLo), (c + 1, .add hi ivHi), (c + 2, .mulKAdd (o os c) bit lo),
     (c + 3, .mulKAdd (o os (c + 1)) bit hi), (c + 4, .halvesToD (o os (c + 2)) (o os (c + 3)))]
  | _, _ => []

def hLen : Start → ℕ
  | .yes => 1
  | .ifBit _ => 5
  | .no => 0

/-- The chaining value's wire. -/
def hWire (c prevOut : ℕ) : Start → ℕ
  | .yes => o os c
  | .ifBit _ => o os (c + 4)
  | .no => prevOut

/-- The block's eight words from `b`. -/
def blockWords (b : ℕ) : List ℕ := (List.range 8).map fun j => o os (b + j)

/-- The block, its compression and the end check, from `b`. -/
def blockCalls (zero b h tf isEnd eLo eHi : ℕ) : List (ℕ × Call) :=
  (List.range 8).map (fun j => (b + j, .freeK)) ++
  [(b + 8, .hashBlock h (blockWords os b) tf), (b + 9, .dToHalves (o os (b + 8))),
   (b + 10, .add (o os (b + 9)) eLo), (b + 11, .mul isEnd (o os (b + 10))), (b + 12, .eqE (o os (b + 11)) zero),
   (b + 13, .add (outAt os (b + 9) 1) eHi), (b + 14, .mul isEnd (o os (b + 13))), (b + 15, .eqE (o os (b + 14)) zero)]

end Item

/-! Semantics of an item's calls. -/

section ItemSem

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}

/-- The kind calls: the forms the products and the counter word read, and the second member bit's check. -/
theorem kind_sem (hF : Facts cs rl os st val) {one zero p : ℕ} (hz : Model.ev val zero = 0) (ho : Model.ev val one = 1)
    (hok : callsOk cs rl (kindCalls os one zero p) = true) :
    let B0 := val (o os p) 0
    let B1 := val (o os (p + 1)) 0
    let P := val (o os (p + 2)) 0
    Model.ev val (o os (p + 4)) = emb B1 ∧ Model.ev val (o os (p + 5)) = emb (B0 * B1) ∧
      Model.ev val (o os (p + 6)) = emb (B0 + B0 * B1) ∧ Model.ev val (o os (p + 7)) = emb (B1 + B0 * B1) ∧
      Model.ev val (o os (p + 9)) = emb (B0 + B1 + B0 * B1) ∧ Model.ev val (o os (p + 11)) = emb ((B0 + B0 * B1) * P) ∧
      P = (B0 + B0 * B1) * P := by
  intro B0 B1 P
  have H := holds_all hF hok
  simp only [kindCalls, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
    Call.Holds, getD_o] at H
  obtain ⟨-, -, -, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := H
  have e0 : Model.ev val (o os (p + 3)) = emb B0 := by rw [h3, ho, hz]; ring
  have e1 : Model.ev val (o os (p + 4)) = emb B1 := by rw [h4, ho, hz]; ring
  have pd : Model.ev val (o os (p + 5)) = emb (B0 * B1) := by rw [h5, e0, hz, emb_mul]; ring
  have mem : Model.ev val (o os (p + 6)) = emb (B0 + B0 * B1) := by rw [h6, e0, pd, emb_add]
  have pr : Model.ev val (o os (p + 11)) = emb ((B0 + B0 * B1) * P) := by rw [h11, mem, hz, emb_mul]; ring
  refine ⟨e1, pd, mem, by rw [h7, e1, pd, emb_add], by rw [h9, h8, e0, e1, pd, emb_add, emb_add], pr, ?_⟩
  apply emb_inj
  have hp : Model.ev val (o os (p + 10)) = emb P := by rw [h10, ho, hz]; ring
  rw [← hp, ← pr]
  exact ev_of_val h12

theorem start_yes (hF : Facts cs rl os st val) {one zero p : ℕ} {ended : Option ℕ} (hz : Model.ev val zero = 0)
    (hok : callsOk cs rl (startCalls os one zero p .yes ended) = true) : Model.ev val (o os (p + 5)) = 0 := by
  have H := holds_all hF hok
  simp only [startCalls, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
    Call.Holds, getD_o] at H
  rw [ev_of_val H, hz]

theorem start_ifBit (hF : Facts cs rl os st val) {one zero p bit ended : ℕ} (hz : Model.ev val zero = 0)
    (ho : Model.ev val one = 1) (hok : callsOk cs rl (startCalls os one zero p (.ifBit bit) (some ended)) = true) :
    Model.ev val (o os (p + 13)) = emb (val bit 0) ∧ Model.ev val ended * emb (val bit 0) = emb (val bit 0) ∧
      Model.ev val (o os (p + 5)) = Model.ev val ended + emb (val bit 0) := by
  have H := holds_all hF hok
  simp only [startCalls, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
    Call.Holds, getD_o] at H
  obtain ⟨h13, h14, h15, h16, h17⟩ := H
  have eb : Model.ev val (o os (p + 13)) = emb (val bit 0) := by rw [h13, ho, hz]; ring
  refine ⟨eb, ?_, by rw [ev_of_val h17, h16, eb]⟩
  rw [← eb, ← h14]
  exact ev_of_val h15

theorem start_no (hF : Facts cs rl os st val) {one zero p ended : ℕ}
    (hok : callsOk cs rl (startCalls os one zero p .no (some ended)) = true) :
    Model.ev val (o os (p + 5)) = Model.ev val ended := by
  have H := holds_all hF hok
  simp only [startCalls, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
    Call.Holds, getD_o] at H
  exact ev_of_val H

/-- The counter word's low limb: the start's bit and the kind bits at their codes. -/
theorem counter_sem (hF : Facts cs rl os st val) {cM cE cP cF kZero c b0 b1 pair isEnd startE : ℕ} {x e : K}
    (hM : Model.ev val cM = toE (ofWord codeMember) (ofWord 0) (ofWord 0))
    (hE : Model.ev val cE = toE (ofWord codeEnd) (ofWord 0) (ofWord 0))
    (hP : Model.ev val cP = toE (ofWord codePair) (ofWord 0) (ofWord 0))
    (hFin : Model.ev val cF = toE (ofWord 0) (ofWord final) (ofWord 0))
    (hs : Model.ev val startE = emb x) (he : Model.ev val isEnd = emb e)
    (hok : callsOk cs rl (counterCalls os cM cE cP cF kZero c b0 b1 pair isEnd startE) = true) :
    val (o os (c + 5)) 0 = x + ofWord 2 * val b0 0 + ofWord 4 * val b1 0 + ofWord 8 * val pair 0 := by
  have H := holds_all hF hok
  simp only [counterCalls, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
    Call.Holds, getD_o] at H
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := H
  have hv : Model.ev val (o os (c + 3)) = toE (x + ofWord 2 * val b0 0 + ofWord 4 * val b1 0 + ofWord 8 * val pair 0)
      (ofWord final * e) 0 := by
    rw [h3, h2, h1, h0, hM, hE, hP, hFin, hs, he, ← toE_emb x]
    simp only [toE_smul, toE_add, ofWord_zero', codeMember, codeEnd, codePair]
    congr 1 <;> ring
  have h40 : val (o os (c + 4)) 0 = val (o os (c + 3)) 0 := h4 0 (by decide)
  rw [h5.1, h40]
  exact (toE_injective _ _ _ _ _ _ ((ev_toE val _).symm.trans hv)).1

/-- At a chunk's start whose begin bit is zero, the chaining value is the previous output's halves. -/
theorem h_ifBit_zero (hF : Facts cs rl os st val) {ivLo ivHi c bit lo hi : ℕ}
    (hok : callsOk cs rl (hCalls os ivLo ivHi c (.ifBit bit) (some (lo, hi))) = true) (hb : val bit 0 = 0) :
    val (o os (c + 4)) 0 = val lo 0 ∧ val (o os (c + 4)) 1 = val lo 1 ∧ val (o os (c + 4)) 2 = val hi 0 ∧
      val (o os (c + 4)) 3 = val hi 1 := by
  have H := holds_all hF hok
  simp only [hCalls, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
    Call.Holds, getD_o] at H
  obtain ⟨-, -, h2, h3, h4⟩ := H
  rw [hb, emb_zero, mul_zero, zero_add] at h2 h3
  obtain ⟨l0, l1, -⟩ := toE_injective _ _ _ _ _ _ ((ev_toE val _).symm.trans (h2.trans (ev_toE val _)))
  obtain ⟨m0, m1, -⟩ := toE_injective _ _ _ _ _ _ ((ev_toE val _).symm.trans (h3.trans (ev_toE val _)))
  exact ⟨h4.1.trans l0, h4.2.1.trans l1, h4.2.2.1.trans m0, h4.2.2.2.1.trans m1⟩

/-- The block's output halves, and at an end the digest the run must have. -/
theorem block_sem (hF : Facts cs rl os st val) {zero b h tf isEnd eLo eHi : ℕ} {e : K}
    (hz : Model.ev val zero = 0) (hok : callsOk cs rl (blockCalls os zero b h tf isEnd eLo eHi) = true)
    (he : Model.ev val isEnd = emb e) :
    (val (o os (b + 9)) 0 = val (o os (b + 8)) 0 ∧ val (o os (b + 9)) 1 = val (o os (b + 8)) 1 ∧
      val (outAt os (b + 9) 1) 0 = val (o os (b + 8)) 2 ∧ val (outAt os (b + 9) 1) 1 = val (o os (b + 8)) 3) ∧
    (e = 1 → halves (vk val (o os (b + 8))) = (Model.ev val eLo, Model.ev val eHi)) := by
  have H := holds_all hF hok
  simp only [blockCalls, List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true, Call.Holds, getD_o] at H
  obtain ⟨-, -, hh, h10, h11, h12, h13, h14, h15⟩ := H
  refine ⟨⟨hh.1, hh.2.1, hh.2.2.2.1, hh.2.2.2.2.1⟩, fun he1 => ?_⟩
  subst he1
  have hlo : Model.ev val (o os (b + 9)) = Model.ev val eLo := by
    apply eq_of_add_eq_zero_E
    rw [← h10]
    have := ev_of_val h12
    rw [h11, he, emb_one', one_mul, hz] at this
    exact this
  have hhi : Model.ev val (outAt os (b + 9) 1) = Model.ev val eHi := by
    apply eq_of_add_eq_zero_E
    rw [← h13]
    have := ev_of_val h15
    rw [h14, he, emb_one', one_mul, hz] at this
    exact this
  have q0 : val (outAt os (b + 9) 1) 0 = val (o os (b + 8)) 2 := hh.2.2.2.1
  have q1 : val (outAt os (b + 9) 1) 1 = val (o os (b + 8)) 3 := hh.2.2.2.2.1
  have q2 : val (outAt os (b + 9) 1) 2 = 0 := hh.2.2.2.2.2
  rw [← hlo, ← hhi, ev_toE, ev_toE, hh.1, hh.2.1, hh.2.2.1, q0, q1, q2]
  simp [halves, vk]

end ItemSem

/-! A pool. -/

/-- Where a dump's calls make a pool: its first call, its shape and digests, the first call of each chunk and each
item, its closing check, and the `pack` calls that hold its hinted bits. -/
structure PoolCert where
  start : ℕ
  chunks : ℕ
  selecting : Bool
  digests : List ℕ
  chunkAt : Array ℕ
  itemAt : Array ℕ
  endAt : ℕ
  packs : List ℕ
  deriving Inhabited, Repr

namespace PoolCert

variable (os : Array (List ℕ)) (pc : PoolCert)

def runs : ℕ := pc.digests.length
def n : ℕ := chunk * pc.chunks
def zero : ℕ := o os pc.start
def one : ℕ := o os (pc.start + 1)
def kZero : ℕ := o os (pc.start + 2)
def ivLo : ℕ := o os (pc.start + 3)
def ivHi : ℕ := o os (pc.start + 4)
def cM : ℕ := o os (pc.start + 5)
def cE : ℕ := o os (pc.start + 6)
def cP : ℕ := o os (pc.start + 7)
def cF : ℕ := o os (pc.start + 8)
/-- Digest `r`'s halves. -/
def halfLo (r : ℕ) : ℕ := o os (pc.start + 9 + r)
def halfHi (r : ℕ) : ℕ := outAt os (pc.start + 9 + r) 1

/-- The pool's constants and its digests' halves. -/
def headerCalls : List (ℕ × Call) :=
  [(pc.start, .zero), (pc.start + 1, .one), (pc.start + 2, .kConst 0),
   (pc.start + 3, .eConst (paramIVLimbs.getD 0 0) (paramIVLimbs.getD 1 0) 0),
   (pc.start + 4, .eConst (paramIVLimbs.getD 2 0) (paramIVLimbs.getD 3 0) 0),
   (pc.start + 5, .eConst codeMember 0 0), (pc.start + 6, .eConst codeEnd 0 0), (pc.start + 7, .eConst codePair 0 0),
   (pc.start + 8, .eConst 0 final 0)] ++
  (List.range pc.runs).map fun r => (pc.start + 9 + r, .dToHalves (pc.digests.getD r 0))

/-- Whether chunk `j` has a begin bit. -/
def begins (j : ℕ) : Bool := 0 < j && 1 < pc.runs

/-- Chunk `j`'s begin bit. -/
def beta (j : ℕ) : ℕ := o os (pc.chunkAt.getD j 0)

/-- The run one-hot's wire `r` at chunk `j`. -/
def cur (j r : ℕ) : ℕ :=
  if pc.begins j then o os (pc.chunkAt.getD j 0 + 2 + 2 * r) else if r = 0 then pc.one os else pc.zero os

/-- The first call of chunk `j`'s expected digest. -/
def expBase (j : ℕ) : ℕ := pc.chunkAt.getD j 0 + if pc.begins j then 1 + 2 * pc.runs else 0

/-- The halves of the digest chunk `j`'s run must end in. -/
def eLo (j : ℕ) : ℕ := if 1 < pc.runs then o os (pc.expBase j + pc.runs - 1) else pc.halfLo os 0
def eHi (j : ℕ) : ℕ := if 1 < pc.runs then o os (pc.expBase j + 2 * pc.runs - 1) else pc.halfHi os 0

/-- Chunk `j`'s calls: the begin bit moving the one-hot on, then the expected digest's halves. -/
def chunkCalls (j : ℕ) : List (ℕ × Call) :=
  (if pc.begins j then (pc.chunkAt.getD j 0, .freeK) :: (List.range pc.runs).flatMap fun r =>
      [(pc.chunkAt.getD j 0 + 1 + 2 * r,
        .add (if r = 0 then pc.zero os else pc.cur os (j - 1) (r - 1)) (pc.cur os (j - 1) r)),
       (pc.chunkAt.getD j 0 + 2 + 2 * r,
        .mulKAdd (o os (pc.chunkAt.getD j 0 + 1 + 2 * r)) (pc.beta os j) (pc.cur os (j - 1) r))]
    else []) ++
  (if 1 < pc.runs then
    (List.range pc.runs).map (fun r => (pc.expBase j + r, .mulAdd (pc.cur os j r) (pc.halfLo os r)
      (if r = 0 then pc.zero os else o os (pc.expBase j + r - 1)))) ++
    (List.range pc.runs).map (fun r => (pc.expBase j + pc.runs + r, .mulAdd (pc.cur os j r) (pc.halfHi os r)
      (if r = 0 then pc.zero os else o os (pc.expBase j + pc.runs + r - 1))))
  else [])

/-- How item `i` starts. -/
def startOf (i : ℕ) : Start :=
  if i = 0 then .yes else if i % chunk = 0 ∧ 1 < pc.runs then .ifBit (pc.beta os (i / chunk)) else .no

/-- Item `i`'s first call, its counter word's, and its block's. -/
def p (i : ℕ) : ℕ := pc.itemAt.getD i 0
def ctr (i : ℕ) : ℕ := pc.p i + 13 + sLen (pc.startOf os i)
def blk (i : ℕ) : ℕ := pc.ctr os i + 6 + hLen (pc.startOf os i)

/-- Item `i`'s chaining value. -/
def hOf (i : ℕ) : ℕ := hWire os (pc.ctr os i + 6) (o os (pc.blk os (i - 1) + 8)) (pc.startOf os i)

/-- Item `i`'s calls. -/
def itemCalls (i : ℕ) : List (ℕ × Call) :=
  kindCalls os (pc.one os) (pc.zero os) (pc.p i) ++
  startCalls os (pc.one os) (pc.zero os) (pc.p i) (pc.startOf os i)
    (if i = 0 then none else some (o os (pc.p (i - 1) + 4))) ++
  counterCalls os (pc.cM os) (pc.cE os) (pc.cP os) (pc.cF os) (pc.kZero os) (pc.ctr os i) (o os (pc.p i))
    (o os (pc.p i + 1)) (o os (pc.p i + 2)) (o os (pc.p i + 7)) (startWire os (pc.one os) (pc.zero os) (pc.p i)
    (pc.startOf os i)) ++
  hCalls os (pc.ivLo os) (pc.ivHi os) (pc.ctr os i + 6) (pc.startOf os i)
    (if i = 0 then none else some (o os (pc.blk os (i - 1) + 9), outAt os (pc.blk os (i - 1) + 9) 1)) ++
  blockCalls os (pc.zero os) (pc.blk os i) (pc.hOf os i) (o os (pc.ctr os i + 5)) (o os (pc.p i + 7))
    (pc.eLo os (i / chunk)) (pc.eHi os (i / chunk)) ++
  (if pc.selecting then [(pc.blk os i + 16, .freeK), (pc.blk os i + 17, .freeK)] else [])

/-- A wire is a bit of one of the pool's `pack` calls. -/
def packed (cs : Array Call) (w : ℕ) : Bool :=
  pc.packs.any fun j => match cs[j]? with
    | some (.pack bits) => (bits.take 64).contains w
    | _ => false

/-- The hinted bits are packed: kind, begin and selection bits. -/
def bitsOk (cs : Array Call) : Bool :=
  (List.range pc.n).all (fun i => pc.packed cs (o os (pc.p i)) && pc.packed cs (o os (pc.p i + 1)) &&
    pc.packed cs (o os (pc.p i + 2)) &&
    (!pc.selecting || (pc.packed cs (o os (pc.blk os i + 16)) && pc.packed cs (o os (pc.blk os i + 17))))) &&
  (List.range pc.chunks).all fun j => !pc.begins j || pc.packed cs (pc.beta os j)

/-- The pool's calls are in the replay. -/
def ok (cs : Array Call) (rl : Array Bool) : Bool :=
  0 < pc.chunks && 0 < pc.runs && callsOk cs rl pc.headerCalls &&
    (List.range pc.chunks).all (fun j => callsOk cs rl (pc.chunkCalls os j)) &&
    (List.range pc.n).all (fun i => callsOk cs rl (pc.itemCalls os i)) &&
    callsOk cs rl [(pc.endAt, .eqE (o os (pc.p (pc.n - 1) + 4)) (pc.one os))] && pc.bitsOk os cs

/-- The run one-hot's closing checks, after the pool's end check: it is at the last digest. -/
def endCalls : List (ℕ × Call) :=
  (List.range pc.runs).map fun r =>
    (pc.endAt + 1 + r, .eqConstE (pc.cur os (pc.chunks - 1) r) (if r + 1 = pc.runs then 1 else 0) 0 0)

/-- The run one-hot's closing checks are in the replay. -/
def endOk (cs : Array Call) (rl : Array Bool) : Bool := callsOk cs rl (pc.endCalls os)

/-- One assignment's values of the pool's items. -/
noncomputable def vals (val : Val) : Vals where
  b0 i := val (o os (pc.p i)) 0
  b1 i := val (o os (pc.p i + 1)) 0
  p i := val (o os (pc.p i + 2)) 0
  ins i c := if c = 0 then val (o os (pc.ctr os i + 5)) 0 else if c = 1 then val (o os (pc.ctr os i + 5)) 1
    else if c < 6 then vk val (pc.hOf os i) (c - 2) else val ((blockWords os (pc.blk os i)).getD (c - 6) 0) 0
  outs i k := vk val (o os (pc.blk os i + 8)) k

/-- The items that start a run. -/
noncomputable def sigma (val : Val) (i : ℕ) : Bool :=
  match pc.startOf os i with
  | .yes => true
  | .no => false
  | .ifBit b => decide (val b 0 = 1)

/-- The halves of the digest each item's run must end in. -/
noncomputable def X (val : Val) (i : ℕ) : E × E :=
  (Model.ev val (pc.eLo os (i / chunk)), Model.ev val (pc.eHi os (i / chunk)))

end PoolCert

/-! Rows of `block` calls. -/

theorem hashIn_block (h tf mux bit x ds o ch : ℕ) (m : List ℕ) (hm : m.length = 8) (val : Val) :
    ∀ c < 14, nu val ((hashIn ([h, tf, mux, bit, x, ds, o, ch] ++ m)).getD c 0) =
      if c = 0 then val tf 0 else if c = 1 then val tf 1 else if c < 6 then vk val h (c - 2)
      else val (m.getD (c - 6) 0) 0 := by
  match m, hm with
  | [m0, m1, m2, m3, m4, m5, m6, m7], _ =>
    intro c hc
    simp only [hashIn, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc, Option.map_some,
      Option.getD_some]
    interval_cases c <;> simp [hashSrc, colNode, nu_limb, vk]

theorem hashOut_block (h tf mux bit x ds o ch : ℕ) (m : List ℕ) (val : Val) :
    ∀ k < 4, nu val ((hashOut ([h, tf, mux, bit, x, ds, o, ch] ++ m)).getD k 0) = vk val o k := by
  intro k hk
  simp only [hashOut, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.getD_some]
  interval_cases k <;> simp [hashSrc, colNode, nu_limb, vk]

theorem length_hashIn (row : List ℕ) : (hashIn row).length = 14 := by simp [hashIn]
theorem length_hashOut (row : List ℕ) : (hashOut row).length = 4 := by simp [hashOut]

theorem map_eq_of_getD {f g : ℕ → K} {l l' : List ℕ} {N : ℕ} (hl : l.length = N) (hl' : l'.length = N)
    (h : ∀ k < N, f (l.getD k 0) = g (l'.getD k 0)) : l.map f = l'.map g := by
  apply List.ext_getElem (by simp [hl, hl'])
  intro k h1 h2
  simp only [List.length_map] at h1 h2
  rw [List.getElem_map, List.getElem_map]
  have := h k (by omega)
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
    Option.getD_some] using this

theorem getD_of_map_eq {f g : ℕ → K} {l l' : List ℕ} {N : ℕ} (hl : l.length = N) (hl' : l'.length = N)
    (h : l.map f = l'.map g) : ∀ k < N, f (l.getD k 0) = g (l'.getD k 0) := by
  intro k hk
  have := congrArg (fun x => x[k]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem (show k < l.length by omega),
    List.getElem?_eq_getElem (show k < l'.length by omega), Option.map_some, Option.some.injEq] at this
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < l.length by omega),
    List.getElem?_eq_getElem (show k < l'.length by omega)] using this

/-! What a pool's calls say of an assignment. -/

namespace PoolCert

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val} {pc : PoolCert}

theorem ok_parts (h : pc.ok os cs rl = true) :
    0 < pc.chunks ∧ 0 < pc.runs ∧ callsOk cs rl pc.headerCalls = true ∧
      (∀ j < pc.chunks, callsOk cs rl (pc.chunkCalls os j) = true) ∧
      (∀ i < pc.n, callsOk cs rl (pc.itemCalls os i) = true) ∧
      callsOk cs rl [(pc.endAt, .eqE (o os (pc.p (pc.n - 1) + 4)) (pc.one os))] = true ∧ pc.bitsOk os cs = true := by
  simp only [ok, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h6⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h0, h6, h1, h2, h3, h4, h5⟩

theorem item_parts {i : ℕ} (h : callsOk cs rl (pc.itemCalls os i) = true) :
    callsOk cs rl (kindCalls os (pc.one os) (pc.zero os) (pc.p i)) = true ∧
    callsOk cs rl (startCalls os (pc.one os) (pc.zero os) (pc.p i) (pc.startOf os i)
      (if i = 0 then none else some (o os (pc.p (i - 1) + 4)))) = true ∧
    callsOk cs rl (counterCalls os (pc.cM os) (pc.cE os) (pc.cP os) (pc.cF os) (pc.kZero os) (pc.ctr os i)
      (o os (pc.p i)) (o os (pc.p i + 1)) (o os (pc.p i + 2)) (o os (pc.p i + 7))
      (startWire os (pc.one os) (pc.zero os) (pc.p i) (pc.startOf os i))) = true ∧
    callsOk cs rl (hCalls os (pc.ivLo os) (pc.ivHi os) (pc.ctr os i + 6) (pc.startOf os i)
      (if i = 0 then none else some (o os (pc.blk os (i - 1) + 9), outAt os (pc.blk os (i - 1) + 9) 1))) = true ∧
    callsOk cs rl (blockCalls os (pc.zero os) (pc.blk os i) (pc.hOf os i) (o os (pc.ctr os i + 5))
      (o os (pc.p i + 7)) (pc.eLo os (i / chunk)) (pc.eHi os (i / chunk))) = true := by
  simp only [itemCalls, callsOk_append, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, -⟩ := h
  exact ⟨h0, h1, h2, h3, h4⟩

/-- The pool's constants. -/
theorem header_sem (hF : Facts cs rl os st val) (h : callsOk cs rl pc.headerCalls = true) :
    Model.ev val (pc.zero os) = 0 ∧ Model.ev val (pc.one os) = 1 ∧
      Model.ev val (pc.cM os) = toE (ofWord codeMember) (ofWord 0) (ofWord 0) ∧
      Model.ev val (pc.cE os) = toE (ofWord codeEnd) (ofWord 0) (ofWord 0) ∧
      Model.ev val (pc.cP os) = toE (ofWord codePair) (ofWord 0) (ofWord 0) ∧
      Model.ev val (pc.cF os) = toE (ofWord 0) (ofWord final) (ofWord 0) ∧
      ∀ r < pc.runs, Model.ev val (pc.halfLo os r) = toE (val (pc.digests.getD r 0) 0) (val (pc.digests.getD r 0) 1) 0 ∧
        Model.ev val (pc.halfHi os r) = toE (val (pc.digests.getD r 0) 2) (val (pc.digests.getD r 0) 3) 0 := by
  have H := holds_all hF h
  simp only [headerCalls, List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, Call.Holds, getD_o] at H
  obtain ⟨⟨h0, h1, -, -, -, h5, h6, h7, h8⟩, hd⟩ := H
  refine ⟨h0, h1, h5, h6, h7, h8, fun r hr => ?_⟩
  obtain ⟨a0, a1, a2, b0, b1, b2⟩ := hd r (List.mem_range.mpr hr)
  refine ⟨?_, ?_⟩
  · rw [ev_toE]; simp only [halfLo]; rw [a0, a1, a2]
  · rw [ev_toE]
    have q0 : val (pc.halfHi os r) 0 = val (pc.digests.getD r 0) 2 := b0
    have q1 : val (pc.halfHi os r) 1 = val (pc.digests.getD r 0) 3 := b1
    have q2 : val (pc.halfHi os r) 2 = 0 := b2
    rw [q0, q1, q2]

/-- A packed wire is a bit. -/
theorem packed_bit (hF : Facts cs rl os st val) {w : ℕ} (h : pc.packed cs w = true) : IsBit (val w 0) := by
  simp only [packed, List.any_eq_true] at h
  obtain ⟨j, -, hj⟩ := h
  split at hj
  · rename_i bits hb
    obtain ⟨hlt, hcj⟩ := Array.getElem?_eq_some_iff.mp hb
    have hH := hF j hlt (by rw [hcj]; simp [Call.isEq]) (by rw [hcj]; rfl)
    rw [hcj] at hH
    obtain ⟨hbits, -⟩ := hH
    have hm : w ∈ bits.take 64 := by simpa using hj
    obtain ⟨i, hi, hw⟩ := List.getElem_of_mem hm
    have hi' : i < 64 ∧ i < bits.length := by simp at hi; omega
    have := hbits i hi'.1 hi'.2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi'.2, Option.getD_some] at this
    rw [List.getElem_take] at hw
    rw [← hw]
    exact this
  · simp at hj

theorem startOf_cases (i : ℕ) :
    (i = 0 ∧ pc.startOf os i = .yes) ∨
    (i ≠ 0 ∧ i % chunk = 0 ∧ 1 < pc.runs ∧ pc.startOf os i = .ifBit (pc.beta os (i / chunk))) ∨
    (i ≠ 0 ∧ ¬(i % chunk = 0 ∧ 1 < pc.runs) ∧ pc.startOf os i = .no) := by
  unfold startOf
  by_cases h0 : i = 0
  · simp [h0]
  · by_cases h1 : i % chunk = 0 ∧ 1 < pc.runs
    · right; left; exact ⟨h0, h1.1, h1.2, by simp [h0, h1]⟩
    · right; right; exact ⟨h0, h1, by simp [h0, h1]⟩

/-- What a pool's calls say of one assignment: its items' values satisfy `PoolParse.Sem`. -/
theorem pool_sem (hF : Facts cs rl os st val) (hok : pc.ok os cs rl = true) :
    Sem pc.n (pc.sigma os val) (pc.X os val) (pc.vals os val) := by
  obtain ⟨hch0, -, hhdr, -, hitem, hend, hbits⟩ := ok_parts hok
  obtain ⟨hz, ho, hM, hE, hP, hFin, -⟩ := header_sem hF hhdr
  simp only [bitsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at hbits
  obtain ⟨hbi, hbc⟩ := hbits
  have hkind := fun i (hi : i < pc.n) => kind_sem hF hz ho (item_parts (hitem i hi)).1
  have hbeta : ∀ i < pc.n, i ≠ 0 → i % chunk = 0 → 1 < pc.runs → IsBit (val (pc.beta os (i / chunk)) 0) := by
    intro i hi h0 hm hr
    have hj : i / chunk < pc.chunks := by simp only [n, chunk] at hi; simp only [chunk]; omega
    have hb : pc.begins (i / chunk) = true := by
      simp only [begins, Bool.and_eq_true, decide_eq_true_eq]; simp only [chunk] at hm ⊢; omega
    rcases hbc _ hj with h | h
    · rw [hb] at h; exact absurd h (by decide)
    · exact packed_bit hF h
  have hstart : ∀ i < pc.n, Model.ev val (startWire os (pc.one os) (pc.zero os) (pc.p i) (pc.startOf os i)) =
      emb (bitK (pc.sigma os val i)) := by
    intro i hi
    rcases startOf_cases (pc := pc) (os := os) i with ⟨-, hs⟩ | ⟨h0, hm, hr, hs⟩ | ⟨-, -, hs⟩
    · simp only [startWire, hs, sigma, bitK, if_true, emb_one']; exact ho
    · have hst := (item_parts (hitem i hi)).2.1
      rw [hs, if_neg h0] at hst
      obtain ⟨eb, -, -⟩ := start_ifBit hF hz ho hst
      simp only [startWire, hs, sigma]
      rw [eb]
      rcases hbeta i hi h0 hm hr with h | h <;> simp [h, bitK]
    · simp only [startWire, hs, sigma, bitK, Bool.false_eq_true, if_false, emb_zero]; exact hz
  refine ⟨?bits, ?counter, ?chain, ?startPad, ?startEnded, ?padAfter, ?last, ?pair, ?ends⟩
  case bits =>
    intro i hi
    obtain ⟨⟨⟨a, b⟩, c⟩, -⟩ := hbi i hi
    exact ⟨packed_bit hF a, packed_bit hF b, packed_bit hF c⟩
  case counter =>
    intro i hi
    obtain ⟨-, -, hc, -, -⟩ := item_parts (hitem i hi)
    have k := hkind i hi
    dsimp only at k
    have := counter_sem hF hM hE hP hFin (hstart i hi) k.2.2.2.1 hc
    rw [show (pc.vals os val).ins i 0 = val (o os (pc.ctr os i + 5)) 0 by simp [vals], this]
    rfl
  case chain =>
    intro i hi hi0 hσ k hk
    rw [show (pc.vals os val).ins i (2 + k) = vk val (pc.hOf os i) k by
      simp [vals, show 2 + k ≠ 1 by omega, show 2 + k < 6 by omega]]
    show vk val (pc.hOf os i) k = vk val (o os (pc.blk os (i - 1) + 8)) k
    rcases startOf_cases (pc := pc) (os := os) i with ⟨h0, -⟩ | ⟨h0, hm, hr, hs⟩ | ⟨-, -, hs⟩
    · omega
    · have hβ : val (pc.beta os (i / chunk)) 0 = 0 := by
        simp only [sigma, hs, decide_eq_false_iff_not] at hσ
        exact (hbeta i hi h0 hm hr).resolve_right hσ
      obtain ⟨-, -, -, hh, -⟩ := item_parts (hitem i hi)
      rw [hs, if_neg h0] at hh
      obtain ⟨g0, g1, g2, g3⟩ := h_ifBit_zero hF hh hβ
      obtain ⟨-, -, -, -, hbp⟩ := item_parts (hitem (i - 1) (by omega))
      have kp := hkind (i - 1) (by omega)
      dsimp only at kp
      obtain ⟨⟨l0, l1, l2, l3⟩, -⟩ := block_sem hF hz hbp kp.2.2.2.1
      simp only [hOf, hWire, hs]
      interval_cases k <;> simp only [vk, dite_true, show (0:ℕ) < 4 by norm_num,
        show (1:ℕ) < 4 by norm_num, show (2:ℕ) < 4 by norm_num, show (3:ℕ) < 4 by norm_num]
      · exact g0.trans l0
      · exact g1.trans l1
      · exact g2.trans l2
      · exact g3.trans l3
    · simp only [hOf, hWire, hs]
  case startPad =>
    intro i hi hσ
    have k := hkind i hi
    dsimp only at k
    show val (o os (pc.p i)) 0 * val (o os (pc.p i + 1)) 0 = 0
    apply emb_inj
    rw [emb_zero, ← k.2.1]
    obtain ⟨-, hst, -, -, -⟩ := item_parts (hitem i hi)
    rcases startOf_cases (pc := pc) (os := os) i with ⟨-, hs⟩ | ⟨h0, -, -, hs⟩ | ⟨-, -, hs⟩
    · rw [hs] at hst; exact start_yes hF hz hst
    · rw [hs, if_neg h0] at hst
      obtain ⟨-, he, hp⟩ := start_ifBit hF hz ho hst
      simp only [sigma, hs, decide_eq_true_eq] at hσ
      rw [hσ, emb_one', mul_one] at he
      rw [hp, he, hσ, emb_one', add_self_E]
    · simp [sigma, hs] at hσ
  case startEnded =>
    intro i hi hi0 hσ
    obtain ⟨-, hst, -, -, -⟩ := item_parts (hitem i hi)
    rcases startOf_cases (pc := pc) (os := os) i with ⟨h0, -⟩ | ⟨h0, -, -, hs⟩ | ⟨-, -, hs⟩
    · omega
    · rw [hs, if_neg h0] at hst
      obtain ⟨-, he, -⟩ := start_ifBit hF hz ho hst
      simp only [sigma, hs, decide_eq_true_eq] at hσ
      rw [hσ, emb_one', mul_one] at he
      have kp := hkind (i - 1) (by omega)
      dsimp only at kp
      apply emb_inj
      rw [emb_one', ← he, kp.1]
      rfl
    · simp [sigma, hs] at hσ
  case padAfter =>
    intro i hi hi0 hσ
    obtain ⟨-, hst, -, -, -⟩ := item_parts (hitem i hi)
    have k := hkind i hi
    have kp := hkind (i - 1) (by omega)
    dsimp only at k kp
    show val (o os (pc.p i)) 0 * val (o os (pc.p i + 1)) 0 = val (o os (pc.p (i - 1) + 1)) 0
    apply emb_inj
    rw [← k.2.1, ← kp.1]
    rcases startOf_cases (pc := pc) (os := os) i with ⟨h0, -⟩ | ⟨h0, hm, hr, hs⟩ | ⟨h0, -, hs⟩
    · omega
    · rw [hs, if_neg h0] at hst
      obtain ⟨-, -, hp⟩ := start_ifBit hF hz ho hst
      have hβ : val (pc.beta os (i / chunk)) 0 = 0 := by
        simp only [sigma, hs, decide_eq_false_iff_not] at hσ
        exact (hbeta i hi h0 hm hr).resolve_right hσ
      rw [hp, hβ, emb_zero, add_zero]
    · rw [hs, if_neg h0] at hst
      exact start_no hF hst
  case last =>
    have H := holds_all hF hend
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
      Call.Holds] at H
    have k := hkind (pc.n - 1) (by simp only [n, chunk]; omega)
    dsimp only at k
    show val (o os (pc.p (pc.n - 1) + 1)) 0 = 1
    apply emb_inj
    rw [emb_one', ← k.1, ev_of_val H, ho]
  case pair =>
    intro i hi
    have k := hkind i hi
    dsimp only at k
    exact k.2.2.2.2.2.2
  case ends =>
    intro i hi he
    obtain ⟨-, -, -, -, hb⟩ := item_parts (hitem i hi)
    have k := hkind i hi
    dsimp only at k
    exact (block_sem hF hz hb k.2.2.2.1).2 he

/-! The run one-hot and the expected digests. -/

/-- `∑_{r < k} c r · h r`, summed as the rows fold it. -/
noncomputable def dotE (c h : ℕ → E) : ℕ → E
  | 0 => 0
  | r + 1 => c r * h r + dotE c h r

theorem dotE_congr {c h c' h' : ℕ → E} : ∀ k, (∀ r < k, c r = c' r ∧ h r = h' r) → dotE c h k = dotE c' h' k
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [dotE]
    rw [(hk k (Nat.lt_succ_self k)).1, (hk k (Nat.lt_succ_self k)).2,
      dotE_congr k fun r hr => hk r (Nat.lt_succ_of_lt hr)]

/-- A chunk's calls: each one-hot wire moved on by the begin bit, and the expected digest's halves. -/
theorem chunk_sem (hF : Facts cs rl os st val) (hz : Model.ev val (pc.zero os) = 0) {j : ℕ}
    (hch : callsOk cs rl (pc.chunkCalls os j) = true) :
    (pc.begins j = true → ∀ r < pc.runs, Model.ev val (pc.cur os j r) =
      (Model.ev val (if r = 0 then pc.zero os else pc.cur os (j - 1) (r - 1)) + Model.ev val (pc.cur os (j - 1) r)) *
        emb (val (pc.beta os j) 0) + Model.ev val (pc.cur os (j - 1) r)) ∧
    (1 < pc.runs → Model.ev val (pc.eLo os j) = dotE (fun r => Model.ev val (pc.cur os j r))
        (fun r => Model.ev val (pc.halfLo os r)) pc.runs ∧
      Model.ev val (pc.eHi os j) = dotE (fun r => Model.ev val (pc.cur os j r))
        (fun r => Model.ev val (pc.halfHi os r)) pc.runs) := by
  refine ⟨fun hb r hr => ?_, fun h1 => ?_⟩
  · have mA : (pc.chunkAt.getD j 0 + 1 + 2 * r,
        Call.add (if r = 0 then pc.zero os else pc.cur os (j - 1) (r - 1)) (pc.cur os (j - 1) r)) ∈
        pc.chunkCalls os j := by
      simp only [chunkCalls, hb, if_true]
      exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, by simp⟩))
    have mM : (pc.chunkAt.getD j 0 + 2 + 2 * r,
        Call.mulKAdd (o os (pc.chunkAt.getD j 0 + 1 + 2 * r)) (pc.beta os j) (pc.cur os (j - 1) r)) ∈
        pc.chunkCalls os j := by
      simp only [chunkCalls, hb, if_true]
      exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, by simp⟩))
    have hA := holds_of_mem hF hch mA
    have hM := holds_of_mem hF hch mM
    simp only [Call.Holds, getD_o] at hA hM
    rw [show pc.cur os j r = o os (pc.chunkAt.getD j 0 + 2 + 2 * r) by simp [cur, hb], hM, hA]
  · have key : ∀ (half : ℕ → ℕ) (base : ℕ),
        (∀ r < pc.runs, (base + r, Call.mulAdd (pc.cur os j r) (half r)
          (if r = 0 then pc.zero os else o os (base + r - 1))) ∈ pc.chunkCalls os j) →
        ∀ r < pc.runs, Model.ev val (o os (base + r)) =
          dotE (fun r => Model.ev val (pc.cur os j r)) (fun r => Model.ev val (half r)) (r + 1) := by
      intro half base hm r
      induction r with
      | zero =>
        intro hr
        have := holds_of_mem hF hch (hm 0 hr)
        simp only [Call.Holds, getD_o, if_true] at this
        rw [this, hz]
        simp [dotE]
      | succ r ih =>
        intro hr
        have := holds_of_mem hF hch (hm (r + 1) hr)
        simp only [Call.Holds, getD_o, Nat.add_one_ne_zero, if_false] at this
        rw [this, show base + (r + 1) - 1 = base + r by omega, ih (by omega)]
        rfl
    have hlo := key (pc.halfLo os) (pc.expBase j) (fun r hr => by
      simp only [chunkCalls, h1, if_true]
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩)))
    have hhi := key (pc.halfHi os) (pc.expBase j + pc.runs) (fun r hr => by
      simp only [chunkCalls, h1, if_true]
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩)))
    refine ⟨?_, ?_⟩
    · rw [show pc.eLo os j = o os (pc.expBase j + (pc.runs - 1)) by simp [eLo, h1]; congr 1; omega,
        hlo (pc.runs - 1) (by omega), Nat.sub_add_cancel (by omega)]
    · rw [show pc.eHi os j = o os (pc.expBase j + pc.runs + (pc.runs - 1)) by simp [eHi, h1]; congr 1; omega,
        hhi (pc.runs - 1) (by omega), Nat.sub_add_cancel (by omega)]

/-! Two assignments of one pool. -/

section Two

variable {st' : ℕ → Fin 4 → K} {val' : Val}

/-- Two assignments agreeing on a pool's digests and begin bits agree on its run one-hot. -/
theorem cur_agree (hF : Facts cs rl os st val) (hF' : Facts cs rl os st' val') (hok : pc.ok os cs rl = true)
    (hb : ∀ j < pc.chunks, pc.begins j = true → val (pc.beta os j) = val' (pc.beta os j)) :
    ∀ j < pc.chunks, ∀ r < pc.runs, Model.ev val (pc.cur os j r) = Model.ev val' (pc.cur os j r) := by
  obtain ⟨-, -, hhdr, hch, -, -, -⟩ := ok_parts hok
  obtain ⟨hz, ho, -⟩ := header_sem hF hhdr
  obtain ⟨hz', ho', -⟩ := header_sem hF' hhdr
  have hconst : ∀ j r, pc.begins j = false →
      Model.ev val (pc.cur os j r) = Model.ev val' (pc.cur os j r) := by
    intro j r hbg
    simp only [cur, hbg, Bool.false_eq_true, if_false]
    by_cases hr : r = 0
    · simp only [hr, if_true, ho, ho']
    · simp only [hr, if_false, hz, hz']
  intro j
  induction j with
  | zero => intro _ r _; exact hconst 0 r (by simp [begins])
  | succ j ih =>
    intro hj r hr
    cases hbg : pc.begins (j + 1) with
    | false => exact hconst _ r hbg
    | true =>
      have hm : Model.ev val (if r = 0 then pc.zero os else pc.cur os j (r - 1)) =
          Model.ev val' (if r = 0 then pc.zero os else pc.cur os j (r - 1)) := by
        split
        · rw [hz, hz']
        · exact ih (by omega) _ (by omega)
      rw [(chunk_sem hF hz (hch _ hj)).1 hbg r hr, (chunk_sem hF' hz' (hch _ hj)).1 hbg r hr, Nat.add_sub_cancel,
        hb _ hj hbg, ih (by omega) r hr, hm]

theorem halfLo_agree (hF : Facts cs rl os st val) (hF' : Facts cs rl os st' val') (hok : pc.ok os cs rl = true)
    (hd : ∀ r < pc.runs, val (pc.digests.getD r 0) = val' (pc.digests.getD r 0)) :
    ∀ r < pc.runs, Model.ev val (pc.halfLo os r) = Model.ev val' (pc.halfLo os r) ∧
      Model.ev val (pc.halfHi os r) = Model.ev val' (pc.halfHi os r) := by
  obtain ⟨-, -, hhdr, -⟩ := ok_parts hok
  obtain ⟨-, -, -, -, -, -, hh⟩ := header_sem hF hhdr
  obtain ⟨-, -, -, -, -, -, hh'⟩ := header_sem hF' hhdr
  intro r hr
  rw [(hh r hr).1, (hh r hr).2, (hh' r hr).1, (hh' r hr).2, hd r hr]
  exact ⟨rfl, rfl⟩

/-- Two assignments agreeing on a pool's digests and begin bits expect the same digests. -/
theorem X_agree (hF : Facts cs rl os st val) (hF' : Facts cs rl os st' val') (hok : pc.ok os cs rl = true)
    (hd : ∀ r < pc.runs, val (pc.digests.getD r 0) = val' (pc.digests.getD r 0))
    (hb : ∀ j < pc.chunks, pc.begins j = true → val (pc.beta os j) = val' (pc.beta os j)) :
    ∀ i < pc.n, pc.X os val i = pc.X os val' i := by
  obtain ⟨-, hr0, hhdr, hch, -, -, -⟩ := ok_parts hok
  obtain ⟨hz, -⟩ := header_sem hF hhdr
  obtain ⟨hz', -⟩ := header_sem hF' hhdr
  intro i hi
  have hj : i / chunk < pc.chunks := by simp only [n, chunk] at hi; simp only [chunk]; omega
  have hh := halfLo_agree hF hF' hok hd
  by_cases h1 : 1 < pc.runs
  · obtain ⟨l, h⟩ := (chunk_sem hF hz (hch _ hj)).2 h1
    obtain ⟨l', h'⟩ := (chunk_sem hF' hz' (hch _ hj)).2 h1
    have hc := cur_agree hF hF' hok hb _ hj
    simp only [X, l, h, l', h']
    rw [dotE_congr _ fun r hr => ⟨hc r hr, (hh r hr).1⟩, dotE_congr _ fun r hr => ⟨hc r hr, (hh r hr).2⟩]
  · simp only [X, eLo, eHi, h1, if_false]
    rw [(hh 0 hr0).1, (hh 0 hr0).2]

theorem sigma_zero : pc.sigma os val 0 = true := by simp [sigma, startOf]

theorem sigma_agree (hb : ∀ j < pc.chunks, pc.begins j = true → val (pc.beta os j) = val' (pc.beta os j)) :
    ∀ i < pc.n, pc.sigma os val i = pc.sigma os val' i := by
  intro i hi
  rcases startOf_cases (pc := pc) (os := os) i with ⟨-, hs⟩ | ⟨h0, hm, hr, hs⟩ | ⟨-, -, hs⟩
  · simp [sigma, hs]
  · have hj : i / chunk < pc.chunks := by simp only [n, chunk] at hi; simp only [chunk]; omega
    have hbg : pc.begins (i / chunk) = true := by
      simp only [begins, Bool.and_eq_true, decide_eq_true_eq]; simp only [chunk] at hm ⊢; omega
    simp only [sigma, hs, hb _ hj hbg]
  · simp [sigma, hs]

/-- A run's items expect one digest. -/
theorem steady (hF : Facts cs rl os st val) (hok : pc.ok os cs rl = true) :
    ∀ i < pc.n, 0 < i → pc.sigma os val i = false → pc.X os val i = pc.X os val (i - 1) := by
  obtain ⟨-, -, hhdr, hch, -, -, -⟩ := ok_parts hok
  obtain ⟨hz, -⟩ := header_sem hF hhdr
  intro i hi hi0 hσ
  rcases startOf_cases (pc := pc) (os := os) i with ⟨h0, -⟩ | ⟨h0, hm, hr, hs⟩ | ⟨-, hn, hs⟩
  · omega
  · simp only [sigma, hs, decide_eq_false_iff_not] at hσ
    have hj : i / chunk < pc.chunks := by simp only [n, chunk] at hi; simp only [chunk]; omega
    have hbg : pc.begins (i / chunk) = true := by
      simp only [begins, Bool.and_eq_true, decide_eq_true_eq]; simp only [chunk] at hm ⊢; omega
    have hj' : (i - 1) / chunk = i / chunk - 1 := by simp only [chunk] at hm ⊢; omega
    have hbit : val (pc.beta os (i / chunk)) 0 = 0 := by
      obtain ⟨-, -, -, -, -, -, hbits⟩ := ok_parts hok
      simp only [bitsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
        Bool.not_eq_true'] at hbits
      rcases hbits.2 _ hj with h | h
      · rw [hbg] at h; exact absurd h (by decide)
      · exact (packed_bit hF h).resolve_right hσ
    obtain ⟨l, h⟩ := (chunk_sem hF hz (hch _ hj)).2 hr
    obtain ⟨l', h'⟩ := (chunk_sem hF hz (hch _ (lt_of_le_of_lt (Nat.sub_le _ _) hj))).2 hr
    have hc : ∀ r < pc.runs, Model.ev val (pc.cur os (i / chunk) r) = Model.ev val (pc.cur os (i / chunk - 1) r) := by
      intro r hr'
      rw [(chunk_sem hF hz (hch _ hj)).1 hbg r hr', hbit, emb_zero, mul_zero, zero_add]
    rw [show pc.X os val (i - 1) = (Model.ev val (pc.eLo os (i / chunk - 1)), Model.ev val (pc.eHi os (i / chunk - 1)))
      by simp only [X, hj'], l', h']
    show (Model.ev val (pc.eLo os (i / chunk)), Model.ev val (pc.eHi os (i / chunk))) = _
    rw [l, h, dotE_congr _ fun r hr' => ⟨hc r hr', rfl⟩, dotE_congr _ fun r hr' => ⟨hc r hr', rfl⟩]
  · by_cases hm : i % chunk = 0
    · have hr : ¬ 1 < pc.runs := fun h => hn ⟨hm, h⟩
      simp [X, eLo, eHi, hr]
    · have : (i - 1) / chunk = i / chunk := by simp only [chunk] at hm ⊢; omega
      simp only [X, this]

/-- The rows of a pool's items, under collision resistance across the two assignments. -/
theorem pool_cr {s : State} (hR : RowsIn cs os s) (hok : pc.ok os cs rl = true) (hcr : HashCR s val val') :
    ∀ i < pc.n, ∀ j < pc.n, (∀ k < 4, (pc.vals os val).outs i k = (pc.vals os val').outs j k) →
      ∀ c < 14, (pc.vals os val).ins i c = (pc.vals os val').ins j c := by
  obtain ⟨-, -, -, -, hitem, -, -⟩ := ok_parts hok
  have hrow : ∀ i < pc.n, ∃ mux bit x ds ch, ([pc.hOf os i, o os (pc.ctr os i + 5), mux, bit, x, ds,
      o os (pc.blk os i + 8), ch] ++ blockWords os (pc.blk os i)) ∈ s.hash := by
    intro i hi
    have hb := (item_parts (hitem i hi)).2.2.2.2
    exact rows_of_mem hR hb (j := pc.blk os i + 8)
      (c := .hashBlock (pc.hOf os i) (blockWords os (pc.blk os i)) (o os (pc.ctr os i + 5))) (by simp [blockCalls])
  have hlen : ∀ b, (blockWords os b).length = 8 := fun b => by simp [blockWords]
  intro i hi j hj hout c hc
  obtain ⟨mux, bit, x, ds, ch, hri⟩ := hrow i hi
  obtain ⟨mux', bit', x', ds', ch', hrj⟩ := hrow j hj
  have hmap := hcr _ hri _ hrj (map_eq_of_getD (length_hashOut _) (length_hashOut _) fun k hk => by
    rw [hashOut_block, hashOut_block]; exact hout k hk; exact hk; exact hk)
  have := getD_of_map_eq (length_hashIn _) (length_hashIn _) hmap c hc
  rw [hashIn_block _ _ _ _ _ _ _ _ _ (hlen _) _ c hc, hashIn_block _ _ _ _ _ _ _ _ _ (hlen _) _ c hc] at this
  simpa [vals] using this

/-- Parse uniqueness of a pool: two assignments in which every replayed call holds, agreeing on its digests and begin
bits, whose compressions do not collide, give every item the same kind bits, and every item but padding the same
row inputs, its block among them. -/
theorem pool_unique {s : State} (hF : Facts cs rl os st val) (hF' : Facts cs rl os st' val') (hR : RowsIn cs os s)
    (hok : pc.ok os cs rl = true) (hcr : HashCR s val val')
    (hd : ∀ r < pc.runs, val (pc.digests.getD r 0) = val' (pc.digests.getD r 0))
    (hb : ∀ j < pc.chunks, pc.begins j = true → val (pc.beta os j) = val' (pc.beta os j)) :
    ∀ i < pc.n, (pc.vals os val).b0 i = (pc.vals os val').b0 i ∧ (pc.vals os val).b1 i = (pc.vals os val').b1 i ∧
      (pc.vals os val).p i = (pc.vals os val').p i ∧
      ((pc.vals os val).pad i = 0 → ∀ c < 14, (pc.vals os val).ins i c = (pc.vals os val').ins i c) :=
  parse_unique (pool_sem hF hok)
    ((pool_sem hF' hok).congr (fun i hi => (sigma_agree hb i hi).symm) fun i hi => (X_agree hF hF' hok hd hb i hi).symm)
    sigma_zero (steady hF hok) (pool_cr hR hok hcr)

end Two

end PoolCert

/-! A product. -/

/-- Where a dump's calls make a union product over a pool: the pool, the product's first call, the point's `X + 1`
and sixteen weights, and each item's first call. -/
structure ProdCert where
  pool : ℕ
  start : ℕ
  x1 : ℕ
  weights : List ℕ
  itemAt : Array ℕ
  deriving Inhabited, Repr

namespace ProdCert

variable (os : Array (List ℕ)) (pc : PoolCert) (qc : ProdCert)

def zero : ℕ := o os qc.start
def one : ℕ := o os (qc.start + 1)
def w (k : ℕ) : ℕ := qc.weights.getD k 0
def q (i : ℕ) : ℕ := qc.itemAt.getD i 0
/-- Whether item `i`'s label is reset by a begin bit: one call. -/
def d (i : ℕ) : ℕ := match pc.startOf os i with
  | .ifBit _ => 1
  | _ => 0
/-- Item `i`'s label after it. -/
def labOut (i : ℕ) : ℕ := o os (qc.q i + d os pc i + 7)
/-- Item `i`'s label before it. -/
def lab (i : ℕ) : ℕ := match pc.startOf os i with
  | .yes => qc.zero os
  | .ifBit _ => o os (qc.q i)
  | .no => labOut os pc qc (i - 1)
/-- Calls per slot. -/
def len : ℕ := if pc.selecting then 8 else 7
def base (i sl : ℕ) : ℕ := qc.q i + d os pc i + 8 + sl * len pc
/-- The running product after item `i`'s slot `sl`. -/
def acc (i sl : ℕ) : ℕ := o os (base os pc qc i sl + len pc - 1)
def accIn (i sl : ℕ) : ℕ := if sl = 1 then acc os pc qc i 0 else if i = 0 then qc.one os else acc os pc qc (i - 1) 1
/-- The product. -/
def out : ℕ := acc os pc qc (pc.n - 1) 1

/-- Item `i`'s block word `j`. -/
def m (i j : ℕ) : ℕ := o os (pc.blk os i + j)
def valid (i sl : ℕ) : ℕ := if sl = 0 then o os (pc.p i + 6) else o os (pc.p i + 11)
def selW (i sl : ℕ) : ℕ := if sl = 0 then o os (pc.blk os i + 16) else o os (pc.blk os i + 17)

/-- Item `i`'s label reset at a begin bit. -/
def resetCalls (i : ℕ) : List (ℕ × Call) :=
  match pc.startOf os i with
  | .ifBit bit => [(qc.q i, .mulKAdd (labOut os pc qc (i - 1)) bit (labOut os pc qc (i - 1)))]
  | _ => []

/-- Item `i`'s header fingerprint and new label. -/
def headCalls (i : ℕ) : List (ℕ × Call) :=
  let p := qc.q i + d os pc i
  [(p, .mulKAdd (qc.w 1) (m os pc i 0) (qc.w 0)), (p + 1, .mulKAdd (qc.w 2) (m os pc i 1) (o os p)),
   (p + 2, .mulKAdd (qc.w 3) (m os pc i 2) (o os (p + 1))), (p + 3, .mulKAdd (qc.w 4) (m os pc i 3) (o os (p + 2))),
   (p + 4, .mulKAdd (qc.w 5) (m os pc i 4) (o os (p + 3))), (p + 5, .mulKAdd (qc.w 6) (m os pc i 5) (o os (p + 4))),
   (p + 6, .add (o os (p + 5)) (lab os pc qc i)), (p + 7, .mulAdd (o os (pc.p i + 9)) (o os (p + 6)) (o os (p + 5)))]

/-- Slot `sl` of item `i`: its fingerprint, term and factor, and the running product. -/
def slotCalls (i sl : ℕ) : List (ℕ × Call) :=
  let b := base os pc qc i sl
  [(b, .mulKAdd (qc.w 7) (m os pc i (4 * sl)) (labOut os pc qc i)),
   (b + 1, .mulKAdd (qc.w 8) (m os pc i (4 * sl + 1)) (o os b)),
   (b + 2, .mulKAdd (qc.w 9) (m os pc i (4 * sl + 2)) (o os (b + 1))),
   (b + 3, .mulKAdd (qc.w 10) (m os pc i (4 * sl + 3)) (o os (b + 2))), (b + 4, .add qc.x1 (o os (b + 3)))] ++
  if pc.selecting then
    [(b + 5, .mul (valid os pc i sl) (o os (b + 4))), (b + 6, .mulKAdd (o os (b + 5)) (selW os pc i sl) (qc.one os)),
     (b + 7, .mul (accIn os pc qc i sl) (o os (b + 6)))]
  else [(b + 5, .mulAdd (valid os pc i sl) (o os (b + 4)) (qc.one os)), (b + 6, .mul (accIn os pc qc i sl) (o os (b + 5)))]

/-- The product's calls are in the replay. -/
def ok (cs : Array Call) (rl : Array Bool) : Bool :=
  callsOk cs rl [(qc.start, .zero), (qc.start + 1, .one)] && (List.range pc.n).all fun i =>
    callsOk cs rl (qc.resetCalls os pc i) && callsOk cs rl (qc.headCalls os pc i) &&
      callsOk cs rl (qc.slotCalls os pc i 0) && callsOk cs rl (qc.slotCalls os pc i 1)

end ProdCert

/-! Two assignments of one product. -/

section Two

open ProdCert

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {pc : PoolCert} {qc : ProdCert}
  {st st' : ℕ → Fin 4 → K} {val val' : Val}

theorem slot_agree (hF : Facts cs rl os st val) (hF' : Facts cs rl os st' val') {i sl : ℕ}
    (hok : callsOk cs rl (qc.slotCalls os pc i sl) = true) (ho : Model.ev val (qc.one os) = 1)
    (ho' : Model.ev val' (qc.one os) = 1)
    (hlab : Model.ev val (labOut os pc qc i) = Model.ev val' (labOut os pc qc i))
    (hacc : Model.ev val (accIn os pc qc i sl) = Model.ev val' (accIn os pc qc i sl))
    (hw : ∀ k < 11, Model.ev val (qc.w k) = Model.ev val' (qc.w k)) (hx : Model.ev val qc.x1 = Model.ev val' qc.x1)
    (hs : pc.selecting = true → val (selW os pc i sl) 0 = val' (selW os pc i sl) 0)
    (hcase : (Model.ev val (valid os pc i sl) = Model.ev val' (valid os pc i sl) ∧
        ∀ j < 4, val (m os pc i (4 * sl + j)) 0 = val' (m os pc i (4 * sl + j)) 0) ∨
      (Model.ev val (valid os pc i sl) = 0 ∧ Model.ev val' (valid os pc i sl) = 0)) :
    Model.ev val (acc os pc qc i sl) = Model.ev val' (acc os pc qc i sl) := by
  have H := holds_all hF hok
  have H' := holds_all hF' hok
  set b := base os pc qc i sl
  cases hsel : pc.selecting with
  | true =>
    simp only [slotCalls, hsel, if_true, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true, Call.Holds, getD_o] at H H'
    obtain ⟨⟨f0, f1, f2, f3, t⟩, hd, fc, ac⟩ := H
    obtain ⟨⟨f0', f1', f2', f3', t'⟩, hd', fc', ac'⟩ := H'
    rw [show acc os pc qc i sl = o os (b + 7) by simp [acc, len, hsel, b], ac, ac', fc, fc', hacc, ho, ho',
      hs hsel]
    rcases hcase with ⟨hv, hm⟩ | ⟨hv, hv'⟩
    · have m0 := hm 0 (by norm_num); have m1 := hm 1 (by norm_num)
      have m2 := hm 2 (by norm_num); have m3 := hm 3 (by norm_num)
      simp only [Nat.add_zero] at m0
      rw [hd, hd', hv, t, t', hx, f3, f3', f2, f2', f1, f1', f0, f0', hw 7 (by norm_num), hw 8 (by norm_num), hw 9 (by norm_num), hw 10 (by norm_num), m0, m1, m2, m3, hlab]
    · rw [hd, hd', hv, hv']
      ring
  | false =>
    simp only [slotCalls, hsel, Bool.false_eq_true, if_false, List.forall_mem_append, List.forall_mem_cons,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, Call.Holds, getD_o] at H H'
    obtain ⟨⟨f0, f1, f2, f3, t⟩, fc, ac⟩ := H
    obtain ⟨⟨f0', f1', f2', f3', t'⟩, fc', ac'⟩ := H'
    rw [show acc os pc qc i sl = o os (b + 6) by simp [acc, len, hsel, b], ac, ac', fc, fc', hacc, ho, ho']
    rcases hcase with ⟨hv, hm⟩ | ⟨hv, hv'⟩
    · have m0 := hm 0 (by norm_num); have m1 := hm 1 (by norm_num)
      have m2 := hm 2 (by norm_num); have m3 := hm 3 (by norm_num)
      simp only [Nat.add_zero] at m0
      rw [hv, t, t', hx, f3, f3', f2, f2', f1, f1', f0, f0', hw 7 (by norm_num), hw 8 (by norm_num), hw 9 (by norm_num), hw 10 (by norm_num), m0, m1, m2, m3, hlab]
    · rw [hv, hv']
      ring

theorem head_agree (hF : Facts cs rl os st val) (hF' : Facts cs rl os st' val') {i : ℕ}
    (hok : callsOk cs rl (qc.headCalls os pc i) = true)
    (hlab : Model.ev val (lab os pc qc i) = Model.ev val' (lab os pc qc i))
    (hw : ∀ k < 11, Model.ev val (qc.w k) = Model.ev val' (qc.w k))
    (hcase : (Model.ev val (o os (pc.p i + 9)) = Model.ev val' (o os (pc.p i + 9)) ∧
        ∀ j < 6, val (m os pc i j) 0 = val' (m os pc i j) 0) ∨
      (Model.ev val (o os (pc.p i + 9)) = 1 ∧ Model.ev val' (o os (pc.p i + 9)) = 1)) :
    Model.ev val (labOut os pc qc i) = Model.ev val' (labOut os pc qc i) := by
  have H := holds_all hF hok
  have H' := holds_all hF' hok
  simp only [headCalls, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
    Call.Holds, getD_o] at H H'
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := H
  obtain ⟨h0', h1', h2', h3', h4', h5', h6', h7'⟩ := H'
  rw [show labOut os pc qc i = o os (qc.q i + d os pc i + 7) from rfl, h7, h7', h6, h6', hlab]
  rcases hcase with ⟨hn, hm⟩ | ⟨hn, hn'⟩
  · rw [hn, h5, h5', h4, h4', h3, h3', h2, h2', h1, h1', h0, h0', hw 0 (by norm_num), hw 1 (by norm_num), hw 2 (by norm_num), hw 3 (by norm_num), hw 4 (by norm_num), hw 5 (by norm_num), hw 6 (by norm_num),
      hm 0 (by norm_num), hm 1 (by norm_num), hm 2 (by norm_num), hm 3 (by norm_num), hm 4 (by norm_num),
      hm 5 (by norm_num)]
  · rw [hn, hn']
    linear_combination (Model.ev val (o os (qc.q i + d os pc i + 5)) - Model.ev val' (o os (qc.q i + d os pc i + 5))) * two_E

theorem blockWords_getD (b j : ℕ) (hj : j < 8) : (blockWords os b).getD j 0 = o os (b + j) := by
  simp [blockWords, List.getD_eq_getElem?_getD, hj]

/-- One item of a product: given the previous item's label and running product agree, so do this item's. -/
theorem prod_step {s : State} (hF : Facts cs rl os st val) (hF' : Facts cs rl os st' val') (hR : RowsIn cs os s)
    (hok : pc.ok os cs rl = true) (hqok : qc.ok os pc cs rl = true) (hcr : HashCR s val val')
    (hd : ∀ r < pc.runs, val (pc.digests.getD r 0) = val' (pc.digests.getD r 0))
    (hb : ∀ j < pc.chunks, pc.begins j = true → val (pc.beta os j) = val' (pc.beta os j))
    (hs : pc.selecting = true → ∀ i < pc.n,
      val (o os (pc.blk os i + 16)) = val' (o os (pc.blk os i + 16)) ∧
        val (o os (pc.blk os i + 17)) = val' (o os (pc.blk os i + 17)))
    (hx : val qc.x1 = val' qc.x1) (hw : ∀ k < 11, val (qc.w k) = val' (qc.w k)) {i : ℕ} (hi : i < pc.n)
    (ih : 0 < i → Model.ev val (labOut os pc qc (i - 1)) = Model.ev val' (labOut os pc qc (i - 1)) ∧
      Model.ev val (acc os pc qc (i - 1) 1) = Model.ev val' (acc os pc qc (i - 1) 1)) :
    Model.ev val (labOut os pc qc i) = Model.ev val' (labOut os pc qc i) ∧
      Model.ev val (acc os pc qc i 1) = Model.ev val' (acc os pc qc i 1) := by
  simp only [ProdCert.ok, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hqok
  obtain ⟨hhq, hitq⟩ := hqok
  obtain ⟨⟨⟨hrst, hhead⟩, hs0⟩, hs1⟩ := hitq i hi
  have Hq := holds_all hF hhq
  have Hq' := holds_all hF' hhq
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, Call.Holds,
    getD_o] at Hq Hq'
  have hz : Model.ev val (qc.zero os) = 0 := Hq.1
  have ho : Model.ev val (qc.one os) = 1 := Hq.2
  have hz' : Model.ev val' (qc.zero os) = 0 := Hq'.1
  have ho' : Model.ev val' (qc.one os) = 1 := Hq'.2
  have hwE : ∀ k < 11, Model.ev val (qc.w k) = Model.ev val' (qc.w k) := fun k hk => ev_of_val' (hw k hk)
  obtain ⟨-, -, hhdr, -, hitem, -, -⟩ := PoolCert.ok_parts hok
  obtain ⟨phz, pho, -⟩ := PoolCert.header_sem hF hhdr
  obtain ⟨phz', pho', -⟩ := PoolCert.header_sem hF' hhdr
  -- The label before the item.
  have hlab : Model.ev val (lab os pc qc i) = Model.ev val' (lab os pc qc i) := by
    rcases PoolCert.startOf_cases (pc := pc) (os := os) i with ⟨-, hst⟩ | ⟨h0, hm, hr, hst⟩ | ⟨h0, -, hst⟩
    · simp only [lab, hst]; rw [hz, hz']
    · have hj : i / chunk < pc.chunks := by simp only [PoolCert.n, chunk] at hi; simp only [chunk]; omega
      have hbg : pc.begins (i / chunk) = true := by
        simp only [PoolCert.begins, Bool.and_eq_true, decide_eq_true_eq]; simp only [chunk] at hm ⊢; omega
      simp only [resetCalls, hst] at hrst
      have H := holds_all hF hrst
      have H' := holds_all hF' hrst
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, Call.Holds,
        getD_o] at H H'
      simp only [lab, hst]
      rw [H, H', (ih (by omega)).1, hb _ hj hbg]
    · simp only [lab, hst]; exact (ih (by omega)).1
  -- The item's values in both assignments.
  have hpu := PoolCert.pool_unique hF hF' hR hok hcr hd hb i hi
  have k := kind_sem hF phz pho (PoolCert.item_parts (hitem i hi)).1
  have k' := kind_sem hF' phz' pho' (PoolCert.item_parts (hitem i hi)).1
  dsimp only at k k'
  obtain ⟨e0, e1, ep, hins⟩ := hpu
  simp only [PoolCert.vals] at e0 e1 ep hins
  have hbits := (PoolCert.pool_sem hF hok).bits i hi
  simp only [PoolCert.vals] at hbits
  have hsel : ∀ sl, pc.selecting = true → val (selW os pc i sl) 0 = val' (selW os pc i sl) 0 := by
    intro sl hse
    obtain ⟨a, b⟩ := hs hse i hi
    unfold selW; split
    · rw [a]
    · rw [b]
  by_cases hpad : val (o os (pc.p i)) 0 * val (o os (pc.p i + 1)) 0 = 0
  · have hmv : ∀ j < 8, val (m os pc i j) 0 = val' (m os pc i j) 0 := by
      intro j hj
      have := hins hpad (6 + j) (by omega)
      simp only [show 6 + j ≠ 0 by omega, show 6 + j ≠ 1 by omega, show ¬ 6 + j < 6 by omega, if_false,
        show 6 + j - 6 = j by omega, blockWords_getD _ j hj] at this
      exact this
    have hl := head_agree hF hF' hhead hlab hwE (Or.inl ⟨by rw [k.2.2.2.2.1, k'.2.2.2.2.1, e0, e1],
      fun j hj => hmv j (by omega)⟩)
    have hv : ∀ sl, Model.ev val (valid os pc i sl) = Model.ev val' (valid os pc i sl) := by
      intro sl; unfold valid; split
      · rw [k.2.2.1, k'.2.2.1, e0, e1]
      · rw [k.2.2.2.2.2.1, k'.2.2.2.2.2.1, e0, e1, ep]
    have a0 := slot_agree hF hF' hs0 ho ho' hl
      (by simp only [accIn, Nat.zero_ne_one, if_false]; split
          · rw [ho, ho']
          · exact (ih (by omega)).2)
      hwE (ev_of_val' hx) (hsel 0) (Or.inl ⟨hv 0, fun j hj => hmv _ (by omega)⟩)
    exact ⟨hl, slot_agree hF hF' hs1 ho ho' hl (by simp only [accIn, if_true]; exact a0) hwE (ev_of_val' hx)
      (hsel 1) (Or.inl ⟨hv 1, fun j hj => hmv _ (by omega)⟩)⟩
  · -- Padding: its label is the label before it, and its factors are one.
    have hp1 : val (o os (pc.p i)) 0 * val (o os (pc.p i + 1)) 0 = 1 :=
      (pad_bit hbits.1 hbits.2.1).resolve_left hpad
    obtain ⟨a0, a1⟩ := pad_one hbits.1 hbits.2.1 hp1
    have b0' : val' (o os (pc.p i)) 0 = 1 := e0 ▸ a0
    have b1' : val' (o os (pc.p i + 1)) 0 = 1 := e1 ▸ a1
    have hl := head_agree hF hF' hhead hlab hwE (Or.inr ⟨by rw [k.2.2.2.2.1, a0, a1, two_K', zero_add, mul_one, emb_one'],
      by rw [k'.2.2.2.2.1, b0', b1', two_K', zero_add, mul_one, emb_one']⟩)
    have hv : ∀ sl, Model.ev val (valid os pc i sl) = 0 ∧ Model.ev val' (valid os pc i sl) = 0 := by
      intro sl; unfold valid; split
      · exact ⟨by rw [k.2.2.1, a0, a1, one_mul, two_K', emb_zero], by rw [k'.2.2.1, b0', b1', one_mul, two_K', emb_zero]⟩
      · exact ⟨by rw [k.2.2.2.2.2.1, a0, a1, one_mul, two_K', zero_mul, emb_zero],
          by rw [k'.2.2.2.2.2.1, b0', b1', one_mul, two_K', zero_mul, emb_zero]⟩
    have a0' := slot_agree hF hF' hs0 ho ho' hl
      (by simp only [accIn, Nat.zero_ne_one, if_false]; split
          · rw [ho, ho']
          · exact (ih (by omega)).2)
      hwE (ev_of_val' hx) (hsel 0) (Or.inr (hv 0))
    exact ⟨hl, slot_agree hF hF' hs1 ho ho' hl (by simp only [accIn, if_true]; exact a0') hwE (ev_of_val' hx)
      (hsel 1) (Or.inr (hv 1))⟩

/-- Two assignments in which every replayed call holds, agreeing on a union's digests, begin and selection bits and
point, whose compressions do not collide, give its product one value. -/
theorem prod_agree {s : State} (hF : Facts cs rl os st val) (hF' : Facts cs rl os st' val') (hR : RowsIn cs os s)
    (hok : pc.ok os cs rl = true) (hqok : qc.ok os pc cs rl = true) (hcr : HashCR s val val')
    (hd : ∀ r < pc.runs, val (pc.digests.getD r 0) = val' (pc.digests.getD r 0))
    (hb : ∀ j < pc.chunks, pc.begins j = true → val (pc.beta os j) = val' (pc.beta os j))
    (hs : pc.selecting = true → ∀ i < pc.n,
      val (o os (pc.blk os i + 16)) = val' (o os (pc.blk os i + 16)) ∧
        val (o os (pc.blk os i + 17)) = val' (o os (pc.blk os i + 17)))
    (hx : val qc.x1 = val' qc.x1) (hw : ∀ k < 11, val (qc.w k) = val' (qc.w k)) :
    Model.ev val (out os pc qc) = Model.ev val' (out os pc qc) := by
  have key : ∀ i < pc.n, Model.ev val (labOut os pc qc i) = Model.ev val' (labOut os pc qc i) ∧
      Model.ev val (acc os pc qc i 1) = Model.ev val' (acc os pc qc i 1) := by
    intro i
    induction i with
    | zero => intro hi; exact prod_step hF hF' hR hok hqok hcr hd hb hs hx hw hi (fun h => absurd h (lt_irrefl 0))
    | succ i ih => intro hi; exact prod_step hF hF' hR hok hqok hcr hd hb hs hx hw hi fun _ => ih (by omega)
  have hn : 0 < pc.n := by
    obtain ⟨h0, -⟩ := PoolCert.ok_parts hok
    simp only [PoolCert.n, chunk]; omega
  exact (key _ (by omega)).2

theorem getD_mem_of_lt {l : List ℕ} {r : ℕ} (hr : r < l.length) : l.getD r 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]
  exact List.getElem_mem hr

/-- What a pool commits to before its point is drawn: its digests, begin bits, and selection words when selecting. -/
def PoolCert.committed (os : Array (List ℕ)) (pc : PoolCert) : List ℕ :=
  pc.digests ++ ((List.range pc.chunks).filter (pc.begins ·)).map (pc.beta os) ++
    (if pc.selecting then (List.range pc.n).flatMap fun i => [o os (pc.blk os i + 16), o os (pc.blk os i + 17)]
      else [])

/-- A product's claim: the wires its value is a function of (what its pool commits to, the point's `X + 1` and the
weights it reads), and its output. -/
def ProdCert.claim (os : Array (List ℕ)) (qc : ProdCert) (pc : PoolCert) : UnionClaim where
  inputs := pc.committed os ++ qc.x1 :: (List.range 11).map qc.w
  out := ProdCert.out os pc qc

/-- A product is a function of its claim's inputs: parse uniqueness of its pool under collision resistance. -/
theorem claim_valid {s : State} (hF : Facts cs rl os st val) (hF' : Facts cs rl os st' val') (hR : RowsIn cs os s)
    (hok : pc.ok os cs rl = true) (hqok : qc.ok os pc cs rl = true) (hcr : HashCR s val val')
    (hin : ∀ w ∈ (qc.claim os pc).inputs, val w = val' w) :
    Model.ev val (qc.claim os pc).out = Model.ev val' (qc.claim os pc).out := by
  simp only [ProdCert.claim, PoolCert.committed, List.mem_append, List.mem_cons, List.mem_map, List.mem_filter,
    List.mem_range] at hin
  refine prod_agree hF hF' hR hok hqok hcr (fun r hr => hin _ (Or.inl (Or.inl (Or.inl (getD_mem_of_lt hr)))))
    (fun j hj hb => hin _ (Or.inl (Or.inl (Or.inr ⟨j, ⟨hj, hb⟩, rfl⟩)))) (fun hse i hi => ⟨?_, ?_⟩)
    (hin _ (Or.inr (Or.inl rfl))) (fun k hk => hin _ (Or.inr (Or.inr ⟨k, hk, rfl⟩)))
  · exact hin _ (Or.inl (Or.inr (by simp [hse]; exact ⟨i, hi, Or.inl rfl⟩)))
  · exact hin _ (Or.inl (Or.inr (by simp [hse]; exact ⟨i, hi, Or.inr rfl⟩)))

end Two

/-! The point. -/

/-- Where a dump's calls draw a union's point: the first call, `X`'s wire and `A`'s four wires. -/
structure PointCert where
  start : ℕ
  x : ℕ
  a : List ℕ
  deriving Inhabited, Repr, DecidableEq

namespace PointCert

variable (os : Array (List ℕ)) (pt : PointCert)

def aj (j : ℕ) : ℕ := pt.a.getD j 0
def one : ℕ := o os (pt.start + 2)
/-- Round `j`'s first call. -/
def round (j : ℕ) : ℕ := pt.start + 3 + j + 2 * (2 ^ j - 1)
/-- The table's entry `k` before round `j`. -/
def tbl (j k : ℕ) : ℕ := if j = 0 then pt.one os else o os (pt.round (j - 1) + 1 + k)

/-- `X + 1`, then `eq_weights`: each round's `1 + A_j`, the table times it, then the table times `A_j`. -/
def calls : List (ℕ × Call) :=
  [(pt.start, .one), (pt.start + 1, .add pt.x (o os pt.start)), (pt.start + 2, .one)] ++
  (List.range 4).flatMap fun j =>
    ((pt.round j, .add (pt.aj j) (pt.one os)) ::
      (List.range (2 ^ j)).map fun k => (pt.round j + 1 + k, .mul (pt.tbl os j k) (o os (pt.round j)))) ++
      (List.range (2 ^ j)).map fun k => (pt.round j + 1 + 2 ^ j + k, .mul (pt.tbl os j k) (pt.aj j))

def x1 : ℕ := o os (pt.start + 1)
def weight (k : ℕ) : ℕ := o os (pt.start + 21 + k)

/-- The point's calls are in the replay, and a product reads its `X + 1` and weights. -/
def ok (cs : Array Call) (rl : Array Bool) (qc : ProdCert) : Bool :=
  callsOk cs rl (pt.calls os) && qc.x1 == pt.x1 os && qc.weights == (List.range 16).map (pt.weight os)

end PointCert

/-- `∏_{i < j} (A_i if bit i of k else 1 + A_i)`. -/
noncomputable def prodBits (a : ℕ → E) (k j : ℕ) : E :=
  ∏ i ∈ Finset.range j, if k.testBit i then a i else 1 + a i

section Point

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}
  {pt : PointCert}

theorem round_succ (j : ℕ) : pt.round (j + 1) = pt.round j + 1 + 2 ^ j + 2 ^ j := by
  simp only [PointCert.round, pow_succ]
  have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  omega

/-- Round `j` of `eq_weights` doubles the table. -/
theorem round_sem (hF : Facts cs rl os st val) (hok : callsOk cs rl (pt.calls os) = true)
    (ho : Model.ev val (pt.one os) = 1) {j : ℕ} (hj : j < 4) :
    ∀ k < 2 ^ (j + 1), Model.ev val (pt.tbl os (j + 1) k) =
      Model.ev val (pt.tbl os j (k % 2 ^ j)) *
        (if k.testBit j then Model.ev val (pt.aj j) else 1 + Model.ev val (pt.aj j)) := by
  have hmem : ∀ x, x ∈ ((pt.round j, Call.add (pt.aj j) (pt.one os)) ::
      (List.range (2 ^ j)).map fun k => (pt.round j + 1 + k, Call.mul (pt.tbl os j k) (o os (pt.round j)))) ++
      (List.range (2 ^ j)).map (fun k => (pt.round j + 1 + 2 ^ j + k, Call.mul (pt.tbl os j k) (pt.aj j))) →
      x ∈ pt.calls os := fun x hx =>
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, hx⟩)
  have hnot := holds_of_mem hF hok (hmem _ (List.mem_append_left _ (List.mem_cons_self ..)))
  simp only [Call.Holds, getD_o, ho] at hnot
  intro k hk
  rw [show pt.tbl os (j + 1) k = o os (pt.round j + 1 + k) by simp [PointCert.tbl]]
  by_cases hlo : k < 2 ^ j
  · have h := holds_of_mem hF hok (hmem _ (List.mem_append_left _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨k, List.mem_range.mpr hlo, rfl⟩))))
    simp only [Call.Holds, getD_o] at h
    rw [h, hnot, Nat.mod_eq_of_lt hlo]
    simp only [Nat.testBit_lt_two_pow hlo, Bool.false_eq_true, if_false]
    ring
  · have hk' : k - 2 ^ j < 2 ^ j := by rw [pow_succ] at hk; omega
    have h := holds_of_mem hF hok (hmem _ (List.mem_append_right _
      (List.mem_map.mpr ⟨k - 2 ^ j, List.mem_range.mpr hk', rfl⟩)))
    simp only [Call.Holds, getD_o] at h
    rw [show pt.round j + 1 + 2 ^ j + (k - 2 ^ j) = pt.round j + 1 + k by omega] at h
    have hmod : k % 2 ^ j = k - 2 ^ j := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hk']
    have hbit : k.testBit j = true := by
      have := Nat.testBit_two_pow_add_eq (k - 2 ^ j) j
      rwa [show 2 ^ j + (k - 2 ^ j) = k by omega, Nat.testBit_lt_two_pow hk', Bool.not_false] at this
    rw [h, hmod, hbit]
    simp

theorem tbl_sem (hF : Facts cs rl os st val) (hok : callsOk cs rl (pt.calls os) = true)
    (ho : Model.ev val (pt.one os) = 1) :
    ∀ j ≤ 4, ∀ k < 2 ^ j, Model.ev val (pt.tbl os j k) = prodBits (fun i => Model.ev val (pt.aj i)) k j := by
  intro j
  induction j with
  | zero => intro _ k _; simp [PointCert.tbl, ho, prodBits]
  | succ j ih =>
    intro hj k hk
    rw [round_sem hF hok ho (by omega) k hk, ih (by omega) _ (Nat.mod_lt _ (by positivity)), prodBits, prodBits,
      Finset.prod_range_succ]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    simp [Nat.testBit_mod_two_pow, hi]

/-- The point's calls: `X + 1`, and the weights `eq(A, k)`. -/
theorem point_sem (hF : Facts cs rl os st val) (hok : callsOk cs rl (pt.calls os) = true) :
    Model.ev val (pt.x1 os) = Model.ev val pt.x + 1 ∧
      ∀ k : Fin 16, Model.ev val (pt.weight os k) = UnionSound.eqAt (fun j => Model.ev val (pt.aj j)) k := by
  have H := holds_all hF hok
  have h0 := H (pt.start, .one) (by simp [PointCert.calls])
  have h1 := H (pt.start + 1, .add pt.x (o os pt.start)) (by simp [PointCert.calls])
  have h2 := H (pt.start + 2, .one) (by simp [PointCert.calls])
  simp only [Call.Holds, getD_o] at h0 h1 h2
  refine ⟨by rw [PointCert.x1, h1, h0], fun k => ?_⟩
  have ht := tbl_sem hF hok h2 4 le_rfl k (by have := k.isLt; norm_num)
  rw [show pt.weight os k = pt.tbl os 4 k by
    simp only [PointCert.weight, PointCert.tbl, PointCert.round]; norm_num, ht, prodBits, UnionSound.eqAt,
    ← Fin.prod_univ_eq_prod_range (fun i => if (k : ℕ).testBit i then Model.ev val (pt.aj i)
      else 1 + Model.ev val (pt.aj i)) 4]

end Point

end LeanVMCircuits.Rec.Bind
