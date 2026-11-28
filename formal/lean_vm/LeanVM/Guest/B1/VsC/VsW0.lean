/-
  LeanVM.Guest.B1.VsC.VsW0

  `verify_sub`'s valuation per memory, and its first window: the `HeapBuf`s, the seed's
  permutation, the stream's chunk count and its range check, the stream's buffer.
-/

module

public import LeanVM.Guest.B1.VsC.VsEval
public import LeanVM.Guest.Memory.Retemp
public import LeanVM.Guest.Value.Bits
import LeanVM.Guest.B1.Sig.CwComplete

/-!
# The valuation per memory, and window `0`

`rdOver σ0 rd`: `σ0` with each range check's temporaries (`vsRcs`, the body's `(t, x)` pairs) read
from `rd` (`rdAt rd (σ0 x) 0`), every other value `σ0`'s: the valuation `VsWindowsA` takes per
memory. `holds_plain`: an atom whose equations read no memory and need no side condition, naming no
temporary, holds on every memory's `rdOver` from its equations on `σ0`. `holds_rc`: a range check
holds on `rdOver` from its equations on `σ0`, its operands in `K`, their words defined and the
divisor nonzero.

`vsW0_segA`: statements `0 ..< 36` (`vsW0`) are a window on `vsVal rd0 w args` and `rdOver`: its
nineteen `HeapBuf`s at the bases from `cur` (the oracle's allocation words `hwA`), the dynamic one
of `256 p` words for the stream's `p ≤ 32` chunks (`w 42 = g^p`, the honest `stream_chunks` entry),
its range check `p ≤ 32` passing on every memory defined on its first `2^k` words, `6 ≤ k`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The valuation per memory -/

/-- The range checks' temporaries of a block, each with the value whose word it reads. -/
def rcPairs : List Stmt → List (V × V)
  | [] => []
  | .atom (.rangeCheck x y t1 t2 _) :: ss => (t1, x) :: (t2, y) :: rcPairs ss
  | _ :: ss => rcPairs ss

/-- `verify_sub`'s range checks' temporaries (its branches' arms have none). -/
noncomputable def vsRcs : List (V × V) := rcPairs vsBody

/-- **`σ0` on a memory**: each range check's temporaries read from `rd`, every other value `σ0`'s. -/
noncomputable def rdOver (σ0 : Val) (rd : Reader) : Val := fun v =>
  match vsRcs.lookup v with
  | some x => rdAt rd (σ0 x) 0
  | none => σ0 v

theorem rdOver_eq {σ0 : Val} {rd : Reader} {v : V} (h : vsRcs.lookup v = none) : rdOver σ0 rd v = σ0 v := by
  simp only [rdOver, h]

theorem rdOver_tmp {σ0 : Val} {rd : Reader} {t x : V} (h : vsRcs.lookup t = some x) :
    rdOver σ0 rd t = rdAt rd (σ0 x) 0 := by
  simp only [rdOver, h]

/-- An atom whose equations read no memory and need no side condition. -/
def plainB : Atom → Bool
  | .const .. | .add .. | .copy .. | .keccak .. | .hint _ => true
  | .mul d x y => decide (x.idx < d.idx) && decide (y.idx < d.idx)
  | _ => false

/-- `plainB`, naming no range check's temporary. -/
noncomputable def plainOk (a : Atom) : Bool :=
  plainB a && (atomUses a ++ atomTmps a).all fun v => (vsRcs.lookup v).isNone

theorem good_plain {rd0 rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {a : Atom} (hp : plainB a = true)
    (h : Good rd0 S w σ a) : Good rd S w σ a := by
  cases a with
  | hint hh =>
    cases hh with
    | witness _ dd => cases dd <;> exact h
    | bits _ _ _ dd => cases dd <;> exact h
    | bitsExp _ _ dd => cases dd <;> exact h
    | digitsExp _ _ _ _ _ _ dd => cases dd <;> exact h
    | windowsExp _ _ _ _ dd => cases dd <;> exact h
    | _ => exact h
  | _ => first | exact h | simp [plainB] at hp

/-- **A plain atom holds on every memory's valuation** from its equations on `σ0`. -/
theorem holds_plain {rd0 rd : Reader} {S : List Atom} {w : ℕ → E} {σ0 : Val} {a : Atom} (hp : plainOk a = true)
    (hg : Good rd0 S w σ0 a) : a.Holds rd (rdOver σ0 rd) := by
  simp only [plainOk, Bool.and_eq_true, List.all_eq_true, Option.isNone_iff_eq_none] at hp
  rw [atom_holds_congr a (fun v hv => rdOver_eq (hp.2 v hv))]
  refine holds_of_good (good_plain hp.1 hg) ?_
  have hb := hp.1
  cases a with
  | mul d x y =>
    simp only [plainB, Bool.and_eq_true, decide_eq_true_eq] at hb
    simp only [Side]; rw [ite_pos' hb]; trivial
  | _ => trivial

/-- **A range check holds on every memory's valuation**: its temporaries read there, its operands
`σ0`'s in `K` with their words defined, the divisor nonzero when it divides. -/
theorem holds_rc {rd0 rd : Reader} {S : List Atom} {w : ℕ → E} {σ0 : Val} {x y t1 t2 k : V}
    (h1 : vsRcs.lookup t1 = some x) (h2 : vsRcs.lookup t2 = some y) (hx : vsRcs.lookup x = none)
    (hy : vsRcs.lookup y = none) (hk : vsRcs.lookup k = none) (hg : Good rd0 S w σ0 (.rangeCheck x y t1 t2 k))
    (hKx : IsInK (σ0 x)) (hKy : IsInK (σ0 y)) (hdx : (rd ((σ0 x).limb 0 * addressOfIndex 0)).isSome)
    (hdy : (rd ((σ0 y).limb 0 * addressOfIndex 0)).isSome) (hx0 : k.idx < y.idx → σ0 x ≠ 0) :
    (Atom.rangeCheck x y t1 t2 k).Holds rd (rdOver σ0 rd) := by
  have ex := rdOver_eq (σ0 := σ0) (rd := rd) hx
  have ey := rdOver_eq (σ0 := σ0) (rd := rd) hy
  have ek := rdOver_eq (σ0 := σ0) (rd := rd) hk
  refine holds_of_good (S := S) (w := w) ?_ ?_
  · refine ⟨by rw [rdOver_tmp h1, ex], by rw [rdOver_tmp h2, ey], ?_⟩
    have h3 := hg.2.2
    rw [ex, ey, ek]; exact h3
  · refine ⟨by rw [ex]; exact hKx, by rw [ex]; exact hdx, by rw [ey]; exact hKy, by rw [ey]; exact hdy, ?_⟩
    rw [ex]
    split_ifs with hh
    exact hx0 hh

/-- **A load holds on every memory's valuation** that reads its word as the evaluation's memory
`rd0` does: a load into a new value takes `rd0`'s word, which `rd` holds too. -/
theorem holds_load {rd0 rd : Reader} {S : List Atom} {w : ℕ → E} {σ0 : Val} {d p : V} {off : ℕ}
    (hd : vsRcs.lookup d = none) (hp : vsRcs.lookup p = none) (hS : Atom.load d p off ∉ S)
    (hg : Good rd0 S w σ0 (.load d p off)) (hK : IsInK (σ0 p))
    (hrd : rd ((σ0 p).limb 0 * addressOfIndex off) = rd0 ((σ0 p).limb 0 * addressOfIndex off))
    (hdef : (rd0 ((σ0 p).limb 0 * addressOfIndex off)).isSome) :
    (Atom.load d p off).Holds rd (rdOver σ0 rd) := by
  show LoadHolds rd (rdOver σ0 rd p) off (rdOver σ0 rd d)
  rw [rdOver_eq hd, rdOver_eq hp]
  have hg' : σ0 d = rdAt rd0 (σ0 p) off := (hg : Atom.load d p off ∈ S ∨ _).resolve_left hS
  refine load_of_rdAt ?_ hK (by rw [hrd]; exact hdef)
  rw [hg', rdAt, rdAt, hrd]

/-- **A store holds on every memory's valuation** that holds the stored word. -/
theorem holds_store {rd : Reader} {σ0 : Val} {d p : V} {off : ℕ} (hd : vsRcs.lookup d = none)
    (hp : vsRcs.lookup p = none) (h : LoadHolds rd (σ0 p) off (σ0 d)) :
    (Atom.load d p off).Holds rd (rdOver σ0 rd) := by
  show LoadHolds rd (rdOver σ0 rd p) off (rdOver σ0 rd d)
  rw [rdOver_eq hd, rdOver_eq hp]; exact h

/-- An atom other than a branch's `assertNe`, which `fixA` keeps. -/
def neB : Atom → Bool
  | .assertNe .. => false
  | _ => true

theorem fixA_eq {a : Atom} (h : neB a = true) : fixA a = a := by
  cases a <;> simp_all [neB, fixA]

/-- **An atom of `vsA` satisfies its equations** on the forward valuation. -/
theorem vsA_good {rd0 : Reader} {w : ℕ → E} {args : List E} (ha : args.length = 6) {a : Atom}
    (hm : Stmt.atom a ∈ vsA) (hn : neB a = true) :
    Good rd0 (storesOf 6 vsAf) w (vsVal rd0 w args) a := by
  have := vsVal_goodA (rd := rd0) (w := w) ha (fixS (.atom a)) (List.mem_map_of_mem hm)
  simp only [fixS, GoodS] at this
  rwa [fixA_eq hn] at this

theorem mem_allocDsts {as : List Atom} {v : V} (h : v ∈ allocDsts (as.map Ev.atom)) :
    ∃ a ∈ as, (∃ n, a = .hint (.alloc v n)) ∨ ∃ s, a = .hint (.allocDyn v s) := by
  simp only [allocDsts, List.mem_filterMap, List.mem_map] at h
  obtain ⟨e, ⟨a, ha, rfl⟩, he⟩ := h
  refine ⟨a, ha, ?_⟩
  cases a with
  | hint hh =>
    cases hh with
    | alloc d n => simp only [Ev.allocDst?, Option.some.injEq] at he; exact Or.inl ⟨n, by rw [he]⟩
    | allocDyn d s => simp only [Ev.allocDst?, Option.some.injEq] at he; exact Or.inr ⟨s, by rw [he]⟩
    | _ => simp [Ev.allocDst?] at he
  | _ => simp [Ev.allocDst?] at he

/-! ## Window `0` -/

/-- Statements `0 ..< 26` of `verify_sub`: the static `HeapBuf`s, the seed's permutation, the
stream's chunk count, the range check's bound. -/
def vsW0a : List Atom := [
    .hint (.alloc (.n 6) 6),
    .hint (.alloc (.n 7) 156),
    .hint (.alloc (.n 8) 24),
    .hint (.alloc (.n 9) 4),
    .hint (.alloc (.n 10) 153),
    .hint (.alloc (.n 11) 30),
    .hint (.alloc (.n 12) 24),
    .hint (.alloc (.n 13) 25),
    .hint (.alloc (.n 14) 36),
    .hint (.alloc (.n 15) 24),
    .hint (.alloc (.n 16) 6),
    .hint (.alloc (.n 17) 126),
    .hint (.alloc (.n 18) 25),
    .hint (.alloc (.n 19) 12),
    .hint (.alloc (.n 20) 78),
    .hint (.alloc (.n 21) 64),
    .hint (.alloc (.n 22) 30),
    .hint (.alloc (.n 23) 1),
    .const (.n 24) (word 1 0),
    .const (.n 25) (word 0 0),
    .const (.n 26) (word 0 0),
    .const (.n 27) (word 0 0),
    .const (.n 28) (word 0 0),
    .keccak [.n 2, .n 3, .n 0, .n 1, .n 25, .n 26, .n 27, .n 28, .n 25, .n 25, .n 26, .n 27, .n 28] [.n 29, .n 30, .n 31, .n 32, .n 33, .n 34, .n 35, .n 36, .n 37, .n 38, .n 39, .n 40, .n 41] false false,
    .hint (.witness "stream_chunks" (.stack [.n 42])),
    .const (.n 43) (word 4294967296 0)]

/-- The range check `p ≤ 32` on the stream's chunk count `g^p`. -/
def vsW0rc : Atom := .rangeCheck (.n 42) (.n 44) (.n 45) (.n 46) (.n 43)

/-- Statements `27 ..< 36`: the stream's size `g^(256 p)` and its `HeapBuf`. -/
def vsW0b : List Atom := [
    .mul (.n 47) (.n 42) (.n 42),
    .mul (.n 48) (.n 47) (.n 47),
    .mul (.n 49) (.n 48) (.n 48),
    .mul (.n 50) (.n 49) (.n 49),
    .mul (.n 51) (.n 50) (.n 50),
    .mul (.n 52) (.n 51) (.n 51),
    .mul (.n 53) (.n 52) (.n 52),
    .mul (.n 54) (.n 53) (.n 53),
    .hint (.allocDyn (.n 55) (.n 54))]

/-- **Window `0`**: statements `0 ..< 36`. -/
def vsW0 : List Atom := vsW0a ++ [vsW0rc] ++ vsW0b

set_option maxRecDepth 100000 in
theorem vsW0_eq : vsA.take 36 = vsW0.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem vsW0a_ok : vsW0a.all plainOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vsW0b_ok : vsW0b.all plainOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vsW0_rcs : vsRcs.lookup (.n 45) = some (.n 42) ∧ vsRcs.lookup (.n 46) = some (.n 44) ∧
    vsRcs.lookup (.n 42) = none ∧ vsRcs.lookup (.n 44) = none ∧ vsRcs.lookup (.n 43) = none ∧
    vsRcs.lookup (.n 54) = none := by decide +kernel

/-- The static `HeapBuf` sizes of window `0`, in order. -/
def vsSz0 : List ℕ := [6, 156, 24, 4, 153, 30, 24, 25, 36, 24, 6, 126, 25, 12, 78, 64, 30, 1]

theorem vsW0_allocs (σ : Val) : allocs σ (vsW0.map Ev.atom) = vsSz0 ++ [logG (σ (.n 54))] := rfl

theorem vsW0_addrs : addrs (vsW0.map Ev.atom) = [] := rfl

theorem vsW0_loadAddrs (σ : Val) : loadAddrs σ (vsW0.map Ev.atom) = [] := rfl

theorem vsW0_hintAddrs (σ : Val) : heapHintAddrs σ (vsW0.map Ev.atom) = [] := rfl

theorem vsW0_allocDsts : (allocDsts (vsW0.map Ev.atom)).map V.idx =
    [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 55] := rfl

section
variable {rd0 : Reader} {w : ℕ → E} {args : List E}

theorem vsW0_good (ha : args.length = 6) {a : Atom} (hm : a ∈ vsW0) :
    Good rd0 (storesOf 6 vsAf) w (vsVal rd0 w args) a := by
  have hA : Stmt.atom a ∈ vsA := List.mem_of_mem_take (by rw [vsW0_eq]; exact List.mem_map_of_mem hm)
  refine vsA_good ha hA ?_
  simp only [vsW0, List.mem_append, List.mem_singleton] at hm
  rcases hm with (hm | rfl) | hm
  · have := List.all_eq_true.mp vsW0a_ok a hm
    cases a <;> simp_all [plainOk, plainB, neB]
  · rfl
  · have := List.all_eq_true.mp vsW0b_ok a hm
    cases a <;> simp_all [plainOk, plainB, neB]

/-- The stream's size word: `(g^p)^(2^8)`. -/
theorem vsW0_54 (ha : args.length = 6) {p : ℕ} (hw42 : w 42 = gen ^ p) :
    vsVal rd0 w args (.n 54) = gen ^ (256 * p) := by
  have hmem : ∀ a ∈ vsW0b, a ∈ vsW0 := fun a h => by simp [vsW0, h]
  have m : ∀ d x : ℕ, Atom.mul (.n d) (.n x) (.n x) ∈ vsW0b → x < d →
      vsVal rd0 w args (.n d) = vsVal rd0 w args (.n x) * vsVal rd0 w args (.n x) := fun d x h hl =>
    good_mul_eq (vsW0_good ha (hmem _ h)) hl hl
  have h42 : vsVal rd0 w args (.n 42) = gen ^ p := by
    have := vsW0_good (rd0 := rd0) (w := w) ha (a := .hint (.witness "stream_chunks" (.stack [.n 42])))
      (by simp [vsW0, vsW0a])
    simp only [Good, List.mem_singleton, forall_eq] at this
    rw [this]; exact hw42
  rw [m 54 53 (by simp [vsW0b]) (by norm_num), m 53 52 (by simp [vsW0b]) (by norm_num),
    m 52 51 (by simp [vsW0b]) (by norm_num), m 51 50 (by simp [vsW0b]) (by norm_num),
    m 50 49 (by simp [vsW0b]) (by norm_num), m 49 48 (by simp [vsW0b]) (by norm_num),
    m 48 47 (by simp [vsW0b]) (by norm_num), m 47 42 (by simp [vsW0b]) (by norm_num), h42]
  ring

end

/-- **Window `0`**: on the forward valuation whose oracle gives the `HeapBuf`s their bases from
`cur` and the stream `p ≤ 32` chunks, statements `0 ..< 36` are a window placing `824 + 256 p`
words from `cur`, entering no callee, on every memory defined on its first `2^k` words. -/
theorem vsW0_segA {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} (hk : 6 ≤ k)
    {rd0 : Reader} {w : ℕ → E} {args : List E} (ha : args.length = 6) {p cur fp kc : ℕ} (hp : p ≤ 32)
    (hw42 : w 42 = gen ^ p)
    (hwA : [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 55].map w =
      (bases cur (vsSz0 ++ [256 * p])).map (fun b => ofK (addressOfIndex b)))
    {f : String} {Own R : ℕ → Prop} {Pre O : Reader → Prop} {D : ℕ → Prop} :
    SegA (fs := fs) (al := al) (cert := cert) k f fp (vsVal rd0 w args) (rdOver (vsVal rd0 w args)) Own R Pre
      (vsW0.map Stmt.atom) (vsW0.map Ev.atom) cur (cur + (824 + 256 * p)) kc kc O O D D [] := by
  obtain ⟨r45, r46, r42, r44, r43, r54⟩ := vsW0_rcs
  have h54 := vsW0_54 (rd0 := rd0) (w := w) ha hw42
  have hlog : logG ((vsVal rd0 w args) (.n 54)) = 256 * p := by
    rw [h54, Value.gen_pow_eq_ofK, logG_spec (by omega)]
  have hal : allocs (vsVal rd0 w args) (vsW0.map Ev.atom) = vsSz0 ++ [256 * p] := by rw [vsW0_allocs, hlog]
  have hsum : (allocs (vsVal rd0 w args) (vsW0.map Ev.atom)).sum = 824 + 256 * p := by rw [hal, List.sum_append, List.sum_singleton]; rfl
  rw [← hsum]
  refine segA_atoms fun rd hl _ _ => ⟨?_, ?_, by intro q hq; rw [vsW0_addrs] at hq; simp at hq,
    by intro A hA; rw [vsW0_loadAddrs] at hA; simp at hA,
    by intro A hA; rw [vsW0_hintAddrs] at hA; simp at hA, ?_⟩
  · rw [vsW0_allocs, vsW0_allocs, rdOver_eq r54]
  · -- the HeapBuf pointers: the oracle's words
    have hv : ∀ v ∈ allocDsts (vsW0.map Ev.atom), rdOver (vsVal rd0 w args) rd v = w v.idx := by
      intro v hv
      obtain ⟨a, ha', hk'⟩ := mem_allocDsts hv
      have hg := vsW0_good (rd0 := rd0) (w := w) ha ha'
      have hok : plainOk a = true := by
        rcases hk' with ⟨n, rfl⟩ | ⟨s, rfl⟩ <;>
          (simp only [vsW0, List.mem_append, List.mem_singleton] at ha'
           rcases ha' with (ha' | ha') | ha'
           · exact List.all_eq_true.mp vsW0a_ok _ ha'
           · simp [vsW0rc] at ha'
           · exact List.all_eq_true.mp vsW0b_ok _ ha')
      have hlk : vsRcs.lookup v = none := by
        simp only [plainOk, Bool.and_eq_true, List.all_eq_true, Option.isNone_iff_eq_none] at hok
        rcases hk' with ⟨n, rfl⟩ | ⟨s, rfl⟩ <;> exact hok.2 v (by simp [atomUses, hintUses])
      rw [rdOver_eq hlk]
      rcases hk' with ⟨n, rfl⟩ | ⟨s, rfl⟩ <;> exact hg
    rw [List.map_congr_left hv, hal]
    have e : (allocDsts (vsW0.map Ev.atom)).map (fun v => w v.idx) =
        [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 55].map w := by
      rw [← vsW0_allocDsts, List.map_map]; rfl
    rw [e, hwA]
  · -- every atom holds
    intro a hm
    simp only [vsW0, List.mem_append, List.mem_singleton] at hm
    rcases hm with (hm | rfl) | hm
    · exact holds_plain (List.all_eq_true.mp vsW0a_ok a hm) (vsW0_good ha (by simp [vsW0, hm]))
    · have hg := vsW0_good (rd0 := rd0) (w := w) (args := args) ha (a := vsW0rc) (by simp [vsW0])
      have h42 : (vsVal rd0 w args) (.n 42) = gen ^ p := by
        have := vsW0_good (rd0 := rd0) (w := w) ha (a := .hint (.witness "stream_chunks" (.stack [.n 42])))
          (by simp [vsW0, vsW0a])
        simp only [Good, List.mem_singleton, forall_eq] at this
        rw [this]; exact hw42
      have h43 : (vsVal rd0 w args) (.n 43) = gen ^ 32 := by
        have := vsW0_good (rd0 := rd0) (w := w) ha (a := .const (.n 43) (word 4294967296 0))
          (by simp [vsW0, vsW0a])
        simp only [Good] at this
        rw [this, show (4294967296 : ℕ) = 2 ^ 32 from rfl, B1.Sig.word_two_pow_eq (by norm_num),
          Value.gen_pow_eq_ofK]
      have h44 : (vsVal rd0 w args) (.n 44) = gen ^ (32 - p) := by
        have := hg.2.2
        simp only [show (V.n 43).idx < (V.n 44).idx from by decide, ↓reduceIte] at this
        rw [this, h43, h42, pow_sub₀ _ Value.gen_ne_zero hp]
      have hdef : ∀ m, m ≤ 32 → (rd ((gen ^ m).limb 0 * addressOfIndex 0)).isSome := by
        intro m hm'
        have e : (gen ^ m).limb 0 * addressOfIndex 0 = addressOfIndex m := by
          rw [Value.gen_pow_eq_ofK]; simp
        rw [e]
        exact hl m (lt_of_le_of_lt hm' (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)))
      refine holds_rc r45 r46 r42 r44 r43 hg ?_ ?_ ?_ ?_ ?_
      · rw [h42, Value.gen_pow_eq_ofK]; exact Value.ofK_isInK _
      · rw [h44, Value.gen_pow_eq_ofK]; exact Value.ofK_isInK _
      · rw [h42]; exact hdef p hp
      · rw [h44]; exact hdef (32 - p) (by omega)
      · intro _; rw [h42]; exact pow_ne_zero _ Value.gen_ne_zero
    · exact holds_plain (List.all_eq_true.mp vsW0b_ok a hm) (vsW0_good ha (by simp [vsW0, hm]))

end
end LeanVM.Guest.B1.VsC
