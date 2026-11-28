/-
  LeanVM.Guest.B1.VsC.CertifyF

  `certify_stack`'s segments under forward evaluation: each atom holds.
-/

module

public import LeanVM.Guest.B1.VsC.CertifyH
public import LeanVM.Guest.B1.VsC.ColSelC

/-!
# `certify_stack`'s segments, evaluated forward

On a valuation satisfying each atom's defining equations (`Good`, as the forward evaluation does),
with its fresh loads no stores (`FreshOk`, what the kernel checks of the body by `freshShape`), each
segment of `csBody` holds atom by atom, given the words its stores write and its loads read:
`csKey_fwd` (a group's key and size), `csRank0_fwd`, `csRank_fwd` (the ranks), `csOut_fwd` (a
group's outputs). Each also says where its loads read (`csKey_loads`, ...).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Stack LeanVM.Guest.B1.Whir LeanVM.Guest.B1.Fwd LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Atoms by their equations -/

/-- A load of this shape in `csBody` is no store. -/
def freshShape (d p : ℕ) : Bool := d == p + 1 || p == 0 || p == 163 || (p == 164 && decide (p < d))

/-- The fresh loads of a segment are no stores. -/
def FreshOk (S : List Atom) (ss : List Stmt) : Prop :=
  ∀ d p off, Stmt.atom (.load (.n d) (.n p) off) ∈ ss → freshShape d p = true → Atom.load (.n d) (.n p) off ∉ S

theorem FreshOk.sub {S : List Atom} {ss ts : List Stmt} (h : FreshOk S ts) (hs : ∀ s ∈ ss, s ∈ ts) :
    FreshOk S ss := fun d p off hm hf => h d p off (hs _ hm) hf

variable {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

theorem good_const {d : V} {c : E} (h : Good rd S w σ (.const d c)) : σ d = c := h

theorem good_mul {d a b : ℕ} (h : Good rd S w σ (.mul (.n d) (.n a) (.n b))) (ha : a < d) (hb : b < d) :
    σ (.n d) = σ (.n a) * σ (.n b) := good_mul_eq h ha hb

/-- A fresh load reading a known word: its value, and it holds. -/
theorem good_fresh {d p off : ℕ} {v : E} (h : Good rd S w σ (.load (.n d) (.n p) off))
    (hS : Atom.load (.n d) (.n p) off ∉ S) (hv : LoadHolds rd (σ (.n p)) off v) :
    σ (.n d) = v ∧ (Atom.load (.n d) (.n p) off).Holds rd σ := by
  have := good_load_eq hv h hS
  exact ⟨this, by show LoadHolds rd (σ (.n p)) off (σ (.n d)); rw [this]; exact hv⟩

/-- A range check of `g^e` against `g^K`, `e ≤ K < 2^k`, its quotient fresh, holds. -/
theorem good_rcK {k : ℕ} (hl : LowDef k rd) {x y t1 t2 b : ℕ} {e K : ℕ} (he : e ≤ K) (hK : K < 2 ^ k)
    (hx : σ (.n x) = gen ^ e) (hb : σ (.n b) = gen ^ K) (hby : b < y)
    (hg : Good rd S w σ (.rangeCheck (.n x) (.n y) (.n t1) (.n t2) (.n b))) :
    (Atom.rangeCheck (.n x) (.n y) (.n t1) (.n t2) (.n b)).Holds rd σ := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hlt : (V.n b).idx < (V.n y).idx := hby
  simp only [hlt, ↓reduceIte] at h3
  have hy : σ (.n y) = gen ^ (K - e) := by
    rw [h3, hb, hx, show K = (K - e) + e by omega, pow_add, mul_inv_cancel_right₀ (gen_pow_ne_zero e),
      Nat.add_sub_cancel]
  have lx := loadHolds_low hl (i := e) (by omega)
  have ly := loadHolds_low hl (i := K - e) (by omega)
  rw [← gen_pow_eq_ofK] at lx ly
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, hx, rdAt_of_load lx]; exact lx
  · rw [hy, hb, hx, ← pow_add, Nat.add_sub_cancel' he]
  · rw [h2, hy, rdAt_of_load ly]; exact ly

/-- The square-and-multiply chain's atoms are products into fresh values. -/
theorem osPowSteps_fresh (x : ℕ) : ∀ (ds : List Bool) (acc k : ℕ), acc < k → x < k →
    ∀ s ∈ (osPowSteps x ds acc k).1, ∃ d a b, s = osMul d a b ∧ a < d ∧ b < d ∧ k ≤ d
  | [], _, _, _, _ => fun s hs => absurd hs List.not_mem_nil
  | d :: ds, acc, k, ha, hx => by
    cases d with
    | true =>
      intro s hs
      simp only [osPowSteps, ↓reduceIte, List.mem_cons] at hs
      rcases hs with rfl | rfl | hs
      · exact ⟨k, acc, acc, rfl, ha, ha, le_rfl⟩
      · exact ⟨k + 1, k, x, rfl, by omega, by omega, by omega⟩
      · obtain ⟨d', a', b', e, h1, h2, h3⟩ := osPowSteps_fresh x ds (k + 1) (k + 2) (by omega) (by omega) s hs
        exact ⟨d', a', b', e, h1, h2, by omega⟩
    | false =>
      intro s hs
      simp only [osPowSteps, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact ⟨k, acc, acc, rfl, ha, ha, le_rfl⟩
      · obtain ⟨d', a', b', e, h1, h2, h3⟩ := osPowSteps_fresh x ds k (k + 1) (by omega) (by omega) s hs
        exact ⟨d', a', b', e, h1, h2, by omega⟩

/-- A chain whose atoms satisfy their equations holds. -/
theorem osPowSteps_allOk {C : CallRel} (x : ℕ) (ds : List Bool) (acc k : ℕ) (ha : acc < k) (hx : x < k)
    (hG : ∀ a, Stmt.atom a ∈ (osPowSteps x ds acc k).1 → Good rd S w σ a) :
    AllOk C rd σ (osPowSteps x ds acc k).1 := by
  intro s hs
  obtain ⟨d, a, b, rfl, h1, h2, -⟩ := osPowSteps_fresh x ds acc k ha hx s hs
  exact good_mul (hG _ hs) h1 h2

theorem osPowSteps_ge (x : ℕ) : ∀ (ds : List Bool) (acc k : ℕ), acc < k →
    (osPowSteps x ds acc k).2 = acc ∨ k ≤ (osPowSteps x ds acc k).2
  | [], _, _, _ => Or.inl rfl
  | d :: ds, acc, k, ha => by
    cases d with
    | true =>
      simp only [osPowSteps, ↓reduceIte]
      rcases osPowSteps_ge x ds (k + 1) (k + 2) (by omega) with h | h <;> right <;> omega
    | false =>
      simp only [osPowSteps, Bool.false_eq_true, ↓reduceIte]
      rcases osPowSteps_ge x ds k (k + 1) (by omega) with h | h <;> right <;> omega

/-! ## A group's key and size -/

/-- Group `gi`'s rank key, as `certify_stack` computes it: `κ^53·g^(-b0)`. -/
def csKeyW (kv : ℕ → ℕ) (gi : ℕ) : E :=
  if (csG gi).b0 = 0 then (gen ^ csKap kv gi) ^ 53 else (gen ^ csKap kv gi) ^ 53 * word (csG gi).inv 0

theorem osPowDigits53 : osPowDigits 53 = [true, false, true, false, true] := by decide

theorem osPowLen53 : osPowLen 53 = 8 := by decide

theorem csKappa_shape (g : CsGroup) (s : ℕ) :
    (g.adj = 0 ∧ (csKappa g s).1 = [] ∧ (csKappa g s).2.1 = 2 + g.src ∧ (csKappa g s).2.2 = s) ∨
      (g.adj ≠ 0 ∧ (csKappa g s).1 = [osCst s (csW g.adj), osMul (s + 1) (2 + g.src) s] ∧
        (csKappa g s).2.1 = s + 1 ∧ (csKappa g s).2.2 = s + 2) := by
  unfold csKappa
  by_cases h : g.adj = 0
  · exact Or.inl ⟨h, by simp [h]⟩
  · exact Or.inr ⟨h, by simp [h]⟩

/-- A group's `κ` under its equations. -/
theorem csKappa_fwd {kv : ℕ → ℕ} (hkb : ∀ i < 8, σ (.n (2 + i)) = gen ^ kv i) {g : CsGroup}
    (hsrc : g.src < 8) (hadj : g.adj < 64) {s : ℕ} (hs : 10 ≤ s)
    (hG : ∀ a, Stmt.atom a ∈ (csKappa g s).1 → Good rd S w σ a) :
    (∀ a, Stmt.atom a ∈ (csKappa g s).1 → a.Holds rd σ) ∧
      σ (.n (csKappa g s).2.1) = gen ^ (kv g.src + g.adj) := by
  have hall : ∀ a, Stmt.atom a ∈ (csKappa g s).1 → a.Holds rd σ := by
    intro a ha
    rcases csKappa_shape g s with ⟨-, h1, -, -⟩ | ⟨-, h1, -, -⟩
    · rw [h1] at ha; exact absurd ha List.not_mem_nil
    · have hg := hG a ha
      rw [h1] at ha
      simp only [osCst, osMul, List.mem_cons, Stmt.atom.injEq, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact hg
      · exact good_mul hg (by omega) (by omega)
  exact ⟨hall, csKappa_val (C := fun _ _ _ => True) (rd := rd) kv hkb hsrc hadj s fun st hst => by
    rcases csKappa_shape g s with ⟨-, h1, -, -⟩ | ⟨-, h1, -, -⟩
    · rw [h1] at hst; exact absurd hst List.not_mem_nil
    · rw [h1] at hst
      simp only [osCst, osMul, List.mem_cons, List.not_mem_nil, or_false] at hst
      rcases hst with rfl | rfl
      · exact hall _ (by rw [h1]; exact List.mem_cons_self)
      · exact hall _ (by rw [h1]; exact List.mem_cons_of_mem _ List.mem_cons_self)⟩

/-- **Group `gi`'s key and size, evaluated forward**: every atom holds where the memory has the
key at `group_key[gi]`, the size at `group_size[gi]` and the exponent table at `σ 1`; its loads
read those two words and the table at `g^κ`. -/
theorem csKey_fwd {k : ℕ} (hk : 6 ≤ k) (hl : LowDef k rd) {kv : ℕ → ℕ}
    (hkb : ∀ i < 8, σ (.n (2 + i)) = gen ^ kv i) (ht : ExpTables rd (σ (.n 1)))
    {gi : ℕ} (hgi : gi < 8) (hκ : csKap kv gi ≤ 33) {s : ℕ} (hs : 12 ≤ s)
    (hG : ∀ a, Stmt.atom a ∈ (csKey gi s).1 → Good rd S w σ a) (hF : FreshOk S (csKey gi s).1)
    (hkey : LoadHolds rd (σ (.n 10)) gi (csKeyW kv gi))
    (hsz : LoadHolds rd (σ (.n 11)) gi (gen ^ csSize kv gi)) :
    (∀ a, Stmt.atom a ∈ (csKey gi s).1 → a.Holds rd σ) ∧
      ∀ d p off, Stmt.atom (.load d p off) ∈ (csKey gi s).1 →
        (p = .n 10 ∧ off = gi) ∨ (p = .n 11 ∧ off = gi) ∨ (σ p = σ (.n 1) * gen ^ csKap kv gi ∧ off = 0) := by
  obtain ⟨hsrc, hadj, hl1, hl14, hdig⟩ := csGroups_facts gi hgi
  set g := csG gi with hgdef
  set kp := csKappa g s with hkpdef
  have hkp_idx : kp.2.1 < kp.2.2 ∧ s ≤ kp.2.2 ∧ kp.2.2 ≤ s + 2 ∧ 2 ≤ kp.2.1 := by
    rcases csKappa_shape g s with ⟨-, -, h2, h3⟩ | ⟨-, -, h2, h3⟩ <;> rw [hkpdef, h2, h3] <;> omega
  set v := kp.2.1 with hvdef
  set s' := kp.2.2 with hs'def
  set ch := osPowSteps v (osPowDigits 53) v (s' + 4) with hchdef
  have hch2 : ch.2 = s' + 11 := by rw [hchdef, osPowDigits53]; simp [osPowSteps]
  set m := (if g.b0 = 0 then s' + 4 + osPowLen 53 else s' + 6 + osPowLen 53) with hmdef
  set kd := (if g.b0 = 0 then ch.2 else s' + 5 + osPowLen 53) with hkddef
  set kst : List Stmt := (if g.b0 = 0 then [] else [osCst (s' + 4 + osPowLen 53) (word g.inv 0),
    osMul (s' + 5 + osPowLen 53) ch.2 (s' + 4 + osPowLen 53)]) with hkstdef
  set sz := osPowSteps (m + 1) (osPowDigits g.len) (m + 1) (m + 2) with hszdef
  have hbody : (csKey gi s).1 = kp.1 ++ [osCst s' (csW 33), csRc v (s' + 1) s'] ++ ch.1 ++ kst ++
      [.atom (.load (.n kd) (.n 10) gi), osMul m 1 v, .atom (.load (.n (m + 1)) (.n m) 0)] ++ sz.1 ++
        [.atom (.load (.n sz.2) (.n 11) gi)] := by
    simp only [hkstdef, hkddef, hmdef, hszdef, hchdef, hs'def, hvdef, hkpdef, hgdef]
    unfold csKey
    by_cases hb : (csG gi).b0 = 0 <;> simp only [hb, ↓reduceIte, List.append_assoc, List.cons_append,
      List.nil_append]
  rw [hbody] at hG hF ⊢
  have hm : m ≥ s' + 12 := by rw [hmdef, osPowLen53]; split <;> omega
  -- the values
  have hGk : ∀ a, Stmt.atom a ∈ kp.1 → Good rd S w σ a := fun a ha => hG a (by simp [ha])
  obtain ⟨hkA, hv⟩ := csKappa_fwd hkb hsrc (by omega) (by omega) hGk
  rw [← hkpdef, ← hvdef] at hv
  have hv' : σ (.n v) = gen ^ csKap kv gi := hv
  have hc33 : σ (.n s') = gen ^ 33 := by
    rw [good_const (hG (.const (.n s') (csW 33)) (by simp)), csW_eq (by decide)]
  have hchA : AllOk (fun _ _ _ => True) rd σ ch.1 :=
    osPowSteps_allOk v _ v (s' + 4) (by omega) (by omega) fun a ha => hG a (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ha)))))
  have hchv : σ (.n ch.2) = (gen ^ csKap kv gi) ^ 53 := by
    have := osPowSteps_val (C := fun _ _ _ => True) (rd := rd) (σ := σ) v (osPowDigits 53) v (s' + 4) 1
      (by rw [pow_one]) hchA
    rw [digits53, hv'] at this; exact this
  have hkdv : σ (.n kd) = csKeyW kv gi := by
    rw [hkddef, csKeyW]
    by_cases hb : g.b0 = 0
    · rw [ite_pos' hb, ite_pos' hb]; exact hchv
    · rw [ite_neg' hb, ite_neg' hb]
      have e1 := good_const (hG (.const (.n (s' + 4 + osPowLen 53)) (word g.inv 0)) (by simp [hkstdef, hb]))
      have e2 := good_mul (hG (.mul (.n (s' + 5 + osPowLen 53)) (.n ch.2) (.n (s' + 4 + osPowLen 53)))
        (by simp [hkstdef, hb])) (by rw [hch2, osPowLen53]; omega) (by omega)
      rw [e2, hchv, e1]
  have hmv : σ (.n m) = σ (.n 1) * gen ^ csKap kv gi := by
    rw [good_mul (hG (.mul (.n m) (.n 1) (.n v)) (by simp)) (by omega) (by omega), hv']
  have hsq : LoadHolds rd (σ (.n m)) 0 (gen ^ 2 ^ csKap kv gi) := by
    rw [hmv, loadHolds_mul_gen_pow, Nat.add_zero]; exact ht.1 _ (by show _ < 34; omega)
  obtain ⟨hsqv, hsqH⟩ := good_fresh (hG (.load (.n (m + 1)) (.n m) 0) (by simp)) (hF (m + 1) m 0 (by simp) (by simp [freshShape])) hsq
  have hszA : AllOk (fun _ _ _ => True) rd σ sz.1 :=
    osPowSteps_allOk (m + 1) _ (m + 1) (m + 2) (by omega) (by omega) fun a ha =>
      hG a (List.mem_append_left _ (List.mem_append_right _ ha))
  have hszv : σ (.n sz.2) = gen ^ csSize kv gi := by
    have := osPowSteps_val (C := fun _ _ _ => True) (rd := rd) (σ := σ) (m + 1) (osPowDigits g.len) (m + 1)
      (m + 2) 1 (by rw [pow_one]) hszA
    rw [hdig, hsqv, ← pow_mul] at this
    rw [this, csSize, Nat.mul_comm]
  refine ⟨fun a ha => ?_, fun d p off ha => ?_⟩
  · have hg := hG a ha
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ((((((ha | ha | ha) | ha) | ha) | ha | ha | ha) | ha) | ha)
    · exact hkA a ha
    · cases ha; exact hg
    · cases ha
      exact good_rcK hl (e := csKap kv gi) (K := 33) hκ
        (lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) hk)) hv' hc33 (by omega) hg
    · exact hchA _ ha
    · rw [hkstdef] at ha
      by_cases hb : g.b0 = 0
      · rw [ite_pos' hb] at ha; exact absurd ha List.not_mem_nil
      · rw [ite_neg' hb] at ha
        simp only [osCst, osMul, List.mem_cons, Stmt.atom.injEq, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact hg
        · exact good_mul hg (by rw [hch2, osPowLen53]; omega) (by omega)
    · cases ha; show LoadHolds rd (σ (.n 10)) gi (σ (.n kd)); rw [hkdv]; exact hkey
    · cases ha; exact good_mul hg (by omega) (by omega)
    · cases ha; exact hsqH
    · exact hszA _ ha
    · cases ha; show LoadHolds rd (σ (.n 11)) gi (σ (.n sz.2)); rw [hszv]; exact hsz
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ((((((ha | ha | ha) | ha) | ha) | ha | ha | ha) | ha) | ha)
    · rcases csKappa_shape g s with ⟨-, h1, -, -⟩ | ⟨-, h1, -, -⟩
      · rw [h1] at ha; exact absurd ha List.not_mem_nil
      · rw [h1] at ha; simp [osCst, osMul] at ha
    · cases ha
    · cases ha
    · obtain ⟨_, _, _, h, -⟩ := osPowSteps_fresh v _ v (s' + 4) (by omega) (by omega) _ ha; cases h
    · rw [hkstdef] at ha
      by_cases hb : g.b0 = 0
      · rw [ite_pos' hb] at ha; exact absurd ha List.not_mem_nil
      · rw [ite_neg' hb] at ha; simp [osCst, osMul] at ha
    · cases ha; exact Or.inl ⟨rfl, rfl⟩
    · cases ha
    · cases ha; exact Or.inr (Or.inr ⟨hmv, rfl⟩)
    · obtain ⟨_, _, _, h, -⟩ := osPowSteps_fresh (m + 1) _ (m + 1) (m + 2) (by omega) (by omega) _ ha; cases h
    · cases ha; exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-! ## The ranks -/

/-- Rank `0`'s statements. -/
def csRank0L (s0 : ℕ) : List Stmt :=
  [.atom (.load (.n s0) (.n 163) 0), osCst (s0 + 1) (csW 7), csRc s0 (s0 + 2) (s0 + 1),
    osMul (s0 + 5) 10 s0, .atom (.load (.n (s0 + 6)) (.n (s0 + 5)) 0), osCst (s0 + 7) (word 1 0),
    osMul (s0 + 8) 164 s0, .atom (.load (.n (s0 + 7)) (.n (s0 + 8)) 0), osMul (s0 + 9) 11 s0,
    .atom (.load (.n (s0 + 10)) (.n (s0 + 9)) 0)]

theorem csRanks_eq (s0 : ℕ) : csRanks 163 164 s0 = csRank0L s0 ++
    ((List.range 7).map fun r ↦
      csRank 163 164 (s0 + 11 + 18 * r) (if r = 0 then s0 + 6 else s0 + 11 + 18 * (r - 1) + 6)
        (if r = 0 then s0 + 10 else s0 + 11 + 18 * (r - 1) + 17) (r + 1)).flatten := rfl

/-- **Rank `0`, evaluated forward**: its group `ρ` read from the order, the group's key and size
read, `group_at[ρ] = 1` stored. -/
theorem csRank0_fwd {k : ℕ} (hk : 3 ≤ k) (hl : LowDef k rd) {s0 ρ : ℕ} (hs0 : 165 ≤ s0) (hρ : ρ < 8)
    (hG : ∀ a, Stmt.atom a ∈ csRank0L s0 → Good rd S w σ a) (hF : FreshOk S (csRank0L s0))
    {key size : E} (hord : LoadHolds rd (σ (.n 163)) 0 (gen ^ ρ))
    (hkey : LoadHolds rd (σ (.n 10)) ρ key) (hat : LoadHolds rd (σ (.n 164)) ρ 1)
    (hsz : LoadHolds rd (σ (.n 11)) ρ size) :
    (∀ a, Stmt.atom a ∈ csRank0L s0 → a.Holds rd σ) ∧ σ (.n (s0 + 6)) = key ∧ σ (.n (s0 + 10)) = size ∧
      ∀ d p off, Stmt.atom (.load d p off) ∈ csRank0L s0 →
        (p = .n 163 ∧ off = 0) ∨ (σ p = σ (.n 10) * gen ^ ρ ∧ off = 0) ∨
          (σ p = σ (.n 164) * gen ^ ρ ∧ off = 0) ∨ (σ p = σ (.n 11) * gen ^ ρ ∧ off = 0) := by
  obtain ⟨v0, h0⟩ := good_fresh (hG (.load (.n s0) (.n 163) 0) (by simp [csRank0L]))
    (hF s0 163 0 (by simp [csRank0L]) (by simp [freshShape])) hord
  have v1 : σ (.n (s0 + 1)) = gen ^ 7 := by
    rw [good_const (hG (.const (.n (s0 + 1)) (csW 7)) (by simp [csRank0L, osCst])), csW_eq (by decide)]
  have v5 : σ (.n (s0 + 5)) = σ (.n 10) * gen ^ ρ := by
    rw [good_mul (hG (.mul (.n (s0 + 5)) (.n 10) (.n s0)) (by simp [csRank0L, osMul])) (by omega) (by omega), v0]
  obtain ⟨v6, h6⟩ := good_fresh (hG (.load (.n (s0 + 6)) (.n (s0 + 5)) 0) (by simp [csRank0L]))
    (hF _ _ 0 (by simp [csRank0L]) (by simp [freshShape])) (by rw [v5, loadHolds_mul_gen_pow]; exact hkey)
  have v7 : σ (.n (s0 + 7)) = 1 := by
    rw [good_const (hG (.const (.n (s0 + 7)) (word 1 0)) (by simp [csRank0L, osCst])), word_one]
  have v8 : σ (.n (s0 + 8)) = σ (.n 164) * gen ^ ρ := by
    rw [good_mul (hG (.mul (.n (s0 + 8)) (.n 164) (.n s0)) (by simp [csRank0L, osMul])) (by omega) (by omega), v0]
  have v9 : σ (.n (s0 + 9)) = σ (.n 11) * gen ^ ρ := by
    rw [good_mul (hG (.mul (.n (s0 + 9)) (.n 11) (.n s0)) (by simp [csRank0L, osMul])) (by omega) (by omega), v0]
  obtain ⟨v10, h10⟩ := good_fresh (hG (.load (.n (s0 + 10)) (.n (s0 + 9)) 0) (by simp [csRank0L]))
    (hF _ _ 0 (by simp [csRank0L]) (by simp [freshShape])) (by rw [v9, loadHolds_mul_gen_pow]; exact hsz)
  refine ⟨fun a ha => ?_, v6, v10, fun d p off ha => ?_⟩
  · have hg := hG a ha
    simp only [csRank0L, osCst, osMul, csRc, List.mem_cons, Stmt.atom.injEq, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact hg
    · exact good_rcK hl (e := ρ) (K := 7) (by omega) (lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right
        (by decide) hk)) v0 v1 (by omega) hg
    · exact good_mul hg (by omega) (by omega)
    · exact h6
    · exact hg
    · exact good_mul hg (by omega) (by omega)
    · show LoadHolds rd (σ (.n (s0 + 8))) 0 (σ (.n (s0 + 7)))
      rw [v8, v7, loadHolds_mul_gen_pow]; exact hat
    · exact good_mul hg (by omega) (by omega)
    · exact h10
  · simp only [csRank0L, osCst, osMul, csRc, List.mem_cons, Stmt.atom.injEq, Atom.load.injEq,
      List.not_mem_nil, or_false, reduceCtorEq, false_or] at ha
    rcases ha with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨v5, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨v8, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨v9, rfl⟩))

/-- **Rank `r ≥ 1`, evaluated forward**: its group `ρ` read from the order, its key under the
previous one by `g^(e + 1)`, `e < 1802`, the running total stored at `group_at[ρ]`, the total times
the group's size. -/
theorem csRank_fwd {k : ℕ} (hk : 11 ≤ k) (hl : LowDef k rd) {s pk tot r ρ : ℕ} (hs : 176 ≤ s) (hpk : pk < s)
    (htot : tot < s) (hρ : ρ < 8)
    (hG : ∀ a, Stmt.atom a ∈ csRank 163 164 s pk tot r → Good rd S w σ a)
    (hF : FreshOk S (csRank 163 164 s pk tot r))
    {key size T : E} {N1 N2 : ℕ} (hord : LoadHolds rd (σ (.n 163)) r (gen ^ ρ))
    (hkey : LoadHolds rd (σ (.n 10)) ρ key) (hkc : key * gen ^ 52 = gen ^ N2)
    (hpkv : σ (.n pk) * gen ^ 52 = gen ^ N1) (hN : N2 < N1) (hN' : N1 < N2 + 1 + 1802)
    (htotv : σ (.n tot) = T) (hat : LoadHolds rd (σ (.n 164)) ρ T)
    (hsz : LoadHolds rd (σ (.n 11)) ρ size) :
    (∀ a, Stmt.atom a ∈ csRank 163 164 s pk tot r → a.Holds rd σ) ∧ σ (.n (s + 6)) = key ∧
      σ (.n (s + 17)) = T * size ∧
      ∀ d p off, Stmt.atom (.load d p off) ∈ csRank 163 164 s pk tot r →
        (p = .n 163 ∧ off = r) ∨ (σ p = σ (.n 10) * gen ^ ρ ∧ off = 0) ∨
          (σ p = σ (.n 164) * gen ^ ρ ∧ off = 0) ∨ (σ p = σ (.n 11) * gen ^ ρ ∧ off = 0) := by
  obtain ⟨v0, h0⟩ := good_fresh (hG (.load (.n s) (.n 163) r) (by simp [csRank]))
    (hF s 163 r (by simp [csRank]) (by simp [freshShape])) hord
  have v1 : σ (.n (s + 1)) = gen ^ 7 := by
    rw [good_const (hG (.const (.n (s + 1)) (csW 7)) (by simp [csRank, osCst])), csW_eq (by decide)]
  have v5 : σ (.n (s + 5)) = σ (.n 10) * gen ^ ρ := by
    rw [good_mul (hG (.mul (.n (s + 5)) (.n 10) (.n s)) (by simp [csRank, osMul])) (by omega) (by omega), v0]
  obtain ⟨v6, h6⟩ := good_fresh (hG (.load (.n (s + 6)) (.n (s + 5)) 0) (by simp [csRank]))
    (hF _ _ 0 (by simp [csRank]) (by simp [freshShape])) (by rw [v5, loadHolds_mul_gen_pow]; exact hkey)
  have v7 : σ (.n (s + 7)) = gen ^ 1801 := by
    rw [good_const (hG (.const (.n (s + 7)) csBound) (by simp [csRank, osCst])), csBound_eq, gen_pow_eq_ofK]
  have hkey0 : key ≠ 0 := fun h => gen_pow_ne_zero N2 (by rw [← hkc, h, zero_mul])
  have g8 := hG (.mul (.n pk) (.n (s + 8)) (.n (s + 6))) (by simp [csRank, osMul])
  have v8 : σ (.n (s + 8)) = σ (.n pk) * key⁻¹ := by
    have : ¬ ((V.n (s + 8)).idx < (V.n pk).idx ∧ (V.n (s + 6)).idx < (V.n pk).idx) := by
      show ¬ (s + 8 < pk ∧ s + 6 < pk); omega
    have h := g8
    simp only [Good, this, ↓reduceIte] at h
    rw [h, v6]
  have hratio : σ (.n pk) * key⁻¹ = gen ^ (N1 - N2) := by
    have hg52 : (gen ^ 52 : E) ≠ 0 := gen_pow_ne_zero 52
    have : σ (.n pk) = gen ^ (N1 - N2) * key := by
      apply mul_right_cancel₀ hg52
      rw [hpkv, mul_assoc, hkc, ← pow_add, Nat.sub_add_cancel hN.le]
    rw [this, mul_assoc, mul_inv_cancel₀ hkey0, mul_one]
  have v9 : σ (.n (s + 9)) = csInvGen := good_const (hG (.const (.n (s + 9)) csInvGen) (by simp [csRank, osCst]))
  have v10 : σ (.n (s + 10)) = gen ^ (N1 - N2 - 1) := by
    rw [good_mul (hG (.mul (.n (s + 10)) (.n (s + 8)) (.n (s + 9))) (by simp [csRank, osMul])) (by omega)
      (by omega), v8, hratio, v9, show N1 - N2 = (N1 - N2 - 1) + 1 by omega, pow_succ, mul_assoc,
      mul_comm gen, csInvGen_mul_gen, mul_one, Nat.add_sub_cancel]
  have v14 : σ (.n (s + 14)) = σ (.n 164) * gen ^ ρ := by
    rw [good_mul (hG (.mul (.n (s + 14)) (.n 164) (.n s)) (by simp [csRank, osMul])) (by omega) (by omega), v0]
  have v15 : σ (.n (s + 15)) = σ (.n 11) * gen ^ ρ := by
    rw [good_mul (hG (.mul (.n (s + 15)) (.n 11) (.n s)) (by simp [csRank, osMul])) (by omega) (by omega), v0]
  obtain ⟨v16, h16⟩ := good_fresh (hG (.load (.n (s + 16)) (.n (s + 15)) 0) (by simp [csRank]))
    (hF _ _ 0 (by simp [csRank]) (by simp [freshShape])) (by rw [v15, loadHolds_mul_gen_pow]; exact hsz)
  have v17 : σ (.n (s + 17)) = T * size := by
    rw [good_mul (hG (.mul (.n (s + 17)) (.n tot) (.n (s + 16))) (by simp [csRank, osMul])) (by omega)
      (by omega), htotv, v16]
  refine ⟨fun a ha => ?_, v6, v17, fun d p off ha => ?_⟩
  · have hg := hG a ha
    simp only [csRank, osCst, osMul, csRc, List.mem_cons, Stmt.atom.injEq, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact hg
    · exact good_rcK hl (e := ρ) (K := 7) (by omega) (lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right
        (by decide) (show 3 ≤ k by omega))) v0 v1 (by omega) hg
    · exact good_mul hg (by omega) (by omega)
    · exact h6
    · exact hg
    · show σ (.n pk) = σ (.n (s + 8)) * σ (.n (s + 6))
      rw [v8, v6, mul_assoc, inv_mul_cancel₀ hkey0, mul_one]
    · exact hg
    · exact good_mul hg (by omega) (by omega)
    · exact good_rcK hl (e := N1 - N2 - 1) (K := 1801) (by omega) (lt_of_lt_of_le (by decide)
        (Nat.pow_le_pow_right (by decide) hk)) v10 v7 (by omega) hg
    · exact good_mul hg (by omega) (by omega)
    · show LoadHolds rd (σ (.n (s + 14))) 0 (σ (.n tot))
      rw [v14, htotv, loadHolds_mul_gen_pow]; exact hat
    · exact good_mul hg (by omega) (by omega)
    · exact h16
    · exact good_mul hg (by omega) (by omega)
  · simp only [csRank, osCst, osMul, csRc, List.mem_cons, Stmt.atom.injEq, Atom.load.injEq,
      List.not_mem_nil, or_false, reduceCtorEq, false_or] at ha
    rcases ha with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨v5, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨v14, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨v15, rfl⟩))

/-! ## A group's outputs -/

theorem csOut_eq (gi s : ℕ) : (csOut 303 164 gi s).1 =
    (csKappa (csG gi) s).1 ++ [osMul (csKappa (csG gi) s).2.2 1 (csKappa (csG gi) s).2.1,
      .atom (.load (.n ((csKappa (csG gi) s).2.2 + 1)) (.n (csKappa (csG gi) s).2.2) 0),
      .atom (.load (.n ((csKappa (csG gi) s).2.2 + 2)) (.n 164) gi),
      .atom (.load (.n ((csKappa (csG gi) s).2.2 + 2)) (.n 303) (csG gi).b0),
      .atom (.load (.n (csKappa (csG gi) s).2.1) (.n 303) (52 + (csG gi).b0))] ++
      ((List.range ((csG gi).len - 1)).map fun j ↦
        [osMul ((csKappa (csG gi) s).2.2 + 3 + j) ((csKappa (csG gi) s).2.2 + 2 + j) ((csKappa (csG gi) s).2.2 + 1),
          .atom (.load (.n ((csKappa (csG gi) s).2.2 + 3 + j)) (.n 303) ((csG gi).b0 + 1 + j)),
          .atom (.load (.n (csKappa (csG gi) s).2.1) (.n 303) (52 + (csG gi).b0 + 1 + j))]).flatten := rfl

/-- **Group `gi`'s outputs, evaluated forward**: from `group_at[gi] = g^A`, the stores of
`g^(A + j·2^κ)` at `outs[b0 + j]` and `g^κ` at `outs[52 + b0 + j]` hold where the memory has them. -/
theorem csOut_fwd {kv : ℕ → ℕ} (hkb : ∀ i < 8, σ (.n (2 + i)) = gen ^ kv i) (ht : ExpTables rd (σ (.n 1)))
    {gi : ℕ} (hgi : gi < 8) (hκ : csKap kv gi ≤ 33) {s : ℕ} (hs : 304 ≤ s)
    (hG : ∀ a, Stmt.atom a ∈ (csOut 303 164 gi s).1 → Good rd S w σ a) (hF : FreshOk S (csOut 303 164 gi s).1)
    {A : ℕ} (hat : LoadHolds rd (σ (.n 164)) gi (gen ^ A))
    (hout : ∀ j < (csG gi).len, LoadHolds rd (σ (.n 303)) ((csG gi).b0 + j) (gen ^ (A + j * 2 ^ csKap kv gi)) ∧
      LoadHolds rd (σ (.n 303)) (52 + (csG gi).b0 + j) (gen ^ csKap kv gi)) :
    (∀ a, Stmt.atom a ∈ (csOut 303 164 gi s).1 → a.Holds rd σ) ∧
      ∀ d p off, Stmt.atom (.load d p off) ∈ (csOut 303 164 gi s).1 →
        (p = .n 303 ∧ off < 104) ∨ (p = .n 164 ∧ off = gi) ∨ (σ p = σ (.n 1) * gen ^ csKap kv gi ∧ off = 0) := by
  obtain ⟨hsrc, hadj, hl1, hl14, -⟩ := csGroups_facts gi hgi
  have hb0 := groups_b0_le gi hgi
  have hblen : (csG gi).b0 + (csG gi).len ≤ 52 := by
    have : ∀ gi < 8, (csG gi).b0 + (csG gi).len ≤ 52 := by decide
    exact this gi hgi
  rw [csOut_eq] at hG hF ⊢
  set g := csG gi with hgdef
  set kp := csKappa g s with hkpdef
  have hkp_idx : kp.2.1 < kp.2.2 ∧ s ≤ kp.2.2 ∧ 2 ≤ kp.2.1 := by
    rcases csKappa_shape g s with ⟨-, -, h2, h3⟩ | ⟨-, -, h2, h3⟩ <;> rw [hkpdef, h2, h3] <;> omega
  set v := kp.2.1 with hvdef
  set s' := kp.2.2 with hs'def
  obtain ⟨hkA, hv⟩ := csKappa_fwd hkb hsrc (by omega) (by omega) fun a ha =>
    hG a (List.mem_append_left _ (List.mem_append_left _ ha))
  have hv' : σ (.n v) = gen ^ csKap kv gi := hv
  have vm : σ (.n s') = σ (.n 1) * gen ^ csKap kv gi := by
    rw [good_mul (hG (.mul (.n s') (.n 1) (.n v)) (by simp [osMul])) (by omega) (by omega), hv']
  have hsq : LoadHolds rd (σ (.n s')) 0 (gen ^ 2 ^ csKap kv gi) := by
    rw [vm, loadHolds_mul_gen_pow, Nat.add_zero]; exact ht.1 _ (show csKap kv gi < 34 by omega)
  obtain ⟨v1, h1⟩ := good_fresh (hG (.load (.n (s' + 1)) (.n s') 0) (by simp))
    (hF _ _ 0 (by simp) (by simp [freshShape])) hsq
  obtain ⟨v2, h2⟩ := good_fresh (hG (.load (.n (s' + 2)) (.n 164) gi) (by simp))
    (hF _ _ gi (by simp) (by simp [freshShape]; omega)) hat
  -- the steps
  have hmemJ : ∀ j < g.len - 1, ∀ st ∈ [osMul (s' + 3 + j) (s' + 2 + j) (s' + 1),
      Stmt.atom (.load (.n (s' + 3 + j)) (.n 303) (g.b0 + 1 + j)),
      Stmt.atom (.load (.n v) (.n 303) (52 + g.b0 + 1 + j))],
      st ∈ (kp.1 ++ [osMul s' 1 v, .atom (.load (.n (s' + 1)) (.n s') 0), .atom (.load (.n (s' + 2)) (.n 164) gi),
        .atom (.load (.n (s' + 2)) (.n 303) g.b0), .atom (.load (.n v) (.n 303) (52 + g.b0))] ++
        ((List.range (g.len - 1)).map fun j ↦ [osMul (s' + 3 + j) (s' + 2 + j) (s' + 1),
          .atom (.load (.n (s' + 3 + j)) (.n 303) (g.b0 + 1 + j)),
          .atom (.load (.n v) (.n 303) (52 + g.b0 + 1 + j))]).flatten) := fun j hj st hst =>
    List.mem_append_right _ (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩, hst⟩)
  have vstep : ∀ j < g.len, σ (.n (s' + 2 + j)) = gen ^ (A + j * 2 ^ csKap kv gi) := by
    intro j
    induction j with
    | zero => intro _; rw [Nat.add_zero, v2, Nat.zero_mul, Nat.add_zero]
    | succ j ih =>
      intro hj
      have e := good_mul (hG _ (hmemJ j (by omega) _ List.mem_cons_self)) (by omega) (by omega)
      rw [show s' + 2 + (j + 1) = s' + 3 + j by omega, e, ih (by omega), v1, ← pow_add]
      congr 1; ring
  refine ⟨fun a ha => ?_, fun d p off ha => ?_⟩
  · have hg := hG a ha
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatten, List.mem_map,
      List.mem_range] at ha
    rcases ha with ((ha | ha | ha | ha | ha | ha) | ⟨_, ⟨j, hj, rfl⟩, ha⟩)
    · exact hkA a ha
    · cases ha; exact good_mul hg (by omega) (by omega)
    · cases ha; exact h1
    · cases ha; exact h2
    · cases ha
      show LoadHolds rd (σ (.n 303)) g.b0 (σ (.n (s' + 2)))
      have := (hout 0 (by omega)).1
      rw [Nat.add_zero, Nat.zero_mul, Nat.add_zero] at this
      rw [v2]; exact this
    · cases ha
      show LoadHolds rd (σ (.n 303)) (52 + g.b0) (σ (.n v))
      have := (hout 0 (by omega)).2
      rw [Nat.add_zero] at this
      rw [hv']; exact this
    · simp only [List.mem_cons, List.not_mem_nil, or_false, osMul, Stmt.atom.injEq] at ha
      rcases ha with rfl | rfl | rfl
      · exact good_mul hg (by omega) (by omega)
      · show LoadHolds rd (σ (.n 303)) (g.b0 + 1 + j) (σ (.n (s' + 3 + j)))
        rw [show s' + 3 + j = s' + 2 + (j + 1) by omega, vstep (j + 1) (by omega),
          show g.b0 + 1 + j = g.b0 + (j + 1) by omega]
        exact (hout (j + 1) (by omega)).1
      · show LoadHolds rd (σ (.n 303)) (52 + g.b0 + 1 + j) (σ (.n v))
        rw [hv', show 52 + g.b0 + 1 + j = 52 + g.b0 + (j + 1) by omega]
        exact (hout (j + 1) (by omega)).2
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatten, List.mem_map,
      List.mem_range] at ha
    rcases ha with ((ha | ha | ha | ha | ha | ha) | ⟨_, ⟨j, hj, rfl⟩, ha⟩)
    · rcases csKappa_shape g s with ⟨-, h1, -, -⟩ | ⟨-, h1, -, -⟩
      · rw [h1] at ha; exact absurd ha List.not_mem_nil
      · rw [h1] at ha; simp [osCst, osMul] at ha
    · simp [osMul] at ha
    · simp only [Stmt.atom.injEq, Atom.load.injEq] at ha
      obtain ⟨-, rfl, rfl⟩ := ha; exact Or.inr (Or.inr ⟨vm, rfl⟩)
    · simp only [Stmt.atom.injEq, Atom.load.injEq] at ha
      obtain ⟨-, rfl, rfl⟩ := ha; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · simp only [Stmt.atom.injEq, Atom.load.injEq] at ha
      obtain ⟨-, rfl, rfl⟩ := ha; exact Or.inl ⟨rfl, by omega⟩
    · simp only [Stmt.atom.injEq, Atom.load.injEq] at ha
      obtain ⟨-, rfl, rfl⟩ := ha; exact Or.inl ⟨rfl, by omega⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, osMul, Stmt.atom.injEq, Atom.load.injEq,
        reduceCtorEq, false_or] at ha
      rcases ha with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
      · exact Or.inl ⟨rfl, by omega⟩
      · exact Or.inl ⟨rfl, by omega⟩

end
end LeanVM.Guest.B1.VsC
