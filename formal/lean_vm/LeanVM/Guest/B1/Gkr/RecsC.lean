/-
  LeanVM.Guest.B1.Gkr.RecsC

  The honest round records of a run of GKR rounds: every run of consecutive rounds among them is
  what `gkr_rounds` and `__loop36` ask.
-/

module

public import LeanVM.Guest.B1.Gkr.Rounds

/-!
# Round records, completely

`RecsAt rd rec cur cs es claim s`: record `r ≤ n` at `rec·g^r` carries the capacity, the cursor
`4r` words on and the claim after the first `r` rounds of `gkrRun cs es claim s`. `recs_rounds`:
with the rounds' words at the cursor, the eq factors at `pt` and the challenges at `pt[42 ..]`,
any `k` consecutive rounds from round `a` are `TbGkrRoundsOut k` at `rec·g^a`, `pt·g^a`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **The round records**: record `r ≤ n` carries the sponge's capacity, the cursor and the claim
after the first `r` rounds. -/
def RecsAt (rd : Reader) (rec cur : E) (cs : List (List E)) (es : List E) (claim : E) (s : Fs) :
    Prop :=
  ∀ r ≤ cs.length,
    TbCapAt rd (rec * gen ^ r) 0 gkCap (gkrRun (cs.take r) (es.take r) claim s).2.2.cap ∧
      LoadHolds rd (rec * gen ^ r) (5 * gkCap) (cur * gen ^ (4 * r)) ∧
      LoadHolds rd (rec * gen ^ r) (6 * gkCap) (gkrRun (cs.take r) (es.take r) claim s).2.1

theorem tb_gkrRun_take_add (cs : List (List E)) (es : List E) (claim : E) (s : Fs) (a k : ℕ)
    (hl : cs.length = es.length) :
    gkrRun (cs.take (a + k)) (es.take (a + k)) claim s =
      ((gkrRun (cs.take a) (es.take a) claim s).1 ++
        (gkrRun ((cs.drop a).take k) ((es.drop a).take k) (gkrRun (cs.take a) (es.take a) claim s).2.1
          (gkrRun (cs.take a) (es.take a) claim s).2.2).1,
       (gkrRun ((cs.drop a).take k) ((es.drop a).take k) (gkrRun (cs.take a) (es.take a) claim s).2.1
          (gkrRun (cs.take a) (es.take a) claim s).2.2).2) := by
  rw [List.take_add, List.take_add]
  exact tb_gkrRun_append _ _ _ _ _ _ (by simp [hl])

theorem tb_flatten_take_length {cs : List (List E)} (h4 : ∀ c ∈ cs, c.length = 4) (a : ℕ) :
    (cs.take a).flatten.length = 4 * min a cs.length := by
  rw [flatten_length_four (fun c hc => h4 c (List.mem_of_mem_take hc)), List.length_take]

/-- Words at `p` from offset `a`, `k` of them. -/
theorem tbReadsAt_drop_take {rd : Reader} {p : E} {xs : List E} (h : TbReadsAt rd p xs) (a k : ℕ) :
    TbReadsAt rd (p * gen ^ (min a xs.length)) ((xs.drop a).take k) := by
  rw [← List.take_append_drop a xs, tbReadsAt_append] at h
  have h2 := h.2
  rw [← List.take_append_drop k (xs.drop a), tbReadsAt_append] at h2
  rw [List.length_take] at h2
  exact h2.1

/-- **Consecutive rounds among the records** are `gkr_rounds`' meaning. -/
theorem recs_rounds {rd : Reader} {rec cur pt claim : E} {cs : List (List E)} {es : List E}
    {s : Fs} (hR : RecsAt rd rec cur cs es claim s) (hp : s.pend = []) (hcan : AllCanonical s.cap)
    (hl : cs.length = es.length) (h4 : ∀ c ∈ cs, c.length = 4) (hx : TbReadsAt rd cur cs.flatten)
    (he : TbReadsAt rd pt es) (hch : TbReadsAt rd (pt * gen ^ 42) (gkrRun cs es claim s).1)
    {a k : ℕ} (hak : a + k ≤ cs.length) :
    TbGkrRoundsOut k rd (rec * gen ^ a) (pt * gen ^ a) := by
  set r1 := gkrRun (cs.take a) (es.take a) claim s with hr1
  have hp1 : r1.2.2 = ⟨r1.2.2.cap, []⟩ := by
    have := tb_gkrRun_pend (cs.take a) (es.take a) claim s hp
    rw [← hr1] at this
    rw [← this]
  set cs2 := (cs.drop a).take k
  set es2 := (es.drop a).take k
  set r2 := gkrRun cs2 es2 r1.2.1 r1.2.2 with hr2
  have hsplit := tb_gkrRun_take_add cs es claim s a k hl
  rw [← hr1, ← hr2] at hsplit
  obtain ⟨c0, u0, l0⟩ := hR a (by omega)
  obtain ⟨c1, u1, l1⟩ := hR (a + k) hak
  rw [hsplit] at c1 l1
  rw [← hr1] at c0 l0
  have hc2 : cs2.length = k := by simp [cs2]; omega
  have he2 : es2.length = k := by simp [es2]; omega
  refine ⟨r1.2.2.cap, cur * gen ^ (4 * a), r1.2.1, cs2, es2, c0,
    tb_gkrRun_canonical _ _ _ _ hcan, u0, l0, hc2, fun c hc => h4 c
      (List.mem_of_mem_drop (List.mem_of_mem_take hc)), ?_, he2, ?_, ?_, ?_, ?_, ?_⟩
  · -- the rounds' words
    have hx' := tbReadsAt_drop_take hx (4 * a) (4 * k)
    rw [flatten_length_four h4, show min (4 * a) (4 * cs.length) = 4 * a by omega] at hx'
    have e : (cs.flatten.drop (4 * a)).take (4 * k) = cs2.flatten := by
      have h1 : cs.flatten = (cs.take a).flatten ++ (cs2 ++ (cs.drop a).drop k).flatten := by
        rw [List.take_append_drop, ← List.flatten_append, List.take_append_drop]
      have hl1 : (cs.take a).flatten.length = 4 * a := by
        rw [tb_flatten_take_length h4]; omega
      have hl2 : cs2.flatten.length = 4 * k := by
        rw [flatten_length_four (fun c hc => h4 c
          (List.mem_of_mem_drop (List.mem_of_mem_take hc))), hc2]
      rw [h1, List.drop_append_of_le_length (by omega), List.flatten_append,
        List.drop_eq_nil_of_le (by omega), List.nil_append, List.take_left' hl2]
    rw [e] at hx'
    exact hx'
  · have he' := tbReadsAt_drop_take he a k
    rwa [show min a es.length = a by omega] at he'
  · -- the challenges
    rw [← hp1]
    have hfull : gkrRun cs es claim s = gkrRun (cs.take (a + k) ++ cs.drop (a + k))
        (es.take (a + k) ++ es.drop (a + k)) claim s := by
      rw [List.take_append_drop, List.take_append_drop]
    rw [hfull, tb_gkrRun_append _ _ _ _ _ _ (by simp [hl]), hsplit] at hch
    simp only [List.append_assoc] at hch
    rw [tbReadsAt_append, tbReadsAt_append] at hch
    have hl1 : r1.1.length = a := by
      rw [hr1, tb_gkrRun_length _ _ _ _ (by simp [hl])]; simp; omega
    rw [hl1, show pt * gen ^ 42 * gen ^ a = pt * gen ^ a * gen ^ 42 by ring] at hch
    exact hch.2.1
  · rw [← hp1, tbCapAt_mul_gen_pow]
    rw [tbCapAt_mul_gen_pow, Nat.add_zero] at c1
    exact c1
  · rw [tb_loadHolds_mul_gen_pow] at u1 ⊢
    rw [show a + (k + 5 * gkCap) = a + k + 5 * gkCap by ring,
      show cur * gen ^ (4 * a) * gen ^ (4 * k) = cur * gen ^ (4 * (a + k)) by ring]
    exact u1
  · rw [← hp1, tb_loadHolds_mul_gen_pow]
    rw [tb_loadHolds_mul_gen_pow] at l1
    rw [show a + (k + 6 * gkCap) = a + k + 6 * gkCap by ring]
    exact l1

end
end LeanVM.Guest.B1.Tables
