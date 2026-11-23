/-
  LeanVM.Guest.B1.Gkr.Rounds

  Runs of GKR rounds between round records, and rounds chained.
-/

module

public import LeanVM.Guest.B1.Gkr.Round
public import LeanVM.Guest.CoreData
public import LeanVM.Guest.GuestConst
import LeanVM.Guest.B1.Tables.Basic

/-!
# Rounds between records

A round record (`ROUND_FS = 0`, `ROUND_CURSOR = 5`, `ROUND_CLAIM = 6`, `ROUND_SLOTS = 7` words)
carries a sponge's capacity, a stream cursor and a claim. `TbGkrRoundsOut n s rd rec pt` (B1-a's
`GkrRoundsOut`, its cursor in the record): from the record at `rec`, `n` rounds read `4n` words at
its cursor, their eq factors at `pt[0 .. n]`, store their challenges at `pt[42 ..]`, and the
record `s` records on, at `rec·g^(7s)`, carries the sponge, the cursor and the claim after them
(`gkrRun`). An iteration of a radix-four layer's loop moves one record (`s = 1`).

* `tb_gkrRun_append`: rounds run in sequence;
* `gkrRoundsOut_append`: two runs of rounds, the second from the first's last record, are one.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A record's five capacity cells, its fields `stride` words apart from offset `off`
(B1-a's `CapAt`). -/
def TbCapAt (rd : Reader) (rec : E) (off stride : ℕ) (cap : List E) : Prop :=
  cap.length = 5 ∧ ∀ j (hj : j < cap.length), LoadHolds rd rec (off + j * stride) cap[j]

/-- **`n` GKR rounds between records `s` apart** (B1-a's `GkrRoundsOut` at `s = 1`, its cursor in
the record). -/
def TbGkrRoundsOut (n s : ℕ) (rd : Reader) (rec pt : E) : Prop :=
  ∃ (cap : List E) (cur claim : E) (cs : List (List E)) (es : List E),
    TbCapAt rd rec 0 1 cap ∧
    LoadHolds rd rec 5 cur ∧ LoadHolds rd rec 6 claim ∧
    cs.length = n ∧ (∀ c ∈ cs, c.length = 4) ∧ TbReadsAt rd cur cs.flatten ∧
    es.length = n ∧ TbReadsAt rd pt es ∧
    TbReadsAt rd (pt * gen ^ 42) (gkrRun cs es claim ⟨cap, []⟩).1 ∧
    TbCapAt rd rec (7 * s) 1 (gkrRun cs es claim ⟨cap, []⟩).2.2.cap ∧
    LoadHolds rd rec (7 * s + 5) (cur * gen ^ (4 * n)) ∧
    LoadHolds rd rec (7 * s + 6) (gkrRun cs es claim ⟨cap, []⟩).2.1

/-! ## Rounds in sequence -/

theorem tb_gkrRun_append : ∀ (cs1 cs2 : List (List E)) (es1 es2 : List E) (claim : E) (s : Fs),
    cs1.length = es1.length →
    gkrRun (cs1 ++ cs2) (es1 ++ es2) claim s =
      ((gkrRun cs1 es1 claim s).1 ++
        (gkrRun cs2 es2 (gkrRun cs1 es1 claim s).2.1 (gkrRun cs1 es1 claim s).2.2).1,
       (gkrRun cs2 es2 (gkrRun cs1 es1 claim s).2.1 (gkrRun cs1 es1 claim s).2.2).2)
  | [], cs2, [], es2, claim, s, _ => by simp [gkrRun]
  | c :: cs1, cs2, e :: es1, es2, claim, s, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.cons_append, gkrRun]
    rw [tb_gkrRun_append cs1 cs2 es1 es2 _ _ h]
  | [], _, _ :: _, _, _, _, h => by simp at h
  | _ :: _, _, [], _, _, _, h => by simp at h

theorem tb_gkrRun_length : ∀ (cs : List (List E)) (es : List E) (claim : E) (s : Fs),
    cs.length = es.length → (gkrRun cs es claim s).1.length = cs.length
  | [], [], _, _, _ => rfl
  | c :: cs, e :: es, claim, s, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [gkrRun, tb_gkrRun_length cs es _ _ h]
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by simp at h

theorem tbCapAt_mul_gen_pow {rd : Reader} {rec : E} {a off stride : ℕ} {cap : List E} :
    TbCapAt rd (rec * gen ^ a) off stride cap ↔ TbCapAt rd rec (a + off) stride cap := by
  simp only [TbCapAt, tb_loadHolds_mul_gen_pow, Nat.add_assoc]

theorem tbCapAt_unique {rd : Reader} {rec : E} {off stride : ℕ} {c1 c2 : List E}
    (h1 : TbCapAt rd rec off stride c1) (h2 : TbCapAt rd rec off stride c2) : c1 = c2 :=
  List.ext_getElem (h1.1.trans h2.1.symm) fun j hj1 hj2 =>
    tb_loadHolds_unique (h1.2 j hj1) (h2.2 j hj2)

theorem flatten_length_four {cs : List (List E)} (h : ∀ c ∈ cs, c.length = 4) :
    cs.flatten.length = 4 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatten_cons, List.length_append, h c (by simp),
      ih fun c' hc' => h c' (by simp [hc']), List.length_cons]
    ring

theorem tb_gkrRun_pend : ∀ (cs : List (List E)) (es : List E) (claim : E) (s : Fs),
    s.pend = [] → (gkrRun cs es claim s).2.2.pend = []
  | [], _, _, _, h => by cases ‹List E› <;> exact h
  | c :: cs, [], _, _, h => h
  | c :: cs, e :: es, claim, s, _ => by
    simp only [gkrRun]
    exact tb_gkrRun_pend _ _ _ _ rfl

/-- The sponge after rounds from a capacity has nothing waiting. -/
theorem tb_gkrRun_eta (cs : List (List E)) (es : List E) (claim : E) (cap : List E)
    {pend : List (E × ℕ)} (hp : pend = []) :
    (gkrRun cs es claim ⟨cap, pend⟩).2.2 =
      ⟨(gkrRun cs es claim ⟨cap, pend⟩).2.2.cap, []⟩ := by
  have := tb_gkrRun_pend cs es claim ⟨cap, pend⟩ hp
  rw [← this]

/-- **Rounds in sequence**: `n1` rounds from `rec` to `s1` records on, then `n2` from there to
`s2` further, are `n1 + n2` rounds from `rec` to `s1 + s2` records on. -/
theorem gkrRoundsOut_append {rd : Reader} {n1 n2 s1 s2 : ℕ} {rec pt : E}
    (h1 : TbGkrRoundsOut n1 s1 rd rec pt)
    (h2 : TbGkrRoundsOut n2 s2 rd (rec * gen ^ (7 * s1)) (pt * gen ^ n1)) :
    TbGkrRoundsOut (n1 + n2) (s1 + s2) rd rec pt := by
  obtain ⟨cap, cur, claim, cs1, es1, hc, hcur, hcl, hl1, h4, hr1, he1, hre1, hch1, hc1, hu1,
    hcl1⟩ := h1
  obtain ⟨cap2, cur2, claim2, cs2, es2, hc2, hcur2, hcl2, hl2, h42, hr2, he2, hre2, hch2, hc2',
    hu2, hcl2'⟩ := h2
  rw [tbCapAt_mul_gen_pow, Nat.add_zero] at hc2
  rw [tb_loadHolds_mul_gen_pow] at hcur2 hcl2
  have ecap := tbCapAt_unique hc2 hc1
  have ecur := tb_loadHolds_unique hcur2 hu1
  have ecl := tb_loadHolds_unique hcl2 hcl1
  subst ecap ecur ecl
  have hrun := tb_gkrRun_append cs1 cs2 es1 es2 claim ⟨cap, []⟩ (hl1.trans he1.symm)
  refine ⟨cap, cur, claim, cs1 ++ cs2, es1 ++ es2, hc, hcur, hcl, by simp [hl1, hl2],
    fun c hc' => ?_, ?_, by simp [he1, he2], ?_, ?_, ?_, ?_, ?_⟩
  · rcases List.mem_append.mp hc' with h | h
    · exact h4 c h
    · exact h42 c h
  · rw [List.flatten_append, tbReadsAt_append, flatten_length_four h4, hl1]
    exact ⟨hr1, hr2⟩
  · rw [tbReadsAt_append, he1]
    exact ⟨hre1, hre2⟩
  · rw [hrun, tbReadsAt_append, tb_gkrRun_length _ _ _ _ (hl1.trans he1.symm), hl1]
    refine ⟨hch1, ?_⟩
    rw [tb_gkrRun_eta _ _ _ _ rfl]
    rw [show pt * gen ^ 42 * gen ^ n1 = pt * gen ^ n1 * gen ^ 42 by ring]
    exact hch2
  · rw [hrun, tb_gkrRun_eta cs1 es1 claim cap rfl]
    rw [tbCapAt_mul_gen_pow] at hc2'
    rw [show 7 * (s1 + s2) = 7 * s1 + 7 * s2 by ring]
    exact hc2'
  · rw [tb_loadHolds_mul_gen_pow] at hu2
    rw [show 7 * (s1 + s2) + 5 = 7 * s1 + (7 * s2 + 5) by ring,
      show cur * gen ^ (4 * (n1 + n2)) = cur * gen ^ (4 * n1) * gen ^ (4 * n2) by ring]
    exact hu2
  · rw [tb_loadHolds_mul_gen_pow] at hcl2'
    rw [hrun, tb_gkrRun_eta cs1 es1 claim cap rfl,
      show 7 * (s1 + s2) + 6 = 7 * s1 + (7 * s2 + 6) by ring]
    exact hcl2'

/-- No rounds: a record's facts. -/
theorem gkrRoundsOut_zero {rd : Reader} {rec pt : E} {cap : List E} {cur claim : E}
    (hc : TbCapAt rd rec 0 1 cap)
    (hcur : LoadHolds rd rec 5 cur) (hcl : LoadHolds rd rec 6 claim) :
    TbGkrRoundsOut 0 0 rd rec pt :=
  ⟨cap, cur, claim, [], [], hc, hcur, hcl, rfl, by simp, tbReadsAt_nil _ _, rfl,
    tbReadsAt_nil _ _, tbReadsAt_nil _ _, by simpa [gkrRun] using hc,
    by simpa using hcur, by simpa [gkrRun] using hcl⟩

end
end LeanVM.Guest.B1.Tables
