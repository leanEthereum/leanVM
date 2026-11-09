/-
  LeanVM.Guest.B1.Tables.VtC.FInBuf

  Where the loads of statements `2688 ..< 6353` read: inside `fp_w`, the cursor's words, the
  challenges' products and the equality prefix.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FComplete
public import LeanVM.Guest.B1.Tables.VtC.InBuf

/-!
# The window's loads, inside buffers

`BufWin σ bufs p len`: the pointer `σ p` starts a run of `len` words inside one of the buffers
`bufs`. `vtF_loadsInBuf`: given such runs for `fp_w` (16 words read), the cursor (the 159
evaluations) and the challenges' products and equality prefix (`n + 1` each), every load of the
statements lands in a buffer.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- The pointer `σ p` starts a run of `len` words inside one of the buffers. -/
def BufWin (σ : Val) (bufs : List (E × ℕ)) (p : V) (len : ℕ) : Prop :=
  ∃ q ∈ bufs, ∃ j : ℕ, σ p = q.1 * gen ^ j ∧ j + len ≤ q.2

theorem BufWin.of_mem {σ : Val} {bufs : List (E × ℕ)} {p : V} {len : ℕ}
    (h : (σ p, len) ∈ bufs) : BufWin σ bufs p len :=
  ⟨_, h, 0, by simp, by simp⟩

theorem BufWin.inBuf {σ : Val} {bufs : List (E × ℕ)} {p : V} {len : ℕ}
    (h : BufWin σ bufs p len) {off : ℕ} (ho : off < len) : InBuf σ bufs p off := by
  obtain ⟨q, hq, j, e, hj⟩ := h
  exact ⟨q, hq, j, e, by omega⟩

/-- A run at `σ p'·g^m`, `m + 1` inside a run at `σ p'`. -/
theorem BufWin.shift {σ : Val} {bufs : List (E × ℕ)} {p p' : V} {len m : ℕ}
    (h : BufWin σ bufs p' len) (hm : m < len) (e : σ p = σ p' * gen ^ m) : InBuf σ bufs p 0 := by
  obtain ⟨q, hq, j, e', hj⟩ := h
  exact ⟨q, hq, j + m, by rw [e, e', mul_assoc, ← pow_add], by omega⟩

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- **The window's loads land in buffers.** -/
theorem vtF_loadsInBuf (hl : args.length = 20) {bufs : List (E × ℕ)}
    (h13 : BufWin (vtσ rd w args) bufs (.n 13) 16)
    (hcur : BufWin (vtσ rd w args) bufs (.n 2625) 159)
    {τs : ℕ → ℕ} (hkbt : ∀ t < 6, vtσ rd w args (.n (30 + t)) = gen ^ τs t)
    {n : ℕ} (hgn : vtσ rd w args (.n 2516) = gen ^ n) (hτn : ∀ t < 6, τs t ≤ n)
    (hcp : BufWin (vtσ rd w args) bufs (.n 2608) (n + 1))
    (hpe : BufWin (vtσ rd w args) bufs (.n 2629) (n + 1)) :
    LoadsInBuf (vtσ rd w args) bufs ((vtPre.drop 2688).take (6353 - 2688)) := by
  intro d p off hs
  rw [tbStmtsEqb_sound vtF_split] at hs
  rcases List.mem_append.mp hs with hs | hs
  swap
  · simp at hs
  cases hr : rdFpw (.atom (.load d p off))
  · have hf : Stmt.atom (.load d p off) ∈ vtFTags.flatMap vtFTagT := by
      rw [← tbStmtsEqb_sound vtF_cover]
      exact List.mem_filter.mpr ⟨hs, by simp [hr, autoB, Fwd.pureB, hintB]⟩
    obtain ⟨q, hq, hsq⟩ := List.mem_flatMap.mp hf
    rcases vtFTags_spec q hq with ⟨h0, hk⟩ | ⟨h1, hj⟩ | ⟨h3, ht⟩
    · obtain ⟨a, k⟩ := q
      simp only at h0 hk
      subst h0
      simp only [vtFTagT, vtEvRest, List.mem_cons, List.not_mem_nil, or_false,
        Stmt.atom.injEq, Atom.load.injEq, reduceCtorEq, or_false] at hsq
      obtain ⟨-, rfl, rfl⟩ := hsq
      exact hcur.inBuf hk
    · obtain ⟨a, j⟩ := q
      simp only at h1
      subst h1
      simp [vtFTagT, vtPermT, keccakA] at hsq
    · obtain ⟨a, t⟩ := q
      simp only at h3 ht
      subst h3
      obtain ⟨e1, e3⟩ := vtF_airVals (w := w) hl hkbt hgn hτn ht
      have hfilt := tbStmtsEqb_sound (vtAirT_rest t ht)
      simp only [vtFTagT] at hsq
      rw [hfilt] at hsq
      simp only [vtAirRest, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq,
        Atom.load.injEq, reduceCtorEq, false_or] at hsq
      rcases hsq with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
      · exact hcp.shift (by omega) e1
      · exact hpe.shift (by have := hτn t ht; omega) e3
  · match p, hr with
    | .n 13, _ =>
      have hm : Stmt.atom (.load d (.n 13) off) ∈ vtEvL :=
        vtEvL_mem (vtF_mem hs) (fun _ _ _ h ↦ by cases h)
      have := List.all_eq_true.mp vtF_loadsBelow _ hm
      simp only at this
      have := List.all_eq_true.mp this (13, 16) (by simp)
      exact h13.inBuf (by simpa using this)

end

end
end LeanVM.Guest.B1.Tables
