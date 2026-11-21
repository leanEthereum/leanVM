/-
  LeanVM.Guest.B1.KeccakGkr.PlainComplete41

  `keccak_plain_rounds__L4_L1`, completely, and both specializations: `keccak_plain_rounds`'
  completeness.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.PlainComplete60
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_plain_rounds__L4_L1»

/-!
# `keccak_plain_rounds__L4_L1`, completely

As `plain60_complete`, with one scalar `w` waiting, its rate cells the arguments `5`, `6`
(`PlainCellsOk`): the first round's `KECCAK` reads them (`plain_core_sq1`).
`keccak_plain_rounds_complete : keccak_plain_rounds_complete_Spec`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

theorem plain41_chk : Fwd.chk 11 (fn% «keccak_plain_rounds__L4_L1»).body = some 130 :=
  by decide +kernel

theorem plain41_stores : storesOf 11 (fn% «keccak_plain_rounds__L4_L1»).body =
    [.load (.n (val% «keccak_plain_rounds__L4_L1» "nxt[0]@1")) (.n (val% «keccak_plain_rounds__L4_L1» "point")) 0, .load (.n (val% «keccak_plain_rounds__L4_L1» "nxt[0]@2")) (.n (val% «keccak_plain_rounds__L4_L1» "point")) 1, .load (.n (val% «keccak_plain_rounds__L4_L1» "nxt[0]@3")) (.n (val% «keccak_plain_rounds__L4_L1» "point")) 2,
      .load (.n (val% «keccak_plain_rounds__L4_L1» "nxt[0]@4")) (.n (val% «keccak_plain_rounds__L4_L1» "point")) 3] := by
  decide +kernel

theorem four_of_length {α : Type} {l : List α} (h : l.length = 4) :
    ∃ a b c d, l = [a, b, c, d] := by
  match l, h with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

/-- **`keccak_plain_rounds__L4_L1` is complete**, the waiting cells a scalar's. -/
theorem plain41_complete (rd : Reader) (args rets : List E) (hpc : PlainCellsOk 1 args)
    (hm : MeaningPlainRounds 4 1 rd args rets) :
    coreProgram.Rel rd "keccak_plain_rounds__L4_L1" args rets := by
  match args, hm with
  | [f0, f1, f2, f3, f4, p0, p1, cur, value, point, tabs], hm =>
  obtain ⟨wv, hwv⟩ := hpc rfl
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hwv
  obtain ⟨rounds, hlen, hreads, hrun⟩ := hm
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, rfl⟩ := four_of_length hlen
  obtain ⟨hpt, hret⟩ := hrun wv (fun _ ↦ hwv)
  simp only [plainStart, ↓reduceIte] at hpt hret
  have rd' : ∀ k (hk : k < 8), LoadHolds rd cur k ([a0, b0, a1, b1, a2, b2, a3, b3][k]'(by
      simpa using hk)) := fun k hk ↦ hreads k (by simpa using hk)
  -- the honest valuation
  set l : List E := [f0, f1, f2, f3, f4, p0, p1, cur, value, point, tabs] with hl
  have g := (ev_spec rd (fun _ ↦ 0) (fn% «keccak_plain_rounds__L4_L1»).body l plain41_chk).2.2
  have pp : ∀ i (hi : i < 11), Val.ofArgs (ev rd (fun _ ↦ 0) l
      (fn% «keccak_plain_rounds__L4_L1»).body) (.n i) =
      l.getD i 0 := fun i hi ↦
    ev_params rd (fun _ ↦ 0) (l := l) plain41_chk (by simpa [hl] using hi)
  rw [show l.length = 11 from rfl, plain41_stores] at g
  generalize Val.ofArgs (ev rd (fun _ ↦ 0) l (fn% «keccak_plain_rounds__L4_L1»).body) = σ at g pp
  rw [body41] at g
  have p7 : σ (.n (val% «keccak_plain_rounds__L4_L1» "cursor")) = cur := pp 7 (by norm_num)
  have p8 : σ (.n (val% «keccak_plain_rounds__L4_L1» "value@1")) = value := pp 8 (by norm_num)
  have p9 : σ (.n (val% «keccak_plain_rounds__L4_L1» "point")) = point := pp 9 (by norm_num)
  have inT : ∀ s, (s ∈ [Stmt.atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "sp[0]")) (.n (val% «keccak_plain_rounds__L4_L1» "fs0"))), .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "sp[1]")) (.n (val% «keccak_plain_rounds__L4_L1» "fs1"))),
      .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "sp[2]")) (.n (val% «keccak_plain_rounds__L4_L1» "fs2"))), .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "sp[3]")) (.n (val% «keccak_plain_rounds__L4_L1» "fs3"))), .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "sp[4]")) (.n (val% «keccak_plain_rounds__L4_L1» "fs4"))),
      .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "rate[0]@1")) (.n (val% «keccak_plain_rounds__L4_L1» "p0"))), .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "rate[1]@1")) (.n (val% «keccak_plain_rounds__L4_L1» "p1")))] ∨
      s ∈ plainRoundT (.n (val% «keccak_plain_rounds__L4_L1» "cursor")) (.n (val% «keccak_plain_rounds__L4_L1» "point")) (.n (val% «keccak_plain_rounds__L4_L1» "value@1"))
        ([.n (val% «keccak_plain_rounds__L4_L1» "rate[0]@1"), .n (val% «keccak_plain_rounds__L4_L1» "rate[1]@1"), .n (val% «keccak_plain_rounds__L4_L1» "rate[2]@1"), .n (val% «keccak_plain_rounds__L4_L1» "rate[3]@1"), .n (val% «keccak_plain_rounds__L4_L1» "rate[4]"), .n (val% «keccak_plain_rounds__L4_L1» "rate[5]")] ++ [.n (val% «keccak_plain_rounds__L4_L1» "rate[6]"), .n (val% «keccak_plain_rounds__L4_L1» "rate[7]")] ++ capV 11) plainMid41a 0 18 26 ∨
      s ∈ plainRoundT (.n (val% «keccak_plain_rounds__L4_L1» "cursor")) (.n (val% «keccak_plain_rounds__L4_L1» "point")) (.n (val% «keccak_plain_rounds__L4_L1» "value@2")) (plainIns0 44 [.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")] 34)
        plainMid41b 1 44 55 ∨
      s ∈ plainRoundT (.n (val% «keccak_plain_rounds__L4_L1» "cursor")) (.n (val% «keccak_plain_rounds__L4_L1» "point")) (.n (val% «keccak_plain_rounds__L4_L1» "value@3")) (plainIns0 73 [.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")] 63) [] 2
        73 79 ∨
      s ∈ plainRoundT (.n (val% «keccak_plain_rounds__L4_L1» "cursor")) (.n (val% «keccak_plain_rounds__L4_L1» "point")) (.n (val% «keccak_plain_rounds__L4_L1» "value@4")) (plainIns0 97 [.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")] 87) [] 3
        97 103 ∨
      s ∈ [Stmt.atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "s2#0")) (.n (val% «keccak_plain_rounds__L4_L1» "nxt[8]@4"))), .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "s2#0[1]")) (.n (val% «keccak_plain_rounds__L4_L1» "nxt[9]@4"))),
        .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "s2#0[2]")) (.n (val% «keccak_plain_rounds__L4_L1» "nxt[10]@4"))), .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "s2#0[3]")) (.n (val% «keccak_plain_rounds__L4_L1» "nxt[11]@4"))),
        .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "s2#0[4]")) (.n (val% «keccak_plain_rounds__L4_L1» "nxt[12]@4"))), .atom (.const (.n (val% «keccak_plain_rounds__L4_L1» "s2#1")) (word 256 0)),
        .atom (.mul (.n (val% «keccak_plain_rounds__L4_L1» "s2#2")) (.n (val% «keccak_plain_rounds__L4_L1» "cursor")) (.n (val% «keccak_plain_rounds__L4_L1» "s2#1"))), .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "s2#0[5]")) (.n (val% «keccak_plain_rounds__L4_L1» "s2#2"))),
        .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "s2#0[6]")) (.n (val% «keccak_plain_rounds__L4_L1» "value@5"))),
        .ret [.n (val% «keccak_plain_rounds__L4_L1» "s2#0"), .n (val% «keccak_plain_rounds__L4_L1» "s2#0[1]"), .n (val% «keccak_plain_rounds__L4_L1» "s2#0[2]"), .n (val% «keccak_plain_rounds__L4_L1» "s2#0[3]"), .n (val% «keccak_plain_rounds__L4_L1» "s2#0[4]"), .n (val% «keccak_plain_rounds__L4_L1» "s2#0[5]"), .n (val% «keccak_plain_rounds__L4_L1» "s2#0[6]")]]) → s ∈ plain41T := by
    intro s hs
    simp only [plain41T, List.mem_append]
    tauto
  have gp := fun s hs ↦ g s (inT s (Or.inl hs))
  have g0 := fun s hs ↦ g s (inT s (Or.inr (Or.inl hs)))
  have g1 := fun s hs ↦ g s (inT s (Or.inr (Or.inr (Or.inl hs))))
  have g2 := fun s hs ↦ g s (inT s (Or.inr (Or.inr (Or.inr (Or.inl hs)))))
  have g3 := fun s hs ↦ g s (inT s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs))))))
  have gt := fun s hs ↦ g s (inT s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hs))))))
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true, GoodS, Good] at gp gt
  obtain ⟨c11, c12, c13, c14, c15, c16, c17⟩ := gp
  obtain ⟨c121, c122, c123, c124, c125, c126, m127, c128, c129⟩ := gt
  simp only [Nat.reduceLT, and_self, ↓reduceIte] at m127
  -- the zero cells
  have inMid0 : ∀ s ∈ plainMid41a, s ∈ plainRoundT (.n (val% «keccak_plain_rounds__L4_L1» "cursor")) (.n (val% «keccak_plain_rounds__L4_L1» "point")) (.n (val% «keccak_plain_rounds__L4_L1» "value@1"))
      ([.n (val% «keccak_plain_rounds__L4_L1» "rate[0]@1"), .n (val% «keccak_plain_rounds__L4_L1» "rate[1]@1"), .n (val% «keccak_plain_rounds__L4_L1» "rate[2]@1"), .n (val% «keccak_plain_rounds__L4_L1» "rate[3]@1"), .n (val% «keccak_plain_rounds__L4_L1» "rate[4]"), .n (val% «keccak_plain_rounds__L4_L1» "rate[5]")] ++ [.n (val% «keccak_plain_rounds__L4_L1» "rate[6]"), .n (val% «keccak_plain_rounds__L4_L1» "rate[7]")] ++ capV 11) plainMid41a 0 18
      26 := fun s hs ↦ by
    unfold plainRoundT
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs))
  have inMid1 : ∀ s ∈ plainMid41b, s ∈ plainRoundT (.n (val% «keccak_plain_rounds__L4_L1» "cursor")) (.n (val% «keccak_plain_rounds__L4_L1» "point")) (.n (val% «keccak_plain_rounds__L4_L1» "value@2"))
      (plainIns0 44 [.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")] 34) plainMid41b 1 44 55 := fun s hs ↦ by
    unfold plainRoundT
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs))
  have z24 : σ (.n (val% «keccak_plain_rounds__L4_L1» "rate[6]")) = word 0 0 :=
    g0 (.atom (.const (.n (val% «keccak_plain_rounds__L4_L1» "rate[6]")) (word 0 0))) (inMid0 _ (by simp [plainMid41a]))
  have z25 : σ (.n (val% «keccak_plain_rounds__L4_L1» "rate[7]")) = word 0 0 :=
    g0 (.atom (.const (.n (val% «keccak_plain_rounds__L4_L1» "rate[7]")) (word 0 0))) (inMid0 _ (by simp [plainMid41a]))
  have z51 : σ (.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]")) = word 0 0 :=
    g1 (.atom (.const (.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]")) (word 0 0))) (inMid1 _ (by simp [plainMid41b]))
  have z52 : σ (.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]")) = word 0 0 :=
    g1 (.atom (.const (.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]")) (word 0 0))) (inMid1 _ (by simp [plainMid41b]))
  have z53 : σ (.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]")) = word 0 0 :=
    g1 (.atom (.const (.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]")) (word 0 0))) (inMid1 _ (by simp [plainMid41b]))
  have z54 : σ (.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")) = word 0 0 :=
    g1 (.atom (.const (.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")) (word 0 0))) (inMid1 _ (by simp [plainMid41b]))
  have hz0 : [V.n (val% «keccak_plain_rounds__L4_L1» "rate[6]"), .n (val% «keccak_plain_rounds__L4_L1» "rate[7]")].map σ = [0, 0] := by
    simp only [List.map_cons, List.map_nil, z24, z25, word_zero]
  have hz : [V.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")].map σ = [0, 0, 0, 0] := by
    simp only [List.map_cons, List.map_nil, z51, z52, z53, z54, word_zero]
  have hmidA : ∀ s ∈ plainMid41a, ∃ d c, s = .atom (.const d c) := by
    intro s hs
    simp only [plainMid41a, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> exact ⟨_, _, rfl⟩
  have hmidB : ∀ s ∈ plainMid41b, ∃ d c, s = .atom (.const d c) := by
    intro s hs
    simp only [plainMid41b, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
  have hnil : ∀ s ∈ ([] : List Stmt), ∃ d c, s = .atom (.const d c) :=
    fun s hs ↦ absurd hs (by simp)
  have pF : ∀ j < 5, σ (.n ((val% «keccak_plain_rounds__L4_L1» "sp[0]") + j)) = [f0, f1, f2, f3, f4].getD j 0 := by
    intro j hj
    interval_cases j
    · rw [c11]; exact pp 0 (by norm_num)
    · rw [c12]; exact pp 1 (by norm_num)
    · rw [c13]; exact pp 2 (by norm_num)
    · rw [c14]; exact pp 3 (by norm_num)
    · rw [c15]; exact pp 4 (by norm_num)
  have e16 : σ (.n (val% «keccak_plain_rounds__L4_L1» "rate[0]@1")) = p0 := by rw [c16]; exact pp 5 (by norm_num)
  have e17 : σ (.n (val% «keccak_plain_rounds__L4_L1» "rate[1]@1")) = p1 := by rw [c17]; exact pp 6 (by norm_num)
  have hpw : (σ (.n (val% «keccak_plain_rounds__L4_L1» "rate[0]@1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "rate[1]@1"))) = Keccak.scalarCells wv dsObserve := by rw [e16, e17]; exact hwv
  -- the rounds
  have l00 : LoadHolds rd (σ (.n (val% «keccak_plain_rounds__L4_L1» "cursor"))) (2 * 0) a0 := by rw [p7]; exact rd' 0 (by norm_num)
  have l01 : LoadHolds rd (σ (.n (val% «keccak_plain_rounds__L4_L1» "cursor"))) (2 * 0 + 1) b0 := by rw [p7]; exact rd' 1 (by norm_num)
  have l10 : LoadHolds rd (σ (.n (val% «keccak_plain_rounds__L4_L1» "cursor"))) (2 * 1) a1 := by rw [p7]; exact rd' 2 (by norm_num)
  have l11 : LoadHolds rd (σ (.n (val% «keccak_plain_rounds__L4_L1» "cursor"))) (2 * 1 + 1) b1 := by rw [p7]; exact rd' 3 (by norm_num)
  have l20 : LoadHolds rd (σ (.n (val% «keccak_plain_rounds__L4_L1» "cursor"))) (2 * 2) a2 := by rw [p7]; exact rd' 4 (by norm_num)
  have l21 : LoadHolds rd (σ (.n (val% «keccak_plain_rounds__L4_L1» "cursor"))) (2 * 2 + 1) b2 := by rw [p7]; exact rd' 5 (by norm_num)
  have l30 : LoadHolds rd (σ (.n (val% «keccak_plain_rounds__L4_L1» "cursor"))) (2 * 3) a3 := by rw [p7]; exact rd' 6 (by norm_num)
  have l31 : LoadHolds rd (σ (.n (val% «keccak_plain_rounds__L4_L1» "cursor"))) (2 * 3 + 1) b3 := by rw [p7]; exact rd' 7 (by norm_num)
  obtain ⟨e18, e21, r0, v0, f0r⟩ := plainRound_complete (C := coreProgram.Rel rd) g0 (by decide)
    (by decide) hmidA (by omega) l00 l01
  obtain ⟨e44, e47, r1, v1, f1r⟩ := plainRound_complete (C := coreProgram.Rel rd) g1 (by decide)
    (by decide) hmidB (by omega) l10 l11
  obtain ⟨e73, e76, r2, v2, f2r⟩ := plainRound_complete (C := coreProgram.Rel rd) g2 (by decide)
    (by decide) hnil (by omega) l20 l21
  obtain ⟨e97, e100, r3, v3, f3r⟩ := plainRound_complete (C := coreProgram.Rel rd) g3 (by decide)
    (by decide) hnil (by omega) l30 l31
  -- the challenges and claims are `plainRun`'s
  have q0 := plain_core_sq1 (cap := [f0, f1, f2, f3, f4]) (w := wv) r0 hpw hz0 (by
    simp only [capV, List.map_cons, List.map_nil]
    rw [show (11 : ℕ) = 11 + 0 from rfl, pF 0 (by norm_num), pF 1 (by norm_num),
      pF 2 (by norm_num), pF 3 (by norm_num), pF 4 (by norm_num)]; rfl)
  have q1 := plain_core_sq0 (cap := [σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[8]@1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[9]@1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[10]@1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[11]@1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[12]@1"))]) r1 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q2 := plain_core_sq0 (cap := [σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[8]@2")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[9]@2")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[10]@2")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[11]@2")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[12]@2"))]) r2 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q3 := plain_core_sq0 (cap := [σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[8]@3")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[9]@3")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[10]@3")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[11]@3")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[12]@3"))])
    r3 hz (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  simp only [Nat.reduceAdd] at q0 q1 q2 q3 v0 v1 v2 v3
  rw [p8] at v0
  have hrunEq : plainRun [(a0, b0), (a1, b1), (a2, b2), (a3, b3)] value
      ⟨[f0, f1, f2, f3, f4], [(wv, dsObserve)]⟩ =
      ([σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[0]@1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[0]@2")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[0]@3")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[0]@4"))], σ (.n (val% «keccak_plain_rounds__L4_L1» "value@5")),
        ⟨[σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[8]@4")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[9]@4")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[10]@4")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[11]@4")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[12]@4"))], []⟩) := by
    rw [← e18, ← e21, ← e44, ← e47, ← e73, ← e76, ← e97, ← e100,
      plainRun_step q0.1.symm q0.2.symm v0.symm, plainRun_step q1.1.symm q1.2.symm v1.symm,
      plainRun_step q2.1.symm q2.2.symm v2.symm, plainRun_step q3.1.symm q3.2.symm v3.symm]
    rfl
  rw [hrunEq] at hpt hret
  have st : ∀ k (hk : k < 4), LoadHolds rd (σ (.n (val% «keccak_plain_rounds__L4_L1» "point"))) k ([σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[0]@1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[0]@2")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[0]@3")),
      σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[0]@4"))][k]'(by simpa using hk)) := fun k hk ↦ by
    rw [p9]; exact hpt k (by simpa using hk)
  -- the relation
  refine (rel_iff_sem find_plain41 _ _).mpr ⟨σ, ?_, ?_⟩
  · show [σ (.n (val% «keccak_plain_rounds__L4_L1» "fs0")), σ (.n (val% «keccak_plain_rounds__L4_L1» "fs1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "fs2")), σ (.n (val% «keccak_plain_rounds__L4_L1» "fs3")), σ (.n (val% «keccak_plain_rounds__L4_L1» "fs4")), σ (.n (val% «keccak_plain_rounds__L4_L1» "p0")), σ (.n (val% «keccak_plain_rounds__L4_L1» "p1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "cursor")),
      σ (.n (val% «keccak_plain_rounds__L4_L1» "value@1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "point")), σ (.n (val% «keccak_plain_rounds__L4_L1» "tabs"))] = l
    rw [pp 0 (by norm_num), pp 1 (by norm_num), pp 2 (by norm_num), pp 3 (by norm_num),
      pp 4 (by norm_num), pp 5 (by norm_num), pp 6 (by norm_num), pp 7 (by norm_num),
      pp 8 (by norm_num), pp 9 (by norm_num), pp 10 (by norm_num)]
    rfl
  show Stmt.HoldsList _ rd σ (fn% «keccak_plain_rounds__L4_L1»).body False (fun rs ↦ rs = rets)
  rw [body41]
  simp only [plain41T, holdsList_append, Stmt.HoldsList, Stmt.Holds]
  refine ⟨c11, c12, c13, c14, c15, c16, c17, f0r (st 0 (by norm_num)) (f1r (st 1 (by norm_num))
    (f2r (st 2 (by norm_num)) (f3r (st 3 (by norm_num))
    ⟨c121, c122, c123, c124, c125, c126, m127, c128, c129, ?_⟩)))⟩
  rw [hret]
  simp only [List.map_cons, List.map_nil, c121, c122, c123, c124, c125, c128, m127, c126, c129,
    p7, word_256, List.cons_append, List.nil_append]

end
end LeanVM.Guest.B1.VerifySub
