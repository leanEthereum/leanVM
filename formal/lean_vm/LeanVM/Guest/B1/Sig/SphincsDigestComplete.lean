/-
  LeanVM.Guest.B1.Sig.SphincsDigestComplete

  The message and `H_msg` of `verify_sig_lean_sphincs` (`lean_ethereum.py:4142-4157`) are complete: the claim's keys and message cells loaded, the randomizer hinted and both
  calls hashed.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsBytesComplete
public import LeanVM.Guest.B1.Sig.SphincsSoundDigest
public import LeanVM.Guest.B1.Sig.CwComplete
public import LeanVM.Guest.B1.Sig.KMsgComplete

/-!
# The message and `H_msg`, complete

* `bFold_desc`, `sFromMarks_complete`: `sp_from_bytes` of bytes hinted from a number's;
* `sMsg_complete`: the claim's four cells, the keys and the message;
* `sDigests_complete`: the randomizer and `H_msg`'s two calls on `R | PK.seed | PK.root | M | BE_32(i)`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## `sp_from_bytes` of a number's bytes -/

/-- Folding a number's bytes high first. -/
theorem bFold_desc (X : Nat) :
    ∀ (m acc : Nat), bFold acc ((List.range m).reverse.map fun k => X / 256 ^ k % 256) =
      acc * 256 ^ m + X % 256 ^ m
  | 0, acc => by simp [bFold, Nat.mod_one]
  | m + 1, acc => by
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_cons, bFold, bFold_desc X m]
      rw [show (256 : Nat) ^ (m + 1) = 256 ^ m * 256 by ring, Nat.mod_mul]
      ring

/-- **`sp_from_bytes` of `n ≤ 8` bytes hinted from `X`'s low bytes completes**: the value `X`'s low
`n` bytes, every byte's pointer the table's. -/
theorem sFromMarks_complete (hm : MemOK rd 256) {bb : E} (hbb : ByteBits rd bb) {b n x X : Nat}
    (hn : 1 ≤ n) (hn8 : n ≤ 8) (σ : Val) (hx : 2 ≤ x) (hbx : b + n ≤ x)
    (hmk : ∀ t < n, σ (.n (b + t)) = ofK (addressOfIndex (X / 256 ^ t % 256))) (h1 : σ (.n 1) = bb) :
    Completes C rd x (x + 6 + 9 * (n - 1)) (sFromMarks b n x).1 σ
      (fun σ' => σ' (sFromMarks b n x).2.2 = eOfNat (X % 256 ^ n) ∧
        ∀ k ≤ n - 1, BytePtr bb (σ' (.n (fbPtr x k)))) := by
  have hl : (sMarks b n).2.length = n - 1 := by simp [sMarks]
  have hc := sFromBytes_complete (C := C) hm hbb (v0 := X / 256 ^ (n - 1) % 256) (Nat.mod_lt _ (by norm_num))
    (sMarks b n).1 (sMarks b n).2 ((List.range (n - 1)).reverse.map fun k => X / 256 ^ k % 256) x σ hx
    ⟨b + n - 1, by omega, rfl⟩ (by rw [show (sMarks b n).1 = .n (b + (n - 1)) by simp [sMarks]; omega,
      hmk _ (by omega)])
    (by
      simp only [sMarks, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine List.forall₂_same.mpr fun k hk => ⟨⟨b + k, by simp at hk; omega, rfl⟩,
        hmk k (by simp at hk; omega), Nat.mod_lt _ (by norm_num)⟩)
    h1 (by
      rw [hl, ← pow_succ']
      exact le_trans (Nat.pow_le_pow_right (by norm_num) (show n - 1 + 1 ≤ 8 by omega)) (by norm_num))
  rw [hl] at hc
  refine hc.mono le_rfl le_rfl fun σ' ⟨h1', h2'⟩ => ⟨?_, h2'⟩
  rw [show sFromMarks b n x = sFromBytes (sMarks b n).1 (sMarks b n).2 x from rfl, h1', bFold_desc,
    show (256 : Nat) ^ n = 256 ^ (n - 1) * 256 by rw [← pow_succ]; congr 1; omega, Nat.mod_mul,
    Nat.add_comm, Nat.mul_comm (X / 256 ^ (n - 1) % 256)]

/-! ## The message -/

/-- **The claim's cells load**: `PK.seed`, `PK.root` and the message's two cells, as the claim holds
them. -/
theorem sMsg_complete {p Pc Rc M0c M1c : E} (hcl : ClaimAt rd p Pc Rc M0c M1c) (σ : Val)
    (h0 : σ (.n 0) = p) :
    Completes C rd 2 6 sMsg σ (fun σ' => σ' sPP = Pc ∧ σ' sRoot = Rc ∧ σ' sM0 = M0c ∧ σ' sM1 = M1c) := by
  obtain ⟨c0, c1, c2, c3⟩ := hcl
  unfold sMsg
  refine Completes.load ⟨0, by norm_num, rfl⟩ (w := Pc) (by rw [h0]; exact c0) (by norm_num)
    (fun σ1 he1 e1 => ?_)
  have p1 : σ1 (.n 0) = p := by rw [he1.apply (Or.inl (by norm_num)), h0]
  refine Completes.load ⟨0, by norm_num, rfl⟩ (w := Rc) (by rw [p1]; exact c1) (by norm_num)
    (fun σ2 he2 e2 => ?_)
  have p2 : σ2 (.n 0) = p := by rw [he2.apply (Or.inl (by norm_num)), p1]
  refine Completes.load ⟨0, by norm_num, rfl⟩ (w := M0c) (by rw [p2]; exact c2) (by norm_num)
    (fun σ3 he3 e3 => ?_)
  have p3 : σ3 (.n 0) = p := by rw [he3.apply (Or.inl (by norm_num)), p2]
  refine Completes.load ⟨0, by norm_num, rfl⟩ (w := M1c) (by rw [p3]; exact c3) (by norm_num)
    (fun σ4 he4 e4 => ?_)
  refine Completes.nil' ⟨?_, ?_, ?_, e4⟩
  · rw [show sPP = .n 2 from rfl, he4.apply (Or.inl (by norm_num)), he3.apply (Or.inl (by norm_num)),
      he2.apply (Or.inl (by norm_num))]; exact e1
  · rw [show sRoot = .n 3 from rfl, he4.apply (Or.inl (by norm_num)), he3.apply (Or.inl (by norm_num))]
    exact e2
  · rw [show sM0 = .n 4 from rfl, he4.apply (Or.inl (by norm_num))]; exact e3

/-! ## `H_msg` -/

theorem word_ctr_one : word (2 ^ 24) 0 + word (2 ^ 32) 0 = word (1 * 2 ^ 24 + 2 ^ 32) 0 := by
  rw [← word_ctr_pad (i := 1) (by norm_num), one_mul]

/-- The statements before `H_msg`'s first `KECCAK`: its tail run, the `0x80`, the padding run. -/
def hPre0 : List Stmt :=
  [copyS (.n 7) sM1, cst 8 (word (2 ^ 32) 0), cst 9 (word 0 0), cst 10 (word 0 0),
    cst 11 (word (2 ^ 63) 0)] ++ padRun sPad

/-- Between the two calls: the second's counter cell with the `0x01`, its tail run, the `0x80`. -/
def hPre1 : List Stmt :=
  [cst 19 (word (2 ^ 24) 0), cst 20 (word (2 ^ 32) 0), addS (.n 21) (.n 19) (.n 20), copyS (.n 22) sM1,
    copyS (.n 23) (.n 21), cst 24 (word 0 0), cst 25 (word 0 0), cst 26 (word (2 ^ 63) 0)]

theorem sDigests_eq : sDigests = hintW "sp_rand" [sRand] :: (hPre0 ++
    ([kecS (sHIns 7) (runV 17 2) false false] ++ (hPre1 ++ [kecS (sHIns 22) (runV 27 1) false false]))) := by
  simp [sDigests, hPre0, hPre1]

theorem hPre0_ok : SeqOK 7 hPre0 17 := seqB_ok (by decide +kernel)
theorem hPre1_ok : SeqOK 19 hPre1 27 := seqB_ok (by decide +kernel)

/-- What `H_msg`'s calls give: the randomizer, the padding run and both calls' outputs. -/
def DigestsPost (σ : Val) (Rho : E) : Prop :=
  σ sRand = Rho ∧ PadOK σ sPad ∧ (σ sHm0, σ sHm0b) = hcellLen (hmsgCells σ 0) 84 ∧
    σ sHm1 = (hcellLen (hmsgCells σ 1) 84).1

/-- **`H_msg`'s two calls complete**: the randomizer hinted, both calls hashed. -/
theorem sDigests_complete {Rho : E} (σ : Val) :
    Completes C rd 6 28 sDigests σ (fun σ' => DigestsPost σ' Rho) := by
  rw [sDigests_eq]
  refine Completes.reload (σr := Function.update σ sRand Rho) (fun v hv =>
    Function.update_of_ne (hv 6 le_rfl (by norm_num)) _ _) ?_
  set σr := Function.update σ sRand Rho with hσr
  have rr : σr sRand = Rho := Function.update_self ..
  have rlow : ∀ k < 6, σr (.n k) = σ (.n k) := fun k hk =>
    Function.update_of_ne (by simp [sRand]; omega) _ _
  refine Completes.append (xs := [hintW "sp_rand" [sRand]]) (m := 7) (by norm_num) (by norm_num)
    (by rw [valsList_hint]; exact numBelow_of_all (by decide)) (hintKeep_complete _ _ _ _ _)
    (fun σ1 _ e1 => ?_)
  subst e1
  refine Completes.seq (m := 17) hPre0_ok (by norm_num) (fun σ2 he2 hh2 => ?_)
  have t2 : ∀ k < 7, σ2 (.n k) = σr (.n k) := fun k hk => he2.apply (Or.inl hk)
  have c : ∀ (k : Nat) (w : E), Stmt.atom (.const (.n k) w) ∈ hPre0 → σ2 (.n k) = w := fun k w hm => hh2.atom hm
  have p0 := c 12 (word 1 0) (by simp [hPre0, padRun, sPad, cst, List.range_succ])
  have p1 := (c 13 (word 0 0) (by simp [hPre0, padRun, sPad, cst, List.range_succ])).trans word_zero
  have p2 := (c 14 (word 0 0) (by simp [hPre0, padRun, sPad, cst, List.range_succ])).trans word_zero
  have p3 := (c 15 (word 0 0) (by simp [hPre0, padRun, sPad, cst, List.range_succ])).trans word_zero
  have p4 := (c 16 (word 0 0) (by simp [hPre0, padRun, sPad, cst, List.range_succ])).trans word_zero
  have k0 := c 8 (word (2 ^ 32) 0) (by simp [hPre0, cst])
  have k1 := (c 9 (word 0 0) (by simp [hPre0, cst])).trans word_zero
  have k1' := (c 10 (word 0 0) (by simp [hPre0, cst])).trans word_zero
  have k2 := c 11 (word (2 ^ 63) 0) (by simp [hPre0, cst])
  have c7 : σ2 (.n 7) = σ2 sM1 := hh2.atom (a := .copy (.n 7) sM1) (by simp [hPre0, copyS])
  have s2 : ∀ k < 6, σ2 (.n k) = σ (.n k) := fun k hk => by rw [t2 k (by omega), rlow k hk]
  have s2r : σ2 sRand = Rho := by rw [show sRand = .n 6 from rfl, t2 6 (by norm_num)]; exact rr
  have hpad2 : PadOK σ2 sPad := ⟨p0, p1, p2, p3, p4⟩
  refine Completes.append (xs := [kecS (sHIns 7) (runV 17 2) false false]) (m := 19) (by norm_num)
    (by norm_num) (numBelow_of_all (by decide))
    (kecS_complete (C := C) (rd := rd) σ2 (ins := sHIns 7) 17 (.inr (.inl rfl)) rfl
      (fun v hv => nbB_ok (List.all_eq_true.mp (by decide : (sHIns 7).all (nbB 17) = true) v hv))
      false false).withHolds (fun σ3 he3 ⟨_, hh3⟩ => ?_)
  have t3 : ∀ k < 17, σ3 (.n k) = σ2 (.n k) := fun k hk => he3.apply (Or.inl hk)
  have hk3 : AtomsHold rd σ3 [kecS (sHIns 7) (runV 17 2) false false] :=
    atomsHold_of_holdsList rfl hh3
  have d0 : (σ3 (.n 17), σ3 (.n (17 + 1))) = hcellLen [σ2 sRand, σ2 sPP, σ2 sRoot, σ2 sM0, σ2 sM1,
      word (0 * 2 ^ 24) 0] 84 := by
    have hr0 : ∀ k < 9, σ3 ((sHIns 7).getD k (.n 0)) = [σ2 sRand, σ2 sPP, σ2 sRoot, σ2 sM0, σ2 sM1,
        word (0 * 2 ^ 24 + 2 ^ 32) 0, 0, 0, word (2 ^ 63) 0].getD k 0 := by
      intro k hk
      interval_cases k <;> simp only [sHIns, List.getD_cons_zero, List.getD_cons_succ] <;>
        first
          | (rw [show sRand = .n 6 from rfl, t3 _ (by norm_num)])
          | (rw [show sPP = .n 2 from rfl, t3 _ (by norm_num)])
          | (rw [show sRoot = .n 3 from rfl, t3 _ (by norm_num)])
          | (rw [show sM0 = .n 4 from rfl, t3 _ (by norm_num)])
          | (rw [t3 _ (by norm_num), c7])
          | (rw [t3 _ (by norm_num), k0]; norm_num)
          | (rw [t3 _ (by norm_num), k1]) | (rw [t3 _ (by norm_num), k1'])
          | (rw [t3 _ (by norm_num), k2])
    have hc0 : ∀ k, 9 ≤ k → k < 13 → σ3 ((sHIns 7).getD k (.n 0)) = 0 := by
      intro k hk1 hk2
      interval_cases k <;> simp only [sHIns, sPad, List.getD_cons_zero, List.getD_cons_succ] <;>
        first
          | (rw [t3 _ (by norm_num), p1])
          | (rw [t3 _ (by norm_num), p2])
          | (rw [t3 _ (by norm_num), p3])
          | (rw [t3 _ (by norm_num), p4])
    exact Prod.ext ((kec84_sound (i := 0) (by norm_num) hk3 hr0 hc0).1 (by norm_num))
      ((kec84_sound (i := 0) (by norm_num) hk3 hr0 hc0).2 (by norm_num))
  refine Completes.seq (m := 27) hPre1_ok (by norm_num) (fun σ4 he4 hh4 => ?_)
  have t43 : ∀ k < 19, σ4 (.n k) = σ3 (.n k) := fun k hk => he4.apply (Or.inl hk)
  have t4 : ∀ k < 17, σ4 (.n k) = σ2 (.n k) := fun k hk => by
    rw [t43 k (by omega), t3 k hk]
  have e : ∀ (k : Nat) (w : E), Stmt.atom (.const (.n k) w) ∈ hPre1 → σ4 (.n k) = w := fun k w hm => hh4.atom hm
  have e30 := e 19 (word (2 ^ 24) 0) (by simp [hPre1, cst])
  have e31 := e 20 (word (2 ^ 32) 0) (by simp [hPre1, cst])
  have e35 := (e 24 (word 0 0) (by simp [hPre1, cst])).trans word_zero
  have e36 := (e 25 (word 0 0) (by simp [hPre1, cst])).trans word_zero
  have e37 := e 26 (word (2 ^ 63) 0) (by simp [hPre1, cst])
  have a32 : σ4 (.n 21) = σ4 (.n 19) + σ4 (.n 20) := hh4.atom (a := .add (.n 21) _ _) (by simp [hPre1, addS])
  have c33 : σ4 (.n 22) = σ4 sM1 := hh4.atom (a := .copy (.n 22) sM1) (by simp [hPre1, copyS])
  have c34 : σ4 (.n 23) = σ4 (.n 21) := hh4.atom (a := .copy (.n 23) (.n 21)) (by simp [hPre1, copyS])
  have v34 : σ4 (.n 23) = word (1 * 2 ^ 24 + 2 ^ 32) 0 := by rw [c34, a32, e30, e31, word_ctr_one]
  obtain ⟨σ5, he5, -, hh5⟩ := kecS_complete (C := C) (rd := rd) σ4 (ins := sHIns 22) 27 (.inl rfl) rfl
    (fun v hv => nbB_ok (List.all_eq_true.mp (by decide : (sHIns 22).all (nbB 27) = true) v hv))
    false false
  have hk5 : AtomsHold rd σ5 [kecS (sHIns 22) (runV 27 1) false false] :=
    atomsHold_of_holdsList rfl (hh5 True (fun _ => True) trivial)
  have t5 : ∀ k < 27, σ5 (.n k) = σ4 (.n k) := fun k hk => he5.apply (Or.inl hk)
  have u : ∀ k < 17, σ5 (.n k) = σ2 (.n k) := fun k hk => by rw [t5 k (by omega), t4 k (by omega)]
  have d1 : σ5 (.n 27) = (hcellLen [σ2 sRand, σ2 sPP, σ2 sRoot, σ2 sM0, σ2 sM1,
      word (1 * 2 ^ 24) 0] 84).1 := by
    refine (kec84_sound (i := 1) (by norm_num) hk5 (fun k hk => ?_) (fun k hk1 hk2 => ?_)).1 le_rfl
    · interval_cases k <;> simp only [sHIns, List.getD_cons_zero, List.getD_cons_succ] <;>
        first
          | (rw [show sRand = .n 6 from rfl, u _ (by norm_num)])
          | (rw [show sPP = .n 2 from rfl, u _ (by norm_num)])
          | (rw [show sRoot = .n 3 from rfl, u _ (by norm_num)])
          | (rw [show sM0 = .n 4 from rfl, u _ (by norm_num)])
          | (rw [t5 _ (by norm_num), c33, show sM1 = .n 5 from rfl, t4 _ (by norm_num)])
          | (rw [t5 _ (by norm_num), v34]) | (rw [t5 _ (by norm_num), e35])
          | (rw [t5 _ (by norm_num), e36]) | (rw [t5 _ (by norm_num), e37])
    · interval_cases k <;> simp only [sHIns, sPad, List.getD_cons_zero, List.getD_cons_succ] <;>
        first
          | (rw [u _ (by norm_num), p1])
          | (rw [u _ (by norm_num), p2])
          | (rw [u _ (by norm_num), p3])
          | (rw [u _ (by norm_num), p4])
  have hcells : ∀ i, hmsgCells σ5 i = [σ2 sRand, σ2 sPP, σ2 sRoot, σ2 sM0, σ2 sM1, word (i * 2 ^ 24) 0] := by
    intro i
    simp only [hmsgCells, show sRand = .n 6 from rfl, show sPP = .n 2 from rfl, show sRoot = .n 3 from rfl,
      show sM0 = .n 4 from rfl, show sM1 = .n 5 from rfl]
    rw [u 6 (by norm_num), u 2 (by norm_num), u 3 (by norm_num), u 4 (by norm_num), u 5 (by norm_num)]
  refine ⟨σ5, he5, ⟨?_, ?_, ?_, ?_⟩, hh5⟩
  · rw [show sRand = .n 6 from rfl, u _ (by norm_num)]; exact s2r
  · exact ⟨by rw [u _ (by simp [sPad])]; exact p0, by rw [u _ (by simp [sPad])]; exact p1,
      by rw [u _ (by simp [sPad])]; exact p2, by rw [u _ (by simp [sPad])]; exact p3,
      by rw [u _ (by simp [sPad])]; exact p4⟩
  · rw [hcells, show sHm0 = .n 17 from rfl, show sHm0b = .n 18 from rfl, t5 _ (by norm_num),
      t5 _ (by norm_num), t43 _ (by norm_num), t43 _ (by norm_num)]
    exact d0
  · rw [hcells, show sHm1 = .n 27 from rfl]
    exact d1

end
end LeanVM.Guest.B1.Sig
