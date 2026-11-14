/-
  LeanVM.Guest.B1.Sig.SphincsBytesComplete

  `sp_from_bytes` (`lean_ethereum.py:3926-3936`) is complete: its marks hinted
  as `g^v` for bytes `v`, on a memory of at least `256` words holding the byte table, its value is
  the word of the bytes' integer, and each byte's pointer is the table's at its mark.
-/

module

public import LeanVM.Guest.B1.Sig.KSeqComplete
public import LeanVM.Guest.B1.Sig.SphincsBytes

/-!
# `sp_from_bytes`, complete

* `byte_load`: the byte table's word at `g^v` is `v`'s word;
* `sByte_complete`: a byte mark `g^v`, `v < 256`, range checks and reads the word of `v`, its
  pointer `b + 4` the table's at `g^v`;
* `bFold`: base-256 folding; `sFromBytesRest_complete`, `sFromBytes_complete`: the folded value is
  the word of the bytes' integer, and every byte's pointer (`fbPtr`) is the table's at a byte;
* `sFromBytesRest_shape`, `sFromBytes_shape`: the bases, the value's number, its values below the
  end.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The byte table's word at `g^v`. -/
theorem byte_load {bb : E} (hbb : ByteBits rd bb) {v : Nat} (hv : v < 256) :
    LoadHolds rd (bb * ofK (addressOfIndex v)) 0 (word v 0) := by
  obtain ⟨hK, hl⟩ := hbb v hv
  have e : bb * ofK (addressOfIndex v) = ofK (bb.limb 0 * addressOfIndex v) := by
    rw [ofK_mul, ← eq_ofK_limb hK]
  refine ⟨(isInK_iff _).mpr ⟨_, e⟩, ?_⟩
  rw [e]
  simpa [addressOfIndex] using hl

theorem nb_mulS {d : Nat} {x y : V} (hx : NBv d x) (hy : NBv d y) :
    NumBelow (d + 1) (Stmt.valsList [mulS (.n d) x y]) := by
  simp only [mulS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
  exact .cons ⟨d, by omega, rfl⟩ (.cons (hx.mono' (by omega)) (.cons (hy.mono' (by omega)) (.nil _)))

theorem nb_addS {d : Nat} {x y : V} (hx : NBv d x) (hy : NBv d y) :
    NumBelow (d + 1) (Stmt.valsList [addS (.n d) x y]) := by
  simp only [addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
  exact .cons ⟨d, by omega, rfl⟩ (.cons (hx.mono' (by omega)) (.cons (hy.mono' (by omega)) (.nil _)))

theorem nb_cst (d : Nat) (c : E) : NumBelow (d + 1) (Stmt.valsList [cst d c]) := by
  simp only [cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
  exact .cons ⟨d, by omega, rfl⟩ (.nil _)

theorem nb_loadS {d : Nat} {p : V} (off : Nat) (hp : NBv d p) :
    NumBelow (d + 1) (Stmt.valsList [loadS (.n d) p off]) := by
  simp only [loadS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
  exact .cons ⟨d, by omega, rfl⟩ (.cons (hp.mono' (by omega)) (.nil _))

theorem rangeS_nb (x : V) (bound : E) (b : Nat) (hx : NBv b x) :
    NumBelow (b + 4) (Stmt.valsList (rangeS x bound b)) := by
  simp only [rangeS, cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
    List.cons_append, List.nil_append]
  exact .cons ⟨b, by omega, rfl⟩ (.cons (hx.mono' (by omega)) (.cons ⟨b + 1, by omega, rfl⟩
    (.cons ⟨b + 2, by omega, rfl⟩ (.cons ⟨b + 3, by omega, rfl⟩ (.cons ⟨b, by omega, rfl⟩ (.nil _))))))

theorem g255W_k : g255W = ofK (addressOfIndex (256 - 1)) := g255W_eq

theorem sByte_nb {mark : V} {b : Nat} (hmk : NBv b mark) :
    NumBelow (b + 6) (Stmt.valsList (sByte mark b)) := by
  rw [sByte, valsList_append, show [mulS (.n (b + 4)) (.n 1) mark, loadS (.n (b + 5)) (.n (b + 4)) 0] =
    [mulS (.n (b + 4)) (.n 1) mark] ++ [loadS (.n (b + 5)) (.n (b + 4)) 0] from rfl, valsList_append]
  exact ((rangeS_nb mark g255W b hmk).mono (by omega)).append
    (((nb_mulS (d := b + 4) ⟨1, by omega, rfl⟩ (hmk.mono' (by omega))).mono (by omega)).append
      (nb_loadS 0 ⟨b + 4, by omega, rfl⟩))

/-- A byte's pointer: the byte table at its mark. -/
def BytePtr (bb : E) (x : E) : Prop := ∃ v < 256, x = bb * ofK (addressOfIndex v)

/-- **A byte completes**: its mark `g^v`, `v < 256`, range checked and read off the table. -/
theorem sByte_complete (hm : MemOK rd 256) {bb : E} (hbb : ByteBits rd bb) {v : Nat}
    (hv : v < 256) (σ : Val) (h1 : σ (.n 1) = bb) {mark : V} {b : Nat} (hb : 2 ≤ b) (hmk : NBv b mark)
    (hmv : σ mark = ofK (addressOfIndex v)) :
    Completes C rd b (b + 6) (sByte mark b) σ
      (fun σ' => σ' (.n (b + 5)) = word v 0 ∧ BytePtr bb (σ' (.n (b + 4)))) := by
  rw [sByte, g255W_k]
  refine Completes.append (m := b + 4) (by omega) (by omega) (rangeS_nb mark _ b hmk)
    (rangeS_complete hm (le_refl 256) hv σ mark hmk hmv) (fun σ1 he1 _ => ?_)
  have e1 : σ1 (.n 1) = bb := by rw [he1.apply (Or.inl (by omega))]; exact h1
  have em : σ1 mark = ofK (addressOfIndex v) := by
    obtain ⟨j, hj, rfl⟩ := hmk
    rw [he1.apply (Or.inl hj)]
    exact hmv
  show Completes C rd (b + 4) (b + 6) ([mulS (.n (b + 4)) (.n 1) mark] ++
    [loadS (.n (b + 5)) (.n (b + 4)) 0]) σ1 _
  refine Completes.append (m := b + 5) (by omega) (by omega)
    (nb_mulS ⟨1, by omega, rfl⟩ (hmk.mono' (by omega)))
    (mulS_complete σ1 (b + 4) ⟨1, by omega, rfl⟩ (hmk.mono' (by omega))) (fun σ2 he2 hp2 => ?_)
  rw [e1, em] at hp2
  obtain ⟨σ3, he3, hp3, hh3⟩ := loadS_complete (C := C) σ2 (b + 5) ⟨b + 4, by omega, rfl⟩
    (by rw [hp2]; exact byte_load hbb (by omega))
  refine ⟨σ3, he3, ⟨hp3, v, by omega, ?_⟩, hh3⟩
  rw [he3.apply (Or.inl (by omega)), hp2]

/-- Base-256 folding of bytes onto `N`. -/
def bFold : Nat → List Nat → Nat
  | N, [] => N
  | N, v :: vs => bFold (256 * N + v) vs

/-- The pointer of byte `k` of `sp_from_bytes` from base `b`: the top one's at `b + 4`, then one
every nine. -/
def fbPtr (b k : Nat) : Nat := if k = 0 then b + 4 else b + 1 + 9 * k

theorem sFromBytesRest_shape : ∀ (ms : List V) (b : Nat) (val : V), (∀ m ∈ ms, NBv b m) → NBv b val →
    (sFromBytesRest ms b val).2.1 = b + 9 * ms.length ∧
      NBv (b + 9 * ms.length) (sFromBytesRest ms b val).2.2 ∧
      NumBelow (b + 9 * ms.length) (Stmt.valsList (sFromBytesRest ms b val).1)
  | [], b, val, _, hv => ⟨rfl, hv, .nil _⟩
  | m :: ms, b, val, hms, hv => by
      obtain ⟨r1, r2, r3⟩ := sFromBytesRest_shape ms (b + 9) (.n (b + 8))
        (fun x hx => (hms x (by simp [hx])).mono' (by omega)) ⟨b + 8, by omega, rfl⟩
      have hm : NBv b m := hms m (by simp)
      simp only [sFromBytesRest, List.length_cons]
      refine ⟨by rw [r1]; ring, by rw [show b + 9 * (ms.length + 1) = b + 9 + 9 * ms.length by ring]; exact r2, ?_⟩
      rw [show b + 9 * (ms.length + 1) = b + 9 + 9 * ms.length by ring, valsList_append, valsList_append]
      refine (((sByte_nb hm).mono (by omega)).append ?_).append r3
      show NumBelow _ (Stmt.valsList ([cst (b + 6) (word 256 0)] ++ [mulS (.n (b + 7)) val (.n (b + 6))] ++
        [addS (.n (b + 8)) (.n (b + 5)) (.n (b + 7))]))
      rw [valsList_append, valsList_append]
      exact ((((nb_cst (b + 6) _).mono (by omega)).append
        ((nb_mulS (d := b + 7) (hv.mono' (by omega)) ⟨b + 6, by omega, rfl⟩).mono (by omega))).append
        ((nb_addS (d := b + 8) ⟨b + 5, by omega, rfl⟩ ⟨b + 7, by omega, rfl⟩).mono (by omega)))

/-- **The bytes after the top one complete**: from the word of `N`, the word of the folding, each
byte's pointer at `b + 4 + 9 k` the table's. -/
theorem sFromBytesRest_complete (hm : MemOK rd 256) {bb : E} (hbb : ByteBits rd bb) :
    ∀ (ms : List V) (vs : List Nat) (b : Nat) (val : V) (N M : Nat) (σ : Val), 2 ≤ b →
      List.Forall₂ (fun m v => NBv b m ∧ σ m = ofK (addressOfIndex v) ∧ v < 256) ms vs →
      NBv b val → σ (.n 1) = bb → σ val = eOfNat N → N < M → M * 256 ^ ms.length ≤ 2 ^ 64 →
      Completes C rd b (b + 9 * ms.length) (sFromBytesRest ms b val).1 σ
        (fun σ' => σ' (sFromBytesRest ms b val).2.2 = eOfNat (bFold N vs) ∧
          ∀ k < ms.length, BytePtr bb (σ' (.n (b + 4 + 9 * k))))
  | [], vs, b, val, N, _, σ, _, hf, _, _, hv, _, _ => by
      cases hf
      refine (Completes.nil' (lo := b) (C := C) (rd := rd) (σ := σ) (Q := fun σ' => σ' val = eOfNat (bFold N []) ∧
        ∀ k < ([] : List V).length, BytePtr bb (σ' (.n (b + 4 + 9 * k)))) ?_).mono le_rfl (by omega)
        (fun _ h => h)
      exact ⟨hv, fun k hk => absurd hk (by simp)⟩
  | _ :: _, [], _, _, _, _, _, _, hf, _, _, _, _, _ => nomatch hf
  | m :: ms, v :: vs, b, val, N, M, σ, hb, .cons ⟨hmb, hmv, hv256⟩ hf', hval, h1, hv, hN, hM => by
      have e : sFromBytesRest (m :: ms) b val = (sByte m b ++ ([cst (b + 6) (word 256 0)] ++
          ([mulS (.n (b + 7)) val (.n (b + 6))] ++ ([addS (.n (b + 8)) (.n (b + 5)) (.n (b + 7))] ++
            (sFromBytesRest ms (b + 9) (.n (b + 8))).1))),
          (sFromBytesRest ms (b + 9) (.n (b + 8))).2.1, (sFromBytesRest ms (b + 9) (.n (b + 8))).2.2) := by
        simp [sFromBytesRest]
      rw [e, show b + 9 * (m :: ms).length = b + 9 + 9 * ms.length by simp; ring]
      dsimp only
      simp only [List.length_cons] at hM
      have hpow : 256 ^ (ms.length + 1) = 256 ^ ms.length * 256 := pow_succ _ _
      have hM1 : 1 ≤ 256 ^ ms.length := Nat.one_le_pow _ _ (by norm_num)
      have hM256 : M * 256 ≤ 2 ^ 64 := by rw [hpow] at hM; nlinarith
      refine Completes.append (m := b + 6)
        (P := fun σ' => σ' (.n (b + 5)) = word v 0 ∧ BytePtr bb (σ' (.n (b + 4)))) (by omega) (by omega)
        (sByte_nb hmb) (sByte_complete hm hbb hv256 σ h1 hb hmb hmv)
        (fun σ1 he1 ⟨hp1, hq1⟩ => ?_)
      refine Completes.append (m := b + 7) (by omega) (by omega) (nb_cst (b + 6) _)
        (cst_complete σ1 (b + 6) _) (fun σ2 he2 hp2 => ?_)
      refine Completes.append (m := b + 8) (by omega) (by omega)
        (nb_mulS (d := b + 7) (hval.mono' (by omega)) ⟨b + 6, by omega, rfl⟩)
        (mulS_complete σ2 (b + 7) (hval.mono' (by omega)) ⟨b + 6, by omega, rfl⟩) (fun σ3 he3 hp3 => ?_)
      refine Completes.append (m := b + 9) (by omega) (by omega)
        (nb_addS (d := b + 8) ⟨b + 5, by omega, rfl⟩ ⟨b + 7, by omega, rfl⟩)
        (addS_complete σ3 (b + 8) ⟨b + 5, by omega, rfl⟩ ⟨b + 7, by omega, rfl⟩) (fun σ4 he4 hp4 => ?_)
      have tr : ∀ k < b, σ4 (.n k) = σ (.n k) := fun k hk => by
        rw [he4.apply (Or.inl (by omega)), he3.apply (Or.inl (by omega)), he2.apply (Or.inl (by omega)),
          he1.apply (Or.inl (by omega))]
      have v5 : σ3 (.n (b + 5)) = word v 0 := by
        rw [he3.apply (Or.inl (by omega)), he2.apply (Or.inl (by omega))]; exact hp1
      have p4 : BytePtr bb (σ4 (.n (b + 4))) := by
        rw [he4.apply (Or.inl (by omega)), he3.apply (Or.inl (by omega)), he2.apply (Or.inl (by omega))]
        exact hq1
      have vv : σ2 val = σ val := by
        obtain ⟨j, hj, rfl⟩ := hval
        rw [he2.apply (Or.inl (by omega)), he1.apply (Or.inl (by omega))]
      have v8 : σ4 (.n (b + 8)) = eOfNat (256 * N + v) := by
        rw [hp4, v5, hp3, vv, hp2, hv, word_eq_eOfNat v, word256_eq, mul_comm,
          eOfNat_two_pow_mul (by omega), add_comm, Value.eOfNat_add_of_lt (by omega)]
        norm_num
      have h14 : σ4 (.n 1) = bb := by rw [tr 1 (by omega)]; exact h1
      have hc := sFromBytesRest_complete hm hbb ms vs (b + 9) (.n (b + 8)) (256 * N + v) (M * 256) σ4
        (by omega) (List.Forall₂.imp (fun x y ⟨g1, g2, g3⟩ => ⟨g1.mono' (by omega), by
          obtain ⟨j, hj, rfl⟩ := g1; rw [tr j hj]; exact g2, g3⟩) hf') ⟨b + 8, by omega, rfl⟩ h14 v8
        (by omega) (by rw [hpow] at hM; linarith)
      refine (hc.keep (Q := fun σ' => BytePtr bb (σ' (.n (b + 4))))
        (Q' := fun σ' => BytePtr bb (σ' (.n (b + 4)))) p4
        (fun σ' he _ => by rw [he.apply (Or.inl (by omega))]; exact p4)).mono le_rfl le_rfl ?_
      rintro σ' ⟨⟨q1, q2⟩, q3⟩
      refine ⟨q1, fun k hk => ?_⟩
      rcases k with _ | k
      · simpa using q3
      · have := q2 k (by simpa using hk)
        rwa [show b + 9 + 4 + 9 * k = b + 4 + 9 * (k + 1) by ring] at this

theorem sFromBytes_shape (top : V) (rest : List V) (b : Nat) (ht : NBv b top)
    (hr : ∀ m ∈ rest, NBv b m) :
    (sFromBytes top rest b).2.1 = b + 6 + 9 * rest.length ∧
      NBv (b + 6 + 9 * rest.length) (sFromBytes top rest b).2.2 ∧
      NumBelow (b + 6 + 9 * rest.length) (Stmt.valsList (sFromBytes top rest b).1) := by
  obtain ⟨r1, r2, r3⟩ := sFromBytesRest_shape rest (b + 6) (.n (b + 5))
    (fun m hm => (hr m hm).mono' (by omega)) ⟨b + 5, by omega, rfl⟩
  refine ⟨r1, r2, ?_⟩
  show NumBelow _ (Stmt.valsList (sByte top b ++ (sFromBytesRest rest (b + 6) (.n (b + 5))).1))
  rw [valsList_append]
  exact ((sByte_nb ht).mono (by omega)).append r3

/-- **`sp_from_bytes` completes**: the top mark `g^v0`, the others bytes, the value the word of
the bytes' integer, every byte's pointer the table's. -/
theorem sFromBytes_complete (hm : MemOK rd 256) {bb : E} (hbb : ByteBits rd bb) {v0 : Nat}
    (hv0 : v0 < 256) (top : V) (rest : List V) (vs : List Nat) (b : Nat) (σ : Val)
    (hb : 2 ≤ b) (ht : NBv b top) (htv : σ top = ofK (addressOfIndex v0))
    (hf : List.Forall₂ (fun m v => NBv b m ∧ σ m = ofK (addressOfIndex v) ∧ v < 256) rest vs)
    (h1 : σ (.n 1) = bb) (hM : 256 * 256 ^ rest.length ≤ 2 ^ 64) :
    Completes C rd b (b + 6 + 9 * rest.length) (sFromBytes top rest b).1 σ
      (fun σ' => σ' (sFromBytes top rest b).2.2 = eOfNat (bFold v0 vs) ∧
        ∀ k ≤ rest.length, BytePtr bb (σ' (.n (fbPtr b k)))) := by
  show Completes C rd b (b + 6 + 9 * rest.length)
    (sByte top b ++ (sFromBytesRest rest (b + 6) (.n (b + 5))).1) σ
    (fun σ' => σ' (sFromBytesRest rest (b + 6) (.n (b + 5))).2.2 = eOfNat (bFold v0 vs) ∧
      ∀ k ≤ rest.length, BytePtr bb (σ' (.n (fbPtr b k))))
  refine Completes.append (m := b + 6) (by omega) (by omega) (sByte_nb ht)
    (sByte_complete hm hbb hv0 σ h1 hb ht htv) (fun σ1 he1 ⟨hp1, hq1⟩ => ?_)
  have tr : ∀ k < b, σ1 (.n k) = σ (.n k) := fun k hk => he1.apply (Or.inl hk)
  have hc := sFromBytesRest_complete (C := C) hm hbb rest vs (b + 6) (.n (b + 5)) v0 256 σ1 (by omega)
    (List.Forall₂.imp (fun x y ⟨g1, g2, g3⟩ => ⟨g1.mono' (by omega), by
      obtain ⟨j, hj, rfl⟩ := g1; rw [tr j hj]; exact g2, g3⟩) hf) ⟨b + 5, by omega, rfl⟩
    (by rw [tr 1 (by omega)]; exact h1) (by rw [hp1, word_eq_eOfNat]) hv0 hM
  refine (hc.keep (Q := fun σ' => BytePtr bb (σ' (.n (b + 4))))
    (Q' := fun σ' => BytePtr bb (σ' (.n (b + 4)))) hq1
    (fun σ' he _ => by rw [he.apply (Or.inl (by omega))]; exact hq1)).mono le_rfl le_rfl ?_
  rintro σ' ⟨⟨q1, q2⟩, q3⟩
  refine ⟨q1, fun k hk => ?_⟩
  rcases k with _ | k
  · simpa [fbPtr] using q3
  · have := q2 k (by omega)
    rwa [show b + 6 + 4 + 9 * k = fbPtr b (k + 1) by simp [fbPtr]; ring] at this

end
end LeanVM.Guest.B1.Sig
