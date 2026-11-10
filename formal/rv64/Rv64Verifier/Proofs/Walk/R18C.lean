import Rv64Verifier.Proofs.Walk.R18B

/-!
# `walk` R18, the table claims: the mirror's steps and the inner loop's head

`tableClaimsRust` one table at a time (`tableClaims_take_succ`), and done when the six bases or the
evaluations run out (`tableClaims_take_done`). `InnerR18`: at the inner loop's head `0x80003894`,
`j` of table `k`'s values appended.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Bus

theorem zip_take_eq {α β : Type} (a : List α) (b : List β) (n : Nat) (h : n ≤ a.length) :
    a.zip (b.take n) = (a.zip b).take n := by
  induction a generalizing b n with
  | nil => simp
  | cons x a ih =>
    cases b with
    | nil => simp
    | cons y b =>
      cases n with
      | zero => simp
      | succ n => simp [ih b n (by simp at h; omega)]

/-- The claims of the first `k + 1` tables: the first `k`'s, then table `k`'s. -/
theorem tableClaims_take_succ (evs : List (List E × List E)) (k : Nat) (hk : k < 6)
    (hl : k < evs.length) :
    tableClaimsRust (evs.take (k + 1)) = tableClaimsRust (evs.take k) ++
      evs[k].2.zipIdx.map fun (value, column) ↦
        (⟨LayoutMirror.globalColumnBasesRust.getD k 0 + column, evs[k].1, value⟩ : ColumnClaim) := by
  have hb : LayoutMirror.globalColumnBasesRust.length = 6 := by rw [bases_val]; rfl
  simp only [tableClaimsRust]
  rw [zip_take_eq _ _ _ (by omega), zip_take_eq _ _ _ (by omega), List.take_add_one,
    List.flatMap_append, List.getElem?_eq_getElem (by simp; omega)]
  simp [List.getElem_zip, List.getElem?_eq_getElem (show k < LayoutMirror.globalColumnBasesRust.length by omega)]

/-- Six tables' claims are all of them. -/
theorem tableClaims_take_six (evs : List (List E × List E)) :
    tableClaimsRust (evs.take 6) = tableClaimsRust evs := by
  have hb : LayoutMirror.globalColumnBasesRust.length = 6 := by rw [bases_val]; rfl
  simp only [tableClaimsRust]
  rw [zip_take_eq _ _ _ (by omega), List.take_of_length_le (by simp; omega)]

theorem tableClaims_take_done (evs : List (List E × List E)) (k : Nat)
    (hk : k = evs.length ∨ k = 6) : tableClaimsRust (evs.take k) = tableClaimsRust evs := by
  rcases hk with rfl | rfl
  · rw [List.take_length]
  · exact tableClaims_take_six evs

/-- Table `k`'s claims: its values, each with its column and the table's point. -/
def tableClaimsOf (evs : List (List E × List E)) (k : Nat) : List ColumnClaim :=
  (evs.getD k ([], [])).2.zipIdx.map fun (value, column) ↦
    ⟨LayoutMirror.globalColumnBasesRust.getD k 0 + column, (evs.getD k ([], [])).1, value⟩

theorem tableClaims_succ (evs : List (List E × List E)) (k : Nat) (hk : k < 6)
    (hl : k < evs.length) :
    tableClaimsRust (evs.take (k + 1)) = tableClaimsRust (evs.take k) ++ tableClaimsOf evs k := by
  rw [tableClaims_take_succ evs k hk hl, tableClaimsOf, List.getD_eq_getElem _ _ hl]

/-- At `0x80003894`, `j` of table `k`'s `n` values appended (`n - j` left), the buffer having room
for all `n`. -/
structure InnerR18 (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ w t u : MachineState) (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64))
    (lir : BitVec 64) (bus : BusResultRust) (evs : List (List E × List E)) (k j : Nat)
    (P C L : Word) : Prop extends CoreR18 OI s u₀ w t u layout rows lir bus evs P C (L.toNat + j)
      (bus.claims ++ tableClaimsRust (evs.take k) ++ (tableClaimsOf evs k).take j) where
  pc : u.pc = 0x80003894
  hk : k < 6 ∧ k < evs.length
  hj : j < (evs.getD k ([], [])).2.length
  room : L.toNat + (evs.getD k ([], [])).2.length ≤ C.toNat
  x8 : u.getReg .x8 = 6
  x9 : u.getReg .x9 = 0xffffffffffffffff
  x18 : u.getReg .x18 = BitVec.ofNat 64 k
  x19 : u.getReg .x19 = s.getReg .x2 - 896
  x21 : u.getReg .x21 = s.getReg .x2 - 1312
  x22 : u.getReg .x22 = vecPtr t (s.getReg .x2 - 928) + 48 * vecLen t (s.getReg .x2 - 928)
  x23 : u.getReg .x23 = vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k)
  x20 : u.getReg .x20 = BitVec.ofNat 64 ((evs.getD k ([], [])).2.length - j)
  x24 : u.getReg .x24 = vecPtr t (vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k + 24)) +
    BitVec.ofNat 64 (24 * j)
  x25 : u.getReg .x25 = L + BitVec.ofNat 64 (evs.getD k ([], [])).2.length
  x26 : u.getReg .x26 = BitVec.ofNat 64 (LayoutMirror.globalColumnBasesRust.getD k 0 + j)
  x27 : u.getReg .x27 = P + BitVec.ofNat 64 (56 * (L.toNat + j))
  lenSlot : u.getMem (s.getReg .x2 - 1616) = L

section Core
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u v : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {P C : Word} {M : Nat}
  {cl : List ColumnClaim}

/-- A step writing frame bytes apart from the loop's slots keeps it. -/
theorem CoreR18.stepW (hpre : WalkPre s)
    (H : CoreR18 OI s u₀ w t u layout rows lir bus evs P C M cl) {W : Word → Prop}
    (st : StepW s u v W False)
    (hW : ∀ a, W a → InF s a ∧ ¬ KeepR s u₀ a ∧ ¬ Within a (tp s) 368)
    (hs : ∀ a, W a → ¬ Within a (s.getReg .x2 - 896) 48 ∧ ¬ Within a (s.getReg .x2 - 1632) 16 ∧
      ¬ Within a (s.getReg .x2 - 2472) 8) :
    CoreR18 OI s u₀ w t v layout rows lir bus evs P C M cl := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have fW : ∀ a, W a → InF s a := fun a ha ↦ (hW a ha).1
  have hm := st.mono
  have htm := H.tmono
  have hh := H.rest.inv.heap.hi
  have hN : heapNext u ≤ 2 ^ 63 := by simp only [heapNext, heapEnd] at hh ⊢; omega
  have gH : ∀ x : Word, x.toNat + 8 ≤ heapNext u → v.getMem x = u.getMem x :=
    fun x hx ↦ st.getH hpre fW hx
  have gF (k : Nat) (hk : 112 ≤ k ∧ k ≤ 2648)
      (hw : ∀ i < 8, ¬ W (s.getReg .x2 - BitVec.ofNat 64 k + BitVec.ofNat 64 i)) :
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 k) :=
    st.getF hpre (by addr_omega [hb1, hk]) hw fun hf ↦ hf.elim
  have hdr (i : Nat) (hi : i < M) (c : Nat) (hc : c ≤ 48) :
      (P + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 c).toNat + 8 ≤ heapNext u := by
    have b1 := H.buf.2.1; have b2 := H.len; addr_omega [hi, hc, hN, b1, b2]
  have pv (i : Nat) (hi : i < M) :
      vecPtr v (P + BitVec.ofNat 64 (56 * i)) = vecPtr u (P + BitVec.ofNat 64 (56 * i)) ∧
      vecLen v (P + BitVec.ofNat 64 (56 * i)) = vecLen u (P + BitVec.ofNat 64 (56 * i)) :=
    ⟨gH _ (hdr i hi 8 (by omega)), gH _ (hdr i hi 16 (by omega))⟩
  refine {
    rest := H.rest.stepW hpre (fun a ha ↦ ⟨(hW a ha).1, (hW a ha).2.1⟩) st
    smono := H.smono
    wmono := H.wmono
    umono := H.umono
    tmono := by omega
    evKept := fun x h1 h2 ↦ (gH x (by omega)).trans (H.evKept x h1 h2)
    rowsAt := H.rowsAt
    bases := fun i hi ↦ by
      have e : s.getReg .x2 - 896 + BitVec.ofNat 64 (8 * i) =
          s.getReg .x2 - BitVec.ofNat 64 (896 - 8 * i) := by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hi]
      rw [e, gF (896 - 8 * i) (by omega) fun j hj hw ↦ (hs _ hw).1 (by
        simp only [Within]; addr_omega [hb1, hi, hj]), ← e]
      exact H.bases i hi
    capSlot := by
      rw [show (1632 : Word) = BitVec.ofNat 64 1632 from rfl, gF 1632 (by omega) fun j hj hw ↦
        (hs _ hw).2.1 (by simp only [Within]; addr_omega [hb1, hj])]
      exact H.capSlot
    ptrSlot := by
      rw [show (1624 : Word) = BitVec.ofNat 64 1624 from rfl, gF 1624 (by omega) fun j hj hw ↦
        (hs _ hw).2.1 (by simp only [Within]; addr_omega [hb1, hj])]
      exact H.ptrSlot
    ptr184 := by
      rw [show (2472 : Word) = BitVec.ofNat 64 2472 from rfl, gF 2472 (by omega) fun j hj hw ↦
        (hs _ hw).2.2 (by simp only [Within]; addr_omega [hb1, hj])]
      exact H.ptr184
    proofPtr := by
      have etp : tp s = s.getReg .x2 - BitVec.ofNat 64 2448 := rfl
      rw [etp, gF 2448 (by omega) fun j hj hw ↦ (hW _ hw).2.2 (by
        rw [tp]; simp only [Within]; addr_omega [hb1, hj]), ← etp]
      exact H.proofPtr
    len := H.len
    buf := ⟨H.buf.1, by have := H.buf.2.1; omega, H.buf.2.2⟩
    claims := by
      rw [← H.claims]
      simp only [claimsIn]
      refine List.map_congr_left fun i hi ↦ ?_
      simp only [List.mem_range] at hi
      have hp := (H.points i hi).1
      simp only [Old] at hp
      have b1 := H.buf.2.1
      have b2 := H.len
      exact claimAt_congr' gH hN (by addr_omega [hi, hN, b1, b2]) (hp.imp_right fun h ↦ h.2.1)
    points := fun i hi ↦ by
      obtain ⟨e1, e2⟩ := pv i hi
      rw [e1, e2]
      exact ⟨(H.points i hi).1.imp_right fun h ↦ h.mono (by omega), (H.points i hi).2⟩
    tracks := H.tracks.keep fun T hT ↦ st.transcript hpre H.rest.inv H.proofPtr
      (fun a ha ↦ ⟨(hW a ha).1, (hW a ha).2.2⟩) hT }

end Core

end Rv64Verifier.Proofs.Walk
