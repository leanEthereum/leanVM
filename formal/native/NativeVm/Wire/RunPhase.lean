module

public import NativeVm.Wire.RunStream
public import NativeVm.Wire.RunSort
public import NativeVm.Wire.RunRows
public import NativeVm.Wire.RunLeaves
public import NativeVm.Wire.RunClimb
public import NativeVm.Wire.RunOutput

/-!
# A phase

`checks` fails exactly where `readPhase`'s bounds fail (`checks_ok`), `header` writes the phase's
three counts (`header_ok`), and `phase` decodes a phase into the decoded area as `phaseM`
(`phase_ok`), from its pieces: the queries, the distinct positions (`sortQ_ok`), the rows
(`rows_ok`), the leaves' digests (`leafHashes_ok`), the climb (`climb_ok`) and the openings
(`output_ok`).
-/

@[expose] public section

namespace NativeVm.Wire

open Native Native.Keccak Native.Keccak.Proof LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Wire
open Native.SphincsVerifier (toUInt64_add toUInt64_sub toUInt64_shl)

theorem Tab.same {W W' : Nat → UInt64} {S : Nat → Prop} {b : Nat} {l : List UInt64} (h : Tab W b l)
    (hs : Same S W W') (hd : ∀ i < l.length, ¬ S (b + i)) : Tab W' b l := fun i hi ↦ by
  rw [hs _ (hd i hi)]; exact h i hi

theorem LeafTab.same {W W' : Nat → UInt64} {S : Nat → Prop} {leaves : List (List K)} {lw : Nat}
    (h : LeafTab W leaves lw) (hs : Same S W W')
    (hd : ∀ i < leaves.length, ∀ t < lw, ¬ S (wLeaf + 64 * i + t)) : LeafTab W' leaves lw :=
  fun i hi t ht ↦ by rw [hs _ (hd i hi t ht)]; exact h i hi t ht

/-- The decoded phase `po` at word `base` of the decoded area, as `Decoded` says. -/
def PhaseAt (D : Nat → UInt64) (base : Nat) (po : PhaseOut) : Prop :=
  po.height ≤ wireMaxHeight ∧ po.leafWords ≤ wireMaxLeafWords ∧
    po.openings.length ≤ wireMaxQueries ∧ D base = po.openings.length.toUInt64 ∧
    D (base + 1) = po.height.toUInt64 ∧ D (base + 2) = po.leafWords.toUInt64 ∧
    ∀ j (hj : j < po.openings.length),
      let o := po.openings[j]
      let ob := base + 3 + j * openingWords
      o.leaf.length = po.leafWords ∧ o.path.length = po.height ∧ o.leafIndex < 2 ^ 32 ∧
      D ob = o.leafIndex.toUInt64 ∧ (∀ t < po.leafWords, D (ob + 1 + t) = (o.leaf.getD t 0).lane) ∧
      ∀ d < po.height, ∀ l < 4,
        D (ob + 1 + wireMaxLeafWords + 4 * d + l) = (o.path.getD d default).toList.getD l 0

/-- `readPhase`'s bounds, as the model checks them. -/
abbrev PhaseOk (h lw rw : Nat) (ps : List Nat) : Prop :=
  h ≤ wireMaxHeight ∧ lw ≤ wireMaxLeafWords ∧ rw ≤ lw ∧ ps ≠ [] ∧ ps.getLastD 0 < 2 ^ h

/-- The model's phase, when every read and check passes. -/
theorem phaseM_some {B : List UInt8} {c c2 c6 c7 n h lw rw : Nat} {qs : List Nat}
    {rws : List (List K)} {sibs : List (List (Nat × Digest))}
    (h1 : rdU32 B c = some (n, c + 4)) (hn : n ≤ wireMaxQueries)
    (h2 : rdU32s B n (c + 4) = some (qs, c2)) (h3 : rdU32 B c2 = some (h, c2 + 4))
    (h4 : rdU32 B (c2 + 4) = some (lw, c2 + 4 + 4))
    (h5 : rdU32 B (c2 + 4 + 4) = some (rw, c2 + 4 + 4 + 4))
    (hok : PhaseOk h lw rw (sortD qs))
    (h6 : rdRows B rw (sortD qs).length (c2 + 4 + 4 + 4) = some (rws, c6))
    (hz : ¬(0 < rw ∧ ∀ r ∈ rws, r.getD 0 0 = 0))
    (h7 : climbM B h ((sortD qs).zip ((rws.map fun r ↦ paddedLeaf r lw).map
      fun l ↦ keccak256 (l.flatMap K.toBytes))) c6 = some (sibs, c7)) :
    phaseM B c = some (⟨h, lw,
      qs.map (openingOf (sortD qs) (rws.map fun r ↦ paddedLeaf r lw) sibs h)⟩, c7) := by
  unfold PhaseOk at hok
  simp only [phaseM, h1, Option.bind_eq_bind, Option.bind_some, show ¬ wireMaxQueries < n by omega,
    ite_false, h2, h3, h4, h5]
  rw [ite_no (not_not.2 hok)]
  simp only [h6, Option.bind_some, ite_no hz, h7]
  rfl

theorem phaseM_none0 {B : List UInt8} {c : Nat} (h1 : rdU32 B c = none) : phaseM B c = none := by
  simp [phaseM, h1]

theorem phaseM_none1 {B : List UInt8} {c n : Nat} (h1 : rdU32 B c = some (n, c + 4))
    (hn : wireMaxQueries < n) : phaseM B c = none := by
  simp [phaseM, h1, hn]

theorem phaseM_none2 {B : List UInt8} {c n : Nat} (h1 : rdU32 B c = some (n, c + 4))
    (hn : ¬ wireMaxQueries < n) (h2 : rdU32s B n (c + 4) = none) : phaseM B c = none := by
  simp [phaseM, h1, hn, h2]

theorem phaseM_none3 {B : List UInt8} {c n c2 : Nat} {qs : List Nat}
    (h1 : rdU32 B c = some (n, c + 4)) (hn : ¬ wireMaxQueries < n)
    (h2 : rdU32s B n (c + 4) = some (qs, c2)) (h3 : rdU32 B c2 = none) : phaseM B c = none := by
  simp [phaseM, h1, hn, h2, h3]

theorem phaseM_none4 {B : List UInt8} {c n c2 h : Nat} {qs : List Nat}
    (h1 : rdU32 B c = some (n, c + 4)) (hn : ¬ wireMaxQueries < n)
    (h2 : rdU32s B n (c + 4) = some (qs, c2)) (h3 : rdU32 B c2 = some (h, c2 + 4))
    (h4 : rdU32 B (c2 + 4) = none) : phaseM B c = none := by
  simp [phaseM, h1, hn, h2, h3, h4]

theorem phaseM_none5 {B : List UInt8} {c n c2 h lw : Nat} {qs : List Nat}
    (h1 : rdU32 B c = some (n, c + 4)) (hn : ¬ wireMaxQueries < n)
    (h2 : rdU32s B n (c + 4) = some (qs, c2)) (h3 : rdU32 B c2 = some (h, c2 + 4))
    (h4 : rdU32 B (c2 + 4) = some (lw, c2 + 4 + 4)) (h5 : rdU32 B (c2 + 4 + 4) = none) :
    phaseM B c = none := by
  simp [phaseM, h1, hn, h2, h3, h4, h5]

/-- What a phase's head reads: the query count, at most `wireMaxQueries`, the queries, the
height, the leaf width and the row width, from `c` on. -/
def HeadOk (B : List UInt8) (c n : Nat) (qs : List Nat) (h lw rw : Nat) : Prop :=
  rdU32 B c = some (n, c + 4) ∧ n ≤ wireMaxQueries ∧ rdU32s B n (c + 4) = some (qs, c + 4 + 4 * n) ∧
    rdU32 B (c + 4 + 4 * n) = some (h, c + 4 + 4 * n + 4) ∧
    rdU32 B (c + 4 + 4 * n + 4) = some (lw, c + 4 + 4 * n + 4 + 4) ∧
    rdU32 B (c + 4 + 4 * n + 4 + 4) = some (rw, c + 4 + 4 * n + 4 + 4 + 4) ∧
    h < 2 ^ 32 ∧ lw < 2 ^ 32 ∧ rw < 2 ^ 32 ∧ qs.length = n ∧ ∀ q ∈ qs, q < 2 ^ 32

/-- The model's phase after its head, by the checks. -/
theorem phaseM_head {B : List UInt8} {c n h lw rw : Nat} {qs : List Nat}
    (hd : HeadOk B c n qs h lw rw) :
    phaseM B c = if ¬ PhaseOk h lw rw (sortD qs) then none else
      (rdRows B rw (sortD qs).length (c + 4 + 4 * n + 4 + 4 + 4)).bind fun r ↦
        if 0 < rw ∧ ∀ x ∈ r.1, x.getD 0 0 = 0 then none else
          (climbM B h ((sortD qs).zip ((r.1.map fun x ↦ paddedLeaf x lw).map
            fun leaf ↦ keccak256 (leaf.flatMap K.toBytes))) r.2).bind fun t ↦
            some (⟨h, lw, qs.map (openingOf (sortD qs) (r.1.map fun x ↦ paddedLeaf x lw) t.1 h)⟩,
              t.2) := by
  obtain ⟨h1, hn, h2, h3, h4, h5, -⟩ := hd
  unfold PhaseOk
  simp only [phaseM, h1, Option.bind_eq_bind, Option.bind_some, show ¬ wireMaxQueries < n by omega,
    ite_false, h2, h3, h4, h5]
  by_cases hok : h ≤ wireMaxHeight ∧ lw ≤ wireMaxLeafWords ∧ rw ≤ lw ∧ sortD qs ≠ [] ∧
      (sortD qs).getLastD 0 < 2 ^ h
  · rw [ite_no (not_not.2 hok), ite_no (not_not.2 hok)]
    congr 1
  · rw [ite_yes hok, ite_yes hok]
    rfl

theorem sibsM_le {B : List UInt8} (nodes : List (Nat × Digest)) :
    ∀ (l : List (Nat × Digest)) {c c' : Nat} {r : List (Nat × Digest × Bool)}, c ≤ B.length →
      sibsM B nodes l c = some (r, c') → c' ≤ B.length
  | [], c, c', r, hc, h => by simp only [sibsM, Option.some.injEq, Prod.mk.injEq] at h; omega
  | (v, _) :: l, c, c', r, hc, h => by
    unfold sibsM at h
    split at h
    · simp only [Option.bind_eq_bind] at h
      cases h1 : sibsM B nodes l c with
      | none => simp [h1] at h
      | some q =>
        simp only [h1, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        exact h.2 ▸ sibsM_le nodes l hc h1
    · simp only [Option.bind_eq_bind] at h
      cases h1 : rdDigest B c with
      | none => simp [h1] at h
      | some q =>
        obtain ⟨d, c1⟩ := q
        simp only [h1, Option.bind_some] at h
        cases h2 : sibsM B nodes l c1 with
        | none => simp [h2] at h
        | some q =>
          simp only [h2, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          exact h.2 ▸ sibsM_le nodes l (rdDigest_le h1) h2

theorem climbM_le {B : List UInt8} : ∀ (h : Nat) {nodes : List (Nat × Digest)} {c c' : Nat}
    {r : List (List (Nat × Digest))}, c ≤ B.length → climbM B h nodes c = some (r, c') →
      c' ≤ B.length
  | 0, nodes, c, c', r, hc, h => by simp only [climbM, Option.some.injEq, Prod.mk.injEq] at h; omega
  | h + 1, nodes, c, c', r, hc, hm => by
    simp only [climbM, Option.bind_eq_bind] at hm
    cases h1 : sibsM B nodes nodes c with
    | none => simp [h1] at hm
    | some q =>
      obtain ⟨sb, c1⟩ := q
      simp only [h1, Option.bind_some] at hm
      cases h2 : climbM B h (parentsOf nodes sb) c1 with
      | none => simp [h2] at hm
      | some q =>
        simp only [h2, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hm
        exact hm.2 ▸ climbM_le h (sibsM_le nodes nodes hc h1) h2

section Run

variable {e : Env} (P : Pre e)
include P

variable {s : QState} {D W : Nat → UInt64} {F : QState → Prop}

omit P in
theorem cond_geu_imm {s : QState} {r : Reg64} {n K : Nat} {k : Int64} (hr : s.reg r = n.toUInt64)
    (hk : k.toUInt64 = K.toUInt64) (hn : n < 2 ^ 32) (hK : K < 2 ^ 31) :
    (Cond.cmp .geu r (.imm k)).eval s = decide (K ≤ n) := by
  simp only [Cond.eval, Rhs.eval, hr, hk, decide_eq_decide]
  rw [UInt64.le_iff_toNat_le, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]

/-- **`readPhase`'s bounds.** -/
theorem checks_ok (hI : Inv e s D W) {h lw rw : Nat} {ps : List Nat}
    (hr13 : s.reg .r13 = h.toUInt64) (hr12 : s.reg .r12 = lw.toUInt64)
    (hr11 : s.reg .r11 = rw.toUInt64) (hr10 : s.reg .r10 = ps.length.toUInt64)
    (hh : h < 2 ^ 32) (hlw : lw < 2 ^ 32) (hrw : rw < 2 ^ 32) (hpn : ps.length ≤ wireMaxQueries)
    (hplt : ∀ p ∈ ps, p < 2 ^ 32) (hps : Tab W wP (ps.map Nat.toUInt64)) :
    WP checks s
      (fun s' ↦ PhaseOk h lw rw ps ∧ Inv e s' D W ∧ RegsFrame [.rax, .rbx, .rcx, .rdx] s s')
      (fun s' ↦ ¬ PhaseOk h lw rw ps ∧ Kept e s') := by
  have hq : wireMaxQueries = 256 := rfl
  have hmh : wireMaxHeight = 32 := rfl
  have hml : wireMaxLeafWords = 64 := rfl
  unfold checks PhaseOk
  apply WP.blk_cons
  refine wp_failIf (fun hc1 ↦ ⟨fun h' ↦ ?_, hI.kept⟩) fun hc1 ↦ ?_
  · rw [cond_geu_imm hr13 (k := 33) (K := 33) rfl hh (by norm_num), decide_eq_true_iff] at hc1
    omega
  rw [cond_geu_imm hr13 (k := 33) (K := 33) rfl hh (by norm_num), decide_eq_false_iff_not] at hc1
  apply WP.blk_cons
  refine wp_failIf (fun hc2 ↦ ⟨fun h' ↦ ?_, hI.kept⟩) fun hc2 ↦ ?_
  · rw [cond_geu_imm hr12 (k := 65) (K := 65) rfl hlw (by norm_num), decide_eq_true_iff] at hc2
    omega
  rw [cond_geu_imm hr12 (k := 65) (K := 65) rfl hlw (by norm_num), decide_eq_false_iff_not] at hc2
  apply WP.blk_cons
  have h3 : (Cond.cmp .ltu .r12 (.reg .r11)).eval s = decide (lw < rw) :=
    Native.SphincsVerifier.cond_ltu_reg hr12 hr11 (by omega) (by omega)
  refine wp_failIf (fun hc3 ↦ ⟨fun h' ↦ ?_, hI.kept⟩) fun hc3 ↦ ?_
  · rw [h3, decide_eq_true_iff] at hc3; omega
  rw [h3, decide_eq_false_iff_not] at hc3
  apply WP.blk_cons
  have h4 : (Cond.cmp .eq .r10 (.imm 0)).eval s = decide (ps.length = 0) :=
    Native.SphincsVerifier.cond_eq_imm hr10 rfl (by omega) (by norm_num)
  refine wp_failIf (fun hc4 ↦ ⟨fun h' ↦ ?_, hI.kept⟩) fun hc4 ↦ ?_
  · rw [h4, decide_eq_true_iff, List.length_eq_zero_iff] at hc4; exact h'.2.2.2.1 hc4
  rw [h4, decide_eq_false_iff_not] at hc4
  refine blk_load_ctx P hI (eval_cw s hI.rdi cWork) (by decide) P.c10 ?_
  step; step
  have hlast : ps.getLastD 0 = ps[ps.length - 1]'(by omega) := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
    simp [List.getElem?_eq_getElem (show ps.length - 1 < ps.length by omega)]
  have hrdx : s.reg .r10 - (1 : Int64).toUInt64 = (ps.length - 1).toUInt64 := by
    rw [hr10, show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl,
      Native.SphincsVerifier.toUInt64_sub (show 1 ≤ ps.length by omega)]
  refine blk_load_work ((hI.setReg (d := .rax) (by decide) _).setReg (d := .rdx) (by decide) _)
    (k := wP + (ps.length - 1)) (by
      rw [eval_ix _ .rax .rdx (a := e.wk) (j := 0) (n := ps.length - 1) (by simp [adr_zero])
        (by simp [hrdx]) wP]
      congr 1; omega)
    (by unfold workWords wLeaf wSib wSibN wPar wNode wFL wP wQ; omega) ?_
  have hw : W (wP + (ps.length - 1)) = (ps.getLastD 0).toUInt64 := by
    rw [hps (ps.length - 1) (by simp; omega), hlast]
    simp
  step; step; step
  have h2h : 2 ^ h ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow : (1 : Int64).toUInt64 <<< (h.toUInt64 &&& 63) = (2 ^ h).toUInt64 := by
    rw [show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl,
      show (63 : UInt64) = (2 ^ 6 - 1 : Nat).toUInt64 from rfl,
      Native.SphincsVerifier.toUInt64_and_mask (by norm_num) (by omega),
      Nat.mod_eq_of_lt (by omega),
      toUInt64_shl (by omega) (by rw [Nat.one_mul]; omega), Nat.one_mul]
  have hlt : ps.getLastD 0 < 2 ^ 32 := by
    rw [hlast]; exact hplt _ (List.getElem_mem _)
  apply WP.blk_cons
  have hcmp : (2 ^ h).toUInt64 ≤ (ps.getLastD 0).toUInt64 ↔ 2 ^ h ≤ ps.getLastD 0 := by
    rw [UInt64.le_iff_toNat_le, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
  refine wp_failIf (fun hc ↦ ⟨fun h' ↦ ?_, ?_⟩) fun hc ↦ ?_
  · simp only [Cond.eval, Rhs.eval, QState.setReg_reg, reduceCtorEq, ite_true, ite_false, hw, hr13,
      hpow, decide_eq_true_eq, hcmp] at hc
    omega
  · exact ((((((hI.setReg (d := .rax) (by decide) _).setReg (d := .rdx) (by decide) _).setReg
      (d := .rbx) (by decide) _).setReg (d := .rax) (by decide) _).setReg (d := .rcx) (by decide)
      _).setReg (d := .rax) (by decide) _).kept
  simp only [Cond.eval, Rhs.eval, QState.setReg_reg, reduceCtorEq, ite_true, ite_false, hw, hr13,
    hpow, decide_eq_false_iff_not, hcmp] at hc
  apply WP.blk_nil
  refine ⟨⟨by omega, by omega, by omega, fun h' ↦ by simp [h'] at hc4, by omega⟩, ?_, ?_⟩
  · exact ((((((hI.setReg (d := .rax) (by decide) _).setReg (d := .rdx) (by decide) _).setReg
      (d := .rbx) (by decide) _).setReg (d := .rax) (by decide) _).setReg (d := .rcx) (by decide)
      _).setReg (d := .rax) (by decide) _)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]

/-- **The phase's three counts.** -/
theorem header_ok (hI : Inv e s D W) {base : Nat} (hpb : W wPB = adr e.da base)
    (hb : base + 3 ≤ e.dn) :
    WP header s (fun s' ↦ Inv e s' (Function.update (Function.update (Function.update D base
      (s.reg .r14)) (base + 1) (s.reg .r13)) (base + 2) (s.reg .r12)) W ∧
      RegsFrame [.rax, .rcx] s s') F := by
  unfold header
  refine blk_load_ctx P hI (eval_cw s hI.rdi cWork) (by decide) P.c10 ?_
  refine blk_load_work (hI.setReg (d := .rcx) (by decide) _) (k := wPB)
    (by rw [eval_rw _ .rcx (a := e.wk) (j := 0) (by simp [adr_zero]) wPB, Nat.zero_add])
    (by unfold workWords wLeaf wSib wSibN wPar wNode wFL wP wQ wPB; omega) ?_
  rw [hpb]
  refine blk_store_dec P ((hI.setReg (d := .rcx) (by decide) _).setReg (d := .rax) (by decide) _)
    (k := base) (by rw [eval_rw _ .rax (a := e.da) (j := base) (by simp) 0, Nat.add_zero])
    (by omega) fun s1 h1 r1 ↦ ?_
  refine blk_store_dec P h1 (k := base + 1) (by rw [eval_rw _ .rax (a := e.da) (j := base)
    (by rw [r1]; simp) 1]) (by omega) fun s2 h2 r2 ↦ ?_
  refine blk_store_dec P h2 (k := base + 2) (by rw [eval_rw _ .rax (a := e.da) (j := base)
    (by rw [r2, r1]; simp) 2]) (by omega) fun s3 h3 r3 ↦ ?_
  apply WP.blk_nil
  refine ⟨by simpa [r1, r2] using h3, fun r hr ↦ ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [r3, r2, r1, hr.1, hr.2]

/-- **A phase's head.** -/
theorem phaseHead_ok (hI : Inv e s D W) {c : Nat} (hp : s.reg .r15 = c.toUInt64) (hc : c ≤ e.L) :
    WP phaseHead s (fun t ↦ ∃ n qs h lw rw W2, HeadOk e.B c n qs h lw rw ∧ Inv e t D W2 ∧
      Tab W2 wQ (qs.map Nat.toUInt64) ∧ Same (fun k ↦ 2 ≤ k) W W2 ∧ t.reg .r14 = n.toUInt64 ∧
      t.reg .r13 = h.toUInt64 ∧ t.reg .r12 = lw.toUInt64 ∧ t.reg .r11 = rw.toUInt64 ∧
      t.reg .r15 = (c + 4 + 4 * n + 4 + 4 + 4).toUInt64)
      (fun t ↦ phaseM e.B c = none ∧ Kept e t) := by
  have hL := P.L32
  have hBl := B_length P
  have hq : wireMaxQueries = 256 := rfl
  unfold phaseHead
  -- the query count
  apply WP.blk_cons
  refine WP.mono (getU32_ok P hI hp hc) (fun s1 ⟨n, hn1, hn32, h1, hb1, hr1, hf1⟩ ↦ ?_)
    (fun s1 ⟨hno, hk⟩ ↦ ⟨phaseM_none0 hno, hk⟩)
  apply WP.blk_cons
  refine wp_failIf (fun hc1 ↦ ⟨?_, h1.kept⟩) fun hc1 ↦ ?_
  · rw [cond_geu_imm hb1 (k := 257) (K := 257) rfl hn32 (by norm_num), decide_eq_true_iff] at hc1
    exact phaseM_none1 hn1 (by omega)
  rw [cond_geu_imm hb1 (k := 257) (K := 257) rfl hn32 (by norm_num), decide_eq_false_iff_not] at hc1
  step
  have hc4 : c + 4 ≤ e.L := by have := rdU32_le hn1; omega
  have hnq : ¬ wireMaxQueries < n := by omega
  -- the queries
  apply WP.blk_cons
  refine WP.mono (readQueries_ok P (h1.setReg (d := .r14) (by decide) _) (n := n) (c := c + 4)
    (by simp [hb1]) (by omega) (by simpa using hr1) hc4)
    (fun s2 ⟨qs, hqs, W2, h2, htab2, hsame2, hr2, hf2⟩ ↦ ?_)
    (fun s2 ⟨hno, hk⟩ ↦ ⟨phaseM_none2 hn1 hnq hno, hk⟩)
  obtain ⟨hc2e, hqsl, hqlt⟩ := rdU32s_pos e.B n hqs
  have hc2 : c + 4 + 4 * n ≤ e.L := by
    have := rdU32s_le n (B := e.B) (by omega) hqs; omega
  -- the height, the leaf width, the row width
  apply WP.blk_cons
  refine WP.mono (getU32_ok P h2 hr2 hc2) (fun s3 ⟨h, hh1, hh32, h3, hb3, hr3, hf3⟩ ↦ ?_)
    (fun s3 ⟨hno, hk⟩ ↦ ⟨phaseM_none3 hn1 hnq hqs hno, hk⟩)
  step
  have hc3 : c + 4 + 4 * n + 4 ≤ e.L := by have := rdU32_le hh1; omega
  apply WP.blk_cons
  refine WP.mono (getU32_ok P (h3.setReg (d := .r13) (by decide) _) (by simpa using hr3) hc3)
    (fun s4 ⟨lw, hw1, hw32, h4, hb4, hr4, hf4⟩ ↦ ?_)
    (fun s4 ⟨hno, hk⟩ ↦ ⟨phaseM_none4 hn1 hnq hqs hh1 hno, hk⟩)
  step
  have hc4' : c + 4 + 4 * n + 4 + 4 ≤ e.L := by have := rdU32_le hw1; omega
  apply WP.blk_cons
  refine WP.mono (getU32_ok P (h4.setReg (d := .r12) (by decide) _) (by simpa using hr4) hc4')
    (fun s5 ⟨rw, hr1', hr32, h5, hb5, hr5, hf5⟩ ↦ ?_)
    (fun s5 ⟨hno, hk⟩ ↦ ⟨phaseM_none5 hn1 hnq hqs hh1 hw1 hno, hk⟩)
  step
  have hc5 : c + 4 + 4 * n + 4 + 4 + 4 ≤ e.L := by have := rdU32_le hr1'; omega
  apply WP.blk_nil
  refine ⟨n, qs, h, lw, rw, W2, ⟨hn1, by omega, by rw [hqs, hc2e], hh1, hw1, hr1', hh32, hw32, hr32,
    hqsl, hqlt⟩, h5.setReg (by decide) _, htab2, hsame2.mono fun k hk ↦ by unfold wQ at hk; omega,
    ?_, ?_, ?_, by simp [hb5], by simp [hr5]⟩
  · simp [hf5 .r14 (by simp), hf4 .r14 (by simp), hf3 .r14 (by simp), hf2 .r14 (by simp), hb1]
  · simp [hf5 .r13 (by simp), hf4 .r13 (by simp), hb3]
  · simp [hf5 .r12 (by simp), hb4]

/-- **A phase's leaves**: the distinct positions, the checks, the rows and the leaves' digests. -/
theorem phaseLeaves_ok (hI : Inv e s D W) {c n h lw rw : Nat} {qs : List Nat}
    (hd : HeadOk e.B c n qs h lw rw) (hq : Tab W wQ (qs.map Nat.toUInt64))
    (r14 : s.reg .r14 = n.toUInt64) (r13 : s.reg .r13 = h.toUInt64)
    (r12 : s.reg .r12 = lw.toUInt64) (r11 : s.reg .r11 = rw.toUInt64)
    (r15 : s.reg .r15 = (c + 4 + 4 * n + 4 + 4 + 4).toUInt64) :
    WP phaseLeaves s (fun t ↦ ∃ rws c6 W', PhaseOk h lw rw (sortD qs) ∧
      rdRows e.B rw (sortD qs).length (c + 4 + 4 * n + 4 + 4 + 4) = some (rws, c6) ∧
      ¬(0 < rw ∧ ∀ r ∈ rws, r.getD 0 0 = 0) ∧ c6 ≤ e.L ∧ Inv e t D W' ∧
      Tab W' wQ (qs.map Nat.toUInt64) ∧ Tab W' wP ((sortD qs).map Nat.toUInt64) ∧
      LeafTab W' (rws.map fun r ↦ paddedLeaf r lw) lw ∧
      NodeTab W' wNode ((sortD qs).zip ((rws.map fun r ↦ paddedLeaf r lw).map
        fun l ↦ keccak256 (l.flatMap K.toBytes))) ∧
      W' wN = (sortD qs).length.toUInt64 ∧ Same (fun k ↦ 2 ≤ k) W W' ∧
      t.reg .r14 = n.toUInt64 ∧ t.reg .r13 = h.toUInt64 ∧ t.reg .r12 = lw.toUInt64 ∧
      t.reg .r10 = (sortD qs).length.toUInt64 ∧ t.reg .r15 = c6.toUInt64)
      (fun t ↦ phaseM e.B c = none ∧ Kept e t) := by
  obtain ⟨_, hn, _, _, _, hr1, hh32, hw32, hr32, hqsl, hqlt⟩ := hd
  have hBl := B_length P
  have hc5 : c + 4 + 4 * n + 4 + 4 + 4 ≤ e.L := by have := rdU32_le hr1; omega
  have hq' : wireMaxQueries = 256 := rfl
  have hml : wireMaxLeafWords = 64 := rfl
  unfold phaseLeaves
  apply WP.blk_cons
  refine WP.mono (sortQ_ok P hI r14 hn hqsl hqlt hq)
    (fun s6 ⟨W6, h6, htab6, hlen6, hsame6, hr10_6, hf6⟩ ↦ ?_) (fun _ h ↦ h)
  have hpsl : (sortD qs).length ≤ wireMaxQueries := by omega
  have hplt : ∀ p ∈ sortD qs, p < 2 ^ 32 := fun p hp ↦ by
    rw [sortD_eq, mem_distinctPositions] at hp; exact hqlt p hp
  have htabQ6 : Tab W6 wQ (qs.map Nat.toUInt64) := hq.same hsame6 fun i hi ↦ by
    simp only [List.length_map] at hi; unfold wP wQ; omega
  apply WP.blk_cons
  refine WP.mono (checks_ok P h6 (h := h) (lw := lw) (rw := rw) (ps := sortD qs)
    (by rw [hf6 .r13 (by simp), r13]) (by rw [hf6 .r12 (by simp), r12])
    (by rw [hf6 .r11 (by simp), r11]) hr10_6 hh32 hw32 hr32 hpsl hplt htab6)
    (fun s7 ⟨hok, h7, hf7⟩ ↦ ?_)
    (fun s7 ⟨hno, hk⟩ ↦ ⟨by rw [phaseM_head ⟨‹_›, hn, ‹_›, ‹_›, ‹_›, hr1, hh32, hw32, hr32, hqsl,
      hqlt⟩, ite_yes hno], hk⟩)
  have hrw : rw ≤ lw := hok.2.2.1
  apply WP.blk_cons
  refine WP.mono (rows_ok P h7 (c := c + 4 + 4 * n + 4 + 4 + 4) (lw := lw) (rw := rw)
    (n := (sortD qs).length) (by rw [hf7 .r15 (by simp), hf6 .r15 (by simp), r15]) hc5
    (by rw [hf7 .r12 (by simp), hf6 .r12 (by simp), r12])
    (by rw [hf7 .r11 (by simp), hf6 .r11 (by simp), r11])
    (by rw [hf7 .r10 (by simp), hr10_6]) hrw hok.2.1 hpsl)
    (fun s8 ⟨rws, c6, hrows, hnz, W8, h8, hleaf8, hsame8, hr15_8, hf8⟩ ↦ ?_)
    (fun s8 ⟨hno, hk⟩ ↦ ⟨?_, hk⟩)
  swap
  · rw [phaseM_head ⟨‹_›, hn, ‹_›, ‹_›, ‹_›, hr1, hh32, hw32, hr32, hqsl, hqlt⟩,
      ite_no (not_not.2 hok)]
    rcases hno with hno | ⟨rws, c6, h6, hz⟩
    · rw [hno]; rfl
    · rw [h6]; simp only [Option.bind_some]; rw [ite_yes hz]
  obtain ⟨hrl, hrwl⟩ := rdRows_length _ _ hrows
  have hc6 : c6 ≤ e.L := by
    have := rdRows_le (B := e.B) _ _ (by rw [hBl]; exact hc5) hrows; omega
  have hsame8' : Same (fun k ↦ wLeaf ≤ k ∧ k < wLeaf + wireMaxLeafWords * wireMaxQueries) W6 W8 :=
    hsame8
  have htabP8 : Tab W8 wP ((sortD qs).map Nat.toUInt64) := htab6.same hsame8' fun i hi ↦ by
    simp only [List.length_map] at hi; unfold wLeaf wSib wSibN wPar wNode wFL wP wQ; omega
  have htabQ8 : Tab W8 wQ (qs.map Nat.toUInt64) := htabQ6.same hsame8' fun i hi ↦ by
    simp only [List.length_map] at hi; unfold wLeaf wSib wSibN wPar wNode wFL wP wQ; omega
  have hll : ∀ l ∈ rws.map (fun r ↦ paddedLeaf r lw), l.length = lw := fun l hl ↦ by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hl
    simp [paddedLeaf, hrwl r hr]; omega
  refine WP.blk_cons (WP.mono (leafHashes_ok P h8 (lw := lw) (ps := sortD qs)
    (leaves := rws.map fun r ↦ paddedLeaf r lw)
    (by rw [hf8 .r12 (by simp), hf7 .r12 (by simp), hf6 .r12 (by simp), r12])
    (by rw [hf8 .r10 (by simp), hf7 .r10 (by simp), hr10_6]) hok.2.1 hpsl htabP8
    (by simp [hrl]) hll hleaf8)
    (fun s9 ⟨W9, h9, hnode9, hN9, hsame9, hf9⟩ ↦ WP.blk_nil ⟨rws, c6, W9, hok, hrows, hnz, hc6, h9,
      ?_, ?_, ?_, hnode9, hN9, ?_, ?_, ?_, ?_, ?_, ?_⟩) (fun _ h ↦ h))
  · exact htabQ8.same hsame9 fun i hi ↦ by
      simp only [List.length_map] at hi; unfold wNode wFL wP wQ wN; omega
  · exact htabP8.same hsame9 fun i hi ↦ by
      simp only [List.length_map] at hi; unfold wNode wFL wP wQ wN; omega
  · exact hleaf8.same hsame9 fun i hi t ht ↦ by
      simp only [List.length_map] at hi
      have : t < 64 := by
        have := hok.2.1; unfold LeanVM.Protocol.Compile.wireMaxLeafWords at this; omega
      unfold wLeaf wSib wSibN wPar wNode wN; omega
  · intro k hk
    rw [hsame9 k (by unfold wNode wFL wP wQ wN; omega),
      hsame8 k (by unfold wLeaf wSib wSibN wPar wNode wFL wP wQ; omega),
      hsame6 k (by unfold wP wQ; omega)]
  · rw [hf9 .r14 (by simp), hf8 .r14 (by simp), hf7 .r14 (by simp), hf6 .r14 (by simp), r14]
  · rw [hf9 .r13 (by simp), hf8 .r13 (by simp), hf7 .r13 (by simp), hf6 .r13 (by simp), r13]
  · rw [hf9 .r12 (by simp), hf8 .r12 (by simp), hf7 .r12 (by simp), hf6 .r12 (by simp), r12]
  · rw [hf9 .r10 (by simp), hf8 .r10 (by simp), hf7 .r10 (by simp), hr10_6]
  · rw [hf9 .r15 (by simp), hr15_8]

/-- **A phase.** -/
theorem phase_ok (hI : Inv e s D W) {c base : Nat} (hp : s.reg .r15 = c.toUInt64) (hc : c ≤ e.L)
    (hpb : W wPB = adr e.da base) (hbase : base + phaseWords ≤ e.dn) :
    WP phase s (fun s' ↦ ∃ po c', phaseM e.B c = some (po, c') ∧ c' ≤ e.L ∧ ∃ D' W',
      Inv e s' D' W' ∧ PhaseAt D' base po ∧ Same (fun k ↦ base ≤ k ∧ k < base + phaseWords) D D' ∧
      W' wPB = W wPB ∧ W' wPN = W wPN ∧ s'.reg .r15 = c'.toUInt64)
      (fun s' ↦ phaseM e.B c = none ∧ Kept e s') := by
  have hq' : wireMaxQueries = 256 := rfl
  have hml : wireMaxLeafWords = 64 := rfl
  have hmh : wireMaxHeight = 32 := rfl
  have hBl := B_length P
  unfold phase
  apply WP.blk_cons
  refine WP.mono (phaseHead_ok P hI hp hc)
    (fun s2 ⟨n, qs, h, lw, rw, W2, hd, h2, hq2, hsame2, r14, r13, r12, r11, r15⟩ ↦ ?_) (fun _ h ↦ h)
  apply WP.blk_cons
  refine WP.mono (phaseLeaves_ok P h2 hd hq2 r14 r13 r12 r11 r15)
    (fun s3 ⟨rws, c6, W3, hok, hrows, hnz, hc6, h3, hq3, hp3, hleaf3, hnode3, hN3, hsame3, r14',
      r13', r12', r10', r15'⟩ ↦ ?_) (fun _ h ↦ h)
  obtain ⟨_, hn, _, _, _, _, hh32, hw32, hr32, hqsl, hqlt⟩ := hd
  set ps := sortD qs with hps
  set leaves := rws.map fun r ↦ paddedLeaf r lw with hleaves
  have hpos : ps.Pairwise (· < ·) := by rw [hps, sortD_eq]; exact pairwise_lt_distinctPositions qs
  have hqp : ∀ q ∈ qs, q ∈ ps := fun q hq ↦ by rw [hps, sortD_eq, mem_distinctPositions]; exact hq
  have hpsl : ps.length ≤ wireMaxQueries := by
    have := (List.Nodup.subperm (hpos.imp ne_of_lt) fun p hp ↦ by
      rw [hps, sortD_eq, mem_distinctPositions] at hp; exact hp).length_le
    omega
  have hplt : ∀ p ∈ ps, p < 2 ^ 32 := fun p hp ↦ by
    rw [hps, sortD_eq, mem_distinctPositions] at hp; exact hqlt p hp
  obtain ⟨hrl, hrwl⟩ := rdRows_length _ _ hrows
  have hll : ∀ l ∈ leaves, l.length = lw := fun l hl ↦ by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hl
    simp [paddedLeaf, hrwl r hr]; omega
  have hkeys : keys (ps.zip (leaves.map fun l ↦ keccak256 (l.flatMap K.toBytes))) =
      levelNodes ps 0 := by
    rw [levelNodes_zero hpos, keys, List.map_fst_zip]
    simp [hleaves, hrl]
  apply WP.blk_cons
  refine WP.mono (climb_ok P h3 (c := c6) (h := h) (ps := ps) r15' hc6 r13' hok.1 hpos hpsl hplt
    hkeys (by rw [hN3]; simp [hleaves, hrl]) hnode3)
    (fun s4 ⟨sibs, c7, hcl, W4, h4, hsib4, hsame4, r15'', hf4⟩ ↦ ?_)
    (fun s4 ⟨hno, hk⟩ ↦ ⟨?_, hk⟩)
  swap
  · rw [phaseM_head ⟨‹_›, hn, ‹_›, ‹_›, ‹_›, ‹_›, hh32, hw32, hr32, hqsl, hqlt⟩,
      ite_no (not_not.2 hok), hrows]
    simp only [Option.bind_some]
    rw [ite_no hnz, hno]
    rfl
  have hw4 : W4 wPB = W wPB := by
    rw [hsame4 _ (by unfold wPB wN wX wH wQ wFL wP; omega), hsame3 _ (by unfold wPB; omega),
      hsame2 _ (by unfold wPB; omega)]
  have hc7 : c7 ≤ e.L := by
    have := climbM_le (B := e.B) h (by rw [hBl]; exact hc6) hcl; omega
  have hq4 : Tab W4 wQ (qs.map Nat.toUInt64) := hq3.same hsame4 fun i hi ↦ by
    simp only [List.length_map] at hi; unfold wN wX wH wQ wFL wP wLeaf wSib wSibN wPar wNode; omega
  have hp4 : Tab W4 wP (ps.map Nat.toUInt64) := hp3.same hsame4 fun i hi ↦ by
    simp only [List.length_map] at hi; unfold wN wX wH wQ wFL wP wLeaf wSib wSibN wPar wNode; omega
  have hleaf4 : LeafTab W4 leaves lw := hleaf3.same hsame4 fun i hi t ht ↦ by
    unfold wN wX wH wQ wFL wP wLeaf wSib wSibN wPar wNode; omega
  apply WP.blk_cons
  refine WP.mono (output_ok P h4 (base := base) (lw := lw) (h := h) (qs := qs) (ps := ps)
    (leaves := leaves) (sibs := sibs) (by rw [hf4 .r14 (by simp), r14', hqsl])
    (by rw [hf4 .r13 (by simp), r13']) (by rw [hf4 .r12 (by simp), r12'])
    (by rw [hf4 .r10 (by simp), r10']) (by omega) hpsl hok.1 hok.2.1 hqlt hplt hqp hq4 hp4
    (by simp [hleaves, hrl]) hleaf4 hsib4 (by rw [hw4, hpb]) hbase)
    (fun s5 ⟨D5, W5, h5, hout, hsameD, hsameW, hf5⟩ ↦ ?_) (fun _ h ↦ h)
  have hw5 : W5 wPB = adr e.da base := by rw [hsameW _ (by unfold wPB wX; omega), hw4, hpb]
  refine WP.blk_cons (WP.mono (header_ok P h5 hw5 (by unfold phaseWords at hbase; omega))
    (fun s6 ⟨h6, hf6⟩ ↦ WP.blk_nil ?_) (fun _ h ↦ h))
  have r14_5 : s5.reg .r14 = n.toUInt64 := by rw [hf5 .r14 (by simp), hf4 .r14 (by simp), r14']
  have r13_5 : s5.reg .r13 = h.toUInt64 := by rw [hf5 .r13 (by simp), hf4 .r13 (by simp), r13']
  have r12_5 : s5.reg .r12 = lw.toUInt64 := by rw [hf5 .r12 (by simp), hf4 .r12 (by simp), r12']
  rw [r14_5, r13_5, r12_5] at h6
  have hpm : phaseM e.B c = some (⟨h, lw, qs.map (openingOf ps leaves sibs h)⟩, c7) := by
    rw [phaseM_head ⟨‹_›, hn, ‹_›, ‹_›, ‹_›, ‹_›, hh32, hw32, hr32, hqsl, hqlt⟩,
      ite_no (not_not.2 hok), hrows]
    simp only [Option.bind_some]
    rw [ite_no hnz, hcl]
    rfl
  have hpw : 3 ≤ phaseWords := by unfold phaseWords; omega
  refine ⟨_, c7, hpm, hc7, _, W5, h6, ⟨hok.1, hok.2.1, by simp; omega, ?_, ?_, ?_, fun j hj ↦ ?_⟩,
    fun k hk ↦ ?_, ?_, ?_, ?_⟩
  · simp [hqsl]
  · simp
  · simp
  · simp only [List.length_map] at hj
    simp only [List.getElem_map]
    obtain ⟨h1, h2, h3⟩ := hout j hj
    have hq : qs[j] ∈ ps := hqp _ (List.getElem_mem _)
    obtain ⟨x, hx, hx1, hlk⟩ := lookup_of_mem_map_fst (l := ps.zip leaves) (a := qs[j])
      (by rw [List.map_fst_zip (by simp [hleaves, hrl])]; exact hq)
    have hxl : x.2 ∈ leaves := (List.of_mem_zip hx).2
    have hne : ∀ k, 3 ≤ k → base + k ≠ base ∧ base + k ≠ base + 1 ∧ base + k ≠ base + 2 :=
      fun k hk ↦ ⟨by omega, by omega, by omega⟩
    have hupd : ∀ k, 3 ≤ k → Function.update (Function.update (Function.update D5 base n.toUInt64)
        (base + 1) h.toUInt64) (base + 2) lw.toUInt64 (base + k) = D5 (base + k) := fun k hk ↦ by
      simp only [Function.update_apply]
      rw [ite_no (hne k hk).2.2, ite_no (hne k hk).2.1, ite_no (hne k hk).1]
    refine ⟨by simp [openingOf, hlk, hll _ hxl], by simp [openingOf], hqlt _ (List.getElem_mem _),
      ?_, fun t ht ↦ ?_, fun d hd l hl ↦ ?_⟩
    · rw [show base + 3 + j * openingWords = base + (3 + j * openingWords) by omega,
        hupd _ (by omega),
        ← show base + 3 + j * openingWords = base + (3 + j * openingWords) by omega, h1]
    · rw [show base + 3 + j * openingWords + 1 + t = base + (3 + j * openingWords + 1 + t) by omega,
        hupd _ (by omega), ← show base + 3 + j * openingWords + 1 + t =
          base + (3 + j * openingWords + 1 + t) by omega, h2 t ht]
    · have := h3 d hd l hl
      rw [show base + 3 + j * openingWords + 1 + wireMaxLeafWords + 4 * d + l =
        base + (3 + j * openingWords + 1 + wireMaxLeafWords + 4 * d + l) by omega,
        hupd _ (by omega), ← show base + 3 + j * openingWords + 1 + wireMaxLeafWords + 4 * d + l =
          base + (3 + j * openingWords + 1 + wireMaxLeafWords + 4 * d + l) by omega, this]
      rfl
  · simp only [Function.update_apply]
    rw [ite_no (by omega), ite_no (by omega), ite_no (by omega), hsameD k (by omega)]
  · rw [hsameW _ (by unfold wPB wX; omega), hw4]
  · rw [hsameW _ (by unfold wPN wX; omega),
      hsame4 _ (by unfold wPN wN wX wH wQ wFL wLeaf wSib wSibN wPar wNode wP; omega),
      hsame3 _ (by unfold wPN; omega), hsame2 _ (by unfold wPN; omega)]
  · rw [hf6 .r15 (by simp), hf5 .r15 (by simp), r15'']

end Run

end NativeVm.Wire
