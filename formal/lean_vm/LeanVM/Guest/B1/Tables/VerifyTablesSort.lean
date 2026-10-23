/-
  LeanVM.Guest.B1.Tables.VerifyTablesSort

  `verify_tables`'s certified block order: each side's hinted order is `stackOffsets`'s, so the
  offsets it stores are the bus layout's.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesBase
public import LeanVM.Guest.B1.Tables.Placement

/-!
# The bus blocks' offsets (G:1495-1525)

For the push side (blocks `0 .. 36`) and the count side (blocks `74 .. 101`), `verify_tables`
reads a hinted order `sort_order`, range-checks each entry into the side's blocks, checks that
the log-heights do not increase and that ties ascend, and stores the running offset
`g^(Σ 2^κ)` at `block_off_g[block]`, write-once. As for `certify_placement`: write-once makes the
order injective, so a bijection; the adjacent checks make it `stackOffsets`'s order
(`sorted_offsets`), so the stored offsets are `stackOffsets`'s (V:877-884).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## An order certified adjacent by adjacent -/

/-- **A certified order is `stackOffsets`'s**: an injective map `π` of the ranks into the `n`
blocks whose sizes `κ` do not increase along it, ties ascending, puts block `π r` at the sum of
the sizes before rank `r`, and every block is some `π r`. -/
theorem sorted_offsets {n : ℕ} (κ π : ℕ → ℕ) (hπ : ∀ r < n, π r < n)
    (hinj : ∀ r < n, ∀ r' < n, π r = π r' → r = r')
    (hadj : ∀ r, r + 1 < n → κ (π (r + 1)) ≤ κ (π r) ∧ (κ (π (r + 1)) = κ (π r) → π r ≤ π (r + 1))) :
    (∀ b < n, ∃ r < n, π r = b) ∧
      ∀ r < n, (stackOffsets ((List.range n).map κ)).1.getD (π r) 0 =
        prefixSize id ((List.range n).map fun i => κ (π i)) r := by
  have hsurj : ∀ b < n, ∃ r < n, π r = b := by
    let f : Fin n → Fin n := fun r => ⟨π r, hπ r r.2⟩
    have hfi : Function.Injective f := fun a b hab =>
      Fin.ext (hinj a a.2 b b.2 (congrArg Fin.val hab))
    have hfb := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfi, rfl⟩
    intro b hb
    obtain ⟨r, hr⟩ := hfb.2 ⟨b, hb⟩
    exact ⟨r, r.2, congrArg Fin.val hr⟩
  refine ⟨hsurj, fun r hr => ?_⟩
  set sizes := (List.range n).map κ
  have hsz : ∀ b < n, sizes.getD b 0 = κ b := fun b hb => by
    simp [sizes, List.getElem?_range hb]
  have hlen : sizes.length = n := by simp [sizes]
  set ord := (List.range n).map π
  have hordget : ∀ r < n, ord.getD r 0 = π r := fun r hr => by
    simp [ord, List.getElem?_range hr]
  have hperm : ord.Perm (List.range n) := by
    rw [List.perm_ext_iff_of_nodup _ List.nodup_range]
    · intro a
      simp only [ord, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨r, hr, rfl⟩; exact hπ r hr
      · intro ha; obtain ⟨r, hr, he⟩ := hsurj a ha; exact ⟨r, hr, he⟩
    · exact (List.nodup_map_iff_inj_on List.nodup_range).mpr fun a ha b hb he =>
        hinj a (List.mem_range.mp ha) b (List.mem_range.mp hb) he
  have hord : ord = (List.range sizes.length).mergeSort (stackLe (sizes.getD · 0)) := by
    rw [hlen]
    refine eq_mergeSort_of_adjacent (sizes.getD · 0) hperm fun i hi => ?_
    have hi' : i + 1 < n := by simpa [ord] using hi
    simp only [ord, List.getElem_map, List.getElem_range]
    rw [hsz (π i) (hπ i (by omega)), hsz (π (i + 1)) (hπ _ hi')]
    obtain ⟨h1, h2⟩ := hadj i hi'
    exact ⟨h1, fun h => h2 h.symm⟩
  have hoff := stackOffsets_fst sizes r (by omega)
  rw [← hord, hordget r hr] at hoff
  rw [hoff, prefixSize_map]
  congr 1
  rw [List.map_map]
  exact List.map_congr_left fun i hi => by
    simp only [Function.comp_apply]; exact hsz _ (hπ i (List.mem_range.mp hi))

/-! ## The ranks -/

/-- `g^101`, the range check `log(global_g) < N_BLOCKS`. -/
abbrev w101 : E := word 3710851743744 0 0

theorem word_g101 : word 3710851743744 0 0 = ofK (Parameters.gpow 101) := by
  rw [word_eOfNat]
  show ofK (K.ofBits 3710851743744) = ofK (Parameters.gpow 101)
  rw [show K.ofBits 3710851743744 = Parameters.gpow 101 by decide +kernel]

/-- `BLOCK_SIDE[b]`: push `0 .. 36`, pull `37 .. 73`, count `74 .. 101`. -/
def vtBlockSide (b : ℕ) : ℕ := if b < 37 then 0 else if b < 74 then 1 else 2

/-- The stores of `block_side_tab` (G:1497-1498). -/
theorem vt_side_blocks : ∀ b < 102, stmtsEqb [.atom (.const (.n (26 + b)) (word (vtBlockSide b) 0 0)),
    .atom (.load (.n (26 + b)) (.n 25) b)] ((vtPre.drop (8 + 2 * b)).take 2) = true := by
  decide +kernel

/-- A side's rank `0`, from value `v`: the block at `sort_order[so]`, its side, its size, the
offset `1` stored, the next offset `g_squares[κ]`. -/
def vtRank0 (v so side : ℕ) : List Stmt :=
  [.atom (.load (.n v) (.n 24) so), .atom (.const (.n (v + 1)) w101),
    .atom (.rangeCheck (.n v) (.n (v + 2)) (.n (v + 3)) (.n (v + 4)) (.n (v + 1))),
    .atom (.mul (.n (v + 5)) (.n 25) (.n v)), .atom (.load (.n (v + 6)) (.n (v + 5)) 0),
    .atom (.const (.n (v + 7)) (word side 0 0)), .atom (.assertEq (.n (v + 6)) (.n (v + 7))),
    .atom (.mul (.n (v + 8)) (.n 9) (.n v)), .atom (.load (.n (v + 9)) (.n (v + 8)) 0),
    .atom (.const (.n (v + 10)) (word 1 0 0)), .atom (.mul (.n (v + 11)) (.n 128) (.n v)),
    .atom (.load (.n (v + 10)) (.n (v + 11)) 0), .atom (.mul (.n (v + 12)) (.n 10) (.n (v + 9))),
    .atom (.load (.n (v + 13)) (.n (v + 12)) 0)]

/-- A side's rank `≥ 1`, from value `v`, with the previous rank's size `pk`, block `pg` and
offset `pgo`. -/
def vtRankN (v pk pg pgo so side : ℕ) : List Stmt :=
  [.atom (.load (.n v) (.n 24) so), .atom (.const (.n (v + 1)) w101),
    .atom (.rangeCheck (.n v) (.n (v + 2)) (.n (v + 3)) (.n (v + 4)) (.n (v + 1))),
    .atom (.mul (.n (v + 5)) (.n 25) (.n v)), .atom (.load (.n (v + 6)) (.n (v + 5)) 0),
    .atom (.const (.n (v + 7)) (word side 0 0)), .atom (.assertEq (.n (v + 6)) (.n (v + 7))),
    .atom (.mul (.n (v + 8)) (.n 9) (.n v)), .atom (.load (.n (v + 9)) (.n (v + 8)) 0),
    .atom (.const (.n (v + 10)) w33), .atom (.mul (.n pk) (.n (v + 11)) (.n (v + 9))),
    .atom (.rangeCheck (.n (v + 11)) (.n (v + 12)) (.n (v + 13)) (.n (v + 14)) (.n (v + 10))),
    .atom (.add (.n (v + 15)) (.n pk) (.n (v + 9))),
    .ite (.n (v + 15))
      [.atom (.const (.n (v + 16)) w101), .atom (.mul (.n v) (.n (v + 17)) (.n pg)),
        .atom (.rangeCheck (.n (v + 17)) (.n (v + 18)) (.n (v + 19)) (.n (v + 20)) (.n (v + 16)))]
      [],
    .atom (.mul (.n (v + 21)) (.n 128) (.n v)), .atom (.load (.n pgo) (.n (v + 21)) 0),
    .atom (.mul (.n (v + 22)) (.n 10) (.n (v + 9))), .atom (.load (.n (v + 23)) (.n (v + 22)) 0),
    .atom (.mul (.n (v + 24)) (.n pgo) (.n (v + 23)))]

/-- Rank `r`'s values from a side's base `v0`: the block, its size, the offset stored, the next
offset. -/
def rkV (v0 q : ℕ) : ℕ := v0 + 14 + 25 * q
def rkGl (v0 r : ℕ) : ℕ := if r = 0 then v0 else rkV v0 (r - 1)
def rkKa (v0 r : ℕ) : ℕ := rkGl v0 r + 9
def rkGo (v0 r : ℕ) : ℕ := v0 + 13 + 25 * r
def rkGi (v0 r : ℕ) : ℕ := if r = 0 then v0 + 10 else rkGo v0 (r - 1)

theorem vt_push_rank0 : stmtsEqb (vtRank0 129 0 0) ((vtPre.drop 213).take 14) = true := by
  decide +kernel

theorem vt_push_ranks : ∀ q < 36, stmtsEqb (vtRankN (rkV 129 q) (rkKa 129 q) (rkGl 129 q)
    (rkGo 129 q) (q + 1) 0) ((vtPre.drop (227 + 19 * q)).take 19) = true := by
  decide +kernel

theorem vt_count_rank0 : stmtsEqb (vtRank0 1043 74 2) ((vtPre.drop 911).take 14) = true := by
  decide +kernel

theorem vt_count_ranks : ∀ q < 27, stmtsEqb (vtRankN (rkV 1043 q) (rkKa 1043 q) (rkGl 1043 q)
    (rkGo 1043 q) (75 + q) 2) ((vtPre.drop (925 + 19 * q)).take 19) = true := by
  decide +kernel

/-! ## What a rank gives -/

/-- What rank `r` of a side (base value `v0`, order entries from `so0`, side word `side`) gives:
its block `g^p`, `p < 102`, read from the order; the block's side is `side`; its size; the
offset stored at the block; the next offset `offset · g_squares[κ]`; and against the previous
rank, a size no larger and, on a tie, a larger block. -/
def VtRankFacts (rd : Reader) (σ : Val) (v0 so0 side r : ℕ) : Prop :=
  (∃ p < 102, σ (.n (rkGl v0 r)) = gen ^ p) ∧ LoadHolds rd (σ (.n 24)) (so0 + r) (σ (.n (rkGl v0 r))) ∧
    LoadHolds rd (σ (.n 25) * σ (.n (rkGl v0 r))) 0 (word side 0 0) ∧
    LoadHolds rd (σ (.n 9) * σ (.n (rkGl v0 r))) 0 (σ (.n (rkKa v0 r))) ∧
    LoadHolds rd (σ (.n 128) * σ (.n (rkGl v0 r))) 0 (σ (.n (rkGi v0 r))) ∧
    (∃ t, LoadHolds rd (σ (.n 10) * σ (.n (rkKa v0 r))) 0 t ∧
      σ (.n (rkGo v0 r)) = σ (.n (rkGi v0 r)) * t) ∧
    (1 ≤ r → (∃ d < 34, σ (.n (rkKa v0 (r - 1))) = gen ^ d * σ (.n (rkKa v0 r))) ∧
      (σ (.n (rkKa v0 (r - 1))) + σ (.n (rkKa v0 r)) = 0 →
        ∃ e < 102, σ (.n (rkGl v0 r)) = gen ^ e * σ (.n (rkGl v0 (r - 1)))))

section
variable {κ : ℕ} (hκ : κ ≤ 32) (Lm : MemImage κ)
include hκ

theorem vt_rc102 {σ : Val} {x y t1 t2 k : ℕ} (hk : σ (.n k) = w101)
    (h : RcHolds Lm.read σ x y t1 t2 k) : ∃ e < 102, σ (.n x) = gen ^ e :=
  rc_sound' hκ Lm (K := 102) (by omega) (by decide) (by rw [hk]; exact word_g101) h.1 h.2.1 h.2.2

theorem vt_rc34 {σ : Val} {x y t1 t2 k : ℕ} (hk : σ (.n k) = w33)
    (h : RcHolds Lm.read σ x y t1 t2 k) : ∃ e < 34, σ (.n x) = gen ^ e :=
  rc_sound' hκ Lm (K := 34) (by omega) (by decide) (by rw [hk]; exact word_g33) h.1 h.2.1 h.2.2

theorem vtRank0_facts {σ : Val} {kret : List E → Prop} {v0 so0 side : ℕ}
    (h : Stmt.HoldsList (coreProgram.Rel Lm.read) Lm.read σ (vtRank0 v0 so0 side) True kret) :
    VtRankFacts Lm.read σ v0 so0 side 0 ∧ σ (.n (rkGi v0 0)) = 1 := by
  simp only [vtRank0, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one] at h
  obtain ⟨l0, c1, ⟨r0, r1, r2⟩, m5, l6, c7, ae, m8, l9, c10, m11, l10, m12, l13⟩ := h
  have e6 : σ (.n (v0 + 6)) = word side 0 0 := by rw [← c7]; exact e_add_eq_zero_iff.mp ae
  simp only [VtRankFacts, rkGl, rkKa, rkGi, rkGo, ↓reduceIte, Nat.add_zero, Nat.mul_zero]
  refine ⟨⟨vt_rc102 hκ Lm c1 ⟨r0, r1, r2⟩, l0, by rw [← m5, ← e6]; exact l6,
    by rw [← m8]; exact l9, by rw [← m11]; exact l10, ⟨_, by rw [← m12]; exact l13, ?_⟩,
    fun h => absurd h (by omega)⟩, c10⟩
  rw [c10, one_mul]

theorem vtRankN_facts {σ : Val} {kret : List E → Prop} {v0 so0 side q : ℕ}
    (h : Stmt.HoldsList (coreProgram.Rel Lm.read) Lm.read σ (vtRankN (rkV v0 q) (rkKa v0 q)
      (rkGl v0 q) (rkGo v0 q) (so0 + (q + 1)) side) True kret) :
    VtRankFacts Lm.read σ v0 so0 side (q + 1) := by
  simp only [vtRankN] at h
  rw [Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList,
    Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList,
    Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, holds_ite_noRet _ _ _ rfl rfl] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, implies_true] at h
  obtain ⟨l0, c1, ⟨r0, r1, r2⟩, m5, l6, c7, ae, m8, l9, c10, m11, ⟨rk0, rk1, rk2⟩, a15, ⟨-, hite⟩,
    m21, l21, m22, l23, m24⟩ := h
  have e6 : σ (.n (rkV v0 q + 6)) = word side 0 0 := by rw [← c7]; exact e_add_eq_zero_iff.mp ae
  have hgl : rkGl v0 (q + 1) = rkV v0 q := by simp [rkGl]
  have hgi : rkGi v0 (q + 1) = rkGo v0 q := by simp [rkGi]
  have hgo : rkGo v0 (q + 1) = rkV v0 q + 24 := by simp only [rkGo, rkV]; ring
  have hka : rkKa v0 (q + 1) = rkV v0 q + 9 := by simp only [rkKa, hgl]
  simp only [VtRankFacts, hka, hgl, hgi, hgo, Nat.add_sub_cancel]
  refine ⟨vt_rc102 hκ Lm c1 ⟨r0, r1, r2⟩, l0, by rw [← m5, ← e6]; exact l6, by rw [← m8]; exact l9,
    by rw [← m21]; exact l21, ⟨_, by rw [← m22]; exact l23, m24⟩, fun _ => ⟨?_, fun h0 => ?_⟩⟩
  · obtain ⟨d, hd, hq⟩ := vt_rc34 hκ Lm c10 ⟨rk0, rk1, rk2⟩
    exact ⟨d, hd, by rw [m11, hq]⟩
  · obtain ⟨c16, m17, rc17⟩ := hite (by rw [a15]; exact h0)
    obtain ⟨e, he, hq⟩ := vt_rc102 hκ Lm c16 rc17
    exact ⟨e, he, by rw [m17, hq]⟩

end

/-! ## A side's offsets -/

theorem vt_prefixSize_le (n : ℕ) (k : ℕ → ℕ) (hk : ∀ r < n, k r < 34) :
    ∀ r ≤ n, prefixSize id ((List.range n).map k) r ≤ r * 2 ^ 33
  | 0, _ => by simp [prefixSize]
  | r + 1, hr => by
    rw [prefixSize_succ _ _ _ (by simp; omega)]
    have := vt_prefixSize_le n k hk r (by omega)
    simp only [id, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show r < n by omega), Option.map_some, Option.getD_some]
    have : 2 ^ k r ≤ 2 ^ 33 := Nat.pow_le_pow_right (by decide) (by have := hk r (by omega); omega)
    nlinarith

theorem vt_prefixSize_strict (n : ℕ) (k : ℕ → ℕ) :
    ∀ r r', r < r' → r' ≤ n →
      prefixSize id ((List.range n).map k) r < prefixSize id ((List.range n).map k) r'
  | r, r' + 1, h, h' => by
    rw [prefixSize_succ _ _ _ (by simp; omega)]
    rcases Nat.lt_or_ge r r' with hlt | hge
    · have := vt_prefixSize_strict n k r r' hlt (by omega)
      have : 0 < 2 ^ (((List.range n).map k).getD r' 0) := Nat.two_pow_pos _
      simp only [id]; omega
    · obtain rfl : r = r' := by omega
      have : 0 < 2 ^ (((List.range n).map k).getD r 0) := Nat.two_pow_pos _
      simp only [id]; omega

/-- **A side's offsets are the bus layout's**: from its ranks' facts, over `block_side_tab`,
`block_kappa = g^ks` and `g_squares`, block `start + i` of the side holds at `block_off_g` the
`stackOffsets` offset of entry `i` of the side's sizes. -/
theorem vt_side_offsets {rd : Reader} {σ : Val} {v0 side start n : ℕ}
    (hn : start + n ≤ 102) (hf : ∀ r < n, VtRankFacts rd σ v0 start side r)
    (hgi0 : σ (.n (rkGi v0 0)) = 1)
    (hside : ∀ b < 102, LoadHolds rd (σ (.n 25)) b (word (vtBlockSide b) 0 0))
    (hsw : ∀ b < 102, word (vtBlockSide b) 0 0 = word side 0 0 → start ≤ b ∧ b < start + n)
    (ks : ℕ → ℕ) (hks : ∀ b < 102, ks b < 34)
    (hbk : ∀ b < 102, LoadHolds rd (σ (.n 9)) b (gen ^ ks b))
    (hsq : ∀ j < 34, LoadHolds rd (σ (.n 10)) j (gen ^ 2 ^ j)) :
    ∀ i < n, LoadHolds rd (σ (.n 128)) (start + i)
      (gen ^ (stackOffsets ((List.range n).map fun i => ks (start + i))).1.getD i 0) := by
  classical
  obtain ⟨p, hp⟩ := exists_fun_of_forall (n := n) (fun r hr => (hf r hr).1)
  have hpr : ∀ r < n, start ≤ p r ∧ p r < start + n := fun r hr => by
    obtain ⟨-, -, hs, -⟩ := hf r hr
    rw [(hp r hr).2, loadHolds_mul_gen_pow, Nat.add_zero] at hs
    exact hsw _ (hp r hr).1 (loadHolds_unique (hside _ (hp r hr).1) hs)
  have hka : ∀ r < n, σ (.n (rkKa v0 r)) = gen ^ ks (p r) := fun r hr => by
    obtain ⟨-, -, -, hk, -⟩ := hf r hr
    rw [(hp r hr).2, loadHolds_mul_gen_pow, Nat.add_zero] at hk
    exact loadHolds_unique hk (hbk _ (hp r hr).1)
  set k := fun r => ks (p r)
  have hk34 : ∀ r < n, ks (p r) < 34 := fun r hr => hks _ (hp r hr).1
  set S := fun r => prefixSize id ((List.range n).map k) r
  have hS : ∀ r ≤ n, S r < 2 ^ 62 := fun r hr => by
    show prefixSize id ((List.range n).map k) r < 2 ^ 62
    have := vt_prefixSize_le n k hk34 r hr
    have : r * 2 ^ 33 ≤ 102 * 2 ^ 33 := Nat.mul_le_mul_right _ (by omega)
    omega
  have hG : ∀ r < n, σ (.n (rkGi v0 r)) = gen ^ S r := fun r hr => by
    induction r with
    | zero => rw [hgi0]; simp [S, prefixSize]
    | succ r ih =>
      obtain ⟨-, -, -, -, -, ⟨t, lt, et⟩, -⟩ := hf r (by omega)
      rw [hka r (by omega), loadHolds_mul_gen_pow, Nat.add_zero] at lt
      rw [show rkGi v0 (r + 1) = rkGo v0 r by simp [rkGi], et, ih (by omega),
        loadHolds_unique lt (hsq _ (hk34 r (by omega))), ← pow_add]
      simp only [S]
      rw [prefixSize_succ _ _ _ (by simp; omega)]
      simp [List.getElem?_range (show r < n by omega), k]
  have hoff : ∀ r < n, LoadHolds rd (σ (.n 128)) (p r) (gen ^ S r) := fun r hr => by
    obtain ⟨-, -, -, -, ho, -⟩ := hf r hr
    rw [(hp r hr).2, loadHolds_mul_gen_pow, Nat.add_zero, hG r hr] at ho
    exact ho
  have hinj : ∀ r < n, ∀ r' < n, p r = p r' → r = r' := fun r hr r' hr' he => by
    have e := loadHolds_unique (hoff r hr) (he ▸ hoff r' hr')
    have := gen_pow_inj' (by have := hS r (by omega); omega) (by have := hS r' (by omega); omega) e
    rcases Nat.lt_trichotomy r r' with h | h | h
    · exact absurd this (Nat.ne_of_lt (vt_prefixSize_strict n k r r' h (by omega)))
    · exact h
    · exact absurd this (Nat.ne_of_gt (vt_prefixSize_strict n k r' r h (by omega)))
  have hadj : ∀ r, r + 1 < n → k (r + 1) ≤ k r ∧ (k (r + 1) = k r → p r ≤ p (r + 1)) := by
    intro r hr
    obtain ⟨-, -, -, -, -, -, hadj⟩ := hf (r + 1) hr
    obtain ⟨⟨d, hd, hdk⟩, htie⟩ := hadj (by omega)
    rw [Nat.add_sub_cancel, hka r (by omega), hka (r + 1) hr] at hdk htie
    have e1 := gen_pow_eq_mul (by have := hk34 r (by omega); omega)
      (by have := hk34 (r + 1) hr; omega) (by omega) hdk
    refine ⟨by simp only [k]; omega, fun heq => ?_⟩
    have h0 : gen ^ ks (p r) + gen ^ ks (p (r + 1)) = 0 := by
      rw [show ks (p (r + 1)) = ks (p r) from heq]; exact e_add_self _
    obtain ⟨e, he, hcol⟩ := htie h0
    rw [(hp (r + 1) hr).2, (hp r (by omega)).2] at hcol
    have := gen_pow_eq_mul (by have := (hp (r + 1) hr).1; omega)
      (by have := (hp r (by omega)).1; omega) (by omega) hcol
    omega
  obtain ⟨hsurj, hst⟩ := sorted_offsets (n := n) (fun i => ks (start + i)) (fun r => p r - start)
    (fun r hr => by have := hpr r hr; omega)
    (fun r hr r' hr' he => hinj r hr r' hr' (by have := hpr r hr; have := hpr r' hr'; omega))
    (fun r hr => by
      have h1 := hpr r (by omega); have h2 := hpr (r + 1) hr
      rw [show start + (p (r + 1) - start) = p (r + 1) by omega,
        show start + (p r - start) = p r by omega]
      obtain ⟨a, b⟩ := hadj r hr
      exact ⟨a, fun h => by have := b h; omega⟩)
  have hmap : ((List.range n).map fun i => ks (start + (p i - start))) = (List.range n).map k :=
    List.map_congr_left fun j hj => by
      simp only [k]; rw [show start + (p j - start) = p j by have := hpr j (List.mem_range.mp hj); omega]
  intro i hi
  obtain ⟨r, hr, rfl⟩ := hsurj i hi
  rw [hst r hr, show start + (p r - start) = p r by have := hpr r hr; omega, hmap]
  exact hoff r hr

/-! ## Both sides -/

theorem word_small_inj {a b : ℕ} (ha : a < 3) (hb : b < 3) (h : word a 0 0 = word b 0 0) : a = b := by
  rw [word_eOfNat, word_eOfNat] at h
  exact eOfNat_inj (by omega) (by omega) h

/-- **The bus blocks' offsets** (G:1495-1525): with `block_kappa = g^ks` (`ks < 34`) and the
exponent tables, the push blocks `0 .. 36` and the count blocks `74 .. 101` hold at
`block_off_g` their `stackOffsets` offsets within their side. -/
theorem vt_offsets {κ : ℕ} (hκ : κ ≤ 32) (Lm : MemImage κ) {σ : Val} (h : VtHolds Lm.read σ)
    (ks : ℕ → ℕ) (hks : ∀ b < 102, ks b < 34)
    (hbk : ∀ b < 102, LoadHolds Lm.read (σ (.n 9)) b (gen ^ ks b))
    (hsq : ∀ j < 34, LoadHolds Lm.read (σ (.n 10)) j (gen ^ 2 ^ j)) :
    (∀ i < 37, LoadHolds Lm.read (σ (.n 128)) i
      (gen ^ (stackOffsets ((List.range 37).map ks)).1.getD i 0)) ∧
    ∀ i < 28, LoadHolds Lm.read (σ (.n 128)) (74 + i)
      (gen ^ (stackOffsets ((List.range 28).map fun i => ks (74 + i))).1.getD i 0) := by
  have hside : ∀ b < 102, LoadHolds Lm.read (σ (.n 25)) b (word (vtBlockSide b) 0 0) := by
    intro b hb
    obtain ⟨k, hs⟩ := h.slice _ _ (vt_side_blocks b hb)
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
    rw [← hs.1]; exact hs.2
  have hvs : ∀ b, vtBlockSide b < 3 := fun b => by unfold vtBlockSide; split_ifs <;> omega
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have := vt_side_offsets (v0 := 129) (side := 0) (start := 0) (n := 37) (by omega)
      (fun r hr => ?_) ?_ hside (fun b hb hw => ?_) ks hks hbk hsq i hi
    · simpa using this
    · rcases Nat.eq_zero_or_pos r with rfl | hr0
      · obtain ⟨k, hr⟩ := h.slice _ _ vt_push_rank0
        exact (vtRank0_facts hκ Lm hr).1
      · obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
        obtain ⟨k, hr⟩ := h.slice _ _ (vt_push_ranks q (by omega))
        exact vtRankN_facts hκ Lm (so0 := 0) (by simpa using hr)
    · obtain ⟨k, hr⟩ := h.slice _ _ vt_push_rank0
      exact (vtRank0_facts hκ Lm hr).2
    · have := word_small_inj (hvs b) (by omega) hw
      unfold vtBlockSide at this; split_ifs at this; omega
  · have := vt_side_offsets (v0 := 1043) (side := 2) (start := 74) (n := 28) (by omega)
      (fun r hr => ?_) ?_ hside (fun b hb hw => ?_) ks hks hbk hsq i hi
    · exact this
    · rcases Nat.eq_zero_or_pos r with rfl | hr0
      · obtain ⟨k, hr⟩ := h.slice _ _ vt_count_rank0
        exact (vtRank0_facts hκ Lm hr).1
      · obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
        obtain ⟨k, hr⟩ := h.slice _ _ (vt_count_ranks q (by omega))
        exact vtRankN_facts hκ Lm (so0 := 74) (by rw [show 74 + (q + 1) = 75 + q by omega]; exact hr)
    · obtain ⟨k, hr⟩ := h.slice _ _ vt_count_rank0
      exact (vtRank0_facts hκ Lm hr).2
    · have := word_small_inj (hvs b) (by omega) hw
      unfold vtBlockSide at this; split_ifs at this <;> omega

end
end LeanVM.Guest.B1.VerifySub
