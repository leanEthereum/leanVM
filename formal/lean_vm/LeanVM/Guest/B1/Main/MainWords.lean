/-
  LeanVM.Guest.B1.Main.MainWords

  `main`'s words on an honest run (`Bmain`) bounded by a budget linear in the work
  (`End.Linear`): its buffers and each callee's bound, every bound linear in the claims, the raw
  signatures, the checked blob matrix's rows and the children.
-/

module

public import LeanVM.Guest.B1.Main.MainHonestBudgetB
public import LeanVM.Guest.Complete
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Source

/-!
# `main`'s words, linear in the work

Component bounds: `dvB_le` (`da_verify`, linear in its blobs and padded blobs),
`clB_le`, `ccB_le` (the claim lists' digests, linear in the list's length), `l5Chain_le` (the
children's loop, linear in the children and their claims). `mainWords`: the budget;
`Bmain_le`: `Bmain` at `0` within it.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (Kid kidsBoundL)

@[expose] public section

/-- The bounds `g` of the first `n` names of `names`. -/
def nameSum (g : String → ℕ) (names : List String) (n : ℕ) : ℕ :=
  ((List.range n).map fun j => g names[j]!).sum

theorem le_nameSum {g : String → ℕ} {names : List String} {n j : ℕ} (hj : j < n) :
    g names[j]! ≤ nameSum g names n :=
  List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

variable (fs SB SK : String → ℕ)

/-! ## `da_verify` -/

/-- The selected DA level's words per padded row, at most: the largest over the dispatch's levels
(`DA_TREE_ARMS`) of `⌈SB (da_levels at j) / 2^j⌉`. -/
def dlK : ℕ := (Finset.range (guest_const% DA_TREE_ARMS)).sup fun j => (SB Da.dlNames[j]! + 2 ^ j - 1) / 2 ^ j

theorem le_cdiv_mul (a d : ℕ) (hd : 0 < d) : a ≤ (a + d - 1) / d * d := by
  have h1 := Nat.div_add_mod (a + d - 1) d
  have h2 := Nat.mod_lt (a + d - 1) hd
  have h3 : d * ((a + d - 1) / d) = (a + d - 1) / d * d := Nat.mul_comm _ _
  omega

/-- **The selected DA level within `dlK` words per padded row.** -/
theorem dl_le {L : ℕ} (hL : L < guest_const% DA_TREE_ARMS) : SB Da.dlNames[L]! ≤ dlK SB * 2 ^ L := by
  have h1 := le_cdiv_mul (SB Da.dlNames[L]!) (2 ^ L) (Nat.two_pow_pos L)
  have h2 : (SB Da.dlNames[L]! + 2 ^ L - 1) / 2 ^ L ≤ dlK SB :=
    Finset.le_sup (f := fun j => (SB Da.dlNames[j]! + 2 ^ j - 1) / 2 ^ j)
      (Finset.mem_range.mpr hL)
  exact le_trans h1 (Nat.mul_le_mul_right _ h2)

/-- **`r` rows of a loop and `P - r` of another within `r · (a - b) + P · b`**, with equality when
`b ≤ a`: the row and padding loops share the padded height. -/
theorem rows_gap_le {a b r P : ℕ} (h : r ≤ P) : r * a + (P - r) * b ≤ r * (a - b) + P * b := by
  rcases le_total b a with hab | hab
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
    exact le_of_eq (by ring)
  · have e : r * b + (P - r) * b = P * b := by rw [← Nat.add_mul, Nat.add_sub_cancel' h]
    have : r * a ≤ r * b := Nat.mul_le_mul_left _ hab
    rw [Nat.sub_eq_zero_of_le hab, Nat.mul_zero, Nat.zero_add]
    omega

/-- `da_verify`'s constant words: its frame, `da_row_shape`'s, `da_vector`'s, the column loop's
`128` iterations (each its frame, the column's, the weights' expansion's and the row loop's
phantom frame) and its untaken tail call's frame, the regions' and the trees' loops' phantom
frames, the padding loop's (or its frame when it does not run): a static loop helper's run is
charged its phantom frame once, here, and `iterK fs SK g` per iteration. -/
def dvC : ℕ :=
  fs "da_verify" + fs "da_row_shape" + SB "da_vector" + fs name% «da_verify_loop0» +
    128 * (fs name% «da_verify_loop1» + fs "da_verify_column" + SB "da_expand__L6_L7" + fs
        name% «da_verify_column_loop0») +
    fs name% «da_verify_loop1» + fs name% «da_verify_loop2» + fs name% «da_verify_loop3»

/-- `da_verify`'s words per blob: its region (`641`) and base, the regions' loop, the column's
row loop in each of the `128` columns, the trees' loop past the padding loop, each an
iteration's words (`iterK`). -/
def dvS : ℕ :=
  642 + iterK fs SK name% «da_verify_loop0» + 128 * iterK fs SK name% «da_verify_column_loop0» +
    (iterK fs SK name% «da_verify_loop2» - iterK fs SK name% «da_verify_loop3»)

/-- `da_verify`'s words per padded blob: the roots (`4`), the padding loop's iteration, the
levels. -/
def dvP : ℕ := 4 + iterK fs SK name% «da_verify_loop3» + dlK SB

theorem dvB_le {r L : ℕ} (hr : r ≤ 2 ^ L) (hL : L < guest_const% DA_TREE_ARMS) :
    Da.dvB fs SB SK r L ≤ dvC fs SB + r * dvS fs SK + 2 ^ L * dvP fs SB SK := by
  unfold Da.dvB Da.dvKB Da.clB Da.colB dvC dvS dvP Da.dvSizes
  generalize iterK fs SK name% «da_verify_loop0» = k21
  generalize iterK fs SK name% «da_verify_loop2» = k23
  generalize iterK fs SK name% «da_verify_loop3» = k24
  generalize iterK fs SK name% «da_verify_column_loop0» = k25
  have h20 : (if 2 ^ L - r ≠ 0 then (2 ^ L - r) * k24 + fs name% «da_verify_loop3» else fs
      name% «da_verify_loop3») ≤
      (2 ^ L - r) * k24 + fs name% «da_verify_loop3» := by
    split <;> omega
  have hg := rows_gap_le (a := k23) (b := k24) hr
  have hd := dl_le SB hL
  simp only [List.sum_cons, List.sum_nil]
  have e : r * (642 + k21 + 128 * k25 + (k23 - k24)) =
      642 * r + r * k21 + 128 * (r * k25) + r * (k23 - k24) := by ring
  have e' : 2 ^ L * (4 + k24 + dlK SB) = 4 * 2 ^ L + 2 ^ L * k24 + dlK SB * 2 ^ L := by ring
  have e'' : 128 * (fs name% «da_verify_loop1» + (fs "da_verify_column" + SB "da_expand__L6_L7" +
      (r * k25 + fs name% «da_verify_column_loop0»))) = 128 * (fs name% «da_verify_loop1» + fs
          "da_verify_column" +
      SB "da_expand__L6_L7" + fs name% «da_verify_column_loop0») + 128 * (r * k25) := by ring
  omega

/-! ## The claim lists

A claim list's digest takes `13` words and a loop iteration per frame of `136` claims
(`CLAIM_BIG`) and per group of `17` (`CLAIM_GROUP`): `(n / d) · K ≤ n · ⌈K / d⌉` (`div17_mul_le`,
`div136_mul_le`), so the words per claim are `1 + ⌈K₁₅ / 136⌉ + ⌈K₁₆ / 17⌉`. -/

theorem div17_mul_le (n K : ℕ) : n / 17 * K ≤ n * ((K + 16) / 17) := by
  have h1 : K ≤ 17 * ((K + 16) / 17) := by omega
  have h2 : n / 17 * 17 ≤ n := Nat.div_mul_le_self n 17
  calc n / 17 * K ≤ n / 17 * (17 * ((K + 16) / 17)) := Nat.mul_le_mul_left _ h1
    _ = n / 17 * 17 * ((K + 16) / 17) := by ring
    _ ≤ n * ((K + 16) / 17) := Nat.mul_le_mul_right _ h2

theorem div136_mul_le (n K : ℕ) : n / 136 * K ≤ n * ((K + 135) / 136) := by
  have h1 : K ≤ 136 * ((K + 135) / 136) := by omega
  have h2 : n / 136 * 136 ≤ n := Nat.div_mul_le_self n 136
  calc n / 136 * K ≤ n / 136 * (136 * ((K + 135) / 136)) := Nat.mul_le_mul_left _ h1
    _ = n / 136 * 136 * ((K + 135) / 136) := by ring
    _ ≤ n * ((K + 135) / 136) := Nat.mul_le_mul_right _ h2

/-- A claim list's digest's constant words. -/
def clC : ℕ :=
  fs "claim_list_digest" + 13 + SB "list_split" + fs name% «claim_list_digest_loop0» + fs
      name% «claim_list_digest_loop1» +
    nameSum SB B1.Digest.clNames 17

/-- A claim list's digest's words per claim: `13` and a `claim_list_digest_loop0` iteration per
`136` claims (`CLAIM_BIG`), `13` and a `claim_list_digest_loop1` iteration per `17` claims
(`CLAIM_GROUP`), the loops' runs'
phantom frames in the constant (`clC`). -/
def clS : ℕ := 1 + (iterK fs SK name% «claim_list_digest_loop0» + 135) / 136 + (iterK fs SK
    name% «claim_list_digest_loop1» + 16) / 17

theorem clB_le (n : ℕ) : B1.Digest.clB fs SB SK n ≤ clC fs SB + n * clS fs SK := by
  unfold B1.Digest.clB clC clS
  generalize iterK fs SK name% «claim_list_digest_loop0» = k15
  generalize iterK fs SK name% «claim_list_digest_loop1» = k16
  split
  · omega
  · have h1 := le_nameSum (g := SB) (names := B1.Digest.clNames) (j := n % 17) (Nat.mod_lt _ (by omega))
    have h2 := div136_mul_le n k15
    have h3 : (if n / 136 ≠ 0 then n / 136 * k15 + fs name% «claim_list_digest_loop0» else fs
        name% «claim_list_digest_loop0») ≤
        n * ((k15 + 135) / 136) + fs name% «claim_list_digest_loop0» := by
      split <;> omega
    have h5 : n % 136 / 17 * k16 ≤ n * ((k16 + 16) / 17) :=
      le_trans (Nat.mul_le_mul_right _ (show n % 136 / 17 ≤ n / 17 by omega)) (div17_mul_le n k16)
    have h6 : (if n % 136 / 17 ≠ 0 then n % 136 / 17 * k16 + fs name% «claim_list_digest_loop1»
        else fs name% «claim_list_digest_loop1») ≤
        n * ((k16 + 16) / 17) + fs name% «claim_list_digest_loop1» := by
      split <;> omega
    have h4 : 13 * (n / 136 + n % 136 / 17) ≤ n := by omega
    have e : n * (1 + (k15 + 135) / 136 + (k16 + 16) / 17) =
        n + n * ((k15 + 135) / 136) + n * ((k16 + 16) / 17) := by ring
    omega

/-- A child's claim list's digest's constant words: its frame, `list_split`, the any walk's frame
(`child_claim_list_any`, the only walk the honest run takes) and its chain's first `13` words, its
two loops' frames twice and its last group's helper. -/
def ccC : ℕ :=
  fs "child_claim_list_digest" + 13 + SB "list_split" + fs "child_claim_list_any" +
    2 * fs name% «child_claim_list_any_loop0» + 2 * fs name% «child_claim_list_any_loop1» + nameSum
        (fun g => fs g) B1.Digest.cclNames 17

/-- A child's claim list's digest's words per claim: `13` and a `child_claim_list_any_loop0` frame
per `136` claims,
`13` and a `child_claim_list_any_loop1` frame per `17` claims. -/
def ccS : ℕ := 1 + (fs name% «child_claim_list_any_loop0» + 135) / 136 + (fs
    name% «child_claim_list_any_loop1» + 16) / 17

theorem ccB_le (n : ℕ) : B1.Digest.ccB fs SB n ≤ ccC fs SB + n * ccS fs := by
  unfold B1.Digest.ccB B1.Digest.anyB ccC ccS
  split
  · omega
  · have h1 := le_nameSum (g := fun g => fs g) (names := B1.Digest.cclNames) (j := n % 17)
      (Nat.mod_lt _ (by omega))
    have hg : B1.Digest.cclNames.getD (n % 17) "" = B1.Digest.cclNames[n % 17]! := by
      simp only [List.getD_eq_getElem?_getD, getElem!_def]
      cases B1.Digest.cclNames[n % 17]? <;> rfl
    rw [hg]
    have h2 := div136_mul_le n (fs name% «child_claim_list_any_loop0»)
    have h3 : (if n / 136 ≠ 0 then (n / 136 + 1) * fs name% «child_claim_list_any_loop0» else fs
        name% «child_claim_list_any_loop0») ≤
        n * ((fs name% «child_claim_list_any_loop0» + 135) / 136) + 2 * fs
            name% «child_claim_list_any_loop0» := by
      split
      · have e : (n / 136 + 1) * fs name% «child_claim_list_any_loop0» = n / 136 * fs
          name% «child_claim_list_any_loop0» + fs name% «child_claim_list_any_loop0» := by ring
        omega
      · omega
    have h5 : n % 136 / 17 * fs name% «child_claim_list_any_loop1» ≤ n * ((fs
        name% «child_claim_list_any_loop1» + 16) / 17) :=
      le_trans (Nat.mul_le_mul_right _ (show n % 136 / 17 ≤ n / 17 by omega))
        (div17_mul_le n (fs name% «child_claim_list_any_loop1»))
    have h6 : (if n % 136 / 17 ≠ 0 then (n % 136 / 17 + 1) * fs name% «child_claim_list_any_loop1»
        else fs name% «child_claim_list_any_loop1») ≤
        n * ((fs name% «child_claim_list_any_loop1» + 16) / 17) + 2 * fs
            name% «child_claim_list_any_loop1» := by
      split
      · have e : (n % 136 / 17 + 1) * fs name% «child_claim_list_any_loop1» = n % 136 / 17 * fs
          name% «child_claim_list_any_loop1» + fs name% «child_claim_list_any_loop1» := by
          ring
        omega
      · omega
    have h4 : 13 * (n / 136 + n % 136 / 17) ≤ n := by omega
    have e : n * (1 + (fs name% «child_claim_list_any_loop0» + 135) / 136 + (fs
        name% «child_claim_list_any_loop1» + 16) / 17) =
        n + n * ((fs name% «child_claim_list_any_loop0» + 135) / 136) + n * ((fs
            name% «child_claim_list_any_loop1» + 16) / 17) := by ring
    omega

/-! ## The children's loop -/

/-- A child's constant words in the children's loop (but `verify_sub`'s): the iteration's frame,
its claim lists' digests' constants, `statement_digest`. -/
def l5A1 : ℕ := fs name% «main_loop4» + 2 * ccC fs SB + SB "statement_digest"

/-- The children's loop's words per child's claim. -/
def l5A2 : ℕ := ccS fs

/-- The children's loop's constant words. -/
def l5A0 : ℕ := fs name% «main_loop4»

theorem l5Chain_le (K : ℕ → ℕ) : ∀ t c, l5ChainB fs K t c ≤
    (t + 2) * fs name% «main_loop4» + ∑ i ∈ Finset.range (t + 1), K (c + i)
  | 0, c => by simp [l5ChainB]; omega
  | t + 1, c => by
    have ih := l5Chain_le K t (c + 1)
    rw [l5ChainB, Finset.sum_range_succ']
    have e : ∑ i ∈ Finset.range (t + 1), K (c + 1 + i) = ∑ i ∈ Finset.range (t + 1), K (c + (i + 1)) :=
      Finset.sum_congr rfl fun i _ => by rw [Nat.add_right_comm, Nat.add_assoc]
    rw [e] at ih
    have e2 : (t + 1 + 2) * fs name% «main_loop4» = fs name% «main_loop4» + (t + 2) * fs
        name% «main_loop4» := by ring
    simp only [Nat.add_zero]
    omega

theorem sum_range_getD : ∀ l : List ℕ, ∑ i ∈ Finset.range l.length, l.getD i 0 = l.sum
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero, sum_range_getD l]
    omega

theorem kid_counts (w : NodeWitness) (c : ℕ) : hEx w c + hEs w c =
    (w.children.map fun ch => ch.statement.claims.xmss.length +
      ch.statement.claims.sphincs.length).getD c 0 := by
  simp only [hEx, hEs, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w.children[c]? <;> rfl

/-- **The children's loop's words**: a constant, each child's constant and `verify_sub`'s bound
`Bv c`, and a slope per child's claim. -/
theorem l5B_le (Bv : ℕ → ℕ) {s : NodeStatement} {w : NodeWitness}
    (hnc : w.children.length ≠ 0) :
    l5B fs SB (fun c => B1.Digest.ccB fs SB (hKid s w c).ex) (fun c => B1.Digest.ccB fs SB (hKid s w c).es)
      Bv w ≤ l5A0 fs + w.children.length * l5A1 fs SB +
        ∑ c ∈ Finset.range w.children.length, Bv c + l5A2 fs * (End.work s w).childClaims := by
  unfold l5B
  have h := l5Chain_le fs (fun c => l5K SB (B1.Digest.ccB fs SB (hKid s w c).ex)
    (B1.Digest.ccB fs SB (hKid s w c).es) (Bv c)) (w.children.length - 1) 0
  rw [show w.children.length - 1 + 1 = w.children.length by omega] at h
  have hK : ∀ c, l5K SB (B1.Digest.ccB fs SB (hKid s w c).ex) (B1.Digest.ccB fs SB (hKid s w c).es)
      (Bv c) ≤ ((l5A1 fs SB - fs name% «main_loop4» + Bv c) + l5A2 fs * (hEx w c + hEs w c)) := by
    intro c
    have h1 := ccB_le fs SB (hKid s w c).ex
    have h2 := ccB_le fs SB (hKid s w c).es
    unfold l5K l5A1 l5A2
    simp only [hKid] at h1 h2 ⊢
    have e : ccS fs * (hEx w c + hEs w c) = hEx w c * ccS fs + hEs w c * ccS fs := by ring
    omega
  have hs := Finset.sum_le_sum fun c (_ : c ∈ Finset.range w.children.length) => hK c
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul, ← Finset.mul_sum] at hs
  have hcc : ∑ c ∈ Finset.range w.children.length, (hEx w c + hEs w c) =
      (End.work s w).childClaims := by
    simp only [kid_counts]
    rw [show w.children.length = (w.children.map fun ch => ch.statement.claims.xmss.length +
      ch.statement.claims.sphincs.length).length by simp, sum_range_getD]
    simp only [End.work]
  rw [hcc] at hs
  simp only [Nat.zero_add] at h
  have hA : fs name% «main_loop4» ≤ l5A1 fs SB := by unfold l5A1; omega
  unfold l5A0
  have e : w.children.length * l5A1 fs SB =
      w.children.length * (l5A1 fs SB - fs name% «main_loop4») + w.children.length * fs
          name% «main_loop4» := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hA]
  have e2 : (w.children.length + 1) * fs name% «main_loop4» = w.children.length * fs
      name% «main_loop4» + fs name% «main_loop4» := by
    ring
  rw [show w.children.length - 1 + 2 = w.children.length + 1 by omega] at h
  beta_reduce at h hs ⊢
  omega

/-! ## `da_verify` at the direct witness, `aggregate_claims` -/

theorem hDvB_le {bytecode : List K} {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    (hr : NodeRelation bytecode seed s w) :
    hDvB fs SB SK w ≤ (End.work s w).rawDa * dvC fs SB + (End.work s w).rawDaRows * dvS fs SK +
      (End.work s w).rawDaPad * dvP fs SB SK := by
  obtain ⟨-, hda, -, -⟩ := hr
  unfold hDvB
  simp only [End.work]
  cases hw : w.daMatrix with
  | none => simp
  | some p =>
    rw [DaDigestHeld, hw] at hda
    have hw' : p.2.Opens p.1.daRoot p.1.membershipChallenge := hda.2
    have hb := Da.nPad_bounds hw'.1
    have hm := hw'.2.1
    rw [Da.maxRows_eq] at hm
    unfold LeanDa.paddedRowCount at hb
    have hL : Da.wLog p.2 < guest_const% DA_TREE_ARMS := by
      unfold Da.wLog
      have : 2 ^ LeanDa.logPaddedRowCount p.2.rows.length < 2 ^ guest_const% DA_TREE_ARMS := by omega
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    simp only [Option.map_some, Option.getD_some, Nat.one_mul]
    refine (dvB_le fs SB SK (r := p.2.rows.length) (by unfold Da.wLog; omega) hL).trans
      (le_of_eq ?_)
    unfold Da.wLog LeanDa.paddedRowCount
    ring

/-- `aggregate_claims`' constant words. -/
def agA0 : ℕ := fs "aggregate_claims" + 109 + SB "grind_check__L2" + SB "batch_sumcheck__L23"

/-- `aggregate_claims`' words per child: its buffers' and its three loops' iterations, each with
its run's phantom frame, which `agA0` would otherwise charge `main` when it has no child. -/
def agA1 : ℕ := 18 + (iterK fs SK name% «aggregate_claims_loop0» + fs
    name% «aggregate_claims_loop0») + (iterK fs SK name% «aggregate_claims_loop1» + fs
    name% «aggregate_claims_loop1») +
  (iterK fs SK name% «aggregate_claims_loop2» + fs name% «aggregate_claims_loop2»)

theorem aggB_le {m : ℕ} (hm : 1 ≤ m) : aggB fs SB SK m ≤ agA0 fs SB + agA1 fs SK * m := by
  unfold aggB aggKB agA0 agA1 aggSizes
  simp only [List.sum_cons, List.sum_nil]
  generalize iterK fs SK name% «aggregate_claims_loop0» = k33
  generalize iterK fs SK name% «aggregate_claims_loop1» = k34
  generalize iterK fs SK name% «aggregate_claims_loop2» = k35
  have e : (18 + (k33 + fs name% «aggregate_claims_loop0») + (k34 + fs
      name% «aggregate_claims_loop1») + (k35 + fs name% «aggregate_claims_loop2»)) * m =
      18 * m + m * k33 + m * k34 + m * k35 +
        (fs name% «aggregate_claims_loop0» + fs name% «aggregate_claims_loop1» + fs
            name% «aggregate_claims_loop2») * m := by ring
  have h := Nat.le_mul_of_pos_right (fs name% «aggregate_claims_loop0» + fs
      name% «aggregate_claims_loop1» + fs name% «aggregate_claims_loop2») hm
  omega

/-! ## `main`'s callees' words -/

/-- Child `c`'s `verify_sub` words, `Bvf` at its announced stack log and rate (`childShape`). -/
noncomputable def childBv (Bvf : ℕ → ℕ → ℕ) (w : NodeWitness) (c : ℕ) : ℕ :=
  (w.children.map fun ch => Bvf (childShape End.bytecode ch).1 (childShape End.bytecode ch).2).getD c 0

theorem sum_childBv (Bvf : ℕ → ℕ → ℕ) (s : NodeStatement) (w : NodeWitness) :
    ∑ c ∈ Finset.range w.children.length, childBv Bvf w c =
      ((End.work s w).childShapes.map fun p => Bvf p.1 p.2).sum := by
  have h := sum_range_getD (w.children.map fun ch =>
    Bvf (childShape End.bytecode ch).1 (childShape End.bytecode ch).2)
  simp only [List.length_map] at h
  unfold childBv
  rw [h]
  simp only [End.work, List.map_map]
  rfl

/-- **`main`'s words budget**, linear in the work: `main`'s frame and buffers, `exponent_tables`',
and each callee's frame and bound, child `c`'s `verify_sub` within `Bvf` at its announced stack log
and rate. -/
def mainWords (Bvf : ℕ → ℕ → ℕ) : End.Linear where
  base := fs "main" + 283 + fs "exponent_tables" + 2284 + 2 * (clC fs SB + fs "claim_list_digest") +
    fs name% «main_loop0» + fs name% «main_loop1» +
    fs name% «main_loop2» + fs name% «main_loop3» + 2 * l5A0 fs + (agA0 fs SB + fs
        "aggregate_claims") + SB "statement_digest" +
    fs "statement_digest"
  declared := clS fs SK
  coverage := 5 + iterK fs SK name% «main_loop0» + iterK fs SK name% «main_loop1»
  rawXmss := iterK fs SK name% «main_loop2»
  rawSphincs := iterK fs SK name% «main_loop3»
  rawDa := dvC fs SB + fs "da_verify"
  rawDaRows := dvS fs SK
  rawDaPad := dvP fs SB SK
  children := 53 + l5A1 fs SB + agA1 fs SK
  childClaims := l5A2 fs
  childShape := Bvf

theorem mSizes_sum (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    (mSizes (hData seed s w)).sum = 5 * Coverage.planSlots s w + 53 * w.children.length + 283 := by
  rw [coverage_eq]
  simp only [mSizes, MainData.T, MainData.X, MainData.Y, hData, List.sum_cons,
    List.sum_nil, List.length_append]
  ring

/-- **`main`'s callees' words**: each callee's bound and frame, the children's loop's frame
alone when there is no child. -/
theorem kidsBoundL_mKids (m : MainIn) (L : Layout) (b : MainBs) :
    kidsBoundL fs (mKids m L) (mBs fs SB SK m b) ≤
      b.Bx + b.Bs + 2 * fs "claim_list_digest" + m.nxd * iterK fs SK name% «main_loop0» + fs
          name% «main_loop0» +
      m.nsd * iterK fs SK name% «main_loop1» + fs name% «main_loop1» + m.nrx * iterK fs SK
          name% «main_loop2» + fs name% «main_loop2» +
      m.nrs * iterK fs SK name% «main_loop3» + fs name% «main_loop3» +
      (if m.nd = 1 then b.Bd + fs "da_verify" else 0) +
      (if m.nc = 0 then fs name% «main_loop4» else b.B5 + fs name% «main_loop4» + b.Ba + fs
          "aggregate_claims") +
      SB "statement_digest" + fs "statement_digest" := by
  unfold mKids mBs
  by_cases hnd : m.nd = 1 <;> by_cases hnc : m.nc = 0 <;>
    simp only [hnd, hnc, ↓reduceIte, List.append_nil, List.cons_append, List.nil_append,
      kidsBoundL, List.headD_cons, List.tail_cons, ne_eq, not_true_eq_false, not_false_eq_true,
      decide_false, decide_true, Bool.false_eq_true] <;>
    split_ifs <;> omega

/-- **`main`'s words on the honest run within the budget**, child `c`'s `verify_sub` within
`childBv Bvf w c`. -/
theorem Bmain_le (Bvf : ℕ → ℕ → ℕ) {bytecode : List K} {seed : Digest} {s : NodeStatement}
    {w : NodeWitness} (hr : NodeRelation bytecode seed s w) (hl : GuestLimits s w) :
    Bmain fs SB SK (childBv Bvf w) 0 seed s w ≤ (mainWords fs SB SK Bvf).eval (End.work s w) := by
  have hmsz := mSizes_sum seed s w
  have hX := clB_le fs SB SK s.claims.xmss.length
  have hS := clB_le fs SB SK s.claims.sphincs.length
  have hD := hDvB_le fs SB SK hr
  have hcov := coverage_eq (s := s) (w := w)
  simp only [List.length_append] at hcov
  have c1 : (xPlan s w).duplicates.length * iterK fs SK name% «main_loop0» ≤ Coverage.planSlots s w
      * iterK fs SK name% «main_loop0» :=
    Nat.mul_le_mul_right _ (by omega)
  have c2 : (sPlan s w).duplicates.length * iterK fs SK name% «main_loop1» ≤ Coverage.planSlots s w
      * iterK fs SK name% «main_loop1» :=
    Nat.mul_le_mul_right _ (by omega)
  have hK := kidsBoundL_mKids fs SB SK (hm fs 0 seed s w) (hLmain fs 0 seed s w)
    (mainBsH fs SB SK (childBv Bvf w) s w)
  have hB : Bmain fs SB SK (childBv Bvf w) 0 seed s w = fs "main" + (mSizes (hData seed s w)).sum +
      (fs "exponent_tables" + 2284 + kidsBoundL fs (mKids (hm fs 0 seed s w) (hLmain fs 0 seed s w))
        (mBs fs SB SK (hm fs 0 seed s w) (mainBsH fs SB SK (childBv Bvf w) s w))) := rfl
  generalize kidsBoundL fs (mKids (hm fs 0 seed s w) (hLmain fs 0 seed s w))
    (mBs fs SB SK (hm fs 0 seed s w) (mainBsH fs SB SK (childBv Bvf w) s w)) = KB at hK hB
  rw [hB, hmsz]
  have hd : (hm fs 0 seed s w).nd ≤ 1 := (hData_bounds hl fs 0).nd
  have hcl : s.claims.xmss.length + s.claims.sphincs.length ≤ (End.work s w).declared := by
    simp only [End.work]; omega
  have hcl2 := Nat.mul_le_mul_right (clS fs SK) hcl
  have hcov' : Coverage.planSlots s w = (End.work s w).coverage := rfl
  have e1 : (hm fs 0 seed s w).nxd = (xPlan s w).duplicates.length := rfl
  have e2 : (hm fs 0 seed s w).nsd = (sPlan s w).duplicates.length := rfl
  have e3 : (hm fs 0 seed s w).nrx = (End.work s w).rawXmss := rfl
  have e4 : (hm fs 0 seed s w).nrs = (End.work s w).rawSphincs := rfl
  have e6 : w.children.length = (End.work s w).children := rfl
  have e7 : (mainBsH fs SB SK (childBv Bvf w) s w).Bx = B1.Digest.clB fs SB SK s.claims.xmss.length := rfl
  have e8 : (mainBsH fs SB SK (childBv Bvf w) s w).Bs = B1.Digest.clB fs SB SK s.claims.sphincs.length :=
    rfl
  have e9 : (mainBsH fs SB SK (childBv Bvf w) s w).Bd = hDvB fs SB SK w := rfl
  have e10 : (mainBsH fs SB SK (childBv Bvf w) s w).Ba = aggB fs SB SK w.children.length := rfl
  have e11 : (mainBsH fs SB SK (childBv Bvf w) s w).B5 = l5B fs SB
      (fun c => B1.Digest.ccB fs SB (hKid s w c).ex) (fun c => B1.Digest.ccB fs SB (hKid s w c).es)
      (childBv Bvf w) w := rfl
  rw [e1, e2, e3, e4, e7, e8, e9, e10, e11] at hK
  rw [hcov'] at c1 c2 ⊢
  rw [e6]
  simp only [End.Linear.eval, mainWords, l5A0]
  have r1 : clS fs SK * (End.work s w).declared = (End.work s w).declared * clS fs SK := Nat.mul_comm _ _
  have r2 : (s.claims.xmss.length + s.claims.sphincs.length) * clS fs SK =
      s.claims.xmss.length * clS fs SK + s.claims.sphincs.length * clS fs SK := Nat.add_mul _ _ _
  have r3 : (5 + iterK fs SK name% «main_loop0» + iterK fs SK name% «main_loop1») * (End.work s
      w).coverage =
      5 * (End.work s w).coverage + (End.work s w).coverage * iterK fs SK name% «main_loop0» +
        (End.work s w).coverage * iterK fs SK name% «main_loop1» := by ring
  have r4 : iterK fs SK name% «main_loop2» * (End.work s w).rawXmss = (End.work s w).rawXmss *
      iterK fs SK name% «main_loop2» :=
    Nat.mul_comm _ _
  have r5 : iterK fs SK name% «main_loop3» * (End.work s w).rawSphincs = (End.work s w).rawSphincs
      * iterK fs SK name% «main_loop3» :=
    Nat.mul_comm _ _
  have r6 : dvS fs SK * (End.work s w).rawDaRows = (End.work s w).rawDaRows * dvS fs SK :=
    Nat.mul_comm _ _
  have r6' : dvP fs SB SK * (End.work s w).rawDaPad = (End.work s w).rawDaPad * dvP fs SB SK :=
    Nat.mul_comm _ _
  have r8 : (dvC fs SB + fs "da_verify") * (End.work s w).rawDa =
      (End.work s w).rawDa * dvC fs SB + (End.work s w).rawDa * fs "da_verify" := by ring
  have erd : (End.work s w).rawDa = (hm fs 0 seed s w).nd := rfl
  have r7 : (53 + l5A1 fs SB + agA1 fs SK) * (End.work s w).children =
      53 * (End.work s w).children + (End.work s w).children * l5A1 fs SB +
        agA1 fs SK * (End.work s w).children := by ring
  by_cases hnc : w.children.length = 0
  · have hnc' : (hm fs 0 seed s w).nc = 0 := hnc
    rw [e6] at hnc
    simp only [hnc', ↓reduceIte] at hK
    rw [hnc]
    simp only [Nat.mul_zero, Nat.add_zero]
    split_ifs at hK with hnd
    · have r9 : (End.work s w).rawDa * fs "da_verify" = fs "da_verify" := by
        rw [erd, hnd, Nat.one_mul]
      omega
    · omega
  · have hnc' : ¬ (hm fs 0 seed s w).nc = 0 := hnc
    have hA := aggB_le fs SB SK (m := w.children.length) (Nat.pos_of_ne_zero hnc)
    have h5 := l5B_le fs SB (childBv Bvf w) (s := s) hnc
    rw [sum_childBv Bvf s w] at h5
    simp only [l5A0] at h5
    simp only [hnc', ↓reduceIte] at hK
    rw [e6] at hA h5 hK
    split_ifs at hK with hnd
    · have r9 : (End.work s w).rawDa * fs "da_verify" = fs "da_verify" := by
        rw [erd, hnd, Nat.one_mul]
      omega
    · omega
end
end LeanVM.Guest.B1.Main
