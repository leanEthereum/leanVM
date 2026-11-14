module

public import LeanVM.Prover.ExecuteHint

/-!
# The executor's logarithms are complete

`baby` holds every `g^j` with `j < 2^17` (`baby_has`), so the baby-step giant-step finds every
`g^k` it covers (`boundedDlog_complete`), and every exponent it returns is below its range
(`boundedDlog_lt`). `Dlog.Small` bounds every exponent the table holds below `2^31`; then
`Dlog.log` finds every `g^k` with `k` below its bound (`Dlog.log_complete`), the exponents being
unique below the order of `g`. `decode_complete`: an instruction whose operands are powers below
`2^28` decodes, to offsets below `2^28` (`OpSmall`).
-/

namespace LeanVM.Prover.Exec

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-! ## Exponents -/

/-- Exponents below `2^63` are unique. -/
theorem gpow_inj {a b : ℕ} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) (h : g ^ a = g ^ b) : a = b :=
  gpow_injOn (show a < 2 ^ 64 - 1 by omega) (show b < 2 ^ 64 - 1 by omega) h

/-! ## Indices -/

/-- Every exponent an index holds is below `B`. -/
def IdxLt (I : Idx) (B : ℕ) : Prop := ∀ (w : UInt64) (k : ℕ), I[w]? = some k → k < B

theorem idxLt_empty (B : ℕ) : IdxLt ∅ B := fun w k h ↦ by simp at h

theorem IdxLt.insert {I : Idx} {B : ℕ} (hI : IdxLt I B) {w : UInt64} {k : ℕ} (hk : k < B) :
    IdxLt (I.insert w k) B := by
  intro w' j h
  rw [Std.HashMap.getElem?_insert] at h
  split_ifs at h
  · cases h; exact hk
  · exact hI w' j h

theorem IdxLt.mono {I : Idx} {B B' : ℕ} (hI : IdxLt I B) (h : B ≤ B') : IdxLt I B' :=
  fun w k hk ↦ lt_of_lt_of_le (hI w k hk) h

theorem fill_lt (gs : K) (step : ℕ) (hs : 0 < step) :
    ∀ (n k : ℕ) (y : K) (I : Idx) (B : ℕ), IdxLt I B → k + step * n ≤ B →
      IdxLt (fill gs step n k y I) B
  | 0, _, _, _, _, hI, _ => hI
  | n + 1, k, y, I, B, hI, hb => by
    rw [Nat.mul_succ] at hb
    exact fill_lt gs step hs n (k + step) (y * gs) _ B (hI.insert (by omega)) (by omega)

theorem insert_has {I : Idx} {w w' : UInt64} {k : ℕ} (h : w' = w ∨ I[w]?.isSome) :
    ((I.insert w' k)[w]?).isSome := by
  rw [Std.HashMap.getElem?_insert]
  rcases h with rfl | h
  · simp
  · split_ifs <;> simp [h]

theorem fill_has (gs : K) (step : ℕ) (hgs : gs = g ^ step) :
    ∀ (n k : ℕ) (y : K) (I : Idx), y = g ^ k → ∀ w : UInt64,
      (I[w]?.isSome ∨ ∃ i < n, w = (g ^ (k + step * i)).lane) → ((fill gs step n k y I)[w]?).isSome
  | 0, _, _, _, _, _, h => by
    rcases h with h | ⟨i, hi, -⟩
    · exact h
    · omega
  | n + 1, k, y, I, hy, w, h => by
    refine fill_has gs step hgs n (k + step) (y * gs) _ (by rw [hy, hgs, pow_add]) w ?_
    rcases h with h | ⟨i, hi, rfl⟩
    · exact Or.inl (insert_has (Or.inr h))
    · rcases i with _ | i
      · exact Or.inl (insert_has (Or.inl (by rw [hy, Nat.mul_zero, Nat.add_zero])))
      · exact Or.inr ⟨i, by omega, by rw [Nat.mul_succ, Nat.add_assoc, Nat.add_comm (step * i)]⟩

/-- `baby` holds every power below `2^17`. -/
theorem baby_has {j : ℕ} (hj : j < 2 ^ 17) : (baby[(g ^ j).lane]?).isSome :=
  fill_has g 1 (pow_one g).symm _ 0 1 ∅ (pow_zero g).symm _
    (Or.inr ⟨j, hj, by rw [Nat.one_mul, Nat.zero_add]⟩)

theorem baby_lt : IdxLt baby (2 ^ 17) :=
  fill_lt g 1 Nat.one_pos _ 0 1 ∅ _ (idxLt_empty _) (by omega)

/-! ## Searches -/

theorem bsgs_lt : ∀ (n a : ℕ) (y : K) (k : ℕ), bsgs n a y = some k → k < 2 ^ 17 * (a + n)
  | 0, _, _, _, h => by rw [bsgs.eq_1] at h; cases h
  | n + 1, a, y, k, h => by
    rw [bsgs.eq_2] at h
    split at h
    · rename_i j hj
      cases h
      have := baby_lt _ _ hj
      rw [Nat.mul_add, Nat.mul_add]
      omega
    · have := bsgs_lt n (a + 1) _ k h
      omega

theorem bsgs_isSome : ∀ (n a : ℕ) (y : K) (j : ℕ), y = g ^ j → j < 2 ^ 17 * n → (bsgs n a y).isSome
  | 0, _, _, _, _, hj => by omega
  | n + 1, a, y, j, hy, hj => by
    rw [bsgs.eq_2]
    split
    · rfl
    · rename_i hn
      have hj' : 2 ^ 17 ≤ j := by
        by_contra hlt
        have := baby_has (j := j) (by omega)
        rw [← hy, hn] at this
        exact absurd this (by simp)
      refine bsgs_isSome n (a + 1) _ (j - 2 ^ 17) ?_ (by rw [Nat.mul_succ] at hj; omega)
      rw [hy, show j = j - 2 ^ 17 + 2 ^ 17 by omega, pow_add, mul_assoc, mul_comm (g ^ 2 ^ 17),
        giant_mul, mul_one, Nat.add_sub_cancel]

theorem boundedDlog_lt {x : K} {nbits k : ℕ} (h : boundedDlog x nbits = some k) :
    k < 2 ^ max nbits 17 := by
  unfold boundedDlog at h
  have := bsgs_lt _ 0 x k h
  rw [Nat.zero_add] at this
  split_ifs at this with hn
  · rw [max_eq_left hn.le]
    rwa [← pow_add, Nat.add_sub_cancel' hn.le] at this
  · rw [max_eq_right (by omega)]
    omega

/-- The bounded discrete logarithm finds every power in its range. -/
theorem boundedDlog_complete {k nbits : ℕ} (hk : k < 2 ^ nbits) (hn : nbits ≤ 62) :
    boundedDlog (g ^ k) nbits = some k := by
  have hs : (boundedDlog (g ^ k) nbits).isSome := by
    unfold boundedDlog
    refine bsgs_isSome _ 0 _ k rfl ?_
    split_ifs with h
    · rwa [← pow_add, Nat.add_sub_cancel' h.le]
    · rw [Nat.mul_one]; exact lt_of_lt_of_le hk (Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.mp hs
  rw [hk']
  have h1 := boundedDlog_ok hk'
  have h2 := boundedDlog_lt hk'
  have h3 : 2 ^ max nbits 17 ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ nbits ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) hn
  rw [gpow_inj (by omega) (by omega) h1]

theorem resolve_lt {coarse : Idx} {B : ℕ} (hc : IdxLt coarse B) :
    ∀ (n j : ℕ) (y : K) (k : ℕ), resolve coarse n j y = some k → k < B + j + n
  | 0, _, _, _, h => by rw [resolve.eq_1] at h; cases h
  | n + 1, j, y, k, h => by
    rw [resolve.eq_2] at h
    split at h
    · rename_i k0 hk0
      cases h
      have := hc _ _ hk0
      omega
    · have := resolve_lt hc n (j + 1) _ k h
      omega

/-! ## The table -/

/-- The exponents the table holds are below `2^31`. -/
structure Dlog.Small (D : Dlog) : Prop where
  noted : IdxLt D.noted (2 ^ 31)
  coarse : IdxLt D.coarse D.cover
  cover : D.cover ≤ 2 ^ 31

theorem Dlog.small_empty : Dlog.empty.Small := ⟨idxLt_empty _, idxLt_empty _, by simp [Dlog.empty]⟩

theorem Dlog.Small.grow {D : Dlog} (h : D.Small) {n : ℕ} (hn : n + 64 ≤ 2 ^ 31) :
    (D.grow n).Small := by
  obtain ⟨noted, coarse, cover, top⟩ := D
  obtain ⟨h1, h2, h3⟩ := h
  dsimp only at h1 h2 h3
  unfold Dlog.grow
  dsimp only
  split_ifs with hc
  · have hm : 64 * ((n - cover) / 64 + 1) ≤ n - cover + 64 := by omega
    exact ⟨h1, fill_lt _ 64 (by norm_num) _ _ _ _ (cover + 64 * ((n - cover) / 64 + 1))
      (h2.mono (by omega)) le_rfl,
      show cover + 64 * ((n - cover) / 64 + 1) ≤ 2 ^ 31 by omega⟩
  · exact ⟨h1, h2, h3⟩

theorem Dlog.Small.note {D : Dlog} (h : D.Small) {k : ℕ} (hk : k < 2 ^ 31) : (D.note k).Small := by
  obtain ⟨noted, coarse, cover, top⟩ := D
  exact ⟨h.noted.insert hk, h.coarse, h.cover⟩

theorem orElse_none {o : Option ℕ} {f : Unit → Option ℕ} (h : o.orElse f = none) : f () = none := by
  cases o with
  | none => exact h
  | some a => cases h

theorem clog_le {b : ℕ} (hb : b ≤ 2 ^ 30) : Nat.clog 2 b ≤ 30 := Nat.clog_le_of_le_pow hb

/-- `log` finds every power below its bound. -/
theorem Dlog.log_complete {D : Dlog} (hD : D.Ok) (hS : D.Small) {k b : ℕ} (hk : k < b)
    (hb : b ≤ 2 ^ 30) : ∃ D', D.log (g ^ k) b = (some k, D') ∧ D'.Ok ∧ D'.Small := by
  have hkb : k < 2 ^ 30 := by omega
  unfold Dlog.log
  split
  · rename_i k' hk'
    have := hS.noted _ _ hk'
    rw [gpow_inj (by omega) (by omega) (hD.noted.get hk'), ite_eq_left hk]
    exact ⟨D, rfl, hD, hS⟩
  · have hcl := clog_le hb
    split
    · rename_i k' hk'
      have hx : g ^ k' = g ^ k ∧ k' < 2 ^ 32 := by
        rcases orElse_some hk' with hk' | hk'
        · refine ⟨by rw [resolve_ok hD.coarse _ _ _ _ hk', pow_zero, mul_one], ?_⟩
          have := resolve_lt hS.coarse _ _ _ _ hk'
          have := hS.cover
          omega
        · refine ⟨boundedDlog_ok hk', ?_⟩
          have := boundedDlog_lt hk'
          have : 2 ^ max (Nat.clog 2 b) 17 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
      rw [gpow_inj (by omega) (by omega) hx.1, ite_eq_left hk]
      exact ⟨_, rfl, hD.note k, hS.note (by omega)⟩
    · rename_i hn
      have := orElse_none hn
      rw [boundedDlog_complete (lt_of_lt_of_le hk (Nat.le_pow_clog (by norm_num) b))
        (by omega)] at this
      cases this

/-- `logOr` finds every power below its bound. -/
theorem St.logOr_complete {s : St} (hD : s.dl.Ok) (hS : s.dl.Small) {k b : ℕ} {f : Fault}
    (hk : k < b) (hb : b ≤ 2 ^ 30) :
    ∃ D', s.logOr (g ^ k) b f = .ok (k, { s with dl := D' }) ∧ D'.Ok ∧ D'.Small := by
  obtain ⟨D', h, h1, h2⟩ := Dlog.log_complete hD hS hk hb
  refine ⟨D', ?_, h1, h2⟩
  unfold St.logOr
  rw [St.log_eq, h]
  rfl

/-! ## Decoding -/

/-- An operand that is a power below `2^28`. -/
def IsOff (o : K) : Prop := ∃ k < 2 ^ 28, g ^ k = o

/-- Every operand of an instruction is a power below `2^28`. -/
def Decodable : LeanIsaInstruction → Prop
  | .xor a b c => IsOff a ∧ IsOff b ∧ IsOff c
  | .mulNative a b c => IsOff a ∧ IsOff b ∧ IsOff c
  | .setConstant o _ => IsOff o
  | .deref o1 o2 o3 _ => IsOff o1 ∧ IsOff o2 ∧ IsOff o3
  | .jump c d f => IsOff c ∧ IsOff d ∧ IsOff f
  | .keccak om otail ob8 ocap oout _ _ _ =>
    (∀ c, IsOff (keccakInputCellOffset om otail ob8 ocap c)) ∧ IsOff oout

/-- Every offset of an `Op` is below `2^28`. -/
def OpSmall : Op → Prop
  | .xor a b c => a < 2 ^ 28 ∧ b < 2 ^ 28 ∧ c < 2 ^ 28
  | .mul a b c => a < 2 ^ 28 ∧ b < 2 ^ 28 ∧ c < 2 ^ 28
  | .set o _ => o < 2 ^ 28
  | .deref a b c _ => a < 2 ^ 28 ∧ b < 2 ^ 28 ∧ c < 2 ^ 28
  | .jump a b c => a < 2 ^ 28 ∧ b < 2 ^ 28 ∧ c < 2 ^ 28
  | .keccak ins out _ _ _ => (∀ i ∈ ins.toList, i < 2 ^ 28) ∧ out < 2 ^ 28

theorem offOf_lt {o : K} {k : ℕ} (h : offOf o = some k) : k < 2 ^ 28 := boundedDlog_lt h

theorem offOf_complete {o : K} (h : IsOff o) : ∃ k, offOf o = some k := by
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨k, boundedDlog_complete hk (by norm_num)⟩

theorem optMapM_isSome {α β : Type} (f : α → Option β) :
    ∀ l : List α, (∀ a ∈ l, (f a).isSome) → (l.mapM f).isSome
  | [], _ => rfl
  | a :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a (List.mem_cons_self ..))
    obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp
      (optMapM_isSome f l fun x hx ↦ h x (List.mem_cons_of_mem _ hx))
    simp [List.mapM_cons, hb, hbs]

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ b ∈ l', ∃ a ∈ l, R a b
  | _, _, .nil, _, hb => nomatch hb
  | _, _, .cons h hs, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self .., h⟩
    · obtain ⟨a, ha, h'⟩ := forall₂_mem_right hs b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h'⟩

theorem decode_small {ins : LeanIsaInstruction} {op : Op} (h : decode ins = some op) :
    OpSmall op := by
  cases ins with
  | keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    simp only [decode, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨l, hl, k, hk, rfl⟩ := h
    refine ⟨fun i hi ↦ ?_, offOf_lt hk⟩
    obtain ⟨c, -, hc⟩ := forall₂_mem_right (optMapM_ok _ _ _ hl) i (by simpa using hi)
    exact offOf_lt hc
  | _ =>
    simp only [decode, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, h⟩ := h
    first
    | (obtain ⟨b, hb, c, hc, rfl⟩ := h; exact ⟨offOf_lt ha, offOf_lt hb, offOf_lt hc⟩)
    | (obtain rfl := h; exact offOf_lt ha)

/-- An instruction whose operands are powers below `2^28` decodes. -/
theorem decode_complete {ins : LeanIsaInstruction} (h : Decodable ins) :
    ∃ op, decode ins = some op := by
  cases ins with
  | keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    obtain ⟨hin, hout⟩ := h
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (optMapM_isSome
      (fun c ↦ offOf (keccakInputCellOffset om otail ob8 ocap c)) (List.finRange 13)
      fun c _ ↦ Option.isSome_iff_exists.mpr (offOf_complete (hin c)))
    obtain ⟨k, hk⟩ := offOf_complete hout
    exact ⟨_, by
      simp only [decode, hl, hk, Option.bind_eq_bind, Option.bind_some, Option.pure_def]; rfl⟩
  | xor a b c =>
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩ :=
      And.imp offOf_complete (And.imp offOf_complete offOf_complete) h
    exact ⟨_, by simp only [decode, hx, hy, hz, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]; rfl⟩
  | mulNative a b c =>
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩ :=
      And.imp offOf_complete (And.imp offOf_complete offOf_complete) h
    exact ⟨_, by simp only [decode, hx, hy, hz, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]; rfl⟩
  | setConstant o k =>
    obtain ⟨x, hx⟩ := offOf_complete h
    exact ⟨_, by
      simp only [decode, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def]; rfl⟩
  | deref a b c mode =>
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩ :=
      And.imp offOf_complete (And.imp offOf_complete offOf_complete) h
    exact ⟨_, by simp only [decode, hx, hy, hz, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]; rfl⟩
  | jump a b c =>
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩ :=
      And.imp offOf_complete (And.imp offOf_complete offOf_complete) h
    exact ⟨_, by simp only [decode, hx, hy, hz, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]; rfl⟩

end

end LeanVM.Prover.Exec
