module

public import LeanVM.Guest.Mode.ResRef
public import LeanVM.Guest.WalkWindows

/-!
# The residuals by family

What each residual needs of the reference `M` at an instance's frame `fp`, by its shape (`Obl`):
a window bound `[[q]·g^k]`'s exponent below `N` needs every cell that word names to hold `g^e`,
`e < N`; a frame cell's bound `[o]`'s exponent below `N` needs `M (fp + o) = g^e`, `e < N`; a run
inside one over the same product, stride and offset (`subBound`) needs its bounds inside the
other's; a run of `S` consecutive cells inside the `S` interleaved runs of stride `S` over a table
(`subTab`) needs its base to be an entry of the table; any other residual needs itself. `obl_rres`:
the obligation gives the residual. `resRef_obl`: one function's `ResRef` from its nonzero residuals'
products (`nz_mul`) and the other residuals' obligations, at the frame of every state.

The obligations' sources: `rwins_of_winsAt`, a window bound from B1's `WinsAt` on the windows'
pointer; `nz_gpow`, a divisor holding a power of `g`; `nz_oneX`, a divisor `x` or `x·k` (`k`
nonzero) of a product `1 + x` (`oneXAt`, the shape `open_stacked`'s challenge divisions have), from
the reference's `XOR` and `MUL`s (`ref_xor`, `ref_mul`).
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.B1 LeanVM.Guest.Core
open LeanVM.Prover.Exec

@[expose] public section

/-! ## Uniqueness on the reference -/

section

variable {M : ℕ → E} {fp : ℕ}

theorem rbs_uniq : ∀ {bs : List (Base × ℕ)} {v v' : E}, RBs M fp bs v → RBs M fp bs v' → v = v'
  | [], _, _, h1, h2 => h1.trans h2.symm
  | (_, _) :: _, _, _, ⟨_, _, hu, hw, rfl⟩, ⟨_, _, hu', hw', rfl⟩ => by
    rw [rbase_uniq hu hu', rbs_uniq hw hw']

theorem rmono_uniq {m : Mono} {v v' : E} (h : RMono M fp m v) (h' : RMono M fp m v') : v = v' := by
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨w', hw', rfl⟩ := h'
  rw [rbs_uniq hw hw']

theorem ridx_uniq : ∀ {i : Idx} {x x' : ℕ}, RIdx M fp i x → RIdx M fp i x' → x = x'
  | .num _, _, _, h1, h2 => h1.trans h2.symm
  | .ex _ _, _, _, ⟨_, e, hv, rfl, he, rfl⟩, ⟨_, e', hv', h1', he', rfl⟩ => by
    have h := (rbase_uniq hv hv').trans h1'
    have := gpow_inj (by omega) (by omega) (ofK_injective h)
    omega

end

/-! ## The obligations -/

/-- Run `bs = [b]` is over `a`'s product with `a`'s stride and offset. -/
def subBound (a : Rng) : List Rng → Bool
  | [b] => b.q.beq a.q && b.S == a.S && b.d == a.d
  | _ => false

/-- A run inside a run over the same product, stride and offset: its bounds inside the other's. -/
def SubBound (M : ℕ → E) (fp : ℕ) (a : Rng) : List Rng → Prop
  | [b] => ∃ xlo xhi ylo yhi, RIdx M fp a.lo xlo ∧ RIdx M fp a.hi xhi ∧ RIdx M fp b.lo ylo ∧
      RIdx M fp b.hi yhi ∧ ylo ≤ xlo ∧ xhi ≤ yhi
  | _ => False

/-- Run `a` is `S` consecutive cells and `bs` the `S` runs of stride `S` and offsets `0, …, S - 1`
over one product with one range. -/
def subTab (a : Rng) : List Rng → Bool
  | [] => false
  | b :: bs => a.lo.beq (.num 0) && a.hi.beq (.num b.S) && a.S == 1 && a.d == 0 &&
      (b :: bs).all (fun c ↦ c.q.beq b.q && c.lo.beq b.lo && c.hi.beq b.hi && c.S == b.S) &&
      (b :: bs).map (·.d) == List.range b.S

/-- `S` consecutive cells inside a table read with stride `S`: the run's base is the table's at an
entry inside its range. -/
def SubTab (M : ℕ → E) (fp : ℕ) (a : Rng) : List Rng → Prop
  | [] => False
  | b :: _ => ∀ vq vb, RMono M fp a.q vq → RMono M fp b.q vb → ∃ ylo yhi i, RIdx M fp b.lo ylo ∧
      RIdx M fp b.hi yhi ∧ ylo ≤ i ∧ i < yhi ∧ vq = vb * ofK (g ^ (b.S * i))

/-- **What a residual needs of the reference**, by its family. -/
def Obl (M : ℕ → E) (fp : ℕ) : Res → Prop
  | .lt (.ex (.hp q k) 0) (.num N) =>
    N ≤ 2 ^ 62 ∧ ∀ x, Names (M (fp + q) * ofK (g ^ k)) x → ∃ e < N, M x = ofK (g ^ e)
  | .lt (.ex (.fr o) 0) (.num N) => N ≤ 2 ^ 62 ∧ ∃ e < N, M (fp + o) = ofK (g ^ e)
  | .sub a bs =>
    if subBound a bs then SubBound M fp a bs else if subTab a bs then SubTab M fp a bs else RSub M fp a bs
  | r => RRes M fp r

/-- A residual has an obligation of its own (`Obl` is not the residual itself): a window or frame
cell bound, a run inside another over the same product or inside a table, or a nonzero divisor. -/
def oblFam : Res → Bool
  | .lt (.ex (.hp _ _) 0) (.num _) => true
  | .lt (.ex (.fr _) 0) (.num _) => true
  | .sub a bs => subBound a bs || subTab a bs
  | .nz _ => true
  | _ => false

/-- **Every residual of a function has an obligation of its own.** -/
def famOk (F : Fun) (len : ℕ) : Bool :=
  (List.range len).all fun i ↦ ((F.res.get i).getD []).all oblFam

/-- A residual, if an order, bounds frame cell `o`'s exponent below `N`. -/
def frAt (o N : ℕ) : Res → Bool
  | .lt (.ex (.fr o') 0) (.num N') => o' == o && N' == N
  | .lt _ _ => false
  | _ => true

/-- **Every order residual bounds frame cell `o`'s exponent below `N`.** -/
def ltFr (F : Fun) (len o N : ℕ) : Bool :=
  (List.range len).all fun i ↦ ((F.res.get i).getD []).all (frAt o N)

theorem subBound_rsub {M : ℕ → E} {fp : ℕ} {a : Rng} :
    ∀ {bs : List Rng}, subBound a bs = true → SubBound M fp a bs → RSub M fp a bs
  | [b], hc, ⟨xlo, xhi, ylo, yhi, h1, h2, h3, h4, hlo, hhi⟩ => by
    simp only [subBound, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨hq, hS⟩, hd⟩ := hc
    have hq := Mono.beq_eq hq
    refine ⟨xlo, xhi, h1, h2, fun vq hvq j hj1 hj2 ↦ ⟨b, List.mem_singleton_self _,
      fun vb ylo' yhi' hvb hylo hyhi ↦ ⟨j, ?_, ?_, ?_⟩⟩⟩
    · rw [← ridx_uniq h3 hylo]; omega
    · rw [← ridx_uniq h4 hyhi]; omega
    · rw [hq] at hvb
      rw [rmono_uniq hvq hvb, hS, hd]
  | [], hc, _ => by simp [subBound] at hc
  | _ :: _ :: _, hc, _ => by simp [subBound] at hc

theorem ofK_mulR (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

theorem subTab_rsub {M : ℕ → E} {fp : ℕ} {a : Rng} :
    ∀ {bs : List Rng}, subTab a bs = true → SubTab M fp a bs → RSub M fp a bs
  | b :: bs, hc, h => by
    simp only [subTab, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨hlo, hhi⟩, hS⟩, hd⟩, hall⟩, hds⟩ := hc
    refine ⟨0, b.S, by rw [Idx.beq_eq hlo]; rfl, by rw [Idx.beq_eq hhi]; rfl, fun vq hvq j _ hj ↦ ?_⟩
    have hjm : j ∈ (b :: bs).map (·.d) := by rw [hds]; exact List.mem_range.mpr hj
    obtain ⟨c, hc, hcd⟩ := List.mem_map.mp hjm
    obtain ⟨⟨⟨hcq, hclo⟩, hchi⟩, hcS⟩ := hall c hc
    refine ⟨c, hc, fun vb ylo yhi hvb hylo hyhi ↦ ?_⟩
    rw [Mono.beq_eq hcq] at hvb
    rw [Idx.beq_eq hclo] at hylo
    rw [Idx.beq_eq hchi] at hyhi
    obtain ⟨ylo', yhi', i, h1, h2, h3, h4, he⟩ := h vq vb hvq hvb
    obtain rfl := ridx_uniq h1 hylo
    obtain rfl := ridx_uniq h2 hyhi
    refine ⟨i, h3, h4, ?_⟩
    rw [he, hS, hd, hcS, hcd, mul_assoc, ← ofK_mulR, ← pow_add, one_mul, add_zero]
  | [], hc, _ => by simp [subTab] at hc

/-- **An obligation gives its residual.** -/
theorem obl_rres {M : ℕ → E} {fp : ℕ} {r : Res} (hin : RIn M fp r) (h : Obl M fp r) : RRes M fp r := by
  unfold Obl at h
  split at h
  · obtain ⟨hN, h⟩ := h
    obtain ⟨⟨_, x, hx, _⟩, _⟩ := hin
    obtain ⟨e, he, hxe⟩ := h x hx
    exact ⟨e, _, ⟨M x, e, ⟨x, hx, rfl⟩, hxe, by omega, rfl⟩, rfl, he⟩
  · obtain ⟨hN, e, he, hxe⟩ := h
    exact ⟨e, _, ⟨_, e, rfl, hxe, by omega, rfl⟩, rfl, he⟩
  · show RSub M fp _ _
    split at h
    · exact subBound_rsub (by assumption) h
    · split at h
      · exact subTab_rsub (by assumption) h
      · exact h
  · exact h

/-- **A function's residuals from their obligations**: `ResRef` for one certificate whose nonzero
residuals are `MUL` divisors, given each product cell nonzero on the reference and the other
residuals' obligations. -/
theorem resRef_obl {prog : LeanIsaProgram} {adv : Advice} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx}
    {X : St → Prop} {Kc : Cert} (hκ : κ ≤ 28) (hC : Ctx.of prog adv = .ok C) (hK : CertOk C Kc)
    (hm : nzMul Kc.F Kc.code = true)
    (hnum : ∀ s i, X s → Fine (refMem img) s → OnRef prog img n s → i < Kc.code.length →
      s.pc = Kc.F.entry + i → ∀ o, Res.nz o ∈ (Kc.F.res.get i).getD [] →
        refMem img (s.fp + numAt Kc.code i) ≠ 0)
    (hobl : ∀ s i, X s → Fine (refMem img) s → OnRef prog img n s → i < Kc.code.length →
      s.pc = Kc.F.entry + i → ∀ r ∈ (Kc.F.res.get i).getD [], (∀ o, r ≠ .nz o) →
        Obl (refMem img) s.fp r) :
    ResRef prog img n [Kc] X :=
  resRef_mul hκ hC hK hm hnum fun s i hX hs hon hi hpc r hr hnz hin ↦
    obl_rres hin (hobl s i hX hs hon hi hpc r hr hnz)

/-! ## Windows -/

/-- A path window is at most six bits wide. -/
theorem qwWin_le {d cd k : ℕ} (hk : k < qwNp d cd) : (qwWin d cd k).2 ≤ 6 := by
  unfold qwWin
  split_ifs <;> simp only [qwNp] at * <;> omega

/-- **The windows on the reference from B1's `WinsAt`**: the word at frame cell `q` a pointer `w`
in `K` whose path windows `WinsAt` bounds on a reader `rd`, each of the first `n` windows' cells
read in `rd` with the reference's word there. -/
theorem rwins_of_winsAt {rd : Reader} {M : ℕ → E} {fp q d cd n : ℕ} {w : E} (hq : M (fp + q) = w)
    (hK : IsInK w) (hn : n ≤ qwNp d cd) (hW : WinsAt rd d cd w)
    (hag : ∀ k < n, ∀ x, Names (w * ofK (g ^ k)) x → ∃ v, rd (g ^ x) = some v ∧ M x = v) :
    RWins M fp q n 64 := by
  intro k hk x hx
  rw [hq] at hx
  obtain ⟨v, hv, rfl⟩ := hag k hk x hx
  have hx1 := hx.1
  rw [limb_mul_ofK] at hx1
  have ha : w.limb 0 * addressOfIndex k = g ^ x := hx1
  rw [← ha] at hv
  obtain ⟨e, he, hve⟩ := hW k (by unfold qwN; omega) _ ⟨hK, hv⟩
  refine ⟨e, lt_of_lt_of_le he ?_, hve⟩
  calc 2 ^ (qwWin d cd k).2 ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (qwWin_le (by omega))
    _ = 64 := by norm_num

/-- `rwins_of_winsAt` on a reader the reference agrees with (`RefRd`), the windows' cells read. -/
theorem rwins_of_winsAt_ref {rd : Reader} {M : ℕ → E} (hrd : LeanVM.Prover.Exec.RefRd rd M)
    {fp q d cd n : ℕ} {w : E} (hq : M (fp + q) = w) (hK : IsInK w) (hn : n ≤ qwNp d cd)
    (hW : WinsAt rd d cd w) (hdef : ∀ k < n, ∃ v, rd (w.limb 0 * addressOfIndex k) = some v) :
    RWins M fp q n 64 :=
  rwins_of_winsAt hq hK hn hW fun k hk x hx ↦ by
    obtain ⟨v, hv⟩ := hdef k hk
    have hx1 := hx.1
    rw [limb_mul_ofK] at hx1
    have ha : w.limb 0 * addressOfIndex k = g ^ x := hx1
    rw [ha] at hv
    have hx2 := hx.2
    unfold maxCells at hx2
    exact ⟨v, hv, (hrd x v (by omega) hv).2⟩

/-- A window bound's obligation from the windows. -/
theorem obl_win {M : ℕ → E} {fp q n N k : ℕ} (hN : N ≤ 2 ^ 62) (hw : RWins M fp q n N) (hk : k < n) :
    Obl M fp (.lt (.ex (.hp q k) 0) (.num N)) :=
  ⟨hN, fun x hx ↦ hw k hk x hx⟩

/-! ## Nonzero divisors -/

/-- A divisor holding a power of `g` is nonzero. -/
theorem nz_gpow {M : ℕ → E} {fp o e : ℕ} (h : M (fp + o) = ofK (g ^ e)) : RRes M fp (.nz o) := by
  show M (fp + o) ≠ 0
  rw [h]
  intro h0
  have := congrArg (fun z : E ↦ z.limb 0) h0
  simp only [limb_ofK, limb_zero] at this
  exact pow_ne_zero _ g_ne_zero this

/-- **A divisor of a product `1 + x`**: `x`, or `x·k` with `k ≠ 0`, is nonzero where the product
is its multiple. -/
theorem nz_oneX {c a o x : E} (hmul : c = a * o) (hxor : c = 1 + x)
    (hox : o = x ∨ ∃ k, o = x * k ∧ k ≠ 0) : o ≠ 0 := by
  intro ho
  rw [ho, mul_zero] at hmul
  have hx : x = 1 := by
    have h := hmul.symm.trans hxor
    rw [eq_comm, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
    exact h.symm
  rcases hox with h | ⟨k, h, hk⟩
  · rw [h, hx] at ho; exact one_ne_zero ho
  · rw [h, hx, one_mul] at ho; exact hk ho

/-- The reference's words at frame `fp` satisfy instruction `ins` (an `XOR` or a `MUL`). -/
def ROp (M : ℕ → E) (fp : ℕ) : OffsetInstruction → Prop
  | .xor a b c => M (fp + c) = M (fp + a) + M (fp + b)
  | .mul a b c => M (fp + c) = M (fp + a) * M (fp + b)
  | _ => True

/-- **The reference's `XOR`**: at a state on the reference run whose instruction is
`[c] = [a] + [b]`, the reference's words satisfy it. -/
theorem ref_xor {prog : LeanIsaProgram} {adv : Advice} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx}
    (hκ : κ ≤ 28) (hC : Ctx.of prog adv = .ok C) {s : St} (hs : Fine (refMem img) s)
    (hon : OnRef prog img n s) {a b c : ℕ} (hop : C.ops[s.pc]? = some (.xor a b c)) :
    refMem img (s.fp + c) = refMem img (s.fp + a) + refMem img (s.fp + b) := by
  obtain ⟨hsize, hdecC⟩ := ctx_of_spec hC
  obtain ⟨hlt, hrun⟩ := hon
  obtain ⟨hpc, hop'⟩ := Array.getElem?_eq_some_iff.mp hop
  have hsm := ctx_small hC s.pc hpc
  rw [hop'] at hsm
  have hpc2 : s.pc < 2 ^ prog.logSize := hsize ▸ hpc
  have hdec := hdecC s.pc hpc2 hpc
  rw [hop'] at hdec
  obtain ⟨k, hk⟩ : ∃ k, n - s.steps = k + 1 := ⟨n - s.steps - 1, by omega⟩
  rw [hk] at hrun
  have hne : (⟨g ^ s.pc, g ^ s.fp⟩ : Registers K) ≠ Registers.final prog := fun h ↦ by
    rw [run_succ, ite_eq_left h] at hrun; cases hrun
  rw [run_succ_of_ne_final hne, Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun
  obtain ⟨r1, hstep, -⟩ := hrun
  rw [step_of_fetch_eq_some (prog.fetch_gpow ⟨s.pc, hpc2⟩), LeanVM.Semantics.execute] at hstep
  generalize prog.instructions ⟨s.pc, hpc2⟩ = ins at hstep hdec
  cases ins <;> simp only [OpOf] at hdec
  obtain ⟨rfl, rfl, rfl⟩ := hdec
  simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
  obtain ⟨vA, hA, vB, hB, vC, hC', hg⟩ := hstep
  simp [guard] at hg
  obtain ⟨rfl, -⟩ := hg
  obtain ⟨ha, hb, hc⟩ := hsm
  rw [((refRd_img hκ img).at hs.fp ha hA).2, ((refRd_img hκ img).at hs.fp hb hB).2,
    ((refRd_img hκ img).at hs.fp hc hC').2]

/-- `[c] = [one] + [x]` at `i1` with `[one] = 1`, and the divisor `o` is `x` or, at `i2`,
`[o] = [x]·[k]`: the shape of a residual `MUL` `[c] = [a]·[o]` at offset `i` dividing `1 + x` by
`x` or `x·k`, `[one]` and `[k]` named by the caller (constant cells). -/
def oneXAt (code : List OffsetInstruction) (i i1 : ℕ) (i2 : Option ℕ) (one k : ℕ) : Bool :=
  match code[i]?, code[i1]? with
  | some (.mul _ o c), some (.xor one' x c') => one' == one && c' == c &&
    match i2 with
    | none => x == o
    | some i2 => match code[i2]? with
      | some (.mul x' k' o') => x' == x && k' == k && o' == o
      | _ => false
  | _, _ => false

/-- The divisor of the `MUL` at an offset. -/
def divAt (code : List OffsetInstruction) (i : ℕ) : ℕ :=
  match code[i]? with
  | some (.mul _ o _) => o
  | _ => 0

/-- **A challenge division's divisor is nonzero**: at a residual `MUL` of shape `oneXAt`, on a
reference satisfying it and the instructions at `i1` and `i2`, with `[one] = 1` and `[k] ≠ 0`. -/
theorem nz_oneX_at {M : ℕ → E} {fp : ℕ} {code : List OffsetInstruction} {i i1 : ℕ} {i2 : Option ℕ}
    {one k : ℕ} (h : oneXAt code i i1 i2 one k = true) (hi : i < code.length) (hi1 : i1 < code.length)
    (hr : ROp M fp code[i]) (hr1 : ROp M fp code[i1])
    (hr2 : ∀ j (hj : j < code.length), i2 = some j → ROp M fp code[j])
    (hone : M (fp + one) = 1) (hk : i2.isSome → M (fp + k) ≠ 0) :
    RRes M fp (.nz (divAt code i)) := by
  show M (fp + divAt code i) ≠ 0
  unfold oneXAt at h
  unfold divAt
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi1] at h
  rw [List.getElem?_eq_getElem hi]
  generalize code[i] = I at h hr
  generalize code[i1] = I1 at h hr1
  cases I with
  | mul a o c =>
    cases I1 with
    | xor one' x c' =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, rfl⟩, h⟩ := h
      simp only [ROp] at hr hr1
      rw [hone] at hr1
      refine nz_oneX hr hr1 ?_
      cases i2 with
      | none => simp only [beq_iff_eq] at h; left; rw [h]
      | some j =>
        simp only at h
        split at h
        · rename_i x' k' o' hj
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          obtain ⟨hjl, hjv⟩ := List.getElem?_eq_some_iff.mp hj
          have := hr2 j hjl rfl
          rw [hjv] at this
          exact Or.inr ⟨_, this, hk rfl⟩
        · simp at h
    | _ => simp at h
  | _ => simp at h

end

end LeanVM.Guest.Mode
