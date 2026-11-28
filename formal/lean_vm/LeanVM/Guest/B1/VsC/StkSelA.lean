/-
  LeanVM.Guest.B1.VsC.StkSelA

  `stack_selectors` completes placed: `selector_tables`, then one `column_selector` per block.
-/

module

public import LeanVM.Guest.B1.VsC.ColSelA
public import LeanVM.Guest.B1.VsC.SelTablesA
public import LeanVM.Guest.B1.Stack.StkSel
public import LeanVM.Guest.B1.Stack.TermPure
public import LeanVM.Guest.Complete.ComposeA
public import LeanVM.Guest.Memory.SelArm
import LeanVM.Guest.CoreRef

/-!
# `stack_selectors`, placed

`stack_selectors__L{n}(offs, kaps, point, point1, g_squares)` (`stsBody n`), placed at frame `fp`
and cursor `c`: its `HeapBuf` of `52` selectors at `c`, its own words the selectors `selW layout x`
there; `selector_tables__L{n}` at the aligned base past it, then each block's
`column_selector__L{n}_L{κ}` (`kidsAtF_csel`), `κ` the block's `variableCount`. The valuation is
fixed by the layout (`stsVal`): each block's offset `g^index`, kappa `g^variableCount` and selector,
the tables' pointer at the cursor `selector_tables` takes. The walk takes each dispatch's arm `κ`
(`walk_stsBody`), and each selector, the column selector's product, is the placement's `eqAbove`
(`eqAbove_selProd`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Stack LeanVM.Guest.B1.Whir LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## The path -/

/-- Block `b`'s events at kappa `κ`. -/
def stsEvB (n κ b : ℕ) : List Ev :=
  [.atom (.load (.n (7 + 5 * b)) (.n 0) b), .atom (.const (.n (8 + 5 * b)) (csW 34)),
    .atom (.mul (.n (9 + 5 * b)) (.n 4) (.n (8 + 5 * b))), .atom (.load (.n (10 + 5 * b)) (.n 1) b),
    .call (cselName n κ) [.n (7 + 5 * b), .n 5, .n (9 + 5 * b)] [.n (11 + 5 * b)],
    .atom (.load (.n (11 + 5 * b)) (.n 6) b)]

/-- `stack_selectors__L{n}`'s path, block `b` at kappa `κ b`. -/
def stsEvs (n : ℕ) (κ : ℕ → ℕ) : List Ev :=
  [.call ("selector_tables__L" ++ natStr n) [.n 2, .n 3] [.n 5], .atom (.hint (.alloc (.n 6) 52))] ++
    ((List.range 52).map fun b => stsEvB n (κ b) b).flatten ++ [.atom (.copy (.n 267) (.n 6))]

/-- Block `b`'s column selector call. -/
def cselCall (n : ℕ) (κ : ℕ → ℕ) (b : ℕ) : Call :=
  ⟨cselName n (κ b), [.n (7 + 5 * b), .n 5, .n (9 + 5 * b)], [.n (11 + 5 * b)], true⟩

theorem walk_flatten_fall {σ : Val} (blk : ℕ → List Stmt) (evs : ℕ → List Ev) :
    ∀ l : List ℕ, (∀ b ∈ l, walk σ (blk b) = .fall (evs b)) →
      walk σ (l.map blk).flatten = .fall (l.map evs).flatten
  | [], _ => rfl
  | b :: l, h => by
    rw [List.map_cons, List.flatten_cons, walk_append, h b List.mem_cons_self,
      walk_flatten_fall blk evs l (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))]
    simp [Out.seq, Out.pre]

theorem walk_stsBlock (σ : Val) (n b κ : ℕ) (hκ : κ < 31)
    (hx : σ (.n (10 + 5 * b)) = ofK (addressOfIndex κ)) :
    walk σ (stsBlock n b) = .fall (stsEvB n κ b) := by
  have hp := pick_eq σ (.n (10 + 5 * b)) [.n (7 + 5 * b), .n 5, .n (9 + 5 * b)] [.n (11 + 5 * b)]
    ((List.range 31).map (cselName n)) 0 κ (by simpa using hκ) (by simp) (by rw [hx, Nat.zero_add])
  have hn : ((List.range 31).map (cselName n))[κ]! = cselName n κ := by
    rw [getElem!_pos _ _ (by simpa using hκ)]; simp
  rw [hn] at hp
  simp [stsBlock, stsEvB, walk, walk1, hp, osCst, osMul, Out.seq, Out.pre]

/-- **The walk of `stack_selectors__L{n}`**, each dispatch at its block's kappa. -/
theorem walk_stsBody (σ : Val) (n : ℕ) (κ : ℕ → ℕ) (hκ : ∀ b < 52, κ b < 31)
    (hx : ∀ b < 52, σ (.n (10 + 5 * b)) = ofK (addressOfIndex (κ b))) :
    walk σ (stsBody n) = .ret (stsEvs n κ) [.n 267] := by
  have hb := walk_flatten_fall (σ := σ) (stsBlock n) (fun b => stsEvB n (κ b) b) (List.range 52)
    fun b hb => walk_stsBlock σ n b (κ b) (hκ b (List.mem_range.mp hb)) (hx b (List.mem_range.mp hb))
  rw [stsBody, stsBodyA, stsEvs, List.append_assoc, List.append_assoc, walk_append, walk_append, hb]
  simp [walk, walk1, Out.seq, Out.pre]

theorem mem_stsEvs {n : ℕ} {κ : ℕ → ℕ} {e : Ev} (he : e ∈ stsEvs n κ) :
    e = .call ("selector_tables__L" ++ natStr n) [.n 2, .n 3] [.n 5] ∨ e = .atom (.hint (.alloc (.n 6) 52)) ∨
      e = .atom (.copy (.n 267) (.n 6)) ∨ ∃ b < 52, e ∈ stsEvB n (κ b) b := by
  simp only [stsEvs, List.mem_append, List.mem_cons, List.mem_flatten, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at he
  rcases he with ((he | he) | ⟨l, ⟨b, hb, rfl⟩, he⟩) | he
  · exact Or.inl he
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (Or.inr ⟨b, hb, he⟩))
  · exact Or.inr (Or.inr (Or.inl he))

theorem calls_append (a b : List Ev) : calls (a ++ b) = calls a ++ calls b := List.filterMap_append

theorem calls_stsBlocks (n : ℕ) (κ : ℕ → ℕ) : ∀ l : List ℕ,
    calls ((l.map fun b => stsEvB n (κ b) b).flatten) = l.map (cselCall n κ)
  | [] => rfl
  | b :: l => by
    rw [List.map_cons, List.flatten_cons, calls_append, calls_stsBlocks n κ l]
    rfl

theorem calls_stsEvs (n : ℕ) (κ : ℕ → ℕ) :
    calls (stsEvs n κ) = ⟨"selector_tables__L" ++ natStr n, [.n 2, .n 3], [.n 5], true⟩ ::
      (List.range 52).map (cselCall n κ) := by
  rw [stsEvs, calls_append, calls_append, calls_stsBlocks]
  rfl

theorem filterMap_stsEvs {α : Type} {g : Ev → Option α} {n : ℕ} {κ : ℕ → ℕ}
    (hb : ∀ b < 52, ∀ e ∈ stsEvB n (κ b) b, g e = none) :
    (stsEvs n κ).filterMap g = ([.call ("selector_tables__L" ++ natStr n) [.n 2, .n 3] [.n 5],
      .atom (.hint (.alloc (.n 6) 52))] : List Ev).filterMap g ++ [.atom (.copy (.n 267) (.n 6))].filterMap g := by
  have h0 : ((List.range 52).map fun b => stsEvB n (κ b) b).flatten.filterMap g = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro e he
    simp only [List.mem_flatten, List.mem_map, List.mem_range] at he
    obtain ⟨l, ⟨b, hb', rfl⟩, he⟩ := he
    exact hb b hb' e he
  rw [stsEvs, List.filterMap_append, List.filterMap_append, h0, List.append_nil]

/-! ## The valuation -/

/-- Block `b`'s value `r`: its offset `g^ix b`, `g^34`, the nibble shares' pointer, its kappa
`g^vc b`, its selector `sw b`. -/
def stsBlk (gsq : E) (ix vc : ℕ → ℕ) (sw : ℕ → E) (b r : ℕ) : E :=
  match r with
  | 0 => gen ^ ix b
  | 1 => csW 34
  | 2 => gsq * csW 34
  | 3 => gen ^ vc b
  | _ => sw b

/-- `stack_selectors`' values: its arguments, the tables' pointer `se`, its buffer `sel`, then its
blocks' (`stsBlk`). -/
def stsVal (offs kaps pt pt1 gsq se sel : E) (ix vc : ℕ → ℕ) (sw : ℕ → E) (i : ℕ) : E :=
  if i = 0 then offs else if i = 1 then kaps else if i = 2 then pt else if i = 3 then pt1
  else if i = 4 then gsq else if i = 5 then se else if i = 6 then sel else if i = 267 then sel
  else stsBlk gsq ix vc sw ((i - 7) / 5) ((i - 7) % 5)

section Val

variable {offs kaps pt pt1 gsq se sel : E} {ix vc : ℕ → ℕ} {sw : ℕ → E} {b : ℕ}

theorem stsVal_at (hb : b < 52) {i : ℕ} (r : ℕ) (hi : i = 7 + 5 * b + r) (hr : r < 5) :
    stsVal offs kaps pt pt1 gsq se sel ix vc sw i = stsBlk gsq ix vc sw b r := by
  subst hi
  unfold stsVal
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    show (7 + 5 * b + r - 7) % 5 = r by omega, show (7 + 5 * b + r - 7) / 5 = b by omega]

end Val

/-! ## The column selectors -/

/-- Where the column selectors of blocks `bs` end, from the cursor `cur`. -/
def cselEnd (fs : String → ℕ) (al : String → Bool) (n : ℕ) (κ : ℕ → ℕ) : List ℕ → ℕ → ℕ
  | [], cur => cur
  | b :: bs, cur => cselEnd fs al n κ bs (allocBase (al (cselName n (κ b))) cur + fs (cselName n (κ b)))

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- The column selectors' end, every frame below `2^16`: a fresh frame per selector. -/
theorem cselEnd_le (hfs : ∀ f, fs f < 2 ^ 16) (n : ℕ) (κ : ℕ → ℕ) :
    ∀ (bs : List ℕ) (cur : ℕ), cselEnd fs al n κ bs cur ≤ cur + bs.length * 2 ^ 17
  | [], cur => by simp [cselEnd]
  | b :: bs, cur => by
    have ih := cselEnd_le hfs n κ bs (allocBase (al (cselName n (κ b))) cur + fs (cselName n (κ b)))
    have := allocBase_le (al (cselName n (κ b))) cur
    have := hfs (cselName n (κ b))
    simp only [cselEnd, List.length_cons]
    omega

/-- **The column selectors complete one after another**, each placed fresh at the aligned base. -/
theorem kidsAtF_csel {k n : ℕ} (hk : 4 ≤ k) (h4 : 4 ≤ n) (h8 : n ≤ 8) {σ : Val} {R : ℕ → Prop}
    {Pre Oend : Reader → Prop} (κ ix : ℕ → ℕ) (p p1 : ℕ → E) (se sg : E) :
    ∀ (bs : List ℕ) (O : Reader → Prop) (Dacc : ℕ → Prop) (cur : ℕ),
      (∀ rd, O rd → Oend rd) → (∀ rd, Pre rd → O rd → CselPre n p p1 se sg rd) →
      ((∀ t < 32 * n, ∃ m, se.limb 0 * addressOfIndex t = addressOfIndex m ∧ (R m ∨ Dacc m)) ∧
        ∀ t < 144, ∃ m, sg.limb 0 * addressOfIndex t = addressOfIndex m ∧ (R m ∨ Dacc m)) →
      (∀ b ∈ bs, κ b ≤ 30 ∧ ix b < 2 ^ (4 * n) ∧ 2 ^ κ b ∣ ix b ∧
        σ (.n (7 + 5 * b)) = gen ^ ix b ∧ σ (.n 5) = se ∧ σ (.n (9 + 5 * b)) = sg ∧
        σ (.n (11 + 5 * b)) = ∏ t ∈ Finset.Ico (κ b) (4 * n), selBit p p1 (ix b) t) →
      KidsAtF fs al cert k σ R Pre O Dacc (bs.map fun _ => PostQuiet) (bs.map (cselCall n κ)) cur
        (cselEnd fs al n κ bs cur) Oend (fun _ => False)
  | [], O, Dacc, cur, hO, _, _, _ => by
    rw [List.map_nil, List.map_nil, KidsAtF]
    exact ⟨rfl, hO, fun _ h => h.elim⟩
  | b :: bs, O, Dacc, cur, hO, hpre, hR, hb => by
    obtain ⟨h30, hix, hal, e7, e5, e9, e11⟩ := hb b List.mem_cons_self
    rw [List.map_cons, List.map_cons, KidsAtF]
    simp only [cselCall, ↓reduceIte, List.headD_cons, List.tail_cons]
    have ea : [V.n (7 + 5 * b), .n 5, .n (9 + 5 * b)].map σ = [gen ^ ix b, se, sg] := by simp [e7, e5, e9]
    have er : [V.n (11 + 5 * b)].map σ = [∏ t ∈ Finset.Ico (κ b) (4 * n), selBit p p1 (ix b) t] := by simp [e11]
    rw [ea, er]
    refine ⟨fs (cselName n (κ b)), allocBase (al (cselName n (κ b))) cur + fs (cselName n (κ b)), fun m => R m ∨ Dacc m, fun _ => False, fun _ => True, fun _ h => h, ?_,
      kidsAtF_csel hk h4 h8 κ ix p p1 se sg bs _ _ _ (fun rd h => hO rd h.1) (fun rd hp h => hpre rd hp h.1)
        ⟨fun t ht => ?_, fun t ht => ?_⟩ fun b' hb' => hb b' (List.mem_cons_of_mem _ hb')⟩
    · exact (column_selector_placed hk n (κ b) h4 h8 h30 hix hal p p1 se sg hR _ _).mono (fun _ h => h)
        (fun _ h => h) (fun _ h => h) (fun rd h => hpre rd h.1 h.2) (fun _ _ _ h => h)
    · obtain ⟨m, hm, h⟩ := hR.1 t ht
      exact ⟨m, hm, h.imp_right Or.inl⟩
    · obtain ⟨m, hm, h⟩ := hR.2 t ht
      exact ⟨m, hm, h.imp_right Or.inl⟩


/-! ## `stack_selectors` -/

/-- What `stack_selectors` reads of its caller's: the `52` offsets and kappas, the `40` coordinates of
the point and of one plus it, the nibble shares `[34, 178)` of the exponent tables. -/
def StsRegion (R : ℕ → Prop) (offs kaps pt pt1 gsq : E) : Prop :=
  (∀ b < 52, (∃ m, offs.limb 0 * addressOfIndex b = addressOfIndex m ∧ R m) ∧
      ∃ m, kaps.limb 0 * addressOfIndex b = addressOfIndex m ∧ R m) ∧
    (∀ i < 40, (∃ m, pt.limb 0 * addressOfIndex i = addressOfIndex m ∧ R m) ∧
      ∃ m, pt1.limb 0 * addressOfIndex i = addressOfIndex m ∧ R m) ∧
    ∀ t < 144, ∃ m, gsq.limb 0 * addressOfIndex (34 + t) = addressOfIndex m ∧ R m

/-- `MeaningStackSelectors`' hypotheses on the memory. -/
def StsPre (layout : Layout) (gmv : E) (x : List E) (offs kaps pt pt1 gsq : E) (rd : Reader) : Prop :=
  StackPlaced rd layout gmv offs kaps ∧ ExpTables rd gsq ∧
    ReadsAt rd pt (x ++ List.replicate (40 - x.length) 0) ∧
    ReadsAt rd pt1 (x.map (1 + ·) ++ List.replicate (40 - x.length) 1)

theorem ofK_aoi_addr (c t : ℕ) : (ofK (addressOfIndex c)).limb 0 * addressOfIndex t = addressOfIndex (c + t) := by
  simp [addressOfIndex, pow_add]

/-- Block `b`'s placement: its kappa below `31`, its index below `2^(4 n)` and aligned, its selector
the column selector's product. -/
theorem sts_block {bytecode : List K} {rows : List ℕ} {layout : Layout} {n : ℕ}
    (hbl : buildLayout bytecode layout.logMemory rows = some layout) (hL : layout.stackLog ≤ 30)
    (hn : (layout.stackLog + 3) / 4 = n) {x : List E} (hx : x.length = layout.stackLog) {b : ℕ} (hb : b < 52) :
    (blockP layout b).variableCount ≤ 30 ∧ (blockP layout b).index < 2 ^ (4 * n) ∧
      2 ^ (blockP layout b).variableCount ∣ (blockP layout b).index ∧
      layout.placements.getD (blockColumn b) none = some (blockP layout b) ∧
      selW layout x b = ∏ t ∈ Finset.Ico (blockP layout b).variableCount (4 * n),
        selBit (padPt x) (padPt1 x) (blockP layout b).index t := by
  obtain ⟨p, hp, -, -, hal, hin⟩ := layout_block hbl hb
  have hbp : blockP layout b = p := by rw [blockP, hp, Option.getD_some]
  have hvc : p.variableCount ≤ layout.stackLog := by
    have : 2 ^ p.variableCount ≤ 2 ^ layout.stackLog := le_trans (Nat.le_add_left _ _) hin
    exact (Nat.pow_le_pow_iff_right (by decide)).1 this
  have hidx : p.index < 2 ^ layout.stackLog := lt_of_lt_of_le (by
    have := Nat.one_le_two_pow (n := p.variableCount); omega) hin
  rw [selW, hbp]
  refine ⟨by omega, lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by decide) (by omega)), hal, hp, ?_⟩
  exact eqAbove_selProd x (vc := p.variableCount) (idx := p.index) (N := 4 * n) (by omega) (by rw [hx]; exact hidx)
    (by omega) (by omega)

/-- **`stack_selectors__L{n}` completes placed**, from its template. -/
theorem sts_placed {k : ℕ} (hk : 4 ≤ k) {name : String} {fn : Fn} {n : ℕ} (h4 : 4 ≤ n) (h8 : n ≤ 8)
    (hfind : coreProgram.find? name = some fn) (hparams : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4])
    (hbody : fn.body = stsBody n) {bytecode : List K} {rows : List ℕ} {layout : Layout}
    (hbl : buildLayout bytecode layout.logMemory rows = some layout) (hL : layout.stackLog ≤ 30)
    (hn : (layout.stackLog + 3) / 4 = n) {x : List E} (hx : x.length = layout.stackLog)
    {gmv offs kaps pt pt1 gsq : E} {R : ℕ → Prop} (hR : StsRegion R offs kaps pt pt1 gsq) (fp c : ℕ)
    (hfc : fp + fs name ≤ c) :
    ∃ e, ((∀ f, fs f < 2 ^ 16) → e ≤ c + 2 ^ 23) ∧
      CallAtA fs al cert k name [offs, kaps, pt, pt1, gsq] [ofK (addressOfIndex c)] R
      (fun i => c ≤ i ∧ i < c + 52) (fun rd => ∀ b < 52, LoadHolds rd (ofK (addressOfIndex c)) b (selW layout x b))
      (StsPre layout gmv x offs kaps pt pt1 gsq) PostQuiet (fs name) fp c e := by
  have hlp : coreProgram.loop name = false := by
    rw [Program.loop_of_find? hfind, Fn.loop, hbody, stsBody]; simp
  set st := "selector_tables__L" ++ natStr n with hst
  set c1 := allocBase (al st) (c + 52) + fs st with hc1
  set se : E := ofK (addressOfIndex c1) with hse
  set sel : E := ofK (addressOfIndex c) with hsel
  set sg : E := gsq * csW 34 with hsg
  set ix : ℕ → ℕ := fun b => (blockP layout b).index with hix
  set κ : ℕ → ℕ := fun b => (blockP layout b).variableCount with hκ
  set σ : Val := fun v => stsVal offs kaps pt pt1 gsq se sel ix κ (selW layout x) v.idx with hσ
  have hblk := fun b (hb : b < 52) => sts_block hbl hL hn hx hb
  have s7 : ∀ b < 52, σ (.n (7 + 5 * b)) = gen ^ ix b := fun b hb => stsVal_at hb 0 rfl (by decide)
  have s8 : ∀ b < 52, σ (.n (8 + 5 * b)) = csW 34 := fun b hb => stsVal_at (i := 8 + 5 * b) hb 1 (by omega) (by decide)
  have s9 : ∀ b < 52, σ (.n (9 + 5 * b)) = sg := fun b hb => stsVal_at (i := 9 + 5 * b) hb 2 (by omega) (by decide)
  have s10 : ∀ b < 52, σ (.n (10 + 5 * b)) = gen ^ κ b := fun b hb => stsVal_at (i := 10 + 5 * b) hb 3 (by omega) (by decide)
  have s11 : ∀ b < 52, σ (.n (11 + 5 * b)) = selW layout x b := fun b hb => stsVal_at (i := 11 + 5 * b) hb 4 (by omega) (by decide)
  have s5 : σ (.n 5) = se := by simp [hσ, stsVal]
  have s6 : σ (.n 6) = sel := by simp [hσ, stsVal]
  have s267 : σ (.n 267) = sel := by simp [hσ, stsVal]
  have hw : walk σ fn.body = .ret (stsEvs n κ) [.n 267] := by
    rw [hbody]
    exact walk_stsBody σ n κ (fun b hb => by have := (hblk b hb).1; simp only [hκ]; omega)
      (fun b hb => by rw [s10 b hb, gen_pow_eq_ofK])
  have hal : allocs σ (stsEvs n κ) = [52] := by
    rw [allocs, filterMap_stsEvs (fun b _ e he => by
      simp only [stsEvB, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)]
    rfl
  have hdst : allocDsts (stsEvs n κ) = [.n 6] := by
    rw [allocDsts, filterMap_stsEvs (fun b _ e he => by
      simp only [stsEvB, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)]
    rfl
  have hadr : addrs (stsEvs n κ) = [] := by
    rw [addrs, filterMap_stsEvs (fun b _ e he => by
      simp only [stsEvB, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)]
    rfl
  have s0 : σ (.n 0) = offs := by simp [hσ, stsVal]
  have s1 : σ (.n 1) = kaps := by simp [hσ, stsVal]
  have s2 : σ (.n 2) = pt := by simp [hσ, stsVal]
  have s3 : σ (.n 3) = pt1 := by simp [hσ, stsVal]
  have s4 : σ (.n 4) = gsq := by simp [hσ, stsVal]
  set Wo : Words := [(c, (List.range 52).map (selW layout x))] with hWo
  set OutSt : Reader → Prop := fun rd => ∀ j < n, ∀ w < 4, ∀ k < 2 ^ (w + 1),
    LoadHolds rd se (32 * j + selOff w + k * 2 ^ (3 - w)) (selLev (padPt x) (padPt1 x) j w k) with hOutSt
  have hWload : ∀ rd, HoldsWords rd Wo → ∀ b < 52, LoadHolds rd sel b (selW layout x b) := by
    intro rd h b hb
    have := h _ List.mem_cons_self b (by simpa using hb)
    simpa using this
  have hmemB : ∀ {e : Ev} {b : ℕ}, e ∈ stsEvB n (κ b) b →
      e = .atom (.load (.n (7 + 5 * b)) (.n 0) b) ∨ e = .atom (.const (.n (8 + 5 * b)) (csW 34)) ∨
      e = .atom (.mul (.n (9 + 5 * b)) (.n 4) (.n (8 + 5 * b))) ∨ e = .atom (.load (.n (10 + 5 * b)) (.n 1) b) ∨
      e = .call (cselName n (κ b)) [.n (7 + 5 * b), .n 5, .n (9 + 5 * b)] [.n (11 + 5 * b)] ∨
      e = .atom (.load (.n (11 + 5 * b)) (.n 6) b) := fun he => by
    simpa only [stsEvB, List.mem_cons, List.not_mem_nil, or_false] using he
  have hown : ∀ i, c ≤ i → i < c + 52 → ownData cert fp c name (allocs σ (stsEvs n κ)) (stsEvs n κ) i := by
    intro i h1 h2
    rw [hal]; unfold ownData; left
    exact ⟨(52, c), by simp [bases], h1, h2⟩
  have hub : (∀ f, fs f < 2 ^ 16) → cselEnd fs al n κ (List.range 52) (c1 + 32 * n) ≤ c + 2 ^ 23 := by
    intro hfs
    have h1 := cselEnd_le (al := al) hfs n κ (List.range 52) (c1 + 32 * n)
    have h2 := allocBase_le (al st) (c + 52)
    have h3 := hfs st
    simp only [List.length_range] at h1
    omega
  refine ⟨cselEnd fs al n κ (List.range 52) (c1 + 32 * n), hub, callAtA_node hlp hfc ⟨σ, fn, stsEvs n κ, [.n 267], Wo,
    (calls (stsEvs n κ)).map fun _ => PostQuiet, fun rd => HoldsWords rd Wo ∧ OutSt rd, fun _ => False,
    hfind, ?_, hw, ?_, ?_, ?_, ?_, ?_, fun i hi => Or.inl (hown i hi.1 hi.2), ?_, fun rd h => hWload rd h.1,
    ?_, ?_⟩⟩
  · rw [hparams]; simp [hσ, stsVal]
  · simp [s267, hsel]
  · rw [hal]; exact ⟨by rw [hdst]; simp [s6, bases, hsel], by rw [hadr]; simp⟩
  · rw [hal]
    exact ⟨fun q hq => by rw [List.mem_singleton] at hq; subst hq; right; simp, List.pairwise_singleton _ _⟩
  · intro A hA
    rw [loadAddrs, List.mem_filterMap] at hA
    obtain ⟨e, he, hA⟩ := hA
    rcases mem_stsEvs he with rfl | rfl | rfl | ⟨b, hb, he⟩
    · cases hA
    · cases hA
    · cases hA
    rcases hmemB he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Ev.loadAddr?, Option.some.injEq, reduceCtorEq] at hA <;> subst hA
    · obtain ⟨m, hm, hRm⟩ := (hR.1 b hb).1
      exact ⟨m, by rw [s0]; exact hm, Or.inr (Or.inl hRm)⟩
    · obtain ⟨m, hm, hRm⟩ := (hR.1 b hb).2
      exact ⟨m, by rw [s1]; exact hm, Or.inr (Or.inl hRm)⟩
    · exact ⟨c + b, by rw [s6, hsel]; exact ofK_aoi_addr c b, Or.inl (hown _ (by omega) (by omega))⟩
  · intro A hA
    rw [heapHintAddrs, List.mem_flatMap] at hA
    obtain ⟨e, he, hA⟩ := hA
    rcases mem_stsEvs he with rfl | rfl | rfl | ⟨b, hb, he⟩
    · cases hA
    · simp [Ev.hintAddrs, hintDest?] at hA
    · cases hA
    rcases hmemB he with rfl | rfl | rfl | rfl | rfl | rfl <;> cases hA
  · rw [calls_stsEvs, hal]
    simp only [List.map_cons, List.sum_cons, List.sum_nil, Nat.add_zero, KidsAtF, ↓reduceIte, List.headD_cons,
      List.tail_cons, List.map_map, List.map_nil, s2, s3, s5]
    refine ⟨fs st, c1 + 32 * n, R, fun i => c1 ≤ i ∧ i < c1 + 32 * n, OutSt, fun i hi => Or.inl (Or.inl hi), ?_, ?_⟩
    · refine (selector_tables_placed n h4 h8 (p := padPt x) (p1 := padPt1 x) (fun i hi => hR.2.1 i (by omega))
        (allocBase (al st) (c + 52)) c1).mono (fun _ h => h) (fun _ h => h) (fun _ h => h)
        (fun rd h => ⟨fun i hi => ?_, fun i hi => ?_⟩) (fun _ _ _ h => h)
      · have := h.1.2.2.1 i (by simp; omega)
        rwa [← List.getD_eq_getElem _ 0] at this
      · have := h.1.2.2.2 i (by simp; omega)
        rwa [← List.getD_eq_getElem _ 0] at this
    · refine kidsAtF_csel hk h4 h8 κ ix (padPt x) (padPt1 x) se sg (List.range 52) _ _ _ (fun rd h => h)
        (fun rd hp ho => ⟨ho.2, fun j hj u hu => ?_⟩) ⟨fun t ht => ⟨c1 + t, ofK_aoi_addr c1 t,
          Or.inr (Or.inr ⟨by omega, by omega⟩)⟩, fun t ht => ?_⟩ fun b hb => ?_
      · rw [hsg, csW_eq (by decide), loadHolds_mul_gen_pow,
          show 34 + (16 * j + u) = sizeBits + 16 * j + u by simp only [sizeBits]; omega]
        exact hp.2.1.2 j hj u hu
      · obtain ⟨m, hm, hRm⟩ := hR.2.2 t ht
        exact ⟨m, by rw [hsg, csW_eq (by decide), limb_gpow_addr]; exact hm, Or.inl (Or.inl hRm)⟩
      · have hb' := List.mem_range.mp hb
        obtain ⟨h1, h2, h3, -, h5⟩ := hblk b hb'
        exact ⟨h1, h2, h3, s7 b hb', s5, s9 b hb', by rw [s11 b hb']; exact h5⟩
  · intro rd _ hp ho e he
    rcases mem_stsEvs he with rfl | rfl | rfl | ⟨b, hb, he⟩
    · trivial
    · trivial
    · show σ (.n 267) = σ (.n 6); rw [s267, s6]
    rcases hmemB he with rfl | rfl | rfl | rfl | rfl | rfl
    · show LoadHolds rd (σ (.n 0)) b (σ (.n (7 + 5 * b)))
      obtain ⟨p, hp', hl, -⟩ := hp.1.2 b (by simpa [nStkBlocks, stackBlocks_length] using hb)
      obtain rfl := Option.some.inj ((hblk b hb).2.2.2.1.symm.trans hp')
      rw [s0, s7 b hb]; exact hl
    · exact s8 b hb
    · show σ (.n (9 + 5 * b)) = σ (.n 4) * σ (.n (8 + 5 * b)); rw [s9 b hb, s4, s8 b hb]
    · show LoadHolds rd (σ (.n 1)) b (σ (.n (10 + 5 * b)))
      obtain ⟨p, hp', -, hl⟩ := hp.1.2 b (by simpa [nStkBlocks, stackBlocks_length] using hb)
      obtain rfl := Option.some.inj ((hblk b hb).2.2.2.1.symm.trans hp')
      rw [s1, s10 b hb]; exact hl
    · trivial
    · show LoadHolds rd (σ (.n 6)) b (σ (.n (11 + 5 * b)))
      rw [s6, s11 b hb]; exact hWload rd ho.1 b hb
  · intro rd ts _ _ _ hv hp
    refine postQuiet_node hfind hw (fun a ha => ?_) (fun e he => ?_) hv hp _
    · rcases mem_stsEvs ha with h | h | h | ⟨b, hb, h⟩
      · cases h
      · cases h; rfl
      · cases h; rfl
      rcases hmemB h with h | h | h | h | h | h <;> cases h <;> rfl
    · rcases mem_stsEvs he with rfl | rfl | rfl | ⟨b, hb, he⟩
      · trivial
      · trivial
      · trivial
      rcases hmemB he with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

/-! ## The specializations -/

set_option maxRecDepth 100000 in
/-- **`stack_selectors__L{n}` completes placed**, every specialization, `4 ≤ n ≤ 8`: on a layout
`buildLayout` returns, its stack at most `2^30` words of `n` nibbles, the opening point `x` of its
length, its `52` selectors at the cursor, each block's `eqAbove` at `x`; its end within `2^23` of its
cursor when every frame is below `2^16`. -/
theorem stack_selectors_placedB {k : ℕ} (hk : 4 ≤ k) (n : ℕ) (h4 : 4 ≤ n) (h8 : n ≤ 8) {bytecode : List K}
    {rows : List ℕ} {layout : Layout} (hbl : buildLayout bytecode layout.logMemory rows = some layout)
    (hL : layout.stackLog ≤ 30) (hn : (layout.stackLog + 3) / 4 = n) {x : List E}
    (hx : x.length = layout.stackLog) {gmv offs kaps pt pt1 gsq : E} {R : ℕ → Prop}
    (hR : StsRegion R offs kaps pt pt1 gsq) (fp c : ℕ) (hfc : fp + fs ("stack_selectors__L" ++ natStr n) ≤ c) :
    ∃ e, ((∀ f, fs f < 2 ^ 16) → e ≤ c + 2 ^ 23) ∧
      CallAtA fs al cert k ("stack_selectors__L" ++ natStr n) [offs, kaps, pt, pt1, gsq]
      [ofK (addressOfIndex c)] R (fun i => c ≤ i ∧ i < c + 52)
      (fun rd => ∀ b < 52, LoadHolds rd (ofK (addressOfIndex c)) b (selW layout x b))
      (StsPre layout gmv x offs kaps pt pt1 gsq) PostQuiet (fs ("stack_selectors__L" ++ natStr n)) fp c e := by
  interval_cases n
  · exact sts_placed hk (by decide) (by decide) (coreProgram_find?_at (j := idx% «stack_selectors__L4») rfl)
      rfl stack_selectors_L4_body hbl hL hn hx hR fp c hfc
  · exact sts_placed hk (by decide) (by decide) (coreProgram_find?_at (j := idx% «stack_selectors__L5») rfl)
      rfl stack_selectors_L5_body hbl hL hn hx hR fp c hfc
  · exact sts_placed hk (by decide) (by decide) (coreProgram_find?_at (j := idx% «stack_selectors__L6») rfl)
      rfl stack_selectors_L6_body hbl hL hn hx hR fp c hfc
  · exact sts_placed hk (by decide) (by decide) (coreProgram_find?_at (j := idx% «stack_selectors__L7») rfl)
      rfl stack_selectors_L7_body hbl hL hn hx hR fp c hfc
  · exact sts_placed hk (by decide) (by decide) (coreProgram_find?_at (j := idx% «stack_selectors__L8») rfl)
      rfl stack_selectors_L8_body hbl hL hn hx hR fp c hfc

/-- **`stack_selectors__L{n}` completes placed** (`stack_selectors_placedB`, its bound forgotten). -/
theorem stack_selectors_placed {k : ℕ} (hk : 4 ≤ k) (n : ℕ) (h4 : 4 ≤ n) (h8 : n ≤ 8) {bytecode : List K}
    {rows : List ℕ} {layout : Layout} (hbl : buildLayout bytecode layout.logMemory rows = some layout)
    (hL : layout.stackLog ≤ 30) (hn : (layout.stackLog + 3) / 4 = n) {x : List E}
    (hx : x.length = layout.stackLog) {gmv offs kaps pt pt1 gsq : E} {R : ℕ → Prop}
    (hR : StsRegion R offs kaps pt pt1 gsq) (fp c : ℕ) (hfc : fp + fs ("stack_selectors__L" ++ natStr n) ≤ c) :
    ∃ e, CallAtA fs al cert k ("stack_selectors__L" ++ natStr n) [offs, kaps, pt, pt1, gsq]
      [ofK (addressOfIndex c)] R (fun i => c ≤ i ∧ i < c + 52)
      (fun rd => ∀ b < 52, LoadHolds rd (ofK (addressOfIndex c)) b (selW layout x b))
      (StsPre layout gmv x offs kaps pt pt1 gsq) PostQuiet (fs ("stack_selectors__L" ++ natStr n)) fp c e :=
  (stack_selectors_placedB (gmv := gmv) hk n h4 h8 hbl hL hn hx hR fp c hfc).imp fun _ h => h.2

end
end LeanVM.Guest.B1.VsC
