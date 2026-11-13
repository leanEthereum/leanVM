/-
  LeanVM.Guest.Memory.StaticVecSound

  A vector check is the check of each coordinate (`chkFnV_proj`).
-/

module

public import LeanVM.Guest.Memory.StaticVec
public import LeanVM.Guest.Memory.StaticSound

/-!
# Coordinates of the vector checker

Every step of `chkFnV` is `chkFn`'s (not counting words) on vectors, and taking coordinate `i`
commutes with each (`Vec.getD_add`, `transBV_proj`, `siteBV_proj`, `blockRV_proj`): the vector
walk's coordinate `i` is the walk of the certificates' coordinates `i`, so a vector check passes
only if each coordinate's does (`chkFnV_proj`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-! ## Vectors -/

theorem Vec.getD_add : ∀ (a b : Vec) (i : ℕ), (a.add b).getD i 0 = a.getD i 0 + b.getD i 0
  | [], b, i => by simp only [Vec.add, List.getD_nil, Nat.zero_add]
  | a :: as, [], i => by simp only [Vec.add, List.getD_nil, Nat.add_zero]
  | a :: as, b :: bs, 0 => rfl
  | a :: as, b :: bs, i + 1 => by simp only [Vec.add, List.getD_cons_succ, Vec.getD_add as bs i]

theorem Vec.getD_max : ∀ (a b : Vec) (i : ℕ), (a.max b).getD i 0 = Max.max (a.getD i 0) (b.getD i 0)
  | [], b, i => by simp only [Vec.max, List.getD_nil, Nat.zero_max]
  | a :: as, [], i => by simp only [Vec.max, List.getD_nil, Nat.max_zero]
  | a :: as, b :: bs, 0 => rfl
  | a :: as, b :: bs, i + 1 => by simp only [Vec.max, List.getD_cons_succ, Vec.getD_max as bs i]

theorem Vec.getD_scale (n : ℕ) : ∀ (a : Vec) (i : ℕ), (a.scale n).getD i 0 = n * a.getD i 0
  | [], i => by simp only [Vec.scale, List.map_nil, List.getD_nil, Nat.mul_zero]
  | a :: as, 0 => rfl
  | a :: as, i + 1 => by
      simp only [Vec.scale, List.map_cons, List.getD_cons_succ]
      exact Vec.getD_scale n as i

theorem Vec.getD_le : ∀ {a b : Vec}, a.le b = true → ∀ i, a.getD i 0 ≤ b.getD i 0
  | [], b, _, i => by simp only [List.getD_nil, Nat.zero_le]
  | a :: as, [], h, i => by
      simp only [Vec.le, Bool.and_eq_true, Nat.beq_eq] at h
      cases i with
      | zero => simp only [List.getD_cons_zero, h.1, List.getD_nil, Nat.le_refl]
      | succ i => simpa only [List.getD_cons_succ, List.getD_nil] using Vec.getD_le h.2 i
  | a :: as, b :: bs, h, i => by
      simp only [Vec.le, Bool.and_eq_true, Nat.ble_eq] at h
      cases i with
      | zero => simpa only [List.getD_cons_zero] using h.1
      | succ i => simpa only [List.getD_cons_succ] using Vec.getD_le h.2 i

variable (i : ℕ)

theorem AffV.proj_add (a b : AffV) : (a.add b).proj i = (a.proj i).add (b.proj i) := by
  simp only [AffV.proj, AffV.add, Aff.add, Vec.getD_add, List.map_append]

theorem AffV.proj_scale (n : ℕ) (a : AffV) : (a.scale n).proj i = (a.proj i).scale n := by
  simp only [AffV.proj, AffV.scale, Aff.scale, Vec.getD_scale, List.map_map, Function.comp_def]

theorem AccV.proj_add (a b : AccV) : (a.add b).proj i = (a.proj i).add (b.proj i) := by
  simp only [AccV.proj, AccV.add, Acc.add, AffV.proj_add]

theorem AccV.proj_join (a b : AccV) : (a.join b).proj i = (a.proj i).join (b.proj i) := by
  simp only [AccV.proj, AccV.join, Acc.join, AffV.proj, Vec.getD_max, List.map_append]

theorem AccV.proj_zero : AccV.zero.proj i = Acc.zero := rfl

theorem addAccV_proj (x y : Option AccV) :
    (Option.addAccV x y).map (AccV.proj i) = Option.addAcc (x.map (AccV.proj i)) (y.map (AccV.proj i)) := by
  cases x <;> cases y <;> simp [Option.addAccV, Option.addAcc, AccV.proj_add]

theorem maxAccV_proj (x y : Option AccV) :
    (Option.maxAccV x y).map (AccV.proj i) = Option.maxAcc (x.map (AccV.proj i)) (y.map (AccV.proj i)) := by
  cases x <;> cases y <;> simp [Option.maxAccV, Option.maxAcc, AccV.proj_join]

theorem sumBV_proj {α : Type} (f : α → Option AccV) :
    ∀ l : List α, (sumBV f l).map (AccV.proj i) = sumB (fun a => (f a).map (AccV.proj i)) l
  | [] => by simp [sumBV, sumB, AccV.proj_zero, Acc.zero]
  | a :: as => by rw [sumBV, sumB, addAccV_proj, sumBV_proj f as]

theorem maxBV_proj {α : Type} (f : α → Option AccV) :
    ∀ l : List α, (maxBV f l).map (AccV.proj i) = maxB (fun a => (f a).map (AccV.proj i)) l
  | [] => by simp [maxBV, maxB, AccV.proj_zero, Acc.zero]
  | a :: as => by rw [maxBV, maxB, maxAccV_proj, maxBV_proj f as]

theorem sumB_map {α β : Type} (f : β → Option Acc) (g : α → β) :
    ∀ l : List α, sumB f (l.map g) = sumB (fun a => f (g a)) l
  | [] => rfl
  | a :: as => by rw [List.map_cons, sumB, sumB, sumB_map f g as]

/-! ## Call sites -/

variable {ρ : Env} {ps : List V} {args : List V}

theorem termBV_proj (q : ℕ × Vec) :
    (termBV ρ ps args q).map (AccV.proj i) = termB ρ ps args (q.1, q.2.getD i 0) := by
  unfold termBV termB
  rcases args[q.1]? with _ | v
  · rfl
  · dsimp only
    rcases cls ρ ps v with e | k | _
    · simp only [Option.map_some, AccV.proj, AffV.proj, Vec.getD_scale, Nat.mul_comm, List.map_nil]
    · rfl
    · rfl

theorem preBV_proj (q : ℕ × ℕ) : (preBV ρ ps args q).map (AccV.proj i) = preB ρ ps args q := by
  unfold preBV preB
  rcases args[q.1]? with _ | v
  · rfl
  · dsimp only
    rcases cls ρ ps v with e | k | _
    · dsimp only
      split_ifs <;> rfl
    · rfl
    · rfl

theorem transBV_proj (pre : List (ℕ × ℕ)) (b : AffV) :
    (transBV ρ ps args pre b).map (AccV.proj i) = transB ρ ps args pre (b.proj i) := by
  unfold transBV transB
  rw [addAccV_proj, addAccV_proj, sumBV_proj, sumBV_proj]
  simp only [Option.map_some, termBV_proj, preBV_proj]
  rw [show (b.proj i).cs = b.cs.map fun q => (q.1, q.2.getD i 0) from rfl, sumB_map]
  rfl

theorem siteBV_proj (cert : String → CertV) (wl : String → Option ℕ) (g : String) :
    (siteBV cert ρ ps g args).map (AccV.proj i) =
      siteB (fun g => (cert g).proj i) wl false ρ ps g args := by
  unfold siteBV siteB
  dsimp only
  rcases cert g with _ | ⟨pre, b, ks⟩ | ⟨endc, pre, b, ks⟩
  · rfl
  · exact transBV_proj i pre b
  · simp only [CertV.proj, phB, Bool.false_eq_true, ↓reduceIte]
    rw [← transBV_proj]
    rcases args[0]? with _ | v0
    · rfl
    · simp only []
      rcases cls ρ ps v0 with a0 | _ | _
      · simp only []
        rcases transBV ρ ps args pre b with _ | r
        · rcases endc with _ | e
          · rcases args[1]? with _ | v1
            · rfl
            · dsimp only
              rcases cls ρ ps v1 with e | k | _ <;> dsimp only <;> (try split_ifs) <;> rfl
          · dsimp only
            split_ifs <;> rfl
        · have hpow : ∀ e, Option.map (AccV.proj i)
              (if a0 < e ∧ e < 2 ^ 64 - 1 then some ((r.1.scale (e - a0)).add ⟨[], []⟩, r.2) else none) =
              if a0 < e ∧ e < 2 ^ 64 - 1 then some (((r.1.proj i).scale (e - a0)).add Acc.zero.1, r.2)
                else none := by
            intro e
            split_ifs
            · simp only [Option.map_some, AccV.proj, AffV.proj_add, AffV.proj_scale]; rfl
            · rfl
          have hparam : ∀ k, Option.map (AccV.proj i)
              (if r.1.cs = [] then some ((⟨[], [(k, r.1.c)]⟩ : AffV).add ⟨[], []⟩, (k, a0) :: r.2) else none) =
              if (r.1.proj i).cs = [] then
                some ((⟨0, [(k, (r.1.proj i).c)]⟩ : Aff).add Acc.zero.1, (k, a0) :: r.2) else none := by
            intro k
            by_cases hr : r.1.cs = []
            · have hr' : (r.1.proj i).cs = [] := by simp only [AffV.proj, hr, List.map_nil]
              simp only [hr, hr', ↓reduceIte, Option.map_some, AccV.proj, AffV.proj_add]
              rfl
            · have hr' : ¬ (r.1.proj i).cs = [] := by
                simpa only [AffV.proj, List.map_eq_nil_iff] using hr
              simp only [hr, hr', ↓reduceIte, Option.map_none]
          rcases endc with _ | e
          · rcases args[1]? with _ | v1
            · rfl
            · dsimp only
              rcases cls ρ ps v1 with e | k | _
              · exact hpow e
              · exact hparam k
              · rfl
          · exact hpow e
      · rfl
      · rfl

/-! ## Blocks -/

theorem atomB_false (ks : List (V × ℕ)) (ρ : Env × BEnv) (a : Atom) :
    atomB false ks ps ρ a = some (Acc.zero, envAtom ks ρ a) := by
  cases a with
  | const v w =>
      simp only [atomB, envAtom]
      rcases vlookup v ks with _ | e
      · rfl
      · dsimp only
        split_ifs <;> rfl
  | hint h => cases h <;> rfl
  | _ => rfl

variable {cert : String → CertV} {wl : String → Option ℕ} {ks : List (V × ℕ)} {self : String}

theorem blockRV_cons (s : Stmt) (ss : List Stmt) (ρ : Env × BEnv) :
    blockRV cert ks ps self (s :: ss) ρ = match stmtRV cert ks ps self s ρ with
      | none => none
      | some (r, some ρ') => Option.addAccV (some r) (blockRV cert ks ps self ss ρ')
      | some (r, none) => some r := rfl

theorem armsRV_cons (a : List Stmt) (as : List (List Stmt)) (ρ : Env × BEnv) :
    armsRV cert ks ps self (a :: as) ρ =
      Option.maxAccV (blockRV cert ks ps self a ρ) (armsRV cert ks ps self as ρ) := rfl

/-- Coordinate `i` of a statement's result. -/
def projS (r : AccV × Option (Env × BEnv)) : Acc × Option (Env × BEnv) := (r.1.proj i, r.2)

theorem map_pair_proj (x : Option AccV) (ρ : Env × BEnv) :
    (x.map fun r => (r, some ρ)).map (projS i) = (x.map (AccV.proj i)).map fun r => (r, some ρ) := by
  cases x <;> rfl

mutual
/-- **Coordinate `i` of a block's vector walk** is the walk of the certificates' coordinates. -/
theorem blockRV_proj : ∀ (ss : List Stmt) (ρ : Env × BEnv),
    (blockRV cert ks ps self ss ρ).map (AccV.proj i) =
      blockR (fun g => (cert g).proj i) wl false ks ps self ss ρ
  | [], ρ => rfl
  | s :: ss, ρ => by
      rw [blockRV_cons, blockR_cons]
      have hs : (stmtRV cert ks ps self s ρ).map (projS i) =
          stmtR (fun g => (cert g).proj i) wl false ks ps self s ρ := by
        cases s with
        | atom a =>
            show some (projS i (AccV.zero, some (envAtom ks ρ a))) =
              (atomB false ks ps ρ a).map fun q => (q.1, some q.2)
            rw [atomB_false]
            simp [projS, AccV.proj_zero]
        | ite c z n =>
            show ((Option.maxAccV (blockRV cert ks ps self z ρ) (blockRV cert ks ps self n ρ)).map
                fun r => (r, some ρ)).map (projS i) =
              (Option.maxAcc (blockR (fun g => (cert g).proj i) wl false ks ps self z ρ)
                (blockR (fun g => (cert g).proj i) wl false ks ps self n ρ)).map fun r => (r, some ρ)
            rw [map_pair_proj, maxAccV_proj, blockRV_proj z ρ, blockRV_proj n ρ]
        | match_ x arms =>
            show ((armsRV cert ks ps self arms ρ).map fun r => (r, some ρ)).map (projS i) =
              (armsR (fun g => (cert g).proj i) wl false ks ps self arms ρ).map fun r => (r, some ρ)
            rw [map_pair_proj, armsRV_proj arms ρ]
        | call g args rets =>
            show ((siteBV cert ρ.1 ps g args).map fun r => (r, some ρ)).map (projS i) =
              (siteB (fun g => (cert g).proj i) wl false ρ.1 ps g args).map fun r => (r, some ρ)
            rw [map_pair_proj, siteBV_proj]
        | callIf c g args =>
            show (if g = self then none
                else (Option.addAccV (siteBV cert ρ.1 ps g args) (some AccV.zero)).map
                  fun r => (r, some ρ)).map (projS i) =
              if g = self then none
                else (Option.addAcc (siteB (fun g => (cert g).proj i) wl false ρ.1 ps g args)
                  (phB wl false g)).map fun r => (r, some ρ)
            split_ifs
            · rfl
            · rw [map_pair_proj, addAccV_proj, siteBV_proj i cert wl]
              rfl
        | dispatch x gs args rets =>
            show ((maxBV (fun g => siteBV cert ρ.1 ps g args) gs).map fun r => (r, some ρ)).map (projS i) =
              (maxB (fun g => siteB (fun g => (cert g).proj i) wl false ρ.1 ps g args) gs).map
                fun r => (r, some ρ)
            rw [map_pair_proj, maxBV_proj]
            simp only [siteBV_proj i cert wl]
        | ret vs => simp [stmtRV, stmtR, projS, AccV.proj_zero]
      rw [← hs]
      rcases stmtRV cert ks ps self s ρ with _ | ⟨r, _ | ρ'⟩
      · rfl
      · rfl
      · simp only [Option.map_some, projS]
        rw [← blockRV_proj ss ρ', addAccV_proj]
        rfl

/-- `blockRV_proj` for arms. -/
theorem armsRV_proj : ∀ (arms : List (List Stmt)) (ρ : Env × BEnv),
    (armsRV cert ks ps self arms ρ).map (AccV.proj i) =
      armsR (fun g => (cert g).proj i) wl false ks ps self arms ρ
  | [], ρ => rfl
  | a :: as, ρ => by
      rw [armsRV_cons, armsR_cons, maxAccV_proj, blockRV_proj a ρ, armsRV_proj as ρ]
end

theorem leB_proj {w : Vec} {r : AccV} {b : AffV} (h : AffV.leB ⟨w.add r.1.c, r.1.cs⟩ b = true) :
    Aff.leB ⟨w.getD i 0 + (r.proj i).1.c, (r.proj i).1.cs⟩ (b.proj i) = true := by
  simp only [AffV.leB, Bool.and_eq_true, beq_iff_eq] at h
  have hc := Vec.getD_le h.1 i
  rw [Vec.getD_add] at hc
  simp only [Aff.leB, AccV.proj, AffV.proj, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, h.2]
  exact ⟨hc, trivial⟩

/-- **A vector check passes only if each coordinate's does.** -/
theorem chkFnV_proj {look : String → CertV} {own : CertV} {w : Vec} {fn : Fn}
    (h : chkFnV look own w fn = true) (wl : String → Option ℕ) :
    chkFn (fun g => (look g).proj i) wl false (own.proj i) (w.getD i 0) fn = true := by
  cases own with
  | none => rfl
  | stat pre b ks =>
      simp only [chkFnV] at h
      show chkFn (fun g => (look g).proj i) wl false (.stat pre (b.proj i) ks) (w.getD i 0) fn = true
      unfold chkFn
      dsimp only
      rw [← blockRV_proj (cert := look)]
      rcases hb : blockRV look ks fn.params fn.name fn.body ([], []) with _ | r
      · rw [hb] at h; cases h
      · rw [hb] at h
        simp only [Bool.and_eq_true] at h
        simp only [Option.map_some, Bool.and_eq_true]
        exact ⟨leB_proj i h.1, h.2⟩
  | loop endc pre b ks =>
      simp only [chkFnV] at h
      show chkFn (fun g => (look g).proj i) wl false (.loop endc pre (b.proj i) ks) (w.getD i 0) fn = true
      unfold chkFn
      dsimp only
      rcases hs : loopShape fn endc with _ | pre'
      · rw [hs] at h; cases h
      · rw [hs] at h
        dsimp only at h ⊢
        rw [← blockRV_proj (cert := look)]
        rcases hb : blockRV look ks fn.params fn.name pre' ([], []) with _ | r
        · rw [hb] at h; cases h
        · rw [hb] at h
          simp only [Bool.and_eq_true] at h
          simp only [Option.map_some, Bool.and_eq_true]
          refine ⟨⟨⟨leB_proj i h.1.1.1, h.1.1.2⟩, ?_⟩, h.2⟩
          simpa [AffV.proj] using h.1.2

end
end LeanVM.Guest.Memory
