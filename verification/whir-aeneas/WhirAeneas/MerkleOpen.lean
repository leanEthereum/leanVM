import WhirAeneas.Merkle

/-! The rest of the generated `PrunedMerklePaths::open`: each query's sibling path over the
rebuilt levels (`push_path`), the per-query expansion into leaf images and paths (`expand`),
and the top-level composition with its guards, the distinct sorted queries, the leaf hashes
(`RowHash`) and the rebuild. -/
namespace WhirAeneas.Merkle
open Aeneas Aeneas.Std ReplaySource

private theorem loop_cont {α β : Type} {body : α → Result (ControlFlow α β)} {x x' : α}
    (h : body x = .ok (.cont x')) : loop body x = loop body x' := by
  rw [loop]; simp [h]

private theorem loop_done {α β : Type} {body : α → Result (ControlFlow α β)} {x : α} {y : β}
    (h : body x = .ok (.done y)) : loop body x = .ok y := by
  rw [loop]; simp [h]

/-! ## Paths over the known nodes -/

/-- The index of node `n`'s sibling. -/
def sibOf (n : Nat) : Nat := if n % 2 = 0 then n + 1 else n - 1

/-- The digest of the node of index `i` in a level, if present. -/
def lookup (lvl : List (Nat × Digest)) (i : Nat) : Option Digest :=
  (lvl.find? fun x => x.1 = i).map (·.2)

/-- The path from node `n` upward: its sibling's digest at each level, lowest first. -/
def pathFrom : List (List (Nat × Digest)) → Nat → Option (List Digest)
  | [], _ => some []
  | lvl :: rest, n => match lookup lvl (sibOf n) with
    | none => none
    | some d => (pathFrom rest (n / 2)).map (d :: ·)

/-- Where each level starts in the one buffer, then where the buffer ends. -/
def offsets (base : Nat) : List (List (Nat × Digest)) → List Nat
  | [] => [base]
  | l :: rest => base :: offsets (base + l.length) rest

theorem startsOf_eq (base : Nat) (lvls : List (List (Nat × Digest × Digest))) :
    startsOf base lvls = offsets base (lvls.map knownOf) := by
  induction lvls generalizing base with
  | nil => rfl
  | cons ps rest ih => simp [startsOf, offsets, ih]

theorem offsets_length (base : Nat) (ks : List (List (Nat × Digest))) :
    (offsets base ks).length = ks.length + 1 := by
  induction ks generalizing base with
  | nil => rfl
  | cons l rest ih => simp [offsets, ih]

theorem offsets_get (base : Nat) (ks : List (List (Nat × Digest))) :
    ∀ (l : Nat) (hl : l < (offsets base ks).length),
      (offsets base ks)[l] = base + ((ks.take l).map List.length).sum := by
  induction ks generalizing base with
  | nil => intro l hl; simp [offsets] at hl ⊢; try omega
  | cons k rest ih =>
    intro l hl
    cases l with
    | zero => simp [offsets]
    | succ l =>
      simp only [offsets, List.getElem_cons_succ]
      rw [ih]
      · simp; try omega
      all_goals (simp [offsets] at hl; omega)

theorem flatten_level (ks : List (List (Nat × Digest))) (l : Nat) (hl : l < ks.length) :
    ((ks.flatten.drop ((ks.take l).map List.length).sum).take ks[l].length) = ks[l] := by
  have key : ∀ (A B : List (List (Nat × Digest))) (x : List (Nat × Digest)),
      (((A ++ x :: B).flatten.drop (A.map List.length).sum).take x.length) = x := by
    intro A B x
    rw [List.flatten_append, ← List.length_flatten, List.drop_left, List.flatten_cons, List.take_left]
  have := key (ks.take l) (ks.drop (l + 1)) ks[l]
  rwa [← List.drop_eq_getElem_cons hl, List.take_append_drop] at this

theorem lookup_of_getElem (l : List (Nat × Digest)) (hs : l.Pairwise (fun a b => a.1 < b.1))
    (m : Nat) (hm : m < l.length) : lookup l l[m].1 = some l[m].2 := by
  induction l generalizing m with
  | nil => simp at hm
  | cons x rest ih =>
    rw [List.pairwise_cons] at hs
    cases m with
    | zero => simp [lookup]
    | succ m =>
      have hm' : m < rest.length := by simpa using hm
      have hx : x.1 ≠ rest[m].1 := by
        have := hs.1 rest[m] (List.getElem_mem hm'); omega
      have := ih hs.2 m hm'
      simp only [lookup] at this ⊢
      simp [List.find?_cons, hx, this]

theorem lookup_none (l : List (Nat × Digest)) (i : Nat) (h : i ∉ l.map (·.1)) : lookup l i = none := by
  simp only [lookup, Option.map_eq_none_iff, List.find?_eq_none]
  intro x hx he
  exact h (List.mem_map.mpr ⟨x, hx, by simpa using he⟩)

theorem node_position_eq (level : Slice (Usize × Digest)) (key : Usize)
    (hs : level.val.Pairwise (fun a b => a.1.val < b.1.val)) :
    ∃ res, merkle.node_position level key = .ok res ∧
      match res with
      | some m => ∃ hm : m.val < level.val.length, (level.val[m.val]).1 = key
      | none => key ∉ level.val.map (·.1) := by
  have hl := level.property
  obtain ⟨res, h, hr⟩ := node_position_loop_eq level key hs _ 0#usize (Slice.len level) le_rfl (by simp)
    (by simp) (by intro j hj; simp at hj) (by intro j hj _; simp at *; omega)
  exact ⟨res, by simp [merkle.node_position, h], hr⟩

theorem natNode_pairwise (l : List (Usize × Digest)) :
    (l.map natNode).Pairwise (fun a b => a.1 < b.1) ↔ l.Pairwise (fun a b => a.1.val < b.1.val) := by
  simp [List.pairwise_map, natNode]

theorem shr_lvl (hword : UScalarTy.Usize.numBits = 64) (q l : Usize) (hl : l.val < 64) :
    (Std.Usize.wrapping_shr q l).val = q.val / 2 ^ l.val := by
  rw [shr_val hword]; simp [Nat.mod_eq_of_lt hl]

theorem usize_max_odd (hword : UScalarTy.Usize.numBits = 64) : Usize.max % 2 = 1 := by
  rw [Usize.max_def, Usize.numBits_def, hword]; decide

theorem push_path_loop_eq (hword : UScalarTy.Usize.numBits = 64) (known : Slice (Usize × Digest))
    (starts : Slice Usize) (q : Usize) (ks : List (List (Nat × Digest)))
    (hk : known.val.map natNode = ks.flatten) (hst : starts.val.map (·.val) = offsets 0 ks)
    (hasc : ∀ lvl ∈ ks, lvl.Pairwise (fun a b => a.1 < b.1)) (h64 : ks.length < 64) :
    ∀ (m : Nat) (lvl : Usize) (paths : alloc.vec.Vec Digest), ks.length - lvl.val = m → lvl.val ≤ ks.length →
      paths.val.length + (ks.length - lvl.val) < Usize.max →
      ∃ b paths', merkle.push_path_loop known starts q paths lvl = .ok (b, paths') ∧
        match pathFrom (ks.drop lvl.val) (q.val / 2 ^ lvl.val) with
        | some p => b = true ∧ paths'.val = paths.val ++ p
        | none => b = false := by
  have hsl : starts.val.length = ks.length + 1 := by
    have := congrArg List.length hst; simpa [offsets_length] using this
  have hmax : Usize.max = 2 ^ 64 - 1 := by rw [Usize.max_def, Usize.numBits_def, hword]
  intro m
  induction m with
  | zero =>
    intro lvl paths hm hl hp
    have hend : lvl.val = ks.length := by omega
    refine ⟨true, paths, ?_, ?_⟩
    · unfold merkle.push_path_loop; apply loop_done
      have e1 : (Std.Usize.wrapping_add lvl 1#usize).val = lvl.val + 1 := add_val _ _ (by simp; omega)
      have hm1 : (lvl.val + 1) % Usize.size = lvl.val + 1 := by
        have := e1; rw [Std.Usize.wrapping_add_val_eq] at this; simpa using this
      have : ¬ (lvl.val + 1 < starts.val.length) := by omega
      simp [merkle.push_path_loop.body, lift, hm1, this]
    · rw [hend, List.drop_length]; simp [pathFrom]
  | succ m ih =>
    intro lvl paths hm hl hp
    have hlt : lvl.val < ks.length := by omega
    have e1 : (Std.Usize.wrapping_add lvl 1#usize).val = lvl.val + 1 := add_val _ _ (by simp; omega)
    have hm1 : (lvl.val + 1) % Usize.size = lvl.val + 1 := by
      have := e1; rw [Std.Usize.wrapping_add_val_eq] at this; simpa using this
    have hlt1 : lvl.val + 1 < starts.val.length := by omega
    -- the level's slice
    have hsa : (starts.val[lvl.val]'(by omega)).val = ((ks.take lvl.val).map List.length).sum := by
      have := congrArg (·[lvl.val]?) hst
      simp only [List.getElem?_map] at this
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by rw [offsets_length]; omega)] at this
      simp only [Option.map_some, Option.some.injEq] at this
      rw [this, offsets_get 0 ks lvl.val (by rw [offsets_length]; omega)]
      simp
    have hsb : (starts.val[lvl.val + 1]'(by omega)).val =
        ((ks.take lvl.val).map List.length).sum + ks[lvl.val].length := by
      have := congrArg (·[lvl.val + 1]?) hst
      simp only [List.getElem?_map] at this
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by rw [offsets_length]; omega)] at this
      simp only [Option.map_some, Option.some.injEq] at this
      rw [this, offsets_get 0 ks (lvl.val + 1) (by rw [offsets_length]; omega), Nat.zero_add,
        List.take_add_one, List.getElem?_eq_getElem hlt]
      simp only [List.map_append, List.sum_append, Option.toList_some, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero]
    have hkl : known.val.length = (ks.flatten).length := by
      have := congrArg List.length hk; simpa using this
    have hfl : ((ks.take lvl.val).map List.length).sum + ks[lvl.val].length ≤ ks.flatten.length := by
      have h1 := congrArg List.length (flatten_level ks lvl.val hlt)
      have h2 := List.length_take_le' ks[lvl.val].length (ks.flatten.drop ((ks.take lvl.val).map List.length).sum)
      rw [h1, List.length_drop] at h2
      have h3 : ((ks.take lvl.val).map List.length).sum ≤ ks.flatten.length := by
        conv_rhs => rw [← List.take_append_drop lvl.val ks]
        rw [List.flatten_append, List.length_append, List.length_flatten]; omega
      omega
    obtain ⟨t, ht, et⟩ := slice_range known (starts.val[lvl.val]'(by omega)) (starts.val[lvl.val + 1]'(by omega))
      (by rw [hsa, hsb]; omega) (by rw [hsb, hkl]; exact hfl)
    have ht' : t.val.map natNode = ks[lvl.val] := by
      rw [et, List.map_take, List.map_drop, hk, hsa, hsb, Nat.add_sub_cancel_left]
      exact flatten_level ks lvl.val hlt
    have htasc : t.val.Pairwise (fun a b => a.1.val < b.1.val) := by
      rw [← natNode_pairwise, ht']; exact hasc _ (List.getElem_mem hlt)
    -- the node and its sibling
    have hnode : (Std.Usize.wrapping_shr q lvl).val = q.val / 2 ^ lvl.val := shr_lvl hword q lvl (by omega)
    set node := Std.Usize.wrapping_shr q lvl with hnodedef
    obtain ⟨sib, hsib, esib⟩ : ∃ sib : Usize,
        (if (node &&& 1#usize) = 0#usize then Result.ok (Std.Usize.wrapping_add node 1#usize)
          else Result.ok (Std.Usize.wrapping_sub node 1#usize)) = .ok sib ∧ sib.val = sibOf node.val := by
      have hand := and_one node
      by_cases hev : node.val % 2 = 0
      · have h0 : (node &&& 1#usize) = 0#usize := by scalar_tac
        have hnm : node.val + 1 ≤ Usize.max := by
          have := usize_max_odd hword; have := usize_lt_size node
          simp only [UScalar.size] at this; scalar_tac
        exact ⟨Std.Usize.wrapping_add node 1#usize, by simp [h0],
          by rw [add_val _ _ (by simpa using hnm)]; simp [sibOf, hev]⟩
      · have h1 : (node &&& 1#usize) ≠ 0#usize := by intro h; have := congrArg UScalar.val h; simp_all
        exact ⟨Std.Usize.wrapping_sub node 1#usize, by simp [h1],
          by rw [sub_val _ _ (by simp; omega)]; simp [sibOf, hev]⟩
    have hdrop : ks.drop lvl.val = ks[lvl.val] :: ks.drop (lvl.val + 1) := List.drop_eq_getElem_cons hlt
    have hdiv : q.val / 2 ^ (lvl.val + 1) = q.val / 2 ^ lvl.val / 2 := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    obtain ⟨res, hnp, hres⟩ := node_position_eq t sib htasc
    have hstart : Slice.index_usize starts lvl = .ok (starts.val[lvl.val]'(by omega)) := slice_index _ _ (by omega)
    have hend : Slice.index_usize starts (Std.Usize.wrapping_add lvl 1#usize) =
        .ok (starts.val[lvl.val + 1]'(by omega)) := by
      rw [slice_index _ _ (by rw [e1]; omega)]; simp [e1]
    simp only [core.slice.index.Slice.index] at ht
    cases res with
    | none =>
      refine ⟨false, paths, ?_, ?_⟩
      · unfold merkle.push_path_loop; apply loop_done
        simp [merkle.push_path_loop.body, lift, hm1, hlt1, hstart, hend, ht, ← hnodedef, hsib, hnp]
      · rw [hdrop, pathFrom]
        have : lookup ks[lvl.val] (sibOf (q.val / 2 ^ lvl.val)) = none := by
          apply lookup_none
          rw [← ht', ← hnode, ← esib]
          intro hm; apply hres
          obtain ⟨y, hy, hye⟩ := List.mem_map.mp hm
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
          simp only [natNode] at hye
          exact List.mem_map.mpr ⟨x, hx, by scalar_tac⟩
        simp [this]
    | some pos =>
      obtain ⟨hpos, hpk⟩ := hres
      obtain ⟨⟨pi, pd⟩, hpd⟩ : ∃ x, t.val[pos.val] = x := ⟨_, rfl⟩
      have hix : Slice.index_usize t pos = .ok (pi, pd) := by rw [slice_index t pos hpos]; exact congrArg _ hpd
      obtain ⟨p1, hpush, ep1⟩ := push_ok paths pd (by omega)
      have hbody : merkle.push_path_loop.body known starts q paths lvl =
          .ok (.cont (p1, Std.Usize.wrapping_add lvl 1#usize)) := by
        simp [merkle.push_path_loop.body, lift, hm1, hlt1, hstart, hend, ht, ← hnodedef, hsib, hnp, hix, hpush]
      obtain ⟨b, paths', hrec, hout⟩ := ih (Std.Usize.wrapping_add lvl 1#usize) p1 (by rw [e1]; omega)
        (by rw [e1]; omega) (by rw [ep1, e1]; simp; omega)
      refine ⟨b, paths', by unfold merkle.push_path_loop; rw [loop_cont hbody]; exact hrec, ?_⟩
      have hlk : lookup ks[lvl.val] (sibOf (q.val / 2 ^ lvl.val)) = some pd := by
        have := lookup_of_getElem (t.val.map natNode) (by rw [natNode_pairwise]; exact htasc) pos.val
          (by simpa using hpos)
        simp only [List.getElem_map, natNode, hpd] at this
        rw [← ht', ← hnode, ← esib]
        have hpi : pi = sib := by rw [hpd] at hpk; exact hpk
        rw [hpi] at this; exact this
      rw [e1, hdiv] at hout
      rw [hdrop, pathFrom, hlk]
      cases hp : pathFrom (ks.drop (lvl.val + 1)) (q.val / 2 ^ lvl.val / 2) with
      | none => rw [hp] at hout; simpa using hout
      | some p =>
        rw [hp] at hout
        simp only [Option.map_some]
        exact ⟨hout.1, by rw [hout.2, ep1]; simp⟩

theorem push_path_eq (hword : UScalarTy.Usize.numBits = 64) (known : Slice (Usize × Digest))
    (starts : Slice Usize) (q : Usize) (ks : List (List (Nat × Digest)))
    (hk : known.val.map natNode = ks.flatten) (hst : starts.val.map (·.val) = offsets 0 ks)
    (hasc : ∀ lvl ∈ ks, lvl.Pairwise (fun a b => a.1 < b.1)) (h64 : ks.length < 64)
    (paths : alloc.vec.Vec Digest) (hp : paths.val.length + ks.length < Usize.max) :
    ∃ b paths', merkle.push_path known starts q paths = .ok (b, paths') ∧
      match pathFrom ks q.val with
      | some p => b = true ∧ paths'.val = paths.val ++ p
      | none => b = false := by
  obtain ⟨b, paths', h, hout⟩ := push_path_loop_eq hword known starts q ks hk hst hasc h64 _ 0#usize paths rfl
    (by simp) (by simpa using hp)
  exact ⟨b, paths', by simp [merkle.push_path, h], by simpa using hout⟩

/-! ## The expansion into openings -/

theorem position_eq (sorted : Slice Usize) (key : Usize)
    (hs : sorted.val.Pairwise (fun a b => a.val < b.val)) :
    ∃ res, merkle.position sorted key = .ok res ∧
      match res with
      | some m => ∃ hm : m.val < sorted.val.length, sorted.val[m.val] = key
      | none => key ∉ sorted.val := by
  have hl := sorted.property
  obtain ⟨res, h, hr⟩ := position_loop_eq sorted key hs _ 0#usize (Slice.len sorted) le_rfl (by simp)
    (by simp) (by intro j hj; simp at hj) (by intro j hj _; simp at *; omega)
  exact ⟨res, by simp [merkle.position, h], hr⟩

theorem idxOf_of_pairwise (l : List Nat) (hs : l.Pairwise (· < ·)) :
    ∀ (m : Nat) (hm : m < l.length), l.idxOf l[m] = m := by
  induction l with
  | nil => intro m hm; simp at hm
  | cons x rest ih =>
    rw [List.pairwise_cons] at hs
    intro m hm
    cases m with
    | zero => simp
    | succ m =>
      have hm' : m < rest.length := by simpa using hm
      have hx : x ≠ rest[m] := by have := hs.1 rest[m] (List.getElem_mem hm'); omega
      simp only [List.getElem_cons_succ, List.idxOf_cons, beq_iff_eq]
      rw [if_neg hx]; simp [ih hs.2 m hm']

/-- Query `q`'s leaf image: the zero prefix, then its row, the one stored at `q`'s place among
the distinct sorted queries. -/
def imageOf (rows : List U64) (sorted : List Nat) (rw lw q : Nat) : List U64 :=
  List.replicate (lw - rw) primitives.field.gf2_64.F64.ZERO ++ (rows.drop (sorted.idxOf q * rw)).take rw

/-- The expansion: each query's leaf image and path, in query order; nothing when a query is not
among the sorted ones or a path misses a sibling. -/
def expandSpec (rows : List U64) (sorted : List Nat) (ks : List (List (Nat × Digest))) (rw lw : Nat) :
    List Nat → Option (List U64 × List Digest)
  | [] => some ([], [])
  | q :: qs => if q ∈ sorted then
      match pathFrom ks q with
      | none => none
      | some p => (expandSpec rows sorted ks rw lw qs).map fun r => (imageOf rows sorted rw lw q ++ r.1, p ++ r.2)
    else none

/-- What `expand` returns after the images `D` and paths `P` written so far, against `expandSpec`. -/
def ExpandOut (lw height : Usize) (D : List U64) (P : List Digest) (res : Option merkle.Openings) :
    Option (List U64 × List Digest) → Prop
  | none => res = none
  | some (I, Ps) => ∃ o, res = some o ∧ o.leaf_words = lw ∧ o.height = height ∧
      o.images.val = D ++ I ∧ o.paths.val = P ++ Ps

theorem setSlice_mid {α : Type} (P row B C : List α) (hB : B.length = row.length) :
    (P ++ (B ++ C)).setSlice! P.length row = P ++ (row ++ C) := by
  simp only [List.setSlice!]
  have hn : min row.length ((P ++ (B ++ C)).length - P.length) = row.length := by
    simp only [List.length_append]; omega
  rw [hn, List.take_left, List.take_of_length_le (le_refl _), List.append_assoc]
  congr 2
  rw [← List.append_assoc, List.drop_left' (by simp [hB])]

theorem setSlice_zeros {α : Type} (D row : List α) (z : α) (pre R : Nat) (hR : pre + row.length ≤ R) :
    (D ++ List.replicate R z).setSlice! (D.length + pre) row =
      D ++ (List.replicate pre z ++ row) ++ List.replicate (R - pre - row.length) z := by
  have hsplit : List.replicate R z =
      List.replicate pre z ++ (List.replicate row.length z ++ List.replicate (R - pre - row.length) z) := by
    rw [← List.replicate_add, ← List.replicate_add]; congr 1; omega
  have := setSlice_mid (D ++ List.replicate pre z) row (List.replicate row.length z)
    (List.replicate (R - pre - row.length) z) (by simp)
  simp only [List.length_append, List.length_replicate, List.append_assoc] at this
  rw [hsplit, this]; simp

theorem vec_index_mut_range {α : Type} (v : alloc.vec.Vec α) (a b : Usize) (hab : a.val ≤ b.val)
    (hb : b.val ≤ v.val.length) :
    ∃ s back, alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice α) v { start := a, «end» := b } =
      .ok (s, back) ∧ s.val.length = b.val - a.val ∧ ∀ s2 : Slice α, (back s2).val = v.val.setSlice! a.val s2.val := by
  have h : a ≤ b ∧ b ≤ v.slice.length := ⟨by scalar_tac, by simpa [alloc.vec.Vec.val] using hb⟩
  simp only [alloc.vec.Vec.index_mut, core.slice.index.SliceIndexRangeUsizeSlice.index_mut, h, and_self,
    ↓reduceIte, bind_tc_ok]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · simp [List.slice, alloc.vec.Vec.val] at hb ⊢; omega
  · intro s2; simp [alloc.vec.Vec.val]

theorem copy_ok {α : Type} (c : core.marker.Copy α) (s src : Slice α) (h : s.val.length = src.val.length) :
    core.slice.Slice.copy_from_slice c s src = .ok src := by
  have : Slice.len s = Slice.len src := UScalar.eq_of_val_eq (by simp [h])
  simp [core.slice.Slice.copy_from_slice, this]

theorem pathFrom_length : ∀ (ks : List (List (Nat × Digest))) (n : Nat) (p : List Digest),
    pathFrom ks n = some p → p.length = ks.length
  | [], n, p, h => by simp [pathFrom] at h; subst h; rfl
  | lvl :: rest, n, p, h => by
    simp only [pathFrom] at h
    cases hl : lookup lvl (sibOf n) with
    | none => rw [hl] at h; cases h
    | some d =>
      rw [hl] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨p', hp', rfl⟩ := h
      simp [pathFrom_length rest (n / 2) p' hp']

theorem ExpandOut_cons {lw height : Usize} {D D' : List U64} {P P' : List Digest} {res o} (img : List U64)
    (p : List Digest) (hD : D' = D ++ img) (hP : P' = P ++ p) (h : ExpandOut lw height D' P' res o) :
    ExpandOut lw height D P res (o.map fun r => (img ++ r.1, p ++ r.2)) := by
  match o with
  | none => exact h
  | some (I, Ps) =>
    obtain ⟨x, h1, h2, h3, h4, h5⟩ := h
    exact ⟨x, h1, h2, h3, by rw [h4, hD]; simp, by rw [h5, hP]; simp⟩

theorem expand_loop_eq (hword : UScalarTy.Usize.numBits = 64) (rows : Slice U64) (sorted : Slice Usize)
    (known : Slice (Usize × Digest)) (starts : Slice Usize) (queries : Slice Usize) (rw lw height : Usize)
    (ks : List (List (Nat × Digest)))
    (hk : known.val.map natNode = ks.flatten) (hst : starts.val.map (·.val) = offsets 0 ks)
    (hasc : ∀ lvl ∈ ks, lvl.Pairwise (fun a b => a.1 < b.1)) (h64 : ks.length < 64)
    (hs : sorted.val.Pairwise (fun a b => a.val < b.val))
    (hrows : rows.val.length = sorted.val.length * rw.val) (hrl : rw.val ≤ lw.val)
    (hnl : queries.val.length * lw.val ≤ Usize.max)
    (hpl : queries.val.length * ks.length + ks.length < Usize.max) :
    ∀ (m : Nat) (k : Usize) (v : alloc.vec.Vec U64) (v1 : alloc.vec.Vec Digest) (D : List U64),
      queries.val.length - k.val = m → k.val ≤ queries.val.length →
      v.val = D ++ List.replicate ((queries.val.length - k.val) * lw.val) primitives.field.gf2_64.F64.ZERO →
      D.length = k.val * lw.val → v1.val.length ≤ k.val * ks.length →
      ∃ res, merkle.expand_loop rows sorted known starts queries rw lw lw height v v1 k = .ok res ∧
        ExpandOut lw height D v1.val res
          (expandSpec rows.val (sorted.val.map (·.val)) ks rw.val lw.val ((queries.val.drop k.val).map (·.val))) := by
  have hql := queries.property
  have hsl := sorted.property
  intro m
  induction m with
  | zero =>
    intro k v v1 D hm hk' hv hD hv1
    have hend : k.val = queries.val.length := by omega
    refine ⟨some { leaf_words := lw, height := height, images := v, paths := v1 }, ?_, ?_⟩
    · unfold merkle.expand_loop; apply loop_done
      have : ¬ (k < Slice.len queries) := by scalar_tac
      simp [merkle.expand_loop.body, this]
    · rw [hend, List.drop_length]
      exact ⟨_, rfl, rfl, rfl, by rw [hv, hend]; simp, by simp⟩
  | succ m ih =>
    intro k v v1 D hm hk' hv hD hv1
    have hlt : k.val < queries.val.length := by omega
    have hlt' : k < Slice.len queries := by scalar_tac
    obtain ⟨q, hqd⟩ : ∃ q, queries.val[k.val] = q := ⟨_, rfl⟩
    have hiq : Slice.index_usize queries k = .ok q := by rw [slice_index queries k hlt]; exact congrArg _ hqd
    have hdrop : (queries.val.drop k.val).map (·.val) = q.val :: (queries.val.drop (k.val + 1)).map (·.val) := by
      simp only [List.drop_eq_getElem_cons hlt, List.map_cons]
      exact congrArg (· :: _) (congrArg UScalar.val hqd)
    obtain ⟨res, hpos, hres⟩ := position_eq sorted q hs
    cases res with
    | none =>
      refine ⟨none, ?_, ?_⟩
      · unfold merkle.expand_loop; apply loop_done
        simp [merkle.expand_loop.body, hlt', hiq, hpos, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
      · rw [hdrop]
        have : q.val ∉ sorted.val.map (·.val) := by
          intro hm'; apply hres
          obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hm'
          have : x = q := by scalar_tac
          rw [← this]; exact hx
        simp [expandSpec, this, ExpandOut]
    | some slot =>
      obtain ⟨hslot, hsq⟩ := hres
      have hmem : q.val ∈ sorted.val.map (·.val) := List.mem_map.mpr ⟨_, List.getElem_mem hslot, by rw [hsq]⟩
      have hidx : (sorted.val.map (·.val)).idxOf q.val = slot.val := by
        have := idxOf_of_pairwise (sorted.val.map (·.val)) (by simpa [List.pairwise_map] using hs) slot.val
          (by simpa using hslot)
        simpa [hsq] using this
      -- arithmetic
      have hn := hnl
      have hkl : (k.val + 1) * lw.val ≤ queries.val.length * lw.val := Nat.mul_le_mul_right _ (by omega)
      have e1 : (Std.Usize.wrapping_add k 1#usize).val = k.val + 1 := add_val _ _ (by simp; omega)
      have eimg : (Std.Usize.wrapping_mul (Std.Usize.wrapping_add k 1#usize) lw).val = (k.val + 1) * lw.val := by
        rw [mul_val _ _ (by rw [e1]; omega), e1]
      have estart : (Std.Usize.wrapping_sub (Std.Usize.wrapping_mul (Std.Usize.wrapping_add k 1#usize) lw) rw).val =
          (k.val + 1) * lw.val - rw.val := by rw [sub_val _ _ (by rw [eimg]; nlinarith), eimg]
      have hvl : v.val.length = queries.val.length * lw.val := by
        rw [hv]; simp [hD]
        have : k.val * lw.val + (queries.val.length - k.val) * lw.val = queries.val.length * lw.val := by
          rw [← Nat.add_mul]; congr 1; omega
        omega
      obtain ⟨sv, back, hmut, hsvl, hback⟩ := vec_index_mut_range v
        (Std.Usize.wrapping_sub (Std.Usize.wrapping_mul (Std.Usize.wrapping_add k 1#usize) lw) rw)
        (Std.Usize.wrapping_mul (Std.Usize.wrapping_add k 1#usize) lw) (by rw [estart, eimg]; omega)
        (by rw [eimg, hvl]; exact hkl)
      rw [estart, eimg] at hsvl
      have hsr : slot.val + 1 ≤ sorted.val.length := hslot
      have hrw1 : (slot.val + 1) * rw.val ≤ rows.val.length := by rw [hrows]; exact Nat.mul_le_mul_right _ hsr
      have e3 : (Std.Usize.wrapping_mul slot rw).val = slot.val * rw.val := mul_val _ _ (by
        have : slot.val * rw.val ≤ (slot.val + 1) * rw.val := Nat.mul_le_mul_right _ (by omega)
        have := rows.property; omega)
      have e4 : (Std.Usize.wrapping_add slot 1#usize).val = slot.val + 1 := add_val _ _ (by simp; omega)
      have e5 : (Std.Usize.wrapping_mul (Std.Usize.wrapping_add slot 1#usize) rw).val = (slot.val + 1) * rw.val := by
        rw [mul_val _ _ (by rw [e4]; have := rows.property; omega), e4]
      obtain ⟨s1, hs1, es1⟩ := slice_range rows (Std.Usize.wrapping_mul slot rw)
        (Std.Usize.wrapping_mul (Std.Usize.wrapping_add slot 1#usize) rw) (by rw [e3, e5]; nlinarith)
        (by rw [e5]; exact hrw1)
      rw [e3, e5, show (slot.val + 1) * rw.val - slot.val * rw.val = rw.val by rw [Nat.add_mul]; omega] at es1
      have hs1l : s1.val.length = rw.val := by
        rw [es1]; simp; have : slot.val * rw.val + rw.val ≤ rows.val.length := by rw [← Nat.succ_mul]; exact hrw1
        omega
      have hcopy := copy_ok primitives.field.gf2_64.F64.Insts.CoreMarkerCopy sv s1 (by
        rw [hsvl, hs1l]; rw [Nat.add_mul]; omega)
      obtain ⟨b, v2, hpp, hpout⟩ := push_path_eq hword known starts q ks hk hst hasc h64 v1 (by
        have : k.val * ks.length + ks.length ≤ queries.val.length * ks.length + ks.length := by
          have := Nat.mul_le_mul_right ks.length (show k.val ≤ queries.val.length by omega); omega
        omega)
      simp only [core.slice.index.Slice.index] at hs1
      cases hpq : pathFrom ks q.val with
      | none =>
        rw [hpq] at hpout
        refine ⟨none, ?_, ?_⟩
        · unfold merkle.expand_loop; apply loop_done
          simp [merkle.expand_loop.body, hlt', hiq, hpos, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
            lift, hmut, hs1, hcopy, hpp, hpout]
        · rw [hdrop]; simp [expandSpec, hmem, hpq, ExpandOut]
      | some p =>
        rw [hpq] at hpout
        obtain ⟨hb, hv2⟩ := hpout
        have hpl' : p.length = ks.length := pathFrom_length ks q.val p hpq
        set img := imageOf rows.val (sorted.val.map (·.val)) rw.val lw.val q.val with himg
        have hback' : (back s1).val = (D ++ img) ++
            List.replicate ((queries.val.length - (k.val + 1)) * lw.val) primitives.field.gf2_64.F64.ZERO := by
          rw [hback, hv, estart]
          have hR : (lw.val - rw.val) + s1.val.length ≤ (queries.val.length - k.val) * lw.val := by
            rw [hs1l]
            have : lw.val ≤ (queries.val.length - k.val) * lw.val :=
              Nat.le_mul_of_pos_left _ (by omega)
            omega
          have hpos' : (k.val + 1) * lw.val - rw.val = D.length + (lw.val - rw.val) := by
            rw [hD, Nat.add_mul]; omega
          rw [hpos', setSlice_zeros D s1.val _ (lw.val - rw.val) _ hR, himg, imageOf, hidx, ← es1]
          congr 2
          rw [hs1l]
          have : (queries.val.length - k.val) * lw.val = (queries.val.length - (k.val + 1)) * lw.val + lw.val := by
            rw [← Nat.succ_mul]; congr 1; omega
          omega
        have hbody : merkle.expand_loop.body rows sorted known starts queries rw lw lw height v v1 k =
            .ok (.cont (back s1, v2, Std.Usize.wrapping_add k 1#usize)) := by
          simp [merkle.expand_loop.body, hlt', hiq, hpos, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
            lift, hmut, hs1, hcopy, hpp, hb]
        obtain ⟨res, hres, hout⟩ := ih (Std.Usize.wrapping_add k 1#usize) (back s1) v2 (D ++ img)
          (by rw [e1]; omega) (by rw [e1]; omega) (by rw [e1]; exact hback')
          (by
            have : slot.val * rw.val + rw.val ≤ rows.val.length := by rw [← Nat.succ_mul]; exact hrw1
            rw [List.length_append, hD, e1, himg, imageOf, hidx, List.length_append, List.length_replicate,
              List.length_take, List.length_drop, Nat.min_eq_left (by omega), Nat.add_mul]
            omega)
          (by rw [hv2, e1, List.length_append, hpl', Nat.add_mul]; omega)
        refine ⟨res, by unfold merkle.expand_loop; rw [loop_cont hbody]; exact hres, ?_⟩
        rw [hdrop, expandSpec, if_pos hmem, hpq]
        rw [e1] at hout
        exact ExpandOut_cons img p rfl hv2 hout

theorem vec_index_usize' {α : Type} (v : alloc.vec.Vec α) (i : Usize) (hi : i.val < v.val.length) :
    v.index_usize i = .ok v.val[i.val] := by
  simp [alloc.vec.Vec.index_usize, hi]

theorem list_clone_id {α : Type} (c : α → Result α) (hc : ∀ x, c x = .ok x) (l : List α) :
    List.clone c l = .ok ⟨l, rfl⟩ := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.clone, List.mapM_with_length] at ih ⊢
    simp only [ih, hc, bind_tc_ok]
    rfl

theorem expand_eq (hword : UScalarTy.Usize.numBits = 64) (rows : Slice U64) (sorted : Slice Usize)
    (known : Slice (Usize × Digest)) (starts : Slice Usize) (queries : Slice Usize) (rw lw : Usize)
    (ks : List (List (Nat × Digest)))
    (hk : known.val.map natNode = ks.flatten) (hst : starts.val.map (·.val) = offsets 0 ks)
    (hasc : ∀ lvl ∈ ks, lvl.Pairwise (fun a b => a.1 < b.1)) (h64 : ks.length < 64)
    (hs : sorted.val.Pairwise (fun a b => a.val < b.val))
    (hrows : rows.val.length = sorted.val.length * rw.val) (hrl : rw.val ≤ lw.val)
    (hnl : queries.val.length * lw.val ≤ Usize.max)
    (hpl : queries.val.length * ks.length + ks.length < Usize.max) :
    ∃ res, merkle.expand rows sorted known starts queries rw lw = .ok res ∧
      ExpandOut lw (Std.Usize.wrapping_sub (Slice.len starts) 1#usize) [] [] res
        (expandSpec rows.val (sorted.val.map (·.val)) ks rw.val lw.val (queries.val.map (·.val))) := by
  have hsl : starts.val.length = ks.length + 1 := by
    have := congrArg List.length hst; simpa [offsets_length] using this
  have em : (Std.Usize.wrapping_mul (Slice.len queries) lw).val = queries.val.length * lw.val :=
    mul_val _ _ (by simpa using hnl)
  have hfe : alloc.vec.from_elem primitives.field.gf2_64.F64.Insts.CoreCloneClone primitives.field.gf2_64.F64.ZERO
      (Std.Usize.wrapping_mul (Slice.len queries) lw) =
      .ok (alloc.vec.Vec.from (List.replicate (queries.val.length * lw.val) primitives.field.gf2_64.F64.ZERO)
        (by simp; omega)) := by
    simp only [alloc.vec.from_elem]
    rw [list_clone_id primitives.field.gf2_64.F64.Insts.CoreCloneClone.clone (fun x => rfl)]
    simp [em]
  obtain ⟨res, h, hout⟩ := expand_loop_eq hword rows sorted known starts queries rw lw
    (Std.Usize.wrapping_sub (Slice.len starts) 1#usize) ks hk hst hasc h64 hs hrows hrl hnl hpl _ 0#usize
    (alloc.vec.Vec.from (List.replicate (queries.val.length * lw.val) primitives.field.gf2_64.F64.ZERO)
        (by simp; omega)) (alloc.vec.Vec.with_capacity Digest (Std.Usize.wrapping_mul (Slice.len queries)
      (Std.Usize.wrapping_sub (Slice.len starts) 1#usize))) [] rfl (by simp) (by simp) (by simp)
    (by simp [alloc.vec.Vec.with_capacity])
  refine ⟨res, ?_, by simpa [alloc.vec.Vec.with_capacity] using hout⟩
  simp [merkle.expand, lift, hfe, h]

/-! ## The distinct sorted queries and the leaves -/

theorem sorted_unique_eq (hword : UScalarTy.Usize.numBits = 64) (queries : Slice Usize) :
    ∃ v, merkle.sorted_unique queries = .ok v ∧
      v.val.map (·.val) = (queries.val.map (·.val)).toFinset.sort (· ≤ ·) := by
  refine ⟨_, rfl, ?_⟩
  simp only [alloc.vec.Vec.from_val, List.map_map]
  conv_rhs => rw [← List.map_id ((queries.val.map (·.val)).toFinset.sort (· ≤ ·))]
  apply List.map_congr_left
  intro n hn
  rw [Finset.mem_sort, List.mem_toFinset] at hn
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hn
  have h2 : x.val < 2 ^ UScalarTy.Usize.numBits := by
    exact x.bv.isLt
  show (BitVec.ofNat UScalarTy.Usize.numBits x.val).toNat = x.val
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h2

theorem sort_strict (l : List Nat) : (l.toFinset.sort (· ≤ ·)).Pairwise (· < ·) :=
  ((Finset.pairwise_sort _ (· ≤ ·)).and (Finset.sort_nodup _ (· ≤ ·))).imp fun h => lt_of_le_of_ne h.1 h.2

theorem mem_sort_iff (l : List Nat) (q : Nat) : q ∈ l.toFinset.sort (· ≤ ·) ↔ q ∈ l := by
  rw [Finset.mem_sort, List.mem_toFinset]

theorem trailing_zeros_pow (h : Nat) (hh : h < 64) (x : Usize) (hx : x.val = 2 ^ h) :
    ∃ t, core.num.Usize.trailing_zeros x = .ok t ∧ t.val = h := by
  have hne : x.val ≠ 0 := by rw [hx]; positivity
  have hf : (List.range 64).find? (fun i => x.val.testBit i) = some h := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simp [hx, Nat.testBit_two_pow_self], h, by simp; omega, by simp, ?_⟩
    intro j hj
    simp [hx, Nat.testBit_two_pow]; omega
  refine ⟨_, rfl, ?_⟩
  simp only [hne, ↓reduceIte, hf, Option.getD_some]
  simp [UScalar.val]; omega

/-- Row `i`'s leaf image among rows of `rw` words one after another: `lw - rw` zero words, then the row. -/
def rowImage (rows : List U64) (rw lw i : Nat) : List U64 :=
  List.replicate (lw - rw) primitives.field.gf2_64.F64.ZERO ++ (rows.drop (i * rw)).take rw

theorem imageOf_eq (rows : List U64) (sorted : List Nat) (rw lw q : Nat) :
    imageOf rows sorted rw lw q = rowImage rows rw lw (sorted.idxOf q) := rfl

/-- The batched leaf hash's content contract: for `0 < rw ≤ lw` and exactly `n` rows of `rw`
words, digest `i` is `leaf` of row `i`'s leaf image. -/
def RowHash (leaf : List U64 → Digest) : Prop :=
  ∀ (rows : Slice U64) (n rw lw : Usize), 0 < rw.val → rw.val ≤ lw.val → rows.val.length = n.val * rw.val →
    ∃ r, merkle.hash_rows rows n rw lw = .ok r ∧
      r.val = (List.range n.val).map fun i => leaf (rowImage rows.val rw.val lw.val i)

/-- The leaves of the rebuild: each distinct sorted query with its row's leaf digest. -/
def leavesOf (leaf : List U64 → Digest) (rows : List U64) (sorted : List Nat) (rw lw : Nat) : List (Nat × Digest) :=
  sorted.zip ((List.range sorted.length).map fun i => leaf (rowImage rows rw lw i))

theorem open_loop_eq (sorted : alloc.vec.Vec Usize) (hashes : alloc.vec.Vec Digest)
    (hl : hashes.val.length = sorted.val.length) :
    ∀ (k : Nat) (i : Usize) (leaves : alloc.vec.Vec (Usize × Digest)), sorted.val.length - i.val = k →
      i.val ≤ sorted.val.length → leaves.val = (sorted.val.zip hashes.val).take i.val →
      ∃ out, merkle.PrunedMerklePaths.open_loop sorted hashes leaves i = .ok out ∧
        out.val = sorted.val.zip hashes.val := by
  have hsl := sorted.property
  intro k
  induction k with
  | zero =>
    intro i leaves hk hi hv
    refine ⟨leaves, ?_, by rw [hv, List.take_of_length_le (by simp; omega)]⟩
    unfold merkle.PrunedMerklePaths.open_loop; apply loop_done
    have : ¬ (i < alloc.vec.Vec.len sorted) := by scalar_tac
    simp [merkle.PrunedMerklePaths.open_loop.body, this]
  | succ k ih =>
    intro i leaves hk hi hv
    have hlt : i.val < sorted.val.length := by omega
    have ei : (Std.Usize.wrapping_add i 1#usize).val = i.val + 1 := add_val _ _ (by simp; omega)
    obtain ⟨l1, hpush, el1⟩ := push_ok leaves (sorted.val[i.val], hashes.val[i.val]'(by omega))
      (by rw [hv]; simp; omega)
    have hbody : merkle.PrunedMerklePaths.open_loop.body sorted hashes leaves i =
        .ok (.cont (l1, Std.Usize.wrapping_add i 1#usize)) := by
      have : i < alloc.vec.Vec.len sorted := by scalar_tac
      simp [merkle.PrunedMerklePaths.open_loop.body, this, vec_index sorted i hlt,
        vec_index hashes i (by omega), lift, hpush]
    unfold merkle.PrunedMerklePaths.open_loop
    rw [loop_cont hbody]
    refine ih _ _ (by rw [ei]; omega) (by rw [ei]; omega) ?_
    rw [el1, hv, ei, List.take_add_one]
    congr 1
    rw [List.getElem?_eq_getElem (by simp; omega)]
    simp

/-! ## The rebuild's invariants: ascending keys and present siblings -/

theorem mem_knownOf (ps : List (Nat × Digest × Digest)) (y : Nat × Digest) :
    y ∈ knownOf ps ↔ ∃ p ∈ ps, y = (2 * p.1, p.2.1) ∨ y = (2 * p.1 + 1, p.2.2) := by
  simp [knownOf, List.mem_flatMap]

theorem knownOf_pairwise : ∀ (ps : List (Nat × Digest × Digest)), ps.Pairwise (fun a b => a.1 < b.1) →
    (knownOf ps).Pairwise (fun a b => a.1 < b.1)
  | [], _ => by simp [knownOf]
  | p :: ps, h => by
    rw [List.pairwise_cons] at h
    have ih := knownOf_pairwise ps h.2
    have hk : knownOf (p :: ps) = (2 * p.1, p.2.1) :: (2 * p.1 + 1, p.2.2) :: knownOf ps := by
      simp [knownOf]
    rw [hk, List.pairwise_cons, List.pairwise_cons]
    refine ⟨?_, ?_, ih⟩
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · simp
      · obtain ⟨q, hq, hy⟩ := (mem_knownOf ps y).mp hy
        have := h.1 q hq
        rcases hy with rfl | rfl <;> simp <;> omega
    · intro y hy
      obtain ⟨q, hq, hy⟩ := (mem_knownOf ps y).mp hy
      have := h.1 q hq
      rcases hy with rfl | rfl <;> simp <;> omega

/-- One level of the rebuild on nodes ascending by index: the parents ascend, every node is a
known node of the level with its digest, every parent is the parent of a node and every node's
parent is a parent. -/
theorem pairSpec_struct (sibs : List Digest) :
    ∀ (n : Nat) (nodes : List (Nat × Digest)) (u : Nat) ps u', nodes.length ≤ n →
      pairSpec sibs nodes u = some (ps, u') → nodes.Pairwise (fun a b => a.1 < b.1) →
      ps.Pairwise (fun a b => a.1 < b.1) ∧ (∀ x ∈ nodes, x ∈ knownOf ps) ∧
      (∀ p ∈ ps, ∃ x ∈ nodes, x.1 / 2 = p.1) ∧ (∀ x ∈ nodes, ∃ p ∈ ps, p.1 = x.1 / 2) := by
  intro n
  induction n with
  | zero =>
    intro nodes u ps u' hl h _
    match nodes, hl with
    | [], _ => simp [pairSpec] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | succ n ih =>
    intro nodes u ps u' hl h hasc
    match nodes with
    | [] => simp [pairSpec] at h; obtain ⟨rfl, rfl⟩ := h; simp
    | [(i, h0)] =>
      cases hs : sibs[u]? with
      | none => simp [pairSpec, hs] at h
      | some d =>
        simp [pairSpec, hs] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by simp, ?_, by simp, by simp⟩
        intro x hx
        simp only [List.mem_singleton] at hx
        subst hx
        rw [mem_knownOf]
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        by_cases hev : i % 2 = 0
        · left; simp [side, hev]; omega
        · right; simp [side, hev]; omega
    | (i, h0) :: (j, h1) :: rest =>
      have hasc' := hasc
      rw [List.pairwise_cons] at hasc'
      have hij : i < j := hasc'.1 (j, h1) (by simp)
      have hrest : ∀ x ∈ rest, j < x.1 := by
        intro x hx
        exact (List.pairwise_cons.mp hasc'.2).1 x hx
      by_cases hp : i % 2 = 0 ∧ j = i + 1
      · simp only [pairSpec, hp, and_self, ↓reduceIte, Option.map_eq_some_iff] at h
        obtain ⟨⟨ps', u''⟩, hr, he⟩ := h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨a1, a2, a3, a4⟩ := ih rest u ps' u'' (by simp at hl; omega) hr
          (List.pairwise_cons.mp hasc'.2).2
        obtain ⟨hev, rfl⟩ := hp
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [List.pairwise_cons]
          refine ⟨fun p hp' => ?_, a1⟩
          obtain ⟨x, hx, hxe⟩ := a3 p hp'
          have := hrest x hx
          simp only at this ⊢; omega
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · rw [mem_knownOf]; exact ⟨_, List.mem_cons_self, Or.inl (by simp; omega)⟩
          · rw [mem_knownOf]; exact ⟨_, List.mem_cons_self, Or.inr (by simp; omega)⟩
          · rw [mem_knownOf]
            obtain ⟨p, hp', hpe⟩ := (mem_knownOf ps' x).mp (a2 x hx)
            exact ⟨p, List.mem_cons_of_mem _ hp', hpe⟩
        · intro p hp'
          simp only [List.mem_cons] at hp'
          rcases hp' with rfl | hp'
          · exact ⟨(i, h0), by simp, rfl⟩
          · obtain ⟨x, hx, hxe⟩ := a3 p hp'
            exact ⟨x, by simp [hx], hxe⟩
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · exact ⟨_, List.mem_cons_self, rfl⟩
          · exact ⟨_, List.mem_cons_self, by simp; omega⟩
          · obtain ⟨p, hp', hpe⟩ := a4 x hx
            exact ⟨p, List.mem_cons_of_mem _ hp', hpe⟩
      · cases hs : sibs[u]? with
        | none => simp [pairSpec, hp, hs] at h
        | some d =>
          simp only [pairSpec, hp, ↓reduceIte, hs, Option.map_eq_some_iff] at h
          obtain ⟨⟨ps', u''⟩, hr, he⟩ := h
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨a1, a2, a3, a4⟩ := ih ((j, h1) :: rest) (u + 1) ps' u'' (by simp at hl ⊢; omega) hr hasc'.2
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [List.pairwise_cons]
            refine ⟨fun p hp' => ?_, a1⟩
            obtain ⟨x, hx, hxe⟩ := a3 p hp'
            have hx' : j ≤ x.1 := by
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · exact le_refl _
              · exact (hrest x hx).le
            simp only at hxe ⊢
            by_cases hev : i % 2 = 0
            · have : j ≠ i + 1 := fun he => hp ⟨hev, he⟩
              omega
            · omega
          · intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · rw [mem_knownOf]
              refine ⟨_, List.mem_cons_self, ?_⟩
              by_cases hev : i % 2 = 0
              · left; simp [side, hev]; omega
              · right; simp [side, hev]; omega
            · rw [mem_knownOf]
              obtain ⟨p, hp', hpe⟩ := (mem_knownOf ps' x).mp (a2 x (by simp only [List.mem_cons] at hx ⊢; exact hx))
              exact ⟨p, List.mem_cons_of_mem _ hp', hpe⟩
          · intro p hp'
            simp only [List.mem_cons] at hp'
            rcases hp' with rfl | hp'
            · exact ⟨(i, h0), by simp, rfl⟩
            · obtain ⟨x, hx, hxe⟩ := a3 p hp'
              exact ⟨x, List.mem_cons_of_mem _ hx, hxe⟩
          · intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact ⟨_, List.mem_cons_self, rfl⟩
            · obtain ⟨p, hp', hpe⟩ := a4 x (by simp only [List.mem_cons]; exact hx)
              exact ⟨p, List.mem_cons_of_mem _ hp', hpe⟩

theorem lookup_isSome (l : List (Nat × Digest)) (i : Nat) (h : i ∈ l.map (·.1)) : (lookup l i).isSome := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  simp only [lookup, Option.isSome_map]
  exact List.find?_isSome.mpr ⟨x, hx, by simp⟩

theorem sibOf_mem (ps : List (Nat × Digest × Digest)) (n : Nat) (h : ∃ p ∈ ps, p.1 = n / 2) :
    sibOf n ∈ (knownOf ps).map (·.1) := by
  obtain ⟨p, hp, hpe⟩ := h
  rw [List.mem_map]
  by_cases hev : n % 2 = 0
  · exact ⟨(2 * p.1 + 1, p.2.2), (mem_knownOf ps _).mpr ⟨p, hp, Or.inr rfl⟩, by simp [sibOf, hev]; omega⟩
  · exact ⟨(2 * p.1, p.2.1), (mem_knownOf ps _).mpr ⟨p, hp, Or.inl rfl⟩, by simp [sibOf, hev]; omega⟩

/-- The rebuild from nodes ascending by index: one level of known nodes per height, each
ascending; every starting node's path finds its sibling at every level; the nodes left on top
ascend, and their indices are the starting ones' shifted by the height. -/
theorem rebuildSpec_struct (node : Digest → Digest → Digest) (sibs : List Digest) :
    ∀ (k : Nat) (nodes : List (Nat × Digest)) (u : Nat) lvls top u',
      rebuildSpec node sibs k nodes u = some (lvls, top, u') → nodes.Pairwise (fun a b => a.1 < b.1) →
      lvls.length = k ∧ (∀ l ∈ lvls, (knownOf l).Pairwise (fun a b => a.1 < b.1)) ∧
      (∀ x ∈ nodes, (pathFrom (lvls.map knownOf) x.1).isSome) ∧
      (∀ B, (∀ x ∈ nodes, x.1 < B * 2 ^ k) → ∀ x ∈ top, x.1 < B) ∧ top.Pairwise (fun a b => a.1 < b.1) := by
  intro k
  induction k with
  | zero =>
    intro nodes u lvls top u' h hasc
    simp only [rebuildSpec, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨rfl, by simp, by simp [pathFrom], fun B hB x hx => by simpa using hB x hx, hasc⟩
  | succ k ih =>
    intro nodes u lvls top u' h hasc
    simp only [rebuildSpec] at h
    cases hps : pairSpec sibs nodes u with
    | none => rw [hps] at h; cases h
    | some r =>
      obtain ⟨ps, u1⟩ := r
      rw [hps] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨lv, tp, uu⟩, hr, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      obtain ⟨a1, a2, a3, a4⟩ := pairSpec_struct sibs _ nodes u ps u1 le_rfl hps hasc
      have hasc' : (ps.map fun p => (p.1, node p.2.1 p.2.2)).Pairwise (fun a b => a.1 < b.1) := by
        rw [List.pairwise_map]; exact a1
      obtain ⟨b1, b2, b3, b4, b5⟩ := ih _ u1 lv tp uu hr hasc'
      refine ⟨by simp [b1], ?_, ?_, ?_, b5⟩
      · intro l hl
        simp only [List.mem_cons] at hl
        rcases hl with rfl | hl
        · exact knownOf_pairwise _ a1
        · exact b2 l hl
      · intro x hx
        simp only [List.map_cons, pathFrom]
        have hs := lookup_isSome _ _ (sibOf_mem ps x.1 (a4 x hx))
        obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hs
        rw [hd]
        obtain ⟨p, hp, hpe⟩ := a4 x hx
        have := b3 (p.1, node p.2.1 p.2.2) (List.mem_map_of_mem hp)
        simp only at this
        rw [hpe] at this
        simpa using this
      · intro B hB
        apply b4 B
        intro y hy
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
        obtain ⟨x, hx, hxe⟩ := a3 p hp
        have := hB x hx
        simp only
        rw [← hxe, pow_succ, ← Nat.mul_assoc] at *
        omega

/-- Top-down binding: if the pair hash is injective and the nodes left on top are the committed
tree's, every node the rebuild started from is the committed tree's. -/
theorem rebuildSpec_tree (node : Digest → Digest → Digest)
    (hinj : ∀ a b c d, node a b = node c d → a = c ∧ b = d) (T : Nat → Nat → Digest)
    (hT : ∀ l i, T (l + 1) i = node (T l (2 * i)) (T l (2 * i + 1))) (sibs : List Digest) :
    ∀ (k : Nat) (nodes : List (Nat × Digest)) (u : Nat) lvls top u' (l0 : Nat),
      rebuildSpec node sibs k nodes u = some (lvls, top, u') → nodes.Pairwise (fun a b => a.1 < b.1) →
      (∀ x ∈ top, x.2 = T (l0 + k) x.1) → ∀ x ∈ nodes, x.2 = T l0 x.1 := by
  intro k
  induction k with
  | zero =>
    intro nodes u lvls top u' l0 h _ htop
    simp only [rebuildSpec, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    simpa using htop
  | succ k ih =>
    intro nodes u lvls top u' l0 h hasc htop
    simp only [rebuildSpec] at h
    cases hps : pairSpec sibs nodes u with
    | none => rw [hps] at h; cases h
    | some r =>
      obtain ⟨ps, u1⟩ := r
      rw [hps] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨lv, tp, uu⟩, hr, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl, -⟩ := he
      obtain ⟨a1, a2, -, -⟩ := pairSpec_struct sibs _ nodes u ps u1 le_rfl hps hasc
      have hup := ih _ u1 lv tp uu (l0 + 1) hr (by rw [List.pairwise_map]; exact a1)
        (by intro x hx; rw [htop x hx]; congr 1; omega)
      intro x hx
      obtain ⟨p, hp, hpe⟩ := (mem_knownOf ps x).mp (a2 x hx)
      have hn := hup (p.1, node p.2.1 p.2.2) (List.mem_map_of_mem hp)
      simp only at hn
      rw [hT] at hn
      obtain ⟨e1, e2⟩ := hinj _ _ _ _ hn
      rcases hpe with rfl | rfl
      · exact e1
      · exact e2

/-! ## The opening -/

theorem expandSpec_some (rows : List U64) (sorted : List Nat) (ks : List (List (Nat × Digest))) (rw lw : Nat) :
    ∀ (qs : List Nat), (∀ q ∈ qs, q ∈ sorted ∧ (pathFrom ks q).isSome) →
      expandSpec rows sorted ks rw lw qs =
        some (qs.flatMap (imageOf rows sorted rw lw), qs.flatMap fun q => (pathFrom ks q).getD [])
  | [], _ => rfl
  | q :: qs, h => by
    obtain ⟨h1, h2⟩ := h q (by simp)
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h2
    rw [expandSpec, if_pos h1, hp, expandSpec_some rows sorted ks rw lw qs (fun q' hq' => h q' (by simp [hq']))]
    simp [hp]

instance (root : Digest) (nsibs : Nat) (top : List (Nat × Digest)) (u : Nat) :
    Decidable (Accepts root nsibs top u) := by
  unfold Accepts; infer_instance

/-- The opening's content, over a tree of `2 ^ h` leaves: nothing when there is no query, a row
is wider than its leaf image, a query is outside the tree, or the rows are not one per distinct
query; else the rebuild from the leaves, and when it uses every sibling and leaves `root` on top,
the expansion. -/
def openSpec (leaf : List U64 → Digest) (node : Digest → Digest → Digest) (rows : List U64)
    (sibs : List Digest) (root : Digest) (h : Nat) (queries : List Nat) (rw lw : Nat) :
    Option (List U64 × List Digest) :=
  let sorted := queries.toFinset.sort (· ≤ ·)
  if queries = [] ∨ lw < rw ∨ (∃ q ∈ queries, 2 ^ h ≤ q) ∨ rows.length ≠ sorted.length * rw then none
  else match rebuildSpec node sibs h (leavesOf leaf rows sorted rw lw) 0 with
    | none => none
    | some (lvls, top, u) =>
      if Accepts root sibs.length top u then expandSpec rows sorted (lvls.map knownOf) rw lw queries else none

/-- What `open` returns against `openSpec`'s images and paths. -/
def OpenOut (lw : Usize) (h : Nat) (res : Option merkle.Openings) : Option (List U64 × List Digest) → Prop
  | none => res = none
  | some (I, Ps) => ∃ o, res = some o ∧ o.leaf_words = lw ∧ o.height.val = h ∧ o.images.val = I ∧ o.paths.val = Ps

theorem last_ge_iff (S : List Nat) (hs : S.Pairwise (· < ·)) (hne : 0 < S.length) (B : Nat) :
    B ≤ S[S.length - 1] ↔ ∃ q ∈ S, B ≤ q := by
  constructor
  · intro hb; exact ⟨_, List.getElem_mem _, hb⟩
  · rintro ⟨q, hq, hb⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    by_cases hjl : j = S.length - 1
    · subst hjl; exact hb
    · have := List.pairwise_iff_getElem.mp hs j (S.length - 1) hj (by omega) (by omega)
      omega

theorem zip_natNode_val (l : List Usize) (r : List Digest) :
    (l.zip r).map natNode = (l.map (·.val)).zip r := by
  induction l generalizing r with
  | nil => simp
  | cons a l ih => cases r with
    | nil => simp
    | cons b r => simp [natNode, ih]

theorem startsOf_length (base : Nat) (lvls : List (List (Nat × Digest × Digest))) :
    (startsOf base lvls).length = lvls.length + 1 := by
  rw [startsOf_eq, offsets_length]; simp

theorem leavesOf_pairwise (leaf : List U64 → Digest) (rows : List U64) (S : List Nat) (rw lw : Nat)
    (hs : S.Pairwise (· < ·)) : (leavesOf leaf rows S rw lw).Pairwise (fun a b => a.1 < b.1) := by
  have : (leavesOf leaf rows S rw lw).map Prod.fst = S := List.map_fst_zip (by simp)
  rw [← List.pairwise_map, this]; exact hs

theorem mem_leavesOf (leaf : List U64 → Digest) (rows : List U64) (S : List Nat) (rw lw : Nat)
    (x : Nat × Digest) (hx : x ∈ leavesOf leaf rows S rw lw) : x.1 ∈ S := by
  have h1 : x.1 ∈ (leavesOf leaf rows S rw lw).map Prod.fst := List.mem_map_of_mem hx
  have h2 : (leavesOf leaf rows S rw lw).map Prod.fst = S := List.map_fst_zip (by simp)
  rwa [h2] at h1

/-- The generated `open` over a tree of `2 ^ h` leaves is `openSpec`, under the leaf and pair
hash content contracts, for nonempty rows and capacities that fit a word. -/
theorem open_eq (hword : UScalarTy.Usize.numBits = 64) {leaf : List U64 → Digest}
    {node : Digest → Digest → Digest} (hR : RowHash leaf) (hP : PairHash node) (p : merkle.PrunedMerklePaths)
    (root : Digest) (nl : Usize) (h : Nat) (hnl : nl.val = 2 ^ h) (hh : h < 62) (queries : Slice Usize)
    (rw lw : Usize) (hrw : 0 < rw.val) (hcap : 128 * (queries.val.length + 1) * (lw.val + 1) < Usize.max) :
    ∃ res, merkle.PrunedMerklePaths.open p root nl queries rw lw = .ok res ∧
      OpenOut lw h res (openSpec leaf node p.rows.val p.sibling_hashes.val root h
        (queries.val.map (·.val)) rw.val lw.val) := by
  have hmax : Usize.max = 2 ^ 64 - 1 := by rw [Usize.max_def, Usize.numBits_def, hword]
  have hql := queries.property
  have hpow : core.num.Usize.is_power_of_two nl = .ok true := by
    simp only [core.num.Usize.is_power_of_two, UScalar.is_power_of_two, hnl]
    simp [Nat.isPowerOfTwo]
  have hnz : ¬ nl = 0#usize := by
    intro he; have := congrArg UScalar.val he; rw [hnl] at this; simp at this
  by_cases hq : queries.val = []
  · refine ⟨none, ?_, ?_⟩
    · simp [merkle.PrunedMerklePaths.open, hpow, hnz, hq]
    · simp [openSpec, OpenOut, hq]
  have hemp : core.slice.Slice.is_empty queries = .ok false := by simp [core.slice.Slice.is_empty, hq]
  by_cases hlr : lw.val < rw.val
  · refine ⟨none, ?_, ?_⟩
    · have : rw > lw := by scalar_tac
      have h2 : ¬ rw.val ≤ lw.val := by omega
      simp [merkle.PrunedMerklePaths.open, hpow, hnz, hemp, this, hq, h2]
    · simp [openSpec, OpenOut, hlr]
  have hgt : ¬ (rw > lw) := by scalar_tac
  have hrwl : rw.val ≤ lw.val := by omega
  obtain ⟨t, ht, et⟩ := trailing_zeros_pow h (by omega) nl hnl
  have hcast : (UScalar.cast .Usize t).val = h := by
    rw [UScalar.cast_val_eq, et, hword]; exact Nat.mod_eq_of_lt (by
      calc h < 2 ^ h := Nat.lt_two_pow_self
        _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega))
  obtain ⟨v, hv, ev⟩ := sorted_unique_eq hword queries
  set S := (queries.val.map (·.val)).toFinset.sort (· ≤ ·) with hS
  have hSasc : S.Pairwise (· < ·) := sort_strict _
  have hmemS : ∀ q, q ∈ S ↔ q ∈ queries.val.map (·.val) := fun q => mem_sort_iff _ q
  have hvl : v.val.length = S.length := by rw [← ev]; simp
  have hSne : 0 < S.length := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hq
    exact List.length_pos_of_mem ((hmemS _).mpr (List.mem_map_of_mem hx))
  have hSq : S.length ≤ queries.val.length := by
    rw [hS, Finset.length_sort]; exact (List.toFinset_card_le _).trans (by simp)
  have hvl' : v.val.length ≤ Usize.max := v.property
  have hlast : ∀ (hc : v.val.length < 2 ^ UScalarTy.Usize.numBits),
      v.index_usize (Std.Usize.wrapping_sub (Usize.ofNatCore v.val.length hc) 1#usize) =
        .ok (v.val[S.length - 1]'(by omega)) := by
    intro hc
    have e1 : (Std.Usize.wrapping_sub (Usize.ofNatCore v.val.length hc) 1#usize).val = S.length - 1 := by
      rw [sub_val _ _ (by simp; omega)]; simp [hvl]
    rw [vec_index_usize' v _ (by rw [e1]; omega)]; simp [e1]
  have hlastv : (v.val[S.length - 1]'(by omega)).val = S[S.length - 1] := by
    have := List.getElem_of_eq ev (i := S.length - 1) (by simp; omega)
    simpa using this
  have hcapn : queries.val.length * lw.val ≤ Usize.max := by
    have : queries.val.length * lw.val ≤ 128 * (queries.val.length + 1) * (lw.val + 1) := by
      have := Nat.mul_le_mul (show queries.val.length ≤ 128 * (queries.val.length + 1) by omega)
        (show lw.val ≤ lw.val + 1 by omega)
      simpa [Nat.mul_assoc] using this
    omega
  have hcapS : S.length * rw.val ≤ Usize.max := by
    have := Nat.mul_le_mul hSq hrwl; omega
  have hcaph : ∀ k, k ≤ queries.val.length → 2 * k * (h + 1) < Usize.max := by
    intro k hk
    have h1 : 2 * k * (h + 1) ≤ 2 * (queries.val.length + 1) * 64 := Nat.mul_le_mul (by omega) (by omega)
    have h2 : 2 * (queries.val.length + 1) * 64 ≤ 128 * (queries.val.length + 1) * (lw.val + 1) := by
      have := Nat.mul_le_mul_left (128 * (queries.val.length + 1)) (show 1 ≤ lw.val + 1 by omega)
      rw [Nat.mul_one] at this
      have e : 2 * (queries.val.length + 1) * 64 = 128 * (queries.val.length + 1) := by ring
      omega
    omega
  have hmod : v.val.length * rw.val % Usize.size = v.val.length * rw.val :=
    Nat.mod_eq_of_lt (by have := usize_lt_size rw; simp only [UScalar.size] at *; rw [hvl]; scalar_tac)
  by_cases hout : ∃ q ∈ queries.val.map (·.val), 2 ^ h ≤ q
  · refine ⟨none, ?_, ?_⟩
    · have hle : nl.val ≤ (v.val[S.length - 1]'(by omega)).val := by
        rw [hnl, hlastv]
        obtain ⟨q, hq', hb⟩ := hout
        exact (last_ge_iff S hSasc hSne _).mpr ⟨q, (hmemS q).mpr hq', hb⟩
      simp [merkle.PrunedMerklePaths.open, hpow, hnz, hemp, hgt, hrwl, hq, ht, hv, lift, hlast, hle]
    · simp only [openSpec]; rw [if_pos (Or.inr (Or.inr (Or.inl hout)))]; rfl
  have hin : ∀ q ∈ S, q < 2 ^ h := by
    intro q hq'; by_contra hc; exact hout ⟨q, (hmemS q).mp hq', by omega⟩
  have hlt' : ¬ nl.val ≤ (v.val[S.length - 1]'(by omega)).val := by
    rw [hnl, hlastv]; have := hin (S[S.length - 1]'(by omega)) (List.getElem_mem _); omega
  by_cases hrl : p.rows.val.length ≠ S.length * rw.val
  · refine ⟨none, ?_, ?_⟩
    · have hne : ¬ p.rows.val.length = v.val.length * rw.val := by rw [hvl]; exact hrl
      simp [merkle.PrunedMerklePaths.open, hpow, hnz, hemp, hgt, hrwl, hq, ht, hv, lift, hlast, hlt', hmod, hne]
    · simp only [openSpec]; rw [if_pos (Or.inr (Or.inr (Or.inr hrl)))]; rfl
  have hrl' : p.rows.val.length = S.length * rw.val := by omega
  have hrl'' : p.rows.val.length = v.val.length * rw.val := by rw [hvl]; exact hrl'
  obtain ⟨r, hr, er⟩ := hR (alloc.vec.Vec.deref p.rows) (alloc.vec.Vec.len v) rw lw hrw hrwl
    (by simp [alloc.vec.Vec.deref, hrl''])
  have hrlen : r.val.length = v.val.length := by rw [er]; simp
  obtain ⟨leaves, hlv, elv⟩ := open_loop_eq v r hrlen _ 0#usize
    (alloc.vec.Vec.with_capacity (Usize × Digest) (alloc.vec.Vec.len v)) rfl (by simp)
    (by simp [alloc.vec.Vec.with_capacity])
  have hleaves : leaves.val.map natNode = leavesOf leaf p.rows.val S rw.val lw.val := by
    rw [elv, zip_natNode_val, ev, er]
    simp [leavesOf, hvl, alloc.vec.Vec.deref]
  have hidx : ∀ x ∈ leaves.val, x.1.val < 2 ^ 62 := by
    intro x hx
    have : natNode x ∈ leavesOf leaf p.rows.val S rw.val lw.val := by
      rw [← hleaves]; exact List.mem_map_of_mem hx
    have := hin _ (mem_leavesOf leaf p.rows.val S rw.val lw.val _ this)
    simp only [natNode] at this
    have : 2 ^ h ≤ 2 ^ 62 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hll : leaves.val.length = S.length := by rw [elv]; simp [hrlen, hvl]
  obtain ⟨res, hreb, hout'⟩ := rebuild_eq hword hP leaves (alloc.vec.Vec.deref p.sibling_hashes)
    (UScalar.cast .Usize t) root hidx (by rw [hll, hcast]; exact hcaph _ hSq) (by rw [hcast]; omega)
  rw [hcast, hleaves] at hout'
  have hcond : ¬ (queries.val.map (·.val) = [] ∨ lw.val < rw.val ∨ (∃ q ∈ queries.val.map (·.val), 2 ^ h ≤ q) ∨
      p.rows.val.length ≠ S.length * rw.val) := by
    simp only [List.map_eq_nil_iff, not_or]; exact ⟨hq, hlr, hout, by omega⟩
  have hspec : openSpec leaf node p.rows.val p.sibling_hashes.val root h (queries.val.map (·.val)) rw.val lw.val =
      match rebuildSpec node p.sibling_hashes.val h (leavesOf leaf p.rows.val S rw.val lw.val) 0 with
      | none => none
      | some (lvls, top, u) =>
        if Accepts root p.sibling_hashes.val.length top u then
          expandSpec p.rows.val S (lvls.map knownOf) rw.val lw.val (queries.val.map (·.val)) else none := by
    simp only [openSpec]; rw [if_neg hcond]
  rw [hspec]
  simp only [alloc.vec.Vec.deref, Slice.from_val] at hout'
  cases hrs : rebuildSpec node p.sibling_hashes.val h (leavesOf leaf p.rows.val S rw.val lw.val) 0 with
  | none =>
    rw [hrs] at hout'
    simp only [RebuildOut] at hout'
    subst hout'
    refine ⟨none, ?_, rfl⟩
    simp [merkle.PrunedMerklePaths.open, hpow, hnz, hemp, hgt, hrwl, hq, ht, hv, lift, hlast, hlt', hmod, hrl'',
      hr, hlv, hreb, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
  | some x =>
    obtain ⟨lvls, top, u⟩ := x
    rw [hrs] at hout'
    obtain ⟨hacc, hrej⟩ := hout'
    dsimp only
    by_cases ha : Accepts root p.sibling_hashes.val.length top u
    · obtain ⟨k', s', rfl, ek, es⟩ := hacc ha
      simp only [List.map_nil, List.nil_append, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.length_nil] at ek es
      obtain ⟨b1, b2, -, -, -⟩ := rebuildSpec_struct node p.sibling_hashes.val h _ 0 lvls top u hrs
        (leavesOf_pairwise leaf p.rows.val S rw.val lw.val hSasc)
      have hvasc : (alloc.vec.Vec.deref v).val.Pairwise (fun a b => a.val < b.val) := by
        simp only [alloc.vec.Vec.deref, Slice.from_val]
        rw [← List.pairwise_map (R := (· < ·)), ev]; exact hSasc
      have hn1 : 1 ≤ queries.val.length := by
        cases hqq : queries.val with
        | nil => exact absurd hqq hq
        | cons a l => simp
      obtain ⟨res2, hexp, hout2⟩ := expand_eq hword (alloc.vec.Vec.deref p.rows) (alloc.vec.Vec.deref v)
        (alloc.vec.Vec.deref k') (alloc.vec.Vec.deref s') queries rw lw (lvls.map knownOf)
        (by simp only [alloc.vec.Vec.deref, Slice.from_val]; rw [ek]; simp [List.flatMap_def])
        (by simp only [alloc.vec.Vec.deref, Slice.from_val]; rw [es, startsOf_eq])
        (by intro l hl; obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl; exact b2 l' hl')
        (by simp [b1]; omega) hvasc
        (by simp [alloc.vec.Vec.deref, hvl, hrl']) hrwl hcapn
        (by
          simp only [List.length_map, b1]
          have h1 : h ≤ queries.val.length * h := Nat.le_mul_of_pos_left h hn1
          have h2 : 2 * queries.val.length * h ≤ 2 * queries.val.length * (h + 1) :=
            Nat.mul_le_mul_left _ (by omega)
          have := hcaph queries.val.length le_rfl
          have e : 2 * queries.val.length * h = queries.val.length * h + queries.val.length * h := by ring
          omega)
      refine ⟨res2, ?_, ?_⟩
      · simp [merkle.PrunedMerklePaths.open, hpow, hnz, hemp, hgt, hrwl, hq, ht, hv, lift, hlast, hlt', hmod, hrl'',
          hr, hlv, hreb, core.option.Option.Insts.CoreOpsTry_traitTry.branch, hexp]
      · rw [if_pos ha]
        have hsl : (Std.Usize.wrapping_sub (Slice.len (alloc.vec.Vec.deref s')) 1#usize).val = h := by
          have hl := congrArg List.length es
          simp only [List.length_map, startsOf_length, b1] at hl
          have hl' : (Slice.len (alloc.vec.Vec.deref s')).val = h + 1 := by
            simp [alloc.vec.Vec.deref, Slice.len]; exact hl
          rw [sub_val _ _ (by rw [hl']; simp), hl']; simp
        have er1 : (alloc.vec.Vec.deref p.rows).val = p.rows.val := by simp [alloc.vec.Vec.deref]
        have er2 : (alloc.vec.Vec.deref v).val.map (·.val) = S := by simp [alloc.vec.Vec.deref, ev]
        rw [er1, er2] at hout2
        cases hx : expandSpec p.rows.val S (lvls.map knownOf) rw.val lw.val (queries.val.map (·.val)) with
        | none => rw [hx] at hout2; exact hout2
        | some y =>
          obtain ⟨I, Ps⟩ := y
          rw [hx] at hout2
          obtain ⟨o, h1, h2, h3, h4, h5⟩ := hout2
          exact ⟨o, h1, h2, by rw [h3, hsl], by simpa using h4, by simpa using h5⟩
    · rw [hrej ha] at hreb
      refine ⟨none, ?_, by rw [if_neg ha]; rfl⟩
      simp [merkle.PrunedMerklePaths.open, hpow, hnz, hemp, hgt, hrwl, hq, ht, hv, lift, hlast, hlt', hmod, hrl'',
        hr, hlv, hreb, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]

/-! ## Acceptance and binding -/

theorem expandSpec_images (rows : List U64) (sorted : List Nat) (ks : List (List (Nat × Digest))) (rw lw : Nat) :
    ∀ (qs : List Nat) I Ps, expandSpec rows sorted ks rw lw qs = some (I, Ps) →
      I = qs.flatMap (imageOf rows sorted rw lw)
  | [], I, Ps, h => by simp [expandSpec] at h; simp [h.1]
  | q :: qs, I, Ps, h => by
    simp only [expandSpec] at h
    split_ifs at h with hq
    cases hp : pathFrom ks q with
    | none => rw [hp] at h; cases h
    | some p =>
      rw [hp] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨I', Ps'⟩, h', he⟩ := h
      simp only [Prod.mk.injEq] at he
      rw [← he.1, expandSpec_images rows sorted ks rw lw qs I' Ps' h']
      simp

/-- Completeness of the opening: when the guards pass and the rebuild uses every sibling and
leaves `root` on top, `openSpec` returns every query's leaf image in query order. -/
theorem openSpec_accepts (leaf : List U64 → Digest) (node : Digest → Digest → Digest) (rows : List U64)
    (sibs : List Digest) (root : Digest) (h : Nat) (queries : List Nat) (rw lw : Nat)
    (hq : queries ≠ []) (hrl : rw ≤ lw) (hin : ∀ q ∈ queries, q < 2 ^ h)
    (hlen : rows.length = (queries.toFinset.sort (· ≤ ·)).length * rw) (lvls top u)
    (hreb : rebuildSpec node sibs h (leavesOf leaf rows (queries.toFinset.sort (· ≤ ·)) rw lw) 0 =
      some (lvls, top, u))
    (hacc : Accepts root sibs.length top u) :
    ∃ Ps, openSpec leaf node rows sibs root h queries rw lw =
      some (queries.flatMap (imageOf rows (queries.toFinset.sort (· ≤ ·)) rw lw), Ps) := by
  set S := queries.toFinset.sort (· ≤ ·) with hS
  have hcond : ¬ (queries = [] ∨ lw < rw ∨ (∃ q ∈ queries, 2 ^ h ≤ q) ∨ rows.length ≠ S.length * rw) := by
    simp only [not_or, not_exists, not_and, not_le]
    exact ⟨hq, by omega, fun q hq' => hin q hq', by omega⟩
  obtain ⟨-, -, b3, -, -⟩ := rebuildSpec_struct node sibs h _ 0 lvls top u hreb
    (leavesOf_pairwise leaf rows S rw lw (sort_strict _))
  have hpres : ∀ q ∈ queries, q ∈ S ∧ (pathFrom (lvls.map knownOf) q).isSome := by
    intro q hq'
    have hqS : q ∈ S := (mem_sort_iff _ q).mpr hq'
    refine ⟨hqS, ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hqS
    have hmem : (S[i], leaf (rowImage rows rw lw i)) ∈ leavesOf leaf rows S rw lw := by
      unfold leavesOf
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp; omega, by simp⟩
    exact b3 _ hmem
  refine ⟨queries.flatMap fun q => (pathFrom (lvls.map knownOf) q).getD [], ?_⟩
  simp only [openSpec]
  rw [if_neg hcond, hreb]
  dsimp only
  rw [if_pos hacc, expandSpec_some rows S (lvls.map knownOf) rw lw queries hpres]

/-- Binding, under an injective pair hash and an injective leaf hash: if the opening accepts
against the root of the committed tree `T` (leaf `i` hashing row `C i` after the zero prefix,
each parent the pair hash of its children), every query's leaf image is the committed row's. -/
theorem openSpec_binding (leaf : List U64 → Digest) (node : Digest → Digest → Digest)
    (hleaf : ∀ a b, leaf a = leaf b → a = b) (hnode : ∀ a b c d, node a b = node c d → a = c ∧ b = d)
    (rows : List U64) (sibs : List Digest) (h : Nat) (queries : List Nat) (rw lw : Nat)
    (C : Nat → List U64) (T : Nat → Nat → Digest)
    (hT0 : ∀ i, T 0 i = leaf (List.replicate (lw - rw) primitives.field.gf2_64.F64.ZERO ++ C i))
    (hT : ∀ l i, T (l + 1) i = node (T l (2 * i)) (T l (2 * i + 1))) (I Ps)
    (hopen : openSpec leaf node rows sibs (T h 0) h queries rw lw = some (I, Ps)) :
    ∀ q ∈ queries, imageOf rows (queries.toFinset.sort (· ≤ ·)) rw lw q =
      List.replicate (lw - rw) primitives.field.gf2_64.F64.ZERO ++ C q := by
  set S := queries.toFinset.sort (· ≤ ·) with hS
  simp only [openSpec] at hopen
  split_ifs at hopen with hcond
  simp only [not_or, not_exists, not_and, not_le] at hcond
  obtain ⟨hq, hrl, hin, hlen⟩ := hcond
  cases hreb : rebuildSpec node sibs h (leavesOf leaf rows S rw lw) 0 with
  | none => rw [hreb] at hopen; cases hopen
  | some x =>
    obtain ⟨lvls, top, u⟩ := x
    rw [hreb] at hopen
    dsimp only at hopen
    split_ifs at hopen with hacc
    have hasc := leavesOf_pairwise leaf rows S rw lw (sort_strict _)
    obtain ⟨-, -, -, b4, b5⟩ := rebuildSpec_struct node sibs h _ 0 lvls top u hreb hasc
    have hidx0 : ∀ x ∈ top, x.1 = 0 := by
      intro x hx
      have := b4 1 (by
        intro y hy
        have := hin y.1 ((mem_sort_iff _ _).mp (mem_leavesOf leaf rows S rw lw y hy))
        omega) x hx
      omega
    have htop : ∀ x ∈ top, x.2 = T (0 + h) x.1 := by
      obtain ⟨-, hroot⟩ := hacc
      cases top with
      | nil => simp at hroot
      | cons y ys =>
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hroot
        have hys : ys = [] := by
          cases ys with
          | nil => rfl
          | cons z zs =>
            have h1 := hidx0 y (by simp)
            have h2 := hidx0 z (by simp)
            have := (List.pairwise_cons.mp b5).1 z (by simp)
            omega
        subst hys
        intro x hx
        simp only [List.mem_singleton] at hx
        subst hx
        rw [hroot, hidx0 x (by simp), Nat.zero_add]
    have hleaves := rebuildSpec_tree node hnode T hT sibs h _ 0 lvls top u 0 hreb hasc htop
    intro q hq'
    have hqS : q ∈ S := (mem_sort_iff _ q).mpr hq'
    obtain ⟨i, hi, hqi⟩ := List.getElem_of_mem hqS
    have hmem : (S[i], leaf (rowImage rows rw lw i)) ∈ leavesOf leaf rows S rw lw := by
      unfold leavesOf
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp; omega, by simp⟩
    have := hleaves _ hmem
    simp only at this
    rw [hT0, hqi] at this
    have hidx : S.idxOf q = i := by rw [← hqi]; exact idxOf_of_pairwise S (sort_strict _) i hi
    rw [imageOf_eq, hidx]
    exact hleaf _ _ this

end WhirAeneas.Merkle
