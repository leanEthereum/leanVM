/-
  Rv64mc.Final.Image

  What the end theorem needs of a concrete image, each as a check the kernel evaluates. `Image.WF` (data words
  distinct, 8-aligned, apart from the input and from the code) makes `Loaded` satisfiable for every input that fits
  (`loaded_exists`). `WordsIn` (each function's words a slice of the image's code, at its address) makes
  machine-checked's functions the image's (`fnsIn_of_wordsIn`, `progOk_of_wordsIn`).
-/

import Rv64mc.Bridge

namespace Rv64mc

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter MachineChecked.RiscV.Lift

/-! ## `Loaded` is satisfiable -/

/-- The image's data can be loaded beside any input: data addresses distinct and 8-aligned, each word apart from
    the input's range and from the code. -/
def Image.WF (img : Image) : Prop :=
  (img.data.map (·.1)).Nodup ∧ ∀ p ∈ img.data, p.1.toNat % 8 = 0 ∧
    (p.1.toNat + 8 ≤ inputBase.toNat ∨ inputBase.toNat + 8 * inputCapacity ≤ p.1.toNat) ∧
    (p.1.toNat + 8 ≤ img.codeBase.toNat ∨ img.codeBase.toNat + 4 * img.code.length ≤ p.1.toNat)

/-- Strictly increasing. -/
def increasing : List Nat → Bool
  | a :: b :: l => decide (a < b) && increasing (b :: l)
  | _ => true

private theorem pairwise_of_increasing : ∀ {l : List Nat}, increasing l = true → l.Pairwise (· < ·)
  | [], _ => .nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [increasing, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_increasing h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

/-- `Image.WF` as one evaluation, linear in the data: the addresses increasing. -/
def Image.wfCheck (img : Image) : Bool :=
  increasing (img.data.map (·.1.toNat)) && img.data.all fun p => p.1.toNat % 8 = 0 &&
    (p.1.toNat + 8 ≤ inputBase.toNat || inputBase.toNat + 8 * inputCapacity ≤ p.1.toNat) &&
    (p.1.toNat + 8 ≤ img.codeBase.toNat || img.codeBase.toNat + 4 * img.code.length ≤ p.1.toNat)

theorem Image.wf_of_check {img : Image} (h : img.wfCheck = true) : img.WF := by
  simp only [Image.wfCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at h
  have hn : ((img.data.map (·.1)).map BitVec.toNat).Nodup := by
    rw [List.map_map]
    exact (pairwise_of_increasing h.1).imp Nat.ne_of_lt
  exact ⟨hn.of_map _, fun p hp => ⟨(h.2 p hp).1.1, (h.2 p hp).1.2, (h.2 p hp).2⟩⟩

private theorem find_of_nodup {l : List (Word × Word)} (hl : (l.map (·.1)).Nodup) {p : Word × Word} (hp : p ∈ l) :
    l.find? (fun q => q.1 == p.1) = some p := by
  induction l with
  | nil => cases hp
  | cons q l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hl
    rcases List.mem_cons.1 hp with rfl | hp
    · simp
    · have hne : q.1 ≠ p.1 := fun he => hl.1 ⟨p, hp, he.symm⟩
      simp [hne, ih hl.2 hp]

/-- **A well-formed image can be loaded with any input that fits.** -/
theorem loaded_exists {img : Image} (hwf : img.WF) (words : List Word) (hlen : words.length ≤ inputCapacity) :
    ∃ s, Loaded img words s := by
  let inInput (a : Word) : Prop :=
    inputBase.toNat ≤ a.toNat ∧ a.toNat < inputBase.toNat + 8 * words.length ∧ a.toNat % 8 = 0
  let mem (a : Word) : Word :=
    if h : inInput a then words[(a.toNat - inputBase.toNat) / 8]'(by
      simp only [inInput] at h; omega)
    else ((img.data.find? (fun q => q.1 == a)).map (·.2)).getD 0
  let s : MachineState :=
    { regs := fun r => if r = .x10 then BitVec.ofNat 64 words.length else 0, mem, code := img.codeAt,
      pc := img.entry }
  have hcap : inputCapacity = 2 ^ 25 := rfl
  have hbase : inputBase.toNat = 0x10000000 := rfl
  refine ⟨s, rfl, rfl, fun p hp => ?_, fun i hi => ?_, rfl, hlen⟩
  · obtain ⟨-, hin, -⟩ := hwf.2 p hp
    have hn : ¬ inInput p.1 := by simp only [inInput]; omega
    simp [MachineState.getMem, s, mem, hn, find_of_nodup hwf.1 hp]
  · have ha : (inputBase + BitVec.ofNat 64 (8 * i)).toNat = 0x10000000 + 8 * i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, hbase]; omega
    have hy : inInput (inputBase + BitVec.ofNat 64 (8 * i)) := by simp only [inInput]; omega
    simp only [MachineState.getMem, s, mem]
    split
    · congr 1
      rw [ha, hbase]; omega
    · contradiction

/-! ## machine-checked's functions are the image's -/

/-- `decompile --to lean`'s functions of a word list (`Gen.fns`'s definition). -/
def fnsOf (ws : List (String × Nat × List Nat)) : List Fn :=
  ws.map fun (name, base, w) =>
    { name, base := BitVec.ofNat 64 base, prog := ((w.map (BitVec.ofNat 32)).mapM decode).getD [] }

/-- Each function's words are the image's code at its address, aligned and below `2^64`. -/
def WordsIn (img : Image) (ws : List (String × Nat × List Nat)) : Prop :=
  img.codeBase.toNat % 4 = 0 ∧ ∀ e ∈ ws, img.codeBase.toNat ≤ e.2.1 ∧ e.2.1 % 4 = 0 ∧
    e.2.1 + 4 * e.2.2.length < 2 ^ 64 ∧
    (img.code.drop ((e.2.1 - img.codeBase.toNat) / 4)).take e.2.2.length = e.2.2.map (BitVec.ofNat 32)

/-- The functions' words, in order, are the code from `addr` on, each function at its address. -/
def contig (code : List (BitVec 32)) (addr : Nat) : List (String × Nat × List Nat) → Bool
  | [] => true
  | (_, b, w) :: rest => b == addr && ((code.take w.length).map BitVec.toNat == w) &&
      contig (code.drop w.length) (addr + 4 * w.length) rest

private theorem contig_spec : ∀ {ws : List (String × Nat × List Nat)} {code : List (BitVec 32)} {addr : Nat},
    contig code addr ws = true → ∀ e ∈ ws, ∃ k, e.2.1 = addr + 4 * k ∧ k + e.2.2.length ≤ code.length ∧
      (code.drop k).take e.2.2.length = e.2.2.map (BitVec.ofNat 32)
  | [], _, _, _, e, he => by cases he
  | (n, b, w) :: rest, code, addr, h, e, he => by
    simp only [contig, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, hp⟩, hr⟩ := h
    have hlen : w.length ≤ code.length := by
      have := congrArg List.length hp; simp only [List.length_map, List.length_take] at this; omega
    have hslice : code.take w.length = w.map (BitVec.ofNat 32) := by
      have hid : (code.take w.length).map (BitVec.ofNat 32 ∘ BitVec.toNat) = code.take w.length := by
        simp [Function.comp_def]
      rw [← hid, ← List.map_map, hp]
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨0, by simp, by simpa using hlen, by simpa using hslice⟩
    · obtain ⟨k, hk, hkl, hks⟩ := contig_spec hr e he
      refine ⟨w.length + k, by omega, by simp only [List.length_drop] at hkl; omega, ?_⟩
      rw [← hks, List.drop_drop]

/-- `WordsIn` as one evaluation, linear in the code. -/
def wordsInCheck (img : Image) (ws : List (String × Nat × List Nat)) : Bool :=
  img.codeBase.toNat % 4 == 0 && decide (img.codeBase.toNat + 4 * img.code.length < 2 ^ 64) &&
    contig img.code img.codeBase.toNat ws

theorem wordsIn_of_check {img : Image} {ws : List (String × Nat × List Nat)} (h : wordsInCheck img ws = true) :
    WordsIn img ws := by
  simp only [wordsInCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h4, hlt⟩, hc⟩ := h
  refine ⟨h4, fun e he => ?_⟩
  obtain ⟨k, hk, hkl, hks⟩ := contig_spec hc e he
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [show (e.2.1 - img.codeBase.toNat) / 4 = k by omega]
  exact hks

private theorem mapM_some {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      ys.length = xs.length ∧ ∀ i (h1 : i < xs.length) (h2 : i < ys.length), f xs[i] = some ys[i]
  | [], ys, h => by simp at h; subst h; simp
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨y, hy, ys', hys, rfl⟩ := h
    obtain ⟨hl, hi⟩ := mapM_some hys
    refine ⟨by simp [hl], fun i h1 h2 => ?_⟩
    cases i with
    | zero => simpa using hy
    | succ i => simpa using hi i (by simpa using h1) (by simpa using h2)

/-- **machine-checked's functions are the image's**, when their words are. -/
theorem fnsIn_of_wordsIn {img : Image} {ws : List (String × Nat × List Nat)} (h : WordsIn img ws) :
    FnsIn img (fnsOf ws) := by
  intro f hf i hi
  obtain ⟨⟨name, b, w⟩, he, rfl⟩ := List.mem_map.1 hf
  obtain ⟨hle, hb4, hlt, hsl⟩ := h.2 _ he
  simp only at hle hb4 hlt hsl hi ⊢
  obtain ⟨l, hm⟩ : ∃ l, (w.map (BitVec.ofNat 32)).mapM decode = some l := by
    cases h' : (w.map (BitVec.ofNat 32)).mapM decode with
    | none => simp [h'] at hi
    | some l => exact ⟨l, rfl⟩
  have hprog : ((w.map (BitVec.ofNat 32)).mapM decode).getD [] = l := by simp [hm]
  simp only [hprog] at hi ⊢
  obtain ⟨hl, hdec⟩ := mapM_some hm
  have hiw : i < w.length := by simpa [hl] using hi
  have hpc : (BitVec.ofNat 64 b + BitVec.ofNat 64 (4 * i)).toNat = b + 4 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hidx : (b + 4 * i - img.codeBase.toNat) / 4 = (b - img.codeBase.toNat) / 4 + i := by omega
  have hcode : img.code[(b - img.codeBase.toNat) / 4 + i]? = some (BitVec.ofNat 32 w[i]) := by
    have := congrArg (·[i]?) hsl
    simp only [List.getElem?_take, List.getElem?_drop, List.getElem?_map, hiw, ↓reduceIte] at this
    simpa [List.getElem?_eq_getElem hiw] using this
  have := hdec i (by simpa using hiw) hi
  simp only [List.getElem_map] at this
  have hcb := h.1
  simp only [Image.codeAt, hpc, hidx, hcode, Option.bind_some, this]
  split
  · rfl
  · rename_i hn; exact absurd ⟨by omega, by omega⟩ hn

/-- machine-checked's functions start at aligned addresses, when their words are the image's. -/
theorem progOk_of_wordsIn {img : Image} {ws : List (String × Nat × List Nat)} (h : WordsIn img ws) :
    ProgOk (fnsOf ws) := by
  intro f hf
  obtain ⟨⟨name, b, w⟩, he, rfl⟩ := List.mem_map.1 hf
  obtain ⟨-, hb4, hlt, -⟩ := h.2 _ he
  simp only at hb4 hlt ⊢
  rw [BitVec.toNat_ofNat]; omega

/-- `AllDecode` as one evaluation. -/
theorem allDecode_of_all {img : Image} (h : (img.code.all fun w => Runnable (decode w)) = true) : AllDecode img :=
  fun w hw => List.all_eq_true.1 h w hw

end Rv64mc
