module

public import LeanVM.Guest.Fast.WhirTablesCheck
public import LeanVM.Guest.B1.Whir.Names
public import LeanVM.Guest.Fast.LogG
public import LeanVM.Guest.Fast.Common
public import LeanVM.Guest.Fast.FunctionIdx
public import LeanVM.Guest.B1.VerifySub.Proof

/-!
# `verify_sub`'s child proof reader, computable

`vsPiOf rd σ V` (`B1/VerifySub/Proof.lean`) reads the child proof off `verify_sub`'s valuation,
the memory and the frame map `V : String → …`, through `open_stacked`'s template at the size `m`
and rate `r` (`osCfgR m (r - 1)`: `osQCalls`, `osWordsLen`) and classical exponent searches
(`dispatchIdx`, `rateOf`). `vsPiOfN rd σ Vn cl` reads the same words off the literal tables of
`Fast/WhirTables.lean`, the frames numbered (`Vn k = V (decoderFunctionName k)`,
`Fast/FunctionNames.lean`) and the cursor's length a parameter `cl` (`cursorLen`);
`vsPiOfN_eq`: they are equal; `openNames_eq`: `open_stacked`'s specializations are the functions
`openStackedIdx m`.

* `oqsOfN`: `opening_queries`' queries (`oqsOf`), its loop's frames numbered;
* `levelOsN`: a level's openings (`osLevelW`) from its `level_queries` dispatch in numbers
  (`OsCall`), read off the callee's frame and its `opening_queries` call's.

**Off arrays, consecutive cells incrementally.** `vsPiOfA T rd σ Vn cl` reads the same proof off
the tables `T` (`WhirTabs`: the lanes of `g^k`, the stream words and the calls of each candidate),
built once by the caller (`whirTabs`), and reads consecutive cells by stepping the address by `g`
(`wordsFrom`: `readN`, `wordsAt`), a query's windows once each, their exponents off the lanes
(`winLogsFrom`, `winPosOfW`: `winPosOf`, whose `gLog7` searches the powers of `g` per bit), each
query's position once (`oqQueryAt`),
each loop iteration's frame at `x·g^j` by stepping `x` (`oqItersFrom`), the loop's other
arguments once (`oqLoopArgs σ`, an argument), the selected candidate and its `open_stacked`
frame once (`vsPiOfM`, `vsPiOfAt`); `vsPiOfA_tabs`: at `whirTabs` it is `vsPiOfN`.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **The query hinted at `b`** (`oqQueryW`), its walk the frames `walk` of `Vn`. -/
def oqQueryN (s : Oq) (walk : ℕ) (rd : Reader) (bp cap flags : E) (b : ℕ) (emit : Bool) (σ : Val)
    (Vn : NFrames) : QW :=
  (winPosOf rd bp (s.pd + s.cd) s.cd, oqRow s b σ,
    oqSibsOf s.pd wpCh (winPosOf rd bp (s.pd + s.cd) s.cd)
      (Vn walk (oqWalkArgs s b emit bp cap flags σ) []))

/-- A loop iteration's queries, from its frame (`oqIterOf`), its walk the frames `walk` of `Vn`. -/
def oqIterN (s : Oq) (walk : ℕ) (rd : Reader) (σ : Val) (Vn : NFrames) : List QW :=
  if s.base = 1 then
    [oqQueryN s walk rd (σ (.n 15)) (σ (.n 4)) (σ (.n 5)) 16 true σ Vn,
      oqQueryN s walk rd (σ (.n (oqE1 s + 1))) (σ (.n 4)) (σ (.n 5)) (oqE1 s + 2) false σ Vn]
  else [oqQueryN s walk rd (σ (.n 13)) (σ (.n 4)) (σ (.n 5)) 14 true σ Vn]

/-- **The queries of `opening_queries`** from its frame `σ`, its loop and its walk the frames
`loop` and `walk` of `Vn` (`oqsOf`). -/
def oqsOfN (s : Oq) (odd loop walk N : ℕ) (rd : Reader) (σ : Val) (Vn : NFrames) : List QW :=
  (if odd = 1 then [oqQueryN s walk rd (σ (.n 12)) (σ (.n 0)) (σ (.n 1)) 13 true σ Vn] else []) ++
    (List.range N).flatMap fun j ↦ oqIterN s walk rd (Vn loop (gen ^ j :: oqLoopArgs σ) []) Vn

/-- The shape of the call `c`'s callee. -/
def OsCall.shape (c : OsCall) : OqShape := oqShapeAt c.sh

/-- **A level's openings** from its `level_queries` dispatch `c`, the caller's frame `σ`
(`osLevelW`): the `opening_queries` call's in the callee's frame `Vq`. -/
def levelOsN (rd : Reader) (σ : Val) (Vn : NFrames) (c : OsCall) : List Opening :=
  let A := c.args.map fun k ↦ σ (.n k)
  let Vq := Vn c.lq A (c.rets.map fun k ↦ σ (.n k))
  (oqsOfN c.shape.oq c.shape.odd c.loop c.walk c.N rd
    (Vn c.fn (osOqArgs Vq A c.N) [Vq (.n 13)]) Vn).map (toOpening rd (Vq (.n 7)) c.cd c.depth)

/-- **The child proof `verify_sub` checks** (`vsPiOf`), the frames numbered, `cl` the cursor's
length (`cursorLen`). -/
def vsPiOfN (rd : Reader) (σ : Val) (Vn : NFrames) (cl : E → E → ℕ) : Proof :=
  let m := logGT (σ (.n 278)) 11
  let j := logGT (σ (.n 66)) 4 * 11 + m
  let fr := Vn (openStackedIdx m) (vsOsArgs σ) (vsOsRets σ)
  ⟨wordsAt rd (σ (.n 25)) (cl (σ (.n 25)) (σ (.n 1919))) ++
      readN rd (fr (.n 9)) (osWordsTab.getD j 0),
    (osCallsTab.getD j []).map (levelOsN rd fr Vn)⟩

/-! ## Equal to the original -/

/-- `open_stacked`'s specializations are the functions `openStackedIdx m`. -/
theorem openNames_eq :
    openNames = (List.range 11).map fun m ↦ decoderFunctionName (openStackedIdx m) := by
  simp only [openNames, ← natStr_eq]
  decide +kernel

theorem gIdx_eq_logGT (N : ℕ) (hN : N ≤ 256) (x : E) : gIdx N x = logGT x N := by
  rw [← logG_eq_logGT _ hN]
  unfold gIdx logG
  congr 2

theorem dispatchIdx_eq_logGT (x : E) : dispatchIdx x = logGT x 11 :=
  gIdx_eq_logGT 11 (by norm_num) x

theorem rateOf_sub_one (x : E) : VerifySub.rateOf x - 1 = logGT x 4 := by
  unfold VerifySub.rateOf
  rw [gIdx_eq_logGT 4 (by norm_num) x, Nat.add_sub_cancel]

theorem map_vIdx {σ : Val} : ∀ {l : List V}, l.all isN = true →
    (l.map vIdx).map (fun k ↦ σ (.n k)) = l.map σ
  | [], _ => rfl
  | v :: l, h => by
      simp only [List.all_cons, Bool.and_eq_true, isN, beq_iff_eq] at h
      simp only [List.map_cons, vIdx, map_vIdx h.2, ← h.1]

theorem oqQueryN_eq (s : Oq) {walk : ℕ} (hw : decoderFunctionName walk = oqWalkOf s)
    (rd : Reader) (bp cap flags : E) (b : ℕ) (emit : Bool) (σ : Val) (Fm : FrameMap) :
    oqQueryN s walk rd bp cap flags b emit σ (fun k ↦ Fm (decoderFunctionName k)) =
      oqQueryW s rd bp cap flags b emit σ Fm := by
  simp only [oqQueryN, oqQueryW, hw]

theorem oqIterN_eq (s : Oq) {walk : ℕ} (hw : decoderFunctionName walk = oqWalkOf s)
    (rd : Reader) (σ : Val) (Fm : FrameMap) :
    oqIterN s walk rd σ (fun k ↦ Fm (decoderFunctionName k)) = oqIterOf s rd σ Fm := by
  simp only [oqIterN, oqIterOf, oqQueryN_eq s hw]

theorem oqsOfN_eq (s : Oq) {walk : ℕ} (hw : decoderFunctionName walk = oqWalkOf s)
    (odd loop N : ℕ) (rd : Reader) (σ : Val) (Fm : FrameMap) :
    oqsOfN s odd loop walk N rd σ (fun k ↦ Fm (decoderFunctionName k)) =
      oqsOf s odd (decoderFunctionName loop) N rd σ Fm := by
  simp only [oqsOfN, oqsOf, oqQueryN_eq s hw, oqIterN_eq s hw]

theorem levelOsN_eq (rd : Reader) (σ : Val) (Fm : FrameMap) {c : OsCfg} {r : OsCall}
    {q : ℕ × OsLv × List V × List V} (h : callMatch c r q = true) :
    levelOsN rd σ (fun k ↦ Fm (decoderFunctionName k)) r =
      osLevelW rd Fm c q.1 q.2.1 (q.2.2.1.map σ) (q.2.2.2.map σ) := by
  obtain ⟨lvl, lv, args, rets⟩ := q
  obtain ⟨sh, lq, fn, loop, walk, N, depth, cd, rargs, rrets⟩ := r
  simp only [callMatch, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs, hlq⟩, hn⟩, hl⟩, hw⟩, hN⟩, hdep⟩, hcd⟩, hra⟩, hrr⟩, ha⟩, hr⟩ := h
  subst hN hdep hcd hra hrr
  have hs' : oqShapeAt sh = oqShapeOf (osOqName c lvl lv) := eq_of_shapeBEq hs
  have hw' : decoderFunctionName walk = oqWalkOf (oqShapeAt sh).oq := by rw [hs', hw]
  dsimp only [levelOsN, osLevelW, OsCall.shape]
  rw [oqsOfN_eq _ hw']
  simp only [map_vIdx ha, map_vIdx hr, hn, hl, hlq, hs']

theorem map_zip_eq {α β γ : Type} {g : α → γ} {h : β → γ} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
      (∀ p ∈ l₁.zip l₂, g p.1 = h p.2) → l₁.map g = l₂.map h
  | [], [], _, _ => rfl
  | a :: l₁, b :: l₂, hl, hp => by
      simp only [List.map_cons]
      rw [hp (a, b) (by simp), map_zip_eq (by simpa using hl)
        (fun p hm ↦ hp p (List.mem_cons_of_mem _ hm))]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem vsPiOfN_eq (rd : Reader) (σ : Val) (Fm : FrameMap) :
    vsPiOfN rd σ (fun k ↦ Fm (decoderFunctionName k)) cursorLen = vsPiOf rd σ Fm := by
  have hm := logG_lt (σ (.n 278)) (bound := 11) (by norm_num)
  rw [logG_eq_logGT _ (by norm_num)] at hm
  have hr := logG_lt (σ (.n 66)) (bound := 4) (by norm_num)
  rw [logG_eq_logGT _ (by norm_num)] at hr
  unfold vsPiOfN vsPiOf piOfW vsOsW open_stacked_osW
  rw [dispatchIdx_eq_logGT, rateOf_sub_one]
  generalize logGT (σ (.n 278)) 11 = m at hm ⊢
  generalize logGT (σ (.n 66)) 4 = ri at hr ⊢
  have hj : ri * 11 + m < 44 := by omega
  have hjm : (ri * 11 + m) % 11 = m := by omega
  have hjr : (ri * 11 + m) / 11 = ri := by omega
  have hname : decoderFunctionName (openStackedIdx m) = openNames.getD m "" := by
    rw [openNames_eq, getD_map_range hm]
  obtain ⟨hlen, hok⟩ := callsOK _ hj
  unfold osQCalls osCfgAt at hlen hok
  rw [hjm, hjr] at hlen hok
  have hw : osWordsTab.getD (ri * 11 + m) 0 = osWordsLen (osCfgR m ri) := by
    rw [osWordsTab_eq, getD_map_range hj, osCfgAt, hjm, hjr]
  dsimp only
  rw [hname, hw, osLevelsW_eq, Proof.mk.injEq]
  refine ⟨rfl, ?_⟩
  exact map_zip_eq hlen fun p hp ↦ levelOsN_eq rd _ Fm (List.all_eq_true.mp hok p hp)

/-! ## Consecutive cells, incrementally -/

/-- **The `n` words from the address `a` on**, each address the last's times `g` (`0` where the
memory has none). -/
def wordsFrom (rd : Reader) : K → ℕ → List E
  | _, 0 => []
  | a, n + 1 => (rd a).getD 0 :: wordsFrom rd (a * Parameters.g) n

theorem wordsFrom_gpow (rd : Reader) (a : K) : ∀ n k, wordsFrom rd (a *
    Parameters.addressOfIndex k) n =
    (List.range' k n).map fun i ↦ (rd (a * Parameters.addressOfIndex i)).getD 0
  | 0, _ => rfl
  | n + 1, k => by
    rw [wordsFrom, List.range'_succ, List.map_cons,
      show a * Parameters.addressOfIndex k * Parameters.g = a * Parameters.addressOfIndex (k + 1) by
        show a * Parameters.g ^ k * Parameters.g = a * Parameters.g ^ (k + 1)
        rw [pow_succ, mul_assoc],
      wordsFrom_gpow rd a n (k + 1)]

theorem wordsFrom_eq (rd : Reader) (a : K) (n : ℕ) :
    wordsFrom rd a n = (List.range n).map fun i ↦ (rd (a * Parameters.addressOfIndex i)).getD
        0 := by
  have h := wordsFrom_gpow rd a n 0
  rw [show a * Parameters.addressOfIndex 0 = a
      by show a * Parameters.g ^ 0 = a; rw [pow_zero, mul_one]] at h
  rw [h, List.range_eq_range']

theorem readN_eq_wordsFrom (rd : Reader) (p : E) (n : ℕ) : readN rd p n = wordsFrom rd (p.limb 0) n := by
  rw [wordsFrom_eq]; rfl

theorem readN_eq_wordsAt (rd : Reader) (p : E) (n : ℕ) : readN rd p n = wordsAt rd p n := rfl

theorem wordsAt_eq_wordsFrom (rd : Reader) (p : E) (n : ℕ) :
    wordsAt rd p n = wordsFrom rd (p.limb 0) n := by
  rw [wordsFrom_eq]; rfl

/-! ## A query's position, its windows read once -/

/-- **The `n` windows' exponents from the address `a` on** (each below `128`, off the lanes
`lanes`: `logGTWith`), each address the last's times `g` (`0` where the memory has none). -/
def winLogsFrom (lanes : List ℕ) (rd : Reader) : K → ℕ → List ℕ
  | _, 0 => []
  | a, n + 1 => logGTWith lanes ((rd a).getD 0) 128 :: winLogsFrom lanes rd (a * Parameters.g) n

theorem winLogsFrom_eq_map (lanes : List ℕ) (rd : Reader) :
    ∀ (a : K) (n : ℕ), winLogsFrom lanes rd a n =
      (wordsFrom rd a n).map fun w ↦ logGTWith lanes w 128
  | _, 0 => rfl
  | a, n + 1 => by
    rw [winLogsFrom, wordsFrom, List.map_cons, winLogsFrom_eq_map lanes rd (a * Parameters.g) n]

/-- `gLog7` off the lanes. -/
theorem gLog7_eq_logGT (x : E) : gLog7 x = logGT x 128 := by
  rw [← logG_eq_logGT _ (by norm_num)]
  unfold gLog7 logG
  congr 2
  funext n
  rw [LeanVM.Guest.Value.gen_pow_eq_ofK]
  simp only [eq_comm]

/-- The windows' exponents, off `gLanes`, are `gLog7`'s. -/
theorem winLogsFrom_gLanes (rd : Reader) (bp : E) (n : ℕ) :
    winLogsFrom gLanes rd (bp.limb 0) n = (List.range n).map fun i ↦ gLog7 (memRead rd bp i) := by
  rw [winLogsFrom_eq_map, wordsFrom_eq, List.map_map]
  apply List.map_congr_left
  intro i _
  rw [Function.comp_apply, gLog7_eq_logGT, ← logGTWith_gLanes]
  rfl

/-- The number whose bits, low first, are `bs`. -/
def bitsB : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsB bs

theorem bitsB_append (l : List Bool) (b : Bool) :
    bitsB (l ++ [b]) = bitsB l + 2 ^ l.length * (if b then 1 else 0) := by
  induction l with
  | nil => simp [bitsB]
  | cons x l ih =>
    show (if x then 1 else 0) + 2 * bitsB (l ++ [b]) =
      ((if x then 1 else 0) + 2 * bitsB l) + 2 ^ (l.length + 1) * (if b then 1 else 0)
    rw [ih, pow_succ]
    ring

theorem bitsVal_eq_bitsB (f : ℕ → Bool) : ∀ n,
    LeanVM.Guest.Value.bitsVal f n = bitsB ((List.range n).map f)
  | 0 => rfl
  | n + 1 => by
    rw [LeanVM.Guest.Value.bitsVal, bitsVal_eq_bitsB f n, List.range_succ, List.map_append,
      List.map_singleton, bitsB_append, List.length_map, List.length_range]
    cases f n <;> rfl

/-- Bit `l` of a position of depth `d`, cap depth `cd`, from its windows' exponents `logs`
(`winPosOf`'s). -/
def winBit (logs : List ℕ) (d cd l : ℕ) : Bool :=
  (logs.getD (qwAt d cd l) 0).testBit (l - (qwWin d cd (qwAt d cd l)).1)

/-- The position of depth `d`, cap depth `cd`, its windows' exponents `logs` given. -/
def winPosAt (logs : List ℕ) (d cd : ℕ) : ℕ := bitsB ((List.range d).map (winBit logs d cd))

/-- **The position whose windows the run at `bp` holds** (`winPosOf`), its `qwN d cd` windows
read in a row, each's exponent once, off the lanes. -/
def winPosOfW (lanes : List ℕ) (rd : Reader) (bp : E) (d cd : ℕ) : ℕ :=
  winPosAt (winLogsFrom lanes rd (bp.limb 0) (qwN d cd)) d cd

/-- The window holding a bit is one of the position's. -/
theorem qwAt_lt_qwN (d cd l : ℕ) : qwAt d cd l < qwN d cd := by
  unfold qwAt qwN qwNp
  split_ifs <;> omega

theorem winPosOfW_eq (rd : Reader) (bp : E) (d cd : ℕ) :
    winPosOfW gLanes rd bp d cd = winPosOf rd bp d cd := by
  rw [winPosOfW, winPosAt, winPosOf, bitsVal_eq_bitsB, winLogsFrom_gLanes]
  congr 1
  apply List.map_congr_left
  intro l _
  rw [winBit, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (qwAt_lt_qwN d cd l)]
  rfl

/-! ## The queries, each position once, the loop's frames stepped -/

/-- The query hinted at `b`, its position `pos` given (`oqQueryN`). -/
def oqQueryAt (s : Oq) (walk : ℕ) (bp cap flags : E) (σ : Val) (Vn : NFrames) (b : ℕ)
    (emit : Bool) (pos : ℕ) : QW :=
  (pos, oqRow s b σ, oqSibsOf s.pd wpCh pos (Vn walk (oqWalkArgs s b emit bp cap flags σ) []))

/-- **The query hinted at `b`**, its position read once off its windows (`oqQueryN`). -/
def oqQueryA (s : Oq) (lanes : List ℕ) (walk : ℕ) (rd : Reader) (bp cap flags : E) (b : ℕ)
    (emit : Bool) (σ : Val) (Vn : NFrames) : QW :=
  oqQueryAt s walk bp cap flags σ Vn b emit (winPosOfW lanes rd bp (s.pd + s.cd) s.cd)

theorem oqQueryA_eq (s : Oq) (walk : ℕ) (rd : Reader) (bp cap flags : E) (b : ℕ) (emit : Bool)
    (σ : Val) (Vn : NFrames) :
    oqQueryA s gLanes walk rd bp cap flags b emit σ Vn =
      oqQueryN s walk rd bp cap flags b emit σ Vn := by
  rw [oqQueryA, oqQueryAt, oqQueryN, winPosOfW_eq]

/-- A loop iteration's queries, from its frame (`oqIterN`). -/
def oqIterA (s : Oq) (lanes : List ℕ) (walk : ℕ) (rd : Reader) (σ : Val) (Vn : NFrames) :
    List QW :=
  if s.base = 1 then
    [oqQueryA s lanes walk rd (σ (.n 15)) (σ (.n 4)) (σ (.n 5)) 16 true σ Vn,
      oqQueryA s lanes walk rd (σ (.n (oqE1 s + 1))) (σ (.n 4)) (σ (.n 5)) (oqE1 s + 2) false σ Vn]
  else [oqQueryA s lanes walk rd (σ (.n 13)) (σ (.n 4)) (σ (.n 5)) 14 true σ Vn]

theorem oqIterA_eq (s : Oq) (walk : ℕ) (rd : Reader) (σ : Val) (Vn : NFrames) :
    oqIterA s gLanes walk rd σ Vn = oqIterN s walk rd σ Vn := by
  simp only [oqIterA, oqIterN, oqQueryA_eq]

/-- **The loop's iterations from the frame at `x`**, `n` of them, the next at `x·g`: each the
queries of the frame of the loop's call `x :: la` (`la` the loop's other arguments). -/
def oqItersFrom (s : Oq) (lanes : List ℕ) (loop walk : ℕ) (rd : Reader) (Vn : NFrames)
    (la : List E) : ℕ → E → List QW
  | 0, _ => []
  | n + 1, x =>
    oqIterA s lanes walk rd (Vn loop (x :: la) []) Vn ++
      oqItersFrom s lanes loop walk rd Vn la n (x * gen)

theorem oqItersFrom_gen (s : Oq) (loop walk : ℕ) (rd : Reader) (Vn : NFrames) (la : List E) :
    ∀ n k, oqItersFrom s gLanes loop walk rd Vn la n (gen ^ k) =
      (List.range' k n).flatMap fun j ↦ oqIterN s walk rd (Vn loop (gen ^ j :: la) []) Vn
  | 0, _ => rfl
  | n + 1, k => by
    rw [oqItersFrom, ← pow_succ, oqItersFrom_gen s loop walk rd Vn la n (k + 1), List.range'_succ,
      List.flatMap_cons, oqIterA_eq]

/-- **`opening_queries`' queries** (`oqsOfN`): its loop's other arguments read once, each
iteration's frame at the next power of `g`, each query's position once. -/
def oqsOfA (s : Oq) (lanes : List ℕ) (odd loop walk N : ℕ) (rd : Reader) (σ : Val)
    (Vn : NFrames) : List QW :=
  (if odd = 1 then [oqQueryA s lanes walk rd (σ (.n 12)) (σ (.n 0)) (σ (.n 1)) 13 true σ Vn]
    else []) ++
    oqItersFrom s lanes loop walk rd Vn (oqLoopArgs σ) N 1

theorem oqsOfA_eq (s : Oq) (odd loop walk N : ℕ) (rd : Reader) (σ : Val) (Vn : NFrames) :
    oqsOfA s gLanes odd loop walk N rd σ Vn = oqsOfN s odd loop walk N rd σ Vn := by
  have h := oqItersFrom_gen s loop walk rd Vn (oqLoopArgs σ) N 0
  rw [pow_zero] at h
  unfold oqsOfA oqsOfN
  rw [h, oqQueryA_eq, List.range_eq_range']

/-- A level's openings, the frame `fr` of its `level_queries` callee and the `opening_queries`
call's argument words `a` given (`levelOsN`). -/
def levelOsAt (lanes : List ℕ) (rd : Reader) (fr : Val) (Vn : NFrames) (c : OsCall) (a : List E) :
    List Opening :=
  (oqsOfA c.shape.oq lanes c.shape.odd c.loop c.walk c.N rd
    (Vn c.fn a [fr (.n 13)]) Vn).map (toOpening rd (fr (.n 7)) c.cd c.depth)

/-- The `opening_queries` call's argument words (`osOqArgs`), `g^N` taken in `K`. -/
def oqCallArgs (fr : Val) (A : List E) (N : ℕ) : List E :=
  [fr (.n 7), fr (.n 9), A.getD 1 0, A.getD 2 0, A.getD 3 0, A.getD 4 0, A.getD 5 0,
    ofK (Parameters.g ^ N)]

theorem oqCallArgs_eq (fr : Val) (A : List E) (N : ℕ) : oqCallArgs fr A N = osOqArgs fr A N := by
  rw [oqCallArgs, osOqArgs, LeanVM.Guest.Value.gen_pow_eq_ofK]

/-- A level's openings, the `level_queries` dispatch's argument words `A` and the callee's frame
`fr` given: the `opening_queries` call's argument words read once. -/
def levelOsQ (lanes : List ℕ) (rd : Reader) (A : List E) (fr : Val) (Vn : NFrames) (c : OsCall) :
    List Opening :=
  levelOsAt lanes rd fr Vn c (oqCallArgs fr A c.N)

/-- A level's openings, the `level_queries` dispatch's argument words `A` given: its callee's frame
read once. -/
def levelOsF (lanes : List ℕ) (rd : Reader) (σ : Val) (Vn : NFrames) (c : OsCall) (A : List E) :
    List Opening :=
  levelOsQ lanes rd A (Vn c.lq A (c.rets.map fun k ↦ σ (.n k))) Vn c

/-- **A level's openings** (`levelOsN`), its dispatch's argument words read once. -/
def levelOsA (lanes : List ℕ) (rd : Reader) (σ : Val) (Vn : NFrames) (c : OsCall) :
    List Opening :=
  levelOsF lanes rd σ Vn c (c.args.map fun k ↦ σ (.n k))

theorem levelOsA_eq (rd : Reader) (σ : Val) (Vn : NFrames) (c : OsCall) :
    levelOsA gLanes rd σ Vn c = levelOsN rd σ Vn c := by
  rw [levelOsA, levelOsF, levelOsQ, levelOsAt, levelOsN, oqsOfA_eq, oqCallArgs_eq]

/-- `open_stacked`'s tables, as arrays: the lanes of `g^k` (`gLanes`), each size and rate's stream
words (`osWordsTab`) and `level_queries` dispatches (`osCallsTab`). -/
structure WhirTabs where
  lanes : List ℕ
  words : Array ℕ
  calls : Array (List OsCall)

/-- **`open_stacked`'s tables**, built from the literals. -/
def whirTabs : WhirTabs := ⟨gLanes, osWordsTab.toArray, osCallsTab.toArray⟩

/-- The child proof, the index `j` of its size and rate and the frame `fr` of its `open_stacked`
call given (`vsPiOfN`). -/
def vsPiOfAt (T : WhirTabs) (rd : Reader) (σ : Val) (Vn : NFrames) (cl : E → E → ℕ) (j : ℕ)
    (fr : Val) : Proof :=
  ⟨wordsFrom rd ((σ (.n 25)).limb 0) (cl (σ (.n 25)) (σ (.n 1919))) ++
      wordsFrom rd ((fr (.n 9)).limb 0) (T.words.getD j 0),
    (T.calls.getD j []).map (levelOsA T.lanes rd fr Vn)⟩

/-- The child proof, its size `m` and the index `j` of its size and rate given: the frame of
`open_stacked__L{m}`'s call read once. -/
def vsPiOfM (T : WhirTabs) (rd : Reader) (σ : Val) (Vn : NFrames) (cl : E → E → ℕ) (m j : ℕ) :
    Proof :=
  vsPiOfAt T rd σ Vn cl j (Vn (openStackedIdx m) (vsOsArgs σ) (vsOsRets σ))

/-- The child proof, its size `m` given. -/
def vsPiOfS (T : WhirTabs) (rd : Reader) (σ : Val) (Vn : NFrames) (cl : E → E → ℕ) (m : ℕ) :
    Proof :=
  vsPiOfM T rd σ Vn cl m (logGTWith T.lanes (σ (.n 66)) 4 * 11 + m)

/-- **The child proof `verify_sub` checks, off the tables `T`** (`vsPiOfN`). -/
def vsPiOfA (T : WhirTabs) (rd : Reader) (σ : Val) (Vn : NFrames) (cl : E → E → ℕ) : Proof :=
  vsPiOfS T rd σ Vn cl (logGTWith T.lanes (σ (.n 278)) 11)

/-- **Off the tables built, the reader is `vsPiOfN`.** -/
theorem vsPiOfA_tabs (rd : Reader) (σ : Val) (Vn : NFrames) (cl : E → E → ℕ) :
    vsPiOfA whirTabs rd σ Vn cl = vsPiOfN rd σ Vn cl := by
  have hl : levelOsA gLanes rd = levelOsN rd := funext fun σ ↦ funext fun Vn ↦ funext fun c ↦
    levelOsA_eq rd σ Vn c
  simp only [vsPiOfA, vsPiOfS, vsPiOfM, vsPiOfAt, vsPiOfN, whirTabs, logGTWith_gLanes,
    getD_toArray, hl, ← wordsAt_eq_wordsFrom, readN_eq_wordsAt]

end
end LeanVM.Guest.Fast
