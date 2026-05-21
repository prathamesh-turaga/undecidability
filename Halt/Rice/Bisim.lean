/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Halt.Rice.Extender

@[expose] public section

/-!
# Rice extender bisimulation — phase lemmas

Working toward discharging `semHalt_riceConstTM_dichotomy` (postulated
in `Halt.Rice.Theorem`). The behaviour of `riceConstTM c` on an input
`w` runs in four phases (see `Halt.Rice.Extender`):

1. **erase** — scan right writing blanks until the first blank.
2. **write** — write `encodeTMCode c` left-to-right.
3. **move-back** — return the head to the start of `encodeTMCode c`.
4. **simulate** — run `c.toTM`.

This file proves the phases as standalone lemmas. The headline
dichotomy theorem then composes them.

## Phase 1: erase

The key observation is that cslib's `BiTape`/`StackTape` *trims*
trailing blanks: `StackTape.cons none ∅ = ∅`. So when the erase phase
writes a blank over the head symbol and moves right, the just-blanked
cell is trimmed away — `mk₁ (a :: rest)` steps directly to `mk₁ rest`.
Consequently the erase phase drives `⟨erase, mk₁ w⟩` to
`⟨writeBit 0, ∅⟩` for **every** `w`, so the post-erase configuration is
input-independent. This is what makes `SemHalt (riceConstTM c)` either
`univ` or `∅`.
-/

namespace Halt.Rice

open Turing PCP Relation

variable (c : Halt.TMCode)

/-! ### `BiTape` erase step -/

/-- Writing a blank over the head of `mk₁ (a :: rest)` and moving right
yields `mk₁ rest`: the blanked cell is trimmed by `StackTape.cons`. -/
lemma biTape_writeNone_moveRight_mk₁_cons (a : Bool) (rest : List Bool) :
    ((BiTape.mk₁ (a :: rest)).write none).optionMove (some Dir.right) =
      BiTape.mk₁ rest := by
  cases rest with
  | nil => rfl
  | cons b rest' => rfl

/-! ### Erase-phase single steps -/

/-- An erase step over a non-empty tape: `⟨erase, mk₁ (a :: rest)⟩`
transitions to `⟨erase, mk₁ rest⟩`. -/
lemma erase_step_cons (a : Bool) (rest : List Bool) :
    (riceConstTM c).step ⟨some RiceState.erase, BiTape.mk₁ (a :: rest)⟩ =
      some ⟨some RiceState.erase, BiTape.mk₁ rest⟩ := by
  show (riceConstTM c).step ⟨some RiceState.erase, BiTape.mk₁ (a :: rest)⟩ = _
  have h_head : (BiTape.mk₁ (a :: rest)).head = some a := rfl
  simp only [SingleTapeTM.step, riceConstTM, riceTr, h_head]
  rw [biTape_writeNone_moveRight_mk₁_cons]

/-- An erase step over the empty tape: `⟨erase, ∅⟩` transitions to the
write phase `⟨writeBit 0, ∅⟩`. -/
lemma erase_step_nil :
    (riceConstTM c).step ⟨some RiceState.erase, BiTape.nil⟩ =
      some ⟨some (RiceState.writeBit ⟨0, encodedLen_pos c⟩), BiTape.nil⟩ := by
  rfl

/-! ### Phase 1 lemma -/

/-- **Erase phase.** From the initial configuration `⟨erase, mk₁ w⟩`,
`riceConstTM c` reaches `⟨writeBit 0, ∅⟩` — the start of the write
phase — for *every* input `w`. -/
theorem erase_phase (w : List Bool) :
    ReflTransGen (riceConstTM c).TransitionRelation
      ⟨some RiceState.erase, BiTape.mk₁ w⟩
      ⟨some (RiceState.writeBit ⟨0, encodedLen_pos c⟩), BiTape.nil⟩ := by
  induction w with
  | nil =>
    exact ReflTransGen.single (erase_step_nil c)
  | cons a rest ih =>
    refine ReflTransGen.head ?_ ih
    exact erase_step_cons c a rest

/-! ## Phase 2: write

The write phase lays `encodeTMCode c` onto the tape one bit at a time,
moving right after each write. After `k` bits the tape is `writtenTape
c k`: head blank, the first `k` bits sit *reversed* on the left stack
(`map_some` — all `some`, so no trimming), right stack empty. -/

/-- `StackTape.map_some` of a cons is a `cons` of `map_some`. -/
lemma map_some_cons (x : Bool) (xs : List Bool) :
    StackTape.map_some (x :: xs) =
      StackTape.cons (some x) (StackTape.map_some xs) := rfl

/-- The tape after the write phase has placed the first `k` bits of
`encodeTMCode c`. -/
def writtenTape (c : Halt.TMCode) (k : ℕ) : BiTape Bool :=
  ⟨none, StackTape.map_some ((Halt.Encoding.encodeTMCode c).take k).reverse, ∅⟩

lemma writtenTape_zero : writtenTape c 0 = BiTape.nil := rfl

/-- Writing bit `k` over the (blank) head of `writtenTape c k` and
moving right yields `writtenTape c (k+1)`. -/
lemma writtenTape_step (k : ℕ) (hk : k < encodedLen c) :
    ((writtenTape c k).write (some (encodedBit c ⟨k, hk⟩))).optionMove
        (some Dir.right) =
      writtenTape c (k + 1) := by
  have h_len : k < (Halt.Encoding.encodeTMCode c).length := hk
  have h_take : (Halt.Encoding.encodeTMCode c).take (k + 1) =
      (Halt.Encoding.encodeTMCode c).take k ++
        [(Halt.Encoding.encodeTMCode c).get ⟨k, h_len⟩] := by
    rw [List.take_add_one]
    congr 1
    rw [List.getElem?_eq_getElem h_len]
    rfl
  show (⟨some (encodedBit c ⟨k, hk⟩),
          StackTape.map_some ((Halt.Encoding.encodeTMCode c).take k).reverse,
          ∅⟩ : BiTape Bool).move_right = writtenTape c (k + 1)
  show (⟨none, StackTape.cons (some (encodedBit c ⟨k, hk⟩))
          (StackTape.map_some ((Halt.Encoding.encodeTMCode c).take k).reverse),
          ∅⟩ : BiTape Bool) = writtenTape c (k + 1)
  unfold writtenTape
  rw [h_take, List.reverse_append, List.reverse_singleton,
      List.singleton_append, map_some_cons]
  rfl

/-- A write step at a *non-final* index `k` (`k+1 < encodedLen c`):
move to `writeBit (k+1)`. -/
lemma writeBit_step_mid (k : ℕ) (hk : k < encodedLen c)
    (hk1 : k + 1 < encodedLen c) :
    (riceConstTM c).step ⟨some (RiceState.writeBit ⟨k, hk⟩), writtenTape c k⟩ =
      some ⟨some (RiceState.writeBit ⟨k + 1, hk1⟩), writtenTape c (k + 1)⟩ := by
  show (riceConstTM c).step ⟨some (RiceState.writeBit ⟨k, hk⟩), writtenTape c k⟩ = _
  have h_head : (writtenTape c k).head = none := rfl
  simp only [SingleTapeTM.step, riceConstTM, riceTr, h_head, dif_pos hk1]
  rw [writtenTape_step]

/-- A write step at the *final* index `k` (`k+1 = encodedLen c`): move
to `moveBack (encodedLen c)`. -/
lemma writeBit_step_last (k : ℕ) (hk : k < encodedLen c)
    (hk1 : k + 1 = encodedLen c) :
    (riceConstTM c).step ⟨some (RiceState.writeBit ⟨k, hk⟩), writtenTape c k⟩ =
      some ⟨some (RiceState.moveBack ⟨encodedLen c, Nat.lt_succ_self _⟩),
              writtenTape c (k + 1)⟩ := by
  show (riceConstTM c).step ⟨some (RiceState.writeBit ⟨k, hk⟩), writtenTape c k⟩ = _
  have h_head : (writtenTape c k).head = none := rfl
  have h_not : ¬ (k + 1 < encodedLen c) := by omega
  simp only [SingleTapeTM.step, riceConstTM, riceTr, h_head, dif_neg h_not]
  rw [writtenTape_step]

/-- Induction core for the write phase: from `⟨writeBit k, writtenTape
c k⟩`, with `d` bits still to write, reach the move-back phase. -/
private lemma write_phase_aux (d : ℕ) :
    ∀ (k : ℕ) (hk : k < encodedLen c), k + d + 1 = encodedLen c →
      ReflTransGen (riceConstTM c).TransitionRelation
        ⟨some (RiceState.writeBit ⟨k, hk⟩), writtenTape c k⟩
        ⟨some (RiceState.moveBack ⟨encodedLen c, Nat.lt_succ_self _⟩),
          writtenTape c (encodedLen c)⟩ := by
  induction d with
  | zero =>
    intro k hk hd
    have hk1 : k + 1 = encodedLen c := by omega
    have h_step := writeBit_step_last c k hk hk1
    rw [hk1] at h_step
    exact ReflTransGen.single h_step
  | succ d ih =>
    intro k hk hd
    have hk1 : k + 1 < encodedLen c := by omega
    refine ReflTransGen.head (writeBit_step_mid c k hk hk1) ?_
    exact ih (k + 1) hk1 (by omega)

/-- **Write phase.** From `⟨writeBit 0, ∅⟩`, `riceConstTM c` reaches
`⟨moveBack (encodedLen c), writtenTape c (encodedLen c)⟩` — the start
of the move-back phase, with `encodeTMCode c` fully laid down. -/
theorem write_phase :
    ReflTransGen (riceConstTM c).TransitionRelation
      ⟨some (RiceState.writeBit ⟨0, encodedLen_pos c⟩), BiTape.nil⟩
      ⟨some (RiceState.moveBack ⟨encodedLen c, Nat.lt_succ_self _⟩),
        writtenTape c (encodedLen c)⟩ := by
  have h := write_phase_aux c (encodedLen c - 1) 0 (encodedLen_pos c)
    (by have := encodedLen_pos c; omega)
  rwa [writtenTape_zero] at h

/-! ## Phase 3: move-back

The move-back phase walks the head left from past-the-end back to the
start of `encodeTMCode c`. The tape is tracked by a two-list split
`splitTape pre suf` (with `pre ++ suf = encodeTMCode c`): `pre` sits
reversed on the left stack, `suf` is "head ++ right". A `move_left`
moves the last element of `pre` to the front of `suf`. -/

/-- A `BiTape` representing `encodeTMCode c` split as `pre ++ suf`:
`pre` reversed on the left, `suf` as head-plus-right. -/
def splitTape (pre suf : List Bool) : BiTape Bool :=
  match suf with
  | [] => ⟨none, StackTape.map_some pre.reverse, ∅⟩
  | h :: t => ⟨some h, StackTape.map_some pre.reverse, StackTape.map_some t⟩

/-- With empty `pre`, `splitTape` is just `mk₁`. -/
lemma splitTape_nil_left (enc : List Bool) :
    splitTape [] enc = BiTape.mk₁ enc := by
  cases enc with
  | nil => rfl
  | cons h t => rfl

/-- The post-write tape `writtenTape c (encodedLen c)` is `splitTape`
with all of `encodeTMCode c` on the left. -/
lemma writtenTape_eq_splitTape :
    writtenTape c (encodedLen c) =
      splitTape (Halt.Encoding.encodeTMCode c) [] := by
  unfold writtenTape splitTape encodedLen
  rw [List.take_length]

/-- A `move_left` shifts the last element of `pre` to the front of
`suf`. -/
lemma move_left_splitTape (pre suf : List Bool) (x : Bool) :
    (splitTape (pre ++ [x]) suf).move_left = splitTape pre (x :: suf) := by
  have hrev : (pre ++ [x]).reverse = x :: pre.reverse := by
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
  cases suf with
  | nil =>
    show (⟨none, StackTape.map_some (pre ++ [x]).reverse, ∅⟩
            : BiTape Bool).move_left = _
    rw [hrev, map_some_cons]
    rfl
  | cons h t =>
    show (⟨some h, StackTape.map_some (pre ++ [x]).reverse,
            StackTape.map_some t⟩ : BiTape Bool).move_left = _
    rw [hrev, map_some_cons]
    rfl

/-- Writing the head symbol back leaves a `BiTape` unchanged. -/
lemma write_head_self (t : BiTape Bool) : t.write t.head = t := rfl

/-- A move-back step at counter `0`: hand off to the simulate phase. -/
lemma moveBack_step_zero (t : BiTape Bool) (h0 : 0 < encodedLen c + 1) :
    (riceConstTM c).step ⟨some (RiceState.moveBack ⟨0, h0⟩), t⟩ =
      some ⟨some (RiceState.inC c.q₀), t⟩ := by
  show (riceConstTM c).step ⟨some (RiceState.moveBack ⟨0, h0⟩), t⟩ = _
  simp only [SingleTapeTM.step, riceConstTM, riceTr]
  rfl

/-- A move-back step at a positive counter `m+1`: move left, decrement. -/
lemma moveBack_step_pos (t : BiTape Bool) (m : ℕ)
    (hm : m + 1 < encodedLen c + 1) (hm' : m < encodedLen c + 1) :
    (riceConstTM c).step ⟨some (RiceState.moveBack ⟨m + 1, hm⟩), t⟩ =
      some ⟨some (RiceState.moveBack ⟨m, hm'⟩), t.move_left⟩ := by
  show (riceConstTM c).step ⟨some (RiceState.moveBack ⟨m + 1, hm⟩), t⟩ = _
  simp only [SingleTapeTM.step, riceConstTM, riceTr]
  rfl

/-- Induction core for the move-back phase, by induction on the
move-back counter `m` (which equals `pre.length`). -/
private lemma moveBack_phase_aux :
    ∀ (m : ℕ) (pre suf : List Bool) (_ : pre.length = m)
      (_ : pre ++ suf = Halt.Encoding.encodeTMCode c)
      (hlen : m < encodedLen c + 1),
      ReflTransGen (riceConstTM c).TransitionRelation
        ⟨some (RiceState.moveBack ⟨m, hlen⟩), splitTape pre suf⟩
        ⟨some (RiceState.inC c.q₀),
          BiTape.mk₁ (Halt.Encoding.encodeTMCode c)⟩ := by
  intro m
  induction m with
  | zero =>
    intro pre suf hm h hlen
    have h_pre : pre = [] := List.eq_nil_of_length_eq_zero hm
    subst h_pre
    have h_suf : suf = Halt.Encoding.encodeTMCode c := by simpa using h
    subst h_suf
    rw [splitTape_nil_left]
    exact ReflTransGen.single
      (moveBack_step_zero c (BiTape.mk₁ (Halt.Encoding.encodeTMCode c)) hlen)
  | succ m ih =>
    intro pre suf hm h hlen
    obtain ⟨pre', x, rfl⟩ : ∃ pre' x, pre = pre' ++ [x] := by
      rcases List.eq_nil_or_concat pre with h_nil | ⟨pre', x, h_eq⟩
      · rw [h_nil] at hm; simp at hm
      · exact ⟨pre', x, by rw [h_eq, List.concat_eq_append]⟩
    have hm' : pre'.length = m := by
      rw [List.length_append] at hm; simpa using hm
    have hlen' : m < encodedLen c + 1 := by omega
    have hstep := moveBack_step_pos c (splitTape (pre' ++ [x]) suf) m hlen hlen'
    rw [move_left_splitTape] at hstep
    refine ReflTransGen.head hstep ?_
    exact ih pre' (x :: suf) hm' (by simpa using h) hlen'

/-- **Move-back phase.** From `⟨moveBack (encodedLen c), writtenTape c
(encodedLen c)⟩`, `riceConstTM c` reaches `⟨inC c.q₀, mk₁ (encodeTMCode
c)⟩` — the simulate phase begins exactly where `c.toTM` would start on
input `encodeTMCode c`. -/
theorem moveBack_phase :
    ReflTransGen (riceConstTM c).TransitionRelation
      ⟨some (RiceState.moveBack ⟨encodedLen c, Nat.lt_succ_self _⟩),
        writtenTape c (encodedLen c)⟩
      ⟨some (RiceState.inC c.q₀), BiTape.mk₁ (Halt.Encoding.encodeTMCode c)⟩ := by
  rw [writtenTape_eq_splitTape]
  exact moveBack_phase_aux c (encodedLen c) (Halt.Encoding.encodeTMCode c) []
    rfl (List.append_nil _) (Nat.lt_succ_self _)

/-! ## Phases 1–3 composed -/

/-- The composite of the erase, write, and move-back phases: from the
initial configuration `⟨erase, mk₁ w⟩`, `riceConstTM c` reaches
`⟨inC c.q₀, mk₁ (encodeTMCode c)⟩` for *every* input `w`. -/
theorem setup_phase (w : List Bool) :
    ReflTransGen (riceConstTM c).TransitionRelation
      ⟨some RiceState.erase, BiTape.mk₁ w⟩
      ⟨some (RiceState.inC c.q₀), BiTape.mk₁ (Halt.Encoding.encodeTMCode c)⟩ :=
  (erase_phase c w).trans ((write_phase c).trans (moveBack_phase c))

/-! ## Phase 4: simulate

In states `inC q`, `riceConstTM c` runs `c.tr` verbatim (just tagging
the next state with `inC`). So `liftCfg` — tagging a `c.toTM`
configuration's state with `inC` — is a step-for-step bisimulation
between `c.toTM` and the `inC`-fragment of `riceConstTM c`. -/

/-- Lift a `c.toTM` configuration into `riceConstTM c` by tagging the
state with `inC`. -/
def liftCfg (cfg : c.toTM.Cfg) : (riceConstTM c).Cfg :=
  ⟨cfg.state.map RiceState.inC, cfg.BiTape⟩

/-- One step commutes with `liftCfg`: the `inC` states of
`riceConstTM c` bisimulate `c.toTM`. -/
lemma step_liftCfg (cfg : c.toTM.Cfg) :
    (riceConstTM c).step (liftCfg c cfg) =
      (c.toTM.step cfg).map (liftCfg c) := by
  obtain ⟨st, t⟩ := cfg
  cases st with
  | none => rfl
  | some q' =>
    show (riceConstTM c).step ⟨some (RiceState.inC q'), t⟩ =
      (c.toTM.step ⟨some q', t⟩).map (liftCfg c)
    rcases hcr : c.tr q' t.head with ⟨stmt, next⟩
    simp only [SingleTapeTM.step, riceConstTM_tr, riceTr, Halt.TMCode.toTM_tr,
               hcr, liftCfg, Option.map_some]
    rfl

/-- Reachability lifts from `c.toTM` to the `inC`-fragment of
`riceConstTM c`. -/
lemma reach_to_rice {cfg cfg' : c.toTM.Cfg}
    (h : ReflTransGen c.toTM.TransitionRelation cfg cfg') :
    ReflTransGen (riceConstTM c).TransitionRelation
      (liftCfg c cfg) (liftCfg c cfg') := by
  refine ReflTransGen.lift (liftCfg c) ?_ h
  intro a b hab
  show (riceConstTM c).step (liftCfg c a) = some (liftCfg c b)
  rw [step_liftCfg, show c.toTM.step a = some b from hab]
  rfl

/-- Reachability descends: any `riceConstTM c` configuration reachable
from a lifted config is itself lifted, and the underlying `c.toTM`
config is reachable. -/
lemma reach_from_rice {cfg : c.toTM.Cfg} {d : (riceConstTM c).Cfg}
    (h : ReflTransGen (riceConstTM c).TransitionRelation (liftCfg c cfg) d) :
    ∃ cfg', d = liftCfg c cfg' ∧
      ReflTransGen c.toTM.TransitionRelation cfg cfg' := by
  induction h with
  | refl => exact ⟨cfg, rfl, ReflTransGen.refl⟩
  | tail _ h_step ih =>
    obtain ⟨cfg', h_eq, h_reach⟩ := ih
    subst h_eq
    rw [show (riceConstTM c).TransitionRelation = fun a b =>
          (riceConstTM c).step a = some b from rfl] at h_step
    rw [step_liftCfg] at h_step
    obtain ⟨cfg'', h_cfg'', h_d⟩ := Option.map_eq_some_iff.mp h_step
    exact ⟨cfg'', h_d.symm, h_reach.tail h_cfg''⟩

/-! ## Determinism / confluence -/

/-- `riceConstTM`'s transition relation is functional (deterministic). -/
lemma step_deterministic (x y z : (riceConstTM c).Cfg)
    (h₁ : (riceConstTM c).TransitionRelation x y)
    (h₂ : (riceConstTM c).TransitionRelation x z) : y = z := by
  rw [show (riceConstTM c).TransitionRelation = fun a b =>
        (riceConstTM c).step a = some b from rfl] at h₁ h₂
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-- For a functional relation, any two configurations reachable from a
common source are comparable. -/
lemma reflTransGen_total {α : Type} {r : α → α → Prop}
    (hfun : ∀ x y z, r x y → r x z → y = z) {a b d : α}
    (hab : ReflTransGen r a b) :
    ReflTransGen r a d → ReflTransGen r b d ∨ ReflTransGen r d b := by
  induction hab with
  | refl => exact fun h => Or.inl h
  | tail _ hstep ih =>
    intro had
    rcases ih had with h | h
    · rcases h.cases_head with h_eq | ⟨m, hm, hmd⟩
      · exact Or.inr (h_eq ▸ ReflTransGen.single hstep)
      · exact Or.inl ((hfun _ _ _ hm hstep) ▸ hmd)
    · exact Or.inr (h.tail hstep)

/-! ## The dichotomy -/

/-- `riceConstTM c` halts on `w` iff `c.toTM` halts on `encodeTMCode c`
— *independent of `w`*. -/
theorem halts_riceConstTM_iff (w : List Bool) :
    PCP.Halts (riceConstTM c) w ↔
      PCP.Halts c.toTM (Halt.Encoding.encodeTMCode c) := by
  have h_initR : SingleTapeTM.initCfg (riceConstTM c) w =
      (⟨some RiceState.erase, BiTape.mk₁ w⟩ : (riceConstTM c).Cfg) := rfl
  have h_initC : liftCfg c (SingleTapeTM.initCfg c.toTM
      (Halt.Encoding.encodeTMCode c)) =
      (⟨some (RiceState.inC c.q₀),
        BiTape.mk₁ (Halt.Encoding.encodeTMCode c)⟩ : (riceConstTM c).Cfg) := rfl
  constructor
  · rintro ⟨tape, h_chain⟩
    rw [h_initR] at h_chain
    rcases reflTransGen_total (step_deterministic c) (setup_phase c w) h_chain
      with h | h
    · obtain ⟨cfg', h_eq, h_reach⟩ := reach_from_rice c (h_initC ▸ h)
      have h_cfg' : cfg' = (⟨none, tape⟩ : c.toTM.Cfg) := by
        obtain ⟨st, t⟩ := cfg'
        simp only [liftCfg] at h_eq
        obtain ⟨h_st, h_t⟩ := SingleTapeTM.Cfg.mk.injEq .. |>.mp h_eq
        cases st with
        | none => rw [h_t]
        | some q => exact absurd h_st (by simp)
      exact ⟨tape, h_cfg' ▸ h_reach⟩
    · exfalso
      rcases h.cases_head with h_eq | ⟨m, hm, _⟩
      · exact absurd h_eq (by simp)
      · exact absurd hm (by
          simp [SingleTapeTM.TransitionRelation, SingleTapeTM.step])
  · intro h_halts
    obtain ⟨tape, h_chain⟩ := h_halts
    refine ⟨tape, ?_⟩
    rw [h_initR]
    refine (setup_phase c w).trans ?_
    have h := reach_to_rice c h_chain
    rw [h_initC] at h
    exact h

/-- **The Rice extender behaviour dichotomy** — formerly the postulate
`semHalt_riceConstTM_dichotomy` in `Halt.Rice.Theorem`. -/
theorem semHalt_riceConstTM_dichotomy :
    (PCP.Halts c.toTM (Halt.Encoding.encodeTMCode c) →
      SemHalt (riceConstTM c) = Set.univ) ∧
    (¬ PCP.Halts c.toTM (Halt.Encoding.encodeTMCode c) →
      SemHalt (riceConstTM c) = ∅) := by
  refine ⟨fun h_halts => ?_, fun h_not => ?_⟩
  · ext w
    simp only [SemHalt, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact (halts_riceConstTM_iff c w).mpr h_halts
  · ext w
    simp only [SemHalt, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => h_not ((halts_riceConstTM_iff c w).mp h)

end Halt.Rice
