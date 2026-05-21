/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Halt.Basic

@[expose] public section

/-!
# Concrete helper Turing machines

A worked example: `invertTM`, a 2-state `SingleTapeTM Bool` that halts
on input `[false]` and loops forever on input `[true]`. Its construction
illustrates the basic pattern of proving non-halting via a "closed
loop-state" invariant.

`invertTM` was originally intended as a building block for a
composition-based diagonal (`compComputer D invertTM`) but the final
proof in `Halt.Undecidable` inlines the diagonal TM directly, so this
file is not on the proof-chain critical path. It is retained as a
self-contained example and reference. -/

namespace Halt.Helpers

open Turing

/-! ## `invertTM` — 2-state TM that loops on `[true]` and halts on `[false]`

We use `State := Fin 2`: `0` is the *read* state, `1` is the *loop*
state. State `1` only ever transitions to itself, so once entered the
TM never halts. -/

/-- The read state of `invertTM`. -/
@[reducible] def invertRead : Fin 2 := 0

/-- The loop state of `invertTM`. -/
@[reducible] def invertLoop : Fin 2 := 1

/-- Concrete `SingleTapeTM Bool` with the following behaviour:
* `q = 0 (read), sym = some false` → write `some false`, no move, halt.
* every other case → write blank, no move, transition to state `1`. -/
def invertTM : SingleTapeTM Bool where
  State := Fin 2
  q₀ := invertRead
  tr q sym :=
    match q, sym with
    | ⟨0, _⟩, some false => (⟨some false, none⟩, none)
    | _, _ => (⟨none, none⟩, some invertLoop)

/-! ### Behaviour on `[false]` — single-step halt -/

/-- One step from the initial configuration on `[false]` reaches the
halt configuration with output `[false]`. -/
lemma invertTM_step_false :
    invertTM.step (SingleTapeTM.initCfg invertTM [false]) =
      some (SingleTapeTM.haltCfg invertTM [false]) := by
  rfl

/-- `invertTM` outputs `[false]` on input `[false]`. -/
lemma outputs_invertTM_false :
    SingleTapeTM.Outputs invertTM [false] [false] :=
  Relation.ReflTransGen.single invertTM_step_false

/-- `invertTM` halts on input `[false]`. -/
lemma halts_invertTM_false : PCP.Halts invertTM [false] :=
  ⟨BiTape.mk₁ [false], outputs_invertTM_false⟩

/-! ### Behaviour on `[true]` — loops forever -/

/-- One step from the initial configuration on `[true]` reaches a
config in the `loop` state. -/
lemma invertTM_step_true :
    invertTM.step (SingleTapeTM.initCfg invertTM [true]) =
      some ⟨some invertLoop, (BiTape.mk₁ [true]).write none⟩ := by
  rfl

/-- From state `1`, every step keeps the state at `1`. -/
lemma invertTM_step_loop (t : BiTape Bool) :
    invertTM.step ⟨some invertLoop, t⟩ =
      some ⟨some invertLoop, t.write none⟩ := by
  rfl

/-- The set of configurations with state `some 1` is closed under the
transition relation. -/
private lemma invertTM_loop_closed
    (cfg cfg' : invertTM.Cfg)
    (h_loop : cfg.state = some invertLoop)
    (h_step : invertTM.TransitionRelation cfg cfg') :
    cfg'.state = some invertLoop := by
  obtain ⟨st, t⟩ := cfg
  cases st with
  | none =>
    simp [SingleTapeTM.TransitionRelation, SingleTapeTM.step] at h_step
  | some q =>
    -- `h_loop` forces `q = 1`.
    have hq : q = invertLoop := Option.some_inj.mp h_loop
    subst hq
    rw [SingleTapeTM.TransitionRelation, invertTM_step_loop] at h_step
    rcases cfg' with ⟨st', t'⟩
    injection h_step with h_eq
    injection h_eq with h_st _
    exact h_st.symm

/-- From a state-1 configuration, every reachable configuration is also
in state 1. -/
private lemma invertTM_loop_persistent
    {cfg cfg' : invertTM.Cfg}
    (h_loop : cfg.state = some invertLoop)
    (h_reach : Relation.ReflTransGen invertTM.TransitionRelation cfg cfg') :
    cfg'.state = some invertLoop := by
  induction h_reach with
  | refl => exact h_loop
  | tail _ h_step ih => exact invertTM_loop_closed _ _ ih h_step

/-- `invertTM` does **not** halt on input `[true]`. -/
lemma not_halts_invertTM_true : ¬ PCP.Halts invertTM [true] := by
  rintro ⟨tape, h_chain⟩
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp h_chain with hrefl | htg
  · -- Zero-step chain: but `initCfg [true]` has state `some 0`, not `none`.
    have h_init :
        (SingleTapeTM.initCfg invertTM [true]).state = some invertRead := rfl
    rw [← hrefl] at h_init
    simp at h_init
  · -- One or more steps. Peel off the first via `head'_iff`.
    obtain ⟨cfg₁, h_first, h_rest⟩ := Relation.TransGen.head'_iff.mp htg
    have h_cfg1 :
        cfg₁ = ⟨some invertLoop, (BiTape.mk₁ [true]).write none⟩ := by
      have h_eq := h_first
      simp only [SingleTapeTM.TransitionRelation, invertTM_step_true,
        Option.some.injEq] at h_eq
      exact h_eq.symm
    subst h_cfg1
    have h_loop_dest : (⟨none, tape⟩ : invertTM.Cfg).state =
        some invertLoop :=
      invertTM_loop_persistent rfl h_rest
    simp at h_loop_dest

end Halt.Helpers
