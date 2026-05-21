/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Halt.Rice.Basic

@[expose] public section

/-!
# Trivial Turing machines for Rice's theorem

Two `SingleTapeTM Bool`s that exhibit the extremes of halting
behaviour:

* `tm_alwaysHalt` — a 1-state TM that halts on every input. Its
  `SemHalt` is the universe `Set.univ`.
* `tm_loop`       — a 1-state TM that loops on every input (transitions
  to itself with no write/move). Its `SemHalt` is `∅`.

These provide the witnesses used to instantiate Rice's theorem.
-/

namespace Halt.Rice

open Turing PCP

/-! ## `tm_alwaysHalt` — halts immediately on any input -/

/-- One-state TM whose initial state's transition is "halt". -/
def tm_alwaysHalt : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ _ := (⟨none, none⟩, none)

lemma tm_alwaysHalt_step (w : List Bool) :
    tm_alwaysHalt.step (SingleTapeTM.initCfg tm_alwaysHalt w) =
      some ⟨none, (BiTape.mk₁ w).write none⟩ := by
  cases w with
  | nil => rfl
  | cons _ _ => rfl

/-- `tm_alwaysHalt` halts on every input. -/
lemma halts_tm_alwaysHalt (w : List Bool) : PCP.Halts tm_alwaysHalt w := by
  refine ⟨(BiTape.mk₁ w).write none, ?_⟩
  exact Relation.ReflTransGen.single (tm_alwaysHalt_step w)

/-- `tm_alwaysHalt` has halt-set equal to `univ`. -/
lemma semHalt_tm_alwaysHalt : SemHalt tm_alwaysHalt = Set.univ := by
  ext w
  exact ⟨fun _ => Set.mem_univ _, fun _ => halts_tm_alwaysHalt w⟩

/-! ## `tm_loop` — loops forever on any input -/

/-- One-state TM that on any input loops forever (transitions to itself
with a no-op `Stmt`). -/
def tm_loop : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ _ := (⟨none, none⟩, some ())

lemma tm_loop_step_some (t : BiTape Bool) :
    tm_loop.step ⟨some (), t⟩ = some ⟨some (), t.write none⟩ := rfl

/-- One step from a state-`some ()` configuration of `tm_loop` lands
in another state-`some ()` configuration. -/
private lemma tm_loop_step_state_persistent
    {cfg cfg' : tm_loop.Cfg}
    (h_state : cfg.state = some ())
    (h_step : tm_loop.TransitionRelation cfg cfg') :
    cfg'.state = some () := by
  obtain ⟨st, t⟩ := cfg
  cases st with
  | none => simp at h_state
  | some u =>
    -- u : tm_loop.State = Unit. Step is identical regardless of u.
    have h_eq : tm_loop.step ⟨some u, t⟩ = some ⟨some (), t.write none⟩ := rfl
    rw [SingleTapeTM.TransitionRelation, h_eq] at h_step
    obtain ⟨st', t'⟩ := cfg'
    injection h_step with h_cfg
    obtain ⟨h_st, _⟩ := SingleTapeTM.Cfg.mk.injEq .. |>.mp h_cfg
    exact h_st.symm

/-- From a state-`some ()` configuration of `tm_loop`, every reachable
configuration also has state `some ()`. -/
private lemma tm_loop_state_persistent
    {cfg cfg' : tm_loop.Cfg}
    (h : cfg.state = some ())
    (h_reach : Relation.ReflTransGen tm_loop.TransitionRelation cfg cfg') :
    cfg'.state = some () := by
  induction h_reach with
  | refl => exact h
  | tail _ h_step ih => exact tm_loop_step_state_persistent ih h_step

/-- `tm_loop` does *not* halt on any input. -/
lemma not_halts_tm_loop (w : List Bool) : ¬ PCP.Halts tm_loop w := by
  rintro ⟨tape, h_chain⟩
  have h_init : (SingleTapeTM.initCfg tm_loop w).state = some () := rfl
  have h_persist : (⟨none, tape⟩ : tm_loop.Cfg).state = some () :=
    tm_loop_state_persistent h_init h_chain
  simp at h_persist

/-- `tm_loop` has halt-set equal to `∅`. -/
lemma semHalt_tm_loop : SemHalt tm_loop = ∅ := by
  ext w
  exact ⟨fun h => not_halts_tm_loop w h, fun h => h.elim⟩

end Halt.Rice
