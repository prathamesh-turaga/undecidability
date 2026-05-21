/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Halt.Basic

@[expose] public section

/-!
# `codeOf` — embedding any `SingleTapeTM Bool` into `TMCode`

A `TMCode` is a `SingleTapeTM Bool` whose state set is fixed to
`Fin (n + 1)`. To form the diagonal `c_diag := codeOf diagTM`, we need
a generic operation that turns any concrete `SingleTapeTM Bool` into a
`TMCode` while preserving its halting behaviour.

The construction picks the unique `n` with `n + 1 = Fintype.card tm.State`
(possible because `tm.q₀` makes `tm.State` non-empty) and bijects through
`Fintype.equivFin tm.State : tm.State ≃ Fin (n + 1)`. The bijection
yields a `cfgEquiv : tm.Cfg ≃ (codeOf tm).toTM.Cfg` that commutes with
`step` in both directions, hence preserves `Halts`.

## Key theorem

```lean
theorem halts_codeOf_iff (tm : SingleTapeTM Bool) (w : List Bool) :
    PCP.Halts (codeOf tm).toTM w ↔ PCP.Halts tm w
```

This is what makes the self-application `c_diag = codeOf (diagTM D)`
work in `Halt.Undecidable`: `c_diag.toTM` halts on `encodeTMCode c_diag`
iff `diagTM D` does. -/

namespace Halt

open Turing

variable (tm : SingleTapeTM Bool)

/-- The state-count of `codeOf tm`: one less than `Fintype.card tm.State`. -/
def numStatesOf : ℕ := Fintype.card tm.State - 1

/-- The state-count equation: `Fintype.card tm.State = numStatesOf tm + 1`.
Holds because `tm.q₀` makes `tm.State` non-empty. -/
lemma card_state_eq_succ : Fintype.card tm.State = numStatesOf tm + 1 := by
  unfold numStatesOf
  have h : 0 < Fintype.card tm.State := Fintype.card_pos
  omega

/-- The state-renaming bijection `tm.State ≃ Fin (numStatesOf tm + 1)`. -/
noncomputable def stateEquiv : tm.State ≃ Fin (numStatesOf tm + 1) :=
  (Fintype.equivFin tm.State).trans
    (Fin.castOrderIso (card_state_eq_succ tm)).toEquiv

/-- Convert any `SingleTapeTM Bool` to a `TMCode` by renaming states
through `stateEquiv tm`. -/
noncomputable def codeOf : Halt.TMCode where
  numStates := numStatesOf tm
  q₀ := stateEquiv tm tm.q₀
  tr i ob :=
    let (stmt, q') := tm.tr ((stateEquiv tm).symm i) ob
    (stmt, q'.map (stateEquiv tm))

@[simp] lemma codeOf_numStates :
    (codeOf tm).numStates = numStatesOf tm := rfl

@[simp] lemma codeOf_q₀ :
    (codeOf tm).q₀ = stateEquiv tm tm.q₀ := rfl

@[simp] lemma codeOf_tr (i : Fin (numStatesOf tm + 1)) (ob : Option Bool) :
    (codeOf tm).tr i ob =
      ((tm.tr ((stateEquiv tm).symm i) ob).1,
       (tm.tr ((stateEquiv tm).symm i) ob).2.map (stateEquiv tm)) := rfl

/-! ## Bisimulation between `tm` and `(codeOf tm).toTM` -/

/-- The configuration bijection induced by `stateEquiv tm`. -/
noncomputable def cfgEquiv : tm.Cfg ≃ (codeOf tm).toTM.Cfg where
  toFun cfg := ⟨cfg.state.map (stateEquiv tm), cfg.BiTape⟩
  invFun cfg := ⟨cfg.state.map (stateEquiv tm).symm, cfg.BiTape⟩
  left_inv := by
    rintro ⟨st, t⟩
    show (⟨(st.map (stateEquiv tm)).map (stateEquiv tm).symm, t⟩ : tm.Cfg)
        = ⟨st, t⟩
    congr 1
    cases st with
    | none => rfl
    | some q => simp
  right_inv := by
    rintro ⟨st, t⟩
    show (⟨(st.map (stateEquiv tm).symm).map (stateEquiv tm), t⟩
            : (codeOf tm).toTM.Cfg) = ⟨st, t⟩
    congr 1
    cases st with
    | none => rfl
    | some q => simp

@[simp] lemma cfgEquiv_state (cfg : tm.Cfg) :
    (cfgEquiv tm cfg).state = cfg.state.map (stateEquiv tm) := rfl

@[simp] lemma cfgEquiv_BiTape (cfg : tm.Cfg) :
    (cfgEquiv tm cfg).BiTape = cfg.BiTape := rfl

@[simp] lemma cfgEquiv_mk (st : Option tm.State) (t : BiTape Bool) :
    cfgEquiv tm ⟨st, t⟩ = ⟨st.map (stateEquiv tm), t⟩ := rfl

@[simp] lemma cfgEquiv_symm_state (cfg : (codeOf tm).toTM.Cfg) :
    ((cfgEquiv tm).symm cfg).state = cfg.state.map (stateEquiv tm).symm := rfl

@[simp] lemma cfgEquiv_symm_BiTape (cfg : (codeOf tm).toTM.Cfg) :
    ((cfgEquiv tm).symm cfg).BiTape = cfg.BiTape := rfl

@[simp] lemma cfgEquiv_symm_mk (st : Option (codeOf tm).toTM.State)
    (t : BiTape Bool) :
    (cfgEquiv tm).symm ⟨st, t⟩ = ⟨st.map (stateEquiv tm).symm, t⟩ := rfl

/-- `cfgEquiv` maps initial configurations to initial configurations. -/
@[simp] lemma cfgEquiv_initCfg (w : List Bool) :
    cfgEquiv tm (SingleTapeTM.initCfg tm w) =
      SingleTapeTM.initCfg (codeOf tm).toTM w := rfl

/-- `cfgEquiv` maps halt configurations to halt configurations. -/
@[simp] lemma cfgEquiv_halt (tape : BiTape Bool) :
    cfgEquiv tm ⟨none, tape⟩ = ⟨none, tape⟩ := rfl

@[simp] lemma cfgEquiv_symm_halt (tape : BiTape Bool) :
    (cfgEquiv tm).symm ⟨none, tape⟩ = ⟨none, tape⟩ := rfl

/-! ### Step commutes with `cfgEquiv` -/

/-- One `tm` step lifts through `cfgEquiv` to one `(codeOf tm).toTM` step. -/
lemma step_cfgEquiv (cfg : tm.Cfg) :
    Option.map (cfgEquiv tm) (tm.step cfg) =
      (codeOf tm).toTM.step (cfgEquiv tm cfg) := by
  obtain ⟨st, t⟩ := cfg
  cases st with
  | none => rfl
  | some q =>
    -- Unfold step on both sides (cfgEquiv tm ⟨some q, t⟩ = ⟨some (stateEquiv tm q), t⟩).
    show Option.map (cfgEquiv tm) (
            match tm.tr q t.head with
            | ⟨⟨wr, dir⟩, q''⟩ => some ⟨q'', (t.write wr).optionMove dir⟩) =
          (match (codeOf tm).toTM.tr (stateEquiv tm q) t.head with
            | ⟨⟨wr, dir⟩, q''⟩ => some ⟨q'', (t.write wr).optionMove dir⟩)
    -- The codeOf tr is computed from tm.tr; collapse to a single lookup.
    have h_code : (codeOf tm).toTM.tr (stateEquiv tm q) t.head =
        ((tm.tr q t.head).1, (tm.tr q t.head).2.map (stateEquiv tm)) := by
      show (codeOf tm).tr (stateEquiv tm q) t.head = _
      rw [codeOf_tr, Equiv.symm_apply_apply]
    rw [h_code]
    -- Now both matches share `tm.tr q t.head`.
    generalize h_tr : tm.tr q t.head = result
    obtain ⟨⟨wr, dir⟩, q''⟩ := result
    rfl

/-- One `(codeOf tm).toTM` step descends through `(cfgEquiv tm).symm` to one
`tm` step. -/
lemma step_cfgEquiv_symm (cfg : (codeOf tm).toTM.Cfg) :
    Option.map (cfgEquiv tm).symm ((codeOf tm).toTM.step cfg) =
      tm.step ((cfgEquiv tm).symm cfg) := by
  have h := step_cfgEquiv tm ((cfgEquiv tm).symm cfg)
  rw [Equiv.apply_symm_apply] at h
  rw [← h, Option.map_map]
  -- (cfgEquiv tm).symm ∘ (cfgEquiv tm) = id
  have h_comp : ((cfgEquiv tm).symm ∘ (cfgEquiv tm)) = id := by
    ext c
    exact (cfgEquiv tm).symm_apply_apply c
  rw [h_comp, Option.map_id_fun, id_eq]

/-! ### Reachability lifts both directions -/

/-- Reachability lifts from `tm` to `(codeOf tm).toTM` via `cfgEquiv`. -/
private lemma reach_to_codeOf {cfg cfg' : tm.Cfg}
    (h : Relation.ReflTransGen tm.TransitionRelation cfg cfg') :
    Relation.ReflTransGen (codeOf tm).toTM.TransitionRelation
      (cfgEquiv tm cfg) (cfgEquiv tm cfg') := by
  refine Relation.ReflTransGen.lift (cfgEquiv tm) ?_ h
  intro a b h_step
  show (codeOf tm).toTM.step (cfgEquiv tm a) = some (cfgEquiv tm b)
  have := step_cfgEquiv tm a
  rw [h_step] at this
  exact this.symm

/-- Reachability descends from `(codeOf tm).toTM` to `tm` via
`(cfgEquiv tm).symm`. -/
private lemma reach_from_codeOf {cfg cfg' : (codeOf tm).toTM.Cfg}
    (h : Relation.ReflTransGen (codeOf tm).toTM.TransitionRelation cfg cfg') :
    Relation.ReflTransGen tm.TransitionRelation
      ((cfgEquiv tm).symm cfg) ((cfgEquiv tm).symm cfg') := by
  refine Relation.ReflTransGen.lift (cfgEquiv tm).symm ?_ h
  intro a b h_step
  show tm.step ((cfgEquiv tm).symm a) = some ((cfgEquiv tm).symm b)
  have := step_cfgEquiv_symm tm a
  rw [h_step] at this
  exact this.symm

/-! ### Halting iff -/

/-- **`codeOf` correctness**: a `SingleTapeTM Bool` halts on `w` iff its
`codeOf` interpretation halts on `w`. -/
theorem halts_codeOf_iff (w : List Bool) :
    PCP.Halts (codeOf tm).toTM w ↔ PCP.Halts tm w := by
  constructor
  · rintro ⟨tape, h_chain⟩
    have h_tm :=
      reach_from_codeOf tm
        (cfg := SingleTapeTM.initCfg (codeOf tm).toTM w)
        (cfg' := ⟨none, tape⟩) h_chain
    rw [cfgEquiv_symm_halt] at h_tm
    have h_init :
        (cfgEquiv tm).symm (SingleTapeTM.initCfg (codeOf tm).toTM w) =
          SingleTapeTM.initCfg tm w := by
      rw [← cfgEquiv_initCfg]
      exact (cfgEquiv tm).symm_apply_apply _
    rw [h_init] at h_tm
    exact ⟨tape, h_tm⟩
  · rintro ⟨tape, h_chain⟩
    have h_code := reach_to_codeOf tm h_chain
    rw [cfgEquiv_initCfg, cfgEquiv_halt] at h_code
    exact ⟨tape, h_code⟩

end Halt


