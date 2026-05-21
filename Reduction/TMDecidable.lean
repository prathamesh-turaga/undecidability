/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Reduction.Basic
public import PCP.Halt

@[expose] public section

/-!
# TM-level decidability

The framework's `Decidable P` / `Undecidable P` (in `Reduction.Basic`)
are *classically vacuous* — every predicate has a classical Bool-valued
decider, so `Undecidable P` is literally never inhabited classically.
That's useful only as an abstract bookkeeping notion.

This file defines the **TM-level** versions, which are the genuinely
meaningful undecidability claims, built directly on cslib's
`SingleTapeTM.TimeComputable`:

* `TMComputable f`  — some `SingleTapeTM Bool` computes `f` within a
  length-indexed time bound. Defined as `Nonempty (TimeComputable f)`.
* `boolIndicator pred` — the function `bits ↦ [true]/[false]` according
  to `pred`.
* `TMDecidable pred`   — `TMComputable (boolIndicator pred)`.
* `TMUndecidable pred` — `¬ TMDecidable pred`.
* `TMDecides D pred`   — the explicit "TM `D` outputs `[true]`/`[false]`"
  relation, related to `TMDecidable` by `TMDecidable.exists_TMDecides`.

## Discharged postulates

Because `TMComputable` is now grounded in cslib's `TimeComputable`
(which ships `TimeComputable.id` and `TimeComputable.comp`), the
TM-composition machinery is **proved, not postulated**:

* `TMComputable.id` — from `TimeComputable.id`.
* `TMComputable.comp` — from `TimeComputable.comp`, after monotonising
  the second machine's time bound (cslib's `comp` requires a monotone
  bound; `TimeComputable.monotonise` supplies one).
* `TMUndecidable.of_TMReduction` — the transfer theorem, now a clean
  consequence of `TMComputable.comp` and `boolIndicator (pred₂ ∘ f) =
  boolIndicator pred₁`.

The only remaining TM-level postulates are the *per-edge*
`TMComputable` witnesses (each asserts a specific concrete reduction
function is TM-computable — true, but requires building the TM) and
the two substantive constructions (`normalisingWrapper`,
`semHalt_riceConstTM_dichotomy`).
-/

namespace DiagonaLean

open PCP Turing SingleTapeTM Relation

/-! ## Bridge: `OutputsWithinTime` ⇒ `Outputs` -/

/-- A time-bounded output run is in particular an (unbounded) output
run: forget the step count. -/
theorem outputs_of_outputsWithinTime {tm : SingleTapeTM Bool}
    {l l' : List Bool} {m : ℕ} (h : tm.OutputsWithinTime l l' m) :
    tm.Outputs l l' := by
  obtain ⟨n, _, hn⟩ := h
  exact hn.reflTransGen

/-! ## Monotonising a `TimeComputable`'s time bound

cslib's `TimeComputable.comp` requires the second machine's time bound
to be `Monotone`. Any `TimeComputable` can be upgraded to one with a
monotone bound by replacing `time_bound` with its running supremum. -/

/-- Replace a `TimeComputable`'s time bound by its running supremum
`n ↦ sup { time_bound k | k ≤ n }`, which is monotone and dominates
the original (so `outputsFunInTime` still holds via
`RelatesWithinSteps.of_le`). -/
noncomputable def monotoniseTC {g : List Bool → List Bool}
    (tc : TimeComputable (Symbol := Bool) g) :
    TimeComputable (Symbol := Bool) g where
  tm := tc.tm
  time_bound n := (Finset.range (n + 1)).sup tc.time_bound
  outputsFunInTime a :=
    RelatesWithinSteps.of_le (tc.outputsFunInTime a)
      (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self _)))

lemma monotoniseTC_isMonotone {g : List Bool → List Bool}
    (tc : TimeComputable (Symbol := Bool) g) :
    Monotone (monotoniseTC tc).time_bound := by
  intro m n hmn
  show (Finset.range (m + 1)).sup tc.time_bound ≤
       (Finset.range (n + 1)).sup tc.time_bound
  apply Finset.sup_mono
  intro x hx
  rw [Finset.mem_range] at hx ⊢
  omega

/-! ## TM-level decidability of `List Bool → Prop` predicates -/

/-- A function `f : List Bool → List Bool` is TM-computable iff some
`SingleTapeTM Bool` computes it within a length-indexed time bound. -/
def TMComputable (f : List Bool → List Bool) : Prop :=
  Nonempty (TimeComputable (Symbol := Bool) f)

open Classical in
/-- The Boolean indicator of a predicate: `[true]` on members,
`[false]` otherwise. Noncomputable (uses classical decidability). -/
noncomputable def boolIndicator (pred : List Bool → Prop) :
    List Bool → List Bool :=
  fun bits => if pred bits then [true] else [false]

/-- TM-decidability of `pred`: the Boolean indicator of `pred` is
TM-computable. -/
def TMDecidable (pred : List Bool → Prop) : Prop :=
  TMComputable (boolIndicator pred)

/-- TM-undecidability of `pred`: `pred` is not TM-decidable. -/
def TMUndecidable (pred : List Bool → Prop) : Prop :=
  ¬ TMDecidable pred

/-- `TMDecides D pred`: the explicit form — `D` halts outputting
`[true]` on members of `pred` and `[false]` on non-members. -/
def TMDecides (D : SingleTapeTM Bool) (pred : List Bool → Prop) : Prop :=
  ∀ bits : List Bool,
    (pred bits → SingleTapeTM.Outputs D bits [true]) ∧
    (¬ pred bits → SingleTapeTM.Outputs D bits [false])

/-- A `TMDecidable` predicate has an explicit `TMDecides` decider: the
TimeComputable's underlying TM outputs the indicator, which is
`[true]`/`[false]` per `pred`. -/
theorem TMDecidable.exists_TMDecides {pred : List Bool → Prop}
    (h : TMDecidable pred) : ∃ D : SingleTapeTM Bool, TMDecides D pred := by
  obtain ⟨tc⟩ := h
  refine ⟨tc.tm, fun bits => ⟨fun hp => ?_, fun hp => ?_⟩⟩
  · have h_out := outputs_of_outputsWithinTime (tc.outputsFunInTime bits)
    have h_ind : boolIndicator pred bits = [true] := by
      unfold boolIndicator; exact if_pos hp
    rwa [h_ind] at h_out
  · have h_out := outputs_of_outputsWithinTime (tc.outputsFunInTime bits)
    have h_ind : boolIndicator pred bits = [false] := by
      unfold boolIndicator; exact if_neg hp
    rwa [h_ind] at h_out

/-! ## Discharged: TM-computation machinery -/

/-- **Identity is TM-computable.** From cslib's `TimeComputable.id`. -/
theorem TMComputable.id : TMComputable (fun bits : List Bool => bits) :=
  ⟨TimeComputable.id⟩

/-- **Composition of TM-computable functions.** From cslib's
`TimeComputable.comp`, monotonising the second machine's time bound. -/
theorem TMComputable.comp {f g : List Bool → List Bool}
    (h_f : TMComputable f) (h_g : TMComputable g) :
    TMComputable (g ∘ f) := by
  obtain ⟨tcf⟩ := h_f
  obtain ⟨tcg⟩ := h_g
  exact ⟨TimeComputable.comp tcf (monotoniseTC tcg) (monotoniseTC_isMonotone tcg)⟩

/-- **TM-undecidability transfers along TM-computable reductions.**

If `f` is TM-computable and `pred₁ bits ↔ pred₂ (f bits)`, then a
TM-decider for `pred₂` composes with the computer for `f` to decide
`pred₁`. Formally: `boolIndicator pred₁ = boolIndicator pred₂ ∘ f`, so
`TMDecidable pred₂ → TMDecidable pred₁` by `TMComputable.comp`. -/
theorem TMUndecidable.of_TMReduction
    {pred₁ pred₂ : List Bool → Prop}
    (f : List Bool → List Bool)
    (h_comp : TMComputable f)
    (h_iff : ∀ bits, pred₁ bits ↔ pred₂ (f bits))
    (h₁ : TMUndecidable pred₁) :
    TMUndecidable pred₂ := by
  intro h_dec₂
  apply h₁
  have h_eq : boolIndicator pred₁ = boolIndicator pred₂ ∘ f := by
    classical
    funext bits
    simp only [boolIndicator, Function.comp_apply]
    exact if_congr (h_iff bits) rfl rfl
  show TMComputable (boolIndicator pred₁)
  rw [h_eq]
  exact TMComputable.comp h_comp h_dec₂

/-! ## Connection to the framework's classical `Undecidable` -/

/-- TM-decidability implies (classical) `Decidable`-style decidability:
classically every predicate is decidable, so this is the easy
direction. -/
theorem TMDecidable.toDecidable
    {pred : List Bool → Prop} (_h : TMDecidable pred) :
    Decidable { Input := List Bool, predicate := pred : Problem } := by
  classical
  refine ⟨fun bits => decide (pred bits), ?_⟩
  intro bits
  by_cases hp : pred bits <;> simp [hp]

/-- Classical `Undecidable` is **weaker** than `TMUndecidable`: no Lean
function decides ⇒ no TM decides. (Since `Undecidable` is classically
vacuous this is useless on its own; the converse is *not* valid.) -/
theorem Undecidable.of_TMUndecidable
    {pred : List Bool → Prop} :
    Undecidable { Input := List Bool, predicate := pred : Problem } →
    TMUndecidable pred := by
  intro h_undec h_tm_dec
  exact h_undec (TMDecidable.toDecidable h_tm_dec)

end DiagonaLean
