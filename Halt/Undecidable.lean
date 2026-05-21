/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Halt.CodeOf

@[expose] public section

/-!
# The Halting Problem is undecidable for `SingleTapeTM Bool`

We prove that the **self-halt** decision problem

  `K := { c : TMCode | c.toTM halts on encodeTMCode c }`

cannot be decided by any `SingleTapeTM Bool`. The argument is the
classical diagonal.

## Construction

* Assume `D : SingleTapeTM Bool` is a strict K-decider (`IsSelfHaltDecider`,
  see `Halt.Basic`) — on input `encodeTMCode c`, `D` outputs `[true]`
  if `c.toTM` halts on `encodeTMCode c`, and `[false]` otherwise.
* Build the *diagonal* TM `diagTM D` directly (state space
  `D.State ⊕ DiagPost`, with `DiagPost = {reading, loop}`): it
  simulates `D` until `D` would halt; then it inspects the head symbol
  of `D`'s output tape. If the head is `true`, `diagTM` enters an
  infinite `loop` state; if the head is `false` (or blank), it halts.
* Let `c_diag := codeOf (diagTM D)`. By `IsSelfHaltDecider` and
  `Halt.CodeOf.halts_codeOf_iff`, `D` outputs `[true]` iff `c_diag.toTM`
  halts iff `diagTM D` halts iff `D` outputs `[false]`. Contradiction.

## Technical core

The forward direction (`Outputs D w [true] → ¬ Halts (diagTM D) w`)
uses *deterministic confluence* on `ReflTransGen`: a `D`-lifted trace
ending in `loop` and the assumed halt trace must agree by determinism,
but `loop` is closed under stepping, so no halt is reachable.

The backward direction (`Outputs D w [false] → Halts (diagTM D) w`) is
direct: lift `D`'s trace to `diagTM`, take one more step from `reading`
with head `some false` to reach the halt configuration.

The inlined `diagTM` avoids `compComputer`'s nested match reductions
and keeps the per-step reasoning straightforward. The trade-off is
~370 LoC for `Halt.Undecidable` itself (versus an estimated
2000–4000 LoC for a textbook universal-TM construction).
-/

namespace Halt

open Turing PCP

/-! ## Deterministic diamond on `ReflTransGen` -/

/-- Two `ReflTransGen` traces from the same point under a deterministic
relation are cofinal: one extends the other. -/
private lemma reflTransGen_diamond {α : Type*} {r : α → α → Prop}
    (h_det : ∀ {a b c : α}, r a b → r a c → b = c)
    {a b c : α}
    (hab : Relation.ReflTransGen r a b)
    (hac : Relation.ReflTransGen r a c) :
    Relation.ReflTransGen r b c ∨ Relation.ReflTransGen r c b := by
  induction hab with
  | refl => exact Or.inl hac
  | @tail b_int b_end h_rest h_step ih =>
    cases ih with
    | inr h_c_b_int => exact Or.inr (h_c_b_int.tail h_step)
    | inl h_b_int_c =>
      rcases h_b_int_c.cases_head with h_eq | ⟨x, h_b_int_x, h_x_c⟩
      · -- b_int = c, so r b_int b_end with b_int = c gives r c b_end.
        subst h_eq
        exact Or.inr (Relation.ReflTransGen.single h_step)
      · have h_eq : x = b_end := h_det h_b_int_x h_step
        subst h_eq
        exact Or.inl h_x_c

/-- `SingleTapeTM.TransitionRelation` is deterministic. -/
private lemma transitionRelation_det {tm : SingleTapeTM Bool}
    {a b c : tm.Cfg}
    (hab : tm.TransitionRelation a b) (hac : tm.TransitionRelation a c) :
    b = c := by
  simp only [SingleTapeTM.TransitionRelation] at hab hac
  rw [hab] at hac
  exact Option.some_inj.mp hac

/-- Specialisation of the diamond to `SingleTapeTM` traces. -/
private lemma trace_diamond {tm : SingleTapeTM Bool}
    {a b c : tm.Cfg}
    (hab : Relation.ReflTransGen tm.TransitionRelation a b)
    (hac : Relation.ReflTransGen tm.TransitionRelation a c) :
    Relation.ReflTransGen tm.TransitionRelation b c ∨
    Relation.ReflTransGen tm.TransitionRelation c b :=
  reflTransGen_diamond (@transitionRelation_det _) hab hac

/-! ## The diagonal TM -/

/-- The state space of `diagTM D`: either a state of `D` (in the
"simulating `D`" phase), or one of two post-`D` states. -/
private inductive DiagPost : Type
  | reading -- about to inspect the head symbol of `D`'s output
  | loop    -- looping forever
  deriving DecidableEq, Inhabited

private instance : Fintype DiagPost where
  elems := {DiagPost.reading, DiagPost.loop}
  complete := fun x => by cases x <;> decide

/-- The diagonal TM for a hypothetical decider `D`. Simulates `D`;
when `D` would halt, transitions to `reading`. From `reading`, halts
if head is anything other than `some true`, loops if head is `some true`. -/
private def diagTM (D : SingleTapeTM Bool) : SingleTapeTM Bool where
  State := D.State ⊕ DiagPost
  q₀ := .inl D.q₀
  tr q sym :=
    match q with
    | .inl q' =>
      let (stmt, next) := D.tr q' sym
      match next with
      | some q'' => (stmt, some (.inl q''))
      | none     => (stmt, some (.inr .reading))  -- D would halt → reading
    | .inr .reading =>
      match sym with
      | some true => (⟨none, none⟩, some (.inr .loop))
      | _         => (⟨none, none⟩, none)  -- halt (some false or blank)
    | .inr .loop => (⟨none, none⟩, some (.inr .loop))

/-! ## Lifting `D`-traces into `diagTM`-traces -/

variable (D : SingleTapeTM Bool)

/-- Lift a `D`-cfg into a `diagTM`-cfg. The `D`-halt cfg `⟨none, t⟩`
maps to `⟨some (.inr .reading), t⟩`. -/
private def liftCfg : D.Cfg → (diagTM D).Cfg
  | ⟨some q, t⟩ => ⟨some (.inl q), t⟩
  | ⟨none, t⟩   => ⟨some (.inr .reading), t⟩

@[simp] private lemma liftCfg_initCfg (w : List Bool) :
    liftCfg D (SingleTapeTM.initCfg D w) =
      SingleTapeTM.initCfg (diagTM D) w := rfl

@[simp] private lemma liftCfg_haltCfg (out : List Bool) :
    liftCfg D (SingleTapeTM.haltCfg D out) =
      ⟨some (.inr .reading), BiTape.mk₁ out⟩ := rfl

/-- One `D`-step lifts to one `diagTM`-step. -/
private lemma step_liftCfg
    {a b : D.Cfg} (h_ab : D.TransitionRelation a b) :
    (diagTM D).TransitionRelation (liftCfg D a) (liftCfg D b) := by
  obtain ⟨st_a, t_a⟩ := a
  cases st_a with
  | none => simp [SingleTapeTM.TransitionRelation, SingleTapeTM.step] at h_ab
  | some q =>
    generalize h_tr : D.tr q t_a.head = res
    obtain ⟨⟨wr, dir⟩, next⟩ := res
    have h_step_D : D.step ⟨some q, t_a⟩ =
        some ⟨next, (t_a.write wr).optionMove dir⟩ := by
      simp only [SingleTapeTM.step, h_tr]
    simp only [SingleTapeTM.TransitionRelation] at h_ab
    rw [h_step_D, Option.some_inj] at h_ab
    subst h_ab
    show (diagTM D).step ⟨some (.inl q), t_a⟩ =
      some (liftCfg D ⟨next, (t_a.write wr).optionMove dir⟩)
    cases next with
    | none =>
      show (diagTM D).step ⟨some (.inl q), t_a⟩ =
        some ⟨some (.inr DiagPost.reading), (t_a.write wr).optionMove dir⟩
      simp only [SingleTapeTM.step, diagTM, h_tr]
    | some q' =>
      show (diagTM D).step ⟨some (.inl q), t_a⟩ =
        some ⟨some (.inl q'), (t_a.write wr).optionMove dir⟩
      simp only [SingleTapeTM.step, diagTM, h_tr]

/-- `D`-traces lift to `diagTM`-traces. -/
private lemma trace_liftCfg {a b : D.Cfg}
    (h : Relation.ReflTransGen D.TransitionRelation a b) :
    Relation.ReflTransGen (diagTM D).TransitionRelation
      (liftCfg D a) (liftCfg D b) :=
  Relation.ReflTransGen.lift (liftCfg D) (fun _ _ => step_liftCfg D) h

/-! ## Behaviour of `diagTM` in the post-`D` phase -/

/-- One step from `reading` with head `some true` enters `loop`. -/
private lemma diagTM_reading_true (t : BiTape Bool)
    (h_head : t.head = some true) :
    (diagTM D).step ⟨some (.inr .reading), t⟩ =
      some ⟨some (.inr .loop), t.write none⟩ := by
  obtain ⟨h, l, r⟩ := t
  cases h_head
  rfl

/-- One step from `reading` with head `some false` halts. -/
private lemma diagTM_reading_false (t : BiTape Bool)
    (h_head : t.head = some false) :
    (diagTM D).step ⟨some (.inr .reading), t⟩ =
      some ⟨none, t.write none⟩ := by
  obtain ⟨h, l, r⟩ := t
  cases h_head
  rfl

/-- One step from `loop` stays in `loop`. -/
private lemma diagTM_loop_step (t : BiTape Bool) :
    (diagTM D).step ⟨some (.inr .loop), t⟩ =
      some ⟨some (.inr .loop), t.write none⟩ := by
  obtain ⟨h, l, r⟩ := t
  rfl

/-- The `loop` state is closed under stepping. -/
private lemma loop_closed
    {a b : (diagTM D).Cfg}
    (h_loop : a.state = some (.inr .loop))
    (h_step : (diagTM D).TransitionRelation a b) :
    b.state = some (.inr .loop) := by
  obtain ⟨st_a, t_a⟩ := a
  simp only at h_loop
  subst h_loop
  have h := diagTM_loop_step D t_a
  show b.state = some (.inr .loop)
  simp only [SingleTapeTM.TransitionRelation] at h_step
  rw [h] at h_step
  rcases b with ⟨st_b, t_b⟩
  injection h_step with h_cfg
  obtain ⟨h_st, _⟩ := SingleTapeTM.Cfg.mk.injEq .. |>.mp h_cfg
  exact h_st.symm

/-- From `loop`, every reachable cfg is in `loop`. -/
private lemma loop_persistent
    {a b : (diagTM D).Cfg}
    (h_loop : a.state = some (.inr .loop))
    (h_reach : Relation.ReflTransGen (diagTM D).TransitionRelation a b) :
    b.state = some (.inr .loop) := by
  induction h_reach with
  | refl => exact h_loop
  | tail _ h_step ih => exact loop_closed D ih h_step

/-! ## Behavior on `Outputs D w [false]` and `Outputs D w [true]` -/

/-- If `D` outputs `[false]` on `w`, then `diagTM D` halts on `w`. -/
private lemma diagTM_halts_of_outputs_false
    {w : List Bool}
    (h : SingleTapeTM.Outputs D w [false]) :
    PCP.Halts (diagTM D) w := by
  -- Lift D's trace to diagTM.
  have h_lift := trace_liftCfg D h
  rw [liftCfg_initCfg, liftCfg_haltCfg] at h_lift
  -- One more step: ⟨some (.inr .reading), mk₁ [false]⟩ → ⟨none, _⟩
  have h_step : (diagTM D).TransitionRelation
      ⟨some (.inr .reading), BiTape.mk₁ [false]⟩
      ⟨none, (BiTape.mk₁ [false]).write none⟩ := by
    show (diagTM D).step _ = some _
    apply diagTM_reading_false
    rfl
  exact ⟨_, h_lift.tail h_step⟩

/-- If `D` outputs `[true]` on `w`, then `diagTM D` does *not* halt
on `w`. -/
private lemma diagTM_loops_of_outputs_true
    {w : List Bool}
    (h : SingleTapeTM.Outputs D w [true]) :
    ¬ PCP.Halts (diagTM D) w := by
  rintro ⟨tape_halt, h_halt⟩
  -- Lift D's trace to diagTM, ending at ⟨some (.inr .reading), mk₁ [true]⟩.
  have h_lift := trace_liftCfg D h
  rw [liftCfg_initCfg, liftCfg_haltCfg] at h_lift
  -- One more step lands in `.loop`.
  have h_step : (diagTM D).TransitionRelation
      ⟨some (.inr .reading), BiTape.mk₁ [true]⟩
      ⟨some (.inr .loop), (BiTape.mk₁ [true]).write none⟩ := by
    show (diagTM D).step _ = some _
    apply diagTM_reading_true
    rfl
  have h_loop_reach : Relation.ReflTransGen (diagTM D).TransitionRelation
      (SingleTapeTM.initCfg (diagTM D) w)
      ⟨some (.inr .loop), (BiTape.mk₁ [true]).write none⟩ :=
    h_lift.tail h_step
  -- By deterministic diamond: ⟨some (.inr .loop), _⟩ →* ⟨none, tape_halt⟩
  -- (since the reverse is impossible from a halt cfg).
  rcases trace_diamond h_loop_reach h_halt with h_loop_to_halt | h_halt_to_loop
  · -- From `.loop`, every reachable cfg is in `.loop`. But the destination
    -- has state `none`. Contradiction.
    have := loop_persistent D rfl h_loop_to_halt
    simp at this
  · -- ⟨none, tape_halt⟩ →* ⟨some (.inr .loop), _⟩. Impossible.
    rcases h_halt_to_loop.cases_head with h_eq | ⟨c, h_step', _⟩
    · -- ⟨none, tape_halt⟩ = ⟨some (.inr .loop), _⟩. Contradicts state mismatch.
      simp at h_eq
    · simp [SingleTapeTM.TransitionRelation, SingleTapeTM.step] at h_step'

/-! ## The main theorem

The predicate `IsSelfHaltDecider` lives in `Halt.Basic`; here we use
it as a hypothesis and derive a contradiction. -/

/-- **The Halting Problem is undecidable**: no `SingleTapeTM Bool` can
decide the self-halt problem `K`. -/
theorem halt_undecidable :
    ¬ ∃ D : SingleTapeTM Bool, IsSelfHaltDecider D := by
  rintro ⟨D, h_dec⟩
  -- Construct the diagonal TM and its code.
  let c_diag : Halt.TMCode := codeOf (diagTM D)
  -- Apply `IsSelfHaltDecider` at `c_diag`.
  obtain ⟨h_pos, h_neg⟩ := h_dec c_diag
  by_cases h_halts : Halts c_diag.toTM (Halt.Encoding.encodeTMCode c_diag)
  · -- D outputs [true] on `encodeTMCode c_diag`.
    have h_out_true := h_pos h_halts
    -- By `halts_codeOf_iff`, diagTM halts on `encodeTMCode c_diag`.
    have h_diag_halts : PCP.Halts (diagTM D)
        (Halt.Encoding.encodeTMCode c_diag) :=
      (halts_codeOf_iff (diagTM D) (Halt.Encoding.encodeTMCode c_diag)).mp
        h_halts
    -- But Outputs D w [true] forbids diagTM from halting.
    exact diagTM_loops_of_outputs_true D h_out_true h_diag_halts
  · -- D outputs [false] on `encodeTMCode c_diag`.
    have h_out_false := h_neg h_halts
    -- By `diagTM_halts_of_outputs_false`, diagTM halts.
    have h_diag_halts := diagTM_halts_of_outputs_false D h_out_false
    -- By `halts_codeOf_iff`, c_diag.toTM halts. Contradiction.
    have :=
      (halts_codeOf_iff (diagTM D) (Halt.Encoding.encodeTMCode c_diag)).mpr
        h_diag_halts
    exact h_halts this

end Halt
