/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Reduction.Basic

@[expose] public section

/-!
# Composition laws for many-one reductions

`ManyOneReduction` is a reflexive-transitive relation on `Problem`s.
This file proves the algebraic laws:

* `ManyOneReduction.id`     — identity reduction `P ≤ₘ P`.
* `ManyOneReduction.trans`  — transitivity `P ≤ₘ Q → Q ≤ₘ R → P ≤ₘ R`.
* `ManyOneReduction.symm_of_iff` — when the spec's bidirectionality is
  realised by an *inverse* function, we get a reduction back; this
  packages iff-style reductions into mutual reducers.
-/

namespace DiagonaLean.ManyOneReduction

/-- The identity reduction `P ≤ₘ P`. -/
def id (P : Problem) : ManyOneReduction P P where
  f := _root_.id
  spec _ := Iff.rfl

/-- Composition of reductions: `P ≤ₘ Q` and `Q ≤ₘ R` give `P ≤ₘ R`. -/
def trans {P Q R : Problem}
    (h₁ : ManyOneReduction P Q) (h₂ : ManyOneReduction Q R) :
    ManyOneReduction P R where
  f := h₂.f ∘ h₁.f
  spec x := (h₁.spec x).trans (h₂.spec (h₁.f x))

/-- A reduction `Q ≤ₘ P` constructed from an inverse function `g` and
its spec. Used when an iff-style theorem already provides
`Q.pred y ↔ P.pred (g y)`. -/
def ofInverse {P Q : Problem}
    (g : Q.Input → P.Input)
    (h_gf : ∀ y, Q.predicate y ↔ P.predicate (g y))
    : ManyOneReduction Q P where
  f := g
  spec := h_gf

/-- Sanity-check: identity composed with anything is the original. -/
@[simp] theorem id_trans {P Q : Problem} (h : ManyOneReduction P Q) :
    (id P).trans h = h := by
  obtain ⟨_, _⟩ := h
  rfl

@[simp] theorem trans_id {P Q : Problem} (h : ManyOneReduction P Q) :
    h.trans (id Q) = h := by
  obtain ⟨_, _⟩ := h
  rfl

/-- Composition is associative. -/
theorem trans_assoc {P Q R S : Problem}
    (h₁ : ManyOneReduction P Q) (h₂ : ManyOneReduction Q R)
    (h₃ : ManyOneReduction R S) :
    (h₁.trans h₂).trans h₃ = h₁.trans (h₂.trans h₃) :=
  rfl

end DiagonaLean.ManyOneReduction
