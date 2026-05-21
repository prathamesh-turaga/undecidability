/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Reduction.Transfer

@[expose] public section

/-!
# Notation for reductions

* `P ≤ₘ Q`     — `ManyOneReduction P Q` exists (asymmetric).
* `P ≡ₘ Q`     — `ManyOneReduction P Q × ManyOneReduction Q P`
  (mutual reducibility).

Both notations live in the `DiagonaLean` namespace.
-/

namespace DiagonaLean

/-- Mutual many-one reducibility. -/
structure ManyOneEquivalent (P Q : Problem) where
  forward  : ManyOneReduction P Q
  backward : ManyOneReduction Q P

@[inherit_doc] infix:50 " ≤ₘ " => ManyOneReduction
@[inherit_doc] infix:50 " ≡ₘ " => ManyOneEquivalent

namespace ManyOneEquivalent

/-- Reflexivity of `≡ₘ`. -/
def refl (P : Problem) : P ≡ₘ P where
  forward := ManyOneReduction.id P
  backward := ManyOneReduction.id P

/-- Symmetry of `≡ₘ`. -/
def symm {P Q : Problem} (h : P ≡ₘ Q) : Q ≡ₘ P where
  forward := h.backward
  backward := h.forward

/-- Transitivity of `≡ₘ`. -/
def trans {P Q R : Problem} (h₁ : P ≡ₘ Q) (h₂ : Q ≡ₘ R) : P ≡ₘ R where
  forward := h₁.forward.trans h₂.forward
  backward := h₂.backward.trans h₁.backward

end ManyOneEquivalent

end DiagonaLean
