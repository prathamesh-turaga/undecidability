/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Reduction.Composition

@[expose] public section

/-!
# Transfer theorems

The headline use of `ManyOneReduction`: pulling decidability backward,
pushing undecidability forward.

* `Decidable.of_manyOne`   — `P ≤ₘ Q ∧ Q decidable → P decidable`.
* `Undecidable.of_manyOne` — `P ≤ₘ Q ∧ P undecidable → Q undecidable`.

These are the load-bearing lemmas of the framework: once a problem is
proved undecidable and registered in the reduction graph, every problem
reachable from it via `ManyOneReduction` inherits the undecidability.
-/

namespace DiagonaLean

/-- **Decidability transfers backward through many-one reductions.**
If `P ≤ₘ Q` and `Q` is decidable, then `P` is decidable (decide a
positive instance of `P` by running the reduction and asking `Q`'s
decider). -/
theorem Decidable.of_manyOne {P Q : Problem}
    (r : ManyOneReduction P Q) (hQ : Decidable Q) : Decidable P := by
  obtain ⟨d, hd⟩ := hQ
  refine ⟨fun x => d (r.f x), fun x => ?_⟩
  exact (hd (r.f x)).trans (r.spec x).symm

/-- **Undecidability transfers forward through many-one reductions.**
If `P ≤ₘ Q` and `P` is undecidable, then `Q` is undecidable. -/
theorem Undecidable.of_manyOne {P Q : Problem}
    (r : ManyOneReduction P Q) (hP : Undecidable P) : Undecidable Q :=
  fun hQ => hP (Decidable.of_manyOne r hQ)

/-- Convenience: undecidability of `P` and `P ≤ₘ Q` give undecidability
of `Q`. Same as `Undecidable.of_manyOne` with arguments flipped. -/
theorem ManyOneReduction.undecidable_target {P Q : Problem}
    (r : ManyOneReduction P Q) (hP : Undecidable P) : Undecidable Q :=
  Undecidable.of_manyOne r hP

end DiagonaLean
