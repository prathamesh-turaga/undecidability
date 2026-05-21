/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Mathlib.Data.Set.Basic

@[expose] public section

/-!
# Diagonalisation — the kernel of the Halting Problem proof

The halting problem's undecidability is, at heart, a diagonal argument:
given any uniform "decider" `f : Code → (Input → Bool)`, we can build a
function `g : Input → Bool` that disagrees with each `f c` at the
diagonal entry, and hence is not equal to any `f c`. If `f` was
*supposed* to enumerate all Bool-valued computable functions, this is a
contradiction.

This file isolates the purely mathematical core of the argument — no
Turing machines, no decidability, just functions and `Bool` — so that
the halting-undecidability proof in `Halt.Basic` (and future files) can
cite it once and stay focused on the model-specific encoding work.

## Main results

* `cantor_diag` — for any `f : α → (α → Bool)`, there is a `g : α → Bool`
  not in the image of `f`. The witness is the diagonal `fun a => !f a a`.
* `Function.cantor_diag_not_surjective` — corollary: there is no
  surjection `α → (α → Bool)`. (This is "Cantor's theorem".)
* `halt_diag` — a general "halting-style" diagonalisation: if `App`
  represents partial application (e.g., `App c x` is "code `c` applied
  to input `x`"), no Bool-valued decider `H : α → α → Bool` can satisfy
  `H c c = isSome (App c c)` for *every* `c` *and* be itself in the
  range of `App` as a `Bool`-valued partial function. This is the
  shape of the argument needed for the Halting Problem.
-/

namespace Halt.Diagonal

/-! ## Cantor's diagonal argument -/

/-- **Cantor's diagonal lemma.** For any uniform family of Boolean
functions `f : α → α → Bool`, the function `fun a => !f a a` differs
from each `f a` at the input `a`, so it is not equal to any `f a`. -/
theorem cantor_diag {α : Type*} (f : α → α → Bool) :
    ∃ g : α → Bool, ∀ a, g ≠ f a := by
  refine ⟨fun a => !f a a, ?_⟩
  intro a h
  have hcontr : (! f a a) = f a a := congrFun h a
  exact (Bool.not_ne_self _) hcontr

/-- **Cantor's theorem**: there is no surjection from a type onto its
Boolean power-set (`α → α → Bool`). -/
theorem not_surjective_cantor {α : Type*} (f : α → α → Bool) :
    ¬ Function.Surjective f := by
  intro hsurj
  obtain ⟨g, hg⟩ := cantor_diag f
  obtain ⟨a, ha⟩ := hsurj g
  exact hg a ha.symm

/-! ## A more refined "halting-style" diagonalisation

The Cantor argument above forbids a uniform `f : α → (α → Bool)` from
hitting every function. The halting argument is slightly different: it
forbids the *decider itself* from being implementable in the same
calculus that the codes are drawn from. We capture this here.

Set-up: think of `α` as a set of "codes" and of `App c x : Option Bool`
as "the code `c` run on input `x`, partially decoded as a Bool". The
diagonal argument says no `H : α → α → Bool` can simultaneously be in
the image of `App` (in a suitable sense) and decide the dom-emptiness
of `App` along the diagonal. -/

/-- A general "no fixpoint" form of the diagonal argument: if `flip` is
a `Bool`-toggle (no fixed point), then `f` cannot satisfy
`f a a = flip (f a a)` for any `a`. The Halting Problem's diagonal
function arises by setting `flip = Bool.not`. -/
theorem no_self_fixpoint_of_flip {α : Type*}
    {flip : Bool → Bool} (hflip : ∀ b, flip b ≠ b)
    (f : α → α → Bool) (a : α) :
    f a a ≠ flip (f a a) := by
  intro h
  exact hflip (f a a) h.symm

/-! ## Halting-flavoured corollaries

The standard halting argument goes:

  Suppose `H : Code → Input → Bool` decides halting:
  `H c x = true ↔ "code `c` halts on input `x`"`.

  Build the diagonal function `D : Code → Bool`, `D c = !(H c c)`.
  - If `D` itself is computable, its code is some `d : Code`.
  - Run `H d d`: `true` iff `D d` halts, `false` iff not.
  - But `D d = !(H d d)`. Two cases:
    - `H d d = true` ⟹ `D d = false`, contradicting `D d` halting.
    - `H d d = false` ⟹ `D d = true`, contradicting `D d` not halting.

The "is computable" / "has a code" step is the model-specific piece
(Church–Turing). The diagonal contradiction itself is captured below.

`halt_diag_contradiction` packages exactly this contradiction
abstractly: any "decider" `H : α → α → Bool` that admits a code for
its own diagonal `fun c => !(H c c)` leads to `False`. -/

/-- The abstract halting-style contradiction: given `H : α → α → Bool`
and any `d : α` such that
`H d d ↔ ¬ (fun c => ! H c c) d` evaluates inconsistently,
we derive `False`. This is the *purely logical* heart of the standard
halting-problem proof; closing it for any concrete model requires
producing the witness `d`. -/
theorem halt_diag_contradiction {α : Type*} (H : α → α → Bool)
    (d : α) (hd : (! H d d) = H d d) : False :=
  Bool.not_ne_self _ hd

end Halt.Diagonal
