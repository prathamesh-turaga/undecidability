/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

module

public import Reduction.Basic
public import Reduction.Composition
public import Reduction.Transfer
public import Reduction.Notation
public import Reduction.Graph
public import Reduction.Search
public import Reduction.Tactic
public import Reduction.TMDecidable
public import Reduction.Instances
public import Reduction.Encoded
public import Reduction.HaltUndecidable
public import Reduction.StackMap
public import Reduction.EncodedPCP
public import Reduction.EncodedHaltMPCP
public import Reduction.EncodedHaltNormalised
public import Reduction.EncodedCFG
public import Reduction.StackEncoding
public import Reduction.EncodedLB

@[expose] public section

/-!
# Reduction — the DiagonaLean library root

This library is the DiagonaLean framework: a compositional toolkit for
many-one reductions, a registered *reduction graph*, and the
`by reduce_diag` proof-search tactic. See [`README.md`](../README.md)
for the project overview and [`ROADMAP.md`](../ROADMAP.md) for the
architecture.

## Core framework

* `Reduction.Basic`       — `Problem`, `ManyOneReduction`, classical
                            `Decidable` / `Undecidable`.
* `Reduction.Composition` — `.id`, `.trans`, identity / associativity.
* `Reduction.Transfer`    — `Decidable.of_manyOne`, `Undecidable.of_manyOne`.
* `Reduction.Notation`    — `P ≤ₘ Q`, `P ≡ₘ Q`.

`ManyOneReduction.f` is an arbitrary Lean function; computability
constraints live at the TM layer below.

## TM-level (un)decidability

* `Reduction.TMDecidable` — `TMComputable`, `TMDecidable`,
                            `TMUndecidable` on `List Bool → Prop`,
                            defined over cslib's
                            `SingleTapeTM.TimeComputable`. The
                            composition machinery — `TMComputable.id`,
                            `TMComputable.comp`,
                            `TMUndecidable.of_TMReduction` — is
                            **proved**, not postulated.
* `Reduction.HaltUndecidable` — bridges `Halt.halt_undecidable` to
                            `TMUndecidable selfHaltPred` (no postulate),
                            and registers `EncodedSelfHalt ≤ₘ
                            EncodedHalt`.

## The reduction graph (`List Bool`-input nodes)

The `Reduction.Encoded*` / `StackMap` / `StackEncoding` modules give
every problem a `List Bool`-flavoured `Problem` node and wire the
13 graph edges. The spine runs end-to-end:

  `EncodedSelfHalt → EncodedHalt → EncodedHaltMPCP → EncodedMPCP_LB`
  `  → EncodedPCP_LB → EncodedCFGI_LB`

The `EncodedHalt → EncodedHaltMPCP` edge applies the HUM normalising
wrapper (`Reduction.EncodedHaltNormalised`).

## The tactic

* `Reduction.Graph`  — `@[reduction_graph]` registers edges;
                       `@[undecidable_anchor]` /
                       `@[tm_undecidable_anchor]` mark anchors.
* `Reduction.Search` — depth-bounded backward DFS to an anchor.
* `Reduction.Tactic` — `by reduce_diag` composes the path and applies
                       the transfer theorem, dispatching on whether the
                       goal is `Undecidable P` or
                       `TMUndecidable P.predicate`.

`Reduction.Smoke` `#eval`s the graph and exercises `by reduce_diag`.

Known limitation: `composeReductions` handles only ground edges
(polymorphic edges throw); see [`TODO.md`](../TODO.md).
-/
